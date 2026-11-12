/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR7StochWerning

/-!
# The zero-bound experiment under uncertainty: the bounded equilibria

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.2, pp. 474–477
(Figure 20.4), §20.2.4, pp. 478–480 (forward guidance), with equations (20.5)–(20.10).

The experiment of §20.2.2: interest rate `i = 0`, natural rate `u` on `[0, T)` and `0` after,
Phillips-curve disturbance `g` on `[0, T)` and `0` after (`g = 0` in §20.2.2, `g ≠ 0` in
§20.2.5). Now the paths are random: the equilibrium may respond to any news (sunspot or fiscal
shocks, "the fiscal innovation at time 0", p. 476) through the expectational errors of
(20.5)–(20.6). We characterise **every** regular `L¹`-bounded stochastic equilibrium
(TidyR7StochWerning: `IsStochEqm`, `Regular`, `BddL1`).

## Main results

* `setIntegral_trap`: for `A ∈ 𝓕_s`, `∫_A π_t = P(A)wPi(0)_t + e^{−λ^b(t−s)}(∫_A π_s −
  P(A)wPi(0)_s)` and `κ(∫_A x_t − P(A)wX(0)_t) = λ^f(∫_A π_t − P(A)wPi(0)_t)` for `t ≥ s`.
* **`condExp_pi_eq`, `condExp_x_eq`**: `E_s π_t = wPi(0)_t + e^{−λ^b(t−s)}(π_s − wPi(0)_s)`,
  `E_s x_t = wX(0)_t + (λ^f/κ)e^{−λ^b(t−s)}(π_s − wPi(0)_s)` almost surely.
* **`condExp_pi_eq_wPi`, `condExp_x_eq_wX`** (stochastic `bdd_path_iff`): for `s ≤ T`,
  `E_s π_t = wPi(E_s π_T)_t` and `E_s x_t = wX(E_s π_T)_t` — the bounded equilibria are the
  family of Figure 20.4 with the free index `π_T` replaced by its conditional expectation.
  Forward guidance (§20.2.4) acts through `E_s π_T` exactly as `π_T` does in the deterministic
  model.
* **`x_eq_of_pi`**: `x_s = wX(0)_s + (λ^f/κ)(π_s − wPi(0)_s)` a.s. at every date: the
  forward-explosive root is ruled out state by state (the unstable combination
  `λ^f π − κ x` is deterministic).
* **`innovation_x_eq`**: `x_t − E_s x_t = (λ^f/κ)(π_t − E_s π_t)`: the response of output to
  any shock is `λ^f/κ` times the response of inflation, the deterministic ratio of
  `wX_shift`/`wPi_shift`; **`revision_pi_eq`**: `E_s π_t − E_r π_t = e^{−λ^b(t−s)}(π_s − E_r π_s)`
  — news at `s` propagates exactly as the deterministic response `e^{−λ^b(t−s)}`.
* **`mean_eq_wPi`**: the mean path `(E x_t, E π_t)` is the member `(wX, wPi)(E π_T)` of the
  deterministic family.
* The deterministic case: **`isStochEqm_det_iff`** (deterministic continuous paths are
  stochastic equilibria iff they are WerningModel `IsPath`s) and **`det_bdd_iff`** (with
  `BddL1`, iff they are members of the family of `bdd_path_iff`).

Comparison with the discrete-time results of TidyR6OrbitStochastic (§20.2.1): there the
zero-bound rule `max(ℓ, z)` is convex, expected inflation lies above the deterministic orbit
(`TidyR6OrbitStochastic.stoch_jensen`) and the path-wise orbit statements fail under uncertainty
(`TidyR6OrbitStochastic.cex_not_ae_tendsto_zero`). Here the interest rate path is given and the
model is linear, so the Jensen gap is zero: conditional means are exactly deterministic paths,
and the deterministic results hold for expectations with no correction, state by state for the
unstable combination.
-/

namespace Cochrane.ZeroBound.TidyR7StochWerningTrap

open MeasureTheory Filter Topology
open Cochrane.ZeroBound.ContinuousTimeNK Cochrane.ZeroBound.WerningModel
open Cochrane.ZeroBound.TidyR7StochWerning

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ## The step forcing -/

/-- Cochrane (2023), §20.2.2, p. 474: the trap step `trapStep c T` is measurable. -/
theorem trapStep_measurable (c T : ℝ) : Measurable (trapStep c T) :=
  Measurable.ite (p := fun t => t < T) measurableSet_Iio measurable_const measurable_const

/-- Cochrane (2023), §20.2.2, p. 474: `|trapStep c T t| ≤ |c|`. -/
theorem trapStep_abs_le (c T t : ℝ) : |trapStep c T t| ≤ |c| := by
  unfold trapStep
  split_ifs <;> simp

/-- Cochrane (2023), §20.2.2, p. 474: the trap step is integrable on every bounded set. -/
theorem trapStep_integrableOn (c T : ℝ) {S : Set ℝ} (hS : volume S ≠ ⊤) :
    IntegrableOn (trapStep c T) S :=
  Measure.integrableOn_of_bounded hS (trapStep_measurable c T).aestronglyMeasurable
    (M := |c|) (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]
      exact trapStep_abs_le c T t)

/-- Cochrane (2023), §20.2.2, p. 474: the trap step is interval integrable. -/
theorem trapStep_intervalIntegrable (c T a b : ℝ) :
    IntervalIntegrable (trapStep c T) volume a b := by
  rw [intervalIntegrable_iff]
  exact trapStep_integrableOn c T (by rw [Set.uIoc]; exact measure_Ioc_lt_top.ne)

/-- Cochrane (2023), §20.2.2, p. 474: the trap step is continuous off `T`. -/
theorem trapStep_continuousAt (c : ℝ) {T t : ℝ} (ht : t ≠ T) :
    ContinuousAt (trapStep c T) t := by
  rcases lt_or_gt_of_ne ht with h | h
  · refine (continuousAt_const : ContinuousAt (fun _ : ℝ => c) t).congr ?_
    filter_upwards [Iio_mem_nhds h] with u (hu : u < T)
    simp [trapStep, hu]
  · refine (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t).congr ?_
    filter_upwards [Ioi_mem_nhds h] with u (hu : T < u)
    simp [trapStep, not_lt.2 hu.le]

/-- Cochrane (2023), §20.2.2, p. 474: scaling the step, `p · trapStep c T = trapStep (p c) T`. -/
theorem mul_trapStep (p c T t : ℝ) : p * trapStep c T t = trapStep (p * c) T t := by
  unfold trapStep
  split_ifs <;> simp

/-! ## The deterministic family in integral form -/

/-- Cochrane (2023), (20.5)–(20.6), p. 474: **the members of the family of Figure 20.4 solve the
model in integral form** on every interval `[s, t] ⊆ [0, ∞)` (across the forcing jump at `T`).
The integral form of `WerningModel.wPath_isPath`. -/
theorem wPath_intForm {σ κ ρ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (T u g πT : ℝ) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    wX σ κ ρ T u g πT t - wX σ κ ρ T u g πT s =
        ∫ r in s..t, σ * (0 - wPi σ κ ρ T u g πT r - trapStep u T r) ∧
      wPi σ κ ρ T u g πT t - wPi σ κ ρ T u g πT s =
        ∫ r in s..t, (ρ * wPi σ κ ρ T u g πT r - κ * (wX σ κ ρ T u g πT r + trapStep g T r)) := by
  have hp := wPath_isPath (ρ := ρ) hκ hσ T u g πT
  have hcx := wX_continuous σ κ ρ T u g πT hκ hσ
  have hcπ := wPi_continuous σ κ ρ T u g πT hκ hσ
  refine ⟨(integral_eq_of_hasDerivAt_off_countable_of_le _ _ hst (Set.countable_singleton T)
      hcx.continuousOn (fun r hr => (hp.2.2 r (hs.trans_lt hr.1.1) hr.2).1)
      (((intervalIntegrable_const.sub (hcπ.intervalIntegrable s t)).sub
        (trapStep_intervalIntegrable u T s t)).const_mul σ)).symm,
    (integral_eq_of_hasDerivAt_off_countable_of_le _ _ hst (Set.countable_singleton T)
      hcπ.continuousOn (fun r hr => (hp.2.2 r (hs.trans_lt hr.1.1) hr.2).2)
      (((hcπ.intervalIntegrable s t).const_mul ρ).sub
        (((hcx.intervalIntegrable s t).add (trapStep_intervalIntegrable g T s t)).const_mul
          κ))).symm⟩

/-! ## Every bounded stochastic equilibrium of the experiment -/

/-- Cochrane (2023), §20.2.2, p. 474 (tool): the zero shock process is regular. -/
theorem regular_zero (𝓕 : Filtration ℝ mΩ) : Regular 𝓕 (fun _ _ => (0 : ℝ)) :=
  ⟨fun _ => continuous_const, fun _ => stronglyMeasurable_const⟩

/-- Cochrane (2023), §20.2.2, p. 474 (tool): the zero shock process is `L¹`-bounded. -/
theorem bddL1_zero [IsFiniteMeasure P] : BddL1 P (fun _ _ => (0 : ℝ)) :=
  ⟨0, fun _ _ => ⟨integrable_zero _ _ _, by simp⟩⟩

/-- Cochrane (2023), §20.2.2, pp. 474–475: **conditional means of a bounded stochastic
equilibrium of the experiment.** For `A ∈ 𝓕_s` and `t ≥ s ≥ 0`,
`∫_A π_t = P(A)wPi(0)_t + e^{−λ^b(t−s)}(∫_A π_s − P(A)wPi(0)_s)` and
`κ(∫_A x_t − P(A)wX(0)_t) = λ^f(∫_A π_t − P(A)wPi(0)_t)`. -/
theorem setIntegral_trap [IsProbabilityMeasure P] {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} {x π : ℝ → Ω → ℝ} (hx : Regular 𝓕 x) (hxb : BddL1 P x)
    (hπ : Regular 𝓕 π) (hπb : BddL1 P π)
    (h : IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T) (fun _ _ => 0) x π)
    {s : ℝ} (hs : 0 ≤ s) {A : Set Ω} (hA : MeasurableSet[𝓕 s] A) (t : ℝ) (hst : s ≤ t) :
    ∫ ω in A, π t ω ∂P = P.real A * wPi σ κ ρ T u g 0 t +
        Real.exp (-(lamb ρ κ σ * (t - s))) * (∫ ω in A, π s ω ∂P - P.real A * wPi σ κ ρ T u g 0 s) ∧
      κ * (∫ ω in A, x t ω ∂P - P.real A * wX σ κ ρ T u g 0 t) =
        lamf ρ κ σ * (∫ ω in A, π t ω ∂P - P.real A * wPi σ κ ρ T u g 0 t) := by
  set p := P.real A
  set W0 := wPi σ κ ρ T u g 0
  set X0 := wX σ κ ρ T u g 0
  obtain ⟨Kx, hKx⟩ := hxb
  obtain ⟨Kπ, hKπ⟩ := hπb
  have hmx : ∀ t, Measurable (x t) := fun t => ((hx.2 t).mono (𝓕.le t)).measurable
  have hmπ : ∀ t, Measurable (π t) := fun t => ((hπ.2 t).mono (𝓕.le t)).measurable
  have hfin : ∀ a b : ℝ, IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Set.Ioc a b) :=
    fun _ _ => integrableOn_zero
  have hcm := fun t' (ht' : s ≤ t') => condMean_integral_eq (P := P) (ν := fun _ _ => 0)
    hfin (fun a b => trapStep_integrableOn u T measure_Ioc_lt_top.ne)
    (fun a b => trapStep_integrableOn g T measure_Ioc_lt_top.ne) (regular_zero 𝓕) bddL1_zero
    hx ⟨Kx, hKx⟩ hπ ⟨Kπ, hKπ⟩ h hs hA t' ht'
  simp only [integral_zero, add_zero, mul_zero] at hcm
  set mx : ℝ → ℝ := fun r => ∫ ω in A, x r ω ∂P
  set mπ : ℝ → ℝ := fun r => ∫ ω in A, π r ω ∂P
  -- integrability of the conditional means on compact intervals
  have hbx : ∀ r, 0 ≤ r → |mx r| ≤ Kx := fun r hr => abs_setIntegral_le hKx A hr
  have hbπ : ∀ r, 0 ≤ r → |mπ r| ≤ Kπ := fun r hr => abs_setIntegral_le hKπ A hr
  have hix : ∀ b, IntegrableOn mx (Set.Icc s b) := fun b =>
    Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
      (stronglyMeasurable_setIntegral hx.1 hmx A).aestronglyMeasurable (M := Kx)
      (ae_restrict_of_forall_mem measurableSet_Icc fun r hr => by
        rw [Real.norm_eq_abs]; exact hbx r (hs.trans hr.1))
  have hiπ : ∀ b, IntegrableOn mπ (Set.Icc s b) := fun b =>
    Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
      (stronglyMeasurable_setIntegral hπ.1 hmπ A).aestronglyMeasurable (M := Kπ)
      (ae_restrict_of_forall_mem measurableSet_Icc fun r hr => by
        rw [Real.norm_eq_abs]; exact hbπ r (hs.trans hr.1))
  have hGx : ∀ b, IntegrableOn (fun r => σ * (-mπ r - p * trapStep u T r)) (Set.Icc s b) :=
    fun b => (((hiπ b).neg).sub
      ((trapStep_integrableOn u T measure_Icc_lt_top.ne).const_mul p)).const_mul σ
  have hGπ : ∀ b, IntegrableOn (fun r => ρ * mπ r - κ * (mx r + p * trapStep g T r))
      (Set.Icc s b) := fun b => ((hiπ b).const_mul ρ).sub
        (((hix b).add ((trapStep_integrableOn g T measure_Icc_lt_top.ne).const_mul p)).const_mul
          κ)
  have hfx : ∀ t', s ≤ t' → mx t' - mx s = ∫ r in s..t', σ * (-mπ r - p * trapStep u T r) :=
    fun t' ht' => by
      rw [(hcm t' ht').1]
      refine intervalIntegral.integral_congr fun r _ => ?_
      simp only [mπ]
      ring
  have hfπ : ∀ t', s ≤ t' → mπ t' - mπ s =
      ∫ r in s..t', (ρ * mπ r - κ * (mx r + p * trapStep g T r)) := fun t' ht' => (hcm t' ht').2
  have hcx : ContinuousOn mx (Set.Ici s) := continuousOn_of_intForm hGx hfx
  have hcπ : ContinuousOn mπ (Set.Ici s) := continuousOn_of_intForm hGπ hfπ
  -- the deviations from `P(A)·(wX(0), wPi(0))` solve the unforced model
  have hW0c := wPi_continuous σ κ ρ T u g 0 hκ hσ
  have hX0c := wX_continuous σ κ ρ T u g 0 hκ hσ
  have hii : ∀ t', s ≤ t' → ∀ G : ℝ → ℝ, (∀ b, IntegrableOn G (Set.Icc s b)) →
      IntervalIntegrable G volume s t' := fun t' ht' G hG =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht').2 ((hG t').mono_set Set.Ioc_subset_Icc_self)
  have hdx : ∀ t', s ≤ t' → (mx t' - p * X0 t') - (mx s - p * X0 s) =
      ∫ r in s..t', -(σ * (mπ r - p * W0 r)) := fun t' ht' => by
    have hw := (wPath_intForm (ρ := ρ) hκ hσ T u g 0 hs ht').1
    have e : (mx t' - p * X0 t') - (mx s - p * X0 s) = (mx t' - mx s) - p * (X0 t' - X0 s) := by
      ring
    rw [e, hfx t' ht', hw, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hii t' ht' _ hGx)
        (((((intervalIntegrable_const.sub (hW0c.intervalIntegrable s t')).sub
          (trapStep_intervalIntegrable u T s t')).const_mul σ)).const_mul p)]
    refine intervalIntegral.integral_congr fun r _ => ?_
    ring
  have hdπ : ∀ t', s ≤ t' → (mπ t' - p * W0 t') - (mπ s - p * W0 s) =
      ∫ r in s..t', (ρ * (mπ r - p * W0 r) - κ * (mx r - p * X0 r)) := fun t' ht' => by
    have hw := (wPath_intForm (ρ := ρ) hκ hσ T u g 0 hs ht').2
    have e : (mπ t' - p * W0 t') - (mπ s - p * W0 s) = (mπ t' - mπ s) - p * (W0 t' - W0 s) := by
      ring
    rw [e, hfπ t' ht', hw, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hii t' ht' _ hGπ)
        ((((hW0c.intervalIntegrable s t').const_mul ρ).sub (((hX0c.intervalIntegrable s t').add
          (trapStep_intervalIntegrable g T s t')).const_mul κ)).const_mul p)]
    refine intervalIntegral.integral_congr fun r _ => ?_
    ring
  obtain ⟨⟨KX, hKX⟩, ⟨KW, hKW⟩⟩ := wPath_bdd (ρ := ρ) hκ hσ T u g 0
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hres := homog_intForm_bdd (s := s) (ρ := ρ) hσ hκ
    (dx := fun r => mx r - p * X0 r) (dπ := fun r => mπ r - p * W0 r)
    (hcx.sub (continuousOn_const.mul hX0c.continuousOn))
    (hcπ.sub (continuousOn_const.mul hW0c.continuousOn)) hdx hdπ
    (Kx := Kx + p * KX) (Kπ := Kπ + p * KW)
    (fun r hr => (abs_sub _ _).trans (add_le_add (hbx r (hs.trans hr)) (by
      rw [abs_mul, abs_of_nonneg hp0]
      exact mul_le_mul_of_nonneg_left (hKX r (hs.trans hr)) hp0)))
    (fun r hr => (abs_sub _ _).trans (add_le_add (hbπ r (hs.trans hr)) (by
      rw [abs_mul, abs_of_nonneg hp0]
      exact mul_le_mul_of_nonneg_left (hKW r (hs.trans hr)) hp0)))
  obtain ⟨h1, h2⟩ := hres t hst
  refine ⟨?_, h2⟩
  have : mπ t = p * W0 t + Real.exp (-(lamb ρ κ σ * (t - s))) * (mπ s - p * W0 s) := by
    linarith
  exact this

/-- Cochrane (2023), §20.2.2, pp. 474–475: **conditional expectations of inflation in every
bounded stochastic equilibrium of the experiment**:
`E_s π_t = wPi(0)_t + e^{−λ^b(t−s)}(π_s − wPi(0)_s)` almost surely, `0 ≤ s ≤ t`. -/
theorem condExp_pi_eq [IsProbabilityMeasure P] {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} {x π : ℝ → Ω → ℝ} (hx : Regular 𝓕 x) (hxb : BddL1 P x)
    (hπ : Regular 𝓕 π) (hπb : BddL1 P π)
    (h : IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T) (fun _ _ => 0) x π)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    P[π t | 𝓕 s] =ᵐ[P] fun ω => wPi σ κ ρ T u g 0 t +
      Real.exp (-(lamb ρ κ σ * (t - s))) * (π s ω - wPi σ κ ρ T u g 0 s) := by
  obtain ⟨Kπ, hKπ⟩ := hπb
  have hπs := (hKπ s hs).1
  have hF : Integrable (fun ω => wPi σ κ ρ T u g 0 t +
      Real.exp (-(lamb ρ κ σ * (t - s))) * (π s ω - wPi σ κ ρ T u g 0 s)) P :=
    (integrable_const _).add ((hπs.sub (integrable_const _)).const_mul _)
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hKπ t (hs.trans hst)).1
    (fun A _ _ => hF.integrableOn) (fun A hA _ => ?_) ?_).symm
  · have i1 : Integrable (fun ω => Real.exp (-(lamb ρ κ σ * (t - s))) *
        (π s ω - wPi σ κ ρ T u g 0 s)) (P.restrict A) :=
      ((hπs.sub (integrable_const _)).const_mul _).integrableOn
    have i2 : Integrable (fun ω => π s ω - wPi σ κ ρ T u g 0 s) (P.restrict A) :=
      (hπs.sub (integrable_const _)).integrableOn
    rw [(setIntegral_trap hσ hκ hx hxb hπ ⟨Kπ, hKπ⟩ h hs hA t hst).1,
      integral_add (integrable_const _) i1, integral_const_mul,
      integral_sub hπs.integrableOn (integrable_const _), setIntegral_const,
      setIntegral_const, smul_eq_mul, smul_eq_mul]
  · exact (stronglyMeasurable_const.add (stronglyMeasurable_const.mul
      ((hπ.2 s).sub stronglyMeasurable_const))).aestronglyMeasurable

/-- Cochrane (2023), (20.10), p. 475: **conditional expectations of output in every bounded
stochastic equilibrium of the experiment**:
`E_s x_t = wX(0)_t + (λ^f/κ)e^{−λ^b(t−s)}(π_s − wPi(0)_s)` almost surely, `0 ≤ s ≤ t`. -/
theorem condExp_x_eq [IsProbabilityMeasure P] {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} {x π : ℝ → Ω → ℝ} (hx : Regular 𝓕 x) (hxb : BddL1 P x)
    (hπ : Regular 𝓕 π) (hπb : BddL1 P π)
    (h : IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T) (fun _ _ => 0) x π)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    P[x t | 𝓕 s] =ᵐ[P] fun ω => wX σ κ ρ T u g 0 t + lamf ρ κ σ / κ *
      (Real.exp (-(lamb ρ κ σ * (t - s))) * (π s ω - wPi σ κ ρ T u g 0 s)) := by
  obtain ⟨Kπ, hKπ⟩ := hπb
  obtain ⟨Kx, hKx⟩ := hxb
  have hπs := (hKπ s hs).1
  have hF : Integrable (fun ω => wX σ κ ρ T u g 0 t + lamf ρ κ σ / κ *
      (Real.exp (-(lamb ρ κ σ * (t - s))) * (π s ω - wPi σ κ ρ T u g 0 s))) P :=
    (integrable_const _).add (((hπs.sub (integrable_const _)).const_mul _).const_mul _)
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hKx t (hs.trans hst)).1
    (fun A _ _ => hF.integrableOn) (fun A hA _ => ?_) ?_).symm
  · obtain ⟨h1, h2⟩ := setIntegral_trap hσ hκ hx ⟨Kx, hKx⟩ hπ ⟨Kπ, hKπ⟩ h hs hA t hst
    have i1 : Integrable (fun ω => lamf ρ κ σ / κ * (Real.exp (-(lamb ρ κ σ * (t - s))) *
        (π s ω - wPi σ κ ρ T u g 0 s))) (P.restrict A) :=
      (((hπs.sub (integrable_const _)).const_mul _).const_mul _).integrableOn
    rw [integral_add (integrable_const _) i1,
      integral_const_mul, integral_const_mul, integral_sub hπs.integrableOn (integrable_const _),
      setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul]
    rw [h1] at h2
    field_simp
    linear_combination -h2
  · exact (stronglyMeasurable_const.add (stronglyMeasurable_const.mul (stronglyMeasurable_const.mul
      ((hπ.2 s).sub stronglyMeasurable_const)))).aestronglyMeasurable

/-- Cochrane (2023), §20.2.2, p. 475 ("we set to zero … forward-explosive equilibria"),
**state by state**: in every bounded stochastic equilibrium of the experiment,
`x_s = wX(0)_s + (λ^f/κ)(π_s − wPi(0)_s)` almost surely at every date `s ≥ 0` — output is pinned
by inflation exactly as in the deterministic family (the combination `λ^f π − κ x` carries no
uncertainty). -/
theorem x_eq_of_pi [IsProbabilityMeasure P] {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} {x π : ℝ → Ω → ℝ} (hx : Regular 𝓕 x) (hxb : BddL1 P x)
    (hπ : Regular 𝓕 π) (hπb : BddL1 P π)
    (h : IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T) (fun _ _ => 0) x π)
    {s : ℝ} (hs : 0 ≤ s) :
    x s =ᵐ[P] fun ω => wX σ κ ρ T u g 0 s +
      lamf ρ κ σ / κ * (π s ω - wPi σ κ ρ T u g 0 s) := by
  have hc := condExp_x_eq hσ hκ hx hxb hπ hπb h hs le_rfl
  obtain ⟨Kx, hKx⟩ := hxb
  rw [condExp_of_stronglyMeasurable (𝓕.le s) (hx.2 s) (hKx s hs).1] at hc
  filter_upwards [hc] with ω hω
  rw [hω]
  simp

/-- Cochrane (2023), (20.10) and §20.2.4, p. 479: **the response of output to any shock is
`λ^f/κ` times the response of inflation** (the deterministic ratio of `wX_shift` to
`wPi_shift`): `x_t − E_s x_t = (λ^f/κ)(π_t − E_s π_t)` almost surely. -/
theorem innovation_x_eq [IsProbabilityMeasure P] {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} {x π : ℝ → Ω → ℝ} (hx : Regular 𝓕 x) (hxb : BddL1 P x)
    (hπ : Regular 𝓕 π) (hπb : BddL1 P π)
    (h : IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T) (fun _ _ => 0) x π)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (fun ω => x t ω - P[x t | 𝓕 s] ω) =ᵐ[P]
      fun ω => lamf ρ κ σ / κ * (π t ω - P[π t | 𝓕 s] ω) := by
  filter_upwards [x_eq_of_pi hσ hκ hx hxb hπ hπb h (hs.trans hst),
    condExp_x_eq hσ hκ hx hxb hπ hπb h hs hst, condExp_pi_eq hσ hκ hx hxb hπ hπb h hs hst]
    with ω h1 h2 h3
  rw [h1, h2, h3]
  ring

/-- Cochrane (2023), §20.2.4, p. 479 ("inflation at time 0 is sensitive to its expectation at
time T"), under uncertainty: **news propagates as the deterministic response.** For
`0 ≤ r ≤ s ≤ t`, `E_s π_t − E_r π_t = e^{−λ^b(t−s)}(π_s − E_r π_s)` almost surely: the
revision of expected inflation at `t` is the news about `π_s` times `e^{−λ^b(t−s)}`, which is
how two deterministic family members differ (`wPi_shift`). -/
theorem revision_pi_eq [IsProbabilityMeasure P] {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} {x π : ℝ → Ω → ℝ} (hx : Regular 𝓕 x) (hxb : BddL1 P x)
    (hπ : Regular 𝓕 π) (hπb : BddL1 P π)
    (h : IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T) (fun _ _ => 0) x π)
    {r s t : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hst : s ≤ t) :
    (fun ω => P[π t | 𝓕 s] ω - P[π t | 𝓕 r] ω) =ᵐ[P]
      fun ω => Real.exp (-(lamb ρ κ σ * (t - s))) * (π s ω - P[π s | 𝓕 r] ω) := by
  filter_upwards [condExp_pi_eq hσ hκ hx hxb hπ hπb h (hr.trans hrs) hst,
    condExp_pi_eq hσ hκ hx hxb hπ hπb h hr (hrs.trans hst),
    condExp_pi_eq hσ hκ hx hxb hπ hπb h hr hrs] with ω h1 h2 h3
  rw [h1, h2, h3]
  have e : Real.exp (-(lamb ρ κ σ * (t - r))) =
      Real.exp (-(lamb ρ κ σ * (t - s))) * Real.exp (-(lamb ρ κ σ * (s - r))) := by
    rw [← Real.exp_add]
    ring_nf
  rw [e]
  ring

/-- Cochrane (2023), §20.2.2, pp. 475–476 (Figure 20.4) and §20.2.4, p. 479, under uncertainty:
**the bounded equilibria are the family indexed by `π_T`, with `π_T` replaced by its conditional
expectation.** For `0 ≤ s ≤ T` and `s ≤ t`, `E_s π_t = wPi(E_s π_T)_t` almost surely. -/
theorem condExp_pi_eq_wPi [IsProbabilityMeasure P] {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} {x π : ℝ → Ω → ℝ} (hx : Regular 𝓕 x) (hxb : BddL1 P x)
    (hπ : Regular 𝓕 π) (hπb : BddL1 P π)
    (h : IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T) (fun _ _ => 0) x π)
    {s t : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (hst : s ≤ t) :
    P[π t | 𝓕 s] =ᵐ[P] fun ω => wPi σ κ ρ T u g (P[π T | 𝓕 s] ω) t := by
  filter_upwards [condExp_pi_eq hσ hκ hx hxb hπ hπb h hs hst,
    condExp_pi_eq hσ hκ hx hxb hπ hπb h hs hsT] with ω h1 h2
  rw [h1, wPi_shift σ κ ρ T u g (P[π T | 𝓕 s] ω) t, h2, wPi_T hκ hσ, zero_add]
  have e : Real.exp (-(lamb ρ κ σ * (t - s))) =
      Real.exp (-(lamb ρ κ σ * (T - s))) * Real.exp (lamb ρ κ σ * (T - t)) := by
    rw [← Real.exp_add]
    ring_nf
  rw [e]
  ring

/-- Cochrane (2023), (20.10), p. 475, under uncertainty: for `0 ≤ s ≤ T` and `s ≤ t`,
`E_s x_t = wX(E_s π_T)_t` almost surely. -/
theorem condExp_x_eq_wX [IsProbabilityMeasure P] {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} {x π : ℝ → Ω → ℝ} (hx : Regular 𝓕 x) (hxb : BddL1 P x)
    (hπ : Regular 𝓕 π) (hπb : BddL1 P π)
    (h : IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T) (fun _ _ => 0) x π)
    {s t : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (hst : s ≤ t) :
    P[x t | 𝓕 s] =ᵐ[P] fun ω => wX σ κ ρ T u g (P[π T | 𝓕 s] ω) t := by
  filter_upwards [condExp_x_eq hσ hκ hx hxb hπ hπb h hs hst,
    condExp_pi_eq hσ hκ hx hxb hπ hπb h hs hsT] with ω h1 h2
  rw [h1, wX_shift σ κ ρ T u g (P[π T | 𝓕 s] ω) t, h2, wPi_T hκ hσ, zero_add]
  have e : Real.exp (-(lamb ρ κ σ * (t - s))) =
      Real.exp (-(lamb ρ κ σ * (T - s))) * Real.exp (lamb ρ κ σ * (T - t)) := by
    rw [← Real.exp_add]
    ring_nf
  rw [e]
  ring

/-- Cochrane (2023), §20.2.2, pp. 475–476 (Figure 20.4), under uncertainty: **the mean path of
every bounded stochastic equilibrium is the member of the deterministic family indexed by
`E π_T`**: `E π_t = wPi(E π_T)_t` and `E x_t = wX(E π_T)_t` for `t ≥ 0` (`T ≥ 0`). -/
theorem mean_eq_wPi [IsProbabilityMeasure P] {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} {x π : ℝ → Ω → ℝ} (hx : Regular 𝓕 x) (hxb : BddL1 P x)
    (hπ : Regular 𝓕 π) (hπb : BddL1 P π)
    (h : IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T) (fun _ _ => 0) x π)
    (hT : 0 ≤ T) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, π t ω ∂P = wPi σ κ ρ T u g (∫ ω, π T ω ∂P) t ∧
      ∫ ω, x t ω ∂P = wX σ κ ρ T u g (∫ ω, π T ω ∂P) t := by
  have hA : MeasurableSet[𝓕 0] (Set.univ : Set Ω) := MeasurableSet.univ
  obtain ⟨a1, a2⟩ := setIntegral_trap hσ hκ hx hxb hπ hπb h le_rfl hA t ht
  obtain ⟨b1, -⟩ := setIntegral_trap hσ hκ hx hxb hπ hπb h le_rfl hA T hT
  simp only [Measure.restrict_univ, probReal_univ, one_mul, sub_zero] at a1 a2 b1
  rw [wPi_T hκ hσ, zero_add] at b1
  have e : Real.exp (-(lamb ρ κ σ * t)) =
      Real.exp (-(lamb ρ κ σ * T)) * Real.exp (lamb ρ κ σ * (T - t)) := by
    rw [← Real.exp_add]
    ring_nf
  refine ⟨?_, ?_⟩
  · rw [wPi_shift, a1, b1, e]
    ring
  · rw [wX_shift, b1]
    rw [a1, e] at a2
    field_simp
    linear_combination a2

/-! ## The deterministic case -/

/-- Cochrane (2023), (20.5)–(20.6), p. 474 (tool): for a process constant in `ω`, `E_t dZ = D dt`
holds iff the deterministic integral equation holds. -/
theorem expDrift_det_iff [IsProbabilityMeasure P] {𝓕 : Filtration ℝ mΩ} {z d : ℝ → ℝ} :
    ExpDrift P 𝓕 (fun t _ => z t) (fun r _ => d r) ↔
      ∀ s t, 0 ≤ s → s ≤ t → z t - z s = ∫ r in s..t, d r := by
  constructor
  · intro h s t hs hst
    obtain ⟨-, hce⟩ := h s t hs hst
    rw [condExp_const (𝓕.le s)] at hce
    obtain ⟨ω, hω⟩ := hce.exists
    have := sub_eq_zero.1 hω
    linarith
  · intro h s t hs hst
    refine ⟨integrable_const _, ?_⟩
    rw [condExp_const (𝓕.le s)]
    exact Eventually.of_forall fun _ => by simp [h s t hs hst]

/-- Cochrane (2023), (20.5)–(20.6), p. 474, with no uncertainty: **a deterministic continuous
path is a stochastic equilibrium of the experiment iff it is a path (`IsPath`) of
WerningModel.** -/
theorem isStochEqm_det_iff [IsProbabilityMeasure P] {σ ρ κ : ℝ} {𝓕 : Filtration ℝ mΩ}
    {T u g : ℝ} {x π : ℝ → ℝ} (hxc : Continuous x) (hπc : Continuous π) :
    IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T) (fun _ _ => 0)
        (fun t _ => x t) (fun t _ => π t) ↔
      IsPath σ ρ κ (fun _ => 0) (trapStep u T) (trapStep g T) {T} x π := by
  unfold IsStochEqm
  simp only [add_zero]
  rw [expDrift_det_iff (z := x) (d := fun r => σ * (0 - π r - trapStep u T r)),
    expDrift_det_iff (z := π) (d := fun r => ρ * π r - κ * (x r + trapStep g T r))]
  have hGx : Continuous fun r => σ * (0 - π r) := by fun_prop
  have hGπ : Continuous fun r => ρ * π r - κ * x r := by fun_prop
  have iGx : ∀ a b, IntervalIntegrable (fun r => σ * (0 - π r - trapStep u T r)) volume a b :=
    fun a b => ((intervalIntegrable_const.sub (hπc.intervalIntegrable a b)).sub
      (trapStep_intervalIntegrable u T a b)).const_mul σ
  have iGπ : ∀ a b, IntervalIntegrable (fun r => ρ * π r - κ * (x r + trapStep g T r)) volume
      a b := fun a b => ((hπc.intervalIntegrable a b).const_mul ρ).sub
        (((hxc.intervalIntegrable a b).add (trapStep_intervalIntegrable g T a b)).const_mul κ)
  have mGx : StronglyMeasurable fun r => σ * (0 - π r - trapStep u T r) :=
    (((measurable_const.sub hπc.measurable).sub (trapStep_measurable u T)).const_mul
      σ).stronglyMeasurable
  have mGπ : StronglyMeasurable fun r => ρ * π r - κ * (x r + trapStep g T r) :=
    ((hπc.measurable.const_mul ρ).sub ((hxc.measurable.add (trapStep_measurable g T)).const_mul
      κ)).stronglyMeasurable
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hxc.continuousOn, hπc.continuousOn, fun t ht htT => ?_⟩
    have htT' : t ≠ T := htT
    have hev1 : (fun v => x 0 + ∫ r in (0 : ℝ)..v, σ * (0 - π r - trapStep u T r)) =ᶠ[𝓝 t] x := by
      filter_upwards [Ioi_mem_nhds ht] with v hv
      linarith [h1 0 v le_rfl hv.le]
    have hev2 : (fun v => π 0 + ∫ r in (0 : ℝ)..v, (ρ * π r - κ * (x r + trapStep g T r)))
        =ᶠ[𝓝 t] π := by
      filter_upwards [Ioi_mem_nhds ht] with v hv
      linarith [h2 0 v le_rfl hv.le]
    have c1 : ContinuousAt (fun r => σ * (0 - π r - trapStep u T r)) t :=
      ((continuousAt_const.sub hπc.continuousAt).sub (trapStep_continuousAt u htT')).const_mul σ
    have c2 : ContinuousAt (fun r => ρ * π r - κ * (x r + trapStep g T r)) t :=
      (hπc.continuousAt.const_mul ρ).sub
        ((hxc.continuousAt.add (trapStep_continuousAt g htT')).const_mul κ)
    exact ⟨((intervalIntegral.integral_hasDerivAt_right (iGx 0 t)
        mGx.stronglyMeasurableAtFilter c1).const_add (x 0)).congr_of_eventuallyEq hev1.symm,
      ((intervalIntegral.integral_hasDerivAt_right (iGπ 0 t)
        mGπ.stronglyMeasurableAtFilter c2).const_add (π 0)).congr_of_eventuallyEq hev2.symm⟩
  · intro hp
    refine ⟨fun s t hs hst => ?_, fun s t hs hst => ?_⟩
    · exact (integral_eq_of_hasDerivAt_off_countable_of_le _ _ hst (Set.countable_singleton T)
        hxc.continuousOn (fun r hr => (hp.2.2 r (hs.trans_lt hr.1.1) hr.2).1) (iGx s t)).symm
    · exact (integral_eq_of_hasDerivAt_off_countable_of_le _ _ hst (Set.countable_singleton T)
        hπc.continuousOn (fun r hr => (hp.2.2 r (hs.trans_lt hr.1.1) hr.2).2) (iGπ s t)).symm

/-- Cochrane (2023), §20.2.2, pp. 474–475, with no uncertainty: **the deterministic bounded
stochastic equilibria are exactly the family of `bdd_path_iff`** — a deterministic continuous
`(x, π)` is an `L¹`-bounded stochastic equilibrium of the experiment iff it equals
`(wX, wPi)(π_T)` on `[0, ∞)` for some `π_T`. -/
theorem det_bdd_iff [IsProbabilityMeasure P] {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} {x π : ℝ → ℝ} (hxc : Continuous x) (hπc : Continuous π) :
    (IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T) (fun _ _ => 0)
        (fun t _ => x t) (fun t _ => π t) ∧ BddL1 P (fun t _ => x t) ∧
        BddL1 P (fun t _ => π t)) ↔
      ∃ πT, ∀ t, 0 ≤ t → π t = wPi σ κ ρ T u g πT t ∧ x t = wX σ κ ρ T u g πT t := by
  have hb : ∀ f : ℝ → ℝ, BddL1 P (fun t _ => f t) ↔ BddOnIci f := fun f => by
    constructor
    · rintro ⟨K, hK⟩
      exact ⟨K, fun t ht => by simpa using (hK t ht).2⟩
    · rintro ⟨K, hK⟩
      exact ⟨K, fun t ht => ⟨integrable_const _, by simpa using hK t ht⟩⟩
  rw [isStochEqm_det_iff hxc hπc, hb, hb, ← bdd_path_iff hκ hσ]

end Cochrane.ZeroBound.TidyR7StochWerningTrap
