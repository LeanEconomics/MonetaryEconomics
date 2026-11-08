/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.WerningModel
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Werning model under uncertainty: `E_t d`-equations and certainty equivalence

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §§20.2.2–20.2.5,
pp. 474–482, equations (20.5)–(20.10).

Under uncertainty the IS and Phillips curves (20.5)–(20.6) are expectational:
`E_t dx_t = σ(i_t − π_t − u_{r,t})dt` and `E_t dπ_t = (ρπ_t − κ(x_t + g_t))dt`. We read
`E_t dZ_t = D_t dt` in integrated form, with Mathlib's conditional expectation, as
`E_s[Z_t − Z_s − ∫_s^t D_r dr] = 0` for all `0 ≤ s ≤ t` (`ExpDrift`): the expected change of
`Z` over every future interval is the expected integrated drift. This needs no stochastic
integral, and it is what the model's expectational equations say; it is the integrated form of
the martingale property of `Z_t − Z_0 − ∫_0^t D`. The natural rate is `u_r = u + ν` with a
deterministic part `u` and a random shock process `ν`; `i` and `g` are deterministic.

The book's selection "do not explode as time increases" (p. 474) is read under uncertainty as
boundedness of first moments, `sup_{t≥0} E|Z_t| < ∞` (`BddL1`), the weakest of the natural
notions; bounded second moments (`BddL2`) imply it (`BddL2.bddL1`). Uniqueness is proved under
`BddL1` and the explicit solutions of TidyR7StochWerningExist are `BddL2`, so the two notions
select the same equilibria. Uniform (`L^∞`) boundedness is a different and stronger notion:
TidyR7StochWerningExist shows that the explicit equilibria with a constant non-zero inflation
innovation loading (Ornstein–Uhlenbeck inflation, bounded in `L²`) are not bounded in `L^∞`, so
a uniform reading of "do not explode" would discard equilibria that the moment reading keeps.
(Their paths are also almost surely unbounded on `[0, ∞)`; that recurrence statement is not
formalised here.)

## Main results

* `ExpDriftFrom`, `ExpDrift`, `Regular`, `BddL1`, `BddL2`, `IsStochEqm`; `BddL2.bddL1`.
* `setIntegral_expDrift`: the expected-increment form of `E_t dZ = D dt` — for `A ∈ 𝓕_s`,
  `∫_A Z_t − ∫_A Z_s = ∫_s^t ∫_A D_r dr` (Fubini).
* **`condMean_integral_eq` (certainty equivalence)**: in every stochastic equilibrium with
  continuous adapted `L¹`-bounded paths, the conditional-mean paths `r ↦ ∫_A x_r`,
  `r ↦ ∫_A π_r` (`A ∈ 𝓕_s`) solve the deterministic model (20.5)–(20.6) on `[s, ∞)` with the
  conditional-mean forcing. No covariation (Itô) correction appears: the model is linear.
* Deterministic tools on `[s, ∞)`: `hasDerivAt_of_intForm`, `continuousOn_of_intForm`, and
  `homog_intForm_bdd` (bounded solutions of the unforced model in integral form are
  `π_t = e^{−λ^b(t−s)}π_s`, `κx = λ^f π`).

The trap experiment is characterised in TidyR7StochWerningTrap, its explicit equilibria on a
Brownian motion are in TidyR7StochWerningExist, selection ((20.7), `π_T`, `π_0`) in
TidyR7StochWerningSelect, and natural-rate shocks in TidyR7StochWerningNatural and
TidyR7StochWerningNaturalExist.
-/

namespace Cochrane.ZeroBound.TidyR7StochWerning

open MeasureTheory Filter Topology
open Cochrane.ZeroBound.ContinuousTimeNK Cochrane.ZeroBound.WerningModel

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ## Definitions -/

/-- Cochrane (2023), (20.5)–(20.7), p. 474, under uncertainty: **`E_t dZ_t = D_t dt` from date
`a` on**, read as `E_s[Z_t − Z_s − ∫_s^t D_r dr] = 0` for all `a ≤ s ≤ t` (the bracket
integrable). -/
def ExpDriftFrom (P : Measure Ω) (𝓕 : Filtration ℝ mΩ) (a : ℝ) (Z D : ℝ → Ω → ℝ) : Prop :=
  ∀ s t, a ≤ s → s ≤ t →
    Integrable (fun ω => Z t ω - Z s ω - ∫ r in s..t, D r ω) P ∧
      P[fun ω => Z t ω - Z s ω - ∫ r in s..t, D r ω | 𝓕 s] =ᵐ[P] 0

/-- Cochrane (2023), (20.5)–(20.6), p. 474, under uncertainty: **`E_t dZ_t = D_t dt`**, read as
`E_s[Z_t − Z_s − ∫_s^t D_r dr] = 0` for all `0 ≤ s ≤ t` (the bracket integrable). -/
def ExpDrift (P : Measure Ω) (𝓕 : Filtration ℝ mΩ) (Z D : ℝ → Ω → ℝ) : Prop :=
  ExpDriftFrom P 𝓕 0 Z D

/-- Cochrane (2023), §20.2.2, p. 474: a regular process — continuous paths and adapted to `𝓕`
(`Z_t` is known at `t`). -/
def Regular (𝓕 : Filtration ℝ mΩ) (Z : ℝ → Ω → ℝ) : Prop :=
  (∀ ω, Continuous fun t => Z t ω) ∧ ∀ t, StronglyMeasurable[𝓕 t] (Z t)

/-- Cochrane (2023), §20.2.2, p. 474 ("do not explode as time increases"), under uncertainty:
bounded first moments on `[0, ∞)`. -/
def BddL1 (P : Measure Ω) (Z : ℝ → Ω → ℝ) : Prop :=
  ∃ K, ∀ t, 0 ≤ t → Integrable (Z t) P ∧ ∫ ω, |Z t ω| ∂P ≤ K

/-- Cochrane (2023), §20.2.2, p. 474, under uncertainty: bounded in mean square (in `L²`) on
`[0, ∞)`. -/
def BddL2 (P : Measure Ω) (Z : ℝ → Ω → ℝ) : Prop :=
  ∃ K, ∀ t, 0 ≤ t → MemLp (Z t) 2 P ∧ ∫ ω, Z t ω ^ 2 ∂P ≤ K

/-- Cochrane (2023), (20.5)–(20.6), p. 474, under uncertainty: `(x, π)` is a **stochastic
equilibrium** with deterministic interest rate `i`, natural rate `u + ν` (`ν` a random shock)
and disturbance `g`: `E_t dx = σ(i − π − (u + ν))dt` and `E_t dπ = (ρπ − κ(x + g))dt`. -/
def IsStochEqm (σ ρ κ : ℝ) (P : Measure Ω) (𝓕 : Filtration ℝ mΩ) (i u g : ℝ → ℝ)
    (ν x π : ℝ → Ω → ℝ) : Prop :=
  ExpDrift P 𝓕 x (fun r ω => σ * (i r - π r ω - (u r + ν r ω))) ∧
    ExpDrift P 𝓕 π (fun r ω => ρ * π r ω - κ * (x r ω + g r))

/-! ## Tools -/

/-- Cochrane (2023), §20.2.2, p. 474: on a probability space, bounded in mean square implies
bounded first moments (`|z| ≤ (1 + z²)/2`). -/
theorem BddL2.bddL1 [IsProbabilityMeasure P] {Z : ℝ → Ω → ℝ} (h : BddL2 P Z) : BddL1 P Z := by
  obtain ⟨K, hK⟩ := h
  refine ⟨(1 + K) / 2, fun t ht => ⟨(hK t ht).1.integrable one_le_two, ?_⟩⟩
  have hsq := (hK t ht).1.integrable_sq
  calc ∫ ω, |Z t ω| ∂P ≤ ∫ ω, (1 + Z t ω ^ 2) / 2 ∂P := by
        refine integral_mono ((hK t ht).1.integrable one_le_two).abs
          (((integrable_const 1).add hsq).div_const 2) fun ω => ?_
        nlinarith [sq_nonneg (|Z t ω| - 1), sq_abs (Z t ω)]
    _ = (1 + ∫ ω, Z t ω ^ 2 ∂P) / 2 := by
        rw [integral_div, integral_add (integrable_const 1) hsq]
        simp
    _ ≤ (1 + K) / 2 := by linarith [(hK t ht).2]

/-- Cochrane (2023), §20.2.2, p. 474 (tool): a process with continuous paths, measurable
sections and bounded first moments on `[0, ∞)` is integrable on `(a, b] × Ω` for `a ≥ 0`. -/
theorem integrable_prod_proc [IsFiniteMeasure P] {Z : ℝ → Ω → ℝ}
    (hc : ∀ ω, Continuous fun t => Z t ω) (hm : ∀ t, Measurable (Z t)) {K : ℝ}
    (hK : ∀ t, 0 ≤ t → Integrable (Z t) P ∧ ∫ ω, |Z t ω| ∂P ≤ K) {a b : ℝ} (ha : 0 ≤ a) :
    Integrable (Function.uncurry Z) ((volume.restrict (Set.Ioc a b)).prod P) := by
  have hmeas : Measurable (Function.uncurry Z) :=
    measurable_uncurry_of_continuous_of_measurable hc hm
  refine (integrable_prod_iff hmeas.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · exact ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => (hK r (ha.trans hr.1.le)).1
  · refine Integrable.of_bound ?_ K (ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => ?_)
    · exact (StronglyMeasurable.integral_prod_right (ν := P)
        (f := fun r ω => ‖Z r ω‖) hmeas.norm.stronglyMeasurable).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      simpa only [Function.uncurry_apply_pair, Real.norm_eq_abs] using
        (hK r (ha.trans hr.1.le)).2

/-- Cochrane (2023), §20.2.2, p. 474 (tool): a deterministic function integrable on `(a, b]`
is integrable on `(a, b] × Ω`. -/
theorem integrable_prod_det [IsFiniteMeasure P] {f : ℝ → ℝ} {a b : ℝ}
    (hf : IntegrableOn f (Set.Ioc a b)) :
    Integrable (fun p : ℝ × Ω => f p.1) ((volume.restrict (Set.Ioc a b)).prod P) :=
  hf.comp_fst P

/-- Cochrane (2023), §20.2.2, p. 474 (tool): the conditional mean `r ↦ ∫_A Z_r` of a process
with continuous paths and measurable sections is measurable in `r`. -/
theorem stronglyMeasurable_setIntegral [IsFiniteMeasure P] {Z : ℝ → Ω → ℝ}
    (hc : ∀ ω, Continuous fun t => Z t ω) (hm : ∀ t, Measurable (Z t)) (A : Set Ω) :
    StronglyMeasurable fun r => ∫ ω in A, Z r ω ∂P :=
  StronglyMeasurable.integral_prod_right (ν := P.restrict A)
    (measurable_uncurry_of_continuous_of_measurable hc hm).stronglyMeasurable

/-- Cochrane (2023), §20.2.2, p. 474 (tool): a conditional mean of an `L¹`-bounded process is
bounded by the `L¹` bound. -/
theorem abs_setIntegral_le {Z : ℝ → Ω → ℝ} {K : ℝ}
    (hK : ∀ t, 0 ≤ t → Integrable (Z t) P ∧ ∫ ω, |Z t ω| ∂P ≤ K) (A : Set Ω) {t : ℝ}
    (ht : 0 ≤ t) : |∫ ω in A, Z t ω ∂P| ≤ K :=
  (abs_integral_le_integral_abs).trans
    ((setIntegral_le_integral (hK t ht).1.abs (Eventually.of_forall fun _ => abs_nonneg _)).trans
      (hK t ht).2)

/-- **Cochrane (2023), (20.5)–(20.6), p. 474: the expected-increment form of `E_t dZ = D dt`.**
For `a ≤ s ≤ t` and `A ∈ 𝓕_s`, `∫_A Z_t − ∫_A Z_s = ∫_s^t (∫_A D_r) dr`. -/
theorem setIntegral_expDrift [IsFiniteMeasure P] {𝓕 : Filtration ℝ mΩ} {a : ℝ}
    {Z D : ℝ → Ω → ℝ} (hZ : ExpDriftFrom P 𝓕 a Z D) {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t)
    {A : Set Ω}
    (hA : MeasurableSet[𝓕 s] A) (hZs : Integrable (Z s) P) (hZt : Integrable (Z t) P)
    (hD : Integrable (Function.uncurry D) ((volume.restrict (Set.Ioc s t)).prod P)) :
    ∫ ω in A, Z t ω ∂P - ∫ ω in A, Z s ω ∂P = ∫ r in s..t, ∫ ω in A, D r ω ∂P := by
  obtain ⟨hint, hce⟩ := hZ s t hs hst
  have hA' : MeasurableSet A := 𝓕.le s _ hA
  have h0 : ∫ ω in A, (Z t ω - Z s ω - ∫ r in s..t, D r ω) ∂P = 0 := by
    rw [← setIntegral_condExp (𝓕.le s) hint hA, integral_congr_ae (ae_restrict_of_ae hce)]
    simp
  have hI : Integrable (fun ω => ∫ r in s..t, D r ω) P :=
    ((hZt.sub hZs).sub hint).congr (Eventually.of_forall fun ω => by simp)
  have hZts : Integrable (fun ω => Z t ω - Z s ω) P := hZt.sub hZs
  rw [integral_sub hZts.integrableOn hI.integrableOn,
    integral_sub hZt.integrableOn hZs.integrableOn] at h0
  have hswap : ∫ ω in A, (∫ r in s..t, D r ω) ∂P = ∫ r in s..t, ∫ ω in A, D r ω ∂P := by
    simp only [intervalIntegral.integral_of_le hst]
    have hDA : Integrable (Function.uncurry D)
        ((volume.restrict (Set.Ioc s t)).prod (P.restrict A)) := by
      have he : (volume.restrict (Set.Ioc s t)).prod (P.restrict A)
          = ((volume.restrict (Set.Ioc s t)).prod P).restrict (Set.univ ×ˢ A) := by
        rw [← Measure.prod_restrict, Measure.restrict_univ]
      rw [he]
      exact hD.restrict
    exact (integral_integral_swap hDA).symm
  linarith

/-! ## Deterministic tools: integral form and derivatives -/

/-- Cochrane (2023), §20.2.2, p. 475 (tool): if `f_t − f_s = ∫_s^t G` on `[s, ∞)` with `G`
continuous there, then `f' = G` on `(s, ∞)`.
From Mathlib `intervalIntegral.integral_hasDerivAt_right`. -/
theorem hasDerivAt_of_intForm {f G : ℝ → ℝ} {s : ℝ} (hG : ContinuousOn G (Set.Ici s))
    (hf : ∀ t, s ≤ t → f t - f s = ∫ r in s..t, G r) {t : ℝ} (ht : s < t) :
    HasDerivAt f (G t) t := by
  have hev : (fun u => f s + ∫ r in s..u, G r) =ᶠ[𝓝 t] f := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    linarith [hf u (le_of_lt hu)]
  have hint : IntervalIntegrable G volume s t :=
    (hG.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc ht.le
  have hmeas : StronglyMeasurableAtFilter G (𝓝 t) volume :=
    (hG.mono Set.Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi t ht
  have hca : ContinuousAt G t := hG.continuousAt (Ici_mem_nhds ht)
  exact ((intervalIntegral.integral_hasDerivAt_right hint hmeas hca).const_add
    (f s)).congr_of_eventuallyEq hev.symm

/-- Cochrane (2023), §20.2.2, p. 475 (tool): if `f_t − f_s = ∫_s^t G` on `[s, ∞)` with `G`
integrable on every `[s, b]`, then `f` is continuous on `[s, ∞)`.
From Mathlib `intervalIntegral.continuousOn_primitive_interval`. -/
theorem continuousOn_of_intForm {f G : ℝ → ℝ} {s : ℝ}
    (hG : ∀ b, IntegrableOn G (Set.Icc s b)) (hf : ∀ t, s ≤ t → f t - f s = ∫ r in s..t, G r) :
    ContinuousOn f (Set.Ici s) := by
  intro x hx
  have hx' : s ≤ x := hx
  have hb : s ≤ x + 1 := by linarith
  have hprim := intervalIntegral.continuousOn_primitive_interval (a := s) (b := x + 1)
    (μ := volume) (by rw [Set.uIcc_of_le hb]; exact hG (x + 1))
  rw [Set.uIcc_of_le hb] at hprim
  have hcont : ContinuousOn f (Set.Icc s (x + 1)) :=
    ((continuousOn_const (c := f s)).add hprim).congr fun u hu => by
      have := hf u hu.1
      change f u = f s + ∫ r in s..u, G r
      linarith
  have hmem : Set.Icc s (x + 1) ∈ 𝓝[Set.Ici s] x := by
    rw [← Set.Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
  exact (hcont x ⟨hx', by linarith⟩).mono_of_mem_nhdsWithin hmem

/-- Cochrane (2023), §20.2.2, p. 475: **bounded solutions of the unforced model in integral form
on `[s, ∞)`** — if `d_x, d_π` are continuous and bounded on `[s, ∞)` and
`d_x(t) − d_x(s) = −σ∫_s^t d_π`, `d_π(t) − d_π(s) = ∫_s^t (ρd_π − κd_x)`, then
`d_π(t) = e^{−λ^b(t−s)}d_π(s)` and `κ d_x(t) = λ^f d_π(t)` (the root `e^{λ^f t}` is ruled out).
The integral-form generalisation of `WerningModel.homog_bdd`; uses
`ContinuousTimeNK.unstable_bdd_zero`. -/
theorem homog_intForm_bdd {σ ρ κ s : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) {dx dπ : ℝ → ℝ}
    (hxc : ContinuousOn dx (Set.Ici s)) (hπc : ContinuousOn dπ (Set.Ici s))
    (hx : ∀ t, s ≤ t → dx t - dx s = ∫ r in s..t, -(σ * dπ r))
    (hπ : ∀ t, s ≤ t → dπ t - dπ s = ∫ r in s..t, (ρ * dπ r - κ * dx r))
    {Kx Kπ : ℝ} (hxb : ∀ t, s ≤ t → |dx t| ≤ Kx) (hπb : ∀ t, s ≤ t → |dπ t| ≤ Kπ) :
    ∀ t, s ≤ t → dπ t = Real.exp (-(lamb ρ κ σ * (t - s))) * dπ s ∧
      κ * dx t = lamf ρ κ σ * dπ t := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hroot := lamf_root (ρ := ρ) hκ hσ
  have hsub := lamf_sub_lamb ρ κ σ
  set lf := lamf ρ κ σ
  set lb := lamb ρ κ σ
  have hdx : ∀ t, s < t → HasDerivAt dx (-(σ * dπ t)) t := fun t ht =>
    hasDerivAt_of_intForm (G := fun r => -(σ * dπ r)) (continuousOn_const.mul hπc).neg hx ht
  have hdπ : ∀ t, s < t → HasDerivAt dπ (ρ * dπ t - κ * dx t) t := fun t ht =>
    hasDerivAt_of_intForm (G := fun r => ρ * dπ r - κ * dx r)
      ((continuousOn_const.mul hπc).sub (continuousOn_const.mul hxc)) hπ ht
  have hy := unstable_bdd_zero (f := fun t => lf * dπ t - κ * dx t) (a := lf) (p := s)
    (K := lf * Kπ + κ * Kx) (S := ∅) hf Set.countable_empty
    ((continuousOn_const.mul hπc).sub (continuousOn_const.mul hxc))
    (fun t ht _ => ((( hdπ t ht).const_mul lf).sub ((hdx t ht).const_mul κ)).congr_deriv
      (by linear_combination (-(dπ t)) * hroot))
    (fun t ht => by
      calc |lf * dπ t - κ * dx t| ≤ |lf * dπ t| + |κ * dx t| := abs_sub _ _
        _ = lf * |dπ t| + κ * |dx t| := by rw [abs_mul, abs_mul, abs_of_pos hf, abs_of_pos hκ]
        _ ≤ lf * Kπ + κ * Kx := add_le_add (mul_le_mul_of_nonneg_left (hπb t ht) hf.le)
            (mul_le_mul_of_nonneg_left (hxb t ht) hκ.le))
  have hsol := linear_ode_Ici (f := dπ) (a := -lb) (p := s) (S := ∅) Set.countable_empty hπc
    fun t ht _ => (hdπ t ht).congr_deriv (by
      have := hy t ht.le
      linear_combination this - (dπ t) * hsub)
  intro t ht
  refine ⟨?_, ?_⟩
  · rw [hsol t ht]
    ring_nf
  · have := hy t ht
    linarith

/-! ## Certainty equivalence -/

/-- **Cochrane (2023), (20.5)–(20.6), p. 474: certainty equivalence.** In a stochastic
equilibrium whose `x`, `π` and natural-rate shock `ν` are regular and `L¹`-bounded, for every
`s ≥ 0` and `A ∈ 𝓕_s` the conditional-mean paths `X_r = ∫_A x_r`, `Π_r = ∫_A π_r` solve the
deterministic model on `[s, ∞)` in integral form, with forcing `P(A)i`, `P(A)u + ∫_A ν` and
`P(A)g`. No covariation correction appears. -/
theorem condMean_integral_eq [IsProbabilityMeasure P] {σ ρ κ : ℝ} {𝓕 : Filtration ℝ mΩ}
    {i u g : ℝ → ℝ} {ν x π : ℝ → Ω → ℝ}
    (hi : ∀ a b, IntegrableOn i (Set.Ioc a b)) (hu : ∀ a b, IntegrableOn u (Set.Ioc a b))
    (hg : ∀ a b, IntegrableOn g (Set.Ioc a b))
    (hν : Regular 𝓕 ν) (hνb : BddL1 P ν) (hx : Regular 𝓕 x) (hxb : BddL1 P x)
    (hπ : Regular 𝓕 π) (hπb : BddL1 P π) (h : IsStochEqm σ ρ κ P 𝓕 i u g ν x π) {s : ℝ}
    (hs : 0 ≤ s) {A : Set Ω} (hA : MeasurableSet[𝓕 s] A) (t : ℝ) (hst : s ≤ t) :
    ∫ ω in A, x t ω ∂P - ∫ ω in A, x s ω ∂P = ∫ r in s..t, σ * (P.real A * i r -
        ∫ ω in A, π r ω ∂P - (P.real A * u r + ∫ ω in A, ν r ω ∂P)) ∧
      ∫ ω in A, π t ω ∂P - ∫ ω in A, π s ω ∂P = ∫ r in s..t, (ρ * ∫ ω in A, π r ω ∂P -
        κ * (∫ ω in A, x r ω ∂P + P.real A * g r)) := by
  obtain ⟨Kν, hKν⟩ := hνb
  obtain ⟨Kx, hKx⟩ := hxb
  obtain ⟨Kπ, hKπ⟩ := hπb
  have hmν : ∀ t, Measurable (ν t) := fun t => ((hν.2 t).mono (𝓕.le t)).measurable
  have hmx : ∀ t, Measurable (x t) := fun t => ((hx.2 t).mono (𝓕.le t)).measurable
  have hmπ : ∀ t, Measurable (π t) := fun t => ((hπ.2 t).mono (𝓕.le t)).measurable
  have pν := integrable_prod_proc (P := P) hν.1 hmν hKν hs (b := t)
  have px := integrable_prod_proc (P := P) hx.1 hmx hKx hs (b := t)
  have pπ := integrable_prod_proc (P := P) hπ.1 hmπ hKπ hs (b := t)
  have pi := integrable_prod_det (P := P) (hi s t)
  have pu := integrable_prod_det (P := P) (hu s t)
  have pg := integrable_prod_det (P := P) (hg s t)
  have hA' : MeasurableSet A := 𝓕.le s _ hA
  refine ⟨?_, ?_⟩
  · rw [setIntegral_expDrift h.1 hs hst hA (hKx s hs).1 (hKx t (hs.trans hst)).1
      (((pi.sub pπ).sub (pu.add pν)).const_mul σ)]
    refine intervalIntegral.integral_congr fun r hr => ?_
    have hr0 : 0 ≤ r := hs.trans (by rw [Set.uIcc_of_le hst] at hr; exact hr.1)
    have h1 := (hKπ r hr0).1.integrableOn (s := A)
    have h2 := (hKν r hr0).1.integrableOn (s := A)
    have e1 : Integrable (fun ω => i r - π r ω) (P.restrict A) := (integrable_const _).sub h1
    have e2 : Integrable (fun ω => u r + ν r ω) (P.restrict A) := (integrable_const _).add h2
    rw [integral_const_mul, integral_sub e1 e2, integral_sub (integrable_const (i r)) h1,
      integral_add (integrable_const (u r)) h2, setIntegral_const, setIntegral_const,
      smul_eq_mul, smul_eq_mul]
  · rw [setIntegral_expDrift h.2 hs hst hA (hKπ s hs).1 (hKπ t (hs.trans hst)).1
      ((pπ.const_mul ρ).sub ((px.add pg).const_mul κ))]
    refine intervalIntegral.integral_congr fun r hr => ?_
    have hr0 : 0 ≤ r := hs.trans (by rw [Set.uIcc_of_le hst] at hr; exact hr.1)
    have h1 := (hKπ r hr0).1.integrableOn (s := A)
    have h2 := (hKx r hr0).1.integrableOn (s := A)
    have e1 : Integrable (fun ω => ρ * π r ω) (P.restrict A) := h1.const_mul ρ
    have e2 : Integrable (fun ω => κ * (x r ω + g r)) (P.restrict A) :=
      (h2.add (integrable_const (g r))).const_mul κ
    rw [integral_sub e1 e2,
      integral_const_mul, integral_const_mul, integral_add h2 (integrable_const (g r)),
      setIntegral_const, smul_eq_mul]

end Cochrane.ZeroBound.TidyR7StochWerning
