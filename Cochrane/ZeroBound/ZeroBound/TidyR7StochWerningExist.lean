/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR7StochWerningTrap
import ZeroBound.TidyR7OrnsteinUhlenbeck

/-!
# The zero-bound experiment under uncertainty: explicit equilibria on a Brownian motion

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.2, pp. 474–477
(Figure 20.4 and the fiscal selection of p. 476), equations (20.5)–(20.10).

TidyR7StochWerningTrap characterises every bounded stochastic equilibrium of the experiment.
Here we construct them on a Brownian motion `W` (any pre-Brownian motion with measurable values,
continuous paths and `W_0 = 0`; e.g. bmPath on gaussSeq), with the natural filtration
`bmFiltrationReal`. The model is linear and the noise additive, so the solutions are explicit
and no SDE theorem is needed: with the Ornstein–Uhlenbeck process
`ζ^b_t = b e^{−λ^b t}∫_0^t e^{λ^b u} dW_u` (`ouProc (λ^b) 0 0 b W`, solved path by path in
TidyR7OUPath and identified with the Itô integral in TidyR7OrnsteinUhlenbeck),

`π_t = wPi(π_T)_t + ζ^b_t`, `x_t = wX(π_T)_t + (λ^f/κ)ζ^b_t` (`eqPi`, `eqX`).

The innovations are `dπ = b dW`, `dx = (λ^f/κ) b dW`; the loading `b` is a free stable-direction
innovation (a sunspot, or the fiscal innovation that fiscal theory uses to select, p. 476).

## Main results

* `stronglyMeasurable_ouProc`: the OU process is adapted to the Brownian filtration.
* `ouProc_sub`: its increments, `ζ_t − ζ_s = −η∫_s^t (ζ − s̄) + σ(W_t − W_s)`, path by path;
  `expDrift_of_bm`: a bracket equal to `c(W_t − W_s)` satisfies `E_s[·] = 0`.
* `ouProc_sq_le`: `E ζ_t² ≤ σ²/(2η)` — the OU process is bounded in mean square.
* **`isStochEqm_eq`, `regular_eqPi`, `regular_eqX`, `bddL2_eqPi`, `bddL2_eqX`**: every `(π_T, b)`
  gives a regular, `L²`-bounded stochastic equilibrium of the experiment.
* **`eqPi_inj`**: distinct `(π_T, b)` give distinct equilibria — bounded (in `L²`) equilibria
  are indexed by `π_T` *and* by the innovation loading `b`; boundedness does not pin the
  stable-direction innovation, so the selection question of p. 476 (fiscal innovation at time
  `0`, `π_0 = 0`) reappears at every date under uncertainty.
* **`not_bdd_ae_eqPi`**: for `b ≠ 0` the equilibrium is not bounded in `L^∞` (no constant
  bounds `|π_t|` almost surely): a uniform-boundedness reading of "do not explode" would rule
  out every such equilibrium, while `L²` (and `L¹`) boundedness keeps them. The book's criterion
  under uncertainty is the moment bound; with it, the unstable direction is pinned state by
  state (TidyR7StochWerningTrap.x_eq_of_pi).
* `eqPi_ae_eq_itoInt`: the Itô form `π_t = wPi(π_T)_t + b e^{−λ^b t}∫_0^t e^{λ^b u} dW_u`.
* `condExp_eqPi`: the general formula `E_s π_t = wPi(0)_t + e^{−λ^b(t−s)}(π_s − wPi(0)_s)`
  holds for these equilibria (the response of `π_t` to `dW_s` is `b e^{−λ^b(t−s)}`, the
  deterministic response of `wPi_shift`).
* Non-vacuity on bmPath at the book's calibration (`ρ = 0.05`, `σ = κ = 1`, `T = 5`,
  `u_r = −2%`): `bmPath_isStochEqm`, `bmPath_eqPi_ne`, `bmPath_not_bdd_ae`.
-/

namespace Cochrane.ZeroBound.TidyR7StochWerningExist

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.ContinuousTimeNK Cochrane.ZeroBound.WerningModel
open Cochrane.ZeroBound.TidyR7StochWerning Cochrane.ZeroBound.TidyR7StochWerningTrap
open Cochrane.ZeroBound.TidyR7OUPath Cochrane.ZeroBound.TidyR7OrnsteinUhlenbeck
open Cochrane.ZeroBound.TidyR7BrownianTools
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

/-! ## The OU process on the Brownian filtration -/

/-- Cochrane (2023), §20.2.2, p. 474 (tool): `W_u` is known at `t` when `u⁺ ≤ t⁺`.
The monotone form of `TidyR7BrownianTools.stronglyAdapted_bmFiltration`. -/
theorem stronglyMeasurable_bmReal_le (hW : ∀ t, Measurable (W t)) {u t : ℝ}
    (hut : u.toNNReal ≤ t.toNNReal) :
    StronglyMeasurable[bmFiltrationReal W hW t] (bmReal W u) :=
  ((stronglyAdapted_bmFiltration hW) u.toNNReal).mono ((bmFiltration W hW).mono hut)

/-- Cochrane (2023), §20.2.2, p. 474 (tool): **the OU process is adapted** to the natural
filtration of `W`: `ζ_t` is a measurable function of the path up to `t`. -/
theorem stronglyMeasurable_ouProc (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (η sbar s0 σ t : ℝ) :
    StronglyMeasurable[bmFiltrationReal W hW t] (ouProc η sbar s0 σ W t) := by
  set m := (bmFiltrationReal W hW) t
  let F : ℝ → Ω → ℝ := fun u ω => Real.exp (η * u) * bmReal W (min u (max t 0)) ω
  have hle : ∀ u, (min u (max t 0)).toNNReal ≤ t.toNNReal := fun u => by
    rcases le_total 0 t with h | h
    · exact Real.toNNReal_le_toNNReal ((min_le_right _ _).trans (max_eq_left h).le)
    · have h1 : min u (max t 0) ≤ 0 := (min_le_right _ _).trans (max_eq_right h).le
      rw [Real.toNNReal_of_nonpos h1]
      exact bot_le
  have hFm : ∀ u, Measurable[m] (F u) := fun u =>
    (stronglyMeasurable_const.mul (stronglyMeasurable_bmReal_le hW (hle u))).measurable
  have hFc : ∀ ω, Continuous fun u => F u ω := fun ω =>
    (by fun_prop : Continuous fun u : ℝ => Real.exp (η * u)).mul
      ((continuous_bmReal (hcont ω)).comp (continuous_id.min continuous_const))
  have hF := (measurable_uncurry_of_continuous_of_measurable (m := m) hFc hFm).stronglyMeasurable
  have h1 := @StronglyMeasurable.integral_prod_left ℝ Ω ℝ _ m (volume.restrict (Set.Ioc 0 t))
    _ _ _ F hF
  have h2 := @StronglyMeasurable.integral_prod_left ℝ Ω ℝ _ m (volume.restrict (Set.Ioc t 0))
    _ _ _ F hF
  have hG : StronglyMeasurable[m] fun ω => ∫ u in (0 : ℝ)..t, F u ω := by
    simp only [intervalIntegral]
    exact h1.sub h2
  have heq : ouProc η sbar s0 σ W t = fun ω => ouMean η sbar s0 t +
      σ * (bmReal W t ω - η * (Real.exp (-η * t) * ∫ u in (0 : ℝ)..t, F u ω)) := by
    funext ω
    have hI : (∫ u in (0 : ℝ)..t, Real.exp (η * u) * bmReal W u ω) =
        ∫ u in (0 : ℝ)..t, F u ω := by
      refine intervalIntegral.integral_congr fun u hu => ?_
      have hu2 : u ≤ max t 0 := by
        have := hu.2
        rw [max_comm]
        exact this
      simp only [F, min_eq_left hu2]
    simp only [ouProc, ouPath, ouNoise, ouPrim]
    rw [hI]
  rw [heq]
  exact stronglyMeasurable_const.add (stronglyMeasurable_const.mul
    ((stronglyAdapted_bmFiltration hW t.toNNReal).sub
      (stronglyMeasurable_const.mul (stronglyMeasurable_const.mul hG))))

/-- Cochrane (2023), §20.2.2, p. 474: the OU process is regular (continuous adapted paths). -/
theorem regular_ouProc (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω)
    (η sbar s0 σ : ℝ) : Regular (bmFiltrationReal W hW) (ouProc η sbar s0 σ W) :=
  ⟨fun ω => continuous_ouPath η sbar s0 σ (continuous_bmReal (hcont ω)),
    fun t => stronglyMeasurable_ouProc hW hcont η sbar s0 σ t⟩

/-- Cochrane (2023), §20.2.2, p. 474: **increments of the OU process**, path by path:
`ζ_t − ζ_s = −η∫_s^t (ζ_u − s̄)du + σ(W_t − W_s)`.
Generalises `TidyR7OrnsteinUhlenbeck.ouProc_integral_eq` from `0` to any `s`. -/
theorem ouProc_sub (hcont : ∀ ω, Continuous fun t => W t ω) (η sbar s0 σ : ℝ) (ω : Ω)
    (s t : ℝ) :
    ouProc η sbar s0 σ W t ω - ouProc η sbar s0 σ W s ω =
      -(η * ∫ u in s..t, (ouProc η sbar s0 σ W u ω - sbar)) +
        σ * (bmReal W t ω - bmReal W s ω) := by
  have hc : Continuous fun u => ouProc η sbar s0 σ W u ω - sbar :=
    (continuous_ouPath η sbar s0 σ (continuous_bmReal (hcont ω))).sub continuous_const
  rw [ouProc_integral_eq hcont η sbar s0 σ ω t, ouProc_integral_eq hcont η sbar s0 σ ω s,
    ← intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable 0 t)
      (hc.intervalIntegrable 0 s)]
  ring

/-- Cochrane (2023), (20.5)–(20.6), p. 474 (tool): **a bracket equal to `c(W_t − W_s)` has zero
conditional mean**, so `E_t dZ = D dt` holds when `Z_t − Z_s − ∫_s^t D = c(W_t − W_s)`. -/
theorem expDrift_of_bm [IsProbabilityMeasure P] (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) {Z D : ℝ → Ω → ℝ} (c : ℝ)
    (h : ∀ s t, 0 ≤ s → s ≤ t → ∀ ω,
      Z t ω - Z s ω - ∫ r in s..t, D r ω = c * (bmReal W t ω - bmReal W s ω)) :
    ExpDrift P (bmFiltrationReal W hW) Z D := by
  intro s t hs hst
  have e : (fun ω => Z t ω - Z s ω - ∫ r in s..t, D r ω) = c • (bmReal W t - bmReal W s) := by
    funext ω
    simp [h s t hs hst ω]
  rw [e]
  have M := martingale_bmReal hB hW
  refine ⟨((M.integrable t).sub (M.integrable s)).const_mul c, ?_⟩
  have h1 := condExp_smul (μ := P) c (bmReal W t - bmReal W s) (bmFiltrationReal W hW s)
  have h2 := condExp_sub (M.integrable t) (M.integrable s) (μ := P) (bmFiltrationReal W hW s)
  have h3 := M.condExp_ae_eq hst
  have h4 := condExp_of_stronglyMeasurable ((bmFiltrationReal W hW).le s) (M.1 s)
    (M.integrable s)
  filter_upwards [h1, h2, h3] with ω e1 e2 e3
  rw [e1, Pi.smul_apply, e2, Pi.sub_apply, e3, h4]
  simp

/-- Cochrane (2023), §20.2.2, p. 474: **the OU process is bounded in mean square**: for
`η > 0` and `t ≥ 0`, `ζ_t ∈ L²` and `E ζ_t² ≤ σ²/(2η)` (`ζ = ouProc η 0 0 σ W`).
From `TidyR7OrnsteinUhlenbeck.ouProc_hasLaw`. -/
theorem ouProc_sq_le [IsProbabilityMeasure P] (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {η : ℝ} (hη : 0 < η) (σ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (ouProc η 0 0 σ W t) 2 P ∧ ∫ ω, ouProc η 0 0 σ W t ω ^ 2 ∂P ≤ σ ^ 2 / (2 * η) := by
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    have hz : ouProc η 0 0 σ W 0 = fun _ => (0 : ℝ) := funext fun ω => ouProc_zero hW0 η 0 0 σ ω
    rw [hz]
    exact ⟨memLp_const 0, by
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero]
      positivity⟩
  · have hlaw := ouProc_hasLaw hB hW hcont hW0 hη 0 0 σ hpos
    have hm : ouMean η 0 0 t = 0 := by simp [ouMean]
    rw [hm] at hlaw
    have hae := aemeasurable_ouProc hB hW hcont hW0 η 0 0 σ hpos
    refine ⟨?_, ?_⟩
    · have := (memLp_map_measure_iff aestronglyMeasurable_id hae (p := 2)).1
        (by rw [hlaw]; exact memLp_id_gaussianReal' 2 (by simp))
      exact this
    · rw [← integral_map hae (continuous_pow 2).aestronglyMeasurable, hlaw,
        TidyR7BrownianTools.integral_sq_gaussianReal, ouVar, Real.coe_toNNReal']
      refine max_le ?_ (by positivity)
      have : 0 < Real.exp (-2 * η * t) := Real.exp_pos _
      rw [div_le_div_iff_of_pos_right (by positivity)]
      nlinarith [sq_nonneg σ]

/-! ## The explicit equilibria -/

/-- Cochrane (2023), §20.2.2, pp. 475–476, under uncertainty: the inflation process
`π_t = wPi(π_T)_t + ζ^b_t` with stable innovation `ζ^b = ouProc (λ^b) 0 0 b W`. -/
noncomputable def eqPi (σ κ ρ T u g πT b : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  wPi σ κ ρ T u g πT t + ouProc (lamb ρ κ σ) 0 0 b W t ω

/-- Cochrane (2023), (20.10), p. 475, under uncertainty: the output process
`x_t = wX(π_T)_t + (λ^f/κ)ζ^b_t`. -/
noncomputable def eqX (σ κ ρ T u g πT b : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  wX σ κ ρ T u g πT t + lamf ρ κ σ / κ * ouProc (lamb ρ κ σ) 0 0 b W t ω

/-- Cochrane (2023), §20.2.2, p. 474: the stable innovation is linear in its loading,
`ζ^b = b ζ^1`. -/
theorem ouProc_loading (η b : ℝ) (t : ℝ) (ω : Ω) :
    ouProc η 0 0 b W t ω = b * ouProc η 0 0 1 W t ω := by
  simp [ouProc, ouPath, ouMean]

/-- **Cochrane (2023), (20.5)–(20.6), p. 474: every `(π_T, b)` gives a stochastic equilibrium**
of the experiment: `E_t dx = σ(0 − π − u_r)dt`, `E_t dπ = (ρπ − κ(x + g))dt`, with innovations
`dπ = b dW` and `dx = (λ^f b/κ) dW`. -/
theorem isStochEqm_eq [IsProbabilityMeasure P] (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω) {σ ρ κ : ℝ}
    (hσ : 0 < σ) (hκ : 0 < κ) (T u g πT b : ℝ) :
    IsStochEqm σ ρ κ P (bmFiltrationReal W hW) (fun _ => 0) (trapStep u T) (trapStep g T)
      (fun _ _ => 0) (eqX σ κ ρ T u g πT b W) (eqPi σ κ ρ T u g πT b W) := by
  have hmul := lamf_mul_lamb (ρ := ρ) hκ hσ
  have hsub := lamf_sub_lamb ρ κ σ
  have hc : lamf ρ κ σ / κ * lamb ρ κ σ = σ := by
    field_simp
    linarith
  have hzc : ∀ ω, Continuous fun r => ouProc (lamb ρ κ σ) 0 0 b W r ω := fun ω =>
    continuous_ouPath (lamb ρ κ σ) 0 0 b (continuous_bmReal (hcont ω))
  have hWc := wPi_continuous σ κ ρ T u g πT hκ hσ
  have hXc := wX_continuous σ κ ρ T u g πT hκ hσ
  refine ⟨expDrift_of_bm hB hW (lamf ρ κ σ / κ * b) fun s t hs hst ω => ?_,
    expDrift_of_bm hB hW b fun s t hs hst ω => ?_⟩
  · obtain ⟨d1, -⟩ := wPath_intForm (ρ := ρ) hκ hσ T u g πT hs hst
    have hz := ouProc_sub hcont (lamb ρ κ σ) 0 0 b ω s t
    have i1 : IntervalIntegrable (fun r => σ * (0 - wPi σ κ ρ T u g πT r - trapStep u T r))
        volume s t := ((intervalIntegrable_const.sub (hWc.intervalIntegrable s t)).sub
          (trapStep_intervalIntegrable u T s t)).const_mul σ
    have i2 : IntervalIntegrable (fun r => σ * ouProc (lamb ρ κ σ) 0 0 b W r ω) volume s t :=
      ((hzc ω).intervalIntegrable s t).const_mul σ
    have e : (∫ r in s..t, σ * (0 - eqPi σ κ ρ T u g πT b W r ω - (trapStep u T r + 0))) =
        (∫ r in s..t, σ * (0 - wPi σ κ ρ T u g πT r - trapStep u T r)) -
          σ * ∫ r in s..t, ouProc (lamb ρ κ σ) 0 0 b W r ω := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub i1 i2]
      refine intervalIntegral.integral_congr fun r _ => ?_
      simp only [eqPi]
      ring
    simp only [sub_zero] at hz
    simp only [eqX]
    rw [e, ← d1]
    linear_combination (lamf ρ κ σ / κ) * hz -
      (∫ u in s..t, ouProc (lamb ρ κ σ) 0 0 b W u ω) * hc
  · obtain ⟨-, d2⟩ := wPath_intForm (ρ := ρ) hκ hσ T u g πT hs hst
    have hz := ouProc_sub hcont (lamb ρ κ σ) 0 0 b ω s t
    have i1 : IntervalIntegrable (fun r => ρ * wPi σ κ ρ T u g πT r -
        κ * (wX σ κ ρ T u g πT r + trapStep g T r)) volume s t :=
      ((hWc.intervalIntegrable s t).const_mul ρ).sub (((hXc.intervalIntegrable s t).add
        (trapStep_intervalIntegrable g T s t)).const_mul κ)
    have i2 : IntervalIntegrable (fun r => (ρ - lamf ρ κ σ) * ouProc (lamb ρ κ σ) 0 0 b W r ω)
        volume s t :=
      ((hzc ω).intervalIntegrable s t).const_mul _
    have e : (∫ r in s..t, (ρ * eqPi σ κ ρ T u g πT b W r ω -
        κ * (eqX σ κ ρ T u g πT b W r ω + trapStep g T r))) =
        (∫ r in s..t, (ρ * wPi σ κ ρ T u g πT r - κ * (wX σ κ ρ T u g πT r + trapStep g T r))) +
          (ρ - lamf ρ κ σ) * ∫ r in s..t, ouProc (lamb ρ κ σ) 0 0 b W r ω := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add i1 i2]
      refine intervalIntegral.integral_congr fun r _ => ?_
      simp only [eqPi, eqX]
      field_simp
      ring
    simp only [sub_zero] at hz
    rw [e]
    simp only [eqPi]
    rw [← d2]
    linear_combination hz + (∫ u in s..t, ouProc (lamb ρ κ σ) 0 0 b W u ω) * hsub

/-- Cochrane (2023), §20.2.2, p. 474: the inflation process is regular. -/
theorem regular_eqPi (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω)
    {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (T u g πT b : ℝ) :
    Regular (bmFiltrationReal W hW) (eqPi σ κ ρ T u g πT b W) :=
  ⟨fun ω => (wPi_continuous σ κ ρ T u g πT hκ hσ).add
      ((regular_ouProc hW hcont (lamb ρ κ σ) 0 0 b).1 ω),
    fun t => stronglyMeasurable_const.add ((regular_ouProc hW hcont (lamb ρ κ σ) 0 0 b).2 t)⟩

/-- Cochrane (2023), (20.10), p. 475: the output process is regular. -/
theorem regular_eqX (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω)
    {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (T u g πT b : ℝ) :
    Regular (bmFiltrationReal W hW) (eqX σ κ ρ T u g πT b W) :=
  ⟨fun ω => (wX_continuous σ κ ρ T u g πT hκ hσ).add
      (continuous_const.mul ((regular_ouProc hW hcont (lamb ρ κ σ) 0 0 b).1 ω)),
    fun t => stronglyMeasurable_const.add (stronglyMeasurable_const.mul
      ((regular_ouProc hW hcont (lamb ρ κ σ) 0 0 b).2 t))⟩

/-- Cochrane (2023), §20.2.2, p. 474 (tool): a bounded deterministic part plus `c` times an OU
process bounded in mean square is bounded in mean square. -/
theorem bddL2_add_ou [IsProbabilityMeasure P] (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {η : ℝ} (hη : 0 < η) (b c : ℝ) {f : ℝ → ℝ} (hf : BddOnIci f) :
    BddL2 P (fun t ω => f t + c * ouProc η 0 0 b W t ω) := by
  obtain ⟨K, hK⟩ := hf
  refine ⟨2 * K ^ 2 + 2 * c ^ 2 * (b ^ 2 / (2 * η)), fun t ht => ?_⟩
  obtain ⟨hm, hq⟩ := ouProc_sq_le hB hW hcont hW0 hη b ht
  have hm' : MemLp (fun ω => f t + c * ouProc η 0 0 b W t ω) 2 P :=
    (memLp_const (f t)).add (hm.const_mul c)
  refine ⟨hm', ?_⟩
  have hfK : f t ^ 2 ≤ K ^ 2 := by
    have := hK t ht
    nlinarith [abs_nonneg (f t), sq_abs (f t)]
  calc ∫ ω, (f t + c * ouProc η 0 0 b W t ω) ^ 2 ∂P
      ≤ ∫ ω, (2 * f t ^ 2 + 2 * c ^ 2 * ouProc η 0 0 b W t ω ^ 2) ∂P := by
        refine integral_mono hm'.integrable_sq
          ((integrable_const _).add (hm.integrable_sq.const_mul _)) fun ω => ?_
        nlinarith [sq_nonneg (f t - c * ouProc η 0 0 b W t ω)]
    _ = 2 * f t ^ 2 + 2 * c ^ 2 * ∫ ω, ouProc η 0 0 b W t ω ^ 2 ∂P := by
        rw [integral_add (integrable_const _) (hm.integrable_sq.const_mul _),
          integral_const_mul (2 * c ^ 2)]
        simp
    _ ≤ 2 * K ^ 2 + 2 * c ^ 2 * (b ^ 2 / (2 * η)) := by
        have := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ 2 * c ^ 2)
        linarith

/-- Cochrane (2023), §20.2.2, p. 474: **the inflation process is bounded in mean square.** -/
theorem bddL2_eqPi [IsProbabilityMeasure P] (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (T u g πT b : ℝ) :
    BddL2 P (eqPi σ κ ρ T u g πT b W) := by
  have h := bddL2_add_ou (P := P) hB hW hcont hW0 (lamb_pos (ρ := ρ) hκ hσ) b 1
    (wPath_bdd (ρ := ρ) hκ hσ T u g πT).2
  simp only [one_mul] at h
  exact h

/-- Cochrane (2023), (20.10), p. 475: **the output process is bounded in mean square.** -/
theorem bddL2_eqX [IsProbabilityMeasure P] (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (T u g πT b : ℝ) :
    BddL2 P (eqX σ κ ρ T u g πT b W) :=
  bddL2_add_ou (P := P) hB hW hcont hW0 (lamb_pos (ρ := ρ) hκ hσ) b _
    (wPath_bdd (ρ := ρ) hκ hσ T u g πT).1

/-! ## Multiplicity, the failure of uniform boundedness, and the Itô form -/

/-- Cochrane (2023), §20.2.2, p. 475 ("multiple forward-stable equilibrium inflation paths"),
under uncertainty: **distinct `(π_T, b)` give distinct equilibria.** If the inflation processes
agree almost surely at every date `t ≥ 0`, then `π_T = π_T'` and `b = b'`. -/
theorem eqPi_inj [IsProbabilityMeasure P] (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) {T u g πT πT' b b' : ℝ}
    (h : ∀ t, 0 ≤ t → eqPi σ κ ρ T u g πT b W t =ᵐ[P] eqPi σ κ ρ T u g πT' b' W t) :
    πT = πT' ∧ b = b' := by
  have hlb := lamb_pos (ρ := ρ) hκ hσ
  have hbb : b = b' := by
    by_contra hne
    have hd : b - b' ≠ 0 := sub_ne_zero.2 hne
    set c := (wPi σ κ ρ T u g πT' 1 - wPi σ κ ρ T u g πT 1) / (b - b')
    have hae : ∀ᵐ ω ∂P, ouProc (lamb ρ κ σ) 0 0 1 W 1 ω = c := by
      filter_upwards [h 1 zero_le_one] with ω hω
      simp only [eqPi, ouProc_loading (lamb ρ κ σ) b, ouProc_loading (lamb ρ κ σ) b'] at hω
      simp only [c]
      field_simp
      linarith
    have hpos := ouProc_gt_pos hB hW hcont hW0 hlb one_ne_zero 0 0 one_pos c
    have h0 : P {ω | c < ouProc (lamb ρ κ σ) 0 0 1 W 1 ω} = 0 := by
      have := ae_iff.1 (hae.mono fun ω hω =>
        (by rw [hω]; exact lt_irrefl c : ¬ (c < ouProc (lamb ρ κ σ) 0 0 1 W 1 ω)))
      simpa using this
    exact absurd h0 hpos.ne'
  subst hbb
  refine ⟨?_, rfl⟩
  obtain ⟨ω, hω⟩ := (h 0 le_rfl).exists
  simp only [eqPi, add_left_inj] at hω
  rw [wPi_shift, wPi_shift σ κ ρ T u g πT'] at hω
  have := mul_right_cancel₀ (Real.exp_pos _).ne' (add_left_cancel hω)
  exact this

/-- Cochrane (2023), §20.2.2, p. 474 ("do not explode"), under uncertainty: **an equilibrium
with a non-zero stable innovation is not uniformly bounded**: for `b ≠ 0` there is no constant
`K` with `|π_t| ≤ K` almost surely for all `t ≥ 0` (at every date `π_t` exceeds any level with
positive probability). It is nevertheless bounded in mean square (`bddL2_eqPi`).
Uses `TidyR7OrnsteinUhlenbeck.ouProc_gt_pos`. -/
theorem not_bdd_ae_eqPi (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {σ ρ κ : ℝ} (hσ : 0 < σ)
    (hκ : 0 < κ) (T u g πT : ℝ) {b : ℝ} (hb : b ≠ 0) :
    ¬ ∃ K, ∀ t, 0 ≤ t → ∀ᵐ ω ∂P, |eqPi σ κ ρ T u g πT b W t ω| ≤ K := by
  rintro ⟨K, hK⟩
  set M := K + |wPi σ κ ρ T u g πT 1|
  have hpos := ouProc_gt_pos hB hW hcont hW0 (lamb_pos (ρ := ρ) hκ hσ) hb 0 0 one_pos M
  have hae : ∀ᵐ ω ∂P, ¬ (M < ouProc (lamb ρ κ σ) 0 0 b W 1 ω) := by
    filter_upwards [hK 1 zero_le_one] with ω hω
    simp only [eqPi] at hω
    have h1 := (abs_le.1 hω).2
    have h2 := neg_abs_le (wPi σ κ ρ T u g πT 1)
    simp only [M, not_lt]
    linarith
  have h0 : P {ω | M < ouProc (lamb ρ κ σ) 0 0 b W 1 ω} = 0 := by
    have := ae_iff.1 hae
    simpa using this
  exact absurd h0 hpos.ne'

/-- Cochrane (2023), §20.2.2, p. 475, under uncertainty: **the Itô form of the equilibrium**:
for `t > 0`, `π_t = wPi(π_T)_t + b e^{−λ^b t}∫_0^t e^{λ^b u} dW_u` almost surely, with the
Itô (Wiener) integral on the Brownian filtration.
Specialises `TidyR7OrnsteinUhlenbeck.ouProc_ae_eq_itoInt`. -/
theorem eqPi_ae_eq_itoInt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) (σ κ ρ T u g πT b : ℝ)
    {t : ℝ} (ht : 0 < t) :
    eqPi σ κ ρ T u g πT b W t =ᵐ[P] fun ω => wPi σ κ ρ T u g πT t + b *
      Real.exp (-lamb ρ κ σ * t) * TidyR7ItoIntegral.itoInt P (bmFiltrationReal W hW) W
        (fun v _ => Real.exp (lamb ρ κ σ * v)) 0 t ω := by
  filter_upwards [ouProc_ae_eq_itoInt hB hW (TidyR7BrownianQV.bmFiltrationReal_isBM hB hW) hcont
    hW0 (lamb ρ κ σ) 0 0 b ht] with ω hω
  simp only [eqPi, hω]
  ring

/-- Cochrane (2023), §20.2.2, pp. 474–475: **the general characterisation applies to the
explicit equilibria**: `E_s π_t = wPi(0)_t + e^{−λ^b(t−s)}(π_s − wPi(0)_s)`; the response of
`π_t` to news at `s` is `e^{−λ^b(t−s)}`, as between deterministic family members.
An instance of `TidyR7StochWerningTrap.condExp_pi_eq`. -/
theorem condExp_eqPi [IsProbabilityMeasure P] (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (T u g πT b : ℝ) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    P[eqPi σ κ ρ T u g πT b W t | bmFiltrationReal W hW s] =ᵐ[P] fun ω =>
      wPi σ κ ρ T u g 0 t + Real.exp (-(lamb ρ κ σ * (t - s))) *
        (eqPi σ κ ρ T u g πT b W s ω - wPi σ κ ρ T u g 0 s) :=
  condExp_pi_eq hσ hκ (regular_eqX hW hcont hσ hκ T u g πT b)
    (bddL2_eqX hB hW hcont hW0 hσ hκ T u g πT b).bddL1 (regular_eqPi hW hcont hσ hκ T u g πT b)
    (bddL2_eqPi hB hW hcont hW0 hσ hκ T u g πT b).bddL1 (isStochEqm_eq hB hW hcont hσ hκ T u g πT b)
    hs hst

/-! ## Non-vacuity on the constructed Brownian motion -/

open Cochrane.ZeroBound.TidyR7BrownianExist Cochrane.ZeroBound.TidyR7BrownianSchauder

/-- Cochrane (2023), §20.2.2, p. 474 (non-vacuity): on bmPath (gaussSeq), at the book's
calibration `ρ = 0.05`, `σ = κ = 1`, `T = 5`, `u_r = −2%`, `g = 0`, the process with `π_T = 0`
and unit innovation loading is a regular, mean-square-bounded stochastic equilibrium. -/
theorem bmPath_isStochEqm :
    IsStochEqm 1 (1 / 20) 1 gaussSeq (bmFiltrationReal bmPath measurable_bmPath) (fun _ => 0)
        (trapStep (-2 / 100) 5) (trapStep 0 5) (fun _ _ => 0)
        (eqX 1 1 (1 / 20) 5 (-2 / 100) 0 0 1 bmPath) (eqPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 1 bmPath) ∧
      Regular (bmFiltrationReal bmPath measurable_bmPath)
        (eqPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 1 bmPath) ∧
      BddL2 gaussSeq (eqPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 1 bmPath) ∧
      BddL2 gaussSeq (eqX 1 1 (1 / 20) 5 (-2 / 100) 0 0 1 bmPath) := by
  have := isProbabilityMeasure_gaussSeq
  exact ⟨isStochEqm_eq isPreBrownianReal_bmPath measurable_bmPath continuous_bmPath one_pos
      one_pos _ _ _ _ _,
    regular_eqPi measurable_bmPath continuous_bmPath one_pos one_pos _ _ _ _ _,
    bddL2_eqPi isPreBrownianReal_bmPath measurable_bmPath continuous_bmPath bmPath_zero one_pos
      one_pos _ _ _ _ _,
    bddL2_eqX isPreBrownianReal_bmPath measurable_bmPath continuous_bmPath bmPath_zero one_pos
      one_pos _ _ _ _ _⟩

/-- Cochrane (2023), §20.2.2, p. 475 (non-vacuity): on bmPath at the book's calibration, the
equilibria with innovation loadings `0` (deterministic) and `1` are different. -/
theorem bmPath_eqPi_ne :
    ¬ ∀ t, 0 ≤ t → eqPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 0 bmPath t =ᵐ[gaussSeq]
      eqPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 1 bmPath t := by
  have := isProbabilityMeasure_gaussSeq
  intro h
  have := (eqPi_inj isPreBrownianReal_bmPath measurable_bmPath continuous_bmPath bmPath_zero
    one_pos one_pos h).2
  norm_num at this

/-- Cochrane (2023), §20.2.2, p. 474 (non-vacuity): on bmPath at the book's calibration, the
equilibrium with unit innovation loading is not uniformly bounded. -/
theorem bmPath_not_bdd_ae :
    ¬ ∃ K, ∀ t, 0 ≤ t → ∀ᵐ ω ∂gaussSeq,
      |eqPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 1 bmPath t ω| ≤ K :=
  not_bdd_ae_eqPi isPreBrownianReal_bmPath measurable_bmPath continuous_bmPath bmPath_zero
    one_pos one_pos _ _ _ _ one_ne_zero

end Cochrane.ZeroBound.TidyR7StochWerningExist
