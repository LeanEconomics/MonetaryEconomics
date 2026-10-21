/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PolicyResponseDynamics.ForwardSystems
import PolicyResponseDynamics.ExpectationCalculus
import PolicyResponseDynamics.ExpectationsFiniteTree
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Predetermined expenditure

Woodford (2003), *Interest and Prices*, Chapter 5, §1.1, pp. 322–332: consequences of
predetermined expenditure. Private expenditure for date `t` is chosen at `t − d`. Every model
equation is written at date `t + d` and conditioned on date `t` (the book's `E_{t−d}`), for an
arbitrary `ExpectationSystem` (perfect foresight and genuine uncertainty alike).

## Main results

* (1.3)–(1.5): `foc13_iff_foc15` (complete markets (1.4) as a hypothesis, the multiplier pulled
  through `E_{t−d}` by `PullOut`); `gross_rate`, `gross_rate_log_form`: `1 + i_t =
  β⁻¹Λ_t/E_tΛ_{t+1}` and its exact log form; `hasDerivAt_log_gross_rate`: the log-linear
  relation `î_t = λ̂_t + E_t[π_{t+1} − λ̂_{t+1}]` as an exact derivative.
* (1.6) as the exact derivative of the log of (1.5) (`foc15_log_form`, `eq16_deriv`,
  `eq16_iff_deriv_zero`), with `σ`, `g = Ĝ + s_C E_{t−d} c̄` from the utility function; the
  information-delay version (1.22) (`eq122_deriv`) gives `g = Ĝ + s_C c̄`.
* The forward solution for `λ̂`: `lam_iterate`, `lam_forward_iff` (the series converges iff
  `E_t λ̂_{t+k}` converges); `lam_forward_needs_limit`: boundedness alone is not enough.
* (1.7): `is17_of_eq16`; (1.7) ⟺ (1.8) plus the boundary condition (`is17_iff_is18`, under
  `LimitExchange`, which holds on every finite state space: `limitExchange_of_finite`);
  (1.8) ⟺ (1.10) ∧ (1.11) (`is18_iff_is110_gap111`).
* (1.9) and footnote 6: `infl_forecastable`, `gap_unforecastable`.
* Proposition 4.3 of Chapter 4 restated (`prop_4_3`, with the forward-system existence theory
  `ForwardSystems.fwdVec_spec`, `ForwardSystems.pow_geom_bound`,
  `ForwardSystems.fwd_existsUnique`).
* The reduction (`delayed_reduce`, `delayed_lift`) and the determinacy transfer
  (`delayedDeterminate_iff_model`): the delayed model is determinate iff (1.14)
  `φ_π + (1 − β)φ_x/(4κ) > 1` (`delayed_determinate_iff`).
* Survey error 7 confirmed: (1.13) as printed lacks `/4` (`rule113_printed_iff`,
  `printed_rule_determinate_iff`, `printed_rule_counterexample`).
* (1.15)–(1.17): `solution_115_117` (the unique bounded solution with the Chapter 4
  coefficients `psiCoef`), `delayed_eq_forecast_ch4` (the `d`-period-ahead forecasts of the
  Chapter 4 solution), `taylorEqm_fc`.
* Intercept tracking with `+ π̄` (`intercept_tracking_iff`); survey error 9 confirmed
  (`printed_intercept_fails`).
* The variance decomposition with Mathlib's conditional expectation (`cov_condExp_resid`,
  `variance_decomposition`, `variance_gap_bound`, `variance_gap_tracking`).
* (1.18)–(1.21): `realMC_eq_lam`, `realMC_avg`, `mu_eq_lam_sub`, `E_mu_zero`,
  `E_mu_zero_of_le`, `mu_term_nonzero_of_lt`, `mu_observables`; (1.20) derived from the
  Chapter 3 Calvo first-order condition with an `s`-period lag (`delayed_calvo`, `eq120`,
  `nkpc19_of_eq120`); the information-delay version removes `μ` (`mc_info_delay`).
-/

namespace Woodford.PolicyResponseDynamics.Predetermined

open Filter Topology Asymptotics ForwardSystems ExpectationCalculus

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Household optimisation, (1.3)–(1.5) -/

omit 𝔼 in
/-- Woodford (2003), eq. (1.4), p. 324 (complete markets): `Λ_t Q_{t,s} = β^{s−t} Λ_s` for
`t ≤ s`, state by state. -/
def CompleteMarkets (β : ℝ) (Lam : ℕ → Ω → ℝ) (Q : ℕ → ℕ → Ω → ℝ) : Prop :=
  ∀ t s, t ≤ s → Lam t * Q t s = β ^ (s - t) • Lam s

/-- Woodford (2003), eqs. (1.3)–(1.5), p. 324: given complete markets (1.4) and the pull-out
property, the first-order condition (1.3) `β^d E_{t−d} u_c(C_t) = Λ_{t−d} E_{t−d}[Q_{t−d,t} P_t]`
is equivalent to (1.5) `E_{t−d} u_c(C_t) = E_{t−d}[Λ_t P_t]` (written at date `t + d`, conditioned
on date `t`): the multiplier `Λ_{t−d}`, known at `t − d`, is pulled through `E_{t−d}`. -/
theorem foc13_iff_foc15 (hpo : 𝔼.PullOut) {β : ℝ} (hβ : β ≠ 0) {Lam P uc : ℕ → Ω → ℝ}
    {Q : ℕ → ℕ → Ω → ℝ} (hLam : 𝔼.Adapted Lam) (hcm : CompleteMarkets β Lam Q) (d t : ℕ) :
    β ^ d • 𝔼.E t (uc (t + d)) = Lam t * 𝔼.E t (Q t (t + d) * P (t + d)) ↔
      𝔼.E t (uc (t + d)) = 𝔼.E t (Lam (t + d) * P (t + d)) := by
  have key : Lam t * 𝔼.E t (Q t (t + d) * P (t + d)) =
      β ^ d • 𝔼.E t (Lam (t + d) * P (t + d)) := by
    rw [← hpo t _ _ (hLam t), ← mul_assoc, hcm t (t + d) (Nat.le_add_right t d),
      Nat.add_sub_cancel_left, smul_mul_assoc, map_smul]
  rw [key]
  constructor
  · intro h
    exact smul_right_injective (Ω → ℝ) (pow_ne_zero d hβ) h
  · intro h
    rw [h]

/-- Woodford (2003), p. 325: complete markets (1.4) and the pricing of a riskless one-period
nominal bond, `(1 + i_t) E_t Q_{t,t+1} = 1`, give `1 + i_t = β⁻¹ Λ_t [E_t Λ_{t+1}]⁻¹`. -/
theorem gross_rate (hpo : 𝔼.PullOut) {β : ℝ} {Lam i : ℕ → Ω → ℝ}
    {Q : ℕ → ℕ → Ω → ℝ} (hLam : 𝔼.Adapted Lam) (hpos : ∀ s ω, 0 < Lam s ω)
    (hcm : CompleteMarkets β Lam Q) (t : ℕ) (hQ : ∀ ω, (1 + i t ω) * 𝔼.E t (Q t (t + 1)) ω = 1)
    (ω : Ω) : 1 + i t ω = Lam t ω / (β * 𝔼.E t (Lam (t + 1)) ω) := by
  have h1 : Lam t * 𝔼.E t (Q t (t + 1)) = β • 𝔼.E t (Lam (t + 1)) := by
    rw [← hpo t _ _ (hLam t), hcm t (t + 1) (Nat.le_succ t),
      show t + 1 - t = 1 by omega, pow_one, map_smul]
  have h1ω := congrFun h1 ω
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at h1ω
  have hq := hQ ω
  have hL := hpos t ω
  have hprod : (1 + i t ω) * (β * 𝔼.E t (Lam (t + 1)) ω) = Lam t ω := by
    rw [← h1ω]
    linear_combination Lam t ω * hq
  have hne : β * 𝔼.E t (Lam (t + 1)) ω ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hprod
    linarith
  rw [eq_div_iff hne]
  exact hprod

/-- Woodford (2003), p. 325 (the exact log form of the bond-pricing relation): with
`λ̂_t ≡ log(Λ_t P_t / ū_c)` (so `Λ_s = ū_c e^{λ̂_s} / P_s`) and `P_{s+1} = P_s e^{π_{s+1}}`,
`β(1 + i_t) = e^{λ̂_t} / E_t[e^{λ̂_{t+1} − π_{t+1}}]`. -/
theorem gross_rate_log_form (hpo : 𝔼.PullOut) {β ucbar : ℝ} (hu : 0 < ucbar)
    {Lam P lam infl i : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ} (hLam : 𝔼.Adapted Lam)
    (hP : 𝔼.Adapted P) (hPpos : ∀ s ω, 0 < P s ω)
    (hLdef : ∀ s ω, Lam s ω = ucbar * Real.exp (lam s ω) / P s ω)
    (hPinfl : ∀ s ω, P (s + 1) ω = P s ω * Real.exp (infl (s + 1) ω))
    (hcm : CompleteMarkets β Lam Q) (t : ℕ)
    (hQ : ∀ ω, (1 + i t ω) * 𝔼.E t (Q t (t + 1)) ω = 1) (ω : Ω) :
    β * (1 + i t ω) = Real.exp (lam t ω) /
      𝔼.E t (fun ω' => Real.exp (lam (t + 1) ω' - infl (t + 1) ω')) ω := by
  have hpos : ∀ s ω, 0 < Lam s ω := fun s ω => by
    rw [hLdef]; have := hPpos s ω; positivity
  have hfun : P t * Lam (t + 1) =
      ucbar • fun ω' => Real.exp (lam (t + 1) ω' - infl (t + 1) ω') := by
    funext ω'
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    rw [hLdef, hPinfl, Real.exp_sub]
    have := hPpos t ω'
    field_simp
  have hE : P t ω * 𝔼.E t (Lam (t + 1)) ω =
      ucbar * 𝔼.E t (fun ω' => Real.exp (lam (t + 1) ω' - infl (t + 1) ω')) ω := by
    have := congrFun (hpo t (P t) (Lam (t + 1)) (hP t)) ω
    simp only [Pi.mul_apply] at this
    rw [← this, hfun, map_smul]
    rfl
  have hPt := hPpos t ω
  have h1 : Lam t * 𝔼.E t (Q t (t + 1)) = β • 𝔼.E t (Lam (t + 1)) := by
    rw [← hpo t _ _ (hLam t), hcm t (t + 1) (Nat.le_succ t),
      show t + 1 - t = 1 by omega, pow_one, map_smul]
  have h1ω := congrFun h1 ω
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at h1ω
  have hprod : (1 + i t ω) * (β * 𝔼.E t (Lam (t + 1)) ω) = Lam t ω := by
    rw [← h1ω]
    linear_combination Lam t ω * hQ ω
  have hEL : 𝔼.E t (Lam (t + 1)) ω ≠ 0 := by
    intro h0
    rw [h0, mul_zero, mul_zero] at hprod
    linarith [hpos t ω]
  have hEx : 𝔼.E t (fun ω' => Real.exp (lam (t + 1) ω' - infl (t + 1) ω')) ω =
      P t ω * 𝔼.E t (Lam (t + 1)) ω / ucbar := by
    rw [hE]; field_simp
  have hprod' : (1 + i t ω) * (β * 𝔼.E t (Lam (t + 1)) ω) * P t ω =
      ucbar * Real.exp (lam t ω) := by
    rw [hprod, hLdef]; field_simp
  rw [hEx]
  field_simp
  linear_combination hprod'

/-- Woodford (2003), p. 325 (**the log-linearised bond-pricing relation as an exact
derivative**): scaling the log deviations `λ̂` and `π` by `ε`, the exact log gross rate
`log(β(1 + i_t)) = ε λ̂_t − log E_t[exp(ε(λ̂_{t+1} − π_{t+1}))]` (`gross_rate_log_form`) has
derivative `λ̂_t + E_t[π_{t+1} − λ̂_{t+1}]` at the steady state `ε = 0`; this is the book's
`î_t = λ̂_t + E_t[π_{t+1} − λ̂_{t+1}]`. -/
theorem hasDerivAt_log_gross_rate {K : ℝ} {lam infl : ℕ → Ω → ℝ} (t : ℕ)
    (hb : ∀ ω, |lam (t + 1) ω - infl (t + 1) ω| ≤ K) (ω : Ω) :
    HasDerivAt (fun ε => ε * lam t ω -
        Real.log (𝔼.E t (fun ω' => Real.exp (ε * (lam (t + 1) ω' - infl (t + 1) ω'))) ω))
      (lam t ω + 𝔼.E t (infl (t + 1) - lam (t + 1)) ω) 0 := by
  have h1 : 𝔼.E t (fun ω' => Real.exp (0 * (lam (t + 1) ω' - infl (t + 1) ω'))) ω = 1 := by
    simp only [zero_mul, Real.exp_zero]
    rw [𝔼.const]
  have hE := hasDerivAt_E_exp 𝔼 (X := fun ω' => lam (t + 1) ω' - infl (t + 1) ω') hb t ω
  have hlog := hE.log (by rw [h1]; exact one_ne_zero)
  rw [h1, div_one] at hlog
  have hlin : HasDerivAt (fun ε : ℝ => ε * lam t ω) (lam t ω) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (lam t ω)
  refine (HasDerivAt.sub hlin hlog).congr_deriv ?_
  have : (fun ω' => lam (t + 1) ω' - infl (t + 1) ω') = -(infl (t + 1) - lam (t + 1)) := by
    funext ω'; simp
  rw [this, map_neg, Pi.neg_apply]
  ring

/-! ### The forward solution for `λ̂` -/

omit 𝔼 in
/-- Woodford (2003), p. 325: the log-linearised bond-pricing relation
`î_t = λ̂_t + E_t[π_{t+1} − λ̂_{t+1}]` at every date. -/
def LamEq (𝔼 : ExpectationSystem Ω) (i infl lam : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = lam t + 𝔼.E t (infl (t + 1) - lam (t + 1))

/-- Woodford (2003), p. 325 (iterating the bond-pricing relation, conditioned on any earlier
date `s ≤ t`): `E_s λ̂_t = E_s λ̂_{t+k} + ∑_{j<k} E_s(î_{t+j} − π_{t+j+1})`. -/
theorem lam_iterate {i infl lam : ℕ → Ω → ℝ} (h : LamEq 𝔼 i infl lam) {s t : ℕ} (hst : s ≤ t)
    (k : ℕ) : 𝔼.E s (lam t) = 𝔼.E s (lam (t + k)) +
      ∑ j ∈ Finset.range k, 𝔼.E s (i (t + j) - infl (t + j + 1)) :=
  unitRoot_iterate 𝔼 h hst k

/-- Woodford (2003), p. 325 (**the forward solution for `λ̂`**, made precise): along a solution
of the bond-pricing relation, the partial sums of `∑_j E_s(î_{t+j} − π_{t+j+1})` converge to
`E_s λ̂_t − λ̂_∞` if and only if `E_s λ̂_{t+k} → λ̂_∞`. With `s = t` and `λ̂` adapted this is
`λ̂_t = λ̂_∞ + ∑_j E_t(î_{t+j} − π_{t+j+1})` (`ForwardSystems.unitRoot_forward_iff`). -/
theorem lam_forward_iff {i infl lam : ℕ → Ω → ℝ} (h : LamEq 𝔼 i infl lam) {s t : ℕ}
    (hst : s ≤ t) (L : ℝ) (ω : Ω) :
    Tendsto (fun k => ∑ j ∈ Finset.range k, 𝔼.E s (i (t + j) - infl (t + j + 1)) ω) atTop
        (𝓝 (𝔼.E s (lam t) ω - L)) ↔
      Tendsto (fun k => 𝔼.E s (lam (t + k)) ω) atTop (𝓝 L) :=
  unitRoot_forward_iff 𝔼 h hst L ω

/-- Woodford (2003), p. 325 (**boundedness alone does not give the forward solution**): under
perfect foresight, `λ̂_t = (−1)ᵗ`, `π = 0`, `î_t = λ̂_t − λ̂_{t+1}` is a bounded solution of the
bond-pricing relation for which the series `∑_j (î_j − π_{j+1})` diverges; so the book's
`λ̂_t = λ̂_∞ + ∑_j E_t(î_{t+j} − π_{t+j+1})` needs the limit `λ̂_∞ = lim E_t λ̂_{t+k}` to exist
(`lam_forward_iff`). -/
theorem lam_forward_needs_limit :
    LamEq perfectForesight (fun t _ => (-1 : ℝ) ^ t - (-1) ^ (t + 1)) (fun _ _ => 0)
        (fun t _ => (-1) ^ t) ∧
      BoundedProc (fun t (_ : Unit) => (-1 : ℝ) ^ t) ∧
      ¬ ∃ a : ℝ, Tendsto (fun k => ∑ j ∈ Finset.range k,
        ((-1 : ℝ) ^ j - (-1) ^ (j + 1) - 0)) atTop (𝓝 a) := by
  refine ⟨fun t => ?_, ⟨1, fun t _ => by simp⟩, ?_⟩
  · funext ω
    simp [perfectForesight]
    ring
  · rintro ⟨a, ha⟩
    have hd := (ha.comp (tendsto_add_atTop_nat 1)).sub ha
    simp only [sub_self] at hd
    have hterm : (fun k => ((fun k => ∑ j ∈ Finset.range k,
        ((-1 : ℝ) ^ j - (-1) ^ (j + 1) - 0)) ∘ fun n => n + 1) k -
        ∑ j ∈ Finset.range k, ((-1 : ℝ) ^ j - (-1) ^ (j + 1) - 0)) =
        fun k => 2 * (-1 : ℝ) ^ k := by
      funext k
      simp only [Function.comp_apply, Finset.sum_range_succ]
      ring
    rw [hterm] at hd
    have habs := hd.abs
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one, abs_zero] at habs
    have : (fun _ : ℕ => |(2 : ℝ)|) = fun _ => 2 := by norm_num
    rw [this] at habs
    exact absurd (tendsto_nhds_unique habs tendsto_const_nhds) (by norm_num)

/-! ### (1.6) as the exact derivative of (1.5)

The lemmas `quadratic_remainder`, `hasDerivAt_neg_log_E_exp`, `lambdaG`, `sigmaIS`, `gcoef`,
`hasFDerivAt_lambdaG`, `contDiffAt_lambdaG` and `lambdaG_zero` are restated from the Woodford
Chapter 4 project (`NeoWicksellianFramework.BasicModel`); differentiation under `E_t`
(`hasDerivAt_E_of_remainder`, `hasDerivAt_E_exp`) is in `ExpectationCalculus`. -/

/-- Woodford (2003), Ch. 4, §1.2, p. 243 (restated from the Chapter 4 project; the
log-linearisation step of (1.6), made exact): a function that is `C²` at `0` has a quadratic
first-order remainder near `0`, `|f(h) − f(0) − Df(0) h| ≤ C ‖h‖²`. -/
theorem quadratic_remainder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f 0) :
    ∃ C r : ℝ, 0 < r ∧ ∀ h : E, ‖h‖ < r → |f h - f 0 - fderiv ℝ f 0 h| ≤ C * ‖h‖ ^ 2 := by
  have hev : ∀ᶠ y in 𝓝 (0 : E), ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) 0 := hf.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hlip⟩ := h1.exists_lipschitzOnWith
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem ht hev)
  refine ⟨K, r, hr, fun h hh => ?_⟩
  have hsub : Metric.closedBall (0 : E) ‖h‖ ⊆ Metric.ball 0 r :=
    Metric.closedBall_subset_ball hh
  have hdiff : ∀ y ∈ Metric.closedBall (0 : E) ‖h‖, DifferentiableAt ℝ f y := by
    intro y hy
    have hy2 : ContDiffAt ℝ 2 f y := (hball (hsub hy)).2
    exact hy2.differentiableAt (by norm_num)
  have h0t : (0 : E) ∈ t := (hball (Metric.mem_ball_self hr)).1
  have hbound : ∀ y ∈ Metric.closedBall (0 : E) ‖h‖,
      ‖fderiv ℝ f y - fderiv ℝ f 0‖ ≤ K * ‖h‖ := by
    intro y hy
    have hyt : y ∈ t := (hball (hsub hy)).1
    have := lipschitzOnWith_iff_norm_sub_le.mp hlip hyt h0t
    rw [sub_zero] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ K.2)
    simpa using hy
  have := Convex.norm_image_sub_le_of_norm_fderiv_le' (x := 0) (y := h) hdiff hbound
    (convex_closedBall 0 ‖h‖)
    (Metric.mem_closedBall_self (norm_nonneg h)) (by simp)
  rw [sub_zero, Real.norm_eq_abs] at this
  calc |f h - f 0 - fderiv ℝ f 0 h| ≤ K * ‖h‖ * ‖h‖ := this
    _ = K * ‖h‖ ^ 2 := by ring

/-- Woodford (2003), §1.2, p. 243, and Chapter 2, eq. (1.32), p. 79 (**the derivative of the exact
log Euler map, general state space**): let `λ : E → ℝ` vanish at `0` and have a quadratic
first-order remainder with derivative `D` (e.g. `λ` is `C²`, `quadratic_remainder`), and let
`a, b, p` be bounded random directions. Then
`ε ↦ −log E_t[exp(λ(ε a) − λ(ε b) − ε p)]` has derivative `E_t[D b − D a + p]` at `ε = 0`. -/
theorem hasDerivAt_neg_log_E_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {lam : E → ℝ} {D : E →L[ℝ] ℝ} {C r K : ℝ} (hr : 0 < r) (hlam0 : lam 0 = 0)
    (hrem : ∀ h : E, ‖h‖ < r → |lam h - lam 0 - D h| ≤ C * ‖h‖ ^ 2)
    {a b : Ω → E} {p : Ω → ℝ} (ha : ∀ ω, ‖a ω‖ ≤ K) (hb : ∀ ω, ‖b ω‖ ≤ K)
    (hp : ∀ ω, |p ω| ≤ K) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => -Real.log (𝔼.E t (fun ω' =>
        Real.exp (lam (ε • a ω') - lam (ε • b ω') - ε * p ω')) ω))
      (𝔼.E t (fun ω' => D (b ω') - D (a ω') + p ω') ω) 0 := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hp ω)
  set B := ‖D‖ * K * 2 + K with hB
  set c := |C| * K ^ 2 with hc
  set A := B + 2 * c with hA
  have hc0 : 0 ≤ c := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hA0 : 0 ≤ A := by positivity
  set g' : Ω → ℝ := fun ω' => D (a ω') - D (b ω') - p ω' with hg'
  have hDv : ∀ v : E, ‖v‖ ≤ K → |D v| ≤ ‖D‖ * K := fun v hv => by
    rw [← Real.norm_eq_abs]
    exact (D.le_opNorm v).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg D))
  have hg'b : ∀ ω', |g' ω'| ≤ B := by
    intro ω'
    simp only [hg']
    calc |D (a ω') - D (b ω') - p ω'| ≤ |D (a ω')| + |D (b ω')| + |p ω'| := by
          have h1 := abs_sub (D (a ω') - D (b ω')) (p ω')
          have h2 := abs_sub (D (a ω')) (D (b ω'))
          linarith
      _ ≤ ‖D‖ * K + ‖D‖ * K + K :=
          add_le_add (add_le_add (hDv _ (ha ω')) (hDv _ (hb ω'))) (hp ω')
      _ = B := by rw [hB]; ring
  -- the remainder of `λ` along a bounded direction
  have hlr : ∀ (ε : ℝ) (v : E), ‖v‖ ≤ K → |ε| * (K + 1) < r →
      |lam (ε • v) - ε * D v| ≤ c * ε ^ 2 := by
    intro ε v hv hε
    have hn : ‖ε • v‖ ≤ |ε| * K := by
      rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left hv (abs_nonneg ε)
    have hlt : ‖ε • v‖ < r := by nlinarith [abs_nonneg ε]
    have h := hrem (ε • v) hlt
    rw [hlam0, sub_zero, map_smul, smul_eq_mul] at h
    calc |lam (ε • v) - ε * D v| ≤ C * ‖ε • v‖ ^ 2 := h
      _ ≤ |C| * (|ε| * K) ^ 2 := by
          refine mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (norm_nonneg _) hn 2)
            (sq_nonneg _) (abs_nonneg C)
      _ = c * ε ^ 2 := by rw [hc, mul_pow, sq_abs]; ring
  set δ := min (r / (K + 1)) (min 1 (1 / (A + 1))) with hδ
  have hδ0 : 0 < δ := lt_min (div_pos hr (by linarith)) (lt_min one_pos (by positivity))
  set g : ℝ → Ω → ℝ := fun ε ω' => Real.exp (lam (ε • a ω') - lam (ε • b ω') - ε * p ω')
    with hg
  have hrem' : ∀ h, |h| < δ → ∀ ω',
      |g (0 + h) ω' - g 0 ω' - h * g' ω'| ≤ (A ^ 2 + 2 * c) * h ^ 2 := by
    intro h hh ω'
    have hh1 : |h| < r / (K + 1) := lt_of_lt_of_le hh (min_le_left _ _)
    have hh2 : |h| < 1 := lt_of_lt_of_le hh ((min_le_right _ _).trans (min_le_left _ _))
    have hh3 : |h| < 1 / (A + 1) := lt_of_lt_of_le hh ((min_le_right _ _).trans (min_le_right _ _))
    have hr' : |h| * (K + 1) < r := by rwa [lt_div_iff₀ (by linarith)] at hh1
    have ra := hlr h (a ω') (ha ω') hr'
    have rb := hlr h (b ω') (hb ω') hr'
    set e := lam (h • a ω') - lam (h • b ω') - h * p ω' with he
    have hlin : |e - h * g' ω'| ≤ 2 * c * h ^ 2 := by
      have : e - h * g' ω' = (lam (h • a ω') - h * D (a ω')) - (lam (h • b ω') - h * D (b ω')) := by
        simp only [he, hg']; ring
      rw [this]
      have := abs_sub (lam (h • a ω') - h * D (a ω')) (lam (h • b ω') - h * D (b ω'))
      linarith
    have hhg : |h * g' ω'| ≤ |h| * B := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hg'b ω') (abs_nonneg h)
    have hsq : h ^ 2 ≤ |h| := by
      rw [← sq_abs]; nlinarith [abs_nonneg h]
    have he1 : |e| ≤ |h| * A := by
      have := abs_sub_abs_le_abs_sub e (h * g' ω')
      rw [hA]; nlinarith [abs_nonneg h]
    have he2 : |e| ≤ 1 := by
      have : |h| * (A + 1) < 1 := by rwa [lt_div_iff₀ (by linarith)] at hh3
      nlinarith [abs_nonneg h]
    have hexp := Real.abs_exp_sub_one_sub_id_le he2
    have hg0 : g 0 ω' = 1 := by simp [hg, hlam0]
    rw [zero_add, hg0]
    have hgh : g h ω' = Real.exp e := rfl
    rw [hgh]
    have hesq : e ^ 2 ≤ A ^ 2 * h ^ 2 := by
      rw [← sq_abs e, ← sq_abs h, ← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg e) (by linarith [he1]) 2
    calc |Real.exp e - 1 - h * g' ω'| ≤ |Real.exp e - 1 - e| + |e - h * g' ω'| := by
          have : Real.exp e - 1 - h * g' ω' = (Real.exp e - 1 - e) + (e - h * g' ω') := by ring
          rw [this]; exact abs_add_le _ _
      _ ≤ A ^ 2 * h ^ 2 + 2 * c * h ^ 2 := add_le_add (hexp.trans hesq) hlin
      _ = (A ^ 2 + 2 * c) * h ^ 2 := by ring
  have hE := hasDerivAt_E_of_remainder 𝔼 hδ0 hrem' t ω
  have h1 : 𝔼.E t (g 0) ω = 1 := by
    have : g 0 = fun _ => (1 : ℝ) := by funext ω'; simp [hg, hlam0]
    rw [this, 𝔼.const]
  have hlog := hE.log (by rw [h1]; exact one_ne_zero)
  rw [h1, div_one] at hlog
  convert hlog.neg using 1
  have hfun : (fun ω' => D (b ω') - D (a ω') + p ω') = -g' := by
    funext ω'; simp only [hg', Pi.neg_apply]; ring
  rw [hfun, map_neg]
  rfl

/-! ### (1.7) as the exact derivative of the log of (1.1) -/

/-- Woodford (2003), §1.2, p. 243 (and Chapter 2, eq. (1.33)): the log deviation of the marginal
utility of real income, `λ(Ŷ, Ĝ, ξ) = log u_c(Ȳ e^Ŷ − Ḡ − Ȳ Ĝ; ξ) − log u_c(C̄; 0)`, with
`C̄ = Ȳ − Ḡ` and `Ĝ = (G − Ḡ)/Ȳ` (restated from the Chapter 2 project). -/
noncomputable def lambdaG (uc : ℝ × ℝ → ℝ) (Ybar Gbar : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  Real.log (uc (Ybar * Real.exp p.1 - Gbar - Ybar * p.2.1, p.2.2)) -
    Real.log (uc (Ybar - Gbar, 0))

/-- Woodford (2003), fn. 10, p. 243: `σ = s_C σ̃`, with `s_C = C̄/Ȳ` and
`σ̃ = −u_c/(C̄ u_cc)` the intertemporal elasticity of household expenditure. -/
noncomputable def sigmaIS (uc : ℝ × ℝ → ℝ) (Ybar Gbar ucc : ℝ) : ℝ :=
  ((Ybar - Gbar) / Ybar) * (-uc (Ybar - Gbar, 0) / (ucc * (Ybar - Gbar)))

/-- Woodford (2003), fn. 11, p. 243, and (2.3), p. 249: the coefficient of the preference shock
`ξ` in `g = Ĝ + s_C c̄`, `c̄ = −u_cξ ξ/(C̄ u_cc)`. -/
noncomputable def gcoef (Ybar Gbar ucc ucxi : ℝ) : ℝ :=
  (Ybar - Gbar) / Ybar * (-ucxi / ((Ybar - Gbar) * ucc))

/-- Woodford (2003), §1.2, p. 243 (restated from the Chapter 2 project, `hasFDerivAt_lambdaG`):
the derivative of `λ(Ŷ, Ĝ, ξ)` at the steady state is `−σ⁻¹(Ŷ − g)`, `σ = s_C σ̃`,
`g = Ĝ + s_C c̄`. -/
theorem hasFDerivAt_lambdaG {uc : ℝ × ℝ → ℝ} {Ybar Gbar ucc ucxi : ℝ} (hY : 0 < Ybar)
    (hC : 0 < Ybar - Gbar) (hu : 0 < uc (Ybar - Gbar, 0)) (hcc : ucc ≠ 0)
    (huc : HasFDerivAt uc (ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ucxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar - Gbar, 0)) :
    HasFDerivAt (lambdaG uc Ybar Gbar)
      ((-(sigmaIS uc Ybar Gbar ucc)⁻¹) •
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) -
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
          gcoef Ybar Gbar ucc ucxi •
            (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))) 0 := by
  set h : ℝ × ℝ × ℝ → ℝ × ℝ := fun p => (Ybar * Real.exp p.1 - Gbar - Ybar * p.2.1, p.2.2)
    with hh
  have hd1 : HasFDerivAt (fun p : ℝ × ℝ × ℝ => Ybar * Real.exp p.1 - Gbar - Ybar * p.2.1)
      (Ybar • Real.exp (0 : ℝ × ℝ × ℝ).1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) -
        Ybar • ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))) 0 := by
    have h1 := ((hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ))).exp.const_mul Ybar).sub_const
      Gbar
    have h2 := ((hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ).2)).comp (0 : ℝ × ℝ × ℝ)
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ)))).const_mul Ybar
    exact h1.sub h2
  have hd2 : HasFDerivAt (fun p : ℝ × ℝ × ℝ => p.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) 0 :=
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ).2)).comp (0 : ℝ × ℝ × ℝ)
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ)))
  have hd := hd1.prodMk hd2
  have h0 : h 0 = (Ybar - Gbar, 0) := by simp [hh]
  have huc' : HasFDerivAt uc (ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ucxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (h 0) := by rw [h0]; exact huc
  have hcomp := (huc'.comp (0 : ℝ × ℝ × ℝ) hd).log
    (by rw [Function.comp_apply, h0]; exact hu.ne')
  have hfin := hcomp.sub_const (Real.log (uc (Ybar - Gbar, 0)))
  refine hfin.congr_fderiv ?_
  have hC' : Ybar - Gbar ≠ 0 := hC.ne'
  ext
  · simp [h0, sigmaIS, gcoef]
    field_simp
  · simp [h0, sigmaIS, gcoef]
    field_simp
  · simp [h0, sigmaIS, gcoef]
    field_simp

/-- Woodford (2003), §1.2, p. 243: `λ` is `C²` at the steady state when `u_c` is `C²` there and
`u_c(C̄; 0) > 0`. -/
theorem contDiffAt_lambdaG {uc : ℝ × ℝ → ℝ} {Ybar Gbar : ℝ} (hu : 0 < uc (Ybar - Gbar, 0))
    (huc2 : ContDiffAt ℝ 2 uc (Ybar - Gbar, 0)) : ContDiffAt ℝ 2 (lambdaG uc Ybar Gbar) 0 := by
  set h : ℝ × ℝ × ℝ → ℝ × ℝ := fun p => (Ybar * Real.exp p.1 - Gbar - Ybar * p.2.1, p.2.2)
    with hh
  have hin : ContDiff ℝ 2 h := by
    refine ContDiff.prodMk ?_ ?_
    · exact ((contDiff_const.mul (Real.contDiff_exp.comp contDiff_fst)).sub contDiff_const).sub
        (contDiff_const.mul (contDiff_fst.comp contDiff_snd))
    · exact contDiff_snd.comp contDiff_snd
  have h0 : h 0 = (Ybar - Gbar, 0) := by simp [hh]
  have hc : ContDiffAt ℝ 2 (uc ∘ h) 0 :=
    ContDiffAt.comp (0 : ℝ × ℝ × ℝ) (by rw [h0]; exact huc2) hin.contDiffAt
  exact (hc.log (by rw [Function.comp_apply, h0]; exact hu.ne')).sub contDiffAt_const

/-- Woodford (2003), §1.2, p. 243: `λ(0) = 0`. -/
theorem lambdaG_zero (uc : ℝ × ℝ → ℝ) (Ybar Gbar : ℝ) : lambdaG uc Ybar Gbar 0 = 0 := by
  simp [lambdaG]

omit 𝔼 in
/-- Woodford (2003), p. 325 and Ch. 4, fn. 10: `σ = s_C σ̃ ≠ 0` at a steady state with
`Ȳ > 0`, `C̄ = Ȳ − Ḡ > 0`, `u_c(C̄; 0) > 0` and `u_cc ≠ 0`. -/
theorem sigmaIS_ne_zero {uc : ℝ × ℝ → ℝ} {Ybar Gbar ucc : ℝ} (hY : 0 < Ybar)
    (hC : 0 < Ybar - Gbar) (hu : 0 < uc (Ybar - Gbar, 0)) (hcc : ucc ≠ 0) :
    sigmaIS uc Ybar Gbar ucc ≠ 0 := by
  unfold sigmaIS
  have h1 : (Ybar - Gbar) / Ybar ≠ 0 := div_ne_zero hC.ne' hY.ne'
  have h2 : -uc (Ybar - Gbar, 0) / (ucc * (Ybar - Gbar)) ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr hu.ne') (mul_ne_zero hcc hC.ne')
  exact mul_ne_zero h1 h2

omit 𝔼 in
/-- Woodford (2003), p. 325: the derivative of `λ(Ŷ, Ĝ, ξ)` evaluated on a deviation vector,
`Dλ(Ŷ, Ĝ, ξ) = −σ⁻¹(Ŷ − (Ĝ + g_c ξ))`. -/
theorem lambdaG_deriv_apply (σ gc a b c : ℝ) :
    ((-σ⁻¹) • (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) -
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
          gc • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))))
      (a, b, c) = -σ⁻¹ * (a - (b + gc * c)) := by
  simp

/-- Woodford (2003), p. 324 (tool): the conditional expectation of `e^f` for `f ≥ −K` is at
least `e^{−K} > 0`. -/
theorem exp_neg_le_E_exp {K : ℝ} {f : Ω → ℝ} (hf : ∀ ω, -K ≤ f ω) (t : ℕ) (ω : Ω) :
    Real.exp (-K) ≤ 𝔼.E t (fun ω' => Real.exp (f ω')) ω := by
  have hl : (fun _ => Real.exp (-K)) ≤ fun ω' => Real.exp (f ω') :=
    fun ω' => Real.exp_le_exp.mpr (hf ω')
  have h0 := 𝔼.mono t hl ω
  rwa [𝔼.const] at h0

/-- Woodford (2003), eq. (1.5), p. 324 (exact log form): with marginal utilities
`u_c(C_s; ξ_s) = ū_c e^{λ(Ŷ_s, Ĝ_s, ξ_s)}` and `Λ_s P_s = ū_c e^{λ̂_s}`, both log deviations
bounded below, (1.5) at date `t + d` holds iff
`log E_t[e^{λ(v_{t+d})}] − log E_t[e^{λ̂_{t+d}}] = 0` in every state. -/
theorem foc15_log_form {ucbar K : ℝ} (hu : 0 < ucbar) {m lamv lam LP : ℕ → Ω → ℝ}
    (hm : ∀ s ω, m s ω = ucbar * Real.exp (lamv s ω))
    (hLP : ∀ s ω, LP s ω = ucbar * Real.exp (lam s ω)) (hv : ∀ s ω, -K ≤ lamv s ω)
    (hl : ∀ s ω, -K ≤ lam s ω) (d t : ℕ) :
    𝔼.E t (m (t + d)) = 𝔼.E t (LP (t + d)) ↔ ∀ ω,
      Real.log (𝔼.E t (fun ω' => Real.exp (lamv (t + d) ω')) ω) -
        Real.log (𝔼.E t (fun ω' => Real.exp (lam (t + d) ω')) ω) = 0 := by
  have hm' : m (t + d) = ucbar • fun ω' => Real.exp (lamv (t + d) ω') := by
    funext ω'; simp [hm]
  have hL' : LP (t + d) = ucbar • fun ω' => Real.exp (lam (t + d) ω') := by
    funext ω'; simp [hLP]
  rw [hm', hL', map_smul, map_smul]
  have hp1 := fun ω => (Real.exp_pos (-K)).trans_le
    (exp_neg_le_E_exp 𝔼 (f := lamv (t + d)) (hv (t + d)) t ω)
  have hp2 := fun ω => (Real.exp_pos (-K)).trans_le
    (exp_neg_le_E_exp 𝔼 (f := lam (t + d)) (hl (t + d)) t ω)
  constructor
  · intro h ω
    have := congrFun h ω
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [mul_right_injective₀ hu.ne' this, sub_self]
  · intro h
    funext ω
    have h1 := h ω
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [sub_eq_zero] at h1
    rw [Real.log_injOn_pos (Set.mem_Ioi.mpr (hp1 ω)) (Set.mem_Ioi.mpr (hp2 ω)) h1]

/-- Woodford (2003), eq. (1.6), p. 325 (**(1.6) as the exact derivative of the log of (1.5)**,
general state space): scale the deviations `v_s = (Ŷ_s, Ĝ_s, ξ_s)` and `λ̂_s` by `ε`. If
consumption `Ĉ_{t+d} = Ŷ_{t+d} − Ĝ_{t+d}` is chosen at `t` (known at `t`), `u_c` is `C²` at
`(C̄, 0)` with partials `u_cc ≠ 0`, `u_cξ`, and the deviations are bounded, then the exact log
form of (1.5) (`foc15_log_form`),
`ε ↦ log E_t[e^{λ(ε v_{t+d})}] − log E_t[e^{ε λ̂_{t+d}}]`, has derivative
`−σ⁻¹(Ŷ_{t+d} − g_{t+d}) − E_t λ̂_{t+d}` at `ε = 0`, with `g = Ĝ + s_C E_t c̄`
(`s_C c̄ = g_c ξ`). -/
theorem eq16_deriv {uc : ℝ × ℝ → ℝ} {Ybar Gbar ucc ucxi K : ℝ} (hY : 0 < Ybar)
    (hC : 0 < Ybar - Gbar) (hu : 0 < uc (Ybar - Gbar, 0)) (hcc : ucc ≠ 0)
    (huc : HasFDerivAt uc (ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ucxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar - Gbar, 0))
    (huc2 : ContDiffAt ℝ 2 uc (Ybar - Gbar, 0)) {Yh Gh xi lam : ℕ → Ω → ℝ}
    (hYb : ∀ s ω, |Yh s ω| ≤ K) (hGb : ∀ s ω, |Gh s ω| ≤ K) (hxb : ∀ s ω, |xi s ω| ≤ K)
    (hlb : ∀ s ω, |lam s ω| ≤ K) (d t : ℕ)
    (hpre : 𝔼.E t (Yh (t + d) - Gh (t + d)) = Yh (t + d) - Gh (t + d)) (ω : Ω) :
    HasDerivAt (fun ε => Real.log (𝔼.E t (fun ω' => Real.exp (lambdaG uc Ybar Gbar
          (ε • (Yh (t + d) ω', Gh (t + d) ω', xi (t + d) ω')))) ω) -
        Real.log (𝔼.E t (fun ω' => Real.exp (ε * lam (t + d) ω')) ω))
      (-(sigmaIS uc Ybar Gbar ucc)⁻¹ * (Yh (t + d) ω - (Gh (t + d) ω +
          gcoef Ybar Gbar ucc ucxi * 𝔼.E t (xi (t + d)) ω)) - 𝔼.E t (lam (t + d)) ω) 0 := by
  have hF := hasFDerivAt_lambdaG hY hC hu hcc huc
  obtain ⟨C, r, hr, hrem⟩ := quadratic_remainder (contDiffAt_lambdaG hu huc2)
  rw [hF.fderiv] at hrem
  have hnorm : ∀ ω', ‖((Yh (t + d) ω', Gh (t + d) ω', xi (t + d) ω') : ℝ × ℝ × ℝ)‖ ≤ K := by
    intro ω'
    rw [Prod.norm_def, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le (hYb _ ω') (max_le (hGb _ ω') (hxb _ ω'))
  have hK : 0 ≤ K := (abs_nonneg _).trans (hYb 0 ω)
  have h1 := hasDerivAt_neg_log_E_exp 𝔼 hr (lambdaG_zero uc Ybar Gbar) hrem
    (a := fun ω' => (Yh (t + d) ω', Gh (t + d) ω', xi (t + d) ω'))
    (b := fun _ => 0) (p := fun _ => 0) hnorm (fun _ => by simpa using hK)
    (fun _ => by simpa using hK) t ω
  have hfun1 : (fun ε => -Real.log (𝔼.E t (fun ω' => Real.exp
      (lambdaG uc Ybar Gbar (ε • (Yh (t + d) ω', Gh (t + d) ω', xi (t + d) ω')) -
        lambdaG uc Ybar Gbar (ε • (0 : ℝ × ℝ × ℝ)) - ε * 0)) ω)) =
      fun ε => -Real.log (𝔼.E t (fun ω' => Real.exp (lambdaG uc Ybar Gbar
        (ε • (Yh (t + d) ω', Gh (t + d) ω', xi (t + d) ω')))) ω) := by
    funext ε
    simp [lambdaG_zero]
  rw [hfun1] at h1
  have h2one : 𝔼.E t (fun ω' => Real.exp (0 * lam (t + d) ω')) ω = 1 := by
    simp only [zero_mul, Real.exp_zero]; rw [𝔼.const]
  have h2 := (hasDerivAt_E_exp 𝔼 (hlb (t + d)) t ω).log (by rw [h2one]; exact one_ne_zero)
  rw [h2one, div_one] at h2
  have h1' := HasDerivAt.neg h1
  simp only [Pi.neg_def, neg_neg] at h1'
  refine (HasDerivAt.sub h1' h2).congr_deriv ?_
  set σ := sigmaIS uc Ybar Gbar ucc
  set gc := gcoef Ybar Gbar ucc ucxi
  have hfun : (fun ω' => ((-σ⁻¹) • (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) -
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
          gc • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))))
          (0 : ℝ × ℝ × ℝ) -
      ((-σ⁻¹) • (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) -
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
          gc • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))))
          (Yh (t + d) ω', Gh (t + d) ω', xi (t + d) ω') + (fun _ => (0 : ℝ)) ω') =
      σ⁻¹ • ((Yh (t + d) - Gh (t + d)) - gc • xi (t + d)) := by
    funext ω'
    rw [map_zero, lambdaG_deriv_apply]
    simp only [zero_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, add_zero]
    ring
  rw [hfun, map_smul, map_sub, hpre, map_smul]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- Woodford (2003), eq. (1.6), p. 325: the exact derivative of `eq16_deriv` vanishes iff
`Ŷ_{t+d} = g_{t+d} − σ E_t λ̂_{t+d}`, `g = Ĝ + s_C E_t c̄` — i.e. (1.6) with delay `d`. -/
theorem eq16_iff_deriv_zero {σ : ℝ} (hσ : σ ≠ 0) (gc Y G Exi El : ℝ) :
    -σ⁻¹ * (Y - (G + gc * Exi)) - El = 0 ↔ Y = (G + gc * Exi) - σ * El := by
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- Woodford (2003), eq. (1.22), p. 331 (**the information-delay interpretation, as an exact
derivative**): if spending is chosen at `t + d` to satisfy `u_c(C_{t+d}; ξ_{t+d}) =
E_t[Λ_{t+d} P_{t+d}]`, the exact log form `λ(ε v_{t+d}) − log E_t[e^{ε λ̂_{t+d}}]` has derivative
`−σ⁻¹(Ŷ_{t+d} − (Ĝ_{t+d} + s_C c̄_{t+d})) − E_t λ̂_{t+d}`; it vanishes iff (1.6) holds with
`g = Ĝ + s_C c̄` (no forecast of the taste shock). No predetermination is assumed. -/
theorem eq122_deriv {uc : ℝ × ℝ → ℝ} {Ybar Gbar ucc ucxi K : ℝ} (hY : 0 < Ybar)
    (hC : 0 < Ybar - Gbar) (hu : 0 < uc (Ybar - Gbar, 0)) (hcc : ucc ≠ 0)
    (huc : HasFDerivAt uc (ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ucxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar - Gbar, 0)) {Yh Gh xi lam : ℕ → Ω → ℝ}
    (hlb : ∀ s ω, |lam s ω| ≤ K) (d t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => lambdaG uc Ybar Gbar
          (ε • (Yh (t + d) ω, Gh (t + d) ω, xi (t + d) ω)) -
        Real.log (𝔼.E t (fun ω' => Real.exp (ε * lam (t + d) ω')) ω))
      (-(sigmaIS uc Ybar Gbar ucc)⁻¹ * (Yh (t + d) ω - (Gh (t + d) ω +
          gcoef Ybar Gbar ucc ucxi * xi (t + d) ω)) - 𝔼.E t (lam (t + d)) ω) 0 := by
  have hF := hasFDerivAt_lambdaG hY hC hu hcc huc
  set v : ℝ × ℝ × ℝ := (Yh (t + d) ω, Gh (t + d) ω, xi (t + d) ω)
  have hpath : HasDerivAt (fun ε : ℝ => ε • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have h1 := hF.comp_hasDerivAt_of_eq (0 : ℝ) hpath (by simp)
  have h2one : 𝔼.E t (fun ω' => Real.exp (0 * lam (t + d) ω')) ω = 1 := by
    simp only [zero_mul, Real.exp_zero]; rw [𝔼.const]
  have h2 := (hasDerivAt_E_exp 𝔼 (hlb (t + d)) t ω).log (by rw [h2one]; exact one_ne_zero)
  rw [h2one, div_one] at h2
  refine (HasDerivAt.sub h1 h2).congr_deriv ?_
  rw [lambdaG_deriv_apply]

/-! ### The IS relation with predetermined expenditure: (1.6)–(1.8) -/

omit 𝔼 in
/-- Woodford (2003), eq. (1.6), p. 325, written at date `t + d` and conditioned on date `t`:
`Ŷ_{t+d} = g_{t+d} − σ E_t λ̂_{t+d}`. -/
def Eq16 (𝔼 : ExpectationSystem Ω) (σ : ℝ) (d : ℕ) (Y g lam : ℕ → Ω → ℝ) : Prop :=
  ∀ t, Y (t + d) = g (t + d) - σ • 𝔼.E t (lam (t + d))

omit 𝔼 in
/-- Woodford (2003), eq. (1.7), p. 325, with the series read as the limit of its partial sums:
`Ŷ_{t+d} = Ŷ_∞ + g_{t+d} − σ ∑_{j ≥ 0} E_t(î_{t+d+j} − π_{t+d+j+1})`. -/
def IS17 (𝔼 : ExpectationSystem Ω) (σ Yinf : ℝ) (d : ℕ) (Y g i infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Tendsto (fun k => ∑ j ∈ Finset.range k, 𝔼.E t (i (t + d + j) - infl (t + d + j + 1)) ω)
    atTop (𝓝 ((Yinf + g (t + d) ω - Y (t + d) ω) / σ))

omit 𝔼 in
/-- Woodford (2003), eq. (1.8), p. 325, at date `t + d`:
`Ŷ_{t+d} = g_{t+d} + E_t(Ŷ_{t+d+1} − g_{t+d+1}) − σ E_t(î_{t+d} − π_{t+d+1})`. -/
def IS18 (𝔼 : ExpectationSystem Ω) (σ : ℝ) (d : ℕ) (Y g i infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, Y (t + d) = g (t + d) + 𝔼.E t (Y (t + d + 1) - g (t + d + 1)) -
    σ • 𝔼.E t (i (t + d) - infl (t + d + 1))

/-- Woodford (2003), eqs. (1.6)–(1.7), p. 325 (**(1.6) and the forward solution for `λ̂` give
(1.7)**): if `E_t λ̂_{t+d+k} → λ̂_∞` (the limit the book calls `λ̂_∞`), then (1.7) holds with
`Ŷ_∞ = −σ λ̂_∞`. -/
theorem is17_of_eq16 {σ lamInf : ℝ} (hσ : σ ≠ 0) {d : ℕ} {Y g i infl lam : ℕ → Ω → ℝ}
    (h16 : Eq16 𝔼 σ d Y g lam) (hlam : LamEq 𝔼 i infl lam)
    (hlim : ∀ t ω, Tendsto (fun k => 𝔼.E t (lam (t + d + k)) ω) atTop (𝓝 lamInf)) :
    IS17 𝔼 σ (-σ * lamInf) d Y g i infl := by
  intro t ω
  have h := (lam_forward_iff 𝔼 hlam (Nat.le_add_right t d) lamInf ω).mpr (hlim t ω)
  have hY := congrFun (h16 t) ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hY
  have : (-σ * lamInf + g (t + d) ω - Y (t + d) ω) / σ = 𝔼.E t (lam (t + d)) ω - lamInf := by
    rw [hY]; field_simp; ring
  rw [this]
  exact h

/-- Woodford (2003), eq. (1.8), p. 325 (iterating (1.8)): with `W = Ŷ − g`,
`W_{t+d} = E_t W_{t+d+k} − σ ∑_{j<k} E_t(î_{t+d+j} − π_{t+d+j+1})`, and `W_{t+d}` is known at
`t`. -/
theorem is18_iterate {σ : ℝ} {d : ℕ} {Y g i infl : ℕ → Ω → ℝ} (h : IS18 𝔼 σ d Y g i infl)
    (t k : ℕ) : Y (t + d) - g (t + d) = 𝔼.E t (Y (t + d + k) - g (t + d + k)) -
      σ • ∑ j ∈ Finset.range k, 𝔼.E t (i (t + d + j) - infl (t + d + j + 1)) := by
  induction k with
  | zero =>
    simp only [add_zero, Finset.range_zero, Finset.sum_empty, smul_zero, sub_zero]
    have := h t
    have hk : 𝔼.E t (Y (t + d) - g (t + d)) = Y (t + d) - g (t + d) := by
      rw [this]
      simp only [map_sub, map_add, map_smul, 𝔼.E_E_self]
      abel
    exact hk.symm
  | succ k ih =>
    have hk := h (t + k)
    rw [show t + k + d = t + d + k by omega] at hk
    have hE := congrArg (𝔼.E t) hk
    simp only [map_sub, map_add, map_smul, 𝔼.tower (Nat.le_add_right t k)] at hE
    rw [ih, Finset.sum_range_succ, smul_add]
    funext ω
    have hEω := congrFun hE ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub] at hEω ⊢
    simp only [← add_assoc] at hEω ⊢
    linarith

omit 𝔼 in
/-- Woodford (2003), p. 325 (the interchange of `E_t` and a convergent limit used to pass from
(1.7) to (1.8)): `E_t` maps pointwise-convergent sequences of random variables to pointwise
convergent sequences. This holds on every finite state space (`limitExchange_of_finite`, so on
every finite event tree and under perfect foresight); it is not implied by the
`ExpectationSystem` axioms, so it is a hypothesis where needed. -/
def LimitExchange (𝔼 : ExpectationSystem Ω) : Prop :=
  ∀ t (f : ℕ → Ω → ℝ) (F : Ω → ℝ), (∀ ω, Tendsto (fun k => f k ω) atTop (𝓝 (F ω))) →
    ∀ ω, Tendsto (fun k => 𝔼.E t (f k) ω) atTop (𝓝 (𝔼.E t F ω))

/-- Woodford (2003), p. 325: on a finite state space every expectation system satisfies
`LimitExchange` (`E_t` is a linear map on a finite-dimensional space, hence continuous). -/
theorem limitExchange_of_finite [Finite Ω] : LimitExchange 𝔼 := by
  intro t f F hf ω
  have := Fintype.ofFinite Ω
  have hF : Tendsto f atTop (𝓝 F) := tendsto_pi_nhds.mpr hf
  have hc : Continuous (𝔼.E t) := LinearMap.continuous_of_finiteDimensional _
  exact tendsto_pi_nhds.mp ((hc.tendsto F).comp hF) ω

/-- Woodford (2003), eqs. (1.7)–(1.8), p. 325 (**(1.7) ⟺ (1.8)**, the "differenced form"):
given `LimitExchange` and `σ ≠ 0`, (1.7) with long-run level `Ŷ_∞` holds iff (1.8) holds and
the forecasts `E_t(Ŷ − g)_{t+d+k}` converge to `Ŷ_∞` (the boundary condition that (1.8) alone
cannot impose). -/
theorem is17_iff_is18 (hc : LimitExchange 𝔼) {σ Yinf : ℝ} (hσ : σ ≠ 0) {d : ℕ}
    {Y g i infl : ℕ → Ω → ℝ} :
    IS17 𝔼 σ Yinf d Y g i infl ↔ IS18 𝔼 σ d Y g i infl ∧
      ∀ t ω, Tendsto (fun k => 𝔼.E t (Y (t + d + k) - g (t + d + k)) ω) atTop (𝓝 Yinf) := by
  set r : ℕ → Ω → ℝ := fun s => i s - infl (s + 1) with hr
  set S : ℕ → ℕ → Ω → ℝ := fun t k => ∑ j ∈ Finset.range k, 𝔼.E t (r (t + d + j)) with hS
  have hSapp : ∀ t k ω, S t k ω =
      ∑ j ∈ Finset.range k, 𝔼.E t (i (t + d + j) - infl (t + d + j + 1)) ω := by
    intro t k ω
    simp [hS, hr, Finset.sum_apply]
  -- the forward direction of the limit statement, from the iterated (1.8)
  have hlimit : IS18 𝔼 σ d Y g i infl → ∀ t ω,
      Tendsto (fun k => 𝔼.E t (Y (t + d + k) - g (t + d + k)) ω) atTop (𝓝 Yinf) →
      Tendsto (fun k => S t k ω) atTop (𝓝 ((Yinf + g (t + d) ω - Y (t + d) ω) / σ)) := by
    intro h18 t ω hl
    have hk : ∀ k, S t k ω =
        (𝔼.E t (Y (t + d + k) - g (t + d + k)) ω - (Y (t + d) ω - g (t + d) ω)) / σ := by
      intro k
      have := congrFun (is18_iterate 𝔼 h18 t k) ω
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at this
      rw [hSapp]
      field_simp
      linarith
    simp_rw [hk]
    have := (hl.sub_const (Y (t + d) ω - g (t + d) ω)).div_const σ
    convert this using 2
    ring
  constructor
  · intro h17
    have h17' : ∀ t ω, Tendsto (fun k => S t k ω) atTop
        (𝓝 ((Yinf + g (t + d) ω - Y (t + d) ω) / σ)) := by
      intro t ω
      simp_rw [hSapp]
      exact h17 t ω
    have h18 : IS18 𝔼 σ d Y g i infl := by
      intro t
      funext ω
      -- limits of the date-(t+1) sums, conditioned on t
      have hE := hc t (fun k => S (t + 1) k)
        (fun ω' => (Yinf + g (t + 1 + d) ω' - Y (t + 1 + d) ω') / σ) (h17' (t + 1)) ω
      have hEk : ∀ k, 𝔼.E t (S (t + 1) k) ω =
          ∑ j ∈ Finset.range k, 𝔼.E t (r (t + d + 1 + j)) ω := by
        intro k
        simp only [hS, map_sum, Finset.sum_apply, 𝔼.tower (Nat.le_succ t)]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show t + 1 + d + j = t + d + 1 + j by omega]
      simp_rw [hEk] at hE
      have hshift : Tendsto (fun k => S t (k + 1) ω) atTop
          (𝓝 ((Yinf + g (t + d) ω - Y (t + d) ω) / σ)) :=
        (h17' t ω).comp (tendsto_add_atTop_nat 1)
      have hsplit : ∀ k, S t (k + 1) ω = 𝔼.E t (r (t + d)) ω +
          ∑ j ∈ Finset.range k, 𝔼.E t (r (t + d + 1 + j)) ω := by
        intro k
        simp only [hS, Finset.sum_apply]
        rw [Finset.sum_range_succ', add_comm, add_zero]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show t + d + (j + 1) = t + d + 1 + j by omega]
      simp_rw [hsplit] at hshift
      have h2 := hE.const_add (𝔼.E t (r (t + d)) ω)
      have heq := tendsto_nhds_unique hshift h2
      have hEF : 𝔼.E t (fun ω' => (Yinf + g (t + 1 + d) ω' - Y (t + 1 + d) ω') / σ) ω =
          (Yinf - 𝔼.E t (Y (t + d + 1) - g (t + d + 1)) ω) / σ := by
        have hfun : (fun ω' => (Yinf + g (t + 1 + d) ω' - Y (t + 1 + d) ω') / σ) =
            σ⁻¹ • ((fun _ => Yinf) - (Y (t + d + 1) - g (t + d + 1))) := by
          funext ω'
          simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          rw [show t + 1 + d = t + d + 1 by omega]
          field_simp
          ring
        rw [hfun, map_smul, map_sub, 𝔼.const]
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        field_simp
      rw [hEF] at heq
      have e1 := div_mul_cancel₀ (Yinf + g (t + d) ω - Y (t + d) ω) hσ
      have e2 := div_mul_cancel₀ (Yinf - 𝔼.E t (Y (t + d + 1) - g (t + d + 1)) ω) hσ
      have h4 : Yinf + g (t + d) ω - Y (t + d) ω = σ * 𝔼.E t (r (t + d)) ω +
          (Yinf - 𝔼.E t (Y (t + d + 1) - g (t + d + 1)) ω) := by
        rw [← e1, heq, add_mul, e2]
        ring
      have hB : 𝔼.E t (r (t + d)) ω = 𝔼.E t (i (t + d)) ω - 𝔼.E t (infl (t + d + 1)) ω := by
        simp [hr, map_sub]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub] at h4 ⊢
      rw [hB] at h4
      linarith
    refine ⟨h18, fun t ω => ?_⟩
    have hk : ∀ k, 𝔼.E t (Y (t + d + k) - g (t + d + k)) ω =
        (Y (t + d) ω - g (t + d) ω) + σ * S t k ω := by
      intro k
      have := congrFun (is18_iterate 𝔼 h18 t k) ω
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at this
      rw [hSapp]
      linarith
    simp_rw [hk]
    have := ((h17' t ω).const_mul σ).const_add (Y (t + d) ω - g (t + d) ω)
    convert this using 2
    field_simp
    ring
  · rintro ⟨h18, hl⟩ t ω
    have := hlimit h18 t ω (hl t ω)
    simp_rw [hSapp] at this
    exact this

/-! ### The gap form (1.10)–(1.11) and the delayed AS relation (1.9) -/

omit 𝔼 in
/-- Woodford (2003), eq. (2.3), p. 337 (and Ch. 4 (2.3)): the natural rate of interest,
`σ r̂ⁿ_s = (g_s − Ŷⁿ_s) − E_s(g_{s+1} − Ŷⁿ_{s+1})`, written with `u = g − Ŷⁿ`. -/
def NatRate (𝔼 : ExpectationSystem Ω) (σ : ℝ) (rn u : ℕ → Ω → ℝ) : Prop :=
  ∀ s, σ • rn s = u s - 𝔼.E s (u (s + 1))

omit 𝔼 in
/-- Woodford (2003), eq. (1.10), p. 326, at date `t + d`: the forecastable component of the
output gap, `E_t x_{t+d} = E_t x_{t+d+1} − σ E_t(î_{t+d} − π_{t+d+1} − r̂ⁿ_{t+d})`. -/
def IS110 (𝔼 : ExpectationSystem Ω) (σ : ℝ) (d : ℕ) (x i infl rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, 𝔼.E t (x (t + d)) = 𝔼.E t (x (t + d + 1)) -
    σ • 𝔼.E t (i (t + d) - infl (t + d + 1) - rn (t + d))

omit 𝔼 in
/-- Woodford (2003), eq. (1.11), p. 326, at date `t + d`: the unforecastable component of the
gap is exogenous, `x_{t+d} = E_t x_{t+d} + (u_{t+d} − E_t u_{t+d})`, `u = g − Ŷⁿ`. -/
def Gap111 (𝔼 : ExpectationSystem Ω) (d : ℕ) (x u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x (t + d) = 𝔼.E t (x (t + d)) + (u (t + d) - 𝔼.E t (u (t + d)))

/-- Woodford (2003), eqs. (1.8), (1.10), (1.11), p. 326 (**(1.10) and (1.11) are jointly
equivalent to (1.8)**): with the output gap `x = Ŷ − Ŷⁿ`, `u = g − Ŷⁿ` and the natural rate
(2.3), the IS relation (1.8) holds iff both (1.10) and (1.11) hold. Only linearity and the law
of iterated expectations are used. -/
theorem is18_iff_is110_gap111 {σ : ℝ} {d : ℕ} {Y g Yn x u i infl rn : ℕ → Ω → ℝ}
    (hx : ∀ s, x s = Y s - Yn s) (hu : ∀ s, u s = g s - Yn s) (hrn : NatRate 𝔼 σ rn u) :
    IS18 𝔼 σ d Y g i infl ↔ IS110 𝔼 σ d x i infl rn ∧ Gap111 𝔼 d x u := by
  have hW : ∀ s, Y s - g s = x s - u s := fun s => by rw [hx, hu]; abel
  -- `E_t (σ r̂ⁿ_{t+d}) = E_t u_{t+d} − E_t u_{t+d+1}`
  have hR : ∀ t, σ • 𝔼.E t (rn (t + d)) = 𝔼.E t (u (t + d)) - 𝔼.E t (u (t + d + 1)) := by
    intro t
    rw [← map_smul, hrn (t + d), map_sub, 𝔼.tower (Nat.le_add_right t d)]
  have hW' : ∀ t ω, 𝔼.E t (Y (t + d + 1) - g (t + d + 1)) ω =
      𝔼.E t (x (t + d + 1)) ω - 𝔼.E t (u (t + d + 1)) ω := by
    intro t ω; rw [hW, map_sub]; rfl
  constructor
  · intro h
    -- `W_{t+d}` is known at `t`
    have hknown : ∀ t, 𝔼.E t (x (t + d) - u (t + d)) = x (t + d) - u (t + d) := by
      intro t
      rw [← hW, h t]
      simp only [map_sub, map_add, map_smul, 𝔼.E_E_self]
      abel
    have hgap : Gap111 𝔼 d x u := by
      intro t
      funext ω
      have e2 := congrFun (hknown t) ω
      simp only [Pi.add_apply, Pi.sub_apply, map_sub] at e2 ⊢
      linarith
    refine ⟨fun t => ?_, hgap⟩
    funext ω
    have e1 := congrFun (h t) ω
    have e2 := congrFun (hknown t) ω
    have e3 := congrFun (hR t) ω
    have e4 := congrFun (hW (t + d)) ω
    have e6 := hW' t ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub] at e1 e2 e3 e4 e6 ⊢
    linarith
  · rintro ⟨h10, h11⟩ t
    funext ω
    have e1 := congrFun (h10 t) ω
    have e2 := congrFun (h11 t) ω
    have e3 := congrFun (hR t) ω
    have e4 := congrFun (hW (t + d)) ω
    have e6 := hW' t ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub] at e1 e2 e3 e4 e6 ⊢
    linarith

omit 𝔼 in
/-- Woodford (2003), eq. (1.9), p. 326, at date `t + d`: the delayed aggregate-supply relation
`π_{t+d} = κ E_t x_{t+d} + β E_t π_{t+d+1}`. -/
def NKPC19 (𝔼 : ExpectationSystem Ω) (κ β : ℝ) (d : ℕ) (infl x : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl (t + d) = κ • 𝔼.E t (x (t + d)) + β • 𝔼.E t (infl (t + d + 1))

/-- Woodford (2003), fn. 6, p. 328: under (1.9), `π_{t+d}` is entirely forecastable at `t`. -/
theorem infl_forecastable {κ β : ℝ} {d : ℕ} {infl x : ℕ → Ω → ℝ} (h : NKPC19 𝔼 κ β d infl x)
    (t : ℕ) : 𝔼.E t (infl (t + d)) = infl (t + d) := by
  rw [h t, map_add, map_smul, map_smul, 𝔼.E_E_self, 𝔼.E_E_self]

/-- Woodford (2003), fn. 6, p. 328: under (1.11), the unforecastable component of `x_{t+d}` is
purely exogenous, `x_{t+d} − E_t x_{t+d} = u_{t+d} − E_t u_{t+d}`. -/
theorem gap_unforecastable {d : ℕ} {x u : ℕ → Ω → ℝ} (h : Gap111 𝔼 d x u) (t : ℕ) :
    x (t + d) - 𝔼.E t (x (t + d)) = u (t + d) - 𝔼.E t (u (t + d)) := by
  nth_rw 1 [h t]
  abel

/-! ### The discrepancy `μ_t`, (1.18)–(1.21), and the AS relation (1.20) -/

omit 𝔼 in
/-- Woodford (2003), eq. (1.19), p. 329: `μ_t ≡ λ̂_t − σ⁻¹(g_t − Ŷ_t)`, the gap between the
log marginal utility of real income and that of consumption. -/
noncomputable def mu (σ : ℝ) (lam g Y : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun s => lam s - σ⁻¹ • (g s - Y s)

omit 𝔼 in
/-- Woodford (2003), eq. (1.18), p. 329: log real marginal cost of good `i` with flexible wages,
`ŝ_t(i) = ω(ŷ_t(i) − Ŷⁿ_t) + σ⁻¹(Ŷ_t − Ŷⁿ_t) − μ_t`. -/
noncomputable def realMC (ω σ : ℝ) (yi Yn Y m : Ω → ℝ) : Ω → ℝ :=
  ω • (yi - Yn) + σ⁻¹ • (Y - Yn) - m

omit 𝔼 in
/-- Woodford (2003), eqs. (1.18)–(1.19), p. 329: real marginal cost depends on the marginal
utility of income `λ̂`, not on that of consumption:
`ŝ_t(i) = ω(ŷ_t(i) − Ŷⁿ_t) + σ⁻¹(g_t − Ŷⁿ_t) − λ̂_t`. -/
theorem realMC_eq_lam (ω σ : ℝ) (lam g Y : ℕ → Ω → ℝ) (yi Yn : Ω → ℝ) (s : ℕ) :
    realMC ω σ yi Yn (Y s) (mu σ lam g Y s) = ω • (yi - Yn) + σ⁻¹ • (g s - Yn) - lam s := by
  unfold realMC mu
  module

omit 𝔼 in
/-- Woodford (2003), p. 330: when expenditure is chosen at `t` (`μ_t = 0`), (1.18) is the
Chapter 3 marginal-cost function; averaged at `ŷ(i) = Ŷ` it is `ω_mc x_t − μ_t` with
`ω_mc = ω + σ⁻¹` and `x = Ŷ − Ŷⁿ`. -/
theorem realMC_avg (ω σ : ℝ) (Yn Y m : Ω → ℝ) :
    realMC ω σ Y Yn Y m = (ω + σ⁻¹) • (Y - Yn) - m := by
  unfold realMC
  module

/-- Woodford (2003), p. 330: (1.6) implies `μ_{t+d} = λ̂_{t+d} − E_t λ̂_{t+d}` (`σ ≠ 0`). -/
theorem mu_eq_lam_sub {σ : ℝ} (hσ : σ ≠ 0) {d : ℕ} {Y g lam : ℕ → Ω → ℝ}
    (h16 : Eq16 𝔼 σ d Y g lam) (t : ℕ) :
    mu σ lam g Y (t + d) = lam (t + d) - 𝔼.E t (lam (t + d)) := by
  unfold mu
  rw [h16 t]
  funext ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Woodford (2003), p. 330: (1.6) implies only `E_{t−d} μ_t = 0`. -/
theorem E_mu_zero {σ : ℝ} (hσ : σ ≠ 0) {d : ℕ} {Y g lam : ℕ → Ω → ℝ}
    (h16 : Eq16 𝔼 σ d Y g lam) (t : ℕ) : 𝔼.E t (mu σ lam g Y (t + d)) = 0 := by
  rw [mu_eq_lam_sub 𝔼 hσ h16, map_sub, 𝔼.E_E_self, sub_self]

/-- Woodford (2003), p. 330: if `s ≥ d`, then `E_{t−s} μ_t = 0` (here `E_t μ_{t+s} = 0`), so the
`E_{t−s} μ_t` term of (1.20) can be neglected. -/
theorem E_mu_zero_of_le {σ : ℝ} (hσ : σ ≠ 0) {d s : ℕ} (hds : d ≤ s) {Y g lam : ℕ → Ω → ℝ}
    (h16 : Eq16 𝔼 σ d Y g lam) (t : ℕ) : 𝔼.E t (mu σ lam g Y (t + s)) = 0 := by
  have hts : t + s = (t + (s - d)) + d := by omega
  rw [hts, ← 𝔼.tower (Nat.le_add_right t (s - d)), E_mu_zero 𝔼 hσ h16, map_zero]

/-- Woodford (2003), p. 330 ("whereas `μ_t` need not equal zero"): with the coin-flip tree,
`d = 1`, `σ = 1`, `g = 0`, `λ̂` the date-1 coin shock and `Ŷ_{t+1} = −E_t λ̂_{t+1}`, (1.6)
holds but `E_1 μ_1 = μ_1 = ±1`; so for `s = 0 < d` the term `E_{t−s} μ_t` of (1.20) is not
zero. -/
theorem mu_term_nonzero_of_lt :
    Eq16 ExpectationsFiniteTree.coinSystem 1 1
        (fun s => -ExpectationsFiniteTree.coinSystem.E (s - 1)
          (ExpectationsFiniteTree.coinAR1 0 s))
        0 (ExpectationsFiniteTree.coinAR1 0) ∧
      ExpectationsFiniteTree.coinSystem.E 1 (mu 1 (ExpectationsFiniteTree.coinAR1 0) 0
        (fun s => -ExpectationsFiniteTree.coinSystem.E (s - 1)
          (ExpectationsFiniteTree.coinAR1 0 s)) 1) (true, true) = 1 := by
  set C := ExpectationsFiniteTree.coinSystem
  set lam := ExpectationsFiniteTree.coinAR1 0
  have hAR := ExpectationsFiniteTree.coinAR1_isAR1 0
  have hnd := ExpectationsFiniteTree.coinAR1_nondegenerate 0
  refine ⟨fun t => ?_, ?_⟩
  · simp only [Nat.add_sub_cancel, Pi.zero_apply, one_smul, zero_sub]
  · have hmu : mu 1 lam 0 (fun s => -C.E (s - 1) (lam s)) 1 = lam 1 := by
      unfold mu
      simp only [inv_one, one_smul, Pi.zero_apply, zero_sub, neg_neg, Nat.sub_self]
      rw [hnd.2.2, sub_zero]
    rw [hmu, hAR.1 1]
    exact hnd.1

/-- Woodford (2003), eq. (1.21), p. 330 (**`μ_t` in terms of observables**): along a solution of
the bond-pricing relation (`λ̂` adapted) and of (1.6),
`μ_t = ∑_{j<d} E_t(î_{t+j} − π_{t+j+1}) + σ⁻¹[(Ŷ_t − g_t) − E_t(Ŷ_{t+d} − g_{t+d})]`. -/
theorem mu_observables {σ : ℝ} (hσ : σ ≠ 0) {d : ℕ} {Y g i infl lam : ℕ → Ω → ℝ}
    (hla : 𝔼.Adapted lam) (hlam : LamEq 𝔼 i infl lam) (h16 : Eq16 𝔼 σ d Y g lam) (t : ℕ) :
    mu σ lam g Y t = ∑ j ∈ Finset.range d, 𝔼.E t (i (t + j) - infl (t + j + 1)) +
      σ⁻¹ • ((Y t - g t) - 𝔼.E t (Y (t + d) - g (t + d))) := by
  have hit := lam_iterate 𝔼 hlam (le_refl t) d
  rw [hla t] at hit
  have hE : 𝔼.E t (Y (t + d) - g (t + d)) = -σ • 𝔼.E t (lam (t + d)) := by
    rw [h16 t]
    simp only [map_sub, map_smul, 𝔼.E_E_self]
    module
  unfold mu
  rw [hE, hit]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  field_simp
  ring

/-- Woodford (2003), p. 332 (**the information-delay interpretation removes `μ`**): if labour
supply, like spending, responds to the date-`t` estimate `E_t λ̂_{t+d}` (so real marginal cost is
`ω(ŷ(i) − Ŷⁿ) + σ⁻¹(g − Ŷⁿ) − E_t λ̂`), then under (1.6) marginal cost is exactly the Chapter 3
function `ω(ŷ(i) − Ŷⁿ) + σ⁻¹(Ŷ − Ŷⁿ)`, i.e. (1.18) without the `μ_t` term. -/
theorem mc_info_delay {σ : ℝ} (hσ : σ ≠ 0) {d : ℕ} {Y g lam : ℕ → Ω → ℝ}
    (h16 : Eq16 𝔼 σ d Y g lam) (ω : ℝ) (yi Yn : Ω → ℝ) (t : ℕ) :
    ω • (yi - Yn) + σ⁻¹ • (g (t + d) - Yn) - 𝔼.E t (lam (t + d)) =
      ω • (yi - Yn) + σ⁻¹ • (Y (t + d) - Yn) := by
  rw [h16 t]
  funext o
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-! ### (1.20): Calvo pricing with an `s`-period implementation lag -/

omit 𝔼 in
/-- Woodford (2003), Ch. 3, eq. (2.7)–(2.12) (the log-linear Calvo first-order condition in
recursive form, restated as a hypothesis): with `q_t` the full-information optimal reset price
relative to `P_{t−1}` and `c_t = ŝ_t/(1 + ωθ)` the strategic-complementarity-weighted average
real marginal cost, `q_t = π_t + (1 − αβ) c_t + αβ E_t q_{t+1}`. -/
def CalvoRec (𝔼 : ExpectationSystem Ω) (α β : ℝ) (q infl c : ℕ → Ω → ℝ) : Prop :=
  ∀ t, q t = infl t + (1 - α * β) • c t + (α * β) • 𝔼.E t (q (t + 1))

omit 𝔼 in
/-- Woodford (2003), p. 330 (the Calvo price index with an `s`-period implementation lag): the
fraction `1 − α` of prices revised for date `t + s` are set at `t` to the date-`t` forecast of the
optimal reset price, `π_{t+s} = (1 − α) E_t q_{t+s}` (log-linear index law, `P_{t+s−1}` known at
`t`). -/
def IndexLawLag (𝔼 : ExpectationSystem Ω) (α : ℝ) (s : ℕ) (q infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl (t + s) = (1 - α) • 𝔼.E t (q (t + s))

omit 𝔼 in
/-- Woodford (2003), Ch. 3, eq. (2.12): the slope `ξ = (1 − α)(1 − αβ)/α`. -/
noncomputable def calvoXi (α β : ℝ) : ℝ := (1 - α) * (1 - α * β) / α

/-- Woodford (2003), p. 330 (the Calvo model with an `s`-period lag, derived): the recursive
first-order condition and the lagged index law give
`π_{t+s} = ξ E_t c_{t+s} + β E_t π_{t+s+1}`. -/
theorem delayed_calvo {α β : ℝ} (hα : α ≠ 0) {s : ℕ} {q infl c : ℕ → Ω → ℝ}
    (hrec : CalvoRec 𝔼 α β q infl c) (hidx : IndexLawLag 𝔼 α s q infl) (t : ℕ) :
    infl (t + s) = calvoXi α β • 𝔼.E t (c (t + s)) + β • 𝔼.E t (infl (t + s + 1)) := by
  have ha := hidx t
  have hknown : 𝔼.E t (infl (t + s)) = infl (t + s) := by
    rw [ha, map_smul, 𝔼.E_E_self]
  have hb := congrArg (𝔼.E t) (hrec (t + s))
  simp only [map_add, map_smul, 𝔼.tower (Nat.le_add_right t s), hknown] at hb
  have hc := congrArg (𝔼.E t) (hidx (t + 1))
  rw [map_smul, 𝔼.tower (Nat.le_succ t), show t + 1 + s = t + s + 1 by omega] at hc
  funext ω
  have ea := congrFun ha ω
  have eb := congrFun hb ω
  have ec := congrFun hc ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ea eb ec ⊢
  unfold calvoXi
  have key : α * infl (t + s) ω = (1 - α) * (1 - α * β) * 𝔼.E t (c (t + s)) ω +
      α * β * 𝔼.E t (infl (t + s + 1)) ω := by
    linear_combination ea + (1 - α) * eb - α * β * ec
  have hξ : α * ((1 - α) * (1 - α * β) / α) = (1 - α) * (1 - α * β) :=
    mul_div_cancel₀ _ hα
  apply mul_left_cancel₀ hα
  linear_combination key - 𝔼.E t (c (t + s)) ω * hξ

/-- Woodford (2003), eq. (1.20), p. 330 (**the AS relation with an `s`-period price lag and
predetermined expenditure**): with average real marginal cost `ŝ = ω_mc x − μ` (`realMC_avg`)
entering the Calvo condition as `c = ŝ/(1 + ωθ)`,
`π_{t+s} = κ E_t x_{t+s} − (κ/ω_mc) E_t μ_{t+s} + β E_t π_{t+s+1}` with `κ = ξ ω_mc/(1 + ωθ)`. -/
theorem eq120 {α β ωmc A : ℝ} (hα : α ≠ 0) (hω : ωmc ≠ 0) (hA : A ≠ 0) {s : ℕ}
    {q infl c x m : ℕ → Ω → ℝ} (hrec : CalvoRec 𝔼 α β q infl c)
    (hidx : IndexLawLag 𝔼 α s q infl) (hc : ∀ r, c r = A⁻¹ • (ωmc • x r - m r)) (t : ℕ) :
    infl (t + s) = (calvoXi α β * (ωmc / A)) • 𝔼.E t (x (t + s)) -
      (calvoXi α β * (ωmc / A) / ωmc) • 𝔼.E t (m (t + s)) + β • 𝔼.E t (infl (t + s + 1)) := by
  rw [delayed_calvo 𝔼 hα hrec hidx t, hc, map_smul, map_sub, map_smul]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- Woodford (2003), pp. 326, 330 (**(1.9) from (1.20) when `s ≥ d`**): with an `s`-period price
lag, `s ≥ d`, and (1.6), the `μ` term vanishes and
`π_{t+s} = κ E_t x_{t+s} + β E_t π_{t+s+1}`; with `s = d` this is (1.9). -/
theorem nkpc19_of_eq120 {α β ωmc A σ : ℝ} (hα : α ≠ 0) (hω : ωmc ≠ 0)
    (hA : A ≠ 0) (hσ : σ ≠ 0) {d s : ℕ} (hds : d ≤ s) {q infl c x Y g lam : ℕ → Ω → ℝ}
    (hrec : CalvoRec 𝔼 α β q infl c) (hidx : IndexLawLag 𝔼 α s q infl)
    (hc : ∀ r, c r = A⁻¹ • (ωmc • x r - mu σ lam g Y r)) (h16 : Eq16 𝔼 σ d Y g lam) (t : ℕ) :
    infl (t + s) = (calvoXi α β * (ωmc / A)) • 𝔼.E t (x (t + s)) +
      β • 𝔼.E t (infl (t + s + 1)) := by
  rw [eq120 𝔼 hα hω hA hrec hidx hc t, E_mu_zero_of_le 𝔼 hσ hds h16, smul_zero, sub_zero]

/-! ### Restatement of Chapter 4: Proposition 4.3

The forward-system tools (`rvMul`, `FSolves`, `fwdVec_spec`, `fwd_existsUnique`) are in
`ForwardSystems`; the model (1.12)–(1.14) of Chapter 4 and Proposition 4.3 are restated from
the Woodford Chapter 4 project (`NeoWicksellianFramework.BlanchardKahn`, `BasicModel`,
`Determinacy2`); the Schur–Cohn step of Proposition 4.3 is proved directly from `tr B`,
`det B`. -/

variable (𝔼 : ExpectationSystem Ω)

omit 𝔼 in
/-- Woodford (2003), eq. (1.12), p. 246 (Chapter 4, restated): the IS relation in gap form,
`x_t = E_t x_{t+1} − σ(î_t − E_t π_{t+1} − r̂ⁿ_t)`. -/
def IS112 (𝔼 : ExpectationSystem Ω) (σ : ℝ) (x ih infl rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t = 𝔼.E t (x (t + 1)) - σ • (ih t - 𝔼.E t (infl (t + 1)) - rn t)

omit 𝔼 in
/-- Woodford (2003), eq. (1.13), p. 246 (Chapter 4, restated): the New Keynesian Phillips
curve `π_t = κ x_t + β E_t π_{t+1}`. -/
def NKPCurve (𝔼 : ExpectationSystem Ω) (β κ : ℝ) (infl x : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = κ • x t + β • 𝔼.E t (infl (t + 1))

/-- Woodford (2003), p. 246 (Chapter 4, restated): the steady-state output gap consistent with
the inflation target, `x̄ = (1 − β)π̄/κ`. -/
noncomputable def xbar (β κ πbar : ℝ) : ℝ := (1 - β) * πbar / κ

omit 𝔼 in
/-- Woodford (2003), eq. (2.6), p. 252 and (C.19), p. 677: the vector `z_t = (π_t − π̄, x_t − x̄)`
of deviations of inflation and the output gap from their steady-state values. -/
def devStack (infl x : ℕ → Ω → ℝ) (p0 x0 : ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun t => ![infl t - fun _ => p0, x t - fun _ => x0]

omit 𝔼 in
/-- Woodford (2003), eq. (C.19), p. 677: the forcing term `b (r̂ⁿ_t − ī_t + c)` of the forward
form of the model. -/
def fwdForcing (b : Fin 2 → ℝ) (rn ib : ℕ → Ω → ℝ) (c : ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun t i => b i • (rn t - ib t + fun _ => c)

/-- Woodford (2003), Ch. 4, §2.2, p. 252 and fn. 24 (determinacy of equilibrium, in the genuine
sense): for every bounded adapted path of the natural rate `r̂ⁿ` and of the policy intercept
`ī`, the model has exactly one bounded adapted equilibrium `(π, x)`. -/
def ModelDeterminate
    (Eqm : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop) : Prop :=
  ∀ rn ib : ℕ → Ω → ℝ, BoundedProc rn → BoundedProc ib → 𝔼.Adapted rn → 𝔼.Adapted ib →
    ∃! p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), BoundedProc p.1 ∧ BoundedProc p.2 ∧
      𝔼.Adapted p.1 ∧ 𝔼.Adapted p.2 ∧ Eqm rn ib p.1 p.2

omit 𝔼 in
/-- Woodford (2003), eq. (2.6), p. 252: the deviation vector of bounded processes is bounded. -/
theorem devStack_bounded {infl x : ℕ → Ω → ℝ} (h1 : BoundedProc infl) (h2 : BoundedProc x)
    (p0 x0 : ℝ) : BoundedVec (devStack infl x p0 x0) := by
  obtain ⟨M₁, hM₁⟩ := h1
  obtain ⟨M₂, hM₂⟩ := h2
  refine ⟨M₁ + M₂ + |p0| + |x0|, fun t i ω => ?_⟩
  have hp := abs_nonneg p0
  have hx := abs_nonneg x0
  have h1' := (abs_nonneg _).trans (hM₁ t ω)
  have h2' := (abs_nonneg _).trans (hM₂ t ω)
  fin_cases i
  · simp only [devStack, Fin.zero_eta, Matrix.cons_val_zero, Pi.sub_apply]
    exact (abs_sub _ _).trans (by linarith [hM₁ t ω])
  · simp only [devStack, Fin.mk_one, Matrix.cons_val_one]
    exact (abs_sub _ _).trans (by linarith [hM₂ t ω])

/-- Woodford (2003), eq. (2.6), p. 252: the deviation vector of adapted processes is adapted. -/
theorem devStack_adapted {infl x : ℕ → Ω → ℝ} (h1 : 𝔼.Adapted infl) (h2 : 𝔼.Adapted x)
    (p0 x0 : ℝ) : 𝔼.AdaptedVec (devStack infl x p0 x0) := by
  intro t i
  fin_cases i
  · simp [devStack, map_sub, h1 t, 𝔼.const]
  · simp [devStack, map_sub, h2 t, 𝔼.const]

/-- Woodford (2003), eq. (C.19), p. 677: the forcing of bounded adapted disturbances is bounded
and adapted. -/
theorem fwdForcing_bounded_adapted (b : Fin 2 → ℝ) {rn ib : ℕ → Ω → ℝ} (hrn : BoundedProc rn)
    (hib : BoundedProc ib) (harn : 𝔼.Adapted rn) (haib : 𝔼.Adapted ib) (c : ℝ) :
    BoundedVec (fwdForcing b rn ib c) ∧ 𝔼.AdaptedVec (fwdForcing b rn ib c) := by
  obtain ⟨M₁, hM₁⟩ := hrn
  obtain ⟨M₂, hM₂⟩ := hib
  refine ⟨⟨(|b 0| + |b 1|) * (M₁ + M₂ + |c|), fun t i ω => ?_⟩, fun t i => ?_⟩
  · simp only [fwdForcing, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    have hb : |b i| ≤ |b 0| + |b 1| := by
      fin_cases i <;> simp
    have he : |rn t ω - ib t ω + c| ≤ M₁ + M₂ + |c| := by
      refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans ?_) le_rfl)
      exact add_le_add (hM₁ t ω) (hM₂ t ω)
    exact mul_le_mul hb he (abs_nonneg _) (by positivity)
  · simp only [fwdForcing, map_smul, map_add, map_sub, harn t, haib t, 𝔼.const]

omit 𝔼 in
/-- Woodford (2003), (C.19), p. 677: recovering `(π, x)` from the deviation vector
`z = (π − p₀, x − x₀)`. -/
def ofDevStack (p0 x0 : ℝ) (z : ℕ → Fin 2 → Ω → ℝ) : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) :=
  (fun t => z t 0 + fun _ => p0, fun t => z t 1 + fun _ => x0)

omit 𝔼 in
/-- Woodford (2003), (C.19), p. 677: `devStack` inverts `ofDevStack`. -/
theorem devStack_ofDevStack (p0 x0 : ℝ) (z : ℕ → Fin 2 → Ω → ℝ) :
    devStack (ofDevStack p0 x0 z).1 (ofDevStack p0 x0 z).2 p0 x0 = z := by
  funext t i
  fin_cases i <;> simp [devStack, ofDevStack]

omit 𝔼 in
/-- Woodford (2003), (C.19), p. 677: `devStack` is injective. -/
theorem devStack_inj {p0 x0 : ℝ} {infl x infl' x' : ℕ → Ω → ℝ}
    (h : devStack infl x p0 x0 = devStack infl' x' p0 x0) : infl = infl' ∧ x = x' := by
  constructor
  · funext t ω
    have := congrFun (congrFun (congrFun h t) 0) ω
    simpa [devStack] using this
  · funext t ω
    have := congrFun (congrFun (congrFun h t) 1) ω
    simpa [devStack] using this

/-- Woodford (2003), (C.19), p. 677: `ofDevStack` of a bounded adapted vector is bounded and
adapted. -/
theorem ofDevStack_bounded_adapted {p0 x0 : ℝ} {z : ℕ → Fin 2 → Ω → ℝ} (hz : BoundedVec z)
    (haz : 𝔼.AdaptedVec z) :
    𝔼.Adapted (ofDevStack p0 x0 z).1 ∧ 𝔼.Adapted (ofDevStack p0 x0 z).2 ∧
      BoundedProc (ofDevStack p0 x0 z).1 ∧ BoundedProc (ofDevStack p0 x0 z).2 := by
  obtain ⟨M, hM⟩ := hz
  refine ⟨fun t => ?_, fun t => ?_, ⟨M + |p0|, fun t ω => ?_⟩, ⟨M + |x0|, fun t ω => ?_⟩⟩
  · simp [ofDevStack, map_add, haz t 0, 𝔼.const]
  · simp [ofDevStack, map_add, haz t 1, 𝔼.const]
  · simpa [ofDevStack] using (abs_add_le _ _).trans (add_le_add (hM t 0 ω) le_rfl)
  · simpa [ofDevStack] using (abs_add_le _ _).trans (add_le_add (hM t 1 ω) le_rfl)

/-- Woodford (2003), Ch. 4, §2.2, pp. 252–254, p. 314 and App. C.1 (the determinacy criterion
at the level of the model, general forcing): if the equilibrium conditions are equivalent to a
forward system `z_t = K E_t z_{t+1} + W_t(r̂ⁿ, ī)` in the deviations `z = (π − p₀, x − x₀)`,
the forcing of bounded adapted disturbances is bounded and adapted, and some bounded adapted
disturbances give zero forcing, the model is determinate iff `K` satisfies the Schur–Cohn
condition. -/
theorem modelDeterminate_iff_of_reduction [Nonempty Ω] {K : Matrix (Fin 2) (Fin 2) ℝ}
    {p0 x0 : ℝ} {Eqm : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop}
    {W : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → ℕ → Fin 2 → Ω → ℝ}
    (hred : ∀ rn ib infl x, Eqm rn ib infl x ↔ 𝔼.Solves K (W rn ib) (devStack infl x p0 x0))
    (hW : ∀ rn ib, BoundedProc rn → BoundedProc ib → 𝔼.Adapted rn → 𝔼.Adapted ib →
      BoundedVec (W rn ib) ∧ 𝔼.AdaptedVec (W rn ib))
    (hW0 : ∃ rn ib, BoundedProc rn ∧ BoundedProc ib ∧ 𝔼.Adapted rn ∧ 𝔼.Adapted ib ∧
      W rn ib = 0) :
    ModelDeterminate 𝔼 Eqm ↔ SchurStable (tr2 K) (det2 K) := by
  constructor
  · intro hdet
    by_contra hA
    obtain ⟨rn, ib, h1, h2, h3, h4, hw0⟩ := hW0
    obtain ⟨y, hy, hay, hby, hne⟩ := 𝔼.system_not_unique hA (x := 0) (w := 0)
      (fun t i => by simp) (fun t i => by simp) ⟨0, fun t i ω => by simp⟩
    obtain ⟨p, _, hpu⟩ := hdet rn ib h1 h2 h3 h4
    have hsol : ∀ z, 𝔼.Solves K 0 z → BoundedVec z → 𝔼.AdaptedVec z →
        ofDevStack p0 x0 z = p := by
      intro z hz hbz haz
      obtain ⟨a1, a2, b1, b2⟩ := ofDevStack_bounded_adapted 𝔼 (p0 := p0) (x0 := x0) hbz haz
      refine hpu _ ⟨b1, b2, a1, a2, ?_⟩
      rw [hred, devStack_ofDevStack, hw0]
      exact hz
    have e1 := hsol y hy hby hay
    have e2 := hsol 0 (fun t i => by simp) ⟨0, fun t i ω => by simp⟩ (fun t i => by simp)
    apply hne
    rw [← devStack_ofDevStack p0 x0 y, ← devStack_ofDevStack p0 x0 (0 : ℕ → Fin 2 → Ω → ℝ),
      e1, e2]
  · intro hK rn ib hrn hib harn haib
    obtain ⟨hwb, hwa⟩ := hW rn ib hrn hib harn haib
    obtain ⟨z, ⟨hz, haz, hbz⟩, hzu⟩ := fwd_existsUnique 𝔼 hK hwb hwa
    obtain ⟨a1, a2, b1, b2⟩ := ofDevStack_bounded_adapted 𝔼 (p0 := p0) (x0 := x0) hbz haz
    refine ⟨ofDevStack p0 x0 z, ⟨b1, b2, a1, a2, ?_⟩, fun q ⟨d1, d2, c1, c2, hq⟩ => ?_⟩
    · rw [hred, devStack_ofDevStack]
      exact hz
    · have := hzu (devStack q.1 q.2 p0 x0)
        ⟨(hred _ _ _ _).mp hq, devStack_adapted 𝔼 c1 c2 p0 x0, devStack_bounded d1 d2 p0 x0⟩
      rw [← this]
      obtain ⟨e1, e2⟩ := devStack_inj (devStack_ofDevStack p0 x0 (devStack q.1 q.2 p0 x0))
      exact Prod.ext e1.symm e2.symm

/-- Woodford (2003), Ch. 4, §2.2, pp. 252–254, and App. C.1 (the determinacy criterion at the
level of the model): if the equilibrium conditions are equivalent to a forward system
`z_t = K E_t z_{t+1} + b (r̂ⁿ_t − ī_t + c)` in the deviations `z = (π − p₀, x − x₀)`, the model
is determinate iff `K` satisfies the Schur–Cohn condition. -/
theorem modelDeterminate_iff [Nonempty Ω] (K : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ)
    (c p0 x0 : ℝ)
    (Eqm : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop)
    (hE : ∀ rn ib infl x, Eqm rn ib infl x ↔
      𝔼.Solves K (fwdForcing b rn ib c) (devStack infl x p0 x0)) :
    ModelDeterminate 𝔼 Eqm ↔ SchurStable (tr2 K) (det2 K) := by
  refine modelDeterminate_iff_of_reduction 𝔼 (W := fun rn ib => fwdForcing b rn ib c) hE
    (fun rn ib hrn hib harn haib => fwdForcing_bounded_adapted 𝔼 b hrn hib harn haib c)
    ⟨fun _ _ => 0, fun _ _ => c, ⟨0, fun _ _ => by simp⟩, ⟨|c|, fun _ _ => le_rfl⟩,
      fun t => 𝔼.const t 0, fun t => 𝔼.const t c, ?_⟩
  funext t i ω
  simp [fwdForcing]

/-- Woodford (2003), eq. (C.19), p. 677: the forward system in the deviations, written out
date by date and state by state. -/
theorem solves_dev_iff (K : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ) (c p0 x0 : ℝ)
    (infl x rn ib : ℕ → Ω → ℝ) :
    𝔼.Solves K (fwdForcing b rn ib c) (devStack infl x p0 x0) ↔ ∀ t ω,
      (infl t ω - p0 = K 0 0 * (𝔼.E t (infl (t + 1)) ω - p0)
        + K 0 1 * (𝔼.E t (x (t + 1)) ω - x0) + b 0 * (rn t ω - ib t ω + c)) ∧
      (x t ω - x0 = K 1 0 * (𝔼.E t (infl (t + 1)) ω - p0)
        + K 1 1 * (𝔼.E t (x (t + 1)) ω - x0) + b 1 * (rn t ω - ib t ω + c)) := by
  simp only [ExpectationSystem.Solves, Fin.forall_fin_two, devStack, fwdForcing, funext_iff,
    ← forall_and]
  simp [map_sub, 𝔼.const, mul_add]

/-! ### The basic model (1.12)–(1.13) -/

/-- Woodford (2003), eq. (1.12), p. 246, state by state. -/
theorem IS_iff (σ : ℝ) (infl x i rn : ℕ → Ω → ℝ) :
    IS112 𝔼 σ x i infl rn ↔ ∀ t ω,
      x t ω = 𝔼.E t (x (t + 1)) ω - σ * (i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) := by
  simp only [IS112, funext_iff, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- Woodford (2003), eq. (1.13), p. 246, state by state. -/
theorem NKPC_iff (β κ : ℝ) (infl x : ℕ → Ω → ℝ) :
    NKPCurve 𝔼 β κ infl x ↔ ∀ t ω, infl t ω = κ * x t ω + β * 𝔼.E t (infl (t + 1)) ω := by
  simp only [NKPCurve, funext_iff, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- Woodford (2003), p. 246: `κ x̄ = (1 − β) π̄`, so `(π̄, x̄)` is a steady state of the NKPC. -/
theorem kappa_mul_xbar {β κ : ℝ} (hκ : κ ≠ 0) (πbar : ℝ) :
    κ * xbar β κ πbar = (1 - β) * πbar := by
  unfold xbar; field_simp

/-- Woodford (2003), p. 246: constant inflation `π̄` and output gap `x̄` satisfy the NKPC. -/
theorem nkpc_steady {β κ : ℝ} (hκ : κ ≠ 0) (πbar : ℝ) :
    NKPCurve 𝔼 β κ (fun _ _ => πbar) (fun _ _ => xbar β κ πbar) := by
  rw [NKPC_iff]
  intro t ω
  simp only [𝔼.const]
  linear_combination -(kappa_mul_xbar hκ πbar)

omit 𝔼 in
/-- Woodford (2003), eq. (1.14), p. 246: the Taylor rule
`î_t = ī_t + φ_π (π_t − π̄) + φ_x (x_t − x̄)/4`, as a process. -/
noncomputable def taylorRate (β κ φπ φx πbar : ℝ) (ib infl x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => ib t + φπ • (infl t - fun _ => πbar) + (φx / 4) • (x t - fun _ => xbar β κ πbar)

/-- Woodford (2003), eqs. (1.12)–(1.14), p. 246: `(π, x)` is an equilibrium under the Taylor
rule (1.14) (the interest rate is then given by the rule). -/
def TaylorEqm (β σ κ φπ φx πbar : ℝ) (rn ib infl x : ℕ → Ω → ℝ) : Prop :=
  IS112 𝔼 σ x (taylorRate β κ φπ φx πbar ib infl x) infl rn ∧ NKPCurve 𝔼 β κ infl x

/-- Woodford (2003), eqs. (1.12)–(1.14), p. 246: a triple `(π, x, î)` satisfies (1.12), (1.13)
and the rule (1.14) iff `î` is given by the rule and `(π, x)` is a `TaylorEqm`; so uniqueness
of `(π, x)` is uniqueness of the triple. -/
theorem taylor_triple_iff (β σ κ φπ φx πbar : ℝ) (rn ib infl x i : ℕ → Ω → ℝ) :
    (IS112 𝔼 σ x i infl rn ∧ NKPCurve 𝔼 β κ infl x ∧ i = taylorRate β κ φπ φx πbar ib infl x) ↔
      (i = taylorRate β κ φπ φx πbar ib infl x ∧ TaylorEqm 𝔼 β σ κ φπ φx πbar rn ib infl x) := by
  constructor
  · rintro ⟨h1, h2, rfl⟩
    exact ⟨rfl, h1, h2⟩
  · rintro ⟨rfl, h1, h2⟩
    exact ⟨h1, h2, rfl⟩

/-- Woodford (2003), App. C.2, p. 677: `Δ = 1 + σ φ_x/4 + σ κ φ_π = β det A` for the (C.19)
matrix `A`. -/
noncomputable def taylorDelta (σ κ φπ φx : ℝ) : ℝ := 1 + σ * φx / 4 + σ * κ * φπ

/-- Woodford (2003), eq. (2.18), p. 263 (the matrix `B` of the temporary-equilibrium map,
`B = A⁻¹` for the (C.19) matrix `A`): the forward form `z_t = B E_t z_{t+1} + b e_t` of the
model under the Taylor rule (1.14). -/
noncomputable def taylorB (β σ κ φπ φx : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(β + σ * κ + β * σ * φx / 4) / taylorDelta σ κ φπ φx, κ / taylorDelta σ κ φπ φx;
    σ * (1 - β * φπ) / taylorDelta σ κ φπ φx, 1 / taylorDelta σ κ φπ φx]

/-- Woodford (2003), eq. (2.18), p. 263: the forcing coefficients `b` of the forward form under
(1.14). -/
noncomputable def taylorb (σ κ φπ φx : ℝ) : Fin 2 → ℝ :=
  ![κ * σ / taylorDelta σ κ φπ φx, σ / taylorDelta σ κ φπ φx]

/-- Woodford (2003), eq. (2.18), p. 263, state by state: under the Taylor rule, the IS relation
and the NKPC are equivalent to the forward form `z = B E z′ + b (r̂ⁿ − ī + π̄)` in deviations
from `(π̄, x̄)`. The values `P`, `X` are arbitrary (rational or subjective) expectations. -/
theorem taylor_pt {β σ κ φπ φx πbar xb : ℝ} (hxb : κ * xb = (1 - β) * πbar)
    (hΔ : taylorDelta σ κ φπ φx ≠ 0) {p x P X rn ib r : ℝ}
    (hr : r = ib + φπ * (p - πbar) + φx / 4 * (x - xb)) :
    (x = X - σ * (r - P - rn) ∧ p = κ * x + β * P) ↔
      (p - πbar = taylorB β σ κ φπ φx 0 0 * (P - πbar) + taylorB β σ κ φπ φx 0 1 * (X - xb)
          + taylorb σ κ φπ φx 0 * (rn - ib + πbar) ∧
        x - xb = taylorB β σ κ φπ φx 1 0 * (P - πbar) + taylorB β σ κ φπ φx 1 1 * (X - xb)
          + taylorb σ κ φπ φx 1 * (rn - ib + πbar)) := by
  subst hr
  simp only [taylorB, taylorb, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  set Δ := taylorDelta σ κ φπ φx with hΔdef
  have hΔe : Δ = 1 + σ * φx / 4 + σ * κ * φπ := rfl
  constructor
  · rintro ⟨h1, h2⟩
    have k1 : Δ * (x - xb) = σ * (1 - β * φπ) * (P - πbar) + (X - xb)
        + σ * (rn - ib + πbar) := by
      rw [hΔe]; linear_combination h1 - σ * φπ * h2 - σ * φπ * hxb
    have k2 : Δ * (p - πbar) = (β + σ * κ + β * σ * φx / 4) * (P - πbar) + κ * (X - xb)
        + κ * σ * (rn - ib + πbar) := by
      rw [hΔe]
      linear_combination κ * h1 + (1 + σ * φx / 4) * h2 + (1 + σ * φx / 4) * hxb
    constructor
    · apply mul_left_cancel₀ hΔ
      rw [k2]
      field_simp
    · apply mul_left_cancel₀ hΔ
      rw [k1]
      field_simp
  · rintro ⟨h1, h2⟩
    have k2 : Δ * (p - πbar) = (β + σ * κ + β * σ * φx / 4) * (P - πbar) + κ * (X - xb)
        + κ * σ * (rn - ib + πbar) := by
      rw [h1]; field_simp
    have k1 : Δ * (x - xb) = σ * (1 - β * φπ) * (P - πbar) + (X - xb)
        + σ * (rn - ib + πbar) := by
      rw [h2]; field_simp
    have e : Δ * (p - κ * x - β * P) = 0 := by
      rw [hΔe] at k1 k2 ⊢
      linear_combination k2 - κ * k1 - (1 + σ * φx / 4 + σ * κ * φπ) * hxb
    have hn : p = κ * x + β * P := by
      have := (mul_eq_zero.mp e).resolve_left hΔ
      linarith
    refine ⟨?_, hn⟩
    rw [hΔe] at k1
    linear_combination k1 + σ * φπ * hn + σ * φπ * hxb

/-- Woodford (2003), eq. (2.18), p. 263 (and App. C.2): under the Taylor rule (1.14) the model
(1.12)–(1.13) is exactly the forward system `z_t = B E_t z_{t+1} + b (r̂ⁿ_t − ī_t + π̄)` in the
deviations `z = (π − π̄, x − x̄)`. -/
theorem taylorEqm_iff_solves {β σ κ φπ φx : ℝ} (hκ : κ ≠ 0) (hΔ : taylorDelta σ κ φπ φx ≠ 0)
    (πbar : ℝ) (rn ib infl x : ℕ → Ω → ℝ) :
    TaylorEqm 𝔼 β σ κ φπ φx πbar rn ib infl x ↔
      𝔼.Solves (taylorB β σ κ φπ φx) (fwdForcing (taylorb σ κ φπ φx) rn ib πbar)
        (devStack infl x πbar (xbar β κ πbar)) := by
  rw [solves_dev_iff, TaylorEqm, IS_iff, NKPC_iff, ← forall_and]
  refine forall_congr' fun t => ?_
  rw [← forall_and]
  refine forall_congr' fun ω => ?_
  exact taylor_pt (kappa_mul_xbar hκ πbar) hΔ (by simp [taylorRate])

/-- Woodford (2003), App. C.2, p. 677: `Δ ≥ 1` under the sign restrictions. -/
theorem one_le_taylorDelta {σ κ φπ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hφπ : 0 ≤ φπ)
    (hφx : 0 ≤ φx) : 1 ≤ taylorDelta σ κ φπ φx := by
  unfold taylorDelta
  have h1 : 0 ≤ σ * φx := mul_nonneg hσ.le hφx
  have h2 : 0 ≤ σ * κ * φπ := mul_nonneg (mul_nonneg hσ.le hκ.le) hφπ
  linarith

/-- Woodford (2003), App. C.2, p. 677: `Δ > 0` under the sign restrictions. -/
theorem taylorDelta_pos {σ κ φπ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hφπ : 0 ≤ φπ)
    (hφx : 0 ≤ φx) : 0 < taylorDelta σ κ φπ φx :=
  lt_of_lt_of_le one_pos (one_le_taylorDelta hσ hκ hφπ hφx)

/-! ### Proposition 4.3 -/

/-- Woodford (2003), eq. (2.7), p. 254 (Chapter 4, restated): the left-hand side
`φ_π + (1 − β) φ_x / (4κ)` of the Taylor principle. -/
noncomputable def taylorLHS (β κ φπ φx : ℝ) : ℝ := φπ + (1 - β) / (4 * κ) * φx

/-- Woodford (2003), App. C.2 (Chapter 4, restated): `tr B = (1 + β + σκ + βσφ_x/4)/Δ`. -/
theorem taylorB_tr (β σ κ φπ φx : ℝ) :
    tr2 (taylorB β σ κ φπ φx) = (1 + β + σ * κ + β * σ * φx / 4) / taylorDelta σ κ φπ φx := by
  simp only [taylorB, tr2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- Woodford (2003), App. C.2 (Chapter 4, restated): `det B = β/Δ`. -/
theorem taylorB_det {β σ κ φπ φx : ℝ} (hΔ : taylorDelta σ κ φπ φx ≠ 0) :
    det2 (taylorB β σ κ φπ φx) = β / taylorDelta σ κ φπ φx := by
  simp only [taylorB, det2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  field_simp
  unfold taylorDelta
  ring

/-- Woodford (2003), App. C.2, pp. 676–677 (the Schur–Cohn step of Proposition 4.3, proved
directly): `B` satisfies the Schur–Cohn condition iff (2.7) `φ_π + (1 − β)φ_x/(4κ) > 1`. -/
theorem taylorB_schurStable_iff {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    SchurStable (tr2 (taylorB β σ κ φπ φx)) (det2 (taylorB β σ κ φπ φx)) ↔
      1 < taylorLHS β κ φπ φx := by
  have hΔ := one_le_taylorDelta hσ hκ hφπ hφx
  have hΔ0 : 0 < taylorDelta σ κ φπ φx := by linarith
  rw [SchurStable, taylorB_tr, taylorB_det hΔ0.ne']
  have hD : |β / taylorDelta σ κ φπ φx| < 1 := by
    rw [abs_of_pos (div_pos hβ0 hΔ0), div_lt_one hΔ0]
    linarith
  have hTpos : 0 < (1 + β + σ * κ + β * σ * φx / 4) / taylorDelta σ κ φπ φx := by
    apply div_pos _ hΔ0
    have : 0 ≤ β * σ * φx / 4 := by positivity
    have : 0 < σ * κ := mul_pos hσ hκ
    linarith
  rw [abs_of_pos hTpos, div_lt_iff₀ hΔ0, add_mul, one_mul, div_mul_cancel₀ _ hΔ0.ne']
  unfold taylorDelta taylorLHS
  constructor
  · rintro ⟨-, h⟩
    have h1 : 0 < σ * (κ * (φπ - 1) + (1 - β) * φx / 4) := by nlinarith
    have h2 : 0 < κ * (φπ - 1) + (1 - β) * φx / 4 := (pos_iff_pos_of_mul_pos h1).mp hσ
    have h3 : (1 - β) / (4 * κ) * φx = ((1 - β) * φx / 4) / κ := by field_simp
    rw [h3]
    have : 1 - φπ < ((1 - β) * φx / 4) / κ := by
      rw [lt_div_iff₀ hκ]; linarith
    linarith
  · intro h
    refine ⟨hD, ?_⟩
    have h3 : (1 - β) / (4 * κ) * φx = ((1 - β) * φx / 4) / κ := by field_simp
    rw [h3] at h
    have h4 : κ * (1 - φπ) < (1 - β) * φx / 4 := by
      have : 1 - φπ < ((1 - β) * φx / 4) / κ := by linarith
      rwa [lt_div_iff₀ hκ, mul_comm] at this
    nlinarith

/-- **Proposition 4.3** (Woodford (2003), p. 254, proof App. C.2, pp. 676–677; restated from the
Chapter 4 project): under the Taylor rule (1.14) of Chapter 4 with `φ_π, φ_x ≥ 0`, equilibrium
is determinate — for every bounded adapted `r̂ⁿ` and `ī` there is exactly one bounded adapted
equilibrium `(π, x)` — iff (2.7) `φ_π + (1 − β) φ_x / (4κ) > 1`. -/
theorem prop_4_3 [Nonempty Ω] {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (πbar : ℝ) :
    ModelDeterminate 𝔼 (TaylorEqm 𝔼 β σ κ φπ φx πbar) ↔ 1 < taylorLHS β κ φπ φx := by
  have hΔ := one_le_taylorDelta hσ hκ hφπ hφx
  rw [modelDeterminate_iff 𝔼 (taylorB β σ κ φπ φx) (taylorb σ κ φπ φx) πbar πbar
    (xbar β κ πbar) _ (fun rn ib infl x =>
      taylorEqm_iff_solves 𝔼 hκ.ne' (by linarith) πbar rn ib infl x)]
  exact taylorB_schurStable_iff hβ0 hβ1 hσ hκ hφπ hφx

/-! ### The delayed model (1.9), (1.10), (1.11), (1.13): reduction to Chapter 4 -/

omit 𝔼 in
/-- Woodford (2003), p. 328: the `d`-period-ahead forecast process `t ↦ E_t y_{t+d}` (the
"component of `y` forecastable `d` periods in advance", dated by the forecast date). -/
def fc (𝔼 : ExpectationSystem Ω) (d : ℕ) (y : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => 𝔼.E t (y (t + d))

/-- Woodford (2003), p. 328: forecasts are adapted. -/
theorem fc_adapted (d : ℕ) (y : ℕ → Ω → ℝ) : 𝔼.Adapted (fc 𝔼 d y) := fun t => 𝔼.E_E_self t _

/-- Woodford (2003), p. 328: forecasts of a bounded process are bounded. -/
theorem fc_bounded {d : ℕ} {y : ℕ → Ω → ℝ} (hy : BoundedProc y) : BoundedProc (fc 𝔼 d y) := by
  obtain ⟨M, hM⟩ := hy
  exact ⟨M, fun t ω => 𝔼.abs_E_le (hM (t + d)) t ω⟩

omit 𝔼 in
/-- Woodford (2003), eq. (1.13), p. 328, at date `t + d`, **with the `/4` of (1.14) restored**
(survey error 7): `î_{t+d} = ī_{t+d} + E_t[φ_π(π_{t+d} − π̄) + (φ_x/4)(x_{t+d} − x̄)]`. The
printed (1.13) has `φ_x` in place of `φ_x/4`, which is this rule with coefficient `4φ_x`
(`rule113_printed_iff`). -/
def Rule113 (𝔼 : ExpectationSystem Ω) (β κ φπ φx πbar : ℝ) (d : ℕ) (ib infl x i : ℕ → Ω → ℝ) :
    Prop :=
  ∀ t, i (t + d) = ib (t + d) + 𝔼.E t (φπ • (infl (t + d) - fun _ => πbar) +
    (φx / 4) • (x (t + d) - fun _ => xbar β κ πbar))

omit 𝔼 in
/-- Woodford (2003), pp. 326–328: an equilibrium of the delayed model — the delayed AS relation
(1.9), the forecastable IS relation (1.10), the gap decomposition (1.11) and the Taylor rule
(1.13) — at all dates `t + d`. -/
def DelayedEqm (𝔼 : ExpectationSystem Ω) (β σ κ φπ φx πbar : ℝ) (d : ℕ)
    (rn ib u infl x i : ℕ → Ω → ℝ) : Prop :=
  NKPC19 𝔼 κ β d infl x ∧ IS110 𝔼 σ d x i infl rn ∧ Gap111 𝔼 d x u ∧
    Rule113 𝔼 β κ φπ φx πbar d ib infl x i

/-- Woodford (2003), p. 328 (**the reduction**): along an equilibrium of the delayed model, the
forecastable components `E_t π_{t+d}`, `E_t x_{t+d}` satisfy the Chapter 4 system (1.12)–(1.14)
with natural rate `E_t r̂ⁿ_{t+d}` and intercept `E_t ī_{t+d}`. -/
theorem delayed_reduce {β σ κ φπ φx πbar : ℝ} {d : ℕ} {rn ib u infl x i : ℕ → Ω → ℝ}
    (h : DelayedEqm 𝔼 β σ κ φπ φx πbar d rn ib u infl x i) :
    TaylorEqm 𝔼 β σ κ φπ φx πbar (fc 𝔼 d rn) (fc 𝔼 d ib) (fc 𝔼 d infl) (fc 𝔼 d x) := by
  obtain ⟨h9, h10, -, h13⟩ := h
  have hP1 : ∀ t, 𝔼.E t (fc 𝔼 d infl (t + 1)) = 𝔼.E t (infl (t + d + 1)) := by
    intro t
    simp only [fc]
    rw [𝔼.tower (Nat.le_succ t), show t + 1 + d = t + d + 1 by omega]
  have hX1 : ∀ t, 𝔼.E t (fc 𝔼 d x (t + 1)) = 𝔼.E t (x (t + d + 1)) := by
    intro t
    simp only [fc]
    rw [𝔼.tower (Nat.le_succ t), show t + 1 + d = t + d + 1 by omega]
  constructor
  · intro t
    rw [hP1, hX1]
    funext ω
    have e10 := congrFun (h10 t) ω
    have eI := congrFun (congrArg (𝔼.E t) (h13 t)) ω
    simp only [taylorRate, fc, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add,
      map_sub, map_smul, 𝔼.E_E_self, 𝔼.const] at e10 eI ⊢
    rw [eI] at e10
    linarith
  · intro t
    rw [hP1]
    have := congrArg (𝔼.E t) (h9 t)
    simp only [map_add, map_smul, 𝔼.E_E_self] at this
    exact this

/-- Woodford (2003), p. 328 (**the lift**, the converse of the reduction): if `(P, X)` is an
adapted solution of the Chapter 4 system with natural rate `E_t r̂ⁿ_{t+d}` and intercept
`E_t ī_{t+d}`, then `π_{t+d} = P_t`, `x_{t+d} = X_t + (u_{t+d} − E_t u_{t+d})` and
`î_{t+d} = ī_{t+d} + φ_π(P_t − π̄) + (φ_x/4)(X_t − x̄)` form an equilibrium of the delayed
model. -/
theorem delayed_lift {β σ κ φπ φx πbar : ℝ} {d : ℕ} {rn ib u infl x i P X : ℕ → Ω → ℝ}
    (hP : 𝔼.Adapted P) (hX : 𝔼.Adapted X)
    (hT : TaylorEqm 𝔼 β σ κ φπ φx πbar (fc 𝔼 d rn) (fc 𝔼 d ib) P X)
    (hinfl : ∀ t, infl (t + d) = P t)
    (hx : ∀ t, x (t + d) = X t + (u (t + d) - 𝔼.E t (u (t + d))))
    (hi : ∀ t, i (t + d) = ib (t + d) + (φπ • (P t - fun _ => πbar) +
      (φx / 4) • (X t - fun _ => xbar β κ πbar))) :
    DelayedEqm 𝔼 β σ κ φπ φx πbar d rn ib u infl x i := by
  have hEx : ∀ t, 𝔼.E t (x (t + d)) = X t := by
    intro t
    rw [hx t, map_add, map_sub, 𝔼.E_E_self, hX t, sub_self, add_zero]
  have hEx1 : ∀ t, 𝔼.E t (x (t + d + 1)) = 𝔼.E t (X (t + 1)) := by
    intro t
    rw [show t + d + 1 = t + 1 + d by omega, ← 𝔼.tower (Nat.le_succ t), hEx (t + 1)]
  have hEp1 : ∀ t, 𝔼.E t (infl (t + d + 1)) = 𝔼.E t (P (t + 1)) := by
    intro t
    rw [show t + d + 1 = t + 1 + d by omega, hinfl (t + 1)]
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · rw [hinfl t, hEx t, hEp1 t]
    exact hT.2 t
  · rw [hEx t, hEx1 t]
    have e := hT.1 t
    have hEi : 𝔼.E t (i (t + d)) = taylorRate β κ φπ φx πbar (fc 𝔼 d ib) P X t := by
      rw [hi t]
      simp only [taylorRate, fc, map_add, map_smul, map_sub, hP t, hX t, 𝔼.const]
      abel
    rw [map_sub, map_sub, hEi, hEp1 t]
    exact e
  · rw [hEx t, hx t]
  · rw [hi t, hinfl t, hx t]
    simp only [map_add, map_smul, map_sub, hP t, hX t, 𝔼.const, 𝔼.E_E_self, sub_self,
      add_zero]

omit 𝔼 in
/-- Woodford (2003), p. 328 (tool): the process equal to `y_{s−d}` at dates `s ≥ d` and to the
initial values `y⁰_s` before. -/
def shiftProc (d : ℕ) (y y0 : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun s => if d ≤ s then y (s - d) else y0 s

omit 𝔼 in
/-- Woodford (2003), p. 328 (tool): `shiftProc d y y⁰` at date `t + d` is `y_t`. -/
theorem shiftProc_add (d : ℕ) (y y0 : ℕ → Ω → ℝ) (t : ℕ) : shiftProc d y y0 (t + d) = y t := by
  simp [shiftProc]

/-- Woodford (2003), p. 328 (tool): `shiftProc d y y⁰` is adapted when `y_t` is known at `t + d`
and `y⁰` is adapted. -/
theorem shiftProc_adapted {d : ℕ} {y y0 : ℕ → Ω → ℝ} (hy : ∀ t, 𝔼.E (t + d) (y t) = y t)
    (hy0 : 𝔼.Adapted y0) : 𝔼.Adapted (shiftProc d y y0) := by
  intro s
  unfold shiftProc
  split_ifs with h
  · have := hy (s - d)
    rwa [Nat.sub_add_cancel h] at this
  · exact hy0 s

omit 𝔼 in
/-- Woodford (2003), p. 328 (tool): `shiftProc` of bounded processes is bounded. -/
theorem shiftProc_bounded {d : ℕ} {y y0 : ℕ → Ω → ℝ} (hy : BoundedProc y)
    (hy0 : BoundedProc y0) : BoundedProc (shiftProc d y y0) := by
  obtain ⟨M, hM⟩ := hy
  obtain ⟨M0, hM0⟩ := hy0
  refine ⟨max M M0, fun s ω => ?_⟩
  unfold shiftProc
  split_ifs
  · exact (hM _ ω).trans (le_max_left _ _)
  · exact (hM0 _ ω).trans (le_max_right _ _)

omit 𝔼 in
/-- Woodford (2003), p. 328 (determinacy of the delayed model, in the genuine sense): for all
bounded adapted `r̂ⁿ`, `ī` and `u = g − Ŷⁿ` there is a bounded adapted equilibrium of the delayed
model, and any two bounded adapted equilibria agree at every date `t + d` (dates before `d` are
initial conditions inherited from the past). -/
def DelayedDeterminate (𝔼 : ExpectationSystem Ω) (β σ κ φπ φx πbar : ℝ) (d : ℕ) : Prop :=
  ∀ rn ib u : ℕ → Ω → ℝ, BoundedProc rn → BoundedProc ib → BoundedProc u →
    𝔼.Adapted rn → 𝔼.Adapted ib → 𝔼.Adapted u →
    (∃ infl x i : ℕ → Ω → ℝ, BoundedProc infl ∧ BoundedProc x ∧ BoundedProc i ∧
      𝔼.Adapted infl ∧ 𝔼.Adapted x ∧ 𝔼.Adapted i ∧
      DelayedEqm 𝔼 β σ κ φπ φx πbar d rn ib u infl x i) ∧
    ∀ infl x i infl' x' i' : ℕ → Ω → ℝ, BoundedProc infl → BoundedProc x → 𝔼.Adapted infl →
      𝔼.Adapted x → BoundedProc infl' → BoundedProc x' → 𝔼.Adapted infl' → 𝔼.Adapted x' →
      DelayedEqm 𝔼 β σ κ φπ φx πbar d rn ib u infl x i →
      DelayedEqm 𝔼 β σ κ φπ φx πbar d rn ib u infl' x' i' →
      ∀ t, infl (t + d) = infl' (t + d) ∧ x (t + d) = x' (t + d) ∧ i (t + d) = i' (t + d)

/-- Woodford (2003), p. 328 (tool): along a delayed equilibrium, the date-`t + d` values are
determined by the forecastable components: `π_{t+d} = E_t π_{t+d}`,
`x_{t+d} = E_t x_{t+d} + (u_{t+d} − E_t u_{t+d})`, and `î_{t+d}` by the rule. -/
theorem delayed_eq_of_fc {β σ κ φπ φx πbar : ℝ} {d : ℕ} {rn ib u infl x i infl' x' i' :
    ℕ → Ω → ℝ} (h : DelayedEqm 𝔼 β σ κ φπ φx πbar d rn ib u infl x i)
    (h' : DelayedEqm 𝔼 β σ κ φπ φx πbar d rn ib u infl' x' i')
    (hp : fc 𝔼 d infl = fc 𝔼 d infl') (hx : fc 𝔼 d x = fc 𝔼 d x') (t : ℕ) :
    infl (t + d) = infl' (t + d) ∧ x (t + d) = x' (t + d) ∧ i (t + d) = i' (t + d) := by
  have e1 : infl (t + d) = infl' (t + d) := by
    rw [← infl_forecastable 𝔼 h.1 t, ← infl_forecastable 𝔼 h'.1 t]
    exact congrFun hp t
  have e2 : x (t + d) = x' (t + d) := by
    rw [h.2.2.1 t, h'.2.2.1 t]
    have := congrFun hx t
    simp only [fc] at this
    rw [this]
  refine ⟨e1, e2, ?_⟩
  rw [h.2.2.2 t, h'.2.2.2 t, e1, e2]

/-- Woodford (2003), p. 328 (**the determinacy transfer**): the delayed model is determinate iff
the Chapter 4 model (1.12)–(1.14) is determinate. -/
theorem delayedDeterminate_iff_model {β σ κ φπ φx πbar : ℝ} {d : ℕ} :
    DelayedDeterminate 𝔼 β σ κ φπ φx πbar d ↔
      ModelDeterminate 𝔼 (TaylorEqm 𝔼 β σ κ φπ φx πbar) := by
  have hzA : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => map_zero _
  have hzB : BoundedProc (0 : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
  have hfcShift : ∀ R : ℕ → Ω → ℝ, 𝔼.Adapted R → fc 𝔼 d (shiftProc d R 0) = R := by
    intro R hR
    funext t
    simp only [fc, shiftProc_add, hR t]
  have hknown : ∀ (R : ℕ → Ω → ℝ), 𝔼.Adapted R → ∀ t, 𝔼.E (t + d) (R t) = R t :=
    fun R hR t => ForwardSolution.E_of_known 𝔼 (Nat.le_add_right t d) (hR t)
  constructor
  · intro hD R IB hR hIB haR haIB
    obtain ⟨⟨infl, x, i, hb1, hb2, -, ha1, ha2, -, heq⟩, huniq⟩ :=
      hD (shiftProc d R 0) (shiftProc d IB 0) 0 (shiftProc_bounded hR hzB)
        (shiftProc_bounded hIB hzB) hzB (shiftProc_adapted 𝔼 (hknown R haR) hzA)
        (shiftProc_adapted 𝔼 (hknown IB haIB) hzA) hzA
    have hred := delayed_reduce 𝔼 heq
    rw [hfcShift R haR, hfcShift IB haIB] at hred
    refine ⟨(fc 𝔼 d infl, fc 𝔼 d x), ⟨fc_bounded 𝔼 hb1, fc_bounded 𝔼 hb2, fc_adapted 𝔼 d infl,
      fc_adapted 𝔼 d x, hred⟩, ?_⟩
    rintro ⟨P, X⟩ ⟨hP1, hX1, hP2, hX2, hT⟩
    -- lift `(P, X)` to the delayed model with `u = 0`
    set iq : ℕ → Ω → ℝ := shiftProc d (fun t => shiftProc d IB 0 (t + d) +
      (φπ • (P t - fun _ => πbar) + (φx / 4) • (X t - fun _ => xbar β κ πbar)))
      (shiftProc d IB 0) with hiq
    have hT' : TaylorEqm 𝔼 β σ κ φπ φx πbar (fc 𝔼 d (shiftProc d R 0))
        (fc 𝔼 d (shiftProc d IB 0)) P X := by
      rw [hfcShift R haR, hfcShift IB haIB]; exact hT
    have hlift := delayed_lift 𝔼 (u := 0) (infl := shiftProc d P 0) (x := shiftProc d X 0)
      (i := iq) hP2 hX2 hT' (fun t => shiftProc_add d P 0 t)
      (fun t => by simp [shiftProc_add]) (fun t => by rw [hiq, shiftProc_add])
    have hb3 : BoundedProc (shiftProc d P 0) := shiftProc_bounded hP1 hzB
    have hb4 : BoundedProc (shiftProc d X 0) := shiftProc_bounded hX1 hzB
    have ha3 : 𝔼.Adapted (shiftProc d P 0) := shiftProc_adapted 𝔼 (hknown P hP2) hzA
    have ha4 : 𝔼.Adapted (shiftProc d X 0) := shiftProc_adapted 𝔼 (hknown X hX2) hzA
    have hu := huniq _ _ _ _ _ _ hb3 hb4 ha3 ha4 hb1 hb2 ha1 ha2 hlift heq
    have hP : P = fc 𝔼 d infl := by
      funext t
      rw [← shiftProc_add d P 0 t, (hu t).1]
      exact (infl_forecastable 𝔼 heq.1 t).symm
    have hX : X = fc 𝔼 d x := by
      funext t
      rw [← shiftProc_add d X 0 t, (hu t).2.1, heq.2.2.1 t]
      simp [fc]
    rw [hP, hX]
  · intro hM rn ib u hrn hib hu harn haib hau
    obtain ⟨⟨P, X⟩, ⟨hP1, hX1, hP2, hX2, hT⟩, hpu⟩ :=
      hM (fc 𝔼 d rn) (fc 𝔼 d ib) (fc_bounded 𝔼 hrn) (fc_bounded 𝔼 hib) (fc_adapted 𝔼 d rn)
        (fc_adapted 𝔼 d ib)
    refine ⟨?_, ?_⟩
    · obtain ⟨Mu, hMu⟩ := hu
      obtain ⟨MX, hMX⟩ := hX1
      obtain ⟨MP, hMP⟩ := hP1
      obtain ⟨Mi, hMi⟩ := hib
      set y : ℕ → Ω → ℝ := fun t => X t + (u (t + d) - 𝔼.E t (u (t + d))) with hy
      set z : ℕ → Ω → ℝ := fun t => ib (t + d) + (φπ • (P t - fun _ => πbar) +
        (φx / 4) • (X t - fun _ => xbar β κ πbar)) with hz
      have hyk : ∀ t, 𝔼.E (t + d) (y t) = y t := by
        intro t
        simp only [hy, map_add, map_sub, hknown X hX2 t, hau (t + d),
          ForwardSolution.E_of_known 𝔼 (Nat.le_add_right t d) (𝔼.E_E_self t (u (t + d)))]
      have hzk : ∀ t, 𝔼.E (t + d) (z t) = z t := by
        intro t
        simp only [hz, map_add, map_sub, map_smul, hknown X hX2 t, hknown P hP2 t, haib (t + d),
          𝔼.const]
      have hyb : BoundedProc y := ⟨MX + (Mu + Mu), fun t ω => by
        simp only [hy, Pi.add_apply, Pi.sub_apply]
        refine (abs_add_le _ _).trans (add_le_add (hMX t ω) ((abs_sub _ _).trans
          (add_le_add (hMu _ ω) (𝔼.abs_E_le (hMu (t + d)) t ω))))⟩
      have hzb : BoundedProc z := ⟨Mi + (|φπ| * (MP + |πbar|) + |φx / 4| * (MX +
          |xbar β κ πbar|)), fun t ω => by
        simp only [hz, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        refine (abs_add_le _ _).trans (add_le_add (hMi _ ω) ((abs_add_le _ _).trans
          (add_le_add ?_ ?_)))
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hMP t ω) le_rfl))
            (abs_nonneg _)
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hMX t ω) le_rfl))
            (abs_nonneg _)⟩
      refine ⟨shiftProc d P 0, shiftProc d y 0, shiftProc d z ib,
        shiftProc_bounded ⟨MP, hMP⟩ hzB, shiftProc_bounded hyb hzB,
        shiftProc_bounded hzb ⟨Mi, hMi⟩, shiftProc_adapted 𝔼 (hknown P hP2) hzA,
        shiftProc_adapted 𝔼 hyk hzA, shiftProc_adapted 𝔼 hzk haib, ?_⟩
      exact delayed_lift 𝔼 hP2 hX2 hT (fun t => shiftProc_add d P 0 t)
        (fun t => by rw [shiftProc_add]) (fun t => by rw [shiftProc_add])
    · intro infl x i infl' x' i' hb1 hb2 ha1 ha2 hb1' hb2' ha1' ha2' h h'
      have e := hpu (fc 𝔼 d infl, fc 𝔼 d x) ⟨fc_bounded 𝔼 hb1, fc_bounded 𝔼 hb2,
        fc_adapted 𝔼 d infl, fc_adapted 𝔼 d x, delayed_reduce 𝔼 h⟩
      have e' := hpu (fc 𝔼 d infl', fc 𝔼 d x') ⟨fc_bounded 𝔼 hb1', fc_bounded 𝔼 hb2',
        fc_adapted 𝔼 d infl', fc_adapted 𝔼 d x', delayed_reduce 𝔼 h'⟩
      have e'' := e.trans e'.symm
      simp only [Prod.mk.injEq] at e''
      exact delayed_eq_of_fc 𝔼 h h' e''.1 e''.2

/-- Woodford (2003), (1.14), p. 328 (**determinacy of the delayed model iff the Taylor
principle**): with `0 < β < 1`, `σ, κ > 0`, `φ_π, φ_x ≥ 0`, the delayed model (1.9)–(1.11) with
the rule (1.13) (with `φ_x/4`) has a determinate equilibrium iff
`φ_π + (1 − β) φ_x / (4κ) > 1`. Via `delayedDeterminate_iff_model` and Proposition 4.3. -/
theorem delayed_determinate_iff [Nonempty Ω] {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hκ : 0 < κ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (πbar : ℝ) (d : ℕ) :
    DelayedDeterminate 𝔼 β σ κ φπ φx πbar d ↔ 1 < taylorLHS β κ φπ φx := by
  rw [delayedDeterminate_iff_model, prop_4_3 𝔼 hβ0 hβ1 hσ hκ hφπ hφx]

/-! ### The bounded solution (1.15)–(1.17) and intercept tracking -/

/-- Woodford (2003), Ch. 4, p. 246 (uniqueness under (2.7), from Proposition 4.3's Schur–Cohn
step): two bounded adapted equilibria of (1.12)–(1.14) with the same disturbances coincide. -/
theorem taylorEqm_unique {β σ κ φπ φx πbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (hT : 1 < taylorLHS β κ φπ φx)
    {rn ib P X P' X' : ℕ → Ω → ℝ} (h : TaylorEqm 𝔼 β σ κ φπ φx πbar rn ib P X)
    (h' : TaylorEqm 𝔼 β σ κ φπ φx πbar rn ib P' X') (hb1 : BoundedProc P)
    (hb2 : BoundedProc X) (ha1 : 𝔼.Adapted P) (ha2 : 𝔼.Adapted X) (hb1' : BoundedProc P')
    (hb2' : BoundedProc X') (ha1' : 𝔼.Adapted P') (ha2' : 𝔼.Adapted X') : P = P' ∧ X = X' := by
  have hΔ := one_le_taylorDelta hσ hκ hφπ hφx
  have hS := (taylorB_schurStable_iff hβ0 hβ1 hσ hκ hφπ hφx).mpr hT
  have e := 𝔼.system_unique hS
    ((taylorEqm_iff_solves 𝔼 hκ.ne' (by linarith) πbar rn ib P X).mp h)
    ((taylorEqm_iff_solves 𝔼 hκ.ne' (by linarith) πbar rn ib P' X').mp h')
    (devStack_adapted 𝔼 ha1 ha2 _ _) (devStack_adapted 𝔼 ha1' ha2' _ _)
    (devStack_bounded hb1 hb2 _ _) (devStack_bounded hb1' hb2' _ _)
  exact devStack_inj e

/-- Woodford (2003), p. 329 ("the forecasts `d` periods in advance of the solutions (2.31)–(2.33)
of Chapter 4"): the Chapter 4 equilibrium conditions are preserved by `d`-period-ahead
forecasting: if `(π, x)` solves (1.12)–(1.14) for `(r̂ⁿ, ī)`, then `(E_t π_{t+d}, E_t x_{t+d})`
solves them for `(E_t r̂ⁿ_{t+d}, E_t ī_{t+d})`. -/
theorem taylorEqm_fc {β σ κ φπ φx πbar : ℝ} {d : ℕ} {rn ib P X : ℕ → Ω → ℝ}
    (h : TaylorEqm 𝔼 β σ κ φπ φx πbar rn ib P X) :
    TaylorEqm 𝔼 β σ κ φπ φx πbar (fc 𝔼 d rn) (fc 𝔼 d ib) (fc 𝔼 d P) (fc 𝔼 d X) := by
  have hsh : ∀ (y : ℕ → Ω → ℝ) t, 𝔼.E t (fc 𝔼 d y (t + 1)) = 𝔼.E t (y (t + d + 1)) := by
    intro y t
    simp only [fc]
    rw [𝔼.tower (Nat.le_succ t), show t + 1 + d = t + d + 1 by omega]
  have hpre : ∀ (y : ℕ → Ω → ℝ) t, 𝔼.E t (𝔼.E (t + d) (y (t + d + 1))) =
      𝔼.E t (y (t + d + 1)) := fun y t => 𝔼.tower (Nat.le_add_right t d) _
  constructor
  · intro t
    rw [hsh P, hsh X]
    have e := congrArg (𝔼.E t) (h.1 (t + d))
    simp only [taylorRate, map_sub, map_add, map_smul, hpre, 𝔼.const] at e
    simp only [taylorRate, fc]
    exact e
  · intro t
    rw [hsh P]
    have e := congrArg (𝔼.E t) (h.2 (t + d))
    simp only [map_add, map_smul, hpre] at e
    exact e

/-- Woodford (2003), p. 329 (**the delayed solution is the `d`-period-ahead forecast of the
Chapter 4 solution**): under (1.14), if `(π⁴, x⁴)` is the bounded adapted equilibrium of the
undelayed model (1.12)–(1.14) with the same `r̂ⁿ`, `ī`, then along any bounded adapted delayed
equilibrium `π_{t+d} = E_t π⁴_{t+d}`, `E_t x_{t+d} = E_t x⁴_{t+d}` and
`x_{t+d} = E_t x⁴_{t+d} + (u_{t+d} − E_t u_{t+d})`. -/
theorem delayed_eq_forecast_ch4 {β σ κ φπ φx πbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hκ : 0 < κ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (hT : 1 < taylorLHS β κ φπ φx)
    {d : ℕ} {rn ib u infl x i P4 X4 : ℕ → Ω → ℝ}
    (h : DelayedEqm 𝔼 β σ κ φπ φx πbar d rn ib u infl x i) (hb1 : BoundedProc infl)
    (hb2 : BoundedProc x) (h4 : TaylorEqm 𝔼 β σ κ φπ φx πbar rn ib P4 X4)
    (hb3 : BoundedProc P4) (hb4 : BoundedProc X4) (t : ℕ) :
    infl (t + d) = 𝔼.E t (P4 (t + d)) ∧ 𝔼.E t (x (t + d)) = 𝔼.E t (X4 (t + d)) ∧
      x (t + d) = 𝔼.E t (X4 (t + d)) + (u (t + d) - 𝔼.E t (u (t + d))) := by
  obtain ⟨e1, e2⟩ := taylorEqm_unique 𝔼 hβ0 hβ1 hσ hκ hφπ hφx hT (delayed_reduce 𝔼 h)
    (taylorEqm_fc 𝔼 h4) (fc_bounded 𝔼 hb1) (fc_bounded 𝔼 hb2) (fc_adapted 𝔼 d infl)
    (fc_adapted 𝔼 d x) (fc_bounded 𝔼 hb3) (fc_bounded 𝔼 hb4) (fc_adapted 𝔼 d P4)
    (fc_adapted 𝔼 d X4)
  have f1 := congrFun e1 t
  have f2 := congrFun e2 t
  simp only [fc] at f1 f2
  refine ⟨?_, f2, ?_⟩
  · rw [← infl_forecastable 𝔼 h.1 t, f1]
  · rw [h.2.2.1 t, f2]

omit 𝔼 in
/-- Woodford (2003), eqs. (1.15)–(1.17), p. 328 and Ch. 4 (2.31)–(2.33): the response
coefficients `ψʲ_k = (Bᵏ b)_j` of the Chapter 4 forward solution (`j = 0` for `π`, `j = 1` for
`x`). -/
noncomputable def psiCoef (β σ κ φπ φx : ℝ) (k : ℕ) (j : Fin 2) : ℝ :=
  ∑ l, (taylorB β σ κ φπ φx ^ k) j l * taylorb σ κ φπ φx l

/-- Woodford (2003), eqs. (1.15)–(1.17), p. 328 (**the unique bounded solution**): under (1.14),
along a bounded adapted equilibrium of the delayed model, with
`F_{t,k} = E_t(r̂ⁿ_{t+d+k} − ī_{t+d+k} + π̄)` (absolutely convergent series):
`π_{t+d} = π̄ + ∑_k ψ^π_k F_{t,k}`,
`x_{t+d} = x̄ + ∑_k ψ^x_k F_{t,k} + (u_{t+d} − E_t u_{t+d})`,
`î_{t+d} = ī_{t+d} + ∑_k ψ^i_k F_{t,k}` with `ψ^i = φ_π ψ^π + (φ_x/4) ψ^x`; the coefficients are
those of Chapter 4 (`psiCoef`). -/
theorem solution_115_117 {β σ κ φπ φx πbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (hT : 1 < taylorLHS β κ φπ φx) {d : ℕ}
    {rn ib u infl x i : ℕ → Ω → ℝ} (hrn : BoundedProc rn) (hib : BoundedProc ib)
    (h : DelayedEqm 𝔼 β σ κ φπ φx πbar d rn ib u infl x i) (hb1 : BoundedProc infl)
    (hb2 : BoundedProc x) (t : ℕ) (ω : Ω) :
    HasSum (fun k => psiCoef β σ κ φπ φx k 0 *
        𝔼.E t (rn (t + d + k) - ib (t + d + k) + fun _ => πbar) ω) (infl (t + d) ω - πbar) ∧
      HasSum (fun k => psiCoef β σ κ φπ φx k 1 *
        𝔼.E t (rn (t + d + k) - ib (t + d + k) + fun _ => πbar) ω)
        (x (t + d) ω - xbar β κ πbar - (u (t + d) ω - 𝔼.E t (u (t + d)) ω)) ∧
      HasSum (fun k => (φπ * psiCoef β σ κ φπ φx k 0 + φx / 4 * psiCoef β σ κ φπ φx k 1) *
        𝔼.E t (rn (t + d + k) - ib (t + d + k) + fun _ => πbar) ω)
        (i (t + d) ω - ib (t + d) ω) := by
  have hΔ := one_le_taylorDelta hσ hκ hφπ hφx
  have hS := (taylorB_schurStable_iff hβ0 hβ1 hσ hκ hφπ hφx).mpr hT
  set B := taylorB β σ κ φπ φx with hB
  set W := fwdForcing (taylorb σ κ φπ φx) (fc 𝔼 d rn) (fc 𝔼 d ib) πbar with hW
  obtain ⟨hWb, hWa⟩ := fwdForcing_bounded_adapted 𝔼 (taylorb σ κ φπ φx) (fc_bounded 𝔼 hrn)
    (fc_bounded 𝔼 hib) (fc_adapted 𝔼 d rn) (fc_adapted 𝔼 d ib) πbar
  obtain ⟨Cb, ρ, hρ0, hρ1, hKb⟩ := pow_geom_bound hS
  obtain ⟨Mw, hMw⟩ := hWb
  obtain ⟨hs, has, hbs⟩ := fwdVec_spec 𝔼 hρ0 hρ1 hKb hMw hWa
  -- the delayed forecasts are the forward series
  have hsol := (taylorEqm_iff_solves 𝔼 hκ.ne' (by linarith) πbar _ _ _ _).mp (delayed_reduce 𝔼 h)
  have heq := 𝔼.system_unique hS hsol ((solves_iff_fsolves 𝔼 B W _).mpr hs)
    (devStack_adapted 𝔼 (fc_adapted 𝔼 d infl) (fc_adapted 𝔼 d x) _ _) has
    (devStack_bounded (fc_bounded 𝔼 hb1) (fc_bounded 𝔼 hb2) _ _) hbs
  -- the terms of the forward series
  have hterm : ∀ k (r : Fin 2), rvMul (B ^ k) (fun j => 𝔼.E t (W (t + k) j)) r ω =
      psiCoef β σ κ φπ φx k r * 𝔼.E t (rn (t + d + k) - ib (t + d + k) + fun _ => πbar) ω := by
    intro k r
    have hEW : ∀ j, 𝔼.E t (W (t + k) j) = taylorb σ κ φπ φx j •
        𝔼.E t (rn (t + d + k) - ib (t + d + k) + fun _ => πbar) := by
      intro j
      simp only [hW, fwdForcing, fc, map_smul, map_add, map_sub,
        𝔼.tower (Nat.le_add_right t k), 𝔼.const]
      rw [show t + k + d = t + d + k by omega]
    simp only [rvMul_apply, hEW, Pi.smul_apply, smul_eq_mul, psiCoef, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsum : ∀ r : Fin 2, HasSum (fun k => psiCoef β σ κ φπ φx k r *
      𝔼.E t (rn (t + d + k) - ib (t + d + k) + fun _ => πbar) ω) (fwdVec 𝔼 B W t r ω) := by
    intro r
    have hsm : Summable fun k => rvMul (B ^ k) (fun j => 𝔼.E t (W (t + k) j)) r ω := by
      refine Summable.of_norm_bounded
        ((summable_geometric_of_lt_one hρ0 hρ1).mul_left (2 * Cb * Mw)) (fun k => ?_)
      rw [Real.norm_eq_abs]
      have := abs_rvMul_pow_le hKb k (fun j ω => 𝔼.abs_E_le (hMw (t + k) j) t ω) r ω
      calc _ ≤ ((2 : ℕ) : ℝ) * (Cb * ρ ^ k * Mw) := this
        _ = 2 * Cb * Mw * ρ ^ k := by push_cast; ring
    have h1 : HasSum (fun k => rvMul (B ^ k) (fun j => 𝔼.E t (W (t + k) j)) r ω)
        (fwdVec 𝔼 B W t r ω) := hsm.hasSum
    have hf : (fun k => rvMul (B ^ k) (fun j => 𝔼.E t (W (t + k) j)) r ω) = fun k =>
        psiCoef β σ κ φπ φx k r * 𝔼.E t (rn (t + d + k) - ib (t + d + k) + fun _ => πbar) ω :=
      funext fun k => hterm k r
    rw [hf] at h1
    exact h1
  have hv0 := congrFun (congrFun (congrFun heq t) 0) ω
  have hv1 := congrFun (congrFun (congrFun heq t) 1) ω
  simp only [devStack, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.sub_apply, fc] at hv0 hv1
  have hP : infl (t + d) ω - πbar = fwdVec 𝔼 B W t 0 ω := by
    rw [← hv0, infl_forecastable 𝔼 h.1 t]
  have hX : x (t + d) ω - xbar β κ πbar - (u (t + d) ω - 𝔼.E t (u (t + d)) ω) =
      fwdVec 𝔼 B W t 1 ω := by
    rw [← hv1]
    have := congrFun (h.2.2.1 t) ω
    simp only [Pi.add_apply, Pi.sub_apply] at this
    linarith
  refine ⟨hP ▸ hsum 0, hX ▸ hsum 1, ?_⟩
  have hI : i (t + d) ω - ib (t + d) ω =
      φπ * fwdVec 𝔼 B W t 0 ω + φx / 4 * fwdVec 𝔼 B W t 1 ω := by
    have := congrFun (h.2.2.2 t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add, map_smul,
      map_sub, 𝔼.const] at this
    rw [← hv0, ← hv1, this]
    ring
  rw [hI]
  have := ((hsum 0).mul_left φπ).add ((hsum 1).mul_left (φx / 4))
  convert this using 1
  funext k
  ring

/-- Woodford (2003), p. 329: a constant path `(π̄, x̄)` solves the Chapter 4 system for natural
rate `R` and intercept `IB` iff `IB_t = R_t + π̄` at all dates (`σ, κ ≠ 0`). -/
theorem taylorEqm_const_iff {β σ κ φπ φx πbar : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0)
    (R IB : ℕ → Ω → ℝ) :
    TaylorEqm 𝔼 β σ κ φπ φx πbar R IB (fun _ _ => πbar) (fun _ _ => xbar β κ πbar) ↔
      ∀ t, IB t = R t + fun _ => πbar := by
  constructor
  · intro h t
    have e := h.1 t
    funext ω
    have e' := congrFun e ω
    simp only [taylorRate, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, 𝔼.const,
      sub_self, Pi.zero_apply, mul_zero, add_zero] at e'
    have : σ * (IB t ω - πbar - R t ω) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hσ
    simp only [Pi.add_apply]
    linarith
  · intro h
    refine ⟨fun t => ?_, nkpc_steady 𝔼 hκ πbar⟩
    funext ω
    have e := congrFun (h t) ω
    simp only [Pi.add_apply] at e
    simp only [taylorRate, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, 𝔼.const,
      sub_self, Pi.zero_apply, mul_zero, add_zero, e]
    ring

/-- Woodford (2003), p. 329 (**intercept tracking**, with the `+ π̄` the text omits — survey
error 9): under (1.14), if the intercept tracks the forecastable natural rate,
`E_t ī_{t+d} = E_t r̂ⁿ_{t+d} + π̄`, then every bounded adapted delayed equilibrium has
`π_{t+d} = π̄` and `E_t x_{t+d} = x̄` at all dates; conversely (`σ ≠ 0`) these outcomes force the
intercept rule. -/
theorem intercept_tracking_iff {β σ κ φπ φx πbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hκ : 0 < κ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (hT : 1 < taylorLHS β κ φπ φx)
    {d : ℕ} {rn ib u infl x i : ℕ → Ω → ℝ}
    (h : DelayedEqm 𝔼 β σ κ φπ φx πbar d rn ib u infl x i) (hb1 : BoundedProc infl)
    (hb2 : BoundedProc x) :
    (∀ t, infl (t + d) = (fun _ => πbar) ∧ 𝔼.E t (x (t + d)) = fun _ => xbar β κ πbar) ↔
      ∀ t, 𝔼.E t (ib (t + d)) = 𝔼.E t (rn (t + d)) + fun _ => πbar := by
  have hred := delayed_reduce 𝔼 h
  constructor
  · intro hc
    have hP : fc 𝔼 d infl = fun _ _ => πbar := by
      funext t
      simp only [fc]
      rw [infl_forecastable 𝔼 h.1 t, (hc t).1]
    have hX : fc 𝔼 d x = fun _ _ => xbar β κ πbar := by
      funext t
      exact (hc t).2
    rw [hP, hX, taylorEqm_const_iff 𝔼 hσ.ne' hκ.ne'] at hred
    exact hred
  · intro hib t
    have hc := (taylorEqm_const_iff 𝔼 (β := β) (φπ := φπ) (φx := φx) hσ.ne' hκ.ne'
      (fc 𝔼 d rn) (fc 𝔼 d ib)).mpr hib
    obtain ⟨e1, e2⟩ := taylorEqm_unique 𝔼 hβ0 hβ1 hσ hκ hφπ hφx hT hred hc (fc_bounded 𝔼 hb1)
      (fc_bounded 𝔼 hb2) (fc_adapted 𝔼 d infl) (fc_adapted 𝔼 d x)
      ⟨|πbar|, fun _ _ => le_rfl⟩ ⟨|xbar β κ πbar|, fun _ _ => le_rfl⟩
      (fun t => 𝔼.const t πbar) (fun t => 𝔼.const t _)
    refine ⟨?_, congrFun e2 t⟩
    rw [← infl_forecastable 𝔼 h.1 t]
    exact congrFun e1 t

/-- Woodford (2003), p. 329 (**survey error 9 confirmed**): with the intercept as printed,
`ī_t = E_{t−d} r̂ⁿ_t` (no `+ π̄`), and `π̄ ≠ 0`, no delayed equilibrium has `π_{t+d} = π̄` and
`E_t x_{t+d} = x̄` at all dates. -/
theorem printed_intercept_fails [Nonempty Ω] {β σ κ φπ φx πbar : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0)
    (hπ : πbar ≠ 0) {d : ℕ} {rn ib u infl x i : ℕ → Ω → ℝ}
    (h : DelayedEqm 𝔼 β σ κ φπ φx πbar d rn ib u infl x i)
    (hib : ∀ t, 𝔼.E t (ib (t + d)) = 𝔼.E t (rn (t + d))) :
    ¬ ∀ t, infl (t + d) = (fun _ => πbar) ∧ 𝔼.E t (x (t + d)) = fun _ => xbar β κ πbar := by
  intro hc
  have hred := delayed_reduce 𝔼 h
  have hP : fc 𝔼 d infl = fun _ _ => πbar := by
    funext t
    simp only [fc]
    rw [infl_forecastable 𝔼 h.1 t, (hc t).1]
  have hX : fc 𝔼 d x = fun _ _ => xbar β κ πbar := by
    funext t
    exact (hc t).2
  rw [hP, hX, taylorEqm_const_iff 𝔼 hσ hκ] at hred
  have e := congrFun (hred 0) (Classical.arbitrary Ω)
  have e2 := congrFun (hib 0) (Classical.arbitrary Ω)
  simp only [fc, Pi.add_apply] at e e2
  rw [e2] at e
  exact hπ (by linarith)

/-- Woodford (2003), eq. (1.13), p. 328 (**survey error 7 confirmed**): the rule as printed,
`î = ī + E_{t−d}[φ_π(π − π̄) + φ_x(x − x̄)]`, is the corrected rule `Rule113` with coefficient
`4φ_x`. -/
theorem rule113_printed_iff (β κ φπ φx πbar : ℝ) (d : ℕ) (ib infl x i : ℕ → Ω → ℝ) :
    (∀ t, i (t + d) = ib (t + d) + 𝔼.E t (φπ • (infl (t + d) - fun _ => πbar) +
      φx • (x (t + d) - fun _ => xbar β κ πbar))) ↔
      Rule113 𝔼 β κ φπ (4 * φx) πbar d ib infl x i := by
  unfold Rule113
  rw [show 4 * φx / 4 = φx by ring]

/-- Woodford (2003), (1.13)–(1.14), p. 328 (survey error 7): under the rule as printed (no `/4`),
determinacy holds iff `φ_π + (1 − β) φ_x / κ > 1`, not (1.14). -/
theorem printed_rule_determinate_iff [Nonempty Ω] {β σ κ φπ φx : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (πbar : ℝ)
    (d : ℕ) :
    DelayedDeterminate 𝔼 β σ κ φπ (4 * φx) πbar d ↔ 1 < φπ + (1 - β) / κ * φx := by
  rw [delayed_determinate_iff 𝔼 hβ0 hβ1 hσ hκ hφπ (by linarith) πbar d, taylorLHS]
  have : (1 - β) / (4 * κ) * (4 * φx) = (1 - β) / κ * φx := by field_simp
  rw [this]

/-- Woodford (2003), p. 328 (survey error 7, a counterexample to "(1.14) iff determinate" for the
printed rule): with the Table 5.1 values `β = 0.99`, `κ = 0.024`, `σ = 1/0.16` and `φ_π = 0.9`,
`φ_x = 0.48` in the printed rule, equilibrium is determinate although (1.14) fails
(`0.9 + 0.01·0.48/0.096 = 0.95 < 1`). -/
theorem printed_rule_counterexample [Nonempty Ω] (πbar : ℝ) (d : ℕ) :
    DelayedDeterminate 𝔼 0.99 (1 / 0.16) 0.024 0.9 (4 * 0.48) πbar d ∧
      ¬ 1 < taylorLHS 0.99 0.024 0.9 0.48 := by
  refine ⟨(printed_rule_determinate_iff 𝔼 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) πbar d).mpr (by norm_num), ?_⟩
  unfold taylorLHS
  norm_num

/-! ### The variance decomposition (p. 329)

The claim "the forecastable and unforecastable components of the output gap are necessarily
uncorrelated" is a statement about a probability measure, which an abstract
`ExpectationSystem` does not carry. It is therefore stated in its fullest form, for Mathlib's
conditional expectation `μ[X | m]` on an arbitrary probability space with a sub-σ-algebra `m`
(date-`(t − d)` information) and square-integrable `X`; finite event trees are the special case
of a finite space with the uniform-on-cells partition σ-algebra. -/

open MeasureTheory ProbabilityTheory in
/-- Woodford (2003), p. 329: the forecastable component `E[X|m]` and the forecast error
`X − E[X|m]` are uncorrelated. -/
theorem cov_condExp_resid {Ω' : Type*} {m mΩ : MeasurableSpace Ω'} {μ : Measure Ω'}
    [IsProbabilityMeasure μ] (hm : m ≤ mΩ) {X : Ω' → ℝ} (hX : MemLp X 2 μ) :
    cov[μ[X | m], X - μ[X | m]; μ] = 0 := by
  set Y := μ[X | m] with hYdef
  have hY : MemLp Y 2 μ := hX.condExp (by norm_num)
  have hR : MemLp (X - Y) 2 μ := hX.sub hY
  have hXi : Integrable X μ := hX.integrable (by norm_num)
  have hYi : Integrable Y μ := hY.integrable (by norm_num)
  rw [covariance_eq_sub hY hR]
  have hEY : μ[Y] = μ[X] := integral_condExp hm
  have hER : μ[X - Y] = 0 := by
    rw [integral_sub' hXi hYi, hEY, sub_self]
  have hYX : μ[Y * X] = μ[Y * Y] := by
    have h1 : μ[Y * X | m] =ᵐ[μ] Y * μ[X | m] :=
      condExp_mul_of_stronglyMeasurable_left stronglyMeasurable_condExp
        (hY.integrable_mul hX) hXi
    rw [← integral_condExp hm (f := Y * X)]
    exact integral_congr_ae h1
  have hYR : μ[Y * (X - Y)] = 0 := by
    rw [mul_sub, integral_sub' (hY.integrable_mul hX) (hY.integrable_mul hY), hYX, sub_self]
  rw [hYR, hER, mul_zero, sub_zero]

open MeasureTheory ProbabilityTheory in
/-- Woodford (2003), p. 329 (**the variance decomposition**):
`var{x} = var{E_{t−d} x} + var{x − E_{t−d} x}` for square-integrable `x`. -/
theorem variance_decomposition {Ω' : Type*} {m mΩ : MeasurableSpace Ω'} {μ : Measure Ω'}
    [IsProbabilityMeasure μ] (hm : m ≤ mΩ) {X : Ω' → ℝ} (hX : MemLp X 2 μ) :
    Var[X; μ] = Var[μ[X | m]; μ] + Var[X - μ[X | m]; μ] := by
  have hY : MemLp (μ[X | m]) 2 μ := hX.condExp (by norm_num)
  have h := variance_add hY (hX.sub hY)
  rw [cov_condExp_resid hm hX, mul_zero, add_zero, add_sub_cancel] at h
  exact h

open MeasureTheory ProbabilityTheory in
/-- Woodford (2003), p. 329 (with (1.11)): if the forecast error of the gap is the exogenous
`u − E_{t−d} u` (`u = g − Ŷⁿ`), then `var{x} = var{E_{t−d} x} + var{u − E_{t−d} u}`; hence
`var{x} ≥ var{u − E_{t−d} u}`, a bound independent of policy, attained iff the forecastable
component has zero variance. -/
theorem variance_gap_bound {Ω' : Type*} {m mΩ : MeasurableSpace Ω'} {μ : Measure Ω'}
    [IsProbabilityMeasure μ] (hm : m ≤ mΩ) {X U : Ω' → ℝ} (hX : MemLp X 2 μ)
    (h111 : X - μ[X | m] =ᵐ[μ] U - μ[U | m]) :
    Var[X; μ] = Var[μ[X | m]; μ] + Var[U - μ[U | m]; μ] ∧
      Var[U - μ[U | m]; μ] ≤ Var[X; μ] ∧
      (Var[X; μ] = Var[U - μ[U | m]; μ] ↔ Var[μ[X | m]; μ] = 0) := by
  have h := variance_decomposition hm hX
  rw [variance_congr h111] at h
  have h0 := variance_nonneg (μ[X | m]) μ
  refine ⟨h, by linarith, ?_⟩
  constructor
  · intro h'; linarith
  · intro h'; rw [h, h', zero_add]

open MeasureTheory ProbabilityTheory in
/-- Woodford (2003), p. 329 ("the proposed policy achieves this"): if the forecastable component
of the gap is a.e. constant (`E_{t−d} x_t = x̄` under intercept tracking,
`intercept_tracking_iff`), the gap variance equals its policy-independent lower bound
`var{u − E_{t−d} u}`. -/
theorem variance_gap_tracking {Ω' : Type*} {m mΩ : MeasurableSpace Ω'} {μ : Measure Ω'}
    [IsProbabilityMeasure μ] (hm : m ≤ mΩ) {X U : Ω' → ℝ} (hX : MemLp X 2 μ)
    (h111 : X - μ[X | m] =ᵐ[μ] U - μ[U | m]) {xb : ℝ} (hc : μ[X | m] =ᵐ[μ] fun _ => xb) :
    Var[X; μ] = Var[U - μ[U | m]; μ] := by
  have hv : Var[μ[X | m]; μ] = 0 := by
    rw [variance_congr hc]
    have := variance_add_const (μ := μ) (X := 0) aestronglyMeasurable_const xb
    simpa using this
  exact ((variance_gap_bound hm hX h111).2.2).mpr hv

end Woodford.PolicyResponseDynamics.Predetermined
