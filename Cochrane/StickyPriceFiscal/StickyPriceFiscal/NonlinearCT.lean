/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Active and passive policy in a nonlinear continuous-time model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.4.2, eqs. (5.43)–(5.50),
pp. 140–143.

Paths are deterministic functions `ℝ → ℝ` (perfect foresight), studied on `[0, ∞)`. A flow
`db/dt = c b − f` is `Flow c f b`: `HasDerivAt b (c b τ − f τ) τ` for every `τ ≥ 0`. Present
values are improper integrals over `(0, ∞)` (`MeasureTheory.integral` on `Set.Ioi 0`) with
proved integrability.

## Main results

* (5.43)–(5.44): `flow_integrated`, `eq_544`, `eq_544_forward`; `tvc_iff_pv`, `tvc_iff_integral`
  (transversality condition iff valuation equation), `integrableOn_pv`, `real_debt_pv`.
* (5.45): `flow_gamma_iff`; `disc_bound`, `disc_bound_exp`; `gamma_pos_tvc`, `gamma_pos_pv`
  (`γ > 0` ⇒ TVC and the present value of the whole surplus); `gamma_lt_r_grows`;
  `gamma_gt_r_bounded`; survey E34: `gamma_eq_r_counterexample` (`γ = r` does not keep debt
  bounded); `gamma_zero_tvc` (`γ > 0` not necessary).
* (5.46)–(5.47): `eq_546`, `nominal_pv_547` (upper limit `∞`; survey E35:
  `printed_547_finite`), `price_level_of_valuation`, `price_level_unique_of_valuation`.
* Passive nominal rule: `nominal_passive_flow` (survey E36 sign, `printed_e36`), `odeSol`,
  `odeSol_flow`, `nominal_passive` (TVC and valuation for every price level),
  `nominal_passive_bounded`.
* (5.48)–(5.50): `vstar_flow`, `vstar_tvc_ct`, `vstar_bounded_ct`, `vstar_pv_ct`, `diff_flow`,
  `diff_grows_at_r` (exactly at `r`, survey E37), `debt_eq_vstar`, `price_level_unique`
  (`P_0 = P*_0`, needs `B_0 ≠ 0`), `price_level_B0_zero`.
-/

namespace Cochrane.StickyPriceFiscal.NonlinearCT

open Filter Topology MeasureTheory

/-- Cochrane (2023), eq. (5.43), p. 140: the flow condition `db/dt = c b − f` on `[0, ∞)`. -/
def Flow (c : ℝ) (f b : ℝ → ℝ) : Prop := ∀ τ, 0 ≤ τ → HasDerivAt b (c * b τ - f τ) τ

/-! ### Real debt: (5.43)–(5.44) -/

/-- Cochrane (2023), eq. (5.44), p. 140 (integrating forwards): for `db/dt = c b − f`,
`e^{−cT} b_{t+T} = b_t − ∫_0^T e^{−cτ} f_{t+τ} dτ`. -/
theorem flow_integrated {c : ℝ} {f b : ℝ → ℝ} (hf : ContinuousOn f (Set.Ici 0))
    (hb : Flow c f b) {t : ℝ} (ht : 0 ≤ t) {T : ℝ} (hT : 0 ≤ T) :
    Real.exp (-c * T) * b (t + T) =
      b t - ∫ τ in (0 : ℝ)..T, Real.exp (-c * τ) * f (t + τ) := by
  have hderiv : ∀ x ∈ Set.uIcc 0 T, HasDerivAt (fun τ => Real.exp (-c * τ) * b (t + τ))
      (-(Real.exp (-c * x) * f (t + x))) x := by
    intro x hx
    rw [Set.uIcc_of_le hT] at hx
    have h1 : HasDerivAt (fun τ => Real.exp (-c * τ)) (Real.exp (-c * x) * (-c)) x := by
      have := ((hasDerivAt_id x).const_mul (-c)).exp
      simpa using this
    have h2 : HasDerivAt (fun τ => b (t + τ)) (c * b (t + x) - f (t + x)) x :=
      HasDerivAt.comp_const_add t x (hb (t + x) (by linarith [hx.1]))
    convert h1.mul h2 using 1
    ring
  have hfc : ContinuousOn (fun x => f (t + x)) (Set.Icc 0 T) :=
    hf.comp (by fun_prop) (fun x hx => by simp only [Set.mem_Ici]; linarith [hx.1])
  have hcont : ContinuousOn (fun x => -(Real.exp (-c * x) * f (t + x))) (Set.uIcc 0 T) := by
    rw [Set.uIcc_of_le hT]
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      hfc).neg
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [intervalIntegral.integral_neg] at this
  simp only [mul_zero, Real.exp_zero, one_mul, add_zero] at this
  linarith

/-- Cochrane (2023), eq. (5.44), p. 140: `b_t = ∫_0^T e^{−rτ} s_{t+τ} dτ + e^{−rT} b_{t+T}`. -/
theorem eq_544 {r : ℝ} {s b : ℝ → ℝ} (hs : ContinuousOn s (Set.Ici 0)) (hb : Flow r s b)
    {t T : ℝ} (ht : 0 ≤ t) (hT : 0 ≤ T) :
    b t = (∫ τ in (0 : ℝ)..T, Real.exp (-r * τ) * s (t + τ)) + Real.exp (-r * T) * b (t + T) := by
  rw [flow_integrated hs hb ht hT]
  ring

/-- Cochrane (2023), p. 140 ("turning (5.44) around"):
`b_{t+T} = e^{rT} [b_t − ∫_0^T e^{−rτ} s_{t+τ} dτ]`: debt grows at the interest rate. -/
theorem eq_544_forward {r : ℝ} {s b : ℝ → ℝ} (hs : ContinuousOn s (Set.Ici 0))
    (hb : Flow r s b) {t T : ℝ} (ht : 0 ≤ t) (hT : 0 ≤ T) :
    b (t + T) = Real.exp (r * T) * (b t - ∫ τ in (0 : ℝ)..T, Real.exp (-r * τ) * s (t + τ)) := by
  rw [← flow_integrated hs hb ht hT, ← mul_assoc, ← Real.exp_add]
  simp

/-- Cochrane (2023), p. 140: the transversality condition `e^{−rT} b_{t+T} → 0` holds if and
only if `b_t` is the present value, `∫_0^T e^{−rτ} s_{t+τ} dτ → b_t` ("The transversality
condition is violated unless the valuation equation holds"). -/
theorem tvc_iff_pv {r : ℝ} {s b : ℝ → ℝ} (hs : ContinuousOn s (Set.Ici 0)) (hb : Flow r s b)
    {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun T => Real.exp (-r * T) * b (t + T)) atTop (𝓝 0) ↔
      Tendsto (fun T => ∫ τ in (0 : ℝ)..T, Real.exp (-r * τ) * s (t + τ)) atTop (𝓝 (b t)) := by
  have hev : (fun T => ∫ τ in (0 : ℝ)..T, Real.exp (-r * τ) * s (t + τ)) =ᶠ[atTop]
      fun T => b t - Real.exp (-r * T) * b (t + T) := by
    filter_upwards [eventually_ge_atTop 0] with T hT
    rw [flow_integrated hs hb ht hT]
    ring
  rw [tendsto_congr' hev]
  constructor
  · intro h
    simpa using (tendsto_const_nhds (x := b t)).sub h
  · intro h
    simpa using (tendsto_const_nhds (x := b t)).sub h

/-- Cochrane (2023), (5.44), p. 140: when the discounted surplus is integrable on `(0, ∞)`, the
transversality condition holds iff `b_t = ∫_0^∞ e^{−rτ} s_{t+τ} dτ`. -/
theorem tvc_iff_integral {r : ℝ} {s b : ℝ → ℝ} (hs : ContinuousOn s (Set.Ici 0))
    (hb : Flow r s b) {t : ℝ} (ht : 0 ≤ t)
    (hint : IntegrableOn (fun τ => Real.exp (-r * τ) * s (t + τ)) (Set.Ioi 0)) :
    Tendsto (fun T => Real.exp (-r * T) * b (t + T)) atTop (𝓝 0) ↔
      b t = ∫ τ in Set.Ioi 0, Real.exp (-r * τ) * s (t + τ) := by
  have hlim := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  rw [tvc_iff_pv hs hb ht]
  constructor
  · intro h
    exact tendsto_nhds_unique h hlim
  · intro h
    rw [h]
    exact hlim

/-- Cochrane (2023), §5.4.2, p. 140 (present values exist): a function continuous on `(0, ∞)`
and dominated by `C e^{−kτ}`, `k > 0`, is integrable on `(0, ∞)`. -/
theorem integrableOn_of_exp_bound {k C : ℝ} (hk : 0 < k) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioi 0)) (hbd : ∀ τ, 0 < τ → |g τ| ≤ C * Real.exp (-k * τ)) :
    IntegrableOn g (Set.Ioi 0) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hk).const_mul C)
    (hg.aestronglyMeasurable measurableSet_Ioi) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => ?_
  rw [Real.norm_eq_abs]
  exact hbd τ hτ

/-- Cochrane (2023), (5.44), p. 140: for `r > 0` and a bounded continuous surplus the discounted
surplus `e^{−rτ} s_{t+τ}` is integrable on `(0, ∞)`. -/
theorem integrableOn_pv {r M : ℝ} (hr : 0 < r) {s : ℝ → ℝ} (hs : ContinuousOn s (Set.Ici 0))
    (hM : ∀ τ, 0 ≤ τ → |s τ| ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun τ => Real.exp (-r * τ) * s (t + τ)) (Set.Ioi 0) := by
  refine integrableOn_of_exp_bound (C := M) hr ?_ fun τ hτ => ?_
  · refine (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul ?_
    exact hs.comp (by fun_prop) (fun x hx => by
      simp only [Set.mem_Ici]; linarith [(Set.mem_Ioi.mp hx)])
  · rw [abs_mul, Real.abs_exp, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _ (by linarith)) (Real.exp_pos _).le

/-- Cochrane (2023), eq. (5.44) and the present-value formula, p. 140: with `r > 0` and bounded
continuous surpluses, real debt satisfying the transversality condition is the present value
`b_t = ∫_0^∞ e^{−rτ} s_{t+τ} dτ`. -/
theorem real_debt_pv {r M : ℝ} (hr : 0 < r) {s b : ℝ → ℝ} (hs : ContinuousOn s (Set.Ici 0))
    (hM : ∀ τ, 0 ≤ τ → |s τ| ≤ M) (hb : Flow r s b) {t : ℝ} (ht : 0 ≤ t)
    (htvc : Tendsto (fun T => Real.exp (-r * T) * b (t + T)) atTop (𝓝 0)) :
    b t = ∫ τ in Set.Ioi 0, Real.exp (-r * τ) * s (t + τ) :=
  (tvc_iff_integral hs hb ht (integrableOn_pv hr hs hM ht)).mp htvc

/-! ### A surplus responding to debt: (5.45) -/

/-- Cochrane (2023), §5.4.2, p. 141: a path with a derivative at every `τ ≥ 0` is continuous on
`[0, ∞)`. -/
theorem flow_continuousOn {c : ℝ} {f b : ℝ → ℝ} (hb : Flow c f b) :
    ContinuousOn b (Set.Ici 0) :=
  fun τ hτ => (hb τ hτ).continuousAt.continuousWithinAt

/-- Cochrane (2023), eq. (5.45), p. 141: with `s_t = s_{0,t} + γ b_t` the flow (5.43) becomes
`db/dt = (r − γ) b − s_0`. -/
theorem flow_gamma_iff {r γ : ℝ} {s0 b : ℝ → ℝ} :
    Flow r (fun τ => s0 τ + γ * b τ) b ↔ Flow (r - γ) s0 b := by
  unfold Flow
  refine forall_congr' fun τ => forall_congr' fun _ => ?_
  rw [show r * b τ - (s0 τ + γ * b τ) = (r - γ) * b τ - s0 τ by ring]

/-- Cochrane (2023), p. 141: `e^{−kτ} → 0` as `τ → ∞` for `k > 0`. -/
theorem tendsto_exp_neg_mul {k : ℝ} (hk : 0 < k) :
    Tendsto (fun T => Real.exp (-k * T)) atTop (𝓝 0) := by
  have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hk)
  refine this.congr fun T => ?_
  simp [neg_mul]

/-- Cochrane (2023), p. 141: `T e^{−mT} ≤ (2/m) e^{−(m/2)T}` for `m > 0`, `T ≥ 0`. -/
theorem mul_exp_neg_le {m T : ℝ} (hm : 0 < m) :
    T * Real.exp (-m * T) ≤ 2 / m * Real.exp (-(m / 2) * T) := by
  have h1 : m / 2 * T + 1 ≤ Real.exp (m / 2 * T) := Real.add_one_le_exp _
  have h2 : Real.exp (-m * T) = Real.exp (-(m / 2) * T) * Real.exp (-(m / 2) * T) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (m / 2 * T) * Real.exp (-(m / 2) * T) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have h4 : T * Real.exp (-(m / 2) * T) ≤ 2 / m := by
    rw [le_div_iff₀ hm]
    have he := Real.exp_pos (-(m / 2) * T)
    nlinarith
  rw [h2, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le

/-- Cochrane (2023), p. 141 (the growth rate of debt): for `db/dt = (r − γ) b − s_0` with
`|s_0| ≤ M`, `|e^{−rT} b_{t+T}| ≤ e^{−γT} |b_t| + M T e^{−mT}`, `m = min(r, γ)`. -/
theorem disc_bound {r γ M : ℝ} {s0 b : ℝ → ℝ}
    (hs0 : ContinuousOn s0 (Set.Ici 0)) (hM : ∀ τ, 0 ≤ τ → |s0 τ| ≤ M) (hb : Flow (r - γ) s0 b)
    {t T : ℝ} (ht : 0 ≤ t) (hT : 0 ≤ T) :
    |Real.exp (-r * T) * b (t + T)| ≤
      Real.exp (-γ * T) * |b t| + M * T * Real.exp (-min r γ * T) := by
  have hI := flow_integrated hs0 hb ht hT
  set m := min r γ with hm
  have hsplit : Real.exp (-r * T) * b (t + T) = Real.exp (-γ * T) * b t -
      ∫ τ in (0 : ℝ)..T, Real.exp (-γ * T) * (Real.exp (-(r - γ) * τ) * s0 (t + τ)) := by
    rw [intervalIntegral.integral_const_mul, ← mul_sub, ← hI, ← mul_assoc, ← Real.exp_add,
      show -γ * T + -(r - γ) * T = -r * T by ring]
  have hbound : ‖∫ τ in (0 : ℝ)..T, Real.exp (-γ * T) * (Real.exp (-(r - γ) * τ) * s0 (t + τ))‖
      ≤ M * Real.exp (-m * T) * |T - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [Set.uIoc_of_le hT] at hx
    rw [Real.norm_eq_abs, abs_mul, abs_mul, Real.abs_exp, Real.abs_exp, ← mul_assoc,
      ← Real.exp_add, mul_comm M]
    refine mul_le_mul (Real.exp_le_exp.mpr ?_) (hM _ (by linarith [hx.1])) (abs_nonneg _)
      (Real.exp_pos _).le
    have h1 : m ≤ r := min_le_left _ _
    have h2 : m ≤ γ := min_le_right _ _
    nlinarith [mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr hx.2),
      mul_nonneg (sub_nonneg.mpr h1) hx.1.le]
  rw [hsplit, sub_zero, abs_of_nonneg hT] at *
  calc |Real.exp (-γ * T) * b t -
        ∫ τ in (0 : ℝ)..T, Real.exp (-γ * T) * (Real.exp (-(r - γ) * τ) * s0 (t + τ))|
      ≤ |Real.exp (-γ * T) * b t| +
        ‖∫ τ in (0 : ℝ)..T, Real.exp (-γ * T) * (Real.exp (-(r - γ) * τ) * s0 (t + τ))‖ :=
        abs_sub _ _
    _ ≤ Real.exp (-γ * T) * |b t| + M * Real.exp (-m * T) * T := by
        rw [abs_mul, Real.abs_exp]
        exact add_le_add le_rfl hbound
    _ = Real.exp (-γ * T) * |b t| + M * T * Real.exp (-m * T) := by ring

/-- Cochrane (2023), p. 141: under the hypotheses of `disc_bound` with `r > 0`,
`|e^{−rT} b_{t+T}| ≤ (|b_t| + 2M/m) e^{−(m/2)T}`. -/
theorem disc_bound_exp {r γ M : ℝ} (hr : 0 < r) (hγ : 0 < γ) {s0 b : ℝ → ℝ}
    (hs0 : ContinuousOn s0 (Set.Ici 0)) (hM : ∀ τ, 0 ≤ τ → |s0 τ| ≤ M) (hb : Flow (r - γ) s0 b)
    {t T : ℝ} (ht : 0 ≤ t) (hT : 0 ≤ T) :
    |Real.exp (-r * T) * b (t + T)| ≤
      (|b t| + 2 * M / min r γ) * Real.exp (-(min r γ / 2) * T) := by
  have hm : 0 < min r γ := lt_min hr hγ
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 le_rfl)
  have h1 := disc_bound hs0 hM hb ht hT
  have h2 := mul_exp_neg_le (T := T) hm
  have h3 : Real.exp (-γ * T) ≤ Real.exp (-(min r γ / 2) * T) := by
    refine Real.exp_le_exp.mpr ?_
    have : min r γ ≤ γ := min_le_right _ _
    nlinarith
  have h4 : Real.exp (-γ * T) * |b t| ≤ Real.exp (-(min r γ / 2) * T) * |b t| :=
    mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
  have h5 : M * T * Real.exp (-min r γ * T) ≤
      M * (2 / min r γ * Real.exp (-(min r γ / 2) * T)) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h2 hM0
  calc _ ≤ _ := h1
    _ ≤ Real.exp (-(min r γ / 2) * T) * |b t| +
        M * (2 / min r γ * Real.exp (-(min r γ / 2) * T)) := add_le_add h4 h5
    _ = _ := by ring

/-- Cochrane (2023), (5.45), p. 141: "If γ > 0 … the present value condition and transversality
conditions hold": with `r > 0`, `γ > 0` and bounded `s_0`, `e^{−rT} b_{t+T} → 0`. -/
theorem gamma_pos_tvc {r γ M : ℝ} (hr : 0 < r) (hγ : 0 < γ) {s0 b : ℝ → ℝ}
    (hs0 : ContinuousOn s0 (Set.Ici 0)) (hM : ∀ τ, 0 ≤ τ → |s0 τ| ≤ M)
    (hb : Flow (r - γ) s0 b) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun T => Real.exp (-r * T) * b (t + T)) atTop (𝓝 0) := by
  have hm : 0 < min r γ / 2 := by have := lt_min hr hγ; linarith
  have hg : Tendsto (fun T => (|b t| + 2 * M / min r γ) * Real.exp (-(min r γ / 2) * T)) atTop
      (𝓝 0) := by
    simpa using (tendsto_exp_neg_mul hm).const_mul (|b t| + 2 * M / min r γ)
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_ge_atTop 0] with T hT
  rw [Real.norm_eq_abs]
  exact disc_bound_exp hr hγ hs0 hM hb ht hT

/-- Cochrane (2023), (5.45) and (5.44), p. 141 ("The surpluses in the present value formula
include the γ b_t term"): with `r, γ > 0` and bounded `s_0`, debt is the present value of the
whole surplus, `b_t = ∫_0^∞ e^{−rτ} (s_{0,t+τ} + γ b_{t+τ}) dτ` (integrable). -/
theorem gamma_pos_pv {r γ M : ℝ} (hr : 0 < r) (hγ : 0 < γ) {s0 b : ℝ → ℝ}
    (hs0 : ContinuousOn s0 (Set.Ici 0)) (hM : ∀ τ, 0 ≤ τ → |s0 τ| ≤ M)
    (hb : Flow r (fun τ => s0 τ + γ * b τ) b) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun τ => Real.exp (-r * τ) * (s0 (t + τ) + γ * b (t + τ))) (Set.Ioi 0) ∧
      b t = ∫ τ in Set.Ioi 0, Real.exp (-r * τ) * (s0 (t + τ) + γ * b (t + τ)) := by
  have hb' := flow_gamma_iff.mp hb
  have hcs : ContinuousOn (fun τ => s0 τ + γ * b τ) (Set.Ici 0) :=
    hs0.add (continuousOn_const.mul (flow_continuousOn hb))
  set m := min r γ with hmdef
  have hm : 0 < m := lt_min hr hγ
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 le_rfl)
  have hint : IntegrableOn (fun τ => Real.exp (-r * τ) * (s0 (t + τ) + γ * b (t + τ)))
      (Set.Ioi 0) := by
    refine integrableOn_of_exp_bound (k := m / 2) (C := M + γ * (|b t| + 2 * M / m))
      (by linarith) ?_ fun τ hτ => ?_
    · refine (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul ?_
      exact hcs.comp (by fun_prop) (fun x hx => by
        simp only [Set.mem_Ici]; linarith [(Set.mem_Ioi.mp hx)])
    · have hτ0 : 0 ≤ τ := le_of_lt hτ
      have hd := disc_bound_exp hr hγ hs0 hM hb' ht hτ0
      have he : Real.exp (-r * τ) ≤ Real.exp (-(m / 2) * τ) := by
        refine Real.exp_le_exp.mpr ?_
        have : m ≤ r := min_le_left _ _
        nlinarith
      have hs := hM (t + τ) (by linarith)
      rw [mul_add, show Real.exp (-r * τ) * (γ * b (t + τ)) =
        γ * (Real.exp (-r * τ) * b (t + τ)) by ring]
      calc |Real.exp (-r * τ) * s0 (t + τ) + γ * (Real.exp (-r * τ) * b (t + τ))|
          ≤ |Real.exp (-r * τ) * s0 (t + τ)| + |γ * (Real.exp (-r * τ) * b (t + τ))| :=
            abs_add_le _ _
        _ ≤ Real.exp (-(m / 2) * τ) * M +
            γ * ((|b t| + 2 * M / m) * Real.exp (-(m / 2) * τ)) := by
            rw [abs_mul, abs_mul, Real.abs_exp, abs_of_pos hγ]
            refine add_le_add ?_ (mul_le_mul_of_nonneg_left hd hγ.le)
            exact mul_le_mul he hs (abs_nonneg _) (Real.exp_pos _).le
        _ = _ := by ring
  exact ⟨hint, (tvc_iff_integral hcs hb ht hint).mp (gamma_pos_tvc hr hγ hs0 hM hb' ht)⟩

/-- Cochrane (2023), p. 141 ("If 0 < γ < r, debt grows, but more slowly than the interest
rate"): with `s_0 = 0`, `b_τ = b_0 e^{(r−γ)τ}` solves (5.45), grows without bound for `b_0 > 0`,
and satisfies the transversality condition. -/
theorem gamma_lt_r_grows {r γ b0 : ℝ} (hγ : 0 < γ) (hγr : γ < r) (hb0 : 0 < b0) :
    Flow r (fun τ => 0 + γ * (b0 * Real.exp ((r - γ) * τ))) (fun τ => b0 * Real.exp ((r - γ) * τ))
      ∧ Tendsto (fun τ => b0 * Real.exp ((r - γ) * τ)) atTop atTop ∧
      Tendsto (fun T => Real.exp (-r * T) * (b0 * Real.exp ((r - γ) * (0 + T)))) atTop (𝓝 0) := by
  refine ⟨fun τ _ => ?_, ?_, ?_⟩
  · have := (((hasDerivAt_id' τ).const_mul (r - γ)).exp).const_mul b0
    convert this using 1
    ring
  · exact (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by linarith))).const_mul_atTop
      hb0
  · have h := (tendsto_exp_neg_mul hγ).const_mul b0
    rw [mul_zero] at h
    refine h.congr fun T => ?_
    rw [zero_add, ← mul_assoc, mul_comm (Real.exp _) b0, mul_assoc, ← Real.exp_add]
    ring_nf

/-- Cochrane (2023), p. 141: `∫_0^T M e^{−k(T−τ)} dτ = (M/k)(1 − e^{−kT})`. -/
theorem integral_exp_decay {k M T : ℝ} (hk : 0 < k) :
    ∫ τ in (0 : ℝ)..T, M * Real.exp (-k * (T - τ)) = M / k * (1 - Real.exp (-k * T)) := by
  have hd : ∀ x ∈ Set.uIcc 0 T, HasDerivAt (fun τ => M / k * Real.exp (-k * (T - τ)))
      (M * Real.exp (-k * (T - x))) x := by
    intro x _
    have := ((((hasDerivAt_id' x).const_sub T).const_mul (-k)).exp).const_mul (M / k)
    convert this using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun τ => M * Real.exp (-k * (T - τ))).intervalIntegrable 0 T)]
  simp only [sub_self, mul_zero, Real.exp_zero, sub_zero]
  ring

/-- Cochrane (2023), p. 141 (for `γ > r`): "the value of debt remains finite". With
`db/dt = (r − γ) b − s_0`, `|s_0| ≤ M` and `γ > r`: `|b_{t+T}| ≤ |b_t| + M/(γ − r)`. -/
theorem gamma_gt_r_bounded {r γ M : ℝ} (hγr : r < γ) {s0 b : ℝ → ℝ}
    (hs0 : ContinuousOn s0 (Set.Ici 0)) (hM : ∀ τ, 0 ≤ τ → |s0 τ| ≤ M) (hb : Flow (r - γ) s0 b)
    {t T : ℝ} (ht : 0 ≤ t) (hT : 0 ≤ T) : |b (t + T)| ≤ |b t| + M / (γ - r) := by
  set k := γ - r with hk
  have hk0 : 0 < k := by linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 le_rfl)
  have hI := flow_integrated hs0 hb ht hT
  have hsplit : b (t + T) = Real.exp (-k * T) * b t -
      ∫ τ in (0 : ℝ)..T, Real.exp (-k * T) * (Real.exp (-(r - γ) * τ) * s0 (t + τ)) := by
    rw [intervalIntegral.integral_const_mul, ← mul_sub, ← hI, ← mul_assoc, ← Real.exp_add,
      show -k * T + -(r - γ) * T = 0 by rw [hk]; ring, Real.exp_zero, one_mul]
  have hbound : ‖∫ τ in (0 : ℝ)..T, Real.exp (-k * T) * (Real.exp (-(r - γ) * τ) * s0 (t + τ))‖
      ≤ ∫ τ in (0 : ℝ)..T, M * Real.exp (-k * (T - τ)) := by
    refine intervalIntegral.norm_integral_le_of_norm_le hT (Eventually.of_forall fun x hx => ?_)
      ((by fun_prop : Continuous fun τ => M * Real.exp (-k * (T - τ))).intervalIntegrable 0 T)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, Real.abs_exp, Real.abs_exp, ← mul_assoc,
      ← Real.exp_add, mul_comm M,
      show -k * T + -(r - γ) * x = -k * (T - x) by rw [hk]; ring]
    exact mul_le_mul_of_nonneg_left (hM _ (by linarith [hx.1])) (Real.exp_pos _).le
  rw [integral_exp_decay hk0] at hbound
  rw [hsplit]
  have he : Real.exp (-k * T) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have he0 := Real.exp_pos (-k * T)
  calc |Real.exp (-k * T) * b t -
        ∫ τ in (0 : ℝ)..T, Real.exp (-k * T) * (Real.exp (-(r - γ) * τ) * s0 (t + τ))|
      ≤ |Real.exp (-k * T) * b t| +
        ‖∫ τ in (0 : ℝ)..T, Real.exp (-k * T) * (Real.exp (-(r - γ) * τ) * s0 (t + τ))‖ :=
        abs_sub _ _
    _ ≤ 1 * |b t| + M / k * 1 := by
        rw [abs_mul, Real.abs_exp]
        refine add_le_add (mul_le_mul_of_nonneg_right he (abs_nonneg _)) (hbound.trans ?_)
        exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hM0 hk0.le)
    _ = |b t| + M / k := by ring

/-- Cochrane (2023), p. 141, survey E34: "If γ ≥ r … the value of debt remains finite" is false
at `γ = r`: with `s_0 ≡ −1`, `b_τ = b_0 + τ` solves `db/dt = r b − (s_0 + r b)` and is
unbounded. -/
theorem gamma_eq_r_counterexample (r b0 : ℝ) :
    Flow r (fun τ => -1 + r * (b0 + τ)) (fun τ => b0 + τ) ∧
      ¬ ∃ M, ∀ τ, 0 ≤ τ → |b0 + τ| ≤ M := by
  refine ⟨fun τ _ => ?_, ?_⟩
  · convert (hasDerivAt_id' τ).const_add b0 using 1
    ring
  · rintro ⟨M, hM⟩
    have h := hM (|M| + |b0| + 1) (by positivity)
    have h1 := le_abs_self (b0 + (|M| + |b0| + 1))
    have h2 := neg_abs_le b0
    have h3 := le_abs_self M
    linarith

/-- Cochrane (2023), p. 141 ("The condition γ > 0 is sufficient, but not necessary"): with
`γ = 0` and the constant surplus `s = r c`, the constant debt `b = c` satisfies the
transversality condition. -/
theorem gamma_zero_tvc {r : ℝ} (hr : 0 < r) (c : ℝ) :
    Flow r (fun _ => 0 + 0 * c + r * c) (fun _ => c) ∧
      Tendsto (fun T => Real.exp (-r * T) * c) atTop (𝓝 0) := by
  refine ⟨fun τ _ => ?_, ?_⟩
  · convert hasDerivAt_const τ c using 1
    ring
  · simpa using (tendsto_exp_neg_mul hr).mul_const c

/-! ### Nominal debt: (5.46)–(5.47) -/

/-- Cochrane (2023), eq. (5.46), p. 141: for nominal debt, `d(B/P)/dt = r B/P − s` integrates to
`B_t/P_t = ∫_0^T e^{−rτ} s_{t+τ} dτ + e^{−rT} B_{t+T}/P_{t+T}`. -/
theorem eq_546 {r : ℝ} {s B P : ℝ → ℝ} (hs : ContinuousOn s (Set.Ici 0))
    (hx : Flow r s (fun τ => B τ / P τ)) {t T : ℝ} (ht : 0 ≤ t) (hT : 0 ≤ T) :
    B t / P t = (∫ τ in (0 : ℝ)..T, Real.exp (-r * τ) * s (t + τ)) +
      Real.exp (-r * T) * (B (t + T) / P (t + T)) :=
  eq_544 hs hx ht hT

/-- Cochrane (2023), eq. (5.47), p. 142 (with upper limit `∞`, survey E35): with `r > 0` and
bounded surpluses, the transversality condition gives the valuation equation
`B_t/P_t = ∫_0^∞ e^{−rτ} s_{t+τ} dτ`. -/
theorem nominal_pv_547 {r M : ℝ} (hr : 0 < r) {s B P : ℝ → ℝ}
    (hs : ContinuousOn s (Set.Ici 0)) (hM : ∀ τ, 0 ≤ τ → |s τ| ≤ M)
    (hx : Flow r s (fun τ => B τ / P τ)) {t : ℝ} (ht : 0 ≤ t)
    (htvc : Tendsto (fun T => Real.exp (-r * T) * (B (t + T) / P (t + T))) atTop (𝓝 0)) :
    B t / P t = ∫ τ in Set.Ioi 0, Real.exp (-r * τ) * s (t + τ) :=
  real_debt_pv hr hs hM hx ht htvc

/-- Cochrane (2023), eq. (5.47), p. 142, survey E35: the printed finite upper limit `T` is wrong.
With `s ≡ r c`, `c ≠ 0`, the constant `B/P ≡ c` solves the flow and the transversality
condition, but `c ≠ ∫_0^T e^{−rτ} r c dτ` for every finite `T > 0`. -/
theorem printed_547_finite {r c : ℝ} (hr : 0 < r) (hc : c ≠ 0) :
    Flow r (fun _ => r * c) (fun _ => c) ∧
      Tendsto (fun T => Real.exp (-r * T) * c) atTop (𝓝 0) ∧
      ∀ T, 0 < T → c ≠ ∫ τ in (0 : ℝ)..T, Real.exp (-r * τ) * (r * c) := by
  have hF : Flow r (fun _ => r * c) (fun _ => c) := fun τ _ => by
    convert hasDerivAt_const τ c using 1
    ring
  refine ⟨hF, by simpa using (tendsto_exp_neg_mul hr).mul_const c, fun T hT h => ?_⟩
  have h1 := eq_544 (t := 0) continuousOn_const hF le_rfl hT.le
  rw [← h] at h1
  have : Real.exp (-r * T) * c = 0 := by linarith
  exact hc ((mul_eq_zero.mp this).resolve_left (Real.exp_pos _).ne')

/-- Cochrane (2023), p. 142 ("the price level adjusts so that the valuation equation holds"):
if `B_t/P_t = V ≠ 0`, then `P_t = B_t/V`. -/
theorem price_level_of_valuation {Bt Pt V : ℝ} (hP : Pt ≠ 0) (hV : V ≠ 0) (h : Bt / Pt = V) :
    Pt = Bt / V := by
  rw [← h]
  have hB : Bt ≠ 0 := by
    intro hB
    rw [hB, zero_div] at h
    exact hV h.symm
  field_simp

/-- Cochrane (2023), p. 142: for given nominal debt `B_t ≠ 0`, two price levels satisfying the
same valuation equation coincide. -/
theorem price_level_unique_of_valuation {Bt Pt Pt' : ℝ} (hB : Bt ≠ 0) (hP : Pt ≠ 0)
    (hP' : Pt' ≠ 0) (h : Bt / Pt = Bt / Pt') : Pt = Pt' := by
  field_simp at h
  exact h.symm

/-- Cochrane (2023), p. 142 (passive policy `s_t = s_{0,t} + γ B_t/P_t`), survey E36: the
nominal flow becomes `d(B/P)/dt = (r − γ) B/P − s_0` (the book prints `s_0 + (r − γ) B/P`). -/
theorem nominal_passive_flow {r γ : ℝ} {s0 x : ℝ → ℝ} :
    Flow r (fun τ => s0 τ + γ * x τ) x ↔ Flow (r - γ) s0 x :=
  flow_gamma_iff

/-- Cochrane (2023), p. 142, survey E36: the printed `d(B/P)/dt = s_0 + (r − γ) B/P` is
compatible with the correct flow at `τ` only where `s_{0,τ} = 0`. -/
theorem printed_e36 {r γ τ : ℝ} {s0 x : ℝ → ℝ}
    (h1 : HasDerivAt x ((r - γ) * x τ - s0 τ) τ) (h2 : HasDerivAt x (s0 τ + (r - γ) * x τ) τ) :
    s0 τ = 0 := by
  have := h1.unique h2
  linarith

/-- Cochrane (2023), p. 142: the solution of `dx/dt = c x − f` with `x_0 = x0`,
`x_τ = e^{cτ} [x0 − ∫_0^τ e^{−cu} f_u du]`. -/
noncomputable def odeSol (c : ℝ) (f : ℝ → ℝ) (x0 τ : ℝ) : ℝ :=
  Real.exp (c * τ) * (x0 - ∫ u in (0 : ℝ)..τ, Real.exp (-c * u) * f u)

/-- Cochrane (2023), p. 142: `odeSol` starts at `x0`. -/
theorem odeSol_zero (c : ℝ) (f : ℝ → ℝ) (x0 : ℝ) : odeSol c f x0 0 = x0 := by
  simp [odeSol]

/-- Cochrane (2023), p. 142: `odeSol` solves `dx/dt = c x − f` for continuous `f`. -/
theorem odeSol_flow {c : ℝ} {f : ℝ → ℝ} (hf : Continuous f) (x0 : ℝ) :
    Flow c f (odeSol c f x0) := by
  intro τ _
  have hg : Continuous fun u => Real.exp (-c * u) * f u := by fun_prop
  have hI := (hg.integral_hasStrictDerivAt 0 τ).hasDerivAt
  have hE : HasDerivAt (fun τ => Real.exp (c * τ)) (Real.exp (c * τ) * (c * 1)) τ :=
    ((hasDerivAt_id' τ).const_mul c).exp
  have hP := hE.mul ((hasDerivAt_const τ x0).sub hI)
  have h1 : Real.exp (c * τ) * Real.exp (-c * τ) = 1 := by
    rw [← Real.exp_add]
    simp
  change HasDerivAt (fun τ => Real.exp (c * τ) *
    (x0 - ∫ u in (0 : ℝ)..τ, Real.exp (-c * u) * f u)) _ τ
  convert hP using 1
  unfold odeSol
  simp only [Pi.sub_apply]
  linear_combination (f τ) * h1

/-- Cochrane (2023), p. 142 ("the transversality condition and valuation equation hold for any
`P_t`"): with `s = s_0 + γ B/P`, `r, γ > 0` and bounded continuous `s_0`, for every initial real
value `x0 = B_0/P_0` (any price level) the real-debt path solving the flow satisfies the
transversality condition and the valuation equation (whole surplus discounted at `r`). -/
theorem nominal_passive {r γ M : ℝ} (hr : 0 < r) (hγ : 0 < γ) {s0 : ℝ → ℝ}
    (hs0 : Continuous s0) (hM : ∀ τ, 0 ≤ τ → |s0 τ| ≤ M) (x0 : ℝ) :
    odeSol (r - γ) s0 x0 0 = x0 ∧
      Flow r (fun τ => s0 τ + γ * odeSol (r - γ) s0 x0 τ) (odeSol (r - γ) s0 x0) ∧
      Tendsto (fun T => Real.exp (-r * T) * odeSol (r - γ) s0 x0 (0 + T)) atTop (𝓝 0) ∧
      x0 = ∫ τ in Set.Ioi 0, Real.exp (-r * τ) *
        (s0 (0 + τ) + γ * odeSol (r - γ) s0 x0 (0 + τ)) := by
  have hF := odeSol_flow (c := r - γ) hs0 x0
  have hF' := nominal_passive_flow.mpr hF
  refine ⟨odeSol_zero _ _ _, hF', gamma_pos_tvc hr hγ hs0.continuousOn hM hF le_rfl, ?_⟩
  have := (gamma_pos_pv hr hγ hs0.continuousOn hM hF' le_rfl).2
  rw [odeSol_zero] at this
  exact this

/-- Cochrane (2023), p. 142 ("If γ > r, then real debt is also bounded for any `P_t`"). -/
theorem nominal_passive_bounded {r γ M : ℝ} (hγr : r < γ) {s0 : ℝ → ℝ}
    (hs0 : Continuous s0) (hM : ∀ τ, 0 ≤ τ → |s0 τ| ≤ M) (x0 : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    |odeSol (r - γ) s0 x0 T| ≤ |x0| + M / (γ - r) := by
  have := gamma_gt_r_bounded hγr hs0.continuousOn hM (odeSol_flow (c := r - γ) hs0 x0) le_rfl hT
  rwa [zero_add, odeSol_zero] at this

/-! ### Active fiscal policy responding to a latent debt: (5.48)–(5.50) -/

/-- Cochrane (2023), eqs. (5.48)–(5.49), p. 142–143: `s = s_0 + α V*`, `dV*/dt = r V* − s`, i.e.
`dV*/dt = (r − α) V* − s_0`. -/
theorem vstar_flow {r α : ℝ} {s0 V : ℝ → ℝ} :
    Flow r (fun τ => s0 τ + α * V τ) V ↔ Flow (r - α) s0 V :=
  flow_gamma_iff

/-- Cochrane (2023), p. 143 ("If α > 0 the latent variable V* grows more slowly than the
interest rate"): `e^{−rT} V*_{t+T} → 0` for `r, α > 0` and bounded `s_0`. -/
theorem vstar_tvc_ct {r α M : ℝ} (hr : 0 < r) (hα : 0 < α) {s0 V : ℝ → ℝ}
    (hs0 : ContinuousOn s0 (Set.Ici 0)) (hM : ∀ τ, 0 ≤ τ → |s0 τ| ≤ M)
    (hV : Flow r (fun τ => s0 τ + α * V τ) V) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun T => Real.exp (-r * T) * V (t + T)) atTop (𝓝 0) :=
  gamma_pos_tvc hr hα hs0 hM (vstar_flow.mp hV) ht

/-- Cochrane (2023), p. 143 ("if α > r, V*_t is bounded"). -/
theorem vstar_bounded_ct {r α M : ℝ} (hαr : r < α) {s0 V : ℝ → ℝ}
    (hs0 : ContinuousOn s0 (Set.Ici 0)) (hM : ∀ τ, 0 ≤ τ → |s0 τ| ≤ M)
    (hV : Flow r (fun τ => s0 τ + α * V τ) V) {t T : ℝ} (ht : 0 ≤ t) (hT : 0 ≤ T) :
    |V (t + T)| ≤ |V t| + M / (α - r) :=
  gamma_gt_r_bounded hαr hs0 hM (vstar_flow.mp hV) ht hT

/-- Cochrane (2023), p. 143 ("Integrating (5.49) forward, then V*_t is the present value of
surpluses"): `V*_t = ∫_0^∞ e^{−rτ} s_{t+τ} dτ` with `s = s_0 + α V*` (integrable). -/
theorem vstar_pv_ct {r α M : ℝ} (hr : 0 < r) (hα : 0 < α) {s0 V : ℝ → ℝ}
    (hs0 : ContinuousOn s0 (Set.Ici 0)) (hM : ∀ τ, 0 ≤ τ → |s0 τ| ≤ M)
    (hV : Flow r (fun τ => s0 τ + α * V τ) V) {t : ℝ} (ht : 0 ≤ t) :
    V t = ∫ τ in Set.Ioi 0, Real.exp (-r * τ) * (s0 (t + τ) + α * V (t + τ)) :=
  (gamma_pos_pv hr hα hs0 hM hV ht).2

/-- Cochrane (2023), p. 143 (differencing (5.49) and (5.50)):
`d/dt (B/P − V*) = r (B/P − V*)`. -/
theorem diff_flow {r : ℝ} {s x V : ℝ → ℝ} (hx : Flow r s x) (hV : Flow r s V) :
    Flow r (fun _ => 0) (fun τ => x τ - V τ) := fun τ hτ => by
  convert (hx τ hτ).sub (hV τ hτ) using 1
  ring

/-- Cochrane (2023), p. 143, survey E37: the gap grows *exactly* at the interest rate,
`(B/P − V*)_{t+T} = e^{rT} (B/P − V*)_t`. -/
theorem diff_grows_at_r {r : ℝ} {z : ℝ → ℝ} (hz : Flow r (fun _ => 0) z) {t T : ℝ}
    (ht : 0 ≤ t) (hT : 0 ≤ T) : z (t + T) = Real.exp (r * T) * z t := by
  rw [eq_544_forward continuousOn_const hz ht hT]
  simp

/-- Cochrane (2023), p. 143 ("only one value of the price level is consistent with the
transversality condition"): if real debt `B/P` and the latent `V*` follow the same flow and both
satisfy the transversality condition at `t`, then `B_t/P_t = V*_t`. -/
theorem debt_eq_vstar {r : ℝ} {s x V : ℝ → ℝ} (hx : Flow r s x) (hV : Flow r s V) {t : ℝ}
    (ht : 0 ≤ t) (htx : Tendsto (fun T => Real.exp (-r * T) * x (t + T)) atTop (𝓝 0))
    (htV : Tendsto (fun T => Real.exp (-r * T) * V (t + T)) atTop (𝓝 0)) : x t = V t := by
  have hz := diff_flow hx hV
  have hev : (fun T => Real.exp (-r * T) * x (t + T) - Real.exp (-r * T) * V (t + T))
      =ᶠ[atTop] fun _ => x t - V t := by
    filter_upwards [eventually_ge_atTop 0] with T hT
    have := flow_integrated continuousOn_const hz ht hT
    simp only [mul_zero, intervalIntegral.integral_zero, sub_zero] at this
    rw [← mul_sub, this]
  have hlim := (htx.sub htV).congr' hev
  rw [sub_zero] at hlim
  exact sub_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hlim)

/-- Cochrane (2023), eqs. (5.48)–(5.50), pp. 142–143: with `r, α > 0`, bounded continuous `s_0`,
the latent `V*` (with `V*_0 = B_0/P*_0`) and real debt `B/P` following the same flow with
`s = s_0 + α V*`, the transversality condition on real debt at date 0 forces `B_t/P_t = V*_t`
for all `t ≥ 0` and `P_0 = P*_0` — provided `B_0 ≠ 0` (survey E37). -/
theorem price_level_unique {r α M : ℝ} (hr : 0 < r) (hα : 0 < α) {s0 V B P : ℝ → ℝ}
    {Ps0 : ℝ} (hs0 : ContinuousOn s0 (Set.Ici 0)) (hM : ∀ τ, 0 ≤ τ → |s0 τ| ≤ M)
    (hV : Flow r (fun τ => s0 τ + α * V τ) V)
    (hx : Flow r (fun τ => s0 τ + α * V τ) (fun τ => B τ / P τ))
    (htx : Tendsto (fun T => Real.exp (-r * T) * (B (0 + T) / P (0 + T))) atTop (𝓝 0))
    (hV0 : V 0 = B 0 / Ps0) (hB0 : B 0 ≠ 0) (hP0 : P 0 ≠ 0) (hPs0 : Ps0 ≠ 0) :
    (∀ t, 0 ≤ t → B t / P t = V t) ∧ P 0 = Ps0 := by
  have h0 : B 0 / P 0 = V 0 :=
    debt_eq_vstar hx hV le_rfl htx (vstar_tvc_ct hr hα hs0 hM hV le_rfl)
  have hz := diff_flow hx hV
  refine ⟨fun t ht => ?_, ?_⟩
  · have := diff_grows_at_r hz le_rfl ht
    simp only [zero_add, h0, sub_self, mul_zero] at this
    exact sub_eq_zero.mp this
  · rw [hV0] at h0
    exact price_level_unique_of_valuation hB0 hP0 hPs0 h0

/-- Cochrane (2023), p. 143, survey E37: without `B_0 ≠ 0` the price level is not pinned down:
with `B_0 = 0` every pair of price levels satisfies `B_0/P_0 = B_0/P*_0`. -/
theorem price_level_B0_zero {B0 : ℝ} (hB : B0 = 0) (P0 Ps0 : ℝ) : B0 / P0 = B0 / Ps0 := by
  rw [hB, zero_div, zero_div]

end Cochrane.StickyPriceFiscal.NonlinearCT
