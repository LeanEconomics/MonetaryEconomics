/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR7GuidanceItoValuation

/-!
# Forward guidance on the constructed Brownian motion

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.2.1, p. 561:
non-vacuity of the continuous-time forward-guidance results of TidyR7GuidanceItoValuation on
the Brownian motion `TidyR7BrownianExist.bmPath` (on `gaussSeq`) with its natural filtration.

## The economy

`bmSDF κ r T ι`: the nominal discount factor
`Λ_t = e^{−rt}(1 + κW_t)` for `t ≤ T` and `Λ_t = Λ_T e^{−ι(t−T)}` for `t > T`.
On `[0, T]` it solves `dΛ = −rΛ dt + κe^{−rt} dW` (Itô's product rule for `e^{−rt}·W_t`,
`TidyR7ItoProductRule.product_rule_pathwise`): the price level carries diffusive inflation risk
of size `κ` and its drift `−rΛ` is unbounded. After `T` the rate is `ι`, known at `T`.

## Main results

* `bmSDF_pre`, `bmSDF_post`, `guidanceSDF_bm`, `integrable_debt_bm`: the hypotheses of
  TidyR7GuidanceItoValuation hold (for `r ≥ 0`, `ι ≥ 0`, `ϖ > 0`, `T ≥ 0`, every `κ`).
* `integral_bmSDF_sub_sq`: `E[(Λ_T − e^{−rT})²] = e^{−2rT}κ²T`: the discount factor is
  genuinely random for `κ ≠ 0`, `T > 0`.
* `bm_guidance_jump` (**non-vacuity of `guidance_jump_ito`**): with constant surpluses `s̄`,
  the price levels `P_0 = cfgValue r i ϖ T · r/s̄` (guidance) and `P_0' = cfgValue r r ϖ T · r/s̄`
  satisfy the stochastic valuation equations, and `P_0/P_0' − 1 = cfgJump r i ϖ T`.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR7GuidanceItoBM

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.LongTermDebtDynamics.TidyR7BrownianExist
  Cochrane.LongTermDebtDynamics.TidyR7BrownianSchauder
  Cochrane.LongTermDebtDynamics.TidyR7BrownianTools
  Cochrane.LongTermDebtDynamics.TidyR7BrownianQV Cochrane.LongTermDebtDynamics.TidyR7ItoIntegral
  Cochrane.LongTermDebtDynamics.TidyR7ItoBridge Cochrane.LongTermDebtDynamics.TidyR7ItoProcess
  Cochrane.LongTermDebtDynamics.TidyR7ItoProductRule
  Cochrane.LongTermDebtDynamics.TidyR7GuidanceSDF
  Cochrane.LongTermDebtDynamics.TidyR7GuidanceItoValuation
  Cochrane.LongTermDebtDynamics.ForwardGuidance
open scoped NNReal

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the natural filtration of the constructed
Brownian motion `bmPath`, on the time index `ℝ`. -/
noncomputable abbrev bmF := bmFiltrationReal bmPath measurable_bmPath

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the constructed Brownian motion on the
time index `ℝ`. -/
noncomputable abbrev bmW : ℝ → (ℕ → ℝ) → ℝ := bmReal bmPath

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: `W_0 = 0` for every path.
Restates `TidyR7BrownianExist.bmPath_zero` on the index `ℝ`. -/
theorem bmW_zero (ω : ℕ → ℝ) : bmW 0 ω = 0 := by
  simp [bmW, bmReal, bmPath_zero]

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: `(t, ω) ↦ W_t(ω)` is jointly measurable
(continuous paths, measurable values). -/
theorem measurable_bmW : Measurable fun p : ℝ × (ℕ → ℝ) => bmW p.1 p.2 :=
  measurable_uncurry_of_continuous_of_measurable (fun ω => continuous_bmReal (continuous_bmPath ω))
    (fun _ => measurable_bmPath _)

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: each `W_u` is integrable.
Restates Mathlib `IsPreBrownianReal.integrable_eval`. -/
theorem integrable_bmW (u : ℝ) : Integrable (bmW u) gaussSeq :=
  isPreBrownianReal_bmPath.integrable_eval _

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: `E[W_u²] = u` for `u ≥ 0`.
The `u = 0` case of `TidyR7BrownianQV.integral_incr_sq`. -/
theorem integral_bmW_sq {u : ℝ} (hu : 0 ≤ u) : ∫ ω, bmW u ω ^ 2 ∂gaussSeq = u := by
  have h := (isPreBrownianReal_bmPath.hasLaw_eval u.toNNReal).integral_comp
    (f := fun x : ℝ => x ^ 2) (by fun_prop)
  rw [integral_sq_gaussianReal, Real.coe_toNNReal _ hu] at h
  exact h

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: `E|W_u| ≤ 1 + u` for `u ≥ 0`. -/
theorem integral_abs_bmW_le {u : ℝ} (hu : 0 ≤ u) : ∫ ω, |bmW u ω| ∂gaussSeq ≤ 1 + u := by
  have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
  have hsq : Integrable (fun ω => bmW u ω ^ 2) gaussSeq :=
    (isPreBrownianReal_bmPath.isGaussianProcess.hasGaussianLaw_eval _).memLp_two.integrable_sq
  have h1 : ∫ ω, |bmW u ω| ∂gaussSeq ≤ ∫ ω, (1 + bmW u ω ^ 2) ∂gaussSeq :=
    integral_mono (integrable_bmW u).abs ((integrable_const 1).add hsq) fun ω => by
      nlinarith [sq_abs (bmW u ω), abs_nonneg (bmW u ω), sq_nonneg (|bmW u ω| - 1)]
  rw [integral_add (integrable_const 1) hsq, integral_bmW_sq hu] at h1
  simpa using h1

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the nominal discount factor of the
model economy**: `Λ_t = e^{−rt}(1 + κW_t)` for `t ≤ T`, `Λ_t = Λ_T e^{−ι(t−T)}` after. -/
noncomputable def bmSDF (κ r T : ℝ) (ι : (ℕ → ℝ) → ℝ) (t : ℝ) (ω : ℕ → ℝ) : ℝ :=
  if t ≤ T then Real.exp (-r * t) * (1 + κ * bmW t ω)
  else Real.exp (-r * T) * (1 + κ * bmW T ω) * Real.exp (-ι ω * (t - T))

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: on `[T, ∞)`,
`Λ_t = Λ_T e^{−ι(t−T)}`. -/
theorem bmSDF_of_ge (κ r : ℝ) {T t : ℝ} (ι : (ℕ → ℝ) → ℝ) (ht : T ≤ t) (ω : ℕ → ℝ) :
    bmSDF κ r T ι t ω = bmSDF κ r T ι T ω * Real.exp (-ι ω * (t - T)) := by
  rcases ht.lt_or_eq with h | h
  · simp only [bmSDF, not_le.2 h, ↓reduceIte, le_refl]
  · subst h
    simp

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the model discount factor is jointly
measurable. -/
theorem measurable_bmSDF (κ r T : ℝ) {ι : (ℕ → ℝ) → ℝ} (hι : Measurable ι) :
    Measurable fun p : ℝ × (ℕ → ℝ) => bmSDF κ r T ι p.1 p.2 := by
  have hW := measurable_bmW
  have hWT : Measurable fun p : ℝ × (ℕ → ℝ) => bmW T p.2 :=
    (measurable_bmPath _).comp measurable_snd
  have hιs : Measurable fun p : ℝ × (ℕ → ℝ) => ι p.2 := hι.comp measurable_snd
  refine Measurable.ite (measurableSet_le measurable_fst measurable_const) ?_ ?_
  · fun_prop
  · fun_prop

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: for `r ≥ 0`, `ι ≥ 0`, `t ≥ 0`,
`|Λ_t| ≤ 1 + |κ| |W_{min(t,T)}|` (`T ≥ 0`). -/
theorem abs_bmSDF_le {κ r T : ℝ} {ι : (ℕ → ℝ) → ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T)
    (hι : ∀ ω, 0 ≤ ι ω) {t : ℝ} (ht : 0 ≤ t) (ω : ℕ → ℝ) :
    |bmSDF κ r T ι t ω| ≤ 1 + |κ| * |bmW (min t T) ω| := by
  have hb : |1 + κ * bmW (min t T) ω| ≤ 1 + |κ| * |bmW (min t T) ω| := by
    calc _ ≤ |(1 : ℝ)| + |κ * bmW (min t T) ω| := abs_add_le _ _
      _ = _ := by rw [abs_one, abs_mul]
  have h0 : 0 ≤ 1 + |κ| * |bmW (min t T) ω| := by positivity
  rcases le_or_gt t T with htT | htT
  · simp only [bmSDF, htT, ↓reduceIte]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [min_eq_left htT] at hb h0 ⊢
    have : Real.exp (-r * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg hr ht])
    nlinarith [abs_nonneg (1 + κ * bmW t ω)]
  · simp only [bmSDF, not_le.2 htT, ↓reduceIte]
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    rw [min_eq_right htT.le] at hb h0 ⊢
    have e1 : Real.exp (-r * T) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg hr hT])
    have e2 : Real.exp (-ι ω * (t - T)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg (hι ω) (sub_nonneg.2 htT.le)])
    have e3 := Real.exp_pos (-r * T)
    have e4 := Real.exp_pos (-ι ω * (t - T))
    have h5 := abs_nonneg (1 + κ * bmW T ω)
    calc Real.exp (-r * T) * |1 + κ * bmW T ω| * Real.exp (-ι ω * (t - T))
        ≤ 1 * |1 + κ * bmW T ω| * 1 := by gcongr
      _ ≤ _ := by linarith

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: each `Λ_t` of the model economy is integrable
(`r ≥ 0`, `ι ≥ 0` measurable, `t ≥ 0`). -/
theorem integrable_bmSDF {κ r T : ℝ} {ι : (ℕ → ℝ) → ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T)
    (hιm : Measurable ι) (hι : ∀ ω, 0 ≤ ι ω) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (bmSDF κ r T ι t) gaussSeq := by
  have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
  refine Integrable.mono' ((integrable_const 1).add ((integrable_bmW (min t T)).abs.const_mul
    |κ|)) ?_ (ae_of_all _ fun ω => abs_bmSDF_le hr hT hι ht ω)
  exact ((measurable_bmSDF κ r T hιm).comp measurable_prodMk_left).aestronglyMeasurable

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: joint integrability.** If `I ⊆ [0, ∞)`
and `|F(j, ω)| ≤ w(j)(1 + |κ||W_{min(j,T)}(ω)|)` on `I` with `w ≥ 0` integrable on `I`, then
`F` is integrable on `I × Ω` (`T ≥ 0`). -/
theorem integrable_prod_bound {κ T : ℝ} (hT : 0 ≤ T) {I : Set ℝ} (hIm : MeasurableSet I)
    (hI : I ⊆ Set.Ici 0) {w : ℝ → ℝ} (hw0 : ∀ j, 0 ≤ w j) (hwm : Measurable w)
    (hwi : IntegrableOn w I) {F : ℝ × (ℕ → ℝ) → ℝ} (hFm : Measurable F)
    (hF : ∀ j ∈ I, ∀ ω, |F (j, ω)| ≤ w j * (1 + |κ| * |bmW (min j T) ω|)) :
    Integrable F ((volume.restrict I).prod gaussSeq) := by
  have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
  have hWm : Measurable fun p : ℝ × (ℕ → ℝ) => bmW (min p.1 T) p.2 :=
    measurable_bmW.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)
  have hGm : Measurable fun p : ℝ × (ℕ → ℝ) => w p.1 * (1 + |κ| * |bmW (min p.1 T) p.2|) :=
    (hwm.comp measurable_fst).mul
      (measurable_const.add (measurable_const.mul (continuous_abs.measurable.comp hWm)))
  have hj1 : ∀ j, Integrable (fun ω => w j * (1 + |κ| * |bmW (min j T) ω|)) gaussSeq :=
    fun j => ((integrable_const (1 : ℝ)).add
      ((integrable_bmW (min j T)).abs.const_mul |κ|)).const_mul (w j)
  have hj2 : ∀ j ∈ I, ∫ ω, ‖w j * (1 + |κ| * |bmW (min j T) ω|)‖ ∂gaussSeq
      ≤ w j * (1 + |κ| * (1 + T)) := by
    intro j hj
    have hj0 : (0 : ℝ) ≤ min j T := le_min (hI hj) hT
    have hn : ∀ ω, ‖w j * (1 + |κ| * |bmW (min j T) ω|)‖
        = w j * (1 + |κ| * |bmW (min j T) ω|) := fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := hw0 j; positivity)]
    simp_rw [hn]
    rw [integral_const_mul, integral_add (integrable_const 1)
      ((integrable_bmW _).abs.const_mul |κ|), integral_const_mul]
    have h1 := integral_abs_bmW_le hj0
    have h2 : min j T ≤ T := min_le_right _ _
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have : |κ| * ∫ ω, |bmW (min j T) ω| ∂gaussSeq ≤ |κ| * (1 + T) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg κ)
    nlinarith [hw0 j]
  have hGint : Integrable (fun p : ℝ × (ℕ → ℝ) => w p.1 * (1 + |κ| * |bmW (min p.1 T) p.2|))
      ((volume.restrict I).prod gaussSeq) := by
    refine (integrable_prod_iff hGm.aestronglyMeasurable).2 ⟨ae_of_all _ fun j => hj1 j, ?_⟩
    refine (hwi.mul_const (1 + |κ| * (1 + T))).mono'
      hGm.norm.aestronglyMeasurable.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem hIm] with j hj
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ω => norm_nonneg _)]
    exact hj2 j hj
  refine hGint.mono' hFm.aestronglyMeasurable ?_
  have hfst := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict I)
    (ν := gaussSeq)).ae (ae_restrict_mem hIm)
  filter_upwards [hfst] with p hp
  rw [Real.norm_eq_abs]
  exact hF p.1 hp p.2

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the deterministic factor `κe^{−rv}` is
an Itô process on `[0, u]` with drift `−rκe^{−rv}` and no diffusion (`r ≥ 0`). -/
theorem itoProcess_detExp (κ : ℝ) {r : ℝ} (hr : 0 ≤ r) (u : ℝ) :
    ItoProcess gaussSeq bmF bmPath (fun v _ => κ * Real.exp (-r * v))
      (fun v _ => -r * (κ * Real.exp (-r * v))) (fun _ _ => 0) 0 u (r * |κ|) 0 where
  adapted _ _ := stronglyMeasurable_const
  init := by
    have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
    exact memLp_const _
  drift := itoIntegrand_deterministic (h := fun v => -r * (κ * Real.exp (-r * v)))
    (by fun_prop) (fun v hv => by
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hr, abs_of_pos (Real.exp_pos _)]
      have : Real.exp (-r * v) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg hr hv.1])
      have h0 := mul_nonneg hr (abs_nonneg κ)
      nlinarith)
  diff := itoIntegrand_deterministic (h := fun _ => 0) continuousOn_const (fun _ _ => by simp)
  eq v hv := by
    have hz := itoInt_const (W := bmPath) (P := gaussSeq) (𝓕 := bmF) isPreBrownianReal_bmPath
      measurable_bmPath (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath)
      le_rfl hv.1 (c := fun _ => (0 : ℝ)) stronglyMeasurable_const (C := 0) (fun _ => by simp)
    filter_upwards [hz] with ω hω
    rw [hω, zero_mul, add_zero]
    have hd : ∀ x ∈ Set.uIcc 0 v, HasDerivAt (fun w => κ * Real.exp (-r * w))
        (-r * (κ * Real.exp (-r * x))) x := fun x _ => by
      have h := (((hasDerivAt_id x).const_mul (-r)).exp).const_mul κ
      refine h.congr_deriv ?_
      simp only [id]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
      apply Continuous.intervalIntegrable; fun_prop)]
    ring

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: before the rate change the model economy
solves `dΛ = −rΛ dt + κe^{−rt} dW`**: a.s., for `u ∈ [0, T]`,
`Λ_u = Λ_0 − r ∫_0^u Λ_v dv + ∫_0^u κe^{−rv} dW_v` (Itô's product rule for `κe^{−rt}·W_t`). -/
theorem bmSDF_pre_eq (κ : ℝ) {r T : ℝ} (hr : 0 ≤ r) (ι : (ℕ → ℝ) → ℝ) {u : ℝ}
    (hu : u ∈ Set.Icc 0 T) :
    bmSDF κ r T ι u =ᵐ[gaussSeq] fun ω => bmSDF κ r T ι 0 ω
      - r * (∫ v in 0..u, bmSDF κ r T ι v ω)
      + itoInt gaussSeq bmF bmPath (fun v _ => κ * Real.exp (-r * v)) 0 u ω := by
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  have h00 : ∀ ω, bmSDF κ r T ι 0 ω = 1 := fun ω => by
    simp [bmSDF, hu.1.trans hu.2, bmW_zero]
  rcases hu.1.eq_or_lt with h0 | h0
  · subst h0
    refine ae_of_all _ fun ω => ?_
    simp [itoInt_of_le]
  have hp := product_rule_pathwise hB measurable_bmPath h𝓕 le_rfl h0
    (itoProcess_detExp κ hr u) (itoProcess_bm (t := u) hB measurable_bmPath h𝓕 le_rfl)
    (ae_of_all _ fun _ => by fun_prop)
    (ae_of_all _ fun ω => (continuous_bmReal (continuous_bmPath ω)).continuousOn)
  have hz := itoInt_const (W := bmPath) (P := gaussSeq) (𝓕 := bmF) hB measurable_bmPath h𝓕
    le_rfl h0.le (c := fun _ => (0 : ℝ)) stronglyMeasurable_const (C := 0) (fun _ => by simp)
  simp only [mul_zero, mul_one, intervalIntegral.integral_zero, zero_add, add_zero] at hp
  filter_upwards [hp, hz] with ω e1 e2
  rw [e2, zero_mul, add_zero] at e1
  have hW0 : bmReal bmPath 0 ω = 0 := bmW_zero ω
  rw [hW0, mul_zero, sub_zero] at e1
  have hcongr : ∫ v in 0..u, bmSDF κ r T ι v ω =
      ∫ v in 0..u, (Real.exp (-r * v) + κ * Real.exp (-r * v) * bmW v ω) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le h0.le] at hv
    simp only [bmSDF, hv.2.trans hu.2, ↓reduceIte]
    ring
  have hc1 : Continuous fun v => Real.exp (-r * v) := by fun_prop
  have hc2 : Continuous fun v => κ * Real.exp (-r * v) * bmW v ω :=
    (by fun_prop : Continuous fun v => κ * Real.exp (-r * v)).mul
      (continuous_bmReal (continuous_bmPath ω))
  rw [hcongr, intervalIntegral.integral_add (hc1.intervalIntegrable _ _)
    (hc2.intervalIntegrable _ _)]
  have hE : r * ∫ v in 0..u, Real.exp (-r * v) = 1 - Real.exp (-r * u) := by
    rw [← intervalIntegral.integral_const_mul]
    have hd : ∀ x ∈ Set.uIcc 0 u, HasDerivAt (fun w => -Real.exp (-r * w))
        (r * Real.exp (-r * x)) x := fun x _ => by
      have h := (((hasDerivAt_id x).const_mul (-r)).exp).neg
      refine h.congr_deriv ?_
      simp only [id]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
      apply Continuous.intervalIntegrable; fun_prop)]
    simp only [mul_zero, Real.exp_zero]
    ring_nf
  have hWint : ∫ v in 0..u, bmReal bmPath v ω * (-r * (κ * Real.exp (-r * v))) =
      -r * ∫ v in 0..u, κ * Real.exp (-r * v) * bmW v ω := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun v _ => ?_
    simp only [bmW]
    ring
  rw [hWint] at e1
  rw [h00 ω]
  simp only [bmSDF, hu.2, ↓reduceIte]
  simp only [bmW] at e1 ⊢
  linear_combination e1 + hE

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: after the rate change the model economy
solves `dΛ = −ιΛ dt`** (no diffusion): a.s., for `T ≤ u`,
`Λ_u = Λ_T − ι ∫_T^u Λ_v dv + ∫_T^u 0 dW`. -/
theorem bmSDF_post_eq (κ r : ℝ) {T : ℝ} (hT : 0 ≤ T) (ι : (ℕ → ℝ) → ℝ) {u : ℝ} (hu : T ≤ u) :
    bmSDF κ r T ι u =ᵐ[gaussSeq] fun ω => bmSDF κ r T ι T ω
      - ι ω * (∫ v in T..u, bmSDF κ r T ι v ω)
      + itoInt gaussSeq bmF bmPath (fun _ _ => 0) T u ω := by
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  have hz := itoInt_const (W := bmPath) (P := gaussSeq) (𝓕 := bmF) hB measurable_bmPath h𝓕
    hT hu (c := fun _ => (0 : ℝ)) stronglyMeasurable_const (C := 0) (fun _ => by simp)
  filter_upwards [hz] with ω e2
  rw [e2, zero_mul, add_zero]
  have hcongr : ∫ v in T..u, bmSDF κ r T ι v ω =
      ∫ v in T..u, bmSDF κ r T ι T ω * Real.exp (-ι ω * (v - T)) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le hu] at hv
    exact bmSDF_of_ge κ r ι hv.1 ω
  have hE : ι ω * ∫ v in T..u, Real.exp (-ι ω * (v - T)) = 1 - Real.exp (-ι ω * (u - T)) := by
    rw [← intervalIntegral.integral_const_mul]
    have hd : ∀ x ∈ Set.uIcc T u, HasDerivAt (fun w => -Real.exp (-ι ω * (w - T)))
        (ι ω * Real.exp (-ι ω * (x - T))) x := fun x _ => by
      have h := ((((hasDerivAt_id x).sub_const T).const_mul (-ι ω)).exp).neg
      refine h.congr_deriv ?_
      simp only [id]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
      apply Continuous.intervalIntegrable; fun_prop)]
    simp only [sub_self, mul_zero, Real.exp_zero]
    ring
  rw [hcongr, intervalIntegral.integral_const_mul, bmSDF_of_ge κ r ι hu ω]
  linear_combination (bmSDF κ r T ι T ω) * hE

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the model economy on `[0, T]` is an
`SDFPiece`** with rate `r` and diffusion `κe^{−rv}` (`r ≥ 0`, `T ≥ 0`, `ι ≥ 0` measurable). -/
theorem bmSDF_pre (κ : ℝ) {r T : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T) {ι : (ℕ → ℝ) → ℝ}
    (hιm : Measurable ι) (hι : ∀ ω, 0 ≤ ι ω) :
    SDFPiece gaussSeq bmF bmPath (bmSDF κ r T ι) (fun v _ => κ * Real.exp (-r * v))
      (fun _ => r) 0 T |κ| where
  adapted := by
    have : bmSDF κ r T ι 0 = fun _ => 1 := funext fun ω => by simp [bmSDF, hT, bmW_zero]
    rw [this]
    exact stronglyMeasurable_const
  rate := stronglyMeasurable_const
  rate_finite := ⟨{r}, fun _ => Finset.mem_singleton_self r⟩
  integ := integrable_prod_bound (κ := κ) hT measurableSet_Ioc
    (fun _ hj => Set.mem_Ici.2 (le_of_lt hj.1)) (w := fun _ => 1) (fun _ => zero_le_one)
    measurable_const (integrableOn_const (by simp) (by simp)) (measurable_bmSDF κ r T hιm)
    (fun j hj ω => by simpa using abs_bmSDF_le (κ := κ) hr hT hι (le_of_lt hj.1) ω)
  integ_at u hu := integrable_bmSDF hr hT hιm hι hu.1
  diff := itoIntegrand_deterministic (h := fun v => κ * Real.exp (-r * v)) (by fun_prop)
    (fun v hv => by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      have : Real.exp (-r * v) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg hr hv.1])
      nlinarith [abs_nonneg κ])
  eq u hu := bmSDF_pre_eq κ hr ι hu

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the model economy on `[T, t]` is an
`SDFPiece`** for every `t`, with the rate `ι` known at `T` (finitely many values, `ι ≥ 0`)
and no diffusion. -/
theorem bmSDF_post (κ : ℝ) {r T : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T) {ι : (ℕ → ℝ) → ℝ}
    (hιT : StronglyMeasurable[bmF T] ι) (hfin : ∃ S : Finset ℝ, ∀ ω, ι ω ∈ S)
    (hι : ∀ ω, 0 ≤ ι ω) (t : ℝ) :
    SDFPiece gaussSeq bmF bmPath (bmSDF κ r T ι) (fun _ _ => 0) ι T t 0 where
  adapted := by
    have : bmSDF κ r T ι T = fun ω => Real.exp (-r * T) * (1 + κ * bmW T ω) :=
      funext fun ω => by simp [bmSDF]
    rw [this]
    exact stronglyMeasurable_const.mul (stronglyMeasurable_const.add
      (stronglyMeasurable_const.mul ((bmFiltrationReal_isBM isPreBrownianReal_bmPath
        measurable_bmPath).adapted T)))
  rate := hιT
  rate_finite := hfin
  integ := integrable_prod_bound (κ := κ) hT measurableSet_Ioc
    (fun _ hj => Set.mem_Ici.2 (hT.trans (le_of_lt hj.1))) (w := fun _ => 1)
    (fun _ => zero_le_one) measurable_const (integrableOn_const (by simp) (by simp))
    (measurable_bmSDF κ r T (hιT.mono (bmF.le T)).measurable)
    (fun j hj ω => by
      simpa using abs_bmSDF_le (κ := κ) hr hT hι (hT.trans (le_of_lt hj.1)) ω)
  integ_at u hu := integrable_bmSDF hr hT (hιT.mono (bmF.le T)).measurable hι (hT.trans hu.1)
  diff := itoIntegrand_deterministic (h := fun _ => 0) continuousOn_const (fun _ _ => by simp)
  eq u hu := bmSDF_post_eq κ r hT ι hu.1

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the model economy satisfies the announcement
structure** `GuidanceSDF` (rate `r` on `[0, T]`, `ι` known at `T` afterwards). -/
theorem guidanceSDF_bm (κ : ℝ) {r T : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T) {ι : (ℕ → ℝ) → ℝ}
    (hιT : StronglyMeasurable[bmF T] ι) (hfin : ∃ S : Finset ℝ, ∀ ω, ι ω ∈ S)
    (hι : ∀ ω, 0 ≤ ι ω) :
    GuidanceSDF gaussSeq bmF bmPath (bmSDF κ r T ι) (fun v _ => κ * Real.exp (-r * v))
      (fun _ _ => 0) r ι T where
  pre := ⟨|κ|, bmSDF_pre κ hr hT (hιT.mono (bmF.le T)).measurable hι⟩
  post t _ := ⟨0, bmSDF_post κ hr hT hιT hfin hι t⟩

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the debt payoffs of the model economy are
jointly integrable**: `(j, ω) ↦ ϖe^{−ϖj}Λ_j(ω)` on `(0, ∞) × Ω` (`ϖ > 0`). -/
theorem integrable_debt_bm (κ : ℝ) {r T ϖ : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T) (hϖ : 0 < ϖ)
    {ι : (ℕ → ℝ) → ℝ} (hιm : Measurable ι) (hι : ∀ ω, 0 ≤ ι ω) :
    Integrable (fun p : ℝ × (ℕ → ℝ) => ϖ * Real.exp (-ϖ * p.1) * bmSDF κ r T ι p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod gaussSeq) := by
  refine integrable_prod_bound (κ := κ) hT measurableSet_Ioi (fun _ hj => Set.mem_Ici.2
    (le_of_lt hj)) (w := fun j => ϖ * Real.exp (-ϖ * j)) (fun j => by positivity)
    (by fun_prop) ((integrableOn_exp_mul_Ioi (by linarith) 0).const_mul ϖ)
    ((by fun_prop : Measurable fun p : ℝ × (ℕ → ℝ) => ϖ * Real.exp (-ϖ * p.1)).mul
      (measurable_bmSDF κ r T hιm)) (fun j hj ω => ?_)
  rw [abs_mul, abs_of_pos (by positivity : 0 < ϖ * Real.exp (-ϖ * j))]
  exact mul_le_mul_of_nonneg_left (abs_bmSDF_le hr hT hι (le_of_lt hj) ω) (by positivity)

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the model economy is genuinely random**:
`E[(Λ_T − e^{−rT})²] = e^{−2rT}κ²T` (`T ≥ 0`), positive for `κ ≠ 0`, `T > 0`. -/
theorem integral_bmSDF_sub_sq (κ r : ℝ) {T : ℝ} (hT : 0 ≤ T) (ι : (ℕ → ℝ) → ℝ) :
    ∫ ω, (bmSDF κ r T ι T ω - Real.exp (-r * T)) ^ 2 ∂gaussSeq
      = Real.exp (-r * T) ^ 2 * κ ^ 2 * T := by
  have e : ∀ ω, (bmSDF κ r T ι T ω - Real.exp (-r * T)) ^ 2
      = Real.exp (-r * T) ^ 2 * κ ^ 2 * bmW T ω ^ 2 := fun ω => by
    simp only [bmSDF, le_refl, ↓reduceIte]
    ring
  simp_rw [e]
  rw [integral_const_mul, integral_bmW_sq hT]

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the value of the debt per unit is
positive, `cfgValue r i ϖ T > 0` for `ϖ > 0`, `r + ϖ > 0`, `i + ϖ > 0`, `T ≥ 0`. -/
theorem cfgValue_pos {r i ϖ T : ℝ} (hϖ : 0 < ϖ) (hrv : 0 < r + ϖ) (hiv : 0 < i + ϖ)
    (hT : 0 ≤ T) : 0 < cfgValue r i ϖ T := by
  have hE : Real.exp (-(r + ϖ) * T) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have h1 : 0 ≤ (1 - Real.exp (-(r + ϖ) * T)) / (r + ϖ) := div_nonneg (by linarith) hrv.le
  have h2 : 0 < Real.exp (-(r + ϖ) * T) / (i + ϖ) := div_pos (Real.exp_pos _) hiv
  rw [cfgValue]
  positivity

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 559: with constant surpluses `s̄` and `r > 0`,
`E_0 ∫_0^∞ e^{−rj} s̄ dj = s̄/r` (the book's `s/r`). -/
theorem pvSurplus_const {r : ℝ} (hr : 0 < r) (sbar : ℝ) :
    pvSurplus gaussSeq bmF r (fun _ _ => sbar) = fun _ => sbar / r := by
  have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
  have h : ∫ j in Set.Ioi (0 : ℝ), Real.exp (-r * j) * sbar = sbar / r := by
    rw [integral_mul_const, integral_exp_mul_Ioi (by linarith) 0]
    field_simp
    simp
  rw [pvSurplus]
  simp_rw [h]
  exact condExp_const (bmF.le 0) _

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: non-vacuity of the stochastic
forward-guidance formula.** On the constructed Brownian motion, for any noise sizes `κ` (with
guidance: `r` then `i` from `T`) and `κ'` (without: `r` throughout), constant surpluses `s̄ > 0`,
`B_0 = 1`, `r > 0`, `i ≥ 0`, `ϖ > 0`, `T ≥ 0`: the price levels `P_0 = cfgValue r i ϖ T · r/s̄`
and `P_0' = cfgValue r r ϖ T · r/s̄` are positive and satisfy the stochastic valuation equations,
and `guidance_jump_ito` applies: `P_0/P_0' − 1 = cfgJump r i ϖ T`. -/
theorem bm_guidance_jump (κ κ' : ℝ) {r i ϖ T sbar : ℝ} (hr : 0 < r) (hi : 0 ≤ i) (hϖ : 0 < ϖ)
    (hT : 0 ≤ T) (hs : 0 < sbar) :
    0 < cfgValue r i ϖ T * r / sbar ∧ 0 < cfgValue r r ϖ T * r / sbar
      ∧ (∀ᵐ ω ∂gaussSeq, 1 / (cfgValue r i ϖ T * r / sbar)
          * debtValue gaussSeq bmF (bmSDF κ r T fun _ => i) ϖ ω
          = pvSurplus gaussSeq bmF r (fun _ _ => sbar) ω)
      ∧ (∀ᵐ ω ∂gaussSeq, 1 / (cfgValue r r ϖ T * r / sbar)
          * debtValue gaussSeq bmF (bmSDF κ' r T fun _ => r) ϖ ω
          = pvSurplus gaussSeq bmF r (fun _ _ => sbar) ω)
      ∧ cfgValue r i ϖ T * r / sbar / (cfgValue r r ϖ T * r / sbar) - 1
          = cfgJump r i ϖ T := by
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  have hrv : 0 < r + ϖ := by linarith
  have hiv : 0 < i + ϖ := by linarith
  have hV := cfgValue_pos hϖ hrv hiv hT
  have hV' := cfgValue_pos hϖ hrv hrv hT
  have hP : 0 < cfgValue r i ϖ T * r / sbar := by positivity
  have hP' : 0 < cfgValue r r ϖ T * r / sbar := by positivity
  have hG := guidanceSDF_bm κ hr.le hT (ι := fun _ => i) stronglyMeasurable_const
    ⟨{i}, fun _ => Finset.mem_singleton_self i⟩ (fun _ => hi)
  have hG' := guidanceSDF_bm κ' hr.le hT (ι := fun _ => r) stronglyMeasurable_const
    ⟨{r}, fun _ => Finset.mem_singleton_self r⟩ (fun _ => hr.le)
  have hI := integrable_debt_bm κ hr.le hT hϖ (ι := fun _ => i) measurable_const (fun _ => hi)
  have hI' := integrable_debt_bm κ' hr.le hT hϖ (ι := fun _ => r) measurable_const
    (fun _ => hr.le)
  have h0 : ∀ (c : ℝ) (ι : (ℕ → ℝ) → ℝ) ω, bmSDF c r T ι 0 ω = 1 := fun c ι ω => by
    simp [bmSDF, hT, bmW_zero]
  have hval : ∀ᵐ ω ∂gaussSeq, 1 / (cfgValue r i ϖ T * r / sbar)
      * debtValue gaussSeq bmF (bmSDF κ r T fun _ => i) ϖ ω
      = pvSurplus gaussSeq bmF r (fun _ _ => sbar) ω := by
    filter_upwards [debtValue_guidance hB measurable_bmPath h𝓕 hT hG hrv hiv hI] with ω hω
    rw [hω (by rw [h0]; exact one_ne_zero), pvSurplus_const hr]
    field_simp
  have hval' : ∀ᵐ ω ∂gaussSeq, 1 / (cfgValue r r ϖ T * r / sbar)
      * debtValue gaussSeq bmF (bmSDF κ' r T fun _ => r) ϖ ω
      = pvSurplus gaussSeq bmF r (fun _ _ => sbar) ω := by
    filter_upwards [debtValue_guidance hB measurable_bmPath h𝓕 hT hG' hrv hrv hI'] with ω hω
    rw [hω (by rw [h0]; exact one_ne_zero), pvSurplus_const hr]
    field_simp
  refine ⟨hP, hP', hval, hval', ?_⟩
  have hj := guidance_jump_ito hB measurable_bmPath h𝓕 hT hϖ hrv hiv (B0 := fun _ => 1)
    (P0 := fun _ => cfgValue r i ϖ T * r / sbar) (P0' := fun _ => cfgValue r r ϖ T * r / sbar)
    hG hI hG' hI' (fun _ => hP) (fun _ => hP') hval hval'
  have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
  obtain ⟨ω, hω⟩ := hj.exists
  refine hω (by rw [h0]; exact one_ne_zero) (by rw [h0]; exact one_ne_zero) ?_
  rw [pvSurplus_const hr]
  positivity

end Cochrane.LongTermDebtDynamics.TidyR7GuidanceItoBM
