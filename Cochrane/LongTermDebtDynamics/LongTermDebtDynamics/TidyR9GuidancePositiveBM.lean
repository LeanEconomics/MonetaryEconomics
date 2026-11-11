/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR8GuidanceDateTBM
import LongTermDebtDynamics.TidyR9ItoFormulaVariants

/-!
# A positive diffusive nominal discount factor with a known rate

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §A1.2.1,
pp. 559–561: the model economy of TidyR7GuidanceItoBM, `Λ_t = e^{−rt}(1 + κW_t)`, can be
negative for `κ ≠ 0`. Here it is replaced by

`posSDF κ r T ι`: `Λ_t = e^{−rt}(1 + κe^{t/2} sin W_t)` for `t ≤ T`, `Λ_T e^{−ι(t−T)}` after.

`e^{t/2} sin W_t` is a martingale (`∂_t + ½∂_xx` kills `e^{t/2} sin x`), so by Itô's formula
with time dependence (`TidyR9ItoFormulaVariants.itoProcess_comp_time`)
`dΛ = −rΛ dt + κe^{(1/2 − r)t} cos W_t dW` on every `[a, T]`: **the rate `r` stays known and
deterministic**, bond prices are those of the book, and `Λ > 0` throughout when
`|κ|e^{T/2} < 1` (`posSDF_pos`).

## Where a random rate is forced

Within this family the positivity bound is sharp: if `|κ|e^{T/2} > 1` then `Λ_T < 0` with
positive probability (`posSDF_not_pos`). So with a known rate the size of the positive
inflation noise before the news date must shrink like `e^{−T/2}`; a noise of fixed size on an
unbounded horizon (the time-homogeneous `2 + sin W` of the Monetarism project's positive
model) is no longer a martingale after discounting at `r`, and its drift forces the random
rate `i = r + sin W/(2(2 + sin W))`. After the news date the rate is the announced one and
`Λ` decays deterministically, so no random rate is needed there either.

## Main results

* `posSDF_piece`, `posSDF_post`, `guidanceSDF_pos`, `guidanceSDFAt_pos`,
  `integrable_debt_pos`, `integrable_debtAt_pos`: the hypotheses of TidyR7GuidanceItoValuation
  and TidyR8GuidanceDateT hold for every `κ`.
* `posSDF_pos`, `posSDF_not_pos`: positivity iff (essentially) `|κ|e^{T/2} ≤ 1`.
* `pos_guidance_jump` (**`bm_guidance_jump` with `Λ, Λ' > 0`**), `condExp_debtAt_pos`,
  `condExp_debtAt_pos_not_const` and `pos_guidance_jump_at` (**the date-`a` instances of
  TidyR8GuidanceDateTBM with `Λ, Λ' > 0`**, the jump formula now holding wherever
  `s̄ + σW_a > 0`, with no condition `Λ_a ≠ 0` left).
-/

namespace Cochrane.LongTermDebtDynamics.TidyR9GuidancePositiveBM

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.LongTermDebtDynamics.TidyR7BrownianExist
  Cochrane.LongTermDebtDynamics.TidyR7BrownianSchauder
  Cochrane.LongTermDebtDynamics.TidyR7BrownianTools
  Cochrane.LongTermDebtDynamics.TidyR7BrownianQV Cochrane.LongTermDebtDynamics.TidyR7ItoIntegral
  Cochrane.LongTermDebtDynamics.TidyR7ItoBridge Cochrane.LongTermDebtDynamics.TidyR7ItoProcess
  Cochrane.LongTermDebtDynamics.TidyR7ItoProductRule
  Cochrane.LongTermDebtDynamics.TidyR9ItoFormulaVariants
  Cochrane.LongTermDebtDynamics.TidyR7GuidanceSDF
  Cochrane.LongTermDebtDynamics.TidyR7GuidanceItoValuation
  Cochrane.LongTermDebtDynamics.TidyR7GuidanceItoBM
  Cochrane.LongTermDebtDynamics.TidyR7GuidanceItoCex
  Cochrane.LongTermDebtDynamics.TidyR8GuidanceDateT
  Cochrane.LongTermDebtDynamics.TidyR8SurplusInterchange
  Cochrane.LongTermDebtDynamics.TidyR8GuidanceDateTBM
  Cochrane.LongTermDebtDynamics.ForwardGuidance
open scoped NNReal

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: a positive diffusive nominal discount
factor with a known rate**: `Λ_t = e^{−rt}(1 + κe^{t/2} sin W_t)` for `t ≤ T`,
`Λ_t = Λ_T e^{−ι(t−T)}` after. -/
noncomputable def posSDF (κ r T : ℝ) (ι : (ℕ → ℝ) → ℝ) (t : ℝ) (ω : ℕ → ℝ) : ℝ :=
  if t ≤ T then Real.exp (-r * t) * (1 + κ * Real.exp (t / 2) * Real.sin (bmW t ω))
  else Real.exp (-r * T) * (1 + κ * Real.exp (T / 2) * Real.sin (bmW T ω))
    * Real.exp (-ι ω * (t - T))

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: on `[T, ∞)`, `Λ_t = Λ_T e^{−ι(t−T)}`. -/
theorem posSDF_of_ge (κ r : ℝ) {T t : ℝ} (ι : (ℕ → ℝ) → ℝ) (ht : T ≤ t) (ω : ℕ → ℝ) :
    posSDF κ r T ι t ω = posSDF κ r T ι T ω * Real.exp (-ι ω * (t - T)) := by
  rcases ht.lt_or_eq with h | h
  · simp only [posSDF, not_le.2 h, ↓reduceIte, le_refl]
  · subst h
    simp

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: on `(−∞, T]`,
`Λ_t = e^{−rt}(1 + κe^{t/2} sin W_t)`. -/
theorem posSDF_of_le (κ r : ℝ) {T t : ℝ} (ι : (ℕ → ℝ) → ℝ) (ht : t ≤ T) (ω : ℕ → ℝ) :
    posSDF κ r T ι t ω = Real.exp (-r * t) * (1 + κ * Real.exp (t / 2) * Real.sin (bmW t ω)) := by
  simp only [posSDF, ht, ↓reduceIte]

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the positive discount factor is jointly
measurable. -/
theorem measurable_posSDF (κ r T : ℝ) {ι : (ℕ → ℝ) → ℝ} (hι : Measurable ι) :
    Measurable fun p : ℝ × (ℕ → ℝ) => posSDF κ r T ι p.1 p.2 := by
  have hW := measurable_bmW
  have hWT : Measurable fun p : ℝ × (ℕ → ℝ) => bmW T p.2 :=
    (measurable_bmPath _).comp measurable_snd
  have hιs : Measurable fun p : ℝ × (ℕ → ℝ) => ι p.2 := hι.comp measurable_snd
  refine Measurable.ite (measurableSet_le measurable_fst measurable_const) ?_ ?_
  · fun_prop
  · fun_prop

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: `|Λ_t| ≤ 1 + |κ|e^{T/2}` for `t ≥ 0`
(`r ≥ 0`, `ι ≥ 0`, `T ≥ 0`). -/
theorem abs_posSDF_le {κ r T : ℝ} {ι : (ℕ → ℝ) → ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T)
    (hι : ∀ ω, 0 ≤ ι ω) {t : ℝ} (ht : 0 ≤ t) (ω : ℕ → ℝ) :
    |posSDF κ r T ι t ω| ≤ 1 + |κ| * Real.exp (T / 2) := by
  have hb : ∀ u, u ≤ T → |1 + κ * Real.exp (u / 2) * Real.sin (bmW u ω)|
      ≤ 1 + |κ| * Real.exp (T / 2) := fun u hu => by
    have h1 : |κ * Real.exp (u / 2) * Real.sin (bmW u ω)| ≤ |κ| * Real.exp (T / 2) := by
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      have := Real.abs_sin_le_one (bmW u ω)
      have h2 : Real.exp (u / 2) ≤ Real.exp (T / 2) := Real.exp_le_exp.2 (by linarith)
      have h3 := abs_nonneg κ
      have h4 := Real.exp_pos (u / 2)
      calc |κ| * Real.exp (u / 2) * |Real.sin (bmW u ω)| ≤ |κ| * Real.exp (T / 2) * 1 := by
            gcongr
        _ = _ := mul_one _
    calc _ ≤ |(1 : ℝ)| + |κ * Real.exp (u / 2) * Real.sin (bmW u ω)| := abs_add_le _ _
      _ ≤ _ := by rw [abs_one]; linarith
  rcases le_or_gt t T with htT | htT
  · rw [posSDF_of_le κ r ι htT, abs_mul, abs_of_pos (Real.exp_pos _)]
    have : Real.exp (-r * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg hr ht])
    have h0 := abs_nonneg (1 + κ * Real.exp (t / 2) * Real.sin (bmW t ω))
    nlinarith [hb t htT]
  · rw [posSDF_of_ge κ r ι htT.le, posSDF_of_le κ r ι le_rfl, abs_mul, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    have e1 : Real.exp (-r * T) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg hr hT])
    have e2 : Real.exp (-ι ω * (t - T)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg (hι ω) (sub_nonneg.2 htT.le)])
    have e3 := Real.exp_pos (-r * T)
    have e4 := Real.exp_pos (-ι ω * (t - T))
    have h5 := abs_nonneg (1 + κ * Real.exp (T / 2) * Real.sin (bmW T ω))
    have h6 := hb T le_rfl
    calc Real.exp (-r * T) * |1 + κ * Real.exp (T / 2) * Real.sin (bmW T ω)|
          * Real.exp (-ι ω * (t - T))
        ≤ 1 * |1 + κ * Real.exp (T / 2) * Real.sin (bmW T ω)| * 1 := by gcongr
      _ ≤ _ := by linarith

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the discount factor is positive**:
if `|κ|e^{T/2} < 1`, then `Λ_t > 0` for every date `t` and every state. -/
theorem posSDF_pos {κ r T : ℝ} (hκ : |κ| * Real.exp (T / 2) < 1) (ι : (ℕ → ℝ) → ℝ) (t : ℝ)
    (ω : ℕ → ℝ) : 0 < posSDF κ r T ι t ω := by
  have hb : ∀ u, u ≤ T → 0 < 1 + κ * Real.exp (u / 2) * Real.sin (bmW u ω) := fun u hu => by
    have h1 : |κ * Real.exp (u / 2) * Real.sin (bmW u ω)| ≤ |κ| * Real.exp (T / 2) := by
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      have := Real.abs_sin_le_one (bmW u ω)
      have h2 : Real.exp (u / 2) ≤ Real.exp (T / 2) := Real.exp_le_exp.2 (by linarith)
      have h3 := abs_nonneg κ
      calc |κ| * Real.exp (u / 2) * |Real.sin (bmW u ω)| ≤ |κ| * Real.exp (T / 2) * 1 := by
            gcongr
        _ = _ := mul_one _
    linarith [neg_abs_le (κ * Real.exp (u / 2) * Real.sin (bmW u ω))]
  rcases le_or_gt t T with htT | htT
  · rw [posSDF_of_le κ r ι htT]
    exact mul_pos (Real.exp_pos _) (hb t htT)
  · rw [posSDF_of_ge κ r ι htT.le, posSDF_of_le κ r ι le_rfl]
    exact mul_pos (mul_pos (Real.exp_pos _) (hb T le_rfl)) (Real.exp_pos _)

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the positivity bound is sharp.** If
`|κ|e^{T/2} > 1` and `T > 0`, then `Λ_T < 0` with positive probability: within this family a
known rate is compatible with a positive `Λ` on `[0, T]` only for noise of size
`|κ| ≤ e^{−T/2}`. -/
theorem posSDF_not_pos {κ r T : ℝ} (hκ : 1 < |κ| * Real.exp (T / 2)) (hT : 0 < T)
    (ι : (ℕ → ℝ) → ℝ) : gaussSeq {ω | posSDF κ r T ι T ω < 0} ≠ 0 := by
  set K := κ * Real.exp (T / 2) with hK
  have hK1 : 1 < |K| := by
    rw [hK, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact hκ
  set g : ℝ → ℝ := fun x => 1 + K * Real.sin x with hg
  have hgc : Continuous g := by fun_prop
  set x₀ : ℝ := if 0 ≤ K then -(Real.pi / 2) else Real.pi / 2 with hx₀
  have hg0 : g x₀ < 0 := by
    simp only [hg, hx₀]
    split_ifs with h
    · rw [Real.sin_neg, Real.sin_pi_div_two, abs_of_nonneg h] at *
      linarith
    · push Not at h
      rw [Real.sin_pi_div_two, abs_of_neg h] at *
      linarith
  have hopen : IsOpen {x | g x < 0} := isOpen_lt hgc continuous_const
  have hvol : volume {x | g x < 0} ≠ 0 := (hopen.measure_pos volume ⟨x₀, hg0⟩).ne'
  have h := gaussSeq_preimage_pos hT hopen.measurableSet hvol
  refine fun h0 => h (measure_mono_null (fun ω hω => ?_) h0)
  change g (bmW T ω) < 0 at hω
  change posSDF κ r T ι T ω < 0
  simp only [hg, hK] at hω
  rw [posSDF_of_le κ r ι le_rfl]
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) hω

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561, with Itô's formula with time dependence
(`TidyR9ItoFormulaVariants.itoProcess_comp_time`): from any date `a ∈ [0, T]` the positive
discount factor solves `dΛ = −rΛ dt + κe^{(1/2−r)t} cos W_t dW` with the known rate `r`**:
`f(u, x) = e^{−ru}(1 + κe^{u/2} sin x)` has `f_t + ½f_xx = −rf`.
The positive-Λ counterpart of `TidyR8GuidanceDateTBM.bmSDF_mid`. -/
theorem posSDF_piece (κ : ℝ) {r T a : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) (haT : a ≤ T)
    {ι : (ℕ → ℝ) → ℝ} (hιm : Measurable ι) (hι : ∀ ω, 0 ≤ ι ω) :
    SDFPiece gaussSeq bmF bmPath (posSDF κ r T ι)
      (fun u ω => Real.exp (-r * u) * (κ * Real.exp (u / 2) * Real.cos (bmW u ω)) * 1)
      (fun _ => r) a T (|κ| * Real.exp (T / 2) * 1) := by
  have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  set E := Real.exp (T / 2) with hE
  have hbd : ∀ u ∈ Set.Icc a T, Real.exp (-r * u) ≤ 1 ∧ Real.exp (u / 2) ≤ E := fun u hu =>
    ⟨Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg hr (ha.trans hu.1)]),
      Real.exp_le_exp.2 (by linarith [hu.2])⟩
  have hgen : ∀ u ∈ Set.Icc a T, ∀ y : ℝ, |y| ≤ 1 →
      |Real.exp (-r * u) * (κ * Real.exp (u / 2) * y)| ≤ |κ| * E := fun u hu y hy => by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    have h1 := (hbd u hu).1
    have h2 := (hbd u hu).2
    have h3 := abs_nonneg κ
    have h4 := Real.exp_pos (u / 2)
    have h5 := Real.exp_pos (-r * u)
    calc Real.exp (-r * u) * (|κ| * Real.exp (u / 2) * |y|) ≤ 1 * (|κ| * E * 1) := by gcongr
      _ = _ := by ring
  have hX := itoProcess_comp_time hB measurable_bmPath h𝓕 ha haT
    (itoProcess_bm hB measurable_bmPath h𝓕 ha)
    (ae_of_all _ fun ω => (continuous_bmReal (continuous_bmPath ω)).continuousOn)
    (f := fun u x => Real.exp (-r * u) * (1 + κ * Real.exp (u / 2) * Real.sin x))
    (ft := fun u x => -r * (Real.exp (-r * u) * (1 + κ * Real.exp (u / 2) * Real.sin x))
      + Real.exp (-r * u) * (κ * Real.exp (u / 2) * Real.sin x) / 2)
    (fx := fun u x => Real.exp (-r * u) * (κ * Real.exp (u / 2) * Real.cos x))
    (fxx := fun u x => -(Real.exp (-r * u) * (κ * Real.exp (u / 2) * Real.sin x)))
    (fun u x => by
      have e1 := ((hasDerivAt_id' u).const_mul (-r)).exp
      have e2 := ((hasDerivAt_id' u).div_const 2).exp
      have e3 := ((e2.const_mul κ).mul_const (Real.sin x)).const_add 1
      exact HasDerivAt.congr_deriv (e1.mul e3) (by ring))
    (fun u x => by
      have e := (((Real.hasDerivAt_sin x).const_mul (κ * Real.exp (u / 2))).const_add 1).const_mul
        (Real.exp (-r * u))
      exact HasDerivAt.congr_deriv e (by ring))
    (fun u x => by
      have e := ((Real.hasDerivAt_cos x).const_mul (κ * Real.exp (u / 2))).const_mul
        (Real.exp (-r * u))
      exact HasDerivAt.congr_deriv e (by ring))
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (Lt := r * (1 + |κ| * E) + |κ| * E / 2) (L1 := |κ| * E) (L2 := |κ| * E)
    (fun u hu x => by
      have h1 := hgen u hu (Real.sin x) (Real.abs_sin_le_one x)
      have h2 : |Real.exp (-r * u) * (1 + κ * Real.exp (u / 2) * Real.sin x)| ≤ 1 + |κ| * E := by
        have e : Real.exp (-r * u) * (1 + κ * Real.exp (u / 2) * Real.sin x)
            = Real.exp (-r * u) + Real.exp (-r * u) * (κ * Real.exp (u / 2) * Real.sin x) := by
          ring
        rw [e]
        refine (abs_add_le _ _).trans ?_
        rw [abs_of_pos (Real.exp_pos _)]
        linarith [(hbd u hu).1]
      calc _ ≤ |-r * (Real.exp (-r * u) * (1 + κ * Real.exp (u / 2) * Real.sin x))|
            + |Real.exp (-r * u) * (κ * Real.exp (u / 2) * Real.sin x) / 2| := abs_add_le _ _
        _ ≤ r * (1 + |κ| * E) + |κ| * E / 2 := by
          rw [abs_mul, abs_neg, abs_of_nonneg hr, abs_div, abs_two]
          gcongr)
    (fun u hu x => hgen u hu (Real.cos x) (Real.abs_cos_le_one x))
    (fun u hu x => by rw [abs_neg]; exact hgen u hu (Real.sin x) (Real.abs_sin_le_one x))
  have hfX : ∀ u, u ≤ T → posSDF κ r T ι u = fun ω =>
      Real.exp (-r * u) * (1 + κ * Real.exp (u / 2) * Real.sin (bmReal bmPath u ω)) :=
    fun u hu => funext fun ω => posSDF_of_le κ r ι hu ω
  have hK : ∀ t ≥ 0, ∀ ω, ‖posSDF κ r T ι t ω‖ ≤ 1 + |κ| * E := fun t ht ω => by
    rw [Real.norm_eq_abs]; exact abs_posSDF_le hr (ha.trans haT) hι ht ω
  exact
    { adapted := by
        rw [hfX a haT]
        exact hX.adapted a ⟨le_rfl, haT⟩
      rate := stronglyMeasurable_const
      rate_finite := ⟨{r}, fun _ => Finset.mem_singleton_self r⟩
      integ := by
        refine (integrable_const (1 + |κ| * E)).mono'
          (measurable_posSDF κ r T hιm).aestronglyMeasurable ?_
        have hfst := (Measure.quasiMeasurePreserving_fst
          (μ := volume.restrict (Set.Ioc a T)) (ν := gaussSeq)).ae
          (ae_restrict_mem measurableSet_Ioc)
        filter_upwards [hfst] with p hp
        exact hK p.1 (ha.trans (le_of_lt hp.1)) p.2
      integ_at := fun u hu => (integrable_const (1 + |κ| * E)).mono'
        ((measurable_posSDF κ r T hιm).comp
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        (ae_of_all _ fun ω => hK u (ha.trans hu.1) ω)
      diff := hX.diff
      eq := fun u hu => by
        filter_upwards [hX.eq u hu] with ω hω
        rw [hfX u hu.2, hfX a haT]
        beta_reduce at hω ⊢
        rw [hω]
        have hcongr : ∫ v in a..u, (-r * (Real.exp (-r * v) * (1 + κ * Real.exp (v / 2)
              * Real.sin (bmReal bmPath v ω))) + Real.exp (-r * v) * (κ * Real.exp (v / 2)
              * Real.sin (bmReal bmPath v ω)) / 2 + Real.exp (-r * v) * (κ * Real.exp (v / 2)
              * Real.cos (bmReal bmPath v ω)) * 0 + -(Real.exp (-r * v) * (κ * Real.exp (v / 2)
              * Real.sin (bmReal bmPath v ω))) / 2 * (1 * 1))
            = -r * ∫ v in a..u, posSDF κ r T ι v ω := by
          rw [← intervalIntegral.integral_const_mul]
          refine intervalIntegral.integral_congr fun v hv => ?_
          rw [Set.uIcc_of_le hu.1] at hv
          rw [posSDF_of_le κ r ι (hv.2.trans hu.2)]
          ring
        rw [hcongr]
        ring }

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: after the rate change the positive
discount factor solves `dΛ = −ιΛ dt` (no diffusion): a.s., for `T ≤ u`,
`Λ_u = Λ_T − ι ∫_T^u Λ_v dv + ∫_T^u 0 dW`.
The positive-Λ counterpart of `TidyR7GuidanceItoBM.bmSDF_post_eq`. -/
theorem posSDF_post_eq (κ r : ℝ) {T : ℝ} (hT : 0 ≤ T) (ι : (ℕ → ℝ) → ℝ) {u : ℝ} (hu : T ≤ u) :
    posSDF κ r T ι u =ᵐ[gaussSeq] fun ω => posSDF κ r T ι T ω
      - ι ω * (∫ v in T..u, posSDF κ r T ι v ω)
      + itoInt gaussSeq bmF bmPath (fun _ _ => 0) T u ω := by
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  have hz := itoInt_const (W := bmPath) (P := gaussSeq) (𝓕 := bmF) hB measurable_bmPath h𝓕
    hT hu (c := fun _ => (0 : ℝ)) stronglyMeasurable_const (C := 0) (fun _ => by simp)
  filter_upwards [hz] with ω e2
  rw [e2, zero_mul, add_zero]
  have hcongr : ∫ v in T..u, posSDF κ r T ι v ω =
      ∫ v in T..u, posSDF κ r T ι T ω * Real.exp (-ι ω * (v - T)) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le hu] at hv
    exact posSDF_of_ge κ r ι hv.1 ω
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
  rw [hcongr, intervalIntegral.integral_const_mul, posSDF_of_ge κ r ι hu ω]
  linear_combination (posSDF κ r T ι T ω) * hE

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the positive discount factor on
`[T, t]` is an `SDFPiece`** for every `t`, with the rate `ι` known at `T` (finitely many values,
`ι ≥ 0`) and no diffusion.
The positive-Λ counterpart of `TidyR7GuidanceItoBM.bmSDF_post`. -/
theorem posSDF_post (κ : ℝ) {r T : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T) {ι : (ℕ → ℝ) → ℝ}
    (hιT : StronglyMeasurable[bmF T] ι) (hfin : ∃ S : Finset ℝ, ∀ ω, ι ω ∈ S)
    (hι : ∀ ω, 0 ≤ ι ω) (t : ℝ) :
    SDFPiece gaussSeq bmF bmPath (posSDF κ r T ι) (fun _ _ => 0) ι T t 0 := by
  have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
  have hιm : Measurable ι := (hιT.mono (bmF.le T)).measurable
  have hK : ∀ t ≥ 0, ∀ ω, ‖posSDF κ r T ι t ω‖ ≤ 1 + |κ| * Real.exp (T / 2) := fun t ht ω => by
    rw [Real.norm_eq_abs]; exact abs_posSDF_le hr hT hι ht ω
  exact
    { adapted := by
        have e : posSDF κ r T ι T = fun ω =>
            Real.exp (-r * T) * (1 + κ * Real.exp (T / 2) * Real.sin (bmW T ω)) :=
          funext fun ω => posSDF_of_le κ r ι le_rfl ω
        rw [e]
        exact stronglyMeasurable_const.mul (stronglyMeasurable_const.add
          (stronglyMeasurable_const.mul (Real.continuous_sin.comp_stronglyMeasurable
            ((bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath).adapted T))))
      rate := hιT
      rate_finite := hfin
      integ := by
        refine (integrable_const (1 + |κ| * Real.exp (T / 2))).mono'
          (measurable_posSDF κ r T hιm).aestronglyMeasurable ?_
        have hfst := (Measure.quasiMeasurePreserving_fst
          (μ := volume.restrict (Set.Ioc T t)) (ν := gaussSeq)).ae
          (ae_restrict_mem measurableSet_Ioc)
        filter_upwards [hfst] with p hp
        exact hK p.1 (hT.trans (le_of_lt hp.1)) p.2
      integ_at := fun u hu => (integrable_const (1 + |κ| * Real.exp (T / 2))).mono'
        ((measurable_posSDF κ r T hιm).comp
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        (ae_of_all _ fun ω => hK u (hT.trans hu.1) ω)
      diff := itoIntegrand_deterministic (h := fun _ => 0) continuousOn_const
        (fun _ _ => by simp)
      eq := fun u hu => posSDF_post_eq κ r hT ι hu.1 }

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the positive economy satisfies the
announcement structure** `GuidanceSDF` (rate `r` on `[0, T]`, `ι` known at `T` after).
The positive-Λ counterpart of `TidyR7GuidanceItoBM.guidanceSDF_bm`. -/
theorem guidanceSDF_pos (κ : ℝ) {r T : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T) {ι : (ℕ → ℝ) → ℝ}
    (hιT : StronglyMeasurable[bmF T] ι) (hfin : ∃ S : Finset ℝ, ∀ ω, ι ω ∈ S)
    (hι : ∀ ω, 0 ≤ ι ω) :
    GuidanceSDF gaussSeq bmF bmPath (posSDF κ r T ι)
      (fun u ω => Real.exp (-r * u) * (κ * Real.exp (u / 2) * Real.cos (bmW u ω)) * 1)
      (fun _ _ => 0) r ι T where
  pre := ⟨_, posSDF_piece κ hr le_rfl hT (hιT.mono (bmF.le T)).measurable hι⟩
  post t _ := ⟨0, posSDF_post κ hr hT hιT hfin hι t⟩

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the positive economy satisfies the
date-`a` announcement structure** `GuidanceSDFAt` (rate `r` on `[a, a + τ]`, `ι` after).
The positive-Λ counterpart of `TidyR8GuidanceDateTBM.guidanceSDFAt_bm`. -/
theorem guidanceSDFAt_pos (κ : ℝ) {r a τ : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) (hτ : 0 ≤ τ)
    {ι : (ℕ → ℝ) → ℝ} (hιT : StronglyMeasurable[bmF (a + τ)] ι)
    (hfin : ∃ S : Finset ℝ, ∀ ω, ι ω ∈ S) (hι : ∀ ω, 0 ≤ ι ω) :
    GuidanceSDFAt gaussSeq bmF bmPath (posSDF κ r (a + τ) ι)
      (fun u ω => Real.exp (-r * u) * (κ * Real.exp (u / 2) * Real.cos (bmW u ω)) * 1)
      (fun _ _ => 0) r ι a τ where
  pre := ⟨_, posSDF_piece κ hr ha (by linarith) (hιT.mono (bmF.le _)).measurable hι⟩
  post t _ := ⟨0, posSDF_post κ hr (by linarith) hιT hfin hι t⟩

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the debt payoffs of the positive economy
from date `a ≥ 0` are jointly integrable, `(j, ω) ↦ ϖe^{−ϖj}Λ_{a+j}(ω)` on `(0, ∞) × Ω`.
The positive-Λ counterpart of `TidyR8GuidanceDateTBM.integrable_debtAt_bm`. -/
theorem integrable_debtAt_pos (κ : ℝ) {r T a ϖ : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T) (ha : 0 ≤ a)
    (hϖ : 0 < ϖ)
    {ι : (ℕ → ℝ) → ℝ} (hιm : Measurable ι) (hι : ∀ ω, 0 ≤ ι ω) :
    Integrable (fun p : ℝ × (ℕ → ℝ) => ϖ * Real.exp (-ϖ * p.1) * posSDF κ r T ι (a + p.1) p.2)
      ((volume.restrict (Set.Ioi 0)).prod gaussSeq) := by
  have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
  have hw : IntegrableOn (fun j : ℝ => ϖ * Real.exp (-ϖ * j)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul ϖ
  refine (hw.mul_prod (integrable_const (1 + |κ| * Real.exp (T / 2)) (μ := gaussSeq))).mono'
    ((by fun_prop : Measurable fun p : ℝ × (ℕ → ℝ) => ϖ * Real.exp (-ϖ * p.1)).mul
      ((measurable_posSDF κ r T hιm).comp ((measurable_const.add measurable_fst).prodMk
        measurable_snd))).aestronglyMeasurable ?_
  have hfst := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (ν := gaussSeq)).ae (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [hfst] with p hp
  have hwp : 0 < ϖ * Real.exp (-ϖ * p.1) := by positivity
  rw [Real.norm_eq_abs]
  change |ϖ * Real.exp (-ϖ * p.1) * posSDF κ r T ι (a + p.1) p.2|
    ≤ ϖ * Real.exp (-ϖ * p.1) * (1 + |κ| * Real.exp (T / 2))
  rw [abs_mul, abs_of_pos hwp]
  exact mul_le_mul_of_nonneg_left (abs_posSDF_le hr hT hι
    (by linarith [le_of_lt (Set.mem_Ioi.1 hp)]) p.2) hwp.le

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the debt payoffs of the positive economy
are jointly integrable on `(0, ∞) × Ω` (the case `a = 0` of `integrable_debtAt_pos`). -/
theorem integrable_debt_pos (κ : ℝ) {r T ϖ : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T) (hϖ : 0 < ϖ)
    {ι : (ℕ → ℝ) → ℝ} (hιm : Measurable ι) (hι : ∀ ω, 0 ≤ ι ω) :
    Integrable (fun p : ℝ × (ℕ → ℝ) => ϖ * Real.exp (-ϖ * p.1) * posSDF κ r T ι p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod gaussSeq) := by
  simpa using integrable_debtAt_pos κ hr hT le_rfl hϖ hιm hι

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: `bm_guidance_jump` with a positive
discount factor.** On the constructed Brownian motion, for noise sizes `κ, κ'` with
`|κ|e^{T/2}, |κ'|e^{T/2} < 1` (guidance: `r` then `i` from `T`; no guidance: `r` throughout),
constant surpluses `s̄ > 0`, `B_0 = 1`, `r > 0`, `i ≥ 0`, `ϖ > 0`, `T ≥ 0`: both discount factors
are positive at every date and state, the price levels `P_0 = cfgValue r i ϖ T · r/s̄` and
`P_0' = cfgValue r r ϖ T · r/s̄` satisfy the stochastic valuation equations, and
`P_0/P_0' − 1 = cfgJump r i ϖ T` (`TidyR7GuidanceItoValuation.guidance_jump_ito`). -/
theorem pos_guidance_jump {κ κ' r i ϖ T sbar : ℝ} (hκ : |κ| * Real.exp (T / 2) < 1)
    (hκ' : |κ'| * Real.exp (T / 2) < 1) (hr : 0 < r) (hi : 0 ≤ i) (hϖ : 0 < ϖ) (hT : 0 ≤ T)
    (hs : 0 < sbar) :
    (∀ t ω, 0 < posSDF κ r T (fun _ => i) t ω ∧ 0 < posSDF κ' r T (fun _ => r) t ω)
      ∧ (∀ᵐ ω ∂gaussSeq, 1 / (cfgValue r i ϖ T * r / sbar)
          * debtValue gaussSeq bmF (posSDF κ r T fun _ => i) ϖ ω
          = pvSurplus gaussSeq bmF r (fun _ _ => sbar) ω)
      ∧ (∀ᵐ ω ∂gaussSeq, 1 / (cfgValue r r ϖ T * r / sbar)
          * debtValue gaussSeq bmF (posSDF κ' r T fun _ => r) ϖ ω
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
  have hG := guidanceSDF_pos κ hr.le hT (ι := fun _ => i) stronglyMeasurable_const
    ⟨{i}, fun _ => Finset.mem_singleton_self i⟩ (fun _ => hi)
  have hG' := guidanceSDF_pos κ' hr.le hT (ι := fun _ => r) stronglyMeasurable_const
    ⟨{r}, fun _ => Finset.mem_singleton_self r⟩ (fun _ => hr.le)
  have hI := integrable_debt_pos κ hr.le hT hϖ (ι := fun _ => i) measurable_const
    (fun _ => hi)
  have hI' := integrable_debt_pos κ' hr.le hT hϖ (ι := fun _ => r) measurable_const
    (fun _ => hr.le)
  have h0 : ∀ (c : ℝ) (ι : (ℕ → ℝ) → ℝ) ω, posSDF c r T ι 0 ω = 1 := fun c ι ω => by
    rw [posSDF_of_le c r ι hT]
    simp [bmW_zero]
  have hval : ∀ᵐ ω ∂gaussSeq, 1 / (cfgValue r i ϖ T * r / sbar)
      * debtValue gaussSeq bmF (posSDF κ r T fun _ => i) ϖ ω
      = pvSurplus gaussSeq bmF r (fun _ _ => sbar) ω := by
    filter_upwards [debtValue_guidance hB measurable_bmPath h𝓕 hT hG hrv hiv hI] with ω hω
    rw [hω (by rw [h0]; exact one_ne_zero), pvSurplus_const hr]
    field_simp
  have hval' : ∀ᵐ ω ∂gaussSeq, 1 / (cfgValue r r ϖ T * r / sbar)
      * debtValue gaussSeq bmF (posSDF κ' r T fun _ => r) ϖ ω
      = pvSurplus gaussSeq bmF r (fun _ _ => sbar) ω := by
    filter_upwards [debtValue_guidance hB measurable_bmPath h𝓕 hT hG' hrv hrv hI'] with ω hω
    rw [hω (by rw [h0]; exact one_ne_zero), pvSurplus_const hr]
    field_simp
  refine ⟨fun t ω => ⟨posSDF_pos hκ _ t ω, posSDF_pos hκ' _ t ω⟩, hval, hval', ?_⟩
  have hj := guidance_jump_ito hB measurable_bmPath h𝓕 hT hϖ hrv hiv (B0 := fun _ => 1)
    (P0 := fun _ => cfgValue r i ϖ T * r / sbar) (P0' := fun _ => cfgValue r r ϖ T * r / sbar)
    hG hI hG' hI' (fun _ => hP) (fun _ => hP') hval hval'
  have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
  obtain ⟨ω, hω⟩ := hj.exists
  refine hω (by rw [h0]; exact one_ne_zero) (by rw [h0]; exact one_ne_zero) ?_
  rw [pvSurplus_const hr]
  positivity

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the date-`a` value of the debt in the
positive economy**: with the known announcement (`r` on `[a, a + τ]`, `i ≥ 0` after),
`E_a ∫_0^∞ ϖe^{−ϖj}Λ_{a+j} dj = cfgValue r i ϖ τ · e^{−ra}(1 + κe^{a/2} sin W_a)` a.s.
(`TidyR8GuidanceDateT.condExp_debtValueAt` on `guidanceSDFAt_pos`).
The positive-Λ counterpart of `TidyR8GuidanceDateTBM.condExp_debtAt_bm`. -/
theorem condExp_debtAt_pos (κ : ℝ) {r i a τ ϖ : ℝ} (hr : 0 ≤ r) (hi : 0 ≤ i) (ha : 0 ≤ a)
    (hτ : 0 ≤ τ) (hϖ : 0 < ϖ) :
    gaussSeq[fun ω => ∫ j in Set.Ioi (0 : ℝ),
        ϖ * Real.exp (-ϖ * j) * posSDF κ r (a + τ) (fun _ => i) (a + j) ω | bmF a]
      =ᵐ[gaussSeq] fun ω => cfgValue r i ϖ τ
        * (Real.exp (-r * a) * (1 + κ * Real.exp (a / 2) * Real.sin (bmW a ω))) := by
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  have hG := guidanceSDFAt_pos κ hr ha hτ (ι := fun _ => i) stronglyMeasurable_const
    ⟨{i}, fun _ => Finset.mem_singleton_self i⟩ (fun _ => hi)
  have hI := integrable_debtAt_pos κ hr (by linarith) ha hϖ (T := a + τ) (ι := fun _ => i)
    measurable_const
    (fun _ => hi)
  refine (condExp_debtValueAt hB measurable_bmPath h𝓕 ha hτ hG (by linarith) (by linarith)
    hI).trans (ae_of_all _ fun ω => ?_)
  change cfgValue r i ϖ τ * posSDF κ r (a + τ) (fun _ => i) a ω = _
  rw [posSDF_of_le κ r _ (le_add_of_nonneg_right hτ)]

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: for `a > 0`, `sin W_a` is not a.s. equal
to any constant (`W_a` falls in `(1, 2)`, where `sin > 0`, and in `(−2, −1)`, where `sin < 0`,
with positive probability).
The positive-Λ counterpart of `TidyR8GuidanceDateTBM.bmW_not_ae_const`. -/
theorem sin_bmW_not_ae_const {a : ℝ} (ha : 0 < a) (d : ℝ) :
    ¬ ((fun ω => Real.sin (bmW a ω)) =ᵐ[gaussSeq] fun _ => d) := by
  intro h
  have hpi := Real.two_le_pi
  rcases le_or_gt d 0 with hd | hd
  · have hpos := gaussSeq_preimage_pos ha measurableSet_Ioo (A := Set.Ioo 1 2) (by simp)
    refine hpos (measure_mono_null (fun ω hω => ?_) (ae_iff.1 h))
    have hs : 0 < Real.sin (bmW a ω) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hω.1]) (by linarith [hω.2])
    exact fun he => by linarith [show Real.sin (bmW a ω) = d from he]
  · have hpos := gaussSeq_preimage_pos ha measurableSet_Ioo (A := Set.Ioo (-2) (-1)) (by simp)
    refine hpos (measure_mono_null (fun ω hω => ?_) (ae_iff.1 h))
    have hs : Real.sin (bmW a ω) < 0 :=
      Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [hω.2]) (by linarith [hω.1])
    exact fun he => by linarith [show Real.sin (bmW a ω) = d from he]

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: in the positive economy the date-`a`
value of the debt depends on the state.** For `κ ≠ 0`, `a > 0` (and `r, i ≥ 0`, `ϖ > 0`,
`τ ≥ 0`) the conditional expectation of `condExp_debtAt_pos` is not a.s. constant.
The positive-Λ counterpart of `TidyR8GuidanceDateTBM.condExp_debtAt_bm_not_const`. -/
theorem condExp_debtAt_pos_not_const {κ r i a τ ϖ : ℝ} (hκ : κ ≠ 0) (hr : 0 ≤ r) (hi : 0 ≤ i)
    (ha : 0 < a) (hτ : 0 ≤ τ) (hϖ : 0 < ϖ) (c : ℝ) :
    ¬ (gaussSeq[fun ω => ∫ j in Set.Ioi (0 : ℝ),
        ϖ * Real.exp (-ϖ * j) * posSDF κ r (a + τ) (fun _ => i) (a + j) ω | bmF a]
      =ᵐ[gaussSeq] fun _ => c) := by
  intro h
  have hV := cfgValue_pos hϖ (by linarith) (by linarith) hτ (r := r) (i := i)
  have hE := Real.exp_pos (-r * a)
  have hE2 := Real.exp_pos (a / 2)
  refine sin_bmW_not_ae_const ha
    ((c / (cfgValue r i ϖ τ * Real.exp (-r * a)) - 1) / (κ * Real.exp (a / 2))) ?_
  filter_upwards [h, condExp_debtAt_pos κ hr hi ha.le hτ hϖ] with ω h1 h2
  rw [h2] at h1
  have hk : κ * Real.exp (a / 2) ≠ 0 := mul_ne_zero hκ hE2.ne'
  rw [eq_div_iff hk, eq_sub_iff_add_eq, eq_div_iff (by positivity)]
  linear_combination h1

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the date-`a` forward-guidance formula in
the positive economy.** As `TidyR8GuidanceDateTBM.bm_guidance_jump_at`, with the discount
factors `posSDF κ r (a + τ) i` (guidance) and `posSDF κ' r (a + τ) r` (none),
`|κ|e^{(a+τ)/2}, |κ'|e^{(a+τ)/2} < 1`, random surpluses `s̄ + σW_j`, `B_a = 1`, `r > 0`,
`i ≥ 0`, `ϖ > 0`, `a, τ ≥ 0`: both discount factors are positive everywhere, the random price
levels `P_a = cfgValue r i ϖ τ · r/(s̄ + σW_a)`, `P_a' = cfgValue r r ϖ τ · r/(s̄ + σW_a)`
satisfy the date-`a` valuation equations a.s., and `P_a/P_a' − 1 = cfgJump r i ϖ τ` a.s.
wherever `s̄ + σW_a > 0`. -/
theorem pos_guidance_jump_at {κ κ' r i ϖ a τ : ℝ} (sbar σ : ℝ)
    (hκ : |κ| * Real.exp ((a + τ) / 2) < 1) (hκ' : |κ'| * Real.exp ((a + τ) / 2) < 1)
    (hr : 0 < r) (hi : 0 ≤ i) (hϖ : 0 < ϖ) (ha : 0 ≤ a) (hτ : 0 ≤ τ) :
    (∀ t ω, 0 < posSDF κ r (a + τ) (fun _ => i) t ω ∧ 0 < posSDF κ' r (a + τ) (fun _ => r) t ω)
    ∧ (∀ᵐ ω ∂gaussSeq, 1 / (cfgValue r i ϖ τ * r / (sbar + σ * bmW a ω))
          * debtValueAt gaussSeq bmF (posSDF κ r (a + τ) fun _ => i) a ϖ ω
        = pvSurplusAt gaussSeq bmF r a (bmSurplus sbar σ) ω)
    ∧ (∀ᵐ ω ∂gaussSeq, 1 / (cfgValue r r ϖ τ * r / (sbar + σ * bmW a ω))
          * debtValueAt gaussSeq bmF (posSDF κ' r (a + τ) fun _ => r) a ϖ ω
        = pvSurplusAt gaussSeq bmF r a (bmSurplus sbar σ) ω)
    ∧ ∀ᵐ ω ∂gaussSeq, 0 < sbar + σ * bmW a ω →
        cfgValue r i ϖ τ * r / (sbar + σ * bmW a ω)
          / (cfgValue r r ϖ τ * r / (sbar + σ * bmW a ω)) - 1 = cfgJump r i ϖ τ := by
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  have hrv : 0 < r + ϖ := by linarith
  have hiv : 0 < i + ϖ := by linarith
  have hV := cfgValue_pos hϖ hrv hiv hτ
  have hV' := cfgValue_pos hϖ hrv hrv hτ
  have hG := guidanceSDFAt_pos κ hr.le ha hτ (ι := fun _ => i) stronglyMeasurable_const
    ⟨{i}, fun _ => Finset.mem_singleton_self i⟩ (fun _ => hi)
  have hG' := guidanceSDFAt_pos κ' hr.le ha hτ (ι := fun _ => r) stronglyMeasurable_const
    ⟨{r}, fun _ => Finset.mem_singleton_self r⟩ (fun _ => hr.le)
  have hI := integrable_debtAt_pos κ hr.le (by linarith) ha hϖ (T := a + τ) (ι := fun _ => i)
    measurable_const (fun _ => hi)
  have hI' := integrable_debtAt_pos κ' hr.le (by linarith) ha hϖ (T := a + τ)
    (ι := fun _ => r)
    measurable_const (fun _ => hr.le)
  have hpv := pvSurplusAt_bm sbar σ hr ha
  have key : ∀ {V S : ℝ}, V ≠ 0 → 1 / (V * r / S) * V = S / r := fun {V S} hV0 => by
    rw [one_div_div, div_mul_eq_mul_div, mul_comm V r, mul_div_mul_right _ _ hV0]
  have hval : ∀ᵐ ω ∂gaussSeq, 1 / (cfgValue r i ϖ τ * r / (sbar + σ * bmW a ω))
        * debtValueAt gaussSeq bmF (posSDF κ r (a + τ) fun _ => i) a ϖ ω
      = pvSurplusAt gaussSeq bmF r a (bmSurplus sbar σ) ω := by
    filter_upwards [debtValueAt_guidance hB measurable_bmPath h𝓕 ha hτ hG hrv hiv hI, hpv]
      with ω e1 e2
    rw [e1 (posSDF_pos hκ _ a ω).ne', e2]
    exact key hV.ne'
  have hval' : ∀ᵐ ω ∂gaussSeq, 1 / (cfgValue r r ϖ τ * r / (sbar + σ * bmW a ω))
        * debtValueAt gaussSeq bmF (posSDF κ' r (a + τ) fun _ => r) a ϖ ω
      = pvSurplusAt gaussSeq bmF r a (bmSurplus sbar σ) ω := by
    filter_upwards [debtValueAt_guidance hB measurable_bmPath h𝓕 ha hτ hG' hrv hrv hI', hpv]
      with ω e1 e2
    rw [e1 (posSDF_pos hκ' _ a ω).ne', e2]
    exact key hV'.ne'
  refine ⟨fun t ω => ⟨posSDF_pos hκ _ t ω, posSDF_pos hκ' _ t ω⟩, hval, hval', ?_⟩
  have hj := guidance_jump_at hB measurable_bmPath h𝓕 ha hτ hϖ hrv hiv (B := fun _ => 1)
    (Pa := fun ω => cfgValue r i ϖ τ * r / (sbar + σ * bmW a ω))
    (Pa' := fun ω => cfgValue r r ϖ τ * r / (sbar + σ * bmW a ω))
    (s := bmSurplus sbar σ) hG hI hG' hI' (by filter_upwards [hval] with ω h _; exact h)
    (by filter_upwards [hval'] with ω h _; exact h)
  filter_upwards [hj, hpv] with ω hω e2 hS
  exact hω (posSDF_pos hκ _ a ω).ne' (posSDF_pos hκ' _ a ω).ne'
    (by rw [e2]; exact (div_pos hS hr).ne') (div_pos (mul_pos hV hr) hS)
    (div_pos (mul_pos hV' hr) hS)

end Cochrane.LongTermDebtDynamics.TidyR9GuidancePositiveBM
