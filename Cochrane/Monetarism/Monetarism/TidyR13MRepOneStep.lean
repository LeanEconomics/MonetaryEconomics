/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR13MRepCutoff

/-!
# One step of the density argument: trigonometric exponential martingales

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34) (Track 3, chunk B6, item 2). For `0 ≤ b < a`
and `λ ∈ ℝ`, the Itô formula (`TidyR9ItoFormulaVariants.ito_formula_time_pathwise` with
`f(u, x) = e^{λ²(u − b)/2} cos λx`, where `f_t + f_xx/2 = 0`) gives a.s.

`e^{λ²(a − b)/2} cos λW_a − cos λW_b = ∫_b^a −λ e^{λ²(u − b)/2} sin λW_u dW_u`,

and the same with `sin` (`mrep_ito_cos`, `mrep_ito_sin`). Hence, if `Y ∈ L²` is orthogonal to
every `∫_b^a G dW` (`G` jointly measurable, mean-square continuous on `[b, a]`), then for every
bounded `𝓕_b`-measurable `V`

`E[Y V cos λW_a] = e^{−λ²(a − b)/2} E[Y V cos λW_b]`, and likewise for `sin`

(`mrep_onestep_cos`, `mrep_onestep_sin`), by pulling `V` into the integral
(`TidyR7ItoProducts.itoInt_mul_left`). Paths of `W` are assumed continuous for every `ω` (true
for `TidyR7BrownianExist.bmPath`), which makes `(u, ω) ↦ W_u(ω)` jointly measurable.
-/

namespace Cochrane.Monetarism.TidyR13MRepOneStep

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoIntegral Cochrane.Monetarism.TidyR7ItoUnbounded
  Cochrane.Monetarism.TidyR7ItoProductRule Cochrane.Monetarism.TidyR9ItoFormula
  Cochrane.Monetarism.TidyR9ItoFormulaVariants
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ}

/-- Cochrane (2023), A1 §1.6, pp. 567–568: with continuous paths, `(u, ω) ↦ W_u(ω)` (on the
index `ℝ`) is jointly measurable. -/
theorem mrep_measurable_bm (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) :
    Measurable (Function.uncurry fun u ω => bmReal W u ω) :=
  measurable_uncurry_of_continuous_of_measurable (fun ω => continuous_bmReal (hcont ω))
    (fun _ => hW _)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `u ↦ e^{λ²(u − b)/2}` and its derivative. -/
theorem mrep_hasDerivAt_exp (lam b u : ℝ) :
    HasDerivAt (fun r => Real.exp (lam ^ 2 * (r - b) / 2))
      (lam ^ 2 / 2 * Real.exp (lam ^ 2 * (u - b) / 2)) u := by
  have h1 : HasDerivAt (fun r => lam ^ 2 * (r - b) / 2) (lam ^ 2 * 1 / 2) u :=
    (((hasDerivAt_id u).sub_const b).const_mul (lam ^ 2)).div_const 2
  convert h1.exp using 1
  ring

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `e^{λ²(u − b)/2} ≤ e^{λ²(a − b)/2}` for `u ≤ a`. -/
theorem mrep_exp_le (lam : ℝ) {b a u : ℝ} (hu : u ≤ a) :
    Real.exp (lam ^ 2 * (u - b) / 2) ≤ Real.exp (lam ^ 2 * (a - b) / 2) := by
  refine Real.exp_le_exp.2 ?_
  have : lam ^ 2 * (u - b) ≤ lam ^ 2 * (a - b) :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg lam)
  linarith

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the cosine exponential martingale.** For
`0 ≤ b < a`, a.s. `e^{λ²(a − b)/2} cos λW_a − cos λW_b
= ∫_b^a e^{λ²(u − b)/2}(−λ sin λW_u) dW_u`.
An instance of `TidyR9ItoFormulaVariants.ito_formula_time_pathwise`. -/
theorem mrep_ito_cos (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω) {b a : ℝ}
    (hb : 0 ≤ b) (hba : b < a) (lam : ℝ) :
    (fun ω => Real.exp (lam ^ 2 * (a - b) / 2) * Real.cos (lam * bmReal W a ω)
        - Real.cos (lam * bmReal W b ω)) =ᵐ[P]
      itoInt P 𝓕 W (fun u ω => Real.exp (lam ^ 2 * (u - b) / 2)
        * -(lam * Real.sin (lam * bmReal W u ω))) b a := by
  have hX := itoProcess_bm (t := a) hB hW h𝓕 hb
  have hXc : ∀ᵐ ω ∂P, ContinuousOn (fun u => bmReal W u ω) (Set.Icc b a) :=
    ae_of_all _ fun ω => (continuous_bmReal (hcont ω)).continuousOn
  set E : ℝ := Real.exp (lam ^ 2 * (a - b) / 2) with hE
  have h := ito_formula_time_pathwise hB hW h𝓕 hb hba hX hXc
    (f := fun u x => Real.exp (lam ^ 2 * (u - b) / 2) * Real.cos (lam * x))
    (ft := fun u x => lam ^ 2 / 2 * Real.exp (lam ^ 2 * (u - b) / 2) * Real.cos (lam * x))
    (fx := fun u x => Real.exp (lam ^ 2 * (u - b) / 2) * -(lam * Real.sin (lam * x)))
    (fxx := fun u x => Real.exp (lam ^ 2 * (u - b) / 2) * -(lam * (lam * Real.cos (lam * x))))
    (fun u x => (mrep_hasDerivAt_exp lam b u).mul_const _)
    (fun u x => by
      have := ((hasDerivAt_id' x).const_mul lam).cos.const_mul (Real.exp (lam ^ 2 * (u - b) / 2))
      convert this using 1; ring)
    (fun u x => by
      have := (((hasDerivAt_id' x).const_mul lam).sin.const_mul lam).neg.const_mul
        (Real.exp (lam ^ 2 * (u - b) / 2))
      convert this using 1; ring)
    (by unfold Function.uncurry; fun_prop) (by unfold Function.uncurry; fun_prop)
    (by unfold Function.uncurry; fun_prop) (by unfold Function.uncurry; fun_prop)
    (Lt := lam ^ 2 / 2 * E) (L1 := |lam| * E) (L2 := lam ^ 2 * E)
    (fun u hu x => by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ lam ^ 2 / 2),
        abs_of_nonneg (Real.exp_pos _).le, mul_assoc]
      exact mul_le_mul_of_nonneg_left ((mul_le_of_le_one_right (Real.exp_pos _).le
        (Real.abs_cos_le_one _)).trans (mrep_exp_le lam hu.2)) (by positivity))
    (fun u hu x => by
      rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg (Real.exp_pos _).le, mul_comm]
      exact mul_le_mul (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))
        (mrep_exp_le lam hu.2) (Real.exp_pos _).le (abs_nonneg _))
    (fun u hu x => by
      rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_of_nonneg (Real.exp_pos _).le, mul_comm,
        ← mul_assoc, ← abs_mul, ← sq, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul (mul_le_of_le_one_right (sq_nonneg _) (Real.abs_cos_le_one _))
        (mrep_exp_le lam hu.2) (Real.exp_pos _).le (sq_nonneg _))
  filter_upwards [h] with ω hω
  have e0 : (fun u => lam ^ 2 / 2 * Real.exp (lam ^ 2 * (u - b) / 2)
        * Real.cos (lam * bmReal W u ω)
      + Real.exp (lam ^ 2 * (u - b) / 2) * -(lam * Real.sin (lam * bmReal W u ω)) * 0
      + Real.exp (lam ^ 2 * (u - b) / 2) * -(lam * (lam * Real.cos (lam * bmReal W u ω))) / 2
        * (1 * 1)) = fun _ => 0 := funext fun u => by ring
  have e1 : (fun u ω => Real.exp (lam ^ 2 * (u - b) / 2) * -(lam * Real.sin (lam * bmReal W u ω))
      * 1) = fun u ω => Real.exp (lam ^ 2 * (u - b) / 2) * -(lam * Real.sin (lam * bmReal W u ω))
      := funext fun u => funext fun ω => mul_one _
  rw [e0, intervalIntegral.integral_zero, zero_add, e1] at hω
  simp only [sub_self, mul_zero, zero_div, Real.exp_zero, one_mul] at hω
  exact hω

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the sine exponential martingale.** For
`0 ≤ b < a`, a.s. `e^{λ²(a − b)/2} sin λW_a − sin λW_b
= ∫_b^a e^{λ²(u − b)/2}(λ cos λW_u) dW_u`.
An instance of `TidyR9ItoFormulaVariants.ito_formula_time_pathwise`. -/
theorem mrep_ito_sin (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω) {b a : ℝ}
    (hb : 0 ≤ b) (hba : b < a) (lam : ℝ) :
    (fun ω => Real.exp (lam ^ 2 * (a - b) / 2) * Real.sin (lam * bmReal W a ω)
        - Real.sin (lam * bmReal W b ω)) =ᵐ[P]
      itoInt P 𝓕 W (fun u ω => Real.exp (lam ^ 2 * (u - b) / 2)
        * (lam * Real.cos (lam * bmReal W u ω))) b a := by
  have hX := itoProcess_bm (t := a) hB hW h𝓕 hb
  have hXc : ∀ᵐ ω ∂P, ContinuousOn (fun u => bmReal W u ω) (Set.Icc b a) :=
    ae_of_all _ fun ω => (continuous_bmReal (hcont ω)).continuousOn
  set E : ℝ := Real.exp (lam ^ 2 * (a - b) / 2) with hE
  have h := ito_formula_time_pathwise hB hW h𝓕 hb hba hX hXc
    (f := fun u x => Real.exp (lam ^ 2 * (u - b) / 2) * Real.sin (lam * x))
    (ft := fun u x => lam ^ 2 / 2 * Real.exp (lam ^ 2 * (u - b) / 2) * Real.sin (lam * x))
    (fx := fun u x => Real.exp (lam ^ 2 * (u - b) / 2) * (lam * Real.cos (lam * x)))
    (fxx := fun u x => Real.exp (lam ^ 2 * (u - b) / 2) * -(lam * (lam * Real.sin (lam * x))))
    (fun u x => (mrep_hasDerivAt_exp lam b u).mul_const _)
    (fun u x => by
      have := ((hasDerivAt_id' x).const_mul lam).sin.const_mul (Real.exp (lam ^ 2 * (u - b) / 2))
      convert this using 1; ring)
    (fun u x => by
      have := (((hasDerivAt_id' x).const_mul lam).cos.const_mul lam).const_mul
        (Real.exp (lam ^ 2 * (u - b) / 2))
      convert this using 1; ring)
    (by unfold Function.uncurry; fun_prop) (by unfold Function.uncurry; fun_prop)
    (by unfold Function.uncurry; fun_prop) (by unfold Function.uncurry; fun_prop)
    (Lt := lam ^ 2 / 2 * E) (L1 := |lam| * E) (L2 := lam ^ 2 * E)
    (fun u hu x => by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ lam ^ 2 / 2),
        abs_of_nonneg (Real.exp_pos _).le, mul_assoc]
      exact mul_le_mul_of_nonneg_left ((mul_le_of_le_one_right (Real.exp_pos _).le
        (Real.abs_sin_le_one _)).trans (mrep_exp_le lam hu.2)) (by positivity))
    (fun u hu x => by
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.exp_pos _).le, mul_comm]
      exact mul_le_mul (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
        (mrep_exp_le lam hu.2) (Real.exp_pos _).le (abs_nonneg _))
    (fun u hu x => by
      rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_of_nonneg (Real.exp_pos _).le, mul_comm,
        ← mul_assoc, ← abs_mul, ← sq, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul (mul_le_of_le_one_right (sq_nonneg _) (Real.abs_sin_le_one _))
        (mrep_exp_le lam hu.2) (Real.exp_pos _).le (sq_nonneg _))
  filter_upwards [h] with ω hω
  have e0 : (fun u => lam ^ 2 / 2 * Real.exp (lam ^ 2 * (u - b) / 2)
        * Real.sin (lam * bmReal W u ω)
      + Real.exp (lam ^ 2 * (u - b) / 2) * (lam * Real.cos (lam * bmReal W u ω)) * 0
      + Real.exp (lam ^ 2 * (u - b) / 2) * -(lam * (lam * Real.sin (lam * bmReal W u ω))) / 2
        * (1 * 1)) = fun _ => 0 := funext fun u => by ring
  have e1 : (fun u ω => Real.exp (lam ^ 2 * (u - b) / 2) * (lam * Real.cos (lam * bmReal W u ω))
      * 1) = fun u ω => Real.exp (lam ^ 2 * (u - b) / 2) * (lam * Real.cos (lam * bmReal W u ω))
      := funext fun u => funext fun ω => mul_one _
  rw [e0, intervalIntegral.integral_zero, zero_add, e1] at hω
  simp only [sub_self, mul_zero, zero_div, Real.exp_zero, one_mul] at hω
  exact hω

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the orthogonality step.** Let `Y ∈ L²` be
orthogonal to every `∫_b^a G dW` with `G` jointly measurable and mean-square continuous on
`[b, a]`, `0 ≤ b`. If `Z₁ − Z₀ = ∫_b^a K dW` a.s. for a bounded admissible jointly measurable `K`
and bounded measurable `Z₀, Z₁`, then `E[Y V Z₁] = E[Y V Z₀]` for every bounded
`𝓕_b`-measurable `V`. -/
theorem mrep_orth_step (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {b a : ℝ} (hb : 0 ≤ b) {Y : Ω → ℝ} (hY2 : MemLp Y 2 P)
    (hY : ∀ G : ℝ → Ω → ℝ, MSIntegrand P 𝓕 G b a → Measurable (Function.uncurry G) →
      ∫ ω, Y ω * itoInt P 𝓕 W G b a ω ∂P = 0)
    {K : ℝ → Ω → ℝ} {CK : ℝ} (hK : ItoIntegrand P 𝓕 K b a CK)
    (hKm : Measurable (Function.uncurry K)) {Z₀ Z₁ : Ω → ℝ} (hZ₀ : Measurable Z₀)
    (hZ₁ : Measurable Z₁) {C₀ C₁ : ℝ} (b₀ : ∀ ω, |Z₀ ω| ≤ C₀) (b₁ : ∀ ω, |Z₁ ω| ≤ C₁)
    (hZ : (fun ω => Z₁ ω - Z₀ ω) =ᵐ[P] itoInt P 𝓕 W K b a) {V : Ω → ℝ}
    (hV : StronglyMeasurable[𝓕 b] V) {C : ℝ} (hVb : ∀ ω, |V ω| ≤ C) :
    ∫ ω, Y ω * (V ω * Z₁ ω) ∂P = ∫ ω, Y ω * (V ω * Z₀ ω) ∂P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hVm : Measurable V := (hV.mono (𝓕.le b)).measurable
  have hV2 : MemLp V 2 P := memLp_of_bound hVm hVb
  have hG := Cochrane.Monetarism.TidyR7ItoProducts.MSIntegrand.mul_itoIntegrand
    (msIntegrand_const (s := b) (t := a) hV hV2) hK
  have hGm : Measurable (Function.uncurry fun u ω => V ω * K u ω) :=
    (hVm.comp measurable_snd).mul hKm
  have h0 := hY _ hG hGm
  have hpull := Cochrane.Monetarism.TidyR7ItoProducts.itoInt_mul_left hB hW h𝓕 hb hV hV2 hK
  have hbd : ∀ {Z : Ω → ℝ} {C' : ℝ}, (∀ ω, |Z ω| ≤ C') → ∀ ω, |V ω * Z ω| ≤ C * C' :=
    fun hb' ω => by
      rw [abs_mul]
      exact mul_le_mul (hVb ω) (hb' ω) (abs_nonneg _) ((abs_nonneg _).trans (hVb ω))
  have i1 : Integrable (fun ω => Y ω * (V ω * Z₁ ω)) P :=
    hY2.integrable_mul (memLp_of_bound (hVm.mul hZ₁) (hbd b₁))
  have i0 : Integrable (fun ω => Y ω * (V ω * Z₀ ω)) P :=
    hY2.integrable_mul (memLp_of_bound (hVm.mul hZ₀) (hbd b₀))
  rw [← sub_eq_zero, ← integral_sub i1 i0, ← h0]
  refine integral_congr_ae ?_
  filter_upwards [hZ, hpull] with ω h1 h2
  rw [h2, ← h1]
  ring

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: one step, cosine.** Under the orthogonality
hypothesis on `[b, a]`, `0 ≤ b ≤ a`, for every bounded `𝓕_b`-measurable `V`:
`E[Y V cos λW_a] = e^{−λ²(a − b)/2} E[Y V cos λW_b]`. -/
theorem mrep_onestep_cos (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω) {b a : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) {Y : Ω → ℝ} (hY2 : MemLp Y 2 P)
    (hY : ∀ G : ℝ → Ω → ℝ, MSIntegrand P 𝓕 G b a → Measurable (Function.uncurry G) →
      ∫ ω, Y ω * itoInt P 𝓕 W G b a ω ∂P = 0)
    (lam : ℝ) {V : Ω → ℝ} (hV : StronglyMeasurable[𝓕 b] V) {C : ℝ} (hVb : ∀ ω, |V ω| ≤ C) :
    ∫ ω, Y ω * (V ω * Real.cos (lam * bmReal W a ω)) ∂P
      = Real.exp (-(lam ^ 2 * (a - b) / 2))
        * ∫ ω, Y ω * (V ω * Real.cos (lam * bmReal W b ω)) ∂P := by
  rcases hba.lt_or_eq with hba | hba
  · have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
    set E : ℝ := Real.exp (lam ^ 2 * (a - b) / 2) with hE
    have hXa : ∀ u ∈ Set.Icc b a, StronglyMeasurable[𝓕 u] (bmReal W u) :=
      fun u _ => h𝓕.adapted u
    have hXc : ∀ᵐ ω ∂P, ContinuousOn (fun u => bmReal W u ω) (Set.Icc b a) :=
      ae_of_all _ fun ω => (continuous_bmReal (hcont ω)).continuousOn
    have hK := itoIntegrand_comp (P := P) hXa hXc
      (g := fun u x => Real.exp (lam ^ 2 * (u - b) / 2) * -(lam * Real.sin (lam * x)))
      (by unfold Function.uncurry; fun_prop) (L := |lam| * E) (fun u hu x => by
        rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg (Real.exp_pos _).le, mul_comm]
        exact mul_le_mul (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))
          (mrep_exp_le lam hu.2) (Real.exp_pos _).le (abs_nonneg _))
    have hKm : Measurable (Function.uncurry fun u ω =>
        Real.exp (lam ^ 2 * (u - b) / 2) * -(lam * Real.sin (lam * bmReal W u ω))) := by
      have hm := mrep_measurable_bm hW hcont
      exact ((Real.continuous_exp.measurable.comp ((measurable_const.mul
        (measurable_fst.sub_const b)).div_const 2)).mul
        ((Real.continuous_sin.measurable.comp (measurable_const.mul hm)).const_mul lam).neg)
    have hm1 : Measurable (fun ω => E * Real.cos (lam * bmReal W a ω)) :=
      (Real.continuous_cos.measurable.comp ((hW _).const_mul lam)).const_mul E
    have hm0 : Measurable (fun ω => Real.cos (lam * bmReal W b ω)) :=
      Real.continuous_cos.measurable.comp ((hW _).const_mul lam)
    have h := mrep_orth_step hB hW h𝓕 hb hY2 hY hK hKm hm0 hm1 (C₀ := 1) (C₁ := E)
      (fun ω => Real.abs_cos_le_one _) (fun ω => by
        rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
        exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _))
      (mrep_ito_cos hB hW h𝓕 hcont hb hba lam) hV hVb
    have e : ∫ ω, Y ω * (V ω * (E * Real.cos (lam * bmReal W a ω))) ∂P
        = E * ∫ ω, Y ω * (V ω * Real.cos (lam * bmReal W a ω)) ∂P := by
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun ω => by ring)
    rw [e] at h
    rw [← h, ← mul_assoc, Real.exp_neg, inv_mul_cancel₀ (Real.exp_pos _).ne', one_mul]
  · subst hba
    simp

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: one step, sine.** Under the orthogonality
hypothesis on `[b, a]`, `0 ≤ b ≤ a`, for every bounded `𝓕_b`-measurable `V`:
`E[Y V sin λW_a] = e^{−λ²(a − b)/2} E[Y V sin λW_b]`. -/
theorem mrep_onestep_sin (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω) {b a : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) {Y : Ω → ℝ} (hY2 : MemLp Y 2 P)
    (hY : ∀ G : ℝ → Ω → ℝ, MSIntegrand P 𝓕 G b a → Measurable (Function.uncurry G) →
      ∫ ω, Y ω * itoInt P 𝓕 W G b a ω ∂P = 0)
    (lam : ℝ) {V : Ω → ℝ} (hV : StronglyMeasurable[𝓕 b] V) {C : ℝ} (hVb : ∀ ω, |V ω| ≤ C) :
    ∫ ω, Y ω * (V ω * Real.sin (lam * bmReal W a ω)) ∂P
      = Real.exp (-(lam ^ 2 * (a - b) / 2))
        * ∫ ω, Y ω * (V ω * Real.sin (lam * bmReal W b ω)) ∂P := by
  rcases hba.lt_or_eq with hba | hba
  · have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
    set E : ℝ := Real.exp (lam ^ 2 * (a - b) / 2) with hE
    have hXa : ∀ u ∈ Set.Icc b a, StronglyMeasurable[𝓕 u] (bmReal W u) :=
      fun u _ => h𝓕.adapted u
    have hXc : ∀ᵐ ω ∂P, ContinuousOn (fun u => bmReal W u ω) (Set.Icc b a) :=
      ae_of_all _ fun ω => (continuous_bmReal (hcont ω)).continuousOn
    have hK := itoIntegrand_comp (P := P) hXa hXc
      (g := fun u x => Real.exp (lam ^ 2 * (u - b) / 2) * (lam * Real.cos (lam * x)))
      (by unfold Function.uncurry; fun_prop) (L := |lam| * E) (fun u hu x => by
        rw [abs_mul, abs_mul, abs_of_nonneg (Real.exp_pos _).le, mul_comm]
        exact mul_le_mul (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
          (mrep_exp_le lam hu.2) (Real.exp_pos _).le (abs_nonneg _))
    have hKm : Measurable (Function.uncurry fun u ω =>
        Real.exp (lam ^ 2 * (u - b) / 2) * (lam * Real.cos (lam * bmReal W u ω))) := by
      have hm := mrep_measurable_bm hW hcont
      exact ((Real.continuous_exp.measurable.comp ((measurable_const.mul
        (measurable_fst.sub_const b)).div_const 2)).mul
        ((Real.continuous_cos.measurable.comp (measurable_const.mul hm)).const_mul lam))
    have hm1 : Measurable (fun ω => E * Real.sin (lam * bmReal W a ω)) :=
      (Real.continuous_sin.measurable.comp ((hW _).const_mul lam)).const_mul E
    have hm0 : Measurable (fun ω => Real.sin (lam * bmReal W b ω)) :=
      Real.continuous_sin.measurable.comp ((hW _).const_mul lam)
    have h := mrep_orth_step hB hW h𝓕 hb hY2 hY hK hKm hm0 hm1 (C₀ := 1) (C₁ := E)
      (fun ω => Real.abs_sin_le_one _) (fun ω => by
        rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
        exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_sin_le_one _))
      (mrep_ito_sin hB hW h𝓕 hcont hb hba lam) hV hVb
    have e : ∫ ω, Y ω * (V ω * (E * Real.sin (lam * bmReal W a ω))) ∂P
        = E * ∫ ω, Y ω * (V ω * Real.sin (lam * bmReal W a ω)) ∂P := by
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun ω => by ring)
    rw [e] at h
    rw [← h, ← mul_assoc, Real.exp_neg, inv_mul_cancel₀ (Real.exp_pos _).ne', one_mul]
  · subst hba
    simp

end Cochrane.Monetarism.TidyR13MRepOneStep
