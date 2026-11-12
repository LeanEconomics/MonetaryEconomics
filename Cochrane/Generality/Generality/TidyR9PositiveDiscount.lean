/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.TidyR9ReturnRatio
import Generality.TidyR7ItoDiscountFactorCex

/-!
# Positive diffusive discount factors: economies W and V redone, and (1.28) on `bmPath`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1.5, pp. 565–566
(`E_t[d(ΛW)] = 0`, `E_t[d(ΛV)] = −Λs dt`, (1.27)–(1.28)), and Chapter 3, §3.6, (3.35)–(3.36),
p. 74. The economies of `TidyR7ItoDiscountFactorCex` had Gaussian discount factors
(`Λ = 1 − ∫ramp + ∫φ dW`), negative with positive probability. With Itô's formula
(`TidyR9ItoFormulaVariants.itoProcess_discount`, `TidyR9ItoFormulaVariants.itoProcess_inv`)
positive diffusive discount factors with bounded coefficients are available. All economies
live on the constructed Brownian motion `bmPath` (law `gaussSeq`, filtration `bmF`); `B` below
is `bmPath` read on `ℝ`.

## Economy W⁺ (zero surplus, `E_t[d(ΛW)] = 0`)

`Λ = 2 + sin B ∈ [1, 3]` (drift `−½ sin B`, diffusion `cos B`) and the cumulative return
`W = 1/Λ ∈ [1/3, 1]` (Itô's formula for `1/x`). The pricing condition holds (`pwModel`),
`ΛW = 1`; the bracket `σ_Λσ_W = −cos²B/Λ²` has `E∫_0^t < 0`, so the bracket-free step fails
(`pw_bookForm_fails`).

## Economy V⁺ (surplus, infinite horizon)

`Λ = e^{−u}(2 + sin B) ∈ (0, 3]`, `V = 2 + sin B ∈ [1, 3]`, surplus
`s = 3(1 + sin B)²/(2 + sin B) ∈ [0, 12]`; the pricing condition is exact (`pvModel`, using
`sin² + cos² = 1`). The transversality condition holds (`|Λ_TV_T| ≤ 9e^{−T}`, `pv_tvc`), the
valuation `E_0∫_0^{T_k} Λs → Λ_0V_0 = 4` holds (`pv_valuation`), the bracket is
`e^{−u}cos²B ≥ 0` with positive mean, so the bracket-free step fails (`pv_bookForm_fails`).

## The return-ratio economy (A1.5, (1.27)–(1.28) with diffusions)

`W = 2 + sin B`, `V = e^{−ru}(2 + sin B)`, `s = rV` (`r ≥ 0`): (1.27) holds on the coefficients
(`rr_flow`), `W ≥ 1`, so `TidyR9ReturnRatio.ratio_127` applies: `d(V/W) = −(s/W)dt = −re^{−ru}dt`
(`rr_ratio_step`). For `r > 0` the transversality condition holds and (1.28),
`V_t/W_t = ∫_t^∞ s/W = e^{−rt}`, holds pathwise (`rr_valuation`); for `r = 0`, (1.27) holds,
`s = 0`, `V/W = 1`, and (1.28) fails (`rr_E23`, the diffusive E23). Dropping the covariation
`dV·d(1/W)` fails on `[0, t]` (`rr_crossFree_fails`).
-/

namespace Cochrane.Generality.TidyR9PositiveDiscount

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Generality.TidyR7StieltjesSums Cochrane.Generality.TidyR7BrownianTools
  Cochrane.Generality.TidyR7BrownianQV Cochrane.Generality.TidyR7ItoL2
  Cochrane.Generality.TidyR7ItoSums Cochrane.Generality.TidyR7ItoIntegral
  Cochrane.Generality.TidyR7ItoUnbounded Cochrane.Generality.TidyR7ItoProducts
  Cochrane.Generality.TidyR7ItoProcess Cochrane.Generality.TidyR7ItoProductRule
  Cochrane.Generality.TidyR7ItoBondStep Cochrane.Generality.TidyR7BrownianExist
  Cochrane.Generality.TidyR7BrownianSchauder Cochrane.Generality.TidyR7ItoDiscountFactor
  Cochrane.Generality.TidyR7ItoDiscountFactorCex Cochrane.Generality.TidyR9ItoFormula
  Cochrane.Generality.TidyR9ItoFormulaVariants Cochrane.Generality.TidyR9ReturnRatio
open scoped ENNReal NNReal

/-! ## Test processes -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (test processes via Itô's formula):
`a₀ + c sin W` is an Itô process** on every `[s, t]`, `0 ≤ s`, for a Brownian motion with
continuous paths: drift `−½c sin W`, diffusion `c cos W`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9MonetarismItoPositive.itoProcess_affine_sin).
Generalises `TidyR9ItoFormula.itoProcess_sin_bm`. -/
theorem itoProcess_affine_sin {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ} {s t : ℝ} (hBM : IsPreBrownianReal W μ)
    (hWm : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration μ W 𝓕)
    (hcont : ∀ ω, Continuous fun t => W t ω) (hs : 0 ≤ s) (a0 c : ℝ) :
    ItoProcess μ 𝓕 W (fun u ω => a0 + c * Real.sin (bmReal W u ω))
      (fun u ω => -(c * Real.sin (bmReal W u ω) / 2)) (fun u ω => c * Real.cos (bmReal W u ω))
      s t (|c| / 2) |c| := by
  have h := itoProcess_comp (t := t) hBM hWm h𝓕 hs (itoProcess_bm hBM hWm h𝓕 hs)
    (ae_of_all _ fun ω => (continuous_bmReal (hcont ω)).continuousOn)
    (f := fun x => a0 + c * Real.sin x) (f' := fun x => c * Real.cos x)
    (f'' := fun x => c * -Real.sin x)
    (fun x => HasDerivAt.const_add a0 (HasDerivAt.const_mul c (Real.hasDerivAt_sin x)))
    (fun x => HasDerivAt.const_mul c (Real.hasDerivAt_cos x))
    (continuous_const.mul Real.continuous_sin.neg) (L1 := |c|) (L2 := |c|)
    (fun x => by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one x))
    (fun x => by
      rw [abs_mul, abs_neg]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one x))
  have e1 : |c| * 0 + |c| / 2 * (1 * 1) = |c| / 2 := by ring
  have e2 : |c| * 1 = |c| := mul_one _
  rw [e1, e2] at h
  exact itoProcess_of_coeff_eq h (fun u ω => by ring) (fun u ω => by ring)

/-- **Cochrane (2023), A1.5, p. 566 (a positive discounted test process):
`e^{−ru}(a₀ + c sin W)` is an Itô process** on every `[s, t]`, `0 ≤ s ≤ t`, `r ≥ 0`, for a
Brownian motion with continuous paths: drift `e^{−ru}(−r(a₀ + c sin W) − ½c sin W)`,
diffusion `e^{−ru}c cos W`. An instance of `TidyR9ItoFormulaVariants.itoProcess_discount`. -/
theorem itoProcess_discount_sin {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ} {s t : ℝ} (hBM : IsPreBrownianReal W μ)
    (hWm : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration μ W 𝓕)
    (hcont : ∀ ω, Continuous fun t => W t ω) (hs : 0 ≤ s) (hst : s ≤ t) {r : ℝ} (hr : 0 ≤ r)
    (a0 c : ℝ) :
    ItoProcess μ 𝓕 W (fun u ω => Real.exp (-(r * u)) * (a0 + c * Real.sin (bmReal W u ω)))
      (fun u ω => Real.exp (-(r * u)) * (-(r * (a0 + c * Real.sin (bmReal W u ω)))
        - c * Real.sin (bmReal W u ω) / 2))
      (fun u ω => Real.exp (-(r * u)) * (c * Real.cos (bmReal W u ω))) s t
      (r * (|a0| + |c|) + |c| * 0 + |c| / 2 * (1 * 1)) (|c| * 1) := by
  have h := itoProcess_discount hBM hWm h𝓕 hs hst (itoProcess_bm hBM hWm h𝓕 hs)
    (ae_of_all _ fun ω => (continuous_bmReal (hcont ω)).continuousOn) hr
    (g := fun x => a0 + c * Real.sin x) (g' := fun x => c * Real.cos x)
    (g'' := fun x => c * -Real.sin x)
    (fun x => HasDerivAt.const_add a0 (HasDerivAt.const_mul c (Real.hasDerivAt_sin x)))
    (fun x => HasDerivAt.const_mul c (Real.hasDerivAt_cos x))
    (continuous_const.mul Real.continuous_sin.neg) (L0 := |a0| + |c|) (L1 := |c|) (L2 := |c|)
    (fun x => (abs_add_le _ _).trans (add_le_add le_rfl (by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one x))))
    (fun x => by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one x))
    (fun x => by
      rw [abs_mul, abs_neg]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one x))
  refine itoProcess_congr_Icc h hst (fun u _ ω => by simp only [neg_mul])
    (fun u _ ω => by simp only [neg_mul]; ring) (fun u _ ω => by simp only [neg_mul]; ring)

/-- Cochrane (2023), A1.5, p. 566: `1 ≤ 2 + sin x ≤ 3`. -/
theorem two_add_sin_bounds (x : ℝ) : 1 ≤ 2 + Real.sin x ∧ 2 + Real.sin x ≤ 3 := by
  constructor <;> linarith [Real.neg_one_le_sin x, Real.sin_le_one x]

/-- Cochrane (2023), A1.5, p. 566: the constructed Brownian motion read on `ℝ` starts at `0`.
`TidyR7BrownianExist.bmPath_zero` read through `TidyR7BrownianTools.bmReal`. -/
theorem bmReal_bmPath_zero (ω : ℕ → ℝ) : bmReal bmPath 0 ω = 0 := by
  simp [bmReal, bmPath_zero]

/-- Cochrane (2023), A1.5, p. 566: the paths of `bmPath` read on `ℝ` are continuous.
`TidyR7BrownianTools.continuous_bmReal` with `TidyR7BrownianExist.continuous_bmPath`. -/
theorem continuous_bmReal_bmPath (ω : ℕ → ℝ) : Continuous fun u => bmReal bmPath u ω :=
  continuous_bmReal (continuous_bmPath ω)

/-! ## Economy W⁺ -/

/-- Cochrane (2023), A1.5, p. 566 (economy W⁺): the discount factor `Λ = 2 + sin B`. -/
noncomputable abbrev pwΛ : ℝ → (ℕ → ℝ) → ℝ := fun u ω => 2 + Real.sin (bmReal bmPath u ω)

/-- Cochrane (2023), A1.5, p. 566 (economy W⁺): the drift `−½ sin B` of `Λ`. -/
noncomputable abbrev pwaΛ : ℝ → (ℕ → ℝ) → ℝ := fun u ω => -(Real.sin (bmReal bmPath u ω) / 2)

/-- Cochrane (2023), A1.5, p. 566 (economy W⁺): the diffusion `cos B` of `Λ`. -/
noncomputable abbrev pwσΛ : ℝ → (ℕ → ℝ) → ℝ := fun u ω => Real.cos (bmReal bmPath u ω)

/-- Cochrane (2023), A1.5, p. 566 (economy W⁺): the cumulative return `W = 1/Λ`. -/
noncomputable abbrev pwR : ℝ → (ℕ → ℝ) → ℝ := fun u ω => (pwΛ u ω)⁻¹

/-- Cochrane (2023), A1.5, p. 566 (economy W⁺): the drift of `W = 1/Λ`,
`−a_Λ/Λ² + σ_Λ²/Λ³` (Itô's formula for `1/x`). -/
noncomputable abbrev pwaR : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => -(pwaΛ u ω / pwΛ u ω ^ 2) + pwσΛ u ω ^ 2 / pwΛ u ω ^ 3

/-- Cochrane (2023), A1.5, p. 566 (economy W⁺): the diffusion `−σ_Λ/Λ²` of `W = 1/Λ`. -/
noncomputable abbrev pwσR : ℝ → (ℕ → ℝ) → ℝ := fun u ω => -(pwσΛ u ω / pwΛ u ω ^ 2)

/-- Cochrane (2023), A1.5, p. 566 (economy W⁺): `Λ = 2 + sin B` is an Itô process on every
`[s, t]`, `0 ≤ s ≤ t`.
An instance of `itoProcess_affine_sin`. -/
theorem pw_lam_ito {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ItoProcess gaussSeq bmF bmPath pwΛ pwaΛ pwσΛ s t (|1| / 2) |1| := by
  have h := itoProcess_affine_sin (t := t) isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) continuous_bmPath hs 2 1
  exact itoProcess_congr_Icc h hst (fun u _ ω => by simp only [one_mul])
    (fun u _ ω => by simp only [one_mul]) (fun u _ ω => by simp only [one_mul])

/-- Cochrane (2023), A1.5, p. 566 (economy W⁺): `W = 1/Λ` is an Itô process on every `[s, t]`,
`0 ≤ s ≤ t` (`TidyR9ItoFormulaVariants.itoProcess_inv` with `Λ ≥ 1`). -/
theorem pw_ret_ito {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ItoProcess gaussSeq bmF bmPath pwR pwaR pwσR s t
      (((1 : ℝ) ^ 2)⁻¹ * (|1| / 2) + 2 * ((1 : ℝ) ^ 3)⁻¹ / 2 * (|1| * |1|))
      (((1 : ℝ) ^ 2)⁻¹ * |1|) :=
  itoProcess_inv isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) hs hst (pw_lam_ito hs hst)
    (ae_of_all _ fun ω => (continuous_const.add
      (Real.continuous_sin.comp (continuous_bmReal_bmPath ω))).continuousOn) one_pos
    fun _ _ _ => (two_add_sin_bounds _).1

/-- **Cochrane (2023), A1.5, p. 566 (economy W⁺): a zero-surplus pricing model with a POSITIVE
diffusive discount factor** on every `[s, t]`, `0 ≤ s ≤ t`: `Λ = 2 + sin B ∈ [1, 3]` and
`W = 1/Λ ∈ [1/3, 1]` satisfy `Λ a_W + W a_Λ + σ_Λσ_W = 0` (`E_t[d(ΛW)] = 0`). -/
theorem pwModel {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ItoDiscountModel gaussSeq bmF bmPath pwΛ pwR pwaΛ pwσΛ pwaR pwσR (fun _ _ => 0) s t
      (|1| / 2) |1| (((1 : ℝ) ^ 2)⁻¹ * (|1| / 2) + 2 * ((1 : ℝ) ^ 3)⁻¹ / 2 * (|1| * |1|))
      (((1 : ℝ) ^ 2)⁻¹ * |1|) where
  lam_ito := pw_lam_ito hs hst
  val_ito := pw_ret_ito hs hst
  pricing u _ ω := by
    have h0 : pwΛ u ω ≠ 0 := by
      have := (two_add_sin_bounds (bmReal bmPath u ω)).1
      simp only [pwΛ]
      linarith
    simp only [pwaR, pwσR, pwR, mul_zero, neg_zero]
    field_simp
    ring

/-- **Cochrane (2023), A1.5, p. 566 (economy W⁺): positivity.** `1 ≤ Λ ≤ 3` and
`1/3 ≤ W ≤ 1` for every date and state, and `ΛW = 1`. -/
theorem pw_bounds (u : ℝ) (ω : ℕ → ℝ) :
    1 ≤ pwΛ u ω ∧ pwΛ u ω ≤ 3 ∧ 1 / 3 ≤ pwR u ω ∧ pwR u ω ≤ 1 ∧ pwΛ u ω * pwR u ω = 1 := by
  obtain ⟨h1, h2⟩ := two_add_sin_bounds (bmReal bmPath u ω)
  have hp : 0 < pwΛ u ω := by simp only [pwΛ]; linarith
  refine ⟨h1, h2, ?_, inv_le_one_of_one_le₀ h1, mul_inv_cancel₀ hp.ne'⟩
  have := one_div_le_one_div_of_le hp h2
  rwa [one_div (pwΛ u ω)] at this

/-- **Cochrane (2023), A1.5, p. 566 (economy W⁺, the theorem): `E_0[Λ_tW_t − Λ_0W_0] = 0`**
a.s. for `t > 0`, an instance of `TidyR7ItoDiscountFactor.ItoDiscountModel.step_W` with a
positive diffusive `Λ`. -/
theorem pw_step {t : ℝ} (ht : 0 < t) :
    gaussSeq[fun ω => pwΛ t ω * pwR t ω - pwΛ 0 ω * pwR 0 ω | bmF 0] =ᵐ[gaussSeq] 0 :=
  (pwModel le_rfl ht.le).step_W isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) le_rfl ht

/-- **Cochrane (2023), A1.5, p. 566 (economy W⁺): the bracket has negative mean.**
`σ_Λσ_W = −cos²B/Λ²`, and `E[∫_0^t σ_Λσ_W du] < 0` for `t > 0` (on every path the integrand is
`≤ 0`, and `−1/4` at `u = 0`). -/
theorem pw_bracket_neg {t : ℝ} (ht : 0 < t) :
    ∫ ω, (∫ u in (0 : ℝ)..t, pwσΛ u ω * pwσR u ω) ∂gaussSeq < 0 := by
  have := isProb
  have hint : Integrable (fun ω => ∫ u in (0 : ℝ)..t, pwσΛ u ω * pwσR u ω) gaussSeq :=
    (memLp_integral_drift (itoIntegrand_mul (pw_lam_ito le_rfl ht.le).diff
      (pw_ret_ito le_rfl ht.le).diff) le_rfl ht.le le_rfl).integrable one_le_two
  have hpos : ∀ ω, 0 < ∫ u in (0 : ℝ)..t, -(pwσΛ u ω * pwσR u ω) := fun ω => by
    have hc : Continuous fun u => -(pwσΛ u ω * pwσR u ω) := by
      have hB := continuous_bmReal_bmPath ω
      have hΛc : Continuous fun u => pwΛ u ω := continuous_const.add (Real.continuous_sin.comp hB)
      refine ((Real.continuous_cos.comp hB).mul ((Real.continuous_cos.comp hB).div
        (hΛc.pow 2) fun u => ?_).neg).neg
      have := (two_add_sin_bounds (bmReal bmPath u ω)).1
      exact pow_ne_zero _ (by simp only [pwΛ]; linarith)
    have e : ∀ u, -(pwσΛ u ω * pwσR u ω) = Real.cos (bmReal bmPath u ω) ^ 2 / pwΛ u ω ^ 2 :=
      fun u => by simp only [pwσΛ, pwσR]; ring
    refine intervalIntegral.integral_pos ht hc.continuousOn (fun u _ => ?_)
      ⟨0, ⟨le_rfl, ht.le⟩, ?_⟩
    · rw [e]
      exact div_nonneg (sq_nonneg _) (sq_nonneg _)
    · rw [e]
      simp only [pwΛ, bmReal_bmPath_zero, Real.cos_zero, Real.sin_zero]
      norm_num
  have hneg : 0 < ∫ ω, (fun ω => ∫ u in (0 : ℝ)..t, -(pwσΛ u ω * pwσR u ω)) ω ∂gaussSeq := by
    rw [integral_pos_iff_support_of_nonneg (fun ω => (hpos ω).le) (by
      refine hint.neg.congr (ae_of_all _ fun ω => ?_)
      simp only [Pi.neg_apply]
      rw [intervalIntegral.integral_neg])]
    have e : Function.support (fun ω => ∫ u in (0 : ℝ)..t, -(pwσΛ u ω * pwσR u ω)) =
        Set.univ := Set.eq_univ_of_forall fun ω => (hpos ω).ne'
    rw [e, measure_univ]
    exact one_pos
  simp only [intervalIntegral.integral_neg, integral_neg] at hneg
  linarith

/-- **Cochrane (2023), A1.5, p. 566 (economy W⁺): the step without the covariation term fails
with a positive discount factor.** For `t > 0`, `E_0[Λ_tW_t − Λ_0W_0]` is not a.s.
`E_0[∫_0^t Λ a_W du + ∫_0^t W a_Λ du]`.
From `TidyR7ItoDiscountFactor.ItoDiscountModel.bookForm_iff`; the positive analogue of
`TidyR7ItoDiscountFactorCex.w_bookForm_fails`. -/
theorem pw_bookForm_fails {t : ℝ} (ht : 0 < t) :
    ¬ (gaussSeq[fun ω => pwΛ t ω * pwR t ω - pwΛ 0 ω * pwR 0 ω | bmF 0] =ᵐ[gaussSeq]
      gaussSeq[fun ω => dtInt gaussSeq bmF (fun u ω => pwΛ u ω * pwaR u ω) 0 t ω
        + dtInt gaussSeq bmF (fun u ω => pwR u ω * pwaΛ u ω) 0 t ω | bmF 0]) := by
  have := isProb
  intro h
  have hiff := ((pwModel le_rfl ht.le).bookForm_iff isPreBrownianReal_bmPath
    measurable_bmPath (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) le_rfl
    ht).1 h
  have hI := integral_condExp (μ := gaussSeq) (bmF.le 0)
    (f := fun ω => ∫ u in (0 : ℝ)..t, pwσΛ u ω * pwσR u ω)
  rw [integral_congr_ae hiff, Pi.zero_def, integral_zero] at hI
  linarith [pw_bracket_neg ht]

/-! ## Economy V⁺ -/

/-- Cochrane (2023), A1.5, p. 566 (economy V⁺): the discount factor `Λ = e^{−u}(2 + sin B)`. -/
noncomputable abbrev pvΛ : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => Real.exp (-(1 * u)) * (2 + Real.sin (bmReal bmPath u ω))

/-- Cochrane (2023), A1.5, p. 566 (economy V⁺): the drift of `Λ`,
`e^{−u}(−(2 + sin B) − ½ sin B)`. -/
noncomputable abbrev pvaΛ : ℝ → (ℕ → ℝ) → ℝ := fun u ω =>
  Real.exp (-(1 * u)) * (-(1 * (2 + Real.sin (bmReal bmPath u ω)))
    - Real.sin (bmReal bmPath u ω) / 2)

/-- Cochrane (2023), A1.5, p. 566 (economy V⁺): the diffusion `e^{−u}cos B` of `Λ`. -/
noncomputable abbrev pvσΛ : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => Real.exp (-(1 * u)) * Real.cos (bmReal bmPath u ω)

/-- Cochrane (2023), A1.5, p. 566 (economy V⁺): the surplus `s = 3(1 + sin B)²/(2 + sin B)`. -/
noncomputable abbrev pvSp : ℝ → (ℕ → ℝ) → ℝ := fun u ω =>
  3 * (1 + Real.sin (bmReal bmPath u ω)) ^ 2 / (2 + Real.sin (bmReal bmPath u ω))

/-- Cochrane (2023), A1.5, p. 566 (economy V⁺): `Λ = e^{−u}(2 + sin B)` is an Itô process on
every `[s, t]`, `0 ≤ s ≤ t`.
An instance of `itoProcess_discount_sin`. -/
theorem pv_lam_ito {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ItoProcess gaussSeq bmF bmPath pvΛ pvaΛ pvσΛ s t
      (1 * (|2| + |1|) + |1| * 0 + |1| / 2 * (1 * 1)) (|1| * 1) := by
  have h := itoProcess_discount_sin isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) continuous_bmPath hs hst
    zero_le_one 2 1
  exact itoProcess_congr_Icc h hst (fun u _ ω => by simp only [pvΛ, one_mul])
    (fun u _ ω => by simp only [pvaΛ, one_mul]) (fun u _ ω => by simp only [pvσΛ, one_mul])

/-- **Cochrane (2023), A1.5, p. 566 (economy V⁺): a pricing model with surplus and a POSITIVE
diffusive discount factor** on every `[s, t]`, `0 ≤ s ≤ t`: `Λ = e^{−u}(2 + sin B)`,
`V = 2 + sin B`, `s = 3(1 + sin B)²/(2 + sin B)`; `Λ a_V + V a_Λ + σ_Λσ_V = −3e^{−u}(1 + sin B)²
= −Λs` (by `sin² + cos² = 1`). -/
theorem pvModel {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ItoDiscountModel gaussSeq bmF bmPath pvΛ pwΛ pvaΛ pvσΛ pwaΛ pwσΛ pvSp s t
      (1 * (|2| + |1|) + |1| * 0 + |1| / 2 * (1 * 1)) (|1| * 1) (|1| / 2) |1| where
  lam_ito := pv_lam_ito hs hst
  val_ito := pw_lam_ito hs hst
  pricing u _ ω := by
    have hx := Real.sin_sq_add_cos_sq (bmReal bmPath u ω)
    have h0 : 2 + Real.sin (bmReal bmPath u ω) ≠ 0 := by
      have := (two_add_sin_bounds (bmReal bmPath u ω)).1
      linarith
    have hsp : pvΛ u ω * pvSp u ω =
        Real.exp (-(1 * u)) * (3 * (1 + Real.sin (bmReal bmPath u ω)) ^ 2) := by
      simp only [pvΛ, pvSp]
      field_simp
    rw [hsp]
    simp only [pvΛ, pvaΛ, pvσΛ, pwΛ, pwaΛ, pwσΛ]
    linear_combination Real.exp (-(1 * u)) * hx

/-- **Cochrane (2023), A1.5, p. 566 (economy V⁺): positivity and bounds**, for every date
`u ≥ 0` and state: `0 < Λ ≤ 3e^{−u}`, `1 ≤ V ≤ 3`, `0 ≤ s ≤ 12`, `|ΛV| ≤ 9e^{−u}`. -/
theorem pv_bounds (u : ℝ) (ω : ℕ → ℝ) :
    0 < pvΛ u ω ∧ pvΛ u ω ≤ 3 * Real.exp (-(1 * u)) ∧ 1 ≤ pwΛ u ω ∧ pwΛ u ω ≤ 3 ∧
      0 ≤ pvSp u ω ∧ pvSp u ω ≤ 12 ∧ |pvΛ u ω * pwΛ u ω| ≤ 9 * Real.exp (-(1 * u)) := by
  obtain ⟨h1, h2⟩ := two_add_sin_bounds (bmReal bmPath u ω)
  have he := Real.exp_pos (-(1 * u))
  have hs1 := Real.neg_one_le_sin (bmReal bmPath u ω)
  have hs2 := Real.sin_le_one (bmReal bmPath u ω)
  refine ⟨mul_pos he (by linarith), by nlinarith, h1, h2, ?_, ?_, ?_⟩
  · exact div_nonneg (by positivity) (by linarith)
  · simp only [pvSp]
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  · simp only [pvΛ, pwΛ]
    rw [abs_of_pos (by positivity)]
    have : (2 + Real.sin (bmReal bmPath u ω)) * (2 + Real.sin (bmReal bmPath u ω)) ≤ 9 := by
      nlinarith
    nlinarith

/-- Cochrane (2023), A1.5, p. 566 (economy V⁺): `Λ_0V_0 = 2·2 = 4`. -/
theorem pv_initial (ω : ℕ → ℝ) : pvΛ 0 ω * pwΛ 0 ω = 4 := by
  simp only [pvΛ, pwΛ, bmReal_bmPath_zero, Real.sin_zero, mul_zero, neg_zero, Real.exp_zero]
  norm_num

/-- **Cochrane (2023), A1.5, p. 566 (economy V⁺): the transversality condition holds**,
`E_0[Λ_{T_k}V_{T_k}] → 0` for `T_k = k + 1` (`|ΛV| ≤ 9e^{−T}`). -/
theorem pv_tvc :
    ∀ᵐ ω ∂gaussSeq, Tendsto (fun k : ℕ => gaussSeq[fun ω => pvΛ ((k : ℝ) + 1) ω
      * pwΛ ((k : ℝ) + 1) ω | bmF 0] ω) atTop (𝓝 0) := by
  have := isProb
  refine ae_of_all _ fun ω => ?_
  rw [bmF_zero]
  simp only [condExp_bot]
  have hT : Tendsto (fun k : ℕ => 9 * Real.exp (-(1 * ((k : ℝ) + 1)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (1 : ℝ) * ((k : ℝ) + 1)) atTop atTop := by
      simp only [one_mul]
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul 9
    rwa [mul_zero] at this
  refine squeeze_zero_norm (fun k => ?_) hT
  rw [Real.norm_eq_abs]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ ω, |pvΛ ((k : ℝ) + 1) ω * pwΛ ((k : ℝ) + 1) ω| ∂gaussSeq
      ≤ ∫ _, 9 * Real.exp (-(1 * ((k : ℝ) + 1))) ∂gaussSeq :=
        integral_mono_of_nonneg (ae_of_all _ fun ω => abs_nonneg _) (integrable_const _)
          (ae_of_all _ fun ω => (pv_bounds _ ω).2.2.2.2.2.2)
    _ = 9 * Real.exp (-(1 * ((k : ℝ) + 1))) := by simp

/-- **Cochrane (2023), (3.35), p. 74, and A1.5, p. 566 (economy V⁺): the valuation equation
`Λ_0V_0 = E_0∫_0^∞ Λs` with a POSITIVE diffusive discount factor**, in the limit form along
`T_k = k + 1`: `E_0[∫_0^{T_k} Λs du] → Λ_0V_0 = 4` a.s. (an instance of
`TidyR7ItoDiscountFactor.ItoDiscountModel.valuation_seq` with `pv_tvc`). -/
theorem pv_valuation :
    ∀ᵐ ω ∂gaussSeq, Tendsto (fun k : ℕ => gaussSeq[dtInt gaussSeq bmF
      (fun u ω => pvΛ u ω * pvSp u ω) 0 ((k : ℝ) + 1) | bmF 0] ω) atTop (𝓝 4) := by
  have h := (ItoDiscountModel.valuation_seq
    (CΛf := fun _ => 1 * (|2| + |1|) + |1| * 0 + |1| / 2 * (1 * 1)) (CΛσf := fun _ => |1| * 1)
    (CVf := fun _ => |1| / 2) (CVσf := fun _ => |1|) (fun T hT => pvModel le_rfl hT.le)
    isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) le_rfl
    (T := fun k : ℕ => (k : ℝ) + 1) (fun k => by positivity)).2 pv_tvc
  filter_upwards [h] with ω hω
  rwa [pv_initial] at hω

/-- **Cochrane (2023), A1.5, p. 566 (economy V⁺): the bracket has positive mean.**
`σ_Λσ_V = e^{−u}cos²B ≥ 0`, `= 1` at `u = 0`, so `E[∫_0^t σ_Λσ_V du] > 0` for `t > 0`. -/
theorem pv_bracket_pos {t : ℝ} (ht : 0 < t) :
    0 < ∫ ω, (∫ u in (0 : ℝ)..t, pvσΛ u ω * pwσΛ u ω) ∂gaussSeq := by
  have := isProb
  have hint : Integrable (fun ω => ∫ u in (0 : ℝ)..t, pvσΛ u ω * pwσΛ u ω) gaussSeq :=
    (memLp_integral_drift (itoIntegrand_mul (pv_lam_ito le_rfl ht.le).diff
      (pw_lam_ito le_rfl ht.le).diff) le_rfl ht.le le_rfl).integrable one_le_two
  have hpos : ∀ ω, 0 < ∫ u in (0 : ℝ)..t, pvσΛ u ω * pwσΛ u ω := fun ω => by
    have hB := continuous_bmReal_bmPath ω
    have hc : Continuous fun u => pvσΛ u ω * pwσΛ u ω :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
        (Real.continuous_cos.comp hB)).mul (Real.continuous_cos.comp hB)
    refine intervalIntegral.integral_pos ht hc.continuousOn (fun u _ => ?_)
      ⟨0, ⟨le_rfl, ht.le⟩, ?_⟩
    · simp only [pvσΛ, pwσΛ]
      rw [mul_assoc]
      exact mul_nonneg (Real.exp_pos _).le (mul_self_nonneg _)
    · simp only [pvσΛ, pwσΛ, bmReal_bmPath_zero, Real.cos_zero, mul_zero, neg_zero,
        Real.exp_zero]
      norm_num
  rw [integral_pos_iff_support_of_nonneg (fun ω => (hpos ω).le) hint]
  have e : Function.support (fun ω => ∫ u in (0 : ℝ)..t, pvσΛ u ω * pwσΛ u ω) = Set.univ :=
    Set.eq_univ_of_forall fun ω => (hpos ω).ne'
  rw [e, measure_univ]
  exact one_pos

/-- **Cochrane (2023), A1.5, p. 566 (economy V⁺): the step without the covariation fails with
a positive discount factor.** For `t > 0`, `E_0[Λ_tV_t − Λ_0V_0]` is not a.s.
`E_0[∫_0^t Λ a_V + ∫_0^t V a_Λ]`.
From `TidyR7ItoDiscountFactor.ItoDiscountModel.bookForm_iff`; the positive analogue of
`TidyR7ItoDiscountFactorCex.v_bookForm_fails`. -/
theorem pv_bookForm_fails {t : ℝ} (ht : 0 < t) :
    ¬ (gaussSeq[fun ω => pvΛ t ω * pwΛ t ω - pvΛ 0 ω * pwΛ 0 ω | bmF 0] =ᵐ[gaussSeq]
      gaussSeq[fun ω => dtInt gaussSeq bmF (fun u ω => pvΛ u ω * pwaΛ u ω) 0 t ω
        + dtInt gaussSeq bmF (fun u ω => pwΛ u ω * pvaΛ u ω) 0 t ω | bmF 0]) := by
  have := isProb
  intro h
  have hiff := ((pvModel le_rfl ht.le).bookForm_iff isPreBrownianReal_bmPath
    measurable_bmPath (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) le_rfl
    ht).1 h
  have hI := integral_condExp (μ := gaussSeq) (bmF.le 0)
    (f := fun ω => ∫ u in (0 : ℝ)..t, pvσΛ u ω * pwσΛ u ω)
  rw [integral_congr_ae hiff, Pi.zero_def, integral_zero] at hI
  linarith [pv_bracket_pos ht]

/-! ## The return-ratio economy: (1.27)–(1.28) with diffusions -/

/-- Cochrane (2023), A1.5, (1.27), p. 565 (return-ratio economy): the value of debt
`V = e^{−ru}(2 + sin B)`. -/
noncomputable abbrev rrV (r : ℝ) : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => Real.exp (-(r * u)) * (2 + Real.sin (bmReal bmPath u ω))

/-- Cochrane (2023), A1.5, (1.27), p. 565 (return-ratio economy): the drift of `V`,
`e^{−ru}(−r(2 + sin B) − ½ sin B)`. -/
noncomputable abbrev rraV (r : ℝ) : ℝ → (ℕ → ℝ) → ℝ := fun u ω =>
  Real.exp (-(r * u)) * (-(r * (2 + Real.sin (bmReal bmPath u ω)))
    - Real.sin (bmReal bmPath u ω) / 2)

/-- Cochrane (2023), A1.5, (1.27), p. 565 (return-ratio economy): the diffusion `e^{−ru}cos B`
of `V`. -/
noncomputable abbrev rrσV (r : ℝ) : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => Real.exp (-(r * u)) * Real.cos (bmReal bmPath u ω)

/-- Cochrane (2023), A1.5, (1.27), p. 565 (return-ratio economy): the surplus `s = rV`. -/
noncomputable abbrev rrSp (r : ℝ) : ℝ → (ℕ → ℝ) → ℝ := fun u ω => r * rrV r u ω

/-- Cochrane (2023), A1.5, p. 566 (return-ratio economy): `V = e^{−ru}(2 + sin B)` is an Itô
process on every `[s, t]`, `0 ≤ s ≤ t`, `r ≥ 0`.
An instance of `itoProcess_discount_sin`. -/
theorem rr_val_ito {r : ℝ} (hr : 0 ≤ r) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ItoProcess gaussSeq bmF bmPath (rrV r) (rraV r) (rrσV r) s t
      (r * (|2| + |1|) + |1| * 0 + |1| / 2 * (1 * 1)) (|1| * 1) := by
  have h := itoProcess_discount_sin isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) continuous_bmPath hs hst
    hr 2 1
  exact itoProcess_congr_Icc h hst (fun u _ ω => by simp only [one_mul])
    (fun u _ ω => by simp only [one_mul]) (fun u _ ω => by simp only [one_mul])

/-- **Cochrane (2023), A1.5, (1.27), p. 565 (return-ratio economy): the flow (1.27) holds on the
coefficients**, with the cumulative return `W = 2 + sin B` (`TidyR9ReturnRatio` calls it `R`):
`W a_V = V a_W − W s` and `W σ_V = V σ_W` for every date and state. -/
theorem rr_flow (r u : ℝ) (ω : ℕ → ℝ) :
    pwΛ u ω * rraV r u ω = rrV r u ω * pwaΛ u ω - pwΛ u ω * rrSp r u ω ∧
      pwΛ u ω * rrσV r u ω = rrV r u ω * pwσΛ u ω := by
  constructor <;> (simp only [pwΛ, rraV, rrV, pwaΛ, rrSp, rrσV, pwσΛ]; ring)

/-- **Cochrane (2023), A1.5, pp. 565–566 (return-ratio economy): `d(V/W) = −(s/W) dt` on
`bmPath`**, an instance of `TidyR9ReturnRatio.ratio_127`: for `0 ≤ s < t`, `r ≥ 0`, a.s.
`V_t/W_t − V_s/W_s = −∫_s^t s/W`, and `s/W = re^{−ru}`. -/
theorem rr_ratio_step {r : ℝ} (hr : 0 ≤ r) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    (fun ω => rrV r t ω / pwΛ t ω - rrV r s ω / pwΛ s ω) =ᵐ[gaussSeq]
      fun ω => -∫ u in s..t, rrSp r u ω / pwΛ u ω := by
  have hc : ∀ ω, Continuous fun u => pwΛ u ω := fun ω =>
    continuous_const.add (Real.continuous_sin.comp (continuous_bmReal_bmPath ω))
  exact ratio_127 isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) hs hst
    (rr_val_ito hr hs hst.le) (pw_lam_ito hs hst.le)
    (ae_of_all _ fun ω => ((Real.continuous_exp.comp (continuous_const.mul
      continuous_id).neg).mul (hc ω)).continuousOn)
    (ae_of_all _ fun ω => (hc ω).continuousOn) one_pos
    (fun _ _ _ => (two_add_sin_bounds _).1) (fun u _ ω => (rr_flow r u ω).1)
    (fun u _ ω => (rr_flow r u ω).2)

/-- Cochrane (2023), A1.5, p. 566 (return-ratio economy): `V/W = e^{−ru}` and
`s/W = re^{−ru}` for every date and state. -/
theorem rr_ratio_eq (r u : ℝ) (ω : ℕ → ℝ) :
    rrV r u ω / pwΛ u ω = Real.exp (-(r * u)) ∧
      rrSp r u ω / pwΛ u ω = r * Real.exp (-(r * u)) := by
  have h0 : pwΛ u ω ≠ 0 := by
    have := (two_add_sin_bounds (bmReal bmPath u ω)).1
    simp only [pwΛ]
    linarith
  constructor
  · simp only [rrV]
    field_simp
  · simp only [rrSp, rrV]
    field_simp

/-- **Cochrane (2023), A1.5, eq. (1.28), p. 566, with diffusions (return-ratio economy,
`r > 0`):** a.s., the transversality condition `V_{T_k}/W_{T_k} → 0` holds along
`T_k = t + k + 1`, and `V_t/W_t = ∫_t^∞ s_τ/W_τ dτ` (`= e^{−rt}`), the instance of
`TidyR9ReturnRatio.valuation_128_iff` with positive diffusive `V`, `W` and surplus. -/
theorem rr_valuation {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂gaussSeq, Tendsto (fun k : ℕ => rrV r (t + k + 1) ω / pwΛ (t + k + 1) ω) atTop (𝓝 0)
      ∧ rrV r t ω / pwΛ t ω = ∫ u in Set.Ioi t, rrSp r u ω / pwΛ u ω := by
  have hc : ∀ ω, Continuous fun u => pwΛ u ω := fun ω =>
    continuous_const.add (Real.continuous_sin.comp (continuous_bmReal_bmPath ω))
  have hT : ∀ k : ℕ, t < t + k + 1 := fun k => by
    have := k.cast_nonneg (α := ℝ)
    linarith
  have hTlim : Tendsto (fun k : ℕ => t + k + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_atTop_add_const_left _ t
      tendsto_natCast_atTop_atTop)
  have hI : ∀ᵐ ω ∂gaussSeq, IntegrableOn (fun u => rrSp r u ω / pwΛ u ω) (Set.Ioi t) :=
    ae_of_all _ fun ω => by
      have e : (fun u => rrSp r u ω / pwΛ u ω) = fun u => r * Real.exp (-r * u) := by
        funext u
        rw [(rr_ratio_eq r u ω).2, neg_mul]
      rw [e]
      exact (exp_neg_integrableOn_Ioi t hr).const_mul r
  have hv := valuation_128_iff (CVf := fun _ => r * (|2| + |1|) + |1| * 0 + |1| / 2 * (1 * 1))
    (CVσf := fun _ => |1| * 1) (CRf := fun _ => |1| / 2) (CRσf := fun _ => |1|)
    (cf := fun _ => 1) isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) ht
    (fun T hT => rr_val_ito hr.le ht hT.le) (fun T hT => pw_lam_ito ht hT.le)
    (fun T => ae_of_all _ fun ω => ((Real.continuous_exp.comp (continuous_const.mul
      continuous_id).neg).mul (hc ω)).continuousOn)
    (fun T => ae_of_all _ fun ω => (hc ω).continuousOn) (fun _ => one_pos)
    (fun _ _ _ _ => (two_add_sin_bounds _).1) (fun u _ ω => (rr_flow r u ω).1)
    (fun u _ ω => (rr_flow r u ω).2) hT hTlim hI
  filter_upwards [hv] with ω hω
  have htvc : Tendsto (fun k : ℕ => rrV r (t + k + 1) ω / pwΛ (t + k + 1) ω) atTop (𝓝 0) := by
    simp_rw [fun k : ℕ => (rr_ratio_eq r (t + k + 1) ω).1]
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp ((tendsto_id.const_mul_atTop hr).comp hTlim)
  exact ⟨htvc, hω.2 htvc⟩

/-- **Cochrane (2023), A1.5, p. 566, E23 with diffusions (return-ratio economy, `r = 0`):**
`V = W = 2 + sin B` and `s = 0` satisfy the flow (1.27) on the coefficients for every date and
state, yet `V/W = 1` for every date: the limit `V_T/W_T` is `1`, not `0`, and
`V_t/W_t = 1 ≠ 0 = ∫_t^∞ s/W`. "V grows more slowly than W, so the limit is zero" fails. -/
theorem rr_E23 (t : ℝ) (ω : ℕ → ℝ) :
    (∀ u, pwΛ u ω * rraV 0 u ω = rrV 0 u ω * pwaΛ u ω - pwΛ u ω * rrSp 0 u ω ∧
      pwΛ u ω * rrσV 0 u ω = rrV 0 u ω * pwσΛ u ω) ∧
    Tendsto (fun T => rrV 0 T ω / pwΛ T ω) atTop (𝓝 1) ∧
    rrV 0 t ω / pwΛ t ω ≠ ∫ u in Set.Ioi t, rrSp 0 u ω / pwΛ u ω := by
  have e : ∀ u, rrV 0 u ω / pwΛ u ω = 1 := fun u => by
    rw [(rr_ratio_eq 0 u ω).1, zero_mul, neg_zero, Real.exp_zero]
  refine ⟨fun u => rr_flow 0 u ω, ?_, ?_⟩
  · simp_rw [e]
    exact tendsto_const_nhds
  · rw [e]
    simp only [rrSp, zero_mul, zero_div, integral_zero]
    exact one_ne_zero

/-- **Cochrane (2023), A1.5, p. 565 (return-ratio economy): dropping the covariation
`dV·d(1/W)` fails on `[0, t]`**, `t > 0`, `r ≥ 0`: the cross-term-free reading of
`TidyR9ReturnRatio.ratio_crossFree_iff` does not hold a.s., because
`∫_0^t σ_Vσ_W/W² du = ∫_0^t e^{−ru}cos²B/(2 + sin B)² du > 0` on every path. -/
theorem rr_crossFree_fails {r : ℝ} (hr : 0 ≤ r) {t : ℝ} (ht : 0 < t) :
    ¬ ((fun ω => rrV r t ω / pwΛ t ω - rrV r 0 ω / pwΛ 0 ω) =ᵐ[gaussSeq] fun ω =>
      (∫ u in (0 : ℝ)..t, (rraV r u ω / pwΛ u ω - rrV r u ω * pwaΛ u ω / pwΛ u ω ^ 2
        + rrV r u ω * pwσΛ u ω ^ 2 / pwΛ u ω ^ 3))
      + itoInt gaussSeq bmF bmPath (fun u ω => rrσV r u ω / pwΛ u ω
        - rrV r u ω * pwσΛ u ω / pwΛ u ω ^ 2) 0 t ω) := by
  have := isProb
  have hc : ∀ ω, Continuous fun u => pwΛ u ω := fun ω =>
    continuous_const.add (Real.continuous_sin.comp (continuous_bmReal_bmPath ω))
  intro h
  have hiff := (ratio_crossFree_iff isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) le_rfl ht
    (rr_val_ito hr le_rfl ht.le) (pw_lam_ito le_rfl ht.le)
    (ae_of_all _ fun ω => ((Real.continuous_exp.comp (continuous_const.mul
      continuous_id).neg).mul (hc ω)).continuousOn)
    (ae_of_all _ fun ω => (hc ω).continuousOn) one_pos
    (fun _ _ _ => (two_add_sin_bounds _).1)).1 h
  obtain ⟨ω, hω⟩ := hiff.exists
  have hB := continuous_bmReal_bmPath ω
  have hne : ∀ u, pwΛ u ω ^ 2 ≠ 0 := fun u => by
    have := (two_add_sin_bounds (bmReal bmPath u ω)).1
    exact pow_ne_zero _ (by simp only [pwΛ]; linarith)
  have hcont : Continuous fun u => rrσV r u ω * pwσΛ u ω / pwΛ u ω ^ 2 :=
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
      (Real.continuous_cos.comp hB)).mul (Real.continuous_cos.comp hB)).div
      ((hc ω).pow 2) hne
  have hpos : 0 < ∫ u in (0 : ℝ)..t, rrσV r u ω * pwσΛ u ω / pwΛ u ω ^ 2 := by
    refine intervalIntegral.integral_pos ht hcont.continuousOn (fun u _ => ?_)
      ⟨0, ⟨le_rfl, ht.le⟩, ?_⟩
    · simp only [rrσV, pwσΛ]
      rw [mul_assoc]
      exact div_nonneg (mul_nonneg (Real.exp_pos _).le (mul_self_nonneg _)) (sq_nonneg _)
    · simp only [rrσV, pwσΛ, pwΛ, bmReal_bmPath_zero, Real.cos_zero, Real.sin_zero, mul_zero,
        neg_zero, Real.exp_zero]
      norm_num
  linarith

end Cochrane.Generality.TidyR9PositiveDiscount
