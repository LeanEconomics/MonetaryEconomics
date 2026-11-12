/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR13MRepTheorem

/-!
# Martingale representation on the constructed Brownian motion

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568; used for the stochastic Werning model of Chapter 20, §20.2,
pp. 474–476.

The mathematical part of the Cochrane Monetarism module TidyR13MRepMonetarism (the natural
filtration hypothesis, the instances on the constructed motion and the a.e.-invariance of the
extended integral). Not restated: the exponential-SDF instance and the characterisation of the
martingales covered by the Monetarism (1.32) step, which need the Monetarism SDE modules.

## Main results

* `mrep_bmFiltrationReal_le`: the natural filtration satisfies `𝓕_T ⊆ 𝓖_T`.
* On the constructed motion `TidyR7BrownianExist.bmPath`: `mrep_representation_bmPath`,
  `mrep_martingale_bmPath`; `mrep_indicator_bmPath` (`1{W_T > 0}`); `mrep_sq_bmPath`
  (`W_T² = T + ∫_0^T 2W dW`, unique).
* `mrepInt_congr_ae`: the extended integral depends only on the `dt × dP`-class of `H`.
-/

namespace Cochrane.ZeroBound.TidyR13MRepMonetarism

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.TidyR7StieltjesSums Cochrane.ZeroBound.TidyR7BrownianTools
  Cochrane.ZeroBound.TidyR7BrownianExist Cochrane.ZeroBound.TidyR7BrownianSchauder
  Cochrane.ZeroBound.TidyR7BrownianQV Cochrane.ZeroBound.TidyR7ItoL2
  Cochrane.ZeroBound.TidyR7ItoIntegral Cochrane.ZeroBound.TidyR7ItoUnbounded
  Cochrane.ZeroBound.TidyR7ItoProductRule Cochrane.ZeroBound.TidyR9ItoFormula
  Cochrane.ZeroBound.TidyR13MRepIntegral Cochrane.ZeroBound.TidyR13MRepCutoff
  Cochrane.ZeroBound.TidyR13MRepOneStep Cochrane.ZeroBound.TidyR13MRepDensity
  Cochrane.ZeroBound.TidyR13MRepTheorem Cochrane.ZeroBound.TidyR7ItoProducts
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ}

/-! ## The natural filtration -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the natural filtration satisfies the hypothesis
`𝓕_T ⊆ 𝓖_T`** of `TidyR13MRepTheorem.mrep_representation`, `T ≥ 0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepMonetarism.mrep_bmFiltrationReal_le). -/
theorem mrep_bmFiltrationReal_le (hW : ∀ t, Measurable (W t)) {T : ℝ} (hT : 0 ≤ T) :
    bmFiltrationReal W hW T ≤ mrepNat W T := by
  change (⨆ j ≤ T.toNNReal, MeasurableSpace.comap (W j) inferInstance) ≤ mrepNat W T
  refine iSup₂_le fun j hj => ?_
  have hjT : (j : ℝ) ≤ T := (Real.le_toNNReal_iff_coe_le hT).1 hj
  refine le_iSup_of_le (f := fun r : Set.Icc (0 : ℝ) T =>
    MeasurableSpace.comap (bmReal W r) inferInstance) ⟨(j : ℝ), j.2, hjT⟩ ?_
  have e : bmReal W (j : ℝ) = W j := by
    funext ω; simp [bmReal]
  simp only [e, le_refl]

/-! ## Non-vacuity on the constructed Brownian motion -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the representation theorem on `bmPath`.** Every
square-integrable `Y` measurable with respect to `σ(W_r : 0 ≤ r ≤ T)` (up to null sets) is
`E[Y] + ∫_0^T H dW` a.s. for the natural filtration.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepMonetarism.mrep_representation_bmPath). -/
theorem mrep_representation_bmPath {T : ℝ} (hT : 0 ≤ T) {Y : (ℕ → ℝ) → ℝ}
    (hY2 : MemLp Y 2 gaussSeq) (hYm : AEStronglyMeasurable[mrepNat bmPath T] Y gaussSeq) :
    ∃ H, MRepIntegrand gaussSeq (bmFiltrationReal bmPath measurable_bmPath) H 0 T ∧
      Y =ᵐ[gaussSeq] fun ω => (∫ ω, Y ω ∂gaussSeq)
        + mrepInt gaussSeq (bmFiltrationReal bmPath measurable_bmPath) bmPath H 0 T ω :=
  mrep_representation isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) continuous_bmPath
    (mrep_bmFiltrationReal_le measurable_bmPath hT) hY2 hYm

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the martingale representation on `bmPath`.** Every
martingale of the natural filtration of `bmPath` with `M_T ∈ L²` is
`M_t = E[M_T] + ∫_0^t H dW` a.s., `t ∈ [0, T]`, one `H`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepMonetarism.mrep_martingale_bmPath). -/
theorem mrep_martingale_bmPath {T : ℝ} (hT : 0 ≤ T) {M : ℝ → (ℕ → ℝ) → ℝ}
    (hM : Martingale M (bmFiltrationReal bmPath measurable_bmPath) gaussSeq)
    (hM2 : MemLp (M T) 2 gaussSeq) :
    ∃ H, MRepIntegrand gaussSeq (bmFiltrationReal bmPath measurable_bmPath) H 0 T ∧
      ∀ t ∈ Set.Icc 0 T, M t =ᵐ[gaussSeq] fun ω => (∫ ω, M T ω ∂gaussSeq)
        + mrepInt gaussSeq (bmFiltrationReal bmPath measurable_bmPath) bmPath H 0 t ω :=
  mrep_martingale isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) continuous_bmPath
    (mrep_bmFiltrationReal_le measurable_bmPath hT) hM hM2

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: a discontinuous functional.** The digital payoff
`1{W_T > 0}` on `bmPath` is `E[1{W_T > 0}] + ∫_0^T H dW` a.s. for some `H` in the extended class
(no mean-square continuity of `H` is claimed).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepMonetarism.mrep_indicator_bmPath). -/
theorem mrep_indicator_bmPath {T : ℝ} (hT : 0 ≤ T) :
    ∃ H, MRepIntegrand gaussSeq (bmFiltrationReal bmPath measurable_bmPath) H 0 T ∧
      (fun ω => (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) (bmReal bmPath T ω))
        =ᵐ[gaussSeq] fun ω =>
          (∫ ω, (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) (bmReal bmPath T ω) ∂gaussSeq)
          + mrepInt gaussSeq (bmFiltrationReal bmPath measurable_bmPath) bmPath H 0 T ω := by
  have : IsProbabilityMeasure gaussSeq :=
    isPreBrownianReal_bmPath.isGaussianProcess.isProbabilityMeasure
  have hm : Measurable[mrepNat bmPath T] (bmReal bmPath T) :=
    measurable_iff_comap_le.2 (le_iSup_of_le (f := fun r : Set.Icc (0 : ℝ) T =>
      MeasurableSpace.comap (bmReal bmPath r) inferInstance) ⟨T, hT, le_rfl⟩ le_rfl)
  have hYm : Measurable[mrepNat bmPath T]
      (fun ω => (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) (bmReal bmPath T ω)) :=
    (measurable_const.indicator measurableSet_Ioi).comp hm
  have hY2 : MemLp (fun ω => (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ))
      (bmReal bmPath T ω)) 2 gaussSeq :=
    memLp_of_bound (C := 1) (hYm.mono (mrepNat_le measurable_bmPath T) le_rfl) fun ω => by
      by_cases h : bmReal bmPath T ω ∈ Set.Ioi (0 : ℝ) <;> simp [h]
  exact mrep_representation_bmPath hT hY2 hYm.aestronglyMeasurable

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `W_T² = T + ∫_0^T 2W dW`, and the representation is
unique.** On `bmPath`, `T > 0`: `2W` (jointly measurable, mean-square continuous) represents
`W_T²` with constant `T`; any `(c, H)` in the extended class representing `W_T²` has `c = T` and
`H = 2W` `dt × dP`-a.e. on `(0, T] × Ω`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepMonetarism.mrep_sq_bmPath). -/
theorem mrep_sq_bmPath {T : ℝ} (hT : 0 < T) :
    MRepIntegrand gaussSeq (bmFiltrationReal bmPath measurable_bmPath)
        (fun u ω => 2 * bmReal bmPath u ω) 0 T
      ∧ (fun ω => bmReal bmPath T ω ^ 2) =ᵐ[gaussSeq] (fun ω => T + mrepInt gaussSeq
          (bmFiltrationReal bmPath measurable_bmPath) bmPath
          (fun u ω => 2 * bmReal bmPath u ω) 0 T ω)
      ∧ ∀ (c : ℝ) (H : ℝ → (ℕ → ℝ) → ℝ),
        MRepIntegrand gaussSeq (bmFiltrationReal bmPath measurable_bmPath) H 0 T →
        (fun ω => bmReal bmPath T ω ^ 2) =ᵐ[gaussSeq] (fun ω => c + mrepInt gaussSeq
          (bmFiltrationReal bmPath measurable_bmPath) bmPath H 0 T ω) →
        c = T ∧ Function.uncurry H =ᵐ[mrepMeasure gaussSeq 0 T]
          Function.uncurry fun u ω => 2 * bmReal bmPath u ω := by
  have hB := isPreBrownianReal_bmPath
  have hW := measurable_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB hW
  have : IsProbabilityMeasure gaussSeq := hB.isGaussianProcess.isProbabilityMeasure
  have hX := itoProcess_bm (t := T) hB hW h𝓕 le_rfl
  have hK : MSIntegrand gaussSeq (bmFiltrationReal bmPath measurable_bmPath)
      (fun u ω => 2 * bmReal bmPath u ω) 0 T :=
    Cochrane.ZeroBound.TidyR7ItoBondStep.MSIntegrand.const_mul (hX.toMS hB hW h𝓕 le_rfl) 2
  have hKm : Measurable (Function.uncurry fun u ω => 2 * bmReal bmPath u ω) :=
    (mrep_measurable_bm hW continuous_bmPath).const_mul 2
  have hag := mrep_agree hB hW h𝓕 le_rfl hK hKm
  have hito := ito_formula_pathwise hB hW h𝓕 le_rfl hT hX
    (ae_of_all _ fun ω => (continuous_bmReal (continuous_bmPath ω)).continuousOn)
    (f := fun x => x ^ 2) (f' := fun x => 2 * x) (f'' := fun _ => 2)
    (fun x => by simpa using hasDerivAt_pow 2 x)
    (fun x => by simpa using (hasDerivAt_id' x).const_mul 2)
    continuous_const (L := 2) (fun _ => by norm_num)
  have hrep : (fun ω => bmReal bmPath T ω ^ 2) =ᵐ[gaussSeq] (fun ω => T + mrepInt gaussSeq
      (bmFiltrationReal bmPath measurable_bmPath) bmPath
      (fun u ω => 2 * bmReal bmPath u ω) 0 T ω) := by
    filter_upwards [hito, hag.2] with ω h1 h2
    have w0 : bmReal bmPath 0 ω = 0 := by simp [bmReal, bmPath_zero]
    have e1 : (fun u => 2 * bmReal bmPath u ω * 0 + 2 / 2 * (1 * 1)) = fun _ => (1 : ℝ) :=
      funext fun _ => by ring
    have e2 : (fun u ω => 2 * bmReal bmPath u ω * 1) = fun u ω => 2 * bmReal bmPath u ω :=
      funext fun _ => funext fun _ => mul_one _
    rw [e1, e2, w0] at h1
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at h1
    rw [h2]
    norm_num at h1
    linarith
  refine ⟨hag.1, hrep, fun c H hH hc => ?_⟩
  have h := mrep_unique hB hW h𝓕 hH hag.1 (hc.symm.trans hrep)
  exact h

/-! ## The extended integral up to null sets -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the extended integral depends only on the
`dt × dP`-class of the integrand.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepMonetarism.mrepInt_congr_ae). -/
theorem mrepInt_congr_ae (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {s t : ℝ} (hs : 0 ≤ s) {H H' : ℝ → Ω → ℝ}
    (hH : MRepIntegrand P 𝓕 H s t) (hH' : MRepIntegrand P 𝓕 H' s t)
    (h : Function.uncurry H =ᵐ[mrepMeasure P s t] Function.uncurry H') :
    mrepInt P 𝓕 W H s t =ᵐ[P] mrepInt P 𝓕 W H' s t := by
  have h0 := mrepInt_isometry_sub hB hW h𝓕 hs hH hH'
  have hz : ∫ x, (Function.uncurry H x - Function.uncurry H' x) ^ 2 ∂mrepMeasure P s t = 0 := by
    rw [← integral_zero (ℝ × Ω) ℝ]
    refine integral_congr_ae ?_
    filter_upwards [h] with x hx
    simp [hx]
  rw [hz] at h0
  have hi := ((memLp_mrepInt hB hW h𝓕 hs hH).sub (memLp_mrepInt hB hW h𝓕 hs hH')).integrable_sq
  have h1 := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).1 h0
  filter_upwards [h1] with ω hω
  simp only [Pi.sub_apply, Pi.zero_apply, pow_eq_zero_iff two_ne_zero, sub_eq_zero] at hω
  exact hω

end Cochrane.ZeroBound.TidyR13MRepMonetarism
