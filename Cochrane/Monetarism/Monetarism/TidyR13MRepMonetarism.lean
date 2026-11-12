/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR13MRepTheorem
import Monetarism.TidyR12SDEGBM
import Monetarism.TidyR12SDEMonetary

/-!
# Martingale representation for the monetary model: every SDF martingale is an Itô integral

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34) (Track 3, chunk B6, item 4). The book writes
`Λ/P`, `B`, `M` as diffusions `dX = (·)dt + σ_X X dW` driven by one Brownian motion. On the
Brownian filtration this loses no martingale: by `TidyR13MRepTheorem.mrep_martingale` every
square-integrable martingale (an SDF `Λ` with zero real rate, a discounted nominal SDF, the
martingale part of `B` or `M`) is `X_0 + ∫ H dW`, with `H` unique up to `dt × dP`-null sets and
in general only in the `L²` closure of mean-square continuous integrands.

What this gives for the corrected (1.32) step (`TidyR12SDEMonetary.ItoMonetaryModelMS`, which
needs `Λ/P` with a mean-square continuous diffusion): `mrep_itoProcessMS_iff` shows that a
square-integrable martingale on the Brownian filtration is a zero-drift `ItoProcessMS` with
diffusion `G` (`G` jointly measurable and mean-square continuous) **iff** its representing
integrand equals `G` `dt × dP`-a.e. So the corrected step covers exactly the martingales whose
representing integrand has a mean-square continuous version. The representation itself holds for
every square-integrable martingale.

## Main results

* `mrep_bmFiltrationReal_le`: the natural filtration satisfies `𝓕_T ⊆ 𝓖_T`.
* On the constructed motion `TidyR7BrownianExist.bmPath`: `mrep_representation_bmPath`,
  `mrep_martingale_bmPath` (the theorems hold with no extra hypotheses);
  `mrep_indicator_bmPath` (`1{W_T > 0}`, a discontinuous functional, is `E[·] + ∫_0^T H dW`);
  `mrep_sq_bmPath` (`W_T² = T + ∫_0^T 2W dW`, and every representation has constant `T` and
  integrand `2W` a.e.).
* `mrep_sdf_gbm_bmPath` (**economics instance**): the positive SDF
  `Λ_t = exp(σW_t − σ²t/2)` has `Λ_T = 1 + ∫_0^T σΛ dW`, and every representation of `Λ_T` has
  constant `1` and loading `σΛ` a.e.: the SDF's innovation loading `σ_Λ` is identified.
* `mrepInt_congr_ae`, `mrep_itoProcessMS_iff` (which martingales the corrected (1.32) step covers).
-/

namespace Cochrane.Monetarism.TidyR13MRepMonetarism

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianExist Cochrane.Monetarism.TidyR7BrownianSchauder
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoIntegral Cochrane.Monetarism.TidyR7ItoUnbounded
  Cochrane.Monetarism.TidyR7ItoProductRule Cochrane.Monetarism.TidyR9ItoFormula
  Cochrane.Monetarism.TidyR12SDEProcess Cochrane.Monetarism.TidyR12SDEGBM
  Cochrane.Monetarism.TidyR13MRepIntegral Cochrane.Monetarism.TidyR13MRepCutoff
  Cochrane.Monetarism.TidyR13MRepOneStep Cochrane.Monetarism.TidyR13MRepDensity
  Cochrane.Monetarism.TidyR13MRepTheorem Cochrane.Monetarism.TidyR7ItoProducts
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ}

/-! ## The natural filtration -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the natural filtration satisfies the hypothesis
`𝓕_T ⊆ 𝓖_T`** of `TidyR13MRepTheorem.mrep_representation`, `T ≥ 0`. -/
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
`E[Y] + ∫_0^T H dW` a.s. for the natural filtration. -/
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
`M_t = E[M_T] + ∫_0^t H dW` a.s., `t ∈ [0, T]`, one `H`. -/
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
(no mean-square continuity of `H` is claimed). -/
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
`H = 2W` `dt × dP`-a.e. on `(0, T] × Ω`. -/
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
    Cochrane.Monetarism.TidyR7ItoBondStep.MSIntegrand.const_mul (hX.toMS hB hW h𝓕 le_rfl) 2
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

/-! ## The SDF: innovation loading identified -/

/-- **Cochrane (2023), A1 §1.6, (1.31)–(1.33), pp. 567–568: the exponential SDF is an Itô
integral with a unique loading.** On `bmPath` let `Λ_t = exp(σ(W_t − W_0) − σ²t/2)`
(`TidyR12SDEGBM.gbm` with `ξ = 1`, `κ = −σ²/2`), `T ≥ 0`. Then `Λ_T > 0`, `Λ_T ∈ L²`,
`Λ_T = 1 + ∫_0^T σΛ dW` a.s. with `σΛ` in the extended class, and every representation
`Λ_T = c + ∫_0^T H dW` has `c = 1` and `H = σΛ` `dt × dP`-a.e.: the innovation loading
`σ_Λ Λ` of the SDF is identified by the martingale `Λ` alone.
Uses `TidyR12SDEGBM.expMart_eq` for the existence part. -/
theorem mrep_sdf_gbm_bmPath (σ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    (∀ ω, 0 < gbm bmPath (fun _ => 1) 0 (-(σ ^ 2 / 2)) σ T ω)
      ∧ MemLp (gbm bmPath (fun _ => 1) 0 (-(σ ^ 2 / 2)) σ T) 2 gaussSeq
      ∧ MRepIntegrand gaussSeq (bmFiltrationReal bmPath measurable_bmPath)
          (fun u ω => σ * gbm bmPath (fun _ => 1) 0 (-(σ ^ 2 / 2)) σ u ω) 0 T
      ∧ gbm bmPath (fun _ => 1) 0 (-(σ ^ 2 / 2)) σ T =ᵐ[gaussSeq] (fun ω => 1 + mrepInt
          gaussSeq (bmFiltrationReal bmPath measurable_bmPath) bmPath
          (fun u ω => σ * gbm bmPath (fun _ => 1) 0 (-(σ ^ 2 / 2)) σ u ω) 0 T ω)
      ∧ ∀ (c : ℝ) (H : ℝ → (ℕ → ℝ) → ℝ),
        MRepIntegrand gaussSeq (bmFiltrationReal bmPath measurable_bmPath) H 0 T →
        gbm bmPath (fun _ => 1) 0 (-(σ ^ 2 / 2)) σ T =ᵐ[gaussSeq] (fun ω => c + mrepInt
          gaussSeq (bmFiltrationReal bmPath measurable_bmPath) bmPath H 0 T ω) →
        c = 1 ∧ Function.uncurry H =ᵐ[mrepMeasure gaussSeq 0 T]
          Function.uncurry fun u ω => σ * gbm bmPath (fun _ => 1) 0 (-(σ ^ 2 / 2)) σ u ω := by
  have hB := isPreBrownianReal_bmPath
  have hW := measurable_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB hW
  have : IsProbabilityMeasure gaussSeq := hB.isGaussianProcess.isProbabilityMeasure
  have hξ2 : MemLp (fun _ : ℕ → ℝ => (1 : ℝ)) 2 gaussSeq := memLp_const 1
  have hξ : StronglyMeasurable[bmFiltrationReal bmPath measurable_bmPath 0]
      (fun _ : ℕ → ℝ => (1 : ℝ)) := stronglyMeasurable_const
  have hG := gbm_ms (κ := -(σ ^ 2 / 2)) (σ := σ) hB hW h𝓕 le_rfl hξ2 hξ T
  have hK := Cochrane.Monetarism.TidyR7ItoBondStep.MSIntegrand.const_mul hG σ
  have hKm : Measurable (Function.uncurry fun u ω =>
      σ * gbm bmPath (fun _ => 1) 0 (-(σ ^ 2 / 2)) σ u ω) := by
    have hm := mrep_measurable_bm hW continuous_bmPath
    have h0 : Measurable fun x : ℝ × (ℕ → ℝ) => bmReal bmPath 0 x.2 := (hW _).comp measurable_snd
    change Measurable fun x : ℝ × (ℕ → ℝ) => σ * (1 * Real.exp (-(σ ^ 2 / 2) * (x.1 - 0)
      + σ * (bmReal bmPath x.1 x.2 - bmReal bmPath 0 x.2)))
    exact measurable_const.mul (measurable_const.mul (Real.measurable_exp.comp
      ((measurable_const.mul (measurable_fst.sub measurable_const)).add
        (measurable_const.mul (hm.sub h0)))))
  have hag := mrep_agree hB hW h𝓕 le_rfl hK hKm
  have hrep : gbm bmPath (fun _ => 1) 0 (-(σ ^ 2 / 2)) σ T =ᵐ[gaussSeq] (fun ω => 1 + mrepInt
      gaussSeq (bmFiltrationReal bmPath measurable_bmPath) bmPath
      (fun u ω => σ * gbm bmPath (fun _ => 1) 0 (-(σ ^ 2 / 2)) σ u ω) 0 T ω) := by
    filter_upwards [expMart_eq (σ := σ) hB hW h𝓕 le_rfl hξ2 hξ hT, hag.2] with ω h1 h2
    rw [gbm_self] at h1
    rw [h2, ← h1]
    ring
  refine ⟨gbm_pos (fun _ => one_pos) T, memLp_gbm hB hW h𝓕 le_rfl hξ2 hξ hT, hag.1, hrep,
    fun c H hH hc => ?_⟩
  have h := mrep_unique hB hW h𝓕 hH hag.1 (hc.symm.trans hrep)
  exact h

/-! ## Which martingales the corrected (1.32) step covers -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the extended integral depends only on the
`dt × dP`-class of the integrand. -/
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

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: which martingales the corrected (1.32) step
covers.** Let `M_t = c + ∫_0^t H dW` a.s. for `t ∈ [0, T]` (`H` in the extended class; e.g. from
`TidyR13MRepTheorem.mrep_martingale`), `M` adapted, and let `G` be jointly measurable and
mean-square continuous on `[0, T]`. Then `M` is a zero-drift `TidyR12SDEProcess.ItoProcessMS`
with diffusion `G` on `[0, T]` (the form `TidyR12SDEMonetary.ItoMonetaryModelMS` requires of
`Λ/P`) **iff** `H = G` `dt × dP`-a.e. on `(0, T] × Ω`. -/
theorem mrep_itoProcessMS_iff (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {T c : ℝ} (hT : 0 ≤ T) {M H G : ℝ → Ω → ℝ}
    (hH : MRepIntegrand P 𝓕 H 0 T)
    (hrep : ∀ t ∈ Set.Icc 0 T, M t =ᵐ[P] fun ω => c + mrepInt P 𝓕 W H 0 t ω)
    (hMa : ∀ u ∈ Set.Icc 0 T, StronglyMeasurable[𝓕 u] (M u)) (hG : MSIntegrand P 𝓕 G 0 T)
    (hGm : Measurable (Function.uncurry G)) :
    ItoProcessMS P 𝓕 W M (fun _ _ => 0) G 0 T ↔
      Function.uncurry H =ᵐ[mrepMeasure P 0 T] Function.uncurry G := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hag := fun {u : ℝ} (hu : u ∈ Set.Icc 0 T) =>
    mrep_agree hB hW h𝓕 le_rfl (hG.mono le_rfl hu.2) hGm
  have hM0 : M 0 =ᵐ[P] fun _ => c := by
    filter_upwards [hrep 0 ⟨le_rfl, hT⟩, mrepInt_self hB hW h𝓕 le_rfl (mrep_mono hH le_rfl hT)]
      with ω h1 h2
    rw [h1, h2]
    simp
  have hdt : ∀ u, dtInt P 𝓕 (fun _ _ => (0 : ℝ)) 0 u =ᵐ[P] 0 := fun u =>
    dtInt_of_eq_zero fun _ _ _ => rfl
  constructor
  · intro hX
    have hT' : T ∈ Set.Icc 0 T := ⟨hT, le_rfl⟩
    refine (mrep_unique (c := c) (c' := c) hB hW h𝓕 hH (hag hT').1 ?_).2
    filter_upwards [hrep T hT', hX.eq T hT', hM0, hdt T, (hag hT').2] with ω e1 e2 e3 e4 e5
    rw [← e1, e2, e3, e4, e5]
    simp
  · intro hHG
    refine ⟨hMa, (memLp_const c).ae_eq hM0.symm, mrep_ms_zero, hG, fun u hu => ?_⟩
    have hHu := mrep_mono hH le_rfl hu.2
    have hGu := (hag hu).1
    have hc := mrepInt_congr_ae hB hW h𝓕 le_rfl hHu hGu
      (ae_mono (mrepMeasure_mono le_rfl hu.2) hHG)
    filter_upwards [hrep u hu, hM0, hdt u, hc, (hag hu).2] with ω e1 e2 e3 e4 e5
    rw [e1, e2, e3, e4, e5]
    simp

end Cochrane.Monetarism.TidyR13MRepMonetarism
