/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.TidyR7ItoDiscountFactorCex

/-!
# The converse: a martingale `ΛW` forces the coefficient identity

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1.5, p. 566 (the basic
pricing relation `E_t[d(Λ_tW_t)] = 0`, written on the coefficients as
`E_t[dΛ/Λ + dW/W + dΛdW/(ΛW)] = 0`, and `E_t[d(Λ_tV_t)] = −Λ_ts_t dt`), and Chapter 3, §3.6,
(3.35), p. 74. `TidyR7ItoDiscountFactor.ItoDiscountModel.martingale_W` proved: the coefficient
identity `Λ a_W + W a_Λ + σ_Λσ_W = 0` makes `ΛW` a martingale. This module proves the converse,
and the corresponding converse of `TidyR7ItoDiscountFactor.ItoDiscountModel.step`.

## The argument (uniqueness of the drift of a continuous semimartingale, in `L²`)

By Itô's product rule, `E_r[Λ_uW_u − Λ_rW_r] = E_r[∫_r^u D dv]` with the drift
`D = Λ a_W + W a_Λ + σ_Λσ_W` (`condExp_incr_eq_condExp_dtInt`). If `ΛW` is a martingale, then
for every `A ∈ 𝓕_r` and `u > r`, `0 = E[1_A ∫_r^u D] = ∫_r^u E[1_A D_v] dv`
(`integral_mul_dtInt`: Riemann sums and the mean-square limit), the function
`v ↦ E[1_A D_v]` is continuous (`continuousOn_integral_mul`, mean-square continuity), so it
vanishes at `v = r` (`eq_zero_of_integral_eq_zero`), and `D_r` is `𝓕_r`-measurable, so `D_r = 0`
a.s. No path regularity, no Doob inequality, no boundedness of `Λ`, `W` is needed.

## Main results

* `ae_zero_of_condExp_dtInt` (the core): a mean-square continuous adapted `D` with
  `E_r[∫_r^u D] = 0` for all `s ≤ r < u ≤ t` vanishes a.s. at every `r ∈ [s, t)`;
  `dtInt_ae_zero`, its converse.
* `drift_ae_zero_of_martingale` (**the converse asked for**): if `ΛW` is a martingale on
  `[s, t]`, then `Λ a_W + W a_Λ + σ_Λσ_W = 0` a.s. at every date of `[s, t)`;
  `martingale_iff_drift_ae_zero`: **iff**; `drift_pathwise_zero_of_martingale`: with a.s.
  continuous paths of `Λ`, `W`, a.s. the identity holds at **every** date of `[s, t]`.
* `pricing_ae_of_step`: the converse of `ItoDiscountModel.step`: if
  `E_r[Λ_uV_u − Λ_rV_r] = −E_r[∫_r^u Λs]` for all `s ≤ r < u ≤ t`, then
  `Λ a_V + V a_Λ + σ_Λσ_V = −Λ s` a.s. at every date of `[s, t)`.
* `w_drift_of_martingale`: the instance on economy W of `TidyR7ItoDiscountFactorCex`.

The identity can only be recovered almost surely: the coefficients of an Itô process are only
determined up to null sets, so "for every state" (the form of `ItoDiscountModel.pricing`) is
not a consequence of the martingale property.
-/

namespace Cochrane.Generality.TidyR9MartingaleDrift

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Generality.TidyR7StieltjesSums Cochrane.Generality.TidyR7BrownianTools
  Cochrane.Generality.TidyR7BrownianQV Cochrane.Generality.TidyR7ItoL2
  Cochrane.Generality.TidyR7ItoSums Cochrane.Generality.TidyR7ItoIntegral
  Cochrane.Generality.TidyR7ItoUnbounded Cochrane.Generality.TidyR7ItoProducts
  Cochrane.Generality.TidyR7ItoProcess Cochrane.Generality.TidyR7ItoProductRule
  Cochrane.Generality.TidyR7ItoBondStep Cochrane.Generality.TidyR7ItoDiscountFactor
  Cochrane.Generality.TidyR7ItoDiscountFactorCex Cochrane.Generality.TidyR7BrownianExist
  Cochrane.Generality.TidyR7BrownianSchauder
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → ℝ} {s t : ℝ}

/-! ## Three lemmas on mean-square continuous processes -/

/-- Cochrane (2023), A1.5, p. 566 (the tool for `E_t[d(ΛW)] = 0` ⇒ coefficients): for a
mean-square continuous `D` on `[s, t]` and a bounded measurable `G`, `v ↦ E[G D_v]` is
continuous on `[s, t]` (`|E[G(D_w − D_v)]| ≤ C E|D_w − D_v| ≤ C √E[(D_w − D_v)²]`). -/
theorem continuousOn_integral_mul [IsProbabilityMeasure P] {D : ℝ → Ω → ℝ}
    (hD : MSIntegrand P 𝓕 D s t) {G : Ω → ℝ} (hG : Measurable G) {C : ℝ}
    (hGb : ∀ ω, |G ω| ≤ C) :
    ContinuousOn (fun v => ∫ ω, G ω * D v ω ∂P) (Set.Icc s t) := by
  intro v hv
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hK0 : 0 < |C| + 1 := by positivity
  have hη : 0 < ε / (2 * (|C| + 1)) := by positivity
  obtain ⟨δ, hδ, hc⟩ := hD.cont ((ε / (2 * (|C| + 1))) ^ 2) (by positivity)
  refine ⟨δ, hδ, fun {w} hw hwv => ?_⟩
  have hw2 := hD.memLp w hw
  have hv2 := hD.memLp v hv
  have hsq : (∫ ω, |D w ω - D v ω| ∂P) ^ 2 ≤ ∫ ω, (D w ω - D v ω) ^ 2 ∂P :=
    sq_integral_abs_le (hw2.sub hv2)
  have hle : ∫ ω, (D w ω - D v ω) ^ 2 ∂P ≤ (ε / (2 * (|C| + 1))) ^ 2 :=
    hc w hw v hv (by rw [Real.dist_eq] at hwv; exact hwv.le)
  have h0 : 0 ≤ ∫ ω, |D w ω - D v ω| ∂P := integral_nonneg fun ω => abs_nonneg _
  have h1 : ∫ ω, |D w ω - D v ω| ∂P ≤ ε / (2 * (|C| + 1)) := by nlinarith
  have hGm : AEStronglyMeasurable G P := hG.aestronglyMeasurable
  have hGb' : ∀ᵐ ω ∂P, ‖G ω‖ ≤ |C| := ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]; exact (hGb ω).trans (le_abs_self C)
  have iw : Integrable (fun ω => G ω * D w ω) P := (hw2.integrable one_le_two).bdd_mul hGm hGb'
  have iv : Integrable (fun ω => G ω * D v ω) P := (hv2.integrable one_le_two).bdd_mul hGm hGb'
  have idiff : Integrable (fun ω => |D w ω - D v ω|) P :=
    ((hw2.sub hv2).integrable one_le_two).abs
  rw [Real.dist_eq, ← integral_sub iw iv]
  calc |∫ ω, (G ω * D w ω - G ω * D v ω) ∂P|
      ≤ ∫ ω, |G ω * D w ω - G ω * D v ω| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (|C| + 1) * |D w ω - D v ω| ∂P := by
        refine integral_mono_of_nonneg (ae_of_all _ fun ω => abs_nonneg _)
          (idiff.const_mul _) (ae_of_all _ fun ω => ?_)
        simp only
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_right ((hGb ω).trans ((le_abs_self C).trans (by linarith)))
          (abs_nonneg _)
    _ = (|C| + 1) * ∫ ω, |D w ω - D v ω| ∂P := integral_const_mul _ _
    _ ≤ (|C| + 1) * (ε / (2 * (|C| + 1))) := mul_le_mul_of_nonneg_left h1 hK0.le
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-- Cochrane (2023), A1.5, p. 566 (`E_t ∫ = ∫ E_t` for the drift): for a mean-square continuous
`D` on `[s, t]`, `s < t`, and a bounded measurable `G`,
`E[G ∫_s^t D_v dv] = ∫_s^t E[G D_v] dv`, with the mean-square time integral
`TidyR7ItoProducts.dtInt` (Riemann sums converge in `L²` and in expectation). -/
theorem integral_mul_dtInt [IsProbabilityMeasure P] {D : ℝ → Ω → ℝ} (hst : s < t)
    (hD : MSIntegrand P 𝓕 D s t) {G : Ω → ℝ} (hG : Measurable G) {C : ℝ}
    (hGb : ∀ ω, |G ω| ≤ C) :
    ∫ ω, G ω * dtInt P 𝓕 D s t ω ∂P = ∫ v in s..t, ∫ ω, G ω * D v ω ∂P := by
  have h1 := tendsto_integral_mul_of_L2Tendsto (L2Tendsto_dyadic_dt hst hD) hG hGb
  have h2 := tendsto_riemannSum (continuousOn_integral_mul hD hG hGb) (dyadic hst)
    (tendsto_mesh_dyadic hst)
  have hGm : AEStronglyMeasurable G P := hG.aestronglyMeasurable
  have hGb' : ∀ᵐ ω ∂P, ‖G ω‖ ≤ |C| := ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]; exact (hGb ω).trans (le_abs_self C)
  have e : ∀ k, ∫ ω, G ω * dtSum D (dyadic hst k) ω ∂P
      = riemannSum (dyadic hst k) (fun v => ∫ ω, G ω * D v ω ∂P) := fun k => by
    simp only [dtSum, riemannSum, Finset.mul_sum]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_mul_const]
      exact integral_congr_ae (ae_of_all _ fun ω => by ring)
    · intro i hi
      have hm := hD.memLp _ (t_mem _ (Finset.mem_range.1 hi).le)
      exact ((hm.integrable one_le_two).mul_const _).bdd_mul hGm hGb'
  exact tendsto_nhds_unique (h1.congr e) h2

/-- Cochrane (2023), A1.5, p. 566 (the last step of the converse): if `F` is continuous on
`[s, t]`, `s < t`, and `∫_s^u F = 0` for every `u ∈ (s, t]`, then `F(s) = 0`. -/
theorem eq_zero_of_integral_eq_zero {F : ℝ → ℝ} (hst : s < t)
    (hF : ContinuousOn F (Set.Icc s t)) (h0 : ∀ u ∈ Set.Ioc s t, ∫ v in s..u, F v = 0) :
    F s = 0 := by
  by_contra hne
  have hH : ContinuousOn (fun v => F s * F v) (Set.Icc s t) := continuousOn_const.mul hF
  have hHs : 0 < F s * F s := mul_self_pos.2 hne
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 (hH s ⟨le_rfl, hst.le⟩)
    (F s * F s / 2) (by linarith)
  have hsu : s < min t (s + δ / 2) := lt_min hst (by linarith)
  have hut : min t (s + δ / 2) ≤ t := min_le_left _ _
  have hbound : ∀ v ∈ Set.Icc s (min t (s + δ / 2)), F s * F s / 2 ≤ F s * F v := by
    intro v hv
    have hvI : v ∈ Set.Icc s t := ⟨hv.1, hv.2.trans hut⟩
    have hd : dist v s < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hv.1])]
      have := hv.2.trans (min_le_right _ _)
      linarith
    have := hball hvI hd
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.1]
  have hint : ∫ v in s..min t (s + δ / 2), F s * F v
      = F s * ∫ v in s..min t (s + δ / 2), F v := intervalIntegral.integral_const_mul _ _
  rw [h0 _ ⟨hsu, hut⟩, mul_zero] at hint
  have hmono : ∫ _ in s..min t (s + δ / 2), F s * F s / 2
      ≤ ∫ v in s..min t (s + δ / 2), F s * F v :=
    intervalIntegral.integral_mono_on hsu.le intervalIntegrable_const
      ((hH.mono (Set.Icc_subset_Icc le_rfl hut)).intervalIntegrable_of_Icc hsu.le) hbound
  rw [intervalIntegral.integral_const, smul_eq_mul, hint] at hmono
  have : 0 < (min t (s + δ / 2) - s) * (F s * F s / 2) := mul_pos (by linarith) (by linarith)
  linarith

/-! ## The core: a drift with zero conditional expectations vanishes -/

/-- **Cochrane (2023), A1.5, p. 566 (uniqueness of the drift): a mean-square continuous adapted
`D` on `[s, t]` with `E_r[∫_r^u D dv] = 0` a.s. for all `s ≤ r < u ≤ t` vanishes a.s. at every
date `r ∈ [s, t)`.** -/
theorem ae_zero_of_condExp_dtInt [IsProbabilityMeasure P] {D : ℝ → Ω → ℝ}
    (hD : MSIntegrand P 𝓕 D s t)
    (h : ∀ r u, s ≤ r → r < u → u ≤ t → P[dtInt P 𝓕 D r u | 𝓕 r] =ᵐ[P] 0) :
    ∀ r ∈ Set.Ico s t, D r =ᵐ[P] 0 := by
  intro r hr
  have hDr := hD.mono hr.1 le_rfl
  have hset : ∀ A, MeasurableSet[𝓕 r] A → ∫ ω in A, D r ω ∂P = 0 := by
    intro A hA
    have hA' : MeasurableSet A := 𝓕.le r A hA
    have hGm : Measurable (A.indicator (1 : Ω → ℝ)) := measurable_one.indicator hA'
    have hGb : ∀ ω, |A.indicator (1 : Ω → ℝ) ω| ≤ 1 := fun ω => by
      by_cases h : ω ∈ A <;> simp [h]
    have hGD : ∀ X : Ω → ℝ, ∫ ω, A.indicator (1 : Ω → ℝ) ω * X ω ∂P = ∫ ω in A, X ω ∂P :=
      fun X => by
        rw [← integral_indicator hA']
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        by_cases h : ω ∈ A <;> simp [h]
    have hF := continuousOn_integral_mul hDr hGm hGb
    have h0 : ∀ u ∈ Set.Ioc r t,
        ∫ v in r..u, ∫ ω, A.indicator (1 : Ω → ℝ) ω * D v ω ∂P = 0 := by
      intro u hu
      have hDru := hDr.mono le_rfl hu.2
      rw [← integral_mul_dtInt hu.1 hDru hGm hGb, hGD]
      have hi : Integrable (dtInt P 𝓕 D r u) P := (memLp_dtInt hDru).integrable one_le_two
      rw [← setIntegral_condExp (𝓕.le r) hi hA,
        setIntegral_congr_ae hA' ((h r u hr.1 hu.1 hu.2).mono fun ω hω _ => hω)]
      simp
    have := eq_zero_of_integral_eq_zero hr.2 hF h0
    rwa [hGD] at this
  have hDi : Integrable (D r) P := (hD.memLp r ⟨hr.1, hr.2.le⟩).integrable one_le_two
  have hmeas : StronglyMeasurable[𝓕 r] (D r) := hD.adapted r ⟨hr.1, hr.2.le⟩
  have h1 := ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le r) hDi (g := fun _ => (0 : ℝ))
    (fun _ _ _ => integrableOn_zero) (fun A hA _ => by rw [hset A hA]; simp)
    stronglyMeasurable_zero.aestronglyMeasurable
  rw [condExp_of_stronglyMeasurable (𝓕.le r) hmeas hDi] at h1
  exact h1.symm

/-- Cochrane (2023), A1.5, p. 566 (the direction of `ItoDiscountModel.martingale_W`, almost
surely): **a mean-square continuous `D` vanishing a.s. at every date of `[s, t)` has
`∫_s^t D = 0` a.s.** (every Riemann sum vanishes a.s.).
Generalises `TidyR7ItoProducts.dtInt_of_eq_zero` to almost surely. -/
theorem dtInt_ae_zero [IsFiniteMeasure P] {D : ℝ → Ω → ℝ} (hD : MSIntegrand P 𝓕 D s t)
    (h0 : ∀ u ∈ Set.Ico s t, D u =ᵐ[P] 0) : dtInt P 𝓕 D s t =ᵐ[P] 0 := by
  rcases lt_or_ge s t with hst | hts
  · have hL := L2Tendsto_dyadic_dt hst hD
    have he : ∀ k, dtSum D (dyadic hst k) =ᵐ[P] 0 := fun k => by
      have hall : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range (dyadic hst k).n,
          D ((dyadic hst k).t i) ω = 0 := by
        refine (Filter.eventually_all_finset _).2 fun i hi => ?_
        have hi' := Finset.mem_range.1 hi
        have hmem := t_mem (dyadic hst k) hi'.le
        have hlt : (dyadic hst k).t i < t := by
          have := (dyadic hst k).strictMono hi'
          rwa [(dyadic hst k).last] at this
        exact h0 _ ⟨hmem.1, hlt⟩
      filter_upwards [hall] with ω hω
      simp only [dtSum, riemannSum, Pi.zero_apply]
      exact Finset.sum_eq_zero fun i hi => by rw [hω i hi, zero_mul]
    have hz : L2Tendsto P (fun k => dtSum D (dyadic hst k)) 0 := by
      refine ⟨hL.1, MemLp.zero, tendsto_const_nhds.congr fun k => ?_⟩
      rw [integral_congr_ae ((he k).mono fun ω hω => by simp [hω] :
        (fun ω => (dtSum D (dyadic hst k) ω - (0 : Ω → ℝ) ω) ^ 2) =ᵐ[P] fun _ => (0 : ℝ))]
      simp
    exact ae_eq_of_L2Tendsto hL hz
  · rw [dtInt_of_le hts]

/-! ## The product `ΛW` -/

variable {Λ aΛ σΛ R aR σR : ℝ → Ω → ℝ} {CΛ CΛσ CR CRσ : ℝ}

/-- Cochrane (2023), A1.5, p. 566: **`E_s[Λ_tW_t − Λ_sW_s] = E_s[∫_s^t D du]` with the drift
`D = Λ a_W + W a_Λ + σ_Λσ_W`** of `ΛW` (Itô's product rule
`TidyR7ItoProductRule.condExp_product_rule`, the three `dt`-terms combined), `0 ≤ s < t`. -/
theorem condExp_incr_eq_condExp_dtInt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hΛ : ItoProcess P 𝓕 W Λ aΛ σΛ s t CΛ CΛσ) (hR : ItoProcess P 𝓕 W R aR σR s t CR CRσ) :
    P[fun ω => Λ t ω * R t ω - Λ s ω * R s ω | 𝓕 s] =ᵐ[P]
      P[dtInt P 𝓕 (fun u ω => Λ u ω * aR u ω + R u ω * aΛ u ω + σΛ u ω * σR u ω) s t
        | 𝓕 s] := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have G1 := MSIntegrand.mul_itoIntegrand (hΛ.toMS hB hW h𝓕 hs) hR.drift
  have G2 := MSIntegrand.mul_itoIntegrand (hR.toMS hB hW h𝓕 hs) hΛ.drift
  have I3 := itoIntegrand_mul hΛ.diff hR.diff
  have e3 := dtInt_ae_eq_integral hst.le (ItoIntegrand.toMS I3) I3.cont
  have a1 := dtInt_add G1 G2
  have a2 := dtInt_add (MSIntegrand.add G1 G2) (ItoIntegrand.toMS I3)
  refine (condExp_product_rule hB hW h𝓕 hs hst hΛ hR).trans (condExp_congr_ae ?_)
  filter_upwards [e3, a1, a2] with ω h3 h1 h2
  simp only [Pi.add_apply] at h1 h2
  linarith

/-- Cochrane (2023), A1.5, p. 566: the drift `Λ a_W + W a_Λ + σ_Λσ_W` of `ΛW` is a mean-square
continuous adapted integrand on `[s, t]`. -/
theorem msIntegrand_drift (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s)
    (hΛ : ItoProcess P 𝓕 W Λ aΛ σΛ s t CΛ CΛσ) (hR : ItoProcess P 𝓕 W R aR σR s t CR CRσ) :
    MSIntegrand P 𝓕 (fun u ω => Λ u ω * aR u ω + R u ω * aΛ u ω + σΛ u ω * σR u ω) s t := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact MSIntegrand.add (MSIntegrand.add (MSIntegrand.mul_itoIntegrand (hΛ.toMS hB hW h𝓕 hs)
    hR.drift) (MSIntegrand.mul_itoIntegrand (hR.toMS hB hW h𝓕 hs) hΛ.drift))
    (ItoIntegrand.toMS (itoIntegrand_mul hΛ.diff hR.diff))

/-- **Cochrane (2023), A1.5, p. 566: the converse of `E_t[d(ΛW)] = 0` ⇐ coefficients.** If
`Λ` and the cumulative return `W` (here `R`) are Itô processes on `[s, t]`, `0 ≤ s`, and `ΛR`
is a martingale on `[s, t]` (`E_r[Λ_uR_u] = Λ_rR_r` a.s. for `s ≤ r < u ≤ t`), then at every
date `u ∈ [s, t)`, a.s. `Λ_u a_R(u) + R_u a_Λ(u) + σ_Λ(u)σ_R(u) = 0`: the book's
`E_t[dΛ/Λ + dW/W + dΛdW/(ΛW)] = 0` on the coefficients
(`TidyR7ItoDiscountFactor.pricing_rate_iff`). The converse of
`TidyR7ItoDiscountFactor.ItoDiscountModel.martingale_W`. -/
theorem drift_ae_zero_of_martingale (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s)
    (hΛ : ItoProcess P 𝓕 W Λ aΛ σΛ s t CΛ CΛσ) (hR : ItoProcess P 𝓕 W R aR σR s t CR CRσ)
    (hmart : ∀ r u, s ≤ r → r < u → u ≤ t →
      P[fun ω => Λ u ω * R u ω | 𝓕 r] =ᵐ[P] fun ω => Λ r ω * R r ω) :
    ∀ u ∈ Set.Ico s t,
      (fun ω => Λ u ω * aR u ω + R u ω * aΛ u ω + σΛ u ω * σR u ω) =ᵐ[P] 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ae_zero_of_condExp_dtInt (msIntegrand_drift hB hW h𝓕 hs hΛ hR)
    fun r u hsr hru hut => ?_
  have hr0 : 0 ≤ r := hs.trans hsr
  have hΛr := itoProcess_restrict hB hW h𝓕 hs hΛ hsr hru.le hut
  have hRr := itoProcess_restrict hB hW h𝓕 hs hR hsr hru.le hut
  have h1 := condExp_incr_eq_condExp_dtInt hB hW h𝓕 hr0 hru hΛr hRr
  have iu : Integrable (fun ω => Λ u ω * R u ω) P :=
    (hΛr.memLp hB hW h𝓕 hr0 ⟨hru.le, le_rfl⟩).integrable_mul
      (hRr.memLp hB hW h𝓕 hr0 ⟨hru.le, le_rfl⟩)
  have ir : Integrable (fun ω => Λ r ω * R r ω) P :=
    (hΛr.memLp hB hW h𝓕 hr0 ⟨le_rfl, hru.le⟩).integrable_mul
      (hRr.memLp hB hW h𝓕 hr0 ⟨le_rfl, hru.le⟩)
  have hYr : StronglyMeasurable[𝓕 r] (fun ω => Λ r ω * R r ω) :=
    (hΛr.adapted r ⟨le_rfl, hru.le⟩).mul (hRr.adapted r ⟨le_rfl, hru.le⟩)
  have h2 := condExp_sub (m := 𝓕 r) iu ir
  have h3 : P[fun ω => Λ r ω * R r ω | 𝓕 r] = fun ω => Λ r ω * R r ω :=
    condExp_of_stronglyMeasurable (𝓕.le r) hYr ir
  filter_upwards [h1, h2, hmart r u hsr hru hut] with ω e1 e2 e3
  have e2' : P[fun ω => Λ u ω * R u ω - Λ r ω * R r ω | 𝓕 r] ω =
      P[fun ω => Λ u ω * R u ω | 𝓕 r] ω - Λ r ω * R r ω := by
    rw [show (fun ω => Λ u ω * R u ω - Λ r ω * R r ω) =
      (fun ω => Λ u ω * R u ω) - fun ω => Λ r ω * R r ω from rfl, e2, Pi.sub_apply, h3]
  rw [← e1, e2', e3, sub_self, Pi.zero_apply]

/-- **Cochrane (2023), A1.5, p. 566: `Λ W` is a martingale on `[s, t]` iff its drift vanishes
a.s. at every date of `[s, t)`.** For Itô processes `Λ`, `R` on `[s, t]`, `0 ≤ s`:
`E_r[Λ_uR_u] = Λ_rR_r` a.s. for all `s ≤ r ≤ u ≤ t` iff
`Λ a_R + R a_Λ + σ_Λσ_R = 0` a.s. at every `u ∈ [s, t)`. -/
theorem martingale_iff_drift_ae_zero (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s)
    (hΛ : ItoProcess P 𝓕 W Λ aΛ σΛ s t CΛ CΛσ) (hR : ItoProcess P 𝓕 W R aR σR s t CR CRσ) :
    (∀ r u, s ≤ r → r ≤ u → u ≤ t →
      P[fun ω => Λ u ω * R u ω | 𝓕 r] =ᵐ[P] fun ω => Λ r ω * R r ω) ↔
    ∀ u ∈ Set.Ico s t,
      (fun ω => Λ u ω * aR u ω + R u ω * aΛ u ω + σΛ u ω * σR u ω) =ᵐ[P] 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  constructor
  · intro h
    exact drift_ae_zero_of_martingale hB hW h𝓕 hs hΛ hR fun r u h1 h2 h3 => h r u h1 h2.le h3
  · intro h0 r u hsr hru hut
    have hr0 : 0 ≤ r := hs.trans hsr
    have hΛr := itoProcess_restrict hB hW h𝓕 hs hΛ hsr hru hut
    have hRr := itoProcess_restrict hB hW h𝓕 hs hR hsr hru hut
    have ir : Integrable (fun ω => Λ r ω * R r ω) P :=
      (hΛr.memLp hB hW h𝓕 hr0 ⟨le_rfl, hru⟩).integrable_mul
        (hRr.memLp hB hW h𝓕 hr0 ⟨le_rfl, hru⟩)
    have hYr : StronglyMeasurable[𝓕 r] (fun ω => Λ r ω * R r ω) :=
      (hΛr.adapted r ⟨le_rfl, hru⟩).mul (hRr.adapted r ⟨le_rfl, hru⟩)
    have h3 : P[fun ω => Λ r ω * R r ω | 𝓕 r] = fun ω => Λ r ω * R r ω :=
      condExp_of_stronglyMeasurable (𝓕.le r) hYr ir
    rcases hru.lt_or_eq with hru' | hru'
    · have iu : Integrable (fun ω => Λ u ω * R u ω) P :=
        (hΛr.memLp hB hW h𝓕 hr0 ⟨hru, le_rfl⟩).integrable_mul
          (hRr.memLp hB hW h𝓕 hr0 ⟨hru, le_rfl⟩)
      have h1 := condExp_incr_eq_condExp_dtInt hB hW h𝓕 hr0 hru' hΛr hRr
      have hz := dtInt_ae_zero ((msIntegrand_drift hB hW h𝓕 hs hΛ hR).mono hsr hut)
        fun v hv => h0 v ⟨hsr.trans hv.1, hv.2.trans_le hut⟩
      have hz' := (condExp_congr_ae (m := 𝓕 r) hz).trans (by rw [condExp_zero])
      have h2 := condExp_sub (m := 𝓕 r) iu ir
      filter_upwards [h1, h2, hz'] with ω e1 e2 e3
      have e2' : P[fun ω => Λ u ω * R u ω - Λ r ω * R r ω | 𝓕 r] ω =
          P[fun ω => Λ u ω * R u ω | 𝓕 r] ω - Λ r ω * R r ω := by
        rw [show (fun ω => Λ u ω * R u ω - Λ r ω * R r ω) =
          (fun ω => Λ u ω * R u ω) - fun ω => Λ r ω * R r ω from rfl, e2, Pi.sub_apply, h3]
      simp only [Pi.zero_apply] at e3
      linarith
    · subst hru'
      rw [h3]

/-- **Cochrane (2023), A1.5, p. 566: the converse, at every date of `[s, t]` along almost every
path.** If moreover `Λ` and `R` have a.s. continuous paths on `[s, t]`, `s < t`, and `ΛR` is a
martingale on `[s, t]`, then a.s., for every `u ∈ [s, t]`,
`Λ_u a_R(u) + R_u a_Λ(u) + σ_Λ(u)σ_R(u) = 0` (the a.e. statements at rational dates and path
continuity). -/
theorem drift_pathwise_zero_of_martingale (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hΛ : ItoProcess P 𝓕 W Λ aΛ σΛ s t CΛ CΛσ) (hR : ItoProcess P 𝓕 W R aR σR s t CR CRσ)
    (hΛc : ∀ᵐ ω ∂P, ContinuousOn (fun u => Λ u ω) (Set.Icc s t))
    (hRc : ∀ᵐ ω ∂P, ContinuousOn (fun u => R u ω) (Set.Icc s t))
    (hmart : ∀ r u, s ≤ r → r < u → u ≤ t →
      P[fun ω => Λ u ω * R u ω | 𝓕 r] =ᵐ[P] fun ω => Λ r ω * R r ω) :
    ∀ᵐ ω ∂P, ∀ u ∈ Set.Icc s t, Λ u ω * aR u ω + R u ω * aΛ u ω + σΛ u ω * σR u ω = 0 := by
  have hper := drift_ae_zero_of_martingale hB hW h𝓕 hs hΛ hR hmart
  have hq : ∀ᵐ ω ∂P, ∀ q : ℚ, (q : ℝ) ∈ Set.Ioo s t →
      Λ q ω * aR q ω + R q ω * aΛ q ω + σΛ q ω * σR q ω = 0 := by
    rw [ae_all_iff]
    intro q
    by_cases hq : (q : ℝ) ∈ Set.Ioo s t
    · filter_upwards [hper q ⟨hq.1.le, hq.2⟩] with ω hω _
      exact hω
    · exact ae_of_all _ fun ω h => absurd h hq
  filter_upwards [hq, hΛc, hRc, hΛ.drift.cont, hΛ.diff.cont, hR.drift.cont, hR.diff.cont]
    with ω h c1 c2 c3 c4 c5 c6
  have hc : ContinuousOn (fun u => Λ u ω * aR u ω + R u ω * aΛ u ω + σΛ u ω * σR u ω)
      (Set.Icc s t) := ((c1.mul c5).add (c2.mul c3)).add (c4.mul c6)
  have hsub : Set.Ioo s t ∩ Set.range (Rat.cast : ℚ → ℝ) ⊆ Set.Icc s t := fun x hx =>
    Set.Ioo_subset_Icc_self hx.1
  have hcl : Set.Icc s t ⊆ closure (Set.Ioo s t ∩ Set.range (Rat.cast : ℚ → ℝ)) := by
    rw [← closure_Ioo hst.ne]
    exact closure_minimal (Dense.open_subset_closure_inter Rat.denseRange_cast isOpen_Ioo)
      isClosed_closure
  have heq : Set.EqOn (fun u => Λ u ω * aR u ω + R u ω * aΛ u ω + σΛ u ω * σR u ω)
      (fun _ => (0 : ℝ)) (Set.Ioo s t ∩ Set.range (Rat.cast : ℚ → ℝ)) := by
    rintro x ⟨hx, q, rfl⟩
    exact h q hx
  intro u hu
  exact heq.of_subset_closure hc continuousOn_const hsub hcl hu

variable {V aV σV sp : ℝ → Ω → ℝ} {CV CVσ : ℝ}

/-- **Cochrane (2023), A1.5, p. 566, and (3.35), p. 74: the converse of
`E_t[d(Λ_tV_t)] = −Λ_ts_t dt`.** If `Λ`, `V` are Itô processes on `[s, t]`, `0 ≤ s`, the
discounted surplus `Λ s` is a mean-square continuous adapted integrand, and
`E_r[Λ_uV_u − Λ_rV_r] = −E_r[∫_r^u Λs]` a.s. for all `s ≤ r < u ≤ t`, then at every date
`u ∈ [s, t)`, a.s. `Λ a_V + V a_Λ + σ_Λσ_V + Λ s = 0` (the pricing condition of
`TidyR7ItoDiscountFactor.ItoDiscountModel`). The converse of `ItoDiscountModel.step`. -/
theorem pricing_ae_of_step (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s)
    (hΛ : ItoProcess P 𝓕 W Λ aΛ σΛ s t CΛ CΛσ) (hV : ItoProcess P 𝓕 W V aV σV s t CV CVσ)
    (hsp : MSIntegrand P 𝓕 (fun u ω => Λ u ω * sp u ω) s t)
    (hstep : ∀ r u, s ≤ r → r < u → u ≤ t →
      P[fun ω => Λ u ω * V u ω - Λ r ω * V r ω | 𝓕 r] =ᵐ[P]
        P[fun ω => -dtInt P 𝓕 (fun u ω => Λ u ω * sp u ω) r u ω | 𝓕 r]) :
    ∀ u ∈ Set.Ico s t, (fun ω => Λ u ω * aV u ω + V u ω * aΛ u ω + σΛ u ω * σV u ω
      + Λ u ω * sp u ω) =ᵐ[P] 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hD0 := msIntegrand_drift hB hW h𝓕 hs hΛ hV
  refine ae_zero_of_condExp_dtInt (MSIntegrand.add hD0 hsp) fun r u hsr hru hut => ?_
  have hD0' := hD0.mono hsr hut
  have hsp' := hsp.mono hsr hut
  have hr0 : 0 ≤ r := hs.trans hsr
  have hΛr := itoProcess_restrict hB hW h𝓕 hs hΛ hsr hru.le hut
  have hVr := itoProcess_restrict hB hW h𝓕 hs hV hsr hru.le hut
  have h1 := condExp_incr_eq_condExp_dtInt hB hW h𝓕 hr0 hru hΛr hVr
  have h2 := hstep r u hsr hru hut
  have i0 := (memLp_dtInt hD0').integrable one_le_two
  have isp := (memLp_dtInt hsp').integrable one_le_two
  have c1 := condExp_congr_ae (m := 𝓕 r) (dtInt_add hD0' hsp')
  have c2 := condExp_add (m := 𝓕 r) i0 isp
  have c3 : P[fun ω => -dtInt P 𝓕 (fun u ω => Λ u ω * sp u ω) r u ω | 𝓕 r] =ᵐ[P]
      fun ω => -P[dtInt P 𝓕 (fun u ω => Λ u ω * sp u ω) r u | 𝓕 r] ω :=
    condExp_neg (μ := P) (dtInt P 𝓕 (fun u ω => Λ u ω * sp u ω) r u) (𝓕 r)
  filter_upwards [c1, c2, c3, h1, h2] with ω e1 e2 e3 e4 e5
  simp only [Pi.add_apply, Pi.zero_apply] at e2 ⊢
  rw [e1, e2]
  linarith

/-! ## Non-vacuity -/

/-- **Cochrane (2023), A1.5, p. 566 (non-vacuity of the converse, economy W of
`TidyR7ItoDiscountFactorCex`):** on the constructed Brownian motion, the martingale property of
`ΛW` on `[0, 1]` (`ItoDiscountModel.martingale_W`) gives back, through
`drift_ae_zero_of_martingale`, the coefficient identity
`Λ ramp + W(−ramp) + φ·φ = 0` a.s. at every date of `[0, 1)`. -/
theorem w_drift_of_martingale : ∀ u ∈ Set.Ico (0 : ℝ) 1,
    (fun ω => wΛ u ω * ramp u + wW u ω * -ramp u + 1 * phiW u * (1 * phiW u))
      =ᵐ[gaussSeq] 0 := by
  have hBM := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hBM measurable_bmPath
  have hm := wModel (le_refl (0 : ℝ)) zero_le_one
  exact drift_ae_zero_of_martingale hBM measurable_bmPath h𝓕 le_rfl hm.lam_ito hm.val_ito
    fun r u hr hru hu => hm.martingale_W hBM measurable_bmPath h𝓕 le_rfl hr hru.le hu

end Cochrane.Generality.TidyR9MartingaleDrift
