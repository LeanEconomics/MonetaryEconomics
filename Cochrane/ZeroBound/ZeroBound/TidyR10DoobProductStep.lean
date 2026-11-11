/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR10DoobAugment
import ZeroBound.TidyR7ProductStep
import ZeroBound.TidyR7BrownianVariation
import ZeroBound.TidyR9ItoFormula

/-!
# The Track 1 product step with a Brownian or Itô-integral martingale part

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eq. (1.32) (Track 3, chunk B3, item 3a). The product step
`TidyR7ProductStep.ProductStepData.product_step`,
`E_s[B_tX_t − B_sX_s] = E_s[∫_s^t X dB] + E_s[∫_s^t B dA]`, needs a martingale part `M` with
EVERY path càdlàg (`TidyR7ProductStep.ProductStepData.M_cadlag`) and an integrable
`sup_{[s,t]}|X|·Var_{[s,t]}(B)` (`TidyR7ProductStep.ProductStepData.int_XB`).
I5b/I5d could not supply either for `M = W` or `M = ∫K dW` (no Doob bound, no path-regular
version). With `TidyR10DoobIto.doob_sq_bm` and `TidyR10DoobAugment.exists_continuous_itoInt_augment`
both are now available, for bonds `B` adapted, bounded, with continuous bounded-variation paths
and bounded measurable variation, and `A = 0`.

## Main results

* `productStepData_of_martingale`: the generic instance from a martingale with càdlàg paths and
  integrable path supremum.
* `martingale_bmReal_of_bmFiltration`: `W` is a martingale for any admissible filtration (on the
  whole index `ℝ`).
* `productStepData_bm` (**M = W**), for `W` with every path continuous.
* `exists_productStepData_itoInt` (**M = ∫K dW**): an every-path-continuous version `X` of
  `t ↦ ∫_{s₀}^t K dW` for the completed filtration `TidyR10DoobAugment.augment P 𝓕`, with the
  data; `product_step_itoInt`: the product step itself, conditioned on `𝓕_s` (not its
  completion): `E_s[B_tX_t − B_sX_s] = E_s[∫_s^t X dB]`.
* Non-vacuity on `TidyR7BrownianExist.bmPath` with `B_u = u`: `productStepData_bmPath` and
  `exists_productStepData_itoInt_cos_bmPath` (`K = cos W`).
-/

namespace Cochrane.ZeroBound.TidyR10DoobProductStep

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.TidyR7StieltjesIntegral Cochrane.ZeroBound.TidyR7StieltjesSums
  Cochrane.ZeroBound.TidyR7BrownianTools Cochrane.ZeroBound.TidyR7BrownianExist
  Cochrane.ZeroBound.TidyR7BrownianSchauder Cochrane.ZeroBound.TidyR7BrownianQV
  Cochrane.ZeroBound.TidyR7ItoSums Cochrane.ZeroBound.TidyR7ItoIntegral
  Cochrane.ZeroBound.TidyR7CondDominated Cochrane.ZeroBound.TidyR7ProductStep
  Cochrane.ZeroBound.TidyR7BrownianVariation Cochrane.ZeroBound.TidyR9ItoFormula
  Cochrane.ZeroBound.TidyR10DoobContinuous Cochrane.ZeroBound.TidyR10DoobIto
  Cochrane.ZeroBound.TidyR10DoobAugment
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Cochrane (2023), A1 §1.6, p. 567: the zero process has zero variation on `[s, t]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobProductStep.pathVar_zero). -/
theorem pathVar_zero (s t : ℝ) (ω : Ω) : pathVar s t (fun _ _ => (0 : ℝ)) ω = 0 := by
  simp only [pathVar]
  rw [eVariationOn.constant_on (Set.subsingleton_of_forall_eq (0 : ℝ) fun _ ⟨_, _, hy⟩ =>
    hy.symm)]
  rfl

/-- Cochrane (2023), A1 §1.6, p. 567: `X = 0 + M` is `M`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobProductStep.addProc_zero_left). -/
theorem addProc_zero_left (M : ℝ → Ω → ℝ) : addProc (fun _ _ => (0 : ℝ)) M = M := by
  funext u ω
  simp [addProc]

/-- Cochrane (2023), A1 §1.6, p. 567: `∫_s^t B d0 = 0` for a path bounded on `[s, t]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobProductStep.intRS_zero_right). -/
theorem intRS_zero_right {s t K : ℝ} (hst : s ≤ t) {B : ℝ → Ω → ℝ}
    (hBK : ∀ u ∈ Set.Icc s t, ∀ ω, |B u ω| ≤ K) (ω : Ω) :
    intRS s t B (fun _ _ => (0 : ℝ)) ω = 0 := by
  have h0 : eVariationOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc s t) = 0 :=
    eVariationOn.constant_on (Set.subsingleton_of_forall_eq (0 : ℝ) fun _ ⟨_, _, hy⟩ => hy.symm)
  have hbv : BoundedVariationOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc s t) := by
    rw [BoundedVariationOn, h0]
    exact ENNReal.zero_ne_top
  have h := abs_rsInt_le hst hbv (fun x hx => hBK x hx ω) (f := fun u => B u ω)
  rw [h0, ENNReal.toReal_zero, mul_zero] at h
  exact abs_nonpos_iff.1 h

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the product-step data from a martingale with
integrable path supremum.** Let `s ≤ t`, `B` adapted on `[s, t]` with continuous
bounded-variation paths, `|B| ≤ K` on `[s, t]`, `Var_{[s,t]}(B)` measurable and `≤ V`; `M` a
martingale with every path càdlàg and `sup_{[s,t]}|M|` integrable. Then
`TidyR7ProductStep.ProductStepData` holds with `A = 0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobProductStep.productStepData_of_martingale). -/
theorem productStepData_of_martingale {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝓖 : Filtration ℝ mΩ} {s t K V : ℝ} {B M : ℝ → Ω → ℝ} (hst : s ≤ t)
    (hBa : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓖 u] (B u))
    (hBc : ∀ ω, ContinuousOn (fun u => B u ω) (Set.Icc s t))
    (hBv : ∀ ω, BoundedVariationOn (fun u => B u ω) (Set.Icc s t))
    (hBK : ∀ u ∈ Set.Icc s t, ∀ ω, |B u ω| ≤ K) (hVm : Measurable (pathVar s t B))
    (hV : ∀ ω, pathVar s t B ω ≤ V) (hM : Martingale M 𝓖 μ)
    (hMc : ∀ ω, IsCadlag fun u => M u ω) (hMs : Integrable (pathSup s t M) μ) :
    ProductStepData μ 𝓖 s t B (fun _ _ => 0) M where
  le := hst
  B_adapted := hBa
  B_cont := hBc
  B_bv := hBv
  A_meas _ _ := measurable_const
  A_cadlag _ := IsCadlag.const
  A_bv _ := by
    rw [BoundedVariationOn, eVariationOn.constant_on
      (Set.subsingleton_of_forall_eq (0 : ℝ) fun _ ⟨_, _, hy⟩ => hy.symm)]
    exact ENNReal.zero_ne_top
  M_mart := hM
  M_cadlag := hMc
  int_XB := by
    rw [addProc_zero_left]
    exact hMs.mul_bdd hVm.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ pathVar s t B ω from ENNReal.toReal_nonneg)]
      exact hV ω)
  int_BA := by
    simp only [pathVar_zero, mul_zero]
    exact integrable_zero _ _ _
  int_BM := integrable_mul_incr_of_bound hBK
    (fun u hu => ((hBa u hu).mono (𝓖.le u)).measurable) hM.integrable

/-! ## `M = W` -/

variable {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ mΩ}

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: Brownian motion is a martingale for every
admissible filtration**, on the whole index `ℝ` (`W_u = W_0` for `u < 0`).
Generalises `TidyR7BrownianTools.martingale_bmReal` to any admissible filtration.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobProductStep.martingale_bmReal_of_bmFiltration). -/
theorem martingale_bmReal_of_bmFiltration (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) : Martingale (bmReal W) 𝓕 P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hint : ∀ u, Integrable (bmReal W u) P := fun u =>
    ((hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two).integrable one_le_two
  refine ⟨fun u => h𝓕.adapted u, fun i j hij => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le i) (hint j)
    (fun _ _ _ => (hint i).integrableOn) ?_ (h𝓕.adapted i).aestronglyMeasurable).symm
  intro A hA _
  have hA' : MeasurableSet A := 𝓕.le i A hA
  have h := integral_mul_incr hB hW h𝓕 hij (Y := A.indicator fun _ => (1 : ℝ))
    (stronglyMeasurable_const.indicator hA)
  rw [integral_indicator_one_mul hA'] at h
  have hinc : Integrable (incr W i j) P := (memLp_incr hB i j).integrable one_le_two
  calc ∫ ω in A, bmReal W i ω ∂P = ∫ ω in A, bmReal W i ω ∂P + ∫ ω in A, incr W i j ω ∂P := by
        rw [h, add_zero]
    _ = ∫ ω in A, (bmReal W i ω + incr W i j ω) ∂P :=
        (integral_add (hint i).integrableOn hinc.integrableOn).symm
    _ = ∫ ω in A, bmReal W j ω ∂P := by
        congr 1
        funext ω
        simp [incr]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567 (Track 3, item 3a): the product step with
`M = W`.** For a pre-Brownian `W` with measurable values and EVERY path continuous, an
admissible filtration, `s < t`, and bonds `B` as in `productStepData_of_martingale`,
`TidyR7ProductStep.ProductStepData` holds with `A = 0`, `M = W`: the path supremum of `W` is
integrable by Doob's inequality `TidyR10DoobIto.doob_sq_bm`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobProductStep.productStepData_bm). -/
theorem productStepData_bm (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω) {s t K V : ℝ}
    (hst : s < t) {B : ℝ → Ω → ℝ} (hBa : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (B u))
    (hBc : ∀ ω, ContinuousOn (fun u => B u ω) (Set.Icc s t))
    (hBv : ∀ ω, BoundedVariationOn (fun u => B u ω) (Set.Icc s t))
    (hBK : ∀ u ∈ Set.Icc s t, ∀ ω, |B u ω| ≤ K) (hVm : Measurable (pathVar s t B))
    (hV : ∀ ω, pathVar s t B ω ≤ V) :
    ProductStepData P 𝓕 s t B (fun _ _ => 0) (bmReal W) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm : Measurable (pathSup s t (bmReal W)) := measurable_pathSup fun _ _ => hW _
  have hsq := (doob_sq_bm hB hW h𝓕 (ae_of_all _ hcont) hst).1
  have hMs : Integrable (pathSup s t (bmReal W)) P :=
    ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 hsq).integrable one_le_two
  exact productStepData_of_martingale hst.le hBa hBc hBv hBK hVm hV
    (martingale_bmReal_of_bmFiltration hB hW h𝓕)
    (fun ω => (continuous_bmReal (hcont ω)).isCadlag) hMs

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567 (Track 3, item 4, non-vacuity): the product step
with `M = W` on the constructed motion**, `B_u = u`, on `[0, 1]`, natural filtration.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobProductStep.productStepData_bmPath). -/
theorem productStepData_bmPath :
    ProductStepData gaussSeq (bmFiltrationReal bmPath measurable_bmPath) 0 1
      (fun u _ => u) (fun _ _ => 0) (bmReal bmPath) :=
  productStepData_bm isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) continuous_bmPath
    zero_lt_one (K := 1) (V := (eVariationOn (fun u : ℝ => u) (Set.Icc 0 1)).toReal)
    (fun _ _ => stronglyMeasurable_const) (fun _ => continuousOn_id) (fun _ => bv_id 0 1)
    (fun u hu _ => by rw [abs_of_nonneg hu.1]; exact hu.2) measurable_const (fun _ => le_rfl)

/-! ## `M = ∫K dW` -/

/-- Cochrane (2023), A1 §1.6, p. 567: for a path continuous on `[s₀, t]` and `s₀ ≤ s ≤ t`,
`sup_{[s,t]}|X| ≤ sup_{[s₀,t]}|X|`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobProductStep.pathSup_le_pathSup). -/
theorem pathSup_le_pathSup {X : ℝ → Ω → ℝ} {ω : Ω} {s₀ s t : ℝ} (hs₀ : s₀ ≤ s) (hst : s ≤ t)
    (hX : ContinuousOn (fun u => X u ω) (Set.Icc s₀ t)) : pathSup s t X ω ≤ pathSup s₀ t X ω :=
  pathSup_le_of_forall_abs_le hst fun _ hu =>
    abs_le_pathSup_of_continuousOn hX ⟨hs₀.trans hu.1, hu.2⟩

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567 (Track 3, item 3a): the product step with
`M = ∫K dW`.** Let `W` be pre-Brownian with measurable values and a.s. continuous paths, `𝓕`
admissible, `0 ≤ s₀ ≤ s < t`, `K` admissible for `𝓕` on every `[s₀, T]` with one bound, and
bonds `B` adapted to `𝓕` as in `productStepData_of_martingale`. There is `X` with
`X_u = ∫_{s₀}^u K dW` a.s. for every `u`, EVERY path continuous, `X` a martingale for the
completed filtration `TidyR10DoobAugment.augment P 𝓕`, and
`TidyR7ProductStep.ProductStepData` holds for `augment P 𝓕` with `A = 0`, `M = X`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobProductStep.exists_productStepData_itoInt). -/
theorem exists_productStepData_itoInt (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω) {s₀ s t C K V : ℝ} (hs₀ : 0 ≤ s₀)
    (hs₀s : s₀ ≤ s) (hst : s < t) {G : ℝ → Ω → ℝ} (hG : ∀ T, ItoIntegrand P 𝓕 G s₀ T C)
    {B : ℝ → Ω → ℝ} (hBa : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (B u))
    (hBc : ∀ ω, ContinuousOn (fun u => B u ω) (Set.Icc s t))
    (hBv : ∀ ω, BoundedVariationOn (fun u => B u ω) (Set.Icc s t))
    (hBK : ∀ u ∈ Set.Icc s t, ∀ ω, |B u ω| ≤ K) (hVm : Measurable (pathVar s t B))
    (hV : ∀ ω, pathVar s t B ω ≤ V) :
    ∃ X : ℝ → Ω → ℝ, (∀ u, X u =ᵐ[P] itoInt P 𝓕 W G s₀ u) ∧
      (∀ ω, Continuous fun u => X u ω) ∧ Martingale X (augment P 𝓕) P ∧
      ProductStepData P (augment P 𝓕) s t B (fun _ _ => 0) X := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨X, hXm, hXI, -, hXc, hXmart, hXd⟩ :=
    exists_continuous_itoInt_augment hB hW h𝓕 hcont hs₀ hG
  have hXmeas : ∀ u, Measurable (X u) := fun u =>
    ((hXm u).mono ((augment P 𝓕).le u)).measurable
  have hm0 : Measurable (pathSup s₀ t X) := measurable_pathSup fun u _ => hXmeas u
  have hm : Measurable (pathSup s t X) := measurable_pathSup fun u _ => hXmeas u
  have hsq := (hXd t (hs₀s.trans_lt hst)).1
  have hMs0 : Integrable (pathSup s₀ t X) P :=
    ((memLp_two_iff_integrable_sq hm0.aestronglyMeasurable).2 hsq).integrable one_le_two
  have hMs : Integrable (pathSup s t X) P := hMs0.mono' hm.aestronglyMeasurable
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pathSup_nonneg _ _ _ _)]
      exact pathSup_le_pathSup hs₀s hst.le (hXc ω).continuousOn)
  exact ⟨X, hXI, hXc, hXmart, productStepData_of_martingale hst.le
    (fun u hu => (hBa u hu).mono (le_augment u)) hBc hBv hBK hVm hV hXmart
    (fun ω => (hXc ω).isCadlag) hMs⟩

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567 (Track 3, item 3a): the product step for
`X = ∫K dW` and bounded-variation bonds, conditioned on `𝓕_s`.** In the setting of
`exists_productStepData_itoInt`, the version `X` satisfies
`E[B_tX_t − B_sX_s | 𝓕_s] = E[∫_s^t X dB | 𝓕_s]` a.s. (the pathwise Riemann–Stieltjes integral
`TidyR7ProductStep.intRS`; the conditional expectations are for `𝓕` itself, via
`TidyR10DoobAugment.condExp_augment`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobProductStep.product_step_itoInt). -/
theorem product_step_itoInt (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω) {s₀ s t C K V : ℝ} (hs₀ : 0 ≤ s₀)
    (hs₀s : s₀ ≤ s) (hst : s < t) {G : ℝ → Ω → ℝ} (hG : ∀ T, ItoIntegrand P 𝓕 G s₀ T C)
    {B : ℝ → Ω → ℝ} (hBa : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (B u))
    (hBc : ∀ ω, ContinuousOn (fun u => B u ω) (Set.Icc s t))
    (hBv : ∀ ω, BoundedVariationOn (fun u => B u ω) (Set.Icc s t))
    (hBK : ∀ u ∈ Set.Icc s t, ∀ ω, |B u ω| ≤ K) (hVm : Measurable (pathVar s t B))
    (hV : ∀ ω, pathVar s t B ω ≤ V) :
    ∃ X : ℝ → Ω → ℝ, (∀ u, X u =ᵐ[P] itoInt P 𝓕 W G s₀ u) ∧
      (∀ ω, Continuous fun u => X u ω) ∧
      P[fun ω => B t ω * X t ω - B s ω * X s ω | 𝓕 s] =ᵐ[P] P[intRS s t X B | 𝓕 s] := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨X, hXI, hXc, -, hd⟩ := exists_productStepData_itoInt hB hW h𝓕 hcont hs₀ hs₀s hst hG
    hBa hBc hBv hBK hVm hV
  refine ⟨X, hXI, hXc, ?_⟩
  have h := hd.product_step
  rw [addProc_zero_left] at h
  have e : intRS s t B (fun _ _ => (0 : ℝ)) = fun _ => 0 :=
    funext (intRS_zero_right hst.le hBK)
  rw [e, condExp_const ((augment P 𝓕).le s), ← Pi.zero_def, add_zero] at h
  exact (condExp_augment _ s).symm.trans (h.trans (condExp_augment _ s))

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `cos W` is admissible on every `[s, T]` for the
natural filtration of the constructed motion, with bound `1`.
Restates TidyR9MonetarismItoPositive.itoIntegrand_cos_bm.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobProductStep.itoIntegrand_cos_bmPath). -/
theorem itoIntegrand_cos_bmPath {s T : ℝ} :
    ItoIntegrand gaussSeq (bmFiltrationReal bmPath measurable_bmPath)
      (fun u ω => Real.cos (bmReal bmPath u ω)) s T 1 :=
  itoIntegrand_comp (g := fun _ x => Real.cos x)
    (fun u _ => (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath).adapted u)
    (ae_of_all _ fun ω => (continuous_bmReal (continuous_bmPath ω)).continuousOn)
    (Real.continuous_cos.comp continuous_snd) fun _ _ x => Real.abs_cos_le_one x

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567 (Track 3, item 4, non-vacuity): the product step
with `M = ∫_0^· cos W dW` on the constructed motion**, `B_u = u`, on `[0, 1]`, for the completed
natural filtration; and the product step conditioned on the natural filtration itself.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobProductStep.exists_productStepData_itoInt_cos_bmPath). -/
theorem exists_productStepData_itoInt_cos_bmPath :
    ∃ X : ℝ → (ℕ → ℝ) → ℝ, (∀ u, X u =ᵐ[gaussSeq] itoInt gaussSeq
        (bmFiltrationReal bmPath measurable_bmPath) bmPath
        (fun u ω => Real.cos (bmReal bmPath u ω)) 0 u) ∧
      (∀ ω, Continuous fun u => X u ω) ∧
      ProductStepData gaussSeq (augment gaussSeq (bmFiltrationReal bmPath measurable_bmPath)) 0 1
        (fun u _ => u) (fun _ _ => 0) X := by
  obtain ⟨X, hXI, hXc, -, hd⟩ := exists_productStepData_itoInt isPreBrownianReal_bmPath
    measurable_bmPath (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath)
    (ae_of_all _ continuous_bmPath) le_rfl le_rfl zero_lt_one
    (fun _ => itoIntegrand_cos_bmPath) (B := fun u _ => u) (K := 1)
    (V := (eVariationOn (fun u : ℝ => u) (Set.Icc 0 1)).toReal)
    (fun _ _ => stronglyMeasurable_const) (fun _ => continuousOn_id) (fun _ => bv_id 0 1)
    (fun u hu _ => by rw [abs_of_nonneg hu.1]; exact hu.2) measurable_const (fun _ => le_rfl)
  exact ⟨X, hXI, hXc, hd⟩

end Cochrane.ZeroBound.TidyR10DoobProductStep
