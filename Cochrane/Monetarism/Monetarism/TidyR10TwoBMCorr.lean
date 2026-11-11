/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR10TwoBMIto
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# The correlated motion `W³ = ρW¹ + √(1 − ρ²)W²` is a Brownian motion

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for (1.32) with correlated
shocks (Track 3, chunk B2): for two independent pre-Brownian motions and `|ρ| ≤ 1`, the
combination `W³ = ρW¹ + √(1 − ρ²)W²` (`TidyR10TwoBMIto.corrBM`) is itself a pre-Brownian
motion (a Brownian motion when paths are continuous), and every common admissible filtration of
`(W¹, W²)` is admissible for `W³`, so the whole one-driver toolkit (I5c–I5d, B1) applies to
`W³`; its bracket with `W¹` is `ρ dt` (`TidyR10TwoBMIto.L2Tendsto_crossSum_corrBM`).

## Main results

* `isGaussianProcess_pair`: independent Gaussian processes are jointly Gaussian
  (`(W¹_t, W²_t)_t`, from Mathlib `IndepFun.hasGaussianLaw`).
* `isPreBrownianReal_corrBM` (`cov[W³_s, W³_t] = (ρ² + (1 − ρ²)) s = s`, the cross covariances
  vanishing by independence), `isBrownianReal_corrBM`.
* `bmFiltration_corrBM`: a `TidyR10TwoBMExist.TwoBMFiltration` of `(W¹, W²)` is a
  `TidyR7BrownianQV.BMFiltration` for `W³`.
* Non-vacuity: `isBrownianReal_corrBM_bmPath` on the constructed pair (Brownian, every path
  continuous, `twoBMF` admissible).
-/

namespace Cochrane.Monetarism.TidyR10TwoBMCorr

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7BrownianTools Cochrane.Monetarism.TidyR7BrownianQV
  Cochrane.Monetarism.TidyR10TwoBMExist Cochrane.Monetarism.TidyR10TwoBMIto
  Cochrane.Monetarism.TidyR7BrownianSchauder Cochrane.Monetarism.TidyR7BrownianExist
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W₁ W₂ : ℝ≥0 → Ω → ℝ}

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **two independent Gaussian processes are jointly
Gaussian**: `t ↦ (W¹_t, W²_t)` is a Gaussian process (Mathlib `IndepFun.hasGaussianLaw` on each
finite set of times). -/
theorem isGaussianProcess_pair (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hI : IndepFun (fun ω t => W₁ t ω) (fun ω t => W₂ t ω) P) :
    IsGaussianProcess (fun t ω => (W₁ t ω, W₂ t ω)) P where
  hasGaussianLaw I := by
    have h1 := hB₁.isGaussianProcess.hasGaussianLaw I
    have h2 := hB₂.isGaussianProcess.hasGaussianLaw I
    have hr : Measurable fun (f : ℝ≥0 → ℝ) => I.restrict f := by fun_prop
    have hind : IndepFun (fun ω => I.restrict (W₁ · ω)) (fun ω => I.restrict (W₂ · ω)) P :=
      hI.comp hr hr
    have hj := IndepFun.hasGaussianLaw h1 h2 hind
    let L : ((I → ℝ) × (I → ℝ)) →L[ℝ] (I → ℝ × ℝ) :=
      ContinuousLinearMap.pi fun i =>
        ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (I → ℝ) (I → ℝ))).prod
          ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ (I → ℝ) (I → ℝ)))
    have e : (fun ω => I.restrict (fun t => (W₁ t ω, W₂ t ω)))
        = fun ω => L (I.restrict (W₁ · ω), I.restrict (W₂ · ω)) := by
      funext ω
      ext i <;> rfl
    rw [e]
    exact hj.map_fun L

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `W³ = ρW¹ + √(1 − ρ²)W²` is a Gaussian process. -/
theorem isGaussianProcess_corrBM (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hI : IndepFun (fun ω t => W₁ t ω) (fun ω t => W₂ t ω) P) (ρ : ℝ) :
    IsGaussianProcess (corrBM ρ W₁ W₂) P := by
  classical
  refine (isGaussianProcess_pair hB₁ hB₂ hI).of_isGaussianProcess fun t => ?_
  let I : Finset ℝ≥0 := {t}
  have ht : t ∈ I := Finset.mem_singleton_self t
  refine ⟨I, (ρ • ContinuousLinearMap.fst ℝ ℝ ℝ
    + Real.sqrt (1 - ρ ^ 2) • ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℝ × ℝ) ⟨t, ht⟩), fun ω => ?_⟩
  simp [corrBM, Finset.restrict]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the correlated motion is a pre-Brownian motion.**
For independent pre-Brownian `W¹`, `W²` (paths independent) and `|ρ| ≤ 1`,
`W³ = ρW¹ + √(1 − ρ²)W²` is pre-Brownian: centred Gaussian with
`cov[W³_s, W³_t] = ρ²s + (1 − ρ²)s = s` for `s ≤ t`. -/
theorem isPreBrownianReal_corrBM (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hI : IndepFun (fun ω t => W₁ t ω) (fun ω t => W₂ t ω) P) {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    IsPreBrownianReal (corrBM ρ W₁ W₂) P := by
  have : IsProbabilityMeasure P := hB₁.isGaussianProcess.isProbabilityMeasure
  have m1 : ∀ t, MemLp (W₁ t) 2 P := fun t =>
    (hB₁.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have m2 : ∀ t, MemLp (W₂ t) 2 P := fun t =>
    (hB₂.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hsq : Real.sqrt (1 - ρ ^ 2) ^ 2 = 1 - ρ ^ 2 := by
    rw [Real.sq_sqrt]
    nlinarith [abs_le.1 hρ, sq_abs ρ]
  have hc : ∀ s t, cov[W₁ s, W₂ t; P] = 0 := fun s t =>
    (hI.comp (measurable_pi_apply s) (measurable_pi_apply t)).covariance_eq_zero (m1 s) (m2 t)
  refine (isGaussianProcess_corrBM hB₁ hB₂ hI ρ).isPreBrownianReal_of_covariance
    (fun t => ?_) (fun s t hst => ?_)
  · change ∫ ω, (ρ * W₁ t ω + Real.sqrt (1 - ρ ^ 2) * W₂ t ω) ∂P = 0
    rw [integral_add ((hB₁.integrable_eval t).const_mul _) ((hB₂.integrable_eval t).const_mul _),
      integral_const_mul, integral_const_mul, hB₁.integral_eval, hB₂.integral_eval]
    ring
  · have e : ∀ u, corrBM ρ W₁ W₂ u
        = (fun ω => ρ * W₁ u ω) + fun ω => Real.sqrt (1 - ρ ^ 2) * W₂ u ω := fun u => rfl
    rw [e, e, covariance_add_left ((m1 s).const_mul _) ((m2 s).const_mul _)
      (((m1 t).const_mul _).add ((m2 t).const_mul _)),
      covariance_add_right ((m1 s).const_mul _) ((m1 t).const_mul _) ((m2 t).const_mul _),
      covariance_add_right ((m2 s).const_mul _) ((m1 t).const_mul _) ((m2 t).const_mul _)]
    simp only [covariance_const_mul_left, covariance_const_mul_right]
    rw [hB₁.covariance_eval, hB₂.covariance_eval, hc, covariance_comm, hc, min_eq_left hst]
    have h2 : Real.sqrt (1 - ρ ^ 2) * (Real.sqrt (1 - ρ ^ 2) * (s : ℝ))
        = (1 - ρ ^ 2) * s := by
      rw [← mul_assoc, ← sq, hsq]
    rw [h2]
    ring

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the correlated motion is a Brownian motion** when
`W¹`, `W²` have a.s. continuous paths, `|ρ| ≤ 1`. -/
theorem isBrownianReal_corrBM (hB₁ : IsBrownianReal W₁ P) (hB₂ : IsBrownianReal W₂ P)
    (hI : IndepFun (fun ω t => W₁ t ω) (fun ω t => W₂ t ω) P) {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    IsBrownianReal (corrBM ρ W₁ W₂) P where
  toIsPreBrownianReal := isPreBrownianReal_corrBM hB₁.toIsPreBrownianReal
    hB₂.toIsPreBrownianReal hI hρ
  cont := by
    filter_upwards [hB₁.cont, hB₂.cont] with ω h1 h2
    exact (continuous_const.mul h1).add (continuous_const.mul h2)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the correlated motion has measurable values. -/
theorem measurable_corrBM (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (ρ : ℝ) (t : ℝ≥0) : Measurable (corrBM ρ W₁ W₂ t) :=
  ((hW₁ t).const_mul ρ).add ((hW₂ t).const_mul _)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: a common admissible filtration of `(W¹, W²)` is
admissible for `W³`**: `W³` is adapted, and its increment over `[u, v]` is a function of the
pair of increments, independent of `𝓕_u`. -/
theorem bmFiltration_corrBM {𝓕 : Filtration ℝ mΩ} (h : TwoBMFiltration P W₁ W₂ 𝓕) (ρ : ℝ) :
    BMFiltration P (corrBM ρ W₁ W₂) 𝓕 where
  adapted u := ((h.bm1.adapted u).const_mul ρ).add
    ((h.bm2.adapted u).const_mul (Real.sqrt (1 - ρ ^ 2)))
  indep u v huv := by
    refine indep_of_indep_of_le_left (h.indep u v huv) ?_
    have hm : Measurable[MeasurableSpace.comap (fun ω => (incr W₁ u v ω, incr W₂ u v ω))
        inferInstance] (fun ω => (fun z : ℝ × ℝ => ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2)
          ((fun ω => (incr W₁ u v ω, incr W₂ u v ω)) ω)) :=
      ((measurable_fst.const_mul _).add (measurable_snd.const_mul _)).comp (comap_measurable _)
    have e : incr (corrBM ρ W₁ W₂) u v = fun ω =>
        (fun z : ℝ × ℝ => ρ * z.1 + Real.sqrt (1 - ρ ^ 2) * z.2)
          ((fun ω => (incr W₁ u v ω, incr W₂ u v ω)) ω) := funext fun ω => incr_corrBM ρ u v ω
    rw [e]
    exact hm.comap_le

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (non-vacuity): on the constructed pair, for
`|ρ| ≤ 1`, `W³ = ρW¹ + √(1 − ρ²)W²` is a Brownian motion with every path continuous**, and the
joint filtration `twoBMF` is admissible for it. -/
theorem isBrownianReal_corrBM_bmPath {ρ : ℝ} (hρ : |ρ| ≤ 1) :
    IsBrownianReal (corrBM ρ bmPath₁ bmPath₂) twoGauss ∧
      (∀ ω, Continuous fun t => corrBM ρ bmPath₁ bmPath₂ t ω) ∧
      BMFiltration twoGauss (corrBM ρ bmPath₁ bmPath₂) twoBMF :=
  ⟨isBrownianReal_corrBM isBrownianReal_bmPath₁ isBrownianReal_bmPath₂ indepFun_bmPath₁₂ hρ,
    fun ω => (continuous_const.mul (continuous_bmPath ω.1)).add
      (continuous_const.mul (continuous_bmPath ω.2)),
    bmFiltration_corrBM twoBMFiltration_bmPath_isTwoBM ρ⟩

end Cochrane.Monetarism.TidyR10TwoBMCorr
