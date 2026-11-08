/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.TidyR7BrownianSchauder
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Moments.Covariance

/-!
# Standard Brownian motion on `[0,1]`: Gaussian process with covariance `min s t`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for (1.32) with diffusive
bonds (chunk I5a): the Lévy–Ciesielski path of `TidyR7BrownianSchauder` is a Brownian motion on
`[0,1]`, realised on the Gaussian sequence space `(ℕ → ℝ, gaussSeq)`.

Every declaration is restated (proofs kept) from the module `LimitTheorems/BrownianMotion.lean`
of the LeanDynamicProgramming project (namespace MeynTweedie.LimitTheorems there). Only what
the extension to `[0, ∞)` (`TidyR7BrownianExist`) needs is copied: the Wiener-measure and
path-space parts are not.

* `brownian t ω = levyPath ω t`; `continuous_brownian` (every path), `brownian_zero` (every
  path), `measurable_levyPath`, `measurable_brownian`.
* `gaussSeq_map_sum_brownian`: `Σ_i c i B(t i)` has law `N(0, Σ_{i,j} c i c j min(t i, t j))`.
* `hasGaussianLaw_brownian_vec`, `isGaussianProcess_brownian`: Mathlib's `IsGaussianProcess`.
* `gaussSeq_map_brownian`, `covariance_brownian`: `B(t) ~ N(0, t)`, `Cov(B s, B t) = min s t`.
-/

namespace Cochrane.Generality.TidyR7BrownianUnit

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Generality.TidyR7BrownianSchauder
open scoped ENNReal NNReal

/-- **Brownian motion on `[0,1]`**, realised on the Gaussian sequence space `(ℕ → ℝ, gaussSeq)`:
`brownian t ω = levyPath ω t`.
Cochrane (2023), Online Appendix A1 §1.6, pp. 567–568: infrastructure for (1.32) with
diffusive bonds. Restated from MeynTweedie.LimitTheorems.brownian
(LeanDynamicProgramming, StochasticStability/LimitTheorems/LimitTheorems/BrownianMotion.lean).
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7BrownianUnit.brownian). -/
noncomputable def brownian (t : unitInterval) (ω : ℕ → ℝ) : ℝ := levyPath ω t

/-- Every path of `brownian` is continuous.
Cochrane (2023), Online Appendix A1 §1.6, pp. 567–568: infrastructure for (1.32) with
diffusive bonds. Restated from MeynTweedie.LimitTheorems.continuous_brownian
(LeanDynamicProgramming, StochasticStability/LimitTheorems/LimitTheorems/BrownianMotion.lean).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianUnit.continuous_brownian). -/
theorem continuous_brownian (ω : ℕ → ℝ) : Continuous fun t => brownian t ω :=
  (levyPath ω).continuous

/-- Every path of `brownian` starts at `0`.
Cochrane (2023), Online Appendix A1 §1.6, pp. 567–568: infrastructure for (1.32) with
diffusive bonds. Restated from MeynTweedie.LimitTheorems.brownian_zero
(LeanDynamicProgramming, StochasticStability/LimitTheorems/LimitTheorems/BrownianMotion.lean).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianUnit.brownian_zero). -/
theorem brownian_zero (ω : ℕ → ℝ) : brownian 0 ω = 0 := levyPath_zero ω

open Classical in
/-- The truncated partial sums converge, for every `ω`, to `levyPath ω`.
Cochrane (2023), Online Appendix A1 §1.6, pp. 567–568: infrastructure for (1.32) with
diffusive bonds. Restated from MeynTweedie.LimitTheorems.tendsto_lcPartial_ite
(LeanDynamicProgramming, StochasticStability/LimitTheorems/LimitTheorems/BrownianMotion.lean).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianUnit.tendsto_lcPartial_ite). -/
lemma tendsto_lcPartial_ite (ω : ℕ → ℝ) :
    Tendsto (fun N => if ω ∈ lcGood then lcPartial N ω else 0) atTop (𝓝 (levyPath ω)) := by
  by_cases hω : ω ∈ lcGood
  · simpa [hω] using tendsto_lcPartial_levyPath hω
  · simp only [hω, ite_false, levyPath]
    exact tendsto_const_nhds

/-- The path map `ω ↦ levyPath ω` is measurable, for any Borel σ-algebra on the path space.
Cochrane (2023), Online Appendix A1 §1.6, pp. 567–568: infrastructure for (1.32) with
diffusive bonds. Restated from MeynTweedie.LimitTheorems.measurable_levyPath
(LeanDynamicProgramming, StochasticStability/LimitTheorems/LimitTheorems/BrownianMotion.lean).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianUnit.measurable_levyPath). -/
theorem measurable_levyPath [MeasurableSpace C(unitInterval, ℝ)]
    [BorelSpace C(unitInterval, ℝ)] : Measurable levyPath := by
  classical
  refine measurable_of_tendsto_metrizable
    (f := fun N ω => if ω ∈ lcGood then lcPartial N ω else 0) (fun N => ?_)
    (tendsto_pi_nhds.2 tendsto_lcPartial_ite)
  exact Measurable.ite measurableSet_lcGood (continuous_lcPartial N).measurable measurable_const

/-- Each `brownian t` is measurable.
Cochrane (2023), Online Appendix A1 §1.6, pp. 567–568: infrastructure for (1.32) with
diffusive bonds. Restated from MeynTweedie.LimitTheorems.measurable_brownian
(LeanDynamicProgramming, StochasticStability/LimitTheorems/LimitTheorems/BrownianMotion.lean).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianUnit.measurable_brownian). -/
theorem measurable_brownian (t : unitInterval) : Measurable (brownian t) := by
  let : MeasurableSpace C(unitInterval, ℝ) := borel _
  have : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩
  exact (continuous_eval_const t).measurable.comp measurable_levyPath

/-- The variance `Σ_{i,j} c i c j min (t i) (t j)` of `Σ_i c i B(t i)`.
Cochrane (2023), Online Appendix A1 §1.6, pp. 567–568: infrastructure for (1.32) with
diffusive bonds. Restated from MeynTweedie.LimitTheorems.bmVar
(LeanDynamicProgramming, StochasticStability/LimitTheorems/LimitTheorems/BrownianMotion.lean).
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7BrownianUnit.bmVar). -/
noncomputable def bmVar {ι : Type*} [Fintype ι] (t : ι → unitInterval) (c : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * min (t i : ℝ) (t j)

/-- The coefficient of `ξ_m` in `Σ_i c i B(t i)` of the Schauder series.
Cochrane (2023), Online Appendix A1 §1.6, pp. 567–568: infrastructure for (1.32) with
diffusive bonds. Restated from MeynTweedie.LimitTheorems.bmCoeff
(LeanDynamicProgramming, StochasticStability/LimitTheorems/LimitTheorems/BrownianMotion.lean).
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7BrownianUnit.bmCoeff). -/
noncomputable def bmCoeff {ι : Type*} [Fintype ι] (t : ι → unitInterval) (c : ι → ℝ) (m : ℕ) :
    ℝ :=
  ∑ i, c i * schauder m (t i)

/-- The partial variances converge: `Σ_{m<2^N} (bmCoeff t c m)² → bmVar t c`.
Cochrane (2023), Online Appendix A1 §1.6, pp. 567–568: infrastructure for (1.32) with
diffusive bonds. Restated from MeynTweedie.LimitTheorems.tendsto_sum_bmCoeff_sq
(LeanDynamicProgramming, StochasticStability/LimitTheorems/LimitTheorems/BrownianMotion.lean).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianUnit.tendsto_sum_bmCoeff_sq). -/
lemma tendsto_sum_bmCoeff_sq {ι : Type*} [Fintype ι] (t : ι → unitInterval) (c : ι → ℝ) :
    Tendsto (fun N => ∑ m ∈ Finset.range (2 ^ N), bmCoeff t c m ^ 2) atTop (𝓝 (bmVar t c)) := by
  have he : ∀ N, ∑ m ∈ Finset.range (2 ^ N), bmCoeff t c m ^ 2
      = ∑ i, ∑ j, c i * c j * ∑ m ∈ Finset.range (2 ^ N), schauder m (t i) * schauder m (t j) := by
    intro N
    simp_rw [bmCoeff, sq, Finset.sum_mul_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  simp_rw [he]
  exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
    (tendsto_schauder_sum_mul (t i).2 (t j).2).const_mul _

/-- **Finite-dimensional laws of Brownian motion.** For a finite family of times `t i` and
coefficients `c i`, `Σ_i c i B(t i)` is centred Gaussian with variance
`Σ_{i,j} c i c j min (t i) (t j)`.
Cochrane (2023), Online Appendix A1 §1.6, pp. 567–568: infrastructure for (1.32) with
diffusive bonds. Restated from MeynTweedie.LimitTheorems.gaussSeq_map_sum_brownian
(LeanDynamicProgramming, StochasticStability/LimitTheorems/LimitTheorems/BrownianMotion.lean).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianUnit.gaussSeq_map_sum_brownian). -/
theorem gaussSeq_map_sum_brownian {ι : Type*} [Fintype ι] (t : ι → unitInterval) (c : ι → ℝ) :
    gaussSeq.map (fun ω => ∑ i, c i * brownian (t i) ω) = gaussianReal 0 (bmVar t c).toNNReal := by
  have := isProbabilityMeasure_gaussSeq
  refine map_eq_gaussianReal_of_tendsto
    (X := fun N ω => ∑ m ∈ Finset.range (2 ^ N), bmCoeff t c m * ω m)
    (v := fun N => (∑ m ∈ Finset.range (2 ^ N), bmCoeff t c m ^ 2).toNNReal)
    (fun N => (Finset.measurable_sum _ fun m _ =>
      measurable_const.mul (measurable_pi_apply m)).aemeasurable)
    (fun N => gaussSeq_map_sum _ _) ?_
    ((continuous_real_toNNReal.tendsto _).comp (tendsto_sum_bmCoeff_sq t c))
  filter_upwards [ae_mem_lcGood] with ω hω
  have he : ∀ N, ∑ m ∈ Finset.range (2 ^ N), bmCoeff t c m * ω m
      = ∑ i, c i * ∑ m ∈ Finset.range (2 ^ N), ω m * schauder m (t i) := by
    intro N
    simp_rw [bmCoeff, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  simp_rw [he]
  exact tendsto_finsetSum _ fun i _ => (tendsto_lcPartial_apply hω (t i)).const_mul _

/-! ### Gaussian process and covariance -/

/-- Any finite vector `(B(u i))_i` of values of Brownian motion is jointly Gaussian.
Cochrane (2023), Online Appendix A1 §1.6, pp. 567–568: infrastructure for (1.32) with
diffusive bonds. Restated from MeynTweedie.LimitTheorems.hasGaussianLaw_brownian_vec
(LeanDynamicProgramming, StochasticStability/LimitTheorems/LimitTheorems/BrownianMotion.lean).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianUnit.hasGaussianLaw_brownian_vec). -/
theorem hasGaussianLaw_brownian_vec {ι : Type*} [Finite ι] (u : ι → unitInterval) :
    HasGaussianLaw (fun ω i => brownian (u i) ω) gaussSeq := by
  classical
  have := Fintype.ofFinite ι
  have hV : Measurable fun ω (i : ι) => brownian (u i) ω :=
    Measurable.of_eval fun i => measurable_brownian (u i)
  refine ⟨hV.aemeasurable, isGaussian_of_map_eq_gaussianReal fun L =>
    ⟨0, (bmVar u fun i => L fun j => if i = j then 1 else 0).toNNReal, ?_⟩⟩
  rw [Measure.map_map L.continuous.measurable hV]
  have hL : (L ∘ fun ω (i : ι) => brownian (u i) ω)
      = fun ω => ∑ i, L (fun j => if i = j then 1 else 0) * brownian (u i) ω := by
    funext ω
    rw [Function.comp_apply, ← ContinuousLinearMap.coe_coe, LinearMap.pi_apply_eq_sum_univ]
    simp_rw [smul_eq_mul, mul_comm (brownian _ ω)]
  rw [hL]
  exact gaussSeq_map_sum_brownian u _

/-- Brownian motion is a Gaussian process (in Mathlib's sense, `IsGaussianProcess`).
Cochrane (2023), Online Appendix A1 §1.6, pp. 567–568: infrastructure for (1.32) with
diffusive bonds. Restated from MeynTweedie.LimitTheorems.isGaussianProcess_brownian
(LeanDynamicProgramming, StochasticStability/LimitTheorems/LimitTheorems/BrownianMotion.lean).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianUnit.isGaussianProcess_brownian). -/
theorem isGaussianProcess_brownian : IsGaussianProcess brownian gaussSeq :=
  ⟨fun I => hasGaussianLaw_brownian_vec (fun i : I => (i : unitInterval))⟩

/-- Each `B(t)` is square integrable.
Cochrane (2023), Online Appendix A1 §1.6, pp. 567–568: infrastructure for (1.32) with
diffusive bonds. Restated from MeynTweedie.LimitTheorems.memLp_brownian
(LeanDynamicProgramming, StochasticStability/LimitTheorems/LimitTheorems/BrownianMotion.lean).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianUnit.memLp_brownian). -/
lemma memLp_brownian (t : unitInterval) : MemLp (brownian t) 2 gaussSeq :=
  (isGaussianProcess_brownian.hasGaussianLaw_eval t).memLp_two

/-- The variance of a random variable with law `N(μ, v)` is `v`.
Cochrane (2023), Online Appendix A1 §1.6, pp. 567–568: infrastructure for (1.32) with
diffusive bonds. Restated from MeynTweedie.LimitTheorems.variance_of_map_eq_gaussianReal
(LeanDynamicProgramming, StochasticStability/LimitTheorems/LimitTheorems/BrownianMotion.lean).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianUnit.variance_of_map_eq_gaussianReal). -/
lemma variance_of_map_eq_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : AEMeasurable X P) {μ : ℝ} {v : ℝ≥0} (h : P.map X = gaussianReal μ v) :
    Var[X; P] = v := by
  have := variance_map (X := id) (μ := P) measurable_id.aemeasurable hX
  rw [h, variance_id_gaussianReal] at this
  exact this.symm

/-- `B(t)` has law `N(0, t)`.
Cochrane (2023), Online Appendix A1 §1.6, pp. 567–568: infrastructure for (1.32) with
diffusive bonds. Restated from MeynTweedie.LimitTheorems.gaussSeq_map_brownian
(LeanDynamicProgramming, StochasticStability/LimitTheorems/LimitTheorems/BrownianMotion.lean).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianUnit.gaussSeq_map_brownian). -/
theorem gaussSeq_map_brownian (t : unitInterval) :
    gaussSeq.map (brownian t) = gaussianReal 0 (t : ℝ).toNNReal := by
  have h := gaussSeq_map_sum_brownian (fun _ : Unit => t) (fun _ => 1)
  simp only [Finset.univ_unique, Finset.sum_singleton, one_mul, bmVar, mul_one, min_self] at h
  exact h

/-- **Covariance of Brownian motion**: `Cov(B(s), B(t)) = min s t`.
Cochrane (2023), Online Appendix A1 §1.6, pp. 567–568: infrastructure for (1.32) with
diffusive bonds. Restated from MeynTweedie.LimitTheorems.covariance_brownian
(LeanDynamicProgramming, StochasticStability/LimitTheorems/LimitTheorems/BrownianMotion.lean).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianUnit.covariance_brownian). -/
theorem covariance_brownian (s t : unitInterval) :
    cov[brownian s, brownian t; gaussSeq] = min (s : ℝ) t := by
  have := isProbabilityMeasure_gaussSeq
  have hsum := gaussSeq_map_sum_brownian ![s, t] ![1, 1]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, bmVar,
    mul_one, min_self] at hsum
  have hvs := variance_of_map_eq_gaussianReal (measurable_brownian s).aemeasurable
    (gaussSeq_map_brownian s)
  have hvt := variance_of_map_eq_gaussianReal (measurable_brownian t).aemeasurable
    (gaussSeq_map_brownian t)
  have hv := variance_of_map_eq_gaussianReal
    ((measurable_brownian s).add (measurable_brownian t)).aemeasurable hsum
  have hadd := variance_add (memLp_brownian s) (memLp_brownian t)
  have hs0 : (0 : ℝ) ≤ s := s.2.1
  have ht0 : (0 : ℝ) ≤ t := t.2.1
  have hm0 : (0 : ℝ) ≤ min (s : ℝ) t := le_min hs0 ht0
  rw [Real.coe_toNNReal _ hs0] at hvs
  rw [Real.coe_toNNReal _ ht0] at hvt
  rw [min_comm (t : ℝ) s, Real.coe_toNNReal _ (by linarith)] at hv
  rw [hvs, hvt] at hadd
  linarith

end Cochrane.Generality.TidyR7BrownianUnit
