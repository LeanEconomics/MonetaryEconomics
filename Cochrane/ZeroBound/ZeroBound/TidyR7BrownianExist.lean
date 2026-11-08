/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR7BrownianUnit
import Mathlib.Probability.BrownianMotion.Basic

/-!
# Brownian motion on `[0, ∞)` exists (Mathlib's `IsBrownianReal`)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). The continuous-time stochastic step (1.32)
`E_t d(BΛ/P) = Λ dB/P + B E_t d(Λ/P)` needs, for bonds or discount factors with a diffusive
component, a Brownian integrator. Mathlib v4.34 defines `ProbabilityTheory.IsBrownianReal`
(index `ℝ≥0`, the Brownian finite-dimensional laws and a.s. continuous paths) but proves no
existence theorem. This module (chunk I5a, infrastructure for (1.32) with diffusive bonds)
supplies one.

## Route: time change of the `[0,1]` motion (no gluing of independent copies)

With `B` the Lévy–Ciesielski Brownian motion on `[0,1]` (`TidyR7BrownianUnit.brownian`, on the
Gaussian sequence space `(ℕ → ℝ, gaussSeq)`), put `u(t) = t/(1+t) ∈ [0,1)` (`bmTime`) and
`W(t) = (1+t) B(u(t)) − t B(1)` (`bmPath`). Then `W(t) = (1+t) β(u(t))` for the Brownian bridge
`β(u) = B(u) − u B(1)`, whose covariance is `min(u,v) − uv`; for `s ≤ t`,
`(1+s)(1+t)(u(s) − u(s)u(t)) = s`. So `W` is a centred Gaussian process with covariance
`min s t`. This is shorter than gluing independent copies on `ℕ × ℕ → ℝ`: one Gaussian sequence,
no floor/fractional-part bookkeeping, no independence across blocks, and every path is
continuous because `u` and `B(·, ω)` are.

## Main results

* `continuous_bmPath`, `bmPath_zero`, `measurable_bmPath`: EVERY path is continuous, starts at
  `0`, and each `W t` is measurable.
* `isGaussianProcess_bmPath` (Mathlib `IsGaussianProcess` on `ℝ≥0`), `integral_bmPath`
  (centred), `covariance_bmPath` (`cov[W s, W t] = min s t`).
* `isPreBrownianReal_bmPath`, `isBrownianReal_bmPath`: Mathlib's predicates hold.
* `exists_isBrownianReal`, `exists_isBrownianReal_measurable_continuous` (headline).
* Non-vacuity: `bmPath_one` (`W 1 = 2 B(1/2) − B(1)` pathwise) and `hasLaw_bmPath_two_sub_half`
  (`W 2 − W (1/2) ~ N(0, 3/2)`).
-/

namespace Cochrane.ZeroBound.TidyR7BrownianExist

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.TidyR7BrownianSchauder Cochrane.ZeroBound.TidyR7BrownianUnit
open scoped ENNReal NNReal

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (infrastructure for (1.32) with diffusive bonds): the
time change `u(t) = t/(1+t)`, mapping `[0, ∞)` into `[0, 1)`.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7BrownianExist.bmTime). -/
noncomputable def bmTime (t : ℝ≥0) : unitInterval :=
  ⟨(t : ℝ) / (1 + t), div_nonneg t.coe_nonneg (by positivity),
    (div_le_one (by positivity)).2 (by linarith)⟩

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the value of the time change `bmTime`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianExist.coe_bmTime). -/
lemma coe_bmTime (t : ℝ≥0) : ((bmTime t : unitInterval) : ℝ) = (t : ℝ) / (1 + t) := rfl

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the time change `bmTime` is continuous.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianExist.continuous_bmTime). -/
lemma continuous_bmTime : Continuous bmTime := by
  refine Continuous.subtype_mk ?_ _
  exact NNReal.continuous_coe.div (continuous_const.add NNReal.continuous_coe)
    fun t => by positivity

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the time change starts at `0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianExist.bmTime_zero). -/
lemma bmTime_zero : bmTime 0 = 0 := by
  ext
  simp [coe_bmTime]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the time change is monotone,
`s ≤ t → s/(1+s) ≤ t/(1+t)`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianExist.coe_bmTime_mono). -/
lemma coe_bmTime_mono {s t : ℝ≥0} (hst : s ≤ t) :
    ((bmTime s : unitInterval) : ℝ) ≤ bmTime t := by
  have h : (s : ℝ) ≤ t := hst
  have hs : (0 : ℝ) ≤ s := s.coe_nonneg
  rw [coe_bmTime, coe_bmTime, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (infrastructure for (1.32) with diffusive bonds):
**the Brownian motion on `[0, ∞)`**, `W(t) = (1+t) B(t/(1+t)) − t B(1)` for the `[0,1]` motion
`B = brownian` on the Gaussian sequence space `(ℕ → ℝ, gaussSeq)`.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7BrownianExist.bmPath). -/
noncomputable def bmPath (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  (1 + (t : ℝ)) * brownian (bmTime t) ω - t * brownian 1 ω

/-- Cochrane (2023), A1 §1.6, pp. 567–568: every path of `bmPath` is continuous.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianExist.continuous_bmPath). -/
theorem continuous_bmPath (ω : ℕ → ℝ) : Continuous fun t => bmPath t ω := by
  have h : Continuous fun t => brownian (bmTime t) ω :=
    (continuous_brownian ω).comp continuous_bmTime
  exact ((continuous_const.add NNReal.continuous_coe).mul h).sub
    (NNReal.continuous_coe.mul continuous_const)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: every path of `bmPath` starts at `0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianExist.bmPath_zero). -/
theorem bmPath_zero (ω : ℕ → ℝ) : bmPath 0 ω = 0 := by
  simp [bmPath, bmTime_zero, brownian_zero]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: each `bmPath t` is measurable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianExist.measurable_bmPath). -/
theorem measurable_bmPath (t : ℝ≥0) : Measurable (bmPath t) :=
  (measurable_const.mul (measurable_brownian _)).sub (measurable_const.mul (measurable_brownian _))

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `bmPath` is a Gaussian process (Mathlib's
`IsGaussianProcess`): each `W t` is a fixed linear combination of the two values
`B(t/(1+t))`, `B(1)` of the Gaussian process `TidyR7BrownianUnit.brownian`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianExist.isGaussianProcess_bmPath). -/
theorem isGaussianProcess_bmPath : IsGaussianProcess bmPath gaussSeq := by
  classical
  refine isGaussianProcess_brownian.of_isGaussianProcess fun t => ?_
  let I : Finset unitInterval := {bmTime t, 1}
  have h1 : bmTime t ∈ I := by simp [I]
  have h2 : (1 : unitInterval) ∈ I := by simp [I]
  refine ⟨I, (1 + (t : ℝ)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℝ) ⟨_, h1⟩
    - (t : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℝ) ⟨_, h2⟩, fun ω => ?_⟩
  simp [bmPath, Finset.restrict]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: each `B(u)` of the `[0,1]` motion is centred.
The mean half of `TidyR7BrownianUnit.gaussSeq_map_brownian`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianExist.integral_brownian). -/
lemma integral_brownian (u : unitInterval) : ∫ ω, brownian u ω ∂gaussSeq = 0 := by
  have h : HasLaw (brownian u) (gaussianReal 0 (u : ℝ).toNNReal) gaussSeq :=
    ⟨(measurable_brownian u).aemeasurable, gaussSeq_map_brownian u⟩
  rw [h.integral_eq, integral_id_gaussianReal]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `bmPath` is centred, `E[W t] = 0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianExist.integral_bmPath). -/
theorem integral_bmPath (t : ℝ≥0) : ∫ ω, bmPath t ω ∂gaussSeq = 0 := by
  have := isProbabilityMeasure_gaussSeq
  unfold bmPath
  rw [integral_sub ((memLp_brownian _).integrable one_le_two |>.const_mul _)
    ((memLp_brownian _).integrable one_le_two |>.const_mul _), integral_const_mul,
    integral_const_mul, integral_brownian, integral_brownian]
  ring

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **covariance of `bmPath`**: for `s ≤ t`,
`cov[W s, W t] = s` (Brownian-bridge covariance `min(u,v) − uv` times `(1+s)(1+t)`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianExist.covariance_bmPath). -/
theorem covariance_bmPath {s t : ℝ≥0} (hst : s ≤ t) :
    cov[bmPath s, bmPath t; gaussSeq] = s := by
  have := isProbabilityMeasure_gaussSeq
  have hs := memLp_brownian (bmTime s)
  have ht := memLp_brownian (bmTime t)
  have h1 := memLp_brownian 1
  have hS : bmPath s = fun ω => (1 + (s : ℝ)) * brownian (bmTime s) ω - s * brownian 1 ω := rfl
  have hT : bmPath t = fun ω => (1 + (t : ℝ)) * brownian (bmTime t) ω - t * brownian 1 ω := rfl
  have hZ : MemLp (fun ω => (1 + (t : ℝ)) * brownian (bmTime t) ω - t * brownian 1 ω) 2
      gaussSeq := (ht.const_mul _).sub (h1.const_mul _)
  rw [hS, hT, covariance_fun_sub_left (hs.const_mul _) (h1.const_mul _) hZ,
    covariance_fun_sub_right (hs.const_mul _) (ht.const_mul _) (h1.const_mul _),
    covariance_fun_sub_right (h1.const_mul _) (ht.const_mul _) (h1.const_mul _)]
  simp only [covariance_const_mul_left, covariance_const_mul_right, covariance_brownian]
  have hm := coe_bmTime_mono hst
  have hs1 : ((bmTime s : unitInterval) : ℝ) ≤ 1 := (bmTime s).2.2
  have ht1 : ((bmTime t : unitInterval) : ℝ) ≤ 1 := (bmTime t).2.2
  rw [min_eq_left hm]
  simp only [Set.Icc.coe_one, min_self]
  rw [min_eq_left hs1, min_eq_right ht1, coe_bmTime, coe_bmTime]
  have h0 : (0 : ℝ) ≤ s := s.coe_nonneg
  have h0' : (0 : ℝ) ≤ t := t.coe_nonneg
  field_simp
  ring

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (infrastructure for (1.32) with diffusive bonds):
`bmPath` is a pre-Brownian motion (Mathlib's `IsPreBrownianReal`), by
`IsGaussianProcess.isPreBrownianReal_of_covariance`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianExist.isPreBrownianReal_bmPath). -/
theorem isPreBrownianReal_bmPath : IsPreBrownianReal bmPath gaussSeq :=
  isGaussianProcess_bmPath.isPreBrownianReal_of_covariance integral_bmPath
    fun _ _ hst => covariance_bmPath hst

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (infrastructure for (1.32) with diffusive bonds):
**`bmPath` is a Brownian motion** (Mathlib's `IsBrownianReal`); its paths are continuous for
EVERY `ω`, not only almost surely.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianExist.isBrownianReal_bmPath). -/
theorem isBrownianReal_bmPath : IsBrownianReal bmPath gaussSeq :=
  ⟨isPreBrownianReal_bmPath, Eventually.of_forall continuous_bmPath⟩

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (infrastructure for (1.32) with diffusive bonds):
**a Brownian motion on `[0, ∞)` exists**, in the sense of Mathlib's `IsBrownianReal`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianExist.exists_isBrownianReal). -/
theorem exists_isBrownianReal :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (W : ℝ≥0 → Ω → ℝ), IsBrownianReal W P :=
  ⟨ℕ → ℝ, inferInstance, gaussSeq, isProbabilityMeasure_gaussSeq, bmPath, isBrownianReal_bmPath⟩

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the existence theorem in the form the tools of
`TidyR7BrownianTools` use: a Brownian motion with each `W t` measurable and with EVERY path
continuous and starting at `0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianExist.exists_isBrownianReal_measurable_continuous). -/
theorem exists_isBrownianReal_measurable_continuous :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (W : ℝ≥0 → Ω → ℝ), IsBrownianReal W P ∧ (∀ t, Measurable (W t)) ∧
        ∀ ω, Continuous (fun t => W t ω) ∧ W 0 ω = 0 :=
  ⟨ℕ → ℝ, inferInstance, gaussSeq, isProbabilityMeasure_gaussSeq, bmPath, isBrownianReal_bmPath,
    measurable_bmPath, fun ω => ⟨continuous_bmPath ω, bmPath_zero ω⟩⟩

/-- Cochrane (2023), A1 §1.6, pp. 567–568: pathwise, `W 1 = 2 B(1/2) − B(1)`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianExist.bmPath_one). -/
theorem bmPath_one (ω : ℕ → ℝ) :
    bmPath 1 ω = 2 * brownian (bmTime 1) ω - brownian 1 ω ∧
      ((bmTime 1 : unitInterval) : ℝ) = 1 / 2 := by
  refine ⟨?_, ?_⟩
  · simp only [bmPath, NNReal.coe_one, one_mul]
    norm_num
  · rw [coe_bmTime]
    norm_num

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (non-vacuity): on the constructed process,
`W 2 − W (1/2)` has law `N(0, 3/2)`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianExist.hasLaw_bmPath_two_sub_half). -/
theorem hasLaw_bmPath_two_sub_half :
    HasLaw (bmPath 2 - bmPath (1 / 2)) (gaussianReal 0 (3 / 2)) gaussSeq := by
  have h := isPreBrownianReal_bmPath.hasLaw_sub 2 (1 / 2)
  have e : nndist (2 : ℝ≥0).1 (1 / 2 : ℝ≥0).1 = 3 / 2 := by
    ext
    rw [coe_nndist, Real.dist_eq]
    norm_num
  rwa [e] at h

end Cochrane.ZeroBound.TidyR7BrownianExist
