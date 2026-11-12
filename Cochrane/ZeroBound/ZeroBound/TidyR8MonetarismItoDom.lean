/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR7ItoBondStep
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Pi
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Setoid.Basic
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Process.Filtration
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Order.IntermediateValue

/-!
# Itô-integral tools from the dominated form of (1.33): additivity over intervals

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.32)–(1.33); used for the stochastic Werning model of
Chapter 20, §20.2, pp. 474–476.

The mathematical part of the Cochrane Monetarism module TidyR8MonetarismItoDom, restated so that
the Doob and martingale-representation modules can be used here without the Monetarism
economics (the valuation equation (1.33) and its flows, which this project does not need, are
not restated). The Mathlib imports of the Monetarism economics modules that the source module
imported are kept, so that the copied modules below see the same Mathlib environment.

## Main results

* `itoInt_add_itoInt_ms` (additivity of the Itô integral over intervals for mean-square
  continuous integrands; generalises `TidyR7ItoIntegral.itoInt_add_itoInt`),
* `itoInt_ae_zero_of_vanish`, `itoInt_eventually_const`, `abs_intervalIntegral_le_Ioi`.
-/

namespace Cochrane.ZeroBound.TidyR8MonetarismItoDom

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.TidyR7StieltjesSums Cochrane.ZeroBound.TidyR7BrownianTools
  Cochrane.ZeroBound.TidyR7BrownianQV Cochrane.ZeroBound.TidyR7ItoL2
  Cochrane.ZeroBound.TidyR7ItoSums Cochrane.ZeroBound.TidyR7ItoIntegral
  Cochrane.ZeroBound.TidyR7ItoUnbounded
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ## Itô-integral tools -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: additivity over intervals for mean-square continuous
integrands**: `∫_s^t G dW = ∫_s^r G dW + ∫_r^t G dW` a.s. for `0 ≤ s ≤ r ≤ t`.
Generalises `TidyR7ItoIntegral.itoInt_add_itoInt` (bounded integrands); the proof is the same
with `TidyR7ItoUnbounded.L2Tendsto_itoSum_ms`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR8MonetarismItoDom.itoInt_add_itoInt_ms). -/
theorem itoInt_add_itoInt_ms {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ}
    {G : ℝ → Ω → ℝ} (hB : IsPreBrownianReal W μ) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) {s r t : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hrt : r ≤ t)
    (hG : MSIntegrand μ 𝓕 G s t) :
    itoInt μ 𝓕 W G s t =ᵐ[μ] fun ω => itoInt μ 𝓕 W G s r ω + itoInt μ 𝓕 W G r t ω := by
  rcases hsr.lt_or_eq with hsr | hsr
  · rcases hrt.lt_or_eq with hrt | hrt
    · set ps : ℕ → Partition s t := fun k => concat (dyadic hsr k) (dyadic hrt k) with hps_def
      have hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0) := by
        refine squeeze_zero (fun k => mesh_nonneg _) (fun k => mesh_concat_le _ _) ?_
        simpa using (tendsto_mesh_dyadic hsr).max (tendsto_mesh_dyadic hrt)
      have h1 := L2Tendsto_itoSum_ms hB hW h𝓕 hs (hsr.trans hrt) hG ps hps
      have h2 := ((L2Tendsto_dyadic_ms hB hW h𝓕 hs hsr (hG.mono le_rfl hrt.le)).add
        (L2Tendsto_dyadic_ms hB hW h𝓕 (hs.trans hsr.le) hrt (hG.mono hsr.le le_rfl))).congr_seq
          (fun k => ae_of_all _ fun ω => (itoSum_concat G _ _ ω).symm)
      exact ae_eq_of_L2Tendsto h1 h2
    · have e : itoInt μ 𝓕 W G r t = 0 := itoInt_of_le hrt.ge
      refine ae_of_all _ fun ω => ?_
      rw [e, ← hrt]
      simp
  · have e : itoInt μ 𝓕 W G s r = 0 := itoInt_of_le hsr.ge
    refine ae_of_all _ fun ω => ?_
    rw [e, ← hsr]
    simp

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the Itô integral of an integrand vanishing on
`[r, t]` is `0` a.s.** (every left-point sum is `0`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR8MonetarismItoDom.itoInt_ae_zero_of_vanish). -/
theorem itoInt_ae_zero_of_vanish {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ}
    {G : ℝ → Ω → ℝ} {r t : ℝ} (hG0 : ∀ u ∈ Set.Icc r t, ∀ ω, G u ω = 0) :
    itoInt μ 𝓕 W G r t =ᵐ[μ] 0 := by
  rcases lt_or_ge r t with hrt | htr
  · have e : ∀ k, itoSum W G (dyadic hrt k) = 0 := fun k => funext fun ω => by
      unfold itoSum
      exact Finset.sum_eq_zero fun i hi => by
        simp only [hG0 _ (t_mem _ (Finset.mem_range.1 hi).le) ω, zero_mul]
    have hL : L2Tendsto μ (fun k => itoSum W G (dyadic hrt k)) 0 :=
      ⟨fun k => by change MemLp (itoSum W G (dyadic hrt k)) 2 μ; rw [e k]; exact MemLp.zero,
        MemLp.zero, by simp [e]⟩
    exact ae_eq_of_L2Tendsto (itoInt_spec hrt ⟨0, stronglyMeasurable_zero, hL⟩).2 hL
  · rw [itoInt_of_le htr]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: an Itô integral whose integrand vanishes after
`T*` is constant after `T*`**: `∫_s^T G dW = ∫_s^{T*} G dW` a.s. for `0 ≤ s ≤ T* ≤ T`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR8MonetarismItoDom.itoInt_eventually_const). -/
theorem itoInt_eventually_const {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ}
    {G : ℝ → Ω → ℝ} (hB : IsPreBrownianReal W μ) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) {s Ts T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ Ts) (hTT : Ts ≤ T)
    (hG : MSIntegrand μ 𝓕 G s T) (hG0 : ∀ u, Ts ≤ u → ∀ ω, G u ω = 0) :
    itoInt μ 𝓕 W G s T =ᵐ[μ] itoInt μ 𝓕 W G s Ts := by
  filter_upwards [itoInt_add_itoInt_ms hB hW h𝓕 hs hsT hTT hG,
    itoInt_ae_zero_of_vanish (μ := μ) (𝓕 := 𝓕) (W := W) (r := Ts) (t := T)
      (fun u hu ω => hG0 u hu.1 ω)] with ω h1 h2
  rw [h1, h2, Pi.zero_apply, add_zero]

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567 (tool): `|∫_s^T f| ≤ ∫_s^∞ |f|` for `s ≤ T` and `f`
integrable on `(s, ∞)`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR8MonetarismItoDom.abs_intervalIntegral_le_Ioi). -/
theorem abs_intervalIntegral_le_Ioi {f : ℝ → ℝ} {s T : ℝ} (hsT : s ≤ T)
    (hf : IntegrableOn f (Set.Ioi s)) : |∫ u in s..T, f u| ≤ ∫ u in Set.Ioi s, |f u| := by
  rw [intervalIntegral.integral_of_le hsT]
  calc |∫ u in Set.Ioc s T, f u| ≤ ∫ u in Set.Ioc s T, |f u| := abs_integral_le_integral_abs
    _ ≤ ∫ u in Set.Ioi s, |f u| :=
      setIntegral_mono_set hf.abs (ae_of_all _ fun _ => abs_nonneg _)
        Set.Ioc_subset_Ioi_self.eventuallyLE

end Cochrane.ZeroBound.TidyR8MonetarismItoDom
