/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR7BrownianQV
import ZeroBound.TidyR7ProductStep

/-!
# Brownian paths have infinite variation; cross variation against bounded-variation paths

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for (1.32) with diffusive
bonds (chunk I5b, consequences of the quadratic variation `TidyR7BrownianQV`).

## Main results

* `tendsto_qvSum_zero_of_bv`: a continuous path of bounded variation on `[s, t]` has
  `Σ(ΔW_i)² → 0` along every sequence of partitions with mesh `→ 0` (Track 1's
  `TidyR7StieltjesSums.tendsto_crossSum_zero` with `f = g` the path; this is
  `Σ(ΔW)² ≤ max|ΔW|·Σ|ΔW|`).
* **Infinite variation** (item 4): `ae_not_bv` (for `0 ≤ s < t`, almost every path is not of
  bounded variation on `[s, t]`), `ae_forall_not_bv` (almost surely, simultaneously on EVERY
  `[s, t]` with `0 ≤ s < t`), `ae_forall_eVariationOn_eq_top` (the variation is `∞`).
* **Why a stochastic integral is needed** (item 4): `not_productStepData_bm`: the setting
  `TidyR7ProductStep.ProductStepData` of the Track 1 product step requires bonds whose paths
  are continuous and of bounded variation (`TidyR7ProductStep.ProductStepData.B_bv`); a
  Brownian bond position `B = W` admits NO such data. The pathwise Riemann–Stieltjes integral
  `∫ X dB` of I1–I4 is therefore unavailable for diffusive bonds, and `∫ X dW` must be built as
  an `L²` limit (I5c).
* **Cross variation** (item 5): `tendsto_crossSum_bm_bv`, `ae_tendsto_sumCross_bm_bv`: for a
  continuous `W` path and a continuous path of bounded variation `B`, `Σ ΔW_iΔB_i → 0`
  along every sequence of partitions with mesh `→ 0`, path by path; `tendsto_crossSum_bm_id`:
  `Σ ΔW_iΔt_i → 0` (`dW·dt = 0`). This is the cross sum that the Track 1 product step drops,
  so that step survives when `Λ/P` has a Brownian part and bonds are of bounded variation.
* Non-vacuity (item 6) on the constructed motion `TidyR7BrownianExist.bmPath`:
  `integral_qvSum_sub_sq_bmPath`, `tendstoInMeasure_qvSum_bmPath`,
  `ae_tendsto_qvSum_dyadic_bmPath`, `ae_forall_not_bv_bmPath`, `not_productStepData_bmPath`,
  `tendsto_crossSum_bmPath_id`, `condExp_qvSum_sub_sq_bmPath`.
-/

namespace Cochrane.ZeroBound.TidyR7BrownianVariation

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.TidyR7StieltjesSums Cochrane.ZeroBound.TidyR7BrownianTools
  Cochrane.ZeroBound.TidyR7BrownianQV Cochrane.ZeroBound.TidyR7ProductStep
  Cochrane.ZeroBound.TidyR7BrownianSchauder Cochrane.ZeroBound.TidyR7BrownianExist
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

/-! ## Bounded-variation paths have zero quadratic variation -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: a continuous path of `W` gives a càdlàg path of
`bmReal W` on `ℝ`. Mathlib `Continuous.isCadlag`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianVariation.isCadlag_bmReal). -/
theorem isCadlag_bmReal {ω : Ω} (hc : Continuous fun t => W t ω) :
    IsCadlag fun u => bmReal W u ω :=
  (continuous_bmReal hc).isCadlag

/-- Cochrane (2023), A1 §1.6, pp. 567–568: if a continuous path were of bounded variation on
`[s, t]`, its quadratic variation sums would tend to `0` along every sequence of partitions
with mesh `→ 0`.
The `f = g` case of `TidyR7StieltjesSums.tendsto_crossSum_zero`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianVariation.tendsto_qvSum_zero_of_bv). -/
theorem tendsto_qvSum_zero_of_bv {s t : ℝ} {ω : Ω} (hc : Continuous fun t => W t ω)
    (hbv : BoundedVariationOn (fun u => bmReal W u ω) (Set.Icc s t)) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => qvSum W (ps k) ω) atTop (𝓝 0) := by
  simp_rw [qvSum_eq_crossSum]
  exact tendsto_crossSum_zero (isCadlag_bmReal hc) hbv (continuous_bmReal hc).continuousOn ps hps

/-! ## Infinite variation -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: Brownian paths have infinite variation.** For
`0 ≤ s < t`, almost every path of `W` is NOT of bounded variation on `[s, t]` (its dyadic
quadratic variation tends to `t − s > 0`, `TidyR7BrownianQV.ae_tendsto_qvSum_dyadic`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianVariation.ae_not_bv). -/
theorem ae_not_bv (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    ∀ᵐ ω ∂P, ¬ BoundedVariationOn (fun u => bmReal W u ω) (Set.Icc s t) := by
  filter_upwards [ae_tendsto_qvSum_dyadic hB hW hs hst, hcont] with ω h1 h2 hbv
  have h0 := tendsto_qvSum_zero_of_bv h2 hbv (dyadic hst) (tendsto_mesh_dyadic hst)
  have := tendsto_nhds_unique h1 h0
  linarith

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: almost surely, a Brownian path has infinite
variation on EVERY interval** `[s, t]` with `0 ≤ s < t` (one null set for all intervals:
the rational intervals are countable and every `[s, t]` contains one).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianVariation.ae_forall_not_bv). -/
theorem ae_forall_not_bv (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ, 0 ≤ s → s < t →
      ¬ BoundedVariationOn (fun u => bmReal W u ω) (Set.Icc s t) := by
  have h : ∀ q : ℚ × ℚ, ∀ᵐ ω ∂P, 0 ≤ (q.1 : ℝ) → (q.1 : ℝ) < q.2 →
      ¬ BoundedVariationOn (fun u => bmReal W u ω) (Set.Icc (q.1 : ℝ) q.2) := by
    intro q
    by_cases hq : 0 ≤ (q.1 : ℝ) ∧ (q.1 : ℝ) < q.2
    · filter_upwards [ae_not_bv hB hW hcont hq.1 hq.2] with ω hω _ _ using hω
    · exact ae_of_all _ fun _ h1 h2 => absurd ⟨h1, h2⟩ hq
  filter_upwards [ae_all_iff.2 h] with ω hω s t hs hst hbv
  obtain ⟨q1, hsq1, hq1⟩ := exists_rat_btwn hst
  obtain ⟨q2, hq12, hq2⟩ := exists_rat_btwn hq1
  exact hω (q1, q2) (hs.trans hsq1.le) hq12 (hbv.mono (Set.Icc_subset_Icc hsq1.le hq2.le))

/-- Cochrane (2023), A1 §1.6, pp. 567–568: almost surely the variation of a Brownian path is
`∞` on every `[s, t]` with `0 ≤ s < t`.
Restates `ae_forall_not_bv` in `eVariationOn` form.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianVariation.ae_forall_eVariationOn_eq_top). -/
theorem ae_forall_eVariationOn_eq_top (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ, 0 ≤ s → s < t →
      eVariationOn (fun u => bmReal W u ω) (Set.Icc s t) = ∞ := by
  filter_upwards [ae_forall_not_bv hB hW hcont] with ω hω s t hs hst
  exact not_not.1 (hω s t hs hst)

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the Track 1 product step does not apply to
diffusive bonds.** For `0 ≤ s < t`, there is no `TidyR7ProductStep.ProductStepData` with
bond position `B = W`: that setting needs every bond path to be of bounded variation on
`[s, t]`, and Brownian paths are not (`ae_not_bv`). Hence the pathwise Riemann–Stieltjes
integral `∫ (Λ/P) dB` of I1–I4 is unavailable, and a stochastic integral is needed.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianVariation.not_productStepData_bm). -/
theorem not_productStepData_bm (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (𝓕 : Filtration ℝ mΩ) (A M : ℝ → Ω → ℝ) :
    ProductStepData P 𝓕 s t (bmReal W) A M → False := by
  intro hd
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨ω, hω⟩ := (ae_not_bv hB hW hcont hs hst).exists
  exact hω (hd.B_bv ω)

/-! ## Cross variation against bounded-variation paths -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `dW·dB = 0` for bounded-variation `B`.** For a
continuous path of `W` and a path `g` continuous and of bounded variation on `[s, t]`,
`Σ ΔW_iΔg_i → 0` along every sequence of partitions with mesh `→ 0`.
The case `f = bmReal W` of `TidyR7StieltjesSums.tendsto_crossSum_zero`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianVariation.tendsto_crossSum_bm_bv). -/
theorem tendsto_crossSum_bm_bv {s t : ℝ} {ω : Ω} (hc : Continuous fun t => W t ω) {g : ℝ → ℝ}
    (hg : BoundedVariationOn g (Set.Icc s t)) (hgc : ContinuousOn g (Set.Icc s t))
    (ps : ℕ → Partition s t) (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => crossSum (ps k) (fun u => bmReal W u ω) g) atTop (𝓝 0) :=
  tendsto_crossSum_zero (isCadlag_bmReal hc) hg hgc ps hps

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: **the cross sum of Brownian motion and a bond
process `B` with continuous bounded-variation paths vanishes almost surely**, along every
sequence of partitions with mesh `→ 0` (the sum `TidyR7ProductStep.sumCross`).
From `tendsto_crossSum_bm_bv`; the pathwise fact behind
`TidyR7ProductStep.ProductStepData.tendsto_condExp_cross`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianVariation.ae_tendsto_sumCross_bm_bv). -/
theorem ae_tendsto_sumCross_bm_bv (hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω) {s t : ℝ}
    {B : ℝ → Ω → ℝ} (hBc : ∀ ω, ContinuousOn (fun u => B u ω) (Set.Icc s t))
    (hBbv : ∀ ω, BoundedVariationOn (fun u => B u ω) (Set.Icc s t)) :
    ∀ᵐ ω ∂P, ∀ ps : ℕ → Partition s t, Tendsto (fun k => mesh (ps k)) atTop (𝓝 0) →
      Tendsto (fun k => sumCross (ps k) (bmReal W) B ω) atTop (𝓝 0) := by
  filter_upwards [hcont] with ω hω ps hps
  exact tendsto_crossSum_bm_bv hω (hBbv ω) (hBc ω) ps hps

/-- Cochrane (2023), A1 §1.6, p. 567: the identity `u ↦ u` is of bounded variation on
`[s, t]`. From Mathlib `MonotoneOn.boundedVariationOn`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianVariation.bv_id). -/
theorem bv_id (s t : ℝ) : BoundedVariationOn (fun u : ℝ => u) (Set.Icc s t) :=
  monotoneOn_id.boundedVariationOn (C := |s| + |t|) fun x hx => by
    rw [abs_le]
    constructor <;> cases abs_cases s <;> cases abs_cases t <;> linarith [hx.1, hx.2]

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (`dW·dt = 0`): for a continuous path of `W`,
`Σ ΔW_iΔt_i → 0` along every sequence of partitions with mesh `→ 0`.
The `g = id` case of `tendsto_crossSum_bm_bv`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianVariation.tendsto_crossSum_bm_id). -/
theorem tendsto_crossSum_bm_id {s t : ℝ} {ω : Ω} (hc : Continuous fun t => W t ω)
    (ps : ℕ → Partition s t) (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => crossSum (ps k) (fun u => bmReal W u ω) fun u => u) atTop (𝓝 0) :=
  tendsto_crossSum_bm_bv hc (bv_id s t) continuousOn_id ps hps

/-! ## Non-vacuity: the constructed motion -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (non-vacuity): the `L²` quadratic variation identity
for the constructed motion `TidyR7BrownianExist.bmPath`.
An instance of `TidyR7BrownianQV.integral_qvSum_sub_sq`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianVariation.integral_qvSum_sub_sq_bmPath). -/
theorem integral_qvSum_sub_sq_bmPath {s t : ℝ} (hs : 0 ≤ s) (p : Partition s t) :
    ∫ ω, (qvSum bmPath p ω - (t - s)) ^ 2 ∂gaussSeq
      = 2 * ∑ i ∈ Finset.range p.n, (p.t (i + 1) - p.t i) ^ 2 :=
  integral_qvSum_sub_sq isPreBrownianReal_bmPath measurable_bmPath hs p

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (non-vacuity): the conditional identity for
`TidyR7BrownianExist.bmPath` and its natural filtration.
An instance of `TidyR7BrownianQV.condExp_qvSum_sub_sq`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianVariation.condExp_qvSum_sub_sq_bmPath). -/
theorem condExp_qvSum_sub_sq_bmPath {s t : ℝ} (hs : 0 ≤ s) (p : Partition s t) :
    gaussSeq[fun ω => (qvSum bmPath p ω - (t - s)) ^ 2 | bmFiltrationReal bmPath
        measurable_bmPath s]
      =ᵐ[gaussSeq] fun _ => 2 * ∑ i ∈ Finset.range p.n, (p.t (i + 1) - p.t i) ^ 2 :=
  condExp_qvSum_sub_sq isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) hs p

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (non-vacuity): `Σ(ΔbmPath_i)² → t − s` in
probability along any sequence of partitions with mesh `→ 0`.
An instance of `TidyR7BrownianQV.tendstoInMeasure_qvSum`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianVariation.tendstoInMeasure_qvSum_bmPath). -/
theorem tendstoInMeasure_qvSum_bmPath {s t : ℝ} (hs : 0 ≤ s) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    TendstoInMeasure gaussSeq (fun k => qvSum bmPath (ps k)) atTop (fun _ => t - s) :=
  tendstoInMeasure_qvSum isPreBrownianReal_bmPath measurable_bmPath hs ps hps

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (non-vacuity): `Σ(ΔbmPath_i)² → t − s` almost surely
along the dyadic partitions.
An instance of `TidyR7BrownianQV.ae_tendsto_qvSum_dyadic`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianVariation.ae_tendsto_qvSum_dyadic_bmPath). -/
theorem ae_tendsto_qvSum_dyadic_bmPath {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    ∀ᵐ ω ∂gaussSeq, Tendsto (fun k => qvSum bmPath (dyadic hst k) ω) atTop (𝓝 (t - s)) :=
  ae_tendsto_qvSum_dyadic isPreBrownianReal_bmPath measurable_bmPath hs hst

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (non-vacuity): almost every path of
`TidyR7BrownianExist.bmPath` has infinite variation on every `[s, t]`, `0 ≤ s < t`.
An instance of `ae_forall_not_bv`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianVariation.ae_forall_not_bv_bmPath). -/
theorem ae_forall_not_bv_bmPath :
    ∀ᵐ ω ∂gaussSeq, ∀ s t : ℝ, 0 ≤ s → s < t →
      ¬ BoundedVariationOn (fun u => bmReal bmPath u ω) (Set.Icc s t) :=
  ae_forall_not_bv isPreBrownianReal_bmPath measurable_bmPath
    (ae_of_all _ continuous_bmPath)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (non-vacuity): no Track 1 product-step data has
the constructed motion as bond position.
An instance of `not_productStepData_bm`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianVariation.not_productStepData_bmPath). -/
theorem not_productStepData_bmPath {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (𝓕 : Filtration ℝ (MeasurableSpace.pi : MeasurableSpace (ℕ → ℝ))) (A M : ℝ → (ℕ → ℝ) → ℝ) :
    ProductStepData gaussSeq 𝓕 s t (bmReal bmPath) A M → False :=
  not_productStepData_bm isPreBrownianReal_bmPath measurable_bmPath
    (ae_of_all _ continuous_bmPath) hs hst 𝓕 A M

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (non-vacuity): for EVERY path of
`TidyR7BrownianExist.bmPath`, `Σ ΔW_iΔt_i → 0`.
An instance of `tendsto_crossSum_bm_id`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianVariation.tendsto_crossSum_bmPath_id). -/
theorem tendsto_crossSum_bmPath_id {s t : ℝ} (ω : ℕ → ℝ) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => crossSum (ps k) (fun u => bmReal bmPath u ω) fun u => u) atTop (𝓝 0) :=
  tendsto_crossSum_bm_id (continuous_bmPath ω) ps hps

end Cochrane.ZeroBound.TidyR7BrownianVariation
