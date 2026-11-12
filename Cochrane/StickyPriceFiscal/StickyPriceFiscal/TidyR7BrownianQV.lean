/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.TidyR7BrownianTools
import StickyPriceFiscal.TidyR7StieltjesSums
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Quadratic variation of Brownian motion: `(dW)² = dt`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for (1.32) with diffusive
bonds (chunk I5b): the quadratic variation of a Brownian motion along partitions, unconditionally,
conditionally on `𝓕_s`, and weighted by an adapted bounded process (the rule `(dW)² = dt` that the
Itô isometry (I5c) and the product rule (I5d) use).

## Conventions

`W : ℝ≥0 → Ω → ℝ` is any pre-Brownian motion (`IsPreBrownianReal W P`) with measurable values
(`hW : ∀ t, Measurable (W t)`). Partitions are those of Track 1
(`TidyR7StieltjesSums.Partition s t`, index `ℝ`, mesh `TidyR7StieltjesSums.mesh`, dyadic partitions
`TidyR7StieltjesSums.dyadic`), with `0 ≤ s`, and the motion is read on `ℝ` through
`TidyR7BrownianTools.bmReal` (`bmReal W u = W (max u 0)`). On the time index `ℝ` an
**admissible filtration** `BMFiltration P W 𝓕` is one to which `bmReal W` is adapted and whose
`𝓕_u` is independent of every later increment; the natural one is `bmFiltrationReal_isBM`.

* `incr W u v = W_v − W_u`, `qvTerm W u v = (W_v − W_u)² − (v − u)`;
  `qvSum W p = Σ_i (ΔW_i)²`; `wqvSum W H p = Σ_i H_{t_i}((ΔW_i)² − Δt_i)`.

## Main results

* Moments: `integral_incr_sq` (`E(ΔW)² = Δt`), `integral_incr_pow_four` (`E(ΔW)⁴ = 3Δt²`),
  `integral_qvTerm` (`= 0`), `integral_qvTerm_sq` (`E[((ΔW)² − Δt)²] = 2Δt²`).
* Orthogonality: `integral_mul_qvTerm` (`E[Y((ΔW)² − Δt)] = 0` for `Y` `𝓕_u`-measurable) and
  `integral_mul_qvTerm_sq` (`E[Y((ΔW)² − Δt)²] = 2Δt²E[Y]`), from independence of the increment
  and the past.
* **Exact `L²` identities** (item 1): `integral_qvSum_sub_sq`:
  `E[(Σ(ΔW_i)² − (t − s))²] = 2Σ(Δt_i)²`, `integral_qvSum_sub_sq_le` (`≤ 2·mesh·(t − s)`);
  weighted, `integral_wqvSum_sq`: `E[(Σ H_i((ΔW_i)² − Δt_i))²] = 2Σ E[H_i²](Δt_i)²`,
  `integral_wqvSum_sq_le` (`≤ 2C²·mesh·(t − s)` when `|H| ≤ C`). Both are the case `G = 1` of
  `integral_mul_wqvSum_sq`: `E[G(Σ H_i((ΔW_i)² − Δt_i))²] = 2Σ E[GH_i²](Δt_i)²` for bounded
  `𝓕_s`-measurable `G`.
* **Conditional identities** (item 3): `condExp_wqvSum_sq`:
  `E[(Σ H_i((ΔW_i)² − Δt_i))² | 𝓕_s] = 2Σ E[H_i² | 𝓕_s](Δt_i)²` a.s.;
  `condExp_qvSum_sub_sq`: `E[(Σ(ΔW_i)² − (t − s))² | 𝓕_s] = 2Σ(Δt_i)²` a.s.
* **Convergence** along ANY sequence of partitions with mesh `→ 0`:
  `tendsto_integral_qvSum_sub_sq`, `tendsto_eLpNorm_qvSum_sub` (`L²`),
  `tendstoInMeasure_qvSum` (in probability); weighted: `tendsto_integral_wqvSum_sq`,
  `tendsto_eLpNorm_wqvSum` (`Σ H_i(ΔW_i)² − Σ H_iΔt_i → 0` in `L²`, the rule `(dW)² = dt`).
* **Almost sure convergence** (item 2): `ae_tendsto_qvSum_of_summable_mesh`
  (`Σ_k mesh_k < ∞`), `ae_tendsto_qvSum_dyadic` (dyadic partitions), by
  `ae_tendsto_zero_of_summable_integral_sq` (first Borel–Cantelli lemma in the form
  `Σ_k E[F_k²] < ∞ ⇒ F_k → 0` a.s., via `∫⁻ Σ_k F_k² < ∞`).
-/

namespace Cochrane.StickyPriceFiscal.TidyR7BrownianQV

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.StickyPriceFiscal.TidyR7StieltjesSums Cochrane.StickyPriceFiscal.TidyR7BrownianTools
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

/-! ## Increments and sums -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (the Brownian increment `dW` in (1.32) with diffusive
bonds): `W_v − W_u` for the motion read on `ℝ`, `TidyR7BrownianTools.bmReal`.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7BrownianQV.incr). -/
def incr (W : ℝ≥0 → Ω → ℝ) (u v : ℝ) (ω : Ω) : ℝ := bmReal W v ω - bmReal W u ω

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the centred squared increment
`(W_v − W_u)² − (v − u)`, the discrete `(dW)² − dt`.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7BrownianQV.qvTerm). -/
def qvTerm (W : ℝ≥0 → Ω → ℝ) (u v : ℝ) (ω : Ω) : ℝ := incr W u v ω ^ 2 - (v - u)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the quadratic variation sum** `Σ_{i<n}(ΔW_i)²`
along a partition of `[s, t]`.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7BrownianQV.qvSum). -/
def qvSum {s t : ℝ} (W : ℝ≥0 → Ω → ℝ) (p : Partition s t) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range p.n, incr W (p.t i) (p.t (i + 1)) ω ^ 2

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the weighted centred sum**
`Σ_{i<n} H_{t_i}((ΔW_i)² − Δt_i)`, the error in the rule `(dW)² = dt` against a weight `H`.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7BrownianQV.wqvSum). -/
def wqvSum {s t : ℝ} (W : ℝ≥0 → Ω → ℝ) (H : ℝ → Ω → ℝ) (p : Partition s t) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range p.n, H (p.t i) ω * qvTerm W (p.t i) (p.t (i + 1)) ω

/-- Cochrane (2023), A1 §1.6, p. 567: the steps of a partition of `[s, t]` add up to `t − s`.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7BrownianQV.sum_step_eq). -/
theorem sum_step_eq {s t : ℝ} (p : Partition s t) :
    ∑ i ∈ Finset.range p.n, (p.t (i + 1) - p.t i) = t - s := by
  rw [Finset.sum_range_sub (fun i => p.t i), p.last, p.first]

/-- Cochrane (2023), A1 §1.6, p. 567: the steps of a partition are positive.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7BrownianQV.step_pos). -/
theorem step_pos {s t : ℝ} (p : Partition s t) (i : ℕ) : 0 < p.t (i + 1) - p.t i :=
  sub_pos.2 (p.strictMono (Nat.lt_succ_self i))

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `Σ(ΔW_i)² − (t − s) = Σ((ΔW_i)² − Δt_i)`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.qvSum_sub_eq). -/
theorem qvSum_sub_eq {s t : ℝ} (p : Partition s t) (ω : Ω) :
    qvSum W p ω - (t - s) = ∑ i ∈ Finset.range p.n, qvTerm W (p.t i) (p.t (i + 1)) ω := by
  rw [← sum_step_eq p, qvSum, ← Finset.sum_sub_distrib]
  rfl

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the weighted sum is
`Σ H_{t_i}(ΔW_i)² − Σ H_{t_i}Δt_i`.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7BrownianQV.wqvSum_eq). -/
theorem wqvSum_eq {s t : ℝ} (H : ℝ → Ω → ℝ) (p : Partition s t) (ω : Ω) :
    wqvSum W H p ω = ∑ i ∈ Finset.range p.n, H (p.t i) ω * incr W (p.t i) (p.t (i + 1)) ω ^ 2
      - ∑ i ∈ Finset.range p.n, H (p.t i) ω * (p.t (i + 1) - p.t i) := by
  simp only [wqvSum, qvTerm, mul_sub, Finset.sum_sub_distrib]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: with weight `1` the weighted sum is
`Σ(ΔW_i)² − (t − s)`.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7BrownianQV.wqvSum_one). -/
theorem wqvSum_one {s t : ℝ} (p : Partition s t) (ω : Ω) :
    wqvSum W (fun _ _ => 1) p ω = qvSum W p ω - (t - s) := by
  rw [qvSum_sub_eq]
  simp [wqvSum]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the quadratic variation sum is Track 1's cross sum
`TidyR7StieltjesSums.crossSum` of the path with itself.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.qvSum_eq_crossSum). -/
theorem qvSum_eq_crossSum {s t : ℝ} (p : Partition s t) (ω : Ω) :
    qvSum W p ω = crossSum p (fun u => bmReal W u ω) (fun u => bmReal W u ω) := by
  simp only [qvSum, crossSum, incr, sq]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: increments are measurable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.measurable_incr). -/
theorem measurable_incr (hW : ∀ t, Measurable (W t)) (u v : ℝ) : Measurable (incr W u v) :=
  (hW _).sub (hW _)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: centred squared increments are measurable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.measurable_qvTerm). -/
theorem measurable_qvTerm (hW : ∀ t, Measurable (W t)) (u v : ℝ) :
    Measurable (qvTerm W u v) :=
  ((measurable_incr hW u v).pow_const 2).sub_const _

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the quadratic variation sum is measurable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.measurable_qvSum). -/
theorem measurable_qvSum (hW : ∀ t, Measurable (W t)) {s t : ℝ} (p : Partition s t) :
    Measurable (qvSum W p) :=
  Finset.measurable_sum _ fun _ _ => (measurable_incr hW _ _).pow_const 2

/-! ## Moments of the increments -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: for `0 ≤ u ≤ v`, `|v₊ − u₊| = v − u`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.abs_toNNReal_sub). -/
lemma abs_toNNReal_sub {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    |((v.toNNReal : ℝ≥0) : ℝ) - u.toNNReal| = v - u := by
  rw [Real.coe_toNNReal _ (hu.trans huv), Real.coe_toNNReal _ hu,
    abs_of_nonneg (sub_nonneg.2 huv)]

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (`E(dW)² = dt`): for `0 ≤ u ≤ v`,
`E[(W_v − W_u)²] = v − u`.
Restates `TidyR7BrownianTools.integral_increment_sq` on the `ℝ` index.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.integral_incr_sq). -/
theorem integral_incr_sq (hB : IsPreBrownianReal W P) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    ∫ ω, incr W u v ω ^ 2 ∂P = v - u := by
  have h := integral_increment_sq hB u.toNNReal v.toNNReal
  rw [abs_toNNReal_sub hu huv] at h
  exact h

/-- Cochrane (2023), A1 §1.6, pp. 567–568: for `0 ≤ u ≤ v`, `E[(W_v − W_u)⁴] = 3(v − u)²`.
Restates `TidyR7BrownianTools.integral_increment_pow_four` on the `ℝ` index.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.integral_incr_pow_four). -/
theorem integral_incr_pow_four (hB : IsPreBrownianReal W P) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) : ∫ ω, incr W u v ω ^ 4 ∂P = 3 * (v - u) ^ 2 := by
  have h := integral_increment_pow_four hB u.toNNReal v.toNNReal
  rw [Real.coe_toNNReal _ (hu.trans huv), Real.coe_toNNReal _ hu] at h
  exact h

/-- Cochrane (2023), A1 §1.6, pp. 567–568: increments are square integrable.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7BrownianQV.memLp_incr). -/
theorem memLp_incr (hB : IsPreBrownianReal W P) (u v : ℝ) : MemLp (incr W u v) 2 P :=
  ((hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two).sub
    ((hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: squared increments are integrable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.integrable_incr_sq). -/
theorem integrable_incr_sq (hB : IsPreBrownianReal W P) (u v : ℝ) :
    Integrable (fun ω => incr W u v ω ^ 2) P :=
  (memLp_incr hB u v).integrable_sq

/-- Cochrane (2023), A1 §1.6, pp. 567–568: fourth powers of increments are integrable.
Restates `TidyR7BrownianTools.integrable_increment_pow_four` on the `ℝ` index.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.integrable_incr_pow_four). -/
theorem integrable_incr_pow_four (hB : IsPreBrownianReal W P) (u v : ℝ) :
    Integrable (fun ω => incr W u v ω ^ 4) P :=
  integrable_increment_pow_four hB _ _

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `E[(W_v − W_u)² − (v − u)] = 0` for `0 ≤ u ≤ v`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.integral_qvTerm). -/
theorem integral_qvTerm (hB : IsPreBrownianReal W P) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    ∫ ω, qvTerm W u v ω ∂P = 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  simp only [qvTerm]
  rw [integral_sub (integrable_incr_sq hB u v) (integrable_const _), integral_incr_sq hB hu huv,
    integral_const]
  simp

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `((ΔW)² − Δt)² = (ΔW)⁴ − 2Δt(ΔW)² + Δt²`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.qvTerm_sq_eq). -/
lemma qvTerm_sq_eq (u v : ℝ) :
    (fun ω => qvTerm W u v ω ^ 2)
      = fun ω => incr W u v ω ^ 4 - 2 * (v - u) * incr W u v ω ^ 2 + (v - u) ^ 2 := by
  funext ω
  simp only [qvTerm]
  ring

/-- Cochrane (2023), A1 §1.6, pp. 567–568: squared centred increments are integrable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.integrable_qvTerm_sq). -/
theorem integrable_qvTerm_sq (hB : IsPreBrownianReal W P) (u v : ℝ) :
    Integrable (fun ω => qvTerm W u v ω ^ 2) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [qvTerm_sq_eq]
  exact ((integrable_incr_pow_four hB u v).sub ((integrable_incr_sq hB u v).const_mul _)).add
    (integrable_const _)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: centred squared increments are square integrable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.memLp_qvTerm). -/
theorem memLp_qvTerm (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t)) (u v : ℝ) :
    MemLp (qvTerm W u v) 2 P :=
  (memLp_two_iff_integrable_sq (measurable_qvTerm hW u v).aestronglyMeasurable).2
    (integrable_qvTerm_sq hB u v)

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (the variance of `(dW)²`): for `0 ≤ u ≤ v`,
`E[((W_v − W_u)² − (v − u))²] = 2(v − u)²`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.integral_qvTerm_sq). -/
theorem integral_qvTerm_sq (hB : IsPreBrownianReal W P) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    ∫ ω, qvTerm W u v ω ^ 2 ∂P = 2 * (v - u) ^ 2 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h1 : ∫ ω, (incr W u v ω ^ 4 - 2 * (v - u) * incr W u v ω ^ 2 + (v - u) ^ 2) ∂P
      = ∫ ω, (incr W u v ω ^ 4 - 2 * (v - u) * incr W u v ω ^ 2) ∂P + ∫ _ω, (v - u) ^ 2 ∂P :=
    integral_add ((integrable_incr_pow_four hB u v).sub
      ((integrable_incr_sq hB u v).const_mul _)) (integrable_const _)
  have h2 : ∫ ω, (incr W u v ω ^ 4 - 2 * (v - u) * incr W u v ω ^ 2) ∂P
      = ∫ ω, incr W u v ω ^ 4 ∂P - ∫ ω, 2 * (v - u) * incr W u v ω ^ 2 ∂P :=
    integral_sub (integrable_incr_pow_four hB u v) ((integrable_incr_sq hB u v).const_mul _)
  rw [qvTerm_sq_eq, h1, h2, integral_const_mul, integral_incr_pow_four hB hu huv,
    integral_incr_sq hB hu huv, integral_const]
  simp only [probReal_univ, one_smul]
  ring

/-! ## Admissible filtrations on the time index `ℝ` -/

variable (P W) (𝓕 : Filtration ℝ mΩ)

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (the information `E_t` of (1.32) with diffusive
bonds): **an admissible filtration for `W`** on the time index `ℝ`: `bmReal W` is adapted, and
every increment `W_v − W_u`, `u ≤ v`, is independent of `𝓕_u`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.BMFiltration). -/
structure BMFiltration where
  adapted : ∀ u, StronglyMeasurable[𝓕 u] (bmReal W u)
  indep : ∀ u v, u ≤ v → Indep (MeasurableSpace.comap (incr W u v) inferInstance) (𝓕 u) P

variable {P W 𝓕}

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the natural filtration on `ℝ`,
`TidyR7BrownianTools.bmFiltrationReal`, is admissible.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.bmFiltrationReal_isBM). -/
theorem bmFiltrationReal_isBM (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t)) :
    BMFiltration P W (bmFiltrationReal W hW) where
  adapted u := stronglyAdapted_bmFiltration hW u.toNNReal
  indep _ _ huv := indep_increment_bmFiltration hB hW (Real.toNNReal_le_toNNReal huv)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: for an admissible filtration, `W_v − W_u` is
`𝓕_v`-measurable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.stronglyMeasurable_incr). -/
theorem stronglyMeasurable_incr (h𝓕 : BMFiltration P W 𝓕) {u v : ℝ} (huv : u ≤ v) :
    StronglyMeasurable[𝓕 v] (incr W u v) :=
  (h𝓕.adapted v).sub ((h𝓕.adapted u).mono (𝓕.mono huv))

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `(W_v − W_u)² − (v − u)` is `𝓕_v`-measurable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.stronglyMeasurable_qvTerm). -/
theorem stronglyMeasurable_qvTerm (h𝓕 : BMFiltration P W 𝓕) {u v : ℝ} (huv : u ≤ v) :
    StronglyMeasurable[𝓕 v] (qvTerm W u v) :=
  ((stronglyMeasurable_incr h𝓕 huv).pow 2).sub stronglyMeasurable_const

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the increment `W_v − W_u` is independent of every
`𝓕_u`-measurable `Y`.
Generalises `TidyR7BrownianTools.indep_increment_bmFiltration` and
`TidyR7BrownianTools.indepFun_increment_past` to any `BMFiltration`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.indepFun_incr). -/
theorem indepFun_incr (h𝓕 : BMFiltration P W 𝓕) {u v : ℝ} (huv : u ≤ v) {Y : Ω → ℝ}
    (hY : StronglyMeasurable[𝓕 u] Y) : IndepFun (incr W u v) Y P := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_right (h𝓕.indep u v huv) hY.measurable.comap_le

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (orthogonality of `(dW)² − dt` to the past): for
`0 ≤ u ≤ v` and `Y` `𝓕_u`-measurable, `E[Y((W_v − W_u)² − (v − u))] = 0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.integral_mul_qvTerm). -/
theorem integral_mul_qvTerm (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) {Y : Ω → ℝ}
    (hY : StronglyMeasurable[𝓕 u] Y) : ∫ ω, Y ω * qvTerm W u v ω ∂P = 0 := by
  have hI : IndepFun Y (qvTerm W u v) P :=
    ((indepFun_incr h𝓕 huv hY).comp (φ := fun x => x ^ 2 - (v - u)) (ψ := id)
      ((measurable_id.pow_const 2).sub_const _) measurable_id).symm
  rw [hI.integral_fun_mul_eq_mul_integral (hY.mono (𝓕.le u)).aestronglyMeasurable
    (measurable_qvTerm hW u v).aestronglyMeasurable, integral_qvTerm hB hu huv, mul_zero]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: for `0 ≤ u ≤ v` and `Y` `𝓕_u`-measurable,
`E[Y((W_v − W_u)² − (v − u))²] = 2(v − u)²E[Y]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.integral_mul_qvTerm_sq). -/
theorem integral_mul_qvTerm_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) {Y : Ω → ℝ}
    (hY : StronglyMeasurable[𝓕 u] Y) :
    ∫ ω, Y ω * qvTerm W u v ω ^ 2 ∂P = 2 * (v - u) ^ 2 * ∫ ω, Y ω ∂P := by
  have hI : IndepFun Y (fun ω => qvTerm W u v ω ^ 2) P :=
    ((indepFun_incr h𝓕 huv hY).comp (φ := fun x => (x ^ 2 - (v - u)) ^ 2) (ψ := id)
      (((measurable_id.pow_const 2).sub_const _).pow_const 2) measurable_id).symm
  rw [hI.integral_fun_mul_eq_mul_integral (hY.mono (𝓕.le u)).aestronglyMeasurable
    ((measurable_qvTerm hW u v).pow_const 2).aestronglyMeasurable, integral_qvTerm_sq hB hu huv,
    mul_comm]

/-! ## The weighted `L²` identity -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: for bounded `G` and `H`, each product
`G·(H_iqvTerm_i)(H_jqvTerm_j)` is integrable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.integrable_mul_term). -/
theorem integrable_mul_term (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    {s t : ℝ} (p : Partition s t) {G : Ω → ℝ} (hGm : Measurable G) {CG : ℝ}
    (hGb : ∀ ω, |G ω| ≤ CG) {H : ℝ → Ω → ℝ} (hHm : ∀ u ∈ Set.Icc s t, Measurable (H u))
    {C : ℝ} (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) {i j : ℕ} (hi : i < p.n)
    (hj : j < p.n) :
    Integrable (fun ω => G ω * ((H (p.t i) ω * qvTerm W (p.t i) (p.t (i + 1)) ω) *
      (H (p.t j) ω * qvTerm W (p.t j) (p.t (j + 1)) ω))) P := by
  have hD : Integrable (fun ω => qvTerm W (p.t i) (p.t (i + 1)) ω *
      qvTerm W (p.t j) (p.t (j + 1)) ω) P :=
    (memLp_qvTerm hB hW _ _).integrable_mul (memLp_qvTerm hB hW _ _)
  have hmi := hHm _ (t_mem p hi.le)
  have hmj := hHm _ (t_mem p hj.le)
  have hb : ∀ᵐ ω ∂P, ‖G ω * H (p.t i) ω * H (p.t j) ω‖ ≤ CG * C * C := by
    refine ae_of_all _ fun ω => ?_
    have h1 := hGb ω
    have h2 := hHb _ (t_mem p hi.le) ω
    have h3 := hHb _ (t_mem p hj.le) ω
    have hC : 0 ≤ C := (abs_nonneg _).trans h2
    have hCG : 0 ≤ CG := (abs_nonneg _).trans h1
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) hCG) h3 (abs_nonneg _)
      (mul_nonneg hCG hC)
  have h := hD.bdd_mul ((hGm.mul hmi).mul hmj).aestronglyMeasurable hb
  refine h.congr (ae_of_all _ fun ω => ?_)
  simp only [Pi.mul_apply]
  ring

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `G·(Σ H_i((ΔW_i)² − Δt_i))²` is integrable for
bounded measurable `G` and `H`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.integrable_mul_wqvSum_sq). -/
theorem integrable_mul_wqvSum_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    {s t : ℝ} (p : Partition s t) {G : Ω → ℝ} (hGm : Measurable G) {CG : ℝ}
    (hGb : ∀ ω, |G ω| ≤ CG) {H : ℝ → Ω → ℝ} (hHm : ∀ u ∈ Set.Icc s t, Measurable (H u))
    {C : ℝ} (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) :
    Integrable (fun ω => G ω * wqvSum W H p ω ^ 2) P := by
  have e : (fun ω => G ω * wqvSum W H p ω ^ 2) = fun ω => ∑ i ∈ Finset.range p.n,
      ∑ j ∈ Finset.range p.n, G ω * ((H (p.t i) ω * qvTerm W (p.t i) (p.t (i + 1)) ω) *
        (H (p.t j) ω * qvTerm W (p.t j) (p.t (j + 1)) ω)) := by
    funext ω
    rw [wqvSum, sq, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
  rw [e]
  exact integrable_finsetSum _ fun i hi => integrable_finsetSum _ fun j hj =>
    integrable_mul_term hB hW p hGm hGb hHm hHb (Finset.mem_range.1 hi) (Finset.mem_range.1 hj)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the weighted `L²` identity with a past weight.**
For an admissible filtration, `0 ≤ s`, a partition of `[s, t]`, a bounded `𝓕_s`-measurable `G`
and a bounded adapted `H`,
`E[G(Σ H_{t_i}((ΔW_i)² − Δt_i))²] = 2Σ E[G H_{t_i}²](Δt_i)²`.
The cross terms vanish by `integral_mul_qvTerm` (the later increment is independent of
everything before it), the diagonal terms by `integral_mul_qvTerm_sq`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.integral_mul_wqvSum_sq). -/
theorem integral_mul_wqvSum_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {s t : ℝ} (hs : 0 ≤ s) (p : Partition s t) {G : Ω → ℝ}
    (hG : StronglyMeasurable[𝓕 s] G) {CG : ℝ} (hGb : ∀ ω, |G ω| ≤ CG) {H : ℝ → Ω → ℝ}
    (hH : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) :
    ∫ ω, G ω * wqvSum W H p ω ^ 2 ∂P
      = 2 * ∑ i ∈ Finset.range p.n,
          (∫ ω, G ω * H (p.t i) ω ^ 2 ∂P) * (p.t (i + 1) - p.t i) ^ 2 := by
  have hGm : Measurable G := (hG.mono (𝓕.le s)).measurable
  have hHm : ∀ u ∈ Set.Icc s t, Measurable (H u) := fun u hu => ((hH u hu).mono (𝓕.le u)).measurable
  have hint := fun i j hi hj => integrable_mul_term hB hW p hGm hGb hHm hHb (i := i) (j := j) hi hj
  have mem : ∀ i, i ≤ p.n → p.t i ∈ Set.Icc s t := fun i hi => t_mem p hi
  have nn : ∀ i, i ≤ p.n → 0 ≤ p.t i := fun i hi => hs.trans (mem i hi).1
  have mono : ∀ i j, i ≤ j → p.t i ≤ p.t j := fun i j h => p.strictMono.monotone h
  have hGt : ∀ i, i ≤ p.n → StronglyMeasurable[𝓕 (p.t i)] G := fun i hi =>
    hG.mono (𝓕.mono (mem i hi).1)
  have ha : ∀ i, i < p.n → ∀ j, i + 1 ≤ j → j ≤ p.n →
      StronglyMeasurable[𝓕 (p.t j)]
        (fun ω => H (p.t i) ω * qvTerm W (p.t i) (p.t (i + 1)) ω) := by
    intro i hi j hij hj
    exact ((hH _ (mem i hi.le)).mono (𝓕.mono (mono i j (by omega)))).mul
      ((stronglyMeasurable_qvTerm h𝓕 (mono i (i + 1) (Nat.le_succ i))).mono
        (𝓕.mono (mono (i + 1) j hij)))
  have e : (fun ω => G ω * wqvSum W H p ω ^ 2) = fun ω => ∑ i ∈ Finset.range p.n,
      ∑ j ∈ Finset.range p.n, G ω * ((H (p.t i) ω * qvTerm W (p.t i) (p.t (i + 1)) ω) *
        (H (p.t j) ω * qvTerm W (p.t j) (p.t (j + 1)) ω)) := by
    funext ω
    rw [wqvSum, sq, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
  rw [e, integral_finsetSum _ fun i hi => integrable_finsetSum _ fun j hj =>
    hint i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  rw [integral_finsetSum _ fun j hj => hint i j hi' (Finset.mem_range.1 hj),
    Finset.sum_eq_single i]
  · have hY : StronglyMeasurable[𝓕 (p.t i)] (fun ω => G ω * H (p.t i) ω ^ 2) :=
      (hGt i hi'.le).mul ((hH _ (mem i hi'.le)).pow 2)
    have h := integral_mul_qvTerm_sq hB hW h𝓕 (nn i hi'.le) (mono i (i + 1) (Nat.le_succ i)) hY
    have e2 : (fun ω => G ω * ((H (p.t i) ω * qvTerm W (p.t i) (p.t (i + 1)) ω) *
        (H (p.t i) ω * qvTerm W (p.t i) (p.t (i + 1)) ω)))
        = fun ω => (G ω * H (p.t i) ω ^ 2) * qvTerm W (p.t i) (p.t (i + 1)) ω ^ 2 := by
      funext ω
      ring
    rw [e2, h]
    ring
  · intro j hj hji
    have hj' := Finset.mem_range.1 hj
    rcases lt_or_gt_of_ne hji with hlt | hlt
    · have hY : StronglyMeasurable[𝓕 (p.t i)] (fun ω => G ω *
          (H (p.t j) ω * qvTerm W (p.t j) (p.t (j + 1)) ω) * H (p.t i) ω) :=
        ((hGt i hi'.le).mul (ha j hj' i hlt hi'.le)).mul (hH _ (mem i hi'.le))
      have h := integral_mul_qvTerm hB hW h𝓕 (nn i hi'.le) (mono i (i + 1) (Nat.le_succ i)) hY
      have e2 : (fun ω => G ω * ((H (p.t i) ω * qvTerm W (p.t i) (p.t (i + 1)) ω) *
          (H (p.t j) ω * qvTerm W (p.t j) (p.t (j + 1)) ω)))
          = fun ω => (G ω * (H (p.t j) ω * qvTerm W (p.t j) (p.t (j + 1)) ω) * H (p.t i) ω) *
            qvTerm W (p.t i) (p.t (i + 1)) ω := by
        funext ω
        ring
      rw [e2, h]
    · have hY : StronglyMeasurable[𝓕 (p.t j)] (fun ω => G ω *
          (H (p.t i) ω * qvTerm W (p.t i) (p.t (i + 1)) ω) * H (p.t j) ω) :=
        ((hGt j hj'.le).mul (ha i hi' j hlt hj'.le)).mul (hH _ (mem j hj'.le))
      have h := integral_mul_qvTerm hB hW h𝓕 (nn j hj'.le) (mono j (j + 1) (Nat.le_succ j)) hY
      have e2 : (fun ω => G ω * ((H (p.t i) ω * qvTerm W (p.t i) (p.t (i + 1)) ω) *
          (H (p.t j) ω * qvTerm W (p.t j) (p.t (j + 1)) ω)))
          = fun ω => (G ω * (H (p.t i) ω * qvTerm W (p.t i) (p.t (i + 1)) ω) * H (p.t j) ω) *
            qvTerm W (p.t j) (p.t (j + 1)) ω := by
        funext ω
        ring
      rw [e2, h]
  · intro h
    exact absurd hi h

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the weighted `L²` identity** (the rule
`(dW)² = dt` in mean square): for a bounded adapted `H`,
`E[(Σ H_{t_i}((ΔW_i)² − Δt_i))²] = 2Σ E[H_{t_i}²](Δt_i)²`.
The `G = 1` case of `integral_mul_wqvSum_sq`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.integral_wqvSum_sq). -/
theorem integral_wqvSum_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {s t : ℝ} (hs : 0 ≤ s) (p : Partition s t) {H : ℝ → Ω → ℝ}
    (hH : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) :
    ∫ ω, wqvSum W H p ω ^ 2 ∂P
      = 2 * ∑ i ∈ Finset.range p.n, (∫ ω, H (p.t i) ω ^ 2 ∂P) * (p.t (i + 1) - p.t i) ^ 2 := by
  have h := integral_mul_wqvSum_sq hB hW h𝓕 hs p (G := fun _ => 1) stronglyMeasurable_const
    (CG := 1) (fun _ => by simp) hH hHb
  simpa using h

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the `L²` quadratic variation identity.** For every
partition `s = t_0 < … < t_n = t`, `0 ≤ s`: `E[(Σ(ΔW_i)² − (t − s))²] = 2Σ(Δt_i)²` exactly.
The `G = 1`, `H = 1` case of `integral_mul_wqvSum_sq`, via `wqvSum_one`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.integral_qvSum_sub_sq). -/
theorem integral_qvSum_sub_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    {s t : ℝ} (hs : 0 ≤ s) (p : Partition s t) :
    ∫ ω, (qvSum W p ω - (t - s)) ^ 2 ∂P
      = 2 * ∑ i ∈ Finset.range p.n, (p.t (i + 1) - p.t i) ^ 2 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h := integral_wqvSum_sq hB hW (bmFiltrationReal_isBM hB hW) hs p (H := fun _ _ => 1)
    (fun _ _ => stronglyMeasurable_const) (C := 1) (fun _ _ _ => by simp)
  simp only [wqvSum_one] at h
  simpa using h

/-- Cochrane (2023), A1 §1.6, p. 567: `Σ(Δt_i)² ≤ mesh·(t − s)`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.sum_step_sq_le). -/
theorem sum_step_sq_le {s t : ℝ} (p : Partition s t) :
    ∑ i ∈ Finset.range p.n, (p.t (i + 1) - p.t i) ^ 2 ≤ mesh p * (t - s) := by
  rw [← sum_step_eq p, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_right (le_mesh p (Finset.mem_range.1 hi)) (step_pos p i).le

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `E[(Σ(ΔW_i)² − (t − s))²] ≤ 2·mesh·(t − s)`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.integral_qvSum_sub_sq_le). -/
theorem integral_qvSum_sub_sq_le (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    {s t : ℝ} (hs : 0 ≤ s) (p : Partition s t) :
    ∫ ω, (qvSum W p ω - (t - s)) ^ 2 ∂P ≤ 2 * (mesh p * (t - s)) := by
  rw [integral_qvSum_sub_sq hB hW hs p]
  exact mul_le_mul_of_nonneg_left (sum_step_sq_le p) zero_le_two

/-- Cochrane (2023), A1 §1.6, pp. 567–568: for `|H| ≤ C`,
`E[(Σ H_{t_i}((ΔW_i)² − Δt_i))²] ≤ 2C²·mesh·(t − s)`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.integral_wqvSum_sq_le). -/
theorem integral_wqvSum_sq_le (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {s t : ℝ} (hs : 0 ≤ s) (p : Partition s t) {H : ℝ → Ω → ℝ}
    (hH : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) :
    ∫ ω, wqvSum W H p ω ^ 2 ∂P ≤ 2 * C ^ 2 * (mesh p * (t - s)) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [integral_wqvSum_sq hB hW h𝓕 hs p hH hHb, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ zero_le_two
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (sum_step_sq_le p) (sq_nonneg C))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  have hb := hHb _ (t_mem p (Finset.mem_range.1 hi).le)
  have h : ∫ ω, H (p.t i) ω ^ 2 ∂P ≤ ∫ _ω, C ^ 2 ∂P :=
    integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _) (integrable_const _)
      (ae_of_all _ fun ω => sq_le_sq' (abs_le.1 (hb ω)).1 (abs_le.1 (hb ω)).2)
  simpa using h

/-! ## The conditional identities -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: for `A` in `𝓕_s`, multiplying by `1_A` and
integrating is integrating over `A`. From Mathlib `integral_indicator`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.integral_indicator_one_mul). -/
lemma integral_indicator_one_mul {A : Set Ω} (hA : MeasurableSet A) (f : Ω → ℝ) :
    ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω * f ω ∂P = ∫ ω in A, f ω ∂P := by
  rw [← integral_indicator hA]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  by_cases h : ω ∈ A <;> simp [h]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the conditional weighted identity.** For an
admissible filtration, `0 ≤ s`, a partition of `[s, t]` and a bounded adapted `H`, a.s.,
`E[(Σ H_{t_i}((ΔW_i)² − Δt_i))² | 𝓕_s] = 2Σ E[H_{t_i}² | 𝓕_s](Δt_i)²`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.condExp_wqvSum_sq). -/
theorem condExp_wqvSum_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {s t : ℝ} (hs : 0 ≤ s) (p : Partition s t) {H : ℝ → Ω → ℝ}
    (hH : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) :
    P[fun ω => wqvSum W H p ω ^ 2 | 𝓕 s]
      =ᵐ[P] fun ω => 2 * ∑ i ∈ Finset.range p.n,
        P[fun ω => H (p.t i) ω ^ 2 | 𝓕 s] ω * (p.t (i + 1) - p.t i) ^ 2 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hHm : ∀ u ∈ Set.Icc s t, Measurable (H u) := fun u hu => ((hH u hu).mono (𝓕.le u)).measurable
  have hf : Integrable (fun ω => wqvSum W H p ω ^ 2) P := by
    have h := integrable_mul_wqvSum_sq hB hW p (G := fun _ => 1) measurable_const (CG := 1)
      (fun _ => by simp) hHm hHb
    simpa using h
  have hH2 : ∀ i ∈ Finset.range p.n, Integrable (fun ω => H (p.t i) ω ^ 2) P := by
    intro i hi
    have hb := hHb _ (t_mem p (Finset.mem_range.1 hi).le)
    refine Integrable.of_bound ((hHm _ (t_mem p (Finset.mem_range.1 hi).le)).pow_const
      2).aestronglyMeasurable (C ^ 2) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (abs_le.1 (hb ω)).1 (abs_le.1 (hb ω)).2
  have hgi : Integrable (fun ω => 2 * ∑ i ∈ Finset.range p.n,
      P[fun ω => H (p.t i) ω ^ 2 | 𝓕 s] ω * (p.t (i + 1) - p.t i) ^ 2) P :=
    (integrable_finsetSum _ fun _ _ => integrable_condExp.mul_const _).const_mul _
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) hf (fun _ _ _ => hgi.integrableOn)
    ?_ ?_).symm
  · intro A hA _
    have hA' : MeasurableSet A := 𝓕.le s A hA
    have hG : StronglyMeasurable[𝓕 s] (A.indicator fun _ => (1 : ℝ)) :=
      stronglyMeasurable_const.indicator hA
    have hGb : ∀ ω, |A.indicator (fun _ => (1 : ℝ)) ω| ≤ 1 := fun ω => by
      by_cases h : ω ∈ A <;> simp [h]
    have h := integral_mul_wqvSum_sq hB hW h𝓕 hs p hG hGb hH hHb
    simp only [integral_indicator_one_mul hA'] at h
    have h2 : ∀ i ∈ Finset.range p.n,
        ∫ ω in A, H (p.t i) ω ^ 2 ∂P = ∫ ω in A, P[fun ω => H (p.t i) ω ^ 2 | 𝓕 s] ω ∂P :=
      fun i hi => (setIntegral_condExp (𝓕.le s) (hH2 i hi) hA).symm
    rw [h, integral_const_mul, integral_finsetSum _ fun i _ =>
      (integrable_condExp.mul_const _).restrict]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [integral_mul_const, h2 i hi]
  · have hm : StronglyMeasurable[𝓕 s] (fun ω => ∑ i ∈ Finset.range p.n,
        P[fun ω => H (p.t i) ω ^ 2 | 𝓕 s] ω * (p.t (i + 1) - p.t i) ^ 2) :=
      Finset.stronglyMeasurable_fun_sum _ fun _ _ => stronglyMeasurable_condExp.mul_const _
    exact (hm.const_mul 2).aestronglyMeasurable

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the conditional `L²` quadratic variation
identity.** For an admissible filtration and `0 ≤ s`, a.s.,
`E[(Σ(ΔW_i)² − (t − s))² | 𝓕_s] = 2Σ(Δt_i)²`.
The `H = 1` case of `condExp_wqvSum_sq`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.condExp_qvSum_sub_sq). -/
theorem condExp_qvSum_sub_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {s t : ℝ} (hs : 0 ≤ s) (p : Partition s t) :
    P[fun ω => (qvSum W p ω - (t - s)) ^ 2 | 𝓕 s]
      =ᵐ[P] fun _ => 2 * ∑ i ∈ Finset.range p.n, (p.t (i + 1) - p.t i) ^ 2 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h := condExp_wqvSum_sq hB hW h𝓕 hs p (H := fun _ _ => 1)
    (fun _ _ => stronglyMeasurable_const) (C := 1) (fun _ _ _ => by simp)
  simp only [wqvSum_one, one_pow, condExp_const (𝓕.le s), one_mul] at h
  exact h

/-! ## Convergence in `L²` and in probability -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: if `E[F_k²] → 0` then `‖F_k‖_{L²} → 0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.tendsto_eLpNorm_of_integral_sq). -/
theorem tendsto_eLpNorm_of_integral_sq {F : ℕ → Ω → ℝ} (hF : ∀ k, MemLp (F k) 2 P)
    (h : Tendsto (fun k => ∫ ω, F k ω ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (F k) 2 P) atTop (𝓝 0) := by
  have e : ∀ k, eLpNorm (F k) 2 P = ENNReal.ofReal ((∫ ω, F k ω ^ 2 ∂P) ^ (2 : ℝ)⁻¹) := by
    intro k
    rw [(hF k).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
    simp [Real.norm_eq_abs, sq_abs]
  simp_rw [e]
  have h2 : Tendsto (fun k => (∫ ω, F k ω ^ 2 ∂P) ^ (2 : ℝ)⁻¹) atTop (𝓝 0) := by
    have := h.rpow_const (p := (2 : ℝ)⁻¹) (Or.inr (by norm_num))
    rwa [Real.zero_rpow (by norm_num)] at this
  simpa using ENNReal.tendsto_ofReal h2

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `Σ(ΔW_i)² − (t − s)` is square integrable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.memLp_qvSum_sub). -/
theorem memLp_qvSum_sub (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t)) {s t : ℝ}
    (p : Partition s t) : MemLp (fun ω => qvSum W p ω - (t - s)) 2 P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine (memLp_two_iff_integrable_sq ((measurable_qvSum hW p).sub_const _).aestronglyMeasurable).2
    ?_
  have h := integrable_mul_wqvSum_sq hB hW p (G := fun _ => 1) measurable_const (CG := 1)
    (fun _ => by simp) (H := fun _ _ => 1) (fun _ _ => measurable_const) (C := 1)
    (fun _ _ _ => by simp)
  simp only [wqvSum_one, one_mul] at h
  exact h

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `Σ(ΔW_i)² → t − s` in mean square.** Along any
sequence of partitions of `[s, t]`, `0 ≤ s`, with mesh `→ 0`,
`E[(Σ(ΔW_i)² − (t − s))²] → 0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.tendsto_integral_qvSum_sub_sq). -/
theorem tendsto_integral_qvSum_sub_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    {s t : ℝ} (hs : 0 ≤ s) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, (qvSum W (ps k) ω - (t - s)) ^ 2 ∂P) atTop (𝓝 0) := by
  have hu : Tendsto (fun k => 2 * (mesh (ps k) * (t - s))) atTop (𝓝 0) := by
    simpa using (hps.mul_const (t - s)).const_mul 2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun _ => integral_nonneg fun _ => sq_nonneg _)
    (fun k => integral_qvSum_sub_sq_le hB hW hs (ps k))

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `Σ(ΔW_i)² → t − s` in `L²` (the `eLpNorm` form).
The `eLpNorm` form of `tendsto_integral_qvSum_sub_sq`, via `tendsto_eLpNorm_of_integral_sq`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.tendsto_eLpNorm_qvSum_sub). -/
theorem tendsto_eLpNorm_qvSum_sub (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    {s t : ℝ} (hs : 0 ≤ s) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun ω => qvSum W (ps k) ω - (t - s)) 2 P) atTop (𝓝 0) :=
  tendsto_eLpNorm_of_integral_sq (fun k => memLp_qvSum_sub hB hW (ps k))
    (tendsto_integral_qvSum_sub_sq hB hW hs ps hps)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `Σ(ΔW_i)² → t − s` in probability** along any
sequence of partitions with mesh `→ 0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.tendstoInMeasure_qvSum). -/
theorem tendstoInMeasure_qvSum (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    {s t : ℝ} (hs : 0 ≤ s) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun k => qvSum W (ps k)) atTop (fun _ => t - s) :=
  tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (tendsto_eLpNorm_qvSum_sub hB hW hs ps hps)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the rule `(dW)² = dt` in mean square.** For a
bounded adapted `H` and any sequence of partitions with mesh `→ 0`,
`E[(Σ H_{t_i}(ΔW_i)² − Σ H_{t_i}Δt_i)²] → 0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.tendsto_integral_wqvSum_sq). -/
theorem tendsto_integral_wqvSum_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {s t : ℝ} (hs : 0 ≤ s) {H : ℝ → Ω → ℝ}
    (hH : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, wqvSum W H (ps k) ω ^ 2 ∂P) atTop (𝓝 0) := by
  have hu : Tendsto (fun k => 2 * C ^ 2 * (mesh (ps k) * (t - s))) atTop (𝓝 0) := by
    simpa using (hps.mul_const (t - s)).const_mul (2 * C ^ 2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun _ => integral_nonneg fun _ => sq_nonneg _)
    (fun k => integral_wqvSum_sq_le hB hW h𝓕 hs (ps k) hH hHb)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the rule `(dW)² = dt` in `L²`:
`‖Σ H_{t_i}(ΔW_i)² − Σ H_{t_i}Δt_i‖_{L²} → 0` (`wqvSum_eq`).
The `eLpNorm` form of `tendsto_integral_wqvSum_sq`, via `tendsto_eLpNorm_of_integral_sq`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.tendsto_eLpNorm_wqvSum). -/
theorem tendsto_eLpNorm_wqvSum (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {s t : ℝ} (hs : 0 ≤ s) {H : ℝ → Ω → ℝ}
    (hH : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (wqvSum W H (ps k)) 2 P) atTop (𝓝 0) := by
  have hHm : ∀ u ∈ Set.Icc s t, Measurable (H u) := fun u hu => ((hH u hu).mono (𝓕.le u)).measurable
  refine tendsto_eLpNorm_of_integral_sq (fun k => ?_)
    (tendsto_integral_wqvSum_sq hB hW h𝓕 hs hH hHb ps hps)
  have hm : Measurable (wqvSum W H (ps k)) :=
    Finset.measurable_sum _ fun i hi =>
      (hHm _ (t_mem (ps k) (Finset.mem_range.1 hi).le)).mul (measurable_qvTerm hW _ _)
  refine (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 ?_
  have h := integrable_mul_wqvSum_sq hB hW (ps k) (G := fun _ => 1) measurable_const (CG := 1)
    (fun _ => by simp) hHm hHb
  simpa using h

/-! ## Almost sure convergence -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (first Borel–Cantelli lemma, in mean-square form):
if `Σ_k E[F_k²] < ∞` then `F_k → 0` almost surely. Proof: `∫⁻ Σ_k F_k² = Σ_k E[F_k²] < ∞`, so
`Σ_k F_k² < ∞` a.s.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.ae_tendsto_zero_of_summable_integral_sq). -/
theorem ae_tendsto_zero_of_summable_integral_sq {F : ℕ → Ω → ℝ} (hFm : ∀ k, Measurable (F k))
    (hFi : ∀ k, Integrable (fun ω => F k ω ^ 2) P)
    (hsum : Summable fun k => ∫ ω, F k ω ^ 2 ∂P) :
    ∀ᵐ ω ∂P, Tendsto (fun k => F k ω) atTop (𝓝 0) := by
  set f : ℕ → Ω → ℝ≥0∞ := fun k ω => ENNReal.ofReal (F k ω ^ 2) with hf
  have hfm : ∀ k, Measurable (f k) := fun k =>
    ENNReal.measurable_ofReal.comp ((hFm k).pow_const 2)
  have hlin : ∫⁻ ω, ∑' k, f k ω ∂P ≠ ∞ := by
    rw [lintegral_tsum fun k => (hfm k).aemeasurable]
    have e : ∀ k, ∫⁻ ω, f k ω ∂P = ENNReal.ofReal (∫ ω, F k ω ^ 2 ∂P) := fun k =>
      (ofReal_integral_eq_lintegral_ofReal (hFi k) (ae_of_all _ fun ω => sq_nonneg _)).symm
    simp_rw [e]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => integral_nonneg fun ω => sq_nonneg _) hsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_lt_top (Measurable.tsum hfm) hlin] with ω hω
  have h1 : Tendsto (fun k => f k ω) atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have h2 : Tendsto (fun k => F k ω ^ 2) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [hf, Function.comp_def, ENNReal.toReal_ofReal (sq_nonneg _)] using this
  have h3 : Tendsto (fun k => ‖F k ω‖) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h2
    simpa [Function.comp_def, Real.sqrt_sq_eq_abs] using this
  exact tendsto_zero_iff_norm_tendsto_zero.2 h3

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `Σ(ΔW_i)² → t − s` almost surely** along any
sequence of partitions of `[s, t]`, `0 ≤ s`, with summable meshes `Σ_k mesh_k < ∞`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.ae_tendsto_qvSum_of_summable_mesh). -/
theorem ae_tendsto_qvSum_of_summable_mesh (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) {s t : ℝ} (hs : 0 ≤ s) (ps : ℕ → Partition s t)
    (hsum : Summable fun k => mesh (ps k)) :
    ∀ᵐ ω ∂P, Tendsto (fun k => qvSum W (ps k) ω) atTop (𝓝 (t - s)) := by
  have h := ae_tendsto_zero_of_summable_integral_sq (P := P)
    (F := fun k ω => qvSum W (ps k) ω - (t - s)) (fun k => (measurable_qvSum hW _).sub_const _)
    (fun k => (memLp_qvSum_sub hB hW (ps k)).integrable_sq)
    (Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => sq_nonneg _)
      (fun k => integral_qvSum_sub_sq_le hB hW hs (ps k)) ((hsum.mul_right (t - s)).mul_left 2))
  filter_upwards [h] with ω hω
  exact tendsto_sub_nhds_zero_iff.1 hω

/-- Cochrane (2023), A1 §1.6, p. 567: the meshes `(t − s)/2^k` of the dyadic partitions are
summable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.summable_mesh_dyadic). -/
theorem summable_mesh_dyadic {s t : ℝ} (hst : s < t) :
    Summable fun k => mesh (dyadic hst k) := by
  simp_rw [mesh_dyadic]
  exact (summable_geometric_two.mul_left (t - s)).congr fun k => by
    rw [one_div_pow, mul_one_div]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `Σ(ΔW_i)² → t − s` almost surely along the dyadic
partitions** `TidyR7StieltjesSums.dyadic` of `[s, t]`, `0 ≤ s < t`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianQV.ae_tendsto_qvSum_dyadic). -/
theorem ae_tendsto_qvSum_dyadic (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    ∀ᵐ ω ∂P, Tendsto (fun k => qvSum W (dyadic hst k) ω) atTop (𝓝 (t - s)) :=
  ae_tendsto_qvSum_of_summable_mesh hB hW hs _ (summable_mesh_dyadic hst)

end Cochrane.StickyPriceFiscal.TidyR7BrownianQV
