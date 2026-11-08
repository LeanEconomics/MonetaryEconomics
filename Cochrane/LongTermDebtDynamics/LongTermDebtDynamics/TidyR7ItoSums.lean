/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR7ItoL2

/-!
# Left-point Itô sums: orthogonality, the discrete isometry, and the Cauchy estimate

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for (1.32) with diffusive
bonds (chunk I5c): the left-point sums `I_p(H) = Σ_i H_{t_i}(W_{t_{i+1}} − W_{t_i})` whose
mean-square limit is the Itô integral `∫ H dW` (TidyR7ItoIntegral).

Conventions as in TidyR7BrownianQV: `W` is any pre-Brownian motion with measurable values,
read on `ℝ` through `TidyR7BrownianTools.bmReal`, `𝓕` any admissible filtration
(`TidyR7BrownianQV.BMFiltration`), partitions are Track 1's `TidyR7StieltjesSums.Partition`.

## Main results

* **Cells.** `cellSum W S a b ξ = Σ_{k∈S} ξ_k(W_{b_k} − W_{a_k})` for finitely many pairwise
  non-overlapping intervals `(a_k, b_k]` with `𝓕_{a_k}`-measurable bounded `ξ_k`:
  `integral_mul_cellSum_sq`, `E[G(Σ ξ_kΔW_k)²] = Σ E[Gξ_k²](b_k − a_k)` for bounded
  `𝓕_r`-measurable `G`, `r ≤ a_k`; `integral_mul_cellSum`, `E[G Σ ξ_kΔW_k] = 0`.
* **Item 1, left-point sums.** `integral_mul_mul_incr` (`E[Y H_{t_i}ΔW_i] = 0`),
  `integral_mul_itoSum_sq`, `integral_itoSum_sq` (**the discrete isometry**
  `E[I_p(H)²] = Σ E[H_{t_i}²]Δt_i`), `condExp_itoSum_sq` (its conditional form given `𝓕_s`),
  `integral_mul_itoSum`, `condExp_itoSum` (`E[I_p(H) | 𝓕_s] = 0`).
* **The common refinement.** For two partitions `p, q` of `[s, t]` the cells
  `(max(p_i, q_j), min(p_{i+1}, q_{j+1})]` (`cellA`, `cellB`) refine both
  (`sub_eq_sum_cells`, `sub_eq_sum_cells'`), so
  `itoSum_sub_itoSum : I_p(H) − I_q(H) = Σ_{i,j} (H_{p_i} − H_{q_j})ΔW_{ij}`, and
  `integral_itoSum_sub_sq_le` (**the Cauchy estimate**): if `E[(H_u − H_v)²] ≤ ε` whenever
  `|u − v| ≤ δ`, then `E[(I_p(H) − I_q(H))²] ≤ ε(t − s)` for meshes `≤ δ`.
* **Concatenation.** `concat p q` of partitions of `[s, r]` and `[r, t]`;
  `itoSum_concat` (`I = I_p + I_q`) and `mesh_concat_le`.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR7ItoSums

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.LongTermDebtDynamics.TidyR7StieltjesSums
  Cochrane.LongTermDebtDynamics.TidyR7BrownianTools
  Cochrane.LongTermDebtDynamics.TidyR7BrownianQV Cochrane.LongTermDebtDynamics.TidyR7ItoL2
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ}

/-! ## Increments -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the increment over an empty interval is `0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.incr_self). -/
theorem incr_self (W : ℝ≥0 → Ω → ℝ) (u : ℝ) (ω : Ω) : incr W u u ω = 0 := sub_self _

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (`E dW = 0`): `E[W_v − W_u] = 0`.
The mean-zero content of `TidyR7BrownianTools.condExp_increment`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.integral_incr). -/
theorem integral_incr (hB : IsPreBrownianReal W P) (u v : ℝ) : ∫ ω, incr W u v ω ∂P = 0 := by
  simp only [incr, bmReal]
  rw [integral_sub (hB.integrable_eval _) (hB.integrable_eval _), hB.integral_eval,
    hB.integral_eval, sub_zero]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: increments are integrable.
From `TidyR7BrownianQV.memLp_incr`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.integrable_incr). -/
theorem integrable_incr (hB : IsPreBrownianReal W P) (u v : ℝ) : Integrable (incr W u v) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact (memLp_incr hB u v).integrable one_le_two

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (`E_t dW = 0`): an increment is orthogonal to the
past.** For an admissible filtration, `u ≤ v` and `Y` `𝓕_u`-measurable,
`E[Y(W_v − W_u)] = 0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.integral_mul_incr). -/
theorem integral_mul_incr (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {u v : ℝ} (huv : u ≤ v) {Y : Ω → ℝ}
    (hY : StronglyMeasurable[𝓕 u] Y) : ∫ ω, Y ω * incr W u v ω ∂P = 0 := by
  have hI : IndepFun Y (incr W u v) P := (indepFun_incr h𝓕 huv hY).symm
  rw [hI.integral_fun_mul_eq_mul_integral (hY.mono (𝓕.le u)).aestronglyMeasurable
    (measurable_incr hW u v).aestronglyMeasurable, integral_incr hB, mul_zero]

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (`E_t (dW)² = dt`): for `0 ≤ u ≤ v` and `Y`
`𝓕_u`-measurable, `E[Y(W_v − W_u)²] = (v − u)E[Y]`.
Equivalent to `TidyR7BrownianQV.integral_mul_qvTerm`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.integral_mul_incr_sq). -/
theorem integral_mul_incr_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) {Y : Ω → ℝ}
    (hY : StronglyMeasurable[𝓕 u] Y) :
    ∫ ω, Y ω * incr W u v ω ^ 2 ∂P = (v - u) * ∫ ω, Y ω ∂P := by
  have hI : IndepFun Y (fun ω => incr W u v ω ^ 2) P :=
    ((indepFun_incr h𝓕 huv hY).comp (φ := fun x => x ^ 2) (ψ := id)
      (measurable_id.pow_const 2) measurable_id).symm
  rw [hI.integral_fun_mul_eq_mul_integral (hY.mono (𝓕.le u)).aestronglyMeasurable
    ((measurable_incr hW u v).pow_const 2).aestronglyMeasurable, integral_incr_sq hB hu huv,
    mul_comm]

/-! ## Sums over non-overlapping cells -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the elementary stochastic integral** over finitely
many intervals `(a_k, b_k]`, `Σ_{k∈S} ξ_k(W_{b_k} − W_{a_k})`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.cellSum). -/
def cellSum {κ : Type*} (W : ℝ≥0 → Ω → ℝ) (S : Finset κ) (a b : κ → ℝ) (ξ : κ → Ω → ℝ)
    (ω : Ω) : ℝ :=
  ∑ k ∈ S, ξ k ω * incr W (a k) (b k) ω

/-- Cochrane (2023), A1 §1.6, pp. 567–568: each product `G(ξ_kΔW_k)(ξ_lΔW_l)` of bounded
coefficients and increments is integrable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.integrable_mul_cell). -/
theorem integrable_mul_cell {κ : Type*} (hB : IsPreBrownianReal W P) {S : Finset κ}
    {a b : κ → ℝ} {ξ : κ → Ω → ℝ} (hξm : ∀ k ∈ S, Measurable (ξ k)) {C : ℝ}
    (hξb : ∀ k ∈ S, ∀ ω, |ξ k ω| ≤ C) {G : Ω → ℝ} (hGm : Measurable G) {CG : ℝ}
    (hGb : ∀ ω, |G ω| ≤ CG) {k l : κ} (hk : k ∈ S) (hl : l ∈ S) :
    Integrable (fun ω => G ω * ((ξ k ω * incr W (a k) (b k) ω) *
      (ξ l ω * incr W (a l) (b l) ω))) P := by
  have hD : Integrable (fun ω => incr W (a k) (b k) ω * incr W (a l) (b l) ω) P :=
    (memLp_incr hB _ _).integrable_mul (memLp_incr hB _ _)
  have hb : ∀ᵐ ω ∂P, ‖G ω * ξ k ω * ξ l ω‖ ≤ CG * C * C := by
    refine ae_of_all _ fun ω => ?_
    have h1 := hGb ω
    have h2 := hξb k hk ω
    have h3 := hξb l hl ω
    have hC : 0 ≤ C := (abs_nonneg _).trans h2
    have hCG : 0 ≤ CG := (abs_nonneg _).trans h1
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) hCG) h3 (abs_nonneg _)
      (mul_nonneg hCG hC)
  have h := hD.bdd_mul ((hGm.mul (hξm k hk)).mul (hξm l hl)).aestronglyMeasurable hb
  refine h.congr (ae_of_all _ fun ω => ?_)
  simp only [Pi.mul_apply]
  ring

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `G·(Σ ξ_kΔW_k)²` is integrable for bounded
measurable `G` and `ξ`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.integrable_mul_cellSum_sq). -/
theorem integrable_mul_cellSum_sq {κ : Type*} (hB : IsPreBrownianReal W P) {S : Finset κ}
    {a b : κ → ℝ} {ξ : κ → Ω → ℝ} (hξm : ∀ k ∈ S, Measurable (ξ k)) {C : ℝ}
    (hξb : ∀ k ∈ S, ∀ ω, |ξ k ω| ≤ C) {G : Ω → ℝ} (hGm : Measurable G) {CG : ℝ}
    (hGb : ∀ ω, |G ω| ≤ CG) :
    Integrable (fun ω => G ω * cellSum W S a b ξ ω ^ 2) P := by
  have e : (fun ω => G ω * cellSum W S a b ξ ω ^ 2) = fun ω => ∑ k ∈ S, ∑ l ∈ S,
      G ω * ((ξ k ω * incr W (a k) (b k) ω) * (ξ l ω * incr W (a l) (b l) ω)) := by
    funext ω
    rw [cellSum, sq, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
  rw [e]
  exact integrable_finsetSum _ fun k hk => integrable_finsetSum _ fun l hl =>
    integrable_mul_cell hB hξm hξb hGm hGb hk hl

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the elementary integral of measurable coefficients
is measurable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.measurable_cellSum). -/
theorem measurable_cellSum {κ : Type*} (hW : ∀ t, Measurable (W t)) {S : Finset κ}
    {a b : κ → ℝ} {ξ : κ → Ω → ℝ} (hξm : ∀ k ∈ S, Measurable (ξ k)) :
    Measurable (cellSum W S a b ξ) :=
  Finset.measurable_sum _ fun k hk => (hξm k hk).mul (measurable_incr hW _ _)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the elementary integral of bounded measurable
coefficients is square integrable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.memLp_cellSum). -/
theorem memLp_cellSum {κ : Type*} (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    {S : Finset κ} {a b : κ → ℝ} {ξ : κ → Ω → ℝ} (hξm : ∀ k ∈ S, Measurable (ξ k)) {C : ℝ}
    (hξb : ∀ k ∈ S, ∀ ω, |ξ k ω| ≤ C) : MemLp (cellSum W S a b ξ) 2 P := by
  refine (memLp_two_iff_integrable_sq (measurable_cellSum hW hξm).aestronglyMeasurable).2 ?_
  have h := integrable_mul_cellSum_sq hB hξm hξb (a := a) (b := b) (G := fun _ => 1)
    measurable_const (CG := 1) (fun _ => by simp)
  simpa using h

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the weighted `L²` identity for non-overlapping
cells.** Let `0 ≤ r ≤ a_k ≤ b_k` for `k ∈ S`, the intervals `(a_k, b_k]` pairwise disjoint or
empty, `ξ_k` bounded and `𝓕_{a_k}`-measurable, and `G` bounded and `𝓕_r`-measurable. Then
`E[G(Σ ξ_k(W_{b_k} − W_{a_k}))²] = Σ E[Gξ_k²](b_k − a_k)`. The cross terms vanish because the
later increment is orthogonal to everything before it (`integral_mul_incr`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.integral_mul_cellSum_sq). -/
theorem integral_mul_cellSum_sq {κ : Type*} (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) {S : Finset κ} {a b : κ → ℝ}
    {ξ : κ → Ω → ℝ} {r : ℝ} (hr : 0 ≤ r) (hra : ∀ k ∈ S, r ≤ a k) (hab : ∀ k ∈ S, a k ≤ b k)
    (hξ : ∀ k ∈ S, StronglyMeasurable[𝓕 (a k)] (ξ k)) {C : ℝ}
    (hξb : ∀ k ∈ S, ∀ ω, |ξ k ω| ≤ C)
    (hdisj : ∀ k ∈ S, ∀ l ∈ S, k ≠ l → b k ≤ a l ∨ b l ≤ a k ∨ a k = b k ∨ a l = b l)
    {G : Ω → ℝ} (hG : StronglyMeasurable[𝓕 r] G) {CG : ℝ} (hGb : ∀ ω, |G ω| ≤ CG) :
    ∫ ω, G ω * cellSum W S a b ξ ω ^ 2 ∂P
      = ∑ k ∈ S, (∫ ω, G ω * ξ k ω ^ 2 ∂P) * (b k - a k) := by
  classical
  have hGm : Measurable G := (hG.mono (𝓕.le r)).measurable
  have hξm : ∀ k ∈ S, Measurable (ξ k) := fun k hk => ((hξ k hk).mono (𝓕.le _)).measurable
  have hint := fun k l (hk : k ∈ S) (hl : l ∈ S) =>
    integrable_mul_cell hB hξm hξb hGm hGb (a := a) (b := b) hk hl
  have e : (fun ω => G ω * cellSum W S a b ξ ω ^ 2) = fun ω => ∑ k ∈ S, ∑ l ∈ S,
      G ω * ((ξ k ω * incr W (a k) (b k) ω) * (ξ l ω * incr W (a l) (b l) ω)) := by
    funext ω
    rw [cellSum, sq, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
  -- the term `ξ_kΔW_k` is `𝓕_v`-measurable for `b_k ≤ v`
  have hpast : ∀ k ∈ S, ∀ v, b k ≤ v →
      StronglyMeasurable[𝓕 v] (fun ω => ξ k ω * incr W (a k) (b k) ω) := fun k hk v hv =>
    ((hξ k hk).mono (𝓕.mono ((hab k hk).trans hv))).mul
      ((stronglyMeasurable_incr h𝓕 (hab k hk)).mono (𝓕.mono hv))
  -- the off-diagonal term with `b_k ≤ a_l` vanishes
  have hoff : ∀ k ∈ S, ∀ l ∈ S, b k ≤ a l → ∫ ω, G ω * ((ξ k ω * incr W (a k) (b k) ω) *
      (ξ l ω * incr W (a l) (b l) ω)) ∂P = 0 := by
    intro k hk l hl hkl
    have hY : StronglyMeasurable[𝓕 (a l)] (fun ω => G ω *
        (ξ k ω * incr W (a k) (b k) ω) * ξ l ω) :=
      ((hG.mono (𝓕.mono (hra l hl))).mul (hpast k hk _ hkl)).mul (hξ l hl)
    have h := integral_mul_incr hB hW h𝓕 (hab l hl) hY
    rw [← h]
    exact integral_congr_ae (ae_of_all _ fun ω => by ring)
  have hempty : ∀ k ∈ S, ∀ l ∈ S, a k = b k → ∫ ω, G ω * ((ξ k ω * incr W (a k) (b k) ω) *
      (ξ l ω * incr W (a l) (b l) ω)) ∂P = 0 := by
    intro k _ l _ hk
    rw [← hk]
    simp [incr_self]
  rw [e, integral_finsetSum _ fun k hk => integrable_finsetSum _ fun l hl => hint k l hk hl]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_finsetSum _ fun l hl => hint k l hk hl, Finset.sum_eq_single k]
  · have hY : StronglyMeasurable[𝓕 (a k)] (fun ω => G ω * ξ k ω ^ 2) :=
      (hG.mono (𝓕.mono (hra k hk))).mul ((hξ k hk).pow 2)
    have h := integral_mul_incr_sq hB hW h𝓕 (hr.trans (hra k hk)) (hab k hk) hY
    rw [mul_comm _ (b k - a k), ← h]
    exact integral_congr_ae (ae_of_all _ fun ω => by ring)
  · intro l hl hlk
    rcases hdisj k hk l hl (Ne.symm hlk) with h | h | h | h
    · exact hoff k hk l hl h
    · rw [← hoff l hl k hk h]
      exact integral_congr_ae (ae_of_all _ fun ω => by ring)
    · exact hempty k hk l hl h
    · rw [← hempty l hl k hk h]
      exact integral_congr_ae (ae_of_all _ fun ω => by ring)
  · intro h
    exact absurd hk h

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (the martingale property of elementary integrals):
for bounded `𝓕_r`-measurable `G` and `r ≤ a_k ≤ b_k`, `E[G Σ ξ_k(W_{b_k} − W_{a_k})] = 0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.integral_mul_cellSum). -/
theorem integral_mul_cellSum {κ : Type*} (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) {S : Finset κ} {a b : κ → ℝ}
    {ξ : κ → Ω → ℝ} {r : ℝ} (hra : ∀ k ∈ S, r ≤ a k) (hab : ∀ k ∈ S, a k ≤ b k)
    (hξ : ∀ k ∈ S, StronglyMeasurable[𝓕 (a k)] (ξ k)) {C : ℝ}
    (hξb : ∀ k ∈ S, ∀ ω, |ξ k ω| ≤ C) {G : Ω → ℝ} (hG : StronglyMeasurable[𝓕 r] G) {CG : ℝ}
    (hGb : ∀ ω, |G ω| ≤ CG) : ∫ ω, G ω * cellSum W S a b ξ ω ∂P = 0 := by
  have hGm : Measurable G := (hG.mono (𝓕.le r)).measurable
  have hint : ∀ k ∈ S, Integrable (fun ω => G ω * (ξ k ω * incr W (a k) (b k) ω)) P := by
    intro k hk
    have hb : ∀ᵐ ω ∂P, ‖G ω * ξ k ω‖ ≤ CG * C := by
      refine ae_of_all _ fun ω => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hGb ω) (hξb k hk ω) (abs_nonneg _) ((abs_nonneg _).trans (hGb ω))
    have h := (integrable_incr hB (a k) (b k)).bdd_mul
      (hGm.mul ((hξ k hk).mono (𝓕.le _)).measurable).aestronglyMeasurable hb
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only [Pi.mul_apply]
    ring
  have e : (fun ω => G ω * cellSum W S a b ξ ω)
      = fun ω => ∑ k ∈ S, G ω * (ξ k ω * incr W (a k) (b k) ω) := by
    funext ω
    rw [cellSum, Finset.mul_sum]
  rw [e, integral_finsetSum _ hint]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hY : StronglyMeasurable[𝓕 (a k)] (fun ω => G ω * ξ k ω) :=
    (hG.mono (𝓕.mono (hra k hk))).mul (hξ k hk)
  rw [← integral_mul_incr hB hW h𝓕 (hab k hk) hY]
  exact integral_congr_ae (ae_of_all _ fun ω => by ring)

/-! ## Left-point sums (item 1) -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the left-point (Itô) sum**
`I_p(H) = Σ_{i<n} H_{t_i}(W_{t_{i+1}} − W_{t_i})` along a partition of `[s, t]`, the discrete
`∫ H dW` of (1.32) with diffusive bonds.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.itoSum). -/
def itoSum {s t : ℝ} (W : ℝ≥0 → Ω → ℝ) (H : ℝ → Ω → ℝ) (p : Partition s t) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range p.n, H (p.t i) ω * incr W (p.t i) (p.t (i + 1)) ω

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the left-point sum is the elementary integral over
the cells `(t_i, t_{i+1}]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.itoSum_eq_cellSum). -/
theorem itoSum_eq_cellSum {s t : ℝ} (H : ℝ → Ω → ℝ) (p : Partition s t) :
    itoSum W H p = cellSum W (Finset.range p.n) p.t (fun i => p.t (i + 1)) (fun i => H (p.t i)) :=
  rfl

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the left-point sum is Track 1's Riemann–Stieltjes
sum `TidyR7StieltjesSums.rsSum` of the path of `H` against the path of `W`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.itoSum_eq_rsSum). -/
theorem itoSum_eq_rsSum {s t : ℝ} (H : ℝ → Ω → ℝ) (p : Partition s t) (ω : Ω) :
    itoSum W H p ω = rsSum p (fun u => H u ω) (fun u => bmReal W u ω) := rfl

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the partition cells `(t_i, t_{i+1}]` are pairwise
disjoint.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.partition_cells_disjoint). -/
theorem partition_cells_disjoint {s t : ℝ} (p : Partition s t) :
    ∀ k ∈ Finset.range p.n, ∀ l ∈ Finset.range p.n, k ≠ l →
      p.t (k + 1) ≤ p.t l ∨ p.t (l + 1) ≤ p.t k ∨ p.t k = p.t (k + 1) ∨
        p.t l = p.t (l + 1) := by
  intro k _ l _ hkl
  rcases lt_or_gt_of_ne hkl with h | h
  · exact Or.inl (p.strictMono.monotone (by omega))
  · exact Or.inr (Or.inl (p.strictMono.monotone (by omega)))

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the left-point sum of an adapted `H` is
`𝓕_t`-strongly measurable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.stronglyMeasurable_itoSum). -/
theorem stronglyMeasurable_itoSum (h𝓕 : BMFiltration P W 𝓕) {s t : ℝ} {H : ℝ → Ω → ℝ}
    (hH : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (H u)) (p : Partition s t) :
    StronglyMeasurable[𝓕 t] (itoSum W H p) := by
  have e : itoSum W H p = fun ω => ∑ i ∈ Finset.range p.n,
      H (p.t i) ω * incr W (p.t i) (p.t (i + 1)) ω := rfl
  rw [e]
  refine Finset.stronglyMeasurable_fun_sum _ fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  exact ((hH _ (t_mem p hi'.le)).mono (𝓕.mono (t_mem p hi'.le).2)).mul
    ((stronglyMeasurable_incr h𝓕 (p.strictMono.monotone (Nat.le_succ i))).mono
      (𝓕.mono (t_mem p hi').2))

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the left-point sum of a bounded adapted `H` is square
integrable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.memLp_itoSum). -/
theorem memLp_itoSum (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t)) {s t : ℝ}
    {H : ℝ → Ω → ℝ} (hHm : ∀ u ∈ Set.Icc s t, Measurable (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) (p : Partition s t) :
    MemLp (itoSum W H p) 2 P :=
  memLp_cellSum hB hW (fun _ hi => hHm _ (t_mem p (Finset.mem_range.1 hi).le))
    (fun _ hi => hHb _ (t_mem p (Finset.mem_range.1 hi).le))

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (item 1): `E[Y H_{t_i}ΔW_i] = 0`** for `Y` bounded
and `𝓕_{t_i}`-measurable, `H_{t_i}` bounded and `𝓕_{t_i}`-measurable, and `t_i ≤ t_{i+1}`.
The case `Y * H` of `integral_mul_incr`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.integral_mul_mul_incr). -/
theorem integral_mul_mul_incr (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {u v : ℝ} (huv : u ≤ v) {Y K : Ω → ℝ}
    (hY : StronglyMeasurable[𝓕 u] Y) (hK : StronglyMeasurable[𝓕 u] K) :
    ∫ ω, Y ω * (K ω * incr W u v ω) ∂P = 0 := by
  rw [← integral_mul_incr hB hW h𝓕 huv (hY.mul hK)]
  exact integral_congr_ae (ae_of_all _ fun ω => by simp only [Pi.mul_apply]; ring)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the weighted discrete isometry.** For a bounded
adapted `H`, a partition of `[s, t]`, `0 ≤ s`, and bounded `𝓕_s`-measurable `G`,
`E[G I_p(H)²] = Σ E[G H_{t_i}²]Δt_i`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.integral_mul_itoSum_sq). -/
theorem integral_mul_itoSum_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {s t : ℝ} (hs : 0 ≤ s) {H : ℝ → Ω → ℝ}
    (hH : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) (p : Partition s t) {G : Ω → ℝ}
    (hG : StronglyMeasurable[𝓕 s] G) {CG : ℝ} (hGb : ∀ ω, |G ω| ≤ CG) :
    ∫ ω, G ω * itoSum W H p ω ^ 2 ∂P
      = ∑ i ∈ Finset.range p.n, (∫ ω, G ω * H (p.t i) ω ^ 2 ∂P) * (p.t (i + 1) - p.t i) := by
  rw [itoSum_eq_cellSum]
  exact integral_mul_cellSum_sq hB hW h𝓕 hs (fun i hi => (t_mem p (Finset.mem_range.1 hi).le).1)
    (fun i _ => p.strictMono.monotone (Nat.le_succ i))
    (fun i hi => hH _ (t_mem p (Finset.mem_range.1 hi).le))
    (fun i hi => hHb _ (t_mem p (Finset.mem_range.1 hi).le)) (partition_cells_disjoint p) hG hGb

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the discrete Itô isometry**
`E[(Σ H_{t_i}ΔW_i)²] = Σ E[H_{t_i}²]Δt_i` for a bounded adapted `H`, `0 ≤ s`.
The `G = 1` case of `integral_mul_itoSum_sq`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.integral_itoSum_sq). -/
theorem integral_itoSum_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {s t : ℝ} (hs : 0 ≤ s) {H : ℝ → Ω → ℝ}
    (hH : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) (p : Partition s t) :
    ∫ ω, itoSum W H p ω ^ 2 ∂P
      = ∑ i ∈ Finset.range p.n, (∫ ω, H (p.t i) ω ^ 2 ∂P) * (p.t (i + 1) - p.t i) := by
  have h := integral_mul_itoSum_sq hB hW h𝓕 hs hH hHb p (G := fun _ => 1)
    stronglyMeasurable_const (CG := 1) (fun _ => by simp)
  simpa using h

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the conditional discrete isometry.** For a bounded
adapted `H` and `0 ≤ s`, a.s.,
`E[(Σ H_{t_i}ΔW_i)² | 𝓕_s] = Σ E[H_{t_i}² | 𝓕_s]Δt_i`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.condExp_itoSum_sq). -/
theorem condExp_itoSum_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {s t : ℝ} (hs : 0 ≤ s) {H : ℝ → Ω → ℝ}
    (hH : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) (p : Partition s t) :
    P[fun ω => itoSum W H p ω ^ 2 | 𝓕 s]
      =ᵐ[P] fun ω => ∑ i ∈ Finset.range p.n,
        P[fun ω => H (p.t i) ω ^ 2 | 𝓕 s] ω * (p.t (i + 1) - p.t i) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hHm : ∀ u ∈ Set.Icc s t, Measurable (H u) := fun u hu =>
    ((hH u hu).mono (𝓕.le u)).measurable
  have hf : Integrable (fun ω => itoSum W H p ω ^ 2) P :=
    (memLp_itoSum hB hW hHm hHb p).integrable_sq
  have hH2 : ∀ i ∈ Finset.range p.n, Integrable (fun ω => H (p.t i) ω ^ 2) P := fun i hi =>
    (memLp_of_bound (hHm _ (t_mem p (Finset.mem_range.1 hi).le))
      (hHb _ (t_mem p (Finset.mem_range.1 hi).le))).integrable_sq
  have hgi : Integrable (fun ω => ∑ i ∈ Finset.range p.n,
      P[fun ω => H (p.t i) ω ^ 2 | 𝓕 s] ω * (p.t (i + 1) - p.t i)) P :=
    integrable_finsetSum _ fun _ _ => integrable_condExp.mul_const _
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) hf (fun _ _ _ => hgi.integrableOn)
    ?_ ?_).symm
  · intro A hA _
    have hA' : MeasurableSet A := 𝓕.le s A hA
    have hG : StronglyMeasurable[𝓕 s] (A.indicator fun _ => (1 : ℝ)) :=
      stronglyMeasurable_const.indicator hA
    have hGb : ∀ ω, |A.indicator (fun _ => (1 : ℝ)) ω| ≤ 1 := fun ω => by
      by_cases h : ω ∈ A <;> simp [h]
    have h := integral_mul_itoSum_sq hB hW h𝓕 hs hH hHb p hG hGb
    simp only [integral_indicator_one_mul hA'] at h
    rw [h, integral_finsetSum _ fun i _ => (integrable_condExp.mul_const _).restrict]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [integral_mul_const, setIntegral_condExp (𝓕.le s) (hH2 i hi) hA]
  · exact (Finset.stronglyMeasurable_fun_sum _ fun _ _ =>
      stronglyMeasurable_condExp.mul_const _).aestronglyMeasurable

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: left-point sums have mean zero given the past**:
`E[G I_p(H)] = 0` for bounded `𝓕_s`-measurable `G`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.integral_mul_itoSum). -/
theorem integral_mul_itoSum (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {s t : ℝ} {H : ℝ → Ω → ℝ}
    (hH : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) (p : Partition s t) {G : Ω → ℝ}
    (hG : StronglyMeasurable[𝓕 s] G) {CG : ℝ} (hGb : ∀ ω, |G ω| ≤ CG) :
    ∫ ω, G ω * itoSum W H p ω ∂P = 0 := by
  rw [itoSum_eq_cellSum]
  exact integral_mul_cellSum hB hW h𝓕 (fun i hi => (t_mem p (Finset.mem_range.1 hi).le).1)
    (fun i _ => p.strictMono.monotone (Nat.le_succ i))
    (fun i hi => hH _ (t_mem p (Finset.mem_range.1 hi).le))
    (fun i hi => hHb _ (t_mem p (Finset.mem_range.1 hi).le)) hG hGb

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (item 1): `E[I_p(H) | 𝓕_s] = 0`** a.s. for a
bounded adapted `H`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.condExp_itoSum). -/
theorem condExp_itoSum (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {s t : ℝ} {H : ℝ → Ω → ℝ}
    (hH : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) (p : Partition s t) :
    P[itoSum W H p | 𝓕 s] =ᵐ[P] 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hHm : ∀ u ∈ Set.Icc s t, Measurable (H u) := fun u hu =>
    ((hH u hu).mono (𝓕.le u)).measurable
  have hf : Integrable (itoSum W H p) P :=
    (memLp_itoSum hB hW hHm hHb p).integrable one_le_two
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) hf
    (fun _ _ _ => (integrable_zero _ _ _).integrableOn) ?_
    stronglyMeasurable_zero.aestronglyMeasurable).symm
  intro A hA _
  have hA' : MeasurableSet A := 𝓕.le s A hA
  have hG : StronglyMeasurable[𝓕 s] (A.indicator fun _ => (1 : ℝ)) :=
    stronglyMeasurable_const.indicator hA
  have hGb : ∀ ω, |A.indicator (fun _ => (1 : ℝ)) ω| ≤ 1 := fun ω => by
    by_cases h : ω ∈ A <;> simp [h]
  have h := integral_mul_itoSum hB hW h𝓕 hH hHb p hG hGb
  rw [integral_indicator_one_mul hA'] at h
  rw [h]
  simp

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (`∫ c dW = c(W_t − W_s)`, discrete form): for an
integrand constant in time, the left-point sum telescopes to `c(W_t − W_s)`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.itoSum_const). -/
theorem itoSum_const {s t : ℝ} (c : Ω → ℝ) (p : Partition s t) (ω : Ω) :
    itoSum W (fun _ => c) p ω = c ω * incr W s t ω := by
  simp only [itoSum, incr, ← Finset.mul_sum]
  rw [Finset.sum_range_sub (fun i => bmReal W (p.t i) ω), p.last, p.first]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: left-point sums are additive in the integrand.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.itoSum_add). -/
theorem itoSum_add {s t : ℝ} (H K : ℝ → Ω → ℝ) (p : Partition s t) :
    itoSum W (fun u ω => H u ω + K u ω) p = fun ω => itoSum W H p ω + itoSum W K p ω := by
  funext ω
  simp only [itoSum, add_mul, Finset.sum_add_distrib]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: left-point sums are homogeneous in the integrand.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.itoSum_const_mul). -/
theorem itoSum_const_mul {s t : ℝ} (c : ℝ) (H : ℝ → Ω → ℝ) (p : Partition s t) :
    itoSum W (fun u ω => c * H u ω) p = fun ω => c * itoSum W H p ω := by
  funext ω
  simp only [itoSum, Finset.mul_sum, mul_assoc]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the `dt`-sum `Σ E[G H_{t_i}²]Δt_i` is
`E[G Σ H_{t_i}²Δt_i]`, the expectation of `G` times the Riemann sum of the path of `H²`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.sum_integral_eq_integral_riemannSum). -/
theorem sum_integral_eq_integral_riemannSum [IsFiniteMeasure P] {s t : ℝ} {H : ℝ → Ω → ℝ}
    (hHm : ∀ u ∈ Set.Icc s t, Measurable (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) (p : Partition s t) {G : Ω → ℝ}
    (hGm : Measurable G) {CG : ℝ} (hGb : ∀ ω, |G ω| ≤ CG) :
    ∑ i ∈ Finset.range p.n, (∫ ω, G ω * H (p.t i) ω ^ 2 ∂P) * (p.t (i + 1) - p.t i)
      = ∫ ω, G ω * riemannSum p (fun u => H u ω ^ 2) ∂P := by
  have hint : ∀ i ∈ Finset.range p.n,
      Integrable (fun ω => G ω * (H (p.t i) ω ^ 2 * (p.t (i + 1) - p.t i))) P := by
    intro i hi
    have hm := hHm _ (t_mem p (Finset.mem_range.1 hi).le)
    have h2 := (memLp_of_bound (P := P) hm
      (hHb _ (t_mem p (Finset.mem_range.1 hi).le))).integrable_sq
    exact (h2.mul_const _).bdd_mul hGm.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact hGb ω)
  simp only [riemannSum, Finset.mul_sum]
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← integral_mul_const]
  exact integral_congr_ae (ae_of_all _ fun ω => by ring)

/-! ## The common refinement of two partitions -/

/-- Cochrane (2023), A1 §1.6, p. 567: clamping telescopes. For strictly increasing `q` and
`q_0 ≤ x`, `Σ_{j<n}(f(max(q_j, min(x, q_{j+1}))) − f(q_j)) = f(min(x, q_n)) − f(q_0)`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.sum_clamp_sub). -/
theorem sum_clamp_sub (f : ℝ → ℝ) {q : ℕ → ℝ} (hq : StrictMono q) {x : ℝ} (hx : q 0 ≤ x)
    (n : ℕ) :
    ∑ j ∈ Finset.range n, (f (max (q j) (min x (q (j + 1)))) - f (q j))
      = f (min x (q n)) - f (q 0) := by
  induction n with
  | zero => simp [min_eq_right hx]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hlt := hq (Nat.lt_succ_self n)
    rcases le_or_gt x (q n) with h | h
    · rw [min_eq_left h, min_eq_left (h.trans hlt.le), max_eq_left h]
      ring
    · rw [min_eq_right h.le, max_eq_right (le_min h.le hlt.le)]
      ring

/-- Cochrane (2023), A1 §1.6, p. 567: the left end `max(p_i, q_j)` of the cell
`(p_i, p_{i+1}] ∩ (q_j, q_{j+1}]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.cellA). -/
noncomputable def cellA {s t : ℝ} (p q : Partition s t) (i j : ℕ) : ℝ := max (p.t i) (q.t j)

/-- Cochrane (2023), A1 §1.6, p. 567: the right end of the cell
`(p_i, p_{i+1}] ∩ (q_j, q_{j+1}]`, `max(cellA, min(p_{i+1}, q_{j+1}))` (equal to the left end
when the cell is empty).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.cellB). -/
noncomputable def cellB {s t : ℝ} (p q : Partition s t) (i j : ℕ) : ℝ :=
  max (cellA p q i j) (min (p.t (i + 1)) (q.t (j + 1)))

/-- Cochrane (2023), A1 §1.6, p. 567: the cell of `(i, j)` for `(p, q)` is the cell of `(j, i)`
for `(q, p)` (left end).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.cellA_comm). -/
theorem cellA_comm {s t : ℝ} (p q : Partition s t) (i j : ℕ) : cellA q p j i = cellA p q i j :=
  max_comm _ _

/-- Cochrane (2023), A1 §1.6, p. 567: the cell of `(i, j)` for `(p, q)` is the cell of `(j, i)`
for `(q, p)` (right end).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.cellB_comm). -/
theorem cellB_comm {s t : ℝ} (p q : Partition s t) (i j : ℕ) : cellB q p j i = cellB p q i j := by
  rw [cellB, cellB, cellA_comm, min_comm]

/-- Cochrane (2023), A1 §1.6, p. 567: `cellA ≤ cellB`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.cellA_le_cellB). -/
theorem cellA_le_cellB {s t : ℝ} (p q : Partition s t) (i j : ℕ) :
    cellA p q i j ≤ cellB p q i j := le_max_left _ _

/-- Cochrane (2023), A1 §1.6, p. 567: the clamp of `p_i, p_{i+1}` into `[q_j, q_{j+1}]` has the
same `f`-increment as the cell.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.clamp_sub_eq_cell). -/
theorem clamp_sub_eq_cell (f : ℝ → ℝ) {s t : ℝ} (p q : Partition s t) (i j : ℕ) :
    f (max (q.t j) (min (p.t (i + 1)) (q.t (j + 1)))) - f (max (q.t j) (min (p.t i) (q.t (j + 1))))
      = f (cellB p q i j) - f (cellA p q i j) := by
  have hp := p.strictMono (Nat.lt_succ_self i)
  have hq := q.strictMono (Nat.lt_succ_self j)
  rcases le_or_gt (p.t (i + 1)) (q.t j) with h1 | h1
  · have hA : cellA p q i j = q.t j := max_eq_right (hp.le.trans h1)
    have hB : cellB p q i j = q.t j := by
      rw [cellB, hA]; exact max_eq_left ((min_le_left _ _).trans h1)
    rw [hA, hB, max_eq_left ((min_le_left _ _).trans h1),
      max_eq_left ((min_le_left _ _).trans (hp.le.trans h1))]
  rcases le_or_gt (q.t (j + 1)) (p.t i) with h2 | h2
  · have hA : cellA p q i j = p.t i := max_eq_left (hq.le.trans h2)
    have hB : cellB p q i j = p.t i := by
      rw [cellB, hA]; exact max_eq_left ((min_le_right _ _).trans h2)
    rw [hA, hB, min_eq_right (h2.trans hp.le), min_eq_right h2]
    ring
  have hm : max (p.t i) (q.t j) ≤ min (p.t (i + 1)) (q.t (j + 1)) :=
    max_le (le_min hp.le h2.le) (le_min h1.le hq.le)
  have hB : cellB p q i j = min (p.t (i + 1)) (q.t (j + 1)) := max_eq_right hm
  rw [hB, show cellA p q i j = max (p.t i) (q.t j) from rfl,
    max_eq_right ((le_max_right _ _).trans hm), min_eq_left h2.le, max_comm (q.t j)]

/-- **Cochrane (2023), A1 §1.6, p. 567: the cells refine `p`.** For partitions `p, q` of
`[s, t]` and `i < p.n`, `f(p_{i+1}) − f(p_i) = Σ_{j<q.n}(f(cellB) − f(cellA))`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.sub_eq_sum_cells). -/
theorem sub_eq_sum_cells (f : ℝ → ℝ) {s t : ℝ} (p q : Partition s t) {i : ℕ} (hi : i < p.n) :
    f (p.t (i + 1)) - f (p.t i)
      = ∑ j ∈ Finset.range q.n, (f (cellB p q i j) - f (cellA p q i j)) := by
  have h1 := sum_clamp_sub f q.strictMono (x := p.t (i + 1))
    (by rw [q.first]; exact (t_mem p hi).1) q.n
  have h0 := sum_clamp_sub f q.strictMono (x := p.t i)
    (by rw [q.first]; exact (t_mem p hi.le).1) q.n
  rw [q.last, min_eq_left (t_mem p hi).2] at h1
  rw [q.last, min_eq_left (t_mem p hi.le).2] at h0
  have e : f (p.t (i + 1)) - f (p.t i) = (f (p.t (i + 1)) - f (q.t 0)) - (f (p.t i) - f (q.t 0)) :=
    by ring
  rw [e, ← h1, ← h0, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← clamp_sub_eq_cell f p q i j]
  ring

/-- **Cochrane (2023), A1 §1.6, p. 567: the cells refine `q`.** For partitions `p, q` of
`[s, t]` and `j < q.n`, `f(q_{j+1}) − f(q_j) = Σ_{i<p.n}(f(cellB) − f(cellA))`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.sub_eq_sum_cells'). -/
theorem sub_eq_sum_cells' (f : ℝ → ℝ) {s t : ℝ} (p q : Partition s t) {j : ℕ} (hj : j < q.n) :
    f (q.t (j + 1)) - f (q.t j)
      = ∑ i ∈ Finset.range p.n, (f (cellB p q i j) - f (cellA p q i j)) := by
  rw [sub_eq_sum_cells f q p hj]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cellA_comm, cellB_comm]

/-- Cochrane (2023), A1 §1.6, p. 567: the cell lengths add up to `t − s`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.sum_cells_eq). -/
theorem sum_cells_eq {s t : ℝ} (p q : Partition s t) :
    ∑ k ∈ Finset.range p.n ×ˢ Finset.range q.n, (cellB p q k.1 k.2 - cellA p q k.1 k.2)
      = t - s := by
  rw [Finset.sum_product, ← sum_step_eq p]
  exact Finset.sum_congr rfl fun i hi => (sub_eq_sum_cells id p q (Finset.mem_range.1 hi)).symm

/-- Cochrane (2023), A1 §1.6, p. 567: distinct cells do not overlap.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.cells_disjoint). -/
theorem cells_disjoint {s t : ℝ} (p q : Partition s t) :
    ∀ k ∈ Finset.range p.n ×ˢ Finset.range q.n, ∀ l ∈ Finset.range p.n ×ˢ Finset.range q.n,
      k ≠ l → cellB p q k.1 k.2 ≤ cellA p q l.1 l.2 ∨ cellB p q l.1 l.2 ≤ cellA p q k.1 k.2 ∨
        cellA p q k.1 k.2 = cellB p q k.1 k.2 ∨ cellA p q l.1 l.2 = cellB p q l.1 l.2 := by
  intro k _ l _ hkl
  -- a nonempty cell ends at `min(p_{i+1}, q_{j+1})`
  have hend : ∀ m : ℕ × ℕ, cellA p q m.1 m.2 = cellB p q m.1 m.2 ∨
      cellB p q m.1 m.2 = min (p.t (m.1 + 1)) (q.t (m.2 + 1)) := by
    intro m
    rcases le_total (cellA p q m.1 m.2) (min (p.t (m.1 + 1)) (q.t (m.2 + 1))) with h | h
    · exact Or.inr (max_eq_right h)
    · exact Or.inl (max_eq_left h).symm
  have key : ∀ m m' : ℕ × ℕ, (m.1 < m'.1 ∨ m.2 < m'.2) →
      cellB p q m.1 m.2 ≤ cellA p q m'.1 m'.2 ∨ cellA p q m.1 m.2 = cellB p q m.1 m.2 := by
    intro m m' hmm
    rcases hend m with h | h
    · exact Or.inr h
    · left
      rw [h]
      rcases hmm with h1 | h1
      · exact (min_le_left _ _).trans ((p.strictMono.monotone h1).trans (le_max_left _ _))
      · exact (min_le_right _ _).trans ((q.strictMono.monotone h1).trans (le_max_right _ _))
  have hne : k.1 ≠ l.1 ∨ k.2 ≠ l.2 := by
    by_contra h
    push Not at h
    exact hkl (Prod.ext h.1 h.2)
  rcases hne with h | h
  · rcases lt_or_gt_of_ne h with h' | h'
    · rcases key k l (Or.inl h') with h'' | h''
      · exact Or.inl h''
      · exact Or.inr (Or.inr (Or.inl h''))
    · rcases key l k (Or.inl h') with h'' | h''
      · exact Or.inr (Or.inl h'')
      · exact Or.inr (Or.inr (Or.inr h''))
  · rcases lt_or_gt_of_ne h with h' | h'
    · rcases key k l (Or.inr h') with h'' | h''
      · exact Or.inl h''
      · exact Or.inr (Or.inr (Or.inl h''))
    · rcases key l k (Or.inr h') with h'' | h''
      · exact Or.inr (Or.inl h'')
      · exact Or.inr (Or.inr (Or.inr h''))

/-- Cochrane (2023), A1 §1.6, p. 567: on a nonempty cell, `|p_i − q_j| ≤ max(mesh p, mesh q)`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.abs_sub_le_of_cell). -/
theorem abs_sub_le_of_cell {s t : ℝ} (p q : Partition s t) {i j : ℕ} (hi : i < p.n)
    (hj : j < q.n) (hne : cellA p q i j < cellB p q i j) :
    |p.t i - q.t j| ≤ max (mesh p) (mesh q) := by
  have hm : cellA p q i j < min (p.t (i + 1)) (q.t (j + 1)) := by
    by_contra h
    push Not at h
    rw [cellB, max_eq_left h] at hne
    exact lt_irrefl _ hne
  have h1 : q.t j < p.t (i + 1) := (le_max_right _ _).trans_lt (hm.trans_le (min_le_left _ _))
  have h2 : p.t i < q.t (j + 1) := (le_max_left _ _).trans_lt (hm.trans_le (min_le_right _ _))
  rw [abs_le]
  constructor
  · have := le_mesh p hi
    linarith [le_max_left (mesh p) (mesh q)]
  · have := le_mesh q hj
    linarith [le_max_right (mesh p) (mesh q)]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the difference of two left-point sums is an
elementary integral over the common refinement**:
`I_p(H) − I_q(H) = Σ_{i,j}(H_{p_i} − H_{q_j})(W_{cellB} − W_{cellA})`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.itoSum_sub_itoSum). -/
theorem itoSum_sub_itoSum {s t : ℝ} (H : ℝ → Ω → ℝ) (p q : Partition s t) (ω : Ω) :
    itoSum W H p ω - itoSum W H q ω
      = cellSum W (Finset.range p.n ×ˢ Finset.range q.n) (fun k => cellA p q k.1 k.2)
        (fun k => cellB p q k.1 k.2) (fun k ω => H (p.t k.1) ω - H (q.t k.2) ω) ω := by
  have hp : itoSum W H p ω = ∑ i ∈ Finset.range p.n, ∑ j ∈ Finset.range q.n,
      H (p.t i) ω * incr W (cellA p q i j) (cellB p q i j) ω := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.mul_sum]
    congr 1
    exact sub_eq_sum_cells (fun u => bmReal W u ω) p q (Finset.mem_range.1 hi)
  have hq : itoSum W H q ω = ∑ j ∈ Finset.range q.n, ∑ i ∈ Finset.range p.n,
      H (q.t j) ω * incr W (cellA p q i j) (cellB p q i j) ω := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.mul_sum]
    congr 1
    exact sub_eq_sum_cells' (fun u => bmReal W u ω) p q (Finset.mem_range.1 hj)
  rw [hp, hq, Finset.sum_comm (s := Finset.range q.n), cellSum, Finset.sum_product,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the isometry for the difference of two left-point
sums**: `E[(I_p(H) − I_q(H))²] = Σ_{i,j} E[(H_{p_i} − H_{q_j})²]·|cell_{ij}|`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.integral_itoSum_sub_sq). -/
theorem integral_itoSum_sub_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {s t : ℝ} (hs : 0 ≤ s) {H : ℝ → Ω → ℝ}
    (hH : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) (p q : Partition s t) :
    ∫ ω, (itoSum W H p ω - itoSum W H q ω) ^ 2 ∂P
      = ∑ k ∈ Finset.range p.n ×ˢ Finset.range q.n,
          (∫ ω, (H (p.t k.1) ω - H (q.t k.2) ω) ^ 2 ∂P) *
            (cellB p q k.1 k.2 - cellA p q k.1 k.2) := by
  classical
  simp_rw [itoSum_sub_itoSum H p q]
  have hmem : ∀ k ∈ Finset.range p.n ×ˢ Finset.range q.n,
      p.t k.1 ∈ Set.Icc s t ∧ q.t k.2 ∈ Set.Icc s t := by
    intro k hk
    rw [Finset.mem_product] at hk
    exact ⟨t_mem p (Finset.mem_range.1 hk.1).le, t_mem q (Finset.mem_range.1 hk.2).le⟩
  have h := integral_mul_cellSum_sq hB hW h𝓕 (r := s) hs
    (S := Finset.range p.n ×ˢ Finset.range q.n) (a := fun k => cellA p q k.1 k.2)
    (b := fun k => cellB p q k.1 k.2) (ξ := fun k ω => H (p.t k.1) ω - H (q.t k.2) ω)
    (fun k hk => (hmem k hk).1.1.trans (le_max_left _ _))
    (fun k _ => cellA_le_cellB p q k.1 k.2)
    (fun k hk => ((hH _ (hmem k hk).1).mono (𝓕.mono (le_max_left _ _))).sub
      ((hH _ (hmem k hk).2).mono (𝓕.mono (le_max_right _ _))))
    (C := 2 * C) (fun k hk ω => by
      rw [two_mul]
      exact (abs_sub _ _).trans (add_le_add (hHb _ (hmem k hk).1 ω) (hHb _ (hmem k hk).2 ω)))
    (cells_disjoint p q) (G := fun _ => 1) stronglyMeasurable_const (CG := 1) (fun _ => by simp)
  simpa using h

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the Cauchy estimate for left-point sums.** If
`E[(H_u − H_v)²] ≤ ε` for all `u, v ∈ [s, t]` with `|u − v| ≤ δ`, then
`E[(I_p(H) − I_q(H))²] ≤ ε(t − s)` for all partitions `p, q` of `[s, t]` with meshes `≤ δ`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.integral_itoSum_sub_sq_le). -/
theorem integral_itoSum_sub_sq_le (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {s t : ℝ} (hs : 0 ≤ s) {H : ℝ → Ω → ℝ}
    (hH : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) {ε δ : ℝ}
    (hδ : ∀ u ∈ Set.Icc s t, ∀ v ∈ Set.Icc s t, |u - v| ≤ δ →
      ∫ ω, (H u ω - H v ω) ^ 2 ∂P ≤ ε)
    (p q : Partition s t) (hp : mesh p ≤ δ) (hq : mesh q ≤ δ) :
    ∫ ω, (itoSum W H p ω - itoSum W H q ω) ^ 2 ∂P ≤ ε * (t - s) := by
  rw [integral_itoSum_sub_sq hB hW h𝓕 hs hH hHb p q, ← sum_cells_eq p q, Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.mem_product] at hk
  have hi := Finset.mem_range.1 hk.1
  have hj := Finset.mem_range.1 hk.2
  rcases (cellA_le_cellB p q k.1 k.2).lt_or_eq with hne | heq
  · refine mul_le_mul_of_nonneg_right ?_ (sub_nonneg.2 hne.le)
    exact hδ _ (t_mem p hi.le) _ (t_mem q hj.le)
      ((abs_sub_le_of_cell p q hi hj hne).trans (max_le hp hq))
  · rw [heq, sub_self, mul_zero, mul_zero]

/-! ## Concatenation of partitions -/

/-- Cochrane (2023), A1 §1.6, p. 567: the points of the concatenation of a partition of `[s, r]`
and one of `[r, t]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.concatT). -/
noncomputable def concatT {s r t : ℝ} (p : Partition s r) (q : Partition r t) (i : ℕ) : ℝ :=
  if i ≤ p.n then p.t i else q.t (i - p.n)

/-- Cochrane (2023), A1 §1.6, p. 567: the concatenated points from index `p.n` on are those of
`q`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.concatT_add). -/
theorem concatT_add {s r t : ℝ} (p : Partition s r) (q : Partition r t) (i : ℕ) :
    concatT p q (p.n + i) = q.t i := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    simp [concatT, p.last, q.first]
  · simp only [concatT, show ¬ (p.n + i ≤ p.n) by omega, ↓reduceIte]
    congr 1
    omega

/-- Cochrane (2023), A1 §1.6, p. 567: the concatenated points up to index `p.n` are those of
`p`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.concatT_of_le). -/
theorem concatT_of_le {s r t : ℝ} (p : Partition s r) (q : Partition r t) {i : ℕ}
    (hi : i ≤ p.n) : concatT p q i = p.t i := by
  simp only [concatT, hi, ↓reduceIte]

/-- Cochrane (2023), A1 §1.6, p. 567: **the concatenation** of a partition of `[s, r]` and a
partition of `[r, t]`, a partition of `[s, t]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.concat). -/
noncomputable def concat {s r t : ℝ} (p : Partition s r) (q : Partition r t) : Partition s t where
  n := p.n + q.n
  t := concatT p q
  strictMono := by
    intro i j hij
    rcases le_or_gt j p.n with hj | hj
    · rw [concatT_of_le p q hj, concatT_of_le p q (hij.le.trans hj)]
      exact p.strictMono hij
    · obtain ⟨j', rfl⟩ : ∃ j', j = p.n + j' := ⟨j - p.n, by omega⟩
      rw [concatT_add]
      rcases le_or_gt i p.n with hi | hi
      · rw [concatT_of_le p q hi]
        calc p.t i ≤ p.t p.n := p.strictMono.monotone hi
          _ = q.t 0 := by rw [p.last, q.first]
          _ < q.t j' := q.strictMono (by omega)
      · obtain ⟨i', rfl⟩ : ∃ i', i = p.n + i' := ⟨i - p.n, by omega⟩
        rw [concatT_add]
        exact q.strictMono (by omega)
  first := by rw [concatT_of_le p q (Nat.zero_le _), p.first]
  last := by rw [concatT_add, q.last]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the left-point sum over a concatenation is the sum of
the two left-point sums.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.itoSum_concat). -/
theorem itoSum_concat {s r t : ℝ} (H : ℝ → Ω → ℝ) (p : Partition s r) (q : Partition r t)
    (ω : Ω) : itoSum W H (concat p q) ω = itoSum W H p ω + itoSum W H q ω := by
  simp only [itoSum, concat]
  rw [Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [concatT_of_le p q hi'.le, concatT_of_le p q hi']
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [concatT_add, add_assoc, concatT_add]

/-- Cochrane (2023), A1 §1.6, p. 567: the mesh of a partition is nonnegative.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.mesh_nonneg). -/
theorem mesh_nonneg {s t : ℝ} (p : Partition s t) : 0 ≤ mesh p :=
  Real.iSup_nonneg fun i => (step_pos p i).le

/-- Cochrane (2023), A1 §1.6, p. 567: the mesh of a concatenation is at most the larger mesh.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoSums.mesh_concat_le). -/
theorem mesh_concat_le {s r t : ℝ} (p : Partition s r) (q : Partition r t) :
    mesh (concat p q) ≤ max (mesh p) (mesh q) := by
  have hne : ∀ i : Fin (concat p q).n,
      (concat p q).t ((i : ℕ) + 1) - (concat p q).t i ≤ max (mesh p) (mesh q) := by
    intro i
    have hi := i.2
    simp only [concat] at hi ⊢
    rcases lt_or_ge (i : ℕ) p.n with h | h
    · rw [concatT_of_le p q h, concatT_of_le p q h.le]
      exact (le_mesh p h).trans (le_max_left _ _)
    · obtain ⟨j, hj⟩ : ∃ j, (i : ℕ) = p.n + j := ⟨i - p.n, by omega⟩
      rw [hj, add_assoc, concatT_add, concatT_add]
      exact (le_mesh q (by omega)).trans (le_max_right _ _)
  rcases isEmpty_or_nonempty (Fin (concat p q).n) with he | he
  · rw [mesh, Real.iSup_of_isEmpty]
    exact (mesh_nonneg p).trans (le_max_left _ _)
  · exact ciSup_le hne

end Cochrane.LongTermDebtDynamics.TidyR7ItoSums
