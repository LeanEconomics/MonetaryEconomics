/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR12SDEExist
import Monetarism.TidyR10DoobVersion

/-!
# Continuous versions: the mean-square time integral and the SDE solution

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34) (Track 3, chunk B4). The SDE solution of
`TidyR12SDEExist` is a mean-square continuous process, specified at fixed times only. B3 gave
`∫_s^t H dW` an adapted continuous version (`TidyR10DoobMSVersion`); here the mean-square time
integral `t ↦ ∫_s^t G du` gets a continuous modification, and so does the SDE solution, which
then gets an adapted a.s.-continuous version on `ℝ` (B3's
`TidyR10DoobVersion.exists_adapted_continuous_version`).

## The device

The stopped left-point sums of B3 (`TidyR7ItoContinuity.truncSum`) taken against the
deterministic path `idPath` (`W_u = u`) are the stopped Riemann sums
`Σ G_{t_i}(t_{i+1}∧t − t_i∧t)`, continuous in `t` for every `ω`. The difference of two of them is
bounded **uniformly in `t`** by `Σ_{cells} |G_{p_i} − G_{q_j}|·|cell|`
(`abs_truncSum_idPath_sub_le`), whose second moment is `≤ ε(T − s)²`
(`integral_dtBound_sq_le`): no maximal inequality is needed.
Borel–Cantelli along a fast subsequence of dyadic partitions gives a.s. uniform convergence.

## Main results

* **`exists_continuous_modification_dtInt`**: for `G` mean-square continuous on `[s, T]`,
  `0 ≤ s < T`, there is `X` with `X_t = ∫_s^t G du` a.s. for every `t ∈ [s, T]` and a.s.
  continuous paths on `[s, T]`.
* **`exists_continuous_modification_sdeSol`**: the SDE solution has a modification with a.s.
  continuous paths on `[s, T]` (W with a.s. continuous paths).
* **`exists_adapted_continuous_sdeSol`**: it has an **adapted** version on `[s, T]`
  (`X_t` `𝓕_t`-measurable, `X_t = sdeSol_t` a.s. for every `t ∈ [s, T]`) with a.s. continuous
  paths on `ℝ`.
-/

namespace Cochrane.Monetarism.TidyR12SDEVersion

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoSums Cochrane.Monetarism.TidyR7ItoIntegral
  Cochrane.Monetarism.TidyR7ItoUnbounded Cochrane.Monetarism.TidyR7ItoProducts
  Cochrane.Monetarism.TidyR7ItoContinuity Cochrane.Monetarism.TidyR10DoobMSVersion
  Cochrane.Monetarism.TidyR10DoobVersion
  Cochrane.Monetarism.TidyR12SDETools Cochrane.Monetarism.TidyR12SDEProcess
  Cochrane.Monetarism.TidyR12SDEPicard Cochrane.Monetarism.TidyR12SDEExist
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ mΩ}
  {s T : ℝ}

/-! ## The deterministic path -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the deterministic path `W_u = u`, against which the
left-point sums are Riemann sums. -/
def idPath : ℝ≥0 → Ω → ℝ := fun t _ => (t : ℝ)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: increments of `idPath` are increments of time on
`[0, ∞)`. -/
lemma incr_idPath {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ω : Ω) :
    incr (idPath (Ω := Ω)) a b ω = b - a := by
  simp only [incr, bmReal, idPath, Real.coe_toNNReal _ ha, Real.coe_toNNReal _ (ha.trans hab)]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: stopped increments of `idPath` are at most the cell
length, `|(b∧t)⁺ − (a∧t)⁺| ≤ b − a` for `a ≤ b`. -/
lemma abs_incr_idPath_min_le {a b : ℝ} (hab : a ≤ b) (t : ℝ) (ω : Ω) :
    |incr (idPath (Ω := Ω)) (min a t) (min b t) ω| ≤ b - a := by
  simp only [incr, bmReal, idPath, Real.coe_toNNReal']
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero, abs_of_nonneg (sub_nonneg.2 hab)]
  exact max_le le_rfl (sub_nonneg.2 hab)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: against `idPath`, left-point sums are Riemann sums
(partitions of `[a, b]`, `0 ≤ a`). -/
lemma itoSum_idPath {a b : ℝ} (ha : 0 ≤ a) (G : ℝ → Ω → ℝ) (q : Partition a b) (ω : Ω) :
    itoSum (idPath (Ω := Ω)) G q ω = dtSum G q ω := by
  simp only [itoSum, dtSum, riemannSum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hm := t_mem q (Finset.mem_range.1 hi).le
  rw [incr_idPath (ha.trans hm.1) (q.strictMono.monotone (Nat.le_succ i))]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the stopped Riemann sum is continuous in the stopping
time, for every `ω`. -/
lemma continuous_truncSum_idPath (G : ℝ → Ω → ℝ) (p : Partition s T) (ω : Ω) :
    Continuous fun t => truncSum (idPath (Ω := Ω)) G p t ω :=
  continuous_truncSum G p (W := idPath) NNReal.continuous_coe

/-! ## The uniform bound -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the cell bound `Σ_{(i,j)} |G_{p_i} − G_{q_j}|·|cell|`
for two partitions of `[s, T]`. -/
noncomputable def dtBound (G : ℝ → Ω → ℝ) (p q : Partition s T) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range p.n ×ˢ Finset.range q.n,
    (cellB p q k.1 k.2 - cellA p q k.1 k.2) * |G (p.t k.1) ω - G (q.t k.2) ω|

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the stopped Riemann sums of two partitions differ by
at most `dtBound`, uniformly in the stopping time.** -/
theorem abs_truncSum_idPath_sub_le (G : ℝ → Ω → ℝ) (p q : Partition s T) (t : ℝ) (ω : Ω) :
    |truncSum (idPath (Ω := Ω)) G p t ω - truncSum idPath G q t ω| ≤ dtBound G p q ω := by
  rw [truncSum_sub_truncSum, cellSum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_incr_idPath_min_le (cellA_le_cellB p q k.1 k.2) t ω)
    (abs_nonneg _)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `dtBound` is square integrable. -/
theorem memLp_dtBound {G : ℝ → Ω → ℝ} (hG : MSIntegrand P 𝓕 G s T) (p q : Partition s T) :
    MemLp (dtBound G p q) 2 P := by
  refine memLp_finsetSum _ fun k hk => ?_
  rw [Finset.mem_product] at hk
  exact (((hG.memLp _ (t_mem p (Finset.mem_range.1 hk.1).le)).sub
    (hG.memLp _ (t_mem q (Finset.mem_range.1 hk.2).le))).abs).const_mul _

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the second moment of the cell bound**: if
`E[(G_u − G_v)²] ≤ ε` whenever `|u − v| ≤ δ`, then `E[dtBound²] ≤ ε(T − s)²` for partitions with
meshes `≤ δ`.
The `|·|` version of `TidyR7ItoProducts.integral_dtSum_sub_sq_le`. -/
theorem integral_dtBound_sq_le {G : ℝ → Ω → ℝ} (hG : ∀ u ∈ Set.Icc s T, MemLp (G u) 2 P)
    {ε δ : ℝ} (hδ : ∀ u ∈ Set.Icc s T, ∀ v ∈ Set.Icc s T, |u - v| ≤ δ →
      ∫ ω, (G u ω - G v ω) ^ 2 ∂P ≤ ε)
    (p q : Partition s T) (hp : mesh p ≤ δ) (hq : mesh q ≤ δ) :
    ∫ ω, dtBound G p q ω ^ 2 ∂P ≤ ε * (T - s) ^ 2 := by
  classical
  set S := Finset.range p.n ×ˢ Finset.range q.n with hS
  set w : ℕ × ℕ → ℝ := fun k => cellB p q k.1 k.2 - cellA p q k.1 k.2 with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => sub_nonneg.2 (cellA_le_cellB p q k.1 k.2)
  have hsw : ∑ k ∈ S, w k = T - s := sum_cells_eq p q
  have hmem : ∀ k ∈ S, p.t k.1 ∈ Set.Icc s T ∧ q.t k.2 ∈ Set.Icc s T := by
    intro k hk
    rw [hS, Finset.mem_product] at hk
    exact ⟨t_mem p (Finset.mem_range.1 hk.1).le, t_mem q (Finset.mem_range.1 hk.2).le⟩
  have hc2 : ∀ k ∈ S, Integrable (fun ω => (G (p.t k.1) ω - G (q.t k.2) ω) ^ 2) P :=
    fun k hk => ((hG _ (hmem k hk).1).sub (hG _ (hmem k hk).2)).integrable_sq
  have hpt : ∀ ω, dtBound G p q ω ^ 2
      ≤ (T - s) * ∑ k ∈ S, w k * (G (p.t k.1) ω - G (q.t k.2) ω) ^ 2 := by
    intro ω
    simp only [dtBound]
    rw [← hsw]
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S (fun k _ => hw0 k)
      (fun k _ => mul_nonneg (hw0 k) (sq_nonneg _)) fun k _ => le_of_eq ?_
    rw [mul_pow, sq_abs]
    ring
  have iR : Integrable (fun ω => (T - s) * ∑ k ∈ S, w k *
      (G (p.t k.1) ω - G (q.t k.2) ω) ^ 2) P :=
    (integrable_finsetSum _ fun k hk => (hc2 k hk).const_mul _).const_mul _
  have mB : MemLp (dtBound G p q) 2 P := memLp_finsetSum _ fun k hk =>
    (((hG _ (hmem k hk).1).sub (hG _ (hmem k hk).2)).abs).const_mul _
  have iL : Integrable (fun ω => dtBound G p q ω ^ 2) P := mB.integrable_sq
  have hts : 0 ≤ T - s := sub_nonneg.2 (a_le_b p)
  calc ∫ ω, dtBound G p q ω ^ 2 ∂P
      ≤ ∫ ω, (T - s) * ∑ k ∈ S, w k * (G (p.t k.1) ω - G (q.t k.2) ω) ^ 2 ∂P :=
        integral_mono iL iR hpt
    _ = (T - s) * ∑ k ∈ S, w k * ∫ ω, (G (p.t k.1) ω - G (q.t k.2) ω) ^ 2 ∂P := by
        rw [integral_const_mul, integral_finsetSum _ fun k hk => (hc2 k hk).const_mul _]
        simp_rw [integral_const_mul]
    _ ≤ (T - s) * ∑ k ∈ S, w k * ε := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => ?_) hts
        rw [hS, Finset.mem_product] at hk
        have hi := Finset.mem_range.1 hk.1
        have hj := Finset.mem_range.1 hk.2
        rcases (cellA_le_cellB p q k.1 k.2).lt_or_eq with hne | heq
        · refine mul_le_mul_of_nonneg_left ?_ (hw0 k)
          exact hδ _ (t_mem p hi.le) _ (t_mem q hj.le)
            ((abs_sub_le_of_cell p q hi hj hne).trans (max_le hp hq))
        · simp only [hw, heq, sub_self, zero_mul, le_refl]
    _ = ε * (T - s) ^ 2 := by rw [← Finset.sum_mul, hsw]; ring

/-! ## The continuous modification of the time integral -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: a continuous modification of `t ↦ ∫_s^t G du`.**
For `G` mean-square continuous on `[s, T]`, `0 ≤ s < T`, and `P` a probability measure, there
is `X` with `X_t = ∫_s^t G du` (mean-square time integral) a.s. for every `t ∈ [s, T]` and a.s.
continuous paths on `[s, T]`. The time-integral analogue of
`TidyR10DoobMSVersion.exists_continuous_modification_ms`. -/
theorem exists_continuous_modification_dtInt [IsProbabilityMeasure P] (hs : 0 ≤ s)
    (hsT : s < T) {G : ℝ → Ω → ℝ} (hG : MSIntegrand P 𝓕 G s T) :
    ∃ X : ℝ → Ω → ℝ, (∀ t ∈ Set.Icc s T, X t =ᵐ[P] dtInt P 𝓕 G s t) ∧
      ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Icc s T) := by
  set d : ℕ → Partition s T := fun n => dyadic hsT n with hd
  have hts : 0 < T - s := sub_pos.2 hsT
  have hcau : ∀ j : ℕ, ∃ N, ∀ m ≥ N, ∀ m' ≥ N,
      ∫ ω, dtBound G (d m) (d m') ω ^ 2 ∂P ≤ (1 / 8) ^ j := by
    intro j
    obtain ⟨δ, hδ, hδG⟩ := hG.cont ((1 / 8) ^ j / (T - s) ^ 2) (by positivity)
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_mesh_dyadic hsT).eventually (ge_mem_nhds hδ))
    refine ⟨N, fun m hm m' hm' => ?_⟩
    refine (integral_dtBound_sq_le hG.memLp hδG _ _ (hN m hm) (hN m' hm')).trans_eq ?_
    field_simp
  choose N hN using hcau
  set n : ℕ → ℕ := fun j => ∑ i ∈ Finset.range (j + 1), N i + j with hn
  have hnN : ∀ j, N j ≤ n j := fun j =>
    (Finset.single_le_sum (fun i _ => Nat.zero_le (N i)) (Finset.self_mem_range_succ j)).trans
      (Nat.le_add_right _ _)
  have hnmono : StrictMono n := strictMono_nat_of_lt_succ fun j => by
    simp only [hn, Finset.sum_range_succ (n := j + 1)]
    omega
  set Sb : ℕ → Ω → ℝ := fun j => dtBound G (d (n (j + 1))) (d (n j)) with hSb
  have hSm : ∀ j, MemLp (Sb j) 2 P := fun j => memLp_dtBound hG _ _
  have hET : ∀ j, ∫ ω, Sb j ω ^ 2 ∂P ≤ (1 / 8) ^ j := fun j =>
    hN j _ ((hnN j).trans (hnmono.monotone (Nat.le_succ j))) _ (hnN j)
  set D : ℕ → ℝ → Ω → ℝ := fun j τ ω =>
    truncSum idPath G (d (n (j + 1))) τ ω - truncSum idPath G (d (n j)) τ ω with hD
  have hDS : ∀ j τ ω, |D j τ ω| ≤ Sb j ω := fun j τ ω => abs_truncSum_idPath_sub_le G _ _ τ ω
  -- the bad events, Markov and Borel–Cantelli
  set E : ℕ → Set Ω := fun j => {ω | (1 / 2) ^ j ≤ Sb j ω} with hE
  have hEbd : ∀ j, P (E j) ≤ ENNReal.ofReal (4 * (1 / 2) ^ j) := by
    intro j
    have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => sq_nonneg (Sb j ω))
      (hSm j).integrable_sq ((1 / 4) ^ j)
    have hsub : E j ⊆ {ω | (1 / 4 : ℝ) ^ j ≤ Sb j ω ^ 2} := by
      intro ω hω
      have h : (1 / 2 : ℝ) ^ j ≤ Sb j ω := hω
      change (1 / 4 : ℝ) ^ j ≤ Sb j ω ^ 2
      have e : (1 / 4 : ℝ) ^ j = ((1 / 2) ^ j) ^ 2 := by
        rw [← pow_mul, mul_comm j 2, pow_mul]
        norm_num
      rw [e]
      exact pow_le_pow_left₀ (by positivity) h 2
    have h2 : (1 / 4 : ℝ) ^ j * P.real (E j) ≤ (1 / 4) ^ j * (4 * (1 / 2) ^ j) := by
      calc (1 / 4 : ℝ) ^ j * P.real (E j)
          ≤ (1 / 4) ^ j * P.real {ω | (1 / 4 : ℝ) ^ j ≤ Sb j ω ^ 2} :=
            mul_le_mul_of_nonneg_left (measureReal_mono hsub (measure_ne_top _ _))
              (by positivity)
        _ ≤ ∫ ω, Sb j ω ^ 2 ∂P := hm
        _ ≤ 4 * (1 / 8) ^ j := by linarith [hET j, pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 8) j]
        _ = (1 / 4) ^ j * (4 * (1 / 2) ^ j) := by
            rw [show (1 / 8 : ℝ) = 1 / 4 * (1 / 2) by norm_num, mul_pow]
            ring
    have h3 : P.real (E j) ≤ 4 * (1 / 2) ^ j := le_of_mul_le_mul_left h2 (by positivity)
    rw [← ofReal_measureReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal h3
  have hsum : ∑' j, P (E j) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hEbd)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 4)]
    exact ENNReal.ofReal_ne_top
  have hae := ae_eventually_notMem hsum
  -- the modification and its uniform convergence on good paths
  set X : ℝ → Ω → ℝ := fun t ω => limUnder atTop (fun j => truncSum idPath G (d (n j)) t ω)
    with hX
  have hgood : ∀ᵐ ω ∂P, TendstoUniformlyOn (fun j t => truncSum idPath G (d (n j)) t ω)
      (fun t => X t ω) atTop (Set.Icc s T) := by
    filter_upwards [hae] with ω hω
    obtain ⟨J, hJ⟩ := eventually_atTop.1 hω
    have hdiff : ∀ j ≥ J, ∀ t ∈ Set.Icc s T, |D j t ω| ≤ (1 / 2) ^ j := by
      intro j hj t _
      have h2 : ¬ ((1 / 2 : ℝ) ^ j ≤ Sb j ω) := hJ j hj
      push Not at h2
      exact (hDS j t ω).trans h2.le
    set u : ℕ → ℝ → ℝ := fun m t => truncSum idPath G (d (n (J + m))) t ω with hu_def
    have hu : ∀ t ∈ Set.Icc s T, ∀ m, dist (u m t) (u (m + 1) t) ≤ 2 * (1 / 2) ^ J / 2 / 2 ^ m := by
      intro t ht m
      rw [Real.dist_eq, abs_sub_comm]
      have h := hdiff (J + m) (Nat.le_add_right J m) t ht
      have e : 2 * (1 / 2 : ℝ) ^ J / 2 / 2 ^ m = (1 / 2) ^ (J + m) := by
        rw [pow_add, one_div_pow (2 : ℝ) m]
        ring
      rw [e]
      exact h
    have hconv : ∀ t ∈ Set.Icc s T, Tendsto (fun m => u m t) atTop (𝓝 (X t ω)) := by
      intro t ht
      obtain ⟨a0, ha0⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two (hu t ht))
      have hfull : Tendsto (fun j => truncSum idPath G (d (n j)) t ω) atTop (𝓝 a0) := by
        refine (tendsto_add_atTop_iff_nat J).1 (ha0.congr fun m => ?_)
        simp only [hu_def]
        rw [add_comm]
      change Tendsto (fun m => u m t) atTop
        (𝓝 (limUnder atTop (fun j => truncSum idPath G (d (n j)) t ω)))
      rw [hfull.limUnder_eq]
      exact ha0
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have h0 : Tendsto (fun m : ℕ => 2 * (1 / 2 : ℝ) ^ J / 2 ^ m) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    obtain ⟨M, hM⟩ := (h0.eventually (gt_mem_nhds hε)).exists
    refine eventually_atTop.2 ⟨J + M, fun j hj t ht => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, j = J + m := ⟨j - J, by omega⟩
    have h := dist_le_of_le_geometric_two_of_tendsto (hu t ht) (hconv t ht) m
    rw [dist_comm]
    calc dist (u m t) (X t ω) ≤ 2 * (1 / 2) ^ J / 2 ^ m := h
      _ ≤ 2 * (1 / 2) ^ J / 2 ^ M :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (pow_le_pow_right₀ one_le_two (by omega))
      _ < ε := hM
  have hXcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Icc s T) := by
    filter_upwards [hgood] with ω h1
    exact h1.continuousOn (Frequently.of_forall fun j =>
      (continuous_truncSum_idPath G _ ω).continuousOn)
  refine ⟨X, fun t ht => ?_, hXcont⟩
  rcases ht.1.lt_or_eq with hst | hst
  · have hps : Tendsto (fun j => mesh (restrict (d (n j)) hst ht.2)) atTop (𝓝 0) :=
      squeeze_zero (fun _ => mesh_nonneg _) (fun j => mesh_restrict_le _ _ _)
        ((tendsto_mesh_dyadic hsT).comp hnmono.tendsto_atTop)
    have hL := L2Tendsto_dtSum hst (hG.mono le_rfl ht.2) _ hps
    have hae2 : ∀ᵐ ω ∂P, Tendsto (fun j => dtSum G (restrict (d (n j)) hst ht.2) ω) atTop
        (𝓝 (X t ω)) := by
      filter_upwards [hgood] with ω hω
      refine (hω.tendsto_at ht).congr fun j => ?_
      rw [← truncSum_eq_itoSum_restrict G _ hst ht.2 ω, itoSum_idPath hs]
    exact (ae_eq_of_L2Tendsto_of_ae_tendsto hL hae2).symm
  · have e1 : X t = 0 := by
      funext ω
      have e2 : (fun j => truncSum idPath G (d (n j)) t ω) = fun _ => 0 :=
        funext fun j => truncSum_of_le_start G _ hst.ge ω
      simp only [hX, e2]
      exact tendsto_const_nhds.limUnder_eq
    rw [e1, ← hst, dtInt_of_le le_rfl]

/-! ## The SDE solution -/

variable {W : ℝ≥0 → Ω → ℝ} {b σ : ℝ → ℝ → ℝ} {ξ : Ω → ℝ} {L Kb Kσ : ℝ}

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `sdeSol … t` is `𝓕_t`-strongly measurable for every
`t` (by construction, as `TidyR7ItoIntegral.itoInt`). -/
theorem stronglyMeasurable_sdeSol (t : ℝ) :
    StronglyMeasurable[𝓕 t] (sdeSol P 𝓕 W b σ ξ s t) := by
  classical
  unfold sdeSol
  split_ifs with h
  · exact h.choose_spec.1
  · exact stronglyMeasurable_zero

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the SDE solution has a continuous modification**:
for `W` with a.s. continuous paths, `0 ≤ s < T` and the hypotheses of
`TidyR12SDEExist.sde_existsUnique`, there is `X` with `X_t = sdeSol_t` a.s. for every
`t ∈ [s, T]` and a.s. continuous paths on `[s, T]`
(`ξ + (continuous ∫ b(u, X_u) du) + (continuous ∫ σ(u, X_u) dW)`). -/
theorem exists_continuous_modification_sdeSol (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω) (hs : 0 ≤ s) (hsT : s < T)
    (hb : SDECoeff b s T L Kb) (hσ : SDECoeff σ s T L Kσ) (hξ2 : MemLp ξ 2 P)
    (hξ : StronglyMeasurable[𝓕 s] ξ) :
    ∃ X : ℝ → Ω → ℝ, (∀ t ∈ Set.Icc s T, X t =ᵐ[P] sdeSol P 𝓕 W b σ ξ s t) ∧
      ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Icc s T) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hY := sdeSol_ms hB hW h𝓕 hs hsT.le hb hσ hξ2 hξ
  obtain ⟨D, hD, hDc⟩ := exists_continuous_modification_dtInt hs hsT (hb.msIntegrand_comp hY)
  obtain ⟨I, hI, hIc⟩ := exists_continuous_modification_ms hB hW h𝓕 hcont hs hsT
    (hσ.msIntegrand_comp hY)
  refine ⟨fun t ω => ξ ω + D t ω + I t ω, fun t ht => ?_, ?_⟩
  · filter_upwards [hD t ht, hI t ht, sdeSol_fixed hB hW h𝓕 hs hsT.le hb hσ hξ2 hξ t ht] with
      ω h1 h2 h3
    rw [h3]
    simp only [picard]
    rw [h1, h2]
  · filter_upwards [hDc, hIc] with ω h1 h2
    exact (continuousOn_const.add h1).add h2

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the SDE solution has an adapted a.s.-continuous
version**: for `W` with a.s. continuous paths, `0 ≤ s < T` and the hypotheses of
`TidyR12SDEExist.sde_existsUnique`, there is `X` with `X_t` `𝓕_t`-strongly measurable and
`X_t = sdeSol_t` a.s. for every `t ∈ [s, T]`, and a.s. every path `t ↦ X_t` continuous on `ℝ`
(B3's `TidyR10DoobVersion.exists_adapted_continuous_version` applied to the solution stopped at
`T`). -/
theorem exists_adapted_continuous_sdeSol (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω) (hs : 0 ≤ s) (hsT : s < T)
    (hb : SDECoeff b s T L Kb) (hσ : SDECoeff σ s T L Kσ) (hξ2 : MemLp ξ 2 P)
    (hξ : StronglyMeasurable[𝓕 s] ξ) :
    ∃ X : ℝ → Ω → ℝ, (∀ t ∈ Set.Icc s T, StronglyMeasurable[𝓕 t] (X t)) ∧
      (∀ t ∈ Set.Icc s T, X t =ᵐ[P] sdeSol P 𝓕 W b σ ξ s t) ∧
      ∀ᵐ ω ∂P, Continuous fun t => X t ω := by
  obtain ⟨Xc, hXc, hXcc⟩ := exists_continuous_modification_sdeSol hB hW h𝓕 hcont hs hsT hb hσ
    hξ2 hξ
  have hinit := sdeSol_init hB hW h𝓕 hs hsT.le hb hσ hξ2 hξ
  set Y : ℝ → Ω → ℝ := fun t => if s < t then fun ω => sdeSol P 𝓕 W b σ ξ s (min t T) ω - ξ ω
    else 0 with hYdef
  have hYa : ∀ t, StronglyMeasurable[𝓕 t] (Y t) := by
    intro t
    by_cases h : s < t
    · simp only [hYdef, h, ↓reduceIte]
      exact ((stronglyMeasurable_sdeSol (min t T)).mono (𝓕.mono (min_le_left _ _))).sub
        (hξ.mono (𝓕.mono h.le))
    · simp only [hYdef, h, ↓reduceIte]
      exact stronglyMeasurable_zero
  have hYs : ∀ ω, Y s ω = 0 := fun ω => by simp [hYdef]
  have hmin : ∀ t, s ≤ t → min t T ∈ Set.Icc s T := fun t ht =>
    ⟨le_min ht hsT.le, min_le_right _ _⟩
  have hmod : ∀ N : ℕ, ∃ X : ℝ → Ω → ℝ, (∀ t ∈ Set.Icc s (s + N), X t =ᵐ[P] Y t) ∧
      ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Icc s (s + N)) := by
    intro N
    refine ⟨fun t ω => Xc (min t T) ω - ξ ω, fun t ht => ?_, ?_⟩
    · rcases ht.1.lt_or_eq with h | h
      · filter_upwards [hXc _ (hmin t ht.1)] with ω h1
        simp only [hYdef, h, ↓reduceIte]
        rw [h1]
      · subst h
        filter_upwards [hXc _ (hmin s le_rfl), hinit] with ω h1 h2
        rw [hYs, min_eq_left hsT.le] at *
        rw [h1, h2, sub_self]
    · filter_upwards [hXcc] with ω hω
      refine (hω.comp (continuous_id.min continuous_const).continuousOn fun t ht =>
        hmin t ht.1).sub continuousOn_const
  obtain ⟨Z, hZa, hZY, hZ0, hZc⟩ := exists_adapted_continuous_version (P := P) hYa hYs hmod
  refine ⟨fun t ω => ξ ω + Z t ω, fun t ht => (hξ.mono (𝓕.mono ht.1)).add (hZa t),
    fun t ht => ?_, ?_⟩
  · rcases ht.1.lt_or_eq with h | h
    · filter_upwards [hZY t ht.1] with ω h1
      simp only [h1, hYdef, h, ↓reduceIte, min_eq_left ht.2]
      ring
    · subst h
      filter_upwards [hinit] with ω h1
      rw [hZ0 _ le_rfl, h1, add_zero]
  · filter_upwards [hZc] with ω h
    exact continuous_const.add h

end Cochrane.Monetarism.TidyR12SDEVersion
