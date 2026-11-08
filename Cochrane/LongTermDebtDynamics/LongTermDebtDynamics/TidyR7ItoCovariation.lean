/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR7ItoProcess
import LongTermDebtDynamics.TidyR7ProductStep

/-!
# The sums of the product rule: `Σ X_iΔY_i → ∫X dY` and `Σ ΔX_iΔY_i → ∫ HK du`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for (1.32) with diffusive
bonds (chunk I5d). The exact partition identity
`X_tY_t − X_sY_s = Σ X_iΔY_i + Σ Y_iΔX_i + Σ ΔX_iΔY_i`
(`TidyR7StieltjesCalculus.prod_partition_identity`, here through Track 1's
`TidyR7ProductStep.sumRS` and `TidyR7ProductStep.sumCross`) has three sums; this module finds
their limits along ANY partitions of `[s, t]` with mesh `→ 0`.

## Main results

For `Y` an Itô process (`TidyR7ItoProcess.ItoProcess`, drift `b`, diffusion `K`) and `X` any
mean-square continuous integrand (`TidyR7ItoUnbounded.MSIntegrand`; an Itô process is one,
`TidyR7ItoProcess.ItoProcess.toMS`):

* `L2Tendsto_sumRS` (**`Σ X_{t_i}ΔY_i → ∫_s^t X dY` in `L²`**), where
  `∫ X dY := ∫_s^t X_u b_u du + ∫_s^t X K dW` — the time integral in mean square
  (`TidyR7ItoProducts.dtInt`) plus the Itô integral of the unbounded integrand `X K`. The proof
  splits `X_iΔY_i = X_ib_iΔt_i + X_iD_i + X_iK_iΔW_i + ∫_{t_i}^{t_{i+1}} X_i(K − K_{t_i}) dW`
  (`sumRS_ae_eq`): a Riemann sum, a drift error (`L2Tendsto_driftRem`), a left-point Itô sum,
  and a martingale-difference remainder (`L2Tendsto_diffRem`, orthogonality and the isometry).

For `X`, `Y` Itô processes with diffusions `H`, `K`:

* `tendsto_integral_abs_sumCross` (**the bracket**, `Σ ΔX_iΔY_i → ∫_s^t H_uK_u du` in `L¹`):
  `d[X, Y] = HK dt`. The main term `Σ H_iK_i(ΔW_i)²` is `(dW)² = dt` with left-point weights
  (`TidyR7BrownianQV.tendsto_integral_wqvSum_sq`); every other product has one factor whose
  summed second moments vanish (`TidyR7ItoProcess.tendsto_integral_abs_sum_mul`).
* `tendsto_integral_abs_sumCross_bv`: if `H = 0` (bounded-variation `X`) the bracket vanishes,
  `Σ ΔX_iΔY_i → 0` in `L¹`.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR7ItoCovariation

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.LongTermDebtDynamics.TidyR7StieltjesSums
  Cochrane.LongTermDebtDynamics.TidyR7BrownianTools
  Cochrane.LongTermDebtDynamics.TidyR7BrownianQV Cochrane.LongTermDebtDynamics.TidyR7ItoL2
  Cochrane.LongTermDebtDynamics.TidyR7ItoSums Cochrane.LongTermDebtDynamics.TidyR7ItoIntegral
  Cochrane.LongTermDebtDynamics.TidyR7ItoUnbounded Cochrane.LongTermDebtDynamics.TidyR7ItoProducts
  Cochrane.LongTermDebtDynamics.TidyR7ItoProcess
open Cochrane.LongTermDebtDynamics.TidyR7ProductStep (sumRS sumCross)
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → ℝ} {s t : ℝ}

/-! ## The remainders -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the drift remainder `Σ X_{t_i}D_i`,
`D_i = ∫_{t_i}^{t_{i+1}} b − b_{t_i}Δt_i` (`TidyR7ItoProcess.driftErr`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoCovariation.driftRem). -/
noncomputable def driftRem (X b : ℝ → Ω → ℝ) (p : Partition s t) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range p.n, X (p.t i) ω * driftErr b (p.t i) (p.t (i + 1)) ω

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the diffusion remainder
`Σ ∫_{t_i}^{t_{i+1}} X_{t_i}(K − K_{t_i}) dW`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoCovariation.diffRem). -/
noncomputable def diffRem (P : Measure Ω) (𝓕 : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ℝ)
    (X K : ℝ → Ω → ℝ) (p : Partition s t) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range p.n,
    itoInt P 𝓕 W (fun r ω => X (p.t i) ω * (K r ω - K (p.t i) ω)) (p.t i) (p.t (i + 1)) ω

/-- Cochrane (2023), A1 §1.6, p. 567: the left end of a cell is at most the right end.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoCovariation.t_le_succ). -/
lemma t_le_succ (p : Partition s t) (i : ℕ) : p.t i ≤ p.t (i + 1) :=
  p.strictMono.monotone (Nat.le_succ i)

/-- Cochrane (2023), A1 §1.6, p. 567: a step of a partition is at most `t − s`.
A variant of `TidyR7StieltjesSums.le_mesh`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoCovariation.step_le). -/
lemma step_le (p : Partition s t) {i : ℕ} (hi : i < p.n) : p.t (i + 1) - p.t i ≤ t - s := by
  have h1 := t_mem p hi
  have h2 := t_mem p hi.le
  linarith [h1.2, h2.1]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the drift remainder vanishes in mean square**,
`Σ X_{t_i}D_i → 0` in `L²` along any partitions with mesh `→ 0` (Cauchy–Schwarz with weights
`Δt_i` and `TidyR7ItoProcess.eventually_integral_sq_mul_driftErr_le`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoCovariation.L2Tendsto_driftRem). -/
theorem L2Tendsto_driftRem [IsFiniteMeasure P] {X b : ℝ → Ω → ℝ} (hX : MSIntegrand P 𝓕 X s t)
    {Cb : ℝ} (hb : ItoIntegrand P 𝓕 b s t Cb) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    L2Tendsto P (fun k => driftRem X b (ps k)) 0 := by
  have hmemi : ∀ (p : Partition s t) (i : ℕ), i < p.n →
      MemLp (fun ω => X (p.t i) ω * driftErr b (p.t i) (p.t (i + 1)) ω) 2 P := by
    intro p i hi
    refine (hX.memLp _ (t_mem p hi.le)).of_le_mul (c := 2 * Cb * (p.t (i + 1) - p.t i))
      ((hX.measurable (t_mem p hi.le)).aestronglyMeasurable.mul
        (aestronglyMeasurable_driftErr hb (t_mem p hi.le).1 (t_le_succ p i) (t_mem p hi).2))
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (abs_driftErr_le hb.bound (t_mem p hi.le).1 (t_le_succ p i) (t_mem p hi).2 ω) (abs_nonneg _)
  have hmem : ∀ k, MemLp (driftRem X b (ps k)) 2 P := fun k =>
    memLp_finsetSum _ fun i hi => hmemi (ps k) i (Finset.mem_range.1 hi)
  refine ⟨hmem, MemLp.zero, ?_⟩
  simp only [Pi.zero_apply, sub_zero]
  rw [Metric.tendsto_atTop]
  intro η hη
  have hts : 0 ≤ t - s := sub_nonneg.2 (a_le_b (ps 0))
  set ε := η / (2 * ((t - s) ^ 2 + 1)) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_integral_sq_mul_driftErr_le hX.memLp hX.cont
    hb ps hps hε0)
  refine ⟨N, fun k hk => ?_⟩
  set p := ps k with hp
  have hpos : ∀ i, 0 < p.t (i + 1) - p.t i := fun i => step_pos p i
  have hpt : ∀ ω, driftRem X b p ω ^ 2 ≤ (∑ i ∈ Finset.range p.n, (p.t (i + 1) - p.t i)) *
      ∑ i ∈ Finset.range p.n,
        (X (p.t i) ω * driftErr b (p.t i) (p.t (i + 1)) ω) ^ 2 / (p.t (i + 1) - p.t i) := by
    intro ω
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ => (hpos i).le)
      (fun i _ => div_nonneg (sq_nonneg _) (hpos i).le) fun i _ => le_of_eq ?_
    field_simp [(hpos i).ne']
  have hi2 : ∀ i ∈ Finset.range p.n, Integrable (fun ω =>
      (X (p.t i) ω * driftErr b (p.t i) (p.t (i + 1)) ω) ^ 2 / (p.t (i + 1) - p.t i)) P :=
    fun i hi => (hmemi p i (Finset.mem_range.1 hi)).integrable_sq.div_const _
  have hle : ∫ ω, driftRem X b p ω ^ 2 ∂P ≤ ε * (t - s) ^ 2 := by
    calc ∫ ω, driftRem X b p ω ^ 2 ∂P
        ≤ ∫ ω, (∑ i ∈ Finset.range p.n, (p.t (i + 1) - p.t i)) * ∑ i ∈ Finset.range p.n,
          (X (p.t i) ω * driftErr b (p.t i) (p.t (i + 1)) ω) ^ 2 / (p.t (i + 1) - p.t i) ∂P :=
          integral_mono (hmem k).integrable_sq
            ((integrable_finsetSum _ hi2).const_mul _) hpt
      _ = (t - s) * ∑ i ∈ Finset.range p.n,
          (∫ ω, (X (p.t i) ω * driftErr b (p.t i) (p.t (i + 1)) ω) ^ 2 ∂P)
            / (p.t (i + 1) - p.t i) := by
          rw [integral_const_mul, integral_finsetSum _ hi2, sum_step_eq p]
          simp_rw [integral_div]
      _ ≤ (t - s) * ∑ i ∈ Finset.range p.n, ε * (p.t (i + 1) - p.t i) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) hts
          rw [div_le_iff₀ (hpos i)]
          have h := hN k hk i (Finset.mem_range.1 hi)
          have e : ∫ ω, (X (p.t i) ω * driftErr b (p.t i) (p.t (i + 1)) ω) ^ 2 ∂P
              = ∫ ω, X (p.t i) ω ^ 2 * driftErr b (p.t i) (p.t (i + 1)) ω ^ 2 ∂P :=
            integral_congr_ae (ae_of_all _ fun ω => mul_pow _ _ _)
          rw [e]
          nlinarith
      _ = ε * (t - s) ^ 2 := by
          rw [← Finset.mul_sum, sum_step_eq p]
          ring
  have h2 : ε * (t - s) ^ 2 < η := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [sq_nonneg (t - s)]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
  linarith

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the diffusion remainder vanishes in mean square**,
`Σ ∫_{t_i}^{t_{i+1}} X_{t_i}(K − K_{t_i}) dW → 0` in `L²` along any partitions with mesh `→ 0`
(the cell integrals are orthogonal martingale differences,
`TidyR7ItoProcess.integral_sum_sq_of_orth`, each of second moment `≤ εΔt_i` by the isometry and
`TidyR7ItoProducts.exists_delta_integral_sq_mul_sub_sq_le`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoCovariation.L2Tendsto_diffRem). -/
theorem L2Tendsto_diffRem (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {X K : ℝ → Ω → ℝ} (hX : MSIntegrand P 𝓕 X s t)
    {CK : ℝ} (hK : ItoIntegrand P 𝓕 K s t CK) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    L2Tendsto P (fun k => diffRem P 𝓕 W X K (ps k)) 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hG : ∀ (p : Partition s t) (i : ℕ), i < p.n → MSIntegrand P 𝓕
      (fun r ω => X (p.t i) ω * (K r ω - K (p.t i) ω)) (p.t i) (p.t (i + 1)) := fun p i hi =>
    MSIntegrand.mul_itoIntegrand (msIntegrand_const (hX.adapted _ (t_mem p hi.le))
      (hX.memLp _ (t_mem p hi.le))) (itoIntegrand_sub_left (t_le_succ p i)
        (hK.mono (t_mem p hi.le).1 (t_mem p hi).2))
  have hV2 : ∀ (p : Partition s t) (i : ℕ), i < p.n → MemLp (itoInt P 𝓕 W
      (fun r ω => X (p.t i) ω * (K r ω - K (p.t i) ω)) (p.t i) (p.t (i + 1))) 2 P :=
    fun p i hi => memLp_itoInt_ms hB hW h𝓕 (hs.trans (t_mem p hi.le).1) (hG p i hi)
  have hmem : ∀ k, MemLp (diffRem P 𝓕 W X K (ps k)) 2 P := fun k =>
    memLp_finsetSum _ fun i hi => hV2 (ps k) i (Finset.mem_range.1 hi)
  have horth : ∀ p : Partition s t, ∫ ω, diffRem P 𝓕 W X K p ω ^ 2 ∂P
      = ∑ i ∈ Finset.range p.n, ∫ ω, itoInt P 𝓕 W
        (fun r ω => X (p.t i) ω * (K r ω - K (p.t i) ω)) (p.t i) (p.t (i + 1)) ω ^ 2 ∂P :=
    fun p => integral_sum_sq_of_orth (𝓕 := 𝓕) p.strictMono.monotone p.n (hV2 p)
      (fun i _ => stronglyMeasurable_itoInt)
      (fun i hi Z hZ hZ2 => integral_mul_itoInt_ms hB hW h𝓕 (hs.trans (t_mem p hi.le).1)
        (hG p i hi) hZ hZ2)
  refine ⟨hmem, MemLp.zero, ?_⟩
  simp only [Pi.zero_apply, sub_zero]
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨δ, hδ, hδK⟩ := exists_delta_integral_sq_mul_sub_sq_le hX.memLp hX.cont
    (fun u hu => hK.measurable hu) hK.bound hK.cont (ε := η / (2 * (t - s + 1))) (by
      have := a_le_b (ps 0); positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hps.eventually (ge_mem_nhds hδ))
  refine ⟨N, fun k hk => ?_⟩
  set p := ps k with hp
  have hts : 0 ≤ t - s := sub_nonneg.2 (a_le_b p)
  have hle : ∫ ω, diffRem P 𝓕 W X K p ω ^ 2 ∂P ≤ η / (2 * (t - s + 1)) * (t - s) := by
    rw [horth p]
    refine (Finset.sum_le_sum (g := fun i => η / (2 * (t - s + 1)) * (p.t (i + 1) - p.t i))
      fun i hi => ?_).trans_eq (by rw [← Finset.mul_sum, sum_step_eq p])
    have hi' := Finset.mem_range.1 hi
    refine integral_itoInt_sq_le_ms hB hW h𝓕 (hs.trans (t_mem p hi'.le).1) (t_le_succ p i)
      (hG p i hi') fun r hr => ?_
    have hr' : r ∈ Set.Icc s t := ⟨(t_mem p hi'.le).1.trans hr.1, hr.2.trans (t_mem p hi').2⟩
    have h := hδK r hr' _ (t_mem p hi'.le) (by
      rw [abs_of_nonneg (sub_nonneg.2 hr.1)]
      exact ((sub_le_sub_right hr.2 _).trans (le_mesh p hi')).trans (hN k hk))
    refine (integral_congr_ae (ae_of_all _ fun ω => ?_)).trans_le h
    ring
  have h2 : η / (2 * (t - s + 1)) * (t - s) < η := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
  linarith

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the four-term split of `Σ X_iΔY_i`.** For every
partition, a.s.,
`Σ X_{t_i}ΔY_i = Σ X_ib_iΔt_i + Σ X_iD_i + Σ X_iK_iΔW_i
  + Σ ∫_{t_i}^{t_{i+1}} X_i(K − K_{t_i}) dW`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoCovariation.sumRS_ae_eq). -/
theorem sumRS_ae_eq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {X Y b K : ℝ → Ω → ℝ} (hX : MSIntegrand P 𝓕 X s t)
    {Cb CK : ℝ} (hY : ItoProcess P 𝓕 W Y b K s t Cb CK) (p : Partition s t) :
    sumRS p X Y =ᵐ[P] fun ω => dtSum (fun u ω => X u ω * b u ω) p ω + driftRem X b p ω
      + itoSum W (fun u ω => X u ω * K u ω) p ω + diffRem P 𝓕 W X K p ω := by
  have hall : ∀ᵐ ω ∂P, ∀ i, i < p.n → X (p.t i) ω * (Y (p.t (i + 1)) ω - Y (p.t i) ω)
      = X (p.t i) ω * b (p.t i) ω * (p.t (i + 1) - p.t i)
        + X (p.t i) ω * driftErr b (p.t i) (p.t (i + 1)) ω
        + X (p.t i) ω * K (p.t i) ω * incr W (p.t i) (p.t (i + 1)) ω
        + itoInt P 𝓕 W (fun r ω => X (p.t i) ω * (K r ω - K (p.t i) ω)) (p.t i)
          (p.t (i + 1)) ω := by
    refine ae_all_iff.2 fun i => ?_
    by_cases hi : i < p.n
    · have hm := t_mem p hi.le
      have hm' := t_mem p hi
      filter_upwards [hY.incr_decomp hB hW h𝓕 hs hm.1 (t_le_succ p i) hm'.2,
        itoInt_mul_left hB hW h𝓕 (hs.trans hm.1) (hX.adapted _ hm) (hX.memLp _ hm)
          (itoIntegrand_sub_left (t_le_succ p i) (hY.diff.mono hm.1 hm'.2))] with ω h1 h2 _
      rw [h1, h2, driftErr]
      ring
    · exact ae_of_all _ fun ω h => absurd h hi
  filter_upwards [hall] with ω hω
  simp only [sumRS, rsSum, dtSum, riemannSum, driftRem, itoSum, diffRem,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i hi => (hω i (Finset.mem_range.1 hi)).trans (by ring)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (the product rule's `X dY` term):
`Σ X_{t_i}(Y_{t_{i+1}} − Y_{t_i}) → ∫_s^t X dY := ∫_s^t X_ub_u du + ∫_s^t X K dW` in `L²`**
along any partitions with mesh `→ 0`, for `Y` an Itô process (drift `b`, diffusion `K`), `X`
mean-square continuous (e.g. an Itô process), `0 ≤ s < t`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoCovariation.L2Tendsto_sumRS). -/
theorem L2Tendsto_sumRS (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) {X Y b K : ℝ → Ω → ℝ}
    (hX : MSIntegrand P 𝓕 X s t) {Cb CK : ℝ} (hY : ItoProcess P 𝓕 W Y b K s t Cb CK)
    (ps : ℕ → Partition s t) (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    L2Tendsto P (fun k => sumRS (ps k) X Y) (fun ω => dtInt P 𝓕 (fun u ω => X u ω * b u ω) s t ω
      + itoInt P 𝓕 W (fun u ω => X u ω * K u ω) s t ω) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h1 := L2Tendsto_dtSum hst (MSIntegrand.mul_itoIntegrand hX hY.drift) ps hps
  have h2 := L2Tendsto_driftRem hX hY.drift ps hps
  have h3 := L2Tendsto_itoSum_ms hB hW h𝓕 hs hst (MSIntegrand.mul_itoIntegrand hX hY.diff) ps hps
  have h4 := L2Tendsto_diffRem hB hW h𝓕 hs hX hY.diff ps hps
  refine ((((h1.add h2).add h3).add h4).congr_seq fun k => ?_).congr_ae
    (ae_of_all _ fun ω => by simp)
  filter_upwards [sumRS_ae_eq hB hW h𝓕 hs hX hY (ps k)] with ω hω
  rw [hω]
  rfl

/-! ## The bracket -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `Σ_i E[(∫_{t_i}^{t_{i+1}} a)²] ≤ C_a²·mesh·(t − s)`
for a bounded drift.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoCovariation.sum_integral_drift_sq_le). -/
theorem sum_integral_drift_sq_le [IsProbabilityMeasure P] {a : ℝ → Ω → ℝ} {Ca : ℝ}
    (ha : ∀ u ∈ Set.Icc s t, ∀ ω, |a u ω| ≤ Ca) (p : Partition s t) :
    ∑ i ∈ Finset.range p.n, ∫ ω, (∫ r in p.t i..p.t (i + 1), a r ω) ^ 2 ∂P
      ≤ Ca ^ 2 * mesh p * (t - s) := by
  refine (Finset.sum_le_sum (g := fun i => Ca ^ 2 * mesh p * (p.t (i + 1) - p.t i))
    fun i hi => ?_).trans_eq (by rw [← Finset.mul_sum, sum_step_eq p])
  have hi' := Finset.mem_range.1 hi
  have hc : ∫ _ω, (Ca ^ 2 * (p.t (i + 1) - p.t i) ^ 2 : ℝ) ∂P
      = Ca ^ 2 * (p.t (i + 1) - p.t i) ^ 2 := by simp
  calc ∫ ω, (∫ r in p.t i..p.t (i + 1), a r ω) ^ 2 ∂P
      ≤ ∫ _ω, (Ca ^ 2 * (p.t (i + 1) - p.t i) ^ 2 : ℝ) ∂P := by
        refine integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _)
          (integrable_const _) (ae_of_all _ fun ω => ?_)
        have h := abs_integral_drift_le ha (t_mem p hi'.le).1 (t_le_succ p i) (t_mem p hi').2 ω
        rw [← mul_pow]
        exact sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
    _ = Ca ^ 2 * (p.t (i + 1) - p.t i) ^ 2 := hc
    _ ≤ Ca ^ 2 * mesh p * (p.t (i + 1) - p.t i) := by
        have h0 := step_pos p i
        have hm := le_mesh p hi'
        rw [sq (p.t (i + 1) - p.t i), ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (sq_nonneg Ca)) h0.le

/-- Cochrane (2023), A1 §1.6, pp. 567–568: along partitions with mesh `→ 0`, the summed second
moments of the cell drift integrals vanish.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoCovariation.tendsto_sum_integral_drift_sq). -/
theorem tendsto_sum_integral_drift_sq [IsProbabilityMeasure P] {a : ℝ → Ω → ℝ} {Ca : ℝ}
    (ha : ∀ u ∈ Set.Icc s t, ∀ ω, |a u ω| ≤ Ca) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∑ i ∈ Finset.range (ps k).n,
      ∫ ω, (∫ r in (ps k).t i..(ps k).t (i + 1), a r ω) ^ 2 ∂P) atTop (𝓝 0) := by
  refine squeeze_zero (fun k => Finset.sum_nonneg fun i _ => integral_nonneg fun _ =>
    sq_nonneg _) (fun k => sum_integral_drift_sq_le (P := P) ha (ps k)) ?_
  have := (hps.const_mul (Ca ^ 2)).mul_const (t - s)
  simpa using this

/-- Cochrane (2023), A1 §1.6, pp. 567–568: along partitions with mesh `→ 0`,
`Σ_i E[(∫_{t_i}^{t_{i+1}} (H − H_{t_i}) dW)²] → 0` for a bounded admissible `H`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoCovariation.tendsto_sum_integral_itoInt_sub_sq). -/
theorem tendsto_sum_integral_itoInt_sub_sq (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {H : ℝ → Ω → ℝ}
    {C : ℝ} (hH : ItoIntegrand P 𝓕 H s t C) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∑ i ∈ Finset.range (ps k).n, ∫ ω, itoInt P 𝓕 W
      (fun r ω => H r ω - H ((ps k).t i) ω) ((ps k).t i) ((ps k).t (i + 1)) ω ^ 2 ∂P) atTop
      (𝓝 0) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [Metric.tendsto_atTop]
  intro η hη
  have hts0 : 0 ≤ t - s := sub_nonneg.2 (a_le_b (ps 0))
  obtain ⟨δ, hδ, hδH⟩ := exists_delta_integral_sq_sub_le (P := P) (fun _ hu => hH.measurable hu)
    hH.bound hH.cont (ε := η / (2 * (t - s + 1))) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hps.eventually (ge_mem_nhds hδ))
  refine ⟨N, fun k hk => ?_⟩
  set p := ps k with hp
  have hle : ∑ i ∈ Finset.range p.n, ∫ ω, itoInt P 𝓕 W (fun r ω => H r ω - H (p.t i) ω)
      (p.t i) (p.t (i + 1)) ω ^ 2 ∂P ≤ η / (2 * (t - s + 1)) * (t - s) := by
    refine (Finset.sum_le_sum (g := fun i => η / (2 * (t - s + 1)) * (p.t (i + 1) - p.t i))
      fun i hi => ?_).trans_eq (by rw [← Finset.mul_sum, sum_step_eq p])
    have hi' := Finset.mem_range.1 hi
    have hHi : ItoIntegrand P 𝓕 H (p.t i) (p.t (i + 1)) C :=
      hH.mono (t_mem p hi'.le).1 (t_mem p hi').2
    refine integral_itoInt_sq_le_ms hB hW h𝓕 (hs.trans (t_mem p hi'.le).1) (t_le_succ p i)
      (ItoIntegrand.toMS (itoIntegrand_sub_left (t_le_succ p i) hHi)) fun r hr => ?_
    have hr' : r ∈ Set.Icc s t := ⟨(t_mem p hi'.le).1.trans hr.1, hr.2.trans (t_mem p hi').2⟩
    exact hδH r hr' _ (t_mem p hi'.le) (by
      rw [abs_of_nonneg (sub_nonneg.2 hr.1)]
      exact ((sub_le_sub_right hr.2 _).trans (le_mesh p hi')).trans (hN k hk))
  have h2 : η / (2 * (t - s + 1)) * (t - s) < η := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Finset.sum_nonneg fun i _ => integral_nonneg
    fun _ => sq_nonneg _)]
  linarith

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `Σ_i E[(H_{t_i}ΔW_i)²] ≤ C_H²(t − s)` for a bounded
adapted `H`, `0 ≤ s`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoCovariation.sum_integral_mul_incr_sq_le). -/
theorem sum_integral_mul_incr_sq_le (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {H : ℝ → Ω → ℝ} {C : ℝ}
    (hH : ItoIntegrand P 𝓕 H s t C) (p : Partition s t) :
    ∑ i ∈ Finset.range p.n, ∫ ω, (H (p.t i) ω * incr W (p.t i) (p.t (i + 1)) ω) ^ 2 ∂P
      ≤ C ^ 2 * (t - s) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine (Finset.sum_le_sum (g := fun i => C ^ 2 * (p.t (i + 1) - p.t i))
    fun i hi => ?_).trans_eq (by rw [← Finset.mul_sum, sum_step_eq p])
  have hm := t_mem p (Finset.mem_range.1 hi).le
  have e : ∫ ω, (H (p.t i) ω * incr W (p.t i) (p.t (i + 1)) ω) ^ 2 ∂P
      = (p.t (i + 1) - p.t i) * ∫ ω, H (p.t i) ω ^ 2 ∂P := by
    rw [← integral_mul_incr_sq hB hW h𝓕 (hs.trans hm.1) (t_le_succ p i)
      (Y := fun ω => H (p.t i) ω ^ 2) ((hH.adapted _ hm).pow 2)]
    exact integral_congr_ae (ae_of_all _ fun ω => mul_pow _ _ _)
  rw [e, mul_comm (C ^ 2)]
  refine mul_le_mul_of_nonneg_left ?_ (step_pos p i).le
  refine (integral_mono (memLp_of_bound (hH.measurable hm) (hH.bound _ hm)).integrable_sq
    (integrable_const (C ^ 2)) fun ω => ?_).trans (by simp)
  have h := hH.bound _ hm ω
  exact sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `Σ_i E[(ΔY_i)²] ≤ (2C_b²(t − s) + 2C_K²)(t − s)` for
an Itô process, uniformly in the partition.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoCovariation.sum_integral_incr_sq_le). -/
theorem sum_integral_incr_sq_le (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {Y b K : ℝ → Ω → ℝ} {Cb CK : ℝ}
    (hY : ItoProcess P 𝓕 W Y b K s t Cb CK) (p : Partition s t) :
    ∑ i ∈ Finset.range p.n, ∫ ω, (Y (p.t (i + 1)) ω - Y (p.t i) ω) ^ 2 ∂P
      ≤ (2 * Cb ^ 2 * (t - s) + 2 * CK ^ 2) * (t - s) := by
  refine (Finset.sum_le_sum (g := fun i => (2 * Cb ^ 2 * (t - s) + 2 * CK ^ 2) *
    (p.t (i + 1) - p.t i)) fun i hi => ?_).trans_eq (by rw [← Finset.mul_sum, sum_step_eq p])
  have hi' := Finset.mem_range.1 hi
  have h := hY.integral_incr_sq_le hB hW h𝓕 hs (t_mem p hi'.le).1 (t_le_succ p i)
    (t_mem p hi').2
  have h0 := step_pos p i
  have h1 := step_le p hi'
  have h3 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (sq_nonneg Cb) h0.le)
  nlinarith [h3]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `|Σ f(t_i)Δt_i| ≤ C(t − s)` for `|f| ≤ C` on
`[s, t]`.
Generalises `TidyR7ItoIntegral.abs_riemannSum_sq_le`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoCovariation.abs_riemannSum_le). -/
theorem abs_riemannSum_le {f : ℝ → ℝ} {C : ℝ} (hf : ∀ u ∈ Set.Icc s t, |f u| ≤ C)
    (p : Partition s t) : |riemannSum p f| ≤ C * (t - s) := by
  rw [riemannSum, ← sum_step_eq p, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul, abs_of_pos (step_pos p i)]
  exact mul_le_mul_of_nonneg_right (hf _ (t_mem p (Finset.mem_range.1 hi).le)) (step_pos p i).le

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (the bracket `d[X, Y] = HK dt`):
`Σ (X_{t_{i+1}} − X_{t_i})(Y_{t_{i+1}} − Y_{t_i}) → ∫_s^t H_uK_u du` in `L¹`** along any
partitions with mesh `→ 0`, for Itô processes `X` (drift `a`, diffusion `H`) and `Y` (drift `b`,
diffusion `K`), `0 ≤ s < t`.
Generalises `TidyR7BrownianQV.tendsto_integral_wqvSum_sq` (the case `X = Y = W`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoCovariation.tendsto_integral_abs_sumCross). -/
theorem tendsto_integral_abs_sumCross (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) {X Y a b H K : ℝ → Ω → ℝ}
    {Ca CH Cb CK : ℝ} (hX : ItoProcess P 𝓕 W X a H s t Ca CH)
    (hY : ItoProcess P 𝓕 W Y b K s t Cb CK) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, |sumCross (ps k) X Y ω - ∫ u in s..t, H u ω * K u ω| ∂P) atTop
      (𝓝 0) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  -- abbreviations for the pieces of cell `i` of partition `p`
  set HK : ℝ → Ω → ℝ := fun u ω => H u ω * K u ω with hHK
  have hHKa : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (HK u) := fun u hu =>
    (hX.diff.adapted u hu).mul (hY.diff.adapted u hu)
  have hHKb : ∀ u ∈ Set.Icc s t, ∀ ω, |HK u ω| ≤ CH * CK := fun u hu ω => by
    simp only [hHK, abs_mul]
    exact mul_le_mul (hX.diff.bound u hu ω) (hY.diff.bound u hu ω) (abs_nonneg _)
      ((abs_nonneg _).trans (hX.diff.bound u hu ω))
  have hHKc : ∀ᵐ ω ∂P, ContinuousOn (fun u => HK u ω) (Set.Icc s t) := by
    filter_upwards [hX.diff.cont, hY.diff.cont] with ω h1 h2
    exact h1.mul h2
  -- the pieces
  set A : ℕ → ℕ → Ω → ℝ := fun k i ω => ∫ r in (ps k).t i..(ps k).t (i + 1), a r ω with hA
  set Bt : ℕ → ℕ → Ω → ℝ := fun k i ω => ∫ r in (ps k).t i..(ps k).t (i + 1), b r ω with hBt
  set R : ℕ → ℕ → Ω → ℝ := fun k i => itoInt P 𝓕 W (fun r ω => H r ω - H ((ps k).t i) ω)
    ((ps k).t i) ((ps k).t (i + 1)) with hR
  set S : ℕ → ℕ → Ω → ℝ := fun k i => itoInt P 𝓕 W (fun r ω => K r ω - K ((ps k).t i) ω)
    ((ps k).t i) ((ps k).t (i + 1)) with hS
  set β : ℕ → ℕ → Ω → ℝ := fun k i ω => H ((ps k).t i) ω * incr W ((ps k).t i) ((ps k).t (i + 1)) ω
    with hβ
  set dY : ℕ → ℕ → Ω → ℝ := fun k i ω => Y ((ps k).t (i + 1)) ω - Y ((ps k).t i) ω with hdY
  -- square integrability of the pieces
  have mA : ∀ k, ∀ i < (ps k).n, MemLp (A k i) 2 P := fun k i hi =>
    memLp_integral_drift hX.drift (t_mem _ hi.le).1 (t_le_succ _ i) (t_mem _ hi).2
  have mB : ∀ k, ∀ i < (ps k).n, MemLp (Bt k i) 2 P := fun k i hi =>
    memLp_integral_drift hY.drift (t_mem _ hi.le).1 (t_le_succ _ i) (t_mem _ hi).2
  have mR : ∀ k, ∀ i < (ps k).n, MemLp (R k i) 2 P := fun k i hi =>
    memLp_itoInt hB hW h𝓕 (hs.trans (t_mem _ hi.le).1) (itoIntegrand_sub_left (t_le_succ _ i)
      (hX.diff.mono (t_mem _ hi.le).1 (t_mem _ hi).2))
  have mS : ∀ k, ∀ i < (ps k).n, MemLp (S k i) 2 P := fun k i hi =>
    memLp_itoInt hB hW h𝓕 (hs.trans (t_mem _ hi.le).1) (itoIntegrand_sub_left (t_le_succ _ i)
      (hY.diff.mono (t_mem _ hi.le).1 (t_mem _ hi).2))
  have mβ : ∀ k, ∀ i < (ps k).n, MemLp (β k i) 2 P := fun k i hi =>
    memLp_mul_incr_of_memLp hB hW h𝓕 (t_le_succ _ i) (hX.diff.adapted _ (t_mem _ hi.le))
      (memLp_of_bound (hX.diff.measurable (t_mem _ hi.le)) (hX.diff.bound _ (t_mem _ hi.le)))
  have mdY : ∀ k, ∀ i < (ps k).n, MemLp (dY k i) 2 P := fun k i hi =>
    (hY.memLp hB hW h𝓕 hs (t_mem _ hi)).sub (hY.memLp hB hW h𝓕 hs (t_mem _ hi.le))
  have mBS : ∀ k, ∀ i < (ps k).n, MemLp (fun ω => Bt k i ω + S k i ω) 2 P := fun k i hi =>
    (mB k i hi).add (mS k i hi)
  -- the pathwise split
  have hsplit : ∀ k, (fun ω => sumCross (ps k) X Y ω - ∫ u in s..t, HK u ω) =ᵐ[P] fun ω =>
      wqvSum W HK (ps k) ω + (riemannSum (ps k) (fun u => HK u ω) - ∫ u in s..t, HK u ω)
        + ∑ i ∈ Finset.range (ps k).n, A k i ω * dY k i ω
        + ∑ i ∈ Finset.range (ps k).n, (Bt k i ω + S k i ω) * β k i ω
        + ∑ i ∈ Finset.range (ps k).n, R k i ω * dY k i ω := by
    intro k
    have hall : ∀ᵐ ω ∂P, ∀ i, i < (ps k).n →
        (X ((ps k).t (i + 1)) ω - X ((ps k).t i) ω) * dY k i ω
          = HK ((ps k).t i) ω * incr W ((ps k).t i) ((ps k).t (i + 1)) ω ^ 2
            + A k i ω * dY k i ω + (Bt k i ω + S k i ω) * β k i ω + R k i ω * dY k i ω := by
      refine ae_all_iff.2 fun i => ?_
      by_cases hi : i < (ps k).n
      · have hm := t_mem (ps k) hi.le
        have hm' := t_mem (ps k) hi
        filter_upwards [hX.incr_decomp hB hW h𝓕 hs hm.1 (t_le_succ _ i) hm'.2,
          hY.incr_decomp hB hW h𝓕 hs hm.1 (t_le_succ _ i) hm'.2] with ω h1 h2 _
        simp only [hdY, hA, hBt, hR, hS, hβ, hHK]
        rw [h1, h2]
        ring
      · exact ae_of_all _ fun ω h => absurd h hi
    filter_upwards [hall] with ω hω
    rw [wqvSum_eq]
    simp only [sumCross, crossSum, riemannSum]
    have e : ∑ i ∈ Finset.range (ps k).n, (X ((ps k).t (i + 1)) ω - X ((ps k).t i) ω) *
        (Y ((ps k).t (i + 1)) ω - Y ((ps k).t i) ω)
        = ∑ i ∈ Finset.range (ps k).n, (HK ((ps k).t i) ω *
          incr W ((ps k).t i) ((ps k).t (i + 1)) ω ^ 2
          + A k i ω * dY k i ω + (Bt k i ω + S k i ω) * β k i ω + R k i ω * dY k i ω) :=
      Finset.sum_congr rfl fun i hi => hω i (Finset.mem_range.1 hi)
    rw [e, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    ring
  -- the five limits
  have hw : Tendsto (fun k => ∫ ω, |wqvSum W HK (ps k) ω| ∂P) atTop (𝓝 0) := by
    have hm : ∀ k, MemLp (wqvSum W HK (ps k)) 2 P := fun k =>
      memLp_finsetSum _ fun i hi => (memLp_qvTerm hB hW _ _).of_le_mul (c := CH * CK)
        ((((hHKa _ (t_mem _ (Finset.mem_range.1 hi).le)).mono (𝓕.le _)).measurable).mul
          (measurable_qvTerm hW _ _)).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (hHKb _ (t_mem _ (Finset.mem_range.1 hi).le) ω)
            (abs_nonneg _))
    refine tendsto_zero_of_sq_le (c := 1) (fun k => ?_)
      (tendsto_integral_wqvSum_sq hB hW h𝓕 hs hHKa hHKb ps hps)
    rw [one_mul]
    exact sq_integral_abs_le (hm k)
  have hr : Tendsto (fun k => ∫ ω, |riemannSum (ps k) (fun u => HK u ω)
      - ∫ u in s..t, HK u ω| ∂P) atTop (𝓝 0) := by
    have hRm : ∀ k, Measurable fun ω => riemannSum (ps k) (fun u => HK u ω) := fun k => by
      simp only [riemannSum]
      exact Finset.measurable_sum _ fun i hi => ((((hHKa _
        (t_mem _ (Finset.mem_range.1 hi).le)).mono (𝓕.le _)).measurable)).mul_const _
    have hlim : ∀ᵐ ω ∂P, Tendsto (fun k => riemannSum (ps k) (fun u => HK u ω)) atTop
        (𝓝 (∫ u in s..t, HK u ω)) := by
      filter_upwards [hHKc] with ω hω
      exact tendsto_riemannSum hω ps hps
    have hIm : AEStronglyMeasurable (fun ω => ∫ u in s..t, HK u ω) P :=
      aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hRm k).aestronglyMeasurable) hlim
    have h := tendsto_integral_of_dominated_convergence
      (F := fun k ω => |riemannSum (ps k) (fun u => HK u ω) - ∫ u in s..t, HK u ω|)
      (f := fun _ => (0 : ℝ)) (fun _ => 2 * (CH * CK) * (t - s))
      (fun k => (((hRm k).aestronglyMeasurable).sub hIm).norm) (integrable_const _)
      (fun k => ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_abs]
        have h1 := abs_riemannSum_le (fun u hu => hHKb u hu ω) (ps k)
        have h2 := abs_integral_drift_le hHKb le_rfl hst.le le_rfl ω
        calc |riemannSum (ps k) (fun u => HK u ω) - ∫ u in s..t, HK u ω|
            ≤ |riemannSum (ps k) (fun u => HK u ω)| + |∫ u in s..t, HK u ω| := abs_sub _ _
          _ ≤ 2 * (CH * CK) * (t - s) := by linarith)
      (by
        filter_upwards [hlim] with ω hω
        have := (hω.sub_const (∫ u in s..t, HK u ω)).abs
        simpa using this)
    simpa using h
  have hp1 := tendsto_integral_abs_sum_mul (P := P) (n := fun k => (ps k).n) mA mdY
    (tendsto_sum_integral_drift_sq hX.drift.bound ps hps)
    (fun k => sum_integral_incr_sq_le hB hW h𝓕 hs hY (ps k))
  have hBS0 : Tendsto (fun k => ∑ i ∈ Finset.range (ps k).n,
      ∫ ω, (Bt k i ω + S k i ω) ^ 2 ∂P) atTop (𝓝 0) := by
    have hl := ((tendsto_sum_integral_drift_sq (P := P) hY.drift.bound ps hps).const_mul 2).add
      ((tendsto_sum_integral_itoInt_sub_sq hB hW h𝓕 hs hY.diff ps hps).const_mul 2)
    rw [mul_zero, add_zero] at hl
    refine squeeze_zero (fun k => Finset.sum_nonneg fun i _ => integral_nonneg fun _ =>
      sq_nonneg _) (fun k => ?_) hl
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add
      ((mB k i hi').integrable_sq.const_mul _) ((mS k i hi').integrable_sq.const_mul _)]
    exact integral_mono ((mBS k i hi').integrable_sq) (((mB k i hi').integrable_sq.const_mul
      _).add ((mS k i hi').integrable_sq.const_mul _)) fun ω => add_sq_le_two _ _
  have hp2 := tendsto_integral_abs_sum_mul (P := P) (n := fun k => (ps k).n)
    (f := fun k i ω => Bt k i ω + S k i ω) mBS mβ hBS0
    (fun k => sum_integral_mul_incr_sq_le hB hW h𝓕 hs hX.diff (ps k))
  have hp3 := tendsto_integral_abs_sum_mul (P := P) (n := fun k => (ps k).n) mR mdY
    (tendsto_sum_integral_itoInt_sub_sq hB hW h𝓕 hs hX.diff ps hps)
    (fun k => sum_integral_incr_sq_le hB hW h𝓕 hs hY (ps k))
  -- integrability of the pieces, and the triangle inequality
  have iw : ∀ k, Integrable (fun ω => |wqvSum W HK (ps k) ω|) P := fun k =>
    (integrable_finsetSum _ fun i hi => ((memLp_qvTerm hB hW _ _).integrable
      one_le_two).bdd_mul (c := CH * CK) (((hHKa _ (t_mem _ (Finset.mem_range.1 hi).le)).mono
        (𝓕.le _)).measurable.aestronglyMeasurable) (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs]; exact hHKb _ (t_mem _ (Finset.mem_range.1 hi).le) ω)).abs
  have ir : ∀ k, Integrable (fun ω => |riemannSum (ps k) (fun u => HK u ω)
      - ∫ u in s..t, HK u ω|) P := by
    intro k
    have hRm : Measurable fun ω => riemannSum (ps k) (fun u => HK u ω) := by
      simp only [riemannSum]
      exact Finset.measurable_sum _ fun i hi => ((((hHKa _
        (t_mem _ (Finset.mem_range.1 hi).le)).mono (𝓕.le _)).measurable)).mul_const _
    have hIm : AEStronglyMeasurable (fun ω => ∫ u in s..t, HK u ω) P :=
      aestronglyMeasurable_of_tendsto_ae atTop (f := fun k ω =>
        riemannSum (dyadic hst k) (fun u => HK u ω)) (fun k => by
          have : Measurable fun ω => riemannSum (dyadic hst k) (fun u => HK u ω) := by
            simp only [riemannSum]
            exact Finset.measurable_sum _ fun i hi => ((((hHKa _
              (t_mem _ (Finset.mem_range.1 hi).le)).mono (𝓕.le _)).measurable)).mul_const _
          exact this.aestronglyMeasurable)
        (by
          filter_upwards [hHKc] with ω hω
          exact tendsto_riemannSum hω _ (tendsto_mesh_dyadic hst))
    refine Integrable.of_bound ((hRm.aestronglyMeasurable.sub hIm).norm)
      (2 * (CH * CK) * (t - s)) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    have h1 := abs_riemannSum_le (fun u hu => hHKb u hu ω) (ps k)
    have h2 := abs_integral_drift_le hHKb le_rfl hst.le le_rfl ω
    calc |riemannSum (ps k) (fun u => HK u ω) - ∫ u in s..t, HK u ω|
        ≤ |riemannSum (ps k) (fun u => HK u ω)| + |∫ u in s..t, HK u ω| := abs_sub _ _
      _ ≤ 2 * (CH * CK) * (t - s) := by linarith
  have isum : ∀ (k : ℕ) (f g : ℕ → Ω → ℝ), (∀ i < (ps k).n, MemLp (f i) 2 P) →
      (∀ i < (ps k).n, MemLp (g i) 2 P) →
      Integrable (fun ω => |∑ i ∈ Finset.range (ps k).n, f i ω * g i ω|) P :=
    fun k f g hf hg => (integrable_finsetSum _ fun i hi =>
      (hf i (Finset.mem_range.1 hi)).integrable_mul (hg i (Finset.mem_range.1 hi))).abs
  have hbound : ∀ k, ∫ ω, |sumCross (ps k) X Y ω - ∫ u in s..t, H u ω * K u ω| ∂P
      ≤ ∫ ω, |wqvSum W HK (ps k) ω| ∂P
        + ∫ ω, |riemannSum (ps k) (fun u => HK u ω) - ∫ u in s..t, HK u ω| ∂P
        + ∫ ω, |∑ i ∈ Finset.range (ps k).n, A k i ω * dY k i ω| ∂P
        + ∫ ω, |∑ i ∈ Finset.range (ps k).n, (Bt k i ω + S k i ω) * β k i ω| ∂P
        + ∫ ω, |∑ i ∈ Finset.range (ps k).n, R k i ω * dY k i ω| ∂P := by
    intro k
    have i1 := isum k (A k) (dY k) (mA k) (mdY k)
    have i2 := isum k (fun i ω => Bt k i ω + S k i ω) (β k) (mBS k) (mβ k)
    have i3 := isum k (R k) (dY k) (mR k) (mdY k)
    have j2 : Integrable (fun ω => |wqvSum W HK (ps k) ω|
        + |riemannSum (ps k) (fun u => HK u ω) - ∫ u in s..t, HK u ω|) P := (iw k).add (ir k)
    have j3 : Integrable (fun ω => |wqvSum W HK (ps k) ω|
        + |riemannSum (ps k) (fun u => HK u ω) - ∫ u in s..t, HK u ω|
        + |∑ i ∈ Finset.range (ps k).n, A k i ω * dY k i ω|) P := j2.add i1
    have j4 : Integrable (fun ω => |wqvSum W HK (ps k) ω|
        + |riemannSum (ps k) (fun u => HK u ω) - ∫ u in s..t, HK u ω|
        + |∑ i ∈ Finset.range (ps k).n, A k i ω * dY k i ω|
        + |∑ i ∈ Finset.range (ps k).n, (Bt k i ω + S k i ω) * β k i ω|) P := j3.add i2
    have j5 : Integrable (fun ω => |wqvSum W HK (ps k) ω|
        + |riemannSum (ps k) (fun u => HK u ω) - ∫ u in s..t, HK u ω|
        + |∑ i ∈ Finset.range (ps k).n, A k i ω * dY k i ω|
        + |∑ i ∈ Finset.range (ps k).n, (Bt k i ω + S k i ω) * β k i ω|
        + |∑ i ∈ Finset.range (ps k).n, R k i ω * dY k i ω|) P := j4.add i3
    rw [← integral_add (iw k) (ir k), ← integral_add j2 i1, ← integral_add j3 i2,
      ← integral_add j4 i3]
    rw [integral_congr_ae (g := fun ω => |wqvSum W HK (ps k) ω + (riemannSum (ps k)
        (fun u => HK u ω) - ∫ u in s..t, HK u ω)
        + ∑ i ∈ Finset.range (ps k).n, A k i ω * dY k i ω
        + ∑ i ∈ Finset.range (ps k).n, (Bt k i ω + S k i ω) * β k i ω
        + ∑ i ∈ Finset.range (ps k).n, R k i ω * dY k i ω|)
      (by filter_upwards [hsplit k] with ω hω; simp only [hHK] at hω; rw [hω])]
    refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) j5
      (ae_of_all _ fun ω => ?_)
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
  have hlim := (((hw.add hr).add hp1).add hp2).add hp3
  simp only [add_zero] at hlim
  exact squeeze_zero (fun k => integral_nonneg fun _ => abs_nonneg _) hbound hlim

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: no bracket against a bounded-variation process.**
If the diffusion coefficient of `X` vanishes (`X_u = X_s + ∫_s^u a dr`, continuous and of bounded
variation), then `Σ ΔX_iΔY_i → 0` in `L¹` for every Itô process `Y`.
The `L¹` Itô-process analogue of `TidyR7ItoBridge.ae_tendsto_crossSum_integrand_bm` and
TidyR7BrownianVariation.ae_tendsto_sumCross_bm_bv (Cochrane Monetarism project).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoCovariation.tendsto_integral_abs_sumCross_bv). -/
theorem tendsto_integral_abs_sumCross_bv (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    {X Y a b H K : ℝ → Ω → ℝ} {Ca CH Cb CK : ℝ} (hX : ItoProcess P 𝓕 W X a H s t Ca CH)
    (hY : ItoProcess P 𝓕 W Y b K s t Cb CK) (hH0 : ∀ u ω, H u ω = 0) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, |sumCross (ps k) X Y ω| ∂P) atTop (𝓝 0) := by
  have h := tendsto_integral_abs_sumCross hB hW h𝓕 hs hst hX hY ps hps
  simpa [hH0] using h

end Cochrane.LongTermDebtDynamics.TidyR7ItoCovariation
