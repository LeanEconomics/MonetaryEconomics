/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR10DoobVersion
import ZeroBound.TidyR10DoobFubini
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Continuous versions of `∫ G dW` for mean-square continuous integrands

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for (1.32) with diffusive
bonds (Track 3, chunk B3, item 2 for `TidyR7ItoUnbounded.MSIntegrand`). I5c's continuous
modification (`TidyR7ItoContinuity.exists_continuous_modification`) needs a bounded integrand
(its Kolmogorov step bounds the cell coefficients). With Doob's inequality the bound is not
needed: the stopped left-point sums `TidyR7ItoContinuity.truncSum` of a mean-square continuous
integrand are adapted, square integrable and have orthogonal increments
(`integral_mul_truncSum_sub_ms`), so `TidyR10DoobContinuous.doob_sq_pathSup` bounds
`E[sup_{[s,T]}|J_{n_{j+1}} − J_{n_j}|²] ≤ 4·8^{−j}` along a fast subsequence; Markov and
Borel–Cantelli give uniform convergence a.s.

## Main results

* `exists_continuous_modification_ms`: a modification of `t ↦ ∫_s^t G dW` with a.s. continuous
  paths on `[s, T]`, for `G` mean-square continuous.
* `exists_adapted_continuous_itoInt_ms` (**item 2 for mean-square integrands**): one process,
  adapted to `𝓕`, `X_t = ∫_s^t G dW` a.s. for every `t`, `0` on `(−∞, s]`, a.s. continuous on
  `ℝ`, a martingale, with `E[sup_{[s,T]} X²] ≤ 4∫_s^T E[G_u²] du` for every `T > s`.
* `exists_adapted_continuous_itoInt_bm_bmPath`: non-vacuity for the unbounded integrand `W`
  (`∫_0^t W dW`) on the constructed motion.
-/

namespace Cochrane.ZeroBound.TidyR10DoobMSVersion

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.TidyR7StieltjesSums Cochrane.ZeroBound.TidyR7BrownianTools
  Cochrane.ZeroBound.TidyR7BrownianExist Cochrane.ZeroBound.TidyR7BrownianSchauder
  Cochrane.ZeroBound.TidyR7BrownianQV Cochrane.ZeroBound.TidyR7ItoL2
  Cochrane.ZeroBound.TidyR7ItoSums Cochrane.ZeroBound.TidyR7ItoIntegral
  Cochrane.ZeroBound.TidyR7ItoContinuity Cochrane.ZeroBound.TidyR7ItoUnbounded
  Cochrane.ZeroBound.TidyR7ItoProcess Cochrane.ZeroBound.TidyR7ItoProductRule
  Cochrane.ZeroBound.TidyR7CondDominated Cochrane.ZeroBound.TidyR10DoobContinuous
  Cochrane.ZeroBound.TidyR10DoobIto Cochrane.ZeroBound.TidyR10DoobVersion
  Cochrane.ZeroBound.TidyR10DoobFubini
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ} {G : ℝ → Ω → ℝ} {s T : ℝ}

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the stopped left-point sum of an adapted integrand
is `𝓕_τ`-strongly measurable.
An instance of `TidyR7ItoContinuity.stronglyMeasurable_cellSum_trunc`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobMSVersion.stronglyMeasurable_truncSum). -/
theorem stronglyMeasurable_truncSum (h𝓕 : BMFiltration P W 𝓕)
    (hGa : ∀ u ∈ Set.Icc s T, StronglyMeasurable[𝓕 u] (G u)) (p : Partition s T) (τ : ℝ) :
    StronglyMeasurable[𝓕 τ] (truncSum W G p τ) :=
  stronglyMeasurable_cellSum_trunc h𝓕 (S := Finset.range p.n) (a := p.t)
    (b := fun i => p.t (i + 1)) (ξ := fun i => G (p.t i))
    (fun i _ => (p.strictMono (Nat.lt_succ_self i)).le)
    (fun _ hi => hGa _ (t_mem p (Finset.mem_range.1 hi).le)) τ

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the stopped left-point sum of a mean-square
continuous integrand is square integrable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobMSVersion.memLp_truncSum_ms). -/
theorem memLp_truncSum_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hG : MSIntegrand P 𝓕 G s T) (p : Partition s T) (τ : ℝ) :
    MemLp (truncSum W G p τ) 2 P := by
  refine memLp_finsetSum _ fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  have hmem := t_mem p hi'.le
  have hlt := p.strictMono (Nat.lt_succ_self i)
  by_cases h : p.t i ≤ τ
  · rw [min_eq_left h]
    exact memLp_mul_incr_of_memLp hB hW h𝓕 (le_min hlt.le h) (hG.adapted _ hmem) (hG.memLp _ hmem)
  · have h' : τ ≤ p.t i := (not_le.1 h).le
    have e : (fun ω => G (p.t i) ω * incr W (min (p.t i) τ) (min (p.t (i + 1)) τ) ω) = 0 := by
      funext ω
      rw [min_eq_right h', min_eq_right (h'.trans hlt.le), incr_self, mul_zero]
      rfl
    rw [e]
    exact MemLp.zero

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the stopped left-point sums have orthogonal
increments** for a mean-square continuous integrand: for `u ≤ v` and square-integrable
`𝓕_u`-strongly measurable `Z`, `E[Z(J_v − J_u)] = 0`,
`J_τ = Σ G_{t_i}(W_{t_{i+1}∧τ} − W_{t_i∧τ})`.
Generalises `TidyR7ItoContinuity.integral_mul_cellSum_trunc_sub` to mean-square continuous
coefficients.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobMSVersion.integral_mul_truncSum_sub_ms). -/
theorem integral_mul_truncSum_sub_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hG : MSIntegrand P 𝓕 G s T) (p : Partition s T) {u v : ℝ}
    (huv : u ≤ v) {Z : Ω → ℝ} (hZ : StronglyMeasurable[𝓕 u] Z) (hZ2 : MemLp Z 2 P) :
    ∫ ω, Z ω * (truncSum W G p v ω - truncSum W G p u ω) ∂P = 0 := by
  set a : ℕ → ℝ := fun i => max (p.t i) u
  set b : ℕ → ℝ := fun i => max (max (p.t i) u) (min (p.t (i + 1)) v)
  have e : ∀ ω, Z ω * (truncSum W G p v ω - truncSum W G p u ω)
      = ∑ i ∈ Finset.range p.n, Z ω * (G (p.t i) ω * incr W (a i) (b i) ω) := by
    intro ω
    rw [truncSum, truncSum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h4 := four_point (fun x => bmReal W x ω) (p.strictMono (Nat.lt_succ_self i)).le huv
    simp only [incr, a, b]
    rw [← h4]
    ring
  have hterm : ∀ i ∈ Finset.range p.n,
      Integrable (fun ω => Z ω * (G (p.t i) ω * incr W (a i) (b i) ω)) P := by
    intro i hi
    have hmem := t_mem p (Finset.mem_range.1 hi).le
    exact hZ2.integrable_mul (memLp_mul_incr_of_memLp hB hW h𝓕 (le_max_left _ _)
      ((hG.adapted _ hmem).mono (𝓕.mono (le_max_left _ _))) (hG.memLp _ hmem))
  simp_rw [e]
  rw [integral_finsetSum _ hterm]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hmem := t_mem p (Finset.mem_range.1 hi).le
  have hY : StronglyMeasurable[𝓕 (a i)] (fun ω => Z ω * G (p.t i) ω) :=
    (hZ.mono (𝓕.mono (le_max_right _ _))).mul ((hG.adapted _ hmem).mono (𝓕.mono (le_max_left _ _)))
  rw [← integral_mul_incr hB hW h𝓕 (le_max_left _ _) hY]
  exact integral_congr_ae (ae_of_all _ fun ω => by ring)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Track 3, item 2): a continuous modification of
`∫ G dW` for a mean-square continuous integrand.** If `W` has a.s. continuous paths and `G` is
mean-square continuous on `[s, T]`, `0 ≤ s < T`, there is `X` with `X_t = ∫_s^t G dW` a.s. for
every `t ∈ [s, T]` and a.s. continuous paths on `[s, T]`.
Generalises `TidyR7ItoContinuity.exists_continuous_modification`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobMSVersion.exists_continuous_modification_ms). -/
theorem exists_continuous_modification_ms (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω) (hs : 0 ≤ s) (hsT : s < T)
    (hG : MSIntegrand P 𝓕 G s T) :
    ∃ X : ℝ → Ω → ℝ, (∀ t ∈ Set.Icc s T, X t =ᵐ[P] itoInt P 𝓕 W G s t) ∧
      ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Icc s T) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set d : ℕ → Partition s T := fun n => dyadic hsT n with hd
  choose N hN using fun j : ℕ => cauchy_itoSum_ms hB hW h𝓕 hs hsT hG d (tendsto_mesh_dyadic hsT)
    (ε := (1 / 8) ^ j) (by positivity)
  set n : ℕ → ℕ := fun j => ∑ i ∈ Finset.range (j + 1), N i + j with hn
  have hnN : ∀ j, N j ≤ n j := fun j =>
    (Finset.single_le_sum (fun i _ => Nat.zero_le (N i)) (Finset.self_mem_range_succ j)).trans
      (Nat.le_add_right _ _)
  have hnmono : StrictMono n := strictMono_nat_of_lt_succ fun j => by
    simp only [hn, Finset.sum_range_succ (n := j + 1)]
    omega
  set D : ℕ → ℝ → Ω → ℝ := fun j τ ω =>
    truncSum W G (d (n (j + 1))) τ ω - truncSum W G (d (n j)) τ ω with hD
  have hDm : ∀ j τ, StronglyMeasurable[𝓕 τ] (D j τ) := fun j τ =>
    (stronglyMeasurable_truncSum h𝓕 hG.adapted _ τ).sub
      (stronglyMeasurable_truncSum h𝓕 hG.adapted _ τ)
  have hD2 : ∀ j τ, MemLp (D j τ) 2 P := fun j τ =>
    (memLp_truncSum_ms hB hW h𝓕 hG _ τ).sub (memLp_truncSum_ms hB hW h𝓕 hG _ τ)
  have hDorth : ∀ j, ∀ u ∈ Set.Icc s T, ∀ Z : Ω → ℝ, StronglyMeasurable[𝓕 u] Z → MemLp Z 2 P →
      ∫ ω, Z ω * (D j T ω - D j u ω) ∂P = 0 := by
    intro j u hu Z hZ hZ2
    have h1 := integral_mul_truncSum_sub_ms hB hW h𝓕 hG (d (n (j + 1))) hu.2 hZ hZ2
    have h2 := integral_mul_truncSum_sub_ms hB hW h𝓕 hG (d (n j)) hu.2 hZ hZ2
    have i1 : Integrable (fun ω => Z ω * (truncSum W G (d (n (j + 1))) T ω
        - truncSum W G (d (n (j + 1))) u ω)) P :=
      hZ2.integrable_mul ((memLp_truncSum_ms hB hW h𝓕 hG _ T).sub
        (memLp_truncSum_ms hB hW h𝓕 hG _ u))
    have i2 : Integrable (fun ω => Z ω * (truncSum W G (d (n j)) T ω
        - truncSum W G (d (n j)) u ω)) P :=
      hZ2.integrable_mul ((memLp_truncSum_ms hB hW h𝓕 hG _ T).sub
        (memLp_truncSum_ms hB hW h𝓕 hG _ u))
    have e : ∫ ω, Z ω * (D j T ω - D j u ω) ∂P = ∫ ω, Z ω * (truncSum W G (d (n (j + 1))) T ω
        - truncSum W G (d (n (j + 1))) u ω) ∂P - ∫ ω, Z ω * (truncSum W G (d (n j)) T ω
        - truncSum W G (d (n j)) u ω) ∂P := by
      rw [← integral_sub i1 i2]
      exact integral_congr_ae (ae_of_all _ fun ω => by simp only [hD]; ring)
    rw [e, h1, h2, sub_zero]
  have hDc : ∀ᵐ ω ∂P, ∀ j, Continuous fun τ => D j τ ω := by
    filter_upwards [hcont] with ω hω j
    exact (continuous_truncSum G _ hω).sub (continuous_truncSum G _ hω)
  have hdoob : ∀ j, Integrable (fun ω => pathSup s T (D j) ω ^ 2) P ∧
      ∫ ω, pathSup s T (D j) ω ^ 2 ∂P ≤ 4 * ∫ ω, D j T ω ^ 2 ∂P := fun j =>
    doob_sq_pathSup hsT (fun u _ => hDm j u) (fun u _ => hD2 j u) (hDorth j)
      (fun _ _ => ae_of_all _ fun _ => rfl)
      (hDc.mono fun ω hω x _ => (hω j).continuousWithinAt)
  have hET : ∀ j, ∫ ω, D j T ω ^ 2 ∂P ≤ (1 / 8) ^ j := by
    intro j
    have e : ∀ ω, D j T ω = itoSum W G (d (n (j + 1))) ω - itoSum W G (d (n j)) ω := fun ω => by
      simp only [hD]
      rw [truncSum_of_le _ _ le_rfl, truncSum_of_le _ _ le_rfl]
    simp_rw [e]
    exact hN j _ ((hnN j).trans (hnmono.monotone (Nat.le_succ j))) _ (hnN j)
  -- the bad events, Markov and Borel–Cantelli
  set E : ℕ → Set Ω := fun j => {ω | (1 / 2) ^ j ≤ pathSup s T (D j) ω} with hE
  have hEbd : ∀ j, P (E j) ≤ ENNReal.ofReal (4 * (1 / 2) ^ j) := by
    intro j
    have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => sq_nonneg _)
      (hdoob j).1 ((1 / 4) ^ j)
    have hsub : E j ⊆ {ω | (1 / 4 : ℝ) ^ j ≤ pathSup s T (D j) ω ^ 2} := by
      intro ω hω
      have h : (1 / 2 : ℝ) ^ j ≤ pathSup s T (D j) ω := hω
      change (1 / 4 : ℝ) ^ j ≤ pathSup s T (D j) ω ^ 2
      have e : (1 / 4 : ℝ) ^ j = ((1 / 2) ^ j) ^ 2 := by
        rw [← pow_mul, mul_comm j 2, pow_mul]
        norm_num
      rw [e]
      exact pow_le_pow_left₀ (by positivity) h 2
    have h2 : (1 / 4 : ℝ) ^ j * P.real (E j) ≤ (1 / 4) ^ j * (4 * (1 / 2) ^ j) := by
      calc (1 / 4 : ℝ) ^ j * P.real (E j)
          ≤ (1 / 4) ^ j * P.real {ω | (1 / 4 : ℝ) ^ j ≤ pathSup s T (D j) ω ^ 2} :=
            mul_le_mul_of_nonneg_left (measureReal_mono hsub (measure_ne_top _ _))
              (by positivity)
        _ ≤ ∫ ω, pathSup s T (D j) ω ^ 2 ∂P := hm
        _ ≤ 4 * (1 / 8) ^ j := (hdoob j).2.trans (by linarith [hET j])
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
  set X : ℝ → Ω → ℝ := fun t ω => limUnder atTop (fun j => truncSum W G (d (n j)) t ω) with hX
  have hgood : ∀ᵐ ω ∂P, TendstoUniformlyOn (fun j t => truncSum W G (d (n j)) t ω)
      (fun t => X t ω) atTop (Set.Icc s T) := by
    filter_upwards [hae, hDc] with ω hω hωc
    obtain ⟨J, hJ⟩ := eventually_atTop.1 hω
    have hdiff : ∀ j ≥ J, ∀ t ∈ Set.Icc s T, |D j t ω| ≤ (1 / 2) ^ j := by
      intro j hj t ht
      have h1 := abs_le_pathSup_of_continuousOn (hωc j).continuousOn ht (X := D j)
      have h2 : ¬ ((1 / 2 : ℝ) ^ j ≤ pathSup s T (D j) ω) := hJ j hj
      push Not at h2
      linarith
    set u : ℕ → ℝ → ℝ := fun m t => truncSum W G (d (n (J + m))) t ω with hu_def
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
      have hfull : Tendsto (fun j => truncSum W G (d (n j)) t ω) atTop (𝓝 a0) := by
        refine (tendsto_add_atTop_iff_nat J).1 (ha0.congr fun m => ?_)
        simp only [hu_def]
        rw [add_comm]
      change Tendsto (fun m => u m t) atTop
        (𝓝 (limUnder atTop (fun j => truncSum W G (d (n j)) t ω)))
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
    filter_upwards [hgood, hcont] with ω h1 h2
    exact h1.continuousOn (Frequently.of_forall fun j => (continuous_truncSum G _ h2).continuousOn)
  refine ⟨X, fun t ht => ?_, hXcont⟩
  rcases ht.1.lt_or_eq with hst | hst
  · have hps : Tendsto (fun j => mesh (restrict (d (n j)) hst ht.2)) atTop (𝓝 0) :=
      squeeze_zero (fun _ => mesh_nonneg _) (fun j => mesh_restrict_le _ _ _)
        ((tendsto_mesh_dyadic hsT).comp hnmono.tendsto_atTop)
    have hL := L2Tendsto_itoSum_ms hB hW h𝓕 hs hst (hG.mono le_rfl ht.2) _ hps
    have hae2 : ∀ᵐ ω ∂P, Tendsto (fun j => itoSum W G (restrict (d (n j)) hst ht.2) ω) atTop
        (𝓝 (X t ω)) := by
      filter_upwards [hgood] with ω hω
      exact (hω.tendsto_at ht).congr fun j => (truncSum_eq_itoSum_restrict G _ hst ht.2 ω).symm
    exact (ae_eq_of_L2Tendsto_of_ae_tendsto hL hae2).symm
  · have e1 : X t = 0 := by
      funext ω
      have e2 : (fun j => truncSum W G (d (n j)) t ω) = fun _ => 0 :=
        funext fun j => truncSum_of_le_start G _ hst.ge ω
      simp only [hX, e2]
      exact tendsto_const_nhds.limUnder_eq
    rw [e1, ← hst, itoInt_of_le le_rfl]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `t ↦ ∫_s^t G dW` is a martingale** for `G` mean-square
continuous on every `[s, T]`, `0 ≤ s` (on the whole index `ℝ`, `0` before `s`).
Generalises `TidyR7ItoIntegral.martingale_itoInt`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobMSVersion.martingale_itoInt_ms). -/
theorem martingale_itoInt_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hG : ∀ T, MSIntegrand P 𝓕 G s T) :
    Martingale (fun t => itoInt P 𝓕 W G s t) 𝓕 P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨fun t => stronglyMeasurable_itoInt, fun i j hij => ?_⟩
  have hint : ∀ t, Integrable (itoInt P 𝓕 W G s t) P := fun t =>
    (memLp_itoInt_ms hB hW h𝓕 hs (hG t)).integrable one_le_two
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le i) (hint j)
    (fun _ _ _ => (hint i).integrableOn) ?_ stronglyMeasurable_itoInt.aestronglyMeasurable).symm
  intro A hA _
  have hA' : MeasurableSet A := 𝓕.le i A hA
  have hZ2 : MemLp (A.indicator fun _ => (1 : ℝ)) 2 P :=
    memLp_of_bound (measurable_const.indicator hA') (C := 1)
      (fun ω => by by_cases h : ω ∈ A <;> simp [h])
  -- the increment from `max i s` to `j` is orthogonal to `1_A`
  rcases le_total j s with hjs | hsj
  · rw [itoInt_of_le hjs, itoInt_of_le (hij.trans hjs)]
  set r := max i s with hr
  have hrj : r ≤ j := max_le hij hsj
  have hAr : MeasurableSet[𝓕 r] A := 𝓕.mono (le_max_left i s) A hA
  have h := integral_mul_itoInt_sub_ms hB hW h𝓕 hs (hG j) ⟨le_max_right i s, hrj⟩
    (stronglyMeasurable_const.indicator hAr) hZ2
  have e : ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω * (itoInt P 𝓕 W G s j ω
      - itoInt P 𝓕 W G s r ω) ∂P = ∫ ω in A, itoInt P 𝓕 W G s j ω ∂P
        - ∫ ω in A, itoInt P 𝓕 W G s r ω ∂P := by
    rw [integral_indicator_one_mul hA', integral_sub (hint j).integrableOn (hint r).integrableOn]
  have hri : itoInt P 𝓕 W G s r = itoInt P 𝓕 W G s i := by
    rcases le_total i s with his | hsi
    · rw [hr, max_eq_right his, itoInt_of_le le_rfl, itoInt_of_le his]
    · rw [hr, max_eq_left hsi]
  rw [h, hri] at e
  linarith

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Track 3, item 2 for mean-square integrands): an
adapted continuous version of `t ↦ ∫_s^t G dW` on `[s, ∞)`.** Let `W` be pre-Brownian with
measurable values and a.s. continuous paths, `𝓕` admissible, `0 ≤ s`, and `G` mean-square
continuous on every `[s, T]` (`TidyR7ItoUnbounded.MSIntegrand`; no bound). There is `X` with:
`X_t` `𝓕_t`-strongly measurable; `X_t = ∫_s^t G dW` a.s. for every `t`; `X_t = 0` for `t ≤ s`;
almost every path continuous on `ℝ`; `X` a martingale for `𝓕`; and for every `T > s`,
`E[(sup_{[s,T]}|X|)²] ≤ 4∫_s^T E[G_u²] du`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobMSVersion.exists_adapted_continuous_itoInt_ms). -/
theorem exists_adapted_continuous_itoInt_ms (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω) (hs : 0 ≤ s)
    (hG : ∀ T, MSIntegrand P 𝓕 G s T) :
    ∃ X : ℝ → Ω → ℝ, (∀ t, StronglyMeasurable[𝓕 t] (X t)) ∧
      (∀ t, X t =ᵐ[P] itoInt P 𝓕 W G s t) ∧ (∀ t ≤ s, ∀ ω, X t ω = 0) ∧
      (∀ᵐ ω ∂P, Continuous fun t => X t ω) ∧ Martingale X 𝓕 P ∧
      ∀ T, s < T → Integrable (fun ω => pathSup s T X ω ^ 2) P ∧
        ∫ ω, pathSup s T X ω ^ 2 ∂P ≤ 4 * ∫ u in s..T, ∫ ω, G u ω ^ 2 ∂P := by
  have hYs : ∀ ω, itoInt P 𝓕 W G s s ω = 0 := fun ω => by rw [itoInt_of_le le_rfl]; rfl
  have hmod : ∀ N : ℕ, ∃ X : ℝ → Ω → ℝ,
      (∀ t ∈ Set.Icc s (s + N), X t =ᵐ[P] itoInt P 𝓕 W G s t) ∧
      ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Icc s (s + N)) := by
    intro N
    rcases (Nat.cast_nonneg N : (0 : ℝ) ≤ N).lt_or_eq with hN | hN
    · exact exists_continuous_modification_ms hB hW h𝓕 hcont hs (by linarith) (hG (s + N))
    · refine ⟨fun t => itoInt P 𝓕 W G s t, fun _ _ => ae_of_all _ fun _ => rfl,
        ae_of_all _ fun ω => ?_⟩
      rw [← hN, add_zero, Set.Icc_self]
      exact continuousOn_singleton _ _
  obtain ⟨X, hXm, hXY, hX0, hXc⟩ := exists_adapted_continuous_version
    (fun t => stronglyMeasurable_itoInt) hYs hmod
  have hXI : ∀ t, X t =ᵐ[P] itoInt P 𝓕 W G s t := by
    intro t
    rcases le_total s t with hst | hts
    · exact hXY t hst
    · exact ae_of_all _ fun ω => by rw [hX0 t hts ω, itoInt_of_le hts]; rfl
  have hmart := martingale_itoInt_ms hB hW h𝓕 hs hG
  refine ⟨X, hXm, hXI, hX0, hXc, ⟨hXm, fun i j hij => ?_⟩, fun T hsT => ?_⟩
  · exact (condExp_congr_ae (hXI j)).trans ((hmart.2 i j hij).trans (hXI i).symm)
  · exact doob_sq_itoInt_fubini_ms hB hW h𝓕 hs hsT (hG T) (fun t _ => hXI t)
      (hXc.mono fun ω hω x _ => hω.continuousWithinAt)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Track 3, item 4, non-vacuity): an adapted
continuous version of `∫_0^t W dW` (unbounded integrand)** on the constructed motion, with
`E[(sup_{[0,1]}|X|)²] ≤ 4∫_0^1 E[W_u²] du`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobMSVersion.exists_adapted_continuous_itoInt_bm_bmPath). -/
theorem exists_adapted_continuous_itoInt_bm_bmPath :
    ∃ X : ℝ → (ℕ → ℝ) → ℝ,
      (∀ t, StronglyMeasurable[bmFiltrationReal bmPath measurable_bmPath t] (X t)) ∧
      (∀ t, X t =ᵐ[gaussSeq] itoInt gaussSeq (bmFiltrationReal bmPath measurable_bmPath) bmPath
        (bmReal bmPath) 0 t) ∧
      (∀ᵐ ω ∂gaussSeq, Continuous fun t => X t ω) ∧
      ∫ ω, pathSup 0 1 X ω ^ 2 ∂gaussSeq
        ≤ 4 * ∫ u in (0 : ℝ)..1, ∫ ω, bmReal bmPath u ω ^ 2 ∂gaussSeq := by
  have h𝓕 := bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath
  obtain ⟨X, hXm, hXI, -, hXc, -, hXd⟩ := exists_adapted_continuous_itoInt_ms
    isPreBrownianReal_bmPath measurable_bmPath h𝓕 (ae_of_all _ continuous_bmPath) le_rfl
    (fun T => (itoProcess_bm isPreBrownianReal_bmPath measurable_bmPath h𝓕 le_rfl
      (t := T)).toMS isPreBrownianReal_bmPath measurable_bmPath h𝓕 le_rfl)
  exact ⟨X, hXm, hXI, hXc, (hXd 1 zero_lt_one).2⟩

end Cochrane.ZeroBound.TidyR10DoobMSVersion
