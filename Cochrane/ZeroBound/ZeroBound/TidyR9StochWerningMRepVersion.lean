/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR13MRepMonetarism
import ZeroBound.TidyR10DoobAugment
import ZeroBound.TidyR10DoobMSVersion
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# The extended Itô integral as a continuous martingale, and martingales on `[0, ∞)`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.2, pp. 474–476
("multiple forward-stable equilibrium inflation paths, indexed by the free constant `C`", p. 475,
and the fiscal innovation of p. 476), under uncertainty. Tools for TidyR9StochWerningInnovations:
the equilibria of the stochastic Werning model are indexed by martingales `M`
(`TidyR8StochWerningMartingale`), and those are, on the Brownian filtration, `M_0 + ∫_0^t H dW`
with `H` in the extended integrand class of `TidyR13MRepIntegral`. For the converse the
equilibrium needs `M` with continuous paths, so `t ↦ ∫_0^t H dW` needs a continuous version.

## Main results

* `swmrep_exists_continuous_modification`: for `H` in the extended class on `[s, T]`, a
  modification of `t ↦ ∫_s^t H dW` with almost surely continuous paths on `[s, T]` (approximate
  `H` by mean-square continuous `G_n`, take the continuous versions of
  `TidyR10DoobMSVersion.exists_continuous_modification_ms`, Doob's inequality
  `TidyR10DoobIto.doob_sq_itoInt_ms` and the isometry along a fast subsequence, Borel–Cantelli).
* `swmrep_exists_adapted_continuous`: one process on `[s, ∞)`, adapted to `𝓕`, almost surely
  continuous (via `TidyR10DoobVersion.exists_adapted_continuous_version`).
* `swmrep_exists_continuous_augment`: EVERY path continuous, adapted to the completed filtration
  `TidyR10DoobAugment.augment`, a martingale for it on `[s, ∞)`.
* `swmrep_martingale_rep`, `swmrep_martingale_rep_unique`: a martingale on `[0, ∞)` (only on
  `[0, ∞)`, adapted, `M_t ∈ L²` for every `t ≥ 0`) of a filtration inside the Brownian one is
  `M_t = E[M_0] + ∫_0^t H dW` a.s. for every `t ≥ 0` with ONE integrand `H`, in the class on every
  `[0, T]`; the constant and `H` (`dt × dP`-a.e. on every `[0, T]`) are unique. The integrands of
  `TidyR13MRepTheorem.mrep_martingale` for different horizons agree (`swmrep_horizon_consistent`)
  and are glued over the unit intervals (`swmrep_glue`).
-/

namespace Cochrane.ZeroBound.TidyR9StochWerningMRepVersion

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.TidyR7BrownianTools Cochrane.ZeroBound.TidyR7BrownianQV
  Cochrane.ZeroBound.TidyR7ItoL2 Cochrane.ZeroBound.TidyR7ItoIntegral
  Cochrane.ZeroBound.TidyR7ItoUnbounded Cochrane.ZeroBound.TidyR7CondDominated
  Cochrane.ZeroBound.TidyR10DoobIto Cochrane.ZeroBound.TidyR10DoobVersion
  Cochrane.ZeroBound.TidyR10DoobAugment Cochrane.ZeroBound.TidyR10DoobMSVersion
  Cochrane.ZeroBound.TidyR12SDETools Cochrane.ZeroBound.TidyR13MRepIntegral
  Cochrane.ZeroBound.TidyR13MRepDensity Cochrane.ZeroBound.TidyR13MRepTheorem
  Cochrane.ZeroBound.TidyR13MRepMonetarism
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ} {s T : ℝ} {H : ℝ → Ω → ℝ}

/-! ## Tools -/

/-- Cochrane (2023), §20.2.2, p. 475 (tool): `L²` convergence passes to subsequences. -/
theorem swmrep_L2Tendsto_comp {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} (h : L2Tendsto P X Y) {n : ℕ → ℕ}
    (hn : StrictMono n) : L2Tendsto P (fun j => X (n j)) Y :=
  ⟨fun j => h.1 (n j), h.2.1, h.2.2.comp hn.tendsto_atTop⟩

/-- Cochrane (2023), §20.2.2, p. 475 (tool): the extended integrand class depends only on the
`dt × dP`-class of the integrand. -/
theorem swmrep_integrand_congr_ae {H' : ℝ → Ω → ℝ} {t : ℝ} (hH : MRepIntegrand P 𝓕 H s t)
    (h : Function.uncurry H =ᵐ[mrepMeasure P s t] Function.uncurry H') :
    MRepIntegrand P 𝓕 H' s t := by
  obtain ⟨G, hG1, hG2, hG3⟩ := hH
  exact ⟨G, hG1, hG2, hG3.congr_ae h⟩

/-- Cochrane (2023), §20.2.2, p. 475 (tool): `μ_{s,t} = (Leb ⊗ P)` restricted to
`(s, t] × Ω`. -/
theorem swmrep_measure_eq [SFinite P] (s t : ℝ) :
    mrepMeasure P s t = ((volume : Measure ℝ).prod P).restrict (Set.Ioc s t ×ˢ Set.univ) := by
  rw [mrepMeasure, ← Measure.prod_restrict, Measure.restrict_univ]

/-! ## A continuous version of the extended integral -/

/-- **Cochrane (2023), §20.2.2, pp. 474–476 (tool): a continuous modification of the extended
Itô integral.** Let `W` be pre-Brownian with measurable values and almost surely continuous
paths, `𝓕` admissible, `0 ≤ s < T`, and `H` in the extended class on `[s, T]`. There is `X`
with `X_t = ∫_s^t H dW` a.s. for every `t ∈ [s, T]` and almost surely continuous paths on
`[s, T]`. Generalises `TidyR10DoobMSVersion.exists_continuous_modification_ms`. -/
theorem swmrep_exists_continuous_modification (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω) (hs : 0 ≤ s) (hsT : s < T)
    (hH : MRepIntegrand P 𝓕 H s T) :
    ∃ X : ℝ → Ω → ℝ, (∀ t ∈ Set.Icc s T, X t =ᵐ[P] mrepInt P 𝓕 W H s t) ∧
      ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Icc s T) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨G, hGa⟩ := hH
  obtain ⟨hGms, hGm, hGL⟩ := hGa
  choose V hVI hVc using fun k =>
    exists_continuous_modification_ms hB hW h𝓕 hcont hs hsT (hGms k)
  choose N hN using fun j : ℕ => mrep_cauchy_of_L2Tendsto hGL ((1 / 8 : ℝ) ^ j) (by positivity)
  set n : ℕ → ℕ := fun j => ∑ i ∈ Finset.range (j + 1), N i + j with hn
  have hnN : ∀ j, N j ≤ n j := fun j =>
    (Finset.single_le_sum (fun i _ => Nat.zero_le (N i)) (Finset.self_mem_range_succ j)).trans
      (Nat.le_add_right _ _)
  have hnmono : StrictMono n := strictMono_nat_of_lt_succ fun j => by
    simp only [hn, Finset.sum_range_succ (n := j + 1)]
    omega
  set D : ℕ → ℝ → Ω → ℝ := fun j τ ω => V (n (j + 1)) τ ω - V (n j) τ ω with hD
  have hVc' : ∀ᵐ ω ∂P, ∀ k, ContinuousOn (fun t => V k t ω) (Set.Icc s T) := ae_all_iff.2 hVc
  have hDc : ∀ᵐ ω ∂P, ∀ j, ContinuousOn (fun τ => D j τ ω) (Set.Icc s T) := by
    filter_upwards [hVc'] with ω hω j
    exact (hω _).sub (hω _)
  have hdoob : ∀ j, Integrable (fun ω => pathSup s T (D j) ω ^ 2) P ∧
      ∫ ω, pathSup s T (D j) ω ^ 2 ∂P ≤ 4 * ∫ ω, itoInt P 𝓕 W
        (fun u ω => G (n (j + 1)) u ω - G (n j) u ω) s T ω ^ 2 ∂P := fun j =>
    doob_sq_itoInt_ms hB hW h𝓕 hs hsT (mrep_ms_sub (hGms _) (hGms _)) (fun t ht => by
      filter_upwards [hVI (n (j + 1)) t ht, hVI (n j) t ht, itoInt_sub_ms hB hW h𝓕 hs
        ((hGms (n (j + 1))).mono le_rfl ht.2) ((hGms (n j)).mono le_rfl ht.2)] with ω h1 h2 h3
      simp only [hD, h1, h2, h3])
      (hDc.mono fun ω hω => rightCont_of_continuousOn (hω j))
  have hET : ∀ j, ∫ ω, itoInt P 𝓕 W (fun u ω => G (n (j + 1)) u ω - G (n j) u ω) s T ω ^ 2 ∂P
      ≤ (1 / 8) ^ j := by
    intro j
    have e := itoInt_sub_ms hB hW h𝓕 hs (hGms (n (j + 1))) (hGms (n j))
    have e2 : (fun ω => itoInt P 𝓕 W (fun u ω => G (n (j + 1)) u ω - G (n j) u ω) s T ω ^ 2)
        =ᵐ[P] fun ω => (itoInt P 𝓕 W (G (n (j + 1))) s T ω
          - itoInt P 𝓕 W (G (n j)) s T ω) ^ 2 := e.mono fun ω hω => by simp only [hω]
    rw [integral_congr_ae e2, mrep_isometry_sub hB hW h𝓕 hs (hGms _) (hGm _) (hGms _) (hGm _)]
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
  set X : ℝ → Ω → ℝ := fun t ω => limUnder atTop (fun j => V (n j) t ω) with hX
  have hgood : ∀ᵐ ω ∂P, TendstoUniformlyOn (fun j t => V (n j) t ω)
      (fun t => X t ω) atTop (Set.Icc s T) := by
    filter_upwards [hae, hDc] with ω hω hωc
    obtain ⟨J, hJ⟩ := eventually_atTop.1 hω
    have hdiff : ∀ j ≥ J, ∀ t ∈ Set.Icc s T, |D j t ω| ≤ (1 / 2) ^ j := by
      intro j hj t ht
      have h1 := abs_le_pathSup_of_continuousOn (hωc j) ht (X := D j)
      have h2 : ¬ ((1 / 2 : ℝ) ^ j ≤ pathSup s T (D j) ω) := hJ j hj
      push Not at h2
      linarith
    set u : ℕ → ℝ → ℝ := fun m t => V (n (J + m)) t ω with hu_def
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
      have hfull : Tendsto (fun j => V (n j) t ω) atTop (𝓝 a0) := by
        refine (tendsto_add_atTop_iff_nat J).1 (ha0.congr fun m => ?_)
        simp only [hu_def]
        rw [add_comm]
      change Tendsto (fun m => u m t) atTop (𝓝 (limUnder atTop (fun j => V (n j) t ω)))
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
    filter_upwards [hgood, hVc'] with ω h1 h2
    exact h1.continuousOn (Frequently.of_forall fun j => h2 (n j))
  refine ⟨X, fun t ht => ?_, hXcont⟩
  have hL := swmrep_L2Tendsto_comp
    (mrep_spec hB hW h𝓕 hs (MRepApprox.mono (⟨hGms, hGm, hGL⟩ : MRepApprox P 𝓕 H s T G)
      le_rfl ht.2)).2
    hnmono
  have hae2 : ∀ᵐ ω ∂P, Tendsto (fun j => itoInt P 𝓕 W (G (n j)) s t ω) atTop
      (𝓝 (X t ω)) := by
    filter_upwards [hgood, ae_all_iff.2 fun k => hVI k t ht] with ω hω hV
    exact (hω.tendsto_at ht).congr fun j => hV (n j)
  exact (ae_eq_of_L2Tendsto_of_ae_tendsto hL hae2).symm

/-- **Cochrane (2023), §20.2.2, pp. 474–476 (tool): an adapted, almost surely continuous version
of `t ↦ ∫_s^t H dW` on `[s, ∞)`** for `H` in the extended class on every `[s, T]`: `X_t` is
`𝓕_t`-strongly measurable, `X_t = ∫_s^t H dW` a.s. for every `t ≥ s`, `X = 0` on `(−∞, s]`, and
almost every path is continuous on `ℝ`. -/
theorem swmrep_exists_adapted_continuous (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω) (hs : 0 ≤ s)
    (hH : ∀ T, MRepIntegrand P 𝓕 H s T) :
    ∃ X : ℝ → Ω → ℝ, (∀ t, StronglyMeasurable[𝓕 t] (X t)) ∧
      (∀ t, s ≤ t → X t =ᵐ[P] mrepInt P 𝓕 W H s t) ∧ (∀ t ≤ s, ∀ ω, X t ω = 0) ∧
      ∀ᵐ ω ∂P, Continuous fun t => X t ω := by
  classical
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set Y : ℝ → Ω → ℝ := fun t => if s < t then mrepInt P 𝓕 W H s t else 0 with hY
  have hYm : ∀ t, StronglyMeasurable[𝓕 t] (Y t) := fun t => by
    by_cases h : s < t
    · simp only [hY, h, ↓reduceIte]
      exact stronglyMeasurable_mrepInt hB hW h𝓕 hs (hH t)
    · simp only [hY, h, ↓reduceIte]
      exact stronglyMeasurable_const
  have hYs : ∀ ω, Y s ω = 0 := fun ω => by simp [hY]
  have hYI : ∀ t, s ≤ t → Y t =ᵐ[P] mrepInt P 𝓕 W H s t := fun t ht => by
    rcases ht.lt_or_eq with h | h
    · exact ae_of_all _ fun ω => by simp [hY, h]
    · subst h
      filter_upwards [mrepInt_self hB hW h𝓕 hs (hH s)] with ω hω
      rw [hYs ω, hω, Pi.zero_apply]
  have hmod : ∀ N : ℕ, ∃ X : ℝ → Ω → ℝ, (∀ t ∈ Set.Icc s (s + N), X t =ᵐ[P] Y t) ∧
      ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Icc s (s + N)) := by
    intro N
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · refine ⟨Y, fun _ _ => EventuallyEq.rfl, ae_of_all _ fun ω => ?_⟩
      simp only [h0, Nat.cast_zero, add_zero, Set.Icc_self]
      exact continuousOn_singleton _ _
    · have hsN : s < s + N := by
        have : (0 : ℝ) < N := Nat.cast_pos.2 hpos
        linarith
      obtain ⟨X, hXI, hXc⟩ := swmrep_exists_continuous_modification hB hW h𝓕 hcont hs hsN (hH _)
      exact ⟨X, fun t ht => (hXI t ht).trans (hYI t ht.1).symm, hXc⟩
  obtain ⟨X, hXm, hXY, hX0, hXc⟩ := exists_adapted_continuous_version hYm hYs hmod
  exact ⟨X, hXm, fun t ht => (hXY t ht).trans (hYI t ht), hX0, hXc⟩

/-- **Cochrane (2023), §20.2.2, pp. 474–476 (tool): `t ↦ ∫_s^t H dW` with every path
continuous.** For `H` in the extended class on every `[s, T]` there is `X`, adapted to the
completed filtration `augment P 𝓕`, with `X_t = ∫_s^t H dW` a.s. for every `t ≥ s`, `X = 0` on
`(−∞, s]`, EVERY path continuous, and `E[X_j | (augment P 𝓕)_i] = X_i` a.s. for `s ≤ i ≤ j`.
Generalises `TidyR10DoobAugment.exists_continuous_itoInt_augment` (bounded integrands). -/
theorem swmrep_exists_continuous_augment (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω) (hs : 0 ≤ s)
    (hH : ∀ T, MRepIntegrand P 𝓕 H s T) :
    ∃ X : ℝ → Ω → ℝ, (∀ t, StronglyMeasurable[augment P 𝓕 t] (X t)) ∧
      (∀ t, s ≤ t → X t =ᵐ[P] mrepInt P 𝓕 W H s t) ∧ (∀ t ≤ s, ∀ ω, X t ω = 0) ∧
      (∀ ω, Continuous fun t => X t ω) ∧
      ∀ i j, s ≤ i → i ≤ j → P[X j | augment P 𝓕 i] =ᵐ[P] X i := by
  classical
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨X0, hX0m, hX0I, hX00, hX0c⟩ := swmrep_exists_adapted_continuous hB hW h𝓕 hcont hs hH
  have hbad : P {ω | ¬ Continuous fun t => X0 t ω} = 0 := ae_iff.1 hX0c
  obtain ⟨N, hSN, hNm, hN0⟩ := exists_measurable_superset_of_null hbad
  set X : ℝ → Ω → ℝ := fun t ω => if ω ∈ N then 0 else X0 t ω with hX
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  have hXX0 : ∀ t, X t =ᵐ[P] X0 t := fun t => by
    filter_upwards [hNae] with ω hω
    simp only [hX, hω, ↓reduceIte]
  have hXm : ∀ t, StronglyMeasurable[augment P 𝓕 t] (X t) := by
    intro t
    have hmeas : Measurable (X t) :=
      Measurable.ite hNm measurable_const (((hX0m t).mono (𝓕.le t)).measurable)
    exact stronglyMeasurable_augment_of_ae_eq hmeas ((hX0m t).mono (le_augment t)) (hXX0 t)
  have hXI : ∀ t, s ≤ t → X t =ᵐ[P] mrepInt P 𝓕 W H s t := fun t ht =>
    (hXX0 t).trans (hX0I t ht)
  have hXc : ∀ ω, Continuous fun t => X t ω := by
    intro ω
    by_cases hω : ω ∈ N
    · simp only [hX, hω, ↓reduceIte]
      exact continuous_const
    · have hc : Continuous fun t => X0 t ω := by
        by_contra h
        exact hω (hSN h)
      simpa only [hX, hω, ↓reduceIte] using hc
  refine ⟨X, hXm, hXI, fun t ht ω => ?_, hXc, fun i j hsi hij => ?_⟩
  · simp only [hX, hX00 t ht ω]
    split_ifs <;> rfl
  · filter_upwards [condExp_augment (P := P) (𝓕 := 𝓕) (X j) i,
      condExp_congr_ae (m := 𝓕 i) (hXI j (hsi.trans hij)),
      mrepInt_condExp hB hW h𝓕 hs hsi hij (hH j), hXI i hsi] with ω e1 e2 e3 e4
    rw [e1, e2, e3, e4]

/-! ## Martingales on `[0, ∞)` as one stochastic integral -/

/-- **Cochrane (2023), §20.2.2, p. 475 (tool): the representing integrands of different
horizons agree.** If `H_k` represents `M` on `[0, k]` and `H_N` on `[0, N]`, `k ≤ N`, with the
same constant, then `H_k = H_N` `dt × dP`-a.e. on `(0, k] × Ω`. -/
theorem swmrep_horizon_consistent (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {M : ℝ → Ω → ℝ} {c k N : ℝ} (hk : 0 ≤ k) (hkN : k ≤ N)
    {Hk HN : ℝ → Ω → ℝ} (hHk : MRepIntegrand P 𝓕 Hk 0 k) (hHN : MRepIntegrand P 𝓕 HN 0 N)
    (hk' : M k =ᵐ[P] fun ω => c + mrepInt P 𝓕 W Hk 0 k ω)
    (hN' : ∀ t ∈ Set.Icc 0 N, M t =ᵐ[P] fun ω => c + mrepInt P 𝓕 W HN 0 t ω) :
    Function.uncurry Hk =ᵐ[mrepMeasure P 0 k] Function.uncurry HN := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact (mrep_unique hB hW h𝓕 hHk (mrep_mono hHN le_rfl hkN)
    (hk'.symm.trans (hN' k ⟨hk, hkN⟩))).2

/-- **Cochrane (2023), §20.2.2, p. 475 (tool): gluing consistent integrands.** If
`H_k = H_N` `dt × dP`-a.e. on `(0, k] × Ω` whenever `k ≤ N`, the glued integrand
`H(u, ω) = H_{⌈u⌉}(u, ω)` equals `H_N` a.e. on `(0, N] × Ω` for every `N`. -/
theorem swmrep_glue [SFinite P] {Hn : ℕ → ℝ → Ω → ℝ}
    (hcons : ∀ k N : ℕ, k ≤ N →
      Function.uncurry (Hn k) =ᵐ[mrepMeasure P 0 k] Function.uncurry (Hn N)) (N : ℕ) :
    Function.uncurry (fun u ω => Hn ⌈u⌉₊ u ω) =ᵐ[mrepMeasure P 0 N]
      Function.uncurry (Hn N) := by
  have hS : ∀ a : ℝ, MeasurableSet (Set.Ioc (0 : ℝ) a ×ˢ (Set.univ : Set Ω)) := fun a =>
    measurableSet_Ioc.prod MeasurableSet.univ
  have hk : ∀ k : ℕ, ∀ᵐ x ∂((volume : Measure ℝ).prod P), k ≤ N →
      x ∈ Set.Ioc (0 : ℝ) k ×ˢ (Set.univ : Set Ω) →
        Function.uncurry (Hn k) x = Function.uncurry (Hn N) x := by
    intro k
    by_cases hkN : k ≤ N
    · have h := hcons k N hkN
      rw [swmrep_measure_eq] at h
      filter_upwards [(ae_restrict_iff' (hS k)).1 h] with x hx _ hxS
      exact hx hxS
    · exact ae_of_all _ fun _ h => absurd h hkN
  rw [swmrep_measure_eq]
  refine (ae_restrict_iff' (hS N)).2 ?_
  filter_upwards [ae_all_iff.2 hk] with x hx hxS
  have hx1 : x.1 ∈ Set.Ioc (0 : ℝ) N := hxS.1
  have hle : ⌈x.1⌉₊ ≤ N := Nat.ceil_le.2 hx1.2
  exact hx ⌈x.1⌉₊ hle ⟨⟨hx1.1, Nat.le_ceil _⟩, trivial⟩

/-- **Cochrane (2023), §20.2.2, pp. 474–476: martingale representation on `[0, ∞)`.** Let `W`
be pre-Brownian with measurable values and EVERY path continuous, `𝓕` admissible with
`𝓕_T ⊆ σ(W_r : 0 ≤ r ≤ T)` for `T ≥ 0` (e.g. `bmFiltrationReal`, by
`TidyR13MRepMonetarism.mrep_bmFiltrationReal_le`), and `M` adapted, a martingale on `[0, ∞)`
(`E_s M_t = M_s`, `0 ≤ s ≤ t`), with `M_t ∈ L²` for every `t ≥ 0`. Then there is ONE `H`, in the
extended class on every `[0, T]`, with `M_t = E[M_0] + ∫_0^t H dW` a.s. for every `t ≥ 0`.
Extends `TidyR13MRepTheorem.mrep_martingale` (one horizon) to all horizons. -/
theorem swmrep_martingale_rep (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (h𝓕T : ∀ T, 0 ≤ T → 𝓕 T ≤ mrepNat W T) {M : ℝ → Ω → ℝ}
    (hMm : ∀ t, StronglyMeasurable[𝓕 t] (M t))
    (hmart : ∀ s t, 0 ≤ s → s ≤ t → P[M t | 𝓕 s] =ᵐ[P] M s)
    (hM2 : ∀ t, 0 ≤ t → MemLp (M t) 2 P) :
    ∃ H : ℝ → Ω → ℝ, (∀ T, MRepIntegrand P 𝓕 H 0 T) ∧
      ∀ t, 0 ≤ t → M t =ᵐ[P] fun ω => (∫ ω, M 0 ω ∂P) + mrepInt P 𝓕 W H 0 t ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hint : ∀ T, 0 ≤ T → ∫ ω, M T ω ∂P = ∫ ω, M 0 ω ∂P := fun T hT =>
    calc ∫ ω, M T ω ∂P = ∫ ω, P[M T | 𝓕 0] ω ∂P := (integral_condExp (𝓕.le 0)).symm
      _ = ∫ ω, M 0 ω ∂P := integral_congr_ae (hmart 0 T le_rfl hT)
  have hrepT : ∀ T : ℝ, 0 ≤ T → ∃ H, MRepIntegrand P 𝓕 H 0 T ∧ ∀ t ∈ Set.Icc 0 T,
      M t =ᵐ[P] fun ω => (∫ ω, M 0 ω ∂P) + mrepInt P 𝓕 W H 0 t ω := by
    intro T hT
    obtain ⟨H, hH, hrep⟩ := mrep_representation hB hW h𝓕 hcont (h𝓕T T hT) (hM2 T hT)
      ((hMm T).mono (h𝓕T T hT)).aestronglyMeasurable
    rw [hint T hT] at hrep
    refine ⟨H, hH, fun t ht => ?_⟩
    have hIT := (memLp_mrepInt hB hW h𝓕 le_rfl hH).integrable one_le_two
    have h1 := hmart t T ht.1 ht.2
    have h2 := condExp_congr_ae (m := 𝓕 t) hrep
    have h3 := condExp_add (integrable_const (∫ ω, M 0 ω ∂P)) hIT (𝓕 t)
    rw [condExp_const (𝓕.le t)] at h3
    have h4 := mrepInt_condExp hB hW h𝓕 le_rfl ht.1 ht.2 hH
    filter_upwards [h1, h2, h3, h4] with ω e1 e2 e3 e4
    rw [← e1, e2]
    refine e3.trans ?_
    rw [Pi.add_apply, e4]
  choose Hn hHn hrepn using fun N : ℕ => hrepT N (Nat.cast_nonneg N)
  have hcons : ∀ k N : ℕ, k ≤ N →
      Function.uncurry (Hn k) =ᵐ[mrepMeasure P 0 k] Function.uncurry (Hn N) := fun k N hkN =>
    swmrep_horizon_consistent hB hW h𝓕 (Nat.cast_nonneg k) (Nat.cast_le.2 hkN) (hHn k) (hHn N)
      (hrepn k k ⟨Nat.cast_nonneg k, le_rfl⟩) (hrepn N)
  set H : ℝ → Ω → ℝ := fun u ω => Hn ⌈u⌉₊ u ω with hHdef
  have hglue := swmrep_glue hcons
  have hHT : ∀ T, MRepIntegrand P 𝓕 H 0 T := fun T =>
    swmrep_integrand_congr_ae (mrep_mono (hHn ⌈T⌉₊) le_rfl (Nat.le_ceil T))
      (ae_mono (mrepMeasure_mono le_rfl (Nat.le_ceil T)) (hglue ⌈T⌉₊).symm)
  refine ⟨H, hHT, fun t ht => ?_⟩
  have hc := mrepInt_congr_ae hB hW h𝓕 le_rfl (mrep_mono (hHn ⌈t⌉₊) le_rfl (Nat.le_ceil t))
    (hHT t) (ae_mono (mrepMeasure_mono le_rfl (Nat.le_ceil t)) (hglue ⌈t⌉₊).symm)
  filter_upwards [hrepn ⌈t⌉₊ t ⟨ht, Nat.le_ceil t⟩, hc] with ω e1 e2
  rw [e1, e2]

/-- **Cochrane (2023), §20.2.2, pp. 474–476: uniqueness of the representation on `[0, ∞)`.**
If `M_t = c + ∫_0^t H dW` and `M_t = c' + ∫_0^t H' dW` a.s. for every `t ≥ 0`, with `H, H'` in
the extended class on every `[0, T]`, then `c = c'` and `H = H'` `dt × dP`-a.e. on
`(0, T] × Ω` for every `T ≥ 0`. -/
theorem swmrep_martingale_rep_unique (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {M : ℝ → Ω → ℝ} {c c' : ℝ} {H H' : ℝ → Ω → ℝ}
    (hH : ∀ T, MRepIntegrand P 𝓕 H 0 T) (hH' : ∀ T, MRepIntegrand P 𝓕 H' 0 T)
    (hrep : ∀ t, 0 ≤ t → M t =ᵐ[P] fun ω => c + mrepInt P 𝓕 W H 0 t ω)
    (hrep' : ∀ t, 0 ≤ t → M t =ᵐ[P] fun ω => c' + mrepInt P 𝓕 W H' 0 t ω) :
    c = c' ∧ ∀ T, 0 ≤ T →
      Function.uncurry H =ᵐ[mrepMeasure P 0 T] Function.uncurry H' := by
  refine ⟨(mrep_unique hB hW h𝓕 (hH 0) (hH' 0) ((hrep 0 le_rfl).symm.trans
    (hrep' 0 le_rfl))).1, fun T hT => ?_⟩
  exact (mrep_unique hB hW h𝓕 (hH T) (hH' T) ((hrep T hT).symm.trans (hrep' T hT))).2

end Cochrane.ZeroBound.TidyR9StochWerningMRepVersion
