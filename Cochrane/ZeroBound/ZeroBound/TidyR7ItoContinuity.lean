/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR7ItoIntegral
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# A continuous modification of `t ↦ ∫_s^t H dW`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for (1.32) with diffusive
bonds (chunk I5c, item 4): the Itô integral `TidyR7ItoIntegral.itoInt` has a modification with
almost surely continuous paths on `[s, T]`.

Mathlib has no continuous-time Doob inequality, so the route is elementary:

* `kolmogorov_maximal`: **Kolmogorov's maximal inequality**, `c²P(max_{l≤N}|Y_l| ≥ c) ≤ E[Y_N²]`,
  for square-integrable `Y_l` adapted to increasing σ-algebras whose future increments
  `Y_N − Y_l` are orthogonal to every square-integrable `m_l`-measurable `G` (first-passage
  decomposition; no martingale machinery).
* `truncSum W H p t = Σ_i H_{t_i}(W_{t_{i+1}∧t} − W_{t_i∧t})`, the left-point sum stopped at
  `t`; continuous in `t` (`continuous_truncSum`), equal to the left-point sum along the
  restricted partition `restrict p t` of `[s, t]` (`truncSum_eq_itoSum_restrict`), and the
  difference of two of them is a stopped elementary integral over the common refinement
  (`truncSum_sub_truncSum`), whose increments are orthogonal to the past
  (`integral_mul_cellSum_trunc_sub`).
* `exists_continuous_modification`: along a fast subsequence of the dyadic partitions
  (`E[(I_{n_{j+1}} − I_{n_j})²] ≤ 8^{−j}`), Kolmogorov's inequality on every dyadic grid and the
  first Borel–Cantelli lemma (`ae_eventually_notMem`) give `sup_{[s,T]}|Δ_j| < 2^{−j}`
  eventually a.s.; the stopped sums converge uniformly on `[s, T]`, so the limit `X` has
  continuous paths, and `X_t = ∫_s^t H dW` a.s. for every `t ∈ [s, T]`.
-/

namespace Cochrane.ZeroBound.TidyR7ItoContinuity

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.TidyR7StieltjesSums Cochrane.ZeroBound.TidyR7BrownianTools
  Cochrane.ZeroBound.TidyR7BrownianQV Cochrane.ZeroBound.TidyR7ItoL2
  Cochrane.ZeroBound.TidyR7ItoSums Cochrane.ZeroBound.TidyR7ItoIntegral
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ} {H : ℝ → Ω → ℝ} {s T C : ℝ}

/-! ## Kolmogorov's maximal inequality -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (tool): Kolmogorov's maximal inequality.** Let
`m_l` be increasing σ-algebras below the ambient one, `Y_l` square integrable and
`m_l`-strongly measurable, and suppose `E[G(Y_N − Y_l)] = 0` for every `l ≤ N` and every
square-integrable `m_l`-strongly measurable `G`. Then for `c > 0`,
`c²·P(∃ l ≤ N, c ≤ |Y_l|) ≤ E[Y_N²]`.
A variant, for orthogonal increments, of Mathlib `maximal_ineq`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoContinuity.kolmogorov_maximal). -/
theorem kolmogorov_maximal [IsFiniteMeasure P] {Y : ℕ → Ω → ℝ} {m : ℕ → MeasurableSpace Ω}
    (hm : Monotone m) (hmle : ∀ l, m l ≤ mΩ) (hY : ∀ l, StronglyMeasurable[m l] (Y l))
    (hY2 : ∀ l, MemLp (Y l) 2 P) (N : ℕ)
    (horth : ∀ l ≤ N, ∀ G : Ω → ℝ, StronglyMeasurable[m l] G → MemLp G 2 P →
      ∫ ω, G ω * (Y N ω - Y l ω) ∂P = 0) {c : ℝ} (hc : 0 < c) :
    c ^ 2 * P.real {ω | ∃ l ≤ N, c ≤ |Y l ω|} ≤ ∫ ω, Y N ω ^ 2 ∂P := by
  classical
  set A : ℕ → Set Ω := fun l => {ω | c ≤ ‖Y l ω‖} ∩ ⋂ j ∈ Finset.range l, {ω | ‖Y j ω‖ < c}
    with hA
  have hAm : ∀ l, MeasurableSet[m l] (A l) := by
    intro l
    refine (stronglyMeasurable_const.measurableSet_le (hY l).norm).inter ?_
    refine MeasurableSet.biInter (Finset.countable_toSet _) fun j hj => ?_
    exact (((hY j).mono (hm (Finset.mem_range.1 hj).le)).norm).measurableSet_lt
      stronglyMeasurable_const
  have hAm' : ∀ l, MeasurableSet (A l) := fun l => hmle l _ (hAm l)
  have hdisj : Set.Pairwise (↑(Finset.range (N + 1))) (Function.onFun Disjoint A) := by
    intro k _ l _ hkl
    refine Set.disjoint_left.2 fun ω hk hl => ?_
    rcases lt_or_gt_of_ne hkl with h | h
    · have h1 : ‖Y k ω‖ < c := Set.mem_iInter₂.1 hl.2 k (Finset.mem_range.2 h)
      have h2 : c ≤ ‖Y k ω‖ := hk.1
      linarith
    · have h1 : ‖Y l ω‖ < c := Set.mem_iInter₂.1 hk.2 l (Finset.mem_range.2 h)
      have h2 : c ≤ ‖Y l ω‖ := hl.1
      linarith
  have hcover : {ω | ∃ l ≤ N, c ≤ |Y l ω|} ⊆ ⋃ l ∈ Finset.range (N + 1), A l := by
    intro ω ⟨l, hl, hcl⟩
    have hex : ∃ l, c ≤ ‖Y l ω‖ := ⟨l, by rwa [Real.norm_eq_abs]⟩
    refine Set.mem_iUnion₂.2 ⟨Nat.find hex, Finset.mem_range.2 (by
      have := Nat.find_min' hex (show c ≤ ‖Y l ω‖ by rwa [Real.norm_eq_abs]); omega), ?_⟩
    refine ⟨Nat.find_spec hex, Set.mem_iInter₂.2 fun j hj => ?_⟩
    exact not_le.1 (Nat.find_min hex (Finset.mem_range.1 hj))
  have hint : ∀ l, Integrable (fun ω => Y l ω ^ 2) P := fun l => (hY2 l).integrable_sq
  -- the step `c²P(A_l) ≤ E[Y_N²; A_l]`
  have hstep : ∀ l ∈ Finset.range (N + 1),
      c ^ 2 * P.real (A l) ≤ ∫ ω in A l, Y N ω ^ 2 ∂P := by
    intro l hl
    have hlN : l ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
    have h1 : c ^ 2 * P.real (A l) ≤ ∫ ω in A l, Y l ω ^ 2 ∂P := by
      rw [mul_comm, ← smul_eq_mul, ← setIntegral_const]
      refine setIntegral_mono_on (integrableOn_const) (hint l).integrableOn (hAm' l)
        fun ω hω => ?_
      have h : c ≤ ‖Y l ω‖ := hω.1
      rw [Real.norm_eq_abs] at h
      rw [← sq_abs (Y l ω)]
      exact pow_le_pow_left₀ hc.le h 2
    have hR : Integrable (fun ω => Y l ω * (Y N ω - Y l ω)) P :=
      (hY2 l).integrable_mul ((hY2 N).sub (hY2 l))
    have hR2 : Integrable (fun ω => (Y N ω - Y l ω) ^ 2) P := ((hY2 N).sub (hY2 l)).integrable_sq
    have h0 : ∫ ω in A l, Y l ω * (Y N ω - Y l ω) ∂P = 0 := by
      rw [← integral_indicator (hAm' l)]
      have h := horth l hlN ((A l).indicator (Y l)) ((hY l).indicator (hAm l))
        ((hY2 l).indicator (hAm' l))
      rw [← h]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      by_cases hω : ω ∈ A l <;> simp [hω]
    have e : ∫ ω in A l, Y N ω ^ 2 ∂P = ∫ ω in A l, Y l ω ^ 2 ∂P
        + 2 * ∫ ω in A l, Y l ω * (Y N ω - Y l ω) ∂P + ∫ ω in A l, (Y N ω - Y l ω) ^ 2 ∂P := by
      have e1 : ∫ ω in A l, Y N ω ^ 2 ∂P = ∫ ω in A l, (Y l ω ^ 2
          + 2 * (Y l ω * (Y N ω - Y l ω)) + (Y N ω - Y l ω) ^ 2) ∂P :=
        integral_congr_ae (ae_of_all _ fun ω => by ring)
      have i1 : Integrable (fun ω => Y l ω ^ 2 + 2 * (Y l ω * (Y N ω - Y l ω)))
          (P.restrict (A l)) := ((hint l).add (hR.const_mul 2)).restrict
      have i2 : Integrable (fun ω => 2 * (Y l ω * (Y N ω - Y l ω))) (P.restrict (A l)) :=
        (hR.const_mul 2).restrict
      rw [e1, integral_add i1 hR2.restrict, integral_add (hint l).restrict i2,
        integral_const_mul]
    rw [e, h0]
    have : 0 ≤ ∫ ω in A l, (Y N ω - Y l ω) ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
    linarith
  calc c ^ 2 * P.real {ω | ∃ l ≤ N, c ≤ |Y l ω|}
      ≤ c ^ 2 * ∑ l ∈ Finset.range (N + 1), P.real (A l) :=
        mul_le_mul_of_nonneg_left ((measureReal_mono hcover (measure_ne_top _ _)).trans
          (measureReal_biUnion_finset_le _ _)) (sq_nonneg c)
    _ ≤ ∑ l ∈ Finset.range (N + 1), ∫ ω in A l, Y N ω ^ 2 ∂P := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum hstep
    _ = ∫ ω in ⋃ l ∈ Finset.range (N + 1), A l, Y N ω ^ 2 ∂P :=
        (integral_biUnion_finset _ (fun l _ => hAm' l) hdisj
          fun l _ => (hint N).integrableOn).symm
    _ ≤ ∫ ω, Y N ω ^ 2 ∂P :=
        setIntegral_le_integral (hint N) (ae_of_all _ fun _ => sq_nonneg _)

/-! ## Stopped elementary integrals -/

/-- Cochrane (2023), A1 §1.6, p. 567: the increment of `f` over `(a, b]` stopped at `v` minus
the one stopped at `u ≤ v` is the increment over `(a, b] ∩ (u, v]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoContinuity.four_point). -/
theorem four_point (f : ℝ → ℝ) {a b u v : ℝ} (hab : a ≤ b) (huv : u ≤ v) :
    (f (min b v) - f (min a v)) - (f (min b u) - f (min a u))
      = f (max (max a u) (min b v)) - f (max a u) := by
  rcases le_total b u with h1 | h1
  · rw [min_eq_left (h1.trans huv), min_eq_left ((hab.trans h1).trans huv), min_eq_left h1,
      min_eq_left (hab.trans h1), max_eq_right (hab.trans h1), max_eq_left h1]
    ring
  rcases le_total v a with h2 | h2
  · rw [min_eq_right (h2.trans hab), min_eq_right h2, min_eq_right (huv.trans (h2.trans hab)),
      min_eq_right (huv.trans h2), max_eq_left (huv.trans h2), max_eq_left h2]
    ring
  rw [min_eq_left h2, min_eq_right h1]
  rcases le_total a u with h3 | h3
  · rw [min_eq_left h3, max_eq_right h3, max_eq_right (le_min h1 huv)]
    ring
  · rw [min_eq_right h3, max_eq_left h3, max_eq_right (le_min hab h2)]
    ring

/-- Cochrane (2023), A1 §1.6, pp. 567–568: an elementary integral stopped at `τ`,
`Σ ξ_k(W_{b_k∧τ} − W_{a_k∧τ})`, is `𝓕_τ`-strongly measurable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoContinuity.stronglyMeasurable_cellSum_trunc). -/
theorem stronglyMeasurable_cellSum_trunc {κ : Type*} (h𝓕 : BMFiltration P W 𝓕) {S : Finset κ}
    {a b : κ → ℝ} {ξ : κ → Ω → ℝ} (hab : ∀ k ∈ S, a k ≤ b k)
    (hξ : ∀ k ∈ S, StronglyMeasurable[𝓕 (a k)] (ξ k)) (τ : ℝ) :
    StronglyMeasurable[𝓕 τ] (cellSum W S (fun k => min (a k) τ) (fun k => min (b k) τ) ξ) := by
  have e : cellSum W S (fun k => min (a k) τ) (fun k => min (b k) τ) ξ = fun ω =>
      ∑ k ∈ S, ξ k ω * incr W (min (a k) τ) (min (b k) τ) ω := rfl
  rw [e]
  refine Finset.stronglyMeasurable_fun_sum _ fun k hk => ?_
  by_cases h : a k ≤ τ
  · exact ((hξ k hk).mono (𝓕.mono h)).mul ((stronglyMeasurable_incr h𝓕
      (min_le_min_right τ (hab k hk))).mono (𝓕.mono (min_le_right _ _)))
  · have h' : τ ≤ a k := (not_le.1 h).le
    have e2 : (fun ω => ξ k ω * incr W (min (a k) τ) (min (b k) τ) ω) = fun _ => 0 := by
      funext ω
      rw [min_eq_right h', min_eq_right (h'.trans (hab k hk)), incr_self, mul_zero]
    rw [e2]
    exact stronglyMeasurable_const

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: future increments of a stopped elementary integral
are orthogonal to the past.** For `u ≤ v` and square-integrable `𝓕_u`-measurable `G`,
`E[G(D_v − D_u)] = 0`, `D_τ = Σ ξ_k(W_{b_k∧τ} − W_{a_k∧τ})`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoContinuity.integral_mul_cellSum_trunc_sub). -/
theorem integral_mul_cellSum_trunc_sub {κ : Type*} (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) {S : Finset κ} {a b : κ → ℝ}
    {ξ : κ → Ω → ℝ} (hab : ∀ k ∈ S, a k ≤ b k) (hξ : ∀ k ∈ S, StronglyMeasurable[𝓕 (a k)] (ξ k))
    {Cξ : ℝ} (hξb : ∀ k ∈ S, ∀ ω, |ξ k ω| ≤ Cξ) {u v : ℝ} (huv : u ≤ v) {G : Ω → ℝ}
    (hG : StronglyMeasurable[𝓕 u] G) (hG2 : MemLp G 2 P) :
    ∫ ω, G ω * (cellSum W S (fun k => min (a k) v) (fun k => min (b k) v) ξ ω
      - cellSum W S (fun k => min (a k) u) (fun k => min (b k) u) ξ ω) ∂P = 0 := by
  have e : ∀ ω, G ω * (cellSum W S (fun k => min (a k) v) (fun k => min (b k) v) ξ ω
      - cellSum W S (fun k => min (a k) u) (fun k => min (b k) u) ξ ω)
      = ∑ k ∈ S, (G ω * ξ k ω) * incr W (max (a k) u) (max (max (a k) u) (min (b k) v)) ω := by
    intro ω
    rw [cellSum, cellSum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have h4 := four_point (fun x => bmReal W x ω) (hab k hk) huv
    simp only [incr]
    rw [← h4]
    ring
  have hterm : ∀ k ∈ S, Integrable
      (fun ω => (G ω * ξ k ω) * incr W (max (a k) u) (max (max (a k) u) (min (b k) v)) ω) P := by
    intro k hk
    have hm : MemLp (fun ω => G ω * ξ k ω) 2 P := by
      refine hG2.of_le_mul (c := Cξ) ((hG.mono (𝓕.le u)).aestronglyMeasurable.mul
        ((hξ k hk).mono (𝓕.le _)).aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, mul_comm Cξ]
      exact mul_le_mul_of_nonneg_left (hξb k hk ω) (abs_nonneg _)
    exact hm.integrable_mul (memLp_incr hB _ _)
  simp_rw [e]
  rw [integral_finsetSum _ hterm]
  refine Finset.sum_eq_zero fun k hk => ?_
  exact integral_mul_incr hB hW h𝓕 (le_max_left _ _)
    ((hG.mono (𝓕.mono (le_max_right _ _))).mul ((hξ k hk).mono (𝓕.mono (le_max_left _ _))))

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: Kolmogorov's inequality for a stopped elementary
integral on a grid.** For times `τ_0 ≤ τ_1 ≤ …`, `0 ≤ τ_0`,
`c²P(∃ l ≤ N, c ≤ |D_{τ_l}|) ≤ E[D_{τ_N}²]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoContinuity.maximal_cellSum_trunc). -/
theorem maximal_cellSum_trunc {κ : Type*} (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) {S : Finset κ} {a b : κ → ℝ}
    {ξ : κ → Ω → ℝ} (hab : ∀ k ∈ S, a k ≤ b k) (hξ : ∀ k ∈ S, StronglyMeasurable[𝓕 (a k)] (ξ k))
    {Cξ : ℝ} (hξb : ∀ k ∈ S, ∀ ω, |ξ k ω| ≤ Cξ) {τ : ℕ → ℝ} (hτ : Monotone τ) (N : ℕ) {c : ℝ}
    (hc : 0 < c) :
    c ^ 2 * P.real {ω | ∃ l ≤ N, c ≤ |cellSum W S (fun k => min (a k) (τ l))
        (fun k => min (b k) (τ l)) ξ ω|}
      ≤ ∫ ω, cellSum W S (fun k => min (a k) (τ N)) (fun k => min (b k) (τ N)) ξ ω ^ 2 ∂P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hξm : ∀ k ∈ S, Measurable (ξ k) := fun k hk => ((hξ k hk).mono (𝓕.le _)).measurable
  exact kolmogorov_maximal (m := fun l => 𝓕 (τ l)) (fun _ _ h => 𝓕.mono (hτ h))
    (fun l => 𝓕.le (τ l)) (fun l => stronglyMeasurable_cellSum_trunc h𝓕 hab hξ (τ l))
    (fun l => memLp_cellSum hB hW hξm hξb) N
    (fun l hl G hG hG2 => integral_mul_cellSum_trunc_sub hB hW h𝓕 hab hξ hξb (hτ hl) hG hG2) hc

/-! ## Stopped left-point sums -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the left-point sum stopped at `t`**,
`Σ_i H_{t_i}(W_{t_{i+1}∧t} − W_{t_i∧t})`, along a partition of `[s, T]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoContinuity.truncSum). -/
noncomputable def truncSum (W : ℝ≥0 → Ω → ℝ) (H : ℝ → Ω → ℝ) (p : Partition s T) (t : ℝ)
    (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range p.n, H (p.t i) ω * incr W (min (p.t i) t) (min (p.t (i + 1)) t) ω

/-- Cochrane (2023), A1 §1.6, pp. 567–568: stopped at `t ≥ T`, the sum is the left-point sum.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoContinuity.truncSum_of_le). -/
theorem truncSum_of_le (H : ℝ → Ω → ℝ) (p : Partition s T) {t : ℝ} (ht : T ≤ t) (ω : Ω) :
    truncSum W H p t ω = itoSum W H p ω := by
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  rw [min_eq_left ((t_mem p hi'.le).2.trans ht), min_eq_left ((t_mem p hi').2.trans ht)]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: stopped at `t ≤ s`, the sum is `0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoContinuity.truncSum_of_le_start). -/
theorem truncSum_of_le_start (H : ℝ → Ω → ℝ) (p : Partition s T) {t : ℝ} (ht : t ≤ s) (ω : Ω) :
    truncSum W H p t ω = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  rw [min_eq_right (ht.trans (t_mem p hi'.le).1), min_eq_right (ht.trans (t_mem p hi').1),
    incr_self, mul_zero]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: for a continuous path of `W`, the stopped sum is
continuous in the stopping time.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoContinuity.continuous_truncSum). -/
theorem continuous_truncSum (H : ℝ → Ω → ℝ) (p : Partition s T) {ω : Ω}
    (hω : Continuous fun t => W t ω) : Continuous fun t => truncSum W H p t ω := by
  have hc := continuous_bmReal hω
  simp only [truncSum, incr]
  refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
  exact (hc.comp (continuous_const.min continuous_id)).sub
    (hc.comp (continuous_const.min continuous_id))

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the difference of two stopped sums is the stopped
elementary integral over the common refinement (`TidyR7ItoSums.sub_eq_sum_cells` applied to
`u ↦ W_{u∧t}`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoContinuity.truncSum_sub_truncSum). -/
theorem truncSum_sub_truncSum (H : ℝ → Ω → ℝ) (p q : Partition s T) (t : ℝ) (ω : Ω) :
    truncSum W H p t ω - truncSum W H q t ω
      = cellSum W (Finset.range p.n ×ˢ Finset.range q.n) (fun k => min (cellA p q k.1 k.2) t)
        (fun k => min (cellB p q k.1 k.2) t) (fun k ω => H (p.t k.1) ω - H (q.t k.2) ω) ω := by
  have hp : truncSum W H p t ω = ∑ i ∈ Finset.range p.n, ∑ j ∈ Finset.range q.n,
      H (p.t i) ω * incr W (min (cellA p q i j) t) (min (cellB p q i j) t) ω := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.mul_sum]
    congr 1
    exact sub_eq_sum_cells (fun u => bmReal W (min u t) ω) p q (Finset.mem_range.1 hi)
  have hq : truncSum W H q t ω = ∑ j ∈ Finset.range q.n, ∑ i ∈ Finset.range p.n,
      H (q.t j) ω * incr W (min (cellA p q i j) t) (min (cellB p q i j) t) ω := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.mul_sum]
    congr 1
    exact sub_eq_sum_cells' (fun u => bmReal W (min u t) ω) p q (Finset.mem_range.1 hj)
  rw [hp, hq, Finset.sum_comm (s := Finset.range q.n), cellSum, Finset.sum_product,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-! ## The restricted partition -/

/-- Cochrane (2023), A1 §1.6, p. 567: the index `m` of the piece `(t_m, t_{m+1}]` of a partition
of `[s, T]` containing `t` (the least `m` with `t ≤ t_{m+1}`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoContinuity.cutIndex). -/
noncomputable def cutIndex (p : Partition s T) (t : ℝ) : ℕ := sInf {j : ℕ | t ≤ p.t (j + 1)}

/-- Cochrane (2023), A1 §1.6, p. 567: for `s < t ≤ T`, `t_m < t ≤ t_{m+1}` and `m < n`, where
`m = cutIndex p t`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoContinuity.cutIndex_spec). -/
theorem cutIndex_spec (p : Partition s T) {t : ℝ} (hst : s < t) (htT : t ≤ T) :
    p.t (cutIndex p t) < t ∧ t ≤ p.t (cutIndex p t + 1) ∧ cutIndex p t < p.n := by
  have hn : p.n ≠ 0 := by
    intro h
    have := p.last
    rw [h, p.first] at this
    linarith
  have hmem : p.n - 1 ∈ {j : ℕ | t ≤ p.t (j + 1)} := by
    change t ≤ p.t (p.n - 1 + 1)
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hn), p.last]
    exact htT
  have h1 : cutIndex p t ∈ {j : ℕ | t ≤ p.t (j + 1)} := Nat.sInf_mem ⟨_, hmem⟩
  have h2 : cutIndex p t ≤ p.n - 1 := Nat.sInf_le hmem
  refine ⟨?_, h1, by omega⟩
  rcases Nat.eq_zero_or_pos (cutIndex p t) with h0 | h0
  · rw [h0, p.first]
    exact hst
  · obtain ⟨m, hm⟩ : ∃ m, cutIndex p t = m + 1 := ⟨cutIndex p t - 1, by omega⟩
    have hlt : m < cutIndex p t := by omega
    have := Nat.notMem_of_lt_sInf hlt
    simp only [Set.mem_ofPred_eq, not_le] at this
    rw [hm]
    exact this

/-- Cochrane (2023), A1 §1.6, p. 567: **the restriction of a partition of `[s, T]` to
`[s, t]`**, `s = t_0 < … < t_m < t` with `m = cutIndex p t` (later points continue past `t`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoContinuity.restrict). -/
noncomputable def restrict (p : Partition s T) {t : ℝ} (hst : s < t) (htT : t ≤ T) :
    Partition s t where
  n := cutIndex p t + 1
  t := fun i => if i ≤ cutIndex p t then p.t i else t + ((i : ℝ) - (cutIndex p t + 1))
  strictMono := by
    obtain ⟨h1, -, -⟩ := cutIndex_spec p hst htT
    intro i j hij
    simp only
    rcases le_or_gt j (cutIndex p t) with hj | hj
    · simp only [hj, hij.le.trans hj, ↓reduceIte]
      exact p.strictMono hij
    · simp only [show ¬ j ≤ cutIndex p t by omega, ↓reduceIte]
      have hj' : ((cutIndex p t : ℕ) : ℝ) + 1 ≤ j := by exact_mod_cast hj
      rcases le_or_gt i (cutIndex p t) with hi | hi
      · simp only [hi, ↓reduceIte]
        calc p.t i ≤ p.t (cutIndex p t) := p.strictMono.monotone hi
          _ < t := h1
          _ ≤ t + ((j : ℝ) - (cutIndex p t + 1)) := by linarith
      · simp only [show ¬ i ≤ cutIndex p t by omega, ↓reduceIte]
        have : (i : ℝ) < j := by exact_mod_cast hij
        linarith
  first := by simp only [Nat.zero_le, ↓reduceIte, p.first]
  last := by
    simp only [show ¬ cutIndex p t + 1 ≤ cutIndex p t by omega, ↓reduceIte]
    push_cast
    ring

/-- Cochrane (2023), A1 §1.6, p. 567: the points of the restriction up to `m`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoContinuity.restrict_t_of_le). -/
theorem restrict_t_of_le (p : Partition s T) {t : ℝ} (hst : s < t) (htT : t ≤ T) {i : ℕ}
    (hi : i ≤ cutIndex p t) : (restrict p hst htT).t i = p.t i := by
  simp only [restrict, hi, ↓reduceIte]

/-- Cochrane (2023), A1 §1.6, p. 567: the last point of the restriction is `t`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoContinuity.restrict_t_succ). -/
theorem restrict_t_succ (p : Partition s T) {t : ℝ} (hst : s < t) (htT : t ≤ T) :
    (restrict p hst htT).t (cutIndex p t + 1) = t := (restrict p hst htT).last

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the stopped sum is the left-point sum along the
restricted partition**.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoContinuity.truncSum_eq_itoSum_restrict). -/
theorem truncSum_eq_itoSum_restrict (H : ℝ → Ω → ℝ) (p : Partition s T) {t : ℝ} (hst : s < t)
    (htT : t ≤ T) (ω : Ω) : itoSum W H (restrict p hst htT) ω = truncSum W H p t ω := by
  obtain ⟨h1, h2, h3⟩ := cutIndex_spec p hst htT
  set m := cutIndex p t with hm
  obtain ⟨r, hr⟩ : ∃ r, p.n = m + 1 + r := ⟨p.n - (m + 1), by omega⟩
  have hzero : ∑ i ∈ Finset.range r, H (p.t (m + 1 + i)) ω *
      incr W (min (p.t (m + 1 + i)) t) (min (p.t (m + 1 + i + 1)) t) ω = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have ha : t ≤ p.t (m + 1 + i) := h2.trans (p.strictMono.monotone (by omega))
    have hb : t ≤ p.t (m + 1 + i + 1) := h2.trans (p.strictMono.monotone (by omega))
    rw [min_eq_right ha, min_eq_right hb, incr_self, mul_zero]
  simp only [itoSum, truncSum]
  rw [hr, Finset.sum_range_add, hzero, add_zero]
  change ∑ i ∈ Finset.range (m + 1), _ = _
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hpi : p.t i < t := (p.strictMono.monotone hi').trans_lt h1
  rw [restrict_t_of_le p hst htT hi', min_eq_left hpi.le]
  rcases hi'.lt_or_eq with hlt | heq
  · rw [restrict_t_of_le p hst htT (by omega : i + 1 ≤ m),
      min_eq_left ((p.strictMono.monotone (by omega : i + 1 ≤ m)).trans h1.le)]
  · rw [heq, restrict_t_succ, min_eq_right h2]

/-- Cochrane (2023), A1 §1.6, p. 567: the restriction has mesh at most that of `p`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoContinuity.mesh_restrict_le). -/
theorem mesh_restrict_le (p : Partition s T) {t : ℝ} (hst : s < t) (htT : t ≤ T) :
    mesh (restrict p hst htT) ≤ mesh p := by
  obtain ⟨_, h2, h3⟩ := cutIndex_spec p hst htT
  have hne : Nonempty (Fin (restrict p hst htT).n) := ⟨⟨0, Nat.succ_pos _⟩⟩
  refine ciSup_le fun i => ?_
  have hi : (i : ℕ) ≤ cutIndex p t := Nat.lt_succ_iff.1 i.2
  rw [restrict_t_of_le p hst htT hi]
  rcases hi.lt_or_eq with hlt | heq
  · rw [restrict_t_of_le p hst htT (by omega : (i : ℕ) + 1 ≤ cutIndex p t)]
    exact le_mesh p (by omega)
  · rw [heq, restrict_t_succ]
    exact (sub_le_sub_right h2 _).trans (le_mesh p h3)

/-! ## Density of the dyadic points -/

/-- Cochrane (2023), A1 §1.6, p. 567: a continuous `g` with `|g| < ε` at every dyadic point of
`[s, T]` (every level) satisfies `|g| ≤ ε` on `[s, T]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoContinuity.abs_le_of_dyadic). -/
theorem abs_le_of_dyadic {g : ℝ → ℝ} (hg : Continuous g) (hsT : s < T) {ε : ℝ}
    (h : ∀ L i, i ≤ 2 ^ L → |g ((dyadic hsT L).t i)| < ε) :
    ∀ t ∈ Set.Icc s T, |g t| ≤ ε := by
  intro t ht
  have hTs : 0 < T - s := sub_pos.2 hsT
  set y : ℕ → ℝ := fun L => (t - s) * 2 ^ L / (T - s) with hy
  have hy0 : ∀ L, 0 ≤ y L := fun L => div_nonneg (mul_nonneg (sub_nonneg.2 ht.1) (by positivity))
    hTs.le
  set x : ℕ → ℕ := fun L => ⌊y L⌋₊ with hx
  have hxle : ∀ L, x L ≤ 2 ^ L := by
    intro L
    have h1 : (x L : ℝ) ≤ y L := Nat.floor_le (hy0 L)
    have h2 : y L ≤ 2 ^ L := by
      rw [hy, div_le_iff₀ hTs]
      nlinarith [ht.2, (by positivity : (0 : ℝ) < 2 ^ L)]
    exact_mod_cast h1.trans h2
  have hpt : ∀ L, (dyadic hsT L).t (x L) = s + (T - s) * (x L) / 2 ^ L := fun L => rfl
  have hb : ∀ L, |(dyadic hsT L).t (x L) - t| ≤ (T - s) / 2 ^ L := by
    intro L
    have h1 : (x L : ℝ) ≤ y L := Nat.floor_le (hy0 L)
    have h2 : y L < x L + 1 := Nat.lt_floor_add_one (y L)
    have e : (dyadic hsT L).t (x L) - t = (T - s) / 2 ^ L * ((x L : ℝ) - y L) := by
      rw [hpt, hy]
      field_simp
      ring
    rw [e, abs_mul, abs_of_pos (by positivity), abs_of_nonpos (by linarith)]
    have : (T - s) / 2 ^ L * -((x L : ℝ) - y L) ≤ (T - s) / 2 ^ L * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hτ : Tendsto (fun L => (dyadic hsT L).t (x L)) atTop (𝓝 t) := by
    have h0 : Tendsto (fun L : ℕ => (T - s) / 2 ^ L) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun L => ?_)
      h0)
    rw [Real.norm_eq_abs]
    exact hb L
  have hlim := ((hg.tendsto t).comp hτ).abs
  exact le_of_tendsto hlim (Eventually.of_forall fun L => (h L (x L) (hxle L)).le)

/-! ## The continuous modification (item 4) -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (item 4): the Itô integral has a continuous
modification.** If `W` has a.s. continuous paths and `H` is admissible on `[s, T]`,
`0 ≤ s < T`, there is `X` with `X_t = ∫_s^t H dW` a.s. for every `t ∈ [s, T]` and
`t ↦ X_t` continuous on `[s, T]` almost surely. `X_t` is the limit of the stopped dyadic sums
along a fast subsequence; Kolmogorov's inequality and Borel–Cantelli give uniform convergence.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoContinuity.exists_continuous_modification). -/
theorem exists_continuous_modification (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω) (hs : 0 ≤ s)
    (hsT : s < T) (hH : ItoIntegrand P 𝓕 H s T C) :
    ∃ X : ℝ → Ω → ℝ, (∀ t ∈ Set.Icc s T, X t =ᵐ[P] itoInt P 𝓕 W H s t) ∧
      ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Set.Icc s T) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set d : ℕ → Partition s T := fun n => dyadic hsT n with hd
  choose N hN using fun j : ℕ => cauchy_itoSum hB hW h𝓕 hs hsT hH d (tendsto_mesh_dyadic hsT)
    (ε := (1 / 8) ^ j) (by positivity)
  set n : ℕ → ℕ := fun j => ∑ i ∈ Finset.range (j + 1), N i + j with hn
  have hnN : ∀ j, N j ≤ n j := fun j =>
    (Finset.single_le_sum (fun i _ => Nat.zero_le (N i)) (Finset.self_mem_range_succ j)).trans
      (Nat.le_add_right _ _)
  have hnmono : StrictMono n := strictMono_nat_of_lt_succ fun j => by
    simp only [hn, Finset.sum_range_succ (n := j + 1)]
    omega
  -- the stopped differences, as stopped elementary integrals
  set S : ℕ → Finset (ℕ × ℕ) := fun j => Finset.range (d (n (j + 1))).n ×ˢ Finset.range (d (n j)).n
  set a : ℕ → ℕ × ℕ → ℝ := fun j k => cellA (d (n (j + 1))) (d (n j)) k.1 k.2
  set b : ℕ → ℕ × ℕ → ℝ := fun j k => cellB (d (n (j + 1))) (d (n j)) k.1 k.2
  set ξ : ℕ → ℕ × ℕ → Ω → ℝ := fun j k ω => H ((d (n (j + 1))).t k.1) ω - H ((d (n j)).t k.2) ω
  set D : ℕ → ℝ → Ω → ℝ := fun j τ =>
    cellSum W (S j) (fun k => min (a j k) τ) (fun k => min (b j k) τ) (ξ j) with hDdef
  have hD : ∀ j τ ω,
      D j τ ω = truncSum W H (d (n (j + 1))) τ ω - truncSum W H (d (n j)) τ ω :=
    fun j τ ω => (truncSum_sub_truncSum H _ _ τ ω).symm
  have hmem : ∀ j, ∀ k ∈ S j,
      (d (n (j + 1))).t k.1 ∈ Set.Icc s T ∧ (d (n j)).t k.2 ∈ Set.Icc s T := by
    intro j k hk
    rw [Finset.mem_product] at hk
    exact ⟨t_mem _ (Finset.mem_range.1 hk.1).le, t_mem _ (Finset.mem_range.1 hk.2).le⟩
  have hab : ∀ j, ∀ k ∈ S j, a j k ≤ b j k := fun j k _ => cellA_le_cellB _ _ _ _
  have hξ : ∀ j, ∀ k ∈ S j, StronglyMeasurable[𝓕 (a j k)] (ξ j k) := fun j k hk =>
    ((hH.adapted _ (hmem j k hk).1).mono (𝓕.mono (le_max_left _ _))).sub
      ((hH.adapted _ (hmem j k hk).2).mono (𝓕.mono (le_max_right _ _)))
  have hξb : ∀ j, ∀ k ∈ S j, ∀ ω, |ξ j k ω| ≤ 2 * C := fun j k hk ω => by
    rw [two_mul]
    exact (abs_sub _ _).trans (add_le_add (hH.bound _ (hmem j k hk).1 ω)
      (hH.bound _ (hmem j k hk).2 ω))
  have hET : ∀ j, ∫ ω, D j T ω ^ 2 ∂P ≤ (1 / 8) ^ j := by
    intro j
    have e : ∀ ω, D j T ω = itoSum W H (d (n (j + 1))) ω - itoSum W H (d (n j)) ω := fun ω => by
      rw [hD, truncSum_of_le _ _ le_rfl, truncSum_of_le _ _ le_rfl]
    simp_rw [e]
    exact hN j _ ((hnN j).trans (hnmono.monotone (Nat.le_succ j))) _ (hnN j)
  -- the bad events and Borel–Cantelli
  set E : ℕ → ℕ → Set Ω := fun j L => {ω | ∃ l ≤ 2 ^ L, (1 / 2) ^ j ≤ |D j ((d L).t l) ω|}
    with hE
  have hEbd : ∀ j L, P (E j L) ≤ ENNReal.ofReal ((1 / 2) ^ j) := by
    intro j L
    have hmax := maximal_cellSum_trunc hB hW h𝓕 (hab j) (hξ j) (hξb j)
      (d L).strictMono.monotone (2 ^ L) (c := (1 / 2) ^ j) (by positivity)
    have hlast : (d L).t (2 ^ L) = T := (d L).last
    rw [hlast] at hmax
    have h2 : (1 / 4) ^ j * P.real (E j L) ≤ (1 / 4) ^ j * (1 / 2) ^ j := by
      calc (1 / 4 : ℝ) ^ j * P.real (E j L) = ((1 / 2) ^ j) ^ 2 * P.real (E j L) := by
            rw [← pow_mul, mul_comm j 2, pow_mul]
            norm_num
        _ ≤ ∫ ω, D j T ω ^ 2 ∂P := hmax
        _ ≤ (1 / 8) ^ j := hET j
        _ = (1 / 4) ^ j * (1 / 2) ^ j := by rw [← mul_pow]; norm_num
    have h3 : P.real (E j L) ≤ (1 / 2) ^ j := le_of_mul_le_mul_left h2 (by positivity)
    rw [← ofReal_measureReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal h3
  have hEmono : ∀ j, Monotone (E j) := by
    intro j L L' hLL' ω hω
    obtain ⟨l, hl, hlω⟩ := hω
    obtain ⟨r, rfl⟩ : ∃ r, L' = L + r := ⟨L' - L, by omega⟩
    refine ⟨l * 2 ^ r, ?_, ?_⟩
    · rw [pow_add]
      exact Nat.mul_le_mul_right _ hl
    · have e : (d (L + r)).t (l * 2 ^ r) = (d L).t l := by
        simp only [hd, dyadic]
        push_cast
        rw [pow_add]
        field_simp
      rw [e]
      exact hlω
  have hBbd : ∀ j, P (⋃ L, E j L) ≤ ENNReal.ofReal ((1 / 2) ^ j) := fun j => by
    rw [(hEmono j).measure_iUnion]
    exact iSup_le (hEbd j)
  have hsum : ∑' j, P (⋃ L, E j L) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hBbd)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
    exact ENNReal.ofReal_ne_top
  have hae := ae_eventually_notMem hsum
  -- the modification and its uniform convergence on good paths
  set X : ℝ → Ω → ℝ := fun t ω => limUnder atTop (fun j => truncSum W H (d (n j)) t ω) with hX
  have hgood : ∀ᵐ ω ∂P, TendstoUniformlyOn (fun j t => truncSum W H (d (n j)) t ω)
      (fun t => X t ω) atTop (Set.Icc s T) := by
    filter_upwards [hae, hcont] with ω hω hωc
    obtain ⟨J, hJ⟩ := eventually_atTop.1 hω
    have hdiff : ∀ j ≥ J, ∀ t ∈ Set.Icc s T, |D j t ω| ≤ (1 / 2) ^ j := by
      intro j hj
      have hc : Continuous fun t => D j t ω := by
        have e : (fun t => D j t ω)
            = fun t => truncSum W H (d (n (j + 1))) t ω - truncSum W H (d (n j)) t ω :=
          funext fun t => hD j t ω
        rw [e]
        exact (continuous_truncSum H _ hωc).sub (continuous_truncSum H _ hωc)
      refine abs_le_of_dyadic hc hsT fun L l hl => ?_
      by_contra hcon
      push Not at hcon
      exact hJ j hj (Set.mem_iUnion.2 ⟨L, l, hl, hcon⟩)
    set u : ℕ → ℝ → ℝ := fun m t => truncSum W H (d (n (J + m))) t ω with hu_def
    have hu : ∀ t ∈ Set.Icc s T, ∀ m, dist (u m t) (u (m + 1) t) ≤ 2 * (1 / 2) ^ J / 2 / 2 ^ m := by
      intro t ht m
      rw [Real.dist_eq, abs_sub_comm]
      have h := hdiff (J + m) (Nat.le_add_right J m) t ht
      rw [hD] at h
      have e : 2 * (1 / 2 : ℝ) ^ J / 2 / 2 ^ m = (1 / 2) ^ (J + m) := by
        rw [pow_add, one_div_pow (2 : ℝ) m]
        ring
      rw [e]
      exact h
    have hconv : ∀ t ∈ Set.Icc s T, Tendsto (fun m => u m t) atTop (𝓝 (X t ω)) := by
      intro t ht
      obtain ⟨a0, ha0⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two (hu t ht))
      have hfull : Tendsto (fun j => truncSum W H (d (n j)) t ω) atTop (𝓝 a0) := by
        refine (tendsto_add_atTop_iff_nat J).1 (ha0.congr fun m => ?_)
        simp only [hu_def]
        rw [add_comm]
      change Tendsto (fun m => u m t) atTop
        (𝓝 (limUnder atTop (fun j => truncSum W H (d (n j)) t ω)))
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
    exact h1.continuousOn (Frequently.of_forall fun j => (continuous_truncSum H _ h2).continuousOn)
  refine ⟨X, fun t ht => ?_, hXcont⟩
  rcases ht.1.lt_or_eq with hst | hst
  · have hps : Tendsto (fun j => mesh (restrict (d (n j)) hst ht.2)) atTop (𝓝 0) :=
      squeeze_zero (fun _ => mesh_nonneg _) (fun j => mesh_restrict_le _ _ _)
        ((tendsto_mesh_dyadic hsT).comp hnmono.tendsto_atTop)
    have hL := L2Tendsto_itoSum hB hW h𝓕 hs hst (hH.mono le_rfl ht.2) _ hps
    have hae2 : ∀ᵐ ω ∂P, Tendsto (fun j => itoSum W H (restrict (d (n j)) hst ht.2) ω) atTop
        (𝓝 (X t ω)) := by
      filter_upwards [hgood] with ω hω
      exact (hω.tendsto_at ht).congr fun j => (truncSum_eq_itoSum_restrict H _ hst ht.2 ω).symm
    exact (ae_eq_of_L2Tendsto_of_ae_tendsto hL hae2).symm
  · have e1 : X t = 0 := by
      funext ω
      have e2 : (fun j => truncSum W H (d (n j)) t ω) = fun _ => 0 :=
        funext fun j => truncSum_of_le_start H _ hst.ge ω
      simp only [hX, e2]
      exact tendsto_const_nhds.limUnder_eq
    rw [e1, ← hst, itoInt_of_le le_rfl]

end Cochrane.ZeroBound.TidyR7ItoContinuity
