/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR7StieltjesIntegral

/-!
# Convergence of Riemann–Stieltjes sums

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). The product step in (1.32),
`Λ/P · dB + E_t d(Λ/P)·B = E_t d(ΛB/P)`, is proved path by path from the exact partition identity
`B_tX_t − B_sX_s = Σ B_iΔX_i + Σ X_iΔB_i + Σ ΔB_iΔX_i` by letting the mesh go to zero. These are
the deterministic Riemann–Stieltjes tools for that (1.32) product step: the left-point sums
converge to the integral `TidyR7StieltjesIntegral.rsInt`, and the cross sum vanishes.

A partition (`Partition a b`) is a strictly increasing `t : ℕ → ℝ` with `t 0 = a`, `t n = b`;
`mesh P = max_{i<n}(t_{i+1} − t_i)`; `rsSum P f g = Σ_{i<n} f(t_i)(g(t_{i+1}) − g(t_i))` and
`crossSum P f g = Σ_{i<n} (f(t_{i+1}) − f(t_i))(g(t_{i+1}) − g(t_i))`.

## Main results (along ANY sequence of partitions with mesh → 0)

* `tendsto_rsSum_of_continuousOn` (case (a)): `f` continuous on `[a, b]`, `g` of bounded
  variation (jumps allowed): `rsSum → ∫_a^b f dg`. Quantitative form
  `abs_rsSum_sub_rsInt_le`: `|rsSum P f g − ∫f dg| ≤ 2ε·Var(g)` when `f` oscillates by `≤ ε` over
  distances `≤ mesh P`.
* `tendsto_rsSum_of_isCadlag` (case (b)): `f` càdlàg (hence bounded on `[a, b]`), `g` continuous
  of bounded variation: `rsSum → ∫_a^b f dg = ∫_a^b f(t−) dg` (`rsInt_eq_rsInt_leftLim`; `g` has
  no atoms and `f` has countably many jumps).
* `tendsto_crossSum_zero`: `f` càdlàg, `g` continuous of bounded variation:
  `crossSum → 0` (`f` need not have bounded variation). Proof: the cross sum is
  `∫ f(right point) dg − ∫ f(left point) dg`, whose integrands converge to `f` and `f(·−)`, equal
  off a countable set, which `dg` does not charge.
* `crossSum_heaviside`, `not_tendsto_crossSum_heaviside`: **continuity of `g` is needed**: with
  `f = g = 1_{[1,∞)}` on `[0, 2]` (càdlàg, bounded variation) the cross sum is `1` for EVERY
  partition.
* `dyadic`, `tendsto_mesh_dyadic`: the dyadic partitions; `tendsto_rsSum_dyadic_of_continuousOn`,
  `tendsto_rsSum_dyadic_of_isCadlag`,
  `tendsto_crossSum_dyadic` are the dyadic corollaries.
-/

namespace Cochrane.ZeroBound.TidyR7StieltjesSums

open MeasureTheory Filter Topology
open Cochrane.ZeroBound.TidyR7StieltjesIntegral

variable (a b : ℝ)

/-- Cochrane (2023), A1 §1.6, p. 567 (tool for (1.32)): a partition `a = t_0 < t_1 < … < t_n = b`
of `[a, b]` (the points `t_i`, `i > n`, are only required to keep increasing).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.Partition). -/
structure Partition where
  n : ℕ
  t : ℕ → ℝ
  strictMono : StrictMono t
  first : t 0 = a
  last : t n = b

variable {a b}

/-- Cochrane (2023), A1 §1.6, p. 567: the mesh `max_{i<n}(t_{i+1} − t_i)` of a partition.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7StieltjesSums.mesh). -/
noncomputable def mesh (P : Partition a b) : ℝ := ⨆ i : Fin P.n, (P.t ((i : ℕ) + 1) - P.t i)

/-- Cochrane (2023), A1 §1.6, p. 567: each step of a partition is at most its mesh.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7StieltjesSums.le_mesh). -/
theorem le_mesh (P : Partition a b) {i : ℕ} (hi : i < P.n) : P.t (i + 1) - P.t i ≤ mesh P :=
  le_ciSup (f := fun i : Fin P.n => P.t ((i : ℕ) + 1) - P.t i) (Set.finite_range _).bddAbove
    ⟨i, hi⟩

/-- Cochrane (2023), A1 §1.6, p. 567: **the left-point Riemann–Stieltjes sum**
`Σ_{i<n} f(t_i)(g(t_{i+1}) − g(t_i))`.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7StieltjesSums.rsSum). -/
def rsSum (P : Partition a b) (f g : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range P.n, f (P.t i) * (g (P.t (i + 1)) - g (P.t i))

/-- Cochrane (2023), A1 §1.6, p. 567: **the cross sum**
`Σ_{i<n} (f(t_{i+1}) − f(t_i))(g(t_{i+1}) − g(t_i))`.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7StieltjesSums.crossSum). -/
def crossSum (P : Partition a b) (f g : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range P.n, (f (P.t (i + 1)) - f (P.t i)) * (g (P.t (i + 1)) - g (P.t i))

/-- Cochrane (2023), A1 §1.6, p. 567: the step function equal to `c_i` on `(t_i, t_{i+1}]`.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7StieltjesSums.stepFn). -/
noncomputable def stepFn (P : Partition a b) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range P.n, (Set.Ioc (P.t i) (P.t (i + 1))).indicator (fun _ => c i) x

/-! ## Partitions and step functions -/

/-- Cochrane (2023), A1 §1.6, p. 567: the points `t_0, …, t_n` lie in `[a, b]`.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7StieltjesSums.t_mem). -/
theorem t_mem (P : Partition a b) {i : ℕ} (hi : i ≤ P.n) : P.t i ∈ Set.Icc a b := by
  have h1 := P.strictMono.monotone (Nat.zero_le i)
  have h2 := P.strictMono.monotone hi
  rw [P.first] at h1
  rw [P.last] at h2
  exact ⟨h1, h2⟩

/-- Cochrane (2023), A1 §1.6, p. 567: a partition of `[a, b]` exists only if `a ≤ b`.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7StieltjesSums.a_le_b). -/
theorem a_le_b (P : Partition a b) : a ≤ b := (t_mem P (le_refl P.n)).1.trans (t_mem P le_rfl).2

/-- Cochrane (2023), A1 §1.6, p. 567: each piece `(t_i, t_{i+1}]`, `i < n`, lies in `(a, b]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.Ioc_subset). -/
theorem Ioc_subset (P : Partition a b) {i : ℕ} (hi : i < P.n) :
    Set.Ioc (P.t i) (P.t (i + 1)) ⊆ Set.Ioc a b :=
  Set.Ioc_subset_Ioc (t_mem P hi.le).1 (t_mem P hi).2

/-- Cochrane (2023), A1 §1.6, p. 567: every `x ∈ (a, b]` lies in a piece `(t_j, t_{j+1}]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.exists_piece). -/
theorem exists_piece (P : Partition a b) {x : ℝ} (hx : x ∈ Set.Ioc a b) :
    ∃ j < P.n, x ∈ Set.Ioc (P.t j) (P.t (j + 1)) := by
  classical
  have hn : x ≤ P.t P.n := by rw [P.last]; exact hx.2
  have hex : ∃ m, x ≤ P.t m := ⟨P.n, hn⟩
  have hm1 : x ≤ P.t (Nat.find hex) := Nat.find_spec hex
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, P.first] at hm1
    exact absurd hm1 (not_le.2 hx.1)
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hle : Nat.find hex ≤ P.n := Nat.find_min' hex hn
  refine ⟨j, by omega, lt_of_not_ge (Nat.find_min hex (by omega)), ?_⟩
  rw [hj] at hm1
  exact hm1

/-- Cochrane (2023), A1 §1.6, p. 567: on the piece `(t_j, t_{j+1}]` the step function is `c_j`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.stepFn_eq). -/
theorem stepFn_eq (P : Partition a b) (c : ℕ → ℝ) {j : ℕ} (hj : j < P.n) {x : ℝ}
    (hx : x ∈ Set.Ioc (P.t j) (P.t (j + 1))) : stepFn P c x = c j := by
  rw [stepFn, Finset.sum_eq_single j]
  · exact Set.indicator_of_mem hx _
  · intro i _ hij
    refine Set.indicator_of_notMem (fun hxi => hij ?_) _
    rcases lt_trichotomy i j with h | h | h
    · exact absurd (hxi.2.trans (P.strictMono.monotone (by omega : i + 1 ≤ j))) (not_le.2 hx.1)
    · exact h
    · exact absurd (hx.2.trans (P.strictMono.monotone (by omega : j + 1 ≤ i))) (not_le.2 hxi.1)
  · intro h
    exact absurd (Finset.mem_range.2 hj) h

/-- Cochrane (2023), A1 §1.6, p. 567: the step function vanishes off `(a, b]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.stepFn_of_notMem). -/
theorem stepFn_of_notMem (P : Partition a b) (c : ℕ → ℝ) {x : ℝ} (hx : x ∉ Set.Ioc a b) :
    stepFn P c x = 0 :=
  Finset.sum_eq_zero fun _ hi =>
    Set.indicator_of_notMem (fun h => hx (Ioc_subset P (Finset.mem_range.1 hi) h)) _

/-- Cochrane (2023), A1 §1.6, p. 567: a step function with values bounded by `C` is bounded by
`C`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.abs_stepFn_le). -/
theorem abs_stepFn_le (P : Partition a b) (c : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ i < P.n, |c i| ≤ C) (x : ℝ) : |stepFn P c x| ≤ C := by
  by_cases hx : x ∈ Set.Ioc a b
  · obtain ⟨j, hj, hjx⟩ := exists_piece P hx
    rw [stepFn_eq P c hj hjx]
    exact hc j hj
  · rw [stepFn_of_notMem P c hx, abs_zero]
    exact hC

/-- Cochrane (2023), A1 §1.6, p. 567: step functions are measurable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.measurable_stepFn). -/
theorem measurable_stepFn (P : Partition a b) (c : ℕ → ℝ) : Measurable (stepFn P c) :=
  Finset.measurable_sum _ fun _ _ => measurable_const.indicator measurableSet_Ioc

/-- Cochrane (2023), A1 §1.6, p. 567: **integral of a step function**: for `G` of bounded
variation on `ℝ`, `∫_{(a,b]} Σ c_i 1_{(t_i, t_{i+1}]} dG = Σ c_i (G(t_{i+1}+) − G(t_i+))`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.integral_stepFn). -/
theorem integral_stepFn {G : ℝ → ℝ} (hG : BoundedVariationOn G Set.univ)
    (hfin : IsFiniteMeasure hG.vectorMeasure.variation) (P : Partition a b) (c : ℕ → ℝ) :
    ∫ᵛ x in Set.Ioc a b, stepFn P c x ∂• hG.vectorMeasure =
      ∑ i ∈ Finset.range P.n,
        c i * (Function.rightLim G (P.t (i + 1)) - Function.rightLim G (P.t i)) := by
  simp only [stepFn]
  rw [VectorMeasure.integral_finsetSum]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [VectorMeasure.setIntegral_indicator measurableSet_Ioc measurableSet_Ioc,
      Set.inter_eq_right.2 (Ioc_subset P (Finset.mem_range.1 hi)),
      VectorMeasure.setIntegral_const,
      hG.vectorMeasure_Ioc (P.strictMono.monotone (Nat.le_succ i))]
    simp
  · intro i _
    exact (integrable_const _).indicator measurableSet_Ioc

/-- Cochrane (2023), A1 §1.6, p. 567: `∫_{[a,b]} f dν = f(a)ν{a} + ∫_{(a,b]} f dν`.
Mathlib `VectorMeasure.setIntegral_union` on `{a} ∪ (a, b]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.setIntegral_Icc_eq). -/
theorem setIntegral_Icc_eq {ν : VectorMeasure ℝ ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : ν.IntegrableOn f (Set.Icc a b)) :
    ∫ᵛ x in Set.Icc a b, f x ∂•ν = f a * ν {a} + ∫ᵛ x in Set.Ioc a b, f x ∂•ν := by
  have e : Set.Icc a b = {a} ∪ Set.Ioc a b := by
    rw [← Set.Icc_union_Ioc_eq_Icc le_rfl hab, Set.Icc_self]
  rw [e, VectorMeasure.setIntegral_union
    (Set.disjoint_singleton_left.2 fun h => lt_irrefl a h.1) (measurableSet_singleton a)
    measurableSet_Ioc (hf.mono measurableSet_Icc (by rw [e]; exact Set.subset_union_left))
    (hf.mono measurableSet_Icc Set.Ioc_subset_Icc_self), VectorMeasure.integral_singleton]
  simp

/-! ## Variation bounds for the jumps -/

/-- Cochrane (2023), A1 §1.6, p. 567: summation by parts,
`Σ_{i<n} u_i(v_{i+1} − v_i) = u_nv_n − u_0v_0 − Σ_{i<n}(u_{i+1} − u_i)v_{i+1}`.
A difference form of Mathlib `Finset.sum_range_by_parts`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.sum_mul_sub_eq). -/
theorem sum_mul_sub_eq (u v : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, u i * (v (i + 1) - v i) =
      u n * v n - u 0 * v 0 - ∑ i ∈ Finset.range n, (u (i + 1) - u i) * v (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

/-- Cochrane (2023), A1 §1.6, p. 567: the right jump `|G(x) − G(x+)|` is at most the
variation of `G` on `[x, y]`, `x < y`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.abs_sub_rightLim_le). -/
theorem abs_sub_rightLim_le {G : ℝ → ℝ} (hG : BoundedVariationOn G Set.univ) {x y : ℝ}
    (hxy : x < y) : |G x - Function.rightLim G x| ≤ (eVariationOn G (Set.Icc x y)).toReal := by
  have hb : BoundedVariationOn G (Set.Icc x y) := hG.mono (Set.subset_univ _)
  have hlim : Tendsto (fun z => |G z - G x|) (𝓝[>] x) (𝓝 |Function.rightLim G x - G x|) :=
    ((hG.tendsto_rightLim x).sub tendsto_const_nhds).abs
  rw [abs_sub_comm]
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hxy] with z hz
  have := hb.dist_le ⟨hz.1.le, hz.2.le⟩ ⟨le_rfl, hxy.le⟩
  rwa [Real.dist_eq] at this

/-- Cochrane (2023), A1 §1.6, p. 567: the variation is additive along a monotone sequence of
points.
Mathlib `eVariationOn.sum'` on `ℝ`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.sum_eVariationOn_Icc). -/
theorem sum_eVariationOn_Icc (G : ℝ → ℝ) {u : ℕ → ℝ} (hu : Monotone u) (k : ℕ) :
    ∑ i ∈ Finset.range k, eVariationOn G (Set.Icc (u i) (u (i + 1))) =
      eVariationOn G (Set.Icc (u 0) (u k)) := by
  induction k with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Set.Icc_self]
    exact (eVariationOn.subsingleton G Set.subsingleton_singleton).symm
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have := eVariationOn.Icc_add_Icc G (s := Set.univ) (hu (Nat.zero_le k)) (hu (Nat.le_succ k))
      (Set.mem_univ _)
    simpa only [Set.univ_inter] using this

/-- Cochrane (2023), A1 §1.6, p. 567: the right jumps of `G` at the points of a partition sum to
at most the variation of `G`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.sum_abs_jump_le). -/
theorem sum_abs_jump_le {G : ℝ → ℝ} (hG : BoundedVariationOn G Set.univ) (P : Partition a b) :
    ∑ i ∈ Finset.range P.n, |G (P.t (i + 1)) - Function.rightLim G (P.t (i + 1))| ≤
      (eVariationOn G Set.univ).toReal := by
  have hu : Monotone fun i => P.t (i + 1) := fun i j h => P.strictMono.monotone (by omega)
  have hs := sum_eVariationOn_Icc G hu P.n
  calc ∑ i ∈ Finset.range P.n, |G (P.t (i + 1)) - Function.rightLim G (P.t (i + 1))|
      ≤ ∑ i ∈ Finset.range P.n, (eVariationOn G (Set.Icc (P.t (i + 1)) (P.t (i + 1 + 1)))).toReal :=
        Finset.sum_le_sum fun i _ => abs_sub_rightLim_le hG (P.strictMono (Nat.lt_succ_self _))
    _ = (∑ i ∈ Finset.range P.n,
          eVariationOn G (Set.Icc (P.t (i + 1)) (P.t (i + 1 + 1)))).toReal :=
        (ENNReal.toReal_sum fun _ _ => hG.mono (Set.subset_univ _)).symm
    _ = (eVariationOn G (Set.Icc (P.t (0 + 1)) (P.t (P.n + 1)))).toReal := by rw [hs]
    _ ≤ (eVariationOn G Set.univ).toReal :=
        ENNReal.toReal_mono hG (eVariationOn.mono G (Set.subset_univ _))

/-! ## Case (a): continuous integrand, bounded-variation integrator -/

/-- **Cochrane (2023), A1 §1.6, p. 567, quantitative case (a).** Let `g` have bounded variation
on `[a, b]` and `f` be continuous on `[a, b]` with oscillation `≤ ε` over distances `≤ mesh P`.
Then `|Σ f(t_i)Δg_i − ∫_a^b f dg| ≤ 2ε·Var_{[a,b]}(g)`. The jumps of `g` at the partition points
contribute `−Σ (f(t_{i+1}) − f(t_i))(g − g(·+))(t_{i+1})` (`sum_mul_sub_eq`), bounded by
`ε·Var` (`sum_abs_jump_le`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.abs_rsSum_sub_rsInt_le). -/
theorem abs_rsSum_sub_rsInt_le {f g : ℝ → ℝ} (hg : BoundedVariationOn g (Set.Icc a b))
    (hf : ContinuousOn f (Set.Icc a b)) (P : Partition a b) {ε : ℝ} (hε : 0 ≤ ε)
    (hfε : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |x - y| ≤ mesh P → |f x - f y| ≤ ε) :
    |rsSum P f g - rsInt a b f g| ≤ ε * (2 * (eVariationOn g (Set.Icc a b)).toReal) := by
  have hab := a_le_b P
  have hG : BoundedVariationOn (clampFn a b g) Set.univ := bv_clampFn hab hg
  have hfin := isFiniteMeasure_stMeasure a b g
  rw [stMeasure_eq hG] at hfin
  set G := clampFn a b g with hGdef
  set ν := hG.vectorMeasure with hν
  set R := Function.rightLim G with hR
  set V := (eVariationOn g (Set.Icc a b)).toReal with hV
  set c : ℕ → ℝ := fun i => f (P.t i) with hc
  have hint : ν.IntegrableOn f (Set.Icc a b) := rsIntegrable_of_continuousOn hf ν hfin
  have hintIoc : ν.IntegrableOn f (Set.Ioc a b) :=
    hint.mono measurableSet_Icc Set.Ioc_subset_Icc_self
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hf
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC a ⟨le_rfl, hab⟩)
  have hstep : ν.IntegrableOn (stepFn P c) (Set.Ioc a b) :=
    Integrable.of_bound (measurable_stepFn P c).aestronglyMeasurable C
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact abs_stepFn_le P c hC0 (fun i hi => by
          have := hC _ (t_mem P hi.le); rwa [Real.norm_eq_abs] at this) x)
  have h1 : rsInt a b f g = f a * ν {a} + ∫ᵛ x in Set.Ioc a b, f x ∂•ν := by
    rw [rsInt, stMeasure_eq hG]
    exact setIntegral_Icc_eq hab hint
  have h2 := integral_stepFn hG hfin P c
  have h3 : ∫ᵛ x in Set.Ioc a b, (stepFn P c x - f x) ∂•ν =
      ∫ᵛ x in Set.Ioc a b, stepFn P c x ∂•ν - ∫ᵛ x in Set.Ioc a b, f x ∂•ν :=
    VectorMeasure.integral_fun_sub hstep hintIoc
  have h4 : ν {a} = R a - g a := by
    rw [hν, hG.vectorMeasure_singleton, hGdef, leftLim_clampFn_left]
  have hgt : ∀ i ≤ P.n, g (P.t i) = G (P.t i) := fun i hi => (clampFn_of_mem (t_mem P hi)).symm
  have hRb : G (P.t P.n) - R (P.t P.n) = 0 := by
    rw [P.last, hR, hGdef, rightLim_clampFn_right hab, clampFn_of_mem ⟨hab, le_rfl⟩, sub_self]
  have hGa : G a - g a = 0 := by rw [hGdef, clampFn_of_mem ⟨le_rfl, hab⟩, sub_self]
  have habel := sum_mul_sub_eq c (fun i => G (P.t i) - R (P.t i)) P.n
  simp only [hc, P.first] at habel
  have hsplit : rsSum P f g = ∑ i ∈ Finset.range P.n, c i * (R (P.t (i + 1)) - R (P.t i)) +
      ∑ i ∈ Finset.range P.n,
        f (P.t i) * (G (P.t (i + 1)) - R (P.t (i + 1)) - (G (P.t i) - R (P.t i))) := by
    rw [rsSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hgt i (Finset.mem_range.1 hi).le, hgt (i + 1) (Finset.mem_range.1 hi)]
    simp only [hc]
    ring
  set B := ∑ i ∈ Finset.range P.n,
    (f (P.t (i + 1)) - f (P.t i)) * (G (P.t (i + 1)) - R (P.t (i + 1))) with hB
  have key : rsSum P f g - rsInt a b f g =
      ∫ᵛ x in Set.Ioc a b, (stepFn P c x - f x) ∂•ν - B := by
    rw [h3, h2, hsplit, habel, h1, h4]
    linear_combination f (P.t P.n) * hRb - f a * hGa
  -- the two bounds
  have hvar : ν.variation.real (Set.Ioc a b) ≤ V := by
    have := variation_real_le hab hg (Set.Ioc a b)
    rwa [stMeasure_eq hG] at this
  have hI : |∫ᵛ x in Set.Ioc a b, (stepFn P c x - f x) ∂•ν| ≤ ε * V := by
    have hb : ∀ x ∈ Set.Ioc a b, ‖stepFn P c x - f x‖ ≤ ε := by
      intro x hx
      obtain ⟨j, hj, hjx⟩ := exists_piece P hx
      rw [stepFn_eq P c hj hjx, Real.norm_eq_abs]
      refine hfε _ (t_mem P hj.le) _ (Set.Ioc_subset_Icc_self hx) ?_
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hjx.1])]
      linarith [le_mesh P hj, hjx.2]
    have h := VectorMeasure.norm_setIntegral_le_of_norm_le_const (μ := ν) (s := Set.Ioc a b)
      (B := ContinuousLinearMap.lsmul ℝ ℝ) (C := ε) hb
    rw [Real.norm_eq_abs] at h
    have hL : ‖ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_lsmul_le
    have hv0 : 0 ≤ ν.variation.real (Set.Ioc a b) := measureReal_nonneg
    calc _ ≤ ε * ‖ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)‖ * ν.variation.real (Set.Ioc a b) := h
      _ ≤ ε * 1 * V := mul_le_mul (mul_le_mul_of_nonneg_left hL hε) hvar hv0 (by linarith)
      _ = ε * V := by ring
  have hBb : |B| ≤ ε * V := by
    have hj := sum_abs_jump_le hG P
    have hGV : (eVariationOn G Set.univ).toReal ≤ V :=
      ENNReal.toReal_mono hg (eVariationOn_clampFn_le hab g)
    calc |B| ≤ ∑ i ∈ Finset.range P.n,
          |(f (P.t (i + 1)) - f (P.t i)) * (G (P.t (i + 1)) - R (P.t (i + 1)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range P.n, ε * |G (P.t (i + 1)) - R (P.t (i + 1))| := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          refine hfε _ (t_mem P (Finset.mem_range.1 hi)) _ (t_mem P (Finset.mem_range.1 hi).le) ?_
          rw [abs_of_nonneg (by linarith [P.strictMono (Nat.lt_succ_self i)])]
          exact le_mesh P (Finset.mem_range.1 hi)
      _ = ε * ∑ i ∈ Finset.range P.n, |G (P.t (i + 1)) - R (P.t (i + 1))| :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ ε * V := mul_le_mul_of_nonneg_left (hj.trans hGV) hε
  rw [key]
  calc _ ≤ |∫ᵛ x in Set.Ioc a b, (stepFn P c x - f x) ∂•ν| + |B| := abs_sub _ _
    _ ≤ ε * V + ε * V := add_le_add hI hBb
    _ = ε * (2 * V) := by ring

/-- **Cochrane (2023), A1 §1.6, p. 567, case (a): convergence of Riemann–Stieltjes sums.** For
`f` continuous on `[a, b]` and `g` of bounded variation on `[a, b]` (jumps allowed), along ANY
sequence of partitions with mesh → 0, `Σ f(t_i)(g(t_{i+1}) − g(t_i)) → ∫_a^b f dg`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.tendsto_rsSum_of_continuousOn). -/
theorem tendsto_rsSum_of_continuousOn {f g : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    (hg : BoundedVariationOn g (Set.Icc a b)) (P : ℕ → Partition a b)
    (hP : Tendsto (fun k => mesh (P k)) atTop (𝓝 0)) :
    Tendsto (fun k => rsSum (P k) f g) atTop (𝓝 (rsInt a b f g)) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  set V := (eVariationOn g (Set.Icc a b)).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set ε := η / (2 * (2 * V + 1)) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hP δ hδ
  refine ⟨N, fun k hk => ?_⟩
  have hmk : mesh (P k) < δ := by
    have := hN k hk
    rw [Real.dist_eq, sub_zero] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  have hb := abs_rsSum_sub_rsInt_le hg hf (P k) hε.le fun x hx y hy hxy => by
    have := hδf x hx y hy (by rw [Real.dist_eq]; exact lt_of_le_of_lt hxy hmk)
    rw [Real.dist_eq] at this
    exact this.le
  rw [Real.dist_eq]
  refine lt_of_le_of_lt hb ?_
  rw [hεdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

/-! ## Case (b): càdlàg integrand, continuous integrator -/

/-- Cochrane (2023), A1 §1.6, p. 567: for continuous `g` of bounded variation the left-point sum
is the integral of the left-point step function over `(a, b]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.rsSum_eq_integral_stepFn). -/
theorem rsSum_eq_integral_stepFn {g : ℝ → ℝ} (hg : BoundedVariationOn g (Set.Icc a b))
    (hgc : ContinuousOn g (Set.Icc a b)) (P : Partition a b) (c : ℕ → ℝ) :
    ∑ i ∈ Finset.range P.n, c i * (g (P.t (i + 1)) - g (P.t i)) =
      ∫ᵛ x in Set.Ioc a b, stepFn P c x ∂• stMeasure a b g := by
  have hab := a_le_b P
  have hG := bv_clampFn hab hg
  have hfin := isFiniteMeasure_stMeasure a b g
  rw [stMeasure_eq hG] at hfin ⊢
  rw [integral_stepFn hG hfin P c]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(rightLim_clampFn_of_continuousOn hab hgc _).1,
    (rightLim_clampFn_of_continuousOn hab hgc _).1,
    clampFn_of_mem (t_mem P (Finset.mem_range.1 hi)),
    clampFn_of_mem (t_mem P (Finset.mem_range.1 hi).le)]

/-- Cochrane (2023), A1 §1.6, p. 567: **dominated convergence for step functions**: if the step
functions are bounded by `C` and converge on `(a, b]` to `φ`, their integrals against a
finite-variation measure converge to `∫_{(a,b]} φ`.
By Mathlib `VectorMeasure.tendsto_integral_of_dominated_convergence`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.tendsto_integral_stepFn). -/
theorem tendsto_integral_stepFn {ν : VectorMeasure ℝ ℝ} (hν : IsFiniteMeasure ν.variation)
    (P : ℕ → Partition a b) (c : ℕ → ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ k, ∀ i < (P k).n, |c k i| ≤ C) {φ : ℝ → ℝ}
    (hlim : ∀ x ∈ Set.Ioc a b, Tendsto (fun k => stepFn (P k) (c k) x) atTop (𝓝 (φ x))) :
    Tendsto (fun k => ∫ᵛ x in Set.Ioc a b, stepFn (P k) (c k) x ∂•ν) atTop
      (𝓝 (∫ᵛ x in Set.Ioc a b, φ x ∂•ν)) := by
  refine VectorMeasure.tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun k => (measurable_stepFn (P k) (c k)).aestronglyMeasurable) (integrable_const C)
    (fun k => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact abs_stepFn_le (P k) (c k) hC (hc k) x) ?_
  rw [VectorMeasure.variation_restrict measurableSet_Ioc]
  exact ae_restrict_of_forall_mem measurableSet_Ioc hlim

/-- Cochrane (2023), A1 §1.6, p. 567: as the mesh → 0 the left-point step function of `f`
converges at `x ∈ (a, b]` to the left limit of `f` at `x`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.tendsto_stepFn_left). -/
theorem tendsto_stepFn_left (P : ℕ → Partition a b)
    (hP : Tendsto (fun k => mesh (P k)) atTop (𝓝 0)) {f : ℝ → ℝ} {x L : ℝ}
    (hx : x ∈ Set.Ioc a b) (hf : Tendsto f (𝓝[<] x) (𝓝 L)) :
    Tendsto (fun k => stepFn (P k) (fun i => f ((P k).t i)) x) atTop (𝓝 L) := by
  choose j hj hjx using fun k => exists_piece (P k) hx
  have heq : ∀ k, f ((P k).t (j k)) = stepFn (P k) (fun i => f ((P k).t i)) x :=
    fun k => (stepFn_eq (P k) (fun i => f ((P k).t i)) (hj k) (hjx k)).symm
  refine (tendsto_congr heq).1 (hf.comp (tendsto_nhdsWithin_iff.2
    ⟨?_, Eventually.of_forall fun k => (hjx k).1⟩))
  have hlow : ∀ k, x - mesh (P k) ≤ (P k).t (j k) := fun k => by
    linarith [le_mesh (P k) (hj k), (hjx k).2]
  have h1 : Tendsto (fun k => x - mesh (P k)) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.sub hP
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds hlow
    fun k => (hjx k).1.le

/-- Cochrane (2023), A1 §1.6, p. 567: as the mesh → 0 the right-point step function of `f`
converges at `x ∈ (a, b]` to the limit of `f` from the right (including `x`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.tendsto_stepFn_right). -/
theorem tendsto_stepFn_right (P : ℕ → Partition a b)
    (hP : Tendsto (fun k => mesh (P k)) atTop (𝓝 0)) {f : ℝ → ℝ} {x L : ℝ}
    (hx : x ∈ Set.Ioc a b) (hf : Tendsto f (𝓝[≥] x) (𝓝 L)) :
    Tendsto (fun k => stepFn (P k) (fun i => f ((P k).t (i + 1))) x) atTop (𝓝 L) := by
  choose j hj hjx using fun k => exists_piece (P k) hx
  have heq : ∀ k, f ((P k).t (j k + 1)) = stepFn (P k) (fun i => f ((P k).t (i + 1))) x :=
    fun k => (stepFn_eq (P k) (fun i => f ((P k).t (i + 1))) (hj k) (hjx k)).symm
  refine (tendsto_congr heq).1 (hf.comp (tendsto_nhdsWithin_iff.2
    ⟨?_, Eventually.of_forall fun k => (hjx k).2⟩))
  have hup : ∀ k, (P k).t (j k + 1) ≤ x + mesh (P k) := fun k => by
    linarith [le_mesh (P k) (hj k), (hjx k).1]
  have h1 : Tendsto (fun k => x + mesh (P k)) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.add hP
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun k => (hjx k).2) hup

/-- Cochrane (2023), A1 §1.6, p. 567: for `g` continuous of bounded variation and `f` càdlàg,
`∫_a^b f dg = ∫_{(a,b]} f(t−) dg`: `g` has no atoms and `f = f(·−)` off the countable set of
jumps of `f`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.rsInt_eq_Ioc_leftLim). -/
theorem rsInt_eq_Ioc_leftLim {f g : ℝ → ℝ} (hab : a ≤ b) (hf : IsCadlag f)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hgc : ContinuousOn g (Set.Icc a b)) :
    rsInt a b f g = ∫ᵛ x in Set.Ioc a b, Function.leftLim f x ∂• stMeasure a b g := by
  have hns : NullSingletonClass (stMeasure a b g).variation :=
    ⟨stMeasure_singleton_of_continuousOn hab hg hgc⟩
  have hnull := (countable_jumps hf).measure_zero (stMeasure a b g).variation
  rw [rsInt, VectorMeasure.setIntegral_congr_set measurableSet_Icc measurableSet_Ioc ?_]
  · refine VectorMeasure.setIntegral_congr_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx _
    exact not_not.1 hx
  · rw [ae_eq_set]
    constructor
    · refine measure_mono_null (fun x hx => ?_) (stMeasure_singleton_of_continuousOn hab hg hgc a)
      exact le_antisymm (not_lt.1 fun h => hx.2 ⟨h, hx.1.2⟩) hx.1.1
    · exact measure_mono_null (fun x hx => absurd (Set.Ioc_subset_Icc_self hx.1) hx.2)
        (measure_empty (μ := (stMeasure a b g).variation))

/-- Cochrane (2023), A1 §1.6, p. 567: **in case (b) the integral of `f` equals the integral of
its left limits**, `∫_a^b f dg = ∫_a^b f(t−) dg`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.rsInt_eq_rsInt_leftLim). -/
theorem rsInt_eq_rsInt_leftLim {f g : ℝ → ℝ} (hab : a ≤ b) (hf : IsCadlag f)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hgc : ContinuousOn g (Set.Icc a b)) :
    rsInt a b f g = rsInt a b (Function.leftLim f) g := by
  have hns : NullSingletonClass (stMeasure a b g).variation :=
    ⟨stMeasure_singleton_of_continuousOn hab hg hgc⟩
  have hnull := (countable_jumps hf).measure_zero (stMeasure a b g).variation
  refine VectorMeasure.setIntegral_congr_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx _
  exact not_not.1 hx

/-- **Cochrane (2023), A1 §1.6, p. 567, case (b): convergence of Riemann–Stieltjes sums.** For
`f` càdlàg (right-continuous with left limits, hence bounded on `[a, b]`) and `g` continuous of
bounded variation on `[a, b]`, along ANY sequence of partitions with mesh → 0,
`Σ f(t_i)(g(t_{i+1}) − g(t_i)) → ∫_a^b f dg` (`= ∫_a^b f(t−) dg`, `rsInt_eq_rsInt_leftLim`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.tendsto_rsSum_of_isCadlag). -/
theorem tendsto_rsSum_of_isCadlag {f g : ℝ → ℝ} (hf : IsCadlag f)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hgc : ContinuousOn g (Set.Icc a b))
    (P : ℕ → Partition a b) (hP : Tendsto (fun k => mesh (P k)) atTop (𝓝 0)) :
    Tendsto (fun k => rsSum (P k) f g) atTop (𝓝 (rsInt a b f g)) := by
  have hab := a_le_b (P 0)
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_isCadlag hf a b
  have e : ∀ k, ∫ᵛ x in Set.Ioc a b, stepFn (P k) (fun i => f ((P k).t i)) x ∂• stMeasure a b g =
      rsSum (P k) f g := fun k =>
    (rsSum_eq_integral_stepFn hg hgc (P k) fun i => f ((P k).t i)).symm
  rw [rsInt_eq_Ioc_leftLim hab hf hg hgc]
  refine (tendsto_congr e).1 (tendsto_integral_stepFn (isFiniteMeasure_stMeasure a b g) P
    (fun k i => f ((P k).t i)) hC0 (fun k i hi => hC _ (t_mem (P k) hi.le)) fun x hx => ?_)
  exact tendsto_stepFn_left P hP hx (hf.tendsto_nhdsLT_leftLim x)

/-! ## The cross sum -/

/-- **Cochrane (2023), A1 §1.6, p. 567: the cross sum vanishes.** For `f` càdlàg (not
necessarily of bounded variation) and `g` continuous of bounded variation on `[a, b]`, along ANY
sequence of partitions with mesh → 0, `Σ (f(t_{i+1}) − f(t_i))(g(t_{i+1}) − g(t_i)) → 0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.tendsto_crossSum_zero). -/
theorem tendsto_crossSum_zero {f g : ℝ → ℝ} (hf : IsCadlag f)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hgc : ContinuousOn g (Set.Icc a b))
    (P : ℕ → Partition a b) (hP : Tendsto (fun k => mesh (P k)) atTop (𝓝 0)) :
    Tendsto (fun k => crossSum (P k) f g) atTop (𝓝 0) := by
  have hab := a_le_b (P 0)
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_isCadlag hf a b
  have hfin := isFiniteMeasure_stMeasure a b g
  have e : ∀ k,
      ∫ᵛ x in Set.Ioc a b, stepFn (P k) (fun i => f ((P k).t (i + 1))) x ∂• stMeasure a b g -
        ∫ᵛ x in Set.Ioc a b, stepFn (P k) (fun i => f ((P k).t i)) x ∂• stMeasure a b g =
      crossSum (P k) f g := by
    intro k
    rw [← rsSum_eq_integral_stepFn hg hgc, ← rsSum_eq_integral_stepFn hg hgc, crossSum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hR := tendsto_integral_stepFn hfin P (fun k i => f ((P k).t (i + 1))) hC0
    (fun k i hi => hC _ (t_mem (P k) hi)) (φ := f) fun x hx =>
      tendsto_stepFn_right P hP hx
        (continuousWithinAt_Ioi_iff_Ici.1 (hf.isRightContinuous x)).tendsto
  have hL := tendsto_integral_stepFn hfin P (fun k i => f ((P k).t i)) hC0
    (fun k i hi => hC _ (t_mem (P k) hi.le)) (φ := Function.leftLim f) fun x hx =>
      tendsto_stepFn_left P hP hx (hf.tendsto_nhdsLT_leftLim x)
  have h := hR.sub hL
  have heq : ∫ᵛ x in Set.Ioc a b, f x ∂• stMeasure a b g =
      ∫ᵛ x in Set.Ioc a b, Function.leftLim f x ∂• stMeasure a b g := by
    have hns : NullSingletonClass (stMeasure a b g).variation :=
      ⟨stMeasure_singleton_of_continuousOn hab hg hgc⟩
    have hnull := (countable_jumps hf).measure_zero (stMeasure a b g).variation
    refine VectorMeasure.setIntegral_congr_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx _
    exact not_not.1 hx
  rw [heq, sub_self] at h
  exact (tendsto_congr e).1 h

/-- Cochrane (2023), A1 §1.6, p. 567: the Heaviside step `1_{[1, ∞)}` (right-continuous).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.heaviside). -/
noncomputable def heaviside (x : ℝ) : ℝ := if 1 ≤ x then 1 else 0

/-- Cochrane (2023), A1 §1.6, p. 567: the Heaviside step is càdlàg.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.isCadlag_heaviside). -/
theorem isCadlag_heaviside : IsCadlag heaviside := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rcases le_or_gt 1 x with hx | hx
    · refine (continuousWithinAt_const (b := (1 : ℝ))).congr (fun y hy => ?_) ?_
      · simp only [heaviside, hx.trans (le_of_lt hy), ↓reduceIte]
      · simp only [heaviside, hx, ↓reduceIte]
    · refine (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [Ioo_mem_nhdsGT hx] with y hy
        simp only [heaviside, not_le.2 hy.2, ↓reduceIte]
      · simp only [heaviside, not_le.2 hx, ↓reduceIte]
  · rcases le_or_gt x 1 with hx | hx
    · refine ⟨0, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with y hy
      simp only [heaviside, not_le.2 (lt_of_lt_of_le hy hx), ↓reduceIte]
    · refine ⟨1, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [Ioo_mem_nhdsLT hx] with y hy
      simp only [heaviside, hy.1.le, ↓reduceIte]

/-- Cochrane (2023), A1 §1.6, p. 567: the Heaviside step is monotone, hence of bounded variation
on `[0, 2]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.bv_heaviside). -/
theorem bv_heaviside : BoundedVariationOn heaviside (Set.Icc 0 2) := by
  have hm : Monotone heaviside := by
    intro x y hxy
    simp only [heaviside]
    split_ifs <;> first | (exfalso; linarith) | norm_num
  refine (hm.monotoneOn _).boundedVariationOn (C := 1) fun x _ => ?_
  simp only [heaviside]
  split_ifs <;> norm_num

/-- **Cochrane (2023), A1 §1.6, p. 567: continuity of `g` is needed in `tendsto_crossSum_zero`.**
With `f = g = 1_{[1,∞)}` on `[0, 2]` (both càdlàg and of bounded variation, `g` jumping where `f`
jumps), the cross sum `Σ (Δf_i)(Δg_i) = Σ (Δf_i)² = Σ Δf_i = 1` for EVERY partition.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.crossSum_heaviside). -/
theorem crossSum_heaviside (P : Partition 0 2) : crossSum P heaviside heaviside = 1 := by
  have hsq : ∀ i, (heaviside (P.t (i + 1)) - heaviside (P.t i)) *
      (heaviside (P.t (i + 1)) - heaviside (P.t i)) =
      heaviside (P.t (i + 1)) - heaviside (P.t i) := by
    intro i
    have hlt := P.strictMono (show i < i + 1 by omega)
    simp only [heaviside]
    split_ifs <;> first | (exfalso; linarith) | ring
  have ht := Finset.sum_range_sub (fun i => heaviside (P.t i)) P.n
  rw [crossSum, Finset.sum_congr rfl fun i _ => hsq i, ht, P.last, P.first]
  norm_num [heaviside]

/-- Cochrane (2023), A1 §1.6, p. 567: hence along any partitions of `[0, 2]` the cross sum of
`1_{[1,∞)}` with itself does NOT tend to `0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.not_tendsto_crossSum_heaviside). -/
theorem not_tendsto_crossSum_heaviside (P : ℕ → Partition 0 2) :
    ¬ Tendsto (fun k => crossSum (P k) heaviside heaviside) atTop (𝓝 0) := by
  intro h
  simp only [crossSum_heaviside] at h
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)

/-! ## Dyadic partitions -/

/-- Cochrane (2023), A1 §1.6, p. 567: the `k`-th dyadic partition `t_i = a + (b − a)i/2^k`,
`i ≤ 2^k`, of `[a, b]`, `a < b`.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7StieltjesSums.dyadic). -/
noncomputable def dyadic (hab : a < b) (k : ℕ) : Partition a b where
  n := 2 ^ k
  t := fun i => a + (b - a) * i / 2 ^ k
  strictMono := by
    intro i j hij
    have h2 : (0 : ℝ) < 2 ^ k := by positivity
    simp only
    have : (b - a) * (i : ℝ) < (b - a) * j :=
      mul_lt_mul_of_pos_left (Nat.cast_lt.2 hij) (sub_pos.2 hab)
    linarith [div_lt_div_of_pos_right this h2]
  first := by simp
  last := by
    push_cast
    field_simp
    ring

/-- Cochrane (2023), A1 §1.6, p. 567: the mesh of the `k`-th dyadic partition is
`(b − a)/2^k`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.mesh_dyadic). -/
theorem mesh_dyadic (hab : a < b) (k : ℕ) : mesh (dyadic hab k) = (b - a) / 2 ^ k := by
  have hne : Nonempty (Fin (dyadic hab k).n) := ⟨⟨0, by simp [dyadic]⟩⟩
  have e : ∀ i : Fin (dyadic hab k).n,
      (dyadic hab k).t ((i : ℕ) + 1) - (dyadic hab k).t i = (b - a) / 2 ^ k := by
    intro i
    simp only [dyadic]
    push_cast
    ring
  simp only [mesh, e, ciSup_const]

/-- Cochrane (2023), A1 §1.6, p. 567: the mesh of the dyadic partitions tends to `0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.tendsto_mesh_dyadic). -/
theorem tendsto_mesh_dyadic (hab : a < b) :
    Tendsto (fun k => mesh (dyadic hab k)) atTop (𝓝 0) := by
  simp only [mesh_dyadic]
  exact tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- Cochrane (2023), A1 §1.6, p. 567: case (a) along the dyadic partitions.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.tendsto_rsSum_dyadic_of_continuousOn). -/
theorem tendsto_rsSum_dyadic_of_continuousOn {f g : ℝ → ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : BoundedVariationOn g (Set.Icc a b)) :
    Tendsto (fun k => rsSum (dyadic hab k) f g) atTop (𝓝 (rsInt a b f g)) :=
  tendsto_rsSum_of_continuousOn hf hg _ (tendsto_mesh_dyadic hab)

/-- Cochrane (2023), A1 §1.6, p. 567: case (b) along the dyadic partitions.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.tendsto_rsSum_dyadic_of_isCadlag). -/
theorem tendsto_rsSum_dyadic_of_isCadlag {f g : ℝ → ℝ} (hab : a < b) (hf : IsCadlag f)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hgc : ContinuousOn g (Set.Icc a b)) :
    Tendsto (fun k => rsSum (dyadic hab k) f g) atTop (𝓝 (rsInt a b f g)) :=
  tendsto_rsSum_of_isCadlag hf hg hgc _ (tendsto_mesh_dyadic hab)

/-- Cochrane (2023), A1 §1.6, p. 567: the cross sum vanishes along the dyadic partitions.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesSums.tendsto_crossSum_dyadic). -/
theorem tendsto_crossSum_dyadic {f g : ℝ → ℝ} (hab : a < b) (hf : IsCadlag f)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hgc : ContinuousOn g (Set.Icc a b)) :
    Tendsto (fun k => crossSum (dyadic hab k) f g) atTop (𝓝 0) :=
  tendsto_crossSum_zero hf hg hgc _ (tendsto_mesh_dyadic hab)

end Cochrane.ZeroBound.TidyR7StieltjesSums
