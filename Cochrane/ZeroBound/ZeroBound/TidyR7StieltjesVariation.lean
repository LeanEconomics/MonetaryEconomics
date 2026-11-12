/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR7StieltjesSums

/-!
# Measurability of the variation of a random path, and the degenerate interval

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). The product step in (1.32),
`Λ/P · dB + E_t d(Λ/P)·B = E_t d(ΛB/P)`, passes to the limit in the Riemann–Stieltjes sums under a
conditional expectation; the sums are dominated by `C(ω)·Var_{[a,b]}(g(ω, ·))`
(`TidyR7StieltjesCalculus.abs_rsSum_le`). These are deterministic Riemann–Stieltjes tools for that
(1.32) product step: the dominating variation is measurable in `ω`.

## Main results

* `eVariationOn_Icc_eq_denseSet`: for `g` right-continuous on `[a, b]` (within `[x, b]` at each
  `x`), the variation over `[a, b]` equals the variation over the countable set `denseSet a b`
  (rationals of `[a, b]` together with `b`). Each point is pushed to the next dyadic point to its
  right (`dyadicUp`), monotonically, and right-continuity passes to the limit.
* `measurable_eVariationOn_countable`: over a countable set the variation is a countable supremum
  of measurable finite sums.
* `measurable_eVariationOn`, `measurable_variation_toReal`: `ω ↦ Var_{[a,b]}(g(ω, ·))` (and its
  `toReal`) is measurable if each `g(·, t)` is measurable and each path is right-continuous on
  `[a, b]`; corollaries for càdlàg paths (`measurable_eVariationOn_of_isCadlag`) and paths
  continuous on `[a, b]` (`measurable_eVariationOn_of_continuousOn`).
* The degenerate interval: `eVariationOn_Icc_self`, `rsInt_self`, `partition_self_n`,
  `rsSum_self`, `crossSum_self`.
-/

namespace Cochrane.ZeroBound.TidyR7StieltjesVariation

open MeasureTheory Filter Topology
open Cochrane.ZeroBound.TidyR7StieltjesIntegral Cochrane.ZeroBound.TidyR7StieltjesSums

/-! ## Pushing points to the right onto a countable set -/

/-- Cochrane (2023), A1 §1.6, p. 567: the countable set of rationals of `[a, b]`, with `b`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.denseSet). -/
def denseSet (a b : ℝ) : Set ℝ := {y | y ∈ Set.Icc a b ∧ (y = b ∨ ∃ q : ℚ, (q : ℝ) = y)}

/-- Cochrane (2023), A1 §1.6, p. 567: `denseSet a b` is countable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.countable_denseSet). -/
theorem countable_denseSet (a b : ℝ) : (denseSet a b).Countable := by
  refine ((Set.countable_range (fun q : ℚ => (q : ℝ))).insert b).mono fun y hy => ?_
  rcases hy.2 with h | ⟨q, hq⟩
  · exact Or.inl h
  · exact Or.inr ⟨q, hq⟩

/-- Cochrane (2023), A1 §1.6, p. 567: the first dyadic point of level `k` strictly right of `x`,
`(⌊2^k x⌋ + 1)/2^k`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.dyadicUp). -/
noncomputable def dyadicUp (k : ℕ) (x : ℝ) : ℝ := ((⌊x * 2 ^ k⌋ : ℝ) + 1) / 2 ^ k

/-- Cochrane (2023), A1 §1.6, p. 567: `x < dyadicUp k x ≤ x + 1/2^k`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.dyadicUp_bounds). -/
theorem dyadicUp_bounds (k : ℕ) (x : ℝ) : x < dyadicUp k x ∧ dyadicUp k x ≤ x + 1 / 2 ^ k := by
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have h1 := Int.lt_floor_add_one (x * 2 ^ k)
  have h3 := Int.floor_le (x * 2 ^ k)
  constructor
  · rw [dyadicUp, lt_div_iff₀ h2]
    linarith
  · rw [dyadicUp, div_le_iff₀ h2, add_mul, div_mul_cancel₀ _ h2.ne']
    linarith

/-- Cochrane (2023), A1 §1.6, p. 567: `dyadicUp k` is monotone.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.dyadicUp_mono). -/
theorem dyadicUp_mono (k : ℕ) : Monotone (dyadicUp k) := by
  intro x y hxy
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have := Int.floor_mono (mul_le_mul_of_nonneg_right hxy h2.le)
  have h' : (⌊x * 2 ^ k⌋ : ℝ) ≤ ⌊y * 2 ^ k⌋ := Int.cast_le.2 this
  exact div_le_div_of_nonneg_right (by linarith) h2.le

/-- Cochrane (2023), A1 §1.6, p. 567: `dyadicUp k x` is rational.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.dyadicUp_rat). -/
theorem dyadicUp_rat (k : ℕ) (x : ℝ) : ∃ q : ℚ, (q : ℝ) = dyadicUp k x :=
  ⟨((⌊x * 2 ^ k⌋ : ℚ) + 1) / 2 ^ k, by rw [dyadicUp]; push_cast; ring⟩

/-- Cochrane (2023), A1 §1.6, p. 567: the push of `x ∈ [a, b]` to the right, capped at `b`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.pushRight). -/
noncomputable def pushRight (b : ℝ) (k : ℕ) (x : ℝ) : ℝ := min (dyadicUp k x) b

/-- Cochrane (2023), A1 §1.6, p. 567: the push lies in `[x, b]` and in `denseSet a b`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.pushRight_mem). -/
theorem pushRight_mem {a b x : ℝ} (hx : x ∈ Set.Icc a b) (k : ℕ) :
    pushRight b k x ∈ Set.Icc x b ∧ pushRight b k x ∈ denseSet a b := by
  have h1 : pushRight b k x ∈ Set.Icc x b :=
    ⟨le_min (dyadicUp_bounds k x).1.le hx.2, min_le_right _ _⟩
  refine ⟨h1, ⟨hx.1.trans h1.1, h1.2⟩, ?_⟩
  rcases le_total (dyadicUp k x) b with h | h
  · rw [pushRight, min_eq_left h]
    exact Or.inr (dyadicUp_rat k x)
  · rw [pushRight, min_eq_right h]
    exact Or.inl rfl

/-- Cochrane (2023), A1 §1.6, p. 567: the push is monotone.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.pushRight_mono). -/
theorem pushRight_mono (b : ℝ) (k : ℕ) : Monotone (pushRight b k) :=
  fun _ _ h => min_le_min (dyadicUp_mono k h) le_rfl

/-- Cochrane (2023), A1 §1.6, p. 567: the push of `x ∈ [a, b]` tends to `x` within `[x, b]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.tendsto_pushRight). -/
theorem tendsto_pushRight {a b x : ℝ} (hx : x ∈ Set.Icc a b) :
    Tendsto (fun k => pushRight b k x) atTop (𝓝[Set.Icc x b] x) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => (pushRight_mem hx k).1⟩
  have hup : Tendsto (fun k : ℕ => x + 1 / (2 : ℝ) ^ k) atTop (𝓝 x) := by
    have h0 : Tendsto (fun k : ℕ => (1 : ℝ) / 2 ^ k) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    simpa using (tendsto_const_nhds (x := x)).add h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun k => (pushRight_mem hx k).1.1)
    (fun k => (min_le_left _ _).trans (dyadicUp_bounds k x).2)

/-- **Cochrane (2023), A1 §1.6, p. 567: the variation of a right-continuous path is a supremum
over a countable set.** If `g` is right-continuous on `[a, b]` (within `[x, b]` at each
`x ∈ [a, b]`), then `Var_{[a,b]}(g) = Var_{denseSet a b}(g)`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.eVariationOn_Icc_eq_denseSet). -/
theorem eVariationOn_Icc_eq_denseSet {a b : ℝ} {g : ℝ → ℝ}
    (hr : ∀ x ∈ Set.Icc a b, ContinuousWithinAt g (Set.Icc x b) x) :
    eVariationOn g (Set.Icc a b) = eVariationOn g (denseSet a b) := by
  refine le_antisymm (iSup_le fun p => ?_) (eVariationOn.mono g fun y hy => hy.1)
  have hbound : ∀ k, ∑ i ∈ Finset.range p.1,
      edist (g (pushRight b k (p.2.1 (i + 1)))) (g (pushRight b k (p.2.1 i))) ≤
        eVariationOn g (denseSet a b) := fun k =>
    eVariationOn.sum_le (u := fun i => pushRight b k (p.2.1 i))
      ((pushRight_mono b k).comp p.2.2.1) fun i => (pushRight_mem (p.2.2.2 i) k).2
  have hpt : ∀ j, Tendsto (fun k => g (pushRight b k (p.2.1 j))) atTop (𝓝 (g (p.2.1 j))) :=
    fun j => (hr _ (p.2.2.2 j)).tendsto.comp (tendsto_pushRight (p.2.2.2 j))
  exact le_of_tendsto' (tendsto_finsetSum _ fun i _ => (hpt (i + 1)).edist (hpt i)) hbound

/-! ## Countable suprema -/

/-- Cochrane (2023), A1 §1.6, p. 567: the points `v_0, …, v_n` of a finite family, extended by
`v_n` to all of `ℕ`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.extFin). -/
def extFin {S : Set ℝ} (n : ℕ) (v : Fin (n + 1) → S) (i : ℕ) : ℝ :=
  v ⟨min i n, Nat.lt_succ_of_le (min_le_right i n)⟩

/-- Cochrane (2023), A1 §1.6, p. 567: the variation over `S` as a supremum over finite families of
points of `S` (a countable index set when `S` is countable).
A reindexing of the definition of Mathlib `eVariationOn`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.eVariationOn_eq_iSup_fin). -/
theorem eVariationOn_eq_iSup_fin (g : ℝ → ℝ) (S : Set ℝ) :
    eVariationOn g S = ⨆ p : Σ n : ℕ, (Fin (n + 1) → S),
      @ite _ (Monotone (extFin p.1 p.2)) (Classical.dec _)
        (∑ i ∈ Finset.range p.1, edist (g (extFin p.1 p.2 (i + 1))) (g (extFin p.1 p.2 i))) 0 := by
  refine le_antisymm (iSup_le fun p => ?_) (iSup_le fun q => ?_)
  · let v : Fin (p.1 + 1) → S := fun j => ⟨p.2.1 j, p.2.2.2 j⟩
    have hv : ∀ i, extFin p.1 v i = p.2.1 (min i p.1) := fun _ => rfl
    have hm : Monotone (extFin p.1 v) := by
      intro i j hij
      rw [hv, hv]
      exact p.2.2.1 (min_le_min_right _ hij)
    refine le_iSup_of_le ⟨p.1, v⟩ ?_
    simp only [hm, ↓reduceIte]
    refine le_of_eq (Finset.sum_congr rfl fun i hi => ?_)
    have hi' := Finset.mem_range.1 hi
    rw [hv, hv, min_eq_left hi'.le, min_eq_left hi']
  · by_cases hm : Monotone (extFin q.1 q.2)
    · simp only [hm, ↓reduceIte]
      exact eVariationOn.sum_le hm fun i => (q.2 _).2
    · simp only [hm, ↓reduceIte]
      exact bot_le

/-- Cochrane (2023), A1 §1.6, p. 567: **over a countable set the variation of a random path is
measurable** when each `g(·, t)` is measurable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.measurable_eVariationOn_countable). -/
theorem measurable_eVariationOn_countable {Ω : Type*} [MeasurableSpace Ω] {g : Ω → ℝ → ℝ}
    {S : Set ℝ} (hS : S.Countable) (hg : ∀ t, Measurable fun ω => g ω t) :
    Measurable fun ω => eVariationOn (g ω) S := by
  have := hS.to_subtype
  simp only [eVariationOn_eq_iSup_fin]
  refine Measurable.iSup fun q => ?_
  by_cases hm : Monotone (extFin q.1 q.2)
  · simp only [hm, ↓reduceIte]
    exact Finset.measurable_sum _ fun i _ => (hg _).edist (hg _)
  · simp only [hm, ↓reduceIte]
    exact measurable_const

/-! ## The variation of a random right-continuous path -/

/-- **Cochrane (2023), A1 §1.6, p. 567: `ω ↦ Var_{[a,b]}(g(ω, ·))` is measurable** if each
`g(·, t)` is measurable and each path `g(ω, ·)` is right-continuous on `[a, b]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.measurable_eVariationOn). -/
theorem measurable_eVariationOn {a b : ℝ} {Ω : Type*} [MeasurableSpace Ω] {g : Ω → ℝ → ℝ}
    (hg : ∀ t, Measurable fun ω => g ω t)
    (hr : ∀ ω, ∀ x ∈ Set.Icc a b, ContinuousWithinAt (g ω) (Set.Icc x b) x) :
    Measurable fun ω => eVariationOn (g ω) (Set.Icc a b) := by
  have e : (fun ω => eVariationOn (g ω) (Set.Icc a b)) =
      fun ω => eVariationOn (g ω) (denseSet a b) :=
    funext fun ω => eVariationOn_Icc_eq_denseSet (hr ω)
  rw [e]
  exact measurable_eVariationOn_countable (countable_denseSet a b) hg

/-- Cochrane (2023), A1 §1.6, p. 567: the real variation `ω ↦ Var_{[a,b]}(g(ω, ·)).toReal` is
measurable under the hypotheses of `measurable_eVariationOn` (it is the variation itself when
the paths have bounded variation).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.measurable_variation_toReal). -/
theorem measurable_variation_toReal {a b : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Ω → ℝ → ℝ} (hg : ∀ t, Measurable fun ω => g ω t)
    (hr : ∀ ω, ∀ x ∈ Set.Icc a b, ContinuousWithinAt (g ω) (Set.Icc x b) x) :
    Measurable fun ω => (eVariationOn (g ω) (Set.Icc a b)).toReal :=
  (measurable_eVariationOn hg hr).ennreal_toReal

/-- Cochrane (2023), A1 §1.6, p. 567: measurability of the variation for càdlàg paths.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.measurable_eVariationOn_of_isCadlag). -/
theorem measurable_eVariationOn_of_isCadlag {a b : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Ω → ℝ → ℝ} (hg : ∀ t, Measurable fun ω => g ω t) (hc : ∀ ω, IsCadlag (g ω)) :
    Measurable fun ω => eVariationOn (g ω) (Set.Icc a b) :=
  measurable_eVariationOn hg fun ω x _ =>
    (continuousWithinAt_Ioi_iff_Ici.1 ((hc ω).isRightContinuous x)).mono Set.Icc_subset_Ici_self

/-- Cochrane (2023), A1 §1.6, p. 567: measurability of the variation for paths continuous on
`[a, b]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.measurable_eVariationOn_of_continuousOn). -/
theorem measurable_eVariationOn_of_continuousOn {a b : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Ω → ℝ → ℝ} (hg : ∀ t, Measurable fun ω => g ω t)
    (hc : ∀ ω, ContinuousOn (g ω) (Set.Icc a b)) :
    Measurable fun ω => eVariationOn (g ω) (Set.Icc a b) :=
  measurable_eVariationOn hg fun ω x hx =>
    ((hc ω) x hx).mono (Set.Icc_subset_Icc_left hx.1)

/-- Cochrane (2023), A1 §1.6, p. 567: real-valued form for càdlàg paths.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.measurable_variation_toReal_of_isCadlag). -/
theorem measurable_variation_toReal_of_isCadlag {a b : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Ω → ℝ → ℝ} (hg : ∀ t, Measurable fun ω => g ω t) (hc : ∀ ω, IsCadlag (g ω)) :
    Measurable fun ω => (eVariationOn (g ω) (Set.Icc a b)).toReal :=
  (measurable_eVariationOn_of_isCadlag hg hc).ennreal_toReal

/-- Cochrane (2023), A1 §1.6, p. 567: real-valued form for paths continuous on `[a, b]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.measurable_variation_toReal_of_continuousOn). -/
theorem measurable_variation_toReal_of_continuousOn {a b : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Ω → ℝ → ℝ} (hg : ∀ t, Measurable fun ω => g ω t)
    (hc : ∀ ω, ContinuousOn (g ω) (Set.Icc a b)) :
    Measurable fun ω => (eVariationOn (g ω) (Set.Icc a b)).toReal :=
  (measurable_eVariationOn_of_continuousOn hg hc).ennreal_toReal

/-! ## The degenerate interval `a = b` -/

/-- Cochrane (2023), A1 §1.6, p. 567: `Var_{[a,a]}(g) = 0`.
A special case of Mathlib `eVariationOn.subsingleton`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.eVariationOn_Icc_self). -/
theorem eVariationOn_Icc_self (g : ℝ → ℝ) (a : ℝ) : eVariationOn g (Set.Icc a a) = 0 := by
  rw [Set.Icc_self]
  exact eVariationOn.subsingleton g Set.subsingleton_singleton

/-- Cochrane (2023), A1 §1.6, p. 567: `∫_a^a f dg = 0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.rsInt_self). -/
theorem rsInt_self (f g : ℝ → ℝ) (a : ℝ) : rsInt a a f g = 0 := by
  have hbv : BoundedVariationOn g (Set.Icc a a) := by
    rw [BoundedVariationOn, eVariationOn_Icc_self]
    exact ENNReal.zero_ne_top
  have h := abs_rsInt_le (C := |f a|) le_rfl hbv fun x hx => by rw [le_antisymm hx.2 hx.1]
  rw [eVariationOn_Icc_self] at h
  simpa using h

/-- Cochrane (2023), A1 §1.6, p. 567: a partition of `[a, a]` has no steps.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.partition_self_n). -/
theorem partition_self_n {a : ℝ} (P : Partition a a) : P.n = 0 := by
  by_contra h
  have := P.strictMono (Nat.pos_of_ne_zero h)
  rw [P.first, P.last] at this
  exact lt_irrefl _ this

/-- Cochrane (2023), A1 §1.6, p. 567: on `[a, a]` every Riemann–Stieltjes sum is `0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.rsSum_self). -/
theorem rsSum_self {a : ℝ} (P : Partition a a) (f g : ℝ → ℝ) : rsSum P f g = 0 := by
  simp [rsSum, partition_self_n P]

/-- Cochrane (2023), A1 §1.6, p. 567: on `[a, a]` every cross sum is `0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesVariation.crossSum_self). -/
theorem crossSum_self {a : ℝ} (P : Partition a a) (f g : ℝ → ℝ) : crossSum P f g = 0 := by
  simp [crossSum, partition_self_n P]

end Cochrane.ZeroBound.TidyR7StieltjesVariation
