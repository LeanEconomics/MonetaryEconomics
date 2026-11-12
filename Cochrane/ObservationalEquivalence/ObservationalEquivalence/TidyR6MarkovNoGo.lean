/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.TidyR6MarkovAbstractN
import Mathlib.Data.Set.Card

/-!
# No pointwise-linear expectation system carries a non-degenerate Markov regime

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 24, §24.2, pp. 522–523 (Markov
switching "with exactly two (or even N) states", p. 523).

An `ExpectationSystem` forecasts every function `Ω → ℝ`. A forecast `E_0(·)(ω)` is
*pointwise-linear* (`PointwiseLinearAt`) when it is a finite linear combination of values,
`E_0 x(ω) = ∑_{z ∈ F} c_z x(z)` with `F` finite. This module proves that such a forecast is
incompatible with a known Markov regime whose transitions are non-degenerate, and that on a
countable state space every forecast is pointwise-linear.

## Main results

* `not_pointwiseLinear` (**the no-go**): if `S` is a Markov regime that is known at each date
  (`RegimeAdapted`) and every row of `P` has two positive entries (`Nondegenerate`), then no
  date-`0` forecast is pointwise-linear. The forecast must give positive weight, inside its
  finite support, to ever more distinct regime histories (`card_hist_ge`).
* `pointwiseLinear_of_finite`: on a finite state space every forecast is pointwise-linear;
  `pointwiseLinear_of_countable`: so is every forecast on a countable state space (a positive
  linear functional on all functions of a countable set is a finite combination of evaluations:
  `finite_support`, `vanish_of_support`).
* `countable_no_regime`: no expectation system on a countable state space carries a known,
  non-degenerate Markov regime; `countable_no_histMarkov`: in particular none satisfies the tree
  hypothesis `TidyR6MarkovAbstractN.HistMarkovN` with non-degenerate `P`, and
  `histMarkov_not_pointwiseLinear`: on any state space, no forecast of such a system is
  pointwise-linear.
* `avgSystem_pointwiseLinear`: the counterexample `TidyR6MarkovAbstractN.avgSystem` is
  pointwise-linear and carries a Markov regime with non-degenerate `P`, which is not known at each
  date — the known-regime hypothesis of the no-go cannot be dropped.
-/

namespace Cochrane.ObservationalEquivalence.TidyR6MarkovNoGo

open Cochrane.ObservationalEquivalence.MarkovRegimesGeneral
open Cochrane.ObservationalEquivalence.TidyR6MarkovAbstractN

variable {Ω : Type*} {N : ℕ}

/-- Cochrane (2023), p. 523: the date-`0` forecast at `ω` is a finite linear combination of
values, `E_0 x(ω) = ∑_{z ∈ F} c_z x(z)`. -/
def PointwiseLinearAt (𝔼 : ExpectationSystem Ω) (ω : Ω) : Prop :=
  ∃ (F : Finset Ω) (c : Ω → ℝ), ∀ x : Ω → ℝ, 𝔼.E 0 x ω = ∑ z ∈ F, c z * x z

/-- Cochrane (2023), p. 522: the regime is known at each date, `E_t f(S_t) = f(S_t)`. -/
def RegimeAdapted (𝔼 : ExpectationSystem Ω) (S : ℕ → Ω → Fin N) : Prop :=
  ∀ t (f : Fin N → ℝ), 𝔼.E t (f ∘ S t) = f ∘ S t

/-- Cochrane (2023), p. 523: every regime can be followed by at least two different regimes. -/
def Nondegenerate (T : TransitionN N) : Prop :=
  ∀ i, ∃ j₁ j₂, j₁ ≠ j₂ ∧ 0 < T.P i j₁ ∧ 0 < T.P i j₂

/-- Cochrane (2023), p. 522: two regime histories up to date `t` agree iff the regimes agree at
every date before `t`. -/
theorem pastOf_eq_iff (S : ℕ → Ω → Fin N) (t : ℕ) (z ω : Ω) :
    pastOf S t z = pastOf S t ω ↔ ∀ s < t, S s z = S s ω := by
  induction t with
  | zero => simp [pastOf]
  | succ t ih =>
    simp only [pastOf, List.cons.injEq, ih]
    constructor
    · rintro ⟨h1, h2⟩ s hs
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
      · exact h2 s hs
      · exact h1
    · intro h
      exact ⟨h t (Nat.lt_succ_self t), fun s hs => h s (Nat.lt_succ_of_lt hs)⟩

/-- Cochrane (2023), p. 522: forecasts of nonnegative variables are nonnegative.
The monotonicity axiom of `ExpectationSystem` at `0`. -/
theorem E_nonneg (𝔼 : ExpectationSystem Ω) (t : ℕ) {x : Ω → ℝ} (hx : 0 ≤ x) :
    0 ≤ 𝔼.E t x := by
  have h := 𝔼.mono t hx
  rwa [map_zero] at h

/-- Cochrane (2023), p. 522: a regime that is known at each date stays known later,
`E_t f(S_s) = f(S_s)` for `s ≤ t`. -/
theorem adapted_later {𝔼 : ExpectationSystem Ω} {S : ℕ → Ω → Fin N} (hA : RegimeAdapted 𝔼 S)
    {s t : ℕ} (hst : s ≤ t) (f : Fin N → ℝ) : 𝔼.E t (f ∘ S s) = f ∘ S s := by
  rw [← hA s f, 𝔼.known hst]

/-- Cochrane (2023), p. 522: when the regime is known, so is the regime history: at `ω`, the
date-`t` forecast of the indicator that the history up to `t` differs from `ω`'s is `0`. -/
theorem hist_known {𝔼 : ExpectationSystem Ω} {S : ℕ → Ω → Fin N} (hA : RegimeAdapted 𝔼 S)
    (t : ℕ) (ω : Ω) :
    𝔼.E t (fun z => if pastOf S (t + 1) z = pastOf S (t + 1) ω then 0 else 1) ω = 0 := by
  classical
  set g : ℕ → Fin N → ℝ := fun s l => if l = S s ω then 0 else 1 with hg
  set D : Ω → ℝ := ∑ s ∈ Finset.range (t + 1), g s ∘ S s with hD
  have hED : 𝔼.E t D = D := by
    rw [hD, map_sum]
    exact Finset.sum_congr rfl fun s hs =>
      adapted_later hA (Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)) (g s)
  have hD0 : D ω = 0 := by
    rw [hD, Finset.sum_apply]
    exact Finset.sum_eq_zero fun s _ => by simp [hg]
  have hle : (fun z => if pastOf S (t + 1) z = pastOf S (t + 1) ω then (0 : ℝ) else 1) ≤ D := by
    intro z
    have hDnn : 0 ≤ D z := by
      rw [hD, Finset.sum_apply]
      exact Finset.sum_nonneg fun s _ => by
        simp only [Function.comp_apply, hg]
        split_ifs <;> norm_num
    change (if pastOf S (t + 1) z = pastOf S (t + 1) ω then (0 : ℝ) else 1) ≤ D z
    split_ifs with h
    · exact hDnn
    · rw [pastOf_eq_iff] at h
      push Not at h
      obtain ⟨s, hs, hne⟩ := h
      rw [hD, Finset.sum_apply]
      have hmem : s ∈ Finset.range (t + 1) := Finset.mem_range.2 hs
      calc (1 : ℝ) = (g s ∘ S s) z := by simp [hg, hne]
        _ ≤ ∑ s ∈ Finset.range (t + 1), (g s ∘ S s) z :=
          Finset.single_le_sum (f := fun s => (g s ∘ S s) z) (fun s _ => by
            simp only [Function.comp_apply, hg]
            split_ifs <;> norm_num) hmem
  have h1 := 𝔼.mono t hle ω
  have h2 := E_nonneg 𝔼 t (x := fun z => if pastOf S (t + 1) z = pastOf S (t + 1) ω then
    (0 : ℝ) else 1) (fun z => by
      change (0 : ℝ) ≤ if _ then 0 else 1
      split_ifs <;> norm_num) ω
  rw [hED, hD0] at h1
  exact le_antisymm h1 h2

variable {𝔼 : ExpectationSystem Ω} {T : TransitionN N}

/-- Cochrane (2023), p. 523: under a pointwise-linear forecast at `ω` with weights `c` on `F`,
the forecast of a regime history up to date `t + 1` from a weighted point `ω'` of `F` puts weight
only on histories realised in `F`: every regime `j` with `P_{S_t(ω'), j} > 0` follows `ω'`'s
history at some point of `F`. -/
theorem split_in_support (R : MarkovRegimeN 𝔼 T) (hA : RegimeAdapted 𝔼 R.S) {ω : Ω}
    {F : Finset Ω} {c : Ω → ℝ} (hL : ∀ x : Ω → ℝ, 𝔼.E 0 x ω = ∑ z ∈ F, c z * x z)
    (hc0 : ∀ z ∈ F, 0 ≤ c z) {ω' : Ω} (hω' : ω' ∈ F) (hcω' : 0 < c ω') (t : ℕ) {j : Fin N}
    (hj : 0 < T.P (R.S t ω') j) :
    ∃ z ∈ F, pastOf R.S (t + 1) z = pastOf R.S (t + 1) ω' ∧ R.S (t + 1) z = j := by
  classical
  by_contra hno
  push Not at hno
  have hvan : ∀ x : Ω → ℝ, 0 ≤ x → (∀ z ∈ F, x z = 0) → 𝔼.E t x ω' = 0 := by
    intro x hx hxF
    have h1 : 𝔼.E 0 (𝔼.E t x) ω = 𝔼.E 0 x ω := congrFun (𝔼.tower (Nat.zero_le t) x) ω
    have h0 : ∑ z ∈ F, c z * x z = 0 := Finset.sum_eq_zero fun z hz => by rw [hxF z hz, mul_zero]
    rw [hL, hL, h0] at h1
    have hnn : ∀ z ∈ F, 0 ≤ c z * 𝔼.E t x z := fun z hz =>
      mul_nonneg (hc0 z hz) (E_nonneg 𝔼 t hx z)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h1 ω' hω'
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hcω'.ne'
    · exact h
  set y : Ω → ℝ := fun z =>
    if pastOf R.S (t + 1) z = pastOf R.S (t + 1) ω' ∧ R.S (t + 1) z = j then 1 else 0 with hy
  set ind : Ω → ℝ := fun z =>
    if pastOf R.S (t + 1) z = pastOf R.S (t + 1) ω' then 0 else 1 with hind
  set f : Fin N → ℝ := fun l => if l = j then 1 else 0 with hf
  have hy0 : 𝔼.E t y ω' = 0 := hvan y (fun z => by
    simp only [hy, Pi.zero_apply]
    split_ifs <;> norm_num) (fun z hz => by
      simp only [hy]
      split_ifs with h
      · exact absurd h.2 (hno z hz h.1)
      · rfl)
  have hi0 : 𝔼.E t ind ω' = 0 := hist_known hA t ω'
  have hle : f ∘ R.S (t + 1) ≤ y + ind := by
    intro z
    simp only [Function.comp_apply, hf, hy, hind, Pi.add_apply]
    split_ifs <;> simp_all
  have h1 := 𝔼.mono t hle ω'
  rw [map_add, R.markov t f] at h1
  simp only [Pi.add_apply, hy0, hi0, add_zero, hf, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h1
  linarith

/-- Cochrane (2023), p. 523: under a pointwise-linear forecast at `ω` supported on `F`, a known,
non-degenerate Markov regime has at least `t + 1` distinct histories up to date `t` among the
points of `F`. -/
theorem card_hist_ge (R : MarkovRegimeN 𝔼 T) (hA : RegimeAdapted 𝔼 R.S) (hT : Nondegenerate T)
    {ω : Ω} {F : Finset Ω} {c : Ω → ℝ} (hL : ∀ x : Ω → ℝ, 𝔼.E 0 x ω = ∑ z ∈ F, c z * x z)
    (hc0 : ∀ z ∈ F, 0 ≤ c z) {ω' : Ω} (hω' : ω' ∈ F) (hcω' : 0 < c ω') (t : ℕ) :
    t + 1 ≤ (F.image (pastOf R.S (t + 1))).card := by
  classical
  induction t with
  | zero =>
    have : (F.image (pastOf R.S 1)).Nonempty := ⟨_, Finset.mem_image_of_mem _ hω'⟩
    exact this.card_pos
  | succ t ih =>
    have himg : (F.image (pastOf R.S (t + 1 + 1))).image List.tail =
        F.image (pastOf R.S (t + 1)) := by
      rw [Finset.image_image]
      rfl
    obtain ⟨j₁, j₂, hne, hp1, hp2⟩ := hT (R.S t ω')
    obtain ⟨z₁, hz₁, hh₁, hs₁⟩ := split_in_support R hA hL hc0 hω' hcω' t hp1
    obtain ⟨z₂, hz₂, hh₂, hs₂⟩ := split_in_support R hA hL hc0 hω' hcω' t hp2
    have hninj : ¬ Set.InjOn List.tail (F.image (pastOf R.S (t + 1 + 1)) : Set (List (Fin N))) := by
      intro hinj
      have heq := hinj (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hz₁))
        (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hz₂))
        (by change pastOf R.S (t + 1) z₁ = pastOf R.S (t + 1) z₂; rw [hh₁, hh₂])
      change R.S (t + 1) z₁ :: pastOf R.S (t + 1) z₁ =
        R.S (t + 1) z₂ :: pastOf R.S (t + 1) z₂ at heq
      rw [List.cons.injEq, hs₁, hs₂] at heq
      exact hne heq.1
    have hlt : (F.image (pastOf R.S (t + 1))).card < (F.image (pastOf R.S (t + 1 + 1))).card := by
      rw [← himg]
      exact lt_of_le_of_ne Finset.card_image_le (fun h => hninj (Finset.card_image_iff.1 h))
    omega

/-- Cochrane (2023), pp. 522–523 (**the no-go**): if a Markov regime is known at each date and
every row of `P` has two positive entries, then no date-`0` forecast of the expectation system
is a finite linear combination of values. -/
theorem not_pointwiseLinear (R : MarkovRegimeN 𝔼 T) (hA : RegimeAdapted 𝔼 R.S)
    (hT : Nondegenerate T) (ω : Ω) : ¬ PointwiseLinearAt 𝔼 ω := by
  classical
  rintro ⟨F, c, hL⟩
  have hc0 : ∀ z ∈ F, 0 ≤ c z := by
    intro z hz
    have h := hL (fun w => if w = z then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', hz, ↓reduceIte] at h
    rw [← h]
    exact E_nonneg 𝔼 0 (fun w => by
      change (0 : ℝ) ≤ if w = z then 1 else 0
      split_ifs <;> norm_num) ω
  have hsum : ∑ z ∈ F, c z = 1 := by
    have h := hL (fun _ => 1)
    rw [𝔼.const] at h
    simpa using h.symm
  obtain ⟨ω', hω', hcω'⟩ : ∃ ω' ∈ F, 0 < c ω' := by
    by_contra hno
    push Not at hno
    have := Finset.sum_nonpos hno
    linarith
  have h1 := card_hist_ge R hA hT hL hc0 hω' hcω' F.card
  have h2 : (F.image (pastOf R.S (F.card + 1))).card ≤ F.card := Finset.card_image_le
  omega

/-- Cochrane (2023), p. 523: on a finite state space every forecast is pointwise-linear,
`E_0 x(ω) = ∑_z E_0 1{z}(ω) x(z)`. -/
theorem pointwiseLinear_of_finite [Finite Ω] (𝔼 : ExpectationSystem Ω) (ω : Ω) :
    PointwiseLinearAt 𝔼 ω := by
  classical
  have := Fintype.ofFinite Ω
  refine ⟨Finset.univ, fun z => 𝔼.E 0 (fun w => if w = z then 1 else 0) ω, fun x => ?_⟩
  have hx : x = ∑ z, x z • (fun w => if w = z then (1 : ℝ) else 0) := by
    funext w
    simp [Finset.sum_apply]
  conv_lhs => rw [hx]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

/-! ### Countable state spaces -/

/-- Cochrane (2023), p. 523: a positive forecast charges only finitely many single states — the
set of `z` with `E_0 1{z}(ω) > 0` is finite. -/
theorem finite_support (𝔼 : ExpectationSystem Ω) (ω : Ω) [DecidableEq Ω] :
    {z | 0 < 𝔼.E 0 (fun w => if w = z then 1 else 0) ω}.Finite := by
  set c : Ω → ℝ := fun z => 𝔼.E 0 (fun w => if w = z then 1 else 0) ω with hc
  by_contra hinf
  set x : Ω → ℝ := fun w => if 0 < c w then 1 / c w else 0 with hx
  obtain ⟨n, hn⟩ := exists_nat_gt (𝔼.E 0 x ω)
  obtain ⟨G, hGsub, hGcard⟩ := Set.Infinite.exists_subset_card_eq hinf n
  have hle : (∑ z ∈ G, (1 / c z) • (fun w => if w = z then (1 : ℝ) else 0)) ≤ x := by
    intro w
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
    split_ifs with hw
    · have hpos : 0 < c w := hGsub hw
      simp [hx, hpos]
    · simp only [hx]
      split_ifs with hp
      · exact (one_div_pos.2 hp).le
      · exact le_rfl
  have h1 := 𝔼.mono 0 hle ω
  rw [map_sum, Finset.sum_apply] at h1
  have h2 : ∑ z ∈ G, (𝔼.E 0 ((1 / c z) • fun w => if w = z then (1 : ℝ) else 0)) ω =
      ∑ z ∈ G, (1 : ℝ) := by
    refine Finset.sum_congr rfl fun z hz => ?_
    have hpos : 0 < c z := hGsub hz
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    change 1 / c z * c z = 1
    field_simp
  rw [h2, Finset.sum_const, nsmul_eq_mul, mul_one, hGcard] at h1
  linarith

/-- Cochrane (2023), p. 523: on a countable state space a forecast vanishes on every nonnegative
variable supported on states that it does not charge (`E_0 1{z}(ω) = 0` wherever `x(z) ≠ 0`). -/
theorem vanish_of_support [Countable Ω] [DecidableEq Ω] (𝔼 : ExpectationSystem Ω) (ω : Ω)
    {y : Ω → ℝ} (hy : 0 ≤ y)
    (hc : ∀ z, y z ≠ 0 → 𝔼.E 0 (fun w => if w = z then 1 else 0) ω = 0) :
    𝔼.E 0 y ω = 0 := by
  obtain ⟨k, hk⟩ := Countable.exists_injective_nat Ω
  set zf : Ω → ℝ := fun w => ((k w : ℝ) + 1) * y w with hzf
  have hhead : ∀ m : ℕ, 𝔼.E 0 (fun w => if k w < m then y w else 0) ω = 0 := by
    intro m
    set G : Finset Ω := (Finset.range m).preimage k hk.injOn with hG
    have hrep : (fun w => if k w < m then y w else 0) =
        ∑ z ∈ G, y z • (fun w => if w = z then (1 : ℝ) else 0) := by
      funext w
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
      simp [hG]
    rw [hrep, map_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hz : y z = 0
    · rw [hz, zero_mul]
    · rw [hc z hz, mul_zero]
  have hbound : ∀ m : ℕ, 0 < m → 𝔼.E 0 y ω * m ≤ 𝔼.E 0 zf ω := by
    intro m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have hle : y ≤ (1 / (m : ℝ)) • zf + fun w => if k w < m then y w else 0 := by
      intro w
      change y w ≤ 1 / (m : ℝ) * (((k w : ℝ) + 1) * y w) + (if k w < m then y w else 0)
      have hyw := hy w
      have hk0 : (0 : ℝ) ≤ (k w : ℝ) + 1 := by positivity
      have hnn : 0 ≤ 1 / (m : ℝ) * (((k w : ℝ) + 1) * y w) :=
        mul_nonneg (by positivity) (mul_nonneg hk0 hyw)
      split_ifs with hkw
      · linarith
      · have hkm : (m : ℝ) ≤ (k w : ℝ) + 1 := by
          have : m ≤ k w := not_lt.1 hkw
          have : (m : ℝ) ≤ k w := by exact_mod_cast this
          linarith
        have hdiv : 1 ≤ ((k w : ℝ) + 1) / m := (one_le_div hmpos).2 hkm
        have : y w ≤ ((k w : ℝ) + 1) / m * y w := by
          simpa using mul_le_mul_of_nonneg_right hdiv hyw
        have heq : ((k w : ℝ) + 1) / m * y w = 1 / (m : ℝ) * (((k w : ℝ) + 1) * y w) := by
          ring
        linarith
    have h1 := 𝔼.mono 0 hle ω
    rw [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hhead m, add_zero] at h1
    rw [← le_div_iff₀ hmpos]
    calc 𝔼.E 0 y ω ≤ 1 / (m : ℝ) * 𝔼.E 0 zf ω := h1
      _ = 𝔼.E 0 zf ω / m := by ring
  have hnn : 0 ≤ 𝔼.E 0 y ω := E_nonneg 𝔼 0 hy ω
  by_contra hne
  have hpos : 0 < 𝔼.E 0 y ω := lt_of_le_of_ne hnn (Ne.symm hne)
  obtain ⟨m, hm⟩ := exists_nat_gt (𝔼.E 0 zf ω / 𝔼.E 0 y ω)
  have hm0 : 0 < m := by
    have : 0 ≤ 𝔼.E 0 zf ω / 𝔼.E 0 y ω := by
      have := hbound 1 one_pos
      rw [Nat.cast_one, mul_one] at this
      exact div_nonneg (by linarith) hnn
    exact_mod_cast (lt_of_le_of_lt this hm)
  have := hbound m hm0
  rw [div_lt_iff₀ hpos] at hm
  linarith

/-- Cochrane (2023), p. 523: on a countable state space every forecast is pointwise-linear —
`E_0 x(ω) = ∑_{z ∈ F} E_0 1{z}(ω) x(z)` with `F` the finite set of charged states. -/
theorem pointwiseLinear_of_countable [Countable Ω] (𝔼 : ExpectationSystem Ω) (ω : Ω) :
    PointwiseLinearAt 𝔼 ω := by
  classical
  set c : Ω → ℝ := fun z => 𝔼.E 0 (fun w => if w = z then 1 else 0) ω with hc
  have hc0 : ∀ z, 0 ≤ c z := fun z => E_nonneg 𝔼 0 (fun w => by
    change (0 : ℝ) ≤ if w = z then 1 else 0
    split_ifs <;> norm_num) ω
  set F : Finset Ω := (finite_support 𝔼 ω).toFinset with hF
  have hmemF : ∀ z, z ∈ F ↔ 0 < c z := fun z => by simp [hF, hc]
  refine ⟨F, c, fun x => ?_⟩
  set xin : Ω → ℝ := fun w => if w ∈ F then x w else 0 with hxin
  set p : Ω → ℝ := fun w => if w ∈ F then 0 else max (x w) 0 with hp
  set q : Ω → ℝ := fun w => if w ∈ F then 0 else max (-x w) 0 with hq
  have hsplit : x = xin + (p - q) := by
    funext w
    simp only [Pi.add_apply, Pi.sub_apply, hxin, hp, hq]
    split_ifs
    · ring
    · rcases le_total (x w) 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]
        ring
      · rw [max_eq_left h, max_eq_right (by linarith)]
        ring
  have hout : ∀ r : Ω → ℝ, 0 ≤ r → (∀ w ∈ F, r w = 0) → 𝔼.E 0 r ω = 0 := by
    intro r hr hrF
    refine vanish_of_support 𝔼 ω hr fun z hz => ?_
    have hzF : z ∉ F := fun h => hz (hrF z h)
    rw [hmemF] at hzF
    exact le_antisymm (not_lt.1 hzF) (hc0 z)
  have hp0 : 𝔼.E 0 p ω = 0 := hout p (fun w => by
    simp only [hp, Pi.zero_apply]
    split_ifs
    · exact le_rfl
    · exact le_max_right _ _) (fun w hw => by simp [hp, hw])
  have hq0 : 𝔼.E 0 q ω = 0 := hout q (fun w => by
    simp only [hq, Pi.zero_apply]
    split_ifs
    · exact le_rfl
    · exact le_max_right _ _) (fun w hw => by simp [hq, hw])
  have hxin' : xin = ∑ z ∈ F, x z • (fun w => if w = z then (1 : ℝ) else 0) := by
    funext w
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, hxin]
  have hE : 𝔼.E 0 x ω = 𝔼.E 0 xin ω := by
    conv_lhs => rw [hsplit]
    rw [map_add, map_sub, Pi.add_apply, Pi.sub_apply, hp0, hq0, sub_zero, add_zero]
  rw [hE, hxin', map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- Cochrane (2023), pp. 522–523 (**no countable model**): no expectation system on a countable
state space carries a Markov regime that is known at each date and has non-degenerate
transitions. -/
theorem countable_no_regime [Countable Ω] (R : MarkovRegimeN 𝔼 T) (hT : Nondegenerate T)
    [Nonempty Ω] : ¬ RegimeAdapted 𝔼 R.S := fun hA =>
  not_pointwiseLinear R hA hT (Classical.arbitrary Ω) (pointwiseLinear_of_countable 𝔼 _)

/-- Cochrane (2023), pp. 522–523: a regime satisfying the tree hypothesis
`TidyR6MarkovAbstractN.HistMarkovN` is known at each date.
Restates `TidyR6MarkovAbstractN.HistMarkovN.adapted`. -/
theorem histMarkov_adapted (R : HistMarkovN 𝔼 T) : RegimeAdapted 𝔼 R.S :=
  fun t f => R.adapted t f

/-- Cochrane (2023), pp. 522–523 (**the tree hypothesis has no pointwise-linear model**): with
non-degenerate transitions, no date-`0` forecast of a system satisfying the tree hypothesis is
pointwise-linear. -/
theorem histMarkov_not_pointwiseLinear (R : HistMarkovN 𝔼 T) (hT : Nondegenerate T) (ω : Ω) :
    ¬ PointwiseLinearAt 𝔼 ω :=
  not_pointwiseLinear R.toMarkov (histMarkov_adapted R) hT ω

/-- Cochrane (2023), pp. 522–523: with non-degenerate transitions, no expectation system on a
countable nonempty state space satisfies the tree hypothesis. -/
theorem countable_no_histMarkov [Countable Ω] [Nonempty Ω] (R : HistMarkovN 𝔼 T)
    (hT : Nondegenerate T) : False :=
  histMarkov_not_pointwiseLinear R hT (Classical.arbitrary Ω) (pointwiseLinear_of_countable 𝔼 _)

/-- Cochrane (2023), p. 523: the i.i.d. chain `p_ij = ½` is non-degenerate. -/
theorem egHalf_nondegenerate : Nondegenerate (ofTwo egHalf) :=
  fun _ => ⟨0, 1, by decide, by norm_num [ofTwo, egHalf], by norm_num [ofTwo, egHalf]⟩

/-- Cochrane (2023), p. 523 (**the known-regime hypothesis cannot be dropped**): the two-state
system `avgSystem` is pointwise-linear and carries the non-degenerate Markov regime
`avgRegime`, which is not known at each date. -/
theorem avgSystem_pointwiseLinear :
    (∀ ω, PointwiseLinearAt avgSystem ω) ∧ Nondegenerate (ofTwo egHalf) ∧
      ¬ RegimeAdapted avgSystem avgRegime.S :=
  ⟨pointwiseLinear_of_finite avgSystem, egHalf_nondegenerate,
    fun hA => avgRegime_not_adapted 0 (hA 0 _)⟩

end Cochrane.ObservationalEquivalence.TidyR6MarkovNoGo
