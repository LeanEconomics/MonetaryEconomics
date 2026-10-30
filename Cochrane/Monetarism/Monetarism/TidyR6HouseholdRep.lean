/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.Expectations
import Mathlib.Data.Set.Finite.Basic

/-!
# Expectation systems on a countable state space are finitely supported averages

Cochrane (2023), *The Fiscal Theory of the Price Level*, Ch. 2, pp. 29–30 (rational expectations
`E_t`) and Ch. 19, p. 439 (expected utility `E ∑ βᵗu`), for the core `ExpectationSystem`. An
`ExpectationSystem` is a family of positive, unital linear operators on all functions `Ω → ℝ`; it
carries no measure. This module shows that on a **countable** state space a measure is
automatically there: every date-`t` expectation at every state is the average under a finitely
supported probability.

## Main results

* `support_finite`: a positive linear functional on `Ω → ℝ` gives positive mass to only finitely
  many states (otherwise it would take an infinite value on a suitable function).
* `vanish_off_support`: on a countable `Ω`, it vanishes on every nonnegative function that is zero
  on those states (otherwise it would be infinite on `h · (ι + 1)` for an injection `ι : Ω → ℕ`).
* `functional_rep`: on a countable `Ω` a positive unital linear functional is
  `L f = ∑_{ω ∈ F} p_ω f(ω)` with `p ≥ 0` finitely supported and `∑ p = 1`.
* **`expectation_rep`**: for every `ExpectationSystem` on a countable `Ω`, every date `t` and
  state `ω₀`, `E_t f(ω₀) = ∑_{ω ∈ F} p_ω f(ω)` for a finitely supported probability `p`
  (depending on `t`, `ω₀`). Neither the tower property nor the pull-out property is needed: the
  representation comes from positivity, linearity and `E_t 1 = 1` alone. So on a countable state
  space an expected-utility household problem can always be posed.

Countability of `Ω` is the extra property, and it is used only in `vanish_off_support`. On an
uncountable `Ω` a counterexample (a unital positive linear functional on all of `ℝ^Ω` that is not a
finitely supported average) would, by the argument of `vanish_off_support`, yield a countably
additive probability on all subsets of `Ω` vanishing on points, i.e. a real-valued measurable
cardinal. ZFC (and Lean's foundations) cannot prove such a cardinal exists, so no Lean
counterexample can be given; the uncountable case is neither proved nor refuted here.
-/

namespace Cochrane.Monetarism.TidyR6HouseholdRep

variable {Ω : Type*}

/-- Cochrane (2023), Ch. 2, p. 29: the indicator of the single state `ω`. -/
noncomputable def ind (ω : Ω) : Ω → ℝ := ({ω} : Set Ω).indicator fun _ => 1

/-- Cochrane (2023), Ch. 2, p. 29: the indicator of `ω` is `1` at `ω`. -/
theorem ind_self (ω : Ω) : ind ω ω = 1 := by simp [ind]

/-- Cochrane (2023), Ch. 2, p. 29: the indicator of `ω` is `0` away from `ω`. -/
theorem ind_ne {ω ω' : Ω} (h : ω' ≠ ω) : ind ω ω' = 0 := by simp [ind, h]

/-- Cochrane (2023), Ch. 2, p. 29: the indicator of a state is nonnegative. -/
theorem ind_nonneg (ω : Ω) : 0 ≤ ind ω := fun ω' => by
  by_cases h : ω' = ω
  · rw [h, ind_self]
    norm_num
  · rw [ind_ne h]
    simp

/-- Cochrane (2023), Ch. 2, p. 29: **only finitely many states carry mass.** For a positive linear
functional `L` on `Ω → ℝ`, the set of states with `L(1_{ω}) > 0` is finite. -/
theorem support_finite (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (hpos : ∀ f, 0 ≤ f → 0 ≤ L f) :
    {ω | 0 < L (ind ω)}.Finite := by
  by_contra hinf
  set e := Set.Infinite.natEmbedding _ hinf with he
  set p : ℕ → ℝ := fun n => L (ind (e n : Ω)) with hp
  have hp0 : ∀ n, 0 < p n := fun n => (e n).2
  set f : Ω → ℝ := (Set.range fun n => (e n : Ω)).indicator fun ω => 1 / L (ind ω) with hf
  have hinj : ∀ {n k : ℕ}, (e n : Ω) = e k → n = k := fun h => e.injective (Subtype.ext h)
  have hle : ∀ N : ℕ, ∑ n ∈ Finset.range N, (1 / p n) • ind (e n : Ω) ≤ f := by
    intro N ω
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hω : ω ∈ Set.range fun n => (e n : Ω)
    · obtain ⟨k, rfl⟩ := hω
      rw [hf, Set.indicator_of_mem (Set.mem_range_self k)]
      have hz : ∀ n, n ≠ k → 1 / p n * ind (e n : Ω) (e k) = 0 := fun n hn => by
        rw [ind_ne (fun h : (e k : Ω) = e n => hn (hinj h.symm)), mul_zero]
      by_cases hk : k ∈ Finset.range N
      · rw [Finset.sum_eq_single_of_mem k hk fun n _ hn => hz n hn, ind_self, mul_one]
      · rw [Finset.sum_eq_zero fun n hn => hz n (fun h => hk (h ▸ hn))]
        exact (one_div_pos.2 (hp0 k)).le
    · rw [hf, Set.indicator_of_notMem hω]
      refine le_of_eq (Finset.sum_eq_zero fun n _ => ?_)
      rw [ind_ne (fun h : ω = e n => hω ⟨n, h.symm⟩), mul_zero]
  have hL : ∀ N : ℕ, (N : ℝ) ≤ L f := by
    intro N
    have h1 := hpos _ (sub_nonneg.2 (hle N))
    rw [map_sub, map_sum] at h1
    have h2 : ∑ n ∈ Finset.range N, L ((1 / p n) • ind (e n : Ω)) = N := by
      rw [Finset.sum_congr rfl fun n _ => by
        rw [map_smul, smul_eq_mul, show L (ind (e n : Ω)) = p n from rfl,
          one_div_mul_cancel (hp0 n).ne']]
      simp
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (L f)
  linarith [hL N]

/-- Cochrane (2023), Ch. 2, p. 29: **a positive functional on a countable space vanishes off its
atoms.** If `Ω` is countable and `h ≥ 0` is zero at every state with `L(1_{ω}) > 0`, then
`L h = 0`. -/
theorem vanish_off_support [Countable Ω] (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (hpos : ∀ f, 0 ≤ f → 0 ≤ L f)
    {h : Ω → ℝ} (h0 : 0 ≤ h) (hS : ∀ ω, 0 < L (ind ω) → h ω = 0) : L h = 0 := by
  classical
  obtain ⟨ι, hι⟩ := Countable.exists_injective_nat Ω
  have hpn : ∀ ω, 0 ≤ L (ind ω) := fun ω => hpos _ (ind_nonneg ω)
  -- the part of `h` on finitely many states has value zero
  have hfin : ∀ n : ℕ, L ({ω | ι ω < n}.indicator h) = 0 := by
    intro n
    have hF : {ω | ι ω < n}.Finite := (Set.finite_lt_nat n).preimage hι.injOn
    have e : {ω | ι ω < n}.indicator h = ∑ ω ∈ hF.toFinset, h ω • ind ω := by
      funext ω'
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hω : ι ω' < n
      · have hm : ω' ∈ hF.toFinset := by simpa using hω
        rw [Set.indicator_of_mem (show ω' ∈ {ω | ι ω < n} from hω),
          Finset.sum_eq_single_of_mem ω' hm fun b _ hb => by rw [ind_ne (Ne.symm hb), mul_zero],
          ind_self, mul_one]
      · rw [Set.indicator_of_notMem (show ω' ∉ {ω | ι ω < n} from hω)]
        refine (Finset.sum_eq_zero fun b hb => ?_).symm
        have hne : b ≠ ω' := fun h => hω (by subst h; simpa using hb)
        rw [ind_ne (Ne.symm hne), mul_zero]
    rw [e, map_sum]
    refine Finset.sum_eq_zero fun ω _ => ?_
    rw [map_smul, smul_eq_mul]
    rcases (hpn ω).lt_or_eq with hp | hp
    · rw [hS ω hp, zero_mul]
    · rw [← hp, mul_zero]
  -- the tails all have value `L h`
  have htail : ∀ n : ℕ, L ({ω | ι ω < n}ᶜ.indicator h) = L h := by
    intro n
    have := congrArg L (Set.indicator_self_add_compl {ω | ι ω < n} h)
    rw [map_add, hfin n, zero_add] at this
    exact this
  set H : Ω → ℝ := fun ω => h ω * (ι ω + 1) with hH
  have hle : ∀ N : ℕ, ∑ n ∈ Finset.range N, {ω | ι ω < n}ᶜ.indicator h ≤ H := by
    intro N ω
    simp only [Finset.sum_apply, hH]
    have hcount : ∑ n ∈ Finset.range N, ({ω | ι ω < n}ᶜ.indicator h) ω =
        h ω * ((Finset.range N).filter fun n => n ≤ ι ω).card := by
      rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases hn : n ≤ ι ω
      · rw [Set.indicator_of_mem (show ω ∈ {ω | ι ω < n}ᶜ by simpa using hn)]
        simp [hn]
      · rw [Set.indicator_of_notMem (show ω ∉ {ω | ι ω < n}ᶜ by simpa using hn)]
        simp [hn]
    rw [hcount]
    refine mul_le_mul_of_nonneg_left ?_ (h0 ω)
    have : ((Finset.range N).filter fun n => n ≤ ι ω) ⊆ Finset.range (ι ω + 1) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
      omega
    have := Finset.card_le_card this
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hNL : ∀ N : ℕ, (N : ℝ) * L h ≤ L H := by
    intro N
    have h1 := hpos _ (sub_nonneg.2 (hle N))
    rw [map_sub, map_sum] at h1
    simp only [htail, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    linarith
  have hLh := hpos h h0
  rcases hLh.lt_or_eq with hlt | heq
  · obtain ⟨N, hN⟩ := exists_nat_gt (L H / L h)
    have := hNL N
    rw [div_lt_iff₀ hlt] at hN
    linarith
  · exact heq.symm

/-- Cochrane (2023), Ch. 2, p. 29: **positive unital linear functionals on a countable space are
finitely supported averages.** On a countable `Ω`, a positive linear functional with `L 1 = 1`
is `L f = ∑_{ω ∈ F} p_ω f(ω)` for a finite set `F` and weights `p ≥ 0` with `∑_{ω∈F} p_ω = 1`. -/
theorem functional_rep [Countable Ω] (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (hpos : ∀ f, 0 ≤ f → 0 ≤ L f)
    (hone : L (fun _ => 1) = 1) :
    ∃ (F : Finset Ω) (p : Ω → ℝ), (∀ ω, 0 ≤ p ω) ∧ ∑ ω ∈ F, p ω = 1 ∧
      ∀ f, L f = ∑ ω ∈ F, p ω * f ω := by
  classical
  set S := {ω | 0 < L (ind ω)} with hSdef
  have hS := support_finite L hpos
  set F := hS.toFinset with hF
  have hrep : ∀ f, L f = ∑ ω ∈ F, L (ind ω) * f ω := by
    intro f
    set g : Ω → ℝ := f - ∑ ω ∈ F, f ω • ind ω with hg
    have hgS : ∀ ω, 0 < L (ind ω) → g ω = 0 := by
      intro ω hω
      have hmem : ω ∈ F := by simpa [hF, hSdef] using hω
      simp only [hg, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single_of_mem ω hmem fun b _ hb => by rw [ind_ne (Ne.symm hb), mul_zero],
        ind_self, mul_one, sub_self]
    have hpart : ∀ k : Ω → ℝ, 0 ≤ k → (∀ ω, 0 < L (ind ω) → k ω = 0) → L k = 0 :=
      fun k hk hk0 => vanish_off_support L hpos hk hk0
    have h1 := hpart (fun ω => max (g ω) 0) (fun ω => le_max_right _ _) fun ω hω => by
      simp [hgS ω hω]
    have h2 := hpart (fun ω => max (-g ω) 0) (fun ω => le_max_right _ _) fun ω hω => by
      simp [hgS ω hω]
    have hsplit : g = (fun ω => max (g ω) 0) - fun ω => max (-g ω) 0 := by
      funext ω
      simp only [Pi.sub_apply]
      rcases le_total 0 (g ω) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]
        ring
      · rw [max_eq_right h, max_eq_left (by linarith)]
        ring
    have hg0 : L g = 0 := by rw [hsplit, map_sub, h1, h2, sub_zero]
    have : f = g + ∑ ω ∈ F, f ω • ind ω := by
      funext ω
      simp [hg]
    conv_lhs => rw [this]
    rw [map_add, hg0, zero_add, map_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  refine ⟨F, fun ω => L (ind ω), fun ω => hpos _ (ind_nonneg ω), ?_, hrep⟩
  have := hrep fun _ => 1
  rw [hone] at this
  simpa using this.symm

/-- Cochrane (2023), Ch. 2, pp. 29–30 and Ch. 19, p. 439, **every expectation system on a
countable state space is given by finitely supported conditional probabilities**: for every date
`t` and state `ω₀` there are a finite set `F` of states and weights `p ≥ 0` with `∑ p = 1` such
that `E_t f(ω₀) = ∑_{ω ∈ F} p_ω f(ω)` for every random variable `f`. Only linearity, positivity
and `E_t 1 = 1` are used. -/
theorem expectation_rep [Countable Ω] (𝔼 : ExpectationSystem Ω) (t : ℕ) (ω₀ : Ω) :
    ∃ (F : Finset Ω) (p : Ω → ℝ), (∀ ω, 0 ≤ p ω) ∧ ∑ ω ∈ F, p ω = 1 ∧
      ∀ f, 𝔼.E t f ω₀ = ∑ ω ∈ F, p ω * f ω := by
  set L : (Ω → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj ω₀).comp (𝔼.E t) with hL
  have hpos : ∀ f, 0 ≤ f → 0 ≤ L f := fun f hf => by
    have := 𝔼.mono t hf ω₀
    simpa [hL] using this
  have hone : L (fun _ => 1) = 1 := by
    simp [hL, 𝔼.const t 1]
  obtain ⟨F, p, h1, h2, h3⟩ := functional_rep L hpos hone
  exact ⟨F, p, h1, h2, fun f => h3 f⟩

end Cochrane.Monetarism.TidyR6HouseholdRep
