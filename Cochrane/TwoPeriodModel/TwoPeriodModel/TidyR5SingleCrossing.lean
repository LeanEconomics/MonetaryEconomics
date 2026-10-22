/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TwoPeriodModel.ActivePassive

/-!
# Active rules with a single crossing: existence of equilibrium

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 1, §1.8, p. 17.

Cochrane says that for active policy "we just have to exclude the one-for-one case … (or
multiple crossings)". `ActivePassive.active_unique_of_strictAnti` shows that a single crossing
(the excess valuation `f(P) = B₀/P − s(P)` strictly decreasing on `P > 0`) gives **at most**
one equilibrium, and `ActivePassive.active_existsUnique` gives existence only for continuous,
weakly increasing surplus rules. This module settles existence for general single-crossing
rules, which may be decreasing in `P₁`.

## Main results

* `eqmSet_nonempty_iff`: for a surplus rule continuous on `P > 0`, an equilibrium exists
  **iff** the valuation curve changes sign: some `a > 0` has `s(a) ≤ B₀/a` and some `b > 0` has
  `B₀/b ≤ s(b)` (intermediate value theorem; no monotonicity needed).
* `singleCrossing_existsUnique_iff`: for a continuous single-crossing rule, the equilibrium is
  unique and exists **iff** the same sign condition holds — the exact characterisation of
  active single-crossing rules.
* `singleCrossing_existsUnique_of_bounds`: an economically checkable sufficient condition
  (surplus bounded above at low price levels and bounded away from zero at high ones).
* `decreasing_rule_active`: the rule `s(P) = B₀/(2P) + c` is strictly decreasing in `P₁`, so
  not covered by `ActivePassive.active_existsUnique`, yet has exactly one equilibrium.
* Counterexamples: `continuous_singleCrossing_no_eqm` (continuity and a single crossing do not
  suffice without the sign condition) and `discont_singleCrossing_no_eqm` (without continuity
  a single-crossing rule with a sign change, positive surpluses everywhere when `B₀ ≥ 1`, has
  no equilibrium; `discont_rule_not_continuousOn` confirms continuity is what fails).
-/

namespace Cochrane.TwoPeriodModel.TidyR5SingleCrossing

open Cochrane.TwoPeriodModel.ActivePassive

/-- Cochrane (2023), p. 17: the excess valuation `f(P) = B₀/P − s(P)` of a surplus rule;
the equilibria are its zeros on `P > 0`, and a "single crossing" means `f` strictly
decreasing there. -/
noncomputable def excess (B0 : ℝ) (s : ℝ → ℝ) (P : ℝ) : ℝ := B0 / P - s P

/-- Cochrane (2023), p. 17: the sign-change condition for a surplus rule: at some price level
`a > 0` the surplus is at most the value of debt, `s(a) ≤ B₀/a`, and at some `b > 0` it is at
least the value of debt, `B₀/b ≤ s(b)`. -/
def SignChange (B0 : ℝ) (s : ℝ → ℝ) : Prop :=
  (∃ a, 0 < a ∧ s a ≤ B0 / a) ∧ ∃ b, 0 < b ∧ B0 / b ≤ s b

/-- Cochrane (2023), p. 17: **existence** of an equilibrium by the intermediate value theorem:
a surplus rule continuous on `P > 0` with a sign change has an equilibrium (in either order of
`a` and `b`; no monotonicity is needed). -/
theorem exists_of_signChange {B0 : ℝ} {s : ℝ → ℝ} (hcont : ContinuousOn s (Set.Ioi 0))
    (hsc : SignChange B0 s) : (eqmSet B0 s).Nonempty := by
  obtain ⟨⟨a, ha, hsa⟩, ⟨b, hb, hsb⟩⟩ := hsc
  have hsub : Set.uIcc a b ⊆ Set.Ioi 0 := by
    intro x hx
    rcases Set.mem_uIcc.mp hx with h | h
    · exact lt_of_lt_of_le ha h.1
    · exact lt_of_lt_of_le hb h.1
  have hcf : ContinuousOn (excess B0 s) (Set.uIcc a b) := by
    refine ContinuousOn.sub ?_ (hcont.mono hsub)
    exact continuousOn_const.div continuousOn_id (fun x hx => (hsub hx).ne')
  have hfa : 0 ≤ excess B0 s a := by simp only [excess]; linarith
  have hfb : excess B0 s b ≤ 0 := by simp only [excess]; linarith
  have h0 : (0 : ℝ) ∈ Set.uIcc (excess B0 s a) (excess B0 s b) :=
    Set.mem_uIcc.mpr (Or.inr ⟨hfb, hfa⟩)
  obtain ⟨c, hc, hfc⟩ := intermediate_value_uIcc hcf h0
  refine ⟨c, hsub hc, ?_⟩
  simp only [excess] at hfc
  linarith

/-- Cochrane (2023), p. 17: the sign-change condition is necessary for an equilibrium: an
equilibrium `P₁` serves as both `a` and `b`. -/
theorem signChange_of_mem {B0 : ℝ} {s : ℝ → ℝ} {P : ℝ} (hP : P ∈ eqmSet B0 s) :
    SignChange B0 s :=
  ⟨⟨P, hP.1, hP.2.symm.le⟩, ⟨P, hP.1, hP.2.le⟩⟩

/-- Cochrane (2023), p. 17: for a surplus rule continuous on `P > 0`, an equilibrium exists
**iff** the sign-change condition holds. -/
theorem eqmSet_nonempty_iff {B0 : ℝ} {s : ℝ → ℝ} (hcont : ContinuousOn s (Set.Ioi 0)) :
    (eqmSet B0 s).Nonempty ↔ SignChange B0 s :=
  ⟨fun ⟨_, hP⟩ => signChange_of_mem hP, exists_of_signChange hcont⟩

/-- Cochrane (2023), p. 17, **active single-crossing rules, exact characterisation**: if the
surplus rule is continuous on `P > 0` and crosses the valuation curve once (`B₀/P − s(P)`
strictly decreasing on `P > 0`), there is exactly one equilibrium price level **iff** the
sign-change condition holds. The rule need not be weakly increasing in `P₁`. -/
theorem singleCrossing_existsUnique_iff {B0 : ℝ} {s : ℝ → ℝ}
    (hcont : ContinuousOn s (Set.Ioi 0))
    (hanti : StrictAntiOn (fun P => B0 / P - s P) (Set.Ioi 0)) :
    (∃! P : ℝ, 0 < P ∧ B0 / P = s P) ↔ SignChange B0 s := by
  constructor
  · rintro ⟨P, hP, -⟩
    exact signChange_of_mem hP
  · intro hsc
    obtain ⟨P, hP⟩ := exists_of_signChange hcont hsc
    exact ⟨P, hP, fun Q hQ => active_unique_of_strictAnti hanti hQ hP⟩

/-- Cochrane (2023), p. 17: a checkable sufficient condition for a continuous single-crossing
rule to be active: if the surplus is bounded above, `s(P) ≤ M`, at price levels `0 < P ≤ 1`, and
bounded away from zero, `s(P) ≥ ε > 0`, at price levels `P ≥ P₀`, then (for `B₀ > 0`) there is
exactly one equilibrium price level. -/
theorem singleCrossing_existsUnique_of_bounds {B0 M ε P0 : ℝ} (hB : 0 < B0) {s : ℝ → ℝ}
    (hcont : ContinuousOn s (Set.Ioi 0))
    (hanti : StrictAntiOn (fun P => B0 / P - s P) (Set.Ioi 0))
    (hM : ∀ P, 0 < P → P ≤ 1 → s P ≤ M) (hε : 0 < ε) (hlarge : ∀ P, P0 ≤ P → ε ≤ s P) :
    ∃! P : ℝ, 0 < P ∧ B0 / P = s P := by
  refine (singleCrossing_existsUnique_iff hcont hanti).mpr ⟨?_, ?_⟩
  · have hden : 0 < |M| + B0 := by positivity
    refine ⟨B0 / (|M| + B0), div_pos hB hden, ?_⟩
    have ha1 : B0 / (|M| + B0) ≤ 1 := by
      rw [div_le_one hden]; linarith [abs_nonneg M]
    have h1 : B0 / (B0 / (|M| + B0)) = |M| + B0 := by field_simp
    rw [h1]
    have := hM _ (div_pos hB hden) ha1
    linarith [le_abs_self M]
  · set b := max P0 (B0 / ε) with hb
    have hbB : B0 / ε ≤ b := le_max_right _ _
    have hb0 : 0 < b := lt_of_lt_of_le (div_pos hB hε) hbB
    refine ⟨b, hb0, ?_⟩
    have h1 : B0 / b ≤ ε := by
      rw [div_le_iff₀ hb0]
      rw [div_le_iff₀ hε] at hbB
      linarith
    exact h1.trans (hlarge b (le_max_left _ _))

/-- Cochrane (2023), p. 17: the surplus rule `s(P) = B₀/(2P) + c` (`B₀, c > 0`) cuts surpluses
as the price level rises — it is strictly decreasing, so `ActivePassive.active_existsUnique`
does not apply — but it crosses the valuation curve once, and it has exactly one equilibrium,
`P₁ = B₀/(2c)`. -/
theorem decreasing_rule_active {B0 c : ℝ} (hB : 0 < B0) (hc : 0 < c) :
    StrictAntiOn (fun P => B0 / (2 * P) + c) (Set.Ioi 0) ∧
      ¬ MonotoneOn (fun P => B0 / (2 * P) + c) (Set.Ioi 0) ∧
      ∃! P : ℝ, 0 < P ∧ B0 / P = B0 / (2 * P) + c := by
  have hsa : StrictAntiOn (fun P => B0 / (2 * P) + c) (Set.Ioi 0) := by
    intro x hx y _ hxy
    have hx' : (0 : ℝ) < x := hx
    have : B0 / (2 * y) < B0 / (2 * x) := div_lt_div_of_pos_left hB (by positivity) (by linarith)
    simp only
    linarith
  refine ⟨hsa, fun hmono => ?_, ?_⟩
  · have m1 : (1 : ℝ) ∈ Set.Ioi 0 := Set.mem_Ioi.mpr one_pos
    have m2 : (2 : ℝ) ∈ Set.Ioi 0 := Set.mem_Ioi.mpr two_pos
    have h1 := hsa m1 m2 one_lt_two
    have h2 := hmono m1 m2 one_lt_two.le
    exact absurd h2 (not_le.mpr h1)
  · have hcont : ContinuousOn (fun P => B0 / (2 * P) + c) (Set.Ioi 0) := by
      refine ContinuousOn.add ?_ continuousOn_const
      refine continuousOn_const.div (continuousOn_const.mul continuousOn_id) ?_
      intro x hx
      have hx' : (0 : ℝ) < x := hx
      positivity
    have hanti : StrictAntiOn (fun P => B0 / P - (B0 / (2 * P) + c)) (Set.Ioi 0) := by
      intro x hx y _ hxy
      have hx' : (0 : ℝ) < x := hx
      have hy' : (0 : ℝ) < y := by linarith
      have e : ∀ z : ℝ, 0 < z → B0 / z - (B0 / (2 * z) + c) = B0 / (2 * z) - c := by
        intro z hz; field_simp; ring
      simp only
      rw [e x hx', e y hy']
      have : B0 / (2 * y) < B0 / (2 * x) := div_lt_div_of_pos_left hB (by positivity)
        (by linarith)
      linarith
    refine (singleCrossing_existsUnique_iff hcont hanti).mpr ⟨⟨B0 / (2 * c), by positivity, ?_⟩,
      ⟨B0 / (2 * c), by positivity, ?_⟩⟩
    · apply le_of_eq; field_simp; ring
    · apply le_of_eq; field_simp; ring

/-- Cochrane (2023), p. 17, counterexample: continuity and a single crossing do **not** give
existence without the sign-change condition: the continuous rule `s(P) = B₀/P + P` has
`B₀/P − s(P) = −P` strictly decreasing, but no equilibrium. -/
theorem continuous_singleCrossing_no_eqm (B0 : ℝ) :
    ContinuousOn (fun P => B0 / P + P) (Set.Ioi 0) ∧
      StrictAntiOn (fun P => B0 / P - (B0 / P + P)) (Set.Ioi 0) ∧
      eqmSet B0 (fun P => B0 / P + P) = ∅ := by
  refine ⟨?_, ?_, ?_⟩
  · refine ContinuousOn.add ?_ continuousOn_id
    exact continuousOn_const.div continuousOn_id (fun x hx => (ne_of_lt hx).symm)
  · intro x _ y _ hxy
    simp only
    linarith
  · ext P
    simp only [eqmSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hP h
    linarith

/-- Cochrane (2023), p. 17: the discontinuous excess valuation used in
`discont_singleCrossing_no_eqm`: `1 − P` below `P = 1` and `−P` from `P = 1` on. -/
noncomputable def jumpExcess (P : ℝ) : ℝ := if P < 1 then 1 - P else -P

/-- Cochrane (2023), p. 17: the discontinuous surplus rule `s(P) = B₀/P − jumpExcess(P)`. -/
noncomputable def jumpRule (B0 : ℝ) (P : ℝ) : ℝ := B0 / P - jumpExcess P

/-- Cochrane (2023), p. 17, counterexample: **continuity cannot be dropped**. The rule
`jumpRule` crosses the valuation curve at most once (`B₀/P − s(P)` strictly decreasing), has
the sign change (`a = 1/2`, `b = 1`), and for `B₀ ≥ 1` runs a positive surplus at every price
level, yet it has no equilibrium: `B₀/P − s(P)` jumps from `+0` to `−1` at `P = 1`. -/
theorem discont_singleCrossing_no_eqm (B0 : ℝ) :
    StrictAntiOn (fun P => B0 / P - jumpRule B0 P) (Set.Ioi 0) ∧
      SignChange B0 (jumpRule B0) ∧ eqmSet B0 (jumpRule B0) = ∅ ∧
      (1 ≤ B0 → ∀ P, 0 < P → 0 < jumpRule B0 P) := by
  have hf : ∀ P, B0 / P - jumpRule B0 P = jumpExcess P := by
    intro P; simp only [jumpRule]; ring
  refine ⟨?_, ⟨⟨1 / 2, by norm_num, ?_⟩, ⟨1, one_pos, ?_⟩⟩, ?_, ?_⟩
  · intro x _ y _ hxy
    simp only [hf, jumpExcess]
    by_cases hy : y < 1
    · have hx : x < 1 := lt_trans hxy hy
      simp only [hx, hy, ↓reduceIte]
      linarith
    · by_cases hx : x < 1
      · simp only [hx, hy, ↓reduceIte]
        linarith
      · simp only [hx, hy, ↓reduceIte]
        linarith
  · have := hf (1 / 2)
    simp only [jumpExcess, show (1 / 2 : ℝ) < 1 by norm_num, ↓reduceIte] at this
    linarith
  · have := hf 1
    simp only [jumpExcess, lt_irrefl, ↓reduceIte] at this
    linarith
  · ext P
    simp only [eqmSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hP h
    have h2 := hf P
    rw [← h, sub_self] at h2
    simp only [jumpExcess] at h2
    by_cases h1 : P < 1
    · simp only [h1, ↓reduceIte] at h2
      linarith
    · simp only [h1, ↓reduceIte] at h2
      linarith
  · intro hB P hP
    simp only [jumpRule, jumpExcess]
    by_cases h1 : P < 1
    · simp only [h1, ↓reduceIte]
      have : 1 < B0 / P := by rw [lt_div_iff₀ hP]; linarith
      linarith
    · simp only [h1, ↓reduceIte]
      have : 0 < B0 / P := div_pos (by linarith) hP
      linarith

/-- Cochrane (2023), p. 17: the rule `jumpRule` is indeed not continuous on `P > 0` — by
`exists_of_signChange`, continuity together with its sign change would produce an
equilibrium. -/
theorem discont_rule_not_continuousOn (B0 : ℝ) :
    ¬ ContinuousOn (jumpRule B0) (Set.Ioi 0) := by
  intro hcont
  obtain ⟨-, hsc, hempty, -⟩ := discont_singleCrossing_no_eqm B0
  have := exists_of_signChange hcont hsc
  rw [hempty] at this
  exact Set.not_nonempty_empty this

end Cochrane.TwoPeriodModel.TidyR5SingleCrossing
