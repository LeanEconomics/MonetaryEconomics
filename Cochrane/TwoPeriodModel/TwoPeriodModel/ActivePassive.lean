/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TwoPeriodModel.MonetaryFiscal
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Real.Cardinality

/-!
# Budget constraints, active versus passive policy, and a debt rule

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 1, §§1.8–1.9, pp. 15–19.

A **fiscal rule** for the last day is a function `s : ℝ → ℝ`, the real surplus the government
runs at each date-1 price level `P₁`. Its equilibrium set is `eqmSet B₀ s = {P₁ > 0 | B₀/P₁ =
s(P₁)}`. Policy is **active** when the equilibrium set has exactly one element (the fiscal theory
determines `P₁`), **passive** when it is `s(P₁) = B₀/P₁`, so that every `P₁ > 0` is an
equilibrium.

## Main results

* (1.14)–(1.15), p. 16: `budget_any_price` (the budget constraint `B₀ = P₁s₁ + M₁` holds at
  every price), `valuation_of_zero_money` and `money_zero_of_valuation` ((1.14) is the budget
  constraint plus zero demand for money left over), `money_nonzero_off_equilibrium`.
* (1.16), p. 17: `passive_eqmSet` (every `P₁ > 0` is an equilibrium), `passive_indeterminate`
  (the equilibrium set is uncountable), `passive_taxRate`, `passive_taxRate_strictAnti`
  (p. 18: the tax rate must fall as the price level rises).
* p. 17, active policy: `active_unique_of_strictAnti` (a single crossing gives at most one
  equilibrium), `active_existsUnique` (a continuous surplus rule that is weakly increasing in
  `P₁` and positive somewhere gives exactly one equilibrium), `fixed_surplus_active`,
  `propTax_active` (p. 18: a proportional tax is active), `multiple_crossings` (a rule with
  two equilibria — "or multiple crossings").
* §1.9, p. 18: `value_decomp`, `value_decomp_innov` (three sources of variation in the value of
  debt).
* §1.9, pp. 18–19, the rule `s₁ = α B₀/P₁* + γ(B₀/P₁ − B₀/P₁*)`: `gamma_eqmSet`,
  `gamma_eqmSet_passive`, `gamma_eqmSet_empty`, `gamma_rule_general_iff` (for `γ ≠ 1`, unique
  iff `(α − γ)/(1 − γ) > 0`), `gamma_rule_determinate_iff` (with `α = 1` the
  equilibrium is unique **iff `γ ≠ 1`** — error E2: "responding less than one-for-one" is
  sufficient, not necessary: `less_than_one_for_one_not_necessary`), `gamma_rule_random`
  (the same state by state with a random target), `gamma_not_identified`,
  `obs_equiv_two_period`, `rule_regression_gamma_one` (p. 18: under (1.13) the data satisfy
  `s₁ = 1 · B₀/P₁` exactly).
-/

namespace Cochrane.TwoPeriodModel.ActivePassive

open Cochrane.TwoPeriodModel.TwoPeriod Cochrane.TwoPeriodModel.MonetaryFiscal

variable {Ω : Type*}

/-! ### (1.14)–(1.15): budget constraint versus equilibrium condition -/

/-- Cochrane (2023), eq. (1.15), p. 16: the budget constraint `B₀ = P₁s₁ + M₁` holds at any
price level: for every `B₀, P₁, s₁` there is exactly one money overhang `M₁`. -/
theorem budget_any_price (B0 P1 s1 : ℝ) : ∃! M1 : ℝ, B0 = P1 * s1 + M1 :=
  ⟨B0 - P1 * s1, by ring, fun M1 h => by linarith⟩

/-- Cochrane (2023), eqs. (1.14)–(1.15), p. 16: the budget constraint plus zero demand for
money at the end of the day, `M₁ = 0`, gives the valuation equation `B₀/P₁ = s₁` (`P₁ ≠ 0`). -/
theorem valuation_of_zero_money {B0 P1 s1 M1 : ℝ} (hP : P1 ≠ 0) (hb : B0 = P1 * s1 + M1)
    (hM : M1 = 0) : B0 / P1 = s1 := by
  rw [← lastDay_iff hP, hb, hM, add_zero]

/-- Cochrane (2023), eqs. (1.14)–(1.15), p. 16: conversely, if `B₀/P₁ = s₁` the money left over
is zero. -/
theorem money_zero_of_valuation {B0 P1 s1 M1 : ℝ} (hP : P1 ≠ 0) (hb : B0 = P1 * s1 + M1)
    (hv : B0 / P1 = s1) : M1 = 0 := by
  have := (lastDay_iff hP).mpr hv
  linarith

/-- Cochrane (2023), p. 16: "budget constraints hold at off-equilibrium prices; equilibrium
conditions need not": at any price level `P₁ > 0` other than `B₀/s₁` (`s₁ > 0`), the budget
constraint holds with a nonzero overhang `M₁ ≠ 0`, so (1.14) fails. -/
theorem money_nonzero_off_equilibrium {B0 P1 s1 M1 : ℝ} (hs : 0 < s1)
    (hb : B0 = P1 * s1 + M1) (hne : P1 ≠ B0 / s1) : M1 ≠ 0 := by
  intro hM
  apply hne
  rw [eq_div_iff hs.ne']
  linarith

/-! ### Fiscal rules and their equilibrium sets -/

/-- Cochrane (2023), p. 17: the equilibrium set of a date-1 fiscal rule `s : ℝ → ℝ`,
`{P₁ > 0 | B₀/P₁ = s(P₁)}`. -/
def eqmSet (B0 : ℝ) (s : ℝ → ℝ) : Set ℝ := {P | 0 < P ∧ B0 / P = s P}

/-- Cochrane (2023), eq. (1.16), p. 17: under the passive rule `s₁ = B₀/P₁`, "`P₁` cancels from
left and right": every positive price level is an equilibrium. -/
theorem passive_eqmSet (B0 : ℝ) : eqmSet B0 (fun P => B0 / P) = Set.Ioi 0 := by
  ext P
  simp [eqmSet]

/-- Cochrane (2023), p. 17: under the passive rule (1.16) "(1.14) no longer determines the
price level": the set of equilibrium price levels is uncountable. -/
theorem passive_indeterminate (B0 : ℝ) : ¬ (eqmSet B0 (fun P => B0 / P)).Countable := by
  rw [passive_eqmSet]
  intro h
  have h1 : Cardinal.mk (Set.Ioi (0 : ℝ)) ≤ Cardinal.aleph0 :=
    Cardinal.mk_le_aleph0_iff.mpr h.to_subtype
  rw [Cardinal.mk_Ioi_real] at h1
  exact absurd h1 (not_le.mpr Cardinal.aleph0_lt_continuum)

/-- Cochrane (2023), eq. (1.16) and p. 18: implementing `s₁ = τ₁y₁ = B₀/P₁` requires the tax
rate `τ₁ = B₀/(P₁y₁)` (`P₁, y₁ ≠ 0`). -/
theorem passive_taxRate {B0 P1 y1 τ1 : ℝ} (hP : P1 ≠ 0) (hy : y1 ≠ 0) :
    τ1 * y1 = B0 / P1 ↔ τ1 = B0 / (P1 * y1) := by
  rw [eq_div_iff hP, eq_div_iff (mul_ne_zero hP hy)]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 18: "the government must systematically lower the tax rate … as the
price level rises": `P₁ ↦ B₀/(P₁y₁)` is strictly decreasing on `P₁ > 0` (`B₀, y₁ > 0`). -/
theorem passive_taxRate_strictAnti {B0 y1 : ℝ} (hB : 0 < B0) (hy : 0 < y1) :
    StrictAntiOn (fun P => B0 / (P * y1)) (Set.Ioi 0) := by
  intro x hx y _ hxy
  have hx' : (0 : ℝ) < x := hx
  exact div_lt_div_of_pos_left hB (mul_pos hx' hy) (mul_lt_mul_of_pos_right hxy hy)

/-- Cochrane (2023), p. 17: "we just have to exclude the one-for-one case … (or multiple
crossings) so that there is only one solution to (1.14)": if `P ↦ B₀/P − s(P)` is strictly
decreasing on `P > 0` (single crossing), there is at most one equilibrium. -/
theorem active_unique_of_strictAnti {B0 : ℝ} {s : ℝ → ℝ}
    (h : StrictAntiOn (fun P => B0 / P - s P) (Set.Ioi 0)) :
    (eqmSet B0 s).Subsingleton := by
  rintro x ⟨hx, hxe⟩ y ⟨hy, hye⟩
  refine h.injOn hx hy ?_
  simp only [hxe, hye, sub_self]

/-- Cochrane (2023), p. 17, **active fiscal policy determines the price level**: if the surplus
rule `s(P₁)` is continuous and weakly increasing in `P₁` on `P₁ > 0` (a fixed real surplus, a
proportional tax, or austerity in response to inflation) and positive at some price level, then
for `B₀ > 0` there is exactly one equilibrium price level. -/
theorem active_existsUnique {B0 : ℝ} (hB : 0 < B0) {s : ℝ → ℝ}
    (hmono : MonotoneOn s (Set.Ioi 0)) (hcont : ContinuousOn s (Set.Ioi 0))
    (hpos : ∃ p, 0 < p ∧ 0 < s p) : ∃! P : ℝ, 0 < P ∧ B0 / P = s P := by
  obtain ⟨p, hp, hsp⟩ := hpos
  set f : ℝ → ℝ := fun P => B0 / P - s P with hf
  have hanti : StrictAntiOn f (Set.Ioi 0) := by
    intro x hx y hy hxy
    have hx' : (0 : ℝ) < x := hx
    have h1 : B0 / y < B0 / x := div_lt_div_of_pos_left hB hx' hxy
    have h2 : s x ≤ s y := hmono hx hy hxy.le
    simp only [hf]
    linarith
  have hden : 0 < s p + B0 / p := by positivity
  set a := B0 / (s p + B0 / p) with ha_def
  set b := p + B0 / s p with hb_def
  have ha : 0 < a := div_pos hB hden
  have hpB : p * (B0 / p) = B0 := by field_simp
  have hap : a ≤ p := by
    rw [ha_def, div_le_iff₀ hden, mul_add, hpB]
    nlinarith [mul_pos hp hsp]
  have hpb : p ≤ b := by
    have : 0 < B0 / s p := div_pos hB hsp
    linarith
  have hb : 0 < b := by linarith
  have hfa : 0 < f a := by
    have h1 : B0 / a = s p + B0 / p := by
      rw [ha_def]; field_simp
    have h2 : s a ≤ s p := hmono ha hp hap
    have h3 : 0 < B0 / p := div_pos hB hp
    simp only [hf]
    linarith
  have hfb : f b < 0 := by
    have h1 : B0 / b < s p := by
      rw [div_lt_iff₀ hb, hb_def, mul_add]
      have : s p * (B0 / s p) = B0 := by field_simp
      nlinarith [mul_pos hsp hp]
    have h2 : s p ≤ s b := hmono hp hb hpb
    simp only [hf]
    linarith
  have hab : a ≤ b := hap.trans hpb
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le ha hx.1
  have hcf : ContinuousOn f (Set.Icc a b) := by
    refine ContinuousOn.sub ?_ (hcont.mono hsub)
    exact continuousOn_const.div continuousOn_id (fun x hx => (hsub hx).ne')
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc' hab hcf ⟨hfb.le, hfa.le⟩
  have hc0 : 0 < c := hsub hc
  refine ⟨c, ⟨hc0, by simp only [hf] at hfc; linarith⟩, fun y ⟨hy, hye⟩ => ?_⟩
  refine hanti.injOn hy hc0 ?_
  simp only [hf, hye, sub_self]
  simp only [hf] at hfc
  exact hfc.symm

/-- Cochrane (2023), §1.1 and p. 17: a fixed real surplus `s₁ > 0` is an active policy: exactly
one equilibrium price level. -/
theorem fixed_surplus_active {B0 s1 : ℝ} (hB : 0 < B0) (hs : 0 < s1) :
    ∃! P : ℝ, 0 < P ∧ B0 / P = (fun _ => s1) P :=
  active_existsUnique hB (fun _ _ _ _ _ => le_rfl) continuousOn_const ⟨1, one_pos, hs⟩

/-- Cochrane (2023), pp. 17–18: "with a proportional tax on income … the real surplus
`s₁ = τy₁ − g₁` is then independent of the price level, so fiscal policy is active": exactly one
equilibrium when `τy₁ − g₁ > 0`. -/
theorem propTax_active {B0 τ y1 g1 : ℝ} (hB : 0 < B0) (hs : 0 < τ * y1 - g1) :
    ∃! P : ℝ, 0 < P ∧ B0 / P = (fun _ => τ * y1 - g1) P :=
  fixed_surplus_active hB hs

/-- Cochrane (2023), p. 17, "(or multiple crossings)": a surplus rule can cross the valuation
curve more than once; for `B₀ > 0` the rule `s(P) = B₀(3 − P)/2` has the two equilibria
`P₁ = 1` and `P₁ = 2`, so it is not active. -/
theorem multiple_crossings {B0 : ℝ} :
    (1 : ℝ) ∈ eqmSet B0 (fun P => B0 * (3 - P) / 2) ∧
      (2 : ℝ) ∈ eqmSet B0 (fun P => B0 * (3 - P) / 2) := by
  refine ⟨⟨one_pos, by ring⟩, ⟨two_pos, by ring⟩⟩

/-! ### §1.9: three sources of variation in the value of debt -/

/-- Cochrane (2023), §1.9, p. 18: `B₀/P₁ = B₀/P₁* + B₀(1/P₁ − 1/P₁*)`: nominal debt, the
price-level target, and inflation different from the target. -/
theorem value_decomp (B0 P1 Pstar : ℝ) : B0 / P1 = B0 / Pstar + B0 * (1 / P1 - 1 / Pstar) := by
  ring

/-- Cochrane (2023), §1.9, p. 18: the unexpected value of debt splits into an innovation in
the target and in inflation relative to the target:
`(E₁ − E₀)(B₀/P₁) = B₀(E₁ − E₀)(1/P₁*) + B₀(E₁ − E₀)(1/P₁ − 1/P₁*)` (`PullOut`, `B₀` known at
date 0). -/
theorem value_decomp_innov (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {B0 P1 Pstar : Ω → ℝ}
    (hkB0 : Known 𝔼 0 B0) :
    innov 𝔼 (B0 / P1) = B0 * innov 𝔼 (1 / Pstar) + B0 * innov 𝔼 (1 / P1 - 1 / Pstar) := by
  have hk1 : Known 𝔼 1 B0 := known_mono 𝔼 zero_le_one hkB0
  have e1 : B0 / P1 = B0 * (1 / P1) := by
    funext ω; simp only [Pi.div_apply, Pi.mul_apply, Pi.one_apply]; ring
  rw [e1]
  unfold innov
  rw [hP 1 B0 _ hk1, hP 0 B0 _ hkB0, map_sub, map_sub]
  funext ω
  simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
  ring

/-- Cochrane (2023), §1.9, p. 19: the surplus rule `s₁ = α B₀/P₁* + γ(B₀/P₁ − B₀/P₁*)`. -/
noncomputable def gammaRule (α γ B0 Pstar : ℝ) (P : ℝ) : ℝ :=
  α * (B0 / Pstar) + γ * (B0 / P - B0 / Pstar)

/-- Cochrane (2023), §1.9, pp. 18–19: the equilibria of the `γ`-rule are the `P₁ > 0` with
`(1 − γ)B₀/P₁ = (α − γ)B₀/P₁*` (for `γ ≠ 1` this pins down `B₀/P₁`). -/
theorem gamma_eqmSet {α γ B0 Pstar : ℝ} :
    eqmSet B0 (gammaRule α γ B0 Pstar) =
      {P | 0 < P ∧ (1 - γ) * (B0 / P) = (α - γ) * (B0 / Pstar)} := by
  ext P
  simp only [eqmSet, gammaRule, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨hP, h⟩ <;> exact ⟨hP, by linarith⟩

/-- Cochrane (2023), §1.9, p. 19: with `α = γ = 1` the `γ`-rule is the passive rule: every
`P₁ > 0` is an equilibrium. -/
theorem gamma_eqmSet_passive (B0 Pstar : ℝ) :
    eqmSet B0 (gammaRule 1 1 B0 Pstar) = Set.Ioi 0 := by
  ext P
  simp only [eqmSet, gammaRule, Set.mem_ofPred_eq, Set.mem_Ioi]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, by ring⟩

/-- Cochrane (2023), §1.9, p. 19: with `γ = 1` and `α ≠ 1` there is no equilibrium
(`B₀ ≠ 0`, `P₁* ≠ 0`). -/
theorem gamma_eqmSet_empty {α B0 Pstar : ℝ} (hα : α ≠ 1) (hB : B0 ≠ 0) (hPs : Pstar ≠ 0) :
    eqmSet B0 (gammaRule α 1 B0 Pstar) = ∅ := by
  rw [gamma_eqmSet]
  ext P
  simp only [Set.mem_ofPred_eq, sub_self, zero_mul, Set.mem_empty_iff_false, iff_false, not_and]
  intro _ h
  have : (α - 1) * (B0 / Pstar) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hα) (div_ne_zero hB hPs)
  exact this h.symm

/-- Cochrane (2023), §1.9, pp. 18–19 (**error E2**): with `α = 1`, `B₀ > 0`, `P₁* > 0`, the
`γ`-rule has a unique equilibrium **iff `γ ≠ 1`**, and then `P₁ = P₁*`. -/
theorem gamma_rule_determinate_iff {γ B0 Pstar : ℝ} (hB : 0 < B0) (hPs : 0 < Pstar) :
    (∃! P : ℝ, 0 < P ∧ B0 / P = gammaRule 1 γ B0 Pstar P) ↔ γ ≠ 1 := by
  constructor
  · rintro ⟨P, hP, hu⟩ rfl
    have h1 := hu P hP
    have h2 := hu (P + 1) ⟨by linarith [hP.1], by simp [gammaRule]⟩
    linarith
  · intro hγ
    refine ⟨Pstar, ⟨hPs, by simp [gammaRule]⟩, fun P ⟨hP, h⟩ => ?_⟩
    simp only [gammaRule, one_mul] at h
    have h1 : (1 - γ) * (B0 / P - B0 / Pstar) = 0 := by linarith
    have h2 : B0 / P = B0 / Pstar := by
      rcases mul_eq_zero.mp h1 with h0 | h0
      · exact absurd (by linarith : γ = 1) hγ
      · linarith
    rw [div_eq_div_iff hP.ne' hPs.ne'] at h2
    exact (mul_left_cancel₀ hB.ne' (by linarith : B0 * Pstar = B0 * P)).symm

/-- Cochrane (2023), §1.9, pp. 18–19, general `α`: for `γ ≠ 1`, `B₀ > 0`, `P₁* > 0` the
`γ`-rule has a unique equilibrium iff `(α − γ)/(1 − γ) > 0`, namely
`P₁ = P₁*(1 − γ)/(α − γ)`. -/
theorem gamma_rule_general_iff {α γ B0 Pstar : ℝ} (hB : 0 < B0) (hPs : 0 < Pstar)
    (hγ : γ ≠ 1) :
    (∃! P : ℝ, 0 < P ∧ B0 / P = gammaRule α γ B0 Pstar P) ↔ 0 < (α - γ) / (1 - γ) := by
  have h1 : (1 - γ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  set c := (α - γ) / (1 - γ) with hc
  have key : ∀ P, B0 / P = gammaRule α γ B0 Pstar P ↔ B0 / P = c * (B0 / Pstar) := by
    intro P
    simp only [gammaRule, hc]
    rw [div_mul_eq_mul_div, eq_div_iff h1]
    constructor <;> intro h <;> linarith
  have hX : 0 < B0 / Pstar := div_pos hB hPs
  constructor
  · rintro ⟨P, ⟨hP, h⟩, -⟩
    rw [key] at h
    by_contra hneg
    have : c * (B0 / Pstar) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) hX.le
    have : 0 < B0 / P := div_pos hB hP
    linarith
  · intro hcpos
    have hQ : 0 < Pstar / c := div_pos hPs hcpos
    have hsol : B0 / (Pstar / c) = c * (B0 / Pstar) := by
      field_simp
    refine ⟨Pstar / c, ⟨hQ, (key _).mpr hsol⟩, fun P ⟨hP, h⟩ => ?_⟩
    rw [key, ← hsol, div_eq_div_iff hP.ne' hQ.ne'] at h
    exact mul_left_cancel₀ hB.ne' (by linarith)

/-- Cochrane (2023), p. 18 (**error E2**): "active fiscal policy only requires that the
government respond less than one-for-one to the last component" — responding less than
one-for-one (`γ < 1`) is not necessary: the over-responding rule `γ = 2` is also determinate. -/
theorem less_than_one_for_one_not_necessary {B0 Pstar : ℝ} (hB : 0 < B0) (hPs : 0 < Pstar) :
    ∃ γ : ℝ, 1 < γ ∧ ∃! P : ℝ, 0 < P ∧ B0 / P = gammaRule 1 γ B0 Pstar P :=
  ⟨2, one_lt_two, (gamma_rule_determinate_iff hB hPs).mpr (by norm_num)⟩

/-- Cochrane (2023), §1.9, pp. 18–19, with a random target: if the surplus follows the
`γ`-rule state by state, `s₁ = B₀/P₁* + γ(B₀/P₁ − B₀/P₁*)`, then for `γ ≠ 1` the only positive
`P₁` solving `B₀/P₁ = s₁` is `P₁ = P₁*`, while for `γ = 1` every positive `P₁` solves it. -/
theorem gamma_rule_random {γ : ℝ} {B0 Pstar : Ω → ℝ} (hB : ∀ ω, 0 < B0 ω)
    (hPs : ∀ ω, 0 < Pstar ω) :
    (γ ≠ 1 → ∀ P1 : Ω → ℝ, (∀ ω, 0 < P1 ω) →
      (Valuation1 B0 P1 (fun ω => gammaRule 1 γ (B0 ω) (Pstar ω) (P1 ω)) ↔ P1 = Pstar)) ∧
    (γ = 1 → ∀ P1 : Ω → ℝ, Valuation1 B0 P1 (fun ω => gammaRule 1 γ (B0 ω) (Pstar ω) (P1 ω))) := by
  refine ⟨fun hγ P1 hP1 => ⟨fun h => funext fun ω => ?_, ?_⟩, fun hγ P1 => ?_⟩
  · obtain ⟨P, -, hu⟩ := (gamma_rule_determinate_iff (hB ω) (hPs ω)).mpr hγ
    exact (hu (P1 ω) ⟨hP1 ω, congrFun h ω⟩).trans (hu (Pstar ω)
      ⟨hPs ω, by simp [gammaRule]⟩).symm
  · rintro rfl
    funext ω
    simp [gammaRule]
  · subst hγ
    funext ω
    simp only [Pi.div_apply, gammaRule]
    ring

/-- Cochrane (2023), p. 19: "the parameter `γ` … is not identified": for every `γ ≠ 1` (with
`α = 1`) the equilibrium is the same, `P₁ = P₁*` and `s₁ = B₀/P₁*`. -/
theorem gamma_not_identified {γ γ' B0 Pstar P P' : ℝ} (hB : 0 < B0) (hPs : 0 < Pstar)
    (hγ : γ ≠ 1) (hγ' : γ' ≠ 1) (hP : 0 < P ∧ B0 / P = gammaRule 1 γ B0 Pstar P)
    (hP' : 0 < P' ∧ B0 / P' = gammaRule 1 γ' B0 Pstar P') :
    P = P' ∧ gammaRule 1 γ B0 Pstar P = gammaRule 1 γ' B0 Pstar P' ∧ P = Pstar := by
  obtain ⟨Q, -, hu⟩ := (gamma_rule_determinate_iff hB hPs).mpr hγ
  obtain ⟨Q', -, hu'⟩ := (gamma_rule_determinate_iff hB hPs).mpr hγ'
  have h1 : P = Pstar := (hu P hP).trans (hu Pstar ⟨hPs, by simp [gammaRule]⟩).symm
  have h2 : P' = Pstar := (hu' P' hP').trans (hu' Pstar ⟨hPs, by simp [gammaRule]⟩).symm
  refine ⟨h1.trans h2.symm, ?_, h1⟩
  rw [h1, h2]
  simp [gammaRule]

/-- Cochrane (2023), p. 19, **observational equivalence**: a passive regime (`α = γ = 1`) whose
price level is set elsewhere at `P₁*`, and the active regime (`α = 1`, `γ = 0`) produce the same
observables `(P₁, s₁) = (P₁*, B₀/P₁*)`: `P₁*` is an equilibrium of the passive rule, and the
active rule's unique equilibrium is `P₁*`, with the same surplus. -/
theorem obs_equiv_two_period {B0 Pstar : ℝ} (hB : 0 < B0) (hPs : 0 < Pstar) :
    Pstar ∈ eqmSet B0 (gammaRule 1 1 B0 Pstar) ∧
      (∀ P, P ∈ eqmSet B0 (gammaRule 1 0 B0 Pstar) ↔ P = Pstar) ∧
      gammaRule 1 1 B0 Pstar Pstar = gammaRule 1 0 B0 Pstar Pstar ∧
      gammaRule 1 0 B0 Pstar Pstar = B0 / Pstar := by
  obtain ⟨Q, -, hu⟩ := (gamma_rule_determinate_iff (γ := 0) hB hPs).mpr (by norm_num)
  have hstar : Pstar ∈ eqmSet B0 (gammaRule 1 0 B0 Pstar) := ⟨hPs, by simp [gammaRule]⟩
  refine ⟨⟨hPs, by simp [gammaRule]⟩, fun P => ⟨fun h => (hu P h).trans (hu Pstar hstar).symm,
    fun h => h ▸ hstar⟩, by simp [gammaRule], by simp [gammaRule]⟩

/-- Cochrane (2023), p. 18: "one is tempted to run a regression, say `s₁ = a + γ(B₀/P₁) + u₁`
… the regression would estimate `γ = 1`": in every equilibrium of the active rule (1.13)
`s₁ = B₀/P₁*`, the data satisfy `s₁ = 0 + 1 · B₀/P₁` exactly. -/
theorem rule_regression_gamma_one {B0 Pstar P1 : ℝ} (hB : 0 < B0) (hPs : 0 < Pstar)
    (h : 0 < P1 ∧ B0 / P1 = B0 / Pstar) : B0 / Pstar = 0 + 1 * (B0 / P1) ∧ P1 = Pstar := by
  refine ⟨by rw [h.2]; ring, ?_⟩
  have h2 := h.2
  rw [div_eq_div_iff h.1.ne' hPs.ne'] at h2
  exact (mul_left_cancel₀ hB.ne' (by linarith : B0 * P1 = B0 * Pstar))

end Cochrane.TwoPeriodModel.ActivePassive
