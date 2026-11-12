/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TwoPeriodModel.ActivePassive

/-!
# The general-`α` `γ`-rule with a random target

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 1, §1.9, pp. 18–19.

The surplus rule `s₁ = α B₀/P₁* + γ(B₀/P₁ − B₀/P₁*)` with a random price-level target `P₁*`
(and, more generally, random coefficients `α, γ` and random debt `B₀`), imposed state by state.
`ActivePassive.gamma_rule_random` treats only `α = 1`, and `ActivePassive.gamma_rule_general_iff`
treats general `α` only for a deterministic target and `γ ≠ 1`. Here:

## Main results

* `gamma_rule_full_iff`: deterministic case, **all** `γ`: a unique equilibrium iff `γ ≠ 1` and
  `(α − γ)/(1 − γ) > 0`, equivalently (`gamma_cond_iff_mul_pos`) `(α − γ)(1 − γ) > 0`.
* `existsUnique_pi_iff`: a random variable is the unique state-by-state solution iff every
  state has a unique solution (a general lemma, proved here).
* `gamma_random_existsUnique_iff`: random `α, γ, B₀ > 0, P₁* > 0`: there is exactly one positive
  random price level satisfying (1.14) under the rule **iff** in every state `γ(ω) ≠ 1` and
  `(α(ω) − γ(ω))/(1 − γ(ω)) > 0`.
* `gamma_random_valuation_iff`: under that condition the equilibrium is
  `P₁ = P₁*(1 − γ)/(α − γ)` state by state.
* `gamma_random_const_iff`: deterministic `α, γ`, random target (`Ω` nonempty): unique iff
  `(α − γ)(1 − γ) > 0` — the deterministic condition, independent of the target's
  distribution; `gamma_random_known` (the equilibrium is known at date 1 when the target is);
  `gamma_random_alpha_one` recovers `ActivePassive.gamma_rule_random`.
* `gamma_random_one_state_fails`: the condition must hold in **every** state: a random `γ`
  equal to `1` in a single state destroys uniqueness even if `γ = 0` elsewhere.
-/

namespace Cochrane.TwoPeriodModel.TidyR5GammaRandom

open Cochrane.TwoPeriodModel.TwoPeriod Cochrane.TwoPeriodModel.ActivePassive

variable {Ω : Type*}

/-- Cochrane (2023), §1.9, pp. 18–19: the coefficient `(α − γ)/(1 − γ)` with which the
`γ`-rule ties the value of debt to its target: `B₀/P₁ = ((α − γ)/(1 − γ)) · B₀/P₁*`. -/
noncomputable def gammaCoef (α γ : ℝ) : ℝ := (α - γ) / (1 - γ)

/-- Cochrane (2023), §1.9, pp. 18–19: `γ ≠ 1` and `(α − γ)/(1 − γ) > 0` iff
`(α − γ)(1 − γ) > 0`. -/
theorem gamma_cond_iff_mul_pos (α γ : ℝ) :
    (γ ≠ 1 ∧ 0 < gammaCoef α γ) ↔ 0 < (α - γ) * (1 - γ) := by
  unfold gammaCoef
  constructor
  · rintro ⟨-, h⟩
    rcases div_pos_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact mul_pos h1 h2
    · exact mul_pos_of_neg_of_neg h1 h2
  · intro h
    rcases mul_pos_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun hγ => by rw [hγ, sub_self] at h2; exact lt_irrefl 0 h2, div_pos h1 h2⟩
    · exact ⟨fun hγ => by rw [hγ, sub_self] at h2; exact lt_irrefl 0 h2,
        div_pos_of_neg_of_neg h1 h2⟩

/-- Cochrane (2023), §1.9, pp. 18–19, deterministic target, **every** `γ` (`B₀ > 0`,
`P₁* > 0`): the `γ`-rule has a unique equilibrium iff `γ ≠ 1` and `(α − γ)/(1 − γ) > 0`
(`γ = 1` gives either every `P₁ > 0` or no equilibrium). -/
theorem gamma_rule_full_iff {α γ B0 Pstar : ℝ} (hB : 0 < B0) (hPs : 0 < Pstar) :
    (∃! P : ℝ, 0 < P ∧ B0 / P = gammaRule α γ B0 Pstar P) ↔ γ ≠ 1 ∧ 0 < gammaCoef α γ := by
  by_cases hγ : γ = 1
  · subst hγ
    simp only [ne_eq, not_true_eq_false, false_and, iff_false]
    intro hu
    by_cases hα : α = 1
    · subst hα
      exact (gamma_rule_determinate_iff hB hPs).mp hu rfl
    · obtain ⟨P, hP, -⟩ := hu
      have hmem : P ∈ eqmSet B0 (gammaRule α 1 B0 Pstar) := hP
      rw [gamma_eqmSet_empty hα hB.ne' hPs.ne'] at hmem
      exact hmem
  · rw [gamma_rule_general_iff hB hPs hγ]
    exact ⟨fun h => ⟨hγ, h⟩, fun h => h.2⟩

/-- Cochrane (2023), §1.9, pp. 18–19, deterministic target: under `γ ≠ 1` and
`(α − γ)/(1 − γ) > 0`, a positive `P₁` is an equilibrium iff `P₁ = P₁*/((α − γ)/(1 − γ))`,
i.e. `P₁ = P₁*(1 − γ)/(α − γ)`. -/
theorem gamma_rule_eq_iff {α γ B0 Pstar P : ℝ} (hB : 0 < B0) (hPs : 0 < Pstar) (hγ : γ ≠ 1)
    (hc : 0 < gammaCoef α γ) (hP : 0 < P) :
    B0 / P = gammaRule α γ B0 Pstar P ↔ P = Pstar / gammaCoef α γ := by
  have h1 : (1 - γ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  have key : B0 / P = gammaRule α γ B0 Pstar P ↔ B0 / P = gammaCoef α γ * (B0 / Pstar) := by
    simp only [gammaRule, gammaCoef]
    rw [div_mul_eq_mul_div, eq_div_iff h1]
    constructor <;> intro h <;> linarith
  have hQ : 0 < Pstar / gammaCoef α γ := div_pos hPs hc
  have hsol : B0 / (Pstar / gammaCoef α γ) = gammaCoef α γ * (B0 / Pstar) := by
    field_simp
  rw [key, ← hsol, div_eq_div_iff hP.ne' hQ.ne']
  constructor
  · intro h; exact mul_left_cancel₀ hB.ne' (by linarith)
  · intro h; rw [h]

/-- Cochrane (2023), §1.9, pp. 18–19, the closed form: `P₁*/((α − γ)/(1 − γ)) =
P₁*(1 − γ)/(α − γ)`. -/
theorem div_gammaCoef (α γ Pstar : ℝ) : Pstar / gammaCoef α γ = Pstar * (1 - γ) / (α - γ) := by
  unfold gammaCoef
  rw [div_div_eq_mul_div]

/-- Cochrane (2023), §1.9, p. 19 (a general lemma used to pass from state-by-state to random
equilibria): for a state-by-state condition `R ω p`, there is exactly one random variable
`P : Ω → ℝ` with `R ω (P ω)` in every state iff every state has exactly one solution. -/
theorem existsUnique_pi_iff (R : Ω → ℝ → Prop) :
    (∃! P : Ω → ℝ, ∀ ω, R ω (P ω)) ↔ ∀ ω, ∃! p : ℝ, R ω p := by
  classical
  constructor
  · rintro ⟨P, hP, hu⟩ ω
    refine ⟨P ω, hP ω, fun p hp => ?_⟩
    have h := hu (Function.update P ω p) (fun ω' => by
      by_cases h : ω' = ω
      · subst h; simpa using hp
      · simpa [h] using hP ω')
    have := congrFun h ω
    simpa using this
  · intro h
    choose P hP hu using h
    exact ⟨P, hP, fun Q hQ => funext fun ω => hu ω (Q ω) (hQ ω)⟩

/-- Cochrane (2023), §1.9, pp. 18–19: the `γ`-rule state by state, with random coefficients
`α, γ`, random debt `B₀` and a random target `P₁*`:
`s₁(ω) = α(ω)B₀(ω)/P₁*(ω) + γ(ω)(B₀(ω)/P₁(ω) − B₀(ω)/P₁*(ω))`. -/
noncomputable def gammaRuleRandom (α γ B0 Pstar P1 : Ω → ℝ) : Ω → ℝ :=
  fun ω => gammaRule (α ω) (γ ω) (B0 ω) (Pstar ω) (P1 ω)

/-- Cochrane (2023), §1.9, pp. 18–19, **general `α`, random target** (and random `α, γ`;
`B₀, P₁* > 0` in every state): there is exactly one positive random price level satisfying
(1.14) `B₀/P₁ = s₁` under the `γ`-rule iff in every state `γ(ω) ≠ 1` and
`(α(ω) − γ(ω))/(1 − γ(ω)) > 0`. -/
theorem gamma_random_existsUnique_iff {α γ B0 Pstar : Ω → ℝ} (hB : ∀ ω, 0 < B0 ω)
    (hPs : ∀ ω, 0 < Pstar ω) :
    (∃! P1 : Ω → ℝ, (∀ ω, 0 < P1 ω) ∧ Valuation1 B0 P1 (gammaRuleRandom α γ B0 Pstar P1)) ↔
      ∀ ω, γ ω ≠ 1 ∧ 0 < gammaCoef (α ω) (γ ω) := by
  have e : ∀ P1 : Ω → ℝ, ((∀ ω, 0 < P1 ω) ∧
      Valuation1 B0 P1 (gammaRuleRandom α γ B0 Pstar P1)) ↔
      ∀ ω, 0 < P1 ω ∧ B0 ω / P1 ω = gammaRule (α ω) (γ ω) (B0 ω) (Pstar ω) (P1 ω) := by
    intro P1
    simp only [Valuation1, gammaRuleRandom, funext_iff, Pi.div_apply]
    exact ⟨fun h ω => ⟨h.1 ω, h.2 ω⟩, fun h => ⟨fun ω => (h ω).1, fun ω => (h ω).2⟩⟩
  simp only [e]
  rw [existsUnique_pi_iff (fun ω p => 0 < p ∧ B0 ω / p =
    gammaRule (α ω) (γ ω) (B0 ω) (Pstar ω) p)]
  exact forall_congr' fun ω => gamma_rule_full_iff (hB ω) (hPs ω)

/-- Cochrane (2023), §1.9, pp. 18–19, random target: when every state satisfies `γ(ω) ≠ 1` and
`(α(ω) − γ(ω))/(1 − γ(ω)) > 0`, a positive random `P₁` is an equilibrium iff
`P₁ = P₁*(1 − γ)/(α − γ)` state by state. -/
theorem gamma_random_valuation_iff {α γ B0 Pstar P1 : Ω → ℝ} (hB : ∀ ω, 0 < B0 ω)
    (hPs : ∀ ω, 0 < Pstar ω) (hcond : ∀ ω, γ ω ≠ 1 ∧ 0 < gammaCoef (α ω) (γ ω))
    (hP1 : ∀ ω, 0 < P1 ω) :
    Valuation1 B0 P1 (gammaRuleRandom α γ B0 Pstar P1) ↔
      P1 = fun ω => Pstar ω * (1 - γ ω) / (α ω - γ ω) := by
  simp only [Valuation1, gammaRuleRandom, funext_iff, Pi.div_apply]
  refine forall_congr' fun ω => ?_
  rw [gamma_rule_eq_iff (hB ω) (hPs ω) (hcond ω).1 (hcond ω).2 (hP1 ω), div_gammaCoef]

/-- Cochrane (2023), §1.9, pp. 18–19, **deterministic `α, γ` with a random target** (`Ω`
nonempty, `B₀, P₁* > 0`): a unique equilibrium iff `(α − γ)(1 − γ) > 0` — the same condition
as with a deterministic target, whatever the distribution of `P₁*`. -/
theorem gamma_random_const_iff [Nonempty Ω] {α γ : ℝ} {B0 Pstar : Ω → ℝ}
    (hB : ∀ ω, 0 < B0 ω) (hPs : ∀ ω, 0 < Pstar ω) :
    (∃! P1 : Ω → ℝ, (∀ ω, 0 < P1 ω) ∧
      Valuation1 B0 P1 (gammaRuleRandom (fun _ => α) (fun _ => γ) B0 Pstar P1)) ↔
      0 < (α - γ) * (1 - γ) := by
  rw [gamma_random_existsUnique_iff hB hPs, ← gamma_cond_iff_mul_pos]
  exact ⟨fun h => h (Classical.arbitrary Ω), fun h _ => h⟩

/-- Cochrane (2023), §1.3, p. 8 and §1.9, p. 19: with deterministic `α, γ` the equilibrium
price level `P₁ = ((1 − γ)/(α − γ)) P₁*` is known at date 1 whenever the target is. -/
theorem gamma_random_known (𝔼 : ExpectationSystem Ω) {α γ : ℝ} {Pstar : Ω → ℝ}
    (hk : Known 𝔼 1 Pstar) :
    Known 𝔼 1 (fun ω => Pstar ω * (1 - γ) / (α - γ)) := by
  have e : (fun ω => Pstar ω * (1 - γ) / (α - γ)) = ((1 - γ) / (α - γ)) • Pstar := by
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [e]
  exact known_smul 𝔼 _ hk

/-- Cochrane (2023), §1.9, pp. 18–19: with `α = 1` the condition reduces to `γ ≠ 1` and the
equilibrium is `P₁ = P₁*`, recovering `ActivePassive.gamma_rule_random` (`Ω` nonempty). -/
theorem gamma_random_alpha_one [Nonempty Ω] {γ : ℝ} {B0 Pstar : Ω → ℝ}
    (hB : ∀ ω, 0 < B0 ω) (hPs : ∀ ω, 0 < Pstar ω) :
    ((∃! P1 : Ω → ℝ, (∀ ω, 0 < P1 ω) ∧
      Valuation1 B0 P1 (gammaRuleRandom (fun _ => 1) (fun _ => γ) B0 Pstar P1)) ↔ γ ≠ 1) ∧
    (γ ≠ 1 → ∀ P1 : Ω → ℝ, (∀ ω, 0 < P1 ω) →
      (Valuation1 B0 P1 (gammaRuleRandom (fun _ => 1) (fun _ => γ) B0 Pstar P1) ↔
        P1 = Pstar)) := by
  have hc : ∀ γ : ℝ, γ ≠ 1 → gammaCoef 1 γ = 1 := fun γ hγ =>
    div_self (sub_ne_zero.mpr (Ne.symm hγ))
  refine ⟨?_, fun hγ P1 hP1 => ?_⟩
  · rw [gamma_random_existsUnique_iff hB hPs]
    constructor
    · intro h; exact (h (Classical.arbitrary Ω)).1
    · intro hγ _; exact ⟨hγ, by rw [hc γ hγ]; exact one_pos⟩
  · rw [gamma_random_valuation_iff hB hPs (fun _ => ⟨hγ, by rw [hc γ hγ]; exact one_pos⟩) hP1]
    have h1 : (1 - γ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
    have e : (fun ω => Pstar ω * (1 - γ) / (1 - γ)) = Pstar := by
      funext ω; field_simp
    rw [e]

/-- Cochrane (2023), §1.9, pp. 18–19, counterexample: the condition must hold in **every**
state. On `Ω = Bool`, with `α = 1`, `B₀ = P₁* = 1`, the random `γ` equal to `1` in state
`true` and `0` in state `false` (determinate in state `false`) gives no unique equilibrium. -/
theorem gamma_random_one_state_fails :
    ¬ ∃! P1 : Bool → ℝ, (∀ ω, 0 < P1 ω) ∧ Valuation1 (fun _ => 1) P1
      (gammaRuleRandom (fun _ => 1) (fun ω => if ω then 1 else 0) (fun _ => 1) (fun _ => 1)
        P1) := by
  rw [gamma_random_existsUnique_iff (fun _ => one_pos) (fun _ => one_pos)]
  intro h
  exact (h true).1 (by simp)

end Cochrane.TwoPeriodModel.TidyR5GammaRandom
