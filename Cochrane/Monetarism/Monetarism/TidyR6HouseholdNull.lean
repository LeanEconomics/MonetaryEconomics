/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.CashInAdvance
import Monetarism.MoneyInUtility

/-!
# Why the first-order conditions are hypotheses for a general expectation system

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, (19.15)–(19.16), p. 441 and
(19.31)–(19.32), p. 450. For a general `ExpectationSystem` the theorems
`CashInAdvance.Stochastic.bond_price_19_32` and `MoneyInUtility.value_recursion` take the
household's first-order conditions (`Λ_t = βᵗu'(y_t)`, respectively (19.15)–(19.16)) as
hypotheses holding at every state. The project README attributed this to the absence of a
measure. This module makes the reason precise, and corrects it: the obstruction is not the
absence of a measure but the possible presence of states the date-0 expectation ignores.

## Main results

* `nullSystem`: an expectation system on two states (`Bool`) in which `E_0` reads only the state
  `true` (the state `false` has probability zero) and information is complete from date `1` on;
  it satisfies every axiom of `ExpectationSystem` and the pull-out property (`nullSystem_pullOut`);
  it describes the probability concentrated on `true`.
* `E0_blind`: `E_0` does not see the state `false`: two variables that agree at `true` have the
  same date-0 expectation. Any household objective `E_0[∑ βᵗu(c_t)]` and any date-0 valuation of
  a budget are therefore unchanged when prices, or the plan, are altered at `false`, so
  optimality cannot restrict them there.
* `bond_price_needs_foc`: on `nullSystem`, every hypothesis of
  `CashInAdvance.Stochastic.bond_price_19_32` holds except
  `Λ_t = βᵗu'(y_t)`, which holds at the state `true` at every date (the only state the household
  objective sees), and the conclusion (19.32) fails at date `1`.
* `value_recursion_needs_foc`: the same for `MoneyInUtility.value_recursion`: every hypothesis but
  the money first-order condition (19.16) holds, (19.16) holds at `true` at every date, and the
  value recursion fails at date `1`.

Hence for a general expectation system the first-order conditions must be assumed pointwise.
Where the date-0 expectation charges every node they are derived from optimality
(`CashInAdvance.TreeEuler.sdf_eq` and `MoneyInUtility.FootnoteTree.tree_foc_1913_1914` on finite
trees, linked to the general theorems by `CashInAdvanceMeasure.Link.link_bond_price` and
`MoneyInUtilityMeasure.Link.link_value_recursion`); on a probability space they are derived almost
surely (`CashInAdvanceMeasure.lambda_derived`, `TidyR6HouseholdCIA.cia_multiplier`,
`TidyR6HouseholdFOC.miu_multiplier`), which is all that can be derived.
-/

namespace Cochrane.Monetarism.TidyR6HouseholdNull

open Filter Topology

/-! ### An expectation system with a null state -/

/-- Cochrane (2023), Ch. 2, p. 29 (expectations with a null state): the linear map
`f ↦ (ω ↦ f true)`, the expectation under the probability concentrated on `true`. -/
def evalTrue : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ) where
  toFun f := fun _ => f true
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Cochrane (2023), Ch. 2, pp. 29–30: the expectation system on two states in which the date-0
expectation reads only the state `true` and every later expectation is the identity (the state is
revealed at date `1`). -/
def nullSystem : ExpectationSystem Bool where
  E t := if t = 0 then evalTrue else LinearMap.id
  const t c := by
    by_cases h : t = 0 <;> simp [h, evalTrue]
  mono t x y hxy := by
    by_cases h : t = 0
    · simp only [h, ↓reduceIte]
      exact fun _ => hxy true
    · simpa [h] using hxy
  tower := by
    intro s t hst x
    by_cases hs : s = 0
    · by_cases ht : t = 0
      · simp [hs, ht, evalTrue]
      · simp [hs, ht, evalTrue]
    · have ht : t ≠ 0 := by omega
      simp [hs, ht]
  known := by
    intro s t hst x
    by_cases ht : t = 0
    · have hs : s = 0 := by omega
      simp [hs, ht, evalTrue]
    · simp [ht]

/-- Cochrane (2023), Ch. 2, p. 29: the date-0 expectation of `nullSystem` reads the state
`true`. -/
theorem nullSystem_E0 (f : Bool → ℝ) : nullSystem.E 0 f = fun _ => f true := by
  simp [nullSystem, evalTrue]

/-- Cochrane (2023), Ch. 2, p. 29: from date `1` on, `nullSystem` has complete information. -/
theorem nullSystem_E_succ (t : ℕ) (f : Bool → ℝ) : nullSystem.E (t + 1) f = f := by
  simp [nullSystem]

/-- Cochrane (2023), Ch. 2, p. 30 (the pull-out property): `nullSystem` satisfies
`E_t[ay] = aE_t[y]` for `a` known at `t`. -/
theorem nullSystem_pullOut : nullSystem.PullOut := by
  intro t a y ha
  cases t with
  | zero =>
    rw [nullSystem_E0] at ha
    rw [nullSystem_E0, nullSystem_E0]
    funext ω
    have := congrFun ha ω
    simp only [Pi.mul_apply] at this ⊢
    rw [this]
  | succ k => simp [nullSystem_E_succ]

/-- Cochrane (2023), (19.9), p. 439, **the date-0 expectation is blind to the null state**: two
variables agreeing at `true` have the same date-0 expectation under `nullSystem`. So every
objective `E_0[∑ βᵗu(c_t)]` and every date-0 valuation `E_0[∑ Λ_t(·)]` is unchanged when the plan
or the prices are altered at the state `false`. -/
theorem E0_blind {f g : Bool → ℝ} (h : f true = g true) : nullSystem.E 0 f = nullSystem.E 0 g := by
  rw [nullSystem_E0, nullSystem_E0, h]

/-! ### (19.32) needs the pointwise first-order condition -/

/-- Cochrane (2023), (19.31), p. 450 (counterexample prices): `Λ_0 = 1`, and from date `1` on
`Λ_t = βᵗ` at the state `true` but `(2β)ᵗ` at the null state `false`. -/
noncomputable def cxΛ (β : ℝ) (t : ℕ) (ω : Bool) : ℝ :=
  if t = 0 then 1 else if ω then β ^ t else (2 * β) ^ t

/-- Cochrane (2023), (19.32), p. 450 (counterexample): the bond price defined by the pricing
equation `Λ_tQ_t/P_t = E_t[Λ_{t+1}/P_{t+1}]` with `P = 1`. -/
noncomputable def cxQ (β : ℝ) (t : ℕ) (ω : Bool) : ℝ :=
  nullSystem.E t (cxΛ β (t + 1) / fun _ => (1 : ℝ)) ω * 1 / cxΛ β t ω

/-- Cochrane (2023), (19.31)–(19.32), p. 450, **the pointwise first-order condition cannot be
dropped from `CashInAdvance.Stochastic.bond_price_19_32`, and is not implied by optimality**:
on `nullSystem` (with the pull-out property), with `0 < β`, marginal utility `u'(y_t) = 1`
(adapted, positive), price level `1` (adapted, positive) and the bond price `cxQ` satisfying the
pricing equation, the identity `Λ_t = βᵗu'(y_t)` holds at the state `true` at every date — the
only state the household's date-0 objective sees (`E0_blind`) — and yet the conclusion of
`CashInAdvance.Stochastic.bond_price_19_32`,
`Q_t = βE_t[(u'(y_{t+1})/u'(y_t))(P_t/P_{t+1})]`, fails at date `1`. -/
theorem bond_price_needs_foc {β : ℝ} (hβ : 0 < β) :
    nullSystem.PullOut ∧ (∀ t ω, 0 < (fun (_ : ℕ) (_ : Bool) => (1 : ℝ)) t ω) ∧
      nullSystem.Adapted (fun _ _ => 1) ∧ nullSystem.Adapted (fun _ _ => 1) ∧
      (∀ t ω, 0 < (fun (_ : ℕ) (_ : Bool) => (1 : ℝ)) t ω) ∧
      (∀ t, cxΛ β t * cxQ β t / (fun _ _ => 1) t =
        nullSystem.E t (cxΛ β (t + 1) / (fun _ _ => (1 : ℝ)) (t + 1))) ∧
      (∀ t, cxΛ β t true = β ^ t * 1) ∧
      ¬ (cxQ β 1 = β • nullSystem.E 1 ((fun _ _ => (1 : ℝ)) 2 / (fun _ _ => (1 : ℝ)) 1 *
        ((fun _ _ => (1 : ℝ)) 1 / (fun _ _ => (1 : ℝ)) 2))) := by
  have hpos : ∀ t ω, 0 < cxΛ β t ω := fun t ω => by
    unfold cxΛ
    split_ifs <;> positivity
  refine ⟨nullSystem_pullOut, fun _ _ => one_pos, fun t => nullSystem.const t 1,
    fun t => nullSystem.const t 1, fun _ _ => one_pos, fun t => ?_, fun t => ?_, ?_⟩
  · funext ω
    have := (hpos t ω).ne'
    simp only [Pi.mul_apply, Pi.div_apply, cxQ]
    field_simp
  · cases t with
    | zero => simp [cxΛ]
    | succ k => simp [cxΛ]
  · intro h
    have h1 := congrFun h false
    simp only [cxQ, nullSystem_E_succ, cxΛ, Pi.smul_apply, smul_eq_mul, Pi.mul_apply,
      Pi.div_apply] at h1
    norm_num at h1
    have hβ' : β ≠ 0 := hβ.ne'
    field_simp at h1
    nlinarith

/-! ### The value recursion needs the pointwise money first-order condition -/

/-- Cochrane (2023), (19.16), p. 441 (counterexample): marginal utility of money `1 − β` at the
state `true` and at date `0`, but `0` at the null state from date `1` on. -/
noncomputable def cxUm (β : ℝ) (t : ℕ) (ω : Bool) : ℝ := if t = 0 ∨ ω then 1 - β else 0

/-- Cochrane (2023), (19.15)–(19.16), p. 441, **the pointwise money first-order condition cannot
be dropped from `MoneyInUtility.value_recursion`**: on `nullSystem`, with `0 < β < 1`, marginal
utility of consumption `1`, price level `1` and nominal rate `i = 1/β − 1`, the bond-pricing
condition (19.15) holds at every state, the money condition (19.16) `u_m/u_c = i/(1 + i)` holds at
the state `true` at every date (the only state the date-0 objective sees), every other hypothesis
of `MoneyInUtility.value_recursion` holds, and yet the value of money `v_t = u_c(t)/P_t` violates
the recursion `v_t = u_m(t)/P_t + βE_tv_{t+1}` at date `1`. -/
theorem value_recursion_needs_foc {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    nullSystem.PullOut ∧
      (∀ t, nullSystem.E t ((fun _ _ => (1 : ℝ)) t / (fun _ _ => (1 : ℝ)) t) =
        (fun _ _ => (1 : ℝ)) t / (fun _ _ => (1 : ℝ)) t) ∧
      (∀ t, nullSystem.E t (β • ((fun _ _ => (1 : ℝ)) (t + 1) / (fun _ _ => (1 : ℝ)) t *
        ((fun _ _ => (1 : ℝ)) t / (fun _ _ => (1 : ℝ)) (t + 1)))) =
          1 / (1 + (fun (_ : ℕ) (_ : Bool) => 1 / β - 1) t)) ∧
      ((1 : ℝ) + (1 / β - 1) ≠ 0) ∧
      (∀ t, cxUm β t true / 1 = (1 / β - 1) / (1 + (1 / β - 1))) ∧
      ¬ ForwardSolution.Solves nullSystem β (fun t => cxUm β t / fun _ => 1)
        (fun _ => (fun _ => (1 : ℝ)) / fun _ => 1) := by
  refine ⟨nullSystem_pullOut, fun t => nullSystem.const t _, fun t => ?_, by
    have : (1 : ℝ) + (1 / β - 1) = 1 / β := by ring
    rw [this]
    positivity, fun t => ?_, ?_⟩
  · have e : (β • ((fun _ _ => (1 : ℝ)) (t + 1) / (fun _ _ => (1 : ℝ)) t *
        ((fun _ _ => (1 : ℝ)) t / (fun _ _ => (1 : ℝ)) (t + 1))) : Bool → ℝ) = fun _ => β := by
      funext ω
      simp
    rw [e, nullSystem.const]
    funext ω
    simp only [Pi.div_apply, Pi.add_apply, Pi.one_apply]
    field_simp
    ring
  · simp only [cxUm, or_true, ↓reduceIte, div_one]
    field_simp
    ring
  · intro h
    have h1 := congrFun (h 1) false
    have h0 : cxUm β 1 false = 0 := by simp [cxUm]
    simp only [nullSystem_E_succ, Pi.div_apply] at h1
    norm_num [h0] at h1
    linarith

end Cochrane.Monetarism.TidyR6HouseholdNull
