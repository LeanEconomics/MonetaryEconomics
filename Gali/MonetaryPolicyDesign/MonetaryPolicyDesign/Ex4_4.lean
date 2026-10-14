/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MonetaryPolicyDesign.Expectations
import Mathlib.Probability.Moments.Variance

/-!
# Exercise 4.4: interest rate versus money supply rules

Galí (2015), Chapter 4, Exercise 4.4, pp. 122–123. The economy is the dynamic IS equation
`ỹ_t = E_t ỹ_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − r^n_t)`, the New Keynesian Phillips curve
`π_t = β E_t π_{t+1} + κ ỹ_t` and the money demand `m_t − p_t = y_t − η i_t`, with
`y_t = ỹ_t + y^n_t`. The natural rate `r^n` and natural output `y^n` are exogenous; the central
bank minimises `ϑ var(ỹ_t) + var(π_t)`.

## (a) An interest rate rule

* `loss_nonneg`, `loss_zero`, `zero_minimises_loss`: the outcome `ỹ = π = 0` attains the lowest
  possible loss, zero (for every probability law of the outcomes and every `ϑ ≥ 0`).
* `zero_equilibrium_iff`: `ỹ = π = 0` satisfies the IS equation and the Phillips curve iff
  `i_t = r^n_t` (eqs. (4)–(5) and p. 103).
* The rule `i_t = r^n_t + φ_π π_t + φ_y ỹ_t` (eq. (11)): `rule_iff_solves` writes the equilibrium
  as `x_t = A_T E_t x_{t+1}` with `A_T` of eq. (13); `schurStable_AT_iff`: for `φ_π, φ_y ≥ 0`
  both eigenvalues of `A_T` lie inside the unit circle iff condition (14),
  `κ (φ_π − 1) + (1 − β) φ_y > 0` (restated from the Chapter 3 project).
* `rule_implements`: under (14) the outcome `ỹ = π = 0, i = r^n` is an equilibrium and it is the
  only bounded one; `rule_not_unique`: without (14) there is a second bounded equilibrium;
  `implements_uniquely_iff`: the rule implements the optimum uniquely iff (14) holds.

## (b) The money supply under the optimal policy

* `price_level_const`: with `π = 0` the price level stays at its initial value `p*`.
* `money_path_optimal`: in every equilibrium with `ỹ = π = 0`, `m_t = p* + y^n_t − η r^n_t`.
* `constant_money_suboptimal`: a constant money supply is consistent with the optimum only if
  `y^n_t − η r^n_t` is constant; `constant_money_not_optimal`: when `y^n − η r^n` moves, no
  equilibrium under a constant money supply attains `ỹ = π = 0`.
* `constant_money_optimal_of_const`: conversely, when `y^n − η r^n` is constant, a constant
  money supply supports the optimal outcome.

## (c) A money supply rule that implements the optimum

* `moneyRule_equilibrium`: under the rule `m_t = p* + y^n_t − η r^n_t` the optimal outcome
  (`ỹ = π = 0`, `p = p*`, `i = r^n`) is an equilibrium.
* `moneyRule_iff_interestRule`: given money demand and `η > 0`, the money rule is equivalent to
  the implicit interest rate rule `i_t = r^n_t + η⁻¹ (ỹ_t + p_t − p*)`, a rule responding to the
  output gap and to the price level.
* `MoneyRuleUniqueness`: whether the optimum is the *unique* bounded equilibrium under the money
  rule is a three-variable determinacy question (the price level is predetermined), the one of
  Galí Chapter 3 footnote 14. It is recorded here as a claim and is **not yet claimed**: the
  project defers it.
-/

namespace Gali.MonetaryPolicyDesign.Ex4_4

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The model -/

/-- Galí (2015), Ex. 4.4, p. 122 (eq. (6), p. 104): the dynamic IS equation
`ỹ_t = E_t ỹ_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − r^n_t)`. -/
def DIS (σ : ℝ) (rn ygap infl i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ygap t = 𝔼.E t (ygap (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - rn t)

/-- Galí (2015), Ex. 4.4, p. 122 (eq. (7), p. 104): the New Keynesian Phillips curve
`π_t = β E_t π_{t+1} + κ ỹ_t`. -/
def NKPC (β κ : ℝ) (ygap infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t

/-- Galí (2015), Ex. 4.4, p. 122: the non-policy block, the IS equation and the Phillips curve. -/
def Block (β σ κ : ℝ) (rn ygap infl i : ℕ → Ω → ℝ) : Prop :=
  DIS 𝔼 σ rn ygap infl i ∧ NKPC 𝔼 β κ ygap infl

/-! ### (a) The optimal policy and an interest rate rule -/

/-- Galí (2015), Ex. 4.4, p. 122: the central bank's loss `ϑ var(ỹ_t) + var(π_t)` at date `t`,
for a probability law `μ` of the outcomes. -/
noncomputable def loss [MeasurableSpace Ω] (μ : Measure Ω) (ϑ : ℝ) (ygap infl : ℕ → Ω → ℝ)
    (t : ℕ) : ℝ :=
  ϑ * variance (ygap t) μ + variance (infl t) μ

/-- Galí (2015), Ex. 4.4, p. 122: the loss is nonnegative for `ϑ ≥ 0`. -/
theorem loss_nonneg [MeasurableSpace Ω] (μ : Measure Ω) {ϑ : ℝ} (hϑ : 0 ≤ ϑ)
    (ygap infl : ℕ → Ω → ℝ) (t : ℕ) : 0 ≤ loss μ ϑ ygap infl t :=
  add_nonneg (mul_nonneg hϑ (variance_nonneg _ _)) (variance_nonneg _ _)

/-- Galí (2015), Ex. 4.4, p. 122: the outcome `ỹ = π = 0` has zero loss. -/
theorem loss_zero [MeasurableSpace Ω] (μ : Measure Ω) (ϑ : ℝ) (t : ℕ) :
    loss μ ϑ (fun _ => 0) (fun _ => 0) t = 0 := by
  simp [loss, variance_zero]

/-- Galí (2015), Ex. 4.4(a), p. 122, with eqs. (4)–(5), p. 103: the outcome `ỹ = π = 0`
minimises the loss at every date against every other outcome. -/
theorem zero_minimises_loss [MeasurableSpace Ω] (μ : Measure Ω) {ϑ : ℝ} (hϑ : 0 ≤ ϑ)
    (ygap infl : ℕ → Ω → ℝ) (t : ℕ) :
    loss μ ϑ (fun _ => 0) (fun _ => 0) t ≤ loss μ ϑ ygap infl t := by
  rw [loss_zero]; exact loss_nonneg μ hϑ ygap infl t

/-- Galí (2015), eqs. (4)–(5) and p. 103 (Ex. 4.4(a)): the optimal outcome `ỹ = π = 0` satisfies
the IS equation and the Phillips curve if and only if `i_t = r^n_t` for all `t`. -/
theorem zero_equilibrium_iff {β σ κ : ℝ} (hσ : σ ≠ 0) (rn i : ℕ → Ω → ℝ) :
    Block 𝔼 β σ κ rn (fun _ => 0) (fun _ => 0) i ↔ i = rn := by
  constructor
  · rintro ⟨hd, -⟩
    funext t ω
    have e := congrFun (hd t) ω
    simp only [map_zero, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at e
    have : σ⁻¹ * (i t ω - rn t ω) = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_left (inv_ne_zero hσ)
    linarith
  · rintro rfl
    refine ⟨fun t => ?_, fun t => ?_⟩
    · funext ω; simp
    · funext ω; simp

/-- Galí (2015), eq. (11), p. 105: the interest rate rule `i_t = r^n_t + φ_π π_t + φ_y ỹ_t`. -/
def Rule (φπ φy : ℝ) (rn ygap infl i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = rn t + φπ • infl t + φy • ygap t

/-- Galí (2015), eq. (13), p. 105: `Ω = 1/(σ + φ_y + κ φ_π)`. -/
noncomputable def omega (σ κ φπ φy : ℝ) : ℝ := 1 / (σ + φy + κ * φπ)

/-- Galí (2015), eq. (13), p. 105: `A_T = Ω [[σ, 1 − βφ_π], [σκ, κ + β(σ + φ_y)]]`. -/
noncomputable def AT (β σ κ φπ φy : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![omega σ κ φπ φy * σ, omega σ κ φπ φy * (1 - β * φπ);
    omega σ κ φπ φy * (σ * κ), omega σ κ φπ φy * (κ + β * (σ + φy))]

/-- Galí (2015), eq. (12): the stacked vector `x_t = (ỹ_t, π_t)`. -/
def stack (ygap infl : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![ygap t, infl t]

/-- Galí (2015), eq. (12), p. 105: under rule (11) the IS equation and the Phillips curve hold
iff `x_t = A_T E_t x_{t+1}`, provided `σ ≠ 0` and `σ + φ_y + κ φ_π ≠ 0` (the natural rate drops
out). -/
theorem rule_iff_solves {β σ κ φπ φy : ℝ} (hσ : σ ≠ 0) (hS : σ + φy + κ * φπ ≠ 0)
    {rn ygap infl i : ℕ → Ω → ℝ} (hr : Rule φπ φy rn ygap infl i) :
    Block 𝔼 β σ κ rn ygap infl i ↔ 𝔼.Solves (AT β σ κ φπ φy) 0 (stack ygap infl) := by
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  constructor
  · rintro ⟨hd, hp⟩ t j
    funext ω
    have e1 := congrFun (hd t) ω
    have e2 := congrFun (hp t) ω
    have r := congrFun (hr t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 r
    have e1' : (σ + φy) * ygap t ω + φπ * infl t ω =
        σ * 𝔼.E t (ygap (t + 1)) ω + 𝔼.E t (infl (t + 1)) ω := by
      linear_combination σ * e1 - r - (i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) * hinv
    fin_cases j
    · simp [stack, AT, omega]
      field_simp
      linear_combination e1' - φπ * e2
    · simp [stack, AT, omega]
      field_simp
      linear_combination κ * e1' + (σ + φy) * e2
  · intro h
    have key : ∀ t ω, (σ + φy) * ygap t ω + φπ * infl t ω =
          σ * 𝔼.E t (ygap (t + 1)) ω + 𝔼.E t (infl (t + 1)) ω ∧
        infl t ω = β * 𝔼.E t (infl (t + 1)) ω + κ * ygap t ω := by
      intro t ω
      have h0 := congrFun (h t 0) ω
      have h1 := congrFun (h t 1) ω
      simp only [stack, Fin.isValue, Matrix.cons_val_zero, AT, omega, one_div, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero] at h0 h1
      field_simp at h0 h1
      constructor
      · apply mul_left_cancel₀ hS
        linear_combination (σ + φy) * h0 + φπ * h1
      · apply mul_left_cancel₀ hS
        linear_combination h1 - κ * h0
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have e := (key t ω).1
      have r := congrFun (hr t) ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at r ⊢
      rw [r]
      field_simp
      linear_combination e
    · have e := (key t ω).2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact e

/-- Galí (2015), p. 105: the trace of `A_T` is `(σ (1 + β) + κ + β φ_y)/(σ + φ_y + κ φ_π)`. -/
theorem tr2_AT {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0) :
    tr2 (AT β σ κ φπ φy) = (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) := by
  simp only [tr2, AT, omega, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), p. 105: the determinant of `A_T` is `σ β/(σ + φ_y + κ φ_π)`. -/
theorem det2_AT {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0) :
    det2 (AT β σ κ φπ φy) = σ * β / (σ + φy + κ * φπ) := by
  simp only [det2, AT, omega, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- **Condition (14)** (Galí 2015, p. 106; Bullard–Mitra): for `σ, κ > 0`, `0 < β < 1` and
`φ_π, φ_y ≥ 0`, both eigenvalues of `A_T` lie inside the unit circle iff
`κ (φ_π − 1) + (1 − β) φ_y > 0` (restated from the Chapter 3 project). -/
theorem schurStable_AT_iff {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    SchurStable (tr2 (AT β σ κ φπ φy)) (det2 (AT β σ κ φπ φy)) ↔
      0 < κ * (φπ - 1) + (1 - β) * φy := by
  have hS : 0 < σ + φy + κ * φπ := by positivity
  rw [tr2_AT hS.ne', det2_AT hS.ne']
  have hD0 : 0 < σ * β / (σ + φy + κ * φπ) := by positivity
  have hD1 : σ * β / (σ + φy + κ * φπ) < 1 := by
    rw [div_lt_one hS]; nlinarith
  have hT0 : 0 < (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) := by positivity
  unfold SchurStable
  rw [abs_of_pos hD0, abs_of_pos hT0]
  have key : (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) < 1 + σ * β / (σ + φy + κ * φπ)
      ↔ σ * (1 + β) + κ + β * φy < σ + φy + κ * φπ + σ * β := by
    rw [one_add_div hS.ne', div_lt_div_iff_of_pos_right hS]
  rw [key]
  constructor
  · rintro ⟨-, h⟩; linarith
  · intro h; exact ⟨hD1, by linarith⟩

/-- Two bounded processes stack to a bounded vector process. -/
theorem boundedVec_stack {a b : ℕ → Ω → ℝ} (ha : BoundedProc a) (hb : BoundedProc b) :
    BoundedVec (stack a b) := by
  obtain ⟨M₁, h₁⟩ := ha
  obtain ⟨M₂, h₂⟩ := hb
  refine ⟨max M₁ M₂, fun t j ω => ?_⟩
  fin_cases j
  · exact (h₁ t ω).trans (le_max_left _ _)
  · exact (h₂ t ω).trans (le_max_right _ _)

/-- Two adapted processes stack to an adapted vector process. -/
theorem adaptedVec_stack {a b : ℕ → Ω → ℝ} (ha : 𝔼.Adapted a) (hb : 𝔼.Adapted b) :
    𝔼.AdaptedVec (stack a b) := by
  intro t j
  fin_cases j
  · exact ha t
  · exact hb t

/-- Galí (2015), Ex. 4.4(a), pp. 105–106: a bounded adapted equilibrium under rule (11), with
`ỹ`, `π` and `i` all determined. -/
def RuleEquilibrium (β σ κ φπ φy : ℝ) (rn ygap infl i : ℕ → Ω → ℝ) : Prop :=
  Block 𝔼 β σ κ rn ygap infl i ∧ Rule φπ φy rn ygap infl i ∧ 𝔼.Adapted ygap ∧
    𝔼.Adapted infl ∧ BoundedProc ygap ∧ BoundedProc infl

/-- **Ex. 4.4(a)** (Galí 2015, pp. 105–106): under condition (14) the rule
`i_t = r^n_t + φ_π π_t + φ_y ỹ_t` implements the optimal policy: `ỹ = π = 0, i = r^n` is an
equilibrium, and every bounded adapted equilibrium is this one. -/
theorem rule_implements {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (h14 : 0 < κ * (φπ - 1) + (1 - β) * φy)
    (rn : ℕ → Ω → ℝ) :
    RuleEquilibrium 𝔼 β σ κ φπ φy rn (fun _ => 0) (fun _ => 0) rn ∧
      ∀ ygap infl i, RuleEquilibrium 𝔼 β σ κ φπ φy rn ygap infl i →
        ygap = (fun _ => 0) ∧ infl = (fun _ => 0) ∧ i = rn := by
  have hS : σ + φy + κ * φπ ≠ 0 := by positivity
  have hr0 : Rule φπ φy rn (fun _ => 0) (fun _ => 0) rn := fun t => by simp
  refine ⟨⟨(zero_equilibrium_iff 𝔼 hσ.ne' rn rn).2 rfl, hr0, fun t => map_zero _,
    fun t => map_zero _, ⟨0, fun t ω => by simp⟩, ⟨0, fun t ω => by simp⟩⟩, ?_⟩
  rintro ygap infl i ⟨hb, hr, ha, hai, hby, hbi⟩
  have hx := (rule_iff_solves 𝔼 hσ.ne' hS hr).1 hb
  have h0 := (rule_iff_solves 𝔼 hσ.ne' hS hr0).1
    ((zero_equilibrium_iff 𝔼 (β := β) (κ := κ) hσ.ne' rn rn).2 rfl)
  have heq := 𝔼.system_unique ((schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy).2 h14) hx h0
    (adaptedVec_stack 𝔼 ha hai) (adaptedVec_stack 𝔼 (fun t => map_zero _) fun t => map_zero _)
    (boundedVec_stack hby hbi)
    (boundedVec_stack ⟨0, fun t ω => by simp⟩ ⟨0, fun t ω => by simp⟩)
  have h1 : ygap = fun _ => 0 := funext fun t => by
    simpa [stack] using congrFun (congrFun heq t) 0
  have h2 : infl = fun _ => 0 := funext fun t => by
    simpa [stack] using congrFun (congrFun heq t) 1
  refine ⟨h1, h2, funext fun t => ?_⟩
  rw [hr t, h1, h2]
  simp

/-- Galí (2015), p. 106 (necessity of (14)): if `κ (φ_π − 1) + (1 − β) φ_y ≤ 0`, the rule
has a bounded equilibrium other than `ỹ = π = 0`. -/
theorem rule_not_unique [Nonempty Ω] {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy)
    (h14 : κ * (φπ - 1) + (1 - β) * φy ≤ 0) (rn : ℕ → Ω → ℝ) :
    ∃ ygap infl i, RuleEquilibrium 𝔼 β σ κ φπ φy rn ygap infl i ∧
      (ygap ≠ (fun _ => 0) ∨ infl ≠ (fun _ => 0)) := by
  have hS : σ + φy + κ * φπ ≠ 0 := by positivity
  have hns : ¬ SchurStable (tr2 (AT β σ κ φπ φy)) (det2 (AT β σ κ φπ φy)) := by
    rw [schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy]; linarith
  have hr0 : Rule φπ φy rn (fun _ => 0) (fun _ => 0) rn := fun t => by simp
  have h0 := (rule_iff_solves 𝔼 hσ.ne' hS hr0).1
    ((zero_equilibrium_iff 𝔼 (β := β) (κ := κ) hσ.ne' rn rn).2 rfl)
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ := 𝔼.system_not_unique hns h0
    (adaptedVec_stack 𝔼 (fun t => map_zero _) fun t => map_zero _)
    (boundedVec_stack ⟨0, fun t ω => by simp⟩ ⟨0, fun t ω => by simp⟩)
  set ygap' : ℕ → Ω → ℝ := fun t => y t 0
  set infl' : ℕ → Ω → ℝ := fun t => y t 1
  have hst : stack ygap' infl' = y := by
    funext t j
    fin_cases j <;> rfl
  have hr' : Rule φπ φy rn ygap' infl' (fun t => rn t + φπ • infl' t + φy • ygap' t) :=
    fun t => rfl
  refine ⟨ygap', infl', _, ⟨(rule_iff_solves 𝔼 hσ.ne' hS hr').2 (hst ▸ hy), hr',
    fun t => hay t 0, fun t => hay t 1, ⟨M, fun t ω => hM t 0 ω⟩, ⟨M, fun t ω => hM t 1 ω⟩⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hst, hcon.1, hcon.2]

/-- **Ex. 4.4(a)** (Galí 2015, p. 106): for `φ_π, φ_y ≥ 0` the rule (11) implements
`ỹ = π = 0` as the unique bounded equilibrium if and only if condition (14) holds. -/
theorem implements_uniquely_iff [Nonempty Ω] {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (rn : ℕ → Ω → ℝ) :
    (∀ ygap infl i, RuleEquilibrium 𝔼 β σ κ φπ φy rn ygap infl i →
      ygap = (fun _ => 0) ∧ infl = (fun _ => 0)) ↔ 0 < κ * (φπ - 1) + (1 - β) * φy := by
  constructor
  · intro h
    by_contra h14
    obtain ⟨ygap, infl, i, he, hne⟩ :=
      rule_not_unique 𝔼 hσ hκ hβ0 hβ1 hφπ hφy (not_lt.1 h14) rn
    have := h ygap infl i he
    rcases hne with hne | hne
    · exact hne this.1
    · exact hne this.2
  · intro h14 ygap infl i he
    have := (rule_implements 𝔼 hσ hκ hβ0 hβ1 hφπ hφy h14 rn).2 ygap infl i he
    exact ⟨this.1, this.2.1⟩

/-! ### (b) The money supply under the optimal policy -/

/-- Galí (2015), Ex. 4.4(b): the lagged price level `p_{t−1}`, with `p_{−1} = p*` given. -/
def lagP (pstar : ℝ) (p : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => pstar
  | t + 1 => p t

/-- Galí (2015), Ex. 4.4: inflation is the change in the (log) price level,
`π_t = p_t − p_{t−1}`, with initial price level `p_{−1} = p*`. -/
def PriceLevel (pstar : ℝ) (p infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = p t - lagP pstar p t

/-- Galí (2015), Ex. 4.4, p. 122: money demand `m_t − p_t = y_t − η i_t` with output
`y_t = ỹ_t + y^n_t`. -/
def MoneyDemand (η : ℝ) (yn ygap p m i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, m t - p t = (ygap t + yn t) - η • i t

/-- Galí (2015), Ex. 4.4: an equilibrium of the full model: the IS equation, the Phillips curve,
the price-level identity and money demand. -/
def FullEquilibrium (β σ κ η pstar : ℝ) (rn yn ygap infl p m i : ℕ → Ω → ℝ) : Prop :=
  Block 𝔼 β σ κ rn ygap infl i ∧ PriceLevel pstar p infl ∧ MoneyDemand η yn ygap p m i

omit 𝔼 in
/-- Galí (2015), Ex. 4.4(b): with zero inflation the price level never moves from `p*`. -/
theorem price_level_const {pstar : ℝ} {p : ℕ → Ω → ℝ}
    (h : PriceLevel pstar p (fun _ => 0)) (t : ℕ) : p t = fun _ => pstar := by
  induction t with
  | zero => have := h 0; simp only [lagP] at this; exact (sub_eq_zero.1 this.symm)
  | succ t ih =>
    have := h (t + 1)
    simp only [lagP] at this
    rw [← ih]
    exact sub_eq_zero.1 this.symm

/-- **Ex. 4.4(b)** (Galí 2015, p. 122): in every equilibrium attaining the optimal outcome
`ỹ = π = 0`, the money supply is `m_t = p* + y^n_t − η r^n_t`. -/
theorem money_path_optimal {β σ κ η pstar : ℝ} (hσ : σ ≠ 0) {rn yn p m i : ℕ → Ω → ℝ}
    (h : FullEquilibrium 𝔼 β σ κ η pstar rn yn (fun _ => 0) (fun _ => 0) p m i) (t : ℕ) :
    m t = (fun _ => pstar) + yn t - η • rn t := by
  have hi := (zero_equilibrium_iff 𝔼 hσ rn i).1 h.1
  have hp := price_level_const h.2.1 t
  have hm := h.2.2 t
  rw [hp, hi] at hm
  funext ω
  have e := congrFun hm ω
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e ⊢
  linarith

/-- **Ex. 4.4(b)** (Galí 2015, p. 122): if the money supply is held constant at `m̄` and an
equilibrium attains `ỹ = π = 0`, then `y^n_t − η r^n_t = m̄ − p*` at every date and state. -/
theorem constant_money_suboptimal {β σ κ η pstar mbar : ℝ} (hσ : σ ≠ 0)
    {rn yn p i : ℕ → Ω → ℝ}
    (h : FullEquilibrium 𝔼 β σ κ η pstar rn yn (fun _ => 0) (fun _ => 0) p (fun _ _ => mbar) i)
    (t : ℕ) (ω : Ω) : yn t ω - η * rn t ω = mbar - pstar := by
  have e := congrFun (money_path_optimal 𝔼 hσ h t) ω
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e
  linarith

/-- **Ex. 4.4(b)** (Galí 2015, p. 122: a constant money supply is generally suboptimal): if
`y^n − η r^n` is not constant, no equilibrium under a constant money supply attains the
optimal outcome `ỹ = π = 0`. -/
theorem constant_money_not_optimal {β σ κ η pstar mbar : ℝ} (hσ : σ ≠ 0)
    {rn yn : ℕ → Ω → ℝ}
    (hvar : ∃ s t ω ω', yn s ω - η * rn s ω ≠ yn t ω' - η * rn t ω') :
    ¬ ∃ p i, FullEquilibrium 𝔼 β σ κ η pstar rn yn (fun _ => 0) (fun _ => 0) p
      (fun _ _ => mbar) i := by
  rintro ⟨p, i, h⟩
  obtain ⟨s, t, ω, ω', hne⟩ := hvar
  exact hne ((constant_money_suboptimal 𝔼 hσ h s ω).trans
    (constant_money_suboptimal 𝔼 hσ h t ω').symm)

/-- Galí (2015), Ex. 4.4(b)–(c): the optimal outcome `ỹ = π = 0`, `p = p*`, `i = r^n` is an
equilibrium whenever money follows `m_t = p* + y^n_t − η r^n_t`. -/
theorem optimal_equilibrium {β σ κ η pstar : ℝ} (hσ : σ ≠ 0) (rn yn : ℕ → Ω → ℝ) :
    FullEquilibrium 𝔼 β σ κ η pstar rn yn (fun _ => 0) (fun _ => 0) (fun _ _ => pstar)
      (fun t => (fun _ => pstar) + yn t - η • rn t) rn := by
  refine ⟨(zero_equilibrium_iff 𝔼 hσ rn rn).2 rfl, fun t => ?_, fun t => ?_⟩
  · cases t <;> simp [lagP]
  · funext ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring

/-- Galí (2015), Ex. 4.4(b): conversely, if `y^n_t − η r^n_t = c` is constant, the constant money
supply `m̄ = p* + c` supports the optimal outcome. -/
theorem constant_money_optimal_of_const {β σ κ η pstar c : ℝ} (hσ : σ ≠ 0)
    {rn yn : ℕ → Ω → ℝ} (hc : ∀ t ω, yn t ω - η * rn t ω = c) :
    FullEquilibrium 𝔼 β σ κ η pstar rn yn (fun _ => 0) (fun _ => 0) (fun _ _ => pstar)
      (fun _ _ => pstar + c) rn := by
  have h := optimal_equilibrium 𝔼 (β := β) (κ := κ) (η := η) (pstar := pstar) hσ rn yn
  have hm : (fun t => (fun _ => pstar) + yn t - η • rn t) = fun (_ : ℕ) (_ : Ω) => pstar + c := by
    funext t ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith [hc t ω]
  rwa [hm] at h

/-! ### (c) A money supply rule implementing the optimum -/

/-- Galí (2015), Ex. 4.4(c), p. 123: the money supply rule `m_t = p* + y^n_t − η r^n_t`. -/
def MoneyRule (η pstar : ℝ) (rn yn m : ℕ → Ω → ℝ) : Prop :=
  ∀ t, m t = (fun _ => pstar) + yn t - η • rn t

/-- **Ex. 4.4(c)** (Galí 2015, p. 123, existence): under the money rule
`m_t = p* + y^n_t − η r^n_t` the optimal outcome `ỹ = π = 0`, `p_t = p*`, `i_t = r^n_t` is an
equilibrium. -/
theorem moneyRule_equilibrium {β σ κ η pstar : ℝ} (hσ : σ ≠ 0) (rn yn : ℕ → Ω → ℝ) :
    FullEquilibrium 𝔼 β σ κ η pstar rn yn (fun _ => 0) (fun _ => 0) (fun _ _ => pstar)
        (fun t => (fun _ => pstar) + yn t - η • rn t) rn ∧
      MoneyRule η pstar rn yn (fun t => (fun _ => pstar) + yn t - η • rn t) :=
  ⟨optimal_equilibrium 𝔼 hσ rn yn, fun _ => rfl⟩

omit 𝔼 in
/-- Galí (2015), Ex. 4.4(c): given money demand and `η > 0`, the money rule
`m_t = p* + y^n_t − η r^n_t` holds iff the nominal rate follows the implicit interest rate rule
`i_t = r^n_t + η⁻¹ (ỹ_t + (p_t − p*))`. -/
theorem moneyRule_iff_interestRule {η pstar : ℝ} (hη : 0 < η) {rn yn ygap p m i : ℕ → Ω → ℝ}
    (hmd : MoneyDemand η yn ygap p m i) :
    MoneyRule η pstar rn yn m ↔
      ∀ t, i t = rn t + η⁻¹ • (ygap t + (p t - fun _ => pstar)) := by
  have hinv : η * η⁻¹ = 1 := mul_inv_cancel₀ hη.ne'
  constructor
  · intro h t
    funext ω
    have e := congrFun (hmd t) ω
    have r := congrFun (h t) ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e r ⊢
    linear_combination η⁻¹ * e - η⁻¹ * r - i t ω * hinv + rn t ω * hinv
  · intro h t
    funext ω
    have e := congrFun (hmd t) ω
    have r := congrFun (h t) ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e r ⊢
    linear_combination e - η * r - (ygap t ω + (p t ω - pstar)) * hinv

/-- Galí (2015), Ex. 4.4(c) (**not yet claimed**): the statement that under the money rule
`m_t = p* + y^n_t − η r^n_t` the optimal outcome is the *unique* bounded equilibrium for every
bounded adapted `r^n`, `y^n`. With the price level predetermined this is a three-variable
determinacy question (the open question of Galí Chapter 3, footnote 14), which this project
leaves open; the definition records the claim without asserting it. -/
def MoneyRuleUniqueness (β σ κ η pstar : ℝ) : Prop :=
  ∀ rn yn ygap infl p m i : ℕ → Ω → ℝ,
    BoundedProc rn → 𝔼.Adapted rn → BoundedProc yn → 𝔼.Adapted yn →
    FullEquilibrium 𝔼 β σ κ η pstar rn yn ygap infl p m i → MoneyRule η pstar rn yn m →
    𝔼.Adapted ygap → 𝔼.Adapted p → BoundedProc ygap → BoundedProc p →
    ygap = (fun _ => 0) ∧ infl = (fun _ => 0)

end Gali.MonetaryPolicyDesign.Ex4_4
