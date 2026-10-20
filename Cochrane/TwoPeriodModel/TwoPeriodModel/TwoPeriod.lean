/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TwoPeriodModel.Expectations
import TwoPeriodModel.ExpectationsFiniteTree

/-!
# The last day and the two-period model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 1, §§1.1–1.3, pp. 4–8.

## The setting

Dates `0` and `1` inside an arbitrary `ExpectationSystem Ω` (`E_0`, `E_1`), so every result holds
under perfect foresight and under genuine uncertainty (`coin_equilibrium`). Random variables are
functions `Ω → ℝ`; all equations are equalities of functions (state by state). Date-0 variables
(`B_{−1}`, `B_0`, `s_0`, `P_0`) are `Known` at date 0: `E_0 x = x`. The date-1 surplus `s_1` and
price level `P_1` are random. Results that pull date-0 quantities out of `E_0` assume the
pull-out property `PullOut` (true for perfect foresight and every finite event tree).

## The fiscal-theory equilibrium notion

`Equilibrium 𝔼 β B₋₁ B₀ s₀ s₁ P₀ P₁ Q₀`: given fiscal policy and the debt sale `(B₋₁, B₀, s₀, s₁)`,
prices `(P₀, P₁, Q₀)` with `P₀, P₁ > 0` statewise, `P₀` known at date 0, the date-0 flow
condition (1.2), the bond-pricing equation (1.3) and the date-1 valuation equation (1.1)/(1.4).
"The price level is determined" means: there is exactly one such triple
(`equilibrium_existsUnique`), namely `P₁ = B₀/s₁`, `P₀ = B₋₁/(s₀ + βE₀s₁)` (`equilibrium_iff`).

## Main results

* (1.1), p. 4: `lastDay_iff` (`B₀ = P₁s₁ ↔ B₀/P₁ = s₁`), `lastDay_existsUnique`,
  `lastDay_none` (error E3: with `s₁ ≤ 0` there is no positive price level).
* p. 5: `excess_money_iff`, `money_shortage_iff` ("too much money chasing too few goods").
* p. 4, p. 7: `propTax_real` (a proportional tax makes `s₁ = τy₁` independent of `P₁`).
* (1.2)–(1.3), p. 8: `Flow0`, `BondPrice0`, `rate`, `bondPrice_eq_inv_one_add_rate`,
  `bondPrice_R`; the unnumbered display `flow_real`.
* (1.4)–(1.5), p. 8: `revenue_eq`, `valuation0_of_flow`, `flow_iff_valuation0`.
* Existence and uniqueness: `equilibrium_iff`, `equilibrium_existsUnique`; non-existence
  (error E3): `no_equilibrium_of_s1_nonpos`, `no_equilibrium_of_pv_nonpos`.
* Box p. 7 / p. 8: `price0_strictAnti_beta` (a lower `β` raises `P₀` with unchanged
  surpluses), `price0_strictAnti_Es1` (bad fiscal news raises `P₀`), `price0_eq_of_pv_eq`
  (`P₀` depends on surpluses only through their present value), `price0_any_level`
  (any deficit or surplus `s₀` is compatible with any price level).
* Genuine uncertainty: `coin_equilibrium` (a coin-flip economy with a random `P₁`).
-/

namespace Cochrane.TwoPeriodModel.TwoPeriod

open Cochrane.TwoPeriodModel.ExpectationsFiniteTree

variable {Ω : Type*}

/-! ### Information: variables known at a date -/

/-- Cochrane (2023), §1.3, p. 8: a random variable is known at date `t` when `E_t x = x`
(date-0 quantities `B₋₁, B₀, s₀, P₀` are known at date 0). -/
def Known (𝔼 : ExpectationSystem Ω) (t : ℕ) (x : Ω → ℝ) : Prop := 𝔼.E t x = x

/-- Cochrane (2023), §1.3, p. 8: constants are known at every date. -/
theorem known_const (𝔼 : ExpectationSystem Ω) (t : ℕ) (c : ℝ) :
    Known 𝔼 t (fun _ => c) :=
  𝔼.const t c

/-- Cochrane (2023), §1.3, p. 8: a conditional expectation `E_t x` is known at date `t`. -/
theorem known_E (𝔼 : ExpectationSystem Ω) (t : ℕ) (x : Ω → ℝ) : Known 𝔼 t (𝔼.E t x) :=
  𝔼.E_E_self t x

/-- Cochrane (2023), §1.4, p. 10: what is known at date `s` is known at every later date. -/
theorem known_mono (𝔼 : ExpectationSystem Ω) {s t : ℕ} (hst : s ≤ t) {x : Ω → ℝ}
    (hx : Known 𝔼 s x) : Known 𝔼 t x := by
  unfold Known at *
  have h := 𝔼.known hst x
  rw [hx] at h
  exact h

/-- Cochrane (2023), §1.3, p. 8: sums of known variables are known. -/
theorem known_add (𝔼 : ExpectationSystem Ω) {t : ℕ} {x y : Ω → ℝ} (hx : Known 𝔼 t x)
    (hy : Known 𝔼 t y) : Known 𝔼 t (x + y) := by
  unfold Known at *
  rw [map_add, hx, hy]

/-- Cochrane (2023), §1.3, p. 8: differences of known variables are known. -/
theorem known_sub (𝔼 : ExpectationSystem Ω) {t : ℕ} {x y : Ω → ℝ} (hx : Known 𝔼 t x)
    (hy : Known 𝔼 t y) : Known 𝔼 t (x - y) := by
  unfold Known at *
  rw [map_sub, hx, hy]

/-- Cochrane (2023), §1.3, p. 8: multiples of known variables are known. -/
theorem known_smul (𝔼 : ExpectationSystem Ω) {t : ℕ} (c : ℝ) {x : Ω → ℝ}
    (hx : Known 𝔼 t x) : Known 𝔼 t (c • x) := by
  unfold Known at *
  rw [map_smul, hx]

/-- Cochrane (2023), §1.3, p. 8: under `PullOut`, products of known variables are known. -/
theorem known_mul (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {t : ℕ} {x y : Ω → ℝ}
    (hx : Known 𝔼 t x) (hy : Known 𝔼 t y) : Known 𝔼 t (x * y) := by
  unfold Known at *
  rw [hP t x y hx, hy]

/-- Cochrane (2023), §1.3, p. 8: under `PullOut`, the reciprocal of a nowhere-zero
random variable known at `t` is known at `t`. -/
theorem known_inv (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {t : ℕ} {x : Ω → ℝ}
    (hx : Known 𝔼 t x) (hx0 : ∀ ω, x ω ≠ 0) : Known 𝔼 t x⁻¹ := by
  have h1 : x * x⁻¹ = fun _ => (1 : ℝ) := by
    funext ω
    simp only [Pi.mul_apply, Pi.inv_apply]
    exact mul_inv_cancel₀ (hx0 ω)
  have h2 := hP t x x⁻¹ hx
  rw [h1, 𝔼.const] at h2
  funext ω
  have h3 := congrFun h2 ω
  simp only [Pi.mul_apply] at h3
  simp only [Pi.inv_apply]
  field_simp [hx0 ω]
  linarith

/-- Cochrane (2023), §1.3, p. 8: under `PullOut`, quotients of known variables (nowhere-zero
denominator) are known. -/
theorem known_div (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {t : ℕ} {x y : Ω → ℝ}
    (hx : Known 𝔼 t x) (hy : Known 𝔼 t y) (hy0 : ∀ ω, y ω ≠ 0) : Known 𝔼 t (x / y) := by
  rw [div_eq_mul_inv]
  exact known_mul 𝔼 hP hx (known_inv 𝔼 hP hy hy0)

/-! ### §1.1–1.2: the last day -/

/-- Cochrane (2023), §1.1, p. 4: "cash printed in the morning must be soaked up by taxes",
`B₀ = P₁s₁`, is (1.1) `B₀/P₁ = s₁` whenever `P₁ ≠ 0`. -/
theorem lastDay_iff {B0 P1 s1 : ℝ} (hP : P1 ≠ 0) : B0 = P1 * s1 ↔ B0 / P1 = s1 := by
  rw [div_eq_iff hP]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), eq. (1.1), p. 4: with `B₀ > 0` and a positive real surplus `s₁ > 0` there is
exactly one positive price level solving `B₀/P₁ = s₁`, namely `P₁ = B₀/s₁`. -/
theorem lastDay_existsUnique {B0 s1 : ℝ} (hB : 0 < B0) (hs : 0 < s1) :
    ∃! P1 : ℝ, 0 < P1 ∧ B0 / P1 = s1 := by
  refine ⟨B0 / s1, ⟨div_pos hB hs, by field_simp⟩, fun P1 hP1 => ?_⟩
  obtain ⟨hpos, h⟩ := hP1
  rw [div_eq_iff hpos.ne'] at h
  rw [eq_div_iff hs.ne']
  linarith

/-- Cochrane (2023), eq. (1.1), p. 4: the price level is `P₁ = B₀/s₁`. -/
theorem lastDay_eq {B0 P1 s1 : ℝ} (hP : P1 ≠ 0) (hs : s1 ≠ 0) (h : B0 / P1 = s1) :
    P1 = B0 / s1 := by
  rw [div_eq_iff hP] at h
  rw [eq_div_iff hs]
  linarith

/-- Cochrane (2023), eq. (1.1), p. 4 (error E3, missing hypothesis): if `B₀ > 0` and the real
surplus is not positive, `s₁ ≤ 0`, no positive price level satisfies (1.1). -/
theorem lastDay_none {B0 s1 : ℝ} (hB : 0 < B0) (hs : s1 ≤ 0) :
    ¬ ∃ P1 : ℝ, 0 < P1 ∧ B0 / P1 = s1 := by
  rintro ⟨P1, hP1, h⟩
  have : 0 < B0 / P1 := div_pos hB hP1
  linarith

/-- Cochrane (2023), §1.2, p. 5: money left over after taxes, `M₁ = B₀ − P₁s₁`, is positive
("too much money chasing too few goods") exactly when the price level is below its equilibrium
value `B₀/s₁` (`P₁, s₁ > 0`). -/
theorem excess_money_iff {B0 P1 s1 : ℝ} (hs : 0 < s1) :
    0 < B0 - P1 * s1 ↔ P1 < B0 / s1 := by
  rw [lt_div_iff₀ hs]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §1.2, p. 5: conversely, taxes exceed the cash printed, `B₀ − P₁s₁ < 0`,
exactly when the price level is above `B₀/s₁` (`s₁ > 0`). -/
theorem money_shortage_iff {B0 P1 s1 : ℝ} (hs : 0 < s1) :
    B0 - P1 * s1 < 0 ↔ B0 / s1 < P1 := by
  rw [div_lt_iff₀ hs]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §1.1, p. 4, and §1.8, pp. 17–18: with a proportional income tax,
`P₁s₁ = τP₁y₁`, the real surplus `s₁ = τy₁` does not depend on the price level (`P₁ ≠ 0`). -/
theorem propTax_real {P1 s1 τ y1 : ℝ} (hP : P1 ≠ 0) (h : P1 * s1 = τ * P1 * y1) :
    s1 = τ * y1 := by
  have h' : P1 * s1 = P1 * (τ * y1) := by rw [h]; ring
  exact mul_left_cancel₀ hP h'

/-! ### §1.3: the two-period model -/

/-- Cochrane (2023), eq. (1.1)/(1.4), pp. 4, 8: the date-1 valuation equation `B₀/P₁ = s₁`
(state by state). -/
def Valuation1 (B0 P1 s1 : Ω → ℝ) : Prop := B0 / P1 = s1

/-- Cochrane (2023), eq. (1.2), p. 8: the date-0 flow condition `B₋₁ = P₀s₀ + Q₀B₀`. -/
def Flow0 (Bm1 P0 s0 Q0 B0 : Ω → ℝ) : Prop := Bm1 = P0 * s0 + Q0 * B0

/-- Cochrane (2023), eq. (1.3), p. 8: the bond-pricing equation `Q₀ = βE₀(P₀/P₁)`. -/
def BondPrice0 (𝔼 : ExpectationSystem Ω) (β : ℝ) (P0 P1 Q0 : Ω → ℝ) : Prop :=
  Q0 = β • 𝔼.E 0 (P0 / P1)

/-- Cochrane (2023), eq. (1.3), p. 8: the nominal interest rate `i₀` defined by
`Q₀ = 1/(1 + i₀)`, i.e. `i₀ = 1/Q₀ − 1`. -/
noncomputable def rate (Q0 : Ω → ℝ) : Ω → ℝ := fun ω => 1 / Q0 ω - 1

/-- Cochrane (2023), eq. (1.3), p. 8, first equality: `Q₀ = 1/(1 + i₀)`. -/
theorem bondPrice_eq_inv_one_add_rate (Q0 : Ω → ℝ) (ω : Ω) :
    Q0 ω = 1 / (1 + rate Q0 ω) := by
  simp only [rate, add_sub_cancel, one_div, inv_inv]

/-- Cochrane (2023), eq. (1.3), p. 8, third equality: with `β = 1/R`,
`βE₀(P₀/P₁) = (1/R)E₀(P₀/P₁)`. -/
theorem bondPrice_R (𝔼 : ExpectationSystem Ω) {β R : ℝ} (hR : β = 1 / R) (P0 P1 Q0 : Ω → ℝ) :
    BondPrice0 𝔼 β P0 P1 Q0 ↔ Q0 = (1 / R) • 𝔼.E 0 (P0 / P1) := by
  rw [BondPrice0, hR]

/-- Cochrane (2023), eq. (1.5), p. 8: the government debt valuation equation
`B₋₁/P₀ = s₀ + βE₀s₁`. -/
def Valuation0 (𝔼 : ExpectationSystem Ω) (β : ℝ) (Bm1 P0 s0 s1 : Ω → ℝ) : Prop :=
  Bm1 / P0 = s0 + β • 𝔼.E 0 s1

/-- Cochrane (2023), eq. (1.5), p. 8: the present value of surpluses `s₀ + βE₀s₁`. -/
noncomputable def pv (𝔼 : ExpectationSystem Ω) (β : ℝ) (s0 s1 : Ω → ℝ) : Ω → ℝ :=
  s0 + β • 𝔼.E 0 s1

/-- Cochrane (2023), §1.3, p. 8: the present value is known at date 0 when `s₀` is. -/
theorem known_pv (𝔼 : ExpectationSystem Ω) (β : ℝ) {s0 : Ω → ℝ} (hs0 : Known 𝔼 0 s0)
    (s1 : Ω → ℝ) : Known 𝔼 0 (pv 𝔼 β s0 s1) :=
  known_add 𝔼 hs0 (known_smul 𝔼 β (known_E 𝔼 0 s1))

/-- Cochrane (2023), §1.3, p. 8 (unnumbered display after (1.3)): substituting the bond price
into the flow condition, `B₋₁/P₀ = s₀ + βE₀(1/P₁)B₀` (`P₀ > 0`; `P₀, B₀` known at 0;
`PullOut`). -/
theorem flow_real (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 P0 P1 Q0 : Ω → ℝ} (hP0 : ∀ ω, 0 < P0 ω) (hkP0 : Known 𝔼 0 P0)
    (hflow : Flow0 Bm1 P0 s0 Q0 B0) (hQ : BondPrice0 𝔼 β P0 P1 Q0) :
    Bm1 / P0 = s0 + β • 𝔼.E 0 (1 / P1) * B0 := by
  have hpo : 𝔼.E 0 (P0 / P1) = P0 * 𝔼.E 0 (1 / P1) := by
    rw [← hP 0 P0 _ hkP0]
    congr 1
    funext ω
    simp only [Pi.div_apply, Pi.mul_apply, Pi.one_apply]
    ring
  funext ω
  have h1 := congrFun hflow ω
  have h2 := congrFun hpo ω
  rw [hQ] at h1
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Pi.div_apply] at h1 h2 ⊢
  rw [h2] at h1
  have := (hP0 ω).ne'
  rw [h1]
  field_simp

/-- Cochrane (2023), eq. (1.8), p. 9 / §1.3, p. 8: bond sales raise nominal revenue
`Q₀B₀ = P₀ · βE₀s₁` when `Q₀ = βE₀(P₀/P₁)` and `B₀/P₁ = s₁` (`P₀, B₀` known at 0; `PullOut`). -/
theorem revenue_eq (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {B0 s1 P0 P1 Q0 : Ω → ℝ} (hkP0 : Known 𝔼 0 P0) (hkB0 : Known 𝔼 0 B0)
    (hQ : BondPrice0 𝔼 β P0 P1 Q0) (h1 : Valuation1 B0 P1 s1) :
    Q0 * B0 = P0 * (β • 𝔼.E 0 s1) := by
  rw [hQ]
  have e1 : 𝔼.E 0 (B0 * (P0 / P1)) = B0 * 𝔼.E 0 (P0 / P1) := hP 0 B0 _ hkB0
  have e2 : 𝔼.E 0 (P0 * s1) = P0 * 𝔼.E 0 s1 := hP 0 P0 _ hkP0
  have e3 : B0 * (P0 / P1) = P0 * s1 := by
    rw [← h1]
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply]
    ring
  rw [e3, e2] at e1
  funext ω
  have := congrFun e1 ω
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
  linear_combination (-β) * this

/-- Cochrane (2023), eqs. (1.2)–(1.5), p. 8: the flow condition (1.2), the bond price (1.3)
and date-1 equilibrium (1.4) imply the government debt valuation equation (1.5)
`B₋₁/P₀ = s₀ + βE₀s₁` (`P₀ > 0`; `P₀, B₀` known at 0; `PullOut`). -/
theorem valuation0_of_flow (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ} (hP0 : ∀ ω, 0 < P0 ω) (hkP0 : Known 𝔼 0 P0)
    (hkB0 : Known 𝔼 0 B0) (hflow : Flow0 Bm1 P0 s0 Q0 B0) (hQ : BondPrice0 𝔼 β P0 P1 Q0)
    (h1 : Valuation1 B0 P1 s1) : Valuation0 𝔼 β Bm1 P0 s0 s1 := by
  have hr := revenue_eq 𝔼 hP hkP0 hkB0 hQ h1
  funext ω
  have e1 := congrFun hflow ω
  have e2 := congrFun hr ω
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Pi.div_apply] at e1 e2 ⊢
  have := (hP0 ω).ne'
  rw [e1, e2]
  field_simp

/-- Cochrane (2023), eqs. (1.2)–(1.5), p. 8: given (1.3) and (1.4), the flow condition (1.2)
and the valuation equation (1.5) are equivalent (`P₀ > 0`; `P₀, B₀` known at 0; `PullOut`). -/
theorem flow_iff_valuation0 (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ} (hP0 : ∀ ω, 0 < P0 ω) (hkP0 : Known 𝔼 0 P0)
    (hkB0 : Known 𝔼 0 B0) (hQ : BondPrice0 𝔼 β P0 P1 Q0) (h1 : Valuation1 B0 P1 s1) :
    Flow0 Bm1 P0 s0 Q0 B0 ↔ Valuation0 𝔼 β Bm1 P0 s0 s1 := by
  refine ⟨fun hflow => valuation0_of_flow 𝔼 hP hP0 hkP0 hkB0 hflow hQ h1, fun hv => ?_⟩
  have hr := revenue_eq 𝔼 hP hkP0 hkB0 hQ h1
  funext ω
  have e1 := congrFun hv ω
  have e2 := congrFun hr ω
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Pi.div_apply] at e1 e2 ⊢
  have := (hP0 ω).ne'
  rw [div_eq_iff this] at e1
  rw [e1, e2]
  ring

/-! ### The equilibrium: existence, uniqueness, non-existence -/

/-- Cochrane (2023), §1.3, pp. 7–8: an equilibrium of the two-period model given fiscal policy
and the debt sale `(B₋₁, B₀, s₀, s₁)`: positive price levels `P₀, P₁`, `P₀` known at date 0,
the flow condition (1.2), the bond price (1.3) and the date-1 valuation equation (1.4). -/
def Equilibrium (𝔼 : ExpectationSystem Ω) (β : ℝ) (Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ) : Prop :=
  (∀ ω, 0 < P0 ω) ∧ (∀ ω, 0 < P1 ω) ∧ Known 𝔼 0 P0 ∧ Flow0 Bm1 P0 s0 Q0 B0 ∧
    BondPrice0 𝔼 β P0 P1 Q0 ∧ Valuation1 B0 P1 s1

/-- Cochrane (2023), eqs. (1.4)–(1.5), p. 8: from `B₀/P₁ = s₁` with `P₁, s₁ ≠ 0`, `P₁ = B₀/s₁`
state by state. -/
theorem price1_eq {B0 P1 s1 : Ω → ℝ} (hP1 : ∀ ω, P1 ω ≠ 0) (hs1 : ∀ ω, s1 ω ≠ 0)
    (h : Valuation1 B0 P1 s1) : P1 = B0 / s1 := by
  funext ω
  exact lastDay_eq (hP1 ω) (hs1 ω) (congrFun h ω)

/-- Cochrane (2023), eq. (1.5), p. 8: from `B₋₁/P₀ = s₀ + βE₀s₁` with `P₀ ≠ 0` and a nonzero
present value, `P₀ = B₋₁/(s₀ + βE₀s₁)`. -/
theorem price0_eq (𝔼 : ExpectationSystem Ω) {β : ℝ} {Bm1 P0 s0 s1 : Ω → ℝ}
    (hP0 : ∀ ω, P0 ω ≠ 0) (hpv : ∀ ω, pv 𝔼 β s0 s1 ω ≠ 0) (h : Valuation0 𝔼 β Bm1 P0 s0 s1) :
    P0 = Bm1 / pv 𝔼 β s0 s1 := by
  funext ω
  exact lastDay_eq (hP0 ω) (hpv ω) (congrFun h ω)

/-- Cochrane (2023), §1.3, pp. 7–8: characterisation of the equilibrium. With `PullOut`,
`B₀` known at 0, `s₁ > 0` and a positive present value, `(P₀, P₁, Q₀)` is an equilibrium iff
`P₀ > 0`, `P₀` known at 0, `P₁ = B₀/s₁`, `P₀ = B₋₁/(s₀ + βE₀s₁)` and `Q₀ = βE₀(P₀/P₁)`, with
`P₁ > 0`. -/
theorem equilibrium_iff (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ} (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0)
    (hs1 : ∀ ω, 0 < s1 ω) (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω) :
    Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0 ↔
      (∀ ω, 0 < P0 ω) ∧ Known 𝔼 0 P0 ∧ P1 = B0 / s1 ∧ P0 = Bm1 / pv 𝔼 β s0 s1 ∧
        BondPrice0 𝔼 β P0 P1 Q0 := by
  constructor
  · rintro ⟨hP0, hP1, hk, hflow, hQ, h1⟩
    have hv := valuation0_of_flow 𝔼 hP hP0 hk hkB0 hflow hQ h1
    exact ⟨hP0, hk, price1_eq (fun ω => (hP1 ω).ne') (fun ω => (hs1 ω).ne') h1,
      price0_eq 𝔼 (fun ω => (hP0 ω).ne') (fun ω => (hpv ω).ne') hv, hQ⟩
  · rintro ⟨hP0, hk, rfl, hP0eq, hQ⟩
    have hP1 : ∀ ω, 0 < (B0 / s1) ω := fun ω => div_pos (hB0 ω) (hs1 ω)
    have h1 : Valuation1 B0 (B0 / s1) s1 := by
      funext ω
      simp only [Pi.div_apply]
      have := (hB0 ω).ne'
      have := (hs1 ω).ne'
      field_simp
    have hv : Valuation0 𝔼 β Bm1 P0 s0 s1 := by
      funext ω
      have e := congrFun hP0eq ω
      simp only [Pi.div_apply] at e ⊢
      have := (hP0 ω).ne'
      have := (hpv ω).ne'
      rw [div_eq_iff (hP0 ω).ne', e]
      simp only [pv] at this ⊢
      field_simp
    exact ⟨hP0, hP1, hk, (flow_iff_valuation0 𝔼 hP hP0 hk hkB0 hQ h1).mpr hv, hQ, h1⟩

/-- Cochrane (2023), §1.3, pp. 7–8: **the fiscal theory determines the price level.** With
`PullOut`, `B₋₁, B₀, s₀` known at date 0, `B₋₁, B₀ > 0`, a positive surplus `s₁ > 0` and a
positive present value `s₀ + βE₀s₁ > 0` (error E3: these hypotheses are needed), there is
exactly one equilibrium `(P₀, P₁, Q₀)`. -/
theorem equilibrium_existsUnique (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 s1 : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω) (hkBm1 : Known 𝔼 0 Bm1)
    (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0) (hks0 : Known 𝔼 0 s0)
    (hs1 : ∀ ω, 0 < s1 ω) (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω) :
    ∃! p : (Ω → ℝ) × (Ω → ℝ) × (Ω → ℝ), Equilibrium 𝔼 β Bm1 B0 s0 s1 p.1 p.2.1 p.2.2 := by
  set P0 := Bm1 / pv 𝔼 β s0 s1 with hP0def
  have hP0 : ∀ ω, 0 < P0 ω := fun ω => div_pos (hBm1 ω) (hpv ω)
  have hk : Known 𝔼 0 P0 :=
    known_div 𝔼 hP hkBm1 (known_pv 𝔼 β hks0 s1) (fun ω => (hpv ω).ne')
  refine ⟨(P0, B0 / s1, β • 𝔼.E 0 (P0 / (B0 / s1))), ?_, ?_⟩
  · exact (equilibrium_iff 𝔼 hP hB0 hkB0 hs1 hpv).mpr ⟨hP0, hk, rfl, rfl, rfl⟩
  · rintro ⟨Q, R, S⟩ h
    obtain ⟨-, -, hR, hQ, hS⟩ := (equilibrium_iff 𝔼 hP hB0 hkB0 hs1 hpv).mp h
    simp only at hR hQ hS
    rw [hS, hR, hQ]

/-- Cochrane (2023), eq. (1.1), p. 4 (error E3): if in some state the date-1 surplus is not
positive (and `B₀ > 0` there), no equilibrium exists. -/
theorem no_equilibrium_of_s1_nonpos (𝔼 : ExpectationSystem Ω) {β : ℝ}
    {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ} {ω : Ω} (hB0 : 0 < B0 ω) (hs1 : s1 ω ≤ 0) :
    ¬ Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0 := by
  rintro ⟨-, hP1, -, -, -, h1⟩
  exact lastDay_none hB0 hs1 ⟨P1 ω, hP1 ω, congrFun h1 ω⟩

/-- Cochrane (2023), eq. (1.5), p. 8 (error E3): if in some state the present value of
surpluses `s₀ + βE₀s₁` is not positive while `B₋₁ > 0`, no equilibrium exists (`PullOut`,
`B₀` known at 0). -/
theorem no_equilibrium_of_pv_nonpos (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ} (hkB0 : Known 𝔼 0 B0) {ω : Ω} (hBm1 : 0 < Bm1 ω)
    (hpv : pv 𝔼 β s0 s1 ω ≤ 0) : ¬ Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0 := by
  rintro ⟨hP0, -, hk, hflow, hQ, h1⟩
  have hv := congrFun (valuation0_of_flow 𝔼 hP hP0 hk hkB0 hflow hQ h1) ω
  exact lastDay_none hBm1 hpv ⟨P0 ω, hP0 ω, hv⟩

/-! ### Comparative statics of `P₀ = B₋₁/(s₀ + βE₀s₁)` (box p. 7, p. 8) -/

/-- Cochrane (2023), box p. 7 and p. 8: "a higher discount rate, lower `β`, can lead to
inflation with no change in surpluses": with `B₋₁ > 0` and `E₀s₁ > 0`, `P₀ = B₋₁/(s₀ + βE₀s₁)`
is strictly decreasing in `β` (where the present value is positive). -/
theorem price0_strictAnti_beta {Bm1 s0 Es1 β β' : ℝ} (hB : 0 < Bm1) (hE : 0 < Es1)
    (hββ' : β < β') (hpv : 0 < s0 + β * Es1) :
    Bm1 / (s0 + β' * Es1) < Bm1 / (s0 + β * Es1) := by
  have h : s0 + β * Es1 < s0 + β' * Es1 := by nlinarith
  exact div_lt_div_of_pos_left hB hpv h

/-- Cochrane (2023), p. 8: "inflation can break out today if people see intractable future
fiscal problems": with `B₋₁ > 0`, `β > 0`, `P₀` is strictly decreasing in expected future
surpluses `E₀s₁` (where the present value is positive). -/
theorem price0_strictAnti_Es1 {Bm1 s0 β e e' : ℝ} (hB : 0 < Bm1) (hβ : 0 < β) (hee' : e < e')
    (hpv : 0 < s0 + β * e) : Bm1 / (s0 + β * e') < Bm1 / (s0 + β * e) := by
  have h : s0 + β * e < s0 + β * e' := by nlinarith
  exact div_lt_div_of_pos_left hB hpv h

/-- Cochrane (2023), p. 8: the price level `P₀` depends on the surpluses `(s₀, s₁)` only through
their present value: two policies with the same `s₀ + βE₀s₁` have the same equilibrium `P₀`
(`PullOut`, `B₀` known at 0, `s₁, s₁' > 0`, positive present value). -/
theorem price0_eq_of_pv_eq (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 s1 s0' s1' P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hB0 : ∀ ω, 0 < B0 ω)
    (hkB0 : Known 𝔼 0 B0) (hs1 : ∀ ω, 0 < s1 ω) (hs1' : ∀ ω, 0 < s1' ω)
    (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω) (hsame : pv 𝔼 β s0 s1 = pv 𝔼 β s0' s1')
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 B0 s0' s1' P0' P1' Q0') : P0 = P0' := by
  have hpv' : ∀ ω, 0 < pv 𝔼 β s0' s1' ω := fun ω => hsame ▸ hpv ω
  obtain ⟨-, -, -, h, -⟩ := (equilibrium_iff 𝔼 hP hB0 hkB0 hs1 hpv).mp he
  obtain ⟨-, -, -, h', -⟩ := (equilibrium_iff 𝔼 hP hB0 hkB0 hs1' hpv').mp he'
  rw [h, h', hsame]

/-- Cochrane (2023), p. 8: "governments can run large deficits `s₀ < 0` … with no inflation",
and "inflation can break out … despite healthy debt and deficits": for any current surplus or
deficit `s₀`, any `B₋₁ > 0`, `β > 0` and any target price level `P̄ > 0`, there is an expected
future surplus `E₀s₁` with `B₋₁/(s₀ + βE₀s₁) = P̄` (and a positive present value). -/
theorem price0_any_level {Bm1 s0 β Pbar : ℝ} (hB : 0 < Bm1) (hβ : 0 < β) (hP : 0 < Pbar) :
    ∃ e : ℝ, 0 < s0 + β * e ∧ Bm1 / (s0 + β * e) = Pbar := by
  refine ⟨(Bm1 / Pbar - s0) / β, ?_, ?_⟩
  · have : s0 + β * ((Bm1 / Pbar - s0) / β) = Bm1 / Pbar := by field_simp; ring
    rw [this]; positivity
  · have : s0 + β * ((Bm1 / Pbar - s0) / β) = Bm1 / Pbar := by field_simp; ring
    rw [this]; field_simp

/-! ### Genuine uncertainty: a coin-flip economy -/

/-- Cochrane (2023), §1.3, p. 8 (the expectation `E₀` under genuine uncertainty): in the
coin-flip tree, with `B₋₁ = B₀ = 1`, `s₀ = 0`, `β = 1/2` and the random surplus
`s₁ = 1 + 𝟙(first flip heads)`, an equilibrium exists, and in every equilibrium the date-1
price level is random: `P₁ = 1/2` after heads and `P₁ = 1` after tails, while `P₀ = 4/3`. -/
theorem coin_equilibrium :
    (∃ p : (Bool × Bool → ℝ) × (Bool × Bool → ℝ) × (Bool × Bool → ℝ),
      Equilibrium coinSystem (1 / 2) 1 1 0 (1 + firstHeads) p.1 p.2.1 p.2.2) ∧
    ∀ P0 P1 Q0 : Bool × Bool → ℝ,
      Equilibrium coinSystem (1 / 2) 1 1 0 (1 + firstHeads) P0 P1 Q0 →
        P1 (true, true) = 1 / 2 ∧ P1 (false, false) = 1 ∧ ∀ ω, P0 ω = 4 / 3 := by
  have hP : coinSystem.PullOut := finiteTree_pullOut coinTree
  have hE : ∀ ω, coinSystem.E 0 (1 + firstHeads) ω = 3 / 2 := by
    intro ω
    have h1 : coinSystem.E 0 (1 : Bool × Bool → ℝ) = fun _ => 1 := coinSystem.const 0 1
    rw [map_add, Pi.add_apply, h1, coinSystem_E0_firstHeads]
    norm_num
  have hk1 : Known coinSystem 0 (1 : Bool × Bool → ℝ) := known_const coinSystem 0 1
  have hk0 : Known coinSystem 0 (0 : Bool × Bool → ℝ) := known_const coinSystem 0 0
  have hs1 : ∀ ω, 0 < (1 + firstHeads) ω := by
    intro ω
    simp only [Pi.add_apply, Pi.one_apply, firstHeads]
    split_ifs <;> norm_num
  have hpv : ∀ ω, 0 < pv coinSystem (1 / 2) 0 (1 + firstHeads) ω := by
    intro ω
    simp only [pv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hE]
    norm_num
  have hpos : ∀ ω, (0 : ℝ) < (1 : Bool × Bool → ℝ) ω := fun _ => one_pos
  refine ⟨(equilibrium_existsUnique coinSystem hP hpos hk1 hpos hk1 hk0 hs1 hpv).exists, ?_⟩
  intro P0 P1 Q0 he
  obtain ⟨-, -, h1, h0, -⟩ := (equilibrium_iff coinSystem hP hpos hk1 hs1 hpv).mp he
  refine ⟨?_, ?_, fun ω => ?_⟩
  · rw [h1]; simp [firstHeads]; norm_num
  · rw [h1]; simp [firstHeads]
  · rw [h0]
    simp only [pv, Pi.div_apply, Pi.one_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, hE]
    norm_num

end Cochrane.TwoPeriodModel.TwoPeriod
