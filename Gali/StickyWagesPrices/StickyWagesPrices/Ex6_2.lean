/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyWagesPrices.Ex6_1

/-!
# Exercise 6.2: optimal monetary policy with wages set in advance

Galí (2015), Chapter 6, Exercise 6.2, pp. 195–196. A competitive firm with `y_t = a_t + n_t`
and flexible prices (so `p = w − a`, `firm_optimal_iff` in `Ex6_1`), productivity
`a_t = ρ_a a_{t−1} + ε^a_t`, labour supply `w − p = φ n`, and the dynamic IS equation
`y_t = −σ⁻¹(i_t − E_t π_{t+1} − ρ) + E_t y_{t+1}`. Dates are `t + 1` for `t : ℕ`; date-0
values are initial conditions, and the book's `E_{t−1}` is `E_t` applied to date-`t + 1`
variables.

## (a) Flexible wages and prices
* `flex_iff`: equilibrium ⇔ `n = a/φ`, `y = (1 + φ) a/φ`, `w − p = a` and the real rate equals
  the natural rate `r_t = ρ + σ(1 + φ)(ρ_a − 1) a_t/φ` (`rnat`).
* `flex_any_price`, `flex_two_equilibria`: nominal indeterminacy — every price path is an
  equilibrium path; two equilibria with different inflation and nominal rates are exhibited.

## (b) Wages set in advance
`WageInAdvance`: `w_t = E_{t−1} p_t + φ E_{t−1} n_t`. Part (b) poses no question (survey
error 9); it only introduces this rule.

## (c) The simple rule `i_t = ρ + φ_π π_t`
* `wage_facts`: under any policy, `E_{t−1} n_t = ρ_a a_{t−1}/φ`,
  `p_t − E_{t−1} p_t = −ε^a_t`, and the real wage is `w_t − p_t = a_t`.
* `expected_IS`, `n_from_IS`: the IS equation in expectation and solved for employment.
* `taylor_unique`: for `φ_π > 1`, `|ρ_a| < 1`, bounded `a`, every equilibrium with bounded
  inflation has `E_{t−1} π_t = γ a_{t−1}`, `π_t = γ a_{t−1} − ε^a_t`,
  `n_t = a_t/φ + c_ε ε^a_t`, `y_t = (1 + φ) a_t/φ + c_ε ε^a_t`, `w_t − p_t = a_t`,
  `γ = K ρ_a/(φ_π − ρ_a)`, `c_ε = φ_π (K + φ_π − ρ_a)/(σ(φ_π − ρ_a))`, `K = σ(1 + φ)(ρ_a − 1)/φ`.
* `taylor_exists`: this equilibrium exists (for any initial price level known at date 0)
  and has bounded inflation.

## (d) Optimal policy
* `optimal_real_rate`: in any equilibrium replicating the (efficient, by the exercise's
  assumption) flexible allocation `n = a/φ`, the real rate is the natural rate; the
  allocation is feasible under sticky wages (`optimal_exists`).
* `optimal_unique`, `optimal_exists`: the rule `i_t = r_t + φ_π E_{t−1} π_t` (natural rate
  plus a response to *expected* inflation) with `φ_π > 1` implements it as the unique
  equilibrium with bounded inflation: `n = a/φ`, `E_{t−1} π_t = 0`, `π_t = −ε^a_t`.
-/

namespace Gali.StickyWagesPrices.Ex6_2

open Gali.StickyWagesPrices.Ex6_1

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Exercise 6.2(a), p. 195: the slope `K = σ(1 + φ)(ρ_a − 1)/φ` of the natural
real rate in productivity. -/
noncomputable def Kc (σ φ ρa : ℝ) : ℝ := σ * (1 + φ) * (ρa - 1) / φ

/-- Galí (2015), Exercise 6.2(a), p. 195: the natural real rate
`r_t = ρ + σ(1 + φ)(ρ_a − 1) a_t/φ`. -/
noncomputable def rnat (σ ρ φ ρa : ℝ) (a : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (fun _ => ρ) + Kc σ φ ρa • a t

/-- Galí (2015), Exercise 6.2, p. 195: expected inflation `E_t π_{t+1} = E_t p_{t+1} − p_t`. -/
def qE (p : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := 𝔼.E t (p (t + 1)) - p t

/-! ### (a) Flexible wages and prices -/

/-- Galí (2015), Exercise 6.2(a), p. 195 (**necessary and sufficient**): the flexible
equilibrium has `n = a/φ`, `y = (1 + φ) a/φ`, `w − p = a`, and the real rate
`i_t − E_t π_{t+1}` equals the natural rate `ρ + σ(1 + φ)(ρ_a − 1) a_t/φ`. -/
theorem flex_iff {φ σ ρ ρa : ℝ} (hφ : φ ≠ 0) (hσ : σ ≠ 0) {a n y w p i : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) :
    (FlexEq φ a n y w p ∧ IS 𝔼 σ ρ y p i) ↔
      (∀ t, n t = φ⁻¹ • a t ∧ y t = ((1 + φ) / φ) • a t ∧ w t - p t = a t) ∧
        ∀ t, i t - qE 𝔼 p t = rnat σ ρ φ ρa a t := by
  rw [flexEq_iff hφ]
  refine and_congr_right fun hf => ?_
  have hy : ∀ t, y t = ((1 + φ) / φ) • a t := fun t => (hf t).2.1
  constructor
  · intro his t
    have e := his t
    rw [hy t, hy (t + 1), map_smul, ha.2 t] at e
    funext ω
    have e' := congrFun e ω
    unfold qE rnat Kc
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at e' ⊢
    linear_combination (norm := skip) σ * e'
    field_simp
    ring
  · intro hr t
    rw [hy t, hy (t + 1), map_smul, ha.2 t]
    have e := hr t
    funext ω
    have e' := congrFun e ω
    unfold qE rnat Kc at e'
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at e' ⊢
    linear_combination (norm := skip) σ⁻¹ * e'
    field_simp
    ring

/-- Galí (2015), Exercise 6.2(a), p. 196 (**nominal indeterminacy**): for every price path
`p`, the flexible allocation with `w = p + a` and `i_t = r_t + E_t π_{t+1}` is an
equilibrium. -/
theorem flex_any_price {φ σ ρ ρa : ℝ} (hφ : φ ≠ 0) (hσ : σ ≠ 0) {a : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (p : ℕ → Ω → ℝ) :
    FlexEq φ a (fun t => φ⁻¹ • a t) (fun t => ((1 + φ) / φ) • a t) (fun t => p t + a t) p ∧
      IS 𝔼 σ ρ (fun t => ((1 + φ) / φ) • a t) p
        (fun t => rnat σ ρ φ ρa a t + qE 𝔼 p t) :=
  (flex_iff 𝔼 hφ hσ ha).mpr ⟨fun t => ⟨rfl, rfl, by abel⟩, fun t => by abel⟩

/-- Galí (2015), Exercise 6.2(a), p. 196 (**two distinct equilibria**): with a constant price
level and with prices rising one-for-one (`p_t = t`) the real allocation is the same, but
inflation and the nominal rate differ, so they are not determined. -/
theorem flex_two_equilibria [Nonempty Ω] {φ σ ρ ρa : ℝ} (hφ : φ ≠ 0) (hσ : σ ≠ 0)
    {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) :
    ∃ p₁ p₂ i₁ i₂ : ℕ → Ω → ℝ,
      (FlexEq φ a (fun t => φ⁻¹ • a t) (fun t => ((1 + φ) / φ) • a t) (fun t => p₁ t + a t)
          p₁ ∧ IS 𝔼 σ ρ (fun t => ((1 + φ) / φ) • a t) p₁ i₁) ∧
      (FlexEq φ a (fun t => φ⁻¹ • a t) (fun t => ((1 + φ) / φ) • a t) (fun t => p₂ t + a t)
          p₂ ∧ IS 𝔼 σ ρ (fun t => ((1 + φ) / φ) • a t) p₂ i₂) ∧
      p₁ 1 - p₁ 0 ≠ p₂ 1 - p₂ 0 ∧ i₁ 0 ≠ i₂ 0 := by
  refine ⟨fun _ _ => 0, fun t _ => (t : ℝ), _, _, flex_any_price 𝔼 hφ hσ ha _,
    flex_any_price 𝔼 hφ hσ ha _, ?_, ?_⟩
  · intro h
    have := congrFun h (Classical.arbitrary Ω)
    simp at this
  · intro h
    have := congrFun h (Classical.arbitrary Ω)
    have hc := 𝔼.const 0 (1 : ℝ)
    have hz := 𝔼.const 0 (0 : ℝ)
    unfold qE at this
    simp only [zero_add, Nat.cast_one, Nat.cast_zero, Pi.add_apply,
      Pi.sub_apply] at this
    rw [hc, hz] at this
    norm_num at this

/-! ### (b) Wages set in advance -/

/-- Galí (2015), Exercise 6.2(b), p. 196: nominal wages set at the end of the previous period,
`w_t = E_{t−1} p_t + φ E_{t−1} n_t` (stated for dates `t + 1`). Part (b) itself asks no
question (survey error 9): it only introduces this rule, used in (c) and (d). -/
def WageInAdvance (φ : ℝ) (p n w : ℕ → Ω → ℝ) : Prop :=
  ∀ t, w (t + 1) = 𝔼.E t (p (t + 1)) + φ • 𝔼.E t (n (t + 1))

/-- Galí (2015), Exercise 6.2, p. 195: the IS equation from date 1 on,
`y_{t+1} = −σ⁻¹(i_{t+1} − E_{t+1} π_{t+2} − ρ) + E_{t+1} y_{t+2}`. -/
def ISfwd (σ ρ : ℝ) (y p i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, y (t + 1) = -(σ⁻¹ • (i (t + 1) - qE 𝔼 p (t + 1) - fun _ => ρ)) +
    𝔼.E (t + 1) (y (t + 1 + 1))

/-- Galí (2015), Exercise 6.2(b)–(d), pp. 195–196: the sticky-wage economy (technology,
`p = w − a`, wages set in advance, IS equation), before monetary policy is specified. -/
def Block (φ σ ρ : ℝ) (a n y w p i : ℕ → Ω → ℝ) : Prop :=
  (∀ t, y t = a t + n t) ∧ PriceEq a w p ∧ WageInAdvance 𝔼 φ p n w ∧ ISfwd 𝔼 σ ρ y p i

/-! ### (c) The simple rule -/

/-- Galí (2015), Exercise 6.2(c), p. 196 (key facts, under any policy): with wages set in
advance, `E_t n_{t+1} = ρ_a a_t/φ`, `p_{t+1} − E_t p_{t+1} = −ε^a_{t+1}` and the real wage is
`w_t − p_t = a_t`. -/
theorem wage_facts {φ σ ρ ρa : ℝ} (hφ : φ ≠ 0) {a n y w p i : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (hb : Block 𝔼 φ σ ρ a n y w p i) (t : ℕ) :
    𝔼.E t (n (t + 1)) = (ρa / φ) • a t ∧
      p (t + 1) - 𝔼.E t (p (t + 1)) = -(a (t + 1) - ρa • a t) ∧ w t - p t = a t := by
  obtain ⟨_, hpe, hw, _⟩ := hb
  have hwE : 𝔼.E t (w (t + 1)) = w (t + 1) := by
    rw [hw t, map_add, map_smul, 𝔼.E_E_self, 𝔼.E_E_self]
  have hpE : 𝔼.E t (p (t + 1)) = w (t + 1) - ρa • a t := by
    rw [hpe (t + 1), map_sub, hwE, ha.2 t]
  refine ⟨?_, ?_, by rw [hpe t]; abel⟩
  · have e := hw t
    rw [hpE] at e
    funext ω
    have e' := congrFun e ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e' ⊢
    field_simp
    linarith
  · rw [hpE, hpe (t + 1)]
    abel

/-- Galí (2015), Exercise 6.2(c), p. 196: expected output, `E_t y_{t+1} = (1 + φ)ρ_a a_t/φ`. -/
theorem expected_y {φ σ ρ ρa : ℝ} (hφ : φ ≠ 0) {a n y w p i : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (hb : Block 𝔼 φ σ ρ a n y w p i) (t : ℕ) :
    𝔼.E t (y (t + 1)) = ((1 + φ) / φ * ρa) • a t := by
  rw [hb.1 (t + 1), map_add, ha.2 t, (wage_facts 𝔼 hφ ha hb t).1, ← add_smul]
  congr 1
  field_simp
  ring

/-- Galí (2015), Exercise 6.2(c)–(d), p. 196: the IS equation in expectation,
`E_t i_{t+1} − ρ − E_t E_{t+1} π_{t+2} = K ρ_a a_t`, under any policy. -/
theorem expected_IS {φ σ ρ ρa : ℝ} (hφ : φ ≠ 0) (hσ : σ ≠ 0) {a n y w p i : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (hb : Block 𝔼 φ σ ρ a n y w p i) (t : ℕ) :
    𝔼.E t (i (t + 1)) - (fun _ => ρ) - 𝔼.E t (qE 𝔼 p (t + 1)) = (Kc σ φ ρa * ρa) • a t := by
  have e := congrArg (𝔼.E t) (hb.2.2.2 t)
  have hEy2 : 𝔼.E t (y (t + 1 + 1)) = ((1 + φ) / φ * ρa * ρa) • a t := by
    rw [← 𝔼.tower (Nat.le_succ t), expected_y 𝔼 hφ ha hb (t + 1), map_smul, ha.2 t, smul_smul]
  rw [map_add, 𝔼.tower (Nat.le_succ t), hEy2, map_neg, map_smul, map_sub, map_sub, 𝔼.const,
    expected_y 𝔼 hφ ha hb t] at e
  funext ω
  have e' := congrFun e ω
  unfold Kc
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at e' ⊢
  linear_combination (norm := skip) σ * e'
  field_simp
  ring

/-- Galí (2015), Exercise 6.2(c)–(d), p. 196: the IS equation solved for employment,
`n_{t+1} = a_{t+1}/φ + (K/σ) a_{t+1} − σ⁻¹(i_{t+1} − E_{t+1} π_{t+2} − ρ)`. -/
theorem n_from_IS {φ σ ρ ρa : ℝ} (hφ : φ ≠ 0) (hσ : σ ≠ 0) {a n y w p i : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (hb : Block 𝔼 φ σ ρ a n y w p i) (t : ℕ) :
    n (t + 1) = φ⁻¹ • a (t + 1) + (Kc σ φ ρa / σ) • a (t + 1) -
      σ⁻¹ • (i (t + 1) - qE 𝔼 p (t + 1) - fun _ => ρ) := by
  have e := hb.2.2.2 t
  rw [expected_y 𝔼 hφ ha hb (t + 1), hb.1 (t + 1)] at e
  funext ω
  have e' := congrFun e ω
  unfold Kc
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at e' ⊢
  linear_combination (norm := skip) e'
  field_simp
  ring

/-- Galí (2015), Exercise 6.2(c), p. 196: the simple rule `i_t = ρ + φ_π π_t` (from date 1). -/
def TaylorRule (ρ φπ : ℝ) (p i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i (t + 1) = (fun _ => ρ) + φπ • (p (t + 1) - p t)

/-- Galí (2015), Exercise 6.2(c), p. 196: the response of expected inflation to productivity,
`γ = K ρ_a/(φ_π − ρ_a)`. -/
noncomputable def gam (σ φ ρa φπ : ℝ) : ℝ := Kc σ φ ρa * ρa / (φπ - ρa)

/-- Galí (2015), Exercise 6.2(c), p. 196: the response of employment to the productivity
innovation, `c_ε = φ_π (K + φ_π − ρ_a)/(σ(φ_π − ρ_a))`. -/
noncomputable def cEps (σ φ ρa φπ : ℝ) : ℝ :=
  φπ * (Kc σ φ ρa + φπ - ρa) / (σ * (φπ - ρa))

/-- Galí (2015), Exercise 6.2(c), p. 196: expected inflation is bounded when inflation is. -/
theorem qE_bounded {p : ℕ → Ω → ℝ} (hp : 𝔼.Adapted p) {M : ℝ}
    (hM : ∀ t ω, |p (t + 1) ω - p t ω| ≤ M) : BoundedProc (qE 𝔼 p) := by
  refine ⟨M, fun t ω => ?_⟩
  have h : qE 𝔼 p t = 𝔼.E t (p (t + 1) - p t) := by rw [map_sub, hp t]; rfl
  rw [h]
  exact 𝔼.abs_E_le (fun ω' => by simpa using hM t ω') t ω

/-- Galí (2015), Exercise 6.2(c), p. 196 (**uniqueness**): under `i_t = ρ + φ_π π_t` with
`φ_π > 1`, `|ρ_a| < 1` and bounded productivity, every equilibrium with bounded inflation has
`E_t π_{t+1} = γ a_t`, `π_{t+1} = γ a_t − ε^a_{t+1}`, `n_{t+1} = a_{t+1}/φ + c_ε ε^a_{t+1}`,
`y_{t+1} = (1 + φ) a_{t+1}/φ + c_ε ε^a_{t+1}`, real wage `w_t − p_t = a_t`, and nominal rate
`i_{t+1} = ρ + φ_π (γ a_t − ε^a_{t+1})`. -/
theorem taylor_unique {φ σ ρ ρa φπ : ℝ} (hφ : φ ≠ 0) (hσ : σ ≠ 0) (hφπ : 1 < φπ)
    (hρa : |ρa| < 1) {a n y w p i : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) (hab : BoundedProc a)
    (hp : 𝔼.Adapted p) (hπb : ∃ M, ∀ t ω, |p (t + 1) ω - p t ω| ≤ M)
    (hb : Block 𝔼 φ σ ρ a n y w p i) (hr : TaylorRule ρ φπ p i) :
    ∀ t, qE 𝔼 p t = gam σ φ ρa φπ • a t ∧
      p (t + 1) - p t = gam σ φ ρa φπ • a t - (a (t + 1) - ρa • a t) ∧
      n (t + 1) = φ⁻¹ • a (t + 1) + cEps σ φ ρa φπ • (a (t + 1) - ρa • a t) ∧
      y (t + 1) = ((1 + φ) / φ) • a (t + 1) + cEps σ φ ρa φπ • (a (t + 1) - ρa • a t) ∧
      w t - p t = a t ∧
      i (t + 1) = (fun _ => ρ) + φπ • (gam σ φ ρa φπ • a t - (a (t + 1) - ρa • a t)) := by
  obtain ⟨M, hM⟩ := hπb
  have hφπ0 : φπ ≠ 0 := by positivity
  have hd : φπ - ρa ≠ 0 := by
    have := (abs_lt.mp hρa).2
    linarith
  -- the forward equation for expected inflation
  have hq : ∀ t, qE 𝔼 p t = φπ⁻¹ • 𝔼.E t (qE 𝔼 p (t + 1)) +
      (Kc σ φ ρa * ρa / φπ) • a t := by
    intro t
    have e := expected_IS 𝔼 hφ hσ ha hb t
    rw [hr t, map_add, 𝔼.const, map_smul, map_sub, hp t,
      show 𝔼.E t (p (t + 1)) - p t = qE 𝔼 p t from rfl] at e
    funext ω
    have e' := congrFun e ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e' ⊢
    field_simp
    linarith
  have hg : ∀ t, gam σ φ ρa φπ • a t = φπ⁻¹ • 𝔼.E t (gam σ φ ρa φπ • a (t + 1)) +
      (Kc σ φ ρa * ρa / φπ) • a t := by
    intro t
    rw [map_smul, ha.2 t]
    funext ω
    unfold gam
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hinv : |φπ⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith : (0 : ℝ) < φπ)]
    exact inv_lt_one_of_one_lt₀ hφπ
  have hgb : BoundedProc fun t => gam σ φ ρa φπ • a t := by
    obtain ⟨B, hB⟩ := hab
    refine ⟨|gam σ φ ρa φπ| * B, fun t ω => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hB t ω) (abs_nonneg _)
  have hqe : qE 𝔼 p = fun t => gam σ φ ρa φπ • a t :=
    𝔼.forward_unique hinv hq hg (qE_bounded 𝔼 hp hM) hgb
  have hqt : ∀ t, qE 𝔼 p t = gam σ φ ρa φπ • a t := fun t => by rw [hqe]
  have hπ : ∀ t, p (t + 1) - p t = gam σ φ ρa φπ • a t - (a (t + 1) - ρa • a t) := by
    intro t
    have e := (wage_facts 𝔼 hφ ha hb t).2.1
    calc p (t + 1) - p t = (𝔼.E t (p (t + 1)) - p t) + (p (t + 1) - 𝔼.E t (p (t + 1))) := by
          abel
      _ = gam σ φ ρa φπ • a t + -(a (t + 1) - ρa • a t) := by
          rw [e, show 𝔼.E t (p (t + 1)) - p t = qE 𝔼 p t from rfl, hqt t]
      _ = _ := by rw [← sub_eq_add_neg]
  have hn : ∀ t, n (t + 1) = φ⁻¹ • a (t + 1) + cEps σ φ ρa φπ • (a (t + 1) - ρa • a t) := by
    intro t
    rw [n_from_IS 𝔼 hφ hσ ha hb t, hr t, hπ t, hqt (t + 1)]
    funext ω
    unfold cEps gam
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  intro t
  refine ⟨hqt t, hπ t, hn t, ?_, (wage_facts 𝔼 hφ ha hb t).2.2, by rw [hr t, hπ t]⟩
  rw [hb.1 (t + 1), hn t]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Galí (2015), Exercise 6.2, p. 195: the productivity innovation `ε^a_{t+1} =
a_{t+1} − ρ_a a_t` (zero at date 0). -/
def innov (ρa : ℝ) (a : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => a (t + 1) - ρa • a t

/-- Galí (2015), Exercise 6.2(c)–(d), p. 196: the price path `p_{t+1} = p_t + g a_t −
ε^a_{t+1}` from the initial price level `p_0 = c`. -/
def pPath (g ρa : ℝ) (a : ℕ → Ω → ℝ) (c : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => c
  | t + 1 => pPath g ρa a c t + g • a t - innov ρa a (t + 1)

/-- Galí (2015), Exercise 6.2, p. 195: the innovation is known at its date. -/
theorem innov_adapted {ρa : ℝ} {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) :
    𝔼.Adapted (innov ρa a) := by
  intro t
  cases t with
  | zero => exact map_zero _
  | succ t =>
    simp only [innov]
    rw [map_sub, map_smul, ha.1 (t + 1), ← ha.1 t, 𝔼.known (Nat.le_succ t)]

/-- Galí (2015), Exercise 6.2, p. 195: the innovation is unforecastable, `E_t ε^a_{t+1} = 0`. -/
theorem innov_E {ρa : ℝ} {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) (t : ℕ) :
    𝔼.E t (innov ρa a (t + 1)) = 0 := by
  simp only [innov]
  rw [map_sub, map_smul, ha.2 t, ha.1 t, sub_self]

/-- Galí (2015), Exercise 6.2(c)–(d), p. 196: the price path is adapted. -/
theorem pPath_adapted {g ρa : ℝ} {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) {c : Ω → ℝ}
    (hc : 𝔼.E 0 c = c) : 𝔼.Adapted (pPath g ρa a c) := by
  intro t
  induction t with
  | zero => exact hc
  | succ t ih =>
    simp only [pPath]
    rw [map_sub, map_add, map_smul, innov_adapted 𝔼 ha (t + 1), ← ih, ← ha.1 t,
      𝔼.known (Nat.le_succ t), 𝔼.known (Nat.le_succ t)]

/-- Galí (2015), Exercise 6.2(c)–(d), p. 196: along the price path, `E_t p_{t+1} = p_t + g a_t`. -/
theorem pPath_E {g ρa : ℝ} {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) {c : Ω → ℝ}
    (hc : 𝔼.E 0 c = c) (t : ℕ) :
    𝔼.E t (pPath g ρa a c (t + 1)) = pPath g ρa a c t + g • a t := by
  simp only [pPath]
  rw [map_sub, map_add, map_smul, innov_E 𝔼 ha t, pPath_adapted 𝔼 ha hc t, ha.1 t, sub_zero]

/-- Galí (2015), Exercise 6.2(c), p. 196 (**existence**): for every initial price level known
at date 0, the closed-form processes of `taylor_unique` (`p_{t+1} = p_t + γ a_t − ε^a_{t+1}`,
`w = p + a`, `n = a/φ + c_ε ε^a`, `y = a + n`, `i_{t+1} = ρ + φ_π π_{t+1}`) are an equilibrium
under the simple rule, with adapted prices and, for bounded `a`, bounded inflation. -/
theorem taylor_exists {φ σ ρ ρa φπ : ℝ} (hφ : φ ≠ 0) (hσ : σ ≠ 0) (hd : φπ - ρa ≠ 0)
    {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) {c : Ω → ℝ} (hc : 𝔼.E 0 c = c) :
    let p := pPath (gam σ φ ρa φπ) ρa a c
    let n := fun t => φ⁻¹ • a t + cEps σ φ ρa φπ • innov ρa a t
    Block 𝔼 φ σ ρ a n (fun t => a t + n t) (fun t => p t + a t) p
        (fun t => (fun _ => ρ) + φπ • (p t - p (t - 1))) ∧
      TaylorRule ρ φπ p (fun t => (fun _ => ρ) + φπ • (p t - p (t - 1))) ∧ 𝔼.Adapted p ∧
      (BoundedProc a → ∃ M, ∀ t ω, |p (t + 1) ω - p t ω| ≤ M) := by
  intro p n
  have hpE := pPath_E (g := gam σ φ ρa φπ) 𝔼 ha hc
  refine ⟨⟨fun t => rfl, fun t => (add_sub_cancel_right (p t) (a t)).symm, fun t => ?_,
    fun t => ?_⟩, fun t => rfl,
    pPath_adapted 𝔼 ha hc, ?_⟩
  · -- wages set in advance
    have hnE : 𝔼.E t (n (t + 1)) = (φ⁻¹ * ρa) • a t := by
      simp only [n]
      rw [map_add, map_smul, map_smul, ha.2 t, innov_E 𝔼 ha t, smul_zero, add_zero, smul_smul]
    rw [hnE, hpE t]
    funext ω
    simp only [p, pPath, innov, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · -- the IS equation
    have hyE : 𝔼.E (t + 1) (a (t + 1 + 1) + n (t + 1 + 1)) =
        ((1 + φ⁻¹) * ρa) • a (t + 1) := by
      simp only [n]
      rw [map_add, map_add, map_smul, map_smul, ha.2 (t + 1), innov_E 𝔼 ha (t + 1), smul_zero,
        add_zero, smul_smul, ← add_smul]
      congr 1
      ring
    have hq : qE 𝔼 p (t + 1) = gam σ φ ρa φπ • a (t + 1) := by
      unfold qE
      rw [hpE (t + 1)]
      abel
    rw [hyE, hq]
    funext ω
    simp only [n, p, pPath, innov, Nat.add_sub_cancel, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
    unfold cEps gam Kc
    field_simp
    ring
  · rintro ⟨B, hB⟩
    refine ⟨|gam σ φ ρa φπ| * B + B + |ρa| * B, fun t ω => ?_⟩
    simp only [p, pPath, innov, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have e1 := hB t ω
    have e2 := hB (t + 1) ω
    have h1 : |gam σ φ ρa φπ * a t ω| ≤ |gam σ φ ρa φπ| * B := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
    have h2 : |ρa * a t ω| ≤ |ρa| * B := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
    calc |pPath (gam σ φ ρa φπ) ρa a c t ω + gam σ φ ρa φπ * a t ω -
          (a (t + 1) ω - ρa * a t ω) - pPath (gam σ φ ρa φπ) ρa a c t ω|
        = |gam σ φ ρa φπ * a t ω - a (t + 1) ω + ρa * a t ω| := by ring_nf
      _ ≤ |gam σ φ ρa φπ * a t ω - a (t + 1) ω| + |ρa * a t ω| := abs_add_le _ _
      _ ≤ |gam σ φ ρa φπ * a t ω| + |a (t + 1) ω| + |ρa * a t ω| := by
          gcongr; exact abs_sub _ _
      _ ≤ _ := by linarith

/-! ### (d) Optimal policy -/

/-- Galí (2015), Exercise 6.2(d), p. 196: in any equilibrium replicating the flexible
allocation `n = a/φ` (efficient by the exercise's assumption), whatever the policy, the real
rate equals the natural rate: `i_{t+1} − E_{t+1} π_{t+2} = r_{t+1}`. -/
theorem optimal_real_rate {φ σ ρ ρa : ℝ} (hφ : φ ≠ 0) (hσ : σ ≠ 0)
    {a n y w p i : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) (hb : Block 𝔼 φ σ ρ a n y w p i)
    (hflex : ∀ t, n t = φ⁻¹ • a t) (t : ℕ) :
    i (t + 1) - qE 𝔼 p (t + 1) = rnat σ ρ φ ρa a (t + 1) := by
  have e := n_from_IS 𝔼 hφ hσ ha hb t
  rw [hflex (t + 1)] at e
  funext ω
  have e' := congrFun e ω
  unfold rnat
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e' ⊢
  linear_combination (norm := skip) σ * e'
  field_simp
  ring

/-- Galí (2015), Exercise 6.2(d), p. 196: the implementing rule
`i_t = r_t + φ_π E_{t−1} π_t` (natural rate plus a response to expected inflation). -/
def OptRule (σ ρ φ ρa φπ : ℝ) (a p i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i (t + 1) = rnat σ ρ φ ρa a (t + 1) + φπ • qE 𝔼 p t

/-- Galí (2015), Exercise 6.2(d), p. 196 (**uniqueness**): under `OptRule` with `φ_π > 1`,
every equilibrium with bounded inflation replicates the flexible allocation,
`n = a/φ`, `y = (1 + φ) a/φ`, with `E_t π_{t+1} = 0`, `π_{t+1} = −ε^a_{t+1}`, the real rate at
its natural level, and real wage `w − p = a`. -/
theorem optimal_unique {φ σ ρ ρa φπ : ℝ} (hφ : φ ≠ 0) (hσ : σ ≠ 0) (hφπ : 1 < φπ)
    {a n y w p i : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) (hp : 𝔼.Adapted p)
    (hπb : ∃ M, ∀ t ω, |p (t + 1) ω - p t ω| ≤ M)
    (hb : Block 𝔼 φ σ ρ a n y w p i) (hr : OptRule 𝔼 σ ρ φ ρa φπ a p i) :
    ∀ t, qE 𝔼 p t = 0 ∧ p (t + 1) - p t = -(a (t + 1) - ρa • a t) ∧
      n (t + 1) = φ⁻¹ • a (t + 1) ∧ y (t + 1) = ((1 + φ) / φ) • a (t + 1) ∧
      i (t + 1) - qE 𝔼 p (t + 1) = rnat σ ρ φ ρa a (t + 1) ∧ w t - p t = a t := by
  obtain ⟨M, hM⟩ := hπb
  have hφπ0 : φπ ≠ 0 := by positivity
  have hqa : ∀ t, 𝔼.E t (qE 𝔼 p t) = qE 𝔼 p t := fun t => by
    unfold qE
    rw [map_sub, 𝔼.E_E_self, hp t]
  have hq : ∀ t, qE 𝔼 p t = φπ⁻¹ • 𝔼.E t (qE 𝔼 p (t + 1)) + 0 := by
    intro t
    have e := expected_IS 𝔼 hφ hσ ha hb t
    rw [hr t, map_add, map_smul, hqa t] at e
    unfold rnat at e
    rw [map_add, 𝔼.const, map_smul, ha.2 t] at e
    funext ω
    have e' := congrFun e ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e' ⊢
    field_simp
    linarith
  have hz : ∀ t, (0 : ℕ → Ω → ℝ) t = φπ⁻¹ • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + 0 := fun t => by
    simp
  have hinv : |φπ⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith : (0 : ℝ) < φπ)]
    exact inv_lt_one_of_one_lt₀ hφπ
  have hqe : qE 𝔼 p = 0 :=
    𝔼.forward_unique hinv hq hz (qE_bounded 𝔼 hp hM) ⟨0, fun t ω => by simp⟩
  have hqt : ∀ t, qE 𝔼 p t = 0 := fun t => by rw [hqe]; rfl
  have hn : ∀ t, n (t + 1) = φ⁻¹ • a (t + 1) := by
    intro t
    rw [n_from_IS 𝔼 hφ hσ ha hb t, hr t, hqt t, hqt (t + 1)]
    funext ω
    unfold rnat
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    field_simp
    ring
  intro t
  refine ⟨hqt t, ?_, hn t, ?_, ?_, (wage_facts 𝔼 hφ ha hb t).2.2⟩
  · have e := (wage_facts 𝔼 hφ ha hb t).2.1
    have e2 := hqt t
    unfold qE at e2
    rw [← e, ← sub_zero (p (t + 1) - p t), ← e2]
    abel
  · rw [hb.1 (t + 1), hn t]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · rw [hr t, hqt t, hqt (t + 1), smul_zero, add_zero, sub_zero]

/-- Galí (2015), Exercise 6.2(d), p. 196 (**existence**): for every initial price level
known at date 0, the flexible allocation `n = a/φ` with `p_{t+1} = p_t − ε^a_{t+1}`,
`w = p + a` and `i = r` (natural rate) is an equilibrium under `OptRule`, with adapted prices
and, for bounded `a`, bounded inflation. -/
theorem optimal_exists {φ σ ρ ρa φπ : ℝ} (hφ : φ ≠ 0) (hσ : σ ≠ 0)
    {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) {c : Ω → ℝ} (hc : 𝔼.E 0 c = c) :
    let p := pPath 0 ρa a c
    Block 𝔼 φ σ ρ a (fun t => φ⁻¹ • a t) (fun t => a t + φ⁻¹ • a t) (fun t => p t + a t) p
        (rnat σ ρ φ ρa a) ∧
      OptRule 𝔼 σ ρ φ ρa φπ a p (rnat σ ρ φ ρa a) ∧ 𝔼.Adapted p ∧
      (BoundedProc a → ∃ M, ∀ t ω, |p (t + 1) ω - p t ω| ≤ M) := by
  intro p
  have hpE : ∀ t, 𝔼.E t (p (t + 1)) = p t := fun t => by
    rw [pPath_E 𝔼 ha hc t, zero_smul, add_zero]
  have hq : ∀ t, qE 𝔼 p t = 0 := fun t => by
    unfold qE
    rw [hpE t, sub_self]
  refine ⟨⟨fun t => rfl, fun t => (add_sub_cancel_right (p t) (a t)).symm, fun t => ?_,
    fun t => ?_⟩, fun t => ?_,
    pPath_adapted 𝔼 ha hc, ?_⟩
  · rw [hpE t, map_smul, ha.2 t]
    funext ω
    simp only [p, pPath, innov, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · rw [hq (t + 1), map_add, map_smul, ha.2 (t + 1)]
    funext ω
    unfold rnat Kc
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply,
      Pi.zero_apply]
    field_simp
    ring
  · rw [hq t, smul_zero, add_zero]
  · rintro ⟨B, hB⟩
    refine ⟨B + |ρa| * B, fun t ω => ?_⟩
    simp only [p, pPath, innov, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have h2 : |ρa * a t ω| ≤ |ρa| * B := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB t ω) (abs_nonneg _)
    calc |pPath 0 ρa a c t ω + 0 * a t ω - (a (t + 1) ω - ρa * a t ω) - pPath 0 ρa a c t ω|
        = |-a (t + 1) ω + ρa * a t ω| := by ring_nf
      _ ≤ |-a (t + 1) ω| + |ρa * a t ω| := abs_add_le _ _
      _ ≤ _ := by rw [abs_neg]; linarith [hB (t + 1) ω]

end Gali.StickyWagesPrices.Ex6_2
