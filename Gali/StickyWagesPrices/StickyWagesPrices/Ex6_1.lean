/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyWagesPrices.Expectations
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Exercise 6.1: optimal monetary policy in a sticky wage economy

Galí (2015), Chapter 6, Exercise 6.1, pp. 194–195. A competitive firm with technology
`y_t = a_t + n_t` and flexible prices, productivity `a_t = ρ_a a_{t−1} + ε_t`, labour supply
`w_t − p_t = φ n_t`. (The book writes `ρ` both for the persistence of `a` and for the discount
rate in the IS equation of part (c); we write `ρa` for the former.)

## (a) Flexible wages and prices
* `firm_optimal_iff`, `labor_demand_log`: the competitive firm (profit `P A N − W N`) employs
  a positive amount of labour iff `W = P A`, i.e. exactly `w − p = a` in logs.
* `flexEq_iff`: the flexible equilibrium is `n = a/φ`, `y = (1 + φ) a/φ` (and `w − p = a`).

## (b) Two-period staggered wages
* `inflation_eq_iff`: given the reset wage
  `w*_t = ½(p_t + E_t p_{t+1}) + (φ/2)(n_t + E_t n_{t+1})` and `p = w − a`, the wage index
  `w_t = ½(w*_t + w*_{t−1})` holds at a date **iff** inflation satisfies
  `π_t = E_t π_{t+1} + φ ň_t + u_t`, `ň_t = n_{t−1} + E_{t−1} n_t + n_t + E_t n_{t+1}`,
  `u_t = −4 a_t − (p_t − E_{t−1} p_t)` (exact; the book only asks for "⇒").

## (c) Optimal policy: replicating the flexible allocation
* `drift_const_of_bounded`: a general lemma (not in the core): a bounded adapted `z` with
  `E_t z_{t+1} − z_t = z_t − z_{t−1}` is constant.
* `optimal_unique`: in every sticky-wage equilibrium with the flexible allocation `n = a/φ`
  and a bounded adapted reset wage, the reset and average wages are constant (`π^w ≡ 0`),
  `p_t = w̄ − a_t`, price inflation is `π_t = −Δa_t`, and the nominal rate is
  `i_t = ρ + (1 − ρ_a)(1 − σ(1 + φ)/φ) a_t`.
* `optimal_exists`: conversely, for every initial reset wage `w̄` known at date 0 these
  processes form a sticky-wage equilibrium with the flexible allocation (existence).
-/

namespace Gali.StickyWagesPrices.Ex6_1

/-! ### (a) The firm and the flexible equilibrium -/

/-- Galí (2015), Exercise 6.1, p. 194 (competitive firm, `Y = A N`): a positive employment
level `N` maximises profit `P A N' − W N'` over `N' ≥ 0` iff `W = P A`. -/
theorem firm_optimal_iff {P A W N : ℝ} (hN : 0 < N) :
    (∀ N', 0 ≤ N' → P * A * N' - W * N' ≤ P * A * N - W * N) ↔ W = P * A := by
  constructor
  · intro h
    have h0 := h 0 le_rfl
    have h2 := h (2 * N) (by positivity)
    have e : (P * A - W) * N = 0 := by nlinarith
    rcases mul_eq_zero.mp e with e | e
    · linarith
    · linarith
  · intro hW N' _
    rw [hW, sub_self, sub_self]

/-- Galí (2015), Exercise 6.1, p. 194: the condition `W = P A` is exactly `w − p = a` in
logs. -/
theorem labor_demand_log {P A W : ℝ} (hP : 0 < P) (hA : 0 < A) (hW : 0 < W) :
    W = P * A ↔ Real.log W - Real.log P = Real.log A := by
  constructor
  · intro h
    rw [h, Real.log_mul hP.ne' hA.ne']
    ring
  · intro h
    have e : Real.log W = Real.log (P * A) := by
      rw [Real.log_mul hP.ne' hA.ne']
      linarith
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr hW) (Set.mem_Ioi.mpr (mul_pos hP hA)) e

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Exercise 6.1(a), p. 194: the flexible wage and price equilibrium:
technology `y = a + n`, labour supply `w − p = φ n`, competitive labour demand `w − p = a`. -/
def FlexEq (φ : ℝ) (a n y w p : ℕ → Ω → ℝ) : Prop :=
  ∀ t, y t = a t + n t ∧ w t - p t = φ • n t ∧ w t - p t = a t

/-- Galí (2015), Exercise 6.1(a), p. 194 (**necessary and sufficient**): the flexible
equilibrium is `n_t = a_t/φ`, `y_t = (1 + φ) a_t/φ`, with real wage `w_t − p_t = a_t`. -/
theorem flexEq_iff {φ : ℝ} (hφ : φ ≠ 0) {a n y w p : ℕ → Ω → ℝ} :
    FlexEq φ a n y w p ↔
      ∀ t, n t = φ⁻¹ • a t ∧ y t = ((1 + φ) / φ) • a t ∧ w t - p t = a t := by
  refine forall_congr' fun t => ?_
  constructor
  · rintro ⟨hy, hs, hd⟩
    have hn : n t = φ⁻¹ • a t := by
      funext ω
      have e1 := congrFun hs ω
      have e2 := congrFun hd ω
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
      rw [eq_inv_mul_iff_mul_eq₀ hφ]
      linarith
    refine ⟨hn, ?_, hd⟩
    funext ω
    have e1 := congrFun hy ω
    have e2 := congrFun hn ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
    rw [e1, e2]
    field_simp
    ring
  · rintro ⟨hn, hy, hd⟩
    refine ⟨?_, ?_, hd⟩
    · funext ω
      have e1 := congrFun hy ω
      have e2 := congrFun hn ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
      rw [e1, e2]
      field_simp
      ring
    · rw [hd, hn, smul_smul, mul_inv_cancel₀ hφ, one_smul]

/-! ### (b) Two-period staggered wages -/

/-- Galí (2015), Exercise 6.1(b), p. 194: the reset wage
`w*_t = ½(p_t + E_t p_{t+1}) + (φ/2)(n_t + E_t n_{t+1})`. -/
def ResetWage (φ : ℝ) (p n wstar : ℕ → Ω → ℝ) : Prop :=
  ∀ t, wstar t = (1 / 2 : ℝ) • (p t + 𝔼.E t (p (t + 1))) + (φ / 2) • (n t + 𝔼.E t (n (t + 1)))

/-- Galí (2015), Exercise 6.1(b), p. 194: the average wage `w_t = ½(w*_t + w*_{t−1})`
(stated from date 1 on). -/
def WageIndex (w wstar : ℕ → Ω → ℝ) : Prop :=
  ∀ t, w (t + 1) = (1 / 2 : ℝ) • (wstar (t + 1) + wstar t)

/-- Galí (2015), Exercise 6.1, p. 194: flexible prices and a competitive firm, `p = w − a`. -/
def PriceEq (a w p : ℕ → Ω → ℝ) : Prop := ∀ t, p t = w t - a t

/-- Galí (2015), Exercise 6.1(b), p. 195: `ň_{t+1} = n_t + E_t n_{t+1} + n_{t+1} +
E_{t+1} n_{t+2}` (the book's `ň_t` one period later). -/
def nCheck (n : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  n t + 𝔼.E t (n (t + 1)) + n (t + 1) + 𝔼.E (t + 1) (n (t + 1 + 1))

/-- Galí (2015), Exercise 6.1(b), p. 195: `u_{t+1} = −4 a_{t+1} − (p_{t+1} − E_t p_{t+1})`. -/
def uShock (a p : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  -(4 : ℝ) • a (t + 1) - (p (t + 1) - 𝔼.E t (p (t + 1)))

/-- Galí (2015), Exercise 6.1(b), p. 195 (**necessary and sufficient**): with the reset wage
rule and `p = w − a`, the wage index `w_{t+1} = ½(w*_{t+1} + w*_t)` holds iff
`π_{t+1} = E_{t+1} π_{t+2} + φ ň_{t+1} + u_{t+1}`. -/
theorem inflation_eq_iff {φ : ℝ} {a n w p wstar : ℕ → Ω → ℝ} (hp : 𝔼.Adapted p)
    (hr : ResetWage 𝔼 φ p n wstar) (hpe : PriceEq a w p) (t : ℕ) :
    w (t + 1) = (1 / 2 : ℝ) • (wstar (t + 1) + wstar t) ↔
      p (t + 1) - p t = 𝔼.E (t + 1) (p (t + 1 + 1) - p (t + 1)) + φ • nCheck 𝔼 n t +
        uShock 𝔼 a p t := by
  have hE : 𝔼.E (t + 1) (p (t + 1 + 1) - p (t + 1)) =
      𝔼.E (t + 1) (p (t + 1 + 1)) - p (t + 1) := by
    rw [map_sub, hp (t + 1)]
  rw [hE]
  have h0 := hr t
  have h1 := hr (t + 1)
  have hw := hpe (t + 1)
  constructor
  · intro h
    funext ω
    have e0 := congrFun h0 ω
    have e1 := congrFun h1 ω
    have e2 := congrFun hw ω
    have e3 := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, nCheck,
      uShock] at e0 e1 e2 e3 ⊢
    linarith
  · intro h
    funext ω
    have e0 := congrFun h0 ω
    have e1 := congrFun h1 ω
    have e2 := congrFun hw ω
    have e3 := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, nCheck,
      uShock] at e0 e1 e2 e3 ⊢
    linarith

/-! ### (c) Optimal policy -/

/-- Galí (2015), Exercise 6.1(c), p. 195: the dynamic IS equation
`y_t = −σ⁻¹(i_t − E_t π_{t+1} − ρ) + E_t y_{t+1}`, with `E_t π_{t+1} = E_t p_{t+1} − p_t`. -/
def IS (σ ρ : ℝ) (y p i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, y t = -(σ⁻¹ • (i t - (𝔼.E t (p (t + 1)) - p t) - fun _ => ρ)) + 𝔼.E t (y (t + 1))

/-- Galí (2015), Exercise 6.1(b)–(c), pp. 194–195: an equilibrium of the sticky-wage economy
(technology, `p = w − a`, reset wage, wage index, IS equation). -/
def StickyEq (φ σ ρ : ℝ) (a n y w p wstar i : ℕ → Ω → ℝ) : Prop :=
  (∀ t, y t = a t + n t) ∧ PriceEq a w p ∧ ResetWage 𝔼 φ p n wstar ∧ WageIndex w wstar ∧
    IS 𝔼 σ ρ y p i

/-- Galí (2015), Exercise 6.1(c), p. 195 (general lemma, proved here): a bounded adapted
process whose expected change equals its last change, `E_{t+1} z_{t+2} − z_{t+1} =
z_{t+1} − z_t`, is constant. (Its expected path is linear, `E_{t+1} z_{t+1+k} =
z_{t+1} + k (z_{t+1} − z_t)`, and is bounded only with zero slope.) -/
theorem drift_const_of_bounded {z : ℕ → Ω → ℝ} (hza : 𝔼.Adapted z) (hzb : BoundedProc z)
    (hz : ∀ t, 𝔼.E (t + 1) (z (t + 1 + 1)) - z (t + 1) = z (t + 1) - z t) (t : ℕ) :
    z (t + 1) = z t := by
  obtain ⟨M, hM⟩ := hzb
  -- expected increments are constant
  have hinc : ∀ k, 𝔼.E (t + 1) (z (t + 1 + k + 1) - z (t + 1 + k)) = z (t + 1) - z t := by
    intro k
    induction k with
    | zero =>
      rw [map_sub, hza (t + 1)]
      simpa using hz t
    | succ k ih =>
      have hk := hz (t + 1 + k)
      have hk' : z (t + 1 + (k + 1) + 1) - z (t + 1 + (k + 1)) =
          𝔼.E (t + 1 + k + 1) (z (t + 1 + k + 1 + 1) - z (t + 1 + k + 1)) +
            (z (t + 1 + (k + 1) + 1) - z (t + 1 + (k + 1)) -
              𝔼.E (t + 1 + k + 1) (z (t + 1 + k + 1 + 1) - z (t + 1 + k + 1))) := by abel
      have hle : t + 1 ≤ t + 1 + k + 1 := by omega
      have hex : 𝔼.E (t + 1) (z (t + 1 + (k + 1) + 1) - z (t + 1 + (k + 1))) =
          𝔼.E (t + 1) (𝔼.E (t + 1 + k + 1)
            (z (t + 1 + k + 1 + 1) - z (t + 1 + k + 1))) := by
        rw [𝔼.tower hle]
        rfl
      rw [hex, map_sub (𝔼.E (t + 1 + k + 1)), hza (t + 1 + k + 1), hk, ← ih]
  -- expected levels are linear in the horizon
  have hlev : ∀ k : ℕ, 𝔼.E (t + 1) (z (t + 1 + k)) = z (t + 1) + (k : ℝ) • (z (t + 1) - z t) := by
    intro k
    induction k with
    | zero => simpa using hza (t + 1)
    | succ k ih =>
      have hs : z (t + 1 + (k + 1)) = z (t + 1 + k) + (z (t + 1 + k + 1) - z (t + 1 + k)) := by
        rw [← add_assoc]; abel
      rw [hs, map_add, ih, hinc k]
      push_cast
      rw [add_smul, one_smul]
      abel
  funext ω
  by_contra hne
  have hd : z (t + 1) ω - z t ω ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * M / |z (t + 1) ω - z t ω|)
  have hb := 𝔼.abs_E_le (hM (t + 1 + k)) (t + 1) ω
  rw [hlev k] at hb
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hb
  have h1 := hM (t + 1) ω
  have hpos : 0 < |z (t + 1) ω - z t ω| := abs_pos.mpr hd
  have hkd : 2 * M < (k : ℝ) * |z (t + 1) ω - z t ω| := by
    rwa [div_lt_iff₀ hpos] at hk
  have htri : (k : ℝ) * |z (t + 1) ω - z t ω| ≤
      |z (t + 1) ω + (k : ℝ) * (z (t + 1) ω - z t ω)| + |z (t + 1) ω| := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hkabs : (k : ℝ) * |z (t + 1) ω - z t ω| = |(k : ℝ) * (z (t + 1) ω - z t ω)| := by
      rw [abs_mul, abs_of_nonneg hk0]
    rw [hkabs]
    calc |(k : ℝ) * (z (t + 1) ω - z t ω)|
        = |(z (t + 1) ω + (k : ℝ) * (z (t + 1) ω - z t ω)) - z (t + 1) ω| := by ring_nf
      _ ≤ _ := abs_sub _ _
  linarith

/-- Galí (2015), Exercise 6.1(c), p. 195: the nominal rate under the optimal policy,
`i_t = ρ + (1 − ρ_a)(1 − σ(1 + φ)/φ) a_t`. -/
noncomputable def iOpt (σ ρ φ ρa : ℝ) (a : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (fun _ => ρ) + ((1 - ρa) * (1 - σ * (1 + φ) / φ)) • a t

/-- Galí (2015), Exercise 6.1(c), p. 195 (**uniqueness**): in a sticky-wage equilibrium that
replicates the flexible allocation `n = a/φ`, with a bounded adapted reset wage, the reset
wage and the average wage are constant at `w̄ = w*_0` (zero wage inflation), the price level
is `p_t = w̄ − a_t`, price inflation is `π_{t+1} = −(a_{t+1} − a_t)`, and the nominal rate is
`i_t = ρ + (1 − ρ_a)(1 − σ(1 + φ)/φ) a_t`. -/
theorem optimal_unique {φ σ ρ ρa : ℝ} (hφ : φ ≠ 0) (hσ : σ ≠ 0)
    {a n y w p wstar i : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (heq : StickyEq 𝔼 φ σ ρ a n y w p wstar i) (hflex : ∀ t, n t = φ⁻¹ • a t)
    (hza : 𝔼.Adapted wstar) (hzb : BoundedProc wstar) :
    ∀ t, wstar t = wstar 0 ∧ w t = wstar 0 ∧ w (t + 1) - w t = 0 ∧ p t = wstar 0 - a t ∧
      p (t + 1) - p t = -(a (t + 1) - a t) ∧ i t = iOpt σ ρ φ ρa a t := by
  obtain ⟨hy, hpe, hr, hwi, his⟩ := heq
  -- the reset wage in terms of the average wage
  have hrw : ∀ t, wstar t = (1 / 2 : ℝ) • (w t + 𝔼.E t (w (t + 1))) := by
    intro t
    rw [hr t, hflex t, hflex (t + 1), hpe t, hpe (t + 1)]
    funext ω
    simp only [map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hdrift : ∀ t, 𝔼.E (t + 1) (wstar (t + 1 + 1)) - wstar (t + 1) =
      wstar (t + 1) - wstar t := by
    intro t
    have e1 := hrw (t + 1)
    rw [hwi (t + 1), hwi t, map_smul, map_add, hza (t + 1)] at e1
    funext ω
    have e := congrFun e1 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    linarith
  have hconst : ∀ t, wstar t = wstar 0 := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [drift_const_of_bounded 𝔼 hza hzb hdrift t, ih]
  have hz0 : ∀ t, 𝔼.E t (wstar 0) = wstar 0 := fun t => by
    rw [← hza 0, 𝔼.known (Nat.zero_le t)]
  have hw1 : ∀ t, w (t + 1) = wstar 0 := fun t => by
    rw [hwi t, hconst (t + 1), hconst t]
    funext ω
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  have hw : ∀ t, w t = wstar 0 := by
    intro t
    cases t with
    | succ t => exact hw1 t
    | zero =>
      have e := hrw 0
      rw [hw1 0, hz0 0] at e
      funext ω
      have e' := congrFun e ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e'
      linarith
  have hp : ∀ t, p t = wstar 0 - a t := fun t => by rw [hpe t, hw t]
  intro t
  refine ⟨hconst t, hw t, by rw [hw, hw, sub_self], hp t, by rw [hp, hp]; abel, ?_⟩
  -- the nominal rate from the IS equation
  have e := his t
  rw [hy t, hy (t + 1), hflex t, hflex (t + 1), hp t, hp (t + 1), map_sub, hz0 t, map_add,
    map_smul, ha.2 t] at e
  funext ω
  have e' := congrFun e ω
  unfold iOpt
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at e' ⊢
  field_simp at e' ⊢
  linear_combination e'

/-- Galí (2015), Exercise 6.1(c), p. 195 (**existence**): for every initial reset wage `w̄`
known at date 0, constant wages `w* = w = w̄`, prices `p_t = w̄ − a_t`, the flexible
allocation `n = a/φ`, `y = (1 + φ) a/φ` and the rate `iOpt` form a sticky-wage equilibrium. -/
theorem optimal_exists {φ σ ρ ρa : ℝ} (hφ : φ ≠ 0) (hσ : σ ≠ 0) {a : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) {c : Ω → ℝ} (hc : 𝔼.E 0 c = c) :
    StickyEq 𝔼 φ σ ρ a (fun t => φ⁻¹ • a t) (fun t => ((1 + φ) / φ) • a t) (fun _ => c)
      (fun t => c - a t) (fun _ => c) (iOpt σ ρ φ ρa a) := by
  have hcE : ∀ t, 𝔼.E t c = c := fun t => by rw [← hc, 𝔼.known (Nat.zero_le t)]
  refine ⟨fun t => ?_, fun t => rfl, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · rw [map_smul, map_sub, hcE t, ha.2 t]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · funext ω
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  · rw [map_sub, hcE t, map_smul, ha.2 t]
    funext ω
    unfold iOpt
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
    field_simp
    ring

end Gali.StickyWagesPrices.Ex6_1
