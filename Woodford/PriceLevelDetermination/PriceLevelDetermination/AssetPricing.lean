/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.ExpectationsFiniteTree
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# An asset-pricing model with nominal assets

Woodford (2003), *Interest and Prices*, Chapter 2, §1.1, pp. 64–68 and p. 73, equations
(1.2)–(1.9), (1.11) and (1.25).

Random variables are `Ω → ℝ`, processes `ℕ → Ω → ℝ`, and `E_t` is an arbitrary
`ExpectationSystem` with the pull-out property `PullOut` (true for perfect foresight and for
every finite event tree). The one-period stochastic discount factor `q t = Q_{t,t+1}` is a
date-`(t+1)` random variable, and `sdf q t n = Q_{t,t+n} = ∏_{s=t+1}^{t+n} Q_{s-1,s}`
(p. 67), with `Q_{t,t} = 1`.

## Main results

* `sdf_add`, `sdf_known`, `E_sdf_mul_E`, `E_sdf_tower` (lemma L3 of the survey):
  `Q_{t,T} = Q_{t,s} Q_{s,T}` and `E_t[Q_{t,T} X] = E_t[Q_{t,s} E_s[Q_{s,T} X]]`.
* `E_q_riskless`, `riskless_gross_return`: (1.5) and the riskless case `A_{t+1} = (1+i_t)B_t`.
* `one_sub_E_q_gross_im`: `1 − E_t[Q_{t,t+1}(1+i^m_t)] = Δ_t` with `Δ ≡ (i − i^m)/(1+i)` (1.8).
* `flow_1_2_iff_flow_1_7`: the flow constraint (1.2) with (1.3)–(1.5) is equivalent to (1.7).
* `riskless_debt_dynamics`: the riskless-debt difference equation (1.6).
* `arbitrage_position`, `arbitrage_unbounded_consumption`: without (1.11) the money/short-bond
  position finances unbounded consumption with unchanged continuation wealth.
* `household_flow_eq_of_gov_flow`: the government flow constraint (1.25) makes the household
  flow constraint hold with equality under market clearing (p. 72–73).
* `MonotoneConvergence` (conditional monotone convergence), satisfied by perfect foresight
  (`perfectForesight_monotoneConvergence`) and every finite tree
  (`finiteTree_monotoneConvergence`), and `hasSum_E_sdf_mul_pv`: under it
  `E_t[Q_{t,T} ∑_n E_T[Q_{T,T+n} Y_{T+n}]] = ∑_n E_t[Q_{t,T+n} Y_{T+n}]` for nonnegative `Y`.
-/

namespace Woodford.PriceLevelDetermination.AssetPricing

open Filter Topology

variable {Ω : Type*}

/-! ### Stochastic discount factors -/

/-- Woodford (2003), p. 67: the stochastic discount factor
`Q_{t,t+n} = ∏_{s=t+1}^{t+n} Q_{s-1,s}` built from the one-period factors `q s = Q_{s,s+1}`;
`Q_{t,t} = 1` (p. 68). -/
def sdf (q : ℕ → Ω → ℝ) (t n : ℕ) : Ω → ℝ := ∏ k ∈ Finset.range n, q (t + k)

/-- Woodford (2003), p. 68: `Q_{t,t} = 1`. -/
@[simp] theorem sdf_zero (q : ℕ → Ω → ℝ) (t : ℕ) : sdf q t 0 = 1 := by
  simp [sdf]

/-- Woodford (2003), p. 67: `Q_{t,t+n+1} = Q_{t,t+n} Q_{t+n,t+n+1}`. -/
theorem sdf_succ (q : ℕ → Ω → ℝ) (t n : ℕ) : sdf q t (n + 1) = sdf q t n * q (t + n) := by
  simp [sdf, Finset.prod_range_succ]

/-- Woodford (2003), p. 67: `Q_{t,t+1}` is the one-period factor. -/
@[simp] theorem sdf_one (q : ℕ → Ω → ℝ) (t : ℕ) : sdf q t 1 = q t := by
  simp [sdf]

/-- Woodford (2003), p. 67 (lemma L3): `Q_{t,t+n+m} = Q_{t,t+n} Q_{t+n,t+n+m}`. -/
theorem sdf_add (q : ℕ → Ω → ℝ) (t n m : ℕ) :
    sdf q t (n + m) = sdf q t n * sdf q (t + n) m := by
  simp only [sdf, Finset.prod_range_add, add_assoc]

/-- Woodford (2003), p. 68 (positive discount factors): `Q_{t,t+n} ≥ 0`. -/
theorem sdf_nonneg {q : ℕ → Ω → ℝ} (hq : ∀ s ω, 0 ≤ q s ω) (t n : ℕ) (ω : Ω) :
    0 ≤ sdf q t n ω := by
  simp only [sdf, Finset.prod_apply]
  exact Finset.prod_nonneg fun k _ => hq (t + k) ω

/-- Woodford (2003), p. 68 (positive discount factors): `Q_{t,t+n} > 0`. -/
theorem sdf_pos {q : ℕ → Ω → ℝ} (hq : ∀ s ω, 0 < q s ω) (t n : ℕ) (ω : Ω) :
    0 < sdf q t n ω := by
  simp only [sdf, Finset.prod_apply]
  exact Finset.prod_pos fun k _ => hq (t + k) ω

/-! ### Information: variables known at a date -/

variable (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), p. 65 (information accumulates): a variable known at `s` is known at every
later date `T ≥ s`. -/
theorem known_of_le {s T : ℕ} (h : s ≤ T) {x : Ω → ℝ} (hx : 𝔼.E s x = x) : 𝔼.E T x = x :=
  calc 𝔼.E T x = 𝔼.E T (𝔼.E s x) := by rw [hx]
    _ = 𝔼.E s x := 𝔼.known h x
    _ = x := hx

/-- Woodford (2003), p. 66 (pull-out): the product of two date-`t` variables is known at `t`. -/
theorem known_mul (hP : 𝔼.PullOut) {t : ℕ} {a b : Ω → ℝ} (ha : 𝔼.E t a = a)
    (hb : 𝔼.E t b = b) : 𝔼.E t (a * b) = a * b := by
  rw [hP t a b ha, hb]

/-- Woodford (2003), p. 66: `1 + x` is known at `t` when `x` is. -/
theorem known_one_add {t : ℕ} {x : Ω → ℝ} (hx : 𝔼.E t x = x) :
    𝔼.E t (fun ω => 1 + x ω) = fun ω => 1 + x ω := by
  have h : (fun ω => 1 + x ω) = (fun _ => (1 : ℝ)) + x := rfl
  rw [h, map_add, 𝔼.const, hx]

/-- Woodford (2003), p. 66: expectations of nonnegative variables are nonnegative. -/
theorem E_nonneg {t : ℕ} {x : Ω → ℝ} (hx : ∀ ω, 0 ≤ x ω) (ω : Ω) : 0 ≤ 𝔼.E t x ω := by
  have h := 𝔼.mono t (show (0 : Ω → ℝ) ≤ x from hx) ω
  simpa using h

/-- Woodford (2003), p. 67: `Q_{t,t+n}` is known at date `t + n`, given that each `Q_{s,s+1}`
is known at `s + 1`. -/
theorem sdf_known (hP : 𝔼.PullOut) {q : ℕ → Ω → ℝ} (hq : ∀ s, 𝔼.E (s + 1) (q s) = q s)
    (t n : ℕ) : 𝔼.E (t + n) (sdf q t n) = sdf q t n := by
  induction n with
  | zero =>
    rw [sdf_zero]
    exact 𝔼.const (t + 0) 1
  | succ n ih =>
    rw [sdf_succ, ← add_assoc]
    exact known_mul 𝔼 hP (known_of_le 𝔼 (Nat.le_succ _) ih) (hq (t + n))

/-- Woodford (2003), p. 627 (lemma L3, pull-out plus the law of iterated expectations):
`E_t[Q_{t,t+n} E_{t+n} Y] = E_t[Q_{t,t+n} Y]`. -/
theorem E_sdf_mul_E (hP : 𝔼.PullOut) {q : ℕ → Ω → ℝ} (hq : ∀ s, 𝔼.E (s + 1) (q s) = q s)
    (t n : ℕ) (Y : Ω → ℝ) :
    𝔼.E t (sdf q t n * 𝔼.E (t + n) Y) = 𝔼.E t (sdf q t n * Y) := by
  rw [← hP (t + n) _ _ (sdf_known 𝔼 hP hq t n), 𝔼.tower (Nat.le_add_right t n)]

/-- Woodford (2003), p. 627 (lemma L3): the tower property of iterated discount factors,
`E_t[Q_{t,t+n+m} X] = E_t[Q_{t,t+n} E_{t+n}[Q_{t+n,t+n+m} X]]`. -/
theorem E_sdf_tower (hP : 𝔼.PullOut) {q : ℕ → Ω → ℝ} (hq : ∀ s, 𝔼.E (s + 1) (q s) = q s)
    (t n m : ℕ) (X : Ω → ℝ) :
    𝔼.E t (sdf q t (n + m) * X) = 𝔼.E t (sdf q t n * 𝔼.E (t + n) (sdf q (t + n) m * X)) := by
  rw [E_sdf_mul_E 𝔼 hP hq, sdf_add, mul_assoc]

/-! ### The riskless rate, the opportunity cost of money, and the flow constraint -/

/-- Woodford (2003), eq. (1.8), p. 67: the interest-rate differential
`Δ_t ≡ (i_t − i^m_t)/(1 + i_t)`, the opportunity cost of holding money. -/
noncomputable def delta (i im : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (i t ω - im t ω) / (1 + i t ω)

/-- Woodford (2003), eq. (1.11), p. 68: given `1 + i_t > 0`, `Δ_t ≥ 0` iff `i_t ≥ i^m_t`. -/
theorem delta_nonneg_iff {i im : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω} (hi : 0 < 1 + i t ω) :
    0 ≤ delta i im t ω ↔ im t ω ≤ i t ω := by
  simp only [delta]
  rw [div_nonneg_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · linarith
    · linarith
  · intro h
    exact Or.inl ⟨by linarith, hi.le⟩

/-- Woodford (2003), eq. (1.8), p. 67: `Δ_t = 0` iff `i_t = i^m_t` (given `1 + i_t > 0`). -/
theorem delta_eq_zero_iff {i im : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω} (hi : 0 < 1 + i t ω) :
    delta i im t ω = 0 ↔ i t ω = im t ω := by
  simp only [delta, div_eq_zero_iff, hi.ne', or_false, sub_eq_zero]

/-- Woodford (2003), eq. (1.5), p. 66: if a portfolio pays a riskless (date-`t` known) amount
`A_{t+1}`, its price (1.4) is `B_t = E_t[Q_{t,t+1}A_{t+1}] = A_{t+1}/(1+i_t)`. -/
theorem E_q_riskless (hP : 𝔼.PullOut) {q i : ℕ → Ω → ℝ} {t : ℕ} {A : Ω → ℝ}
    (h15 : 𝔼.E t (q t) = fun ω => (1 + i t ω)⁻¹) (hA : 𝔼.E t A = A) :
    𝔼.E t (q t * A) = fun ω => A ω / (1 + i t ω) := by
  rw [mul_comm, hP t A (q t) hA, h15]
  funext ω
  simp [div_eq_mul_inv]

/-- Woodford (2003), p. 66 (after (1.5)): a riskless portfolio satisfies
`A_{t+1} = (1 + i_t) B_t`. -/
theorem riskless_gross_return (hP : 𝔼.PullOut) {q i : ℕ → Ω → ℝ} {t : ℕ} {A B : Ω → ℝ}
    (h15 : 𝔼.E t (q t) = fun ω => (1 + i t ω)⁻¹) (hi : ∀ ω, 0 < 1 + i t ω)
    (hA : 𝔼.E t A = A) (h14 : B = 𝔼.E t (q t * A)) : A = fun ω => (1 + i t ω) * B ω := by
  rw [h14, E_q_riskless 𝔼 hP h15 hA]
  funext ω
  have := (hi ω).ne'
  field_simp

/-- Woodford (2003), eqs. (1.7)–(1.8), pp. 66–67: `1 − E_t[Q_{t,t+1}(1 + i^m_t)] = Δ_t`. -/
theorem one_sub_E_q_gross_im (hP : 𝔼.PullOut) {q i im : ℕ → Ω → ℝ} {t : ℕ}
    (h15 : 𝔼.E t (q t) = fun ω => (1 + i t ω)⁻¹) (hi : ∀ ω, 0 < 1 + i t ω)
    (him : 𝔼.E t (im t) = im t) :
    (fun ω => 1 - 𝔼.E t (q t * fun ω' => 1 + im t ω') ω) = delta i im t := by
  rw [E_q_riskless 𝔼 hP h15 (known_one_add 𝔼 him)]
  funext ω
  have := (hi ω).ne'
  simp only [delta]
  field_simp
  ring

/-- Woodford (2003), pp. 66–67, the step from (1.2)–(1.4) to (1.7): with
`W_{t+1} = (1+i^m_t)M_t + A_{t+1}` (1.3), `B_t = E_t[Q_{t,t+1}A_{t+1}]` (1.4) and (1.5),
end-of-period assets are worth `M_t + B_t = Δ_t M_t + E_t[Q_{t,t+1}W_{t+1}]`. -/
theorem portfolio_value_identity (hP : 𝔼.PullOut) {q i im M A W : ℕ → Ω → ℝ} {B : Ω → ℝ}
    {t : ℕ} (h15 : 𝔼.E t (q t) = fun ω => (1 + i t ω)⁻¹) (hi : ∀ ω, 0 < 1 + i t ω)
    (him : 𝔼.E t (im t) = im t) (hM : 𝔼.E t (M t) = M t)
    (h13 : W (t + 1) = fun ω => (1 + im t ω) * M t ω + A (t + 1) ω)
    (h14 : B = 𝔼.E t (q t * A (t + 1))) :
    M t + B = delta i im t * M t + 𝔼.E t (q t * W (t + 1)) := by
  have hk : 𝔼.E t (fun ω => (1 + im t ω) * M t ω) = fun ω => (1 + im t ω) * M t ω :=
    known_mul 𝔼 hP (known_one_add 𝔼 him) hM
  have hsplit : q t * W (t + 1) = q t * (fun ω => (1 + im t ω) * M t ω) + q t * A (t + 1) := by
    rw [h13, ← mul_add]
    rfl
  rw [hsplit, map_add, ← h14, E_q_riskless 𝔼 hP h15 hk]
  funext ω
  have := (hi ω).ne'
  simp only [Pi.add_apply, Pi.mul_apply, delta]
  field_simp
  ring

/-- Woodford (2003), eqs. (1.2) and (1.7), pp. 64–67: given (1.3)–(1.5), the flow budget
constraint (1.2) `M_t + B_t ≤ W_t + P_tY_t − T_t − P_tC_t` holds iff (1.7)
`P_tC_t + Δ_tM_t + E_t[Q_{t,t+1}W_{t+1}] ≤ W_t + (P_tY_t − T_t)` holds. -/
theorem flow_1_2_iff_flow_1_7 (hP : 𝔼.PullOut) {q i im M A W P C Y Tx : ℕ → Ω → ℝ}
    {B : Ω → ℝ} {t : ℕ} (h15 : 𝔼.E t (q t) = fun ω => (1 + i t ω)⁻¹)
    (hi : ∀ ω, 0 < 1 + i t ω) (him : 𝔼.E t (im t) = im t) (hM : 𝔼.E t (M t) = M t)
    (h13 : W (t + 1) = fun ω => (1 + im t ω) * M t ω + A (t + 1) ω)
    (h14 : B = 𝔼.E t (q t * A (t + 1))) :
    M t + B ≤ W t + P t * Y t - Tx t - P t * C t ↔
      P t * C t + delta i im t * M t + 𝔼.E t (q t * W (t + 1)) ≤
        W t + (P t * Y t - Tx t) := by
  have hid := portfolio_value_identity 𝔼 hP h15 hi him hM h13 h14
  constructor
  · intro h ω
    have h1 := h ω
    have h2 := congrFun hid ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] at h1 h2 ⊢
    linarith
  · intro h ω
    have h1 := h ω
    have h2 := congrFun hid ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] at h1 h2 ⊢
    linarith

/-- Woodford (2003), eq. (1.6), p. 66: if the household holds only riskless one-period debt
(`A_{t+1}` known at `t`) and (1.2) holds with equality at `t + 1`, then
`M_{t+1} + B_{t+1} = (1+i^m_t)M_t + (1+i_t)B_t + P_{t+1}Y_{t+1} − T_{t+1} − P_{t+1}C_{t+1}`. -/
theorem riskless_debt_dynamics (hP : 𝔼.PullOut) {q i im M A W P C Y Tx B : ℕ → Ω → ℝ}
    {t : ℕ} (h15 : 𝔼.E t (q t) = fun ω => (1 + i t ω)⁻¹) (hi : ∀ ω, 0 < 1 + i t ω)
    (hA : 𝔼.E t (A (t + 1)) = A (t + 1))
    (h13 : W (t + 1) = fun ω => (1 + im t ω) * M t ω + A (t + 1) ω)
    (h14 : B t = 𝔼.E t (q t * A (t + 1)))
    (h12 : M (t + 1) + B (t + 1) =
      W (t + 1) + P (t + 1) * Y (t + 1) - Tx (t + 1) - P (t + 1) * C (t + 1)) :
    M (t + 1) + B (t + 1) = (fun ω => (1 + im t ω) * M t ω + (1 + i t ω) * B t ω) +
      P (t + 1) * Y (t + 1) - Tx (t + 1) - P (t + 1) * C (t + 1) := by
  have hAB := riskless_gross_return 𝔼 hP h15 hi hA h14
  rw [h12, h13, hAB]

/-! ### The arbitrage when `i_t < i^m_t` (1.11) -/

/-- Woodford (2003), eq. (1.11), p. 68, the arbitrage: starting from any plan
`(C_t, M_t, B_t, A_{t+1})` at date `t`, add `m ≥ 0` (known at `t`) of money, financed by
shorting riskless bonds paying `(1+i^m_t)m` at `t+1`, and change consumption by `−Δ_t m/P_t`.
Then (1.4) holds for the new bond position, continuation wealth `W_{t+1}` (1.3) is unchanged,
and the new plan satisfies the flow constraint (1.2) iff the old one does. -/
theorem arbitrage_position (hP : 𝔼.PullOut) {q i im P : ℕ → Ω → ℝ} {t : ℕ}
    (h15 : 𝔼.E t (q t) = fun ω => (1 + i t ω)⁻¹) (hi : ∀ ω, 0 < 1 + i t ω)
    (hPpos : ∀ ω, 0 < P t ω) (him : 𝔼.E t (im t) = im t)
    {M B C A W Y Tx m : Ω → ℝ} (hm : 𝔼.E t m = m) (h14 : B = 𝔼.E t (q t * A)) :
    let M' := M + m
    let A' := A - fun ω => (1 + im t ω) * m ω
    let B' := B - fun ω => (1 + im t ω) * m ω / (1 + i t ω)
    let C' := C - fun ω => delta i im t ω * m ω / P t ω
    B' = 𝔼.E t (q t * A') ∧
      ((fun ω => (1 + im t ω) * M' ω + A' ω) = fun ω => (1 + im t ω) * M ω + A ω) ∧
      (M' + B' ≤ W + P t * Y - Tx - P t * C' ↔ M + B ≤ W + P t * Y - Tx - P t * C) := by
  intro M' A' B' C'
  have hk : 𝔼.E t (fun ω => (1 + im t ω) * m ω) = fun ω => (1 + im t ω) * m ω :=
    known_mul 𝔼 hP (known_one_add 𝔼 him) hm
  refine ⟨?_, ?_, ?_⟩
  · simp only [B', A', mul_sub, map_sub, ← h14, E_q_riskless 𝔼 hP h15 hk]
  · funext ω
    simp only [M', A', Pi.add_apply, Pi.sub_apply]
    ring
  · have key : ∀ ω, M' ω + B' ω - (W ω + P t ω * Y ω - Tx ω - P t ω * C' ω) =
        M ω + B ω - (W ω + P t ω * Y ω - Tx ω - P t ω * C ω) := by
      intro ω
      have h1 := (hi ω).ne'
      have h2 := (hPpos ω).ne'
      simp only [M', B', C', Pi.add_apply, Pi.sub_apply, delta]
      field_simp
      ring
    constructor
    · intro h ω
      have := h ω
      have := key ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] at *
      linarith
    · intro h ω
      have := h ω
      have := key ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] at *
      linarith

/-- Woodford (2003), eq. (1.11), p. 68: if `i_t ≤ i^m_t` in every date-`t` state and
`i_t < i^m_t` in state `ω` (so (1.11) fails), then for every bound `K` there is a constant money
position whose arbitrage raises consumption weakly in every state and above `K` in state `ω`,
leaving continuation wealth unchanged and preserving the flow constraint: consumption is
unbounded, so no optimal plan exists. -/
theorem arbitrage_unbounded_consumption (hP : 𝔼.PullOut) {q i im P : ℕ → Ω → ℝ} {t : ℕ}
    (h15 : 𝔼.E t (q t) = fun ω => (1 + i t ω)⁻¹) (hi : ∀ ω, 0 < 1 + i t ω)
    (hPpos : ∀ ω, 0 < P t ω) (him : 𝔼.E t (im t) = im t)
    (hle : ∀ ω, i t ω ≤ im t ω) {ω₀ : Ω} (hlt : i t ω₀ < im t ω₀)
    {M B C A W Y Tx : Ω → ℝ} (h14 : B = 𝔼.E t (q t * A)) (K : ℝ) :
    ∃ m : ℝ, 0 ≤ m ∧
      let M' := M + fun _ => m
      let A' := A - fun ω => (1 + im t ω) * m
      let B' := B - fun ω => (1 + im t ω) * m / (1 + i t ω)
      let C' := C - fun ω => delta i im t ω * m / P t ω
      B' = 𝔼.E t (q t * A') ∧
      ((fun ω => (1 + im t ω) * M' ω + A' ω) = fun ω => (1 + im t ω) * M ω + A ω) ∧
      (M' + B' ≤ W + P t * Y - Tx - P t * C' ↔ M + B ≤ W + P t * Y - Tx - P t * C) ∧
      C ≤ C' ∧ K ≤ C' ω₀ := by
  have hd : ∀ ω, delta i im t ω ≤ 0 := fun ω => by
    simp only [delta]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [hle ω]) (hi ω).le
  have hd0 : delta i im t ω₀ < 0 := by
    simp only [delta]
    exact div_neg_of_neg_of_pos (by linarith) (hi ω₀)
  set c : ℝ := max 0 ((K - C ω₀) * P t ω₀ / (-delta i im t ω₀)) with hc
  refine ⟨c, le_max_left _ _, ?_⟩
  have hpos := arbitrage_position 𝔼 hP h15 hi hPpos him (m := fun _ => c) (M := M) (W := W)
    (Y := Y) (Tx := Tx) (C := C) (𝔼.const t c) h14
  refine ⟨hpos.1, hpos.2.1, hpos.2.2, ?_, ?_⟩
  · intro ω
    simp only [Pi.sub_apply]
    have : delta i im t ω * c / P t ω ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (hd ω) (le_max_left _ _))
        (hPpos ω).le
    linarith
  · simp only [Pi.sub_apply]
    have hP0 := hPpos ω₀
    have hcge : (K - C ω₀) * P t ω₀ / (-delta i im t ω₀) ≤ c := le_max_right _ _
    rw [div_le_iff₀ (by linarith)] at hcge
    rw [show C ω₀ - delta i im t ω₀ * c / P t ω₀ = C ω₀ + (-delta i im t ω₀) * c / P t ω₀ by
      ring, ← sub_le_iff_le_add', le_div_iff₀ hP0]
    linarith

/-! ### The government flow budget constraint (1.25) -/

/-- Woodford (2003), eq. (1.25), p. 73, and p. 72: if the supplies of government liabilities
follow `E_t[Q_{t,t+1}W^s_{t+1}] = W^s_t − T_t − Δ_tM^s_t` and markets clear (`C = Y`,
`M = M^s`, `W = W^s`), the household flow constraint (1.7) holds with equality. -/
theorem household_flow_eq_of_gov_flow {q i im Ms Ws P Y Tx : ℕ → Ω → ℝ} {t : ℕ}
    (h125 : 𝔼.E t (q t * Ws (t + 1)) = Ws t - Tx t - delta i im t * Ms t) :
    P t * Y t + delta i im t * Ms t + 𝔼.E t (q t * Ws (t + 1)) = Ws t + (P t * Y t - Tx t) := by
  rw [h125]
  ring

/-! ### Conditional monotone convergence and present values -/

/-- Woodford (2003), p. 627–628 (the interchange of `E_t` and infinite sums used in the proof
of Proposition 2.1): the conditional monotone convergence theorem. For nonnegative random
variables `f k` whose sum converges in every state, `E_t ∑_k f_k = ∑_k E_t f_k`. It is true for
genuine conditional expectations (a.e.) but not implied by the `ExpectationSystem` axioms, so
it is a hypothesis, satisfied by perfect foresight and by every finite event tree. -/
def MonotoneConvergence (𝔼 : ExpectationSystem Ω) : Prop :=
  ∀ t (f : ℕ → Ω → ℝ), (∀ k ω, 0 ≤ f k ω) → (∀ ω, Summable fun k => f k ω) →
    ∀ ω, HasSum (fun k => 𝔼.E t (f k) ω) (𝔼.E t (fun ω' => ∑' k, f k ω') ω)

/-- Woodford (2003), pp. 627–628: perfect foresight satisfies conditional monotone
convergence. -/
theorem perfectForesight_monotoneConvergence : MonotoneConvergence perfectForesight :=
  fun _ _ _ hs ω => (hs ω).hasSum

/-- Woodford (2003), pp. 627–628: the cell-average expectations of every finite event tree
commute with every pointwise convergent series, so conditional monotone convergence holds under
genuine uncertainty. -/
theorem finiteTree_monotoneConvergence {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') : MonotoneConvergence T.toExpectationSystem := by
  classical
  intro t f _ hs ω
  simp only [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E,
    ExpectationsFiniteTree.FiniteTree.condE, ExpectationsFiniteTree.FiniteTree.num]
  refine HasSum.div_const ?_ _
  refine hasSum_sum fun ω' _ => ?_
  split_ifs
  · exact (hs ω').hasSum.mul_left _
  · exact hasSum_zero

/-- Woodford (2003), eqs. (1.9), (1.10), (1.12), pp. 67–69: the date-`t` present value
`∑_{n ≥ 0} E_t[Q_{t,t+n} Y_{t+n}]` of a nominal stream `Y`, as a genuine infinite sum in each
state (summability is always an explicit hypothesis where it is used). -/
noncomputable def pv (𝔼 : ExpectationSystem Ω) (q Y : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' n, 𝔼.E t (sdf q t n * Y (t + n)) ω

/-- Woodford (2003), p. 627 (the step of the proof of Proposition 2.1 that combines the
borrowing limit with the tower property): for a nonnegative stream `Y` whose date-`(t+N)` present
value converges in every state,
`E_t[Q_{t,t+N} ∑_n E_{t+N}[Q_{t+N,t+N+n} Y_{t+N+n}]] = ∑_m E_t[Q_{t,t+N+m} Y_{t+N+m}]`
(with the series on the right summable). -/
theorem hasSum_E_sdf_mul_pv (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut)
    {q Y : ℕ → Ω → ℝ} (hq : ∀ s, 𝔼.E (s + 1) (q s) = q s) (hq0 : ∀ s ω, 0 ≤ q s ω)
    (hY : ∀ s ω, 0 ≤ Y s ω) (t N : ℕ)
    (hs : ∀ ω, Summable fun n => 𝔼.E (t + N) (sdf q (t + N) n * Y (t + N + n)) ω) (ω : Ω) :
    HasSum (fun m => 𝔼.E t (sdf q t (m + N) * Y (t + (m + N))) ω)
      (𝔼.E t (sdf q t N * pv 𝔼 q Y (t + N)) ω) := by
  set f : ℕ → Ω → ℝ :=
    fun n => sdf q t N * 𝔼.E (t + N) (sdf q (t + N) n * Y (t + N + n)) with hf
  have hf0 : ∀ k ω, 0 ≤ f k ω := fun k ω =>
    mul_nonneg (sdf_nonneg hq0 t N ω)
      (E_nonneg 𝔼 (fun ω' => mul_nonneg (sdf_nonneg hq0 _ _ ω') (hY _ ω')) ω)
  have hfs : ∀ ω, Summable fun k => f k ω := fun ω => (hs ω).mul_left (sdf q t N ω)
  have hsum : sdf q t N * pv 𝔼 q Y (t + N) = fun ω' => ∑' k, f k ω' := by
    funext ω'
    simp only [hf, pv, Pi.mul_apply, tsum_mul_left]
  rw [hsum]
  convert hMC t f hf0 hfs ω using 1
  funext m
  simp only [hf]
  rw [E_sdf_mul_E 𝔼 hP hq, ← mul_assoc, ← sdf_add, add_assoc, add_comm N m]

end Woodford.PriceLevelDetermination.AssetPricing
