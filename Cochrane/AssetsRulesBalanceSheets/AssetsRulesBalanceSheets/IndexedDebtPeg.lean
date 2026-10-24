/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.SpreadSwap
import Mathlib.Analysis.Convex.Deriv

/-!
# A price-level target via indexed debt

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.5
"A price-level target via indexed debt", eqs. (9.28)–(9.29), pp. 281–284.

The government pegs the nominal price of a one-period indexed bond (paying `$P_{t+1}`) at `β P*_t`,
so its real price is `q_t = β P*_t / P_t`. Real debt follows (9.28) `b_{t−1} = s_t + q_t b_t`; the
consumer's first-order condition and budget constraint are (9.29),
`(β P*_t/P_t) u'(c_t) = β u'(c_{t+1})` and `y + b_{t−1} = c_t + s_t + q_t b_t` (perfect foresight).
Lean date `n` carries the debt `b n` outstanding at the start of date `n` (book `b_{n−1}`).

## Main results

* `real_rate_low_iff`: the real return on the pegged bond, `P_t/(βP*_t)`, is below `1/β` iff
  `P_t < P*_t` (p. 281).
* `marginal_utility_strictAntiOn`: strict concavity gives a strictly decreasing marginal utility.
* **Theorem IP**: `one_period_deviation` — if `P_{t+j} = P*_{t+j}` for `j ≥ 1`, consumption is
constant
  from `t + 1` on, and `P_t < P*_t` implies `c_t > c_{t+1}` (`P_t > P*_t` implies `c_t < c_{t+1}`);
  `price_eq_target`: market clearing `c = y` forces `P_t = P*_t` at every date.
* `log_demand`, `log_demand_strictAntiOn`: with log utility the one-period-deviation consumption
  demand is finite at every price level, `c_t = (1 − β)(y + b_{t−1} − s_t) + β(P*_t/P_t)(y − (1 −
β)S)`,
  and falls as `P_t` rises when `y > (1 − β)S` ("with concave utility, consumption and bond demands
  do not explode at off-equilibrium prices", p. 282).
* `nominal_debt_crowds_out_real`: with the peg in place, extra nominal debt is matched one-for-one
  (at `1/P*_{t+1}`) by less real debt; `devaluation_lowers_value`.
* `price_eq_peg_times_rate`: `Q* = P*_t/(1 + r_t)`, so real-rate variation induces price-level
  variation (p. 283).
* `five_minute_example`, `five_minute_unbounded`, `annualised_rate`: the numbers of pp. 283–284
  (`250 · 1.25 = 312.5`; `100 (1.25³⁶⁵ − 1) ≈ 2.36 × 10³⁷` %).
-/

namespace Cochrane.AssetsRulesBalanceSheets.IndexedDebtPeg

open Filter Topology

/-- Cochrane (2023), §9.5, p. 281: "with the peg in place buying bonds gives a real return
`1/(1 + r_t) = βP*_t/P_t`. If `P_t < P*_t`, then the real interest rate is too low": the gross real
return `P_t/(βP*_t)` is below `1/β` iff `P_t < P*_t`. -/
theorem real_rate_low_iff {β P Pstar : ℝ} (hβ : 0 < β) (hPs : 0 < Pstar) :
    P / (β * Pstar) < 1 / β ↔ P < Pstar := by
  rw [div_lt_div_iff₀ (mul_pos hβ hPs) hβ]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- Cochrane (2023), §9.5, p. 282 ("with concave utility"): a strictly concave utility with
derivative `u'` on positive consumption has strictly decreasing marginal utility. -/
theorem marginal_utility_strictAntiOn {u up : ℝ → ℝ}
    (hu : StrictConcaveOn ℝ (Set.Ioi 0) u) (hd : ∀ c, 0 < c → HasDerivAt u (up c) c) :
    StrictAntiOn up (Set.Ioi 0) := by
  have h := hu.strictAntiOn_deriv (fun c hc => (hd c hc).differentiableAt)
  intro a ha b hb hab
  have e1 := (hd a ha).deriv
  have e2 := (hd b hb).deriv
  have := h ha hb hab
  rwa [e1, e2] at this

/-- Cochrane (2023), eq. (9.29), p. 281 (**Theorem IP**, one-period deviation, p. 282): under
perfect foresight with strictly decreasing marginal utility, if `P_{t+j} = P*_{t+j}` for all
`j ≥ 1`, then `c_{t+1+j} = c_{t+1}` for all `j`; and `P_t < P*_t` implies `c_t > c_{t+1}`, while
`P*_t < P_t` implies `c_t < c_{t+1}`. -/
theorem one_period_deviation {β : ℝ} (hβ : 0 < β) {up : ℝ → ℝ}
    (hup : StrictAntiOn up (Set.Ioi 0)) {c P Pstar : ℕ → ℝ} (hc : ∀ n, 0 < c n)
    (hP : ∀ n, 0 < P n) (hPs : ∀ n, 0 < Pstar n) (hpos : ∀ n, 0 < up (c n))
    (hfoc : ∀ n, β * Pstar n / P n * up (c n) = β * up (c (n + 1))) (t : ℕ)
    (hlater : ∀ j, P (t + 1 + j) = Pstar (t + 1 + j)) :
    (∀ j, c (t + 1 + j) = c (t + 1)) ∧ (P t < Pstar t → c (t + 1) < c t) ∧
      (Pstar t < P t → c t < c (t + 1)) := by
  have hinj := hup.injOn
  have hstep : ∀ j, c (t + 1 + j + 1) = c (t + 1 + j) := by
    intro j
    have h := hfoc (t + 1 + j)
    rw [hlater j, mul_div_assoc, div_self (hPs _).ne', mul_one] at h
    have h2 := mul_left_cancel₀ hβ.ne' h
    exact (hinj (Set.mem_Ioi.mpr (hc _)) (Set.mem_Ioi.mpr (hc _)) h2).symm
  refine ⟨fun j => ?_, fun hlt => ?_, fun hgt => ?_⟩
  · induction j with
    | zero => simp
    | succ j ih => rw [← add_assoc, hstep j, ih]
  · have h := hfoc t
    have hratio : 1 < Pstar t / P t := (one_lt_div (hP t)).mpr hlt
    have hup_lt : up (c t) < up (c (t + 1)) := by
      have e : β * Pstar t / P t * up (c t) = β * (Pstar t / P t * up (c t)) := by ring
      rw [e] at h
      have h2 := mul_left_cancel₀ hβ.ne' h
      have := hpos t
      nlinarith
    by_contra hge
    push Not at hge
    rcases hge.lt_or_eq with hlt' | heq
    · have := hup (Set.mem_Ioi.mpr (hc t)) (Set.mem_Ioi.mpr (hc (t + 1))) hlt'
      linarith
    · rw [heq] at hup_lt
      exact lt_irrefl _ hup_lt
  · have h := hfoc t
    have hratio : Pstar t / P t < 1 := (div_lt_one (hP t)).mpr hgt
    have hup_lt : up (c (t + 1)) < up (c t) := by
      have e : β * Pstar t / P t * up (c t) = β * (Pstar t / P t * up (c t)) := by ring
      rw [e] at h
      have h2 := mul_left_cancel₀ hβ.ne' h
      have := hpos t
      nlinarith
    by_contra hge
    push Not at hge
    rcases hge.lt_or_eq with hlt' | heq
    · have := hup (Set.mem_Ioi.mpr (hc (t + 1))) (Set.mem_Ioi.mpr (hc t)) hlt'
      linarith
    · rw [heq] at hup_lt
      exact lt_irrefl _ hup_lt

/-- Cochrane (2023), §9.5, p. 281 (**Theorem IP**, "then we must have an equilibrium price level
`P_t = P*_t`"): with the indexed-bond peg and market clearing `c_t = y`, the first-order condition
(9.29) holds at every date if and only if `P_t = P*_t` at every date (`u'(y) > 0`): existence and
uniqueness. -/
theorem price_eq_target {β y : ℝ} (hβ : 0 < β) {up : ℝ → ℝ} (hy : 0 < up y) {P Pstar : ℕ → ℝ}
    (hP : ∀ n, 0 < P n) : (∀ n, β * Pstar n / P n * up y = β * up y) ↔ P = Pstar := by
  constructor
  · intro hfoc
    funext n
    have h := hfoc n
    have h2 : Pstar n / P n = 1 := by
      have e : β * Pstar n / P n * up y = (β * up y) * (Pstar n / P n) := by ring
      rw [e] at h
      exact mul_left_cancel₀ (mul_pos hβ hy).ne' (h.trans (mul_one _).symm)
    rw [div_eq_one_iff_eq (hP n).ne'] at h2
    exact h2.symm
  · rintro rfl n
    rw [mul_div_assoc, div_self (hP n).ne', mul_one]

/-- Cochrane (2023), eq. (9.28), p. 281: with market clearing `c_t = y`, the consumer's budget
constraint in (9.29), `y + b_{t−1} = c_t + s_t + q_t b_t`, is the government's flow condition
`b_{t−1} = s_t + q_t b_t`. -/
theorem eq_9_28_of_clearing {y b s q b' c : ℝ} (hc : c = y) (hbud : y + b = c + s + q * b') :
    b = s + q * b' := by
  rw [hc] at hbud
  linarith

/-- Cochrane (2023), eqs. (9.28)–(9.29), p. 282, with log utility (`u'(c) = 1/c`): in a one-period
deviation (`P_{t+j} = P*_{t+j}`, `j ≥ 1`), given the later budget constraints
`y + b_n = c̄ + s_n + β b_{n+1}`, the transversality condition and summable surpluses
`S = ∑ⱼ βʲ s_{t+1+j}`, consumption demand is
`c_t = (1 − β)(y + b_t − s_t) + β (P*_t/P_t)(y − (1 − β) S)` — finite at every price level. -/
theorem log_demand {β y Pt Pst ct cbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hPt : 0 < Pt)
    (hPst : 0 < Pst) {b s : ℕ → ℝ} (t : ℕ)
    (hfoc : β * Pst / Pt * (1 / ct) = β * (1 / cbar)) (hct : 0 < ct)
    (hbud : y + b t = ct + s t + β * Pst / Pt * b (t + 1))
    (hlater : ∀ n, t + 1 ≤ n → y + b n = cbar + s n + β * b (n + 1))
    (htvc : Tendsto (fun T => β ^ T * b (t + 1 + T)) atTop (𝓝 0))
    (hs : Summable (fun j => β ^ j * s (t + 1 + j))) :
    ct = (1 - β) * (y + b t - s t) +
      β * (Pst / Pt) * (y - (1 - β) * ∑' j, β ^ j * s (t + 1 + j)) := by
  have hβne := hβ0.ne'
  -- the forward value of later debt
  have hflow : ∀ n, b (t + 1 + n) = (cbar + s (t + 1 + n) - y) + β * b (t + 1 + n + 1) := by
    intro n
    have := hlater (t + 1 + n) (by omega)
    linarith
  set d : ℕ → ℝ := fun n => b (t + 1 + n) with hd
  set g : ℕ → ℝ := fun n => cbar + s (t + 1 + n) - y with hg
  have hflow' : ∀ n, d n = g n + β * d (n + 1) := by
    intro n
    simp only [hd, hg]
    rw [show t + 1 + (n + 1) = t + 1 + n + 1 by ring]
    exact hflow n
  have hgeo := summable_geometric_of_lt_one hβ0.le hβ1
  have hsum : Summable (fun j => β ^ j * g (0 + j)) := by
    have := ((hgeo.mul_right (cbar - y)).add hs)
    refine this.congr fun j => ?_
    simp only [hg, zero_add]
    ring
  have hhas := PresentValue.hasSum_of_tvc hflow' 0 (by simpa [hd] using htvc) hsum
  have hval : b (t + 1) = (cbar - y) / (1 - β) + ∑' j, β ^ j * s (t + 1 + j) := by
    have e1 := hhas.tsum_eq
    simp only [hd, hg, add_zero, zero_add] at e1
    rw [← e1]
    have hsplit : (fun j => β ^ j * (cbar + s (t + 1 + j) - y)) =
        fun j => (cbar - y) * β ^ j + β ^ j * s (t + 1 + j) := by
      funext j
      ring
    rw [hsplit, (hgeo.mul_left (cbar - y)).tsum_add hs, tsum_mul_left,
      tsum_geometric_of_lt_one hβ0.le hβ1]
    field_simp
  -- the first-order condition: cbar = ct Pt / Pst
  have hcbar : cbar = ct * Pt / Pst := by
    have hcb : cbar ≠ 0 := by
      intro h0
      rw [h0, div_zero, mul_zero] at hfoc
      have : 0 < β * Pst / Pt * (1 / ct) := by positivity
      linarith
    field_simp at hfoc
    field_simp
    nlinarith [hfoc]
  rw [hval, hcbar] at hbud
  have h1 : (1 - β) ≠ 0 := by linarith
  field_simp at hbud
  field_simp
  linear_combination -hbud

/-- Cochrane (2023), §9.5, p. 282 ("as the price level `P_t` falls, consumption demand `c_t`
rises"):
with log utility the demand of `log_demand` is strictly decreasing in `P_t > 0` when the endowment
exceeds the annuity value of future surpluses, `y > (1 − β) S`. -/
theorem log_demand_strictAntiOn {β y Pst A S : ℝ} (hβ0 : 0 < β) (hPst : 0 < Pst)
    (hS : (1 - β) * S < y) :
    StrictAntiOn (fun Pt => A + β * (Pst / Pt) * (y - (1 - β) * S)) (Set.Ioi 0) := by
  intro P₁ h₁ P₂ h₂ hlt
  simp only [Set.mem_Ioi] at h₁ h₂
  simp only [add_lt_add_iff_left]
  have hk : 0 < y - (1 - β) * S := by linarith
  have : Pst / P₂ < Pst / P₁ := div_lt_div_of_pos_left hPst h₁ hlt
  have hb : 0 < β * (y - (1 - β) * S) := mul_pos hβ0 hk
  nlinarith

/-- Cochrane (2023), §9.5, p. 282: with the peg in place (`P = P*`), the flow condition with both
debts, `b_{t−1} + B_{t−1}/P*_t = s_t + β b_t + Q_t B_t/P*_t` with `Q_t = β P*_t/P*_{t+1}`, shows
that
selling more nominal debt `B_t` "simply ends up selling less real debt `b_t`", one-for-one at
`1/P*_{t+1}`. -/
theorem nominal_debt_crowds_out_real {β bprev Bprev s Pst Pst1 b B b' B' : ℝ} (hβ : 0 < β)
    (hPst : 0 < Pst) (hPst1 : 0 < Pst1)
    (h : bprev + Bprev / Pst = s + β * b + (β * Pst / Pst1) * B / Pst)
    (h' : bprev + Bprev / Pst = s + β * b' + (β * Pst / Pst1) * B' / Pst) :
    b' - b = -(B' - B) / Pst1 := by
  have e : ∀ X : ℝ, (β * Pst / Pst1) * X / Pst = β * (X / Pst1) := fun X => by
    field_simp
  rw [e B] at h
  rw [e B'] at h'
  have h2 : β * ((b' - b) + (B' - B) / Pst1) = 0 := by linear_combination h - h'
  have h3 := (mul_eq_zero.mp h2).resolve_left hβ.ne'
  linear_combination h3

/-- Cochrane (2023), §9.5, p. 282 ("suppose the government unexpectedly devalues at time `t`,
raising the price level target `P*_t`"): the real value `B_{t−1}/P*_t` of outstanding nominal debt
falls strictly as the target rises. -/
theorem devaluation_lowers_value {Bprev : ℝ} (hB : 0 < Bprev) :
    StrictAntiOn (fun Pst : ℝ => Bprev / Pst) (Set.Ioi 0) := by
  simpa using MixedDebtRules.value_strictAntiOn (b := 0) hB

/-- Cochrane (2023), §9.5, p. 283: with a fixed nominal bond-price target `Q*`, the real bond price
`1/(1 + r_t) = Q*/P_t` gives `P_t = Q*(1 + r_t)`: real-interest-rate variation is price-level
variation (`P_t/P_s = (1 + r_t)/(1 + r_s)`). -/
theorem price_eq_peg_times_rate {Qs P r : ℕ → ℝ} {Q : ℝ} (hQ : 0 < Q)
    (hP : ∀ n, 0 < P n) (hr : ∀ n, 0 < 1 + r n) (h : ∀ n, 1 / (1 + r n) = Q / P n)
    (hQs : ∀ n, Qs n = Q) (t s : ℕ) :
    P t = Qs t * (1 + r t) ∧ P t / P s = (1 + r t) / (1 + r s) ∧ (r t ≠ r s → P t ≠ P s) := by
  have hPt : ∀ n, P n = Q * (1 + r n) := by
    intro n
    have := h n
    rw [div_eq_div_iff (hr n).ne' (hP n).ne'] at this
    linarith
  refine ⟨by rw [hQs t, hPt t], ?_, fun hne heq => hne ?_⟩
  · rw [hPt t, hPt s]
    field_simp
  · rw [hPt t, hPt s] at heq
    have := mul_left_cancel₀ hQ.ne' heq
    linarith

/-- Cochrane (2023), §9.5, pp. 283–284 (the five-minute example): for `$200` one buys a claim to
`$250`; reinvesting, `250 · 1.25 = 312.5`; the overnight return is `100 (250/200 − 1) = 25` %. -/
theorem five_minute_example :
    (200 : ℝ) * (5 / 4) = 250 ∧ (250 : ℝ) * (5 / 4) = 312.5 ∧ 100 * ((250 : ℝ) / 200 - 1) = 25 := by
  norm_num

/-- Cochrane (2023), §9.5, p. 284 ("money is exploding"): repeatedly rolling over the pegged claim
multiplies dollars by `5/4` each round, so holdings `200 · (5/4)ⁿ` grow without bound. -/
theorem five_minute_unbounded :
    Tendsto (fun n : ℕ => (200 : ℝ) * (5 / 4) ^ n) atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)).const_mul_atTop (by norm_num)

set_option exponentiation.threshold 400 in
/-- Cochrane (2023), §9.5, p. 284: a 25% one-day return annualises to
`100 ((250/200)³⁶⁵ − 1) ≈ 2.36 × 10³⁷` %, between `2.3 × 10³⁷` and `2.4 × 10³⁷` (the book's
"`2.3 × 10³⁷` %"; the gross factor itself is `≈ 2.36 × 10³⁵`). -/
theorem annualised_rate :
    (2.3e37 : ℝ) < 100 * (((250 : ℝ) / 200) ^ 365 - 1) ∧
      100 * (((250 : ℝ) / 200) ^ 365 - 1) < 2.4e37 := by
  norm_num

end Cochrane.AssetsRulesBalanceSheets.IndexedDebtPeg
