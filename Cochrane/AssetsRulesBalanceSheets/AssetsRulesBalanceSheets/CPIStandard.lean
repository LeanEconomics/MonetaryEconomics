/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.IndexedDebtPeg

/-!
# A CPI standard?

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.6
"A CPI standard?", pp. 284–286. The section is mostly verbal; this module formalises its precise
claims.

## Main results

* `commodity_standard_price`: pegging the dollar price `G` of a commodity whose relative price is
  `g_t` gives `P_t = G/g_t`, so variation in the relative price is price-level variation
  (p. 285, "the relative price of gold and everything else varies over time, so the gold
  standard leaves substantial inflation volatility").
* `hasSum_perpetuity`, `perpetuity_rises_more`: a real perpetuity costs `1/r`, a one-year indexed
  bond `1/(1 + r)`; when the real rate falls, the perpetuity's price rises by more (p. 285, "when
the
  real interest-rate declines, long-term real asset prices rise relative to the consumption basket,
  much more so than the price of a one-year indexed bond").
* `indexed_claim_price`, `indexed_peg_pins_price`: the dollar price of a claim to next period's
  basket is `β P_t`, so pegging it ties down today's price level (p. 286).
* `cpi_bet_unbounded`, `cpi_bet_example`: offering `$250` for a CPI-linked bet that pays the CPI
  of `260` today is an arbitrage whose reinvested proceeds grow without bound (p. 286).
-/

namespace Cochrane.AssetsRulesBalanceSheets.CPIStandard

open Filter Topology

/-- Cochrane (2023), §9.6, p. 285: under a commodity (gold) standard the dollar price of the
commodity is pegged at `G` and its relative price is `g_t` goods per unit, so `P_t = G/g_t`;
inflation
is `P_{t+1}/P_t = g_t/g_{t+1}` and any change in the relative price changes the price level. -/
theorem commodity_standard_price {G : ℝ} (hG : 0 < G) {g P : ℕ → ℝ} (hg : ∀ t, 0 < g t)
    (hpeg : ∀ t, P t * g t = G) (t s : ℕ) :
    P t = G / g t ∧ P (t + 1) / P t = g t / g (t + 1) ∧ (g t ≠ g s → P t ≠ P s) := by
  have hP : ∀ n, P n = G / g n := fun n => by
    rw [eq_div_iff (hg n).ne']
    exact hpeg n
  refine ⟨hP t, ?_, fun hne heq => hne ?_⟩
  · rw [hP t, hP (t + 1)]
    field_simp [(hg t).ne', (hg (t + 1)).ne', hG.ne']
  · rw [hP t, hP s] at heq
    rw [div_eq_div_iff (hg t).ne' (hg s).ne'] at heq
    exact (mul_left_cancel₀ hG.ne' heq).symm

/-- Cochrane (2023), §9.6, p. 285: a real perpetuity paying one unit of consumption at every future
date costs `∑_{j≥1} (1 + r)^{−j} = 1/r`. -/
theorem hasSum_perpetuity {r : ℝ} (hr : 0 < r) :
    HasSum (fun j : ℕ => (1 / (1 + r)) ^ (j + 1)) (1 / r) := by
  have hq0 : 0 ≤ 1 / (1 + r) := by positivity
  have hq1 : 1 / (1 + r) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (1 / (1 + r))
  convert h using 1
  · funext j
    rw [pow_succ]
    ring
  · have hr0 := hr.ne'
    have h1r : 1 + r ≠ 0 := by linarith
    field_simp
    ring_nf
    field_simp

/-- Cochrane (2023), §9.6, p. 285: when the real rate falls from `r₂` to `r₁` (`0 < r₁ < r₂`), the
price of a real perpetuity rises by more than the price of a one-year indexed bond,
`1/r₁ − 1/r₂ > 1/(1 + r₁) − 1/(1 + r₂)`. -/
theorem perpetuity_rises_more {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (hlt : r₁ < r₂) :
    1 / (1 + r₁) - 1 / (1 + r₂) < 1 / r₁ - 1 / r₂ := by
  have h₂ : 0 < r₂ := h₁.trans hlt
  rw [div_sub_div _ _ (by linarith) (by linarith), div_sub_div _ _ h₁.ne' h₂.ne',
    div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos h₁ h₂, mul_pos (mul_pos h₁ h₂) (sub_pos.mpr hlt)]

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §9.6, p. 286 ("the indexed debt peg ties down today's price of next-year's
basket"): with a constant real rate and the pull-out property, a claim paying `$P_{t+1}` (next
period's basket) has dollar price `P_t · β E_t (P_{t+1}/P_{t+1}) = β P_t`. -/
theorem indexed_claim_price {β : ℝ} {P : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω) (t : ℕ) :
    P t * β • 𝔼.E t (P (t + 1) / P (t + 1)) = β • P t := by
  have h1 : P (t + 1) / P (t + 1) = fun _ => 1 := by
    funext ω
    exact div_self (hP (t + 1) ω).ne'
  rw [h1, 𝔼.const]
  funext ω
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), §9.5–§9.6, pp. 281, 286: pegging the dollar price of that claim at `β P*_t`
ties down today's price level, `P_t = P*_t`. -/
theorem indexed_peg_pins_price {β : ℝ} (hβ : 0 < β) {P : ℕ → Ω → ℝ} {Pstar : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (t : ℕ) (hpeg : P t * β • 𝔼.E t (P (t + 1) / P (t + 1)) =
      β • Pstar t) : P t = Pstar t := by
  rw [indexed_claim_price 𝔼 hP t] at hpeg
  funext ω
  have := congrFun hpeg ω
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hβ.ne' this

/-- Cochrane (2023), §9.6, p. 286 ("if the government offers to trade `$250` for a CPI-linked bet
that
pays off today, and the CPI is `260`, people will trade infinite amounts"): whenever the offer price
`p` is below the index value `v`, reinvesting `W` dollars `n` times yields `W (v/p)ⁿ → ∞`. -/
theorem cpi_bet_unbounded {p v W : ℝ} (hp : 0 < p) (hpv : p < v) (hW : 0 < W) :
    Tendsto (fun n : ℕ => W * (v / p) ^ n) atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt ((one_lt_div hp).mpr hpv)).const_mul_atTop hW

/-- Cochrane (2023), §9.6, p. 286: the book's numbers — each round turns `$250` into `$260`, and the
reinvested holdings `250 (260/250)ⁿ` grow without bound. -/
theorem cpi_bet_example :
    (250 : ℝ) * (260 / 250) = 260 ∧
      Tendsto (fun n : ℕ => (250 : ℝ) * (260 / 250) ^ n) atTop atTop :=
  ⟨by norm_num, cpi_bet_unbounded (by norm_num) (by norm_num) (by norm_num)⟩

end Cochrane.AssetsRulesBalanceSheets.CPIStandard
