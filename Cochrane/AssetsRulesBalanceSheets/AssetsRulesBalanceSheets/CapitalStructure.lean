/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.RealDebt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The corporate finance of government debt

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 8, §8.3 (pp. 245–249),
eq. (8.3).

With real debt `b_{t−1}` and nominal debt `B_{t−1}` outstanding, the valuation equation is
`b_{t−1} + B_{t−1}/P_t = E_t ∑ βʲ s_{t+j} =: V_t` (8.3). Real debt is like corporate debt and
nominal debt like equity: the price level is determined by the nominal part only, and more real
debt (leverage) makes the price level more sensitive to fiscal news.

## Main results

* `mixedFlow_iff_solves`, `mixed_valuation_iff`: the flow with both kinds of debt plus the
  transversality condition is equivalent to (8.3).
* `mixed_price_unique` (`P = B/(V − b)` when `V > b`, `B > 0`), `mixed_no_price` (no price level
  when `V ≤ b`: default is needed), `mixed_zero_nominal` (with no nominal debt the price level is
  free when `V = b` and no price level exists otherwise).
* Leverage: `log_price_hasDerivAt`, `log_price_elasticity` (the exact elasticity
  `d log P/d log V = −V/(V − b)`), `elasticity_gt_one_iff`, `elasticity_strictMono`,
  `price_ratio`, `log_price_spread_strictMono` (for any two values of `V`, the log price-level
  difference strictly increases with real debt `b`), `default_prob_mono` (a larger real debt
  raises the conditional probability of explicit default).
* Cashless limit (p. 248): `cashless_sequence_determinate`, `cashless_nominal_vanishes`,
  `cashless_elasticity_explodes`, `cashless_limit_indeterminate`, and the pennies example
  `pennies_inflation` (exactly `10/9`, i.e. 11.1%, where the book says 10%).
-/

namespace Cochrane.AssetsRulesBalanceSheets.CapitalStructure

open Filter Topology RealDebt PresentValue

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The valuation equation (8.3) -/

/-- Cochrane (2023), eq. (8.3), p. 246 (flow form): with real debt `b` and nominal debt `B`,
`P_t b_{t−1} + B_{t−1} = P_t s_t + (β P_t) b_t + Q_t B_t`, the indexed bond selling at
`E_t[β (P_t/P_{t+1}) P_{t+1}]` and the nominal bond at `Q_t = β E_t(P_t/P_{t+1})`. -/
def MixedFlow (β : ℝ) (b B P s : ℕ → Ω → ℝ) : Prop :=
  ∀ t, P t * b t + B t = P t * s t + indexedPrice 𝔼 β P t * b (t + 1) +
    𝔼.E t (β • (P t / P (t + 1))) * B (t + 1)

/-- Cochrane (2023), eq. (8.3), p. 246: with the pull-out property, an adapted nowhere-zero price
level, and both debts chosen at `t`, the mixed flow is the real recursion for the total real
value `x_t = b_{t−1} + B_{t−1}/P_t`, `x_t = s_t + β E_t x_{t+1}`. -/
theorem mixedFlow_iff_solves (hPO : 𝔼.PullOut) {β : ℝ} {b B P s : ℕ → Ω → ℝ}
    (hPa : 𝔼.Adapted P) (hP : ∀ t ω, P t ω ≠ 0) (hbpre : ∀ t, 𝔼.E t (b (t + 1)) = b (t + 1))
    (hBpre : ∀ t, 𝔼.E t (B (t + 1)) = B (t + 1)) :
    MixedFlow 𝔼 β b B P s ↔ ForwardSolution.Solves 𝔼 β s (fun t => b t + B t / P t) := by
  have hE1 : ∀ t, 𝔼.E t (β • (P t / P (t + 1))) = β • (P t * 𝔼.E t (P (t + 1))⁻¹) := by
    intro t
    rw [map_smul, div_eq_mul_inv, hPO t (P t) (P (t + 1))⁻¹ (hPa t)]
  have hE2 : ∀ t, 𝔼.E t (b (t + 1) + B (t + 1) / P (t + 1)) =
      b (t + 1) + B (t + 1) * 𝔼.E t (P (t + 1))⁻¹ := by
    intro t
    rw [map_add, hbpre t, div_eq_mul_inv, hPO t (B (t + 1)) (P (t + 1))⁻¹ (hBpre t)]
  simp only [MixedFlow, ForwardSolution.Solves, indexedPrice_eq 𝔼 hPa hP, hE1, hE2, funext_iff,
    Pi.add_apply, Pi.mul_apply, Pi.smul_apply, Pi.div_apply, smul_eq_mul]
  constructor
  · intro h t ω
    have hPt := hP t ω
    have h1 := h t ω
    field_simp
    linear_combination h1
  · intro h t ω
    have hPt := hP t ω
    have h1 := h t ω
    field_simp at h1
    linear_combination h1

/-- Cochrane (2023), eq. (8.3), p. 246: for bounded adapted surpluses and `0 ≤ β < 1`, the mixed
flow plus the transversality condition on the total real value is equivalent to
`b_{t−1} + B_{t−1}/P_t = E_t ∑ βʲ s_{t+j}` at every date. -/
theorem mixed_valuation_iff (hPO : 𝔼.PullOut) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {b B P s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s) (hPa : 𝔼.Adapted P)
    (hP : ∀ t ω, P t ω ≠ 0) (hbpre : ∀ t, 𝔼.E t (b (t + 1)) = b (t + 1))
    (hBpre : ∀ t, 𝔼.E t (B (t + 1)) = B (t + 1)) :
    (MixedFlow 𝔼 β b B P s ∧ TVC 𝔼 β (fun t => b t + B t / P t)) ↔
      ∀ t, b t + B t / P t = pv 𝔼 β s t := by
  rw [mixedFlow_iff_solves 𝔼 hPO hPa hP hbpre hBpre, flow_tvc_iff_pv 𝔼 hβ0 hβ1 hs hsa,
    funext_iff]

/-! ### Existence and uniqueness of the price level -/

/-- Cochrane (2023), eq. (8.3), p. 246: "the price level is determined by the ability to devalue
the nominal debt only": with `B > 0` and `V > b` there is exactly one positive price level,
`P = B/(V − b)`. -/
theorem mixed_price_unique {b B V : ℝ} (hB : 0 < B) (hVb : b < V) :
    ∃! P : ℝ, 0 < P ∧ b + B / P = V := by
  have hpos : 0 < V - b := sub_pos.mpr hVb
  refine ⟨B / (V - b), ⟨div_pos hB hpos, ?_⟩, ?_⟩
  · field_simp
    ring
  · rintro P ⟨hP, h⟩
    rw [eq_div_iff hpos.ne', ← h]
    field_simp
    ring

/-- Cochrane (2023), §8.3, p. 246: if the present value of surpluses does not exceed the real
debt, `V ≤ b`, no positive price level satisfies (8.3): the real debt must be defaulted on. -/
theorem mixed_no_price {b B V : ℝ} (hB : 0 < B) (hVb : V ≤ b) :
    ¬ ∃ P : ℝ, 0 < P ∧ b + B / P = V := by
  rintro ⟨P, hP, h⟩
  have : 0 < B / P := div_pos hB hP
  linarith

/-- Cochrane (2023), §8.1 and §8.3, pp. 239, 246: with no nominal debt, (8.3) does not involve the
price level: every price level solves it if `V = b` and none does otherwise. -/
theorem mixed_zero_nominal (b V P : ℝ) : b + 0 / P = V ↔ V = b := by
  rw [zero_div, add_zero, eq_comm]

/-! ### Leverage and price-level volatility -/

/-- Cochrane (2023), §8.3, p. 246: the exact derivative of the log price level
`log P = log(B/(V − b))` with respect to the present value of surpluses is `−1/(V − b)`. -/
theorem log_price_hasDerivAt {b B V : ℝ} (hB : 0 < B) (hVb : b < V) :
    HasDerivAt (fun x => Real.log (B / (x - b))) (-(1 / (V - b))) V := by
  have hne : V - b ≠ 0 := (sub_pos.mpr hVb).ne'
  have h1 : HasDerivAt (fun x => x - b) 1 V := HasDerivAt.sub_const b (hasDerivAt_id V)
  have h2 : HasDerivAt (fun x => (x - b)⁻¹) (-1 / (V - b) ^ 2) V := HasDerivAt.inv h1 hne
  have h3 : HasDerivAt (fun x => B * (x - b)⁻¹) (B * (-1 / (V - b) ^ 2)) V :=
    HasDerivAt.const_mul B h2
  have h4 := HasDerivAt.log h3 (mul_ne_zero hB.ne' (inv_ne_zero hne))
  have hf : (fun x => Real.log (B / (x - b))) = fun x => Real.log (B * (x - b)⁻¹) := by
    funext x
    rw [div_eq_mul_inv]
  rw [hf]
  refine HasDerivAt.congr_deriv h4 ?_
  field_simp

/-- Cochrane (2023), §8.3, p. 246 (leverage): the exact elasticity of the price level with
respect to the present value of surpluses, `d log P/d log V = −V/(V − b)` at `V > max(b, 0)`. -/
theorem log_price_elasticity {b B V : ℝ} (hB : 0 < B) (hV : 0 < V) (hVb : b < V) :
    HasDerivAt (fun u => Real.log (B / (Real.exp u - b))) (-(V / (V - b))) (Real.log V) := by
  have h : HasDerivAt (fun x => Real.log (B / (x - b))) (-(1 / (V - b)))
      (Real.exp (Real.log V)) := by
    rw [Real.exp_log hV]
    exact log_price_hasDerivAt hB hVb
  have h2 := HasDerivAt.comp (Real.log V) h (Real.hasDerivAt_exp (Real.log V))
  refine HasDerivAt.congr_deriv h2 ?_
  rw [Real.exp_log hV]
  ring

/-- Cochrane (2023), §8.3, p. 246: the price level is more sensitive than one-for-one to fiscal
news, `V/(V − b) > 1`, exactly when there is real debt, `b > 0`. -/
theorem elasticity_gt_one_iff {b V : ℝ} (hVb : b < V) :
    1 < V / (V - b) ↔ 0 < b := by
  have hpos : 0 < V - b := sub_pos.mpr hVb
  rw [one_lt_div hpos]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §8.3, p. 246: "a government that issues more real debt and less nominal
debt ... increases the volatility of inflation": the elasticity `V/(V − b)` is strictly
increasing in real debt `b < V`. -/
theorem elasticity_strictMono {b b' V : ℝ} (hV : 0 < V) (hbb : b < b') (hb'V : b' < V) :
    V / (V - b) < V / (V - b') :=
  div_lt_div_of_pos_left hV (sub_pos.mpr hb'V) (by linarith)

/-- Cochrane (2023), eq. (8.3), p. 246: the exact price-level response to a change of the present
value from `V` to `V'` (both above `b`) is `P(V')/P(V) = (V − b)/(V' − b)`. -/
theorem price_ratio {b B V V' : ℝ} (hB : 0 < B) (hVb : b < V) (hV'b : b < V') :
    (B / (V' - b)) / (B / (V - b)) = (V - b) / (V' - b) := by
  have h1 : V - b ≠ 0 := (sub_pos.mpr hVb).ne'
  have h2 : V' - b ≠ 0 := (sub_pos.mpr hV'b).ne'
  field_simp

/-- Cochrane (2023), §8.3, p. 246 (leverage raises inflation volatility, exactly): for any two
present values `V₁ < V₂`, the log price-level difference
`log P(V₁) − log P(V₂) = log((V₂ − b)/(V₁ − b)) > 0` is strictly increasing in real debt
`b < V₁`. -/
theorem log_price_spread_strictMono {b b' B V₁ V₂ : ℝ} (hB : 0 < B) (hV : V₁ < V₂)
    (hbb : b < b') (hb'V : b' < V₁) :
    0 < Real.log (B / (V₁ - b)) - Real.log (B / (V₂ - b)) ∧
    Real.log (B / (V₁ - b)) - Real.log (B / (V₂ - b)) <
      Real.log (B / (V₁ - b')) - Real.log (B / (V₂ - b')) := by
  have p1 : 0 < V₁ - b := by linarith
  have p2 : 0 < V₂ - b := by linarith
  have p1' : 0 < V₁ - b' := by linarith
  have p2' : 0 < V₂ - b' := by linarith
  have key : ∀ c : ℝ, 0 < V₁ - c → 0 < V₂ - c →
      Real.log (B / (V₁ - c)) - Real.log (B / (V₂ - c)) = Real.log ((V₂ - c) / (V₁ - c)) := by
    intro c hc1 hc2
    rw [← Real.log_div (div_pos hB hc1).ne' (div_pos hB hc2).ne']
    congr 1
    field_simp
  rw [key b p1 p2, key b' p1' p2']
  constructor
  · apply Real.log_pos
    rw [one_lt_div p1]
    linarith
  · apply Real.log_lt_log (div_pos p2 p1)
    rw [div_lt_div_iff₀ p1 p1']
    nlinarith

/-- Cochrane (2023), §8.3, p. 246 ("raises the chance of explicit default"): with real debt `b`,
explicit default occurs in the states where `V < b`; its conditional probability
`E_t 1{V < b}` is weakly increasing in `b`. -/
theorem default_prob_mono (t : ℕ) (V : Ω → ℝ) {b b' : ℝ} (hbb : b ≤ b') :
    𝔼.E t (fun ω => if V ω < b then (1 : ℝ) else 0) ≤
      𝔼.E t (fun ω => if V ω < b' then (1 : ℝ) else 0) := by
  refine 𝔼.mono t fun ω => ?_
  by_cases h : V ω < b
  · have h' : V ω < b' := lt_of_lt_of_le h hbb
    simp [h, h']
  · by_cases h' : V ω < b'
    · simp [h, h']
    · simp [h, h']

/-! ### The cashless limit (p. 248) -/

/-- Cochrane (2023), §8.3, p. 248: along a sequence with real debt `b_n < V` and nominal debt
`B_n = P (V − b_n)`, the price level `P` is the unique positive solution of (8.3) at every `n`
("determinate all the way along"). -/
theorem cashless_sequence_determinate {P V : ℝ} (hP : 0 < P) {b : ℕ → ℝ}
    (hb : ∀ n, b n < V) (n : ℕ) :
    ∃! p : ℝ, 0 < p ∧ b n + P * (V - b n) / p = V := by
  have hpos : 0 < V - b n := sub_pos.mpr (hb n)
  obtain ⟨p, ⟨hp, hpv⟩, huniq⟩ := mixed_price_unique (mul_pos hP hpos) (hb n)
  refine ⟨p, ⟨hp, hpv⟩, huniq⟩

/-- Cochrane (2023), §8.3, p. 248: the solution in `cashless_sequence_determinate` is the same
price level `P` at every `n` ("so that inflation remains the same"). -/
theorem cashless_sequence_price {P V : ℝ} (hP : 0 < P) (b : ℕ → ℝ) (n : ℕ) :
    b n + P * (V - b n) / P = V := by
  have : P * (V - b n) / P = V - b n := by field_simp
  rw [this]
  ring

/-- Cochrane (2023), §8.3, p. 248: as real debt approaches the present value, `b_n → V`, the
nominal debt `B_n = P(V − b_n)` vanishes. -/
theorem cashless_nominal_vanishes {P V : ℝ} {b : ℕ → ℝ} (hlim : Tendsto b atTop (𝓝 V)) :
    Tendsto (fun n => P * (V - b n)) atTop (𝓝 0) := by
  have h : Tendsto (fun n => V - b n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := V)).sub hlim
  simpa using h.const_mul P

/-- Cochrane (2023), §8.3, p. 248: along the cashless sequence the elasticity of the price level
to fiscal news, `V/(V − b_n)`, diverges to `+∞`. -/
theorem cashless_elasticity_explodes {V : ℝ} (hV : 0 < V) {b : ℕ → ℝ} (hb : ∀ n, b n < V)
    (hlim : Tendsto b atTop (𝓝 V)) : Tendsto (fun n => V / (V - b n)) atTop atTop := by
  have h : Tendsto (fun n => V - b n) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · simpa using (tendsto_const_nhds (x := V)).sub hlim
    · exact sub_pos.mpr (hb n)
  have h2 : Tendsto (fun n => (V - b n)⁻¹) atTop atTop := tendsto_inv_nhdsGT_zero.comp h
  simpa [div_eq_mul_inv] using Tendsto.const_mul_atTop hV h2

/-- Cochrane (2023), §8.3, p. 248: at the limit point (`B = 0`, `b = V`) every positive price
level solves (8.3) — determinate along the sequence, not at the limit. -/
theorem cashless_limit_indeterminate (V p : ℝ) : V + 0 / p = V := by
  rw [zero_div, add_zero]

/-- Cochrane (2023), §8.3, p. 248 ($10 of pennies, survey E8.4): if the nominal debt is worth
`B/P = 10` and the surplus present value falls by `1` with real debt unchanged, the price level
rises by the exact factor `10/9` (11.1%; the book's "10%" is the first-order approximation). -/
theorem pennies_inflation {b B P P' V : ℝ} (hB : 0 < B) (hP : 0 < P) (hP' : 0 < P')
    (h0 : b + B / P = V) (h1 : b + B / P' = V - 1) (h10 : B / P = 10) : P' / P = 10 / 9 := by
  have h9 : B / P' = 9 := by linarith
  have e1 : P = B / 10 := by
    rw [eq_div_iff (by norm_num : (10 : ℝ) ≠ 0), ← h10]
    field_simp
  have e2 : P' = B / 9 := by
    rw [eq_div_iff (by norm_num : (9 : ℝ) ≠ 0), ← h9]
    field_simp
  rw [e1, e2]
  field_simp

end Cochrane.AssetsRulesBalanceSheets.CapitalStructure
