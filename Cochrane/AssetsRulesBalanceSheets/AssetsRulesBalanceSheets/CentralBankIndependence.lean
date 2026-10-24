/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.Default

/-!
# Central bank independence

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 8, §8.6 (pp. 256–258).
§8.6 is largely institutional; this module formalises its precise claims.

## Main results

* `cb_purchase_neutral` (p. 256): a central-bank purchase of treasury debt paid for with
  reserves is the same as the treasury issuing reserves directly; the consolidated valuation
  equation, and hence the price level, is unchanged.
* `cash_left_pos_iff`, `cash_left_zero_iff` (p. 257, "inflation in the end comes from too much
  cash"): the government prints `B_{t−1}` to redeem maturing debt and soaks money up with
  surpluses and new debt; cash is left over exactly when the price level is below its
  equilibrium value.
* `unified_inflates`, `independence_default_vs_inflation` (p. 257; the default half is
  `RealDebt.haircut_of_fixed_price`): when an independent central bank pins the price level, a
  shortfall of treasury surpluses must be met by explicit default; when the treasury can print,
  the same shortfall is met by inflation.
-/

namespace Cochrane.AssetsRulesBalanceSheets.CentralBankIndependence

open RealDebt

/-- Cochrane (2023), §8.6, p. 256: "If the treasury issues debt, the central bank buys that debt
and issues reserves or cash, it is the same as the treasury issuing reserves or cash rather than
treasury debt directly": moving `x` from publicly held treasury debt to reserves leaves the
consolidated valuation equation `(B + M)/P = V` unchanged. -/
theorem cb_purchase_neutral (B M x P V : ℝ) :
    ((B - x) + (M + x)) / P = V ↔ (B + M) / P = V := by
  rw [show (B - x) + (M + x) = B + M by ring]

/-- Cochrane (2023), §8.6, p. 257: the cash left in private hands at the end of date `t`, when
the government prints `B_{t−1}` to redeem maturing debt and soaks up `P_t s_t` with surpluses and
`P_t q_t` with new debt sales (`q_t = Q_t B_t/P_t` the real revenue). -/
def cashLeft (B P s q : ℝ) : ℝ := B - P * (s + q)

/-- Cochrane (2023), §8.6, p. 257: with positive real backing `s + q > 0`, cash is left over —
"too much cash" — exactly when the price level is below the value set by the flow condition,
`P < B/(s + q)`. -/
theorem cash_left_pos_iff {B P s q : ℝ} (hsq : 0 < s + q) :
    0 < cashLeft B P s q ↔ P < B / (s + q) := by
  rw [cashLeft, lt_div_iff₀ hsq]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §8.6, p. 257: no cash is left over iff the flow condition
`B_{t−1}/P_t = s_t + q_t` holds (for a nonzero price level). -/
theorem cash_left_zero_iff {B P s q : ℝ} (hP : P ≠ 0) :
    cashLeft B P s q = 0 ↔ B / P = s + q := by
  rw [cashLeft, div_eq_iff hP, sub_eq_zero, mul_comm]

/-- Cochrane (2023), §8.6, p. 257 (contrast): if the treasury can print money to redeem its debt
(no default, `D = 1`), the valuation `B/P = V` with `B, V > 0` sets `P = B/V`, which exceeds a
target `P̄ > 0` iff `V < B/P̄`. -/
theorem unified_inflates {B Pbar V P : ℝ} (hB : 0 < B) (hP : 0 < Pbar) (hV : 0 < V)
    (hval : B / P = V) : P = B / V ∧ (Pbar < P ↔ V < B / Pbar) := by
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, div_zero] at hval
    exact hV.ne hval
  have hPe : P = B / V := by
    rw [eq_div_iff hV.ne', ← hval]
    field_simp
  refine ⟨hPe, ?_⟩
  rw [hPe, lt_div_iff₀ hV, lt_div_iff₀ hP, mul_comm]

/-- Cochrane (2023), §8.6, p. 257: the same fiscal shortfall `V < B/P̄` produces explicit default
(`D < 1` at `P = P̄`) under an independent central bank and inflation (`P > P̄` with `D = 1`) under
a unified treasury and central bank. -/
theorem independence_default_vs_inflation {B Pbar V D P : ℝ} (hB : 0 < B) (hP : 0 < Pbar)
    (hV : 0 < V) (hshort : V < B / Pbar) (hind : B * D / Pbar = V) (huni : B / P = V) :
    D < 1 ∧ Pbar < P :=
  ⟨((haircut_of_fixed_price hB hP hind).2.2).mpr hshort,
    ((unified_inflates hB hP hV huni).2).mpr hshort⟩

end Cochrane.AssetsRulesBalanceSheets.CentralBankIndependence
