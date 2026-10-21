/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.PotOfAssets
import AssetsRulesBalanceSheets.CentralBankIndependence
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Central-bank and treasury balance sheets

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 10, §10.2–10.7 (pp. 297–311).
These sections are largely institutional; this module formalises their precise claims in the
two-balance-sheet valuation model: the central bank has nominal liabilities `M` (reserves and
cash), real assets with value `A` and treasury debt `B_c` (nominal); the treasury owes `B_p` to
the public and `B_c` to the central bank and has surplus present value `V_T`.

## Main results

* §10.3 (pp. 298–300): `consolidated_of_separate` ("that view only adds debt and the surpluses
  that repay it to left and right-hand sides"), `treasury_iff_consolidated`,
  `contingent_transfers_unite` (with residual profit rebates and recapitalisations, only the
  consolidated equation restricts the price level).
* p. 301 (Bassetto–Sargent): `nominal_cb_cannot_determine` (a central bank holding only nominal
  government debt cannot determine the price level), `real_cb_determines` (one holding real
  assets can).
* §10.2 (p. 298): `walled_off_insulated` (a walled-off central bank pins `P`; a treasury default
  on publicly held debt does not move it), `topping_up_lowers_price` (topping up central-bank
  assets lowers the price level, confiscating them raises it).
* §10.4 (p. 301): `asset_volatility_passes_through` (the log price level moves one-for-one with
  the log value of the real assets, so stable assets give a stable price level).
* §10.7 (p. 310): converting government debt into fixed-value floating-rate money leaves the
  price level unchanged — the same statement as `CentralBankIndependence.cb_purchase_neutral`.
-/

namespace Cochrane.AssetsRulesBalanceSheets.BalanceSheets

/-- Cochrane (2023), §10.3, p. 299: if the central bank's valuation `M/P = A + B_c/P` and the
treasury's valuation `(B_p + B_c)/P = V_T` hold, so does the consolidated valuation
`(B_p + M)/P = V_T + A`: the consolidated view adds central-bank debt and the assets that back it
to both sides. -/
theorem consolidated_of_separate {M A Bc Bp VT P : ℝ} (hcb : M / P = A + Bc / P)
    (htr : (Bp + Bc) / P = VT) : (Bp + M) / P = VT + A := by
  rw [add_div] at htr ⊢
  linarith

/-- Cochrane (2023), §10.3, p. 300: "In any case, the price level still adjusts so that the
value of overall government liabilities is equal to the present value of overall surpluses":
given the central bank's valuation, the treasury's valuation holds iff the consolidated one
does. -/
theorem treasury_iff_consolidated {M A Bc Bp VT P : ℝ} (hcb : M / P = A + Bc / P) :
    (Bp + Bc) / P = VT ↔ (Bp + M) / P = VT + A := by
  rw [add_div, add_div]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §10.3, pp. 299–300: contingent transfers (profit rebates and
recapitalisations, real present value `τ` from the central bank to the treasury) unite the
balance sheets: there is a transfer making both separate valuations hold iff the consolidated
valuation holds. -/
theorem contingent_transfers_unite {M A Bc Bp VT P : ℝ} :
    (∃ τ : ℝ, M / P = A + Bc / P - τ ∧ (Bp + Bc) / P = VT + τ) ↔ (Bp + M) / P = VT + A := by
  constructor
  · rintro ⟨τ, h1, h2⟩
    rw [add_div] at h2 ⊢
    linarith
  · intro h
    refine ⟨A + Bc / P - M / P, by ring, ?_⟩
    rw [add_div] at h ⊢
    linarith

/-- Cochrane (2023), §10.3, p. 301 (Bassetto and Sargent): a central bank holding only nominal
government debt (`A = 0`) cannot determine the price level: `M/P = B_c/P` holds at one nonzero
price level iff it holds at all of them (iff `M = B_c`). -/
theorem nominal_cb_cannot_determine {M Bc P : ℝ} (hP : P ≠ 0) :
    M / P = 0 + Bc / P ↔ M = Bc := by
  rw [zero_add]
  constructor
  · intro h
    field_simp at h
    exact h
  · intro h
    rw [h]

/-- Cochrane (2023), §10.3, p. 301 (Bassetto and Sargent): a central bank holding real assets
`A > 0` (with `M > B_c`) determines the price level, `P = (M − B_c)/A`. -/
theorem real_cb_determines {M A Bc : ℝ} (hA : 0 < A) (hM : Bc < M) :
    ∃! P : ℝ, 0 < P ∧ M / P = A + Bc / P := by
  have hpos : 0 < M - Bc := sub_pos.mpr hM
  refine ⟨(M - Bc) / A, ⟨div_pos hpos hA, ?_⟩, ?_⟩
  · field_simp
    ring
  · rintro P ⟨hP, h⟩
    rw [eq_div_iff hA.ne']
    field_simp at h
    linarith

/-- Cochrane (2023), §10.2, p. 298: with a walled-off central bank, the price level
`P = (M − B_c)/A` is set by the central bank's balance sheet alone; a treasury that cannot meet
its debt to the public defaults on it, with haircut `D = (P V_T − B_c)/B_p`, without causing
inflation. -/
theorem walled_off_insulated {M A Bc Bp VT P D : ℝ} (hA : A ≠ 0) (hP : P ≠ 0) (hBp : Bp ≠ 0)
    (hcb : M / P = A + Bc / P) (htr : (Bp * D + Bc) / P = VT) :
    P = (M - Bc) / A ∧ D = (P * VT - Bc) / Bp := by
  constructor
  · rw [eq_div_iff hA]
    field_simp at hcb
    linarith
  · rw [eq_div_iff hBp]
    rw [div_eq_iff hP] at htr
    linarith

/-- Cochrane (2023), §10.2, p. 298: "topping up central bank assets would be a way to slow
inflation, and confiscating those asset would be a way to create inflation": `P = (M − B_c)/A`
is strictly decreasing in the real assets `A > 0` (for `M > B_c`). -/
theorem topping_up_lowers_price {M Bc A A' : ℝ} (hM : Bc < M) (hA : 0 < A) (hAA : A < A') :
    (M - Bc) / A' < (M - Bc) / A :=
  div_lt_div_of_pos_left (sub_pos.mpr hM) hA hAA

/-- Cochrane (2023), §10.4, p. 301: "It is also desirable for the assets on the right-hand side to
have a stable value, so as not to induce inflation volatility": with `P = (M − n)/a` (nominal
asset `n`, real asset value `a`), the log price level moves one-for-one, inversely, with the log
asset value. -/
theorem asset_volatility_passes_through {M n a₁ a₂ : ℝ} (hM : n < M) (h₁ : 0 < a₁)
    (h₂ : 0 < a₂) :
    Real.log ((M - n) / a₁) - Real.log ((M - n) / a₂) = Real.log a₂ - Real.log a₁ := by
  have hpos : 0 < M - n := sub_pos.mpr hM
  rw [Real.log_div hpos.ne' h₁.ne', Real.log_div hpos.ne' h₂.ne']
  ring

end Cochrane.AssetsRulesBalanceSheets.BalanceSheets
