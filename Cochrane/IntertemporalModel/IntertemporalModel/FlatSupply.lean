/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.FiscalMonetary

/-!
# The flat supply curve

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.9, pp. 47–49.

The central bank sets the interest rate; the Treasury then chooses the face value of debt `B_t`
from the flow condition (2.28) `B_{t−1}/P_t = s_t + Q_t B_t/P_t` given the bond price
`Q_t = 1/(1 + i_t)`. Together they sell any quantity of debt at the fixed rate: a flat supply
curve meeting the unit-elastic demand for debt.

## Main results

* `eq_2_28`, `eq_2_28_zero`: the flow condition (2.28) holds in equilibrium (the book cites it as
  "the flow condition (2.15)"; it is (2.4)/(2.9), survey E9).
* `treasury_rule_iff`: (2.28) is equivalent to the Treasury rule `B_t = (B_{t−1} − P_t s_t)/Q_t`;
  `treasury_rule_of_equilibrium`, `treasury_rule_of_equilibrium_zero`.
* `flat_supply_revenue`: whatever bond price the central bank sets, the Treasury rule raises the
  same nominal revenue `Q_t B_t = B_{t−1} − P_t s_t`; `flat_supply_meets_demand`: for every bond
  price exactly one quantity meets the unit-elastic demand `Q_t B_t/P_t = PV^{ex}_t`.
* `treasury_debt_ratio`: a higher rate raises the face value sold in proportion to `1 + i_t`;
  `one_percent_price_fall`, `one_percent_printed_fails` (a 1% lower bond price requires
  `1/99`, not 1%, more face value; survey E7).
* `twoStep`, `twoStep_eq_pegP`, `twoStep_debt_eq_pegB`, `twoStep_equilibrium`: the two-step
  process (central bank sets `i_t`, Treasury applies its rule, the price level satisfies the
  valuation equation) reproduces exactly the interest-rate-target equilibrium, so the central
  bank and Treasury together generate the flat supply curve.
-/

namespace Cochrane.IntertemporalModel.FlatSupply

open FiscalMonetary

variable {Ω : Type*} {𝔼 : ExpectationSystem Ω} {β : ℝ} {Bm1 : Ω → ℝ} {s B P i : ℕ → Ω → ℝ}

/-- Cochrane (2023), eq. (2.28), p. 48: the flow condition
`B_t/P_{t+1} = s_{t+1} + Q_{t+1} B_{t+1}/P_{t+1}` with `Q = 1/(1 + i)` holds in equilibrium (the
book's reference "(2.15)" should be (2.4)/(2.9), survey E9). -/
theorem eq_2_28 (hPO : 𝔼.PullOut) (hs : SurplusSummable β s) (hsa : 𝔼.Adapted s)
    (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) (ω : Ω) :
    B t ω / P (t + 1) ω = s (t + 1) ω + (1 + i (t + 1) ω)⁻¹ * (B (t + 1) ω / P (t + 1) ω) := by
  have e := congrFun (eq_2_26 hPO hs hsa h t).1 ω
  simp only [Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply, Pi.one_apply] at e
  rw [e, mul_comm]

/-- Cochrane (2023), eq. (2.28), p. 48, at the initial date:
`B_{−1}/P_0 = s_0 + Q_0 B_0/P_0`. -/
theorem eq_2_28_zero (hPO : 𝔼.PullOut) (hs : SurplusSummable β s) (hsa : 𝔼.Adapted s)
    (h : Equilibrium 𝔼 β Bm1 s B P i) (ω : Ω) :
    Bm1 ω / P 0 ω = s 0 ω + (1 + i 0 ω)⁻¹ * (B 0 ω / P 0 ω) := by
  have e := congrFun (eq_2_26_zero hPO hs hsa h).1 ω
  simp only [Pi.add_apply, Pi.mul_apply, Pi.div_apply, Pi.inv_apply, Pi.one_apply] at e
  rw [e, mul_comm]

/-- Cochrane (2023), eq. (2.28), p. 48, "how much nominal debt `B_t` the Treasury must sell":
for `Q_t ≠ 0` and `P_t ≠ 0`, (2.28) holds iff `B_t = (B_{t−1} − P_t s_t)/Q_t`. -/
theorem treasury_rule_iff {Bprev Pt st Qt Bt : ℝ} (hQ : Qt ≠ 0) (hP : Pt ≠ 0) :
    Bprev / Pt = st + Qt * Bt / Pt ↔ Bt = (Bprev - Pt * st) / Qt := by
  constructor
  · intro h
    field_simp at h
    rw [eq_div_iff hQ]
    linear_combination -h
  · intro h
    rw [h]
    field_simp
    ring

/-- Cochrane (2023), eq. (2.28), p. 48: in equilibrium the debt sold follows the Treasury rule
`B_{t+1} = (B_t − P_{t+1} s_{t+1})(1 + i_{t+1})`. -/
theorem treasury_rule_of_equilibrium (hPO : 𝔼.PullOut) (hs : SurplusSummable β s)
    (hsa : 𝔼.Adapted s) (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) (ω : Ω) :
    B (t + 1) ω = (B t ω - P (t + 1) ω * s (t + 1) ω) * (1 + i (t + 1) ω) := by
  have e := flow_nominal hPO hs hsa h t ω
  have hi : 1 + i (t + 1) ω ≠ 0 := by linarith [h.2.2.2.2.1 (t + 1) ω]
  rw [e]
  field_simp
  ring

/-- Cochrane (2023), eq. (2.28), p. 48, at the initial date:
`B_0 = (B_{−1} − P_0 s_0)(1 + i_0)`. -/
theorem treasury_rule_of_equilibrium_zero (hPO : 𝔼.PullOut) (hs : SurplusSummable β s)
    (hsa : 𝔼.Adapted s) (h : Equilibrium 𝔼 β Bm1 s B P i) (ω : Ω) :
    B 0 ω = (Bm1 ω - P 0 ω * s 0 ω) * (1 + i 0 ω) := by
  have e := eq_2_28_zero hPO hs hsa h ω
  have hi : 1 + i 0 ω ≠ 0 := by linarith [h.2.2.2.2.1 0 ω]
  have hP := (h.2.1 0 ω).ne'
  field_simp at e
  linear_combination -e

/-- Cochrane (2023), p. 48, "to obtain the same revenue": under the Treasury rule the nominal
revenue `Q_t B_t = B_{t−1} − P_t s_t` does not depend on the bond price the central bank sets,
so supply is flat at any price. -/
theorem flat_supply_revenue {Bprev Pt st Qt : ℝ} (hQ : Qt ≠ 0) :
    Qt * ((Bprev - Pt * st) / Qt) = Bprev - Pt * st := by
  field_simp

/-- Cochrane (2023), §2.4.3, p. 31, and §2.9, p. 48: a horizontal supply curve meets the
unit-elastic demand for debt `Q_t B_t/P_t = PV^{ex}_t` at exactly one quantity, whatever the
bond price `Q_t > 0`. -/
theorem flat_supply_meets_demand {Pt Qt R : ℝ} (hP : Pt ≠ 0) (hQ : Qt ≠ 0) :
    ∃! Bt : ℝ, Qt * Bt / Pt = R := by
  refine ⟨R * Pt / Qt, by field_simp, fun y hy => ?_⟩
  field_simp at hy ⊢
  linarith

/-- Cochrane (2023), p. 48, "if the central bank raises interest rates ... the Treasury then
raises the face value of debt it sells": with the same maturing debt, price level and surplus,
the Treasury rule at gross rates `1 + i` and `1 + i'` gives `B'_t/B_t = (1 + i'_t)/(1 + i_t)`. -/
theorem treasury_debt_ratio {Bprev Pt st i0 i1 : ℝ}
    (hrev : Bprev - Pt * st ≠ 0) :
    ((Bprev - Pt * st) * (1 + i1)) / ((Bprev - Pt * st) * (1 + i0)) = (1 + i1) / (1 + i0) :=
  mul_div_mul_left _ _ hrev

/-- Cochrane (2023), p. 48 (survey E7): when the bond price falls by one percent,
`Q' = 0.99 Q`, the Treasury rule raises the face value by exactly `1/99`. -/
theorem one_percent_price_fall {Bprev Pt st Qt : ℝ} (hQ : Qt ≠ 0) (hrev : Bprev - Pt * st ≠ 0) :
    ((Bprev - Pt * st) / (99 / 100 * Qt)) / ((Bprev - Pt * st) / Qt) - 1 = 1 / 99 := by
  field_simp
  ring

/-- Cochrane (2023), p. 48 (survey E7): the printed "raises the face value ... by one percent"
is an approximation: the exact rise `1/99` differs from `1/100`. -/
theorem one_percent_printed_fails : (1 / 99 : ℝ) ≠ 1 / 100 := by norm_num

/-! ### The two-step process: central bank sets `i`, Treasury follows its rule -/

/-- Cochrane (2023), §2.9, p. 48: the nominal debt maturing at date `t` in the two-step process:
`D_0 = B_{−1}`; the price level is `P_t = D_t/PV_t` (valuation equation) and the Treasury sells
`D_{t+1} = (D_t − P_t s_t)(1 + i_t)` at the rate the central bank sets. -/
noncomputable def twoStep (𝔼 : ExpectationSystem Ω) (β : ℝ) (Bm1 : Ω → ℝ) (s i : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ
  | 0 => Bm1
  | t + 1 =>
    (twoStep 𝔼 β Bm1 s i t - twoStep 𝔼 β Bm1 s i t / pv 𝔼 β s t * s t) * (1 + i t)

/-- Cochrane (2023), §2.9, p. 48: the two-step process produces the interest-rate-target price
level, `D_t/PV_t = pegP_t`. -/
theorem twoStep_eq_pegP (hs : SurplusSummable β s) (hsa : 𝔼.Adapted s)
    (hpv : ∀ t ω, pv 𝔼 β s t ω ≠ 0) (t : ℕ) :
    twoStep 𝔼 β Bm1 s i t / pv 𝔼 β s t = pegP 𝔼 β Bm1 s i t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [pegP_succ]
    congr 1
    change (twoStep 𝔼 β Bm1 s i t - twoStep 𝔼 β Bm1 s i t / pv 𝔼 β s t * s t) * (1 + i t) =
      (1 + i t) * pegP 𝔼 β Bm1 s i t * pvEx 𝔼 β s t
    rw [← ih]
    funext ω
    have e := congrFun (pv_eq_add_pvEx 𝔼 hs hsa t) ω
    simp only [Pi.add_apply] at e
    have := hpv t ω
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.one_apply]
    rw [show pvEx 𝔼 β s t ω = pv 𝔼 β s t ω - s t ω by linarith]
    field_simp

/-- Cochrane (2023), §2.9, p. 48: the debt the Treasury sells in the two-step process is the
debt sold on the flat supply curve, `D_{t+1} = pegB_t`. -/
theorem twoStep_debt_eq_pegB (hs : SurplusSummable β s) (hsa : 𝔼.Adapted s)
    (hpv : ∀ t ω, pv 𝔼 β s t ω ≠ 0) (t : ℕ) :
    twoStep 𝔼 β Bm1 s i (t + 1) = pegB 𝔼 β Bm1 s i t := by
  have h1 := twoStep_eq_pegP (Bm1 := Bm1) (i := i) hs hsa hpv (t + 1)
  rw [pegP_succ] at h1
  funext ω
  have e := congrFun h1 ω
  simp only [Pi.div_apply] at e
  have := hpv (t + 1) ω
  exact (div_left_inj' this).mp e

/-- Cochrane (2023), §2.9, p. 48, "the central bank plus Treasury thus really do sell any
quantity of debt at the fixed interest rate": the two-step process is the (unique)
interest-rate-target equilibrium. -/
theorem twoStep_equilibrium (hPO : 𝔼.PullOut) (hs : SurplusSummable β s) (hsa : 𝔼.Adapted s)
    (hBm1 : 𝔼.E 0 Bm1 = Bm1) (hB : ∀ ω, 0 < Bm1 ω) (hia : 𝔼.Adapted i)
    (hi : ∀ t ω, -1 < i t ω) (hpv : ∀ t ω, 0 < pv 𝔼 β s t ω)
    (hpvEx : ∀ t ω, 0 < pvEx 𝔼 β s t ω) :
    Equilibrium 𝔼 β Bm1 s (fun t => twoStep 𝔼 β Bm1 s i (t + 1))
      (fun t => twoStep 𝔼 β Bm1 s i t / pv 𝔼 β s t) i := by
  have hpv' : ∀ t ω, pv 𝔼 β s t ω ≠ 0 := fun t ω => (hpv t ω).ne'
  have e1 : (fun t => twoStep 𝔼 β Bm1 s i (t + 1)) = pegB 𝔼 β Bm1 s i :=
    funext (twoStep_debt_eq_pegB hs hsa hpv')
  have e2 : (fun t => twoStep 𝔼 β Bm1 s i t / pv 𝔼 β s t) = pegP 𝔼 β Bm1 s i :=
    funext (twoStep_eq_pegP hs hsa hpv')
  rw [e1, e2]
  exact peg_equilibrium hPO hBm1 hB hia hi hpv hpvEx

end Cochrane.IntertemporalModel.FlatSupply
