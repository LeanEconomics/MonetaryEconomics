/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.MaturingDebt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Bond sales and bond-price targets

Cochrane (2023), §7.3 and §7.3.1–7.3.2, pp. 220–224, equations (7.8)–(7.13).

The government inherits `B_{−1}^{(j)} = D 0 j`, sells `B_0^{(j)} − B_{−1}^{(j)}` at date 0
(`B_0^{(j)} = D 1 j`) and never trades again.

## Main results

* `maturing_eq` — (7.9): `B_0^{(j)}/P_j = s_j` for `j ≥ 1`.
* `E_price_eq` — `B_0^{(j)} E_0(1/P_j) = E_0 s_j`; `bondPrice_mul_debt` — (7.10);
  `real_revenue` — (7.11): `Q_0^{(j)} B_0^{(j)}/P_0 = β^j E_0 s_j`, independent of the amount sold.
* `dilution_formula` — (7.12): `B_{−1}^{(0)}/P_0 =
  s_0 + ∑_{j≥1} β^j ((B_0^{(j)} − B_{−1}^{(j)})/B_0^{(j)}) E_0 s_j`.
* `no_outstanding` — (7.13), and `no_outstanding_price_indep`: with no long-term debt outstanding,
  `P_0` does not depend on the sales.
* `sales_lower_bondPrice`, `sales_raise_future_price`: additional sales lower bond prices and raise
  future price levels.
* `bondPrice_target_iff`: a bond-price target is supported by a unique, finite quantity of debt;
  `unit_elasticity`: `d log B / d log Q = −1`.
* `outstanding_sales_lower_price`, `hasDerivAt_dilution`: with long-term debt outstanding,
  additional sales raise revenue and lower `P_0`.
* `offset_shock`: a state-contingent sale can offset a surplus shock at date 0, at the cost of a
  higher future price level.
-/

namespace Cochrane.LongTermDebtDynamics.BondSales

open Filter Topology MaturityStructure

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §7.3, p. 221: debt is sold or bought at date 0 only: `B_t^{(t+j)} =
B_{t−1}^{(t+j)}` for every `t ≥ 1` and `j ≥ 1`. -/
def SalesAtZeroOnly (D : ℕ → ℕ → Ω → ℝ) : Prop :=
  ∀ t j, D (t + 2) (t + 1 + (j + 1)) = D (t + 1) (t + 1 + (j + 1))

/-- Cochrane (2023), §7.3, p. 221: after date 0 the debt outstanding is `B_0^{(m)}`. -/
theorem debt_eq_one {D : ℕ → ℕ → Ω → ℝ} (h : SalesAtZeroOnly D) (t k : ℕ) :
    D (t + 1) (t + 1 + k) = D 1 (t + 1 + k) := by
  induction t generalizing k with
  | zero => rfl
  | succ t ih =>
    rw [show t + 1 + 1 + k = t + 1 + (k + 1) by omega, h t k, ih]

/-- Cochrane (2023), eq. (7.9), p. 221: after the date-0 sales each surplus pays off the debt
maturing at its date, `B_0^{(t)}/P_t = s_t` for `t ≥ 1`. -/
theorem maturing_eq {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (h : SalesAtZeroOnly D)
    {t : ℕ} (hflow : RealFlow 𝔼 β D x s (t + 1)) (ω : Ω) : D 1 (t + 1) ω * x (t + 1) ω =
      s (t + 1) ω := by
  have hz : (fun j : ℕ => β ^ (j + 1) * (sales D (t + 1) (t + 1 + (j + 1)) ω *
      𝔼.E (t + 1) (x (t + 1 + (j + 1))) ω)) = fun _ => 0 := by
    funext j
    simp [sales, h t j]
  have h0 := hflow ω
  rw [hz] at h0
  have := h0.unique hasSum_zero
  have hD := debt_eq_one h t 0
  rw [add_zero] at hD
  rw [← hD]
  linarith

/-- Cochrane (2023), eqs. (7.9)–(7.10), p. 221: `B_0^{(j)} E_0(1/P_j) = E_0 s_j` for `j ≥ 1`
(pull-out of the date-0 choice `B_0^{(j)}`). -/
theorem E_price_eq (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (h : SalesAtZeroOnly D) (hflow : ∀ t, RealFlow 𝔼 β D x s t)
    (j : ℕ) : D 1 (j + 1) * 𝔼.E 0 (x (j + 1)) = 𝔼.E 0 (s (j + 1)) := by
  have hm : D 1 (j + 1) * x (j + 1) = s (j + 1) := by
    funext ω; exact maturing_eq 𝔼 h (hflow (j + 1)) ω
  rw [← hpo 0 _ _ (hD.2 0 _), hm]

/-- Cochrane (2023), eq. (7.10), p. 221: `Q_0^{(j)} = β^j E_0(P_0/P_j)`, so
`Q_0^{(j)} B_0^{(j)} = β^j P_0 E_0 s_j`. -/
theorem bondPrice_mul_debt (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {P x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (h : SalesAtZeroOnly D) (hP : 𝔼.Adapted P)
    (hflow : ∀ t, RealFlow 𝔼 β D x s t) (j : ℕ) :
    bondPrice 𝔼 β P x 0 (j + 1) * D 1 (j + 1) = β ^ (j + 1) • (P 0 * 𝔼.E 0 (s (j + 1))) := by
  rw [bondPrice_eq 𝔼 hpo hP, ← E_price_eq 𝔼 hpo hD h hflow j]
  funext ω
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, zero_add]
  ring

/-- Cochrane (2023), eq. (7.11), p. 221: the real end-of-period value of date-`j` debt is
`Q_0^{(j)} B_0^{(j)}/P_0 = β^j E_0 s_j`, independent of the amount sold. -/
theorem real_revenue (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {P x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (h : SalesAtZeroOnly D) (hP : 𝔼.Adapted P)
    (hPx : ∀ t ω, P t ω * x t ω = 1) (hflow : ∀ t, RealFlow 𝔼 β D x s t) (j : ℕ) (ω : Ω) :
    bondPrice 𝔼 β P x 0 (j + 1) ω * D 1 (j + 1) ω * x 0 ω =
      β ^ (j + 1) * 𝔼.E 0 (s (j + 1)) ω := by
  have := congrFun (bondPrice_mul_debt 𝔼 hpo hD h hP hflow j) ω
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at this
  rw [this]
  linear_combination (β ^ (j + 1) * 𝔼.E 0 (s (j + 1)) ω) * hPx 0 ω

/-- Cochrane (2023), eq. (7.12), p. 222: **the dilution formula.** With sales at date 0 only and
`B_0^{(j)} ≠ 0`,
`B_{−1}^{(0)}/P_0 = s_0 + ∑_{j≥1} β^j ((B_0^{(j)} − B_{−1}^{(j)})/B_0^{(j)}) E_0 s_j`,
a genuine convergent series. -/
theorem dilution_formula (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (h : SalesAtZeroOnly D) (hD1 : ∀ j ω, D 1 (j + 1) ω ≠ 0)
    (hflow : ∀ t, RealFlow 𝔼 β D x s t) (ω : Ω) :
    HasSum (fun j : ℕ => β ^ (j + 1) * ((D 1 (j + 1) ω - D 0 (j + 1) ω) / D 1 (j + 1) ω *
      𝔼.E 0 (s (j + 1)) ω)) (D 0 0 ω * x 0 ω - s 0 ω) := by
  refine (hflow 0 ω).congr_fun fun j => ?_
  have he := congrFun (E_price_eq 𝔼 hpo hD h hflow j) ω
  simp only [Pi.mul_apply] at he
  simp only [sales, zero_add, Pi.sub_apply]
  rw [← he]
  field_simp [hD1 j ω]

/-- Cochrane (2023), eq. (7.13), p. 222: with no long-term debt outstanding
(`B_{−1}^{(j)} = 0`, `j ≥ 1`), `B_{−1}^{(0)}/P_0 = s_0 + ∑_{j≥1} β^j E_0 s_j`. -/
theorem no_outstanding (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (h : SalesAtZeroOnly D) (hD1 : ∀ j ω, D 1 (j + 1) ω ≠ 0)
    (hD0 : ∀ j, D 0 (j + 1) = 0) (hflow : ∀ t, RealFlow 𝔼 β D x s t) (ω : Ω) :
    HasSum (fun j : ℕ => β ^ (j + 1) * 𝔼.E 0 (s (j + 1)) ω) (D 0 0 ω * x 0 ω - s 0 ω) := by
  refine (dilution_formula 𝔼 hpo hD h hD1 hflow ω).congr_fun fun j => ?_
  rw [hD0 j, Pi.zero_apply, sub_zero, div_self (hD1 j ω), one_mul]

/-- Cochrane (2023), §7.3.1, p. 222 (bullet): with no long-term debt outstanding, `P_0` is
determined by fiscal shocks alone: two debt policies with the same inherited debt and surpluses
give the same `P_0`, whatever the amounts sold. -/
theorem no_outstanding_price_indep (hpo : 𝔼.PullOut) {β : ℝ} {D D' : ℕ → ℕ → Ω → ℝ}
    {x x' s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (hD' : Predetermined 𝔼 D')
    (h : SalesAtZeroOnly D) (h' : SalesAtZeroOnly D') (hD1 : ∀ j ω, D 1 (j + 1) ω ≠ 0)
    (hD1' : ∀ j ω, D' 1 (j + 1) ω ≠ 0) (hD0 : ∀ j, D 0 (j + 1) = 0) (hinit : D 0 0 = D' 0 0)
    (hD00 : ∀ ω, D 0 0 ω ≠ 0) (hD0' : ∀ j, D' 0 (j + 1) = 0)
    (hflow : ∀ t, RealFlow 𝔼 β D x s t) (hflow' : ∀ t, RealFlow 𝔼 β D' x' s t) :
    x 0 = x' 0 := by
  funext ω
  have h1 := (no_outstanding 𝔼 hpo hD h hD1 hD0 hflow ω).unique
    (no_outstanding 𝔼 hpo hD' h' hD1' hD0' hflow' ω)
  rw [← hinit] at h1
  exact mul_left_cancel₀ (hD00 ω) (by linarith)

/-- Cochrane (2023), §7.3.1, p. 222 (bullet): additional sales lower the bond price: with
`Q_0^{(j)} B_0^{(j)} = β^j P_0 E_0 s_j > 0` fixed, a larger `B_0^{(j)}` means a lower
`Q_0^{(j)}`. -/
theorem sales_lower_bondPrice {c b b' q q' : ℝ} (hc : 0 < c) (hb : 0 < b) (hbb' : b < b')
    (hq : q * b = c) (hq' : q' * b' = c) : q' < q := by
  have hb' : 0 < b' := hb.trans hbb'
  have e1 : q = c / b := by rw [eq_div_iff hb.ne']; exact hq
  have e2 : q' = c / b' := by rw [eq_div_iff hb'.ne']; exact hq'
  rw [e1, e2]
  exact div_lt_div_of_pos_left hc hb hbb'

/-- Cochrane (2023), §7.3.1, p. 222 (bullet): additional sales raise the future price level:
`1/P_j = s_j / B_0^{(j)}` falls when `B_0^{(j)}` rises (for `s_j > 0`). -/
theorem sales_raise_future_price {sj b b' x x' : ℝ} (hs : 0 < sj) (hb : 0 < b) (hbb' : b < b')
    (hx : b * x = sj) (hx' : b' * x' = sj) : x' < x := by
  have hb' : 0 < b' := hb.trans hbb'
  have e1 : x = sj / b := by rw [eq_div_iff hb.ne', mul_comm]; exact hx
  have e2 : x' = sj / b' := by rw [eq_div_iff hb'.ne', mul_comm]; exact hx'
  rw [e1, e2]
  exact div_lt_div_of_pos_left hs hb hbb'

/-- Cochrane (2023), §7.3.1, p. 223 (bullet): the government can target the long-term bond price
`Q_0^{(j)} = q ≠ 0` by trading freely at that price; the quantity sold is then finite and unique,
`B_0^{(j)} = β^j P_0 E_0 s_j / q` (from (7.11)). -/
theorem bondPrice_target_iff (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ}
    {P x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (h : SalesAtZeroOnly D) (hP : 𝔼.Adapted P)
    (hflow : ∀ t, RealFlow 𝔼 β D x s t) (j : ℕ) {q : ℝ} (hq : q ≠ 0) (ω : Ω)
    (hQ : bondPrice 𝔼 β P x 0 (j + 1) ω = q) :
    D 1 (j + 1) ω = β ^ (j + 1) * P 0 ω * 𝔼.E 0 (s (j + 1)) ω / q := by
  have := congrFun (bondPrice_mul_debt 𝔼 hpo hD h hP hflow j) ω
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hQ] at this
  rw [eq_div_iff hq, mul_comm, this]
  ring

/-- Cochrane (2023), §7.3.1, p. 223: unit elasticity: along the demand curve `B = c/Q`
(from (7.11)), `d log B / d log Q = −1`. -/
theorem unit_elasticity (c u : ℝ) (hc : 0 < c) :
    HasDerivAt (fun v => Real.log (c / Real.exp v)) (-1) u := by
  have : (fun v => Real.log (c / Real.exp v)) = fun v => Real.log c - v := by
    funext v
    rw [Real.log_div hc.ne' (Real.exp_pos v).ne', Real.log_exp]
  rw [this]
  simpa using (hasDerivAt_id u).const_sub (Real.log c)

/-- Cochrane (2023), §7.3.2, p. 223 (bullet): **with long-term debt outstanding, additional sales
lower `P_0`.** Compare two policies with the same inherited debt (`B_{−1}^{(j)} ≥ 0`, `B_{−1}^{(0)}
> 0`) and surpluses (`E_0 s_j ≥ 0`), where the second sells weakly more of every maturity, and
strictly more of a maturity `j` with `B_{−1}^{(j)} > 0`, `E_0 s_j > 0`: then `1/P_0` is strictly
higher. -/
theorem outstanding_sales_lower_price {β : ℝ} (hβ : 0 < β) {d0 b b' e : ℕ → ℝ}
    {D00 s0 x0 x0' : ℝ} (hD00 : 0 < D00) (hd : ∀ j, 0 ≤ d0 j) (hb : ∀ j, 0 < b j)
    (hbb' : ∀ j, b j ≤ b' j) (he : ∀ j, 0 ≤ e j) {j₀ : ℕ} (hd₀ : 0 < d0 j₀)
    (hb₀ : b j₀ < b' j₀) (he₀ : 0 < e j₀)
    (hx : HasSum (fun j => β ^ (j + 1) * ((b j - d0 j) / b j * e j)) (D00 * x0 - s0))
    (hx' : HasSum (fun j => β ^ (j + 1) * ((b' j - d0 j) / b' j * e j)) (D00 * x0' - s0)) :
    x0 < x0' := by
  have hmono : ∀ j, (b j - d0 j) / b j ≤ (b' j - d0 j) / b' j := by
    intro j
    have hb' : 0 < b' j := (hb j).trans_le (hbb' j)
    rw [sub_div, sub_div, div_self (hb j).ne', div_self hb'.ne']
    exact sub_le_sub_left (div_le_div_of_nonneg_left (hd j) (hb j) (hbb' j)) 1
  have hlt : (b j₀ - d0 j₀) / b j₀ < (b' j₀ - d0 j₀) / b' j₀ := by
    have hb' : 0 < b' j₀ := (hb j₀).trans hb₀
    rw [sub_div, sub_div, div_self (hb j₀).ne', div_self hb'.ne']
    exact sub_lt_sub_left (div_lt_div_of_pos_left hd₀ (hb j₀) hb₀) 1
  have := hasSum_lt (f := fun j => β ^ (j + 1) * ((b j - d0 j) / b j * e j))
    (g := fun j => β ^ (j + 1) * ((b' j - d0 j) / b' j * e j)) (i := j₀)
    (fun j => mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hmono j) (he j))
      (pow_nonneg hβ.le _))
    (mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right hlt he₀) (pow_pos hβ _)) hx hx'
  nlinarith

/-- Cochrane (2023), §7.3.2, p. 223: the marginal effect of selling more maturity-`j` debt on
`1/P_0`: with `B_{−1}^{(0)}/P_0 = c + β^j (1 − B_{−1}^{(j)}/B_0^{(j)}) E_0 s_j`, the derivative with
respect to `B_0^{(j)} = b` is `β^j B_{−1}^{(j)} E_0 s_j / (b² B_{−1}^{(0)}) > 0`. -/
theorem hasDerivAt_dilution (c βj d e D00 b : ℝ) (hb : b ≠ 0) :
    HasDerivAt (fun v => (c + βj * (1 - d / v) * e) / D00) (βj * d * e / (b ^ 2 * D00)) b := by
  have h1 : HasDerivAt (fun v => d / v) (-(d / b ^ 2)) b := by
    simpa [div_eq_mul_inv, neg_div] using (hasDerivAt_inv hb).const_mul d
  have h2 := ((((h1.const_sub 1).const_mul βj).mul_const e).const_add c).div_const D00
  convert h2 using 1
  field_simp

/-- Cochrane (2023), §7.3.2, p. 224 (bullet): **a state-contingent sale can offset a surplus
shock.** If the date-0 surplus falls by `δ ≥ 0` and the revenue from maturity `j`
(`R = β^j (1 − d/b) e`, `d = B_{−1}^{(j)} > 0`, `e = E_0 s_j > 0`) can rise by `δ`
(`R + δ < β^j e`),
there is a sale `b' ≥ b` raising exactly the extra revenue `δ`, so `P_0` is unchanged; when
`δ > 0` the sale is strictly larger, raising the future price level `P_j = b'/s_j`. -/
theorem offset_shock {βj d e b δ : ℝ} (hβ : 0 < βj) (hd : 0 < d) (he : 0 < e) (hb : 0 < b)
    (hδ : 0 ≤ δ) (hR : βj * (1 - d / b) * e + δ < βj * e) :
    ∃ b', b ≤ b' ∧ βj * (1 - d / b') * e = βj * (1 - d / b) * e + δ ∧ (0 < δ → b < b') := by
  set R := βj * (1 - d / b) * e + δ with hRdef
  have hpos : 0 < βj * e - R := by linarith
  refine ⟨d * (βj * e) / (βj * e - R), ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hpos]
    have : βj * e - R = βj * e * d / b - δ := by rw [hRdef]; field_simp; ring
    rw [this]
    have hbe : 0 < βj * e := mul_pos hβ he
    have : b * (βj * e * d / b - δ) = βj * e * d - b * δ := by field_simp
    rw [this]
    nlinarith [mul_nonneg hb.le hδ]
  · have hne : βj * e - R ≠ 0 := hpos.ne'
    have hd0 : d ≠ 0 := hd.ne'
    have hbe : βj * e ≠ 0 := (mul_pos hβ he).ne'
    field_simp
    ring
  · intro hδpos
    rw [lt_div_iff₀ hpos]
    have : βj * e - R = βj * e * d / b - δ := by rw [hRdef]; field_simp; ring
    rw [this]
    have : b * (βj * e * d / b - δ) = βj * e * d - b * δ := by field_simp
    rw [this]
    nlinarith [mul_pos hb hδpos]

end Cochrane.LongTermDebtDynamics.BondSales
