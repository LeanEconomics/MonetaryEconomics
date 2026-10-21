/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.BondSales

/-!
# Expected future bond sales: the three-period economy

Cochrane (2023), §7.3.3, p. 224, and Online Appendix §A1.14, pp. 588–592, equations
(1.63)–(1.68).

Dates 0, 1, 2. Inherited debt `B_{−1}^{(0)}, B_{−1}^{(1)}, B_{−1}^{(2)}` (`D 0 0`, `D 0 1`, `D 0
2`);
at date 0 the government sells time-1 and time-2 debt (`B_0^{(1)} = D 1 1`, `B_0^{(2)} = D 1 2`);
at date 1 it may sell more time-2 debt, `B_1^{(2)} − B_0^{(2)}` (`B_1^{(2)} = D 2 2`), the expected
future sale. Surpluses are unchanged throughout.

## Main results

* `flows_of_realFlow`: the general flow conditions (7.1) reduce to the three flow equations.
* `price_two` (1.63), `price_one` (1.64), `price_zero` (1.65)/(1.66).
* `no_outstanding_price_zero`: with no long-term debt outstanding the expected sale has no effect on
  `P_0` (§A1.14.1).
* `price_two_symm`, `bondPrice_two_symm`: future sales enter symmetrically with date-0 sales in
  `P_2` and (with no outstanding debt) in `Q_0^{(2)}`; a date-0 purchase can be undone by an
  expected future sale.
* `x1_formula`, `future_sales_raise_Q1`: expected sales raise `E_0(1/P_1)` and the bond price
  `Q_0^{(1)}` when time-2 debt has been sold.
* `no_time0_sales`: with no date-0 sales the expected sale has no effect on `P_0` (interaction
  only).
* `price_zero_no_sale_two` (1.67), `price_zero_no_sale_one` (1.68).
* `x0_closed`, `hasDerivAt_x0`, `x0_strictMono`, `x0_strictAnti`, `x0_const`: the sign of the
  effect of expected sales on `P_0` is the sign of `A₂ − A₁`, with
  `A_k = (B_0^{(k)} − B_{−1}^{(k)})/B_0^{(k)}`.
-/

namespace Cochrane.LongTermDebtDynamics.FutureSales

open Filter Topology MaturityStructure

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), Online Appendix §A1.14, pp. 589–590: in the three-period economy (no debt
maturing after date 2) the flow conditions (7.1) at dates 0, 1, 2 are the three displayed
equations. -/
theorem flows_of_realFlow {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD3 : ∀ t j, D t (j + 3) = 0) (h0 : RealFlow 𝔼 β D x s 0) (h1 : RealFlow 𝔼 β D x s 1)
    (h2 : RealFlow 𝔼 β D x s 2) :
    D 2 2 * x 2 = s 2 ∧
      D 1 1 * x 1 = s 1 + β • ((D 2 2 - D 1 2) * 𝔼.E 1 (x 2)) ∧
      D 0 0 * x 0 = s 0 + β • ((D 1 1 - D 0 1) * 𝔼.E 0 (x 1)) +
        β ^ 2 • ((D 1 2 - D 0 2) * 𝔼.E 0 (x 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · funext ω
    have hz : (fun j : ℕ => β ^ (j + 1) * (sales D 2 (2 + (j + 1)) ω *
        𝔼.E 2 (x (2 + (j + 1))) ω)) = fun _ => 0 := by
      funext j
      simp [sales, show 2 + (j + 1) = j + 3 by omega, hD3]
    have := (h2 ω)
    rw [hz] at this
    have := this.unique hasSum_zero
    simp only [Pi.mul_apply]
    linarith
  · funext ω
    have hz : (fun j : ℕ => β ^ (j + 1) * (sales D 1 (1 + (j + 1)) ω *
        𝔼.E 1 (x (1 + (j + 1))) ω)) =
        Pi.single 0 (β * ((D 2 2 ω - D 1 2 ω) * 𝔼.E 1 (x 2) ω)) := by
      funext j
      rcases j with _ | j
      · simp [sales]
      · simp [sales, show 1 + (j + 1 + 1) = j + 3 by omega, hD3]
    have := (h1 ω)
    rw [hz] at this
    have := this.unique (hasSum_pi_single 0 _)
    simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    linarith
  · funext ω
    have hfin : ∀ j ∉ ({0, 1} : Finset ℕ), β ^ (j + 1) * (sales D 0 (0 + (j + 1)) ω *
        𝔼.E 0 (x (0 + (j + 1))) ω) = 0 := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
      simp [sales, show 0 + (k + 2 + 1) = k + 3 by omega, hD3]
    have := (h0 ω).unique (hasSum_sum_of_ne_finset_zero hfin)
    simp only [Finset.sum_insert (by simp : (0 : ℕ) ∉ ({1} : Finset ℕ)), Finset.sum_singleton,
      sales] at this
    simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    norm_num at this ⊢
    linarith

/-- Cochrane (2023), Online Appendix eq. (1.63), p. 589: `B_1^{(2)}/P_2 = s_2`, so total time-2 debt
`B_1^{(2)} = B_0^{(2)} + (B_1^{(2)} − B_0^{(2)})` sets `P_2`. -/
theorem price_two {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (F2 : D 2 2 * x 2 = s 2)
    (hD22 : ∀ ω, D 2 2 ω ≠ 0) : x 2 = s 2 / D 2 2 := by
  funext ω
  have := congrFun F2 ω
  simp only [Pi.mul_apply] at this
  simp only [Pi.div_apply]
  rw [eq_div_iff (hD22 ω), ← this, mul_comm]

/-- Cochrane (2023), Online Appendix eq. (1.64), p. 590: `B_0^{(1)}/P_1 =
s_1 + β ((B_1^{(2)} − B_0^{(2)})/B_1^{(2)}) E_1 s_2` (pull-out of the date-1 choice `B_1^{(2)}`). -/
theorem price_one (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (F2 : D 2 2 * x 2 = s 2)
    (F1 : D 1 1 * x 1 = s 1 + β • ((D 2 2 - D 1 2) * 𝔼.E 1 (x 2))) (hD22 : ∀ ω, D 2 2 ω ≠ 0) :
    D 1 1 * x 1 = s 1 + β • ((D 2 2 - D 1 2) / D 2 2 * 𝔼.E 1 (s 2)) := by
  rw [F1, ← F2, hpo 1 _ _ (hD.2 1 _)]
  congr 2
  funext ω
  simp only [Pi.mul_apply, Pi.div_apply]
  field_simp [hD22 ω]

/-- Cochrane (2023), Online Appendix eq. (1.64), p. 590: `B_0^{(1)} E_0(1/P_1) =
E_0[s_1 + β ((B_1^{(2)} − B_0^{(2)})/B_1^{(2)}) s_2]`. -/
theorem E_price_one (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (F2 : D 2 2 * x 2 = s 2)
    (F1 : D 1 1 * x 1 = s 1 + β • ((D 2 2 - D 1 2) * 𝔼.E 1 (x 2))) (hD22 : ∀ ω, D 2 2 ω ≠ 0) :
    D 1 1 * 𝔼.E 0 (x 1) = 𝔼.E 0 (s 1 + β • ((D 2 2 - D 1 2) / D 2 2 * s 2)) := by
  have hk : (D 2 2 - D 1 2) / D 2 2 * s 2 = (D 2 2 - D 1 2) * x 2 := by
    rw [← F2]
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply, Pi.sub_apply]
    field_simp [hD22 ω]
  have hk1 : 𝔼.E 1 (D 2 2 - D 1 2) = D 2 2 - D 1 2 := by
    rw [map_sub, hD.2 1, Predetermined.known_succ 𝔼 hD (Nat.zero_le 1)]
  rw [← hpo 0 _ _ (hD.2 0 _), F1, hk, map_add, map_add, map_smul, map_smul,
    ← hpo 1 _ _ hk1, 𝔼.tower (Nat.zero_le 1)]

/-- Cochrane (2023), Online Appendix eq. (1.65)/(1.66), pp. 590–591: the date-0 price level,
`B_{−1}^{(0)}/P_0 = s_0 + A₁ E_0[β s_1 + β² ((B_1^{(2)} − B_0^{(2)})/B_1^{(2)}) s_2]
  + E_0[β² ((B_0^{(2)} − B_{−1}^{(2)})/B_1^{(2)}) s_2]`, with `A₁ = (B_0^{(1)} −
B_{−1}^{(1)})/B_0^{(1)}`. -/
theorem price_zero (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (F2 : D 2 2 * x 2 = s 2)
    (F1 : D 1 1 * x 1 = s 1 + β • ((D 2 2 - D 1 2) * 𝔼.E 1 (x 2)))
    (F0 : D 0 0 * x 0 = s 0 + β • ((D 1 1 - D 0 1) * 𝔼.E 0 (x 1)) +
      β ^ 2 • ((D 1 2 - D 0 2) * 𝔼.E 0 (x 2)))
    (hD22 : ∀ ω, D 2 2 ω ≠ 0) (hD11 : ∀ ω, D 1 1 ω ≠ 0) :
    D 0 0 * x 0 = s 0 + (D 1 1 - D 0 1) / D 1 1 *
        𝔼.E 0 (β • s 1 + β ^ 2 • ((D 2 2 - D 1 2) / D 2 2 * s 2)) +
      𝔼.E 0 (β ^ 2 • ((D 1 2 - D 0 2) / D 2 2 * s 2)) := by
  have h1 := E_price_one 𝔼 hpo hD F2 F1 hD22
  have h2 : 𝔼.E 0 (β ^ 2 • ((D 1 2 - D 0 2) / D 2 2 * s 2)) =
      β ^ 2 • ((D 1 2 - D 0 2) * 𝔼.E 0 (x 2)) := by
    have hk : (D 1 2 - D 0 2) / D 2 2 * s 2 = (D 1 2 - D 0 2) * x 2 := by
      rw [← F2]
      funext ω
      simp only [Pi.mul_apply, Pi.div_apply, Pi.sub_apply]
      field_simp [hD22 ω]
    have hk0 : 𝔼.E 0 (D 1 2 - D 0 2) = D 1 2 - D 0 2 := by
      rw [map_sub, hD.2 0, hD.1]
    rw [hk, map_smul, hpo 0 _ _ hk0]
  rw [F0, h2]
  congr 1
  congr 1
  have hE : 𝔼.E 0 (β • s 1 + β ^ 2 • ((D 2 2 - D 1 2) / D 2 2 * s 2)) =
      β • 𝔼.E 0 (s 1 + β • ((D 2 2 - D 1 2) / D 2 2 * s 2)) := by
    rw [← map_smul, smul_add, smul_smul, ← pow_two]
  rw [hE, ← h1]
  funext ω
  simp only [Pi.mul_apply, Pi.smul_apply, Pi.div_apply, Pi.sub_apply, smul_eq_mul]
  field_simp [hD11 ω]

/-- Cochrane (2023), Online Appendix §A1.14.1, p. 590: with no long-term debt outstanding
(`B_{−1}^{(1)} = B_{−1}^{(2)} = 0`), `B_{−1}^{(0)}/P_0 = s_0 + E_0(β s_1 + β² s_2)`: the expected
sale `B_1^{(2)} − B_0^{(2)}` has no effect on `P_0`. -/
theorem no_outstanding_price_zero (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ}
    {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (F2 : D 2 2 * x 2 = s 2)
    (F1 : D 1 1 * x 1 = s 1 + β • ((D 2 2 - D 1 2) * 𝔼.E 1 (x 2)))
    (F0 : D 0 0 * x 0 = s 0 + β • ((D 1 1 - D 0 1) * 𝔼.E 0 (x 1)) +
      β ^ 2 • ((D 1 2 - D 0 2) * 𝔼.E 0 (x 2)))
    (hD22 : ∀ ω, D 2 2 ω ≠ 0) (hD11 : ∀ ω, D 1 1 ω ≠ 0) (h01 : D 0 1 = 0) (h02 : D 0 2 = 0) :
    D 0 0 * x 0 = s 0 + 𝔼.E 0 (β • s 1 + β ^ 2 • s 2) := by
  rw [price_zero 𝔼 hpo hD F2 F1 F0 hD22 hD11, h01, h02, add_assoc]
  congr 1
  have hA : (D 1 1 - 0) / D 1 1 = 1 := by
    funext ω; simp [div_self (hD11 ω)]
  rw [hA, one_mul, ← map_add]
  congr 1
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.div_apply, Pi.sub_apply,
    Pi.zero_apply, smul_eq_mul]
  field_simp [hD22 ω]
  ring

/-- Cochrane (2023), Online Appendix p. 589 (bullet): expected future sales enter symmetrically
with date-0 sales in `P_2`: two policies with the same total `B_1^{(2)}` give the same `P_2`. -/
theorem price_two_symm {D D' : ℕ → ℕ → Ω → ℝ} {x x' s : ℕ → Ω → ℝ} (F2 : D 2 2 * x 2 = s 2)
    (F2' : D' 2 2 * x' 2 = s 2) (hD22 : ∀ ω, D 2 2 ω ≠ 0) (htot : D 2 2 = D' 2 2) :
    x 2 = x' 2 := by
  funext ω
  have h1 := congrFun F2 ω
  have h2 := congrFun F2' ω
  simp only [Pi.mul_apply] at h1 h2
  rw [← htot] at h2
  exact mul_left_cancel₀ (hD22 ω) (h1.trans h2.symm)

/-- Cochrane (2023), Online Appendix p. 590 (bullets): with `P_0` fixed (as with no outstanding
long-term debt), expected future sales enter symmetrically with date-0 sales in the bond price
`Q_0^{(2)}`: the same total `B_1^{(2)}` gives the same `Q_0^{(2)}`, so a date-0 purchase can be
undone
by an expected future sale. -/
theorem bondPrice_two_symm {β : ℝ} {D D' : ℕ → ℕ → Ω → ℝ} {P x x' s : ℕ → Ω → ℝ}
    (F2 : D 2 2 * x 2 = s 2) (F2' : D' 2 2 * x' 2 = s 2) (hD22 : ∀ ω, D 2 2 ω ≠ 0)
    (htot : D 2 2 = D' 2 2) :
    bondPrice 𝔼 β P x 0 2 = bondPrice 𝔼 β P x' 0 2 := by
  simp only [bondPrice, zero_add, price_two_symm F2 F2' hD22 htot]

/-- Cochrane (2023), Online Appendix eq. (1.64), p. 590, with deterministic debt: writing
`F = B_1^{(2)} − B_0^{(2)}`, `B_0^{(1)} E_0(1/P_1) = E_0 s_1 + β (F/(B_0^{(2)} + F)) E_0 s_2`. -/
theorem x1_formula {β b1 b2 F : ℝ} {x s : ℕ → Ω → ℝ}
    (h : b1 • 𝔼.E 0 (x 1) = 𝔼.E 0 (s 1 + β • ((b2 + F - b2) / (b2 + F)) • s 2)) :
    b1 • 𝔼.E 0 (x 1) = 𝔼.E 0 (s 1) + (β * (F / (b2 + F))) • 𝔼.E 0 (s 2) := by
  rw [h, map_add, map_smul, map_smul, smul_smul]
  congr 2
  rw [add_sub_cancel_left]

/-- Cochrane (2023), Online Appendix p. 591 (bullet): if time-2 debt has been sold at date 0
(`B_0^{(2)} > 0`), expected future sales `F` raise `B_0^{(1)} E_0(1/P_1)` (lower the expected
`P_1`),
and hence raise the bond price `Q_0^{(1)} = β P_0 E_0(1/P_1)` when `P_0` is fixed:
`F ↦ F/(B_0^{(2)} + F)` is strictly increasing on `F > −B_0^{(2)}`. -/
theorem future_sales_raise_Q1 {b2 F F' : ℝ} (hb2 : 0 < b2) (hF : -b2 < F) (hFF' : F < F') :
    F / (b2 + F) < F' / (b2 + F') := by
  have h1 : 0 < b2 + F := by linarith
  have h2 : 0 < b2 + F' := by linarith
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith

/-- Cochrane (2023), Online Appendix §A1.14.2, p. 591 (bullet): expected future sales have only an
interaction effect: with no date-0 sales (`B_0^{(1)} = B_{−1}^{(1)}`, `B_0^{(2)} = B_{−1}^{(2)}`),
`B_{−1}^{(0)}/P_0 = s_0` whatever the date-1 sale. -/
theorem no_time0_sales (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (F2 : D 2 2 * x 2 = s 2)
    (F1 : D 1 1 * x 1 = s 1 + β • ((D 2 2 - D 1 2) * 𝔼.E 1 (x 2)))
    (F0 : D 0 0 * x 0 = s 0 + β • ((D 1 1 - D 0 1) * 𝔼.E 0 (x 1)) +
      β ^ 2 • ((D 1 2 - D 0 2) * 𝔼.E 0 (x 2)))
    (hD22 : ∀ ω, D 2 2 ω ≠ 0) (hD11 : ∀ ω, D 1 1 ω ≠ 0) (h1 : D 1 1 = D 0 1)
    (h2 : D 1 2 = D 0 2) : D 0 0 * x 0 = s 0 := by
  have z1 : ∀ f g : Ω → ℝ, (0 : Ω → ℝ) / f * g = 0 := fun f g => by funext ω; simp
  rw [price_zero 𝔼 hpo hD F2 F1 F0 hD22 hD11, h1, h2]
  simp only [sub_self, z1, map_zero, smul_zero, add_zero]

/-- Cochrane (2023), Online Appendix eq. (1.67), p. 592: with no date-0 sale of time-2 debt
(`B_0^{(2)} = B_{−1}^{(2)}`), `B_{−1}^{(0)}/P_0 = s_0 + A₁ E_0[β s_1 + β² ((B_1^{(2)} −
B_0^{(2)})/B_1^{(2)})
s_2]`. -/
theorem price_zero_no_sale_two (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ}
    {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (F2 : D 2 2 * x 2 = s 2)
    (F1 : D 1 1 * x 1 = s 1 + β • ((D 2 2 - D 1 2) * 𝔼.E 1 (x 2)))
    (F0 : D 0 0 * x 0 = s 0 + β • ((D 1 1 - D 0 1) * 𝔼.E 0 (x 1)) +
      β ^ 2 • ((D 1 2 - D 0 2) * 𝔼.E 0 (x 2)))
    (hD22 : ∀ ω, D 2 2 ω ≠ 0) (hD11 : ∀ ω, D 1 1 ω ≠ 0) (h2 : D 1 2 = D 0 2) :
    D 0 0 * x 0 = s 0 + (D 1 1 - D 0 1) / D 1 1 *
      𝔼.E 0 (β • s 1 + β ^ 2 • ((D 2 2 - D 1 2) / D 2 2 * s 2)) := by
  have z1 : ∀ f g : Ω → ℝ, (0 : Ω → ℝ) / f * g = 0 := fun f g => by funext ω; simp
  rw [price_zero 𝔼 hpo hD F2 F1 F0 hD22 hD11, h2]
  simp only [sub_self, z1, smul_zero, map_zero, add_zero]

/-- Cochrane (2023), Online Appendix eq. (1.68), p. 592: with no date-0 sale of time-1 debt
(`B_0^{(1)} = B_{−1}^{(1)}`), `B_{−1}^{(0)}/P_0 = s_0 + E_0[β² ((B_0^{(2)} − B_{−1}^{(2)}) /
(B_{−1}^{(2)} + (B_0^{(2)} − B_{−1}^{(2)}) + (B_1^{(2)} − B_0^{(2)}))) s_2]`: dilution is relative
to all
claims, including expected future sales. -/
theorem price_zero_no_sale_one (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ}
    {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (F2 : D 2 2 * x 2 = s 2)
    (F1 : D 1 1 * x 1 = s 1 + β • ((D 2 2 - D 1 2) * 𝔼.E 1 (x 2)))
    (F0 : D 0 0 * x 0 = s 0 + β • ((D 1 1 - D 0 1) * 𝔼.E 0 (x 1)) +
      β ^ 2 • ((D 1 2 - D 0 2) * 𝔼.E 0 (x 2)))
    (hD22 : ∀ ω, D 2 2 ω ≠ 0) (hD11 : ∀ ω, D 1 1 ω ≠ 0) (h1 : D 1 1 = D 0 1) :
    D 0 0 * x 0 = s 0 + 𝔼.E 0 (β ^ 2 • ((D 1 2 - D 0 2) /
      (D 0 2 + (D 1 2 - D 0 2) + (D 2 2 - D 1 2)) * s 2)) := by
  have z1 : ∀ f g : Ω → ℝ, (0 : Ω → ℝ) / f * g = 0 := fun f g => by funext ω; simp
  rw [price_zero 𝔼 hpo hD F2 F1 F0 hD22 hD11, h1,
    show D 0 2 + (D 1 2 - D 0 2) + (D 2 2 - D 1 2) = D 2 2 by ring]
  simp only [sub_self, z1, add_zero]

/-! ### The sign of the effect of expected future sales on `P_0` (deterministic debt) -/

/-- Cochrane (2023), Online Appendix eq. (1.66), p. 591, with deterministic debt and the expected
sale `F = B_1^{(2)} − B_0^{(2)}` as a parameter: `B_{−1}^{(0)}/P_0 = s_0 + A₁ β e_1 +
β² e_2 (A₁ F + B_0^{(2)} − B_{−1}^{(2)})/(B_0^{(2)} + F)`, with `e_k = E_0 s_k`. -/
noncomputable def x0Fun (s0 e1 e2 β A1 b2 d2 D00 F : ℝ) : ℝ :=
  (s0 + A1 * β * e1 + β ^ 2 * e2 * ((A1 * F + (b2 - d2)) / (b2 + F))) / D00

/-- Cochrane (2023), Online Appendix eq. (1.66), p. 591: the closed form agrees with (1.65) term by
term: `A₁ β² (F/B_1^{(2)}) e_2 + β² ((B_0^{(2)} − B_{−1}^{(2)})/B_1^{(2)}) e_2`. -/
theorem x0_closed {s0 e1 e2 β A1 b2 d2 D00 F : ℝ} (hD00 : D00 ≠ 0) (hb : b2 + F ≠ 0) :
    x0Fun s0 e1 e2 β A1 b2 d2 D00 F * D00 =
      s0 + A1 * (β * e1 + β ^ 2 * (F / (b2 + F)) * e2) + β ^ 2 * ((b2 - d2) / (b2 + F)) * e2 := by
  rw [x0Fun, div_mul_cancel₀ _ hD00]
  field_simp
  ring

/-- Cochrane (2023), Online Appendix p. 592: the derivative of `1/P_0` with respect to the expected
sale, `β² e_2 B_0^{(2)} (A₁ − A₂)/((B_0^{(2)} + F)² B_{−1}^{(0)})` with
`A₂ = (B_0^{(2)} − B_{−1}^{(2)})/B_0^{(2)}`. -/
theorem hasDerivAt_x0 (s0 e1 e2 β A1 b2 d2 D00 F : ℝ) (hb2 : b2 ≠ 0) (hb : b2 + F ≠ 0) :
    HasDerivAt (fun G => x0Fun s0 e1 e2 β A1 b2 d2 D00 G)
      (β ^ 2 * e2 * b2 * (A1 - (b2 - d2) / b2) / ((b2 + F) ^ 2 * D00)) F := by
  have hq : HasDerivAt (fun G => (A1 * G + (b2 - d2)) / (b2 + G))
      ((A1 * (b2 + F) - (A1 * F + (b2 - d2)) * 1) / (b2 + F) ^ 2) F := by
    have h1 : HasDerivAt (fun G => A1 * G + (b2 - d2)) A1 F := by
      simpa using ((hasDerivAt_id F).const_mul A1).add_const (b2 - d2)
    have h2 : HasDerivAt (fun G => b2 + G) 1 F := by
      simpa using (hasDerivAt_id F).const_add b2
    exact h1.div h2 hb
  have := ((hq.const_mul (β ^ 2 * e2)).const_add (s0 + A1 * β * e1)).div_const D00
  have hnum : A1 * (b2 + F) - (A1 * F + (b2 - d2)) * 1 = b2 * (A1 - (b2 - d2) / b2) := by
    field_simp
    ring
  rw [hnum] at this
  unfold x0Fun
  convert this using 1
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- Cochrane (2023), Online Appendix p. 592 (bullet): **if the government sells proportionally
more time-1 than time-2 debt at date 0 (`A₁ > A₂`), expected future sales lower `P_0`:** with
`E_0 s_2 > 0`, `B_0^{(2)} > 0`, `B_{−1}^{(0)} > 0`, `1/P_0` is strictly increasing in `F` on
`F > −B_0^{(2)}`. -/
theorem x0_strictMono {s0 e1 e2 β A1 b2 d2 D00 F F' : ℝ} (he2 : 0 < e2) (hβ : β ≠ 0)
    (hb2 : 0 < b2) (hD00 : 0 < D00) (hA : (b2 - d2) / b2 < A1) (hF : -b2 < F) (hFF' : F < F') :
    x0Fun s0 e1 e2 β A1 b2 d2 D00 F < x0Fun s0 e1 e2 β A1 b2 d2 D00 F' := by
  unfold x0Fun
  apply div_lt_div_of_pos_right _ hD00
  have h1 : 0 < b2 + F := by linarith
  have h2 : 0 < b2 + F' := by linarith
  have hβ2 : 0 < β ^ 2 * e2 := mul_pos (lt_of_le_of_ne (sq_nonneg β) (pow_ne_zero 2 hβ).symm) he2
  have hA' : b2 - d2 < A1 * b2 := by rwa [div_lt_iff₀ hb2] at hA
  have : (A1 * F + (b2 - d2)) / (b2 + F) < (A1 * F' + (b2 - d2)) / (b2 + F') := by
    rw [div_lt_div_iff₀ h1 h2]
    nlinarith
  nlinarith

/-- Cochrane (2023), Online Appendix p. 592: conversely, if `A₁ < A₂`, expected future sales raise
`P_0`: `1/P_0` is strictly decreasing in `F` on `F > −B_0^{(2)}`. -/
theorem x0_strictAnti {s0 e1 e2 β A1 b2 d2 D00 F F' : ℝ} (he2 : 0 < e2) (hβ : β ≠ 0)
    (hb2 : 0 < b2) (hD00 : 0 < D00) (hA : A1 < (b2 - d2) / b2) (hF : -b2 < F) (hFF' : F < F') :
    x0Fun s0 e1 e2 β A1 b2 d2 D00 F' < x0Fun s0 e1 e2 β A1 b2 d2 D00 F := by
  unfold x0Fun
  apply div_lt_div_of_pos_right _ hD00
  have h1 : 0 < b2 + F := by linarith
  have h2 : 0 < b2 + F' := by linarith
  have hβ2 : 0 < β ^ 2 * e2 := mul_pos (lt_of_le_of_ne (sq_nonneg β) (pow_ne_zero 2 hβ).symm) he2
  have hA' : A1 * b2 < b2 - d2 := by rwa [lt_div_iff₀ hb2] at hA
  have : (A1 * F' + (b2 - d2)) / (b2 + F') < (A1 * F + (b2 - d2)) / (b2 + F) := by
    rw [div_lt_div_iff₀ h2 h1]
    nlinarith
  nlinarith

/-- Cochrane (2023), Online Appendix p. 592: when the two fractions are equal (`A₁ = A₂`), the last
two terms offset exactly and expected future sales have no effect on `P_0`. -/
theorem x0_const {s0 e1 e2 β A1 b2 d2 D00 F : ℝ} (hb2 : b2 ≠ 0) (hb : b2 + F ≠ 0)
    (hA : A1 = (b2 - d2) / b2) :
    x0Fun s0 e1 e2 β A1 b2 d2 D00 F = x0Fun s0 e1 e2 β A1 b2 d2 D00 0 := by
  unfold x0Fun
  congr 3
  rw [hA, add_zero, mul_zero, zero_add]
  field_simp
  ring

end Cochrane.LongTermDebtDynamics.FutureSales
