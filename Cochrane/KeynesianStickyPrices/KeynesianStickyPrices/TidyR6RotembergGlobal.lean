/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR6RotembergPC

/-!
# The Rotemberg first-order condition is not globally sufficient

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.1, p. 118 ("The Phillips
curve (5.2) comes from the first-order condition for monopolistically-competitive price setters,
facing costs of changing prices"), and eq. (17.17), p. 407.

TidyR6Rotemberg proved that the first-order condition is necessary over all plans and sufficient
among the plans in the concavity region `rotRegion`. This module decides the remaining question,
global sufficiency, **negatively**, with a stationary symmetric equilibrium of the price setter's
problem in deep deflation.

## The counterexample

`β = 1/2`, `ε = 2`, `ϕ = 0` (so `η = ε(1 + ϕ) = 2`), `φ = 4`, `γ = 1`, steady state `Ȳ = 1/2`
(`εȲ^{1+ϕ} = (ε − 1)Ȳ^{1−γ}`, `cex_ss`), constant output gap `x = log(5/8)` and constant
inflation `π = −2 log 2` (prices fall by three quarters every period). The price setter's data are
`(A, B, π) = (1, 5/16, −2 log 2)` (`cexData`, `cexData_eq_yeoData`: exactly the symmetric
equilibrium data `TidyR6RotembergPC.yeoData`).

* `cex_foc`: charging the aggregate price (`q ≡ 0`) satisfies the first-order condition at every
  date, on every probability space (equivalently, the exact nonlinear Phillips curve holds,
  `cex_nonlinPC`).
* `cex_gain`: raising the date-0 price by `log 2` (doubling it) and following the aggregate price
  afterwards raises the value by exactly `5/32`.
* `cex_not_optimal`, `cex_not_optimal_u`: so `q ≡ 0` is **not optimal**, among all plans or among
  uniformly bounded plans, although it satisfies the first-order condition everywhere.
* `cex_outside_region`: `q ≡ 0` lies outside the concavity region (the price is cut by more than
  half every period), consistently with `TidyR6Rotemberg.optimal_iff_foc_region`, which is
  therefore the correct (corrected) statement: the first-order condition is sufficient among the
  plans of the concavity region, not among all plans.

`TidyR6RotembergLocal` shows the first-order condition is nevertheless sufficient among all
plans near the steady state.
-/

namespace Cochrane.KeynesianStickyPrices.TidyR6RotembergGlobal

open MeasureTheory ProbabilityTheory Filter Topology TidyR5ExpectationsMeasure
open TidyR6HouseholdMeasure TidyR6PriceSetting TidyR6Rotemberg TidyR6RotembergPC

/-- Cochrane (2023), p. 118: the counterexample's data `(A, B, π) = (1, 5/16, −2 log 2)`. -/
noncomputable def cexV : ℝ × ℝ × ℝ := (1, 5 / 16, -(2 * Real.log 2))

/-- Cochrane (2023), p. 118: the counterexample's data at every date and state. -/
noncomputable def cexData {Ω : Type*} : ℕ → Ω → ℝ × ℝ × ℝ := fun _ _ => cexV

/-- Cochrane (2023), p. 118: `e^{log 2} = 2`. -/
theorem exp_L : Real.exp (Real.log 2) = 2 := Real.exp_log two_pos

/-- Cochrane (2023), p. 118: `e^{−k log 2} = 2^{−k}` for `k = 1, 2, 3`. -/
theorem exp_negL : Real.exp (-Real.log 2) = 1 / 2 ∧ Real.exp (-(2 * Real.log 2)) = 1 / 4 ∧
    Real.exp (-(3 * Real.log 2)) = 1 / 8 := by
  have h2 : Real.exp (2 * Real.log 2) = 4 := by
    rw [two_mul, Real.exp_add, exp_L]; norm_num
  have h3 : Real.exp (3 * Real.log 2) = 8 := by
    rw [show 3 * Real.log 2 = Real.log 2 + 2 * Real.log 2 by ring, Real.exp_add, exp_L, h2]
    norm_num
  refine ⟨?_, ?_, ?_⟩ <;> rw [Real.exp_neg]
  · rw [exp_L]; norm_num
  · rw [h2]; norm_num
  · rw [h3]; norm_num

/-- Cochrane (2023), p. 118: the steady state `Ȳ = 1/2` for `ε = 2`, `ϕ = 0`, `γ = 1`. -/
theorem cex_ss : (2 : ℝ) * (1 / 2 : ℝ) ^ ((1 : ℝ) + 0) = (2 - 1) * (1 / 2 : ℝ) ^ ((1 : ℝ) - 1) := by
  norm_num

/-- Cochrane (2023), p. 118: the counterexample's data are the symmetric-equilibrium data with
`γ = 1`, `ϕ = 0`, `Ȳ = 1/2`, `x = log(5/8)`, `π = −2 log 2`. -/
theorem cexData_eq_yeoData {Ω : Type*} (t : ℕ) (ω : Ω) :
    yeoData 1 0 (1 / 2) (fun _ _ => Real.log (5 / 8)) (fun _ _ => -(2 * Real.log 2)) t ω =
      cexData t ω := by
  simp only [yeoData, cexData, cexV, sub_self, zero_mul, Real.exp_zero, mul_one, add_zero,
    Real.rpow_zero, one_mul, Real.rpow_one, div_one]
  rw [Real.exp_log (by norm_num)]
  norm_num

/-- Cochrane (2023), p. 118: the payoff values used in the counterexample. -/
theorem cex_values :
    rotPay 2 2 4 0 0 cexV = -7 / 16 ∧ rotPay 2 2 4 (0 + Real.log 2 * 1) 0 cexV = -5 / 64 ∧
      rotPay 2 2 4 0 (0 + Real.log 2 * 1) cexV = -27 / 32 := by
  obtain ⟨e1, e2, e3⟩ := exp_negL
  refine ⟨?_, ?_, ?_⟩ <;> simp only [rotPay, cexV]
  · rw [show (1 - (2 : ℝ)) * 0 = 0 by ring, show -((2 : ℝ) * 0) = 0 by ring,
      show (0 : ℝ) - 0 + -(2 * Real.log 2) = -(2 * Real.log 2) by ring, e2, Real.exp_zero]
    norm_num
  · rw [show (1 - (2 : ℝ)) * (0 + Real.log 2 * 1) = -Real.log 2 by ring,
      show -((2 : ℝ) * (0 + Real.log 2 * 1)) = -(2 * Real.log 2) by ring,
      show 0 + Real.log 2 * 1 - 0 + -(2 * Real.log 2) = -Real.log 2 by ring, e1, e2]
    norm_num
  · rw [show (1 - (2 : ℝ)) * 0 = 0 by ring, show -((2 : ℝ) * 0) = 0 by ring,
      show (0 : ℝ) - (0 + Real.log 2 * 1) + -(2 * Real.log 2) = -(3 * Real.log 2) by ring, e3,
      Real.exp_zero]
    norm_num

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-- Cochrane (2023), p. 118 and eq. (17.17), p. 407: in the counterexample, charging the
aggregate price satisfies the price setter's first-order condition at every date. -/
theorem cex_foc (t : ℕ) :
    FOC S (1 / 2) (rotD1 2 2 4) (rotD2 4) cexData (fun _ => 0) zeroPlan t := by
  obtain ⟨-, e2, -⟩ := exp_negL
  refine Eventually.of_forall fun ω => ?_
  rw [lag_zeroPlan]
  have hc : (fun ω => rotD2 4 (zeroPlan (t + 1) ω) (zeroPlan t ω) (cexData (t + 1) ω)) =
      fun _ : Ω => rotD2 4 0 0 cexV := rfl
  rw [hc, S.E_const]
  simp only [rotD1, rotD2, zeroPlan, cexData, cexV]
  rw [show (1 - (2 : ℝ)) * 0 = 0 by ring, show -((2 : ℝ) * 0) = 0 by ring,
    show (0 : ℝ) - 0 + -(2 * Real.log 2) = -(2 * Real.log 2) by ring, e2, Real.exp_zero]
  norm_num

/-- Cochrane (2023), eq. (17.17), p. 407: in the counterexample the exact nonlinear Phillips curve
holds at every date (the symmetric equilibrium of the price setters). -/
theorem cex_nonlinPC (t : ℕ) :
    NonlinPC S (1 / 2) (kappaT 2 4 1 (1 / 2)) 1 0 (fun _ _ => Real.log (5 / 8))
      (fun _ _ => -(2 * Real.log 2)) t := by
  have hd : yeoData (Ω := Ω) 1 0 (1 / 2) (fun _ _ => Real.log (5 / 8))
      (fun _ _ => -(2 * Real.log 2)) = cexData := by
    funext t ω
    exact cexData_eq_yeoData t ω
  have h := (symFOC_iff_nonlinPC (S := S) (β := 1 / 2) (ε := 2) (φ := 4) (γ := 1) (ϕ := 0)
    (Ybar := 1 / 2) (x := fun _ _ => Real.log (5 / 8)) (π := fun _ _ => -(2 * Real.log 2))
    (t := t) (by norm_num) (by norm_num) cex_ss).1
  rw [show (2 : ℝ) * (1 + 0) = 2 by norm_num, hd] at h
  exact h (cex_foc t)

/-- Cochrane (2023), p. 118: charging the aggregate price is admissible in the counterexample. -/
theorem cex_admissible : Admissible S (1 / 2) (rotPay 2 2 4) cexData (fun _ => 0) zeroPlan :=
  admissible_zero (by norm_num) (by norm_num)
    ⟨fun _ => stronglyMeasurable_const, fun _ => ⟨‖cexV‖, Eventually.of_forall fun _ => le_rfl⟩⟩
    ⟨‖cexV‖, fun _ => Eventually.of_forall fun _ => le_rfl⟩

/-- Cochrane (2023), p. 118: doubling the date-0 price and following the aggregate price from
date 1 on raises the value by `5/32`. -/
theorem cex_gain :
    value S (1 / 2) (rotPay 2 2 4) cexData (fun _ => 0)
        (perturb zeroPlan (fun _ => 1) 0 (Real.log 2)) =
      value S (1 / 2) (rotPay 2 2 4) cexData (fun _ => 0) zeroPlan + 5 / 32 := by
  obtain ⟨v0, v1, v2⟩ := cex_values
  rw [value_perturb (by norm_num) cex_admissible, pay_perturb_t, pay_perturb_succ]
  simp only [pay, zeroPlan, cexData, lag, v0, v1, v2, integral_const,
    probReal_univ, one_smul]
  norm_num

/-- Cochrane (2023), p. 118, **counterexample to global sufficiency**: in the counterexample,
charging the aggregate price satisfies the first-order condition at every date (`cex_foc`) but is
not optimal among all plans. -/
theorem cex_not_optimal :
    ¬ OptimalIn S (Plan S) (1 / 2) (rotPay 2 2 4) cexData (fun _ => 0) zeroPlan := by
  intro hopt
  have hdata : DataReg S (cexData : ℕ → Ω → ℝ × ℝ × ℝ) :=
    ⟨fun _ => stronglyMeasurable_const, fun _ => ⟨‖cexV‖, Eventually.of_forall fun _ => le_rfl⟩⟩
  have hz : StronglyMeasurable[S.𝓕 0] (fun _ : Ω => (1 : ℝ)) := stronglyMeasurable_const
  have h := hopt.2.2 _ (plan_perturb hopt.1 hz (BddAt.const 1) (Real.log 2))
    (admissible_perturb (rot_smooth 2 2 4).2.2.1 hdata stronglyMeasurable_const (BddAt.const 0)
      hopt.1 hopt.2.1 hz (BddAt.const 1) (Real.log 2))
  rw [cex_gain] at h
  linarith

/-- Cochrane (2023), p. 118: nor is it optimal among uniformly bounded plans. -/
theorem cex_not_optimal_u :
    ¬ OptimalIn S (UPlan S) (1 / 2) (rotPay 2 2 4) cexData (fun _ => 0) zeroPlan := by
  intro hopt
  have hdata : DataReg S (cexData : ℕ → Ω → ℝ × ℝ × ℝ) :=
    ⟨fun _ => stronglyMeasurable_const, fun _ => ⟨‖cexV‖, Eventually.of_forall fun _ => le_rfl⟩⟩
  have hz : StronglyMeasurable[S.𝓕 0] (fun _ : Ω => (1 : ℝ)) := stronglyMeasurable_const
  have h := hopt.2.2 _ (uplan_perturb hopt.1 hz (BddAt.const 1) (Real.log 2))
    (admissible_perturb (rot_smooth 2 2 4).2.2.1 hdata stronglyMeasurable_const (BddAt.const 0)
      hopt.1.1 hopt.2.1 hz (BddAt.const 1) (Real.log 2))
  rw [cex_gain] at h
  linarith

/-- Cochrane (2023), p. 118: in the counterexample, charging the aggregate price is outside the
concavity region (`e^{q_t − q_{t−1} + π_t} = 1/4 < 1/2`), so the region theorem
`TidyR6Rotemberg.optimal_iff_foc_region` does not apply to it. -/
theorem cex_outside_region (a : ℝ) : (a, a) ∉ rotRegion 2 2 cexV := by
  rintro ⟨-, h⟩
  have e : a - a + cexV.2.2 = -(2 * Real.log 2) := by simp [cexV]
  have h' : (1 : ℝ) / 2 ≤ Real.exp (a - a + cexV.2.2) := h
  rw [e, exp_negL.2.1] at h'
  norm_num at h'

end Cochrane.KeynesianStickyPrices.TidyR6RotembergGlobal
