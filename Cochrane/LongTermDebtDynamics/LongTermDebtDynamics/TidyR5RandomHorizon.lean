/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR5RandomGuidance

/-!
# Horizon comparisons for state-contingent forward guidance

Cochrane (2023), §7.1, p. 213 (first bullet): guidance has less effect than the same immediate
rise, and the effect falls with the horizon (`ForwardGuidance.priceLevel_mono`,
`ForwardGuidance.priceLevel_immediate_le`).

With a state-contingent announced rate path both comparisons fail.

* `cg2_fisher`, `cg2_presentValue`: an equilibrium (Fisher relations at every date and the date-0
  valuation (7.3), as in `TidyR5RandomGuidance`) for the rate path `cgRate2`. That path is
  `TidyR5RandomGuidance.cgRate` delayed by one period, with `r` inserted at date 0
  (`cgRate2_delay`).
* `cg_horizon_counterexample`: same debt and surpluses; the earlier announcement has the
  *higher* price level, `P_0 = 7/48 > 1/8`.
  - Read the shape as "`ρ` at the first date, `r` afterwards". Then horizon 1 versus horizon 2
    contradicts monotonicity in the horizon.
  - Read the shape as "`r`, then `ρ`, then `r`". Then the immediate rise (horizon 0) versus
    horizon 1 contradicts "the immediate rise has the largest effect".
* `cg_cov_zero`: the date-0 covariance term of `TidyR5RandomGuidance.bondPrice_cov_rate` is zero
  in this example. So rates uncorrelated with later bond prices do not rescue the comparisons; the
  failure is the convexity (Jensen) effect `E_0(1+i_1)^{-1} > (1 + E_0 i_1)^{-1}`.

The surviving version is the one for rate paths known at date 0:
`TidyR5GuidanceUncertainty.stoch_fg_mono`, of which the immediate-rise comparison is the case
`T = 0`.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR5RandomHorizon

open Filter Topology MaturityStructure TidyR5RandomGuidance

/-- Cochrane (2023), §7.1 (counterexample): the rate path of `cgRate` delayed one period: `2`
after heads and `1/5` after tails at date 2, `r = 1` at every other date. -/
noncomputable def cgRate2 : ℕ → Bool × Bool → ℝ :=
  fun t ω => if t = 2 then (if ω.1 then 2 else 1 / 5) else 1

/-- Cochrane (2023), §7.1 (counterexample): `cgRate2` is `cgRate` delayed by one period, with the
unchanged rate `r = 1` at date 0. -/
theorem cgRate2_delay (t : ℕ) (ω : Bool × Bool) :
    cgRate2 0 ω = 1 ∧ cgRate2 (t + 1) ω = cgRate t ω := by
  refine ⟨by simp [cgRate2], ?_⟩
  simp only [cgRate2, cgRate, show (t + 1 = 2) = (t = 1) by simp]

/-- Cochrane (2023), §7.1 (counterexample): `1/P_t` for the delayed path: `8` up to date 2, then
`16/3` after heads and `40/3` after tails. -/
noncomputable def cgX2 : ℕ → Bool × Bool → ℝ :=
  fun t ω => if t ≤ 2 then 8 else (if ω.1 then 16 / 3 else 40 / 3)

/-- Cochrane (2023), §7.1 (counterexample): the price level `P_t = 1/cgX2`. -/
noncomputable def cgP2 : ℕ → Bool × Bool → ℝ := fun t ω => (cgX2 t ω)⁻¹

/-- Cochrane (2023), §7.1 (counterexample): the delayed path implements the rates `cgRate2`
(`β = 1/2`). -/
theorem cg2_fisher : RFisher ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ cgP2 cgX2 cgRate2 := by
  intro t
  rcases Nat.lt_or_ge t 2 with h2 | h2
  · have : cgP2 t * cgX2 (t + 1) = fun _ => 1 := by
      funext ω
      simp [cgP2, cgX2, show t ≤ 2 by omega, show t + 1 ≤ 2 by omega]
    simp only [bondPrice, pow_one, this, ExpectationsFiniteTree.coinSystem.const]
    funext ω; simp [cgRate2, show t ≠ 2 by omega]
  · rcases Nat.lt_or_ge t 3 with h3 | h3
    · obtain rfl : t = 2 := by omega
      have hk : ExpectationsFiniteTree.coinSystem.E 2 (cgP2 2 * cgX2 (2 + 1)) =
          cgP2 2 * cgX2 (2 + 1) :=
        coin_known (fun ω ω' h => by simp only [Pi.mul_apply, cgP2, cgX2, h]) (by norm_num)
      simp only [bondPrice, pow_one, hk]
      funext ω
      rcases ω with ⟨_ | _, _⟩ <;> simp [cgP2, cgX2, cgRate2] <;> norm_num
    · have : cgP2 t * cgX2 (t + 1) = fun _ => 1 := by
        funext ω
        simp only [Pi.mul_apply, cgP2, cgX2, show ¬ (t ≤ 2) by omega,
          show ¬ (t + 1 ≤ 2) by omega, ↓reduceIte]
        split_ifs <;> norm_num
      simp only [bondPrice, pow_one, this, ExpectationsFiniteTree.coinSystem.const]
      funext ω
      simp [cgRate2, show t ≠ 2 by omega]

/-- Cochrane (2023), §7.1 (counterexample): the delayed path satisfies the date-0 valuation
equation (7.3) with debt `B_{−1}^{(2)} = 1` and surpluses `s_t = 1`: `β² · 8 = 2`. -/
theorem cg2_presentValue : PresentValue ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹
    (fun _ j _ => cgB j) cgX2 (fun _ _ => 1) 0 := by
  intro ω
  refine ⟨(cg_pv ω).summable, ?_⟩
  rw [pvSurplus, (cg_pv ω).tsum_eq]
  have h := hasSum_single (f := fun j => debtTerm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹
    (fun _ j _ => cgB j) cgX2 0 j ω) 2 fun j hj => by simp [debtTerm, cgB, hj]
  convert h using 1
  simp only [debtTerm, cgB, ↓reduceIte, one_mul, zero_add]
  rw [show cgX2 2 = fun _ => (8 : ℝ) from funext fun _ => by simp [cgX2],
    ExpectationsFiniteTree.coinSystem.const]
  norm_num

/-- Cochrane (2023), §7.1, p. 213 (first bullet), **counterexample for state-contingent guidance**:
the path `cgRate` and its one-period delay `cgRate2` (same debt `B_{−1}^{(2)} = 1`, surpluses
`s_t = 1`, `r = 1`) both have equilibria (`cg_fisher`, `cg_presentValue`, `cg2_fisher`,
`cg2_presentValue`), and the earlier announcement gives the higher price level,
`P_0 = 7/48 > 1/8`. This contradicts both monotonicity in the horizon and the immediate-rise
comparison. -/
theorem cg_horizon_counterexample (ω : Bool × Bool) :
    cgP 0 ω = 7 / 48 ∧ cgP2 0 ω = 1 / 8 ∧ cgP2 0 ω < cgP 0 ω := by
  refine ⟨by simp [cgP, cgX], by simp [cgP2, cgX2], ?_⟩
  simp [cgP, cgX, cgP2, cgX2]
  norm_num

/-- Cochrane (2023), §7.1 (counterexample): the covariance term
`Cov_0(β P_0/P_1, Q_1^{(2)})` of `TidyR5RandomGuidance.bondPrice_cov_rate` vanishes in the
counterexample (`P_0/P_1 = 1`), so the failure is not a correlation effect. -/
theorem cg_cov_zero :
    condCov ExpectationsFiniteTree.coinSystem 0 ((1 + 1 : ℝ)⁻¹ • (cgP 0 * cgX (0 + 1)))
      (bondPrice ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ cgP cgX (0 + 1) 1) = 0 := by
  have hc : (1 + 1 : ℝ)⁻¹ • (cgP 0 * cgX (0 + 1)) = fun _ => (1 + 1 : ℝ)⁻¹ := by
    funext ω; simp [cgP, cgX]
  set b := bondPrice ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ cgP cgX (0 + 1) 1
  have hm : (fun _ => (1 + 1 : ℝ)⁻¹) * b = (1 + 1 : ℝ)⁻¹ • b := by
    funext ω; simp
  rw [condCov, hc, hm, map_smul, ExpectationsFiniteTree.coinSystem.const]
  funext ω
  simp

end Cochrane.LongTermDebtDynamics.TidyR5RandomHorizon
