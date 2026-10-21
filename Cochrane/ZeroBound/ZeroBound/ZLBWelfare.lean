/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Welfare at the zero-bound steady state

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.3, pp. 484–485.

The book: "The zero-bound left equilibrium `Π_L` in Figure 16.2 has greater welfare than the
desired right-hand equilibrium `Π*`. Less inflation means that firms are closer to their optimal
prices, and relative prices are less distorted." We make this precise in the Calvo model with
constant (log) inflation `π`.

* The stationary Calvo age distribution: a fraction `(1−α)αʲ` of firms last reset their price
  `j` periods ago; their log relative price is `p* − jπ`, with the reset price `p*` fixed by
  the (log-linear) price-index normalisation `∑ (1−α)αʲ p_j = 0`, i.e. `p* = απ/(1−α)`
  (`relPrice_mean`).
* **Exact** relative-price dispersion (cross-sectional variance of log prices)
  `dispersion_eq`: `∑ (1−α)αʲ p_j² = απ²/(1−α)²`, the steady state of Woodford's
  second-order recursion `Δ = αΔ + (α/(1−α))π²` (`dispersion_fixed_point`); and the average
  squared distance from the optimal (reset) price, `resetGap_eq`: `α(1+α)π²/(1−α)²`.
* Both are increasing in `|π|`: `dispersion_lt_iff`, `resetGap_lt_iff`; zero iff `π = 0`
  (`dispersion_eq_zero_iff`, all firms at the optimal price).
* The steady-state quadratic welfare loss `π² + λx̄²` with the steady-state Phillips curve
  `x̄ = (1−β)π/κ` (`ss_phillips_iff`) is also `∝ π²`: `ssLoss_lt_iff`.
* The zero-bound steady state has `Π_L = β` (`zlb_steady_state`, from `Π' = β(1+i)` with
  `i = 0`). **The book's claim holds iff the real rate is below the inflation target**:
  `zlb_better_iff` (`1 < βΠ*`), `zlb_worse_iff` (`βΠ* < 1`); survey **E9** is confirmed as a
  missing qualifier: `e9_counterexample` (`β = 0.95`, `Π* = 1.02`); the book's own numbers
  (`r = 1%`, `Π* = 2%`) satisfy it (`book_calibration`), as does every `Π_L ∈ [1, Π*)`
  (`zlb_better_of_one_le`).
-/

namespace Cochrane.ZeroBound.ZLBWelfare

open Filter Topology

/-! ## The stationary Calvo distribution -/

/-- Cochrane (2023), §20.3, p. 485 (Calvo pricing):
the stationary share of firms whose price was last reset `j` periods ago, `(1−α)αʲ`. -/
noncomputable def calvoW (α : ℝ) (j : ℕ) : ℝ := (1 - α) * α ^ j

/-- Cochrane (2023), §20.3, p. 485: the log relative price of a firm that last reset `j` periods
ago under constant inflation `π`, `p_j = απ/(1−α) − jπ`. -/
noncomputable def relPrice (α π : ℝ) (j : ℕ) : ℝ := α * π / (1 - α) - j * π

/-- Cochrane (2023), §20.3, p. 485 ("relative prices are less distorted"): the cross-sectional
dispersion (variance) of log prices, `∑ (1−α)αʲ p_j²`. -/
noncomputable def dispersion (α π : ℝ) : ℝ := ∑' j, calvoW α j * relPrice α π j ^ 2

/-- Cochrane (2023), §20.3, p. 485 ("firms are closer to their optimal prices"): the average
squared distance of prices from the optimal (reset) price, `∑ (1−α)αʲ (jπ)²`. -/
noncomputable def resetGap (α π : ℝ) : ℝ := ∑' j, calvoW α j * ((j : ℝ) * π) ^ 2

/-- Cochrane (2023), §20.3, p. 485: the age weights sum to one. -/
theorem hasSum_calvoW {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) : HasSum (calvoW α) 1 := by
  have := (hasSum_geometric_of_lt_one h0 h1).mul_left (1 - α)
  rwa [mul_inv_cancel₀ (by linarith : (1 : ℝ) - α ≠ 0)] at this

/-- Cochrane (2023), §20.3, p. 485: the mean age, `∑ (1−α)αʲ j = α/(1−α)`. -/
theorem hasSum_calvoW_mul {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    HasSum (fun j : ℕ => calvoW α j * j) (α / (1 - α)) := by
  have hn : ‖α‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have := (hasSum_coe_mul_geometric_of_norm_lt_one hn).mul_left (1 - α)
  have e : (1 - α) * (α / (1 - α) ^ 2) = α / (1 - α) := by
    field_simp [(by linarith : (1 : ℝ) - α ≠ 0)]
  rw [e] at this
  refine this.congr_fun fun j => ?_
  simp only [calvoW]
  ring

/-- Cochrane (2023), §20.3, p. 485: `∑ j² αʲ = α(1+α)/(1−α)³` for `0 ≤ α < 1`. -/
theorem hasSum_sq_mul_geometric {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    HasSum (fun j : ℕ => (j : ℝ) ^ 2 * α ^ j) (α * (1 + α) / (1 - α) ^ 3) := by
  have hn : ‖α‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have hs2 : Summable (fun j : ℕ => (j : ℝ) ^ 2 * α ^ j) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hn
  have hS1 := hasSum_coe_mul_geometric_of_norm_lt_one hn
  have hS0 := hasSum_geometric_of_lt_one h0 h1
  set S2 := ∑' j : ℕ, (j : ℝ) ^ 2 * α ^ j
  -- the shift `S₂ = α(S₂ + 2S₁ + S₀)`
  have hshift : S2 = α * (S2 + 2 * (α / (1 - α) ^ 2) + (1 - α)⁻¹) := by
    have e1 := hs2.tsum_eq_zero_add
    have hsucc : HasSum (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ 2 * α ^ (j + 1))
        (α * (S2 + 2 * (α / (1 - α) ^ 2) + (1 - α)⁻¹)) := by
      have := ((hs2.hasSum.add (hS1.mul_left 2)).add hS0).mul_left α
      refine this.congr_fun fun j => ?_
      push_cast
      ring
    simp only [CharP.cast_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      pow_zero, mul_one, zero_add] at e1
    exact e1.trans hsucc.tsum_eq
  have hne : (1 : ℝ) - α ≠ 0 := by linarith
  have hval : S2 = α * (1 + α) / (1 - α) ^ 3 := by
    field_simp at hshift ⊢
    linear_combination hshift
  rw [← hval]
  exact hs2.hasSum

/-- Cochrane (2023), §20.3, p. 485: the second moment of the age,
`∑ (1−α)αʲ j² = α(1+α)/(1−α)²`. -/
theorem hasSum_calvoW_sq {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    HasSum (fun j : ℕ => calvoW α j * (j : ℝ) ^ 2) (α * (1 + α) / (1 - α) ^ 2) := by
  have := (hasSum_sq_mul_geometric h0 h1).mul_left (1 - α)
  have e : (1 - α) * (α * (1 + α) / (1 - α) ^ 3) = α * (1 + α) / (1 - α) ^ 2 := by
    field_simp [(by linarith : (1 : ℝ) - α ≠ 0)]
  rw [e] at this
  refine this.congr_fun fun j => ?_
  simp only [calvoW]
  ring

/-- Cochrane (2023), §20.3, p. 485: the price-index normalisation — the weighted mean of log
relative prices is zero, `∑ (1−α)αʲ p_j = 0`. -/
theorem relPrice_mean {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (π : ℝ) :
    HasSum (fun j => calvoW α j * relPrice α π j) 0 := by
  have := ((hasSum_calvoW h0 h1).mul_left (α * π / (1 - α))).sub
    ((hasSum_calvoW_mul h0 h1).mul_left π)
  have e : α * π / (1 - α) * 1 - π * (α / (1 - α)) = 0 := by ring
  rw [e] at this
  refine this.congr_fun fun j => ?_
  simp only [relPrice]
  ring

/-- Cochrane (2023), §20.3, p. 485: **the exact steady-state dispersion**,
`∑ (1−α)αʲ p_j² = απ²/(1−α)²` (`0 ≤ α < 1`). -/
theorem dispersion_eq {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (π : ℝ) :
    dispersion α π = α * π ^ 2 / (1 - α) ^ 2 := by
  have hne : (1 : ℝ) - α ≠ 0 := by linarith
  have h := (((hasSum_calvoW h0 h1).mul_left ((α * π / (1 - α)) ^ 2)).sub
    ((hasSum_calvoW_mul h0 h1).mul_left (2 * (α * π / (1 - α)) * π))).add
    ((hasSum_calvoW_sq h0 h1).mul_left (π ^ 2))
  have e : (α * π / (1 - α)) ^ 2 * 1 - 2 * (α * π / (1 - α)) * π * (α / (1 - α)) +
      π ^ 2 * (α * (1 + α) / (1 - α) ^ 2) = α * π ^ 2 / (1 - α) ^ 2 := by
    field_simp
    ring
  rw [e] at h
  rw [dispersion, ← h.tsum_eq]
  congr 1
  funext j
  simp only [relPrice]
  ring

/-- Cochrane (2023), §20.3, p. 485: the average squared distance from the optimal price,
`∑ (1−α)αʲ (jπ)² = α(1+α)π²/(1−α)²`. -/
theorem resetGap_eq {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (π : ℝ) :
    resetGap α π = α * (1 + α) * π ^ 2 / (1 - α) ^ 2 := by
  have h := (hasSum_calvoW_sq h0 h1).mul_left (π ^ 2)
  rw [resetGap, ← (show π ^ 2 * (α * (1 + α) / (1 - α) ^ 2) =
    α * (1 + α) * π ^ 2 / (1 - α) ^ 2 by ring), ← h.tsum_eq]
  congr 1
  funext j
  ring

/-- Cochrane (2023), §20.3, p. 485 (Woodford's (2.20) in steady state): the dispersion is the
fixed point of `Δ = αΔ + (α/(1−α))π²`. -/
theorem dispersion_fixed_point {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (π : ℝ) :
    dispersion α π = α * dispersion α π + α / (1 - α) * π ^ 2 := by
  rw [dispersion_eq h0 h1]
  field_simp [(by linarith : (1 : ℝ) - α ≠ 0)]
  ring

/-- Cochrane (2023), §20.3, p. 485: with price stickiness (`0 < α < 1`), relative prices are
undistorted iff inflation is zero. -/
theorem dispersion_eq_zero_iff {α : ℝ} (h0 : 0 < α) (h1 : α < 1) (π : ℝ) :
    dispersion α π = 0 ↔ π = 0 := by
  rw [dispersion_eq h0.le h1]
  have h1' : 0 < 1 - α := by linarith
  have : (0 : ℝ) < (1 - α) ^ 2 := by positivity
  constructor
  · intro h
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · linarith
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
    · linarith
  · rintro rfl; simp

/-- Cochrane (2023), §20.3, p. 485: at zero inflation every firm is at the optimal price. -/
theorem relPrice_zero (α : ℝ) (j : ℕ) : relPrice α 0 j = 0 := by
  simp [relPrice]

/-- Cochrane (2023), §20.3, p. 485 ("less inflation means … relative prices are less
distorted"): dispersion is strictly increasing in `|π|` (`0 < α < 1`). -/
theorem dispersion_lt_iff {α : ℝ} (h0 : 0 < α) (h1 : α < 1) (π1 π2 : ℝ) :
    dispersion α π1 < dispersion α π2 ↔ |π1| < |π2| := by
  rw [dispersion_eq h0.le h1, dispersion_eq h0.le h1]
  have h1' : 0 < 1 - α := by linarith
  have hd : (0 : ℝ) < (1 - α) ^ 2 := by positivity
  rw [div_lt_div_iff_of_pos_right hd, mul_lt_mul_iff_right₀ h0, ← sq_abs, ← sq_abs π2]
  exact pow_lt_pow_iff_left₀ (abs_nonneg _) (abs_nonneg _) (by norm_num)

/-- Cochrane (2023), §20.3, p. 485 ("firms are closer to their optimal prices"): the average
squared distance from the optimal price is strictly increasing in `|π|`. -/
theorem resetGap_lt_iff {α : ℝ} (h0 : 0 < α) (h1 : α < 1) (π1 π2 : ℝ) :
    resetGap α π1 < resetGap α π2 ↔ |π1| < |π2| := by
  rw [resetGap_eq h0.le h1, resetGap_eq h0.le h1]
  have h1' : 0 < 1 - α := by linarith
  have hd : (0 : ℝ) < (1 - α) ^ 2 := by positivity
  have hc : 0 < α * (1 + α) := by positivity
  rw [div_lt_div_iff_of_pos_right hd, mul_lt_mul_iff_right₀ hc, ← sq_abs, ← sq_abs π2]
  exact pow_lt_pow_iff_left₀ (abs_nonneg _) (abs_nonneg _) (by norm_num)

/-! ## Steady-state welfare loss -/

/-- Cochrane (2023), §20.3, p. 485 (the new-Keynesian Phillips curve in steady state):
`π = βπ + κx̄` iff `x̄ = (1−β)π/κ`. -/
theorem ss_phillips_iff {β κ π x : ℝ} (hκ : κ ≠ 0) :
    π = β * π + κ * x ↔ x = (1 - β) * π / κ := by
  rw [eq_div_iff hκ]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §20.3, p. 485: the steady-state quadratic welfare loss
`π² + λx̄²` at the steady state `x̄ = (1−β)π/κ` of inflation `π`. -/
noncomputable def ssLoss (lam β κ π : ℝ) : ℝ := π ^ 2 + lam * ((1 - β) * π / κ) ^ 2

/-- Cochrane (2023), §20.3, p. 485: the steady-state loss is `π²(1 + λ(1−β)²/κ²)`, strictly
increasing in `|π|` (`λ ≥ 0`). -/
theorem ssLoss_lt_iff {lam β κ : ℝ} (hlam : 0 ≤ lam) (π1 π2 : ℝ) :
    ssLoss lam β κ π1 < ssLoss lam β κ π2 ↔ |π1| < |π2| := by
  have e : ∀ π, ssLoss lam β κ π = π ^ 2 * (1 + lam * ((1 - β) / κ) ^ 2) := fun π => by
    simp only [ssLoss]; ring
  have hc : 0 < 1 + lam * ((1 - β) / κ) ^ 2 := by positivity
  rw [e, e, mul_lt_mul_iff_left₀ hc, ← sq_abs, ← sq_abs π2]
  exact pow_lt_pow_iff_left₀ (abs_nonneg _) (abs_nonneg _) (by norm_num)

/-! ## The zero-bound steady state `Π_L` versus `Π*` -/

/-- Cochrane (2023), §20.3, p. 484, with (16.28) `Π' = β(1+i)`: at the zero bound (`i = 0`) the
steady state is `Π_L = β` (deflation at the real rate). -/
theorem zlb_steady_state {β PL i : ℝ} (hfisher : PL = β * (1 + i)) (hi : i = 0) : PL = β := by
  rw [hfisher, hi]; ring

/-- Cochrane (2023), §20.3, pp. 484–485, **corrected** (survey E9): with `0 < β ≤ 1` and a
target `Π* ≥ 1`, the zero-bound steady state `Π_L = β` has strictly less relative-price
dispersion than `Π*` iff `1 < βΠ*` (the real rate is below the target inflation rate). -/
theorem zlb_better_iff {α β Pstar : ℝ} (h0 : 0 < α) (h1 : α < 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hP : 1 ≤ Pstar) :
    dispersion α (Real.log β) < dispersion α (Real.log Pstar) ↔ 1 < β * Pstar := by
  rw [dispersion_lt_iff h0 h1, abs_of_nonpos (Real.log_nonpos hβ0.le hβ1),
    abs_of_nonneg (Real.log_nonneg hP), neg_lt_iff_pos_add, ← Real.log_mul (by linarith)
      hβ0.ne', mul_comm, Real.log_pos_iff (by positivity)]

/-- Cochrane (2023), §20.3, pp. 484–485 (survey E9): conversely the zero-bound steady state is
strictly *worse* iff `βΠ* < 1` (the real rate exceeds the target). -/
theorem zlb_worse_iff {α β Pstar : ℝ} (h0 : 0 < α) (h1 : α < 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hP : 1 ≤ Pstar) :
    dispersion α (Real.log Pstar) < dispersion α (Real.log β) ↔ β * Pstar < 1 := by
  rw [dispersion_lt_iff h0 h1, abs_of_nonpos (Real.log_nonpos hβ0.le hβ1),
    abs_of_nonneg (Real.log_nonneg hP), lt_neg_iff_add_neg, ← Real.log_mul (by linarith)
      hβ0.ne', mul_comm, Real.log_neg_iff (by positivity)]

/-- Cochrane (2023), §20.3, pp. 484–485, the same comparison for the steady-state quadratic
welfare loss: `Π_L = β` is better than `Π*` iff `1 < βΠ*`. -/
theorem zlb_welfare_better_iff {lam βd κ β Pstar : ℝ} (hlam : 0 ≤ lam) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hP : 1 ≤ Pstar) :
    ssLoss lam βd κ (Real.log β) < ssLoss lam βd κ (Real.log Pstar) ↔ 1 < β * Pstar := by
  rw [ssLoss_lt_iff hlam, abs_of_nonpos (Real.log_nonpos hβ0.le hβ1),
    abs_of_nonneg (Real.log_nonneg hP), neg_lt_iff_pos_add, ← Real.log_mul (by linarith)
      hβ0.ne', mul_comm, Real.log_pos_iff (by positivity)]

/-- Cochrane (2023), §20.3, p. 485, **E9 counterexample**: with a 5% real rate (`β = 0.95`) and a
2% target (`Π* = 1.02`), the zero-bound steady state has strictly more relative-price
dispersion than `Π*` (for every Calvo parameter `0 < α < 1`). -/
theorem e9_counterexample {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    dispersion α (Real.log (1.02 : ℝ)) < dispersion α (Real.log (0.95 : ℝ)) :=
  (zlb_worse_iff h0 h1 (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)

/-- Cochrane (2023), §20.3 and p. 380 (the book's numbers): with `r = 1%` (`β = 1/1.01`) and a
2% target, the zero-bound steady state (`−1%` inflation) has less dispersion than `Π*`. -/
theorem book_calibration {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    dispersion α (Real.log (1 / 1.01 : ℝ)) < dispersion α (Real.log (1.02 : ℝ)) :=
  (zlb_better_iff h0 h1 (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)

/-- Cochrane (2023), §20.3, p. 380 ("`Π_L` may occur at, say, 1% inflation"): any zero-bound
steady state with `1 ≤ Π_L < Π*` has strictly less dispersion than `Π*`. -/
theorem zlb_better_of_one_le {α PL Pstar : ℝ} (h0 : 0 < α) (h1 : α < 1) (hL : 1 ≤ PL)
    (hlt : PL < Pstar) : dispersion α (Real.log PL) < dispersion α (Real.log Pstar) := by
  rw [dispersion_lt_iff h0 h1, abs_of_nonneg (Real.log_nonneg hL),
    abs_of_nonneg (Real.log_nonneg (by linarith))]
  exact Real.log_lt_log (by linarith) hlt

end Cochrane.ZeroBound.ZLBWelfare
