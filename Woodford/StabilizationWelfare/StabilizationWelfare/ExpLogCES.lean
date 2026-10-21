/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.OneParamTaylor
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential

/-!
# Exponential, logarithm and CES (Dixit–Stiglitz) expansions

Woodford (2003), *Interest and Prices*, Chapter 6, §2, eq. (2.6), p. 393 and Appendix E,
eqs. (E.5) and (E.8), pp. 693–695; §4.1, p. 425 (the target rate `i*`).

This module collects the elementary expansions the welfare calculations of Chapter 6 use.

* (T2) `|eˣ − 1 − x − x²/2| ≤ (2/9)|x|³` for `|x| ≤ 1` (`abs_exp_sub_taylor2_le`,
  `exp_taylor2_isBigO`), and the logarithmic counterparts `log_taylor2_isBigO`,
  `istar_expansion` (`log(1 − x) = −x + O(x²)`).
* The CES / cumulant expansion for a finite weighted cross-section of goods: with mean
  `E_i y` (`crossMean`) and variance `var_i y` (`crossVar`),
  `(1/r) log E_i[exp(r y)] = E_i y + (r/2) var_i y + O(‖y‖∞³)` (`cumulant_expansion`), and in
  one-parameter form `y = ε y₁`: the first two `ε`-derivatives at `0` are `E_i y₁` and
  `r var_i y₁` (`cumulant_eps_hasDerivAt_zero`, `cumulant_eps_second_deriv`), with the cubic
  expansion `cumulant_eps_expansion`.
* The Dixit–Stiglitz aggregates: (E.5) `Ŷ = E_i ŷ + ½(1 − θ⁻¹) var_i ŷ + O(‖ŷ‖³)`
  (`log_outputIndex_expansion`) and the price-index expansion
  `log P = P̄ + ½(1 − θ) Δ + O(3)` with `P̄ = E_i log p`, `Δ = var_i log p`
  (`log_priceIndex_expansion`), which refines the appendix's `P̄ = log P + O(2)`
  (`log_priceIndex_sub_mean_isBigO`).
* §4.1, p. 425: `i* = log((1 + īᵐ)/(1 + ī)) = −Δ̄ + O(Δ̄²)` with
  `Δ̄ = (ī − īᵐ)/(1 + ī)` (`istar_ratio`, `istar_expansion`, `abs_istar_add_le`).
-/

namespace Woodford.StabilizationWelfare.ExpLogCES

open Filter Topology Asymptotics
open OneParamTaylor (pow_succ_isBigO_self)

/-! ## Exponential and logarithm -/

/-- Woodford (2003), App. E, eq. (E.5), p. 693 (ingredient (T2)): for `|x| ≤ 1`,
`|eˣ − (1 + x + x²/2)| ≤ (2/9)|x|³`. -/
theorem abs_exp_sub_taylor2_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - (1 + x + x ^ 2 / 2)| ≤ 2 / 9 * |x| ^ 3 := by
  have h := Real.exp_bound hx (n := 3) (by norm_num)
  have e : ∑ m ∈ Finset.range 3, x ^ m / (m.factorial : ℝ) = 1 + x + x ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [e] at h
  have e2 : ((Nat.succ 3 : ℕ) : ℝ) / ((Nat.factorial 3 : ℕ) * (3 : ℕ)) = 2 / 9 := by
    norm_num [Nat.factorial]
  rw [e2] at h
  linarith

/-- Woodford (2003), App. E, p. 693: the exact remainder of `eˣ = 1 + x + x²/2 + O(x³)`,
`expRem x = eˣ − 1 − x − x²/2` (an atom of weight three, `abs_expRem_le`); it gives
`Y/Ȳ − 1 = Ŷ + Ŷ²/2 + expRem Ŷ` exactly. -/
noncomputable def expRem (x : ℝ) : ℝ := Real.exp x - 1 - x - x ^ 2 / 2

/-- Woodford (2003), App. E, p. 693: `eˣ − 1 = x + x²/2 + expRem x` exactly. -/
theorem exp_sub_one_eq (x : ℝ) : Real.exp x - 1 = x + x ^ 2 / 2 + expRem x := by
  unfold expRem; ring

/-- Woodford (2003), App. E, p. 693: the exponential remainder is of third order,
`|expRem x| ≤ (2/9)|x|³` for `|x| ≤ 1`. -/
theorem abs_expRem_le {x : ℝ} (hx : |x| ≤ 1) : |expRem x| ≤ 2 / 9 * |x| ^ 3 := by
  have e : expRem x = Real.exp x - (1 + x + x ^ 2 / 2) := by unfold expRem; ring
  rw [e]
  exact abs_exp_sub_taylor2_le hx

/-- Woodford (2003), App. E, p. 693: the logarithmic remainder
`rlog u = log(1 + u) − u + u²/2` (an atom of weight three, `abs_rlog_le`). -/
noncomputable def rlog (u : ℝ) : ℝ := Real.log (1 + u) - u + u ^ 2 / 2

/-- Woodford (2003), App. E, p. 693: the logarithmic remainder is of third order,
`|rlog u| ≤ |u|³/(1 − |u|)` for `|u| < 1`. -/
theorem abs_rlog_le {u : ℝ} (hu : |u| < 1) : |rlog u| ≤ |u| ^ 3 / (1 - |u|) := by
  have hu' : |-u| < 1 := by rwa [abs_neg]
  have h := Real.abs_log_sub_add_sum_range_le hu' 2
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Nat.cast_zero, Nat.cast_one, pow_one, abs_neg, sub_neg_eq_add] at h
  have he : rlog u = -u / (0 + 1) + (-u) ^ 2 / (1 + 1) + Real.log (1 + u) := by
    unfold rlog; ring
  rw [he]
  simpa using h

/-- Woodford (2003), App. E, eq. (E.5), p. 693: `eˣ − (1 + x + x²/2) = O(x³)` as `x → 0`. -/
theorem exp_taylor2_isBigO :
    (fun x => Real.exp x - (1 + x + x ^ 2 / 2)) =O[𝓝 0] (fun x => x ^ 3) := by
  refine IsBigO.of_bound (2 / 9) ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with x hx
  have hx' : |x| ≤ 1 := by simpa using hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  exact abs_exp_sub_taylor2_le hx'

/-- Woodford (2003), App. E, p. 693 (log counterpart of (T2)): for `|u| ≤ 1/2`,
`|log(1 + u) − (u − u²/2)| ≤ 2|u|³`. -/
theorem abs_log_one_add_sub_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |Real.log (1 + u) - (u - u ^ 2 / 2)| ≤ 2 * |u| ^ 3 := by
  have hpos : 0 < 1 - |u| := by linarith
  have h := abs_rlog_le (by linarith : |u| < 1)
  have e : Real.log (1 + u) - (u - u ^ 2 / 2) = rlog u := by unfold rlog; ring
  rw [e]
  refine h.trans ?_
  rw [div_le_iff₀ hpos]
  have : 0 ≤ |u| ^ 3 := by positivity
  nlinarith

/-- Woodford (2003), App. E, p. 693: `log(1 + u) − (u − u²/2) = O(u³)` as `u → 0`. -/
theorem log_taylor2_isBigO :
    (fun u => Real.log (1 + u) - (u - u ^ 2 / 2)) =O[𝓝 0] (fun u => u ^ 3) := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with u hu
  have hu' : |u| ≤ 1 / 2 := by simpa using hu
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  exact abs_log_one_add_sub_le hu'

/-- Woodford (2003), §4.1, p. 425: for `|x| < 1`, `|log(1 − x) + x| ≤ x²/(1 − |x|)`. -/
theorem abs_log_one_sub_add_le {x : ℝ} (hx : |x| < 1) :
    |Real.log (1 - x) + x| ≤ x ^ 2 / (1 - |x|) := by
  have h := Real.abs_log_sub_add_sum_range_le hx 1
  simp only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_zero, div_one] at h
  rw [add_comm, sq_abs] at h
  simpa using h

/-! ## Interest-rate target `i*` (§4.1) -/

/-- Woodford (2003), §4.1, p. 425: with the steady-state interest-rate differential
`Δ̄ = (ī − īᵐ)/(1 + ī)`, exactly `(1 + īᵐ)/(1 + ī) = 1 − Δ̄`. -/
theorem istar_ratio {ibar im : ℝ} (hi : 1 + ibar ≠ 0) :
    (1 + im) / (1 + ibar) = 1 - (ibar - im) / (1 + ibar) := by
  field_simp
  ring

/-- Woodford (2003), §4.1, p. 425: `i* = log((1 + īᵐ)/(1 + ī)) = −Δ̄ + O(Δ̄²)`, stated as a
function of the differential `Δ̄` (by `istar_ratio`, `i* = log(1 − Δ̄)`). -/
theorem istar_expansion :
    (fun x => Real.log (1 - x) - (-x)) =O[𝓝 0] (fun x => x ^ 2) := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
  have hx' : |x| ≤ 1 / 2 := by simpa using hx
  have h := abs_log_one_sub_add_le (by linarith : |x| < 1)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_neg_eq_add]
  have hpos : 0 < 1 - |x| := by linarith
  calc _ ≤ x ^ 2 / (1 - |x|) := h
    _ ≤ 2 * |x ^ 2| := by
      rw [div_le_iff₀ hpos, abs_of_nonneg (sq_nonneg x)]
      nlinarith [sq_nonneg x]

/-- Woodford (2003), §4.1, p. 425: the explicit bound behind `i* = −Δ̄ + O(Δ̄²)`: whenever
`|Δ̄| < 1`, `|log((1 + īᵐ)/(1 + ī)) + Δ̄| ≤ Δ̄²/(1 − |Δ̄|)`. -/
theorem abs_istar_add_le {ibar im : ℝ} (hi : 1 + ibar ≠ 0)
    (hd : |(ibar - im) / (1 + ibar)| < 1) :
    |Real.log ((1 + im) / (1 + ibar)) + (ibar - im) / (1 + ibar)| ≤
      ((ibar - im) / (1 + ibar)) ^ 2 / (1 - |(ibar - im) / (1 + ibar)|) := by
  rw [istar_ratio hi]
  exact abs_log_one_sub_add_le hd

/-! ## Cross-sectional means and variances -/

variable {ι : Type*} [Fintype ι]

/-- Woodford (2003), App. E, p. 693: the cross-sectional mean `E_i y = ∑ w_i y_i` over a finite
set of goods with weights `w`. -/
def crossMean (w y : ι → ℝ) : ℝ := ∑ i, w i * y i

/-- Woodford (2003), App. E, p. 693: the cross-sectional variance
`var_i y = ∑ w_i (y_i − E_i y)²`. -/
def crossVar (w y : ι → ℝ) : ℝ := ∑ i, w i * (y i - crossMean w y) ^ 2

/-- Woodford (2003), App. E, p. 693: the cross-sectional mean is the finite-state expectation
of `OneParamTaylor`. -/
theorem crossMean_eq_expect (w y : ι → ℝ) : crossMean w y = OneParamTaylor.expect w y := by
  simp [crossMean, OneParamTaylor.expect]

/-- Woodford (2003), App. E, p. 693: `var_i y = E_i y² − (E_i y)²` when the weights sum to one. -/
theorem crossVar_eq {w : ι → ℝ} (hw1 : ∑ i, w i = 1) (y : ι → ℝ) :
    crossVar w y = crossMean w (fun i => y i ^ 2) - crossMean w y ^ 2 := by
  unfold crossVar
  have h : ∀ i, w i * (y i - crossMean w y) ^ 2 =
      w i * y i ^ 2 - 2 * crossMean w y * (w i * y i) + crossMean w y ^ 2 * w i :=
    fun i => by ring
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hw1]
  simp only [crossMean]
  ring

/-- Woodford (2003), App. E, p. 695: adding a constant shifts the mean by that constant. -/
theorem crossMean_const_add {w : ι → ℝ} (hw1 : ∑ i, w i = 1) (c : ℝ) (y : ι → ℝ) :
    crossMean w (fun i => c + y i) = c + crossMean w y := by
  simp only [crossMean, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hw1, one_mul]

/-- Woodford (2003), App. E, eq. (E.8), p. 695: the variance is invariant to a common shift
(`var_i(log p − P̄_{t−1}) = var_i log p`). -/
theorem crossVar_const_add {w : ι → ℝ} (hw1 : ∑ i, w i = 1) (c : ℝ) (y : ι → ℝ) :
    crossVar w (fun i => c + y i) = crossVar w y := by
  unfold crossVar
  rw [crossMean_const_add hw1]
  congr 1
  ext i
  ring

/-- Woodford (2003), §2, eq. (2.12), p. 396 (scaling): `E_i(a y) = a E_i y`. -/
theorem crossMean_mul (w : ι → ℝ) (a : ℝ) (y : ι → ℝ) :
    crossMean w (fun i => a * y i) = a * crossMean w y := by
  simp only [crossMean, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Woodford (2003), §2, eq. (2.12), p. 396 (scaling): `var_i(a y) = a² var_i y`. -/
theorem crossVar_mul (w : ι → ℝ) (a : ℝ) (y : ι → ℝ) :
    crossVar w (fun i => a * y i) = a ^ 2 * crossVar w y := by
  simp only [crossVar, crossMean_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Woodford (2003), App. E, p. 693: `|E_i y| ≤ ‖y‖∞` for probability weights. -/
theorem abs_crossMean_le {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (y : ι → ℝ) : |crossMean w y| ≤ ‖y‖ := by
  unfold crossMean
  calc |∑ i, w i * y i| ≤ ∑ i, |w i * y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, w i * ‖y‖ := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, abs_of_nonneg (hw i)]
        exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm y i) (hw i)
    _ = ‖y‖ := by rw [← Finset.sum_mul, hw1, one_mul]

/-- Woodford (2003), App. E, p. 693: `0 ≤ E_i y² ≤ ‖y‖∞²` for probability weights. -/
theorem crossMean_sq_le {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (y : ι → ℝ) :
    0 ≤ crossMean w (fun i => y i ^ 2) ∧ crossMean w (fun i => y i ^ 2) ≤ ‖y‖ ^ 2 := by
  unfold crossMean
  refine ⟨Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _), ?_⟩
  calc ∑ i, w i * y i ^ 2 ≤ ∑ i, w i * ‖y‖ ^ 2 := Finset.sum_le_sum fun i _ => by
        refine mul_le_mul_of_nonneg_left ?_ (hw i)
        have h := norm_le_pi_norm y i
        rw [Real.norm_eq_abs] at h
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = ‖y‖ ^ 2 := by rw [← Finset.sum_mul, hw1, one_mul]

/-- Woodford (2003), App. E, p. 693: `0 ≤ var_i y ≤ ‖y‖∞²` for probability weights. -/
theorem crossVar_le {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (y : ι → ℝ) :
    0 ≤ crossVar w y ∧ crossVar w y ≤ ‖y‖ ^ 2 := by
  refine ⟨Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _), ?_⟩
  rw [crossVar_eq hw1]
  have := (crossMean_sq_le hw hw1 y).2
  nlinarith [sq_nonneg (crossMean w y)]

/-! ## The CES / cumulant expansion -/

/-- Woodford (2003), eq. (2.6), p. 393: the exponential moment `E_i[exp(r y)] = ∑ w_i e^{r y_i}`
underlying a Dixit–Stiglitz aggregate with exponent `r`. -/
noncomputable def cesMoment (w : ι → ℝ) (r : ℝ) (y : ι → ℝ) : ℝ := ∑ i, w i * Real.exp (r * y i)

/-- Woodford (2003), eq. (2.6), p. 393: the normalised cumulant
`(1/r) log E_i[exp(r y)]` (the log of a Dixit–Stiglitz aggregate of `e^{y}`). -/
noncomputable def cumulant (w : ι → ℝ) (r : ℝ) (y : ι → ℝ) : ℝ :=
  1 / r * Real.log (cesMoment w r y)

/-- Woodford (2003), eq. (2.6), p. 393: the exponential moment is positive for probability
weights. -/
theorem cesMoment_pos {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (r : ℝ)
    (y : ι → ℝ) : 0 < cesMoment w r y := by
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hw1]; exact one_ne_zero)
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hw j) (Real.exp_pos _).le)
    ⟨i, Finset.mem_univ i, mul_pos (lt_of_le_of_ne (hw i) (Ne.symm hi)) (Real.exp_pos _)⟩

/-- Woodford (2003), App. E, eq. (E.5), p. 693 and survey (T4): the CES / cumulant expansion
for a finite weighted cross-section,
`(1/r) log E_i[exp(r y)] = E_i y + (r/2) var_i y + O(‖y‖∞³)` as `y → 0`, for any `r ≠ 0`. -/
theorem cumulant_expansion {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {r : ℝ}
    (hr : r ≠ 0) :
    (fun y => cumulant w r y - (crossMean w y + r / 2 * crossVar w y)) =O[𝓝 0]
      (fun y => ‖y‖ ^ 3) := by
  have hN : Tendsto (fun y : ι → ℝ => ‖y‖) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_norm.tendsto (0 : ι → ℝ))
  have hE1 : (fun y => crossMean w y) =O[𝓝 (0 : ι → ℝ)] (fun y => ‖y‖) :=
    IsBigO.of_bound 1 (Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using abs_crossMean_le hw hw1 y)
  have hE2 : (fun y => crossMean w (fun i => y i ^ 2)) =O[𝓝 (0 : ι → ℝ)] (fun y => ‖y‖ ^ 2) :=
    IsBigO.of_bound 1 (Eventually.of_forall fun y => by
      have h := crossMean_sq_le hw hw1 y
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h.1, abs_of_nonneg (by positivity)]
      linarith [h.2])
  -- the remainder of the exponential moment
  have hA : (fun y => (cesMoment w r y - 1) - (r * crossMean w y +
      r ^ 2 / 2 * crossMean w (fun i => y i ^ 2))) =O[𝓝 (0 : ι → ℝ)] (fun y => ‖y‖ ^ 3) := by
    refine IsBigO.of_bound (2 / 9 * |r| ^ 3) ?_
    have hrpos : 0 < 1 / |r| := by positivity
    filter_upwards [Metric.closedBall_mem_nhds (0 : ι → ℝ) hrpos] with y hy
    have hy' : |r| * ‖y‖ ≤ 1 := by
      have : ‖y‖ ≤ 1 / |r| := by simpa using hy
      rw [le_div_iff₀ (abs_pos.2 hr)] at this
      linarith
    have key : (cesMoment w r y - 1) - (r * crossMean w y +
        r ^ 2 / 2 * crossMean w (fun i => y i ^ 2)) =
        ∑ i, w i * (Real.exp (r * y i) - (1 + r * y i + (r * y i) ^ 2 / 2)) := by
      have h1 : ∀ i, w i * (Real.exp (r * y i) - (1 + r * y i + (r * y i) ^ 2 / 2)) =
          w i * Real.exp (r * y i) - w i - r * (w i * y i) - r ^ 2 / 2 * (w i * y i ^ 2) :=
        fun i => by ring
      rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hw1]
      simp only [cesMoment, crossMean]
      ring
    rw [key, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_norm]
    calc |∑ i, w i * (Real.exp (r * y i) - (1 + r * y i + (r * y i) ^ 2 / 2))|
        ≤ ∑ i, |w i * (Real.exp (r * y i) - (1 + r * y i + (r * y i) ^ 2 / 2))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, w i * (2 / 9 * |r| ^ 3 * ‖y‖ ^ 3) := Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_of_nonneg (hw i)]
          refine mul_le_mul_of_nonneg_left ?_ (hw i)
          have hyi : |y i| ≤ ‖y‖ := by simpa using norm_le_pi_norm y i
          have hri : |r * y i| ≤ |r| * ‖y‖ := by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left hyi (abs_nonneg r)
          calc _ ≤ 2 / 9 * |r * y i| ^ 3 := abs_exp_sub_taylor2_le (hri.trans hy')
            _ ≤ 2 / 9 * (|r| * ‖y‖) ^ 3 := by gcongr
            _ = 2 / 9 * |r| ^ 3 * ‖y‖ ^ 3 := by ring
      _ = 2 / 9 * |r| ^ 3 * ‖y‖ ^ 3 := by rw [← Finset.sum_mul, hw1, one_mul]
  have h31 : (fun y : ι → ℝ => ‖y‖ ^ 3) =O[𝓝 0] (fun y => ‖y‖) := pow_succ_isBigO_self hN 2
  have h21 : (fun y : ι → ℝ => ‖y‖ ^ 2) =O[𝓝 0] (fun y => ‖y‖) := pow_succ_isBigO_self hN 1
  have h32 : (fun y : ι → ℝ => ‖y‖ ^ 3) =O[𝓝 0] (fun y => ‖y‖ ^ 2) := by
    refine ((hN.isBigO_one ℝ).mul (isBigO_refl (fun y : ι → ℝ => ‖y‖ ^ 2) _)).congr
      (fun y => by ring) (fun y => by ring)
  -- `u = E[exp(r y)] − 1` is first order
  have hu : (fun y => cesMoment w r y - 1) =O[𝓝 (0 : ι → ℝ)] (fun y => ‖y‖) := by
    refine ((hA.trans h31).add ((hE1.const_mul_left r).add
      ((hE2.trans h21).const_mul_left (r ^ 2 / 2)))).congr_left fun y => ?_
    ring
  have hut : Tendsto (fun y => cesMoment w r y - 1) (𝓝 (0 : ι → ℝ)) (𝓝 0) :=
    hu.trans_tendsto hN
  have hL : (fun y => Real.log (1 + (cesMoment w r y - 1)) -
      ((cesMoment w r y - 1) - (cesMoment w r y - 1) ^ 2 / 2)) =O[𝓝 (0 : ι → ℝ)]
      (fun y => ‖y‖ ^ 3) :=
    (log_taylor2_isBigO.comp_tendsto hut).trans (hu.pow 3)
  have hP : (fun y => ((cesMoment w r y - 1) - r * crossMean w y) *
      ((cesMoment w r y - 1) + r * crossMean w y)) =O[𝓝 (0 : ι → ℝ)] (fun y => ‖y‖ ^ 3) := by
    have h1 : (fun y => (cesMoment w r y - 1) - r * crossMean w y) =O[𝓝 (0 : ι → ℝ)]
        (fun y => ‖y‖ ^ 2) := by
      refine ((hA.trans h32).add (hE2.const_mul_left (r ^ 2 / 2))).congr_left fun y => ?_
      ring
    exact (h1.mul (hu.add (hE1.const_mul_left r))).congr_right fun y => by ring
  refine (((hL.add hA).sub (hP.const_mul_left (1 / 2))).const_mul_left (1 / r)).congr_left
    fun y => ?_
  rw [crossVar_eq hw1, cumulant]
  have e : 1 + (cesMoment w r y - 1) = cesMoment w r y := by ring
  rw [e]
  field_simp
  ring

/-- Woodford (2003), App. E, p. 693: for a one-parameter cross-section `y = ε y₁`, the cumulant
expansion becomes `(1/r) log E_i[exp(r ε y₁)] = ε E_i y₁ + ε²/2 · r var_i y₁ + O(ε³)`. -/
theorem cumulant_eps_expansion {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {r : ℝ}
    (hr : r ≠ 0) (y : ι → ℝ) :
    (fun ε => cumulant w r (fun i => ε * y i) -
      (ε * crossMean w y + ε ^ 2 / 2 * (r * crossVar w y))) =O[𝓝 0] (fun ε => ε ^ 3) := by
  have ht : Tendsto (fun ε : ℝ => fun i => ε * y i) (𝓝 0) (𝓝 0) := by
    have : Continuous (fun ε : ℝ => fun i => ε * y i) := by fun_prop
    rw [show (0 : ι → ℝ) = fun i => (0 : ℝ) * y i from by ext; simp]
    exact this.tendsto 0
  have h := (cumulant_expansion hw hw1 hr).comp_tendsto ht
  have hb : (fun ε : ℝ => ‖fun i => ε * y i‖ ^ 3) =O[𝓝 0] (fun ε => ε ^ 3) := by
    refine IsBigO.of_bound (‖y‖ ^ 3) (Eventually.of_forall fun ε => ?_)
    have e : ‖fun i => ε * y i‖ = |ε| * ‖y‖ := by
      rw [show (fun i => ε * y i) = ε • y from rfl, norm_smul, Real.norm_eq_abs]
    rw [e, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_pow, abs_mul, abs_abs, abs_norm]
    apply le_of_eq
    ring
  refine (h.trans hb).congr_left fun ε => ?_
  simp only [Function.comp, crossMean_mul, crossVar_mul]
  ring

/-- The `ε`-derivative of the exponential moment along `y = ε y₁` (Woodford (2003), App. E,
p. 693): `M₁(ε) = ∑ w_i (r y₁ᵢ) e^{r ε y₁ᵢ}`. -/
noncomputable def cesMoment1 (w : ι → ℝ) (r : ℝ) (y : ι → ℝ) (ε : ℝ) : ℝ :=
  ∑ i, w i * (r * y i) * Real.exp (r * (ε * y i))

/-- Woodford (2003), App. E, p. 693: `d/dε E_i[exp(r ε y)] = M₁(ε)`. -/
theorem hasDerivAt_cesMoment_eps (w : ι → ℝ) (r : ℝ) (y : ι → ℝ) (ε : ℝ) :
    HasDerivAt (fun ε => cesMoment w r (fun i => ε * y i)) (cesMoment1 w r y ε) ε := by
  unfold cesMoment cesMoment1
  refine HasDerivAt.fun_sum fun i _ => ?_
  have h := ((((hasDerivAt_id ε).mul_const (y i)).const_mul r).exp).const_mul (w i)
  refine h.congr_deriv ?_
  simp only [id]
  ring

/-- Woodford (2003), App. E, p. 693: `d/dε M₁(ε) = ∑ w_i (r y₁ᵢ)² e^{r ε y₁ᵢ}`. -/
theorem hasDerivAt_cesMoment1 (w : ι → ℝ) (r : ℝ) (y : ι → ℝ) (ε : ℝ) :
    HasDerivAt (cesMoment1 w r y) (∑ i, w i * (r * y i) ^ 2 * Real.exp (r * (ε * y i))) ε := by
  unfold cesMoment1
  refine HasDerivAt.fun_sum fun i _ => ?_
  have h := ((((hasDerivAt_id ε).mul_const (y i)).const_mul r).exp).const_mul (w i * (r * y i))
  refine h.congr_deriv ?_
  simp only [id]
  ring

/-- Woodford (2003), App. E, p. 693 (ε-form, first derivative): along `y = ε y₁` the cumulant
`(1/r) log E_i[exp(r ε y₁)]` has derivative `(1/r) M₁(ε)/M(ε)` at every `ε`. -/
theorem cumulant_eps_hasDerivAt {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (r : ℝ) (y : ι → ℝ) (ε : ℝ) :
    HasDerivAt (fun ε => cumulant w r (fun i => ε * y i))
      (1 / r * (cesMoment1 w r y ε / cesMoment w r (fun i => ε * y i))) ε := by
  unfold cumulant
  exact ((hasDerivAt_cesMoment_eps w r y ε).log
    (cesMoment_pos hw hw1 r _).ne').const_mul (1 / r)

/-- Woodford (2003), App. E, p. 693 (ε-form): the first `ε`-derivative of the cumulant at
`ε = 0` is the cross-sectional mean `E_i y₁`. -/
theorem cumulant_eps_hasDerivAt_zero {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    {r : ℝ} (hr : r ≠ 0) (y : ι → ℝ) :
    HasDerivAt (fun ε => cumulant w r (fun i => ε * y i)) (crossMean w y) 0 := by
  refine (cumulant_eps_hasDerivAt hw hw1 r y 0).congr_deriv ?_
  have h0 : cesMoment w r (fun i => (0 : ℝ) * y i) = 1 := by simp [cesMoment, hw1]
  rw [h0]
  simp only [cesMoment1, crossMean, zero_mul, mul_zero, Real.exp_zero, mul_one, div_one]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

/-- Woodford (2003), App. E, p. 693 (ε-form): the second `ε`-derivative of the cumulant at
`ε = 0` — the derivative at `0` of its first derivative `(1/r) M₁/M` — is `r var_i y₁`. -/
theorem cumulant_eps_second_deriv {w : ι → ℝ} (hw1 : ∑ i, w i = 1)
    {r : ℝ} (hr : r ≠ 0) (y : ι → ℝ) :
    HasDerivAt (fun ε => 1 / r * (cesMoment1 w r y ε / cesMoment w r (fun i => ε * y i)))
      (r * crossVar w y) 0 := by
  have h0 : cesMoment w r (fun i => (0 : ℝ) * y i) = 1 := by simp [cesMoment, hw1]
  have h := ((hasDerivAt_cesMoment1 w r y 0).div (hasDerivAt_cesMoment_eps w r y 0)
    (by rw [h0]; exact one_ne_zero)).const_mul (1 / r)
  refine h.congr_deriv ?_
  rw [h0, crossVar_eq hw1]
  simp only [cesMoment1, crossMean, zero_mul, mul_zero, Real.exp_zero, mul_one, one_pow, div_one]
  have e1 : ∑ i, w i * (r * y i) = r * ∑ i, w i * y i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, w i * (r * y i) ^ 2 = r ^ 2 * ∑ i, w i * y i ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2]
  field_simp

/-! ## Dixit–Stiglitz aggregates -/

/-- Woodford (2003), eq. (2.6), p. 393 (and the price index, Ch. 3 eq. (1.3)): the
Dixit–Stiglitz aggregate `(∑ w_i p_iʳ)^{1/r}` with exponent `r` (`r = 1 − θ` for the price
index, `r = (θ − 1)/θ` for the output aggregate). -/
noncomputable def cesIndex (w : ι → ℝ) (r : ℝ) (p : ι → ℝ) : ℝ :=
  (∑ i, w i * p i ^ r) ^ (1 / r)

/-- Woodford (2003), eq. (2.6), p. 393: the log of a Dixit–Stiglitz aggregate of `e^{q}` is
the normalised cumulant `(1/r) log E_i[exp(r q)]`. -/
theorem log_cesIndex_exp {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (r : ℝ)
    (q : ι → ℝ) : Real.log (cesIndex w r (fun i => Real.exp (q i))) = cumulant w r q := by
  have e : ∑ i, w i * Real.exp (q i) ^ r = cesMoment w r q := by
    unfold cesMoment
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm (q i) r]
  unfold cesIndex cumulant
  rw [e, Real.log_rpow (cesMoment_pos hw hw1 r q)]

/-- Woodford (2003), eq. (2.6), p. 393: the Dixit–Stiglitz aggregate is homogeneous of degree
one, so `Y = Ȳ · CES(y/Ȳ)` and `Ŷ = log(Y/Ȳ)` is the log aggregate of `e^{ŷ}`. -/
theorem cesIndex_mul {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) {r : ℝ} (hr : r ≠ 0) {a : ℝ}
    (ha : 0 < a) {p : ι → ℝ} (hp : ∀ i, 0 < p i) :
    cesIndex w r (fun i => a * p i) = a * cesIndex w r p := by
  unfold cesIndex
  have hS : 0 ≤ ∑ i, w i * p i ^ r :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Real.rpow_nonneg (hp i).le _)
  have e : ∑ i, w i * (a * p i) ^ r = a ^ r * ∑ i, w i * p i ^ r := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.mul_rpow ha.le (hp i).le]
    ring
  rw [e, Real.mul_rpow (Real.rpow_nonneg ha.le _) hS, ← Real.rpow_mul ha.le,
    mul_one_div_cancel hr, Real.rpow_one]

/-- Woodford (2003), App. E, eq. (E.8), p. 695: shifting every log price by `c` shifts the
cumulant by `c`. -/
theorem cumulant_const_add {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {r : ℝ}
    (hr : r ≠ 0) (c : ℝ) (y : ι → ℝ) :
    cumulant w r (fun i => c + y i) = c + cumulant w r y := by
  have e : cesMoment w r (fun i => c + y i) = Real.exp (r * c) * cesMoment w r y := by
    unfold cesMoment
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_add, Real.exp_add]
    ring
  unfold cumulant
  rw [e, Real.log_mul (Real.exp_pos _).ne' (cesMoment_pos hw hw1 r y).ne', Real.log_exp]
  field_simp

/-- Woodford (2003), App. E, eq. (E.5), p. 693: with `ŷ_i = log(y_i/Ȳ)` and
`Ŷ = log(Y/Ȳ)`, `Y` the Dixit–Stiglitz aggregate (2.6) with elasticity `θ ≠ 1` (the book has
`θ > 1`),
`Ŷ = E_i ŷ + ½(1 − θ⁻¹) var_i ŷ + O(‖ŷ‖³)`. -/
theorem log_outputIndex_expansion {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    {θ : ℝ} (hθ1 : θ ≠ 1) :
    (fun yhat => Real.log (cesIndex w (1 - θ⁻¹) (fun i => Real.exp (yhat i))) -
      (crossMean w yhat + 1 / 2 * (1 - θ⁻¹) * crossVar w yhat)) =O[𝓝 0]
      (fun yhat => ‖yhat‖ ^ 3) := by
  have hr : 1 - θ⁻¹ ≠ 0 := by
    intro h
    apply hθ1
    have : θ⁻¹ = 1 := by linarith
    simpa using congrArg (·⁻¹) this
  refine (cumulant_expansion hw hw1 hr).congr_left fun yhat => ?_
  rw [log_cesIndex_exp hw hw1]
  ring

/-- Woodford (2003), App. E, p. 695 (price index; survey §4): with
`P = (∑ w_i p_i^{1−θ})^{1/(1−θ)}`,
`P̄ = E_i log p` and `Δ = var_i log p`,
`log P = P̄ + ½(1 − θ) Δ + O(‖log p − c‖³)` around any common log price `c` (e.g.
`c = P̄_{t−1}`), for `θ ≠ 1`. -/
theorem log_priceIndex_expansion {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    {θ : ℝ} (hθ : θ ≠ 1) (c : ℝ) :
    (fun q => Real.log (cesIndex w (1 - θ) (fun i => Real.exp (q i))) -
      (crossMean w q + 1 / 2 * (1 - θ) * crossVar w q)) =O[𝓝 (fun _ => c)]
      (fun q => ‖q - fun _ => c‖ ^ 3) := by
  have hr : 1 - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  have ht : Tendsto (fun q : ι → ℝ => q - fun _ => c) (𝓝 fun _ => c) (𝓝 0) := by
    have : Continuous (fun q : ι → ℝ => q - fun _ => c) := by fun_prop
    simpa using this.tendsto (fun _ => c)
  refine ((cumulant_expansion hw hw1 hr).comp_tendsto ht).congr_left fun q => ?_
  have hq : q = fun i => c + (q - fun _ => c : ι → ℝ) i := by ext i; simp
  have h1 : cumulant w (1 - θ) q = c + cumulant w (1 - θ) (q - fun _ => c) := by
    conv_lhs => rw [hq]
    exact cumulant_const_add hw hw1 hr c _
  have h2 : crossMean w q = c + crossMean w (q - fun _ => c) := by
    conv_lhs => rw [hq]
    exact crossMean_const_add hw1 c _
  have h3 : crossVar w q = crossVar w (q - fun _ => c) := by
    conv_lhs => rw [hq]
    exact crossVar_const_add hw1 c _
  simp only [Function.comp]
  rw [log_cesIndex_exp hw hw1, h1, h2, h3]
  ring

/-- Woodford (2003), App. E, p. 695: hence `log P = P̄ + O(‖log p − c‖²)` (the appendix's
`P̄_t = log P_t + O(2)`), since `Δ ≤ ‖log p − c‖²`. -/
theorem log_priceIndex_sub_mean_isBigO {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    {θ : ℝ} (hθ : θ ≠ 1) (c : ℝ) :
    (fun q => Real.log (cesIndex w (1 - θ) (fun i => Real.exp (q i))) - crossMean w q)
      =O[𝓝 (fun _ => c)] (fun q => ‖q - fun _ => c‖ ^ 2) := by
  have ht : Tendsto (fun q : ι → ℝ => ‖q - fun _ => c‖) (𝓝 fun _ => c) (𝓝 0) := by
    have : Continuous (fun q : ι → ℝ => ‖q - fun _ => c‖) := by fun_prop
    simpa using this.tendsto (fun _ => c)
  have h32 : (fun q : ι → ℝ => ‖q - fun _ => c‖ ^ 3) =O[𝓝 fun _ => c]
      (fun q => ‖q - fun _ => c‖ ^ 2) := by
    refine ((ht.isBigO_one ℝ).mul (isBigO_refl (fun q : ι → ℝ => ‖q - fun _ => c‖ ^ 2) _)).congr
      (fun q => by ring) (fun q => by ring)
  have hV : (fun q => 1 / 2 * (1 - θ) * crossVar w q) =O[𝓝 fun _ => c]
      (fun q => ‖q - fun _ => c‖ ^ 2) := by
    refine IsBigO.const_mul_left (IsBigO.of_bound 1 (Eventually.of_forall fun q => ?_)) _
    have hq : crossVar w q = crossVar w (q - fun _ => c) := by
      have e : q = fun i => c + (q - fun _ => c : ι → ℝ) i := by ext i; simp
      conv_lhs => rw [e, crossVar_const_add hw1]
    have h := crossVar_le hw hw1 (q - fun _ => c)
    rw [hq, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h.1, abs_of_nonneg (by positivity)]
    linarith [h.2]
  refine (((log_priceIndex_expansion hw hw1 hθ c).trans h32).add hV).congr_left fun q => ?_
  ring

end Woodford.StabilizationWelfare.ExpLogCES
