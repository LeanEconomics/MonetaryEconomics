/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.PriceDuration
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Exercise 3.1: discrete records of exponential price durations

Galí (2015), Chapter 3, Exercise 3.1 (pp. 88–89). Prices change in continuous time, and the
duration `T` (in months) of a price spell has the exponential law with density
`f(t) = φ e^{−φt}`, i.e. `T ∼ expMeasure φ` (Mathlib's exponential distribution, the gamma
law with shape one). Every statement below is a statement about this probability measure.

## Main results

* (a) `hazard_eq`, `hazard_tendsto`, `cond_change_prob`: the hazard `f(t)/(1 − F(t))` equals
  `φ` at every date, and the conditional probability of a change in `(t, t + h]` divided by
  `h` tends to `φ` as `h ↓ 0`, at every `t ≥ 0`; `memoryless`.
* (b) `mean_duration` (`∫ T = 1/φ`), `median_duration` and `cdf_eq_half_iff` (the median is
  `log 2/φ` and it is the unique one), `median_div_mean` (the ratio is `log 2`) and
  `median_lt_mean`.
* (c) `monthly_change_prob`: whatever the age of a price at a monthly record date, the
  probability that the next record differs is `λ = 1 − e^{−φ}`; `lambda_eq_iff` inverts this
  as the estimator `φ = −log(1 − λ)`; `lambda_lt_phi` (the raw frequency understates `φ`,
  because a price may change more than once within a month).
* (d) `quarterly_survival`: the probability that a price is not changed over a quarter is
  `θ = e^{−3φ} = (1 − λ)³`; `quarterlyCalvo` is the implied quarterly Calvo parameter and
  `quarterlyCalvo_mean_duration` its mean duration in quarters.
-/

namespace Gali.BasicNewKeynesianModel.Ex3_1

open MeasureTheory ProbabilityTheory Filter Topology

/-- Galí (2015), Ex. 3.1, p. 88: the distribution function of the exponential duration,
`F(t) = 1 − e^{−φt}` for `t ≥ 0`. -/
theorem cdf_eq {φ t : ℝ} (hφ : 0 < φ) (ht : 0 ≤ t) :
    cdf (expMeasure φ) t = 1 - Real.exp (-(φ * t)) := by
  rw [cdf_expMeasure_eq hφ]
  simp only [ht, ↓reduceIte]

/-- Galí (2015), Ex. 3.1, p. 88: `P(T ≤ t) = 1 − e^{−φt}` for `t ≥ 0`. -/
theorem prob_le {φ t : ℝ} (hφ : 0 < φ) (ht : 0 ≤ t) :
    (expMeasure φ).real (Set.Iic t) = 1 - Real.exp (-(φ * t)) := by
  have := isProbabilityMeasure_expMeasure hφ
  rw [← cdf_eq_real, cdf_eq hφ ht]

/-- Galí (2015), Ex. 3.1, p. 88: the survival function, `P(T > t) = e^{−φt}` for `t ≥ 0`. -/
theorem survival {φ t : ℝ} (hφ : 0 < φ) (ht : 0 ≤ t) :
    (expMeasure φ).real (Set.Ioi t) = Real.exp (-(φ * t)) := by
  have := isProbabilityMeasure_expMeasure hφ
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, prob_le hφ ht]
  ring

/-- Galí (2015), Ex. 3.1, p. 88: the survival probability is positive. -/
theorem survival_pos {φ t : ℝ} (hφ : 0 < φ) (ht : 0 ≤ t) :
    0 < (expMeasure φ).real (Set.Ioi t) := by
  rw [survival hφ ht]
  exact Real.exp_pos _

/-- Galí (2015), Ex. 3.1, p. 88: the probability of a price change in the window
`(t, t + h]`, `P(t < T ≤ t + h) = e^{−φt}(1 − e^{−φh})`. -/
theorem prob_window {φ t h : ℝ} (hφ : 0 < φ) (ht : 0 ≤ t) (hh : 0 ≤ h) :
    (expMeasure φ).real (Set.Ioc t (t + h)) = Real.exp (-(φ * t)) * (1 - Real.exp (-(φ * h))) := by
  have := isProbabilityMeasure_expMeasure hφ
  rw [← Set.Ioi_sdiff_Ioi, measureReal_sdiff (Set.Ioi_subset_Ioi (by linarith)) measurableSet_Ioi,
    survival hφ ht, survival hφ (by linarith)]
  rw [mul_sub, mul_one, ← Real.exp_add]
  ring_nf

/-- Galí (2015), Ex. 3.1(a), p. 88: **memorylessness**,
`P(T > t + s | T > t) = P(T > s)` for `t, s ≥ 0`. -/
theorem memoryless {φ t s : ℝ} (hφ : 0 < φ) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    (expMeasure φ).real (Set.Ioi (t + s)) / (expMeasure φ).real (Set.Ioi t)
      = (expMeasure φ).real (Set.Ioi s) := by
  rw [survival hφ (by linarith), survival hφ ht, survival hφ hs, div_eq_iff (Real.exp_pos _).ne',
    ← Real.exp_add]
  ring_nf

/-- Galí (2015), Ex. 3.1(a), p. 88: the **hazard rate** `f(t)/(1 − F(t))` equals `φ` at every
date `t ≥ 0`. -/
theorem hazard_eq {φ t : ℝ} (hφ : 0 < φ) (ht : 0 ≤ t) :
    exponentialPDFReal φ t / (expMeasure φ).real (Set.Ioi t) = φ := by
  rw [survival hφ ht, exponentialPDFReal, gammaPDFReal]
  simp only [ht, ↓reduceIte, Real.rpow_one, Real.Gamma_one, div_one, sub_self, Real.rpow_zero,
    mul_one]
  rw [mul_div_assoc, div_self (Real.exp_pos _).ne', mul_one]

/-- Galí (2015), Ex. 3.1(a), p. 88: the conditional probability of a price change within
`h` months, given that the price has survived to `t`, is `1 − e^{−φh}`, independently of
`t` (the change probability is constant over time). -/
theorem cond_change_prob {φ t h : ℝ} (hφ : 0 < φ) (ht : 0 ≤ t) (hh : 0 ≤ h) :
    (expMeasure φ).real (Set.Ioc t (t + h)) / (expMeasure φ).real (Set.Ioi t)
      = 1 - Real.exp (-(φ * h)) := by
  rw [prob_window hφ ht hh, survival hφ ht, mul_div_cancel_left₀ _ (Real.exp_pos _).ne']

/-- Galí (2015), Ex. 3.1(a), p. 88: the **instantaneous probability of a price change** is
`φ` at every date: `P(t < T ≤ t + h | T > t)/h → φ` as `h ↓ 0`, for every `t ≥ 0`. -/
theorem hazard_tendsto {φ t : ℝ} (hφ : 0 < φ) (ht : 0 ≤ t) :
    Tendsto (fun h => (expMeasure φ).real (Set.Ioc t (t + h)) /
      (h * (expMeasure φ).real (Set.Ioi t))) (𝓝[>] 0) (𝓝 φ) := by
  have hd : HasDerivAt (fun h : ℝ => -Real.exp (-(φ * h))) φ 0 := by
    have h1 : HasDerivAt (fun h : ℝ => -(φ * h)) (-φ) 0 := by
      have := (hasDerivAt_id (0 : ℝ)).const_mul (-φ)
      simp only [id, mul_one] at this
      convert this using 1
      ext h
      ring
    have h2 := HasDerivAt.neg (HasDerivAt.exp h1)
    convert h2 using 1
    simp
  refine tendsto_nhdsWithin_congr (fun h (hh : 0 < h) => ?_) hd.tendsto_slope_zero_right
  rw [div_mul_eq_div_div_swap, cond_change_prob hφ ht hh.le]
  simp only [zero_add, mul_zero, neg_zero, Real.exp_zero, smul_eq_mul]
  field_simp
  ring

/-- Galí (2015), Ex. 3.1(b), p. 89: the **mean duration** of a price is `E[T] = 1/φ`. -/
theorem mean_duration {φ : ℝ} (hφ : 0 < φ) : ∫ x, x ∂(expMeasure φ) = 1 / φ := by
  have hmeas : Measurable (gammaPDF 1 φ) := (measurable_gammaPDFReal 1 φ).ennreal_ofReal
  rw [expMeasure, gammaMeasure, integral_withDensity_eq_integral_toReal_smul hmeas
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hpdf : ∀ x, (gammaPDF 1 φ x).toReal = gammaPDFReal 1 φ x := fun x =>
    ENNReal.toReal_ofReal (gammaPDFReal_nonneg one_pos hφ x)
  simp_rw [hpdf, smul_eq_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioi 0) (fun x hx => by
    simp only [Set.mem_Ioi, not_lt] at hx
    rcases hx.lt_or_eq with h | h
    · simp [gammaPDFReal, not_le.mpr h]
    · simp [h])]
  have hcongr : ∀ x ∈ Set.Ioi (0 : ℝ), gammaPDFReal 1 φ x * x
      = φ * (x ^ ((2 : ℝ) - 1) * Real.exp (-(φ * x))) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := le_of_lt hx
    simp only [gammaPDFReal, hx0, ↓reduceIte, Real.rpow_one, Real.Gamma_one, div_one,
      sub_self, Real.rpow_zero, mul_one]
    norm_num
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi two_pos hφ]
  have hG : Real.Gamma 2 = 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one one_ne_zero, Real.Gamma_one,
      mul_one]
  rw [hG, Real.rpow_two]
  field_simp

/-- Galí (2015), Ex. 3.1(b), p. 89: the **median duration** is `log 2/φ`: exactly half of
all prices last at most `log 2/φ` months and half last longer. -/
theorem median_duration {φ : ℝ} (hφ : 0 < φ) :
    (expMeasure φ).real (Set.Iic (Real.log 2 / φ)) = 1 / 2 ∧
      (expMeasure φ).real (Set.Ioi (Real.log 2 / φ)) = 1 / 2 := by
  have hm : 0 ≤ Real.log 2 / φ := div_nonneg (Real.log_nonneg (by norm_num)) hφ.le
  have he : Real.exp (-(φ * (Real.log 2 / φ))) = 1 / 2 := by
    rw [mul_div_cancel₀ _ hφ.ne', Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  rw [prob_le hφ hm, survival hφ hm, he]
  norm_num

/-- Galí (2015), Ex. 3.1(b), p. 89: the median is unique: `F(t) = 1/2` iff `t = log 2/φ`. -/
theorem cdf_eq_half_iff {φ t : ℝ} (hφ : 0 < φ) :
    cdf (expMeasure φ) t = 1 / 2 ↔ t = Real.log 2 / φ := by
  rw [cdf_expMeasure_eq hφ]
  by_cases ht : 0 ≤ t
  · simp only [ht, ↓reduceIte]
    constructor
    · intro h
      have he : Real.exp (-(φ * t)) = 2⁻¹ := by linarith
      have hl := congrArg Real.log he
      rw [Real.log_exp, Real.log_inv] at hl
      field_simp
      linarith
    · intro h
      rw [h, mul_div_cancel₀ _ hφ.ne', Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
  · simp only [ht, ↓reduceIte]
    constructor
    · intro h; norm_num at h
    · intro h
      exact absurd (h ▸ div_nonneg (Real.log_nonneg (by norm_num)) hφ.le) ht

/-- Galí (2015), Ex. 3.1(b), p. 89: the ratio of the median to the mean duration is
`log 2 ≈ 0.69`, independently of `φ`. -/
theorem median_div_mean {φ : ℝ} (hφ : 0 < φ) :
    (Real.log 2 / φ) / ∫ x, x ∂(expMeasure φ) = Real.log 2 := by
  rw [mean_duration hφ]
  field_simp

/-- Galí (2015), Ex. 3.1(b), p. 89: the median duration is strictly below the mean. -/
theorem median_lt_mean {φ : ℝ} (hφ : 0 < φ) : Real.log 2 / φ < ∫ x, x ∂(expMeasure φ) := by
  rw [mean_duration hφ]
  have h2 : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num)
    linarith
  exact div_lt_div_of_pos_right h2 hφ

/-- Galí (2015), Ex. 3.1(c), p. 89: the monthly frequency of price changes implied by a
rate `φ`, `λ = 1 − e^{−φ}`. -/
noncomputable def monthlyFreq (φ : ℝ) : ℝ := 1 - Real.exp (-φ)

/-- Galí (2015), Ex. 3.1(c), p. 89: whatever the age `a ≥ 0` of a price at a monthly record
date, the probability that the next monthly record differs (at least one change within the
month, possibly several) is `λ = 1 − e^{−φ}`. Hence the fraction `λ_t` of items whose
recorded price changes estimates `λ` whatever the age distribution of prices. -/
theorem monthly_change_prob {φ a : ℝ} (hφ : 0 < φ) (ha : 0 ≤ a) :
    (expMeasure φ).real (Set.Ioc a (a + 1)) / (expMeasure φ).real (Set.Ioi a) = monthlyFreq φ := by
  rw [cond_change_prob hφ ha zero_le_one, mul_one, monthlyFreq]

/-- Galí (2015), Ex. 3.1(c), p. 89: estimating `φ`: the observed monthly frequency `λ < 1`
equals `1 − e^{−φ}` if and only if `φ = −log(1 − λ)`. -/
theorem lambda_eq_iff {φ lam : ℝ} (hl : lam < 1) :
    monthlyFreq φ = lam ↔ φ = -Real.log (1 - lam) := by
  rw [monthlyFreq]
  constructor
  · intro h
    have : Real.exp (-φ) = 1 - lam := by linarith
    rw [← this, Real.log_exp, neg_neg]
  · intro h
    rw [h, neg_neg, Real.exp_log (by linarith)]
    ring

/-- Galí (2015), Ex. 3.1(c), p. 89: the monthly frequency lies in `(0, 1)` for `φ > 0`. -/
theorem monthlyFreq_mem {φ : ℝ} (hφ : 0 < φ) : 0 < monthlyFreq φ ∧ monthlyFreq φ < 1 := by
  rw [monthlyFreq]
  constructor
  · have : Real.exp (-φ) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_zero] at this
    linarith
  · have := Real.exp_pos (-φ)
    linarith

/-- Galí (2015), Ex. 3.1(c), p. 89: the raw monthly frequency `λ` understates the rate `φ`
(`1 − e^{−φ} < φ` for `φ ≠ 0`), because a price may change more than once in a month. -/
theorem lambda_lt_phi {φ : ℝ} (hφ : φ ≠ 0) : monthlyFreq φ < φ := by
  rw [monthlyFreq]
  have := Real.add_one_lt_exp (neg_ne_zero.mpr hφ)
  linarith

/-- Galí (2015), Ex. 3.1(d), p. 89: the probability that a price survives a quarter (three
months), whatever its age `a ≥ 0`, is `θ = e^{−3φ} = (1 − λ)³`. This is the quarterly Calvo
parameter. -/
theorem quarterly_survival {φ a : ℝ} (hφ : 0 < φ) (ha : 0 ≤ a) :
    (expMeasure φ).real (Set.Ioi (a + 3)) / (expMeasure φ).real (Set.Ioi a)
      = Real.exp (-(3 * φ)) ∧ Real.exp (-(3 * φ)) = (1 - monthlyFreq φ) ^ 3 := by
  constructor
  · rw [memoryless hφ ha (by norm_num), survival hφ (by norm_num), mul_comm]
  · rw [monthlyFreq, sub_sub_cancel, ← Real.exp_nat_mul]
    norm_num

/-- Galí (2015), Ex. 3.1(d), p. 89: the quarterly Calvo parameter `θ = (1 − λ)³` calibrated
from a monthly frequency `λ ∈ (0, 1]`. -/
noncomputable def quarterlyCalvo (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) : CalvoParam where
  θ := (1 - lam) ^ 3
  nonneg := pow_nonneg (by linarith) 3
  lt_one := by
    have ha : 0 ≤ 1 - lam := by linarith
    have hb : 1 - lam < 1 := by linarith
    calc (1 - lam) ^ 3 ≤ 1 - lam := pow_le_of_le_one ha hb.le (by norm_num)
      _ < 1 := hb

/-- Galí (2015), Ex. 3.1(d), p. 89: calibrated from `λ = 1 − e^{−φ}`, the quarterly Calvo
parameter equals the quarterly survival probability `e^{−3φ}`. -/
theorem quarterlyCalvo_theta {φ : ℝ} (hφ : 0 < φ) :
    (quarterlyCalvo (monthlyFreq φ) (monthlyFreq_mem hφ).1 (monthlyFreq_mem hφ).2.le).θ
      = Real.exp (-(3 * φ)) :=
  (quarterly_survival hφ le_rfl).2.symm

/-- Galí (2015), Ex. 3.1(d), p. 89, with p. 55: the mean price duration in quarters implied
by the calibrated Calvo parameter, `1/(1 − θ) = 1/(1 − e^{−3φ})`. -/
theorem quarterlyCalvo_mean_duration {φ : ℝ} (hφ : 0 < φ) :
    ∑' k : ℕ, ((k : ℝ) + 1) * durationProb
      (quarterlyCalvo (monthlyFreq φ) (monthlyFreq_mem hφ).1 (monthlyFreq_mem hφ).2.le).θ k
      = 1 / (1 - Real.exp (-(3 * φ))) := by
  rw [CalvoParam.mean_duration, quarterlyCalvo_theta hφ]

end Gali.BasicNewKeynesianModel.Ex3_1
