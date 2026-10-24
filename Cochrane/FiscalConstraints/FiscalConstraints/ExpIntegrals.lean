/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exponential integrals on `[0, ∞)`

Infrastructure for Cochrane (2023), Chapter 6, *Fiscal constraints*, §6.1–§6.4 (pp. 189–199).
Every present value in the continuous-time parts of the chapter is an improper integral
`∫₀^∞ e^{-a u} f(u) du`: the present value of tax revenue (p. 189), the value of debt (6.2)
(p. 191) and (6.3) (p. 195), and the forward solution of the debt-to-GDP equation (6.4)
(p. 196). This module collects the exact facts used.

## Main results

* `integrableOn_exp_neg_mul`, `integral_exp_neg_mul_Ioi`, `integral_exp_neg_mul_Ioi_zero`:
  `∫₀^∞ e^{-a u} du = 1/a` for `a > 0`.
* `not_integrableOn_exp_neg_mul`: for `a ≤ 0` and `c ≠ 0` the integrand `c e^{-a u}` is not
  integrable on `(0, ∞)` (the present value is genuinely infinite, not a junk value).
* `integral_exp_growth`, `not_integrableOn_exp_growth`: the growing-stream present value
  `∫₀^∞ e^{-r u} c e^{g u} du = c/(r - g)` iff `r > g` (pp. 189, 191, 195).
* `integrableOn_exp_mul_bdd`, `abs_integral_exp_mul_le`: discounted bounded continuous streams
  are integrable, with the bound `M e^{-a c}/a`.
* `integral_Ioi_comp_add`, `integral_exp_shift`: translation of `(0, ∞)` to `(t, ∞)`.
* `integral_Ioi_sub_interval`: `∫_{(0,∞)} - ∫_0^t = ∫_{(t,∞)}`.
* `intervalIntegral_exp_neg_mul`: `∫₀^T e^{-a u} du = (1 - e^{-aT})/a`.
* `tendsto_const_mul_exp_zero_iff`, `tendsto_const_mul_exp_atTop`: `K e^{aT} → 0` iff `a < 0`,
  and `→ ∞` for `a > 0` (p. 200).
* `tvc_of_bounded`: a bounded path satisfies `e^{-a(T-t)} w_T → 0` for `a > 0` (p. 201).
-/

namespace Cochrane.FiscalConstraints.ExpIntegrals

open Real MeasureTheory Filter Topology

/-- Cochrane (2023), §6.1, p. 189: the discount factor `e^{-a u}` is integrable on `(c, ∞)` when
`a > 0`. -/
theorem integrableOn_exp_neg_mul {a : ℝ} (ha : 0 < a) (c : ℝ) :
    IntegrableOn (fun u : ℝ => exp (-a * u)) (Set.Ioi c) :=
  integrableOn_exp_mul_Ioi (by linarith) c

/-- Cochrane (2023), §6.1, p. 189: `∫_c^∞ e^{-a u} du = e^{-a c}/a` for `a > 0`. -/
theorem integral_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∫ u in Set.Ioi c, exp (-a * u) = exp (-a * c) / a := by
  rw [integral_exp_mul_Ioi (by linarith) c, neg_div, div_neg, neg_neg]

/-- Cochrane (2023), §6.1, p. 189: `∫₀^∞ e^{-a u} du = 1/a` for `a > 0`. -/
theorem integral_exp_neg_mul_Ioi_zero {a : ℝ} (ha : 0 < a) :
    ∫ u in Set.Ioi (0 : ℝ), exp (-a * u) = 1 / a := by
  rw [integral_exp_neg_mul_Ioi ha 0, mul_zero, exp_zero]

/-- Cochrane (2023), §6.1, p. 189 and §6.4, p. 195: for `a ≤ 0` and `c ≠ 0` the stream
`c e^{-a u}` is NOT integrable on `(0, ∞)`: its present value is infinite. -/
theorem not_integrableOn_exp_neg_mul {a : ℝ} (ha : a ≤ 0) {c : ℝ} (hc : c ≠ 0) :
    ¬ IntegrableOn (fun u : ℝ => c * exp (-a * u)) (Set.Ioi 0) := by
  intro h
  have h1 : IntegrableOn (fun _ : ℝ => c) (Set.Ioi 0) := by
    refine Integrable.mono h aestronglyMeasurable_const ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have hu' : (0 : ℝ) < u := hu
    have he : 1 ≤ exp (-a * u) := one_le_exp (by nlinarith)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
    nlinarith [abs_nonneg c]
  rw [integrableOn_const_iff] at h1
  rcases h1 with h1 | h1
  · exact hc (enorm_eq_zero.1 h1)
  · rw [Real.volume_Ioi] at h1
    exact lt_irrefl _ h1

/-- Cochrane (2023), §6.1, p. 189, and (6.2), p. 191: the integrand of the present value of a
stream `c e^{g u}` discounted at `r` is `c e^{-(r-g)u}`. -/
theorem exp_growth_eq (r g c u : ℝ) :
    exp (-r * u) * (c * exp (g * u)) = c * exp (-(r - g) * u) := by
  rw [mul_left_comm, ← exp_add]
  ring_nf

/-- Cochrane (2023), §6.1, p. 189: for `r > g` a stream growing at `g` has an integrable
present value. -/
theorem integrableOn_exp_growth {r g : ℝ} (h : g < r) (c : ℝ) :
    IntegrableOn (fun u : ℝ => exp (-r * u) * (c * exp (g * u))) (Set.Ioi 0) := by
  simp_rw [exp_growth_eq]
  exact (integrableOn_exp_neg_mul (by linarith) 0).const_mul c

/-- Cochrane (2023), §6.1, p. 189, (6.2), p. 191, and (6.3), p. 195: for `r > g`,
`∫₀^∞ e^{-r u} c e^{g u} du = c/(r - g)`. -/
theorem integral_exp_growth {r g : ℝ} (h : g < r) (c : ℝ) :
    ∫ u in Set.Ioi (0 : ℝ), exp (-r * u) * (c * exp (g * u)) = c / (r - g) := by
  simp_rw [exp_growth_eq]
  rw [integral_const_mul, integral_exp_neg_mul_Ioi_zero (by linarith)]
  ring

/-- Cochrane (2023), §6.4, p. 195: for `r ≤ g` and `c ≠ 0` the present value of a stream
growing at `g` is infinite (the integrand is not integrable). -/
theorem not_integrableOn_exp_growth {r g : ℝ} (h : r ≤ g) {c : ℝ} (hc : c ≠ 0) :
    ¬ IntegrableOn (fun u : ℝ => exp (-r * u) * (c * exp (g * u))) (Set.Ioi 0) := by
  simp_rw [exp_growth_eq]
  exact not_integrableOn_exp_neg_mul (by linarith) hc

/-- Cochrane (2023), §6.4.1, p. 196: a bounded continuous surplus stream discounted at `a > 0`
is integrable on `(c, ∞)`. -/
theorem integrableOn_exp_mul_bdd {a M : ℝ} (ha : 0 < a) {σ : ℝ → ℝ} (hσ : Continuous σ)
    (hM : ∀ u, |σ u| ≤ M) (c : ℝ) :
    IntegrableOn (fun u => exp (-a * u) * σ u) (Set.Ioi c) := by
  have := Integrable.bdd_mul (integrableOn_exp_neg_mul ha c) hσ.aestronglyMeasurable
    (c := M) (ae_of_all _ fun u => (Real.norm_eq_abs _).le.trans (hM u))
  exact Integrable.congr this (ae_of_all _ fun u => mul_comm _ _)

/-- Cochrane (2023), §6.4.1, p. 196: `|∫_c^∞ e^{-a u} σ(u) du| ≤ M e^{-a c}/a` when `|σ| ≤ M`. -/
theorem abs_integral_exp_mul_le {a M : ℝ} (ha : 0 < a) {σ : ℝ → ℝ}
    (hM : ∀ u, |σ u| ≤ M) (c : ℝ) :
    |∫ u in Set.Ioi c, exp (-a * u) * σ u| ≤ M * (exp (-a * c) / a) := by
  have hint : IntegrableOn (fun u : ℝ => M * exp (-a * u)) (Set.Ioi c) :=
    (integrableOn_exp_neg_mul ha c).const_mul M
  have := norm_integral_le_of_norm_le (f := fun u => exp (-a * u) * σ u) hint
    (ae_of_all _ fun u => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hM u) (exp_pos _).le)
  rw [Real.norm_eq_abs, integral_const_mul, integral_exp_neg_mul_Ioi ha c] at this
  exact this

/-- Cochrane (2023), §6.4.1, p. 196 (infrastructure): translating `(0, ∞)` to `(t, ∞)`,
`∫₀^∞ f(t + u) du = ∫_t^∞ f(v) dv` (no integrability needed: both sides are Bochner integrals
of translates). -/
theorem integral_Ioi_comp_add (f : ℝ → ℝ) (t : ℝ) :
    ∫ u in Set.Ioi (0 : ℝ), f (t + u) = ∫ v in Set.Ioi t, f v := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self (μ := volume) (fun v => Set.indicator (Set.Ioi t) f v) t]
  congr 1
  funext u
  by_cases hu : 0 < u
  · rw [Set.indicator_of_mem (show u ∈ Set.Ioi (0 : ℝ) from hu),
      Set.indicator_of_mem (show u + t ∈ Set.Ioi t by simp [hu]), add_comm]
  · rw [Set.indicator_of_notMem (show u ∉ Set.Ioi (0 : ℝ) from hu),
      Set.indicator_of_notMem (show u + t ∉ Set.Ioi t by simpa using hu)]

/-- Cochrane (2023), §6.4.1, p. 196: the forward present value at date `t`,
`∫₀^∞ e^{-a u} σ(t + u) du = e^{a t} ∫_t^∞ e^{-a v} σ(v) dv`. -/
theorem integral_exp_shift (a t : ℝ) (σ : ℝ → ℝ) :
    ∫ u in Set.Ioi (0 : ℝ), exp (-a * u) * σ (t + u) =
      exp (a * t) * ∫ v in Set.Ioi t, exp (-a * v) * σ v := by
  rw [← integral_const_mul,
    ← integral_Ioi_comp_add (fun v => exp (a * t) * (exp (-a * v) * σ v)) t]
  congr 1
  funext u
  rw [← mul_assoc, ← exp_add]
  ring_nf

/-- Cochrane (2023), §6.4.1, p. 196 (infrastructure): `∫_{(0,∞)} f - ∫_0^t f = ∫_{(t,∞)} f` for
`f` integrable on every `(c, ∞)`. -/
theorem integral_Ioi_sub_interval {f : ℝ → ℝ} (hf : ∀ c, IntegrableOn f (Set.Ioi c)) (t : ℝ) :
    (∫ v in Set.Ioi (0 : ℝ), f v) - ∫ v in (0 : ℝ)..t, f v = ∫ v in Set.Ioi t, f v := by
  rw [← intervalIntegral.integral_Ioi_sub_Ioi' (hf 0) (hf t)]
  exact sub_sub_cancel (∫ v in Set.Ioi (0 : ℝ), f v) (∫ v in Set.Ioi t, f v)

/-- Cochrane (2023), §6.4.2, p. 198 (infrastructure): `∫₀^T e^{-a u} du = (1 - e^{-a T})/a` for
`a ≠ 0`. -/
theorem intervalIntegral_exp_neg_mul {a : ℝ} (ha : a ≠ 0) (T : ℝ) :
    ∫ u in (0 : ℝ)..T, exp (-a * u) = (1 - exp (-a * T)) / a := by
  have hna : -a ≠ 0 := neg_ne_zero.2 ha
  rw [intervalIntegral.integral_comp_mul_left (fun u => exp u) hna, integral_exp, mul_zero,
    exp_zero, smul_eq_mul]
  field_simp
  ring

/-- Cochrane (2023), §6.4.4, p. 200 (infrastructure, moved here from `GrowthTheoryTVC`):
`K e^{a T} → 0` as `T → ∞` iff `a < 0`, for `K > 0`. -/
theorem tendsto_const_mul_exp_zero_iff {K a : ℝ} (hK : 0 < K) :
    Tendsto (fun T : ℝ => K * Real.exp (a * T)) atTop (𝓝 0) ↔ a < 0 := by
  constructor
  · intro h
    by_contra ha
    push Not at ha
    have hge : ∀ T : ℝ, 0 ≤ T → K ≤ K * Real.exp (a * T) := fun T hT => by
      have : 1 ≤ Real.exp (a * T) := Real.one_le_exp (mul_nonneg ha hT)
      nlinarith
    have hev : ∀ᶠ T in atTop, K ≤ K * Real.exp (a * T) :=
      (eventually_ge_atTop 0).mono hge
    have := ge_of_tendsto h hev
    linarith
  · intro ha
    have h1 : Tendsto (fun T : ℝ => a * T) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg ha
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul K

/-- Cochrane (2023), §6.4.4, p. 200 (infrastructure, moved here from `GrowthTheoryTVC`):
for `K > 0` and `a > 0`, `K e^{a T} → ∞`. -/
theorem tendsto_const_mul_exp_atTop {K a : ℝ} (hK : 0 < K) (ha : 0 < a) :
    Tendsto (fun T : ℝ => K * Real.exp (a * T)) atTop atTop := by
  have h1 : Tendsto (fun T : ℝ => a * T) atTop atTop := tendsto_id.const_mul_atTop ha
  exact (Real.tendsto_exp_atTop.comp h1).const_mul_atTop hK

/-- Cochrane (2023), §6.4.5, p. 201 (infrastructure, moved here from `MoneyLiquidity`):
with `a > 0`, a bounded solution satisfies the transversality condition
`e^{−a(T−t)} w_T → 0`. -/
theorem tvc_of_bounded {a C : ℝ} (ha : 0 < a) {w : ℝ → ℝ} (hC : ∀ τ, |w τ| ≤ C) (t : ℝ) :
    Tendsto (fun T => Real.exp (-a * (T - t)) * w T) atTop (𝓝 0) := by
  have h1 : Tendsto (fun T => -a * (T - t)) atTop atBot := by
    have : Tendsto (fun T : ℝ => T - t) atTop atTop := tendsto_atTop_add_const_right _ _
      tendsto_id
    exact this.const_mul_atTop_of_neg (by linarith)
  have h2 : Tendsto (fun T => Real.exp (-a * (T - t))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp h1
  have h3 : Tendsto (fun T => Real.exp (-a * (T - t)) * C) atTop (𝓝 0) := by
    have := h2.mul_const C
    rwa [zero_mul] at this
  refine squeeze_zero_norm (fun T => ?_) h3
  rw [norm_mul, Real.norm_eq_abs, Real.abs_exp, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hC T) (Real.exp_pos _).le

end Cochrane.FiscalConstraints.ExpIntegrals
