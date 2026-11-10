/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.TidyR7OUPath

/-!
# Restarting the OU surplus and the debt (6.5) at a date

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.1, p. 197, with the
debt equation (6.4)–(6.5), p. 196. Deterministic, for an arbitrary continuous driving path `w`.

Restarted at date `t`, the OU surplus and the debt `ḃ = ab − s` are the same objects driven by
the shifted path `w^t(r) = w(t + r) − w(t)` (`shiftPath`) from the date-`t` values:

* `ouStep_eq_ouNoise`, **`ouPath_restart`**: `s_{t+h} = ouPath(s_t, w^t)(h)`;
* **`ouDebt_restart`**: `b_{t+h} = ouDebt(s_t, b_t, w^t)(h)`;
* **`ouDebt_succ`**: over one period,
  `b_{t+1} = e^a b_t − s̄·A − D·(s_t − s̄) − σ∫_0^1 w^t(r)k_1(r)dr` with the constants
  `debtA`, `debtD`; `shift_integral_eq` writes the noise term in the by-parts Wiener form on
  `[t, t + 1]` with the integrand `G_1(· − t)`;
* `debtKernel_shift`, `debtG_shift`: the debt kernel depends only on `t − r`;
* **`integral_debtG_sq_le`**: `∫_0^1 G_1² ≤ ∫_0^t G_t²` for `t ≥ 1` (the debt variance at `t ≥ 1`
  is at least the one-period variance);
* **`abs_debtMean_le`**: for `a = r − g < 0` and `η > 0`, the mean debt path is bounded,
  `|debtMean_t| ≤ |b_0| + |s̄|/(−a) + |s_0 − s̄|/η` for every `t ≥ 0`.
-/

namespace Cochrane.FiscalConstraints.TidyR8OURestart

open Real MeasureTheory Filter Topology
open Cochrane.FiscalConstraints.TidyR7OUPath Cochrane.FiscalConstraints.LinearODE

variable {w : ℝ → ℝ}

/-- Cochrane (2023), p. 197: the driving path restarted at date `t`, `w^t(r) = w(t + r) − w(t)`. -/
def shiftPath (w : ℝ → ℝ) (t r : ℝ) : ℝ := w (t + r) - w t

/-- Cochrane (2023), p. 197: the shifted path is continuous. -/
theorem continuous_shiftPath (hw : Continuous w) (t : ℝ) : Continuous (shiftPath w t) := by
  unfold shiftPath
  fun_prop

/-- Cochrane (2023), p. 197 (tool): `η∫_0^h e^{ηu} du = e^{ηh} − 1`.
`ExpIntegrals.intervalIntegral_exp_neg_mul` at `a = −η`, also covering `η = 0`. -/
theorem integral_exp_mul_eta (η h : ℝ) :
    η * ∫ u in (0 : ℝ)..h, exp (η * u) = exp (η * h) - 1 := by
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) h, HasDerivAt (fun u => exp (η * u)) (exp (η * x) * η) x :=
    fun x _ => by simpa using ((hasDerivAt_id' x).const_mul η).exp
  rw [← intervalIntegral.integral_const_mul]
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun u => exp (η * u) * η).intervalIntegrable 0 h)
  rw [show (fun u => η * exp (η * u)) = fun u => exp (η * u) * η by funext u; ring, this]
  simp

/-- Cochrane (2023), p. 197: the OU innovation over `[t, t + h]` is the OU noise of the shifted
path, `ouStep η w t h = ouNoise η w^t h`.
Compare `TidyR7OUPath.ouPath_step`. -/
theorem ouStep_eq_ouNoise (η : ℝ) (hw : Continuous w) (t h : ℝ) :
    ouStep η w t h = ouNoise η (shiftPath w t) h := by
  have hI : (∫ u in t..(t + h), exp (η * u) * w u)
      = exp (η * t) * ∫ u in (0 : ℝ)..h, exp (η * u) * w (t + u) := by
    have h1 := intervalIntegral.integral_comp_add_right (fun u => exp (η * u) * w u) (a := 0)
      (b := h) t
    rw [zero_add, add_comm h t] at h1
    rw [← h1, ← intervalIntegral.integral_const_mul]
    congr 1
    funext u
    rw [add_comm u t, mul_add, exp_add]
    ring
  have hS : (∫ u in (0 : ℝ)..h, exp (η * u) * shiftPath w t u)
      = (∫ u in (0 : ℝ)..h, exp (η * u) * w (t + u)) - w t * ∫ u in (0 : ℝ)..h, exp (η * u) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun u => exp (η * u) * w (t + u)).intervalIntegrable 0 h)
      ((by fun_prop : Continuous fun u => w t * exp (η * u)).intervalIntegrable 0 h)]
    congr 1
    funext u
    simp only [shiftPath]
    ring
  have he1 : exp (-η * (t + h)) * exp (η * t) = exp (-η * h) := by rw [← exp_add]; ring_nf
  have he2 : exp (-η * h) * exp (η * h) = 1 := by rw [← exp_add]; ring_nf; exact exp_zero
  have hE := integral_exp_mul_eta η h
  simp only [ouStep, ouNoise, ouPrim, hI, hS]
  simp only [shiftPath]
  linear_combination (-(η * ∫ u in (0 : ℝ)..h, exp (η * u) * w (t + u))) * he1
    - (w t) * exp (-η * h) * hE - (w t) * he2

/-- **Cochrane (2023), p. 197: the OU surplus restarts at any date**: `s_{t+h}` is the OU
surplus from `s_t` driven by the shifted path `w^t`.
Generalises `TidyR7OUPath.ouPath_step` (the whole path restarts). -/
theorem ouPath_restart (η sbar s0 σ : ℝ) (hw : Continuous w) (t h : ℝ) :
    ouPath η sbar s0 σ w (t + h)
      = ouPath η sbar (ouPath η sbar s0 σ w t) σ (shiftPath w t) h := by
  have h1 := ouPath_step (η := η) (sbar := sbar) (s0 := s0) (σ := σ) hw t h
  rw [ouStep_eq_ouNoise η hw] at h1
  simp only [ouPath, ouMean] at h1 ⊢
  linarith

/-- **Cochrane (2023), (6.4)–(6.5), pp. 196–197: debt restarts at any date**: `b_{t+h}` is the
debt from `(s_t, b_t)` driven by the shifted path `w^t` (uniqueness for `ḃ = ab − s`,
`LinearODE.vocFrom_eq_of_global`). -/
theorem ouDebt_restart (a η sbar s0 σ b0 : ℝ) (hw : Continuous w) (t h : ℝ) :
    ouDebt a η sbar s0 σ b0 w (t + h)
      = ouDebt a η sbar (ouPath η sbar s0 σ w t) σ (ouDebt a η sbar s0 σ b0 w t)
          (shiftPath w t) h := by
  set f : ℝ → ℝ := fun τ => ouPath η sbar s0 σ w (t + τ) with hf
  have hfc : Continuous f :=
    (continuous_ouPath η sbar s0 σ hw).comp (continuous_const.add continuous_id)
  have h1 : ∀ τ, HasDerivAt (fun τ => ouDebt a η sbar s0 σ b0 w (t + τ))
      (a * ouDebt a η sbar s0 σ b0 w (t + τ) - f τ) τ := fun τ =>
    (ouDebt_hasDerivAt a b0 hw (t + τ)).comp_const_add t τ
  have hf2 : ouPath η sbar (ouPath η sbar s0 σ w t) σ (shiftPath w t) = f := by
    funext τ
    exact (ouPath_restart η sbar s0 σ hw t τ).symm
  have h2 : ∀ τ, HasDerivAt (ouDebt a η sbar (ouPath η sbar s0 σ w t) σ
      (ouDebt a η sbar s0 σ b0 w t) (shiftPath w t))
      (a * ouDebt a η sbar (ouPath η sbar s0 σ w t) σ (ouDebt a η sbar s0 σ b0 w t)
        (shiftPath w t) τ - f τ) τ := fun τ => by
    have := ouDebt_hasDerivAt (η := η) (sbar := sbar) (s0 := ouPath η sbar s0 σ w t) (σ := σ)
      a (ouDebt a η sbar s0 σ b0 w t) (continuous_shiftPath hw t) τ
    rwa [hf2] at this
  have e1 := vocFrom_eq_of_global h1 hfc 0 h
  have e2 := vocFrom_eq_of_global h2 hfc 0 h
  simp only [add_zero] at e1
  rw [e1, e2, ouDebt_zero]

/-- Cochrane (2023), (6.5), p. 197: the one-period response of debt to the mean surplus,
`A = e^a∫_0^1 e^{−au}du`. -/
noncomputable def debtA (a : ℝ) : ℝ := exp a * ∫ u in (0 : ℝ)..1, exp (-a * u)

/-- Cochrane (2023), (6.5), p. 197: the one-period response of debt to the surplus gap
`s_t − s̄`, `D = e^a∫_0^1 e^{−au}e^{−ηu}du`. -/
noncomputable def debtD (a η : ℝ) : ℝ := exp a * ∫ u in (0 : ℝ)..1, exp (-a * u) * exp (-η * u)

/-- Cochrane (2023), (6.5), p. 197: the one-period mean debt is affine in `(s_0, b_0)`,
`debtMean_1 = e^a b_0 − s̄A − (s_0 − s̄)D`. -/
theorem debtMean_one (a η sbar s0 b0 : ℝ) :
    debtMean a η sbar s0 b0 1 = exp a * b0 - sbar * debtA a - (s0 - sbar) * debtD a η := by
  have i1 := (by fun_prop : Continuous fun u => exp (-a * u) * sbar).intervalIntegrable
    (μ := volume) 0 1
  have i2 := (by fun_prop : Continuous fun u =>
    exp (-a * u) * exp (-η * u) * (s0 - sbar)).intervalIntegrable (μ := volume) 0 1
  have e : (fun u => exp (-a * u) * ouMean η sbar s0 u)
      = fun u => exp (-a * u) * sbar + exp (-a * u) * exp (-η * u) * (s0 - sbar) := by
    funext u
    simp only [ouMean]
    ring
  simp only [debtMean, vocFrom, debtA, debtD, e]
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_mul_const]
  simp only [mul_zero, exp_zero, one_mul, mul_one]
  ring

/-- **Cochrane (2023), (6.4)–(6.5), pp. 196–197: debt over one period.** On every continuous
path, `b_{t+1} = e^a b_t − s̄A − D(s_t − s̄) − σ∫_0^1 w^t(r)k_1(r)dr`. -/
theorem ouDebt_succ (a η sbar s0 σ b0 : ℝ) (hw : Continuous w) (t : ℝ) :
    ouDebt a η sbar s0 σ b0 w (t + 1)
      = exp a * ouDebt a η sbar s0 σ b0 w t - sbar * debtA a
        - debtD a η * (ouPath η sbar s0 σ w t - sbar)
        - σ * ∫ r in (0 : ℝ)..1, shiftPath w t r * debtKernel a η 1 r := by
  rw [ouDebt_restart a η sbar s0 σ b0 hw t 1, ouDebt_eq a _ (continuous_shiftPath hw t),
    debtMean_one, debtNoise_eq_integral a η (continuous_shiftPath hw t)]
  ring

/-- Cochrane (2023), (6.5), p. 197: the one-period debt noise in by-parts Wiener form on
`[t, t + 1]` with integrand `h(u) = G_1(u − t)` (`h(t + 1) = 0`, `h' = −k_1(· − t)`). -/
theorem shift_integral_eq (a η : ℝ) (hw : Continuous w) (t : ℝ) :
    ∫ r in (0 : ℝ)..1, shiftPath w t r * debtKernel a η 1 r
      = debtG a η 1 ((t + 1) - t) * w (t + 1) - debtG a η 1 (t - t) * w t
        - ∫ u in t..(t + 1), w u * -debtKernel a η 1 (u - t) := by
  have hk := continuous_debtKernel a η 1
  have hG0 : debtG a η 1 0 = ∫ u in (0 : ℝ)..1, debtKernel a η 1 u := by
    rw [debtG, intervalIntegral.integral_symm, neg_neg]
  have hsub : (∫ u in t..(t + 1), w u * -debtKernel a η 1 (u - t))
      = -∫ r in (0 : ℝ)..1, w (t + r) * debtKernel a η 1 r := by
    have h1 := intervalIntegral.integral_comp_add_right
      (fun u => w u * -debtKernel a η 1 (u - t)) (a := 0) (b := 1) t
    rw [zero_add, add_comm 1 t] at h1
    rw [← h1, ← intervalIntegral.integral_neg]
    congr 1
    funext r
    change w (r + t) * -debtKernel a η 1 (r + t - t) = -(w (t + r) * debtKernel a η 1 r)
    rw [add_sub_cancel_right, add_comm r t]
    ring
  have hsplit : (∫ r in (0 : ℝ)..1, shiftPath w t r * debtKernel a η 1 r)
      = (∫ r in (0 : ℝ)..1, w (t + r) * debtKernel a η 1 r)
        - w t * ∫ r in (0 : ℝ)..1, debtKernel a η 1 r := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun r => w (t + r) * debtKernel a η 1 r).intervalIntegrable 0 1)
      ((by fun_prop : Continuous fun r => w t * debtKernel a η 1 r).intervalIntegrable 0 1)]
    congr 1
    funext r
    simp only [shiftPath]
    ring
  rw [hsplit, hsub, add_sub_cancel_left, sub_self, debtG_self, hG0]
  ring

/-! ### Stationarity of the debt kernel -/

/-- Cochrane (2023), (6.5), p. 197 (tool): `F_c(t + δ) − F_c(u + δ) = e^{−cδ}(F_c(t) − F_c(u))`. -/
theorem debtF_shift (c t u δ : ℝ) :
    debtF c (t + δ) - debtF c (u + δ) = exp (-c * δ) * (debtF c t - debtF c u) := by
  have hc : ∀ x y : ℝ, IntervalIntegrable (fun v => exp (-c * v)) volume x y :=
    fun x y => (by fun_prop : Continuous fun v => exp (-c * v)).intervalIntegrable x y
  simp only [debtF]
  rw [intervalIntegral.integral_interval_sub_left (hc 0 _) (hc 0 _),
    intervalIntegral.integral_interval_sub_left (hc 0 _) (hc 0 _),
    ← intervalIntegral.integral_comp_add_right (fun v => exp (-c * v)) δ,
    ← intervalIntegral.integral_const_mul]
  congr 1
  funext v
  rw [← exp_add]
  ring_nf

/-- Cochrane (2023), (6.5), p. 197: the debt kernel is stationary,
`k_{t+δ}(u + δ) = k_t(u)`. -/
theorem debtKernel_shift (a η t u δ : ℝ) :
    debtKernel a η (t + δ) (u + δ) = debtKernel a η t u := by
  have hF := debtF_shift (a + η) t u δ
  have e1 : exp (a * (t + δ)) * exp (-a * (u + δ)) = exp (a * t) * exp (-a * u) := by
    rw [← exp_add, ← exp_add]; ring_nf
  have e2 : exp (a * (t + δ)) * exp (η * (u + δ)) * exp (-(a + η) * δ)
      = exp (a * t) * exp (η * u) := by
    rw [← exp_add, ← exp_add, ← exp_add]; ring_nf
  simp only [debtKernel]
  linear_combination e1 - η * exp (a * (t + δ)) * exp (η * (u + δ)) * hF
    - η * (debtF (a + η) t - debtF (a + η) u) * e2

/-- Cochrane (2023), (6.5), p. 197: `G_{t+δ}(r + δ) = G_t(r)`. -/
theorem debtG_shift (a η t r δ : ℝ) : debtG a η (t + δ) (r + δ) = debtG a η t r := by
  simp only [debtG]
  rw [← intervalIntegral.integral_comp_add_right (fun u => debtKernel a η (t + δ) u) δ]
  simp only [debtKernel_shift]

/-- **Cochrane (2023), (6.5), p. 197: the debt variance does not fall below its one-period
value**: `∫_0^1 G_1² ≤ ∫_0^t G_t²` for `t ≥ 1`. -/
theorem integral_debtG_sq_le (a η : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    ∫ r in (0 : ℝ)..1, debtG a η 1 r ^ 2 ≤ ∫ r in (0 : ℝ)..t, debtG a η t r ^ 2 := by
  have hc : ∀ x y : ℝ, IntervalIntegrable (fun r => debtG a η t r ^ 2) volume x y :=
    fun x y => ((continuous_debtG a η t).pow 2).intervalIntegrable x y
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc 0 (t - 1)) (hc (t - 1) t)]
  have h0 : 0 ≤ ∫ r in (0 : ℝ)..(t - 1), debtG a η t r ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun r _ => sq_nonneg _
  have h1 : (∫ r in (t - 1)..t, debtG a η t r ^ 2) = ∫ r in (0 : ℝ)..1, debtG a η 1 r ^ 2 := by
    have := intervalIntegral.integral_comp_add_right (fun r => debtG a η t r ^ 2) (a := 0)
      (b := 1) (t - 1)
    rw [zero_add, show (1 : ℝ) + (t - 1) = t by ring] at this
    rw [← this]
    congr 1
    funext r
    have e := debtG_shift a η 1 r (t - 1)
    rw [show (1 : ℝ) + (t - 1) = t by ring] at e
    rw [e]
  linarith

/-! ### The mean debt path is bounded when `r < g` -/

/-- Cochrane (2023), p. 197 (tool): for `c > 0` and `t ≥ 0`,
`0 ≤ ∫_0^t e^{−cu}du ≤ 1/c`.
From `ExpIntegrals.intervalIntegral_exp_neg_mul`. -/
theorem integral_exp_neg_le {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ∫ u in (0 : ℝ)..t, exp (-c * u) ∧ ∫ u in (0 : ℝ)..t, exp (-c * u) ≤ 1 / c := by
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun u => -exp (-c * u) / c) (exp (-c * x)) x := fun x _ => by
    have h := (((hasDerivAt_id' x).const_mul (-c)).exp.neg).div_const c
    refine h.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun u => exp (-c * u)).intervalIntegrable 0 t)]
  have h1 : exp (-c * t) ≤ 1 := exp_le_one_iff.2 (by nlinarith)
  have h2 : 0 < exp (-c * t) := exp_pos _
  simp only [mul_zero, exp_zero]
  constructor
  · rw [show -exp (-c * t) / c - -1 / c = (1 - exp (-c * t)) / c by ring]
    exact div_nonneg (by linarith) hc.le
  · rw [show -exp (-c * t) / c - -1 / c = (1 - exp (-c * t)) / c by ring]
    exact div_le_div_of_nonneg_right (by linarith) hc.le

/-- **Cochrane (2023), (6.5), p. 197: with permanent `r < g` the mean debt path is bounded.**
For `a = r − g < 0`, `η > 0` and `t ≥ 0`,
`|debtMean_t| ≤ |b_0| + |s̄|/(−a) + |s_0 − s̄|/η`. -/
theorem abs_debtMean_le {a η : ℝ} (ha : a < 0) (hη : 0 < η) (sbar s0 b0 : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    |debtMean a η sbar s0 b0 t| ≤ |b0| + |sbar| / (-a) + |s0 - sbar| / η := by
  have i1 := (by fun_prop : Continuous fun u => exp (-a * u) * sbar).intervalIntegrable
    (μ := volume) 0 t
  have i2 := (by fun_prop : Continuous fun u =>
    exp (-a * u) * exp (-η * u) * (s0 - sbar)).intervalIntegrable (μ := volume) 0 t
  have e : (fun u => exp (-a * u) * ouMean η sbar s0 u)
      = fun u => exp (-a * u) * sbar + exp (-a * u) * exp (-η * u) * (s0 - sbar) := by
    funext u
    simp only [ouMean]
    ring
  -- the first integral: `e^{at}∫_0^t e^{−au} = (1 − e^{at})/(−a)`
  have hA : exp (a * t) * ∫ u in (0 : ℝ)..t, exp (-a * u) = (1 - exp (a * t)) / (-a) := by
    have ha0 : a ≠ 0 := ha.ne
    have hd : ∀ x ∈ Set.uIcc (0 : ℝ) t,
        HasDerivAt (fun u => -exp (-a * u) / a) (exp (-a * x)) x := fun x _ => by
      have h := (((hasDerivAt_id' x).const_mul (-a)).exp.neg).div_const a
      refine h.congr_deriv ?_
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun u => exp (-a * u)).intervalIntegrable 0 t)]
    have he : exp (a * t) * exp (-a * t) = 1 := by rw [← exp_add]; ring_nf; exact exp_zero
    simp only [mul_zero, exp_zero]
    field_simp
    simp only [neg_mul] at he ⊢
    linear_combination (-1 : ℝ) * he
  have hA0 : 0 ≤ (1 - exp (a * t)) / (-a) :=
    div_nonneg (by linarith [exp_le_one_iff.2 (by nlinarith : a * t ≤ 0)]) (by linarith)
  have hA1 : (1 - exp (a * t)) / (-a) ≤ 1 / (-a) :=
    div_le_div_of_nonneg_right (by linarith [exp_pos (a * t)]) (by linarith)
  -- the second integral lies in `[0, 1/η]`
  have hD0 : 0 ≤ exp (a * t) * ∫ u in (0 : ℝ)..t, exp (-a * u) * exp (-η * u) :=
    mul_nonneg (exp_pos _).le (intervalIntegral.integral_nonneg ht fun u _ => by positivity)
  have hD1 : exp (a * t) * ∫ u in (0 : ℝ)..t, exp (-a * u) * exp (-η * u) ≤ 1 / η := by
    rw [← intervalIntegral.integral_const_mul]
    refine le_trans (intervalIntegral.integral_mono_on ht
      ((by fun_prop : Continuous fun u => exp (a * t) * (exp (-a * u) * exp (-η * u)))
        |>.intervalIntegrable 0 t)
      ((by fun_prop : Continuous fun u => exp (-η * u)).intervalIntegrable 0 t)
      fun u hu => ?_) (integral_exp_neg_le hη ht).2
    have : exp (a * t) * exp (-a * u) ≤ 1 := by
      rw [← exp_add]; exact exp_le_one_iff.2 (by nlinarith [hu.2])
    calc exp (a * t) * (exp (-a * u) * exp (-η * u))
        = (exp (a * t) * exp (-a * u)) * exp (-η * u) := by ring
      _ ≤ 1 * exp (-η * u) := mul_le_mul_of_nonneg_right this (exp_pos _).le
      _ = exp (-η * u) := one_mul _
  have hval : debtMean a η sbar s0 b0 t = exp (a * t) * b0
      - sbar * (exp (a * t) * ∫ u in (0 : ℝ)..t, exp (-a * u))
      - (s0 - sbar) * (exp (a * t) * ∫ u in (0 : ℝ)..t, exp (-a * u) * exp (-η * u)) := by
    simp only [debtMean, vocFrom, e]
    rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_mul_const]
    simp only [mul_zero, exp_zero, one_mul]
    ring
  rw [hval, hA]
  have hb : |exp (a * t) * b0| ≤ |b0| := by
    rw [abs_mul, abs_of_pos (exp_pos _)]
    exact mul_le_of_le_one_left (abs_nonneg _) (exp_le_one_iff.2 (by nlinarith))
  have hs : |sbar * ((1 - exp (a * t)) / (-a))| ≤ |sbar| / (-a) := by
    rw [abs_mul, abs_of_nonneg hA0, div_eq_mul_one_div |sbar|]
    exact mul_le_mul_of_nonneg_left hA1 (abs_nonneg _)
  have hd : |(s0 - sbar) * (exp (a * t) * ∫ u in (0 : ℝ)..t, exp (-a * u) * exp (-η * u))|
      ≤ |s0 - sbar| / η := by
    rw [abs_mul, abs_of_nonneg hD0, div_eq_mul_one_div |s0 - sbar|]
    exact mul_le_mul_of_nonneg_left hD1 (abs_nonneg _)
  calc |exp (a * t) * b0 - sbar * ((1 - exp (a * t)) / (-a))
        - (s0 - sbar) * (exp (a * t) * ∫ u in (0 : ℝ)..t, exp (-a * u) * exp (-η * u))|
      ≤ |exp (a * t) * b0 - sbar * ((1 - exp (a * t)) / (-a))|
        + |(s0 - sbar) * (exp (a * t) * ∫ u in (0 : ℝ)..t, exp (-a * u) * exp (-η * u))| :=
        abs_sub _ _
    _ ≤ (|exp (a * t) * b0| + |sbar * ((1 - exp (a * t)) / (-a))|)
        + |(s0 - sbar) * (exp (a * t) * ∫ u in (0 : ℝ)..t, exp (-a * u) * exp (-η * u))| := by
        gcongr; exact abs_sub _ _
    _ ≤ |b0| + |sbar| / (-a) + |s0 - sbar| / η := by linarith

end Cochrane.FiscalConstraints.TidyR8OURestart
