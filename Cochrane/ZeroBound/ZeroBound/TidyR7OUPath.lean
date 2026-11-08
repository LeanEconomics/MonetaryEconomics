/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.LinearODE
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The Ornstein–Uhlenbeck surplus path by path

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.1, p. 197 ("Suppose we
generate the surplus by an AR(1), `ds_t = −η(s_t − s̄) + σ_s dz_s`"), and the debt-to-GDP
equation (6.4)–(6.5), p. 196.

The book's continuous-time AR(1) is the Ornstein–Uhlenbeck equation
`ds = −η(s − s̄)dt + σ dW`, which (with additive noise) is the integral equation
`s_t = s_0 − η∫_0^t (s_u − s̄)du + σW_t`. This module solves that integral equation for an
arbitrary continuous driving path `w` (later a Brownian path), with no stochastic calculus:

`s_t = s̄ + e^{−ηt}(s_0 − s̄) + σ(w_t − η e^{−ηt}∫_0^t e^{ηu}w_u du)` (`ouPath`).

By parts this is `s̄ + e^{−ηt}(s_0 − s̄) + σe^{−ηt}∫_0^t e^{ηu}dw_u`, the Wiener-integral form
(identified a.s. with the Itô integral in TidyR7WienerGaussian).

## Main results

* `ouPath_integral_eq`: `ouPath` solves the integral equation at every date, for every continuous
  path (no hypothesis `w_0 = 0` is needed).
* `ouPath_unique`: it is the only continuous solution.
* `ouPath_step`: over any step `h`,
  `s_{t+h} − s̄ = e^{−ηh}(s_t − s̄) + σ·ouStep` (the exact AR(1) form of the sampled path).
* `ouDebt_hasDerivAt`, `ouDebt_eq`: with the OU surplus the debt-to-GDP ratio of (6.4),
  corrected (6.5), `ḃ = ab − s`, is a deterministic part minus `σ·debtNoise`.
* `debtNoise_eq_integral`: the noise part of debt is `∫_0^t w_r k_t(r) dr` for an explicit
  continuous kernel `debtKernel` (one integration by parts, no Fubini); `debtG` is
  `G(r) = ∫_r^t k_t`, with `G(t) = 0`, `G' = −k_t`, and `∫_0^t G² > 0`
  (`integral_debtG_sq_pos`), which makes debt non-degenerate.
-/

namespace Cochrane.ZeroBound.TidyR7OUPath

open Real MeasureTheory Filter Topology

/-- Cochrane (2023), p. 197: the primitive `∫_0^t e^{ηu} w_u du` of the discounted driving path.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.ouPrim). -/
noncomputable def ouPrim (η : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, exp (η * u) * w u

/-- Cochrane (2023), p. 197: the noise of the OU surplus driven by the path `w`,
`w_t − η e^{−ηt}∫_0^t e^{ηu} w_u du` (`= e^{−ηt}∫_0^t e^{ηu} dw_u` by parts).
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.ouNoise). -/
noncomputable def ouNoise (η : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  w t - η * (exp (-η * t) * ouPrim η w t)

/-- Cochrane (2023), p. 197: the mean path `s̄ + e^{−ηt}(s_0 − s̄)` of the OU surplus.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.ouMean). -/
noncomputable def ouMean (η sbar s0 t : ℝ) : ℝ := sbar + exp (-η * t) * (s0 - sbar)

/-- Cochrane (2023), p. 197 (**the OU surplus**, path by path): the solution of
`ds = −η(s − s̄)dt + σ dw` from `s_0`, `s_t = s̄ + e^{−ηt}(s_0 − s̄) + σ·ouNoise`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.ouPath). -/
noncomputable def ouPath (η sbar s0 σ : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  ouMean η sbar s0 t + σ * ouNoise η w t

/-- Cochrane (2023), p. 197: the innovation of the OU surplus over `[t, t + h]`,
`w_{t+h} − e^{−ηh}w_t − η e^{−η(t+h)}∫_t^{t+h} e^{ηu}w_u du`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.ouStep). -/
noncomputable def ouStep (η : ℝ) (w : ℝ → ℝ) (t h : ℝ) : ℝ :=
  w (t + h) - exp (-η * h) * w t - η * (exp (-η * (t + h)) * ∫ u in t..(t + h), exp (η * u) * w u)

variable {η sbar s0 σ : ℝ} {w : ℝ → ℝ}

/-- Cochrane (2023), p. 197: `t ↦ ∫_0^t e^{ηu}w_u du` has derivative `e^{ηt}w_t`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.hasDerivAt_ouPrim). -/
theorem hasDerivAt_ouPrim (η : ℝ) (hw : Continuous w) (t : ℝ) :
    HasDerivAt (ouPrim η w) (exp (η * t) * w t) t :=
  ((by fun_prop : Continuous fun u => exp (η * u) * w u).integral_hasStrictDerivAt 0 t).hasDerivAt

/-- Cochrane (2023), p. 197: the primitive is continuous.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.continuous_ouPrim). -/
theorem continuous_ouPrim (η : ℝ) (hw : Continuous w) : Continuous (ouPrim η w) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_ouPrim η hw t).continuousAt

/-- Cochrane (2023), p. 197: the primitive vanishes at `0`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.ouPrim_zero). -/
theorem ouPrim_zero (η : ℝ) (w : ℝ → ℝ) : ouPrim η w 0 = 0 := by
  simp [ouPrim]

/-- Cochrane (2023), p. 197: the OU noise is continuous.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.continuous_ouNoise). -/
theorem continuous_ouNoise (η : ℝ) (hw : Continuous w) : Continuous (ouNoise η w) := by
  have := continuous_ouPrim η hw
  unfold ouNoise
  fun_prop

/-- Cochrane (2023), p. 197: the mean path is continuous.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.continuous_ouMean). -/
theorem continuous_ouMean (η sbar s0 : ℝ) : Continuous (ouMean η sbar s0) := by
  unfold ouMean
  fun_prop

/-- Cochrane (2023), p. 197: the OU surplus path is continuous.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.continuous_ouPath). -/
theorem continuous_ouPath (η sbar s0 σ : ℝ) (hw : Continuous w) :
    Continuous (ouPath η sbar s0 σ w) := by
  have h1 := continuous_ouNoise η hw
  have h2 := continuous_ouMean η sbar s0
  unfold ouPath
  fun_prop

/-- Cochrane (2023), p. 197: the OU surplus starts at `s_0 + σ w_0`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.ouPath_zero). -/
theorem ouPath_zero (η sbar s0 σ : ℝ) (w : ℝ → ℝ) : ouPath η sbar s0 σ w 0 = s0 + σ * w 0 := by
  simp [ouPath, ouMean, ouNoise, ouPrim_zero]

/-- Cochrane (2023), p. 197: the OU surplus less its noise, `s_t − σw_t`, is differentiable
with derivative `−η(s_t − s̄)`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.hasDerivAt_ouPath_sub). -/
theorem hasDerivAt_ouPath_sub (hw : Continuous w) (t : ℝ) :
    HasDerivAt (fun u => ouMean η sbar s0 u - σ * η * (exp (-η * u) * ouPrim η w u))
      (-η * (ouPath η sbar s0 σ w t - sbar)) t := by
  have hE : HasDerivAt (fun u => exp (-η * u)) (exp (-η * t) * -η) t := by
    simpa using ((hasDerivAt_id' t).const_mul (-η)).exp
  have hP := hasDerivAt_ouPrim η hw t
  have h := HasDerivAt.sub ((hE.mul_const (s0 - sbar)).const_add sbar)
    ((hE.mul hP).const_mul (σ * η))
  refine h.congr_deriv ?_
  have he : exp (-η * t) * exp (η * t) = 1 := by rw [← exp_add]; ring_nf; exact exp_zero
  simp only [ouPath, ouMean, ouNoise]
  linear_combination (-(σ * η * w t)) * he

/-- **Cochrane (2023), p. 197: the OU surplus solves `ds = −η(s − s̄)dt + σ dw`**, in integral
form, at every date and for every continuous driving path:
`s_t = s_0 − η∫_0^t (s_u − s̄)du + σ w_t`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.ouPath_integral_eq). -/
theorem ouPath_integral_eq (hw : Continuous w) (t : ℝ) :
    ouPath η sbar s0 σ w t
      = s0 - η * (∫ u in (0 : ℝ)..t, (ouPath η sbar s0 σ w u - sbar)) + σ * w t := by
  have hc : Continuous fun u => -η * (ouPath η sbar s0 σ w u - sbar) := by
    have := continuous_ouPath η sbar s0 σ hw
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_ouPath_sub (η := η) (sbar := sbar) (s0 := s0) (σ := σ) hw x)
    (hc.intervalIntegrable 0 t)
  rw [intervalIntegral.integral_const_mul] at hftc
  have h0 : ouMean η sbar s0 0 = s0 := by simp [ouMean]
  rw [h0, ouPrim_zero] at hftc
  have e : ouPath η sbar s0 σ w t
      = (ouMean η sbar s0 t - σ * η * (exp (-η * t) * ouPrim η w t)) + σ * w t := by
    simp only [ouPath, ouNoise]
    ring
  rw [e]
  linarith

/-- **Cochrane (2023), p. 197: uniqueness.** A continuous path `x` with
`x_t = s_0 − η∫_0^t (x_u − s̄)du + σ w_t` for every `t` is the OU surplus `ouPath`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.ouPath_unique). -/
theorem ouPath_unique (hw : Continuous w) {x : ℝ → ℝ} (hx : Continuous x)
    (h : ∀ t, x t = s0 - η * (∫ u in (0 : ℝ)..t, (x u - sbar)) + σ * w t) :
    x = ouPath η sbar s0 σ w := by
  have hs := continuous_ouPath η sbar s0 σ hw
  set d : ℝ → ℝ := fun u => x u - ouPath η sbar s0 σ w u with hd
  have hdc : Continuous d := hx.sub hs
  have hdeq : ∀ t, d t = -η * ∫ u in (0 : ℝ)..t, d u := by
    intro t
    have h1 := h t
    have h2 := ouPath_integral_eq (η := η) (sbar := sbar) (s0 := s0) (σ := σ) hw t
    have hi : (∫ u in (0 : ℝ)..t, d u)
        = (∫ u in (0 : ℝ)..t, (x u - sbar))
          - ∫ u in (0 : ℝ)..t, (ouPath η sbar s0 σ w u - sbar) := by
      rw [← intervalIntegral.integral_sub ((by fun_prop : Continuous fun u => x u - sbar)
        |>.intervalIntegrable 0 t) ((by fun_prop : Continuous fun u =>
          ouPath η sbar s0 σ w u - sbar) |>.intervalIntegrable 0 t)]
      congr 1
      funext u
      simp only [hd]
      ring
    simp only [hd] at hi ⊢
    rw [hi]
    linarith
  have hD : ∀ t, HasDerivAt (fun t => ∫ u in (0 : ℝ)..t, d u) (d t) t := fun t =>
    (hdc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hF : ∀ t, HasDerivAt (fun t => exp (η * t) * ∫ u in (0 : ℝ)..t, d u) 0 t := by
    intro t
    have hE : HasDerivAt (fun u => exp (η * u)) (exp (η * t) * η) t := by
      simpa using ((hasDerivAt_id' t).const_mul η).exp
    refine (hE.mul (hD t)).congr_deriv ?_
    rw [hdeq t]
    ring
  have hconst : ∀ t, exp (η * t) * (∫ u in (0 : ℝ)..t, d u) = 0 := by
    intro t
    have := is_const_of_deriv_eq_zero (fun t => (hF t).differentiableAt)
      (fun t => (hF t).deriv) t 0
    simpa using this
  funext t
  have hz : (∫ u in (0 : ℝ)..t, d u) = 0 := by
    have := hconst t
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' (exp_pos _).ne'
    · exact h'
  have := hdeq t
  rw [hz, mul_zero] at this
  simp only [hd] at this
  linarith

/-- **Cochrane (2023), p. 197: the OU surplus is an exact AR(1) over any step `h`**:
`s_{t+h} − s̄ = e^{−ηh}(s_t − s̄) + σ·ouStep η w t h`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.ouPath_step). -/
theorem ouPath_step (hw : Continuous w) (t h : ℝ) :
    ouPath η sbar s0 σ w (t + h) - sbar
      = exp (-η * h) * (ouPath η sbar s0 σ w t - sbar) + σ * ouStep η w t h := by
  have hi : IntervalIntegrable (fun u => exp (η * u) * w u) volume 0 t :=
    (by fun_prop : Continuous fun u => exp (η * u) * w u).intervalIntegrable 0 t
  have hj : IntervalIntegrable (fun u => exp (η * u) * w u) volume t (t + h) :=
    (by fun_prop : Continuous fun u => exp (η * u) * w u).intervalIntegrable t (t + h)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi hj
  have hexp : exp (-η * (t + h)) = exp (-η * h) * exp (-η * t) := by
    rw [← exp_add]
    ring_nf
  simp only [ouPath, ouMean, ouNoise, ouStep, ouPrim]
  rw [← hadd]
  linear_combination ((s0 - sbar) - σ * η * ∫ u in (0 : ℝ)..t, exp (η * u) * w u) * hexp

/-! ### Debt with an OU surplus (6.4)–(6.5) -/

/-- Cochrane (2023), (6.4)–(6.5), pp. 196–197: the debt-to-GDP ratio with the OU surplus,
`b_t = e^{at}b_0 − ∫_0^t e^{a(t−u)}s_u du` (corrected (6.5), `LinearODE.vocFrom`), `a = r − g`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.ouDebt). -/
noncomputable def ouDebt (a η sbar s0 σ b0 : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  LinearODE.vocFrom a (ouPath η sbar s0 σ w) 0 b0 t

/-- Cochrane (2023), (6.5), p. 196: the deterministic part of debt, driven by the mean surplus.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.debtMean). -/
noncomputable def debtMean (a η sbar s0 b0 t : ℝ) : ℝ :=
  LinearODE.vocFrom a (ouMean η sbar s0) 0 b0 t

/-- Cochrane (2023), (6.5), p. 197: the noise part of debt, `e^{at}∫_0^t e^{−au}·ouNoise_u du`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.debtNoise). -/
noncomputable def debtNoise (a η : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  exp (a * t) * ∫ u in (0 : ℝ)..t, exp (-a * u) * ouNoise η w u

/-- Cochrane (2023), (6.4), p. 196: with the OU surplus, debt solves `ḃ = ab − s` at every
date.
A special case of Mathlib `LinearODE.vocFrom_hasDerivAt`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.ouDebt_hasDerivAt). -/
theorem ouDebt_hasDerivAt (a b0 : ℝ) (hw : Continuous w) (t : ℝ) :
    HasDerivAt (ouDebt a η sbar s0 σ b0 w)
      (a * ouDebt a η sbar s0 σ b0 w t - ouPath η sbar s0 σ w t) t :=
  LinearODE.vocFrom_hasDerivAt a (continuous_ouPath η sbar s0 σ hw) 0 b0 t

/-- Cochrane (2023), (6.4), p. 196: the OU debt starts at `b_0`.
A special case of Mathlib `LinearODE.vocFrom_self`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.ouDebt_zero). -/
theorem ouDebt_zero (a b0 : ℝ) : ouDebt a η sbar s0 σ b0 w 0 = b0 :=
  LinearODE.vocFrom_self a _ 0 b0

/-- Cochrane (2023), (6.5), p. 197: debt is its deterministic part minus `σ` times its noise.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.ouDebt_eq). -/
theorem ouDebt_eq (a b0 : ℝ) (hw : Continuous w) (t : ℝ) :
    ouDebt a η sbar s0 σ b0 w t = debtMean a η sbar s0 b0 t - σ * debtNoise a η w t := by
  have h1 : Continuous fun u => exp (-a * u) * ouMean η sbar s0 u := by
    have := continuous_ouMean η sbar s0
    fun_prop
  have h2 : Continuous fun u => σ * (exp (-a * u) * ouNoise η w u) := by
    have := continuous_ouNoise η hw
    fun_prop
  have hsplit : (∫ u in (0 : ℝ)..t, exp (-a * u) * ouPath η sbar s0 σ w u)
      = (∫ u in (0 : ℝ)..t, exp (-a * u) * ouMean η sbar s0 u)
        + σ * ∫ u in (0 : ℝ)..t, exp (-a * u) * ouNoise η w u := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
      (h1.intervalIntegrable 0 t) (h2.intervalIntegrable 0 t)]
    congr 1
    funext u
    simp only [ouPath]
    ring
  simp only [ouDebt, debtMean, debtNoise, LinearODE.vocFrom]
  rw [hsplit]
  ring

/-- Cochrane (2023), (6.5), p. 197: the primitive `F_c(x) = ∫_0^x e^{−cv}dv` used in the debt
kernel.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.debtF). -/
noncomputable def debtF (c x : ℝ) : ℝ := ∫ v in (0 : ℝ)..x, exp (-c * v)

/-- Cochrane (2023), (6.5), p. 197: `F_c' = e^{−cx}`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.hasDerivAt_debtF). -/
theorem hasDerivAt_debtF (c x : ℝ) : HasDerivAt (debtF c) (exp (-c * x)) x :=
  ((by fun_prop : Continuous fun v => exp (-c * v)).integral_hasStrictDerivAt 0 x).hasDerivAt

/-- Cochrane (2023), (6.5), p. 197: `F_c` is continuous.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.continuous_debtF). -/
theorem continuous_debtF (c : ℝ) : Continuous (debtF c) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_debtF c x).continuousAt

/-- Cochrane (2023), (6.5), p. 197: the kernel of the debt noise,
`k_t(r) = e^{at}(e^{−ar} − η(F_{a+η}(t) − F_{a+η}(r))e^{ηr})`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.debtKernel). -/
noncomputable def debtKernel (a η t r : ℝ) : ℝ :=
  exp (a * t) * (exp (-a * r) - η * (debtF (a + η) t - debtF (a + η) r) * exp (η * r))

/-- Cochrane (2023), (6.5), p. 197: the debt kernel is continuous in `r`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.continuous_debtKernel). -/
theorem continuous_debtKernel (a η t : ℝ) : Continuous (debtKernel a η t) := by
  have := continuous_debtF (a + η)
  unfold debtKernel
  fun_prop

/-- Cochrane (2023), (6.5), p. 197: `k_t(t) = 1`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.debtKernel_self). -/
theorem debtKernel_self (a η t : ℝ) : debtKernel a η t t = 1 := by
  simp only [debtKernel, sub_self, mul_zero, zero_mul, sub_zero]
  rw [← exp_add]
  ring_nf
  exact exp_zero

/-- **Cochrane (2023), (6.5), p. 197: the noise part of debt is a linear functional of the
driving path**, `e^{at}∫_0^t e^{−au}·ouNoise_u du = ∫_0^t w_r k_t(r) dr` (one integration by
parts).
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.debtNoise_eq_integral). -/
theorem debtNoise_eq_integral (a η : ℝ) (hw : Continuous w) (t : ℝ) :
    debtNoise a η w t = ∫ r in (0 : ℝ)..t, w r * debtKernel a η t r := by
  have hP := continuous_ouPrim η hw
  have hFc := continuous_debtF (a + η)
  have hex : ∀ u : ℝ, exp (-(a + η) * u) = exp (-a * u) * exp (-η * u) := fun u => by
    rw [← exp_add]
    ring_nf
  -- step 1: split the integrand of `debtNoise`
  have s1 : (∫ u in (0 : ℝ)..t, exp (-a * u) * ouNoise η w u)
      = (∫ u in (0 : ℝ)..t, exp (-a * u) * w u)
        - η * ∫ u in (0 : ℝ)..t, ouPrim η w u * exp (-(a + η) * u) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun u => exp (-a * u) * w u).intervalIntegrable 0 t)
      ((by fun_prop : Continuous fun u => η * (ouPrim η w u * exp (-(a + η) * u)))
        |>.intervalIntegrable 0 t)]
    congr 1
    funext u
    simp only [ouNoise, hex]
    ring
  -- step 2: integrate by parts
  have s2 : (∫ u in (0 : ℝ)..t, ouPrim η w u * exp (-(a + η) * u))
      = ouPrim η w t * debtF (a + η) t
        - ∫ u in (0 : ℝ)..t, (exp (η * u) * w u) * debtF (a + η) u := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := ouPrim η w) (v := debtF (a + η)) (a := 0) (b := t)
      (fun x _ => hasDerivAt_ouPrim η hw x) (fun x _ => hasDerivAt_debtF (a + η) x)
      ((by fun_prop : Continuous fun u => exp (η * u) * w u).intervalIntegrable 0 t)
      ((by fun_prop : Continuous fun u => exp (-(a + η) * u)).intervalIntegrable 0 t)
    rw [h, ouPrim_zero]
    ring
  -- step 3: split the kernel integral
  have s3 : (∫ r in (0 : ℝ)..t, w r * debtKernel a η t r)
      = exp (a * t) * ((∫ r in (0 : ℝ)..t, exp (-a * r) * w r)
        - η * debtF (a + η) t * ouPrim η w t
        + η * ∫ r in (0 : ℝ)..t, (exp (η * r) * w r) * debtF (a + η) r) := by
    have i1 := (by fun_prop : Continuous fun r => exp (-a * r) * w r).intervalIntegrable
      (μ := volume) 0 t
    have i2 := (by fun_prop : Continuous fun r =>
      η * debtF (a + η) t * (exp (η * r) * w r)).intervalIntegrable (μ := volume) 0 t
    have i3 := (by fun_prop : Continuous fun r =>
      η * ((exp (η * r) * w r) * debtF (a + η) r)).intervalIntegrable (μ := volume) 0 t
    have e : (fun r => w r * debtKernel a η t r) = fun r => exp (a * t) *
        ((exp (-a * r) * w r) - η * debtF (a + η) t * (exp (η * r) * w r)
          + η * ((exp (η * r) * w r) * debtF (a + η) r)) := by
      funext r
      simp only [debtKernel]
      ring
    rw [e, intervalIntegral.integral_const_mul, intervalIntegral.integral_add (i1.sub i2) i3,
      intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    simp only [ouPrim]
  rw [s3, debtNoise, s1, s2]
  ring

/-- Cochrane (2023), (6.5), p. 197: `G_t(r) = ∫_r^t k_t(u)du`, the deterministic Wiener integrand
whose integral `∫_0^t G_t dW` is the noise part of debt.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.debtG). -/
noncomputable def debtG (a η t r : ℝ) : ℝ := -∫ u in t..r, debtKernel a η t u

/-- Cochrane (2023), (6.5), p. 197: `G_t' = −k_t`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.hasDerivAt_debtG). -/
theorem hasDerivAt_debtG (a η t r : ℝ) :
    HasDerivAt (debtG a η t) (-debtKernel a η t r) r :=
  ((continuous_debtKernel a η t).integral_hasStrictDerivAt t r).hasDerivAt.neg

/-- Cochrane (2023), (6.5), p. 197: `G_t(t) = 0`.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.debtG_self). -/
theorem debtG_self (a η t : ℝ) : debtG a η t t = 0 := by
  simp [debtG]

/-- Cochrane (2023), (6.5), p. 197: `G_t` is continuous.
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.continuous_debtG). -/
theorem continuous_debtG (a η t : ℝ) : Continuous (debtG a η t) :=
  continuous_iff_continuousAt.2 fun r => (hasDerivAt_debtG a η t r).continuousAt

/-- **Cochrane (2023), (6.5), p. 197: the debt noise is non-degenerate**: for `t > 0`,
`∫_0^t G_t(r)² dr > 0` (since `G_t(t) = 0` and `G_t'(t) = −1`).
Restated from the Cochrane FiscalConstraints project
(Cochrane.FiscalConstraints.TidyR7OUPath.integral_debtG_sq_pos). -/
theorem integral_debtG_sq_pos (a η : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < ∫ r in (0 : ℝ)..t, debtG a η t r ^ 2 := by
  have hd := hasDerivAt_debtG a η t t
  rw [debtKernel_self] at hd
  have hs := (hasDerivAt_iff_tendsto_slope.1 hd).mono_left
    (nhdsWithin_mono t (fun x (hx : x < t) => ne_of_lt hx))
  have hev : ∀ᶠ r in 𝓝[<] t, slope (debtG a η t) t r < 0 ∧ r ∈ Set.Ioo 0 t :=
    (hs.eventually (gt_mem_nhds (by norm_num : (-1 : ℝ) < 0))).and (Ioo_mem_nhdsLT ht)
  obtain ⟨r0, hr0, hr0I⟩ := hev.exists
  have hG0 : debtG a η t r0 ≠ 0 := by
    intro h0
    rw [slope_def_field, h0, debtG_self, sub_self, zero_div] at hr0
    exact lt_irrefl 0 hr0
  have hc : Continuous fun r => debtG a η t r ^ 2 := (continuous_debtG a η t).pow 2
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae'
    (ae_of_all _ fun r => sq_nonneg (debtG a η t r)) (hc.intervalIntegrable 0 t)]
  refine ⟨ht, ?_⟩
  have hU : IsOpen (Function.support (fun r => debtG a η t r ^ 2) ∩ Set.Ioo 0 t) :=
    (isOpen_compl_singleton.preimage hc).inter isOpen_Ioo
  have hne : (Function.support (fun r => debtG a η t r ^ 2) ∩ Set.Ioo 0 t).Nonempty :=
    ⟨r0, pow_ne_zero 2 hG0, hr0I⟩
  exact (hU.measure_pos volume hne).trans_le (measure_mono
    (Set.inter_subset_inter_right _ Set.Ioo_subset_Ioc_self))

end Cochrane.ZeroBound.TidyR7OUPath
