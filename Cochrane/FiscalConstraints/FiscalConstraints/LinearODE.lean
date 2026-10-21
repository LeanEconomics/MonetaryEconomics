/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.ExpIntegrals
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# The debt-to-GDP equation and linear first-order ODEs

Cochrane (2023), Chapter 6, §6.4.1, eqs. (6.4)–(6.5), p. 196.

Debt grows at the real rate less the surplus, `ḃ = r b - s`, and GDP grows at `g`, `ẏ = g y`;
hence the debt-to-GDP ratio obeys (6.4): `d(b/y)/dt = (r - g)(b/y) - s/y`. Writing `x = b/y`,
`σ = s/y` and `a = r - g`, this is the linear ODE `x' = a x - σ`, whose solution from `x(t₀)` is
given by variation of constants. The book's backward solution (6.5) is printed as
`x_t = ∫₀^t e^{aτ} σ_{t-τ} dτ + e^{a} x₀`; the correct formula is
`x_t = e^{a t} x₀ - ∫₀^t e^{aτ} σ_{t-τ} dτ` (survey E6.1: the integral has the wrong sign and the
exponent of the homogeneous term lacks `t`).

## Main results

* `debt_gdp_ode` (6.4): the exact derivative of `b/y` (time-varying `r`, `g`, `s`);
  `debt_gdp_discrete`: the discrete-time analogue `x_{t+1} = ((1+r)/(1+g)) x_t - σ_{t+1}`.
* `vocFrom`, `vocFrom_self`, `vocFrom_hasDerivAt`: the variation-of-constants solution from
  `(t₀, x₀)` is a solution.
* `eq_vocFrom`: every solution on `[t₀, T]` (continuous on the closed interval, differentiable
  inside) equals it; `solution_unique`.
* `corrected_6_5`: `vocFrom a σ 0 x₀ t = e^{a t} x₀ - ∫₀^t e^{aτ} σ(t - τ) dτ`.
* `printed65`, `printed_6_5_wrong_exponent`, `printed_6_5_wrong_sign`: the printed (6.5) is not the
  solution (two counterexamples, isolating each error).
* `finite_horizon_identity`, `vocFrom_eq_of_global`: for a solution on all of `ℝ`,
  `w_t = ∫_t^T e^{-a(τ-t)} f_τ dτ + e^{-a(T-t)} w_T` for all `t, T` (the identity behind
  (6.12)–(6.13), pp. 202–203), equivalently `w_T = vocFrom a f t w_t T`.
* `forward_present_value`: for `a > 0`, bounded continuous `f` and the transversality condition,
  `w_t = ∫_t^∞ e^{-a(τ-t)} f_τ dτ` (the present value (6.9), p. 201).
-/

namespace Cochrane.FiscalConstraints.LinearODE

open Real MeasureTheory Filter Topology

/-- Cochrane (2023), eq. (6.4), p. 196: if debt obeys `ḃ = r b - s` and GDP `ẏ = g y`, the
debt-to-GDP ratio obeys `d(b/y)/dt = (r - g)(b/y) - s/y` (exact derivative; `r`, `g`, `s` may
vary over time). -/
theorem debt_gdp_ode {b y r g s : ℝ → ℝ} {t : ℝ} (hb : HasDerivAt b (r t * b t - s t) t)
    (hy : HasDerivAt y (g t * y t) t) (hy0 : y t ≠ 0) :
    HasDerivAt (fun u => b u / y u) ((r t - g t) * (b t / y t) - s t / y t) t := by
  refine (hb.div hy hy0).congr_deriv ?_
  field_simp
  ring

/-- Cochrane (2023), §6.4.1, p. 196 (discrete-time analogue of (6.4)): if
`b_{t+1} = (1 + r) b_t - s_{t+1}` and `y_{t+1} = (1 + g) y_t`, then
`b_{t+1}/y_{t+1} = ((1 + r)/(1 + g)) (b_t/y_t) - s_{t+1}/y_{t+1}`. -/
theorem debt_gdp_discrete {b y s : ℕ → ℝ} {r g : ℝ}
    (hb : ∀ t, b (t + 1) = (1 + r) * b t - s (t + 1))
    (hy : ∀ t, y (t + 1) = (1 + g) * y t) (hy0 : ∀ t, y t ≠ 0) (hg : 1 + g ≠ 0) (t : ℕ) :
    b (t + 1) / y (t + 1) = (1 + r) / (1 + g) * (b t / y t) - s (t + 1) / y (t + 1) := by
  have h0 := hy0 t
  rw [hb t, hy t]
  field_simp

/-- Cochrane (2023), eq. (6.5), p. 196 (corrected): the variation-of-constants solution of
`x' = a x - σ` from `x(t₀) = x₀`,
`x(t) = e^{a t}(e^{-a t₀} x₀ - ∫_{t₀}^t e^{-a u} σ(u) du)`. -/
noncomputable def vocFrom (a : ℝ) (σ : ℝ → ℝ) (t0 x0 t : ℝ) : ℝ :=
  exp (a * t) * (exp (-a * t0) * x0 - ∫ u in t0..t, exp (-a * u) * σ u)

/-- Cochrane (2023), eq. (6.5), p. 196: the variation-of-constants solution starts at `x₀`. -/
theorem vocFrom_self (a : ℝ) (σ : ℝ → ℝ) (t0 x0 : ℝ) : vocFrom a σ t0 x0 t0 = x0 := by
  unfold vocFrom
  rw [intervalIntegral.integral_same, sub_zero, ← mul_assoc, ← exp_add]
  ring_nf
  rw [exp_zero, one_mul]

/-- Cochrane (2023), eqs. (6.4)–(6.5), p. 196: the variation-of-constants formula solves
`x' = a x - σ` at every date, for continuous `σ`. -/
theorem vocFrom_hasDerivAt (a : ℝ) {σ : ℝ → ℝ} (hσ : Continuous σ) (t0 x0 t : ℝ) :
    HasDerivAt (vocFrom a σ t0 x0) (a * vocFrom a σ t0 x0 t - σ t) t := by
  have hf : Continuous (fun u => exp (-a * u) * σ u) := by fun_prop
  have hI := (hf.integral_hasStrictDerivAt t0 t).hasDerivAt
  have hE : HasDerivAt (fun u => exp (a * u)) (exp (a * t) * a) t := by
    simpa using ((hasDerivAt_id' t).const_mul a).exp
  have h := hE.mul (hI.const_sub (exp (-a * t0) * x0))
  unfold vocFrom
  refine h.congr_deriv ?_
  have : exp (a * t) * exp (-a * t) = 1 := by rw [← exp_add]; ring_nf; exact exp_zero
  linear_combination (-(σ t)) * this

/-- Cochrane (2023), eqs. (6.4)–(6.5), p. 196: uniqueness. Any `x` continuous on `[t₀, T]` that
solves `x' = a x - σ` on `(t₀, T)` equals the variation-of-constants solution at `T`. -/
theorem eq_vocFrom (a : ℝ) {σ : ℝ → ℝ} (hσ : Continuous σ) {x : ℝ → ℝ} {t0 T : ℝ}
    (hle : t0 ≤ T) (hc : ContinuousOn x (Set.Icc t0 T))
    (hd : ∀ t ∈ Set.Ioo t0 T, HasDerivAt x (a * x t - σ t) t) :
    x T = vocFrom a σ t0 (x t0) T := by
  set w : ℝ → ℝ := fun t => exp (-a * t) * x t with hw
  have hwc : ContinuousOn w (Set.Icc t0 T) :=
    ContinuousOn.mul (by fun_prop) hc
  have hwd : ∀ t ∈ Set.Ioo t0 T, HasDerivAt w (-(exp (-a * t) * σ t)) t := by
    intro t ht
    have hE : HasDerivAt (fun u => exp (-a * u)) (exp (-a * t) * -a) t := by
      simpa using ((hasDerivAt_id' t).const_mul (-a)).exp
    refine (hE.mul (hd t ht)).congr_deriv ?_
    ring
  have hint : IntervalIntegrable (fun t => -(exp (-a * t) * σ t)) volume t0 T :=
    (by fun_prop : Continuous (fun t => -(exp (-a * t) * σ t))).intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hwc hwd hint
  rw [intervalIntegral.integral_neg] at hftc
  have hwT : w T = exp (-a * t0) * x t0 - ∫ u in t0..T, exp (-a * u) * σ u := by
    simp only [hw] at hftc ⊢
    linarith
  unfold vocFrom
  rw [← hwT, hw]
  simp only
  rw [← mul_assoc, ← exp_add]
  ring_nf
  rw [exp_zero, one_mul]

/-- Cochrane (2023), eq. (6.5), p. 196: two solutions of `x' = a x - σ` on `[t₀, T]` that agree at
`t₀` agree at `T`. -/
theorem solution_unique (a : ℝ) {σ : ℝ → ℝ} (hσ : Continuous σ) {x z : ℝ → ℝ} {t0 T : ℝ}
    (hle : t0 ≤ T) (hcx : ContinuousOn x (Set.Icc t0 T)) (hcz : ContinuousOn z (Set.Icc t0 T))
    (hdx : ∀ t ∈ Set.Ioo t0 T, HasDerivAt x (a * x t - σ t) t)
    (hdz : ∀ t ∈ Set.Ioo t0 T, HasDerivAt z (a * z t - σ t) t) (h0 : x t0 = z t0) :
    x T = z T := by
  rw [eq_vocFrom a hσ hle hcx hdx, eq_vocFrom a hσ hle hcz hdz, h0]

/-- Cochrane (2023), eq. (6.5), p. 196, corrected (survey E6.1): the backward solution of (6.4)
from `x₀` is `x_t = e^{a t} x₀ - ∫₀^t e^{aτ} σ_{t-τ} dτ`. -/
theorem corrected_6_5 (a : ℝ) (σ : ℝ → ℝ) (x0 t : ℝ) :
    vocFrom a σ 0 x0 t = exp (a * t) * x0 - ∫ τ in (0 : ℝ)..t, exp (a * τ) * σ (t - τ) := by
  have h1 : (∫ τ in (0 : ℝ)..t, exp (a * τ) * σ (t - τ)) =
      ∫ τ in (0 : ℝ)..t, (fun u => exp (a * (t - u)) * σ u) (t - τ) := by
    congr 1
    funext τ
    simp only [sub_sub_cancel]
  rw [h1, intervalIntegral.integral_comp_sub_left (fun u => exp (a * (t - u)) * σ u) t,
    sub_self, sub_zero]
  unfold vocFrom
  rw [mul_sub, ← intervalIntegral.integral_const_mul, mul_zero, exp_zero, one_mul]
  congr 2
  funext u
  rw [← mul_assoc, ← exp_add]
  ring_nf

/-- Cochrane (2023), eq. (6.5), p. 196, as printed: `∫₀^t e^{aτ} σ_{t-τ} dτ + e^{a} x₀`. -/
noncomputable def printed65 (a : ℝ) (σ : ℝ → ℝ) (x0 t : ℝ) : ℝ :=
  (∫ τ in (0 : ℝ)..t, exp (a * τ) * σ (t - τ)) + exp a * x0

/-- Cochrane (2023), eq. (6.5), p. 196 (survey E6.1, the exponent): with `a = 1`, no surpluses
and `x₀ = 1`, the solution at `t = 2` is `e²`, while the printed formula gives `e`. -/
theorem printed_6_5_wrong_exponent :
    vocFrom 1 (fun _ => 0) 0 1 2 = exp 2 ∧ printed65 1 (fun _ => 0) 1 2 = exp 1 ∧
      exp (2 : ℝ) ≠ exp 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [corrected_6_5]
    simp
  · unfold printed65
    simp
  · intro h
    have := exp_injective h
    norm_num at this

/-- Cochrane (2023), eq. (6.5), p. 196 (survey E6.1, the sign): with `a = 0` (`r = g`), a constant
surplus ratio `σ = 1` and `x₀ = 0`, the solution at `t = 1` is `-1` (surpluses pay debt down),
while the printed formula gives `+1`. -/
theorem printed_6_5_wrong_sign :
    vocFrom 0 (fun _ => 1) 0 0 1 = -1 ∧ printed65 0 (fun _ => 1) 0 1 = 1 := by
  refine ⟨?_, ?_⟩
  · rw [corrected_6_5]
    simp
  · unfold printed65
    simp

/-- Cochrane (2023), (6.12) and (6.13) pp. 202–203 (variation of constants, moved here from
`MoneyLiquidity`): if
`dw/dτ = a w − f` with `f` continuous, then for all `t, T`,
`w_t = ∫_t^T e^{−a(τ−t)} f_τ dτ + e^{−a(T−t)} w_T`. -/
theorem finite_horizon_identity {a : ℝ} {w f : ℝ → ℝ}
    (hw : ∀ τ, HasDerivAt w (a * w τ - f τ) τ) (hf : Continuous f) (t T : ℝ) :
    w t = (∫ τ in t..T, Real.exp (-a * (τ - t)) * f τ) + Real.exp (-a * (T - t)) * w T := by
  have hφ : ∀ τ ∈ Set.uIcc t T, HasDerivAt (fun x => Real.exp (-a * (x - t)) * w x)
      (-(Real.exp (-a * (τ - t)) * f τ)) τ := by
    intro τ _
    have h1 : HasDerivAt (fun x => -a * (x - t)) (-a * 1) τ :=
      ((hasDerivAt_id τ).sub_const t).const_mul (-a)
    have h2 := h1.exp.mul (hw τ)
    convert h2 using 1
    ring
  have hint : IntervalIntegrable (fun τ => -(Real.exp (-a * (τ - t)) * f τ)) volume t T :=
    (by fun_prop : Continuous fun τ => -(Real.exp (-a * (τ - t)) * f τ)).intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hφ hint
  rw [intervalIntegral.integral_neg] at hftc
  simp only [sub_self, mul_zero, Real.exp_zero, one_mul] at hftc
  linarith

/-- Cochrane (2023), eqs. (6.5) and (6.12)–(6.13), pp. 196 and 202–203: the finite-horizon
identity and the variation-of-constants formula agree: a solution of `w' = a w - f` on all of `ℝ`
satisfies `w_T = vocFrom a f t w_t T` for every pair of dates `t, T` (in either order). -/
theorem vocFrom_eq_of_global {a : ℝ} {w f : ℝ → ℝ}
    (hw : ∀ τ, HasDerivAt w (a * w τ - f τ) τ) (hf : Continuous f) (t T : ℝ) :
    w T = vocFrom a f t (w t) T := by
  have h := finite_horizon_identity hw hf t T
  have hI : (∫ τ in t..T, Real.exp (-a * (τ - t)) * f τ) =
      exp (a * t) * ∫ τ in t..T, exp (-a * τ) * f τ := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext τ
    rw [← mul_assoc, ← exp_add]
    ring_nf
  rw [hI] at h
  have e4 : exp (-a * t) * exp (a * t) = 1 := by rw [← exp_add]; ring_nf; exact exp_zero
  have e5 : exp (a * T) * exp (-a * t) * exp (-a * (T - t)) = 1 := by
    rw [← exp_add, ← exp_add]; ring_nf; exact exp_zero
  unfold vocFrom
  rw [h]
  linear_combination (-(exp (a * T) * ∫ τ in t..T, exp (-a * τ) * f τ)) * e4 + (-(w T)) * e5

/-- Cochrane (2023), (6.9) p. 201, the infinite-horizon present value (moved here from
`MoneyLiquidity`): if `dw/dτ = a w − f`
with `a = r^f − g > 0`, `f` continuous and bounded, and the transversality condition
`e^{−a(T−t)} w_T → 0` holds, then `f` discounted at `a` is integrable on `(t, ∞)` and
`w_t = ∫_t^∞ e^{−a(τ−t)} f_τ dτ`. -/
theorem forward_present_value {a K : ℝ} (ha : 0 < a) {w f : ℝ → ℝ}
    (hw : ∀ τ, HasDerivAt w (a * w τ - f τ) τ) (hf : Continuous f) (hK : ∀ τ, |f τ| ≤ K)
    (t : ℝ) (htvc : Tendsto (fun T => Real.exp (-a * (T - t)) * w T) atTop (𝓝 0)) :
    IntegrableOn (fun τ => Real.exp (-a * (τ - t)) * f τ) (Set.Ioi t) ∧
      w t = ∫ τ in Set.Ioi t, Real.exp (-a * (τ - t)) * f τ := by
  have hint : IntegrableOn (fun τ => Real.exp (-a * (τ - t)) * f τ) (Set.Ioi t) := by
    have hexp : IntegrableOn (fun τ => K * (Real.exp (a * t) * Real.exp (-a * τ)))
        (Set.Ioi t) := ((exp_neg_integrableOn_Ioi t ha).const_mul _).const_mul K
    refine hexp.mono' ?_ (Filter.Eventually.of_forall fun τ => ?_)
    · exact (by fun_prop : Continuous fun τ => Real.exp (-a * (τ - t)) * f τ)
        |>.aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs, Real.abs_exp, ← Real.exp_add, Real.norm_eq_abs,
        mul_comm]
      have : -a * (τ - t) = a * t + -a * τ := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (hK τ) (Real.exp_pos _).le
  refine ⟨hint, ?_⟩
  have hlim := intervalIntegral_tendsto_integral_Ioi t hint tendsto_id
  have hsum := hlim.add htvc
  rw [add_zero] at hsum
  have hconst : (fun T => (∫ τ in t..T, Real.exp (-a * (τ - t)) * f τ) +
      Real.exp (-a * (T - t)) * w T) = fun _ => w t := by
    funext T; exact (finite_horizon_identity hw hf t T).symm
  simp only [id] at hsum
  rw [hconst] at hsum
  exact tendsto_nhds_unique tendsto_const_nhds hsum

end Cochrane.FiscalConstraints.LinearODE
