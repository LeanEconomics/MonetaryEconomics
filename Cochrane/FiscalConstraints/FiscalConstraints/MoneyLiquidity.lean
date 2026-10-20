/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.GrowthTheoryTVC
import FiscalConstraints.LinearODE
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Liquidity, seigniorage and `r < g`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.5, pp. 200–203,
equations (6.7)–(6.13).

A government financed by non-interest-bearing money `M` with money demand `M V(i) = P y`
earns a return `−π` on its liabilities, below growth `g`, yet the value of money is a
well-defined present value when discounted at the real rate `r^f > g`. Money and nominal
debt `B` evolve by `d(M + B)/dt = i B − P s` (money-only: (6.7) `dM/dt = −P s`), the price level
by `dP/dt = π P` and output by `dy/dt = g y`.

## Main results

* `money_growth`: constant velocity gives `(1/M) dM/dt = π + g` (p. 201).
* `steady_state_deficit` (6.8) and `middle_term` (p. 202): `s/y + i M/(Py) = (r^f − g) M/(Py)`.
* `hasDerivAt_moneyRatio` (6.10) and `hasDerivAt_moneyRatio_rf` (6.11) as exact derivatives;
  `hasDerivAt_liabilityRatio` for money plus interest-bearing debt.
* The variation-of-constants identity behind (6.12) and (6.13) and the forward present value
  are the general `LinearODE.finite_horizon_identity` and `LinearODE.forward_present_value`.
* `eq_6_12`, `eq_6_13`: both finite-horizon representations hold on the same path.
* `eq_6_9`: with `r^f > g`, bounded flows and the transversality condition, the value of
  money and debt is the improper present-value integral (6.9) of surpluses plus seigniorage.
* `steady_6_12_explodes`: in the steady state the two terms of (6.12) diverge to `−∞` and `+∞`.
* `steady_6_13_converges`: both terms of (6.13) converge.
* `tvc_mrs_iff`, `return_discounted_terminal_explodes`: the transversality condition holds
  with the marginal rate of substitution, but the terminal term discounted at the ex-post
  return on money explodes (p. 203).
-/

namespace Cochrane.FiscalConstraints.MoneyLiquidity

open Filter Topology MeasureTheory
open Cochrane.FiscalConstraints.LinearODE (finite_horizon_identity forward_present_value)
open Cochrane.FiscalConstraints.ExpIntegrals (tvc_of_bounded)

/-- Cochrane (2023), p. 201: with constant velocity, `M V = P y`, `dP/dt = π P` and
`dy/dt = g y`, money grows at `π + g`: `dM/dt = (π + g) M`. -/
theorem money_growth {M P y : ℝ → ℝ} {V infl g t : ℝ} (hV : 0 < V)
    (hMV : ∀ τ, M τ * V = P τ * y τ) (hP : HasDerivAt P (infl * P t) t)
    (hy : HasDerivAt y (g * y t) t) : HasDerivAt M ((infl + g) * M t) t := by
  have hM : M = fun τ => P τ * y τ / V := by
    funext τ; rw [← hMV τ, mul_div_cancel_right₀ _ hV.ne']
  have h := (hP.mul hy).div_const V
  rw [hM]
  convert h using 1
  field_simp

/-- Cochrane (2023), (6.8) p. 201: if money finances deficits, `dM/dt = −P s` (6.7), and
money grows at `π + g`, then `(π + g) M/(P y) = −s/y`. -/
theorem steady_state_deficit {M P y s infl g : ℝ} (hP : P ≠ 0) (hy : y ≠ 0)
    (h67 : (infl + g) * M = -(P * s)) : (infl + g) * (M / (P * y)) = -(s / y) := by
  field_simp
  linear_combination h67

/-- Cochrane (2023), p. 202: with the steady-state deficit (6.8) and `i = r^f + π`, the middle
term of (6.9) is `s/y + i M/(Py) = (r^f − g) M/(Py)`. -/
theorem middle_term {m σ infl g rf i : ℝ} (hi : i = rf + infl)
    (h68 : (infl + g) * m = -σ) : σ + i * m = (rf - g) * m := by
  subst hi; linarith

/-- Cochrane (2023), p. 202 ("the seigniorage term is larger than the deficit term"): with
`r^f > g` and positive real money, seigniorage `i M/(Py)` exceeds the deficit `−s/y`. -/
theorem seigniorage_exceeds_deficit {m σ infl g rf i : ℝ} (hi : i = rf + infl)
    (h68 : (infl + g) * m = -σ) (hrg : g < rf) (hm : 0 < m) : -σ < i * m := by
  have := middle_term hi h68
  nlinarith

/-- Cochrane (2023), p. 201 ("the rate of return on government debt is `r = −π`, so
`r < g`"): in the steady state (6.8) with a deficit `s < 0` and positive real money, the
return on money `−π` is below growth `g`. -/
theorem money_return_lt_growth {m σ infl g : ℝ} (h68 : (infl + g) * m = -σ) (hσ : σ < 0)
    (hm : 0 < m) : -infl < g := by
  by_contra h
  push Not at h
  nlinarith

/-- Cochrane (2023), (6.10) p. 202 and footnote 1, as an exact derivative: with (6.7)
`dM/dt = −P s`, `dP/dt = π P` and `dy/dt = g y`, the money/GDP ratio `m = M/(P y)` satisfies
`dm/dt + m (π + g) = −s/y`. -/
theorem hasDerivAt_moneyRatio {M P y s infl g : ℝ → ℝ} {t : ℝ}
    (hM : HasDerivAt M (-(P t * s t)) t) (hP : HasDerivAt P (infl t * P t) t)
    (hy : HasDerivAt y (g t * y t) t) (hP0 : P t ≠ 0) (hy0 : y t ≠ 0) :
    HasDerivAt (fun τ => M τ / (P τ * y τ))
      (-(s t / y t) - M t / (P t * y t) * (infl t + g t)) t := by
  have h := hM.div (hP.mul hy) (mul_ne_zero hP0 hy0)
  convert h using 1
  simp only [Pi.mul_apply]
  field_simp

/-- Cochrane (2023), (6.11) p. 202: with `i = r^f + π` the same law of motion reads
`dm/dt + m (i − r^f + g) = −s/y`. -/
theorem hasDerivAt_moneyRatio_rf {M P y s infl g i : ℝ → ℝ} {rf t : ℝ}
    (hi : i t = rf + infl t)
    (hM : HasDerivAt M (-(P t * s t)) t) (hP : HasDerivAt P (infl t * P t) t)
    (hy : HasDerivAt y (g t * y t) t) (hP0 : P t ≠ 0) (hy0 : y t ≠ 0) :
    HasDerivAt (fun τ => M τ / (P τ * y τ))
      (-(s t / y t) - M t / (P t * y t) * (i t - rf + g t)) t := by
  have h := hasDerivAt_moneyRatio hM hP hy hP0 hy0
  rw [hi]
  convert h using 2
  ring

/-- Cochrane (2023), (6.9) p. 201, flow form with money and interest-bearing debt: if
`d(M + B)/dt = i B − P s`, the ratio `w = (M + B)/(P y)` satisfies
`dw/dt = (i − π − g) w − i M/(P y) − s/y`. -/
theorem hasDerivAt_liabilityRatio {M B P y s infl g i : ℝ → ℝ} {t : ℝ}
    (hW : HasDerivAt (fun τ => M τ + B τ) (i t * B t - P t * s t) t)
    (hP : HasDerivAt P (infl t * P t) t) (hy : HasDerivAt y (g t * y t) t)
    (hP0 : P t ≠ 0) (hy0 : y t ≠ 0) :
    HasDerivAt (fun τ => (M τ + B τ) / (P τ * y τ))
      ((i t - infl t - g t) * ((M t + B t) / (P t * y t)) - i t * (M t / (P t * y t))
        - s t / y t) t := by
  have h := hW.div (hP.mul hy) (mul_ne_zero hP0 hy0)
  convert h using 1
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- Cochrane (2023), (6.12) p. 202: integrating (6.10) forward at the money return,
`M_t/(P_t y_t) = ∫_t^T e^{(π+g)(τ−t)} s_τ/y_τ dτ + e^{(π+g)(T−t)} M_T/(P_T y_T)`, for constant
inflation `π` and growth `g`. -/
theorem eq_6_12 {M P y s : ℝ → ℝ} {infl g : ℝ}
    (hM : ∀ τ, HasDerivAt M (-(P τ * s τ)) τ) (hP : ∀ τ, HasDerivAt P (infl * P τ) τ)
    (hy : ∀ τ, HasDerivAt y (g * y τ) τ) (hP0 : ∀ τ, P τ ≠ 0) (hy0 : ∀ τ, y τ ≠ 0)
    (hs : Continuous s) (t T : ℝ) :
    M t / (P t * y t) = (∫ τ in t..T, Real.exp ((infl + g) * (τ - t)) * (s τ / y τ)) +
      Real.exp ((infl + g) * (T - t)) * (M T / (P T * y T)) := by
  have hyc : Continuous y := continuous_iff_continuousAt.mpr fun τ => (hy τ).continuousAt
  have hf : Continuous fun τ => s τ / y τ := hs.div hyc hy0
  have hw : ∀ τ, HasDerivAt (fun x => M x / (P x * y x))
      (-(infl + g) * (M τ / (P τ * y τ)) - s τ / y τ) τ := fun τ => by
    have h := hasDerivAt_moneyRatio (g := fun _ => g) (infl := fun _ => infl) (hM τ) (hP τ)
      (hy τ) (hP0 τ) (hy0 τ)
    convert h using 1
    ring
  have h := finite_horizon_identity hw hf t T
  simpa only [neg_neg] using h

/-- Cochrane (2023), (6.13) p. 203: integrating (6.11) forward at the real rate `r^f`, the
money/GDP ratio is the discounted value of surpluses plus seigniorage over `[t, T]` plus a
terminal term: `m_t = ∫_t^T e^{−(r^f−g)(τ−t)} (s_τ/y_τ + i_τ m_τ) dτ + e^{−(r^f−g)(T−t)} m_T`,
with `i_τ = r^f + π_τ`. -/
theorem eq_6_13 {M P y s infl : ℝ → ℝ} {g rf : ℝ}
    (hM : ∀ τ, HasDerivAt M (-(P τ * s τ)) τ) (hP : ∀ τ, HasDerivAt P (infl τ * P τ) τ)
    (hy : ∀ τ, HasDerivAt y (g * y τ) τ) (hP0 : ∀ τ, P τ ≠ 0) (hy0 : ∀ τ, y τ ≠ 0)
    (hs : Continuous s) (hinfl : Continuous infl) (t T : ℝ) :
    M t / (P t * y t) = (∫ τ in t..T, Real.exp (-(rf - g) * (τ - t)) *
        (s τ / y τ + (rf + infl τ) * (M τ / (P τ * y τ)))) +
      Real.exp (-(rf - g) * (T - t)) * (M T / (P T * y T)) := by
  have hyc : Continuous y := continuous_iff_continuousAt.mpr fun τ => (hy τ).continuousAt
  have hPc : Continuous P := continuous_iff_continuousAt.mpr fun τ => (hP τ).continuousAt
  have hMc : Continuous M := continuous_iff_continuousAt.mpr fun τ => (hM τ).continuousAt
  have hf : Continuous fun τ => s τ / y τ + (rf + infl τ) * (M τ / (P τ * y τ)) :=
    (hs.div hyc hy0).add ((continuous_const.add hinfl).mul
      (hMc.div (hPc.mul hyc) fun τ => mul_ne_zero (hP0 τ) (hy0 τ)))
  have hw : ∀ τ, HasDerivAt (fun x => M x / (P x * y x))
      ((rf - g) * (M τ / (P τ * y τ)) -
        (s τ / y τ + (rf + infl τ) * (M τ / (P τ * y τ)))) τ := fun τ => by
    have h := hasDerivAt_moneyRatio (g := fun _ => g) (hM τ) (hP τ) (hy τ) (hP0 τ) (hy0 τ)
    convert h using 1
    ring
  exact finite_horizon_identity hw hf t T

/-- Cochrane (2023), (6.9) p. 201: the value of money and nominal debt as a fraction of GDP
is the present value, discounted at `r^f − g > 0`, of surpluses plus the interest saving on
money, `(M_t + B_t)/(P_t y_t) = ∫_t^∞ e^{−(r^f−g)(τ−t)} (s_τ/y_τ + i_τ M_τ/(P_τ y_τ)) dτ`,
given `i = r^f + π`, bounded continuous flows and the transversality condition. -/
theorem eq_6_9 {M B P y s infl i : ℝ → ℝ} {g rf K : ℝ} (hrg : g < rf)
    (hW : ∀ τ, HasDerivAt (fun x => M x + B x) (i τ * B τ - P τ * s τ) τ)
    (hP : ∀ τ, HasDerivAt P (infl τ * P τ) τ) (hy : ∀ τ, HasDerivAt y (g * y τ) τ)
    (hP0 : ∀ τ, P τ ≠ 0) (hy0 : ∀ τ, y τ ≠ 0) (hi : ∀ τ, i τ = rf + infl τ)
    (hf : Continuous fun τ => s τ / y τ + i τ * (M τ / (P τ * y τ)))
    (hK : ∀ τ, |s τ / y τ + i τ * (M τ / (P τ * y τ))| ≤ K) (t : ℝ)
    (htvc : Tendsto (fun T => Real.exp (-(rf - g) * (T - t)) * ((M T + B T) / (P T * y T)))
      atTop (𝓝 0)) :
    (M t + B t) / (P t * y t) = ∫ τ in Set.Ioi t, Real.exp (-(rf - g) * (τ - t)) *
      (s τ / y τ + i τ * (M τ / (P τ * y τ))) := by
  have hw : ∀ τ, HasDerivAt (fun x => (M x + B x) / (P x * y x))
      ((rf - g) * ((M τ + B τ) / (P τ * y τ)) -
        (s τ / y τ + i τ * (M τ / (P τ * y τ)))) τ := fun τ => by
    have h := hasDerivAt_liabilityRatio (g := fun _ => g) (hW τ) (hP τ) (hy τ) (hP0 τ) (hy0 τ)
    convert h using 1
    rw [hi τ]
    ring
  exact (forward_present_value (by linarith) hw hf hK t htvc).2

/-- Cochrane (2023), (6.9) p. 201: the value of debt is unique: two liability paths solving the
same flow equation and both satisfying the transversality condition coincide. -/
theorem present_value_unique {a K : ℝ} (ha : 0 < a) {w₁ w₂ f : ℝ → ℝ}
    (h₁ : ∀ τ, HasDerivAt w₁ (a * w₁ τ - f τ) τ) (h₂ : ∀ τ, HasDerivAt w₂ (a * w₂ τ - f τ) τ)
    (hf : Continuous f) (hK : ∀ τ, |f τ| ≤ K) (t : ℝ)
    (htvc₁ : Tendsto (fun T => Real.exp (-a * (T - t)) * w₁ T) atTop (𝓝 0))
    (htvc₂ : Tendsto (fun T => Real.exp (-a * (T - t)) * w₂ T) atTop (𝓝 0)) :
    w₁ t = w₂ t := by
  rw [(forward_present_value ha h₁ hf hK t htvc₁).2, (forward_present_value ha h₂ hf hK t htvc₂).2]

/-- Cochrane (2023), (6.12) p. 202 ("the terminal condition explodes ... the present value
integral also explodes negatively"): in a steady state with constant positive real money
`m̄`, constant deficit ratio `σ̄` and `π + g > 0`, satisfying (6.8), the present-value term of
(6.12) tends to `−∞` and the terminal term to `+∞`, while their sum is `m̄`. -/
theorem steady_6_12_explodes {m σ infl g : ℝ} (hm : 0 < m) (hk : 0 < infl + g)
    (h68 : (infl + g) * m = -σ) (t : ℝ) :
    (∀ T, (∫ τ in t..T, Real.exp ((infl + g) * (τ - t)) * σ) +
        Real.exp ((infl + g) * (T - t)) * m = m) ∧
      Tendsto (fun T => ∫ τ in t..T, Real.exp ((infl + g) * (τ - t)) * σ) atTop atBot ∧
      Tendsto (fun T => Real.exp ((infl + g) * (T - t)) * m) atTop atTop := by
  have hw : ∀ τ, HasDerivAt (fun _ : ℝ => m) (-(infl + g) * m - σ) τ := fun τ => by
    convert hasDerivAt_const τ m using 1
    linarith
  have hid : ∀ T, (∫ τ in t..T, Real.exp ((infl + g) * (τ - t)) * σ) +
      Real.exp ((infl + g) * (T - t)) * m = m := fun T => by
    have h := finite_horizon_identity hw (continuous_const (y := σ)) t T
    simp only [neg_neg] at h
    exact h.symm
  have hterm : Tendsto (fun T => Real.exp ((infl + g) * (T - t)) * m) atTop atTop := by
    have h1 : Tendsto (fun T : ℝ => (infl + g) * (T - t)) atTop atTop :=
      (tendsto_atTop_add_const_right _ _ tendsto_id).const_mul_atTop hk
    exact (Real.tendsto_exp_atTop.comp h1).atTop_mul_const hm
  refine ⟨hid, ?_, hterm⟩
  have heq : (fun T => ∫ τ in t..T, Real.exp ((infl + g) * (τ - t)) * σ) =
      fun T => m - Real.exp ((infl + g) * (T - t)) * m := by
    funext T; linarith [hid T]
  rw [heq]
  exact tendsto_atBot_add_const_left _ m (tendsto_neg_atTop_atBot.comp hterm)

/-- Cochrane (2023), (6.13) p. 203 ("both the present value and the terminal condition
converge"): in the steady state of (6.8) with `i = r^f + π` and `r^f > g`, the present-value
term of (6.13) tends to `m̄` and the terminal term to `0`. -/
theorem steady_6_13_converges {m σ infl g rf i : ℝ} (hi : i = rf + infl) (hrg : g < rf)
    (h68 : (infl + g) * m = -σ) (t : ℝ) :
    (∀ T, (∫ τ in t..T, Real.exp (-(rf - g) * (τ - t)) * (σ + i * m)) +
        Real.exp (-(rf - g) * (T - t)) * m = m) ∧
      Tendsto (fun T => ∫ τ in t..T, Real.exp (-(rf - g) * (τ - t)) * (σ + i * m)) atTop
        (𝓝 m) ∧
      Tendsto (fun T => Real.exp (-(rf - g) * (T - t)) * m) atTop (𝓝 0) := by
  have hmid := middle_term hi h68
  have hw : ∀ τ, HasDerivAt (fun _ : ℝ => m) ((rf - g) * m - (σ + i * m)) τ := fun τ => by
    convert hasDerivAt_const τ m using 1
    linarith
  have hid : ∀ T, (∫ τ in t..T, Real.exp (-(rf - g) * (τ - t)) * (σ + i * m)) +
      Real.exp (-(rf - g) * (T - t)) * m = m := fun T =>
    (finite_horizon_identity hw continuous_const t T).symm
  have hterm : Tendsto (fun T => Real.exp (-(rf - g) * (T - t)) * m) atTop (𝓝 0) :=
    tvc_of_bounded (C := |m|) (by linarith) (fun _ => le_rfl) t
  refine ⟨hid, ?_, hterm⟩
  have heq : (fun T => ∫ τ in t..T, Real.exp (-(rf - g) * (τ - t)) * (σ + i * m)) =
      fun T => m - Real.exp (-(rf - g) * (T - t)) * m := by
    funext T; linarith [hid T]
  rw [heq]
  simpa using (tendsto_const_nhds (x := m)).sub hterm

/-- Cochrane (2023), p. 203: the transversality condition with marginal-utility discounting.
With `M_T/P_T = m̄ y_T`, `y_T = y_t e^{g(T−t)}` and the marginal rate of substitution
`e^{−r^f(T−t)}`, `lim e^{−r^f(T−t)} M_T/P_T = 0` iff `r^f > g` (for `m̄ y_t > 0`). -/
theorem tvc_mrs_iff {m yt rf g t : ℝ} (hm : 0 < m * yt) :
    Tendsto (fun T => Real.exp (-rf * (T - t)) * (m * (yt * Real.exp (g * (T - t)))))
      atTop (𝓝 0) ↔ g < rf := by
  have heq : (fun T => Real.exp (-rf * (T - t)) * (m * (yt * Real.exp (g * (T - t))))) =
      (fun s => m * yt * Real.exp ((g - rf) * s)) ∘ (fun T => T - t) := by
    funext T
    simp only [Function.comp]
    rw [mul_comm (Real.exp _), mul_assoc m, mul_assoc, mul_assoc, ← Real.exp_add]
    ring_nf
  have hshift : Tendsto (fun T : ℝ => T - t) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  rw [heq]
  constructor
  · intro h
    have h2 : Tendsto (fun s => m * yt * Real.exp ((g - rf) * s)) atTop (𝓝 0) := by
      have := h.comp (tendsto_atTop_add_const_right atTop t tendsto_id)
      refine this.congr fun s => ?_
      simp
    rw [ExpIntegrals.tendsto_const_mul_exp_zero_iff hm] at h2
    linarith
  · intro h
    exact ((ExpIntegrals.tendsto_const_mul_exp_zero_iff hm).mpr (by linarith)).comp hshift

/-- Cochrane (2023), p. 203 ("we discount using the consumer's marginal rate of
substitution"): power utility over `c = y = y₀ e^{g τ}` with discount rate `ρ` gives
`e^{−ρ(τ−t)} u'(c_τ)/u'(c_t) = e^{−r^f(τ−t)}` with `r^f = ρ + γ g`. -/
theorem mrs_eq_riskfree {y₀ : ℝ} (hy : 0 < y₀) (ρ γ g t τ : ℝ) :
    GrowthTheoryTVC.marginalUtility ρ γ y₀ g τ / GrowthTheoryTVC.marginalUtility ρ γ y₀ g t =
      Real.exp (-(ρ + γ * g) * (τ - t)) :=
  GrowthTheoryTVC.marginalUtility_ratio hy ρ γ g t τ

/-- Cochrane (2023), p. 203 ("even when the transversality condition holds, the terminal
condition does not necessarily hold discounting with the ex-post return"): with `r^f > g` and
`π + g > 0` (money's return `−π` below growth), the marginal-utility-discounted terminal value
of real money tends to `0` while the terminal value discounted at the return on money,
`e^{π(T−t)} M_T/P_T`, tends to `+∞`. -/
theorem return_discounted_terminal_explodes {m yt rf g infl t : ℝ} (hm : 0 < m * yt)
    (hrg : g < rf) (hk : 0 < infl + g) :
    Tendsto (fun T => Real.exp (-rf * (T - t)) * (m * (yt * Real.exp (g * (T - t)))))
        atTop (𝓝 0) ∧
      Tendsto (fun T => Real.exp (infl * (T - t)) * (m * (yt * Real.exp (g * (T - t)))))
        atTop atTop := by
  refine ⟨(tvc_mrs_iff hm).mpr hrg, ?_⟩
  have heq : (fun T => Real.exp (infl * (T - t)) * (m * (yt * Real.exp (g * (T - t))))) =
      (fun s => m * yt * Real.exp ((infl + g) * s)) ∘ (fun T => T - t) := by
    funext T
    simp only [Function.comp]
    rw [mul_comm (Real.exp _), mul_assoc m, mul_assoc, mul_assoc, ← Real.exp_add]
    ring_nf
  rw [heq]
  exact (ExpIntegrals.tendsto_const_mul_exp_atTop hm hk).comp
    (tendsto_atTop_add_const_right _ _ tendsto_id)

end Cochrane.FiscalConstraints.MoneyLiquidity
