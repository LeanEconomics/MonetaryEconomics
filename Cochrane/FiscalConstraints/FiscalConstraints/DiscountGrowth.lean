/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.ExpIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Discount rates and growth

Cochrane (2023), Chapter 6, §6.2 *Discount rates*, eqs. (6.1)–(6.2), pp. 191–193, and the
consumer first-order condition (6.6) with population growth, §6.4.4, pp. 199–200.

The representative consumer's first-order condition links the real rate to growth,
`r = δ + γ g` (6.1). The value of debt with a constant surplus/GDP ratio is
`B/(P y) = (s/y)/(r - g)` (6.2). Substituting (6.1), the value is `(s/y)/(δ + (γ - 1) g)`: for
`γ = 1` it does not depend on `g`, for `γ > 1` it falls with `g` (p. 191).

## Main results

* `euler_discrete_iff`: the discrete-time Euler equation `e^{-δ}(1+g)^{-γ}(1+r) = 1` holds iff
  `log(1+r) = δ + γ log(1+g)` (the exact log form of (6.1)).
* `marginalValue_hasDerivAt`, `euler_continuous_iff`: in continuous time the discounted marginal
  utility of a unit invested at `r`, `e^{-δt} c(t)^{-γ} e^{rt}`, is stationary at `t` iff
  `r = δ + γ ċ/c`; `euler_exponential_iff`: along `c(t) = c₀ e^{gt}` it is constant iff
  `r = δ + γ g` (6.1), (6.6).
* `value_of_debt_eq` (6.2), `value_of_debt_not_integrable`.
* `value_indep_of_g` (`γ = 1`), `value_hasDerivAt`, `value_strictAntiOn` (`γ > 1`),
  `value_strictMonoOn` (`γ < 1`), `log_value_hasDerivAt` (cash-flow effect `1/(r-g)` minus
  discount-rate effect `γ/(r-g)`).
* `percapita_growth`, `euler_population_iff`, `r_lt_g_population_iff`: with population growth `n`
  the per-capita first-order condition is `r = δ + γ(g - n)` (p. 200), so `r < g` iff
  `δ + (γ - 1) g < γ n`.
-/

namespace Cochrane.FiscalConstraints.DiscountGrowth

open Real MeasureTheory Filter Topology
open Cochrane.FiscalConstraints.ExpIntegrals

/-- Cochrane (2023), eq. (6.1), p. 191 (discrete-time exact form): with gross growth `1 + g > 0`
and gross return `1 + r > 0`, the consumer's Euler equation `e^{-δ}(1+g)^{-γ}(1+r) = 1` holds iff
`log(1+r) = δ + γ log(1+g)`. -/
theorem euler_discrete_iff {r g : ℝ} (hr : 0 < 1 + r) (hg : 0 < 1 + g) (δ γ : ℝ) :
    exp (-δ) * (1 + g) ^ (-γ) * (1 + r) = 1 ↔ log (1 + r) = δ + γ * log (1 + g) := by
  have h : exp (-δ) * (1 + g) ^ (-γ) * (1 + r) =
      exp (-δ - γ * log (1 + g) + log (1 + r)) := by
    rw [rpow_def_of_pos hg, exp_add, exp_log hr, sub_eq_add_neg, exp_add]
    ring_nf
  rw [h, exp_eq_one_iff]
  constructor <;> intro h' <;> linarith

/-- Cochrane (2023), eq. (6.1), p. 191: the time-`t` value, in marginal utility, of a unit
invested at the real rate `r`: `λ(t) = e^{-δt} c(t)^{-γ} e^{rt}`. -/
noncomputable def marginalValue (δ γ r : ℝ) (c : ℝ → ℝ) (t : ℝ) : ℝ :=
  exp (-δ * t) * c t ^ (-γ) * exp (r * t)

/-- Cochrane (2023), eq. (6.1), p. 191: exact derivative of `λ(t) = e^{-δt} c(t)^{-γ} e^{rt}`,
`λ'(t) = λ(t) (r - δ - γ ċ/c)`. -/
theorem marginalValue_hasDerivAt {δ γ r : ℝ} {c : ℝ → ℝ} {c' t : ℝ} (hc : 0 < c t)
    (hd : HasDerivAt c c' t) :
    HasDerivAt (marginalValue δ γ r c)
      (marginalValue δ γ r c t * (r - δ - γ * (c' / c t))) t := by
  have h1 : HasDerivAt (fun s => exp (-δ * s)) (exp (-δ * t) * -δ) t := by
    simpa using ((hasDerivAt_id t).const_mul (-δ)).exp
  have h3 : HasDerivAt (fun s => exp (r * s)) (exp (r * t) * r) t := by
    simpa using ((hasDerivAt_id t).const_mul r).exp
  have h2 : HasDerivAt (fun s => c s ^ (-γ)) (c' * (-γ) * c t ^ (-γ - 1)) t :=
    hd.rpow_const (Or.inl hc.ne')
  have h := (h1.mul h2).mul h3
  unfold marginalValue
  refine h.congr_deriv ?_
  have hcpow : c t ^ (-γ - 1) = c t ^ (-γ) / c t := by
    rw [rpow_sub hc, rpow_one]
  rw [hcpow]
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- Cochrane (2023), eq. (6.1), p. 191: the consumer is indifferent to shifting consumption at
`t` (the marginal value `λ` is stationary, `λ'(t) = 0`) iff `r = δ + γ ċ/c`. -/
theorem euler_continuous_iff {δ γ r : ℝ} {c : ℝ → ℝ} {c' t : ℝ} (hc : 0 < c t)
    (hd : HasDerivAt c c' t) :
    HasDerivAt (marginalValue δ γ r c) 0 t ↔ r = δ + γ * (c' / c t) := by
  have h := marginalValue_hasDerivAt (δ := δ) (γ := γ) (r := r) hc hd
  have hpos : 0 < marginalValue δ γ r c t := by
    unfold marginalValue
    exact mul_pos (mul_pos (exp_pos _) (rpow_pos_of_pos hc _)) (exp_pos _)
  constructor
  · intro h0
    have := h.unique h0
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hpos.ne'
    · linarith
  · intro hr
    have : r - δ - γ * (c' / c t) = 0 := by linarith
    rw [this, mul_zero] at h
    exact h

/-- Cochrane (2023), eqs. (6.1), p. 191, and (6.6), p. 199: along consumption growing at rate
`g`, `c(t) = c₀ e^{g t}` with `c₀ > 0`, the marginal value `λ(t)` is constant over time iff
`r = δ + γ g`. -/
theorem euler_exponential_iff {c₀ : ℝ} (hc₀ : 0 < c₀) (δ γ r g : ℝ) :
    (∀ t, marginalValue δ γ r (fun s => c₀ * exp (g * s)) t =
        marginalValue δ γ r (fun s => c₀ * exp (g * s)) 0) ↔ r = δ + γ * g := by
  have key : ∀ t, marginalValue δ γ r (fun s => c₀ * exp (g * s)) t =
      c₀ ^ (-γ) * exp ((r - δ - γ * g) * t) := by
    intro t
    unfold marginalValue
    rw [mul_rpow hc₀.le (exp_pos _).le, ← exp_mul]
    have : exp (-δ * t) * (c₀ ^ (-γ) * exp (g * t * -γ)) * exp (r * t) =
        c₀ ^ (-γ) * (exp (-δ * t) * exp (g * t * -γ) * exp (r * t)) := by ring
    rw [this, ← exp_add, ← exp_add]
    ring_nf
  simp only [key, mul_zero, exp_zero, mul_one]
  have hc : 0 < c₀ ^ (-γ) := rpow_pos_of_pos hc₀ _
  constructor
  · intro h
    have h1 := h 1
    rw [mul_one] at h1
    have h2 : exp (r - δ - γ * g) = 1 := by
      have := mul_left_cancel₀ hc.ne' (h1.trans (mul_one _).symm)
      exact this
    rw [exp_eq_one_iff] at h2
    linarith
  · intro hr t
    have : r - δ - γ * g = 0 := by linarith
    rw [this, zero_mul, exp_zero, mul_one]

/-- Cochrane (2023), eq. (6.2), p. 191: with output growing at `g`, `y(t+u) = y(t) e^{g u}`, and a
constant surplus/GDP ratio `σ = s/y`, the value of debt is
`B_t/(P_t y_t) = ∫₀^∞ e^{-r u} σ (y_{t+u}/y_t) du = σ/(r - g)` for `r > g`. -/
theorem value_of_debt_eq {r g σ t : ℝ} (h : g < r) {y : ℝ → ℝ} (hy : y t ≠ 0)
    (hgrow : ∀ u, y (t + u) = y t * exp (g * u)) :
    ∫ u in Set.Ioi (0 : ℝ), exp (-r * u) * (σ * (y (t + u) / y t)) = σ / (r - g) := by
  have : ∀ u, σ * (y (t + u) / y t) = σ * exp (g * u) := by
    intro u
    rw [hgrow u]
    field_simp
  simp_rw [this]
  exact integral_exp_growth h σ

/-- Cochrane (2023), eq. (6.2), p. 191: for `r ≤ g` and `σ ≠ 0` the integral in (6.2) diverges. -/
theorem value_of_debt_not_integrable {r g σ t : ℝ} (h : r ≤ g) (hσ : σ ≠ 0) {y : ℝ → ℝ}
    (hy : y t ≠ 0) (hgrow : ∀ u, y (t + u) = y t * exp (g * u)) :
    ¬ IntegrableOn (fun u => exp (-r * u) * (σ * (y (t + u) / y t))) (Set.Ioi 0) := by
  have : ∀ u, σ * (y (t + u) / y t) = σ * exp (g * u) := by
    intro u
    rw [hgrow u]
    field_simp
  simp_rw [this]
  exact not_integrableOn_exp_growth h hσ

/-- Cochrane (2023), §6.2, p. 191: substituting `r = δ + γ g` (6.1) into (6.2), the value of debt
is `σ/(δ + γ g - g)`. -/
noncomputable def valueOfDebt (σ δ γ g : ℝ) : ℝ := σ / (δ + γ * g - g)

/-- Cochrane (2023), §6.2, p. 191: if `γ = 1`, `r` and `g` move one for one and the value of debt
does not depend on growth. -/
theorem value_indep_of_g (σ δ g g' : ℝ) : valueOfDebt σ δ 1 g = valueOfDebt σ δ 1 g' := by
  unfold valueOfDebt
  ring_nf

/-- Cochrane (2023), §6.2, p. 191: the exact derivative of the value of debt with respect to
growth, `∂/∂g [σ/(δ + (γ-1) g)] = -σ(γ - 1)/(δ + (γ - 1) g)²`. -/
theorem value_hasDerivAt {σ δ γ g : ℝ} (hpos : 0 < δ + γ * g - g) :
    HasDerivAt (valueOfDebt σ δ γ) (-(σ * (γ - 1)) / (δ + γ * g - g) ^ 2) g := by
  have hd : HasDerivAt (fun h => δ + γ * h - h) (γ - 1) g := by
    have h1 : HasDerivAt (fun h => δ + γ * h) γ g := by
      simpa using ((hasDerivAt_id' g).const_mul γ).const_add δ
    exact HasDerivAt.sub h1 (hasDerivAt_id' g)
  have h := (hasDerivAt_const g σ).div hd hpos.ne'
  unfold valueOfDebt
  refine h.congr_deriv ?_
  ring

/-- Cochrane (2023), §6.2, p. 191: with `γ > 1` and positive surpluses, higher growth lowers the
value of debt (on the region `r > g`, i.e. `δ + (γ-1) g > 0`). -/
theorem value_strictAntiOn {σ δ γ : ℝ} (hσ : 0 < σ) (hγ : 1 < γ) :
    StrictAntiOn (valueOfDebt σ δ γ) {g | 0 < δ + γ * g - g} := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < δ + γ * a - a := ha
  have hb' : (0 : ℝ) < δ + γ * b - b := hb
  unfold valueOfDebt
  apply div_lt_div_of_pos_left hσ ha'
  nlinarith

/-- Cochrane (2023), §6.2, p. 191: with `γ < 1` and positive surpluses, higher growth raises the
value of debt (the cash-flow effect dominates). -/
theorem value_strictMonoOn {σ δ γ : ℝ} (hσ : 0 < σ) (hγ : γ < 1) :
    StrictMonoOn (valueOfDebt σ δ γ) {g | 0 < δ + γ * g - g} := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < δ + γ * a - a := ha
  have hb' : (0 : ℝ) < δ + γ * b - b := hb
  unfold valueOfDebt
  apply div_lt_div_of_pos_left hσ hb'
  nlinarith

/-- Cochrane (2023), §6.2, p. 191: "the discount rate effect is larger than the cashflow
effect": the semi-elasticity of the value of debt with respect to `g` is the cash-flow effect
`1/(r - g)` minus the discount-rate effect `γ/(r - g)`, with `r - g = δ + (γ - 1) g`. -/
theorem log_value_hasDerivAt {σ δ γ g : ℝ} (hσ : 0 < σ) (hpos : 0 < δ + γ * g - g) :
    HasDerivAt (fun h => log (valueOfDebt σ δ γ h))
      (1 / (δ + γ * g - g) - γ / (δ + γ * g - g)) g := by
  have h := (value_hasDerivAt (σ := σ) hpos).log
    (by unfold valueOfDebt; exact (div_pos hσ hpos).ne')
  refine h.congr_deriv ?_
  unfold valueOfDebt
  field_simp
  ring

/-- Cochrane (2023), §6.4.4, p. 200: with aggregate consumption `C₀ e^{g t}` and population
`N₀ e^{n t}`, per-capita consumption grows at `g - n`. -/
theorem percapita_growth {C₀ N₀ : ℝ} (hN : N₀ ≠ 0) (g n t : ℝ) :
    C₀ * exp (g * t) / (N₀ * exp (n * t)) = C₀ / N₀ * exp ((g - n) * t) := by
  rw [sub_mul, exp_sub]
  field_simp

/-- Cochrane (2023), §6.4.4, p. 200: the per-capita first-order condition with population growth:
along per-capita consumption `(C₀/N₀) e^{(g - n) t}` the marginal value is constant iff
`r = δ + γ (g - n)`. -/
theorem euler_population_iff {C₀ N₀ : ℝ} (hC : 0 < C₀) (hN : 0 < N₀) (δ γ r g n : ℝ) :
    (∀ t, marginalValue δ γ r (fun s => C₀ / N₀ * exp ((g - n) * s)) t =
        marginalValue δ γ r (fun s => C₀ / N₀ * exp ((g - n) * s)) 0) ↔
      r = δ + γ * (g - n) :=
  euler_exponential_iff (div_pos hC hN) δ γ r (g - n)

/-- Cochrane (2023), §6.4.4, p. 200: with `r = δ + γ (g - n)`, `r < g` iff
`δ + (γ - 1) g < γ n`: population growth makes `r < g` easier. -/
theorem r_lt_g_population_iff {δ γ r g n : ℝ} (hr : r = δ + γ * (g - n)) :
    r < g ↔ δ + (γ - 1) * g < γ * n := by
  rw [hr]
  constructor <;> intro h <;> linarith

end Cochrane.FiscalConstraints.DiscountGrowth
