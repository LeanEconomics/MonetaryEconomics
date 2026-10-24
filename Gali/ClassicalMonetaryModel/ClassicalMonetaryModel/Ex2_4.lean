/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ClassicalMonetaryModel.Ex2_1
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Exercise 2.4: the welfare costs of inflation (Lucas 2000)

Galí (2015), Chapter 2, Exercise 2.4, p. 48. Endowment economy with period utility
`U(C, M/P) = ([C ψ(M/(P C))]^{1−σ} − 1)/(1 − σ)` (log for `σ = 1`), `ψ(z) = z/(χ + z)`,
`χ > 0`, `σ > 0`, and budget `P_t C_t + Q_t B_t + M_t ≤ B_{t−1} + M_{t−1} + P_t Y_t`.
With real balances `m = M/P`, `C ψ(m/C) = C m/(χ C + m)` (`aggX_eq`), so
`1/X = 1/C + χ/m` (`inv_aggX`).

## a. Optimality conditions and money demand

* `hasDerivAt_periodUtility_C`, `hasDerivAt_periodUtility_M` (**exact derivatives**):
  `U_C = X^{−σ} m²/(χC + m)²`, `U_m = X^{−σ} χC²/(χC + m)²`; `mrs_money`: `U_m/U_C = χ (C/m)²`.
* Money versus bonds (holding `δ` more money and `δ` fewer bonds leaves `t+1` resources
  unchanged and costs `(1 − Q_t)δ/P_t` of consumption): `money_foc_necessary`,
  `money_foc_sufficient`, `money_optimum_iff`: optimal iff `U_m = (1 − Q_t) U_C`, i.e.
  `(1 − Q_t) m² = χ C²`. `money_demand_iff`: for `Q_t < 1`,
  `M_t/P_t = C_t (χ/(1 − Q_t))^{1/2}`. `no_money_foc_at_zero_rate`: at `Q_t = 1` the condition
  has no solution (no satiation). `money_demand_log`, `hasDerivAt_money_demand_log`: in logs
  `m − p − c = ½ log χ − ½ log(1 − e^{−i})`, interest semi-elasticity `1/(2(e^i − 1))`.
* Bonds (`EulerEq`, `Q_t U_{C,t}/P_t = β E_t[U_{C,t+1}/P_{t+1}]`): `euler_necessary` (uniform
  continuity of marginal utility), `euler_necessary_finite`, `euler_sufficient`, using the
  generic results of `Ex2_1`.

## b. The Friedman rule

`eqWelfare σ χ Y i` is equilibrium period utility (`C = Y`, money demand at rate `i`).
`eqWelfare_eq`: it equals `u(Y/(1 + s(i)))`, `s(i) = (χ(1 − e^{−i}))^{1/2}`.
`friedman_rule`: it is strictly decreasing in `i > 0`, below the satiation level `u(Y)`, and
tends to `u(Y)` as `i → 0⁺`; `friedman_rule_inflation`: in a steady state `i = ρ + π`, welfare
strictly decreases in `π > −ρ`, so the optimum is the Friedman rule `π = −ρ`.

## c. The welfare cost of inflation (steady state, `Y = 1`, `i = ρ + π`)

With `s_π = s(ρ + π)`:
* `welfareCost_levels` (consumption raised by `λ`, real balances `M/P` at their `π` level):
  if `s_π < 1 + s_0` then `λ(π) = (s_π − s_0)/(1 + s_0 − s_π)` is the unique compensation
  (`welfareCost_levels_unique`); `welfareCost_levels_none`: otherwise no rise in consumption
  compensates.
* `welfareCost_ratio` (consumption and real balances scaled together, velocity at its `π`
  level): `λ(π) = (s_π − s_0)/(1 + s_0)`, unique (`welfareCost_ratio_unique`).
* `welfareCost_levels_pos_iff`, `welfareCost_ratio_pos_iff`: the cost is positive iff `π > 0`.

## d. Interest-rate fluctuations to second order

* `hasDerivAt_W`, `hasDerivAt_W1`: `W(i) = u(1/(1 + s(i)))` (`Wf`, equal to `eqWelfare` at
  `Y = 1` by `eqWelfare_one_eq_Wf`) has `W' = W1`, `W'' = W2` in
  closed form; `welfare_taylor`: `W(i) = W(ī) + W1(ī)(i − ī) + ½ W2(ī)(i − ī)² + O((i − ī)³)`.
* `welfare_fluctuations`: for `i_t = ī + s ε_t` with `|ε_t| ≤ M`, `E_0 ε_t = 0`,
  `∑ βᵗ E_0 W(i_t) − ∑ βᵗ W(ī) = ½ W2(ī) s² ∑ βᵗ E_0 ε_t² + O(s³)`.
* `W2_pos_of_le_two`, `fluctuations_raise_welfare` (**finding**): for `σ ≤ 2` (including log
  utility) `W'' > 0`, so mean-preserving interest-rate fluctuations *raise* welfare to second
  order: the "losses" of part (d) are negative. `W2_pos_iff` gives the exact sign condition.
-/

namespace Gali.ClassicalMonetaryModel.Ex2_4

open Filter Topology

/-! ### Utility -/

/-- Galí (2015), Exercise 2.4, p. 48: `ψ(z) = z/(χ + z)`. -/
noncomputable def psi (χ z : ℝ) : ℝ := z / (χ + z)

/-- Galí (2015), Exercise 2.4, p. 48: the composite `X = C ψ(m/C)`, `m = M/P`. -/
noncomputable def aggX (χ C m : ℝ) : ℝ := C * psi χ (m / C)

/-- Galí (2015), Exercise 2.4, p. 48: period utility `U(C, M/P) = u(C ψ(M/(P C)))` with
`u(x) = (x^{1−σ} − 1)/(1 − σ)` (`log x` for `σ = 1`). -/
noncomputable def periodUtility (σ χ C m : ℝ) : ℝ := Ex2_1.utilC σ (aggX χ C m)

/-- Galí (2015), Exercise 2.4: `C ψ(m/C) = C m/(χ C + m)`. -/
theorem aggX_eq {χ C m : ℝ} (hχ : 0 ≤ χ) (hC : 0 < C) (hm : 0 < m) :
    aggX χ C m = C * m / (χ * C + m) := by
  have h : 0 < χ * C + m := by positivity
  unfold aggX psi
  field_simp

/-- Galí (2015), Exercise 2.4: `X > 0`. -/
theorem aggX_pos {χ C m : ℝ} (hχ : 0 ≤ χ) (hC : 0 < C) (hm : 0 < m) : 0 < aggX χ C m := by
  rw [aggX_eq hχ hC hm]
  positivity

/-- Galí (2015), Exercise 2.4: `1/X = 1/C + χ/m`. -/
theorem inv_aggX {χ C m : ℝ} (hχ : 0 ≤ χ) (hC : 0 < C) (hm : 0 < m) :
    (aggX χ C m)⁻¹ = C⁻¹ + χ / m := by
  rw [aggX_eq hχ hC hm]
  field_simp
  ring

/-- Galí (2015), Exercise 2.4: marginal utility of consumption `U_C = X^{−σ} m²/(χ C + m)²`. -/
noncomputable def margUtilC (σ χ C m : ℝ) : ℝ :=
  (C * m / (χ * C + m)) ^ (-σ) * (m ^ 2 / (χ * C + m) ^ 2)

/-- Galí (2015), Exercise 2.4: marginal utility of real balances
`U_m = X^{−σ} χ C²/(χ C + m)²`. -/
noncomputable def margUtilM (σ χ C m : ℝ) : ℝ :=
  (C * m / (χ * C + m)) ^ (-σ) * (χ * C ^ 2 / (χ * C + m) ^ 2)

/-- Galí (2015), Exercise 2.4 (**exact derivative**): `∂X/∂C = m²/(χ C + m)²`. -/
theorem hasDerivAt_aggX_C {χ C m : ℝ} (hχ : 0 ≤ χ) (hC : 0 < C) (hm : 0 < m) :
    HasDerivAt (fun C' => aggX χ C' m) (m ^ 2 / (χ * C + m) ^ 2) C := by
  have hD : χ * C + m ≠ 0 := by positivity
  have h : HasDerivAt (fun C' => C' * m / (χ * C' + m)) (m ^ 2 / (χ * C + m) ^ 2) C := by
    have := ((hasDerivAt_id' C).mul_const m).div
      (((hasDerivAt_id' C).const_mul χ).add_const m) hD
    refine this.congr_deriv ?_
    field_simp
    ring
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [eventually_gt_nhds hC] with C' hC'
  exact aggX_eq hχ hC' hm

/-- Galí (2015), Exercise 2.4 (**exact derivative**): `∂X/∂m = χ C²/(χ C + m)²`. -/
theorem hasDerivAt_aggX_M {χ C m : ℝ} (hχ : 0 ≤ χ) (hC : 0 < C) (hm : 0 < m) :
    HasDerivAt (fun m' => aggX χ C m') (χ * C ^ 2 / (χ * C + m) ^ 2) m := by
  have hD : χ * C + m ≠ 0 := by positivity
  have h : HasDerivAt (fun m' => C * m' / (χ * C + m')) (χ * C ^ 2 / (χ * C + m) ^ 2) m := by
    have := ((hasDerivAt_id' m).const_mul C).div ((hasDerivAt_id' m).const_add (χ * C)) hD
    refine this.congr_deriv ?_
    field_simp
    ring
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [eventually_gt_nhds hm] with m' hm'
  exact aggX_eq hχ hC hm'

/-- Galí (2015), Exercise 2.4(a) (**exact derivative**): `∂U/∂C = margUtilC`. -/
theorem hasDerivAt_periodUtility_C (σ : ℝ) {χ C m : ℝ} (hχ : 0 ≤ χ) (hC : 0 < C)
    (hm : 0 < m) : HasDerivAt (fun C' => periodUtility σ χ C' m) (margUtilC σ χ C m) C := by
  have h := (Ex2_1.hasDerivAt_utilC σ (aggX_pos hχ hC hm)).comp C (hasDerivAt_aggX_C hχ hC hm)
  rw [aggX_eq hχ hC hm] at h
  exact h

/-- Galí (2015), Exercise 2.4(a) (**exact derivative**): `∂U/∂m = margUtilM`. -/
theorem hasDerivAt_periodUtility_M (σ : ℝ) {χ C m : ℝ} (hχ : 0 ≤ χ) (hC : 0 < C)
    (hm : 0 < m) : HasDerivAt (fun m' => periodUtility σ χ C m') (margUtilM σ χ C m) m := by
  have h := (Ex2_1.hasDerivAt_utilC σ (aggX_pos hχ hC hm)).comp m (hasDerivAt_aggX_M hχ hC hm)
  rw [aggX_eq hχ hC hm] at h
  exact h

/-- Galí (2015), Exercise 2.4(a): `U_m/U_C = χ (C/m)²`. -/
theorem mrs_money (σ : ℝ) {χ C m : ℝ} (hχ : 0 ≤ χ) (hC : 0 < C) (hm : 0 < m) :
    margUtilM σ χ C m / margUtilC σ χ C m = χ * (C / m) ^ 2 := by
  have hD : 0 < χ * C + m := by positivity
  have hX : 0 < (C * m / (χ * C + m)) ^ (-σ) := Real.rpow_pos_of_pos (by positivity) _
  unfold margUtilM margUtilC
  field_simp

/-! ### a. Money versus bonds: the demand for real balances -/

/-- Galí (2015), Exercise 2.4(a): date-`t` utility after holding `δ` more money and `δ` fewer
bonds: consumption falls by `(1 − Q)δ/P`, real balances rise by `δ/P`, and date-`t+1`
resources are unchanged. -/
noncomputable def swapValue (σ χ Q P C m δ : ℝ) : ℝ :=
  periodUtility σ χ (C - (1 - Q) * δ / P) (m + δ / P)

/-- Galí (2015), Exercise 2.4(a): along the money-bond swap, `X` has derivative
`(χ C² − (1 − Q) m²)/(P (χ C + m)²)` at `δ = 0`. -/
theorem hasDerivAt_swap_aggX {χ Q P C m : ℝ} (hχ : 0 ≤ χ) (hP : 0 < P) (hC : 0 < C)
    (hm : 0 < m) :
    HasDerivAt (fun δ => aggX χ (C - (1 - Q) * δ / P) (m + δ / P))
      ((χ * C ^ 2 - (1 - Q) * m ^ 2) / (P * (χ * C + m) ^ 2)) 0 := by
  have hD : χ * C + m ≠ 0 := by positivity
  have hc : HasDerivAt (fun δ : ℝ => C - (1 - Q) * δ / P) (-((1 - Q) / P)) 0 := by
    have := (((hasDerivAt_id' (0 : ℝ)).const_mul (1 - Q)).div_const P).const_sub C
    simpa [mul_div_assoc] using this
  have hmm : HasDerivAt (fun δ : ℝ => m + δ / P) (1 / P) 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).div_const P).const_add m
  have hden : (fun δ : ℝ => χ * (C - (1 - Q) * δ / P) + (m + δ / P)) 0 ≠ 0 := by
    simpa using hD
  have h := HasDerivAt.div (HasDerivAt.mul hc hmm) (HasDerivAt.add (hc.const_mul χ) hmm) hden
  have h' : HasDerivAt (fun δ => (C - (1 - Q) * δ / P) * (m + δ / P)
      / (χ * (C - (1 - Q) * δ / P) + (m + δ / P)))
      ((χ * C ^ 2 - (1 - Q) * m ^ 2) / (P * (χ * C + m) ^ 2)) 0 := by
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply, Pi.add_apply, mul_zero, zero_div, sub_zero, add_zero]
    field_simp
    ring
  refine h'.congr_of_eventuallyEq ?_
  have hc1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < C - (1 - Q) * δ / P :=
    (hc.continuousAt.tendsto).eventually_const_lt (by simpa using hC)
  have hm1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < m + δ / P :=
    (hmm.continuousAt.tendsto).eventually_const_lt (by simpa using hm)
  filter_upwards [hc1, hm1] with δ h1 h2
  exact aggX_eq hχ h1 h2

/-- Galí (2015), Exercise 2.4(a) (**necessity**): if the money-bond swap has a local maximum at
`δ = 0` (with `χ > 0`, `P, C, m > 0`), then `(1 − Q) m² = χ C²`, i.e. `U_m = (1 − Q) U_C`. -/
theorem money_foc_necessary {σ χ Q P C m : ℝ} (hχ : 0 ≤ χ) (hP : 0 < P) (hC : 0 < C)
    (hm : 0 < m) (hloc : IsLocalMax (swapValue σ χ Q P C m) 0) :
    (1 - Q) * m ^ 2 = χ * C ^ 2 := by
  have hX := hasDerivAt_swap_aggX (Q := Q) hχ hP hC hm
  have hpos : 0 < aggX χ (C - (1 - Q) * 0 / P) (m + 0 / P) := by
    simpa using aggX_pos hχ hC hm
  have hu := (Ex2_1.hasDerivAt_utilC σ hpos).comp 0 hX
  have h0 := hloc.hasDerivAt_eq_zero hu
  have hr : 0 < aggX χ (C - (1 - Q) * 0 / P) (m + 0 / P) ^ (-σ) := Real.rpow_pos_of_pos hpos _
  have h1 := (mul_eq_zero.1 h0).resolve_left hr.ne'
  have hD : 0 < P * (χ * C + m) ^ 2 := by positivity
  rw [div_eq_zero_iff] at h1
  rcases h1 with h1 | h1
  · linarith
  · linarith

/-- Galí (2015), Exercise 2.4(a): `1/y ≥ 1/x − (y − x)/x²` for `x, y > 0` (convexity of `1/x`). -/
theorem inv_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : x⁻¹ - (y - x) / x ^ 2 ≤ y⁻¹ := by
  have h : y⁻¹ - (x⁻¹ - (y - x) / x ^ 2) = (y - x) ^ 2 / (x ^ 2 * y) := by
    field_simp
    ring
  have : 0 ≤ (y - x) ^ 2 / (x ^ 2 * y) := by positivity
  linarith

/-- Galí (2015), Exercise 2.4(a) (**sufficiency**): if `(1 − Q) m² = χ C²`, no feasible
money-bond swap `δ` (keeping consumption and real balances positive) raises utility. -/
theorem money_foc_sufficient {σ χ Q P C m : ℝ} (hχ : 0 ≤ χ) (hP : 0 < P) (hC : 0 < C)
    (hm : 0 < m) (hfoc : (1 - Q) * m ^ 2 = χ * C ^ 2) {δ : ℝ}
    (hc : 0 < C - (1 - Q) * δ / P) (hm' : 0 < m + δ / P) :
    swapValue σ χ Q P C m δ ≤ swapValue σ χ Q P C m 0 := by
  unfold swapValue periodUtility
  simp only [mul_zero, zero_div, sub_zero, add_zero]
  have h1 := inv_tangent hC hc
  have h2 := inv_tangent hm hm'
  have hinv : (aggX χ C m)⁻¹ ≤ (aggX χ (C - (1 - Q) * δ / P) (m + δ / P))⁻¹ := by
    rw [inv_aggX hχ hC hm, inv_aggX hχ hc hm']
    have e : (C - (1 - Q) * δ / P - C) / C ^ 2 + χ * ((m + δ / P - m) / m ^ 2) = 0 := by
      field_simp
      linear_combination (-δ) * hfoc
    have h3 : χ * (m⁻¹ - (m + δ / P - m) / m ^ 2) ≤ χ * (m + δ / P)⁻¹ :=
      mul_le_mul_of_nonneg_left h2 hχ
    rw [div_eq_mul_inv χ m, div_eq_mul_inv χ (m + δ / P)]
    nlinarith
  have hle := (inv_le_inv₀ (aggX_pos hχ hC hm) (aggX_pos hχ hc hm')).1 hinv
  exact (Ex2_1.utilC_strictMonoOn σ).monotoneOn (aggX_pos hχ hc hm') (aggX_pos hχ hC hm) hle

/-- Galí (2015), Exercise 2.4(a): for `χ ≥ 0` and `C, m > 0`, holding real balances `m` is
optimal against every feasible money-bond swap iff `(1 − Q) m² = χ C²`
(`U_m/U_C = 1 − Q`, cf. eq. (33), p. 33). -/
theorem money_optimum_iff {σ χ Q P C m : ℝ} (hχ : 0 ≤ χ) (hP : 0 < P) (hC : 0 < C)
    (hm : 0 < m) :
    (∀ δ, 0 < C - (1 - Q) * δ / P → 0 < m + δ / P →
      swapValue σ χ Q P C m δ ≤ swapValue σ χ Q P C m 0) ↔ (1 - Q) * m ^ 2 = χ * C ^ 2 := by
  constructor
  · intro h
    refine money_foc_necessary (σ := σ) hχ hP hC hm ?_
    have hc : Continuous fun δ : ℝ => C - (1 - Q) * δ / P := by fun_prop
    have hmc : Continuous fun δ : ℝ => m + δ / P := by fun_prop
    filter_upwards [(hc.tendsto 0).eventually_const_lt (by simpa using hC),
      (hmc.tendsto 0).eventually_const_lt (by simpa using hm)] with δ h1 h2
    exact h δ h1 h2
  · intro h δ h1 h2
    exact money_foc_sufficient hχ hP hC hm h h1 h2

/-- Galí (2015), Exercise 2.4(a) (**money demand**): for `χ > 0`, `Q < 1` and `C, m > 0`,
`(1 − Q) m² = χ C²` iff `M/P = C (χ/(1 − Q))^{1/2}`. -/
theorem money_demand_iff {χ Q C m : ℝ} (hχ : 0 < χ) (hQ : Q < 1) (hC : 0 < C) (hm : 0 < m) :
    (1 - Q) * m ^ 2 = χ * C ^ 2 ↔ m = C * Real.sqrt (χ / (1 - Q)) := by
  have h1 : 0 < 1 - Q := by linarith
  have hs : Real.sqrt (χ / (1 - Q)) ^ 2 = χ / (1 - Q) := Real.sq_sqrt (by positivity)
  constructor
  · intro h
    have hpos : 0 ≤ C * Real.sqrt (χ / (1 - Q)) := by positivity
    refine (pow_left_inj₀ hm.le hpos two_ne_zero).1 ?_
    rw [mul_pow, hs]
    field_simp
    linarith
  · intro h
    rw [h, mul_pow, hs]
    field_simp

/-- Galí (2015), Exercise 2.4(a): at a zero nominal rate (`Q = 1`) the money condition
`(1 − Q) m² = χ C²` has no solution with `χ, C > 0`: real balances are never satiated. -/
theorem no_money_foc_at_zero_rate {χ C m : ℝ} (hχ : 0 < χ) (hC : 0 < C) :
    (1 - 1) * m ^ 2 ≠ χ * C ^ 2 := by
  have : 0 < χ * C ^ 2 := by positivity
  simp only [sub_self, zero_mul]
  exact this.ne

/-- Galí (2015), Exercise 2.4(a) (**money demand in logs**, exact): with `Q = e^{−i}`, `i > 0`,
`log m − log C = ½ log χ − ½ log(1 − e^{−i})`. -/
theorem money_demand_log {χ i C : ℝ} (hχ : 0 < χ) (hi : 0 < i) (hC : 0 < C) :
    Real.log (C * Real.sqrt (χ / (1 - Real.exp (-i)))) - Real.log C
      = 1 / 2 * Real.log χ - 1 / 2 * Real.log (1 - Real.exp (-i)) := by
  have he : Real.exp (-i) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have h1 : 0 < 1 - Real.exp (-i) := by linarith
  rw [Real.log_mul hC.ne' (Real.sqrt_pos.2 (by positivity)).ne', Real.log_sqrt (by positivity),
    Real.log_div hχ.ne' h1.ne']
  ring

/-- Galí (2015), Exercise 2.4(a) (**exact derivative**): the log money demand
`½ log χ − ½ log(1 − e^{−i})` has derivative `−1/(2(e^i − 1))` in `i > 0`: the interest
semi-elasticity is `η(i) = 1/(2(e^i − 1))`. -/
theorem hasDerivAt_money_demand_log (χ : ℝ) {i : ℝ} (hi : 0 < i) :
    HasDerivAt (fun i => 1 / 2 * Real.log χ - 1 / 2 * Real.log (1 - Real.exp (-i)))
      (-(1 / (2 * (Real.exp i - 1)))) i := by
  have he : Real.exp (-i) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hei : 1 < Real.exp i := Real.one_lt_exp_iff.2 hi
  have hexp : HasDerivAt (fun i => Real.exp (-i)) (-Real.exp (-i)) i := by
    have := (hasDerivAt_neg i).exp
    convert this using 1
    ring
  have h := ((hexp.const_sub 1).log (by linarith)).const_mul (1 / 2) |>.const_sub
    (1 / 2 * Real.log χ)
  refine h.congr_deriv ?_
  rw [Real.exp_neg]
  have : Real.exp i - 1 ≠ 0 := by linarith
  field_simp

/-! ### a. The Euler equation for bonds -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Exercise 2.4(a) and eq. (5), p. 19, node by node:
`Q_t U_{C,t}/P_t = β E_t[U_{C,t+1}/P_{t+1}]`, with `U_C` evaluated at `(C, M/P)`. -/
def EulerEq (β σ χ : ℝ) (Q C m P : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, Q t ω * margUtilC σ χ (C t ω) (m t ω) / P t ω =
    β * 𝔼.E t (fun ω' => margUtilC σ χ (C (t + 1) ω') (m (t + 1) ω') / P (t + 1) ω') ω

/-- Galí (2015), Exercise 2.4(a): expected utility at node `ω` after buying `δ` more bonds at
`t` and consuming the payoff at `t + 1`, money holdings unchanged. -/
noncomputable def perturbedValue (β σ χ : ℝ) (Q C m P : ℕ → Ω → ℝ) (t : ℕ) (δ : ℝ) :
    Ω → ℝ :=
  fun ω => periodUtility σ χ (C t ω - Q t ω * δ / P t ω) (m t ω)
    + β * 𝔼.E t (fun ω' => periodUtility σ χ (C (t + 1) ω' + δ / P (t + 1) ω') (m (t + 1) ω')) ω

/-- Galí (2015), Exercise 2.4(a): `U_C` is nonincreasing in `C` (`σ > 0`, `χ ≥ 0`, `m > 0`). -/
theorem margUtilC_antitoneOn {σ χ m : ℝ} (hσ : 0 < σ) (hχ : 0 ≤ χ) (hm : 0 < m) :
    AntitoneOn (fun C => margUtilC σ χ C m) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  have hDa : 0 < χ * a + m := by positivity
  have hDb : 0 < χ * b + m := by positivity
  have hX : a * m / (χ * a + m) ≤ b * m / (χ * b + m) := by
    rw [div_le_div_iff₀ hDa hDb]
    nlinarith [mul_pos hm hm]
  have h1 : (b * m / (χ * b + m)) ^ (-σ) ≤ (a * m / (χ * a + m)) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hX (by linarith)
  have h2 : m ^ 2 / (χ * b + m) ^ 2 ≤ m ^ 2 / (χ * a + m) ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have : χ * a + m ≤ χ * b + m := by nlinarith
    exact pow_le_pow_left₀ hDa.le this 2
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- Galí (2015), Exercise 2.4(a): `U_C` is continuous in `C` at `C > 0`. -/
theorem margUtilC_continuousAt (σ : ℝ) {χ C m : ℝ} (hχ : 0 ≤ χ) (hC : 0 < C) (hm : 0 < m) :
    ContinuousAt (fun C' => margUtilC σ χ C' m) C := by
  have hD : χ * C + m ≠ 0 := by positivity
  have hX : C * m / (χ * C + m) ≠ 0 := by positivity
  unfold margUtilC
  refine ContinuousAt.mul ?_ ?_
  · exact ((continuousAt_id.mul continuousAt_const).div
      (continuousAt_const.mul continuousAt_id |>.add continuousAt_const) hD).rpow_const
      (Or.inl hX)
  · exact continuousAt_const.div
      ((continuousAt_const.mul continuousAt_id |>.add continuousAt_const).pow 2) (by positivity)

/-- Galí (2015), Exercise 2.4(a) (**necessity of the Euler equation**): if no small bond
perturbation is profitable at any date-`t` node, the Euler equation holds. Hypotheses: `σ > 0`,
`χ ≥ 0`, positive consumption, real balances and prices, a uniform lower bound
`k ≤ P_{t+1} C_{t+1}` and a uniform modulus of continuity of `U_{C,t+1}` (automatic with
finitely many states, `euler_necessary_finite`). -/
theorem euler_necessary {β σ χ : ℝ} {Q C m P : ℕ → Ω → ℝ} {t : ℕ} (hσ : 0 < σ) (hχ : 0 ≤ χ)
    (hC : ∀ ω, 0 < C t ω) (hm : ∀ ω, 0 < m t ω) (hP : ∀ ω, 0 < P t ω)
    (hm1 : ∀ ω, 0 < m (t + 1) ω) (hP1 : ∀ ω, 0 < P (t + 1) ω)
    {k : ℝ} (hk : 0 < k) (hkPC : ∀ ω, k ≤ P (t + 1) ω * C (t + 1) ω)
    (huc : ∀ ε > 0, ∀ᶠ h in 𝓝 (0 : ℝ), ∀ ω,
      |margUtilC σ χ (C (t + 1) ω + h / P (t + 1) ω) (m (t + 1) ω)
        - margUtilC σ χ (C (t + 1) ω) (m (t + 1) ω)| / P (t + 1) ω ≤ ε)
    (hopt : ∀ ω, IsLocalMax (fun δ => perturbedValue 𝔼 β σ χ Q C m P t δ ω) 0) :
    EulerEq 𝔼 β σ χ Q C m P t := by
  intro ω
  have hG := Ex2_1.uniform_of_concave (u := fun ω' c => periodUtility σ χ c (m (t + 1) ω'))
    (D := fun ω' c => margUtilC σ χ c (m (t + 1) ω')) hk hP1 hkPC
    (fun ω' x hx => hasDerivAt_periodUtility_C σ hχ hx (hm1 ω'))
    (fun ω' => margUtilC_antitoneOn hσ hχ (hm1 ω')) huc
  have hin : HasDerivAt (fun δ : ℝ => C t ω - Q t ω * δ / P t ω) (-(Q t ω / P t ω)) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).const_mul (Q t ω)).div_const (P t ω)).const_sub (C t ω)
    simpa [mul_div_assoc] using this
  have hu : HasDerivAt (fun c => periodUtility σ χ c (m t ω)) (margUtilC σ χ (C t ω) (m t ω))
      (C t ω - Q t ω * 0 / P t ω) := by
    simpa using hasDerivAt_periodUtility_C σ hχ (hC ω) (hm ω)
  have h := Ex2_1.euler_necessary_generic 𝔼 (hu.comp 0 hin) hG t ω (hopt ω)
  have hP0 := (hP ω).ne'
  have e : Q t ω * margUtilC σ χ (C t ω) (m t ω) / P t ω
      = -(margUtilC σ χ (C t ω) (m t ω) * -(Q t ω / P t ω)) := by
    field_simp
  rw [e]
  linarith

/-- Galí (2015), Exercise 2.4(a) (**necessity**, finitely many states). -/
theorem euler_necessary_finite [Finite Ω] {β σ χ : ℝ} {Q C m P : ℕ → Ω → ℝ} {t : ℕ}
    (hσ : 0 < σ) (hχ : 0 ≤ χ) (hC : ∀ ω, 0 < C t ω) (hm : ∀ ω, 0 < m t ω)
    (hP : ∀ ω, 0 < P t ω) (hC1 : ∀ ω, 0 < C (t + 1) ω) (hm1 : ∀ ω, 0 < m (t + 1) ω)
    (hP1 : ∀ ω, 0 < P (t + 1) ω)
    (hopt : ∀ ω, IsLocalMax (fun δ => perturbedValue 𝔼 β σ χ Q C m P t δ ω) 0) :
    EulerEq 𝔼 β σ χ Q C m P t := by
  obtain ⟨k, hk, hkPC⟩ : ∃ k, 0 < k ∧ ∀ ω, k ≤ P (t + 1) ω * C (t + 1) ω := by
    rcases isEmpty_or_nonempty Ω with hΩ | hΩ
    · exact ⟨1, one_pos, fun ω => (IsEmpty.false ω).elim⟩
    · obtain ⟨ω₀, h₀⟩ := Finite.exists_min fun ω => P (t + 1) ω * C (t + 1) ω
      exact ⟨_, mul_pos (hP1 ω₀) (hC1 ω₀), h₀⟩
  exact euler_necessary 𝔼 hσ hχ hC hm hP hm1 hP1 hk hkPC
    (Ex2_1.uniformCont_of_finite (D := fun ω' c => margUtilC σ χ c (m (t + 1) ω'))
      (fun ω' => margUtilC_continuousAt σ hχ (hC1 ω') (hm1 ω'))) hopt

/-- Galí (2015), Exercise 2.4(a) (**sufficiency** of the Euler equation, by concavity in
consumption): no feasible bond perturbation raises expected utility. -/
theorem euler_sufficient {β σ χ : ℝ} {Q C m P : ℕ → Ω → ℝ} {t : ℕ} (hσ : 0 < σ) (hβ : 0 ≤ β)
    (hχ : 0 ≤ χ) (hC : ∀ ω, 0 < C t ω) (hm : ∀ ω, 0 < m t ω) (hP : ∀ ω, 0 < P t ω)
    (hC1 : ∀ ω, 0 < C (t + 1) ω) (hm1 : ∀ ω, 0 < m (t + 1) ω)
    (heul : EulerEq 𝔼 β σ χ Q C m P t) {δ : ℝ} (ω : Ω)
    (hfeas : 0 < C t ω - Q t ω * δ / P t ω)
    (hfeas1 : ∀ ω', 0 < C (t + 1) ω' + δ / P (t + 1) ω') :
    perturbedValue 𝔼 β σ χ Q C m P t δ ω ≤ perturbedValue 𝔼 β σ χ Q C m P t 0 ω := by
  have hP0 := (hP ω).ne'
  have hf := Ex2_1.tangent_of_deriv (hC ω) hfeas
    (fun x hx => hasDerivAt_periodUtility_C σ hχ hx (hm ω)) (margUtilC_antitoneOn hσ hχ (hm ω))
  have hG : ∀ ω', periodUtility σ χ (C (t + 1) ω' + δ / P (t + 1) ω') (m (t + 1) ω')
      ≤ periodUtility σ χ (C (t + 1) ω' + 0 / P (t + 1) ω') (m (t + 1) ω')
        + δ * (margUtilC σ χ (C (t + 1) ω') (m (t + 1) ω') / P (t + 1) ω') := by
    intro ω'
    have := Ex2_1.tangent_of_deriv (hC1 ω') (hfeas1 ω')
      (fun x hx => hasDerivAt_periodUtility_C σ hχ hx (hm1 ω'))
      (margUtilC_antitoneOn hσ hχ (hm1 ω'))
    rw [zero_div, add_zero]
    have e : margUtilC σ χ (C (t + 1) ω') (m (t + 1) ω')
        * (C (t + 1) ω' + δ / P (t + 1) ω' - C (t + 1) ω')
        = δ * (margUtilC σ χ (C (t + 1) ω') (m (t + 1) ω') / P (t + 1) ω') := by ring
    linarith
  have hfoc : -(margUtilC σ χ (C t ω) (m t ω) * Q t ω / P t ω)
      + β * 𝔼.E t (fun ω' => margUtilC σ χ (C (t + 1) ω') (m (t + 1) ω') / P (t + 1) ω') ω
      = 0 := by
    have := heul ω
    rw [← this]
    ring
  have h := Ex2_1.euler_sufficient_generic 𝔼
    (f := fun δ => periodUtility σ χ (C t ω - Q t ω * δ / P t ω) (m t ω))
    (G := fun δ ω' => periodUtility σ χ (C (t + 1) ω' + δ / P (t + 1) ω') (m (t + 1) ω'))
    (a := -(margUtilC σ χ (C t ω) (m t ω) * Q t ω / P t ω)) hβ ?_ hG t ω hfoc
  · exact h
  · simp only [mul_zero, zero_div, sub_zero]
    have e : margUtilC σ χ (C t ω) (m t ω) * (C t ω - Q t ω * δ / P t ω - C t ω)
        = δ * -(margUtilC σ χ (C t ω) (m t ω) * Q t ω / P t ω) := by ring
    linarith

/-! ### b. The Friedman rule -/

/-- Galí (2015), Exercise 2.4(b): `s(i) = (χ(1 − e^{−i}))^{1/2}`, which equals `χ/(M/(PC))` on
the money-demand schedule. -/
noncomputable def sRate (χ i : ℝ) : ℝ := Real.sqrt (χ * (1 - Real.exp (-i)))

/-- Galí (2015), Exercise 2.4(a)–(b): the money demand `M/(PC) = (χ/(1 − e^{−i}))^{1/2}`. -/
noncomputable def zDemand (χ i : ℝ) : ℝ := Real.sqrt (χ / (1 - Real.exp (-i)))

/-- Galí (2015), Exercise 2.4(b): equilibrium period utility with `C = Y` and real balances on
the money-demand schedule at the nominal rate `i`. -/
noncomputable def eqWelfare (σ χ Y i : ℝ) : ℝ := periodUtility σ χ Y (Y * zDemand χ i)

/-- Galí (2015), Exercise 2.4: `0 < 1 − e^{−i}` for `i > 0`. -/
theorem one_sub_exp_neg_pos {i : ℝ} (hi : 0 < i) : 0 < 1 - Real.exp (-i) := by
  have : Real.exp (-i) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  linarith

/-- Galí (2015), Exercise 2.4(b): `M/(PC) > 0` for `i > 0`. -/
theorem zDemand_pos {χ i : ℝ} (hχ : 0 < χ) (hi : 0 < i) : 0 < zDemand χ i :=
  Real.sqrt_pos.2 (div_pos hχ (one_sub_exp_neg_pos hi))

/-- Galí (2015), Exercise 2.4(b): `s(i) > 0` for `i > 0`. -/
theorem sRate_pos {χ i : ℝ} (hχ : 0 < χ) (hi : 0 < i) : 0 < sRate χ i :=
  Real.sqrt_pos.2 (mul_pos hχ (one_sub_exp_neg_pos hi))

/-- Galí (2015), Exercise 2.4(b): on the money-demand schedule `χ/(M/(PC)) = s(i)`. -/
theorem chi_div_zDemand {χ i : ℝ} (hχ : 0 < χ) (hi : 0 < i) : χ / zDemand χ i = sRate χ i := by
  have h1 := one_sub_exp_neg_pos hi
  have hz := zDemand_pos hχ hi
  refine (pow_left_inj₀ (div_pos hχ hz).le (sRate_pos hχ hi).le two_ne_zero).1 ?_
  rw [div_pow, zDemand, sRate, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  field_simp

/-- Galí (2015), Exercise 2.4(b): equilibrium utility is `u(Y/(1 + s(i)))`. -/
theorem eqWelfare_eq (σ : ℝ) {χ Y i : ℝ} (hχ : 0 < χ) (hY : 0 < Y) (hi : 0 < i) :
    eqWelfare σ χ Y i = Ex2_1.utilC σ (Y / (1 + sRate χ i)) := by
  have hz := zDemand_pos hχ hi
  have hs := sRate_pos hχ hi
  unfold eqWelfare periodUtility
  congr 1
  have hX := inv_aggX hχ.le hY (mul_pos hY hz)
  rw [show χ / (Y * zDemand χ i) = (χ / zDemand χ i) / Y by field_simp, chi_div_zDemand hχ hi]
    at hX
  have hXpos := aggX_pos hχ.le hY (mul_pos hY hz)
  have : aggX χ Y (Y * zDemand χ i) = ((aggX χ Y (Y * zDemand χ i))⁻¹)⁻¹ := (inv_inv _).symm
  rw [this, hX]
  field_simp

/-- Galí (2015), Exercise 2.4(b): `s` is strictly increasing on `[0, ∞)`. -/
theorem sRate_strictMonoOn {χ : ℝ} (hχ : 0 < χ) : StrictMonoOn (sRate χ) (Set.Ici 0) := by
  intro a ha b _ hab
  have ha' : (0 : ℝ) ≤ a := ha
  have h1 : Real.exp (-b) < Real.exp (-a) := Real.exp_lt_exp.2 (by linarith)
  have h2 : 0 ≤ 1 - Real.exp (-a) := by
    have : Real.exp (-a) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    linarith
  exact Real.sqrt_lt_sqrt (mul_nonneg hχ.le h2) (by nlinarith)

/-- Galí (2015), Exercise 2.4(b): `s` is continuous and `s(0) = 0`. -/
theorem sRate_continuous (χ : ℝ) : Continuous (sRate χ) := by
  unfold sRate
  fun_prop

/-- Galí (2015), Exercise 2.4(b) (**the Friedman rule is optimal**): for `χ > 0` and every
endowment realisation `Y > 0`, equilibrium utility is strictly decreasing in the nominal rate
`i > 0`, lies strictly below the satiation level `u(Y)`, and tends to `u(Y)` as `i → 0⁺`;
since `i ≥ 0` (`Q ≤ 1`), welfare is maximised by driving the nominal rate to zero. -/
theorem friedman_rule (σ : ℝ) {χ Y : ℝ} (hχ : 0 < χ) (hY : 0 < Y) :
    StrictAntiOn (eqWelfare σ χ Y) (Set.Ioi 0) ∧
      (∀ i, 0 < i → eqWelfare σ χ Y i < Ex2_1.utilC σ Y) ∧
      Tendsto (eqWelfare σ χ Y) (𝓝[>] 0) (𝓝 (Ex2_1.utilC σ Y)) := by
  have hpos : ∀ i, 0 < i → 0 < Y / (1 + sRate χ i) := fun i hi => by
    have := sRate_pos hχ hi
    positivity
  refine ⟨fun a ha b hb hab => ?_, fun i hi => ?_, ?_⟩
  · rw [eqWelfare_eq σ hχ hY ha, eqWelfare_eq σ hχ hY hb]
    refine Ex2_1.utilC_strictMonoOn σ (hpos b hb) (hpos a ha) ?_
    have hs := sRate_strictMonoOn hχ (Set.mem_Ici.2 (le_of_lt ha))
      (Set.mem_Ici.2 (le_of_lt hb)) hab
    have := sRate_pos hχ ha
    exact div_lt_div_of_pos_left hY (by positivity) (by linarith)
  · rw [eqWelfare_eq σ hχ hY hi]
    refine Ex2_1.utilC_strictMonoOn σ (hpos i hi) hY ?_
    have := sRate_pos hχ hi
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  · have hs0 : sRate χ 0 = 0 := by simp [sRate]
    have hlim : Tendsto (fun i => Y / (1 + sRate χ i)) (𝓝[>] 0) (𝓝 Y) := by
      have h := ((sRate_continuous χ).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      rw [hs0] at h
      have h2 := (tendsto_const_nhds (x := Y)).div (h.const_add 1) (by norm_num)
      rw [add_zero, div_one] at h2
      exact h2
    have hu := ((Ex2_1.hasDerivAt_utilC σ hY).continuousAt.tendsto).comp hlim
    refine hu.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with i hi
    exact (eqWelfare_eq σ hχ hY hi).symm

/-- Galí (2015), Exercise 2.4(b): in a steady state with `i = ρ + π`, equilibrium utility is
strictly decreasing in inflation `π > −ρ`, so the optimum is the Friedman rule `π = −ρ`. -/
theorem friedman_rule_inflation (σ ρ : ℝ) {χ Y : ℝ} (hχ : 0 < χ) (hY : 0 < Y) :
    StrictAntiOn (fun π => eqWelfare σ χ Y (ρ + π)) (Set.Ioi (-ρ)) := by
  intro a ha b hb hab
  have ha' : -ρ < a := ha
  have hb' : -ρ < b := hb
  exact (friedman_rule σ hχ hY).1 (show (0 : ℝ) < ρ + a by linarith)
    (show (0 : ℝ) < ρ + b by linarith) (by linarith)

/-! ### c. The welfare cost of inflation -/

/-- Galí (2015), Exercise 2.4(c): on the money-demand schedule, `1/X(C, m) = 1/C + s(i)` when
real balances are `m = zDemand χ i` (steady state `C = 1`) held fixed while `C` varies. -/
theorem inv_aggX_demand {χ C i : ℝ} (hχ : 0 < χ) (hC : 0 < C) (hi : 0 < i) :
    (aggX χ C (zDemand χ i))⁻¹ = C⁻¹ + sRate χ i := by
  rw [inv_aggX hχ.le hC (zDemand_pos hχ hi), chi_div_zDemand hχ hi]

/-- Galí (2015), Exercise 2.4(c): the welfare cost (consumption raised by `λ`, real balances at
their `π` level): `λ(π) = (s_π − s_0)/(1 + s_0 − s_π)`, `s_π = s(ρ + π)`. -/
noncomputable def welfareCostLevels (χ ρ π : ℝ) : ℝ :=
  (sRate χ (ρ + π) - sRate χ ρ) / (1 + sRate χ ρ - sRate χ (ρ + π))

/-- Galí (2015), Exercise 2.4(c): indifference between steady-state inflation `π` with
consumption `1 + λ` and zero inflation with consumption `1` holds iff
`1/(1 + λ) + s_π = 1 + s_0` (real balances at their own steady-state levels). -/
theorem indifference_levels_iff (σ : ℝ) {χ ρ π l : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ)
    (hπ : -ρ < π) (hl : -1 < l) :
    periodUtility σ χ (1 + l) (zDemand χ (ρ + π)) = periodUtility σ χ 1 (zDemand χ ρ) ↔
      (1 + l)⁻¹ + sRate χ (ρ + π) = 1 + sRate χ ρ := by
  have hi : 0 < ρ + π := by linarith
  have hl1 : 0 < 1 + l := by linarith
  have hA := aggX_pos hχ.le hl1 (zDemand_pos hχ hi)
  have hB := aggX_pos hχ.le one_pos (zDemand_pos hχ hρ)
  unfold periodUtility
  rw [(Ex2_1.utilC_strictMonoOn σ).injOn.eq_iff hA hB, ← inv_inj, inv_aggX_demand hχ hl1 hi,
    inv_aggX_demand hχ one_pos hρ, inv_one]

/-- Galí (2015), Exercise 2.4(c) (**closed form**, levels version): if `s_π < 1 + s_0`, the
compensation `λ(π) = (s_π − s_0)/(1 + s_0 − s_π)` satisfies `1 + λ > 0` and makes the
household indifferent between inflation `π` and zero inflation. -/
theorem welfareCost_levels (σ : ℝ) {χ ρ π : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ) (hπ : -ρ < π)
    (hex : sRate χ (ρ + π) < 1 + sRate χ ρ) :
    -1 < welfareCostLevels χ ρ π ∧
      periodUtility σ χ (1 + welfareCostLevels χ ρ π) (zDemand χ (ρ + π))
        = periodUtility σ χ 1 (zDemand χ ρ) := by
  have hd : 0 < 1 + sRate χ ρ - sRate χ (ρ + π) := by linarith
  have e : 1 + welfareCostLevels χ ρ π = 1 / (1 + sRate χ ρ - sRate χ (ρ + π)) := by
    unfold welfareCostLevels
    field_simp
    ring
  have hl : -1 < welfareCostLevels χ ρ π := by
    have : 0 < 1 + welfareCostLevels χ ρ π := by rw [e]; positivity
    linarith
  refine ⟨hl, (indifference_levels_iff σ hχ hρ hπ hl).2 ?_⟩
  rw [e, one_div, inv_inv]
  ring

/-- Galí (2015), Exercise 2.4(c) (**uniqueness**, levels version): any compensation `λ > −1`
making the household indifferent equals `λ(π)`. -/
theorem welfareCost_levels_unique (σ : ℝ) {χ ρ π l : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ)
    (hπ : -ρ < π) (hl : -1 < l)
    (h : periodUtility σ χ (1 + l) (zDemand χ (ρ + π)) = periodUtility σ χ 1 (zDemand χ ρ)) :
    l = welfareCostLevels χ ρ π := by
  have h' := (indifference_levels_iff σ hχ hρ hπ hl).1 h
  have hl1 : 0 < 1 + l := by linarith
  have hd : 1 + sRate χ ρ - sRate χ (ρ + π) = (1 + l)⁻¹ := by linarith
  have hd0 : 0 < 1 + sRate χ ρ - sRate χ (ρ + π) := by rw [hd]; positivity
  have e1 : l * (1 + l)⁻¹ = 1 - (1 + l)⁻¹ := by
    field_simp
    ring
  have key : sRate χ (ρ + π) - sRate χ ρ = l * (1 + l)⁻¹ := by rw [e1]; linarith
  unfold welfareCostLevels
  rw [key, hd]
  field_simp

/-- Galí (2015), Exercise 2.4(c) (**no compensation**, levels version): if `s_π ≥ 1 + s_0`, no
increase in consumption with real balances held at their `π` level compensates for inflation
`π` (utility in `C` is bounded by the satiation level `1/s_π` of `X`). -/
theorem welfareCost_levels_none (σ : ℝ) {χ ρ π l : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ)
    (hπ : -ρ < π) (hl : -1 < l) (hno : 1 + sRate χ ρ ≤ sRate χ (ρ + π)) :
    periodUtility σ χ (1 + l) (zDemand χ (ρ + π)) ≠ periodUtility σ χ 1 (zDemand χ ρ) := by
  intro h
  have h' := (indifference_levels_iff σ hχ hρ hπ hl).1 h
  have : 0 < (1 + l)⁻¹ := inv_pos.2 (by linarith)
  linarith

/-- Galí (2015), Exercise 2.4(c): the welfare cost when consumption and real balances are
scaled together (velocity held at its `π` level): `λ(π) = (s_π − s_0)/(1 + s_0)`. -/
noncomputable def welfareCostRatio (χ ρ π : ℝ) : ℝ :=
  (sRate χ (ρ + π) - sRate χ ρ) / (1 + sRate χ ρ)

/-- Galí (2015), Exercise 2.4(c) (**closed form**, ratio version):
`U((1 + λ), (1 + λ) z_π) = U(1, z_0)` with `λ = welfareCostRatio`, and `1 + λ > 0`. -/
theorem welfareCost_ratio (σ : ℝ) {χ ρ π : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ) (hπ : -ρ < π) :
    -1 < welfareCostRatio χ ρ π ∧
      periodUtility σ χ (1 + welfareCostRatio χ ρ π)
        ((1 + welfareCostRatio χ ρ π) * zDemand χ (ρ + π))
        = periodUtility σ χ 1 (zDemand χ ρ) := by
  have hi : 0 < ρ + π := by linarith
  have hs0 := sRate_pos hχ hρ
  have hs := sRate_pos hχ hi
  have e : 1 + welfareCostRatio χ ρ π = (1 + sRate χ (ρ + π)) / (1 + sRate χ ρ) := by
    unfold welfareCostRatio
    field_simp
    ring
  have hl1 : 0 < 1 + welfareCostRatio χ ρ π := by rw [e]; positivity
  refine ⟨by linarith, ?_⟩
  unfold periodUtility
  congr 1
  have hz := zDemand_pos hχ hi
  have hA := aggX_pos hχ.le hl1 (mul_pos hl1 hz)
  have hB := aggX_pos hχ.le one_pos (zDemand_pos hχ hρ)
  rw [← inv_inj, inv_aggX hχ.le hl1 (mul_pos hl1 hz), inv_aggX_demand hχ one_pos hρ,
    show χ / ((1 + welfareCostRatio χ ρ π) * zDemand χ (ρ + π))
      = (1 + welfareCostRatio χ ρ π)⁻¹ * (χ / zDemand χ (ρ + π)) by field_simp,
    chi_div_zDemand hχ hi, e]
  field_simp

/-- Galí (2015), Exercise 2.4(c) (**uniqueness**, ratio version). -/
theorem welfareCost_ratio_unique (σ : ℝ) {χ ρ π l : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ)
    (hπ : -ρ < π) (hl : -1 < l)
    (h : periodUtility σ χ (1 + l) ((1 + l) * zDemand χ (ρ + π))
      = periodUtility σ χ 1 (zDemand χ ρ)) : l = welfareCostRatio χ ρ π := by
  have hi : 0 < ρ + π := by linarith
  have hl1 : 0 < 1 + l := by linarith
  have hz := zDemand_pos hχ hi
  have hs0 := sRate_pos hχ hρ
  have hA := aggX_pos hχ.le hl1 (mul_pos hl1 hz)
  have hB := aggX_pos hχ.le one_pos (zDemand_pos hχ hρ)
  unfold periodUtility at h
  rw [(Ex2_1.utilC_strictMonoOn σ).injOn.eq_iff hA hB, ← inv_inj,
    inv_aggX hχ.le hl1 (mul_pos hl1 hz), inv_aggX_demand hχ one_pos hρ,
    show χ / ((1 + l) * zDemand χ (ρ + π)) = (1 + l)⁻¹ * (χ / zDemand χ (ρ + π)) by
      field_simp, chi_div_zDemand hχ hi] at h
  unfold welfareCostRatio
  rw [eq_div_iff (by positivity)]
  field_simp at h
  linarith

/-- Galí (2015), Exercise 2.4(c): the (ratio-version) welfare cost is positive iff `π > 0`. -/
theorem welfareCost_ratio_pos_iff {χ ρ π : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ) (hπ : -ρ < π) :
    0 < welfareCostRatio χ ρ π ↔ 0 < π := by
  have hs0 := sRate_pos hχ hρ
  have hmono := sRate_strictMonoOn hχ
  unfold welfareCostRatio
  rw [div_pos_iff_of_pos_right (by positivity), sub_pos]
  constructor
  · intro h
    by_contra h'
    push Not at h'
    have : sRate χ (ρ + π) ≤ sRate χ ρ :=
      hmono.monotoneOn (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 hρ.le) (by linarith)
    linarith
  · intro h
    exact hmono (Set.mem_Ici.2 hρ.le) (Set.mem_Ici.2 (by linarith)) (by linarith)

/-- Galí (2015), Exercise 2.4(c): when it exists, the (levels-version) welfare cost is
positive iff `π > 0`. -/
theorem welfareCost_levels_pos_iff {χ ρ π : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ) (hπ : -ρ < π)
    (hex : sRate χ (ρ + π) < 1 + sRate χ ρ) : 0 < welfareCostLevels χ ρ π ↔ 0 < π := by
  have hmono := sRate_strictMonoOn hχ
  unfold welfareCostLevels
  rw [div_pos_iff_of_pos_right (by linarith), sub_pos]
  constructor
  · intro h
    by_contra h'
    push Not at h'
    have : sRate χ (ρ + π) ≤ sRate χ ρ :=
      hmono.monotoneOn (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 hρ.le) (by linarith)
    linarith
  · intro h
    exact hmono (Set.mem_Ici.2 hρ.le) (Set.mem_Ici.2 (by linarith)) (by linarith)

/-! ### d. Interest-rate fluctuations to second order -/

/-- Galí (2015), Exercise 2.4(d): equilibrium utility as a function of the nominal rate,
`W(i) = u(1/(1 + s(i)))` (steady-state endowment `Y = 1`). -/
noncomputable def Wf (σ χ i : ℝ) : ℝ := Ex2_1.utilC σ (1 + sRate χ i)⁻¹

/-- Galí (2015), Exercise 2.4(d): `W` is equilibrium utility `eqWelfare` at `Y = 1`. -/
theorem eqWelfare_one_eq_Wf (σ : ℝ) {χ i : ℝ} (hχ : 0 < χ) (hi : 0 < i) :
    eqWelfare σ χ 1 i = Wf σ χ i := by
  rw [eqWelfare_eq σ hχ one_pos hi, one_div]
  rfl

/-- Galí (2015), Exercise 2.4(d): `s'(i) = χ e^{−i}/(2 s(i))`. -/
noncomputable def sDeriv (χ i : ℝ) : ℝ := χ * Real.exp (-i) / (2 * sRate χ i)

/-- Galí (2015), Exercise 2.4(d): `s''(i) = −s'(i) − s'(i)²/s(i)`. -/
noncomputable def sDeriv2 (χ i : ℝ) : ℝ := -sDeriv χ i - sDeriv χ i ^ 2 / sRate χ i

/-- Galí (2015), Exercise 2.4(d): `W'(i) = −(1 + s)^{σ−2} s'`. -/
noncomputable def W1 (σ χ i : ℝ) : ℝ := -((1 + sRate χ i) ^ (σ - 2) * sDeriv χ i)

/-- Galí (2015), Exercise 2.4(d):
`W''(i) = (2 − σ)(1 + s)^{σ−3} s'² + (1 + s)^{σ−2}(s' + s'²/s)`. -/
noncomputable def W2 (σ χ i : ℝ) : ℝ :=
  (2 - σ) * (1 + sRate χ i) ^ (σ - 3) * sDeriv χ i ^ 2
    + (1 + sRate χ i) ^ (σ - 2) * (sDeriv χ i + sDeriv χ i ^ 2 / sRate χ i)

/-- Galí (2015), Exercise 2.4(d) (**exact derivative**): `s` has derivative `s'` at `i > 0`. -/
theorem hasDerivAt_sRate {χ i : ℝ} (hχ : 0 < χ) (hi : 0 < i) :
    HasDerivAt (sRate χ) (sDeriv χ i) i := by
  have h1 := one_sub_exp_neg_pos hi
  have hexp : HasDerivAt (fun i => Real.exp (-i)) (-Real.exp (-i)) i := by
    have := (hasDerivAt_neg i).exp
    convert this using 1
    ring
  have hg := (hexp.const_sub 1).const_mul χ
  have hs := (Real.hasDerivAt_sqrt (mul_pos hχ h1).ne').comp i hg
  refine hs.congr_deriv ?_
  unfold sDeriv sRate
  have : 0 < Real.sqrt (χ * (1 - Real.exp (-i))) := Real.sqrt_pos.2 (mul_pos hχ h1)
  field_simp

/-- Galí (2015), Exercise 2.4(d) (**exact derivative**): `s'` has derivative `s''` at `i > 0`. -/
theorem hasDerivAt_sDeriv {χ i : ℝ} (hχ : 0 < χ) (hi : 0 < i) :
    HasDerivAt (sDeriv χ) (sDeriv2 χ i) i := by
  have hs := sRate_pos hχ hi
  have hexp : HasDerivAt (fun i => Real.exp (-i)) (-Real.exp (-i)) i := by
    have := (hasDerivAt_neg i).exp
    convert this using 1
    ring
  have h := (hexp.const_mul χ).div ((hasDerivAt_sRate hχ hi).const_mul 2)
    (by positivity : (2 * sRate χ i) ≠ 0)
  refine h.congr_deriv ?_
  unfold sDeriv2 sDeriv
  field_simp

/-- Galí (2015), Exercise 2.4(d) (**exact derivative**): `W' = W1` at `i > 0`. -/
theorem hasDerivAt_W (σ : ℝ) {χ i : ℝ} (hχ : 0 < χ) (hi : 0 < i) :
    HasDerivAt (Wf σ χ) (W1 σ χ i) i := by
  have hs := sRate_pos hχ hi
  have h1 : 0 < 1 + sRate χ i := by linarith
  have hinv := ((hasDerivAt_sRate hχ hi).const_add 1).inv h1.ne'
  have hu := (Ex2_1.hasDerivAt_utilC σ (inv_pos.2 h1)).comp i hinv
  refine hu.congr_deriv ?_
  unfold W1
  rw [Real.inv_rpow h1.le, Real.rpow_neg h1.le, inv_inv, Real.rpow_sub h1, Real.rpow_two]
  field_simp

/-- Galí (2015), Exercise 2.4(d) (**exact derivative**): `W1' = W2` at `i > 0`. -/
theorem hasDerivAt_W1 (σ : ℝ) {χ i : ℝ} (hχ : 0 < χ) (hi : 0 < i) :
    HasDerivAt (W1 σ χ) (W2 σ χ i) i := by
  have hs := sRate_pos hχ hi
  have h1 : 0 < 1 + sRate χ i := by linarith
  have hA := (Real.hasDerivAt_rpow_const (p := σ - 2) (Or.inl h1.ne')).comp i
    ((hasDerivAt_sRate hχ hi).const_add 1)
  have h := (hA.mul (hasDerivAt_sDeriv hχ hi)).neg
  refine h.congr_deriv ?_
  unfold W2 sDeriv2
  rw [show σ - 2 - 1 = σ - 3 by ring]
  simp only [Function.comp_apply]
  ring

/-- Galí (2015), Exercise 2.4(d): `W` is three times continuously differentiable on
`(0, ∞)`. -/
theorem contDiffOn_W (σ : ℝ) {χ : ℝ} (hχ : 0 < χ) :
    ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) (Wf σ χ) (Set.Ioi 0) := by
  intro x hx
  have hx' : (0 : ℝ) < x := hx
  have h1 := one_sub_exp_neg_pos hx'
  have hs := sRate_pos hχ hx'
  have hin : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (fun i => (1 + sRate χ i)⁻¹) x := by
    have hg : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) (fun i : ℝ => χ * (1 - Real.exp (-i))) := by
      fun_prop
    have hsq : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (sRate χ) x :=
      hg.contDiffAt.sqrt (mul_pos hχ h1).ne'
    exact (contDiffAt_const.add hsq).inv (by linarith)
  have hy : 0 < (1 + sRate χ x)⁻¹ := inv_pos.2 (by linarith)
  have hout : ContDiffAt ℝ ((3 : ℕ) : WithTop ℕ∞) (Ex2_1.utilC σ) (1 + sRate χ x)⁻¹ := by
    by_cases hσ : σ = 1
    · have hfun : Ex2_1.utilC σ = Real.log := funext fun y => by simp [Ex2_1.utilC, hσ]
      rw [hfun]
      exact Real.contDiffAt_log.2 hy.ne'
    · have hfun : Ex2_1.utilC σ = fun y => (y ^ (1 - σ) - 1) / (1 - σ) :=
        funext fun y => by simp [Ex2_1.utilC, hσ]
      rw [hfun]
      exact ((Real.contDiffAt_rpow_const_of_ne hy.ne').sub contDiffAt_const).div_const _
  exact (hout.comp x hin).contDiffWithinAt

/-- Galí (2015), Exercise 2.4(d): `W'' = W2` at `i > 0`. -/
theorem deriv_deriv_W (σ : ℝ) {χ i : ℝ} (hχ : 0 < χ) (hi : 0 < i) :
    deriv (deriv (Wf σ χ)) i = W2 σ χ i := by
  have heq : deriv (Wf σ χ) =ᶠ[𝓝 i] W1 σ χ := by
    filter_upwards [Ioi_mem_nhds hi] with x hx
    exact (hasDerivAt_W σ hχ hx).deriv
  rw [heq.deriv_eq, (hasDerivAt_W1 σ hχ hi).deriv]

/-- Galí (2015), Exercise 2.4(d) (**second-order Taylor expansion**): for `ī > 0`,
`W(i) = W(ī) + W1(ī)(i − ī) + ½ W2(ī)(i − ī)² + O((i − ī)³)`. -/
theorem welfare_taylor (σ : ℝ) {χ ibar : ℝ} (hχ : 0 < χ) (hi : 0 < ibar) :
    (fun i => Wf σ χ i - Wf σ χ ibar - W1 σ χ ibar * (i - ibar)
      - 1 / 2 * W2 σ χ ibar * (i - ibar) ^ 2) =O[𝓝 ibar] fun i => (i - ibar) ^ 3 := by
  have ht := taylor_isLittleO (convex_Ioi 0) hi (contDiffOn_W σ hχ)
  rw [nhdsWithin_eq_nhds.2 (Ioi_mem_nhds hi)] at ht
  set c3 := iteratedDerivWithin 3 (Wf σ χ) (Set.Ioi 0) ibar with hc3
  have d1 : iteratedDerivWithin 1 (Wf σ χ) (Set.Ioi 0) ibar = W1 σ χ ibar := by
    rw [iteratedDerivWithin_of_isOpen isOpen_Ioi hi, iteratedDeriv_one,
      (hasDerivAt_W σ hχ hi).deriv]
  have d2 : iteratedDerivWithin 2 (Wf σ χ) (Set.Ioi 0) ibar = W2 σ χ ibar := by
    rw [iteratedDerivWithin_of_isOpen isOpen_Ioi hi, iteratedDeriv_succ, iteratedDeriv_one,
      deriv_deriv_W σ hχ hi]
  have hT : ∀ i, taylorWithinEval (Wf σ χ) 3 (Set.Ioi 0) ibar i
      = Wf σ χ ibar + W1 σ χ ibar * (i - ibar) + 1 / 2 * W2 σ χ ibar * (i - ibar) ^ 2
        + c3 / 6 * (i - ibar) ^ 3 := by
    intro i
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDerivWithin_zero, d1, d2,
      ← hc3, Nat.factorial, smul_eq_mul]
    push_cast
    ring
  have hfun : (fun i => Wf σ χ i - Wf σ χ ibar - W1 σ χ ibar * (i - ibar)
      - 1 / 2 * W2 σ χ ibar * (i - ibar) ^ 2)
      = (fun i => Wf σ χ i - taylorWithinEval (Wf σ χ) 3 (Set.Ioi 0) ibar i)
        + fun i => c3 / 6 * (i - ibar) ^ 3 := by
    funext i
    simp only [Pi.add_apply, hT]
    ring
  rw [hfun]
  exact ht.isBigO.add (Asymptotics.isBigO_const_mul_self _ _ _)

/-- Galí (2015), Exercise 2.4(d) (**second-order welfare effect of interest-rate
fluctuations**): let `i_t = ī + s ε_t` with `ī > 0`, `|ε_t| ≤ M`, `E_0 ε_t = 0`, and
`0 ≤ β < 1`. Relative to the constant policy `i_t = ī`, expected discounted utility changes by
`½ W2(ī) s² ∑ βᵗ E_0 ε_t²` up to an `O(|s|³)` remainder:
there are `K` and `r > 0` with
`|∑ βᵗ E_0 W(i_t) − ∑ βᵗ W(ī) − ½ W2(ī) s² ∑ βᵗ E_0 ε_t²| ≤ K |s|³` for `|s| < r`. -/
theorem welfare_fluctuations (σ : ℝ) {χ ibar β M : ℝ}
    (hχ : 0 < χ) (hi : 0 < ibar) (hβ0 : 0 ≤ β) (hβ1 : β < 1) {ε : ℕ → Ω → ℝ}
    (hε : ∀ t ω, |ε t ω| ≤ M) (hE : ∀ t, 𝔼.E 0 (ε t) = 0) (ω : Ω) :
    ∃ K r : ℝ, 0 < r ∧ ∀ s : ℝ, |s| < r →
      |∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => Wf σ χ (ibar + s * ε t ω')) ω
        - ∑' t : ℕ, β ^ t * Wf σ χ ibar
        - 1 / 2 * W2 σ χ ibar * s ^ 2 * ∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => ε t ω' ^ 2) ω|
        ≤ K * |s| ^ 3 := by
  obtain ⟨c, hc⟩ := (welfare_taylor σ hχ hi).bound
  obtain ⟨η, hη, hηb⟩ := Metric.eventually_nhds_iff.1 hc
  have hM : 0 ≤ M := by
    have := hε 0 ω
    exact (abs_nonneg _).trans this
  have hM1 : 0 < M + 1 := by linarith
  set R : ℝ → ℝ := fun i => Wf σ χ i - Wf σ χ ibar - W1 σ χ ibar * (i - ibar)
    - 1 / 2 * W2 σ χ ibar * (i - ibar) ^ 2 with hR
  refine ⟨|c| * M ^ 3 / (1 - β), η / (M + 1), div_pos hη hM1, fun s hs => ?_⟩
  have hsM : ∀ e : ℝ, |e| ≤ M → |s * e| < η := by
    intro e he
    rw [abs_mul]
    have : |s| * |e| ≤ |s| * (M + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg s)
    have := (lt_div_iff₀ hM1).1 hs
    linarith
  have hRb : ∀ t ω', |R (ibar + s * ε t ω')| ≤ |c| * M ^ 3 * |s| ^ 3 := by
    intro t ω'
    have hd : dist (ibar + s * ε t ω') ibar < η := by
      rw [Real.dist_eq, add_sub_cancel_left]
      exact hsM _ (hε t ω')
    have h0 := hηb hd
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h0
    have h : |R (ibar + s * ε t ω')| ≤ c * |(ibar + s * ε t ω' - ibar) ^ 3| := h0
    rw [add_sub_cancel_left, abs_pow, abs_mul] at h
    calc |R (ibar + s * ε t ω')| ≤ c * (|s| * |ε t ω'|) ^ 3 := h
      _ ≤ |c| * (|s| * |ε t ω'|) ^ 3 := by gcongr; exact le_abs_self c
      _ ≤ |c| * (|s| * M) ^ 3 := by gcongr; exact hε t ω'
      _ = |c| * M ^ 3 * |s| ^ 3 := by ring
  -- one period
  have hper : ∀ t, 𝔼.E 0 (fun ω' => Wf σ χ (ibar + s * ε t ω')) ω
      = Wf σ χ ibar + 1 / 2 * W2 σ χ ibar * s ^ 2 * 𝔼.E 0 (fun ω' => ε t ω' ^ 2) ω
        + 𝔼.E 0 (fun ω' => R (ibar + s * ε t ω')) ω := by
    intro t
    have hfun : (fun ω' => Wf σ χ (ibar + s * ε t ω'))
        = (fun _ => Wf σ χ ibar) + (W1 σ χ ibar * s) • ε t
          + (1 / 2 * W2 σ χ ibar * s ^ 2) • (fun ω' => ε t ω' ^ 2)
          + fun ω' => R (ibar + s * ε t ω') := by
      funext ω'
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hR]
      ring
    rw [hfun, map_add, map_add, map_add, map_smul, map_smul, 𝔼.const, hE t]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero, add_zero]
  have hgeo := summable_geometric_of_lt_one hβ0 hβ1
  have hsum2 : Summable fun t : ℕ => β ^ t * 𝔼.E 0 (fun ω' => ε t ω' ^ 2) ω := by
    refine Summable.of_norm_bounded (hgeo.mul_right (M ^ 2)) (fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
    refine mul_le_mul_of_nonneg_left (𝔼.abs_E_le (fun ω' => ?_) 0 ω) (pow_nonneg hβ0 t)
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hε t ω') 2
  have hsumR : Summable fun t : ℕ => β ^ t * 𝔼.E 0 (fun ω' => R (ibar + s * ε t ω')) ω := by
    refine Summable.of_norm_bounded (hgeo.mul_right (|c| * M ^ 3 * |s| ^ 3)) (fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hRb t) 0 ω) (pow_nonneg hβ0 t)
  have hsum0 : Summable fun t : ℕ => β ^ t * Wf σ χ ibar := hgeo.mul_right _
  have htot : ∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => Wf σ χ (ibar + s * ε t ω')) ω
      = ∑' t : ℕ, β ^ t * Wf σ χ ibar
        + 1 / 2 * W2 σ χ ibar * s ^ 2 * ∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => ε t ω' ^ 2) ω
        + ∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => R (ibar + s * ε t ω')) ω := by
    calc ∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => Wf σ χ (ibar + s * ε t ω')) ω
        = ∑' t : ℕ, ((β ^ t * Wf σ χ ibar
            + 1 / 2 * W2 σ χ ibar * s ^ 2 * (β ^ t * 𝔼.E 0 (fun ω' => ε t ω' ^ 2) ω))
            + β ^ t * 𝔼.E 0 (fun ω' => R (ibar + s * ε t ω')) ω) :=
          tsum_congr fun t => by rw [hper t]; ring
      _ = _ := by
          rw [(hsum0.add (hsum2.mul_left _)).tsum_add hsumR,
            hsum0.tsum_add (hsum2.mul_left _), tsum_mul_left]
  rw [htot]
  have hbound : |∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => R (ibar + s * ε t ω')) ω|
      ≤ |c| * M ^ 3 / (1 - β) * |s| ^ 3 := by
    have hs' : HasSum (fun t : ℕ => β ^ t * (|c| * M ^ 3 * |s| ^ 3))
        ((1 - β)⁻¹ * (|c| * M ^ 3 * |s| ^ 3)) :=
      (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right _
    have := tsum_of_norm_bounded
      (f := fun t : ℕ => β ^ t * 𝔼.E 0 (fun ω' => R (ibar + s * ε t ω')) ω) hs' (fun t => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hRb t) 0 ω) (pow_nonneg hβ0 t))
    rw [Real.norm_eq_abs] at this
    calc _ ≤ (1 - β)⁻¹ * (|c| * M ^ 3 * |s| ^ 3) := this
      _ = |c| * M ^ 3 / (1 - β) * |s| ^ 3 := by field_simp
  have e : ∑' t : ℕ, β ^ t * Wf σ χ ibar
      + 1 / 2 * W2 σ χ ibar * s ^ 2 * ∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => ε t ω' ^ 2) ω
      + ∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => R (ibar + s * ε t ω')) ω
      - ∑' t : ℕ, β ^ t * Wf σ χ ibar
      - 1 / 2 * W2 σ χ ibar * s ^ 2 * ∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => ε t ω' ^ 2) ω
      = ∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => R (ibar + s * ε t ω')) ω := by ring
  rw [e]
  exact hbound

/-- Galí (2015), Exercise 2.4(d): the sign of `W''`: `W2(i) > 0` iff
`1 + s'/s + (2 − σ) s'/(1 + s) > 0` (all evaluated at `i > 0`). -/
theorem W2_pos_iff (σ : ℝ) {χ i : ℝ} (hχ : 0 < χ) (hi : 0 < i) :
    0 < W2 σ χ i ↔
      0 < 1 + sDeriv χ i / sRate χ i + (2 - σ) * sDeriv χ i / (1 + sRate χ i) := by
  have hs := sRate_pos hχ hi
  have h1 : 0 < 1 + sRate χ i := by linarith
  have hd : 0 < sDeriv χ i := by unfold sDeriv; positivity
  have e : W2 σ χ i = sDeriv χ i * (1 + sRate χ i) ^ (σ - 2)
      * (1 + sDeriv χ i / sRate χ i + (2 - σ) * sDeriv χ i / (1 + sRate χ i)) := by
    unfold W2
    rw [show σ - 3 = (σ - 2) - 1 by ring, Real.rpow_sub_one h1.ne']
    field_simp
    ring
  have hp : 0 < sDeriv χ i * (1 + sRate χ i) ^ (σ - 2) :=
    mul_pos hd (Real.rpow_pos_of_pos h1 _)
  rw [e]
  exact ⟨fun h => pos_of_mul_pos_right h hp.le, fun h => mul_pos hp h⟩

/-- Galí (2015), Exercise 2.4(d) (**finding**): for `σ ≤ 2` (including log utility) `W'' > 0`
at every `i > 0`: utility is convex in the nominal rate. -/
theorem W2_pos_of_le_two {σ : ℝ} (hσ : σ ≤ 2) {χ i : ℝ} (hχ : 0 < χ) (hi : 0 < i) :
    0 < W2 σ χ i := by
  have hs := sRate_pos hχ hi
  have h1 : 0 < 1 + sRate χ i := by linarith
  have hd : 0 < sDeriv χ i := by unfold sDeriv; positivity
  unfold W2
  have : 0 ≤ (2 - σ) * (1 + sRate χ i) ^ (σ - 3) * sDeriv χ i ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith) (Real.rpow_pos_of_pos h1 _).le) (sq_nonneg _)
  have : 0 < (1 + sRate χ i) ^ (σ - 2) * (sDeriv χ i + sDeriv χ i ^ 2 / sRate χ i) :=
    mul_pos (Real.rpow_pos_of_pos h1 _) (by positivity)
  linarith

/-- Galí (2015), Exercise 2.4(d) (**finding: fluctuations raise welfare for `σ ≤ 2`**): if
`σ ≤ 2` and the fluctuations have positive discounted variance
`V = ∑ βᵗ E_0 ε_t² > 0`, then for all small `s ≠ 0` expected discounted utility under
`i_t = ī + s ε_t` strictly exceeds that of the constant policy `i_t = ī`. -/
theorem fluctuations_raise_welfare {σ : ℝ} (hσ : σ ≤ 2)
    {χ ibar β M : ℝ} (hχ : 0 < χ) (hi : 0 < ibar) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {ε : ℕ → Ω → ℝ} (hε : ∀ t ω, |ε t ω| ≤ M) (hE : ∀ t, 𝔼.E 0 (ε t) = 0) (ω : Ω)
    (hV : 0 < ∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => ε t ω' ^ 2) ω) :
    ∃ r : ℝ, 0 < r ∧ ∀ s : ℝ, s ≠ 0 → |s| < r →
      ∑' t : ℕ, β ^ t * Wf σ χ ibar
        < ∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => Wf σ χ (ibar + s * ε t ω')) ω := by
  obtain ⟨K, r, hr, hK⟩ := welfare_fluctuations 𝔼 σ hχ hi hβ0 hβ1 hε hE ω
  set V := ∑' t : ℕ, β ^ t * 𝔼.E 0 (fun ω' => ε t ω' ^ 2) ω with hVdef
  have hW := W2_pos_of_le_two hσ hχ hi
  set a := 1 / 2 * W2 σ χ ibar * V with ha
  have ha0 : 0 < a := by positivity
  refine ⟨min r (a / (|K| + 1)), lt_min hr (by positivity), fun s hs0 hs => ?_⟩
  have hsr : |s| < r := hs.trans_le (min_le_left _ _)
  have hsa : |s| < a / (|K| + 1) := hs.trans_le (min_le_right _ _)
  have h := hK s hsr
  have hspos : 0 < |s| := abs_pos.2 hs0
  have hK1 : 0 < |K| + 1 := by positivity
  have hsq : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
  have hcube : K * |s| ^ 3 < a * s ^ 2 := by
    rw [hsq]
    have h1 : |s| * (|K| + 1) < a := (lt_div_iff₀ hK1).1 hsa
    have h2 : K * |s| ^ 3 ≤ |K| * |s| ^ 3 :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    have h3 : |K| * |s| ^ 3 < a * |s| ^ 2 := by
      have : |K| * |s| < a := by nlinarith
      have hs2 : 0 < |s| ^ 2 := by positivity
      calc |K| * |s| ^ 3 = (|K| * |s|) * |s| ^ 2 := by ring
        _ < a * |s| ^ 2 := mul_lt_mul_of_pos_right this hs2
    linarith
  have e : 1 / 2 * W2 σ χ ibar * s ^ 2 * V = a * s ^ 2 := by rw [ha]; ring
  rw [e] at h
  have := (abs_le.1 h).1
  linarith

end Gali.ClassicalMonetaryModel.Ex2_4
