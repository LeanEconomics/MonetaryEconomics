/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PolicyResponseDynamics.Expectations
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.Exponential

/-!
# Differentiating under the conditional expectation

Woodford (2003), *Interest and Prices*, §A.3, p. 634 and Chapter 5, pp. 325, 333, 355–357: the
exact-derivative tools that turn the nonlinear first-order conditions of Chapter 5 into their
log-linear forms (the bond-pricing relation (1.5)–(1.6), the habit Euler equation (1.24), the
investment first-order condition (3.3) and the interest-rate relation (3.10)). Restated from the
Woodford Chapter 2 project (`LogLinear`) and the Chapter 3/4 projects; they are shared by the
modules `Predetermined`, `Habit` and `InvestmentModel`.

## Main results

* `hasDerivAt_E`: on a finite state space `E_t` commutes with differentiation.
* `hasDerivAt_E_of_remainder`: on any state space, if the second-order remainder is bounded
  uniformly in the state, `z ↦ E_t[g z]` has derivative `E_t[g']`.
* `hasDerivAt_E_exp`: for bounded `X`, `ε ↦ E_t[exp(ε X)]` has derivative `E_t X` at `0`.
-/

namespace Woodford.PolicyResponseDynamics.ExpectationCalculus

open Filter Topology Asymptotics

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), §A.3, p. 634 (finite state space; restated from the Woodford Chapter 2
project, `LogLinear.hasDerivAt_E`): on a finite state space `E_t` commutes with
differentiation. -/
theorem hasDerivAt_E [Finite Ω] {f : ℝ → Ω → ℝ} {g : Ω → ℝ} {x : ℝ}
    (hf : ∀ ω, HasDerivAt (fun ε => f ε ω) (g ω) x) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => 𝔼.E t (f ε) ω) (𝔼.E t g ω) x := by
  have := Fintype.ofFinite Ω
  have hF : HasDerivAt f g x := hasDerivAt_pi.mpr hf
  have hL := (LinearMap.toContinuousLinearMap (𝔼.E t)).hasFDerivAt.comp_hasDerivAt x hF
  have := hasDerivAt_pi.mp hL ω
  simpa using this


/-- Woodford (2003), §1.2, p. 243 (differentiating under `E_t`; restated from the Chapter 3
project): if the second-order remainder of `z ↦ g z` at `x` is bounded by `C h²` uniformly in the
state, then `z ↦ E_t[g z]` has derivative `E_t[g']` at `x`. -/
theorem hasDerivAt_E_of_remainder {g : ℝ → Ω → ℝ} {g' : Ω → ℝ} {x C δ : ℝ} (hδ : 0 < δ)
    (hrem : ∀ h, |h| < δ → ∀ ω, |g (x + h) ω - g x ω - h * g' ω| ≤ C * h ^ 2)
    (t : ℕ) (ω : Ω) :
    HasDerivAt (fun z => 𝔼.E t (g z) ω) (𝔼.E t g' ω) x := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun h => 𝔼.E t (g (x + h)) ω - 𝔼.E t (g x) ω - h • 𝔼.E t g' ω)
      =O[𝓝 0] fun h : ℝ => h ^ 2 := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
    have hh' : |h| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hh
    have key : 𝔼.E t (g (x + h)) ω - 𝔼.E t (g x) ω - h • 𝔼.E t g' ω
        = 𝔼.E t (g (x + h) - g x - h • g') ω := by
      simp [map_sub, map_smul]
    rw [key, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, sq_abs]
    exact 𝔼.abs_E_le (fun ω' => by simpa [smul_eq_mul] using hrem h hh' ω') t ω
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two)


/-- Woodford (2003), p. 325 (and §A.3 of the Chapter 2 project, `hasDerivAt_E_exp`, restated):
for a bounded random variable `X`, `ε ↦ E_t[exp(ε X)]` has derivative `E_t X` at `0`. -/
theorem hasDerivAt_E_exp {K : ℝ} {X : Ω → ℝ} (hX : ∀ ω, |X ω| ≤ K) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => 𝔼.E t (fun ω' => Real.exp (ε * X ω')) ω) (𝔼.E t X ω) 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hK : 0 ≤ |K| := abs_nonneg K
  have hbig : (fun h : ℝ => 𝔼.E t (fun ω' => Real.exp ((0 + h) * X ω')) ω -
      𝔼.E t (fun ω' => Real.exp (0 * X ω')) ω - h • 𝔼.E t X ω) =O[𝓝 0] fun h => h ^ 2 := by
    refine IsBigO.of_bound (|K| ^ 2) ?_
    have hball : Metric.ball (0 : ℝ) (1 / (|K| + 1)) ∈ 𝓝 (0 : ℝ) :=
      Metric.ball_mem_nhds 0 (by positivity)
    filter_upwards [hball] with h hh
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
    have hrem : ∀ ω', |Real.exp (h * X ω') - 1 - h * X ω'| ≤ |K| ^ 2 * h ^ 2 := by
      intro ω'
      have hx : |h * X ω'| ≤ 1 := by
        rw [abs_mul]
        have h1 : |X ω'| ≤ |K| := (hX ω').trans (le_abs_self K)
        have h2 : |h| * (|K| + 1) ≤ 1 := by
          rw [lt_div_iff₀ (by positivity)] at hh
          exact hh.le
        nlinarith [abs_nonneg h, abs_nonneg (X ω')]
      refine (Real.abs_exp_sub_one_sub_id_le hx).trans ?_
      rw [mul_pow, mul_comm (|K| ^ 2)]
      have : X ω' ^ 2 ≤ |K| ^ 2 := by
        rw [← sq_abs (X ω')]
        exact pow_le_pow_left₀ (abs_nonneg _) ((hX ω').trans (le_abs_self K)) 2
      exact mul_le_mul_of_nonneg_left this (sq_nonneg h)
    have heq : 𝔼.E t (fun ω' => Real.exp ((0 + h) * X ω')) ω -
        𝔼.E t (fun ω' => Real.exp (0 * X ω')) ω - h • 𝔼.E t X ω =
        𝔼.E t (fun ω' => Real.exp (h * X ω') - 1 - h * X ω') ω := by
      have hfun : (fun ω' => Real.exp (h * X ω') - 1 - h * X ω') =
          (fun ω' => Real.exp (h * X ω')) - (fun _ => (1 : ℝ)) - h • X := by
        funext ω'
        simp
      rw [hfun, map_sub, map_sub, map_smul, 𝔼.const]
      simp [𝔼.const]
    rw [heq, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h)]
    exact 𝔼.abs_E_le hrem t ω
  exact hbig.trans_isLittleO (isLittleO_pow_id (by norm_num))

end Woodford.PolicyResponseDynamics.ExpectationCalculus
