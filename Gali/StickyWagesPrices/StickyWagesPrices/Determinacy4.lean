/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyWagesPrices.Expectations
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# The determinacy theorem of Galí (2015), p. 174

Galí (2015), Chapter 6, Section 6.2, pp. 172–175. Under the interest rate rule (23) the
sticky-wage-and-price economy is the system (24),

  `A₀ʷ x_t = A₁ʷ E_t x_{t+1} + B₀ʷ u_t`,  `x_t = (ỹ_t, π^p_t, π^w_t, ω̃_{t−1})`,

with three non-predetermined variables and one predetermined variable (the lagged real wage
gap). The book states without proof (fn. 2, citing Flaschel–Franke–Proaño 2008 and
Blasselle–Poissonnier 2013) that, for nonnegative rule coefficients, the equilibrium is
determinate if and only if

  `φ_p + φ_w + φ_y (1 − β)/Θ_y (1/λ_p + 1/λ_w) > 1`,  `Θ_y = σ + (α + φ)/(1 − α)`,

equivalently three eigenvalues of `(A₀ʷ)⁻¹ A₁ʷ` lie inside and one outside the unit circle.
This module proves both statements in full.

## Method

* `q(z) = −det(A₀ʷ − z A₁ʷ)` is an explicit quartic with `q(1) = λ_p λ_w Θ_y (LHS − 1)`.
* **No root on the unit circle when `q(1) > 0`** (`Par.qC_ne_zero_of_norm_eq_one`): writing
  `z = x + i y`, `Re(q(z) · i z̄ ē)` with `e = (1 − βz)(1 − z̄)` equals
  `(1 − β) y q(1)` plus a sum of nonnegative terms (`circle_cert`, an exact polynomial identity
  modulo `x² + y² = 1`).
* **Counting by the argument principle** (`argument_principle`, `inCount_path`): along a path
  of quartics without roots on the circle the number of roots in the unit disc is constant.
  A two-stage homotopy (policy coefficients, then structural parameters) inside the region
  `q(1) > 0` connects any parameter vector to a reference vector whose quartic factors with
  roots `1/2, 1/3, 4, 1/8` (`Par.inCount_QC`).
* **Blanchard–Kahn with one predetermined variable**: the unique stable root `μ ∈ (0, 1)` of
  `q` and its eigenvector `(g, 1)` quasi-difference the system into a forward system
  `s_t = K E_t s_{t+1} + F u_t` whose matrix `K` has all eigenvalues in the open unit disc
  (`Par.Km_eigen`, via `det(C − z D) = −q(z)/(z − μ)`); Gelfand's formula gives geometric decay
  of `Kᵏ` (`pow_entry_bound`), whence existence and uniqueness (`Fwd.fsolves_exists`,
  `Fwd.fsolves_unique`, `Dyn.determinate_of_pos`).
* **Failure when the condition fails**: at `q(1) = 0` a unit root makes a constant forcing
  produce no bounded solution (`Dyn.not_determinate_of_eq`); when `q(1) < 0` the number of
  roots of `q` in the closed disc is never one (`Dyn.closedRoots_card_ne_one`); with none, no
  bounded solution exists for `ω̃_{−1} = 1` (`Dyn.not_determinate_of_no_root`); with two or
  more, an explicit nonzero bounded solution with `ω̃_{−1} = 0` exists (complex pair, two real
  roots, or a Jordan chain for a double root).

## Main results

* `determinacy_iff`: the p. 174 theorem, in the book's parameters.
* `eigenvalues_iff`: the eigenvalue form (three inside, one outside, with multiplicity).
* `determinacy_iff_phiY_zero`: with `φ_y = 0` the condition is `φ_p + φ_w > 1`.
* `exNE_no_bounded_solution`, `exBase_multiplicity`: both failure modes occur.

## Remark on the book (Lean-checked)

Figure 6.1 labels the region where the condition fails "Indeterminacy". At the book's baseline
calibration that is what happens (`exBase_multiplicity`: two stable roots, two bounded
solutions), but not in general: at the admissible point `exNE` (`β = 9/10, σ = 3/4, α = 3/4,
φ = 3, λ_p = 1/40, λ_w = 6/5, φ_p = 2/25, φ_w = 31/50, φ_y = 7/100`, `LHS = 1939/2700 < 1`)
all four eigenvalues of `Aʷ` lie inside the unit circle (`exNE_no_root`) and there is no bounded
solution for zero forcing and `ω̃_{−1} = 1` (`exNE_no_bounded_solution`): non-existence, not
multiplicity. The theorem `determinacy_iff` covers both cases.
-/

namespace Gali.StickyWagesPrices.Determinacy4

open Polynomial Complex Real Filter Topology

/-- Galí (2015), p. 174: The number of roots (with multiplicity) of `p` in the open unit disc. -/
noncomputable def inCount (p : ℂ[X]) : ℕ := (p.roots.filter (fun z => ‖z‖ < 1)).card

/-- Galí (2015), p. 174: `∮ (z − α)⁻¹` over the unit circle: `2πi` inside, `0` outside. -/
theorem circleIntegral_sub_inv (α : ℂ) (hα : ‖α‖ ≠ 1) :
    (∮ z in C(0, 1), (z - α)⁻¹) = if ‖α‖ < 1 then 2 * π * I else 0 := by
  split_ifs with h
  · exact circleIntegral.integral_sub_inv_of_mem_ball (by simpa using h)
  · have hgt : 1 < ‖α‖ := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hα)
    refine DiffContOnCl.circleIntegral_eq_zero zero_le_one ?_
    refine DifferentiableOn.diffContOnCl_ball (U := {z | z ≠ α}) ?_ ?_
    · intro z hz
      exact ((differentiableAt_id.sub_const α).inv (sub_ne_zero.mpr hz)).differentiableWithinAt
    · intro z hz
      simp only [Metric.mem_closedBall, dist_zero_right] at hz
      intro h'
      rw [h'] at hz
      linarith

/-- Galí (2015), p. 174 (tool): the argument principle for polynomials on the unit circle. -/
theorem argument_principle (p : ℂ[X]) (hp : p ≠ 0) (hc : ∀ z : ℂ, ‖z‖ = 1 → p.eval z ≠ 0) :
    (∮ z in C(0, 1), p.derivative.eval z / p.eval z) = 2 * π * I * inCount p := by
  induction h : p.natDegree generalizing p with
  | zero =>
    obtain ⟨a, rfl⟩ : ∃ a, p = C a := ⟨_, eq_C_of_natDegree_eq_zero h⟩
    simp [inCount, circleIntegral]
  | succ n ih =>
    obtain ⟨α, hα⟩ : ∃ α, IsRoot p α :=
      Complex.exists_root (by rw [degree_eq_natDegree hp, h]; exact_mod_cast Nat.succ_pos n)
    set p₁ := p /ₘ (X - C α) with hp₁
    have hfac : (X - C α) * p₁ = p := mul_divByMonic_eq_iff_isRoot.mpr hα
    have hp₁0 : p₁ ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hfac; exact hp hfac.symm
    have hdeg : p₁.natDegree = n := by
      have := congrArg natDegree hfac
      rw [natDegree_mul (X_sub_C_ne_zero α) hp₁0, natDegree_X_sub_C, h] at this
      omega
    have hc₁ : ∀ z : ℂ, ‖z‖ = 1 → p₁.eval z ≠ 0 := by
      intro z hz h0
      apply hc z hz
      rw [← hfac, eval_mul, h0, mul_zero]
    have hαn : ‖α‖ ≠ 1 := fun h1 => hc α h1 hα
    have hne : ∀ z : ℂ, ‖z‖ = 1 → z - α ≠ 0 := fun z hz h0 => by
      rw [sub_eq_zero] at h0; rw [h0] at hz; exact hαn hz
    have heq : Set.EqOn (fun z => p.derivative.eval z / p.eval z)
        (fun z => (z - α)⁻¹ + p₁.derivative.eval z / p₁.eval z) (Metric.sphere 0 1) := by
      intro z hz
      have hz' : ‖z‖ = 1 := by simpa using hz
      have h1 := hne z hz'
      have h2 := hc₁ z hz'
      simp only
      rw [← hfac, derivative_mul]
      simp only [eval_mul, eval_add, eval_sub, eval_X, eval_C, derivative_sub, derivative_X,
        derivative_C, sub_zero, one_mul]
      field_simp
    have hint1 : CircleIntegrable (fun z : ℂ => (z - α)⁻¹) 0 1 := by
      refine ContinuousOn.circleIntegrable zero_le_one ?_
      refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) ?_
      intro z hz
      exact hne z (by simpa using hz)
    have hint2 : CircleIntegrable (fun z : ℂ => p₁.derivative.eval z / p₁.eval z) 0 1 := by
      refine ContinuousOn.circleIntegrable zero_le_one ?_
      refine ContinuousOn.div (Polynomial.continuousOn _) (Polynomial.continuousOn _) ?_
      intro z hz
      exact hc₁ z (by simpa using hz)
    rw [circleIntegral.integral_congr zero_le_one heq, circleIntegral.integral_add hint1 hint2,
      circleIntegral_sub_inv α hαn, ih p₁ hp₁0 hc₁ hdeg]
    have hroots : p.roots = α ::ₘ p₁.roots := by
      rw [← hfac, roots_mul (by rw [hfac]; exact hp), roots_X_sub_C]
      rfl
    unfold inCount
    rw [hroots, Multiset.filter_cons]
    split_ifs with hlt
    · simp only [Multiset.singleton_add, Multiset.card_cons]
      push_cast
      ring
    · simp

/-- Galí (2015), p. 174: A quartic polynomial from its five coefficients. -/
noncomputable def quart (a : Fin 5 → ℂ) : ℂ[X] :=
  C (a 0) + C (a 1) * X + C (a 2) * X ^ 2 + C (a 3) * X ^ 3 + C (a 4) * X ^ 4

/-- Galí (2015), p. 174 (tool): evaluating a quartic. -/
theorem eval_quart (a : Fin 5 → ℂ) (z : ℂ) :
    (quart a).eval z = a 0 + a 1 * z + a 2 * z ^ 2 + a 3 * z ^ 3 + a 4 * z ^ 4 := by
  simp [quart]

/-- Galí (2015), p. 174 (tool): evaluating the derivative of a quartic. -/
theorem eval_derivative_quart (a : Fin 5 → ℂ) (z : ℂ) :
    (quart a).derivative.eval z = a 1 + 2 * a 2 * z + 3 * a 3 * z ^ 2 + 4 * a 4 * z ^ 3 := by
  simp only [quart, derivative_add, derivative_C, derivative_mul, derivative_X, derivative_X_pow,
    eval_add, eval_mul, eval_C, eval_X, eval_pow, zero_mul, zero_add, mul_one]
  push_cast
  ring

/-- Galí (2015), p. 174 (tool): along a continuous path of quartics with no root on the unit
circle, the number of roots inside the unit disc is constant. -/
theorem inCount_path (a : ℝ → Fin 5 → ℂ) (ha : ∀ i, Continuous fun s => a s i)
    (hne : ∀ s ∈ Set.Icc (0 : ℝ) 1, quart (a s) ≠ 0)
    (hc : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ z : ℂ, ‖z‖ = 1 → (quart (a s)).eval z ≠ 0) :
    inCount (quart (a 0)) = inCount (quart (a 1)) := by
  set pr : ℝ → ℝ := fun s => (Set.projIcc (0 : ℝ) 1 zero_le_one s : ℝ) with hpr
  have hprc : Continuous pr := continuous_subtype_val.comp continuous_projIcc
  have hprm : ∀ s, pr s ∈ Set.Icc (0 : ℝ) 1 := fun s => Subtype.prop _
  set b : ℝ → Fin 5 → ℂ := fun s => a (pr s) with hb
  have hbc : ∀ i, Continuous fun s => b s i := fun i => (ha i).comp hprc
  have hI : ∀ s, (∮ z in C(0, 1), (quart (b s)).derivative.eval z / (quart (b s)).eval z)
      = 2 * π * I * inCount (quart (b s)) := fun s =>
    argument_principle _ (hne _ (hprm s)) (hc _ (hprm s))
  set n : ℝ → ℝ := fun s => (inCount (quart (b s)) : ℝ) with hn
  have hn_eq : ∀ s, n s = ((∮ z in C(0, 1), (quart (b s)).derivative.eval z /
      (quart (b s)).eval z) / (2 * π * I)).re := by
    intro s
    rw [hI s]
    have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    rw [mul_div_cancel_left₀ _ h2]
    simp [hn]
  have hcont : Continuous n := by
    have hF : Continuous fun s => (∮ z in C(0, 1), (quart (b s)).derivative.eval z /
        (quart (b s)).eval z) := by
      unfold circleIntegral
      refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun s θ => deriv (circleMap 0 1) θ • ((quart (b s)).derivative.eval
          (circleMap 0 1 θ) / (quart (b s)).eval (circleMap 0 1 θ))) ?_ 0 (2 * π)
      simp only [deriv_circleMap, eval_quart, eval_derivative_quart, smul_eq_mul]
      have hm : Continuous fun x : ℝ × ℝ => circleMap 0 1 x.2 :=
        (continuous_circleMap 0 1).comp continuous_snd
      have hbi : ∀ i, Continuous fun x : ℝ × ℝ => b x.1 i := fun i => (hbc i).comp continuous_fst
      refine Continuous.mul (by fun_prop) (Continuous.div (by fun_prop) (by fun_prop) ?_)
      intro x
      have := hc _ (hprm x.1) (circleMap 0 1 x.2) (by simp)
      rw [eval_quart] at this
      exact this
    have : n = fun s => ((∮ z in C(0, 1), (quart (b s)).derivative.eval z /
        (quart (b s)).eval z) / (2 * π * I)).re := funext hn_eq
    rw [this]
    exact Complex.continuous_re.comp (hF.div_const _)
  have hb0 : b 0 = a 0 := by simp [hb, hpr]
  have hb1 : b 1 = a 1 := by simp [hb, hpr]
  rw [← hb0, ← hb1]
  by_contra hneq
  -- an integer-valued continuous function on `[0,1]` is constant
  have hmid : ∀ m₀ m₁ : ℕ, m₀ < m₁ → ∀ s, n s ≠ m₀ + 1 / 2 := by
    intro m₀ m₁ _ s hs
    have : (2 * inCount (quart (b s)) : ℝ) = 2 * m₀ + 1 := by
      have := hs; simp only [hn] at this; linarith
    have h' : 2 * inCount (quart (b s)) = 2 * m₀ + 1 := by exact_mod_cast this
    omega
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · obtain ⟨s, -, hs⟩ := intermediate_value_Icc (zero_le_one (α := ℝ)) hcont.continuousOn
      (show (inCount (quart (b 0)) : ℝ) + 1 / 2 ∈ Set.Icc (n 0) (n 1) by
        simp only [hn, Set.mem_Icc]
        have : (inCount (quart (b 0)) + 1 : ℝ) ≤ inCount (quart (b 1)) := by exact_mod_cast hlt
        constructor <;> linarith)
    exact hmid _ _ hlt s hs
  · obtain ⟨s, -, hs⟩ := intermediate_value_Icc' (zero_le_one (α := ℝ)) hcont.continuousOn
      (show (inCount (quart (b 1)) : ℝ) + 1 / 2 ∈ Set.Icc (n 1) (n 0) by
        simp only [hn, Set.mem_Icc]
        have : (inCount (quart (b 1)) + 1 : ℝ) ≤ inCount (quart (b 0)) := by exact_mod_cast hgt
        constructor <;> linarith)
    exact hmid _ _ hgt s hs

/-- Galí (2015), eq. (24), p. 173: Parameters of system (24). -/
structure Par where
  β : ℝ
  σ : ℝ
  κp : ℝ
  κw : ℝ
  lamP : ℝ
  lamW : ℝ
  φp : ℝ
  φw : ℝ
  φy : ℝ

namespace Par

/-- Galí (2015), p. 174: `Ψ = λ_w κ_p + λ_p κ_w` \(= λ_p λ_w Θ_y\). -/
def Ψ (P : Par) : ℝ := P.lamW * P.κp + P.lamP * P.κw

/-- Galí (2015), p. 174: Constant coefficient of `q`. -/
def c0 (P : Par) : ℝ := -P.σ - P.κp * P.φp - P.κw * P.φw - P.φy

/-- Galí (2015), p. 174: Linear coefficient of `q`. -/
def c1 (P : Par) : ℝ :=
  2 * P.β * P.σ + P.β * P.κp * P.φp + P.β * P.κw * P.φw + 2 * P.β * P.φy + P.σ * P.lamP
    + P.σ * P.lamW + 2 * P.σ + P.κp * P.lamW * P.φp + P.κp * P.lamW * P.φw + P.κp * P.φp
    + P.κp + P.κw * P.lamP * P.φp + P.κw * P.lamP * P.φw + P.κw * P.φw + P.lamP * P.φy
    + P.lamW * P.φy + P.φy

/-- Galí (2015), p. 174: Quadratic coefficient of `q`. -/
def c2 (P : Par) : ℝ :=
  -P.β ^ 2 * P.σ - P.β ^ 2 * P.φy - P.β * P.σ * P.lamP - P.β * P.σ * P.lamW
    - 4 * P.β * P.σ - P.β * P.κp * P.φp - P.β * P.κp - P.β * P.κw * P.φw
    - P.β * P.lamP * P.φy - P.β * P.lamW * P.φy - 2 * P.β * P.φy - P.σ * P.lamP
    - P.σ * P.lamW - P.σ - P.κp * P.lamW - P.κp - P.κw * P.lamP

/-- Galí (2015), p. 174: Cubic coefficient of `q`. -/
def c3 (P : Par) : ℝ :=
  2 * P.β ^ 2 * P.σ + P.β ^ 2 * P.φy + P.β * P.σ * P.lamP + P.β * P.σ * P.lamW
    + 2 * P.β * P.σ + P.β * P.κp

/-- Galí (2015), p. 174: Leading coefficient of `q`. -/
def c4 (P : Par) : ℝ := -P.β ^ 2 * P.σ

/-- Galí (2015), p. 174: `q` evaluated at a real point. -/
def qr (P : Par) (r : ℝ) : ℝ :=
  P.c0 + P.c1 * r + P.c2 * r ^ 2 + P.c3 * r ^ 3 + P.c4 * r ^ 4

/-- Galí (2015), p. 174: `q(1) = Ψ (L − 1)` in polynomial form. -/
theorem qr_one (P : Par) :
    P.qr 1 = -P.Ψ + P.φy * (1 - P.β) * (P.lamP + P.lamW) + (P.φp + P.φw) * P.Ψ := by
  simp only [qr, c0, c1, c2, c3, c4, Ψ]; ring

end Par

set_option maxRecDepth 20000 in
/-- Galí (2015), p. 174 (the key inequality): writing `z = x + i y` on the unit circle, the real
combination `Re(q(z) · i z̄ ē)` with `e = (1 − βz)(1 − z̄)` equals
`(1 − β) y q(1) + y · (nonnegative terms)`. Here it is stated through the real and imaginary
parts of `q(z)`. -/
theorem circle_cert (P : Par) {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1)
    (hre : P.c0 + P.c1 * x + P.c2 * (x ^ 2 - y ^ 2) + P.c3 * (x ^ 3 - 3 * x * y ^ 2)
      + P.c4 * (x ^ 4 - 6 * x ^ 2 * y ^ 2 + y ^ 4) = 0)
    (him : P.c1 * y + P.c2 * (2 * x * y) + P.c3 * (3 * x ^ 2 * y - y ^ 3)
      + P.c4 * (4 * x ^ 3 * y - 4 * x * y ^ 3) = 0) :
    (1 - P.β) * y * P.qr 1 + y * (2 * P.Ψ * (1 - x)
        + (((1 - P.β * x) * (1 - x) + P.β * y ^ 2) ^ 2 + ((1 - P.β) * y) ^ 2)
          * (P.κp + P.σ * (1 + P.β - 2 * P.β * x + (P.lamP + P.lamW)))
        + P.φy * P.β * ((((1 - P.β * x) * (1 - x) + P.β * y ^ 2) ^ 2 + ((1 - P.β) * y) ^ 2)
          + 2 * (P.lamP + P.lamW) * (1 - x))) = 0 := by
  simp only [Par.c0, Par.c1, Par.c2, Par.c3, Par.c4, Par.qr, Par.Ψ] at hre him ⊢
  linear_combination (x ^ 2 * y * P.β - 2 * x * y * P.β + y ^ 3 * P.β + y) * hre
    - (x ^ 3 * P.β - x ^ 2 * P.β - x ^ 2 + x * y ^ 2 * P.β + x + y ^ 2 * P.β - y ^ 2) * him
    - (3 * x ^ 4 * y * P.β ^ 3 * P.σ - 4 * x ^ 3 * y * P.β ^ 3 * P.σ
      - 2 * x ^ 3 * y * P.β ^ 3 * P.φy - 2 * x ^ 3 * y * P.β ^ 2 * P.σ * P.lamP
      - 2 * x ^ 3 * y * P.β ^ 2 * P.σ * P.lamW - 8 * x ^ 3 * y * P.β ^ 2 * P.σ
      - 2 * x ^ 3 * y * P.β ^ 2 * P.κp + 2 * x ^ 2 * y ^ 3 * P.β ^ 3 * P.σ
      + x ^ 2 * y * P.β ^ 3 * P.σ + x ^ 2 * y * P.β ^ 3 * P.φy
      + x ^ 2 * y * P.β ^ 2 * P.σ * P.lamP + x ^ 2 * y * P.β ^ 2 * P.σ * P.lamW
      + 10 * x ^ 2 * y * P.β ^ 2 * P.σ + x ^ 2 * y * P.β ^ 2 * P.κp * P.φp
      + x ^ 2 * y * P.β ^ 2 * P.κp + x ^ 2 * y * P.β ^ 2 * P.κw * P.φw
      + x ^ 2 * y * P.β ^ 2 * P.lamP * P.φy + x ^ 2 * y * P.β ^ 2 * P.lamW * P.φy
      + 5 * x ^ 2 * y * P.β ^ 2 * P.φy + 4 * x ^ 2 * y * P.β * P.σ * P.lamP
      + 4 * x ^ 2 * y * P.β * P.σ * P.lamW + 7 * x ^ 2 * y * P.β * P.σ
      + x ^ 2 * y * P.β * P.κp * P.lamW + 4 * x ^ 2 * y * P.β * P.κp
      + x ^ 2 * y * P.β * P.κw * P.lamP - 4 * x * y ^ 3 * P.β ^ 3 * P.σ
      - 2 * x * y ^ 3 * P.β ^ 3 * P.φy - 2 * x * y ^ 3 * P.β ^ 2 * P.σ * P.lamP
      - 2 * x * y ^ 3 * P.β ^ 2 * P.σ * P.lamW - 2 * x * y ^ 3 * P.β ^ 2 * P.κp
      - 2 * x * y * P.β ^ 2 * P.σ - 2 * x * y * P.β ^ 2 * P.φy - 2 * x * y * P.β * P.σ * P.lamP
      - 2 * x * y * P.β * P.σ * P.lamW - 8 * x * y * P.β * P.σ - 2 * x * y * P.β * P.κp * P.φp
      - 2 * x * y * P.β * P.κp - 2 * x * y * P.β * P.κw * P.φw - 2 * x * y * P.β * P.lamP * P.φy
      - 2 * x * y * P.β * P.lamW * P.φy - 4 * x * y * P.β * P.φy - 2 * x * y * P.σ * P.lamP
      - 2 * x * y * P.σ * P.lamW - 2 * x * y * P.σ - 2 * x * y * P.κp * P.lamW
      - 2 * x * y * P.κp - 2 * x * y * P.κw * P.lamP - y ^ 5 * P.β ^ 3 * P.σ
      + y ^ 3 * P.β ^ 3 * P.σ + y ^ 3 * P.β ^ 3 * P.φy + y ^ 3 * P.β ^ 2 * P.σ * P.lamP
      + y ^ 3 * P.β ^ 2 * P.σ * P.lamW + 2 * y ^ 3 * P.β ^ 2 * P.σ
      + y ^ 3 * P.β ^ 2 * P.κp * P.φp + y ^ 3 * P.β ^ 2 * P.κp + y ^ 3 * P.β ^ 2 * P.κw * P.φw
      + y ^ 3 * P.β ^ 2 * P.lamP * P.φy + y ^ 3 * P.β ^ 2 * P.lamW * P.φy
      + y ^ 3 * P.β ^ 2 * P.φy - y ^ 3 * P.β * P.σ + y ^ 3 * P.β * P.κp * P.lamW
      + y ^ 3 * P.β * P.κw * P.lamP + y * P.β ^ 2 * P.lamP * P.φy + y * P.β ^ 2 * P.lamW * P.φy
      + y * P.β * P.σ - y * P.β * P.κp * P.lamW * P.φp - y * P.β * P.κp * P.lamW * P.φw
      + y * P.β * P.κp * P.lamW - y * P.β * P.κw * P.lamP * P.φp
      - y * P.β * P.κw * P.lamP * P.φw + y * P.β * P.κw * P.lamP + y * P.β * P.φy
      + y * P.σ * P.lamP + y * P.σ * P.lamW + 2 * y * P.σ + y * P.κp * P.lamW * P.φp
      + y * P.κp * P.lamW * P.φw + y * P.κp * P.lamW + y * P.κp * P.φp + y * P.κp
      + y * P.κw * P.lamP * P.φp + y * P.κw * P.lamP * P.φw + y * P.κw * P.lamP
      + y * P.κw * P.φw + y * P.lamP * P.φy + y * P.lamW * P.φy + y * P.φy) * hxy

namespace Par

/-- Galí (2015), p. 174: The complex coefficient vector of `q`. -/
noncomputable def qv (P : Par) : Fin 5 → ℂ := ![(P.c0 : ℂ), P.c1, P.c2, P.c3, P.c4]

/-- Galí (2015), p. 174: The quartic `q(z)`, with `det(A₀ʷ − z A₁ʷ) = −q(z)`. -/
noncomputable def qC (P : Par) : ℂ[X] := quart P.qv

/-- Galí (2015), p. 174: The reversed coefficient vector. -/
noncomputable def Qv (P : Par) : Fin 5 → ℂ := ![(P.c4 : ℂ), P.c3, P.c2, P.c1, P.c0]

/-- Galí (2015), p. 174: The reversed quartic `Q(w) = w⁴ q(1/w)`, whose roots are the eigenvalues of
`(A₀ʷ)⁻¹ A₁ʷ`. -/
noncomputable def QC (P : Par) : ℂ[X] := quart P.Qv

/-- Galí (2015), p. 174: `q(z)` in coefficient form. -/
theorem eval_qC (P : Par) (z : ℂ) :
    P.qC.eval z = P.c0 + P.c1 * z + P.c2 * z ^ 2 + P.c3 * z ^ 3 + P.c4 * z ^ 4 := by
  simp [qC, qv, eval_quart]

/-- Galí (2015), p. 174: the reversed quartic `Q(w)` in coefficient form. -/
theorem eval_QC (P : Par) (z : ℂ) :
    P.QC.eval z = P.c4 + P.c3 * z + P.c2 * z ^ 2 + P.c1 * z ^ 3 + P.c0 * z ^ 4 := by
  simp [QC, Qv, eval_quart]

/-- Galí (2015), p. 174: `Q(w) = w⁴ q(1/w)`, so the roots of `Q` (eigenvalues of `Aʷ`) are
the reciprocals of the roots of `q`. -/
theorem eval_QC_eq (P : Par) {w : ℂ} (hw : w ≠ 0) : P.QC.eval w = w ^ 4 * P.qC.eval w⁻¹ := by
  rw [eval_QC, eval_qC]
  field_simp
  ring

/-- Galí (2015), p. 174: `q` at a real point is real. -/
theorem eval_qC_ofReal (P : Par) (r : ℝ) : P.qC.eval (r : ℂ) = (P.qr r : ℂ) := by
  rw [eval_qC]; simp [qr]

/-- Galí (2015), p. 174: `q` has real coefficients, `q(z̄) = conj (q z)`. -/
theorem eval_qC_conj (P : Par) (z : ℂ) :
    P.qC.eval ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.qC.eval z) := by
  simp [eval_qC, map_add, map_mul, map_pow]

/-- Galí (2015), p. 174: real and imaginary parts of `q(x + i y)`. -/
theorem eval_qC_mk (P : Par) (x y : ℝ) : P.qC.eval ⟨x, y⟩ =
    ⟨P.c0 + P.c1 * x + P.c2 * (x ^ 2 - y ^ 2) + P.c3 * (x ^ 3 - 3 * x * y ^ 2)
      + P.c4 * (x ^ 4 - 6 * x ^ 2 * y ^ 2 + y ^ 4),
     P.c1 * y + P.c2 * (2 * x * y) + P.c3 * (3 * x ^ 2 * y - y ^ 3)
      + P.c4 * (4 * x ^ 3 * y - 4 * x * y ^ 3)⟩ := by
  rw [eval_qC]
  apply Complex.ext <;> simp [pow_succ, Complex.mul_re, Complex.mul_im] <;> ring

/-- Galí (2015), p. 174: The sign conditions of the book (all coefficients nonnegative, `0 < β <
1`, `σ > 0`,
`λ_p, λ_w > 0`), with `κ_p, κ_w ≥ 0`. -/
def Adm (P : Par) : Prop :=
  0 < P.β ∧ P.β < 1 ∧ 0 < P.σ ∧ 0 ≤ P.κp ∧ 0 ≤ P.κw ∧ 0 < P.lamP ∧ 0 < P.lamW ∧
    0 ≤ P.φp ∧ 0 ≤ P.φw ∧ 0 ≤ P.φy

/-- Galí (2015), p. 174: `q(−1)` as minus a sum of terms that are nonnegative under the sign
conditions. -/
theorem qr_neg_one (P : Par) : P.qr (-1) =
    -(2 * P.σ * (1 + P.β) * (2 + 2 * P.β + (P.lamP + P.lamW)) + P.κp * (2 + 2 * P.β) + P.Ψ)
    - P.φy * (1 + P.β) * (2 + 2 * P.β + (P.lamP + P.lamW))
    - P.φp * (P.κp * (2 + 2 * P.β) + P.Ψ) - P.φw * (P.κw * (2 + 2 * P.β) + P.Ψ) := by
  simp only [qr, c0, c1, c2, c3, c4, Ψ]; ring

/-- Galí (2015), p. 174: `Ψ = λ_w κ_p + λ_p κ_w ≥ 0` under the sign conditions. -/
theorem Ψ_nonneg {P : Par} (hP : P.Adm) : 0 ≤ P.Ψ := by
  obtain ⟨-, -, -, hkp, hkw, hlp, hlw, -⟩ := hP
  unfold Ψ
  exact add_nonneg (mul_nonneg hlw.le hkp) (mul_nonneg hlp.le hkw)

/-- Galí (2015), p. 174: `q(−1) < 0`, so `−1` is never an eigenvalue. -/
theorem qr_neg_one_neg {P : Par} (hP : P.Adm) : P.qr (-1) < 0 := by
  have hΨ := Ψ_nonneg hP
  obtain ⟨hb0, -, hs, hkp, hkw, hlp, hlw, hfp, hfw, hfy⟩ := hP
  rw [qr_neg_one]
  have h1 : 0 < 2 * P.σ * (1 + P.β) * (2 + 2 * P.β + (P.lamP + P.lamW)) := by positivity
  have h2 : 0 ≤ P.φy * (1 + P.β) * (2 + 2 * P.β + (P.lamP + P.lamW)) := by positivity
  have h3 : 0 ≤ P.φp * (P.κp * (2 + 2 * P.β) + P.Ψ) := by positivity
  have h4 : 0 ≤ P.φw * (P.κw * (2 + 2 * P.β) + P.Ψ) := by positivity
  have h5 : 0 ≤ P.κp * (2 + 2 * P.β) := by positivity
  linarith

/-- Galí (2015), p. 174: `q(0) = −det A₀ʷ < 0`. -/
theorem c0_neg {P : Par} (hP : P.Adm) : P.c0 < 0 := by
  obtain ⟨-, -, hs, hkp, hkw, -, -, hfp, hfw, hfy⟩ := hP
  unfold c0
  nlinarith [mul_nonneg hkp hfp, mul_nonneg hkw hfw]

/-- Galí (2015), p. 174: the leading coefficient `−β² σ` of `q` is negative. -/
theorem c4_neg {P : Par} (hP : P.Adm) : P.c4 < 0 := by
  obtain ⟨hb, -, hs, -⟩ := hP
  unfold c4
  nlinarith [mul_pos (pow_pos hb 2) hs]

/-- Galí (2015), p. 174: the circle certificate forces `q(1) < 0` at any root `x + i y`,
`y > 0`, on the unit circle. -/
theorem qr_one_neg_of_root {P : Par} (hP : P.Adm) {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1)
    (hy : 0 < y) (h0 : P.qC.eval ⟨x, y⟩ = 0) : P.qr 1 < 0 := by
  have hΨ := Ψ_nonneg hP
  obtain ⟨hb0, hb1, hs, hkp, -, hlp, hlw, -, -, hfy⟩ := hP
  rw [eval_qC_mk] at h0
  have hre := congrArg Complex.re h0
  have him := congrArg Complex.im h0
  simp only [Complex.zero_re, Complex.zero_im] at hre him
  have hc := circle_cert P hxy hre him
  have hx1 : x ≤ 1 := by nlinarith
  have he2p : 0 < ((1 - P.β * x) * (1 - x) + P.β * y ^ 2) ^ 2 + ((1 - P.β) * y) ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos (mul_pos (by linarith) hy) 2)
  have hA : 0 ≤ 2 * P.Ψ * (1 - x) := mul_nonneg (by linarith) (by linarith)
  have hbx : P.β * x ≤ P.β := by
    have := mul_le_mul_of_nonneg_left hx1 hb0.le
    linarith
  have hB : 0 < (((1 - P.β * x) * (1 - x) + P.β * y ^ 2) ^ 2 + ((1 - P.β) * y) ^ 2)
      * (P.κp + P.σ * (1 + P.β - 2 * P.β * x + (P.lamP + P.lamW))) :=
    mul_pos he2p (add_pos_of_nonneg_of_pos hkp (mul_pos hs (by linarith)))
  have hC : 0 ≤ P.φy * P.β * ((((1 - P.β * x) * (1 - x) + P.β * y ^ 2) ^ 2
      + ((1 - P.β) * y) ^ 2) + 2 * (P.lamP + P.lamW) * (1 - x)) :=
    mul_nonneg (mul_nonneg hfy hb0.le)
      (add_nonneg he2p.le (mul_nonneg (by linarith) (by linarith)))
  have hsum := mul_pos hy (add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos hA hB) hC)
  by_contra hq
  have hq' : 0 ≤ (1 - P.β) * y * P.qr 1 :=
    mul_nonneg (mul_nonneg (by linarith) hy.le) (not_lt.mp hq)
  linarith

/-- Galí (2015), p. 174: when `q(1) > 0`, i.e. the condition of p. 174 holds, `q` has no root on
the unit circle. -/
theorem qC_ne_zero_of_norm_eq_one {P : Par} (hP : P.Adm) (h1 : 0 < P.qr 1) {z : ℂ}
    (hz : ‖z‖ = 1) : P.qC.eval z ≠ 0 := by
  obtain ⟨x, y⟩ := z
  have hxy : x ^ 2 + y ^ 2 = 1 := by
    have h := Complex.sq_norm (⟨x, y⟩ : ℂ)
    rw [hz, Complex.normSq_mk] at h
    nlinarith
  rcases lt_trichotomy y 0 with hy | hy | hy
  · intro h0
    have hconj : P.qC.eval ⟨x, -y⟩ = 0 := by
      have := eval_qC_conj P ⟨x, y⟩
      rw [h0, map_zero] at this
      exact this
    exact absurd (qr_one_neg_of_root hP (by nlinarith) (by linarith) hconj) (not_lt.mpr h1.le)
  · subst hy
    have hx : x = 1 ∨ x = -1 := by
      have : (x - 1) * (x + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    have hz' : (⟨x, 0⟩ : ℂ) = (x : ℂ) := Complex.ext (by simp) (by simp)
    rw [hz', eval_qC_ofReal]
    intro h0
    have h0' : P.qr x = 0 := by exact_mod_cast h0
    rcases hx with rfl | rfl
    · linarith
    · linarith [qr_neg_one_neg hP]
  · exact fun h0 => absurd (qr_one_neg_of_root hP hxy hy h0) (not_lt.mpr h1.le)

/-- Galí (2015), p. 174: The reversed quartic has no root on the unit circle when `q(1) > 0`. -/
theorem QC_ne_zero_of_norm_eq_one {P : Par} (hP : P.Adm) (h1 : 0 < P.qr 1) {w : ℂ}
    (hw : ‖w‖ = 1) : P.QC.eval w ≠ 0 := by
  have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; exact zero_ne_one hw
  rw [eval_QC_eq P hw0]
  refine mul_ne_zero (pow_ne_zero _ hw0) (qC_ne_zero_of_norm_eq_one hP h1 ?_)
  rw [norm_inv, hw, inv_one]

end Par

/-- Galí (2015), p. 174 (tool): the leading coefficient of a quartic. -/
theorem coeff_quart_four (a : Fin 5 → ℂ) : (quart a).coeff 4 = a 4 := by
  simp [quart, coeff_X_pow, coeff_C_mul]

/-- Galí (2015), p. 174 (tool): a quartic with nonzero leading coefficient is nonzero. -/
theorem quart_ne_zero {a : Fin 5 → ℂ} (h : a 4 ≠ 0) : quart a ≠ 0 := by
  intro h0
  apply h
  rw [← coeff_quart_four a, h0, coeff_zero]

namespace Par

/-- Galí (2015), p. 174: Linear interpolation between two parameter vectors (the homotopy of the
proof). -/
def mix (P Q : Par) (s : ℝ) : Par :=
  ⟨(1 - s) * P.β + s * Q.β, (1 - s) * P.σ + s * Q.σ, (1 - s) * P.κp + s * Q.κp,
    (1 - s) * P.κw + s * Q.κw, (1 - s) * P.lamP + s * Q.lamP, (1 - s) * P.lamW + s * Q.lamW,
    (1 - s) * P.φp + s * Q.φp, (1 - s) * P.φw + s * Q.φw, (1 - s) * P.φy + s * Q.φy⟩

/-- Galí (2015), p. 174 (homotopy): the path starts at `P`. -/
theorem mix_zero (P Q : Par) : P.mix Q 0 = P := by
  cases P; simp [mix]

/-- Galí (2015), p. 174 (homotopy): the path ends at `Q`. -/
theorem mix_one (P Q : Par) : P.mix Q 1 = Q := by
  cases Q; simp [mix]

/-- Galí (2015), p. 174 (homotopy): the sign conditions are convex. -/
theorem adm_mix {P Q : Par} (hP : P.Adm) (hQ : Q.Adm) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (P.mix Q s).Adm := by
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hP
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := hQ
  have h1s : 0 ≤ 1 - s := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [mix]
  · rcases eq_or_lt_of_le hs0 with h | h
    · subst h; simpa using a1
    · nlinarith
  · rcases eq_or_lt_of_le hs0 with h | h
    · subst h; simpa using a2
    · nlinarith
  · rcases eq_or_lt_of_le hs0 with h | h
    · subst h; simpa using a3
    · nlinarith
  · positivity
  · positivity
  · rcases eq_or_lt_of_le hs0 with h | h
    · subst h; simpa using a6
    · nlinarith
  · rcases eq_or_lt_of_le hs0 with h | h
    · subst h; simpa using a7
    · nlinarith
  · positivity
  · positivity
  · positivity

/-- Galí (2015), p. 174 (homotopy): the coefficients move continuously along the path. -/
theorem continuous_Qv_mix (P Q : Par) (i : Fin 5) : Continuous fun s => (P.mix Q s).Qv i := by
  fin_cases i <;> simp only [Qv, c0, c1, c2, c3, c4, mix] <;> fun_prop

/-- Galí (2015), p. 174 (homotopy step): along a segment of admissible parameters on which
`q(1) > 0`, the number of eigenvalues inside the unit circle does not change. -/
theorem inCount_QC_mix {P Q : Par} (hP : P.Adm) (hQ : Q.Adm)
    (h1 : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < (P.mix Q s).qr 1) : inCount P.QC = inCount Q.QC := by
  have h := inCount_path (fun s => (P.mix Q s).Qv) (continuous_Qv_mix P Q) ?_ ?_
  · simpa [QC, mix_zero, mix_one] using h
  · intro s hs
    refine quart_ne_zero ?_
    simp only [Qv, Matrix.cons_val]
    exact_mod_cast (c0_neg (adm_mix hP hQ hs)).ne
  · intro s hs z hz
    exact QC_ne_zero_of_norm_eq_one (adm_mix hP hQ hs) (h1 s hs) hz

/-- Galí (2015), p. 174: The reference parameters: `β = 1/2`, `σ = 1`, `κ_p = κ_w = 1`, `λ_p = λ_w
= 21/16`,
`φ_p = 2`, `φ_w = φ_y = 0`. -/
noncomputable def Pref : Par := ⟨1 / 2, 1, 1, 1, 21 / 16, 21 / 16, 2, 0, 0⟩

/-- Galí (2015), p. 174 (reference point): at `Pref`, `Q` factors with roots
`1/2, 1/3, 4, 1/8`. -/
theorem QC_ref : Pref.QC = C (-3) * ((X - C (1 / 2)) * (X - C (1 / 3)) * (X - C 4)
    * (X - C (1 / 8))) := by
  apply Polynomial.funext
  intro z
  rw [eval_QC]
  simp only [Pref, c0, c1, c2, c3, c4, eval_mul, eval_C, eval_sub, eval_X]
  push_cast
  ring

/-- Galí (2015), p. 174 (reference point): three eigenvalues inside the unit circle. -/
theorem inCount_ref : inCount Pref.QC = 3 := by
  rw [QC_ref, inCount, roots_C_mul _ (by norm_num)]
  have h1 : ∀ a : ℂ, X - C a ≠ 0 := X_sub_C_ne_zero
  rw [roots_mul (by simp [h1]), roots_mul (by simp [h1]), roots_mul (by simp [h1])]
  simp only [roots_X_sub_C]
  norm_num [Multiset.filter_cons, Multiset.filter_singleton]

/-- Galí (2015), p. 174 (reference point): `Pref` satisfies the sign conditions. -/
theorem adm_ref : Pref.Adm := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Pref] <;> norm_num

/-- Galí (2015), p. 174: The policy endpoint: `φ_p = 2`, `φ_w = φ_y = 0` with the structural
parameters of `P`. -/
def endpt (P : Par) : Par := ⟨P.β, P.σ, P.κp, P.κw, P.lamP, P.lamW, 2, 0, 0⟩

/-- Galí (2015), p. 174 (eigenvalue count): under the sign conditions and `q(1) > 0`, exactly
three roots of `Q` (eigenvalues of `(A₀ʷ)⁻¹ A₁ʷ`) lie in the open unit disc. -/
theorem inCount_QC {P : Par} (hP : P.Adm) (hΨ : 0 < P.Ψ) (h1 : 0 < P.qr 1) :
    inCount P.QC = 3 := by
  have hE : P.endpt.Adm := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, -⟩ := hP
    exact ⟨a1, a2, a3, a4, a5, a6, a7, by simp [endpt], by simp [endpt], by simp [endpt]⟩
  have step1 : inCount P.QC = inCount P.endpt.QC := by
    refine inCount_QC_mix hP hE fun s hs => ?_
    have : (P.mix P.endpt s).qr 1 = (1 - s) * P.qr 1 + s * P.Ψ := by
      simp only [qr_one, mix, endpt, Ψ]; ring
    rw [this]
    obtain ⟨hs0, hs1⟩ := hs
    rcases eq_or_lt_of_le hs0 with h | h
    · subst h; simpa using h1
    · have : 0 ≤ (1 - s) * P.qr 1 := mul_nonneg (by linarith) h1.le
      nlinarith
  have step2 : inCount P.endpt.QC = inCount Pref.QC := by
    refine inCount_QC_mix hE adm_ref fun s hs => ?_
    have hm := adm_mix hE adm_ref hs
    have : (P.endpt.mix Pref s).qr 1 = (P.endpt.mix Pref s).Ψ := by
      simp only [qr_one, mix, endpt, Pref, Ψ]; ring
    rw [this]
    obtain ⟨hs0, hs1⟩ := hs
    rcases eq_or_lt_of_le hs0 with h | h
    · subst h; simpa [mix_zero, endpt, Ψ] using hΨ
    · obtain ⟨-, -, -, hkp, hkw, hlp, hlw, -⟩ := hm
      have hk : 0 < (P.endpt.mix Pref s).κp := by
        simp only [mix, endpt, Pref] at hkp ⊢
        nlinarith [hP.2.2.2.1]
      unfold Ψ
      nlinarith [mul_pos hlw hk, mul_nonneg hlp.le hkw]
  rw [step1, step2, inCount_ref]

end Par

/-- Galí (2015), p. 174 (tool): a quartic with nonzero leading coefficient has degree four. -/
theorem natDegree_quart {a : Fin 5 → ℂ} (h : a 4 ≠ 0) : (quart a).natDegree = 4 := by
  unfold quart
  compute_degree!

/-- Galí (2015), p. 174 (tool): such a quartic has four complex roots with multiplicity. -/
theorem card_roots_quart {a : Fin 5 → ℂ} (h : a 4 ≠ 0) : (quart a).roots.card = 4 := by
  rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_quart h]

/-- Galí (2015), p. 174: The number of roots (with multiplicity) of `p` strictly outside the unit
circle. -/
noncomputable def outCount (p : ℂ[X]) : ℕ := (p.roots.filter (fun z => 1 < ‖z‖)).card

/-- Galí (2015), p. 174 (tool): without roots on the unit circle, roots split into those
inside and those outside. -/
theorem inCount_add_outCount {p : ℂ[X]} (hc : ∀ z : ℂ, ‖z‖ = 1 → p.eval z ≠ 0) :
    inCount p + outCount p = p.roots.card := by
  unfold inCount outCount
  have h : p.roots.filter (fun z => 1 < ‖z‖) = p.roots.filter (fun z => ¬ ‖z‖ < 1) := by
    refine Multiset.filter_congr fun z hz => ?_
    have hz1 : ‖z‖ ≠ 1 := fun h1 => hc z h1 (Polynomial.isRoot_of_mem_roots hz)
    constructor
    · intro h; exact not_lt.mpr h.le
    · intro h; exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm hz1)
  rw [h, ← Multiset.card_add, Multiset.filter_add_not]

namespace Par

/-- Galí (2015), p. 174: `Q ≠ 0`. -/
theorem QC_ne_zero {P : Par} (hP : P.Adm) : P.QC ≠ 0 :=
  quart_ne_zero (by simp only [Qv, Matrix.cons_val]; exact_mod_cast (c0_neg hP).ne)

/-- Galí (2015), p. 174: `Aʷ` has four eigenvalues with multiplicity. -/
theorem card_roots_QC {P : Par} (hP : P.Adm) : P.QC.roots.card = 4 :=
  card_roots_quart (by simp only [Qv, Matrix.cons_val]; exact_mod_cast (c0_neg hP).ne)

/-- Galí (2015), p. 174: under the condition, exactly one eigenvalue lies outside the unit
circle. -/
theorem outCount_QC {P : Par} (hP : P.Adm) (hΨ : 0 < P.Ψ) (h1 : 0 < P.qr 1) :
    outCount P.QC = 1 := by
  have h := inCount_add_outCount (p := P.QC) fun z hz => QC_ne_zero_of_norm_eq_one hP h1 hz
  rw [inCount_QC hP hΨ h1, card_roots_QC hP] at h
  omega

/-- Galí (2015), p. 174: The derivative `q'(r)`. -/
def dqr (P : Par) (r : ℝ) : ℝ := P.c1 + 2 * P.c2 * r + 3 * P.c3 * r ^ 2 + 4 * P.c4 * r ^ 3

/-- Galí (2015), p. 174: the derivative of `Q` in coefficient form. -/
theorem eval_derivative_QC (P : Par) (w : ℂ) :
    P.QC.derivative.eval w = P.c3 + 2 * P.c2 * w + 3 * P.c1 * w ^ 2 + 4 * P.c0 * w ^ 3 := by
  simp [QC, Qv, eval_derivative_quart]

/-- Galí (2015), p. 174: `q` is continuous on the reals. -/
theorem continuous_qr (P : Par) : Continuous P.qr := by
  unfold qr; fun_prop

/-- Galí (2015), p. 174: `q(0)` is the constant coefficient. -/
theorem qr_zero (P : Par) : P.qr 0 = P.c0 := by simp [qr]

/-- Galí (2015), p. 174: `q(0)` is the constant coefficient (complex form). -/
theorem qC_eval_zero (P : Par) : P.qC.eval 0 = P.c0 := by simp [eval_qC]

/-- Galí (2015), p. 174: A root `ζ` of `q` in the closed unit disc gives the root `ζ⁻¹` of `Q`
strictly outside the
unit circle (when `q(1) > 0`). -/
theorem inv_mem_out {P : Par} (hP : P.Adm) (h1 : 0 < P.qr 1) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1)
    (h0 : P.qC.eval ζ = 0) : ζ⁻¹ ∈ P.QC.roots.filter (fun z => 1 < ‖z‖) := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [qC_eval_zero] at h0
    exact (c0_neg hP).ne (by exact_mod_cast h0)
  have hroot : P.QC.eval ζ⁻¹ = 0 := by
    rw [eval_QC_eq P (inv_ne_zero hζ0), inv_inv, h0, mul_zero]
  rw [Multiset.mem_filter, mem_roots (QC_ne_zero hP)]
  refine ⟨hroot, ?_⟩
  have hn : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
  rw [norm_inv]
  have hge : 1 ≤ ‖ζ‖⁻¹ := one_le_inv_iff₀.mpr ⟨hn, hζ⟩
  refine lt_of_le_of_ne hge fun he => ?_
  exact QC_ne_zero_of_norm_eq_one hP h1 (w := ζ⁻¹) (by rw [norm_inv, ← he]) hroot

/-- Galí (2015), p. 174: under the condition, `q` has exactly one root in the closed unit disc;
it is real, lies in `(0, 1)` and is simple. -/
theorem stable_root {P : Par} (hP : P.Adm) (hΨ : 0 < P.Ψ) (h1 : 0 < P.qr 1) :
    ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ P.qr μ = 0 ∧ P.dqr μ ≠ 0 ∧
      ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → P.qC.eval ζ = 0 → ζ = μ := by
  have hq0 : P.qr 0 < 0 := by rw [qr_zero]; exact c0_neg hP
  obtain ⟨μ, ⟨hμ0, hμ1⟩, hμ⟩ := intermediate_value_Ioo (zero_le_one (α := ℝ))
    (continuous_qr P).continuousOn (show (0 : ℝ) ∈ Set.Ioo (P.qr 0) (P.qr 1) from ⟨hq0, h1⟩)
  obtain ⟨w0, hw0⟩ := Multiset.card_eq_one.mp (outCount_QC hP hΨ h1)
  have hμC : P.qC.eval (μ : ℂ) = 0 := by rw [eval_qC_ofReal, hμ, Complex.ofReal_zero]
  have hμn : ‖(μ : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hμ0]; exact hμ1.le
  have hmem := inv_mem_out hP h1 hμn hμC
  rw [hw0, Multiset.mem_singleton] at hmem
  refine ⟨μ, hμ0, hμ1, hμ, ?_, ?_⟩
  · intro hd
    have hw : ((μ : ℂ))⁻¹ ∈ P.QC.roots.filter (fun z => 1 < ‖z‖) := inv_mem_out hP h1 hμn hμC
    have hroot : P.QC.IsRoot ((μ : ℂ))⁻¹ := by
      have := (Multiset.mem_filter.mp hw).1
      exact (mem_roots (QC_ne_zero hP)).mp this
    have hder : P.QC.derivative.IsRoot ((μ : ℂ))⁻¹ := by
      have hμ0' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ0.ne'
      have e1 : (P.qr μ : ℂ) = 0 := by rw [hμ]; simp
      have e2 : (P.dqr μ : ℂ) = 0 := by rw [hd]; simp
      simp only [qr, dqr] at e1 e2
      push_cast at e1 e2
      rw [IsRoot, eval_derivative_QC]
      field_simp
      linear_combination 4 * e1 - (μ : ℂ) * e2
    have hmult := (one_lt_rootMultiplicity_iff_isRoot (QC_ne_zero hP)).mpr ⟨hroot, hder⟩
    have hcnt : 2 ≤ (P.QC.roots.filter (fun z => 1 < ‖z‖)).count ((μ : ℂ))⁻¹ := by
      rw [Multiset.count_filter_of_pos (p := fun z : ℂ => 1 < ‖z‖) (Multiset.mem_filter.mp hw).2,
        count_roots]
      omega
    have hle := Multiset.count_le_card ((μ : ℂ))⁻¹ (P.QC.roots.filter (fun z => 1 < ‖z‖))
    have hc1 : (P.QC.roots.filter (fun z => 1 < ‖z‖)).card = 1 := outCount_QC hP hΨ h1
    omega
  · intro ζ hζ h0
    have hm := inv_mem_out hP h1 hζ h0
    rw [hw0, Multiset.mem_singleton, ← hmem] at hm
    exact inv_injective hm

end Par

/-- Galí (2015), p. 174, fn. 1 (Blanchard–Kahn, the tool): if every complex eigenvalue of a
real square matrix `K` lies in the open unit disc, the entries of `Kᵏ` decay geometrically
(Gelfand's spectral radius formula). -/
theorem pow_entry_bound {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ w : ℂ, (Matrix.scalar (Fin n) w - K.map Complex.ofReal).det = 0 → ‖w‖ < 1) :
    ∃ Cb ρ : ℝ, 0 ≤ Cb ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k := by
  have hpow : ∀ k, ((K ^ k).map Complex.ofReal) = (K.map Complex.ofReal) ^ k := fun k =>
    (Complex.ofRealHom.mapMatrix.map_pow K k)
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  set A : Matrix (Fin n) (Fin n) ℂ := K.map Complex.ofReal with hA
  have hspec : ∀ w ∈ spectrum ℂ A, w ∈ A.charpoly.roots.toFinset ∧ ‖w‖ < 1 := by
    intro w hw
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at hw
    refine ⟨?_, h w ?_⟩
    · rw [Multiset.mem_toFinset, mem_roots (Matrix.charpoly_monic A).ne_zero]
      exact hw
    · rw [← Matrix.eval_charpoly]; exact hw
  set ρ0 : NNReal := A.charpoly.roots.toFinset.sup (fun w => ‖w‖₊) with hρ0
  have hρ0lt : ρ0 < 1 := by
    rw [hρ0, Finset.sup_lt_iff (by norm_num)]
    intro w hw
    have hw' : w ∈ spectrum ℂ A := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
      rw [Multiset.mem_toFinset, mem_roots (Matrix.charpoly_monic A).ne_zero] at hw
      exact hw
    have := (hspec w hw').2
    rw [← NNReal.coe_lt_coe, coe_nnnorm]
    simpa using this
  have hsr : spectralRadius ℂ A ≤ (ρ0 : ENNReal) := by
    refine iSup₂_le fun w hw => ?_
    rw [quasispectrum_eq_spectrum_union_zero] at hw
    rcases hw with hw | hw
    · exact ENNReal.coe_le_coe.mpr (Finset.le_sup (f := fun w => ‖w‖₊) (hspec w hw).1)
    · rw [Set.mem_singleton_iff] at hw
      subst hw
      simp
  set r : ℝ := ((ρ0 : ℝ) + 1) / 2 with hr
  have hρ0r : (ρ0 : ℝ) < r := by
    have : (ρ0 : ℝ) < 1 := by exact_mod_cast hρ0lt
    rw [hr]; linarith
  have hr1 : r < 1 := by
    have : (ρ0 : ℝ) < 1 := by exact_mod_cast hρ0lt
    rw [hr]; linarith
  have hr0 : 0 < r := lt_of_le_of_lt ρ0.coe_nonneg hρ0r
  have hlt : spectralRadius ℂ A < ENNReal.ofReal r := by
    refine lt_of_le_of_lt hsr ?_
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff hr0).mpr hρ0r
  have hev := (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius A).eventually_lt_const
    hlt
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  -- norm bound for large powers
  have hbig : ∀ k ≥ N + 1, ‖A ^ k‖ ≤ r ^ k := by
    intro k hk
    have h1 := hN k (by omega)
    rw [ENNReal.ofReal_lt_ofReal_iff hr0] at h1
    have hk0 : k ≠ 0 := by omega
    have h2 : (‖A ^ k‖ ^ (1 / k : ℝ)) ^ k = ‖A ^ k‖ := by
      rw [one_div]; exact Real.rpow_inv_natCast_pow (norm_nonneg _) hk0
    rw [← h2]
    exact (pow_lt_pow_left₀ h1 (Real.rpow_nonneg (norm_nonneg _) _) hk0).le
  set Cb : ℝ := 1 + ∑ k ∈ Finset.range (N + 1), ‖A ^ k‖ / r ^ k with hCb
  have hCb0 : 0 ≤ Cb := by
    have : 0 ≤ ∑ k ∈ Finset.range (N + 1), ‖A ^ k‖ / r ^ k :=
      Finset.sum_nonneg fun k _ => div_nonneg (norm_nonneg _) (pow_nonneg hr0.le _)
    linarith
  have hCb1 : 1 ≤ Cb := by
    have : 0 ≤ ∑ k ∈ Finset.range (N + 1), ‖A ^ k‖ / r ^ k :=
      Finset.sum_nonneg fun k _ => div_nonneg (norm_nonneg _) (pow_nonneg hr0.le _)
    linarith
  have hall : ∀ k, ‖A ^ k‖ ≤ Cb * r ^ k := by
    intro k
    by_cases hk : k ≤ N
    · have hmem : k ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
      have hle : ‖A ^ k‖ / r ^ k ≤ ∑ k ∈ Finset.range (N + 1), ‖A ^ k‖ / r ^ k :=
        Finset.single_le_sum (f := fun k => ‖A ^ k‖ / r ^ k)
          (fun k _ => div_nonneg (norm_nonneg _) (pow_nonneg hr0.le _)) hmem
      have hrk : 0 < r ^ k := pow_pos hr0 k
      have : ‖A ^ k‖ = ‖A ^ k‖ / r ^ k * r ^ k := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith) hrk.le
    · have := hbig k (by omega)
      have hrk : 0 ≤ r ^ k := pow_nonneg hr0.le k
      nlinarith
  refine ⟨Cb, r, hCb0, hr0, hr1, fun k i j => ?_⟩
  have hentry : |(K ^ k) i j| = ‖(A ^ k) i j‖ := by
    have e : (A ^ k) i j = ((K ^ k) i j : ℂ) := by
      have := congrFun (congrFun (hpow k) i) j
      exact this.symm
    rw [e, Complex.norm_real, Real.norm_eq_abs]
  rw [hentry]
  refine le_trans ?_ (hall k)
  rw [Matrix.linfty_opNorm_def]
  have h1 : ‖(A ^ k) i j‖₊ ≤ ∑ j, ‖(A ^ k) i j‖₊ :=
    Finset.single_le_sum (f := fun j => ‖(A ^ k) i j‖₊) (fun _ _ => by positivity)
      (Finset.mem_univ j)
  have h2 : ∑ j, ‖(A ^ k) i j‖₊ ≤ Finset.univ.sup fun i => ∑ j, ‖(A ^ k) i j‖₊ :=
    Finset.le_sup (f := fun i => ∑ j, ‖(A ^ k) i j‖₊) (Finset.mem_univ i)
  have := h1.trans h2
  rw [← coe_nnnorm]
  exact_mod_cast this

/-- Galí (2015), p. 174: A matrix acting on a vector of random variables: `(M a)_i = ∑_j M_{ij}
a_j`. -/
def rvMul {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a : Fin m → Ω → ℝ) :
    Fin n → Ω → ℝ :=
  fun i => ∑ j, M i j • a j

/-- Galí (2015), p. 174 (tool): matrices act on vectors of random variables compatibly with
multiplication. -/
theorem rvMul_rvMul {Ω : Type*} {n m l : ℕ} (M : Matrix (Fin n) (Fin m) ℝ)
    (N : Matrix (Fin m) (Fin l) ℝ) (a : Fin l → Ω → ℝ) :
    rvMul M (rvMul N a) = rvMul (M * N) a := by
  funext i
  simp only [rvMul, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

/-- Galí (2015), p. 174 (tool): additivity of the action. -/
theorem rvMul_add {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a b : Fin m → Ω → ℝ) :
    rvMul M (a + b) = rvMul M a + rvMul M b := by
  funext i
  simp only [rvMul, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- Galí (2015), p. 174 (tool): the action respects subtraction. -/
theorem rvMul_sub {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a b : Fin m → Ω → ℝ) :
    rvMul M (a - b) = rvMul M a - rvMul M b := by
  funext i
  simp only [rvMul, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

/-- Galí (2015), p. 174 (tool): the identity matrix acts trivially. -/
theorem rvMul_one {Ω : Type*} {n : ℕ} (a : Fin n → Ω → ℝ) : rvMul 1 a = a := by
  funext i
  simp [rvMul, Matrix.one_apply]

/-- Galí (2015), p. 174 (tool): the action on the zero vector. -/
theorem rvMul_zero {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) :
    rvMul M (0 : Fin m → Ω → ℝ) = 0 := by
  funext i
  simp [rvMul]

/-- Galí (2015), p. 174 (tool): the action, pointwise. -/
theorem rvMul_apply {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a : Fin m → Ω → ℝ)
    (i : Fin n) (ω : Ω) : rvMul M a i ω = ∑ j, M i j * a j ω := by
  simp [rvMul, Finset.sum_apply]

namespace Fwd

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), p. 174 (tool): `E_t` commutes with constant matrices. -/
theorem E_rvMul {n m : ℕ} (t : ℕ) (M : Matrix (Fin n) (Fin m) ℝ) (a : Fin m → Ω → ℝ)
    (i : Fin n) : 𝔼.E t (rvMul M a i) = rvMul M (fun j => 𝔼.E t (a j)) i := by
  simp only [rvMul, map_sum, map_smul]

/-- Galí (2015), p. 174: A vector process solves the forward system `s_t = K E_t s_{t+1} + w_t`. -/
def FSolves {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (w s : ℕ → Fin n → Ω → ℝ) : Prop :=
  ∀ t, s t = rvMul K (fun j => 𝔼.E t (s (t + 1) j)) + w t

/-- Galí (2015), p. 174: A vector process is adapted. -/
def VAdapted {n : ℕ} (s : ℕ → Fin n → Ω → ℝ) : Prop := ∀ t i, 𝔼.E t (s t i) = s t i

/-- Galí (2015), p. 174: A vector process is bounded. -/
def VBounded {n : ℕ} (s : ℕ → Fin n → Ω → ℝ) : Prop := ∃ M, ∀ t i ω, |s t i ω| ≤ M

/-- Galí (2015), p. 174: Iterating a homogeneous forward system: `d_t = Kᵏ E_t d_{t+k}`. -/
theorem fsolves_iterate {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ} {d : ℕ → Fin n → Ω → ℝ}
    (hd : FSolves 𝔼 K 0 d) (had : VAdapted 𝔼 d) (t k : ℕ) :
    d t = rvMul (K ^ k) (fun j => 𝔼.E t (d (t + k) j)) := by
  induction k with
  | zero =>
    funext i
    simp only [pow_zero, add_zero, rvMul_one, had t i]
  | succ k ih =>
    rw [ih]
    have h := hd (t + k)
    simp only [Pi.zero_apply, add_zero] at h
    have : (fun j => 𝔼.E t (d (t + k) j)) =
        rvMul K (fun j => 𝔼.E t (d (t + (k + 1)) j)) := by
      funext j
      rw [h, E_rvMul 𝔼]
      congr 1
      funext l
      rw [𝔼.tower (Nat.le_add_right t k), ← add_assoc]
    rw [this, rvMul_rvMul, ← pow_succ]

/-- Galí (2015), p. 174: Bound for `Kᵏ` acting on a bounded vector. -/
theorem abs_rvMul_pow_le {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ} {Cb ρ : ℝ}
    (hK : ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k) (k : ℕ) {a : Fin n → Ω → ℝ} {M : ℝ}
    (ha : ∀ j ω, |a j ω| ≤ M) (i : Fin n) (ω : Ω) :
    |rvMul (K ^ k) a i ω| ≤ n * (Cb * ρ ^ k * M) := by
  rw [rvMul_apply]
  have hM : 0 ≤ M := (abs_nonneg _).trans (ha i ω)
  calc |∑ j, (K ^ k) i j * a j ω| ≤ ∑ j, |(K ^ k) i j * a j ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, Cb * ρ ^ k * M := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hK k i j) (ha j ω) (abs_nonneg _)
          ((abs_nonneg _).trans (hK k i j))
    _ = n * (Cb * ρ ^ k * M) := by simp

/-- Galí (2015), p. 174, fn. 1 (Blanchard–Kahn): if the powers of `K` decay geometrically, the
forward system `s_t = K E_t s_{t+1} + w_t` has at most one bounded adapted solution. -/
theorem fsolves_unique {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ} {Cb ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hK : ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k) {w x y : ℕ → Fin n → Ω → ℝ}
    (hx : FSolves 𝔼 K w x) (hy : FSolves 𝔼 K w y) (hax : VAdapted 𝔼 x)
    (hay : VAdapted 𝔼 y) (hbx : VBounded x) (hby : VBounded y) : x = y := by
  obtain ⟨M₁, hM₁⟩ := hbx
  obtain ⟨M₂, hM₂⟩ := hby
  set d : ℕ → Fin n → Ω → ℝ := fun t => x t - y t with hd_def
  have hd : FSolves 𝔼 K 0 d := by
    intro t
    simp only [hd_def, Pi.zero_apply, add_zero, Pi.sub_apply, map_sub]
    rw [hx t, hy t]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, rvMul, smul_sub, Finset.sum_sub_distrib]
    abel
  have had : VAdapted 𝔼 d := by
    intro t i
    simp only [hd_def, Pi.sub_apply, map_sub, hax t i, hay t i]
  have hdb : ∀ t i ω, |d t i ω| ≤ M₁ + M₂ := fun t i ω => by
    simp only [hd_def, Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hM₁ t i ω) (hM₂ t i ω))
  have hzero : d = 0 := by
    funext t i ω
    have hle : ∀ k, |d t i ω| ≤ n * (Cb * ρ ^ k * (M₁ + M₂)) := by
      intro k
      rw [fsolves_iterate 𝔼 hd had t k]
      exact abs_rvMul_pow_le hK k (fun j ω => 𝔼.abs_E_le (hdb (t + k) j) t ω) i ω
    have hlim : Tendsto (fun k : ℕ => (n : ℝ) * (Cb * ρ ^ k * (M₁ + M₂))) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul Cb).mul_const
        (M₁ + M₂)
      simpa using this.const_mul (n : ℝ)
    have h0 : |d t i ω| ≤ 0 := ge_of_tendsto' hlim hle
    simpa using h0
  funext t i ω
  have := congrFun (congrFun (congrFun hzero t) i) ω
  simpa [hd_def, sub_eq_zero] using this

/-- Galí (2015), p. 174, fn. 1 (Blanchard–Kahn): if the powers of `K` decay geometrically, the
forward series `s_t = ∑_{k ≥ 0} Kᵏ E_t w_{t+k}` is a bounded adapted solution of
`s_t = K E_t s_{t+1} + w_t` for bounded adapted forcing `w`. -/
theorem fsolves_exists {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ} {Cb ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hK : ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k)
    {w : ℕ → Fin n → Ω → ℝ} {Mw : ℝ} (hw : ∀ t i ω, |w t i ω| ≤ Mw) (haw : VAdapted 𝔼 w) :
    ∃ s, FSolves 𝔼 K w s ∧ VAdapted 𝔼 s ∧ VBounded s := by
  set Mb : ℝ := n * Cb * Mw with hMb
  set B : ℕ → ℕ → Fin n → Ω → ℝ := fun k t => rvMul (K ^ k) (fun j => 𝔼.E t (w (t + k) j))
    with hB
  have hT : ∀ k t t' i ω, |rvMul (K ^ k) (fun j => 𝔼.E t (w t' j)) i ω| ≤ ρ ^ k * Mb := by
    intro k t t' i ω
    have := abs_rvMul_pow_le hK k (fun j ω => 𝔼.abs_E_le (hw t' j) t ω) i ω
    calc _ ≤ n * (Cb * ρ ^ k * Mw) := this
      _ = ρ ^ k * Mb := by rw [hMb]; ring
  have hTs : ∀ t t' : ℕ → ℕ, ∀ i ω,
      Summable fun k => rvMul (K ^ k) (fun j => 𝔼.E (t k) (w (t' k) j)) i ω := fun t t' i ω =>
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hρ0 hρ1).mul_right Mb)
      (fun k => by rw [Real.norm_eq_abs]; exact hT k (t k) (t' k) i ω)
  have hBb : ∀ k t i ω, |B k t i ω| ≤ ρ ^ k * Mb := fun k t i ω => hT k t (t + k) i ω
  have hsum : ∀ t i ω, Summable fun k => B k t i ω := fun t i ω =>
    hTs (fun _ => t) (fun k => t + k) i ω
  set s : ℕ → Fin n → Ω → ℝ := fun t i ω => ∑' k, B k t i ω with hs
  have hEB : ∀ k t i, 𝔼.E t (B k (t + 1) i) =
      rvMul (K ^ k) (fun j => 𝔼.E t (w (t + 1 + k) j)) i := by
    intro k t i
    simp only [hB, E_rvMul 𝔼, 𝔼.tower (Nat.le_succ t)]
  have hEs : ∀ t i ω, 𝔼.E t (s (t + 1) i) ω =
      ∑' k, rvMul (K ^ k) (fun j => 𝔼.E t (w (t + 1 + k) j)) i ω := by
    intro t i ω
    have := 𝔼.E_tsum hρ0 hρ1 (f := fun k => B k (t + 1) i) (fun k ω => hBb k (t + 1) i ω) t ω
    rw [show s (t + 1) i = fun ω' => ∑' k, B k (t + 1) i ω' from rfl, this]
    exact tsum_congr fun k => by rw [hEB]
  refine ⟨s, ?_, ?_, ?_⟩
  · intro t
    funext i ω
    have hB0 : B 0 t i ω = w t i ω := by
      simp only [hB, pow_zero, add_zero, rvMul_one, haw t i]
    have hshift : ∀ k, B (k + 1) t i ω =
        ∑ l, K i l * rvMul (K ^ k) (fun j => 𝔼.E t (w (t + 1 + k) j)) l ω := by
      intro k
      simp only [hB]
      rw [← rvMul_apply, rvMul_rvMul, ← pow_succ', show t + (k + 1) = t + 1 + k by omega]
    have hR : (rvMul K (fun j => 𝔼.E t (s (t + 1) j)) + w t) i ω =
        (∑' k, B (k + 1) t i ω) + w t i ω := by
      rw [Pi.add_apply, Pi.add_apply, rvMul_apply]
      congr 1
      simp only [hEs, ← tsum_mul_left]
      rw [← Summable.tsum_finsetSum (fun l _ => (hTs (fun _ => t) (fun k => t + 1 + k) l ω).mul_left
        (K i l))]
      exact tsum_congr fun k => (hshift k).symm
    rw [hR, show s t i ω = ∑' k, B k t i ω from rfl, (hsum t i ω).tsum_eq_zero_add, hB0]
    ring
  · intro t i
    funext ω
    have := 𝔼.E_tsum hρ0 hρ1 (f := fun k => B k t i) (fun k ω => hBb k t i ω) t ω
    rw [show s t i = fun ω' => ∑' k, B k t i ω' from rfl, this]
    refine tsum_congr fun k => ?_
    simp only [hB, E_rvMul 𝔼, 𝔼.E_E_self]
  · refine ⟨Mb / (1 - ρ), fun t i ω => ?_⟩
    have hg : HasSum (fun k : ℕ => ρ ^ k * Mb) (Mb / (1 - ρ)) := by
      have := (hasSum_geometric_of_lt_one hρ0 hρ1).mul_right Mb
      rwa [← div_eq_inv_mul] at this
    have := tsum_of_norm_bounded hg (f := fun k => B k t i ω)
      (fun k => by rw [Real.norm_eq_abs]; exact hBb k t i ω)
    rw [Real.norm_eq_abs] at this
    exact this

end Fwd

namespace Par

/-- Galí (2015), eq. (24), p. 173: the matrix `A₀ʷ`. -/
def A0 (P : Par) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![P.σ + P.φy, P.φp, P.φw, 0; -P.κp, 1, 0, 0; -P.κw, 0, 1, 0; 0, -1, 1, 1]

/-- Galí (2015), eq. (24), p. 173: the matrix `A₁ʷ`. -/
def A1 (P : Par) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![P.σ, 1, 0, 0; 0, P.β, 0, P.lamP; 0, 0, P.β, -P.lamW; 0, 0, 0, 1]

/-- Galí (2015), p. 174: `det(A₀ʷ − z A₁ʷ) = −q(z)` for complex `z`. -/
theorem det_A0_sub_A1 (P : Par) (z : ℂ) :
    (P.A0.map Complex.ofReal - z • P.A1.map Complex.ofReal).det = -(P.qC.eval z) := by
  rw [eval_qC]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, A0, A1, c0, c1, c2, c3, c4]
  ring

/-- Galí (2015), p. 174: `det(A₀ʷ − r A₁ʷ) = −q(r)` for real `r`. -/
theorem det_A0_sub_A1_real (P : Par) (r : ℝ) : (P.A0 - r • P.A1).det = -(P.qr r) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, A0, A1, qr, c0, c1, c2, c3,
    c4]
  ring

end Par

/-- Galí (2015), eq. (24), p. 173: the matrix `B₀ʷ`. -/
def B0 : Matrix (Fin 4) (Fin 2) ℝ := !![1, 0; 0, 0; 0, 0; 0, 1]

namespace Par

/-- Galí (2015), p. 174: `D(r) = (r − 1)(1 − β r) + (λ_p + λ_w) r`. -/
def Dr (P : Par) (r : ℝ) : ℝ := -P.β * r ^ 2 + (1 + P.β + (P.lamP + P.lamW)) * r - 1

/-- Galí (2015), p. 174: `Br(r) = (σ + φ_y − σ r)(1 − β r) + (φ_p − r) κ_p + φ_w κ_w`. -/
def Brr (P : Par) (r : ℝ) : ℝ :=
  P.σ * P.β * r ^ 2 - (P.σ + P.β * (P.σ + P.φy) + P.κp) * r
    + (P.σ + P.φy + P.φp * P.κp + P.φw * P.κw)

/-- Galí (2015), p. 174: `H(r) = (φ_p − r) λ_p − φ_w λ_w`. -/
def Hr (P : Par) (r : ℝ) : ℝ := -P.lamP * r + (P.φp * P.lamP - P.φw * P.lamW)

/-- Galí (2015), p. 174: The factorisation `q(r) = Br(r) D(r) + r (κ_w − κ_p) H(r)`. -/
theorem qr_factor (P : Par) (r : ℝ) :
    P.qr r = P.Brr r * P.Dr r + r * (P.κw - P.κp) * P.Hr r := by
  simp only [qr, Brr, Dr, Hr, c0, c1, c2, c3, c4]; ring

/-- Galí (2015), p. 174: the derivative of the factorisation `q = Br D + r (κ_w − κ_p) H`. -/
theorem dqr_factor (P : Par) (r : ℝ) :
    P.dqr r = (2 * P.σ * P.β * r - (P.σ + P.β * (P.σ + P.φy) + P.κp)) * P.Dr r
      + P.Brr r * (-2 * P.β * r + (1 + P.β + (P.lamP + P.lamW)))
      + (P.κw - P.κp) * (P.Hr r - P.lamP * r) := by
  simp only [dqr, Brr, Dr, Hr, c1, c2, c3, c4]; ring

/-- Galí (2015), p. 174: The eigen-equations `(A₀ʷ − μ A₁ʷ) (g₀, g₁, g₂, 1)ᵀ = 0`: the stable
mode, normalised on
the predetermined real wage gap. -/
def StableVec (P : Par) (μ : ℝ) (g : Fin 3 → ℝ) : Prop :=
  (P.σ + P.φy) * g 0 + P.φp * g 1 + P.φw * g 2 - μ * (P.σ * g 0 + g 1) = 0 ∧
  -P.κp * g 0 + g 1 - μ * (P.β * g 1 + P.lamP) = 0 ∧
  -P.κw * g 0 + g 2 - μ * (P.β * g 2 - P.lamW) = 0 ∧
  -g 1 + g 2 + 1 - μ = 0

/-- Galí (2015), p. 174: Normalising an eigenvector `v` of `A₀ʷ − μ A₁ʷ` with `v₃ ≠ 0`. -/
theorem stableVec_of_hom (P : Par) {μ v0 v1 v2 v3 : ℝ} (hv3 : v3 ≠ 0)
    (h1 : (P.σ + P.φy) * v0 + P.φp * v1 + P.φw * v2 - μ * (P.σ * v0 + v1) = 0)
    (h2 : -P.κp * v0 + v1 - μ * (P.β * v1 + P.lamP * v3) = 0)
    (h3 : -P.κw * v0 + v2 - μ * (P.β * v2 - P.lamW * v3) = 0)
    (h4 : -v1 + v2 + v3 - μ * v3 = 0) : P.StableVec μ ![v0 / v3, v1 / v3, v2 / v3] := by
  have hinv : v3 * v3⁻¹ = 1 := mul_inv_cancel₀ hv3
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, div_eq_mul_inv]
  · linear_combination v3⁻¹ * h1
  · linear_combination v3⁻¹ * h2 + μ * P.lamP * hinv
  · linear_combination v3⁻¹ * h3 - μ * P.lamW * hinv
  · linear_combination v3⁻¹ * h4 - (1 - μ) * hinv

/-- Galí (2015), p. 174: the stable root `μ` has an eigenvector whose real-wage-gap component
is nonzero. -/
theorem exists_stableVec {P : Par} (hP : P.Adm) {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hq : P.qr μ = 0) (hd : P.dqr μ ≠ 0)
    (huniq : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → P.qC.eval ζ = 0 → ζ = μ) : ∃ g, P.StableVec μ g := by
  obtain ⟨hb0, hb1, -, -, -, hlp, hlw, -⟩ := hP
  have hb : 0 < 1 - P.β * μ := by nlinarith
  have hb' : (1 - P.β * μ) ≠ 0 := hb.ne'
  rw [qr_factor] at hq
  by_cases hBr : P.Brr μ = 0
  · -- then `κ_w ≠ κ_p`, and the first eigenvector field works
    have hk : P.κw - P.κp ≠ 0 := by
      intro hk
      obtain ⟨μD, ⟨hD0, hD1⟩, hDμ⟩ := intermediate_value_Ioo (zero_le_one (α := ℝ))
        (show Continuous P.Dr by unfold Dr; fun_prop).continuousOn
        (show (0 : ℝ) ∈ Set.Ioo (P.Dr 0) (P.Dr 1) by
          simp only [Dr, Set.mem_Ioo]; constructor <;> nlinarith)
      have hqD : P.qr μD = 0 := by rw [qr_factor, hDμ, hk]; ring
      have hμD : (μD : ℂ) = μ := huniq μD (by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD0]; exact hD1.le)
        (by rw [eval_qC_ofReal, hqD, Complex.ofReal_zero])
      have hμD' : μD = μ := by exact_mod_cast hμD
      subst hμD'
      exact hd (by rw [dqr_factor, hDμ, hBr, hk]; ring)
    refine ⟨_, P.stableVec_of_hom (v0 := P.Dr μ * (1 - P.β * μ))
      (v1 := P.κp * P.Dr μ + P.lamP * μ * (P.κw - P.κp))
      (v2 := P.κw * P.Dr μ - P.lamW * μ * (P.κw - P.κp)) (mul_ne_zero hk hb') ?_ ?_ ?_ ?_⟩
    · simp only [Brr, Dr, Hr] at hq ⊢
      linear_combination hq
    · ring
    · ring
    · simp only [Dr]; ring
  · refine ⟨_, P.stableVec_of_hom (v0 := -μ * P.Hr μ * (1 - P.β * μ))
      (v1 := -P.κp * μ * P.Hr μ + P.lamP * μ * P.Brr μ)
      (v2 := -P.κw * μ * P.Hr μ - P.lamW * μ * P.Brr μ) (mul_ne_zero hBr hb') ?_ ?_ ?_ ?_⟩
    · simp only [Brr, Hr]; ring
    · ring
    · ring
    · simp only [Dr, Hr, Brr] at hq ⊢
      linear_combination -hq

end Par

namespace Par

/-- Galí (2015), p. 174: The matrix acting on `(ẑ_t, n_t)` after quasi-differencing by the stable
mode:
the first three columns of `A₀ʷ` and `−A₁ʷ v`, `v = (g, 1)`. -/
def Cm (P : Par) (g : Fin 3 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![P.σ + P.φy, P.φp, P.φw, -(P.σ * g 0 + g 1); -P.κp, 1, 0, -(P.β * g 1 + P.lamP);
    -P.κw, 0, 1, -(P.β * g 2 - P.lamW); 0, -1, 1, -1]

/-- Galí (2015), p. 174: The first three columns of `A₁ʷ` (and a zero column). -/
def Dm (P : Par) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![P.σ, 1, 0, 0; 0, P.β, 0, 0; 0, 0, P.β, 0; 0, 0, 0, 0]

/-- Galí (2015), p. 174: The change of basis `[e₀ e₁ e₂ v]`. -/
def Vm (g : Fin 3 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, g 0; 0, 1, 0, g 1; 0, 0, 1, g 2; 0, 0, 0, 1]

/-- Galí (2015), p. 174: `(A₀ʷ − z A₁ʷ) V = (C − z D) diag(1, 1, 1, z − μ)`, whence
`det(C − z D) (z − μ) = −q(z)`. -/
theorem det_Cm_sub_mul {P : Par} {μ : ℝ} {g : Fin 3 → ℝ} (hg : P.StableVec μ g) (z : ℂ) :
    ((P.Cm g).map Complex.ofReal - z • P.Dm.map Complex.ofReal).det * (z - μ) =
      -(P.qC.eval z) := by
  obtain ⟨e1, e2, e3, e4⟩ := hg
  have c1 : ((P.σ : ℂ) + P.φy) * g 0 + P.φp * g 1 + P.φw * g 2 - μ * (P.σ * g 0 + g 1) = 0 := by
    exact_mod_cast e1
  have c2 : -(P.κp : ℂ) * g 0 + g 1 - μ * (P.β * g 1 + P.lamP) = 0 := by exact_mod_cast e2
  have c3 : -(P.κw : ℂ) * g 0 + g 2 - μ * (P.β * g 2 - P.lamW) = 0 := by exact_mod_cast e3
  have c4 : -(g 1 : ℂ) + g 2 + 1 - μ = 0 := by exact_mod_cast e4
  have hmat : (P.A0.map Complex.ofReal - z • P.A1.map Complex.ofReal) * (Vm g).map Complex.ofReal =
      ((P.Cm g).map Complex.ofReal - z • P.Dm.map Complex.ofReal) *
        Matrix.diagonal ![1, 1, 1, z - μ] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, A0, A1, Cm, Dm, Vm, Matrix.diagonal]
    · linear_combination c1
    · linear_combination c2
    · linear_combination c3
    · linear_combination c4
  have hV : ((Vm g).map Complex.ofReal).det = 1 := by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, Vm]
  have hd := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, hV, mul_one, det_A0_sub_A1, Matrix.det_diagonal,
    Fin.prod_univ_four] at hd
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, one_mul] at hd
  exact hd.symm

/-- Galí (2015), p. 174: The cubic `r(z) = q(z)/(z − μ)` (synthetic division). -/
noncomputable def rr (P : Par) (μ : ℝ) (z : ℂ) : ℂ :=
  P.c4 * z ^ 3 + (P.c3 + μ * P.c4) * z ^ 2 + (P.c2 + μ * (P.c3 + μ * P.c4)) * z
    + (P.c1 + μ * (P.c2 + μ * (P.c3 + μ * P.c4)))

/-- Galí (2015), p. 174: `q(z) = (z − μ) r(z)` when `q(μ) = 0`. -/
theorem qC_eq_mul_rr (P : Par) {μ : ℝ} (hq : P.qr μ = 0) (z : ℂ) :
    P.qC.eval z = (z - μ) * P.rr μ z := by
  have hq' : (P.qr μ : ℂ) = 0 := by rw [hq, Complex.ofReal_zero]
  simp only [qr] at hq'
  push_cast at hq'
  rw [eval_qC, rr]
  linear_combination hq'

/-- Galí (2015), p. 174: `r(μ) = q′(μ)`. -/
theorem rr_self (P : Par) (μ : ℝ) : P.rr μ μ = P.dqr μ := by
  simp only [rr, dqr]; push_cast; ring

/-- Galí (2015), p. 174: `r` is continuous. -/
theorem continuous_rr (P : Par) (μ : ℝ) : Continuous (P.rr μ) := by
  unfold rr; fun_prop

/-- Galí (2015), p. 174: `det(C − z D) = −r(z)` for every complex `z`. -/
theorem det_Cm_sub {P : Par} {μ : ℝ} {g : Fin 3 → ℝ} (hg : P.StableVec μ g) (hq : P.qr μ = 0)
    (z : ℂ) : ((P.Cm g).map Complex.ofReal - z • P.Dm.map Complex.ofReal).det = -P.rr μ z := by
  have hcont : Continuous fun z : ℂ =>
      ((P.Cm g).map Complex.ofReal - z • P.Dm.map Complex.ofReal).det :=
    Continuous.matrix_det (continuous_const.sub (continuous_id.smul continuous_const))
  have heq := Continuous.ext_on (dense_compl_singleton (μ : ℂ)) hcont
    (continuous_rr P μ).neg (fun z hz => by
      have hz' : z - μ ≠ 0 := sub_ne_zero.mpr hz
      have h := det_Cm_sub_mul hg z
      rw [qC_eq_mul_rr P hq] at h
      apply mul_right_cancel₀ hz'
      rw [h, Pi.neg_apply]; ring)
  exact congrFun heq z

/-- Galí (2015), p. 174: `r` has no root in the closed unit disc. -/
theorem rr_ne_zero {P : Par} {μ : ℝ} (hq : P.qr μ = 0) (hd : P.dqr μ ≠ 0)
    (huniq : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → P.qC.eval ζ = 0 → ζ = μ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    P.rr μ z ≠ 0 := by
  intro h0
  have hzμ : z = μ := huniq z hz (by rw [qC_eq_mul_rr P hq, h0, mul_zero])
  rw [hzμ, rr_self] at h0
  exact hd (by exact_mod_cast h0)

/-- Galí (2015), p. 174: The forward matrix `K = C⁻¹ D` of the quasi-differenced system. -/
noncomputable def Km (P : Par) (g : Fin 3 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ := (P.Cm g)⁻¹ * P.Dm

/-- Galí (2015), p. 174: The forcing matrix `F = C⁻¹ B₀ʷ`. -/
noncomputable def Fm (P : Par) (g : Fin 3 → ℝ) : Matrix (Fin 4) (Fin 2) ℝ := (P.Cm g)⁻¹ * B0

/-- Galí (2015), p. 174: the quasi-differenced system is well defined, `det C ≠ 0`. -/
theorem det_Cm_ne_zero {P : Par} {μ : ℝ} {g : Fin 3 → ℝ} (hg : P.StableVec μ g)
    (hq : P.qr μ = 0) (hd : P.dqr μ ≠ 0)
    (huniq : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → P.qC.eval ζ = 0 → ζ = μ) : (P.Cm g).det ≠ 0 := by
  intro h0
  have h := det_Cm_sub hg hq 0
  rw [zero_smul, sub_zero] at h
  have hc : ((P.Cm g).map Complex.ofReal).det = ((P.Cm g).det : ℂ) :=
    (RingHom.map_det Complex.ofRealHom (P.Cm g)).symm
  rw [hc, h0, Complex.ofReal_zero] at h
  exact rr_ne_zero hq hd huniq (z := 0) (by simp) (neg_eq_zero.mp h.symm)

/-- Galí (2015), p. 174: every eigenvalue of `K = C⁻¹ D` lies in the open unit disc. -/
theorem Km_eigen {P : Par} {μ : ℝ} {g : Fin 3 → ℝ} (hg : P.StableVec μ g)
    (hq : P.qr μ = 0) (hd : P.dqr μ ≠ 0)
    (huniq : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → P.qC.eval ζ = 0 → ζ = μ) (w : ℂ)
    (hw : (Matrix.scalar (Fin 4) w - (P.Km g).map Complex.ofReal).det = 0) : ‖w‖ < 1 := by
  by_cases hw0 : w = 0
  · rw [hw0, norm_zero]; exact zero_lt_one
  have hCu : IsUnit (P.Cm g).det := isUnit_iff_ne_zero.mpr (det_Cm_ne_zero hg hq hd huniq)
  have hCK : (P.Cm g).map Complex.ofReal * (P.Km g).map Complex.ofReal =
      P.Dm.map Complex.ofReal := by
    have e : ∀ M : Matrix (Fin 4) (Fin 4) ℝ, M.map Complex.ofReal = Complex.ofRealHom.mapMatrix M :=
      fun M => rfl
    rw [e, e, e, ← map_mul, Km, Matrix.mul_nonsing_inv_cancel_left _ _ hCu]
  have hprod : (P.Cm g).map Complex.ofReal * (Matrix.scalar (Fin 4) w - (P.Km g).map
      Complex.ofReal) = w • ((P.Cm g).map Complex.ofReal - w⁻¹ • P.Dm.map Complex.ofReal) := by
    rw [Matrix.mul_sub, hCK, smul_sub, smul_smul, mul_inv_cancel₀ hw0, one_smul,
      Matrix.scalar_apply]
    congr 1
    ext i j
    simp [Matrix.mul_diagonal, mul_comm]
  have hdet := congrArg Matrix.det hprod
  rw [Matrix.det_mul, hw, mul_zero, Matrix.det_smul, det_Cm_sub hg hq] at hdet
  have hr : P.rr μ w⁻¹ = 0 := by
    have : (w ^ Fintype.card (Fin 4)) * (-P.rr μ w⁻¹) = 0 := hdet.symm
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (pow_eq_zero_iff (by simp) |>.mp h) hw0
    · exact neg_eq_zero.mp h
  by_contra hge
  have hle : ‖w⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ (not_lt.mp hge)
  exact rr_ne_zero hq hd huniq hle hr

end Par

namespace Dyn

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (24), p. 173: `x_t = (ỹ_t, π^p_t, π^w_t, ω̃_{t−1})` solves
`A₀ʷ x_t = A₁ʷ E_t x_{t+1} + B₀ʷ u_t` with initial real wage gap `ω̃_{−1}`; all variables are
adapted and `ω̃_t` (the last entry of `x_{t+1}`) is predetermined, i.e. known at `t`. -/
def IsSol (P : Par) (u : ℕ → Fin 2 → Ω → ℝ) (ω0 : Ω → ℝ) (x : ℕ → Fin 4 → Ω → ℝ) : Prop :=
  (∀ t, rvMul P.A0 (x t) = rvMul P.A1 (fun j => 𝔼.E t (x (t + 1) j)) + rvMul B0 (u t)) ∧
    x 0 3 = ω0 ∧ Fwd.VAdapted 𝔼 x ∧ ∀ t, 𝔼.E t (x (t + 1) 3) = x (t + 1) 3

/-- Galí (2015), p. 174: the equilibrium is determinate when, for every bounded adapted forcing
`u` and every bounded initial real wage gap `ω̃_{−1}` known at date `0`, system (24) has exactly
one bounded solution. -/
def Determinate (P : Par) : Prop :=
  ∀ (u : ℕ → Fin 2 → Ω → ℝ) (ω0 : Ω → ℝ), Fwd.VBounded u → Fwd.VAdapted 𝔼 u →
    (∃ M, ∀ ω, |ω0 ω| ≤ M) → 𝔼.E 0 ω0 = ω0 → ∃! x, IsSol 𝔼 P u ω0 x ∧ Fwd.VBounded x

/-- Galí (2015), p. 174: Quasi-differencing by the stable mode: `ẑ_t = (ỹ, π^p, π^w)_t − g
ω̃_{t−1}` and
`n_t = ω̃_t − μ ω̃_{t−1}`. -/
def toS (μ : ℝ) (g : Fin 3 → ℝ) (x : ℕ → Fin 4 → Ω → ℝ) : ℕ → Fin 4 → Ω → ℝ :=
  fun t => ![x t 0 - g 0 • x t 3, x t 1 - g 1 • x t 3, x t 2 - g 2 • x t 3,
    x (t + 1) 3 - μ • x t 3]

/-- Galí (2015), p. 174: The key identity: `C s_t − D E_t s_{t+1} = A₀ʷ x_t − A₁ʷ E_t x_{t+1}`. -/
theorem transform {P : Par} {μ : ℝ} {g : Fin 3 → ℝ} (hg : P.StableVec μ g)
    (x : ℕ → Fin 4 → Ω → ℝ) (t : ℕ) (hpre : 𝔼.E t (x (t + 1) 3) = x (t + 1) 3) :
    rvMul (P.Cm g) (toS μ g x t) - rvMul P.Dm (fun j => 𝔼.E t (toS μ g x (t + 1) j)) =
      rvMul P.A0 (x t) - rvMul P.A1 (fun j => 𝔼.E t (x (t + 1) j)) := by
  obtain ⟨e1, e2, e3, e4⟩ := hg
  funext i ω
  fin_cases i <;>
    simp [rvMul_apply, Fin.sum_univ_four, Par.Cm, Par.Dm, Par.A0, Par.A1, toS, map_sub,
      map_smul, hpre]
  · linear_combination (-x t 3 ω) * e1
  · linear_combination (-x t 3 ω) * e2
  · linear_combination (-x t 3 ω) * e3
  · linear_combination (-x t 3 ω) * e4

/-- Galí (2015), p. 174: Equation (24) at date `t` is equivalent to the quasi-differenced forward
system
`s_t = K E_t s_{t+1} + F u_t`. -/
theorem eq_iff_fwd {P : Par} {μ : ℝ} {g : Fin 3 → ℝ} (hg : P.StableVec μ g)
    (hCu : IsUnit (P.Cm g).det) (x : ℕ → Fin 4 → Ω → ℝ) (u : ℕ → Fin 2 → Ω → ℝ) (t : ℕ)
    (hpre : 𝔼.E t (x (t + 1) 3) = x (t + 1) 3) :
    rvMul P.A0 (x t) = rvMul P.A1 (fun j => 𝔼.E t (x (t + 1) j)) + rvMul B0 (u t) ↔
      toS μ g x t = rvMul (P.Km g) (fun j => 𝔼.E t (toS μ g x (t + 1) j))
        + rvMul (P.Fm g) (u t) := by
  have htr := transform 𝔼 hg x t hpre
  constructor
  · intro h
    have hC : rvMul (P.Cm g) (toS μ g x t) =
        rvMul P.Dm (fun j => 𝔼.E t (toS μ g x (t + 1) j)) + rvMul B0 (u t) := by
      rw [← sub_eq_iff_eq_add', htr, h]; abel
    calc toS μ g x t = rvMul ((P.Cm g)⁻¹ * P.Cm g) (toS μ g x t) := by
          rw [Matrix.nonsing_inv_mul _ hCu, rvMul_one]
      _ = _ := by
          rw [← rvMul_rvMul, hC, rvMul_add, rvMul_rvMul, rvMul_rvMul]; rfl
  · intro h
    have hC : rvMul (P.Cm g) (toS μ g x t) =
        rvMul P.Dm (fun j => 𝔼.E t (toS μ g x (t + 1) j)) + rvMul B0 (u t) := by
      rw [h, rvMul_add, rvMul_rvMul, rvMul_rvMul, Par.Km, Par.Fm,
        Matrix.mul_nonsing_inv_cancel_left _ _ hCu, Matrix.mul_nonsing_inv_cancel_left _ _ hCu]
    rw [← sub_eq_iff_eq_add', ← htr, hC]; abel

/-- Galí (2015), p. 174: The quasi-differenced process of a solution is adapted. -/
theorem toS_adapted {μ : ℝ} {g : Fin 3 → ℝ} {x : ℕ → Fin 4 → Ω → ℝ} (hax : Fwd.VAdapted 𝔼 x)
    (hpre : ∀ t, 𝔼.E t (x (t + 1) 3) = x (t + 1) 3) : Fwd.VAdapted 𝔼 (toS μ g x) := by
  intro t i
  fin_cases i <;> simp [toS, map_sub, map_smul, hax t, hpre t]

/-- Galí (2015), p. 174: The quasi-differenced process of a bounded process is bounded. -/
theorem toS_bounded {μ : ℝ} {g : Fin 3 → ℝ} {x : ℕ → Fin 4 → Ω → ℝ} (hbx : Fwd.VBounded x) :
    Fwd.VBounded (toS μ g x) := by
  obtain ⟨M, hM⟩ := hbx
  refine ⟨M * (1 + |g 0| + |g 1| + |g 2| + |μ|), fun t i ω => ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM t 0 ω)
  have hb : ∀ (a : ℝ) (j : Fin 4) (s : ℕ), |x s j ω - a * x t 3 ω| ≤ M * (1 + |a|) := by
    intro a j s
    calc |x s j ω - a * x t 3 ω| ≤ |x s j ω| + |a| * |x t 3 ω| := by
          rw [← abs_mul]; exact abs_sub _ _
      _ ≤ M + |a| * M := add_le_add (hM s j ω) (mul_le_mul_of_nonneg_left (hM t 3 ω)
          (abs_nonneg a))
      _ = M * (1 + |a|) := by ring
  have hg0 := abs_nonneg (g 0)
  have hg1 := abs_nonneg (g 1)
  have hg2 := abs_nonneg (g 2)
  have hμ := abs_nonneg μ
  fin_cases i <;> simp only [toS, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  · exact (hb (g 0) 0 t).trans (by nlinarith)
  · exact (hb (g 1) 1 t).trans (by nlinarith)
  · exact (hb (g 2) 2 t).trans (by nlinarith)
  · exact (hb μ 3 (t + 1)).trans (by nlinarith)

/-- Galí (2015), p. 174: The predetermined real wage gap rebuilt from `ω̃_{−1}` and the
innovations `n_t`:
`ω̃_t = μ ω̃_{t−1} + n_t`. -/
def mseq (μ : ℝ) (ω0 : Ω → ℝ) (s : ℕ → Fin 4 → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => ω0
  | t + 1 => μ • mseq μ ω0 s t + s t 3

/-- Galí (2015), p. 174: The solution rebuilt from the quasi-differenced variables. -/
def ofS (g : Fin 3 → ℝ) (m : ℕ → Ω → ℝ) (s : ℕ → Fin 4 → Ω → ℝ) : ℕ → Fin 4 → Ω → ℝ :=
  fun t => ![s t 0 + g 0 • m t, s t 1 + g 1 • m t, s t 2 + g 2 • m t, m t]

/-- Galí (2015), p. 174 (existence): quasi-differencing the rebuilt solution returns `s`. -/
theorem toS_ofS (μ : ℝ) (g : Fin 3 → ℝ) (ω0 : Ω → ℝ) (s : ℕ → Fin 4 → Ω → ℝ) :
    toS μ g (ofS g (mseq μ ω0 s) s) = s := by
  funext t i
  fin_cases i <;> simp [toS, ofS, mseq]

/-- Galí (2015), p. 174 (existence): the rebuilt real wage gap is adapted. -/
theorem mseq_adapted {μ : ℝ} {ω0 : Ω → ℝ} {s : ℕ → Fin 4 → Ω → ℝ} (hω0 : 𝔼.E 0 ω0 = ω0)
    (has : Fwd.VAdapted 𝔼 s) (t : ℕ) : 𝔼.E t (mseq μ ω0 s t) = mseq μ ω0 s t := by
  induction t with
  | zero => exact hω0
  | succ t ih =>
    have h1 : 𝔼.E t (mseq μ ω0 s (t + 1)) = mseq μ ω0 s (t + 1) := by
      simp only [mseq, map_add, map_smul, ih, has t 3]
    rw [← h1, 𝔼.known (Nat.le_succ t)]

/-- Galí (2015), p. 174 (existence): the rebuilt real wage gap is bounded (`0 ≤ μ < 1`). -/
theorem mseq_bounded {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) {ω0 : Ω → ℝ} {M0 : ℝ}
    (hω : ∀ ω, |ω0 ω| ≤ M0) {s : ℕ → Fin 4 → Ω → ℝ} {Ms : ℝ}
    (hs : ∀ t i ω, |s t i ω| ≤ Ms) (t : ℕ) (ω : Ω) :
    |mseq μ ω0 s t ω| ≤ max M0 (Ms / (1 - μ)) := by
  induction t with
  | zero => exact (hω ω).trans (le_max_left _ _)
  | succ t ih =>
    simp only [mseq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1μ : 0 < 1 - μ := by linarith
    have hMs : Ms ≤ (1 - μ) * max M0 (Ms / (1 - μ)) := by
      have := le_max_right M0 (Ms / (1 - μ))
      rw [div_le_iff₀ h1μ] at this
      linarith
    calc |μ * mseq μ ω0 s t ω + s t 3 ω| ≤ μ * |mseq μ ω0 s t ω| + |s t 3 ω| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_nonneg hμ0]
      _ ≤ μ * max M0 (Ms / (1 - μ)) + Ms :=
          add_le_add (mul_le_mul_of_nonneg_left ih hμ0) (hs t 3 ω)
      _ ≤ max M0 (Ms / (1 - μ)) := by linarith

/-- **Galí (2015), p. 174, sufficiency**: under the sign conditions, if
`φ_p + φ_w + φ_y (1 − β)/Θ_y (1/λ_p + 1/λ_w) > 1` (equivalently `q(1) > 0`), system (24) has
exactly one bounded solution for every bounded adapted forcing and every bounded initial real
wage gap. -/
theorem determinate_of_pos {P : Par} (hP : P.Adm) (hΨ : 0 < P.Ψ) (h1 : 0 < P.qr 1) :
    Determinate 𝔼 P := by
  obtain ⟨μ, hμ0, hμ1, hq, hd, huniq⟩ := P.stable_root hP hΨ h1
  obtain ⟨g, hg⟩ := P.exists_stableVec hP hμ0 hμ1 hq hd huniq
  have hCu : IsUnit (P.Cm g).det := isUnit_iff_ne_zero.mpr (P.det_Cm_ne_zero hg hq hd huniq)
  obtain ⟨Cb, ρ, -, hρ0, hρ1, hK⟩ := pow_entry_bound (P.Km g) (P.Km_eigen hg hq hd huniq)
  intro u ω0 hbu hau hbω hω0
  obtain ⟨Mu, hMu⟩ := hbu
  obtain ⟨M0, hM0⟩ := hbω
  set w : ℕ → Fin 4 → Ω → ℝ := fun t => rvMul (P.Fm g) (u t) with hw_def
  have hwb : ∀ t i ω, |w t i ω| ≤ ∑ k, |P.Fm g i k| * Mu := by
    intro t i ω
    simp only [hw_def]
    rw [rvMul_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hMu t k ω) (abs_nonneg _)
  set Mw : ℝ := ∑ i, ∑ k, |P.Fm g i k| * Mu with hMw
  have hwb' : ∀ t i ω, |w t i ω| ≤ Mw := by
    intro t i ω
    refine (hwb t i ω).trans ?_
    have hMu0 : 0 ≤ Mu := (abs_nonneg _).trans (hMu t 0 ω)
    exact Finset.single_le_sum (f := fun i => ∑ k, |P.Fm g i k| * Mu)
      (fun i _ => Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) hMu0)
      (Finset.mem_univ i)
  have haw : Fwd.VAdapted 𝔼 w := by
    intro t i
    rw [hw_def]
    simp only [Fwd.E_rvMul 𝔼, hau t]
  obtain ⟨s, hs, has, ⟨Ms, hMs⟩⟩ := Fwd.fsolves_exists 𝔼 hρ0.le hρ1 hK hwb' haw
  set m := mseq μ ω0 s with hm
  have ham : ∀ t, 𝔼.E t (m t) = m t := mseq_adapted 𝔼 hω0 has
  have hpre : ∀ t, 𝔼.E t (ofS g m s (t + 1) 3) = ofS g m s (t + 1) 3 := by
    intro t
    simp only [ofS, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons, hm, mseq,
      map_add, map_smul, mseq_adapted 𝔼 hω0 has t, has t 3]
  refine ⟨ofS g m s, ⟨⟨fun t => ?_, ?_, ?_, hpre⟩, ?_⟩, ?_⟩
  · rw [eq_iff_fwd 𝔼 hg hCu _ u t (hpre t), toS_ofS]
    exact hs t
  · simp [ofS, hm, mseq]
  · intro t i
    fin_cases i <;> simp [ofS, map_add, map_smul, has t, ham t]
  · have hmb := mseq_bounded hμ0.le hμ1 hM0 hMs
    set Mm := max M0 (Ms / (1 - μ))
    refine ⟨Ms + (|g 0| + |g 1| + |g 2| + 1) * Mm, fun t i ω => ?_⟩
    have hmt := hmb t ω
    have hMm : 0 ≤ Mm := (abs_nonneg _).trans hmt
    have hg0 := abs_nonneg (g 0)
    have hg1 := abs_nonneg (g 1)
    have hg2 := abs_nonneg (g 2)
    have hMs0 : 0 ≤ Ms := (abs_nonneg _).trans (hMs t 0 ω)
    have hb : ∀ (a : ℝ) (j : Fin 4), |s t j ω + a * m t ω| ≤ Ms + |a| * Mm := by
      intro a j
      refine (abs_add_le _ _).trans (add_le_add (hMs t j ω) ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hmt (abs_nonneg a)
    fin_cases i <;> simp only [ofS, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    · exact (hb (g 0) 0).trans (by nlinarith)
    · exact (hb (g 1) 1).trans (by nlinarith)
    · exact (hb (g 2) 2).trans (by nlinarith)
    · exact hmt.trans (by nlinarith)
  · rintro y ⟨⟨hy, hy0, hay, hpy⟩, hby⟩
    have hsy : Fwd.FSolves 𝔼 (P.Km g) w (toS μ g y) := fun t =>
      (eq_iff_fwd 𝔼 hg hCu y u t (hpy t)).mp (hy t)
    have heq : toS μ g y = s := Fwd.fsolves_unique 𝔼 hρ0.le hρ1 hK hsy hs
      (toS_adapted 𝔼 hay hpy) has (toS_bounded hby) ⟨Ms, hMs⟩
    have h3 : ∀ t, y t 3 = m t := by
      intro t
      induction t with
      | zero => rw [hy0, hm, mseq]
      | succ t ih =>
        have := congrFun (congrFun heq t) 3
        simp only [toS, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons] at this
        rw [hm, mseq, ← hm, ← this, ih]
        abel
    funext t i
    have hc := congrFun (congrFun heq t) i
    fin_cases i <;> simp only [toS, ofS, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val] at hc ⊢
    · rw [← hc, h3 t]; abel
    · rw [← hc, h3 t]; abel
    · rw [← hc, h3 t]; abel
    · exact h3 t

end Dyn

namespace Par

/-- Galí (2015), eq. (24): `det A₀ʷ = −q(0) > 0`. -/
theorem det_A0 (P : Par) : P.A0.det = -P.c0 := by
  have h := P.det_A0_sub_A1_real 0
  rw [zero_smul, sub_zero, qr_zero] at h
  exact h

/-- Galí (2015), eq. (24): `det A₁ʷ = σ β²`. -/
theorem det_A1 (P : Par) : P.A1.det = P.σ * P.β ^ 2 := by
  rw [show P.σ * P.β ^ 2 = P.σ * (P.β * (P.β * 1)) by ring]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, A1]

/-- Galí (2015), p. 174: the derivative of `q` in coefficient form. -/
theorem eval_derivative_qC (P : Par) (z : ℂ) :
    P.qC.derivative.eval z = P.c1 + 2 * P.c2 * z + 3 * P.c3 * z ^ 2 + 4 * P.c4 * z ^ 3 := by
  simp [qC, qv, eval_derivative_quart]

end Par

namespace Dyn

open scoped Matrix

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), p. 174 (tool): a row combination `ℓᵀ M a = (ℓᵀ M) a`. -/
theorem sum_smul_rvMul {n m : ℕ} (ℓ : Fin n → ℝ) (M : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin m → Ω → ℝ) : ∑ i, ℓ i • rvMul M a i = ∑ j, (ℓ ᵥ* M) j • a j := by
  simp only [rvMul, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]

/-- Galí (2015), p. 174 (tool): the action on deterministic vectors. -/
theorem rvMul_const {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a : Fin m → ℝ) :
    rvMul M (fun j (_ : Ω) => a j) = fun i _ => (M *ᵥ a) i := by
  funext i ω
  simp [rvMul_apply, Matrix.mulVec, dotProduct]

/-- Galí (2015), p. 174 (multiplicity): a nonzero bounded deterministic solution of the
homogeneous system with `ω̃_{−1} = 0` gives two different bounded solutions of (24) for
`u = 0`, `ω̃_{−1} = 0`. -/
theorem multiple_solutions_of_mode [Nonempty Ω] {P : Par} {X : ℕ → Fin 4 → ℝ}
    (hX : ∀ t, P.A0 *ᵥ X t = P.A1 *ᵥ X (t + 1)) (h0 : X 0 3 = 0)
    (hb : ∃ M, ∀ t j, |X t j| ≤ M) (hne : X ≠ 0) :
    IsSol 𝔼 P 0 0 0 ∧ Fwd.VBounded (0 : ℕ → Fin 4 → Ω → ℝ) ∧
      IsSol 𝔼 P 0 0 (fun t j _ => X t j) ∧ Fwd.VBounded (fun t j (_ : Ω) => X t j) ∧
      (fun t j (_ : Ω) => X t j) ≠ 0 := by
  have hz : IsSol 𝔼 P 0 0 0 := by
    refine ⟨fun t => ?_, rfl, fun t i => by simp, fun t => by simp⟩
    funext i ω
    simp [rvMul_apply]
  have hc : IsSol 𝔼 P 0 0 (fun t j _ => X t j) := by
    refine ⟨fun t => ?_, ?_, fun t i => 𝔼.const t _, fun t => 𝔼.const t _⟩
    · have hE : (fun j => 𝔼.E t (fun _ : Ω => X (t + 1) j)) = fun j _ => X (t + 1) j :=
        funext fun j => 𝔼.const t _
      rw [hE, Pi.zero_apply, rvMul_zero, add_zero, rvMul_const, rvMul_const, hX t]
    · funext ω; simp [h0]
  obtain ⟨M, hM⟩ := hb
  refine ⟨hz, ⟨0, by simp⟩, hc, ⟨M, fun t j _ => hM t j⟩, fun h => hne ?_⟩
  funext t j
  have := congrFun (congrFun (congrFun h t) j) (Classical.arbitrary Ω)
  simpa using this

/-- Galí (2015), p. 174 (indeterminacy): such a mode rules out determinacy. -/
theorem not_determinate_of_mode [Nonempty Ω] {P : Par} {X : ℕ → Fin 4 → ℝ}
    (hX : ∀ t, P.A0 *ᵥ X t = P.A1 *ᵥ X (t + 1)) (h0 : X 0 3 = 0)
    (hb : ∃ M, ∀ t j, |X t j| ≤ M) (hne : X ≠ 0) : ¬ Determinate 𝔼 P := by
  intro hdet
  obtain ⟨x, -, huniq⟩ := hdet 0 0 ⟨0, by simp⟩ (by intro t i; simp) ⟨0, by simp⟩ (by simp)
  obtain ⟨hz, hzb, hc, hcb, hne'⟩ := multiple_solutions_of_mode 𝔼 hX h0 hb hne
  exact hne' ((huniq _ ⟨hc, hcb⟩).trans (huniq 0 ⟨hz, hzb⟩).symm)

/-- **Galí (2015), p. 174, the boundary**: if `φ_p + φ_w + φ_y (1 − β)/Θ_y (1/λ_p + 1/λ_w) = 1`
(`q(1) = 0`, a unit eigenvalue) the equilibrium is not determinate: for a suitable constant
forcing there is no bounded solution. -/
theorem not_determinate_of_eq [Nonempty Ω] {P : Par} (hP : P.Adm) (h1 : P.qr 1 = 0) :
    ¬ Determinate 𝔼 P := by
  obtain ⟨hb0, hb1, -⟩ := hP
  have hdet : (P.A0 - (1 : ℝ) • P.A1).det = 0 := by rw [P.det_A0_sub_A1_real, h1, neg_zero]
  obtain ⟨ℓ, hℓ0, hℓ⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  have hℓA : ℓ ᵥ* P.A0 = ℓ ᵥ* P.A1 := by
    rw [one_smul, Matrix.vecMul_sub, sub_eq_zero] at hℓ; exact hℓ
  have hcol : ∀ j, (ℓ ᵥ* P.A0) j = (ℓ ᵥ* P.A1) j := fun j => congrFun hℓA j
  have h03 : ℓ 0 ^ 2 + ℓ 3 ^ 2 ≠ 0 := by
    intro hN
    have h0 : ℓ 0 = 0 := by nlinarith [sq_nonneg (ℓ 0), sq_nonneg (ℓ 3)]
    have h3 : ℓ 3 = 0 := by nlinarith [sq_nonneg (ℓ 0), sq_nonneg (ℓ 3)]
    have c1 := hcol 1
    have c2 := hcol 2
    simp only [Matrix.vecMul, dotProduct, Par.A0, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one, Fin.sum_univ_four, h0,
      zero_mul, mul_one, zero_add, Matrix.cons_val, mul_zero, add_zero, h3, mul_neg, neg_zero,
      Par.A1] at c1 c2
    have h1' : ℓ 1 = 0 := by
      have : ℓ 1 * (1 - P.β) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (by linarith)
    have h2' : ℓ 2 = 0 := by
      have : ℓ 2 * (1 - P.β) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (by linarith)
    apply hℓ0
    funext j
    fin_cases j <;> simp [h0, h3, h1', h2']
  set N := ℓ 0 ^ 2 + ℓ 3 ^ 2 with hN
  set u : ℕ → Fin 2 → Ω → ℝ := fun _ => ![fun _ => ℓ 0 / N, fun _ => ℓ 3 / N] with hu
  intro hdetm
  obtain ⟨x, ⟨⟨hx, -, hax, -⟩, ⟨Mx, hMx⟩⟩, -⟩ := hdetm u 0
    ⟨|ℓ 0 / N| + |ℓ 3 / N|, fun t i ω => by
      fin_cases i <;> simp [hu]⟩
    (fun t i => by fin_cases i <;> simp [hu, 𝔼.const]) ⟨0, by simp⟩ (by simp)
  set S : ℕ → Ω → ℝ := fun t => ∑ i, ℓ i • rvMul P.A1 (x t) i with hS
  have hSrec : ∀ t, S t = 𝔼.E t (S (t + 1)) + fun _ => 1 := by
    intro t
    have h := congrArg (fun v => ∑ i, ℓ i • v i) (hx t)
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib] at h
    rw [sum_smul_rvMul, hℓA, ← sum_smul_rvMul] at h
    have hB : ∑ i, ℓ i • rvMul B0 (u t) i = fun _ => 1 := by
      funext ω
      simp [rvMul_apply, Fin.sum_univ_four, Fin.sum_univ_two, B0, hu, Finset.sum_apply]
      field_simp
      linear_combination -hN
    rw [hB] at h
    change ∑ i, ℓ i • rvMul P.A1 (x t) i =
      𝔼.E t (∑ i, ℓ i • rvMul P.A1 (x (t + 1)) i) + fun _ => 1
    rw [h]
    congr 1
    simp only [map_sum, map_smul, Fwd.E_rvMul 𝔼]
  have hS0 : 𝔼.E 0 (S 0) = S 0 := by
    simp only [hS, map_sum, map_smul, Fwd.E_rvMul 𝔼, hax 0]
  have hE0 : ∀ t, 𝔼.E 0 (S t) = S 0 - fun _ => (t : ℝ) := by
    intro t
    induction t with
    | zero => rw [hS0]; funext ω; simp
    | succ t ih =>
      have h := congrArg (𝔼.E 0) (hSrec t)
      rw [map_add, 𝔼.tower (Nat.zero_le t), 𝔼.const] at h
      rw [ih] at h
      funext ω
      have := congrFun h ω
      simp only [Pi.sub_apply, Pi.add_apply] at this ⊢
      push_cast
      linarith
  set MS : ℝ := ∑ i, |ℓ i| * ∑ j, |P.A1 i j| * Mx with hMS
  have hSb : ∀ t ω, |S t ω| ≤ MS := by
    intro t ω
    simp only [hS, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rvMul_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hMx t j ω) (abs_nonneg _)
  obtain ⟨T, hT⟩ := exists_nat_gt (|S 0 (Classical.arbitrary Ω)| + MS)
  have h1' := 𝔼.abs_E_le (hSb T) 0 (Classical.arbitrary Ω)
  rw [hE0 T] at h1'
  simp only [Pi.sub_apply] at h1'
  have := abs_sub_abs_le_abs_sub (T : ℝ) (S 0 (Classical.arbitrary Ω))
  rw [abs_sub_comm] at h1'
  rw [abs_of_nonneg (Nat.cast_nonneg T)] at this
  linarith

/-- Galí (2015), p. 174 (tool): complexification of a real matrix as a ring map. -/
theorem map_ofReal_eq (M : Matrix (Fin 4) (Fin 4) ℝ) :
    M.map Complex.ofReal = Complex.ofRealHom.mapMatrix M := rfl

/-- Galí (2015), p. 174: if `q` has no root in the closed unit disc (all four eigenvalues of
`(A₀ʷ)⁻¹ A₁ʷ` inside the unit circle) there is no bounded solution with `u = 0` and
`ω̃_{−1} = 1` (non-existence). -/
theorem no_bounded_solution_of_no_root [Nonempty Ω] {P : Par} (hP : P.Adm)
    (hno : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → P.qC.eval ζ ≠ 0) (x : ℕ → Fin 4 → Ω → ℝ)
    (hsol : IsSol 𝔼 P 0 (fun _ => 1) x) (hbx : Fwd.VBounded x) : False := by
  obtain ⟨hx, hx0, hax, -⟩ := hsol
  have hA0u : IsUnit P.A0.det := by
    rw [P.det_A0]; exact isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (P.c0_neg hP).ne)
  have hfs : Fwd.FSolves 𝔼 (P.A0⁻¹ * P.A1) 0 x := by
    intro t
    have h := hx t
    rw [Pi.zero_apply, rvMul_zero, add_zero] at h
    rw [Pi.zero_apply, add_zero, ← rvMul_rvMul, ← h, rvMul_rvMul,
      Matrix.nonsing_inv_mul _ hA0u, rvMul_one]
  have heig : ∀ w : ℂ, (Matrix.scalar (Fin 4) w - (P.A0⁻¹ * P.A1).map Complex.ofReal).det = 0 →
      ‖w‖ < 1 := by
    intro w hw
    have hAA : P.A0.map Complex.ofReal * (P.A0⁻¹ * P.A1).map Complex.ofReal =
        P.A1.map Complex.ofReal := by
      rw [map_ofReal_eq, map_ofReal_eq, map_ofReal_eq, ← map_mul,
        Matrix.mul_nonsing_inv_cancel_left _ _ hA0u]
    have hprod : P.A0.map Complex.ofReal * (Matrix.scalar (Fin 4) w -
        (P.A0⁻¹ * P.A1).map Complex.ofReal) =
        w • P.A0.map Complex.ofReal - P.A1.map Complex.ofReal := by
      rw [Matrix.mul_sub, hAA, Matrix.scalar_apply]
      congr 1
      ext i j
      simp [Matrix.mul_diagonal, mul_comm]
    have hdet0 := congrArg Matrix.det hprod
    rw [Matrix.det_mul, hw, mul_zero] at hdet0
    have hA1c : (P.A1.map Complex.ofReal).det = ((P.σ * P.β ^ 2 : ℝ) : ℂ) := by
      rw [map_ofReal_eq, ← RingHom.map_det, P.det_A1]; rfl
    by_cases hw0 : w = 0
    · exfalso
      rw [hw0, zero_smul, zero_sub, Matrix.det_neg, hA1c] at hdet0
      obtain ⟨hb0, -, hs, -⟩ := hP
      simp only [Fintype.card_fin, ofReal_mul, ofReal_pow, zero_eq_mul, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, neg_eq_zero, one_ne_zero,
        mul_eq_zero, ofReal_eq_zero, false_or] at hdet0
      rcases hdet0 with h | h
      · exact hs.ne' h
      · exact hb0.ne' h
    have hsplit : w • P.A0.map Complex.ofReal - P.A1.map Complex.ofReal =
        w • (P.A0.map Complex.ofReal - w⁻¹ • P.A1.map Complex.ofReal) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hw0, one_smul]
    rw [hsplit, Matrix.det_smul, P.det_A0_sub_A1] at hdet0
    have hq : P.qC.eval w⁻¹ = 0 := by
      rcases mul_eq_zero.mp hdet0.symm with h | h
      · exact absurd (pow_eq_zero_iff (by simp) |>.mp h) hw0
      · exact neg_eq_zero.mp h
    by_contra hge
    exact hno w⁻¹ (by rw [norm_inv]; exact inv_le_one_of_one_le₀ (not_lt.mp hge)) hq
  obtain ⟨Cb, ρ, -, hρ0, hρ1, hK⟩ := pow_entry_bound _ heig
  have hz : Fwd.FSolves 𝔼 (P.A0⁻¹ * P.A1) 0 0 := by
    intro t; funext i ω; simp [rvMul_apply]
  have h := Fwd.fsolves_unique 𝔼 hρ0.le hρ1 hK hfs hz hax (by intro t i; simp) hbx ⟨0, by simp⟩
  have h03 := congrFun (congrFun (congrFun h 0) 3) (Classical.arbitrary Ω)
  rw [hx0] at h03
  simp at h03

/-- Galí (2015), p. 174: no root of `q` in the closed unit disc rules out determinacy. -/
theorem not_determinate_of_no_root [Nonempty Ω] {P : Par} (hP : P.Adm)
    (hno : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → P.qC.eval ζ ≠ 0) : ¬ Determinate 𝔼 P := by
  intro hdet
  obtain ⟨x, ⟨hsol, hbx⟩, -⟩ := hdet 0 (fun _ => 1) ⟨0, by simp⟩
    (by intro t i; simp) ⟨1, by simp⟩ (𝔼.const 0 1)
  exact no_bounded_solution_of_no_root 𝔼 hP hno x hsol hbx

/-- Galí (2015), p. 174: The roots of `q` in the closed unit disc, with multiplicity. -/
noncomputable def closedRoots (P : Par) : Multiset ℂ := P.qC.roots.filter (fun z => ‖z‖ ≤ 1)

/-- Galí (2015), p. 174: `q ≠ 0`. -/
theorem qC_ne_zero {P : Par} (hP : P.Adm) : P.qC ≠ 0 :=
  quart_ne_zero (by simp only [Par.qv, Matrix.cons_val]; exact_mod_cast (P.c4_neg hP).ne)

/-- Galí (2015), p. 174: membership in the roots of `q` in the closed unit disc. -/
theorem mem_closedRoots {P : Par} (hP : P.Adm) {ζ : ℂ} :
    ζ ∈ closedRoots P ↔ ‖ζ‖ ≤ 1 ∧ P.qC.eval ζ = 0 := by
  rw [closedRoots, Multiset.mem_filter, mem_roots (qC_ne_zero hP), IsRoot]
  exact and_comm

/-- Galí (2015), p. 174: The real synthetic-division cubic `s(t) = q(t)/(t − r)`. -/
def sr (P : Par) (r t : ℝ) : ℝ :=
  P.c4 * t ^ 3 + (P.c3 + r * P.c4) * t ^ 2 + (P.c2 + r * (P.c3 + r * P.c4)) * t
    + (P.c1 + r * (P.c2 + r * (P.c3 + r * P.c4)))

/-- Galí (2015), p. 174: synthetic division `q(t) = (t − r) s(t) + q(r)`. -/
theorem qr_eq_sr (P : Par) (r t : ℝ) : P.qr t = (t - r) * sr P r t + P.qr r := by
  simp only [Par.qr, sr]; ring

/-- Galí (2015), p. 174: `s(r) = q′(r)`. -/
theorem sr_self (P : Par) (r : ℝ) : sr P r r = P.dqr r := by
  simp only [sr, Par.dqr]; ring

/-- Galí (2015), p. 174: when `q(1) < 0`, the number of roots of `q` in the closed unit disc
cannot be one (it is even: complex roots pair up, and `q(−1) < 0`, `q(1) < 0` force an even
number of real roots in `(−1, 1)`). -/
theorem closedRoots_card_ne_one {P : Par} (hP : P.Adm) (h1 : P.qr 1 < 0) :
    (closedRoots P).card ≠ 1 := by
  intro hc
  obtain ⟨ζ0, hζ0⟩ := Multiset.card_eq_one.mp hc
  have huniq : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → P.qC.eval ζ = 0 → ζ = ζ0 := by
    intro ζ hζ h0
    have := (mem_closedRoots hP).mpr ⟨hζ, h0⟩
    rwa [hζ0, Multiset.mem_singleton] at this
  have hmem : ζ0 ∈ closedRoots P := by rw [hζ0]; exact Multiset.mem_singleton_self _
  obtain ⟨hn0, hq0⟩ := (mem_closedRoots hP).mp hmem
  -- `ζ0` is real
  have hconj : (starRingEnd ℂ) ζ0 = ζ0 := huniq _ (by rwa [Complex.norm_conj])
    (by rw [Par.eval_qC_conj, hq0, map_zero])
  set r := ζ0.re with hr
  have hζr : ζ0 = (r : ℂ) := (Complex.conj_eq_iff_re.mp hconj).symm
  have hqr : P.qr r = 0 := by
    have := hq0; rw [hζr, Par.eval_qC_ofReal] at this; exact_mod_cast this
  have hrn : |r| ≤ 1 := by
    have := hn0; rwa [hζr, Complex.norm_real, Real.norm_eq_abs] at this
  -- `r` is a simple root
  have hdr : P.dqr r ≠ 0 := by
    intro hd
    have hroot : P.qC.IsRoot ζ0 := hq0
    have hder : P.qC.derivative.IsRoot ζ0 := by
      rw [IsRoot, P.eval_derivative_qC, hζr]
      have : (P.dqr r : ℂ) = 0 := by rw [hd, Complex.ofReal_zero]
      simp only [Par.dqr] at this
      push_cast at this
      exact this
    have hm := (one_lt_rootMultiplicity_iff_isRoot (qC_ne_zero hP)).mpr ⟨hroot, hder⟩
    have hcnt : 2 ≤ (closedRoots P).count ζ0 := by
      rw [closedRoots, Multiset.count_filter_of_pos (p := fun z : ℂ => ‖z‖ ≤ 1) hn0,
        count_roots]
      omega
    have := Multiset.count_le_card ζ0 (closedRoots P)
    omega
  have hr1 : r ≠ 1 := fun h => by rw [h] at hqr; linarith
  have hrm1 : r ≠ -1 := fun h => by rw [h] at hqr; linarith [P.qr_neg_one_neg hP]
  have hrlt : -1 < r ∧ r < 1 := by
    rw [abs_le] at hrn
    exact ⟨lt_of_le_of_ne hrn.1 (Ne.symm hrm1), lt_of_le_of_ne hrn.2 hr1⟩
  -- the cofactor `s` has no zero on `[−1, 1]`
  have hs : ∀ t ∈ Set.Icc (-1 : ℝ) 1, sr P r t ≠ 0 := by
    intro t ht h0
    by_cases htr : t = r
    · rw [htr, sr_self] at h0; exact hdr h0
    · have hqt : P.qr t = 0 := by rw [qr_eq_sr P r t, h0, hqr]; ring
      have := huniq t (by rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; exact ht)
        (by rw [Par.eval_qC_ofReal, hqt, Complex.ofReal_zero])
      rw [hζr] at this
      exact htr (by exact_mod_cast this)
  have hscont : Continuous (sr P r) := by unfold sr; fun_prop
  have hsgn : 0 < sr P r (-1) * sr P r 1 := by
    by_contra hle
    rw [not_lt] at hle
    rcases le_total (sr P r (-1)) 0 with ha | ha
    · have hb : 0 ≤ sr P r 1 := by
        by_contra hb; rw [not_le] at hb
        have := mul_pos_of_neg_of_neg (lt_of_le_of_ne ha (hs (-1) ⟨le_rfl, by norm_num⟩)) hb
        linarith
      obtain ⟨t, ht, ht0⟩ := intermediate_value_Icc (show (-1 : ℝ) ≤ 1 by norm_num)
        hscont.continuousOn (show (0 : ℝ) ∈ Set.Icc (sr P r (-1)) (sr P r 1) from ⟨ha, hb⟩)
      exact hs t ht ht0
    · have hb : sr P r 1 ≤ 0 := by
        by_contra hb; rw [not_le] at hb
        have := mul_pos (lt_of_le_of_ne ha (Ne.symm (hs (-1) ⟨le_rfl, by norm_num⟩))) hb
        linarith
      obtain ⟨t, ht, ht0⟩ := intermediate_value_Icc' (show (-1 : ℝ) ≤ 1 by norm_num)
        hscont.continuousOn (show (0 : ℝ) ∈ Set.Icc (sr P r 1) (sr P r (-1)) from ⟨hb, ha⟩)
      exact hs t ht ht0
  have hprod : P.qr 1 * P.qr (-1) = -((1 - r) * (1 + r)) * (sr P r (-1) * sr P r 1) := by
    rw [qr_eq_sr P r 1, qr_eq_sr P r (-1), hqr]; ring
  have hpos : 0 < (1 - r) * (1 + r) := mul_pos (by linarith) (by linarith)
  have hneg := mul_pos_of_neg_of_neg h1 (P.qr_neg_one_neg hP)
  nlinarith

/-- Galí (2015), p. 174: A real root of `q` gives a real eigenvector: `A₀ʷ V = r A₁ʷ V`. -/
theorem exists_real_eigvec {P : Par} {r : ℝ} (hq : P.qr r = 0) :
    ∃ V : Fin 4 → ℝ, V ≠ 0 ∧ P.A0 *ᵥ V = r • (P.A1 *ᵥ V) := by
  have hdet : (P.A0 - r • P.A1).det = 0 := by rw [P.det_A0_sub_A1_real, hq, neg_zero]
  obtain ⟨V, hV0, hV⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨V, hV0, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.smul_mulVec] at hV
  exact hV

/-- Galí (2015), p. 174: The geometric mode `X_t = rᵗ V`. -/
theorem geom_mode {P : Par} {r : ℝ} {V : Fin 4 → ℝ} (hV : P.A0 *ᵥ V = r • (P.A1 *ᵥ V))
    (t : ℕ) : P.A0 *ᵥ (r ^ t • V) = P.A1 *ᵥ (r ^ (t + 1) • V) := by
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, hV, smul_smul, pow_succ]

/-- Galí (2015), p. 174 (tool): powers of a number in `[−1, 1]` stay in `[−1, 1]`. -/
theorem abs_pow_le_one {r : ℝ} (hr : |r| ≤ 1) (t : ℕ) : |r ^ t| ≤ 1 := by
  rw [abs_pow]; exact pow_le_one₀ (abs_nonneg r) hr

/-- Galí (2015), p. 174 (indeterminacy, complex roots): a non-real root of `q` in the closed
unit disc gives a nonzero bounded oscillating solution with `ω̃_{−1} = 0`. -/
theorem not_determinate_of_complex_root [Nonempty Ω] {P : Par} {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1)
    (hq : P.qC.eval ζ = 0) (him : ζ.im ≠ 0) : ¬ Determinate 𝔼 P := by
  have hdet : (P.A0.map Complex.ofReal - ζ • P.A1.map Complex.ofReal).det = 0 := by
    rw [P.det_A0_sub_A1, hq, neg_zero]
  obtain ⟨V, hV0, hV⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.smul_mulVec] at hV
  set c : ℂ := if V 3 = 0 then 1 else Complex.I * (starRingEnd ℂ) (V 3) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; split_ifs with h
    · exact one_ne_zero
    · exact mul_ne_zero Complex.I_ne_zero ((_root_.map_ne_zero _).mpr h)
  have hc3 : (c * V 3).re = 0 := by
    rw [hc]; split_ifs with h
    · simp [h]
    · rw [mul_assoc, Complex.conj_mul', ← Complex.ofReal_pow, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im]
      ring
  have key : ∀ (M : Matrix (Fin 4) (Fin 4) ℝ) (a : ℂ) (i : Fin 4),
      (M *ᵥ fun j => (a * V j).re) i = (a * ((M.map Complex.ofReal) *ᵥ V) i).re := by
    intro M a i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show a * (↑(M i j) * V j) = ↑(M i j) * (a * V j) by ring, Complex.re_ofReal_mul]
  refine not_determinate_of_mode 𝔼 (X := fun t j => (c * ζ ^ t * V j).re) (fun t => ?_) ?_ ?_ ?_
  · funext i
    rw [key, key, hV, Pi.smul_apply, smul_eq_mul]
    ring_nf
  · simpa using hc3
  · refine ⟨‖c‖ * ∑ j, ‖V j‖, fun t j => ?_⟩
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_mul, norm_pow]
    have h1 : ‖ζ‖ ^ t ≤ 1 := pow_le_one₀ (norm_nonneg _) hζ
    have h2 : ‖V j‖ ≤ ∑ j, ‖V j‖ :=
      Finset.single_le_sum (f := fun j => ‖V j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    calc ‖c‖ * ‖ζ‖ ^ t * ‖V j‖ ≤ ‖c‖ * 1 * ∑ j, ‖V j‖ := by gcongr
      _ = _ := by ring
  · intro hX
    obtain ⟨j, hj⟩ : ∃ j, V j ≠ 0 := by
      by_contra h; push Not at h; exact hV0 (funext h)
    have e0 := congrFun (congrFun hX 0) j
    have e1 := congrFun (congrFun hX 1) j
    simp only [pow_zero, mul_one, pow_one, Pi.zero_apply] at e0 e1
    set a := c * V j with ha
    have ha0 : a ≠ 0 := mul_ne_zero hc0 hj
    have e1' : (ζ * a).re = 0 := by rw [ha, ← e1]; ring_nf
    rw [Complex.mul_re, e0, mul_zero, zero_sub, neg_eq_zero] at e1'
    rcases mul_eq_zero.mp e1' with h | h
    · exact him h
    · exact ha0 (Complex.ext e0 h)

/-- Galí (2015), p. 174 (indeterminacy, two real roots): two distinct real roots of `q` in
`[−1, 1]` give a nonzero bounded mode with `ω̃_{−1} = 0`. -/
theorem exists_mode_of_two_real_roots {P : Par} {r₁ r₂ : ℝ} (hne : r₁ ≠ r₂)
    (h₁ : |r₁| ≤ 1) (h₂ : |r₂| ≤ 1) (hq₁ : P.qr r₁ = 0) (hq₂ : P.qr r₂ = 0) :
    ∃ X : ℕ → Fin 4 → ℝ, (∀ t, P.A0 *ᵥ X t = P.A1 *ᵥ X (t + 1)) ∧ X 0 3 = 0 ∧
      (∃ M, ∀ t j, |X t j| ≤ M) ∧ X ≠ 0 := by
  obtain ⟨V, hV0, hV⟩ := exists_real_eigvec hq₁
  obtain ⟨W, hW0, hW⟩ := exists_real_eigvec hq₂
  have hbd : ∀ (r : ℝ), |r| ≤ 1 → ∀ (U : Fin 4 → ℝ) t j, |(r ^ t • U) j| ≤ ∑ j, |U j| := by
    intro r hr U t j
    rw [Pi.smul_apply, smul_eq_mul, abs_mul]
    calc |r ^ t| * |U j| ≤ 1 * |U j| :=
          mul_le_mul_of_nonneg_right (abs_pow_le_one hr t) (abs_nonneg _)
      _ ≤ ∑ j, |U j| := by
          rw [one_mul]
          exact Finset.single_le_sum (f := fun j => |U j|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j)
  by_cases hV3 : V 3 = 0
  · refine ⟨fun t => r₁ ^ t • V, geom_mode hV, by simp [hV3], ⟨_, hbd r₁ h₁ V⟩,
      fun h => hV0 ?_⟩
    have := congrFun h 0; simpa using this
  by_cases hW3 : W 3 = 0
  · refine ⟨fun t => r₂ ^ t • W, geom_mode hW, by simp [hW3], ⟨_, hbd r₂ h₂ W⟩,
      fun h => hW0 ?_⟩
    have := congrFun h 0; simpa using this
  refine ⟨fun t => W 3 • (r₁ ^ t • V) - V 3 • (r₂ ^ t • W), fun t => ?_, ?_,
    ⟨|W 3| * ∑ j, |V j| + |V 3| * ∑ j, |W j|, fun t j => ?_⟩, ?_⟩
  · simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, hV, hW]
    module
  · simp; ring
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa using hbd r₁ h₁ V t j) (abs_nonneg _)
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa using hbd r₂ h₂ W t j) (abs_nonneg _)
  · intro h
    have e0 := congrFun h 0
    have e1 := congrFun h 1
    simp only [pow_zero, one_smul, pow_one, Pi.zero_apply] at e0 e1
    apply hV0
    funext j
    have a0 := congrFun e0 j
    have a1 := congrFun e1 j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at a0 a1
    have : W 3 * (r₁ - r₂) * V j = 0 := by linear_combination a1 - r₂ * a0
    rcases mul_eq_zero.mp this with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' hW3
      · exact absurd (sub_eq_zero.mp h'') hne
    · exact h'

/-- Galí (2015), p. 174 (indeterminacy, two real roots): not determinate. -/
theorem not_determinate_of_two_real_roots [Nonempty Ω] {P : Par} {r₁ r₂ : ℝ} (hne : r₁ ≠ r₂)
    (h₁ : |r₁| ≤ 1) (h₂ : |r₂| ≤ 1) (hq₁ : P.qr r₁ = 0) (hq₂ : P.qr r₂ = 0) :
    ¬ Determinate 𝔼 P := by
  obtain ⟨X, hX, h0, hb, hX0⟩ := exists_mode_of_two_real_roots hne h₁ h₂ hq₁ hq₂
  exact not_determinate_of_mode 𝔼 hX h0 hb hX0

/-- Galí (2015), p. 174 (indeterminacy, a double real root): a real root `r ∈ (−1, 1)` of
multiplicity at least two gives a nonzero bounded solution `rᵗ((t + c) V + r V′)` (or a pure
mode when `κ_w = κ_p`) with `ω̃_{−1} = 0`. -/
theorem not_determinate_of_double_root [Nonempty Ω] {P : Par} (hP : P.Adm) {r : ℝ}
    (hr : |r| < 1) (hq : P.qr r = 0) (hd : P.dqr r = 0) : ¬ Determinate 𝔼 P := by
  have hr0 : r ≠ 0 := by
    rintro rfl; rw [Par.qr_zero] at hq; exact (P.c0_neg hP).ne hq
  obtain ⟨hb0, hb1, -, -, -, hlp, hlw, -⟩ := hP
  have hbr : 0 < 1 - P.β * r := by
    have := abs_lt.mp hr
    nlinarith [abs_lt.mp hr]
  rw [P.qr_factor] at hq
  rw [P.dqr_factor] at hd
  by_cases hk : P.κw - P.κp = 0
  · -- `κ_w = κ_p`: then `Br(r) = 0` and `(1 − βr, κ_p, κ_w, 0)` is an eigenvector
    have hBr : P.Brr r = 0 := by
      by_contra hB
      rw [hk] at hq hd
      have hD : P.Dr r = 0 := by
        have : P.Brr r * P.Dr r = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left hB
      have hD' : -2 * P.β * r + (1 + P.β + (P.lamP + P.lamW)) = 0 := by
        rw [hD] at hd
        have : P.Brr r * (-2 * P.β * r + (1 + P.β + (P.lamP + P.lamW))) = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left hB
      simp only [Par.Dr] at hD
      have hr2 : P.β * r ^ 2 = 1 := by nlinarith
      have : r ^ 2 < 1 := by nlinarith [abs_lt.mp hr]
      nlinarith
    set V : Fin 4 → ℝ := ![1 - P.β * r, P.κp, P.κw, 0] with hVdef
    have hV : P.A0 *ᵥ V = r • (P.A1 *ᵥ V) := by
      funext i
      fin_cases i <;> simp [hVdef, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Par.A0,
        Par.A1]
      · simp only [Par.Brr] at hBr; linear_combination hBr
      · ring
      · ring
      · linear_combination hk
    refine not_determinate_of_mode 𝔼 (X := fun t => r ^ t • V) (geom_mode hV) (by simp [hVdef])
      ⟨∑ j, |V j|, fun t j => ?_⟩ fun h => ?_
    · rw [Pi.smul_apply, smul_eq_mul, abs_mul]
      calc |r ^ t| * |V j| ≤ 1 * |V j| :=
            mul_le_mul_of_nonneg_right (abs_pow_le_one hr.le t) (abs_nonneg _)
        _ ≤ ∑ j, |V j| := by
            rw [one_mul]
            exact Finset.single_le_sum (f := fun j => |V j|) (fun _ _ => abs_nonneg _)
              (Finset.mem_univ j)
    · have := congrFun (congrFun h 0) 0
      simp [hVdef] at this
      linarith
  · -- `κ_w ≠ κ_p`: the eigenvector field `v(r)` and its derivative give a Jordan chain
    set k := P.κw - P.κp with hkdef
    set V : Fin 4 → ℝ := ![P.Dr r * (1 - P.β * r), P.κp * P.Dr r + P.lamP * r * k,
      P.κw * P.Dr r - P.lamW * r * k, k * (1 - P.β * r)] with hVdef
    set D' := -2 * P.β * r + (1 + P.β + (P.lamP + P.lamW)) with hD'
    set V' : Fin 4 → ℝ := ![D' * (1 - P.β * r) - P.β * P.Dr r, P.κp * D' + P.lamP * k,
      P.κw * D' - P.lamW * k, -(k * P.β)] with hV'def
    have hV : ∀ i, (P.A0 *ᵥ V) i = r * (P.A1 *ᵥ V) i := by
      intro i
      fin_cases i <;> simp [hVdef, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Par.A0,
        Par.A1]
      · simp only [Par.Brr, Par.Dr, Par.Hr] at hq ⊢; linear_combination hq
      · ring
      · ring
      · simp only [Par.Dr]; ring
    have hV' : ∀ i, (P.A0 *ᵥ V') i = r * (P.A1 *ᵥ V') i + (P.A1 *ᵥ V) i := by
      intro i
      fin_cases i <;> simp [hVdef, hV'def, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
        Par.A0, Par.A1]
      · simp only [Par.Brr, Par.Dr, Par.Hr, hD'] at hd ⊢; linear_combination hd
      · ring
      · ring
      · simp only [hD']; ring
    have hV3 : V 3 ≠ 0 := by rw [hVdef]; exact mul_ne_zero hk hbr.ne'
    set c : ℝ := -(r * V' 3) / V 3 with hc
    have hc3 : c * V 3 + r * V' 3 = 0 := by rw [hc]; field_simp; ring
    obtain ⟨B, hB⟩ := (tendsto_self_mul_const_pow_of_lt_one (abs_nonneg r) hr).bddAbove_range
    refine not_determinate_of_mode 𝔼 (X := fun t => r ^ t • (((t : ℝ) + c) • V + r • V'))
      (fun t => ?_) ?_ ⟨(B + |c|) * ∑ j, |V j| + ∑ j, |V' j|, fun t j => ?_⟩ ?_
    · funext i
      simp only [Matrix.mulVec_smul, Matrix.mulVec_add, Pi.smul_apply, Pi.add_apply,
        smul_eq_mul, hV i, hV' i]
      push_cast
      ring
    · simp only [pow_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_zero, zero_add]
      linear_combination hc3
    · have hBt : |r| ^ t * t ≤ B := by
        have := hB ⟨t, rfl⟩; simp only at this; linarith [mul_comm (|r| ^ t) (t : ℝ)]
      have hpt : |r| ^ t ≤ 1 := pow_le_one₀ (abs_nonneg r) hr.le
      have hVj : |V j| ≤ ∑ j, |V j| :=
        Finset.single_le_sum (f := fun j => |V j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      have hV'j : |V' j| ≤ ∑ j, |V' j| :=
        Finset.single_le_sum (f := fun j => |V' j|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ j)
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      have hB0 : 0 ≤ B := le_trans (by positivity) hBt
      calc |r ^ t * ((t + c) * V j + r * V' j)|
          ≤ (|r| ^ t * t + |r| ^ t * |c|) * |V j| + |r| ^ t * |r| * |V' j| := by
            rw [abs_mul, abs_pow]
            have h1 : |(t + c) * V j + r * V' j| ≤ (t + |c|) * |V j| + |r| * |V' j| := by
              refine (abs_add_le _ _).trans (add_le_add ?_ (by rw [abs_mul]))
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_right ((abs_add_le _ _).trans (by
                rw [abs_of_nonneg (Nat.cast_nonneg t)])) (abs_nonneg _)
            calc |r| ^ t * |(t + c) * V j + r * V' j| ≤
                |r| ^ t * ((t + |c|) * |V j| + |r| * |V' j|) :=
                  mul_le_mul_of_nonneg_left h1 (by positivity)
              _ = _ := by ring
        _ ≤ (B + |c|) * ∑ j, |V j| + ∑ j, |V' j| := by
            have hr1 : |r| ^ t * |r| ≤ 1 := by
              have := mul_le_mul hpt hr.le (abs_nonneg r) zero_le_one; linarith
            have hc1 : |r| ^ t * |c| ≤ |c| := by
              have := mul_le_mul_of_nonneg_right hpt (abs_nonneg c); linarith
            have e1 : (|r| ^ t * t + |r| ^ t * |c|) * |V j| ≤ (B + |c|) * ∑ j, |V j| :=
              mul_le_mul (by linarith) hVj (abs_nonneg _) (by positivity)
            have e2 : |r| ^ t * |r| * |V' j| ≤ ∑ j, |V' j| := by
              have := mul_le_mul hr1 hV'j (abs_nonneg _) zero_le_one; linarith
            linarith
    · intro h
      have e0 := congrFun h 0
      have e1 := congrFun h 1
      apply hV3
      have a0 : c • V + r • V' = 0 := by simpa using e0
      have a1 : r • ((1 + c) • V + r • V') = 0 := by simpa using e1
      have hVz : r • V = 0 := by
        have : r • ((1 + c) • V + r • V') = r • V + r • (c • V + r • V') := by module
        rw [this, a0, smul_zero, add_zero] at a1
        exact a1
      have := congrFun hVz 3
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      exact (mul_eq_zero.mp this).resolve_left hr0

end Dyn

namespace Dyn

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- **Galí (2015), p. 174, necessity (strict case)**: if
`φ_p + φ_w + φ_y (1 − β)/Θ_y (1/λ_p + 1/λ_w) < 1` the equilibrium is not determinate: either no
bounded solution exists (no root of `q` in the closed unit disc) or there are many (two or more
roots in the closed disc; one is impossible). -/
theorem not_determinate_of_neg [Nonempty Ω] {P : Par} (hP : P.Adm) (h1 : P.qr 1 < 0) :
    ¬ Determinate 𝔼 P := by
  rcases Nat.lt_or_ge (closedRoots P).card 2 with hlt | hge
  · have h0 : (closedRoots P).card = 0 := by
      have := closedRoots_card_ne_one hP h1
      omega
    refine not_determinate_of_no_root 𝔼 hP fun ζ hζ h0' => ?_
    have hm := (mem_closedRoots hP).mpr ⟨hζ, h0'⟩
    rw [Multiset.card_eq_zero.mp h0] at hm
    exact Multiset.notMem_zero _ hm
  · by_cases hcx : ∃ ζ ∈ closedRoots P, ζ.im ≠ 0
    · obtain ⟨ζ, hζ, him⟩ := hcx
      obtain ⟨hn, hq⟩ := (mem_closedRoots hP).mp hζ
      exact not_determinate_of_complex_root 𝔼 hn hq him
    · push Not at hcx
      obtain ⟨ζ₁, h₁⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < (closedRoots P).card)
      have hcard : 0 < ((closedRoots P).erase ζ₁).card := by
        rw [Multiset.card_erase_of_mem h₁, Nat.pred_eq_sub_one]; omega
      obtain ⟨ζ₂, h₂e⟩ := Multiset.card_pos_iff_exists_mem.mp hcard
      have h₂ := Multiset.mem_of_mem_erase h₂e
      have hreal : ∀ ζ ∈ closedRoots P, ζ = (ζ.re : ℂ) := fun ζ hζ =>
        Complex.ext (by simp) (by simp [hcx ζ hζ])
      obtain ⟨hn₁, hq₁⟩ := (mem_closedRoots hP).mp h₁
      obtain ⟨hn₂, hq₂⟩ := (mem_closedRoots hP).mp h₂
      have hr₁ : P.qr ζ₁.re = 0 := by
        have := hq₁; rw [hreal ζ₁ h₁, Par.eval_qC_ofReal] at this; exact_mod_cast this
      have hr₂ : P.qr ζ₂.re = 0 := by
        have := hq₂; rw [hreal ζ₂ h₂, Par.eval_qC_ofReal] at this; exact_mod_cast this
      have ha₁ : |ζ₁.re| ≤ 1 := by
        have := hn₁; rwa [hreal ζ₁ h₁, Complex.norm_real, Real.norm_eq_abs] at this
      have ha₂ : |ζ₂.re| ≤ 1 := by
        have := hn₂; rwa [hreal ζ₂ h₂, Complex.norm_real, Real.norm_eq_abs] at this
      by_cases h12 : ζ₁ = ζ₂
      · subst h12
        have hc1 : 1 ≤ ((closedRoots P).erase ζ₁).count ζ₁ := Multiset.one_le_count_iff_mem.mpr h₂e
        rw [Multiset.count_erase_self] at hc1
        have hcnt : 2 ≤ P.qC.rootMultiplicity ζ₁ := by
          rw [← count_roots]
          have := Multiset.count_le_of_le ζ₁ (Multiset.filter_le (fun z : ℂ => ‖z‖ ≤ 1) P.qC.roots)
          rw [closedRoots] at hc1
          omega
        obtain ⟨-, hder⟩ := (one_lt_rootMultiplicity_iff_isRoot (qC_ne_zero hP)).mp hcnt
        have hd : P.dqr ζ₁.re = 0 := by
          have := hder
          rw [IsRoot, P.eval_derivative_qC, hreal ζ₁ h₁] at this
          have e : ((P.dqr ζ₁.re : ℝ) : ℂ) = 0 := by
            simp only [Par.dqr]; push_cast; exact this
          exact_mod_cast e
        have hlt1 : |ζ₁.re| < 1 := by
          refine lt_of_le_of_ne ha₁ fun he => ?_
          rcases abs_eq (zero_le_one) |>.mp he with h | h
          · rw [h] at hr₁; linarith
          · rw [h] at hr₁; linarith [P.qr_neg_one_neg hP]
        exact not_determinate_of_double_root 𝔼 hP hlt1 hr₁ hd
      · have hne : ζ₁.re ≠ ζ₂.re := fun h => h12 (by rw [hreal ζ₁ h₁, hreal ζ₂ h₂, h])
        exact not_determinate_of_two_real_roots 𝔼 hne ha₁ ha₂ hr₁ hr₂

/-- Galí (2015), p. 174, necessity: if the condition fails, the equilibrium is not determinate. -/
theorem not_determinate_of_le [Nonempty Ω] {P : Par} (hP : P.Adm) (h1 : P.qr 1 ≤ 0) :
    ¬ Determinate 𝔼 P := by
  rcases eq_or_lt_of_le h1 with h | h
  · exact not_determinate_of_eq 𝔼 hP h
  · exact not_determinate_of_neg 𝔼 hP h

/-- **Galí (2015), p. 174 (the determinacy theorem, in `q(1)` form)**: under the sign conditions,
system (24) is determinate if and only if `q(1) = λ_p λ_w Θ_y (LHS − 1) > 0`. -/
theorem determinate_iff [Nonempty Ω] {P : Par} (hP : P.Adm) (hΨ : 0 < P.Ψ) :
    Determinate 𝔼 P ↔ 0 < P.qr 1 := by
  constructor
  · intro h
    by_contra h1
    exact not_determinate_of_le 𝔼 hP (not_lt.mp h1) h
  · exact determinate_of_pos 𝔼 hP hΨ

end Dyn

namespace Par

/-- Galí (2015), p. 174: `Aʷ = (A₀ʷ)⁻¹ A₁ʷ` (Galí 2015, p. 174). -/
noncomputable def Aw (P : Par) : Matrix (Fin 4) (Fin 4) ℝ := P.A0⁻¹ * P.A1

/-- Galí (2015), p. 174: `det(A₀ʷ) · det(w I − Aʷ) = det(w A₀ʷ − A₁ʷ)`. -/
theorem det_A0_mul_det_charmat {P : Par} (hP : P.Adm) (w : ℂ) :
    (P.A0.map Complex.ofReal).det * (Matrix.scalar (Fin 4) w - P.Aw.map Complex.ofReal).det =
      (w • P.A0.map Complex.ofReal - P.A1.map Complex.ofReal).det := by
  have hA0u : IsUnit P.A0.det := by
    rw [P.det_A0]; exact isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (P.c0_neg hP).ne)
  have hAA : P.A0.map Complex.ofReal * P.Aw.map Complex.ofReal = P.A1.map Complex.ofReal := by
    rw [Dyn.map_ofReal_eq, Dyn.map_ofReal_eq, Dyn.map_ofReal_eq, ← map_mul, Aw,
      Matrix.mul_nonsing_inv_cancel_left _ _ hA0u]
  rw [← Matrix.det_mul, Matrix.mul_sub, hAA, Matrix.scalar_apply]
  congr 2
  ext i j
  simp [Matrix.mul_diagonal, mul_comm]

/-- Galí (2015), p. 174: the characteristic polynomial of `Aʷ` is a nonzero multiple of the
reversed quartic `Q(w) = w⁴ q(1/w)`. -/
theorem charpoly_Aw {P : Par} (hP : P.Adm) :
    (P.Aw.map Complex.ofReal).charpoly = C (-((P.A0.det : ℂ))⁻¹) * P.QC := by
  have hdA0 : ((P.A0.det : ℝ) : ℂ) ≠ 0 := by
    rw [P.det_A0]; exact_mod_cast neg_ne_zero.mpr (P.c0_neg hP).ne
  have hdc : (P.A0.map Complex.ofReal).det = ((P.A0.det : ℝ) : ℂ) := by
    rw [Dyn.map_ofReal_eq, ← RingHom.map_det]; rfl
  refine Polynomial.eq_of_infinite_eval_eq _ _ ((Set.finite_singleton (0 : ℂ)).infinite_compl.mono
    fun w hw => ?_)
  have hw0 : w ≠ 0 := hw
  simp only [Set.mem_ofPred_eq, Matrix.eval_charpoly, eval_mul, eval_C]
  have h := det_A0_mul_det_charmat hP w
  have hsplit : w • P.A0.map Complex.ofReal - P.A1.map Complex.ofReal =
      w • (P.A0.map Complex.ofReal - w⁻¹ • P.A1.map Complex.ofReal) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hw0, one_smul]
  rw [hsplit, Matrix.det_smul, P.det_A0_sub_A1, hdc] at h
  rw [P.eval_QC_eq hw0]
  simp only [Fintype.card_fin] at h
  have h' := congrArg (fun z => ((P.A0.det : ℝ) : ℂ)⁻¹ * z) h
  simp only [← mul_assoc, inv_mul_cancel₀ hdA0, one_mul] at h'
  rw [h']
  ring

/-- **Galí (2015), p. 174 (the eigenvalue form)**: under the sign conditions, exactly three
eigenvalues of `Aʷ = (A₀ʷ)⁻¹ A₁ʷ` lie inside the unit circle and one outside (counted with
multiplicity) if and only if `q(1) > 0`. -/
theorem eigen_count_iff {P : Par} (hP : P.Adm) (hΨ : 0 < P.Ψ) :
    ((P.Aw.map Complex.ofReal).charpoly.roots.filter (fun z => ‖z‖ < 1)).card = 3 ∧
      ((P.Aw.map Complex.ofReal).charpoly.roots.filter (fun z => 1 < ‖z‖)).card = 1 ↔
      0 < P.qr 1 := by
  have hc : (-((P.A0.det : ℂ))⁻¹) ≠ 0 := by
    rw [P.det_A0]
    simp only [Complex.ofReal_neg, inv_neg, neg_neg, ne_eq, inv_eq_zero]
    exact_mod_cast (P.c0_neg hP).ne
  rw [charpoly_Aw hP, roots_C_mul _ hc]
  constructor
  · rintro ⟨hin, hout⟩
    by_contra hq
    have hq' := not_lt.mp hq
    have h4 := card_roots_QC hP
    -- no root of `Q` lies on the unit circle
    have hsplit := Multiset.filter_add_not (fun z : ℂ => ‖z‖ < 1) P.QC.roots
    have hnot : (P.QC.roots.filter (fun z => ¬ ‖z‖ < 1)).card = 1 := by
      have := congrArg Multiset.card hsplit
      rw [Multiset.card_add, hin, h4] at this
      omega
    have hsub : P.QC.roots.filter (fun z => 1 < ‖z‖) ≤
        P.QC.roots.filter (fun z => ¬ ‖z‖ < 1) :=
      Multiset.monotone_filter_right _ fun z h => not_lt.mpr h.le
    have heqf : P.QC.roots.filter (fun z => 1 < ‖z‖) =
        P.QC.roots.filter (fun z => ¬ ‖z‖ < 1) :=
      Multiset.eq_of_le_of_card_le hsub (by rw [hout, hnot])
    have hcirc : ∀ z ∈ P.QC.roots, ‖z‖ ≠ 1 := by
      intro z hz h1
      have hm : z ∈ P.QC.roots.filter (fun z => ¬ ‖z‖ < 1) :=
        Multiset.mem_filter.mpr ⟨hz, by rw [h1]; exact lt_irrefl 1⟩
      rw [← heqf, Multiset.mem_filter, h1] at hm
      exact lt_irrefl 1 hm.2
    rcases eq_or_lt_of_le hq' with h1 | h1
    · -- `Q(1) = q(1) = 0`: a unit eigenvalue
      apply hcirc 1 ((mem_roots (QC_ne_zero hP)).mpr ?_) (by simp)
      rw [IsRoot, eval_QC_eq P one_ne_zero, inv_one, one_pow, one_mul]
      have := P.eval_qC_ofReal 1
      rw [Complex.ofReal_one] at this
      rw [this, h1, Complex.ofReal_zero]
    · obtain ⟨w0, hw0⟩ := Multiset.card_eq_one.mp hout
      have hw0f : w0 ∈ P.QC.roots.filter (fun z => 1 < ‖z‖) := by
        rw [hw0]; exact Multiset.mem_singleton_self w0
      have hw0m : w0 ∈ P.QC.roots := Multiset.mem_of_mem_filter hw0f
      have hw0n : 1 < ‖w0‖ := (Multiset.mem_filter.mp hw0f).2
      have hw00 : w0 ≠ 0 := by intro h; rw [h, norm_zero] at hw0n; linarith
      -- every root of `q` in the closed disc is `w0⁻¹`
      have hall : ∀ ζ ∈ Dyn.closedRoots P, ζ = w0⁻¹ := by
        intro ζ hζ
        obtain ⟨hn, hq0⟩ := (Dyn.mem_closedRoots hP).mp hζ
        have hζ0 : ζ ≠ 0 := by
          rintro rfl; rw [qC_eval_zero] at hq0; exact (c0_neg hP).ne (by exact_mod_cast hq0)
        have hroot : ζ⁻¹ ∈ P.QC.roots := (mem_roots (QC_ne_zero hP)).mpr (by
          rw [IsRoot, eval_QC_eq P (inv_ne_zero hζ0), inv_inv, hq0, mul_zero])
        have hge : 1 ≤ ‖ζ⁻¹‖ := by
          rw [norm_inv]; exact one_le_inv_iff₀.mpr ⟨norm_pos_iff.mpr hζ0, hn⟩
        have hout' : ζ⁻¹ ∈ P.QC.roots.filter (fun z => 1 < ‖z‖) :=
          Multiset.mem_filter.mpr ⟨hroot, lt_of_le_of_ne hge (Ne.symm (hcirc _ hroot))⟩
        rw [hw0, Multiset.mem_singleton] at hout'
        rw [← hout', inv_inv]
      -- `w0⁻¹` is a root of `q` in the open disc
      have hmem : w0⁻¹ ∈ Dyn.closedRoots P := by
        refine (Dyn.mem_closedRoots hP).mpr ⟨?_, ?_⟩
        · rw [norm_inv]; exact inv_le_one_of_one_le₀ hw0n.le
        · have := (mem_roots (QC_ne_zero hP)).mp hw0m
          rw [IsRoot, eval_QC_eq P hw00] at this
          exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hw00)
      -- and it is simple
      have hcount : (Dyn.closedRoots P).count w0⁻¹ ≤ 1 := by
        rw [Dyn.closedRoots, Multiset.count_filter_of_pos (p := fun z : ℂ => ‖z‖ ≤ 1)
          ((Dyn.mem_closedRoots hP).mp hmem).1, count_roots]
        by_contra hm
        obtain ⟨hr, hd⟩ := (one_lt_rootMultiplicity_iff_isRoot (t := w0⁻¹)
          (Dyn.qC_ne_zero hP)).mp (by omega)
        have hQd : P.QC.derivative.IsRoot w0 := by
          rw [IsRoot, eval_derivative_QC]
          rw [IsRoot, P.eval_derivative_qC] at hd
          rw [IsRoot, eval_qC] at hr
          have hw' : w0 * w0⁻¹ = 1 := mul_inv_cancel₀ hw00
          linear_combination (4 * w0 ^ 3) * hr - w0 ^ 2 * hd
            + (-4 * w0 ^ 2 * w0⁻¹ ^ 3 * P.c4 - 4 * w0 ^ 2 * w0⁻¹ ^ 2 * P.c3
              - 4 * w0 ^ 2 * w0⁻¹ * P.c2 - 4 * w0 ^ 2 * P.c1 - w0 * w0⁻¹ * P.c3
              - 2 * w0 * P.c2 - P.c3) * hw'
        have hm2 := (one_lt_rootMultiplicity_iff_isRoot (QC_ne_zero hP)).mpr
          ⟨(mem_roots (QC_ne_zero hP)).mp hw0m, hQd⟩
        have : 2 ≤ (P.QC.roots.filter (fun z => 1 < ‖z‖)).count w0 := by
          rw [Multiset.count_filter_of_pos (p := fun z : ℂ => 1 < ‖z‖) hw0n, count_roots]
          omega
        rw [hw0, Multiset.count_singleton_self] at this
        omega
      have hcard : (Dyn.closedRoots P).card = 1 := by
        rw [Multiset.eq_replicate_of_mem hall, Multiset.card_replicate]
        have := Multiset.count_pos.mpr hmem
        rw [Multiset.eq_replicate_of_mem hall, Multiset.count_replicate_self] at this hcount
        omega
      exact Dyn.closedRoots_card_ne_one hP h1 hcard
  · intro h1
    exact ⟨inCount_QC hP hΨ h1, outCount_QC hP hΨ h1⟩

end Par

namespace Dyn

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (24), p. 173, row by row: the matrix equation is the IS equation (22) with
rule (23) substituted, the price and wage Phillips curves (18) and (20), and the real-wage
identity (21), where `x_t = (ỹ_t, π^p_t, π^w_t, ω̃_{t−1})` and
`u_t = (r̂ⁿ_t − v_t − φ_y ŷⁿ_t, Δωⁿ_t)`. -/
theorem eq24_iff (P : Par) (x : ℕ → Fin 4 → Ω → ℝ) (u : ℕ → Fin 2 → Ω → ℝ) (t : ℕ) :
    rvMul P.A0 (x t) = rvMul P.A1 (fun j => 𝔼.E t (x (t + 1) j)) + rvMul B0 (u t) ↔
      ∀ ω, (P.σ + P.φy) * x t 0 ω + P.φp * x t 1 ω + P.φw * x t 2 ω =
          P.σ * 𝔼.E t (x (t + 1) 0) ω + 𝔼.E t (x (t + 1) 1) ω + u t 0 ω ∧
        x t 1 ω = P.β * 𝔼.E t (x (t + 1) 1) ω + P.κp * x t 0 ω
          + P.lamP * 𝔼.E t (x (t + 1) 3) ω ∧
        x t 2 ω = P.β * 𝔼.E t (x (t + 1) 2) ω + P.κw * x t 0 ω
          - P.lamW * 𝔼.E t (x (t + 1) 3) ω ∧
        𝔼.E t (x (t + 1) 3) ω = x t 3 ω + x t 2 ω - x t 1 ω - u t 1 ω := by
  constructor
  · intro h ω
    have h0 := congrFun (congrFun h 0) ω
    have h1 := congrFun (congrFun h 1) ω
    have h2 := congrFun (congrFun h 2) ω
    have h3 := congrFun (congrFun h 3) ω
    simp only [Par.A0, Fin.isValue, rvMul_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_fin_one, Matrix.cons_val_zero, Fin.sum_univ_four, Matrix.cons_val_one,
      Matrix.cons_val, zero_mul, add_zero, Par.A1, B0, Pi.add_apply, one_mul, Fin.sum_univ_two,
      neg_mul, zero_add] at h0 h1 h2 h3
    refine ⟨by linear_combination h0, by linear_combination h1, by linear_combination h2,
      by linear_combination -h3⟩
  · intro h
    funext i ω
    obtain ⟨h0, h1, h2, h3⟩ := h ω
    fin_cases i <;>
      simp [rvMul_apply, Fin.sum_univ_four, Fin.sum_univ_two, Par.A0, Par.A1, B0]
    · linear_combination h0
    · linear_combination h1
    · linear_combination h2
    · linear_combination -h3

end Dyn

namespace Par

/-- Galí (2015), p. 174: the left-hand side
`φ_p + φ_w + φ_y (1 − β)(λ_p + λ_w)/(λ_w κ_p + λ_p κ_w)` of the determinacy condition. -/
noncomputable def Lhs (P : Par) : ℝ := P.φp + P.φw + P.φy * (1 - P.β) * (P.lamP + P.lamW) / P.Ψ

/-- Galí (2015), p. 174: `q(1) = Ψ (LHS − 1)`, i.e. `det(A₀ʷ − A₁ʷ) = −Ψ (LHS − 1)`. -/
theorem qr_one_eq_mul {P : Par} (hΨ : P.Ψ ≠ 0) : P.qr 1 = P.Ψ * (P.Lhs - 1) := by
  rw [qr_one, Lhs]; field_simp; ring

/-- Galí (2015), p. 174: `q(1) > 0` is exactly the book's condition `LHS > 1`. -/
theorem qr_one_pos_iff {P : Par} (hΨ : 0 < P.Ψ) : 0 < P.qr 1 ↔ 1 < P.Lhs := by
  rw [qr_one_eq_mul hΨ.ne']
  constructor
  · intro h; by_contra h'; nlinarith
  · intro h; nlinarith

end Par

/-- Galí (2015), (18) and (20), p. 172: the system parameters from the primitives,
`κ_p = α λ_p/(1 − α)` and `κ_w = λ_w (σ + φ/(1 − α))`. -/
noncomputable def bookPar (β σ φ α lamP lamW φp φw φy : ℝ) : Par :=
  ⟨β, σ, α * lamP / (1 - α), lamW * (σ + φ / (1 - α)), lamP, lamW, φp, φw, φy⟩

/-- Galí (2015), p. 174: the book's hypotheses give the sign conditions. -/
theorem bookPar_adm {β σ φ α lamP lamW φp φw φy : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hlp : 0 < lamP) (hlw : 0 < lamW) (hfp : 0 ≤ φp)
    (hfw : 0 ≤ φw) (hfy : 0 ≤ φy) : (bookPar β σ φ α lamP lamW φp φw φy).Adm := by
  have h1α : 0 < 1 - α := by linarith
  exact ⟨hβ0, hβ1, hσ, by simp only [bookPar]; positivity, by simp only [bookPar]; positivity,
    hlp, hlw, hfp, hfw, hfy⟩

/-- Galí (2015), p. 174: `Ψ = λ_p λ_w Θ_y` with `Θ_y = σ + (φ + α)/(1 − α)`. -/
theorem bookPar_Ψ {β σ φ α lamP lamW φp φw φy : ℝ} (hα1 : α < 1) :
    (bookPar β σ φ α lamP lamW φp φw φy).Ψ = lamP * lamW * (σ + (φ + α) / (1 - α)) := by
  have h1α : (1 - α) ≠ 0 := by linarith
  simp only [Par.Ψ, bookPar]
  field_simp
  ring

/-- Galí (2015), p. 174: the left-hand side in the book's form. -/
theorem bookPar_Lhs {β σ φ α lamP lamW φp φw φy : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hlp : 0 < lamP) (hlw : 0 < lamW) :
    (bookPar β σ φ α lamP lamW φp φw φy).Lhs =
      φp + φw + φy * (1 - β) / (σ + (α + φ) / (1 - α)) * (1 / lamP + 1 / lamW) := by
  have h1α : 0 < 1 - α := by linarith
  have hΘ : 0 < σ + (α + φ) / (1 - α) := by positivity
  rw [Par.Lhs, bookPar_Ψ hα1]
  simp only [bookPar]
  rw [show φ + α = α + φ by ring]
  field_simp
  ring

/-- **Galí (2015), p. 174 — the determinacy theorem.** Let `0 < β < 1`, `σ > 0`, `φ ≥ 0`,
`0 ≤ α < 1`, `λ_p, λ_w > 0` and `φ_p, φ_w, φ_y ≥ 0`. The equilibrium of system (24) under rule
(23) is determinate (for every bounded adapted forcing and every bounded initial real wage gap
`ω̃_{−1}` there is exactly one bounded solution) if and only if
`φ_p + φ_w + φ_y (1 − β)/Θ_y (1/λ_p + 1/λ_w) > 1`, `Θ_y = σ + (α + φ)/(1 − α)`. -/
theorem determinacy_iff {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω)
    {β σ φ α lamP lamW φp φw φy : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hφ : 0 ≤ φ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hlp : 0 < lamP) (hlw : 0 < lamW) (hfp : 0 ≤ φp)
    (hfw : 0 ≤ φw) (hfy : 0 ≤ φy) :
    Dyn.Determinate 𝔼 (bookPar β σ φ α lamP lamW φp φw φy) ↔
      1 < φp + φw + φy * (1 - β) / (σ + (α + φ) / (1 - α)) * (1 / lamP + 1 / lamW) := by
  have hP := bookPar_adm (φp := φp) (φw := φw) (φy := φy) (lamP := lamP) (lamW := lamW)
    hβ0 hβ1 hσ hφ hα0 hα1 hlp hlw hfp hfw hfy
  have hΨ : 0 < (bookPar β σ φ α lamP lamW φp φw φy).Ψ := by
    rw [bookPar_Ψ hα1]
    have h1α : 0 < 1 - α := by linarith
    positivity
  rw [Dyn.determinate_iff 𝔼 hP hΨ, Par.qr_one_pos_iff hΨ, bookPar_Lhs hσ hφ hα0 hα1 hlp hlw]

/-- **Galí (2015), p. 174 — the eigenvalue form.** Under the same hypotheses, exactly three
eigenvalues of `Aʷ = (A₀ʷ)⁻¹ A₁ʷ` lie inside and one outside the unit circle (counted with
multiplicity) if and only if `φ_p + φ_w + φ_y (1 − β)/Θ_y (1/λ_p + 1/λ_w) > 1`. -/
theorem eigenvalues_iff {β σ φ α lamP lamW φp φw φy : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hlp : 0 < lamP) (hlw : 0 < lamW)
    (hfp : 0 ≤ φp) (hfw : 0 ≤ φw) (hfy : 0 ≤ φy) :
    (((bookPar β σ φ α lamP lamW φp φw φy).Aw.map Complex.ofReal).charpoly.roots.filter
        (fun z => ‖z‖ < 1)).card = 3 ∧
      (((bookPar β σ φ α lamP lamW φp φw φy).Aw.map Complex.ofReal).charpoly.roots.filter
        (fun z => 1 < ‖z‖)).card = 1 ↔
      1 < φp + φw + φy * (1 - β) / (σ + (α + φ) / (1 - α)) * (1 / lamP + 1 / lamW) := by
  have hP := bookPar_adm (φp := φp) (φw := φw) (φy := φy) (lamP := lamP) (lamW := lamW)
    hβ0 hβ1 hσ hφ hα0 hα1 hlp hlw hfp hfw hfy
  have hΨ : 0 < (bookPar β σ φ α lamP lamW φp φw φy).Ψ := by
    rw [bookPar_Ψ hα1]
    have h1α : 0 < 1 - α := by linarith
    positivity
  rw [Par.eigen_count_iff hP hΨ, Par.qr_one_pos_iff hΨ, bookPar_Lhs hσ hφ hα0 hα1 hlp hlw]

/-- Galí (2015), p. 174: with `φ_y = 0` the condition reads `φ_p + φ_w > 1`. -/
theorem determinacy_iff_phiY_zero {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω)
    {β σ φ α lamP lamW φp φw : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hφ : 0 ≤ φ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hlp : 0 < lamP) (hlw : 0 < lamW) (hfp : 0 ≤ φp)
    (hfw : 0 ≤ φw) :
    Dyn.Determinate 𝔼 (bookPar β σ φ α lamP lamW φp φw 0) ↔ 1 < φp + φw := by
  rw [determinacy_iff 𝔼 hβ0 hβ1 hσ hφ hα0 hα1 hlp hlw hfp hfw le_rfl]
  simp

namespace Par

/-- Galí (2015), p. 174 (non-existence criterion): if on the unit circle `q(z)` is never a
nonnegative real number, all four roots of `Q` (eigenvalues of `Aʷ`) lie in the open unit disc.
The proof deforms `Q` to `q(0) w⁴` along `(1 − s) Q(w) + s q(0) w⁴`. -/
theorem inCount_QC_four {P : Par} (hP : P.Adm)
    (hcirc : ∀ z : ℂ, ‖z‖ = 1 → (P.qC.eval z).im = 0 → (P.qC.eval z).re < 0) :
    inCount P.QC = 4 := by
  have hc0 : (P.c0 : ℂ) ≠ 0 := by exact_mod_cast (c0_neg hP).ne
  set a : ℝ → Fin 5 → ℂ := fun s => ![(1 - s) * P.c4, (1 - s) * P.c3, (1 - s) * P.c2,
    (1 - s) * P.c1, P.c0] with ha
  have h := inCount_path a (fun i => by fin_cases i <;> simp only [ha] <;> fun_prop)
    (fun s _ => quart_ne_zero (by simpa [ha] using hc0)) ?_
  · have h0 : quart (a 0) = P.QC := by
      rw [QC]; congr 1; funext i; fin_cases i <;> simp [ha, Qv]
    have h1 : quart (a 1) = C (P.c0 : ℂ) * X ^ 4 := by
      simp [ha, quart]
    rw [h0, h1] at h
    rw [h, inCount, roots_C_mul _ hc0, roots_X_pow]
    simp [Multiset.filter_nsmul, Multiset.filter_singleton]
  · intro s ⟨hs0, hs1⟩ w hw h0
    have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; exact zero_ne_one hw
    set z := w⁻¹ with hz
    have hzn : ‖z‖ = 1 := by rw [hz, norm_inv, hw, inv_one]
    have hexp : (quart (a s)).eval w = w ^ 4 * ((1 - s) * P.qC.eval z + s * P.c0) := by
      rw [eval_quart, eval_qC, hz]
      simp only [ha, Matrix.cons_val]
      field_simp
      ring
    rw [hexp] at h0
    have key : ((1 - s : ℝ) : ℂ) * P.qC.eval z + ((s * P.c0 : ℝ) : ℂ) = 0 := by
      have := (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ hw0)
      push_cast; linear_combination this
    have kre := congrArg Complex.re key
    have kim := congrArg Complex.im key
    simp only [Complex.add_re, Complex.add_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im, add_zero] at kre kim
    have hc0' := c0_neg hP
    rcases eq_or_lt_of_le hs1 with h1 | h1
    · subst h1; exact hc0'.ne (by linear_combination kre)
    · have h1s : 0 < 1 - s := by linarith
      have him : (P.qC.eval z).im = 0 := by
        rcases mul_eq_zero.mp kim with h | h
        · linarith
        · exact h
      have hre := hcirc z hzn him
      nlinarith [mul_nonneg hs0 (neg_nonneg.mpr hc0'.le)]

/-- Galí (2015), p. 174 (non-existence criterion): if all roots of `Q` lie in the open unit disc,
`q` has no root in the closed unit disc. -/
theorem no_root_of_inCount_four {P : Par} (hP : P.Adm) (h4 : inCount P.QC = 4) :
    ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → P.qC.eval ζ ≠ 0 := by
  intro ζ hζ h0
  have hζ0 : ζ ≠ 0 := by
    rintro rfl; rw [qC_eval_zero] at h0; exact (c0_neg hP).ne (by exact_mod_cast h0)
  have hroot : ζ⁻¹ ∈ P.QC.roots := (mem_roots (QC_ne_zero hP)).mpr (by
    rw [IsRoot, eval_QC_eq P (inv_ne_zero hζ0), inv_inv, h0, mul_zero])
  have hall : P.QC.roots.filter (fun z => ‖z‖ < 1) = P.QC.roots :=
    Multiset.eq_of_le_of_card_le (Multiset.filter_le _ _) (by
      rw [card_roots_QC hP]; exact h4.ge)
  rw [← hall, Multiset.mem_filter, norm_inv] at hroot
  have hn : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
  have : 1 ≤ ‖ζ‖⁻¹ := one_le_inv_iff₀.mpr ⟨hn, hζ⟩
  linarith [hroot.2]

end Par

/-- Galí (2015), Fig. 6.1, p. 175 (correction): an admissible parameter point violating the
p. 174 condition at which the failure is non-existence: `β = 9/10`, `σ = 3/4`, `φ = 3`,
`α = 3/4`, `λ_p = 1/40`, `λ_w = 6/5`, `φ_p = 2/25`, `φ_w = 31/50`, `φ_y = 7/100`. -/
noncomputable def exNE : Par :=
  bookPar (9 / 10) (3 / 4) 3 (3 / 4) (1 / 40) (6 / 5) (2 / 25) (31 / 50) (7 / 100)

/-- Galí (2015), Fig. 6.1 (correction): the coefficients of `q` at `exNE`. -/
theorem exNE_coeffs : exNE.c0 = -1289 / 125 ∧ exNE.c1 = 449821 / 20000 ∧
    exNE.c2 = -9513 / 625 ∧ exNE.c3 = 140643 / 40000 ∧ exNE.c4 = -243 / 400 := by
  simp only [exNE, bookPar, Par.c0, Par.c1, Par.c2, Par.c3, Par.c4]
  norm_num

/-- Galí (2015), Fig. 6.1 (correction): `exNE` satisfies the sign conditions. -/
theorem exNE_adm : exNE.Adm :=
  bookPar_adm (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Galí (2015), Fig. 6.1 (correction): at `exNE` the p. 174 condition fails
(`LHS = 1939/2700 < 1`). -/
theorem exNE_lhs : (2 / 25 : ℝ) + 31 / 50 + 7 / 100 * (1 - 9 / 10) / (3 / 4 + (3 / 4 + 3)
    / (1 - 3 / 4)) * (1 / (1 / 40) + 1 / (6 / 5)) = 1939 / 2700 := by
  norm_num

/-- Galí (2015), Fig. 6.1 (correction): on the unit circle `q` is never a nonnegative real at
`exNE` (its imaginary part is `y · P(x)` with `P > 0` on `[−1, 1]`, and `q(±1) < 0`). -/
theorem exNE_circle : ∀ z : ℂ, ‖z‖ = 1 → (exNE.qC.eval z).im = 0 →
    (exNE.qC.eval z).re < 0 := by
  intro z hz him
  obtain ⟨x, y⟩ := z
  have hxy : x ^ 2 + y ^ 2 = 1 := by
    have h := Complex.sq_norm (⟨x, y⟩ : ℂ)
    rw [hz, Complex.normSq_mk] at h
    nlinarith
  obtain ⟨e0, e1, e2, e3, e4⟩ := exNE_coeffs
  rw [Par.eval_qC_mk] at him ⊢
  simp only [e0, e1, e2, e3, e4] at him ⊢
  have hx1 : x ≤ 1 := by nlinarith
  set Pc : ℝ := 449821 / 20000 + 2 * (-9513 / 625) * x + 140643 / 40000 * (4 * x ^ 2 - 1)
    + (-243 / 400) * (8 * x ^ 3 - 4 * x) with hPc
  have hG : 0 < 243 / 50 * x ^ 2 - 92043 / 10000 * x + 188073 / 10000 := by
    nlinarith [sq_nonneg (x - 1)]
  have hPpos : 0 < Pc := by
    have : Pc = 6707 / 40000 + (1 - x) * (243 / 50 * x ^ 2 - 92043 / 10000 * x
      + 188073 / 10000) := by rw [hPc]; ring
    rw [this]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1) hG.le]
  have himP : y * Pc = 0 := by
    rw [hPc]
    linear_combination him - (-(140643 / 40000) * y - 4 * (-243 / 400) * x * y) * hxy
  have hy : y = 0 := (mul_eq_zero.mp himP).resolve_right hPpos.ne'
  subst hy
  have hx : x = 1 ∨ x = -1 := by
    have : (x - 1) * (x + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  rcases hx with rfl | rfl <;> norm_num

/-- **Galí (2015), Fig. 6.1, p. 175 (correction): non-existence in the "Indeterminacy"
region.** At `exNE` (`LHS < 1`) `q` has no root in the closed unit disc and all four
eigenvalues of `Aʷ` lie inside the unit circle. -/
theorem exNE_no_root : (∀ ζ : ℂ, ‖ζ‖ ≤ 1 → exNE.qC.eval ζ ≠ 0) ∧
    ((exNE.Aw.map Complex.ofReal).charpoly.roots.filter (fun z => ‖z‖ < 1)).card = 4 := by
  have h4 := Par.inCount_QC_four exNE_adm exNE_circle
  refine ⟨Par.no_root_of_inCount_four exNE_adm h4, ?_⟩
  have hc : (-((exNE.A0.det : ℂ))⁻¹) ≠ 0 := by
    rw [exNE.det_A0]
    simp only [Complex.ofReal_neg, inv_neg, neg_neg, ne_eq, inv_eq_zero]
    exact_mod_cast (Par.c0_neg exNE_adm).ne
  rw [Par.charpoly_Aw exNE_adm, roots_C_mul _ hc]
  exact h4

/-- **Galí (2015), Fig. 6.1, p. 175 (correction).** At `exNE`, where the p. 174 condition
fails, system (24) with zero forcing and initial real wage gap `ω̃_{−1} = 1` has no bounded
solution, under any expectation system: the failure is non-existence, not multiplicity. -/
theorem exNE_no_bounded_solution {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω)
    (x : ℕ → Fin 4 → Ω → ℝ) : ¬ (Dyn.IsSol 𝔼 exNE 0 (fun _ => 1) x ∧ Fwd.VBounded x) :=
  fun h => Dyn.no_bounded_solution_of_no_root 𝔼 exNE_adm exNE_no_root.1 x h.1 h.2

/-- Galí (2015), §6.2.1 (baseline calibration): `λ_p` and `λ_w` for `β = 0.99`, `θ_p = θ_w = 3/4`,
`α = 1/4`, `ε_p = 9`, `ε_w = 4.5`, `φ = 5`. -/
theorem baseline_lambdas :
    (1 - 3 / 4 : ℝ) * (1 - 99 / 100 * (3 / 4)) / (3 / 4) * ((1 - 1 / 4) / (1 - 1 / 4 + 1 / 4 * 9))
      = 103 / 4800 ∧
    (1 - 3 / 4 : ℝ) * (1 - 99 / 100 * (3 / 4)) / (3 / 4 * (1 + 9 / 2 * 5)) = 103 / 28200 := by
  norm_num

/-- Galí (2015), Fig. 6.1, p. 175: the baseline calibration with `φ_p = 9/10`,
`φ_w = φ_y = 0` (so `LHS = 9/10 < 1`). -/
noncomputable def exBase : Par :=
  bookPar (99 / 100) 1 5 (1 / 4) (103 / 4800) (103 / 28200) (9 / 10) 0 0

/-- Galí (2015), Fig. 6.1 (baseline): `q(0) < 0 < q(9/10)` and `q(1) < 0`. -/
theorem exBase_signs : exBase.qr 0 < 0 ∧ 0 < exBase.qr (9 / 10) ∧ exBase.qr 1 < 0 := by
  simp only [exBase, bookPar, Par.qr, Par.c0, Par.c1, Par.c2, Par.c3, Par.c4]
  norm_num

/-- Galí (2015), Fig. 6.1 (baseline): `q` has two distinct real roots in `(0, 1)`, i.e. two
eigenvalues of `Aʷ` outside the unit circle (two stable roots for one predetermined
variable). -/
theorem exBase_two_roots : ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ < 9 / 10 ∧ 9 / 10 < r₂ ∧ r₂ < 1 ∧
    exBase.qr r₁ = 0 ∧ exBase.qr r₂ = 0 := by
  obtain ⟨h0, hm, h1⟩ := exBase_signs
  obtain ⟨r₁, ⟨a1, b1⟩, e1⟩ := intermediate_value_Ioo (show (0 : ℝ) ≤ 9 / 10 by norm_num)
    (exBase.continuous_qr).continuousOn (show (0 : ℝ) ∈ Set.Ioo (exBase.qr 0)
      (exBase.qr (9 / 10)) from ⟨h0, hm⟩)
  obtain ⟨r₂, ⟨a2, b2⟩, e2⟩ := intermediate_value_Ioo' (show (9 / 10 : ℝ) ≤ 1 by norm_num)
    (exBase.continuous_qr).continuousOn (show (0 : ℝ) ∈ Set.Ioo (exBase.qr 1)
      (exBase.qr (9 / 10)) from ⟨h1, hm⟩)
  exact ⟨r₁, r₂, a1, b1, a2, b2, e1, e2⟩

/-- **Galí (2015), Fig. 6.1, p. 175 (baseline: multiplicity).** At the baseline calibration
with `φ_p = 9/10`, `φ_w = φ_y = 0` the failure of the p. 174 condition is genuine
indeterminacy: with zero forcing and `ω̃_{−1} = 0` there are two different bounded
solutions of (24). -/
theorem exBase_multiplicity {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω) :
    ∃ x y : ℕ → Fin 4 → Ω → ℝ, x ≠ y ∧ Dyn.IsSol 𝔼 exBase 0 0 x ∧ Fwd.VBounded x ∧
      Dyn.IsSol 𝔼 exBase 0 0 y ∧ Fwd.VBounded y := by
  obtain ⟨r₁, r₂, a1, b1, a2, b2, e1, e2⟩ := exBase_two_roots
  obtain ⟨X, hX, h0, hb, hX0⟩ := Dyn.exists_mode_of_two_real_roots (P := exBase)
    (show r₁ ≠ r₂ by intro h; linarith) (by rw [abs_le]; constructor <;> linarith)
    (by rw [abs_le]; constructor <;> linarith) e1 e2
  obtain ⟨hz, hzb, hc, hcb, hne⟩ := Dyn.multiple_solutions_of_mode 𝔼 hX h0 hb hX0
  exact ⟨_, _, hne, hc, hcb, hz, hzb⟩

end Gali.StickyWagesPrices.Determinacy4
