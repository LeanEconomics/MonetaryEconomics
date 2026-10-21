/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.IRuleBasic
import OptimalPolicyRules.CubicRoots
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# Two remarks of Chapter 8: the generalised Taylor principle and the parity of `Δ(γ)`

Woodford (2003), *Interest and Prices*, Chapter 8, §3.1, p. 585 (with Chapter 4, §2.2,
pp. 255–256 and footnote 27), and Appendix G, §G.6, p. 727.

## The generalised Taylor principle (p. 585)

The book says that the optimal rule (3.7) "satisfies the Taylor principle, given that `φπ > 0`
and `ρ₁ > 1`", referring to the generalisation of Chapter 4, §2.2: for a rule with interest-rate
inertia the principle concerns the long-run (cumulative) response of the interest rate to a
permanent increase in inflation, and reads (Ch. 4, (2.9)) `φπ + (1 − β)φₓ/(4κ) > 1 − ρ`.

* `GenRule`: a general linear rule `iₜ = c₀ + ∑ⱼ₌₁ᴺ ρⱼ i_{t−j} + ∑ⱼ₌₀ᴺ φπ,ⱼ π_{t−j} +
  ¼∑ⱼ₌₀ᴺ φx,ⱼ x_{t−j}`; `GTP`: the generalised Taylor principle
  `φπ(1) + (1 − β)φₓ(1)/(4κ) > 1 − ρ(1)` (sums of the lag coefficients); `gap` its slack.
* Footnote 27 made exact: `symOne` is the symbol of the system (2.1), (3.1), rule at the
  eigenvalue `1`; `det_symOne` (`det = κσ · gap`), `gtp_iff_det_pos`; `shift_solves_iff`
  (adding constants `(a, b, d)` to a solution preserves (2.1), (3.1) and the rule iff
  `symOne (a, b, d) = 0`), `symOne_ker` (at `gap = 0` the vector `(1, (1 − β)/κ, 1)` is in the
  kernel), `eq_zero_of_symOne` (off the boundary the kernel is trivial), `unit_root_iff`
  (an eigenvalue exactly `1` iff `gap = 0`), `const_solution` (on the boundary the constant path
  solves the homogeneous system).
* p. 256: `gtp_iff_longrun` (for `ρ(1) < 1`, the principle in terms of the long-run responses
  `Φπ = φπ(1)/(1 − ρ(1))`, `Φₓ`), `gtp_of_superinertial` (for `ρ(1) ≥ 1` it holds
  automatically).
* The rule (3.7): `rule37_iff_genRule` ((3.7) is a `GenRule` with `N = 2`), `gap37`
  (`gap = φπ + ρ₁ − 1`), `gtp37_iff` (for every coefficient vector of the form (3.7), the
  principle holds iff `φπ + ρ₁ > 1`), **`rule37_gtp`** (at the optimal coefficients (3.8)–(3.9)
  the principle holds at every admissible calibration, with slack `κσ/λᵢ + κσ/β`),
  `rule37_gtp_determinate` (together with the determinacy already proved,
  `IRuleBasic.rule_determinate`), and the p. 256 reading for `ρ₁ ≥ 1`: `stepResp`,
  `rule37_step_rule`, **`rule37_step_tendsto`** (the response of `iₜ` to a permanent unit
  increase in inflation grows without bound).

## The parity remark of p. 727

The book infers from `Δ(0) < 0 < Δ(1)` and `Δ(±∞) = −∞` that the quartic `Δ(γ)` "admits either
one or three roots between 0 and 1". Exactly one occurs, and it is simple:

* `deltaQuartic_eq_disc`, `discC`: `Δ(γ) = −β⁴ disc(P(·, γ))`, the discriminant of the cubic
  `P(λ) = βγλ³ − (1 + γ + βγ)λ² + A₂λ − β⁻¹` (`CubicRoots.Precip`);
* `discQ_pos_of_lt`: if `0 < γ₀ < γ₁ ≤ 1` and the roots `λ₂, λ₃` are real at `γ₁`, they are real
  and distinct at `γ₀` (the larger root exceeds `β⁻¹`, where `∂P/∂γ = λ(βλ − 1)(λ − 1) > 0`);
* `deltaDeriv_eq`, `discJ_double`: at a double root `m` of `P` (simple root `l`),
  `Δ′(γ) = −4β⁴(βγ)³ m(βm − 1)(l − m)³(m − 1)`, which is positive;
* **`delta_unique_root`**: a unique `γ̄ ∈ (0, 1)` with `Δ(γ̄) = 0`; `Δ < 0` on `(0, γ̄)`,
  `Δ > 0` on `(γ̄, 1]`, `Δ′(γ̄) > 0`;
* **`deltaPoly_roots_Ioo`**: as a polynomial, the roots of `Δ` in `(0, 1)` counted with
  multiplicity are exactly `{γ̄}` (`deltaPoly_card_roots_Ioo`: one root); the boundary points
  are not roots. So "one or three" is true but "three" never occurs (correction).
-/

namespace Woodford.OptimalPolicyRules.Tidy

open Filter Topology Polynomial
open IRuleBasic (Calib rho1 rho2 phiPi phiX)
open CubicRoots CubicRoots.Assumptions

/-! ### The parity remark of p. 727 -/

namespace Parity

variable {β γ κ σ : ℝ}

/-- Woodford (2003), App. G.6, p. 726: the discriminant
`q²r² − 4pr³ − 4q³s − 27p²s² + 18pqrs` of the cubic `pλ³ + qλ² + rλ + s`. -/
def discC (p q r s : ℝ) : ℝ :=
  q ^ 2 * r ^ 2 - 4 * p * r ^ 3 - 4 * q ^ 3 * s - 27 * p ^ 2 * s ^ 2 + 18 * p * q * r * s

/-- Woodford (2003), App. G.6, p. 727 (tool): the derivative of `discC` along the direction
`(β, −(1 + β), 1, 0)` in which the coefficients of `P(·, γ)` move with `γ`. -/
def discJ (β p q r s : ℝ) : ℝ :=
  β * (-4 * r ^ 3 - 54 * p * s ^ 2 + 18 * q * r * s) -
    (1 + β) * (2 * q * r ^ 2 - 12 * q ^ 2 * s + 18 * p * r * s) +
      (2 * q ^ 2 * r - 12 * p * r ^ 2 + 18 * p * q * s)

/-- Woodford (2003), App. G.6, pp. 726–727: `Δ(γ) = −β⁴ disc(P(·, γ))`, where
`P(λ) = βγλ³ − (1 + γ + βγ)λ² + A₂λ − β⁻¹` has the roots `λ₁, λ₂, λ₃`. -/
theorem deltaQuartic_eq_disc (hβ : β ≠ 0) :
    deltaQuartic β γ κ σ =
      -β ^ 4 * discC (β * γ) (-(1 + γ + β * γ)) (coefA2 β γ κ σ) (-β⁻¹) := by
  unfold deltaQuartic discC coefA2
  field_simp
  ring

/-- Woodford (2003), App. G.6, p. 727: the coefficients of the quartic `Δ(γ)` (from `γ⁴`
down to `γ⁰`). -/
def dc4 (β : ℝ) : ℝ := -β ^ 4 * (1 - β) ^ 2

/-- Woodford (2003), App. G.6, p. 727: the `γ³` coefficient of `Δ`. -/
def dc3 (β κ σ : ℝ) : ℝ :=
  -(2 * β ^ 3 * ((1 + β ^ 2 - 4 * β) * (κ * σ) - (1 + β) * (1 - β) ^ 2))

/-- Woodford (2003), App. G.6, p. 727: the `γ²` coefficient of `Δ`. -/
def dc2 (β κ σ : ℝ) : ℝ :=
  -(β ^ 2 * ((κ * σ) ^ 2 * (1 - 10 * β + β ^ 2) + 2 * (κ * σ) * (1 + β) * (1 + β + β ^ 2)
    + (1 + 4 * β + β ^ 2) * (1 - β) ^ 2))

/-- Woodford (2003), App. G.6, p. 727: the `γ` coefficient of `Δ`. -/
def dc1 (β κ σ : ℝ) : ℝ :=
  β ^ 2 * (4 * (κ * σ) ^ 3 + 10 * (1 + β) * (κ * σ) ^ 2 + 4 * (2 + 2 * β ^ 2 - β) * (κ * σ)
    + 2 * (1 + β) * (1 - β) ^ 2)

/-- Woodford (2003), App. G.6, p. 727: the constant coefficient `Δ(0)`. -/
def dc0 (β κ σ : ℝ) : ℝ := -(β ^ 2 * (2 * β * (κ * σ) + (κ * σ) ^ 2 + 2 * (κ * σ) + (1 - β) ^ 2))

/-- Woodford (2003), App. G.6, p. 727: `Δ(γ)` as a polynomial in `γ`. -/
noncomputable def deltaPoly (β κ σ : ℝ) : ℝ[X] :=
  C (dc4 β) * X ^ 4 + C (dc3 β κ σ) * X ^ 3 + C (dc2 β κ σ) * X ^ 2 + C (dc1 β κ σ) * X +
    C (dc0 β κ σ)

/-- Woodford (2003), App. G.6, p. 727: the derivative `Δ′(γ)`. -/
def deltaDeriv (β γ κ σ : ℝ) : ℝ :=
  4 * dc4 β * γ ^ 3 + 3 * dc3 β κ σ * γ ^ 2 + 2 * dc2 β κ σ * γ + dc1 β κ σ

/-- Woodford (2003), App. G.6, p. 727: `deltaPoly` evaluates to the quartic `Δ(γ)`. -/
theorem eval_deltaPoly : (deltaPoly β κ σ).eval γ = deltaQuartic β γ κ σ := by
  simp only [deltaPoly, eval_add, eval_mul, eval_C, eval_pow, eval_X, dc4, dc3, dc2, dc1, dc0,
    deltaQuartic]
  ring

/-- Woodford (2003), App. G.6, p. 727: the derivative of `deltaPoly` is `deltaDeriv`. -/
theorem eval_derivative_deltaPoly :
    (derivative (deltaPoly β κ σ)).eval γ = deltaDeriv β γ κ σ := by
  simp only [deltaPoly, derivative_add, derivative_mul, derivative_C, derivative_X_pow,
    derivative_X, zero_mul, zero_add, eval_add, eval_mul, eval_C, eval_pow, eval_X,
    deltaDeriv, mul_one, derivative_C, add_zero]
  push_cast
  ring

/-- Woodford (2003), App. G.6, p. 727 (chain rule, exact): `Δ′(γ) = −β⁴ J(γ)` with
`J = ∂disc/∂p · β − ∂disc/∂q · (1 + β) + ∂disc/∂r` at the coefficients of `P(·, γ)`. -/
theorem deltaDeriv_eq (hβ : β ≠ 0) :
    deltaDeriv β γ κ σ =
      -β ^ 4 * discJ β (β * γ) (-(1 + γ + β * γ)) (coefA2 β γ κ σ) (-β⁻¹) := by
  unfold deltaDeriv discJ coefA2 dc4 dc3 dc2 dc1
  field_simp
  ring

/-- Woodford (2003), App. G.6, p. 727: at the coefficients of `a(λ − l)(λ − m)²` the derivative
of the discriminant along `(β, −(1 + β), 1, 0)` is `4a³m(βm − 1)(l − m)³(m − 1)`. -/
theorem discJ_double (β a l m : ℝ) :
    discJ β a (-(a * (l + 2 * m))) (a * (m ^ 2 + 2 * m * l)) (-(a * l * m ^ 2)) =
      4 * a ^ 3 * m * (β * m - 1) * (l - m) ^ 3 * (m - 1) := by
  unfold discJ
  ring

/-- Woodford (2003), App. G.6, p. 727: `∂P/∂γ = λ(βλ − 1)(λ − 1)`: `P(λ, γ₀) = P(λ, γ₁) +
(γ₀ − γ₁)λ(βλ − 1)(λ − 1)`. -/
theorem Precip_sub (β γ₀ γ₁ κ σ l : ℝ) :
    Precip β γ₀ κ σ l = Precip β γ₁ κ σ l + (γ₀ - γ₁) * (l * (β * l - 1) * (l - 1)) := by
  unfold Precip coefA2
  ring

/-- Woodford (2003), App. G.6, p. 726: if `P(λ) < 0` at some `λ > 1`, the roots `λ₂, λ₃` are
real and distinct (`S² − 4P₂₃ > 0`). -/
theorem discQ_pos_of_Precip_neg (h : Standing β γ κ σ) {l : ℝ} (hl : 1 < l)
    (hP : Precip β γ κ σ l < 0) : 0 < discQ β γ κ σ := by
  rw [Precip_factor h] at hP
  have h1 := (lam1_spec h).2.1
  have hβγ : 0 < β * γ := mul_pos h.beta_pos h.gamma_pos
  have hq : l ^ 2 - sumS β γ κ σ * l + prodP β γ κ σ < 0 := by
    by_contra hq
    push Not at hq
    have : 0 ≤ β * γ * (l - lam1 β γ κ σ) := mul_nonneg hβγ.le (by linarith)
    nlinarith [mul_nonneg this hq]
  unfold discQ
  nlinarith [sq_nonneg (2 * l - sumS β γ κ σ)]

/-- Woodford (2003), App. G.6, p. 726: if `λ₂, λ₃` are real (`S² − 4P₂₃ ≥ 0`), the larger one
`(S + √(S² − 4P₂₃))/2` is a root of `P` above `β⁻¹` (from `β²γλ₁P₂₃ = 1`, `γλ₁ < 1`). -/
theorem root_gt_inv_beta (h : Standing β γ κ σ) (hD : 0 ≤ discQ β γ κ σ) :
    ∃ l, β⁻¹ < l ∧ Precip β γ κ σ l = 0 := by
  have hβ := h.beta_pos
  have hS := two_lt_sumS h
  have hl1 := lam1_spec h
  have hv := vieta_const h
  set S := sumS β γ κ σ with hSd
  set P := prodP β γ κ σ with hPd
  set l1 := lam1 β γ κ σ with hl1d
  set s := Real.sqrt (discQ β γ κ σ) with hsd
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = S ^ 2 - 4 * P := by
    rw [hsd, Real.sq_sqrt hD]
    rfl
  refine ⟨(S + s) / 2, ?_, ?_⟩
  · have hP1 : β * γ * l1 * P * β = 1 := by
      rw [hv, inv_mul_cancel₀ hβ.ne']
    have hγl : γ * l1 < 1 := by
      have := mul_lt_mul_of_pos_left hl1.2.1 h.gamma_pos
      nlinarith [h.gamma_le_one]
    have hP : 0 < P := by
      by_contra hP0
      push Not at hP0
      have : 0 ≤ β * γ * l1 := by have := hl1.1; have := h.gamma_pos; positivity
      nlinarith [mul_nonpos_of_nonneg_of_nonpos this hP0]
    have hβP : 1 < β ^ 2 * P := by
      have hgl0 : 0 < γ * l1 := mul_pos h.gamma_pos hl1.1
      nlinarith [mul_lt_mul_of_pos_left hγl (by positivity : 0 < β ^ 2 * P)]
    have hl2 : P ≤ ((S + s) / 2) ^ 2 := by nlinarith
    have hpos : 0 < (S + s) / 2 := by linarith
    have hβl : 1 < β * ((S + s) / 2) := by
      by_contra hc
      push Not at hc
      have : (β * ((S + s) / 2)) ^ 2 ≤ 1 := by
        have h0 : 0 ≤ β * ((S + s) / 2) := by positivity
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hl2 (by positivity : (0 : ℝ) ≤ β ^ 2)]
    have := mul_lt_mul_of_pos_left hβl (inv_pos.mpr hβ)
    rwa [mul_one, ← mul_assoc, inv_mul_cancel₀ hβ.ne', one_mul] at this
  · rw [Precip_factor h]
    have : ((S + s) / 2) ^ 2 - S * ((S + s) / 2) + P = 0 := by nlinarith
    rw [← hSd, ← hPd, this, mul_zero]

/-- **Woodford (2003), App. G.6, p. 727 (monotonicity in `γ`)**: if `0 < γ₀ < γ₁ ≤ 1` and the
roots `λ₂, λ₃` are real at `γ₁` (`S² − 4P₂₃ ≥ 0`), they are real and distinct at `γ₀`. -/
theorem discQ_pos_of_lt {γ₀ γ₁ : ℝ} (h₀ : Standing β γ₀ κ σ) (h₁ : Standing β γ₁ κ σ)
    (hlt : γ₀ < γ₁) (hD : 0 ≤ discQ β γ₁ κ σ) : 0 < discQ β γ₀ κ σ := by
  obtain ⟨l, hl, hP⟩ := root_gt_inv_beta h₁ hD
  have hβ := h₀.beta_pos
  have hb1 : 1 < β⁻¹ := one_lt_inv₀ hβ |>.mpr h₀.beta_lt_one
  have hβl : 1 < β * l := by
    have := mul_lt_mul_of_pos_left hl hβ
    rwa [mul_inv_cancel₀ hβ.ne'] at this
  refine discQ_pos_of_Precip_neg h₀ (hb1.trans hl) ?_
  rw [Precip_sub β γ₀ γ₁ κ σ l, hP, zero_add]
  have : 0 < l * (β * l - 1) * (l - 1) := by
    have : 0 < l := by linarith
    have : 0 < β * l - 1 := by linarith
    have : 0 < l - 1 := by linarith
    positivity
  nlinarith

/-- Woodford (2003), App. G.6, p. 726, with `CubicRoots.deltaG_neg_iff`: `Δ(γ) < 0` iff the roots
`λ₂, λ₃` are real and distinct. -/
theorem deltaQuartic_neg_iff (h : Standing β γ κ σ) :
    deltaQuartic β γ κ σ < 0 ↔ 0 < discQ β γ κ σ := by
  rw [← deltaG_eq_quartic h.beta_pos.ne']
  exact deltaG_neg_iff h

/-- Woodford (2003), App. G.6, p. 726: `Δ(γ) = 0` iff `λ₂ = λ₃` (real double root). -/
theorem deltaQuartic_eq_zero_iff (h : Standing β γ κ σ) :
    deltaQuartic β γ κ σ = 0 ↔ discQ β γ κ σ = 0 := by
  rw [← deltaG_eq_quartic h.beta_pos.ne']
  exact deltaG_eq_zero_iff h

/-- Woodford (2003), App. G.6, p. 726: `Δ(γ) > 0` iff `λ₂, λ₃` are a complex pair. -/
theorem deltaQuartic_pos_iff (h : Standing β γ κ σ) :
    0 < deltaQuartic β γ κ σ ↔ discQ β γ κ σ < 0 := by
  rw [← deltaG_eq_quartic h.beta_pos.ne']
  exact deltaG_pos_iff h

/-- Woodford (2003), App. G.6, p. 727: at a root `γ ∈ (0, 1]` of `Δ`, the derivative is
positive, `Δ′(γ) = −4β⁴(βγ)³ m(βm − 1)(λ₁ − m)³(m − 1) > 0` with `m = S/2` the double root
(`m > 1`, `βm > 1` because `β²γλ₁m² = 1`, `λ₁ < 1 < m`). -/
theorem deltaDeriv_pos (h : Standing β γ κ σ) (h0 : deltaQuartic β γ κ σ = 0) :
    0 < deltaDeriv β γ κ σ := by
  have hβ := h.beta_pos
  have hγ := h.gamma_pos
  have hD := (deltaQuartic_eq_zero_iff h).mp h0
  have hS := two_lt_sumS h
  have hl1 := lam1_spec h
  have hv1 := vieta_sum h
  have hv2 := vieta_pair h
  have hv3 := vieta_const h
  set S := sumS β γ κ σ with hSd
  set P := prodP β γ κ σ with hPd
  set l := lam1 β γ κ σ with hld
  set m := S / 2 with hmd
  have hPm : P = m ^ 2 := by
    unfold discQ at hD
    rw [hmd]
    linarith
  have e1 : -(1 + γ + β * γ) = -(β * γ * (l + 2 * m)) := by rw [← hv1, hmd]; ring
  have e2 : coefA2 β γ κ σ = β * γ * (m ^ 2 + 2 * m * l) := by rw [← hv2, hPm, hmd]; ring
  have e3 : -β⁻¹ = -(β * γ * l * m ^ 2) := by rw [← hv3, hPm]
  rw [deltaDeriv_eq hβ.ne', e1, e2, e3, discJ_double]
  have hm1 : 1 < m := by rw [hmd]; linarith
  have hβm : 1 < β * m := by
    have hk : β * γ * l * m ^ 2 * β = 1 := by
      rw [← hPm, hv3, inv_mul_cancel₀ hβ.ne']
    have hγl : γ * l < 1 := by
      have := mul_lt_mul_of_pos_left hl1.2.1 hγ
      nlinarith [h.gamma_le_one]
    have hgl0 : 0 < γ * l := mul_pos hγ hl1.1
    have hbm2 : 0 < (β * m) ^ 2 := by positivity
    have hb3 := mul_lt_mul_of_pos_left hγl hbm2
    have hb2 : 1 < (β * m) ^ 2 := by nlinarith
    have h0 : 0 < β * m := by positivity
    nlinarith
  have hlm : 0 < m - l := by linarith [hl1.2.1]
  have e4 : (l - m) ^ 3 = -(m - l) ^ 3 := by ring
  rw [e4]
  have : 0 < β * m - 1 := by linarith
  have : 0 < m - 1 := by linarith
  have : 0 < m := by linarith
  have : 0 < β * γ := by positivity
  have : 0 < β ^ 4 := by positivity
  have hpos : 0 < 4 * (β * γ) ^ 3 * m * (β * m - 1) * (m - l) ^ 3 * (m - 1) := by positivity
  nlinarith

/-- **Woodford (2003), App. G.6, p. 727, the parity remark made exact.** Under `σ, κ > 0`,
`0 < β < 1`, the quartic `Δ(γ)` has exactly one root `γ̄` in `(0, 1)`; `Δ < 0` on `(0, γ̄)` (three
real roots `λ₁ < λ₂ < λ₃`), `Δ > 0` on `(γ̄, 1]` (a complex pair), and `Δ′(γ̄) > 0` (a simple
root). The book's "one or three roots between 0 and 1" is true, but three never occurs. -/
theorem delta_unique_root (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ g, 0 < g ∧ g < 1 ∧ deltaQuartic β g κ σ = 0 ∧
      (∀ γ', 0 < γ' → γ' ≤ 1 → deltaQuartic β γ' κ σ = 0 → γ' = g) ∧
      (∀ γ', 0 < γ' → γ' < g → deltaQuartic β γ' κ σ < 0) ∧
      (∀ γ', g < γ' → γ' ≤ 1 → 0 < deltaQuartic β γ' κ σ) ∧ 0 < deltaDeriv β g κ σ := by
  obtain ⟨g, hg0, hg1, hg⟩ := deltaQuartic_exists_root hβ hβ1 (mul_pos hκ hσ)
  have st : ∀ γ', 0 < γ' → γ' ≤ 1 → Standing β γ' κ σ := fun γ' h0 h1 =>
    ⟨hσ, hκ, hβ, hβ1, h0, h1⟩
  have hsg := st g hg0 hg1.le
  have hDg := (deltaQuartic_eq_zero_iff hsg).mp hg
  refine ⟨g, hg0, hg1, hg, fun γ' h0 h1 hz => ?_, fun γ' h0 hlt => ?_, fun γ' hlt h1 => ?_,
    deltaDeriv_pos hsg hg⟩
  · have hs' := st γ' h0 h1
    have hD' := (deltaQuartic_eq_zero_iff hs').mp hz
    rcases lt_trichotomy γ' g with hl | he | hl
    · have := discQ_pos_of_lt hs' hsg hl hDg.ge
      linarith
    · exact he
    · have := discQ_pos_of_lt hsg hs' hl hD'.ge
      linarith
  · exact (deltaQuartic_neg_iff (st γ' h0 (hlt.trans hg1).le)).mpr
      (discQ_pos_of_lt (st γ' h0 (hlt.trans hg1).le) hsg hlt hDg.ge)
  · have hs' := st γ' (hg0.trans hlt) h1
    by_contra hc
    have hD' : 0 ≤ discQ β γ' κ σ := by
      by_contra hn
      push Not at hn
      exact hc ((deltaQuartic_pos_iff hs').mpr hn)
    have := discQ_pos_of_lt hsg hs' hlt hD'
    linarith

/-- Woodford (2003), App. G.6, p. 727: `Δ` is a nonzero polynomial (`Δ(0) < 0`). -/
theorem deltaPoly_ne_zero (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) : deltaPoly β κ σ ≠ 0 := by
  intro h0
  have := congrArg (eval 0) h0
  rw [eval_deltaPoly, eval_zero] at this
  have := deltaQuartic_zero_neg (κ := κ) (σ := σ) hβ (mul_pos hκ hσ)
  linarith

/-- **Woodford (2003), App. G.6, p. 727, counted with multiplicity**: the multiset of roots of
the polynomial `Δ` lying in `(0, 1)` is exactly `{γ̄}` — one root, of multiplicity one. -/
theorem deltaPoly_roots_Ioo (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ g, 0 < g ∧ g < 1 ∧
      (deltaPoly β κ σ).roots.filter (fun γ' => 0 < γ' ∧ γ' < 1) = {g} := by
  obtain ⟨g, hg0, hg1, hg, huniq, -, -, hd⟩ := delta_unique_root hσ hκ hβ hβ1
  have hp := deltaPoly_ne_zero hσ hκ hβ
  refine ⟨g, hg0, hg1, Multiset.ext.mpr fun a => ?_⟩
  rw [Multiset.count_filter, count_roots, Multiset.count_singleton]
  by_cases ha : 0 < a ∧ a < 1
  · simp only [ha, and_self, ↓reduceIte]
    by_cases hag : a = g
    · subst hag
      simp only [↓reduceIte]
      have hr : (deltaPoly β κ σ).IsRoot a := by rw [IsRoot, eval_deltaPoly]; exact hg
      have h1 : 0 < rootMultiplicity a (deltaPoly β κ σ) := (rootMultiplicity_pos hp).mpr hr
      have h2 : ¬ 1 < rootMultiplicity a (deltaPoly β κ σ) := by
        rw [one_lt_rootMultiplicity_iff_isRoot hp]
        rintro ⟨-, hd'⟩
        rw [IsRoot, eval_derivative_deltaPoly] at hd'
        linarith
      omega
    · simp only [hag, ↓reduceIte]
      apply rootMultiplicity_eq_zero
      rw [IsRoot, eval_deltaPoly]
      exact fun hz => hag (huniq a ha.1 ha.2.le hz)
  · have hag : a ≠ g := by rintro rfl; exact ha ⟨hg0, hg1⟩
    simp only [ha, hag, ↓reduceIte]

/-- Woodford (2003), App. G.6, p. 727: **exactly one** root of `Δ` in `(0, 1)` counted with
multiplicity (so the book's "one or three" holds, with "three" impossible), and neither
boundary point `0`, `1` is a root. -/
theorem deltaPoly_card_roots_Ioo (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) :
    Multiset.card ((deltaPoly β κ σ).roots.filter (fun γ' => 0 < γ' ∧ γ' < 1)) = 1 ∧
      deltaQuartic β 0 κ σ < 0 ∧ 0 < deltaQuartic β 1 κ σ := by
  obtain ⟨g, -, -, h⟩ := deltaPoly_roots_Ioo hσ hκ hβ hβ1
  exact ⟨by rw [h, Multiset.card_singleton], deltaQuartic_zero_neg hβ (mul_pos hκ hσ),
    deltaQuartic_one_pos hβ hβ1 (mul_pos hκ hσ)⟩

end Parity

/-! ### The generalised Taylor principle (p. 585; Chapter 4, §2.2 and footnote 27) -/

namespace TaylorPrinciple

open Matrix

variable {Ω : Type*}

/-- Woodford (2003), Ch. 4, (2.8) and footnote 27, pp. 255–256, generalised to any finite number
of lags: the interest-rate rule
`iₜ = c₀ + ∑ⱼ₌₁ᴺ ρⱼ i_{t−j} + ∑ⱼ₌₀ᴺ φπ,ⱼ π_{t−j} + ¼ ∑ⱼ₌₀ᴺ φx,ⱼ x_{t−j}` at date `t`. -/
def GenRule (N : ℕ) (c0 : ℝ) (ρ φπ φx : ℕ → ℝ) (ı π x : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, ı t ω = c0 + ∑ j ∈ Finset.range N, ρ (j + 1) * ı (t - (j + 1)) ω +
    ∑ j ∈ Finset.range (N + 1), φπ j * π (t - j) ω +
      (∑ j ∈ Finset.range (N + 1), φx j * x (t - j) ω) / 4

/-- Woodford (2003), Ch. 4, p. 256: the sum `ρ(1) = ∑ⱼ ρⱼ` of the inertia coefficients. -/
def rhoSum (N : ℕ) (ρ : ℕ → ℝ) : ℝ := ∑ j ∈ Finset.range N, ρ (j + 1)

/-- Woodford (2003), Ch. 4, p. 256: the sum `φπ(1) = ∑ⱼ φπ,ⱼ` of the inflation coefficients. -/
def coefSum (N : ℕ) (φ : ℕ → ℝ) : ℝ := ∑ j ∈ Finset.range (N + 1), φ j

/-- Woodford (2003), Ch. 4, (2.9), p. 255, and footnote 27, p. 256 (**the generalised Taylor
principle**): `φπ(1) + (1 − β)φₓ(1)/(4κ) > 1 − ρ(1)` — the long-run increase in the interest
rate exceeds a permanent increase in inflation (with the associated long-run output gap
`x = (1 − β)π/κ` from (2.1)). -/
def GTP (β κ : ℝ) (N : ℕ) (ρ φπ φx : ℕ → ℝ) : Prop :=
  1 - rhoSum N ρ < coefSum N φπ + (1 - β) / (4 * κ) * coefSum N φx

/-- Woodford (2003), Ch. 4, (2.9): the slack `φπ(1) + (1 − β)φₓ(1)/(4κ) − (1 − ρ(1))` of the
generalised Taylor principle. -/
noncomputable def gap (β κ : ℝ) (N : ℕ) (ρ φπ φx : ℕ → ℝ) : ℝ :=
  coefSum N φπ + (1 - β) / (4 * κ) * coefSum N φx - (1 - rhoSum N ρ)

/-- Woodford (2003), Ch. 4, (2.9): the principle is `gap > 0`. -/
theorem gtp_iff_gap_pos (β κ : ℝ) (N : ℕ) (ρ φπ φx : ℕ → ℝ) :
    GTP β κ N ρ φπ φx ↔ 0 < gap β κ N ρ φπ φx := by
  unfold GTP gap
  constructor <;> intro h <;> linarith

/-- Woodford (2003), Ch. 4, footnote 27, p. 256: the symbol of the system (2.1), (3.1), rule at
the eigenvalue `μ = 1` (rows (2.1), (3.1), rule; columns `π, x, i`):
`[1 − β, −κ, 0; −σ, 0, σ; −φπ(1), −φₓ(1)/4, 1 − ρ(1)]`. -/
noncomputable def symOne (β κ σ : ℝ) (N : ℕ) (ρ φπ φx : ℕ → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 - β, -κ, 0; -σ, 0, σ; -coefSum N φπ, -(coefSum N φx / 4), 1 - rhoSum N ρ]

/-- **Woodford (2003), Ch. 4, footnote 27, p. 256**: `det symOne = κσ · gap`; the boundary of
the generalised Taylor principle is exactly where the system has the eigenvalue `1`. -/
theorem det_symOne {β κ : ℝ} (σ : ℝ) (hκ : κ ≠ 0) (N : ℕ) (ρ φπ φx : ℕ → ℝ) :
    (symOne β κ σ N ρ φπ φx).det = κ * σ * gap β κ N ρ φπ φx := by
  rw [Matrix.det_fin_three]
  simp [symOne, gap]
  field_simp
  ring

/-- Woodford (2003), Ch. 4, footnote 27: for `κσ > 0` the generalised Taylor principle holds iff
the symbol at `μ = 1` has positive determinant. -/
theorem gtp_iff_det_pos {β κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (N : ℕ) (ρ φπ φx : ℕ → ℝ) :
    GTP β κ N ρ φπ φx ↔ 0 < (symOne β κ σ N ρ φπ φx).det := by
  rw [det_symOne σ hκ.ne', gtp_iff_gap_pos]
  constructor
  · intro h; positivity
  · intro h
    exact pos_of_mul_pos_right h (mul_pos hκ hσ).le

/-- **Woodford (2003), Ch. 4, footnote 27 (the eigenvector)**: on the boundary `gap = 0` the
vector `(π, x, i) = (1, (1 − β)/κ, 1)` is in the kernel of the symbol at `μ = 1`. (The book's
output-gap entry "(1 − β)/4κ" is the product of this entry with the rule weight `¼`.) -/
theorem symOne_ker {β κ : ℝ} (σ : ℝ) (hκ : κ ≠ 0) {N : ℕ} {ρ φπ φx : ℕ → ℝ}
    (h0 : gap β κ N ρ φπ φx = 0) :
    symOne β κ σ N ρ φπ φx *ᵥ ![1, (1 - β) / κ, 1] = 0 := by
  unfold gap at h0
  funext r
  fin_cases r
  · simp [symOne, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    field_simp
    ring
  · simp [symOne, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · simp [symOne, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    linear_combination -h0

/-- Woodford (2003), Ch. 4, footnote 27: off the boundary (`gap ≠ 0`) the symbol at `μ = 1` has
trivial kernel: no constant shift of a solution is again a solution. -/
theorem eq_zero_of_symOne {β κ σ : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0) {N : ℕ} {ρ φπ φx : ℕ → ℝ}
    (hg : gap β κ N ρ φπ φx ≠ 0) {v : Fin 3 → ℝ} (hv : symOne β κ σ N ρ φπ φx *ᵥ v = 0) :
    v = 0 := by
  refine Matrix.eq_zero_of_mulVec_eq_zero ?_ hv
  rw [det_symOne σ hκ]
  exact mul_ne_zero (mul_ne_zero hκ hσ) hg

/-- **Woodford (2003), Ch. 4, footnote 27 (exact form)**: the system (2.1), (3.1), rule has the
eigenvalue `1` (a nonzero vector in the kernel of the symbol at `μ = 1`) iff the generalised
Taylor principle holds with equality. -/
theorem unit_root_iff {β κ σ : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0) (N : ℕ) (ρ φπ φx : ℕ → ℝ) :
    (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ symOne β κ σ N ρ φπ φx *ᵥ v = 0) ↔
      gap β κ N ρ φπ φx = 0 := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    by_contra hg
    exact hv0 (eq_zero_of_symOne hκ hσ hg hv)
  · intro h0
    refine ⟨![1, (1 - β) / κ, 1], fun h => ?_, symOne_ker σ hκ h0⟩
    have := congrFun h 0
    simp at this

/-- Woodford (2003), Ch. 4, footnote 27 (tool): a process shifted by a constant. -/
def shift (a : ℝ) (z : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun k ω => z k ω + a

/-- **Woodford (2003), Ch. 4, footnote 27, p. 256** ("the IS relation, the AS relation, and the
policy rule all share the property that the equation continues to be satisfied if inflation,
output, and interest rates are increased at all dates by the constant factors"): if `(π, x, i)`
solves (2.1), (3.1) and the rule at date `t`, then `(π + a, x + b, i + d)` does too iff
`symOne (a, b, d) = 0` (any expectation system, nonempty sample space). -/
theorem shift_solves_iff [Nonempty Ω] (𝔼 : ExpectationSystem Ω) (c : Calib) {N : ℕ}
    {c0 : ℝ} {ρ φπ φx : ℕ → ℝ} {u rn π x ı : ℕ → Ω → ℝ} {t : ℕ}
    (hAS : IRuleBasic.AS 𝔼 c u π x t) (hIS : IRuleBasic.IS 𝔼 c rn π x ı t)
    (hR : GenRule N c0 ρ φπ φx ı π x t) (a b d : ℝ) :
    (IRuleBasic.AS 𝔼 c u (shift a π) (shift b x) t ∧
      IRuleBasic.IS 𝔼 c rn (shift a π) (shift b x) (shift d ı) t ∧
      GenRule N c0 ρ φπ φx (shift d ı) (shift a π) (shift b x) t) ↔
      symOne c.β c.κ c.σ N ρ φπ φx *ᵥ ![a, b, d] = 0 := by
  obtain ⟨ω0⟩ := ‹Nonempty Ω›
  have hE : ∀ (e : ℝ) (z : ℕ → Ω → ℝ), 𝔼.E t (shift e z (t + 1)) =
      fun ω => 𝔼.E t (z (t + 1)) ω + e := by
    intro e z
    change 𝔼.E t (z (t + 1) + fun _ => e) = _
    rw [map_add, 𝔼.const]
    rfl
  have hRs : ∀ ω, (∑ j ∈ Finset.range N, ρ (j + 1) * shift d ı (t - (j + 1)) ω) =
        (∑ j ∈ Finset.range N, ρ (j + 1) * ı (t - (j + 1)) ω) + rhoSum N ρ * d ∧
      (∑ j ∈ Finset.range (N + 1), φπ j * shift a π (t - j) ω) =
        (∑ j ∈ Finset.range (N + 1), φπ j * π (t - j) ω) + coefSum N φπ * a ∧
      (∑ j ∈ Finset.range (N + 1), φx j * shift b x (t - j) ω) =
        (∑ j ∈ Finset.range (N + 1), φx j * x (t - j) ω) + coefSum N φx * b := by
    intro ω
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [shift, mul_add, Finset.sum_add_distrib, rhoSum, coefSum, Finset.sum_mul]
  have rAS : ∀ ω, π t ω = c.κ * x t ω + c.β * 𝔼.E t (π (t + 1)) ω + u t ω := fun ω => by
    have := congrFun hAS ω
    simpa using this
  have rIS : ∀ ω, x t ω = 𝔼.E t (x (t + 1)) ω -
      c.σ * (ı t ω - 𝔼.E t (π (t + 1)) ω - rn t ω) := fun ω => by
    have := congrFun hIS ω
    simpa using this
  have hmv : symOne c.β c.κ c.σ N ρ φπ φx *ᵥ ![a, b, d] = 0 ↔
      ((1 - c.β) * a - c.κ * b = 0 ∧ -c.σ * a + c.σ * d = 0 ∧
        -coefSum N φπ * a - coefSum N φx / 4 * b + (1 - rhoSum N ρ) * d = 0) := by
    constructor
    · intro h
      have h1 := congrFun h 0
      have h2 := congrFun h 1
      have h3 := congrFun h 2
      simp [symOne, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1 h2 h3
      refine ⟨by linarith, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      funext r
      fin_cases r <;> simp [symOne, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> linarith
  rw [hmv]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have e1 := congrFun h1 ω0
    have e2 := congrFun h2 ω0
    have e3 := h3 ω0
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hE] at e1 e2
    rw [(hRs ω0).1, (hRs ω0).2.1, (hRs ω0).2.2] at e3
    have r3 := hR ω0
    simp only [shift] at e1 e2 e3
    have := rAS ω0
    have := rIS ω0
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨funext fun ω => ?_, funext fun ω => ?_, fun ω => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hE, shift]
      linarith [rAS ω]
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hE, shift]
      linarith [rIS ω]
    · rw [(hRs ω).1, (hRs ω).2.1, (hRs ω).2.2]
      have r3 := hR ω
      simp only [shift]
      linarith

/-- **Woodford (2003), Ch. 4, footnote 27: on the boundary of the generalised Taylor principle
the constant path is an equilibrium of the homogeneous system** — `π = 1`, `x = (1 − β)/κ`,
`i = 1` at every date solve (2.1), (3.1) (no disturbances) and the rule (no intercept), so the
system has the eigenvalue `1`. -/
theorem const_solution (𝔼 : ExpectationSystem Ω) (c : Calib) (hκ : c.κ ≠ 0) {N : ℕ}
    {ρ φπ φx : ℕ → ℝ} (h0 : gap c.β c.κ N ρ φπ φx = 0) (t : ℕ) :
    IRuleBasic.AS 𝔼 c (fun _ _ => 0) (fun _ _ => 1) (fun _ _ => (1 - c.β) / c.κ) t ∧
      IRuleBasic.IS 𝔼 c (fun _ _ => 0) (fun _ _ => 1) (fun _ _ => (1 - c.β) / c.κ)
        (fun _ _ => 1) t ∧
      GenRule N 0 ρ φπ φx (fun (_ : ℕ) (_ : Ω) => (1 : ℝ)) (fun _ _ => 1)
        (fun _ _ => (1 - c.β) / c.κ) t := by
  have hk := symOne_ker c.σ hκ h0
  have r2 := congrFun hk 2
  simp only [mulVec, dotProduct, symOne, Fin.isValue, of_apply, cons_val', cons_val_fin_one,
    cons_val_zero, Fin.sum_univ_three, mul_one, cons_val_one, neg_mul, cons_val,
    Pi.zero_apply] at r2
  unfold rhoSum coefSum at r2
  refine ⟨funext fun ω => ?_, funext fun ω => ?_, fun ω => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, 𝔼.const]
    field_simp
    ring
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, 𝔼.const]
    ring
  · simp only [mul_one, ← Finset.sum_mul, zero_add]
    linarith

/-- Woodford (2003), Ch. 4, p. 256: for `ρ(1) < 1` the generalised Taylor principle says that
the long-run responses `Φπ = φπ(1)/(1 − ρ(1))`, `Φₓ = φₓ(1)/(1 − ρ(1))` satisfy
`Φπ + (1 − β)Φₓ/(4κ) > 1`. -/
theorem gtp_iff_longrun {β κ : ℝ} {N : ℕ} {ρ φπ φx : ℕ → ℝ} (hR : rhoSum N ρ < 1) :
    GTP β κ N ρ φπ φx ↔
      1 < coefSum N φπ / (1 - rhoSum N ρ) +
        (1 - β) / (4 * κ) * (coefSum N φx / (1 - rhoSum N ρ)) := by
  have hpos : 0 < 1 - rhoSum N ρ := by linarith
  have e : coefSum N φπ / (1 - rhoSum N ρ) +
      (1 - β) / (4 * κ) * (coefSum N φx / (1 - rhoSum N ρ)) =
        (coefSum N φπ + (1 - β) / (4 * κ) * coefSum N φx) / (1 - rhoSum N ρ) := by
    field_simp
  rw [e, one_lt_div hpos]
  rfl

/-- Woodford (2003), Ch. 4, p. 256: if `ρ(1) ≥ 1` ("the eventual cumulative increase in the
nominal interest rate is infinite if at least one of `φπ` or `φx` is positive"), the generalised
Taylor principle holds automatically (`0 < β < 1`, `κ > 0`, nonnegative long-run responses, one
positive). -/
theorem gtp_of_superinertial {β κ : ℝ} (hβ1 : β < 1) (hκ : 0 < κ) {N : ℕ} {ρ φπ φx : ℕ → ℝ}
    (hR : 1 ≤ rhoSum N ρ) (hπ : 0 ≤ coefSum N φπ) (hx : 0 ≤ coefSum N φx)
    (hpos : 0 < coefSum N φπ ∨ 0 < coefSum N φx) : GTP β κ N ρ φπ φx := by
  unfold GTP
  have hw : 0 < (1 - β) / (4 * κ) := by
    have : 0 < 1 - β := by linarith
    positivity
  rcases hpos with h | h
  · nlinarith [mul_nonneg hw.le hx]
  · nlinarith [mul_pos hw h]

/-! ### The optimal rule (3.7) -/

/-- Woodford (2003), (3.7), p. 584: the inertia coefficients of a rule of the form (3.7),
`i_{t−1}: ρ₁ + ρ₂`, `i_{t−2}: −ρ₂`. -/
def rho37 (r1 r2 : ℝ) : ℕ → ℝ := fun j => if j = 1 then r1 + r2 else if j = 2 then -r2 else 0

/-- Woodford (2003), (3.7): the inflation coefficients, `π_t: φπ`. -/
def pi37 (fp : ℝ) : ℕ → ℝ := fun j => if j = 0 then fp else 0

/-- Woodford (2003), (3.7): the output-gap coefficients (the rule responds to `Δx_t`):
`x_t: φₓ`, `x_{t−1}: −φₓ`. -/
def x37 (fx : ℝ) : ℕ → ℝ := fun j => if j = 0 then fx else if j = 1 then -fx else 0

/-- Woodford (2003), (3.7)–(3.9), p. 584: from date 2 on (where the history no longer enters),
the optimal rule `IRuleBasic.Rule` is the general rule with `N = 2`, intercept `(1 − ρ₁)i*`,
inertia `(ρ₁ + ρ₂, −ρ₂)`, inflation coefficient `φπ` and output-gap coefficients `(φₓ, −φₓ)`. -/
theorem rule37_iff_genRule (c : Calib) (xm1 im1 im2 : ℝ)
    (π x i : ℕ → Ω → ℝ) {t : ℕ} (ht : 2 ≤ t) :
    IRuleBasic.Rule c xm1 im1 im2 π x i t ↔
      GenRule 2 ((1 - rho1 c.β c.σ c.κ) * c.istar) (rho37 (rho1 c.β c.σ c.κ) (rho2 c.β))
        (pi37 (phiPi c.σ c.κ c.li)) (x37 (phiX c.σ c.lx c.li)) i π x t := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
  have l1 : IRuleBasic.lag im1 i (s + 2) = i (s + 1) := rfl
  have l2 : IRuleBasic.lag im2 (IRuleBasic.lag im1 i) (s + 2) = i s := rfl
  have l3 : IRuleBasic.lag xm1 x (s + 2) = x (s + 1) := rfl
  unfold IRuleBasic.Rule GenRule
  rw [l1, l2, l3, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, rho37, pi37, x37, Pi.add_apply,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  simp only [show s + 2 - (0 + 1) = s + 1 by omega, show s + 2 - (1 + 1) = s by omega,
    show s + 2 - 0 = s + 2 by omega]
  norm_num
  constructor <;> intro h <;> linarith

/-- Woodford (2003), (3.7): the long-run sums of a rule of the form (3.7): `ρ(1) = ρ₁`,
`φπ(1) = φπ`, `φₓ(1) = 0`. -/
theorem sums37 (r1 r2 fp fx : ℝ) :
    rhoSum 2 (rho37 r1 r2) = r1 ∧ coefSum 2 (pi37 fp) = fp ∧ coefSum 2 (x37 fx) = 0 := by
  simp only [rhoSum, coefSum, Finset.sum_range_succ, Finset.sum_range_zero, rho37, pi37, x37]
  norm_num

/-- Woodford (2003), (3.7), p. 585: for a rule of the form (3.7) the slack of the generalised
Taylor principle is `φπ + ρ₁ − 1` (the response to `Δxₜ` has no long-run effect). -/
theorem gap37 (β κ r1 r2 fp fx : ℝ) :
    gap β κ 2 (rho37 r1 r2) (pi37 fp) (x37 fx) = fp + r1 - 1 := by
  obtain ⟨h1, h2, h3⟩ := sums37 r1 r2 fp fx
  unfold gap
  rw [h1, h2, h3]
  ring

/-- **Woodford (2003), p. 585 ("given that `φπ > 0` and `ρ₁ > 1`")**: a rule of the form (3.7)
satisfies the generalised Taylor principle iff `φπ + ρ₁ > 1`; in particular whenever `φπ > 0`
and `ρ₁ ≥ 1`, or `φπ ≥ 0` and `ρ₁ > 1`. -/
theorem gtp37_iff (β κ r1 r2 fp fx : ℝ) :
    GTP β κ 2 (rho37 r1 r2) (pi37 fp) (x37 fx) ↔ 1 < fp + r1 := by
  rw [gtp_iff_gap_pos, gap37]
  constructor <;> intro h <;> linarith

/-- **Woodford (2003), p. 585: the optimal rule (3.7)–(3.9) satisfies the generalised Taylor
principle** at every admissible calibration, with slack `φπ + ρ₁ − 1 = κσ/λᵢ + κσ/β > 0`. -/
theorem rule37_gtp (c : Calib) (hc : c.Adm) :
    GTP c.β c.κ 2 (rho37 (rho1 c.β c.σ c.κ) (rho2 c.β)) (pi37 (phiPi c.σ c.κ c.li))
        (x37 (phiX c.σ c.lx c.li)) ∧
      gap c.β c.κ 2 (rho37 (rho1 c.β c.σ c.κ) (rho2 c.β)) (pi37 (phiPi c.σ c.κ c.li))
        (x37 (phiX c.σ c.lx c.li)) = c.κ * c.σ / c.li + c.κ * c.σ / c.β := by
  obtain ⟨hβ0, -, hσ, hκ, -, hli⟩ := hc
  have hg := gap37 c.β c.κ (rho1 c.β c.σ c.κ) (rho2 c.β) (phiPi c.σ c.κ c.li)
    (phiX c.σ c.lx c.li)
  have he : phiPi c.σ c.κ c.li + rho1 c.β c.σ c.κ - 1 = c.κ * c.σ / c.li + c.κ * c.σ / c.β := by
    unfold phiPi rho1
    ring
  refine ⟨?_, hg.trans he⟩
  rw [gtp_iff_gap_pos, hg, he]
  positivity

/-- **Woodford (2003), pp. 584–585: the generalised Taylor principle and determinacy for the
optimal rule.** At every admissible calibration the rule (3.7)–(3.9) satisfies the generalised
Taylor principle (`rule37_gtp`), its symbol at `μ = 1` is nonsingular (no unit eigenvalue,
`det = κσ(κσ/λᵢ + κσ/β) > 0`), and — the determinacy proved directly in
`IRuleBasic.rule_determinate` (Proposition 8.5) — for every bounded adapted disturbance and
every history there is exactly one bounded adapted equilibrium. -/
theorem rule37_gtp_determinate (𝔼 : ExpectationSystem Ω) (c : Calib) (hc : c.Adm) :
    GTP c.β c.κ 2 (rho37 (rho1 c.β c.σ c.κ) (rho2 c.β)) (pi37 (phiPi c.σ c.κ c.li))
        (x37 (phiX c.σ c.lx c.li)) ∧
      0 < (symOne c.β c.κ c.σ 2 (rho37 (rho1 c.β c.σ c.κ) (rho2 c.β))
        (pi37 (phiPi c.σ c.κ c.li)) (x37 (phiX c.σ c.lx c.li))).det ∧
      ∀ {rn u : ℕ → Ω → ℝ}, BoundedProc rn → 𝔼.Adapted rn → BoundedProc u → 𝔼.Adapted u →
        ∀ xm1 im1 im2 : ℝ, ∃! e : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
          IRuleBasic.RuleEqm 𝔼 c rn u xm1 im1 im2 e.1 e.2.1 e.2.2 ∧
            (𝔼.Adapted e.1 ∧ 𝔼.Adapted e.2.1 ∧ 𝔼.Adapted e.2.2) ∧
            (BoundedProc e.1 ∧ BoundedProc e.2.1 ∧ BoundedProc e.2.2) := by
  have hg := (rule37_gtp c hc).1
  refine ⟨hg, (gtp_iff_det_pos hc.2.2.2.1 hc.2.2.1 _ _ _ _).mp hg,
    fun hrb hra hub hua xm1 im1 im2 => IRuleBasic.rule_determinate 𝔼 c hc hrb hra hub hua
      xm1 im1 im2⟩

/-- Woodford (2003), Ch. 4, p. 256, for (3.7) (tool): the cumulative response of the interest
rate to a permanent unit increase in inflation from date 0 (output gap unchanged, interest rate
previously at `i*`): `(sₜ, sₜ₋₁)` with `sₜ = (ρ₁ + ρ₂)sₜ₋₁ − ρ₂sₜ₋₂ + φπ`, `s₋₁ = s₋₂ = 0`. -/
def stepResp (r1 r2 f : ℝ) : ℕ → ℝ × ℝ
  | 0 => (f, 0)
  | n + 1 => ((r1 + r2) * (stepResp r1 r2 f n).1 - r2 * (stepResp r1 r2 f n).2 + f,
      (stepResp r1 r2 f n).1)

/-- Woodford (2003), Ch. 4, p. 256 (tool): for `ρ₁ ≥ 1`, `ρ₂ ≥ 0`, `φπ > 0` the response is
nonnegative, increasing by at least `φπ` each period, so `sₜ ≥ (t + 1)φπ`. -/
theorem stepResp_bounds {r1 r2 f : ℝ} (h1 : 1 ≤ r1) (h2 : 0 ≤ r2) (hf : 0 < f) (n : ℕ) :
    0 ≤ (stepResp r1 r2 f n).2 ∧ f ≤ (stepResp r1 r2 f n).1 - (stepResp r1 r2 f n).2 ∧
      (n + 1) * f ≤ (stepResp r1 r2 f n).1 := by
  induction n with
  | zero => simp [stepResp]
  | succ n ih =>
    obtain ⟨hb, hd, ha⟩ := ih
    simp only [stepResp]
    have ha0 : 0 ≤ (stepResp r1 r2 f n).1 := by
      have : 0 ≤ ((n : ℝ) + 1) * f := by positivity
      linarith
    have m1 := mul_nonneg (by linarith : 0 ≤ r1 - 1) ha0
    have m2 := mul_nonneg h2 (by linarith : 0 ≤ (stepResp r1 r2 f n).1 - (stepResp r1 r2 f n).2)
    refine ⟨ha0, by nlinarith, ?_⟩
    push_cast
    nlinarith

/-- **Woodford (2003), Ch. 4, p. 256, for the optimal rule (3.7)**: with `πₜ = 1` from date 0
on, `xₜ = x₋₁` and `i₋₁ = i₋₂ = i*`, the rule (3.7) holds at every date for
`iₜ = i* + sₜ` (`stepResp` with `ρ₁, ρ₂, φπ` of (3.8)–(3.9)). -/
theorem rule37_step_rule (c : Calib) (xm1 : ℝ) (t : ℕ) :
    IRuleBasic.Rule c xm1 c.istar c.istar (fun (_ : ℕ) (_ : Ω) => (1 : ℝ)) (fun _ _ => xm1)
      (fun k _ => c.istar + (stepResp (rho1 c.β c.σ c.κ) (rho2 c.β) (phiPi c.σ c.κ c.li) k).1)
      t := by
  set s := stepResp (rho1 c.β c.σ c.κ) (rho2 c.β) (phiPi c.σ c.κ c.li) with hs
  have hl : ∀ k, IRuleBasic.lag c.istar (fun k (_ : Ω) => c.istar + (s k).1) k =
      fun _ => c.istar + (s k).2 := by
    intro k
    cases k with
    | zero => funext ω; simp [IRuleBasic.lag, hs, stepResp]
    | succ k => funext ω; simp [IRuleBasic.lag, hs, stepResp]
  have hx : IRuleBasic.lag xm1 (fun _ (_ : Ω) => xm1) t = fun _ => xm1 := by
    cases t <;> rfl
  unfold IRuleBasic.Rule
  rw [hl t, hx]
  funext ω
  cases t with
  | zero =>
    simp only [IRuleBasic.lag, hs, stepResp, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul]
    ring
  | succ k =>
    have h2 : IRuleBasic.lag c.istar (IRuleBasic.lag c.istar
        (fun k (_ : Ω) => c.istar + (s k).1)) (k + 1) = fun _ => c.istar + (s k).2 := by
      change IRuleBasic.lag c.istar (fun k (_ : Ω) => c.istar + (s k).1) k = _
      exact hl k
    rw [h2]
    simp only [hs, stepResp, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring

/-- **Woodford (2003), Ch. 4, p. 256, for the optimal rule (3.7) (`ρ₁ > 1`)**: "the eventual
cumulative increase in the nominal interest rate is infinite": the response `iₜ − i*` of
`rule37_step_rule` tends to `+∞` (every admissible calibration). -/
theorem rule37_step_tendsto (c : Calib) (hc : c.Adm) :
    Tendsto (fun t => (stepResp (rho1 c.β c.σ c.κ) (rho2 c.β) (phiPi c.σ c.κ c.li) t).1)
      atTop atTop := by
  obtain ⟨h1, h2, h3, -⟩ := IRuleBasic.coef_signs hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1
    hc.2.2.2.2.1 hc.2.2.2.2.2
  refine tendsto_atTop_mono (fun n => (stepResp_bounds h1.le (by linarith) h3 n).2.2) ?_
  exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const h3

end TaylorPrinciple

end Woodford.OptimalPolicyRules.Tidy
