/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MonetaryPolicyDesign.MoneyRuleSystem
import MonetaryPolicyDesign.InvariantSplit

/-!
# Root location for the money-supply system (34): Galí's footnote 14 proved

Galí (2015), Chapter 3, §3.4.2, p. 75 and fn. 14. Under an exogenous money supply the
equilibrium solves (34), `A_{M,0} x_t = A_{M,1} E_t x_{t+1} + B_M s_t`, and the book states,
supported only by a numerical exploration (fn. 14), that `A_M = A_{M,0}⁻¹ A_{M,1}` always has two
eigenvalues inside and one outside the unit circle. Here this is proved for all parameters.

With `b = 1 + ση` the eigenvalues of `A_M` are the roots of the characteristic cubic
`f(z) = (ση − z b)(β − z)(1 − z) − ηκ z(1 − z) + κ z²` (`MoneyRuleSystem.isRoot_charpoly_AM_iff`):
`f(0) = σηβ`, `f(1) = κ > 0`, `f(−1) = 2(1 + 2ση)(1 + β) + 2ηκ + κ > 0`, leading coefficient
`−b < 0`. So `f` has a real root `r > 1` and factors as `f(z) = −b (z − r)(z² + q₁ z + q₀)`;
evaluating at `0`, `1`, `−1` gives `b r q₀ = σηβ`, `b (r − 1)(1 + q₁ + q₀) = κ` and
`b (1 + r)(1 − q₁ + q₀) = f(−1)`, which are exactly the Schur–Cohn conditions
`|q₀| < 1`, `|q₁| < 1 + q₀` for the quadratic factor.

## Parameter domain

Everything holds for `σ ≥ 0`, `η ≥ 0`, `κ > 0`, `0 ≤ β ≤ 1`, which contains Galí's domain
(`σ > 0`, `κ > 0`, `0 < β < 1`, and `η ≥ 0`: Galí (2015), Ch. 2, eq. (4), p. 21 allows a zero
interest semi-elasticity of money demand). At `η = 0` one eigenvalue is `0` (still inside).

## Main results

* `exists_root_gt_one`, `charCubic_factor`: the real root `r > 1` and the factorisation.
* `quad_schurStable`: the quadratic factor satisfies the Schur–Cohn conditions.
* `bookDeterminacyClaim_holds`, `bookDeterminacyClaim_gali`: the book's claim
  `MoneyRuleSystem.BookDeterminacyClaim` is TRUE (stated before without proof).
* `norm_lt_one_of_quadratic`: a complex root of a real monic quadratic satisfying the Schur–Cohn
  conditions lies in the open unit disc.
* `AM_root_location`: counted with algebraic multiplicity over `ℂ`, `A_M` has exactly one
  eigenvalue outside the closed unit disc (`unstableCount = 1`), two in the open disc
  (`stableCount = 2`) and none on the unit circle (`NoUnit`).
* `real_eigenvalue_unique`: every real eigenvalue of modulus `≥ 1` is the root `r > 1`.

The analogous result for a more general model was proved analytically by Schabert and
Stoltenberg (2005), ECB Working Paper 458, Prop. 12 and App. 6.12.

Restated from the Chapter 3 project (`BasicNewKeynesianModel.MoneyRuleRoots`, namespace renamed;
this project does not import across projects). Used for Galí (2015), Ex. 4.4(c), p. 123.
-/

namespace Gali.MonetaryPolicyDesign.MoneyRuleRoots

open Polynomial MoneyRuleSystem InvariantSplit

/-! ### The real factorisation -/

/-- Galí (2015), p. 75: the coefficient of `z²` in the characteristic cubic. -/
def coef2 (σ η β κ : ℝ) : ℝ := σ * η + (1 + σ * η) * (1 + β) + η * κ + κ

/-- Galí (2015), p. 75: the coefficient of `z` in the characteristic cubic. -/
def coef1 (σ η β κ : ℝ) : ℝ := -(σ * η) * (1 + β) - (1 + σ * η) * β - η * κ

/-- Galí (2015), p. 75: `f(z) = −(1+ση) z³ + c₂ z² + c₁ z + σηβ`. -/
theorem charCubic_eq_coef (σ η β κ z : ℝ) :
    charCubic σ η β κ z =
      -(1 + σ * η) * z ^ 3 + coef2 σ η β κ * z ^ 2 + coef1 σ η β κ * z + σ * η * β := by
  rw [charCubic_expand, coef2, coef1]

/-- Galí (2015), p. 75: the linear coefficient `q₁ = r − c₂/(1+ση)` of the quadratic factor of
the cubic after the root `r` is divided out. -/
noncomputable def quadQ1 (σ η β κ r : ℝ) : ℝ := r - coef2 σ η β κ / (1 + σ * η)

/-- Galí (2015), p. 75: the constant `q₀ = r q₁ − c₁/(1+ση)` of the quadratic factor. -/
noncomputable def quadQ0 (σ η β κ r : ℝ) : ℝ := r * quadQ1 σ η β κ r - coef1 σ η β κ / (1 + σ * η)

/-- Galí (2015), p. 75: `(1+ση) q₁ = (1+ση) r − c₂`. -/
theorem quadQ1_mul {σ η β κ : ℝ} (hb : 1 + σ * η ≠ 0) (r : ℝ) :
    (1 + σ * η) * quadQ1 σ η β κ r = (1 + σ * η) * r - coef2 σ η β κ := by
  rw [quadQ1, mul_sub, mul_div_cancel₀ _ hb]

/-- Galí (2015), p. 75: `(1+ση) q₀ = (1+ση) r q₁ − c₁`. -/
theorem quadQ0_mul {σ η β κ : ℝ} (hb : 1 + σ * η ≠ 0) (r : ℝ) :
    (1 + σ * η) * quadQ0 σ η β κ r = (1 + σ * η) * r * quadQ1 σ η β κ r - coef1 σ η β κ := by
  rw [quadQ0, mul_sub, mul_div_cancel₀ _ hb, mul_assoc]

/-- Galí (2015), p. 75: if `f(r) = 0` the cubic factors as
`f(z) = −(1+ση)(z − r)(z² + q₁ z + q₀)`. -/
theorem charCubic_factor {σ η β κ r : ℝ} (hb : 1 + σ * η ≠ 0) (hr : charCubic σ η β κ r = 0)
    (z : ℝ) : charCubic σ η β κ z =
      -(1 + σ * η) * (z - r) * (z ^ 2 + quadQ1 σ η β κ r * z + quadQ0 σ η β κ r) := by
  have h1 := quadQ1_mul (κ := κ) (β := β) hb r
  have h0 := quadQ0_mul (κ := κ) (β := β) hb r
  rw [charCubic_eq_coef] at hr ⊢
  linear_combination (z ^ 2 - r ^ 2) * h1 + (z - r) * h0 + hr

/-- Galí (2015), p. 75: `f(−1) = 2(1 + 2ση)(1 + β) + 2ηκ + κ`. -/
theorem charCubic_neg_one (σ η β κ : ℝ) :
    charCubic σ η β κ (-1) = 2 * (1 + 2 * (σ * η)) * (1 + β) + 2 * (η * κ) + κ := by
  unfold charCubic; ring

/-- Galí (2015), p. 75: for `σ, η ≥ 0`, `κ > 0`, `0 ≤ β ≤ 1` the cubic has a real root strictly
greater than one (IVT between `f(1) = κ > 0` and `f(1 + c₂/(1+ση)) < 0`). -/
theorem exists_root_gt_one {σ η β κ : ℝ} (hσ : 0 ≤ σ) (hη : 0 ≤ η) (hκ : 0 < κ) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) : ∃ r, 1 < r ∧ charCubic σ η β κ r = 0 := by
  have hsη : 0 ≤ σ * η := mul_nonneg hσ hη
  have hηκ : 0 ≤ η * κ := mul_nonneg hη hκ.le
  set b := 1 + σ * η with hb
  have hb0 : 0 < b := by linarith
  have hc2 : 0 < coef2 σ η β κ := by
    unfold coef2; nlinarith
  have hc1 : coef1 σ η β κ ≤ 0 := by
    unfold coef1; nlinarith
  set R := 1 + coef2 σ η β κ / b with hR
  have hR1 : 1 < R := by have := div_pos hc2 hb0; linarith
  have hbR : b * R = b + coef2 σ η β κ := by rw [hR]; field_simp
  have hfR : charCubic σ η β κ R < 0 := by
    rw [charCubic_eq_coef]
    have hlead : -b * R ^ 3 + coef2 σ η β κ * R ^ 2 = -b * R ^ 2 := by
      have : -b * R ^ 3 + coef2 σ η β κ * R ^ 2 = R ^ 2 * (coef2 σ η β κ - b * R) := by ring
      rw [this, hbR]; ring
    have hR2 : 1 < R ^ 2 := by nlinarith
    have hc1R : coef1 σ η β κ * R ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc1 (by linarith)
    have hsηβ : σ * η * β ≤ σ * η := by nlinarith
    have hbR2 : b < b * R ^ 2 := by nlinarith
    rw [← hb]
    linarith
  have hcont : ContinuousOn (charCubic σ η β κ) (Set.Icc 1 R) := by
    unfold charCubic
    fun_prop
  have hmem : (0 : ℝ) ∈ Set.Ioo (charCubic σ η β κ R) (charCubic σ η β κ 1) := by
    rw [charCubic_one]
    exact ⟨hfR, hκ⟩
  obtain ⟨z, ⟨hz1, -⟩, hz⟩ := intermediate_value_Ioo' hR1.le hcont hmem
  exact ⟨z, hz1, hz⟩

/-- Galí (2015), p. 75: the values of the quadratic factor at `0`, `1`, `−1` (given a root
`r > 1`): `(1+ση) r q₀ = σηβ`, `(1+ση)(r − 1)(1 + q₁ + q₀) = κ`,
`(1+ση)(1 + r)(1 − q₁ + q₀) = f(−1)`. -/
theorem quad_values {σ η β κ r : ℝ} (hb : 1 + σ * η ≠ 0) (hr : charCubic σ η β κ r = 0) :
    (1 + σ * η) * r * quadQ0 σ η β κ r = σ * η * β ∧
      (1 + σ * η) * (r - 1) * (1 + quadQ1 σ η β κ r + quadQ0 σ η β κ r) = κ ∧
      (1 + σ * η) * (1 + r) * (1 - quadQ1 σ η β κ r + quadQ0 σ η β κ r) =
        charCubic σ η β κ (-1) := by
  have h0 := charCubic_factor hb hr 0
  have h1 := charCubic_factor hb hr 1
  have hm := charCubic_factor hb hr (-1)
  rw [charCubic_zero] at h0
  rw [charCubic_one] at h1
  refine ⟨by linear_combination -h0, by linear_combination -h1, by linear_combination -hm⟩

/-- Galí (2015), p. 75: for `σ, η ≥ 0`, `κ > 0`, `0 ≤ β ≤ 1` and a root `r > 1`, the quadratic
factor `z² + q₁ z + q₀` satisfies the Schur–Cohn conditions `|q₀| < 1`, `|q₁| < 1 + q₀`, and
`q₀ ≥ 0` (with `q₀ > 0` iff `σηβ > 0`). -/
theorem quad_schurStable {σ η β κ r : ℝ} (hσ : 0 ≤ σ) (hη : 0 ≤ η) (hκ : 0 < κ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hr1 : 1 < r) (hr : charCubic σ η β κ r = 0) :
    SchurStable (-quadQ1 σ η β κ r) (quadQ0 σ η β κ r) ∧ 0 ≤ quadQ0 σ η β κ r := by
  have hsη : 0 ≤ σ * η := mul_nonneg hσ hη
  have hηκ : 0 ≤ η * κ := mul_nonneg hη hκ.le
  have hb0 : 0 < 1 + σ * η := by linarith
  obtain ⟨h0, h1, hm⟩ := quad_values hb0.ne' hr
  rw [charCubic_neg_one] at hm
  have hbr : 0 < (1 + σ * η) * r := by positivity
  have hq0 : 0 ≤ quadQ0 σ η β κ r := by
    by_contra hneg
    push Not at hneg
    have : (1 + σ * η) * r * quadQ0 σ η β κ r < 0 := mul_neg_of_pos_of_neg hbr hneg
    have : 0 ≤ σ * η * β := mul_nonneg hsη hβ0
    linarith
  have hq0' : quadQ0 σ η β κ r < 1 := by
    by_contra hge
    push Not at hge
    have hsηβ : σ * η * β ≤ σ * η := by nlinarith
    have : (1 + σ * η) * r * 1 ≤ (1 + σ * η) * r * quadQ0 σ η β κ r :=
      mul_le_mul_of_nonneg_left hge hbr.le
    nlinarith
  have hp1 : 0 < 1 + quadQ1 σ η β κ r + quadQ0 σ η β κ r := by
    have hpos : 0 < (1 + σ * η) * (r - 1) := mul_pos hb0 (by linarith)
    refine pos_of_mul_pos_right (a := (1 + σ * η) * (r - 1)) ?_ hpos.le
    rw [h1]; exact hκ
  have hm1 : 0 < 1 - quadQ1 σ η β κ r + quadQ0 σ η β κ r := by
    have hpos : 0 < (1 + σ * η) * (1 + r) := mul_pos hb0 (by linarith)
    refine pos_of_mul_pos_right (a := (1 + σ * η) * (1 + r)) ?_ hpos.le
    rw [hm]; positivity
  refine ⟨⟨?_, ?_⟩, hq0⟩
  · rw [abs_lt]; constructor <;> linarith
  · rw [abs_lt]; constructor <;> linarith

/-- **Galí (2015), p. 75, fn. 14, PROVED**: for `σ, η ≥ 0`, `κ > 0`, `0 ≤ β ≤ 1` the
characteristic cubic factors as `−(1+ση)(z − r)(z² + q₁ z + q₀)` with `r > 1` and the quadratic
factor Schur stable: the book's (numerically supported) determinacy claim holds. -/
theorem bookDeterminacyClaim_holds {σ η β κ : ℝ} (hσ : 0 ≤ σ) (hη : 0 ≤ η) (hκ : 0 < κ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) : BookDeterminacyClaim σ η β κ := by
  obtain ⟨r, hr1, hr⟩ := exists_root_gt_one hσ hη hκ hβ0 hβ1
  have hb : 1 + σ * η ≠ 0 := by have := mul_nonneg hσ hη; linarith
  exact ⟨r, quadQ1 σ η β κ r, quadQ0 σ η β κ r, hr1, charCubic_factor hb hr,
    (quad_schurStable hσ hη hκ hβ0 hβ1 hr1 hr).1⟩

/-- **Galí (2015), p. 75, fn. 14, PROVED** on the book's parameter domain `σ > 0`, `η ≥ 0`,
`κ > 0`, `0 < β < 1`. -/
theorem bookDeterminacyClaim_gali {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) : BookDeterminacyClaim σ η β κ :=
  bookDeterminacyClaim_holds hσ.le hη hκ hβ0.le hβ1.le

/-! ### Complex roots -/

/-- Galí (2015), p. 75 (Schur–Cohn for a real quadratic): if `|b| < 1` and `|a| < 1 + b`, every
complex root of `ν² + a ν + b` lies in the open unit disc. -/
theorem norm_lt_one_of_quadratic {a b : ℝ} (hb : |b| < 1) (ha : |a| < 1 + b) {ν : ℂ}
    (hν : ν ^ 2 + a * ν + b = 0) : ‖ν‖ < 1 := by
  have hre := congrArg Complex.re hν
  have him := congrArg Complex.im hν
  simp only [sq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_im, Complex.mul_im, Complex.zero_re, Complex.zero_im] at hre him
  set x := ν.re
  set y := ν.im
  obtain ⟨hb1, hb2⟩ := abs_lt.mp hb
  obtain ⟨ha1, ha2⟩ := abs_lt.mp ha
  have hn : ‖ν‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have key : x ^ 2 + y ^ 2 < 1 := by
    by_cases hy : y = 0
    · rw [hy] at hre ⊢
      have hx : x * x + a * x + b = 0 := by linarith
      have hlt : x < 1 := by
        by_contra hx1
        push Not at hx1
        nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr (hb2.le.trans hx1))]
      have hgt : -1 < x := by
        by_contra hx1
        push Not at hx1
        nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (by linarith : (0 : ℝ) ≤ -x - b)]
      nlinarith
    · have h2 : 2 * x + a = 0 := by
        have : y * (2 * x + a) = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hy
        · exact h
      nlinarith
  rw [← hn] at key
  exact (sq_lt_one_iff₀ (norm_nonneg _)).mp key

/-- Galí (2015), p. 75: the real monic quadratic `z² + q₁ z + q₀`. -/
noncomputable def quadPoly (q₁ q₀ : ℝ) : ℝ[X] := X ^ 2 + C q₁ * X + C q₀

/-- Galí (2015), p. 75: a complex root `μ` of the quadratic satisfies `μ² + q₁ μ + q₀ = 0`. -/
theorem quadPoly_root {q₁ q₀ : ℝ} {μ : ℂ}
    (h : μ ∈ ((quadPoly q₁ q₀).map Complex.ofRealHom).roots) : μ ^ 2 + q₁ * μ + q₀ = 0 := by
  have h' := (mem_roots'.mp h).2
  simpa [quadPoly, IsRoot] using h'

/-- Galí (2015), p. 75: with `1 + ση ≠ 0` and `f(r) = 0`, the characteristic polynomial of `A_M`
is `(X − r)(X² + q₁ X + q₀)`. -/
theorem charpoly_AM_factor {σ η β κ r : ℝ} (hb : 1 + σ * η ≠ 0) (hr : charCubic σ η β κ r = 0) :
    (AM σ η β κ).charpoly = (X - C r) * quadPoly (quadQ1 σ η β κ r) (quadQ0 σ η β κ r) := by
  refine Polynomial.funext fun z => ?_
  rw [charpoly_AM_eval hb, charCubic_factor hb hr]
  simp only [quadPoly, eval_mul, eval_sub, eval_X, eval_C, eval_add, eval_pow]
  field_simp

/-- Galí (2015), p. 75: the eigenvalues of `A_M` (with multiplicity) are `r` and the two complex
roots of the quadratic factor. -/
theorem eigs_AM {σ η β κ r : ℝ} (hb : 1 + σ * η ≠ 0) (hr : charCubic σ η β κ r = 0) :
    eigs (AM σ η β κ) = {(r : ℂ)} +
      ((quadPoly (quadQ1 σ η β κ r) (quadQ0 σ η β κ r)).map Complex.ofRealHom).roots := by
  have hne : ((AM σ η β κ).charpoly.map Complex.ofRealHom) ≠ 0 :=
    ((Matrix.charpoly_monic _).map _).ne_zero
  rw [eigs, charpoly_map_ofReal]
  rw [charpoly_AM_factor hb hr, Polynomial.map_mul] at hne ⊢
  rw [roots_mul hne, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, roots_X_sub_C]
  rfl

/-- **Galí (2015), p. 75, fn. 14 — root location, PROVED**: for `σ, η ≥ 0`, `κ > 0`,
`0 ≤ β ≤ 1`, counted with algebraic multiplicity over `ℂ`, `A_M = A_{M,0}⁻¹ A_{M,1}` has no
eigenvalue on the unit circle, exactly one outside the closed unit disc and exactly two in the
open unit disc. -/
theorem AM_root_location {σ η β κ : ℝ} (hσ : 0 ≤ σ) (hη : 0 ≤ η) (hκ : 0 < κ) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) :
    NoUnit (AM σ η β κ) ∧ unstableCount (AM σ η β κ) = 1 ∧ stableCount (AM σ η β κ) = 2 := by
  obtain ⟨r, hr1, hr⟩ := exists_root_gt_one hσ hη hκ hβ0 hβ1
  have hb : 1 + σ * η ≠ 0 := by have := mul_nonneg hσ hη; linarith
  obtain ⟨hS, -⟩ := quad_schurStable hσ hη hκ hβ0 hβ1 hr1 hr
  set R := ((quadPoly (quadQ1 σ η β κ r) (quadQ0 σ η β κ r)).map Complex.ofRealHom).roots
    with hRdef
  have hRin : ∀ μ ∈ R, ‖μ‖ < 1 := by
    intro μ hμ
    refine norm_lt_one_of_quadratic hS.1 ?_ (quadPoly_root hμ)
    have := hS.2
    rwa [abs_neg] at this
  have hrn : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have he : eigs (AM σ η β κ) = {(r : ℂ)} + R := eigs_AM hb hr
  have hcard : Multiset.card R = 2 := by
    have h3 := card_eigs (AM σ η β κ)
    rw [he, Multiset.card_add, Multiset.card_singleton, Fintype.card_fin] at h3
    omega
  have hra : |r| = r := abs_of_pos (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · intro μ hμ
    rw [he, Multiset.mem_add, Multiset.mem_singleton] at hμ
    rcases hμ with rfl | hμ
    · rw [hrn]; exact hr1.ne'
    · exact (hRin μ hμ).ne
  · rw [unstableCount, he, Multiset.filter_add,
      Multiset.filter_eq_nil.mpr (fun μ hμ => not_lt.mpr (hRin μ hμ).le), add_zero,
      Multiset.filter_singleton]
    simp [hra, hr1]
  · rw [stableCount, he, Multiset.filter_add, Multiset.filter_eq_self.mpr hRin,
      Multiset.filter_singleton]
    simp [hra, hr1.le, hcard]

/-- **Galí (2015), p. 75 — root location on the book's domain** (`σ > 0`, `η ≥ 0`, `κ > 0`,
`0 < β < 1`): one eigenvalue of `A_M` outside the closed unit disc, two inside the open disc,
none on the circle. -/
theorem AM_root_location_gali {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    NoUnit (AM σ η β κ) ∧ unstableCount (AM σ η β κ) = 1 ∧ stableCount (AM σ η β κ) = 2 :=
  AM_root_location hσ.le hη hκ hβ0.le hβ1.le

/-- Galí (2015), p. 75: the real eigenvalue outside the unit circle is unique: every real root of
the cubic with `|z| ≥ 1` equals the root `r > 1`. -/
theorem real_eigenvalue_unique {σ η β κ r z : ℝ} (hσ : 0 ≤ σ) (hη : 0 ≤ η) (hκ : 0 < κ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hr1 : 1 < r) (hr : charCubic σ η β κ r = 0)
    (hz : charCubic σ η β κ z = 0) (hz1 : 1 ≤ |z|) : z = r := by
  have hb : 1 + σ * η ≠ 0 := by have := mul_nonneg hσ hη; linarith
  obtain ⟨hS, -⟩ := quad_schurStable hσ hη hκ hβ0 hβ1 hr1 hr
  rw [charCubic_factor hb hr, mul_eq_zero, mul_eq_zero] at hz
  rcases hz with (h | h) | h
  · exact absurd (neg_eq_zero.mp h) hb
  · linarith
  · have hn := norm_lt_one_of_quadratic hS.1 (by have := hS.2; rwa [abs_neg] at this)
      (ν := (z : ℂ)) (by exact_mod_cast h)
    rw [Complex.norm_real, Real.norm_eq_abs] at hn
    linarith

end Gali.MonetaryPolicyDesign.MoneyRuleRoots
