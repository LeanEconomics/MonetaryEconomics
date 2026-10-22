/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.LinksTidy
import Monetarism.TidyR5BK
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Order.IntermediateValue

/-!
# Galí's determinacy theorem for the money rule, proved in this project

Cochrane (2023), Ch. 19, §19.1, p. 435 (the sticky-price New-Keynesian alternative to the
monetarist models of Chapter 19) and §19.2, pp. 436–438 (the money-growth rule). The module
`LinksTidy` restates Galí's (2015) money-rule system (34), its row equivalence and its equilibrium
notion (`LinksTidy.GaliMoneyRule.System34`, `LinksTidy.GaliMoneyRule.Equil34`) but not Galí's
determinacy theorem. Here that theorem is proved, for the SAME definitions, using the general
Blanchard–Kahn theorem `TidyR5BK.GeneralBK.determinate_of`.

Restated from the Galí Chapter 4 project (its modules MoneyRuleSystem,
MoneyRuleRoots and MoneyRuleDeterminacy of the MonetaryPolicyDesign library), namespace
renamed and merged into one module; the matrices `A_{M,0}`, `A_{M,1}`, `B_M`, the system (34),
`Predetermined` and `Equil34` are NOT copied but taken from `LinksTidy.GaliMoneyRule`, so the
determinacy result below is a statement about the equilibrium notion already in this project.

## Main results

* `bookDeterminacyClaim_holds`: Galí's fn. 14 root count: `A_M = A_{M,0}⁻¹A_{M,1}` has one
  eigenvalue outside and two inside the unit circle (`AM_root_location`).
* `Abk_determinate` (`η > 0`) and `B2_determinate` (`η = 0`): the Blanchard–Kahn conditions.
* `system34_existsUnique`: for `σ > 0`, `η ≥ 0`, `κ > 0`, `0 < β ≤ 1`, bounded adapted shocks and
  any `l̂_{−1}`, (34) has exactly one bounded adapted equilibrium with predetermined real balances,
  `LinksTidy.GaliMoneyRule.Equil34`, for every `ExpectationSystem`.
* `system34_and_flex_existsUnique`: the sticky-price and flexible-price
  (`LinksTidy.GaliMoneyRule.flex_existsUnique`) models are both determinate under the same money
  rule.
-/

namespace Cochrane.Monetarism.TidyR5MoneyRule

open Polynomial LinksTidy.GaliMoneyRule TidyR5BK.InvariantSplit TidyR5BK.GeneralBKForward
  TidyR5BK.GeneralBK
open scoped Matrix

/-! ### The characteristic cubic (restated from the Galí Chapter 4 project) -/


/-- Galí (2015), p. 75 (survey §3.1): the characteristic cubic
`f(z) = det(A_{M,1} − z A_{M,0}) = (ση − z(1+ση))(β−z)(1−z) − ηκz(1−z) + κz²`. -/
def charCubic (σ η β κ z : ℝ) : ℝ :=
  (σ * η - z * (1 + σ * η)) * (β - z) * (1 - z) - η * κ * z * (1 - z) + κ * z ^ 2

/-- Galí (2015), p. 75: `det(A_{M,1} − z A_{M,0})` is the characteristic cubic (exact). -/
theorem det_AM1_sub_smul_AM0 (σ η β κ z : ℝ) :
    (AM1 σ η β - z • AM0 σ η κ).det = charCubic σ η β κ z := by
  simp [Matrix.det_fin_three, AM0, AM1, charCubic]
  ring

/-- Galí (2015), p. 75: `det A_{M,0} = 1 + ση`. -/
theorem det_AM0 (σ η κ : ℝ) : (AM0 σ η κ).det = 1 + σ * η := by
  simp [Matrix.det_fin_three, AM0]

/-- Galí (2015), p. 75: `det A_{M,1} = σηβ`. -/
theorem det_AM1 (σ η β : ℝ) : (AM1 σ η β).det = σ * η * β := by
  simp [Matrix.det_fin_three, AM1]

/-- Galí (2015), p. 75: the matrix `A_M ≡ A_{M,0}⁻¹ A_{M,1}`. -/
noncomputable def AM (σ η β κ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (AM0 σ η κ)⁻¹ * AM1 σ η β

/-- Galí (2015), p. 75: `det(A_M − z I) = (1+ση)⁻¹ f(z)` when `1 + ση ≠ 0`. -/
theorem det_AM_sub_smul {σ η β κ : ℝ} (h : 1 + σ * η ≠ 0) (z : ℝ) :
    (AM σ η β κ - z • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det =
      (1 + σ * η)⁻¹ * charCubic σ η β κ z := by
  have hu : IsUnit (AM0 σ η κ).det := by rw [det_AM0]; exact h.isUnit
  have hfac : AM σ η β κ - z • (1 : Matrix (Fin 3) (Fin 3) ℝ) =
      (AM0 σ η κ)⁻¹ * (AM1 σ η β - z • AM0 σ η κ) := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hu, AM]
  rw [hfac, Matrix.det_mul, Matrix.det_nonsing_inv, det_AM0, Ring.inverse_eq_inv',
    det_AM1_sub_smul_AM0]

/-- Galí (2015), p. 75: the characteristic polynomial of `A_M` evaluated at `z` is
`−(1+ση)⁻¹ f(z)`, so the eigenvalues of `A_M` are exactly the roots of `f`. -/
theorem charpoly_AM_eval {σ η β κ : ℝ} (h : 1 + σ * η ≠ 0) (z : ℝ) :
    (AM σ η β κ).charpoly.eval z = -((1 + σ * η)⁻¹ * charCubic σ η β κ z) := by
  rw [Matrix.eval_charpoly, ← det_AM_sub_smul h]
  have : Matrix.scalar (Fin 3) z - AM σ η β κ =
      -(AM σ η β κ - z • (1 : Matrix (Fin 3) (Fin 3) ℝ)) := by
    rw [neg_sub, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
  rw [this, Matrix.det_neg]
  simp only [Fintype.card_fin]
  ring

/-- Galí (2015), p. 75: a real `z` is an eigenvalue of `A_M` iff `f(z) = 0`. -/
theorem isRoot_charpoly_AM_iff {σ η β κ : ℝ} (h : 1 + σ * η ≠ 0) (z : ℝ) :
    (AM σ η β κ).charpoly.IsRoot z ↔ charCubic σ η β κ z = 0 := by
  rw [Polynomial.IsRoot.def, charpoly_AM_eval h, neg_eq_zero, mul_eq_zero]
  simp [inv_eq_zero, h]

/-- Galí (2015), p. 75: the cubic expanded; its leading coefficient is `−(1+ση)`. -/
theorem charCubic_expand (σ η β κ z : ℝ) :
    charCubic σ η β κ z = -(1 + σ * η) * z ^ 3 +
      (σ * η + (1 + σ * η) * (1 + β) + η * κ + κ) * z ^ 2 +
      (-(σ * η) * (1 + β) - (1 + σ * η) * β - η * κ) * z + σ * η * β := by
  unfold charCubic
  ring

/-- Galí (2015), p. 75: `f(0) = σηβ`. -/
theorem charCubic_zero (σ η β κ : ℝ) : charCubic σ η β κ 0 = σ * η * β := by
  unfold charCubic; ring

/-- Galí (2015), p. 75: `f(1) = κ`. -/
theorem charCubic_one (σ η β κ : ℝ) : charCubic σ η β κ 1 = κ := by
  unfold charCubic; ring

/-- Galí (2015), p. 75: `f(0) > 0` and `f(1) > 0` for `σ, η, β, κ > 0`, and the leading
coefficient `−(1+ση)` is negative. -/
theorem charCubic_signs {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hβ : 0 < β) (hκ : 0 < κ) :
    0 < charCubic σ η β κ 0 ∧ 0 < charCubic σ η β κ 1 ∧ -(1 + σ * η) < 0 := by
  rw [charCubic_zero, charCubic_one]
  refine ⟨by positivity, hκ, ?_⟩
  have : 0 < σ * η := mul_pos hσ hη
  linarith

/-- Galí (2015), p. 75: the cubic has a real root strictly greater than one (IVT between
`f(1) = κ > 0` and a point where `f < 0`). -/
theorem charCubic_root_gt_one {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hβ : 0 < β)
    (hκ : 0 < κ) : ∃ z, 1 < z ∧ charCubic σ η β κ z = 0 := by
  set b := 1 + σ * η with hb
  set c₂ := σ * η + b * (1 + β) + η * κ + κ with hc₂
  have hsη : 0 < σ * η := mul_pos hσ hη
  have hb0 : 0 < b := by linarith
  have hc₂0 : 0 < c₂ := by
    have : 0 < η * κ := mul_pos hη hκ
    nlinarith
  set R := 1 + c₂ / b with hR
  have hR1 : 1 < R := by have := div_pos hc₂0 hb0; linarith
  have hbR : b * R = b + c₂ := by rw [hR]; field_simp
  have hfR : charCubic σ η β κ R < 0 := by
    rw [charCubic_expand]
    have hηκ : 0 < η * κ := mul_pos hη hκ
    have hsηβ : 0 < σ * η * β := by positivity
    have hlead : -b * R ^ 3 + c₂ * R ^ 2 = -b * R ^ 2 := by
      have : -b * R ^ 3 + c₂ * R ^ 2 = R ^ 2 * (c₂ - b * R) := by ring
      rw [this, hbR]; ring
    have hc1 : (-(σ * η) * (1 + β) - b * β - η * κ) * R ≤
        -(σ * η) * (1 + β) - b * β - η * κ := by
      have hneg : -(σ * η) * (1 + β) - b * β - η * κ < 0 := by nlinarith
      nlinarith
    have hR2 : 1 < R ^ 2 := by nlinarith
    have hsum : -(σ * η) * (1 + β) - b * β - η * κ + σ * η * β < 0 := by nlinarith
    have hfin : -b * R ^ 2 < 0 := by nlinarith
    calc -(1 + σ * η) * R ^ 3 + (σ * η + (1 + σ * η) * (1 + β) + η * κ + κ) * R ^ 2 +
          (-(σ * η) * (1 + β) - (1 + σ * η) * β - η * κ) * R + σ * η * β
        = (-b * R ^ 3 + c₂ * R ^ 2) +
          (-(σ * η) * (1 + β) - b * β - η * κ) * R + σ * η * β := by
          rw [hb, hc₂]
      _ < 0 := by rw [hlead]; linarith
  have hcont : ContinuousOn (charCubic σ η β κ) (Set.Icc 1 R) := by
    unfold charCubic
    fun_prop
  have hmem : (0 : ℝ) ∈ Set.Ioo (charCubic σ η β κ R) (charCubic σ η β κ 1) := by
    rw [charCubic_one]
    exact ⟨hfR, hκ⟩
  obtain ⟨z, ⟨hz1, -⟩, hz⟩ := intermediate_value_Ioo' hR1.le hcont hmem
  exact ⟨z, hz1, hz⟩

/-- Galí (2015), p. 75: for `σ, η, β, κ > 0`, `A_M` has a real eigenvalue strictly
greater than one (so at least one eigenvalue lies outside the unit circle). -/
theorem AM_has_eigenvalue_gt_one {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hβ : 0 < β)
    (hκ : 0 < κ) : ∃ z, 1 < z ∧ (AM σ η β κ).charpoly.IsRoot z := by
  obtain ⟨z, hz1, hz⟩ := charCubic_root_gt_one hσ hη hβ hκ
  have h : 1 + σ * η ≠ 0 := by have := mul_pos hσ hη; linarith
  exact ⟨z, hz1, (isRoot_charpoly_AM_iff h z).mpr hz⟩

/-- Galí (2015), p. 75: `det A_M = σηβ/(1+ση)`, the product of the three eigenvalues. -/
theorem det_AM {σ η β κ : ℝ} (h : 1 + σ * η ≠ 0) :
    (AM σ η β κ).det = σ * η * β / (1 + σ * η) := by
  rw [AM, Matrix.det_mul, Matrix.det_nonsing_inv, det_AM0, Ring.inverse_eq_inv', det_AM1]
  field_simp

/-- Galí (2015), p. 75: for `σ, η > 0` and `0 < β < 1`, the product of the eigenvalues of
`A_M` lies in `(0, 1)`. -/
theorem det_AM_pos_lt_one {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hβ : 0 < β)
    (hβ1 : β < 1) : 0 < (AM σ η β κ).det ∧ (AM σ η β κ).det < 1 := by
  have hsη : 0 < σ * η := mul_pos hσ hη
  have hb : 0 < 1 + σ * η := by linarith
  rw [det_AM hb.ne']
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hb]
  nlinarith

/-- Galí (2015), p. 75 and fn. 14: the book's determinacy claim: the cubic factors as
`−(1+ση)(z − r)(z² + q₁ z + q₀)` with `r > 1` and both roots of the quadratic factor inside the
unit circle (Schur–Cohn). The book supports it numerically only; it is proved in
`bookDeterminacyClaim_holds`. -/
def BookDeterminacyClaim (σ η β κ : ℝ) : Prop :=
  ∃ r q₁ q₀ : ℝ, 1 < r ∧
    (∀ z, charCubic σ η β κ z = -(1 + σ * η) * (z - r) * (z ^ 2 + q₁ * z + q₀)) ∧
    SchurStable (-q₁) q₀


/-! ### Root location (restated from the Galí Chapter 4 project) -/

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


/-! ### Determinacy (restated from the Galí Chapter 4 project) -/


/-! ### Tools -/

/-- Galí (2015), p. 75 (tool): the eigenvalues are invariant under a relabelling of the state. -/
theorem eigs_submatrix_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (M : Matrix κ κ ℝ) : eigs (M.submatrix e e) = eigs M := by
  unfold eigs
  rw [show (M.submatrix e e).map Complex.ofReal = Matrix.reindex e.symm e.symm
    (M.map Complex.ofReal) from rfl, Matrix.charpoly_reindex]

/-- Galí (2015), p. 75 (tool): if the stable count is one and a real eigenvector of a stable
eigenvalue has a non-zero predetermined component, the genericity condition holds (the stable
subspace is the line through that eigenvector). -/
theorem genericX_of_eigvec {Z X : Type*} [Fintype Z] [Fintype X] [DecidableEq Z]
    [DecidableEq X] {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} (hnu : NoUnit A) (hs : stableCount A = 1)
    {ρ : ℝ} (hρ : |ρ| < 1) {e : Z ⊕ X → ℝ} (he : A *ᵥ e = ρ • e) {j : X}
    (hej : e (Sum.inr j) ≠ 0) : GenericX A := by
  have he0 : e ≠ 0 := fun h => hej (by rw [h]; rfl)
  have hmem : e ∈ boundedOrbits A := by
    refine ⟨∑ k, |e k|, fun t i => ?_⟩
    rw [pow_mulVec_eigvec he t, Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
    calc |ρ| ^ t * |e i| ≤ 1 * |e i| :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (abs_nonneg _) hρ.le) (abs_nonneg _)
      _ = |e i| := one_mul _
      _ ≤ ∑ k, |e k| :=
          Finset.single_le_sum (f := fun k => |e k|) (fun k _ => abs_nonneg _)
            (Finset.mem_univ i)
  have hspan : Submodule.span ℝ {e} = boundedOrbits A := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hmem
    · rw [finrank_span_singleton he0, finrank_eq_stableCount hnu, hs]
  intro v hv hvx
  rw [← hspan, Submodule.mem_span_singleton] at hv
  obtain ⟨c, rfl⟩ := hv
  have h := hvx j
  rw [Pi.smul_apply, smul_eq_mul, mul_eq_zero] at h
  rcases h with h | h
  · rw [h, zero_smul]
  · exact absurd h hej

/-- Galí (2015), p. 75 (tool): the roots of `X² + (q₁/q₀) X + 1/q₀` are the reciprocals of the
roots of `X² + q₁ X + q₀`, so they lie OUTSIDE the closed unit disc when the latter satisfies the
Schur–Cohn conditions. -/
theorem norm_gt_one_of_recip {q₁ q₀ : ℝ} (hS : SchurStable (-q₁) q₀) (hq0 : q₀ ≠ 0) {μ : ℂ}
    (h : μ ∈ ((quadPoly (q₁ / q₀) q₀⁻¹).map Complex.ofRealHom).roots) : 1 < ‖μ‖ := by
  have h1 := quadPoly_root h
  have hq0c : (q₀ : ℂ) ≠ 0 := by exact_mod_cast hq0
  have hμ : μ ≠ 0 := by
    rintro rfl
    have : ((q₀⁻¹ : ℝ) : ℂ) = 0 := by simpa using h1
    exact hq0 (by exact_mod_cast inv_eq_zero.mp (by exact_mod_cast this))
  have h2 : (q₀ : ℂ) * μ ^ 2 + q₁ * μ + 1 = 0 := by
    have e : (q₀ : ℂ) * (μ ^ 2 + ((q₁ / q₀ : ℝ) : ℂ) * μ + ((q₀⁻¹ : ℝ) : ℂ)) =
        q₀ * μ ^ 2 + q₁ * μ + 1 := by
      push_cast
      field_simp
    rw [← e, h1, mul_zero]
  set ν := μ⁻¹ with hν
  have hνμ : ν * μ = 1 := inv_mul_cancel₀ hμ
  have h3 : ν ^ 2 + q₁ * ν + q₀ = 0 := by
    linear_combination ν ^ 2 * h2 - ((q₁ : ℂ) * ν + q₀ * (1 + ν * μ)) * hνμ
  have hn := norm_lt_one_of_quadratic hS.1 (by have := hS.2; rwa [abs_neg] at this) h3
  have hν0 : ν ≠ 0 := inv_ne_zero hμ
  have hμν : μ = ν⁻¹ := by rw [hν, inv_inv]
  rw [hμν, norm_inv]
  exact (one_lt_inv₀ (norm_pos_iff.mpr hν0)).mpr hn

/-! ### `η > 0`: the backward matrix `A_b = A_{M,1}⁻¹ A_{M,0}` -/

/-- Galí (2015), eq. (34), p. 75: with `A_{M,1}` invertible, (34) reads
`E_t x_{t+1} = A_b x_t − A_{M,1}⁻¹ B_M s_t` with `A_b = A_{M,1}⁻¹ A_{M,0}`. -/
noncomputable def Ab3 (σ η β κ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (AM1 σ η β)⁻¹ * AM0 σ η κ

/-- Galí (2015), p. 75: `A_{M,1}` is invertible iff `σηβ ≠ 0`; in particular for `η > 0`. -/
theorem isUnit_det_AM1 {σ η β : ℝ} (hσ : σ ≠ 0) (hη : η ≠ 0) (hβ : β ≠ 0) :
    IsUnit (AM1 σ η β).det := by
  rw [det_AM1]
  exact (mul_ne_zero (mul_ne_zero hσ hη) hβ).isUnit

/-- Galí (2015), p. 75: `A_{M,0}` is invertible whenever `1 + ση ≠ 0`. -/
theorem isUnit_det_AM0 {σ η κ : ℝ} (hb : 1 + σ * η ≠ 0) : IsUnit (AM0 σ η κ).det := by
  rw [det_AM0]
  exact hb.isUnit

/-- Galí (2015), p. 75: the backward matrix is the inverse of `A_M = A_{M,0}⁻¹ A_{M,1}`, so its
eigenvalues are the reciprocals of those of `A_M`. -/
theorem Ab3_eq_inv_AM {σ η β κ : ℝ} (hb : 1 + σ * η ≠ 0) :
    Ab3 σ η β κ = (AM σ η β κ)⁻¹ := by
  rw [AM, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_AM0 hb), Ab3]

/-- Galí (2015), p. 75: `det(z A_{M,1} − A_{M,0}) = σηβ z³ + c₁ z² + c₂ z − (1+ση)`, the
reversed characteristic cubic `z³ f(1/z)`. -/
theorem det_pencil (σ η β κ z : ℝ) :
    (z • AM1 σ η β - AM0 σ η κ).det =
      σ * η * β * z ^ 3 + coef1 σ η β κ * z ^ 2 + coef2 σ η β κ * z - (1 + σ * η) := by
  simp [Matrix.det_fin_three, AM0, AM1, coef1, coef2]
  ring

/-- Galí (2015), p. 75: with `f(r) = 0`,
`det(z A_{M,1} − A_{M,0}) = −(1+ση)(1 − r z)(1 + q₁ z + q₀ z²)`. -/
theorem det_pencil_factor {σ η β κ r : ℝ} (hb : 1 + σ * η ≠ 0) (hr : charCubic σ η β κ r = 0)
    (z : ℝ) : (z • AM1 σ η β - AM0 σ η κ).det =
      -(1 + σ * η) * (1 - r * z) * (1 + quadQ1 σ η β κ r * z + quadQ0 σ η β κ r * z ^ 2) := by
  have h1 := quadQ1_mul (κ := κ) (β := β) hb r
  have h0 := quadQ0_mul (κ := κ) (β := β) hb r
  rw [det_pencil]
  rw [charCubic_eq_coef] at hr
  linear_combination (z - r ^ 2 * z ^ 3) * h1 + (z ^ 2 - r * z ^ 3) * h0 + z ^ 3 * hr

/-- Galí (2015), p. 75: `det A_{M,1} · det(z − A_b) = det(z A_{M,1} − A_{M,0})`. -/
theorem det_AM1_mul_charpoly_Ab3 {σ η β κ : ℝ} (hu : IsUnit (AM1 σ η β).det) (z : ℝ) :
    (AM1 σ η β).det * (Ab3 σ η β κ).charpoly.eval z = (z • AM1 σ η β - AM0 σ η κ).det := by
  rw [Matrix.eval_charpoly, ← Matrix.det_mul]
  congr 1
  rw [Matrix.mul_sub, Ab3, Matrix.mul_nonsing_inv_cancel_left _ _ hu, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

/-- Galí (2015), p. 75: for `σ, η, β ≠ 0`, `1 + ση ≠ 0` and a root `r` of the cubic, the
characteristic polynomial of `A_b` is `(X − r⁻¹)(X² + (q₁/q₀) X + q₀⁻¹)`. -/
theorem charpoly_Ab3_factor {σ η β κ r : ℝ} (hσ : σ ≠ 0) (hη : η ≠ 0) (hβ : β ≠ 0)
    (hb : 1 + σ * η ≠ 0) (hr : charCubic σ η β κ r = 0) :
    (Ab3 σ η β κ).charpoly = (X - C r⁻¹) *
      quadPoly (quadQ1 σ η β κ r / quadQ0 σ η β κ r) (quadQ0 σ η β κ r)⁻¹ := by
  have hu := isUnit_det_AM1 hσ hη hβ
  obtain ⟨hv0, -, -⟩ := quad_values hb hr
  have hsηβ : σ * η * β ≠ 0 := mul_ne_zero (mul_ne_zero hσ hη) hβ
  have hr0 : r ≠ 0 := by rintro rfl; apply hsηβ; rw [← hv0]; ring
  have hq0 : quadQ0 σ η β κ r ≠ 0 := by rintro h; apply hsηβ; rw [← hv0, h]; ring
  refine Polynomial.funext fun z => ?_
  have e := det_AM1_mul_charpoly_Ab3 (κ := κ) hu z
  rw [det_pencil_factor hb hr, det_AM1, ← hv0] at e
  have hden : (1 + σ * η) * r * quadQ0 σ η β κ r ≠ 0 := by rw [hv0]; exact hsηβ
  simp only [quadPoly, eval_mul, eval_sub, eval_X, eval_C, eval_add, eval_pow]
  have key : (1 + σ * η) * r * quadQ0 σ η β κ r * ((z - r⁻¹) * (z ^ 2 +
      quadQ1 σ η β κ r / quadQ0 σ η β κ r * z + (quadQ0 σ η β κ r)⁻¹)) =
      -(1 + σ * η) * (1 - r * z) * (1 + quadQ1 σ η β κ r * z + quadQ0 σ η β κ r * z ^ 2) := by
    field_simp
    ring
  exact mul_left_cancel₀ hden (e.trans key.symm)

/-- Galí (2015), p. 75, fn. 14 (backward form, `η > 0`): for `σ, η, β > 0`, `κ > 0`, `β ≤ 1`,
`A_b = A_M⁻¹` has exactly one eigenvalue in the open unit disc (namely `1/r`), two outside the
closed disc and none on the unit circle (with algebraic multiplicity over `ℂ`). -/
theorem Ab3_root_location {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) :
    NoUnit (Ab3 σ η β κ) ∧ stableCount (Ab3 σ η β κ) = 1 ∧ unstableCount (Ab3 σ η β κ) = 2 := by
  obtain ⟨r, hr1, hr⟩ := exists_root_gt_one hσ.le hη.le hκ hβ0.le hβ1
  have hb : 1 + σ * η ≠ 0 := by have := mul_pos hσ hη; linarith
  obtain ⟨hS, -⟩ := quad_schurStable hσ.le hη.le hκ hβ0.le hβ1 hr1 hr
  obtain ⟨hv0, -, -⟩ := quad_values hb hr
  have hq0 : quadQ0 σ η β κ r ≠ 0 := by
    intro h
    rw [h, mul_zero] at hv0
    have := mul_pos (mul_pos hσ hη) hβ0
    linarith
  set R := ((quadPoly (quadQ1 σ η β κ r / quadQ0 σ η β κ r)
    (quadQ0 σ η β κ r)⁻¹).map Complex.ofRealHom).roots with hRdef
  have hRout : ∀ μ ∈ R, 1 < ‖μ‖ := fun μ hμ => norm_gt_one_of_recip hS hq0 hμ
  have he : eigs (Ab3 σ η β κ) = {((r⁻¹ : ℝ) : ℂ)} + R := by
    have hne : ((Ab3 σ η β κ).charpoly.map Complex.ofRealHom) ≠ 0 :=
      ((Matrix.charpoly_monic _).map _).ne_zero
    rw [eigs, charpoly_map_ofReal]
    rw [charpoly_Ab3_factor hσ.ne' hη.ne' hβ0.ne' hb hr, Polynomial.map_mul] at hne ⊢
    rw [roots_mul hne, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, roots_X_sub_C]
    rfl
  have hr0 : 0 < r := by linarith
  have hrlt : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr1
  have hra : |r⁻¹| = r⁻¹ := abs_of_pos (inv_pos.mpr hr0)
  have hcard : Multiset.card R = 2 := by
    have h3 := card_eigs (Ab3 σ η β κ)
    rw [he, Multiset.card_add, Multiset.card_singleton, Fintype.card_fin] at h3
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro μ hμ
    rw [he, Multiset.mem_add, Multiset.mem_singleton] at hμ
    rcases hμ with rfl | hμ
    · rw [Complex.norm_real, Real.norm_eq_abs, hra]; exact hrlt.ne
    · exact (hRout μ hμ).ne'
  · rw [stableCount, he, Multiset.filter_add,
      Multiset.filter_eq_nil.mpr (fun μ hμ => not_lt.mpr (hRout μ hμ).le), add_zero,
      Multiset.filter_singleton]
    simp [abs_of_pos hr0, hrlt]
  · rw [unstableCount, he, Multiset.filter_add, Multiset.filter_eq_self.mpr hRout,
      Multiset.filter_singleton]
    simp [abs_of_pos hr0, hrlt.le, hcard]

/-- Galí (2015), p. 75: the relabelling of `Fin 3` as `Fin 2 ⊕ Fin 1`: `ỹ_t, π_t`
non-predetermined (`Sum.inl 0`, `Sum.inl 1`), `l̂_{t−1}` predetermined (`Sum.inr 0`). -/
abbrev eS : Fin 2 ⊕ Fin 1 ≃ Fin 3 := finSumFinEquiv

/-- Galí (2015), eq. (34), p. 75: the backward matrix on the split state `Fin 2 ⊕ Fin 1`. -/
noncomputable def Abk (σ η β κ : ℝ) : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ :=
  (Ab3 σ η β κ).submatrix eS eS

/-- Galí (2015), p. 75: a real eigenvector of the pencil for the root `r`:
`A_{M,1} v = r A_{M,0} v` with `v = ((r − β)(r − 1), rκ(r − 1), r²κ)`. -/
def eigv3 (β κ r : ℝ) : Fin 3 → ℝ := ![(r - β) * (r - 1), r * κ * (r - 1), r ^ 2 * κ]

/-- Galí (2015), p. 75: `A_{M,1} v = r A_{M,0} v` when `f(r) = 0`. -/
theorem pencil_eigvec {σ η β κ r : ℝ} (hr : charCubic σ η β κ r = 0) :
    AM1 σ η β *ᵥ eigv3 β κ r = r • (AM0 σ η κ *ᵥ eigv3 β κ r) := by
  unfold charCubic at hr
  funext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, eigv3]
    linear_combination hr
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, eigv3]
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, eigv3]
    ring

/-- Galí (2015), p. 75: `A_b v = r⁻¹ v` (the stable eigenvector of the backward matrix). -/
theorem Ab3_eigvec {σ η β κ r : ℝ} (hu : IsUnit (AM1 σ η β).det) (hr0 : r ≠ 0)
    (hr : charCubic σ η β κ r = 0) : Ab3 σ η β κ *ᵥ eigv3 β κ r = r⁻¹ • eigv3 β κ r := by
  have h := pencil_eigvec (σ := σ) (η := η) hr
  have h0 : AM0 σ η κ *ᵥ eigv3 β κ r = r⁻¹ • (AM1 σ η β *ᵥ eigv3 β κ r) := by
    rw [h, smul_smul, inv_mul_cancel₀ hr0, one_smul]
  rw [Ab3, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

/-- Galí (2015), p. 75: the eigenvalues of the split backward matrix are those of `A_b`. -/
theorem eigs_Abk (σ η β κ : ℝ) : eigs (Abk σ η β κ) = eigs (Ab3 σ η β κ) :=
  eigs_submatrix_equiv eS _

/-- Galí (2015), p. 75, fn. 14 (`η > 0`): the Blanchard–Kahn conditions for (34): no eigenvalue
of the backward matrix on the unit circle, exactly one (= the number of predetermined variables)
in the open unit disc, and genericity (the stable eigenvector moves real balances). -/
theorem Abk_bk_conditions {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) :
    NoUnit (Abk σ η β κ) ∧ stableCount (Abk σ η β κ) = Fintype.card (Fin 1) ∧
      GenericX (Abk σ η β κ) := by
  obtain ⟨hnu, hs, -⟩ := Ab3_root_location hσ hη hκ hβ0 hβ1
  have hnu' : NoUnit (Abk σ η β κ) := by unfold NoUnit; rw [eigs_Abk]; exact hnu
  have hs' : stableCount (Abk σ η β κ) = 1 := by unfold stableCount; rw [eigs_Abk]; exact hs
  refine ⟨hnu', hs', ?_⟩
  obtain ⟨r, hr1, hr⟩ := exists_root_gt_one hσ.le hη.le hκ hβ0.le hβ1
  have hr0 : 0 < r := by linarith
  have hu := isUnit_det_AM1 hσ.ne' hη.ne' hβ0.ne'
  have hev : Abk σ η β κ *ᵥ (eigv3 β κ r ∘ eS) = r⁻¹ • (eigv3 β κ r ∘ eS) := by
    rw [Abk, Matrix.submatrix_mulVec_equiv, Function.comp_assoc, Equiv.self_comp_symm,
      Function.comp_id, Ab3_eigvec hu hr0.ne' hr]
    rfl
  refine genericX_of_eigvec hnu' hs' (ρ := r⁻¹) ?_ hev (j := 0) ?_
  · rw [abs_of_pos (inv_pos.mpr hr0)]; exact inv_lt_one_of_one_lt₀ hr1
  · change r ^ 2 * κ ≠ 0
    positivity

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- **Galí (2015), p. 75, fn. 14 (`η > 0`)**: the backward form of (34) is determinate, in the
strong Blanchard–Kahn sense: for EVERY bounded adapted forcing vector and every initial real
balance there is exactly one bounded equilibrium, for any expectation system. -/
theorem Abk_determinate {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) : Determinate 𝔼 (Abk σ η β κ) := by
  obtain ⟨hnu, hs, hg⟩ := Abk_bk_conditions hσ hη hκ hβ0 hβ1
  exact determinate_of 𝔼 hnu (by rw [finrank_eq_stableCount hnu, hs]) hg

/-! ### `η > 0`: from the state-space form back to (34) -/

/-- Galí (2015), eq. (34), p. 75: the state `x_t = (ỹ_t, π_t; l̂_{t−1})` as a vector process on
the split index `Fin 2 ⊕ Fin 1`. -/
def yvec (ygap infl L : ℕ → Ω → ℝ) : ℕ → Fin 2 ⊕ Fin 1 → Ω → ℝ :=
  fun t k => ![ygap t, infl t, L t] (eS k)

/-- Galí (2015), eq. (34), p. 75: the shock vector `s_t = (r̂ⁿ_t, ŷⁿ_t, Δm_t)` as a vector
process. -/
def svec (rn yn dm : ℕ → Ω → ℝ) : ℕ → Fin 3 → Ω → ℝ := fun t => ![rn t, yn t, dm t]

/-- Galí (2015), eq. (34), p. 75: the forcing `−A_{M,1}⁻¹ B_M s_t` of the backward form. -/
noncomputable def wvec (σ η β : ℝ) (rn yn dm : ℕ → Ω → ℝ) : ℕ → Fin 2 ⊕ Fin 1 → Ω → ℝ :=
  fun t k => mv (-((AM1 σ η β)⁻¹ * BM η)) (svec rn yn dm t) (eS k)

omit 𝔼 in
/-- Galí (2015), p. 75 (tool): the state vector at an outcome, relabelled. -/
theorem yvec_apply (ygap infl L : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    (fun k => yvec ygap infl L t k ω) = stateVec ygap infl L t ω ∘ eS := by
  funext k
  simp only [Function.comp, yvec, stateVec]
  generalize eS k = i
  fin_cases i <;> rfl

/-- Galí (2015), p. 75 (tool): the forecast vector at an outcome, relabelled. -/
theorem E_yvec_apply (ygap infl L : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    (fun k => 𝔼.E t (yvec ygap infl L (t + 1) k) ω) = expVec 𝔼 ygap infl L t ω ∘ eS := by
  funext k
  simp only [Function.comp, yvec, expVec]
  generalize eS k = i
  fin_cases i <;> rfl

omit 𝔼 in
/-- Galí (2015), p. 75 (tool): the forcing at an outcome, relabelled. -/
theorem wvec_apply (σ η β : ℝ) (rn yn dm : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    (fun k => wvec σ η β rn yn dm t k ω) =
      ((-((AM1 σ η β)⁻¹ * BM η)) *ᵥ shockVec rn yn dm t ω) ∘ eS := by
  funext k
  simp only [Function.comp, wvec, mv_apply]
  congr 2
  funext j
  fin_cases j <;> rfl

omit 𝔼 in
/-- Galí (2015), p. 75 (tool): the split backward matrix acting on a state, relabelled. -/
theorem mv_Abk_apply (σ η β κ : ℝ) (a : Fin 2 ⊕ Fin 1 → Ω → ℝ) (ω : Ω) :
    (fun k => mv (Abk σ η β κ) a k ω) = (Ab3 σ η β κ *ᵥ ((fun k => a k ω) ∘ eS.symm)) ∘ eS := by
  funext k
  rw [mv_apply, Abk, Matrix.submatrix_mulVec_equiv]

/-- Galí (2015), eq. (34), p. 75: with `A_{M,1}` invertible,
`E = A_b x − A_{M,1}⁻¹ B_M s` iff `A_{M,0} x = A_{M,1} E + B_M s`. -/
theorem backward_iff {σ η β κ : ℝ} (hu : IsUnit (AM1 σ η β).det) (x Ex s : Fin 3 → ℝ) :
    Ex = Ab3 σ η β κ *ᵥ x + (-((AM1 σ η β)⁻¹ * BM η)) *ᵥ s ↔
      AM0 σ η κ *ᵥ x = AM1 σ η β *ᵥ Ex + BM η *ᵥ s := by
  constructor
  · rintro rfl
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Ab3,
      Matrix.mul_nonsing_inv_cancel_left _ _ hu, Matrix.mul_neg,
      Matrix.mul_nonsing_inv_cancel_left _ _ hu, Matrix.neg_mulVec]
    abel
  · intro h
    have hE : Ex = (AM1 σ η β)⁻¹ *ᵥ (AM1 σ η β *ᵥ Ex) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
    have h1 : AM1 σ η β *ᵥ Ex = AM0 σ η κ *ᵥ x - BM η *ᵥ s := by rw [h]; abel
    rw [hE, h1, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Ab3,
      Matrix.neg_mulVec, sub_eq_add_neg]

/-- Galí (2015), eq. (34), p. 75 (`η > 0`): the backward state-space system holds iff (34) holds. -/
theorem solves_Abk_iff {σ η β κ : ℝ} (hu : IsUnit (AM1 σ η β).det)
    {ygap infl L rn yn dm : ℕ → Ω → ℝ} :
    Solves 𝔼 (Abk σ η β κ) (wvec σ η β rn yn dm) (yvec ygap infl L) ↔
      System34 𝔼 σ η β κ ygap infl L rn yn dm := by
  have key : ∀ t ω, (∀ k, 𝔼.E t (yvec ygap infl L (t + 1) k) ω =
      mv (Abk σ η β κ) (yvec ygap infl L t) k ω + wvec σ η β rn yn dm t k ω) ↔
      (AM0 σ η κ).mulVec (stateVec ygap infl L t ω) =
        (AM1 σ η β).mulVec (expVec 𝔼 ygap infl L t ω) + (BM η).mulVec (shockVec rn yn dm t ω) := by
    intro t ω
    rw [← backward_iff hu]
    have hfun : (∀ k, 𝔼.E t (yvec ygap infl L (t + 1) k) ω =
        mv (Abk σ η β κ) (yvec ygap infl L t) k ω + wvec σ η β rn yn dm t k ω) ↔
        (fun k => 𝔼.E t (yvec ygap infl L (t + 1) k) ω) =
          (fun k => mv (Abk σ η β κ) (yvec ygap infl L t) k ω) +
            (fun k => wvec σ η β rn yn dm t k ω) :=
      ⟨fun h => funext h, fun h k => congrFun h k⟩
    rw [hfun, E_yvec_apply, mv_Abk_apply, wvec_apply, yvec_apply, Function.comp_assoc,
      Equiv.self_comp_symm, Function.comp_id, ← Pi.add_comp]
    exact eS.surjective.injective_comp_right.eq_iff
  constructor
  · intro h t ω
    exact (key t ω).mp fun k => congrFun (h t k) ω
  · intro h t k
    funext ω
    exact (key t ω).mpr (h t ω) k

/-- Galí (2015), p. 75 (`η > 0`): equilibria of the backward state-space form are exactly the
bounded equilibria of (34). -/
theorem equil_Abk_iff {σ η β κ L0 : ℝ} (hu : IsUnit (AM1 σ η β).det)
    {ygap infl L rn yn dm : ℕ → Ω → ℝ} :
    Equil 𝔼 (Abk σ η β κ) (wvec σ η β rn yn dm) (fun _ => L0) (yvec ygap infl L) ↔
      Equil34 𝔼 σ η β κ L0 rn yn dm ygap infl L := by
  have hA : AdaptedV 𝔼 (yvec ygap infl L) ↔
      𝔼.Adapted ygap ∧ 𝔼.Adapted infl ∧ 𝔼.Adapted L := by
    constructor
    · intro h
      exact ⟨fun t => h t (Sum.inl 0), fun t => h t (Sum.inl 1), fun t => h t (Sum.inr 0)⟩
    · rintro ⟨h1, h2, h3⟩ t k
      rcases k with i | j
      · fin_cases i
        · exact h1 t
        · exact h2 t
      · fin_cases j
        exact h3 t
  have hK : (∀ t (j : Fin 1), 𝔼.E t (yvec ygap infl L (t + 1) (Sum.inr j)) =
      yvec ygap infl L (t + 1) (Sum.inr j)) ↔ Predetermined 𝔼 L := by
    constructor
    · intro h t
      exact h t 0
    · intro h t j
      fin_cases j
      exact h t
  have hI : (∀ j : Fin 1, yvec ygap infl L 0 (Sum.inr j) = fun _ => (fun _ => L0) j) ↔
      L 0 = fun _ => L0 := by
    constructor
    · intro h
      exact h 0
    · intro h j
      fin_cases j
      exact h
  have hB : BoundedV (yvec ygap infl L) ↔
      BoundedProc ygap ∧ BoundedProc infl ∧ BoundedProc L := by
    constructor
    · rintro ⟨M, hM⟩
      exact ⟨⟨M, fun t ω => hM t (Sum.inl 0) ω⟩, ⟨M, fun t ω => hM t (Sum.inl 1) ω⟩,
        ⟨M, fun t ω => hM t (Sum.inr 0) ω⟩⟩
    · rintro ⟨⟨M1, h1⟩, ⟨M2, h2⟩, ⟨M3, h3⟩⟩
      refine ⟨max M1 (max M2 M3), fun t k ω => ?_⟩
      rcases k with i | j
      · fin_cases i
        · exact (h1 t ω).trans (le_max_left _ _)
        · exact (h2 t ω).trans ((le_max_left _ _).trans (le_max_right _ _))
      · fin_cases j
        exact (h3 t ω).trans ((le_max_right _ _).trans (le_max_right _ _))
  unfold Equil Equil34
  rw [solves_Abk_iff 𝔼 hu, hA, hK, hI, hB]
  tauto

omit 𝔼 in
/-- Galí (2015), p. 75 (tool): bounded shocks give a bounded shock vector. -/
theorem svec_boundedV {rn yn dm : ℕ → Ω → ℝ} (h1 : BoundedProc rn) (h2 : BoundedProc yn)
    (h3 : BoundedProc dm) : BoundedV (svec rn yn dm) := by
  obtain ⟨M1, h1⟩ := h1
  obtain ⟨M2, h2⟩ := h2
  obtain ⟨M3, h3⟩ := h3
  refine ⟨max M1 (max M2 M3), fun t k ω => ?_⟩
  fin_cases k
  · exact (h1 t ω).trans (le_max_left _ _)
  · exact (h2 t ω).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h3 t ω).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- Galí (2015), p. 75 (tool): adapted shocks give an adapted shock vector. -/
theorem svec_adaptedV {rn yn dm : ℕ → Ω → ℝ} (h1 : 𝔼.Adapted rn) (h2 : 𝔼.Adapted yn)
    (h3 : 𝔼.Adapted dm) : AdaptedV 𝔼 (svec rn yn dm) := by
  intro t k
  fin_cases k
  · exact h1 t
  · exact h2 t
  · exact h3 t

/-- **Galí (2015), p. 75, fn. 14 (`η > 0`), PROVED**: for `σ, η, β > 0`, `κ > 0`, `β ≤ 1`, any
expectation system, bounded adapted shocks `r̂ⁿ, ŷⁿ, Δm` and any initial real balance
`l̂_{−1} = L0`, system (34) has exactly one bounded adapted equilibrium with predetermined real
balances. -/
theorem system34_existsUnique_pos {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) {rn yn dm : ℕ → Ω → ℝ} (hrnb : BoundedProc rn)
    (hynb : BoundedProc yn) (hdmb : BoundedProc dm) (hrna : 𝔼.Adapted rn)
    (hyna : 𝔼.Adapted yn) (hdma : 𝔼.Adapted dm) (L0 : ℝ) :
    ∃! v : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      Equil34 𝔼 σ η β κ L0 rn yn dm v.1 v.2.1 v.2.2 := by
  have hu := isUnit_det_AM1 hσ.ne' hη.ne' hβ0.ne'
  have hwb : BoundedV (wvec σ η β rn yn dm) := by
    obtain ⟨B, hB⟩ := boundedV_mv (-((AM1 σ η β)⁻¹ * BM η)) (svec_boundedV hrnb hynb hdmb)
    exact ⟨B, fun t k ω => hB t (eS k) ω⟩
  have hwa : AdaptedV 𝔼 (wvec σ η β rn yn dm) := fun t k =>
    adaptedV_mv 𝔼 (-((AM1 σ η β)⁻¹ * BM η)) (svec_adaptedV 𝔼 hrna hyna hdma) t (eS k)
  obtain ⟨y, hy, huniq⟩ := Abk_determinate 𝔼 hσ hη hκ hβ0 hβ1 _ hwb hwa (fun _ => L0)
  have hyv : yvec (fun t => y t (Sum.inl 0)) (fun t => y t (Sum.inl 1))
      (fun t => y t (Sum.inr 0)) = y := by
    funext t k
    rcases k with i | j
    · fin_cases i <;> rfl
    · fin_cases j; rfl
  refine ⟨(fun t => y t (Sum.inl 0), fun t => y t (Sum.inl 1), fun t => y t (Sum.inr 0)),
    ?_, ?_⟩
  · exact (equil_Abk_iff 𝔼 hu).mp (by rw [hyv]; exact hy)
  · rintro ⟨a, b, c⟩ hv
    have h := huniq _ ((equil_Abk_iff 𝔼 hu).mpr hv)
    rw [← h]
    rfl

/-! ### `η = 0`: the reduced two-variable system -/

/-- Galí (2015), eq. (34), p. 75 with `η = 0`: the backward matrix of the reduced system in
`(π_t; l̂_{t−1})`, `[[(1+κ)/β, −κ/β], [−1, 1]]`. -/
noncomputable def B2f (β κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![(1 + κ) / β, -κ / β; -1, 1]

/-- Galí (2015), p. 75: the relabelling of `Fin 2` as `Fin 1 ⊕ Fin 1` (`π_t` non-predetermined,
`l̂_{t−1}` predetermined). -/
abbrev eS2 : Fin 1 ⊕ Fin 1 ≃ Fin 2 := finSumFinEquiv

/-- Galí (2015), eq. (34), p. 75 with `η = 0`: the reduced backward matrix on `Fin 1 ⊕ Fin 1`. -/
noncomputable def B2 (β κ : ℝ) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  (B2f β κ).submatrix eS2 eS2

omit 𝔼 in
/-- Galí (2015), p. 75 (`η = 0`): the stable root `ρ₁ ∈ (0, 1)` of
`β ρ² − (1 + β + κ) ρ + 1 = 0` (IVT: the left side is `1` at `0` and `−κ` at `1`). -/
theorem exists_rho1 {β κ : ℝ} (hκ : 0 < κ) :
    ∃ ρ, 0 < ρ ∧ ρ < 1 ∧ β * ρ ^ 2 - (1 + β + κ) * ρ + 1 = 0 := by
  have hcont : ContinuousOn (fun z : ℝ => β * z ^ 2 - (1 + β + κ) * z + 1) (Set.Icc 0 1) := by
    fun_prop
  have hmem : (0 : ℝ) ∈ Set.Ioo ((fun z : ℝ => β * z ^ 2 - (1 + β + κ) * z + 1) 1)
      ((fun z : ℝ => β * z ^ 2 - (1 + β + κ) * z + 1) 0) := by
    simp only [Set.mem_Ioo]
    constructor <;> nlinarith
  obtain ⟨z, ⟨hz0, hz1⟩, hz⟩ := intermediate_value_Ioo' zero_le_one hcont hmem
  exact ⟨z, hz0, hz1, hz⟩

omit 𝔼 in
/-- Galí (2015), p. 75 (`η = 0`): the characteristic polynomial of the reduced matrix is
`(X − ρ₁)(X − 1/(βρ₁))`. -/
theorem charpoly_B2f {β κ ρ : ℝ} (hβ : β ≠ 0) (hρ0 : ρ ≠ 0)
    (hρ : β * ρ ^ 2 - (1 + β + κ) * ρ + 1 = 0) :
    (B2f β κ).charpoly = (X - C ρ) * (X - C (1 / (β * ρ))) := by
  refine Polynomial.funext fun z => ?_
  rw [Matrix.eval_charpoly, Matrix.det_fin_two]
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  simp [B2f, Matrix.scalar_apply]
  field_simp
  linear_combination z * hρ

omit 𝔼 in
/-- Galí (2015), p. 75 (`η = 0`): the reduced matrix has one eigenvalue `ρ₁ ∈ (0, 1)`, one
eigenvalue `1/(βρ₁) > 1`, none on the unit circle. -/
theorem B2f_root_location {β κ : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    NoUnit (B2f β κ) ∧ stableCount (B2f β κ) = 1 := by
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := exists_rho1 (β := β) hκ
  have hβρ : β * ρ < 1 := by nlinarith
  have hρ2 : 1 < 1 / (β * ρ) := one_lt_one_div (by positivity) hβρ
  have he : eigs (B2f β κ) = {(ρ : ℂ)} + {((1 / (β * ρ) : ℝ) : ℂ)} := by
    have hne : ((B2f β κ).charpoly.map Complex.ofRealHom) ≠ 0 :=
      ((Matrix.charpoly_monic _).map _).ne_zero
    rw [eigs, charpoly_map_ofReal]
    rw [charpoly_B2f hβ0.ne' hρ0.ne' hρ, Polynomial.map_mul] at hne ⊢
    rw [roots_mul hne, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, roots_X_sub_C,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, roots_X_sub_C]
    rfl
  have hn1 : ‖(ρ : ℂ)‖ = ρ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
  have hn2 : ‖((1 / (β * ρ) : ℝ) : ℂ)‖ = 1 / (β * ρ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  refine ⟨?_, ?_⟩
  · intro μ hμ
    rw [he, Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_singleton] at hμ
    rcases hμ with rfl | rfl
    · rw [hn1]; exact hρ1.ne
    · rw [hn2]; exact hρ2.ne'
  · have hlt2 : ¬ 1 / (β * ρ) < 1 := not_lt.mpr hρ2.le
    rw [stableCount, he, Multiset.filter_add, Multiset.filter_singleton,
      Multiset.filter_singleton]
    simp only [hn1, hn2, hρ1, hlt2, ↓reduceIte, Multiset.card_add, Multiset.card_singleton,
      Multiset.empty_eq_zero, Multiset.card_zero]

omit 𝔼 in
/-- Galí (2015), p. 75 (`η = 0`): the Blanchard–Kahn conditions for the reduced system: no
eigenvalue on the unit circle, exactly one in the open disc, genericity (the stable eigenvector
`(1 − ρ₁, 1)` moves real balances). -/
theorem B2_bk_conditions {β κ : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    NoUnit (B2 β κ) ∧ stableCount (B2 β κ) = Fintype.card (Fin 1) ∧ GenericX (B2 β κ) := by
  obtain ⟨hnu, hs⟩ := B2f_root_location hκ hβ0 hβ1
  have heq : eigs (B2 β κ) = eigs (B2f β κ) := eigs_submatrix_equiv eS2 _
  have hnu' : NoUnit (B2 β κ) := by unfold NoUnit; rw [heq]; exact hnu
  have hs' : stableCount (B2 β κ) = 1 := by unfold stableCount; rw [heq]; exact hs
  refine ⟨hnu', hs', ?_⟩
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := exists_rho1 (β := β) hκ
  have hv : B2f β κ *ᵥ ![1 - ρ, 1] = ρ • ![1 - ρ, 1] := by
    funext i
    fin_cases i
    · simp [B2f, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      field_simp
      linear_combination hρ
    · simp [B2f, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hev : B2 β κ *ᵥ (![1 - ρ, 1] ∘ eS2) = ρ • (![1 - ρ, 1] ∘ eS2) := by
    rw [B2, Matrix.submatrix_mulVec_equiv, Function.comp_assoc, Equiv.self_comp_symm,
      Function.comp_id, hv]
    rfl
  refine genericX_of_eigvec hnu' hs' (ρ := ρ) ?_ hev (j := 0) ?_
  · rw [abs_of_pos hρ0]; exact hρ1
  · change (1 : ℝ) ≠ 0
    exact one_ne_zero

/-- **Galí (2015), p. 75 (`η = 0`)**: the reduced backward system is determinate for every
bounded adapted forcing vector, for any expectation system. -/
theorem B2_determinate {β κ : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    Determinate 𝔼 (B2 β κ) := by
  obtain ⟨hnu, hs, hg⟩ := B2_bk_conditions hκ hβ0 hβ1
  exact determinate_of 𝔼 hnu (by rw [finrank_eq_stableCount hnu, hs]) hg

/-- Galí (2015), eq. (34), p. 75 (`η = 0`): the reduced state `(π_t; l̂_{t−1})`. -/
def y2 (infl L : ℕ → Ω → ℝ) : ℕ → Fin 1 ⊕ Fin 1 → Ω → ℝ := fun t k => ![infl t, L t] (eS2 k)

/-- Galí (2015), eq. (34), p. 75 (`η = 0`): the reduced forcing
`((κ/β)(ŷⁿ_t − Δm_t); Δm_t)`. -/
noncomputable def w2 (β κ : ℝ) (yn dm : ℕ → Ω → ℝ) : ℕ → Fin 1 ⊕ Fin 1 → Ω → ℝ :=
  fun t k => ![(κ / β) • (yn t - dm t), dm t] (eS2 k)

/-- Galí (2015), eq. (34), p. 75 (`η = 0`): the reduced system, written out:
`E_t π_{t+1} = ((1+κ)/β) π_t − (κ/β) l̂_{t−1} + (κ/β)(ŷⁿ_t − Δm_t)` and
`E_t l̂_t = −π_t + l̂_{t−1} + Δm_t`. -/
theorem solves_B2_iff {β κ : ℝ} {infl L yn dm : ℕ → Ω → ℝ} :
    Solves 𝔼 (B2 β κ) (w2 β κ yn dm) (y2 infl L) ↔
      (∀ t ω, 𝔼.E t (infl (t + 1)) ω = (1 + κ) / β * infl t ω + -κ / β * L t ω +
        κ / β * (yn t ω - dm t ω)) ∧
      (∀ t ω, 𝔼.E t (L (t + 1)) ω = -infl t ω + L t ω + dm t ω) := by
  have h0 : ∀ t ω, mv (B2 β κ) (y2 infl L t) (Sum.inl 0) ω =
      (1 + κ) / β * infl t ω + -κ / β * L t ω := by
    intro t ω
    rw [mv_apply_sum, Fintype.sum_sum_type]
    simp [B2, B2f, y2, show eS2 (Sum.inl 0) = 0 from rfl, show eS2 (Sum.inr 0) = 1 from rfl]
  have h1 : ∀ t ω, mv (B2 β κ) (y2 infl L t) (Sum.inr 0) ω = -infl t ω + L t ω := by
    intro t ω
    rw [mv_apply_sum, Fintype.sum_sum_type]
    simp [B2, B2f, y2, show eS2 (Sum.inl 0) = 0 from rfl, show eS2 (Sum.inr 0) = 1 from rfl]
  constructor
  · intro h
    refine ⟨fun t ω => ?_, fun t ω => ?_⟩
    · have := congrFun (h t (Sum.inl 0)) ω
      rw [Pi.add_apply, h0] at this
      exact this
    · have := congrFun (h t (Sum.inr 0)) ω
      rw [Pi.add_apply, h1] at this
      exact this
  · rintro ⟨ha, hb⟩ t k
    funext ω
    rcases k with i | j
    · fin_cases i
      rw [Pi.add_apply]
      have := h0 t ω
      simp only [Fin.zero_eta, Fin.isValue] at this ⊢
      rw [this]
      exact ha t ω
    · fin_cases j
      rw [Pi.add_apply]
      have := h1 t ω
      simp only [Fin.zero_eta, Fin.isValue] at this ⊢
      rw [this]
      exact hb t ω

/-- Galí (2015), eq. (34), p. 75 (`η = 0`): with predetermined real balances, (34) is the static
equation `ỹ_t = l̂_t − ŷⁿ_t` together with the reduced two-variable system. -/
theorem system34_zero_iff {σ β κ : ℝ} (hβ : β ≠ 0) {ygap infl L rn yn dm : ℕ → Ω → ℝ}
    (hL : Predetermined 𝔼 L) :
    System34 𝔼 σ 0 β κ ygap infl L rn yn dm ↔
      (∀ t, ygap t = L (t + 1) - yn t) ∧
      (∀ t ω, 𝔼.E t (infl (t + 1)) ω = (1 + κ) / β * infl t ω + -κ / β * L t ω +
        κ / β * (yn t ω - dm t ω)) ∧
      (∀ t ω, 𝔼.E t (L (t + 1)) ω = -infl t ω + L t ω + dm t ω) := by
  have e1 : ∀ x l s : ℝ, β * ((1 + κ) / β * x + -κ / β * l + κ / β * s) =
      (1 + κ) * x - κ * l + κ * s := by
    intro x l s
    field_simp
    ring
  constructor
  · intro h
    have hrow : ∀ t ω, ygap t ω = L (t + 1) ω - yn t ω ∧
        -κ * ygap t ω + infl t ω = β * 𝔼.E t (infl (t + 1)) ω ∧
        -infl t ω + L t ω = L (t + 1) ω - dm t ω := by
      intro t ω
      have h0 := congrFun (h t ω) 0
      have h1 := congrFun (h t ω) 1
      have h2 := congrFun (h t ω) 2
      have hLω := congrFun (hL t) ω
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec] at h0 h1 h2
      refine ⟨by linarith, by linarith, by linarith⟩
    refine ⟨fun t => funext fun ω => (hrow t ω).1, fun t ω => ?_, fun t ω => ?_⟩
    · obtain ⟨a, b, c⟩ := hrow t ω
      apply mul_left_cancel₀ hβ
      rw [e1]
      linear_combination -b - κ * a + κ * c
    · have hLω := congrFun (hL t) ω
      obtain ⟨-, -, c⟩ := hrow t ω
      linarith
  · rintro ⟨ha, hb, hc⟩ t ω
    have a := congrFun (ha t) ω
    have b := hb t ω
    have c := hc t ω
    have hLω := congrFun (hL t) ω
    have b' : β * 𝔼.E t (infl (t + 1)) ω =
        (1 + κ) * infl t ω - κ * L t ω + κ * (yn t ω - dm t ω) := by rw [b, e1]
    simp only [Pi.sub_apply] at a
    funext j
    fin_cases j
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec]
      linarith
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec]
      linear_combination (-κ) * a - b' + κ * hLω - κ * c
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec]
      linarith

/-- **Galí (2015), p. 75, fn. 14 (`η = 0`), PROVED**: with an interest-inelastic money demand
(`η = 0`, allowed in Galí, Ch. 2, p. 21), `κ > 0`, `0 < β ≤ 1`, any `σ`, any expectation system,
bounded adapted shocks and any initial real balance, (34) has exactly one bounded adapted
equilibrium with predetermined real balances (the natural rate `r̂ⁿ` does not enter). -/
theorem system34_existsUnique_zero {σ β κ : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {rn yn dm : ℕ → Ω → ℝ} (hynb : BoundedProc yn) (hdmb : BoundedProc dm)
    (hyna : 𝔼.Adapted yn) (hdma : 𝔼.Adapted dm) (L0 : ℝ) :
    ∃! v : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      Equil34 𝔼 σ 0 β κ L0 rn yn dm v.1 v.2.1 v.2.2 := by
  obtain ⟨My, hMy⟩ := hynb
  obtain ⟨Md, hMd⟩ := hdmb
  have hwb : BoundedV (w2 β κ yn dm) := by
    refine ⟨|κ / β| * (My + Md) + Md, fun t k ω => ?_⟩
    have hd0 : 0 ≤ Md := (abs_nonneg _).trans (hMd 0 ω)
    have hk : 0 ≤ |κ / β| * (My + Md) := by
      have : 0 ≤ My := (abs_nonneg _).trans (hMy 0 ω)
      positivity
    rcases k with i | j
    · fin_cases i
      change |(κ / β) * (yn t ω - dm t ω)| ≤ _
      rw [abs_mul]
      have : |yn t ω - dm t ω| ≤ My + Md :=
        (abs_sub _ _).trans (add_le_add (hMy t ω) (hMd t ω))
      nlinarith [abs_nonneg (κ / β)]
    · fin_cases j
      change |dm t ω| ≤ _
      linarith [hMd t ω]
  have hwa : AdaptedV 𝔼 (w2 β κ yn dm) := by
    intro t k
    rcases k with i | j
    · fin_cases i
      change 𝔼.E t ((κ / β) • (yn t - dm t)) = (κ / β) • (yn t - dm t)
      rw [map_smul, map_sub, hyna t, hdma t]
    · fin_cases j
      exact hdma t
  obtain ⟨y, ⟨hs, ha, hk, hi, hb⟩, huniq⟩ :=
    B2_determinate 𝔼 hκ hβ0 hβ1 (w2 β κ yn dm) hwb hwa (fun _ => L0)
  set infl : ℕ → Ω → ℝ := fun t => y t (Sum.inl 0) with hinfl
  set L : ℕ → Ω → ℝ := fun t => y t (Sum.inr 0) with hLdef
  have hyv : y2 infl L = y := by
    funext t k
    rcases k with i | j
    · fin_cases i; rfl
    · fin_cases j; rfl
  have hpred : Predetermined 𝔼 L := fun t => hk t 0
  rw [← hyv, solves_B2_iff] at hs
  refine ⟨(fun t => L (t + 1) - yn t, infl, L), ⟨?_, hpred, hi 0, ?_, fun t => ha t (Sum.inl 0),
    fun t => ha t (Sum.inr 0), ?_, ?_, ?_⟩, ?_⟩
  · exact (system34_zero_iff 𝔼 hβ0.ne' hpred).mpr ⟨fun t => rfl, hs.1, hs.2⟩
  · intro t
    change 𝔼.E t (L (t + 1) - yn t) = L (t + 1) - yn t
    rw [map_sub, hpred t, hyna t]
  · obtain ⟨M, hM⟩ := hb
    refine ⟨M + My, fun t ω => ?_⟩
    change |L (t + 1) ω - yn t ω| ≤ _
    exact (abs_sub _ _).trans (add_le_add (hM (t + 1) (Sum.inr 0) ω) (hMy t ω))
  · obtain ⟨M, hM⟩ := hb
    exact ⟨M, fun t ω => hM t (Sum.inl 0) ω⟩
  · obtain ⟨M, hM⟩ := hb
    exact ⟨M, fun t ω => hM t (Sum.inr 0) ω⟩
  · rintro ⟨g', i', L'⟩ ⟨hsys, hpred', hL0, -, hai, haL, -, hbi, hbL⟩
    obtain ⟨hg, ha', hb'⟩ := (system34_zero_iff 𝔼 hβ0.ne' hpred').mp hsys
    have heq : y2 i' L' = y := by
      refine huniq _ ⟨(solves_B2_iff 𝔼).mpr ⟨ha', hb'⟩, ?_, ?_, ?_, ?_⟩
      · intro t k
        rcases k with i | j
        · fin_cases i; exact hai t
        · fin_cases j; exact haL t
      · intro t j
        fin_cases j
        exact hpred' t
      · intro j
        fin_cases j
        exact hL0
      · obtain ⟨M1, h1⟩ := hbi
        obtain ⟨M2, h2⟩ := hbL
        refine ⟨max M1 M2, fun t k ω => ?_⟩
        rcases k with i | j
        · fin_cases i; exact (h1 t ω).trans (le_max_left _ _)
        · fin_cases j; exact (h2 t ω).trans (le_max_right _ _)
    have hi' : i' = infl := funext fun t => congrFun (congrFun heq t) (Sum.inl 0)
    have hL' : L' = L := funext fun t => congrFun (congrFun heq t) (Sum.inr 0)
    subst hi' hL'
    have hg' : g' = fun t => L (t + 1) - yn t := funext hg
    rw [hg']

/-- **Galí (2015), p. 75 and fn. 14, PROVED** ("the equilibrium is always determined under an
exogenous path for the money supply"): for `σ > 0`, `η ≥ 0`, `κ > 0`, `0 < β ≤ 1`, any
expectation system, bounded adapted shocks `r̂ⁿ, ŷⁿ, Δm` and any initial real balance
`l̂_{−1} = L0`, system (34) has exactly one bounded adapted equilibrium `(ỹ, π, l̂)` with real
balances predetermined. -/
theorem system34_existsUnique {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) {rn yn dm : ℕ → Ω → ℝ} (hrnb : BoundedProc rn)
    (hynb : BoundedProc yn) (hdmb : BoundedProc dm) (hrna : 𝔼.Adapted rn)
    (hyna : 𝔼.Adapted yn) (hdma : 𝔼.Adapted dm) (L0 : ℝ) :
    ∃! v : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      Equil34 𝔼 σ η β κ L0 rn yn dm v.1 v.2.1 v.2.2 := by
  rcases hη.lt_or_eq with h | h
  · exact system34_existsUnique_pos 𝔼 hσ h hκ hβ0 hβ1 hrnb hynb hdmb hrna hyna hdma L0
  · subst h
    exact system34_existsUnique_zero 𝔼 hκ hβ0 hβ1 hynb hdmb hyna hdma L0

/-- Cochrane (2023), §19.1, p. 435, and §19.2, pp. 436–437, with Galí's (2015) equilibrium
notion, p. 75: under the same exogenous money-growth rule, BOTH the sticky-price model (Galí's
system (34), `LinksTidy.GaliMoneyRule.Equil34`) and the flexible-price model
(`LinksTidy.GaliMoneyRule.FlexEquil`) have exactly one bounded adapted equilibrium with
predetermined real balances, for every `ExpectationSystem`. -/
theorem system34_and_flex_existsUnique {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) {rn yn dm : ℕ → Ω → ℝ} (hrnb : BoundedProc rn)
    (hynb : BoundedProc yn) (hdmb : BoundedProc dm) (hrna : 𝔼.Adapted rn)
    (hyna : 𝔼.Adapted yn) (hdma : 𝔼.Adapted dm) (L0 : ℝ) :
    (∃! v : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      Equil34 𝔼 σ η β κ L0 rn yn dm v.1 v.2.1 v.2.2) ∧
    ∃! v : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), FlexEquil 𝔼 η L0 rn yn dm v.1 v.2 :=
  ⟨system34_existsUnique 𝔼 hσ hη hκ hβ0 hβ1 hrnb hynb hdmb hrna hyna hdma L0,
    flex_existsUnique 𝔼 hη hrnb hynb hdmb hrna hyna hdma L0⟩

end Cochrane.Monetarism.TidyR5MoneyRule
