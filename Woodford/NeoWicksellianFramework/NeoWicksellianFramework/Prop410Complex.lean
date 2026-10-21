/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.Prop410
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Proposition 4.10 needs real eigenvalues of `C`

Woodford (2003), *Interest and Prices*, Chapter 4, Proposition 4.10, p. 274: the hypothesis
"all of the eigenvalues of the matrix `C` are real" (also in Preston (2005), (21)) is
**necessary**. Proposition 4.9 (Bullard–Mitra) needs only stationarity; for Preston's scheme a
damped rotation `C` destroys E-stability even under the Taylor principle.

* `hurwitz_of_roots`: both roots of `ν² + c₁ν + c₀` (complex coefficients) in the open left
  half-plane imply `Re c₁ > 0` and `(Re c₁)² Re c₀ + Re c₁ Im c₁ Im c₀ − (Im c₀)² > 0`;
  `isEig_two_iff_complex`, `hurwitzVal`, `exists_isEig_re_ge_one`.
* `isEig_kronSum_of`, `isEig_hMat_of`: eigenvalues of `G(ρ)` for complex `ρ` are eigenvalues of
  `H` (converse of `Prop410.exists_isEig_of_isEig_kronSum`); `row_two_complex`, `restr_pq`.
* The counterexample: `cexC` (`C = [[0.95, −0.1], [0.1, 0.95]]`), `cexC_isEig_iff`,
  `cexC_eig_cases`, `cexC_stationary`, `cexC_not_real`, `cexC_left_eig`; parameters
  `α = 0.9`, `β = 0.99`, `κ = 1`, `σ = 0.01`, `φ_π = 8`, `φ_x = 0`; `restrS_cex`, `restrD_cex`,
  `xCex`, `yCex`, `rCex`, `p_cex`, `q_cex`, `p_cex'`, `q_cex'`, `restr_cex`, `restr_cex'`,
  `hurwitz_fails_cex`, `one_sub_tr_add_det_ne_cex`, `not_eStable_hMat_cex`,
  `not_isEig_one_dTP_cex`.
* **`prop_4_10_needs_real_eigenvalues`**: there the Taylor principle holds, the r.e.e. exists
  and is unique, it is not E-stable under Preston's learning, yet the Bullard–Mitra r.e.e. of
  Proposition 4.9 is E-stable.
-/

namespace Woodford.NeoWicksellianFramework.Prop410Complex

open Matrix Determinacy2 PrestonLearning Prop410
open Determinacy2Learning (EStable EStableAt eStable_iff)
open scoped _root_.Kronecker

/-! ### Complex quadratics: a necessary condition for both roots in the left half-plane -/

/-- Woodford (2003), p. 274 (E-stability for complex blocks): if both roots of
`ν² + c₁ν + c₀` (complex coefficients) have negative real part, then `Re c₁ > 0` and
`(Re c₁)² Re c₀ + Re c₁ Im c₁ Im c₀ − (Im c₀)² > 0` (the Hurwitz condition for complex
quadratics). The identity behind it: with roots `xᵢ + i yᵢ`, the second expression equals
`x₁x₂((x₁ + x₂)² + (y₁ − y₂)²)`. -/
theorem hurwitz_of_roots (c1 c0 : ℂ) (h : ∀ ν : ℂ, ν ^ 2 + c1 * ν + c0 = 0 → ν.re < 0) :
    0 < c1.re ∧ 0 < c1.re ^ 2 * c0.re + c1.re * c1.im * c0.im - c0.im ^ 2 := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (c1 ^ 2 - 4 * c0)
  set ν1 : ℂ := (-c1 + s) / 2 with hν1
  set ν2 : ℂ := (-c1 - s) / 2 with hν2
  have hr1 : ν1 ^ 2 + c1 * ν1 + c0 = 0 := by
    rw [hν1]
    linear_combination (1 / 4 : ℂ) * hs.symm
  have hr2 : ν2 ^ 2 + c1 * ν2 + c0 = 0 := by
    rw [hν2]
    linear_combination (1 / 4 : ℂ) * hs.symm
  have hc1 : c1 = -(ν1 + ν2) := by
    rw [hν1, hν2]
    ring
  have hc0 : c0 = ν1 * ν2 := by
    rw [hν1, hν2]
    linear_combination (-1 / 4 : ℂ) * hs
  have hx1 := h ν1 hr1
  have hx2 := h ν2 hr2
  rw [hc1, hc0]
  simp only [Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im]
  set x1 := ν1.re
  set x2 := ν2.re
  set y1 := ν1.im
  set y2 := ν2.im
  refine ⟨by linarith, ?_⟩
  have key : (-(x1 + x2)) ^ 2 * (x1 * x2 - y1 * y2) + -(x1 + x2) * -(y1 + y2) *
      (x1 * y2 + y1 * x2) - (x1 * y2 + y1 * x2) ^ 2 =
      x1 * x2 * ((x1 + x2) ^ 2 + (y1 - y2) ^ 2) := by ring
  rw [key]
  have h12 : 0 < x1 * x2 := mul_pos_of_neg_of_neg hx1 hx2
  have hs2 : 0 < (x1 + x2) ^ 2 := by
    have : x1 + x2 < 0 := by linarith
    nlinarith
  exact mul_pos h12 (add_pos_of_pos_of_nonneg hs2 (sq_nonneg _))

/-- Woodford (2003), p. 266: `μ` is an eigenvalue of a complex `2 × 2` matrix iff
`μ² − tr(R) μ + det(R) = 0`. -/
theorem isEig_two_iff_complex (R : Matrix (Fin 2) (Fin 2) ℂ) (μ : ℂ) :
    KroneckerSpectrum.IsEig R μ ↔
      μ ^ 2 - (R 0 0 + R 1 1) * μ + (R 0 0 * R 1 1 - R 0 1 * R 1 0) = 0 := by
  rw [KroneckerSpectrum.isEig_iff_det, det_fin_two]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), mul_zero, zero_sub]
  constructor <;> intro h <;> linear_combination h

/-- Woodford (2003), p. 274: the Hurwitz expression
`(Re c₁)² Re c₀ + Re c₁ Im c₁ Im c₀ − (Im c₀)²` for `R − I`, with `c₁ = 2 − tr R`,
`c₀ = 1 − tr R + det R`. -/
noncomputable def hurwitzVal (R : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (2 - (R 0 0 + R 1 1)).re ^ 2 * (1 - (R 0 0 + R 1 1) + (R 0 0 * R 1 1 - R 0 1 * R 1 0)).re +
    (2 - (R 0 0 + R 1 1)).re * (2 - (R 0 0 + R 1 1)).im *
      (1 - (R 0 0 + R 1 1) + (R 0 0 * R 1 1 - R 0 1 * R 1 0)).im -
    (1 - (R 0 0 + R 1 1) + (R 0 0 * R 1 1 - R 0 1 * R 1 0)).im ^ 2

/-- Woodford (2003), p. 274: if the Hurwitz condition for `ν² + (2 − tr R)ν + (1 − tr R +
det R)` fails, the complex `2 × 2` matrix `R` has an eigenvalue with real part `≥ 1`, so it
is not E-stable. -/
theorem exists_isEig_re_ge_one (R : Matrix (Fin 2) (Fin 2) ℂ)
    (h : ¬ (0 < (2 - (R 0 0 + R 1 1)).re ∧ 0 < hurwitzVal R)) :
    ∃ μ, KroneckerSpectrum.IsEig R μ ∧ 1 ≤ μ.re := by
  by_contra hc
  push Not at hc
  apply h
  refine hurwitz_of_roots _ _ fun ν hν => ?_
  have := hc (ν + 1) ((isEig_two_iff_complex R _).mpr (by linear_combination hν))
  simp only [Complex.add_re, Complex.one_re] at this
  linarith

/-- Woodford (2003), p. 275 (converse of `exists_isEig_of_isEig_kronSum`): if `w′C = ρw′`
(`w ≠ 0`), `(I − aᵢC)Kᵢ = C`, `1 − aᵢρ ≠ 0`, and `μ` is an eigenvalue of
`ρ/(1 − a₁ρ) A₁ + ρ/(1 − a₂ρ) A₂`, then `μ` is an eigenvalue of `K₁′ ⊗ A₁ + K₂′ ⊗ A₂`
(eigenvector `vec(u w′)`). -/
theorem isEig_kronSum_of {n : ℕ} {m : Type*} [Fintype m]
    {C K1 K2 : Matrix (Fin n) (Fin n) ℂ} {A1 A2 : Matrix m m ℂ} {a1 a2 ρ μ : ℂ}
    (hK1 : (1 - a1 • C) * K1 = C) (hK2 : (1 - a2 • C) * K2 = C) {w : Fin n → ℂ}
    (hw0 : w ≠ 0) (hw : w ᵥ* C = ρ • w) (hne1 : 1 - a1 * ρ ≠ 0) (hne2 : 1 - a2 * ρ ≠ 0)
    (hG : KroneckerSpectrum.IsEig ((ρ / (1 - a1 * ρ)) • A1 + (ρ / (1 - a2 * ρ)) • A2) μ) :
    KroneckerSpectrum.IsEig (K1ᵀ ⊗ₖ A1 + K2ᵀ ⊗ₖ A2) μ := by
  classical
  obtain ⟨u, hu0, hu⟩ := hG
  have hwK : ∀ (a : ℂ) (K : Matrix (Fin n) (Fin n) ℂ), (1 - a • C) * K = C →
      1 - a * ρ ≠ 0 → w ᵥ* K = (ρ / (1 - a * ρ)) • w := by
    intro a K hK hne
    have e : (1 - a * ρ) • (w ᵥ* K) = ρ • w := by
      rw [← hw]
      conv_rhs => rw [← hK]
      rw [← vecMul_vecMul, vecMul_sub, vecMul_one, vecMul_smul, hw, smul_smul, ← smul_vecMul]
      congr 1
      module
    calc w ᵥ* K = (1 - a * ρ)⁻¹ • ((1 - a * ρ) • (w ᵥ* K)) := by
          rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      _ = (ρ / (1 - a * ρ)) • w := by rw [e, smul_smul, div_eq_inv_mul]
  set X : Matrix m (Fin n) ℂ := vecMulVec u w with hX
  have hXK : ∀ (a : ℂ) (K : Matrix (Fin n) (Fin n) ℂ), (1 - a • C) * K = C →
      1 - a * ρ ≠ 0 → X * K = (ρ / (1 - a * ρ)) • X := by
    intro a K hK hne
    rw [hX, vecMulVec_mul, hwK a K hK hne]
    ext i k
    simp [vecMulVec_apply]
    ring
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hu0
  obtain ⟨k0, hk0⟩ := Function.ne_iff.mp hw0
  refine ⟨vec X, fun h0 => ?_, ?_⟩
  · have := congrFun h0 (k0, i0)
    simp [hX, vec, vecMulVec_apply] at this
    tauto
  · rw [add_mulVec, KroneckerSpectrum.vec_mul_mul, KroneckerSpectrum.vec_mul_mul, ← vec_add,
      Matrix.mul_assoc, Matrix.mul_assoc, hXK a1 K1 hK1 hne1, hXK a2 K2 hK2 hne2,
      Matrix.mul_smul, Matrix.mul_smul, ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.add_mul,
      hX, mul_vecMulVec, hu, ← vec_smul]
    congr 1
    ext i k
    simp [vecMulVec_apply, mul_assoc]

/-- Woodford (2003), p. 275: for complex weights `p, q`, the range of `p A₁ + q A₂` still lies in
the Taylor-rule plane. -/
theorem row_two_complex (α β κ σ φπ φx : ℝ) (p q : ℂ) (j : Fin 3) :
    (p • (matS α β κ σ φπ φx).map Complex.ofReal + q • (matD β κ σ φπ φx).map Complex.ofReal) 2 j
      = (φπ : ℂ) * (p • (matS α β κ σ φπ φx).map Complex.ofReal +
          q • (matD β κ σ φπ φx).map Complex.ofReal) 0 j +
        ((φx / 4 : ℝ) : ℂ) * (p • (matS α β κ σ φπ φx).map Complex.ofReal +
          q • (matD β κ σ φπ φx).map Complex.ofReal) 1 j := by
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, matS, matD,
    vecMulVec_apply, smul_eq_mul, colS_two, colD_two]
  push_cast
  ring

/-- Woodford (2003), p. 275: eigenvalues of `G(ρ)` (complex `ρ`) are eigenvalues of `H`: if
`w′C = ρw′` with `w ≠ 0` and `‖ρ‖ < 1`, for a stationary real `C`. -/
theorem isEig_hMat_of {n : ℕ} {α β κ σ φπ φx : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ‖ρ‖ < 1) {ρ μ : ℂ}
    (hρ : ‖ρ‖ < 1) {w : Fin n → ℂ} (hw0 : w ≠ 0) (hw : w ᵥ* C.map Complex.ofReal = ρ • w)
    (hG : KroneckerSpectrum.IsEig ((ρ / (1 - ((α * β : ℝ) : ℂ) * ρ)) •
        (matS α β κ σ φπ φx).map Complex.ofReal +
      (ρ / (1 - (β : ℂ) * ρ)) • (matD β κ σ φπ φx).map Complex.ofReal) μ) :
    KroneckerSpectrum.IsEig ((hMat α β κ σ φπ φx C).map Complex.ofReal) μ := by
  have hab : |α * β| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  have hb : |β| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have hd1 := det_one_sub_smul_ne_zero hC hab
  have hd2 := det_one_sub_smul_ne_zero hC hb
  have hK1 : (1 - ((α * β : ℝ) : ℂ) • C.map Complex.ofReal) *
      ((1 - (α * β) • C)⁻¹ * C).map Complex.ofReal = C.map Complex.ofReal := by
    rw [← map_one_sub_smul, ← map_ofReal_mul, one_sub_smul_mul_inv_mul hd1]
  have hK2 : (1 - (β : ℂ) • C.map Complex.ofReal) *
      ((1 - β • C)⁻¹ * C).map Complex.ofReal = C.map Complex.ofReal := by
    rw [← map_one_sub_smul, ← map_ofReal_mul, one_sub_smul_mul_inv_mul hd2]
  have hH : (hMat α β κ σ φπ φx C).map Complex.ofReal =
      (((1 - (α * β) • C)⁻¹ * C).map Complex.ofReal)ᵀ ⊗ₖ (matS α β κ σ φπ φx).map Complex.ofReal +
        (((1 - β • C)⁻¹ * C).map Complex.ofReal)ᵀ ⊗ₖ (matD β κ σ φπ φx).map Complex.ofReal := by
    rw [hMat, Matrix.map_add Complex.ofReal Complex.ofReal_add,
      KroneckerSpectrum.kronecker_map_ofReal, KroneckerSpectrum.kronecker_map_ofReal,
      KroneckerSpectrum.transpose_map_ofReal, KroneckerSpectrum.transpose_map_ofReal]
  have hne : ∀ a : ℝ, |a| ≤ 1 → 1 - (a : ℂ) * ρ ≠ 0 := by
    intro a ha h0
    have h1 : (a : ℂ) * ρ = 1 := by linear_combination -h0
    have h2 := congrArg norm h1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_one] at h2
    nlinarith [norm_nonneg ρ, abs_nonneg a]
  rw [hH]
  exact isEig_kronSum_of hK1 hK2 hw0 hw (hne _ hab) (hne _ hb) hG

/-! ### The counterexample -/

/-- Woodford (2003), (2.24): a stationary state matrix with complex eigenvalues
`0.95 ± 0.1 i` (modulus `√0.9125 < 1`), a damped rotation. -/
noncomputable def cexC : Matrix (Fin 2) (Fin 2) ℝ := !![95 / 100, -(1 / 10); 1 / 10, 95 / 100]

/-- Woodford (2003), (2.24): the eigenvalues of `cexC` solve `(μ − 0.95)² + 0.1² = 0`. -/
theorem cexC_isEig_iff (μ : ℂ) :
    KroneckerSpectrum.IsEig (cexC.map Complex.ofReal) μ ↔
      (μ - 95 / 100) ^ 2 + (1 / 10) ^ 2 = 0 := by
  rw [isEig_two_iff_complex]
  simp only [cexC, one_div, Fin.isValue, map_apply, of_apply, cons_val', cons_val_zero,
    cons_val_fin_one, Complex.ofReal_div, Complex.ofReal_ofNat, cons_val_one,
    Complex.ofReal_neg, Complex.ofReal_inv, neg_mul, sub_neg_eq_add, inv_pow]
  constructor <;> intro h <;> linear_combination h

/-- Woodford (2003), (2.24): the eigenvalues of `cexC` are `0.95 ± 0.1 i`. -/
theorem cexC_eig_cases {μ : ℂ} (h : KroneckerSpectrum.IsEig (cexC.map Complex.ofReal) μ) :
    μ = 95 / 100 + 1 / 10 * Complex.I ∨ μ = 95 / 100 - 1 / 10 * Complex.I := by
  rw [cexC_isEig_iff] at h
  have : (μ - (95 / 100 + 1 / 10 * Complex.I)) * (μ - (95 / 100 - 1 / 10 * Complex.I)) = 0 := by
    linear_combination h - (1 / 100 : ℂ) * Complex.I_sq
  rcases mul_eq_zero.mp this with h1 | h1
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (sub_eq_zero.mp h1)

/-- Woodford (2003), (2.24): `cexC` is stationary — every eigenvalue lies inside the unit
circle. -/
theorem cexC_stationary :
    ∀ ρ, KroneckerSpectrum.IsEig (cexC.map Complex.ofReal) ρ → ‖ρ‖ < 1 := by
  intro ρ hρ
  have hsq : ‖ρ‖ ^ 2 < 1 := by
    rw [Complex.sq_norm]
    rcases cexC_eig_cases hρ with rfl | rfl
    · rw [Complex.normSq_apply]
      simp
      norm_num
    · rw [Complex.normSq_apply]
      simp
      norm_num
  nlinarith [norm_nonneg ρ]

/-- Woodford (2003), (2.24): `0.95 + 0.1 i` is an eigenvalue of `cexC` and is not real, so
`cexC` violates the hypothesis "all of the eigenvalues of the matrix `C` are real" of
Proposition 4.10 (but not the stationarity of (2.24)). -/
theorem cexC_not_real :
    KroneckerSpectrum.IsEig (cexC.map Complex.ofReal) (95 / 100 + 1 / 10 * Complex.I) ∧
      (95 / 100 + 1 / 10 * Complex.I : ℂ).im ≠ 0 := by
  refine ⟨(cexC_isEig_iff _).mpr ?_, by simp⟩
  linear_combination (1 / 100 : ℂ) * Complex.I_sq

/-- Woodford (2003), (2.24): `w = (1, i)` is a left eigenvector of `cexC` for `0.95 + 0.1 i`. -/
theorem cexC_left_eig :
    ![1, Complex.I] ᵥ* cexC.map Complex.ofReal =
      (95 / 100 + 1 / 10 * Complex.I) • ![1, Complex.I] := by
  funext k
  fin_cases k
  · simp [cexC, vecMul, dotProduct, Fin.sum_univ_two]
    ring
  · simp [cexC, vecMul, dotProduct, Fin.sum_univ_two]
    linear_combination (-1 / 10 : ℂ) * Complex.I_sq

/-- Woodford (2003), p. 275: `restr` is linear in complex combinations of real matrices. -/
theorem restr_pq (A B : Matrix (Fin 3) (Fin 3) ℝ) (a b : ℝ) (p q : ℂ) :
    restr (p • A.map Complex.ofReal + q • B.map Complex.ofReal) (a : ℂ) (b : ℂ) =
      p • (restr A a b).map Complex.ofReal + q • (restr B a b).map Complex.ofReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp [restr]
    ring

/-- Woodford (2003), p. 275: in the counterexample (`α = 0.9`, `β = 0.99`, `κ = 1`,
`σ = 0.01`, `φ_π = 8`, `φ_x = 0`) the supply block on the Taylor-rule plane. -/
theorem restrS_cex : restr (matS (9 / 10) (99 / 100) 1 (1 / 100) 8 0) 8 (0 / 4) =
    !![11 / 120, 33 / 40; -11 / 1500, -33 / 500] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  norm_num [restr, matS, colS, supplyW, taylorDelta, vecMulVec_apply]

/-- Woodford (2003), p. 275: in the counterexample, the demand block on the Taylor-rule
plane. -/
theorem restrD_cex : restr (matD (99 / 100) 1 (1 / 100) 8 0) 8 (0 / 4) =
    !![-173 / 2700, 1 / 108; -173 / 2700, 1 / 108] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  norm_num [restr, matD, colD, demandW, taylorDelta, vecMulVec_apply]

/-- Woodford (2003), p. 275: the weight `ρ/(1 − αβρ)` at `ρ = 0.95 + 0.1 i`. -/
theorem p_cex : (95 / 100 + 1 / 10 * Complex.I) /
      (1 - (((9 / 10 * (99 / 100) : ℝ)) : ℂ) * (95 / 100 + 1 / 10 * Complex.I)) =
    ⟨10957000 / 2521313, 8000000 / 2521313⟩ := by
  have hne : (1 - (((9 / 10 * (99 / 100) : ℝ)) : ℂ) * (95 / 100 + 1 / 10 * Complex.I)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  rw [div_eq_iff hne]
  apply Complex.ext <;> norm_num

/-- Woodford (2003), p. 275: the weight `ρ/(1 − βρ)` at `ρ = 0.95 + 0.1 i`. -/
theorem q_cex : (95 / 100 + 1 / 10 * Complex.I) /
      (1 - ((99 / 100 : ℝ) : ℂ) * (95 / 100 + 1 / 10 * Complex.I)) =
    ⟨37300 / 10673, 80000 / 10673⟩ := by
  have hne : (1 - ((99 / 100 : ℝ) : ℂ) * (95 / 100 + 1 / 10 * Complex.I)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  rw [div_eq_iff hne]
  apply Complex.ext <;> norm_num

/-- Woodford (2003), p. 275: the weight `ρ/(1 − αβρ)` at `ρ = 0.95 − 0.1 i`. -/
theorem p_cex' : (95 / 100 - 1 / 10 * Complex.I) /
      (1 - (((9 / 10 * (99 / 100) : ℝ)) : ℂ) * (95 / 100 - 1 / 10 * Complex.I)) =
    ⟨10957000 / 2521313, -(8000000 / 2521313)⟩ := by
  have hne : (1 - (((9 / 10 * (99 / 100) : ℝ)) : ℂ) * (95 / 100 - 1 / 10 * Complex.I)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  rw [div_eq_iff hne]
  apply Complex.ext <;> norm_num

/-- Woodford (2003), p. 275: the weight `ρ/(1 − βρ)` at `ρ = 0.95 − 0.1 i`. -/
theorem q_cex' : (95 / 100 - 1 / 10 * Complex.I) /
      (1 - ((99 / 100 : ℝ) : ℂ) * (95 / 100 - 1 / 10 * Complex.I)) =
    ⟨37300 / 10673, -(80000 / 10673)⟩ := by
  have hne : (1 - ((99 / 100 : ℝ) : ℂ) * (95 / 100 - 1 / 10 * Complex.I)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  rw [div_eq_iff hne]
  apply Complex.ext <;> norm_num

/-- Woodford (2003), p. 275: the counterexample's supply block on the Taylor-rule plane. -/
noncomputable def xCex : Matrix (Fin 2) (Fin 2) ℝ := !![11 / 120, 33 / 40; -11 / 1500, -33 / 500]

/-- Woodford (2003), p. 275: the counterexample's demand block on the Taylor-rule plane. -/
noncomputable def yCex : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-173 / 2700, 1 / 108; -173 / 2700, 1 / 108]

/-- Woodford (2003), p. 275: `B̃(ρ) = p X + q Y` with complex weights `p = ρ/(1 − αβρ)`,
`q = ρ/(1 − βρ)`. -/
noncomputable def rCex (p q : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  p • xCex.map Complex.ofReal + q • yCex.map Complex.ofReal

/-- Woodford (2003), p. 274: in the counterexample, at `ρ = 0.95 + 0.1 i`, the Hurwitz
condition for `B̃(ρ) − I` fails (its value is `≈ −3.7`). -/
theorem hurwitz_fails_cex :
    ¬ (0 < (2 - (rCex ⟨10957000 / 2521313, 8000000 / 2521313⟩ ⟨37300 / 10673, 80000 / 10673⟩
          0 0 + rCex ⟨10957000 / 2521313, 8000000 / 2521313⟩
          ⟨37300 / 10673, 80000 / 10673⟩ 1 1)).re ∧
      0 < hurwitzVal (rCex ⟨10957000 / 2521313, 8000000 / 2521313⟩
        ⟨37300 / 10673, 80000 / 10673⟩)) := by
  rintro ⟨-, h⟩
  simp only [hurwitzVal, rCex, xCex, yCex, Matrix.add_apply, Matrix.smul_apply,
    Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
    Complex.re_ofNat, Complex.im_ofNat] at h
  norm_num at h

/-- Woodford (2003), p. 274: in the counterexample `1` is not an eigenvalue of `B̃(ρ)` for
`ρ = 0.95 ± 0.1 i` (`Re(1 − tr B̃ + det B̃) ≈ 0.58`; it depends on the imaginary parts of the
weights only through their product). -/
theorem one_sub_tr_add_det_ne_cex (pim qim : ℝ)
    (hpq : pim * qim = 8000000 / 2521313 * (80000 / 10673)) :
    1 - (rCex ⟨10957000 / 2521313, pim⟩ ⟨37300 / 10673, qim⟩ 0 0 +
          rCex ⟨10957000 / 2521313, pim⟩ ⟨37300 / 10673, qim⟩ 1 1) +
      (rCex ⟨10957000 / 2521313, pim⟩ ⟨37300 / 10673, qim⟩ 0 0 *
          rCex ⟨10957000 / 2521313, pim⟩ ⟨37300 / 10673, qim⟩ 1 1 -
        rCex ⟨10957000 / 2521313, pim⟩ ⟨37300 / 10673, qim⟩ 0 1 *
          rCex ⟨10957000 / 2521313, pim⟩ ⟨37300 / 10673, qim⟩ 1 0) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp only [rCex, xCex, yCex, Matrix.add_apply, Matrix.smul_apply,
    Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
    Complex.zero_re] at this
  nlinarith [hpq]

/-! ### Proposition 4.10 fails without real eigenvalues -/

/-- Woodford (2003), p. 275, at the counterexample: `B̃(ρ)` for `ρ = 0.95 + 0.1 i`. -/
theorem restr_cex :
    restr (((95 / 100 + 1 / 10 * Complex.I) /
        (1 - (((9 / 10 * (99 / 100) : ℝ)) : ℂ) * (95 / 100 + 1 / 10 * Complex.I))) •
          (matS (9 / 10) (99 / 100) 1 (1 / 100) 8 0).map Complex.ofReal +
        ((95 / 100 + 1 / 10 * Complex.I) /
          (1 - ((99 / 100 : ℝ) : ℂ) * (95 / 100 + 1 / 10 * Complex.I))) •
          (matD (99 / 100) 1 (1 / 100) 8 0).map Complex.ofReal) ((8 : ℝ) : ℂ)
        (((0 : ℝ) / 4 : ℝ) : ℂ) =
      rCex ⟨10957000 / 2521313, 8000000 / 2521313⟩ ⟨37300 / 10673, 80000 / 10673⟩ := by
  rw [restr_pq, restrS_cex, restrD_cex, p_cex, q_cex]
  rfl

/-- Woodford (2003), p. 275, at the counterexample: `B̃(ρ)` for `ρ = 0.95 − 0.1 i`. -/
theorem restr_cex' :
    restr (((95 / 100 - 1 / 10 * Complex.I) /
        (1 - (((9 / 10 * (99 / 100) : ℝ)) : ℂ) * (95 / 100 - 1 / 10 * Complex.I))) •
          (matS (9 / 10) (99 / 100) 1 (1 / 100) 8 0).map Complex.ofReal +
        ((95 / 100 - 1 / 10 * Complex.I) /
          (1 - ((99 / 100 : ℝ) : ℂ) * (95 / 100 - 1 / 10 * Complex.I))) •
          (matD (99 / 100) 1 (1 / 100) 8 0).map Complex.ofReal) ((8 : ℝ) : ℂ)
        (((0 : ℝ) / 4 : ℝ) : ℂ) =
      rCex ⟨10957000 / 2521313, -(8000000 / 2521313)⟩ ⟨37300 / 10673, -(80000 / 10673)⟩ := by
  rw [restr_pq, restrS_cex, restrD_cex, p_cex', q_cex']
  rfl

/-- Woodford (2003), p. 275: **in the counterexample `H` is not E-stable**: it has an
eigenvalue with real part `≥ 1` (numerically `≈ 2.97 − 3.17 i`), coming from the complex
eigenvalue `0.95 + 0.1 i` of `C`. -/
theorem not_eStable_hMat_cex : ¬ EStable (hMat (9 / 10) (99 / 100) 1 (1 / 100) 8 0 cexC) := by
  intro hE
  have hρn := cexC_stationary _ cexC_not_real.1
  have hw0 : (![1, Complex.I] : Fin 2 → ℂ) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  obtain ⟨μ, hμ, hμ1⟩ := exists_isEig_re_ge_one _ hurwitz_fails_cex
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    norm_num at hμ1
  have hG := (isEig_three_iff _ _ _ (row_two_complex (9 / 10) (99 / 100) 1 (1 / 100) 8 0 _ _)
    μ).mpr (Or.inr (by rw [restr_cex]; exact hμ))
  have hH := isEig_hMat_of (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    cexC_stationary hρn hw0 cexC_left_eig hG
  have := (eStable_iff _).mp hE μ hH
  linarith

/-- Woodford (2003), p. 274: in the counterexample `1` is not an eigenvalue of `DT_Φ`, so the
r.e.e. (fixed point of the `T`-map) exists and is unique. -/
theorem not_isEig_one_dTP_cex :
    ¬ KroneckerSpectrum.IsEig
      ((dTP (9 / 10) (99 / 100) 1 (1 / 100) 8 0 cexC).map Complex.ofReal) 1 := by
  rw [dTP, KroneckerSpectrum.fromBlocks_map_ofReal, KroneckerSpectrum.isEig_fromBlocks_iff]
  rintro (h | h)
  · have hE := (eStable_aInt_iff (α := 9 / 10) (β := 99 / 100) (κ := 1) (σ := 1 / 100)
      (φπ := 8) (φx := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) le_rfl).mpr (by norm_num [taylorLHS])
    have := (eStable_iff _).mp hE 1 h
    norm_num at this
  · obtain ⟨ρ, hρ, hG⟩ := isEig_hMat_sub (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) cexC_stationary h
    rcases (isEig_three_iff _ _ _ (row_two_complex (9 / 10) (99 / 100) 1 (1 / 100) 8 0 _ _)
      1).mp hG with h3 | h3
    · exact one_ne_zero h3
    · rcases cexC_eig_cases hρ with rfl | rfl
      · rw [restr_cex, isEig_two_iff_complex] at h3
        exact one_sub_tr_add_det_ne_cex _ _ rfl (by linear_combination h3)
      · rw [restr_cex', isEig_two_iff_complex] at h3
        exact one_sub_tr_add_det_ne_cex (-(8000000 / 2521313)) (-(80000 / 10673)) (by ring)
          (by linear_combination h3)

/-- Woodford (2003), **Proposition 4.10: the hypothesis "all of the eigenvalues of the matrix
`C` are real" cannot be dropped.** For `α = 0.9`, `β = 0.99`, `κ = 1`, `σ = 0.01`, `φ_π = 8`,
`φ_x = 0` (so the Taylor principle (2.7) holds) and the stationary state matrix
`C = [[0.95, −0.1], [0.1, 0.95]]` (eigenvalues `0.95 ± 0.1 i`, inside the unit circle), and any
Taylor-rule constant and loadings `f_r`, `f_ī`: the r.e.e. of Preston's model exists and is
unique but is **not E-stable**, whereas the Bullard–Mitra r.e.e. of Proposition 4.9 **is**
E-stable. So for complex eigenvalues the two learning schemes have different E-stability
regions. -/
theorem prop_4_10_needs_real_eigenvalues (c : ℝ) (gr gi : Fin 2 → ℝ) :
    (∀ ρ, KroneckerSpectrum.IsEig (cexC.map Complex.ofReal) ρ → ‖ρ‖ < 1) ∧
    (∃ ρ, KroneckerSpectrum.IsEig (cexC.map Complex.ofReal) ρ ∧ ρ.im ≠ 0) ∧
    1 < taylorLHS (99 / 100) 1 8 0 ∧
    (∃! v, tVecP (9 / 10) (99 / 100) 1 (1 / 100) 8 0 c gr gi cexC v = v) ∧
    (∀ v, ¬ EStableAt (tVecP (9 / 10) (99 / 100) 1 (1 / 100) 8 0 c gr gi cexC) v) ∧
    EStable (Learning.Regression.dT (taylorB (99 / 100) (1 / 100) 1 8 0) cexC) := by
  have hT : 1 < taylorLHS (99 / 100) 1 8 0 := by norm_num [taylorLHS]
  refine ⟨cexC_stationary, ⟨_, cexC_not_real⟩, hT, ?_, fun v h => ?_, ?_⟩
  · exact fixed_existsUnique_of_det _ _ _ _ _ _ c gr gi cexC
      (KroneckerSpectrum.det_one_sub_ne_zero _ not_isEig_one_dTP_cex)
  · exact not_eStable_hMat_cex ((eStable_dTP_iff_and _ _ _ _ _ _ cexC).mp
      (eStable_dTP_of_eStableAt h)).2
  · exact (Learning.BullardMitra.prop_4_9 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) cexC cexC_stationary).mpr hT

end Woodford.NeoWicksellianFramework.Prop410Complex
