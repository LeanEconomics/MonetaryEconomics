/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.PrestonLearning

/-!
# Proposition 4.10: E-stability under Preston's long-horizon learning

Woodford (2003), *Interest and Prices*, Chapter 4, Proposition 4.10, p. 274, and the
intuition of p. 275; Preston (2005), *IJCB* 1(2), Proposition 2 and Appendix 4. The book gives no
proof. The setup and the `T`-map are in `PrestonLearning`.

## The proof

* `restr`, `det_restr`, `isEig_three_iff`, `eStable_three_iff`: a `3 × 3` matrix whose range lies
  in the Taylor-rule plane `î = φ_π π + φ_x x/4` has the eigenvalue `0` plus those of its
  `2 × 2` restriction.
* `gMat` (`G(ρ) = ρ/(1 − αβρ) A₁ + ρ/(1 − βρ) A₂`, with `G(1) = DT₀`), `gMat_row`, `bTil`
  (`B̃(ρ)`), `bTil_det_identity`, `bTil_tr_identity`: the Routh quantities of `B̃(ρ) − I` times
  `Δ(1 − αβρ)(1 − βρ)` are the polynomials `nPoly`, `trPoly`; `nPoly_one`: at `ρ = 1`,
  `σκ(φ_π + (1 − β)φ_x/(4κ) − 1)`.
* `nPoly_pos`, `trPoly_pos`, `eStable_gMat_of_taylor`: under (2.7) every `G(ρ)`, real `ρ ≤ 1`,
  is E-stable (Preston's "Mathematica" step, proved here for all `0 ≤ α < 1`);
  `taylor_of_eStable_aInt`, `eStable_aInt_iff`.
* `exists_isEig_of_isEig_kronSum`, `isEig_hMat_sub`: every eigenvalue of `H` is an eigenvalue of
  some `G(ρ)`, `ρ` an eigenvalue of `C` (no diagonalisability needed, unlike Preston's proof);
  `eStable_hMat_of_taylor`.
* **`prop_4_10`**: with every eigenvalue of `C` real and inside the unit circle, a fixed point of
  the `T`-map is E-stable iff (2.7); `taylor_of_eStableAt`: necessity holds for every `C`;
  `fixed_existsUnique_of_taylor`, `fixed_existsUnique_of_det`, `prop_4_10_existsUnique`: under
  (2.7) the r.e.e. `(Φ̄, C)` exists, is unique and is E-stable.
* `same_eStability_region`, `same_eStability_region_at`: the same E-stability region as the
  Bullard–Mitra scheme of Proposition 4.9; `eStable_bTil_iff_eStable_taylorB`;
  `bTil_ne_taylorB`: the learning dynamics themselves differ.

## The intuition of p. 275

`isEig_jacobian_iff` (zeros plus the eigenvalues of `DT_Φ`), `isEig_dTP_of_isEig_aInt`,
`eStable_dTP_of_eStable_aInt`, `interceptP_two` (actual means satisfy the Taylor rule),
`embedT`, `tHat` (the restricted map `T̂₀`), `interceptP_embedT`, `tHat_eq`, `tHat_eq_Tmap`
(the form (2.19) with `B̃`), `isEig_aInt_iff`, `eStable_bTil_iff`, `fixed_infinite_iff_det`,
`det_one_sub_bTil_eq_zero_iff`, `steadyStates_infinite_iff`, `same_critical_values`,
`loci_coincide_iff_det`, `loci_coincide_iff`. `bTil_not_inverse`: the book's "`B̃ = Ã⁻¹`" is
imprecise — `B̃` can be singular even under (2.7).
-/

namespace Woodford.NeoWicksellianFramework.Prop410

open Matrix Filter Topology Determinacy2 PrestonLearning
open Determinacy2Learning (EStable EStableAt eStable_iff eStable_iff_routh Tmap
  Tmap_fixed_iff_one_sub Tmap_fixed_unique)
open scoped _root_.Kronecker

/-! ### Stationary exogenous states -/

/-- Woodford (2003), (2.24) p. 270: a nonzero eigenvalue `w` of `aC` has `a ≠ 0` and `w/a` an
eigenvalue of `C`. -/
theorem isEig_of_isEig_smul {n : ℕ} {C : Matrix (Fin n) (Fin n) ℝ} {a : ℝ} {w : ℂ}
    (h : KroneckerSpectrum.IsEig ((a • C).map Complex.ofReal) w) (hw : w ≠ 0) :
    a ≠ 0 ∧ KroneckerSpectrum.IsEig (C.map Complex.ofReal) (w / a) := by
  obtain ⟨v, hv0, hv⟩ := h
  have hm : (a • C).map Complex.ofReal = (a : ℂ) • C.map Complex.ofReal := by
    ext i j
    simp
  rw [hm, Matrix.smul_mulVec] at hv
  have ha : a ≠ 0 := by
    rintro rfl
    simp only [Complex.ofReal_zero, zero_smul] at hv
    exact hw (smul_eq_zero.mp hv.symm |>.resolve_right hv0)
  refine ⟨ha, v, hv0, ?_⟩
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  rw [div_eq_inv_mul, mul_smul, ← hv, smul_smul, inv_mul_cancel₀ ha', one_smul]

/-- Woodford (2003), (2.24): if every eigenvalue of `C` lies inside the unit circle and
`|a| ≤ 1`, so does every eigenvalue of `aC`. -/
theorem norm_lt_one_of_isEig_smul {n : ℕ} {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ‖ρ‖ < 1) {a : ℝ}
    (ha : |a| ≤ 1) (w : ℂ) (hw : KroneckerSpectrum.IsEig ((a • C).map Complex.ofReal) w) :
    ‖w‖ < 1 := by
  by_cases hw0 : w = 0
  · simp [hw0]
  obtain ⟨ha0, hρ⟩ := isEig_of_isEig_smul hw hw0
  have h1 := hC _ hρ
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs] at h1
  have hpos : 0 < |a| := abs_pos.mpr ha0
  rw [div_lt_one hpos] at h1
  linarith

/-- Woodford (2003), p. 274: for a stationary state and `|a| ≤ 1`, `I − aC` is invertible. -/
theorem det_one_sub_smul_ne_zero {n : ℕ} {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ‖ρ‖ < 1) {a : ℝ}
    (ha : |a| ≤ 1) : (1 - a • C).det ≠ 0 :=
  KroneckerSpectrum.det_one_sub_ne_zero _ fun h => by
    have := norm_lt_one_of_isEig_smul hC ha 1 h
    simp at this

/-! ### Reduction of a `3 × 3` matrix whose range lies in the Taylor-rule plane -/

/-- Woodford (2003), p. 275: the `2 × 2` matrix of a `3 × 3` map `M` restricted to the plane
`z₂ = a z₀ + b z₁` (in the coordinates `(z₀, z₁)`). -/
def restr {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) (a b : R) :
    Matrix (Fin 2) (Fin 2) R :=
  !![M 0 0 + a * M 0 2, M 0 1 + b * M 0 2; M 1 0 + a * M 1 2, M 1 1 + b * M 1 2]

/-- Woodford (2003), p. 275: if the third row of `M` is `a` times the first plus `b` times the
second (the range of `M` lies in the plane `z₂ = a z₀ + b z₁`), then
`det(μI − M) = μ det(μI − M̂)`, `M̂ = restr M a b`. -/
theorem det_restr (M : Matrix (Fin 3) (Fin 3) ℂ) (a b : ℂ)
    (h : ∀ j, M 2 j = a * M 0 j + b * M 1 j) (μ : ℂ) :
    (μ • (1 : Matrix (Fin 3) (Fin 3) ℂ) - M).det =
      μ * (μ • (1 : Matrix (Fin 2) (Fin 2) ℂ) - restr M a b).det := by
  rw [det_fin_three, det_fin_two]
  simp [restr, h]
  ring

/-- Woodford (2003), p. 275 ("two of the three eigenvalues of `DT₀` are the eigenvalues of
`DT̂₀`"): the eigenvalues of `M` are `0` and those of `restr M a b`. -/
theorem isEig_three_iff (M : Matrix (Fin 3) (Fin 3) ℂ) (a b : ℂ)
    (h : ∀ j, M 2 j = a * M 0 j + b * M 1 j) (μ : ℂ) :
    KroneckerSpectrum.IsEig M μ ↔ μ = 0 ∨ KroneckerSpectrum.IsEig (restr M a b) μ := by
  rw [KroneckerSpectrum.isEig_iff_det, KroneckerSpectrum.isEig_iff_det, det_restr M a b h,
    mul_eq_zero]

/-- Woodford (2003), p. 275: complexification commutes with `restr`. -/
theorem restr_map (M : Matrix (Fin 3) (Fin 3) ℝ) (a b : ℝ) :
    restr (M.map Complex.ofReal) (a : ℂ) (b : ℂ) = (restr M a b).map Complex.ofReal := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [restr]

/-- Woodford (2003), p. 275 ("only the dynamics on this subspace are potentially unstable"):
for a real `M` with range in the plane `z₂ = a z₀ + b z₁`, `M` is E-stable iff its restriction
is (the remaining eigenvalue is `0`). -/
theorem eStable_three_iff (M : Matrix (Fin 3) (Fin 3) ℝ) (a b : ℝ)
    (h : ∀ j, M 2 j = a * M 0 j + b * M 1 j) : EStable M ↔ EStable (restr M a b) := by
  rw [eStable_iff, eStable_iff]
  have hc : ∀ j, M.map Complex.ofReal 2 j =
      (a : ℂ) * M.map Complex.ofReal 0 j + (b : ℂ) * M.map Complex.ofReal 1 j := fun j => by
    simp [h j]
  simp only [isEig_three_iff _ _ _ hc, restr_map]
  constructor
  · intro h' μ hμ
    exact h' μ (Or.inr hμ)
  · rintro h' μ (rfl | hμ)
    · simp
    · exact h' μ hμ

/-! ### The matrices `G(ρ)` of Preston's Appendix 4 -/

/-- Woodford (2003), p. 275 (Preston (2005), App. 4, `G_k(ρ_k)`): the block of the Jacobian
belonging to an eigenvalue `ρ` of `C`, `G(ρ) = ρ/(1 − αβρ) A₁ + ρ/(1 − βρ) A₂`. At `ρ = 1`
it is the intercept Jacobian `DT₀` (`aInt_eq_gMat`). -/
noncomputable def gMat (α β κ σ φπ φx r : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (r / (1 - α * β * r)) • matS α β κ σ φπ φx + (r / (1 - β * r)) • matD β κ σ φπ φx

/-- Woodford (2003), p. 275: `DT₀ = G(1)`. -/
theorem aInt_eq_gMat (α β κ σ φπ φx : ℝ) : aInt α β κ σ φπ φx = gMat α β κ σ φπ φx 1 := by
  simp [aInt, gMat]

/-- Woodford (2003), p. 275 ("if private agents have mean beliefs in this subspace, the actual
means will also lie in this subspace"): the response columns satisfy the Taylor rule,
`colS₂ = φ_π colS₀ + (φ_x/4) colS₁`. -/
theorem colS_two (σ κ φπ φx : ℝ) :
    colS σ κ φπ φx 2 = φπ * colS σ κ φπ φx 0 + φx / 4 * colS σ κ φπ φx 1 := by
  simp [colS]
  ring

/-- Woodford (2003), p. 275: `colD₂ = φ_π colD₀ + (φ_x/4) colD₁`. -/
theorem colD_two (σ κ φπ φx : ℝ) :
    colD σ κ φπ φx 2 = φπ * colD σ κ φπ φx 0 + φx / 4 * colD σ κ φπ φx 1 := by
  simp [colD]
  ring

/-- Woodford (2003), p. 275: the range of every `G(ρ)` lies in the Taylor-rule plane
`î = φ_π π + φ_x x/4`. -/
theorem gMat_row (α β κ σ φπ φx r : ℝ) (j : Fin 3) :
    gMat α β κ σ φπ φx r 2 j =
      φπ * gMat α β κ σ φπ φx r 0 j + φx / 4 * gMat α β κ σ φπ φx r 1 j := by
  simp only [gMat, matS, matD, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply,
    smul_eq_mul, colS_two, colD_two]
  ring

/-- Woodford (2003), p. 275: the `2 × 2` matrix `B̃(ρ)` of `G(ρ)` on the Taylor-rule plane;
`B̃(1)` is the book's `B̃` replacing `B` in (2.19). -/
noncomputable def bTil (α β κ σ φπ φx r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  restr (gMat α β κ σ φπ φx r) φπ (φx / 4)

/-- Woodford (2003), p. 275: `G(ρ)` is E-stable iff `B̃(ρ)` is. -/
theorem eStable_gMat_iff (α β κ σ φπ φx r : ℝ) :
    EStable (gMat α β κ σ φπ φx r) ↔ EStable (bTil α β κ σ φπ φx r) :=
  eStable_three_iff _ _ _ (gMat_row α β κ σ φπ φx r)

/-- Woodford (2003), p. 275: the Routh determinant of `B̃(ρ)` times `Δ(1 − αβρ)(1 − βρ)`:
`1 − (1 + β + κσ)ρ + βρ² + σκφ_π + (1 − βρ)σφ_x/4`. -/
noncomputable def nPoly (β κ σ φπ φx r : ℝ) : ℝ :=
  1 - (1 + β + κ * σ) * r + β * r ^ 2 + σ * κ * φπ + (1 - β * r) * (σ * φx / 4)

/-- Woodford (2003), p. 275: the Routh trace term `2 − tr B̃(ρ)` times
`Δ(1 − αβρ)(1 − βρ)`. -/
noncomputable def trPoly (α β κ σ φπ φx r : ℝ) : ℝ :=
  2 * (1 - α * β * r) * (1 - β * r) - (1 - α) * β * r * (1 - β * r) -
    (κ * σ + 1 - β) * r * (1 - α * β * r) + σ * κ * ((1 - α * β * r) + (1 - β * r)) * φπ +
    ((1 - α * β * r) * (1 - β * r) + (1 - β * r) + (1 - α) * β ^ 2 * r ^ 2) * (σ * φx / 4)

/-- Woodford (2003), p. 275 (Preston (2005), App. 4, the coefficient `c` of the quadratic):
`Δ(1 − αβρ)(1 − βρ)(det B̃ − tr B̃ + 1) = nPoly(ρ)` — independent of `α`. -/
theorem bTil_det_identity {α β κ σ φπ φx r : ℝ} (hΔ : taylorDelta σ κ φπ φx ≠ 0)
    (hP : 1 - α * β * r ≠ 0) (hQ : 1 - β * r ≠ 0) :
    taylorDelta σ κ φπ φx * (1 - α * β * r) * (1 - β * r) *
        (det2 (bTil α β κ σ φπ φx r) - tr2 (bTil α β κ σ φπ φx r) + 1) =
      nPoly β κ σ φπ φx r := by
  have hΔe : taylorDelta σ κ φπ φx = 1 + σ * φx / 4 + σ * κ * φπ := rfl
  simp only [bTil, restr, gMat, matS, matD, det2, tr2, Matrix.add_apply, Matrix.smul_apply,
    vecMulVec_apply, smul_eq_mul, colS, colD, supplyW, demandW, nPoly, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
    Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue]
  field_simp
  rw [hΔe]
  ring

/-- Woodford (2003), p. 275 (Preston (2005), App. 4, the coefficient `b`):
`Δ(1 − αβρ)(1 − βρ)(2 − tr B̃) = trPoly(ρ)`. -/
theorem bTil_tr_identity {α β κ σ φπ φx r : ℝ} (hΔ : taylorDelta σ κ φπ φx ≠ 0)
    (hP : 1 - α * β * r ≠ 0) (hQ : 1 - β * r ≠ 0) :
    taylorDelta σ κ φπ φx * (1 - α * β * r) * (1 - β * r) *
        (2 - tr2 (bTil α β κ σ φπ φx r)) = trPoly α β κ σ φπ φx r := by
  have hΔe : taylorDelta σ κ φπ φx = 1 + σ * φx / 4 + σ * κ * φπ := rfl
  simp only [bTil, restr, gMat, matS, matD, tr2, Matrix.add_apply, Matrix.smul_apply,
    vecMulVec_apply, smul_eq_mul, colS, colD, supplyW, demandW, trPoly, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
    Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue]
  field_simp
  rw [hΔe]
  ring

/-! ### The Routh conditions under the Taylor principle -/

/-- Woodford (2003), p. 275: `nPoly(ρ) = (1 − ρ)(1 − βρ + κσ) + σκ(φ_π + (1 − β)φ_x/(4κ) − 1)
+ β(1 − ρ)σφ_x/4`. -/
theorem nPoly_eq {β κ σ φπ φx : ℝ} (hκ : κ ≠ 0) (r : ℝ) :
    nPoly β κ σ φπ φx r = (1 - r) * (1 - β * r + κ * σ) + σ * κ * (taylorLHS β κ φπ φx - 1) +
      β * (1 - r) * (σ * φx / 4) := by
  unfold nPoly taylorLHS
  field_simp
  ring

/-- Woodford (2003), p. 275: at `ρ = 1`, `nPoly(1) = σκ(φ_π + (1 − β)φ_x/(4κ) − 1)`, the
left side of (2.7) minus one. -/
theorem nPoly_one {β κ σ φπ φx : ℝ} (hκ : κ ≠ 0) :
    nPoly β κ σ φπ φx 1 = σ * κ * (taylorLHS β κ φπ φx - 1) := by
  rw [nPoly_eq hκ]
  ring

/-- Woodford (2003), p. 275: the decomposition of `trPoly` used for its sign. -/
theorem trPoly_eq {α β κ σ φπ φx : ℝ} (hκ : κ ≠ 0) (r : ℝ) :
    trPoly α β κ σ φπ φx r = ((1 - β * r) ^ 2 + (1 - α * β * r) * (1 - r) +
        σ * κ * ((1 - α * β * r) * (1 - r) + (1 - β * r))) +
      ((1 - α * β * r) + (1 - β * r)) * (σ * κ * (taylorLHS β κ φπ φx - 1)) +
      ((1 - α * β * r) * β * (1 - r) + β * (1 - β * r) + (1 - α) * β ^ 2 * r ^ 2) *
        (σ * φx / 4) := by
  unfold trPoly taylorLHS
  field_simp
  ring

/-- Woodford (2003), p. 275 (Preston (2005), App. 4, `c > 0`): under the Taylor principle
`nPoly(ρ) > 0` for every real `ρ ≤ 1`. -/
theorem nPoly_pos {β κ σ φπ φx r : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hx : 0 ≤ φx) (hT : 1 < taylorLHS β κ φπ φx) (hr : r ≤ 1) :
    0 < nPoly β κ σ φπ φx r := by
  rw [nPoly_eq hκ.ne']
  have h1 : 0 ≤ (1 - r) * (1 - β * r + κ * σ) := by
    refine mul_nonneg (by linarith) ?_
    nlinarith [mul_pos hκ hσ]
  have h2 : 0 < σ * κ * (taylorLHS β κ φπ φx - 1) := by
    have := mul_pos hσ hκ
    have : 0 < taylorLHS β κ φπ φx - 1 := by linarith
    positivity
  have h3 : 0 ≤ β * (1 - r) * (σ * φx / 4) := by
    have : 0 ≤ 1 - r := by linarith
    positivity
  linarith

/-- Woodford (2003), p. 275 (Preston (2005), App. 4, `b > 0`): under the Taylor principle
`trPoly(ρ) > 0` for every real `ρ ≤ 1`. -/
theorem trPoly_pos {α β κ σ φπ φx r : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hx : 0 ≤ φx) (hT : 1 < taylorLHS β κ φπ φx)
    (hr : r ≤ 1) : 0 < trPoly α β κ σ φπ φx r := by
  rw [trPoly_eq hκ.ne']
  have hQ : 0 < 1 - β * r := by nlinarith
  have hab : α * β < 1 := by nlinarith
  have hP : 0 < 1 - α * β * r := by
    nlinarith [mul_nonneg (mul_nonneg hα0 hβ0.le) (sub_nonneg.2 hr)]
  have h1r : 0 ≤ 1 - r := by linarith
  have hsk := mul_pos hσ hκ
  have hT' : 0 < taylorLHS β κ φπ φx - 1 := by linarith
  have e1 : 0 < (1 - β * r) ^ 2 + (1 - α * β * r) * (1 - r) +
      σ * κ * ((1 - α * β * r) * (1 - r) + (1 - β * r)) := by positivity
  have e2 : 0 < ((1 - α * β * r) + (1 - β * r)) * (σ * κ * (taylorLHS β κ φπ φx - 1)) := by
    positivity
  have e3 : 0 ≤ ((1 - α * β * r) * β * (1 - r) + β * (1 - β * r) + (1 - α) * β ^ 2 * r ^ 2) *
      (σ * φx / 4) := by
    have : 0 ≤ 1 - α := by linarith
    positivity
  linarith

/-- Woodford (2003), p. 275 (Preston (2005), App. 4): **under the Taylor principle every
`G(ρ)`, `ρ ≤ 1` real, is E-stable** (all eigenvalues have real part `< 1`); in particular the
intercept Jacobian `DT₀ = G(1)` and the blocks `G(ρ_k)` for the real eigenvalues `ρ_k ∈ (−1, 1)`
of `C`. -/
theorem eStable_gMat_of_taylor {α β κ σ φπ φx r : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hπ : 0 ≤ φπ) (hx : 0 ≤ φx)
    (hT : 1 < taylorLHS β κ φπ φx) (hr : r ≤ 1) : EStable (gMat α β κ σ φπ φx r) := by
  rw [eStable_gMat_iff, eStable_iff_routh]
  have hΔ := taylorDelta_pos hσ hκ hπ hx
  have hQ : 0 < 1 - β * r := by nlinarith
  have hab : α * β < 1 := by nlinarith
  have hP : 0 < 1 - α * β * r := by
    nlinarith [mul_nonneg (mul_nonneg hα0 hβ0.le) (sub_nonneg.2 hr)]
  have hD : 0 < taylorDelta σ κ φπ φx * (1 - α * β * r) * (1 - β * r) := by positivity
  have ht := bTil_tr_identity hΔ.ne' hP.ne' hQ.ne' (α := α) (β := β) (φx := φx)
  have hd := bTil_det_identity hΔ.ne' hP.ne' hQ.ne' (α := α) (β := β) (φx := φx)
  have htp := trPoly_pos hα0 hα1 hβ0 hβ1 hκ hσ hx hT hr (φπ := φπ)
  have hnp := nPoly_pos hβ0 hβ1 hκ hσ hx hT hr (φπ := φπ)
  constructor
  · have : 0 < 2 - tr2 (bTil α β κ σ φπ φx r) := by
      by_contra hc
      push Not at hc
      nlinarith
    linarith
  · by_contra hc
    push Not at hc
    nlinarith

/-- Woodford (2003), p. 275 and (2.7) (necessity): if the intercept Jacobian `DT₀ = G(1)` is
E-stable then the Taylor principle holds. -/
theorem taylor_of_eStable_aInt {α β κ σ φπ φx : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hπ : 0 ≤ φπ) (hx : 0 ≤ φx)
    (h : EStable (aInt α β κ σ φπ φx)) : 1 < taylorLHS β κ φπ φx := by
  rw [aInt_eq_gMat, eStable_gMat_iff, eStable_iff_routh] at h
  have hΔ := taylorDelta_pos hσ hκ hπ hx
  have hQ : 0 < 1 - β * 1 := by linarith
  have hP : 0 < 1 - α * β * 1 := by nlinarith
  have hD : 0 < taylorDelta σ κ φπ φx * (1 - α * β * 1) * (1 - β * 1) := by positivity
  have hd := bTil_det_identity hΔ.ne' hP.ne' hQ.ne' (α := α) (β := β) (φx := φx)
  rw [nPoly_one hκ.ne'] at hd
  have : 0 < σ * κ * (taylorLHS β κ φπ φx - 1) := by
    rw [← hd]
    exact mul_pos hD (by linarith [h.2])
  have hsk := mul_pos hσ hκ
  by_contra hc
  push Not at hc
  nlinarith

/-- Woodford (2003), p. 275: **the intercept Jacobian `DT₀` is E-stable iff (2.7)**. -/
theorem eStable_aInt_iff {α β κ σ φπ φx : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hπ : 0 ≤ φπ) (hx : 0 ≤ φx) :
    EStable (aInt α β κ σ φπ φx) ↔ 1 < taylorLHS β κ φπ φx := by
  refine ⟨taylor_of_eStable_aInt hα0 hα1 hβ0 hβ1 hκ hσ hπ hx, fun hT => ?_⟩
  rw [aInt_eq_gMat]
  exact eStable_gMat_of_taylor hα0 hα1 hβ0 hβ1 hκ hσ hπ hx hT le_rfl

/-! ### The slope block `H`: eigenvalues come from the blocks `G(ρ)` -/

/-- Woodford (2003), p. 275 (Preston (2005), App. 4, where `C` is assumed diagonalisable; here
no diagonalisability is needed): if `(I − a₁C)K₁ = C`, `(I − a₂C)K₂ = C`, `K₁, K₂` commute with
`C` and `1 − aᵢρ ≠ 0` on the spectrum of `C`, then every eigenvalue `μ` of
`K₁′ ⊗ A₁ + K₂′ ⊗ A₂` is an eigenvalue of `ρ/(1 − a₁ρ) A₁ + ρ/(1 − a₂ρ) A₂` for some eigenvalue
`ρ` of `C`. Proof by a common eigenvector of the commuting maps `X ↦ A₁XK₁ + A₂XK₂` and
`X ↦ XC`. -/
theorem exists_isEig_of_isEig_kronSum {n : ℕ} {m : Type*} [Fintype m]
    {C K1 K2 : Matrix (Fin n) (Fin n) ℂ} {A1 A2 : Matrix m m ℂ} {a1 a2 μ : ℂ}
    (hK1 : (1 - a1 • C) * K1 = C) (hK2 : (1 - a2 • C) * K2 = C)
    (hc1 : C * K1 = K1 * C) (hc2 : C * K2 = K2 * C)
    (hρ : ∀ ρ, KroneckerSpectrum.IsEig C ρ → 1 - a1 * ρ ≠ 0 ∧ 1 - a2 * ρ ≠ 0)
    (h : KroneckerSpectrum.IsEig (K1ᵀ ⊗ₖ A1 + K2ᵀ ⊗ₖ A2) μ) :
    ∃ ρ, KroneckerSpectrum.IsEig C ρ ∧
      KroneckerSpectrum.IsEig ((ρ / (1 - a1 * ρ)) • A1 + (ρ / (1 - a2 * ρ)) • A2) μ := by
  classical
  set Hm : Matrix (Fin n × m) (Fin n × m) ℂ := K1ᵀ ⊗ₖ A1 + K2ᵀ ⊗ₖ A2 with hHm
  set P : Matrix (Fin n × m) (Fin n × m) ℂ := Cᵀ ⊗ₖ (1 : Matrix m m ℂ) with hP
  have hcomm : Hm * P = P * Hm := by
    simp only [hHm, hP, Matrix.add_mul, Matrix.mul_add, ← mul_kronecker_mul, Matrix.mul_one,
      Matrix.one_mul, ← transpose_mul, hc1, hc2]
  set E : Submodule ℂ (Fin n × m → ℂ) := Module.End.eigenspace (mulVecLin Hm) μ with hE
  have memE : ∀ x, x ∈ E ↔ Hm *ᵥ x = μ • x := fun x => by
    rw [hE, Module.End.mem_eigenspace_iff, mulVecLin_apply]
  obtain ⟨v, hv0, hv⟩ := h
  have hEne : E ≠ ⊥ := by
    intro hbot
    have : v ∈ E := (memE v).mpr hv
    rw [hbot, Submodule.mem_bot] at this
    exact hv0 this
  have hPE : ∀ x ∈ E, mulVecLin P x ∈ E := by
    intro x hx
    rw [memE] at hx ⊢
    rw [mulVecLin_apply, mulVec_mulVec, hcomm, ← mulVec_mulVec, hx, mulVec_smul]
  obtain ⟨w, hwE, hw0, ρ, hρw⟩ :=
    KroneckerSpectrum.exists_eigenvector_mem (mulVecLin P) E hEne hPE
  rw [mulVecLin_apply] at hρw
  have hHw := (memE w).mp hwE
  set X : Matrix m (Fin n) ℂ := Matrix.of fun i k => w (k, i) with hX
  have hvecX : vec X = w := by
    funext ⟨k, i⟩
    rfl
  have hX0 : X ≠ 0 := by
    intro h0
    apply hw0
    rw [← hvecX, h0]
    rfl
  have hXC : X * C = ρ • X := by
    apply vec_inj.mp
    have := KroneckerSpectrum.vec_mul_mul (1 : Matrix m m ℂ) X C
    rw [Matrix.one_mul, hvecX] at this
    rw [← this, vec_smul, hvecX]
    exact hρw
  have hHX : A1 * X * K1 + A2 * X * K2 = μ • X := by
    apply vec_inj.mp
    rw [vec_add, ← KroneckerSpectrum.vec_mul_mul, ← KroneckerSpectrum.vec_mul_mul, vec_smul,
      hvecX, ← Matrix.add_mulVec]
    exact hHw
  obtain ⟨i0, k0, hik⟩ : ∃ i k, X i k ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hX0 (Matrix.ext hc)
  have hρC : KroneckerSpectrum.IsEig C ρ := by
    rw [← KroneckerSpectrum.isEig_transpose_iff]
    refine ⟨fun k => X i0 k, fun h0 => hik (congrFun h0 k0), ?_⟩
    rw [mulVec_transpose]
    funext k
    have := congrFun (congrFun hXC i0) k
    simpa [Matrix.mul_apply, vecMul, dotProduct] using this
  have hXK : ∀ (a : ℂ) (K : Matrix (Fin n) (Fin n) ℂ), (1 - a • C) * K = C →
      1 - a * ρ ≠ 0 → X * K = (ρ / (1 - a * ρ)) • X := by
    intro a K hK hne
    have e1 : X * C = ((1 - a * ρ) • X) * K := by
      conv_lhs => rw [← hK]
      rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, hXC, smul_smul]
      congr 1
      module
    have e : (1 - a * ρ) • (X * K) = ρ • X := by rw [← Matrix.smul_mul, ← e1, hXC]
    calc X * K = (1 - a * ρ)⁻¹ • ((1 - a * ρ) • (X * K)) := by
          rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      _ = (ρ / (1 - a * ρ)) • X := by rw [e, smul_smul, div_eq_inv_mul]
  obtain ⟨hne1, hne2⟩ := hρ ρ hρC
  have hG : ((ρ / (1 - a1 * ρ)) • A1 + (ρ / (1 - a2 * ρ)) • A2) * X = μ • X := by
    rw [← hHX, Matrix.mul_assoc, Matrix.mul_assoc, hXK a1 K1 hK1 hne1, hXK a2 K2 hK2 hne2,
      Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul]
  refine ⟨ρ, hρC, fun i => X i k0, fun h0 => hik (congrFun h0 i0), ?_⟩
  funext i
  have := congrFun (congrFun hG i) k0
  simpa [Matrix.mul_apply, mulVec, dotProduct] using this

/-- Woodford (2003), p. 274: `(I − aC)⁻¹ C` solves `(I − aC)K = C` when `I − aC` is
invertible. -/
theorem one_sub_smul_mul_inv_mul {n : ℕ} {C : Matrix (Fin n) (Fin n) ℝ} {a : ℝ}
    (h : (1 - a • C).det ≠ 0) : (1 - a • C) * ((1 - a • C)⁻¹ * C) = C := by
  rw [← Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h), Matrix.one_mul]

/-- Woodford (2003), p. 274: `(I − aC)⁻¹ C` commutes with `C`. -/
theorem commute_inv_mul {n : ℕ} {C : Matrix (Fin n) (Fin n) ℝ} {a : ℝ}
    (h : (1 - a • C).det ≠ 0) : C * ((1 - a • C)⁻¹ * C) = ((1 - a • C)⁻¹ * C) * C := by
  set N := 1 - a • C with hN
  have hu : IsUnit N.det := isUnit_iff_ne_zero.mpr h
  have hNC : N * C = C * N := by
    rw [hN, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul]
  have hCN : C * N⁻¹ = N⁻¹ * C := by
    calc C * N⁻¹ = (N⁻¹ * N) * C * N⁻¹ := by rw [nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = N⁻¹ * (N * C) * N⁻¹ := by simp only [Matrix.mul_assoc]
      _ = N⁻¹ * (C * N) * N⁻¹ := by rw [hNC]
      _ = N⁻¹ * C * (N * N⁻¹) := by simp only [Matrix.mul_assoc]
      _ = N⁻¹ * C := by rw [mul_nonsing_inv _ hu, Matrix.mul_one]
  rw [← Matrix.mul_assoc, hCN, Matrix.mul_assoc]

/-- Woodford (2003), p. 274: complexification of `I − aC`. -/
theorem map_one_sub_smul {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) :
    (1 - a • C).map Complex.ofReal = 1 - (a : ℂ) • C.map Complex.ofReal := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

/-- Woodford (2003), p. 274: complexification is multiplicative. -/
theorem map_ofReal_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    (A * B).map Complex.ofReal = A.map Complex.ofReal * B.map Complex.ofReal :=
  Matrix.map_mul (f := Complex.ofRealHom)

/-- Woodford (2003), p. 275: **every eigenvalue of `H` is an eigenvalue of `G(ρ)` (complexified)
for an eigenvalue `ρ` of `C`**, when `C` is stationary and `0 ≤ α < 1`, `0 < β < 1`. -/
theorem isEig_hMat_sub {n : ℕ} {α β κ σ φπ φx : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ‖ρ‖ < 1) {μ : ℂ}
    (h : KroneckerSpectrum.IsEig ((hMat α β κ σ φπ φx C).map Complex.ofReal) μ) :
    ∃ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ ∧
      KroneckerSpectrum.IsEig ((ρ / (1 - ((α * β : ℝ) : ℂ) * ρ)) •
          (matS α β κ σ φπ φx).map Complex.ofReal +
        (ρ / (1 - (β : ℂ) * ρ)) • (matD β κ σ φπ φx).map Complex.ofReal) μ := by
  have hab : |α * β| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  have hb : |β| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have hd1 := det_one_sub_smul_ne_zero hC hab
  have hd2 := det_one_sub_smul_ne_zero hC hb
  set K1 := (1 - (α * β) • C)⁻¹ * C with hK1d
  set K2 := (1 - β • C)⁻¹ * C with hK2d
  have hK1 : (1 - ((α * β : ℝ) : ℂ) • C.map Complex.ofReal) * K1.map Complex.ofReal =
      C.map Complex.ofReal := by
    rw [← map_one_sub_smul, ← map_ofReal_mul, one_sub_smul_mul_inv_mul hd1]
  have hK2 : (1 - (β : ℂ) • C.map Complex.ofReal) * K2.map Complex.ofReal =
      C.map Complex.ofReal := by
    rw [← map_one_sub_smul, ← map_ofReal_mul, one_sub_smul_mul_inv_mul hd2]
  have hc1 : C.map Complex.ofReal * K1.map Complex.ofReal =
      K1.map Complex.ofReal * C.map Complex.ofReal := by
    rw [← map_ofReal_mul, ← map_ofReal_mul, commute_inv_mul hd1]
  have hc2 : C.map Complex.ofReal * K2.map Complex.ofReal =
      K2.map Complex.ofReal * C.map Complex.ofReal := by
    rw [← map_ofReal_mul, ← map_ofReal_mul, commute_inv_mul hd2]
  have hH : (hMat α β κ σ φπ φx C).map Complex.ofReal =
      (K1.map Complex.ofReal)ᵀ ⊗ₖ (matS α β κ σ φπ φx).map Complex.ofReal +
        (K2.map Complex.ofReal)ᵀ ⊗ₖ (matD β κ σ φπ φx).map Complex.ofReal := by
    rw [hMat, Matrix.map_add Complex.ofReal Complex.ofReal_add,
      KroneckerSpectrum.kronecker_map_ofReal,
      KroneckerSpectrum.kronecker_map_ofReal, KroneckerSpectrum.transpose_map_ofReal,
      KroneckerSpectrum.transpose_map_ofReal]
  rw [hH] at h
  refine exists_isEig_of_isEig_kronSum hK1 hK2 hc1 hc2 (fun ρ hρ => ?_) h
  have hn := hC ρ hρ
  have hne : ∀ a : ℝ, |a| ≤ 1 → 1 - (a : ℂ) * ρ ≠ 0 := by
    intro a ha h0
    have h1 : (a : ℂ) * ρ = 1 := by linear_combination -h0
    have h2 := congrArg norm h1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_one] at h2
    nlinarith [norm_nonneg ρ, abs_nonneg a]
  exact ⟨hne _ hab, hne _ hb⟩

/-- Woodford (2003), p. 275: for real `ρ`, the complexified block is `G(ρ)` complexified. -/
theorem gMat_map (α β κ σ φπ φx r : ℝ) :
    (gMat α β κ σ φπ φx r).map Complex.ofReal =
      ((r : ℂ) / (1 - ((α * β : ℝ) : ℂ) * r)) • (matS α β κ σ φπ φx).map Complex.ofReal +
        ((r : ℂ) / (1 - (β : ℂ) * r)) • (matD β κ σ φπ φx).map Complex.ofReal := by
  ext i j
  simp [gMat]

/-- Woodford (2003), p. 275 (Preston (2005), App. 4): **with real stationary eigenvalues of `C`
and the Taylor principle, `H` is E-stable.** -/
theorem eStable_hMat_of_taylor {n : ℕ} {α β κ σ φπ φx : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hπ : 0 ≤ φπ) (hx : 0 ≤ φx)
    {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ρ.im = 0 ∧ ‖ρ‖ < 1)
    (hT : 1 < taylorLHS β κ φπ φx) : EStable (hMat α β κ σ φπ φx C) := by
  rw [eStable_iff]
  intro μ hμ
  obtain ⟨ρ, hρ, hG⟩ := isEig_hMat_sub hα0 hα1 hβ0 hβ1 (fun ρ hρ => (hC ρ hρ).2) hμ
  obtain ⟨him, hnorm⟩ := hC ρ hρ
  have hρr : ρ = (ρ.re : ℂ) := Complex.ext rfl (by simp [him])
  have hr : ρ.re ≤ 1 := by
    have := Complex.abs_re_le_norm ρ
    have := (abs_le.mp (this.trans hnorm.le)).2
    exact this
  rw [hρr, ← gMat_map] at hG
  exact (eStable_iff _).mp (eStable_gMat_of_taylor hα0 hα1 hβ0 hβ1 hκ hσ hπ hx hT hr) μ hG

/-! ### Proposition 4.10 -/

/-- Woodford (2003), p. 275: `DT_Φ = blockdiag(DT₀, H)` is E-stable iff both blocks are. -/
theorem eStable_dTP_iff_and {n : ℕ} (α β κ σ φπ φx : ℝ) (C : Matrix (Fin n) (Fin n) ℝ) :
    EStable (dTP α β κ σ φπ φx C) ↔
      EStable (aInt α β κ σ φπ φx) ∧ EStable (hMat α β κ σ φπ φx C) := by
  simp only [eStable_iff, dTP, KroneckerSpectrum.fromBlocks_map_ofReal,
    KroneckerSpectrum.isEig_fromBlocks_iff]
  constructor
  · intro h
    exact ⟨fun μ hμ => h μ (Or.inl hμ), fun μ hμ => h μ (Or.inr hμ)⟩
  · rintro ⟨h1, h2⟩ μ (hμ | hμ)
    · exact h1 μ hμ
    · exact h2 μ hμ

/-- Woodford (2003), Proposition 4.10 (necessity, for every `C`): E-stability of `DT_Φ` implies
the Taylor principle (2.7). -/
theorem taylor_of_eStable_dTP {n : ℕ} {α β κ σ φπ φx : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hπ : 0 ≤ φπ) (hx : 0 ≤ φx)
    (C : Matrix (Fin n) (Fin n) ℝ) (h : EStable (dTP α β κ σ φπ φx C)) :
    1 < taylorLHS β κ φπ φx :=
  taylor_of_eStable_aInt hα0 hα1 hβ0 hβ1 hκ hσ hπ hx ((eStable_dTP_iff_and _ _ _ _ _ _ C).mp h).1

/-- Woodford (2003), Proposition 4.10 at the level of the Jacobian: with real eigenvalues of
`C` inside the unit circle, `DT_Φ` is E-stable iff (2.7). -/
theorem eStable_dTP_iff {n : ℕ} {α β κ σ φπ φx : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hπ : 0 ≤ φπ) (hx : 0 ≤ φx)
    {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ρ.im = 0 ∧ ‖ρ‖ < 1) :
    EStable (dTP α β κ σ φπ φx C) ↔ 1 < taylorLHS β κ φπ φx := by
  refine ⟨taylor_of_eStable_dTP hα0 hα1 hβ0 hβ1 hκ hσ hπ hx C, fun hT => ?_⟩
  rw [eStable_dTP_iff_and]
  exact ⟨(eStable_aInt_iff hα0 hα1 hβ0 hβ1 hκ hσ hπ hx).mpr hT,
    eStable_hMat_of_taylor hα0 hα1 hβ0 hβ1 hκ hσ hπ hx hC hT⟩

/-- Woodford (2003), **Proposition 4.10** (p. 274; Preston (2005), Proposition 2): let the
exogenous states follow (2.24) with every eigenvalue of `C` real and inside the unit circle;
let inflation and the output gap be determined by Preston's long-horizon rules (2.29)–(2.30)
under beliefs `(Φ̂, Ĉ)` estimated by regression of `z_τ` and `s_τ` on `s̄_{τ−1}`
(`decisionRules_iff`, `E_succ_eq_tMapP`), and policy by the Taylor rule (1.14) with
`φ_π, φ_x ≥ 0`. Then **the r.e.e. `(Φ̄, C)` — any fixed point of the `T`-map — is E-stable iff
the Taylor principle (2.7) holds.** Here `0 < β < 1`, `0 ≤ α < 1`, `κ, σ > 0`. -/
theorem prop_4_10 {n : ℕ} {α β κ σ φπ φx c : ℝ} {gr gi : Fin n → ℝ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hπ : 0 ≤ φπ)
    (hx : 0 ≤ φx) {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ρ.im = 0 ∧ ‖ρ‖ < 1)
    {v : IdxP n → ℝ} (hfix : tVecP α β κ σ φπ φx c gr gi C v = v) :
    EStableAt (tVecP α β κ σ φπ φx c gr gi C) v ↔ 1 < taylorLHS β κ φπ φx := by
  have hC' : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ‖ρ‖ < 1 :=
    fun ρ hρ => (hC ρ hρ).2
  have hab : |α * β| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  have hb : |β| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  rw [eStableAt_tVecP_iff hfix (det_one_sub_smul_ne_zero hC' hab)
    (det_one_sub_smul_ne_zero hC' hb)]
  exact eStable_dTP_iff hα0 hα1 hβ0 hβ1 hκ hσ hπ hx hC

/-- Woodford (2003), Proposition 4.10, **necessity for every `C`**: if a fixed point of the
`T`-map is E-stable, the Taylor principle holds — no assumption on `C` at all (stationarity,
real eigenvalues) is needed for this half. -/
theorem taylor_of_eStableAt {n : ℕ} {α β κ σ φπ φx c : ℝ} {gr gi : Fin n → ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hπ : 0 ≤ φπ) (hx : 0 ≤ φx) {C : Matrix (Fin n) (Fin n) ℝ} {v : IdxP n → ℝ}
    (h : EStableAt (tVecP α β κ σ φπ φx c gr gi C) v) : 1 < taylorLHS β κ φπ φx :=
  taylor_of_eStable_dTP hα0 hα1 hβ0 hβ1 hκ hσ hπ hx C (eStable_dTP_of_eStableAt h)

/-! ### The fixed point: existence and uniqueness -/

/-- Woodford (2003), p. 274: the constant term of the affine belief part of the `T`-map. -/
noncomputable def kP {n : ℕ} (α β κ σ φπ φx c : ℝ) (gr gi : Fin n → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) : Fin 3 ⊕ (Fin n × Fin 3) → ℝ :=
  Learning.Regression.vecBelief (interceptP α β κ σ φπ φx c 0,
    slopeP α β κ σ φπ φx gr gi 0 C * C)

/-- Woodford (2003), p. 274: `v` is a fixed point of the `T`-map iff its `Ĉ`-part is `C` and
its belief part solves `w = k + DT_Φ w`. -/
theorem tVecP_fixed_iff {n : ℕ} (α β κ σ φπ φx c : ℝ) (gr gi : Fin n → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (v : IdxP n → ℝ) :
    tVecP α β κ σ φπ φx c gr gi C v = v ↔ v ∘ Sum.inr = vec C ∧
      v ∘ Sum.inl = kP α β κ σ φπ φx c gr gi C + dTP α β κ σ φπ φx C *ᵥ (v ∘ Sum.inl) := by
  constructor
  · intro hfix
    obtain ⟨hinr, -⟩ := unvecP_snd_of_fixed hfix
    refine ⟨hinr, ?_⟩
    have hv : v = Sum.elim (v ∘ Sum.inl) (vec C) := by
      rw [← hinr, Sum.elim_comp_inl_inr]
    conv_lhs => rw [← hfix, hv]
    exact tVecP_inl_eq α β κ σ φπ φx c gr gi C (v ∘ Sum.inl)
  · rintro ⟨hinr, hinl⟩
    have hv : v = Sum.elim (v ∘ Sum.inl) (vec C) := by
      rw [← hinr, Sum.elim_comp_inl_inr]
    have h1 : tVecP α β κ σ φπ φx c gr gi C v ∘ Sum.inl = v ∘ Sum.inl := by
      conv_lhs => rw [hv]
      rw [tVecP_inl_eq]
      exact hinl.symm
    funext x
    rcases x with x | x
    · exact congrFun h1 x
    · exact (congrFun (tVecP_inr α β κ σ φπ φx c gr gi C v) x).trans (congrFun hinr x).symm

/-- Woodford (2003), p. 274 ("the (generically unique) fixed point `(Φ̄, C)`"): when `1` is not
an eigenvalue of `DT_Φ` the `T`-map has exactly one fixed point. -/
theorem fixed_existsUnique_of_det {n : ℕ} (α β κ σ φπ φx c : ℝ) (gr gi : Fin n → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (hdet : (1 - dTP α β κ σ φπ φx C).det ≠ 0) :
    ∃! v, tVecP α β κ σ φπ φx c gr gi C v = v := by
  set D := dTP α β κ σ φπ φx C
  set k := kP α β κ σ φπ φx c gr gi C
  have hu : IsUnit (1 - D).det := isUnit_iff_ne_zero.mpr hdet
  set w0 := (1 - D)⁻¹ *ᵥ k with hw0
  have hw0' : w0 = k + D *ᵥ w0 := by
    have h1 : (1 - D) *ᵥ w0 = k := by
      rw [hw0, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
    rw [sub_mulVec, one_mulVec] at h1
    rw [← h1]
    abel
  refine ⟨Sum.elim w0 (vec C), ?_, fun v hv => ?_⟩
  · beta_reduce
    rw [tVecP_fixed_iff]
    exact ⟨Sum.elim_comp_inr _ _, by rw [Sum.elim_comp_inl]; exact hw0'⟩
  · beta_reduce at hv
    rw [tVecP_fixed_iff] at hv
    obtain ⟨hinr, hinl⟩ := hv
    have hinl' : v ∘ Sum.inl = k + D *ᵥ (v ∘ Sum.inl) := hinl
    have a1 : (1 - D) *ᵥ (v ∘ Sum.inl) = k := by
      rw [sub_mulVec, one_mulVec, sub_eq_iff_eq_add]
      exact hinl'
    have a2 : (1 - D) *ᵥ w0 = k := by
      rw [sub_mulVec, one_mulVec, sub_eq_iff_eq_add]
      exact hw0'
    have h0 : (1 - D) *ᵥ (v ∘ Sum.inl - w0) = 0 := by rw [mulVec_sub, a1, a2, sub_self]
    have h1 : v ∘ Sum.inl = w0 := sub_eq_zero.mp (eq_zero_of_mulVec_eq_zero hdet h0)
    rw [← h1, ← hinr, Sum.elim_comp_inl_inr]

/-- Woodford (2003), p. 274: **under (2.7), with real stationary eigenvalues of `C`, the
r.e.e. `(Φ̄, C)` exists and is unique** (`1` is not an eigenvalue of the E-stable `DT_Φ`). -/
theorem fixed_existsUnique_of_taylor {n : ℕ} {α β κ σ φπ φx c : ℝ} {gr gi : Fin n → ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hπ : 0 ≤ φπ) (hx : 0 ≤ φx) {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ρ.im = 0 ∧ ‖ρ‖ < 1)
    (hT : 1 < taylorLHS β κ φπ φx) : ∃! v, tVecP α β κ σ φπ φx c gr gi C v = v := by
  have hE := (eStable_dTP_iff hα0 hα1 hβ0 hβ1 hκ hσ hπ hx hC).mpr hT
  refine fixed_existsUnique_of_det α β κ σ φπ φx c gr gi C
    (KroneckerSpectrum.det_one_sub_ne_zero _ fun h => ?_)
  have := (eStable_iff _).mp hE 1 h
  simp at this

/-- Woodford (2003), **Proposition 4.10, complete form**: under the hypotheses of `prop_4_10`
and the Taylor principle the r.e.e. exists, is unique and is E-stable; and conversely, if any
fixed point is E-stable, the Taylor principle holds. -/
theorem prop_4_10_existsUnique {n : ℕ} {α β κ σ φπ φx c : ℝ} {gr gi : Fin n → ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hπ : 0 ≤ φπ) (hx : 0 ≤ φx) {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ρ.im = 0 ∧ ‖ρ‖ < 1) :
    1 < taylorLHS β κ φπ φx ↔ ∃! v, tVecP α β κ σ φπ φx c gr gi C v = v ∧
      EStableAt (tVecP α β κ σ φπ φx c gr gi C) v := by
  constructor
  · intro hT
    obtain ⟨v, hv, hu⟩ := fixed_existsUnique_of_taylor (c := c) (gr := gr) (gi := gi)
      hα0 hα1 hβ0 hβ1 hκ hσ hπ hx hC hT
    exact ⟨v, ⟨hv, (prop_4_10 hα0 hα1 hβ0 hβ1 hκ hσ hπ hx hC hv).mpr hT⟩,
      fun w hw => hu w hw.1⟩
  · rintro ⟨v, ⟨-, hE⟩, -⟩
    exact taylor_of_eStableAt hα0 hα1 hβ0 hβ1 hκ hσ hπ hx hE

/-! ### Comparison with Proposition 4.9 (Bullard–Mitra one-step learning) -/

/-- Woodford (2003), p. 275 ("the conditions required for stability ... turn out to be the same
in this case as those found by Bullard and Mitra"): with real stationary eigenvalues of `C`,
Preston's Jacobian `DT_Φ` is E-stable iff the Bullard–Mitra regression Jacobian
`blockdiag(B, C′ ⊗ B)` of Proposition 4.9 is (both iff (2.7)). -/
theorem same_eStability_region {n : ℕ} {α β κ σ φπ φx : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hπ : 0 ≤ φπ) (hx : 0 ≤ φx)
    {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ρ.im = 0 ∧ ‖ρ‖ < 1) :
    EStable (dTP α β κ σ φπ φx C) ↔
      EStable (Learning.Regression.dT (taylorB β σ κ φπ φx) C) := by
  rw [eStable_dTP_iff hα0 hα1 hβ0 hβ1 hκ hσ hπ hx hC,
    Learning.BullardMitra.prop_4_9 hβ0 hβ1 hκ hσ hπ hx C fun ρ hρ => (hC ρ hρ).2]

/-- Woodford (2003), p. 275: the same comparison at the rational-expectations equilibria
themselves: Preston's r.e.e. `(Φ̄, C)` is E-stable iff the Bullard–Mitra r.e.e. `Φ̄` of
Proposition 4.9 is. -/
theorem same_eStability_region_at {n : ℕ} {α β κ σ φπ φx c : ℝ} {gr gi : Fin n → ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hπ : 0 ≤ φπ) (hx : 0 ≤ φx) {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ρ.im = 0 ∧ ‖ρ‖ < 1)
    {v : IdxP n → ℝ} (hv : tVecP α β κ σ φπ φx c gr gi C v = v) (zbar : Fin 2 → ℝ)
    (g : Fin n → ℝ) {Φ : Learning.Regression.Belief (Fin 2) (Fin n)}
    (hΦ : Learning.Regression.tMap zbar (taylorB β σ κ φπ φx) (taylorb σ κ φπ φx) g C Φ = Φ) :
    EStableAt (tVecP α β κ σ φπ φx c gr gi C) v ↔
      EStableAt (Learning.Regression.tVec zbar (taylorB β σ κ φπ φx) (taylorb σ κ φπ φx) g C)
        (Learning.Regression.vecBelief Φ) := by
  rw [prop_4_10 hα0 hα1 hβ0 hβ1 hκ hσ hπ hx hC hv,
    Learning.BullardMitra.prop_4_9_at hβ0 hβ1 hκ hσ hπ hx zbar g C (fun ρ hρ => (hC ρ hρ).2) hΦ]

/-- Woodford (2003), p. 275 ("the matrix `B` must be replaced by a matrix `B̃`"): the mean
dynamics of Preston's model are E-stable exactly when those of Bullard–Mitra (Proposition 4.8)
are. -/
theorem eStable_bTil_iff_eStable_taylorB {α β κ σ φπ φx : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hπ : 0 ≤ φπ) (hx : 0 ≤ φx) :
    EStable (bTil α β κ σ φπ φx 1) ↔ EStable (taylorB β σ κ φπ φx) := by
  rw [← eStable_gMat_iff, ← aInt_eq_gMat, eStable_aInt_iff hα0 hα1 hβ0 hβ1 hκ hσ hπ hx,
    Determinacy2Learning.prop_4_8 hβ0 hβ1 hσ hκ hπ hx]

/-- Woodford (2003), p. 275 ("even if the implied learning dynamics are generally different"):
`B̃ ≠ B` in general; e.g. `α = 0`, `β = 1/2`, `κ = σ = 1`, `φ_π = 2`, `φ_x = 0`, where
`B̃₀₀ = (1/2)/Δ` but `B₀₀ = (3/2)/Δ`. -/
theorem bTil_ne_taylorB :
    bTil 0 (1 / 2) 1 1 2 0 1 ≠ taylorB (1 / 2) 1 1 2 0 := by
  intro h
  have := congrFun (congrFun h 0) 0
  norm_num [bTil, restr, gMat, matS, matD, colS, colD, supplyW, demandW, taylorB, taylorDelta,
    vecMulVec_apply] at this

/-! ### The intuition of p. 275 -/

/-- Woodford (2003), p. 275 ("the eigenvalues of `DT` consist of a set of zeros ... plus the
eigenvalues of `DT_Φ(Φ̄)`"): at a fixed point (with `I − αβC`, `I − βC` invertible) the
eigenvalues of the full Jacobian of the `T`-map are those of `DT_Φ` and, if there are states,
`0`. -/
theorem isEig_jacobian_iff {n : ℕ} {α β κ σ φπ φx c : ℝ} {gr gi : Fin n → ℝ}
    {C : Matrix (Fin n) (Fin n) ℝ} {v : IdxP n → ℝ}
    (hfix : tVecP α β κ σ φπ φx c gr gi C v = v) (h1 : (1 - (α * β) • C).det ≠ 0)
    (h2 : (1 - β • C).det ≠ 0) (μ : ℂ) :
    KroneckerSpectrum.IsEig ((LinearMap.toMatrix'
        (fderiv ℝ (tVecP α β κ σ φπ φx c gr gi C) v : (IdxP n → ℝ) →ₗ[ℝ] (IdxP n → ℝ))).map
          Complex.ofReal) μ ↔
      KroneckerSpectrum.IsEig ((dTP α β κ σ φπ φx C).map Complex.ofReal) μ ∨
        (μ = 0 ∧ 0 < n) := by
  obtain ⟨hinr, hC⟩ := unvecP_snd_of_fixed hfix
  rw [toMatrix_fderiv_of_block _ v (vec C) (kP α β κ σ φπ φx c gr gi C) (dTP α β κ σ φπ φx C)
    (tVecP_inr α β κ σ φπ φx c gr gi C) (fun w => by
      rw [hinr]; exact tVecP_inl_eq α β κ σ φπ φx c gr gi C w)
    (differentiableAt_tVecP α β κ σ φπ φx c gr gi C v (by rwa [hC]) (by rwa [hC]))]
  rw [fromBlocks_map]
  simp only [Matrix.map_zero _ Complex.ofReal_zero]
  rw [isEig_fromBlocks_zero_iff]
  refine or_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · rintro ⟨⟨i, _⟩⟩
    exact Fin.pos i
  · intro hn
    exact ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩

/-- Woodford (2003), p. 275 ("a subset of these eigenvalues is the set of eigenvalues of
`DT₀(Φ̄₀)`"): every eigenvalue of `DT₀` is an eigenvalue of `DT_Φ`. -/
theorem isEig_dTP_of_isEig_aInt {n : ℕ} {α β κ σ φπ φx : ℝ} (C : Matrix (Fin n) (Fin n) ℝ)
    {μ : ℂ} (h : KroneckerSpectrum.IsEig ((aInt α β κ σ φπ φx).map Complex.ofReal) μ) :
    KroneckerSpectrum.IsEig ((dTP α β κ σ φπ φx C).map Complex.ofReal) μ := by
  rw [dTP, KroneckerSpectrum.fromBlocks_map_ofReal, KroneckerSpectrum.isEig_fromBlocks_iff]
  exact Or.inl h

/-- Woodford (2003), p. 275 ("all the eigenvalues of `DT_Φ − I` have a negative real part if the
eigenvalues of `DT₀ − I` do"), with real stationary eigenvalues of `C`. -/
theorem eStable_dTP_of_eStable_aInt {n : ℕ} {α β κ σ φπ φx : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hπ : 0 ≤ φπ) (hx : 0 ≤ φx)
    {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ρ.im = 0 ∧ ‖ρ‖ < 1)
    (h : EStable (aInt α β κ σ φπ φx)) : EStable (dTP α β κ σ φπ φx C) :=
  (eStable_dTP_iff hα0 hα1 hβ0 hβ1 hκ hσ hπ hx hC).mpr
    ((eStable_aInt_iff hα0 hα1 hβ0 hβ1 hκ hσ hπ hx).mp h)

/-- Woodford (2003), p. 275 ("if private agents have mean beliefs in this subspace, the actual
means `E[z]` will also lie in this subspace"): in fact the actual means always satisfy the
Taylor rule, `E[î] = c + φ_π E[π] + φ_x E[x]/4`. -/
theorem interceptP_two (α β κ σ φπ φx c : ℝ) (Φ0 : Fin 3 → ℝ) :
    interceptP α β κ σ φπ φx c Φ0 2 =
      c + φπ * interceptP α β κ σ φπ φx c Φ0 0 + φx / 4 * interceptP α β κ σ φπ φx c Φ0 1 := by
  simp only [interceptP, matS, matD, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    vecMulVec_mulVec', colS_two, colD_two, eI, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons,
    Matrix.head_cons]
  ring

/-- Woodford (2003), p. 275: a mean belief `(πᵉ, xᵉ)` extended to the Taylor-rule plane,
`(πᵉ, xᵉ, c + φ_π πᵉ + φ_x xᵉ/4)`. -/
noncomputable def embedT (φπ φx c : ℝ) (ze : Fin 2 → ℝ) : Fin 3 → ℝ :=
  ![ze 0, ze 1, c + φπ * ze 0 + φx / 4 * ze 1]

/-- Woodford (2003), p. 275: `T̂₀`, the restriction of the intercept map `T₀` to the Taylor-rule
plane, in the coordinates `(πᵉ, xᵉ)`. -/
noncomputable def tHat (α β κ σ φπ φx c : ℝ) (ze : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![interceptP α β κ σ φπ φx c (embedT φπ φx c ze) 0,
    interceptP α β κ σ φπ φx c (embedT φπ φx c ze) 1]

/-- Woodford (2003), p. 275: the plane is invariant and `T₀` acts on it as `T̂₀`. -/
theorem interceptP_embedT (α β κ σ φπ φx c : ℝ) (ze : Fin 2 → ℝ) :
    interceptP α β κ σ φπ φx c (embedT φπ φx c ze) =
      embedT φπ φx c (tHat α β κ σ φπ φx c ze) := by
  funext j
  fin_cases j
  · rfl
  · rfl
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [interceptP_two]
    rfl

/-- Woodford (2003), p. 275 ("the mapping in question is once again of the form (2.19), except
that the matrix `B` must be replaced by a matrix `B̃`"): `T̂₀` is affine with matrix
`B̃ = B̃(1)`. -/
theorem tHat_eq (α β κ σ φπ φx c : ℝ) (ze : Fin 2 → ℝ) :
    tHat α β κ σ φπ φx c ze = tHat α β κ σ φπ φx c 0 + bTil α β κ σ φπ φx 1 *ᵥ ze := by
  have e : ∀ y, interceptP α β κ σ φπ φx c y =
      interceptP α β κ σ φπ φx c 0 + gMat α β κ σ φπ φx 1 *ᵥ y := fun y => by
    rw [interceptP_eq, aInt_eq_gMat]
  funext i
  fin_cases i <;>
  · simp only [tHat, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Pi.add_apply]
    rw [e (embedT φπ φx c ze), e (embedT φπ φx c 0)]
    simp only [embedT, bTil, restr, Pi.add_apply, mulVec, dotProduct, Fin.sum_univ_three,
      Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Nat.succ_eq_add_one,
      Nat.reduceAdd, Fin.isValue, Pi.zero_apply]
    ring

/-- Woodford (2003), (2.19) with `B̃`: around any fixed point `z̄` (the r.e.e. means),
`T̂₀(zᵉ) = z̄ + B̃(zᵉ − z̄)`. -/
theorem tHat_eq_Tmap (α β κ σ φπ φx c : ℝ) {zbar : Fin 2 → ℝ}
    (hz : tHat α β κ σ φπ φx c zbar = zbar) (ze : Fin 2 → ℝ) :
    tHat α β κ σ φπ φx c ze = Tmap (bTil α β κ σ φπ φx 1) zbar ze := by
  have h2 := tHat_eq α β κ σ φπ φx c zbar
  rw [hz] at h2
  have h2' := sub_eq_of_eq_add h2
  rw [tHat_eq, Tmap, mulVec_sub,
    show zbar + (bTil α β κ σ φπ φx 1 *ᵥ ze - bTil α β κ σ φπ φx 1 *ᵥ zbar) =
      (zbar - bTil α β κ σ φπ φx 1 *ᵥ zbar) + bTil α β κ σ φπ φx 1 *ᵥ ze by abel, h2']

/-- Woodford (2003), p. 275 ("two of the three eigenvalues of `DT₀` are the eigenvalues of
`DT̂₀`"): the eigenvalues of `DT₀` are `0` and the eigenvalues of `B̃`. -/
theorem isEig_aInt_iff (α β κ σ φπ φx : ℝ) (μ : ℂ) :
    KroneckerSpectrum.IsEig ((aInt α β κ σ φπ φx).map Complex.ofReal) μ ↔
      μ = 0 ∨ KroneckerSpectrum.IsEig ((bTil α β κ σ φπ φx 1).map Complex.ofReal) μ := by
  rw [aInt_eq_gMat, bTil, ← restr_map]
  refine isEig_three_iff _ _ _ (fun j => ?_) μ
  simp [gMat_row α β κ σ φπ φx 1 j]

/-- Woodford (2003), p. 275 ("E-stability depends on the properties of the matrix `B̃` in
exactly the same way as ... Proposition 4.8"): `B̃` is E-stable iff (2.7). -/
theorem eStable_bTil_iff {α β κ σ φπ φx : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hπ : 0 ≤ φπ) (hx : 0 ≤ φx) :
    EStable (bTil α β κ σ φπ φx 1) ↔ 1 < taylorLHS β κ φπ φx := by
  rw [← eStable_gMat_iff, ← aInt_eq_gMat, eStable_aInt_iff hα0 hα1 hβ0 hβ1 hκ hσ hπ hx]

/-- Woodford (2003), p. 268 and footnote 35 (general form): the self-consistent mean beliefs of
`zᵉ ↦ z̄ + B(zᵉ − z̄)` form an infinite set (a continuum) iff `det(I − B) = 0`. -/
theorem fixed_infinite_iff_det (B : Matrix (Fin 2) (Fin 2) ℝ) (zbar : Fin 2 → ℝ) :
    {z | Tmap B zbar z = z}.Infinite ↔ (1 - B).det = 0 := by
  constructor
  · intro hinf
    by_contra hB
    apply hinf
    refine (Set.finite_singleton zbar).subset fun z hz => ?_
    exact (Tmap_fixed_unique _ zbar hB z).mp hz
  · intro hd
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hw0
    refine Set.infinite_of_injective_forall_mem (f := fun c : ℝ => zbar + c • w) ?_ ?_
    · intro c₁ c₂ h
      have := congrFun h j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_right_inj] at this
      exact mul_right_cancel₀ hj this
    · intro c
      change Tmap B zbar (zbar + c • w) = zbar + c • w
      rw [Tmap_fixed_iff_one_sub, add_sub_cancel_left, mulVec_smul, hw, smul_zero]

/-- Woodford (2003), p. 275: `det(I − B̃) = 0` iff equality holds in (2.7). -/
theorem det_one_sub_bTil_eq_zero_iff {α β κ σ φπ φx : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hπ : 0 ≤ φπ) (hx : 0 ≤ φx) :
    (1 - bTil α β κ σ φπ φx 1).det = 0 ↔ taylorLHS β κ φπ φx = 1 := by
  have hΔ := taylorDelta_pos hσ hκ hπ hx
  have hQ : 0 < 1 - β * 1 := by linarith
  have hP : 0 < 1 - α * β * 1 := by nlinarith
  have hD : 0 < taylorDelta σ κ φπ φx * (1 - α * β * 1) * (1 - β * 1) := by positivity
  have hd := bTil_det_identity hΔ.ne' hP.ne' hQ.ne' (α := α) (β := β) (φx := φx)
  rw [nPoly_one hκ.ne'] at hd
  have e : (1 - bTil α β κ σ φπ φx 1).det =
      det2 (bTil α β κ σ φπ φx 1) - tr2 (bTil α β κ σ φπ φx 1) + 1 := by
    rw [det_fin_two]
    simp [tr2, det2]
    ring
  rw [e]
  have hsk := mul_pos hσ hκ
  constructor
  · intro h0
    rw [h0, mul_zero] at hd
    have : taylorLHS β κ φπ φx - 1 = 0 := by
      rcases mul_eq_zero.mp hd.symm with h | h
      · exact absurd h hsk.ne'
      · exact h
    linarith
  · intro hT
    rw [hT, sub_self, mul_zero] at hd
    rcases mul_eq_zero.mp hd with h | h
    · exact absurd h hD.ne'
    · exact h

/-- Woodford (2003), p. 275 ("the boundary between E-instability and E-stability ... corresponds
to the case in which there exists a continuum of steady-state equilibrium inflation rates"):
the self-consistent mean beliefs of Preston's mean dynamics form a continuum iff (2.7) holds
with equality. -/
theorem steadyStates_infinite_iff {α β κ σ φπ φx : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hπ : 0 ≤ φπ) (hx : 0 ≤ φx)
    (zbar : Fin 2 → ℝ) :
    {z | Tmap (bTil α β κ σ φπ φx 1) zbar z = z}.Infinite ↔ taylorLHS β κ φπ φx = 1 := by
  rw [fixed_infinite_iff_det, det_one_sub_bTil_eq_zero_iff hα0 hα1 hβ1 hκ hσ hπ hx]

/-- Woodford (2003), p. 275 ("the conditions under which there exists a continuum of steady
states are the same for Preston's model as for that of Bullard and Mitra"): the critical
parameter values coincide. -/
theorem same_critical_values {α β κ σ φπ φx : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hπ : 0 ≤ φπ) (hx : 0 ≤ φx)
    (zbar zbar' : Fin 2 → ℝ) :
    {z | Tmap (bTil α β κ σ φπ φx 1) zbar z = z}.Infinite ↔
      {z | Tmap (taylorB β σ κ φπ φx) zbar' z = z}.Infinite := by
  rw [steadyStates_infinite_iff hα0 hα1 hβ1 hκ hσ hπ hx,
    Learning.BullardMitra.steadyStates_infinite_iff hκ hσ hπ hx]

/-- Woodford (2003), p. 275 (the `π̇ᵉ = 0` and `ẋᵉ = 0` loci): for a `2 × 2` matrix `M` with
nonzero rows, the two lines `(Md)₀ = 0` and `(Md)₁ = 0` coincide iff `det M = 0`. -/
theorem loci_coincide_iff_det (M : Matrix (Fin 2) (Fin 2) ℝ) (h0 : M 0 0 ≠ 0 ∨ M 0 1 ≠ 0)
    (h1 : M 1 0 ≠ 0 ∨ M 1 1 ≠ 0) :
    (∀ d : Fin 2 → ℝ, (M *ᵥ d) 0 = 0 ↔ (M *ᵥ d) 1 = 0) ↔ M.det = 0 := by
  have hm : ∀ d : Fin 2 → ℝ, (M *ᵥ d) 0 = M 0 0 * d 0 + M 0 1 * d 1 ∧
      (M *ᵥ d) 1 = M 1 0 * d 0 + M 1 1 * d 1 := fun d => by
    simp [mulVec, dotProduct, Fin.sum_univ_two]
  rw [det_fin_two]
  constructor
  · intro h
    have := (h ![M 0 1, -M 0 0]).mp (by rw [(hm _).1]; simp; ring)
    rw [(hm _).2] at this
    simp at this
    linarith
  · intro hd d
    rw [(hm d).1, (hm d).2]
    constructor
    · intro e
      rcases h0 with h0 | h0
      · have : (M 1 0 * d 0 + M 1 1 * d 1) * M 0 0 = 0 := by
          linear_combination M 1 0 * e + d 1 * hd
        exact (mul_eq_zero.mp this).resolve_right h0
      · have : (M 1 0 * d 0 + M 1 1 * d 1) * M 0 1 = 0 := by
          linear_combination M 1 1 * e - d 0 * hd
        exact (mul_eq_zero.mp this).resolve_right h0
    · intro e
      rcases h1 with h1 | h1
      · have : (M 0 0 * d 0 + M 0 1 * d 1) * M 1 0 = 0 := by
          linear_combination M 0 0 * e - d 1 * hd
        exact (mul_eq_zero.mp this).resolve_right h1
      · have : (M 0 0 * d 0 + M 0 1 * d 1) * M 1 1 = 0 := by
          linear_combination M 0 1 * e + d 0 * hd
        exact (mul_eq_zero.mp this).resolve_right h1

/-- Woodford (2003), p. 275 ("the boundary between E-instability and E-stability is again the
case in which the `π̇ᵉ = 0` and `ẋᵉ = 0` loci coincide"): when both rows of `B̃ − I` are
nonzero (so the loci are lines), the loci of Preston's mean dynamics coincide iff (2.7) holds
with equality. -/
theorem loci_coincide_iff {α β κ σ φπ φx : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hπ : 0 ≤ φπ) (hx : 0 ≤ φx)
    (h0 : (bTil α β κ σ φπ φx 1 - 1) 0 0 ≠ 0 ∨ (bTil α β κ σ φπ φx 1 - 1) 0 1 ≠ 0)
    (h1 : (bTil α β κ σ φπ φx 1 - 1) 1 0 ≠ 0 ∨ (bTil α β κ σ φπ φx 1 - 1) 1 1 ≠ 0) :
    (∀ d : Fin 2 → ℝ, ((bTil α β κ σ φπ φx 1 - 1) *ᵥ d) 0 = 0 ↔
        ((bTil α β κ σ φπ φx 1 - 1) *ᵥ d) 1 = 0) ↔ taylorLHS β κ φπ φx = 1 := by
  rw [loci_coincide_iff_det _ h0 h1, ← det_one_sub_bTil_eq_zero_iff hα0 hα1 hβ1 hκ hσ hπ hx]
  rw [← neg_sub, det_neg]
  simp

/-- Woodford (2003), p. 275, **"`B̃ = Ã⁻¹`" is imprecise**: `B̃` can be singular, so it is not
the inverse of any matrix, even when the Taylor principle holds (and the r.e.e. is E-stable).
Example: `α = β = 1/2`, `κ = 2`, `σ = 1`, `φ_π = 3/2`, `φ_x = 0`, where `B̃ = [[1/3, 2/3], [0, 0]]`
and `φ_π + (1 − β)φ_x/(4κ) = 3/2 > 1`. -/
theorem bTil_not_inverse :
    1 < taylorLHS (1 / 2) 2 (3 / 2) 0 ∧ (bTil (1 / 2) (1 / 2) 2 1 (3 / 2) 0 1).det = 0 ∧
      ¬ ∃ A : Matrix (Fin 2) (Fin 2) ℝ, A * bTil (1 / 2) (1 / 2) 2 1 (3 / 2) 0 1 = 1 := by
  have hd : (bTil (1 / 2) (1 / 2) 2 1 (3 / 2) 0 1).det = 0 := by
    rw [det_fin_two]
    norm_num [bTil, restr, gMat, matS, matD, colS, colD, supplyW, demandW, taylorDelta,
      vecMulVec_apply]
  refine ⟨by norm_num [taylorLHS], hd, ?_⟩
  rintro ⟨A, hA⟩
  have := congrArg Matrix.det hA
  rw [det_mul, hd, mul_zero, det_one] at this
  exact zero_ne_one this

end Woodford.NeoWicksellianFramework.Prop410
