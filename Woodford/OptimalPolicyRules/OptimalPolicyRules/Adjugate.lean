/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The adjugate factorisation (1.22)

Woodford (2003), *Interest and Prices*, Chapter 8, Section 1.4, p. 553, eq. (1.22) and fn 16.

For any square matrix `Λ` there are a matrix lag polynomial `B(L)` and a scalar lag polynomial
`α(L)` with `B(L) (I − Λ L) = α(L) I` (1.22): `α(L) = det(I − ΛL)` and `B(L)` the adjugate
("adjoint") of `I − ΛL`. Lag polynomials are polynomials in `X = L`.

## Main results

* `eq122`, `eq122_right`: (1.22) via `Matrix.adjugate_mul` over `K[X]`.
* `alpha_eval_zero`, `Bpoly_eval_zero` (fn 16): `α(0) = 1`, `B(0) = I`.
* `alpha_eq_reverse_charpoly`, `natDegree_alpha`: `α` is the reversed characteristic polynomial;
  `deg α = n − (multiplicity of the eigenvalue 0)`.
* `natDegree_alpha_eq_card_nonzero_roots`: over `ℂ`, `deg α` is the number of nonzero
  eigenvalues counted with multiplicity.
* `natDegree_alpha_le_rank`, `natDegree_Bpoly_le_rank`, `natDegree_Bpoly_le_card_sub_one`:
  the correct degree statements, `deg α ≤ rank Λ` and `deg B ≤ min(rank Λ, n − 1)`.
* `nilpotent_counterexample` (survey E18): Woodford's "`α(L)` is of order `rank Λ`" is false for
  `Λ = [0 1; 0 0]`: `α = 1` while `rank Λ = 1`.
* `natDegree_alpha_of_isUnit`: equality `deg α = rank Λ = n` for invertible `Λ`.
-/

namespace Woodford.OptimalPolicyRules.Adjugate

open Matrix Polynomial

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- Woodford (2003), eq. (1.22), p. 553: the matrix lag polynomial `I − Λ L` (with `L = X`). -/
noncomputable def lagMat (Λ : Matrix n n K) : Matrix n n K[X] := 1 - (X : K[X]) • Λ.map C

/-- Woodford (2003), p. 553: `α(L) = det(I − Λ L)`. -/
noncomputable def alpha (Λ : Matrix n n K) : K[X] := (lagMat Λ).det

/-- Woodford (2003), p. 553: `B(L)`, the adjoint (adjugate) of `I − Λ L`. -/
noncomputable def Bpoly (Λ : Matrix n n K) : Matrix n n K[X] := (lagMat Λ).adjugate

/-- Woodford (2003), eq. (1.22), p. 553: `B(L) (I − Λ L) = α(L) I`. -/
theorem eq122 (Λ : Matrix n n K) : Bpoly Λ * lagMat Λ = alpha Λ • (1 : Matrix n n K[X]) :=
  adjugate_mul _

/-- Woodford (2003), eq. (1.22), p. 553: also `(I − Λ L) B(L) = α(L) I`. -/
theorem eq122_right (Λ : Matrix n n K) :
    lagMat Λ * Bpoly Λ = alpha Λ • (1 : Matrix n n K[X]) :=
  mul_adjugate _

omit [Fintype n] in
/-- Woodford (2003), fn 16, p. 555: `I − Λ L` at `L = 0` is `I`. -/
theorem lagMat_eval_zero (Λ : Matrix n n K) : (lagMat Λ).map (eval 0) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [lagMat, h, one_apply]

/-- Woodford (2003), fn 16, p. 555: `α(0) = 1`. -/
theorem alpha_eval_zero (Λ : Matrix n n K) : (alpha Λ).eval 0 = 1 := by
  have h := RingHom.map_det (evalRingHom (0 : K)) (lagMat Λ)
  rw [coe_evalRingHom] at h
  rw [alpha, h]
  have : (evalRingHom (0 : K)).mapMatrix (lagMat Λ) = 1 := lagMat_eval_zero Λ
  rw [this, det_one]

/-- Woodford (2003), fn 16, p. 555: the constant coefficient of `α` is `1`. -/
theorem alpha_coeff_zero (Λ : Matrix n n K) : (alpha Λ).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, alpha_eval_zero]

/-- Woodford (2003), fn 16, p. 555: `B(0) = I`. -/
theorem Bpoly_eval_zero (Λ : Matrix n n K) : (Bpoly Λ).map (eval 0) = 1 := by
  have h := RingHom.map_adjugate (evalRingHom (0 : K)) (lagMat Λ)
  have h1 : (evalRingHom (0 : K)).mapMatrix (lagMat Λ) = 1 := lagMat_eval_zero Λ
  rw [h1, adjugate_one] at h
  exact h

/-- Woodford (2003), fn 16, p. 555: the constant coefficients of `B` form the identity. -/
theorem Bpoly_coeff_zero (Λ : Matrix n n K) (i j : n) :
    (Bpoly Λ i j).coeff 0 = (1 : Matrix n n K) i j := by
  rw [coeff_zero_eq_eval_zero, ← Bpoly_eval_zero Λ]
  rfl

/-- Woodford (2003), p. 553: `α ≠ 0`. -/
theorem alpha_ne_zero (Λ : Matrix n n K) : alpha Λ ≠ 0 := by
  intro h
  have := alpha_eval_zero Λ
  rw [h, eval_zero] at this
  exact zero_ne_one this

/-- Woodford (2003), p. 553: `α(L) = det(I − ΛL)` is Mathlib's reversed characteristic
polynomial. -/
theorem alpha_eq_charpolyRev (Λ : Matrix n n K) : alpha Λ = Λ.charpolyRev := rfl

/-- Woodford (2003), p. 553: `α` is the reverse of the characteristic polynomial of `Λ`. -/
theorem alpha_eq_reverse_charpoly (Λ : Matrix n n K) : alpha Λ = Λ.charpoly.reverse :=
  (reverse_charpoly Λ).symm

/-- Woodford (2003), p. 553 (survey E18, corrected): `deg α = n − m₀`, where `m₀` is the
multiplicity of `0` as a root of the characteristic polynomial (the algebraic multiplicity of
the eigenvalue `0`). -/
theorem natDegree_alpha (Λ : Matrix n n K) :
    (alpha Λ).natDegree = Fintype.card n - Λ.charpoly.rootMultiplicity 0 := by
  rw [alpha_eq_reverse_charpoly, reverse_natDegree, charpoly_natDegree_eq_dim,
    rootMultiplicity_eq_natTrailingDegree]
  simp

/-- Woodford (2003), p. 553 (survey E18, corrected): over `ℂ`, `deg α` is the number of nonzero
eigenvalues of `Λ` counted with multiplicity. -/
theorem natDegree_alpha_eq_card_nonzero_roots (Λ : Matrix n n ℂ) :
    (alpha Λ).natDegree = Multiset.card (Λ.charpoly.roots.filter (fun μ => μ ≠ 0)) := by
  rw [natDegree_alpha]
  have hsplit : Multiset.card Λ.charpoly.roots = Fintype.card n := by
    rw [← charpoly_natDegree_eq_dim Λ]
    exact (splits_iff_card_roots).mp (IsAlgClosed.splits _)
  have hfilt := Multiset.filter_add_not (fun μ : ℂ => μ = 0) Λ.charpoly.roots
  simp only [← ne_eq] at hfilt
  have hcount : Multiset.card (Λ.charpoly.roots.filter (fun μ : ℂ => μ = 0)) =
      Λ.charpoly.rootMultiplicity 0 := by
    rw [Multiset.filter_eq', Multiset.card_replicate, count_roots]
  have hc := congrArg Multiset.card hfilt
  rw [Multiset.card_add, hcount, hsplit] at hc
  omega

omit [DecidableEq n] in
/-- Woodford (2003), p. 553: a rank factorisation `Λ = U V` with `U : n × r`, `V : r × n`,
`r = rank Λ` (the columns of `U` are a basis of the column space). -/
theorem exists_rank_factorization (Λ : Matrix n n K) :
    ∃ (U : Matrix n (Fin Λ.rank) K) (V : Matrix (Fin Λ.rank) n K), Λ = U * V := by
  classical
  set R := LinearMap.range Λ.mulVecLin
  let b : Module.Basis (Fin Λ.rank) K R := Module.finBasisOfFinrankEq K R rfl
  have hcol : ∀ i, (fun r => Λ r i) ∈ R := fun i => by
    refine ⟨Pi.single i 1, ?_⟩
    rw [mulVecLin_apply, mulVec_single_one]
    rfl
  refine ⟨Matrix.of fun r j => (b j : n → K) r,
    Matrix.of fun j i => b.repr ⟨fun r => Λ r i, hcol i⟩ j, ?_⟩
  ext r i
  have h := congrArg (fun x : R => (x : n → K) r) (b.sum_repr ⟨fun r => Λ r i, hcol i⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  rw [mul_apply]
  simp only [of_apply]
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

omit [Fintype n] in
/-- Woodford (2003), p. 553: `I − (UV)L` written in the form used by `det_one_sub_mul_comm`. -/
theorem lagMat_mul {r : Type*} [Fintype r] (U : Matrix n r K)
    (V : Matrix r n K) : lagMat (U * V) = 1 - ((X : K[X]) • U.map C) * V.map C := by
  rw [lagMat, Matrix.map_mul, Matrix.smul_mul]

/-- Woodford (2003), p. 553: for `Λ = UV` with `U : n × r`, `α(L) = det(I_r − VU L)`, so
`deg α ≤ r`. -/
theorem natDegree_alpha_mul_le {r : Type*} [Fintype r] (U : Matrix n r K)
    (V : Matrix r n K) : (alpha (U * V)).natDegree ≤ Fintype.card r := by
  classical
  have h1 : alpha (U * V) = alpha (V * U) := by
    rw [alpha, alpha, lagMat_mul, det_one_sub_mul_comm, lagMat_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  rw [h1, alpha, lagMat]
  have h2 : (1 : Matrix r r K[X]) - (X : K[X]) • (V * U).map C =
      (X : K[X]) • (-(V * U)).map C + (1 : Matrix r r K).map C := by
    have hneg : (-(V * U)).map C = -((V * U).map C) :=
      Matrix.ext fun i j => by simp only [Matrix.map_apply, Matrix.neg_apply, map_neg]
    rw [hneg, smul_neg, Matrix.map_one _ (map_zero C) (map_one C)]
    abel
  rw [h2]
  exact natDegree_det_X_add_C_le (-(V * U)) 1

/-- Woodford (2003), p. 553 (survey E18, corrected): `deg α ≤ rank Λ`. -/
theorem natDegree_alpha_le_rank (Λ : Matrix n n K) : (alpha Λ).natDegree ≤ Λ.rank := by
  obtain ⟨U, V, hUV⟩ := exists_rank_factorization Λ
  have := natDegree_alpha_mul_le U V
  rw [← hUV, Fintype.card_fin] at this
  exact this

/-- Woodford (2003), p. 553 (survey E18, "at most"): every entry of `B(L) = adj(I − ΛL)` has
degree at most `n − 1`. -/
theorem natDegree_Bpoly_le_card_sub_one (Λ : Matrix n n K) (i j : n) :
    (Bpoly Λ i j).natDegree ≤ Fintype.card n - 1 := by
  rw [Bpoly, adjugate_apply, det_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  rw [Units.smul_def]
  refine (natDegree_smul_le _ _).trans ?_
  refine (natDegree_prod_le _ _).trans ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (σ.symm j))]
  have h0 : (updateRow (lagMat Λ) j (Pi.single i 1) (σ (σ.symm j)) (σ.symm j)).natDegree = 0 := by
    rw [Equiv.apply_symm_apply, updateRow_self]
    by_cases h : σ.symm j = i
    · rw [h, Pi.single_eq_same, natDegree_one]
    · rw [Pi.single_eq_of_ne h, natDegree_zero]
  rw [h0, zero_add]
  have hle : ∀ a ∈ Finset.univ.erase (σ.symm j),
      (updateRow (lagMat Λ) j (Pi.single i 1) (σ a) a).natDegree ≤ 1 := by
    intro a ha
    have hne : σ a ≠ j := by
      intro h
      apply (Finset.mem_erase.mp ha).1
      rw [← h, Equiv.symm_apply_apply]
    rw [updateRow_ne hne, lagMat]
    simp only [Matrix.sub_apply, Matrix.smul_apply, map_apply, smul_eq_mul]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · rw [one_apply]
      split_ifs <;> simp
    · exact natDegree_mul_le.trans (by simp)
  refine (Finset.sum_le_sum hle).trans ?_
  simp [Finset.card_erase_of_mem (Finset.mem_univ _)]

/-- Woodford (2003), p. 553: the adjugate is the unique matrix `B` with `(I − ΛL) B = α I`
(`α ≠ 0`, polynomials over a field form a domain). -/
theorem Bpoly_unique (Λ : Matrix n n K) {B : Matrix n n K[X]}
    (hB : lagMat Λ * B = alpha Λ • (1 : Matrix n n K[X])) : B = Bpoly Λ := by
  have h1 : Bpoly Λ * (lagMat Λ * B) = alpha Λ • B := by
    rw [← Matrix.mul_assoc, eq122, Matrix.smul_mul, Matrix.one_mul]
  rw [hB, Matrix.mul_smul, Matrix.mul_one] at h1
  refine Matrix.ext fun a b => ?_
  have := congrFun (congrFun h1 a) b
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact (mul_left_cancel₀ (alpha_ne_zero Λ) this).symm

/-- Woodford (2003), p. 553 (survey E18, "at most"): with a rank factorisation `Λ = UV` the
adjugate is `B = det(N) I + L · U adj(N) V`, `N = I − (VU) L`. -/
theorem Bpoly_of_factorization {r : Type*} [Fintype r] [DecidableEq r] (U : Matrix n r K)
    (V : Matrix r n K) :
    Bpoly (U * V) = alpha (V * U) • (1 : Matrix n n K[X]) +
      ((X : K[X]) • U.map C) * Bpoly (V * U) * V.map C := by
  symm
  apply Bpoly_unique
  have hα : alpha (U * V) = alpha (V * U) := by
    rw [alpha, alpha, lagMat_mul, det_one_sub_mul_comm, lagMat_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  rw [hα]
  set Ux := (X : K[X]) • U.map C
  have hN : lagMat (V * U) = 1 - V.map C * Ux := by
    rw [lagMat, Matrix.map_mul, Matrix.mul_smul]
  have hNB := eq122_right (V * U)
  rw [hN] at hNB
  rw [lagMat_mul]
  have key : (1 - Ux * V.map C) * (alpha (V * U) • 1 + Ux * Bpoly (V * U) * V.map C) =
      alpha (V * U) • 1 + Ux * ((1 - V.map C * Ux) * Bpoly (V * U) -
        alpha (V * U) • (1 : Matrix r r K[X])) * V.map C := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_add,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    module
  rw [key, hNB, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero]

/-- Woodford (2003), p. 553: for `Λ = UV` with `U : n × r`, every entry of `B(L)` has degree at
most `r`. -/
theorem natDegree_Bpoly_mul_le {r : Type*} [Fintype r] (U : Matrix n r K)
    (V : Matrix r n K) (i j : n) : (Bpoly (U * V) i j).natDegree ≤ Fintype.card r := by
  classical
  rw [Bpoly_of_factorization]
  have hα : (alpha (V * U)).natDegree ≤ Fintype.card r := by
    have h := natDegree_alpha_le_rank (V * U)
    exact h.trans (rank_le_card_width _)
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · rw [one_apply]
    split_ifs
    · rwa [mul_one]
    · simp
  · simp only [mul_apply, Matrix.smul_apply, map_apply, smul_eq_mul]
    refine natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
    refine (natDegree_mul_le).trans ?_
    rw [natDegree_C, add_zero]
    refine natDegree_sum_le_of_forall_le _ _ fun a _ => ?_
    refine (natDegree_mul_le).trans ?_
    have hB := natDegree_Bpoly_le_card_sub_one (V * U) a b
    have hX : (X * C (U i a)).natDegree ≤ 1 := natDegree_mul_le.trans (by simp)
    have hpos : 1 ≤ Fintype.card r := Fintype.card_pos_iff.mpr ⟨a⟩
    omega

/-- Woodford (2003), p. 553 (survey E18, "at most"): every entry of `B(L)` has degree at most
`rank Λ`. Together with `natDegree_Bpoly_le_card_sub_one`: `deg B ≤ min(rank Λ, n − 1)`. -/
theorem natDegree_Bpoly_le_rank (Λ : Matrix n n K) (i j : n) :
    (Bpoly Λ i j).natDegree ≤ Λ.rank := by
  obtain ⟨U, V, hUV⟩ := exists_rank_factorization Λ
  have := natDegree_Bpoly_mul_le U V i j
  rw [← hUV, Fintype.card_fin] at this
  exact this

/-- Woodford (2003), p. 553 (survey E18): **"`α(L)` is of order `rank Λ`" is false.** For the
nilpotent `Λ = [0 1; 0 0]`, `α(L) = det(I − ΛL) = 1` has degree `0`, while `rank Λ = 1`. -/
theorem nilpotent_counterexample :
    alpha (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) = 1 ∧
      (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).rank = 1 ∧
      (alpha (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)).natDegree <
        (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).rank := by
  have hα : alpha (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    rw [alpha, lagMat, det_fin_two]
    simp
  have hle : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).rank ≤ 1 := by
    have hfac : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) =
        (!![1; 0] : Matrix (Fin 2) (Fin 1) ℝ) * (!![0, 1] : Matrix (Fin 1) (Fin 2) ℝ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [mul_apply]
    rw [hfac]
    exact (rank_mul_le_left _ _).trans ((rank_le_width _).trans (by simp))
  have hge : 1 ≤ (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).rank := by
    unfold Matrix.rank
    rw [Submodule.one_le_finrank_iff]
    intro hbot
    have hmem : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).mulVecLin (Pi.single 1 1) ∈
        LinearMap.range (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).mulVecLin :=
      LinearMap.mem_range_self _ _
    rw [hbot, Submodule.mem_bot] at hmem
    have := congrFun hmem 0
    simp [mulVec, dotProduct, Fin.sum_univ_two] at this
  have hr : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).rank = 1 := le_antisymm hle hge
  refine ⟨hα, hr, ?_⟩
  rw [hα, hr, natDegree_one]
  norm_num

/-- Woodford (2003), p. 553: the printed claim does hold when `Λ` is invertible:
`deg α = rank Λ = n`. -/
theorem natDegree_alpha_of_isUnit (Λ : Matrix n n K) (h : IsUnit Λ) :
    (alpha Λ).natDegree = Λ.rank := by
  rw [rank_of_isUnit Λ h, natDegree_alpha, rootMultiplicity_eq_natTrailingDegree]
  have hdet : Λ.det ≠ 0 := ((isUnit_iff_isUnit_det Λ).mp h).ne_zero
  have hc : Λ.charpoly.coeff 0 ≠ 0 := by
    intro h0
    rw [det_eq_sign_charpoly_coeff, h0, mul_zero] at hdet
    exact hdet rfl
  have : (Λ.charpoly.comp (X + C 0)).natTrailingDegree = 0 := by
    simp only [map_zero, add_zero, comp_X]
    exact natTrailingDegree_eq_zero.mpr (Or.inr hc)
  rw [this, Nat.sub_zero]

end Woodford.OptimalPolicyRules.Adjugate
