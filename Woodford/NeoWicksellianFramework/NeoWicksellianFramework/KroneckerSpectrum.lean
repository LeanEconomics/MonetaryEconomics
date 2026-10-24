/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Spectra of Kronecker products and block-diagonal matrices

Woodford (2003), Appendix C.7, pp. 683–685 (proof of Proposition 4.9). The proof uses three
facts of linear algebra that Mathlib does not state in this form:

* `vec (B X C) = (Cᵀ ⊗ B) vec X` (Woodford, (C.29), p. 684): `vec_mul_mul`, restated from
  Mathlib's `Matrix.kronecker_mulVec_vec`;
* the eigenvalues of a Kronecker product `A ⊗ B` are exactly the products `α β` of an
  eigenvalue `α` of `A` and an eigenvalue `β` of `B` (Woodford, p. 684):
  `isEig_kronecker_iff`, `eigenvalues_kronecker`. The hard direction (every eigenvalue of
  `A ⊗ B` is such a product) is proved here by a simultaneous-eigenvector argument: `A ⊗ B` is
  the product of the commuting matrices `A ⊗ 1` and `1 ⊗ B`; the eigenspace of `A ⊗ B` is
  invariant under `A ⊗ 1`, which has an eigenvector in it (ℂ is algebraically closed); the
  common eigenspace is invariant under `1 ⊗ B`, which again has an eigenvector there;
* the eigenvalues of a block-diagonal matrix are those of its diagonal blocks (Woodford,
  p. 684): `isEig_fromBlocks_iff`.

Eigenvalues are complex: `IsEig M μ` says `μ : ℂ` has a nonzero eigenvector for the complex
matrix `M`, equivalently `det (μ I − M) = 0` (`isEig_iff_det`). Real matrices are handled
through `Matrix.map` with `Complex.ofReal` (`kronecker_map_ofReal`, `transpose_map_ofReal`).
-/

namespace Woodford.NeoWicksellianFramework.KroneckerSpectrum

open Matrix
open scoped _root_.Kronecker

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Woodford (2003), App. C.7, p. 684: `μ` is a (complex) eigenvalue of the square complex
matrix `M`: there is a nonzero `v` with `M v = μ v`. -/
def IsEig (M : Matrix m m ℂ) (μ : ℂ) : Prop := ∃ v : m → ℂ, v ≠ 0 ∧ M *ᵥ v = μ • v

/-- Woodford (2003), App. C.7, p. 684: `μ` is an eigenvalue of `M` iff it is a root of the
characteristic polynomial, `det (μ I − M) = 0`. -/
theorem isEig_iff_det [DecidableEq m] (M : Matrix m m ℂ) (μ : ℂ) :
    IsEig M μ ↔ (μ • (1 : Matrix m m ℂ) - M).det = 0 := by
  rw [← exists_mulVec_eq_zero_iff]
  unfold IsEig
  refine exists_congr fun v => and_congr_right fun _ => ?_
  rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero, eq_comm]

/-- Woodford (2003), App. C.7, p. 684: a matrix and its transpose have the same eigenvalues
(used for "the eigenvalues of `C` (and hence of `C′`)"). -/
theorem isEig_transpose_iff (M : Matrix m m ℂ) (μ : ℂ) : IsEig Mᵀ μ ↔ IsEig M μ := by
  classical
  rw [isEig_iff_det, isEig_iff_det, ← det_transpose (μ • (1 : Matrix m m ℂ) - M)]
  simp [transpose_sub, transpose_smul, transpose_one]

/-- Woodford (2003), (C.29), p. 684: `vec (B X C) = (C′ ⊗ B) vec X`, with `vec` the
column-stacking map (Mathlib's `Matrix.vec`). -/
theorem vec_mul_mul {R : Type*} [CommSemiring R] {p q : Type*} [Fintype p] [Fintype q]
    (B : Matrix p p R) (X : Matrix p q R) (C : Matrix q q R) :
    (Cᵀ ⊗ₖ B) *ᵥ vec X = vec (B * X * C) := by
  rw [kronecker_mulVec_vec, transpose_transpose]

/-- Woodford (2003), App. C.7, p. 684: the Kronecker product with an identity factor acts
column by column: `((A ⊗ 1) v)(i, j) = (A v(·, j))(i)`. -/
theorem kronecker_one_mulVec_apply [DecidableEq n]
    (A : Matrix m m ℂ) (v : m × n → ℂ) (i : m) (j : n) :
    ((A ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ v) (i, j) = (A *ᵥ fun k => v (k, j)) i := by
  simp only [mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type, one_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [ite_mul, mul_ite]

/-- Woodford (2003), App. C.7, p. 684: `((1 ⊗ B) v)(i, j) = (B v(i, ·))(j)`. -/
theorem one_kronecker_mulVec_apply [DecidableEq m]
    (B : Matrix n n ℂ) (v : m × n → ℂ) (i : m) (j : n) :
    (((1 : Matrix m m ℂ) ⊗ₖ B) *ᵥ v) (i, j) = (B *ᵥ fun l => v (i, l)) j := by
  simp only [mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type, one_apply]
  simp [ite_mul, Finset.sum_ite_eq]

/-- Woodford (2003), App. C.7, p. 684: the tensor product of eigenvectors is an eigenvector
of the Kronecker product, so every product `α β` of eigenvalues is an eigenvalue of `A ⊗ B`. -/
theorem isEig_kronecker_of {A : Matrix m m ℂ} {B : Matrix n n ℂ} {α β : ℂ}
    (hA : IsEig A α) (hB : IsEig B β) : IsEig (A ⊗ₖ B) (α * β) := by
  obtain ⟨x, hx0, hx⟩ := hA
  obtain ⟨y, hy0, hy⟩ := hB
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx0
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hy0
  refine ⟨fun p => x p.1 * y p.2, fun h => ?_, ?_⟩
  · have := congrFun h (i₀, j₀)
    simp only [Pi.zero_apply, mul_eq_zero] at this
    rcases this with h1 | h1
    · exact hi₀ h1
    · exact hj₀ h1
  · funext ⟨i, j⟩
    have hxi := congrFun hx i
    have hyj := congrFun hy j
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hxi hyj
    simp only [mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type, Pi.smul_apply,
      smul_eq_mul]
    calc ∑ k, ∑ l, A i k * B j l * (x k * y l)
        = (∑ k, A i k * x k) * ∑ l, B j l * y l := by
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          ring
      _ = α * β * (x i * y j) := by rw [hxi, hyj]; ring

/-- Woodford (2003), App. C.7, p. 684 (auxiliary): an endomorphism of a finite-dimensional
complex space has an eigenvector inside any nonzero invariant subspace. -/
theorem exists_eigenvector_mem {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : Module.End ℂ V) (W : Submodule ℂ V) (hW : W ≠ ⊥)
    (hf : ∀ x ∈ W, f x ∈ W) : ∃ v ∈ W, v ≠ 0 ∧ ∃ a : ℂ, f v = a • v := by
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue (f.restrict hf)
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha
  rw [Module.End.mem_eigenspace_iff] at hw
  refine ⟨w.1, w.2, fun h => hw0 (Subtype.ext h), a, ?_⟩
  have := congrArg Subtype.val hw
  simpa using this

/-- Woodford (2003), App. C.7, p. 684: **every eigenvalue of a Kronecker product is a product
of eigenvalues** of the factors. Proof by a simultaneous eigenvector of the commuting matrices
`A ⊗ 1` and `1 ⊗ B` inside the eigenspace of `A ⊗ B = (A ⊗ 1)(1 ⊗ B)`. -/
theorem exists_of_isEig_kronecker
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} {μ : ℂ}
    (h : IsEig (A ⊗ₖ B) μ) : ∃ α β, IsEig A α ∧ IsEig B β ∧ μ = α * β := by
  classical
  set P : Matrix (m × n) (m × n) ℂ := A ⊗ₖ (1 : Matrix n n ℂ) with hP
  set Q : Matrix (m × n) (m × n) ℂ := (1 : Matrix m m ℂ) ⊗ₖ B with hQ
  have hPQ : P * Q = A ⊗ₖ B := by rw [hP, hQ, ← mul_kronecker_mul, mul_one, one_mul]
  have hQP : Q * P = A ⊗ₖ B := by rw [hP, hQ, ← mul_kronecker_mul, mul_one, one_mul]
  have hKP : (A ⊗ₖ B) * P = P * (A ⊗ₖ B) := by
    rw [hP, ← mul_kronecker_mul, ← mul_kronecker_mul, mul_one, one_mul]
  have hKQ : (A ⊗ₖ B) * Q = Q * (A ⊗ₖ B) := by
    rw [hQ, ← mul_kronecker_mul, ← mul_kronecker_mul, mul_one, one_mul]
  set E : Submodule ℂ (m × n → ℂ) := Module.End.eigenspace (mulVecLin (A ⊗ₖ B)) μ with hE
  have memE : ∀ x, x ∈ E ↔ (A ⊗ₖ B) *ᵥ x = μ • x := fun x => by
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
    rw [mulVecLin_apply, mulVec_mulVec, hKP, ← mulVec_mulVec, hx, mulVec_smul]
  obtain ⟨v₁, hv₁E, hv₁0, a, ha⟩ := exists_eigenvector_mem (mulVecLin P) E hEne hPE
  set F : Submodule ℂ (m × n → ℂ) := E ⊓ Module.End.eigenspace (mulVecLin P) a with hF
  have memF : ∀ x, x ∈ F ↔ (A ⊗ₖ B) *ᵥ x = μ • x ∧ P *ᵥ x = a • x := fun x => by
    rw [hF, Submodule.mem_inf, memE, Module.End.mem_eigenspace_iff, mulVecLin_apply]
  have hFne : F ≠ ⊥ := by
    intro hbot
    have : v₁ ∈ F := (memF v₁).mpr ⟨(memE v₁).mp hv₁E, by rw [← mulVecLin_apply]; exact ha⟩
    rw [hbot, Submodule.mem_bot] at this
    exact hv₁0 this
  have hQF : ∀ x ∈ F, mulVecLin Q x ∈ F := by
    intro x hx
    rw [memF] at hx ⊢
    refine ⟨?_, ?_⟩
    · rw [mulVecLin_apply, mulVec_mulVec, hKQ, ← mulVec_mulVec, hx.1, mulVec_smul]
    · rw [mulVecLin_apply, mulVec_mulVec, hPQ, ← hQP, ← mulVec_mulVec, hx.2, mulVec_smul]
  obtain ⟨v₂, hv₂F, hv₂0, b, hb⟩ := exists_eigenvector_mem (mulVecLin Q) F hFne hQF
  rw [mulVecLin_apply] at hb
  obtain ⟨hK2, hP2⟩ := (memF v₂).mp hv₂F
  have hμ : μ = a * b := by
    have h1 : (A ⊗ₖ B) *ᵥ v₂ = (a * b) • v₂ := by
      rw [← hPQ, ← mulVec_mulVec, hb, mulVec_smul, hP2, smul_smul, mul_comm b a]
    rw [hK2] at h1
    have h2 : (μ - a * b) • v₂ = 0 := by rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hv₂0
  obtain ⟨⟨i₀, j₀⟩, hp⟩ := Function.ne_iff.mp hv₂0
  refine ⟨a, b, ⟨fun k => v₂ (k, j₀), fun h0 => hp (congrFun h0 i₀), ?_⟩,
    ⟨fun l => v₂ (i₀, l), fun h0 => hp (congrFun h0 j₀), ?_⟩, hμ⟩
  · funext i
    have := congrFun hP2 (i, j₀)
    rw [hP, kronecker_one_mulVec_apply] at this
    simpa using this
  · funext j
    have := congrFun hb (i₀, j)
    rw [hQ, one_kronecker_mulVec_apply] at this
    simpa using this

/-- Woodford (2003), App. C.7, p. 684: "the eigenvalues of the Kronecker product are the set of
products of the form `ρᵢ λⱼ`": `μ` is an eigenvalue of `A ⊗ B` iff `μ = α β` for eigenvalues
`α` of `A` and `β` of `B`. -/
theorem isEig_kronecker_iff
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (μ : ℂ) :
    IsEig (A ⊗ₖ B) μ ↔ ∃ α β, IsEig A α ∧ IsEig B β ∧ μ = α * β := by
  refine ⟨exists_of_isEig_kronecker, ?_⟩
  rintro ⟨α, β, hα, hβ, rfl⟩
  exact isEig_kronecker_of hα hβ

/-- Woodford (2003), App. C.7, p. 684: the spectrum of `A ⊗ B` as a set is the set of
pairwise products of the spectra of `A` and `B`. -/
theorem eigenvalues_kronecker
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    {μ | IsEig (A ⊗ₖ B) μ} = Set.image2 (· * ·) {α | IsEig A α} {β | IsEig B β} := by
  ext μ
  rw [Set.mem_ofPred_eq, isEig_kronecker_iff, Set.mem_image2]
  constructor
  · rintro ⟨α, β, hα, hβ, rfl⟩
    exact ⟨α, hα, β, hβ, rfl⟩
  · rintro ⟨α, hα, β, hβ, rfl⟩
    exact ⟨α, β, hα, hβ, rfl⟩

/-- Woodford (2003), App. C.7, pp. 684–685: if every eigenvalue of `A` and of `B` has modulus
less than one, so does every eigenvalue of `A ⊗ B` (`|ρᵢ λⱼ| < 1`). -/
theorem norm_lt_one_of_isEig_kronecker
    {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : ∀ α, IsEig A α → ‖α‖ < 1) (hB : ∀ β, IsEig B β → ‖β‖ < 1) {μ : ℂ}
    (h : IsEig (A ⊗ₖ B) μ) : ‖μ‖ < 1 := by
  obtain ⟨α, β, hα, hβ, rfl⟩ := exists_of_isEig_kronecker h
  rw [norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (hB β hβ).le).trans_lt (hA α hα)

/-- Woodford (2003), App. C.7, p. 684: "the eigenvalues of `DT` are the eigenvalues of the two
diagonal blocks": `μ` is an eigenvalue of `blockdiag(P, K)` iff it is one of `P` or of `K`. -/
theorem isEig_fromBlocks_iff (P : Matrix m m ℂ) (K : Matrix n n ℂ) (μ : ℂ) :
    IsEig (fromBlocks P 0 0 K) μ ↔ IsEig P μ ∨ IsEig K μ := by
  classical
  rw [isEig_iff_det, isEig_iff_det, isEig_iff_det, ← mul_eq_zero,
    ← det_fromBlocks_zero₂₁ _ 0]
  rw [← fromBlocks_one, fromBlocks_smul, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  simp [sub_eq_add_neg]

omit [Fintype m] [Fintype n] in
/-- Woodford (2003), App. C.7, p. 684: complexification commutes with the Kronecker product. -/
theorem kronecker_map_ofReal (A : Matrix m m ℝ) (B : Matrix n n ℝ) :
    (A ⊗ₖ B).map Complex.ofReal = A.map Complex.ofReal ⊗ₖ B.map Complex.ofReal := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [kroneckerMap_apply]

omit [Fintype m] in
/-- Woodford (2003), App. C.7, p. 684: complexification commutes with transposition. -/
theorem transpose_map_ofReal (A : Matrix m m ℝ) :
    Aᵀ.map Complex.ofReal = (A.map Complex.ofReal)ᵀ := by
  rw [transpose_map]

omit [Fintype m] [Fintype n] in
/-- Woodford (2003), App. C.7, p. 684: complexification commutes with forming a block-diagonal
matrix. -/
theorem fromBlocks_map_ofReal (P : Matrix m m ℝ) (K : Matrix n n ℝ) :
    (fromBlocks P 0 0 K).map Complex.ofReal =
      fromBlocks (P.map Complex.ofReal) 0 0 (K.map Complex.ofReal) := by
  rw [fromBlocks_map]
  simp

/-- Woodford (2003), App. C.7, p. 684: a real matrix none of whose complex eigenvalues equals
one has `I − M` invertible (nonzero determinant). Used for uniqueness of the fixed point of the
regression `T`-map. -/
theorem det_one_sub_ne_zero [DecidableEq m] (M : Matrix m m ℝ)
    (h : ¬ IsEig (M.map Complex.ofReal) 1) : (1 - M).det ≠ 0 := by
  intro h0
  apply h
  rw [isEig_iff_det, one_smul]
  have : ((1 - M).map Complex.ofReal).det = 0 := by
    rw [show (1 - M).map Complex.ofReal = Complex.ofRealHom.mapMatrix (1 - M) from rfl,
      ← RingHom.map_det, h0, map_zero]
  simpa [Matrix.map_sub, Matrix.map_one] using this

end Woodford.NeoWicksellianFramework.KroneckerSpectrum
