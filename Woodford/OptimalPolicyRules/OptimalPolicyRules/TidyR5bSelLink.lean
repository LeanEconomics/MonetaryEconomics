/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR5bCyclicSel
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# The column space of a deflating pair is a selected subspace

Woodford (2003), *Interest and Prices*, Chapter 8, Assumption 8.2 (p. 552), Appendix G.1
(pp. 716–718), (G.4), Propositions 8.1 and 8.2.

`TidyR5bCyclicSel.selSpace_conj_unique_iff` characterises uniqueness of the selected subspace
(`TidyR5bCyclicSel.SelSpace`). This module connects it to the book's objects: a real deflating
pair `A J = Î J Ψ` (a `PencilEigen.RealSelection`, the data of a `PencilSplit.DeflatingSplit`).

## The count data

A `RealSelection` records only which roots `Ψ` has. `CountData` adds how many times:
each selected root `μ` is a root of `det(μI − Ψ)` exactly `sel.count μ` times, the zero root
`n − rank A` times, and `ker A` lies in the column space of `J`.

## Results

* `selSpace_colSpan`: with the count data, the (complexified) column space of `J` is a
  conjugation-closed selected subspace; its blocks are its intersections with the generalised
  eigenspaces of `N = (A − sÎ)⁻¹Î`, whose dimensions are the multiplicities of the roots of `Ψ`
  (`finrank_colSpan_inf`).
* `exists_realSel_of_selSpace`, `countData_of_selSpace`: conversely every conjugation-closed
  selected subspace of the right dimension is the column space of a real deflating pair, and a
  pair whose column space is selected has the count data.
* `colSpan_eq_iff_mul`: two such `J` have the same column space iff `J' = J T` with `T`
  invertible.
* `Υ_unique_of_cyclic`, `exists_two_realSel`, `Υ_unique_iff` (**the criterion on the book's
  objects**): for a nonzero (1.15), a conjugation-closed selection, Assumption 8.4 and `Ẽ`
  invertible, `Υ` (eq. (1.21)) is the same for every real selection with the count data (every
  deflating split `PencilRepeated.splitGen` built from one) iff
  `TidyR5bCyclicSel.CyclicPartial` holds.
-/

namespace Woodford.OptimalPolicyRules.TidyR5bSelLink

open Matrix Polynomial GeneralSetup PencilSplit PencilEigen PencilAssumptions PencilRepeated
  GeneralFOC.Selection TidyR5bPartialSel TidyR5bCyclicSel

variable {ιZ ιz : Type*} [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ### Matrix powers and endomorphism powers -/

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), App. G.1 (tool): `((M − ν)ᵏ)` as an endomorphism is the matrix power. -/
theorem toLin'_sub_pow_apply (M : Matrix κ κ ℂ) (ν : ℂ) (k : ℕ) (x : κ → ℂ) :
    ((Matrix.toLin' M - ν • (1 : Module.End ℂ (κ → ℂ))) ^ k) x = ((M - ν • 1) ^ k) *ᵥ x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', ← mulVec_mulVec, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, Matrix.toLin'_apply, sub_mulVec, smul_mulVec,
      one_mulVec]

/-! ### The column space -/

/-- Woodford (2003), App. G.1, (G.4): the complexified column space of `J`. -/
noncomputable def colSpanC (J : Matrix (ιZ ⊕ ιz) κ ℝ) : Submodule ℂ (ιZ ⊕ ιz → ℂ) :=
  LinearMap.range (Matrix.toLin' (J.map Complex.ofReal))

variable (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) (J : Matrix (ιZ ⊕ ιz) κ ℝ)
  (Ψ : Matrix κ κ ℝ) in
/-- Woodford (2003), App. G.1 (the count data missing from a `RealSelection`): each selected
root `μ` is a root of `det(μI − Ψ)` exactly `sel.count μ` times, the zero root `n − rank A`
times, and `ker A` lies in the column space of `J`. -/
structure CountData : Prop where
  /-- Woodford (2003), Assumption 8.2: each selected root counted `sel.count μ` times. -/
  sel_count : ∀ μ ∈ sel, (Ψ.map Complex.ofReal).charpoly.rootMultiplicity μ = sel.count μ
  /-- Woodford (2003), Assumption 8.3: the zero root counted `n − rank A` times. -/
  zero_count : (Ψ.map Complex.ofReal).charpoly.rootMultiplicity 0 =
    Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank
  /-- Woodford (2003), Assumption 8.3: `ker A` lies in the column space of `J`. -/
  ker_le : ∀ v, S.Ahat *ᵥ v = 0 → ∃ w, J *ᵥ w = v

/-- Woodford (2003), App. G.1: with `A − sÎ` invertible and `s` not an eigenvalue of `Ψ`,
`N J = J (Ψ − s)⁻¹` (complexified). -/
theorem N_mul_J (S : LinearRESystem ιZ ιz) {s : ℝ} (hs : (S.Ahat - s • S.Ihat).det ≠ 0)
    {J : Matrix (ιZ ⊕ ιz) κ ℝ} {Ψ : Matrix κ κ ℝ} (hd : S.Ahat * J = S.Ihat * J * Ψ)
    (hP : IsUnit (Ψ.map Complex.ofReal - (s : ℂ) • 1).det) :
    (Nr S s).map Complex.ofReal * J.map Complex.ofReal =
      J.map Complex.ofReal * (Ψ.map Complex.ofReal - (s : ℂ) • 1)⁻¹ := by
  set M0 := S.Ahat.map Complex.ofReal - (s : ℂ) • S.Ihat.map Complex.ofReal with hM0
  set Nc := (Nr S s).map Complex.ofReal
  set Jc := J.map Complex.ofReal
  set P := Ψ.map Complex.ofReal - (s : ℂ) • 1
  have hM0u : IsUnit M0.det := isUnit_iff_ne_zero.mpr (det_shift_C S hs)
  have hdc : S.Ahat.map Complex.ofReal * Jc = S.Ihat.map Complex.ofReal * Jc *
      Ψ.map Complex.ofReal := by
    rw [← PencilAssumptions.map_ofReal_mul, ← PencilAssumptions.map_ofReal_mul,
      ← PencilAssumptions.map_ofReal_mul, hd]
  have h1 : M0 * Jc = S.Ihat.map Complex.ofReal * Jc * P := by
    rw [hM0, Matrix.sub_mul, hdc, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_one]
  have h2 : M0 * (Nc * Jc * P) = M0 * Jc := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, shift_mul_Nc S hs, h1]
  have h3 : Nc * Jc * P = Jc := by
    have := congrArg (M0⁻¹ * ·) h2
    simp only [← Matrix.mul_assoc, nonsing_inv_mul _ hM0u, Matrix.one_mul] at this
    exact this
  calc Nc * Jc = Nc * Jc * P * P⁻¹ := by
        rw [Matrix.mul_assoc _ P, mul_nonsing_inv _ hP, Matrix.mul_one]
    _ = Jc * P⁻¹ := by rw [h3]

/-- Woodford (2003), App. G.1: `s` is not an eigenvalue of `Ψ` (its eigenvalues are `0` or
selected roots, and `s ≠ 0` is not a root of (1.15)), so `Ψ − s` is invertible. -/
theorem P_isUnit (S : LinearRESystem ιZ ιz) {sel : Multiset ℂ} {s : ℝ} (hs0 : s ≠ 0)
    (hs : (S.Ahat - s • S.Ihat).det ≠ 0) (hsel : ∀ μ ∈ sel, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0)
    {Ψ : Matrix κ κ ℝ}
    (heig : ∀ μ : ℂ, (Matrix.scalar κ μ - Ψ.map Complex.ofReal).det = 0 → μ = 0 ∨ μ ∈ sel) :
    IsUnit (Ψ.map Complex.ofReal - (s : ℂ) • 1).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← mulVec_injective_iff_isUnit]
  intro a b hab
  by_contra hne
  have hv0 : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hv : (Ψ.map Complex.ofReal - (s : ℂ) • 1) *ᵥ (a - b) = 0 := by
    rw [mulVec_sub, hab, sub_self]
  have hdet : (Matrix.scalar κ (s : ℂ) - Ψ.map Complex.ofReal).det = 0 := by
    refine exists_mulVec_eq_zero_iff.mp ⟨a - b, hv0, ?_⟩
    have e : Matrix.scalar κ (s : ℂ) - Ψ.map Complex.ofReal =
        -(Ψ.map Complex.ofReal - (s : ℂ) • 1) := by
      rw [neg_sub, Matrix.scalar_apply, smul_one_eq_diagonal]
    rw [e, neg_mulVec, hv, neg_zero]
  rcases heig _ hdet with h | h
  · exact hs0 (by exact_mod_cast h)
  · exact sel_ne_shift S hs (hsel _ h).2 rfl

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] [DecidableEq κ] in
/-- Woodford (2003), App. G.1: independent real columns stay independent over `ℂ`, so `J`
(complexified) is injective. -/
theorem Jc_injective {J : Matrix (ιZ ⊕ ιz) κ ℝ} (hind : LinearIndependent ℝ Jᵀ) :
    Function.Injective (J.map Complex.ofReal).mulVec := by
  have hli : LinearIndependent ℂ (fun k i => (Jᵀ k i : ℂ)) := linearIndependent_ofReal hind
  intro a b hab
  have hsum : ∑ k, (a - b) k • (fun i => (Jᵀ k i : ℂ)) = 0 := by
    have h0 : (J.map Complex.ofReal) *ᵥ (a - b) = 0 := by rw [mulVec_sub, hab, sub_self]
    rw [← h0]
    funext i
    simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
  funext k
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli (a - b) hsum k)

/-- Woodford (2003), App. G.1: `(N − ν)ᵏ J = J (Φ − ν)ᵏ` when `N J = J Φ`. -/
theorem pow_intertwine (S : LinearRESystem ιZ ιz) (s : ℝ) {J : Matrix (ιZ ⊕ ιz) κ ℝ}
    {Φ : Matrix κ κ ℂ} (hNJ : (Nr S s).map Complex.ofReal * J.map Complex.ofReal =
      J.map Complex.ofReal * Φ) (ν : ℂ) (k : ℕ) (w : κ → ℂ) :
    ((φN S s - ν • (1 : Module.End ℂ (ιZ ⊕ ιz → ℂ))) ^ k) (J.map Complex.ofReal *ᵥ w) =
      J.map Complex.ofReal *ᵥ (((Matrix.toLin' Φ - ν • (1 : Module.End ℂ (κ → ℂ))) ^ k) w) := by
  rw [φN, toLin'_sub_pow_apply, toLin'_sub_pow_apply, mulVec_mulVec, mulVec_mulVec]
  congr 1
  have h1 : ((Nr S s).map Complex.ofReal - ν • 1) * J.map Complex.ofReal =
      J.map Complex.ofReal * (Φ - ν • 1) := by
    rw [Matrix.sub_mul, hNJ, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Matrix.mul_assoc, h1, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]

/-- Woodford (2003), App. G.1: the column space meets the generalised eigenspace of `N` at `ν`
in the image under `J` of the generalised eigenspace of `Φ` at `ν`. -/
theorem colSpan_inf_maxGen (S : LinearRESystem ιZ ιz) (s : ℝ) {J : Matrix (ιZ ⊕ ιz) κ ℝ}
    (hind : LinearIndependent ℝ Jᵀ) {Φ : Matrix κ κ ℂ}
    (hNJ : (Nr S s).map Complex.ofReal * J.map Complex.ofReal = J.map Complex.ofReal * Φ)
    (ν : ℂ) :
    colSpanC J ⊓ (φN S s).maxGenEigenspace ν =
      (Module.End.maxGenEigenspace (Matrix.toLin' Φ) ν).map
        (Matrix.toLin' (J.map Complex.ofReal)) := by
  ext v
  rw [Submodule.mem_inf, colSpanC, LinearMap.mem_range, Submodule.mem_map]
  constructor
  · rintro ⟨⟨w, rfl⟩, hv⟩
    refine ⟨w, ?_, rfl⟩
    rw [Module.End.mem_maxGenEigenspace] at hv ⊢
    obtain ⟨k, hk⟩ := hv
    refine ⟨k, Jc_injective hind ?_⟩
    rw [Matrix.toLin'_apply, pow_intertwine S s hNJ] at hk
    rw [hk, mulVec_zero]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨⟨w, rfl⟩, ?_⟩
    rw [Module.End.mem_maxGenEigenspace] at hw ⊢
    obtain ⟨k, hk⟩ := hw
    refine ⟨k, ?_⟩
    rw [Matrix.toLin'_apply, pow_intertwine S s hNJ, hk, mulVec_zero]

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), App. G.1: for `Φ = (Ψ − s)⁻¹` and `ν ≠ 0`, the generalised eigenspace of
`Φ` at `ν` is that of `Ψ` at `μ = s + ν⁻¹`. -/
theorem maxGen_inv_eq {Ψc : Matrix κ κ ℂ} {s : ℂ} (hP : IsUnit (Ψc - s • 1).det) {ν : ℂ}
    (hν : ν ≠ 0) :
    Module.End.maxGenEigenspace (Matrix.toLin' (Ψc - s • 1)⁻¹) ν =
      Module.End.maxGenEigenspace (Matrix.toLin' Ψc) (s + ν⁻¹) := by
  set P := Ψc - s • 1 with hPdef
  set Φ := P⁻¹
  have hΦP : Φ * P = 1 := nonsing_inv_mul _ hP
  have hPΦ : P * Φ = 1 := mul_nonsing_inv _ hP
  have hB : Ψc - (s + ν⁻¹) • (1 : Matrix κ κ ℂ) = P - ν⁻¹ • 1 := by
    rw [hPdef, add_smul]
    abel
  have hA : Φ - ν • (1 : Matrix κ κ ℂ) = ((-ν) • Φ) * (P - ν⁻¹ • 1) := by
    rw [Matrix.smul_mul, Matrix.mul_sub, hΦP, Matrix.mul_smul, Matrix.mul_one, smul_sub,
      smul_smul, show (-ν) * ν⁻¹ = -1 by field_simp]
    module
  have hA' : P - ν⁻¹ • (1 : Matrix κ κ ℂ) = ((-ν⁻¹) • P) * (Φ - ν • 1) := by
    rw [Matrix.smul_mul, Matrix.mul_sub, hPΦ, Matrix.mul_smul, Matrix.mul_one, smul_sub,
      smul_smul, show (-ν⁻¹) * ν = -1 by field_simp]
    module
  have hcP : Commute Φ P := hΦP.trans hPΦ.symm
  have c1 : Commute ((-ν) • Φ) (P - ν⁻¹ • 1) :=
    ((hcP.sub_right ((Commute.one_right Φ).smul_right _))).smul_left _
  have c2 : Commute ((-ν⁻¹) • P) (Φ - ν • 1) :=
    ((hcP.symm.sub_right ((Commute.one_right P).smul_right _))).smul_left _
  ext x
  rw [Module.End.mem_maxGenEigenspace, Module.End.mem_maxGenEigenspace]
  simp only [toLin'_sub_pow_apply]
  rw [hB]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hA', c2.mul_pow, ← mulVec_mulVec, hk, mulVec_zero]
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hA, c1.mul_pow, ← mulVec_mulVec, hk, mulVec_zero]

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), App. G.1: `Φ = (Ψ − s)⁻¹` is invertible, so it has no generalised
eigenvector for `0`. -/
theorem maxGen_inv_zero {Ψc : Matrix κ κ ℂ} {s : ℂ} (hP : IsUnit (Ψc - s • 1).det) :
    Module.End.maxGenEigenspace (Matrix.toLin' (Ψc - s • 1)⁻¹) 0 = ⊥ := by
  set P := Ψc - s • 1
  have hPΦ : P * P⁻¹ = 1 := mul_nonsing_inv _ hP
  have hc : Commute P P⁻¹ := hPΦ.trans (nonsing_inv_mul _ hP).symm
  rw [eq_bot_iff]
  intro x hx
  rw [Module.End.mem_maxGenEigenspace] at hx
  obtain ⟨k, hk⟩ := hx
  rw [toLin'_sub_pow_apply, zero_smul, sub_zero] at hk
  rw [Submodule.mem_bot]
  have h1 : (P ^ k * P⁻¹ ^ k) *ᵥ x = x := by rw [← hc.mul_pow, hPΦ, one_pow, one_mulVec]
  rw [← h1, ← mulVec_mulVec, hk, mulVec_zero]

/-- Woodford (2003), App. G.1 (**block dimensions**): for `ν ≠ 0`, the column space meets the
generalised eigenspace of `N` at `ν` in a subspace of dimension the multiplicity of
`μ = s + ν⁻¹` as a root of `det(μI − Ψ)`. -/
theorem finrank_colSpan_inf (S : LinearRESystem ιZ ιz) {s : ℝ}
    (hs : (S.Ahat - s • S.Ihat).det ≠ 0) {J : Matrix (ιZ ⊕ ιz) κ ℝ} {Ψ : Matrix κ κ ℝ}
    (hd : S.Ahat * J = S.Ihat * J * Ψ) (hind : LinearIndependent ℝ Jᵀ)
    (hP : IsUnit (Ψ.map Complex.ofReal - (s : ℂ) • 1).det) {ν : ℂ} (hν : ν ≠ 0) :
    Module.finrank ℂ (colSpanC J ⊓ (φN S s).maxGenEigenspace ν : Submodule ℂ _) =
      (Ψ.map Complex.ofReal).charpoly.rootMultiplicity ((s : ℂ) + ν⁻¹) := by
  rw [colSpan_inf_maxGen S s hind (N_mul_J S hs hd hP) ν,
    ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
      (fun a b h => Jc_injective hind h) _),
    maxGen_inv_eq hP hν, LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_toLin']

/-- Woodford (2003), App. G.1: the column space meets the generalised eigenspace of `N` at `0`
trivially. -/
theorem colSpan_inf_zero (S : LinearRESystem ιZ ιz) {s : ℝ}
    (hs : (S.Ahat - s • S.Ihat).det ≠ 0) {J : Matrix (ιZ ⊕ ιz) κ ℝ} {Ψ : Matrix κ κ ℝ}
    (hd : S.Ahat * J = S.Ihat * J * Ψ) (hind : LinearIndependent ℝ Jᵀ)
    (hP : IsUnit (Ψ.map Complex.ofReal - (s : ℂ) • 1).det) :
    colSpanC J ⊓ (φN S s).maxGenEigenspace 0 = ⊥ := by
  rw [colSpan_inf_maxGen S s hind (N_mul_J S hs hd hP) 0, maxGen_inv_zero hP,
    Submodule.map_bot]

/-- Woodford (2003), App. G.1: the column space is `N`-invariant (`N J = J Φ`). -/
theorem colSpan_inv (S : LinearRESystem ιZ ιz) (s : ℝ) {J : Matrix (ιZ ⊕ ιz) κ ℝ}
    {Φ : Matrix κ κ ℂ}
    (hNJ : (Nr S s).map Complex.ofReal * J.map Complex.ofReal = J.map Complex.ofReal * Φ) :
    ∀ w ∈ colSpanC J, φN S s w ∈ colSpanC J := by
  rintro _ ⟨z, rfl⟩
  refine ⟨Φ *ᵥ z, ?_⟩
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, φN, Matrix.toLin'_apply, mulVec_mulVec,
    mulVec_mulVec, hNJ]

/-- Woodford (2003), App. G.1 and Assumption 8.3: if `ker A` lies in the real column space of
`J`, the eigenspace of `ν₀` (the complexified `ker A`) lies in the complex column space. -/
theorem eigen_ν0_le (S : LinearRESystem ιZ ιz) {s : ℝ} (hs0 : s ≠ 0)
    (hs : (S.Ahat - s • S.Ihat).det ≠ 0) {J : Matrix (ιZ ⊕ ιz) κ ℝ}
    (hker : ∀ v, S.Ahat *ᵥ v = 0 → ∃ w, J *ᵥ w = v) :
    (φN S s).eigenspace (ν0 s) ≤ colSpanC J := by
  intro w hw
  rw [Module.End.mem_eigenspace_iff, φN, Matrix.toLin'_apply] at hw
  have hν0 : ν0 s = ((-s⁻¹ : ℝ) : ℂ) := ν0_eq s
  have hAw : S.Ahat.map Complex.ofReal *ᵥ w = 0 := by
    have h1 := congrArg (fun v => (S.Ahat.map Complex.ofReal -
      (s : ℂ) • S.Ihat.map Complex.ofReal) *ᵥ v) hw
    rw [mulVec_mulVec, shift_mul_Nc S hs, mulVec_smul, sub_mulVec, smul_mulVec, smul_sub,
      smul_smul, hν0] at h1
    have hs' : ((-s⁻¹ : ℝ) : ℂ) * (s : ℂ) = -1 := by
      rw [Complex.ofReal_neg, Complex.ofReal_inv, neg_mul,
        inv_mul_cancel₀ (by exact_mod_cast hs0)]
    rw [hs', neg_one_smul, sub_neg_eq_add] at h1
    have h2 : ((-s⁻¹ : ℝ) : ℂ) • (S.Ahat.map Complex.ofReal *ᵥ w) = 0 := by
      have := congrArg (· - S.Ihat.map Complex.ofReal *ᵥ w) h1
      simp only [sub_self, add_sub_cancel_right] at this
      exact this.symm
    have hne : ((-s⁻¹ : ℝ) : ℂ) ≠ 0 := by
      have : (-s⁻¹ : ℝ) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hs0)
      exact_mod_cast this
    exact (smul_eq_zero.mp h2).resolve_left hne
  have hre : S.Ahat *ᵥ (fun i => (w i).re) = 0 := by
    funext i
    have := congrArg Complex.re (congrFun hAw i)
    simpa [mulVec, dotProduct, Complex.re_sum] using this
  have him : S.Ahat *ᵥ (fun i => (w i).im) = 0 := by
    funext i
    have := congrArg Complex.im (congrFun hAw i)
    simpa [mulVec, dotProduct, Complex.im_sum] using this
  obtain ⟨a, ha⟩ := hker _ hre
  obtain ⟨b, hb⟩ := hker _ him
  refine ⟨fun k => (a k : ℂ) + Complex.I * b k, ?_⟩
  rw [Matrix.toLin'_apply]
  funext i
  have h1 := congrFun ha i
  have h2 := congrFun hb i
  simp only [mulVec, dotProduct] at h1 h2
  apply Complex.ext
  · simp [mulVec, dotProduct, Complex.re_sum, h1]
  · simp [mulVec, dotProduct, Complex.im_sum, h2]

/-- Woodford (2003), App. G.1: an `N`-invariant subspace is the sum of its intersections with
the generalised eigenspaces of `N`. -/
theorem eq_iSup_inf_maxGen (S : LinearRESystem ιZ ιz) (s : ℝ) {W : Submodule ℂ (ιZ ⊕ ιz → ℂ)}
    (hW : ∀ w ∈ W, φN S s w ∈ W) :
    W = ⨆ ν, W ⊓ (φN S s).maxGenEigenspace ν := by
  have h := Submodule.inf_iSup_genEigenspace (p := W) (f := φN S s) hW ⊤
  have htop := Module.End.iSup_maxGenEigenspace_eq_top (φN S s)
  rw [htop, inf_top_eq] at h
  exact h

/-- Woodford (2003), App. G.1, (G.4) and Assumption 8.3 (**the column space is a selected
subspace**): for a real deflating pair `A J = Î J Ψ` (independent columns, every eigenvalue of
`Ψ` zero or selected) with the count data, the complexified column space of `J` is a
conjugation-closed selected subspace (`TidyR5bCyclicSel.SelSpace`), with blocks
`colSpan ∩ Wfam ν`. -/
theorem selSpace_colSpan (S : LinearRESystem ιZ ιz) {sel : Multiset ℂ} {s : ℝ} (hs0 : s ≠ 0)
    (hs : (S.Ahat - s • S.Ihat).det ≠ 0) (hsel : ∀ μ ∈ sel, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0)
    {J : Matrix (ιZ ⊕ ιz) κ ℝ} {Ψ : Matrix κ κ ℝ} (hd : S.Ahat * J = S.Ihat * J * Ψ)
    (hind : LinearIndependent ℝ Jᵀ)
    (heig : ∀ μ : ℂ, (Matrix.scalar κ μ - Ψ.map Complex.ofReal).det = 0 → μ = 0 ∨ μ ∈ sel)
    (hcd : CountData S sel J Ψ) :
    SelSpace S sel s (colSpanC J) ∧ ConjStable (colSpanC J) := by
  have hP := P_isUnit S hs0 hs hsel heig
  have hNJ := N_mul_J S hs hd hP
  have hinv := colSpan_inv S s hNJ
  have hE := eigen_ν0_le S hs0 hs hcd.ker_le
  have hν0ne : ν0 s ≠ 0 := by
    rw [ν0_eq]
    have : (-s⁻¹ : ℝ) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hs0)
    exact_mod_cast this
  have hμ0 : (s : ℂ) + (ν0 s)⁻¹ = 0 := by
    rw [ν0, inv_inv]
    ring
  have h0blk : colSpanC J ⊓ (φN S s).maxGenEigenspace (ν0 s) =
      (φN S s).eigenspace (ν0 s) := by
    refine (Submodule.eq_of_le_of_finrank_le
      (le_inf hE Module.End.eigenspace_le_maxGenEigenspace) ?_).symm
    rw [finrank_colSpan_inf S hs hd hind hP hν0ne, hμ0, hcd.zero_count,
      finrank_eigenspace_ν0 S hs0 hs]
  set B : ℂ → Submodule ℂ (ιZ ⊕ ιz → ℂ) := fun ν => colSpanC J ⊓ Wfam S s ν with hB
  have hB0 : B (ν0 s) = Wfam S s (ν0 s) := by
    change colSpanC J ⊓ Wfam S s (ν0 s) = _
    rw [Wfam_ν0]
    exact inf_eq_right.mpr hE
  have hadm : AdmBlocks S sel s B := by
    refine ⟨hB0, fun ν hν h0 => ⟨inf_le_right, fun x hx => ?_, ?_⟩⟩
    · obtain ⟨hxW, hxF⟩ := Submodule.mem_inf.mp hx
      change φN S s x ∈ colSpanC J ⊓ Wfam S s ν
      rw [Wfam_ne S s h0] at hxF ⊢
      exact Submodule.mem_inf.mpr ⟨hinv x hxW, maxGen_mapsTo S s ν x hxF⟩
    · rw [Tset, Finset.mem_insert] at hν
      rcases hν with h | h
      · exact absurd h h0
      obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp h
      have hμs : μ - s ≠ 0 := sub_ne_zero.mpr (sel_ne_shift S hs (hsel μ
        (Multiset.mem_toFinset.mp hμ)).2)
      have hsμ : (s : ℂ) + ((μ - s)⁻¹)⁻¹ = μ := by rw [inv_inv]; ring
      change Module.finrank ℂ (colSpanC J ⊓ Wfam S s (μ - s)⁻¹ : Submodule ℂ _) = _
      rw [Wfam_ne S s h0, finrank_colSpan_inf S hs hd hind hP (inv_ne_zero hμs), hsμ,
        hcd.sel_count μ (Multiset.mem_toFinset.mp hμ), kc, hsμ]
  refine ⟨⟨B, hadm, le_antisymm ?_ (Finset.sup_le fun ν _ => inf_le_left)⟩, ?_⟩
  · rw [eq_iSup_inf_maxGen S s hinv]
    refine iSup_le fun ν => ?_
    by_cases hT : ν ∈ Tset sel s
    · by_cases h0 : ν = ν0 s
      · rw [h0, h0blk, ← Wfam_ν0, ← hB0]
        exact Finset.le_sup (f := B) (Finset.mem_insert_self _ _)
      · rw [← Wfam_ne S s h0]
        exact Finset.le_sup (f := B) hT
    · have hbot : colSpanC J ⊓ (φN S s).maxGenEigenspace ν = ⊥ := by
        by_cases hν : ν = 0
        · rw [hν]
          exact colSpan_inf_zero S hs hd hind hP
        · apply Submodule.finrank_eq_zero.mp
          rw [finrank_colSpan_inf S hs hd hind hP hν]
          refine Polynomial.rootMultiplicity_eq_zero fun hroot => ?_
          rw [Polynomial.IsRoot, Matrix.eval_charpoly] at hroot
          rcases heig _ hroot with h | h
          · apply hT
            have : ν = ν0 s := by
              rw [ν0]
              have h' : ν⁻¹ = -(s : ℂ) := by linear_combination h
              rw [← inv_inv ν, h']
              ring
            rw [this]
            exact Finset.mem_insert_self _ _
          · apply hT
            refine Finset.mem_insert_of_mem (Finset.mem_image.mpr
              ⟨_, Multiset.mem_toFinset.mpr h, ?_⟩)
            rw [add_sub_cancel_left, inv_inv]
      rw [hbot]
      exact bot_le
  · rintro _ ⟨z, rfl⟩
    refine ⟨fun k => starRingEnd ℂ (z k), ?_⟩
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, map_mulVec_conj]

/-! ### Column spaces and change of basis -/

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), App. G.1, p. 718 (tool): a change of basis `J T` does not enlarge the
column space. -/
theorem colSpan_mul_le (J : Matrix (ιZ ⊕ ιz) κ ℝ) (T : Matrix κ κ ℝ) :
    colSpanC (J * T) ≤ colSpanC J := by
  rintro _ ⟨z, rfl⟩
  refine ⟨T.map Complex.ofReal *ᵥ z, ?_⟩
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, mulVec_mulVec,
    PencilAssumptions.map_ofReal_mul]

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), App. G.1, p. 718 (**the column space determines `J` up to a change of
basis**): for `J`, `J'` with independent columns, the complexified column spaces agree iff
`J' = J T` with `T` invertible. -/
theorem colSpan_eq_iff_mul {J J' : Matrix (ιZ ⊕ ιz) κ ℝ} (hind' : LinearIndependent ℝ J'ᵀ) :
    colSpanC J = colSpanC J' ↔ ∃ T : Matrix κ κ ℝ, IsUnit T.det ∧ J' = J * T := by
  constructor
  · intro h
    have hcol : ∀ c, ∃ z : κ → ℂ, J.map Complex.ofReal *ᵥ z =
        fun i => (J' i c : ℂ) := fun c => by
      have hm : (fun i => (J' i c : ℂ)) ∈ colSpanC J := by
        rw [h]
        refine ⟨Pi.single c 1, ?_⟩
        rw [Matrix.toLin'_apply, mulVec_single_one]
        rfl
      obtain ⟨z, hz⟩ := hm
      exact ⟨z, hz⟩
    choose z hz using hcol
    set T : Matrix κ κ ℝ := Matrix.of fun k c => (z c k).re with hT
    have hJT : J' = J * T := by
      ext i c
      have := congrArg Complex.re (congrFun (hz c) i)
      simp only [mulVec, dotProduct, Matrix.map_apply, Complex.re_sum, Complex.re_ofReal_mul,
        Complex.ofReal_re] at this
      rw [Matrix.mul_apply, ← this]
      rfl
    refine ⟨T, ?_, hJT⟩
    rw [← Matrix.isUnit_iff_isUnit_det, ← mulVec_injective_iff_isUnit]
    intro a b hab
    have h0 : J' *ᵥ (a - b) = 0 := by rw [hJT, ← mulVec_mulVec, mulVec_sub, hab, sub_self,
      mulVec_zero]
    have hsum : ∑ k, (a - b) k • J'ᵀ k = 0 := by
      rw [← h0]
      funext i
      simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
    funext k
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hind' (a - b) hsum k)
  · rintro ⟨T, hT, rfl⟩
    refine le_antisymm ?_ (colSpan_mul_le J T)
    have : J = J * T * T⁻¹ := by rw [Matrix.mul_assoc, mul_nonsing_inv _ hT, Matrix.mul_one]
    conv_lhs => rw [this]
    exact colSpan_mul_le _ _

/-- Woodford (2003), eq. (1.21), App. G.1 and Proposition 8.1 (**cyclic ⇒ `Υ` unique on the
book's objects**): under `TidyR5bCyclicSel.CyclicPartial`, any two real selections with the
count data have the same column space, hence (`InertiaSplit.Υmat_mul`) the same `Υ`. -/
theorem Υ_unique_of_cyclic (S : LinearRESystem ιZ ιz) {sel : Multiset ℂ} {s : ℝ}
    (hs0 : s ≠ 0) (hs : (S.Ahat - s • S.Ihat).det ≠ 0)
    (hsel : ∀ μ ∈ sel, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0) (hcyc : CyclicPartial S sel s)
    (R R' : RealSelection S sel) (hR : CountData S sel R.J R.Ψ)
    (hR' : CountData S sel R'.J R'.Ψ) : Υmat S R.J = Υmat S R'.J := by
  have h1 := (selSpace_colSpan S hs0 hs hsel R.deflate R.indep R.eig hR).1
  have h2 := (selSpace_colSpan S hs0 hs hsel R'.deflate R'.indep R'.eig hR').1
  obtain ⟨T, hT, hJ⟩ := (colSpan_eq_iff_mul R'.indep).mp (selSpace_unique_of_cyclic S hcyc h1 h2)
  rw [hJ, InertiaSplit.Υmat_mul S R.J hT]

/-! ### From a selected subspace back to a real deflating pair -/

/-- Woodford (2003), App. G.1, (G.4): a selected subspace has dimension `(n − rank A) + #sel`
(the blocks sit in independent generalised eigenspaces). -/
theorem finrank_selSpace (S : LinearRESystem ιZ ιz) {sel : Multiset ℂ} {s : ℝ} (hs0 : s ≠ 0)
    (hs : (S.Ahat - s • S.Ihat).det ≠ 0) (hsel : ∀ μ ∈ sel, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0)
    {W : Submodule ℂ (ιZ ⊕ ιz → ℂ)} (hW : SelSpace S sel s W) :
    Module.finrank ℂ W = (Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank) + Multiset.card sel := by
  classical
  obtain ⟨B, hB, rfl⟩ := hW
  set B' : ℂ → Submodule ℂ (ιZ ⊕ ιz → ℂ) := fun ν => if ν ∈ Tset sel s then B ν else ⊥
    with hB'
  have hB'T : ∀ ν ∈ Tset sel s, B' ν = B ν := fun ν hν => by simp [hB', hν]
  have hsup : (Tset sel s).sup B = (Tset sel s).sup B' :=
    Finset.sup_congr rfl fun ν hν => (hB'T ν hν).symm
  have hle : ∀ ν, B' ν ≤ Wfam S s ν := fun ν => by
    by_cases hν : ν ∈ Tset sel s
    · simp only [hB', hν, ↓reduceIte]
      by_cases h0 : ν = ν0 s
      · rw [h0, hB.1]
      · exact (hB.2 ν hν h0).1
    · simp [hB', hν]
  have hind : iSupIndep B' := (Wfam_indep S s).mono hle
  have hnot : ν0 s ∉ sel.toFinset.image fun μ : ℂ => (μ - s)⁻¹ := by
    intro h
    obtain ⟨μ, hμ, he⟩ := Finset.mem_image.mp h
    exact inv_sub_ne_ν0 (hsel μ (Multiset.mem_toFinset.mp hμ)).1 he
  have hinj : Set.InjOn (fun μ : ℂ => (μ - s)⁻¹) (sel.toFinset : Set ℂ) :=
    fun a _ b _ h => sub_left_injective (inv_injective h)
  rw [hsup, finrank_finset_sup hind, Tset, Finset.sum_insert hnot, Finset.sum_image hinj]
  congr 1
  · rw [hB'T _ (Finset.mem_insert_self _ _), hB.1, Wfam_ν0]
    exact finrank_eigenspace_ν0 S hs0 hs
  · rw [← Multiset.toFinset_sum_count_eq]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hT : (μ - s)⁻¹ ∈ Tset sel s :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨μ, hμ, rfl⟩)
    rw [hB'T _ hT, (hB.2 _ hT (inv_sub_ne_ν0 (hsel μ (Multiset.mem_toFinset.mp hμ)).1)).2.2]
    simp [kc]

/-- Woodford (2003), App. G.1: a sum of admissible blocks meets the generalised eigenspace of
`N` at a used `ν` exactly in its block, and at an unused `ν` trivially. -/
theorem sup_inf_maxGen (S : LinearRESystem ιZ ιz) {T : Finset ℂ} {s : ℝ}
    {B : ℂ → Submodule ℂ (ιZ ⊕ ιz → ℂ)} (hB : ∀ μ ∈ T, B μ ≤ (φN S s).maxGenEigenspace μ)
    (ν : ℂ) : T.sup B ⊓ (φN S s).maxGenEigenspace ν = if ν ∈ T then B ν else ⊥ := by
  classical
  have hI := Module.End.independent_maxGenEigenspace (φN S s)
  have hR : ∀ T' : Finset ℂ, ν ∉ T' → (∀ μ ∈ T', B μ ≤ (φN S s).maxGenEigenspace μ) →
      T'.sup B ⊓ (φN S s).maxGenEigenspace ν = ⊥ := by
    intro T' hν hB'
    have h1 : T'.sup B ≤ ⨆ j, ⨆ (_ : j ≠ ν), (φN S s).maxGenEigenspace j :=
      Finset.sup_le fun μ hμ => (hB' μ hμ).trans
        (le_iSup₂_of_le μ (fun h => hν (h ▸ hμ)) le_rfl)
    exact disjoint_iff.mp (((hI ν).symm).mono_left h1)
  by_cases hν : ν ∈ T
  · rw [ite_eq_left hν, ← Finset.insert_erase hν, Finset.sup_insert,
      sup_inf_assoc_of_le _ (hB ν hν), hR _ (Finset.notMem_erase ν T)
        (fun μ hμ => hB μ (Finset.mem_of_mem_erase hμ)), sup_bot_eq]
  · rw [ite_eq_right hν]
    exact hR T hν hB

/-- Woodford (2003), App. G.1: a selected subspace is `N`-invariant and lies in
`PencilRepeated.Wsub`. -/
theorem selSpace_inv_le (S : LinearRESystem ιZ ιz) {sel : Multiset ℂ} {s : ℝ}
    {W : Submodule ℂ (ιZ ⊕ ιz → ℂ)} (hW : SelSpace S sel s W) :
    (∀ w ∈ W, φN S s w ∈ W) ∧ W ≤ Wsub S sel s := by
  obtain ⟨B, hB, rfl⟩ := hW
  have hBle : ∀ ν ∈ Tset sel s, B ν ≤ Wfam S s ν := fun ν hν => by
    by_cases h0 : ν = ν0 s
    · rw [h0, hB.1]
    · exact (hB.2 ν hν h0).1
  have hBinv : ∀ ν ∈ Tset sel s, ∀ w ∈ B ν, φN S s w ∈ B ν := fun ν hν w hw => by
    by_cases h0 : ν = ν0 s
    · subst h0
      rw [hB.1, Wfam_ν0] at hw ⊢
      rw [Module.End.mem_eigenspace_iff] at hw ⊢
      rw [hw, map_smul, hw]
    · exact (hB.2 ν hν h0).2.1 w hw
  refine ⟨fun w hw => ?_, Finset.sup_mono_fun hBle⟩
  have hle : (Tset sel s).sup B ≤ ((Tset sel s).sup B).comap (φN S s) :=
    Finset.sup_le fun ν hν v hv => by
      rw [Submodule.mem_comap]
      exact (Finset.le_sup (f := B) hν) (hBinv ν hν v hv)
  exact hle hw

/-- Woodford (2003), App. G.1, (G.4) and fn 2 (**every conjugation-closed selected subspace is
the column space of a real deflating pair**): with `#κ = (n − rank A) + #sel`, there are a real
`J` with independent columns and `Ψ` with `A J = Î J Ψ`, every eigenvalue of `Ψ` zero or
selected, and complexified column space `W`. -/
theorem exists_realSel_of_selSpace (S : LinearRESystem ιZ ιz) {sel : Multiset ℂ} {s : ℝ}
    (hs0 : s ≠ 0) (hs : (S.Ahat - s • S.Ihat).det ≠ 0)
    (hsel : ∀ μ ∈ sel, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0) {W : Submodule ℂ (ιZ ⊕ ιz → ℂ)}
    (hW : SelSpace S sel s W) (hWc : ConjStable W)
    (hcard : (Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank) + Multiset.card sel = Fintype.card κ) :
    ∃ (J : Matrix (ιZ ⊕ ιz) κ ℝ) (Ψ : Matrix κ κ ℝ), S.Ahat * J = S.Ihat * J * Ψ ∧
      LinearIndependent ℝ Jᵀ ∧
      (∀ μ : ℂ, (Matrix.scalar κ μ - Ψ.map Complex.ofReal).det = 0 → μ = 0 ∨ μ ∈ sel) ∧
      colSpanC J = W := by
  obtain ⟨hWinv, hWle⟩ := selSpace_inv_le S hW
  have hWdim := finrank_selSpace S hs0 hs hsel hW
  set U := realPart W with hU
  have hdim : Module.finrank ℝ U = Fintype.card κ := by
    rw [hU, finrank_realPart _ hWc, hWdim, hcard]
  have hUle : ∀ v ∈ U, v ∈ Ureal S sel s := fun v hv => hWle hv
  have hNU : ∀ v ∈ U, Nr S s *ᵥ v ∈ U := by
    intro v hv
    change (fun i => ((Nr S s *ᵥ v) i : ℂ)) ∈ W
    rw [← map_mulVec_ofReal]
    have := hWinv (fun i => (v i : ℂ)) hv
    rwa [φN, Matrix.toLin'_apply] at this
  let b := Module.finBasisOfFinrankEq ℝ U hdim
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let col : κ → ιZ ⊕ ιz → ℝ := fun c => (b (e c) : ιZ ⊕ ιz → ℝ)
  have hcolU : ∀ c, col c ∈ U := fun c => (b (e c)).2
  let T : U →ₗ[ℝ] U := (Nr S s).mulVecLin.restrict (fun v hv => hNU v hv)
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [Submodule.mem_bot]
    have h0 : Nr S s *ᵥ (x : ιZ ⊕ ιz → ℝ) = 0 := by
      have := congrArg Subtype.val hx
      exact this
    exact Subtype.ext (Nr_inj_Ureal S hs0 hs hsel (hUle _ x.2) h0)
  have hTsurj := LinearMap.injective_iff_surjective.mp hTinj
  choose pre hpre using fun c => hTsurj ⟨col c, hcolU c⟩
  let x : κ → U := fun c => pre c + s • ⟨col c, hcolU c⟩
  let Ψ : Matrix κ κ ℝ := Matrix.of fun c' c => b.repr (x c) (e c')
  have hsum : ∀ c, ∑ c', Ψ c' c • col c' = (x c : ιZ ⊕ ιz → ℝ) := by
    intro c
    have h1 := b.sum_repr (x c)
    have h2 : ∑ c', Ψ c' c • col c' = ∑ i, b.repr (x c) i • (b i : ιZ ⊕ ιz → ℝ) :=
      Equiv.sum_comp e (fun i => b.repr (x c) i • (b i : ιZ ⊕ ιz → ℝ))
    rw [h2]
    have := congrArg Subtype.val h1
    rw [Submodule.coe_sum] at this
    simpa using this
  have hcolA : ∀ c, S.Ahat *ᵥ col c = S.Ihat *ᵥ (x c : ιZ ⊕ ιz → ℝ) := by
    intro c
    have hp : Nr S s *ᵥ (pre c : ιZ ⊕ ιz → ℝ) = col c := by
      have := congrArg Subtype.val (hpre c)
      exact this
    have h1 : (S.Ahat - s • S.Ihat) *ᵥ col c = S.Ihat *ᵥ (pre c : ιZ ⊕ ιz → ℝ) := by
      rw [← hp, mulVec_mulVec, shift_mul_Nr S hs]
    rw [sub_mulVec, smul_mulVec] at h1
    change S.Ahat *ᵥ col c = S.Ihat *ᵥ ((pre c : ιZ ⊕ ιz → ℝ) + s • col c)
    rw [mulVec_add, mulVec_smul, ← h1]
    abel
  have hdefl : S.Ahat * Matrix.of (fun a c => col c a) =
      S.Ihat * Matrix.of (fun a c => col c a) * Ψ :=
    deflate_of_cols _ _ _ _ fun c => by rw [hsum c]; exact hcolA c
  have hind : LinearIndependent ℝ col :=
    (b.linearIndependent.comp e e.injective).map' U.subtype (Submodule.ker_subtype _)
  have hindT : LinearIndependent ℝ (Matrix.of fun a c => col c a)ᵀ := hind
  refine ⟨Matrix.of fun a c => col c a, Ψ, hdefl, hindT, fun μ hμ => ?_, ?_⟩
  · obtain ⟨z, hz0, hz⟩ := exists_eigvec hμ
    set Jc : Matrix (ιZ ⊕ ιz) κ ℂ := (Matrix.of fun a c => col c a).map Complex.ofReal with hJc
    set u := Jc *ᵥ z with hu
    have hcolC : LinearIndependent ℂ (fun c i => (col c i : ℂ)) := linearIndependent_ofReal hind
    have hJsum : u = ∑ c, z c • fun i => (col c i : ℂ) := by
      funext i
      simp [hu, hJc, mulVec, dotProduct, Finset.sum_apply, mul_comm]
    have hu0 : u ≠ 0 := by
      intro h0
      rw [hJsum] at h0
      exact hz0 (funext fun c => Fintype.linearIndependent_iff.mp hcolC z h0 c)
    have huW : u ∈ Wsub S sel s := by
      rw [hJsum]
      exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hUle _ (hcolU c))
    have hAu : S.Ahat.map Complex.ofReal *ᵥ u = μ • (S.Ihat.map Complex.ofReal *ᵥ u) := by
      have hdc : S.Ahat.map Complex.ofReal * Jc = S.Ihat.map Complex.ofReal * Jc *
          Ψ.map Complex.ofReal := by
        rw [hJc, ← PencilAssumptions.map_ofReal_mul, ← PencilAssumptions.map_ofReal_mul,
          ← PencilAssumptions.map_ofReal_mul, hdefl]
      rw [hu, mulVec_mulVec, hdc, ← mulVec_mulVec, hz, mulVec_smul, mulVec_mulVec]
    have hμs : μ ≠ s := by
      intro h
      apply det_shift_C S hs
      refine exists_mulVec_eq_zero_iff.mp ⟨u, hu0, ?_⟩
      rw [sub_mulVec, hAu, smul_mulVec, h, sub_self]
    have hN := eig_to_N S hs hμs hAu
    have hT := mem_Tset_of_eig S sel s hu0 huW (by rw [φN, Matrix.toLin'_apply]; exact hN)
    rw [Tset, Finset.mem_insert] at hT
    rcases hT with h | h
    · left
      have h' : μ - s = 0 - s := inv_injective h
      simpa using h'
    · right
      obtain ⟨μ', hμ', he⟩ := Finset.mem_image.mp h
      have : μ' = μ := sub_left_injective (inv_injective he)
      rw [← this]
      exact Multiset.mem_toFinset.mp hμ'
  · have hle : colSpanC (Matrix.of fun a c => col c a) ≤ W := by
      rintro _ ⟨z, rfl⟩
      have e : Matrix.toLin' ((Matrix.of fun a c => col c a).map Complex.ofReal) z =
          ∑ c, z c • fun i => (col c i : ℂ) := by
        funext i
        simp [Matrix.toLin'_apply, mulVec, dotProduct, Finset.sum_apply, mul_comm]
      rw [e]
      exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hcolU c)
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    rw [hWdim, hcard, colSpanC, LinearMap.finrank_range_of_inj
      (fun a b h => Jc_injective hindT h), Module.finrank_fintype_fun_eq_card]

/-- Woodford (2003), App. G.1 (**the count data of a selected column space**): if the column
space of a real deflating pair is a selected subspace, the pair has the count data. -/
theorem countData_of_selSpace (S : LinearRESystem ιZ ιz) {sel : Multiset ℂ} {s : ℝ}
    (hs0 : s ≠ 0) (hs : (S.Ahat - s • S.Ihat).det ≠ 0)
    (hsel : ∀ μ ∈ sel, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0) {J : Matrix (ιZ ⊕ ιz) κ ℝ}
    {Ψ : Matrix κ κ ℝ} (hd : S.Ahat * J = S.Ihat * J * Ψ) (hind : LinearIndependent ℝ Jᵀ)
    (heig : ∀ μ : ℂ, (Matrix.scalar κ μ - Ψ.map Complex.ofReal).det = 0 → μ = 0 ∨ μ ∈ sel)
    (hW : SelSpace S sel s (colSpanC J)) : CountData S sel J Ψ := by
  have hP := P_isUnit S hs0 hs hsel heig
  obtain ⟨B, hB, hWB⟩ := hW
  have hBle : ∀ ν ∈ Tset sel s, B ν ≤ (φN S s).maxGenEigenspace ν := fun ν hν => by
    refine le_trans ?_ (Wfam_le S s ν)
    by_cases h0 : ν = ν0 s
    · rw [h0, hB.1]
    · exact (hB.2 ν hν h0).1
  have hblk : ∀ ν ∈ Tset sel s, colSpanC J ⊓ (φN S s).maxGenEigenspace ν = B ν := by
    intro ν hν
    rw [hWB, sup_inf_maxGen S hBle ν, ite_eq_left hν]
  have hν0T : ν0 s ∈ Tset sel s := Finset.mem_insert_self _ _
  have hν0ne : ν0 s ≠ 0 := by
    rw [ν0_eq]
    have : (-s⁻¹ : ℝ) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hs0)
    exact_mod_cast this
  refine ⟨fun μ hμ => ?_, ?_, fun v hv => ?_⟩
  · have hμs : μ - s ≠ 0 := sub_ne_zero.mpr (sel_ne_shift S hs (hsel μ hμ).2)
    have hT : (μ - s)⁻¹ ∈ Tset sel s :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨μ, Multiset.mem_toFinset.mpr hμ, rfl⟩)
    have h := finrank_colSpan_inf S hs hd hind hP (inv_ne_zero hμs)
    rw [inv_inv, add_sub_cancel, hblk _ hT,
      (hB.2 _ hT (inv_sub_ne_ν0 (hsel μ hμ).1)).2.2] at h
    rw [← h]
    simp [kc]
  · have h := finrank_colSpan_inf S hs hd hind hP hν0ne
    rw [hblk _ hν0T, hB.1, Wfam_ν0, finrank_eigenspace_ν0 S hs0 hs] at h
    rw [h]
    congr 1
    rw [ν0, inv_inv]
    ring
  · have hvE : (fun i => (v i : ℂ)) ∈ (φN S s).eigenspace (ν0 s) := by
      rw [Module.End.mem_eigenspace_iff, φN, Matrix.toLin'_apply, map_mulVec_ofReal, ν0_eq]
      have hNv : Nr S s *ᵥ v = (-s⁻¹) • v := by
        have h1 : (S.Ahat - s • S.Ihat) *ᵥ ((-s⁻¹) • v) = S.Ihat *ᵥ v := by
          rw [mulVec_smul, sub_mulVec, hv, smul_mulVec, zero_sub, smul_neg, neg_smul, neg_neg,
            smul_smul, inv_mul_cancel₀ hs0, one_smul]
        have hu : IsUnit (S.Ahat - s • S.Ihat).det := isUnit_iff_ne_zero.mpr hs
        rw [Nr, ← mulVec_mulVec, ← h1, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
      rw [hNv]
      funext i
      simp
    have hmem : (fun i => (v i : ℂ)) ∈ colSpanC J := by
      have := (hblk _ hν0T).symm ▸ (show (fun i => (v i : ℂ)) ∈ B (ν0 s) by
        rw [hB.1, Wfam_ν0]; exact hvE)
      exact (Submodule.mem_inf.mp this).1
    obtain ⟨z, hz⟩ := hmem
    refine ⟨fun k => (z k).re, funext fun i => ?_⟩
    have := congrArg Complex.re (congrFun hz i)
    simpa [Matrix.toLin'_apply, mulVec, dotProduct, Complex.re_sum] using this

/-! ### The criterion on the book's objects -/

/-- Woodford (2003), App. G.1 (**not cyclic ⇒ two real selections**): if some partially
selected eigenvalue has two Jordan chains, there are two real selections with the count data and
different column spaces. -/
theorem exists_two_realSel (S : LinearRESystem ιZ ιz) {sel : Multiset ℂ} (hc : ConjClosed sel)
    {s : ℝ} (hs0 : s ≠ 0) (hs : (S.Ahat - s • S.Ihat).det ≠ 0)
    (hsel : ∀ μ ∈ sel, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0)
    (hcnt : ∀ μ ∈ sel, sel.count μ ≤ S.pencilPoly.roots.count μ)
    (hcard : (Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank) + Multiset.card sel = Fintype.card ιZ)
    (hnc : ¬ CyclicPartial S sel s) :
    ∃ R R' : RealSelection S sel, CountData S sel R.J R.Ψ ∧ CountData S sel R'.J R'.Ψ ∧
      colSpanC R.J ≠ colSpanC R'.J := by
  obtain ⟨W, W', h1, c1, h2, c2, hne⟩ := exists_two_of_not_cyclic S hc hs hsel hcnt hnc
  obtain ⟨J, Ψ, hd, hind, heig, hJ⟩ := exists_realSel_of_selSpace S hs0 hs hsel h1 c1 hcard
  obtain ⟨J', Ψ', hd', hind', heig', hJ'⟩ :=
    exists_realSel_of_selSpace S hs0 hs hsel h2 c2 hcard
  refine ⟨⟨J, Ψ, hd, hind, heig⟩, ⟨J', Ψ', hd', hind', heig'⟩,
    countData_of_selSpace S hs0 hs hsel hd hind heig (hJ ▸ h1),
    countData_of_selSpace S hs0 hs hsel hd' hind' heig' (hJ' ▸ h2), ?_⟩
  change colSpanC J ≠ colSpanC J'
  rw [hJ, hJ']
  exact hne

/-- Woodford (2003), eq. (1.21), App. G.1, Assumptions 8.2 and 8.4, Proposition 8.1 (**the
exact criterion on the book's objects**): for a nonzero (1.15), a conjugation-closed selection,
Assumption 8.4 and `Ẽ` invertible, `Υ` is the same for every real selection with the count data
(every deflating split `PencilRepeated.splitGen` built from one) **iff** every partially selected
eigenvalue has a single Jordan chain (`TidyR5bCyclicSel.CyclicPartial`). -/
theorem Υ_unique_iff {S : LinearRESystem ιZ ιz} {β : ℝ} (hβ : 0 < β) (h82 : Assumption82 S β)
    (hc : ConjClosed h82.sel) (hreg : S.pencilPoly ≠ 0) (h84 : Assumption84 S h82.sel)
    (hE : IsUnit S.Et.det) {s : ℝ} (hs0 : s ≠ 0) (hs : (S.Ahat - s • S.Ihat).det ≠ 0) :
    (∀ R R' : RealSelection S h82.sel, CountData S h82.sel R.J R.Ψ →
      CountData S h82.sel R'.J R'.Ψ → Υmat S R.J = Υmat S R'.J) ↔
      CyclicPartial S h82.sel s := by
  have hsel : ∀ μ ∈ h82.sel, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0 := by
    intro μ hμ
    have := Multiset.mem_of_le h82.sel_le hμ
    rw [Multiset.mem_filter, Polynomial.mem_roots hreg] at this
    exact ⟨this.2.1, this.1⟩
  have hcnt : ∀ μ ∈ h82.sel, h82.sel.count μ ≤ S.pencilPoly.roots.count μ := fun μ _ =>
    (Multiset.count_le_of_le μ h82.sel_le).trans (Multiset.count_le_of_le μ
      (Multiset.filter_le _ _))
  constructor
  · intro h
    by_contra hnc
    obtain ⟨R, R', hR, hR', hne⟩ := exists_two_realSel S hc hs0 hs hsel hcnt
      (by rw [add_comm]; exact h82.sel_card) hnc
    have h1 : IsUnit (J1 R.J).det := isUnit_iff_ne_zero.mpr (splitGen hβ h82 R hreg h84).J1_det
    have h1' : IsUnit (J1 R'.J).det :=
      isUnit_iff_ne_zero.mpr (splitGen hβ h82 R' hreg h84).J1_det
    obtain ⟨hT, hJ⟩ := mul_of_Υ_eq S hE h1 h1' (h R R' hR hR')
    exact hne ((colSpan_eq_iff_mul R'.indep).mpr ⟨_, hT, hJ⟩)
  · intro hcyc R R' hR hR'
    exact Υ_unique_of_cyclic S hs0 hs hsel hcyc R R' hR hR'

end Woodford.OptimalPolicyRules.TidyR5bSelLink
