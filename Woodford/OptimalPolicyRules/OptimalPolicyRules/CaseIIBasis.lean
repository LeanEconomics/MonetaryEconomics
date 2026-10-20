/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.Prop81CaseII
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# The corrected Assumption 8.4 (ii) does not depend on the basis

Woodford (2003), *Interest and Prices*, Chapter 8, Assumption 8.2 (ii) (p. 552), Assumption 8.4
(ii) and Appendix G.1 (pp. 716–718), Propositions 8.1 and 8.2.

In case (ii) of Assumption 8.2 the construction of `Prop81CaseII` uses a real basis `J⁺` of the
`(n_Z + 1)`-dimensional invariant subspace of the selection plus `conj μ`, a real `P` and the
residual root `h` (`CondII`). This module shows that the condition is a property of the subspace,
not of the basis:

* `cond_change`: `(J⁺, Ψ⁺, P, h) ↦ (J⁺T, T⁻¹Ψ⁺T, T⁻¹P, h)` preserves `CondII` for invertible `T`;
* `exists_T_of_span`, `Ψ_eq_of_basis`: every other basis of the same subspace (with its own `Ψ`) is
  of this form (`Î J⁺` is injective, `IJ_inj_cols`);
* `basis_invariance`: so if `CondII` holds for one basis it holds for every basis of the same
  subspace, with the same `h`.

Hence the corrected Assumption 8.4 (ii) is stated existentially (`Assumption84II`: some admissible
basis satisfies `CondII`), and Propositions 8.1 and 8.2 hold under it (`prop81_caseII`,
`prop82_caseII`). The universal form `Prop81CaseII.Assumption84IIall` implies it
(`ex_of_all`), and conversely it implies the universal form whenever all admissible bases span
the same subspace (`all_of_ex`). They do when the zero root of (1.15) is semisimple — the book's
convention that it counts `n − rank A` times (`ZeroSemisimple`): every column of an admissible
basis lies in the selected subspace (`col_mem_Wsub`), so all admissible bases span it
(`sameSubspace_of_semisimple`, `all_of_ex_semisimple`). They also do when the subspace is the
whole space (`sameSubspace_of_card`).
-/

namespace Woodford.OptimalPolicyRules.CaseIIBasis

open Matrix GeneralSetup GeneralFOC.LQ PencilSplit Prop81General PencilEigen PencilAssumptions
  PencilRepeated GeneralFOC.Selection Prop81CaseII

variable {Ω : Type*} {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]
variable {ιc : Type*} [Fintype ιc] [DecidableEq ιc]

/-! ### The condition and admissible bases -/

/-- Woodford (2003), Assumption 8.4 (ii), corrected for case (ii): with `J = J⁺P`, `J₁` and
`K = A₂₂' + A₁₂' Υ` are invertible and the residual root `h` on `ker P'` has `|βh| < 1`. -/
def CondII (S : LinearRESystem ιZ ιz) (β : ℝ) (Jp : Matrix (ιZ ⊕ ιz) ιc ℝ) (Ψp : Matrix ιc ιc ℝ)
    (P : Matrix ιc ιZ ℝ) (h : ℝ) : Prop :=
  (J1 (Jp * P)).det ≠ 0 ∧ (Kmat S (Jp * P)).det ≠ 0 ∧ |β * h| < 1 ∧
    ∀ v, Pᵀ *ᵥ v = 0 → (residProj Jp P * Ψpᵀ) *ᵥ v = h • v

/-- Woodford (2003), App. G.1, (G.4): `(J⁺, Ψ⁺)` is an admissible real basis of an invariant
subspace for the roots `sel'`: `A J⁺ = Î J⁺ Ψ⁺`, independent columns, and every eigenvalue of
`Ψ⁺` zero or in `sel'`. -/
def Admissible (S : LinearRESystem ιZ ιz) (sel' : Multiset ℂ) (Jp : Matrix (ιZ ⊕ ιz) ιc ℝ)
    (Ψp : Matrix ιc ιc ℝ) : Prop :=
  S.Ahat * Jp = S.Ihat * Jp * Ψp ∧ LinearIndependent ℝ Jpᵀ ∧
    ∀ ν : ℂ, (Matrix.scalar ιc ν - Ψp.map Complex.ofReal).det = 0 → ν = 0 ∨ ν ∈ sel'

/-- Woodford (2003), **Assumption 8.4 (ii), corrected for case (ii) of Assumption 8.2
(existential, normalisation-free)**: some admissible real basis `J⁺` (`n_Z + 1` columns) of an
invariant subspace of the selection plus `conj μ` has a real `P` and a residual root `h` with
`CondII`. By `basis_invariance` the choice of basis does not matter. -/
def Assumption84II (S : LinearRESystem ιZ ιz) (β : ℝ) (sel' : Multiset ℂ) : Prop :=
  ∃ (Jp : Matrix (ιZ ⊕ ιz) (Option ιZ) ℝ) (Ψp : Matrix (Option ιZ) (Option ιZ) ℝ),
    Admissible S sel' Jp Ψp ∧ ∃ (P : Matrix (Option ιZ) ιZ ℝ) (h : ℝ), CondII S β Jp Ψp P h

/-! ### Change of basis -/

omit [Fintype ιz] [DecidableEq ιz] in
/-- Woodford (2003), App. G.1: the residual projection transforms by conjugation,
`I − (J⁺T)₁'(J₁')⁻¹(T⁻¹P)' = T' (I − J⁺₁'(J₁')⁻¹P') T'⁻¹`. -/
theorem residProj_change {J : Matrix (ιZ ⊕ ιz) ιc ℝ} {P : Matrix ιc ιZ ℝ} {T : Matrix ιc ιc ℝ}
    (hT : IsUnit T.det) : residProj (J * T) (T⁻¹ * P) = Tᵀ * residProj J P * (T⁻¹)ᵀ := by
  have hJP : J * T * (T⁻¹ * P) = J * P := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc T, mul_nonsing_inv _ hT, Matrix.one_mul]
  have hTT : Tᵀ * (T⁻¹)ᵀ = 1 := by rw [← transpose_mul, nonsing_inv_mul _ hT, transpose_one]
  rw [residProj, residProj, hJP, J1_mul, transpose_mul, transpose_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_one, hTT]
  simp only [Matrix.mul_assoc]

/-- Woodford (2003), App. G.1: **`CondII` is invariant under a change of basis**
`(J⁺, Ψ⁺, P, h) ↦ (J⁺T, T⁻¹Ψ⁺T, T⁻¹P, h)` (`T` invertible), with the same residual root. -/
theorem cond_change {S : LinearRESystem ιZ ιz} {β : ℝ} {J : Matrix (ιZ ⊕ ιz) ιc ℝ}
    {Ψ : Matrix ιc ιc ℝ} {P : Matrix ιc ιZ ℝ} {h : ℝ} {T : Matrix ιc ιc ℝ} (hT : IsUnit T.det)
    (hc : CondII S β J Ψ P h) : CondII S β (J * T) (T⁻¹ * Ψ * T) (T⁻¹ * P) h := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  have hJP : J * T * (T⁻¹ * P) = J * P := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc T, mul_nonsing_inv _ hT, Matrix.one_mul]
  refine ⟨by rw [hJP]; exact h1, by rw [hJP]; exact h2, h3, fun v hv => ?_⟩
  have hTT : Tᵀ * (T⁻¹)ᵀ = 1 := by rw [← transpose_mul, nonsing_inv_mul _ hT, transpose_one]
  have hTT' : (T⁻¹)ᵀ * Tᵀ = 1 := by rw [← transpose_mul, mul_nonsing_inv _ hT, transpose_one]
  have hw : Pᵀ *ᵥ ((T⁻¹)ᵀ *ᵥ v) = 0 := by
    rw [mulVec_mulVec, ← transpose_mul]
    exact hv
  have e : Tᵀ * residProj J P * (T⁻¹)ᵀ * (T⁻¹ * Ψ * T)ᵀ =
      Tᵀ * (residProj J P * Ψᵀ) * (T⁻¹)ᵀ := by
    rw [transpose_mul, transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (T⁻¹)ᵀ Tᵀ, hTT', Matrix.one_mul]
  rw [residProj_change hT, e, ← mulVec_mulVec, ← mulVec_mulVec, h4 _ hw, mulVec_smul,
    mulVec_mulVec, hTT, one_mulVec]

/-- Woodford (2003), (G.4): `A J⁺ = Î J⁺ Ψ⁺` gives `A (J⁺T) = Î (J⁺T)(T⁻¹Ψ⁺T)`. -/
theorem deflate_change {S : LinearRESystem ιZ ιz} {J : Matrix (ιZ ⊕ ιz) ιc ℝ}
    {Ψ T : Matrix ιc ιc ℝ} (hT : IsUnit T.det) (hd : S.Ahat * J = S.Ihat * J * Ψ) :
    S.Ahat * (J * T) = S.Ihat * (J * T) * (T⁻¹ * Ψ * T) := by
  rw [← Matrix.mul_assoc, hd]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc T T⁻¹, mul_nonsing_inv _ hT, Matrix.one_mul]

/-- Woodford (2003), App. G.1: two bases with independent columns spanning the same subspace
differ by an invertible `T`: `J' = J T`. -/
theorem exists_T_of_span {n : Type*} {J J' : Matrix n ιc ℝ} (hJ' : LinearIndependent ℝ J'ᵀ)
    (hspan : ∀ c, J'ᵀ c ∈ Submodule.span ℝ (Set.range Jᵀ)) :
    ∃ T : Matrix ιc ιc ℝ, IsUnit T.det ∧ J' = J * T := by
  classical
  choose g hg using fun c => (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hspan c)
  set T : Matrix ιc ιc ℝ := Matrix.of fun c' c => g c c' with hTdef
  have heq : J' = J * T := by
    ext a c
    have := congrFun (hg c) a
    simp only [Finset.sum_apply, Pi.smul_apply, transpose_apply, smul_eq_mul] at this
    rw [← this, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun c' _ => by rw [hTdef, of_apply, mul_comm]
  refine ⟨T, ?_, heq⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨z, hz0, hz⟩ := exists_mulVec_eq_zero_iff.mpr h0
  apply hz0
  exact eq_zero_of_indep hJ' (by rw [heq, ← mulVec_mulVec, hz, mulVec_zero])

/-- Woodford (2003), App. G.1: for an admissible basis, `Î J⁺` is injective (a real `s ≠ 0` that
is not a root makes `A − sÎ` and `Ψ⁺ − s` invertible). -/
theorem IJ_inj_cols {S : LinearRESystem ιZ ιz} {sel' : Multiset ℂ} {Jp : Matrix (ιZ ⊕ ιz) ιc ℝ}
    {Ψp : Matrix ιc ιc ℝ} (hA : Admissible S sel' Jp Ψp)
    (hsel : ∀ μ ∈ sel', S.pencilPoly.eval μ = 0) (hreg : S.pencilPoly ≠ 0) {v : ιc → ℝ}
    (hv : (S.Ihat * Jp) *ᵥ v = 0) : v = 0 := by
  obtain ⟨hd, hind, heig⟩ := hA
  obtain ⟨s, hs0, hs⟩ := PencilEigen.Construction.exists_shift hreg
  have hAs : (S.Ahat - s • S.Ihat).det ≠ 0 := by
    intro h
    apply hs
    rw [pencilPoly_eval, det_pencil_ofReal, h, Complex.ofReal_zero]
  set N' := Ψp - s • (1 : Matrix ιc ιc ℝ) with hN'
  have hN : N'.det ≠ 0 := by
    intro h
    have hc : (Matrix.scalar ιc (s : ℂ) - Ψp.map Complex.ofReal).det = 0 := by
      have e1 : Matrix.scalar ιc (s : ℂ) - Ψp.map Complex.ofReal = -(N'.map Complex.ofReal) := by
        ext i j
        by_cases hij : i = j
        · subst hij
          simp [hN', Matrix.scalar_apply]
        · simp [hN', Matrix.scalar_apply, hij, Matrix.one_apply_ne hij]
      have e2 := Complex.ofRealHom.map_det N'
      rw [RingHom.mapMatrix_apply] at e2
      change (N'.det : ℂ) = (N'.map Complex.ofReal).det at e2
      rw [e1, det_neg, ← e2, h, Complex.ofReal_zero, mul_zero]
    rcases heig _ hc with h0 | hm
    · exact hs0 (Complex.ofReal_eq_zero.mp h0)
    · exact hs (hsel _ hm)
  have hkey : (S.Ahat - s • S.Ihat) * Jp = S.Ihat * Jp * N' := by
    rw [Matrix.sub_mul, hd, hN', Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_one]
  have hIJ : S.Ihat * Jp = (S.Ahat - s • S.Ihat) * Jp * N'⁻¹ := by
    rw [hkey, Matrix.mul_assoc, mul_nonsing_inv _ (Ne.isUnit hN), Matrix.mul_one]
  rw [hIJ, ← mulVec_mulVec, ← mulVec_mulVec] at hv
  have h1 := eq_zero_of_mulVec_eq_zero hAs hv
  have h2 := eq_zero_of_indep hind h1
  calc v = N' *ᵥ (N'⁻¹ *ᵥ v) := by
        rw [mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit hN), one_mulVec]
    _ = 0 := by rw [h2, mulVec_zero]

/-- Woodford (2003), App. G.1: on a basis `J' = J T` of the same subspace, `Ψ'` is forced to be
`T⁻¹ Ψ T` (because `Î J'` is injective). -/
theorem Ψ_eq_of_basis {S : LinearRESystem ιZ ιz} {J J' : Matrix (ιZ ⊕ ιz) ιc ℝ}
    {Ψ Ψ' T : Matrix ιc ιc ℝ} (hT : IsUnit T.det) (hJ' : J' = J * T)
    (hd : S.Ahat * J = S.Ihat * J * Ψ) (hd' : S.Ahat * J' = S.Ihat * J' * Ψ')
    (hinj : ∀ v, (S.Ihat * J') *ᵥ v = 0 → v = 0) : Ψ' = T⁻¹ * Ψ * T := by
  have hD : S.Ihat * J' * (Ψ' - T⁻¹ * Ψ * T) = 0 := by
    rw [Matrix.mul_sub, ← hd', hJ', ← Matrix.mul_assoc, hd]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc T T⁻¹, mul_nonsing_inv _ hT, Matrix.one_mul, sub_self]
  ext i j
  have hcol := hinj (fun k => (Ψ' - T⁻¹ * Ψ * T) k j) (by
    funext a
    exact congrFun (congrFun hD a) j)
  have := congrFun hcol i
  rw [Matrix.sub_apply] at this
  exact sub_eq_zero.mp this

/-- Woodford (2003), App. G.1: if `CondII` holds for one basis `J` it holds, with the same
residual root `h`, for every basis `J'` (with its `Ψ'`) of the same subspace, provided `Î J'` is
injective. -/
theorem cond_of_sameSpan {S : LinearRESystem ιZ ιz} {β : ℝ} {J J' : Matrix (ιZ ⊕ ιz) ιc ℝ}
    {Ψ Ψ' : Matrix ιc ιc ℝ} {P : Matrix ιc ιZ ℝ} {h : ℝ} (hc : CondII S β J Ψ P h)
    (hd : S.Ahat * J = S.Ihat * J * Ψ) (hd' : S.Ahat * J' = S.Ihat * J' * Ψ')
    (hJ' : LinearIndependent ℝ J'ᵀ) (hspan : ∀ c, J'ᵀ c ∈ Submodule.span ℝ (Set.range Jᵀ))
    (hinj : ∀ v, (S.Ihat * J') *ᵥ v = 0 → v = 0) : ∃ P', CondII S β J' Ψ' P' h := by
  obtain ⟨T, hT, hJT⟩ := exists_T_of_span hJ' hspan
  have hΨ := Ψ_eq_of_basis hT hJT hd hd' hinj
  refine ⟨T⁻¹ * P, ?_⟩
  rw [hJT, hΨ]
  exact cond_change hT hc

/-- Woodford (2003), Assumption 8.4 (ii) corrected, App. G.1: **basis invariance** — for two
admissible bases of the same subspace (roots of a nonzero (1.15)), `CondII` for one gives
`CondII` for the other with the same residual root. -/
theorem basis_invariance {S : LinearRESystem ιZ ιz} {β : ℝ} {sel' : Multiset ℂ}
    (hreg : S.pencilPoly ≠ 0) (hsel : ∀ μ ∈ sel', S.pencilPoly.eval μ = 0)
    {J J' : Matrix (ιZ ⊕ ιz) ιc ℝ} {Ψ Ψ' : Matrix ιc ιc ℝ} (hA : Admissible S sel' J Ψ)
    (hA' : Admissible S sel' J' Ψ') (hspan : ∀ c, J'ᵀ c ∈ Submodule.span ℝ (Set.range Jᵀ))
    {P : Matrix ιc ιZ ℝ} {h : ℝ} (hc : CondII S β J Ψ P h) : ∃ P', CondII S β J' Ψ' P' h :=
  cond_of_sameSpan hc hA.1 hA'.1 hA'.2.1 hspan fun _ hv => IJ_inj_cols hA' hsel hreg hv

/-! ### The existential and universal forms -/

/-- Woodford (2003), App. G.1: all admissible bases (for `sel'`, `n_Z + 1` columns) span the same
subspace. -/
def SameSubspace (S : LinearRESystem ιZ ιz) (sel' : Multiset ℂ) : Prop :=
  ∀ (J J' : Matrix (ιZ ⊕ ιz) (Option ιZ) ℝ) (Ψ Ψ' : Matrix (Option ιZ) (Option ιZ) ℝ),
    Admissible S sel' J Ψ → Admissible S sel' J' Ψ' →
      ∀ c, J'ᵀ c ∈ Submodule.span ℝ (Set.range Jᵀ)

/-- Woodford (2003), App. G.1: when `n_Z + 1 = n`, every admissible basis spans the whole space,
so all admissible bases span the same subspace. -/
theorem sameSubspace_of_card {S : LinearRESystem ιZ ιz} {sel' : Multiset ℂ}
    (hcard : Fintype.card (Option ιZ) = Fintype.card (ιZ ⊕ ιz)) : SameSubspace S sel' := by
  intro J J' Ψ Ψ' hA _ c
  rw [hA.2.1.span_eq_top_of_card_eq_finrank' (by
    rw [Module.finrank_fintype_fun_eq_card]
    exact hcard)]
  exact Submodule.mem_top

/-- Woodford (2003), Assumption 8.4 (ii) corrected: the existential form implies the universal
form `Prop81CaseII.Assumption84IIall` when all admissible bases span the same subspace. -/
theorem all_of_ex {S : LinearRESystem ιZ ιz} {β : ℝ} {sel' : Multiset ℂ}
    (hreg : S.pencilPoly ≠ 0) (hsel : ∀ μ ∈ sel', S.pencilPoly.eval μ = 0)
    (hsame : SameSubspace S sel') (h84 : Assumption84II S β sel') :
    Assumption84IIall S β sel' := by
  obtain ⟨J, Ψ, hA, P, h, hc⟩ := h84
  intro J' Ψ' hd' hind' heig'
  have hA' : Admissible S sel' J' Ψ' := ⟨hd', hind', heig'⟩
  obtain ⟨P', hc'⟩ := basis_invariance hreg hsel hA hA' (hsame J J' Ψ Ψ' hA hA') hc
  exact ⟨P', h, hc'⟩

/-- Woodford (2003), Assumption 8.4 (ii) corrected: the universal form implies the existential
form, since an admissible basis exists (`PencilRepeated.exists_deflating_cols`; Assumption 8.2
(ii) with whole root classes and a nonzero (1.15)). -/
theorem ex_of_all {S : LinearRESystem ιZ ιz} {β : ℝ} (h82 : Assumption82 S β) {μ : ℂ}
    (hμ : μ ∈ h82.sel) (hc : ConjClosed (h82.sel.erase μ)) (hreg : S.pencilPoly ≠ 0)
    (hw : SelWhole S (selPlus h82.sel μ)) (hall : Assumption84IIall S β (selPlus h82.sel μ)) :
    Assumption84II S β (selPlus h82.sel μ) := by
  have hsel : ∀ ν ∈ h82.sel, ν ≠ 0 ∧ S.pencilPoly.eval ν = 0 := by
    intro ν hν
    have := Multiset.mem_of_le h82.sel_le hν
    rw [Multiset.mem_filter, Polynomial.mem_roots hreg] at this
    exact ⟨this.2.1, this.1⟩
  have hsel' : ∀ ν ∈ selPlus h82.sel μ, ν ≠ 0 ∧ S.pencilPoly.eval ν = 0 := by
    intro ν hν
    rw [selPlus, Multiset.mem_cons] at hν
    rcases hν with rfl | hν
    · obtain ⟨h0, hr⟩ := hsel μ hμ
      exact ⟨by rwa [ne_eq, map_eq_zero], pencil_eval_conj S hr⟩
    · exact hsel ν hν
  obtain ⟨Jp, Ψp, hd, hind, heig⟩ := exists_deflating_cols S (κ := Option ιZ)
    (conjClosed_selPlus hμ hc) hsel' hreg hw (by
      rw [selPlus, Multiset.card_cons, Fintype.card_option]
      have := h82.sel_card
      omega)
  obtain ⟨P, h, hJ1, hK, hh, hres⟩ := hall Jp Ψp hd hind heig
  exact ⟨Jp, Ψp, ⟨hd, hind, heig⟩, P, h, hJ1, hK, hh, hres⟩

/-! ### Propositions 8.1 and 8.2 under the existential form -/

/-- Woodford (2003), App. G.1: Assumption 8.2 and the existential Assumption 8.4 (ii) give a
quasi-split (`Prop81CaseII.QuasiSplit`). -/
theorem nonempty_quasiSplit_ex {S : LinearRESystem ιZ ιz} {β : ℝ} (hβ : 0 < β)
    (h82 : Assumption82 S β) {μ : ℂ} (hμ : μ ∈ h82.sel)
    (h84 : Assumption84II S β (selPlus h82.sel μ)) : Nonempty (QuasiSplit S β (Option ιZ)) := by
  have hnorm : ∀ ν ∈ selPlus h82.sel μ, ‖ν‖ < β⁻¹ := by
    intro ν hν
    rw [selPlus, Multiset.mem_cons] at hν
    rcases hν with rfl | hν
    · have := Multiset.mem_of_le h82.sel_le hμ
      rw [Multiset.mem_filter] at this
      rw [Complex.norm_conj]
      exact this.2.2
    · have := Multiset.mem_of_le h82.sel_le hν
      rw [Multiset.mem_filter] at this
      exact this.2.2
  obtain ⟨Jp, Ψp, ⟨hd, -, heig⟩, P, h, hJ1, hK, hh, hres⟩ := h84
  refine ⟨⟨Jp, Ψp, hd, fun ν hν => ?_, P, hJ1, hK, h • 1,
    fun v hv => by rw [hres v hv, smul_mulVec, one_mulVec],
    by rw [smul_smul]; exact powDecay_smul_one hh⟩⟩
  rcases heig ν hν with h0 | hm
  · rw [h0, norm_zero]
    exact inv_pos.mpr hβ
  · exact hnorm ν hm

/-- Woodford (2003), App. G.1: the quasi-split chosen from Assumption 8.2 (ii) and the
existential Assumption 8.4 (ii). -/
noncomputable def quasiSplitOfEx (P : LQProblem ιZ ιz ιτ) (h82 : Assumption82 P.sys P.β) {μ : ℂ}
    (hμ : μ ∈ h82.sel) (h84 : Assumption84II P.sys P.β (selPlus h82.sel μ)) :
    QuasiSplit P.sys P.β (Option ιZ) :=
  (nonempty_quasiSplit_ex P.β_pos h82 hμ h84).some

/-- Woodford (2003), **Proposition 8.1**, p. 553, **in case (ii) of Assumption 8.2**, under the
existential (basis-free, normalisation-free) Assumption 8.4 (ii): the corrected Proposition 8.1
holds for any expectation system. -/
theorem prop81_caseII (P : LQProblem ιZ ιz ιτ) (h82 : Assumption82 P.sys P.β) {μ : ℂ}
    (hμ : μ ∈ h82.sel) (h84 : Assumption84II P.sys P.β (selPlus h82.sel μ))
    (𝔼 : ExpectationSystem Ω) (t0 : ℕ) : Nonempty (Prop81ConclusionM P 𝔼 t0) :=
  ⟨prop81II P (quasiSplitOfEx P h82 hμ h84) 𝔼 t0⟩

/-- Woodford (2003), **Proposition 8.2**, p. 555, **in case (ii) of Assumption 8.2**, under
Assumptions 8.1, 8.2 (ii), the existential 8.4 (ii) and 8.5: commitment to (1.23) is robustly
optimal. -/
theorem prop82_caseII {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (hpull : 𝔼.PullOut) (hA : Prop82General.Assumption81M P 𝔼 t0)
    (h82 : Assumption82 P.sys P.β) {μ : ℂ} (hμ : μ ∈ h82.sel)
    (h84 : Assumption84II P.sys P.β (selPlus h82.sel μ))
    (h85 : Assumption85 (Λmat P.sys P.β ((quasiSplitOfEx P h82 hμ h84).Jp *
      (quasiSplitOfEx P h82 hμ h84).P)) P.sys.B2)
    {D : ℕ} (hD : D + 1 ≤ t0) (hDk : P.sys.Et.rank ≤ D) {Mh qh : ℕ → Ω → ιz → ℝ}
    {vh : ℕ → Ω → ℝ}
    (hhist : TargetCriterion.Prop82.HistoryOK (Λmat P.sys P.β
      ((quasiSplitOfEx P h82 hμ h84).Jp * (quasiSplitOfEx P h82 hμ h84).P))
      P.sys.B2 t0 D Mh qh vh)
    (hMhb : BoundedV Mh) (hMhk : AdaptedV 𝔼 Mh) (hqhb : BoundedV qh)
    (hvhb : ∃ K, ∀ t ω, |vh t ω| ≤ K) :
    RobustlyOptimal (κ := ιz) P 𝔼 t0
      (fun _ y => Prop82General.Prop82M.CriterionM
        (prop81II P (quasiSplitOfEx P h82 hμ h84) 𝔼 t0) D qh vh y)
      (fun _ y t ω => zpart (y t ω)) :=
  prop82_of_quasiSplit hpull hA _ h85.2 hD hDk hhist hMhb hMhk hqhb hvhb


/-! ### All admissible bases span the same subspace (zero root semisimple) -/

/-- Woodford (2003), p. 547 (the convention that the zero root of (1.15) counts `n − rank A`
times): the zero root has multiplicity exactly `n − rank A`, i.e. it is semisimple. -/
def ZeroSemisimple (S : LinearRESystem ιZ ιz) : Prop :=
  S.pencilPoly.roots.count 0 = Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank

/-- Woodford (2003), App. G.1: with a semisimple zero root the generalised eigenspace of
`ν₀ = −1/s` is the eigenspace (`ker A`). -/
theorem maxGen_ν0_eq (S : LinearRESystem ιZ ιz) {s : ℝ} (hs0 : s ≠ 0)
    (hs : (S.Ahat - s • S.Ihat).det ≠ 0) (hz : ZeroSemisimple S) :
    (φN S s).maxGenEigenspace (ν0 s) = (φN S s).eigenspace (ν0 s) := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq (Module.End.eigenspace_le_maxGenEigenspace) ?_
  rw [finrank_eigenspace_ν0 S hs0 hs, LinearMap.finrank_maxGenEigenspace_eq, φN,
    Matrix.charpoly_toLin', ← Polynomial.count_roots, ν0,
    ← count_pencil_roots S hs (μ := 0) (by exact_mod_cast hs0.symm)]
  exact hz.symm

/-- Woodford (2003), App. G.1: a real matrix injective on real vectors is injective on complex
vectors. -/
theorem injC_of_injR {m n : Type*} [Fintype n] {M : Matrix m n ℝ}
    (h : ∀ v, M *ᵥ v = 0 → v = 0) (z : n → ℂ) (hz : M.map Complex.ofReal *ᵥ z = 0) : z = 0 := by
  have hre := h _ (funext fun i => by rw [← re_mulVec_map, hz]; rfl)
  have him := h _ (funext fun i => by rw [← im_mulVec_map, hz]; rfl)
  funext k
  exact Complex.ext (congrFun hre k) (congrFun him k)

/-- Woodford (2003), App. G.1: **every column of an admissible basis lies in the selected
subspace `W`** (with a semisimple zero root): the span `V` of the columns is `N`-invariant, every
eigenvalue of `N` on `V` is `ν₀` or `(μ − s)⁻¹` with `μ` selected, and `V` is the sum of the
generalised eigenspaces of `N` on `V`. -/
theorem col_mem_Wsub {S : LinearRESystem ιZ ιz} {sel' : Multiset ℂ} {s : ℝ} (hs0 : s ≠ 0)
    (hs : (S.Ahat - s • S.Ihat).det ≠ 0) (hsel : ∀ μ ∈ sel', μ ≠ 0 ∧ S.pencilPoly.eval μ = 0)
    (hreg : S.pencilPoly ≠ 0) (hz : ZeroSemisimple S) {J : Matrix (ιZ ⊕ ιz) ιc ℝ}
    {Ψ : Matrix ιc ιc ℝ} (hA : Admissible S sel' J Ψ) (c : ιc) :
    (fun i => (J i c : ℂ)) ∈ Wsub S sel' s := by
  have hinjR : ∀ v, (S.Ihat * J) *ᵥ v = 0 → v = 0 :=
    fun _ hv => IJ_inj_cols hA (fun μ h => (hsel μ h).2) hreg hv
  obtain ⟨hd, hind, heig⟩ := hA
  set col : ιc → (ιZ ⊕ ιz → ℂ) := fun c i => (J i c : ℂ) with hcol
  set Jc : Matrix (ιZ ⊕ ιz) ιc ℂ := J.map Complex.ofReal with hJc
  have hcolJ : ∀ z : ιc → ℂ, ∑ c, z c • col c = Jc *ᵥ z := by
    intro z
    funext i
    simp [hcol, hJc, mulVec, dotProduct, Finset.sum_apply, mul_comm]
  -- `Ψ − s` is invertible
  set N' := Ψ - s • (1 : Matrix ιc ιc ℝ) with hN'
  have hN : N'.det ≠ 0 := by
    intro h
    have hc : (Matrix.scalar ιc (s : ℂ) - Ψ.map Complex.ofReal).det = 0 := by
      have e1 : Matrix.scalar ιc (s : ℂ) - Ψ.map Complex.ofReal = -(N'.map Complex.ofReal) := by
        ext i j
        by_cases hij : i = j
        · subst hij
          simp [hN', Matrix.scalar_apply]
        · simp [hN', Matrix.scalar_apply, hij, Matrix.one_apply_ne hij]
      have e2 := Complex.ofRealHom.map_det N'
      rw [RingHom.mapMatrix_apply] at e2
      change (N'.det : ℂ) = (N'.map Complex.ofReal).det at e2
      rw [e1, det_neg, ← e2, h, Complex.ofReal_zero, mul_zero]
    rcases heig _ hc with h0 | hm
    · exact hs0 (Complex.ofReal_eq_zero.mp h0)
    · apply hs
      have := (hsel _ hm).2
      rw [pencilPoly_eval, det_pencil_ofReal] at this
      exact_mod_cast this
  -- `N J = J (Ψ − s)⁻¹`
  have hkey : (S.Ahat - s • S.Ihat) * J = S.Ihat * J * N' := by
    rw [Matrix.sub_mul, hd, hN', Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_one]
  have hNJ : Nr S s * J = J * N'⁻¹ := by
    have hIJ : S.Ihat * J = (S.Ahat - s • S.Ihat) * J * N'⁻¹ := by
      rw [hkey, Matrix.mul_assoc, mul_nonsing_inv _ (Ne.isUnit hN), Matrix.mul_one]
    rw [Nr, Matrix.mul_assoc, hIJ, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      nonsing_inv_mul _ (Ne.isUnit hs), Matrix.one_mul]
  -- the complex span of the columns is `N`-invariant
  set V : Submodule ℂ (ιZ ⊕ ιz → ℂ) := Submodule.span ℂ (Set.range col) with hV
  have hgen : ∀ c, φN S s (col c) ∈ V := by
    intro c
    have e : φN S s (col c) = ∑ c', ((N'⁻¹ c' c : ℝ) : ℂ) • col c' := by
      rw [φN, Matrix.toLin'_apply, hcol, map_mulVec_ofReal]
      funext i
      have := congrFun (congrFun hNJ i) c
      simp only [Matrix.mul_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      change ((∑ b, Nr S s i b * J b c : ℝ) : ℂ) = _
      rw [this]
      push_cast
      exact Finset.sum_congr rfl fun c' _ => mul_comm _ _
    rw [e]
    exact Submodule.sum_mem _ fun c' _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c', rfl⟩)
  have hVinv : ∀ x ∈ V, φN S s x ∈ V := by
    have hle : V ≤ V.comap (φN S s) := by
      rw [hV, Submodule.span_le]
      rintro _ ⟨c, rfl⟩
      exact hgen c
    exact fun x hx => hle hx
  -- every eigenvalue of `N` on `V` lies in `Tset`
  have hTs : ∀ x ∈ V, x ≠ 0 → ∀ lam : ℂ, φN S s x = lam • x → lam ∈ Tset sel' s := by
    intro x hxV hx0 lam hx
    obtain ⟨z, hzx⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hxV
    rw [hcolJ] at hzx
    subst hzx
    have hIc : S.Ihat.map Complex.ofReal * Jc = (S.Ihat * J).map Complex.ofReal := by
      rw [hJc, map_ofReal_mul]
    have hlam0 : lam ≠ 0 := by
      rintro rfl
      apply hx0
      have h1 : (Nr S s).map Complex.ofReal *ᵥ (Jc *ᵥ z) = 0 := by
        rw [← Matrix.toLin'_apply, ← φN, hx, zero_smul]
      have h2 : S.Ihat.map Complex.ofReal *ᵥ (Jc *ᵥ z) = 0 := by
        have := congrArg (· *ᵥ (Jc *ᵥ z)) (shift_mul_Nc S hs)
        rw [← this, ← mulVec_mulVec, h1, mulVec_zero]
      rw [mulVec_mulVec, hIc] at h2
      rw [injC_of_injR hinjR z h2, mulVec_zero]
    have hNx : (Nr S s).map Complex.ofReal *ᵥ (Jc *ᵥ z) = lam • (Jc *ᵥ z) := by
      rw [← Matrix.toLin'_apply, ← φN, hx]
    have hAx := N_to_eig S hs hlam0 hNx
    have hdc : S.Ahat.map Complex.ofReal * Jc =
        S.Ihat.map Complex.ofReal * Jc * Ψ.map Complex.ofReal := by
      rw [hJc, ← map_ofReal_mul, ← map_ofReal_mul, ← map_ofReal_mul, hd]
    have hΨz : Ψ.map Complex.ofReal *ᵥ z = ((s : ℂ) + lam⁻¹) • z := by
      have h3 : (S.Ihat.map Complex.ofReal * Jc) *ᵥ
          (Ψ.map Complex.ofReal *ᵥ z - ((s : ℂ) + lam⁻¹) • z) = 0 := by
        rw [mulVec_sub, mulVec_mulVec, ← hdc, ← mulVec_mulVec, hAx, mulVec_smul, mulVec_mulVec,
          sub_self]
      rw [hIc] at h3
      exact sub_eq_zero.mp (injC_of_injR hinjR _ h3)
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hx0 (mulVec_zero _)
    have hdet : (Matrix.scalar ιc ((s : ℂ) + lam⁻¹) - Ψ.map Complex.ofReal).det = 0 := by
      refine exists_mulVec_eq_zero_iff.mp ⟨z, hz0, ?_⟩
      rw [sub_mulVec, hΨz]
      funext i
      simp [Matrix.scalar_apply]
    rw [Tset, Finset.mem_insert]
    rcases heig _ hdet with h0 | hm
    · left
      rw [ν0]
      have : lam⁻¹ = -(s : ℂ) := by linear_combination h0
      rw [zero_sub, ← this, inv_inv]
    · right
      refine Finset.mem_image.mpr ⟨_, Multiset.mem_toFinset.mpr hm, ?_⟩
      simp
  -- `V` is the sum of the generalised eigenspaces of `N` on `V`
  set T : Module.End ℂ V := (φN S s).restrict hVinv with hT
  have hle : ∀ lam : ℂ, T.maxGenEigenspace lam ≤ (Wsub S sel' s).comap V.subtype := by
    intro lam
    by_cases hl : lam ∈ Tset sel' s
    · change (Module.End.genEigenspace ((φN S s).restrict hVinv) lam) ⊤ ≤ _
      rw [Module.End.genEigenspace_restrict]
      refine Submodule.comap_mono ?_
      have hW : (φN S s).maxGenEigenspace lam = Wfam S s lam := by
        by_cases h : lam = ν0 s
        · rw [h, Wfam_ν0, maxGen_ν0_eq S hs0 hs hz]
        · rw [Wfam_ne S s h]
      change (φN S s).maxGenEigenspace lam ≤ _
      rw [hW]
      exact Finset.le_sup (f := Wfam S s) hl
    · have hbot : T.maxGenEigenspace lam = ⊥ := by
        by_contra hne
        have hev : T.HasEigenvalue lam :=
          (Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one (by simp)).mp hne
        obtain ⟨x, hx⟩ := hev.exists_hasEigenvector
        have hxe := Module.End.mem_eigenspace_iff.mp hx.1
        have hx0 : (x : ιZ ⊕ ιz → ℂ) ≠ 0 := fun h => hx.2 (Subtype.ext h)
        exact hl (hTs x x.2 hx0 lam (congrArg Subtype.val hxe))
      rw [hbot]
      exact bot_le
  have htop := Module.End.iSup_maxGenEigenspace_eq_top T
  have hmem : (⟨col c, Submodule.subset_span ⟨c, rfl⟩⟩ : V) ∈ ⨆ lam, T.maxGenEigenspace lam := by
    rw [htop]
    exact Submodule.mem_top
  exact (iSup_le hle) hmem

/-- Woodford (2003), App. G.1: **with a semisimple zero root, every admissible basis spans the
same subspace** (the real selected subspace `Ureal`), for a conjugation-closed selection of
nonzero roots taken in whole classes, `#κ = (n − rank A) + #sel'` columns and a nonzero (1.15). -/
theorem sameSubspace_of_semisimple {S : LinearRESystem ιZ ιz} {sel' : Multiset ℂ}
    (hi : ConjClosed sel') (hsel : ∀ μ ∈ sel', μ ≠ 0 ∧ S.pencilPoly.eval μ = 0)
    (hreg : S.pencilPoly ≠ 0) (hw : SelWhole S sel') (hz : ZeroSemisimple S)
    (hcard : (Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank) + Multiset.card sel' =
      Fintype.card (Option ιZ)) : SameSubspace S sel' := by
  obtain ⟨s, hs0, hsev⟩ := PencilEigen.Construction.exists_shift hreg
  have hs : (S.Ahat - s • S.Ihat).det ≠ 0 := by
    intro h
    apply hsev
    rw [pencilPoly_eval, det_pencil_ofReal, h, Complex.ofReal_zero]
  have hsub : ∀ (J : Matrix (ιZ ⊕ ιz) (Option ιZ) ℝ) (Ψ : Matrix (Option ιZ) (Option ιZ) ℝ),
      Admissible S sel' J Ψ → Submodule.span ℝ (Set.range Jᵀ) ≤ Ureal S sel' s := by
    intro J Ψ hA
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact col_mem_Wsub hs0 hs hsel hreg hz hA c
  have hdimU : Module.finrank ℝ (Ureal S sel' s) = Fintype.card (Option ιZ) := by
    rw [Ureal, finrank_realPart _ (Wsub_conj S hi (fun μ hμ => (hsel μ hμ).1) s),
      finrank_Wsub S hs0 hs hsel hw, hcard]
  have heq : ∀ (J : Matrix (ιZ ⊕ ιz) (Option ιZ) ℝ) (Ψ : Matrix (Option ιZ) (Option ιZ) ℝ),
      Admissible S sel' J Ψ → Submodule.span ℝ (Set.range Jᵀ) = Ureal S sel' s := by
    intro J Ψ hA
    refine Submodule.eq_of_le_of_finrank_eq (hsub J Ψ hA) ?_
    rw [finrank_span_eq_card hA.2.1, hdimU]
  intro J J' Ψ Ψ' hA hA' c
  rw [heq J Ψ hA, ← heq J' Ψ' hA']
  exact Submodule.subset_span ⟨c, rfl⟩

/-- Woodford (2003), **Assumption 8.4 (ii), corrected: the universal form is a theorem** — under
Assumption 8.2 (ii) with whole root classes, a nonzero (1.15) and a semisimple zero root (the
book's counting convention), the existential form `Assumption84II` implies
`Prop81CaseII.Assumption84IIall` (and conversely, `ex_of_all`). -/
theorem all_of_ex_semisimple {S : LinearRESystem ιZ ιz} {β : ℝ} (h82 : Assumption82 S β) {μ : ℂ}
    (hμ : μ ∈ h82.sel) (hc : ConjClosed (h82.sel.erase μ)) (hreg : S.pencilPoly ≠ 0)
    (hw : SelWhole S (selPlus h82.sel μ)) (hz : ZeroSemisimple S)
    (h84 : Assumption84II S β (selPlus h82.sel μ)) :
    Assumption84IIall S β (selPlus h82.sel μ) := by
  have hsel : ∀ ν ∈ h82.sel, ν ≠ 0 ∧ S.pencilPoly.eval ν = 0 := by
    intro ν hν
    have := Multiset.mem_of_le h82.sel_le hν
    rw [Multiset.mem_filter, Polynomial.mem_roots hreg] at this
    exact ⟨this.2.1, this.1⟩
  have hsel' : ∀ ν ∈ selPlus h82.sel μ, ν ≠ 0 ∧ S.pencilPoly.eval ν = 0 := by
    intro ν hν
    rw [selPlus, Multiset.mem_cons] at hν
    rcases hν with rfl | hν
    · obtain ⟨h0, hr⟩ := hsel μ hμ
      exact ⟨by rwa [ne_eq, map_eq_zero], pencil_eval_conj S hr⟩
    · exact hsel ν hν
  refine all_of_ex hreg (fun ν hν => (hsel' ν hν).2)
    (sameSubspace_of_semisimple (conjClosed_selPlus hμ hc) hsel' hreg hw hz ?_) h84
  rw [selPlus, Multiset.card_cons, Fintype.card_option]
  have := h82.sel_card
  omega

end Woodford.OptimalPolicyRules.CaseIIBasis
