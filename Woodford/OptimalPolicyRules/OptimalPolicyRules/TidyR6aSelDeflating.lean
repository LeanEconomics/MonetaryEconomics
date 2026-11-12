/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR5bSelLink
import OptimalPolicyRules.CaseIIBasis

/-!
# Every deflating split carries its own selection and count data

Woodford (2003), *Interest and Prices*, Chapter 8, Assumption 8.2 (p. 552), Appendix G.1
(pp. 716–718), (G.4), (1.20)–(1.21) (p. 553) and Proposition 8.1.

`TidyR5bSelLink.Υ_unique_iff` takes the per-root count data `TidyR5bSelLink.CountData` as a
hypothesis and is stated for `PencilEigen.RealSelection`s. Here the count data is derived from a
bare `PencilSplit.DeflatingSplit`, exactly where it can be, and the criterion is extended to all
deflating splits.

## The selection of a split

A deflating split `A J = Î J Ψ` selects the nonzero eigenvalues of `Ψ`, with multiplicity:
`selOf Ψ` (conjugation-closed, `selOf_conjClosed`; each element a nonzero root of (1.15) with
`|μ| < β⁻¹`, `mem_selOf_split`). `toRealSel` turns every deflating split into a real selection
for `selOf Ψ`, with the same `J` and `Ψ`; `sel_eq_selOf`: a selection with count data is
necessarily `selOf Ψ`.

## The count data

* `ker_le_colSpan` (**new**): for every deflating split, `ker A` lies in the column space of
  `J`. The invertibility of `K = A₂₂' + A₁₂'Υ` forces it: for `v ∈ ker A`,
  `K'(v_z − J₂J₁⁻¹v_Z) = 0` (`Kt_mulVec_ker`).
* `countData_iff`: the count data for `selOf Ψ` holds **iff** the zero eigenvalue of `Ψ` has
  multiplicity exactly `n − rank A`.
* `countData_of_semisimple`: if the zero root of (1.15) is semisimple
  (`CaseIIBasis.ZeroSemisimple`) and (1.15) is nonzero, **every** deflating split has the count
  data.
* `chainSys`, `chainSplit`, `chain_not_countData` (**counterexample**): with a non-semisimple zero
  root a deflating split can use a Jordan chain of the zero root (`Ψ = [[0, 1], [0, 0]]`, while
  `n − rank A = 1`); then the count data fails for **every** selection. So `CountData` cannot be
  derived from a bare deflating split in general, and these are exactly the splits that lack it
  (`countData_iff`).

## The criterion for all deflating splits

`Υ_unique_iff_split`: under the hypotheses of `TidyR5bSelLink.Υ_unique_iff`, `Υ` (eq. (1.21)) is
the same for every deflating split that selects `h82.sel` and has the count data iff
`TidyR5bCyclicSel.CyclicPartial` holds; `Υ_unique_iff_split_semisimple` drops the count data when
the zero root is semisimple.
-/

namespace Woodford.OptimalPolicyRules.TidyR6aSelDeflating

open Matrix Polynomial GeneralSetup PencilSplit PencilEigen PencilAssumptions PencilRepeated
  GeneralFOC.Selection TidyR5bPartialSel TidyR5bCyclicSel TidyR5bSelLink CaseIIBasis

variable {ιZ ιz : Type*} [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz]

/-! ### The selection of a deflating split -/

/-- Woodford (2003), App. G.1, (G.4): the roots selected by `Ψ`, the nonzero eigenvalues of `Ψ`
counted with algebraic multiplicity. -/
noncomputable def selOf (Ψ : Matrix ιZ ιZ ℝ) : Multiset ℂ :=
  (Ψ.map Complex.ofReal).charpoly.roots.filter (fun μ => μ ≠ 0)

omit [Fintype ιz] [DecidableEq ιz] in
/-- Woodford (2003), App. G.1: `μ` is selected iff it is a nonzero eigenvalue of `Ψ`. -/
theorem mem_selOf {Ψ : Matrix ιZ ιZ ℝ} {μ : ℂ} :
    μ ∈ selOf Ψ ↔ μ ≠ 0 ∧ (Matrix.scalar ιZ μ - Ψ.map Complex.ofReal).det = 0 := by
  rw [selOf, Multiset.mem_filter, mem_roots (charpoly_monic _).ne_zero, IsRoot.def,
    eval_charpoly, and_comm]

omit [Fintype ιz] [DecidableEq ιz] in
/-- Woodford (2003), App. G.1: a nonzero `μ` is selected as many times as its algebraic
multiplicity as an eigenvalue of `Ψ`. -/
theorem count_selOf {Ψ : Matrix ιZ ιZ ℝ} {μ : ℂ} (hμ : μ ≠ 0) :
    (selOf Ψ).count μ = (Ψ.map Complex.ofReal).charpoly.rootMultiplicity μ := by
  rw [selOf, Multiset.count_filter_of_pos (p := fun x : ℂ => x ≠ 0) hμ, count_roots]

omit [Fintype ιz] [DecidableEq ιz] in
/-- Woodford (2003), App. G.1, fn 2: the eigenvalues of a real matrix come in conjugate pairs,
so the selection of a real `Ψ` is conjugation-closed. -/
theorem selOf_conjClosed (Ψ : Matrix ιZ ιZ ℝ) : ConjClosed (selOf Ψ) := by
  set q := (Ψ.map Complex.ofReal).charpoly with hq
  have hq' : q = Ψ.charpoly.map Complex.ofRealHom := by
    rw [hq, ← Matrix.charpoly_map]
    rfl
  have hmap : q.map (starRingEnd ℂ) = q := by
    rw [hq', Polynomial.map_map]
    congr 1
    ext x
    simp
  have hR : q.roots.map (starRingEnd ℂ) = q.roots := by
    rw [roots_map_of_injective_of_card_eq_natDegree (starRingEnd ℂ).injective
      (IsAlgClosed.card_roots_eq_natDegree), hmap]
  have hcnt : ∀ μ, q.roots.count (starRingEnd ℂ μ) = q.roots.count μ := by
    intro μ
    conv_lhs => rw [← hR]
    exact Multiset.count_map_eq_count' _ _ (starRingEnd ℂ).injective μ
  unfold ConjClosed selOf
  rw [← hq]
  ext μ
  have e : μ = starRingEnd ℂ (starRingEnd ℂ μ) := by simp
  rw [e, Multiset.count_map_eq_count' _ _ (starRingEnd ℂ).injective, ← e]
  by_cases h0 : μ = 0
  · subst h0
    simp
  · have h0' : starRingEnd ℂ μ ≠ 0 := by simpa using h0
    rw [Multiset.count_filter_of_pos (p := fun x : ℂ => x ≠ 0) h0',
      Multiset.count_filter_of_pos (p := fun x : ℂ => x ≠ 0) h0, hcnt]

/-- Woodford (2003), App. G.1, (G.4): every selected root of a deflating split is a nonzero root
of (1.15) with `|μ| < β⁻¹`. -/
theorem mem_selOf_split {S : LinearRESystem ιZ ιz} {β : ℝ} (D : DeflatingSplit S β) {μ : ℂ}
    (h : μ ∈ selOf D.Ψ) : μ ≠ 0 ∧ S.pencilPoly.eval μ = 0 ∧ ‖μ‖ < β⁻¹ := by
  obtain ⟨h0, hd⟩ := mem_selOf.mp h
  exact ⟨h0, D.eig_isRoot hd, D.eig_lt μ hd⟩

/-- Woodford (2003), App. G.1: the columns of `J` are independent, since `J₁` is invertible. -/
theorem indep_of_split {S : LinearRESystem ιZ ιz} {β : ℝ} (D : DeflatingSplit S β) :
    LinearIndependent ℝ D.Jᵀ := by
  refine Fintype.linearIndependent_iff.mpr fun g hg => ?_
  have hJ : D.J *ᵥ g = 0 := by
    rw [← hg]
    funext i
    simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hJ1 : J1 D.J *ᵥ g = 0 := by
    funext i
    have := congrFun hJ (Sum.inl i)
    simpa [mulVec, dotProduct, J1] using this
  exact congrFun (eq_zero_of_mulVec_eq_zero D.J1_det hJ1)

/-- Woodford (2003), App. G.1, (G.4) and fn 2: **every deflating split is a real selection** for
the roots it selects, with the same `J` and `Ψ`. -/
def toRealSel {S : LinearRESystem ιZ ιz} {β : ℝ} (D : DeflatingSplit S β) :
    RealSelection S (selOf D.Ψ) where
  J := D.J
  Ψ := D.Ψ
  deflate := D.deflate
  indep := indep_of_split D
  eig := fun μ hμ => by
    by_cases h0 : μ = 0
    · exact Or.inl h0
    · exact Or.inr (mem_selOf.mpr ⟨h0, hμ⟩)

omit [Fintype ιz] [DecidableEq ιz] in
/-- Woodford (2003), Assumption 8.2 and App. G.1: **a selection with count data is the selection
of `Ψ`**: if every eigenvalue of `Ψ` is `0` or in `sel`, the elements of `sel` are nonzero, and
each is counted as often as its multiplicity, then `sel = selOf Ψ`. -/
theorem sel_eq_selOf {sel : Multiset ℂ} {Ψ : Matrix ιZ ιZ ℝ} (hnz : ∀ μ ∈ sel, μ ≠ 0)
    (heig : ∀ μ : ℂ, (Matrix.scalar ιZ μ - Ψ.map Complex.ofReal).det = 0 → μ = 0 ∨ μ ∈ sel)
    (hcount : ∀ μ ∈ sel, (Ψ.map Complex.ofReal).charpoly.rootMultiplicity μ = sel.count μ) :
    sel = selOf Ψ := by
  ext μ
  by_cases h0 : μ = 0
  · subst h0
    rw [Multiset.count_eq_zero.mpr (fun h => hnz 0 h rfl),
      Multiset.count_eq_zero.mpr (fun h => (mem_selOf.mp h).1 rfl)]
  · rw [count_selOf h0]
    by_cases hm : μ ∈ sel
    · exact (hcount μ hm).symm
    · rw [Multiset.count_eq_zero.mpr hm, eq_comm, ← count_roots, Multiset.count_eq_zero]
      intro hr
      rw [mem_roots (charpoly_monic _).ne_zero, IsRoot.def, eval_charpoly] at hr
      rcases heig μ hr with h | h
      · exact h0 h
      · exact hm h

/-! ### `ker A` lies in every deflating subspace -/

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), App. G.1 (tool): `J` is stacked from its blocks, `J v = (J₁v, J₂v)`. -/
theorem J_mulVec_blocks {κ : Type*} [Fintype κ] (J : Matrix (ιZ ⊕ ιz) κ ℝ) (w : κ → ℝ) :
    J *ᵥ w = Sum.elim (J1 J *ᵥ w) (J2 J *ᵥ w) := by
  funext a
  rcases a with a | a <;> rfl

/-- Woodford (2003), (G.4) by blocks: `A₁₁J₁ + A₁₂J₂ = J₁Ψ` and `A₂₁J₁ + A₂₂J₂ = ẼJ₂Ψ`. -/
theorem deflate_blocks {S : LinearRESystem ιZ ιz} {J : Matrix (ιZ ⊕ ιz) ιZ ℝ}
    {Ψ : Matrix ιZ ιZ ℝ} (hd : S.Ahat * J = S.Ihat * J * Ψ) :
    S.A11 * J1 J + S.A12 * J2 J = J1 J * Ψ ∧ S.A21 * J1 J + S.A22 * J2 J = S.Et * J2 J * Ψ := by
  constructor
  · ext i j
    have := congrFun (congrFun hd (Sum.inl i)) j
    simpa [LinearRESystem.Ahat, LinearRESystem.Ihat, mul_apply, Fintype.sum_sum_type, J1, J2,
      one_apply, ite_mul] using this
  · ext i j
    have := congrFun (congrFun hd (Sum.inr i)) j
    simpa [LinearRESystem.Ahat, LinearRESystem.Ihat, mul_apply, Fintype.sum_sum_type, J1, J2,
      one_apply, ite_mul] using this

/-- Woodford (2003), (1.20), p. 553 (tool): `K' = A₂₂ − Ẽ J₂ J₁⁻¹ A₁₂`. -/
theorem Kmat_transpose {S : LinearRESystem ιZ ιz} {J : Matrix (ιZ ⊕ ιz) ιZ ℝ} :
    (Kmat S J)ᵀ = S.A22 - S.Et * J2 J * (J1 J)⁻¹ * S.A12 := by
  rw [Kmat, Υmat, transpose_add, transpose_transpose, transpose_mul, transpose_transpose,
    transpose_neg, transpose_mul, transpose_mul, transpose_transpose, transpose_transpose,
    transpose_nonsing_inv, transpose_transpose, Matrix.neg_mul, ← sub_eq_add_neg,
    Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  simp only [Matrix.mul_assoc]

/-- Woodford (2003), App. G.1 and (1.20) (**the key identity**): for `v ∈ ker A`,
`K'(v_z − J₂J₁⁻¹v_Z) = 0`. -/
theorem Kt_mulVec_ker {S : LinearRESystem ιZ ιz} {J : Matrix (ιZ ⊕ ιz) ιZ ℝ}
    {Ψ : Matrix ιZ ιZ ℝ} (hd : S.Ahat * J = S.Ihat * J * Ψ) (hJ1 : (J1 J).det ≠ 0)
    {v : ιZ ⊕ ιz → ℝ} (hv : S.Ahat *ᵥ v = 0) :
    (Kmat S J)ᵀ *ᵥ (v ∘ Sum.inr - J2 J *ᵥ ((J1 J)⁻¹ *ᵥ (v ∘ Sum.inl))) = 0 := by
  obtain ⟨d1, d2⟩ := deflate_blocks hd
  set G := (J1 J)⁻¹ with hG
  have hu : IsUnit (J1 J).det := isUnit_iff_ne_zero.mpr hJ1
  have hJG : J1 J * G = 1 := mul_nonsing_inv _ hu
  have hGJ : G * J1 J = 1 := nonsing_inv_mul _ hu
  set vZ := v ∘ Sum.inl
  set vz := v ∘ Sum.inr
  have hk : S.Ahat *ᵥ v = Sum.elim (S.A11 *ᵥ vZ + S.A12 *ᵥ vz) (S.A21 *ᵥ vZ + S.A22 *ᵥ vz) := by
    have e : v = Sum.elim vZ vz := by
      funext a
      rcases a with a | a <;> rfl
    conv_lhs => rw [e]
    rw [LinearRESystem.Ahat, fromBlocks_mulVec]
    rfl
  have k1 : S.A12 *ᵥ vz = -(S.A11 *ᵥ vZ) := by
    have := congrFun (hk.symm.trans hv)
    funext i
    have h := this (Sum.inl i)
    simp only [Sum.elim_inl, Pi.add_apply, Pi.zero_apply] at h
    simp only [Pi.neg_apply]
    linarith
  have k2 : S.A22 *ᵥ vz = -(S.A21 *ᵥ vZ) := by
    have := congrFun (hk.symm.trans hv)
    funext i
    have h := this (Sum.inr i)
    simp only [Sum.elim_inr, Pi.add_apply, Pi.zero_apply] at h
    simp only [Pi.neg_apply]
    linarith
  have hA12J2 : S.A12 * J2 J = J1 J * Ψ - S.A11 * J1 J := by rw [← d1]; abel
  have hA22J2 : S.A22 * J2 J = S.Et * J2 J * Ψ - S.A21 * J1 J := by rw [← d2]; abel
  rw [Kmat_transpose, sub_mulVec, mulVec_sub, mulVec_sub, k2, ← hG]
  have e1 : S.A22 *ᵥ (J2 J *ᵥ (G *ᵥ vZ)) = (S.Et * J2 J * Ψ * G) *ᵥ vZ - S.A21 *ᵥ vZ := by
    rw [mulVec_mulVec, mulVec_mulVec, hA22J2, Matrix.sub_mul, sub_mulVec,
      Matrix.mul_assoc S.A21, hJG, Matrix.mul_one]
  have e2 : (S.Et * J2 J * G * S.A12) *ᵥ vz = -((S.Et * J2 J * G * S.A11) *ᵥ vZ) := by
    rw [← mulVec_mulVec, k1, mulVec_neg, mulVec_mulVec]
  have e3 : (S.Et * J2 J * G * S.A12) *ᵥ (J2 J *ᵥ (G *ᵥ vZ)) =
      (S.Et * J2 J * Ψ * G) *ᵥ vZ - (S.Et * J2 J * G * S.A11) *ᵥ vZ := by
    rw [mulVec_mulVec, mulVec_mulVec, show S.Et * J2 J * G * S.A12 * J2 J * G =
      S.Et * J2 J * G * (S.A12 * J2 J) * G by simp only [Matrix.mul_assoc], hA12J2,
      Matrix.mul_sub, Matrix.sub_mul, sub_mulVec]
    congr 2
    · rw [show S.Et * J2 J * G * (J1 J * Ψ) * G = S.Et * J2 J * (G * J1 J) * Ψ * G by
        simp only [Matrix.mul_assoc], hGJ, Matrix.mul_one]
    · rw [show S.Et * J2 J * G * (S.A11 * J1 J) * G = S.Et * J2 J * G * S.A11 * (J1 J * G) by
        simp only [Matrix.mul_assoc], hJG, Matrix.mul_one]
  rw [e1, e2, e3]
  abel

/-- Woodford (2003), App. G.1, Assumption 8.3 and (1.20) (**`ker A` lies in every deflating
subspace**): for every deflating split, each `v` with `A v = 0` is `J w` for some `w` — the
invertibility of `J₁` and of `K = A₂₂' + A₁₂'Υ` forces the zero roots of `ker A` into the
selection. -/
theorem ker_le_colSpan {S : LinearRESystem ιZ ιz} {β : ℝ} (D : DeflatingSplit S β) :
    ∀ v, S.Ahat *ᵥ v = 0 → ∃ w, D.J *ᵥ w = v := by
  intro v hv
  have hK := Kt_mulVec_ker D.deflate D.J1_det hv
  have hKt : ((Kmat S D.J)ᵀ).det ≠ 0 := by rw [det_transpose]; exact D.K_det
  have hu := eq_zero_of_mulVec_eq_zero hKt hK
  refine ⟨(J1 D.J)⁻¹ *ᵥ (v ∘ Sum.inl), ?_⟩
  rw [J_mulVec_blocks]
  funext a
  rcases a with a | a
  · simp only [Sum.elim_inl]
    rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr D.J1_det), one_mulVec]
    rfl
  · simp only [Sum.elim_inr]
    have := congrFun hu a
    simp only [Pi.sub_apply, Pi.zero_apply, Function.comp_apply] at this
    linarith

/-! ### The count data of a deflating split -/

/-- Woodford (2003), App. G.1 (**the count data of a split, exactly**): a deflating split has the
count data for the roots it selects iff the zero eigenvalue of `Ψ` has algebraic multiplicity
exactly `n − rank A` (the other two parts of `TidyR5bSelLink.CountData` always hold). -/
theorem countData_iff {S : LinearRESystem ιZ ιz} {β : ℝ} (D : DeflatingSplit S β) :
    CountData S (selOf D.Ψ) D.J D.Ψ ↔
      (D.Ψ.map Complex.ofReal).charpoly.rootMultiplicity 0 =
        Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank := by
  refine ⟨fun h => h.zero_count, fun h => ⟨fun μ hμ => ?_, h, ker_le_colSpan D⟩⟩
  exact (count_selOf (mem_selOf.mp hμ).1).symm

/-- Woodford (2003), App. G.1 and Assumption 8.3 (**the count data is automatic for a semisimple
zero root**): if (1.15) is nonzero and its zero root is semisimple
(`CaseIIBasis.ZeroSemisimple`), every deflating split has the count data for the roots it
selects. -/
theorem countData_of_semisimple {S : LinearRESystem ιZ ιz} {β : ℝ} (hreg : S.pencilPoly ≠ 0)
    (hz : ZeroSemisimple S) (D : DeflatingSplit S β) : CountData S (selOf D.Ψ) D.J D.Ψ := by
  rw [countData_iff]
  obtain ⟨s, hs0, hsev⟩ := PencilEigen.Construction.exists_shift hreg
  have hs : (S.Ahat - s • S.Ihat).det ≠ 0 := by
    intro h0
    apply hsev
    rw [pencilPoly_eval, det_pencil_ofReal, h0, Complex.ofReal_zero]
  have hsel : ∀ μ ∈ selOf D.Ψ, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0 := fun μ hμ =>
    ⟨(mem_selOf_split D hμ).1, (mem_selOf_split D hμ).2.1⟩
  have hP := P_isUnit S hs0 hs hsel (toRealSel D).eig
  have hfr := finrank_colSpan_inf S hs D.deflate (indep_of_split D) hP (ν0_ne_zero hs0)
  have hμ0 : (s : ℂ) + (ν0 s)⁻¹ = 0 := by
    rw [ν0, inv_inv]
    ring
  rw [hμ0, maxGen_ν0_eq S hs0 hs hz,
    inf_eq_right.mpr (eigen_ν0_le S hs0 hs (ker_le_colSpan D)),
    finrank_eigenspace_ν0 S hs0 hs] at hfr
  exact hfr.symm

/-! ### A split through a Jordan chain of the zero root -/

/-- Woodford (2003), eq. (1.1), p. 537 (**the counterexample**): `n_Z = 2`, `n_z = 1`,
`A₁₁ = [[0, 1], [0, 0]]` (a Jordan chain of the zero root), `A₁₂ = 0`, `A₂₁ = 0`, `A₂₂ = 1`,
`Ẽ = 1`, `B₂ = 1`. -/
noncomputable def chainSys : LinearRESystem (Fin 2) (Fin 1) where
  A11 := !![0, 1; 0, 0]
  A12 := 0
  A21 := 0
  A22 := 1
  Et := 1
  B2 := ![1]
  A22_isUnit := by simp
  B2_ne_zero := by
    intro h
    have := congrFun h 0
    simp at this

/-- Woodford (2003), App. G.1, (G.4) (the counterexample): `J = [e_{Z₁} e_{Z₂}]`. -/
def chainJ : Matrix (Fin 2 ⊕ Fin 1) (Fin 2) ℝ :=
  Matrix.of fun a j => Sum.elim (fun i => if i = j then (1 : ℝ) else 0) (fun _ => 0) a

/-- Woodford (2003), App. G.1, (G.4) (**the counterexample split**): `J = [e_{Z₁} e_{Z₂}]` and
`Ψ = [[0, 1], [0, 0]]`; it is a deflating split for every `β > 0`. -/
noncomputable def chainSplit {β : ℝ} (hβ : 0 < β) : DeflatingSplit chainSys β where
  J := chainJ
  Ψ := !![0, 1; 0, 0]
  deflate := by
    ext a j
    rcases a with a | a <;> fin_cases j <;>
      simp [chainJ, chainSys, LinearRESystem.Ahat, LinearRESystem.Ihat, mul_apply,
        Fintype.sum_sum_type]
  eig_lt := fun μ hμ => by
    have h : μ ^ 2 = 0 := by
      rw [det_fin_two] at hμ
      simpa [Matrix.scalar_apply, sq] using hμ
    rw [pow_eq_zero_iff two_ne_zero |>.mp h, norm_zero]
    exact inv_pos.mpr hβ
  J1_det := by
    have e : J1 chainJ = 1 := by
      ext i j
      simp [chainJ, J1, one_apply]
    rw [e, det_one]
    exact one_ne_zero
  K_det := by
    have e : Kmat chainSys chainJ = 1 := by
      simp [Kmat, chainSys]
    rw [e, det_one]
    exact one_ne_zero

/-- Woodford (2003), p. 547: `ker A` of `chainSys` is spanned by `e_{Z₁}`. -/
theorem chain_ker : LinearMap.ker chainSys.Ahat.mulVecLin =
    Submodule.span ℝ {Pi.single (Sum.inl 0) 1} := by
  ext x
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Submodule.mem_span_singleton]
  constructor
  · intro h
    have h0 := congrFun h (Sum.inl 0)
    have h3 := congrFun h (Sum.inr 0)
    simp [LinearRESystem.Ahat, mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
      chainSys] at h0 h3
    refine ⟨x (Sum.inl 0), funext fun a => ?_⟩
    rcases a with a | a <;> fin_cases a <;> simp [h0, h3]
  · rintro ⟨a, rfl⟩
    funext r
    rcases r with r | r <;> fin_cases r <;>
      simp [LinearRESystem.Ahat, mulVec, dotProduct, chainSys, Pi.single_apply]

/-- Woodford (2003), p. 547: `rank A = 2`, so `n − rank A = 1`. -/
theorem chain_rank : chainSys.Ahat.rank = 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker chainSys.Ahat.mulVecLin
  rw [chain_ker, finrank_span_singleton (by
    intro h0
    have := congrFun h0 (Sum.inl 0)
    simp at this), Module.finrank_fintype_fun_eq_card] at h
  change chainSys.Ahat.rank + 1 = _ at h
  simp at h
  omega

/-- Woodford (2003), App. G.1: the zero eigenvalue of `Ψ = [[0, 1], [0, 0]]` has algebraic
multiplicity `2`. -/
theorem chain_rootMult {β : ℝ} (hβ : 0 < β) :
    ((chainSplit hβ).Ψ.map Complex.ofReal).charpoly.rootMultiplicity 0 = 2 := by
  have e : ((chainSplit hβ).Ψ.map Complex.ofReal).charpoly = X ^ 2 := by
    rw [charpoly_fin_two]
    simp [chainSplit, trace_fin_two, det_fin_two]
  rw [e, show (X : ℂ[X]) ^ 2 = (X - C 0) ^ 2 by simp, rootMultiplicity_X_sub_C_pow]

/-- **Woodford (2003), App. G.1 and Assumption 8.2 (counterexample): a deflating split without
the count data.** `chainSplit` is a deflating split of `chainSys` whose `Ψ` has the zero
eigenvalue twice while `n − rank A = 1`, so `TidyR5bSelLink.CountData` fails for **every**
selection. -/
theorem chain_not_countData {β : ℝ} (hβ : 0 < β) (sel : Multiset ℂ) :
    ¬ CountData chainSys sel (chainSplit hβ).J (chainSplit hβ).Ψ := by
  intro h
  have h0 := h.zero_count
  rw [chain_rootMult hβ, chain_rank] at h0
  simp at h0

/-- Woodford (2003), (1.15): `det(A − 2Î) = −4 ≠ 0` for `chainSys`, so (1.15) is nonzero. -/
theorem chain_reg : chainSys.pencilPoly ≠ 0 := by
  intro h
  have e := congrArg (Polynomial.eval ((2 : ℝ) : ℂ)) h
  rw [pencilPoly_eval, det_pencil_ofReal, eval_zero] at e
  have hd : (chainSys.Ahat - (2 : ℝ) • chainSys.Ihat).det = -4 := by
    have e2 : chainSys.Ahat - (2 : ℝ) • chainSys.Ihat =
        fromBlocks (!![-2, 1; 0, -2]) 0 0 (-1) := by
      ext a b
      rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
        norm_num [chainSys, LinearRESystem.Ahat, LinearRESystem.Ihat]
    rw [e2, det_fromBlocks_zero₂₁, det_fin_two]
    simp
    norm_num
  rw [hd] at e
  norm_num at e

/-- Woodford (2003), App. G.1 (**the counterexample is the non-semisimple case**): the zero root
of `chainSys` is not semisimple, as it must be by `countData_of_semisimple`. -/
theorem chain_not_zeroSemisimple : ¬ ZeroSemisimple chainSys := fun hz =>
  chain_not_countData one_pos _ (countData_of_semisimple chain_reg hz (chainSplit one_pos))

/-! ### The uniqueness criterion for all deflating splits -/

/-- Woodford (2003), eq. (1.21), App. G.1, Assumptions 8.2 and 8.4, Proposition 8.1 (**the exact
criterion for every deflating split**): under the hypotheses of `TidyR5bSelLink.Υ_unique_iff`,
`Υ` is the same for every deflating split that selects the roots `h82.sel` and has the count
data iff every partially selected root has a single Jordan chain. -/
theorem Υ_unique_iff_split {S : LinearRESystem ιZ ιz} {β : ℝ} (hβ : 0 < β)
    (h82 : Assumption82 S β) (hc : ConjClosed h82.sel) (hreg : S.pencilPoly ≠ 0)
    (h84 : Assumption84 S h82.sel) (hE : IsUnit S.Et.det) {s : ℝ} (hs0 : s ≠ 0)
    (hs : (S.Ahat - s • S.Ihat).det ≠ 0) :
    (∀ D D' : DeflatingSplit S β, selOf D.Ψ = h82.sel → selOf D'.Ψ = h82.sel →
      CountData S h82.sel D.J D.Ψ → CountData S h82.sel D'.J D'.Ψ →
        Υmat S D.J = Υmat S D'.J) ↔ CyclicPartial S h82.sel s := by
  rw [← Υ_unique_iff hβ h82 hc hreg h84 hE hs0 hs]
  have hnz : ∀ μ ∈ h82.sel, μ ≠ 0 := fun μ hμ => by
    have := Multiset.mem_of_le h82.sel_le hμ
    rw [Multiset.mem_filter] at this
    exact this.2.1
  constructor
  · intro h R R' hR hR'
    have e : ∀ R'' : RealSelection S h82.sel, CountData S h82.sel R''.J R''.Ψ →
        selOf (splitGen hβ h82 R'' hreg h84).Ψ = h82.sel := fun R'' hR'' =>
      (sel_eq_selOf hnz R''.eig hR''.sel_count).symm
    exact h (splitGen hβ h82 R hreg h84) (splitGen hβ h82 R' hreg h84) (e R hR) (e R' hR') hR hR'
  · intro h D D' hD hD' hcd hcd'
    exact h ⟨D.J, D.Ψ, D.deflate, indep_of_split D, fun μ hμ => hD ▸ (toRealSel D).eig μ hμ⟩
      ⟨D'.J, D'.Ψ, D'.deflate, indep_of_split D', fun μ hμ => hD' ▸ (toRealSel D').eig μ hμ⟩
      hcd hcd'

/-- Woodford (2003), eq. (1.21), App. G.1, Proposition 8.1 (**the criterion with no count data,
semisimple zero root**): if moreover the zero root is semisimple, `Υ` is the same for every
deflating split selecting `h82.sel` iff `TidyR5bCyclicSel.CyclicPartial` holds. -/
theorem Υ_unique_iff_split_semisimple {S : LinearRESystem ιZ ιz} {β : ℝ} (hβ : 0 < β)
    (h82 : Assumption82 S β) (hc : ConjClosed h82.sel) (hreg : S.pencilPoly ≠ 0)
    (h84 : Assumption84 S h82.sel) (hE : IsUnit S.Et.det) (hz : ZeroSemisimple S) {s : ℝ}
    (hs0 : s ≠ 0) (hs : (S.Ahat - s • S.Ihat).det ≠ 0) :
    (∀ D D' : DeflatingSplit S β, selOf D.Ψ = h82.sel → selOf D'.Ψ = h82.sel →
        Υmat S D.J = Υmat S D'.J) ↔ CyclicPartial S h82.sel s := by
  rw [← Υ_unique_iff_split hβ h82 hc hreg h84 hE hs0 hs]
  constructor
  · intro h D D' hD hD' _ _
    exact h D D' hD hD'
  · intro h D D' hD hD'
    have c1 := countData_of_semisimple hreg hz D
    have c2 := countData_of_semisimple hreg hz D'
    rw [hD] at c1
    rw [hD'] at c2
    exact h D D' hD hD' c1 c2

end Woodford.OptimalPolicyRules.TidyR6aSelDeflating
