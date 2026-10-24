/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.PencilSplit
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The eigenvector apparatus of Appendix G.1: Assumptions 8.2 and 8.3

Woodford (2003), *Interest and Prices*, Chapter 8, Assumption 8.2 (p. 552) and Appendix G.1,
Assumption 8.3 and (G.1)–(G.4) (pp. 716–718).

* `Assumption82`, `Assumption83`: the two assumptions as stated in the book. Assumption 8.2
  selects `n_Z` roots of (1.15) with `|μ| < β⁻¹`, including the zero root counted `n − rank A`
  times, either closed under conjugation (case (i)) or with one unpaired complex root (case
  (ii)). Assumption 8.3: distinct nonzero roots, `rank Ẽ + rank A − n_z` of them, and the
  kernel vectors of `A`, `A'`, `Î'`, `Î`. The polynomial (1.15) is taken to be nonzero, as the
  book's root count presupposes.
* `RealSelection`: a real `n × n_Z` matrix `J` with independent columns and `Ψ` with
  `A J = Î J Ψ` (G.4) whose eigenvalues are the selected roots or zero.
* `exists_realSelection`: under Assumption 8.2 case (i) and Assumption 8.3 such a pair exists.
  Its columns are the real eigenvectors of the real selected roots, the real and imaginary parts
  of eigenvectors of the selected complex pairs (fn 2, p. 717), and a basis of `ker A`; `Ψ` is
  block diagonal with blocks `μ`, `[[Re μ, Im μ], [−Im μ, Re μ]]` and `0`. Linear independence
  comes from a shift `s` (not a root): `A u = μ Î u` iff `u` is an eigenvector of
  `N = (A − sÎ)⁻¹ Î` for `(μ − s)⁻¹`, so eigenvectors of distinct roots are independent.
-/

namespace Woodford.OptimalPolicyRules.PencilEigen

open Matrix GeneralSetup PencilSplit GeneralFOC.Selection

variable {ιZ ιz : Type*} [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz]

/-! ### The assumptions -/

/-- Woodford (2003), Assumption 8.2, p. 552 (the selection condition): (i) the selected roots are
closed under conjugation, or (ii) exactly one selected complex root `μ` has its conjugate
unselected, and `|Re μ⁻¹| > β`. -/
def SelCases (sel : Multiset ℂ) (β : ℝ) : Prop :=
  ConjClosed sel ∨ ∃ μ ∈ sel, starRingEnd ℂ μ ∉ sel ∧ ConjClosed (sel.erase μ) ∧ β < |(μ⁻¹).re|

/-- Woodford (2003), Assumption 8.2, p. 552: (1.15) has at least `n_Z` roots with `|μ| < β⁻¹`
(zero counted `n − rank A` times), and one can select exactly `n_Z` of them, including the
`n − rank A` zeros — `sel` is the multiset of the selected *nonzero* roots — such that either
(i) the selection is closed under complex conjugation, or (ii) it contains a single complex root
`μ` whose conjugate is not selected, with `|Re μ⁻¹| > β`. -/
structure Assumption82 (S : LinearRESystem ιZ ιz) (β : ℝ) where
  count : S.Assumption82Count β
  sel : Multiset ℂ
  sel_le : sel ≤ S.pencilPoly.roots.filter (fun μ => μ ≠ 0 ∧ ‖μ‖ < β⁻¹)
  sel_card : Multiset.card sel + (Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank) = Fintype.card ιZ
  cases : SelCases sel β

/-- Woodford (2003), Assumption 8.3, App. G.1, p. 716: the nonzero roots of (1.15). -/
noncomputable def nonzeroRoots (S : LinearRESystem ιZ ιz) : Multiset ℂ :=
  S.pencilPoly.roots.filter (fun μ => μ ≠ 0)

/-- Woodford (2003), Assumption 8.3, App. G.1, p. 716: `n − rank A` independent vectors `uᵢ`
with `A uᵢ = 0`. -/
def KerA (S : LinearRESystem ιZ ιz) : Prop :=
  ∃ u : Fin (Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank) → ιZ ⊕ ιz → ℝ,
    LinearIndependent ℝ u ∧ ∀ i, S.Ahat *ᵥ u i = 0

/-- Woodford (2003), Assumption 8.3, App. G.1, p. 716: `n − rank A` independent vectors `fᵢ`
with `fᵢ' A = 0`. -/
def KerALeft (S : LinearRESystem ιZ ιz) : Prop :=
  ∃ f : Fin (Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank) → ιZ ⊕ ιz → ℝ,
    LinearIndependent ℝ f ∧ ∀ i, f i ᵥ* S.Ahat = 0

/-- Woodford (2003), Assumption 8.3, App. G.1, p. 716: `n_z − rank Ẽ` independent vectors `eⱼ`
with `eⱼ' Î = 0`. -/
def KerILeft (S : LinearRESystem ιZ ιz) : Prop :=
  ∃ e : Fin (Fintype.card ιz - S.Et.rank) → ιZ ⊕ ιz → ℝ,
    LinearIndependent ℝ e ∧ ∀ j, e j ᵥ* S.Ihat = 0

/-- Woodford (2003), Assumption 8.3, App. G.1, p. 716: `n_z − rank Ẽ` independent vectors `hⱼ`
with `Î hⱼ = 0`. -/
def KerI (S : LinearRESystem ιZ ιz) : Prop :=
  ∃ h : Fin (Fintype.card ιz - S.Et.rank) → ιZ ⊕ ιz → ℝ,
    LinearIndependent ℝ h ∧ ∀ j, S.Ihat *ᵥ h j = 0

/-- Woodford (2003), Assumption 8.3, App. G.1, p. 716: (1.15) — a nonzero polynomial, as its
root count presupposes — has `rank Ẽ + rank A − n_z` distinct nonzero roots; there are
`n − rank A` independent `uᵢ` with `A uᵢ = 0` and as many `fᵢ` with `fᵢ' A = 0`; there are
`n_z − rank Ẽ` independent `eⱼ` with `eⱼ' Î = 0` and as many `hⱼ` with `Î hⱼ = 0`. -/
structure Assumption83 (S : LinearRESystem ιZ ιz) where
  regular : S.pencilPoly ≠ 0
  nodup : (nonzeroRoots S).Nodup
  card_nonzero : Multiset.card (nonzeroRoots S) = S.Et.rank + S.Ahat.rank - Fintype.card ιz
  kerA : KerA S
  kerA_left : KerALeft S
  kerI_left : KerILeft S
  kerI : KerI S

/-- Woodford (2003), App. G.1, (G.4) and fn 2, p. 717: a real selection — `J` (`n × n_Z`, real,
independent columns) and `Ψ` with `A J = Î J Ψ`, every eigenvalue of `Ψ` being `0` or a selected
root. -/
structure RealSelection (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) where
  J : Matrix (ιZ ⊕ ιz) ιZ ℝ
  Ψ : Matrix ιZ ιZ ℝ
  deflate : S.Ahat * J = S.Ihat * J * Ψ
  indep : LinearIndependent ℝ Jᵀ
  eig : ∀ μ : ℂ, (Matrix.scalar ιZ μ - Ψ.map Complex.ofReal).det = 0 → μ = 0 ∨ μ ∈ sel

/-! ### Elementary facts -/

/-- Woodford (2003), App. G.1: an eigenvalue of a complex matrix has an eigenvector. -/
theorem exists_eigvec {κ : Type*} [Fintype κ] [DecidableEq κ] {Q : Matrix κ κ ℂ} {μ : ℂ}
    (h : (Matrix.scalar κ μ - Q).det = 0) : ∃ z, z ≠ 0 ∧ Q *ᵥ z = μ • z := by
  obtain ⟨z, hz0, hz⟩ := exists_mulVec_eq_zero_iff.mpr h
  refine ⟨z, hz0, ?_⟩
  rw [sub_mulVec, sub_eq_zero] at hz
  rw [← hz]
  funext i
  simp [Matrix.scalar_apply, mulVec_diagonal]

/-- Woodford (2003), App. G.1: real matrices act on complexified vectors componentwise,
`A (ofReal ∘ v) = ofReal ∘ (A v)`. -/
theorem map_mulVec_ofReal {m n : Type*} [Fintype n] (A : Matrix m n ℝ) (v : n → ℝ) :
    A.map Complex.ofReal *ᵥ (fun i => (v i : ℂ)) = fun i => ((A *ᵥ v) i : ℂ) := by
  funext i
  simp [mulVec, dotProduct]

/-- Woodford (2003), App. G.1 (complex eigenvectors come in conjugate pairs): for real matrices,
`A (conj w) = conj (A w)`. -/
theorem map_mulVec_conj {m n : Type*} [Fintype n] (A : Matrix m n ℝ) (w : n → ℂ) :
    A.map Complex.ofReal *ᵥ (fun i => starRingEnd ℂ (w i)) =
      fun i => starRingEnd ℂ ((A.map Complex.ofReal *ᵥ w) i) := by
  funext i
  simp [mulVec, dotProduct, map_sum]

/-- Woodford (2003), App. G.1: real vectors that are linearly independent over `ℝ` stay
independent over `ℂ`. -/
theorem linearIndependent_ofReal {κ n : Type*} [Finite κ] {v : κ → n → ℝ}
    (hv : LinearIndependent ℝ v) : LinearIndependent ℂ (fun k i => (v k i : ℂ)) := by
  cases nonempty_fintype κ
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro g hg k
  have hre : ∑ k, (g k).re • v k = 0 := by
    funext i
    have := congrArg Complex.re (congrFun hg i)
    simpa [Finset.sum_apply, Complex.re_sum] using this
  have him : ∑ k, (g k).im • v k = 0 := by
    funext i
    have := congrArg Complex.im (congrFun hg i)
    simpa [Finset.sum_apply, Complex.im_sum] using this
  exact Complex.ext (by simpa using hv _ hre k) (by simpa using hv _ him k)

/-- Woodford (2003), App. G.1: real parts of a complex vector under a real matrix. -/
theorem re_mulVec_map {m n : Type*} [Fintype n] (M : Matrix m n ℝ) (z : n → ℂ) (i : m) :
    ((M.map Complex.ofReal *ᵥ z) i).re = (M *ᵥ fun k => (z k).re) i := by
  simp [mulVec, dotProduct, Complex.re_sum]

/-- Woodford (2003), App. G.1: imaginary parts of a complex vector under a real matrix. -/
theorem im_mulVec_map {m n : Type*} [Fintype n] (M : Matrix m n ℝ) (z : n → ℂ) (i : m) :
    ((M.map Complex.ofReal *ᵥ z) i).im = (M *ᵥ fun k => (z k).im) i := by
  simp [mulVec, dotProduct, Complex.im_sum]

/-- Woodford (2003), App. G.1 (restated from the Woodford Chapter 4 project,
`InvariantSplit.finrank_finset_sup`): the dimension of the span of finitely many independent
subspaces is the sum of their dimensions. -/
theorem finrank_finset_sup {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : ℂ → Submodule ℂ V} (hW : iSupIndep W) (s : Finset ℂ) :
    Module.finrank ℂ (s.sup W : Submodule ℂ V) = ∑ μ ∈ s, Module.finrank ℂ (W μ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sup_insert, Finset.sum_insert ha, ← ih]
    have hd : Disjoint (W a) (s.sup W) := by
      rw [Finset.sup_eq_iSup]
      have := hW.disjoint_biSup (x := a) (y := (s : Set ℂ)) (by simpa using ha)
      simpa using this
    have h := Submodule.finrank_sup_add_finrank_inf_eq (W a) (s.sup W)
    rw [disjoint_iff.mp hd, finrank_bot, add_zero] at h
    exact h

omit [DecidableEq ιZ] in
/-- Woodford (2003), Assumption 8.3 with (1.1): `rank A ≥ n_z`, since `A₂₂` is invertible. -/
theorem card_le_rank_Ahat (S : LinearRESystem ιZ ιz) : Fintype.card ιz ≤ S.Ahat.rank := by
  have h1 : S.A22.rank = Fintype.card ιz :=
    rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr S.A22_isUnit)
  have h2 : S.Ahat.submatrix Sum.inr Sum.inr = S.A22 := by
    ext i j
    rfl
  rw [← h1, ← h2]
  exact rank_submatrix_le _ _ _

/-- Woodford (2003), (1.15): the determinant of the complexified pencil at a real point is the
real determinant. -/
theorem det_pencil_ofReal (S : LinearRESystem ιZ ιz) (x : ℝ) :
    (S.Ahat.map Complex.ofReal - (x : ℂ) • S.Ihat.map Complex.ofReal).det =
      ((S.Ahat - x • S.Ihat).det : ℂ) := by
  have e := Complex.ofRealHom.map_det (S.Ahat - x • S.Ihat)
  rw [RingHom.mapMatrix_apply] at e
  change ((S.Ahat - x • S.Ihat).det : ℂ) = ((S.Ahat - x • S.Ihat).map Complex.ofReal).det at e
  rw [e]
  congr 1
  ext a b
  simp

/-- Woodford (2003), App. G.1, (G.1): a root `μ` of (1.15) has a complex eigenvector,
`A u = μ Î u`, `u ≠ 0`. -/
theorem exists_pencil_eigvec (S : LinearRESystem ιZ ιz) {μ : ℂ} (h : S.pencilPoly.eval μ = 0) :
    ∃ w : ιZ ⊕ ιz → ℂ, w ≠ 0 ∧
      S.Ahat.map Complex.ofReal *ᵥ w = μ • (S.Ihat.map Complex.ofReal *ᵥ w) := by
  rw [pencilPoly_eval] at h
  obtain ⟨w, hw0, hw⟩ := exists_mulVec_eq_zero_iff.mpr h
  refine ⟨w, hw0, ?_⟩
  rw [sub_mulVec, sub_eq_zero, smul_mulVec] at hw
  exact hw

/-- Woodford (2003), App. G.1, (G.1) and fn 2: a real root of (1.15) has a real eigenvector. -/
theorem exists_pencil_eigvec_real (S : LinearRESystem ιZ ιz) {x : ℝ}
    (h : S.pencilPoly.eval (x : ℂ) = 0) :
    ∃ v : ιZ ⊕ ιz → ℝ, v ≠ 0 ∧ S.Ahat *ᵥ v = x • (S.Ihat *ᵥ v) := by
  rw [pencilPoly_eval, det_pencil_ofReal] at h
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.mpr (Complex.ofReal_eq_zero.mp h)
  refine ⟨v, hv0, ?_⟩
  rw [sub_mulVec, sub_eq_zero, smul_mulVec] at hv
  exact hv

/-- Woodford (2003), App. G.1 (the shift that turns the pencil into an ordinary eigenproblem):
if `det(A − sÎ) ≠ 0`, `μ ≠ s` and `A u = μ Î u`, then `u` is an eigenvector of
`N = (A − sÎ)⁻¹ Î` with eigenvalue `(μ − s)⁻¹`. -/
theorem shift_eigvec {κ : Type*} [Fintype κ] [DecidableEq κ] {A I : Matrix κ κ ℂ} {s μ : ℂ}
    (hs : (A - s • I).det ≠ 0) (hμ : μ ≠ s) {u : κ → ℂ} (hu : A *ᵥ u = μ • (I *ᵥ u)) :
    ((A - s • I)⁻¹ * I) *ᵥ u = (μ - s)⁻¹ • u := by
  have hu' : (A - s • I) *ᵥ u = (μ - s) • (I *ᵥ u) := by
    rw [sub_mulVec, hu, smul_mulVec, sub_smul]
  have hI : I *ᵥ u = (μ - s)⁻¹ • ((A - s • I) *ᵥ u) := by
    rw [hu', smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hμ), one_smul]
  rw [← mulVec_mulVec, hI, mulVec_smul, mulVec_mulVec, nonsing_inv_mul _ (Ne.isUnit hs),
    one_mulVec]

/-- Woodford (2003), App. G.1: a matrix with columns `col c` satisfies `A J = Î J Ψ` when each
column satisfies `A col_c = Î ∑_{c'} Ψ_{c'c} col_{c'}`. -/
theorem deflate_of_cols {n κ : Type*} [Fintype n] [Fintype κ] (A I : Matrix n n ℝ)
    (col : κ → n → ℝ) (Ψ : Matrix κ κ ℝ)
    (h : ∀ c, A *ᵥ col c = I *ᵥ ∑ c', Ψ c' c • col c') :
    A * Matrix.of (fun a c => col c a) = I * Matrix.of (fun a c => col c a) * Ψ := by
  ext a c
  have h1 := congrFun (h c) a
  have lhs : (A * Matrix.of (fun a c => col c a)) a c = (A *ᵥ col c) a := by
    simp [mul_apply, mulVec, dotProduct]
  have rhs : (I * Matrix.of (fun a c => col c a) * Ψ) a c =
      (I *ᵥ ∑ c', Ψ c' c • col c') a := by
    simp only [mul_apply, of_apply, mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c' _ => by ring
  rw [lhs, rhs, h1]

/-! ### The construction -/

namespace Construction

/-- Woodford (2003), Assumption 8.2 (i): the selected real nonzero roots. -/
noncomputable def RS (sel : Multiset ℂ) : Finset ℂ := sel.toFinset.filter (fun μ => μ.im = 0)

/-- Woodford (2003), Assumption 8.2 (i): one representative (positive imaginary part) of each
selected complex-conjugate pair. -/
noncomputable def US (sel : Multiset ℂ) : Finset ℂ := sel.toFinset.filter (fun μ => 0 < μ.im)

/-- Woodford (2003), Assumption 8.2 (i): a conjugation-closed selection without repetitions has
`#real + 2 · #pairs` elements. -/
theorem card_sel {sel : Multiset ℂ} (hnd : sel.Nodup) (hc : ConjClosed sel) :
    Multiset.card sel = (RS sel).card + 2 * (US sel).card := by
  rw [← Multiset.toFinset_card_of_nodup hnd,
    ← Finset.card_filter_add_card_filter_not (s := sel.toFinset) (fun μ : ℂ => μ.im = 0)]
  rw [← Finset.card_filter_add_card_filter_not (s := sel.toFinset.filter
    (fun μ : ℂ => ¬ μ.im = 0)) (fun μ : ℂ => 0 < μ.im), Finset.filter_filter,
    Finset.filter_filter]
  have h1 : sel.toFinset.filter (fun μ : ℂ => ¬ μ.im = 0 ∧ 0 < μ.im) = US sel := by
    unfold US
    congr 1
    funext μ
    apply propext
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h.ne', h⟩
  have h2 : (sel.toFinset.filter (fun μ : ℂ => ¬ μ.im = 0 ∧ ¬ 0 < μ.im)).card =
      (US sel).card := by
    refine Finset.card_bij' (fun a _ => starRingEnd ℂ a) (fun a _ => starRingEnd ℂ a)
      ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Multiset.mem_toFinset] at ha
      simp only [US, Finset.mem_filter, Multiset.mem_toFinset, Complex.conj_im]
      refine ⟨hc.conj_mem ha.1, ?_⟩
      have := ha.2.1
      have := ha.2.2
      push Not at *
      exact neg_pos.mpr (lt_of_le_of_ne (by assumption) (by assumption))
    · intro a ha
      simp only [US, Finset.mem_filter, Multiset.mem_toFinset] at ha
      simp only [Finset.mem_filter, Multiset.mem_toFinset, Complex.conj_im]
      refine ⟨hc.conj_mem ha.1, by linarith [ha.2], by linarith [ha.2]⟩
    · intro a _
      simp
    · intro a _
      simp
  rw [h1, h2, RS]
  ring

/-- Woodford (2003), App. G.1 (G.1): the chosen eigenvectors — real eigenvectors of the real
selected roots, complex eigenvectors of one root of each selected pair, and a basis of `ker A`
(the zero root, `n − rank A` times). -/
structure EigenData (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) where
  vR : RS sel → ιZ ⊕ ιz → ℝ
  vR_ne : ∀ r, vR r ≠ 0
  vR_eig : ∀ r, S.Ahat *ᵥ vR r = (r : ℂ).re • (S.Ihat *ᵥ vR r)
  wU : US sel → ιZ ⊕ ιz → ℂ
  wU_ne : ∀ u, wU u ≠ 0
  wU_eig : ∀ u, S.Ahat.map Complex.ofReal *ᵥ wU u = (u : ℂ) • (S.Ihat.map Complex.ofReal *ᵥ wU u)
  kv : Fin (Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank) → ιZ ⊕ ιz → ℝ
  kv_ind : LinearIndependent ℝ kv
  kv_ker : ∀ i, S.Ahat *ᵥ kv i = 0

/-- Woodford (2003), App. G.1: the eigenvectors exist when every selected root is a root of
(1.15) and Assumption 8.3 supplies the kernel basis. -/
theorem exists_eigenData {S : LinearRESystem ιZ ιz} {sel : Multiset ℂ}
    (hroot : ∀ μ ∈ sel, S.pencilPoly.eval μ = 0) (h83 : Assumption83 S) :
    Nonempty (EigenData S sel) := by
  have hR : ∀ r : RS sel, ∃ v : ιZ ⊕ ιz → ℝ, v ≠ 0 ∧
      S.Ahat *ᵥ v = (r : ℂ).re • (S.Ihat *ᵥ v) := by
    intro r
    have hr := r.2
    simp only [RS, Finset.mem_filter, Multiset.mem_toFinset] at hr
    have he : ((r : ℂ).re : ℂ) = r := Complex.ext (by simp) (by simp [hr.2])
    exact exists_pencil_eigvec_real S (by rw [he]; exact hroot _ hr.1)
  have hU : ∀ u : US sel, ∃ w : ιZ ⊕ ιz → ℂ, w ≠ 0 ∧
      S.Ahat.map Complex.ofReal *ᵥ w = (u : ℂ) • (S.Ihat.map Complex.ofReal *ᵥ w) := by
    intro u
    have hu := u.2
    simp only [US, Finset.mem_filter, Multiset.mem_toFinset] at hu
    exact exists_pencil_eigvec S (hroot _ hu.1)
  choose vR hvR0 hvR using hR
  choose wU hwU0 hwU using hU
  obtain ⟨kv, hkv, hker⟩ := h83.kerA
  exact ⟨⟨vR, hvR0, hvR, wU, hwU0, hwU, kv, hkv, hker⟩⟩

variable {S : LinearRESystem ιZ ιz} {sel : Multiset ℂ}

/-- Woodford (2003), App. G.1: the index set of the columns of `J`: real roots, the real and
imaginary parts of each selected complex pair, and the kernel of `A`. -/
abbrev Col (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) : Type :=
  RS sel ⊕ (Fin 2 × US sel) ⊕ Fin (Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank)

/-- Woodford (2003), App. G.1 and fn 2, p. 717: the real columns of `J`. -/
noncomputable def col (E : EigenData S sel) : Col S sel → ιZ ⊕ ιz → ℝ
  | Sum.inl r => E.vR r
  | Sum.inr (Sum.inl (i, u)) =>
    if i = 0 then fun a => (E.wU u a).re else fun a => (E.wU u a).im
  | Sum.inr (Sum.inr j) => E.kv j

/-- Woodford (2003), fn 2, p. 717: the real `2 × 2` block of a complex pair `μ = a + ib`. -/
noncomputable def rot (μ : ℂ) : Matrix (Fin 2) (Fin 2) ℝ := !![μ.re, μ.im; -μ.im, μ.re]

/-- Woodford (2003), App. G.1, (G.4): the block-diagonal `Ψ`. -/
noncomputable def PsiC (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) :
    Matrix (Col S sel) (Col S sel) ℝ :=
  fromBlocks (diagonal fun r : RS sel => (r : ℂ).re) 0 0
    (fromBlocks (blockDiagonal fun u : US sel => rot (u : ℂ)) 0 0 0)

/-- Woodford (2003), App. G.1: the real and imaginary parts of a complex eigenvector,
`A x = Î (a x − b y)`, `A y = Î (b x + a y)` for `A w = μ Î w`, `w = x + iy`, `μ = a + ib`. -/
theorem reim_eig {μ : ℂ} {w : ιZ ⊕ ιz → ℂ}
    (h : S.Ahat.map Complex.ofReal *ᵥ w = μ • (S.Ihat.map Complex.ofReal *ᵥ w)) :
    S.Ahat *ᵥ (fun a => (w a).re) =
        S.Ihat *ᵥ (μ.re • (fun a => (w a).re) - μ.im • (fun a => (w a).im)) ∧
      S.Ahat *ᵥ (fun a => (w a).im) =
        S.Ihat *ᵥ (μ.im • (fun a => (w a).re) + μ.re • (fun a => (w a).im)) := by
  have hre : ∀ i, (S.Ahat *ᵥ fun a => (w a).re) i =
      μ.re * (S.Ihat *ᵥ fun a => (w a).re) i - μ.im * (S.Ihat *ᵥ fun a => (w a).im) i := by
    intro i
    have h1 := congrArg Complex.re (congrFun h i)
    simpa [mulVec, dotProduct, Complex.re_sum, Complex.im_sum, Complex.mul_re,
      Complex.mul_im] using h1
  have him : ∀ i, (S.Ahat *ᵥ fun a => (w a).im) i =
      μ.im * (S.Ihat *ᵥ fun a => (w a).re) i + μ.re * (S.Ihat *ᵥ fun a => (w a).im) i := by
    intro i
    have h1 := congrArg Complex.im (congrFun h i)
    simp [mulVec, dotProduct, Complex.re_sum, Complex.im_sum, Complex.mul_re,
      Complex.mul_im] at h1 ⊢
    linarith
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · rw [mulVec_sub, mulVec_smul, mulVec_smul, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul]
    exact hre i
  · rw [mulVec_add, mulVec_smul, mulVec_smul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul]
    exact him i

/-- Woodford (2003), (G.4): column `r` (a real root) of `J Ψ` is `μ_r` times column `r`. -/
theorem sum_PsiC_inl (E : EigenData S sel) (r : RS sel) :
    ∑ c', PsiC S sel c' (Sum.inl r) • col E c' = (r : ℂ).re • col E (Sum.inl r) := by
  simp [PsiC, Fintype.sum_sum_type, diagonal_apply, ite_smul]

/-- Woodford (2003), (G.4) and fn 2: the columns of `J Ψ` for a complex pair are
`rot_{0i} x + rot_{1i} y`. -/
theorem sum_PsiC_pair (E : EigenData S sel) (i : Fin 2) (u : US sel) :
    ∑ c', PsiC S sel c' (Sum.inr (Sum.inl (i, u))) • col E c' =
      rot (u : ℂ) 0 i • col E (Sum.inr (Sum.inl (0, u))) +
        rot (u : ℂ) 1 i • col E (Sum.inr (Sum.inl (1, u))) := by
  simp [PsiC, Fintype.sum_sum_type, Fintype.sum_prod_type, blockDiagonal_apply, ite_smul,
    Fin.sum_univ_two]

/-- Woodford (2003), (G.4): the kernel columns of `J Ψ` vanish. -/
theorem sum_PsiC_ker (E : EigenData S sel)
    (j : Fin (Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank)) :
    ∑ c', PsiC S sel c' (Sum.inr (Sum.inr j)) • col E c' = 0 := by
  simp [PsiC, Fintype.sum_sum_type]

/-- Woodford (2003), App. G.1, (G.4): `A J = Î J Ψ` for the constructed real `J`, `Ψ`. -/
theorem deflate_C (E : EigenData S sel) :
    S.Ahat * Matrix.of (fun a c => col E c a) =
      S.Ihat * Matrix.of (fun a c => col E c a) * PsiC S sel := by
  refine deflate_of_cols _ _ _ _ fun c => ?_
  rcases c with r | ⟨i, u⟩ | j
  · rw [sum_PsiC_inl, mulVec_smul]
    exact E.vR_eig r
  · rw [sum_PsiC_pair]
    obtain ⟨h1, h2⟩ := reim_eig (E.wU_eig u)
    fin_cases i
    · simp only [col, rot, Fin.zero_eta, Fin.isValue, ↓reduceIte, one_ne_zero,
        of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one, neg_smul]
      rw [h1, sub_eq_add_neg]
    · simp only [col, rot, Fin.mk_one, Fin.isValue, ↓reduceIte, one_ne_zero,
        of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one]
      exact h2
  · rw [sum_PsiC_ker, mulVec_zero]
    exact E.kv_ker j

omit [DecidableEq ιZ] in
/-- Woodford (2003), (G.4): the rows of the complexified `Ψ` acting on a vector. -/
theorem mulVec_PsiC (z : Col S sel → ℂ) :
    ((PsiC S sel).map Complex.ofReal *ᵥ z) =
      Sum.elim (fun r : RS sel => ((r : ℂ).re : ℂ) * z (Sum.inl r))
        (Sum.elim (fun p : Fin 2 × US sel =>
          (rot (p.2 : ℂ) p.1 0 : ℂ) * z (Sum.inr (Sum.inl (0, p.2))) +
          (rot (p.2 : ℂ) p.1 1 : ℂ) * z (Sum.inr (Sum.inl (1, p.2)))) 0) := by
  funext c
  rcases c with r | ⟨i, u⟩ | j
  · simp only [Sum.elim_inl]
    change ∑ c', ((PsiC S sel (Sum.inl r) c' : ℝ) : ℂ) * z c' = _
    rw [Fintype.sum_eq_single (Sum.inl r)]
    · simp [PsiC]
    · intro c' hc'
      rcases c' with b | b
      · have hb : r ≠ b := fun h => hc' (h ▸ rfl)
        simp [PsiC, diagonal_apply_ne _ hb]
      · simp [PsiC]
  · simp only [Sum.elim_inr, Sum.elim_inl]
    change ∑ c', ((PsiC S sel (Sum.inr (Sum.inl (i, u))) c' : ℝ) : ℂ) * z c' = _
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [PsiC, fromBlocks_apply₂₁, fromBlocks_apply₂₂, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, Matrix.zero_apply, Complex.ofReal_zero, zero_mul,
      Finset.sum_const_zero, zero_add, add_zero, Fin.sum_univ_two]
    rw [Fintype.sum_eq_single u, Fintype.sum_eq_single u]
    · simp [blockDiagonal_apply_eq]
    · intro u' hu'
      simp [blockDiagonal_apply_ne _ _ _ (Ne.symm hu')]
    · intro u' hu'
      simp [blockDiagonal_apply_ne _ _ _ (Ne.symm hu')]
  · simp only [Sum.elim_inr, Pi.zero_apply]
    change ∑ c', ((PsiC S sel (Sum.inr (Sum.inr j)) c' : ℝ) : ℂ) * z c' = 0
    simp [PsiC, Fintype.sum_sum_type]

omit [DecidableEq ιZ] in
/-- Woodford (2003), App. G.1, (G.4): every eigenvalue of the constructed `Ψ` is zero or a
selected root (for a conjugation-closed selection). -/
theorem PsiC_eig (hc : ConjClosed sel) {μ : ℂ}
    (h : (Matrix.scalar (Col S sel) μ - (PsiC S sel).map Complex.ofReal).det = 0) :
    μ = 0 ∨ μ ∈ sel := by
  obtain ⟨z, hz0, hz⟩ := exists_eigvec h
  rw [mulVec_PsiC] at hz
  obtain ⟨c, hc0⟩ := Function.ne_iff.mp hz0
  rcases c with r | ⟨i, u⟩ | j
  · have e := congrFun hz (Sum.inl r)
    simp only [Sum.elim_inl, Pi.smul_apply, smul_eq_mul] at e
    have hμ : μ = ((r : ℂ).re : ℂ) := by
      have := mul_right_cancel₀ hc0 e
      exact this.symm
    have hr := r.2
    simp only [RS, Finset.mem_filter, Multiset.mem_toFinset] at hr
    right
    rw [hμ, show ((r : ℂ).re : ℂ) = (r : ℂ) from Complex.ext (by simp) (by simp [hr.2])]
    exact hr.1
  · have e0 := congrFun hz (Sum.inr (Sum.inl (0, u)))
    have e1 := congrFun hz (Sum.inr (Sum.inl (1, u)))
    simp only [Sum.elim_inr, Sum.elim_inl, Pi.smul_apply, smul_eq_mul, rot, of_apply,
      cons_val', cons_val_zero, cons_val_fin_one, cons_val_one, Fin.isValue,
      Complex.ofReal_neg] at e0 e1
    set a : ℂ := ((u : ℂ).re : ℂ)
    set b : ℂ := ((u : ℂ).im : ℂ)
    set z0 := z (Sum.inr (Sum.inl (0, u)))
    set z1 := z (Sum.inr (Sum.inl (1, u)))
    have k0 : ((μ - a) ^ 2 + b ^ 2) * z0 = 0 := by linear_combination (-(μ - a)) * e0 - b * e1
    have k1 : ((μ - a) ^ 2 + b ^ 2) * z1 = 0 := by linear_combination b * e0 - (μ - a) * e1
    have hq : (μ - a) ^ 2 + b ^ 2 = 0 := by
      fin_cases i
      · exact (mul_eq_zero.mp k0).resolve_right hc0
      · exact (mul_eq_zero.mp k1).resolve_right hc0
    have hfac : (μ - (u : ℂ)) * (μ - starRingEnd ℂ (u : ℂ)) = (μ - a) ^ 2 + b ^ 2 := by
      have hu : (u : ℂ) = a + b * Complex.I := (Complex.re_add_im _).symm
      have hcu : starRingEnd ℂ (u : ℂ) = a - b * Complex.I := by
        apply Complex.ext <;> simp [a, b]
      rw [hcu, hu]
      ring_nf
      rw [Complex.I_sq]
      ring
    have hu := u.2
    simp only [US, Finset.mem_filter, Multiset.mem_toFinset] at hu
    right
    rcases mul_eq_zero.mp (hfac.trans hq) with h1 | h1
    · rw [sub_eq_zero.mp h1]
      exact hu.1
    · rw [sub_eq_zero.mp h1]
      exact hc.conj_mem hu.1
  · have e := congrFun hz (Sum.inr (Sum.inr j))
    simp only [Sum.elim_inr, Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at e
    left
    exact (mul_eq_zero.mp e.symm).resolve_right hc0

/-- Woodford (2003), App. G.1: a real shift `s ≠ 0` that is not a root of (1.15) (the
polynomial is nonzero, so it has finitely many roots). -/
theorem exists_shift (hreg : S.pencilPoly ≠ 0) :
    ∃ s : ℝ, s ≠ 0 ∧ S.pencilPoly.eval (s : ℂ) ≠ 0 := by
  obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset
    (S.pencilPoly.roots.toFinset.image Complex.re ∪ {0})
  refine ⟨s, fun h => hs (by simp [h]), fun h => hs ?_⟩
  have hm : (s : ℂ) ∈ S.pencilPoly.roots := (Polynomial.mem_roots hreg).mpr h
  exact Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨(s : ℂ), Multiset.mem_toFinset.mpr hm, by simp⟩)

/-- Woodford (2003), App. G.1: the selected root behind each complex eigenvector of the
construction (a real root, a root `u` of a pair, or its conjugate). -/
noncomputable def μf : RS sel ⊕ (US sel × Bool) → ℂ
  | Sum.inl r => (r : ℂ)
  | Sum.inr (u, false) => (u : ℂ)
  | Sum.inr (u, true) => starRingEnd ℂ (u : ℂ)

/-- Woodford (2003), App. G.1, (G.1): the complex eigenvectors of the construction. -/
noncomputable def famE (E : EigenData S sel) : RS sel ⊕ (US sel × Bool) → ιZ ⊕ ιz → ℂ
  | Sum.inl r => fun a => (E.vR r a : ℂ)
  | Sum.inr (u, false) => E.wU u
  | Sum.inr (u, true) => fun a => starRingEnd ℂ (E.wU u a)

omit [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), App. G.1: the roots behind distinct eigenvectors are distinct. -/
theorem μf_injective : Function.Injective (μf (sel := sel)) := by
  have hR : ∀ r : RS sel, (r : ℂ).im = 0 := fun r => by
    have hr := r.2
    simp only [RS, Finset.mem_filter] at hr
    exact hr.2
  have hU : ∀ u : US sel, 0 < (u : ℂ).im := fun u => by
    have hu := u.2
    simp only [US, Finset.mem_filter] at hu
    exact hu.2
  intro p q h
  have him := congrArg Complex.im h
  rcases p with r | ⟨u, _ | _⟩ <;> rcases q with r' | ⟨u', _ | _⟩ <;>
    simp only [μf, Complex.conj_im] at h him
  · exact congrArg Sum.inl (Subtype.ext h)
  · linarith [hR r, hU u']
  · linarith [hR r, hU u']
  · linarith [hU u, hR r']
  · exact congrArg (fun x => Sum.inr (x, false)) (Subtype.ext h)
  · linarith [hU u, hU u']
  · linarith [hR r', hU u]
  · linarith [hU u, hU u']
  · exact congrArg (fun x => Sum.inr (x, true)) (Subtype.ext ((starRingEnd ℂ).injective h))

/-- Woodford (2003), App. G.1: the complex eigenvectors are nonzero and satisfy
`A u = μ Î u` for their root `μ` (real roots, `u`, and `ū` with the conjugate eigenvector). -/
theorem famE_eig (E : EigenData S sel) (p : RS sel ⊕ (US sel × Bool)) :
    famE E p ≠ 0 ∧ S.Ahat.map Complex.ofReal *ᵥ famE E p =
      μf p • (S.Ihat.map Complex.ofReal *ᵥ famE E p) := by
  rcases p with r | ⟨u, _ | _⟩
  · refine ⟨fun h0 => E.vR_ne r (funext fun a => ?_), ?_⟩
    · have := congrFun h0 a
      simp only [famE, Pi.zero_apply, Complex.ofReal_eq_zero] at this
      exact this
    have hr := r.2
    simp only [RS, Finset.mem_filter] at hr
    have hre : ((r : ℂ).re : ℂ) = (r : ℂ) := Complex.ext (by simp) (by simp [hr.2])
    simp only [famE, μf]
    rw [map_mulVec_ofReal, map_mulVec_ofReal, E.vR_eig r]
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, hre]
  · exact ⟨E.wU_ne u, E.wU_eig u⟩
  · refine ⟨fun h0 => E.wU_ne u (funext fun a => ?_), ?_⟩
    · have := congrFun h0 a
      simp only [famE, Pi.zero_apply, map_eq_zero] at this
      exact this
    · simp only [famE, μf]
      rw [map_mulVec_conj, map_mulVec_conj, E.wU_eig u]
      funext a
      simp [map_mul]

/-- Woodford (2003), fn 2, p. 717: real coefficients of `Re w`, `Im w` in terms of complex
coefficients of `w`, `w̄`. -/
theorem pair_combo (g0 g1 : ℝ) (w : ℂ) :
    ((g0 : ℂ) + Complex.I * g1) / 2 * starRingEnd ℂ w + ((g0 : ℂ) - Complex.I * g1) / 2 * w =
      ((g0 * w.re + g1 * w.im : ℝ) : ℂ) := by
  apply Complex.ext <;> simp <;> ring

/-- Woodford (2003), App. G.1, p. 716–717 (Assumption 8.3 "implies ... linearly independent
vectors"): the real columns of `J` — real eigenvectors, real and imaginary parts of complex
eigenvectors, and the kernel basis — are linearly independent. Proof: they are real
combinations of eigenvectors of `N = (A − sÎ)⁻¹ Î` for distinct eigenvalues `(μ − s)⁻¹`, the
kernel vectors all belonging to `(0 − s)⁻¹`. -/
theorem col_indep (hc : ConjClosed sel) (hsel : ∀ μ ∈ sel, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0)
    (hreg : S.pencilPoly ≠ 0) (E : EigenData S sel) : LinearIndependent ℝ (col E) := by
  obtain ⟨s, hs0, hs⟩ := exists_shift hreg
  have hdet : (S.Ahat.map Complex.ofReal - (s : ℂ) • S.Ihat.map Complex.ofReal).det ≠ 0 := by
    rw [← pencilPoly_eval]
    exact hs
  set f := Matrix.toLin' ((S.Ahat.map Complex.ofReal - (s : ℂ) • S.Ihat.map Complex.ofReal)⁻¹ *
    S.Ihat.map Complex.ofReal) with hf
  have hmem : ∀ p : RS sel ⊕ (US sel × Bool), μf p ∈ sel := by
    intro p
    rcases p with r | ⟨u, _ | _⟩
    · have hr := r.2
      simp only [RS, Finset.mem_filter, Multiset.mem_toFinset] at hr
      exact hr.1
    · have hu := u.2
      simp only [US, Finset.mem_filter, Multiset.mem_toFinset] at hu
      exact hu.1
    · have hu := u.2
      simp only [US, Finset.mem_filter, Multiset.mem_toFinset] at hu
      exact hc.conj_mem hu.1
  have hEv : ∀ p : RS sel ⊕ (US sel × Bool), f (famE E p) = (μf p - s)⁻¹ • famE E p := by
    intro p
    rw [hf, Matrix.toLin'_apply]
    refine shift_eigvec hdet (fun h => hs ?_) (famE_eig E p).2
    rw [← h]
    exact (hsel _ (hmem p)).2
  have hinj : Function.Injective fun p => (μf (sel := sel) p - s)⁻¹ := by
    intro p q h
    exact μf_injective (sub_left_injective (inv_injective h))
  have hE : LinearIndependent ℂ (famE E) :=
    Module.End.eigenvectors_linearIndependent' f _ hinj (famE E) fun p =>
      Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr (hEv p), (famE_eig E p).1⟩
  set famK : Fin (Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank) → ιZ ⊕ ιz → ℂ :=
    fun j a => (E.kv j a : ℂ) with hfamK
  have hK : LinearIndependent ℂ famK := linearIndependent_ofReal E.kv_ind
  have hs0c : (0 : ℂ) ≠ (s : ℂ) := fun h => hs0 (Complex.ofReal_eq_zero.mp h.symm)
  have hKv : ∀ j, f (famK j) = ((0 : ℂ) - s)⁻¹ • famK j := by
    intro j
    rw [hf, Matrix.toLin'_apply]
    refine shift_eigvec hdet hs0c ?_
    rw [hfamK, map_mulVec_ofReal, E.kv_ker j, zero_smul]
    funext a
    simp
  set ν0 : ℂ := ((0 : ℂ) - s)⁻¹ with hν0
  have hspanK : Submodule.span ℂ (Set.range famK) ≤ Module.End.eigenspace f ν0 := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Module.End.mem_eigenspace_iff.mpr (hKv j)
  have hspanE : Submodule.span ℂ (Set.range (famE E)) ≤
      ⨆ (ν : ℂ) (_ : ν ≠ ν0), Module.End.eigenspace f ν := by
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    have hne : (μf p - s)⁻¹ ≠ ν0 := fun h =>
      (hsel _ (hmem p)).1 (sub_left_injective (inv_injective h))
    exact (le_iSup₂_of_le ((μf p - s)⁻¹) hne le_rfl :
      Module.End.eigenspace f ((μf p - s)⁻¹) ≤ _) (Module.End.mem_eigenspace_iff.mpr (hEv p))
  have hdisj := (Module.End.eigenspaces_iSupIndep f) ν0
  have hfam : LinearIndependent ℂ (Sum.elim (famE E) famK) :=
    hE.sum_type hK (Disjoint.mono hspanE hspanK hdisj.symm)
  rw [Fintype.linearIndependent_iff]
  intro g hg c
  set h : (RS sel ⊕ (US sel × Bool)) ⊕ Fin (Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank) → ℂ :=
    Sum.elim (Sum.elim (fun r => (g (Sum.inl r) : ℂ)) (fun q => if q.2 then
      ((g (Sum.inr (Sum.inl (0, q.1))) : ℂ) + Complex.I * g (Sum.inr (Sum.inl (1, q.1)))) / 2
      else ((g (Sum.inr (Sum.inl (0, q.1))) : ℂ) -
        Complex.I * g (Sum.inr (Sum.inl (1, q.1)))) / 2))
      (fun j => (g (Sum.inr (Sum.inr j)) : ℂ)) with hh
  have hsum : ∑ x, h x • Sum.elim (famE E) famK x = 0 := by
    funext a
    have hga := congrFun hg a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hga ⊢
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type] at hga ⊢
    simp only [Fin.sum_univ_two, Fintype.sum_bool] at hga ⊢
    have hpair : ∀ u : US sel,
        h (Sum.inl (Sum.inr (u, true))) * Sum.elim (famE E) famK (Sum.inl (Sum.inr (u, true))) a +
          h (Sum.inl (Sum.inr (u, false))) *
            Sum.elim (famE E) famK (Sum.inl (Sum.inr (u, false))) a =
        ((g (Sum.inr (Sum.inl (0, u))) * col E (Sum.inr (Sum.inl (0, u))) a +
          g (Sum.inr (Sum.inl (1, u))) * col E (Sum.inr (Sum.inl (1, u))) a : ℝ) : ℂ) := by
      intro u
      simp only [hh, Sum.elim_inl, Sum.elim_inr, ↓reduceIte, Bool.false_eq_true, famE, col,
        Fin.isValue, one_ne_zero]
      exact pair_combo _ _ _
    simp only [hpair]
    have hcast : ((∑ x : RS sel, g (Sum.inl x) * col E (Sum.inl x) a +
        ((∑ y : US sel, g (Sum.inr (Sum.inl (0, y))) * col E (Sum.inr (Sum.inl (0, y))) a) +
          ∑ y : US sel, g (Sum.inr (Sum.inl (1, y))) * col E (Sum.inr (Sum.inl (1, y))) a) +
        ∑ j, g (Sum.inr (Sum.inr j)) * col E (Sum.inr (Sum.inr j)) a : ℝ) : ℂ) = 0 := by
      rw [add_assoc, hga]
      simp
    rw [← hcast]
    push_cast
    simp only [hh, Sum.elim_inl, Sum.elim_inr, famE, col, hfamK, Finset.sum_add_distrib]
  have h0 := Fintype.linearIndependent_iff.mp hfam h hsum
  rcases c with r | ⟨i, u⟩ | j
  · have := h0 (Sum.inl (Sum.inl r))
    simpa [hh] using this
  · have hf0 := h0 (Sum.inl (Sum.inr (u, false)))
    have ht0 := h0 (Sum.inl (Sum.inr (u, true)))
    simp only [hh, Sum.elim_inl, Sum.elim_inr, ↓reduceIte, Bool.false_eq_true] at hf0 ht0
    have hg0 : (g (Sum.inr (Sum.inl (0, u))) : ℂ) = 0 := by linear_combination hf0 + ht0
    have hg1 : Complex.I * (g (Sum.inr (Sum.inl (1, u))) : ℂ) = 0 := by
      linear_combination ht0 - hf0
    fin_cases i
    · exact_mod_cast hg0
    · have := (mul_eq_zero.mp hg1).resolve_left Complex.I_ne_zero
      exact_mod_cast this
  · have := h0 (Sum.inr j)
    simpa [hh] using this

end Construction

open Construction

/-- Woodford (2003), App. G.1, pp. 716–718 (from Assumption 8.2 to (G.4)): **under Assumption
8.2 with a conjugation-closed selection (case (i)) and Assumption 8.3 there is a real
`n × n_Z` matrix `J` with independent columns and `Ψ` with `A J = Î J Ψ`, every eigenvalue of
`Ψ` being zero or a selected root.** (The columns are the real eigenvectors, the real and
imaginary parts of complex eigenvectors, fn 2, and a basis of `ker A`.) -/
theorem exists_realSelection {S : LinearRESystem ιZ ιz} {β : ℝ} (h82 : Assumption82 S β)
    (hi : ConjClosed h82.sel) (h83 : Assumption83 S) : Nonempty (RealSelection S h82.sel) := by
  set sel := h82.sel with hsel_def
  have hsel : ∀ μ ∈ sel, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0 := by
    intro μ hμ
    have := Multiset.mem_of_le h82.sel_le hμ
    rw [Multiset.mem_filter, Polynomial.mem_roots h83.regular] at this
    exact ⟨this.2.1, this.1⟩
  have hnd : sel.Nodup := by
    refine Multiset.nodup_of_le (h82.sel_le.trans ?_) h83.nodup
    exact Multiset.monotone_filter_right _ fun μ h => h.1
  obtain ⟨E⟩ := exists_eigenData (fun μ hμ => (hsel μ hμ).2) h83 (sel := sel)
  have hcard : Fintype.card (Col S sel) = Fintype.card ιZ := by
    change Fintype.card (RS sel ⊕ (Fin 2 × US sel) ⊕
      Fin (Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank)) = _
    rw [Fintype.card_sum (α := RS sel), Fintype.card_sum (α := Fin 2 × US sel),
      Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_coe, Fintype.card_coe,
      ← h82.sel_card, card_sel hnd hi]
    ring
  let e : Col S sel ≃ ιZ := Fintype.equivOfCardEq hcard
  set Jc : Matrix (ιZ ⊕ ιz) (Col S sel) ℝ := Matrix.of fun a c => col E c a with hJc
  refine ⟨⟨Jc.submatrix id e.symm, (PsiC S sel).submatrix e.symm e.symm, ?_, ?_, ?_⟩⟩
  · have h1 : S.Ahat * Jc.submatrix id e.symm = (S.Ahat * Jc).submatrix id e.symm := by
      rw [← submatrix_mul_equiv (e₂ := Equiv.refl _), Equiv.coe_refl, submatrix_id_id]
    have h2 : S.Ihat * Jc.submatrix id e.symm * (PsiC S sel).submatrix e.symm e.symm =
        (S.Ihat * Jc * PsiC S sel).submatrix id e.symm := by
      rw [← submatrix_mul_equiv (e₂ := e.symm), ← submatrix_mul_equiv (e₂ := Equiv.refl _),
        Equiv.coe_refl, submatrix_id_id]
    rw [h1, h2, hJc, deflate_C E]
  · have : (Jc.submatrix id e.symm)ᵀ = col E ∘ e.symm := by
      funext i a
      rfl
    rw [this]
    exact (col_indep hi hsel h83.regular E).comp _ e.symm.injective
  · intro μ hμ
    have heq : Matrix.scalar ιZ μ - ((PsiC S sel).submatrix e.symm e.symm).map Complex.ofReal =
        (Matrix.scalar (Col S sel) μ - (PsiC S sel).map Complex.ofReal).submatrix e.symm
          e.symm := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.scalar_apply]
      · have : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
        simp [Matrix.scalar_apply, diagonal_apply_ne _ hij, diagonal_apply_ne _ this]
    rw [heq, det_submatrix_equiv_self] at hμ
    exact PsiC_eig hi hμ

/-! ### The kernel clauses of Assumption 8.3 are automatic -/

/-- Woodford (2003), App. G.1 (rank–nullity): every real matrix has `#columns − rank`
independent vectors in its kernel. -/
theorem exists_ker_basis {m n : Type*} [Fintype n] (M : Matrix m n ℝ) {k : ℕ}
    (hk : Fintype.card n - M.rank = k) :
    ∃ u : Fin k → n → ℝ, LinearIndependent ℝ u ∧ ∀ i, M *ᵥ u i = 0 := by
  subst hk
  set K := LinearMap.ker M.mulVecLin with hK
  have hdim : Module.finrank ℝ K = Fintype.card n - M.rank := by
    have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at this
    change M.rank + Module.finrank ℝ K = _ at this
    omega
  let b := Module.finBasisOfFinrankEq ℝ K hdim
  refine ⟨fun i => (b i : n → ℝ), ?_, fun i => (b i).2⟩
  exact b.linearIndependent.map' K.subtype (Submodule.ker_subtype K)

/-- Woodford (2003), Assumption 8.3, App. G.1, p. 716: the four kernel clauses (`n − rank A`
independent `uᵢ` with `A uᵢ = 0` and `fᵢ` with `fᵢ' A = 0`; `n_z − rank Ẽ` independent `eⱼ` with
`eⱼ' Î = 0` and `hⱼ` with `Î hⱼ = 0`) **hold for every system** (rank–nullity); only the root
clauses of Assumption 8.3 restrict the model. -/
theorem assumption83_kernels (S : LinearRESystem ιZ ιz) :
    KerA S ∧ KerALeft S ∧ KerILeft S ∧ KerI S := by
  have hlift : ∀ {k : ℕ} (v : Fin k → ιz → ℝ), LinearIndependent ℝ v →
      LinearIndependent ℝ (fun j => (Sum.elim 0 (v j) : ιZ ⊕ ιz → ℝ)) := by
    intro k v hv
    rw [Fintype.linearIndependent_iff] at hv ⊢
    intro g hg j
    refine hv g (funext fun r => ?_) j
    have := congrFun hg (Sum.inr r)
    simpa [Finset.sum_apply] using this
  refine ⟨exists_ker_basis S.Ahat rfl, ?_, ?_, ?_⟩
  · obtain ⟨f, hf, hf0⟩ := exists_ker_basis S.Ahatᵀ (by rw [rank_transpose])
    exact ⟨f, hf, fun i => by rw [← mulVec_transpose]; exact hf0 i⟩
  · obtain ⟨v, hv, hv0⟩ := exists_ker_basis S.Etᵀ (by rw [rank_transpose])
    refine ⟨fun j => Sum.elim 0 (v j), hlift v hv, fun j => ?_⟩
    rw [← mulVec_transpose, LinearRESystem.Ihat, fromBlocks_transpose, fromBlocks_mulVec]
    funext a
    rcases a with i | r
    · simp
    · have := congrFun (hv0 j) r
      simpa using this
  · obtain ⟨v, hv, hv0⟩ := exists_ker_basis S.Et rfl
    refine ⟨fun j => Sum.elim 0 (v j), hlift v hv, fun j => ?_⟩
    rw [LinearRESystem.Ihat, fromBlocks_mulVec]
    funext a
    rcases a with i | r
    · simp
    · have := congrFun (hv0 j) r
      simpa using this

/-- Woodford (2003), Assumption 8.3: it is equivalent to its root clauses (a nonzero
polynomial (1.15) with `rank Ẽ + rank A − n_z` distinct nonzero roots). -/
theorem Assumption83.ofRoots (S : LinearRESystem ιZ ιz) (hreg : S.pencilPoly ≠ 0)
    (hnd : (nonzeroRoots S).Nodup)
    (hcard : Multiset.card (nonzeroRoots S) = S.Et.rank + S.Ahat.rank - Fintype.card ιz) :
    Nonempty (Assumption83 S) :=
  ⟨⟨hreg, hnd, hcard, (assumption83_kernels S).1, (assumption83_kernels S).2.1,
    (assumption83_kernels S).2.2.1, (assumption83_kernels S).2.2.2⟩⟩

end Woodford.OptimalPolicyRules.PencilEigen
