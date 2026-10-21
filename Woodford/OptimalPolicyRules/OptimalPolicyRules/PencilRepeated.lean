/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.PencilAssumptions
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Proposition 8.1 with repeated roots: generalised eigenspaces of the pencil

Woodford (2003), *Interest and Prices*, Chapter 8, Assumption 8.2 (p. 552) and Appendix G.1
(pp. 716–718), without the distinct-root condition of Assumption 8.3.

The real deflating pair `A J = Î J Ψ` of (G.4) is built from **generalised** eigenvectors, so no
diagonalisability is needed. With a real shift `s ≠ 0` that is not a root of (1.15) and the real
matrix `N = (A − sÎ)⁻¹ Î`:

* `pencil_roots_eq`: the roots of (1.15) are exactly `s + ν⁻¹` for the nonzero eigenvalues `ν`
  of `N`, with multiplicity (`det(A − μÎ) = det(A − sÎ) · det(I − (μ − s)N)`); so a root `μ` has
  the multiplicity of the eigenvalue `(μ − s)⁻¹` of `N` (`count_pencil_roots`).
* `W`: the complex `N`-invariant subspace spanned by the eigenvectors of `−1/s` (that is,
  `ker A`, the zero roots counted `n − rank A` times) and the generalised eigenspaces of
  `(μ − s)⁻¹` for the selected nonzero roots `μ`; it is closed under conjugation, so its real
  part `realPart W` has the same dimension (`finrank_realPart`, real descent).
* `exists_deflating_cols`: the same for any number of columns
  (`#κ = (n − rank A) + #sel`), used for case (ii) in `Prop81CaseII`.
* `exists_realSelection_general`: under Assumption 8.2 with a conjugation-closed selection that
  takes **whole root classes** (`SelWhole`: each selected root with its full multiplicity) and a
  nonzero (1.15), a real deflating pair exists; `selWhole_of_assumption83` shows that distinct
  roots (Assumption 8.3) give `SelWhole`, so `PencilEigen.exists_realSelection` is the special
  case.
* `prop81_of_assumptions_general`, `prop82_of_assumptions_general`: Propositions 8.1 and 8.2
  under Assumptions 8.1, 8.2 (case (i), whole classes), 8.4, 8.5 and a nonzero (1.15), with no
  distinctness assumption (`PencilAssumptions.prop81_of_assumptions` is the distinct-root case,
  via `selWhole_of_assumption83`).

The dimension count of a finite sum of independent subspaces (`PencilEigen.finrank_finset_sup`)
and the real-descent pattern are restated from the Woodford Chapter 4 project
(`InvariantSplit.finrank_finset_sup`, `finrank_boundedOrbitsC_le`).
-/

namespace Woodford.OptimalPolicyRules.PencilRepeated

open Matrix Polynomial GeneralSetup PencilSplit PencilEigen PencilAssumptions
  GeneralFOC.Selection

variable {ιZ ιz : Type*} [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz]

/-! ### The shifted matrix `N = (A − sÎ)⁻¹ Î` -/

/-- Woodford (2003), App. G.1 (the shift): `N = (A − sÎ)⁻¹ Î` (real). -/
noncomputable def Nr (S : LinearRESystem ιZ ιz) (s : ℝ) : Matrix (ιZ ⊕ ιz) (ιZ ⊕ ιz) ℝ :=
  (S.Ahat - s • S.Ihat)⁻¹ * S.Ihat

/-- Woodford (2003), App. G.1: `(A − sÎ) N = Î` when `A − sÎ` is invertible. -/
theorem shift_mul_Nr (S : LinearRESystem ιZ ιz) {s : ℝ} (hs : (S.Ahat - s • S.Ihat).det ≠ 0) :
    (S.Ahat - s • S.Ihat) * Nr S s = S.Ihat := by
  rw [Nr, ← Matrix.mul_assoc, mul_nonsing_inv _ (Ne.isUnit hs), Matrix.one_mul]

/-- Woodford (2003), App. G.1: the complexified identity `(A − sÎ) N = Î`. -/
theorem shift_mul_Nc (S : LinearRESystem ιZ ιz) {s : ℝ} (hs : (S.Ahat - s • S.Ihat).det ≠ 0) :
    (S.Ahat.map Complex.ofReal - (s : ℂ) • S.Ihat.map Complex.ofReal) *
      (Nr S s).map Complex.ofReal = S.Ihat.map Complex.ofReal := by
  have e : S.Ahat.map Complex.ofReal - (s : ℂ) • S.Ihat.map Complex.ofReal =
      (S.Ahat - s • S.Ihat).map Complex.ofReal := by
    ext a b
    simp
  rw [e, ← map_ofReal_mul, shift_mul_Nr S hs]

/-- Woodford (2003), App. G.1: the complexified `A − sÎ` is invertible. -/
theorem det_shift_C (S : LinearRESystem ιZ ιz) {s : ℝ} (hs : (S.Ahat - s • S.Ihat).det ≠ 0) :
    (S.Ahat.map Complex.ofReal - (s : ℂ) • S.Ihat.map Complex.ofReal).det ≠ 0 := by
  rw [det_pencil_ofReal]
  exact_mod_cast hs

/-- Woodford (2003), App. G.1: `A u = μ Î u` with `μ ≠ s` iff `N u = (μ − s)⁻¹ u` (one
direction). -/
theorem eig_to_N (S : LinearRESystem ιZ ιz) {s : ℝ} (hs : (S.Ahat - s • S.Ihat).det ≠ 0)
    {μ : ℂ} (hμ : μ ≠ s) {u : ιZ ⊕ ιz → ℂ}
    (hu : S.Ahat.map Complex.ofReal *ᵥ u = μ • (S.Ihat.map Complex.ofReal *ᵥ u)) :
    (Nr S s).map Complex.ofReal *ᵥ u = (μ - s)⁻¹ • u := by
  set M0 := S.Ahat.map Complex.ofReal - (s : ℂ) • S.Ihat.map Complex.ofReal with hM0
  have h1 : M0 *ᵥ u = (μ - s) • (M0 *ᵥ ((Nr S s).map Complex.ofReal *ᵥ u)) := by
    rw [mulVec_mulVec, shift_mul_Nc S hs, hM0, sub_mulVec, hu, smul_mulVec, sub_smul]
  have h2 : M0 *ᵥ (u - (μ - s) • ((Nr S s).map Complex.ofReal *ᵥ u)) = 0 := by
    rw [mulVec_sub, mulVec_smul, h1, sub_self]
  have h3 := sub_eq_zero.mp (eq_zero_of_mulVec_eq_zero (det_shift_C S hs) h2)
  have hne : μ - (s : ℂ) ≠ 0 := sub_ne_zero.mpr hμ
  calc (Nr S s).map Complex.ofReal *ᵥ u =
      (μ - s)⁻¹ • ((μ - s) • ((Nr S s).map Complex.ofReal *ᵥ u)) := by
        rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    _ = (μ - s)⁻¹ • u := by rw [← h3]

/-- Woodford (2003), App. G.1: `N u = ν u` with `ν ≠ 0` gives `A u = (s + ν⁻¹) Î u`. -/
theorem N_to_eig (S : LinearRESystem ιZ ιz) {s : ℝ} (hs : (S.Ahat - s • S.Ihat).det ≠ 0)
    {ν : ℂ} (hν : ν ≠ 0) {u : ιZ ⊕ ιz → ℂ} (hu : (Nr S s).map Complex.ofReal *ᵥ u = ν • u) :
    S.Ahat.map Complex.ofReal *ᵥ u = ((s : ℂ) + ν⁻¹) • (S.Ihat.map Complex.ofReal *ᵥ u) := by
  have h0 := congrArg (· *ᵥ u) (shift_mul_Nc S hs)
  rw [← mulVec_mulVec, hu, mulVec_smul, sub_mulVec, smul_mulVec] at h0
  set a := S.Ahat.map Complex.ofReal *ᵥ u
  set b := S.Ihat.map Complex.ofReal *ᵥ u
  have h2 : ν⁻¹ • b = a - (s : ℂ) • b := by
    conv_lhs => rw [← h0]
    rw [smul_smul, inv_mul_cancel₀ hν, one_smul]
  rw [add_smul, h2]
  abel

/-! ### The roots of (1.15) and the eigenvalues of `N` -/

/-- Woodford (2003), App. G.1: `det(I − xN) = ∏ (1 − x νᵢ)` over the eigenvalues of `N`. -/
theorem det_one_sub_smul {κ : Type*} [Fintype κ] [DecidableEq κ] (M : Matrix κ κ ℂ) (x : ℂ) :
    (1 - x • M).det = (M.charpoly.roots.map fun ν => 1 - x * ν).prod := by
  have hsplit : (M.charpoly.roots.map fun ν => X - C ν).prod = M.charpoly :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq (charpoly_monic M)
      (IsAlgClosed.card_roots_eq_natDegree)
  have hcard : Multiset.card M.charpoly.roots = Fintype.card κ := by
    rw [IsAlgClosed.card_roots_eq_natDegree, charpoly_natDegree_eq_dim]
  by_cases hx : x = 0
  · subst hx
    simp
  · have e : 1 - x • M = x • (Matrix.scalar κ x⁻¹ - M) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.scalar_apply]
        field_simp
      · simp [Matrix.scalar_apply, hij, Matrix.one_apply_ne hij]
    rw [e, det_smul, ← eval_charpoly]
    conv_lhs => rw [← hsplit]
    rw [eval_multiset_prod, Multiset.map_map, ← hcard]
    have hfac : ∀ ν ∈ M.charpoly.roots, 1 - x * ν = x * (eval x⁻¹ ∘ fun ν => X - C ν) ν := by
      intro ν _
      simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
      field_simp
    rw [Multiset.map_congr rfl hfac, Multiset.prod_map_mul, Multiset.map_const',
      Multiset.prod_replicate]

/-- Woodford (2003), (1.15) and App. G.1: `A − μÎ = (A − sÎ)(I − (μ − s)N)`. -/
theorem pencil_factor (S : LinearRESystem ιZ ιz) {s : ℝ} (hs : (S.Ahat - s • S.Ihat).det ≠ 0)
    (μ : ℂ) :
    S.Ahat.map Complex.ofReal - μ • S.Ihat.map Complex.ofReal =
      (S.Ahat.map Complex.ofReal - (s : ℂ) • S.Ihat.map Complex.ofReal) *
        (1 - (μ - s) • (Nr S s).map Complex.ofReal) := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, shift_mul_Nc S hs, sub_smul]
  abel

/-- Woodford (2003), (1.15) and App. G.1: **the roots of (1.15) are `s + ν⁻¹` for the nonzero
eigenvalues `ν` of `N`, with multiplicity.** -/
theorem pencil_roots_eq (S : LinearRESystem ιZ ιz) {s : ℝ}
    (hs : (S.Ahat - s • S.Ihat).det ≠ 0) :
    S.pencilPoly.roots = (((Nr S s).map Complex.ofReal).charpoly.roots.filter
      (fun ν => ν ≠ 0)).map (fun ν => (s : ℂ) + ν⁻¹) := by
  set R := ((Nr S s).map Complex.ofReal).charpoly.roots with hR
  set F := R.filter (fun ν => ν ≠ 0) with hF
  set κ : ℂ := (S.Ahat.map Complex.ofReal - (s : ℂ) • S.Ihat.map Complex.ofReal).det *
    (F.map fun ν => -ν).prod with hκ
  have hκ0 : κ ≠ 0 := by
    refine mul_ne_zero (det_shift_C S hs) (Multiset.prod_ne_zero ?_)
    intro h0
    obtain ⟨ν, hν, h⟩ := Multiset.mem_map.mp h0
    rw [hF, Multiset.mem_filter] at hν
    exact hν.2 (neg_eq_zero.mp h)
  have hpoly : S.pencilPoly =
      C κ * ((F.map fun ν => (s : ℂ) + ν⁻¹).map fun r => X - C r).prod := by
    refine Polynomial.funext fun μ => ?_
    rw [pencilPoly_eval, pencil_factor S hs μ, det_mul, det_one_sub_smul, eval_mul, eval_C,
      eval_multiset_prod, Multiset.map_map, Multiset.map_map, hκ, mul_assoc]
    congr 1
    rw [← Multiset.filter_add_not (fun ν : ℂ => ν ≠ 0)
      (((Nr S s).map Complex.ofReal).charpoly.roots), Multiset.map_add, Multiset.prod_add]
    have hz : ((((Nr S s).map Complex.ofReal).charpoly.roots.filter fun ν => ¬ ν ≠ 0).map
        fun ν => 1 - (μ - s) * ν).prod = 1 := by
      refine Multiset.prod_eq_one fun a ha => ?_
      obtain ⟨ν, hν, rfl⟩ := Multiset.mem_map.mp ha
      rw [Multiset.mem_filter, not_not] at hν
      rw [hν.2, mul_zero, sub_zero]
    rw [hz, mul_one, ← hF, ← Multiset.prod_map_mul]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun ν hν => ?_)
    rw [hF, Multiset.mem_filter] at hν
    have hν0 := hν.2
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
    field_simp
    ring
  rw [hpoly, roots_C_mul _ hκ0, roots_multiset_prod_X_sub_C]

/-- Woodford (2003), App. G.1: for `μ ≠ s`, the multiplicity of the root `μ` of (1.15) is the
multiplicity of the eigenvalue `(μ − s)⁻¹` of `N`. -/
theorem count_pencil_roots (S : LinearRESystem ιZ ιz) {s : ℝ}
    (hs : (S.Ahat - s • S.Ihat).det ≠ 0) {μ : ℂ} (hμ : μ ≠ s) :
    S.pencilPoly.roots.count μ =
      ((Nr S s).map Complex.ofReal).charpoly.roots.count (μ - s)⁻¹ := by
  have hinj : Function.Injective fun ν : ℂ => (s : ℂ) + ν⁻¹ :=
    fun a b h => inv_injective (add_left_cancel h)
  have hμe : μ = (fun ν : ℂ => (s : ℂ) + ν⁻¹) ((μ - s)⁻¹) := by
    simp only [inv_inv]
    ring
  have hne : (μ - (s : ℂ))⁻¹ ≠ 0 := inv_ne_zero (sub_ne_zero.mpr hμ)
  rw [pencil_roots_eq S hs]
  conv_lhs => rw [hμe]
  rw [Multiset.count_map_eq_count' _ _ hinj,
    Multiset.count_filter_of_pos (p := fun ν : ℂ => ν ≠ 0) hne]

/-! ### Real descent -/

/-- Woodford (2003), App. G.1, fn 2 (real combinations of complex eigenvectors): the real
vectors whose complexification lies in a complex subspace `W`. -/
def realPart {κ : Type*} (W : Submodule ℂ (κ → ℂ)) : Submodule ℝ (κ → ℝ) where
  carrier := {v | (fun i => (v i : ℂ)) ∈ W}
  add_mem' := by
    intro a b ha hb
    have := W.add_mem ha hb
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Complex.ofReal_add]
    exact this
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, Complex.ofReal_zero]
    exact W.zero_mem
  smul_mem' := by
    intro c v hv
    have := W.smul_mem (c : ℂ) hv
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    exact this

/-- Woodford (2003), App. G.1, p. 716 (complex roots come in conjugate pairs): a complex subspace
closed under componentwise conjugation. -/
def ConjStable {κ : Type*} (W : Submodule ℂ (κ → ℂ)) : Prop :=
  ∀ w ∈ W, (fun i => starRingEnd ℂ (w i)) ∈ W

/-- Woodford (2003), App. G.1, fn 2 (**real descent**): a conjugation-closed complex subspace
has a real part of the same dimension (restated pattern from the Woodford Chapter 4 project,
`InvariantSplit.finrank_boundedOrbitsC_le`). -/
theorem finrank_realPart {κ : Type*} [Finite κ] (W : Submodule ℂ (κ → ℂ)) (hW : ConjStable W) :
    Module.finrank ℝ (realPart W) = Module.finrank ℂ W := by
  set b := Module.finBasis ℝ (realPart W) with hb
  set f : Fin (Module.finrank ℝ (realPart W)) → (κ → ℂ) :=
    fun k i => (((b k : realPart W) : κ → ℝ) i : ℂ) with hf
  have hfW : ∀ k, f k ∈ W := fun k => (b k).2
  have hind : LinearIndependent ℂ f :=
    linearIndependent_ofReal (b.linearIndependent.map' (realPart W).subtype
      (Submodule.ker_subtype _))
  have hspan : Submodule.span ℂ (Set.range f) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact hfW k
  have hreal : ∀ v ∈ realPart W,
      (fun i => (v i : ℂ)) ∈ Submodule.span ℂ (Set.range f) := by
    intro v hv
    have hsum := b.sum_repr ⟨v, hv⟩
    have e : (fun i => (v i : ℂ)) = ∑ k, ((b.repr ⟨v, hv⟩ k : ℝ) : ℂ) • f k := by
      funext i
      have := congrArg (fun z : realPart W => (z : κ → ℝ) i) hsum
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hf, ← this, Complex.ofReal_sum,
        Complex.ofReal_mul]
    rw [e]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))
  have hle : W ≤ Submodule.span ℂ (Set.range f) := by
    intro w hw
    have hc := hW w hw
    have hre : (fun i => (w i).re) ∈ realPart W := by
      change (fun i => (((w i).re : ℝ) : ℂ)) ∈ W
      have e : (fun i => (((w i).re : ℝ) : ℂ)) =
          (2⁻¹ : ℂ) • (w + fun i => starRingEnd ℂ (w i)) := by
        funext i
        apply Complex.ext
        · simp
          ring
        · simp
      rw [e]
      exact W.smul_mem _ (W.add_mem hw hc)
    have him : (fun i => (w i).im) ∈ realPart W := by
      change (fun i => (((w i).im : ℝ) : ℂ)) ∈ W
      have e : (fun i => (((w i).im : ℝ) : ℂ)) =
          (-Complex.I / 2) • (w - fun i => starRingEnd ℂ (w i)) := by
        funext i
        apply Complex.ext
        · simp
          ring
        · simp
      rw [e]
      exact W.smul_mem _ (W.sub_mem hw hc)
    have e : w = (fun i => ((w i).re : ℂ)) + Complex.I • fun i => ((w i).im : ℂ) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [mul_comm]
      exact (Complex.re_add_im (w i)).symm
    rw [e]
    exact Submodule.add_mem _ (hreal _ hre) (Submodule.smul_mem _ _ (hreal _ him))
  have h1 := finrank_span_eq_card hind
  rw [Fintype.card_fin] at h1
  apply le_antisymm
  · calc Module.finrank ℝ (realPart W) = Module.finrank ℂ (Submodule.span ℂ (Set.range f)) :=
          h1.symm
      _ ≤ Module.finrank ℂ W := Submodule.finrank_mono hspan
  · calc Module.finrank ℂ W ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range f)) :=
          Submodule.finrank_mono hle
      _ = Module.finrank ℝ (realPart W) := h1

/-! ### Generalised eigenspaces of a real matrix and conjugation -/

/-- Woodford (2003), App. G.1: `((f − ν)^k) w` for `f = toLin' M` is `(M − ν)^k w`. -/
theorem toLin'_sub_pow_apply {κ : Type*} [Fintype κ] [DecidableEq κ] (M : Matrix κ κ ℂ)
    (ν : ℂ) (k : ℕ) (w : κ → ℂ) :
    ((Matrix.toLin' M - ν • 1) ^ k) w = ((M - ν • (1 : Matrix κ κ ℂ)) ^ k) *ᵥ w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', ← mulVec_mulVec, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, Matrix.toLin'_apply, sub_mulVec, smul_mulVec,
      one_mulVec]

/-- Woodford (2003), App. G.1, p. 716: conjugation maps the generalised eigenspace of `ν` of a
real matrix onto that of `ν̄`. -/
theorem conj_mem_maxGen {κ : Type*} [Fintype κ] [DecidableEq κ] (Nr : Matrix κ κ ℝ) {ν : ℂ}
    {w : κ → ℂ} (hw : w ∈ Module.End.maxGenEigenspace (Matrix.toLin' (Nr.map Complex.ofReal)) ν) :
    (fun i => starRingEnd ℂ (w i)) ∈
      Module.End.maxGenEigenspace (Matrix.toLin' (Nr.map Complex.ofReal)) (starRingEnd ℂ ν) := by
  rw [Module.End.mem_maxGenEigenspace] at hw ⊢
  obtain ⟨k, hk⟩ := hw
  refine ⟨k, ?_⟩
  rw [toLin'_sub_pow_apply] at hk ⊢
  have hm : ((Nr.map Complex.ofReal - ν • (1 : Matrix κ κ ℂ)) ^ k).map (starRingEnd ℂ) =
      (Nr.map Complex.ofReal - starRingEnd ℂ ν • (1 : Matrix κ κ ℂ)) ^ k := by
    rw [← RingHom.mapMatrix_apply, map_pow, RingHom.mapMatrix_apply]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply_ne hij]
  rw [← hm]
  funext i
  have := congrFun hk i
  simp only [Pi.zero_apply] at this ⊢
  have h2 := congrArg (starRingEnd ℂ) this
  rw [map_zero] at h2
  rw [← h2]
  simp [mulVec, dotProduct, map_sum]

/-- Woodford (2003), App. G.1: conjugation maps the eigenspace of a real eigenvalue of a real
matrix into itself. -/
theorem conj_mem_eigenspace {κ : Type*} [Fintype κ] [DecidableEq κ] (Nr : Matrix κ κ ℝ)
    (r : ℝ) {w : κ → ℂ}
    (hw : w ∈ Module.End.eigenspace (Matrix.toLin' (Nr.map Complex.ofReal)) (r : ℂ)) :
    (fun i => starRingEnd ℂ (w i)) ∈
      Module.End.eigenspace (Matrix.toLin' (Nr.map Complex.ofReal)) (r : ℂ) := by
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hw ⊢
  funext i
  have := congrArg (starRingEnd ℂ) (congrFun hw i)
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal] at this
  have e : (Nr.map Complex.ofReal *ᵥ fun i => starRingEnd ℂ (w i)) i =
      starRingEnd ℂ ((Nr.map Complex.ofReal *ᵥ w) i) := by
    simp [mulVec, dotProduct, map_sum]
  rw [e, this]
  simp

/-! ### The selected subspace `W` -/

/-- Woodford (2003), Assumption 8.2: the selection takes whole root classes — each selected
nonzero root with its full multiplicity as a root of (1.15). -/
def SelWhole (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) : Prop :=
  ∀ μ ∈ sel, sel.count μ = S.pencilPoly.roots.count μ

/-- Woodford (2003), App. G.1: `N` as a complex linear map. -/
noncomputable def φN (S : LinearRESystem ιZ ιz) (s : ℝ) : Module.End ℂ (ιZ ⊕ ιz → ℂ) :=
  Matrix.toLin' ((Nr S s).map Complex.ofReal)

/-- Woodford (2003), App. G.1: the eigenvalue `(0 − s)⁻¹` of `N` belonging to the zero root. -/
noncomputable def ν0 (s : ℝ) : ℂ := ((0 : ℂ) - s)⁻¹

/-- Woodford (2003), App. G.1: the eigenspace of `ν₀` (that is, `ker A`) and the generalised
eigenspaces of the other values. -/
noncomputable def Wfam (S : LinearRESystem ιZ ιz) (s : ℝ) (ν : ℂ) :
    Submodule ℂ (ιZ ⊕ ιz → ℂ) :=
  if ν = ν0 s then (φN S s).eigenspace ν else (φN S s).maxGenEigenspace ν

/-- Woodford (2003), App. G.1: the eigenvalues of `N` used: `ν₀` and `(μ − s)⁻¹` for the
selected nonzero roots `μ`. -/
noncomputable def Tset (sel : Multiset ℂ) (s : ℝ) : Finset ℂ :=
  insert (ν0 s) (sel.toFinset.image fun μ => (μ - s)⁻¹)

/-- Woodford (2003), App. G.1, (G.4): the complex selected subspace. -/
noncomputable def Wsub (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) (s : ℝ) :
    Submodule ℂ (ιZ ⊕ ιz → ℂ) :=
  (Tset sel s).sup (Wfam S s)

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), App. G.1: the conjugation preimage of a complex subspace. -/
def conjPre {κ : Type*} (W : Submodule ℂ (κ → ℂ)) : Submodule ℂ (κ → ℂ) where
  carrier := {w | (fun i => starRingEnd ℂ (w i)) ∈ W}
  add_mem' := by
    intro a b ha hb
    have := W.add_mem ha hb
    simp only [Set.mem_ofPred_eq, Pi.add_apply, map_add]
    exact this
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, map_zero]
    exact W.zero_mem
  smul_mem' := by
    intro c v hv
    have := W.smul_mem (starRingEnd ℂ c) hv
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, map_mul]
    exact this

/-- Woodford (2003), App. G.1: `Wfam ν₀` is the eigenspace of `ν₀`. -/
theorem Wfam_ν0 (S : LinearRESystem ιZ ιz) (s : ℝ) :
    Wfam S s (ν0 s) = (φN S s).eigenspace (ν0 s) := by
  simp [Wfam]

/-- Woodford (2003), App. G.1: `Wfam ν` is the generalised eigenspace of `ν ≠ ν₀`. -/
theorem Wfam_ne (S : LinearRESystem ιZ ιz) (s : ℝ) {ν : ℂ} (h : ν ≠ ν0 s) :
    Wfam S s ν = (φN S s).maxGenEigenspace ν := by
  simp [Wfam, h]

/-- Woodford (2003), App. G.1: `Wfam ν ≤` generalised eigenspace. -/
theorem Wfam_le (S : LinearRESystem ιZ ιz) (s : ℝ) (ν : ℂ) :
    Wfam S s ν ≤ (φN S s).maxGenEigenspace ν := by
  unfold Wfam
  split_ifs
  · exact Module.End.eigenspace_le_maxGenEigenspace
  · exact le_rfl

/-- Woodford (2003), App. G.1: the family `Wfam` is independent. -/
theorem Wfam_indep (S : LinearRESystem ιZ ιz) (s : ℝ) : iSupIndep (Wfam S s) :=
  (Module.End.independent_maxGenEigenspace _).mono (Wfam_le S s)

/-- Woodford (2003), App. G.1: `ν₀ = −1/s` is real. -/
theorem ν0_eq (s : ℝ) : ν0 s = ((-s⁻¹ : ℝ) : ℂ) := by
  simp [ν0]

/-- Woodford (2003), App. G.1: `ν₀ ≠ 0` for `s ≠ 0`. -/
theorem ν0_ne_zero {s : ℝ} (hs0 : s ≠ 0) : ν0 s ≠ 0 := by
  rw [ν0_eq]
  exact_mod_cast neg_ne_zero.mpr (inv_ne_zero hs0)

/-- Woodford (2003), App. G.1: `(μ − s)⁻¹ ≠ ν₀` for `μ ≠ 0`. -/
theorem inv_sub_ne_ν0 {s : ℝ} {μ : ℂ} (hμ : μ ≠ 0) : (μ - s)⁻¹ ≠ ν0 s := by
  intro h
  apply hμ
  have := sub_left_injective (inv_injective h)
  simpa using this

/-- Woodford (2003), App. G.1, p. 716: `W` is closed under conjugation (the selection is closed
under conjugation and `s` is real). -/
theorem Wsub_conj (S : LinearRESystem ιZ ιz) {sel : Multiset ℂ} (hc : ConjClosed sel)
    (hsel0 : ∀ μ ∈ sel, μ ≠ 0) (s : ℝ) : ConjStable (Wsub S sel s) := by
  intro w hw
  have hle : Wsub S sel s ≤ conjPre (Wsub S sel s) := by
    refine Finset.sup_le fun ν hν => ?_
    intro v hv
    change (fun i => starRingEnd ℂ (v i)) ∈ Wsub S sel s
    by_cases h0 : ν = ν0 s
    · subst h0
      simp only [Wfam, ↓reduceIte] at hv
      have hv' := conj_mem_eigenspace (Nr S s) (-s⁻¹) (by rw [← ν0_eq]; exact hv)
      rw [← ν0_eq] at hv'
      have : Wfam S s (ν0 s) ≤ Wsub S sel s := Finset.le_sup (Finset.mem_insert_self _ _)
      exact this (by simp only [Wfam, ↓reduceIte]; exact hv')
    · simp only [Wfam, h0, ↓reduceIte] at hv
      have hv' := conj_mem_maxGen (Nr S s) hv
      rw [Tset, Finset.mem_insert] at hν
      rcases hν with hν | hν
      · exact absurd hν h0
      obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp hν
      rw [Multiset.mem_toFinset] at hμ
      have hcμ : starRingEnd ℂ ((μ - s)⁻¹) = (starRingEnd ℂ μ - s)⁻¹ := by
        simp [map_inv₀, map_sub]
      rw [hcμ] at hv'
      have hmem : (starRingEnd ℂ μ - s)⁻¹ ∈ Tset sel s :=
        Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨starRingEnd ℂ μ, Multiset.mem_toFinset.mpr (hc.conj_mem hμ), rfl⟩)
      have hne : (starRingEnd ℂ μ - s)⁻¹ ≠ ν0 s :=
        inv_sub_ne_ν0 ((_root_.map_ne_zero _).mpr (hsel0 μ hμ))
      have : Wfam S s ((starRingEnd ℂ μ - s)⁻¹) ≤ Wsub S sel s := Finset.le_sup hmem
      exact this (by simp only [Wfam, hne, ↓reduceIte]; exact hv')
  exact hle hw

/-- Woodford (2003), App. G.1: `W` is invariant under `N`. -/
theorem Wsub_invariant (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) (s : ℝ) {w : ιZ ⊕ ιz → ℂ}
    (hw : w ∈ Wsub S sel s) : φN S s w ∈ Wsub S sel s := by
  have hle : Wsub S sel s ≤ (Wsub S sel s).comap (φN S s) := by
    refine Finset.sup_le fun ν hν v hv => ?_
    rw [Submodule.mem_comap]
    have hsup : Wfam S s ν ≤ Wsub S sel s := Finset.le_sup hν
    apply hsup
    unfold Wfam at hv ⊢
    split_ifs at hv ⊢
    · rw [Module.End.mem_eigenspace_iff] at hv ⊢
      rw [hv, map_smul, hv]
    · exact Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl _) ν hv
  exact hle hw

/-- Woodford (2003), App. G.1: an eigenvector of `N` in `W` has its eigenvalue in `Tset`. -/
theorem mem_Tset_of_eig (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) (s : ℝ) {lam : ℂ}
    {u : ιZ ⊕ ιz → ℂ} (hu0 : u ≠ 0) (huW : u ∈ Wsub S sel s) (hu : φN S s u = lam • u) :
    lam ∈ Tset sel s := by
  by_contra hnl
  have h1 : u ∈ (φN S s).maxGenEigenspace lam :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hu)
  have h2 : u ∈ ⨆ ν, ⨆ (_ : ν ≠ lam), (φN S s).maxGenEigenspace ν := by
    have hle : Wsub S sel s ≤ ⨆ ν, ⨆ (_ : ν ≠ lam), (φN S s).maxGenEigenspace ν := by
      refine Finset.sup_le fun ν hν => ?_
      have hne : ν ≠ lam := fun h => hnl (h ▸ hν)
      exact (Wfam_le S s ν).trans (le_iSup₂_of_le ν hne le_rfl)
    exact hle huW
  have hd := (Module.End.independent_maxGenEigenspace (φN S s)) lam
  exact hu0 ((Submodule.disjoint_def.mp hd) u h1 h2)

/-- Woodford (2003), App. G.1 (the zero root): the real part of the eigenspace of `ν₀` is
`ker A`. -/
theorem realPart_eigenspace_ν0 (S : LinearRESystem ιZ ιz) {s : ℝ} (hs0 : s ≠ 0)
    (hs : (S.Ahat - s • S.Ihat).det ≠ 0) :
    realPart ((φN S s).eigenspace (ν0 s)) = LinearMap.ker S.Ahat.mulVecLin := by
  ext v
  change (fun i => (v i : ℂ)) ∈ (φN S s).eigenspace (ν0 s) ↔ S.Ahat *ᵥ v = 0
  rw [Module.End.mem_eigenspace_iff, φN, Matrix.toLin'_apply]
  constructor
  · intro h
    have h1 := N_to_eig S hs (ν0_ne_zero hs0) h
    have hz : (s : ℂ) + (ν0 s)⁻¹ = 0 := by simp [ν0]
    rw [hz, zero_smul, map_mulVec_ofReal] at h1
    funext i
    have := congrFun h1 i
    simpa using this
  · intro h
    have h1 : S.Ahat.map Complex.ofReal *ᵥ (fun i => (v i : ℂ)) =
        (0 : ℂ) • (S.Ihat.map Complex.ofReal *ᵥ fun i => (v i : ℂ)) := by
      rw [map_mulVec_ofReal, h, zero_smul]
      funext i
      simp
    have h2 := eig_to_N S hs (μ := 0) (by exact_mod_cast hs0.symm) h1
    rw [h2]
    rfl

/-- Woodford (2003), App. G.1: `dim_ℂ (eigenspace of ν₀) = n − rank A`. -/
theorem finrank_eigenspace_ν0 (S : LinearRESystem ιZ ιz) {s : ℝ} (hs0 : s ≠ 0)
    (hs : (S.Ahat - s • S.Ihat).det ≠ 0) :
    Module.finrank ℂ ((φN S s).eigenspace (ν0 s)) = Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank := by
  have hcs : ConjStable ((φN S s).eigenspace (ν0 s)) := fun w hw => by
    have := conj_mem_eigenspace (Nr S s) (-s⁻¹) (by rw [← ν0_eq]; exact hw)
    rw [← ν0_eq] at this
    exact this
  rw [← finrank_realPart _ hcs, realPart_eigenspace_ν0 S hs0 hs]
  have := LinearMap.finrank_range_add_finrank_ker S.Ahat.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at this
  change S.Ahat.rank + _ = _ at this
  omega

/-- Woodford (2003), Assumption 8.2 and App. G.1: **`dim W = (n − rank A) + #sel`** (with
`SelWhole`, every selected root carried with its full multiplicity). -/
theorem finrank_Wsub (S : LinearRESystem ιZ ιz) {sel : Multiset ℂ} {s : ℝ} (hs0 : s ≠ 0)
    (hs : (S.Ahat - s • S.Ihat).det ≠ 0) (hsel : ∀ μ ∈ sel, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0)
    (hw : SelWhole S sel) :
    Module.finrank ℂ (Wsub S sel s) =
      (Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank) + Multiset.card sel := by
  have hnot : ν0 s ∉ sel.toFinset.image fun μ : ℂ => (μ - s)⁻¹ := by
    intro h
    obtain ⟨μ, hμ, he⟩ := Finset.mem_image.mp h
    exact inv_sub_ne_ν0 (hsel μ (Multiset.mem_toFinset.mp hμ)).1 he
  have hinj : Set.InjOn (fun μ : ℂ => (μ - s)⁻¹) (sel.toFinset : Set ℂ) :=
    fun a _ b _ h => sub_left_injective (inv_injective h)
  rw [Wsub, finrank_finset_sup (Wfam_indep S s), Tset, Finset.sum_insert hnot,
    Finset.sum_image hinj]
  congr 1
  · rw [Wfam_ν0]
    exact finrank_eigenspace_ν0 S hs0 hs
  · rw [← Multiset.toFinset_sum_count_eq]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [Multiset.mem_toFinset] at hμ
    have hne := inv_sub_ne_ν0 (s := s) (hsel μ hμ).1
    change Module.finrank ℂ (Wfam S s ((μ - s)⁻¹)) = _
    rw [Wfam_ne S s hne, LinearMap.finrank_maxGenEigenspace_eq, φN, Matrix.charpoly_toLin',
      ← count_roots, hw μ hμ]
    have hμs : μ ≠ (s : ℂ) := by
      intro h
      apply hs
      have := (hsel μ hμ).2
      rw [h, pencilPoly_eval, det_pencil_ofReal] at this
      exact_mod_cast this
    exact (count_pencil_roots S hs hμs).symm

/-! ### The real deflating pair -/

/-- Woodford (2003), App. G.1, fn 2: the real selected subspace (real part of `W`). -/
noncomputable def Ureal (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) (s : ℝ) :
    Submodule ℝ (ιZ ⊕ ιz → ℝ) :=
  realPart (Wsub S sel s)

/-- Woodford (2003), App. G.1: the real selected subspace is invariant under `N`. -/
theorem Nr_mem_Ureal (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) (s : ℝ)
    {v : ιZ ⊕ ιz → ℝ} (hv : v ∈ Ureal S sel s) : Nr S s *ᵥ v ∈ Ureal S sel s := by
  change (fun i => ((Nr S s *ᵥ v) i : ℂ)) ∈ Wsub S sel s
  rw [← map_mulVec_ofReal]
  have := Wsub_invariant S sel s (w := fun i => (v i : ℂ)) hv
  rw [φN, Matrix.toLin'_apply] at this
  exact this

/-- Woodford (2003), App. G.1: `N` is injective on the selected subspace (`0` is not among the
selected eigenvalues of `N`). -/
theorem Nr_inj_Ureal (S : LinearRESystem ιZ ιz) {sel : Multiset ℂ} {s : ℝ} (hs0 : s ≠ 0)
    (hs : (S.Ahat - s • S.Ihat).det ≠ 0) (hsel : ∀ μ ∈ sel, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0)
    {v : ιZ ⊕ ιz → ℝ} (hv : v ∈ Ureal S sel s) (h0 : Nr S s *ᵥ v = 0) : v = 0 := by
  by_contra hne
  have hvc : (fun i => (v i : ℂ)) ≠ 0 := fun h => hne (funext fun i => by
    have := congrFun h i
    simpa using this)
  have heig : φN S s (fun i => (v i : ℂ)) = (0 : ℂ) • fun i => (v i : ℂ) := by
    rw [φN, Matrix.toLin'_apply, map_mulVec_ofReal, h0, zero_smul]
    funext i
    simp
  have hT := mem_Tset_of_eig S sel s hvc hv heig
  rw [Tset, Finset.mem_insert] at hT
  rcases hT with h | h
  · exact ν0_ne_zero hs0 h.symm
  · obtain ⟨μ, hμ, he⟩ := Finset.mem_image.mp h
    rw [Multiset.mem_toFinset] at hμ
    have hμs : μ = s := sub_eq_zero.mp (inv_eq_zero.mp he)
    apply hs
    have := (hsel μ hμ).2
    rw [hμs, pencilPoly_eval, det_pencil_ofReal] at this
    exact_mod_cast this

/-- Woodford (2003), App. G.1, (G.4) and fn 2 (**repeated roots allowed**), for any number of
columns: a conjugation-closed multiset `sel` of nonzero roots of a nonzero (1.15), each taken with
its full multiplicity, gives a real `n × κ` matrix `J` with independent columns,
`#κ = (n − rank A) + #sel`, and `Ψ` with `A J = Î J Ψ`, every eigenvalue of `Ψ` zero or in
`sel`. -/
theorem exists_deflating_cols (S : LinearRESystem ιZ ιz) {κ : Type*} [Fintype κ]
    [DecidableEq κ] {sel : Multiset ℂ} (hi : ConjClosed sel)
    (hsel : ∀ μ ∈ sel, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0) (hreg : S.pencilPoly ≠ 0)
    (hw : SelWhole S sel)
    (hcard : (Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank) + Multiset.card sel = Fintype.card κ) :
    ∃ (J : Matrix (ιZ ⊕ ιz) κ ℝ) (Ψ : Matrix κ κ ℝ), S.Ahat * J = S.Ihat * J * Ψ ∧
      LinearIndependent ℝ Jᵀ ∧
      ∀ μ : ℂ, (Matrix.scalar κ μ - Ψ.map Complex.ofReal).det = 0 → μ = 0 ∨ μ ∈ sel := by
  obtain ⟨s, hs0, hsev⟩ := PencilEigen.Construction.exists_shift hreg
  have hs : (S.Ahat - s • S.Ihat).det ≠ 0 := by
    intro h
    apply hsev
    rw [pencilPoly_eval, det_pencil_ofReal, h, Complex.ofReal_zero]
  have hdim : Module.finrank ℝ (Ureal S sel s) = Fintype.card κ := by
    rw [Ureal, finrank_realPart _ (Wsub_conj S hi (fun μ hμ => (hsel μ hμ).1) s),
      finrank_Wsub S hs0 hs hsel hw, hcard]
  let U := Ureal S sel s
  let b := Module.finBasisOfFinrankEq ℝ U hdim
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let col : κ → ιZ ⊕ ιz → ℝ := fun c => (b (e c) : ιZ ⊕ ιz → ℝ)
  have hcolU : ∀ c, col c ∈ U := fun c => (b (e c)).2
  let T : U →ₗ[ℝ] U := (Nr S s).mulVecLin.restrict (fun v hv => Nr_mem_Ureal S sel s hv)
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [Submodule.mem_bot]
    have h0 : Nr S s *ᵥ (x : ιZ ⊕ ιz → ℝ) = 0 := by
      have := congrArg Subtype.val hx
      exact this
    exact Subtype.ext (Nr_inj_Ureal S hs0 hs hsel x.2 h0)
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
  refine ⟨Matrix.of fun a c => col c a, Ψ, hdefl, hind, fun μ hμ => ?_⟩
  obtain ⟨z, hz0, hz⟩ := exists_eigvec hμ
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
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hcolU c)
  have hAu : S.Ahat.map Complex.ofReal *ᵥ u = μ • (S.Ihat.map Complex.ofReal *ᵥ u) := by
    have hdc : S.Ahat.map Complex.ofReal * Jc = S.Ihat.map Complex.ofReal * Jc *
        Ψ.map Complex.ofReal := by
      rw [hJc, ← map_ofReal_mul, ← map_ofReal_mul, ← map_ofReal_mul, hdefl]
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

/-- Woodford (2003), Assumption 8.2 and App. G.1, (G.4) and fn 2 (**repeated roots allowed**):
under Assumption 8.2 with a conjugation-closed selection that takes whole root classes, and a
nonzero (1.15), there is a real `n × n_Z` matrix `J` with independent columns and `Ψ` with
`A J = Î J Ψ`, every eigenvalue of `Ψ` zero or selected. -/
theorem exists_realSelection_general {S : LinearRESystem ιZ ιz} {β : ℝ}
    (h82 : Assumption82 S β) (hi : ConjClosed h82.sel) (hreg : S.pencilPoly ≠ 0)
    (hw : SelWhole S h82.sel) : Nonempty (RealSelection S h82.sel) := by
  have hsel : ∀ μ ∈ h82.sel, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0 := by
    intro μ hμ
    have := Multiset.mem_of_le h82.sel_le hμ
    rw [Multiset.mem_filter, Polynomial.mem_roots hreg] at this
    exact ⟨this.2.1, this.1⟩
  obtain ⟨J, Ψ, hd, hind, heig⟩ := exists_deflating_cols S (κ := ιZ) hi hsel hreg hw
    (by rw [add_comm]; exact h82.sel_card)
  exact ⟨⟨J, Ψ, hd, hind, heig⟩⟩

/-- Woodford (2003), Assumption 8.3: with distinct nonzero roots every selection takes whole
root classes, so `PencilEigen.exists_realSelection` is the special case of
`exists_realSelection_general`. -/
theorem selWhole_of_assumption83 {S : LinearRESystem ιZ ιz} {β : ℝ} (h82 : Assumption82 S β)
    (h83 : Assumption83 S) : SelWhole S h82.sel := by
  intro μ hμ
  have hle : h82.sel ≤ nonzeroRoots S :=
    h82.sel_le.trans (Multiset.monotone_filter_right _ fun ν h => h.1)
  have hnd : h82.sel.Nodup := Multiset.nodup_of_le hle h83.nodup
  have hμn : μ ∈ nonzeroRoots S := Multiset.mem_of_le hle hμ
  have hμ0 : μ ≠ 0 := (Multiset.mem_filter.mp hμn).2
  rw [Multiset.count_eq_one_of_mem hnd hμ,
    ← Multiset.count_filter_of_pos (p := fun ν : ℂ => ν ≠ 0) hμ0]
  exact (Multiset.count_eq_one_of_mem h83.nodup hμn).symm

/-- Woodford (2003), Assumptions 8.2 (case (i), whole classes) and 8.4, App. G.1: the deflating
pair, now with only a nonzero (1.15) in place of Assumption 8.3. -/
noncomputable def splitGen {β : ℝ} {S : LinearRESystem ιZ ιz} (hβ : 0 < β)
    (h82 : Assumption82 S β) (R : RealSelection S h82.sel) (hreg : S.pencilPoly ≠ 0)
    (h84 : Assumption84 S h82.sel) : DeflatingSplit S β where
  J := R.J
  Ψ := R.Ψ
  deflate := R.deflate
  eig_lt := fun μ hμ => by
    rcases R.eig μ hμ with h0 | hm
    · rw [h0, norm_zero]
      exact inv_pos.mpr hβ
    · have := Multiset.mem_of_le h82.sel_le hm
      rw [Multiset.mem_filter] at this
      exact this.2.2
  J1_det := J1_det_ne_zero R h84 fun _ hv => IJ_injective R (fun μ hμ => by
      have := Multiset.mem_of_le h82.sel_le hμ
      rw [Multiset.mem_filter, Polynomial.mem_roots hreg] at this
      exact this.1) hreg hv
  K_det := K_det_ne_zero R h84 (J1_det_ne_zero R h84 fun _ hv => IJ_injective R (fun μ hμ => by
      have := Multiset.mem_of_le h82.sel_le hμ
      rw [Multiset.mem_filter, Polynomial.mem_roots hreg] at this
      exact this.1) hreg hv)

/-- Woodford (2003), App. G.1: the deflating pair chosen from Assumptions 8.2 (i, whole classes)
and 8.4 with (1.15) nonzero (no distinctness). -/
noncomputable def splitOfGen {ιτ : Type*} [Fintype ιτ] (P : LQProblem ιZ ιz ιτ)
    (h82 : Assumption82 P.sys P.β) (hi : ConjClosed h82.sel) (hreg : P.sys.pencilPoly ≠ 0)
    (hw : SelWhole P.sys h82.sel) (h84 : Assumption84 P.sys h82.sel) :
    DeflatingSplit P.sys P.β :=
  splitGen P.β_pos h82 (exists_realSelection_general h82 hi hreg hw).some hreg h84

/-- Woodford (2003), **Proposition 8.1**, p. 553, **with repeated roots allowed**: under
Assumption 8.2 (case (i), whole root classes), Assumption 8.4 and a nonzero (1.15) — no
distinctness — the corrected Proposition 8.1 holds for any expectation system. -/
theorem prop81_of_assumptions_general {Ω ιτ : Type*} [Fintype ιτ] (P : LQProblem ιZ ιz ιτ)
    (h82 : Assumption82 P.sys P.β) (hi : ConjClosed h82.sel) (hreg : P.sys.pencilPoly ≠ 0)
    (hw : SelWhole P.sys h82.sel) (h84 : Assumption84 P.sys h82.sel)
    (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    Nonempty (Prop81General.Prop81ConclusionM P 𝔼 t0) :=
  ⟨Prop81General.prop81 P (splitOfGen P h82 hi hreg hw h84) 𝔼 t0⟩

/-- Woodford (2003), **Proposition 8.2**, p. 555, **with repeated roots allowed**: under
Assumptions 8.1, 8.2 (case (i), whole classes), 8.4, 8.5 and a nonzero (1.15), commitment to
(1.23) is robustly optimal (unique bounded equilibrium for every bounded disturbance process,
optimal subject to (1.27)). -/
theorem prop82_of_assumptions_general {Ω ιτ : Type*} [Fintype ιτ] {P : LQProblem ιZ ιz ιτ}
    {𝔼 : ExpectationSystem Ω} {t0 : ℕ} (hpull : 𝔼.PullOut)
    (hA : Prop82General.Assumption81M P 𝔼 t0) (h82 : Assumption82 P.sys P.β)
    (hi : ConjClosed h82.sel) (hreg : P.sys.pencilPoly ≠ 0) (hw : SelWhole P.sys h82.sel)
    (h84 : Assumption84 P.sys h82.sel)
    (h85 : Assumption85 (Λmat P.sys P.β (splitOfGen P h82 hi hreg hw h84).J) P.sys.B2)
    {D : ℕ} (hD : D + 1 ≤ t0) (hDk : P.sys.Et.rank ≤ D) {Mh qh : ℕ → Ω → ιz → ℝ}
    {vh : ℕ → Ω → ℝ}
    (hhist : TargetCriterion.Prop82.HistoryOK
      (Λmat P.sys P.β (splitOfGen P h82 hi hreg hw h84).J) P.sys.B2 t0 D Mh qh vh)
    (hMhb : BoundedV Mh) (hMhk : AdaptedV 𝔼 Mh) (hqhb : BoundedV qh)
    (hvhb : ∃ K, ∀ t ω, |vh t ω| ≤ K) :
    RobustlyOptimal (κ := ιz) P 𝔼 t0
      (fun _ y => Prop82General.Prop82M.CriterionM
        (Prop81General.prop81 P (splitOfGen P h82 hi hreg hw h84) 𝔼 t0) D qh vh y)
      (fun _ y t ω => zpart (y t ω)) :=
  Prop82General.prop82_of_split hpull hA _ h85.2 hD hDk hhist hMhb hMhk hqhb hvhb

end Woodford.OptimalPolicyRules.PencilRepeated
