/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.PencilEigen
import OptimalPolicyRules.Prop81General
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-!
# Proposition 8.3 (superinertia) in general

Woodford (2003), *Interest and Prices*, Chapter 8, §1.5, pp. 556–557: Assumption 8.7 and
Proposition 8.3, with Assumption 8.3 of Appendix G.1, p. 716.

Proposition 8.3 says that when (1.15) has `n_Z + m` roots with `|μ| < β⁻¹` (Assumption 8.7), the
lag polynomial `α(L) = det(I − ΛL)` of the optimal instrument rule (1.28) has `m` zeros inside
the unit circle. The book gives no proof (Giannoni and Woodford 2002a).

## What is proved

The matrix `Λ` is *any* matrix delivered by Proposition 8.1 (`Prop81Conclusion`): the claim is
proved for every representation (1.20)–(1.21) of the bounded solutions of (1.18), not only for
the one Giannoni and Woodford construct from eigenvectors. The proof is a dimension count.

* Perturbing a bounded solution of (1.18) by a deterministic bounded process `h` shows that
  bounded `h` solve the homogeneous (1.18) iff they solve the homogeneous (1.20)–(1.21)
  (`homEquiv_of_prop81`).
* **Upper bound.** Every nonzero root `λ` of (1.15) with `|λ| ≥ β⁻¹` gives a bounded homogeneous
  solution `(βλ)^{-t} w` of (1.18), hence an eigenvalue `(βλ)⁻¹` of `Λ` in the closed unit disc
  (`charpoly_root_of_pencil_root`); `Λ` kills `ker Ẽ'` (`mulVec_eq_zero_of_ker`). With
  Assumption 8.3 this leaves at most `m` eigenvalues outside the closed disc.
* **Lower bound.** Every vector `v` whose orbit `Λᵗ v` is bounded generates a bounded homogeneous
  solution of (1.18), which must satisfy the `n_Z + m` independent constraints `(Îu)'φ_t = 0`
  coming from the roots `|λ| < β⁻¹` (`constraint_of_orbitBdd`, `finrank_orbitBdd_le`).
  The generalised eigenspaces of `Λ` for `|μ| < 1` lie in that space, so `Λ` has at most
  `n_z − m` eigenvalues in the open disc (`card_inside_le`).
* An eigenvalue of `Λ` on the unit circle forces a root of (1.15) on `|λ| = β⁻¹`
  (`pencil_root_of_circle_eigenvalue`).

Since the zeros of `α` are the reciprocals of the nonzero eigenvalues of `Λ`
(`zerosInside_alpha`, `zerosOnCircle_alpha`):

* `prop83_bounds`: `zerosInside α ≤ m ≤ zerosInside α + zerosOnCircle α`, under Assumptions 8.1
  (only its existence half is used), 8.3 and 8.7 — no other hypothesis.
* `prop83`: **Proposition 8.3**: `zerosInside α = m` when, in addition, (1.15) has no root with
  `|λ| = β⁻¹` (`prop83Claim_holds`: the statement `TargetCriterion.Prop83Claim`);
  `prop83_superinertial`: with `m ≥ 1`, `α` has a zero inside the unit circle.
* `prop83_of_perturbation`: the same for any representation of Proposition 8.1 that is only
  known to be valid for deterministic perturbations of one bounded solution of (1.18) — e.g. a
  version restricted to multipliers with `M_t` known at `t`, the form that holds under
  uncertainty (`TargetCriterion.Prop81.Prop81Equiv` itself quantifies over all bounded
  multipliers).

Assumptions 8.2, 8.4, 8.5, 8.6 and `λ_i > 0` are not needed: `α` does not depend on the instrument
weight. The sample space must be nonempty (`Nonempty Ω`): on an empty sample space every matrix
satisfies the conclusion of Proposition 8.1 vacuously (`prop81Conclusion_of_isEmpty`).

## Corrections

* The hypothesis "no root of (1.15) on `|λ| = β⁻¹`" cannot be dropped from the dimension-count
  argument: `circle_counterexample` gives a system satisfying Assumptions 8.3 and 8.7 (`m = 1`)
  with a root on `|λ| = β⁻¹` and a matrix `Λ'` (a Jordan block) that represents the bounded
  homogeneous solutions of (1.18) exactly as Proposition 8.1 requires (`HomEquiv`), but whose
  `α(L) = (1 − L)²` has no zero inside the unit circle. (Whether such a `Λ'` can also be completed
  to a full `Prop81Conclusion` for a problem satisfying Assumption 8.1 is not settled here.)
* The sample space must be nonempty (`prop83_needs_nonempty`).
-/

namespace Woodford.OptimalPolicyRules.Prop83

open Matrix Polynomial GeneralSetup GeneralFOC GeneralFOC.LQ Adjugate
open TargetCriterion (zerosInside map_reverse_ofReal)
open TargetCriterion.Prop81
open PencilSplit (pencilPoly_eval EV_add_const)
open PencilEigen (Assumption83 nonzeroRoots card_le_rank_Ahat finrank_finset_sup map_mulVec_ofReal
  re_mulVec_map im_mulVec_map)

/-! ### Roots of a reversed polynomial -/

/-- Woodford (2003), p. 557 (tool): the roots of `1 − aX` are `{a⁻¹}` (none if `a = 0`). -/
theorem roots_one_sub_C_mul_X (a : ℂ) :
    (1 - C a * X : ℂ[X]).roots = if a = 0 then 0 else {a⁻¹} := by
  by_cases ha : a = 0
  · simp [ha]
  · have h : (1 - C a * X : ℂ[X]) = C (-a) * (X - C a⁻¹) := by
      rw [mul_sub, ← C_mul, neg_mul, mul_inv_cancel₀ ha, C_neg, C_neg, C_1]
      ring
    rw [h, roots_C_mul _ (neg_ne_zero.mpr ha), roots_X_sub_C]
    simp [ha]

/-- Woodford (2003), p. 557 (tool): `1 − aX ≠ 0`. -/
theorem one_sub_C_mul_X_ne_zero (a : ℂ) : (1 - C a * X : ℂ[X]) ≠ 0 := by
  intro h
  have := congrArg (fun p => p.coeff 0) h
  simp at this

/-- Woodford (2003), p. 557 (tool): the roots of `∏ (1 − a X)` are the inverses of the nonzero
`a`. -/
theorem roots_prod_one_sub (s : Multiset ℂ) :
    ((s.map fun a => (1 - C a * X : ℂ[X])).prod).roots = (s.filter (· ≠ 0)).map (·⁻¹) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have hprod : (s.map fun a => (1 - C a * X : ℂ[X])).prod ≠ 0 := by
      refine Multiset.prod_ne_zero fun h => ?_
      obtain ⟨b, -, hb⟩ := Multiset.mem_map.mp h
      exact one_sub_C_mul_X_ne_zero b hb
    rw [Multiset.map_cons, Multiset.prod_cons,
      roots_mul (mul_ne_zero (one_sub_C_mul_X_ne_zero a) hprod), ih, roots_one_sub_C_mul_X,
      Multiset.filter_cons]
    by_cases ha : a = 0 <;> simp [ha]

/-- Woodford (2003), p. 557 (tool): the reverse of a product is the product of the reverses. -/
theorem reverse_multiset_prod (s : Multiset ℂ[X]) : s.prod.reverse = (s.map reverse).prod := by
  induction s using Multiset.induction_on with
  | empty => simpa using reverse_C (1 : ℂ)
  | cons p s ih =>
    rw [Multiset.prod_cons, reverse_mul_of_domain, ih, Multiset.map_cons, Multiset.prod_cons]

/-- Woodford (2003), pp. 557–558 (tool): `reverse (X − a) = 1 − aX` (over any nontrivial
commutative ring; used over `ℂ` and `ℝ`). -/
theorem reverse_X_sub_C {R : Type*} [CommRing R] [Nontrivial R] (a : R) :
    (X - C a : R[X]).reverse = 1 - C a * X := by
  have hX : (X : R[X]).reverse = 1 := by
    have := reverse_mul_X (1 : R[X])
    rw [one_mul] at this
    rw [this]
    simpa using reverse_C (1 : R)
  rw [sub_eq_add_neg, ← C_neg, reverse_add_C, hX, natDegree_X, pow_one, C_neg]
  ring

/-- Woodford (2003), p. 557: over `ℂ` the roots of the reverse of `p ≠ 0` are the inverses of the
nonzero roots of `p`, with multiplicity. -/
theorem roots_reverse {p : ℂ[X]} (hp : p ≠ 0) :
    p.reverse.roots = (p.roots.filter (· ≠ 0)).map (·⁻¹) := by
  have hcard : Multiset.card p.roots = p.natDegree :=
    (splits_iff_card_roots).mp (IsAlgClosed.splits p)
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  conv_lhs => rw [← hfac]
  rw [reverse_mul_of_domain, reverse_C, reverse_multiset_prod, Multiset.map_map]
  have : (reverse ∘ fun a => X - C a) = fun a : ℂ => (1 - C a * X : ℂ[X]) :=
    funext reverse_X_sub_C
  rw [this, roots_C_mul _ hlc, roots_prod_one_sub]

/-! ### The zeros of `α(L)` and the eigenvalues of `Λ` -/

/-- Woodford (2003), p. 557: the number of zeros of a lag polynomial on the unit circle (with
multiplicity). -/
noncomputable def zerosOnCircle (α : ℝ[X]) : ℕ :=
  Multiset.card ((α.map Complex.ofRealHom).roots.filter (fun z => ‖z‖ = 1))

/-- Woodford (2003), p. 557 (tool): a real matrix viewed as a complex matrix. -/
abbrev cmat {a b : Type*} (M : Matrix a b ℝ) : Matrix a b ℂ := M.map Complex.ofReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Woodford (2003), p. 553: complexified, `α(L) = det(I − ΛL)` is the reversed characteristic
polynomial of `Λ`. -/
theorem alpha_map_ofReal (Λ : Matrix ι ι ℝ) :
    (alpha Λ).map Complex.ofRealHom = (cmat Λ).charpoly.reverse := by
  rw [alpha_eq_reverse_charpoly, map_reverse_ofReal, ← charpoly_map]
  rfl

/-- Woodford (2003), pp. 556–557: the zeros of `α(L) = det(I − ΛL)` inside the unit circle are the
reciprocals of the eigenvalues of `Λ` outside it. -/
theorem zerosInside_alpha (Λ : Matrix ι ι ℝ) :
    zerosInside (alpha Λ) = Multiset.card ((cmat Λ).charpoly.roots.filter (fun μ => 1 < ‖μ‖)) := by
  unfold zerosInside
  rw [alpha_map_ofReal, roots_reverse (charpoly_monic _).ne_zero, Multiset.filter_map,
    Multiset.card_map, Multiset.filter_filter]
  congr 1
  refine Multiset.filter_congr fun μ _ => ?_
  simp only [Function.comp, norm_inv]
  constructor
  · rintro ⟨h1, h0⟩
    exact (inv_lt_one₀ (norm_pos_iff.mpr h0)).mp h1
  · intro h
    have h0 : μ ≠ 0 := fun h0 => by simp [h0] at h; linarith
    exact ⟨(inv_lt_one₀ (norm_pos_iff.mpr h0)).mpr h, h0⟩

/-- Woodford (2003), p. 557: the zeros of `α(L)` on the unit circle are the reciprocals of the
eigenvalues of `Λ` on it. -/
theorem zerosOnCircle_alpha (Λ : Matrix ι ι ℝ) :
    zerosOnCircle (alpha Λ) =
      Multiset.card ((cmat Λ).charpoly.roots.filter (fun μ => ‖μ‖ = 1)) := by
  unfold zerosOnCircle
  rw [alpha_map_ofReal, roots_reverse (charpoly_monic _).ne_zero, Multiset.filter_map,
    Multiset.card_map, Multiset.filter_filter]
  congr 1
  refine Multiset.filter_congr fun μ _ => ?_
  simp only [Function.comp, norm_inv]
  constructor
  · rintro ⟨h1, -⟩
    exact inv_eq_one.mp h1
  · intro h
    have h0 : μ ≠ 0 := fun h0 => by simp [h0] at h
    exact ⟨by rw [h, inv_one], h0⟩

/-! ### Complex matrices and vectors: real and imaginary parts -/

/-- Woodford (2003), p. 557 (tool): `‖(M v)_i‖ ≤ (∑ |M|) C` when every `‖v_j‖ ≤ C`, `C ≥ 0`. -/
theorem norm_mulVec_le {a b : Type*} [Fintype a] [Fintype b] (M : Matrix a b ℂ) {w : b → ℂ}
    {C : ℝ} (hC0 : 0 ≤ C) (hw : ∀ j, ‖w j‖ ≤ C) (i : a) :
    ‖(M *ᵥ w) i‖ ≤ (∑ i', ∑ j, ‖M i' j‖) * C := by
  calc ‖(M *ᵥ w) i‖ = ‖∑ j, M i j * w j‖ := rfl
    _ ≤ ∑ j, ‖M i j * w j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖M i j‖ * C := Finset.sum_le_sum fun j _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hw j) (norm_nonneg _)
    _ = (∑ j, ‖M i j‖) * C := by rw [Finset.sum_mul]
    _ ≤ (∑ i', ∑ j, ‖M i' j‖) * C := by
        refine mul_le_mul_of_nonneg_right ?_ hC0
        exact Finset.single_le_sum (f := fun i' => ∑ j, ‖M i' j‖)
          (fun i' _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i)

/-! ### The homogeneous equations (1.18) and (1.20)–(1.21) -/

variable {ιZ ιz : Type*} [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz]

/-- Woodford (2003), fn 6, p. 539: a bounded deterministic vector sequence. -/
def BddSeq {κ R : Type*} [Norm R] (h : ℕ → κ → R) : Prop := ∃ C, ∀ t i, ‖h t i‖ ≤ C

/-- Woodford (2003), eq. (1.18), p. 552, homogeneous and deterministic (dates shifted to start
at `0`): `A' φ_{t+1} = β⁻¹ Î' φ_t`. -/
def HomSol (S : LinearRESystem ιZ ιz) (β : ℝ) (h : ℕ → ιZ ⊕ ιz → ℝ) : Prop :=
  ∀ t, S.Ahatᵀ *ᵥ h (t + 1) = β⁻¹ • (S.Ihatᵀ *ᵥ h t)

/-- Woodford (2003), eqs. (1.20)–(1.21), p. 553, homogeneous: `M_t = Λ M_{t−1}` and
`ξ_t = Υ M_{t−1}`, with `φ_t = (ξ_t, M_{t−1})`. -/
def RepSol (Λ : Matrix ιz ιz ℝ) (Υ : Matrix ιZ ιz ℝ) (h : ℕ → ιZ ⊕ ιz → ℝ) : Prop :=
  ∀ t, Mpart (h (t + 1)) = Λ *ᵥ Mpart (h t) ∧ ξpart (h t) = Υ *ᵥ Mpart (h t)

/-- Woodford (2003), Proposition 8.1, p. 553, for deterministic bounded perturbations: a bounded
`h` solves the homogeneous (1.18) iff it solves the homogeneous (1.20)–(1.21). -/
def HomEquiv (S : LinearRESystem ιZ ιz) (β : ℝ) (Λ : Matrix ιz ιz ℝ) (Υ : Matrix ιZ ιz ℝ) :
    Prop :=
  ∀ h, BddSeq h → (HomSol S β h ↔ RepSol Λ Υ h)

/-- Woodford (2003), eq. (1.18), homogeneous, for complex sequences. -/
def HomSolC (S : LinearRESystem ιZ ιz) (β : ℝ) (h : ℕ → ιZ ⊕ ιz → ℂ) : Prop :=
  ∀ t, cmat (S.Ahatᵀ) *ᵥ h (t + 1) = (β : ℂ)⁻¹ • (cmat (S.Ihatᵀ) *ᵥ h t)

/-- Woodford (2003), eqs. (1.20)–(1.21), homogeneous, for complex sequences. -/
def RepSolC (Λ : Matrix ιz ιz ℝ) (Υ : Matrix ιZ ιz ℝ) (h : ℕ → ιZ ⊕ ιz → ℂ) : Prop :=
  ∀ t, (fun r => h (t + 1) (Sum.inr r)) = cmat Λ *ᵥ (fun r => h t (Sum.inr r)) ∧
    (fun r => h t (Sum.inl r)) = cmat Υ *ᵥ (fun r => h t (Sum.inr r))

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 540 (tool): `M_{t−1}` is the `z`-block of `φ_t = (ξ_t, M_{t−1})`. -/
theorem Mpart_eq (v : ιZ ⊕ ιz → ℝ) : Mpart v = fun r => v (Sum.inr r) := rfl

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 540 (tool): `ξ_t` is the `Z`-block of `φ_t = (ξ_t, M_{t−1})`. -/
theorem ξpart_eq (v : ιZ ⊕ ιz → ℝ) : ξpart v = fun r => v (Sum.inl r) := rfl

variable {S : LinearRESystem ιZ ιz} {β : ℝ} {Λ : Matrix ιz ιz ℝ} {Υ : Matrix ιZ ιz ℝ}

/-- Woodford (2003), p. 553 (tool): a bounded complex solution of the homogeneous (1.18) solves
the homogeneous (1.20)–(1.21) (apply the real equivalence to real and imaginary parts). -/
theorem repSolC_of_homSolC (hE : HomEquiv S β Λ Υ) {h : ℕ → ιZ ⊕ ιz → ℂ} (hb : BddSeq h)
    (hs : HomSolC S β h) : RepSolC Λ Υ h := by
  obtain ⟨C, hC⟩ := hb
  have hre : RepSol Λ Υ (fun t i => (h t i).re) := by
    refine (hE _ ⟨C, fun t i => ?_⟩).mp fun t => ?_
    · rw [Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans (hC t i)
    · funext i
      have := congrArg (fun v => (v i).re) (hs t)
      simp only [re_mulVec_map, Pi.smul_apply, smul_eq_mul, ← Complex.ofReal_inv,
        Complex.re_ofReal_mul] at this
      simpa using this
  have him : RepSol Λ Υ (fun t i => (h t i).im) := by
    refine (hE _ ⟨C, fun t i => ?_⟩).mp fun t => ?_
    · rw [Real.norm_eq_abs]
      exact (Complex.abs_im_le_norm _).trans (hC t i)
    · funext i
      have := congrArg (fun v => (v i).im) (hs t)
      simp only [im_mulVec_map, Pi.smul_apply, smul_eq_mul, ← Complex.ofReal_inv,
        Complex.im_ofReal_mul] at this
      simpa using this
  intro t
  refine ⟨funext fun r => Complex.ext ?_ ?_, funext fun r => Complex.ext ?_ ?_⟩
  · have := congrFun (hre t).1 r
    simpa [Mpart_eq, re_mulVec_map] using this
  · have := congrFun (him t).1 r
    simpa [Mpart_eq, im_mulVec_map] using this
  · have := congrFun (hre t).2 r
    simpa [Mpart_eq, ξpart_eq, re_mulVec_map] using this
  · have := congrFun (him t).2 r
    simpa [Mpart_eq, ξpart_eq, im_mulVec_map] using this

/-- Woodford (2003), p. 553 (tool): a bounded complex solution of the homogeneous (1.20)–(1.21)
solves the homogeneous (1.18). -/
theorem homSolC_of_repSolC (hE : HomEquiv S β Λ Υ) {h : ℕ → ιZ ⊕ ιz → ℂ} (hb : BddSeq h)
    (hs : RepSolC Λ Υ h) : HomSolC S β h := by
  obtain ⟨C, hC⟩ := hb
  have hre : HomSol S β (fun t i => (h t i).re) := by
    refine (hE _ ⟨C, fun t i => ?_⟩).mpr fun t => ⟨funext fun r => ?_, funext fun r => ?_⟩
    · rw [Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans (hC t i)
    · have := congrArg (fun v => (v r).re) (hs t).1
      simpa [Mpart_eq, re_mulVec_map] using this
    · have := congrArg (fun v => (v r).re) (hs t).2
      simpa [Mpart_eq, ξpart_eq, re_mulVec_map] using this
  have him : HomSol S β (fun t i => (h t i).im) := by
    refine (hE _ ⟨C, fun t i => ?_⟩).mpr fun t => ⟨funext fun r => ?_, funext fun r => ?_⟩
    · rw [Real.norm_eq_abs]
      exact (Complex.abs_im_le_norm _).trans (hC t i)
    · have := congrArg (fun v => (v r).im) (hs t).1
      simpa [Mpart_eq, im_mulVec_map] using this
    · have := congrArg (fun v => (v r).im) (hs t).2
      simpa [Mpart_eq, ξpart_eq, im_mulVec_map] using this
  intro t
  funext i
  refine Complex.ext ?_ ?_
  · have := congrFun (hre t) i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    simp [re_mulVec_map, ← Complex.ofReal_inv, this]
  · have := congrFun (him t) i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    simp [im_mulVec_map, ← Complex.ofReal_inv, this]

/-! ### The upper bound: eigenvalues of `Λ` in the closed unit disc -/

/-- Woodford (2003), p. 557 (tool): `cmat (Mᵀ) = (cmat M)ᵀ`. -/
theorem cmat_transpose {a b : Type*} (M : Matrix a b ℝ) : cmat (Mᵀ) = (cmat M)ᵀ := rfl

/-- Woodford (2003), pp. 553, 557: **a root `λ ≠ 0` of (1.15) with `|λ| ≥ β⁻¹` gives the
eigenvalue `(βλ)⁻¹` of `Λ`.** A left null vector `w` of `A − λÎ` makes `φ_t = (βλ)^{-t} w` a
bounded solution of the homogeneous (1.18); by Proposition 8.1 its `M`-block obeys
`M_t = Λ M_{t−1}`, and it is nonzero because `ξ_t = Υ M_{t−1}`. -/
theorem charpoly_root_of_pencil_root (hE : HomEquiv S β Λ Υ) (hβ : 0 < β) {l : ℂ}
    (hl0 : l ≠ 0) (hdet : (cmat S.Ahat - l • cmat S.Ihat).det = 0) (hl : β⁻¹ ≤ ‖l‖) :
    (cmat Λ).charpoly.eval ((β : ℂ) * l)⁻¹ = 0 := by
  obtain ⟨w, hw0, hw⟩ := exists_vecMul_eq_zero_iff.mpr hdet
  have hA : cmat (S.Ahatᵀ) *ᵥ w = l • (cmat (S.Ihatᵀ) *ᵥ w) := by
    rw [← mulVec_transpose, transpose_sub, transpose_smul, sub_mulVec, smul_mulVec,
      sub_eq_zero] at hw
    rw [cmat_transpose, cmat_transpose, hw]
  set μ : ℂ := ((β : ℂ) * l)⁻¹ with hμdef
  have hβc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
  have hμl : μ * l = (β : ℂ)⁻¹ := by
    rw [hμdef]
    field_simp
  have hμn : ‖μ‖ ≤ 1 := by
    have h1 : 1 ≤ β * ‖l‖ := by
      have := mul_le_mul_of_nonneg_left hl hβ.le
      rwa [mul_inv_cancel₀ hβ.ne'] at this
    rw [hμdef, norm_inv, norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ.le]
    exact inv_le_one_of_one_le₀ h1
  let h : ℕ → ιZ ⊕ ιz → ℂ := fun t => μ ^ t • w
  have hs : HomSolC S β h := by
    intro t
    simp only [h]
    rw [mulVec_smul, mulVec_smul, hA, smul_smul, smul_smul, pow_succ, mul_assoc, hμl,
      mul_comm]
  have hb : BddSeq h := by
    refine ⟨∑ i, ‖w i‖, fun t i => ?_⟩
    simp only [h, Pi.smul_apply, smul_eq_mul, norm_mul, norm_pow]
    calc ‖μ‖ ^ t * ‖w i‖ ≤ 1 * ‖w i‖ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hμn) (norm_nonneg _)
      _ ≤ ∑ i, ‖w i‖ := by
          rw [one_mul]
          exact Finset.single_le_sum (fun j _ => norm_nonneg (w j)) (Finset.mem_univ i)
  have hr := repSolC_of_homSolC hE hb hs 0
  simp only [h, zero_add, pow_one, pow_zero, one_smul, Pi.smul_apply] at hr
  set wM : ιz → ℂ := fun r => w (Sum.inr r) with hwMdef
  have hwM : wM ≠ 0 := by
    intro h0
    apply hw0
    funext r
    rcases r with r | r
    · have := congrFun hr.2 r
      rw [h0, mulVec_zero] at this
      simpa using this
    · exact congrFun h0 r
  rw [eval_charpoly]
  refine exists_mulVec_eq_zero_iff.mp ⟨wM, hwM, ?_⟩
  have hsc : (scalar ιz μ : Matrix ιz ιz ℂ) *ᵥ wM = μ • wM := by
    funext r
    simp [scalar_apply, mulVec_diagonal]
  rw [sub_mulVec, hsc, ← hr.1]
  exact sub_eq_zero.mpr rfl

/-- Woodford (2003), p. 553 and App. G.2, p. 719: **`Λ` annihilates `ker Ẽ'`.** For `Ẽ'v = 0`
the impulse `φ_0 = (0, v)`, `φ_t = 0` (`t ≥ 1`) solves the homogeneous (1.18), so
`Λ v = M_0 = 0`. -/
theorem mulVec_eq_zero_of_ker (hE : HomEquiv S β Λ Υ) {v : ιz → ℝ} (hv : S.Etᵀ *ᵥ v = 0) :
    Λ *ᵥ v = 0 := by
  let h : ℕ → ιZ ⊕ ιz → ℝ := fun t => if t = 0 then Sum.elim 0 v else 0
  have hI : S.Ihatᵀ *ᵥ (Sum.elim 0 v : ιZ ⊕ ιz → ℝ) = 0 := by
    funext r
    rcases r with r | r
    · simp [LinearRESystem.Ihat, fromBlocks_transpose, fromBlocks_mulVec]
    · have := congrFun hv r
      simp [LinearRESystem.Ihat, fromBlocks_transpose, fromBlocks_mulVec, this]
  have hs : HomSol S β h := by
    intro t
    cases t with
    | zero => simp [h, hI]
    | succ t => simp [h]
  have hsum : ∀ r, |v r| ≤ ∑ i, |v i| := fun r =>
    Finset.single_le_sum (fun i _ => abs_nonneg (v i)) (Finset.mem_univ r)
  have hsum0 : 0 ≤ ∑ i, |v i| := Finset.sum_nonneg fun i _ => abs_nonneg (v i)
  have hb : BddSeq h := by
    refine ⟨∑ i, |v i|, fun t i => ?_⟩
    rw [Real.norm_eq_abs]
    by_cases ht : t = 0
    · rcases i with i | i
      · simp [h, ht, hsum0]
      · simpa [h, ht] using hsum i
    · simp [h, ht, hsum0]
  have := ((hE h hb).mp hs 0).1
  simp only [h, Mpart_eq] at this
  exact this.symm

/-- Woodford (2003), App. G.2, p. 719: the eigenvalue `0` of `Λ` has algebraic multiplicity at
least `n_z − rank Ẽ`. -/
theorem card_sub_rank_le_rootMultiplicity (hE : HomEquiv S β Λ Υ) :
    Fintype.card ιz - S.Et.rank ≤ (cmat Λ).charpoly.rootMultiplicity 0 := by
  have hK : Module.finrank ℝ (LinearMap.ker (S.Etᵀ.mulVecLin)) =
      Fintype.card ιz - S.Et.rank := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (S.Etᵀ.mulVecLin)
    have h2 : Module.finrank ℝ (LinearMap.range S.Etᵀ.mulVecLin) = S.Et.rank := by
      rw [← rank_transpose]
      rfl
    rw [Module.finrank_fintype_fun_eq_card, h2] at h1
    omega
  let K := LinearMap.ker (S.Etᵀ.mulVecLin)
  let b := Module.finBasis ℝ K
  let v : Fin (Module.finrank ℝ K) → ιz → ℝ := fun i => (b i : ιz → ℝ)
  have hv : LinearIndependent ℝ v :=
    b.linearIndependent.map' K.subtype (Submodule.ker_subtype K)
  have hvc : LinearIndependent ℂ (fun i => (algebraMap ℝ ℂ) ∘ v i) :=
    linearIndependent_algebraMap_comp_iff.mpr hv
  have hmem : ∀ i, (algebraMap ℝ ℂ) ∘ v i ∈ Module.End.eigenspace (toLin' (cmat Λ)) 0 := by
    intro i
    rw [Module.End.mem_eigenspace_iff, zero_smul, toLin'_apply]
    have hker : S.Etᵀ *ᵥ v i = 0 := LinearMap.mem_ker.mp (b i).2
    have h0 := mulVec_eq_zero_of_ker hE hker
    have e : (algebraMap ℝ ℂ ∘ v i) = fun j => (v i j : ℂ) := rfl
    rw [e, map_mulVec_ofReal, h0]
    funext j
    simp
  have hle := Submodule.finrank_mono (Submodule.span_le.mpr (Set.range_subset_iff.mpr hmem))
  rw [finrank_span_eq_card hvc, Fintype.card_fin, hK] at hle
  calc _ ≤ _ := hle
    _ ≤ _ := LinearMap.finrank_eigenspace_le _ _
    _ = _ := by rw [charpoly_toLin']

/-- Woodford (2003), p. 557 (tool): the roots of the characteristic polynomial of a complex
`n × n` matrix number `n`. -/
theorem card_charpoly_roots (M : Matrix ι ι ℂ) :
    Multiset.card M.charpoly.roots = Fintype.card ι := by
  rw [(splits_iff_card_roots).mp (IsAlgClosed.splits _), charpoly_natDegree_eq_dim]

/-- Woodford (2003), Proposition 8.3, p. 556, **upper half**: under Assumptions 8.3 and 8.7
(`n_Z + m` roots of (1.15) with `|μ| < β⁻¹`), `Λ` has at most `m` eigenvalues outside the
closed unit disc. -/
theorem card_outside_le (hE : HomEquiv S β Λ Υ) (hβ : 0 < β) (h83 : Assumption83 S) {m : ℕ}
    (h87 : S.stableCount β⁻¹ = Fintype.card ιZ + m) :
    Multiset.card ((cmat Λ).charpoly.roots.filter (fun μ => 1 < ‖μ‖)) ≤ m := by
  set R := (cmat Λ).charpoly.roots with hRdef
  have hR : Multiset.card R = Fintype.card ιz := card_charpoly_roots _
  have hp1 := congrArg Multiset.card (Multiset.filter_add_not (fun μ : ℂ => μ = 0) R)
  have hp2 := congrArg Multiset.card (Multiset.filter_add_not (fun μ : ℂ => ‖μ‖ ≤ 1)
    (R.filter (fun μ => ¬ μ = 0)))
  rw [Multiset.card_add] at hp1 hp2
  have hout : (R.filter (fun μ => ¬ μ = 0)).filter (fun μ => ¬ ‖μ‖ ≤ 1) =
      R.filter (fun μ => 1 < ‖μ‖) := by
    rw [Multiset.filter_filter]
    refine Multiset.filter_congr fun μ _ => ?_
    constructor
    · rintro ⟨h1, -⟩
      exact not_le.mp h1
    · intro h1
      refine ⟨not_le.mpr h1, fun h0 => ?_⟩
      rw [h0, norm_zero] at h1
      linarith
  rw [hout] at hp2
  have hzero : Multiset.card (R.filter (fun μ : ℂ => μ = 0)) =
      (cmat Λ).charpoly.rootMultiplicity 0 := by
    rw [Multiset.filter_eq', Multiset.card_replicate, count_roots]
  have hz := card_sub_rank_le_rootMultiplicity hE (S := S)
  -- the eigenvalues coming from the roots of (1.15) with `|λ| ≥ β⁻¹`
  set ST := (nonzeroRoots S).filter (fun l => β⁻¹ ≤ ‖l‖) with hST
  set f : ℂ → ℂ := fun l => ((β : ℂ) * l)⁻¹ with hf
  have hβc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
  have hmemST : ∀ l ∈ ST, l ∈ S.pencilPoly.roots ∧ l ≠ 0 ∧ β⁻¹ ≤ ‖l‖ := by
    intro l hl
    rw [hST, nonzeroRoots, Multiset.mem_filter, Multiset.mem_filter] at hl
    exact ⟨hl.1.1, hl.1.2, hl.2⟩
  have hnd : (ST.map f).Nodup := by
    refine Multiset.Nodup.map_on (fun x hx y hy hxy => ?_) (h83.nodup.filter _)
    have hx0 := (hmemST x hx).2.1
    have hy0 := (hmemST y hy).2.1
    simp only [hf, _root_.inv_inj] at hxy
    exact mul_left_cancel₀ hβc hxy
  have hsub : ST.map f ⊆ (R.filter (fun μ => ¬ μ = 0)).filter (fun μ => ‖μ‖ ≤ 1) := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Multiset.mem_map.mp hx
    obtain ⟨hlr, hl0, hln⟩ := hmemST l hl
    have hdet : (cmat S.Ahat - l • cmat S.Ihat).det = 0 := by
      rw [← pencilPoly_eval]
      exact (mem_roots h83.regular).mp hlr
    have hroot := charpoly_root_of_pencil_root hE hβ hl0 hdet hln
    refine Multiset.mem_filter.mpr ⟨Multiset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · exact (mem_roots (charpoly_monic _).ne_zero).mpr hroot
    · simp only [hf]
      exact inv_ne_zero (mul_ne_zero hβc hl0)
    · simp only [hf]
      have h1 : 1 ≤ β * ‖l‖ := by
        have := mul_le_mul_of_nonneg_left hln hβ.le
        rwa [mul_inv_cancel₀ hβ.ne'] at this
      rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ.le]
      exact inv_le_one_of_one_le₀ h1
  have hmid := Multiset.card_le_card ((Multiset.le_iff_subset hnd).mpr hsub)
  rw [Multiset.card_map] at hmid
  -- counting the roots of (1.15)
  have hsplit := congrArg Multiset.card
    (Multiset.filter_add_not (fun l : ℂ => ‖l‖ < β⁻¹) (nonzeroRoots S))
  rw [Multiset.card_add] at hsplit
  have hnot : (nonzeroRoots S).filter (fun l => ¬ ‖l‖ < β⁻¹) = ST := by
    rw [hST]
    exact Multiset.filter_congr fun l _ => not_lt
  rw [hnot] at hsplit
  have hless : S.pencilPoly.roots.filter (fun μ => μ ≠ 0 ∧ ‖μ‖ < β⁻¹) =
      (nonzeroRoots S).filter (fun l => ‖l‖ < β⁻¹) := by
    rw [nonzeroRoots, Multiset.filter_filter]
    exact Multiset.filter_congr fun l _ => and_comm
  have h87' := h87
  unfold LinearRESystem.stableCount at h87'
  rw [hless, Fintype.card_sum] at h87'
  have hrA := rank_le_card_width S.Ahat
  have hrE := rank_le_card_width S.Et
  rw [Fintype.card_sum] at hrA
  have hc := h83.card_nonzero
  have hAr := card_le_rank_Ahat S
  omega

/-! ### The lower bound: eigenvalues of `Λ` in the open unit disc -/

/-- Woodford (2003), p. 557: the vectors `v` whose orbit `Λᵗ v` is bounded (a subspace). -/
def orbitBdd (M : Matrix ιz ιz ℂ) : Submodule ℂ (ιz → ℂ) where
  carrier := {v | ∃ C, ∀ k i, ‖((M ^ k) *ᵥ v) i‖ ≤ C}
  add_mem' := by
    rintro v w ⟨C, hC⟩ ⟨D, hD⟩
    refine ⟨C + D, fun k i => ?_⟩
    rw [mulVec_add, Pi.add_apply]
    exact (norm_add_le _ _).trans (add_le_add (hC k i) (hD k i))
  zero_mem' := ⟨0, fun k i => by simp⟩
  smul_mem' := by
    rintro c v ⟨C, hC⟩
    refine ⟨‖c‖ * C, fun k i => ?_⟩
    rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hC k i) (norm_nonneg c)

/-- Woodford (2003), p. 557: the bounded-orbit subspace is invariant under `Λ`. -/
theorem pow_mulVec_mem_orbitBdd {M : Matrix ιz ιz ℂ} {v : ιz → ℂ} (hv : v ∈ orbitBdd M)
    (j : ℕ) : (M ^ j) *ᵥ v ∈ orbitBdd M := by
  obtain ⟨C, hC⟩ := hv
  exact ⟨C, fun k i => by rw [mulVec_mulVec, ← pow_add]; exact hC (k + j) i⟩

/-- Woodford (2003), p. 557: generalised eigenvectors of `Λ` for an eigenvalue `|μ| < 1` have
bounded orbits (induction on the height `k` of `(Λ − μ)^k v = 0`). -/
theorem mem_orbitBdd_of_pow (M : Matrix ιz ιz ℂ) {μ : ℂ} (hμ : ‖μ‖ < 1) :
    ∀ (k : ℕ) (v : ιz → ℂ), ((M - μ • 1) ^ k) *ᵥ v = 0 → v ∈ orbitBdd M := by
  intro k
  induction k with
  | zero =>
    intro v hv
    rw [pow_zero, one_mulVec] at hv
    rw [hv]
    exact (orbitBdd M).zero_mem
  | succ k ih =>
    intro v hv
    set w := (M - μ • 1) *ᵥ v with hw
    have hw0 : ((M - μ • 1) ^ k) *ᵥ w = 0 := by
      rw [hw, mulVec_mulVec, ← pow_succ]
      exact hv
    obtain ⟨C, hC⟩ := ih w hw0
    have hMv : M *ᵥ v = w + μ • v := by
      rw [hw, sub_mulVec, smul_mulVec, one_mulVec]
      abel
    have hstep : ∀ t, (M ^ (t + 1)) *ᵥ v = (M ^ t) *ᵥ w + μ • ((M ^ t) *ᵥ v) := by
      intro t
      rw [pow_succ, ← mulVec_mulVec, hMv, mulVec_add, mulVec_smul]
    have h1 : 0 < 1 - ‖μ‖ := by linarith
    set B := max (∑ i, ‖v i‖) (C / (1 - ‖μ‖)) with hB
    have hCB : C ≤ (1 - ‖μ‖) * B := by
      have := le_max_right (∑ i, ‖v i‖) (C / (1 - ‖μ‖))
      rw [← hB, div_le_iff₀ h1] at this
      linarith
    refine ⟨B, fun t => ?_⟩
    induction t with
    | zero =>
      intro i
      rw [pow_zero, one_mulVec]
      exact (Finset.single_le_sum (fun j _ => norm_nonneg (v j)) (Finset.mem_univ i)).trans
        (le_max_left _ _)
    | succ t iht =>
      intro i
      rw [hstep, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc ‖((M ^ t) *ᵥ w) i + μ * ((M ^ t) *ᵥ v) i‖ ≤ C + ‖μ‖ * B := by
            refine (norm_add_le _ _).trans (add_le_add (hC t i) ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (iht i) (norm_nonneg _)
        _ ≤ B := by linarith

/-- Woodford (2003), p. 557: the generalised eigenspace of `Λ` for `|μ| < 1` consists of vectors
with bounded orbits. -/
theorem maxGenEigenspace_le_orbitBdd (M : Matrix ιz ιz ℂ) {μ : ℂ} (hμ : ‖μ‖ < 1) :
    Module.End.maxGenEigenspace (toLin' M) μ ≤ orbitBdd M := by
  intro v hv
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hv
  have e : toLin' (M - μ • 1) = toLin' M - μ • 1 := by
    rw [map_sub, map_smul, toLin'_one]
    rfl
  rw [← e, ← toLin'_pow, toLin'_apply] at hk
  exact mem_orbitBdd_of_pow M hμ k v hk

/-- Woodford (2003), p. 557 (tool): the number of roots of `p` satisfying `q` is the sum of their
multiplicities. -/
theorem card_filter_roots_eq_sum (p : ℂ[X]) (q : ℂ → Prop) [DecidablePred q] :
    Multiset.card (p.roots.filter q) =
      ∑ μ ∈ (p.roots.filter q).toFinset, p.rootMultiplicity μ := by
  rw [← Multiset.toFinset_sum_count_eq]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [Multiset.mem_toFinset, Multiset.mem_filter] at hμ
  rw [Multiset.count_filter_of_pos hμ.2, count_roots]

/-- Woodford (2003), p. 557: the number of eigenvalues of `Λ` in the open unit disc (with
algebraic multiplicity) is at most the dimension of the bounded-orbit subspace. -/
theorem card_inside_le_finrank (M : Matrix ιz ιz ℂ) :
    Multiset.card (M.charpoly.roots.filter (fun μ => ‖μ‖ < 1)) ≤
      Module.finrank ℂ (orbitBdd M) := by
  rw [card_filter_roots_eq_sum]
  have h1 : ∀ μ, M.charpoly.rootMultiplicity μ =
      Module.finrank ℂ (Module.End.maxGenEigenspace (toLin' M) μ) := by
    intro μ
    rw [LinearMap.finrank_maxGenEigenspace_eq, charpoly_toLin']
  simp_rw [h1]
  rw [← finrank_finset_sup (Module.End.independent_maxGenEigenspace _)]
  refine Submodule.finrank_mono (Finset.sup_le fun μ hμ => maxGenEigenspace_le_orbitBdd M ?_)
  exact (Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hμ)).2

/-- Woodford (2003), p. 540: the multiplier vector `φ = (Υ M, M)` built from `M` by (1.21). -/
def Gmap (Υc : Matrix ιZ ιz ℂ) : (ιz → ℂ) →ₗ[ℂ] (ιZ ⊕ ιz → ℂ) where
  toFun w := Sum.elim (Υc *ᵥ w) w
  map_add' w w' := by
    funext r
    rcases r with r | r <;> simp [mulVec_add]
  map_smul' c w := by
    funext r
    rcases r with r | r <;> simp [mulVec_smul]

omit [Fintype ιZ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 540: `M ↦ (Υ M, M)` is injective. -/
theorem Gmap_injective (Υc : Matrix ιZ ιz ℂ) : Function.Injective (Gmap Υc) :=
  fun _ _ h => funext fun r => congrFun h (Sum.inr r)

omit [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 557 (tool): a bound on `φ = (Υ M, M)` from a bound on `M`. -/
theorem norm_Gmap_le (Υc : Matrix ιZ ιz ℂ) {w : ιz → ℂ} {C : ℝ} (hC0 : 0 ≤ C)
    (hw : ∀ j, ‖w j‖ ≤ C) (i : ιZ ⊕ ιz) :
    ‖Gmap Υc w i‖ ≤ (∑ i', ∑ j, ‖Υc i' j‖) * C + C := by
  have hK0 : 0 ≤ (∑ i', ∑ j, ‖Υc i' j‖) * C :=
    mul_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) hC0
  rcases i with i | i
  · have := norm_mulVec_le Υc hC0 hw i
    change ‖(Υc *ᵥ w) i‖ ≤ _
    linarith
  · change ‖w i‖ ≤ _
    linarith [hw i]

/-- Woodford (2003), p. 557 (tool): `‖x · y‖ ≤ (∑ ‖x_i‖) B` when every `‖y_i‖ ≤ B`. -/
theorem norm_dotProduct_le {κ : Type*} [Fintype κ] (x : κ → ℂ) {y : κ → ℂ} {B : ℝ}
    (hy : ∀ i, ‖y i‖ ≤ B) : ‖x ⬝ᵥ y‖ ≤ (∑ i, ‖x i‖) * B := by
  calc ‖x ⬝ᵥ y‖ = ‖∑ i, x i * y i‖ := rfl
    _ ≤ ∑ i, ‖x i * y i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖x i‖ * B := Finset.sum_le_sum fun i _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hy i) (norm_nonneg _)
    _ = (∑ i, ‖x i‖) * B := by rw [Finset.sum_mul]

/-- Woodford (2003), pp. 553, 557: **the homogeneous (1.18) on the bounded-orbit subspace.** For
`v` with bounded orbit, `φ_t = (Υ Λᵗ v, Λᵗ v)` is a bounded solution of the homogeneous
(1.20)–(1.21), hence of (1.18): `A' φ(Λ v) = β⁻¹ Î' φ(v)`. -/
theorem star_of_orbitBdd (hE : HomEquiv S β Λ Υ) {v : ιz → ℂ} (hv : v ∈ orbitBdd (cmat Λ)) :
    cmat (S.Ahatᵀ) *ᵥ Gmap (cmat Υ) (cmat Λ *ᵥ v) =
      (β : ℂ)⁻¹ • (cmat (S.Ihatᵀ) *ᵥ Gmap (cmat Υ) v) := by
  obtain ⟨C, hC⟩ := hv
  set h : ℕ → ιZ ⊕ ιz → ℂ := fun t => Gmap (cmat Υ) ((cmat Λ ^ t) *ᵥ v) with hh
  have hrep : RepSolC Λ Υ h := by
    intro t
    refine ⟨funext fun r => ?_, funext fun r => ?_⟩
    · change ((cmat Λ ^ (t + 1)) *ᵥ v) r = (cmat Λ *ᵥ ((cmat Λ ^ t) *ᵥ v)) r
      rw [pow_succ', mulVec_mulVec]
    · rfl
  have hb : BddSeq h := by
    refine ⟨(∑ i', ∑ j, ‖cmat Υ i' j‖) * max C 0 + max C 0, fun t i => ?_⟩
    exact norm_Gmap_le (cmat Υ) (le_max_right C 0) (fun j => (hC t j).trans (le_max_left _ _)) i
  have := homSolC_of_repSolC hE hb hrep 0
  simp only [hh, zero_add, pow_one, pow_zero, one_mulVec] at this
  exact this

/-- Woodford (2003), pp. 553, 557: **the constraints from the roots `|λ| < β⁻¹`.** If
`A u = λ Î u` with `|λ| < β⁻¹` (including `λ = 0`, `A u = 0`), then every `φ(v) = (Υ v, v)` with
`v` of bounded orbit satisfies `(Î u) · φ(v) = 0`: along the solution the scalar
`s_t = (Îu)·φ_t` obeys `λ s_{t+1} = β⁻¹ s_t`, which is explosive unless `s ≡ 0`. -/
theorem constraint_of_orbitBdd (hE : HomEquiv S β Λ Υ) (hβ : 0 < β) {u : ιZ ⊕ ιz → ℂ} {l : ℂ}
    (hu : cmat S.Ahat *ᵥ u = l • (cmat S.Ihat *ᵥ u)) (hl : ‖l‖ < β⁻¹) {v : ιz → ℂ}
    (hv : v ∈ orbitBdd (cmat Λ)) : (cmat S.Ihat *ᵥ u) ⬝ᵥ Gmap (cmat Υ) v = 0 := by
  set s : ℕ → ℂ := fun k => (cmat S.Ihat *ᵥ u) ⬝ᵥ Gmap (cmat Υ) ((cmat Λ ^ k) *ᵥ v) with hs
  have hdot : ∀ (A : Matrix (ιZ ⊕ ιz) (ιZ ⊕ ιz) ℝ) (x : ιZ ⊕ ιz → ℂ),
      (cmat A *ᵥ u) ⬝ᵥ x = u ⬝ᵥ (cmat (Aᵀ) *ᵥ x) := by
    intro A x
    rw [cmat_transpose, dotProduct_mulVec, vecMul_transpose]
  have hβc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
  have hrel : ∀ k, l * s (k + 1) = (β : ℂ)⁻¹ * s k := by
    intro k
    have hst := star_of_orbitBdd hE (pow_mulVec_mem_orbitBdd hv k)
    have e : (cmat Λ ^ (k + 1)) *ᵥ v = cmat Λ *ᵥ ((cmat Λ ^ k) *ᵥ v) := by
      rw [pow_succ', mulVec_mulVec]
    calc l * s (k + 1) = (l • (cmat S.Ihat *ᵥ u)) ⬝ᵥ
          Gmap (cmat Υ) (cmat Λ *ᵥ ((cmat Λ ^ k) *ᵥ v)) := by
          rw [smul_dotProduct, smul_eq_mul, hs]
          simp only
          rw [e]
      _ = u ⬝ᵥ (cmat (S.Ahatᵀ) *ᵥ Gmap (cmat Υ) (cmat Λ *ᵥ ((cmat Λ ^ k) *ᵥ v))) := by
          rw [← hu, hdot]
      _ = (β : ℂ)⁻¹ * s k := by
          rw [hst, dotProduct_smul, ← hdot, smul_eq_mul]
  obtain ⟨C, hC⟩ := hv
  have hbd : ∀ k, ‖s k‖ ≤ (∑ i, ‖(cmat S.Ihat *ᵥ u) i‖) *
      ((∑ i', ∑ j, ‖cmat Υ i' j‖) * max C 0 + max C 0) := by
    intro k
    refine norm_dotProduct_le _ fun i => ?_
    exact norm_Gmap_le (cmat Υ) (le_max_right C 0) (fun j => (hC k j).trans (le_max_left _ _)) i
  have hs0 : s 0 = (cmat S.Ihat *ᵥ u) ⬝ᵥ Gmap (cmat Υ) v := by
    simp only [hs, pow_zero, one_mulVec]
  rw [← hs0]
  by_cases hl0 : l = 0
  · have := hrel 0
    rw [hl0, zero_mul] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (inv_ne_zero hβc)
  · set ρ : ℂ := (β : ℂ)⁻¹ / l with hρ
    have hρn : 1 < ‖ρ‖ := by
      rw [hρ, norm_div, norm_inv, Complex.norm_real, Real.norm_of_nonneg hβ.le]
      rw [one_lt_div (norm_pos_iff.mpr hl0)]
      exact hl
    have hpow : ∀ k, s k = ρ ^ k * s 0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have h1 := hrel k
        have h2 : s (k + 1) = ρ * s k := by
          rw [hρ, div_mul_eq_mul_div, eq_div_iff hl0]
          linear_combination h1
        rw [h2, ih, pow_succ]
        ring
    by_contra h0
    set D := (∑ i, ‖(cmat S.Ihat *ᵥ u) i‖) * ((∑ i', ∑ j, ‖cmat Υ i' j‖) * max C 0 + max C 0)
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (D / ‖s 0‖) hρn
    have h3 := hbd k
    rw [hpow, norm_mul, norm_pow] at h3
    have h4 := (div_lt_iff₀ (norm_pos_iff.mpr h0)).mp hk
    linarith

/-- Woodford (2003), Proposition 8.3, p. 556, **the dimension count**: under Assumptions 8.3 and
8.7 the bounded-orbit subspace of `Λ` has dimension at most `n_z − m`. The `n − rank A` null
vectors of `A` and one eigenvector of the pencil for each nonzero root `|λ| < β⁻¹` give `n_Z + m`
constraints `(Î u)·φ = 0` (`constraint_of_orbitBdd`); they are linearly independent because the
`Î u` are eigenvectors of `Î (A − μ₀ Î)⁻¹` (`μ₀` a regular point) for the distinct eigenvalues
`(λ − μ₀)⁻¹`. -/
theorem finrank_orbitBdd_le (hE : HomEquiv S β Λ Υ) (hβ : 0 < β) (h83 : Assumption83 S)
    {m : ℕ} (h87 : S.stableCount β⁻¹ = Fintype.card ιZ + m) :
    Module.finrank ℂ (orbitBdd (cmat Λ)) + m ≤ Fintype.card ιz := by
  classical
  set Ac := cmat S.Ahat with hAc
  set Ic := cmat S.Ihat with hIc
  -- a regular point `μ₀ ≠ 0` of the pencil
  obtain ⟨μ0, hμ0⟩ := Infinite.exists_notMem_finset (insert (0 : ℂ) S.pencilPoly.roots.toFinset)
  have hμ00 : μ0 ≠ 0 := fun h => hμ0 (by simp [h])
  have hroot_ne : ∀ l ∈ S.pencilPoly.roots, l ≠ μ0 := fun l hl h =>
    hμ0 (by rw [Finset.mem_insert, Multiset.mem_toFinset]; right; rw [← h]; exact hl)
  have hdet0 : (Ac - μ0 • Ic).det ≠ 0 := by
    intro h
    refine hroot_ne μ0 ((mem_roots h83.regular).mpr ?_) rfl
    rw [IsRoot, pencilPoly_eval]
    exact h
  set N := Ac - μ0 • Ic with hN
  have hRN : N⁻¹ * N = 1 := nonsing_inv_mul N (isUnit_iff_ne_zero.mpr hdet0)
  set K := Ic * N⁻¹ with hK
  have hkey : ∀ (u : ιZ ⊕ ιz → ℂ) (l : ℂ), Ac *ᵥ u = l • (Ic *ᵥ u) → l ≠ μ0 →
      K *ᵥ (Ic *ᵥ u) = (l - μ0)⁻¹ • (Ic *ᵥ u) := by
    intro u l hu hl
    have hNu : N *ᵥ u = (l - μ0) • (Ic *ᵥ u) := by
      rw [hN, sub_mulVec, smul_mulVec, hu, sub_smul]
    have hl' : l - μ0 ≠ 0 := sub_ne_zero.mpr hl
    have hRu : N⁻¹ *ᵥ (Ic *ᵥ u) = (l - μ0)⁻¹ • u := by
      have h1 : u = N⁻¹ *ᵥ (N *ᵥ u) := by rw [mulVec_mulVec, hRN, one_mulVec]
      rw [hNu, mulVec_smul] at h1
      conv_rhs => rw [h1]
      rw [smul_smul, inv_mul_cancel₀ hl', one_smul]
    rw [hK, ← mulVec_mulVec, hRu, mulVec_smul]
  have hinj : ∀ x, Ac *ᵥ x = 0 → Ic *ᵥ x = 0 → x = 0 := by
    intro x h1 h2
    have h3 : N *ᵥ x = 0 := by rw [hN, sub_mulVec, smul_mulVec, h1, h2, smul_zero, sub_zero]
    rw [← one_mulVec x, ← hRN, ← mulVec_mulVec, h3, mulVec_zero]
  -- the null vectors of `A`
  let KA := LinearMap.ker (S.Ahat.mulVecLin)
  let bA := Module.finBasis ℝ KA
  have hr0' : Module.finrank ℝ (LinearMap.ker (S.Ahat.mulVecLin)) + S.Ahat.rank =
      Fintype.card (ιZ ⊕ ιz) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (S.Ahat.mulVecLin)
    rw [Module.finrank_fintype_fun_eq_card] at h1
    have h2 : Module.finrank ℝ (LinearMap.range S.Ahat.mulVecLin) = S.Ahat.rank := rfl
    omega
  have hr0 : Module.finrank ℝ KA + S.Ahat.rank = Fintype.card (ιZ ⊕ ιz) := hr0'
  let kv : Fin (Module.finrank ℝ KA) → ιZ ⊕ ιz → ℂ :=
    fun i => (algebraMap ℝ ℂ) ∘ (bA i : ιZ ⊕ ιz → ℝ)
  have hkvA : ∀ i, Ac *ᵥ kv i = 0 := by
    intro i
    have hker : S.Ahat *ᵥ (bA i : ιZ ⊕ ιz → ℝ) = 0 := LinearMap.mem_ker.mp (bA i).2
    have e : kv i = fun j => ((bA i : ιZ ⊕ ιz → ℝ) j : ℂ) := rfl
    rw [hAc, e, map_mulVec_ofReal, hker]
    funext j
    simp
  have hkv : LinearIndependent ℂ kv :=
    linearIndependent_algebraMap_comp_iff.mpr
      (bA.linearIndependent.map' KA.subtype (Submodule.ker_subtype KA))
  let c1 : Fin (Module.finrank ℝ KA) → ιZ ⊕ ιz → ℂ := fun i => Ic *ᵥ kv i
  have hspanA : Submodule.span ℂ (Set.range kv) ≤ LinearMap.ker (toLin' Ac) :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i => by
      rw [SetLike.mem_coe, LinearMap.mem_ker, toLin'_apply]
      exact hkvA i)
  have hc1 : LinearIndependent ℂ c1 := by
    refine hkv.map (f := toLin' Ic) ?_
    rw [disjoint_iff]
    refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
    obtain ⟨hxs, hxk⟩ := Submodule.mem_inf.mp hx
    have hA : Ac *ᵥ x = 0 := by
      have := hspanA hxs
      rwa [LinearMap.mem_ker, toLin'_apply] at this
    rw [LinearMap.mem_ker, toLin'_apply] at hxk
    exact hinj x hA hxk
  -- one eigenvector of the pencil for each nonzero root `|λ| < β⁻¹`
  set T := (S.pencilPoly.roots.filter (fun l => l ≠ 0 ∧ ‖l‖ < β⁻¹)).toFinset with hT
  have hTmem : ∀ l ∈ T, l ∈ S.pencilPoly.roots ∧ l ≠ 0 ∧ ‖l‖ < β⁻¹ := by
    intro l hl
    rw [hT, Multiset.mem_toFinset, Multiset.mem_filter] at hl
    exact ⟨hl.1, hl.2.1, hl.2.2⟩
  have hex : ∀ l : T, ∃ u : ιZ ⊕ ιz → ℂ, u ≠ 0 ∧ (Ac - (l : ℂ) • Ic) *ᵥ u = 0 := by
    intro l
    have hdet : (Ac - (l : ℂ) • Ic).det = 0 := by
      rw [hAc, hIc, ← pencilPoly_eval]
      exact (mem_roots h83.regular).mp (hTmem l l.2).1
    exact exists_mulVec_eq_zero_iff.mpr hdet
  choose U hU0 hU using hex
  have hUA : ∀ l : T, Ac *ᵥ U l = (l : ℂ) • (Ic *ᵥ U l) := by
    intro l
    have := hU l
    rw [sub_mulVec, smul_mulVec, sub_eq_zero] at this
    exact this
  let c2 : T → ιZ ⊕ ιz → ℂ := fun l => Ic *ᵥ U l
  let e : T → ℂ := fun l => ((l : ℂ) - μ0)⁻¹
  have heig : ∀ l : T, Module.End.HasEigenvector (toLin' K) (e l) (c2 l) := by
    intro l
    refine Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
    · rw [toLin'_apply]
      exact hkey (U l) l (hUA l) (hroot_ne l (hTmem l l.2).1)
    · intro h0
      refine hU0 l (hinj _ ?_ h0)
      rw [hUA l]
      change (l : ℂ) • c2 l = 0
      rw [h0, smul_zero]
  have he : Function.Injective e := by
    intro a b hab
    simp only [e, _root_.inv_inj, sub_left_inj] at hab
    exact Subtype.ext hab
  have hc2 : LinearIndependent ℂ c2 :=
    Module.End.eigenvectors_linearIndependent' (toLin' K) e he c2 heig
  -- the two blocks lie in different eigenspaces of `Î (A − μ₀ Î)⁻¹`
  have he0 : ((0 : ℂ) - μ0)⁻¹ ∉ Set.range e := by
    rintro ⟨l, hl⟩
    simp only [e, _root_.inv_inj, sub_left_inj] at hl
    exact (hTmem l l.2).2.1 hl
  have hspan1 : Submodule.span ℂ (Set.range c1) ≤
      Module.End.eigenspace (toLin' K) ((0 : ℂ) - μ0)⁻¹ := by
    refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i => ?_)
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, toLin'_apply]
    exact hkey (kv i) 0 (by rw [hkvA i, zero_smul]) (Ne.symm hμ00)
  have hspan2 : Submodule.span ℂ (Set.range c2) ≤
      ⨆ x ∈ Set.range e, Module.End.eigenspace (toLin' K) x := by
    refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun l => ?_)
    have h1 : c2 l ∈ Module.End.eigenspace (toLin' K) (e l) :=
      (Module.End.hasEigenvector_iff.mp (heig l)).1
    exact (le_biSup (fun x => Module.End.eigenspace (toLin' K) x) (Set.mem_range_self l)) h1
  have hdis : Disjoint (Submodule.span ℂ (Set.range c1)) (Submodule.span ℂ (Set.range c2)) :=
    ((Module.End.eigenspaces_iSupIndep (toLin' K)).disjoint_biSup he0).mono hspan1 hspan2
  have hc : LinearIndependent ℂ (Sum.elim c1 c2) := hc1.sum_type hc2 hdis
  -- every constraint annihilates `φ(v)` for `v` of bounded orbit
  have hconstr : ∀ j, ∀ v ∈ orbitBdd (cmat Λ), Sum.elim c1 c2 j ⬝ᵥ Gmap (cmat Υ) v = 0 := by
    intro j v hv
    rcases j with i | l
    · exact constraint_of_orbitBdd hE hβ (u := kv i) (l := 0) (by rw [hkvA i, zero_smul])
        (by simpa using hβ) hv
    · exact constraint_of_orbitBdd hE hβ (hUA l) (hTmem l l.2).2.2 hv
  -- the dimension count
  let Cm : Matrix (Fin (Module.finrank ℝ KA) ⊕ T) (ιZ ⊕ ιz) ℂ := Matrix.of (Sum.elim c1 c2)
  have hrank : Cm.rank = Fintype.card (Fin (Module.finrank ℝ KA) ⊕ T) := by
    rw [rank_eq_finrank_span_row]
    exact finrank_span_eq_card hc
  have hker := LinearMap.finrank_range_add_finrank_ker Cm.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hker
  have hrk : Module.finrank ℂ (LinearMap.range Cm.mulVecLin) = Cm.rank := rfl
  have hmap : (orbitBdd (cmat Λ)).map (Gmap (cmat Υ)) ≤ LinearMap.ker Cm.mulVecLin := by
    rintro x ⟨v, hv, rfl⟩
    rw [LinearMap.mem_ker, mulVecLin_apply]
    funext j
    exact hconstr j v hv
  have hfin := Submodule.finrank_mono hmap
  rw [← (Submodule.equivMapOfInjective _ (Gmap_injective (cmat Υ)) _).finrank_eq] at hfin
  -- the number of constraints is `n_Z + m`
  have hnd : (S.pencilPoly.roots.filter (fun l => l ≠ 0 ∧ ‖l‖ < β⁻¹)).Nodup := by
    refine Multiset.nodup_of_le ?_ h83.nodup
    exact Multiset.monotone_filter_right _ fun l hl => hl.1
  have hcardT : T.card = Multiset.card
      (S.pencilPoly.roots.filter (fun l => l ≠ 0 ∧ ‖l‖ < β⁻¹)) :=
    Multiset.toFinset_card_of_nodup hnd
  have h87' := h87
  unfold LinearRESystem.stableCount at h87'
  rw [Fintype.card_sum] at h87' hr0 hker
  rw [hrank, Fintype.card_sum, Fintype.card_fin, Fintype.card_coe, hcardT] at hrk
  have hrA := rank_le_card_width S.Ahat
  rw [Fintype.card_sum] at hrA
  omega

/-- Woodford (2003), Proposition 8.3, p. 556, **lower half**: under Assumptions 8.3 and 8.7,
`Λ` has at most `n_z − m` eigenvalues in the open unit disc. -/
theorem card_inside_le (hE : HomEquiv S β Λ Υ) (hβ : 0 < β) (h83 : Assumption83 S) {m : ℕ}
    (h87 : S.stableCount β⁻¹ = Fintype.card ιZ + m) :
    Multiset.card ((cmat Λ).charpoly.roots.filter (fun μ => ‖μ‖ < 1)) + m ≤
      Fintype.card ιz :=
  (Nat.add_le_add_right (card_inside_le_finrank _) m).trans (finrank_orbitBdd_le hE hβ h83 h87)

/-- Woodford (2003), pp. 553, 557: **an eigenvalue of `Λ` on the unit circle forces a root of
(1.15) on `|λ| = β⁻¹`.** An eigenvector `v`, `|μ| = 1`, has a bounded orbit, so
`A' φ(v) μ = β⁻¹ Î' φ(v)`, i.e. `(A − (βμ)⁻¹ Î)' φ(v) = 0` with `φ(v) ≠ 0`. -/
theorem pencil_root_of_circle_eigenvalue (hE : HomEquiv S β Λ Υ) (hβ : 0 < β)
    (hreg : S.pencilPoly ≠ 0) {μ : ℂ} (hμ : ‖μ‖ = 1) (hroot : (cmat Λ).charpoly.eval μ = 0) :
    ∃ l ∈ S.pencilPoly.roots, ‖l‖ = β⁻¹ := by
  rw [eval_charpoly] at hroot
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.mpr hroot
  have hΛv : cmat Λ *ᵥ v = μ • v := by
    rw [sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    funext r
    simp [scalar_apply, mulVec_diagonal]
  have hpow : ∀ k, (cmat Λ ^ k) *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hΛv, smul_smul]
      congr 1
  have hvb : v ∈ orbitBdd (cmat Λ) := by
    refine ⟨∑ i, ‖v i‖, fun k i => ?_⟩
    rw [hpow, Pi.smul_apply, smul_eq_mul, norm_mul, norm_pow, hμ, one_pow, one_mul]
    exact Finset.single_le_sum (fun j _ => norm_nonneg (v j)) (Finset.mem_univ i)
  have hst := star_of_orbitBdd hE hvb
  rw [hΛv, map_smul, mulVec_smul] at hst
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp at hμ
  have hβc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
  set l : ℂ := ((β : ℂ) * μ)⁻¹ with hl
  have hAG : cmat (S.Ahatᵀ) *ᵥ Gmap (cmat Υ) v = l • (cmat (S.Ihatᵀ) *ᵥ Gmap (cmat Υ) v) := by
    have h2 := congrArg (fun x => μ⁻¹ • x) hst
    simp only [smul_smul, inv_mul_cancel₀ hμ0, one_smul] at h2
    rw [h2, hl, mul_inv, mul_comm]
  have hgv : (cmat S.Ahat - l • cmat S.Ihat)ᵀ *ᵥ Gmap (cmat Υ) v = 0 := by
    rw [transpose_sub, transpose_smul, sub_mulVec, smul_mulVec, ← cmat_transpose,
      ← cmat_transpose, hAG, sub_self]
  have hGv0 : Gmap (cmat Υ) v ≠ 0 := fun h =>
    hv0 (Gmap_injective (cmat Υ) (by rw [h, map_zero]))
  have hdet : (cmat S.Ahat - l • cmat S.Ihat).det = 0 := by
    rw [← det_transpose]
    exact exists_mulVec_eq_zero_iff.mp ⟨_, hGv0, hgv⟩
  refine ⟨l, (mem_roots hreg).mpr (by rw [IsRoot, pencilPoly_eval]; exact hdet), ?_⟩
  rw [hl, norm_inv, norm_mul, hμ, mul_one, Complex.norm_real, Real.norm_of_nonneg hβ.le]

/-- Woodford (2003), Proposition 8.3, pp. 556–557, for any `Λ` representing the bounded
solutions of the homogeneous (1.18) as in Proposition 8.1: `Λ` has at most `m` eigenvalues
outside the closed unit disc and at least `m` outside the open one. -/
theorem bounds_of_homEquiv (hE : HomEquiv S β Λ Υ) (hβ : 0 < β) (h83 : Assumption83 S)
    {m : ℕ} (h87 : S.stableCount β⁻¹ = Fintype.card ιZ + m) :
    zerosInside (alpha Λ) ≤ m ∧ m ≤ zerosInside (alpha Λ) + zerosOnCircle (alpha Λ) := by
  rw [zerosInside_alpha, zerosOnCircle_alpha]
  refine ⟨card_outside_le hE hβ h83 h87, ?_⟩
  have hin := card_inside_le hE hβ h83 h87
  have hR : Multiset.card (cmat Λ).charpoly.roots = Fintype.card ιz := card_charpoly_roots _
  set R := (cmat Λ).charpoly.roots
  have hp1 := congrArg Multiset.card (Multiset.filter_add_not (fun μ : ℂ => ‖μ‖ < 1) R)
  have hp2 := congrArg Multiset.card (Multiset.filter_add_not (fun μ : ℂ => 1 < ‖μ‖)
    (R.filter (fun μ => ¬ ‖μ‖ < 1)))
  rw [Multiset.card_add] at hp1 hp2
  have e1 : (R.filter (fun μ => ¬ ‖μ‖ < 1)).filter (fun μ => 1 < ‖μ‖) =
      R.filter (fun μ => 1 < ‖μ‖) := by
    rw [Multiset.filter_filter]
    exact Multiset.filter_congr fun μ _ => ⟨fun h => h.1, fun h => ⟨h, by linarith⟩⟩
  have e2 : (R.filter (fun μ => ¬ ‖μ‖ < 1)).filter (fun μ => ¬ 1 < ‖μ‖) =
      R.filter (fun μ => ‖μ‖ = 1) := by
    rw [Multiset.filter_filter]
    refine Multiset.filter_congr fun μ _ => ⟨fun h => ?_, fun h => ⟨?_, ?_⟩⟩
    · exact le_antisymm (not_lt.mp h.1) (not_lt.mp h.2)
    · rw [h]
      exact lt_irrefl 1
    · rw [h]
      exact lt_irrefl 1
  rw [e1, e2] at hp2
  omega

/-- Woodford (2003), pp. 557–558: if (1.15) has no root with `|λ| = β⁻¹`, `α(L) = det(I − ΛL)`
has no zero on the unit circle. -/
theorem zerosOnCircle_eq_zero (hE : HomEquiv S β Λ Υ) (hβ : 0 < β) (hreg : S.pencilPoly ≠ 0)
    (hcirc : ∀ l ∈ S.pencilPoly.roots, ‖l‖ ≠ β⁻¹) : zerosOnCircle (alpha Λ) = 0 := by
  rw [zerosOnCircle_alpha, Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro μ hμ h1
  obtain ⟨l, hl, hln⟩ := pencil_root_of_circle_eigenvalue hE hβ hreg h1
    ((mem_roots (charpoly_monic _).ne_zero).mp hμ)
  exact hcirc l hl hln

/-- Woodford (2003), Proposition 8.3, pp. 556–557, for any `Λ` representing the bounded
solutions of the homogeneous (1.18): if (1.15) has no root with `|λ| = β⁻¹`, `α(L) = det(I − ΛL)`
has exactly `m` zeros inside the unit circle. -/
theorem eq_of_homEquiv (hE : HomEquiv S β Λ Υ) (hβ : 0 < β) (h83 : Assumption83 S) {m : ℕ}
    (h87 : S.stableCount β⁻¹ = Fintype.card ιZ + m)
    (hcirc : ∀ l ∈ S.pencilPoly.roots, ‖l‖ ≠ β⁻¹) : zerosInside (alpha Λ) = m := by
  have h0 := zerosOnCircle_eq_zero hE hβ h83.regular hcirc
  have := bounds_of_homEquiv hE hβ h83 h87
  omega

/-! ### From Proposition 8.1 to the homogeneous equivalence -/

variable {Ω : Type*} {ιτ : Type*} [Fintype ιτ]

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 540 (tool): the `M`-block is additive. -/
theorem Mpart_add (a b : ιZ ⊕ ιz → ℝ) : Mpart (a + b) = Mpart a + Mpart b := rfl

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 540 (tool): the `ξ`-block is additive. -/
theorem ξpart_add (a b : ιZ ⊕ ιz → ℝ) : ξpart (a + b) = ξpart a + ξpart b := rfl

/-- Woodford (2003), Proposition 8.1, p. 553: **the representation restricted to deterministic
perturbations.** Let `(y₀, φ₀)` solve (1.18), and suppose that for every bounded deterministic
`h` the perturbed multipliers `φ₀ + h` (dates shifted by `t₀`) solve (1.18) iff they solve
(1.20)–(1.21) with the forcing `q`, `r` of `y₀`. Then bounded `h` solve the homogeneous (1.18)
iff they solve the homogeneous (1.20)–(1.21). The sample space must be nonempty. (This is the
only consequence of Proposition 8.1 the dimension count uses; it holds for the original
`Prop81Conclusion` and for any version of Proposition 8.1 restricted to multipliers with `M_t`
known at `t`, since deterministic perturbations preserve that property.) -/
theorem homEquiv_of_perturbation [Nonempty Ω] {P : LQProblem ιZ ιz ιτ}
    {𝔼 : ExpectationSystem Ω} {t0 : ℕ} {Λ : Matrix ιz ιz ℝ} {Υ : Matrix ιZ ιz ℝ}
    {q : ℕ → Ω → ιz → ℝ} {r : ℕ → Ω → ιZ → ℝ} {y0 : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ0 : ℕ → Ω → ιZ ⊕ ιz → ℝ} (h118 : Eq118 P 𝔼 t0 y0 φ0)
    (hequiv : ∀ h : ℕ → ιZ ⊕ ιz → ℝ, BddSeq h →
      (Eq118 P 𝔼 t0 y0 (fun t ω => φ0 t ω + h (t - t0)) ↔
        Eq120 t0 Λ q (fun t ω => φ0 t ω + h (t - t0)) ∧
          Eq121 t0 Υ r (fun t ω => φ0 t ω + h (t - t0)))) :
    HomEquiv P.sys P.β Λ Υ := by
  obtain ⟨h120, h121⟩ : Eq120 t0 Λ q φ0 ∧ Eq121 t0 Υ r φ0 := by
    have h0 := hequiv 0 ⟨0, fun t i => by simp⟩
    simp only [Pi.zero_apply, add_zero] at h0
    exact h0.mp h118
  intro h hb
  obtain ⟨ω0⟩ := ‹Nonempty Ω›
  set φ' : ℕ → Ω → ιZ ⊕ ιz → ℝ := fun t ω => φ0 t ω + h (t - t0) with hφ'
  have e118 : ∀ t, t0 ≤ t → ∀ ω,
      P.sys.Ahatᵀ *ᵥ EV 𝔼 t (φ' (t + 1)) ω + P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ y0 t ω - P.τstar)) -
        P.β⁻¹ • (P.sys.Ihatᵀ *ᵥ φ' t ω) =
      P.sys.Ahatᵀ *ᵥ h (t - t0 + 1) - P.β⁻¹ • (P.sys.Ihatᵀ *ᵥ h (t - t0)) := by
    intro t ht ω
    have h0 := h118 t ht ω
    have e : t + 1 - t0 = t - t0 + 1 := by omega
    simp only [hφ', EV_add_const, mulVec_add, smul_add, e]
    linear_combination (norm := module) h0
  have e120 : ∀ t, t0 ≤ t → ∀ ω,
      (Mpart (φ' (t + 1) ω) = Λ *ᵥ Mpart (φ' t ω) + q t ω ↔
        Mpart (h (t - t0 + 1)) = Λ *ᵥ Mpart (h (t - t0))) := by
    intro t ht ω
    have h0 := h120 t ht ω
    have e : t + 1 - t0 = t - t0 + 1 := by omega
    simp only [hφ', e, Mpart_add, mulVec_add]
    constructor
    · intro h1
      linear_combination (norm := module) h1 - h0
    · intro h1
      linear_combination (norm := module) h1 + h0
  have e121 : ∀ t, t0 ≤ t → ∀ ω,
      (ξpart (φ' t ω) = Υ *ᵥ Mpart (φ' t ω) + r t ω ↔
        ξpart (h (t - t0)) = Υ *ᵥ Mpart (h (t - t0))) := by
    intro t ht ω
    have h0 := h121 t ht ω
    simp only [hφ', Mpart_add, ξpart_add, mulVec_add]
    constructor
    · intro h1
      linear_combination (norm := module) h1 - h0
    · intro h1
      linear_combination (norm := module) h1 + h0
  constructor
  · intro hs
    have h118' : Eq118 P 𝔼 t0 y0 φ' := fun t ht ω => by
      rw [e118 t ht ω, hs (t - t0), sub_self]
    obtain ⟨h120', h121'⟩ := (hequiv h hb).mp h118'
    intro s
    have hts : t0 ≤ s + t0 := by omega
    have es : s + t0 - t0 = s := by omega
    refine ⟨?_, ?_⟩
    · have := (e120 (s + t0) hts ω0).mp (h120' (s + t0) hts ω0)
      rwa [es] at this
    · have := (e121 (s + t0) hts ω0).mp (h121' (s + t0) hts ω0)
      rwa [es] at this
  · intro hr
    have h120' : Eq120 t0 Λ q φ' := fun t ht ω => (e120 t ht ω).mpr (hr (t - t0)).1
    have h121' : Eq121 t0 Υ r φ' := fun t ht ω => (e121 t ht ω).mpr (hr (t - t0)).2
    have h118' := (hequiv h hb).mpr ⟨h120', h121'⟩
    intro s
    have := e118 (s + t0) (by omega) ω0
    rw [h118' (s + t0) (by omega) ω0, show s + t0 - t0 = s by omega] at this
    exact sub_eq_zero.mp this.symm

/-- Woodford (2003), Proposition 8.1, p. 553: **the representation of Proposition 8.1 restricted
to deterministic perturbations.** Given one bounded solution `(y₀, φ₀)` of (1.18), a bounded
deterministic `h` solves the homogeneous (1.18) iff it solves the homogeneous (1.20)–(1.21):
apply the equivalence of Proposition 8.1 to `(y₀, φ₀ + h)` (dates shifted by `t₀`). The sample
space must be nonempty. -/
theorem homEquiv_of_prop81 [Nonempty Ω] {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω}
    {t0 : ℕ} (H : Prop81Conclusion P 𝔼 t0) {y0 : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ0 : ℕ → Ω → ιZ ⊕ ιz → ℝ} (hy0 : BoundedV y0) (hφ0 : BoundedV φ0)
    (h118 : Eq118 P 𝔼 t0 y0 φ0) : HomEquiv P.sys P.β H.Λ H.Υ := by
  refine homEquiv_of_perturbation h118 fun h hb => H.equiv y0 _ hy0 ?_
  obtain ⟨M, hM⟩ := hφ0
  obtain ⟨C, hC⟩ := hb
  refine ⟨M + C, fun t ω i => (abs_add_le _ _).trans (add_le_add (hM t ω i) ?_)⟩
  have := hC (t - t0) i
  rwa [Real.norm_eq_abs] at this

/-- Woodford (2003), Assumption 8.1, p. 541 (existence half): a bounded solution of the
first-order conditions is a bounded adapted plan with bounded multipliers, `M_t` known at `t`
(`Prop81General.MultKnown`), solving (1.18) (`foc_iff_split`). -/
theorem exists_base_of_assumption81 {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω}
    {t0 : ℕ} (hA : Assumption81 P 𝔼 t0) :
    ∃ y φ, BoundedV y ∧ AdaptedV 𝔼 y ∧ BoundedV φ ∧ Prop81General.MultKnown 𝔼 t0 φ ∧
      Eq118 P 𝔼 t0 y φ := by
  obtain ⟨y, φ, hsys⟩ := hA.solvable (fun _ _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
    ⟨0, fun _ _ _ => by simp⟩ (fun t _ => 𝔼.const t 0) (fun _ => 𝔼.const t0 0)
    (fun _ => 𝔼.const t0 0)
  exact ⟨y, φ, hsys.1.2.2.1, hsys.1.2.2.2, hsys.2.1, fun t _ r => hsys.2.2.1 t r,
    fun t ht ω => ((foc_iff_split P hsys.2.2.1 y t ω).mp (hsys.2.2.2.2 t ht ω)).1⟩

/-! ### Proposition 8.3 -/

/-- **Woodford (2003), Proposition 8.3, pp. 556–557, the two-sided general form.** For a
linear-quadratic problem satisfying Assumption 8.1 (only the existence of a bounded solution is
used), Assumption 8.3 and Assumption 8.7 (`n_Z + m` roots of (1.15) with `|μ| < β⁻¹`, the zero
root counted `n − rank A` times), and for **every** matrix `Λ` delivered by Proposition 8.1, the
lag polynomial `α(L) = det(I − ΛL)` of the optimal instrument rule (1.28) has at most `m` zeros
inside the unit circle, and at least `m` zeros in the closed unit disc. -/
theorem prop83_bounds [Nonempty Ω] {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω}
    {t0 : ℕ} (H : Prop81Conclusion P 𝔼 t0) (hA : Assumption81 P 𝔼 t0)
    (h83 : Assumption83 P.sys) {m : ℕ} (h87 : P.sys.stableCount P.β⁻¹ = Fintype.card ιZ + m) :
    zerosInside (alpha H.Λ) ≤ m ∧
      m ≤ zerosInside (alpha H.Λ) + zerosOnCircle (alpha H.Λ) := by
  obtain ⟨y, φ, hy, -, hφ, -, h118⟩ := exists_base_of_assumption81 hA
  exact bounds_of_homEquiv (homEquiv_of_prop81 H hy hφ h118) P.β_pos h83 h87

/-- **Woodford (2003), Proposition 8.3, pp. 556–557 (superinertia).** Under Assumptions 8.1,
8.3 and 8.7 (`n_Z + m` roots of (1.15) with `|μ| < β⁻¹`), if no root of (1.15) lies on
`|μ| = β⁻¹`, then for every matrix `Λ` delivered by Proposition 8.1 the lag polynomial
`α(L) = 1 − γ(L)L = det(I − ΛL)` of the optimal instrument rule (1.28) has exactly `m` zeros
inside the unit circle. (`λ_i > 0` and Assumptions 8.2, 8.4–8.6 are not needed: `α` does not
involve the loss weights.) -/
theorem prop83 [Nonempty Ω] {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (H : Prop81Conclusion P 𝔼 t0) (hA : Assumption81 P 𝔼 t0) (h83 : Assumption83 P.sys)
    {m : ℕ} (h87 : P.sys.stableCount P.β⁻¹ = Fintype.card ιZ + m)
    (hcirc : ∀ l ∈ P.sys.pencilPoly.roots, ‖l‖ ≠ P.β⁻¹) : zerosInside (alpha H.Λ) = m := by
  obtain ⟨y, φ, hy, -, hφ, -, h118⟩ := exists_base_of_assumption81 hA
  exact eq_of_homEquiv (homEquiv_of_prop81 H hy hφ h118) P.β_pos h83 h87 hcirc

/-- **Woodford (2003), Proposition 8.3, for any representation that is valid for deterministic
perturbations of one bounded solution of (1.18)** (`homEquiv_of_perturbation`; this covers a
version of Proposition 8.1 restricted to multipliers with `M_t` known at `t`, which is the one
that holds under uncertainty): under Assumptions 8.3 and 8.7 and with no root of (1.15) on
`|λ| = β⁻¹`, `α(L) = det(I − ΛL)` has exactly `m` zeros inside the unit circle. -/
theorem prop83_of_perturbation [Nonempty Ω] {P : LQProblem ιZ ιz ιτ}
    {𝔼 : ExpectationSystem Ω} {t0 : ℕ} {Λ : Matrix ιz ιz ℝ} {Υ : Matrix ιZ ιz ℝ}
    {q : ℕ → Ω → ιz → ℝ} {r : ℕ → Ω → ιZ → ℝ} {y0 : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ0 : ℕ → Ω → ιZ ⊕ ιz → ℝ} (h118 : Eq118 P 𝔼 t0 y0 φ0)
    (hequiv : ∀ h : ℕ → ιZ ⊕ ιz → ℝ, BddSeq h →
      (Eq118 P 𝔼 t0 y0 (fun t ω => φ0 t ω + h (t - t0)) ↔
        Eq120 t0 Λ q (fun t ω => φ0 t ω + h (t - t0)) ∧
          Eq121 t0 Υ r (fun t ω => φ0 t ω + h (t - t0))))
    (h83 : Assumption83 P.sys) {m : ℕ} (h87 : P.sys.stableCount P.β⁻¹ = Fintype.card ιZ + m)
    (hcirc : ∀ l ∈ P.sys.pencilPoly.roots, ‖l‖ ≠ P.β⁻¹) : zerosInside (alpha Λ) = m :=
  eq_of_homEquiv (homEquiv_of_perturbation h118 hequiv) P.β_pos h83 h87 hcirc

/-- Woodford (2003), pp. 557–558: under Assumption 8.1 and a regular pencil with no root on
`|λ| = β⁻¹`, the `α(L)` of every `Λ` delivered by Proposition 8.1 has no zero on the unit
circle (so in Proposition 8.4 the factor `α₂` has all its zeros strictly outside it). -/
theorem prop83_noCircle [Nonempty Ω] {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω}
    {t0 : ℕ} (H : Prop81Conclusion P 𝔼 t0) (hA : Assumption81 P 𝔼 t0)
    (hreg : P.sys.pencilPoly ≠ 0) (hcirc : ∀ l ∈ P.sys.pencilPoly.roots, ‖l‖ ≠ P.β⁻¹) :
    zerosOnCircle (alpha H.Λ) = 0 := by
  obtain ⟨y, φ, hy, -, hφ, -, h118⟩ := exists_base_of_assumption81 hA
  exact zerosOnCircle_eq_zero (homEquiv_of_prop81 H hy hφ h118) P.β_pos hreg hcirc

/-- Woodford (2003), Proposition 8.3 with Assumption 8.7 as stated (`m ≥ 1`), pp. 556–557:
`α(L)` has a zero inside the unit circle, so the instrument dynamics implied by (1.28) for an
arbitrary path of the other targets are explosive (superinertia). -/
theorem prop83_superinertial [Nonempty Ω] {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω}
    {t0 : ℕ} (H : Prop81Conclusion P 𝔼 t0) (hA : Assumption81 P 𝔼 t0)
    (h83 : Assumption83 P.sys) (h87 : P.sys.Assumption87 P.β)
    (hcirc : ∀ l ∈ P.sys.pencilPoly.roots, ‖l‖ ≠ P.β⁻¹) :
    ∃ z ∈ ((alpha H.Λ).map Complex.ofRealHom).roots, ‖z‖ < 1 := by
  obtain ⟨m, hm1, hm⟩ := h87
  have h := prop83 H hA h83 hm hcirc
  unfold zerosInside at h
  have hpos : 0 < Multiset.card (((alpha H.Λ).map Complex.ofRealHom).roots.filter
      (fun z => ‖z‖ < 1)) := by omega
  obtain ⟨z, hz⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
  exact ⟨z, (Multiset.mem_filter.mp hz).1, (Multiset.mem_filter.mp hz).2⟩

/-- Woodford (2003), Proposition 8.3, pp. 556–557: the statement `TargetCriterion.Prop83Claim`
(for the given representation `H`) holds under Assumptions 8.1 and 8.3, a nonempty sample space
and no root of (1.15) on `|λ| = β⁻¹`. -/
theorem prop83Claim_holds [Nonempty Ω] {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω}
    {t0 : ℕ} (H : Prop81Conclusion P 𝔼 t0) (hA : Assumption81 P 𝔼 t0)
    (h83 : Assumption83 P.sys) (hcirc : ∀ l ∈ P.sys.pencilPoly.roots, ‖l‖ ≠ P.β⁻¹) :
    TargetCriterion.Prop83Claim P 𝔼 t0 H :=
  fun _ h87 _ => prop83 H hA h83 h87 hcirc

/-! ### The sample space must be nonempty -/

/-- Woodford (2003), Proposition 8.1, p. 553: on an empty sample space every matrix `Λ` is
delivered by Proposition 8.1 (all its conditions are vacuous). -/
theorem prop81Conclusion_of_isEmpty [IsEmpty Ω] (P : LQProblem ιZ ιz ιτ)
    (𝔼 : ExpectationSystem Ω) (t0 : ℕ) (Λ : Matrix ιz ιz ℝ) :
    ∃ H : Prop81Conclusion P 𝔼 t0, H.Λ = Λ :=
  ⟨⟨Λ, 0, fun _ _ _ _ => 0, fun _ _ _ _ => 0,
    fun _ _ _ _ => ⟨fun _ => ⟨fun _ _ ω => isEmptyElim ω, fun _ _ ω => isEmptyElim ω⟩,
      fun _ _ _ ω => isEmptyElim ω⟩,
    fun _ _ => ⟨0, fun _ ω => isEmptyElim ω⟩, fun _ _ => ⟨0, fun _ ω => isEmptyElim ω⟩,
    fun _ _ _ => funext fun ω => isEmptyElim ω⟩, rfl⟩

/-- Woodford (2003), Assumption 8.1, p. 541: on an empty sample space Assumption 8.1 holds
vacuously. -/
theorem assumption81_of_isEmpty [IsEmpty Ω] (P : LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω)
    (t0 : ℕ) : Assumption81 P 𝔼 t0 :=
  ⟨fun _ _ _ _ _ _ _ => ⟨fun _ ω => isEmptyElim ω, fun _ ω => isEmptyElim ω,
      ⟨⟨fun _ _ ω => isEmptyElim ω, fun ω => isEmptyElim ω, ⟨0, fun _ ω => isEmptyElim ω⟩,
        fun _ _ => funext fun ω => isEmptyElim ω⟩,
      ⟨0, fun _ ω => isEmptyElim ω⟩, fun _ _ => funext fun ω => isEmptyElim ω,
      fun ω => isEmptyElim ω, fun _ _ ω => isEmptyElim ω⟩⟩,
    fun _ _ _ _ _ _ _ _ _ _ _ => ⟨funext fun ω => isEmptyElim ω,
      funext fun ω => isEmptyElim ω⟩⟩

/-- Woodford (2003), Proposition 8.3: **the sample space must be nonempty.** On an empty sample
space Assumption 8.1 holds and Proposition 8.1 delivers `Λ = 0`, whose `α(L) = 1` has no zero
inside the unit circle, whatever `m`. -/
theorem prop83_needs_nonempty [IsEmpty Ω] (P : LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω)
    (t0 : ℕ) :
    Assumption81 P 𝔼 t0 ∧ ∃ H : Prop81Conclusion P 𝔼 t0, zerosInside (alpha H.Λ) = 0 := by
  refine ⟨assumption81_of_isEmpty P 𝔼 t0, ?_⟩
  obtain ⟨H, hH⟩ := prop81Conclusion_of_isEmpty P 𝔼 t0 0
  refine ⟨H, ?_⟩
  rw [hH, zerosInside_alpha]
  simp [cmat, charpoly_zero]

/-! ### Counterexample: a root of (1.15) on `|λ| = β⁻¹` -/

/-- Woodford (2003), eq. (1.1), p. 537 (counterexample to Prop. 8.3 without the circle
hypothesis): `n_Z = 0`, `n_z = 2`, `E_t z_{1,t+1} = z_{1t} + i_t + c_{1t}`,
`E_t z_{2,t+1} = β⁻¹ z_{2t} + i_t + c_{2t}`; (1.15) has the roots `1` and `β⁻¹`. -/
noncomputable def circSys (β : ℝ) (hβ : β ≠ 0) : LinearRESystem Empty (Fin 2) where
  A11 := 0
  A12 := 0
  A21 := 0
  A22 := !![1, 0; 0, β⁻¹]
  Et := 1
  B2 := ![1, 1]
  A22_isUnit := by
    rw [isUnit_iff_ne_zero, det_fin_two_of]
    simpa using hβ
  B2_ne_zero := by
    intro h
    have := congrFun h 0
    simp at this

/-- Woodford (2003), p. 553 (counterexample): a Jordan block at the eigenvalue `1`. -/
noncomputable def jordanΛ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1, 1]

/-- Woodford (2003), p. 557 (tool): the determinant of a matrix indexed by `Empty ⊕ ι` is that of
its `ι`-block. -/
theorem det_empty_sum {R : Type*} [CommRing R] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : Matrix (Empty ⊕ κ) (Empty ⊕ κ) R) : M.det = M.toBlocks₂₂.det := by
  rw [← fromBlocks_toBlocks M]
  have h21 : M.toBlocks₂₁ = 0 := by
    ext i j
    exact j.elim
  rw [h21, det_fromBlocks_zero₂₁, det_isEmpty, one_mul]
  rfl

/-- Woodford (2003), eq. (1.15) (counterexample): `det(A − μÎ) = (μ − 1)(μ − β⁻¹)`. -/
theorem circSys_pencilPoly {β : ℝ} (hβ : β ≠ 0) :
    (circSys β hβ).pencilPoly = (X - C 1) * (X - C ((β : ℂ)⁻¹)) := by
  unfold LinearRESystem.pencilPoly
  rw [det_empty_sum, det_fin_two]
  simp [toBlocks₂₂, LinearRESystem.Ahat, LinearRESystem.Ihat, circSys]
  ring

/-- Woodford (2003), App. G.1 and Assumption 8.7 (counterexample): the roots of (1.15) are
`1` and `β⁻¹`. -/
theorem circSys_roots {β : ℝ} (hβ : β ≠ 0) :
    (circSys β hβ).pencilPoly.roots = {1, (β : ℂ)⁻¹} := by
  rw [circSys_pencilPoly, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    roots_X_sub_C, roots_X_sub_C]
  rfl

/-- Woodford (2003), p. 553 (counterexample): the homogeneous (1.18) of `circSys` is
`φ₁(t+1) = β⁻¹ φ₁(t)`, `φ₂(t+1) = φ₂(t)`; its bounded solutions (`φ₁ = 0`, `φ₂` constant) are
exactly the bounded solutions of `M_t = Λ' M_{t−1}` with the Jordan block `Λ'`. -/
theorem circSys_homEquiv {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    HomEquiv (circSys β hβ0.ne') β jordanΛ 0 := by
  have hb1 : 1 < β⁻¹ := one_lt_inv₀ hβ0 |>.mpr hβ1
  have hbne : β⁻¹ ≠ 0 := inv_ne_zero hβ0.ne'
  intro h hb
  obtain ⟨C, hC⟩ := hb
  have hCa : ∀ t, |h t (Sum.inr 0)| ≤ C := fun t => by
    have := hC t (Sum.inr 0)
    rwa [Real.norm_eq_abs] at this
  have hCb : ∀ t, |h t (Sum.inr 1)| ≤ C := fun t => by
    have := hC t (Sum.inr 1)
    rwa [Real.norm_eq_abs] at this
  have hsol : HomSol (circSys β hβ0.ne') β h ↔
      ∀ t, h (t + 1) (Sum.inr 0) = β⁻¹ * h t (Sum.inr 0) ∧
        h (t + 1) (Sum.inr 1) = h t (Sum.inr 1) := by
    refine forall_congr' fun t => ?_
    rw [funext_iff]
    constructor
    · intro H
      refine ⟨?_, ?_⟩
      · simpa [LinearRESystem.Ahat, LinearRESystem.Ihat, circSys, mulVec, dotProduct,
          Fin.sum_univ_two] using H (Sum.inr 0)
      · simpa [LinearRESystem.Ahat, LinearRESystem.Ihat, circSys, mulVec, dotProduct,
          Fin.sum_univ_two, hβ0.ne'] using H (Sum.inr 1)
    · rintro ⟨h0, h1⟩ r
      rcases r with r | r
      · exact r.elim
      · fin_cases r <;>
          simp [LinearRESystem.Ahat, LinearRESystem.Ihat, circSys, mulVec, dotProduct,
            Fin.sum_univ_two, h0, h1]
  have hrep : RepSol jordanΛ (0 : Matrix Empty (Fin 2) ℝ) h ↔
      ∀ t, h (t + 1) (Sum.inr 0) = h t (Sum.inr 0) ∧
        h (t + 1) (Sum.inr 1) = h t (Sum.inr 0) + h t (Sum.inr 1) := by
    refine forall_congr' fun t => ?_
    constructor
    · rintro ⟨h1, -⟩
      exact ⟨by simpa [Mpart_eq, jordanΛ, mulVec, dotProduct, Fin.sum_univ_two] using
          congrFun h1 0,
        by simpa [Mpart_eq, jordanΛ, mulVec, dotProduct, Fin.sum_univ_two] using congrFun h1 1⟩
    · rintro ⟨h0, h1⟩
      refine ⟨funext fun r => ?_, funext fun r => r.elim⟩
      fin_cases r <;> simp [Mpart_eq, jordanΛ, mulVec, dotProduct, Fin.sum_univ_two, h0, h1]
  rw [hsol, hrep]
  constructor
  · intro H
    -- the first component is explosive, hence zero
    have ha : ∀ t, h t (Sum.inr 0) = (β⁻¹) ^ t * h 0 (Sum.inr 0) := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [(H t).1, ih, pow_succ]; ring
    have ha0 : h 0 (Sum.inr 0) = 0 := by
      by_contra h0
      have hpos : 0 < |h 0 (Sum.inr 0)| := abs_pos.mpr h0
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (C / |h 0 (Sum.inr 0)|) hb1
      have := hCa k
      rw [ha k, abs_mul, abs_of_pos (pow_pos (inv_pos.mpr hβ0) k)] at this
      have := (div_lt_iff₀ hpos).mp hk
      linarith
    intro t
    have hat : ∀ s, h s (Sum.inr 0) = 0 := fun s => by rw [ha s, ha0, mul_zero]
    exact ⟨by rw [hat, hat], by rw [(H t).2, hat, zero_add]⟩
  · intro H
    have ha : ∀ t, h t (Sum.inr 0) = h 0 (Sum.inr 0) := by
      intro t
      induction t with
      | zero => rfl
      | succ t ih => rw [(H t).1, ih]
    have hbt : ∀ t, h t (Sum.inr 1) = h 0 (Sum.inr 1) + t * h 0 (Sum.inr 0) := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [(H t).2, ih, ha t]; push_cast; ring
    have ha0 : h 0 (Sum.inr 0) = 0 := by
      by_contra h0
      have hpos : 0 < |h 0 (Sum.inr 0)| := abs_pos.mpr h0
      obtain ⟨k, hk⟩ := exists_nat_gt (2 * C / |h 0 (Sum.inr 0)|)
      have h1 := hCb k
      have h2 := hCb 0
      rw [hbt k] at h1
      have h3 : (k : ℝ) * |h 0 (Sum.inr 0)| ≤ 2 * C := by
        have h4 := (abs_sub (h 0 (Sum.inr 1) + k * h 0 (Sum.inr 0)) (h 0 (Sum.inr 1))).trans
          (add_le_add h1 h2)
        rw [add_sub_cancel_left, abs_mul, Nat.abs_cast] at h4
        linarith
      have := (div_lt_iff₀ hpos).mp hk
      linarith
    intro t
    have hat : ∀ s, h s (Sum.inr 0) = 0 := fun s => by rw [ha s, ha0]
    exact ⟨by rw [hat, hat, mul_zero], by rw [(H t).2, hat, zero_add]⟩

/-- Woodford (2003), p. 557 (counterexample): `α(L) = det(I − Λ'L)` has no zero inside the unit
circle and a double zero at `1`. -/
theorem jordanΛ_zeros : zerosInside (alpha jordanΛ) = 0 ∧ zerosOnCircle (alpha jordanΛ) = 2 := by
  have hcp : (cmat jordanΛ).charpoly = (X - C 1) * (X - C 1) := by
    rw [charpoly, det_fin_two]
    simp [cmat, jordanΛ]
  have hroots : (cmat jordanΛ).charpoly.roots = {1, 1} := by
    rw [hcp, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)), roots_X_sub_C]
    rfl
  rw [zerosInside_alpha, zerosOnCircle_alpha, hroots]
  simp [Multiset.filter_singleton]

/-- **Woodford (2003), Proposition 8.3 — counterexample without the circle hypothesis.** For
`0 < β < 1` the system `circSys` satisfies Assumption 8.3 and Assumption 8.7 with `m = 1`, and
the Jordan block `Λ'` represents the bounded solutions of the homogeneous (1.18) as Proposition
8.1 requires (`HomEquiv`), but (1.15) has the root `β⁻¹` on `|λ| = β⁻¹` and `α(L) = (1 − L)²`
has no zero inside the unit circle. So the conclusion of `eq_of_homEquiv` (and of Proposition
8.3 for an arbitrary representation) needs the hypothesis that no root lies on `|λ| = β⁻¹`;
`bounds_of_homEquiv` still holds (`0 ≤ 1 ≤ 0 + 2`). -/
theorem circle_counterexample {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    HomEquiv (circSys β hβ0.ne') β jordanΛ 0 ∧ Assumption83 (circSys β hβ0.ne') ∧
      (circSys β hβ0.ne').stableCount β⁻¹ = Fintype.card Empty + 1 ∧
      ((β : ℂ)⁻¹ ∈ (circSys β hβ0.ne').pencilPoly.roots ∧ ‖((β : ℂ)⁻¹)‖ = β⁻¹) ∧
      zerosInside (alpha jordanΛ) = 0 := by
  have hb1 : 1 < β⁻¹ := one_lt_inv₀ hβ0 |>.mpr hβ1
  have hbc : (β : ℂ)⁻¹ ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [← Complex.ofReal_inv, Complex.ofReal_re, Complex.one_re] at this
    linarith
  have hbc0 : (β : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr hβ0.ne')
  have hnorm : ‖((β : ℂ)⁻¹)‖ = β⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hβ0.le]
  have hnz : nonzeroRoots (circSys β hβ0.ne') = {1, (β : ℂ)⁻¹} := by
    rw [nonzeroRoots, circSys_roots]
    simp [hbc0]
  have hdetA : IsUnit (circSys β hβ0.ne').Ahat.det := by
    rw [det_empty_sum]
    exact (circSys β hβ0.ne').A22_isUnit
  have hrankA : (circSys β hβ0.ne').Ahat.rank = 2 := by
    rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr hdetA)]
    simp
  have hrankE : (circSys β hβ0.ne').Et.rank = 2 := by
    change (1 : Matrix (Fin 2) (Fin 2) ℝ).rank = 2
    rw [rank_one]
    simp
  refine ⟨circSys_homEquiv hβ0 hβ1, (Assumption83.ofRoots _ ?_ ?_ ?_).elim id, ?_, ⟨?_, hnorm⟩,
    jordanΛ_zeros.1⟩
  · rw [circSys_pencilPoly]
    exact mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
  · rw [hnz]
    simpa using hbc.symm
  · rw [hnz, hrankA, hrankE]
    simp
  · unfold LinearRESystem.stableCount
    rw [circSys_roots, hrankA]
    simp [hbc0, hnorm, hb1]
  · rw [circSys_roots]
    simp

end Woodford.OptimalPolicyRules.Prop83
