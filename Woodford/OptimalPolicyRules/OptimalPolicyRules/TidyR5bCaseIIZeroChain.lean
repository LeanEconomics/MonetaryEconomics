/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.CaseIIBasis

/-!
# Case (ii): the existential Assumption 8.4 (ii) does not imply the universal one when the zero
root is not semisimple

Woodford (2003), *Interest and Prices*, Chapter 8, Assumption 8.2 (ii) (p. 552), Assumption 8.4
(ii) and Appendix G.1 (pp. 716–718); the counting convention for the zero root (p. 547).

`CaseIIBasis.all_of_ex_semisimple` proves that the existential corrected Assumption 8.4 (ii)
(`CaseIIBasis.Assumption84II`: SOME admissible basis satisfies `CondII`) implies the universal
form (`Prop81CaseII.Assumption84IIall`: EVERY admissible basis does) when the zero root of (1.15)
is semisimple. This module shows that the semisimplicity hypothesis cannot be dropped.

## The system `zcSys` (`n_Z = 3`, `n_z = 2`, `Ẽ = I`, `β = 1/4`)

In the coordinates `(Z₁, Z₂, Z₃, z₁, z₂)`, `A` acts as a rotation-scaling block
`[[1, 1], [−1, 1]]` on `(Z₁, z₂)` (roots `1 ± i`), a nilpotent Jordan chain `Z₃ ↦ Z₂ ↦ 0`, and
`z₁ ↦ ½ z₁`. So (1.15) is `−μ²(μ − ½)(μ² − 2μ + 2)` (`zc_pencilPoly`), `rank A = 4` (`zc_rank`):
the zero root has multiplicity 2 but `n − rank A = 1`, it is **not semisimple**
(`zc_not_zeroSemisimple`). The selection `{1 + i, ½}` is case (ii) of Assumption 8.2
(`zc82`), with whole root classes (`zc_selWhole`) and a nonzero (1.15).

* The admissible basis `W' = (e_{Z₁}, e_{z₂}, e_{Z₂}, e_{Z₃})` uses the full zero chain in place of
  the selected root `½`; with `P` selecting `(e_{Z₁}, e_{Z₂}, e_{Z₃})` it satisfies `CondII` with
  residual root `h = 1`: the existential form holds (`zc_ex`).
* The admissible basis `W = (e_{Z₁}, e_{z₂}, e_{Z₂}, e_{z₁})` — the subspace the book's counting
  convention selects (`ker A`, the plane of `1 ± i`, the eigenvector of `½`) — has no `Z₃`
  component, so `J₁(W P)` is singular for every `P`: the universal form fails (`zc_not_all`).

`zc_semisimple_needed` collects every hypothesis of `CaseIIBasis.all_of_ex_semisimple` except
`ZeroSemisimple`, together with `Assumption84II` and `¬ Assumption84IIall`.
-/

namespace Woodford.OptimalPolicyRules.TidyR5bCaseIIZeroChain

open Matrix Polynomial GeneralSetup PencilSplit PencilEigen PencilRepeated
  GeneralFOC.Selection Prop81CaseII CaseIIBasis

/-! ### The system -/

/-- Woodford (2003), eq. (1.1), p. 537 (the counterexample): `A₁₁`, the predetermined block. -/
noncomputable def zcA11 : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 0, 1; 0, 0, 0]

/-- Woodford (2003), eq. (1.1): `A₁₂`. -/
noncomputable def zcA12 : Matrix (Fin 3) (Fin 2) ℝ := !![0, 1; 0, 0; 0, 0]

/-- Woodford (2003), eq. (1.1): `A₂₁`. -/
noncomputable def zcA21 : Matrix (Fin 2) (Fin 3) ℝ := !![0, 0, 0; -1, 0, 0]

/-- Woodford (2003), eq. (1.1): `A₂₂ = diag(½, 1)` (invertible). -/
noncomputable def zcA22 : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, 0; 0, 1]

/-- Woodford (2003), eq. (1.1), p. 537 (the counterexample system): `n_Z = 3`, `n_z = 2`,
`Ẽ = I`, `B₂ = (1, 1)'`. -/
noncomputable def zcSys : LinearRESystem (Fin 3) (Fin 2) where
  A11 := zcA11
  A12 := zcA12
  A21 := zcA21
  A22 := zcA22
  Et := 1
  B2 := ![1, 1]
  A22_isUnit := by
    rw [isUnit_iff_ne_zero, zcA22, det_fin_two_of]
    norm_num
  B2_ne_zero := by
    intro h
    have := congrFun h 0
    simp at this

/-- Woodford (2003), (1.15) (tool): the coordinates `(Z₁, Z₂, Z₃, z₁, z₂)` as `Fin 5`. -/
def e5 : Fin 5 ≃ Fin 3 ⊕ Fin 2 where
  toFun := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1]
  invFun := Sum.elim ![0, 1, 2] ![3, 4]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by
    intro a
    rcases a with a | a <;> fin_cases a <;> rfl

/-- Woodford (2003), (1.15) (tool): `A − μÎ` in the coordinates `(Z₁, Z₂, Z₃, z₁, z₂)`. -/
theorem zc_pencil_mat (μ : ℂ) :
    (zcSys.Ahat.map Complex.ofReal - μ • zcSys.Ihat.map Complex.ofReal).submatrix e5 e5 =
      !![1 - μ, 0, 0, 0, 1; 0, -μ, 1, 0, 0; 0, 0, -μ, 0, 0; 0, 0, 0, 1 / 2 - μ, 0;
        -1, 0, 0, 0, 1 - μ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e5, zcSys, zcA11, zcA12, zcA21, zcA22, LinearRESystem.Ahat, LinearRESystem.Ihat]

/-- Woodford (2003), eq. (1.15), p. 546: `det(A − μÎ) = −μ²(μ − ½)(μ² − 2μ + 2)`. -/
theorem zc_pencil_eval (μ : ℂ) :
    zcSys.pencilPoly.eval μ = -(μ ^ 2 * (μ - 1 / 2) * (μ ^ 2 - 2 * μ + 2)) := by
  rw [pencilPoly_eval, ← det_submatrix_equiv_self e5, zc_pencil_mat]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [Fin.succAbove, Fin.lt_def]
  ring

/-- Woodford (2003), (1.15) (tool): `(μ − (1 + i))(μ − (1 − i)) = μ² − 2μ + 2`. -/
theorem quad_factor (μ : ℂ) :
    (μ - (1 + Complex.I)) * (μ - (1 - Complex.I)) = μ ^ 2 - 2 * μ + 2 := by
  linear_combination (-1 : ℂ) * Complex.I_sq

/-- Woodford (2003), eq. (1.15), p. 546: the characteristic polynomial factored,
`−μ² (μ − ½)(μ − (1 + i))(μ − (1 − i))`. -/
theorem zc_pencilPoly : zcSys.pencilPoly = C (-1) * (X ^ 2 * ((X - C (1 / 2)) *
    ((X - C (1 + Complex.I)) * (X - C (1 - Complex.I))))) := by
  refine Polynomial.funext fun μ => ?_
  rw [zc_pencil_eval]
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub]
  rw [quad_factor]
  ring

/-- Woodford (2003), (1.15): the polynomial is nonzero. -/
theorem zc_reg : zcSys.pencilPoly ≠ 0 := by
  rw [zc_pencilPoly]
  refine mul_ne_zero (by simp) (mul_ne_zero (pow_ne_zero _ X_ne_zero) (mul_ne_zero
    (X_sub_C_ne_zero _) (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))))

/-- Woodford (2003), (1.15): the roots with multiplicity, `{0, 0, ½, 1 + i, 1 − i}`. -/
theorem zc_roots : zcSys.pencilPoly.roots =
    (0 : ℂ) ::ₘ (0 : ℂ) ::ₘ (1 / 2 : ℂ) ::ₘ (1 + Complex.I) ::ₘ (1 - Complex.I) ::ₘ 0 := by
  rw [zc_pencilPoly, roots_C_mul _ (by simp),
    roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (mul_ne_zero (X_sub_C_ne_zero _)
      (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)))),
    roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (mul_ne_zero (X_sub_C_ne_zero _)
      (X_sub_C_ne_zero _))),
    roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)), roots_X_pow,
    roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
  rfl

/-- Woodford (2003), (1.15) (tool): the roots are distinct complex numbers. -/
theorem zc_ne : (1 + Complex.I ≠ 1 - Complex.I) ∧ (1 + Complex.I ≠ (1 / 2 : ℂ)) ∧
    (1 - Complex.I ≠ (1 / 2 : ℂ)) ∧ ((0 : ℂ) ≠ 1 / 2) ∧ ((0 : ℂ) ≠ 1 + Complex.I) ∧
    ((0 : ℂ) ≠ 1 - Complex.I) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, by norm_num, fun h => ?_, fun h => ?_⟩
  · have := congrArg Complex.im h; simp at this; norm_num at this
  · have := congrArg Complex.im h; simp at this
  · have := congrArg Complex.im h; simp at this
  · have := congrArg Complex.re h; simp at this
  · have := congrArg Complex.re h; simp at this

/-! ### The rank of `A` -/

/-- Woodford (2003), p. 547 (the counting convention): `ker A` is spanned by `e_{Z₂}`. -/
theorem zc_ker : LinearMap.ker zcSys.Ahat.mulVecLin =
    Submodule.span ℝ {Pi.single (Sum.inl 1) 1} := by
  ext x
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Submodule.mem_span_singleton]
  constructor
  · intro h
    have h0 := congrFun h (Sum.inl 0)
    have h1 := congrFun h (Sum.inl 1)
    have h3 := congrFun h (Sum.inr 0)
    have h4 := congrFun h (Sum.inr 1)
    simp [LinearRESystem.Ahat, mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_three,
      Fin.sum_univ_two, zcSys, zcA11, zcA12, zcA21, zcA22] at h0 h1 h3 h4
    refine ⟨x (Sum.inl 1), funext fun a => ?_⟩
    rcases a with a | a <;> fin_cases a <;> simp <;> linarith
  · rintro ⟨a, rfl⟩
    funext r
    rcases r with r | r <;> fin_cases r <;>
      simp [LinearRESystem.Ahat, mulVec, dotProduct, zcSys, zcA11, zcA12, zcA21, zcA22,
        Pi.single_apply]

/-- Woodford (2003), p. 547: `rank A = 4`, so `n − rank A = 1`. -/
theorem zc_rank : zcSys.Ahat.rank = 4 := by
  have h := LinearMap.finrank_range_add_finrank_ker zcSys.Ahat.mulVecLin
  rw [zc_ker, finrank_span_singleton (by
    intro h0
    have := congrFun h0 (Sum.inl 1)
    simp at this), Module.finrank_fintype_fun_eq_card] at h
  change zcSys.Ahat.rank + 1 = _ at h
  simp at h
  omega

/-- Woodford (2003), p. 547: **the zero root is not semisimple** — it has multiplicity 2 as a
root of (1.15), but `n − rank A = 1`. -/
theorem zc_not_zeroSemisimple : ¬ ZeroSemisimple zcSys := by
  unfold ZeroSemisimple
  rw [zc_roots, zc_rank]
  obtain ⟨-, -, -, -, h5, h6⟩ := zc_ne
  simp [h5, h6]

/-! ### Assumption 8.2, case (ii) -/

/-- Woodford (2003), Assumption 8.2 (ii), p. 552: the selected unpaired root `μ₀ = 1 + i`. -/
noncomputable def μ0 : ℂ := 1 + Complex.I

/-- Woodford (2003), Assumption 8.2 (ii): the selection `{1 + i, ½}` (with `n − rank A = 1` zero,
`n_Z = 3` roots). -/
noncomputable def zcSel : Multiset ℂ := μ0 ::ₘ (1 / 2 : ℂ) ::ₘ 0

/-- Woodford (2003), Assumption 8.2: the nonzero roots with `|μ| < 4 = β⁻¹`. -/
theorem zc_filter : zcSys.pencilPoly.roots.filter (fun μ => μ ≠ 0 ∧ ‖μ‖ < (1 / 4 : ℝ)⁻¹) =
    (1 / 2 : ℂ) ::ₘ (1 + Complex.I) ::ₘ (1 - Complex.I) ::ₘ 0 := by
  have h1 : ‖(1 + Complex.I : ℂ)‖ < 4 := by
    calc ‖(1 + Complex.I : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.I‖ := norm_add_le _ _
      _ < 4 := by simp; norm_num
  have h2 : ‖(1 - Complex.I : ℂ)‖ < 4 := by
    calc ‖(1 - Complex.I : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.I‖ := norm_sub_le _ _
      _ < 4 := by simp; norm_num
  obtain ⟨-, -, -, h4, h5, h6⟩ := zc_ne
  have h3 : ‖(1 / 2 : ℂ)‖ < 4 := by
    rw [norm_div]
    simp
    norm_num
  have h4' : (1 / 4 : ℝ)⁻¹ = 4 := by norm_num
  rw [zc_roots, h4', Multiset.filter_cons_of_neg _ (fun h => h.1 rfl),
    Multiset.filter_cons_of_neg _ (fun h => h.1 rfl),
    Multiset.filter_cons_of_pos _ ⟨h4.symm, h3⟩, Multiset.filter_cons_of_pos _ ⟨h5.symm, h1⟩,
    Multiset.filter_cons_of_pos _ ⟨h6.symm, h2⟩, Multiset.filter_zero]

/-- **Woodford (2003), Assumption 8.2 (ii), p. 552, for `zcSys` with `β = 1/4`**: the selection
`{1 + i, ½}` plus the zero root (counted `n − rank A = 1` time) gives `n_Z = 3` roots with
`|μ| < 4`; the conjugate `1 − i` is not selected, `{½}` is closed under conjugation and
`|Re (1 + i)⁻¹| = ½ > ¼`. -/
noncomputable def zc82 : Assumption82 zcSys (1 / 4) where
  count := by
    unfold LinearRESystem.Assumption82Count LinearRESystem.stableCount
    rw [zc_filter, zc_rank]
    simp
  sel := zcSel
  sel_le := by
    rw [zc_filter, zcSel, μ0, Multiset.cons_swap]
    exact Multiset.cons_le_cons _ (Multiset.cons_le_cons _ (Multiset.zero_le _))
  sel_card := by
    rw [zc_rank, zcSel]
    simp
  cases := by
    right
    refine ⟨μ0, Multiset.mem_cons_self _ _, ?_, ?_, ?_⟩
    · obtain ⟨h1, -, h3, -⟩ := zc_ne
      simp only [zcSel, μ0, Multiset.mem_cons, Multiset.notMem_zero, or_false, not_or]
      refine ⟨fun h => h1 ?_, fun h => h3 ?_⟩
      · rw [← h]; simp [Complex.ext_iff]
      · rw [← h]; simp [Complex.ext_iff]
    · rw [zcSel, Multiset.erase_cons_head]
      unfold ConjClosed
      simp [map_ofNat]
    · rw [μ0]
      have : ((1 + Complex.I)⁻¹).re = 1 / 2 := by
        rw [Complex.inv_re, Complex.normSq_apply]
        simp
        norm_num
      rw [this]
      norm_num

/-- Woodford (2003), Assumption 8.2 (ii): the unpaired root is selected. -/
theorem zc_mem : μ0 ∈ zc82.sel := by
  change μ0 ∈ zcSel
  exact Multiset.mem_cons_self _ _

/-- Woodford (2003), Assumption 8.2 (ii): the rest of the selection is closed under
conjugation. -/
theorem zc_conjClosed : ConjClosed (zc82.sel.erase μ0) := by
  change ConjClosed (zcSel.erase μ0)
  rw [zcSel, Multiset.erase_cons_head]
  unfold ConjClosed
  simp [map_ofNat]

/-- Woodford (2003), Assumption 8.2 (ii), App. G.1: the selection plus `conj μ₀` takes whole
root classes (every root used is simple). -/
theorem zc_selWhole : SelWhole zcSys (selPlus zc82.sel μ0) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := zc_ne
  have hc : starRingEnd ℂ μ0 = 1 - Complex.I := by simp [μ0, Complex.ext_iff]
  intro a ha
  change a ∈ starRingEnd ℂ μ0 ::ₘ zcSel at ha
  change Multiset.count a (starRingEnd ℂ μ0 ::ₘ zcSel) = _
  rw [hc, zcSel, μ0] at *
  rw [zc_roots]
  simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at ha
  simp only [one_div] at h2 h3 h4 ha ⊢
  rcases ha with rfl | rfl | rfl
  · simp [h1.symm, h3, h6.symm]
  · simp [h1, h2, h5.symm]
  · simp [h2.symm, h3.symm, h4.symm]

/-! ### Two admissible bases -/

/-- Woodford (2003), App. G.1 (tool): the columns `none, some 0, some 1, some 2` as `Fin 4`. -/
def e4 : Fin 4 ≃ Option (Fin 3) := finSuccEquiv 3

/-- Woodford (2003), App. G.1: the columns of `W' = (e_{Z₁}, e_{z₂}, e_{Z₂}, e_{Z₃})` (real and
imaginary parts of the eigenvector of `1 + i`, then the zero chain `Z₂ ← Z₃`). -/
def colGood : Option (Fin 3) → Fin 3 ⊕ Fin 2
  | none => Sum.inl 0
  | some c => ![Sum.inr 1, Sum.inl 1, Sum.inl 2] c

/-- Woodford (2003), App. G.1: the columns of `W = (e_{Z₁}, e_{z₂}, e_{Z₂}, e_{z₁})` (the plane of
`1 ± i`, `ker A`, the eigenvector of `½`). -/
def colBad : Option (Fin 3) → Fin 3 ⊕ Fin 2
  | none => Sum.inl 0
  | some c => ![Sum.inr 1, Sum.inl 1, Sum.inr 0] c

/-- Woodford (2003), App. G.1: the basis matrix whose column `c` is the unit vector `e_{f c}`. -/
def colMat (f : Option (Fin 3) → Fin 3 ⊕ Fin 2) : Matrix (Fin 3 ⊕ Fin 2) (Option (Fin 3)) ℝ :=
  Matrix.of fun a c => if a = f c then 1 else 0

/-- Woodford (2003), App. G.1, (G.4): `Ψ'` for `W'` — the rotation-scaling block of `1 + i` and
the nilpotent block of the zero chain. -/
def ΨGood : Matrix (Option (Fin 3)) (Option (Fin 3)) ℝ :=
  (!![1, 1, 0, 0; -1, 1, 0, 0; 0, 0, 0, 1; 0, 0, 0, 0] : Matrix (Fin 4) (Fin 4) ℝ).submatrix
    e4.symm e4.symm

/-- Woodford (2003), App. G.1, (G.4): `Ψ` for `W` — the block of `1 + i`, `0` and `½`. -/
noncomputable def ΨBad : Matrix (Option (Fin 3)) (Option (Fin 3)) ℝ :=
  (!![1, 1, 0, 0; -1, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1 / 2] : Matrix (Fin 4) (Fin 4) ℝ).submatrix
    e4.symm e4.symm

/-- Woodford (2003), App. G.1, (G.4): `A W' = Î W' Ψ'`. -/
theorem good_deflate : zcSys.Ahat * colMat colGood = zcSys.Ihat * colMat colGood * ΨGood := by
  ext a c
  rcases a with a | a <;> rcases c with _ | c <;> fin_cases a <;> (try fin_cases c) <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_option, Fin.sum_univ_three,
      colMat, colGood, ΨGood, e4, LinearRESystem.Ahat, LinearRESystem.Ihat, zcSys, zcA11, zcA12,
      zcA21, zcA22]

/-- Woodford (2003), App. G.1, (G.4): `A W = Î W Ψ`. -/
theorem bad_deflate : zcSys.Ahat * colMat colBad = zcSys.Ihat * colMat colBad * ΨBad := by
  ext a c
  rcases a with a | a <;> rcases c with _ | c <;> fin_cases a <;> (try fin_cases c) <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_option, Fin.sum_univ_three,
      colMat, colBad, ΨBad, e4, LinearRESystem.Ahat, LinearRESystem.Ihat, zcSys, zcA11, zcA12,
      zcA21, zcA22]

/-- Woodford (2003), App. G.1: distinct unit-vector columns are linearly independent. -/
theorem colMat_indep {f : Option (Fin 3) → Fin 3 ⊕ Fin 2} (hf : Function.Injective f) :
    LinearIndependent ℝ (colMat f)ᵀ := by
  have e : (colMat f)ᵀ = fun c => Pi.basisFun ℝ (Fin 3 ⊕ Fin 2) (f c) := by
    funext c a
    simp [colMat, Pi.single_apply]
  rw [e]
  exact (Pi.basisFun ℝ _).linearIndependent.comp f hf

/-- Woodford (2003), App. G.1: the columns of `W'` are distinct unit vectors. -/
theorem colGood_inj : Function.Injective colGood := by decide

/-- Woodford (2003), App. G.1: the columns of `W` are distinct unit vectors. -/
theorem colBad_inj : Function.Injective colBad := by decide

/-- Woodford (2003), App. G.1 (tool): a scalar matrix reindexed along `e4`. -/
theorem scalar_submatrix (ν : ℂ) :
    (Matrix.scalar (Option (Fin 3)) ν).submatrix e4 e4 = Matrix.scalar (Fin 4) ν := by
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, e4.injective.eq_iff]

/-- Woodford (2003), App. G.1: the eigenvalues of `Ψ'` are `1 ± i` and `0` (twice):
`det(ν − Ψ') = ((ν − 1)² + 1) ν²`. -/
theorem good_det (ν : ℂ) : (Matrix.scalar (Option (Fin 3)) ν - ΨGood.map Complex.ofReal).det =
    (ν - (1 + Complex.I)) * (ν - (1 - Complex.I)) * ν ^ 2 := by
  rw [← det_submatrix_equiv_self e4]
  have e : (Matrix.scalar (Option (Fin 3)) ν - ΨGood.map Complex.ofReal).submatrix e4 e4 =
      !![ν - 1, -1, 0, 0; 1, ν - 1, 0, 0; 0, 0, ν, -1; 0, 0, 0, ν] := by
    ext i j
    have hs := congrFun (congrFun (scalar_submatrix ν) i) j
    simp only [submatrix_apply] at hs
    simp only [submatrix_apply, Matrix.sub_apply, hs, ΨGood, Matrix.map_apply,
      Equiv.symm_apply_apply]
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  rw [e, quad_factor]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [Fin.succAbove, Fin.lt_def]
  ring

/-- Woodford (2003), App. G.1: the eigenvalues of `Ψ` are `1 ± i`, `0` and `½`:
`det(ν − Ψ) = ((ν − 1)² + 1) ν (ν − ½)`. -/
theorem bad_det (ν : ℂ) : (Matrix.scalar (Option (Fin 3)) ν - ΨBad.map Complex.ofReal).det =
    (ν - (1 + Complex.I)) * (ν - (1 - Complex.I)) * (ν * (ν - 1 / 2)) := by
  rw [← det_submatrix_equiv_self e4]
  have e : (Matrix.scalar (Option (Fin 3)) ν - ΨBad.map Complex.ofReal).submatrix e4 e4 =
      !![ν - 1, -1, 0, 0; 1, ν - 1, 0, 0; 0, 0, ν, 0; 0, 0, 0, ν - 1 / 2] := by
    ext i j
    have hs := congrFun (congrFun (scalar_submatrix ν) i) j
    simp only [submatrix_apply] at hs
    simp only [submatrix_apply, Matrix.sub_apply, hs, ΨBad, Matrix.map_apply,
      Equiv.symm_apply_apply]
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  rw [e, quad_factor]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [Fin.succAbove, Fin.lt_def]
  ring

/-- Woodford (2003), Assumption 8.2 (ii): the selection plus `conj μ₀` is `{1 − i, 1 + i, ½}`. -/
theorem selPlus_eq : selPlus zc82.sel μ0 =
    (1 - Complex.I) ::ₘ (1 + Complex.I) ::ₘ (1 / 2 : ℂ) ::ₘ 0 := by
  change starRingEnd ℂ μ0 ::ₘ zcSel = _
  rw [zcSel, μ0]
  congr 1
  simp [Complex.ext_iff]

/-- Woodford (2003), App. G.1, (G.4): **`W'` is admissible** — a real deflating basis with
independent columns whose `Ψ'` has eigenvalues `0` and `1 ± i` only. -/
theorem good_admissible : Admissible zcSys (selPlus zc82.sel μ0) (colMat colGood) ΨGood := by
  refine ⟨good_deflate, colMat_indep colGood_inj, fun ν hν => ?_⟩
  rw [good_det] at hν
  rw [selPlus_eq]
  rcases mul_eq_zero.1 hν with h | h
  · rcases mul_eq_zero.1 h with h | h
    · right; rw [sub_eq_zero.1 h]; simp
    · right; rw [sub_eq_zero.1 h]; simp
  · left; exact pow_eq_zero_iff (two_ne_zero) |>.1 h

/-- Woodford (2003), App. G.1, (G.4): **`W` is admissible** — the eigenvalues of its `Ψ` are
`0`, `½` and `1 ± i`. -/
theorem bad_admissible : Admissible zcSys (selPlus zc82.sel μ0) (colMat colBad) ΨBad := by
  refine ⟨bad_deflate, colMat_indep colBad_inj, fun ν hν => ?_⟩
  rw [bad_det] at hν
  rw [selPlus_eq]
  rcases mul_eq_zero.1 hν with h | h
  · rcases mul_eq_zero.1 h with h | h
    · right; rw [sub_eq_zero.1 h]; simp
    · right; rw [sub_eq_zero.1 h]; simp
  · rcases mul_eq_zero.1 h with h | h
    · left; exact h
    · right; rw [sub_eq_zero.1 h]; simp

/-! ### `CondII` holds for `W'` and fails for `W` -/

/-- Woodford (2003), App. G.1, case (ii): `P` selecting the columns `e_{Z₁}, e_{Z₂}, e_{Z₃}` of
`W'` (`J = J⁺P`). -/
def Psel : Matrix (Option (Fin 3)) (Fin 3) ℝ :=
  Matrix.of fun c k => if c = ![none, some 1, some 2] k then 1 else 0

/-- Woodford (2003), App. G.1: `J = W'P = [e_{Z₁}, e_{Z₂}, e_{Z₃}]`. -/
theorem good_JP : colMat colGood * Psel = Matrix.of fun a k => if a = Sum.inl k then 1 else 0 := by
  ext a k
  rcases a with a | a <;> fin_cases a <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fintype.sum_option, colMat, colGood, Psel]

/-- Woodford (2003), App. G.1: `J₁ = I` for `J = W'P`. -/
theorem good_J1 : J1 (colMat colGood * Psel) = 1 := by
  rw [good_JP]
  ext r k
  simp [J1, Matrix.one_apply]

/-- Woodford (2003), App. G.1: `J₂ = 0` for `J = W'P`. -/
theorem good_J2 : J2 (colMat colGood * Psel) = 0 := by
  rw [good_JP]
  ext r k
  simp [J2]

/-- Woodford (2003), (1.20): `K = A₂₂' + A₁₂'Υ = A₂₂'` (`Υ = 0`) for `J = W'P`, invertible. -/
theorem good_K : (Kmat zcSys (colMat colGood * Psel)).det ≠ 0 := by
  have hΥ : Υmat zcSys (colMat colGood * Psel) = 0 := by
    rw [Υmat, good_J2]
    simp
  rw [Kmat, hΥ, Matrix.mul_zero, add_zero, det_transpose]
  change zcA22.det ≠ 0
  rw [zcA22, det_fin_two_of]
  norm_num

/-- Woodford (2003), App. G.1, case (ii): **`CondII` holds for `W'`** with residual root `h = 1`
(`|βh| = 1/4 < 1`). -/
theorem good_cond : CondII zcSys (1 / 4) (colMat colGood) ΨGood Psel 1 := by
  refine ⟨by rw [good_J1, det_one]; exact one_ne_zero, good_K, by norm_num, fun v hv => ?_⟩
  have hv0 : ∀ k, v (![none, some 1, some 2] k) = 0 := by
    intro k
    have := congrFun hv k
    fin_cases k <;> simpa [mulVec, dotProduct, Fintype.sum_option, Psel] using this
  have h0 := hv0 0
  have h1 := hv0 1
  have h2 := hv0 2
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  rw [residProj, good_J1, transpose_one, inv_one, Matrix.mul_one]
  funext c
  rcases c with _ | c
  · simp [mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_option, Matrix.sub_apply,
      Matrix.one_apply, J1, colMat, colGood, Psel, ΨGood, e4, h0, Fin.sum_univ_three]
  · fin_cases c <;>
      simp [mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_option, Matrix.sub_apply,
        Matrix.one_apply, J1, colMat, colGood, Psel, ΨGood, e4, h0, h1, h2, Fin.sum_univ_three]

/-- Woodford (2003), App. G.1, case (ii): **`CondII` fails for `W` for every `P` and `h`**:
`W` has no `Z₃` component, so the third row of `J₁(WP)` vanishes and `J₁` is singular. -/
theorem bad_not_cond (P : Matrix (Option (Fin 3)) (Fin 3) ℝ) (h : ℝ) :
    ¬ CondII zcSys (1 / 4) (colMat colBad) ΨBad P h := by
  rintro ⟨hJ1, -⟩
  apply hJ1
  refine Matrix.det_eq_zero_of_row_eq_zero 2 fun k => ?_
  simp [J1, Matrix.mul_apply, Fintype.sum_option, colMat, colBad, Fin.sum_univ_three]

/-! ### The counterexample -/

/-- **Woodford (2003), Assumption 8.4 (ii) corrected, existential form, for `zcSys`**: the
admissible basis `W'` satisfies `CondII`. -/
theorem zc_ex : Assumption84II zcSys (1 / 4) (selPlus zc82.sel μ0) :=
  ⟨colMat colGood, ΨGood, good_admissible, Psel, 1, good_cond⟩

/-- **Woodford (2003), Assumption 8.4 (ii) corrected, universal form, fails for `zcSys`**: the
admissible basis `W` (the subspace of the book's counting convention: `ker A`, the plane of `1 ± i`
and the eigenvector of `½`) has no `P`, `h` with `CondII`. -/
theorem zc_not_all : ¬ Assumption84IIall zcSys (1 / 4) (selPlus zc82.sel μ0) := by
  intro hall
  obtain ⟨hd, hind, heig⟩ := bad_admissible
  obtain ⟨P, h, hc⟩ := hall _ _ hd hind heig
  exact bad_not_cond P h hc

/-- **Woodford (2003), Assumption 8.4 (ii) corrected (∃ ⇏ ∀ without a semisimple zero root)**:
`zcSys` with `β = 1/4` satisfies every hypothesis of `CaseIIBasis.all_of_ex_semisimple` —
Assumption 8.2 (ii) with the unpaired root `μ₀ = 1 + i`, `sel.erase μ₀` closed under conjugation,
a nonzero (1.15), whole root classes — except that the zero root is not semisimple, and the
existential Assumption 8.4 (ii) holds while the universal one fails. So the semisimplicity
hypothesis of `all_of_ex_semisimple` cannot be dropped. -/
theorem zc_semisimple_needed :
    μ0 ∈ zc82.sel ∧ ConjClosed (zc82.sel.erase μ0) ∧ zcSys.pencilPoly ≠ 0 ∧
      SelWhole zcSys (selPlus zc82.sel μ0) ∧ ¬ ZeroSemisimple zcSys ∧
      Assumption84II zcSys (1 / 4) (selPlus zc82.sel μ0) ∧
      ¬ Assumption84IIall zcSys (1 / 4) (selPlus zc82.sel μ0) :=
  ⟨zc_mem, zc_conjClosed, zc_reg, zc_selWhole, zc_not_zeroSemisimple, zc_ex, zc_not_all⟩

/-- Woodford (2003), (1.1)–(1.4): an LQ problem on `zcSys` (`β = 1/4`, loss `½ i_t²`). -/
noncomputable def zcProblem : LQProblem (Fin 3) (Fin 2) Unit where
  sys := zcSys
  β := 1 / 4
  β_pos := by norm_num
  β_lt_one := by norm_num
  Ttil := 0
  Ti := fun _ => 1
  W := 1
  τstar := 0
  W_posDef := Matrix.PosDef.one

/-- Woodford (2003), **Proposition 8.1 for `zcProblem`** (any expectation system): the
existential corrected Assumption 8.4 (ii) suffices (`CaseIIBasis.prop81_caseII`), although the
universal form fails. -/
theorem zc_prop81 {Ω : Type*} (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    Nonempty (Prop81General.Prop81ConclusionM zcProblem 𝔼 t0) :=
  prop81_caseII zcProblem zc82 zc_mem zc_ex 𝔼 t0

end Woodford.OptimalPolicyRules.TidyR5bCaseIIZeroChain
