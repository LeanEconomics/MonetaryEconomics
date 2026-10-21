/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.CaseIIBasis

/-!
# Case (ii) with `n_Z = 1`: the residual root, the book's normalisation, and an example

Woodford (2003), *Interest and Prices*, Chapter 8, Assumption 8.2 (ii) (p. 552), Assumption 8.4
(ii) (App. G.1, p. 718), Propositions 8.1 and 8.2.

## The residual root as a function of the eigenvector's scaling (`n_Z = 1`)

Let `A u = μ Î u` with `μ = ρ + iσ`. The real and imaginary parts `(a, b)` of `u` span a real
invariant plane with `A a = Î(ρa − σb)`, `A b = Î(σa + ρb)` (`deflate_pair`). Taking `J = a`
(`P = selA`), the residual root of `Prop81CaseII` is `h = ρ + σ b₁/a₁`, where `a₁ + i b₁ = u_ξ`
(`resid_pair`). Rescaling `u` by `c ∈ ℂ` gives `h = hOf ρ σ (c u_ξ)` (`resid_of_eigvec`), which
depends only on the phase of `c` (`hOf_real_mul`).

* `hOf_book`, `book_iff`: at the scaling `c u_ξ ∈ ℝ μ` (the book's normalisation),
  `h⁻¹ = Re μ⁻¹`, so `|βh| < 1 ↔ β < |Re μ⁻¹|` — the book's condition in Assumption 8.2 (ii).
* `hOf_surj`, `book_condition_depends_on_scaling`: for `σ ≠ 0`, every real `h` is attained by some
  scaling, so `|βh| < 1` holds for some scalings and fails for others: the book's condition is
  tied to one normalisation.

## A concrete case-(ii) system (`exSys`, `exProblem`)

`n_Z = n_z = 1`, `A = [[1, 1], [−1, 1]]`, `Î = I`, `β = 1/4`. The roots of (1.15) are `1 ± i`
(`|1 ± i| = √2 < 4`, `Re (1 + i)⁻¹ = 1/2 > 1/4`). Selecting `μ = 1 + i` alone is case (ii) of
Assumption 8.2 (`ex82`). With `J⁺ = I`, `P = e₁`, the residual root is `h = 1` and `|βh| = 1/4`, so
the corrected Assumption 8.4 (ii) holds (`ex84`, and its universal form `ex84all`); hence
`ex_prop81` (Proposition 8.1 for this system, any expectation system) is a genuine instance of
`CaseIIBasis.prop81_caseII`.
-/

namespace Woodford.OptimalPolicyRules.CaseIIInstance

open Matrix GeneralSetup GeneralFOC.LQ PencilSplit Prop81General PencilEigen PencilAssumptions
  PencilRepeated GeneralFOC.Selection Prop81CaseII CaseIIBasis Complex

variable {ιz : Type*} [Fintype ιz] [DecidableEq ιz]
variable {ιZ : Type*} [Fintype ιZ] [DecidableEq ιZ] [Unique ιZ]

/-! ### The residual root for `n_Z = 1` -/

/-- Woodford (2003), App. G.1, case (ii), `n_Z = 1`: the residual root `ρ + σ b₁/a₁` for the
`ξ`-component `w = a₁ + i b₁` of the (scaled) eigenvector of `μ = ρ + iσ`. -/
noncomputable def hOf (ρ σ : ℝ) (w : ℂ) : ℝ := ρ + σ * w.im / w.re

/-- Woodford (2003), App. G.1: the real `2 × 2` block of `μ = ρ + iσ` acting on `(a, b)`
(`none` = real part, `some 0` = imaginary part). -/
def rotΨ (ρ σ : ℝ) : Matrix (Option ιZ) (Option ιZ) ℝ :=
  Matrix.of fun c' c => Option.elim c (Option.elim c' ρ fun _ => -σ) fun _ =>
    Option.elim c' σ fun _ => ρ

/-- Woodford (2003), App. G.1, case (ii): `P` selecting the real part `a` (`J = J⁺P = a`). -/
def selA : Matrix (Option ιZ) ιZ ℝ := Matrix.of fun c _ => Option.elim c 1 fun _ => 0

/-- Woodford (2003), App. G.1: the real basis `(Re u, Im u)` of the plane of a complex
eigenvector `u`. -/
def pairJ (u : ιZ ⊕ ιz → ℂ) : Matrix (ιZ ⊕ ιz) (Option ιZ) ℝ :=
  Matrix.of fun a c => Option.elim c (u a).re fun _ => (u a).im

/-- Woodford (2003), App. G.1, (G.1) and fn 2: for `A u = μ Î u`, the real and imaginary parts
satisfy `A (a, b) = Î (a, b) [[ρ, σ], [−σ, ρ]]`. -/
theorem deflate_pair (S : LinearRESystem ιZ ιz) {μ : ℂ} {u : ιZ ⊕ ιz → ℂ}
    (hu : S.Ahat.map Complex.ofReal *ᵥ u = μ • (S.Ihat.map Complex.ofReal *ᵥ u)) :
    S.Ahat * pairJ u = S.Ihat * pairJ u * rotΨ μ.re μ.im := by
  ext a c
  have e := congrFun hu a
  have hre := congrArg Complex.re e
  have him := congrArg Complex.im e
  simp only [mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul, Complex.re_sum,
    Complex.im_sum, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero] at hre him
  rcases c with _ | c
  · simp only [Matrix.mul_apply, pairJ, rotΨ, of_apply, Option.elim, Fintype.sum_option,
      Finset.univ_unique, Finset.sum_singleton]
    linear_combination hre
  · simp only [Matrix.mul_apply, pairJ, rotΨ, of_apply, Option.elim, Fintype.sum_option,
      Finset.univ_unique, Finset.sum_singleton]
    linear_combination him

/-- Woodford (2003), App. G.1: the inverse of a nonzero `1 × 1` matrix. -/
theorem inv_fin_one {M : Matrix ιZ ιZ ℝ} (h : M default default ≠ 0) :
    M⁻¹ = Matrix.of fun _ _ => (M default default)⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  rw [Subsingleton.elim i default, Subsingleton.elim j default]
  simp [Matrix.mul_apply, h]

omit [Fintype ιz] [DecidableEq ιz] in
/-- Woodford (2003), App. G.1, case (ii), `n_Z = 1`: with `J = a` (`P = selA`), the residual
root on `ker P'` is `hOf ρ σ (a₁ + i b₁) = ρ + σ b₁/a₁`, for any real basis `(a, b)` with
`a₁ ≠ 0`. -/
theorem resid_pair (Jp : Matrix (ιZ ⊕ ιz) (Option ιZ) ℝ) (ρ σ : ℝ)
    (ha : Jp (Sum.inl default) none ≠ 0) (v : Option ιZ → ℝ) (hv : selAᵀ *ᵥ v = 0) :
    (residProj Jp selA * (rotΨ ρ σ)ᵀ) *ᵥ v =
      hOf ρ σ ⟨Jp (Sum.inl default) none, Jp (Sum.inl default) (some default)⟩ • v := by
  have hv0 : v none = 0 := by
    have := congrFun hv default
    simpa [mulVec, dotProduct, selA, Fintype.sum_option] using this
  have hJ1 : (J1 (Jp * selA))ᵀ default default = Jp (Sum.inl default) none := by
    simp [J1, Matrix.mul_apply, selA, Fintype.sum_option]
  rw [residProj, inv_fin_one (by rw [hJ1]; exact ha), hJ1]
  funext c
  rcases c with _ | c
  · simp [mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_option, selA, rotΨ, J1,
      Matrix.sub_apply, Matrix.one_apply, hv0, hOf, mul_inv_cancel₀ ha]
  · rw [Subsingleton.elim c default]
    simp only [mulVec, dotProduct, J1, transpose_submatrix, selA, rotΨ,
      Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Finset.univ_unique,
      submatrix_apply, id_eq, transpose_apply, of_apply, Finset.sum_singleton, Finset.sum_const,
      Finset.card_singleton, one_smul, Fintype.sum_option, reduceCtorEq, ↓reduceIte,
      Option.elim_none, mul_one, zero_sub, neg_mul, Option.some.injEq, Option.elim_some, mul_zero,
      sub_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_singleton, hv0, mul_neg,
      neg_neg, zero_add, hOf, Pi.smul_apply, smul_eq_mul, mul_eq_mul_right_iff]
    left
    field_simp
    ring

/-- Woodford (2003), App. G.1, case (ii), `n_Z = 1`: **the residual root as a function of the
eigenvector's scaling** — for `A u = μ Î u` and any `c ∈ ℂ` with `Re(c u_ξ) ≠ 0`, the basis
`(Re(cu), Im(cu))` is a deflating pair for `[[ρ, σ], [−σ, ρ]]`, and with `J = Re(cu)` the residual
root is `hOf ρ σ (c u_ξ)`. -/
theorem resid_of_eigvec (S : LinearRESystem ιZ ιz) {μ : ℂ} {u : ιZ ⊕ ιz → ℂ}
    (hu : S.Ahat.map Complex.ofReal *ᵥ u = μ • (S.Ihat.map Complex.ofReal *ᵥ u)) (c : ℂ)
    (ha : (c * u (Sum.inl default)).re ≠ 0) :
    S.Ahat * pairJ (c • u) = S.Ihat * pairJ (c • u) * rotΨ μ.re μ.im ∧
      ∀ v, selAᵀ *ᵥ v = 0 → (residProj (pairJ (c • u)) selA * (rotΨ μ.re μ.im)ᵀ) *ᵥ v =
        hOf μ.re μ.im (c * u (Sum.inl default)) • v := by
  have hcu : S.Ahat.map Complex.ofReal *ᵥ (c • u) = μ • (S.Ihat.map Complex.ofReal *ᵥ (c • u)) := by
    rw [mulVec_smul, hu, mulVec_smul, smul_comm]
  refine ⟨deflate_pair S hcu, fun v hv => ?_⟩
  rw [resid_pair _ _ _ ha v hv]
  rfl

/-- Woodford (2003), App. G.1: the residual root depends only on the phase of the scaling. -/
theorem hOf_real_mul (ρ σ : ℝ) (w : ℂ) {r : ℝ} (hr : r ≠ 0) :
    hOf ρ σ ((r : ℂ) * w) = hOf ρ σ w := by
  unfold hOf
  simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  by_cases hw : w.re = 0
  · simp [hw]
  · field_simp

/-- Woodford (2003), Assumption 8.2 (ii) and 8.4 (ii): **at the book's normalisation** (the
`ξ`-component of the eigenvector a real multiple of `μ`), the residual root satisfies
`h⁻¹ = Re μ⁻¹`. -/
theorem hOf_book {μ : ℂ} (hρ : μ.re ≠ 0) {r : ℝ} (hr : r ≠ 0) :
    (hOf μ.re μ.im ((r : ℂ) * μ))⁻¹ = (μ⁻¹).re := by
  rw [hOf_real_mul _ _ _ hr, hOf, Complex.inv_re, Complex.normSq_apply]
  have h2 : μ.re * μ.re + μ.im * μ.im ≠ 0 :=
    (by nlinarith [mul_self_pos.mpr hρ, mul_self_nonneg μ.im] : 0 < μ.re * μ.re + μ.im * μ.im).ne'
  field_simp

/-- Woodford (2003), Assumption 8.2 (ii), p. 552: at the book's normalisation, **`|βh| < 1` is
exactly the book's condition `β < |Re μ⁻¹|`**. -/
theorem book_iff {μ : ℂ} (hρ : μ.re ≠ 0) {r : ℝ} (hr : r ≠ 0) {β : ℝ} (hβ : 0 < β) :
    |β * hOf μ.re μ.im ((r : ℂ) * μ)| < 1 ↔ β < |(μ⁻¹).re| := by
  rw [← hOf_book hρ hr]
  set h := hOf μ.re μ.im ((r : ℂ) * μ) with hh
  have hne : h ≠ 0 := by
    intro h0
    have := hOf_book hρ hr
    rw [← hh, h0, _root_.inv_zero, Complex.inv_re] at this
    have hμ : μ ≠ 0 := fun h0 => hρ (by rw [h0]; simp)
    exact div_ne_zero hρ (Complex.normSq_pos.mpr hμ).ne' this.symm
  have habs : 0 < |h| := abs_pos.mpr hne
  rw [abs_mul, abs_of_pos hβ, abs_inv, ← one_div, lt_div_iff₀ habs]

/-- Woodford (2003), App. G.1: for `σ ≠ 0`, **every real number is the residual root at some
scaling** of the eigenvector (`u_ξ ≠ 0`). -/
theorem hOf_surj (ρ : ℝ) {σ : ℝ} (hσ : σ ≠ 0) {u1 : ℂ} (hu1 : u1 ≠ 0) (h' : ℝ) :
    ∃ c : ℂ, c ≠ 0 ∧ (c * u1).re ≠ 0 ∧ hOf ρ σ (c * u1) = h' := by
  set t : ℝ := (h' - ρ) / σ with ht
  have hz : (1 + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
  refine ⟨(1 + (t : ℂ) * Complex.I) / u1, div_ne_zero hz hu1, ?_, ?_⟩
  · rw [div_mul_cancel₀ _ hu1]
    simp
  · rw [div_mul_cancel₀ _ hu1, hOf]
    simp [ht]
    field_simp
    ring

/-- Woodford (2003), Assumption 8.2 (ii) and 8.4 (ii): **the condition `|βh| < 1` depends on the
eigenvector's normalisation** — for `σ ≠ 0` some scalings satisfy it and others do not. So the
book's `|Re μ⁻¹| > β`, which is `|βh| < 1` at one scaling (`book_iff`), is normalisation-specific,
and the normalisation-free replacement is `CaseIIBasis.Assumption84II`. -/
theorem book_condition_depends_on_scaling (ρ : ℝ) {σ : ℝ} (hσ : σ ≠ 0) {u1 : ℂ} (hu1 : u1 ≠ 0)
    {β : ℝ} (hβ : 0 < β) :
    (∃ c : ℂ, c ≠ 0 ∧ (c * u1).re ≠ 0 ∧ |β * hOf ρ σ (c * u1)| < 1) ∧
      ∃ c : ℂ, c ≠ 0 ∧ (c * u1).re ≠ 0 ∧ ¬ |β * hOf ρ σ (c * u1)| < 1 := by
  obtain ⟨c0, hc0, hr0, he0⟩ := hOf_surj ρ hσ hu1 0
  obtain ⟨c1, hc1, hr1, he1⟩ := hOf_surj ρ hσ hu1 β⁻¹
  refine ⟨⟨c0, hc0, hr0, by rw [he0]; simp⟩, c1, hc1, hr1, ?_⟩
  rw [he1, mul_inv_cancel₀ hβ.ne', abs_one]
  exact lt_irrefl 1


/-! ### A concrete system in case (ii) -/

/-- Woodford (2003), (1.1), p. 537, a concrete instance: `n_Z = n_z = 1`, `A = [[1, 1], [−1, 1]]`,
`Ẽ = 1` (so `Î = I`), `B₂ = 1`. -/
noncomputable def exSys : LinearRESystem (Fin 1) (Fin 1) where
  A11 := !![1]
  A12 := !![1]
  A21 := !![-1]
  A22 := !![1]
  Et := !![1]
  B2 := ![1]
  A22_isUnit := by simp
  B2_ne_zero := by
    intro h
    have := congrFun h 0
    simp at this

/-- Woodford (2003), (1.1)–(1.4), p. 537: `exSys` with `β = 1/4` and `W = I` as an LQ problem. -/
noncomputable def exProblem : LQProblem (Fin 1) (Fin 1) (Fin 1) where
  sys := exSys
  β := 1 / 4
  β_pos := by norm_num
  β_lt_one := by norm_num
  Ttil := 0
  Ti := 0
  W := 1
  τstar := 0
  W_posDef := Matrix.PosDef.one

/-- Woodford (2003), (1.15) for `exSys`: the selected root `μ = 1 + i`. -/
noncomputable def μ0 : ℂ := 1 + Complex.I

/-- Woodford (2003), (G.1) for `exSys`: the eigenvector `u = (1, i)` of `μ = 1 + i`. -/
noncomputable def u0 : Fin 1 ⊕ Fin 1 → ℂ := Sum.elim (fun _ => 1) fun _ => Complex.I

/-- Woodford (2003), (G.1): `A u = μ Î u` for `exSys`. -/
theorem ex_eig : exSys.Ahat.map Complex.ofReal *ᵥ u0 =
    μ0 • (exSys.Ihat.map Complex.ofReal *ᵥ u0) := by
  funext a
  rcases a with a | a <;> rw [Fin.fin_one_eq_zero a] <;> apply Complex.ext <;>
    simp [mulVec, dotProduct, Fintype.sum_sum_type, LinearRESystem.Ahat, LinearRESystem.Ihat,
      exSys, u0, μ0]

/-- Woodford (2003), (1.15) for `exSys`: `1 + i` is a root. -/
theorem ex_root : exSys.pencilPoly.eval μ0 = 0 := by
  rw [pencilPoly_eval]
  refine exists_mulVec_eq_zero_iff.mp ⟨u0, ?_, ?_⟩
  · intro h
    have := congrFun h (Sum.inl 0)
    simp [u0] at this
  · rw [sub_mulVec, ex_eig, smul_mulVec, sub_self]

/-- Woodford (2003), (1.1) for `exSys`: `A` is invertible (`A⁻¹ = ½ [[1, −1], [1, 1]]`). -/
theorem ex_det : IsUnit exSys.Ahat.det := by
  refine Matrix.isUnit_det_of_right_inverse
    (B := fromBlocks !![1 / 2] !![-1 / 2] !![1 / 2] !![1 / 2]) ?_
  rw [LinearRESystem.Ahat, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> ext i j <;> rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j] <;>
    simp [exSys] <;> norm_num

/-- Woodford (2003), (1.15) for `exSys`: the polynomial is nonzero (its value at `0` is
`det A ≠ 0`). -/
theorem ex_reg : exSys.pencilPoly ≠ 0 := by
  intro h
  have e := det_pencil_ofReal exSys 0
  rw [← pencilPoly_eval, h, Polynomial.eval_zero, zero_smul, sub_zero] at e
  exact ex_det.ne_zero (Complex.ofReal_eq_zero.mp e.symm)

/-- Woodford (2003), p. 547 for `exSys`: `rank A = 2`. -/
theorem ex_rank : exSys.Ahat.rank = 2 := by
  rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr ex_det)]
  simp

/-- Woodford (2003), Assumption 8.2 for `exSys`: `1 + i` is a nonzero root with
`|1 + i| = √2 < β⁻¹ = 4`. -/
theorem ex_mem : μ0 ∈ exSys.pencilPoly.roots.filter
    (fun μ => μ ≠ 0 ∧ ‖μ‖ < ((1 : ℝ) / 4)⁻¹) := by
  refine Multiset.mem_filter.mpr ⟨(Polynomial.mem_roots ex_reg).mpr ex_root, ?_, ?_⟩
  · intro h
    have := congrArg Complex.re h
    simp [μ0] at this
  · refine (Complex.norm_le_abs_re_add_abs_im μ0).trans_lt ?_
    simp [μ0]
    norm_num

/-- Woodford (2003), **Assumption 8.2, case (ii)**, for `exProblem`: select the single root
`1 + i` (`n_Z = 1`, `n − rank A = 0`); its conjugate is unselected and
`Re (1 + i)⁻¹ = 1/2 > β = 1/4`. -/
noncomputable def ex82 : Assumption82 exProblem.sys exProblem.β where
  count := by
    change Fintype.card (Fin 1) ≤ exSys.stableCount ((1 : ℝ) / 4)⁻¹
    unfold LinearRESystem.stableCount
    rw [ex_rank]
    have := Multiset.card_pos_iff_exists_mem.mpr ⟨μ0, ex_mem⟩
    simp only [Fintype.card_fin, Fintype.card_sum]
    omega
  sel := {μ0}
  sel_le := Multiset.singleton_le.mpr ex_mem
  sel_card := by
    change Multiset.card {μ0} + (Fintype.card (Fin 1 ⊕ Fin 1) - exSys.Ahat.rank) =
      Fintype.card (Fin 1)
    rw [ex_rank]
    simp
  cases := by
    refine Or.inr ⟨μ0, Multiset.mem_singleton_self _, ?_, ?_, ?_⟩
    · rw [Multiset.mem_singleton]
      intro h
      have := congrArg Complex.im h
      simp [μ0] at this
      norm_num at this
    · rw [Multiset.erase_singleton]
      simp [ConjClosed]
    · change (1 : ℝ) / 4 < |(μ0⁻¹).re|
      rw [Complex.inv_re, Complex.normSq_apply]
      simp [μ0]
      norm_num

/-- Woodford (2003), Assumption 8.2 for `exProblem`: the selection is **not** closed under
conjugation, so this is case (ii), not case (i). -/
theorem ex_not_caseI : ¬ ConjClosed ex82.sel := by
  intro h
  have hm : starRingEnd ℂ μ0 ∈ ex82.sel := h.conj_mem (Multiset.mem_singleton_self μ0)
  change starRingEnd ℂ μ0 ∈ ({μ0} : Multiset ℂ) at hm
  rw [Multiset.mem_singleton] at hm
  have := congrArg Complex.im hm
  simp [μ0] at this
  norm_num at this

/-- Woodford (2003), App. G.1, for `exSys`: `(Re u, Im u)` with `[[1, 1], [−1, 1]]` is an
admissible basis of the invariant subspace of `{1 − i, 1 + i}`. -/
theorem ex_admissible : Admissible exSys (selPlus ex82.sel μ0) (pairJ u0) (rotΨ 1 1) := by
  have hre : μ0.re = 1 := by simp [μ0]
  have him : μ0.im = 1 := by simp [μ0]
  refine ⟨?_, ?_, fun ν hν => ?_⟩
  · have hd := deflate_pair exSys ex_eig
    rw [hre, him] at hd
    exact hd
  · refine Fintype.linearIndependent_iff.mpr fun g hg c => ?_
    have h1 : g none = 0 := by
      simpa [Fintype.sum_option, pairJ, u0] using congrFun hg (Sum.inl 0)
    have h2 : g (some 0) = 0 := by
      simpa [Fintype.sum_option, pairJ, u0] using congrFun hg (Sum.inr 0)
    rcases c with _ | c
    · exact h1
    · rw [Fin.fin_one_eq_zero c]
      exact h2
  · right
    obtain ⟨z, hz0, hz⟩ := exists_eigvec hν
    have e1 : z none + z (some 0) = ν * z none := by
      simpa [mulVec, dotProduct, Fintype.sum_option, rotΨ] using congrFun hz none
    have e2 : -z none + z (some 0) = ν * z (some 0) := by
      simpa [mulVec, dotProduct, Fintype.sum_option, rotΨ] using congrFun hz (some 0)
    have hzn : z none ≠ 0 := by
      intro h0
      apply hz0
      funext c
      rcases c with _ | c
      · exact h0
      · rw [Fin.fin_one_eq_zero c]
        rw [h0] at e1
        simpa using e1
    have hq : ((ν - 1) ^ 2 + 1) * z none = 0 := by
      linear_combination (1 - ν) * e1 - e2
    have hq2 : (ν - (1 + Complex.I)) * (ν - (1 - Complex.I)) = 0 := by
      linear_combination (mul_eq_zero.mp hq).resolve_right hzn - Complex.I_sq
    rcases mul_eq_zero.mp hq2 with h | h
    · rw [sub_eq_zero.mp h]
      exact Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _)
    · rw [sub_eq_zero.mp h]
      have : starRingEnd ℂ μ0 = 1 - Complex.I := by
        apply Complex.ext <;> simp [μ0]
      rw [← this]
      exact Multiset.mem_cons_self _ _

/-- Woodford (2003), **Assumption 8.4 (ii), corrected, holds for `exProblem`**: with `J = Re u`
(`P = selA`), `J₁ = 1`, `K = 1` and the residual root is `h = 1`, `|βh| = 1/4 < 1`. -/
theorem ex84 : Assumption84II exProblem.sys exProblem.β (selPlus ex82.sel μ0) := by
  have ha : pairJ u0 (Sum.inl 0) none ≠ 0 := by simp [pairJ, u0]
  refine ⟨pairJ u0, rotΨ 1 1, ex_admissible, selA,
    hOf 1 1 ⟨pairJ u0 (Sum.inl 0) none, pairJ u0 (Sum.inl 0) (some 0)⟩, ?_, ?_, ?_,
    fun v hv => resid_pair (pairJ u0) 1 1 ha v hv⟩
  · rw [Matrix.det_unique]
    simp [J1, Matrix.mul_apply, Fintype.sum_option, pairJ, selA, u0]
  · have hJ2 : J2 (pairJ u0 * selA) = 0 := by
      ext i j
      simp [J2, Matrix.mul_apply, Fintype.sum_option, pairJ, selA, u0]
    change (Kmat exSys (pairJ u0 * selA)).det ≠ 0
    rw [Kmat, Υmat, hJ2]
    simp [exSys]
  · change |(1 : ℝ) / 4 * hOf 1 1 ⟨pairJ u0 (Sum.inl 0) none, pairJ u0 (Sum.inl 0) (some 0)⟩| < 1
    simp [hOf, pairJ, u0]
    norm_num

/-- Woodford (2003), Assumption 8.4 (ii) corrected, universal form, for `exProblem` (every
admissible basis spans the whole plane, `sameSubspace_of_card`). -/
theorem ex84all : Assumption84IIall exProblem.sys exProblem.β (selPlus ex82.sel μ0) := by
  refine all_of_ex ex_reg (fun ν hν => ?_) (sameSubspace_of_card (by simp)) ex84
  change ν ∈ starRingEnd ℂ μ0 ::ₘ ({μ0} : Multiset ℂ) at hν
  rw [Multiset.mem_cons, Multiset.mem_singleton] at hν
  rcases hν with rfl | rfl
  · exact pencil_eval_conj exSys ex_root
  · exact ex_root

/-- Woodford (2003), **Proposition 8.1 in case (ii) is not vacuous**: `exProblem` satisfies
Assumption 8.2 (case (ii), `ex82`, `ex_not_caseI`) and the corrected Assumption 8.4 (ii) (`ex84`),
so `CaseIIBasis.prop81_caseII` gives the corrected Proposition 8.1 for it, for any expectation
system. -/
theorem ex_prop81 {Ω : Type*} (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    Nonempty (Prop81ConclusionM exProblem 𝔼 t0) :=
  prop81_caseII exProblem ex82 (μ := μ0) (Multiset.mem_singleton_self μ0) ex84 𝔼 t0

end Woodford.OptimalPolicyRules.CaseIIInstance
