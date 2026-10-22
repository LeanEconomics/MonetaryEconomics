/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR5aExogenousInstrument

/-!
# Determinacy under an exogenous instrument for every `Ẽ` (p. 546)

Woodford (2003), *Interest and Prices*, Chapter 8, §1.2, pp. 546–547, with (1.1) (p. 537) and
the characteristic equation (1.15), `det[A − μÎ] = 0`, `Î = diag(I, Ẽ)`.
`TidyR5aExogenousInstrument.Exo.exoDeterminate_iff` proves the determinacy claim of p. 546 for
invertible `Ẽ`. Here `Ẽ` is arbitrary.

## The reduction (a pencil decomposition)

* `exists_fitting`: the Fitting decomposition in matrix form.
* `pen`, `Decomp`, `nonempty_decomp`: if `det[A − μÎ] ≢ 0` (a **regular** pencil), pick a real `α`
  with `A − αÎ` invertible and split `F = (A − αÎ)⁻¹Î` into `diag(N, G)`, with `N` nilpotent (the
  static rows and the "roots at infinity") and `G` invertible.
* `Decomp.bigA = P diag(2I, G⁻¹ + αI) Q`: a full-dimension Blanchard–Kahn matrix, with the same
  ordering of the variables. `Decomp.eigs_bigA`: its eigenvalues are the finite roots of (1.15)
  plus `2` once for each infinite root. Hence `Decomp.stableCount_bigA` and
  `Decomp.noUnit_bigA_iff`.
* `Decomp.dsolves_iff_solves`: a bounded adapted process solves `Î E_ty_{t+1} = Ay_t + h_t` iff
  it solves `E_ty_{t+1} = bigA y_t + wBig_t`. On the nilpotent block both forms have exactly one
  bounded solution, the forcing-driven `Decomp.vstar`.

## Main results

* `Sys.exoSol_to_equil`, `Sys.equil_to_exoSol`: solutions of (1.1) with an exogenous instrument
  are exactly the Blanchard–Kahn equilibria of `Decomp.bigA`.
* `Sys.exoDeterminate_iff_bk`, `Sys.exoDeterminate_iff_roots`: determinacy under a decomposition.
* `Sys.not_exoDeterminate_of_pencil_zero`: **a singular pencil is never determinate**. A
  polynomial null vector of `A − μÎ`, read backwards in time, gives a second bounded solution.
* **`Sys.exoDeterminate_iff_count`** (p. 546, every `Ẽ`): with no root of (1.15) on the unit
  circle, determinacy holds iff (1.15) has exactly `n_Z` roots with `|μ| < 1` and the genericity
  condition holds.
* `Sys.not_exoDeterminate_of_card_lt`, **`Sys.sargentWallace_not_exoDeterminate`** (pp. 546–547,
  every `Ẽ`; via `X_pow_dvd_det`, the zero root has multiplicity `≥ n − rank A`).
* `Sys.singSys`, `Sys.singSys_pencilPoly`, `Sys.singSys_not_exoDeterminate`: a system with
  `A₂₂ = I` and singular `Ẽ` whose pencil is singular. No exogenous rule is determinate there.

So, compared with the invertible case, three things change:
(i) only the finite roots of (1.15) are counted, since its degree drops by `rank`-deficiency of
`Ẽ` and the missing "roots at infinity" act as unstable roots;
(ii) a singular pencil is indeterminate (it then has no roots, so the count `n_Z` fails unless
`n_Z = 0`, and `n_Z = 0` forces regularity, `Sys.pencil_ne_zero_of_isEmpty`);
(iii) the genericity condition is that of `Decomp.bigA`.
-/

namespace Woodford.OptimalPolicyRules.TidyR5aExoSingular

open Matrix Polynomial BKForward BKInvariantSplit

/-! ### Determinant tools -/

variable {𝕜 : Type*} [Field 𝕜] {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
  [DecidableEq m]

/-- Woodford (2003), (1.15) (tool): conjugation by a pair of mutually inverse rectangular
matrices preserves the determinant. -/
theorem det_conj_rect {P : Matrix n m 𝕜} {Q : Matrix m n 𝕜} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (Y : Matrix m m 𝕜) : (P * Y * Q).det = Y.det := by
  have e : P * Y * Q = 1 + P * ((Y - 1) * Q) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, hPQ, ← Matrix.mul_assoc]
    abel
  rw [e, det_one_add_mul_comm, Matrix.mul_assoc, hQP, Matrix.mul_one, add_sub_cancel]

/-- Woodford (2003), (1.15) (tool): `det(I − cN) = 1` for a nilpotent `N`. -/
theorem det_one_sub_smul_nilpotent {N : Matrix m m 𝕜} {j : ℕ} (hN : N ^ j = 0) (c : 𝕜) :
    (1 - c • N).det = 1 := by
  have hu : IsUnit N.charpolyRev := isUnit_charpolyRev_of_isNilpotent ⟨j, hN⟩
  obtain ⟨r, -, hr⟩ := Polynomial.isUnit_iff.mp hu
  have h0 : N.charpolyRev.eval 0 = 1 := eval_charpolyRev
  rw [← hr, eval_C] at h0
  have hev : N.charpolyRev.eval c = (1 - c • N).det := by
    rw [charpolyRev, ← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext a b
    by_cases hab : a = b
    · subst hab
      simp only [RingHom.mapMatrix_apply, map_apply, Matrix.sub_apply, one_apply_eq,
        Matrix.smul_apply, smul_eq_mul, coe_evalRingHom, eval_sub, eval_one, eval_mul, eval_X,
        eval_C]
    · simp only [RingHom.mapMatrix_apply, map_apply, Matrix.sub_apply, one_apply_ne hab,
        Matrix.smul_apply, smul_eq_mul, coe_evalRingHom, eval_sub, eval_zero, eval_mul, eval_X,
        eval_C]
  rw [← hev, ← hr, eval_C, h0]

/-- Woodford (2003), (1.15) (tool): `det(I − c·diag(N, G)) = det(I − cN) det(I − cG)`. -/
theorem det_one_sub_fromBlocks {k r : Type*} [Fintype k] [Fintype r] [DecidableEq k]
    [DecidableEq r] (N : Matrix k k 𝕜) (G : Matrix r r 𝕜) (c : 𝕜) :
    (1 - c • fromBlocks N 0 0 G).det = (1 - c • N).det * (1 - c • G).det := by
  have e : 1 - c • fromBlocks N 0 0 G = fromBlocks (1 - c • N) 0 0 (1 - c • G) := by
    rw [← fromBlocks_one, fromBlocks_smul]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]
  rw [e, det_fromBlocks_zero₂₁]

/-- **Woodford (2003), (1.15): the pencil factorises through the decomposition.** If
`H = A − aÎ` is invertible (`Hi`), `P, Q` are mutually inverse and `Q H⁻¹ Î P = diag(N, G)` with
`N` nilpotent and `G` invertible (`Gi`), then
`det(A − μÎ) = det H · det G · det((G⁻¹ + aI) − μI)`. -/
theorem det_pencil_eq {k r : Type*} [Fintype k] [Fintype r] [DecidableEq k] [DecidableEq r]
    {A I Hi : Matrix n n 𝕜} {a : 𝕜} (h2 : (A - a • I) * Hi = 1)
    {P : Matrix n (k ⊕ r) 𝕜} {Q : Matrix (k ⊕ r) n 𝕜} (hPQ : P * Q = 1)
    {N : Matrix k k 𝕜} {G Gi : Matrix r r 𝕜} {j : ℕ} (hN : N ^ j = 0) (hG : G * Gi = 1)
    (hD : Q * Hi * I * P = fromBlocks N 0 0 G) (μ : 𝕜) :
    (A - μ • I).det = (A - a • I).det * G.det * ((Gi + a • 1) - μ • 1).det := by
  have e1 : A - μ • I = (A - a • I) * (1 - (μ - a) • (Hi * I)) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, h2, Matrix.one_mul,
      sub_smul]
    abel
  have e2 : (1 - (μ - a) • (Hi * I)).det = (1 - (μ - a) • fromBlocks N 0 0 G).det := by
    have e : Hi * I = (Hi * I * P) * Q := by rw [Matrix.mul_assoc _ P Q, hPQ, Matrix.mul_one]
    rw [e, ← Matrix.smul_mul, det_one_sub_mul_comm, Matrix.mul_smul, ← hD]
    simp only [Matrix.mul_assoc]
  have e3 : 1 - (μ - a) • G = G * ((Gi + a • 1) - μ • 1) := by
    rw [Matrix.mul_sub, Matrix.mul_add, hG, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul,
      Matrix.mul_one, sub_smul]
    abel
  rw [e1, det_mul, e2, det_one_sub_fromBlocks, det_one_sub_smul_nilpotent hN, e3, det_mul]
  ring

/-! ### The Fitting decomposition in matrix form -/

/-- **Woodford (2003), (1.15) (tool): the Fitting decomposition, in matrix form.** For every real
square matrix `F` there are mutually inverse `P`, `Q` with `Q F P = diag(N, G)`, `N` nilpotent and
`G` invertible (`ker Fʲ ⊕ range Fʲ` for large `j`). -/
theorem exists_fitting (F : Matrix n n ℝ) : ∃ (j k r : ℕ) (P : Matrix n (Fin k ⊕ Fin r) ℝ)
    (Q : Matrix (Fin k ⊕ Fin r) n ℝ) (N : Matrix (Fin k) (Fin k) ℝ)
    (G : Matrix (Fin r) (Fin r) ℝ), P * Q = 1 ∧ Q * P = 1 ∧ N ^ j = 0 ∧ IsUnit G.det ∧
      Q * F * P = fromBlocks N 0 0 G := by
  set f : Module.End ℝ (n → ℝ) := Matrix.toLin' F with hf
  obtain ⟨j, hj, hj1⟩ :=
    (f.eventually_isCompl_ker_pow_range_pow.and (Filter.eventually_ge_atTop 1)).exists
  set K := LinearMap.ker (f ^ j) with hKdef
  set R := LinearMap.range (f ^ j) with hRdef
  have hcomm : f * f ^ j = f ^ j * f := (Commute.self_pow f j).eq
  have hK : ∀ x ∈ K, f x ∈ K := by
    intro x hx
    rw [hKdef, LinearMap.mem_ker] at hx ⊢
    rw [← Module.End.mul_apply, ← hcomm, Module.End.mul_apply, hx, map_zero]
  have hR : ∀ x ∈ R, f x ∈ R := by
    rintro x ⟨y, rfl⟩
    exact ⟨f y, by rw [← Module.End.mul_apply, ← hcomm, Module.End.mul_apply]⟩
  set fK := f.restrict hK with hfK
  set fR := f.restrict hR with hfR
  set bK := Module.finBasis ℝ K with hbK
  set bR := Module.finBasis ℝ R with hbR
  set b := (bK.prod bR).map (Submodule.prodEquivOfIsCompl K R hj) with hb
  set e := Pi.basisFun ℝ n with he
  refine ⟨j, _, _, e.toMatrix b, b.toMatrix e, LinearMap.toMatrix bK bK fK,
    LinearMap.toMatrix bR bR fR, Module.Basis.toMatrix_mul_toMatrix_flip _ _,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, ?_, ?_, ?_⟩
  · rw [LinearMap.toMatrix_pow, Module.End.pow_restrict]
    have h0 : (f ^ j).restrict (Module.End.pow_apply_mem_of_forall_mem j hK) = 0 := by
      ext x
      simp only [LinearMap.restrict_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero]
      exact congrFun (LinearMap.mem_ker.mp x.2) _
    rw [h0, map_zero]
  · rw [LinearMap.det_toMatrix, ← LinearMap.isUnit_iff_isUnit_det,
      LinearMap.isUnit_iff_ker_eq_bot, eq_bot_iff]
    rintro ⟨x, hxR⟩ hx
    rw [LinearMap.mem_ker] at hx
    have hfx : f x = 0 := by
      have := congrArg Subtype.val hx
      simpa [hfR] using this
    have hxK : x ∈ K := by
      rw [hKdef, LinearMap.mem_ker]
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [pow_succ, Module.End.mul_apply, hfx, map_zero]
    have h0 : x = 0 := by
      have := hj.disjoint.le_bot ⟨hxK, hxR⟩
      simpa using this
    simp [h0]
  · have h1 : b.toMatrix e * F * e.toMatrix b = LinearMap.toMatrix b b f := by
      have hF : LinearMap.toMatrix e e f = F := by
        rw [he, LinearMap.toMatrix_eq_toMatrix', hf, LinearMap.toMatrix'_toLin']
      rw [← hF]
      exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (b := b) (b' := e) (c := b)
        (c' := e) (f := f)
    rw [h1]
    ext c c'
    rw [LinearMap.toMatrix_apply]
    rcases c' with a | a
    · have hm : f (b (Sum.inl a)) = ((fK (bK a) : K) : n → ℝ) := by
        simp [hb, hfK]
      rw [hm]
      rcases c with c | c
      · simp [hb, LinearMap.toMatrix_apply]
      · simp [hb]
    · have hm : f (b (Sum.inr a)) = ((fR (bR a) : R) : n → ℝ) := by
        simp [hb, hfR]
      rw [hm]
      rcases c with c | c
      · simp [hb]
      · simp [hb, LinearMap.toMatrix_apply]

/-! ### The decomposition of a regular pencil -/

/-- Woodford (2003), (1.15), p. 546: the characteristic polynomial `det[A − μÎ]` of a real pencil
`(A, Î)` (over `ℂ`). -/
noncomputable def pen (A I : Matrix n n ℝ) : ℂ[X] :=
  (A.map (fun a => C (a : ℂ)) - (X : ℂ[X]) • I.map (fun a => C (a : ℂ))).det

/-- Woodford (2003), (1.15): `pen` evaluated at `μ` is `det(A − μÎ)`. -/
theorem pen_eval (A I : Matrix n n ℝ) (μ : ℂ) :
    (pen A I).eval μ = (A.map Complex.ofReal - μ • I.map Complex.ofReal).det := by
  rw [pen, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
    Polynomial.coe_evalRingHom, Polynomial.eval_sub, Polynomial.eval_C, smul_eq_mul,
    Polynomial.eval_mul, Polynomial.eval_X]

/-- Woodford (2003), (1.1) and (1.15): a **decomposition of the pencil** `(A, Î)`: a real `α` with
`A − αÎ` invertible (inverse `Hi`), and mutually inverse `P`, `Q` with
`Q (A − αÎ)⁻¹ Î P = diag(N, G)`, `N` nilpotent, `G` invertible (inverse `Gi`). It exists when the
pencil is regular (`nonempty_decomp`). -/
structure Decomp (A I : Matrix n n ℝ) where
  α : ℝ
  Hi : Matrix n n ℝ
  mul_Hi : (A - α • I) * Hi = 1
  Hi_mul : Hi * (A - α • I) = 1
  j : ℕ
  k : ℕ
  r : ℕ
  P : Matrix n (Fin k ⊕ Fin r) ℝ
  Q : Matrix (Fin k ⊕ Fin r) n ℝ
  PQ : P * Q = 1
  QP : Q * P = 1
  N : Matrix (Fin k) (Fin k) ℝ
  N_pow : N ^ j = 0
  G : Matrix (Fin r) (Fin r) ℝ
  Gi : Matrix (Fin r) (Fin r) ℝ
  G_Gi : G * Gi = 1
  Gi_G : Gi * G = 1
  split : Q * Hi * I * P = fromBlocks N 0 0 G

/-- **Woodford (2003), (1.15): a regular pencil has a decomposition.** If `det[A − μÎ]` is not
the zero polynomial, some real `α` has `det(A − αÎ) ≠ 0`, and the Fitting decomposition of
`(A − αÎ)⁻¹Î` (`exists_fitting`) gives `Decomp A I`. -/
theorem nonempty_decomp {A I : Matrix n n ℝ} (h : pen A I ≠ 0) : Nonempty (Decomp A I) := by
  have hfin : {α : ℝ | (α : ℂ) ∈ (pen A I).roots}.Finite :=
    ((pen A I).roots.toFinset.finite_toSet.preimage Complex.ofReal_injective.injOn).subset
      fun α hα => by simpa using hα
  obtain ⟨α, hα⟩ := hfin.infinite_compl.nonempty
  have hdet : (A - α • I).det ≠ 0 := by
    intro h0
    apply hα
    rw [Set.mem_ofPred_eq, Polynomial.mem_roots h, IsRoot.def, pen_eval]
    have e : A.map Complex.ofReal - (α : ℂ) • I.map Complex.ofReal =
        Complex.ofRealHom.mapMatrix (A - α • I) := by
      ext a b
      simp
    rw [e, ← RingHom.map_det, h0, map_zero]
  have hu : IsUnit (A - α • I).det := isUnit_iff_ne_zero.mpr hdet
  obtain ⟨j, k, r, P, Q, N, G, hPQ, hQP, hN, hG, hD⟩ := exists_fitting ((A - α • I)⁻¹ * I)
  refine ⟨⟨α, (A - α • I)⁻¹, Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu, j, k, r,
    P, Q, hPQ, hQP, N, hN, G, G⁻¹, Matrix.mul_nonsing_inv _ hG, Matrix.nonsing_inv_mul _ hG, ?_⟩⟩
  rw [← hD, Matrix.mul_assoc Q]

variable {A I : Matrix n n ℝ} (d : Decomp A I)

/-- Woodford (2003), (1.15): the regular part `G⁻¹ + αI` of the decomposition; its eigenvalues
are the finite roots of the pencil. -/
def Decomp.MR : Matrix (Fin d.r) (Fin d.r) ℝ := d.Gi + d.α • 1

/-- Woodford (2003), App. C.1: the block matrix `diag(2I, G⁻¹ + αI)` (the nilpotent part is given
the unstable eigenvalue `2`). -/
def Decomp.Bm : Matrix (Fin d.k ⊕ Fin d.r) (Fin d.k ⊕ Fin d.r) ℝ :=
  fromBlocks ((2 : ℝ) • (1 : Matrix (Fin d.k) (Fin d.k) ℝ)) 0 0 d.MR

/-- **Woodford (2003), (1.1) and App. C.1: the Blanchard–Kahn matrix of a regular pencil**,
`P diag(2I, G⁻¹ + αI) Q`. -/
def Decomp.bigA : Matrix n n ℝ := d.P * d.Bm * d.Q

/-- Woodford (2003), (1.15) (tool): complexification respects products. -/
theorem map_ofReal_mul {a b c : Type*} [Fintype b] (L : Matrix a b ℝ) (M : Matrix b c ℝ) :
    (L * M).map Complex.ofReal = L.map Complex.ofReal * M.map Complex.ofReal :=
  Matrix.map_mul (f := Complex.ofRealHom)

/-- Woodford (2003), (1.15) (tool): complexification of the identity. -/
theorem map_ofReal_one {a : Type*} [DecidableEq a] :
    (1 : Matrix a a ℝ).map Complex.ofReal = 1 :=
  Matrix.map_one _ (by simp) (by simp)

/-- Woodford (2003), (1.15) (tool): the decomposition's relations over `ℂ`. -/
theorem Decomp.map_rels :
    (A.map Complex.ofReal - (d.α : ℂ) • I.map Complex.ofReal) * d.Hi.map Complex.ofReal = 1 ∧
      d.P.map Complex.ofReal * d.Q.map Complex.ofReal = 1 ∧
      d.Q.map Complex.ofReal * d.P.map Complex.ofReal = 1 ∧
      d.N.map Complex.ofReal ^ d.j = 0 ∧
      d.G.map Complex.ofReal * d.Gi.map Complex.ofReal = 1 ∧
      d.Q.map Complex.ofReal * d.Hi.map Complex.ofReal * I.map Complex.ofReal *
        d.P.map Complex.ofReal =
        fromBlocks (d.N.map Complex.ofReal) 0 0 (d.G.map Complex.ofReal) := by
  have hs : A.map Complex.ofReal - (d.α : ℂ) • I.map Complex.ofReal =
      (A - d.α • I).map Complex.ofReal := by
    ext a b
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs, ← map_ofReal_mul, d.mul_Hi, map_ofReal_one]
  · rw [← map_ofReal_mul, d.PQ, map_ofReal_one]
  · rw [← map_ofReal_mul, d.QP, map_ofReal_one]
  · have e : d.N.map Complex.ofReal ^ d.j = (d.N ^ d.j).map Complex.ofReal :=
      (Complex.ofRealHom.mapMatrix.map_pow d.N d.j).symm
    rw [e, d.N_pow]
    ext a b
    simp
  · rw [← map_ofReal_mul, d.G_Gi, map_ofReal_one]
  · rw [← map_ofReal_mul, ← map_ofReal_mul, ← map_ofReal_mul, d.split]
    ext a b
    rcases a with a | a <;> rcases b with b | b <;> simp

/-- **Woodford (2003), (1.15): the pencil polynomial is a nonzero multiple of the characteristic
polynomial of `G⁻¹ + αI`.** -/
theorem Decomp.pen_eq : ∃ κ : ℂ, κ ≠ 0 ∧
    pen A I = Polynomial.C κ * (d.MR.map Complex.ofReal).charpoly := by
  obtain ⟨h2, hPQ, -, hN, hG, hD⟩ := d.map_rels
  have hH : (A.map Complex.ofReal - (d.α : ℂ) • I.map Complex.ofReal).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h2
    rw [det_mul, h0, zero_mul, det_one] at this
    exact zero_ne_one this
  have hGd : (d.G.map Complex.ofReal).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hG
    rw [det_mul, h0, zero_mul, det_one] at this
    exact zero_ne_one this
  refine ⟨(A.map Complex.ofReal - (d.α : ℂ) • I.map Complex.ofReal).det *
    (d.G.map Complex.ofReal).det * (-1) ^ d.r, mul_ne_zero (mul_ne_zero hH hGd)
      (pow_ne_zero _ (by norm_num)), Polynomial.funext fun μ => ?_⟩
  rw [pen_eval, det_pencil_eq h2 hPQ hN hG hD μ, eval_mul, eval_C, eval_charpoly]
  have e : d.Gi.map Complex.ofReal + (d.α : ℂ) • 1 - μ • 1 =
      -(Matrix.scalar (Fin d.r) μ - d.MR.map Complex.ofReal) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [Decomp.MR]
    · simp [Decomp.MR, hab]
  rw [e, det_neg, Fintype.card_fin]
  ring

/-- Woodford (2003), (1.15) (tool): conjugation by mutually inverse rectangular matrices preserves
the characteristic polynomial. -/
theorem charpoly_conj_rect {P : Matrix n m ℂ} {Q : Matrix m n ℂ} (hPQ : P * Q = 1)
    (hQP : Q * P = 1) (Y : Matrix m m ℂ) : (P * Y * Q).charpoly = Y.charpoly := by
  refine Polynomial.funext fun μ => ?_
  rw [eval_charpoly, eval_charpoly]
  have hn : Matrix.scalar n μ = μ • (1 : Matrix n n ℂ) := by
    rw [smul_one_eq_diagonal]
    rfl
  have hm : Matrix.scalar m μ = μ • (1 : Matrix m m ℂ) := by
    rw [smul_one_eq_diagonal]
    rfl
  have e : Matrix.scalar n μ - P * Y * Q = P * (Matrix.scalar m μ - Y) * Q := by
    rw [hn, hm, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      hPQ]
  rw [e, det_conj_rect hPQ hQP]

/-- **Woodford (2003), (1.15): the eigenvalues of `Decomp.bigA`** (with multiplicity) are the
roots of `det[A − μÎ]` together with `2` repeated `k` times (one for each dimension of the nilpotent
part, the "infinite roots"). -/
theorem Decomp.eigs_bigA : eigs d.bigA = Multiset.replicate d.k 2 + (pen A I).roots := by
  unfold eigs
  have e1 : d.bigA.map Complex.ofReal =
      d.P.map Complex.ofReal * d.Bm.map Complex.ofReal * d.Q.map Complex.ofReal := by
    simp only [Decomp.bigA, map_ofReal_mul]
  obtain ⟨-, hPQ, hQP, -⟩ := d.map_rels
  rw [e1, charpoly_conj_rect hPQ hQP]
  have e2 : d.Bm.map Complex.ofReal =
      fromBlocks ((2 : ℂ) • (1 : Matrix (Fin d.k) (Fin d.k) ℂ)) 0 0 (d.MR.map Complex.ofReal) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · by_cases hab : a = b
      · subst hab
        simp [Decomp.Bm]
      · simp [Decomp.Bm, hab]
    · simp [Decomp.Bm]
    · simp [Decomp.Bm]
    · simp [Decomp.Bm]
  rw [e2, charpoly_fromBlocks_zero₁₂]
  have e3 : ((2 : ℂ) • (1 : Matrix (Fin d.k) (Fin d.k) ℂ)).charpoly = (X - C 2) ^ d.k := by
    rw [smul_one_eq_diagonal, charpoly_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  obtain ⟨κ, hκ, hpen⟩ := d.pen_eq
  have hne : (X - C (2 : ℂ)) ^ d.k * (d.MR.map Complex.ofReal).charpoly ≠ 0 :=
    (((monic_X_sub_C (2 : ℂ)).pow _).mul (charpoly_monic _)).ne_zero
  rw [e3, roots_mul hne, roots_pow, roots_X_sub_C, hpen, roots_C_mul _ hκ,
    Multiset.nsmul_singleton]

/-- Woodford (2003), (1.15) and p. 546: the number of eigenvalues of `Decomp.bigA` in the open
unit disc is the number of roots of `det[A − μÎ]` there, with multiplicity. -/
theorem Decomp.stableCount_bigA :
    stableCount d.bigA = Multiset.card ((pen A I).roots.filter fun μ => ‖μ‖ < 1) := by
  unfold stableCount
  rw [d.eigs_bigA, Multiset.filter_add, Multiset.card_add]
  have h0 : (Multiset.replicate d.k (2 : ℂ)).filter (fun μ => ‖μ‖ < 1) = 0 := by
    refine Multiset.filter_eq_nil.mpr fun μ hμ => ?_
    rw [Multiset.eq_of_mem_replicate hμ]
    norm_num
  rw [h0, Multiset.card_zero, zero_add]

/-- Woodford (2003), (1.15): `Decomp.bigA` has no eigenvalue on the unit circle iff `det[A − μÎ]`
has no root there. -/
theorem Decomp.noUnit_bigA_iff : NoUnit d.bigA ↔ ∀ μ ∈ (pen A I).roots, ‖μ‖ ≠ 1 := by
  unfold NoUnit
  rw [d.eigs_bigA]
  constructor
  · intro h μ hμ
    exact h μ (Multiset.mem_add.mpr (Or.inr hμ))
  · intro h μ hμ
    rcases Multiset.mem_add.mp hμ with h1 | h1
    · rw [Multiset.eq_of_mem_replicate h1]
      norm_num
    · exact h μ h1

/-! ### The algebra of the decomposition -/

/-- Woodford (2003), (1.1) (tool): the block-diagonal matrix `diag(N, G) = Q (A − αÎ)⁻¹ Î P`. -/
def Decomp.D : Matrix (Fin d.k ⊕ Fin d.r) (Fin d.k ⊕ Fin d.r) ℝ := fromBlocks d.N 0 0 d.G

/-- Woodford (2003), (1.1) (tool): `T = ∑_{i<j} (−αN)ⁱ`, the inverse of `I + αN`. -/
def Decomp.T : Matrix (Fin d.k) (Fin d.k) ℝ := ∑ i ∈ Finset.range d.j, (-d.α • d.N) ^ i

/-- Woodford (2003), (1.1) (tool): the nilpotent forward matrix `T N`. -/
def Decomp.Nn : Matrix (Fin d.k) (Fin d.k) ℝ := d.T * d.N

/-- Woodford (2003), (1.1) (tool): `(−αN)ʲ = 0`. -/
theorem Decomp.negN_pow : (-d.α • d.N) ^ d.j = 0 := by
  rw [smul_pow, d.N_pow, smul_zero]

/-- Woodford (2003), (1.1) (tool): `T (I + αN) = I`. -/
theorem Decomp.T_mul : d.T * (1 + d.α • d.N) = 1 := by
  have h := geom_sum_mul_neg (-d.α • d.N) d.j
  have e : (1 : Matrix (Fin d.k) (Fin d.k) ℝ) - -d.α • d.N = 1 + d.α • d.N := by
    rw [neg_smul, sub_neg_eq_add]
  rw [d.negN_pow, sub_zero, e] at h
  exact h

/-- Woodford (2003), (1.1) (tool): `(I + αN) T = I`. -/
theorem Decomp.mul_T : (1 + d.α • d.N) * d.T = 1 := by
  have h := mul_neg_geom_sum (-d.α • d.N) d.j
  have e : (1 : Matrix (Fin d.k) (Fin d.k) ℝ) - -d.α • d.N = 1 + d.α • d.N := by
    rw [neg_smul, sub_neg_eq_add]
  rw [d.negN_pow, sub_zero, e] at h
  exact h

/-- Woodford (2003), (1.1) (tool): `T` commutes with `N`. -/
theorem Decomp.T_comm : d.T * d.N = d.N * d.T := by
  have hc : Commute d.T d.N := by
    refine Commute.sum_left _ _ _ fun i _ => ?_
    exact ((Commute.refl d.N).smul_left (-d.α)).pow_left i
  exact hc.eq

/-- Woodford (2003), (1.1) (tool): `T N` is nilpotent. -/
theorem Decomp.Nn_pow : d.Nn ^ d.j = 0 := by
  have hc : Commute d.T d.N := d.T_comm
  rw [Decomp.Nn, hc.mul_pow, d.N_pow, Matrix.mul_zero]

/-- Woodford (2003), (1.1) (tool): `Q (A − αÎ)⁻¹ A P = I + α diag(N, G)`. -/
theorem Decomp.QHiAP : d.Q * d.Hi * A * d.P = 1 + d.α • d.D := by
  have hD : d.Q * d.Hi * I * d.P = d.D := d.split
  calc d.Q * d.Hi * A * d.P = d.Q * d.Hi * ((A - d.α • I) + d.α • I) * d.P := by
        rw [sub_add_cancel]
    _ = d.Q * (d.Hi * (A - d.α • I)) * d.P + d.α • (d.Q * d.Hi * I * d.P) := by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
        simp only [Matrix.mul_assoc]
    _ = 1 + d.α • d.D := by rw [d.Hi_mul, Matrix.mul_one, d.QP, hD]

/-- Woodford (2003), (1.1) (tool): `(A − αÎ) P diag(N, G) = Î P`. -/
theorem Decomp.HPD : (A - d.α • I) * d.P * d.D = I * d.P := by
  rw [Decomp.D, ← d.split]
  calc (A - d.α • I) * d.P * (d.Q * d.Hi * I * d.P) =
      ((A - d.α • I) * (d.P * d.Q) * d.Hi) * I * d.P := by simp only [Matrix.mul_assoc]
    _ = I * d.P := by rw [d.PQ, Matrix.mul_one, d.mul_Hi, Matrix.one_mul]

/-- Woodford (2003), (1.1) (tool): `(A − αÎ) P (I + α diag(N, G)) = A P`. -/
theorem Decomp.HP_one_add : (A - d.α • I) * d.P * (1 + d.α • d.D) = A * d.P := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, d.HPD, Matrix.sub_mul, Matrix.smul_mul]
  abel

/-- Woodford (2003), (1.1) (tool): `(A − αÎ) P Q (A − αÎ)⁻¹ = I`. -/
theorem Decomp.HPQHi : (A - d.α • I) * d.P * (d.Q * d.Hi) = 1 := by
  rw [← Matrix.mul_assoc, Matrix.mul_assoc _ d.P d.Q, d.PQ, Matrix.mul_one, d.mul_Hi]

/-! ### Tools for vector processes -/

/-- Woodford (2003), App. C.1 (tool): a nilpotent matrix has geometrically decaying powers
(rate `1/2`). -/
theorem nil_decay {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Matrix ι ι ℝ} {j : ℕ}
    (hK : K ^ j = 0) : ∃ Cb, ∀ k i l, |(K ^ k) i l| ≤ Cb * (1 / 2 : ℝ) ^ k := by
  refine ⟨∑ p ∈ Finset.range j, ∑ i, ∑ l, |(K ^ p) i l| * 2 ^ p, fun k i l => ?_⟩
  have hnn : 0 ≤ ∑ p ∈ Finset.range j, ∑ i, ∑ l, |(K ^ p) i l| * (2 : ℝ) ^ p :=
    Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun l _ => by
      positivity
  by_cases hk : k < j
  · have h1 : |(K ^ k) i l| * 2 ^ k ≤ ∑ p ∈ Finset.range j, ∑ i, ∑ l, |(K ^ p) i l| * 2 ^ p := by
      refine le_trans ?_ (Finset.single_le_sum (f := fun p => ∑ i, ∑ l, |(K ^ p) i l| * 2 ^ p)
        (fun p _ => by positivity) (Finset.mem_range.mpr hk))
      refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ l, |(K ^ k) i l| * 2 ^ k)
        (fun _ _ => by positivity) (Finset.mem_univ i))
      exact Finset.single_le_sum (f := fun l => |(K ^ k) i l| * 2 ^ k) (fun _ _ => by positivity)
        (Finset.mem_univ l)
    have h2 : |(K ^ k) i l| = |(K ^ k) i l| * 2 ^ k * (1 / 2) ^ k := by
      rw [mul_assoc, ← mul_pow]
      norm_num
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  · have h0 : K ^ k = 0 := by
      obtain ⟨q, rfl⟩ : ∃ q, k = j + q := ⟨k - j, by omega⟩
      rw [pow_add, hK, Matrix.zero_mul]
    rw [h0, Matrix.zero_apply, abs_zero]
    positivity

/-- Woodford (2003), App. C.1 (tool): the powers of `½I` decay at rate `1/2`. -/
theorem half_decay {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∀ k (i l : ι), |(((1 / 2 : ℝ) • (1 : Matrix ι ι ℝ)) ^ k) i l| ≤ 1 * (1 / 2 : ℝ) ^ k := by
  intro k i l
  rw [smul_pow, one_pow, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, abs_mul, one_mul]
  split_ifs
  · rw [abs_one, mul_one, abs_of_nonneg (by positivity)]
  · simp

/-- Woodford (2003), App. C.1 (tool): a scalar multiple of a matrix acting on a vector process. -/
theorem mv_smul_mat {Ω ι κ : Type*} [Fintype κ] (c : ℝ) (M : Matrix ι κ ℝ) (a : κ → Ω → ℝ) :
    mv (c • M) a = c • mv M a := by
  funext i ω
  simp only [mv, Matrix.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- Woodford (2003), App. C.1 (tool): a matrix acting on a scalar multiple of a vector
process. -/
theorem mv_smul_vec {Ω ι κ : Type*} [Fintype κ] (c : ℝ) (M : Matrix ι κ ℝ) (a : κ → Ω → ℝ) :
    mv M (c • a) = c • mv M a := by
  funext i ω
  simp only [mv, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- Woodford (2003), App. C.1 (tool): a matrix acting on a negated vector process. -/
theorem mv_neg_vec {Ω ι κ : Type*} [Fintype κ] (M : Matrix ι κ ℝ) (a : κ → Ω → ℝ) :
    mv M (-a) = -mv M a := by
  funext i ω
  simp [mv, Finset.sum_apply]

/-- Woodford (2003), App. C.1 (tool): the zero matrix acting on a vector process. -/
theorem mv_zero_mat {Ω ι κ : Type*} [Fintype κ] (a : κ → Ω → ℝ) :
    mv (0 : Matrix ι κ ℝ) a = 0 := by
  funext i ω
  simp [mv]

/-- Woodford (2003), App. C.1 (tool): two vector processes on a sum type agree iff both blocks
do. -/
theorem sum_funext_iff {α β γ : Type*} (f g : α ⊕ β → γ) :
    f = g ↔ (fun a => f (Sum.inl a)) = (fun a => g (Sum.inl a)) ∧
      (fun b => f (Sum.inr b)) = (fun b => g (Sum.inr b)) := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    funext c
    rcases c with a | b
    · exact congrFun h1 a
    · exact congrFun h2 b

/-- Woodford (2003), App. C.1 (tool): the rows of a block-diagonal matrix acting on a vector
process. -/
theorem mv_fromBlocks_diag {Ω k r : Type*} [Fintype k] [Fintype r] (N : Matrix k k ℝ)
    (G : Matrix r r ℝ) (x : k ⊕ r → Ω → ℝ) :
    mv (fromBlocks N 0 0 G) x = fun c => Sum.elim (fun a => mv N (fun a' => x (Sum.inl a')) a)
      (fun b => mv G (fun b' => x (Sum.inr b')) b) c := by
  funext c ω
  rcases c with a | b
  · simp [mv, Fintype.sum_sum_type, Finset.sum_apply]
  · simp [mv, Fintype.sum_sum_type, Finset.sum_apply]

/-! ### The descriptor system and its Blanchard–Kahn form -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), (1.1), p. 537: `y` solves the descriptor system `Î E_t y_{t+1} = A y_t + h_t`
at every date. -/
def DSolves (A I : Matrix n n ℝ) (h y : ℕ → n → Ω → ℝ) : Prop :=
  ∀ t, mv I (fun j => 𝔼.E t (y (t + 1) j)) = mv A (y t) + h t

/-- Woodford (2003), (1.1) (tool): the forcing in the coordinates of the decomposition,
`Q (A − αÎ)⁻¹ h_t`. -/
def Decomp.gF (h : ℕ → n → Ω → ℝ) : ℕ → Fin d.k ⊕ Fin d.r → Ω → ℝ :=
  fun t => mv (d.Q * d.Hi) (h t)

/-- Woodford (2003), (1.1) and App. C.1: the unique bounded solution of the nilpotent block,
`v_t = T N E_t v_{t+1} − T g_t` (it is pinned down by the forcing alone). -/
noncomputable def Decomp.vstar (h : ℕ → n → Ω → ℝ) : ℕ → Fin d.k → Ω → ℝ := by
  classical
  exact if hx : ∃ s, FSolves 𝔼 d.Nn (fun t => -mv d.T (fun a => d.gF h t (Sum.inl a))) s ∧
    AdaptedV 𝔼 s ∧ BoundedV s then hx.choose else 0

/-- Woodford (2003), App. C.1: the Blanchard–Kahn forcing in the coordinates of the
decomposition: `E_tv*_{t+1} − 2v*_t` on the nilpotent block, `G⁻¹g_t` on the regular block. -/
noncomputable def Decomp.wF (h : ℕ → n → Ω → ℝ) : ℕ → Fin d.k ⊕ Fin d.r → Ω → ℝ := fun t c =>
  Sum.elim (fun a => 𝔼.E t (d.vstar 𝔼 h (t + 1) a) - (2 : ℝ) • d.vstar 𝔼 h t a)
    (fun b => mv d.Gi (fun b' => d.gF h t (Sum.inr b')) b) c

/-- **Woodford (2003), App. C.1: the Blanchard–Kahn forcing of the descriptor system**,
`P wF_t`. -/
noncomputable def Decomp.wBig (h : ℕ → n → Ω → ℝ) : ℕ → n → Ω → ℝ := fun t => mv d.P (d.wF 𝔼 h t)

variable {𝔼}

/-- Woodford (2003), App. C.1: for bounded adapted forcing, `Decomp.vstar` is a bounded adapted
solution of the nilpotent block. -/
theorem Decomp.vstar_spec {h : ℕ → n → Ω → ℝ} (hb : BoundedV h) (ha : AdaptedV 𝔼 h) :
    FSolves 𝔼 d.Nn (fun t => -mv d.T (fun a => d.gF h t (Sum.inl a))) (d.vstar 𝔼 h) ∧
      AdaptedV 𝔼 (d.vstar 𝔼 h) ∧ BoundedV (d.vstar 𝔼 h) := by
  classical
  have hgb : BoundedV (d.gF h) := boundedV_mv _ hb
  have hga : AdaptedV 𝔼 (d.gF h) := adaptedV_mv 𝔼 _ ha
  have hKb : BoundedV (fun t (a : Fin d.k) => d.gF h t (Sum.inl a)) := by
    obtain ⟨M, hM⟩ := hgb
    exact ⟨M, fun t a ω => hM t _ ω⟩
  have hKa : AdaptedV 𝔼 (fun t (a : Fin d.k) => d.gF h t (Sum.inl a)) := fun t a => hga t _
  have hwb := GeneralBKCopy.boundedV_neg (boundedV_mv d.T hKb)
  have hwa := GeneralBKCopy.adaptedV_neg 𝔼 (adaptedV_mv 𝔼 d.T hKa)
  obtain ⟨Cb, hCb⟩ := nil_decay d.Nn_pow
  obtain ⟨Mw, hMw⟩ := hwb
  have hex := fsolves_exists 𝔼 (K := d.Nn) (by norm_num) (by norm_num) hCb hMw hwa
  unfold Decomp.vstar
  simp only [hex, ↓reduceDIte]
  exact hex.choose_spec

/-- Woodford (2003), App. C.1 (tool): `P Q x = x`. -/
theorem Decomp.mv_PQ (x : n → Ω → ℝ) : mv d.P (mv d.Q x) = x := by rw [mv_mv, d.PQ, mv_one]

/-- Woodford (2003), App. C.1 (tool): `Q P x = x`. -/
theorem Decomp.mv_QP (x : Fin d.k ⊕ Fin d.r → Ω → ℝ) : mv d.Q (mv d.P x) = x := by
  rw [mv_mv, d.QP, mv_one]

/-- Woodford (2003), (1.1) (tool): `diag(N, G) Q = Q (A − αÎ)⁻¹ Î`. -/
theorem Decomp.DQ : d.D * d.Q = d.Q * d.Hi * I := by
  rw [Decomp.D, ← d.split, Matrix.mul_assoc _ d.P, d.PQ, Matrix.mul_one]

/-- Woodford (2003), (1.1) (tool): `(I + α diag(N, G)) Q = Q (A − αÎ)⁻¹ A`. -/
theorem Decomp.oneDQ : (1 + d.α • d.D) * d.Q = d.Q * d.Hi * A := by
  rw [← d.QHiAP, Matrix.mul_assoc _ d.P, d.PQ, Matrix.mul_one]

/-- Woodford (2003), (1.1) (tool): `(A − αÎ) P diag(N, G) Q = Î`. -/
theorem Decomp.HPDQ : (A - d.α • I) * d.P * d.D * d.Q = I := by
  rw [d.HPD, Matrix.mul_assoc, d.PQ, Matrix.mul_one]

/-- Woodford (2003), (1.1) (tool): `(A − αÎ) P (I + α diag(N, G)) Q = A`. -/
theorem Decomp.HPoneDQ : (A - d.α • I) * d.P * (1 + d.α • d.D) * d.Q = A := by
  rw [d.HP_one_add, Matrix.mul_assoc, d.PQ, Matrix.mul_one]

/-- Woodford (2003), (1.1) (tool): `I + α diag(N, G) = diag(I + αN, I + αG)`. -/
theorem Decomp.one_add_D :
    1 + d.α • d.D = fromBlocks (1 + d.α • d.N) 0 0 (1 + d.α • d.G) := by
  rw [Decomp.D, ← fromBlocks_one, fromBlocks_smul]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply]

/-- **Woodford (2003), (1.1): the descriptor system in the coordinates of the decomposition**,
`diag(N, G) E_tY_{t+1} = (I + α diag(N, G)) Y_t + Q(A − αÎ)⁻¹h_t` with `Y_t = Q y_t`. -/
theorem Decomp.dsolves_iff_coord {h y : ℕ → n → Ω → ℝ} :
    DSolves 𝔼 A I h y ↔ ∀ t, mv d.D (fun c => 𝔼.E t (mv d.Q (y (t + 1)) c)) =
      mv (1 + d.α • d.D) (mv d.Q (y t)) + d.gF h t := by
  have hE : ∀ t, (fun c => 𝔼.E t (mv d.Q (y (t + 1)) c)) =
      mv d.Q (fun j => 𝔼.E t (y (t + 1) j)) :=
    fun t => funext fun c => E_mv 𝔼 t d.Q (y (t + 1)) c
  constructor
  · intro hD t
    have e := congrArg (mv (d.Q * d.Hi)) (hD t)
    rw [mv_mv, mv_add, mv_mv] at e
    rw [hE, mv_mv, mv_mv, d.DQ, d.oneDQ, Decomp.gF]
    exact e
  · intro hc t
    have e := congrArg (mv ((A - d.α • I) * d.P)) (hc t)
    rw [hE, mv_add, Decomp.gF] at e
    simp only [mv_mv] at e
    rw [← Matrix.mul_assoc _ d.D, ← Matrix.mul_assoc _ (1 + d.α • d.D), d.HPDQ, d.HPoneDQ,
      d.HPQHi, mv_one] at e
    exact e

/-- **Woodford (2003), App. C.1: the Blanchard–Kahn system of `Decomp.bigA` in the coordinates of
the decomposition**, `E_tY_{t+1} = diag(2I, G⁻¹ + αI) Y_t + wF_t`. -/
theorem Decomp.solves_iff_coord {h y : ℕ → n → Ω → ℝ} :
    GeneralBKCopy.Solves 𝔼 d.bigA (d.wBig 𝔼 h) y ↔ ∀ t,
      (fun c => 𝔼.E t (mv d.Q (y (t + 1)) c)) = mv d.Bm (mv d.Q (y t)) + d.wF 𝔼 h t := by
  have hE : ∀ t, (fun c => 𝔼.E t (mv d.Q (y (t + 1)) c)) =
      mv d.Q (fun j => 𝔼.E t (y (t + 1) j)) :=
    fun t => funext fun c => E_mv 𝔼 t d.Q (y (t + 1)) c
  have hBQ : d.Q * d.bigA = d.Bm * d.Q := by
    rw [Decomp.bigA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.QP, Matrix.one_mul]
  constructor
  · intro hs t
    have e0 : (fun j => 𝔼.E t (y (t + 1) j)) = mv d.bigA (y t) + d.wBig 𝔼 h t :=
      funext fun j => hs t j
    have e := congrArg (mv d.Q) e0
    rw [mv_add, mv_mv, hBQ, Decomp.wBig, d.mv_QP, ← mv_mv] at e
    rw [hE]
    exact e
  · intro hc t i
    have e := congrArg (mv d.P) (hc t)
    rw [hE, d.mv_PQ, mv_add, mv_mv, mv_mv] at e
    exact congrFun e i

/-- **Woodford (2003), (1.1) and App. C.1: a bounded adapted process solves the descriptor system
`Î E_t y_{t+1} = A y_t + h_t` iff it solves the Blanchard–Kahn system
`E_t y_{t+1} = bigA y_t + wBig_t`** (bounded adapted forcing). On the regular block the two are
the same equation; on the nilpotent block both have exactly one bounded solution, `Decomp.vstar`. -/
theorem Decomp.dsolves_iff_solves {h y : ℕ → n → Ω → ℝ} (hb : BoundedV h) (ha : AdaptedV 𝔼 h)
    (hyb : BoundedV y) (hya : AdaptedV 𝔼 y) :
    DSolves 𝔼 A I h y ↔ GeneralBKCopy.Solves 𝔼 d.bigA (d.wBig 𝔼 h) y := by
  rw [d.dsolves_iff_coord, d.solves_iff_coord]
  set Y : ℕ → Fin d.k ⊕ Fin d.r → Ω → ℝ := fun t => mv d.Q (y t) with hY
  have hYb : BoundedV Y := boundedV_mv _ hyb
  have hYa : AdaptedV 𝔼 Y := adaptedV_mv 𝔼 _ hya
  set V : ℕ → Fin d.k → Ω → ℝ := fun t a => Y t (Sum.inl a) with hV
  set U : ℕ → Fin d.r → Ω → ℝ := fun t b => Y t (Sum.inr b) with hU
  have hVb : BoundedV V := by
    obtain ⟨M, hM⟩ := hYb
    exact ⟨M, fun t a ω => hM t _ ω⟩
  have hVa : AdaptedV 𝔼 V := fun t a => hYa t _
  set gK : ℕ → Fin d.k → Ω → ℝ := fun t a => d.gF h t (Sum.inl a) with hgK
  set gR : ℕ → Fin d.r → Ω → ℝ := fun t b => d.gF h t (Sum.inr b) with hgR
  set vs := d.vstar 𝔼 h with hvs
  obtain ⟨hvF, hva, hvb⟩ := d.vstar_spec hb ha
  obtain ⟨Cb, hCb⟩ := nil_decay d.Nn_pow
  -- the block forms
  have hDblk : ∀ t, (mv d.D (fun c => 𝔼.E t (Y (t + 1) c)) =
      mv (1 + d.α • d.D) (Y t) + d.gF h t) ↔
      (mv d.N (fun a => 𝔼.E t (V (t + 1) a)) = V t + d.α • mv d.N (V t) + gK t) ∧
      (mv d.G (fun b => 𝔼.E t (U (t + 1) b)) = U t + d.α • mv d.G (U t) + gR t) := by
    intro t
    rw [d.one_add_D, Decomp.D, mv_fromBlocks_diag, mv_fromBlocks_diag, sum_funext_iff]
    simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_inr, add_mv, mv_one, mv_smul_mat]
    rfl
  have hBblk : ∀ t, ((fun c => 𝔼.E t (Y (t + 1) c)) = mv d.Bm (Y t) + d.wF 𝔼 h t) ↔
      ((fun a => 𝔼.E t (V (t + 1) a)) =
        (2 : ℝ) • V t + (fun a => 𝔼.E t (vs (t + 1) a) - (2 : ℝ) • vs t a)) ∧
      ((fun b => 𝔼.E t (U (t + 1) b)) = mv d.MR (U t) + mv d.Gi (gR t)) := by
    intro t
    rw [Decomp.Bm, mv_fromBlocks_diag, sum_funext_iff]
    simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_inr, Decomp.wF, mv_smul_mat, mv_one]
    rfl
  -- the regular block
  have hUeq : ∀ t, (mv d.G (fun b => 𝔼.E t (U (t + 1) b)) = U t + d.α • mv d.G (U t) + gR t) ↔
      ((fun b => 𝔼.E t (U (t + 1) b)) = mv d.MR (U t) + mv d.Gi (gR t)) := by
    intro t
    constructor
    · intro e
      have e2 := congrArg (mv d.Gi) e
      rw [mv_mv, d.Gi_G, mv_one, mv_add, mv_add, mv_smul_vec, mv_mv, d.Gi_G, mv_one] at e2
      rw [e2, Decomp.MR, add_mv, mv_smul_mat, mv_one]
    · intro e
      have e2 := congrArg (mv d.G) e
      rw [mv_add, mv_mv, mv_mv, d.G_Gi, mv_one, Decomp.MR, Matrix.mul_add, d.G_Gi,
        Matrix.mul_smul, Matrix.mul_one, add_mv, mv_one, mv_smul_mat] at e2
      exact e2
  -- the nilpotent block: both forms say `V = vstar`
  have hTm : d.T + d.α • (d.T * d.N) = 1 := by
    have := d.T_mul
    rwa [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul] at this
  have hmT : (1 + d.α • d.N) * d.T = 1 := d.mul_T
  have hiff1 : (∀ t, mv d.N (fun a => 𝔼.E t (V (t + 1) a)) = V t + d.α • mv d.N (V t) + gK t) ↔
      FSolves 𝔼 d.Nn (fun t => -mv d.T (gK t)) V := by
    constructor
    · intro e t
      have e2 := congrArg (mv d.T) (e t)
      rw [mv_mv, mv_add, mv_add, mv_smul_vec, mv_mv] at e2
      have hTV : mv d.T (V t) + d.α • mv (d.T * d.N) (V t) = V t := by
        rw [← mv_smul_mat, ← add_mv, hTm, mv_one]
      rw [hTV] at e2
      change V t = mv (d.T * d.N) (fun j => 𝔼.E t (V (t + 1) j)) + -mv d.T (gK t)
      rw [e2]
      abel
    · intro hF t
      have e := hF t
      have e2 := congrArg (mv (1 + d.α • d.N)) e
      rw [mv_add, mv_neg_vec, mv_mv, mv_mv, Decomp.Nn, ← Matrix.mul_assoc, hmT, Matrix.one_mul,
        mv_one, add_mv, mv_one, mv_smul_mat] at e2
      rw [← sub_eq_zero] at e2 ⊢
      rw [← neg_eq_zero, ← e2]
      abel
  have hiff2 : (∀ t, (fun a => 𝔼.E t (V (t + 1) a)) =
      (2 : ℝ) • V t + (fun a => 𝔼.E t (vs (t + 1) a) - (2 : ℝ) • vs t a)) ↔
      FSolves 𝔼 ((1 / 2 : ℝ) • (1 : Matrix (Fin d.k) (Fin d.k) ℝ))
        (fun t => -(1 / 2 : ℝ) • (fun a => 𝔼.E t (vs (t + 1) a) - (2 : ℝ) • vs t a)) V := by
    constructor
    · intro e t
      rw [mv_smul_mat, mv_one, e t]
      funext a ω
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, neg_mul]
      ring
    · intro hF t
      have e := hF t
      rw [mv_smul_mat, mv_one] at e
      funext a ω
      have := congrFun (congrFun e a) ω
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, neg_mul] at this ⊢
      linarith
  have hvs2 : FSolves 𝔼 ((1 / 2 : ℝ) • (1 : Matrix (Fin d.k) (Fin d.k) ℝ))
      (fun t => -(1 / 2 : ℝ) • (fun a => 𝔼.E t (vs (t + 1) a) - (2 : ℝ) • vs t a)) vs := by
    intro t
    rw [mv_smul_mat, mv_one]
    funext a ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, neg_mul]
    ring
  have hVeq1 : (∀ t, mv d.N (fun a => 𝔼.E t (V (t + 1) a)) = V t + d.α • mv d.N (V t) + gK t) ↔
      V = vs := by
    rw [hiff1]
    constructor
    · intro hF
      exact fsolves_unique 𝔼 (by norm_num) (by norm_num) hCb hF hvF hVa hva hVb hvb
    · intro hEq
      rw [hEq]
      exact hvF
  have hVeq2 : (∀ t, (fun a => 𝔼.E t (V (t + 1) a)) =
      (2 : ℝ) • V t + (fun a => 𝔼.E t (vs (t + 1) a) - (2 : ℝ) • vs t a)) ↔ V = vs := by
    rw [hiff2]
    constructor
    · intro hF
      exact fsolves_unique 𝔼 (by norm_num) (by norm_num) half_decay hF hvs2 hVa hva hVb hvb
    · intro hEq
      rw [hEq]
      exact hvs2
  constructor
  · intro hD t
    obtain ⟨-, h2⟩ := (hDblk t).mp (hD t)
    refine (hBblk t).mpr ⟨?_, (hUeq t).mp h2⟩
    have hv : V = vs := hVeq1.mp fun s => ((hDblk s).mp (hD s)).1
    exact hVeq2.mpr hv t
  · intro hB t
    obtain ⟨-, h2⟩ := (hBblk t).mp (hB t)
    refine (hDblk t).mpr ⟨?_, (hUeq t).mpr h2⟩
    have hv : V = vs := hVeq2.mp fun s => ((hBblk s).mp (hB s)).1
    exact hVeq1.mpr hv t

/-- Woodford (2003), App. C.1 (tool): with zero forcing the Blanchard–Kahn forcing vanishes. -/
theorem Decomp.wBig_zero (𝔼 : ExpectationSystem Ω) : d.wBig 𝔼 (0 : ℕ → n → Ω → ℝ) = 0 := by
  have hb : BKForward.BoundedV (0 : ℕ → n → Ω → ℝ) := ⟨0, fun _ _ _ => by simp⟩
  have ha : BKForward.AdaptedV 𝔼 (0 : ℕ → n → Ω → ℝ) := fun t i => by
    change 𝔼.E t 0 = 0
    exact map_zero _
  obtain ⟨hvF, hva, hvb⟩ := d.vstar_spec hb ha
  obtain ⟨Cb, hCb⟩ := nil_decay d.Nn_pow
  have hg : d.gF (0 : ℕ → n → Ω → ℝ) = 0 := by
    funext t c ω
    simp [Decomp.gF, mv]
  have hz : FSolves 𝔼 d.Nn (fun t => -mv d.T (fun a => d.gF (0 : ℕ → n → Ω → ℝ) t (Sum.inl a)))
      0 := by
    intro t
    rw [hg]
    funext a ω
    simp [mv]
  have hza : BKForward.AdaptedV 𝔼 (0 : ℕ → Fin d.k → Ω → ℝ) := fun t i => by
    change 𝔼.E t 0 = 0
    exact map_zero _
  have hv0 : d.vstar 𝔼 0 = 0 :=
    fsolves_unique 𝔼 (by norm_num) (by norm_num) hCb hvF hz hva hza hvb
      ⟨0, fun _ _ _ => by simp⟩
  funext t k ω
  have hE0 : 𝔼.E t (0 : Ω → ℝ) = 0 := map_zero _
  have hw : ∀ c, d.wF 𝔼 (0 : ℕ → n → Ω → ℝ) t c ω = 0 := by
    intro c
    rcases c with a | b
    · simp [Decomp.wF, hv0, hE0]
    · simp [Decomp.wF, hg, mv]
  simp [Decomp.wBig, mv, hw]

/-! ### The zero root of the pencil -/

/-- **Woodford (2003), p. 547 (the zero-root convention), any `Î`: `μ^{n − rank A}` divides
`det[A − μÎ]`.** Each of the `n − rank A` kernel directions of `A` contributes a factor `μ` (the
column `(A − μÎ)v = −μÎv`). -/
theorem X_pow_dvd_det (A I : Matrix n n ℝ) :
    (X : ℝ[X]) ^ (Fintype.card n - A.rank) ∣
      (A.map Polynomial.C - (X : ℝ[X]) • I.map Polynomial.C).det := by
  classical
  set K := LinearMap.ker A.mulVecLin with hK
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl K
  set bK := Module.finBasis ℝ K with hbK
  set bW := Module.finBasis ℝ W with hbW
  set b := (bK.prod bW).map (Submodule.prodEquivOfIsCompl K W hW) with hb
  have hk : Module.finrank ℝ K = Fintype.card n - A.rank := by
    have h1 : Module.finrank ℝ (LinearMap.range A.mulVecLin) + Module.finrank ℝ K =
        Fintype.card n := by
      rw [hK, LinearMap.finrank_range_add_finrank_ker, Module.finrank_fintype_fun_eq_card]
    have h2 : Module.finrank ℝ (LinearMap.range A.mulVecLin) = A.rank := rfl
    omega
  have hcard : Fintype.card (Fin (Module.finrank ℝ K) ⊕ Fin (Module.finrank ℝ W)) =
      Fintype.card n := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card]
  set e := Fintype.equivOfCardEq hcard with he
  set b' := b.reindex e with hb'
  set B := (Pi.basisFun ℝ n).toMatrix b' with hB
  have hBdet : B.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det (Module.Basis.toMatrix_mul_toMatrix_flip (Pi.basisFun ℝ n) b')
    rw [det_mul, ← hB, h0, zero_mul, det_one] at this
    exact zero_ne_one this
  have hBcol : ∀ c, (fun l => B l c) = b' c := by
    intro c
    funext l
    simp [hB, Module.Basis.toMatrix_apply]
  have hker : ∀ a, A *ᵥ b' (e (Sum.inl a)) = 0 := by
    intro a
    have hmem : b' (e (Sum.inl a)) ∈ K := by
      simp [hb', hb]
    exact LinearMap.mem_ker.mp hmem
  set Pm : Matrix n n ℝ[X] := A.map Polynomial.C - (X : ℝ[X]) • I.map Polynomial.C with hPm
  set Mx := Pm * B.map Polynomial.C with hMx
  have hMx_entry : ∀ r c, Mx r c = Polynomial.C ((A *ᵥ b' c) r) -
      X * Polynomial.C ((I *ᵥ b' c) r) := by
    intro r c
    simp only [hMx, hPm, Matrix.mul_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply,
      smul_eq_mul, mulVec, dotProduct, ← hBcol c, map_sum, map_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib, sub_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  set d : n → ℝ[X] := fun c => Sum.elim (fun _ => X) (fun _ => 1) (e.symm c) with hd
  set M' : Matrix n n ℝ[X] := Matrix.of fun r c =>
    Sum.elim (fun _ => -Polynomial.C ((I *ᵥ b' c) r)) (fun _ => Mx r c) (e.symm c) with hM'
  have hfac : Mx = M' * diagonal d := by
    ext r c
    rw [mul_diagonal]
    simp only [hM', hd, Matrix.of_apply]
    rcases hs : e.symm c with a | w
    · have hc : c = e (Sum.inl a) := by rw [← hs, Equiv.apply_symm_apply]
      simp only [Sum.elim_inl]
      rw [hMx_entry, hc, hker a]
      simp only [Pi.zero_apply, map_zero, zero_sub]
      ring_nf
    · simp
  have hprod : ∏ c, d c = X ^ (Fintype.card n - A.rank) := by
    rw [← hk, ← Equiv.prod_comp e]
    simp [hd, Fintype.prod_sum_type]
  have hmain : Pm.det * Polynomial.C B.det = M'.det * X ^ (Fintype.card n - A.rank) := by
    have e1 : (B.map Polynomial.C).det = Polynomial.C B.det := by
      rw [show B.map Polynomial.C = Polynomial.C.mapMatrix B from rfl, ← RingHom.map_det]
    rw [← e1, ← det_mul, ← hMx, hfac, det_mul, det_diagonal, hprod]
  have hu : IsUnit (Polynomial.C B.det) := Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hBdet)
  have hdvd : X ^ (Fintype.card n - A.rank) ∣ Pm.det * Polynomial.C B.det :=
    ⟨M'.det, by rw [hmain, mul_comm]⟩
  exact (hu.dvd_mul_right).mp hdvd

/-! ### (1.1) with an exogenous instrument, any `Ẽ` -/

namespace Sys

open GeneralSetup
open TidyR5aExogenousInstrument.Exo (ExoSol ExoDeterminate toBK ofBK)

variable {ιZ ιz : Type*} [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz]
variable (S : LinearRESystem ιZ ιz)

/-- Woodford (2003), (1.1), p. 537: the matrix `A` of (1.1) in the Blanchard–Kahn ordering
`(z, Z)`. -/
def bkA : Matrix (ιz ⊕ ιZ) (ιz ⊕ ιZ) ℝ := fromBlocks S.A22 S.A21 S.A12 S.A11

/-- Woodford (2003), (1.1), p. 537: the matrix `Î = diag(I, Ẽ)` of (1.1) in the Blanchard–Kahn
ordering `(z, Z)`. -/
def bkI : Matrix (ιz ⊕ ιZ) (ιz ⊕ ιZ) ℝ := fromBlocks S.Et 0 0 1

/-- Woodford (2003), (1.15): reordering the variables does not change `det[A − μÎ]`. -/
theorem pen_bk : pen (bkA S) (bkI S) = S.pencilPoly := by
  refine Polynomial.funext fun μ => ?_
  rw [pen_eval, PencilSplit.pencilPoly_eval]
  have e : (bkA S).map Complex.ofReal - μ • (bkI S).map Complex.ofReal =
      (S.Ahat.map Complex.ofReal - μ • S.Ihat.map Complex.ofReal).submatrix
        (Equiv.sumComm ιz ιZ) (Equiv.sumComm ιz ιZ) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [bkA, bkI, LinearRESystem.Ahat, LinearRESystem.Ihat]
  rw [e, det_submatrix_equiv_self]

/-- Woodford (2003), (1.1): the forcing `(B₂ie_t + c_t, 0)` of (1.1) with the exogenous
instrument path ie, dates from `t₀`. -/
def hExo {Ω : Type*} (c : ℕ → Ω → ιz → ℝ) (ie : ℕ → Ω → ℝ) (t0 : ℕ) :
    ℕ → ιz ⊕ ιZ → Ω → ℝ :=
  fun s k ω => Sum.elim (fun i => (ie (s + t0) ω • S.B2 + c (s + t0) ω) i) (fun _ => 0) k

variable {S}

omit [Fintype ιZ] [DecidableEq ιZ] in
/-- Woodford (2003), (1.1) (tool): the forcing is bounded for a bounded disturbance and a bounded
instrument path. -/
theorem hExo_bounded {Ω : Type*} {c : ℕ → Ω → ιz → ℝ} {ie : ℕ → Ω → ℝ} (t0 : ℕ)
    (hcb : GeneralSetup.BoundedV c) (hib : ∃ K, ∀ t ω, |ie t ω| ≤ K) :
    BKForward.BoundedV (hExo S c ie t0) := by
  obtain ⟨Mc, hMc⟩ := hcb
  obtain ⟨Ki, hKi⟩ := hib
  refine ⟨max (Ki * ∑ i, |S.B2 i| + Mc) 0, fun s k ω => ?_⟩
  rcases k with i | j
  · refine le_trans ?_ (le_max_left _ _)
    simp only [hExo, Sum.elim_inl, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : |S.B2 i| ≤ ∑ i, |S.B2 i| :=
      Finset.single_le_sum (f := fun i => |S.B2 i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : |ie (s + t0) ω| * |S.B2 i| ≤ Ki * ∑ i, |S.B2 i| :=
      mul_le_mul (hKi (s + t0) ω) h1 (abs_nonneg _) ((abs_nonneg _).trans (hKi (s + t0) ω))
    calc |ie (s + t0) ω * S.B2 i + c (s + t0) ω i|
        ≤ |ie (s + t0) ω * S.B2 i| + |c (s + t0) ω i| := abs_add_le _ _
      _ ≤ Ki * ∑ i, |S.B2 i| + Mc := by rw [abs_mul]; linarith [hMc (s + t0) ω i]
  · simp [hExo]

omit [Fintype ιZ] [DecidableEq ιZ] in
/-- Woodford (2003), (1.1) (tool): the forcing is adapted (dates from `t₀`) for an adapted
disturbance and instrument path. -/
theorem hExo_adapted {Ω : Type*} {𝔼 : ExpectationSystem Ω} {c : ℕ → Ω → ιz → ℝ}
    {ie : ℕ → Ω → ℝ} (t0 : ℕ) (hca : GeneralSetup.AdaptedV 𝔼 c) (hia : 𝔼.Adapted ie) :
    BKForward.AdaptedV (Prop84General.shiftES 𝔼 t0) (hExo S c ie t0) := by
  intro s k
  change 𝔼.E (s + t0) _ = _
  rcases k with i | j
  · have e : (hExo S c ie t0 s (Sum.inl i)) =
        (S.B2 i) • ie (s + t0) + fun ω => c (s + t0) ω i := by
      funext ω
      simp [hExo, mul_comm]
    rw [e, map_add, map_smul, hia (s + t0), hca (s + t0) i]
  · exact 𝔼.const _ 0

omit [Fintype ιZ] [DecidableEq ιZ] in
/-- Woodford (2003), (1.1) (tool): with no disturbance and a zero instrument the forcing
vanishes. -/
theorem hExo_zero {Ω : Type*} (t0 : ℕ) :
    hExo S (fun _ _ _ => 0) (fun (_ : ℕ) (_ : Ω) => 0) t0 = 0 := by
  funext s k ω
  rcases k with i | j <;> simp [hExo]

/-- **Woodford (2003), (1.1): the descriptor system `Î E_t y_{t+1} = A y_t + h_t`, by rows.** -/
theorem dsolves_bk_iff {Ω : Type*} (𝔼 : ExpectationSystem Ω) (h Y : ℕ → ιz ⊕ ιZ → Ω → ℝ) :
    DSolves 𝔼 (bkA S) (bkI S) h Y ↔ ∀ t ω,
      S.Et *ᵥ (fun i => 𝔼.E t (Y (t + 1) (Sum.inl i)) ω) =
        S.A22 *ᵥ (fun i => Y t (Sum.inl i) ω) + S.A21 *ᵥ (fun j => Y t (Sum.inr j) ω) +
          (fun i => h t (Sum.inl i) ω) ∧
      (fun j => 𝔼.E t (Y (t + 1) (Sum.inr j)) ω) =
        S.A12 *ᵥ (fun i => Y t (Sum.inl i) ω) + S.A11 *ᵥ (fun j => Y t (Sum.inr j) ω) +
          (fun j => h t (Sum.inr j) ω) := by
  have key : ∀ t ω k, (mv (bkI S) (fun j => 𝔼.E t (Y (t + 1) j)) k ω =
      (mv (bkA S) (Y t) + h t) k ω) ↔
      ((bkI S) *ᵥ (fun j => 𝔼.E t (Y (t + 1) j) ω)) k =
        ((bkA S) *ᵥ (fun j => Y t j ω)) k + h t k ω := by
    intro t ω k
    rw [Pi.add_apply, Pi.add_apply, mv_apply, mv_apply]
  constructor
  · intro hD t ω
    have e : ∀ k, ((bkI S) *ᵥ (fun j => 𝔼.E t (Y (t + 1) j) ω)) k =
        ((bkA S) *ᵥ (fun j => Y t j ω)) k + h t k ω :=
      fun k => (key t ω k).mp (congrFun (congrFun (hD t) k) ω)
    refine ⟨funext fun i => ?_, funext fun j => ?_⟩
    · have := e (Sum.inl i)
      simp only [bkI, bkA, fromBlocks_mulVec, Sum.elim_inl, Pi.add_apply, zero_mulVec,
        add_zero] at this
      exact this
    · have := e (Sum.inr j)
      simp only [bkI, bkA, fromBlocks_mulVec, Sum.elim_inr, Pi.add_apply, zero_mulVec,
        one_mulVec, zero_add] at this
      exact this
  · intro hr t
    funext k ω
    refine (key t ω k).mpr ?_
    obtain ⟨h1, h2⟩ := hr t ω
    rcases k with i | j
    · have := congrFun h1 i
      simp only [bkI, bkA, fromBlocks_mulVec, Sum.elim_inl, Pi.add_apply, zero_mulVec,
        add_zero]
      exact this
    · have := congrFun h2 j
      simp only [bkI, bkA, fromBlocks_mulVec, Sum.elim_inr, Pi.add_apply, zero_mulVec,
        one_mulVec, zero_add]
      exact this

variable (dS : Decomp (bkA S) (bkI S))

/-- **Woodford (2003), (1.1) and App. C.1: a solution of (1.1) with an exogenous instrument is a
Blanchard–Kahn equilibrium of `Decomp.bigA`** (any `Ẽ`, dates from `t₀`). -/
theorem exoSol_to_equil {Ω : Type*} {𝔼 : ExpectationSystem Ω} {c : ℕ → Ω → ιz → ℝ}
    {ie : ℕ → Ω → ℝ} {t0 : ℕ} {Z0 : Ω → ιZ → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hcb : GeneralSetup.BoundedV c) (hca : GeneralSetup.AdaptedV 𝔼 c)
    (hib : ∃ K, ∀ t ω, |ie t ω| ≤ K) (hia : 𝔼.Adapted ie) (hy : ExoSol S 𝔼 c ie t0 Z0 y) :
    GeneralBKCopy.Equil (Prop84General.shiftES 𝔼 t0) dS.bigA
      (dS.wBig (Prop84General.shiftES 𝔼 t0) (hExo S c ie t0)) (fun j ω => Z0 ω j)
      (toBK t0 y) := by
  obtain ⟨hS, hZ0, hi, ⟨K, hK⟩, ha⟩ := hy
  have hZk : ∀ t, t0 ≤ t → KnownV 𝔼 t (fun ω => Zpart (y (t + 1) ω)) := by
    intro t ht
    have e : (fun ω => Zpart (y (t + 1) ω)) =
        fun ω => S.A11 *ᵥ Zpart (y t ω) + S.A12 *ᵥ zpart (y t ω) :=
      funext fun ω => (hS t ht ω).1
    rw [e]
    have hZ : KnownV 𝔼 t (fun ω => Zpart (y t ω)) := fun j => ha t _
    have hz : KnownV 𝔼 t (fun ω => zpart (y t ω)) := fun i => ha t _
    exact PencilSplit.knownV_mulVec_add 𝔼 S.A11 hZ (PencilSplit.knownV_mulVec 𝔼 S.A12 hz)
  have hYb : BKForward.BoundedV (toBK t0 y) :=
    ⟨K, fun s k ω => by rcases k with i | j <;> exact hK _ ω _⟩
  have hYa : BKForward.AdaptedV (Prop84General.shiftES 𝔼 t0) (toBK t0 y) := by
    intro s k
    change 𝔼.E (s + t0) (toBK t0 y s k) = toBK t0 y s k
    rcases k with i | j
    · exact ha (s + t0) (Sum.inl (Sum.inr i))
    · exact ha (s + t0) (Sum.inl (Sum.inl j))
  have hDS : DSolves (Prop84General.shiftES 𝔼 t0) (bkA S) (bkI S) (hExo S c ie t0)
      (toBK t0 y) := by
    rw [dsolves_bk_iff]
    intro s ω
    have est : s + 1 + t0 = s + t0 + 1 := by omega
    refine ⟨?_, ?_⟩
    · obtain ⟨-, h2⟩ := hS (s + t0) (by omega) ω
      change S.Et *ᵥ (fun i => 𝔼.E (s + t0) (fun ω' => zpart (y (s + 1 + t0) ω') i) ω) = _
      rw [est]
      change S.Et *ᵥ EV 𝔼 (s + t0) (fun ω' => zpart (y (s + t0 + 1) ω')) ω = _
      rw [h2, hi (s + t0) (by omega) ω]
      funext i
      simp only [Pi.add_apply, hExo, Sum.elim_inl, Pi.smul_apply, smul_eq_mul]
      change _ = (S.A22 *ᵥ zpart (y (s + t0) ω)) i + (S.A21 *ᵥ Zpart (y (s + t0) ω)) i + _
      ring
    · change (fun j => 𝔼.E (s + t0) (fun ω' => Zpart (y (s + 1 + t0) ω') j) ω) = _
      rw [est]
      have h1 : (fun j => 𝔼.E (s + t0) (fun ω' => Zpart (y (s + t0 + 1) ω') j) ω) =
          Zpart (y (s + t0 + 1) ω) := funext fun j => congrFun (hZk (s + t0) (by omega) j) ω
      rw [h1, (hS (s + t0) (by omega) ω).1]
      funext j
      simp only [Pi.add_apply, hExo, Sum.elim_inr, add_zero]
      change _ = (S.A12 *ᵥ zpart (y (s + t0) ω)) j + (S.A11 *ᵥ Zpart (y (s + t0) ω)) j
      ring
  refine ⟨(dS.dsolves_iff_solves (hExo_bounded t0 hcb hib) (hExo_adapted t0 hca hia) hYb
    hYa).mp hDS, hYa, fun s j => ?_, fun j => ?_, hYb⟩
  · change 𝔼.E (s + t0) (fun ω => Zpart (y (s + 1 + t0) ω) j) =
      fun ω => Zpart (y (s + 1 + t0) ω) j
    rw [show s + 1 + t0 = s + t0 + 1 by omega]
    exact hZk (s + t0) (by omega) j
  · funext ω
    simp only [toBK, zero_add, Sum.elim_inr]
    exact congrFun (hZ0 ω) j

/-- **Woodford (2003), App. C.1 and (1.1): a Blanchard–Kahn equilibrium of `Decomp.bigA` gives a
solution of (1.1) with the exogenous instrument** (any `Ẽ`; the plan `ofBK`). -/
theorem equil_to_exoSol {Ω : Type*} {𝔼 : ExpectationSystem Ω} {c : ℕ → Ω → ιz → ℝ}
    {ie : ℕ → Ω → ℝ} {t0 : ℕ} {Z0 : Ω → ιZ → ℝ}
    (hcb : GeneralSetup.BoundedV c) (hca : GeneralSetup.AdaptedV 𝔼 c)
    (hib : ∃ K, ∀ t ω, |ie t ω| ≤ K) (hia : 𝔼.Adapted ie) {Y : ℕ → ιz ⊕ ιZ → Ω → ℝ}
    (hY : GeneralBKCopy.Equil (Prop84General.shiftES 𝔼 t0) dS.bigA
      (dS.wBig (Prop84General.shiftES 𝔼 t0) (hExo S c ie t0)) (fun j ω => Z0 ω j) Y) :
    ExoSol S 𝔼 c ie t0 Z0 (ofBK t0 Y ie) := by
  obtain ⟨hSol, ha, hpk, h0, hb⟩ := hY
  have hDS := (dS.dsolves_iff_solves (hExo_bounded t0 hcb hib) (hExo_adapted t0 hca hia) hb
    ha).mpr hSol
  rw [dsolves_bk_iff] at hDS
  obtain ⟨K, hK⟩ := hb
  obtain ⟨Ki, hKi⟩ := hib
  refine ⟨fun t ht ω => ⟨funext fun j => ?_, funext fun i => ?_⟩, fun ω => funext fun j => ?_,
    fun t ht ω => ?_, ⟨max (max K Ki) 0, fun t ω v => ?_⟩, fun t v => ?_⟩
  · -- `Z_{t+1} = A₁₁Z_t + A₁₂z_t`
    have e1 : t + 1 - t0 = t - t0 + 1 := by omega
    have e2 : t - t0 + t0 = t := by omega
    obtain ⟨-, h2⟩ := hDS (t - t0) ω
    have hk := congrFun h2 j
    have hp := congrFun (hpk (t - t0) j) ω
    change 𝔼.E (t - t0 + t0) _ ω = _ at hk hp
    rw [hp] at hk
    simp only [hExo, Sum.elim_inr, Pi.add_apply, add_zero] at hk
    simp only [ofBK, show t0 ≤ t + 1 by omega, ht, ↓reduceIte, e1,
      TidyR5aExogenousInstrument.Exo.Zpart_elim, TidyR5aExogenousInstrument.Exo.zpart_elim,
      Pi.add_apply]
    rw [hk]
    ring
  · -- `Ẽ E_tz_{t+1} = A₂₁Z_t + A₂₂z_t + B₂i_t + c_t`
    have e1 : t + 1 - t0 = t - t0 + 1 := by omega
    have e2 : t - t0 + t0 = t := by omega
    obtain ⟨h1, -⟩ := hDS (t - t0) ω
    have hEV : EV 𝔼 t (fun ω' => zpart (ofBK t0 Y ie (t + 1) ω')) ω =
        fun i => (Prop84General.shiftES 𝔼 t0).E (t - t0) (Y (t - t0 + 1) (Sum.inl i)) ω := by
      funext i
      change _ = 𝔼.E (t - t0 + t0) _ ω
      rw [e2]
      simp only [EV, zpart, ofBK, show t0 ≤ t + 1 by omega, ↓reduceIte, Sum.elim_inl,
        Sum.elim_inr, e1]
    rw [hEV, h1]
    simp only [ofBK, ht, ↓reduceIte, TidyR5aExogenousInstrument.Exo.Zpart_elim,
      TidyR5aExogenousInstrument.Exo.zpart_elim, TidyR5aExogenousInstrument.Exo.ipart_elim,
      Pi.add_apply, hExo, Sum.elim_inl, e2]
    ring
  · simp only [Zpart, ofBK, le_rfl, ↓reduceIte, Sum.elim_inl, Nat.sub_self]
    exact congrFun (h0 j) ω
  · simp [ipart, ofBK, ht]
  · simp only [ofBK]
    split_ifs
    · rcases v with (j | i) | u
      · exact (hK _ _ ω).trans ((le_max_left _ _).trans (le_max_left _ _))
      · exact (hK _ _ ω).trans ((le_max_left _ _).trans (le_max_left _ _))
      · exact (hKi t ω).trans ((le_max_right _ _).trans (le_max_left _ _))
    · simp only [Pi.zero_apply, abs_zero]
      exact le_max_right _ _
  · by_cases ht : t0 ≤ t
    · have e2 : t - t0 + t0 = t := by omega
      rcases v with (j | i) | u
      · have := ha (t - t0) (Sum.inr j)
        change 𝔼.E (t - t0 + t0) _ = _ at this
        rw [e2] at this
        simp only [ofBK, ht, ↓reduceIte, Sum.elim_inl]
        exact this
      · have := ha (t - t0) (Sum.inl i)
        change 𝔼.E (t - t0 + t0) _ = _ at this
        rw [e2] at this
        simp only [ofBK, ht, ↓reduceIte, Sum.elim_inl, Sum.elim_inr]
        exact this
      · simp only [ofBK, ht, ↓reduceIte, Sum.elim_inr]
        exact hia t
    · simp only [ofBK, ht, ↓reduceIte, Pi.zero_apply]
      exact 𝔼.const t 0

/-- Woodford (2003), (1.1) (tool): with no disturbance and a zero instrument path the
Blanchard–Kahn forcing of `Decomp.bigA` vanishes. -/
theorem wBig_hExo_zero {Ω : Type*} (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    dS.wBig (Prop84General.shiftES 𝔼 t0) (hExo S (fun _ _ _ => 0) (fun (_ : ℕ) (_ : Ω) => 0) t0) =
      fun _ _ _ => 0 := by
  rw [hExo_zero, Decomp.wBig_zero]
  rfl

/-- **Woodford (2003), p. 546, any `Ẽ`: without the genericity condition an exogenous instrument
rule is indeterminate.** -/
theorem not_exoDeterminate_of_not_generic {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω)
    (t0 : ℕ) (h : ¬ GenericX dS.bigA) : ¬ ExoDeterminate S 𝔼 t0 := by
  intro hD
  simp only [GenericX, not_forall] at h
  obtain ⟨v, hv, hx, hne⟩ := h
  have hcb : GeneralSetup.BoundedV (fun (_ : ℕ) (_ : Ω) (_ : ιz) => (0 : ℝ)) :=
    ⟨0, fun _ _ _ => by simp⟩
  have hca : GeneralSetup.AdaptedV 𝔼 (fun (_ : ℕ) (_ : Ω) (_ : ιz) => (0 : ℝ)) :=
    fun t i => 𝔼.const t 0
  have hib : ∃ K, ∀ (t : ℕ) (ω : Ω), |(fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) t ω| ≤ K :=
    ⟨0, fun _ _ => by simp⟩
  have hia : 𝔼.Adapted (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) := fun t => 𝔼.const t 0
  have h1 : GeneralBKCopy.Equil (Prop84General.shiftES 𝔼 t0) dS.bigA
      (dS.wBig (Prop84General.shiftES 𝔼 t0) (hExo S (fun _ _ _ => 0) (fun _ _ => 0) t0))
      (fun j ω => (fun (_ : Ω) (_ : ιZ) => (0 : ℝ)) ω j)
      (fun t k _ => (dS.bigA ^ t *ᵥ v) k) := by
    rw [wBig_hExo_zero]
    have hx0 : (fun j (ω : Ω) => (fun (_ : Ω) (_ : ιZ) => (0 : ℝ)) ω j) =
        fun j _ => v (Sum.inr j) := by
      funext j ω
      exact (hx j).symm
    rw [hx0]
    exact TidyR5aExogenousInstrument.BK.orbit_equil _ hv
  have h0 : GeneralBKCopy.Equil (Prop84General.shiftES 𝔼 t0) dS.bigA
      (dS.wBig (Prop84General.shiftES 𝔼 t0) (hExo S (fun _ _ _ => 0) (fun _ _ => 0) t0))
      (fun j ω => (fun (_ : Ω) (_ : ιZ) => (0 : ℝ)) ω j) (fun _ _ _ => 0) := by
    rw [wBig_hExo_zero]
    exact TidyR5aExogenousInstrument.BK.zero_equil _ _
  obtain ⟨y, -, huniq⟩ := hD (fun _ _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) hcb hca hib hia
    (fun j => 𝔼.const t0 0) ⟨0, fun _ _ => by simp⟩
  have e1 := huniq _ (equil_to_exoSol dS hcb hca hib hia h1) t0 le_rfl
  have e0 := huniq _ (equil_to_exoSol dS hcb hca hib hia h0) t0 le_rfl
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  apply hne
  funext k
  rcases k with i | j
  · have := congrFun (congrFun (e1.trans e0.symm) ω) (Sum.inl (Sum.inr i))
    simpa [ofBK] using this
  · exact hx j

/-- **Woodford (2003), p. 546, any `Ẽ`: too few bounded directions means non-existence.** -/
theorem not_exoDeterminate_of_finrank_lt {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω)
    (t0 : ℕ) (h : Module.finrank ℝ (boundedOrbits dS.bigA) < Fintype.card ιZ) :
    ¬ ExoDeterminate S 𝔼 t0 := by
  intro hD
  have hr : Module.finrank ℝ (LinearMap.range (TidyR5aExogenousInstrument.BK.projB dS.bigA)) <
      Module.finrank ℝ (ιZ → ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact (LinearMap.finrank_range_le _).trans_lt h
  have hne : LinearMap.range (TidyR5aExogenousInstrument.BK.projB dS.bigA) ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top] at hr
    exact lt_irrefl _ hr
  obtain ⟨c, hc⟩ : ∃ c, c ∉ LinearMap.range (TidyR5aExogenousInstrument.BK.projB dS.bigA) := by
    by_contra hcon
    push Not at hcon
    exact hne (eq_top_iff.mpr fun c _ => hcon c)
  have hcb : GeneralSetup.BoundedV (fun (_ : ℕ) (_ : Ω) (_ : ιz) => (0 : ℝ)) :=
    ⟨0, fun _ _ _ => by simp⟩
  have hca : GeneralSetup.AdaptedV 𝔼 (fun (_ : ℕ) (_ : Ω) (_ : ιz) => (0 : ℝ)) :=
    fun t i => 𝔼.const t 0
  have hib : ∃ K, ∀ (t : ℕ) (ω : Ω), |(fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) t ω| ≤ K :=
    ⟨0, fun _ _ => by simp⟩
  have hia : 𝔼.Adapted (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) := fun t => 𝔼.const t 0
  obtain ⟨y, hy, -⟩ := hD (fun _ _ _ => 0) (fun _ _ => 0) (fun _ j => c j) hcb hca hib hia
    (fun j => 𝔼.const t0 (c j))
    ⟨∑ j, |c j|, fun _ j => Finset.single_le_sum (f := fun j => |c j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)⟩
  have hY := exoSol_to_equil dS hcb hca hib hia hy
  rw [wBig_hExo_zero] at hY
  obtain ⟨v, hv, hvx⟩ := TidyR5aExogenousInstrument.BK.mem_proj_of_equil _ hY
  exact hc ⟨⟨v, hv⟩, funext fun j => hvx j⟩

/-- **Woodford (2003), p. 546, any `Ẽ`, with the Blanchard–Kahn matrix of a decomposition.** For
a nonempty sample space and no eigenvalue of `Decomp.bigA` on the unit circle, an exogenous
instrument rule gives a determinate equilibrium iff `Decomp.bigA` has exactly `n_Z` eigenvalues in
the open unit disc and the genericity condition holds. -/
theorem exoDeterminate_iff_bk {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    (hnu : NoUnit dS.bigA) :
    ExoDeterminate S 𝔼 t0 ↔ stableCount dS.bigA = Fintype.card ιZ ∧ GenericX dS.bigA := by
  constructor
  · intro hD
    have hg : GenericX dS.bigA := by
      by_contra h
      exact not_exoDeterminate_of_not_generic dS 𝔼 t0 h hD
    refine ⟨?_, hg⟩
    rw [← BKInvariantSplit.finrank_eq_stableCount hnu]
    refine le_antisymm (TidyR5aExogenousInstrument.BK.finrank_le_of_generic hg) ?_
    by_contra h
    exact not_exoDeterminate_of_finrank_lt dS 𝔼 t0 (lt_of_not_ge h) hD
  · rintro ⟨hd, hg⟩
    have hDet := (TidyR5aExogenousInstrument.BK.determinate_iff
      (Prop84General.shiftES 𝔼 t0) hnu).mpr ⟨hd, hg⟩
    intro c ie Z0 hcb hca hib hia hZk hZb
    have hwb : BKForward.BoundedV (dS.wBig (Prop84General.shiftES 𝔼 t0) (hExo S c ie t0)) := by
      have h1 := dS.vstar_spec (𝔼 := Prop84General.shiftES 𝔼 t0)
        (hExo_bounded (S := S) t0 hcb hib) (hExo_adapted (S := S) t0 hca hia)
      obtain ⟨-, hva, ⟨Mv, hMv⟩⟩ := h1
      have hψ : BKForward.BoundedV (dS.wF (Prop84General.shiftES 𝔼 t0) (hExo S c ie t0)) := by
        obtain ⟨Mg, hMg⟩ := boundedV_mv dS.Gi (boundedV_mv (dS.Q * dS.Hi)
          (hExo_bounded (S := S) t0 hcb hib) |> fun ⟨M, hM⟩ =>
            (⟨M, fun t b ω => hM t (Sum.inr b) ω⟩ : BKForward.BoundedV
              (fun t (b : Fin dS.r) => dS.gF (hExo S c ie t0) t (Sum.inr b))))
        refine ⟨max (Mv + 2 * Mv) Mg, fun t k ω => ?_⟩
        rcases k with a | b
        · simp only [Decomp.wF, Sum.elim_inl, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          have e1 := (Prop84General.shiftES 𝔼 t0).abs_E_le (fun ω' => hMv (t + 1) a ω') t ω
          have e2 := hMv t a ω
          refine le_trans ?_ (le_max_left _ _)
          calc |(Prop84General.shiftES 𝔼 t0).E t (dS.vstar (Prop84General.shiftES 𝔼 t0)
                (hExo S c ie t0) (t + 1) a) ω - 2 * dS.vstar (Prop84General.shiftES 𝔼 t0)
                (hExo S c ie t0) t a ω|
              ≤ |(Prop84General.shiftES 𝔼 t0).E t (dS.vstar (Prop84General.shiftES 𝔼 t0)
                (hExo S c ie t0) (t + 1) a) ω| + |2 * dS.vstar (Prop84General.shiftES 𝔼 t0)
                (hExo S c ie t0) t a ω| := abs_sub _ _
            _ ≤ Mv + 2 * Mv := by rw [abs_mul]; norm_num; linarith
        · simp only [Decomp.wF, Sum.elim_inr]
          exact (hMg t b ω).trans (le_max_right _ _)
      exact boundedV_mv _ hψ
    have hwa : BKForward.AdaptedV (Prop84General.shiftES 𝔼 t0)
        (dS.wBig (Prop84General.shiftES 𝔼 t0) (hExo S c ie t0)) := by
      have h1 := dS.vstar_spec (𝔼 := Prop84General.shiftES 𝔼 t0)
        (hExo_bounded (S := S) t0 hcb hib) (hExo_adapted (S := S) t0 hca hia)
      obtain ⟨-, hva, -⟩ := h1
      have hga := adaptedV_mv (Prop84General.shiftES 𝔼 t0) (dS.Q * dS.Hi)
        (hExo_adapted (S := S) t0 hca hia)
      have hψ : BKForward.AdaptedV (Prop84General.shiftES 𝔼 t0)
          (dS.wF (Prop84General.shiftES 𝔼 t0) (hExo S c ie t0)) := by
        intro t k
        rcases k with a | b
        · simp only [Decomp.wF, Sum.elim_inl]
          rw [map_sub, map_smul, (Prop84General.shiftES 𝔼 t0).known le_rfl, hva t a]
        · simp only [Decomp.wF, Sum.elim_inr]
          exact adaptedV_mv (Prop84General.shiftES 𝔼 t0) dS.Gi
            (a := fun t (b : Fin dS.r) => dS.gF (hExo S c ie t0) t (Sum.inr b))
            (fun t b => hga t (Sum.inr b)) t b
      exact adaptedV_mv _ _ hψ
    obtain ⟨Y, hY, huniq⟩ := hDet _ hwb hwa (fun j ω => Z0 ω j)
      (fun j => by change 𝔼.E (0 + t0) _ = _; rw [zero_add]; exact hZk j)
      (by obtain ⟨K, hK⟩ := hZb; exact ⟨K, fun j ω => hK ω j⟩)
    refine ⟨ofBK t0 Y ie, equil_to_exoSol dS hcb hca hib hia hY, fun y' hy' t ht => ?_⟩
    rw [TidyR5aExogenousInstrument.Exo.ofBK_toBK S hy' t ht,
      huniq _ (exoSol_to_equil dS hcb hca hib hia hy')]

/-- **Woodford (2003), (1.15) and p. 546: a singular pencil is never determinate.** If
`det[A − μÎ]` is the zero polynomial (possible only when `Ẽ` is singular), then (1.1) with no
disturbance, a zero instrument and `Z_{t₀} = 0` has, besides `0`, a nonzero bounded
deterministic solution: the coefficients of a polynomial null vector `x(μ)` of `A − μÎ`, run
backwards in time. -/
theorem not_exoDeterminate_of_pencil_zero {Ω : Type*} [Nonempty Ω] (h : S.pencilPoly = 0)
    (𝔼 : ExpectationSystem Ω) (t0 : ℕ) : ¬ ExoDeterminate S 𝔼 t0 := by
  intro hDet
  set M : Matrix (ιZ ⊕ ιz) (ιZ ⊕ ιz) ℝ[X] :=
    S.Ahat.map Polynomial.C - (X : ℝ[X]) • S.Ihat.map Polynomial.C with hM
  have hdet : M.det = 0 := by
    have e : M.det.map Complex.ofRealHom = S.pencilPoly := by
      rw [← Polynomial.coe_mapRingHom, RingHom.map_det, LinearRESystem.pencilPoly]
      congr 1
      ext a b
      simp [hM]
    rw [h] at e
    exact (Polynomial.map_eq_zero_iff Complex.ofRealHom.injective).mp e
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := M)).mpr hdet
  set x : ℕ → ιZ ⊕ ιz → ℝ := fun p l => (v l).coeff p with hx
  have hentry : ∀ r l, M r l = Polynomial.C (S.Ahat r l) - X * Polynomial.C (S.Ihat r l) := by
    intro r l
    simp [hM]
  have hrec : ∀ p, S.Ahat *ᵥ x (p + 1) = S.Ihat *ᵥ x p := by
    intro p
    funext r
    have e := congrArg (fun q => q.coeff (p + 1)) (congrFun hv r)
    simp only [mulVec, dotProduct, hentry, Polynomial.finsetSum_coeff, Pi.zero_apply,
      Polynomial.coeff_zero] at e
    have hterm : ∀ l, ((Polynomial.C (S.Ahat r l) - X * Polynomial.C (S.Ihat r l)) * v l).coeff
        (p + 1) = S.Ahat r l * x (p + 1) l - S.Ihat r l * x p l := by
      intro l
      rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul, mul_assoc, Polynomial.coeff_X_mul,
        Polynomial.coeff_C_mul]
    simp only [hterm, Finset.sum_sub_distrib] at e
    simp only [mulVec, dotProduct]
    linarith
  have h0 : S.Ahat *ᵥ x 0 = 0 := by
    funext r
    have e := congrArg (fun q => q.coeff 0) (congrFun hv r)
    simp only [mulVec, dotProduct, hentry, Polynomial.finsetSum_coeff, Pi.zero_apply,
      Polynomial.coeff_zero] at e
    have hterm : ∀ l, ((Polynomial.C (S.Ahat r l) - X * Polynomial.C (S.Ihat r l)) * v l).coeff
        0 = S.Ahat r l * x 0 l := by
      intro l
      rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul, mul_assoc,
        Polynomial.coeff_X_mul_zero, sub_zero]
    simp only [hterm] at e
    simpa [mulVec, dotProduct] using e
  obtain ⟨D, hD⟩ : ∃ D, ∀ p, D < p → x p = 0 := by
    refine ⟨∑ l, (v l).natDegree, fun p hp => funext fun l => ?_⟩
    refine Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ?_ hp)
    exact Finset.single_le_sum (f := fun l => (v l).natDegree) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ l)
  obtain ⟨p0, hp0⟩ : ∃ p0, x p0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hv0
    funext l
    ext p
    exact congrFun (hcon p) l
  have hp0D : p0 ≤ D := by
    by_contra hlt
    exact hp0 (hD p0 (by omega))
  set N := t0 + D + 1 with hN
  set vec : ℕ → ιZ ⊕ ιz → ℝ := fun t => if t ≤ N then x (N - t) else 0 with hvec
  have hstep : ∀ t, S.Ihat *ᵥ vec (t + 1) = S.Ahat *ᵥ vec t := by
    intro t
    by_cases ht : t + 1 ≤ N
    · simp only [hvec, ht, show t ≤ N by omega, ite_true]
      rw [show N - t = (N - (t + 1)) + 1 by omega, hrec]
    · by_cases ht' : t = N
      · rw [ht']
        simp only [hvec]
        rw [ite_eq_right (by omega), ite_eq_left le_rfl, Nat.sub_self, h0, mulVec_zero]
      · simp only [hvec, ht, show ¬ t ≤ N by omega, ite_false, mulVec_zero]
  have hrows : ∀ t, (vec (t + 1) ∘ Sum.inl = S.A11 *ᵥ (vec t ∘ Sum.inl) +
      S.A12 *ᵥ (vec t ∘ Sum.inr)) ∧ (S.Et *ᵥ (vec (t + 1) ∘ Sum.inr) =
      S.A21 *ᵥ (vec t ∘ Sum.inl) + S.A22 *ᵥ (vec t ∘ Sum.inr)) := by
    intro t
    have e := hstep t
    have hv1 : vec (t + 1) = Sum.elim (vec (t + 1) ∘ Sum.inl) (vec (t + 1) ∘ Sum.inr) := by
      funext k
      rcases k with i | j <;> rfl
    have hv2 : vec t = Sum.elim (vec t ∘ Sum.inl) (vec t ∘ Sum.inr) := by
      funext k
      rcases k with i | j <;> rfl
    rw [hv1, hv2, LinearRESystem.Ihat, LinearRESystem.Ahat, fromBlocks_mulVec,
      fromBlocks_mulVec] at e
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, one_mulVec, zero_mulVec, add_zero,
      zero_add] at e
    exact ⟨congrArg (fun f => f ∘ Sum.inl) e, congrArg (fun f => f ∘ Sum.inr) e⟩
  set y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ := fun t _ => Sum.elim (vec t) (fun _ => 0) with hy
  have hvb : ∀ t l, |vec t l| ≤ ∑ q ∈ Finset.range (N + 1), ∑ l, |x q l| := by
    intro t l
    simp only [hvec]
    split_ifs with htN
    · refine le_trans ?_ (Finset.single_le_sum (f := fun q => ∑ l, |x q l|)
        (fun q _ => Finset.sum_nonneg fun l _ => abs_nonneg _)
        (Finset.mem_range.mpr (by omega : N - t < N + 1)))
      exact Finset.single_le_sum (f := fun l => |x (N - t) l|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ l)
    · rw [Pi.zero_apply, abs_zero]
      exact Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun l _ => abs_nonneg _
  have hsol : ExoSol S 𝔼 (fun _ _ _ => 0) (fun _ _ => 0) t0 (fun _ _ => 0) y := by
    refine ⟨fun t _ ω => ⟨?_, ?_⟩, fun ω => ?_, fun t _ ω => rfl,
      ⟨∑ q ∈ Finset.range (N + 1), ∑ l, |x q l|, fun t ω v => ?_⟩, fun t v => ?_⟩
    · exact (hrows t).1
    · rw [show (fun ω' => zpart (y (t + 1) ω')) = fun _ => vec (t + 1) ∘ Sum.inr from rfl,
        PencilSplit.EV_const, (hrows t).2]
      simp only [ipart, hy, Sum.elim_inr, zero_smul, add_zero]
      change _ = _ + _ + (0 : ιz → ℝ)
      rw [add_zero]
      rfl
    · funext j
      have hx0 : x (D + 1) = 0 := hD (D + 1) (by omega)
      change vec t0 (Sum.inl j) = 0
      simp only [hvec, show t0 ≤ N by omega, ite_true, show N - t0 = D + 1 by omega, hx0,
        Pi.zero_apply]
    · rcases v with l | u
      · exact hvb t l
      · simp only [hy, Sum.elim_inr, abs_zero]
        exact Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun l _ => abs_nonneg _
    · exact 𝔼.const t _
  have hzero : ExoSol S 𝔼 (fun _ _ _ => 0) (fun _ _ => 0) t0 (fun _ _ => 0)
      (fun _ _ _ => 0) := by
    refine ⟨fun t _ ω => ⟨?_, ?_⟩, fun ω => rfl, fun t _ ω => rfl,
      ⟨0, fun _ _ _ => by simp⟩, fun t v => 𝔼.const t 0⟩
    · funext j
      simp [Zpart, zpart, mulVec, dotProduct]
    · rw [show (fun ω' => zpart ((fun _ _ _ => (0 : ℝ)) (t + 1) ω' :
          (ιZ ⊕ ιz) ⊕ Unit → ℝ)) = fun _ => (0 : ιz → ℝ) from rfl, PencilSplit.EV_const]
      funext i
      simp [Zpart, zpart, ipart, mulVec, dotProduct]
  have hcb : GeneralSetup.BoundedV (fun (_ : ℕ) (_ : Ω) (_ : ιz) => (0 : ℝ)) :=
    ⟨0, fun _ _ _ => by simp⟩
  obtain ⟨ys, -, huniq⟩ := hDet (fun _ _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) hcb
    (fun t i => 𝔼.const t 0) ⟨0, fun _ _ => by simp⟩ (fun t => 𝔼.const t 0)
    (fun j => 𝔼.const t0 0) ⟨0, fun _ _ => by simp⟩
  have ht1 : t0 ≤ N - p0 := by omega
  have e := (huniq y hsol (N - p0) ht1).trans (huniq _ hzero (N - p0) ht1).symm
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  apply hp0
  funext l
  have := congrFun (congrFun e ω) (Sum.inl l)
  simp only [hy, Sum.elim_inl, hvec, show N - p0 ≤ N by omega, ite_true,
    show N - (N - p0) = p0 by omega] at this
  exact this

/-- **Woodford (2003), p. 546, any `Ẽ`, for a regular pencil.** For a nonempty sample space, a
decomposition of the pencil and no root of (1.15) on the unit circle, an exogenous instrument
rule gives a determinate equilibrium iff (1.15) has exactly `n_Z` roots (with multiplicity) in
the open unit disc and the genericity condition of `Decomp.bigA` holds. -/
theorem exoDeterminate_iff_roots {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    (hcirc : ∀ μ ∈ S.pencilPoly.roots, ‖μ‖ ≠ 1) :
    ExoDeterminate S 𝔼 t0 ↔
      Multiset.card (S.pencilPoly.roots.filter fun μ => ‖μ‖ < 1) = Fintype.card ιZ ∧
        GenericX dS.bigA := by
  have hnu : NoUnit dS.bigA := dS.noUnit_bigA_iff.mpr (by rw [pen_bk]; exact hcirc)
  rw [exoDeterminate_iff_bk dS 𝔼 t0 hnu, dS.stableCount_bigA, pen_bk]

variable (S)

/-- **Woodford (2003), p. 546, for every `Ẽ`: "rational-expectations equilibrium is (generically)
determinate if the number of roots `μᵢ` such that `|μᵢ| < 1` is exactly equal to `n_Z`".** For a
nonempty sample space and no root of (1.15) on the unit circle, an exogenous instrument rule gives
a determinate equilibrium **iff** the pencil is regular (`det[A − μÎ] ≢ 0`), (1.15) has exactly
`n_Z` roots in the open unit disc (counted with multiplicity; when `Ẽ` is singular the "roots at
infinity" are not counted), and the genericity condition holds (for every decomposition of the
pencil — equivalently for one). -/
theorem exoDeterminate_iff {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    (hcirc : ∀ μ ∈ S.pencilPoly.roots, ‖μ‖ ≠ 1) :
    ExoDeterminate S 𝔼 t0 ↔ S.pencilPoly ≠ 0 ∧
      Multiset.card (S.pencilPoly.roots.filter fun μ => ‖μ‖ < 1) = Fintype.card ιZ ∧
        ∀ dS : Decomp (bkA S) (bkI S), GenericX dS.bigA := by
  constructor
  · intro hD
    have hreg : S.pencilPoly ≠ 0 := fun h0 => not_exoDeterminate_of_pencil_zero h0 𝔼 t0 hD
    obtain ⟨dS⟩ := nonempty_decomp (A := bkA S) (I := bkI S) (by rw [pen_bk]; exact hreg)
    exact ⟨hreg, ((exoDeterminate_iff_roots dS 𝔼 t0 hcirc).mp hD).1,
      fun d' => ((exoDeterminate_iff_roots d' 𝔼 t0 hcirc).mp hD).2⟩
  · rintro ⟨hreg, hc, hg⟩
    obtain ⟨dS⟩ := nonempty_decomp (A := bkA S) (I := bkI S) (by rw [pen_bk]; exact hreg)
    exact (exoDeterminate_iff_roots dS 𝔼 t0 hcirc).mpr ⟨hc, hg dS⟩

/-- **Woodford (2003), p. 546, for every `Ẽ`: more than `n_Z` roots of (1.15) in the open unit
disc means an exogenous instrument rule is indeterminate** (no condition on the unit circle). -/
theorem not_exoDeterminate_of_card_lt {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω)
    (t0 : ℕ)
    (h : Fintype.card ιZ < Multiset.card (S.pencilPoly.roots.filter fun μ => ‖μ‖ < 1)) :
    ¬ ExoDeterminate S 𝔼 t0 := by
  by_cases h0 : S.pencilPoly = 0
  · exact not_exoDeterminate_of_pencil_zero h0 𝔼 t0
  obtain ⟨dS⟩ := nonempty_decomp (A := bkA S) (I := bkI S) (by rw [pen_bk]; exact h0)
  rw [← pen_bk, ← dS.stableCount_bigA] at h
  have hg : ¬ GenericX dS.bigA := fun hg => absurd
    ((BKInvariantSplit.stableCount_le_finrank _).trans
      (TidyR5aExogenousInstrument.BK.finrank_le_of_generic hg)) (not_le.mpr h)
  exact not_exoDeterminate_of_not_generic dS 𝔼 t0 hg

/-- Woodford (2003), (1.15): with no predetermined variable the pencil is regular —
`det[A₂₂ − μẼ]` equals `det A₂₂ ≠ 0` at `μ = 0`. -/
theorem pencil_ne_zero_of_isEmpty [IsEmpty ιZ] : S.pencilPoly ≠ 0 := by
  intro h0
  have e := congrArg (Polynomial.eval 0) h0
  rw [PencilSplit.pencilPoly_eval, zero_smul, sub_zero, Polynomial.eval_zero] at e
  have hdet : (S.A22.map Complex.ofReal).det ≠ 0 := by
    rw [show S.A22.map Complex.ofReal = Complex.ofRealHom.mapMatrix S.A22 from rfl,
      ← RingHom.map_det]
    exact (map_ne_zero Complex.ofRealHom).mpr S.A22_isUnit.ne_zero
  let eqv : ιZ ⊕ ιz ≃ ιz := Equiv.emptySum ιZ ιz
  have hA' : S.Ahat.map Complex.ofReal = (S.A22.map Complex.ofReal).submatrix eqv eqv := by
    ext a b
    rcases a with a | a
    · exact isEmptyElim a
    rcases b with b | b
    · exact isEmptyElim b
    simp [LinearRESystem.Ahat, eqv]
  rw [hA', det_submatrix_equiv_self] at e
  exact hdet e

/-- Woodford (2003), (1.15): if (1.15) has exactly `n_Z` roots in the open unit disc, the pencil
is regular (a singular pencil has no roots, and `n_Z = 0` forces regularity). -/
theorem pencil_ne_zero_of_card_eq
    (h : Multiset.card (S.pencilPoly.roots.filter fun μ => ‖μ‖ < 1) = Fintype.card ιZ) :
    S.pencilPoly ≠ 0 := by
  intro h0
  rw [h0, Polynomial.roots_zero, Multiset.filter_zero, Multiset.card_zero] at h
  have : IsEmpty ιZ := Fintype.card_eq_zero_iff.mp h.symm
  exact pencil_ne_zero_of_isEmpty S h0

/-- **Woodford (2003), p. 546, for every `Ẽ`, in the book's form: an exogenous instrument rule
gives a determinate equilibrium iff (1.15) has exactly `n_Z` roots with `|μ| < 1` (with
multiplicity; when `Ẽ` is singular, the "roots at infinity" — the missing degree — are not
counted) and the genericity condition holds** (nonempty sample space, no root of (1.15) on the unit
circle). A singular pencil (`det[A − μÎ] ≡ 0`) has no roots and is never determinate. -/
theorem exoDeterminate_iff_count {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    (hcirc : ∀ μ ∈ S.pencilPoly.roots, ‖μ‖ ≠ 1) :
    ExoDeterminate S 𝔼 t0 ↔
      Multiset.card (S.pencilPoly.roots.filter fun μ => ‖μ‖ < 1) = Fintype.card ιZ ∧
        ∀ dS : Decomp (bkA S) (bkI S), GenericX dS.bigA := by
  rw [exoDeterminate_iff S 𝔼 t0 hcirc]
  constructor
  · rintro ⟨-, hc, hg⟩
    exact ⟨hc, hg⟩
  · rintro ⟨hc, hg⟩
    exact ⟨pencil_ne_zero_of_card_eq S hc, hc, hg⟩

/-- Woodford (2003), p. 547, any `Ẽ`: for a regular pencil the zero root of (1.15) has
multiplicity at least `n − rank A`. -/
theorem card_sub_rank_le_count_zero (h : S.pencilPoly ≠ 0) :
    Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank ≤ S.pencilPoly.roots.count 0 := by
  have hdvd := X_pow_dvd_det S.Ahat S.Ihat
  have e : (S.Ahat.map Polynomial.C - (X : ℝ[X]) • S.Ihat.map Polynomial.C).det.map
      Complex.ofRealHom = S.pencilPoly := by
    rw [← Polynomial.coe_mapRingHom, RingHom.map_det, LinearRESystem.pencilPoly]
    congr 1
    ext a b
    simp
  have hdvd' := Polynomial.map_dvd Complex.ofRealHom hdvd
  rw [e, Polynomial.map_pow, Polynomial.map_X] at hdvd'
  rw [Polynomial.count_roots, Polynomial.le_rootMultiplicity_iff h, map_zero, sub_zero]
  exact hdvd'

/-- Woodford (2003), p. 547, any `Ẽ`: for a regular pencil, the count of p. 547 (zero root counted
`n − rank A` times) never exceeds the number of roots of (1.15) in the open unit disc counted with
multiplicity. -/
theorem stableCount_le_card (h : S.pencilPoly ≠ 0) :
    S.stableCount 1 ≤ Multiset.card (S.pencilPoly.roots.filter fun μ => ‖μ‖ < 1) := by
  rw [LinearRESystem.stableCount]
  have hsplit := Multiset.filter_add_not (fun r : ℂ => r = 0)
    (S.pencilPoly.roots.filter fun μ => ‖μ‖ < 1)
  rw [← hsplit, Multiset.card_add, Multiset.filter_filter, Multiset.filter_filter]
  have h0 : Multiset.card (S.pencilPoly.roots.filter fun μ => μ = 0 ∧ ‖μ‖ < 1) =
      S.pencilPoly.roots.count 0 := by
    rw [Multiset.count_eq_card_filter_eq]
    congr 1
    refine Multiset.filter_congr fun r _ => ?_
    constructor
    · rintro ⟨rfl, -⟩
      rfl
    · rintro rfl
      exact ⟨rfl, by simp⟩
  have h1 : (S.pencilPoly.roots.filter fun μ => ¬ μ = 0 ∧ ‖μ‖ < 1) =
      S.pencilPoly.roots.filter fun μ => μ ≠ 0 ∧ ‖μ‖ < 1 := rfl
  rw [h0, h1]
  have := card_sub_rank_le_count_zero S h
  omega

/-- **Woodford (2003), pp. 546–547, for every `Ẽ`: under the Sargent–Wallace property no exogenous
instrument rule gives a determinate equilibrium** (nonempty sample space; singular pencils are
never determinate). -/
theorem sargentWallace_not_exoDeterminate {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω)
    (t0 : ℕ) (h : S.SargentWallace) : ¬ ExoDeterminate S 𝔼 t0 := by
  by_cases h0 : S.pencilPoly = 0
  · exact not_exoDeterminate_of_pencil_zero h0 𝔼 t0
  exact not_exoDeterminate_of_card_lt S 𝔼 t0 (lt_of_lt_of_le h (stableCount_le_card S h0))

/-! ### A singular pencil -/

/-- Woodford (2003), (1.1), p. 537: a system with a singular pencil (`n_Z = 1`, `n_z = 2`):
`Z_{t+1} = z¹_t`, `E_tz²_{t+1} = z¹_t + i_t + c¹_t`, `0 = −Z_t + z²_t + c²_t`. `A₂₂ = I` is
invertible, but `Ẽ = [[0, 1], [0, 0]]` is singular and `det[A − μÎ] ≡ 0`. -/
def singSys : LinearRESystem (Fin 1) (Fin 2) where
  A11 := 0
  A12 := !![1, 0]
  A21 := !![0; -1]
  A22 := 1
  Et := !![0, 1; 0, 0]
  B2 := ![1, 0]
  A22_isUnit := by simp
  B2_ne_zero := by
    intro h
    have := congrFun h 0
    simp at this

/-- Woodford (2003), (1.15): `Ẽ` of `singSys` is singular. -/
theorem singSys_Et_det : singSys.Et.det = 0 := by
  simp [singSys, det_fin_two]

/-- **Woodford (2003), (1.15): the pencil of `singSys` is singular**, `det[A − μÎ] ≡ 0`. -/
theorem singSys_pencilPoly : singSys.pencilPoly = 0 := by
  refine Polynomial.funext fun μ => ?_
  rw [PencilSplit.pencilPoly_eval, Polynomial.eval_zero,
    ← det_submatrix_equiv_self finSumFinEquiv.symm]
  rw [det_fin_three]
  simp [singSys, LinearRESystem.Ahat, LinearRESystem.Ihat, finSumFinEquiv, Fin.addCases]

/-- **Woodford (2003), p. 546: in `singSys` no exogenous instrument rule is determinate** (any
expectation system with a nonempty sample space), although (1.15) has `0 ≠ n_Z` roots in the unit
disc only because it has no roots at all. -/
theorem singSys_not_exoDeterminate {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω)
    (t0 : ℕ) : ¬ ExoDeterminate singSys 𝔼 t0 :=
  not_exoDeterminate_of_pencil_zero singSys_pencilPoly 𝔼 t0

end Sys

end Woodford.OptimalPolicyRules.TidyR5aExoSingular
