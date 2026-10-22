/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.Determinacy2Learning
import NeoWicksellianFramework.BlanchardKahn
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The E-stability differential equation (2.20)

Woodford (2003), *Interest and Prices*, Chapter 4, §2.3, pp. 264–266 ((2.20) and n. 37), and
App. C.7, p. 684. The book defines an s.c.e. `θ̄` to be E-stable if it is a locally stable rest
point of the ordinary differential equation `θ̇ = T(θ) − θ` (2.20), and states (p. 266) that this
holds iff every eigenvalue of `DT(θ̄) − I` has negative real part, ignoring (n. 37) the
non-generic case of eigenvalues with zero real part. The project defines E-stability through the
eigenvalues (`Determinacy2Learning.EStable`, `EStableAt`). Here the link with the differential
equation is proved for the linear(ised) map `T(θ) = θ̄ + J (θ − θ̄)`, with no genericity
assumption:

* `linT`, `IsESol`: the linear(ised) `T`-map and the solutions of (2.20) (differentiable on all
  of `ℝ`); `flow`: `exp(τ (J − I))` as a continuous linear map; `isESol_flow`,
  `eq_flow_of_isESol`, `existsUnique_isESol`: from every initial belief there is exactly one
  solution, `θ(τ) = θ̄ + exp(τ (J − I)) (θ(0) − θ̄)`.
* `flow_bound`: under E-stability `‖exp(τ (J − I))‖` decays geometrically (the eigenvalues of
  `exp(J − I)` are `e^μ`, `μ` an eigenvalue of `J − I`, by a common-eigenvector argument:
  `kMat_map_mulVec_of_eig`, `norm_lt_one_of_isEig_kMat`; then Gelfand's formula via
  `BlanchardKahn.pow_entry_bound`).
* `tendsto_of_eStable`: E-stable ⇒ every solution converges to `θ̄`;
  `eStable_of_tendsto`: if every solution converges, `J` is E-stable (an eigenvalue `μ` with
  `Re μ ≥ 0` and eigenvector `v` gives the non-convergent real solutions `Re(e^{τμ} v)`,
  `Re(e^{τμ} i v)`: `eigSol`, `isESol_eigSol`); **`eStable_iff_tendsto`**.
* `IsLocallyStable` (the book's wording: Lyapunov stable and locally attracting);
  **`eStable_iff_locallyStable`**: for the linear(ised) map the eigenvalue definition and the
  book's ODE definition coincide, including the boundary case `Re μ = 0` excluded by n. 37.
* `eStableAt_iff_ode`: `EStableAt T θ̄` iff `θ̄` is a differentiable fixed point and every
  solution of the linearised equation converges; `linT_eq_of_affine`,
  `eStable_iff_tendsto_affine`: for an affine `T` (Propositions 4.8, 4.9) this is the actual
  equation (2.20), and convergence is global.

The stochastic-approximation results the book cites from Evans and Honkapohja (pp. 265–266:
mean dynamics (2.22) approximate (2.20), convergence with probability one of least-squares
learning) are not formalised.
-/

namespace Woodford.NeoWicksellianFramework.TidyR5EStabilityODE

open Matrix Filter Topology NormedSpace
open Determinacy2Learning (EStable EStableAt)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The linear(ised) `T`-map and the differential equation (2.20) -/

/-- Woodford (2003), p. 266: the `T`-map linearised at the rest point `θ̄`,
`T(θ) = θ̄ + J (θ − θ̄)` (`J = DT(θ̄)`); for Proposition 4.8 it is the map (2.19) itself. -/
def linT (J : Matrix ι ι ℝ) (θs θ : ι → ℝ) : ι → ℝ := θs + J *ᵥ (θ - θs)

/-- Woodford (2003), (2.20) p. 265: `θ : ℝ → ℝⁿ` solves the E-stability differential equation
`θ̇ = T(θ) − θ` (at every date `τ`). -/
def IsESol (T : (ι → ℝ) → ι → ℝ) (θ : ℝ → ι → ℝ) : Prop :=
  ∀ τ : ℝ, HasDerivAt θ (T (θ τ) - θ τ) τ

/-- Woodford (2003), p. 266: for the linearised map, `T(θ) − θ = (J − I)(θ − θ̄)`. -/
theorem linT_sub (J : Matrix ι ι ℝ) (θs θ : ι → ℝ) :
    linT J θs θ - θ = (J - 1) *ᵥ (θ - θs) := by
  simp only [linT, Matrix.sub_mulVec, Matrix.one_mulVec]
  abel

/-- Woodford (2003), p. 266: the matrix `A` as a continuous linear map `x ↦ A x`. -/
noncomputable def gen (A : Matrix ι ι ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' A)

/-- Woodford (2003), p. 266: `gen A x = A x`. -/
theorem gen_apply (A : Matrix ι ι ℝ) (x : ι → ℝ) : gen A x = A *ᵥ x := by
  simp [gen, Matrix.toLin'_apply]

/-- Woodford (2003), p. 266: `gen (−A) = −gen A`. -/
theorem gen_neg (A : Matrix ι ι ℝ) : gen (-A) = -gen A := by
  ext x i
  simp [gen_apply, Matrix.neg_mulVec]

/-- Woodford (2003), (2.20) p. 265: the flow `exp(τ A)` of the linear equation `ẋ = A x`. -/
noncomputable def flow (A : Matrix ι ι ℝ) (τ : ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) := exp (τ • gen A)

/-- Woodford (2003), (2.20): `exp((s + t) A) = exp(s A) exp(t A)`. -/
theorem flow_add (A : Matrix ι ι ℝ) (s t : ℝ) : flow A (s + t) = flow A s * flow A t := by
  unfold flow
  rw [add_smul]
  exact exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
    (((Commute.refl (gen A)).smul_left s).smul_right t)
    ((expSeries_radius_eq_top ℝ ((ι → ℝ) →L[ℝ] (ι → ℝ))).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℝ ((ι → ℝ) →L[ℝ] (ι → ℝ))).symm ▸ edist_lt_top _ _)

/-- Woodford (2003), (2.20): `exp(0 A) = I`. -/
theorem flow_zero (A : Matrix ι ι ℝ) : flow A 0 = 1 := by
  simp [flow]

/-- Woodford (2003), (2.20): `exp(τ A) exp(−τ A) = I`. -/
theorem flow_mul_flow_neg (A : Matrix ι ι ℝ) (τ : ℝ) : flow A τ * flow (-A) τ = 1 := by
  unfold flow
  rw [gen_neg, ← exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
    (((Commute.refl (gen A)).neg_right.smul_left τ).smul_right τ)
    ((expSeries_radius_eq_top ℝ ((ι → ℝ) →L[ℝ] (ι → ℝ))).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℝ ((ι → ℝ) →L[ℝ] (ι → ℝ))).symm ▸ edist_lt_top _ _)]
  simp

/-- Woodford (2003), (2.20): `d/dτ exp(τ A) x = A exp(τ A) x`. -/
theorem hasDerivAt_flow_apply (A : Matrix ι ι ℝ) (x : ι → ℝ) (τ : ℝ) :
    HasDerivAt (fun u => flow A u x) (A *ᵥ flow A τ x) τ := by
  have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (gen A) τ).clm_apply (hasDerivAt_const τ x)
  change HasDerivAt (fun y => exp (y • gen A) x) _ τ
  convert h using 1
  rw [map_zero, add_zero, mul_apply_eq_comp, gen_apply]
  rfl

/-- Woodford (2003), (2.20) p. 265: from every initial belief `θ₀`,
`θ(τ) = θ̄ + exp(τ (J − I)) (θ₀ − θ̄)` solves `θ̇ = T(θ) − θ` for the linearised map. -/
theorem isESol_flow (J : Matrix ι ι ℝ) (θs x0 : ι → ℝ) :
    IsESol (linT J θs) (fun τ => θs + flow (J - 1) τ (x0 - θs)) := by
  intro τ
  have h := (hasDerivAt_flow_apply (J - 1) (x0 - θs) τ).const_add θs
  convert h using 1
  rw [linT_sub, add_sub_cancel_left]

/-- Woodford (2003), (2.20) p. 265: **every solution of the linearised equation is the flow
solution**, `θ(τ) = θ̄ + exp(τ (J − I)) (θ(0) − θ̄)` (`exp(−τ(J − I))(θ(τ) − θ̄)` has zero
derivative). -/
theorem eq_flow_of_isESol {J : Matrix ι ι ℝ} {θs : ι → ℝ} {θ : ℝ → ι → ℝ}
    (h : IsESol (linT J θs) θ) (τ : ℝ) : θ τ = θs + flow (J - 1) τ (θ 0 - θs) := by
  set A := J - 1 with hA
  have hx : ∀ t, HasDerivAt (fun u => θ u - θs) (A *ᵥ (θ t - θs)) t := fun t => by
    have := (h t).sub_const θs
    rwa [linT_sub] at this
  set g : ℝ → ι → ℝ := fun t => flow (-A) t (θ t - θs) with hg
  have hgd : ∀ t, HasDerivAt g 0 t := by
    intro t
    change HasDerivAt (fun y => exp (y • gen (-A)) (θ y - θs)) 0 t
    have h1 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) (gen (-A)) t).clm_apply (hx t)
    convert h1 using 1
    rw [mul_apply_eq_comp, gen_apply, ← map_add, Matrix.neg_mulVec, neg_add_cancel,
      map_zero]
  have hconst : g τ = g 0 :=
    is_const_of_deriv_eq_zero (fun t => (hgd t).differentiableAt) (fun t => (hgd t).deriv) τ 0
  have hg0 : g 0 = θ 0 - θs := by
    simp [hg, flow_zero]
  have key : θ τ - θs = flow A τ (θ 0 - θs) := by
    rw [← hg0, ← hconst, hg]
    simp only
    rw [← mul_apply_eq_comp, flow_mul_flow_neg, one_apply_eq_self]
  rw [← key, add_sub_cancel]

omit [DecidableEq ι] in
/-- Woodford (2003), (2.20) p. 265: **existence and uniqueness**: from every initial belief
`θ₀` there is exactly one solution of the linearised equation (2.20) with `θ(0) = θ₀`. -/
theorem existsUnique_isESol (J : Matrix ι ι ℝ) (θs x0 : ι → ℝ) :
    ∃! θ : ℝ → ι → ℝ, IsESol (linT J θs) θ ∧ θ 0 = x0 := by
  classical
  refine ⟨fun τ => θs + flow (J - 1) τ (x0 - θs), ⟨isESol_flow J θs x0, ?_⟩, ?_⟩
  · simp [flow_zero]
  · rintro θ ⟨hθ, h0⟩
    funext τ
    rw [eq_flow_of_isESol hθ τ, h0]

/-! ### E-stability ⇒ geometric decay of the flow -/

/-- Woodford (2003), (2.20): `exp(N A) = exp(A)ᴺ`. -/
theorem flow_nat (A : Matrix ι ι ℝ) (N : ℕ) : flow A N = flow A 1 ^ N := by
  induction N with
  | zero => simp [flow_zero]
  | succ N ih => rw [Nat.cast_succ, flow_add, ih, pow_succ]

/-- Woodford (2003), (2.20): the matrix of `exp(A)`. -/
noncomputable def kMat (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  LinearMap.toMatrix' (flow A 1 : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))

/-- Woodford (2003), (2.20): `kMat A x = exp(A) x`. -/
theorem kMat_mulVec (A : Matrix ι ι ℝ) (y : ι → ℝ) : kMat A *ᵥ y = flow A 1 y := by
  simp [kMat, LinearMap.toMatrix'_mulVec]

/-- Woodford (2003), (2.20): `kMat Aᴺ x = exp(A)ᴺ x`. -/
theorem kMat_pow_mulVec (A : Matrix ι ι ℝ) (N : ℕ) (y : ι → ℝ) :
    kMat A ^ N *ᵥ y = (flow A 1 ^ N) y := by
  induction N generalizing y with
  | zero => simp
  | succ N ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, kMat_mulVec, ih, pow_succ,
      mul_apply_eq_comp]

/-- Woodford (2003), (2.20): `gen Aⁿ x = Aⁿ x`. -/
theorem gen_pow_apply (A : Matrix ι ι ℝ) (n : ℕ) (y : ι → ℝ) : (gen A ^ n) y = A ^ n *ᵥ y := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_apply_eq_comp, ih, gen_apply, Matrix.mulVec_mulVec, pow_succ]

/-- Woodford (2003), (2.20): `A` commutes with `exp(A)`. -/
theorem commute_kMat (A : Matrix ι ι ℝ) : A * kMat A = kMat A * A := by
  have hc : Commute (gen A) (flow A 1) :=
    ((Commute.refl (gen A)).smul_right (1 : ℝ)).exp_right
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro y
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    kMat_mulVec, kMat_mulVec, ← gen_apply, ← gen_apply, ← mul_apply_eq_comp,
    hc.eq, mul_apply_eq_comp]

/-- Woodford (2003), (2.20): the entries of `exp(A)` are the sums `∑ₙ (Aⁿ)ᵢⱼ/n!`. -/
theorem hasSum_kMat (A : Matrix ι ι ℝ) (i j : ι) :
    HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ * (A ^ n) i j) (kMat A i j) := by
  have hS := exp_series_hasSum_exp' (𝕂 := ℝ) (gen A)
  have h := hS.mapL ((ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.apply ℝ (ι → ℝ) (Pi.single j 1)))
  convert h using 1
  · funext n
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.proj_apply, _root_.smul_apply, gen_pow_apply,
      Matrix.mulVec_single_one, Pi.smul_apply, smul_eq_mul, Matrix.col_apply]
  · simp [kMat, LinearMap.toMatrix'_apply, flow]

/-- Woodford (2003), App. C.7, p. 684: if `A v = μ v` (complex), then `exp(A) v = e^μ v`. -/
theorem kMat_map_mulVec_of_eig {A : Matrix ι ι ℝ} {μ : ℂ} {w : ι → ℂ}
    (hw : A.map Complex.ofReal *ᵥ w = μ • w) :
    (kMat A).map Complex.ofReal *ᵥ w = Complex.exp μ • w := by
  have hm : ∀ X Y : Matrix ι ι ℝ, (X * Y).map Complex.ofReal =
      X.map Complex.ofReal * Y.map Complex.ofReal := fun _ _ =>
    Matrix.map_mul (f := Complex.ofRealHom)
  have hpow : ∀ n : ℕ, (A ^ n).map Complex.ofReal *ᵥ w = μ ^ n • w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, hm, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul, ih,
        smul_smul, pow_succ, mul_comm]
  funext i
  have h1 : HasSum (fun n : ℕ => ∑ j, ((((n.factorial : ℝ)⁻¹ * (A ^ n) i j : ℝ) : ℂ) * w j))
      (((kMat A).map Complex.ofReal *ᵥ w) i) := by
    simp only [mulVec, dotProduct, Matrix.map_apply]
    exact hasSum_sum fun j _ =>
      ((Complex.ofRealCLM.hasSum (hasSum_kMat A i j)).mul_right (w j))
  have h2 : HasSum (fun n : ℕ => ∑ j, ((((n.factorial : ℝ)⁻¹ * (A ^ n) i j : ℝ) : ℂ) * w j))
      ((Complex.exp μ • w) i) := by
    have he := exp_series_hasSum_exp' (𝕂 := ℂ) μ
    rw [← Complex.exp_eq_exp_ℂ] at he
    convert he.mul_right (w i) using 1
    funext n
    have := congrFun (hpow n) i
    simp only [mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, mul_assoc,
      ← Finset.mul_sum, this, smul_eq_mul]
  exact h1.unique h2

/-- Woodford (2003), p. 266: **if `J` is E-stable, every eigenvalue of `exp(J − I)` lies
inside the unit circle**: an eigenvalue `ν` of `exp(J − I)` has an eigenspace invariant under
`J − I`, which contains an eigenvector `w` of `J − I` (eigenvalue `μ`, `Re μ < 0`); then
`ν w = exp(J − I) w = e^μ w`, so `|ν| = e^{Re μ} < 1`. -/
theorem norm_lt_one_of_isEig_kMat {J : Matrix ι ι ℝ} (hJ : EStable J) {ν : ℂ}
    (h : KroneckerSpectrum.IsEig ((kMat (J - 1)).map Complex.ofReal) ν) : ‖ν‖ < 1 := by
  set A := J - 1 with hA
  set Ac : Matrix ι ι ℂ := A.map Complex.ofReal with hAc
  set Kc : Matrix ι ι ℂ := (kMat A).map Complex.ofReal with hKc
  have hm : ∀ X Y : Matrix ι ι ℝ, (X * Y).map Complex.ofReal =
      X.map Complex.ofReal * Y.map Complex.ofReal := fun _ _ =>
    Matrix.map_mul (f := Complex.ofRealHom)
  have hcomm : Ac * Kc = Kc * Ac := by
    rw [hAc, hKc, ← hm, ← hm, commute_kMat]
  obtain ⟨v, hv0, hv⟩ := h
  set W : Submodule ℂ (ι → ℂ) := Module.End.eigenspace (Matrix.toLin' Kc) ν with hW
  have hmem : ∀ x, x ∈ W ↔ Kc *ᵥ x = ν • x := fun x => by
    rw [hW, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  have hWne : W ≠ ⊥ := (Submodule.ne_bot_iff W).mpr ⟨v, (hmem v).mpr hv, hv0⟩
  have hinv : ∀ x ∈ W, Matrix.toLin' Ac x ∈ W := by
    intro x hx
    rw [hmem, Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← hcomm, ← Matrix.mulVec_mulVec,
      (hmem x).mp hx, Matrix.mulVec_smul]
  obtain ⟨w, hwW, hw0, a, ha⟩ :=
    KroneckerSpectrum.exists_eigenvector_mem (Matrix.toLin' Ac) W hWne hinv
  rw [Matrix.toLin'_apply] at ha
  have hre : a.re < 0 := hJ a ⟨w, hw0, ha⟩
  have h1 := kMat_map_mulVec_of_eig ha
  rw [(hmem w).mp hwW] at h1
  have hνa : ν = Complex.exp a := by
    by_contra hne
    apply hw0
    have : (ν - Complex.exp a) • w = 0 := by rw [sub_smul, h1, sub_self]
    exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  rw [hνa, Complex.norm_exp]
  exact Real.exp_lt_one_iff.mpr hre

/-- Woodford (2003), p. 270: the entries of `Kᵏ` decay geometrically when every complex
eigenvalue of `K` lies inside the unit circle, for any finite index type (restated from
`BlanchardKahn.pow_entry_bound`, by reindexing to `Fin n`). -/
theorem pow_bound_fintype (K : Matrix ι ι ℝ)
    (hK : ∀ w, KroneckerSpectrum.IsEig (K.map Complex.ofReal) w → ‖w‖ < 1) :
    ∃ Cb ρ : ℝ, 0 ≤ Cb ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k := by
  set e := Fintype.equivFin ι with he
  set K' := Matrix.reindex e e K with hK'
  have hK'e : ∀ w : ℂ, (Matrix.scalar (Fin (Fintype.card ι)) w -
      K'.map Complex.ofReal).det = 0 → ‖w‖ < 1 := by
    intro w hw
    have hs : Matrix.scalar (Fin (Fintype.card ι)) w =
        w • (1 : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) := by
      ext a b
      by_cases hab : a = b <;> simp [hab, Matrix.scalar_apply]
    rw [hs, ← KroneckerSpectrum.isEig_iff_det] at hw
    obtain ⟨v, hv0, hv⟩ := hw
    refine hK w ⟨v ∘ e, fun h0 => hv0 ?_, ?_⟩
    · funext b
      have := congrFun h0 (e.symm b)
      simpa using this
    · funext i
      have := congrFun hv (e i)
      simp only [mulVec, dotProduct, Matrix.map_apply, hK', Matrix.reindex_apply,
        Matrix.submatrix_apply, Equiv.symm_apply_apply, Pi.smul_apply, smul_eq_mul] at this
      simp only [mulVec, dotProduct, Matrix.map_apply, Function.comp_apply, Pi.smul_apply,
        smul_eq_mul]
      rw [← this, ← Equiv.sum_comp e (fun b => (K i (e.symm b) : ℂ) * v b)]
      simp
  obtain ⟨Cb, ρ, h0, h1, h2, hb⟩ := BlanchardKahn.pow_entry_bound K' hK'e
  refine ⟨Cb, ρ, h0, h1, h2, fun k i j => ?_⟩
  have hp : K' ^ k = Matrix.reindex e e (K ^ k) := by
    rw [hK', ← Matrix.coe_reindexAlgEquiv ℝ ℝ e,
      map_pow]
  have := hb k (e i) (e j)
  rw [hp] at this
  simpa using this

/-- Woodford (2003), p. 266: **under E-stability the flow of (2.20) decays geometrically**:
`‖exp(τ (J − I)) x‖ ≤ M ρ^⌊τ⌋ ‖x‖` for `τ ≥ 0`, some `M ≥ 0` and `0 < ρ < 1`. -/
theorem flow_bound {J : Matrix ι ι ℝ} (hJ : EStable J) :
    ∃ M ρ : ℝ, 0 ≤ M ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ τ : ℝ, 0 ≤ τ → ∀ x, ‖flow (J - 1) τ x‖ ≤ M * ρ ^ ⌊τ⌋₊ * ‖x‖ := by
  set A := J - 1 with hA
  obtain ⟨Cb, ρ, hCb, hρ0, hρ1, hb⟩ :=
    pow_bound_fintype (kMat A) (fun w hw => norm_lt_one_of_isEig_kMat hJ hw)
  have hcont : Continuous (fun s : ℝ => flow A s) :=
    continuous_iff_continuousAt.2 fun s =>
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) (gen A) s).continuousAt
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 ⟨le_rfl, zero_le_one⟩)
  have hvec : ∀ (N : ℕ) (x : ι → ℝ),
      ‖kMat A ^ N *ᵥ x‖ ≤ Fintype.card ι * Cb * ρ ^ N * ‖x‖ := by
    intro N x
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    simp only [mulVec, dotProduct]
    calc |∑ j, (kMat A ^ N) i j * x j| ≤ ∑ j, |(kMat A ^ N) i j * x j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : ι, Cb * ρ ^ N * ‖x‖ := Finset.sum_le_sum fun j _ => by
          rw [abs_mul]
          exact mul_le_mul (hb N i j) (norm_le_pi_norm x j) (abs_nonneg _) (by positivity)
      _ = Fintype.card ι * Cb * ρ ^ N * ‖x‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  refine ⟨B * (Fintype.card ι * Cb), ρ, by positivity, hρ0, hρ1, fun τ hτ x => ?_⟩
  have hdec : flow A τ x = flow A (τ - ⌊τ⌋₊) (kMat A ^ ⌊τ⌋₊ *ᵥ x) := by
    rw [kMat_pow_mulVec, ← flow_nat, ← mul_apply_eq_comp, ← flow_add,
      sub_add_cancel]
  have hs : τ - ⌊τ⌋₊ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.2 (Nat.floor_le hτ), by linarith [Nat.lt_floor_add_one τ]⟩
  rw [hdec]
  calc ‖flow A (τ - ⌊τ⌋₊) (kMat A ^ ⌊τ⌋₊ *ᵥ x)‖
      ≤ ‖flow A (τ - ⌊τ⌋₊)‖ * ‖kMat A ^ ⌊τ⌋₊ *ᵥ x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ B * (Fintype.card ι * Cb * ρ ^ ⌊τ⌋₊ * ‖x‖) :=
        mul_le_mul (hB _ hs) (hvec _ _) (norm_nonneg _) hB0
    _ = B * (Fintype.card ι * Cb) * ρ ^ ⌊τ⌋₊ * ‖x‖ := by ring

/-- Woodford (2003), p. 266: under E-stability `exp(τ (J − I)) x → 0` as `τ → ∞`. -/
theorem tendsto_flow_of_eStable {J : Matrix ι ι ℝ} (hJ : EStable J) (x : ι → ℝ) :
    Tendsto (fun τ => flow (J - 1) τ x) atTop (𝓝 0) := by
  obtain ⟨M, ρ, hM, hρ0, hρ1, hb⟩ := flow_bound hJ
  have hlim : Tendsto (fun τ : ℝ => M * ρ ^ ⌊τ⌋₊ * ‖x‖) atTop (𝓝 0) := by
    have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).comp
      (tendsto_nat_floor_atTop (α := ℝ))
    have h2 := (h1.const_mul M).mul_const ‖x‖
    simpa using h2
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 0] with τ hτ
  exact hb τ hτ x

/-- Woodford (2003), p. 266: **E-stability implies convergence**: if every eigenvalue of
`J − I` has negative real part, every solution of the linearised equation (2.20) converges to
the rest point `θ̄`, from every initial belief. -/
theorem tendsto_of_eStable {J : Matrix ι ι ℝ} {θs : ι → ℝ} (hJ : EStable J)
    {θ : ℝ → ι → ℝ} (h : IsESol (linT J θs) θ) : Tendsto θ atTop (𝓝 θs) := by
  have := (tendsto_flow_of_eStable hJ (θ 0 - θs)).const_add θs
  rw [add_zero] at this
  exact this.congr fun τ => (eq_flow_of_isESol h τ).symm

/-! ### Convergence ⇒ E-stability -/

/-- Woodford (2003), p. 266: the real solution `θ̄ + Re(e^{τμ} v)` built from a complex
eigenpair `(μ, v)` of `J − I`. -/
noncomputable def eigSol (θs : ι → ℝ) (μ : ℂ) (v : ι → ℂ) (τ : ℝ) : ι → ℝ :=
  θs + fun i => (Complex.exp (τ * μ) * v i).re

/-- Woodford (2003), p. 266: if `(J − I) v = μ v` (complex), `θ̄ + Re(e^{τμ} v)` solves the
linearised equation (2.20). -/
theorem isESol_eigSol {J : Matrix ι ι ℝ} {θs : ι → ℝ} {μ : ℂ} {v : ι → ℂ}
    (hv : (J - 1).map Complex.ofReal *ᵥ v = μ • v) : IsESol (linT J θs) (eigSol θs μ v) := by
  intro τ
  rw [linT_sub]
  have hθ : eigSol θs μ v τ - θs = fun i => (Complex.exp (τ * μ) * v i).re := by
    simp [eigSol]
  rw [hθ]
  refine HasDerivAt.const_add θs (f := fun t : ℝ => fun i => (Complex.exp (t * μ) * v i).re) ?_
  refine hasDerivAt_pi.2 fun i => ?_
  have he : HasDerivAt (fun z : ℂ => Complex.exp (z * μ) * v i)
      (Complex.exp (↑τ * μ) * μ * v i) ↑τ := by
    have := (((hasDerivAt_id (τ : ℂ)).mul_const μ).cexp).mul_const (v i)
    simpa using this
  have hr := he.real_of_complex
  convert hr using 1
  have hi := congrFun hv i
  simp only [mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at hi
  simp only [mulVec, dotProduct]
  rw [show Complex.exp (↑τ * μ) * μ * v i =
      Complex.exp (↑τ * μ) * ∑ j, (((J - 1) i j : ℝ) : ℂ) * v j by rw [hi]; ring,
    Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_left_comm, Complex.re_ofReal_mul]

/-- Woodford (2003), p. 266: **convergence implies E-stability**: if every solution of the
linearised equation (2.20) converges to `θ̄`, every eigenvalue of `J − I` has negative real
part (no genericity assumption: eigenvalues with zero real part are covered, cf. n. 37). -/
theorem eStable_of_tendsto {J : Matrix ι ι ℝ} {θs : ι → ℝ}
    (h : ∀ θ, IsESol (linT J θs) θ → Tendsto θ atTop (𝓝 θs)) : EStable J := by
  intro μ hμ
  by_contra hre
  push Not at hre
  obtain ⟨v, hv0, hv⟩ := hμ
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
  have hv' : (J - 1).map Complex.ofReal *ᵥ (Complex.I • v) = μ • (Complex.I • v) := by
    rw [Matrix.mulVec_smul, hv, smul_comm]
  have comp : ∀ w : ι → ℂ, (J - 1).map Complex.ofReal *ᵥ w = μ • w →
      Tendsto (fun τ : ℝ => (Complex.exp (τ * μ) * w i).re) atTop (𝓝 0) := by
    intro w hw
    have t := (tendsto_pi_nhds.1 (h _ (isESol_eigSol (θs := θs) hw))) i
    have t2 := t.sub_const (θs i)
    simpa [eigSol] using t2
  have c1 := comp v hv
  have c2 := comp _ hv'
  have c2' : Tendsto (fun τ : ℝ => (Complex.exp (τ * μ) * v i).im) atTop (𝓝 0) := by
    have := c2.neg
    rw [neg_zero] at this
    refine this.congr fun τ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im]
    ring
  have c3 : Tendsto (fun τ : ℝ => ‖Complex.exp (τ * μ) * v i‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => norm_nonneg _)
      (fun τ => Complex.norm_le_abs_re_add_abs_im _) ?_
    simpa using c1.abs.add c2'.abs
  have hpos : 0 < ‖v i‖ := norm_pos_iff.2 hi
  obtain ⟨τ, h1, h2⟩ := ((c3.eventually (gt_mem_nhds hpos)).and (eventually_ge_atTop 0)).exists
  have hge : ‖v i‖ ≤ ‖Complex.exp (τ * μ) * v i‖ := by
    rw [norm_mul, Complex.norm_exp]
    have : (↑τ * μ).re = τ * μ.re := by simp
    rw [this]
    exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (mul_nonneg h2 hre))
  linarith

/-- Woodford (2003), p. 266: **E-stability (eigenvalues of `DT − I`) iff every solution of the
linearised E-stability equation (2.20) converges to the rest point**, from every initial
belief. -/
theorem eStable_iff_tendsto (J : Matrix ι ι ℝ) (θs : ι → ℝ) :
    EStable J ↔ ∀ θ, IsESol (linT J θs) θ → Tendsto θ atTop (𝓝 θs) :=
  ⟨fun hJ _ h => tendsto_of_eStable hJ h, eStable_of_tendsto⟩

/-! ### The book's definition: a locally stable rest point -/

/-- Woodford (2003), p. 264: `θ̄` is a **locally stable rest point** of `θ̇ = T(θ) − θ`:
solutions starting close stay close (Lyapunov stability) and solutions starting close enough
converge to `θ̄`. -/
def IsLocallyStable (T : (ι → ℝ) → ι → ℝ) (θs : ι → ℝ) : Prop :=
  (∀ ε > 0, ∃ δ > 0, ∀ θ, IsESol T θ → ‖θ 0 - θs‖ < δ → ∀ τ : ℝ, 0 ≤ τ → ‖θ τ - θs‖ < ε) ∧
    ∃ δ > 0, ∀ θ, IsESol T θ → ‖θ 0 - θs‖ < δ → Tendsto θ atTop (𝓝 θs)

omit [DecidableEq ι] in
/-- Woodford (2003), (2.20): solutions of the linearised equation scale about `θ̄`. -/
theorem isESol_scale {J : Matrix ι ι ℝ} {θs : ι → ℝ} {θ : ℝ → ι → ℝ}
    (h : IsESol (linT J θs) θ) (c : ℝ) :
    IsESol (linT J θs) (fun τ => θs + c • (θ τ - θs)) := by
  classical
  intro τ
  have h1 := (((h τ).sub_const θs).const_smul c).const_add θs
  convert h1 using 1
  rw [linT_sub, linT_sub, add_sub_cancel_left, Matrix.mulVec_smul]

/-- Woodford (2003), pp. 264–266 and n. 37: **for the linear(ised) map the book's definition
(a locally stable rest point of (2.20)) and the eigenvalue definition coincide**, with no
genericity assumption. -/
theorem eStable_iff_locallyStable (J : Matrix ι ι ℝ) (θs : ι → ℝ) :
    EStable J ↔ IsLocallyStable (linT J θs) θs := by
  constructor
  · intro hJ
    refine ⟨fun ε hε => ?_, ⟨1, one_pos, fun θ h _ => tendsto_of_eStable hJ h⟩⟩
    obtain ⟨M, ρ, hM, hρ0, hρ1, hb⟩ := flow_bound hJ
    refine ⟨ε / (M + 1), by positivity, fun θ h h0 τ hτ => ?_⟩
    have e := eq_flow_of_isESol h τ
    rw [e, add_sub_cancel_left]
    calc ‖flow (J - 1) τ (θ 0 - θs)‖ ≤ M * ρ ^ ⌊τ⌋₊ * ‖θ 0 - θs‖ := hb τ hτ _
      _ ≤ M * ‖θ 0 - θs‖ := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _)
            (pow_le_one₀ hρ0.le hρ1.le)) hM
      _ ≤ (M + 1) * ‖θ 0 - θs‖ := by nlinarith [norm_nonneg (θ 0 - θs)]
      _ < (M + 1) * (ε / (M + 1)) := by
          exact mul_lt_mul_of_pos_left h0 (by linarith)
      _ = ε := by field_simp
  · rintro ⟨-, δ, hδ, hconv⟩
    refine eStable_of_tendsto (θs := θs) fun θ h => ?_
    set c : ℝ := δ / (2 * (‖θ 0 - θs‖ + 1)) with hc
    have hc0 : 0 < c := by positivity
    have hsol := isESol_scale h c
    have hsmall : ‖(θs + c • (θ 0 - θs)) - θs‖ < δ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc0, hc]
      have hn := norm_nonneg (θ 0 - θs)
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    have t := hconv _ hsol hsmall
    have t2 := (t.sub_const θs).const_smul c⁻¹
    simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc0.ne', one_smul,
      sub_self, smul_zero] at t2
    simpa using t2.const_add θs

/-! ### Fixed points of a differentiable `T`-map; affine `T`-maps -/

/-- Woodford (2003), p. 266: **`EStableAt T θ̄` iff `θ̄` is a fixed point at which `T` is
differentiable and every solution of the equation (2.20) linearised at `θ̄`
(`θ̇ = DT(θ̄)(θ − θ̄) − (θ − θ̄)`) converges to `θ̄`**. -/
theorem eStableAt_iff_ode (T : (ι → ℝ) → ι → ℝ) (θs : ι → ℝ) :
    EStableAt T θs ↔ T θs = θs ∧ DifferentiableAt ℝ T θs ∧
      ∀ θ, IsESol (linT (LinearMap.toMatrix' (fderiv ℝ T θs : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))) θs) θ →
        Tendsto θ atTop (𝓝 θs) := by
  unfold EStableAt
  rw [eStable_iff_tendsto _ θs]

omit [DecidableEq ι] in
/-- Woodford (2003), p. 266: an affine `T(θ) = c + M θ` with rest point `θ̄` is the map
`θ̄ + M (θ − θ̄)`, so its linearisation is exact. -/
theorem linT_eq_of_affine {T : (ι → ℝ) → ι → ℝ} {c : ι → ℝ} {M : Matrix ι ι ℝ}
    (hT : ∀ y, T y = c + M *ᵥ y) {θs : ι → ℝ} (hfix : T θs = θs) : T = linT M θs := by
  funext y
  have h1 := hT θs
  rw [hfix] at h1
  rw [hT, linT, Matrix.mulVec_sub]
  linear_combination -h1

/-- Woodford (2003), (2.20) and p. 266, for an affine `T`-map (Propositions 4.8, 4.9): **`M` is
E-stable iff every solution of the actual equation `θ̇ = T(θ) − θ` converges to the rest
point**, from every initial belief (global convergence). -/
theorem eStable_iff_tendsto_affine {T : (ι → ℝ) → ι → ℝ} {c : ι → ℝ} {M : Matrix ι ι ℝ}
    (hT : ∀ y, T y = c + M *ᵥ y) {θs : ι → ℝ} (hfix : T θs = θs) :
    EStable M ↔ ∀ θ, IsESol T θ → Tendsto θ atTop (𝓝 θs) := by
  rw [linT_eq_of_affine hT hfix]
  exact eStable_iff_tendsto M θs

/-- Woodford (2003), pp. 264–266, for an affine `T`-map: `M` is E-stable iff the rest point is
a locally stable rest point of the actual equation (2.20) (the book's definition). -/
theorem eStable_iff_locallyStable_affine {T : (ι → ℝ) → ι → ℝ} {c : ι → ℝ} {M : Matrix ι ι ℝ}
    (hT : ∀ y, T y = c + M *ᵥ y) {θs : ι → ℝ} (hfix : T θs = θs) :
    EStable M ↔ IsLocallyStable T θs := by
  rw [linT_eq_of_affine hT hfix]
  exact eStable_iff_locallyStable M θs

end Woodford.NeoWicksellianFramework.TidyR5EStabilityODE
