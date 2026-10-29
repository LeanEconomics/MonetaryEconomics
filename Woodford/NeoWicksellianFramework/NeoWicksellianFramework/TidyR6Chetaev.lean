/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.TidyR5Lyapunov
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# A Chetaev function for the E-stability equation (2.20)

Woodford (2003), *Interest and Prices*, Chapter 4, §2.3, pp. 264–266: the local stability of a
rest point `θ̄` of `θ̇ = T(θ) − θ` (2.20) "depends on the eigenvalues of the Jacobian matrix
`DT(θ̄) − I`". The module TidyR5Lyapunov proves the stability half. This module supplies the
quadratic function behind the instability half (an eigenvalue with positive real part).

* `isEig_iff_isRoot`, `finite_eigs`: the eigenvalues of a square matrix are the roots of its
  characteristic polynomial, a finite set.
* `sylvester_eq_zero` (the Kronecker-sum spectrum): if no two eigenvalues `λ, ν` of `B` satisfy
  `λ + ν = 0`, then `BᵀX + XB = 0` forces `X = 0`. Proof by Cayley–Hamilton: `BᵀX = X(−B)`
  gives `p(Bᵀ)X = X p(−B)` for every polynomial `p`; with `p` the characteristic polynomial of
  `B`, `p(Bᵀ) = 0`, and `p(−B)` is invertible by the spectral mapping theorem.
* `exists_sylvester`: under the same condition `BᵀP + PB = I` has a symmetric solution.
* `exists_pos_of_sylvester`: if moreover `B` has an eigenvalue with positive real part, the
  quadratic form `x′Px` takes a positive value (along the decaying real solution
  `Re(e^{−τν} w)` of `ẋ = −Bx`, `x′Px` is non-increasing with derivative `−x′x` and tends to `0`).
* `exists_chetaev`: if `A = DT − I` has an eigenvalue `μ` with `Re μ > 0`, there are `σ > 0` and a
  symmetric `P` with `AᵀP + PA = 2σP + I` and `e′Pe > 0` for some `e` (shift `B = A − σI`, with
  `σ ∈ (0, Re μ)` avoiding the finitely many half-sums of real parts of eigenvalues).
* **`escape_of_unstable`**: if `T(θ̄) = θ̄`, `T` is differentiable at `θ̄` and `DT(θ̄) − I` has
  an eigenvalue with positive real part, there is `ρ > 0` such that arbitrarily close to `θ̄` there
  are initial beliefs from which every forward solution of (2.20) reaches distance `ρ` from `θ̄`.
  Along a solution that stayed within `ρ`, `V = (θ − θ̄)′P(θ − θ̄)` would satisfy
  `V̇ ≥ 2σV + ‖θ − θ̄‖²/2`, so `V ≥ (V(0)/2) e^{2στ}` (a lower barrier,
  `image_le_of_deriv_right_lt_deriv_boundary`), contradicting `V ≤ K ρ²`.
-/

namespace Woodford.NeoWicksellianFramework.TidyR6Chetaev

open Matrix Filter Topology TidyR5EStabilityODE TidyR5Lyapunov
open KroneckerSpectrum (IsEig)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Eigenvalues -/

/-- Woodford (2003), p. 266: `k` is an eigenvalue of `M` iff it is a root of the characteristic
polynomial of `M`. -/
theorem isEig_iff_isRoot (M : Matrix ι ι ℂ) (k : ℂ) : IsEig M k ↔ M.charpoly.IsRoot k := by
  rw [KroneckerSpectrum.isEig_iff_det, Polynomial.IsRoot.def, Matrix.eval_charpoly,
    Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

omit [DecidableEq ι] in
/-- Woodford (2003), p. 266: a square matrix has finitely many eigenvalues. -/
theorem finite_eigs (M : Matrix ι ι ℂ) : {k | IsEig M k}.Finite := by
  classical
  exact (Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic M).ne_zero).subset
    fun k hk => (isEig_iff_isRoot M k).1 hk

omit [DecidableEq ι] in
/-- Woodford (2003), p. 266: `k` is an eigenvalue of `−M` iff `−k` is an eigenvalue of `M`. -/
theorem isEig_neg_iff (M : Matrix ι ι ℂ) (k : ℂ) : IsEig (-M) k ↔ IsEig M (-k) := by
  unfold IsEig
  refine exists_congr fun v => and_congr_right fun _ => ?_
  rw [Matrix.neg_mulVec, neg_smul, neg_eq_iff_eq_neg]

/-- Woodford (2003), p. 266: `k` is an eigenvalue of `A − σI` iff `k + σ` is an eigenvalue of
`A`. -/
theorem isEig_shift_iff (A : Matrix ι ι ℝ) (σ : ℝ) (k : ℂ) :
    IsEig ((A - σ • 1).map Complex.ofReal) k ↔ IsEig (A.map Complex.ofReal) (k + σ) := by
  have hm : (A - σ • 1).map Complex.ofReal = A.map Complex.ofReal - (σ : ℂ) • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  unfold IsEig
  refine exists_congr fun v => and_congr_right fun _ => ?_
  rw [hm, sub_mulVec, smul_mulVec, one_mulVec, sub_eq_iff_eq_add, add_smul]

/-! ### The Kronecker-sum (Sylvester) equation -/

omit [DecidableEq ι] in
/-- Woodford (2003), p. 266 (cf. the Kronecker-sum spectrum, App. C.7): if no two eigenvalues of
`B` sum to zero, `BᵀX + XB = 0` only for `X = 0`. -/
theorem sylvester_eq_zero {B X : Matrix ι ι ℝ}
    (hB : ∀ l ν : ℂ, IsEig (B.map Complex.ofReal) l → IsEig (B.map Complex.ofReal) ν →
      l + ν ≠ 0)
    (hX : Bᵀ * X + X * B = 0) : X = 0 := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact Subsingleton.elim _ _
  set Bc := B.map Complex.ofReal with hBc
  set Xc := X.map Complex.ofReal with hXc
  have h1 : Bcᵀ * Xc + Xc * Bc = 0 := by
    ext i j
    have := congrFun (congrFun hX i) j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.zero_apply] at this ⊢
    simp only [hBc, hXc, Matrix.map_apply]
    exact_mod_cast this
  have h2 : Bcᵀ * Xc = Xc * (-Bc) := by
    rw [Matrix.mul_neg, eq_neg_iff_add_eq_zero, h1]
  have hpow : ∀ n : ℕ, Bcᵀ ^ n * Xc = Xc * (-Bc) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_assoc, h2, ← mul_assoc, ih, mul_assoc, ← pow_succ]
  have hpoly : ∀ p : Polynomial ℂ,
      Polynomial.aeval Bcᵀ p * Xc = Xc * Polynomial.aeval (-Bc) p := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, map_add, add_mul, mul_add, hp, hq]
    | monomial n a =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, mul_assoc, hpow, ← mul_assoc,
        Algebra.commutes, mul_assoc]
  set p := Bc.charpoly with hp
  have hz : Polynomial.aeval Bcᵀ p = 0 := by
    rw [hp, ← Matrix.charpoly_transpose]
    exact Matrix.aeval_self_charpoly _
  have hunit : IsUnit (Polynomial.aeval (-Bc) p) := by
    by_contra hnu
    have h0 : (0 : ℂ) ∈ spectrum ℂ (Polynomial.aeval (-Bc) p) := (spectrum.zero_mem_iff ℂ).mpr hnu
    rw [spectrum.map_polynomial_aeval_of_nonempty _ _
      (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ _)] at h0
    obtain ⟨k, hk, hk0⟩ := h0
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, ← isEig_iff_isRoot, isEig_neg_iff] at hk
    have hk' : IsEig Bc k := (isEig_iff_isRoot Bc k).2 hk0
    exact hB k (-k) hk' hk (add_neg_cancel k)
  have hXc0 : Xc = 0 := by
    have := hpoly p
    rw [hz, zero_mul] at this
    exact (hunit.mul_left_eq_zero).mp this.symm
  ext i j
  have := congrFun (congrFun hXc0 i) j
  simpa [hXc] using this

/-- Woodford (2003), p. 266: if no two eigenvalues of `B` sum to zero, the equation
`BᵀP + PB = I` has a symmetric solution `P`. -/
theorem exists_sylvester {B : Matrix ι ι ℝ}
    (hB : ∀ l ν : ℂ, IsEig (B.map Complex.ofReal) l → IsEig (B.map Complex.ofReal) ν →
      l + ν ≠ 0) :
    ∃ P : Matrix ι ι ℝ, Pᵀ = P ∧ Bᵀ * P + P * B = 1 := by
  set L : Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ :=
    LinearMap.mulLeft ℝ Bᵀ + LinearMap.mulRight ℝ B with hL
  have hLapp : ∀ X, L X = Bᵀ * X + X * B := fun X => rfl
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX
    rw [hLapp] at hX
    exact sylvester_eq_zero hB hX
  obtain ⟨P, hP⟩ := (LinearMap.injective_iff_surjective.mp hinj) 1
  rw [hLapp] at hP
  refine ⟨P, ?_, hP⟩
  apply hinj
  rw [hLapp, hLapp, hP]
  have := congrArg Matrix.transpose hP
  rw [transpose_add, transpose_mul, transpose_mul, transpose_transpose, transpose_one] at this
  rw [← this, add_comm]

/-- Woodford (2003), p. 266: if `BᵀP + PB = I` and `B` has an eigenvalue with positive real part,
the quadratic form `x′Px` takes a positive value. -/
theorem exists_pos_of_sylvester {B P : Matrix ι ι ℝ} (hP : Bᵀ * P + P * B = 1) {ν : ℂ}
    (hν : IsEig (B.map Complex.ofReal) ν) (hre : 0 < ν.re) : ∃ e : ι → ℝ, 0 < e ⬝ᵥ (P *ᵥ e) := by
  obtain ⟨w, hw0, hw⟩ := hν
  obtain ⟨w', hw'r, hw'⟩ : ∃ w' : ι → ℂ, (fun i => (w' i).re) ≠ 0 ∧
      B.map Complex.ofReal *ᵥ w' = ν • w' := by
    by_cases h : (fun i => (w i).re) = 0
    · refine ⟨Complex.I • w, ?_, by rw [mulVec_smul, hw, smul_comm]⟩
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hw0
      have hre0 : (w i).re = 0 := congrFun h i
      intro h2
      have him : (Complex.I * w i).re = 0 := congrFun h2 i
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
        zero_sub, neg_eq_zero] at him
      exact hi (Complex.ext hre0 him)
    · exact ⟨w, h, hw⟩
  by_contra hneg
  push Not at hneg
  set y : ℝ → ι → ℝ := eigSol (0 : ι → ℝ) (-ν) w' with hy
  have hyv : ((1 - B) - 1).map Complex.ofReal *ᵥ w' = (-ν) • w' := by
    have : (1 - B) - 1 = -B := by abel
    have hneg : (-B).map Complex.ofReal = -(B.map Complex.ofReal) := by
      ext i j
      simp
    rw [this, hneg, Matrix.neg_mulVec, hw', neg_smul]
  have hysol := isESol_eigSol (θs := (0 : ι → ℝ)) hyv
  have hyd : ∀ t, HasDerivAt y (-B *ᵥ y t) t := by
    intro t
    have h1 := hysol t
    rw [linT_sub, sub_zero, show (1 - B) - 1 = -B by abel] at h1
    exact h1
  set g : ℝ → ℝ := fun t => y t ⬝ᵥ (P *ᵥ y t) with hg
  have hgd : ∀ t, HasDerivAt g (-(y t ⬝ᵥ y t)) t := by
    intro t
    have h := hasDerivWithinAt_bilin P (s := Set.univ) (hyd t).hasDerivWithinAt
      (hyd t).hasDerivWithinAt
    rw [hasDerivWithinAt_univ, dot_mulVec_add, transpose_neg, Matrix.neg_mul, Matrix.mul_neg,
      ← neg_add, hP, neg_mulVec, one_mulVec, dotProduct_neg] at h
    exact h
  have hanti : Antitone g := antitone_of_deriv_nonpos (fun t => (hgd t).differentiableAt)
    fun t => by
      rw [(hgd t).deriv]
      exact neg_nonpos.2 (le_trans (sq_nonneg ‖y t‖) (norm_sq_le_dot (y t)))
  have hlimy : Tendsto y atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro i
    have he : Tendsto (fun t : ℝ => Real.exp (-(ν.re * t)) * ‖w' i‖) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hre)).mul_const ‖w' i‖
      simpa [Function.comp_def] using this
    refine squeeze_zero_norm (fun t => ?_) he
    simp only [hy, eigSol, Pi.add_apply, Pi.zero_apply, zero_add]
    calc ‖(Complex.exp (↑t * -ν) * w' i).re‖ ≤ ‖Complex.exp (↑t * -ν) * w' i‖ := by
          rw [Real.norm_eq_abs]
          exact Complex.abs_re_le_norm _
      _ = Real.exp (-(ν.re * t)) * ‖w' i‖ := by
          rw [norm_mul, Complex.norm_exp]
          congr 2
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.neg_re, Complex.ofReal_im,
            Complex.neg_im, zero_mul, sub_zero]
          ring
  have hlimg : Tendsto g atTop (𝓝 0) := by
    have := ((continuous_quad P).tendsto 0).comp hlimy
    simpa [Function.comp_def] using this
  have hg0 : ∀ t, g t = 0 := fun t => le_antisymm (hneg _) (hanti.le_of_tendsto hlimg t)
  have hdd : y 0 ⬝ᵥ y 0 = 0 := by
    have h1 := (hgd 0).deriv
    have h2 : deriv g 0 = 0 := by
      rw [show g = fun _ => (0 : ℝ) from funext hg0]
      simp
    linarith
  have hy0 : y 0 = fun i => (w' i).re := by
    funext i
    simp [hy, eigSol]
  apply hw'r
  rw [← hy0]
  by_contra hne
  exact (dot_self_pos hne).ne' hdd

/-- Woodford (2003), pp. 264–266: **the Chetaev matrix**: if `A` (here `DT − I`) has an
eigenvalue with positive real part, there are `σ > 0` and a symmetric `P` with
`AᵀP + PA = 2σP + I` such that `x′Px` takes a positive value. -/
theorem exists_chetaev {A : Matrix ι ι ℝ} {μ : ℂ} (hμ : IsEig (A.map Complex.ofReal) μ)
    (hre : 0 < μ.re) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ P : Matrix ι ι ℝ, Pᵀ = P ∧ Aᵀ * P + P * A = (2 * σ) • P + 1 ∧
      ∃ e : ι → ℝ, 0 < e ⬝ᵥ (P *ᵥ e) := by
  set Ac := A.map Complex.ofReal with hAc
  have hfin := finite_eigs Ac
  set S : Set ℝ := (fun p : ℂ × ℂ => (p.1.re + p.2.re) / 2) ''
    ({k | IsEig Ac k} ×ˢ {k | IsEig Ac k}) with hS
  have hSfin : S.Finite := (hfin.prod hfin).image _
  obtain ⟨σ, hσI, hσS⟩ := ((Set.Ioo_infinite hre).sdiff hSfin).nonempty
  set B := A - σ • 1 with hBdef
  have hB : ∀ l ν : ℂ, IsEig (B.map Complex.ofReal) l → IsEig (B.map Complex.ofReal) ν →
      l + ν ≠ 0 := by
    intro l ν hl hν hsum
    apply hσS
    refine ⟨(l + σ, ν + σ), ⟨(isEig_shift_iff A σ l).1 hl, (isEig_shift_iff A σ ν).1 hν⟩, ?_⟩
    have := congrArg Complex.re hsum
    simp only [Complex.add_re, Complex.zero_re] at this
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  obtain ⟨P, hPs, hP⟩ := exists_sylvester hB
  have hμB : IsEig (B.map Complex.ofReal) (μ - σ) := (isEig_shift_iff A σ _).2 (by simpa using hμ)
  obtain ⟨e, he⟩ := exists_pos_of_sylvester hP hμB (by simp; linarith [hσI.2])
  refine ⟨σ, hσI.1, P, hPs, ?_, e, he⟩
  have hA : A = B + σ • 1 := by rw [hBdef, sub_add_cancel]
  rw [hA, transpose_add, add_mul, mul_add, ← add_add_add_comm, hP, transpose_smul,
    transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, two_mul,
    add_smul]
  abel

/-! ### Escape from a neighbourhood of an unstable rest point -/

/-- Woodford (2003), pp. 264–266: **escape from an unstable rest point**: if `T(θ̄) = θ̄`, `T` is
differentiable at `θ̄` and `DT(θ̄) − I` has an eigenvalue with positive real part, there is
`ρ > 0` such that within every distance `δ > 0` of `θ̄` there is an initial belief from which
every forward solution of (2.20) reaches distance `ρ` from `θ̄`. -/
theorem escape_of_unstable {T : (ι → ℝ) → ι → ℝ} {θs : ι → ℝ} (hfix : T θs = θs)
    (hd : DifferentiableAt ℝ T θs) {μ : ℂ}
    (hμ : IsEig ((LinearMap.toMatrix' (fderiv ℝ T θs : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) - 1).map
      Complex.ofReal) μ) (hre : 0 < μ.re) :
    ∃ ρ > 0, ∀ δ > 0, ∃ x0 : ι → ℝ, ‖x0 - θs‖ < δ ∧
      ∀ θ, IsFwdSol T θ → θ 0 = x0 → ∃ τ : ℝ, 0 ≤ τ ∧ ρ ≤ ‖θ τ - θs‖ := by
  set J := LinearMap.toMatrix' (fderiv ℝ T θs : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) with hJdef
  obtain ⟨σ, hσ, P, -, hP, e, he⟩ := exists_chetaev hμ hre
  set K := ∑ i, ∑ j, |P i j| with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  set η := 1 / (4 * (K + 1)) with hη
  have hηpos : 0 < η := by positivity
  have hKη : K * η ≤ 1 / 4 := by
    rw [hη, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hJapp : ∀ y, J *ᵥ y = fderiv ℝ T θs y := fun y => by
    rw [hJdef, LinearMap.toMatrix'_mulVec]
    rfl
  obtain ⟨ρ0, hρ0, hrem⟩ := Metric.eventually_nhds_iff.mp
    (hd.hasFDerivAt.isLittleO.def hηpos)
  -- the derivative of `V` along the vector field
  have hD : ∀ y, ‖y - θs‖ < ρ0 →
      2 * σ * ((y - θs) ⬝ᵥ (P *ᵥ (y - θs))) + ‖y - θs‖ ^ 2 / 2 ≤
        (T y - y) ⬝ᵥ (P *ᵥ (y - θs)) + (y - θs) ⬝ᵥ (P *ᵥ (T y - y)) := by
    intro y hy
    set x := y - θs with hx
    set r := T y - θs - J *ᵥ x with hr
    have hF : T y - y = (J - 1) *ᵥ x + r := by
      rw [hr, hx, sub_mulVec, one_mulVec]
      abel
    have hrb : ‖r‖ ≤ η * ‖x‖ := by
      have := hrem (y := y) (by rwa [dist_eq_norm])
      rw [hfix] at this
      rw [hr, hJapp]
      exact this
    rw [hF, add_dotProduct, mulVec_add, dotProduct_add]
    have hq : ((J - 1) *ᵥ x) ⬝ᵥ (P *ᵥ x) + x ⬝ᵥ (P *ᵥ ((J - 1) *ᵥ x)) =
        2 * σ * (x ⬝ᵥ (P *ᵥ x)) + x ⬝ᵥ x := by
      rw [dot_mulVec_add, hP, add_mulVec, smul_mulVec, one_mulVec, dotProduct_add,
        dotProduct_smul, smul_eq_mul]
    have hb1 : |r ⬝ᵥ (P *ᵥ x)| ≤ K * ‖r‖ * ‖x‖ := bilin_bound P r x
    have hb2 : |x ⬝ᵥ (P *ᵥ r)| ≤ K * ‖x‖ * ‖r‖ := bilin_bound P x r
    have h1 : K * ‖r‖ * ‖x‖ ≤ ‖x‖ ^ 2 / 4 := by
      have : K * ‖r‖ * ‖x‖ ≤ K * (η * ‖x‖) * ‖x‖ := by
        have := mul_le_mul_of_nonneg_left hrb hK0
        exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
      have h' : K * (η * ‖x‖) * ‖x‖ = (K * η) * ‖x‖ ^ 2 := by ring
      nlinarith [sq_nonneg ‖x‖]
    have h3 := norm_sq_le_dot x
    have h4 := neg_abs_le (r ⬝ᵥ (P *ᵥ x))
    have h5 := neg_abs_le (x ⬝ᵥ (P *ᵥ r))
    have h6 : K * ‖x‖ * ‖r‖ = K * ‖r‖ * ‖x‖ := by ring
    linarith
  refine ⟨ρ0, hρ0, fun δ hδ => ?_⟩
  set c := δ / (2 * (‖e‖ + 1)) with hc
  have hc0 : 0 < c := by positivity
  refine ⟨θs + c • e, ?_, fun θ hθ h0 => ?_⟩
  · rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc0, hc]
    have hn := norm_nonneg e
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  by_contra hcon
  push Not at hcon
  obtain ⟨hcont, hder⟩ := hθ
  set V : ℝ → ℝ := fun s => (θ s - θs) ⬝ᵥ (P *ᵥ (θ s - θs)) with hV
  have hV0 : V 0 = c ^ 2 * (e ⬝ᵥ (P *ᵥ e)) := by
    simp only [hV, h0, add_sub_cancel_left, mulVec_smul, dotProduct_smul, smul_dotProduct,
      smul_eq_mul]
    ring
  have hV0pos : 0 < V 0 := by rw [hV0]; positivity
  -- the lower barrier `V(t) ≥ (V(0)/2) e^{2σt}`
  have hbar : ∀ t, 0 ≤ t → V 0 / 2 * Real.exp (2 * σ * t) ≤ V t := by
    intro t ht
    have hVc : ContinuousOn (fun s => -V s) (Set.Icc 0 t) :=
      ((continuous_quad P).comp_continuousOn
        ((hcont.mono Set.Icc_subset_Ici_self).sub continuousOn_const)).neg
    have hVd : ∀ s ∈ Set.Ico (0 : ℝ) t, HasDerivWithinAt (fun s => -V s)
        (-((T (θ s) - θ s) ⬝ᵥ (P *ᵥ (θ s - θs)) + (θ s - θs) ⬝ᵥ (P *ᵥ (T (θ s) - θ s))))
        (Set.Ici s) s := by
      intro s hs
      have hs' := (hder s hs.1).sub_const θs
      exact (hasDerivWithinAt_bilin P hs' hs').neg
    have hB : ∀ s, HasDerivAt (fun s => -(V 0 / 2 * Real.exp (2 * σ * s)))
        (-(V 0 / 2 * (Real.exp (2 * σ * s) * (2 * σ * 1)))) s := fun s =>
      ((((hasDerivAt_id s).const_mul (2 * σ)).exp).const_mul (V 0 / 2)).neg
    have hV0B : -V 0 ≤ -(V 0 / 2 * Real.exp (2 * σ * 0)) := by
      simp only [mul_zero, Real.exp_zero, mul_one]
      linarith
    have := image_le_of_deriv_right_lt_deriv_boundary hVc hVd hV0B hB ?_ ⟨ht, le_rfl⟩
    · linarith
    intro s hs hcontact
    have hVs : V s = V 0 / 2 * Real.exp (2 * σ * s) := by linarith
    have hpos : 0 < V s := by rw [hVs]; positivity
    have hx0 : θ s - θs ≠ 0 := by
      intro h
      rw [hV] at hpos
      simp only [h, mulVec_zero, dotProduct_zero, lt_irrefl] at hpos
    have hn : 0 < ‖θ s - θs‖ := norm_pos_iff.mpr hx0
    have hDs := hD (θ s) (hcon s hs.1)
    have : V s = (θ s - θs) ⬝ᵥ (P *ᵥ (θ s - θs)) := rfl
    nlinarith [sq_pos_of_pos hn]
  -- but `V` stays bounded by `K ρ0²`
  set t := (K * ρ0 ^ 2 + 1) / (σ * V 0) with ht
  have ht0 : 0 ≤ t := by positivity
  have hup : V t ≤ K * ρ0 ^ 2 := by
    have h1 := bilin_bound P (θ t - θs) (θ t - θs)
    have h2 := hcon t ht0
    have h3 : V t ≤ K * ‖θ t - θs‖ * ‖θ t - θs‖ := (le_abs_self _).trans h1
    have h4 : ‖θ t - θs‖ * ‖θ t - θs‖ ≤ ρ0 ^ 2 := by
      rw [sq]
      exact mul_le_mul h2.le h2.le (norm_nonneg _) hρ0.le
    calc V t ≤ K * ‖θ t - θs‖ * ‖θ t - θs‖ := h3
      _ = K * (‖θ t - θs‖ * ‖θ t - θs‖) := by ring
      _ ≤ K * ρ0 ^ 2 := mul_le_mul_of_nonneg_left h4 hK0
  have hlow := hbar t ht0
  have hexp : 2 * σ * t + 1 ≤ Real.exp (2 * σ * t) := Real.add_one_le_exp _
  have hσt : σ * V 0 * t = K * ρ0 ^ 2 + 1 := by
    rw [ht]
    field_simp
  nlinarith

end Woodford.NeoWicksellianFramework.TidyR6Chetaev
