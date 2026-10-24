/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.Determinacy2
import NeoWicksellianFramework.KroneckerSpectrum
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# E-stability under sample-mean learning (Proposition 4.8)

Woodford (2003), *Interest and Prices*, Chapter 4, §2.3, pp. 262–269.

Under the Bullard–Mitra temporary-equilibrium relations (2.16)–(2.17) and the Taylor rule
(1.14), outcomes are `z = z̄ + B (Ê z′ − z̄) + b e` (2.18), and beliefs `zᵉ` about the mean are
mapped to the correct mean by the T-map `T(zᵉ) = z̄ + B (zᵉ − z̄)` (2.19), with `DT = B`.
E-stability is defined, as in the book (p. 266), by the eigenvalues of `DT − I = B − I` having
negative real parts.

## Main results

* `temporary_eqm_iff` (2.18): the temporary equilibrium for arbitrary subjective expectations;
  `taylorB_eq_inv`, `taylorA_mul_taylorB` show `B` is the inverse of the (C.19) matrix, and
  `A25_mul_taylorB_eq_one_iff`, `e18_B_ne_inv_A25` that it is NOT the inverse of the (2.5)
  matrix unless `φ_π = φ_x = 0` (survey E18, confirmed).
* `sampleMean_succ` (2.21), `tau_succ`, `tendsto_tau` (the rescaled time of (2.22)).
* The T-map `Tmap` (2.19) for any number of variables, `hasFDerivAt_Tmap` (`DT = B`), its fixed
  points (`Tmap_fixed_iff_one_sub`, `Tmap_fixed_unique`). E-stability in general (`EStable`,
  `EStableAt`, `eStable_iff`: every eigenvalue of `DT` has real part `< 1`;
  `eStableAt_affine_iff`); for `2 × 2` matrices `isEig_two_iff`, `routh2`, `eStable_iff_routh`:
  E-stability iff `tr(B − I) < 0 < det(B − I)`.
* `isEig_inv2`: the eigenvalues of `B = A⁻¹` are the reciprocals of those of `A`.
* **Proposition 4.8** (`prop_4_8`): E-stable iff (2.7).
* Survey E22 (`taylorB_pos_re_eig`, `e22_counterexample`, `exists_real_eig_gt_one`,
  `exists_real_eig_ge_one`, `e22_corrected_iff`): `B` ALWAYS has an eigenvalue with positive
  real part, so "positive real part" cannot be the failure condition; when (2.7) fails `B` has
  a real eigenvalue `≥ 1` (`> 1` when it fails strictly).
* Iterative E-stability (2.23) iff `|eig B| < 1` iff determinacy (`iterEStable_iff`,
  `taylor_iterEStable_iff`); determinacy implies E-stability (`schurStable_imp_eStable`).
* Fn. 35 and p. 268: the s.c.e. is unique iff (2.7) is not an equality (`sce_unique`); at
  equality there is a line of s.c.e. (`sce_line`) and the `π̇ᵉ = 0` and `ẋᵉ = 0` loci coincide
  (`loci_coincide`); otherwise they meet only at `z̄` (`loci_meet_once`). Fns. 38–39
  (`fn38_vertical`, `fn39_vertical`; the sign statements of the footnotes, on the whole positive
  orthant, are `Learning.BullardMitra.piDot_pos` and `xDot_neg`).
-/

namespace Woodford.NeoWicksellianFramework.Determinacy2Learning

open Filter Topology Woodford.NeoWicksellianFramework.Determinacy2 BlanchardKahn
open BasicModel (xbar)
open scoped Matrix

/-! ### The temporary equilibrium (2.16)–(2.18) -/

/-- Woodford (2003), eqs. (2.16)–(2.18), pp. 263: for ANY subjective expectations
`Ê π′ = P`, `Ê x′ = X` (not necessarily rational), the relations (2.16), (2.17) and the rule
(1.14) give `z − z̄ = B (Ê z′ − z̄) + b (r̂ⁿ − ī + π̄)` with `z̄ = (π̄, x̄)` and the matrix `B` of
`taylorB` (the inverse of the (C.19) matrix, `taylorB_eq_inv`). -/
theorem temporary_eqm_iff {β σ κ φπ φx πbar : ℝ} (hκ : κ ≠ 0)
    (hΔ : taylorDelta σ κ φπ φx ≠ 0) {p x P X rn ib : ℝ} :
    (x = X - σ * (ib + φπ * (p - πbar) + φx / 4 * (x - xbar β κ πbar) - P - rn) ∧
        p = κ * x + β * P) ↔
      ![p, x] = ![πbar, xbar β κ πbar] + (taylorB β σ κ φπ φx).mulVec
        (![P, X] - ![πbar, xbar β κ πbar]) + (rn - ib + πbar) • taylorb σ κ φπ φx := by
  rw [taylor_pt (kappa_mul_xbar hκ πbar) hΔ rfl]
  have c0 : (![πbar, xbar β κ πbar] + (taylorB β σ κ φπ φx).mulVec
      (![P, X] - ![πbar, xbar β κ πbar]) + (rn - ib + πbar) • taylorb σ κ φπ φx) 0 =
      πbar + (taylorB β σ κ φπ φx 0 0 * (P - πbar) + taylorB β σ κ φπ φx 0 1 *
        (X - xbar β κ πbar)) + (rn - ib + πbar) * taylorb σ κ φπ φx 0 := by
    simp [Matrix.vecHead, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have c1 : (![πbar, xbar β κ πbar] + (taylorB β σ κ φπ φx).mulVec
      (![P, X] - ![πbar, xbar β κ πbar]) + (rn - ib + πbar) • taylorb σ κ φπ φx) 1 =
      xbar β κ πbar + (taylorB β σ κ φπ φx 1 0 * (P - πbar) + taylorB β σ κ φπ φx 1 1 *
        (X - xbar β κ πbar)) + (rn - ib + πbar) * taylorb σ κ φπ φx 1 := by
    simp [Matrix.vecHead, Matrix.vecTail, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  constructor
  · rintro ⟨h1, h2⟩
    ext i
    fin_cases i
    · rw [Fin.zero_eta, c0]
      simp only [Matrix.cons_val_zero]
      linarith
    · rw [Fin.mk_one, c1]
      simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
      linarith
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    rw [c0] at h0
    rw [c1] at h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h0 h1
    exact ⟨by linarith, by linarith⟩

/-- Woodford (2003), p. 263 (corrected, survey E18): `B` is the inverse of the matrix `A` of
(C.19): `A B = I`. -/
theorem taylorA_mul_taylorB {β σ κ φπ φx : ℝ} (hβ : β ≠ 0) (hΔ : taylorDelta σ κ φπ φx ≠ 0) :
    taylorA β σ κ φπ φx * taylorB β σ κ φπ φx = 1 := by
  rw [taylorB_eq_inv hβ]
  exact mul_inv2 (by rw [taylorA_det_eq]; exact div_ne_zero hΔ hβ)

/-- Woodford (2003), p. 263: `B A = I` as well. -/
theorem taylorB_mul_taylorA {β σ κ φπ φx : ℝ} (hβ : β ≠ 0) (hΔ : taylorDelta σ κ φπ φx ≠ 0) :
    taylorB β σ κ φπ φx * taylorA β σ κ φπ φx = 1 := by
  rw [taylorB_eq_inv hβ]
  exact inv2_mul (by rw [taylorA_det_eq]; exact div_ne_zero hΔ hβ)

/-- Woodford (2003), p. 263 (survey E18): `B` is the inverse of the matrix of (2.5) only when the
rule has no feedback at all; for any rule with `φ_π ≠ 0` or `φ_x ≠ 0` the printed claim
"`B` is just the inverse of the matrix `A` in (2.5)" fails. -/
theorem A25_mul_taylorB_eq_one_iff {β σ κ φπ φx : ℝ} (hβ : β ≠ 0) (hσ : σ ≠ 0)
    (hΔ : taylorDelta σ κ φπ φx ≠ 0) :
    A25 β σ κ * taylorB β σ κ φπ φx = 1 ↔ φπ = 0 ∧ φx = 0 := by
  constructor
  · intro h
    have hdiff : taylorA β σ κ φπ φx - A25 β σ κ = !![0, 0; σ * φπ, σ * φx / 4] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [taylorA, A25] <;> ring
    have h0 : (taylorA β σ κ φπ φx - A25 β σ κ) * taylorB β σ κ φπ φx = 0 := by
      rw [Matrix.sub_mul, h, taylorA_mul_taylorB hβ hΔ, sub_self]
    have h1 : taylorA β σ κ φπ φx - A25 β σ κ = 0 := by
      have := congrArg (· * taylorA β σ κ φπ φx) h0
      simpa [Matrix.mul_assoc, taylorB_mul_taylorA hβ hΔ] using this
    rw [hdiff] at h1
    have e0 : σ * φπ = 0 := congrFun (congrFun h1 1) 0
    have e1 : σ * φx / 4 = 0 := congrFun (congrFun h1 1) 1
    refine ⟨(mul_eq_zero.mp e0).resolve_left hσ, ?_⟩
    have e2 : σ * φx = 0 := by linarith
    exact (mul_eq_zero.mp e2).resolve_left hσ
  · rintro ⟨rfl, rfl⟩
    rw [A25_eq_taylorA]
    exact taylorA_mul_taylorB hβ hΔ

/-- Woodford (2003), p. 263 and p. 266, survey E18 (confirmed): the text says `B` is the inverse
of the matrix `A` of (2.5). That is true only for `φ_π = φ_x = 0`: for any rule with `φ_π > 0`
or `φ_x > 0`, `B` is not the inverse of the (2.5) matrix (`A25_mul_taylorB_eq_one_iff`); it is
the inverse of the (C.19) matrix instead (`taylorB_eq_inv`). -/
theorem e18_B_ne_inv_A25 {β σ κ φπ φx : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ)
    (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (h : 0 < φπ ∨ 0 < φx) :
    taylorB β σ κ φπ φx ≠ inv2 (A25 β σ κ) ∧ taylorB β σ κ 0 0 = inv2 (A25 β σ κ) := by
  refine ⟨fun hB => ?_, by rw [A25_eq_taylorA, taylorB_eq_inv hβ.ne']⟩
  have hd : det2 (A25 β σ κ) ≠ 0 := by
    rw [(A25_tr_det β σ κ 0).2.1 hβ.ne']; positivity
  have hΔ := one_le_taylorDelta hσ hκ hφπ hφx
  have h1 : A25 β σ κ * taylorB β σ κ φπ φx = 1 := by rw [hB, mul_inv2 hd]
  obtain ⟨e0, e1⟩ := (A25_mul_taylorB_eq_one_iff hβ.ne' hσ.ne' (by linarith)).mp h1
  rcases h with h | h <;> linarith

/-! ### Sample-mean learning (2.21)–(2.22) -/

/-- Woodford (2003), p. 265: the sample mean `zᵉ_t = t⁻¹ ∑_{k<t} z_k` of past observations
(componentwise). -/
noncomputable def sampleMean (z : ℕ → ℝ) (t : ℕ) : ℝ := (t : ℝ)⁻¹ * ∑ k ∈ Finset.range t, z k

/-- Woodford (2003), eq. (2.21), p. 265: `zᵉ_{t+1} − zᵉ_t = (t + 1)⁻¹ (z_t − zᵉ_t)` (valid at
`t = 0` too, with `zᵉ_0 = 0`). -/
theorem sampleMean_succ (z : ℕ → ℝ) (t : ℕ) :
    sampleMean z (t + 1) - sampleMean z t = ((t : ℝ) + 1)⁻¹ * (z t - sampleMean z t) := by
  unfold sampleMean
  rw [Finset.sum_range_succ]
  push_cast
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  · have : (t : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-- Woodford (2003), eq. (2.22), p. 265 (mean dynamics): if the outcome equals its mean
`T(zᵉ_t)` then `(zᵉ_{t+1} − zᵉ_t)/(τ_{t+1} − τ_t) = T(zᵉ_t) − zᵉ_t`, the step `τ_{t+1} − τ_t`
being `1/(t + 1)`. -/
theorem mean_dynamics (z : ℕ → ℝ) (Tz : ℝ) (t : ℕ) (hz : z t = Tz) :
    (sampleMean z (t + 1) - sampleMean z t) / ((t : ℝ) + 1)⁻¹ = Tz - sampleMean z t := by
  rw [sampleMean_succ, hz]
  field_simp

/-- Woodford (2003), p. 265: the rescaled time `τ_t = ∑_{k=1}^t 1/k`. -/
noncomputable def tau (t : ℕ) : ℝ := ∑ k ∈ Finset.range t, (1 / ((k : ℝ) + 1))

/-- Woodford (2003), p. 265: `τ_{t+1} − τ_t = 1/(t + 1)`, so the increments vanish. -/
theorem tau_succ (t : ℕ) : tau (t + 1) - tau t = 1 / ((t : ℝ) + 1) := by
  unfold tau
  rw [Finset.sum_range_succ]
  ring

/-- Woodford (2003), p. 265: `τ_t → ∞` (the harmonic series diverges), so the mean dynamics
(2.22) approximate the ODE (2.20) on an unbounded time scale. -/
theorem tendsto_tau : Tendsto tau atTop atTop :=
  Real.tendsto_sum_range_one_div_nat_succ_atTop

/-! ### The T-map (2.19) and E-stability -/

/-- Woodford (2003), eq. (2.19), p. 264: the T-map `T(zᵉ) = z̄ + B (zᵉ − z̄)`, sending beliefs
about the mean of `z` to the mean actually generated. -/
def Tmap {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ) (zbar ze : ι → ℝ) : ι → ℝ :=
  zbar + B.mulVec (ze - zbar)

/-- Woodford (2003), p. 266: "the mapping `T` is linear, and its derivative `DT` is simply the
matrix `B`". -/
theorem hasFDerivAt_Tmap {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ) (zbar z : ι → ℝ) :
    HasFDerivAt (Tmap B zbar) (LinearMap.toContinuousLinearMap (Matrix.mulVecLin B)) z := by
  have e : Tmap B zbar = fun w => (zbar - B.mulVec zbar) +
      LinearMap.toContinuousLinearMap (Matrix.mulVecLin B) w := by
    funext w
    simp only [Tmap, Matrix.mulVec_sub, LinearMap.coe_toContinuousLinearMap',
      Matrix.mulVecLin_apply]
    abel
  rw [e]
  exact (ContinuousLinearMap.hasFDerivAt _).const_add _

/-- Woodford (2003), p. 264: `z̄` is always a fixed point of `T` (a self-consistent
equilibrium). -/
theorem Tmap_zbar {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ) (zbar : ι → ℝ) :
    Tmap B zbar zbar = zbar := by
  simp [Tmap]

/-- Woodford (2003), p. 264: `zᵉ` is self-consistent (`T(zᵉ) = zᵉ`) iff
`(I − B)(zᵉ − z̄) = 0`. -/
theorem Tmap_fixed_iff_one_sub {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℝ)
    (zbar ze : ι → ℝ) : Tmap B zbar ze = ze ↔ (1 - B) *ᵥ (ze - zbar) = 0 := by
  rw [Tmap, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero, sub_eq_iff_eq_add', eq_comm]

/-- Woodford (2003), p. 264 and footnote 35: when `B` has no eigenvalue equal to one
(`det (I − B) ≠ 0`), the unique s.c.e. is `zᵉ = z̄`. -/
theorem Tmap_fixed_unique {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℝ)
    (zbar : ι → ℝ) (hB : (1 - B).det ≠ 0) (ze : ι → ℝ) : Tmap B zbar ze = ze ↔ ze = zbar := by
  rw [Tmap_fixed_iff_one_sub]
  constructor
  · intro h
    exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hB h)
  · intro h; rw [h, sub_self, Matrix.mulVec_zero]

/-- Woodford (2003), (2.20) p. 265 and p. 266: a self-consistent equilibrium with Jacobian `DT`
is **E-stable** when every (complex) eigenvalue of `DT − I` has negative real part. This is the
book's definition (p. 266, App. C.7 p. 684): it is the condition for local asymptotic stability
of the linear ODE `ż = (DT − I)(z − z̄)` that linearises `ż = T(z) − z`. -/
def EStable {ι : Type*} [Fintype ι] [DecidableEq ι] (DT : Matrix ι ι ℝ) : Prop :=
  ∀ ν : ℂ, KroneckerSpectrum.IsEig ((DT - 1).map Complex.ofReal) ν → ν.re < 0

/-- Woodford (2003), p. 269: `ν` is an eigenvalue of `DT − I` iff `ν + 1` is an eigenvalue of
`DT`. -/
theorem isEig_sub_one_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (ν : ℂ) :
    KroneckerSpectrum.IsEig ((M - 1).map Complex.ofReal) ν ↔
      KroneckerSpectrum.IsEig (M.map Complex.ofReal) (ν + 1) := by
  rw [KroneckerSpectrum.isEig_iff_det, KroneckerSpectrum.isEig_iff_det]
  have h : (M - 1).map Complex.ofReal = M.map Complex.ofReal - 1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [h, add_smul, one_smul]
  congr! 2
  abel

/-- Woodford (2003), p. 269: E-stability means every eigenvalue of `DT` has real part less
than one ("both eigenvalues of `B` have a real part less than 1"). -/
theorem eStable_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) :
    EStable M ↔ ∀ μ : ℂ, KroneckerSpectrum.IsEig (M.map Complex.ofReal) μ → μ.re < 1 := by
  constructor
  · intro h μ hμ
    have := h (μ - 1) ((isEig_sub_one_iff M _).mpr (by simpa using hμ))
    simpa using this
  · intro h ν hν
    have := h (ν + 1) ((isEig_sub_one_iff M ν).mp hν)
    simp only [Complex.add_re, Complex.one_re] at this
    linarith

/-- Woodford (2003), p. 266: E-stability of a rest point `x̄` of `ẋ = T(x) − x` for a map `T`
differentiable at `x̄`, defined through the matrix of the Fréchet derivative `DT(x̄)`. -/
def EStableAt {ι : Type*} [Fintype ι] [DecidableEq ι] (T : (ι → ℝ) → (ι → ℝ))
    (xbar : ι → ℝ) : Prop :=
  T xbar = xbar ∧ DifferentiableAt ℝ T xbar ∧
    EStable (LinearMap.toMatrix' (fderiv ℝ T xbar : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)))

/-- Woodford (2003), p. 266 ("the mapping `T` is linear, and its derivative `DT` is simply the
matrix `B`"): an affine map `T(x) = c + M x` has Fréchet derivative `M` everywhere. -/
theorem hasFDerivAt_affine {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ)
    (M : Matrix ι ι ℝ) (x : ι → ℝ) :
    HasFDerivAt (fun y => c + M *ᵥ y) (LinearMap.toContinuousLinearMap (Matrix.toLin' M)) x := by
  have h := (LinearMap.toContinuousLinearMap (Matrix.toLin' M)).hasFDerivAt (x := x)
  have h2 := h.const_add c
  convert h2 using 1
  funext y
  simp [Matrix.toLin'_apply]

/-- Woodford (2003), p. 266: for an affine `T(x) = c + M x`, a fixed point `x̄` is E-stable iff
the constant matrix `M` is (the Jacobian is the same at every point). -/
theorem eStableAt_affine_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ)
    (M : Matrix ι ι ℝ) (xbar : ι → ℝ) (hfix : c + M *ᵥ xbar = xbar) :
    EStableAt (fun y => c + M *ᵥ y) xbar ↔ EStable M := by
  have hd := hasFDerivAt_affine c M xbar
  unfold EStableAt
  rw [hd.fderiv]
  simp only [LinearMap.coe_toContinuousLinearMap, LinearMap.toMatrix'_toLin']
  exact ⟨fun h => h.2.2, fun h => ⟨hfix, hd.differentiableAt, h⟩⟩

/-- Woodford (2003), p. 266: `μ` is an eigenvalue of a real `2 × 2` matrix iff it is a root of
the characteristic polynomial `μ² − (tr M) μ + det M`. -/
theorem isEig_two_iff (M : Matrix (Fin 2) (Fin 2) ℝ) (μ : ℂ) :
    KroneckerSpectrum.IsEig (M.map Complex.ofReal) μ ↔
      μ ^ 2 - (tr2 M : ℂ) * μ + (det2 M : ℂ) = 0 := by
  have key : (μ • (1 : Matrix (Fin 2) (Fin 2) ℂ) - M.map Complex.ofReal).det =
      μ ^ 2 - (tr2 M : ℂ) * μ + (det2 M : ℂ) := by
    rw [Matrix.det_fin_two]
    simp [tr2, det2]
    ring
  rw [KroneckerSpectrum.isEig_iff_det, key]

/-- Woodford (2003), p. 269: if the characteristic polynomial `z² − T z + D` is non-positive at
`z = 1`, the matrix has a real eigenvalue `μ ≥ 1` (the larger root). -/
theorem exists_real_root_ge_one {T D : ℝ} (h : 1 - T + D ≤ 0) :
    ∃ μ : ℝ, 1 ≤ μ ∧ μ ^ 2 - T * μ + D = 0 := by
  have hdisc : 0 ≤ T ^ 2 - 4 * D := by nlinarith [sq_nonneg (1 - D), sq_nonneg (T - 1 - D)]
  set s := Real.sqrt (T ^ 2 - 4 * D) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = T ^ 2 - 4 * D := Real.sq_sqrt hdisc
  refine ⟨(T + s) / 2, ?_, by nlinarith⟩
  by_cases hT : 2 ≤ T
  · linarith
  · have h2 : (2 - T) ^ 2 ≤ s ^ 2 := by nlinarith
    have : 2 - T ≤ s := by
      by_contra hlt
      push Not at hlt
      nlinarith
    linarith

/-- Woodford (2003), p. 269: if the characteristic polynomial is negative at `z = 1`, the
larger real root exceeds one ("one eigenvalue is real and greater than 1"). -/
theorem exists_real_root_gt_one {T D : ℝ} (h : 1 - T + D < 0) :
    ∃ μ : ℝ, 1 < μ ∧ μ ^ 2 - T * μ + D = 0 := by
  obtain ⟨μ, hμ1, hμ⟩ := exists_real_root_ge_one h.le
  refine ⟨μ, lt_of_le_of_ne hμ1 fun h1 => ?_, hμ⟩
  rw [← h1] at hμ
  linarith

/-- Woodford (2003), p. 266 (tool): `tr(B − I) = tr B − 2`. -/
theorem tr2_sub_one (B : Matrix (Fin 2) (Fin 2) ℝ) : tr2 (B - 1) = tr2 B - 2 := by
  simp [tr2]; ring

/-- Woodford (2003), p. 266 (tool): `det(B − I) = 1 − tr B + det B`. -/
theorem det2_sub_one (B : Matrix (Fin 2) (Fin 2) ℝ) : det2 (B - 1) = det2 B - tr2 B + 1 := by
  simp [det2, tr2]; ring

/-- Woodford (2003), App. C.1 (tool): the real parts of the two roots of `z² − T z + D`. -/
theorem re_roots (T D : ℝ) :
    (root₁ T D).re = (if 0 ≤ disc T D then (T + Real.sqrt (disc T D)) / 2 else T / 2) ∧
      (root₂ T D).re = (if 0 ≤ disc T D then (T - Real.sqrt (disc T D)) / 2 else T / 2) := by
  unfold root₁ root₂
  constructor <;> split_ifs <;> simp

/-- Woodford (2003), p. 266, fn. 37 (Routh–Hurwitz for real quadratics): both roots of
`z² − T z + D` have negative real part iff `T < 0` and `D > 0`. -/
theorem routh2 (T D : ℝ) :
    (∀ w : ℂ, w ^ 2 - (T : ℂ) * w + (D : ℂ) = 0 → w.re < 0) ↔ (T < 0 ∧ 0 < D) := by
  obtain ⟨r1, r2⟩ := re_roots T D
  have hdisc : disc T D = T ^ 2 - 4 * D := rfl
  constructor
  · intro h
    have h1 := h _ (root_eq T D _ (Or.inl rfl))
    have h2 := h _ (root_eq T D _ (Or.inr rfl))
    rw [r1] at h1
    rw [r2] at h2
    split_ifs at h1 h2 with hd
    · have hs := Real.sq_sqrt hd
      have hs0 := Real.sqrt_nonneg (disc T D)
      refine ⟨by linarith, ?_⟩
      nlinarith
    · push Not at hd
      refine ⟨by linarith, ?_⟩
      nlinarith [sq_nonneg T]
  · rintro ⟨hT, hD⟩ w hw
    rcases eq_root_of_eq hw with rfl | rfl
    · rw [r1]
      split_ifs with hd
      · have hs := Real.sq_sqrt hd
        have hs0 := Real.sqrt_nonneg (disc T D)
        nlinarith
      · linarith
    · rw [r2]
      split_ifs with hd
      · have hs0 := Real.sqrt_nonneg (disc T D)
        linarith
      · linarith

/-- Woodford (2003), p. 266: for `2 × 2` matrices, E-stability iff `tr(B − I) < 0` and
`det(B − I) > 0`. -/
theorem eStable_iff_routh (B : Matrix (Fin 2) (Fin 2) ℝ) :
    EStable B ↔ (tr2 B - 2 < 0 ∧ 0 < det2 B - tr2 B + 1) := by
  unfold EStable
  simp only [isEig_two_iff]
  rw [tr2_sub_one, det2_sub_one]
  exact routh2 _ _

/-- Woodford (2003), p. 266: the eigenvalues of `B = A⁻¹` are the inverses of those of `A`. -/
theorem isEig_inv2 {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : det2 A ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    KroneckerSpectrum.IsEig (A.map Complex.ofReal) w ↔
      KroneckerSpectrum.IsEig ((inv2 A).map Complex.ofReal) w⁻¹ := by
  rw [isEig_two_iff, isEig_two_iff, tr2_inv2, det2_inv2]
  have hA' : (det2 A : ℂ) ≠ 0 := by exact_mod_cast hA
  push_cast
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    field_simp at h
    linear_combination h

/-- Woodford (2003), p. 269: if both eigenvalues of `B` lie inside the unit circle
(determinacy), their real parts are less than one (E-stability). -/
theorem schurStable_imp_eStable {B : Matrix (Fin 2) (Fin 2) ℝ}
    (h : SchurStable (tr2 B) (det2 B)) : EStable B := by
  rw [eStable_iff]
  intro w hw
  obtain ⟨h1, h2⟩ := (schurStable_iff_roots _ _).mp h
  have hn : ‖w‖ < 1 := by
    rcases eq_root_of_eq ((isEig_two_iff _ _).mp hw) with rfl | rfl
    · exact h1
    · exact h2
  exact (Complex.re_le_norm w).trans_lt hn

/-! ### Proposition 4.8 -/

/-- **Proposition 4.8** (Woodford (2003), p. 266): with the Bullard–Mitra temporary equilibrium,
a rule (1.14) with `φ_π, φ_x ≥ 0`, and sample-mean forecasts, the s.c.e. `(π̄, x̄)` is E-stable
iff (2.7) holds (the Taylor principle). -/
theorem prop_4_8 {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ)
    (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    EStable (taylorB β σ κ φπ φx) ↔ 1 < taylorLHS β κ φπ φx := by
  have hΔ := one_le_taylorDelta hσ hκ hφπ hφx
  have hΔ0 : taylorDelta σ κ φπ φx ≠ 0 := by linarith
  have e := taylorB_one_sub (β := β) (φπ := φπ) (φx := φx) hκ.ne' hΔ0
  have hd := taylorB_det (β := β) hΔ0
  rw [eStable_iff_routh, e]
  have hc : 0 < σ * κ := mul_pos hσ hκ
  constructor
  · rintro ⟨-, h⟩
    have := div_pos_iff.mp h
    rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
    · have := (pos_iff_pos_of_mul_pos h1).mp hc
      linarith
    · linarith
  · intro h
    have hpos : 0 < σ * κ * (taylorLHS β κ φπ φx - 1) / taylorDelta σ κ φπ φx :=
      div_pos (mul_pos hc (by linarith)) (by linarith)
    refine ⟨?_, hpos⟩
    have hdet : det2 (taylorB β σ κ φπ φx) < 1 := by
      rw [hd, div_lt_one (by linarith)]
      linarith
    rw [← e] at hpos
    linarith

/-- Woodford (2003), p. 267: with no feedback at all (`φ_π = φ_x = 0`, Friedman's case) the
s.c.e. is not E-stable. -/
theorem friedman_not_eStable {β σ κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) : ¬ EStable (taylorB β σ κ 0 0) := by
  rw [prop_4_8 hβ0 hβ1 hσ hκ le_rfl le_rfl]
  simp [taylorLHS]

/-! ### Survey E22: "positive real part" should be "real part greater than one" -/

/-- Woodford (2003), p. 266, survey E22: for EVERY admissible rule `B` has an eigenvalue with
positive real part (the real parts sum to `tr B > 0`). -/
theorem taylorB_pos_re_eig {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ)
    (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    ∃ w : ℂ, KroneckerSpectrum.IsEig ((taylorB β σ κ φπ φx).map Complex.ofReal) w ∧
      0 < w.re := by
  have hΔ := one_le_taylorDelta hσ hκ hφπ hφx
  have hT : 0 < tr2 (taylorB β σ κ φπ φx) := by
    rw [taylorB_tr]
    exact div_pos (by positivity) (by linarith)
  have hs := congrArg Complex.re (root_sum (tr2 (taylorB β σ κ φπ φx))
    (det2 (taylorB β σ κ φπ φx)))
  rw [Complex.add_re, Complex.ofReal_re] at hs
  by_cases h1 : 0 < (root₁ (tr2 (taylorB β σ κ φπ φx)) (det2 (taylorB β σ κ φπ φx))).re
  · exact ⟨_, (isEig_two_iff _ _).mpr (root_eq _ _ _ (Or.inl rfl)), h1⟩
  · exact ⟨_, (isEig_two_iff _ _).mpr (root_eq _ _ _ (Or.inr rfl)), by linarith⟩

/-- Woodford (2003), p. 266, survey E22 (counterexample to the printed wording): whenever (2.7)
holds, the s.c.e. is E-stable and yet `B` has an eigenvalue with positive real part. -/
theorem e22_counterexample {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (h : 1 < taylorLHS β κ φπ φx) :
    EStable (taylorB β σ κ φπ φx) ∧
      ∃ w : ℂ, KroneckerSpectrum.IsEig ((taylorB β σ κ φπ φx).map Complex.ofReal) w ∧
        0 < w.re :=
  ⟨(prop_4_8 hβ0 hβ1 hσ hκ hφπ hφx).mpr h, taylorB_pos_re_eig hβ0 hσ hκ hφπ hφx⟩

/-- Woodford (2003), p. 269: when the Taylor principle fails, `B` has a real eigenvalue `μ ≥ 1`
(at equality in (2.7) the eigenvalue is exactly one). -/
theorem exists_real_eig_ge_one {β σ κ φπ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hφπ : 0 ≤ φπ)
    (hφx : 0 ≤ φx) (hT : ¬ 1 < taylorLHS β κ φπ φx) :
    ∃ μ : ℝ, 1 ≤ μ ∧ KroneckerSpectrum.IsEig ((taylorB β σ κ φπ φx).map Complex.ofReal) μ := by
  have hΔ := one_le_taylorDelta hσ hκ hφπ hφx
  have hkey := taylorB_one_sub (β := β) (φπ := φπ) (φx := φx) hκ.ne'
    (by linarith : taylorDelta σ κ φπ φx ≠ 0)
  have hle : 1 - tr2 (taylorB β σ κ φπ φx) + det2 (taylorB β σ κ φπ φx) ≤ 0 := by
    have : σ * κ * (taylorLHS β κ φπ φx - 1) / taylorDelta σ κ φπ φx ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith [not_lt.mp hT]))
        (by linarith)
    linarith
  obtain ⟨μ, hμ1, hμ⟩ := exists_real_root_ge_one hle
  exact ⟨μ, hμ1, (isEig_two_iff _ _).mpr (by exact_mod_cast hμ)⟩

/-- Woodford (2003), pp. 266 and 269 ("when the Taylor principle is not satisfied, one eigenvalue
is real and greater than 1"), corrected E22: when (2.7) fails strictly, `B` has a REAL eigenvalue
greater than one (so both its modulus and its real part exceed one). -/
theorem exists_real_eig_gt_one {β σ κ φπ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hφπ : 0 ≤ φπ)
    (hφx : 0 ≤ φx) (hT : taylorLHS β κ φπ φx < 1) :
    ∃ μ : ℝ, 1 < μ ∧ KroneckerSpectrum.IsEig ((taylorB β σ κ φπ φx).map Complex.ofReal) μ := by
  have hΔ := one_le_taylorDelta hσ hκ hφπ hφx
  have hkey := taylorB_one_sub (β := β) (φπ := φπ) (φx := φx) hκ.ne'
    (by linarith : taylorDelta σ κ φπ φx ≠ 0)
  have hlt : 1 - tr2 (taylorB β σ κ φπ φx) + det2 (taylorB β σ κ φπ φx) < 0 := by
    have : σ * κ * (taylorLHS β κ φπ φx - 1) / taylorDelta σ κ φπ φx < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) (by linarith))
        (by linarith)
    linarith
  obtain ⟨μ, hμ1, hμ⟩ := exists_real_root_gt_one hlt
  exact ⟨μ, hμ1, (isEig_two_iff _ _).mpr (by exact_mod_cast hμ)⟩

/-- Woodford (2003), fn. 35, p. 264, and p. 268: when (2.7) holds with equality, `1` is an
eigenvalue of `B`. -/
theorem eig_one_at_equality {β σ κ φπ φx : ℝ} (hκ : κ ≠ 0) (hΔ : taylorDelta σ κ φπ φx ≠ 0)
    (h : taylorLHS β κ φπ φx = 1) :
    KroneckerSpectrum.IsEig ((taylorB β σ κ φπ φx).map Complex.ofReal) 1 := by
  rw [isEig_two_iff]
  have e := taylorB_one_sub (β := β) hκ hΔ
  rw [h, sub_self, mul_zero, zero_div] at e
  have : (1 : ℝ) ^ 2 - tr2 (taylorB β σ κ φπ φx) * 1 + det2 (taylorB β σ κ φπ φx) = 0 := by
    linarith
  exact_mod_cast this

/-- Woodford (2003), p. 266 and p. 269, corrected (E22): (2.7) fails iff `B` has an eigenvalue
with real part at least one (a real eigenvalue `> 1` when it fails strictly, the eigenvalue `1`
at equality). -/
theorem e22_corrected_iff {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    ¬ 1 < taylorLHS β κ φπ φx ↔
      ∃ w : ℂ, KroneckerSpectrum.IsEig ((taylorB β σ κ φπ φx).map Complex.ofReal) w ∧
        1 ≤ w.re := by
  constructor
  · intro h
    obtain ⟨μ, hμ1, hμ⟩ := exists_real_eig_ge_one hσ hκ hφπ hφx h
    exact ⟨μ, hμ, by simpa using hμ1⟩
  · rintro ⟨w, hw, h1⟩ h
    have := ((eStable_iff _).mp ((prop_4_8 hβ0 hβ1 hσ hκ hφπ hφx).mpr h)) w hw
    linarith

/-! ### Iterative E-stability (2.23) -/

/-- Woodford (2003), eq. (2.23), p. 269: iterating the T-map, `Tᵏ(zᵉ) = z̄ + Bᵏ (zᵉ − z̄)`. -/
theorem Tmap_iterate (B : Matrix (Fin 2) (Fin 2) ℝ) (zbar ze : Fin 2 → ℝ) (k : ℕ) :
    (Tmap B zbar)^[k] ze = zbar + (B ^ k).mulVec (ze - zbar) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Tmap, add_sub_cancel_left, Matrix.mulVec_mulVec,
      ← pow_succ']

/-- Woodford (2003), p. 269: the s.c.e. `z̄` is iteratively E-stable if the iterates (2.23)
converge to `z̄` from every initial belief. -/
def IterEStable (B : Matrix (Fin 2) (Fin 2) ℝ) (zbar : Fin 2 → ℝ) : Prop :=
  ∀ ze : Fin 2 → ℝ, Tendsto (fun k => (Tmap B zbar)^[k] ze) atTop (𝓝 zbar)

/-- Woodford (2003), p. 269: iterative E-stability holds iff both eigenvalues of `B` lie inside
the unit circle — the same condition as determinacy (`fwdDeterminate_iff`). -/
theorem iterEStable_iff (B : Matrix (Fin 2) (Fin 2) ℝ) (zbar : Fin 2 → ℝ) :
    IterEStable B zbar ↔ SchurStable (tr2 B) (det2 B) := by
  constructor
  · intro h
    -- the entries of `Bᵏ` tend to zero
    have hent : ∀ i j, Tendsto (fun k => (B ^ k) i j) atTop (𝓝 0) := by
      intro i j
      have := (tendsto_pi_nhds.mp (h (zbar + Pi.single j 1))) i
      have hsub := this.sub_const (zbar i)
      simp only [sub_self] at hsub
      refine hsub.congr fun k => ?_
      rw [Tmap_iterate, add_sub_cancel_left]
      simp [Matrix.mulVec_single]
    by_contra hS
    rw [schurStable_iff_roots, not_and_or, not_lt, not_lt] at hS
    obtain ⟨r, hr1, hroot⟩ : ∃ r : ℂ, 1 ≤ ‖r‖ ∧ r ^ 2 - tr2 B * r + det2 B = 0 := by
      rcases hS with hS | hS
      · exact ⟨_, hS, root_eq _ _ _ (Or.inl rfl)⟩
      · exact ⟨_, hS, root_eq _ _ _ (Or.inr rfl)⟩
    obtain ⟨v, ⟨i, hi⟩, hv⟩ := exists_eigenvector B hroot
    have hpow : ∀ k : ℕ, ((B ^ k) i 0 : ℂ) * v 0 + (B ^ k) i 1 * v 1 = r ^ k * v i := by
      intro k
      induction k generalizing i with
      | zero => fin_cases i <;> simp
      | succ k ih =>
        rw [pow_succ]
        simp only [Matrix.mul_apply, Fin.sum_univ_two]
        push_cast
        have h0 := hv 0
        have h1 := hv 1
        have := ih i hi
        linear_combination ((B ^ k) i 0 : ℂ) * h0 + ((B ^ k) i 1 : ℂ) * h1 + r * this
    have hlim : Tendsto (fun k : ℕ => r ^ k * v i) atTop (𝓝 0) := by
      have h0 := (Complex.continuous_ofReal.tendsto 0).comp (hent i 0)
      have h1 := (Complex.continuous_ofReal.tendsto 0).comp (hent i 1)
      have := (h0.mul_const (v 0)).add (h1.mul_const (v 1))
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at this
      exact this.congr fun k => hpow k
    have hvi : 0 < ‖v i‖ := norm_pos_iff.mpr fun h0 => hi (by simp [h0])
    have hle : ∀ k : ℕ, ‖v i‖ ≤ ‖r ^ k * v i‖ := by
      intro k
      rw [norm_mul, norm_pow]
      exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hr1)
    have := ge_of_tendsto' (tendsto_norm_zero.comp hlim) hle
    linarith
  · intro hS ze
    have hv : Tendsto (fun k => (B ^ k).mulVec (ze - zbar)) atTop (𝓝 0) := by
      refine tendsto_pi_nhds.mpr fun i => ?_
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.zero_apply]
      have := ((tendsto_pow_entry hS i 0).mul_const ((ze - zbar) 0)).add
        ((tendsto_pow_entry hS i 1).mul_const ((ze - zbar) 1))
      simpa using this
    have := hv.const_add zbar
    rw [add_zero] at this
    exact this.congr fun k => (Tmap_iterate B zbar ze k).symm

/-- Woodford (2003), p. 269: for the Taylor rule (1.14), iterative E-stability, E-stability,
determinacy and (2.7) all coincide. -/
theorem taylor_iterEStable_iff {Ω' : Type*} [Nonempty Ω'] (𝔼 : ExpectationSystem Ω')
    {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ) (hφπ : 0 ≤ φπ)
    (hφx : 0 ≤ φx) (zbar : Fin 2 → ℝ) (πbar : ℝ) :
    (IterEStable (taylorB β σ κ φπ φx) zbar ↔ 1 < taylorLHS β κ φπ φx) ∧
      (EStable (taylorB β σ κ φπ φx) ↔ 1 < taylorLHS β κ φπ φx) ∧
      (ModelDeterminate 𝔼 (TaylorEqm 𝔼 β σ κ φπ φx πbar) ↔ 1 < taylorLHS β κ φπ φx) := by
  refine ⟨?_, prop_4_8 hβ0 hβ1 hσ hκ hφπ hφx, prop_4_3 𝔼 hβ0 hβ1 hσ hκ hφπ hφx πbar⟩
  rw [iterEStable_iff]
  exact taylorB_schurStable_iff hβ0 hβ1 hσ hκ hφπ hφx

/-! ### Self-consistent equilibria and the loci of Figures 4.3–4.4 -/

/-- Woodford (2003), p. 264: `zᵉ` is a fixed point of `T` iff `(B − I)(zᵉ − z̄) = 0`. -/
theorem Tmap_fixed_iff (B : Matrix (Fin 2) (Fin 2) ℝ) (zbar ze : Fin 2 → ℝ) :
    Tmap B zbar ze = ze ↔ (B - 1).mulVec (ze - zbar) = 0 := by
  unfold Tmap
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  constructor
  · intro h
    rw [eq_sub_iff_add_eq, add_comm]
    exact h
  · intro h
    rw [h]
    abel

/-- Woodford (2003), App. C.1 (tool): if `det(M − I) ≠ 0` the only solution of
`(M − I) w = 0` is `w = 0`. -/
theorem sub_one_mulVec_eq_zero {M : Matrix (Fin 2) (Fin 2) ℝ}
    (h : det2 M - tr2 M + 1 ≠ 0) {w : Fin 2 → ℝ} (hw : (M - 1).mulVec w = 0) : w = 0 := by
  have h0 : (M 0 0 - 1) * w 0 + M 0 1 * w 1 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hw 0
  have h1 : M 1 0 * w 0 + (M 1 1 - 1) * w 1 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hw 1
  unfold det2 tr2 at h
  have e0 : (M 0 0 * M 1 1 - M 0 1 * M 1 0 - (M 0 0 + M 1 1) + 1) * w 0 = 0 := by
    linear_combination (M 1 1 - 1) * h0 - M 0 1 * h1
  have e1 : (M 0 0 * M 1 1 - M 0 1 * M 1 0 - (M 0 0 + M 1 1) + 1) * w 1 = 0 := by
    linear_combination (M 0 0 - 1) * h1 - M 1 0 * h0
  funext i
  fin_cases i
  · exact (mul_eq_zero.mp e0).resolve_left h
  · exact (mul_eq_zero.mp e1).resolve_left h

/-- Woodford (2003), fn. 35, p. 264: unless (2.7) holds as an equality, `z̄` is the unique
self-consistent equilibrium. -/
theorem sce_unique {β σ κ φπ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (h : taylorLHS β κ φπ φx ≠ 1) (zbar ze : Fin 2 → ℝ) :
    Tmap (taylorB β σ κ φπ φx) zbar ze = ze ↔ ze = zbar := by
  have hΔ := one_le_taylorDelta hσ hκ hφπ hφx
  have hΔ0 : taylorDelta σ κ φπ φx ≠ 0 := by linarith
  have hne : det2 (taylorB β σ κ φπ φx) - tr2 (taylorB β σ κ φπ φx) + 1 ≠ 0 := by
    rw [taylorB_one_sub hκ.ne' hΔ0]
    exact div_ne_zero (mul_ne_zero (mul_pos hσ hκ).ne' (sub_ne_zero.mpr h)) hΔ0
  constructor
  · intro hf
    have := sub_one_mulVec_eq_zero hne ((Tmap_fixed_iff _ _ _).mp hf)
    exact sub_eq_zero.mp this
  · rintro rfl
    exact Tmap_zbar _ _

/-- Woodford (2003), fn. 35, p. 264 and p. 268: when (2.7) holds with equality, every point of
the line `z̄ + c (1, (1 − β)/κ)` is a self-consistent equilibrium (a continuum of s.c.e.). -/
theorem sce_line {β σ κ φπ φx : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0)
    (hΔ : taylorDelta σ κ φπ φx ≠ 0) (h : taylorLHS β κ φπ φx = 1) (zbar : Fin 2 → ℝ)
    (c : ℝ) :
    Tmap (taylorB β σ κ φπ φx) zbar (zbar + c • ![1, (1 - β) / κ]) =
      zbar + c • ![1, (1 - β) / κ] := by
  rw [Tmap_fixed_iff, add_sub_cancel_left, Matrix.mulVec_smul, Matrix.sub_mulVec,
    Matrix.one_mulVec, (fn27_eigenvector hβ hκ hΔ h).2, sub_self, smul_zero]

/-- Woodford (2003), eq. (2.20), p. 265: the E-stability ODE `żᵉ = T(zᵉ) − zᵉ`, whose vector
field is `(B − I)(zᵉ − z̄)`. -/
theorem estability_field (B : Matrix (Fin 2) (Fin 2) ℝ) (zbar ze : Fin 2 → ℝ) :
    Tmap B zbar ze - ze = (B - 1).mulVec (ze - zbar) := by
  unfold Tmap
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  abel

/-- Woodford (2003), p. 268: when (2.7) holds with equality the loci `π̇ᵉ = 0` (first row of
`(B − I)w = 0`) and `ẋᵉ = 0` (second row) coincide: both are the line
`wₓ = ((1 − β)/κ) w_π` through `z̄`. -/
theorem loci_coincide {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (h : taylorLHS β κ φπ φx = 1)
    (w : Fin 2 → ℝ) :
    ((taylorB β σ κ φπ φx - 1).mulVec w 0 = 0 ↔ w 1 = (1 - β) / κ * w 0) ∧
      ((taylorB β σ κ φπ φx - 1).mulVec w 1 = 0 ↔ w 1 = (1 - β) / κ * w 0) := by
  have hΔ := one_le_taylorDelta hσ hκ hφπ hφx
  have hΔ0 : taylorDelta σ κ φπ φx ≠ 0 := by linarith
  have hv := (fn27_eigenvector (σ := σ) hβ0.ne' hκ.ne' hΔ0 h).2
  have hv0 : taylorB β σ κ φπ φx 0 0 + taylorB β σ κ φπ φx 0 1 * ((1 - β) / κ) = 1 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hv 0
  have hv1 : taylorB β σ κ φπ φx 1 0 + taylorB β σ κ φπ φx 1 1 * ((1 - β) / κ) =
      (1 - β) / κ := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hv 1
  -- the strict inequality `Δ > 1` (some coefficient is positive at equality)
  have hΔ1 : 1 < taylorDelta σ κ φπ φx := by
    unfold taylorLHS at h
    unfold taylorDelta
    by_contra hc
    push Not at hc
    have h1 : 0 ≤ σ * φx := mul_nonneg hσ.le hφx
    have h2 : 0 ≤ σ * κ * φπ := mul_nonneg (mul_nonneg hσ.le hκ.le) hφπ
    have hx0 : σ * φx = 0 := by linarith
    have hp0 : σ * κ * φπ = 0 := by linarith
    have hφx0 : φx = 0 := by
      rcases mul_eq_zero.mp hx0 with h' | h'
      · linarith
      · exact h'
    have hφπ0 : φπ = 0 := by
      rcases mul_eq_zero.mp hp0 with h' | h'
      · exact absurd h' (mul_pos hσ hκ).ne'
      · exact h'
    rw [hφx0, hφπ0] at h
    norm_num at h
  have hB01 : taylorB β σ κ φπ φx 0 1 ≠ 0 := by
    simp only [taylorB, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    exact div_ne_zero hκ.ne' hΔ0
  have hB11 : taylorB β σ κ φπ φx 1 1 - 1 ≠ 0 := by
    simp only [taylorB, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [sub_ne_zero, ne_eq, div_eq_one_iff_eq hΔ0]
    intro h'
    linarith
  have r0 : (taylorB β σ κ φπ φx - 1).mulVec w 0 = (taylorB β σ κ φπ φx 0 0 - 1) * w 0 +
      taylorB β σ κ φπ φx 0 1 * w 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have r1 : (taylorB β σ κ φπ φx - 1).mulVec w 1 = taylorB β σ κ φπ φx 1 0 * w 0 +
      (taylorB β σ κ φπ φx 1 1 - 1) * w 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [r0, r1]
  constructor
  · constructor
    · intro hw
      have : taylorB β σ κ φπ φx 0 1 * (w 1 - (1 - β) / κ * w 0) = 0 := by
        linear_combination hw - w 0 * hv0
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hB01)
    · intro hw
      rw [hw]
      linear_combination w 0 * hv0
  · constructor
    · intro hw
      have : (taylorB β σ κ φπ φx 1 1 - 1) * (w 1 - (1 - β) / κ * w 0) = 0 := by
        linear_combination hw - w 0 * hv1
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hB11)
    · intro hw
      rw [hw]
      linear_combination w 0 * hv1

/-- Woodford (2003), p. 268: away from the equality case the two loci meet only at `z̄`. -/
theorem loci_meet_once {β σ κ φπ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hφπ : 0 ≤ φπ)
    (hφx : 0 ≤ φx) (h : taylorLHS β κ φπ φx ≠ 1) (w : Fin 2 → ℝ)
    (h0 : (taylorB β σ κ φπ φx - 1).mulVec w 0 = 0)
    (h1 : (taylorB β σ κ φπ φx - 1).mulVec w 1 = 0) : w = 0 := by
  have hΔ := one_le_taylorDelta hσ hκ hφπ hφx
  have hΔ0 : taylorDelta σ κ φπ φx ≠ 0 := by linarith
  have hne : det2 (taylorB β σ κ φπ φx) - tr2 (taylorB β σ κ φπ φx) + 1 ≠ 0 := by
    rw [taylorB_one_sub hκ.ne' hΔ0]
    exact div_ne_zero (mul_ne_zero (mul_pos hσ hκ).ne' (sub_ne_zero.mpr h)) hΔ0
  refine sub_one_mulVec_eq_zero hne ?_
  funext i
  fin_cases i
  · exact h0
  · exact h1

/-- Woodford (2003), fn. 38, p. 267: the coefficient of `πᵉ` in `π̇ᵉ` is
`B₀₀ − 1 = (σκ(1 − LHS) − (1 − β))/Δ`; the `π̇ᵉ = 0` locus is vertical exactly when the
left-hand side of (2.7) equals `1 − (1 − β)/(κσ)`. -/
theorem fn38_vertical {β σ κ φπ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hΔ : taylorDelta σ κ φπ φx ≠ 0) :
    taylorB β σ κ φπ φx 0 0 - 1 =
        (σ * κ * (1 - taylorLHS β κ φπ φx) - (1 - β)) / taylorDelta σ κ φπ φx ∧
      (taylorB β σ κ φπ φx 0 0 = 1 ↔ taylorLHS β κ φπ φx = 1 - (1 - β) / (κ * σ)) := by
  have e : taylorB β σ κ φπ φx 0 0 - 1 =
      (σ * κ * (1 - taylorLHS β κ φπ φx) - (1 - β)) / taylorDelta σ κ φπ φx := by
    simp only [taylorB, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [taylorLHS]
    field_simp
    unfold taylorDelta
    ring
  refine ⟨e, ?_⟩
  rw [← sub_eq_zero, e, div_eq_zero_iff, or_iff_left hΔ]
  constructor
  · intro h0
    field_simp
    linear_combination -h0
  · intro h0
    rw [h0]
    field_simp
    ring

/-- Woodford (2003), fn. 39, p. 267: the coefficient of `πᵉ` in `ẋᵉ` is `σ(1 − βφ_π)/Δ`, zero
exactly at `φ_π = β⁻¹` (where the `ẋᵉ = 0` locus is vertical). -/
theorem fn39_vertical {β σ κ φπ φx : ℝ} (hβ : 0 < β) (hσ : 0 < σ)
    (hΔ : taylorDelta σ κ φπ φx ≠ 0) :
    taylorB β σ κ φπ φx 1 0 = 0 ↔ φπ = β⁻¹ := by
  simp only [taylorB, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero,
    div_eq_zero_iff, or_iff_left hΔ, mul_eq_zero, or_iff_right hσ.ne']
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

end Woodford.NeoWicksellianFramework.Determinacy2Learning
