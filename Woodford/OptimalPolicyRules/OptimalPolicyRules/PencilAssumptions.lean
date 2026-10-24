/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.PencilEigen
import OptimalPolicyRules.Prop82General
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

/-!
# Propositions 8.1 and 8.2 under Assumptions 8.1–8.5

Woodford (2003), *Interest and Prices*, Chapter 8, Propositions 8.1 (p. 553) and 8.2 (p. 555),
with Appendix G.1–G.2 (pp. 716–719): Assumptions 8.4 and 8.5, (G.6)–(G.7).

* `Assumption84`: the matrix `Γ` of left (generalised) eigenvectors for the roots *not*
  selected (G.6): `W Γ' A = Γ' Î`, the eigenvalues of `W` being zero or reciprocals of unselected
  roots; (i) `A'Γ` has full rank `n_z`; (ii) `det Γ₂ ≠ 0`. `Γ` is taken real (real and imaginary
  parts of conjugate pairs, as for `J`, fn 2), so the book's `det[Re Γ₂] ≠ 0` is `det Γ₂ ≠ 0`.
* `sylvester_zero`: if `W Y Ψ = Y` and no eigenvalue product `θμ` equals `1`, then `Y = 0`.
  Hence (G.7), `Γ' Î J = Γ' A J = 0` (`G7`).
* `J1_det_ne_zero`, `K_det_ne_zero`: Assumption 8.4 makes `J₁` and `K = A₂₂' + A₁₂'Υ`
  invertible (using `rank Î J = n_Z`, from a shift `s` that is not a root).
* `deflatingSplit_of_assumptions`: Assumptions 8.2 (case (i)), 8.3 and 8.4 give a
  `PencilSplit.DeflatingSplit`.
* `prop81_of_assumptions`: **Proposition 8.1 under Assumptions 8.2–8.4** (corrected form, any
  expectation system); `prop81_of_assumptions_perfectForesight`: the original statement under
  perfect foresight.
* `Assumption85`, `prop82_of_assumptions`: **Proposition 8.2 under Assumptions 8.1–8.5**:
  commitment to (1.23) determines a unique bounded equilibrium for every bounded disturbance
  process, optimal subject to (1.27), robustly optimal, with the time-invariant multiplier rule
  (1.17).
* `natDegree_alpha_eq_rank`: under Assumptions 8.2 (i)–8.4, `deg α = rank Λ = rank Ẽ` (the
  book's claim on p. 553 holds under its assumptions; E18 is the general correction).
-/

namespace Woodford.OptimalPolicyRules.PencilAssumptions

open Matrix Polynomial GeneralSetup PencilSplit PencilEigen GeneralFOC.Selection

/-! ### A Sylvester-type uniqueness lemma -/

/-- Woodford (2003), App. G.1, (G.7) ("follows from (G.3)"): if `W Y Ψ = Y` and no eigenvalue
`θ` of `W` and `μ` of `Ψ` have `θ μ = 1`, then `Y = 0`. Proof: `r(W) Y = 0` for the reversed
characteristic polynomial `r(w) = ∑ pⱼ w^{d−j}` of `Ψ`, and `r(W)` is invertible by the spectral
mapping theorem. -/
theorem sylvester_zero {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {W : Matrix m m ℂ} {Ψ : Matrix n n ℂ} {Y : Matrix m n ℂ} (hY : W * Y * Ψ = Y)
    (hdisj : ∀ θ μ : ℂ, (Matrix.scalar m θ - W).det = 0 → (Matrix.scalar n μ - Ψ).det = 0 →
      θ * μ ≠ 1) : Y = 0 := by
  rcases isEmpty_or_nonempty m with hm | hm
  · ext i j
    exact isEmptyElim i
  set p := Ψ.charpoly with hp
  set d := Fintype.card n with hd
  have hpd : p.natDegree = d := charpoly_natDegree_eq_dim Ψ
  have hpow : ∀ k : ℕ, W ^ k * Y * Ψ ^ k = Y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc W ^ (k + 1) * Y * Ψ ^ (k + 1) = W ^ k * (W * Y * Ψ) * Ψ ^ k := by
            rw [pow_succ, pow_succ']
            simp only [Matrix.mul_assoc]
        _ = Y := by rw [hY, ih]
  set r : ℂ[X] := ∑ j ∈ Finset.range (d + 1), C (p.coeff j) * X ^ (d - j) with hr
  have hrW : aeval W r = ∑ j ∈ Finset.range (d + 1), p.coeff j • W ^ (d - j) := by
    simp [hr, map_sum, Algebra.smul_def]
  have hkill : aeval W r * Y = 0 := by
    rw [hrW, Matrix.sum_mul]
    have hterm : ∀ j ∈ Finset.range (d + 1),
        p.coeff j • W ^ (d - j) * Y = W ^ d * Y * (p.coeff j • Ψ ^ j) := by
      intro j hj
      have hj' : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      calc p.coeff j • W ^ (d - j) * Y = p.coeff j • (W ^ (d - j) * (W ^ j * Y * Ψ ^ j)) := by
            rw [hpow j, Matrix.smul_mul]
        _ = p.coeff j • (W ^ d * Y * Ψ ^ j) := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← pow_add, Nat.sub_add_cancel hj']
        _ = W ^ d * Y * (p.coeff j • Ψ ^ j) := by rw [Matrix.mul_smul]
    rw [Finset.sum_congr rfl hterm, ← Matrix.mul_sum]
    have hcay : ∑ j ∈ Finset.range (d + 1), p.coeff j • Ψ ^ j = 0 := by
      rw [← hpd, ← aeval_eq_sum_range, hp, aeval_self_charpoly]
    rw [hcay, Matrix.mul_zero]
  have hunit : IsUnit (aeval W r) := by
    by_contra hnu
    have h0 : (0 : ℂ) ∈ spectrum ℂ (aeval W r) := spectrum.zero_mem_iff ℂ |>.mpr hnu
    rw [spectrum.map_polynomial_aeval_of_nonempty W r
      (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ W)] at h0
    obtain ⟨θ, hθ, hθr⟩ := h0
    simp only at hθr
    have hθW : (Matrix.scalar m θ - W).det = 0 := by
      rw [← eval_charpoly]
      exact Matrix.mem_spectrum_iff_isRoot_charpoly.mp hθ
    have heval : r.eval θ = ∑ j ∈ Finset.range (d + 1), p.coeff j * θ ^ (d - j) := by
      simp [hr, eval_finsetSum]
    rw [heval] at hθr
    by_cases hθ0 : θ = 0
    · subst hθ0
      rw [Finset.sum_eq_single d] at hθr
      · have hmon : p.coeff d = 1 := by
          rw [← hpd]
          exact (charpoly_monic Ψ).coeff_natDegree
        simp [hmon] at hθr
      · intro j hj hjd
        have hj' : j < d := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hjd
        rw [zero_pow (by omega), mul_zero]
      · intro hd'
        exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self d)) hd'
    · have hμ : p.eval θ⁻¹ = 0 := by
        have hsum : ∑ j ∈ Finset.range (d + 1), p.coeff j * θ ^ (d - j) =
            θ ^ d * p.eval θ⁻¹ := by
          rw [eval_eq_sum_range, hpd, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hj' : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          rw [pow_sub₀ θ hθ0 hj', inv_pow]
          ring
        rw [hsum] at hθr
        exact (mul_eq_zero.mp hθr).resolve_left (pow_ne_zero _ hθ0)
      have hμΨ : (Matrix.scalar n θ⁻¹ - Ψ).det = 0 := by
        rw [← eval_charpoly]
        exact hμ
      exact hdisj θ θ⁻¹ hθW hμΨ (mul_inv_cancel₀ hθ0)
  calc Y = (aeval W r)⁻¹ * (aeval W r * Y) := by
        rw [← Matrix.mul_assoc,
          Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit), Matrix.one_mul]
    _ = 0 := by rw [hkill, Matrix.mul_zero]

/-! ### Ranks and kernels -/

/-- Woodford (2003), App. G.1: independent columns make `M v = 0` force `v = 0`. -/
theorem eq_zero_of_indep {l k : Type*} [Fintype k] {M : Matrix l k ℝ}
    (h : LinearIndependent ℝ Mᵀ) {v : k → ℝ} (hv : M *ᵥ v = 0) : v = 0 := by
  have hsum : ∑ j, v j • Mᵀ j = 0 := by
    funext a
    have := congrFun hv a
    simpa [mulVec, dotProduct, Finset.sum_apply, mul_comm] using this
  funext j
  exact Fintype.linearIndependent_iff.mp h v hsum j

/-- Woodford (2003), App. G.1: a matrix whose kernel is zero has rank equal to its number of
columns. -/
theorem rank_eq_of_injective {l k : Type*} [Fintype k] {M : Matrix l k ℝ}
    (h : ∀ v, M *ᵥ v = 0 → v = 0) : M.rank = Fintype.card k := by
  have hker : LinearMap.ker M.mulVecLin = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    exact h v hv
  have := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [hker, finrank_bot, add_zero, Module.finrank_fintype_fun_eq_card] at this
  exact this

/-- Woodford (2003), App. G.1 (the columns of `Γ` and `Ω` form a basis, p. 718): if `N M = 0`
and `rank M + rank N` is the dimension of the middle space, then the kernel of `N` is the range
of `M`. -/
theorem exists_of_mulVec_eq_zero {l k m : Type*} [Fintype l] [Fintype k]
    (M : Matrix l k ℝ) (N : Matrix m l ℝ) (hNM : N * M = 0)
    (hdim : M.rank + N.rank = Fintype.card l) {p : l → ℝ} (hp : N *ᵥ p = 0) :
    ∃ a, M *ᵥ a = p := by
  have hle : LinearMap.range M.mulVecLin ≤ LinearMap.ker N.mulVecLin := by
    rintro _ ⟨a, rfl⟩
    change N *ᵥ (M *ᵥ a) = 0
    rw [mulVec_mulVec, hNM, zero_mulVec]
  have hker : Module.finrank ℝ (LinearMap.range M.mulVecLin) =
      Module.finrank ℝ (LinearMap.ker N.mulVecLin) := by
    have := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at this
    change N.rank + _ = _ at this
    change M.rank = _
    omega
  have heq := Submodule.eq_of_le_of_finrank_eq hle hker
  have hp' : p ∈ LinearMap.ker N.mulVecLin := hp
  rw [← heq] at hp'
  obtain ⟨a, ha⟩ := hp'
  exact ⟨a, ha⟩

/-- Woodford (2003), App. G.1: complexification commutes with matrix products. -/
theorem map_ofReal_mul {l m n : Type*} [Fintype m] (A : Matrix l m ℝ) (B : Matrix m n ℝ) :
    (A * B).map Complex.ofReal = A.map Complex.ofReal * B.map Complex.ofReal := by
  ext i j
  simp [Matrix.mul_apply]

/-! ### Assumption 8.4 and (G.7) -/

variable {ιZ ιz : Type*} [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz]

/-- Woodford (2003), (G.6), App. G.1, p. 718: every eigenvalue of `W` is zero or the reciprocal
of a nonzero root of (1.15) that is not selected. -/
def WEig (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) (W : Matrix ιz ιz ℝ) : Prop :=
  ∀ θ : ℂ, (Matrix.scalar ιz θ - W.map Complex.ofReal).det = 0 →
    θ = 0 ∨ ∃ μ : ℂ, S.pencilPoly.eval μ = 0 ∧ μ ≠ 0 ∧ μ ∉ sel ∧ θ = μ⁻¹

/-- Woodford (2003), Assumption 8.4, App. G.1, p. 718, with (G.6): the `n × n_z` matrix `Γ`
whose columns combine the left eigenvectors with eigenvalue zero or the reciprocal of a root of
(1.15) *not* selected (`W Γ' A = Γ' Î`, every eigenvalue of `W` zero or `μ⁻¹` for an
unselected nonzero root `μ`) satisfies (i) `A'Γ` has full rank `n_z` and (ii) `det Γ₂ ≠ 0`
(`Γ₂` the rows belonging to `z`). `Γ` is real (fn 2), so `Re Γ₂ = Γ₂`. -/
structure Assumption84 (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) where
  Γ : Matrix (ιZ ⊕ ιz) ιz ℝ
  W : Matrix ιz ιz ℝ
  G6 : W * Γᵀ * S.Ahat = Γᵀ * S.Ihat
  W_eig : WEig S sel W
  full_rank : (S.Ahatᵀ * Γ).rank = Fintype.card ιz
  det_Γ2 : (Γ.submatrix Sum.inr id).det ≠ 0

variable {S : LinearRESystem ιZ ιz} {sel : Multiset ℂ}

/-- Woodford (2003), App. G.1, (G.7), p. 718: `Γ' Î J = Γ' A J = 0` (the left eigenvectors of
the unselected roots annihilate the selected deflating subspace). -/
theorem G7 (R : RealSelection S sel) (h84 : Assumption84 S sel) :
    h84.Γᵀ * S.Ihat * R.J = 0 ∧ h84.Γᵀ * S.Ahat * R.J = 0 := by
  set Y := h84.Γᵀ * S.Ihat * R.J with hY
  have hWY : h84.W * Y * R.Ψ = Y := by
    calc h84.W * Y * R.Ψ = h84.W * h84.Γᵀ * (S.Ihat * R.J * R.Ψ) := by
          simp only [hY, Matrix.mul_assoc]
      _ = h84.W * h84.Γᵀ * S.Ahat * R.J := by
          rw [← R.deflate, Matrix.mul_assoc (h84.W * h84.Γᵀ) S.Ahat R.J]
      _ = Y := by rw [h84.G6, hY]
  have hWYc : h84.W.map Complex.ofReal * Y.map Complex.ofReal * R.Ψ.map Complex.ofReal =
      Y.map Complex.ofReal := by
    rw [← map_ofReal_mul, ← map_ofReal_mul, hWY]
  have hYc := sylvester_zero hWYc fun θ μ hθ hμ hθμ => by
    rcases R.eig μ hμ with h0 | hs
    · rw [h0, mul_zero] at hθμ
      exact zero_ne_one hθμ
    · rcases h84.W_eig θ hθ with h0 | ⟨μ', -, hμ'0, hμ's, hθe⟩
      · rw [h0, zero_mul] at hθμ
        exact zero_ne_one hθμ
      · rw [hθe, inv_mul_eq_one₀ hμ'0] at hθμ
        exact hμ's (hθμ ▸ hs)
  have hY0 : Y = 0 := by
    ext i j
    have := congrFun (congrFun hYc i) j
    simpa using this
  refine ⟨hY0, ?_⟩
  rw [Matrix.mul_assoc, R.deflate, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    show h84.Γᵀ * S.Ihat * R.J = Y from rfl, hY0, Matrix.zero_mul]

/-- Woodford (2003), App. G.1: `Î J` has full column rank `n_Z` (with `(A − sÎ) J = Î J (Ψ − s)`
for a real `s ≠ 0` that is not a root, so `A − sÎ` and `Ψ − s` are invertible). -/
theorem IJ_injective (R : RealSelection S sel) (hsel : ∀ μ ∈ sel, S.pencilPoly.eval μ = 0)
    (hreg : S.pencilPoly ≠ 0) {v : ιZ → ℝ} (hv : (S.Ihat * R.J) *ᵥ v = 0) : v = 0 := by
  obtain ⟨s, hs0, hs⟩ := PencilEigen.Construction.exists_shift hreg
  have hA : (S.Ahat - s • S.Ihat).det ≠ 0 := by
    intro h
    apply hs
    rw [pencilPoly_eval, det_pencil_ofReal, h, Complex.ofReal_zero]
  set N' := R.Ψ - s • (1 : Matrix ιZ ιZ ℝ) with hN'
  have hN : N'.det ≠ 0 := by
    intro h
    have hc : (Matrix.scalar ιZ (s : ℂ) - R.Ψ.map Complex.ofReal).det = 0 := by
      have e1 : Matrix.scalar ιZ (s : ℂ) - R.Ψ.map Complex.ofReal = -(N'.map Complex.ofReal) := by
        ext i j
        by_cases hij : i = j
        · subst hij
          simp [hN', Matrix.scalar_apply]
        · simp [hN', Matrix.scalar_apply, hij, Matrix.one_apply_ne hij]
      have e2 := Complex.ofRealHom.map_det N'
      rw [RingHom.mapMatrix_apply] at e2
      change (N'.det : ℂ) = (N'.map Complex.ofReal).det at e2
      rw [e1, det_neg, ← e2, h, Complex.ofReal_zero, mul_zero]
    rcases R.eig _ hc with h0 | hm
    · exact hs0 (Complex.ofReal_eq_zero.mp h0)
    · exact hs (hsel _ hm)
  have hkey : (S.Ahat - s • S.Ihat) * R.J = S.Ihat * R.J * N' := by
    rw [Matrix.sub_mul, R.deflate, hN', Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_one]
  have hIJ : S.Ihat * R.J = (S.Ahat - s • S.Ihat) * R.J * N'⁻¹ := by
    rw [hkey, Matrix.mul_assoc, mul_nonsing_inv _ (Ne.isUnit hN), Matrix.mul_one]
  rw [hIJ, ← mulVec_mulVec, ← mulVec_mulVec] at hv
  have h1 := eq_zero_of_mulVec_eq_zero hA hv
  have h2 := eq_zero_of_indep R.indep h1
  calc v = N' *ᵥ (N'⁻¹ *ᵥ v) := by
        rw [mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit hN), one_mulVec]
    _ = 0 := by rw [h2, mulVec_zero]

/-- Woodford (2003), Assumption 8.4 (ii), App. G.1, p. 718: `det Γ₂ ≠ 0` makes `J₁` invertible
(the role it plays in (1.21)): if `J₁' ξ = 0` then `(ξ, 0)` lies in the kernel of `(Î J)'`, which
is the range of `Γ` by (G.7) and a dimension count, and `Γ₂` is invertible. -/
theorem J1_det_ne_zero (R : RealSelection S sel) (h84 : Assumption84 S sel)
    (hIJ : ∀ v, (S.Ihat * R.J) *ᵥ v = 0 → v = 0) : (J1 R.J).det ≠ 0 := by
  intro hdet
  have hdetT : ((J1 R.J)ᵀ).det = 0 := by rw [det_transpose]; exact hdet
  obtain ⟨ξ, hξ0, hξ⟩ := exists_mulVec_eq_zero_iff.mpr hdetT
  set p : ιZ ⊕ ιz → ℝ := Sum.elim ξ 0 with hpdef
  have hp : (S.Ihat * R.J)ᵀ *ᵥ p = 0 := by
    rw [transpose_mul, ← mulVec_mulVec, Ihat_transpose_mulVec, J_transpose_mulVec]
    have h1 : (Sum.elim (p ∘ Sum.inl) (S.Etᵀ *ᵥ (p ∘ Sum.inr)) : ιZ ⊕ ιz → ℝ) ∘ Sum.inl = ξ :=
      rfl
    have h2 : (Sum.elim (p ∘ Sum.inl) (S.Etᵀ *ᵥ (p ∘ Sum.inr)) : ιZ ⊕ ιz → ℝ) ∘ Sum.inr = 0 := by
      funext r
      simp [hpdef]
    rw [h1, h2, hξ, mulVec_zero, add_zero]
  have hNM : (S.Ihat * R.J)ᵀ * h84.Γ = 0 := by
    have := (G7 R h84).1
    rw [← transpose_transpose h84.Γ, ← transpose_mul, ← Matrix.mul_assoc, this,
      transpose_zero]
  have hrΓ : h84.Γ.rank = Fintype.card ιz :=
    le_antisymm (rank_le_card_width _) (h84.full_rank ▸ rank_mul_le_right _ _)
  have hrIJ : (S.Ihat * R.J)ᵀ.rank = Fintype.card ιZ := by
    rw [rank_transpose]
    exact rank_eq_of_injective hIJ
  have hdim : h84.Γ.rank + (S.Ihat * R.J)ᵀ.rank = Fintype.card (ιZ ⊕ ιz) := by
    rw [hrΓ, hrIJ, Fintype.card_sum, add_comm]
  obtain ⟨a, ha⟩ := exists_of_mulVec_eq_zero h84.Γ _ hNM hdim hp
  have ha2 : (h84.Γ.submatrix Sum.inr id) *ᵥ a = 0 := by
    funext r
    have := congrFun ha (Sum.inr r)
    change (h84.Γ *ᵥ a) (Sum.inr r) = 0
    rw [this, hpdef]
    rfl
  have ha0 := eq_zero_of_mulVec_eq_zero h84.det_Γ2 ha2
  have hp0 : p = 0 := by rw [← ha, ha0, mulVec_zero]
  exact hξ0 (funext fun i => by simpa [hpdef] using congrFun hp0 (Sum.inl i))

/-- Woodford (2003), Assumption 8.4 (i), App. G.1, p. 718: `A'Γ` of full rank makes
`K = A₂₂' + A₁₂' Υ` invertible (the role it plays in (1.20)): if `K' u = 0`, `(0, u)` lies in the
kernel of `Γ' A`, which is the range of `J` by (G.7) and a dimension count, and `J₁` is
invertible. -/
theorem K_det_ne_zero (R : RealSelection S sel) (h84 : Assumption84 S sel)
    (hJ1 : (J1 R.J).det ≠ 0) : (Kmat S R.J).det ≠ 0 := by
  intro hdet
  have hdetT : ((Kmat S R.J)ᵀ).det = 0 := by rw [det_transpose]; exact hdet
  obtain ⟨u, hu0, hu⟩ := exists_mulVec_eq_zero_iff.mpr hdetT
  have hKT : (Kmat S R.J)ᵀ = S.A22 - S.Et * J2 R.J * (J1 R.J)⁻¹ * S.A12 := by
    simp only [Kmat, Υmat, transpose_add, transpose_mul, transpose_neg, transpose_transpose,
      transpose_nonsing_inv, Matrix.mul_neg, sub_eq_add_neg, Matrix.mul_assoc]
  rw [hKT, sub_mulVec, sub_eq_zero] at hu
  have hJ1u : IsUnit (J1 R.J).det := Ne.isUnit hJ1
  set v := (J1 R.J)⁻¹ *ᵥ (S.A12 *ᵥ u) with hv
  set p : ιZ ⊕ ιz → ℝ := Sum.elim 0 u with hpdef
  have hAp : S.Ahat *ᵥ p = S.Ihat *ᵥ (R.J *ᵥ v) := by
    have hJv1 : (R.J *ᵥ v) ∘ Sum.inl = J1 R.J *ᵥ v := rfl
    have hJv2 : (R.J *ᵥ v) ∘ Sum.inr = J2 R.J *ᵥ v := rfl
    rw [LinearRESystem.Ahat, LinearRESystem.Ihat, fromBlocks_mulVec, fromBlocks_mulVec, hJv1,
      hJv2]
    have hp1 : p ∘ Sum.inl = 0 := rfl
    have hp2 : p ∘ Sum.inr = u := rfl
    rw [hp1, hp2]
    simp only [one_mulVec, zero_mulVec, mulVec_zero, zero_add, add_zero]
    congr 1
    · rw [hv, mulVec_mulVec, mul_nonsing_inv _ hJ1u, one_mulVec]
    · rw [hu, hv]
      simp only [mulVec_mulVec, Matrix.mul_assoc]
  have hΓAp : (h84.Γᵀ * S.Ahat) *ᵥ p = 0 := by
    rw [← mulVec_mulVec, hAp, mulVec_mulVec, mulVec_mulVec, (G7 R h84).1, zero_mulVec]
  have hNM : (h84.Γᵀ * S.Ahat) * R.J = 0 := (G7 R h84).2
  have hrJ : R.J.rank = Fintype.card ιZ :=
    rank_eq_of_injective fun w hw => eq_zero_of_indep R.indep hw
  have hrΓA : (h84.Γᵀ * S.Ahat).rank = Fintype.card ιz := by
    rw [← rank_transpose, transpose_mul, transpose_transpose]
    exact h84.full_rank
  have hdim : R.J.rank + (h84.Γᵀ * S.Ahat).rank = Fintype.card (ιZ ⊕ ιz) := by
    rw [hrJ, hrΓA, Fintype.card_sum]
  obtain ⟨w, hw⟩ := exists_of_mulVec_eq_zero R.J _ hNM hdim hΓAp
  have hw1 : J1 R.J *ᵥ w = 0 := by
    funext i
    have := congrFun hw (Sum.inl i)
    simpa [hpdef, mulVec, dotProduct, J1] using this
  have hw0 := eq_zero_of_mulVec_eq_zero hJ1 hw1
  have hp0 : p = 0 := by rw [← hw, hw0, mulVec_zero]
  exact hu0 (funext fun r => by simpa [hpdef] using congrFun hp0 (Sum.inr r))

/-! ### Proposition 8.1 under Assumptions 8.2–8.4 -/

/-- Woodford (2003), Assumptions 8.2–8.4 (App. G.1): a real selection (from Assumptions 8.2 (i)
and 8.3) together with Assumption 8.4 is a deflating pair with all eigenvalues of `Ψ` in
`|μ| < β⁻¹` and `J₁`, `K` invertible (`β > 0`). -/
noncomputable def splitOfSel {β : ℝ} (hβ : 0 < β) (h82 : Assumption82 S β)
    (R : RealSelection S h82.sel) (h83 : Assumption83 S) (h84 : Assumption84 S h82.sel) :
    DeflatingSplit S β where
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
      rw [Multiset.mem_filter, Polynomial.mem_roots h83.regular] at this
      exact this.1) h83.regular hv
  K_det := K_det_ne_zero R h84 (J1_det_ne_zero R h84 fun _ hv => IJ_injective R (fun μ hμ => by
      have := Multiset.mem_of_le h82.sel_le hμ
      rw [Multiset.mem_filter, Polynomial.mem_roots h83.regular] at this
      exact this.1) h83.regular hv)

/-- Woodford (2003), Assumptions 8.2–8.4 (App. G.1): with case (i) of Assumption 8.2 (a selection
closed under conjugation) and `β > 0`, there is a real deflating pair `A J = Î J Ψ` with all
eigenvalues of `Ψ` in `|μ| < β⁻¹` and `J₁`, `K` invertible. -/
theorem nonempty_deflatingSplit {β : ℝ} (hβ : 0 < β) (h82 : Assumption82 S β)
    (hi : ConjClosed h82.sel) (h83 : Assumption83 S) (h84 : Assumption84 S h82.sel) :
    Nonempty (DeflatingSplit S β) :=
  ⟨splitOfSel hβ h82 (exists_realSelection h82 hi h83).some h83 h84⟩

/-- Woodford (2003), App. G.1: the deflating pair chosen from Assumptions 8.2 (i), 8.3, 8.4. -/
noncomputable def splitOf {ιτ : Type*} [Fintype ιτ] (P : LQProblem ιZ ιz ιτ)
    (h82 : Assumption82 P.sys P.β) (hi : ConjClosed h82.sel) (h83 : Assumption83 P.sys)
    (h84 : Assumption84 P.sys h82.sel) : DeflatingSplit P.sys P.β :=
  splitOfSel P.β_pos h82 (exists_realSelection h82 hi h83).some h83 h84

/-- Woodford (2003), **Proposition 8.1**, p. 553, **proved under Assumptions 8.2 (case (i)),
8.3 and 8.4**: there exist real `Λ`, `Υ` and operators `Q(L⁻¹)`, `R(L⁻¹)` (mapping bounded
processes to bounded adapted processes) such that bounded `(φ, τ)` — adapted plans, multipliers
`M_t` known at `t` (p. 540) — satisfy (1.18) for all `t ≥ t₀` iff they satisfy (1.20)–(1.21).
Any expectation system. -/
theorem prop81_of_assumptions {Ω ιτ : Type*} [Fintype ιτ] (P : LQProblem ιZ ιz ιτ)
    (h82 : Assumption82 P.sys P.β) (hi : ConjClosed h82.sel) (h83 : Assumption83 P.sys)
    (h84 : Assumption84 P.sys h82.sel) (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    Nonempty (Prop81General.Prop81ConclusionM P 𝔼 t0) :=
  ⟨Prop81General.prop81 P (splitOf P h82 hi h83 h84) 𝔼 t0⟩

/-- Woodford (2003), **Proposition 8.1**, p. 553, deterministic case, exactly as stated (the
hypothesis structure `TargetCriterion.Prop81.Prop81Conclusion`), under Assumptions 8.2 (i),
8.3 and 8.4. -/
theorem prop81_of_assumptions_perfectForesight {ιτ : Type*} [Fintype ιτ]
    (P : LQProblem ιZ ιz ιτ) (h82 : Assumption82 P.sys P.β) (hi : ConjClosed h82.sel)
    (h83 : Assumption83 P.sys) (h84 : Assumption84 P.sys h82.sel) (t0 : ℕ) :
    Nonempty (TargetCriterion.Prop81.Prop81Conclusion P perfectForesight t0) :=
  ⟨Prop81General.prop81_perfectForesight P (splitOf P h82 hi h83 h84) t0⟩

/-! ### Proposition 8.2 under Assumptions 8.1–8.5 -/

/-- Woodford (2003), Assumption 8.5, App. G.2, p. 719: `B₂'` and `B₂'Λʲ`, `j = 1, …, k − 1`, are
linearly independent, and so are `B₂'Λʲ`, `j = 1, …, k` (`k = rank Λ`). -/
def Assumption85 {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℝ) (B2 : ι → ℝ) :
    Prop :=
  LinearIndependent ℝ (fun j : Fin Λ.rank => B2 ᵥ* Λ ^ j.val) ∧
    TargetCriterion.Krylov.Assumption85b Λ B2

/-- Woodford (2003), **Proposition 8.2**, p. 555, **under Assumptions 8.1–8.5** (Assumption 8.2
in case (i)), with the matrices of Proposition 8.1 built in `prop81_of_assumptions`: for a lag
length `D ≥ max(1, rank Ẽ)` with `D < t₀` and a bounded history consistent with an optimal
commitment chosen in the past, commitment to the target criterion (1.23) at all `t ≥ t₀`
determines, for every bounded adapted disturbance process and initial condition, a unique
bounded equilibrium; it is optimal subject to the initial constraint (1.27) `Ẽ z_{t₀} = ē`, i.e.
the rule is robustly optimal (any expectation system with pull-out). -/
theorem prop82_of_assumptions {Ω ιτ : Type*} [Fintype ιτ] {P : LQProblem ιZ ιz ιτ}
    {𝔼 : ExpectationSystem Ω} {t0 : ℕ} (hpull : 𝔼.PullOut) (hA : Prop82General.Assumption81M P 𝔼 t0)
    (h82 : Assumption82 P.sys P.β) (hi : ConjClosed h82.sel) (h83 : Assumption83 P.sys)
    (h84 : Assumption84 P.sys h82.sel)
    (h85 : Assumption85 (Λmat P.sys P.β (splitOf P h82 hi h83 h84).J) P.sys.B2) {D : ℕ}
    (hD : D + 1 ≤ t0) (hDk : P.sys.Et.rank ≤ D) {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : TargetCriterion.Prop82.HistoryOK (Λmat P.sys P.β (splitOf P h82 hi h83 h84).J)
      P.sys.B2 t0 D Mh qh vh) (hMhb : BoundedV Mh) (hMhk : AdaptedV 𝔼 Mh) (hqhb : BoundedV qh)
    (hvhb : ∃ K, ∀ t ω, |vh t ω| ≤ K) :
    RobustlyOptimal (κ := ιz) P 𝔼 t0
      (fun _ y => Prop82General.Prop82M.CriterionM
        (Prop81General.prop81 P (splitOf P h82 hi h83 h84) 𝔼 t0) D qh vh y)
      (fun _ y t ω => zpart (y t ω)) :=
  Prop82General.prop82_of_split hpull hA _ h85.2 hD hDk hhist hMhb hMhk hqhb hvhb

/-- Woodford (2003), Proposition 8.2, p. 555, and (1.17), (1.24) **under Assumptions 8.1–8.5**:
in the equilibrium (the FOC solution with the recovered initial multipliers), there is one
matrix `C` such that at every date `t ≥ t₀` the multipliers `M_{t-1}` are the time-invariant
linear rule `gRule` of the predetermined state (1.24) (lags `1, …, D` of `q` and `v`). -/
theorem prop82_multiplier_rule_of_assumptions {Ω ιτ : Type*} [Fintype ιτ]
    {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (h82 : Assumption82 P.sys P.β) (hi : ConjClosed h82.sel) (h83 : Assumption83 P.sys)
    (h84 : Assumption84 P.sys h82.sel)
    (h85 : Assumption85 (Λmat P.sys P.β (splitOf P h82 hi h83 h84).J) P.sys.B2) {D : ℕ}
    (hD : D + 1 ≤ t0) (hD1 : 1 ≤ D) (hDk : P.sys.Et.rank ≤ D) {Mh qh : ℕ → Ω → ιz → ℝ}
    {vh : ℕ → Ω → ℝ}
    (hhist : TargetCriterion.Prop82.HistoryOK (Λmat P.sys P.β (splitOf P h82 hi h83 h84).J)
      P.sys.B2 t0 D Mh qh vh) {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (hs : GeneralFOC.LQ.FOCSystem P 𝔼 c t0 Z0 (Mh (t0 - 1)) y φ) :
    ∃ C : Matrix ιz (Fin (Λmat P.sys P.β (splitOf P h82 hi h83 h84).J).rank) ℝ,
      ∀ t, t0 ≤ t → ∀ ω, GeneralFOC.LQ.Mpart (φ t ω) =
        Prop82General.KrylovBound.gRule (Λmat P.sys P.β (splitOf P h82 hi h83 h84).J)
          P.sys.B2 C D
          (fun i => TargetCriterion.Recursion.splice t0 qh
            (Prop81General.Qop 𝔼 (splitOf P h82 hi h83 h84) (TargetCriterion.Prop81.xproc P y))
            (t - D + i) ω)
          (fun i => TargetCriterion.Recursion.splice t0 vh (TargetCriterion.Prop81.vproc P y)
            (t - D + i) ω) := by
  have hrk : (Λmat P.sys P.β (splitOf P h82 hi h83 h84).J).rank ≤ D := by
    rw [Prop81General.rank_Λmat P.sys P.β_pos.ne' (splitOf P h82 hi h83 h84).K_det]
    exact hDk
  exact Prop82General.Prop82M.prop82M_multiplier_rule
    (Prop81General.prop81 P (splitOf P h82 hi h83 h84) 𝔼 t0) h85.2 hD hD1 hrk hhist hs

/-! ### The degree of `α(L)` (E18 made precise) -/

omit [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), App. G.1: block form of `J' v` over `ℂ`. -/
theorem J_transpose_mulVec_C (J : Matrix (ιZ ⊕ ιz) ιZ ℝ) (v : ιZ ⊕ ιz → ℂ) :
    (J.map Complex.ofReal)ᵀ *ᵥ v = ((J1 J).map Complex.ofReal)ᵀ *ᵥ (v ∘ Sum.inl) +
      ((J2 J).map Complex.ofReal)ᵀ *ᵥ (v ∘ Sum.inr) := by
  funext j
  simp [mulVec, dotProduct, Fintype.sum_sum_type, J1, J2]

/-- Woodford (2003), App. G.1 and p. 553: every nonzero root `μ` of (1.15) that is **not**
selected gives the eigenvalue `(βμ)⁻¹` of `Λ = β⁻¹ K⁻¹ Ẽ'`. (Its left eigenvector `e`,
`A'e = μ Î'e`, has `J'Î'e = 0` because `μ` is not an eigenvalue of `Ψ`, so `e_Z = Υ e_z`, and
the `z`-rows give `K e_z = μ Ẽ' e_z`.) -/
theorem unselected_eig (R : RealSelection S sel) (hJ1 : (J1 R.J).det ≠ 0)
    (hK : (Kmat S R.J).det ≠ 0) {β : ℝ} (hβ : β ≠ 0) {μ : ℂ} (hroot : S.pencilPoly.eval μ = 0)
    (hμ0 : μ ≠ 0) (hμs : μ ∉ sel) :
    (Matrix.scalar ιz ((β : ℂ) * μ)⁻¹ - (Λmat S β R.J).map Complex.ofReal).det = 0 := by
  have hdetT : ((S.Ahat.map Complex.ofReal - μ • S.Ihat.map Complex.ofReal)ᵀ).det = 0 := by
    rw [det_transpose, ← pencilPoly_eval]
    exact hroot
  obtain ⟨e, he0, he⟩ := exists_mulVec_eq_zero_iff.mpr hdetT
  have hAe : (S.Ahat.map Complex.ofReal)ᵀ *ᵥ e = μ • ((S.Ihat.map Complex.ofReal)ᵀ *ᵥ e) := by
    rw [transpose_sub, transpose_smul, sub_mulVec, sub_eq_zero, smul_mulVec] at he
    exact he
  set eZ : ιZ → ℂ := e ∘ Sum.inl with heZ
  set ez : ιz → ℂ := e ∘ Sum.inr with hez
  have hAblock : (S.Ahat.map Complex.ofReal)ᵀ *ᵥ e =
      Sum.elim ((S.A11.map Complex.ofReal)ᵀ *ᵥ eZ + (S.A21.map Complex.ofReal)ᵀ *ᵥ ez)
        ((S.A12.map Complex.ofReal)ᵀ *ᵥ eZ + (S.A22.map Complex.ofReal)ᵀ *ᵥ ez) := by
    rw [LinearRESystem.Ahat, fromBlocks_map, fromBlocks_transpose, fromBlocks_mulVec]
  have hIblock : (S.Ihat.map Complex.ofReal)ᵀ *ᵥ e =
      Sum.elim eZ ((S.Et.map Complex.ofReal)ᵀ *ᵥ ez) := by
    rw [LinearRESystem.Ihat, fromBlocks_map, fromBlocks_transpose, fromBlocks_mulVec]
    simp [heZ, hez]
  -- `w = J'Î'e = 0`
  have hw : (R.J.map Complex.ofReal)ᵀ *ᵥ ((S.Ihat.map Complex.ofReal)ᵀ *ᵥ e) = 0 := by
    have hdefT : (R.J.map Complex.ofReal)ᵀ * (S.Ahat.map Complex.ofReal)ᵀ =
        (R.Ψ.map Complex.ofReal)ᵀ * ((R.J.map Complex.ofReal)ᵀ *
          (S.Ihat.map Complex.ofReal)ᵀ) := by
      rw [← transpose_mul, ← map_ofReal_mul, R.deflate, map_ofReal_mul, map_ofReal_mul,
        transpose_mul, transpose_mul]
    have h1 := congrArg (· *ᵥ e) hdefT
    rw [← mulVec_mulVec, hAe, mulVec_smul, ← mulVec_mulVec, ← mulVec_mulVec] at h1
    by_contra hw0
    have hdet0 : (Matrix.scalar ιZ μ - R.Ψ.map Complex.ofReal).det = 0 := by
      rw [← det_transpose]
      set w := (R.J.map Complex.ofReal)ᵀ *ᵥ ((S.Ihat.map Complex.ofReal)ᵀ *ᵥ e) with hwdef
      refine exists_mulVec_eq_zero_iff.mp ⟨w, hw0, ?_⟩
      have hsc : (Matrix.scalar ιZ μ)ᵀ *ᵥ w = μ • w := by
        funext i
        simp [Matrix.scalar_apply, mulVec_diagonal]
      rw [transpose_sub, sub_mulVec, hsc, h1, sub_self]
    rcases R.eig μ hdet0 with h | h
    · exact hμ0 h
    · exact hμs h
  rw [hIblock, J_transpose_mulVec_C] at hw
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at hw
  -- `e_Z = Υ e_z`
  have hJΥ : (J1 R.J)ᵀ * Υmat S R.J = -((J2 R.J)ᵀ * S.Etᵀ) := by
    have hu : IsUnit ((J1 R.J)ᵀ).det := by rw [det_transpose]; exact Ne.isUnit hJ1
    rw [Υmat, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hu,
      Matrix.one_mul]
  have hJΥc : ((J1 R.J).map Complex.ofReal)ᵀ * (Υmat S R.J).map Complex.ofReal =
      -(((J2 R.J).map Complex.ofReal)ᵀ * (S.Et.map Complex.ofReal)ᵀ) := by
    rw [← transpose_map, ← map_ofReal_mul, hJΥ, ← transpose_map, ← transpose_map,
      ← map_ofReal_mul]
    ext i j
    simp
  have hEZ : eZ = (Υmat S R.J).map Complex.ofReal *ᵥ ez := by
    have hd : (((J1 R.J).map Complex.ofReal)ᵀ).det ≠ 0 := by
      have e2 := Complex.ofRealHom.map_det (J1 R.J)
      rw [RingHom.mapMatrix_apply] at e2
      change ((J1 R.J).det : ℂ) = ((J1 R.J).map Complex.ofReal).det at e2
      rw [det_transpose, ← e2]
      exact_mod_cast hJ1
    have : ((J1 R.J).map Complex.ofReal)ᵀ *ᵥ (eZ - (Υmat S R.J).map Complex.ofReal *ᵥ ez) =
        0 := by
      rw [mulVec_sub, mulVec_mulVec, hJΥc, neg_mulVec, sub_neg_eq_add, ← mulVec_mulVec]
      exact hw
    exact sub_eq_zero.mp (eq_zero_of_mulVec_eq_zero hd this)
  -- the `z`-rows: `K e_z = μ Ẽ' e_z`
  have hz := congrArg (· ∘ Sum.inr) hAe
  simp only [hAblock, hIblock, Sum.elim_comp_inr] at hz
  have hz' : (S.A12.map Complex.ofReal)ᵀ *ᵥ eZ + (S.A22.map Complex.ofReal)ᵀ *ᵥ ez =
      μ • ((S.Et.map Complex.ofReal)ᵀ *ᵥ ez) := by
    funext r
    have := congrFun hz r
    simpa using this
  have hKe : (Kmat S R.J).map Complex.ofReal *ᵥ ez = μ • ((S.Et.map Complex.ofReal)ᵀ *ᵥ ez) := by
    rw [← hz', hEZ, Kmat]
    have hm : (S.A22ᵀ + S.A12ᵀ * Υmat S R.J).map Complex.ofReal =
        (S.A22.map Complex.ofReal)ᵀ + (S.A12.map Complex.ofReal)ᵀ *
          (Υmat S R.J).map Complex.ofReal := by
      rw [Matrix.map_add _ Complex.ofReal_add, map_ofReal_mul, transpose_map, transpose_map]
    rw [hm, add_mulVec, ← mulVec_mulVec]
    abel
  -- `K Λ = β⁻¹ Ẽ'`
  have hKΛ : Kmat S R.J * Λmat S β R.J = β⁻¹ • S.Etᵀ := by
    rw [Λmat, Matrix.mul_smul, ← Matrix.mul_assoc, mul_nonsing_inv _ (Ne.isUnit hK),
      Matrix.one_mul]
  have hKΛc : (Kmat S R.J).map Complex.ofReal * (Λmat S β R.J).map Complex.ofReal =
      (β : ℂ)⁻¹ • (S.Et.map Complex.ofReal)ᵀ := by
    rw [← map_ofReal_mul, hKΛ]
    ext i j
    simp
  have hKc : ((Kmat S R.J).map Complex.ofReal).det ≠ 0 := by
    have e2 := Complex.ofRealHom.map_det (Kmat S R.J)
    rw [RingHom.mapMatrix_apply] at e2
    change ((Kmat S R.J).det : ℂ) = ((Kmat S R.J).map Complex.ofReal).det at e2
    rw [← e2]
    exact_mod_cast hK
  have hβc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ
  have hΛ : (Λmat S β R.J).map Complex.ofReal *ᵥ ez = ((β : ℂ) * μ)⁻¹ • ez := by
    have h1 : (Kmat S R.J).map Complex.ofReal *ᵥ
        ((Λmat S β R.J).map Complex.ofReal *ᵥ ez - ((β : ℂ) * μ)⁻¹ • ez) = 0 := by
      rw [mulVec_sub, mulVec_mulVec, hKΛc, mulVec_smul, hKe, smul_mulVec, smul_smul,
        sub_eq_zero]
      congr 1
      field_simp
    exact sub_eq_zero.mp (eq_zero_of_mulVec_eq_zero hKc h1)
  have hez0 : ez ≠ 0 := by
    intro h0
    apply he0
    funext a
    rcases a with i | r
    · have := congrFun hEZ i
      rw [h0, mulVec_zero] at this
      exact this
    · exact congrFun h0 r
  refine exists_mulVec_eq_zero_iff.mp ⟨ez, hez0, ?_⟩
  rw [sub_mulVec, hΛ, sub_eq_zero]
  funext r
  simp [Matrix.scalar_apply, mulVec_diagonal]

/-- Woodford (2003), (1.22): `α(L) = det(I − ΛL)` commutes with complexification. -/
theorem alpha_map_ofReal (Λ : Matrix ιz ιz ℝ) :
    (Adjugate.alpha Λ).map Complex.ofRealHom = Adjugate.alpha (Λ.map Complex.ofReal) := by
  have e := (Polynomial.mapRingHom Complex.ofRealHom).map_det (Adjugate.lagMat Λ)
  rw [Adjugate.alpha, Adjugate.alpha, ← Polynomial.coe_mapRingHom, e]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Adjugate.lagMat, RingHom.mapMatrix_apply]
  · simp [Adjugate.lagMat, RingHom.mapMatrix_apply, Matrix.one_apply_ne hij]

/-- Woodford (2003), Assumptions 8.2–8.3: the nonzero roots of (1.15) that are not selected. -/
noncomputable def unselected (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) : Multiset ℂ :=
  nonzeroRoots S - sel

/-- Woodford (2003), Assumptions 8.2–8.3 (p. 552, App. G.1): there are exactly `rank Ẽ`
unselected nonzero roots, all distinct; each is a root, nonzero and not selected. -/
theorem unselected_spec {β : ℝ} (h82 : Assumption82 S β) (h83 : Assumption83 S) :
    (unselected S h82.sel).Nodup ∧ Multiset.card (unselected S h82.sel) = S.Et.rank ∧
      ∀ μ ∈ unselected S h82.sel, S.pencilPoly.eval μ = 0 ∧ μ ≠ 0 ∧ μ ∉ h82.sel := by
  have hsel_le : h82.sel ≤ nonzeroRoots S :=
    h82.sel_le.trans (Multiset.monotone_filter_right _ fun μ h => h.1)
  refine ⟨Multiset.nodup_of_le (Multiset.sub_le_self _ _) h83.nodup, ?_, ?_⟩
  · rw [unselected, Multiset.card_sub hsel_le, h83.card_nonzero]
    have h1 := h82.sel_card
    have h2 := card_le_rank_Ahat S
    have h3 : Fintype.card (ιZ ⊕ ιz) = Fintype.card ιZ + Fintype.card ιz := Fintype.card_sum
    have h4 : S.Ahat.rank ≤ Fintype.card (ιZ ⊕ ιz) := rank_le_card_width _
    omega
  · intro μ hμ
    rw [unselected, Multiset.mem_sub_of_nodup h83.nodup] at hμ
    obtain ⟨h1, h2⟩ := hμ
    simp only [nonzeroRoots, Multiset.mem_filter, Polynomial.mem_roots h83.regular] at h1
    exact ⟨h1.1, h1.2, h2⟩

/-- Woodford (2003), p. 553: the eigenvalues `(βμ)⁻¹` of `Λ` from the unselected roots form a
sub-multiset of the nonzero roots of the characteristic polynomial of `Λ` (over `ℂ`). -/
theorem unselected_map_le {β : ℝ} (hβ : 0 < β) (h82 : Assumption82 S β)
    (R : RealSelection S h82.sel) (h83 : Assumption83 S) (h84 : Assumption84 S h82.sel) :
    (unselected S h82.sel).map (fun μ => ((β : ℂ) * μ)⁻¹) ≤
      ((Λmat S β (splitOfSel hβ h82 R h83 h84).J).map Complex.ofReal).charpoly.roots.filter
        (fun x => x ≠ 0) := by
  set D := splitOfSel hβ h82 R h83 h84 with hD
  obtain ⟨hUnd, -, hmemU⟩ := unselected_spec h82 h83
  have hβc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
  have hinj : ∀ μ ∈ unselected S h82.sel, ∀ ν ∈ unselected S h82.sel,
      ((β : ℂ) * μ)⁻¹ = ((β : ℂ) * ν)⁻¹ → μ = ν := by
    intro μ _ ν _ h
    exact mul_left_cancel₀ hβc (inv_injective h)
  rw [Multiset.le_iff_subset (Multiset.Nodup.map_on hinj hUnd)]
  intro x hx
  obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.mp hx
  obtain ⟨hr, h0, hs⟩ := hmemU μ hμ
  rw [Multiset.mem_filter, Polynomial.mem_roots (charpoly_monic _).ne_zero, IsRoot,
    eval_charpoly]
  exact ⟨unselected_eig R D.J1_det D.K_det hβ.ne' hr h0 hs, inv_ne_zero (mul_ne_zero hβc h0)⟩

/-- Woodford (2003), p. 553 and fn 15 (**E18 made precise; the book's claim holds under its
assumptions**): under Assumptions 8.2 (case (i)), 8.3 and 8.4, the matrix `Λ` of Proposition 8.1
has `rank Λ = rank Ẽ` and `deg α(L) = rank Ẽ`, `α(L) = det(I − ΛL)`. The `rank Ẽ` nonzero roots
of (1.15) not selected give `rank Ẽ` distinct nonzero eigenvalues `(βμ)⁻¹` of `Λ`
(`unselected_eig`), and `deg α ≤ rank Λ` always. (Without the assumptions only
`deg α ≤ rank Λ` holds: `Adjugate.nilpotent_counterexample`.) -/
theorem natDegree_alpha_eq_rank {β : ℝ} (hβ : 0 < β) (h82 : Assumption82 S β)
    (R : RealSelection S h82.sel) (h83 : Assumption83 S) (h84 : Assumption84 S h82.sel) :
    (Adjugate.alpha (Λmat S β (splitOfSel hβ h82 R h83 h84).J)).natDegree = S.Et.rank ∧
      (Λmat S β (splitOfSel hβ h82 R h83 h84).J).rank = S.Et.rank := by
  set D := splitOfSel hβ h82 R h83 h84 with hD
  have hrank := Prop81General.rank_Λmat S hβ.ne' D.K_det
  refine ⟨le_antisymm ((Adjugate.natDegree_alpha_le_rank _).trans hrank.le) ?_, hrank⟩
  have hle := Multiset.card_le_card (unselected_map_le hβ h82 R h83 h84)
  rw [Multiset.card_map, (unselected_spec h82 h83).2.1,
    ← Adjugate.natDegree_alpha_eq_card_nonzero_roots, ← alpha_map_ofReal,
    natDegree_map_eq_of_injective Complex.ofRealHom.injective] at hle
  exact hle

/-- Woodford (2003), p. 553: under Assumptions 8.2 (i)–8.4 the nonzero eigenvalues of `Λ` are
exactly the `(βμ)⁻¹` for the unselected nonzero roots `μ` (as multisets). -/
theorem nonzero_eig_eq {β : ℝ} (hβ : 0 < β) (h82 : Assumption82 S β)
    (R : RealSelection S h82.sel) (h83 : Assumption83 S) (h84 : Assumption84 S h82.sel) :
    (unselected S h82.sel).map (fun μ => ((β : ℂ) * μ)⁻¹) =
      ((Λmat S β (splitOfSel hβ h82 R h83 h84).J).map Complex.ofReal).charpoly.roots.filter
        (fun x => x ≠ 0) := by
  refine Multiset.eq_of_le_of_card_le (unselected_map_le hβ h82 R h83 h84) ?_
  rw [Multiset.card_map, (unselected_spec h82 h83).2.1,
    ← Adjugate.natDegree_alpha_eq_card_nonzero_roots, ← alpha_map_ofReal,
    natDegree_map_eq_of_injective Complex.ofRealHom.injective]
  exact (natDegree_alpha_eq_rank hβ h82 R h83 h84).1.le

/-! ### The stability hypothesis `MultStable` of `TargetCriterion` fails under Assumption 8.7 -/

/-- Woodford (2003), (1.20): with zero forcing the multiplier recursion is `m_k = Λ^{k+1} m₀`. -/
theorem mrec_zero {Ω' ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℝ)
    (m0 : Ω' → ι → ℝ) (k : ℕ) (ω : Ω') :
    TargetCriterion.Recursion.mrec Λ m0 (fun _ _ _ => 0) k ω = (Λ ^ (k + 1)) *ᵥ m0 ω := by
  induction k with
  | zero =>
    funext i
    simp [TargetCriterion.Recursion.mrec]
  | succ k ih =>
    have e : TargetCriterion.Recursion.mrec Λ m0 (fun _ _ _ => 0) (k + 1) ω =
        Λ *ᵥ TargetCriterion.Recursion.mrec Λ m0 (fun _ _ _ => 0) k ω + fun _ => 0 := rfl
    rw [e, ih, mulVec_mulVec, ← pow_succ']
    funext i
    simp

/-- Woodford (2003), (1.20): a real matrix with a complex eigenvalue of modulus `> 1` is not
`MultStable` (the hypothesis of `TargetCriterion.Prop82`): the recursion from the real or the
imaginary part of an eigenvector explodes. -/
theorem not_multStable_of_eig {Ω' ι : Type*} [Nonempty Ω'] [Fintype ι] [DecidableEq ι]
    {Λ : Matrix ι ι ℝ} {θ : ℂ} (hθ : 1 < ‖θ‖)
    (h : (Matrix.scalar ι θ - Λ.map Complex.ofReal).det = 0) :
    ¬ TargetCriterion.Recursion.MultStable Ω' Λ := by
  intro hst
  obtain ⟨v, hv0, hv⟩ := exists_eigvec h
  have hpow : ∀ k, (Λ.map Complex.ofReal) ^ k *ᵥ v = θ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hv, smul_smul, pow_succ, mul_comm]
  have hmapk : ∀ k, (Λ ^ k).map Complex.ofReal = (Λ.map Complex.ofReal) ^ k := fun k =>
    Complex.ofRealHom.mapMatrix.map_pow Λ k
  have hre : ∀ k i, ((Λ ^ k) *ᵥ fun a => (v a).re) i = ((θ ^ k • v) i).re := by
    intro k i
    rw [← hpow k, ← hmapk k]
    simp [mulVec, dotProduct, Complex.re_sum]
  have him : ∀ k i, ((Λ ^ k) *ᵥ fun a => (v a).im) i = ((θ ^ k • v) i).im := by
    intro k i
    rw [← hpow k, ← hmapk k]
    simp [mulVec, dotProduct, Complex.im_sum]
  obtain ⟨K1, hK1⟩ := hst (fun _ a => (v a).re) (fun _ _ _ => 0) ⟨∑ a, |(v a).re|,
    fun _ i => Finset.single_le_sum (f := fun a => |(v a).re|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)⟩ ⟨0, fun _ _ _ => by simp⟩
  obtain ⟨K2, hK2⟩ := hst (fun _ a => (v a).im) (fun _ _ _ => 0) ⟨∑ a, |(v a).im|,
    fun _ i => Finset.single_le_sum (f := fun a => |(v a).im|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)⟩ ⟨0, fun _ _ _ => by simp⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
  have hvi : 0 < ‖v i‖ := norm_pos_iff.mpr hi
  have ω0 : Ω' := Classical.arbitrary Ω'
  have hbound : ∀ k : ℕ, ‖θ‖ ^ (k + 1) * ‖v i‖ ≤ K1 + K2 := by
    intro k
    have h1 := hK1 k ω0 i
    have h2 := hK2 k ω0 i
    rw [mrec_zero, hre] at h1
    rw [mrec_zero, him] at h2
    calc ‖θ‖ ^ (k + 1) * ‖v i‖ = ‖(θ ^ (k + 1) • v) i‖ := by
          rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_pow]
      _ ≤ |((θ ^ (k + 1) • v) i).re| + |((θ ^ (k + 1) • v) i).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ ≤ K1 + K2 := add_le_add h1 h2
  have htend : Filter.Tendsto (fun k : ℕ => ‖θ‖ ^ (k + 1) * ‖v i‖) Filter.atTop
      Filter.atTop :=
    ((tendsto_pow_atTop_atTop_of_one_lt hθ).comp (Filter.tendsto_add_atTop_nat 1)).atTop_mul_const
      hvi
  obtain ⟨k, hk⟩ := (htend.eventually_gt_atTop (K1 + K2)).exists
  exact absurd (hbound k) (not_le.mpr hk)

/-- Woodford (2003), Assumption 8.7 (p. 556) vs the hypothesis `MultStable` of
`TargetCriterion.Prop82`: under Assumptions 8.2 (i)–8.4, if some nonzero root `μ` of (1.15)
with `|μ| < β⁻¹` is **not** selected — which happens exactly when (1.15) has more than `n_Z`
roots with `|μ| < β⁻¹`, Assumption 8.7, true under the Sargent–Wallace property in all the book's
examples — then `Λ` has the eigenvalue `(βμ)⁻¹` of modulus `> 1` and `MultStable` fails. So the
earlier conditional Proposition 8.2 was vacuous in the book's applications;
`Prop82General` removes the hypothesis. -/
theorem not_multStable_of_unselected {Ω' : Type*} [Nonempty Ω'] {β : ℝ} (hβ : 0 < β)
    (h82 : Assumption82 S β) (R : RealSelection S h82.sel) (h83 : Assumption83 S)
    (h84 : Assumption84 S h82.sel) {μ : ℂ} (hroot : S.pencilPoly.eval μ = 0) (hμ0 : μ ≠ 0)
    (hμs : μ ∉ h82.sel) (hin : ‖μ‖ < β⁻¹) :
    ¬ TargetCriterion.Recursion.MultStable Ω' (Λmat S β (splitOfSel hβ h82 R h83 h84).J) := by
  set D := splitOfSel hβ h82 R h83 h84
  refine not_multStable_of_eig ?_ (unselected_eig R D.J1_det D.K_det hβ.ne' hroot hμ0 hμs)
  rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ]
  have h1 : β * ‖μ‖ < 1 := by
    have := mul_lt_mul_of_pos_left hin hβ
    rwa [mul_inv_cancel₀ hβ.ne'] at this
  have h2 : 0 < β * ‖μ‖ := mul_pos hβ (norm_pos_iff.mpr hμ0)
  exact one_lt_inv₀ h2 |>.mpr h1

end Woodford.OptimalPolicyRules.PencilAssumptions
