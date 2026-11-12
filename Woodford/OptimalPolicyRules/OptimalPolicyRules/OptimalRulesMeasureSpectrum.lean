/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.OptimalRulesMeasureCounterexample
import OptimalPolicyRules.OptimalRulesMeasureModelsProp82

/-!
# The spectrum of `H` and the characteristic roots

Woodford (2003), *Interest and Prices*, Chapter 8: the state transition
`(Z_{t+1}, M_t) = h + H (Z_t, M_{t−1})` of the optimal plan (p. 539,
`OptimalRulesMeasureGeneral.Hgen`), the characteristic polynomial (1.15) `det[A − μÎ]` of the
structural system (p. 546, `GeneralSetup.LinearRESystem.pencilPoly`) and the roots selected by a
deflating split (App. G.1, `PencilSplit.DeflatingSplit`).

## The relation

* **`H`'s eigenvalues are not the roots of (1.15)** selected by the split: (1.15) involves only
  the constraints `(A, Î)`, while `H` is the closed loop of the optimal plan and depends on the
  loss `(T, W)`; `H` is `(n_Z + n_z)`-square while the split selects `n_Z` roots. In the basic
  model (`n_Z = 0`) the split selects no root, but `H` has an eigenvalue
  (`nk_spec_not_selected`).
* **The exact relation** (`eig_Hgen_iff`): under the perfect-foresight Assumption 8.1, `ν` is an
  eigenvalue of `H` **iff** `|ν| ≤ 1` and `ν` is a root of the **Euler pencil** of (1.1) + (1.9),
  i.e. (1.1) + (1.9) with no disturbance and `τ* = 0` has a solution of the form
  `(y_t, φ_t) = νᵗ(u, p)`, `(u, p) ≠ 0` (`EulerRoot`):
  `ν Ĩu = Ãu` and `ν Ã'p + T'WTu − β⁻¹Ĩ'p = 0`.
  Forward: the eigenvector `v` of `H` generates the homogeneous solution `νᵗ(D_Y v, D_Φ v)`;
  backward: the real and imaginary parts of a bounded eigen-solution are bounded solutions, so by
  uniqueness they are the plans from their initial states, and these states form an eigenvector.
* **The root condition on the book's pencil** (`powDecay_Hgen_iff_noEulerRoot`): `H` is
  geometrically stable iff the Euler pencil has no root on the unit circle; under that condition
  the measure Assumption 8.1 holds for every bounded adapted disturbance on every filtered
  probability space (`m_assumption81MB_of_noEulerRoot`). In the counterexample
  `OptimalRulesMeasureCounterexample.eBP` the Euler pencil has the root `1` (`eB_eulerRoot_one`).
-/

namespace Woodford.OptimalPolicyRules.OptimalRulesMeasureSpectrum

open Filter Topology Matrix GeneralSetup GeneralFOC GeneralFOC.LQ
open OptimalRulesMeasureKernel OptimalRulesMeasureGeneral

variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-! ### Real and imaginary parts -/

/-- Woodford (2003), App. G.1 (tool): the real part of a complexified (rectangular) matrix–vector
product. -/
theorem re_mulVec_apply {m n : Type*} [Fintype n] (K : Matrix m n ℝ) (v : n → ℂ) (i : m) :
    ((K.map Complex.ofReal *ᵥ v) i).re = (K *ᵥ fun j => (v j).re) i := by
  simp [Matrix.mulVec, dotProduct, Complex.re_sum]

/-- Woodford (2003), App. G.1 (tool): the imaginary part of a complexified (rectangular)
matrix–vector product. -/
theorem im_mulVec_apply {m n : Type*} [Fintype n] (K : Matrix m n ℝ) (v : n → ℂ) (i : m) :
    ((K.map Complex.ofReal *ᵥ v) i).im = (K *ᵥ fun j => (v j).im) i := by
  simp [Matrix.mulVec, dotProduct, Complex.im_sum]

/-- Woodford (2003), App. G.1 (tool): the eigenvalues of a power-bounded real matrix lie in the
closed unit disc. -/
theorem eig_norm_le_one {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℝ}
    (hb : OptimalRulesMeasureMarkov.PowBdd H) {ν : ℂ} {v : ι → ℂ}
    (hv : H.map Complex.ofReal *ᵥ v = ν • v) (hv0 : v ≠ 0) : ‖ν‖ ≤ 1 := by
  by_contra h1
  push Not at h1
  obtain ⟨K, hK⟩ := hb
  set Hc := H.map Complex.ofReal with hHc
  have hpow : ∀ k, Hc ^ k *ᵥ v = ν ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hv, smul_smul, pow_succ', mul_comm]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
  have hvi : 0 < ‖v i‖ := norm_pos_iff.mpr hi
  set C := ∑ j, |K| * ‖v j‖ with hC
  have hbound : ∀ k, ‖ν‖ ^ k * ‖v i‖ ≤ C := by
    intro k
    have e := congrFun (hpow k) i
    have hmap : Hc ^ k = (H ^ k).map Complex.ofReal := by
      rw [hHc]
      exact (Matrix.map_pow H Complex.ofRealHom k).symm
    rw [hmap] at e
    have : ‖ν ^ k • v i‖ ≤ C := by
      rw [← Pi.smul_apply, ← e]
      calc ‖((H ^ k).map Complex.ofReal *ᵥ v) i‖
          = ‖∑ j, ((H ^ k) i j : ℂ) * v j‖ := rfl
        _ ≤ ∑ j, ‖((H ^ k) i j : ℂ) * v j‖ := norm_sum_le _ _
        _ ≤ C := Finset.sum_le_sum fun j _ => by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right ((hK k i j).trans (le_abs_self _)) (norm_nonneg _)
    rwa [norm_smul, norm_pow] at this
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (C / ‖v i‖) h1
  have := hbound k
  rw [div_lt_iff₀ hvi] at hk
  linarith

/-! ### The Euler pencil of (1.1) + (1.9) -/

/-- Woodford (2003), (1.1) and (1.9), pp. 537–541: `(u, p)` and `ν` give the eigen-solution
`(y_t, φ_t) = νᵗ(u, p)` of the homogeneous system (no disturbance, `τ* = 0`) under perfect
foresight: `ν Ĩu = Ãu` and `ν Ã'p + T'WTu − β⁻¹Ĩ'p = 0` (over `ℂ`). -/
def EulerEq (P : LQProblem ιZ ιz ιτ) (ν : ℂ) (u : (ιZ ⊕ ιz) ⊕ Unit → ℂ) (p : ιZ ⊕ ιz → ℂ) :
    Prop :=
  ν • (P.sys.Itil.map Complex.ofReal *ᵥ u) = P.sys.Atil.map Complex.ofReal *ᵥ u ∧
    ν • (P.sys.Atilᵀ.map Complex.ofReal *ᵥ p) +
        P.Tᵀ.map Complex.ofReal *ᵥ (P.W.map Complex.ofReal *ᵥ (P.T.map Complex.ofReal *ᵥ u)) -
      ((P.β⁻¹ : ℝ) : ℂ) • (P.sys.Itilᵀ.map Complex.ofReal *ᵥ p) = 0

/-- Woodford (2003), (1.1) + (1.9), pp. 537–541: `ν` is a **root of the Euler pencil** — the
homogeneous perfect-foresight system has a nonzero solution `νᵗ(u, p)`. -/
def EulerRoot (P : LQProblem ιZ ιz ιτ) (ν : ℂ) : Prop :=
  ∃ (u : (ιZ ⊕ ιz) ⊕ Unit → ℂ) (p : ιZ ⊕ ιz → ℂ), (u ≠ 0 ∨ p ≠ 0) ∧ EulerEq P ν u p

/-! ### The responses to the initial state -/

variable {P : LQProblem ιZ ιz ιτ} (hA81 : Assumption81 P perfectForesight 0)

/-- Woodford (2003), p. 539 (tool): the response of the date-`d` plan to the initial state
`(Z_0, M_{−1})` with zero forcing (column `j`: the plan from `e_j` minus the plan from `0`). -/
noncomputable def DY (d : ℕ) : Matrix ((ιZ ⊕ ιz) ⊕ Unit) (ιZ ⊕ ιz) ℝ :=
  Matrix.of fun a j => solY hA81 (Pi.single j 1) 0 d a - solY hA81 0 0 d a

/-- Woodford (2003), p. 539 (tool): the response of the date-`d` multipliers to the initial
state with zero forcing. -/
noncomputable def DΦ (d : ℕ) : Matrix (ιZ ⊕ ιz) (ιZ ⊕ ιz) ℝ :=
  Matrix.of fun a j => solΦ hA81 (Pi.single j 1) 0 d a - solΦ hA81 0 0 d a

/-- Woodford (2003), p. 539 (tool): `D_Y n` and `D_Φ n` are the plan and multipliers from `n`
minus those from `0` (the solution is affine in the state, `sol0_affine`). -/
theorem D_mulVec (d : ℕ) (n : ιZ ⊕ ιz → ℝ) :
    DY hA81 d *ᵥ n = solY hA81 n 0 d - solY hA81 0 0 d ∧
      DΦ hA81 d *ᵥ n = solΦ hA81 n 0 d - solΦ hA81 0 0 d := by
  obtain ⟨y0, By, p0, Bp, h⟩ := sol0_affine hA81 d
  have hY : DY hA81 d = By := by
    ext a j
    rw [DY, of_apply, (h _).1, (h 0).1]
    simp
  have hΦ : DΦ hA81 d = Bp := by
    ext a j
    rw [DΦ, of_apply, (h _).2, (h 0).2]
    simp
  refine ⟨?_, ?_⟩
  · rw [hY, (h n).1, (h 0).1, mulVec_zero, add_zero, add_sub_cancel_left]
  · rw [hΦ, (h n).2, (h 0).2, mulVec_zero, add_zero, add_sub_cancel_left]

/-- Woodford (2003), p. 539 (tool): `H n` is the date-1 state of `D n`. -/
theorem Hgen_eq_next (n : ιZ ⊕ ιz → ℝ) :
    Hgen hA81 *ᵥ n = nextS hA81 n 0 - nextS hA81 0 0 := by
  have e0 := hgen_spec hA81 0
  rw [mulVec_zero, add_zero] at e0
  rw [hgen_spec hA81 n, e0]
  abel

/-- Woodford (2003), p. 539: **time invariance of the responses**,
`D_Y(1) n = D_Y(0) H n` and `D_Φ(1) n = D_Φ(0) H n`. -/
theorem D_shift (n : ιZ ⊕ ιz → ℝ) :
    DY hA81 1 *ᵥ n = DY hA81 0 *ᵥ (Hgen hA81 *ᵥ n) ∧
      DΦ hA81 1 *ᵥ n = DΦ hA81 0 *ᵥ (Hgen hA81 *ᵥ n) := by
  have hz : (fun j => (0 : ℕ → ιz → ℝ) (j + 1)) = 0 := rfl
  have hs : ∀ m, solY hA81 m 0 1 = solY hA81 (nextS hA81 m 0) 0 0 ∧
      solΦ hA81 m 0 1 = solΦ hA81 (nextS hA81 m 0) 0 0 := by
    intro m
    have := sol_shift hA81 m (bddSeq_zero (ι := ιz)) 0
    rw [hz] at this
    exact this
  refine ⟨?_, ?_⟩
  · rw [(D_mulVec hA81 1 n).1, (hs n).1, (hs 0).1, Hgen_eq_next, mulVec_sub,
      (D_mulVec hA81 0 _).1, (D_mulVec hA81 0 _).1]
    abel
  · rw [(D_mulVec hA81 1 n).2, (hs n).2, (hs 0).2, Hgen_eq_next, mulVec_sub,
      (D_mulVec hA81 0 _).2, (D_mulVec hA81 0 _).2]
    abel

/-- Woodford (2003), p. 541: the responses respect the initial conditions,
`Z_0 = n_Z` and `M_{−1} = n_M`. -/
theorem D_init (n : ιZ ⊕ ιz → ℝ) :
    (∀ j, (DY hA81 0 *ᵥ n) (Sum.inl (Sum.inl j)) = n (Sum.inl j)) ∧
      ∀ r, (DΦ hA81 0 *ᵥ n) (Sum.inr r) = n (Sum.inr r) := by
  have hn := sol_spec hA81 n (bddSeq_zero (ι := ιz))
  have h0 := sol_spec hA81 0 (bddSeq_zero (ι := ιz))
  refine ⟨fun j => ?_, fun r => ?_⟩
  · rw [(D_mulVec hA81 0 n).1, Pi.sub_apply]
    have e1 := congrFun (hn.1.2.1 ()) j
    have e2 := congrFun (h0.1.2.1 ()) j
    simp only [Zpart] at e1 e2
    rw [e1, e2]
    simp
  · rw [(D_mulVec hA81 0 n).2, Pi.sub_apply]
    have e1 := congrFun (hn.2.2.2.1 ()) r
    have e2 := congrFun (h0.2.2.2.1 ()) r
    simp only [Mpart] at e1 e2
    rw [e1, e2]
    simp

/-- Woodford (2003), p. 539: `H n` is the date-1 state `(Z_1, M_0)` of the responses. -/
theorem D_next (n : ιZ ⊕ ιz → ℝ) :
    Hgen hA81 *ᵥ n = Sum.elim (fun j => (DY hA81 1 *ᵥ n) (Sum.inl (Sum.inl j)))
      (fun r => (DΦ hA81 1 *ᵥ n) (Sum.inr r)) := by
  rw [Hgen_eq_next, (D_mulVec hA81 1 n).1, (D_mulVec hA81 1 n).2]
  funext a
  rcases a with j | r <;> simp [nextS, Zpart, Mpart]

/-- Woodford (2003), eq. (1.1), p. 537, under perfect foresight with zero forcing:
`Ĩ y_1 = Ã y_0`. -/
theorem sol_struct (m : ιZ ⊕ ιz → ℝ) :
    P.sys.Itil *ᵥ solY hA81 m 0 1 = P.sys.Atil *ᵥ solY hA81 m 0 0 := by
  obtain ⟨⟨hst, -, -, -⟩, -, -, -, -⟩ := sol_spec hA81 m (bddSeq_zero (ι := ιz))
  have h1 : Zpart (solY hA81 m 0 1) = P.sys.A11 *ᵥ Zpart (solY hA81 m 0 0) +
      P.sys.A12 *ᵥ zpart (solY hA81 m 0 0) := (hst 0 le_rfl ()).1
  have h2 : P.sys.Et *ᵥ zpart (solY hA81 m 0 1) = P.sys.A21 *ᵥ Zpart (solY hA81 m 0 0) +
      P.sys.A22 *ᵥ zpart (solY hA81 m 0 0) + ipart (solY hA81 m 0 0) • P.sys.B2 + 0 :=
    (hst 0 le_rfl ()).2
  rw [add_zero] at h2
  rw [LinearRESystem.Itil_mulVec, LinearRESystem.Atil_mulVec, h1, h2]

/-- Woodford (2003), eq. (1.9), p. 541, at date 0 under perfect foresight with zero forcing. -/
theorem sol_foc (m : ιZ ⊕ ιz → ℝ) :
    P.sys.Atilᵀ *ᵥ solΦ hA81 m 0 1 + P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ solY hA81 m 0 0 - P.τstar)) -
      P.β⁻¹ • (P.sys.Itilᵀ *ᵥ solΦ hA81 m 0 0) = 0 := by
  obtain ⟨-, -, -, -, hfoc⟩ := sol_spec hA81 m (bddSeq_zero (ι := ιz))
  exact hfoc 0 le_rfl ()

/-- Woodford (2003), eq. (1.1), p. 537: the responses solve the homogeneous structural system,
`Ĩ D_Y(1) n = Ã D_Y(0) n`. -/
theorem D_struct (n : ιZ ⊕ ιz → ℝ) :
    P.sys.Itil *ᵥ (DY hA81 1 *ᵥ n) = P.sys.Atil *ᵥ (DY hA81 0 *ᵥ n) := by
  rw [(D_mulVec hA81 1 n).1, (D_mulVec hA81 0 n).1, mulVec_sub, mulVec_sub, sol_struct,
    sol_struct]

/-- Woodford (2003), eq. (1.9), p. 541: the responses solve the homogeneous first-order
conditions, `Ã'D_Φ(1)n + T'WT D_Y(0)n − β⁻¹Ĩ'D_Φ(0)n = 0`. -/
theorem D_foc (n : ιZ ⊕ ιz → ℝ) :
    P.sys.Atilᵀ *ᵥ (DΦ hA81 1 *ᵥ n) + P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ (DY hA81 0 *ᵥ n))) -
      P.β⁻¹ • (P.sys.Itilᵀ *ᵥ (DΦ hA81 0 *ᵥ n)) = 0 := by
  have e1 := sol_foc hA81 n
  have e0 := sol_foc hA81 0
  rw [(D_mulVec hA81 1 n).2, (D_mulVec hA81 0 n).1, (D_mulVec hA81 0 n).2]
  have key : P.sys.Atilᵀ *ᵥ (solΦ hA81 n 0 1 - solΦ hA81 0 0 1) +
      P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ (solY hA81 n 0 0 - solY hA81 0 0 0))) -
      P.β⁻¹ • (P.sys.Itilᵀ *ᵥ (solΦ hA81 n 0 0 - solΦ hA81 0 0 0)) =
      (P.sys.Atilᵀ *ᵥ solΦ hA81 n 0 1 + P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ solY hA81 n 0 0 - P.τstar)) -
        P.β⁻¹ • (P.sys.Itilᵀ *ᵥ solΦ hA81 n 0 0)) -
      (P.sys.Atilᵀ *ᵥ solΦ hA81 0 0 1 + P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ solY hA81 0 0 0 - P.τstar)) -
        P.β⁻¹ • (P.sys.Itilᵀ *ᵥ solΦ hA81 0 0 0)) := by
    simp only [mulVec_sub, smul_sub]
    abel
  rw [key, e1, e0, sub_zero]

/-! ### From an eigenvector of `H` to an eigen-solution -/

/-- Woodford (2003), p. 539 (tool): `D_Y(1)v = D_Y(0)Hv` and `D_Φ(1)v = D_Φ(0)Hv` for complex
`v`. -/
theorem Dc_shift (v : ιZ ⊕ ιz → ℂ) :
    (DY hA81 1).map Complex.ofReal *ᵥ v =
        (DY hA81 0).map Complex.ofReal *ᵥ ((Hgen hA81).map Complex.ofReal *ᵥ v) ∧
      (DΦ hA81 1).map Complex.ofReal *ᵥ v =
        (DΦ hA81 0).map Complex.ofReal *ᵥ ((Hgen hA81).map Complex.ofReal *ᵥ v) := by
  refine ⟨funext fun a => Complex.ext ?_ ?_, funext fun a => Complex.ext ?_ ?_⟩ <;>
    simp only [re_mulVec_apply, im_mulVec_apply]
  · exact congrFun (D_shift hA81 _).1 a
  · exact congrFun (D_shift hA81 _).1 a
  · exact congrFun (D_shift hA81 _).2 a
  · exact congrFun (D_shift hA81 _).2 a

/-- Woodford (2003), p. 541 (tool): the complex responses respect the initial conditions. -/
theorem Dc_init (v : ιZ ⊕ ιz → ℂ) :
    (∀ j, ((DY hA81 0).map Complex.ofReal *ᵥ v) (Sum.inl (Sum.inl j)) = v (Sum.inl j)) ∧
      ∀ r, ((DΦ hA81 0).map Complex.ofReal *ᵥ v) (Sum.inr r) = v (Sum.inr r) := by
  refine ⟨fun j => Complex.ext ?_ ?_, fun r => Complex.ext ?_ ?_⟩ <;>
    simp only [re_mulVec_apply, im_mulVec_apply]
  · exact (D_init hA81 _).1 j
  · exact (D_init hA81 _).1 j
  · exact (D_init hA81 _).2 r
  · exact (D_init hA81 _).2 r

/-- Woodford (2003), (1.1) + (1.9): **an eigenvector `v` of `H` (eigenvalue `ν`) generates the
eigen-solution** `νᵗ(D_Y v, D_Φ v)` of the homogeneous system. -/
theorem eulerEq_of_eig {ν : ℂ} {v : ιZ ⊕ ιz → ℂ}
    (hv : (Hgen hA81).map Complex.ofReal *ᵥ v = ν • v) :
    EulerEq P ν ((DY hA81 0).map Complex.ofReal *ᵥ v) ((DΦ hA81 0).map Complex.ofReal *ᵥ v) := by
  have hY := (Dc_shift hA81 v).1
  have hF := (Dc_shift hA81 v).2
  rw [hv, mulVec_smul] at hY hF
  refine ⟨?_, ?_⟩
  · rw [← mulVec_smul (P.sys.Itil.map Complex.ofReal) ν, ← hY]
    funext a
    refine Complex.ext ?_ ?_ <;> simp only [re_mulVec_apply, im_mulVec_apply]
    · exact congrFun (D_struct hA81 _) a
    · exact congrFun (D_struct hA81 _) a
  · rw [← mulVec_smul (P.sys.Atilᵀ.map Complex.ofReal) ν, ← hF]
    funext a
    refine Complex.ext ?_ ?_
    · have := congrFun (D_foc hA81 fun j => (v j).re) a
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul, re_mulVec_apply, Complex.zero_re]
      linarith
    · have := congrFun (D_foc hA81 fun j => (v j).im) a
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        Complex.add_im, Complex.sub_im, Complex.im_ofReal_mul, im_mulVec_apply, Complex.zero_im]
      linarith

/-! ### From an eigen-solution to an eigenvector of `H` -/

/-- Woodford (2003), p. 539 (tool): the initial state `(Z_0, M_{−1})` of an eigen-solution
`(u, p)`. -/
def stateOf (u : (ιZ ⊕ ιz) ⊕ Unit → ℂ) (p : ιZ ⊕ ιz → ℂ) : ιZ ⊕ ιz → ℂ :=
  Sum.elim (fun j => u (Sum.inl (Sum.inl j))) (fun r => p (Sum.inr r))

/-- Woodford (2003), Assumption 8.1, p. 541: **a bounded eigen-solution is the plan from its
initial state** — for `|ν| ≤ 1` and `|w| ≤ 1` the real part of `w νᵗ(u, p)` is the response
`(D_Y(t), D_Φ(t))` to the real part of `w · stateOf u p` (it is a bounded solution of the
homogeneous system, so uniqueness applies). -/
theorem eig_sol {ν : ℂ} (hν : ‖ν‖ ≤ 1) {u : (ιZ ⊕ ιz) ⊕ Unit → ℂ} {p : ιZ ⊕ ιz → ℂ}
    (he : EulerEq P ν u p) (w : ℂ) (hw : ‖w‖ ≤ 1) (t : ℕ) :
    DY hA81 t *ᵥ (fun k => (w * stateOf u p k).re) = (fun a => (w * ν ^ t * u a).re) ∧
      DΦ hA81 t *ᵥ (fun k => (w * stateOf u p k).re) = fun a => (w * ν ^ t * p a).re := by
  set n : ιZ ⊕ ιz → ℝ := fun k => (w * stateOf u p k).re with hn
  set ys : ℕ → (ιZ ⊕ ιz) ⊕ Unit → ℝ := fun t a => (w * ν ^ t * u a).re with hys
  set φs : ℕ → ιZ ⊕ ιz → ℝ := fun t a => (w * ν ^ t * p a).re with hφs
  have c1 : ∀ t, P.sys.Itil.map Complex.ofReal *ᵥ ((w * ν ^ (t + 1)) • u) =
      P.sys.Atil.map Complex.ofReal *ᵥ ((w * ν ^ t) • u) := by
    intro t
    rw [mulVec_smul, mulVec_smul, ← he.1, smul_smul, pow_succ]
    congr 1
    ring
  have hU : ∀ t, P.sys.Itil *ᵥ ys (t + 1) = P.sys.Atil *ᵥ ys t := by
    intro t
    funext a
    have := congrArg (fun z => (z a).re) (c1 t)
    simp only [re_mulVec_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this
  have c2 : ∀ t, P.sys.Atilᵀ.map Complex.ofReal *ᵥ ((w * ν ^ (t + 1)) • p) +
      P.Tᵀ.map Complex.ofReal *ᵥ (P.W.map Complex.ofReal *ᵥ
        (P.T.map Complex.ofReal *ᵥ ((w * ν ^ t) • u))) -
      ((P.β⁻¹ : ℝ) : ℂ) • (P.sys.Itilᵀ.map Complex.ofReal *ᵥ ((w * ν ^ t) • p)) = 0 := by
    intro t
    funext a
    have e := congrFun he.2 a
    simp only [mulVec_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at e ⊢
    linear_combination (w * ν ^ t) * e
  have hF1 : ∀ t, P.sys.Atilᵀ *ᵥ φs (t + 1) + P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ ys t)) -
      P.β⁻¹ • (P.sys.Itilᵀ *ᵥ φs t) = 0 := by
    intro t
    funext a
    have := congrArg (fun z => (z a).re) (c2 t)
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.add_re,
      Complex.sub_re, Complex.re_ofReal_mul, re_mulVec_apply, Pi.zero_apply,
      Complex.zero_re] at this
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact this
  have hnorm : ∀ t (z : ℂ), |(w * ν ^ t * z).re| ≤ ‖z‖ := by
    intro t z
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_mul, norm_pow]
    have h1 : ‖ν‖ ^ t ≤ 1 := pow_le_one₀ (norm_nonneg _) hν
    have h2 : ‖w‖ * ‖ν‖ ^ t ≤ 1 :=
      (mul_le_mul hw h1 (pow_nonneg (norm_nonneg _) t) zero_le_one).trans_eq (one_mul 1)
    exact mul_le_of_le_one_left (norm_nonneg z) h2
  have hZadd : ∀ a b : (ιZ ⊕ ιz) ⊕ Unit → ℝ, Zpart (a + b) = Zpart a + Zpart b :=
    fun _ _ => rfl
  have hzadd : ∀ a b : (ιZ ⊕ ιz) ⊕ Unit → ℝ, zpart (a + b) = zpart a + zpart b :=
    fun _ _ => rfl
  have hiadd : ∀ a b : (ιZ ⊕ ιz) ⊕ Unit → ℝ, ipart (a + b) = ipart a + ipart b :=
    fun _ _ => rfl
  obtain ⟨⟨hst0, hZ00, ⟨M1, hM1⟩, -⟩, ⟨M2, hM2⟩, -, hM00, hfoc0⟩ :=
    sol_spec hA81 0 (bddSeq_zero (ι := ιz))
  have hsol : PFSol P n 0 (fun t _ => solY hA81 0 0 t + ys t)
      (fun t _ => solΦ hA81 0 0 t + φs t) := by
    refine ⟨⟨fun t _ ω => ⟨?_, ?_⟩, fun ω => ?_, ⟨M1 + ∑ a, ‖u a‖, fun t ω a => ?_⟩,
      fun _ _ => rfl⟩, ⟨M2 + ∑ a, ‖p a‖, fun t ω a => ?_⟩, fun _ _ => rfl, fun ω => ?_,
      fun t _ ω => ?_⟩
    · change Zpart (solY hA81 0 0 (t + 1) + ys (t + 1)) =
        P.sys.A11 *ᵥ Zpart (solY hA81 0 0 t + ys t) + P.sys.A12 *ᵥ zpart (solY hA81 0 0 t + ys t)
      have e1 : Zpart (solY hA81 0 0 (t + 1)) = P.sys.A11 *ᵥ Zpart (solY hA81 0 0 t) +
          P.sys.A12 *ᵥ zpart (solY hA81 0 0 t) := (hst0 t (Nat.zero_le t) ()).1
      have e2 : Zpart (ys (t + 1)) = P.sys.A11 *ᵥ Zpart (ys t) + P.sys.A12 *ᵥ zpart (ys t) := by
        funext j
        have := congrFun (hU t) (Sum.inl j)
        rw [LinearRESystem.Itil_mulVec, LinearRESystem.Atil_mulVec] at this
        simpa using this
      rw [hZadd, hZadd, hzadd, mulVec_add, mulVec_add, e1, e2]
      abel
    · change P.sys.Et *ᵥ zpart (solY hA81 0 0 (t + 1) + ys (t + 1)) =
        P.sys.A21 *ᵥ Zpart (solY hA81 0 0 t + ys t) + P.sys.A22 *ᵥ zpart (solY hA81 0 0 t + ys t) +
          ipart (solY hA81 0 0 t + ys t) • P.sys.B2 + 0
      have e1 : P.sys.Et *ᵥ zpart (solY hA81 0 0 (t + 1)) =
          P.sys.A21 *ᵥ Zpart (solY hA81 0 0 t) + P.sys.A22 *ᵥ zpart (solY hA81 0 0 t) +
            ipart (solY hA81 0 0 t) • P.sys.B2 + 0 := (hst0 t (Nat.zero_le t) ()).2
      have e2 : P.sys.Et *ᵥ zpart (ys (t + 1)) = P.sys.A21 *ᵥ Zpart (ys t) +
          P.sys.A22 *ᵥ zpart (ys t) + ipart (ys t) • P.sys.B2 := by
        funext r
        have := congrFun (hU t) (Sum.inr r)
        rw [LinearRESystem.Itil_mulVec, LinearRESystem.Atil_mulVec] at this
        simpa using this
      rw [hZadd, hzadd, hzadd, hiadd, mulVec_add, mulVec_add, mulVec_add, add_smul, e1, e2]
      abel
    · funext j
      have e := congrFun (hZ00 ()) j
      simp only [Zpart] at e ⊢
      simp only [Pi.add_apply, e, hys, hn, stateOf]
      simp
    · refine (abs_add_le _ _).trans (add_le_add (hM1 t () a) ?_)
      exact (hnorm t (u a)).trans (Finset.single_le_sum (f := fun a => ‖u a‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ a))
    · refine (abs_add_le _ _).trans (add_le_add (hM2 t () a) ?_)
      exact (hnorm t (p a)).trans (Finset.single_le_sum (f := fun a => ‖p a‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ a))
    · funext r
      have e := congrFun (hM00 ()) r
      simp only [Mpart] at e ⊢
      simp only [Pi.add_apply, e, hφs, hn, stateOf]
      simp
    · change P.sys.Atilᵀ *ᵥ (solΦ hA81 0 0 (t + 1) + φs (t + 1)) +
          P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ (solY hA81 0 0 t + ys t) - P.τstar)) -
          P.β⁻¹ • (P.sys.Itilᵀ *ᵥ (solΦ hA81 0 0 t + φs t)) = 0
      have e1 : P.sys.Atilᵀ *ᵥ solΦ hA81 0 0 (t + 1) +
          P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ solY hA81 0 0 t - P.τstar)) -
          P.β⁻¹ • (P.sys.Itilᵀ *ᵥ solΦ hA81 0 0 t) = 0 := hfoc0 t (Nat.zero_le t) ()
      have key : P.sys.Atilᵀ *ᵥ (solΦ hA81 0 0 (t + 1) + φs (t + 1)) +
          P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ (solY hA81 0 0 t + ys t) - P.τstar)) -
          P.β⁻¹ • (P.sys.Itilᵀ *ᵥ (solΦ hA81 0 0 t + φs t)) =
          (P.sys.Atilᵀ *ᵥ solΦ hA81 0 0 (t + 1) +
            P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ solY hA81 0 0 t - P.τstar)) -
            P.β⁻¹ • (P.sys.Itilᵀ *ᵥ solΦ hA81 0 0 t)) +
          (P.sys.Atilᵀ *ᵥ φs (t + 1) + P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ ys t)) -
            P.β⁻¹ • (P.sys.Itilᵀ *ᵥ φs t)) := by
        simp only [mulVec_add, mulVec_sub, smul_add]
        abel
      rw [key, e1, hF1 t, add_zero]
  have hu := sol_unique hA81 (bddSeq_zero (ι := ιz)) hsol t
  refine ⟨?_, ?_⟩
  · rw [(D_mulVec hA81 t n).1, ← hu.1, add_sub_cancel_left]
  · rw [(D_mulVec hA81 t n).2, ← hu.2, add_sub_cancel_left]

/-! ### The exact relation -/

/-- **Woodford (2003), p. 539 and (1.1) + (1.9): the spectrum of `H` is the set of roots of the
Euler pencil in the closed unit disc** — under the perfect-foresight Assumption 8.1, `ν` is an
eigenvalue of `H` iff `|ν| ≤ 1` and the homogeneous perfect-foresight system has a nonzero
solution `νᵗ(u, p)`. (These are not the roots of (1.15) selected by the split:
`nk_spec_not_selected`.) -/
theorem eig_Hgen_iff (ν : ℂ) :
    (Matrix.scalar (ιZ ⊕ ιz) ν - (Hgen hA81).map Complex.ofReal).det = 0 ↔
      ‖ν‖ ≤ 1 ∧ EulerRoot P ν := by
  have hsc : ∀ v : ιZ ⊕ ιz → ℂ, Matrix.scalar (ιZ ⊕ ιz) ν *ᵥ v = ν • v := fun v => by
    rw [Matrix.scalar_apply]
    funext i
    rw [mulVec_diagonal]
    simp
  constructor
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hHv : (Hgen hA81).map Complex.ofReal *ᵥ v = ν • v := by
      rw [sub_mulVec, hsc] at hv
      exact (sub_eq_zero.mp hv).symm
    refine ⟨eig_norm_le_one (powBdd_Hgen hA81) hHv hv0, _, _, ?_, eulerEq_of_eig hA81 hHv⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hu, hp⟩ := hcon
    apply hv0
    funext k
    rcases k with j | r
    · rw [← (Dc_init hA81 v).1 j, hu]
      rfl
    · rw [← (Dc_init hA81 v).2 r, hp]
  · rintro ⟨hν, u, p, hne, he⟩
    have hH : ∀ w : ℂ, ‖w‖ ≤ 1 → Hgen hA81 *ᵥ (fun k => (w * stateOf u p k).re) =
        fun k => (w * ν * stateOf u p k).re := by
      intro w hw
      rw [D_next, (eig_sol hA81 hν he w hw 1).1, (eig_sol hA81 hν he w hw 1).2]
      funext k
      rcases k with j | r <;> simp [stateOf]
    have hre := hH 1 (by simp)
    have him := hH (-Complex.I) (by simp)
    simp only [one_mul] at hre
    have hcI : ∀ z : ℂ, (-Complex.I * z).re = z.im := fun z => by simp
    have hcI' : ∀ z : ℂ, (-Complex.I * ν * z).re = (ν * z).im := fun z => by
      rw [mul_assoc, hcI]
    simp only [hcI, hcI'] at him
    have hHv : (Hgen hA81).map Complex.ofReal *ᵥ stateOf u p = ν • stateOf u p := by
      funext k
      refine Complex.ext ?_ ?_
      · rw [re_mulVec_apply, hre]
        simp
      · rw [im_mulVec_apply, him]
        simp
    have hn0 : stateOf u p = 0 → ∀ w : ℂ, (fun k => (w * stateOf u p k).re) = 0 :=
      fun h0 w => by
        funext k
        simp [h0]
    have hv0 : stateOf u p ≠ 0 := by
      intro h0
      have hu0 : u = 0 := by
        funext a
        have e1 := congrFun (eig_sol hA81 hν he 1 (by simp) 0).1 a
        have e2 := congrFun (eig_sol hA81 hν he (-Complex.I) (by simp) 0).1 a
        rw [hn0 h0 1, mulVec_zero] at e1
        rw [hn0 h0 (-Complex.I), mulVec_zero] at e2
        simp at e1 e2
        refine Complex.ext ?_ ?_ <;> simp only [Pi.zero_apply, Complex.zero_re, Complex.zero_im]
        · linarith
        · linarith
      have hp0 : p = 0 := by
        funext a
        have e1 := congrFun (eig_sol hA81 hν he 1 (by simp) 0).2 a
        have e2 := congrFun (eig_sol hA81 hν he (-Complex.I) (by simp) 0).2 a
        rw [hn0 h0 1, mulVec_zero] at e1
        rw [hn0 h0 (-Complex.I), mulVec_zero] at e2
        simp at e1 e2
        refine Complex.ext ?_ ?_ <;> simp only [Pi.zero_apply, Complex.zero_re, Complex.zero_im]
        · linarith
        · linarith
      rcases hne with h | h
      · exact h hu0
      · exact h hp0
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨stateOf u p, hv0, ?_⟩
    rw [sub_mulVec, hsc, hHv, sub_self]

/-- Woodford (2003), Assumption 8.1, p. 541, **the root condition on the pencil of (1.1) + (1.9)**:
under the perfect-foresight Assumption 8.1, `H` is geometrically stable iff the Euler pencil has
no root on the unit circle. -/
theorem powDecay_Hgen_iff_noEulerRoot :
    PencilSplit.PowDecay (Hgen hA81) ↔ ∀ ν : ℂ, ‖ν‖ = 1 → ¬ EulerRoot P ν := by
  constructor
  · intro hd ν hν hr
    exact OptimalRulesMeasureStability.noUnit_of_powDecay hd ν hν
      ((eig_Hgen_iff hA81 ν).mpr ⟨hν.le, hr⟩)
  · intro h
    exact powDecay_Hgen_of_noUnit hA81 fun ν hν hdet => h ν hν ((eig_Hgen_iff hA81 ν).mp hdet).2

include hA81 in
/-- Woodford (2003), **Assumption 8.1**, p. 541, **from the perfect-foresight Assumption 8.1 and
the root condition on the Euler pencil**: if (1.1) + (1.9) has no eigen-solution `νᵗ(u, p)` with
`|ν| = 1`, the measure Assumption 8.1 holds on every filtered probability space for every bounded
adapted disturbance. -/
theorem m_assumption81MB_of_noEulerRoot (h : ∀ ν : ℂ, ‖ν‖ = 1 → ¬ EulerRoot P ν) {Ω : Type*}
    [MeasurableSpace Ω] (S : ExpectationsMeasure.MeasExpectationSystem Ω) (t0 : ℕ) :
    OptimalRulesMeasure.MAssumption81MB S P t0 :=
  m_assumption81MB_of_powDecay hA81 S t0 ((powDecay_Hgen_iff_noEulerRoot hA81).mpr h)

/-! ### The book's models and the counterexample -/

/-- Woodford (2003), App. G.1 and p. 539, for the counterexample
`OptimalRulesMeasureCounterexample.eBP`: the Euler pencil has the root `1` (so the root condition
fails, and indeed the measure Assumption 8.1 fails on the fair-coin economy). -/
theorem eB_eulerRoot_one : EulerRoot OptimalRulesMeasureCounterexample.eBP 1 :=
  ((eig_Hgen_iff OptimalRulesMeasureCounterexample.eB_pf 1).mp
    OptimalRulesMeasureCounterexample.eB_eigenvalue_one).2

/-- Woodford (2003), §3.1: in the basic model the Euler pencil has no root on the unit circle
(every admissible calibration). -/
theorem nk_noEulerRoot (c : IRuleBasic.Calib) (hc : c.Adm) :
    ∀ ν : ℂ, ‖ν‖ = 1 → ¬ EulerRoot (GeneralLinks.nkProblem c hc) ν :=
  (powDecay_Hgen_iff_noEulerRoot _).mp (OptimalRulesMeasureStabilityModels.NK.nk_powDecay c hc)

/-- Woodford (2003), §3.2: in the inflation-inertia model the Euler pencil has no root on the
unit circle (every admissible calibration, `0 < γ ≤ 1`). -/
theorem in_noEulerRoot (c : IRuleBasic.Calib) (γ : ℝ) (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    ∀ ν : ℂ, ‖ν‖ = 1 → ¬ EulerRoot (GeneralLinksInertia.inProblem c γ hc hγ0.le) ν :=
  (powDecay_Hgen_iff_noEulerRoot _).mp
    (OptimalRulesMeasureStabilityModels.Inertia.in_powDecay c γ hc hγ0 hγ1)

/-- Woodford (2003), (1.15), p. 546, App. G.1 and §3.1: **the eigenvalues of `H` are not the roots
of (1.15) selected by the split** — in the basic model the split selects no root (`n_Z = 0`,
`OptimalRulesMeasureModelsProp82.NK.nkSplit`), but `H` (a `2 × 2` matrix) has an eigenvalue. -/
theorem nk_spec_not_selected (c : IRuleBasic.Calib) (hc : c.Adm) :
    (∃ ν : ℂ, (Matrix.scalar (Empty ⊕ Fin 2) ν -
      (Hgen (NKAssumption81.NK.nk_assumption81_perfectForesight c hc 0)).map
        Complex.ofReal).det = 0) ∧
    ∀ ν : ℂ, (Matrix.scalar Empty ν -
      (OptimalRulesMeasureModelsProp82.NK.nkSplit c hc).Ψ.map Complex.ofReal).det ≠ 0 := by
  refine ⟨?_, fun ν => ?_⟩
  · obtain ⟨z, hz⟩ := Complex.exists_root (f := ((Hgen
      (NKAssumption81.NK.nk_assumption81_perfectForesight c hc 0)).map Complex.ofReal).charpoly)
      (by rw [Matrix.charpoly_degree_eq_dim]; simp)
    exact ⟨z, by rw [← Matrix.eval_charpoly]; exact hz⟩
  · rw [Matrix.det_isEmpty]
    exact one_ne_zero

end Woodford.OptimalPolicyRules.OptimalRulesMeasureSpectrum
