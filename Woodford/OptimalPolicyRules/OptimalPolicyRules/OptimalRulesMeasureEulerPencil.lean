/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.OptimalRulesMeasureSpectrum

/-!
# The Euler pencil of (1.1) + (1.9): its polynomial and the symplectic pairing `ν ↔ 1/(βν)`

Woodford (2003), *Interest and Prices*, Chapter 8, (1.1) (p. 537) and the first-order
conditions (1.9) (p. 541), with the roots of App. G.1 (pp. 716–718).

Stack the plan and the multipliers, `x_t = (y_t, φ_t)`. Under perfect foresight with no
disturbance and `τ* = 0`, (1.1) + (1.9) read `F x_{t+1} = G x_t` with the square matrices
(rows: the FOC (1.9) for the columns of `y`, then the structural rows (1.1))
`F = [[0, Ã'], [Ĩ, 0]]` and `G = [[−T'WT, β⁻¹Ĩ'], [Ã, 0]]` (`Fm`, `Gm`); the **Euler pencil** is
`νF − G = [[T'WT, νÃ' − β⁻¹Ĩ'], [νĨ − Ã, 0]]` (`pencilC`, `pencilC_eq`) and its
characteristic polynomial `eulerPoly = det(νF − G)` has degree at most `2n + 1`
(`n = n_Z + n_z`). `ν` is a root (`det = 0`) iff the eigen-solution of
`OptimalRulesMeasureSpectrum.EulerRoot` exists (`eulerRoot_iff`).

## The symplectic pairing

* `pencilC_recip`: `det(μF − G) = (βν²)^{−n} det(νF − G)` for `μ = 1/(βν)`: the pencil at `μ` is
  a block rescaling of the **transpose** of the pencil at `ν` (this uses `W = W'`).
* `eulerRoot_pairMap_iff`: `ν ≠ 0` is a root iff `1/(βν)` is a root (no nondegeneracy needed).
* `eulerPoly_reflect`: the polynomial identity `X^{2n+1} E(1/X) ∘ (βX) = β^{n+1} X E(X)`;
  hence the coefficient symmetry `β^{i+1} e_{2n−i} = β^{n+1} e_i` (`eulerPoly_coeff_symm`), the
  top coefficient `e_{2n+1} = 0`, and — when `E ≢ 0` (a **regular** pencil, the nondegeneracy
  condition) — `deg E + mult₀ E = 2n` (`natDegree_add_rootMultiplicity_zero`): the zero root
  pairs with the roots "at infinity".
* `rootMultiplicity_pairMap`: for a regular pencil, **`ν ≠ 0` and `1/(βν)` have the same
  multiplicity**; `nzRoots_map_pairMap`: the multiset of nonzero roots is invariant under
  `ν ↦ 1/(βν)`.
* **The halves**: the fixed circle of the involution is `|ν| = β^{−1/2}`, and the nonzero
  roots with `|ν| < β^{−1/2}` (that is `β|ν|² < 1`) are exactly as many as those with
  `|ν| > β^{−1/2}`, counted with multiplicity (`card_lower_eq_upper`, and `card_lower_le_eq_upper`
  for the closed halves).
* `card_closedDisk_le`: since `β < 1`, a pair `(ν, 1/(βν))` has at most one member in the closed
  unit disc, so **at most `n` roots** (with multiplicity, including the zero root) lie in
  `|ν| ≤ 1`; and if exactly `n` do, every root outside the closed disc has `|ν| ≥ β⁻¹`
  (`ge_inv_beta_of_card`): a spectral gap `1 < |ν| < β⁻¹` free of roots.
-/

namespace Woodford.OptimalPolicyRules.OptimalRulesMeasureEulerPencil

open Matrix Polynomial GeneralSetup GeneralFOC GeneralFOC.LQ OptimalRulesMeasureSpectrum

variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-! ### The pencil -/

/-- Woodford (2003), (1.3) and (1.9), pp. 537–541: the loss matrix `Q = T'WT` (the Hessian of the
period loss) entering the first-order conditions. -/
def Qmat (P : LQProblem ιZ ιz ιτ) : Matrix ((ιZ ⊕ ιz) ⊕ Unit) ((ιZ ⊕ ιz) ⊕ Unit) ℝ :=
  P.Tᵀ * P.W * P.T

/-- Woodford (2003), (1.1) + (1.9): the lead matrix `F = [[0, Ã'], [Ĩ, 0]]` of the stacked
homogeneous system `F x_{t+1} = G x_t`, `x = (y, φ)` (rows: the FOC, then (1.1)). -/
def Fm (P : LQProblem ιZ ιz ιτ) :
    Matrix (((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz)) (((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz)) ℝ :=
  fromBlocks 0 P.sys.Atilᵀ P.sys.Itil 0

/-- Woodford (2003), (1.1) + (1.9): the current-date matrix `G = [[−T'WT, β⁻¹Ĩ'], [Ã, 0]]` of
the stacked homogeneous system `F x_{t+1} = G x_t`. -/
noncomputable def Gm (P : LQProblem ιZ ιz ιτ) :
    Matrix (((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz)) (((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz)) ℝ :=
  fromBlocks (-Qmat P) (P.β⁻¹ • P.sys.Itilᵀ) P.sys.Atil 0

/-- Woodford (2003), (1.1) + (1.9): the **Euler pencil** `νF − G` (over `ℂ`). -/
noncomputable def pencilC (P : LQProblem ιZ ιz ιτ) (ν : ℂ) :
    Matrix (((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz)) (((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz)) ℂ :=
  ν • (Fm P).map Complex.ofReal - (Gm P).map Complex.ofReal

/-- Woodford (2003), (1.1) + (1.9): the characteristic polynomial `det(νF − G)` of the Euler
pencil. -/
noncomputable def eulerPoly (P : LQProblem ιZ ιz ιτ) : ℂ[X] :=
  det ((X : ℂ[X]) • ((Fm P).map Complex.ofReal).map C + (-(Gm P).map Complex.ofReal).map C)

/-- Woodford (2003), (1.1) + (1.9): `eulerPoly` evaluated at `ν` is `det(νF − G)`. -/
theorem eulerPoly_eval (P : LQProblem ιZ ιz ιτ) (ν : ℂ) :
    (eulerPoly P).eval ν = (pencilC P ν).det := by
  rw [eulerPoly, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.neg_apply, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_C,
    smul_eq_mul, Polynomial.eval_mul, Polynomial.eval_X, pencilC, Matrix.sub_apply]
  ring

omit [Fintype ιZ] in
/-- Woodford (2003), (1.1) + (1.9): the block form
`νF − G = [[T'WT, νÃ' − β⁻¹Ĩ'], [νĨ − Ã, 0]]`. -/
theorem pencilC_eq (P : LQProblem ιZ ιz ιτ) (ν : ℂ) :
    pencilC P ν = fromBlocks ((Qmat P).map Complex.ofReal)
      (ν • P.sys.Atilᵀ.map Complex.ofReal - ((P.β⁻¹ : ℝ) : ℂ) • P.sys.Itilᵀ.map Complex.ofReal)
      (ν • P.sys.Itil.map Complex.ofReal - P.sys.Atil.map Complex.ofReal) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [pencilC, Fm, Gm]

/-- Woodford (2003), (1.1) + (1.9): the Euler pencil applied to `(u, p)`: the FOC rows
`νÃ'p + T'WTu − β⁻¹Ĩ'p` and the structural rows `νĨu − Ãu`. -/
theorem pencilC_mulVec (P : LQProblem ιZ ιz ιτ) (ν : ℂ) (u : (ιZ ⊕ ιz) ⊕ Unit → ℂ)
    (p : ιZ ⊕ ιz → ℂ) :
    pencilC P ν *ᵥ Sum.elim u p = Sum.elim
      (ν • (P.sys.Atilᵀ.map Complex.ofReal *ᵥ p) +
          P.Tᵀ.map Complex.ofReal *ᵥ (P.W.map Complex.ofReal *ᵥ (P.T.map Complex.ofReal *ᵥ u)) -
        ((P.β⁻¹ : ℝ) : ℂ) • (P.sys.Itilᵀ.map Complex.ofReal *ᵥ p))
      (ν • (P.sys.Itil.map Complex.ofReal *ᵥ u) - P.sys.Atil.map Complex.ofReal *ᵥ u) := by
  rw [pencilC_eq, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]
  have hQ : (Qmat P).map Complex.ofReal *ᵥ u =
      P.Tᵀ.map Complex.ofReal *ᵥ (P.W.map Complex.ofReal *ᵥ (P.T.map Complex.ofReal *ᵥ u)) := by
    rw [Qmat, PencilAssumptions.map_ofReal_mul, PencilAssumptions.map_ofReal_mul, mulVec_mulVec,
      mulVec_mulVec, Matrix.mul_assoc]
  rw [hQ, zero_mulVec, add_zero, sub_mulVec, sub_mulVec, smul_mulVec, smul_mulVec,
    smul_mulVec]
  congr 1
  abel

/-- Woodford (2003), (1.1) + (1.9), pp. 537–541: **`ν` is a root of the Euler pencil
(`OptimalRulesMeasureSpectrum.EulerRoot`) iff `det(νF − G) = 0`**. -/
theorem eulerRoot_iff (P : LQProblem ιZ ιz ιτ) (ν : ℂ) :
    EulerRoot P ν ↔ (pencilC P ν).det = 0 := by
  have key : ∀ u p, EulerEq P ν u p ↔ pencilC P ν *ᵥ Sum.elim u p = 0 := by
    intro u p
    rw [pencilC_mulVec, EulerEq]
    constructor
    · rintro ⟨h1, h2⟩
      funext a
      rcases a with a | a
      · simpa using congrFun h2 a
      · simpa [sub_eq_zero] using congrFun h1 a
    · intro h
      refine ⟨?_, ?_⟩
      · funext a
        have := congrFun h (Sum.inr a)
        simpa [sub_eq_zero] using this
      · funext a
        simpa using congrFun h (Sum.inl a)
  constructor
  · rintro ⟨u, p, hne, he⟩
    refine exists_mulVec_eq_zero_iff.mp ⟨Sum.elim u p, fun h0 => ?_, (key u p).mp he⟩
    rcases hne with h | h
    · exact h (funext fun a => by simpa using congrFun h0 (Sum.inl a))
    · exact h (funext fun a => by simpa using congrFun h0 (Sum.inr a))
  · intro h
    obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.mpr h
    have hv' : Sum.elim (fun a => v (Sum.inl a)) (fun r => v (Sum.inr r)) = v :=
      Sum.elim_comp_inl_inr v
    refine ⟨fun a => v (Sum.inl a), fun r => v (Sum.inr r), ?_, (key _ _).mpr (hv'.symm ▸ hv)⟩
    by_contra hcon
    push Not at hcon
    apply hv0
    rw [← hv', hcon.1, hcon.2]
    funext a
    rcases a with a | a <;> rfl

/-! ### The pairing `ν ↔ 1/(βν)` -/

/-- Woodford (2003), App. G.1, pp. 716–718: the involution `ν ↦ 1/(βν)` (`0 ↦ 0`) that pairs
the roots of the Euler pencil (and maps the roots `μ` of (1.15) to the eigenvalues `(βμ)⁻¹` of
`Λ`, `PencilAssumptions.nonzero_eig_eq`). -/
noncomputable def pairMap (β : ℝ) (ν : ℂ) : ℂ := ((β : ℂ) * ν)⁻¹

/-- Woodford (2003), App. G.1: `ν ↦ 1/(βν)` is an involution. -/
theorem pairMap_pairMap {β : ℝ} (hβ : β ≠ 0) (ν : ℂ) : pairMap β (pairMap β ν) = ν := by
  have hβc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ
  rw [pairMap, pairMap, mul_inv, inv_inv, ← mul_assoc, inv_mul_cancel₀ hβc, one_mul]

/-- Woodford (2003), App. G.1: `ν ↦ 1/(βν)` is injective. -/
theorem pairMap_injective {β : ℝ} (hβ : β ≠ 0) : Function.Injective (pairMap β) :=
  Function.LeftInverse.injective (pairMap_pairMap hβ)

/-- Woodford (2003), App. G.1: `1/(βν) ≠ 0` iff `ν ≠ 0`. -/
theorem pairMap_ne_zero {β : ℝ} (hβ : β ≠ 0) {ν : ℂ} : pairMap β ν ≠ 0 ↔ ν ≠ 0 := by
  have hβc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ
  simp [pairMap, hβc]

/-- Woodford (2003), App. G.1: `|1/(βν)| = 1/(β|ν|)` for `β > 0`. -/
theorem norm_pairMap {β : ℝ} (hβ : 0 < β) (ν : ℂ) : ‖pairMap β ν‖ = (β * ‖ν‖)⁻¹ := by
  rw [pairMap, norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ]

/-- Woodford (2003), (1.1) + (1.9) and App. G.1: **the pencil at `1/(βν)` is a block rescaling of
the transpose of the pencil at `ν`**, so `det(μF − G) = (βν²)^{−n} det(νF − G)` for
`μ = 1/(βν)`, `n = n_Z + n_z` (uses `W = W'`). -/
theorem pencilC_recip (P : LQProblem ιZ ιz ιτ) {ν : ℂ} (hν : ν ≠ 0) :
    (pencilC P (pairMap P.β ν)).det =
      (((P.β : ℂ) * ν ^ 2)⁻¹) ^ Fintype.card (ιZ ⊕ ιz) * (pencilC P ν).det := by
  have hβ : (P.β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr P.β_pos.ne'
  have hW : P.Wᵀ = P.W := by
    have h := P.W_posDef.1
    rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at h
  have hQ : ((Qmat P).map Complex.ofReal)ᵀ = (Qmat P).map Complex.ofReal := by
    rw [← transpose_map]
    congr 1
    simp [Qmat, transpose_mul, hW, Matrix.mul_assoc]
  set c1 : ℂ := -((P.β : ℂ) * ν)⁻¹ with hc1
  set c2 : ℂ := -ν⁻¹ with hc2
  have key : pencilC P (pairMap P.β ν) =
      fromBlocks 1 0 0 (c2 • (1 : Matrix (ιZ ⊕ ιz) (ιZ ⊕ ιz) ℂ)) * (pencilC P ν)ᵀ *
        fromBlocks 1 0 0 (c1 • (1 : Matrix (ιZ ⊕ ιz) (ιZ ⊕ ιz) ℂ)) := by
    rw [pencilC_eq, pencilC_eq, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero,
      zero_add, hQ, Matrix.mul_smul, Matrix.smul_mul, transpose_zero]
    rw [fromBlocks_inj]
    refine ⟨rfl, ?_, ?_, (smul_zero c1).symm⟩
    · ext a b
      simp only [Matrix.sub_apply, Matrix.smul_apply, transpose_apply, Matrix.map_apply,
        smul_eq_mul, pairMap, hc1, transpose_sub, transpose_smul]
      push_cast
      field_simp
      ring
    · ext a b
      simp only [Matrix.sub_apply, Matrix.smul_apply, transpose_apply, Matrix.map_apply,
        smul_eq_mul, pairMap, hc2, transpose_sub, transpose_smul]
      push_cast
      field_simp
      ring
  have hc : c2 * c1 = ((P.β : ℂ) * ν ^ 2)⁻¹ := by
    rw [hc1, hc2]
    field_simp
  rw [key, det_mul, det_mul, det_transpose, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁]
  simp only [det_one, det_smul, mul_one, one_mul]
  rw [← hc, mul_pow]
  ring

/-- Woodford (2003), App. G.1: **`ν ≠ 0` is a root of the Euler pencil iff `1/(βν)` is** (no
nondegeneracy needed). -/
theorem eulerRoot_pairMap_iff (P : LQProblem ιZ ιz ιτ) {ν : ℂ} (hν : ν ≠ 0) :
    EulerRoot P (pairMap P.β ν) ↔ EulerRoot P ν := by
  have hβ : (P.β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr P.β_pos.ne'
  rw [eulerRoot_iff, eulerRoot_iff, pencilC_recip P hν]
  have : (((P.β : ℂ) * ν ^ 2)⁻¹) ^ Fintype.card (ιZ ⊕ ιz) ≠ 0 :=
    pow_ne_zero _ (inv_ne_zero (mul_ne_zero hβ (pow_ne_zero 2 hν)))
  exact ⟨fun h => (mul_eq_zero.mp h).resolve_left this, fun h => by rw [h, mul_zero]⟩

/-! ### The polynomial: degree, reciprocity and coefficients -/

omit [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), (1.1) + (1.9) (tool): the stacked state `x = (y, φ)` has `2n + 1`
coordinates, `n = n_Z + n_z`. -/
theorem card_idx : Fintype.card (((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz)) =
    Fintype.card (ιZ ⊕ ιz) + 1 + Fintype.card (ιZ ⊕ ιz) := by
  simp only [Fintype.card_sum, Fintype.card_unit]

/-- Woodford (2003), (1.1) + (1.9): `deg det(νF − G) ≤ 2n + 1`. -/
theorem natDegree_eulerPoly_le (P : LQProblem ιZ ιz ιτ) :
    (eulerPoly P).natDegree ≤ Fintype.card (((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz)) :=
  natDegree_det_X_add_C_le _ _

/-- Woodford (2003), (1.1) + (1.9) and App. G.1: **the reciprocity identity**
`(X^{2n+1} E(1/X)) ∘ (βX) = β^{n+1} X E(X)`, i.e. `(βν)^{2n+1} E(1/(βν)) = β^{n+1} ν E(ν)`. -/
theorem eulerPoly_reflect (P : LQProblem ιZ ιz ιτ) :
    ((eulerPoly P).reflect (Fintype.card (((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz)))).comp
        (C (P.β : ℂ) * X) =
      C ((P.β : ℂ) ^ (Fintype.card (ιZ ⊕ ιz) + 1)) * X * eulerPoly P := by
  set N := Fintype.card (((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz)) with hN
  set n := Fintype.card (ιZ ⊕ ιz) with hn
  have hNn : N = n + 1 + n := card_idx
  have hβ : (P.β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr P.β_pos.ne'
  apply eq_of_infinite_eval_eq
  refine Set.Infinite.mono (fun ν (hν : ν ∈ ({0}ᶜ : Set ℂ)) => ?_)
    (Set.finite_singleton (0 : ℂ)).infinite_compl
  have hν0 : ν ≠ 0 := hν
  change eval ν _ = eval ν _
  rw [eval_comp, eval_mul, eval_C, eval_X, eval_mul, eval_mul, eval_C, eval_X]
  have hx : (P.β : ℂ) * ν ≠ 0 := mul_ne_zero hβ hν0
  let _ : Invertible (((P.β : ℂ) * ν)⁻¹) := invertibleOfNonzero (inv_ne_zero hx)
  have h := eval₂_reflect_mul_pow (RingHom.id ℂ) (((P.β : ℂ) * ν)⁻¹) N (eulerPoly P)
    (natDegree_eulerPoly_le P)
  rw [invOf_eq_inv, inv_inv, eval₂_id, eval₂_id, eulerPoly_eval] at h
  have h2 := pencilC_recip P hν0
  rw [pairMap] at h2
  rw [h2, ← eulerPoly_eval] at h
  have hpow : (((P.β : ℂ) * ν)⁻¹) ^ N * ((P.β : ℂ) * ν) ^ N = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hx, one_pow]
  calc eval ((P.β : ℂ) * ν) ((eulerPoly P).reflect N)
      = eval ((P.β : ℂ) * ν) ((eulerPoly P).reflect N) *
          ((((P.β : ℂ) * ν)⁻¹) ^ N * ((P.β : ℂ) * ν) ^ N) := by rw [hpow, mul_one]
    _ = ((P.β : ℂ) * ν) ^ N * (eval ((P.β : ℂ) * ν) ((eulerPoly P).reflect N) *
          (((P.β : ℂ) * ν)⁻¹) ^ N) := by ring
    _ = ((P.β : ℂ) * ν) ^ N * ((((P.β : ℂ) * ν ^ 2)⁻¹) ^ n * eval ν (eulerPoly P)) := by
          rw [h]
    _ = (P.β : ℂ) ^ (n + 1) * ν * eval ν (eulerPoly P) := by
          have e1 : (P.β : ℂ) * ν * ((P.β : ℂ) * ν ^ 2)⁻¹ = ν⁻¹ := by
            field_simp
          have key : ((P.β : ℂ) * ν) ^ (n + 1 + n) * (((P.β : ℂ) * ν ^ 2)⁻¹) ^ n =
              (P.β : ℂ) ^ (n + 1) * ν := by
            calc ((P.β : ℂ) * ν) ^ (n + 1 + n) * (((P.β : ℂ) * ν ^ 2)⁻¹) ^ n
                = ((P.β : ℂ) * ν) ^ (n + 1) *
                    ((P.β : ℂ) * ν * ((P.β : ℂ) * ν ^ 2)⁻¹) ^ n := by
                  rw [pow_add _ (n + 1) n, mul_pow ((P.β : ℂ) * ν)]
                  ring
              _ = (P.β : ℂ) ^ (n + 1) * ν * (ν ^ n * ν⁻¹ ^ n) := by
                  rw [e1, mul_pow, pow_succ ν]
                  ring
              _ = (P.β : ℂ) ^ (n + 1) * ν := by
                  rw [← mul_pow, mul_inv_cancel₀ hν0, one_pow, mul_one]
          rw [hNn]
          linear_combination eval ν (eulerPoly P) * key

/-- Woodford (2003), (1.1) + (1.9): the coefficient of `ν^{2n+1}` in `det(νF − G)` vanishes, so
`deg E ≤ 2n`. -/
theorem eulerPoly_coeff_top (P : LQProblem ιZ ιz ιτ) :
    (eulerPoly P).coeff (Fintype.card (ιZ ⊕ ιz) + 1 + Fintype.card (ιZ ⊕ ιz)) = 0 := by
  have h := congrArg (fun q => q.coeff 0) (eulerPoly_reflect P)
  rw [comp_C_mul_X_coeff, coeff_reflect, revAt_le (Nat.zero_le _), Nat.sub_zero, pow_zero,
    mul_one, mul_assoc, coeff_C_mul, coeff_X_mul_zero, mul_zero, card_idx] at h
  exact h

/-- Woodford (2003), (1.1) + (1.9) and App. G.1: **the coefficient symmetry**
`β^{i+1} e_{2n−i} = β^{n+1} e_i` of `E(ν) = ∑ e_i νⁱ`, for `i ≤ 2n`. -/
theorem eulerPoly_coeff_symm (P : LQProblem ιZ ιz ιτ) {i : ℕ}
    (hi : i ≤ Fintype.card (ιZ ⊕ ιz) + Fintype.card (ιZ ⊕ ιz)) :
    (P.β : ℂ) ^ (i + 1) *
        (eulerPoly P).coeff (Fintype.card (ιZ ⊕ ιz) + Fintype.card (ιZ ⊕ ιz) - i) =
      (P.β : ℂ) ^ (Fintype.card (ιZ ⊕ ιz) + 1) * (eulerPoly P).coeff i := by
  have h := congrArg (fun q => q.coeff (i + 1)) (eulerPoly_reflect P)
  have hle : i + 1 ≤ Fintype.card (((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz)) := by
    rw [card_idx]
    omega
  have hidx : Fintype.card (((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz)) - (i + 1) =
      Fintype.card (ιZ ⊕ ιz) + Fintype.card (ιZ ⊕ ιz) - i := by
    rw [card_idx]
    omega
  rw [comp_C_mul_X_coeff, coeff_reflect, revAt_le hle, hidx, mul_assoc, coeff_C_mul,
    coeff_X_mul] at h
  rw [← h, mul_comm]

/-- Woodford (2003), (1.1) + (1.9) and App. G.1: for a regular Euler pencil (`E ≢ 0`),
`deg E + mult₀ E = 2n` — the zero roots are paired with the roots "at infinity" (the
shortfall of the degree below `2n`). -/
theorem natDegree_add_rootMultiplicity_zero (P : LQProblem ιZ ιz ιτ) (hE : eulerPoly P ≠ 0) :
    (eulerPoly P).natDegree + (eulerPoly P).rootMultiplicity 0 =
      Fintype.card (ιZ ⊕ ιz) + Fintype.card (ιZ ⊕ ιz) := by
  rw [rootMultiplicity_eq_natTrailingDegree']
  set n := Fintype.card (ιZ ⊕ ιz) with hn
  have hβ : (P.β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr P.β_pos.ne'
  have hlead : (eulerPoly P).coeff (eulerPoly P).natDegree ≠ 0 := fun h =>
    hE (leadingCoeff_eq_zero.mp h)
  have htr : (eulerPoly P).coeff (eulerPoly P).natTrailingDegree ≠ 0 := fun h =>
    hE (trailingCoeff_eq_zero.mp h)
  have hd : (eulerPoly P).natDegree ≤ n + n := by
    have h1 := natDegree_eulerPoly_le P
    rw [card_idx] at h1
    by_contra h2
    have h3 : (eulerPoly P).natDegree = n + 1 + n := by omega
    have htop := eulerPoly_coeff_top P
    rw [← h3] at htop
    exact hlead htop
  have hle : (eulerPoly P).natTrailingDegree ≤ (eulerPoly P).natDegree :=
    natTrailingDegree_le_natDegree _
  have h1 : (eulerPoly P).natTrailingDegree ≤ n + n - (eulerPoly P).natDegree := by
    apply natTrailingDegree_le_of_ne_zero
    intro h0
    have := eulerPoly_coeff_symm P (i := n + n - (eulerPoly P).natDegree) (by omega)
    rw [show n + n - (n + n - (eulerPoly P).natDegree) = (eulerPoly P).natDegree by omega, h0,
      mul_zero] at this
    exact hlead ((mul_eq_zero.mp this).resolve_left (pow_ne_zero _ hβ))
  have h2 : n + n - (eulerPoly P).natTrailingDegree ≤ (eulerPoly P).natDegree := by
    apply le_natDegree_of_ne_zero
    intro h0
    have := eulerPoly_coeff_symm P (i := (eulerPoly P).natTrailingDegree) (by omega)
    rw [h0, mul_zero] at this
    exact htr ((mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero _ hβ))
  omega

/-! ### Multiplicities -/

/-- Woodford (2003), App. G.1 (tool): the multiplicity of a nonzero root `a` of `f` is at most
that of `a⁻¹` in the reflection `X^N f(1/X)` (`deg f ≤ N`). -/
theorem rootMultiplicity_le_reflect {f : ℂ[X]} (hf : f ≠ 0) {N : ℕ} (hN : f.natDegree ≤ N)
    {a : ℂ} (ha : a ≠ 0) : f.rootMultiplicity a ≤ (f.reflect N).rootMultiplicity a⁻¹ := by
  set m := f.rootMultiplicity a with hm
  set g := f /ₘ (X - C a) ^ m with hg
  have hfg : (X - C a) ^ m * g = f := pow_mul_divByMonic_rootMultiplicity_eq f a
  have hg0 : g ≠ 0 := by
    intro h
    rw [h, mul_zero] at hfg
    exact hf hfg.symm
  have hpd : ∀ k : ℕ, ((X - C a) ^ k).natDegree ≤ k := fun k => by
    rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  have hdeg : f.natDegree = m + g.natDegree := by
    rw [← hfg, natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero a)) hg0, natDegree_pow,
      natDegree_X_sub_C, mul_one]
  have hrefl1 : ∀ k : ℕ, ((X - C a) ^ k).reflect k = (C (-a) * (X - C a⁻¹)) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, reflect_mul _ _ (hpd k) (natDegree_X_sub_C a).le, ih, pow_succ]
      congr 1
      rw [reflect_sub, reflect_one_X, reflect_C, pow_one, mul_sub, C_neg, neg_mul, neg_mul,
        ← C_mul, mul_inv_cancel₀ ha, C_1]
      ring
  obtain ⟨k, rfl⟩ : ∃ k, N = m + k := ⟨N - m, by omega⟩
  have hrefl : f.reflect (m + k) = (C (-a) * (X - C a⁻¹)) ^ m * g.reflect k := by
    rw [← hfg, reflect_mul _ _ (hpd m) (by omega), hrefl1]
  have hdvd : (X - C a⁻¹) ^ m ∣ f.reflect (m + k) := by
    rw [hrefl, mul_pow]
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  exact (le_rootMultiplicity_iff (reflect_eq_zero_iff.not.mpr hf)).mpr hdvd

/-- Woodford (2003), App. G.1: **the symplectic pairing with multiplicities** — for a regular
Euler pencil (`E ≢ 0`), a nonzero `ν` and `1/(βν)` are roots of `det(νF − G)` of the same
multiplicity. -/
theorem rootMultiplicity_pairMap (P : LQProblem ιZ ιz ιτ) (hE : eulerPoly P ≠ 0) {a : ℂ}
    (ha : a ≠ 0) :
    (eulerPoly P).rootMultiplicity (pairMap P.β a) = (eulerPoly P).rootMultiplicity a := by
  have hβ0 : P.β ≠ 0 := P.β_pos.ne'
  have hβ : (P.β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ0
  have hle : ∀ b : ℂ, b ≠ 0 →
      (eulerPoly P).rootMultiplicity (pairMap P.β b) ≤ (eulerPoly P).rootMultiplicity b := by
    intro b hb
    have hc : C ((P.β : ℂ) ^ (Fintype.card (ιZ ⊕ ιz) + 1)) * X ≠ 0 :=
      mul_ne_zero (C_ne_zero.mpr (pow_ne_zero _ hβ)) X_ne_zero
    have e1 : (eulerPoly P).rootMultiplicity b =
        (C ((P.β : ℂ) ^ (Fintype.card (ιZ ⊕ ιz) + 1)) * X * eulerPoly P).rootMultiplicity b := by
      rw [rootMultiplicity_mul (mul_ne_zero hc hE), rootMultiplicity_mul hc, rootMultiplicity_C,
        rootMultiplicity_eq_zero (p := X) (by simp [hb]), zero_add, zero_add]
    have e2 : (C ((P.β : ℂ) ^ (Fintype.card (ιZ ⊕ ιz) + 1)) * X * eulerPoly P).rootMultiplicity b
        = ((eulerPoly P).reflect (Fintype.card (((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz)))).rootMultiplicity
          ((P.β : ℂ) * b) := by
      rw [← eulerPoly_reflect P, show C (P.β : ℂ) * X = C (P.β : ℂ) * X + C 0 by simp,
        rootMultiplicity_comp_C_mul_X_add_C _ _ _ _ (isUnit_iff_ne_zero.mpr hβ), add_zero]
    have e3 := rootMultiplicity_le_reflect hE (natDegree_eulerPoly_le P)
      ((pairMap_ne_zero hβ0).mpr hb)
    rw [pairMap, inv_inv] at e3
    rw [e1, e2]
    exact e3
  refine le_antisymm (hle a ha) ?_
  have := hle (pairMap P.β a) ((pairMap_ne_zero hβ0).mpr ha)
  rwa [pairMap_pairMap hβ0] at this

/-- Woodford (2003), App. G.1: the multiset of **nonzero** roots of the Euler pencil (with
multiplicity). -/
noncomputable def nzRoots (P : LQProblem ιZ ιz ιτ) : Multiset ℂ :=
  (eulerPoly P).roots.filter (fun r => r ≠ 0)

/-- Woodford (2003), App. G.1: the multiplicity of `1/(βx)` among the nonzero roots equals that
of `x`. -/
theorem count_nzRoots_pairMap (P : LQProblem ιZ ιz ιτ) (hE : eulerPoly P ≠ 0) (x : ℂ) :
    (nzRoots P).count (pairMap P.β x) = (nzRoots P).count x := by
  have hβ0 : P.β ≠ 0 := P.β_pos.ne'
  by_cases hx : x = 0
  · subst hx
    simp [pairMap]
  · rw [nzRoots, Multiset.count_filter_of_pos (p := fun r : ℂ => r ≠ 0)
      ((pairMap_ne_zero hβ0).mpr hx), Multiset.count_filter_of_pos (p := fun r : ℂ => r ≠ 0) hx,
      count_roots, count_roots, rootMultiplicity_pairMap P hE hx]

/-- Woodford (2003), App. G.1: **the nonzero roots are invariant under `ν ↦ 1/(βν)`** (as a
multiset, for a regular Euler pencil). -/
theorem nzRoots_map_pairMap (P : LQProblem ιZ ιz ιτ) (hE : eulerPoly P ≠ 0) :
    (nzRoots P).map (pairMap P.β) = nzRoots P := by
  have hβ0 : P.β ≠ 0 := P.β_pos.ne'
  ext x
  conv_lhs => rw [← pairMap_pairMap hβ0 x]
  rw [Multiset.count_map_eq_count' _ _ (pairMap_injective hβ0), count_nzRoots_pairMap P hE]

/-- Woodford (2003), App. G.1: for any property `q`, the nonzero roots with `q` are as many as
those whose partner `1/(βν)` has `q` (with multiplicity). -/
theorem card_filter_pairMap (P : LQProblem ιZ ιz ιτ) (hE : eulerPoly P ≠ 0) (q : ℂ → Prop)
    [DecidablePred q] :
    Multiset.card ((nzRoots P).filter q) =
      Multiset.card ((nzRoots P).filter fun r => q (pairMap P.β r)) := by
  conv_lhs => rw [← nzRoots_map_pairMap P hE]
  rw [Multiset.filter_map, Multiset.card_map]
  rfl

/-- Woodford (2003), App. G.1: `β|1/(βν)|² = (β|ν|²)⁻¹`. -/
theorem beta_norm_sq_pairMap {β : ℝ} (hβ : 0 < β) (ν : ℂ) :
    β * ‖pairMap β ν‖ ^ 2 = (β * ‖ν‖ ^ 2)⁻¹ := by
  rw [norm_pairMap hβ]
  by_cases hν : ‖ν‖ = 0
  · simp [hν]
  · field_simp

/-- Woodford (2003), App. G.1: **the two open halves** — the nonzero roots with
`|ν| < β^{−1/2}` (`β|ν|² < 1`) are exactly as many as those with `|ν| > β^{−1/2}`, counted with
multiplicity (regular Euler pencil). -/
theorem card_lower_eq_upper (P : LQProblem ιZ ιz ιτ) (hE : eulerPoly P ≠ 0) :
    Multiset.card ((nzRoots P).filter fun r => P.β * ‖r‖ ^ 2 < 1) =
      Multiset.card ((nzRoots P).filter fun r => 1 < P.β * ‖r‖ ^ 2) := by
  rw [card_filter_pairMap P hE (fun r => 1 < P.β * ‖r‖ ^ 2)]
  congr 1
  refine Multiset.filter_congr fun r hr => ?_
  have hr0 : r ≠ 0 := (Multiset.mem_filter.mp hr).2
  have hpos : 0 < P.β * ‖r‖ ^ 2 := mul_pos P.β_pos (pow_pos (norm_pos_iff.mpr hr0) 2)
  rw [beta_norm_sq_pairMap P.β_pos, one_lt_inv₀ hpos]

/-- Woodford (2003), App. G.1: **the two closed halves** — the nonzero roots with
`|ν| ≤ β^{−1/2}` are as many as those with `|ν| ≥ β^{−1/2}` (regular Euler pencil). -/
theorem card_lower_le_eq_upper (P : LQProblem ιZ ιz ιτ) (hE : eulerPoly P ≠ 0) :
    Multiset.card ((nzRoots P).filter fun r => P.β * ‖r‖ ^ 2 ≤ 1) =
      Multiset.card ((nzRoots P).filter fun r => 1 ≤ P.β * ‖r‖ ^ 2) := by
  rw [card_filter_pairMap P hE (fun r => 1 ≤ P.β * ‖r‖ ^ 2)]
  congr 1
  refine Multiset.filter_congr fun r hr => ?_
  have hr0 : r ≠ 0 := (Multiset.mem_filter.mp hr).2
  have hpos : 0 < P.β * ‖r‖ ^ 2 := mul_pos P.β_pos (pow_pos (norm_pos_iff.mpr hr0) 2)
  rw [beta_norm_sq_pairMap P.β_pos, one_le_inv₀ hpos]

/-! ### Roots in the closed unit disc -/

/-- Woodford (2003), App. G.1 (tool): the closed-disc roots split into the zero root and the
nonzero ones `A'`; the partners of `A'` are roots outside the closed disc (`β < 1`); and the
roots split into those in and outside the closed disc. -/
theorem disk_split (P : LQProblem ιZ ιz ιτ) (hE : eulerPoly P ≠ 0) :
    Multiset.card ((eulerPoly P).roots.filter fun r => ‖r‖ ≤ 1) =
        (eulerPoly P).rootMultiplicity 0 +
          Multiset.card ((eulerPoly P).roots.filter fun r => r ≠ 0 ∧ ‖r‖ ≤ 1) ∧
      ((eulerPoly P).roots.filter fun r => r ≠ 0 ∧ ‖r‖ ≤ 1).map (pairMap P.β) ≤
        (eulerPoly P).roots.filter (fun r => 1 < ‖r‖) ∧
      Multiset.card (eulerPoly P).roots =
        Multiset.card ((eulerPoly P).roots.filter fun r => ‖r‖ ≤ 1) +
          Multiset.card ((eulerPoly P).roots.filter fun r => 1 < ‖r‖) := by
  have hβ0 : P.β ≠ 0 := P.β_pos.ne'
  set s := (eulerPoly P).roots with hs
  refine ⟨?_, ?_, ?_⟩
  · have h := Multiset.filter_add_not (fun r : ℂ => r = 0) (s.filter fun r => ‖r‖ ≤ 1)
    rw [Multiset.filter_filter, Multiset.filter_filter] at h
    rw [← h, Multiset.card_add, ← count_roots, Multiset.count_eq_card_filter_eq]
    congr 2
    · refine Multiset.filter_congr fun r _ => ?_
      constructor
      · rintro ⟨h1, -⟩
        exact h1.symm
      · intro h1
        subst h1
        simp
  · refine Multiset.le_iff_count.mpr fun x => ?_
    conv_lhs => rw [← pairMap_pairMap hβ0 x]
    rw [Multiset.count_map_eq_count' _ _ (pairMap_injective hβ0)]
    by_cases hc : pairMap P.β x ≠ 0 ∧ ‖pairMap P.β x‖ ≤ 1
    · rw [Multiset.count_filter_of_pos (p := fun r : ℂ => r ≠ 0 ∧ ‖r‖ ≤ 1) hc]
      have hx0 : x ≠ 0 := (pairMap_ne_zero hβ0).mp hc.1
      have hgt : 1 < ‖x‖ := by
        have e : ‖x‖ = (P.β * ‖pairMap P.β x‖)⁻¹ := by
          rw [← norm_pairMap P.β_pos, pairMap_pairMap hβ0]
        have hpos : 0 < P.β * ‖pairMap P.β x‖ :=
          mul_pos P.β_pos (norm_pos_iff.mpr hc.1)
        have hlt : P.β * ‖pairMap P.β x‖ < 1 :=
          lt_of_le_of_lt (mul_le_of_le_one_right P.β_pos.le hc.2) P.β_lt_one
        rw [e]
        exact one_lt_inv₀ hpos |>.mpr hlt
      rw [Multiset.count_filter_of_pos (p := fun r : ℂ => 1 < ‖r‖) hgt, count_roots, count_roots,
        rootMultiplicity_pairMap P hE hx0]
    · rw [Multiset.count_filter_of_neg (p := fun r : ℂ => r ≠ 0 ∧ ‖r‖ ≤ 1) hc]
      exact Nat.zero_le _
  · have h := Multiset.filter_add_not (fun r : ℂ => ‖r‖ ≤ 1) s
    have h' : s.filter (fun a => ¬ ‖a‖ ≤ 1) = s.filter (fun r => 1 < ‖r‖) :=
      Multiset.filter_congr fun r _ => not_le
    rw [h'] at h
    conv_lhs => rw [← h]
    rw [Multiset.card_add]

/-- Woodford (2003), App. G.1 and Assumption 8.1 (root count): **at most `n = n_Z + n_z` roots of
the Euler pencil lie in the closed unit disc** (with multiplicity, the zero root included), for a
regular pencil — a pair `(ν, 1/(βν))` has at most one member there since `β < 1`. -/
theorem card_closedDisk_le (P : LQProblem ιZ ιz ιτ) (hE : eulerPoly P ≠ 0) :
    Multiset.card ((eulerPoly P).roots.filter fun r => ‖r‖ ≤ 1) ≤ Fintype.card (ιZ ⊕ ιz) := by
  obtain ⟨ha, hb, hc⟩ := disk_split P hE
  have h1 := Multiset.card_le_card hb
  rw [Multiset.card_map] at h1
  have h2 : Multiset.card (eulerPoly P).roots = (eulerPoly P).natDegree :=
    IsAlgClosed.card_roots_eq_natDegree
  have h3 := natDegree_add_rootMultiplicity_zero P hE
  omega

/-- Woodford (2003), App. G.1: **the spectral gap** — if exactly `n` roots of a regular Euler
pencil lie in the closed unit disc, then every root outside it has `|ν| ≥ β⁻¹` (no root in the
annulus `1 < |ν| < β⁻¹`): the roots outside are exactly the partners `1/(βν)` of the nonzero
roots inside. -/
theorem ge_inv_beta_of_card (P : LQProblem ιZ ιz ιτ) (hE : eulerPoly P ≠ 0)
    (hcard : Multiset.card ((eulerPoly P).roots.filter fun r => ‖r‖ ≤ 1) =
      Fintype.card (ιZ ⊕ ιz)) {r : ℂ} (hr : r ∈ (eulerPoly P).roots) (h1 : 1 < ‖r‖) :
    P.β⁻¹ ≤ ‖r‖ := by
  obtain ⟨ha, hb, hc⟩ := disk_split P hE
  have h2 : Multiset.card (eulerPoly P).roots = (eulerPoly P).natDegree :=
    IsAlgClosed.card_roots_eq_natDegree
  have h3 := natDegree_add_rootMultiplicity_zero P hE
  have heq := Multiset.eq_of_le_of_card_le hb (by rw [Multiset.card_map]; omega)
  have hmem : r ∈ (eulerPoly P).roots.filter (fun r => 1 < ‖r‖) := Multiset.mem_filter.mpr ⟨hr, h1⟩
  rw [← heq] at hmem
  obtain ⟨a, ha', rfl⟩ := Multiset.mem_map.mp hmem
  obtain ⟨-, ha0, ha1⟩ := Multiset.mem_filter.mp ha'
  rw [norm_pairMap P.β_pos]
  exact inv_anti₀ (mul_pos P.β_pos (norm_pos_iff.mpr ha0)) (mul_le_of_le_one_right P.β_pos.le ha1)

end Woodford.OptimalPolicyRules.OptimalRulesMeasureEulerPencil
