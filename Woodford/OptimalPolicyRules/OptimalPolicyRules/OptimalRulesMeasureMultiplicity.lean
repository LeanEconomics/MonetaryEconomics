/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.OptimalRulesMeasureEulerPencil
import OptimalPolicyRules.Prop81Unique

/-!
# The spectrum of `H` with multiplicities

Woodford (2003), *Interest and Prices*, Chapter 8: the state transition
`(Z_{t+1}, M_t) = h + H (Z_t, M_{t−1})` of the optimal plan (p. 539,
`OptimalRulesMeasureGeneral.Hgen`) under the perfect-foresight Assumption 8.1 (p. 541), and the
Euler pencil `det(νF − G)` of (1.1) + (1.9) (`OptimalRulesMeasureEulerPencil.eulerPoly`).

`OptimalRulesMeasureSpectrum.eig_Hgen_iff` identified the eigenvalues of `H` as a **set**: the
roots of the Euler pencil in the closed unit disc. Here the relation is made exact **with
multiplicities**.

## The factorisation

Let `V = [D_Y(0); D_Φ(0)]` (the responses of `(y_0, φ_0)` to the initial state) and `S` the
selection of the state coordinates `(Z_0, M_{−1})` from `x = (y, φ)`. Then `F V H = G V`
(`Fm_Vmat_Hgen`, time invariance), `S V = I` (initial conditions) and `S S' = I`. With the
unimodular `U = I + (V − S')S` (`det U = 1`, Weinstein–Aronszajn) one gets
`(νF − G) U = N(ν) [S'(νI − H)S + I − S'S]`, whence (`eulerPoly_factor`)

  `det(νF − G) = det(νI − H) · R(ν)`,  `R(ν) = det(F V S + (νF − G)(I − S'S))`.

## The exact relation

* `eulerPoly_ne_zero`: the perfect-foresight Assumption 8.1 forces the Euler pencil to be
  **regular** (`E ≢ 0`); otherwise every `ν` in the closed disc would be an eigenvalue of `H`.
* `roots_charpoly_eq`: **the roots of `det(νI − H)`, with multiplicity, are exactly the roots of
  the Euler pencil in the closed unit disc, with their multiplicities**; equivalently
  (`charpoly_eq_prod`) `det(νI − H) = ∏_{|ν_i| ≤ 1} (ν − ν_i)` over the roots of `E` counted with
  multiplicity, and (`rootMultiplicity_charpoly`) the algebraic multiplicity of `ν` in `H` is
  that in `E` when `|ν| ≤ 1` and `0` otherwise. In particular the multiplicities agree **also
  on the unit circle** (no counterexample exists). Proof: `E = χ_H R`, `χ_H` has `n` roots, all
  in the closed disc (`H` is power-bounded), while `E` has at most `n` roots there
  (`OptimalRulesMeasureEulerPencil.card_closedDisk_le`, from the pairing `ν ↔ 1/(βν)` and
  `β < 1`); so `R` has none there.
* `card_closedDisk_eq`: exactly `n = n_Z + n_z` roots in the closed disc — the number of
  predetermined variables `(Z_t, M_{t−1})` of the stacked system, Blanchard–Kahn's count
  (cf. `GeneralBKCopy.determinate_of`, whose hypothesis is a stable subspace of dimension equal to
  the number of predetermined variables).
* `eulerRoot_gap`, `Rpoly_root_ge`: every root of `E` is in `|ν| ≤ 1` or in `|ν| ≥ β⁻¹`; the
  cofactor `R` carries exactly the roots outside, and `deg E = 2n − mult₀ E`.
* `roots_charpoly_eq_lower_half`: the eigenvalues of `H` are exactly the **lower half**
  `|ν| < β^{−1/2}` of the symplectic pairing.

## Links

* `prop81_eig_pairMap`, `powDecay_Λ_iff_outside`: in Proposition 8.1 the multiplier transition `Λ`
  has the eigenvalues `pairMap β μ = 1/(βμ)` for the unselected roots `μ` of (1.15) — the same
  involution — and `Λ` is stable **iff** every unselected root has `|μ| > β⁻¹` (the core
  `Prop81Unique.powDecay_Λ_of_outside` gave `⇐`).
* `eig_Hgen_iff'`: `OptimalRulesMeasureSpectrum.eig_Hgen_iff` recovered from the multiplicity
  statement.
-/

namespace Woodford.OptimalPolicyRules.OptimalRulesMeasureMultiplicity

open Matrix Polynomial GeneralSetup GeneralFOC GeneralFOC.LQ OptimalRulesMeasureKernel
  OptimalRulesMeasureGeneral OptimalRulesMeasureSpectrum OptimalRulesMeasureEulerPencil

variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-- Woodford (2003), (1.1) + (1.9): **the Euler pencil is singular (`E ≡ 0`) iff every `ν` is a
root**; the nondegeneracy (regularity) condition is `E ≢ 0`. -/
theorem eulerPoly_eq_zero_iff (P : LQProblem ιZ ιz ιτ) :
    eulerPoly P = 0 ↔ ∀ ν, EulerRoot P ν := by
  constructor
  · intro h ν
    rw [eulerRoot_iff, ← eulerPoly_eval, h, eval_zero]
  · intro h
    refine eq_zero_of_infinite_isRoot _ (Set.infinite_univ.mono fun ν _ => ?_)
    change eval ν (eulerPoly P) = 0
    rw [eulerPoly_eval]
    exact (eulerRoot_iff P ν).mp (h ν)

/-! ### The state coordinates and the responses -/

/-- Woodford (2003), p. 539: the position of the state `(Z_0, M_{−1})` inside `x = (y, φ)`:
`Z` is the `Z`-block of `y`, `M_{−1}` the `z`-block of `φ`. -/
def sel : ιZ ⊕ ιz → ((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz) :=
  Sum.elim (fun j => Sum.inl (Sum.inl (Sum.inl j))) (fun r => Sum.inr (Sum.inr r))

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 539 (tool): the state coordinates are distinct. -/
theorem sel_injective : Function.Injective (sel (ιZ := ιZ) (ιz := ιz)) := by
  rintro (a | a) (b | b) h <;> simp_all [sel]

/-- Woodford (2003), p. 539 (tool): the selection matrix `S` of the state coordinates. -/
def Smat : Matrix (ιZ ⊕ ιz) (((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz)) ℝ :=
  Matrix.of fun i k => if k = sel i then 1 else 0

/-- Woodford (2003), p. 539 (tool): `S S' = I`. -/
theorem Smat_mul_transpose :
    Smat (ιZ := ιZ) (ιz := ιz) * (Smat (ιZ := ιZ) (ιz := ιz))ᵀ = 1 := by
  ext i j
  simp only [Smat, mul_apply, transpose_apply, of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, one_apply, sel_injective.eq_iff]

variable {P : LQProblem ιZ ιz ιτ} (hA81 : Assumption81 P perfectForesight 0)

/-- Woodford (2003), p. 539: `V = [D_Y(0); D_Φ(0)]`, the response of `x_0 = (y_0, φ_0)` to the
initial state (zero forcing). -/
noncomputable def Vmat : Matrix (((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz)) (ιZ ⊕ ιz) ℝ :=
  Matrix.fromRows (DY hA81 0) (DΦ hA81 0)

/-- Woodford (2003), p. 541: `S V = I` — the responses start from the given state. -/
theorem Smat_mul_Vmat : Smat (ιZ := ιZ) (ιz := ιz) * Vmat hA81 = 1 := by
  ext i j
  have hcol : ∀ a, (Vmat hA81 *ᵥ Pi.single j 1) a = Vmat hA81 a j := fun a => by
    rw [mulVec_single_one]
    rfl
  have hS : (Smat (ιZ := ιZ) (ιz := ιz) * Vmat hA81) i j = Vmat hA81 (sel i) j := by
    simp [Smat, mul_apply]
  rw [hS, ← hcol]
  rcases i with i | i
  · have := (D_init hA81 (Pi.single j 1)).1 i
    simp only [Vmat, fromRows_mulVec, sel, Sum.elim_inl] at this ⊢
    rw [this, Pi.single_apply, one_apply]
  · have := (D_init hA81 (Pi.single j 1)).2 i
    simp only [Vmat, fromRows_mulVec, sel, Sum.elim_inr] at this ⊢
    rw [this, Pi.single_apply, one_apply]

/-- Woodford (2003), p. 539 and (1.1) + (1.9): **`F V H = G V`** — the responses from the
state `H n` are those from `n` one period later, and they solve the homogeneous system. -/
theorem Fm_Vmat_Hgen : Fm P * Vmat hA81 * Hgen hA81 = Gm P * Vmat hA81 := by
  refine ext_iff_mulVec.mpr fun v => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, Vmat, fromRows_mulVec, fromRows_mulVec,
    ← (D_shift hA81 v).1, ← (D_shift hA81 v).2, Fm, Gm, fromBlocks_mulVec, fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, zero_add, add_zero]
  congr 1
  · have h := D_foc hA81 v
    have hQ : Qmat P *ᵥ (DY hA81 0 *ᵥ v) = P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ (DY hA81 0 *ᵥ v))) := by
      rw [Qmat, ← mulVec_mulVec, ← mulVec_mulVec]
    rw [neg_mulVec, hQ, smul_mulVec]
    rw [← sub_eq_zero, ← h]
    abel
  · exact D_struct hA81 v

/-! ### The factorisation `det(νF − G) = det(νI − H) R(ν)` -/

/-- Woodford (2003), p. 539 (tool): the projector `I − S'S` onto the coordinates of `x` other
than the state (over `ℂ`). -/
noncomputable def Dc : Matrix (((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz)) (((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz)) ℂ :=
  1 - ((Smat (ιZ := ιZ) (ιz := ιz)).map Complex.ofReal)ᵀ * (Smat (ιZ := ιZ) (ιz := ιz)).map
    Complex.ofReal

/-- Woodford (2003), p. 539 (tool): the cofactor matrix `N(ν) = F V S + (νF − G)(I − S'S)`. -/
noncomputable def Nmat (ν : ℂ) :
    Matrix (((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz)) (((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz)) ℂ :=
  (Fm P).map Complex.ofReal * (Vmat hA81).map Complex.ofReal *
      (Smat (ιZ := ιZ) (ιz := ιz)).map Complex.ofReal + pencilC P ν * Dc

/-- Woodford (2003), p. 539: the cofactor polynomial `R(ν) = det N(ν)`. -/
noncomputable def Rpoly : ℂ[X] :=
  det ((X : ℂ[X]) • ((Fm P).map Complex.ofReal * Dc).map C +
    ((Fm P).map Complex.ofReal * (Vmat hA81).map Complex.ofReal *
      (Smat (ιZ := ιZ) (ιz := ιz)).map Complex.ofReal - (Gm P).map Complex.ofReal * Dc).map C)

/-- Woodford (2003), p. 539: `R(ν) = det N(ν)`. -/
theorem Rpoly_eval (ν : ℂ) : (Rpoly hA81).eval ν = (Nmat hA81 ν).det := by
  rw [Rpoly, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  have hN : Nmat hA81 ν = ν • ((Fm P).map Complex.ofReal * Dc) +
      ((Fm P).map Complex.ofReal * (Vmat hA81).map Complex.ofReal *
        (Smat (ιZ := ιZ) (ιz := ιz)).map Complex.ofReal - (Gm P).map Complex.ofReal * Dc) := by
    rw [Nmat, pencilC, Matrix.sub_mul, Matrix.smul_mul]
    abel
  rw [hN]
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_C, smul_eq_mul,
    Polynomial.eval_mul, Polynomial.eval_X]

/-- Woodford (2003), p. 539 and (1.1) + (1.9): **`det(νF − G) = R(ν) det(νI − H)`** — via
`(νF − G)(I + (V − S')S) = N(ν)(S'(νI − H)S + I − S'S)`, both outer factors having determinant
`1` and `det(νI − H)` (Weinstein–Aronszajn). -/
theorem pencil_factor (ν : ℂ) :
    (pencilC P ν).det =
      (Nmat hA81 ν).det * (Matrix.scalar (ιZ ⊕ ιz) ν - (Hgen hA81).map Complex.ofReal).det := by
  set Sc := (Smat (ιZ := ιZ) (ιz := ιz)).map Complex.ofReal with hSc
  set Vc := (Vmat hA81).map Complex.ofReal with hVc
  set Fc := (Fm P).map Complex.ofReal with hFc
  set Gc := (Gm P).map Complex.ofReal with hGc
  set Hc := (Hgen hA81).map Complex.ofReal with hHc
  set M := Matrix.scalar (ιZ ⊕ ιz) ν - Hc with hM
  have hSJ : Sc * Scᵀ = 1 := by
    rw [hSc, ← transpose_map, ← PencilAssumptions.map_ofReal_mul, Smat_mul_transpose,
      Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one]
  have hSV : Sc * Vc = 1 := by
    rw [hSc, hVc, ← PencilAssumptions.map_ofReal_mul, Smat_mul_Vmat,
      Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one]
  have hFVH : Fc * Vc * Hc = Gc * Vc := by
    rw [hFc, hVc, hHc, hGc, ← PencilAssumptions.map_ofReal_mul,
      ← PencilAssumptions.map_ofReal_mul, ← PencilAssumptions.map_ofReal_mul, Fm_Vmat_Hgen]
  set D := Dc (ιZ := ιZ) (ιz := ιz) with hD0
  have hD : D = 1 - Scᵀ * Sc := rfl
  have hN : Nmat hA81 ν = Fc * Vc * Sc + pencilC P ν * D := rfl
  clear_value D
  have hSD : Sc * D = 0 := by
    rw [hD, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hSJ, Matrix.one_mul, sub_self]
  have hDJ : D * Scᵀ = 0 := by
    rw [hD, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hSJ, Matrix.mul_one, sub_self]
  have hDD : D * D = D := by
    calc D * D = D * (1 - Scᵀ * Sc) := by rw [← hD]
      _ = D - D * Scᵀ * Sc := by rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
      _ = D := by rw [hDJ, Matrix.zero_mul, sub_zero]
  have hscal : Matrix.scalar (ιZ ⊕ ιz) ν = ν • (1 : Matrix (ιZ ⊕ ιz) (ιZ ⊕ ιz) ℂ) := by
    rw [scalar_apply, smul_one_eq_diagonal]
  have hpV : pencilC P ν * Vc = Fc * Vc * M := by
    rw [pencilC, ← hFc, ← hGc, hM, hscal, Matrix.sub_mul, Matrix.mul_sub, hFVH, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_one]
  clear_value M
  have hU : (1 + (Vc - Scᵀ) * Sc).det = 1 := by
    rw [det_one_add_mul_comm, Matrix.mul_sub, hSV, hSJ, sub_self, add_zero, det_one]
  have hB : (Scᵀ * M * Sc + D).det = M.det := by
    have e : Scᵀ * M * Sc + D = 1 + Scᵀ * ((M - 1) * Sc) := by
      rw [hD, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, ← Matrix.mul_assoc]
      abel
    rw [e, det_one_add_mul_comm, Matrix.mul_assoc, hSJ, Matrix.mul_one, add_sub_cancel]
  have hprod : pencilC P ν * (1 + (Vc - Scᵀ) * Sc) = Nmat hA81 ν * (Scᵀ * M * Sc + D) := by
    have e1 : Fc * Vc * Sc * (Scᵀ * M * Sc) = Fc * Vc * M * Sc := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Sc Scᵀ, hSJ, Matrix.one_mul]
    have e2 : Fc * Vc * Sc * D = 0 := by
      rw [Matrix.mul_assoc, hSD, Matrix.mul_zero]
    have e3 : pencilC P ν * D * (Scᵀ * M * Sc) = 0 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc D Scᵀ, hDJ, Matrix.zero_mul, Matrix.mul_zero]
    have e4 : pencilC P ν * D * D = pencilC P ν * D := by
      rw [Matrix.mul_assoc, hDD]
    have L : pencilC P ν * (1 + (Vc - Scᵀ) * Sc) =
        pencilC P ν + Fc * Vc * M * Sc - pencilC P ν * Scᵀ * Sc := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.sub_mul, Matrix.mul_sub, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, hpV]
      abel
    have R : (Fc * Vc * Sc + pencilC P ν * D) * (Scᵀ * M * Sc + D) =
        Fc * Vc * M * Sc + pencilC P ν * D := by
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e1, e2, e3, e4, add_zero, zero_add]
    rw [hN, L, R, hD, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc]
    abel
  calc (pencilC P ν).det = (pencilC P ν).det * (1 + (Vc - Scᵀ) * Sc).det := by
        rw [hU, mul_one]
    _ = (Nmat hA81 ν).det * M.det := by rw [← det_mul, hprod, det_mul, hB]

/-- Woodford (2003), p. 539 and (1.1) + (1.9): **the polynomial factorisation**
`det(νF − G) = det(νI − H) · R(ν)`. -/
theorem eulerPoly_factor :
    eulerPoly P = ((Hgen hA81).map Complex.ofReal).charpoly * Rpoly hA81 := by
  refine Polynomial.funext fun ν => ?_
  rw [eval_mul, eulerPoly_eval, eval_charpoly, Rpoly_eval, pencil_factor, mul_comm]

/-! ### The exact relation with multiplicities -/

include hA81 in
/-- Woodford (2003), Assumption 8.1 (p. 541) and (1.1) + (1.9): **the perfect-foresight
Assumption 8.1 makes the Euler pencil regular**, `det(νF − G) ≢ 0` (otherwise every `ν` with
`|ν| ≤ 1` would be an eigenvalue of `H`, `OptimalRulesMeasureSpectrum.eig_Hgen_iff`). -/
theorem eulerPoly_ne_zero : eulerPoly P ≠ 0 := by
  intro hE
  have hroot : ∀ ν : ℂ, ‖ν‖ ≤ 1 → ((Hgen hA81).map Complex.ofReal).charpoly.IsRoot ν := by
    intro ν hν
    rw [IsRoot.def, eval_charpoly]
    exact (eig_Hgen_iff hA81 ν).mpr ⟨hν, (eulerPoly_eq_zero_iff P).mp hE ν⟩
  have hinf : Set.Infinite {x : ℂ | ((Hgen hA81).map Complex.ofReal).charpoly.IsRoot x} := by
    refine Set.Infinite.mono ?_
      (Set.Infinite.image Complex.ofReal_injective.injOn (Set.Icc_infinite (zero_lt_one' ℝ)))
    rintro _ ⟨a, ⟨ha0, ha1⟩, rfl⟩
    refine hroot _ ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
    exact ha1
  exact (charpoly_monic _).ne_zero (eq_zero_of_infinite_isRoot _ hinf)

/-- Woodford (2003), p. 539 (tool): the eigenvalues of `H` (roots of `det(νI − H)`) lie in the
closed unit disc, and `det(νI − H)` has `n` roots. -/
theorem charpoly_roots_disk :
    (∀ r ∈ ((Hgen hA81).map Complex.ofReal).charpoly.roots, ‖r‖ ≤ 1) ∧
      Multiset.card ((Hgen hA81).map Complex.ofReal).charpoly.roots = Fintype.card (ιZ ⊕ ιz) := by
  refine ⟨fun r hr => ?_, ?_⟩
  · have h : ((Hgen hA81).map Complex.ofReal).charpoly.IsRoot r :=
      (mem_roots (charpoly_monic _).ne_zero).mp hr
    rw [IsRoot.def, eval_charpoly] at h
    exact ((eig_Hgen_iff hA81 r).mp h).1
  · rw [IsAlgClosed.card_roots_eq_natDegree, charpoly_natDegree_eq_dim]

/-- Woodford (2003), p. 539 (tool): `R` has no root in the closed unit disc, and
`roots E = roots det(νI − H) + roots R`. -/
theorem roots_split :
    (eulerPoly P).roots = ((Hgen hA81).map Complex.ofReal).charpoly.roots + (Rpoly hA81).roots ∧
      (Rpoly hA81).roots.filter (fun r => ‖r‖ ≤ 1) = 0 := by
  have hE := eulerPoly_ne_zero hA81
  have hfac := eulerPoly_factor hA81
  have hprod : ((Hgen hA81).map Complex.ofReal).charpoly * Rpoly hA81 ≠ 0 := hfac ▸ hE
  have hroots : (eulerPoly P).roots =
      ((Hgen hA81).map Complex.ofReal).charpoly.roots + (Rpoly hA81).roots := by
    rw [hfac, roots_mul hprod]
  obtain ⟨hdisk, hcard⟩ := charpoly_roots_disk hA81
  have hfilt : (eulerPoly P).roots.filter (fun r => ‖r‖ ≤ 1) =
      ((Hgen hA81).map Complex.ofReal).charpoly.roots +
        (Rpoly hA81).roots.filter (fun r => ‖r‖ ≤ 1) := by
    rw [hroots, Multiset.filter_add, Multiset.filter_eq_self.mpr hdisk]
  have hle := card_closedDisk_le P hE
  rw [hfilt, Multiset.card_add, hcard] at hle
  exact ⟨hroots, Multiset.card_eq_zero.mp (by omega)⟩

/-- **Woodford (2003), p. 539 and (1.1) + (1.9): the eigenvalues of `H`, with algebraic
multiplicity, are exactly the roots of the Euler pencil in the closed unit disc, with their
multiplicities** (perfect-foresight Assumption 8.1). -/
theorem roots_charpoly_eq :
    ((Hgen hA81).map Complex.ofReal).charpoly.roots =
      (eulerPoly P).roots.filter (fun r => ‖r‖ ≤ 1) := by
  obtain ⟨hroots, h0⟩ := roots_split hA81
  rw [hroots, Multiset.filter_add, Multiset.filter_eq_self.mpr (charpoly_roots_disk hA81).1, h0,
    add_zero]

/-- Woodford (2003), p. 539: **`det(νI − H) = ∏ (ν − ν_i)` over the roots `ν_i` of the Euler
pencil with `|ν_i| ≤ 1`, counted with multiplicity**. -/
theorem charpoly_eq_prod :
    ((Hgen hA81).map Complex.ofReal).charpoly =
      (((eulerPoly P).roots.filter (fun r => ‖r‖ ≤ 1)).map fun r => X - C r).prod := by
  rw [← roots_charpoly_eq hA81]
  exact (prod_multiset_X_sub_C_of_monic_of_roots_card_eq (charpoly_monic _)
    IsAlgClosed.card_roots_eq_natDegree).symm

/-- Woodford (2003), p. 539: **the algebraic multiplicity of `ν` as an eigenvalue of `H` is its
multiplicity as a root of the Euler pencil when `|ν| ≤ 1`** (including `|ν| = 1`), and `0`
otherwise. -/
theorem rootMultiplicity_charpoly (ν : ℂ) :
    ((Hgen hA81).map Complex.ofReal).charpoly.rootMultiplicity ν =
      if ‖ν‖ ≤ 1 then (eulerPoly P).rootMultiplicity ν else 0 := by
  rw [← count_roots, roots_charpoly_eq hA81, Multiset.count_filter, count_roots]

include hA81 in
/-- Woodford (2003), Assumption 8.1 and App. C.1 (**the Blanchard–Kahn count** for the stacked
system (1.1) + (1.9)): exactly `n = n_Z + n_z` roots of the Euler pencil (with multiplicity) lie
in the closed unit disc — the number of predetermined variables `(Z_t, M_{t−1})`. -/
theorem card_closedDisk_eq :
    Multiset.card ((eulerPoly P).roots.filter fun r => ‖r‖ ≤ 1) = Fintype.card (ιZ ⊕ ιz) := by
  rw [← roots_charpoly_eq hA81]
  exact (charpoly_roots_disk hA81).2

include hA81 in
/-- Woodford (2003), App. G.1: **the spectral gap** under the perfect-foresight Assumption 8.1 —
every root of the Euler pencil has `|ν| ≤ 1` or `|ν| ≥ β⁻¹`. -/
theorem eulerRoot_gap {ν : ℂ} (h : EulerRoot P ν) : ‖ν‖ ≤ 1 ∨ P.β⁻¹ ≤ ‖ν‖ := by
  by_cases h1 : ‖ν‖ ≤ 1
  · exact Or.inl h1
  · refine Or.inr (ge_inv_beta_of_card P (eulerPoly_ne_zero hA81) (card_closedDisk_eq hA81) ?_
      (lt_of_not_ge h1))
    rw [mem_roots (eulerPoly_ne_zero hA81), IsRoot.def, eulerPoly_eval]
    exact (eulerRoot_iff P ν).mp h

/-- Woodford (2003), p. 539: **the cofactor `R(ν) = det(νF − G)/det(νI − H)` carries exactly the
roots outside the closed disc**: every root of `R` has `|ν| ≥ β⁻¹`. -/
theorem Rpoly_root_ge {ν : ℂ} (h : (Rpoly hA81).eval ν = 0) : P.β⁻¹ ≤ ‖ν‖ := by
  obtain ⟨hroots, h0⟩ := roots_split hA81
  have hE := eulerPoly_ne_zero hA81
  have hR : Rpoly hA81 ≠ 0 := fun h' => by
    rw [eulerPoly_factor hA81, h', mul_zero] at hE
    exact hE rfl
  have hmem : ν ∈ (Rpoly hA81).roots := (mem_roots hR).mpr h
  have hout : ¬ ‖ν‖ ≤ 1 := fun h1 => by
    have : ν ∈ (Rpoly hA81).roots.filter (fun r => ‖r‖ ≤ 1) := Multiset.mem_filter.mpr ⟨hmem, h1⟩
    rw [h0] at this
    exact Multiset.notMem_zero _ this
  refine ge_inv_beta_of_card P hE (card_closedDisk_eq hA81) ?_ (lt_of_not_ge hout)
  rw [hroots]
  exact Multiset.mem_add.mpr (Or.inr hmem)

/-- Woodford (2003), App. G.1: **the eigenvalues of `H` are the lower half of the symplectic
pairing** — the roots of the Euler pencil with `|ν| < β^{−1/2}` (`β|ν|² < 1`), with
multiplicity. -/
theorem roots_charpoly_eq_lower_half :
    ((Hgen hA81).map Complex.ofReal).charpoly.roots =
      (eulerPoly P).roots.filter (fun r => P.β * ‖r‖ ^ 2 < 1) := by
  rw [roots_charpoly_eq hA81]
  refine Multiset.filter_congr fun r hr => ?_
  have hβ := P.β_pos
  have hβ1 := P.β_lt_one
  constructor
  · intro h1
    have : ‖r‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg r) h1
    nlinarith
  · intro h1
    by_contra h2
    have hroot : EulerRoot P r := by
      rw [eulerRoot_iff, ← eulerPoly_eval]
      exact (mem_roots (eulerPoly_ne_zero hA81)).mp hr
    rcases eulerRoot_gap hA81 hroot with h3 | h3
    · exact h2 h3
    · have h4 : 1 ≤ P.β * ‖r‖ := by
        have := mul_le_mul_of_nonneg_left h3 hβ.le
        rwa [mul_inv_cancel₀ hβ.ne'] at this
      have h5 : 1 < ‖r‖ := lt_of_not_ge h2
      nlinarith

/-- Woodford (2003), Assumption 8.1 and App. C.1, **under the root condition** (no root on the
unit circle, `OptimalRulesMeasureSpectrum.powDecay_Hgen_iff_noEulerRoot`): exactly `n` roots lie
in the open unit disc, all of them eigenvalues of `H`, and the remaining roots have
`|ν| ≥ β⁻¹`. -/
theorem card_openDisk_eq_of_noEulerRoot (h : ∀ ν : ℂ, ‖ν‖ = 1 → ¬ EulerRoot P ν) :
    Multiset.card ((eulerPoly P).roots.filter fun r => ‖r‖ < 1) = Fintype.card (ιZ ⊕ ιz) ∧
      ((Hgen hA81).map Complex.ofReal).charpoly.roots =
        (eulerPoly P).roots.filter (fun r => ‖r‖ < 1) := by
  have hc : (eulerPoly P).roots.filter (fun r => ‖r‖ ≤ 1) =
      (eulerPoly P).roots.filter (fun r => ‖r‖ < 1) := by
    refine Multiset.filter_congr fun r hr => ⟨fun h1 => lt_of_le_of_ne h1 fun h2 => h r h2 ?_,
      le_of_lt⟩
    rw [eulerRoot_iff, ← eulerPoly_eval]
    exact (mem_roots (eulerPoly_ne_zero hA81)).mp hr
  rw [← hc, ← roots_charpoly_eq hA81]
  exact ⟨(charpoly_roots_disk hA81).2, rfl⟩

/-- Woodford (2003), p. 539: `OptimalRulesMeasureSpectrum.eig_Hgen_iff` recovered from the
multiplicity statement: `ν` is an eigenvalue of `H` iff `|ν| ≤ 1` and `det(νF − G) = 0`. -/
theorem eig_Hgen_iff' (ν : ℂ) :
    ((Hgen hA81).map Complex.ofReal).charpoly.eval ν = 0 ↔
      ‖ν‖ ≤ 1 ∧ (eulerPoly P).eval ν = 0 := by
  rw [← IsRoot.def, ← mem_roots (charpoly_monic _).ne_zero, roots_charpoly_eq hA81,
    Multiset.mem_filter, mem_roots (eulerPoly_ne_zero hA81), IsRoot.def, and_comm]

/-! ### Links to Proposition 8.1 -/

/-- Woodford (2003), p. 553 and App. G.1, **link to the root selection of Proposition 8.1**: under
Assumptions 8.2 (i)–8.4 the nonzero eigenvalues of the multiplier transition `Λ` of (1.20) are
`pairMap β μ = 1/(βμ)` for the unselected roots `μ` of (1.15) — the same involution that pairs
the roots of the Euler pencil (`OptimalRulesMeasureEulerPencil.rootMultiplicity_pairMap`). -/
theorem prop81_eig_pairMap {S : LinearRESystem ιZ ιz} {β : ℝ} (hβ : 0 < β)
    (h82 : PencilEigen.Assumption82 S β) (R : PencilEigen.RealSelection S h82.sel)
    (h83 : PencilEigen.Assumption83 S) (h84 : PencilAssumptions.Assumption84 S h82.sel) :
    (PencilAssumptions.unselected S h82.sel).map (pairMap β) =
      ((PencilSplit.Λmat S β (PencilAssumptions.splitOfSel hβ h82 R h83 h84).J).map
        Complex.ofReal).charpoly.roots.filter (fun x => x ≠ 0) :=
  PencilAssumptions.nonzero_eig_eq hβ h82 R h83 h84

/-- Woodford (2003), p. 553, **the remark after Proposition 8.1 as an equivalence**: under
Assumptions 8.2 (i)–8.4, `Λ` is (geometrically) stable **iff** every unselected nonzero root of
(1.15) has `|μ| > β⁻¹`, i.e. iff its partner `1/(βμ)` lies in the open unit disc. (The core
`Prop81Unique.powDecay_Λ_of_outside` is the direction `⇐`.) -/
theorem powDecay_Λ_iff_outside {S : LinearRESystem ιZ ιz} {β : ℝ} (hβ : 0 < β)
    (h82 : PencilEigen.Assumption82 S β) (R : PencilEigen.RealSelection S h82.sel)
    (h83 : PencilEigen.Assumption83 S) (h84 : PencilAssumptions.Assumption84 S h82.sel) :
    PencilSplit.PowDecay (PencilSplit.Λmat S β (PencilAssumptions.splitOfSel hβ h82 R h83 h84).J)
      ↔ ∀ μ ∈ PencilAssumptions.unselected S h82.sel, β⁻¹ < ‖μ‖ := by
  constructor
  · intro hd μ hμ
    have hμ0 : μ ≠ 0 := ((PencilAssumptions.unselected_spec h82 h83).2.2 μ hμ).2.1
    have hmem := Multiset.mem_map_of_mem (pairMap β) hμ
    rw [prop81_eig_pairMap hβ h82 R h83 h84] at hmem
    obtain ⟨hr, -⟩ := Multiset.mem_filter.mp hmem
    have hdet := (mem_roots (charpoly_monic _).ne_zero).mp hr
    rw [IsRoot.def, eval_charpoly] at hdet
    obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.mpr hdet
    have hsc : ∀ w : ιz → ℂ, Matrix.scalar ιz (pairMap β μ) *ᵥ w = pairMap β μ • w := fun w => by
      rw [Matrix.scalar_apply]
      funext i
      rw [mulVec_diagonal]
      simp
    have hHv : (PencilSplit.Λmat S β (PencilAssumptions.splitOfSel hβ h82 R h83 h84).J).map
        Complex.ofReal *ᵥ v = pairMap β μ • v := by
      rw [sub_mulVec, hsc] at hv
      exact (sub_eq_zero.mp hv).symm
    have hle := eig_norm_le_one (OptimalRulesMeasureIID.powBdd_of_powDecay hd) hHv hv0
    have hne : ‖pairMap β μ‖ ≠ 1 := fun h1 =>
      OptimalRulesMeasureStability.noUnit_of_powDecay hd _ h1 hdet
    have hlt : ‖pairMap β μ‖ < 1 := lt_of_le_of_ne hle hne
    rw [norm_pairMap hβ] at hlt
    have hpos : 0 < β * ‖μ‖ := mul_pos hβ (norm_pos_iff.mpr hμ0)
    have h1 : 1 < β * ‖μ‖ := (inv_lt_one₀ hpos).mp hlt
    calc β⁻¹ = β⁻¹ * 1 := (mul_one _).symm
      _ < β⁻¹ * (β * ‖μ‖) := mul_lt_mul_of_pos_left h1 (inv_pos.mpr hβ)
      _ = ‖μ‖ := by rw [← mul_assoc, inv_mul_cancel₀ hβ.ne', one_mul]
  · exact Prop81Unique.powDecay_Λ_of_outside hβ h82 R h83 h84

end Woodford.OptimalPolicyRules.OptimalRulesMeasureMultiplicity
