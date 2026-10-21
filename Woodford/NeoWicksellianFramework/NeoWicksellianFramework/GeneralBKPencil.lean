/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.GeneralBK

/-!
# The Blanchard–Kahn theorem for systems in pencil form

Woodford (2003), *Interest and Prices*, Appendix C.1, p. 670 (the models of Chapter 4 are first
written as `A₀ E_t y_{t+1} = A₁ y_t + w_t` and then solved for `E_t y_{t+1}`); Blanchard and Kahn
(1980).

* `equilPencil_iff`, `determinatePencil_iff`: when `A₀` is invertible, the system
  `A₀ E_t y_{t+1} = A₁ y_t + w_t` has the same equilibria as `E_t y_{t+1} = A₀⁻¹A₁ y_t + A₀⁻¹w_t`,
  and (since `w ↦ A₀⁻¹ w` is a bijection of bounded adapted forcings) it is determinate iff
  `A₀⁻¹A₁` is.
* `pencilPoly A₀ A₁ = det(λA₀ − A₁)`, `pencilPoly_eq`: it equals `det A₀ · charpoly(A₀⁻¹A₁)`, so
  the generalised eigenvalues of the pencil, the roots of `det(λA₀ − A₁)` with multiplicity, are
  the eigenvalues of `A₀⁻¹A₁` (`eigs_pencil`, `mem_eigs_pencil_iff`).
* `determinatePencil_iff_count` (**Blanchard–Kahn for pencils**): determinate iff no generalised
  eigenvalue on the unit circle, exactly `|X|` of them in the open disc, and genericity.

Singular `A₀` (the King–Watson (1998) / Klein (2000) case, with infinite generalised
eigenvalues counted as unstable) is treated in `GeneralBKSingular`.
-/

namespace Woodford.NeoWicksellianFramework.GeneralBKPencil

open Polynomial InvariantSplit GeneralBKForward GeneralBK
open scoped Matrix

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)
variable {Z X : Type*} [Fintype Z] [Fintype X] [DecidableEq Z] [DecidableEq X]

/-- Woodford (2003), App. C.1, p. 670: `y` solves `A₀ E_t y_{t+1} = A₁ y_t + w_t`. -/
def SolvesPencil {ι : Type*} [Fintype ι] (A0 A1 : Matrix ι ι ℝ) (w y : ℕ → ι → Ω → ℝ) : Prop :=
  ∀ t, mv A0 (fun i => 𝔼.E t (y (t + 1) i)) = mv A1 (y t) + w t

/-- Woodford (2003), App. C.1, p. 670: a bounded equilibrium of the pencil system with
predetermined block `x` (known one period ahead, `x_0` given). -/
def EquilPencil (A0 A1 : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (w : ℕ → Z ⊕ X → Ω → ℝ) (x0 : X → ℝ)
    (y : ℕ → Z ⊕ X → Ω → ℝ) : Prop :=
  SolvesPencil 𝔼 A0 A1 w y ∧ AdaptedV 𝔼 y ∧
    (∀ t j, 𝔼.E t (y (t + 1) (Sum.inr j)) = y (t + 1) (Sum.inr j)) ∧
    (∀ j, y 0 (Sum.inr j) = fun _ => x0 j) ∧ BoundedV y

/-- Woodford (2003), App. C.1, p. 670: determinacy of the pencil system. -/
def DeterminatePencil (A0 A1 : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) : Prop :=
  ∀ w : ℕ → Z ⊕ X → Ω → ℝ, BoundedV w → AdaptedV 𝔼 w →
    ∀ x0 : X → ℝ, ∃! y, EquilPencil 𝔼 A0 A1 w x0 y

/-- Woodford (2003), App. C.1, p. 670: with `A₀` invertible, `A₀ E_t y_{t+1} = A₁ y_t + w_t` iff
`E_t y_{t+1} = A₀⁻¹A₁ y_t + A₀⁻¹ w_t`. -/
theorem solvesPencil_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {A0 A1 : Matrix ι ι ℝ}
    (h : IsUnit A0.det) (w y : ℕ → ι → Ω → ℝ) :
    SolvesPencil 𝔼 A0 A1 w y ↔ Solves 𝔼 (A0⁻¹ * A1) (fun t => mv A0⁻¹ (w t)) y := by
  constructor
  · intro hs t i
    have e := congrArg (mv A0⁻¹) (hs t)
    rw [mv_mv, Matrix.nonsing_inv_mul _ h, mv_one, mv_add, mv_mv] at e
    exact congrFun e i
  · intro hs t
    have e : (fun i => 𝔼.E t (y (t + 1) i)) = mv (A0⁻¹ * A1) (y t) + mv A0⁻¹ (w t) := by
      funext i
      exact hs t i
    rw [e, mv_add, mv_mv, mv_mv, Matrix.mul_nonsing_inv_cancel_left _ _ h,
      Matrix.mul_nonsing_inv _ h, mv_one]

/-- Woodford (2003), App. C.1, p. 670: with `A₀` invertible the pencil system and the reduced
system `E_t y_{t+1} = A₀⁻¹A₁ y_t + A₀⁻¹ w_t` have the same equilibria. -/
theorem equilPencil_iff {A0 A1 : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} (h : IsUnit A0.det)
    (w : ℕ → Z ⊕ X → Ω → ℝ) (x0 : X → ℝ) (y : ℕ → Z ⊕ X → Ω → ℝ) :
    EquilPencil 𝔼 A0 A1 w x0 y ↔ Equil 𝔼 (A0⁻¹ * A1) (fun t => mv A0⁻¹ (w t)) x0 y := by
  unfold EquilPencil Equil
  rw [solvesPencil_iff 𝔼 h]

/-- **Pencil reduction** (Woodford (2003), App. C.1, p. 670): with `A₀` invertible,
`A₀ E_t y_{t+1} = A₁ y_t + w_t` is determinate iff `E_t y_{t+1} = A₀⁻¹A₁ y_t + w_t` is. -/
theorem determinatePencil_iff {A0 A1 : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} (h : IsUnit A0.det) :
    DeterminatePencil 𝔼 A0 A1 ↔ Determinate 𝔼 (A0⁻¹ * A1) := by
  constructor
  · intro hd w hwb hwa x0
    have hfb : BoundedV (fun t => mv A0 (w t)) := boundedV_mv A0 hwb
    have hfa : AdaptedV 𝔼 (fun t => mv A0 (w t)) := adaptedV_mv 𝔼 A0 hwa
    have hback : (fun t => mv A0⁻¹ (mv A0 (w t))) = w := by
      funext t
      rw [mv_mv, Matrix.nonsing_inv_mul _ h, mv_one]
    obtain ⟨y, hy, hu⟩ := hd _ hfb hfa x0
    refine ⟨y, ?_, fun y' hy' => hu y' ?_⟩
    · have := (equilPencil_iff 𝔼 h _ x0 y).mp hy
      rwa [hback] at this
    · refine (equilPencil_iff 𝔼 h _ x0 y').mpr ?_
      rw [hback]
      exact hy'
  · intro hd w hwb hwa x0
    obtain ⟨y, hy, hu⟩ := hd _ (boundedV_mv _ hwb) (adaptedV_mv 𝔼 _ hwa) x0
    exact ⟨y, (equilPencil_iff 𝔼 h w x0 y).mpr hy,
      fun y' hy' => hu y' ((equilPencil_iff 𝔼 h w x0 y').mp hy')⟩

/-- Woodford (2003), App. C.1, p. 670: the pencil polynomial `det(λA₀ − A₁)`. -/
noncomputable def pencilPoly {ι : Type*} [Fintype ι] [DecidableEq ι] (A0 A1 : Matrix ι ι ℝ) :
    ℝ[X] :=
  (Matrix.scalar ι (Polynomial.X : ℝ[X]) * (C : ℝ →+* ℝ[X]).mapMatrix A0 -
    (C : ℝ →+* ℝ[X]).mapMatrix A1).det

/-- Woodford (2003), App. C.1, p. 670: `det(λA₀ − A₁) = det A₀ · det(λ − A₀⁻¹A₁)`. -/
theorem pencilPoly_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {A0 A1 : Matrix ι ι ℝ}
    (h : IsUnit A0.det) : pencilPoly A0 A1 = C A0.det * (A0⁻¹ * A1).charpoly := by
  set CA0 := (C : ℝ →+* ℝ[X]).mapMatrix A0 with hCA0
  have hcomm : Matrix.scalar ι (Polynomial.X : ℝ[X]) * CA0 =
      CA0 * Matrix.scalar ι (Polynomial.X : ℝ[X]) :=
    (Matrix.scalar_commute _ (fun r => Commute.all _ r) CA0)
  have hA1 : (C : ℝ →+* ℝ[X]).mapMatrix A1 = CA0 * (C : ℝ →+* ℝ[X]).mapMatrix (A0⁻¹ * A1) := by
    rw [hCA0, ← map_mul, Matrix.mul_nonsing_inv_cancel_left _ _ h]
  have e : Matrix.scalar ι (Polynomial.X : ℝ[X]) * CA0 - (C : ℝ →+* ℝ[X]).mapMatrix A1 =
      CA0 * (A0⁻¹ * A1).charmatrix := by
    rw [hcomm, hA1, ← Matrix.mul_sub]
    rfl
  rw [pencilPoly, e, Matrix.det_mul, hCA0, ← RingHom.map_det, Matrix.charpoly]

/-- Woodford (2003), App. C.1, p. 670: the generalised eigenvalues of the pencil, the roots of
`det(λA₀ − A₁)` counted with multiplicity, are the eigenvalues of `A₀⁻¹A₁`. -/
theorem eigs_pencil {ι : Type*} [Fintype ι] [DecidableEq ι] {A0 A1 : Matrix ι ι ℝ}
    (h : IsUnit A0.det) :
    eigs (A0⁻¹ * A1) = ((pencilPoly A0 A1).map Complex.ofRealHom).roots := by
  have hd : (Complex.ofRealHom A0.det) ≠ 0 := by
    simpa using h.ne_zero
  rw [pencilPoly_eq h, Polynomial.map_mul, Polynomial.map_C, roots_C_mul _ hd, eigs,
    charpoly_map_ofReal]

/-- Woodford (2003), App. C.1, p. 670: `μ` is a generalised eigenvalue iff `det(μA₀ − A₁) = 0`. -/
theorem mem_eigs_pencil_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {A0 A1 : Matrix ι ι ℝ}
    (h : IsUnit A0.det) (μ : ℂ) :
    μ ∈ eigs (A0⁻¹ * A1) ↔ ((pencilPoly A0 A1).map Complex.ofRealHom).IsRoot μ := by
  rw [eigs_pencil h, mem_roots]
  rw [pencilPoly_eq h, Polynomial.map_mul, Polynomial.map_C]
  refine mul_ne_zero (by simpa using h.ne_zero) ((Matrix.charpoly_monic _).map _).ne_zero

/-- **Blanchard–Kahn for pencils** (Woodford (2003), App. C.1, p. 670; Blanchard and Kahn 1980):
with `A₀` invertible and any expectation system on a nonempty state space,
`A₀ E_t y_{t+1} = A₁ y_t + w_t` is determinate iff no root of `det(λA₀ − A₁)` lies on the unit
circle, exactly `|X|` roots (with multiplicity) lie in the open unit disc, and the stable
subspace of `A₀⁻¹A₁` meets `{x = 0}` only in `0`. -/
theorem determinatePencil_iff_count [Nonempty Ω] {A0 A1 : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (h : IsUnit A0.det) :
    DeterminatePencil 𝔼 A0 A1 ↔
      (∀ μ ∈ ((pencilPoly A0 A1).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1) ∧
      Multiset.card (((pencilPoly A0 A1).map Complex.ofRealHom).roots.filter
        (fun μ => ‖μ‖ < 1)) = Fintype.card X ∧ GenericX (A0⁻¹ * A1) := by
  rw [determinatePencil_iff 𝔼 h, determinate_iff_count, NoUnit, stableCount, eigs_pencil h]

end Woodford.NeoWicksellianFramework.GeneralBKPencil
