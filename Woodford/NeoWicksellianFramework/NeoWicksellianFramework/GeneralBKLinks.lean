/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.GeneralBK
import NeoWicksellianFramework.ThreeByThree

/-!
# The general Blanchard–Kahn theorem: any index type, and the special cases

Woodford (2003), *Interest and Prices*, Appendix C.1, pp. 670–673 (Props. C.1 and C.2, fn. 1–2)
and Appendix C.3, pp. 677–680 (Prop. 4.4); Blanchard and Kahn (1980).

## Any finite index type

A state indexed by any finite type `ι`, with the predetermined coordinates singled out by an
equivalence `e : ι ≃ Z ⊕ X` (`EquilOn`, `DeterminateOn`, `GenericOn`). `equilOn_iff`,
`determinateOn_iff_determinate`: relabelling the coordinates does not change equilibria;
`determinateOn_iff`, `determinateOn_iff_finrank` (**the Blanchard–Kahn theorem, any index
type**).

## The special cases recovered

* `determinate2_iff_on` (two non-predetermined variables, Prop. C.1) and
  `determinate2_iff_recovered`: `BlanchardKahn.determinate2_iff` re-derived from the general
  result (`unstable_iff_bothOutside`: both roots of `λ² − tr A λ + det A` lie outside the unit
  circle iff every eigenvalue does).
* `determinate3_iff_on` (one predetermined variable, Prop. C.2), `oneInTwoOut_iff_count`,
  `generic_iff_genericOn`, `determinate3_iff_recovered`: `BlanchardKahn.determinate3_iff`
  (`OneInTwoOut ∧ Generic`) re-derived from the general theorem.

## A Chapter 4 model

`prop44_bk_conditions`, `prop44_determinate3`, `prop44_determinate3_iff`: for the inertial
Taylor-rule model of Prop. 4.4 (matrix `ThreeByThree.A44`), the general conditions hold under
(2.9) and a response to inflation or the gap; then the system is determinate for **every**
bounded adapted forcing, not only the IS disturbance, and conversely.
-/

namespace Woodford.NeoWicksellianFramework.GeneralBKLinks

open Polynomial InvariantSplit GeneralBKForward GeneralBK
open scoped Matrix

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)
variable {ι Z X : Type*} [Fintype ι] [Fintype Z] [Fintype X]

/-! ### Any finite index type -/

/-- Woodford (2003), App. C.1, p. 670: a bounded equilibrium of `E_t y_{t+1} = A y_t + w_t` for a
state indexed by `ι`, the predetermined coordinates being `e.symm (inr j)`. -/
def EquilOn (A : Matrix ι ι ℝ) (e : ι ≃ Z ⊕ X) (w : ℕ → ι → Ω → ℝ) (x0 : X → ℝ)
    (y : ℕ → ι → Ω → ℝ) : Prop :=
  Solves 𝔼 A w y ∧ AdaptedV 𝔼 y ∧
    (∀ t j, 𝔼.E t (y (t + 1) (e.symm (Sum.inr j))) = y (t + 1) (e.symm (Sum.inr j))) ∧
    (∀ j, y 0 (e.symm (Sum.inr j)) = fun _ => x0 j) ∧ BoundedV y

/-- Woodford (2003), App. C.1, p. 670: determinacy for a state indexed by `ι`. -/
def DeterminateOn (A : Matrix ι ι ℝ) (e : ι ≃ Z ⊕ X) : Prop :=
  ∀ w : ℕ → ι → Ω → ℝ, BoundedV w → AdaptedV 𝔼 w → ∀ x0 : X → ℝ, ∃! y, EquilOn 𝔼 A e w x0 y

/-- Woodford (2003), App. C.1, p. 672, fn. 2: genericity for a state indexed by `ι`. -/
def GenericOn [DecidableEq ι] (A : Matrix ι ι ℝ) (e : ι ≃ Z ⊕ X) : Prop :=
  ∀ v ∈ boundedOrbits A, (∀ j, v (e.symm (Sum.inr j)) = 0) → v = 0

/-- Woodford (2003), App. C.1, p. 670 (tool): the relabelled matrix acting on the relabelled
vector. -/
theorem mv_reindex (A : Matrix ι ι ℝ) (e : ι ≃ Z ⊕ X) (a : ι → Ω → ℝ) (k : Z ⊕ X) :
    mv (Matrix.reindex e e A) (fun k => a (e.symm k)) k = mv A a (e.symm k) := by
  simp only [mv, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => A (e.symm k) i • a i)

/-- Woodford (2003), App. C.1, p. 670: relabelling the coordinates does not change equilibria. -/
theorem equilOn_iff (A : Matrix ι ι ℝ) (e : ι ≃ Z ⊕ X) (w : ℕ → ι → Ω → ℝ) (x0 : X → ℝ)
    (y : ℕ → ι → Ω → ℝ) :
    EquilOn 𝔼 A e w x0 y ↔ Equil 𝔼 (Matrix.reindex e e A) (fun t k => w t (e.symm k)) x0
      (fun t k => y t (e.symm k)) := by
  unfold EquilOn Equil Solves AdaptedV BoundedV
  simp only [mv_reindex]
  constructor
  · rintro ⟨hs, ha, hk, h0, M, hM⟩
    exact ⟨fun t k => hs t _, fun t k => ha t _, hk, h0, M, fun t k ω => hM t _ ω⟩
  · rintro ⟨hs, ha, hk, h0, M, hM⟩
    refine ⟨fun t i => ?_, fun t i => ?_, hk, h0, M, fun t i ω => ?_⟩
    · simpa using hs t (e i)
    · simpa using ha t (e i)
    · simpa using hM t (e i) ω

/-- Woodford (2003), App. C.1, p. 670: determinacy does not depend on how the coordinates are
labelled. -/
theorem determinateOn_iff_determinate (A : Matrix ι ι ℝ) (e : ι ≃ Z ⊕ X) :
    DeterminateOn 𝔼 A e ↔ Determinate 𝔼 (Matrix.reindex e e A) := by
  constructor
  · intro hd w' hwb hwa x0
    obtain ⟨M, hM⟩ := hwb
    obtain ⟨y, hy, hu⟩ := hd (fun t i => w' t (e i)) ⟨M, fun t i ω => hM t _ ω⟩
      (fun t i => hwa t _) x0
    have hw : (fun t k => (fun t i => w' t (e i)) t (e.symm k)) = w' := by
      funext t k; simp
    refine ⟨fun t k => y t (e.symm k), ?_, fun y' hy' => ?_⟩
    · have := (equilOn_iff 𝔼 A e _ x0 y).mp hy
      rwa [hw] at this
    · have h1 : EquilOn 𝔼 A e (fun t i => w' t (e i)) x0 (fun t i => y' t (e i)) := by
        rw [equilOn_iff, hw]
        simpa using hy'
      have h2 := hu _ h1
      funext t k
      have := congrFun (congrFun h2 t) (e.symm k)
      simpa using this
  · intro hd w hwb hwa x0
    obtain ⟨M, hM⟩ := hwb
    obtain ⟨y', hy', hu⟩ := hd (fun t k => w t (e.symm k)) ⟨M, fun t k ω => hM t _ ω⟩
      (fun t k => hwa t _) x0
    refine ⟨fun t i => y' t (e i), ?_, fun y hy => ?_⟩
    · refine (equilOn_iff 𝔼 A e w x0 _).mpr ?_
      simpa using hy'
    · have h2 := hu _ ((equilOn_iff 𝔼 A e w x0 y).mp hy)
      funext t i
      have := congrFun (congrFun h2 t) (e i)
      simpa using this

/-- Woodford (2003), App. C.1, p. 670 (tool): powers of the relabelled matrix. -/
theorem reindex_pow [DecidableEq ι] [DecidableEq Z] [DecidableEq X] (A : Matrix ι ι ℝ)
    (e : ι ≃ Z ⊕ X) (t : ℕ) :
    Matrix.reindex e e A ^ t = Matrix.reindex e e (A ^ t) := by
  have := map_pow (Matrix.reindexAlgEquiv ℝ ℝ e) A t
  simpa [Matrix.coe_reindexAlgEquiv] using this.symm

/-- Woodford (2003), App. C.1, p. 670 (tool): bounded orbits of the relabelled matrix are the
relabelled bounded orbits. -/
theorem mem_boundedOrbits_reindex [DecidableEq ι] [DecidableEq Z] [DecidableEq X]
    (A : Matrix ι ι ℝ) (e : ι ≃ Z ⊕ X) (v : Z ⊕ X → ℝ) :
    v ∈ boundedOrbits (Matrix.reindex e e A) ↔ (fun i => v (e i)) ∈ boundedOrbits A := by
  have key : ∀ t k, (Matrix.reindex e e A ^ t *ᵥ v) k = (A ^ t *ᵥ fun i => v (e i)) (e.symm k) := by
    intro t k
    rw [reindex_pow, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv (A ^ t) v e.symm e.symm,
      Equiv.symm_symm]
    rfl
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun t i => by have := hC t (e i); rwa [key, e.symm_apply_apply] at this⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, fun t k => by rw [key]; exact hC t _⟩

/-- Woodford (2003), App. C.1, p. 670 (tool): relabelling does not change the eigenvalues. -/
theorem eigs_reindex [DecidableEq ι] [DecidableEq Z] [DecidableEq X] (A : Matrix ι ι ℝ)
    (e : ι ≃ Z ⊕ X) :
    eigs (Matrix.reindex e e A) = eigs A := by
  rw [eigs, eigs]
  congr 1
  rw [show (Matrix.reindex e e A).map Complex.ofReal =
    Matrix.reindex e e (A.map Complex.ofReal) from rfl, Matrix.charpoly_reindex]

/-- Woodford (2003), App. C.1, p. 672: genericity does not depend on the labelling. -/
theorem genericX_reindex_iff [DecidableEq ι] [DecidableEq Z] [DecidableEq X] (A : Matrix ι ι ℝ)
    (e : ι ≃ Z ⊕ X) :
    GenericX (Matrix.reindex e e A) ↔ GenericOn A e := by
  constructor
  · intro hg v hv hvx
    have hv' : (fun k => v (e.symm k)) ∈ boundedOrbits (Matrix.reindex e e A) := by
      rw [mem_boundedOrbits_reindex]
      simpa using hv
    have := hg _ hv' hvx
    funext i
    have := congrFun this (e i)
    simpa using this
  · intro hg v hv hvx
    rw [mem_boundedOrbits_reindex] at hv
    have := hg _ hv (fun j => by simpa using hvx j)
    funext k
    have := congrFun this (e.symm k)
    simpa using this

omit [Fintype Z] in
/-- **The Blanchard–Kahn theorem, any index type** (Woodford (2003), App. C.1, p. 670 and
fn. 1–2; Blanchard and Kahn 1980): for a state indexed by any finite type, with predetermined
coordinates `e.symm (inr j)`, and any expectation system on a nonempty state space, the system is
determinate iff no eigenvalue lies on the unit circle, exactly `|X|` eigenvalues (with
multiplicity) lie in the open unit disc, and genericity holds. -/
theorem determinateOn_iff [Nonempty Ω] [DecidableEq ι] (A : Matrix ι ι ℝ) (e : ι ≃ Z ⊕ X) :
    DeterminateOn 𝔼 A e ↔ NoUnit A ∧ stableCount A = Fintype.card X ∧ GenericOn A e := by
  classical
  have : Finite Z :=
    Finite.of_injective (fun z => e.symm (Sum.inl z)) (fun a b h => by simpa using h)
  have := Fintype.ofFinite Z
  rw [determinateOn_iff_determinate, determinate_iff_count, NoUnit, NoUnit, stableCount,
    stableCount, eigs_reindex, genericX_reindex_iff]

omit [Fintype Z] in
/-- **The Blanchard–Kahn theorem, any index type, dimension form** (Woodford (2003), App. C.1,
p. 670; Blanchard and Kahn 1980): determinate iff no eigenvalue on the unit circle, the stable
(bounded-orbit) subspace has dimension `|X|`, and genericity. -/
theorem determinateOn_iff_finrank [Nonempty Ω] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (e : ι ≃ Z ⊕ X) :
    DeterminateOn 𝔼 A e ↔
      NoUnit A ∧ Module.finrank ℝ (boundedOrbits A) = Fintype.card X ∧ GenericOn A e := by
  rw [determinateOn_iff]
  constructor
  · rintro ⟨hnu, hc, hg⟩
    exact ⟨hnu, (finrank_eq_stableCount hnu).trans hc, hg⟩
  · rintro ⟨hnu, hc, hg⟩
    exact ⟨hnu, (finrank_eq_stableCount hnu).symm.trans hc, hg⟩

/-! ### Two non-predetermined variables: Proposition C.1 recovered -/

/-- Woodford (2003), Prop. C.1, p. 670: the labelling of `Fin 2` with no predetermined
coordinate. -/
def e2 : Fin 2 ≃ Fin 2 ⊕ Fin 0 := (Equiv.sumEmpty (Fin 2) (Fin 0)).symm

/-- Woodford (2003), Prop. C.1, p. 670: with no predetermined variable, an equilibrium is a bounded
adapted solution of `E_t z_{t+1} = A z_t + w_t` (`BlanchardKahn.SolvesE2`). -/
theorem equilOn_e2_iff (A : Matrix (Fin 2) (Fin 2) ℝ) (w y : ℕ → Fin 2 → Ω → ℝ)
    (x0 : Fin 0 → ℝ) :
    EquilOn 𝔼 A e2 w x0 y ↔
      BlanchardKahn.SolvesE2 𝔼 A w y ∧ BlanchardKahn.VAdapted 𝔼 y ∧ BlanchardKahn.VBounded y := by
  unfold EquilOn
  constructor
  · rintro ⟨hs, ha, -, -, hb⟩
    exact ⟨hs, ha, hb⟩
  · rintro ⟨hs, ha, hb⟩
    exact ⟨hs, ha, fun _ j => j.elim0, fun j => j.elim0, hb⟩

/-- Woodford (2003), Prop. C.1, p. 670: `BlanchardKahn.Determinate2` is the general determinacy
notion with no predetermined variable. -/
theorem determinate2_iff_on (A : Matrix (Fin 2) (Fin 2) ℝ) :
    BlanchardKahn.Determinate2 𝔼 A ↔ DeterminateOn 𝔼 A e2 := by
  constructor
  · intro hd w hwb hwa x0
    obtain ⟨z, hz, hu⟩ := hd w hwb hwa
    exact ⟨z, (equilOn_e2_iff 𝔼 A w z x0).mpr hz,
      fun y hy => hu y ((equilOn_e2_iff 𝔼 A w y x0).mp hy)⟩
  · intro hd w hwb hwa
    obtain ⟨y, hy, hu⟩ := hd w hwb hwa Fin.elim0
    exact ⟨y, (equilOn_e2_iff 𝔼 A w y _).mp hy,
      fun z hz => hu z ((equilOn_e2_iff 𝔼 A w z _).mpr hz)⟩

/-- Woodford (2003), Prop. C.1, p. 670: the eigenvalues of a `2 × 2` matrix are the roots of
`λ² − tr A λ + det A`. -/
theorem mem_eigs_two (A : Matrix (Fin 2) (Fin 2) ℝ) (μ : ℂ) :
    μ ∈ eigs A ↔ μ ^ 2 - (tr2 A : ℂ) * μ + (det2 A : ℂ) = 0 := by
  rw [mem_eigs_iff, Matrix.det_fin_two]
  simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.map_apply, Matrix.diagonal_apply_eq,
    ne_eq, Fin.isValue, zero_ne_one, not_false_eq_true, Matrix.diagonal_apply_ne,
    one_ne_zero, zero_sub, tr2, det2]
  push_cast
  constructor <;> intro h <;> linear_combination h

/-- Woodford (2003), Prop. C.1, p. 670: both roots of `λ² − tr A λ + det A` lie outside the unit
circle iff every eigenvalue of `A` does. -/
theorem unstable_iff_bothOutside (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ μ ∈ eigs A, 1 < ‖μ‖) ↔ SchurCohn.BothOutside (tr2 A) (det2 A) := by
  constructor
  · intro h
    exact ⟨h _ ((mem_eigs_two A _).mpr (root_eq _ _ _ (Or.inl rfl))),
      h _ ((mem_eigs_two A _).mpr (root_eq _ _ _ (Or.inr rfl)))⟩
  · intro h μ hμ
    rcases eq_root_of_eq ((mem_eigs_two A μ).mp hμ) with e | e
    · rw [e]; exact h.1
    · rw [e]; exact h.2

/-- Woodford (2003), Prop. C.1, p. 670, from the general theorem: with two non-predetermined
variables, determinate iff every eigenvalue lies outside the closed unit disc. -/
theorem determinate2_iff_eigs [Nonempty Ω] (A : Matrix (Fin 2) (Fin 2) ℝ) :
    BlanchardKahn.Determinate2 𝔼 A ↔ ∀ μ ∈ eigs A, 1 < ‖μ‖ := by
  rw [determinate2_iff_on, determinateOn_iff, Fintype.card_fin]
  constructor
  · rintro ⟨hnu, hc, -⟩ μ hμ
    rw [stableCount, Multiset.card_eq_zero, Multiset.filter_eq_nil] at hc
    exact lt_of_le_of_ne (not_lt.mp (hc μ hμ)) (Ne.symm (hnu μ hμ))
  · intro h
    refine ⟨fun μ hμ h1 => by have := h μ hμ; rw [h1] at this; exact lt_irrefl _ this, ?_, ?_⟩
    · rw [stableCount, Multiset.card_eq_zero, Multiset.filter_eq_nil]
      exact fun μ hμ => not_lt.mpr (h μ hμ).le
    · intro v hv _
      rw [boundedOrbits_eq_bot_of_unstable h] at hv
      exact (Submodule.mem_bot ℝ).mp hv

/-- **Proposition C.1 recovered from the general Blanchard–Kahn theorem** (Woodford (2003),
p. 670): the statement of `BlanchardKahn.determinate2_iff`, re-derived through
`determinateOn_iff` — determinate iff both eigenvalues lie outside the unit circle. -/
theorem determinate2_iff_recovered [Nonempty Ω] (A : Matrix (Fin 2) (Fin 2) ℝ) :
    BlanchardKahn.Determinate2 𝔼 A ↔ SchurCohn.BothOutside (tr2 A) (det2 A) :=
  (determinate2_iff_eigs 𝔼 A).trans (unstable_iff_bothOutside A)

/-! ### One predetermined variable: Proposition C.2 recovered -/

/-- Woodford (2003), Prop. C.2, p. 672: the labelling of `Fin 3` with index `2` predetermined. -/
def e3 : Fin 3 ≃ Fin 2 ⊕ Fin 1 := (finSumFinEquiv (m := 2) (n := 1)).symm

/-- Woodford (2003), Prop. C.2, p. 672: the predetermined coordinate is index `2`. -/
theorem e3_symm_inr (j : Fin 1) : e3.symm (Sum.inr j) = 2 := by
  rw [Fin.fin_one_eq_zero j]
  simp only [e3, Equiv.symm_symm]
  rfl

/-- Woodford (2003), Prop. C.2, p. 672: the general equilibrium notion for `e3` is
`BlanchardKahn.Equil3`. -/
theorem equilOn_e3_iff (A : Matrix (Fin 3) (Fin 3) ℝ) (w y : ℕ → Fin 3 → Ω → ℝ)
    (x0 : Fin 1 → ℝ) :
    EquilOn 𝔼 A e3 w x0 y ↔ BlanchardKahn.Equil3 𝔼 A w (x0 0) y := by
  unfold EquilOn BlanchardKahn.Equil3
  simp only [e3_symm_inr, Fin.forall_fin_one]
  constructor
  · rintro ⟨hs, ha, hk, h0, hb⟩
    exact ⟨hs, ha, hk, h0, hb⟩
  · rintro ⟨hs, ha, hk, h0, hb⟩
    exact ⟨hs, ha, hk, h0, hb⟩

/-- Woodford (2003), Prop. C.2, p. 672: `BlanchardKahn.Determinate3` is the general determinacy
notion with index `2` predetermined. -/
theorem determinate3_iff_on (A : Matrix (Fin 3) (Fin 3) ℝ) :
    BlanchardKahn.Determinate3 𝔼 A ↔ DeterminateOn 𝔼 A e3 := by
  constructor
  · intro hd w hwb hwa x0
    obtain ⟨y, hy, hu⟩ := hd w hwb hwa (x0 0)
    exact ⟨y, (equilOn_e3_iff 𝔼 A w y x0).mpr hy,
      fun y' hy' => hu y' ((equilOn_e3_iff 𝔼 A w y' x0).mp hy')⟩
  · intro hd w hwb hwa x0
    obtain ⟨y, hy, hu⟩ := hd w hwb hwa (fun _ => x0)
    exact ⟨y, (equilOn_e3_iff 𝔼 A w y _).mp hy,
      fun y' hy' => hu y' ((equilOn_e3_iff 𝔼 A w y' (fun _ => x0)).mpr hy')⟩

/-- Woodford (2003), Prop. C.2, p. 672: genericity for `e3` says no nonzero bounded orbit starts
with a zero predetermined component. -/
theorem genericOn_e3_iff (A : Matrix (Fin 3) (Fin 3) ℝ) :
    GenericOn A e3 ↔ ∀ v ∈ boundedOrbits A, v 2 = 0 → v = 0 := by
  simp only [GenericOn, e3_symm_inr, Fin.forall_fin_one]

/-- Woodford (2003), Prop. C.2, p. 672: the characteristic polynomial of a `3 × 3` matrix,
`det(z I − A) = z³ + A₂z² + A₁z + A₀`, over `ℂ`. -/
theorem eval_charpoly_three (A : Matrix (Fin 3) (Fin 3) ℝ) (z : ℂ) :
    (A.map Complex.ofReal).charpoly.eval z =
      SchurCohn.cubic (BlanchardKahn.ch2 A) (BlanchardKahn.ch1 A) (BlanchardKahn.ch0 A) z := by
  rw [Matrix.eval_charpoly, Matrix.det_fin_three]
  simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.map_apply, Matrix.diagonal_apply,
    SchurCohn.cubic, BlanchardKahn.ch2, BlanchardKahn.ch1, BlanchardKahn.ch0]
  simp
  ring

/-- Woodford (2003), Prop. C.2, p. 672: a factorisation of the characteristic cubic identifies the
eigenvalues with multiplicity. -/
theorem eigs_of_factors {A : Matrix (Fin 3) (Fin 3) ℝ} {l1 l2 l3 : ℂ}
    (h : SchurCohn.Factors (BlanchardKahn.ch2 A) (BlanchardKahn.ch1 A) (BlanchardKahn.ch0 A)
      l1 l2 l3) :
    eigs A = {l1} + {l2} + {l3} := by
  have hp : (A.map Complex.ofReal).charpoly = (X - C l1) * (X - C l2) * (X - C l3) := by
    refine Polynomial.funext fun z => ?_
    rw [eval_charpoly_three, h z]
    simp
  rw [eigs, hp, roots_mul, roots_mul, roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
  · exact mul_ne_zero (X_sub_C_ne_zero l1) (X_sub_C_ne_zero l2)
  · exact mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero l1) (X_sub_C_ne_zero l2)) (X_sub_C_ne_zero l3)

/-- Woodford (2003), Prop. C.2, p. 672: "one eigenvalue inside and two outside the unit circle"
is "no eigenvalue on the circle and exactly one inside". -/
theorem oneInTwoOut_iff_count (A : Matrix (Fin 3) (Fin 3) ℝ) :
    SchurCohn.OneInTwoOut (BlanchardKahn.ch2 A) (BlanchardKahn.ch1 A) (BlanchardKahn.ch0 A) ↔
      NoUnit A ∧ stableCount A = 1 := by
  constructor
  · rintro ⟨l1, l2, l3, F, h1, h2, h3⟩
    have he := eigs_of_factors F
    refine ⟨fun μ hμ => ?_, ?_⟩
    · rw [he] at hμ
      simp only [Multiset.mem_add, Multiset.mem_singleton] at hμ
      rcases hμ with (rfl | rfl) | rfl
      · exact ne_of_lt h1
      · exact ne_of_gt h2
      · exact ne_of_gt h3
    · rw [stableCount, he, Multiset.filter_add, Multiset.filter_add, Multiset.filter_singleton,
        Multiset.filter_singleton, Multiset.filter_singleton]
      simp [h1, not_lt.mpr h2.le, not_lt.mpr h3.le]
  · rintro ⟨hnu, hc⟩
    obtain ⟨l1, hl1⟩ := Multiset.card_eq_one.mp hc
    set rest := (eigs A).filter (fun μ => ¬ ‖μ‖ < 1) with hrest
    have hsplit : eigs A = {l1} + rest := by
      rw [← hl1, hrest]
      exact (Multiset.filter_add_not _ _).symm
    have hcard : Multiset.card rest = 2 := by
      have := card_eigs A
      rw [hsplit, Multiset.card_add, Multiset.card_singleton, Fintype.card_fin] at this
      omega
    obtain ⟨l2, l3, hr⟩ := Multiset.card_eq_two.mp hcard
    have hmem1 : l1 ∈ (eigs A).filter (fun μ => ‖μ‖ < 1) := by
      rw [hl1]; exact Multiset.mem_singleton_self l1
    have hout : ∀ μ ∈ rest, 1 < ‖μ‖ := by
      intro μ hμ
      rw [hrest, Multiset.mem_filter] at hμ
      exact lt_of_le_of_ne (not_lt.mp hμ.2) (Ne.symm (hnu μ hμ.1))
    refine ⟨l1, l2, l3, fun z => ?_, (Multiset.mem_filter.mp hmem1).2,
      hout l2 (by rw [hr]; simp), hout l3 (by rw [hr]; simp)⟩
    have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
      (Matrix.charpoly_monic (A.map Complex.ofReal)) (by rw [IsAlgClosed.card_roots_eq_natDegree])
    rw [← eval_charpoly_three, ← hprod]
    change Polynomial.eval z ((Multiset.map (fun a => X - C a) (eigs A)).prod) = _
    rw [hsplit, hr, Polynomial.eval_multiset_prod]
    simp only [Multiset.map_add, Multiset.map_singleton, Multiset.insert_eq_cons,
      Multiset.map_cons, Multiset.prod_add, Multiset.prod_singleton, Multiset.prod_cons,
      eval_sub, eval_X, eval_C]
    ring

/-- Woodford (2003), Prop. C.2, p. 672, fn. 2: with no eigenvalue on the unit circle and exactly
one inside, the book's genericity (`BlanchardKahn.Generic`: the stable real eigenvector has a
nonzero predetermined component) is the general genericity condition. -/
theorem generic_iff_genericOn {A : Matrix (Fin 3) (Fin 3) ℝ} (h : NoUnit A ∧ stableCount A = 1) :
    BlanchardKahn.Generic A ↔ GenericOn A e3 := by
  rw [genericOn_e3_iff]
  constructor
  · intro hg v hv h2
    set B := boundedOrbits A with hB
    have hd : Module.finrank ℝ B = 1 := (finrank_eq_stableCount h.1).trans h.2
    obtain ⟨T, -, hexp⟩ := restrict_block A B (fun v hv => mulVec_mem_boundedOrbits hv)
    set bV := Module.finBasis ℝ B with hbV
    set i0 : Fin (Module.finrank ℝ B) := ⟨0, by rw [hd]; norm_num⟩ with hi0
    have hall : ∀ i : Fin (Module.finrank ℝ B), i = i0 := fun i => by
      have := i.isLt
      exact Fin.ext (by simp only [hi0]; omega)
    set b : Fin 3 → ℝ := (bV i0 : Fin 3 → ℝ) with hb
    set lam : ℝ := T i0 i0 with hlam
    have hAb : A *ᵥ b = lam • b := by
      rw [hb, hexp i0, Finset.sum_eq_single i0 (fun i _ hi => absurd (hall i) hi)
        (fun h => absurd (Finset.mem_univ _) h)]
    have hb0 : b ≠ 0 := by
      intro h0
      apply bV.ne_zero i0
      exact Subtype.ext h0
    obtain ⟨k, hk⟩ : ∃ k, b k ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hb0 (funext hne)
    obtain ⟨C, hC⟩ := (bV i0).2
    have hlam1 : ‖(lam : ℂ)‖ ≤ 1 := by
      refine norm_le_one_of_bounded_pow_mul (z := (b k : ℂ)) (by exact_mod_cast hk) (C := C)
        fun t => ?_
      have e := congrFun (pow_mulVec_eigvec hAb t) k
      have := hC t k
      rw [e] at this
      simp only [Pi.smul_apply, smul_eq_mul] at this
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs]
      exact this
    have hlamE : (lam : ℂ) ∈ eigs A := by
      refine mem_eigs_of_eigvec (c := fun i => (b i : ℂ)) ?_ ?_
      · intro hc
        apply hk
        have := congrFun hc k
        simpa using this
      · rw [map_ofReal_mulVec, hAb]
        funext i
        simp
    have hlam : |lam| < 1 := by
      have := lt_of_le_of_ne hlam1 (h.1 _ hlamE)
      rwa [Complex.norm_real, Real.norm_eq_abs] at this
    have hb2 : b 2 ≠ 0 := fun h2' => hb0 (hg lam b hlam hAb h2')
    have hv' := bV.sum_repr ⟨v, hv⟩
    have hvb : v = (bV.repr ⟨v, hv⟩ i0) • b := by
      have h1 : (⟨v, hv⟩ : B) = (bV.repr ⟨v, hv⟩ i0) • bV i0 :=
        calc (⟨v, hv⟩ : B) = ∑ i, bV.repr ⟨v, hv⟩ i • bV i := hv'.symm
          _ = (bV.repr ⟨v, hv⟩ i0) • bV i0 :=
            Finset.sum_eq_single i0 (fun i _ hi => absurd (hall i) hi)
              (fun h => absurd (Finset.mem_univ _) h)
      have := congrArg Subtype.val h1
      simpa [hb] using this
    have hc0 : bV.repr ⟨v, hv⟩ i0 = 0 := by
      have := congrFun hvb 2
      rw [h2, Pi.smul_apply, smul_eq_mul] at this
      exact (mul_eq_zero.mp this.symm).resolve_right hb2
    rw [hvb, hc0, zero_smul]
  · intro hg μ v hμ hv h2
    refine hg v ⟨∑ i, |v i|, fun t i => ?_⟩ h2
    rw [pow_mulVec_eigvec hv t, Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
    calc |μ| ^ t * |v i| ≤ 1 * |v i| :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (abs_nonneg _) hμ.le) (abs_nonneg _)
      _ ≤ ∑ i, |v i| := by
          rw [one_mul]
          exact Finset.single_le_sum (f := fun i => |v i|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ i)

/-- **Proposition C.2 recovered from the general Blanchard–Kahn theorem** (Woodford (2003),
p. 672, first sentence, with the genericity of fn. 2): the statement of
`BlanchardKahn.determinate3_iff`, re-derived through `determinateOn_iff` — determinate iff one
eigenvalue inside and two outside the unit circle, and the stable eigenvector has a nonzero
predetermined component. -/
theorem determinate3_iff_recovered [Nonempty Ω] (A : Matrix (Fin 3) (Fin 3) ℝ) :
    BlanchardKahn.Determinate3 𝔼 A ↔
      SchurCohn.OneInTwoOut (BlanchardKahn.ch2 A) (BlanchardKahn.ch1 A) (BlanchardKahn.ch0 A) ∧
        BlanchardKahn.Generic A := by
  rw [determinate3_iff_on, determinateOn_iff, Fintype.card_fin]
  constructor
  · rintro ⟨hnu, hc, hg⟩
    exact ⟨(oneInTwoOut_iff_count A).mpr ⟨hnu, hc⟩, (generic_iff_genericOn ⟨hnu, hc⟩).mpr hg⟩
  · rintro ⟨ho, hg⟩
    have h := (oneInTwoOut_iff_count A).mp ho
    exact ⟨h.1, h.2, (generic_iff_genericOn h).mp hg⟩

/-! ### The inertial Taylor-rule model of Proposition 4.4 -/

/-- Woodford (2003), Prop. 4.4, p. 255 (App. C.3): under the sign restrictions, (2.9) and a
response to inflation or the gap, the matrix `A` of (C.21) satisfies the general Blanchard–Kahn
conditions (no unit eigenvalue, one stable eigenvalue, genericity). -/
theorem prop44_bk_conditions {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (h29 : 1 - ρ < φπ + (1 - β) / (4 * κ) * φx) (hφ : 0 < φπ ∨ 0 < φx) :
    NoUnit (ThreeByThree.A44 β κ σ ρ φπ φx) ∧ stableCount (ThreeByThree.A44 β κ σ ρ φπ φx) = 1 ∧
      GenericOn (ThreeByThree.A44 β κ σ ρ φπ φx) e3 := by
  have h := (oneInTwoOut_iff_count _).mp
    (ThreeByThree.oneInTwoOut_A44 hβ0 hβ1 hκ hσ hρ hφπ hφx h29)
  exact ⟨h.1, h.2, (generic_iff_genericOn h).mp
    (ThreeByThree.generic_A44 hβ0 hβ1 hκ hφπ hφx hφ)⟩

/-- Woodford (2003), Prop. 4.4, p. 255, through the general theorem: under (2.9) and a response
to inflation or the gap, the inertial-rule system is determinate for **every** bounded adapted
forcing vector (not only the IS disturbance of the model). -/
theorem prop44_determinate3 [Nonempty Ω] {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (h29 : 1 - ρ < φπ + (1 - β) / (4 * κ) * φx) (hφ : 0 < φπ ∨ 0 < φx) :
    BlanchardKahn.Determinate3 𝔼 (ThreeByThree.A44 β κ σ ρ φπ φx) := by
  rw [determinate3_iff_on, determinateOn_iff, Fintype.card_fin]
  exact prop44_bk_conditions hβ0 hβ1 hκ hσ hρ hφπ hφx h29 hφ

/-- Woodford (2003), Prop. 4.4, p. 255: for the inertial-rule system, determinacy for every bounded
adapted forcing vector holds iff (2.9) holds and the rule responds to inflation or the gap — the
same condition as for the model's own disturbance (`ThreeByThree.prop44`). -/
theorem prop44_determinate3_iff [Nonempty Ω] {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    BlanchardKahn.Determinate3 𝔼 (ThreeByThree.A44 β κ σ ρ φπ φx) ↔
      1 - ρ < φπ + (1 - β) / (4 * κ) * φx ∧ (0 < φπ ∨ 0 < φx) := by
  constructor
  · intro hd
    exact (ThreeByThree.prop44 𝔼 hβ0 hβ1 hκ hσ hρ hφπ hφx).mp
      ((ThreeByThree.determinate44_iff_for 𝔼 hβ0.ne').mpr
        (BlanchardKahn.determinateFor_of_determinate3 𝔼 hd _))
  · rintro ⟨h29, hφ⟩
    exact prop44_determinate3 𝔼 hβ0 hβ1 hκ hσ hρ hφπ hφx h29 hφ

end Woodford.NeoWicksellianFramework.GeneralBKLinks
