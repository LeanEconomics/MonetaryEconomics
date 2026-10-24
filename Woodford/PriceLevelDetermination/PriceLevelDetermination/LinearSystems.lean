/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.SystemsBKPencil
import PriceLevelDetermination.LocalIFT

/-!
# The linearised `n`-dimensional system (A.10) and the root condition (A.9)

Woodford (2003), *Interest and Prices*, Appendix A.3, pp. 631–633. For `n` equations per period
`f(p_{t−1}, p_t, p_{t+1}; u_t) = 0` the derivative of the sequence-space map at the steady state
is the operator (A.8) `p̂ ↦ (f₁ p̂_{t−1} + f₂ p̂_t + f₃ p̂_{t+1})_t` on `ℓ∞(ℕ, ℝⁿ)` (with
`p̂_{−1} = 0`, fn. 4). The book states without proof that it is invertible — (A.10) has a unique
bounded solution for every bounded forcing and initial condition — "generically if and only if"
`det(f₃λ² + f₂λ + f₁) = 0` (A.9) has exactly `n` roots inside and `n` outside the unit circle.
This module proves the exact statement, says which cases the word "generically" covers, and gives
counterexamples. The proofs reduce (A.10) to the first-order companion pencil in
`y_t = (p̂_t, p̂_{t−1})` and use the general Blanchard–Kahn theorem for regular and singular
pencils (`SystemsBK`, `SystemsBKPencil`, restated from the Chapter 4 project).

## Main results

* `sysOp`, `sysOp_apply`: the operator (A.8) on `SeqV ι = ℓ∞(ℕ, ℝⁿ)`; `isUnit_sysOp_iff`: it is
  invertible iff (A.10) is determinate (`LinDeterminate`); `homInjective_iff_injective`.
* `linDeterminate_iff_pencil`, `pencilPoly_comp`: (A.10) is the companion pencil, whose pencil
  polynomial `det(λA₀ − A₁)` is exactly `det(f₃λ² + f₂λ + f₁)` (`quadPoly`, `eval_quadPoly`);
  `genericPencil_comp_iff`: the pencil genericity condition is `HomInjective`.
* **(A.9) made exact**, `linDeterminate_iff`, `isUnit_sysOp_iff_roots`: invertible iff
  `det(f₃λ² + f₂λ + f₁) ≢ 0`, no root on the unit circle, exactly `n` roots in the open disc
  (with multiplicity), and genericity (no nonzero bounded solution of the homogeneous system with
  `p̂_{−1} = 0`). No condition on `f₃`.
* For `det f₃ ≠ 0` (`natDegree_quadPoly`: degree `2n`): `linDeterminate_iff_of_det` — invertible
  iff `n` roots inside and `n` outside (`BookRootCount`, the printed count) **and** genericity.
  `outside_add_infinite`: in general the roots outside plus the `2n − deg` infinite roots number
  `n`.
* **What "generically" hides** (the only two failures of the printed equivalence):
  `book_count_not_sufficient` — with `f₃ = 1`, `f₂ = 0`, `f₁ = diag(0, −4)` the count holds
  (roots `0, 0, ±2`) but uniqueness fails (genericity fails); `book_count_not_necessary` — with
  `f₃` singular (`n = 1`, `p̂_t = w_t`) the system is determinate but `det(f₃λ² + f₂λ + f₁) = λ`
  has no root outside. Roots on the unit circle never break the equivalence (they always destroy
  invertibility, and for `det f₃ ≠ 0` the count excludes them).
* Which half fails (`not_isUnit_iff`, `failure_cases`): a root on the circle gives non-existence
  (`not_surjective_of_unit`, resonance, invertible `f₃`); more than `n` roots inside gives
  non-uniqueness (`not_injective_of_count_gt`); fewer than `n` inside (no unit root) gives
  non-existence (`not_surjective_of_count_lt`); otherwise genericity fails (non-uniqueness).
* Regularity (used for the nonlinear necessity in `LocalIFTSystems`):
  `quadPoly_ne_zero_of_surjective` (a surjective derivative forces a regular pencil) and
  `eq_zero_of_regular` (then a bounded homogeneous solution is determined by `p̂_0`).
-/

namespace Woodford.PriceLevelDetermination.LinearSystems

open Polynomial SystemsBK.InvariantSplit SystemsBK.GeneralBKForward SystemsBK.GeneralBK
open SystemsBKPencil.GeneralBKPencil SystemsBKPencil.GeneralBKSingular
open scoped Matrix

/-! ### The linearised system on sequences -/

/-- Woodford (2003), App. A.3, eq. (A.10), p. 633: the lagged sequence `x_{t−1}`, with the
predetermined initial condition `x_{−1} = xm`. -/
def lagV {V : Type*} (xm : V) (x : ℕ → V) : ℕ → V
  | 0 => xm
  | t + 1 => x t

/-- Woodford (2003), App. A.3, p. 633: `x_{−1}` is the initial condition. -/
@[simp] theorem lagV_zero {V : Type*} (xm : V) (x : ℕ → V) : lagV xm x 0 = xm := rfl

/-- Woodford (2003), App. A.3, p. 633: the lag of `x` at `t + 1` is `x_t`. -/
@[simp] theorem lagV_succ {V : Type*} (xm : V) (x : ℕ → V) (t : ℕ) : lagV xm x (t + 1) = x t :=
  rfl

/-- Woodford (2003), App. A.3, p. 633: the lag is additive. -/
theorem lagV_add {V : Type*} [Add V] (xm ym : V) (x y : ℕ → V) (t : ℕ) :
    lagV (xm + ym) (x + y) t = lagV xm x t + lagV ym y t := by
  cases t <;> rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Woodford (2003), App. A.3, p. 632: a uniformly bounded sequence of vectors in `ℝⁿ`. -/
def BoundedSeq (x : ℕ → ι → ℝ) : Prop := ∃ C, ∀ t i, |x t i| ≤ C

/-- Woodford (2003), App. A.3, eq. (A.10), p. 633: `x` solves the linearised conditions
`f₁ x_{t−1} + f₂ x_t + f₃ x_{t+1} = w_t` (all `t ≥ 0`) with initial condition `x_{−1} = xm`. -/
def SolvesLin (f₁ f₂ f₃ : Matrix ι ι ℝ) (w : ℕ → ι → ℝ) (xm : ι → ℝ) (x : ℕ → ι → ℝ) : Prop :=
  ∀ t, f₁ *ᵥ lagV xm x t + f₂ *ᵥ x t + f₃ *ᵥ x (t + 1) = w t

/-- Woodford (2003), App. A.3, pp. 632–633: **determinacy of the linearised system** (A.10): for
every bounded forcing `w` and every initial condition `x_{−1}` there is exactly one bounded
solution. -/
def LinDeterminate (f₁ f₂ f₃ : Matrix ι ι ℝ) : Prop :=
  ∀ w : ℕ → ι → ℝ, BoundedSeq w → ∀ xm : ι → ℝ, ∃! x, BoundedSeq x ∧ SolvesLin f₁ f₂ f₃ w xm x

/-- Woodford (2003), App. A.3, p. 632 (the genericity condition behind "generically"): the
homogeneous linearised system with `x_{−1} = 0` has no nonzero bounded solution. -/
def HomInjective (f₁ f₂ f₃ : Matrix ι ι ℝ) : Prop :=
  ∀ x, BoundedSeq x → SolvesLin f₁ f₂ f₃ 0 0 x → x = 0

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 632 (tool): a matrix maps bounded sequences to bounded
sequences. -/
theorem boundedSeq_mulVec (M : Matrix ι ι ℝ) {x : ℕ → ι → ℝ} (hx : BoundedSeq x) :
    BoundedSeq (fun t => M *ᵥ x t) := by
  obtain ⟨C, hC⟩ := hx
  exact ⟨Fintype.card ι * ((∑ i, ∑ j, |M i j|) * C), fun t i =>
    SystemsBK.InvariantSplit.abs_mulVec_le M _ (abs_entry_le_sum M) (hC t) i⟩

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 632 (tool): sums of bounded sequences are bounded. -/
theorem boundedSeq_add {x y : ℕ → ι → ℝ} (hx : BoundedSeq x) (hy : BoundedSeq y) :
    BoundedSeq (fun t => x t + y t) := by
  obtain ⟨C, hC⟩ := hx
  obtain ⟨D, hD⟩ := hy
  exact ⟨C + D, fun t i => (abs_add_le _ _).trans (add_le_add (hC t i) (hD t i))⟩

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 632 (tool): differences of bounded sequences are bounded. -/
theorem boundedSeq_sub {x y : ℕ → ι → ℝ} (hx : BoundedSeq x) (hy : BoundedSeq y) :
    BoundedSeq (fun t => x t - y t) := by
  obtain ⟨C, hC⟩ := hx
  obtain ⟨D, hD⟩ := hy
  exact ⟨C + D, fun t i => (abs_sub _ _).trans (add_le_add (hC t i) (hD t i))⟩

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 632 (tool): the lag of a bounded sequence is bounded. -/
theorem boundedSeq_lagV [Finite ι] (xm : ι → ℝ) {x : ℕ → ι → ℝ} (hx : BoundedSeq x) :
    BoundedSeq (lagV xm x) := by
  have := Fintype.ofFinite ι
  obtain ⟨C, hC⟩ := hx
  refine ⟨max C (∑ i, |xm i|), fun t i => ?_⟩
  cases t with
  | zero =>
    exact (Finset.single_le_sum (f := fun i => |xm i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)).trans (le_max_right _ _)
  | succ t => exact (hC t i).trans (le_max_left _ _)

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 632 (tool): the lead of a bounded sequence is bounded. -/
theorem boundedSeq_succ {x : ℕ → ι → ℝ} (hx : BoundedSeq x) :
    BoundedSeq (fun t => x (t + 1)) := by
  obtain ⟨C, hC⟩ := hx
  exact ⟨C, fun t i => hC (t + 1) i⟩

/-! ### The companion pencil (first-order `2n` system) -/

/-- Woodford (2003), App. A.3, eq. (A.10), p. 633, as a first-order system in
`y_t = (x_t, x_{t−1})` (non-predetermined block `x_t`, predetermined block `x_{t−1}`): the
left-hand matrix `A₀ = diag(f₃, 1)` of `A₀ y_{t+1} = A₁ y_t + w_t`. -/
def compA0 (f₃ : Matrix ι ι ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ := Matrix.fromBlocks f₃ 0 0 1

/-- Woodford (2003), App. A.3, eq. (A.10), p. 633: the right-hand matrix
`A₁ = [[−f₂, −f₁], [1, 0]]` of the companion pencil. -/
def compA1 (f₁ f₂ : Matrix ι ι ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ := Matrix.fromBlocks (-f₂) (-f₁) 1 0

/-- Woodford (2003), App. A.3, eq. (A.10), p. 633: one step of the companion pencil is one
period of (A.10), `f₁ k + f₂ z + f₃ z' = a`, together with the definition `k' = z + b` of the
predetermined block. -/
theorem comp_step (f₁ f₂ f₃ : Matrix ι ι ℝ) (y y' W : ι ⊕ ι → ℝ) :
    compA0 f₃ *ᵥ y' = compA1 f₁ f₂ *ᵥ y + W ↔
      f₁ *ᵥ (y ∘ Sum.inr) + f₂ *ᵥ (y ∘ Sum.inl) + f₃ *ᵥ (y' ∘ Sum.inl) = W ∘ Sum.inl ∧
        y' ∘ Sum.inr = y ∘ Sum.inl + W ∘ Sum.inr := by
  rw [compA0, compA1, Matrix.fromBlocks_mulVec, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, Matrix.one_mulVec, add_zero, zero_add, Matrix.neg_mulVec]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · funext i
      have := congrFun h (Sum.inl i)
      simp only [Sum.elim_inl, Pi.add_apply, Pi.neg_apply] at this
      simp only [Pi.add_apply, Function.comp_apply]
      linarith
    · funext i
      have := congrFun h (Sum.inr i)
      simpa only [Sum.elim_inr, Pi.add_apply, Function.comp_apply] using this
  · rintro ⟨h1, h2⟩
    funext j
    cases j with
    | inl i =>
      have := congrFun h1 i
      simp only [Pi.add_apply, Function.comp_apply] at this
      simp only [Sum.elim_inl, Pi.add_apply, Pi.neg_apply]
      linarith
    | inr i =>
      have := congrFun h2 i
      simpa only [Sum.elim_inr, Pi.add_apply, Function.comp_apply] using this

/-- Woodford (2003), App. A.3, p. 633 (tool): the lag of the zero sequence from zero is zero. -/
theorem lagV_zero_zero {V : Type*} [Zero V] (t : ℕ) : lagV (0 : V) (fun _ => 0) t = 0 := by
  cases t <;> rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 632 (tool): a sequence of stacked vectors `(u_t, v_t)` is
bounded when both blocks are. -/
theorem boundedSeq_elim {u v : ℕ → ι → ℝ} (hu : BoundedSeq u) (hv : BoundedSeq v) :
    BoundedSeq (fun t => (Sum.elim (u t) (v t) : ι ⊕ ι → ℝ)) := by
  obtain ⟨C, hC⟩ := hu
  obtain ⟨D, hD⟩ := hv
  refine ⟨max C D, fun t j => ?_⟩
  cases j with
  | inl i => exact (hC t i).trans (le_max_left _ _)
  | inr i => exact (hD t i).trans (le_max_right _ _)

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 632 (tool): the first block of a bounded stacked sequence is
bounded. -/
theorem boundedSeq_inl {Y : ℕ → ι ⊕ ι → ℝ} (h : BoundedSeq Y) :
    BoundedSeq (fun t => Y t ∘ Sum.inl) := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun t i => hC t (Sum.inl i)⟩

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 632 (tool): the second block of a bounded stacked sequence is
bounded. -/
theorem boundedSeq_inr {Y : ℕ → ι ⊕ ι → ℝ} (h : BoundedSeq Y) :
    BoundedSeq (fun t => Y t ∘ Sum.inr) := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun t i => hC t (Sum.inr i)⟩

/-- Woodford (2003), App. A.3, eq. (A.10), p. 633: a solution `y_t = (z_t, k_t)` of the companion
pencil with forcing `(a_t, b_t)` has `k_t = z_{t−1} + b_{t−1}` (with `k_0` given), and `z` solves
(A.10) with initial condition `k_0` and forcing `a_t − f₁ b_{t−1}`. -/
theorem lin_of_pencil {f₁ f₂ f₃ : Matrix ι ι ℝ} {Y W : ℕ → ι ⊕ ι → ℝ}
    (h : ∀ t, compA0 f₃ *ᵥ Y (t + 1) = compA1 f₁ f₂ *ᵥ Y t + W t) :
    (∀ t, Y t ∘ Sum.inr =
        lagV (Y 0 ∘ Sum.inr) (fun s => Y s ∘ Sum.inl) t + lagV 0 (fun s => W s ∘ Sum.inr) t) ∧
      SolvesLin f₁ f₂ f₃ (fun t => W t ∘ Sum.inl - f₁ *ᵥ lagV 0 (fun s => W s ∘ Sum.inr) t)
        (Y 0 ∘ Sum.inr) (fun s => Y s ∘ Sum.inl) := by
  have hk : ∀ t, Y t ∘ Sum.inr =
      lagV (Y 0 ∘ Sum.inr) (fun s => Y s ∘ Sum.inl) t + lagV 0 (fun s => W s ∘ Sum.inr) t := by
    intro t
    cases t with
    | zero => simp
    | succ t => simpa using ((comp_step f₁ f₂ f₃ _ _ _).mp (h t)).2
  refine ⟨hk, fun t => ?_⟩
  have h1 := ((comp_step f₁ f₂ f₃ _ _ _).mp (h t)).1
  rw [hk t, Matrix.mulVec_add] at h1
  beta_reduce
  rw [← h1]
  abel

/-- Woodford (2003), App. A.3, eq. (A.10), p. 633: conversely, a solution `z` of (A.10) with
initial condition `x_{−1}` and forcing `a_t − f₁ b_{t−1}` gives the solution
`y_t = (z_t, x_{t−1}-part + b_{t−1})` of the companion pencil with forcing `(a_t, b_t)`. -/
theorem pencil_of_lin {f₁ f₂ f₃ : Matrix ι ι ℝ} {W : ℕ → ι ⊕ ι → ℝ} {xm : ι → ℝ}
    {z : ℕ → ι → ℝ}
    (h : SolvesLin f₁ f₂ f₃ (fun t => W t ∘ Sum.inl - f₁ *ᵥ lagV 0 (fun s => W s ∘ Sum.inr) t)
      xm z) (t : ℕ) :
    compA0 f₃ *ᵥ (Sum.elim (z (t + 1))
        (lagV xm z (t + 1) + lagV 0 (fun s => W s ∘ Sum.inr) (t + 1)) : ι ⊕ ι → ℝ) =
      compA1 f₁ f₂ *ᵥ (Sum.elim (z t) (lagV xm z t + lagV 0 (fun s => W s ∘ Sum.inr) t)) +
        W t := by
  rw [comp_step]
  constructor
  · simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    have h1 := h t
    beta_reduce at h1
    rw [eq_sub_iff_add_eq] at h1
    rw [Matrix.mulVec_add, ← h1]
    abel
  · simp

/-! ### Perfect foresight: the pencil system of the general Blanchard–Kahn theorem -/

/-- Woodford (2003), App. A.3, p. 631 (tool): a deterministic process (perfect foresight, a
single state of the world) as a sequence of vectors. -/
def dseq {κ : Type*} (y : ℕ → κ → Unit → ℝ) : ℕ → κ → ℝ := fun t i => y t i ()

/-- Woodford (2003), App. A.3, p. 631 (tool): coordinates of `dseq`. -/
theorem dseq_apply {κ : Type*} (y : ℕ → κ → Unit → ℝ) (t : ℕ) : dseq y t = fun i => y t i () :=
  rfl

/-- Woodford (2003), App. A.3, p. 631 (tool): a sequence of vectors as a deterministic
process. -/
def useq {κ : Type*} (Y : ℕ → κ → ℝ) : ℕ → κ → Unit → ℝ := fun t i _ => Y t i

/-- Woodford (2003), App. A.3, p. 631 (tool): `useq` inverts `dseq`. -/
theorem useq_dseq {κ : Type*} (y : ℕ → κ → Unit → ℝ) : useq (dseq y) = y := by
  funext t i u
  cases u
  rfl

/-- Woodford (2003), App. A.3, p. 631 (tool): under perfect foresight a process is bounded iff
its sequence of vectors is. -/
theorem boundedV_iff {κ : Type*} (y : ℕ → κ → Unit → ℝ) :
    BoundedV y ↔ ∃ C, ∀ t i, |dseq y t i| ≤ C :=
  ⟨fun ⟨M, h⟩ => ⟨M, fun t i => h t i ()⟩, fun ⟨M, h⟩ => ⟨M, fun t i u => by cases u; exact h t i⟩⟩

/-- Woodford (2003), App. A.3, p. 631 (tool): under perfect foresight every process is
adapted. -/
theorem adaptedV_pf {κ : Type*} (y : ℕ → κ → Unit → ℝ) : AdaptedV perfectForesight y :=
  fun _ _ => rfl

/-- Woodford (2003), App. A.3, p. 631: under perfect foresight the pencil system
`A₀ y_{t+1} = A₁ y_t + w_t` holds iff it holds for the sequences of vectors. -/
theorem solvesPencil_pf_iff {κ : Type*} [Fintype κ] (A0 A1 : Matrix κ κ ℝ)
    (w y : ℕ → κ → Unit → ℝ) :
    SolvesPencil perfectForesight A0 A1 w y ↔
      ∀ t, A0 *ᵥ dseq y (t + 1) = A1 *ᵥ dseq y t + dseq w t := by
  have hE : ∀ t (x : Unit → ℝ), perfectForesight.E t x = x := fun _ _ => rfl
  refine forall_congr' fun t => ?_
  constructor
  · intro h
    funext i
    have := congrFun (congrFun h i) ()
    simpa only [mv_apply, Pi.add_apply, hE, dseq_apply] using this
  · intro h
    funext i u
    cases u
    have := congrFun h i
    simpa only [mv_apply, Pi.add_apply, hE, dseq_apply] using this

/-- Woodford (2003), App. A.3, p. 631: under perfect foresight an equilibrium of the pencil
system is a bounded solution of the deterministic system with the given `x_0`. -/
theorem equilPencil_pf_iff {Z X : Type*} [Fintype Z] [Fintype X]
    (A0 A1 : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (w : ℕ → Z ⊕ X → Unit → ℝ) (x0 : X → ℝ)
    (y : ℕ → Z ⊕ X → Unit → ℝ) :
    EquilPencil perfectForesight A0 A1 w x0 y ↔
      (∀ t, A0 *ᵥ dseq y (t + 1) = A1 *ᵥ dseq y t + dseq w t) ∧
        (∀ j, dseq y 0 (Sum.inr j) = x0 j) ∧ ∃ C, ∀ t i, |dseq y t i| ≤ C := by
  unfold EquilPencil
  rw [solvesPencil_pf_iff, boundedV_iff]
  constructor
  · rintro ⟨h1, -, -, h4, h5⟩
    exact ⟨h1, fun j => congrFun (h4 j) (), h5⟩
  · rintro ⟨h1, h4, h5⟩
    refine ⟨h1, adaptedV_pf y, fun _ _ => rfl, fun j => ?_, h5⟩
    funext u
    cases u
    exact h4 j

/-- **(A.10) as a Blanchard–Kahn pencil** (Woodford (2003), App. A.3, pp. 632–633): the
linearised system is determinate (a unique bounded solution for every bounded forcing and every
initial condition) iff the companion pencil `A₀ y_{t+1} = A₁ y_t + w_t`, `y_t = (x_t, x_{t−1})`,
is determinate under perfect foresight. -/
theorem linDeterminate_iff_pencil (f₁ f₂ f₃ : Matrix ι ι ℝ) :
    LinDeterminate f₁ f₂ f₃ ↔ DeterminatePencil perfectForesight (compA0 f₃) (compA1 f₁ f₂) := by
  constructor
  · intro hL w hwb _ x0
    set W := dseq w with hW
    have hWb : BoundedSeq W := (boundedV_iff w).mp hwb
    set b : ℕ → ι → ℝ := fun s => W s ∘ Sum.inr with hb
    have hbb : BoundedSeq b := boundedSeq_inr hWb
    obtain ⟨z, ⟨hzb, hz⟩, hzu⟩ := hL (fun t => W t ∘ Sum.inl - f₁ *ᵥ lagV 0 b t)
      (boundedSeq_sub (boundedSeq_inl hWb) (boundedSeq_mulVec f₁ (boundedSeq_lagV 0 hbb))) x0
    set Y : ℕ → ι ⊕ ι → ℝ := fun t => Sum.elim (z t) (lagV x0 z t + lagV 0 b t) with hY
    refine ⟨useq Y, (equilPencil_pf_iff _ _ _ _ _).mpr ⟨fun t => pencil_of_lin hz t,
      fun j => by simp [dseq, useq, hY], boundedSeq_elim hzb (boundedSeq_add
        (boundedSeq_lagV x0 hzb) (boundedSeq_lagV 0 hbb))⟩, fun y' hy' => ?_⟩
    obtain ⟨h1, h2, h3⟩ := (equilPencil_pf_iff _ _ _ _ _).mp hy'
    obtain ⟨hk, hs⟩ := lin_of_pencil h1
    have h0 : dseq y' 0 ∘ Sum.inr = x0 := funext h2
    rw [h0] at hk hs
    have hz' := hzu _ ⟨boundedSeq_inl h3, hs⟩
    rw [← useq_dseq y']
    congr 1
    funext t j
    cases j with
    | inl i => exact congrFun (congrFun hz' t) i
    | inr i =>
      have := congrFun (hk t) i
      rw [hz'] at this
      exact this
  · intro hD w hwb xm
    set W : ℕ → ι ⊕ ι → ℝ := fun t => Sum.elim (w t) 0 with hW
    have hWb : BoundedSeq W := boundedSeq_elim hwb ⟨0, fun _ _ => by simp⟩
    have hforce : (fun t => W t ∘ Sum.inl - f₁ *ᵥ lagV 0 (fun s => W s ∘ Sum.inr) t) = w := by
      funext t
      simp only [hW, Sum.elim_comp_inl, Sum.elim_comp_inr, lagV_zero_zero, Matrix.mulVec_zero,
        sub_zero]
    obtain ⟨y, hy, hyu⟩ := hD (useq W) ((boundedV_iff _).mpr hWb) (adaptedV_pf _) xm
    obtain ⟨h1, h2, h3⟩ := (equilPencil_pf_iff _ _ _ _ _).mp hy
    obtain ⟨-, hs⟩ := lin_of_pencil h1
    have h0 : dseq y 0 ∘ Sum.inr = xm := funext h2
    rw [h0] at hs
    have hdW : dseq (useq W) = W := rfl
    rw [hdW, hforce] at hs
    refine ⟨fun s => dseq y s ∘ Sum.inl, ⟨boundedSeq_inl h3, hs⟩, fun x' ⟨hx'b, hx'⟩ => ?_⟩
    rw [← hforce] at hx'
    set Y' : ℕ → ι ⊕ ι → ℝ :=
      fun t => Sum.elim (x' t) (lagV xm x' t + lagV 0 (fun s => W s ∘ Sum.inr) t) with hY'
    have hY'b : BoundedSeq Y' := boundedSeq_elim hx'b (boundedSeq_add (boundedSeq_lagV xm hx'b)
      (boundedSeq_lagV 0 (boundedSeq_inr hWb)))
    have he : useq Y' = y := hyu _ ((equilPencil_pf_iff _ _ _ _ _).mpr
      ⟨fun t => pencil_of_lin hx' t, fun j => by simp [dseq, useq, hY'], hY'b⟩)
    funext t
    rw [← he]
    rfl

/-! ### The characteristic polynomial (A.9) -/

/-- Woodford (2003), App. A.3, eq. (A.9), p. 632: the characteristic polynomial
`det(f₃λ² + f₂λ + f₁)` of the linearised system (A.10). -/
noncomputable def quadPoly (f₁ f₂ f₃ : Matrix ι ι ℝ) : ℝ[X] :=
  (Matrix.scalar ι (X ^ 2 : ℝ[X]) * (C : ℝ →+* ℝ[X]).mapMatrix f₃ +
    Matrix.scalar ι (X : ℝ[X]) * (C : ℝ →+* ℝ[X]).mapMatrix f₂ +
      (C : ℝ →+* ℝ[X]).mapMatrix f₁).det

/-- Woodford (2003), App. A.3, eq. (A.9), p. 632: the value of the characteristic polynomial at
`r` is `det(r² f₃ + r f₂ + f₁)`. -/
theorem eval_quadPoly (f₁ f₂ f₃ : Matrix ι ι ℝ) (r : ℝ) :
    (quadPoly f₁ f₂ f₃).eval r = (r ^ 2 • f₃ + r • f₂ + f₁).det := by
  rw [quadPoly, eval_det_mapMatrix]
  congr 1
  rw [map_add, map_add, map_mul, map_mul]
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.smul_apply]

/-- Woodford (2003), App. A.3, eq. (A.9), p. 632 (tool): for `r ≠ 0`,
`det(r A₀ − A₁) = det(r² f₃ + r f₂ + f₁)` for the companion pencil. -/
theorem det_comp_pencil (f₁ f₂ f₃ : Matrix ι ι ℝ) {r : ℝ} (hr : r ≠ 0) :
    (r • compA0 f₃ - compA1 f₁ f₂).det = (r ^ 2 • f₃ + r • f₂ + f₁).det := by
  have hM : r • compA0 f₃ - compA1 f₁ f₂ =
      Matrix.fromBlocks (r • f₃ + f₂) f₁ (-1) (r • (1 : Matrix ι ι ℝ)) := by
    rw [compA0, compA1, Matrix.fromBlocks_smul, sub_eq_add_neg, Matrix.fromBlocks_neg,
      Matrix.fromBlocks_add]
    simp only [smul_zero, neg_neg, zero_add, neg_zero, add_zero]
  have hR : (Matrix.fromBlocks (1 : Matrix ι ι ℝ) 0 (r⁻¹ • (1 : Matrix ι ι ℝ)) 1).det = 1 := by
    rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]
  have hP : Matrix.fromBlocks (r • f₃ + f₂) f₁ (-1) (r • (1 : Matrix ι ι ℝ)) *
      Matrix.fromBlocks (1 : Matrix ι ι ℝ) 0 (r⁻¹ • (1 : Matrix ι ι ℝ)) 1 =
      Matrix.fromBlocks (r • f₃ + f₂ + r⁻¹ • f₁) f₁ 0 (r • (1 : Matrix ι ι ℝ)) := by
    rw [Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · simp
    · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hr, one_smul,
        Matrix.mul_one, Matrix.mul_one, neg_add_cancel]
    · simp
  have hD : ((r • f₃ + f₂ + r⁻¹ • f₁) * (r • (1 : Matrix ι ι ℝ))) =
      r ^ 2 • f₃ + r • f₂ + f₁ := by
    rw [Matrix.mul_smul, Matrix.mul_one, smul_add, smul_add, smul_smul, smul_smul,
      mul_inv_cancel₀ hr, one_smul, pow_two]
  rw [hM, ← mul_one (Matrix.det _), ← hR, ← Matrix.det_mul, hP, Matrix.det_fromBlocks_zero₂₁,
    ← Matrix.det_mul, hD]

/-- Woodford (2003), App. A.3, eq. (A.9), p. 632: **the pencil polynomial of the companion system
is the characteristic polynomial (A.9)**, `det(λA₀ − A₁) = det(f₃λ² + f₂λ + f₁)`. -/
theorem pencilPoly_comp (f₁ f₂ f₃ : Matrix ι ι ℝ) :
    pencilPoly (compA0 f₃) (compA1 f₁ f₂) = quadPoly f₁ f₂ f₃ := by
  refine Polynomial.eq_of_infinite_eval_eq _ _ ((Set.finite_singleton (0 : ℝ)).infinite_compl.mono
    fun r hr => ?_)
  rw [Set.mem_compl_singleton_iff] at hr
  rw [Set.mem_ofPred_eq, eval_pencilPoly, eval_quadPoly, det_comp_pencil f₁ f₂ f₃ hr]

/-- Woodford (2003), App. A.3, p. 632 (tool): the homogeneous companion pencil solved by a
solution of the homogeneous (A.10). -/
theorem pencil_of_lin_zero {f₁ f₂ f₃ : Matrix ι ι ℝ} {xm : ι → ℝ} {z : ℕ → ι → ℝ}
    (h : SolvesLin f₁ f₂ f₃ 0 xm z) (t : ℕ) :
    compA0 f₃ *ᵥ (Sum.elim (z (t + 1)) (lagV xm z (t + 1)) : ι ⊕ ι → ℝ) =
      compA1 f₁ f₂ *ᵥ (Sum.elim (z t) (lagV xm z t)) := by
  rw [← add_zero (compA1 f₁ f₂ *ᵥ _), comp_step]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, lagV_succ]
  refine ⟨?_, by simp⟩
  have h1 := h t
  simp only [Pi.zero_apply] at h1
  rw [h1]
  rfl

/-- Woodford (2003), App. A.3, p. 632, fn. 2 of App. C.1 (**genericity**): for the companion
pencil, "no nonzero bounded solution of `A₀ y_{t+1} = A₁ y_t` starts with predetermined block
`0`" is exactly "the homogeneous (A.10) with `x_{−1} = 0` has no nonzero bounded solution". -/
theorem genericPencil_comp_iff (f₁ f₂ f₃ : Matrix ι ι ℝ) :
    GenericPencil (compA0 f₃) (compA1 f₁ f₂) ↔ HomInjective f₁ f₂ f₃ := by
  constructor
  · intro hg x hxb hx
    have key : ∀ s, (∀ t < s, x t = 0) → x s = 0 := by
      intro s hs
      set z : ℕ → ι → ℝ := fun t => x (t + s) with hz
      have hlag : ∀ t, lagV (lagV 0 x s) z t = lagV 0 x (t + s) := by
        intro t
        cases t with
        | zero => simp
        | succ t => simp [hz, show t + 1 + s = t + s + 1 by omega]
      have hzs : SolvesLin f₁ f₂ f₃ 0 (lagV 0 x s) z := by
        intro t
        have := hx (t + s)
        rw [hlag t]
        simpa [hz, show t + 1 + s = t + s + 1 by omega] using this
      have hzb : BoundedSeq z := by
        obtain ⟨C, hC⟩ := hxb
        exact ⟨C, fun t i => hC (t + s) i⟩
      have hv := hg (Sum.elim (z 0) (lagV (lagV 0 x s) z 0))
        ⟨fun t => Sum.elim (z t) (lagV (lagV 0 x s) z t), rfl,
          (boundedSeq_elim hzb (boundedSeq_lagV _ hzb)),
          fun t => pencil_of_lin_zero hzs t⟩
        (fun j => by
          cases s with
          | zero => simp
          | succ s => simpa using congrFun (hs s (by omega)) j)
      have := congrFun hv
      funext i
      simpa [hz] using this (Sum.inl i)
    funext s
    induction s using Nat.strong_induction_on with
    | _ s ih => exact key s ih
  · rintro hinj v ⟨y, hy0, hyb, hy⟩ hv
    have hy' : ∀ t, compA0 f₃ *ᵥ y (t + 1) = compA1 f₁ f₂ *ᵥ y t + (0 : ℕ → ι ⊕ ι → ℝ) t :=
      fun t => by rw [Pi.zero_apply, add_zero]; exact hy t
    obtain ⟨hk, hs⟩ := lin_of_pencil hy'
    have h0 : y 0 ∘ Sum.inr = 0 := by
      funext j
      rw [Function.comp_apply, hy0]
      exact hv j
    have hforce : (fun t => (0 : ℕ → ι ⊕ ι → ℝ) t ∘ Sum.inl -
        f₁ *ᵥ lagV 0 (fun s => (0 : ℕ → ι ⊕ ι → ℝ) s ∘ Sum.inr) t) = 0 := by
      funext t
      simp only [Pi.zero_apply, Pi.zero_comp]
      rw [show (fun _ : ℕ => (0 : ι → ℝ)) = fun _ => 0 from rfl, lagV_zero_zero,
        Matrix.mulVec_zero, sub_zero]
    rw [h0, hforce] at hs
    have hz := hinj _ (boundedSeq_inl hyb) hs
    rw [← hy0]
    funext j
    cases j with
    | inl i => exact congrFun (congrFun hz 0) i
    | inr i => exact congrFun h0 i

/-! ### The root condition: the exact statement of (A.9) -/

/-- **(A.9) made exact** (Woodford (2003), App. A.3, eqs. (A.9)–(A.10), pp. 632–633): the
linearised system `f₁ x_{t−1} + f₂ x_t + f₃ x_{t+1} = w_t` has a unique bounded solution for every
bounded forcing and every initial condition **iff** (i) `det(f₃λ² + f₂λ + f₁)` is not
identically zero, (ii) it has no root on the unit circle, (iii) exactly `n` of its roots (with
multiplicity) lie in the open unit disc, and (iv) genericity: the homogeneous system with
`x_{−1} = 0` has no nonzero bounded solution. No invertibility of `f₃` is assumed. -/
theorem linDeterminate_iff (f₁ f₂ f₃ : Matrix ι ι ℝ) :
    LinDeterminate f₁ f₂ f₃ ↔ quadPoly f₁ f₂ f₃ ≠ 0 ∧
      (∀ μ ∈ ((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1) ∧
      Multiset.card (((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots.filter
        (fun μ => ‖μ‖ < 1)) = Fintype.card ι ∧ HomInjective f₁ f₂ f₃ := by
  rw [linDeterminate_iff_pencil, determinatePencil_iff_general, pencilPoly_comp,
    genericPencil_comp_iff]

/-- Woodford (2003), App. A.3, eq. (A.9), p. 632 (the book's count, as printed): exactly `n`
roots of `det(f₃λ² + f₂λ + f₁)` (with multiplicity) inside the unit circle and exactly `n`
outside. -/
def BookRootCount (f₁ f₂ f₃ : Matrix ι ι ℝ) : Prop :=
  Multiset.card (((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots.filter
      (fun μ => ‖μ‖ < 1)) = Fintype.card ι ∧
    Multiset.card (((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots.filter
      (fun μ => 1 < ‖μ‖)) = Fintype.card ι

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 632 (tool): every root lies inside, on or outside the unit
circle. -/
theorem card_split (s : Multiset ℂ) :
    Multiset.card s = Multiset.card (s.filter (fun μ => ‖μ‖ < 1)) +
      Multiset.card (s.filter (fun μ => ‖μ‖ = 1)) +
        Multiset.card (s.filter (fun μ => 1 < ‖μ‖)) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rcases lt_trichotomy ‖a‖ 1 with h | h | h
    · simp only [Multiset.filter_cons, h, h.ne, not_lt.mpr h.le, ↓reduceIte,
        Multiset.card_cons, Multiset.card_add, Multiset.card_zero, Multiset.card_singleton]
      omega
    · simp only [Multiset.filter_cons, h, lt_irrefl, ↓reduceIte, Multiset.card_cons,
        Multiset.card_add, Multiset.card_zero, Multiset.card_singleton]
      omega
    · simp only [Multiset.filter_cons, h, h.ne', not_lt.mpr h.le, ↓reduceIte,
        Multiset.card_cons, Multiset.card_add, Multiset.card_zero, Multiset.card_singleton]
      omega

/-- Woodford (2003), App. A.3, p. 632 (tool): `det A₀ = det f₃` for the companion pencil. -/
theorem det_compA0 (f₃ : Matrix ι ι ℝ) : (compA0 f₃).det = f₃.det := by
  rw [compA0, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

/-- Woodford (2003), App. A.3, eq. (A.9), p. 632: with `det f₃ ≠ 0`,
`det(f₃λ² + f₂λ + f₁) = det f₃ · det(λ − A)` for the companion matrix `A = A₀⁻¹A₁`. -/
theorem quadPoly_eq_of_det {f₁ f₂ f₃ : Matrix ι ι ℝ} (h : f₃.det ≠ 0) :
    quadPoly f₁ f₂ f₃ = C f₃.det * ((compA0 f₃)⁻¹ * compA1 f₁ f₂).charpoly := by
  rw [← pencilPoly_comp, pencilPoly_eq (isUnit_iff_ne_zero.mpr (by rwa [det_compA0])),
    det_compA0]

/-- Woodford (2003), App. A.3, eq. (A.9), p. 632: with `det f₃ ≠ 0` the characteristic
polynomial is nonzero of degree exactly `2n`. -/
theorem natDegree_quadPoly {f₁ f₂ f₃ : Matrix ι ι ℝ} (h : f₃.det ≠ 0) :
    quadPoly f₁ f₂ f₃ ≠ 0 ∧ (quadPoly f₁ f₂ f₃).natDegree = 2 * Fintype.card ι := by
  rw [quadPoly_eq_of_det h]
  refine ⟨mul_ne_zero (Polynomial.C_ne_zero.mpr h) (Matrix.charpoly_monic _).ne_zero, ?_⟩
  rw [natDegree_C_mul h, Matrix.charpoly_natDegree_eq_dim, Fintype.card_sum, two_mul]

/-- **(A.9) as printed, for invertible `f₃`** (Woodford (2003), App. A.3, pp. 632–633): if
`det f₃ ≠ 0`, the linearised system (A.10) is determinate **iff** exactly `n` roots of
`det(f₃λ² + f₂λ + f₁)` lie inside and exactly `n` outside the unit circle **and** the genericity
condition holds. (Roots on the circle are excluded by the count, since there are `2n` roots.) -/
theorem linDeterminate_iff_of_det {f₁ f₂ f₃ : Matrix ι ι ℝ} (h : f₃.det ≠ 0) :
    LinDeterminate f₁ f₂ f₃ ↔ BookRootCount f₁ f₂ f₃ ∧ HomInjective f₁ f₂ f₃ := by
  obtain ⟨hq, hdeg⟩ := natDegree_quadPoly (f₁ := f₁) (f₂ := f₂) h
  set rts := ((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots with hrts
  have hcard : Multiset.card rts = 2 * Fintype.card ι := by
    rw [hrts, IsAlgClosed.card_roots_eq_natDegree, natDegree_map, hdeg]
  have hpart := card_split rts
  have hon : (∀ μ ∈ rts, ‖μ‖ ≠ 1) ↔ Multiset.card (rts.filter (fun μ => ‖μ‖ = 1)) = 0 := by
    rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  rw [linDeterminate_iff, BookRootCount, ← hrts, hon]
  constructor
  · rintro ⟨-, h1, h2, hg⟩
    exact ⟨⟨h2, by omega⟩, hg⟩
  · rintro ⟨⟨h1, h2⟩, hg⟩
    exact ⟨hq, by omega, h1, hg⟩

/-- Woodford (2003), App. A.3, eq. (A.9), p. 632 (**the infinite roots count as outside**): when
the linearised system is determinate, the roots of `det(f₃λ² + f₂λ + f₁)` outside the unit
circle together with the `2n − deg` "infinite roots" (present exactly when `f₃` is singular)
number exactly `n`. -/
theorem outside_add_infinite {f₁ f₂ f₃ : Matrix ι ι ℝ} (hL : LinDeterminate f₁ f₂ f₃) :
    Multiset.card (((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots.filter
        (fun μ => 1 < ‖μ‖)) + (2 * Fintype.card ι - (quadPoly f₁ f₂ f₃).natDegree) =
      Fintype.card ι := by
  obtain ⟨hreg, hnu, hc, -⟩ := (linDeterminate_iff f₁ f₂ f₃).mp hL
  rw [← pencilPoly_comp] at hreg hnu hc ⊢
  have := unstable_add_infinite hreg hnu hc
  rwa [Fintype.card_sum, ← two_mul] at this

/-! ### Exactly which cases break the printed "(generically) iff" -/

/-- Woodford (2003), App. A.3, p. 632 (counterexample data): `f₁ = diag(0, −4)`, `f₂ = 0`,
`f₃ = 1`, i.e. `x¹_{t+1} = 0` and `x²_{t+1} = 4 x²_{t−1}`. -/
def cexF1 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, -4]

/-- Woodford (2003), App. A.3, p. 632 (counterexample): the characteristic polynomial of the
counterexample is `λ²(λ² − 4)`. -/
theorem quadPoly_cex : quadPoly cexF1 0 1 = X ^ 2 * (X ^ 2 - C 4) := by
  refine Polynomial.funext fun r => ?_
  rw [eval_quadPoly, Matrix.det_fin_two]
  simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_C, cexF1, smul_zero, add_zero,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    smul_eq_mul]
  norm_num
  left
  ring

/-- Woodford (2003), App. A.3, p. 632 (counterexample): its complex roots are `0, 0, 2, −2`. -/
theorem roots_cex : ((quadPoly cexF1 0 1).map Complex.ofRealHom).roots =
    2 • ({0} : Multiset ℂ) + {2} + {-2} := by
  have e : (quadPoly cexF1 0 1).map Complex.ofRealHom =
      X ^ 2 * (X - C (2 : ℂ)) * (X - C (-2 : ℂ)) := by
    rw [quadPoly_cex, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_pow, map_X, Polynomial.map_C]
    have h4 : Complex.ofRealHom 4 = (2 : ℂ) * 2 := by norm_num
    rw [h4, C_mul, mul_assoc]
    congr 1
    rw [C_neg]
    ring
  have hm : (X ^ 2 * (X - C (2 : ℂ))).Monic := (monic_X_pow 2).mul (monic_X_sub_C 2)
  rw [e, roots_mul (hm.mul (monic_X_sub_C _)).ne_zero, roots_mul hm.ne_zero, roots_X_pow,
    roots_X_sub_C, roots_X_sub_C]

/-- **The printed root count is not sufficient** (Woodford (2003), App. A.3, eq. (A.9), p. 632;
the role of "generically"): with `f₃ = 1` invertible, `f₂ = 0`, `f₁ = diag(0, −4)`, exactly two
roots (`0, 0`) lie inside and two (`±2`) outside the unit circle, yet the linearised system is
not determinate: `x_0 = (1, 0)`, `x_t = 0` otherwise, is a second bounded solution of the
homogeneous system with `x_{−1} = 0` (genericity fails). -/
theorem book_count_not_sufficient :
    (1 : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 ∧ BookRootCount cexF1 0 1 ∧
      ¬ LinDeterminate cexF1 0 1 := by
  refine ⟨by simp, ?_, ?_⟩
  · rw [BookRootCount, roots_cex]
    norm_num [Multiset.filter_add, Multiset.filter_nsmul, Multiset.filter_singleton]
  · intro hL
    set x : ℕ → Fin 2 → ℝ := fun t => if t = 0 then Pi.single 0 1 else 0 with hx
    have hsol : SolvesLin cexF1 0 1 0 0 x := by
      intro t
      cases t with
      | zero => funext i; fin_cases i <;> simp [hx, cexF1]
      | succ t =>
        cases t with
        | zero => funext i; fin_cases i <;> simp [hx, cexF1]
        | succ t => funext i; fin_cases i <;> simp [hx, cexF1]
    have hxb : BoundedSeq x := ⟨1, fun t i => by
      by_cases ht : t = 0
      · subst ht; fin_cases i <;> simp [hx]
      · simp [hx, ht]⟩
    have h0 : SolvesLin cexF1 0 1 0 0 (0 : ℕ → Fin 2 → ℝ) := fun t => by
      cases t <;> simp
    have := (hL 0 ⟨0, fun _ _ => by simp⟩ 0).unique ⟨hxb, hsol⟩ ⟨⟨0, fun _ _ => by simp⟩, h0⟩
    have h1 := congrFun (congrFun this 0) 0
    simp [hx] at h1

/-- **The printed root count is not necessary when `f₃` is singular** (Woodford (2003), App. A.3,
eq. (A.9), p. 632): for `n = 1`, `f₁ = f₃ = 0`, `f₂ = 1` (the static condition `x_t = w_t`) the
linearised system is determinate, but `det(f₃λ² + f₂λ + f₁) = λ` has no root outside the unit
circle (its second root is infinite; compare `outside_add_infinite`). -/
theorem book_count_not_necessary :
    LinDeterminate (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 0 ∧
      ¬ BookRootCount (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 0 := by
  constructor
  · intro w hw xm
    refine ⟨w, ⟨hw, fun t => by simp⟩, fun x ⟨_, hx⟩ => funext fun t => ?_⟩
    simpa using hx t
  · rintro ⟨-, h2⟩
    have e : quadPoly (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 0 = X := by
      refine Polynomial.funext fun r => ?_
      rw [eval_quadPoly]
      simp
    rw [e, Polynomial.map_X, roots_X, Multiset.filter_singleton] at h2
    norm_num at h2

/-! ### The derivative (A.8) as a bounded operator on `ℓ∞(ℕ, ℝⁿ)` -/

/-- Woodford (2003), App. A.3, p. 632: the Banach space `ℓ∞(ℕ, ℝⁿ)` of bounded sequences of
vectors `{p̂_t}` (sup norm over `t` of the sup norm on `ℝⁿ`). -/
abbrev SeqV (ι : Type*) [Fintype ι] : Type _ := LocalIFT.Seq (ι → ℝ)

/-- Woodford (2003), App. A.3, p. 632 (tool): two bounded sequences with the same coordinates
are equal. -/
theorem seq_ext {V : Type*} [NormedAddCommGroup V] {x y : LocalIFT.Seq V} (h : ∀ t, x t = y t) :
    x = y :=
  lp.ext (funext h)

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 632 (tool): the elements of `ℓ∞(ℕ, ℝⁿ)` are bounded
sequences. -/
theorem boundedSeq_coe (x : SeqV ι) : BoundedSeq (fun t => x t) :=
  ⟨‖x‖, fun t i => by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (x t) i).trans (LocalIFT.norm_seq_apply_le x t)⟩

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 632 (tool): a bounded sequence of vectors has a uniform bound
on its norms. -/
theorem exists_norm_bound {x : ℕ → ι → ℝ} (hx : BoundedSeq x) : ∃ C, ∀ t, ‖x t‖ ≤ C := by
  obtain ⟨C, hC⟩ := hx
  exact ⟨max C 0, fun t => (pi_norm_le_iff_of_nonneg (le_max_right _ _)).mpr fun i => by
    rw [Real.norm_eq_abs]
    exact (hC t i).trans (le_max_left _ _)⟩

/-- Woodford (2003), App. A.3, p. 632 (tool): a bounded sequence of vectors as an element of
`ℓ∞(ℕ, ℝⁿ)`. -/
noncomputable def toSeqV (x : ℕ → ι → ℝ) (hx : BoundedSeq x) : SeqV ι :=
  LocalIFT.mkS x (exists_norm_bound hx)

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 632 (tool): coordinates of `toSeqV`. -/
@[simp] theorem toSeqV_apply (x : ℕ → ι → ℝ) (hx : BoundedSeq x) (t : ℕ) : toSeqV x hx t = x t :=
  rfl

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: a coefficient matrix `f_j` as a continuous
linear map of `ℝⁿ`. -/
noncomputable def mclm (M : Matrix ι ι ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' M)

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632 (tool): `mclm M v = M v`. -/
@[simp] theorem mclm_apply (M : Matrix ι ι ℝ) (v : ι → ℝ) : mclm M v = M *ᵥ v := by
  simp [mclm, Matrix.toLin'_apply]

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: a continuous linear map `g` applied date by
date, `(x_t)_t ↦ (g x_t)_t`, a bounded operator `ℓ∞(V) → ℓ∞(W)` of norm at most `‖g‖`. -/
noncomputable def pw {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] (g : V →L[ℝ] W) : LocalIFT.Seq V →L[ℝ] LocalIFT.Seq W :=
  LinearMap.mkContinuous
    { toFun := fun x => LocalIFT.mkS (fun t => g (x t)) ⟨‖g‖ * ‖x‖, fun t =>
        (g.le_opNorm _).trans (mul_le_mul_of_nonneg_left (LocalIFT.norm_seq_apply_le x t)
          (norm_nonneg _))⟩
      map_add' := fun x y => by ext t; simp
      map_smul' := fun c x => by ext t; simp }
    ‖g‖ (fun x => LocalIFT.norm_seq_le (by positivity) fun t =>
      (g.le_opNorm _).trans (mul_le_mul_of_nonneg_left (LocalIFT.norm_seq_apply_le x t)
        (norm_nonneg _)))

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632 (tool): coordinates of `pw`. -/
@[simp] theorem pw_apply {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (g : V →L[ℝ] W) (x : LocalIFT.Seq V) (t : ℕ) :
    pw g x t = g (x t) := rfl

/-- Woodford (2003), App. A.3, p. 632 and fn. 4 (tool): the lagged sequence `x_{t−1}` with
`x_{−1} = 0` is bounded by `‖x‖`. -/
theorem norm_lagV_le {V : Type*} [NormedAddCommGroup V] (x : LocalIFT.Seq V) (t : ℕ) :
    ‖lagV 0 (fun s => x s) t‖ ≤ ‖x‖ := by
  cases t with
  | zero => simp
  | succ t => exact LocalIFT.norm_seq_apply_le x t

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632 and fn. 4: the lag operator
`(x_t)_t ↦ (x_{t−1})_t` with the `t = 0` term suppressed (`x_{−1} = 0`). -/
noncomputable def lagOp (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    LocalIFT.Seq V →L[ℝ] LocalIFT.Seq V :=
  LinearMap.mkContinuous
    { toFun := fun x => LocalIFT.mkS (lagV 0 (fun s => x s)) ⟨‖x‖, norm_lagV_le x⟩
      map_add' := fun x y => by
        ext t
        cases t <;> simp
      map_smul' := fun c x => by
        ext t
        cases t <;> simp }
    1 (fun x => by
      rw [one_mul]
      exact LocalIFT.norm_seq_le (norm_nonneg _) (norm_lagV_le x))

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632 (tool): coordinates of the lag operator. -/
@[simp] theorem lagOp_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x : LocalIFT.Seq V) (t : ℕ) : lagOp V x t = lagV 0 (fun s => x s) t := rfl

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: the lead operator `(x_t)_t ↦ (x_{t+1})_t`. -/
noncomputable def leadOp (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    LocalIFT.Seq V →L[ℝ] LocalIFT.Seq V :=
  LinearMap.mkContinuous
    { toFun := fun x => LocalIFT.mkS (fun t => x (t + 1))
        ⟨‖x‖, fun t => LocalIFT.norm_seq_apply_le x (t + 1)⟩
      map_add' := fun x y => by ext t; simp
      map_smul' := fun c x => by ext t; simp }
    1 (fun x => by
      rw [one_mul]
      exact LocalIFT.norm_seq_le (norm_nonneg _) fun t => LocalIFT.norm_seq_apply_le x (t + 1))

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632 (tool): coordinates of the lead operator. -/
@[simp] theorem leadOp_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x : LocalIFT.Seq V) (t : ℕ) : leadOp V x t = x (t + 1) := rfl

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: **the derivative operator**
`p̂ ↦ f̂`, `f̂_t = f₁ p̂_{t−1} + f₂ p̂_t + f₃ p̂_{t+1}` (with `p̂_{−1} = 0`, fn. 4), a bounded
linear operator on `ℓ∞(ℕ, ℝⁿ)`. -/
noncomputable def sysOp (f₁ f₂ f₃ : Matrix ι ι ℝ) : SeqV ι →L[ℝ] SeqV ι :=
  (pw (mclm f₁)).comp (lagOp (ι → ℝ)) + pw (mclm f₂) + (pw (mclm f₃)).comp (leadOp (ι → ℝ))

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: coordinates of the derivative operator. -/
theorem sysOp_apply (f₁ f₂ f₃ : Matrix ι ι ℝ) (x : SeqV ι) (t : ℕ) :
    sysOp f₁ f₂ f₃ x t = f₁ *ᵥ lagV 0 (fun s => x s) t + f₂ *ᵥ x t + f₃ *ᵥ x (t + 1) := by
  simp [sysOp]

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 633 (tool): the lag with initial condition `x_{−1}` splits into
the lag with `x_{−1} = 0` and the initial-condition impulse. -/
theorem lagV_split (xm : ι → ℝ) (x : ℕ → ι → ℝ) (t : ℕ) :
    lagV xm x t = lagV 0 x t + lagV xm 0 t := by
  cases t <;> simp

/-- Woodford (2003), App. A.3, pp. 632–633: a bounded solution with `x_{−1} = 0` is exactly a
preimage under the derivative operator. -/
theorem sysOp_eq_iff (f₁ f₂ f₃ : Matrix ι ι ℝ) (x y : SeqV ι) :
    sysOp f₁ f₂ f₃ x = y ↔ SolvesLin f₁ f₂ f₃ (fun t => y t) 0 (fun t => x t) := by
  constructor
  · intro h t
    subst h
    exact (sysOp_apply f₁ f₂ f₃ x t).symm
  · intro h
    refine seq_ext fun t => ?_
    rw [sysOp_apply]
    exact h t

/-- **Invertibility of the derivative (A.8) on `ℓ∞` is determinacy of (A.10)** (Woodford
(2003), App. A.3, pp. 632–633): the bounded operator `f₁ L + f₂ + f₃ S` on `ℓ∞(ℕ, ℝⁿ)` is
invertible iff the linearised system has a unique bounded solution for every bounded forcing and
every initial condition `p̂_{−1}`. -/
theorem isUnit_sysOp_iff (f₁ f₂ f₃ : Matrix ι ι ℝ) :
    IsUnit (sysOp f₁ f₂ f₃) ↔ LinDeterminate f₁ f₂ f₃ := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  constructor
  · rintro ⟨hinj, hsurj⟩ w hw xm
    have hw' : BoundedSeq (fun t => w t - f₁ *ᵥ lagV xm 0 t) :=
      boundedSeq_sub hw (boundedSeq_mulVec f₁ (boundedSeq_lagV xm ⟨0, fun _ _ => by simp⟩))
    obtain ⟨x, hx⟩ := hsurj (toSeqV _ hw')
    have hsol : ∀ (z : ℕ → ι → ℝ), SolvesLin f₁ f₂ f₃ w xm z ↔
        SolvesLin f₁ f₂ f₃ (fun t => w t - f₁ *ᵥ lagV xm 0 t) 0 z := by
      intro z
      refine forall_congr' fun t => ?_
      rw [lagV_split xm z t, Matrix.mulVec_add, eq_sub_iff_add_eq]
      constructor <;> intro h <;> rw [← h] <;> abel
    refine ⟨fun t => x t, ⟨boundedSeq_coe x, (hsol _).mpr ((sysOp_eq_iff _ _ _ _ _).mp hx)⟩,
      fun z ⟨hzb, hz⟩ => ?_⟩
    have h1 : sysOp f₁ f₂ f₃ (toSeqV z hzb) = toSeqV _ hw' :=
      (sysOp_eq_iff _ _ _ _ _).mpr ((hsol _).mp hz)
    have h2 := hinj (h1.trans hx.symm)
    funext t
    exact congrArg (fun q : SeqV ι => q t) h2
  · intro hL
    constructor
    · intro x y hxy
      obtain ⟨x0, -, hu⟩ := hL (fun t => sysOp f₁ f₂ f₃ x t) (boundedSeq_coe _) 0
      have hx := (sysOp_eq_iff f₁ f₂ f₃ x _).mp rfl
      have hy := (sysOp_eq_iff f₁ f₂ f₃ y _).mp hxy.symm
      have e := (hu _ ⟨boundedSeq_coe x, hx⟩).trans (hu _ ⟨boundedSeq_coe y, hy⟩).symm
      exact seq_ext fun t => congrFun e t
    · intro y
      obtain ⟨x, ⟨hxb, hx⟩, -⟩ := hL (fun t => y t) (boundedSeq_coe y) 0
      exact ⟨toSeqV x hxb, (sysOp_eq_iff _ _ _ _ _).mpr hx⟩

/-- Woodford (2003), App. A.3, p. 632 (genericity as injectivity): the genericity condition is
exactly injectivity of the derivative operator. -/
theorem homInjective_iff_injective (f₁ f₂ f₃ : Matrix ι ι ℝ) :
    HomInjective f₁ f₂ f₃ ↔ Function.Injective (sysOp f₁ f₂ f₃) := by
  constructor
  · intro h x y hxy
    have hz : sysOp f₁ f₂ f₃ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have := h _ (boundedSeq_coe _) ((sysOp_eq_iff _ _ _ _ _).mp hz)
    have e : x - y = 0 := seq_ext fun t => congrFun this t
    exact sub_eq_zero.mp e
  · intro h x hxb hx
    have e : toSeqV x hxb = 0 :=
      h ((sysOp_eq_iff _ _ _ _ _).mpr hx |>.trans (map_zero _).symm)
    funext t
    exact congrArg (fun q : SeqV ι => q t) e

/-- **The exact form of the book's (A.9) claim on `ℓ∞`** (Woodford (2003), App. A.3, eq. (A.9),
p. 632): the derivative operator (A.8) is invertible on `ℓ∞(ℕ, ℝⁿ)` iff `det(f₃λ² + f₂λ + f₁)`
is not identically zero, has no root on the unit circle and exactly `n` roots in the open disc,
and the operator is injective (genericity). -/
theorem isUnit_sysOp_iff_roots (f₁ f₂ f₃ : Matrix ι ι ℝ) :
    IsUnit (sysOp f₁ f₂ f₃) ↔ quadPoly f₁ f₂ f₃ ≠ 0 ∧
      (∀ μ ∈ ((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1) ∧
      Multiset.card (((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots.filter
        (fun μ => ‖μ‖ < 1)) = Fintype.card ι ∧ Function.Injective (sysOp f₁ f₂ f₃) := by
  rw [isUnit_sysOp_iff, linDeterminate_iff, homInjective_iff_injective]

/-! ### Regularity: surjectivity forces a regular pencil, and then kernels are finite-dimensional -/

/-- Woodford (2003), App. A.3, p. 632 (tool, regular pencils): if `det(λA₀ − A₁) ≢ 0`, a bounded
solution of `A₀ y_{t+1} = A₁ y_t` with `y_0 = 0` vanishes identically. (The nilpotent block is
forced to zero, and the finite block is `y_{t+1} = (cP − Ni) y_t`.) -/
theorem pencil_hom_eq_zero {κ : Type*} [Fintype κ] [DecidableEq κ] {A0 A1 : Matrix κ κ ℝ}
    (hreg : pencilPoly A0 A1 ≠ 0) {Y : ℕ → κ → ℝ} (hYb : ∃ C, ∀ t i, |Y t i| ≤ C)
    (hY : ∀ t, A0 *ᵥ Y (t + 1) = A1 *ᵥ Y t) (h0 : Y 0 = 0) (t : ℕ) : Y t = 0 := by
  obtain ⟨c, hB⟩ := exists_regular_point hreg
  obtain ⟨m, P, Q, Ni, hFit⟩ := exists_fitting ((c • A0 - A1)⁻¹ * A0)
  have hF : Fitting ((c • A0 - A1)⁻¹ * A0) m P Q Ni := hFit
  set y : ℕ → κ → Unit → ℝ := useq Y with hydef
  have hy : SolvesPencil perfectForesight A0 A1 0 y :=
    (solvesPencil_pf_iff _ _ _ _).mpr fun t => (hY t).trans (add_zero _).symm
  have hyb : BoundedV y := (boundedV_iff y).mpr hYb
  have hE : ∀ (s : ℕ) (a : κ → Unit → ℝ), (fun i => perfectForesight.E s (a i)) = a :=
    fun _ _ => rfl
  -- the nilpotent block vanishes
  have hQ : (fun s => mv Q (y s)) = fun _ => 0 := by
    refine (pencilV_existsUnique perfectForesight hF c (g := fun _ => 0)
      (fun _ => mv_zero Q) ⟨0, fun _ _ _ => by simp⟩ (adaptedV_pf _)).2 _ _
      (fun s => mvQ_idem hF _) (fun s => ?_) (adaptedV_pf _) (boundedV_mv Q hyb)
      (fun _ => mv_zero Q) (fun s => ?_) (adaptedV_pf _) ⟨0, fun _ _ _ => by simp⟩
    · have := pencil_Vpart perfectForesight hB hF hy s
      rwa [Pi.zero_apply, mv_zero, mv_zero] at this
    · rw [hE, mv_zero, mv_zero, add_zero]
  -- the finite block evolves by `cP − Ni`
  have hstep : ∀ s, y (s + 1) = mv (c • P - Ni) (y s) := by
    intro s
    have h1 := ((split_pencil hF c _ _ _).mp ((pencil_reduce hB _ _ _).mp (hy s))).1
    rw [hE, Pi.zero_apply, mv_zero, mv_zero, add_zero] at h1
    have hq := congrFun hQ (s + 1)
    calc y (s + 1) = mv (1 : Matrix κ κ ℝ) (y (s + 1)) := (mv_one _).symm
      _ = mv P (y (s + 1)) + mv Q (y (s + 1)) := by rw [← hF.1, add_mv]
      _ = mv (c • P - Ni) (y s) := by rw [h1, hq, add_zero]
  have hy0 : y 0 = 0 := by
    funext i u
    simp [hydef, useq, h0]
  have hyt : y t = 0 := by
    induction t with
    | zero => exact hy0
    | succ t ih => rw [hstep, ih, mv_zero]
  funext i
  exact congrFun (congrFun hyt i) ()

/-- Woodford (2003), App. A.3, p. 632: when `det(f₃λ² + f₂λ + f₁) ≢ 0`, a bounded solution of the
homogeneous linearised system with `x_{−1} = 0` is determined by `x_0`: if `x_0 = 0` it vanishes.
(So the kernel of the derivative operator has dimension at most `n`.) -/
theorem eq_zero_of_regular {f₁ f₂ f₃ : Matrix ι ι ℝ} (hreg : quadPoly f₁ f₂ f₃ ≠ 0)
    {x : ℕ → ι → ℝ} (hxb : BoundedSeq x) (hx : SolvesLin f₁ f₂ f₃ 0 0 x) (h0 : x 0 = 0) :
    x = 0 := by
  rw [← pencilPoly_comp] at hreg
  have key := pencil_hom_eq_zero hreg (boundedSeq_elim hxb (boundedSeq_lagV 0 hxb))
    (fun t => pencil_of_lin_zero hx t) (by funext j; cases j <;> simp [h0])
  funext t
  funext i
  have := congrFun (key t) (Sum.inl i)
  simpa using this

/-- Woodford (2003), App. A.3, p. 632 and App. C.1 (King–Watson/Klein): **a surjective
derivative operator forces a regular pencil** — if `det(f₃λ² + f₂λ + f₁) ≡ 0`, some bounded
forcing (with `x_{−1} = 0`) admits no solution of (A.10) at all, bounded or not. -/
theorem quadPoly_ne_zero_of_surjective {f₁ f₂ f₃ : Matrix ι ι ℝ}
    (hs : Function.Surjective (sysOp f₁ f₂ f₃)) : quadPoly f₁ f₂ f₃ ≠ 0 := by
  intro h0
  rw [← pencilPoly_comp] at h0
  obtain ⟨w, hwb, -, hno⟩ := nonexist_of_not_regular perfectForesight h0
  set W := dseq w with hW
  have hWb : BoundedSeq W := (boundedV_iff w).mp hwb
  have hfb : BoundedSeq (fun t => W t ∘ Sum.inl - f₁ *ᵥ lagV 0 (fun s => W s ∘ Sum.inr) t) :=
    boundedSeq_sub (boundedSeq_inl hWb) (boundedSeq_mulVec f₁
      (boundedSeq_lagV 0 (boundedSeq_inr hWb)))
  obtain ⟨z, hz⟩ := hs (toSeqV _ hfb)
  have hzs := (sysOp_eq_iff _ _ _ _ _).mp hz
  apply hno (useq fun t => Sum.elim (z t)
    (lagV 0 (fun s => z s) t + lagV 0 (fun s => W s ∘ Sum.inr) t))
  rw [solvesPencil_pf_iff]
  intro t
  exact pencil_of_lin hzs t

/-! ### Which of existence and uniqueness fails when the root condition fails -/

/-- Woodford (2003), App. A.3, p. 632: the derivative operator fails to be invertible iff it
fails to be injective (non-uniqueness of bounded solutions of (A.10)) or fails to be surjective
(non-existence for some bounded forcing). -/
theorem not_isUnit_iff (f₁ f₂ f₃ : Matrix ι ι ℝ) :
    ¬ IsUnit (sysOp f₁ f₂ f₃) ↔
      ¬ Function.Injective (sysOp f₁ f₂ f₃) ∨ ¬ Function.Surjective (sysOp f₁ f₂ f₃) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective, Function.Bijective, not_and_or]

/-- Woodford (2003), App. A.3, p. 632 (**too many stable roots: non-uniqueness**): if more than
`n` roots of `det(f₃λ² + f₂λ + f₁)` lie in the open unit disc, the homogeneous system with
`x_{−1} = 0` has a nonzero bounded solution (`f₃` may be singular). -/
theorem not_injective_of_count_gt {f₁ f₂ f₃ : Matrix ι ι ℝ}
    (h : Fintype.card ι < Multiset.card (((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots.filter
      (fun μ => ‖μ‖ < 1))) : ¬ Function.Injective (sysOp f₁ f₂ f₃) := by
  have hreg : quadPoly f₁ f₂ f₃ ≠ 0 := by
    intro h0
    rw [h0, Polynomial.map_zero, roots_zero] at h
    simp at h
  rw [← homInjective_iff_injective, ← genericPencil_comp_iff]
  rw [← pencilPoly_comp] at hreg h
  obtain ⟨c, hB⟩ := exists_regular_point hreg
  obtain ⟨m, P, Q, Ni, hFit⟩ := exists_fitting ((c • compA0 f₃ - compA1 f₁ f₂)⁻¹ * compA0 f₃)
  have hF : Fitting ((c • compA0 f₃ - compA1 f₁ f₂)⁻¹ * compA0 f₃) m P Q Ni := hFit
  have hgen : GenericX (ahat c P Q Ni) ↔ GenericPencil (compA0 f₃) (compA1 f₁ f₂) := by
    unfold GenericX GenericPencil
    exact forall_congr' fun v => by rw [mem_boundedOrbits_ahat hB hF]
  rw [← hgen]
  apply not_genericX_of_lt
  rw [← stableCount_ahat hB hF] at h
  exact h.trans_le (stableCount_le_finrank _)

/-- Woodford (2003), App. A.3, p. 632 (**too few stable roots: non-existence**): with no root on
the unit circle and fewer than `n` roots of `det(f₃λ² + f₂λ + f₁)` in the open disc, some
initial condition `x_{−1}` admits no bounded solution of the homogeneous (A.10); so the
derivative operator is not surjective (`f₃` may be singular). -/
theorem not_surjective_of_count_lt {f₁ f₂ f₃ : Matrix ι ι ℝ}
    (hnu : ∀ μ ∈ ((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1)
    (h : Multiset.card (((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots.filter
      (fun μ => ‖μ‖ < 1)) < Fintype.card ι) : ¬ Function.Surjective (sysOp f₁ f₂ f₃) := by
  intro hs
  have hreg := quadPoly_ne_zero_of_surjective hs
  rw [← pencilPoly_comp] at hreg hnu h
  obtain ⟨c, hB⟩ := exists_regular_point hreg
  obtain ⟨m, P, Q, Ni, hFit⟩ := exists_fitting ((c • compA0 f₃ - compA1 f₁ f₂)⁻¹ * compA0 f₃)
  have hF : Fitting ((c • compA0 f₃ - compA1 f₁ f₂)⁻¹ * compA0 f₃) m P Q Ni := hFit
  have hnuA : NoUnit (ahat c P Q Ni) := (noUnit_ahat_iff hB hF).mpr hnu
  have hfin : Module.finrank ℝ (boundedOrbits (ahat c P Q Ni)) < Fintype.card ι := by
    rw [finrank_eq_stableCount hnuA, stableCount_ahat hB hF]
    exact h
  obtain ⟨x0, hx0⟩ := exists_unreached_of_lt hfin
  have hwb : BoundedSeq (fun t => -(f₁ *ᵥ lagV x0 0 t)) := by
    obtain ⟨C, hC⟩ := boundedSeq_mulVec f₁ (boundedSeq_lagV x0 (x := 0) ⟨0, fun _ _ => by simp⟩)
    exact ⟨C, fun t i => by simpa using hC t i⟩
  obtain ⟨z, hz⟩ := hs (toSeqV _ hwb)
  have hz0 : SolvesLin f₁ f₂ f₃ 0 x0 (fun t => z t) := by
    intro t
    have := (sysOp_eq_iff _ _ _ _ _).mp hz t
    rw [lagV_split x0 _ t, Matrix.mulVec_add, Pi.zero_apply]
    simp only [toSeqV_apply] at this
    beta_reduce
    rw [show ∀ a b c d : ι → ℝ, a + b + c + d = (a + c + d) + b from fun a b c d => by abel,
      this, neg_add_cancel]
  have hzb := boundedSeq_coe z
  have hpb : PencilBounded (compA0 f₃) (compA1 f₁ f₂)
      (Sum.elim (z 0) (lagV x0 (fun t => z t) 0)) :=
    ⟨fun t => Sum.elim (z t) (lagV x0 (fun s => z s) t), rfl,
      boundedSeq_elim hzb (boundedSeq_lagV x0 hzb), fun t => pencil_of_lin_zero hz0 t⟩
  exact hx0 _ ((mem_boundedOrbits_ahat hB hF _).mpr hpb) (by funext j; simp)

/-- Woodford (2003), App. A.3, p. 632 (**a root on the unit circle: non-existence**, invertible
`f₃`): if `det f₃ ≠ 0` and `det(f₃μ² + f₂μ + f₁) = 0` with `|μ| = 1`, some bounded forcing
(resonating with `μ`) admits no bounded solution of (A.10). -/
theorem not_surjective_of_unit {f₁ f₂ f₃ : Matrix ι ι ℝ} (hdet : f₃.det ≠ 0) {μ : ℂ}
    (hμ : μ ∈ ((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots) (h1 : ‖μ‖ = 1) :
    ¬ Function.Surjective (sysOp f₁ f₂ f₃) := by
  intro hs
  have hA0 : IsUnit (compA0 f₃).det := isUnit_iff_ne_zero.mpr (by rwa [det_compA0])
  rw [← pencilPoly_comp, ← eigs_pencil hA0] at hμ
  obtain ⟨w, hwb, -, hno⟩ := nonexist_of_unit perfectForesight hμ h1
  set W : ℕ → ι ⊕ ι → ℝ := fun t => compA0 f₃ *ᵥ dseq w t with hW
  have hWb : BoundedSeq W := boundedSeq_mulVec _ ((boundedV_iff w).mp hwb)
  have hfb : BoundedSeq (fun t => W t ∘ Sum.inl - f₁ *ᵥ lagV 0 (fun s => W s ∘ Sum.inr) t) :=
    boundedSeq_sub (boundedSeq_inl hWb) (boundedSeq_mulVec f₁
      (boundedSeq_lagV 0 (boundedSeq_inr hWb)))
  obtain ⟨z, hz⟩ := hs (toSeqV _ hfb)
  have hzs := (sysOp_eq_iff _ _ _ _ _).mp hz
  set Y : ℕ → ι ⊕ ι → ℝ := fun t => Sum.elim (z t)
    (lagV 0 (fun s => z s) t + lagV 0 (fun s => W s ∘ Sum.inr) t) with hY
  have hYb : BoundedSeq Y := boundedSeq_elim (boundedSeq_coe z)
    (boundedSeq_add (boundedSeq_lagV 0 (boundedSeq_coe z)) (boundedSeq_lagV 0 (boundedSeq_inr hWb)))
  have hp : SolvesPencil perfectForesight (compA0 f₃) (compA1 f₁ f₂) (useq W) (useq Y) :=
    (solvesPencil_pf_iff _ _ _ _).mpr fun t => pencil_of_lin hzs t
  rw [solvesPencil_iff perfectForesight hA0] at hp
  refine hno (useq Y) ?_ ((boundedV_iff _).mpr hYb)
  have hw : (fun t => mv (compA0 f₃)⁻¹ (useq W t)) = w := by
    funext t i u
    cases u
    rw [mv_apply]
    have e : (fun j => useq W t j ()) = compA0 f₃ *ᵥ dseq w t := rfl
    rw [e, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA0, Matrix.one_mulVec]
    rfl
  rwa [hw] at hp

/-- **Which half fails** (Woodford (2003), App. A.3, pp. 632–633, invertible `f₃`): if the
linearised system is not determinate, then exactly one of the following explains it: a root on
the unit circle (existence fails for some bounded forcing), more than `n` roots inside (uniqueness
fails), no root on the circle but fewer than `n` inside (existence fails for some initial
condition), or the count is right but genericity fails (uniqueness fails). -/
theorem failure_cases {f₁ f₂ f₃ : Matrix ι ι ℝ} (hdet : f₃.det ≠ 0)
    (hfail : ¬ LinDeterminate f₁ f₂ f₃) :
    (∃ μ ∈ ((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots, ‖μ‖ = 1) ∧
        ¬ Function.Surjective (sysOp f₁ f₂ f₃) ∨
      Fintype.card ι < Multiset.card (((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots.filter
          (fun μ => ‖μ‖ < 1)) ∧ ¬ Function.Injective (sysOp f₁ f₂ f₃) ∨
      (∀ μ ∈ ((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1) ∧
        Multiset.card (((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots.filter
          (fun μ => ‖μ‖ < 1)) < Fintype.card ι ∧ ¬ Function.Surjective (sysOp f₁ f₂ f₃) ∨
      (∀ μ ∈ ((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1) ∧
        Multiset.card (((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots.filter
          (fun μ => ‖μ‖ < 1)) = Fintype.card ι ∧ ¬ Function.Injective (sysOp f₁ f₂ f₃) := by
  by_cases hu : ∃ μ ∈ ((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots, ‖μ‖ = 1
  · obtain ⟨μ, hμ, h1⟩ := hu
    exact Or.inl ⟨⟨μ, hμ, h1⟩, not_surjective_of_unit hdet hμ h1⟩
  · have hnu : ∀ μ ∈ ((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1 :=
      fun μ hμ h1 => hu ⟨μ, hμ, h1⟩
    rcases lt_trichotomy (Multiset.card (((quadPoly f₁ f₂ f₃).map Complex.ofRealHom).roots.filter
      (fun μ => ‖μ‖ < 1))) (Fintype.card ι) with h | h | h
    · exact Or.inr (Or.inr (Or.inl ⟨hnu, h, not_surjective_of_count_lt hnu h⟩))
    · refine Or.inr (Or.inr (Or.inr ⟨hnu, h, fun hinj => hfail ?_⟩))
      exact (linDeterminate_iff f₁ f₂ f₃).mpr ⟨(natDegree_quadPoly hdet).1, hnu, h,
        (homInjective_iff_injective _ _ _).mpr hinj⟩
    · exact Or.inr (Or.inl ⟨h, not_injective_of_count_gt h⟩)

end Woodford.PriceLevelDetermination.LinearSystems
