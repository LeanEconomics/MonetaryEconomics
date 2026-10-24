/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.GeneralBKForward

/-!
# The general Blanchard–Kahn theorem

Woodford (2003), *Interest and Prices*, Appendix C.1, p. 670 (Props. C.1, C.2 and footnotes
1–2), which *assumes* the counting rule of Blanchard and Kahn (1980). This module proves the
general rule, for any number of predetermined and non-predetermined variables and any
`ExpectationSystem` (perfect foresight and genuine uncertainty alike), with existence and
uniqueness among bounded adapted processes.

Restated from the Woodford Chapter 4 project (`NeoWicksellianFramework.GeneralBK`, namespace
renamed; this project does not import across projects). Used here for Galí (2015), Ch. 3,
§3.4.2, p. 75 and fn. 14 (`MoneyRuleDeterminacy`).

## Setting

The state is `y_t = (z_t, x_t)` with index type `Z ⊕ X`: `z_t` non-predetermined, `x_t`
predetermined. `E_t y_{t+1} = A y_t + w_t` (`Solves`) for a real matrix `A`; an equilibrium
(`Equil`) is a bounded adapted solution whose predetermined block `x_{t+1}` is known at date `t`
and starts at the given `x_0`. `Determinate`: for every bounded adapted forcing `w` and every
`x_0` there is exactly one equilibrium.

## Main results

* `determinate_of` (**sufficiency**, any `ExpectationSystem`): no eigenvalue of `A` on the unit
  circle (`NoUnit`), the bounded-orbit (stable) subspace of dimension `|X|`, and genericity
  (`GenericX`: the stable subspace meets `{x = 0}` only in `0`) imply determinacy. Proof: the
  stable subspace is the graph of `G` (`InvariantSplit.exists_graph`); `ẑ_t = z_t − G x_t` solves
  `E_t ẑ_{t+1} = C ẑ_t + ŵ_t` with all eigenvalues of `C` outside the closed disc, so it is the
  forward solution through `C⁻¹`; then `x_{t+1} = Λ x_t + A_xz ẑ_t + w^x_t` with `Λ` stable is
  solved backward from `x_0`.
* Necessity, for every `ExpectationSystem` on a nonempty state space, failure by failure:
  - an eigenvalue on the unit circle gives **non-existence** by resonance: a bounded
    deterministic forcing `w_t = Re(μ^{t+1} b)` admits no bounded solution at all
    (`nonexist_of_unit`);
  - a failure of genericity gives **non-uniqueness**: next to every equilibrium there is another
    one, obtained by adding a bounded orbit with `x_0 = 0` (`mult_of_not_genericX`); this
    covers a stable subspace of dimension larger than `|X|` (`InvariantSplit.not_genericX_of_lt`);
  - a stable subspace of dimension smaller than `|X|` gives **non-existence** for some `x_0`
    already with `w = 0` (`nonexist_of_lt`).
* `determinate_iff` (**the Blanchard–Kahn theorem**): `Determinate ↔ NoUnit ∧ dim = |X| ∧ GenericX`;
  `determinate_iff_count`: the same with the dimension replaced by the number of eigenvalues in
  the open unit disc counted with algebraic multiplicity (`stableCount A = |X|`);
  `determinate_iff_unstableCount`: equivalently `|Z|` eigenvalues outside the closed disc.
* `determinate_iff_perfectForesight`: determinacy does not depend on the expectation system.
* `mem_boundedOrbits_iff_tendsto_of_noUnit`: with no eigenvalue on the unit circle the
  bounded-orbit subspace is the stable invariant subspace `{v : Aᵗ v → 0}`, and its dimension is
  the number of stable eigenvalues (`InvariantSplit.finrank_eq_stableCount`), so (ii) can be read
  either way.
-/

namespace Gali.BasicNewKeynesianModel.GeneralBK

open Filter Topology InvariantSplit GeneralBKForward
open scoped Matrix

/-! ### Small tools -/

/-- Woodford (2003), App. C.1, p. 670 (tool): a complexified real vector under a complexified
real matrix. -/
theorem map_ofReal_mulVec {m n : Type*} [Fintype n] (K : Matrix m n ℝ) (v : n → ℝ) :
    K.map Complex.ofReal *ᵥ (fun i => (v i : ℂ)) = fun i => ((K *ᵥ v) i : ℂ) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Complex.ofReal_sum]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Woodford (2003), App. C.1, p. 670 (tool): a matrix with all eigenvalues outside the closed
unit disc is invertible. -/
theorem det_ne_zero_of_unstable {K : Matrix κ κ ℝ} (h : ∀ μ ∈ eigs K, 1 < ‖μ‖) : K.det ≠ 0 := by
  intro hd
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  have h0 : (0 : ℂ) ∈ eigs K := by
    refine mem_eigs_of_eigvec (c := fun i => (v i : ℂ)) ?_ ?_
    · intro hc
      apply hv0
      funext i
      have := congrFun hc i
      simpa using this
    · rw [map_ofReal_mulVec, hv]
      funext i
      simp
  have := h 0 h0
  norm_num at this

/-- Woodford (2003), App. C.1, p. 670 (tool): if every eigenvalue of `K` lies outside the closed
unit disc, every eigenvalue of `K⁻¹` lies in the open disc. -/
theorem inv_stable {K : Matrix κ κ ℝ} (h : ∀ μ ∈ eigs K, 1 < ‖μ‖) : ∀ μ ∈ eigs K⁻¹, ‖μ‖ < 1 := by
  have hdet := det_ne_zero_of_unstable h
  have hKK : K * K⁻¹ = 1 := Matrix.mul_nonsing_inv K (isUnit_iff_ne_zero.mpr hdet)
  intro μ hμ
  obtain ⟨c, hc0, hc⟩ := exists_eigvec hμ
  have hmap : K.map Complex.ofReal * K⁻¹.map Complex.ofReal = 1 := by
    have e : (K * K⁻¹).map Complex.ofReal = K.map Complex.ofReal * K⁻¹.map Complex.ofReal :=
      Matrix.map_mul (f := Complex.ofRealHom)
    rw [← e, hKK]
    exact Matrix.map_one _ (by simp) (by simp)
  have hc' : μ • (K.map Complex.ofReal *ᵥ c) = c := by
    calc μ • (K.map Complex.ofReal *ᵥ c) = K.map Complex.ofReal *ᵥ (μ • c) :=
          (Matrix.mulVec_smul _ _ _).symm
      _ = (K.map Complex.ofReal * K⁻¹.map Complex.ofReal) *ᵥ c := by
          rw [← hc, Matrix.mulVec_mulVec]
      _ = c := by rw [hmap, Matrix.one_mulVec]
  have hμ0 : μ ≠ 0 := by
    intro h0
    apply hc0
    rw [← hc', h0, zero_smul]
  have hev : K.map Complex.ofReal *ᵥ c = μ⁻¹ • c := (eq_inv_smul_iff₀ hμ0).mpr hc'
  have h1 := h μ⁻¹ (mem_eigs_of_eigvec hc0 hev)
  rw [norm_inv] at h1
  exact (one_lt_inv₀ (norm_pos_iff.mpr hμ0)).mp h1

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

omit [Fintype κ] [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): sums of bounded vector processes are bounded. -/
theorem boundedV_add {a b : ℕ → κ → Ω → ℝ} (ha : BoundedV a) (hb : BoundedV b) :
    BoundedV (fun t => a t + b t) := by
  obtain ⟨A, hA⟩ := ha
  obtain ⟨B, hB⟩ := hb
  exact ⟨A + B, fun t i ω => (abs_add_le _ _).trans (add_le_add (hA t i ω) (hB t i ω))⟩

omit [Fintype κ] [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): differences of bounded vector processes are
bounded. -/
theorem boundedV_sub {a b : ℕ → κ → Ω → ℝ} (ha : BoundedV a) (hb : BoundedV b) :
    BoundedV (fun t => a t - b t) := by
  obtain ⟨A, hA⟩ := ha
  obtain ⟨B, hB⟩ := hb
  exact ⟨A + B, fun t i ω => (abs_sub _ _).trans (add_le_add (hA t i ω) (hB t i ω))⟩

omit [Fintype κ] [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): negatives of bounded vector processes are
bounded. -/
theorem boundedV_neg {a : ℕ → κ → Ω → ℝ} (ha : BoundedV a) : BoundedV (fun t => -a t) := by
  obtain ⟨A, hA⟩ := ha
  exact ⟨A, fun t i ω => by simpa using hA t i ω⟩

omit [Fintype κ] [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): sums of adapted vector processes are adapted. -/
theorem adaptedV_add {a b : ℕ → κ → Ω → ℝ} (ha : AdaptedV 𝔼 a) (hb : AdaptedV 𝔼 b) :
    AdaptedV 𝔼 (fun t => a t + b t) := fun t i => by
  simp only [Pi.add_apply, map_add, ha t i, hb t i]

omit [Fintype κ] [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): differences of adapted vector processes are
adapted. -/
theorem adaptedV_sub {a b : ℕ → κ → Ω → ℝ} (ha : AdaptedV 𝔼 a) (hb : AdaptedV 𝔼 b) :
    AdaptedV 𝔼 (fun t => a t - b t) := fun t i => by
  simp only [Pi.sub_apply, map_sub, ha t i, hb t i]

omit [Fintype κ] [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): negatives of adapted vector processes are
adapted. -/
theorem adaptedV_neg {a : ℕ → κ → Ω → ℝ} (ha : AdaptedV 𝔼 a) : AdaptedV 𝔼 (fun t => -a t) :=
  fun t i => by simp only [Pi.neg_apply, map_neg, ha t i]

/-! ### The system -/

/-- Woodford (2003), (C.19) and App. C.1, p. 670: `y` solves `E_t y_{t+1} = A y_t + w_t`. -/
def Solves {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (w y : ℕ → ι → Ω → ℝ) : Prop :=
  ∀ t i, 𝔼.E t (y (t + 1) i) = mv A (y t) i + w t i

variable {Z X : Type*} [Fintype Z] [Fintype X] [DecidableEq Z] [DecidableEq X]

/-- Woodford (2003), App. C.1, pp. 670–672 (Blanchard and Kahn 1980): a (bounded) rational
expectations equilibrium of `E_t y_{t+1} = A y_t + w_t` with state `y = (z, x)`: `y` solves the
system, is adapted and bounded, the predetermined block `x_{t+1}` is known at date `t`, and
`x_0` is the given vector. -/
def Equil (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (w : ℕ → Z ⊕ X → Ω → ℝ) (x0 : X → ℝ)
    (y : ℕ → Z ⊕ X → Ω → ℝ) : Prop :=
  Solves 𝔼 A w y ∧ AdaptedV 𝔼 y ∧
    (∀ t j, 𝔼.E t (y (t + 1) (Sum.inr j)) = y (t + 1) (Sum.inr j)) ∧
    (∀ j, y 0 (Sum.inr j) = fun _ => x0 j) ∧ BoundedV y

/-- Woodford (2003), App. C.1, p. 670 (determinacy, Blanchard and Kahn 1980): for every bounded
adapted forcing and every initial value of the predetermined variables there is exactly one
bounded equilibrium. -/
def Determinate (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) : Prop :=
  ∀ w : ℕ → Z ⊕ X → Ω → ℝ, BoundedV w → AdaptedV 𝔼 w → ∀ x0 : X → ℝ, ∃! y, Equil 𝔼 A w x0 y

omit [Fintype Z] [Fintype X] [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 670 (tool): a random state vector at a fixed outcome, split
into its blocks. -/
theorem eval_split (y : Z ⊕ X → Ω → ℝ) (ω : Ω) :
    (fun k => y k ω) = Sum.elim (fun i => y (Sum.inl i) ω) (fun j => y (Sum.inr j) ω) := by
  funext k
  rcases k with i | j <;> rfl

/-! ### Identities behind the change of variables `ẑ = z − G x` -/

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (tool): the rows of `A y` for the non-predetermined block,
`(A y)_z = A_zz z + A_zx x`. -/
theorem mv_inl (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (y : Z ⊕ X → Ω → ℝ) :
    (fun i => mv A y (Sum.inl i)) =
      mv A.toBlocks₁₁ (fun i => y (Sum.inl i)) + mv A.toBlocks₁₂ (fun j => y (Sum.inr j)) := by
  funext i
  simp only [mv, Fintype.sum_sum_type, Pi.add_apply]
  rfl

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (tool): the rows of `A y` for the predetermined block,
`(A y)_x = A_xz z + A_xx x`. -/
theorem mv_inr (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (y : Z ⊕ X → Ω → ℝ) :
    (fun j => mv A y (Sum.inr j)) =
      mv A.toBlocks₂₁ (fun i => y (Sum.inl i)) + mv A.toBlocks₂₂ (fun j => y (Sum.inr j)) := by
  funext j
  simp only [mv, Fintype.sum_sum_type, Pi.add_apply]
  rfl

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (tool): the invariance of the graph solved for `A_zx`:
`A_zx = G A_xz G + G A_xx − A_zz G`. -/
theorem zx_block_eq {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ}
    (hinv : A.toBlocks₁₁ * G + A.toBlocks₁₂ = G * lam A G) :
    A.toBlocks₁₂ = G * A.toBlocks₂₁ * G + G * A.toBlocks₂₂ - A.toBlocks₁₁ * G := by
  rw [eq_sub_iff_add_eq, add_comm, hinv, lam, Matrix.mul_add, Matrix.mul_assoc]

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (uniqueness step): for random `(z, x)`,
`A_zz z + A_zx x + w^z − G (A_xz z + A_xx x + w^x) = C (z − G x) + (w^z − G w^x)`. -/
theorem identity_zhat {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ}
    (hinv : A.toBlocks₁₁ * G + A.toBlocks₁₂ = G * lam A G) (z wz : Z → Ω → ℝ)
    (x wx : X → Ω → ℝ) :
    mv A.toBlocks₁₁ z + mv A.toBlocks₁₂ x + wz -
        mv G (mv A.toBlocks₂₁ z + mv A.toBlocks₂₂ x + wx) =
      mv (cmat A G) (z - mv G x) + (wz - mv G wx) := by
  rw [zx_block_eq hinv, cmat]
  simp only [add_mv, sub_mv, mv_add, mv_sub, ← mv_mv]
  abel

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (the predetermined block):
`A_xz z + A_xx x = A_xz (z − G x) + Λ x`. -/
theorem identity_x (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (G : Matrix Z X ℝ) (z : Z → Ω → ℝ)
    (x : X → Ω → ℝ) :
    mv A.toBlocks₂₁ z + mv A.toBlocks₂₂ x = mv A.toBlocks₂₁ (z - mv G x) + mv (lam A G) x := by
  rw [lam]
  simp only [add_mv, mv_sub, ← mv_mv]
  abel

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (existence step): with `z = ẑ + G x`,
`C ẑ + (w^z − G w^x) + G (Λ x + (A_xz ẑ + w^x)) = A_zz z + A_zx x + w^z`. -/
theorem identity_exist {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ}
    (hinv : A.toBlocks₁₁ * G + A.toBlocks₁₂ = G * lam A G) (a wz : Z → Ω → ℝ)
    (b c : X → Ω → ℝ) :
    mv (cmat A G) a + (wz - mv G c) + mv G (mv (lam A G) b + (mv A.toBlocks₂₁ a + c)) =
      mv A.toBlocks₁₁ (a + mv G b) + mv A.toBlocks₁₂ b + wz := by
  rw [zx_block_eq hinv, cmat, lam]
  simp only [add_mv, sub_mv, mv_add, ← mv_mv]
  abel_nf

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (existence step, predetermined block):
`Λ x + (A_xz ẑ + w^x) = A_xz (ẑ + G x) + A_xx x + w^x`. -/
theorem identity_exist_x (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (G : Matrix Z X ℝ) (a : Z → Ω → ℝ)
    (b c : X → Ω → ℝ) :
    mv (lam A G) b + (mv A.toBlocks₂₁ a + c) =
      mv A.toBlocks₂₁ (a + mv G b) + mv A.toBlocks₂₂ b + c := by
  rw [lam]
  simp only [add_mv, mv_add, ← mv_mv]
  abel

/-! ### The backward recursion for the predetermined block -/

/-- Woodford (2003), App. C.1, p. 672: the predetermined block `x_{t+1} = Λ x_t + g_t`,
`x_0` given, as a process of random variables. -/
def xrecR (L : Matrix X X ℝ) (g : ℕ → X → Ω → ℝ) (x0 : X → ℝ) : ℕ → X → Ω → ℝ
  | 0 => fun j _ => x0 j
  | t + 1 => mv L (xrecR L g x0 t) + g t

omit [DecidableEq Z] in
/-- Woodford (2003), App. C.1, p. 672: the backward recursion is bounded when `Λ` is stable and
`g` is bounded. -/
theorem xrecR_bounded {L : Matrix X X ℝ} (hL : ∀ μ ∈ eigs L, ‖μ‖ < 1) {g : ℕ → X → Ω → ℝ}
    (hg : BoundedV g) (x0 : X → ℝ) : BoundedV (xrecR L g x0) := by
  obtain ⟨Cb, ρ, hCb, hρ0, hρ1, hLp⟩ := pow_entry_bound L hL
  obtain ⟨F, hF⟩ := hg
  refine ⟨Fintype.card X * Cb * (∑ j, |x0 j| + max F 0 / (1 - ρ)), fun t j ω => ?_⟩
  have hrec : ∀ t, (fun j => xrecR L g x0 (t + 1) j ω) =
      L *ᵥ (fun j => xrecR L g x0 t j ω) + fun j => g t j ω := by
    intro t
    funext j
    simp only [xrecR, Pi.add_apply, mv_apply]
  exact rec_bounded (x := fun t j => xrecR L g x0 t j ω) (f := fun t j => g t j ω) hCb hρ0.le
    hρ1 hLp hrec (le_max_right _ _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (fun t j => (hF t j ω).trans (le_max_left _ _))
    (fun j => Finset.single_le_sum (f := fun j => |x0 j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)) t j

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672: the backward recursion is known one period ahead:
`x_t` is known at `t` and so is `x_{t+1}` (when `g` is adapted). -/
theorem xrecR_known {L : Matrix X X ℝ} {g : ℕ → X → Ω → ℝ} (hg : AdaptedV 𝔼 g) (x0 : X → ℝ) :
    ∀ t j, 𝔼.E t (xrecR L g x0 t j) = xrecR L g x0 t j ∧
      𝔼.E t (xrecR L g x0 (t + 1) j) = xrecR L g x0 (t + 1) j := by
  have hnext : ∀ t, (∀ j, 𝔼.E t (xrecR L g x0 t j) = xrecR L g x0 t j) →
      ∀ j, 𝔼.E t (xrecR L g x0 (t + 1) j) = xrecR L g x0 (t + 1) j := by
    intro t ht j
    simp only [xrecR, Pi.add_apply, map_add, E_mv 𝔼, hg t j]
    congr 2
    funext k
    exact ht k
  have hcur : ∀ t j, 𝔼.E t (xrecR L g x0 t j) = xrecR L g x0 t j := by
    intro t
    induction t with
    | zero => intro j; exact 𝔼.const 0 (x0 j)
    | succ t ih =>
      intro j
      rw [← hnext t ih j, 𝔼.known (Nat.le_succ t)]
  exact fun t j => ⟨hcur t j, hnext t (hcur t) j⟩

/-! ### Sufficiency -/

/-- Woodford (2003), App. C.1, p. 672 (tool): with `K C = C K = 1`, the forward form
`ẑ_t = K E_t ẑ_{t+1} − K ŵ_t` is the system `E_t ẑ_{t+1} = C ẑ_t + ŵ_t`. -/
theorem fsolves_iff_cform {C K : Matrix Z Z ℝ} (hKC : K * C = 1) (hCK : C * K = 1)
    (wh zh : ℕ → Z → Ω → ℝ) :
    FSolves 𝔼 K (fun t => -mv K (wh t)) zh ↔
      ∀ t, (fun i => 𝔼.E t (zh (t + 1) i)) = mv C (zh t) + wh t := by
  constructor
  · intro h t
    have e := congrArg (mv C) (h t)
    rw [mv_add, mv_neg, mv_mv, mv_mv, hCK, mv_one, mv_one] at e
    rw [e]
    abel
  · intro h t
    simp only [h t, mv_add, mv_mv, hKC, mv_one, add_neg_cancel_right]

/-- **Blanchard–Kahn, sufficiency** (Woodford (2003), App. C.1, p. 670; Blanchard and Kahn 1980):
for any expectation system, if no eigenvalue of `A` lies on the unit circle, the stable
(bounded-orbit) subspace has dimension equal to the number of predetermined variables, and it
meets `{x = 0}` only in `0`, then for every bounded adapted forcing and every `x_0` there is
exactly one bounded equilibrium. -/
theorem determinate_of {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} (hnu : NoUnit A)
    (hd : Module.finrank ℝ (boundedOrbits A) = Fintype.card X) (hg : GenericX A) :
    Determinate 𝔼 A := by
  obtain ⟨G, hG⟩ := exists_graph hd hg
  have hinv := graph_invariant hG
  have hΛ := lam_stable hG hnu
  have hC := cmat_unstable hG hg hΛ
  have hdet : IsUnit (cmat A G).det := isUnit_iff_ne_zero.mpr (det_ne_zero_of_unstable hC)
  have hKC : (cmat A G)⁻¹ * cmat A G = 1 := Matrix.nonsing_inv_mul _ hdet
  have hCK : cmat A G * (cmat A G)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  obtain ⟨CbK, ρK, -, hρK0, hρK1, hKpow⟩ := pow_entry_bound _ (inv_stable hC)
  intro w hwb hwa x0
  set wz : ℕ → Z → Ω → ℝ := fun t i => w t (Sum.inl i) with hwz
  set wx : ℕ → X → Ω → ℝ := fun t j => w t (Sum.inr j) with hwx
  have hwzb : BoundedV wz := by
    obtain ⟨M, hM⟩ := hwb; exact ⟨M, fun t i ω => hM t _ ω⟩
  have hwxb : BoundedV wx := by
    obtain ⟨M, hM⟩ := hwb; exact ⟨M, fun t j ω => hM t _ ω⟩
  have hwzA : AdaptedV 𝔼 wz := fun t i => hwa t (Sum.inl i)
  have hwxA : AdaptedV 𝔼 wx := fun t j => hwa t (Sum.inr j)
  set wh : ℕ → Z → Ω → ℝ := fun t => wz t - mv G (wx t) with hwh
  have hwhb : BoundedV wh := boundedV_sub hwzb (boundedV_mv G hwxb)
  have hwhA : AdaptedV 𝔼 wh := adaptedV_sub 𝔼 hwzA (adaptedV_mv 𝔼 G hwxA)
  have hfb : BoundedV (fun t => -mv (cmat A G)⁻¹ (wh t)) :=
    boundedV_neg (boundedV_mv _ hwhb)
  have hfA : AdaptedV 𝔼 (fun t => -mv (cmat A G)⁻¹ (wh t)) :=
    adaptedV_neg 𝔼 (adaptedV_mv 𝔼 _ hwhA)
  obtain ⟨Mf, hMf⟩ := hfb
  obtain ⟨zh, hzh, hzhA, hzhb⟩ := fsolves_exists 𝔼 hρK0.le hρK1 hKpow hMf hfA
  have hzhE := (fsolves_iff_cform 𝔼 hKC hCK wh zh).mp hzh
  set g : ℕ → X → Ω → ℝ := fun t => mv A.toBlocks₂₁ (zh t) + wx t with hgdef
  have hgA : AdaptedV 𝔼 g := adaptedV_add 𝔼 (adaptedV_mv 𝔼 _ hzhA) hwxA
  have hgb : BoundedV g := boundedV_add (boundedV_mv _ hzhb) hwxb
  set xr := xrecR (lam A G) g x0 with hxr
  have hxrb : BoundedV xr := xrecR_bounded hΛ hgb x0
  have hxrK := xrecR_known 𝔼 (L := lam A G) hgA x0
  have hxr1 : ∀ t, xr (t + 1) = mv (lam A G) (xr t) + g t := fun t => rfl
  set y : ℕ → Z ⊕ X → Ω → ℝ := fun t => Sum.elim (zh t + mv G (xr t)) (xr t) with hy
  have hyz : ∀ t, (fun i => y t (Sum.inl i)) = zh t + mv G (xr t) := fun t => rfl
  have hyx : ∀ t, (fun j => y t (Sum.inr j)) = xr t := fun t => rfl
  -- every equilibrium is `y`
  have huniq : ∀ y', Equil 𝔼 A w x0 y' → y' = y := by
    rintro y' ⟨hs, ha, hk, h0, hb⟩
    set zh' : ℕ → Z → Ω → ℝ :=
      fun t => (fun i => y' t (Sum.inl i)) - mv G (fun j => y' t (Sum.inr j)) with hzh'
    have hzh'A : AdaptedV 𝔼 zh' :=
      adaptedV_sub 𝔼 (fun t i => ha t (Sum.inl i))
        (adaptedV_mv 𝔼 G (fun t j => ha t (Sum.inr j)))
    have hb1 : BoundedV (fun t i => y' t (Sum.inl i)) := by
      obtain ⟨M, hM⟩ := hb; exact ⟨M, fun t i ω => hM t _ ω⟩
    have hb2 : BoundedV (fun t j => y' t (Sum.inr j)) := by
      obtain ⟨M, hM⟩ := hb; exact ⟨M, fun t j ω => hM t _ ω⟩
    have hzh'b : BoundedV zh' := boundedV_sub hb1 (boundedV_mv G hb2)
    have hEz : ∀ t, (fun i => 𝔼.E t (y' (t + 1) (Sum.inl i))) =
        (fun i => mv A (y' t) (Sum.inl i)) + wz t := fun t => by
      funext i; rw [hs t]; rfl
    have hEx : ∀ t, (fun j => 𝔼.E t (y' (t + 1) (Sum.inr j))) =
        (fun j => mv A (y' t) (Sum.inr j)) + wx t := fun t => by
      funext j; rw [hs t]; rfl
    have hcf : ∀ t, (fun i => 𝔼.E t (zh' (t + 1) i)) = mv (cmat A G) (zh' t) + wh t := by
      intro t
      have hE : (fun i => 𝔼.E t (zh' (t + 1) i)) =
          (fun i => 𝔼.E t (y' (t + 1) (Sum.inl i))) -
            mv G (fun j => 𝔼.E t (y' (t + 1) (Sum.inr j))) := by
        funext i
        simp only [hzh', Pi.sub_apply, map_sub, E_mv 𝔼]
      rw [hE, hEz, hEx, mv_inl, mv_inr, identity_zhat hinv]
    have hzz : zh' = zh :=
      fsolves_unique 𝔼 hρK0.le hρK1 hKpow ((fsolves_iff_cform 𝔼 hKC hCK wh zh').mpr hcf) hzh
        hzh'A hzhA hzh'b ⟨_, hzhb.choose_spec⟩
    have hxx : ∀ t, (fun j => y' t (Sum.inr j)) = xr t := by
      intro t
      induction t with
      | zero => funext j; exact h0 j
      | succ t ih =>
        have e1 : (fun j => y' (t + 1) (Sum.inr j)) =
            (fun j => 𝔼.E t (y' (t + 1) (Sum.inr j))) := by
          funext j; exact (hk t j).symm
        have hz't : (fun i => y' t (Sum.inl i)) - mv G (fun j => y' t (Sum.inr j)) = zh' t := rfl
        rw [e1, hEx, mv_inr, identity_x A G, hz't, hzz, ih, hxr1]
        simp only [hgdef]
        abel
    funext t k
    rcases k with i | j
    · have e := congrFun (congrArg (fun f => f t) hzz) i
      simp only [hzh', Pi.sub_apply, hxx t] at e
      have e2 : y' t (Sum.inl i) = zh t i + mv G (xr t) i := by
        rw [← e]; abel
      rw [e2]
      rfl
    · exact congrFun (hxx t) j
  refine ⟨y, ⟨?_, ?_, ?_, ?_, ?_⟩, huniq⟩
  · -- the system
    intro t k
    rcases k with i | j
    · have hv : (fun i => 𝔼.E t (y (t + 1) (Sum.inl i))) =
          (fun i => mv A (y t) (Sum.inl i)) + wz t := by
        have e1 : (fun i => 𝔼.E t (y (t + 1) (Sum.inl i))) =
            (fun i => 𝔼.E t (zh (t + 1) i)) + mv G (fun j => 𝔼.E t (xr (t + 1) j)) := by
          funext i
          simp only [hy, Sum.elim_inl, Pi.add_apply, map_add, E_mv 𝔼]
        have e2 : (fun j => 𝔼.E t (xr (t + 1) j)) = xr (t + 1) := by
          funext j; exact (hxrK t j).2
        rw [e1, e2, hzhE t, hxr1, mv_inl, hyz, hyx, hwh, hgdef]
        exact identity_exist hinv _ _ _ _
      exact congrFun hv i
    · have hv : (fun j => 𝔼.E t (y (t + 1) (Sum.inr j))) =
          (fun j => mv A (y t) (Sum.inr j)) + wx t := by
        have e1 : (fun j => 𝔼.E t (y (t + 1) (Sum.inr j))) = xr (t + 1) := by
          funext j; exact (hxrK t j).2
        rw [e1, hxr1, mv_inr, hyz, hyx, hgdef]
        exact identity_exist_x A G _ _ _
      exact congrFun hv j
  · -- adapted
    intro t k
    rcases k with i | j
    · simp only [hy, Sum.elim_inl, Pi.add_apply, map_add, E_mv 𝔼, hzhA t i]
      congr 2
      funext j
      exact (hxrK t j).1
    · exact (hxrK t j).1
  · -- the predetermined block is known one period ahead
    intro t j
    exact (hxrK t j).2
  · -- the initial condition
    intro j
    rfl
  · -- boundedness
    obtain ⟨Mz, hMz⟩ := hzhb
    obtain ⟨Mx, hMx⟩ := hxrb
    obtain ⟨Mg, hMg⟩ := boundedV_mv G ⟨Mx, hMx⟩
    refine ⟨max (Mz + Mg) Mx, fun t k ω => ?_⟩
    rcases k with i | j
    · change |zh t i ω + mv G (xr t) i ω| ≤ _
      exact ((abs_add_le _ _).trans (add_le_add (hMz t i ω) (hMg t i ω))).trans
        (le_max_left _ _)
    · exact (hMx t j ω).trans (le_max_right _ _)

/-! ### Necessity (i): an eigenvalue on the unit circle gives non-existence by resonance -/

open ComplexConjugate

omit [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): for a left eigenvector `q A = μ q`,
`q · (A e) = μ (q · e)`. -/
theorem sum_q_mulVec {A : Matrix κ κ ℝ} {μ : ℂ} {q : κ → ℂ}
    (hq : q ᵥ* A.map Complex.ofReal = μ • q) (e : κ → ℝ) :
    ∑ i, q i * ((A *ᵥ e) i : ℂ) = μ * ∑ j, q j * (e j : ℂ) := by
  have hcol : ∀ j, ∑ i, q i * (A i j : ℂ) = μ * q j := fun j => by
    have := congrFun hq j
    simpa [Matrix.vecMul, dotProduct] using this
  simp only [Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, hcol j, mul_assoc]

/-- Woodford (2003), App. C.1, p. 670 (tool): a linear lower bound `a + T c − K` with `c > 0`
cannot stay below a constant. -/
theorem false_of_linear_growth {a c K Q : ℝ} (hc : 0 < c) (h : ∀ T : ℕ, a + T * c - K ≤ Q) :
    False := by
  obtain ⟨T, hT⟩ := exists_nat_gt ((Q + K - a) / c)
  have := h T
  rw [div_lt_iff₀ hc] at hT
  linarith

omit [DecidableEq κ] in
/-- **Resonance** (Woodford (2003), App. C.1, p. 670, fn. 1: the boundary case): let `‖μ‖ = 1`
and `q A = μ q`, `q ≠ 0` (with `q` real when `μ = ±1`). Then the deterministic system
`e_{t+1} = A e_t + w_t` with the bounded forcing `w_{t,i} = Re(μ^{t+1} q̄_i)` has no bounded
solution: `d_t = (q · e_t) μ̄ᵗ` grows like `t ∑|q_i|²/2`. -/
theorem no_bounded_resonance {A : Matrix κ κ ℝ} {μ : ℂ} (hμ : ‖μ‖ = 1) {q : κ → ℂ}
    (hq0 : q ≠ 0) (hq : q ᵥ* A.map Complex.ofReal = μ • q)
    (hre : μ ^ 2 = 1 → ∀ i, (q i).im = 0) {e : ℕ → κ → ℝ}
    (he : ∀ t, e (t + 1) = A *ᵥ e t + fun i => (μ ^ (t + 1) * conj (q i)).re)
    {B : ℝ} (hB : ∀ t i, |e t i| ≤ B) : False := by
  set m : ℕ → ℂ := fun t => ∑ i, q i * (e t i : ℂ) with hm
  set N : ℝ := ∑ i, ‖q i‖ ^ 2 with hN
  set σ : ℂ := ∑ i, q i ^ 2 with hσ
  set ζ : ℂ := conj μ ^ 2 with hζ
  have hμc : μ * conj μ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hμ]
    norm_num
  have hN0 : 0 < N := by
    obtain ⟨i, hi⟩ : ∃ i, q i ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hq0 (funext hne)
    exact Finset.sum_pos' (fun i _ => by positivity)
      ⟨i, Finset.mem_univ i, by have := norm_pos_iff.mpr hi; positivity⟩
  have hNc : (N : ℂ) = ∑ i, q i * conj (q i) := by
    rw [hN]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hqw : ∀ t, ∑ i, q i * (((μ ^ (t + 1) * conj (q i)).re : ℝ) : ℂ) =
      (μ ^ (t + 1) * (N : ℂ) + conj μ ^ (t + 1) * σ) / 2 := by
    intro t
    rw [hNc, hσ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_eq_add_conj, map_mul, map_pow, Complex.conj_conj]
    ring
  have hm_succ : ∀ t, m (t + 1) = μ * m t + (μ ^ (t + 1) * (N : ℂ) + conj μ ^ (t + 1) * σ) / 2 := by
    intro t
    simp only [hm, he t, Pi.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib]
    rw [sum_q_mulVec hq, hqw]
  set d : ℕ → ℂ := fun t => m t * conj μ ^ t with hd
  have hd_succ : ∀ t, d (t + 1) = d t + ((N : ℂ) + σ * ζ ^ (t + 1)) / 2 := by
    intro t
    have h1 : μ ^ (t + 1) * conj μ ^ (t + 1) = 1 := by rw [← mul_pow, hμc, one_pow]
    have h2 : μ * conj μ ^ (t + 1) = conj μ ^ t := by
      rw [pow_succ]
      linear_combination (conj μ ^ t) * hμc
    have h3 : conj μ ^ (t + 1) * conj μ ^ (t + 1) = ζ ^ (t + 1) := by
      rw [hζ, ← pow_mul, ← pow_add]
      ring_nf
    simp only [hd]
    rw [hm_succ t]
    linear_combination (m t) * h2 + ((N : ℂ) / 2) * h1 + (σ / 2) * h3
  set S : ℕ → ℂ := fun T => ∑ s ∈ Finset.range T, ζ ^ (s + 1) with hS
  have hd_closed : ∀ T : ℕ, d T = d 0 + ((T * N / 2 : ℝ) : ℂ) + σ / 2 * S T := by
    intro T
    induction T with
    | zero => simp [hS]
    | succ T ih =>
      rw [hd_succ T, ih]
      simp only [hS, Finset.sum_range_succ]
      push_cast
      ring
  set Q : ℝ := ∑ i, ‖q i‖ * B with hQ
  have hdQ : ∀ T, ‖d T‖ ≤ Q := by
    intro T
    simp only [hd, hm, norm_mul, norm_pow, Complex.norm_conj, hμ, one_pow, mul_one]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hB T i) (norm_nonneg _)
  -- the oscillating part is bounded below
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ T, -K ≤ (σ / 2 * S T).re := by
    by_cases hζ1 : ζ = 1
    · have hμ2 : μ ^ 2 = 1 := by
        have := congrArg conj hζ1
        rw [hζ, map_pow, Complex.conj_conj, map_one] at this
        exact this
      have hreal := hre hμ2
      have hσN : σ = (N : ℂ) := by
        rw [hσ, hNc]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hqi : q i = ((q i).re : ℂ) := Complex.ext rfl (by simp [hreal i])
        rw [hqi, Complex.conj_ofReal]
        ring
      refine ⟨0, fun T => ?_⟩
      have hST : S T = (T : ℂ) := by simp [hS, hζ1]
      rw [hσN, hST]
      have : ((N : ℂ) / 2 * (T : ℂ)).re = N / 2 * T := by
        rw [show ((N : ℂ) / 2 * (T : ℂ)) = ((N / 2 * T : ℝ) : ℂ) by push_cast; ring,
          Complex.ofReal_re]
      rw [this]
      have : 0 ≤ N / 2 * T := by positivity
      linarith
    · have hζn : ‖ζ‖ = 1 := by rw [hζ, norm_pow, Complex.norm_conj, hμ, one_pow]
      have hζ1' : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ1
      refine ⟨‖σ‖ / ‖ζ - 1‖, fun T => ?_⟩
      have hSb : ‖S T‖ ≤ 2 / ‖ζ - 1‖ := by
        have e : S T = ζ * ((ζ ^ T - 1) / (ζ - 1)) := by
          rw [hS, ← geom_sum_eq hζ1 T, Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by ring
        rw [e, norm_mul, hζn, one_mul, norm_div]
        refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
        calc ‖ζ ^ T - 1‖ ≤ ‖ζ ^ T‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [norm_pow, hζn, one_pow, norm_one]; norm_num
      have hb : ‖σ / 2 * S T‖ ≤ ‖σ‖ / ‖ζ - 1‖ := by
        rw [norm_mul, norm_div, Complex.norm_two]
        calc ‖σ‖ / 2 * ‖S T‖ ≤ ‖σ‖ / 2 * (2 / ‖ζ - 1‖) :=
              mul_le_mul_of_nonneg_left hSb (by positivity)
          _ = ‖σ‖ / ‖ζ - 1‖ := by ring
      have := Complex.abs_re_le_norm (σ / 2 * S T)
      have := neg_abs_le (σ / 2 * S T).re
      linarith
  refine false_of_linear_growth (a := (d 0).re) (c := N / 2) (K := K) (Q := Q)
    (by positivity) fun T => ?_
  have h1 : (d T).re = (d 0).re + T * N / 2 + (σ / 2 * S T).re := by
    rw [hd_closed T, Complex.add_re, Complex.add_re, Complex.ofReal_re]
  have h2 : (d T).re ≤ Q := (Complex.re_le_norm _).trans (hdQ T)
  have h3 := hK T
  have : (T : ℝ) * (N / 2) = T * N / 2 := by ring
  linarith

/-- Woodford (2003), App. C.1, p. 670 (tool): an eigenvalue on the unit circle has a left
eigenvector, which can be chosen real when the eigenvalue is `±1`. -/
theorem exists_left_eigvec_unit {A : Matrix κ κ ℝ} {μ : ℂ} (hμ : μ ∈ eigs A) :
    ∃ q : κ → ℂ, q ≠ 0 ∧ q ᵥ* A.map Complex.ofReal = μ • q ∧
      (μ ^ 2 = 1 → ∀ i, (q i).im = 0) := by
  by_cases h2 : μ ^ 2 = 1
  · obtain ⟨r, hr⟩ : ∃ r : ℝ, μ = (r : ℂ) := by
      have : (μ - 1) * (μ + 1) = 0 := by linear_combination h2
      rcases mul_eq_zero.mp this with e | e
      · exact ⟨1, by push_cast; linear_combination e⟩
      · exact ⟨-1, by push_cast; linear_combination e⟩
    have hdetC := (mem_eigs_iff A μ).mp hμ
    have hmap : Matrix.scalar κ μ - A.map Complex.ofReal =
        (Matrix.scalar κ r - A).map Complex.ofReal := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [hr]
      · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
    have hdetR : (Matrix.scalar κ r - A).det = 0 := by
      have e := RingHom.map_det Complex.ofRealHom (Matrix.scalar κ r - A)
      rw [hmap] at hdetC
      have e2 : (Complex.ofRealHom.mapMatrix (Matrix.scalar κ r - A)) =
          (Matrix.scalar κ r - A).map Complex.ofReal := rfl
      rw [e2, hdetC] at e
      exact Complex.ofReal_eq_zero.mp e
    obtain ⟨p, hp0, hp⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdetR
    refine ⟨fun i => (p i : ℂ), ?_, ?_, fun _ i => by simp⟩
    · intro h
      apply hp0
      funext i
      have := congrFun h i
      simpa using this
    · rw [Matrix.vecMul_sub, sub_eq_zero] at hp
      funext j
      have hj := congrFun hp j
      have h1 : (p ᵥ* Matrix.scalar κ r) j = r * p j := by
        simp [Matrix.scalar_apply, Matrix.vecMul_diagonal, mul_comm]
      have e : ∑ i, p i * A i j = r * p j := by
        calc ∑ i, p i * A i j = (p ᵥ* A) j := rfl
          _ = r * p j := hj.symm.trans h1
      simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul, hr]
      exact_mod_cast e
  · obtain ⟨q, hq0, hq⟩ := exists_left_eigvec hμ
    exact ⟨q, hq0, hq, fun h => absurd h h2⟩

/-- **Non-existence at a unit-circle eigenvalue** (Woodford (2003), App. C.1, p. 670, fn. 1;
Blanchard and Kahn 1980): if `A` has an eigenvalue `μ` with `|μ| = 1`, there is a bounded
adapted (indeed deterministic) forcing, `w_{t,i} = Re(μ^{t+1} q̄_i)` for a left eigenvector `q`,
for which `E_t y_{t+1} = A y_t + w_t` has no bounded solution at all, adapted or not, whatever the
predetermined restrictions. Taking `E_0` of a solution reduces to `no_bounded_resonance`. -/
theorem nonexist_of_unit [Nonempty Ω] {A : Matrix κ κ ℝ} {μ : ℂ} (hμ : μ ∈ eigs A)
    (h1 : ‖μ‖ = 1) :
    ∃ w : ℕ → κ → Ω → ℝ, BoundedV w ∧ AdaptedV 𝔼 w ∧
      ∀ y, Solves 𝔼 A w y → BoundedV y → False := by
  obtain ⟨q, hq0, hq, hre⟩ := exists_left_eigvec_unit hμ
  refine ⟨fun t i _ => (μ ^ (t + 1) * conj (q i)).re, ⟨∑ i, ‖q i‖, fun t i _ => ?_⟩,
    fun t i => 𝔼.const t _, ?_⟩
  · refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_pow, h1, one_pow, one_mul, Complex.norm_conj]
    exact Finset.single_le_sum (f := fun i => ‖q i‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ i)
  · rintro y hy ⟨B, hB⟩
    obtain ⟨ω₀⟩ := ‹Nonempty Ω›
    refine no_bounded_resonance h1 hq0 hq hre (e := fun t i => 𝔼.E 0 (y t i) ω₀) (fun t => ?_)
      (B := B) (fun t i => 𝔼.abs_E_le (hB t i) 0 ω₀)
    funext i
    have e1 : 𝔼.E 0 (y (t + 1) i) = 𝔼.E 0 (𝔼.E t (y (t + 1) i)) :=
      (𝔼.tower (Nat.zero_le t) _).symm
    rw [e1, hy t i, map_add, E_mv 𝔼, 𝔼.const, Pi.add_apply, Pi.add_apply, mv_apply]

/-- Woodford (2003), App. C.1, p. 670, fn. 1: with an eigenvalue on the unit circle the system is
not determinate (equilibrium fails to exist for some bounded forcing). -/
theorem not_determinate_of_unit [Nonempty Ω] {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {μ : ℂ}
    (hμ : μ ∈ eigs A) (h1 : ‖μ‖ = 1) : ¬ Determinate 𝔼 A := by
  intro hdet
  obtain ⟨w, hwb, hwa, hno⟩ := nonexist_of_unit 𝔼 hμ h1
  obtain ⟨y, ⟨hs, -, -, -, hb⟩, -⟩ := hdet w hwb hwa 0
  exact hno y hs hb

/-! ### Necessity (ii): genericity and the dimension of the stable subspace -/

/-- **Non-uniqueness without genericity** (Woodford (2003), App. C.1, p. 672, fn. 2; Blanchard
and Kahn 1980): if a nonzero bounded orbit `Aᵗ v` starts with `x = 0`, then next to every
equilibrium there is another one (add the deterministic path `Aᵗ v`). -/
theorem mult_of_not_genericX [Nonempty Ω] {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} (h : ¬ GenericX A)
    {w : ℕ → Z ⊕ X → Ω → ℝ} {x0 : X → ℝ} {y : ℕ → Z ⊕ X → Ω → ℝ} (hy : Equil 𝔼 A w x0 y) :
    ∃ y', Equil 𝔼 A w x0 y' ∧ y' ≠ y := by
  unfold GenericX at h
  push Not at h
  obtain ⟨v, ⟨C, hC⟩, hvx, hv0⟩ := h
  obtain ⟨hs, ha, hk, h0, ⟨M, hM⟩⟩ := hy
  set y' : ℕ → Z ⊕ X → Ω → ℝ := fun t k => y t k + fun _ => (A ^ t *ᵥ v) k with hy'
  refine ⟨y', ⟨fun t k => ?_, fun t k => ?_, fun t j => ?_, fun j => ?_, ⟨M + C, ?_⟩⟩, ?_⟩
  · simp only [hy', map_add, 𝔼.const, hs t k]
    funext ω
    simp only [Pi.add_apply, mv_apply]
    rw [show (fun j => y t j ω + (A ^ t *ᵥ v) j) = (fun j => y t j ω) + A ^ t *ᵥ v from rfl,
      Matrix.mulVec_add, Pi.add_apply, Matrix.mulVec_mulVec, ← pow_succ']
    ring
  · simp only [hy', map_add, 𝔼.const, ha t k]
  · simp only [hy', map_add, 𝔼.const, hk t j]
  · simp only [hy', pow_zero, Matrix.one_mulVec, hvx j, h0 j]
    funext ω
    simp
  · intro t k ω
    exact (abs_add_le _ _).trans (add_le_add (hM t k ω) (hC t k))
  · intro he
    apply hv0
    funext k
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun (congrFun he 0) k) ω
    simpa [hy'] using this

/-- Woodford (2003), App. C.1, p. 672, fn. 2: without genericity the system is not
determinate (already for `w = 0`, `x_0 = 0` there are two equilibria). -/
theorem not_determinate_of_not_genericX [Nonempty Ω] {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (h : ¬ GenericX A) : ¬ Determinate 𝔼 A := by
  intro hdet
  have hb0 : BoundedV (0 : ℕ → Z ⊕ X → Ω → ℝ) := ⟨0, fun _ _ _ => by simp⟩
  have ha0 : AdaptedV 𝔼 (0 : ℕ → Z ⊕ X → Ω → ℝ) := fun t k => by simp
  obtain ⟨y, hy, huniq⟩ := hdet 0 hb0 ha0 0
  obtain ⟨y', hy', hne⟩ := mult_of_not_genericX 𝔼 h hy
  exact hne (huniq y' hy')

/-- **Non-existence with too few stable directions** (Woodford (2003), App. C.1, p. 670;
Blanchard and Kahn 1980): if the bounded-orbit subspace has dimension below the number of
predetermined variables, some initial `x_0` admits no equilibrium even with `w = 0`. Taking
`E_0` of an equilibrium gives, outcome by outcome, a bounded orbit starting at `(z_0, x_0)`. -/
theorem nonexist_of_lt [Nonempty Ω] {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (h : Module.finrank ℝ (boundedOrbits A) < Fintype.card X) :
    ∃ x0 : X → ℝ, ∀ y, ¬ Equil 𝔼 A 0 x0 y := by
  obtain ⟨x0, hx0⟩ := exists_unreached_of_lt h
  refine ⟨x0, fun y hy => ?_⟩
  obtain ⟨hs, -, -, h0, ⟨M, hM⟩⟩ := hy
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  set e : ℕ → Z ⊕ X → ℝ := fun t k => 𝔼.E 0 (y t k) ω₀ with he
  have hstep : ∀ t, e (t + 1) = A *ᵥ e t := by
    intro t
    funext k
    have e1 : 𝔼.E 0 (y (t + 1) k) = 𝔼.E 0 (𝔼.E t (y (t + 1) k)) :=
      (𝔼.tower (Nat.zero_le t) _).symm
    simp only [he]
    rw [e1, hs t k, Pi.zero_apply, Pi.zero_apply, add_zero, E_mv 𝔼, mv_apply]
  have hmem := mem_boundedOrbits_of_orbit hstep (fun t k => 𝔼.abs_E_le (hM t k) 0 ω₀)
  apply hx0 _ hmem
  funext j
  simp only [he, h0 j, 𝔼.const]

/-- Woodford (2003), App. C.1, p. 670: too few stable directions — not determinate. -/
theorem not_determinate_of_lt [Nonempty Ω] {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (h : Module.finrank ℝ (boundedOrbits A) < Fintype.card X) : ¬ Determinate 𝔼 A := by
  intro hdet
  obtain ⟨x0, hx0⟩ := nonexist_of_lt 𝔼 h
  obtain ⟨y, hy, -⟩ := hdet 0 ⟨0, fun _ _ _ => by simp⟩ (fun t k => by simp) x0
  exact hx0 y hy

/-- Woodford (2003), App. C.1, p. 672, fn. 2: too many stable directions — not determinate
(genericity must fail, so equilibria are not unique). -/
theorem not_determinate_of_gt [Nonempty Ω] {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (h : Fintype.card X < Module.finrank ℝ (boundedOrbits A)) : ¬ Determinate 𝔼 A :=
  not_determinate_of_not_genericX 𝔼 (not_genericX_of_lt h)

/-! ### The Blanchard–Kahn theorem -/

/-- **The Blanchard–Kahn theorem** (Woodford (2003), App. C.1, p. 670 and fn. 1–2, which the book
takes from Blanchard and Kahn (1980)): for any expectation system on a nonempty state space, the
system `E_t y_{t+1} = A y_t + w_t` with `|X|` predetermined variables is determinate iff
(i) no eigenvalue of `A` lies on the unit circle, (ii) the stable (bounded-orbit) subspace has
dimension `|X|`, and (iii) the stable subspace meets `{x = 0}` only in `0`. -/
theorem determinate_iff [Nonempty Ω] (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) :
    Determinate 𝔼 A ↔ NoUnit A ∧ Module.finrank ℝ (boundedOrbits A) = Fintype.card X ∧
      GenericX A := by
  constructor
  · intro hdet
    have hnu : NoUnit A := fun μ hμ h1 => not_determinate_of_unit 𝔼 hμ h1 hdet
    have hg : GenericX A := by
      by_contra hg
      exact not_determinate_of_not_genericX 𝔼 hg hdet
    refine ⟨hnu, ?_, hg⟩
    rcases lt_trichotomy (Module.finrank ℝ (boundedOrbits A)) (Fintype.card X) with h | h | h
    · exact absurd hdet (not_determinate_of_lt 𝔼 h)
    · exact h
    · exact absurd hdet (not_determinate_of_gt 𝔼 h)
  · rintro ⟨hnu, hd, hg⟩
    exact determinate_of 𝔼 hnu hd hg

/-- **The Blanchard–Kahn counting rule** (Woodford (2003), App. C.1, p. 670 and fn. 1–2; Blanchard
and Kahn 1980): determinate iff no eigenvalue on the unit circle, exactly `|X|` eigenvalues in the
open unit disc counted with algebraic multiplicity, and genericity. -/
theorem determinate_iff_count [Nonempty Ω] (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) :
    Determinate 𝔼 A ↔ NoUnit A ∧ stableCount A = Fintype.card X ∧ GenericX A := by
  rw [determinate_iff]
  constructor
  · rintro ⟨hnu, hd, hg⟩
    exact ⟨hnu, (finrank_eq_iff_stableCount_eq hnu hg).mp hd, hg⟩
  · rintro ⟨hnu, hc, hg⟩
    exact ⟨hnu, (finrank_eq_iff_stableCount_eq hnu hg).mpr hc, hg⟩

/-- **The Blanchard–Kahn counting rule, unstable form** (Woodford (2003), App. C.1, p. 670;
Blanchard and Kahn 1980): determinate iff no eigenvalue on the unit circle, exactly as many
eigenvalues outside the unit circle (with multiplicity) as non-predetermined variables, and
genericity. -/
theorem determinate_iff_unstableCount [Nonempty Ω] (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) :
    Determinate 𝔼 A ↔ NoUnit A ∧ unstableCount A = Fintype.card Z ∧ GenericX A := by
  rw [determinate_iff_count]
  constructor
  · rintro ⟨hnu, hc, hg⟩
    refine ⟨hnu, ?_, hg⟩
    have := stableCount_add_unstableCount hnu
    rw [Fintype.card_sum, hc] at this
    omega
  · rintro ⟨hnu, hc, hg⟩
    refine ⟨hnu, ?_, hg⟩
    have := stableCount_add_unstableCount hnu
    rw [Fintype.card_sum, hc] at this
    omega

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 670: determinacy does not depend on the expectation system —
it holds under any expectation system on a nonempty state space iff it holds under perfect
foresight. -/
theorem determinate_iff_perfectForesight [Nonempty Ω] (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) :
    Determinate 𝔼 A ↔ Determinate perfectForesight A := by
  classical
  rw [determinate_iff, determinate_iff]

/-! ### The bounded-orbit subspace is the stable subspace -/

/-- Woodford (2003), App. C.1, p. 670 (tool): a vector whose orbit tends to `0` has a bounded
orbit. -/
theorem mem_boundedOrbits_of_tendsto {A : Matrix κ κ ℝ} {v : κ → ℝ}
    (h : Tendsto (fun t => A ^ t *ᵥ v) atTop (𝓝 0)) : v ∈ boundedOrbits A := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto (fun t => A ^ t *ᵥ v) h)
  exact ⟨C, fun t i => (norm_le_pi_norm (A ^ t *ᵥ v) i).trans (hC _ ⟨t, rfl⟩) |>.trans' le_rfl⟩

/-- Woodford (2003), App. C.1, p. 670 (Blanchard and Kahn 1980): with no eigenvalue on the unit
circle, the bounded-orbit subspace is exactly the stable subspace `{v : Aᵗ v → 0}`. -/
theorem mem_boundedOrbits_iff_tendsto_of_noUnit {A : Matrix κ κ ℝ} (hnu : NoUnit A)
    (v : κ → ℝ) : v ∈ boundedOrbits A ↔ Tendsto (fun t => A ^ t *ᵥ v) atTop (𝓝 0) :=
  ⟨tendsto_of_mem_boundedOrbits hnu, mem_boundedOrbits_of_tendsto⟩

/-- Woodford (2003), App. C.1, p. 670 (Blanchard and Kahn 1980): under the Blanchard–Kahn
conditions every bounded orbit tends to `0` — the bounded-orbit subspace is exactly the stable
subspace `{v : Aᵗ v → 0}`. -/
theorem mem_boundedOrbits_iff_tendsto {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} (hnu : NoUnit A)
    (hd : Module.finrank ℝ (boundedOrbits A) = Fintype.card X) (hg : GenericX A)
    (v : Z ⊕ X → ℝ) :
    v ∈ boundedOrbits A ↔ Tendsto (fun t => A ^ t *ᵥ v) atTop (𝓝 0) := by
  refine ⟨fun hv => ?_, mem_boundedOrbits_of_tendsto⟩
  obtain ⟨G, hG⟩ := exists_graph hd hg
  have hinv := graph_invariant hG
  obtain ⟨Cb, ρ, hCb, hρ0, hρ1, hL⟩ := pow_entry_bound _ (lam_stable hG hnu)
  set x : X → ℝ := fun j => v (Sum.inr j) with hx
  have hvg : v = graphV G x := by
    funext k
    rcases k with i | j
    · exact hG.2 v hv i
    · rfl
  set Xb : ℝ := ∑ j, |x j| with hXb
  have hXb0 : 0 ≤ Xb := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hxj : ∀ j, |x j| ≤ Xb := fun j =>
    Finset.single_le_sum (f := fun j => |x j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  set aG : ℝ := ∑ i, ∑ j, |G i j| with haG
  have hLx : ∀ t j, |(lam A G ^ t *ᵥ x) j| ≤ Fintype.card X * (Cb * ρ ^ t * Xb) :=
    fun t j => InvariantSplit.abs_mulVec_le _ _ (hL t) hxj j
  have hlim : Tendsto (fun t : ℕ => (Fintype.card X : ℝ) * (Cb * ρ ^ t * Xb)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).const_mul Cb).mul_const Xb
    simpa using this.const_mul (Fintype.card X : ℝ)
  have hlim2 : Tendsto (fun t : ℕ => (Fintype.card X : ℝ) *
      (aG * ((Fintype.card X : ℝ) * (Cb * ρ ^ t * Xb)))) atTop (𝓝 0) := by
    simpa using (hlim.const_mul aG).const_mul (Fintype.card X : ℝ)
  rw [hvg, tendsto_pi_nhds]
  intro k
  simp only [pow_mulVec_graphV hinv]
  rcases k with i | j
  · refine squeeze_zero_norm (fun t => ?_) hlim2
    rw [Real.norm_eq_abs]
    exact InvariantSplit.abs_mulVec_le G _ (abs_entry_le_sum G) (hLx t) i
  · refine squeeze_zero_norm (fun t => ?_) hlim
    rw [Real.norm_eq_abs]
    exact hLx t j

end Gali.BasicNewKeynesianModel.GeneralBK
