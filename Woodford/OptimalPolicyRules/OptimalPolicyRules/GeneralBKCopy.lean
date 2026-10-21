/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.BKForward

/-!
# The general Blanchard–Kahn theorem (sufficiency), with random initial conditions

Woodford (2003), *Interest and Prices*, Appendix C.1, p. 670 (Props. C.1, C.2 and footnotes
1–2; Blanchard and Kahn 1980). Restated from the Woodford Chapter 4 project
(`NeoWicksellianFramework.GeneralBK`, the sufficiency half `determinate_of` and its tools), with
the namespace renamed and one generalisation needed in Chapter 8: the initial value `x₀` of the
predetermined block is a **random vector known at date `0` and bounded** (the Chapter 4 version
takes a deterministic `x₀`, the case of a constant random vector).

## Setting

The state is `y_t = (z_t, x_t)` with index type `Z ⊕ X`: `z_t` non-predetermined, `x_t`
predetermined. `E_t y_{t+1} = A y_t + w_t` (`Solves`) for a real matrix `A`; an equilibrium
(`Equil`) is a bounded adapted solution whose predetermined block `x_{t+1}` is known at date `t`
and starts at the given `x_0`. `Determinate`: for every bounded adapted forcing `w` and every
bounded `x_0` known at date `0` there is exactly one equilibrium.

## Main results

* `determinate_of` (**sufficiency**, any `ExpectationSystem`): no eigenvalue of `A` on the unit
  circle (`NoUnit`), the bounded-orbit (stable) subspace of dimension `|X|`, and genericity
  (`GenericX`: the stable subspace meets `{x = 0}` only in `0`) imply determinacy. Proof: the
  stable subspace is the graph of `G` (`BKInvariantSplit.exists_graph`); `ẑ_t = z_t − G x_t`
  solves `E_t ẑ_{t+1} = C ẑ_t + ŵ_t` with all eigenvalues of `C` outside the closed disc, so it is
  the forward solution through `C⁻¹`; then `x_{t+1} = Λ x_t + A_xz ẑ_t + w^x_t` with `Λ` stable is
  solved backward from `x_0`.
-/

namespace Woodford.OptimalPolicyRules.GeneralBKCopy

open Filter Topology BKInvariantSplit BKForward
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
`x_0` is the given random vector (restated from the Woodford Chapter 4 project, with a random
`x_0`). -/
def Equil (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (w : ℕ → Z ⊕ X → Ω → ℝ) (x0 : X → Ω → ℝ)
    (y : ℕ → Z ⊕ X → Ω → ℝ) : Prop :=
  Solves 𝔼 A w y ∧ AdaptedV 𝔼 y ∧
    (∀ t j, 𝔼.E t (y (t + 1) (Sum.inr j)) = y (t + 1) (Sum.inr j)) ∧
    (∀ j, y 0 (Sum.inr j) = x0 j) ∧ BoundedV y

/-- Woodford (2003), App. C.1, p. 670 (determinacy, Blanchard and Kahn 1980): for every bounded
adapted forcing and every bounded initial value of the predetermined variables known at date `0`
there is exactly one bounded equilibrium (restated from the Woodford Chapter 4 project, with a
random `x_0`). -/
def Determinate (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) : Prop :=
  ∀ w : ℕ → Z ⊕ X → Ω → ℝ, BoundedV w → AdaptedV 𝔼 w → ∀ x0 : X → Ω → ℝ,
    (∀ j, 𝔼.E 0 (x0 j) = x0 j) → (∃ K, ∀ j ω, |x0 j ω| ≤ K) → ∃! y, Equil 𝔼 A w x0 y

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
def xrecR (L : Matrix X X ℝ) (g : ℕ → X → Ω → ℝ) (x0 : X → Ω → ℝ) : ℕ → X → Ω → ℝ
  | 0 => x0
  | t + 1 => mv L (xrecR L g x0 t) + g t

omit [DecidableEq Z] in
/-- Woodford (2003), App. C.1, p. 672: the backward recursion is bounded when `Λ` is stable and
`g` and `x_0` are bounded. -/
theorem xrecR_bounded {L : Matrix X X ℝ} (hL : ∀ μ ∈ eigs L, ‖μ‖ < 1) {g : ℕ → X → Ω → ℝ}
    (hg : BoundedV g) {x0 : X → Ω → ℝ} (hx0 : ∃ K, ∀ j ω, |x0 j ω| ≤ K) :
    BoundedV (xrecR L g x0) := by
  obtain ⟨Cb, ρ, hCb, hρ0, hρ1, hLp⟩ := pow_entry_bound L hL
  obtain ⟨F, hF⟩ := hg
  obtain ⟨K, hK⟩ := hx0
  refine ⟨Fintype.card X * Cb * (max K 0 + max F 0 / (1 - ρ)), fun t j ω => ?_⟩
  have hrec : ∀ t, (fun j => xrecR L g x0 (t + 1) j ω) =
      L *ᵥ (fun j => xrecR L g x0 t j ω) + fun j => g t j ω := by
    intro t
    funext j
    simp only [xrecR, Pi.add_apply, mv_apply]
  exact rec_bounded (x := fun t j => xrecR L g x0 t j ω) (f := fun t j => g t j ω) hCb hρ0.le
    hρ1 hLp hrec (le_max_right _ _) (le_max_right _ _)
    (fun t j => (hF t j ω).trans (le_max_left _ _))
    (fun j => (hK j ω).trans (le_max_left _ _)) t j

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672: the backward recursion is known one period ahead:
`x_t` is known at `t` and so is `x_{t+1}` (when `g` is adapted). -/
theorem xrecR_known {L : Matrix X X ℝ} {g : ℕ → X → Ω → ℝ} (hg : AdaptedV 𝔼 g) {x0 : X → Ω → ℝ}
    (hx0 : ∀ j, 𝔼.E 0 (x0 j) = x0 j) :
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
    | zero => exact hx0
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
meets `{x = 0}` only in `0`, then for every bounded adapted forcing and every bounded `x_0` known
at date `0` there is exactly one bounded equilibrium (restated from the Woodford Chapter 4
project, with a random `x_0`). -/
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
  intro w hwb hwa x0 hx0k hx0b
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
  have hxrb : BoundedV xr := xrecR_bounded hΛ hgb hx0b
  have hxrK := xrecR_known 𝔼 (L := lam A G) hgA hx0k
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
end Woodford.OptimalPolicyRules.GeneralBKCopy
