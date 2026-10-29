/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR6aBKRandom
import OptimalPolicyRules.OptimalRulesMeasureMultiplicity
import OptimalPolicyRules.InertiaAssumption81

/-!
# Blanchard–Kahn determinacy of the stacked system (1.1) + (1.9)

Woodford (2003), *Interest and Prices*, Chapter 8, (1.1) (p. 537), the first-order conditions
(1.9) (p. 541), Assumption 8.1 (p. 541), with Appendix C.1 (p. 670).

Stack the plan and the multipliers, `x_t = (y_t, φ_t)`, `y_t = (Z_t, z_t, i_t)`,
`φ_t = (ξ_t, M_{t−1})`. Then (1.1) + (1.9) is the pencil system
`F E_t x_{t+1} = G x_t + w_t` with `F = [[0, Ã'], [Ĩ, 0]]` and `G = [[−T'WT, β⁻¹Ĩ'], [Ã, 0]]`
(`OptimalRulesMeasureEulerPencil.Fm`, `Gm`), forcing `w_t = (T'Wτ*, (0, c_t))`, predetermined
variables `(Z_t, M_{t−1})`. `F` is singular (it has zero rows for the instrument and zero
columns for the `ξ`'s), so the system is not in Blanchard–Kahn form; the singular-pencil theorem
(King–Watson, Klein; `TidyR6aBKRandom.determinatePencilR_iff_general`) applies.

* `eS`, `A0`, `A1`: the stacked state reordered as (non-predetermined `(z, i, ξ)`, predetermined
  `(Z, M)`), and `F`, `G` in that order; `stk`, `wS`, `x0S` the stacked plan, forcing and initial
  condition.
* `pencilPoly_map`: `det(λA₀ − A₁)` is the Euler polynomial
  `OptimalRulesMeasureEulerPencil.eulerPoly` (over `ℂ`).
* `focSystem_of_equil`, `equil_of_focSystem`: at `t₀ = 0` the bounded solutions of (1.1) + (1.9)
  (`GeneralFOC.LQ.FOCSystem`) are exactly the equilibria of the stacked pencil system.
* **`stack_determinate_iff_count`**: for any expectation system on a nonempty sample space the
  stacked system is determinate iff the Euler polynomial is nonzero, has no root on the unit
  circle, has exactly `n = n_Z + n_z` roots (with multiplicity) in the open unit disc, and the
  genericity condition holds.
* `assumption81MB_of_determinate`: stacked determinacy gives the (corrected) Assumption 8.1 for
  every expectation system.
* `determinate_of_assumption81`: conversely the perfect-foresight Assumption 8.1 plus no Euler root
  on the unit circle give stacked determinacy under every expectation system; the count is
  `OptimalRulesMeasureMultiplicity.card_closedDisk_eq` (closed disc = open disc), and genericity
  comes from the uniqueness half of Assumption 8.1.
* **`stack_determinate_iff`**: stacked determinacy ⟺ perfect-foresight Assumption 8.1 ∧ no root of
  the Euler pencil on the unit circle; `stack_determinate_card`: then exactly `n` roots lie in the
  closed (= open) unit disc, the count `OptimalRulesMeasureMultiplicity.card_closedDisk_eq`.
* `eB_not_determinate`: Assumption 8.1 alone does **not** give Blanchard–Kahn determinacy of the
  stacked system: the problem `OptimalRulesMeasureCounterexample.eBP` satisfies the
  perfect-foresight Assumption 8.1 but its Euler pencil has the root `1`.
-/

namespace Woodford.OptimalPolicyRules.TidyR6aStackedBK

open Matrix Polynomial GeneralSetup GeneralFOC GeneralFOC.LQ OptimalRulesMeasureEulerPencil
open OptimalRulesMeasureSpectrum TidyR6aGeneralBKPencil TidyR6aGeneralBKSingular TidyR6aBKRandom

variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-! ### The stacked system in Blanchard–Kahn order -/

/-- Woodford (2003), (1.1) + (1.9) (tool): the stacked coordinates `x = (y, φ)`,
`y = ((Z, z), i)`, `φ = (ξ, M)`, reordered as (non-predetermined `((z, i), ξ)`, predetermined
`(Z, M)`). -/
def eSf : ((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz) → ((ιz ⊕ Unit) ⊕ ιZ) ⊕ (ιZ ⊕ ιz)
  | Sum.inl (Sum.inl (Sum.inl j)) => Sum.inr (Sum.inl j)
  | Sum.inl (Sum.inl (Sum.inr r)) => Sum.inl (Sum.inl (Sum.inl r))
  | Sum.inl (Sum.inr u) => Sum.inl (Sum.inl (Sum.inr u))
  | Sum.inr (Sum.inl j) => Sum.inl (Sum.inr j)
  | Sum.inr (Sum.inr r) => Sum.inr (Sum.inr r)

/-- Woodford (2003), (1.1) + (1.9) (tool): the inverse reordering. -/
def eSi : ((ιz ⊕ Unit) ⊕ ιZ) ⊕ (ιZ ⊕ ιz) → ((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz)
  | Sum.inl (Sum.inl (Sum.inl r)) => Sum.inl (Sum.inl (Sum.inr r))
  | Sum.inl (Sum.inl (Sum.inr u)) => Sum.inl (Sum.inr u)
  | Sum.inl (Sum.inr j) => Sum.inr (Sum.inl j)
  | Sum.inr (Sum.inl j) => Sum.inl (Sum.inl (Sum.inl j))
  | Sum.inr (Sum.inr r) => Sum.inr (Sum.inr r)

/-- Woodford (2003), (1.1) + (1.9) (tool): the reordering as an equivalence. -/
def eS : ((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz) ≃ ((ιz ⊕ Unit) ⊕ ιZ) ⊕ (ιZ ⊕ ιz) where
  toFun := eSf
  invFun := eSi
  left_inv := by rintro (((j | r) | u) | (j | r)) <;> rfl
  right_inv := by rintro (((r | u) | j) | (j | r)) <;> rfl

/-- Woodford (2003), (1.1) + (1.9): the lead matrix `F` in Blanchard–Kahn order. -/
def A0 (P : LQProblem ιZ ιz ιτ) : Matrix (((ιz ⊕ Unit) ⊕ ιZ) ⊕ (ιZ ⊕ ιz))
    (((ιz ⊕ Unit) ⊕ ιZ) ⊕ (ιZ ⊕ ιz)) ℝ :=
  reindex eS eS (Fm P)

/-- Woodford (2003), (1.1) + (1.9): the current-date matrix `G` in Blanchard–Kahn order. -/
noncomputable def A1 (P : LQProblem ιZ ιz ιτ) : Matrix (((ιz ⊕ Unit) ⊕ ιZ) ⊕ (ιZ ⊕ ιz))
    (((ιz ⊕ Unit) ⊕ ιZ) ⊕ (ιZ ⊕ ιz)) ℝ :=
  reindex eS eS (Gm P)

variable {Ω : Type*}

/-- Woodford (2003), (1.1) + (1.9): the stacked process `x_t = (y_t, φ_t)` in Blanchard–Kahn
order. -/
def stk (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ) :
    ℕ → ((ιz ⊕ Unit) ⊕ ιZ) ⊕ (ιZ ⊕ ιz) → Ω → ℝ :=
  fun t k ω => Sum.elim (y t ω) (φ t ω) (eS.symm k)

/-- Woodford (2003), (1.1) + (1.9): the forcing `w_t = (T'Wτ*, (0, c_t))` of the stacked system
(rows: the first-order conditions, then the structural equations). -/
def wS (P : LQProblem ιZ ιz ιτ) (c : ℕ → Ω → ιz → ℝ) :
    ℕ → ((ιz ⊕ Unit) ⊕ ιZ) ⊕ (ιZ ⊕ ιz) → Ω → ℝ :=
  fun t k ω => Sum.elim (P.Tᵀ *ᵥ (P.W *ᵥ P.τstar)) (liftDist c t ω) (eS.symm k)

/-- Woodford (2003), p. 541: the initial condition `(Z_0, M_{−1}) = (Z₀, M₀)` of the stacked
system. -/
def x0S (Z0 : Ω → ιZ → ℝ) (M0 : Ω → ιz → ℝ) : ιZ ⊕ ιz → Ω → ℝ :=
  fun k ω => Sum.elim (Z0 ω) (M0 ω) k

/-! ### The pointwise equations -/

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), (1.1) + (1.9) (tool): blockwise addition of stacked vectors. -/
theorem elim_add {α β : Type*} (a c : α → ℝ) (b d : β → ℝ) :
    Sum.elim a b + Sum.elim c d = Sum.elim (a + c) (b + d) := by
  funext x
  rcases x with x | x <;> rfl

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), (1.1) + (1.9) (tool): stacked vectors are equal iff their blocks are. -/
theorem elim_eq_iff {α β : Type*} (a c : α → ℝ) (b d : β → ℝ) :
    Sum.elim a b = Sum.elim c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨funext fun x => congrFun h (Sum.inl x), funext fun x => congrFun h (Sum.inr x)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Woodford (2003), (1.1) + (1.9), pointwise: `F e = G x + w` iff the first-order conditions
(1.9) and the structural rows `Ĩ e_y = Ã y + (0, c)` hold. -/
theorem pencil_pt_iff (P : LQProblem ιZ ιz ιτ) (ey yv : (ιZ ⊕ ιz) ⊕ Unit → ℝ)
    (eφ φv : ιZ ⊕ ιz → ℝ) (cv : ιz → ℝ) :
    Fm P *ᵥ Sum.elim ey eφ = Gm P *ᵥ Sum.elim yv φv +
        Sum.elim (P.Tᵀ *ᵥ (P.W *ᵥ P.τstar)) (Sum.elim (0 : ιZ → ℝ) cv) ↔
      (P.sys.Atilᵀ *ᵥ eφ + P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ yv - P.τstar)) -
          P.β⁻¹ • (P.sys.Itilᵀ *ᵥ φv) = 0) ∧
        P.sys.Itil *ᵥ ey = P.sys.Atil *ᵥ yv + Sum.elim (0 : ιZ → ℝ) cv := by
  have hq : P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ yv - P.τstar)) =
      Qmat P *ᵥ yv - P.Tᵀ *ᵥ (P.W *ᵥ P.τstar) := by
    rw [Qmat, mulVec_sub, mulVec_sub, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  simp only [Fm, Gm, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec,
    zero_add, add_zero, elim_add, elim_eq_iff]
  rw [hq, neg_mulVec, smul_mulVec]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [h1]
    abel
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [← sub_eq_zero, ← h1]
    abel

omit [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), (1.1) + (1.9) (tool): the reordered matrix acting on a reordered vector. -/
theorem reindex_mulVec_eS (M : Matrix (((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz))
    (((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz)) ℝ) (v : ((ιz ⊕ Unit) ⊕ ιZ) ⊕ (ιZ ⊕ ιz) → ℝ)
    (ρ : ((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz)) :
    (reindex eS eS M *ᵥ v) (eS ρ) = (M *ᵥ (v ∘ eS)) ρ := by
  rw [reindex_apply, submatrix_mulVec_equiv]
  simp [Function.comp_def]

/-! ### Solutions of the stacked system -/

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), (1.1) + (1.9) (tool): the stacked process read back in the original
coordinates. -/
theorem stk_eS (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ) (t : ℕ)
    (σ : ((ιZ ⊕ ιz) ⊕ Unit) ⊕ (ιZ ⊕ ιz)) :
    stk y φ t (eS σ) = fun ω => Sum.elim (y t ω) (φ t ω) σ := by
  funext ω
  simp [stk]

/-- Woodford (2003), (1.1) + (1.9) on the stacked process: `x = (y, φ)` solves the pencil system
`F E_t x_{t+1} = G x_t + w_t` iff, at every date and state, the first-order conditions (1.9) and
the structural rows `Ĩ E_t y_{t+1} = Ã y_t + (0, c_t)` hold. -/
theorem solvesPencil_stk_iff (𝔼 : ExpectationSystem Ω) (P : LQProblem ιZ ιz ιτ)
    (c : ℕ → Ω → ιz → ℝ) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ) :
    SolvesPencil 𝔼 (A0 P) (A1 P) (wS P c) (stk y φ) ↔ ∀ t ω,
      (P.sys.Atilᵀ *ᵥ EV 𝔼 t (φ (t + 1)) ω + P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ y t ω - P.τstar)) -
          P.β⁻¹ • (P.sys.Itilᵀ *ᵥ φ t ω) = 0) ∧
        P.sys.Itil *ᵥ EV 𝔼 t (y (t + 1)) ω =
          P.sys.Atil *ᵥ y t ω + Sum.elim (0 : ιZ → ℝ) (c t ω) := by
  have hE : ∀ t ω, (fun k => 𝔼.E t (stk y φ (t + 1) k) ω) ∘ eS =
      Sum.elim (EV 𝔼 t (y (t + 1)) ω) (EV 𝔼 t (φ (t + 1)) ω) := by
    intro t ω
    funext σ
    simp only [Function.comp_apply, stk_eS]
    rcases σ with a | b <;> rfl
  have hX : ∀ t ω, (fun k => stk y φ t k ω) ∘ eS = Sum.elim (y t ω) (φ t ω) := by
    intro t ω
    funext σ
    simp only [Function.comp_apply, stk_eS]
  have hW : ∀ t ω σ, wS P c t (eS σ) ω =
      Sum.elim (P.Tᵀ *ᵥ (P.W *ᵥ P.τstar)) (liftDist c t ω) σ := by
    intro t ω σ
    simp [wS]
  have key : ∀ t ω, (∀ σ, BKForward.mv (A0 P) (fun i => 𝔼.E t (stk y φ (t + 1) i)) (eS σ) ω =
      (BKForward.mv (A1 P) (stk y φ t) + wS P c t) (eS σ) ω) ↔
      Fm P *ᵥ Sum.elim (EV 𝔼 t (y (t + 1)) ω) (EV 𝔼 t (φ (t + 1)) ω) =
        Gm P *ᵥ Sum.elim (y t ω) (φ t ω) +
          Sum.elim (P.Tᵀ *ᵥ (P.W *ᵥ P.τstar)) (liftDist c t ω) := by
    intro t ω
    simp only [Pi.add_apply, BKForward.mv_apply, A0, A1, reindex_mulVec_eS, hE, hX, hW]
    constructor
    · intro h
      funext σ
      exact h σ
    · intro h σ
      exact congrFun h σ
  unfold SolvesPencil
  constructor
  · intro h t ω
    have h1 := (key t ω).mp fun σ => congrFun (congrFun (h t) (eS σ)) ω
    exact (pencil_pt_iff P _ _ _ _ _).mp h1
  · intro h t
    funext k ω
    obtain ⟨σ, rfl⟩ := eS.surjective k
    exact (key t ω).mpr ((pencil_pt_iff P _ _ _ _ _).mpr (h t ω)) σ

/-! ### Information -/

/-- Woodford (2003), p. 540 (tool): with the first-order conditions (1.9) at date `t` and `y_t`
known at `t`, the multipliers `ξ_t` on the predetermined rows are known at `t`
(`ξ_t = β (Ã'E_tφ_{t+1} + T'W(τ_t − τ*))_Z`). -/
theorem xi_known (𝔼 : ExpectationSystem Ω) (P : LQProblem ιZ ιz ιτ)
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ} {t : ℕ}
    (hfoc : ∀ ω, P.sys.Atilᵀ *ᵥ EV 𝔼 t (φ (t + 1)) ω +
      P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ y t ω - P.τstar)) - P.β⁻¹ • (P.sys.Itilᵀ *ᵥ φ t ω) = 0)
    (hy : KnownV 𝔼 t (y t)) (j : ιZ) :
    𝔼.E t (fun ω => φ t ω (Sum.inl j)) = fun ω => φ t ω (Sum.inl j) := by
  set g : Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ := fun ω => P.sys.Atilᵀ *ᵥ EV 𝔼 t (φ (t + 1)) ω +
    ((P.Tᵀ * P.W * P.T) *ᵥ y t ω + -(P.Tᵀ *ᵥ (P.W *ᵥ P.τstar))) with hgdef
  have hb : KnownV 𝔼 t (fun ω => (P.Tᵀ * P.W * P.T) *ᵥ y t ω + -(P.Tᵀ *ᵥ (P.W *ᵥ P.τstar))) :=
    PencilSplit.knownV_mulVec_add 𝔼 _ hy (fun _ => 𝔼.const t _)
  have hg : KnownV 𝔼 t g := PencilSplit.knownV_mulVec_add 𝔼 _ (PencilSplit.knownV_EV 𝔼 t _) hb
  have hφ : (fun ω => φ t ω (Sum.inl j)) = P.β • fun ω => g ω (Sum.inl (Sum.inl j)) := by
    funext ω
    have h0 := hfoc ω
    have hT : P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ y t ω - P.τstar)) =
        (P.Tᵀ * P.W * P.T) *ᵥ y t ω + -(P.Tᵀ *ᵥ (P.W *ᵥ P.τstar)) := by
      rw [mulVec_sub, mulVec_sub, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc,
        sub_eq_add_neg]
    rw [hT, sub_eq_zero, ← add_assoc] at h0
    have h1 := congrFun h0 (Sum.inl (Sum.inl j))
    rw [Itil_transpose_mulVec, Pi.smul_apply, Sum.elim_inl, PencilSplit.Ihat_transpose_mulVec,
      Sum.elim_inl] at h1
    simp only [Pi.smul_apply, smul_eq_mul, hgdef, ← add_assoc]
    rw [h1, Function.comp_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ P.β_pos.ne', one_mul]
  rw [hφ, map_smul, hg (Sum.inl (Sum.inl j))]

/-! ### Solutions of (1.1) + (1.9) are the equilibria of the stacked system -/

/-- Woodford (2003), (1.1) + (1.9) (tool): the plan `y` read off a stacked process. -/
def unY (x : ℕ → ((ιz ⊕ Unit) ⊕ ιZ) ⊕ (ιZ ⊕ ιz) → Ω → ℝ) :
    ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ :=
  fun t ω a => x t (eS (Sum.inl a)) ω

/-- Woodford (2003), (1.1) + (1.9) (tool): the multipliers `φ` read off a stacked process. -/
def unΦ (x : ℕ → ((ιz ⊕ Unit) ⊕ ιZ) ⊕ (ιZ ⊕ ιz) → Ω → ℝ) : ℕ → Ω → ιZ ⊕ ιz → ℝ :=
  fun t ω b => x t (eS (Sum.inr b)) ω

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), (1.1) + (1.9) (tool): stacking what was read off gives back the process. -/
theorem stk_un (x : ℕ → ((ιz ⊕ Unit) ⊕ ιZ) ⊕ (ιZ ⊕ ιz) → Ω → ℝ) :
    stk (unY x) (unΦ x) = x := by
  funext t k ω
  obtain ⟨σ, rfl⟩ := eS.surjective k
  rw [stk_eS]
  rcases σ with a | b <;> rfl

omit [Fintype ιτ] in
/-- Woodford (2003), eq. (1.1), p. 537 (tool): when `Z_{t+1}` is known at `t`, the stacked
structural rows `Ĩ E_t y_{t+1} = Ã y_t + (0, c_t)` are (1.1) at `(t, ω)`. -/
theorem struct_pt_iff (𝔼 : ExpectationSystem Ω) (S : LinearRESystem ιZ ιz)
    (c : ℕ → Ω → ιz → ℝ) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (t : ℕ)
    (hZ : KnownV 𝔼 t (fun ω => Zpart (y (t + 1) ω))) (ω : Ω) :
    S.Itil *ᵥ EV 𝔼 t (y (t + 1)) ω = S.Atil *ᵥ y t ω + Sum.elim (0 : ιZ → ℝ) (c t ω) ↔
      Zpart (y (t + 1) ω) = S.A11 *ᵥ Zpart (y t ω) + S.A12 *ᵥ zpart (y t ω) ∧
        S.Et *ᵥ EV 𝔼 t (fun ω' => zpart (y (t + 1) ω')) ω =
          S.A21 *ᵥ Zpart (y t ω) + S.A22 *ᵥ zpart (y t ω) + ipart (y t ω) • S.B2 + c t ω := by
  have hE : Zpart (EV 𝔼 t (y (t + 1)) ω) = Zpart (y (t + 1) ω) :=
    congrFun (EV_of_known 𝔼 hZ) ω
  rw [S.Itil_mulVec, S.Atil_mulVec, elim_add, elim_eq_iff, hE, add_zero]
  rfl

/-- Woodford (2003), pp. 541–542 and App. C.1 (tool): a bounded solution of (1.1) + (1.9) from
`t₀ = 0` solves the stacked pencil system, is bounded, has its predetermined block known one
period ahead, starts at `(Z₀, M₀)`, and is adapted except possibly for `M_{−1} = M₀` at date `0`. -/
theorem focSystem_pre (𝔼 : ExpectationSystem Ω) (P : LQProblem ιZ ιz ιτ)
    {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h : FOCSystem P 𝔼 c 0 Z0 M0 y φ) :
    SolvesPencil 𝔼 (A0 P) (A1 P) (wS P c) (stk y φ) ∧
      (∀ t σ, (0 < t ∨ ∀ r, σ ≠ Sum.inr (Sum.inr r)) →
        𝔼.E t (stk y φ t (eS σ)) = stk y φ t (eS σ)) ∧
      (∀ t j, 𝔼.E t (stk y φ (t + 1) (Sum.inr j)) = stk y φ (t + 1) (Sum.inr j)) ∧
      (∀ j, stk y φ 0 (Sum.inr j) = x0S Z0 M0 j) ∧ BKForward.BoundedV (stk y φ) := by
  obtain ⟨⟨hst, hZ0, hyb, hya⟩, hφb, hmm, hM0eq, hfoc⟩ := h
  have hZk : ∀ t, KnownV 𝔼 t (fun ω => Zpart (y (t + 1) ω)) := by
    intro t
    have e : (fun ω => Zpart (y (t + 1) ω)) =
        fun ω => P.sys.A11 *ᵥ Zpart (y t ω) + P.sys.A12 *ᵥ zpart (y t ω) :=
      funext fun ω => (hst t (Nat.zero_le t) ω).1
    rw [e]
    exact PencilSplit.knownV_mulVec_add 𝔼 _ (fun j => hya t (Sum.inl (Sum.inl j)))
      (PencilSplit.knownV_mulVec 𝔼 _ (fun r => hya t (Sum.inl (Sum.inr r))))
  refine ⟨(solvesPencil_stk_iff 𝔼 P c y φ).mpr fun t ω =>
      ⟨hfoc t (Nat.zero_le t) ω,
        (struct_pt_iff 𝔼 P.sys c y t (hZk t) ω).mpr (hst t (Nat.zero_le t) ω)⟩,
    fun t σ hσ => ?_, fun t j => ?_, fun j => ?_, ?_⟩
  · rw [stk_eS]
    rcases σ with a | (j | r)
    · exact hya t a
    · exact xi_known 𝔼 P (hfoc t (Nat.zero_le t)) (hya t) j
    · rcases t with _ | s
      · rcases hσ with h0 | h0
        · exact absurd h0 (lt_irrefl 0)
        · exact absurd rfl (h0 r)
      · change 𝔼.E (s + 1) (fun ω => φ (s + 1) ω (Sum.inr r)) = fun ω => φ (s + 1) ω (Sum.inr r)
        rw [← hmm s r, 𝔼.known (Nat.le_succ s)]
  · rcases j with j | r
    · exact hZk t j
    · exact hmm t r
  · rcases j with j | r
    · funext ω
      exact congrFun (hZ0 ω) j
    · funext ω
      exact congrFun (hM0eq ω) r
  · obtain ⟨K1, h1⟩ := hyb
    obtain ⟨K2, h2⟩ := hφb
    refine ⟨max K1 K2, fun t k ω => ?_⟩
    obtain ⟨σ, rfl⟩ := eS.surjective k
    rw [stk_eS]
    rcases σ with a | b
    · exact (h1 t ω a).trans (le_max_left _ _)
    · exact (h2 t ω b).trans (le_max_right _ _)

/-- Woodford (2003), pp. 541–542 and App. C.1 (**solutions are equilibria**): a bounded solution
of (1.1) + (1.9) from `t₀ = 0` with `M_{−1} = M₀` known at date `0` is a bounded equilibrium of
the stacked pencil system with initial condition `(Z₀, M₀)`. -/
theorem equil_of_focSystem (𝔼 : ExpectationSystem Ω) (P : LQProblem ιZ ιz ιτ)
    {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h : FOCSystem P 𝔼 c 0 Z0 M0 y φ) (hM0 : KnownV 𝔼 0 M0) :
    EquilPencilR 𝔼 (A0 P) (A1 P) (wS P c) (x0S Z0 M0) (stk y φ) := by
  obtain ⟨hs, ha, hp, hi, hb⟩ := focSystem_pre 𝔼 P h
  refine ⟨hs, fun t k => ?_, hp, hi, hb⟩
  obtain ⟨σ, rfl⟩ := eS.surjective k
  by_cases hσ : 0 < t ∨ ∀ r, σ ≠ Sum.inr (Sum.inr r)
  · exact ha t σ hσ
  · push Not at hσ
    obtain ⟨ht, r, rfl⟩ := hσ
    obtain rfl : t = 0 := by omega
    have e := hi (Sum.inr r)
    change stk y φ 0 (eS (Sum.inr (Sum.inr r))) = fun ω => M0 ω r at e
    rw [e]
    exact hM0 r

/-- Woodford (2003), pp. 541–542 and App. C.1 (**equilibria are solutions**): a bounded
equilibrium of the stacked pencil system with initial condition `(Z₀, M₀)` is a bounded solution
of (1.1) + (1.9) from `t₀ = 0` with `Z_0 = Z₀`, `M_{−1} = M₀`. -/
theorem focSystem_of_equil (𝔼 : ExpectationSystem Ω) (P : LQProblem ιZ ιz ιτ)
    {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ}
    {x : ℕ → ((ιz ⊕ Unit) ⊕ ιZ) ⊕ (ιZ ⊕ ιz) → Ω → ℝ}
    (h : EquilPencilR 𝔼 (A0 P) (A1 P) (wS P c) (x0S Z0 M0) x) :
    FOCSystem P 𝔼 c 0 Z0 M0 (unY x) (unΦ x) := by
  rw [← stk_un x] at h
  obtain ⟨hs, ha, hp, hi, hb⟩ := h
  have hs' := (solvesPencil_stk_iff 𝔼 P c (unY x) (unΦ x)).mp hs
  have hZk : ∀ t, KnownV 𝔼 t (fun ω => Zpart (unY x (t + 1) ω)) := fun t j =>
    hp t (Sum.inl j)
  refine ⟨⟨fun t _ ω => (struct_pt_iff 𝔼 P.sys c (unY x) t (hZk t) ω).mp (hs' t ω).2,
    fun ω => funext fun j => congrFun (hi (Sum.inl j)) ω, ?_, fun t a => by
      have := ha t (eS (Sum.inl a)); rwa [stk_eS] at this⟩,
    ?_, fun t r => hp t (Sum.inr r), fun ω => funext fun r => congrFun (hi (Sum.inr r)) ω,
    fun t _ ω => (hs' t ω).1⟩
  · obtain ⟨K, hK⟩ := hb
    refine ⟨K, fun t ω a => ?_⟩
    have := hK t (eS (Sum.inl a)) ω
    rwa [stk_eS] at this
  · obtain ⟨K, hK⟩ := hb
    refine ⟨K, fun t ω b => ?_⟩
    have := hK t (eS (Sum.inr b)) ω
    rwa [stk_eS] at this

/-! ### The characteristic polynomial -/

/-- Woodford (2003), (1.1) + (1.9) and App. C.1: **the pencil polynomial of the stacked system
is the Euler polynomial**, `det(λA₀ − A₁) = det(λF − G)` (over `ℂ`). -/
theorem pencilPoly_map (P : LQProblem ιZ ιz ιτ) :
    (pencilPoly (A0 P) (A1 P)).map Complex.ofRealHom = eulerPoly P := by
  refine Polynomial.funext fun ν => ?_
  rw [eulerPoly_eval, eval_map, ← coe_eval₂RingHom, pencilPoly, RingHom.map_det,
    ← det_reindex_self eS (pencilC P ν)]
  congr 1
  ext i j
  simp [A0, A1, pencilC, Matrix.scalar_apply, mul_apply, diagonal, sub_eq_add_neg]
  ring

/-! ### Determinacy of the stacked system -/

/-- **Woodford (2003), (1.1) + (1.9) and App. C.1 (Blanchard–Kahn for the stacked system; King and
Watson, Klein)**: for any expectation system on a nonempty sample space, the stacked system is
determinate (a unique bounded equilibrium for every bounded adapted forcing and every bounded
initial `(Z_0, M_{−1})` known at `0`) iff the Euler polynomial `det(νF − G)` is nonzero, has no
root on the unit circle, has exactly `n = n_Z + n_z` roots (with multiplicity) in the open unit
disc, and the genericity condition `TidyR6aGeneralBKSingular.GenericPencil` holds. -/
theorem stack_determinate_iff_count [Nonempty Ω] (𝔼 : ExpectationSystem Ω)
    (P : LQProblem ιZ ιz ιτ) :
    DeterminatePencilR 𝔼 (A0 P) (A1 P) ↔ eulerPoly P ≠ 0 ∧
      (∀ μ ∈ (eulerPoly P).roots, ‖μ‖ ≠ 1) ∧
      Multiset.card ((eulerPoly P).roots.filter (fun μ => ‖μ‖ < 1)) =
        Fintype.card (ιZ ⊕ ιz) ∧ GenericPencil (A0 P) (A1 P) := by
  rw [determinatePencilR_iff_general, pencilPoly_map, ← pencilPoly_map,
    Polynomial.map_ne_zero_iff Complex.ofRealHom.injective, pencilPoly_map]

/-- Woodford (2003), App. G.1 (tool): for a nonzero Euler polynomial, no root lies on the unit
circle iff the homogeneous perfect-foresight system has no eigen-solution `νᵗ(u, p)` with
`|ν| = 1`. -/
theorem noUnit_iff (P : LQProblem ιZ ιz ιτ) (hE : eulerPoly P ≠ 0) :
    (∀ μ ∈ (eulerPoly P).roots, ‖μ‖ ≠ 1) ↔ ∀ ν : ℂ, ‖ν‖ = 1 → ¬ EulerRoot P ν := by
  constructor
  · intro h ν hν hr
    refine h ν ?_ hν
    rw [mem_roots hE, IsRoot.def, eulerPoly_eval]
    exact (eulerRoot_iff P ν).mp hr
  · intro h μ hμ h1
    refine h μ h1 ((eulerRoot_iff P μ).mpr ?_)
    rw [← eulerPoly_eval]
    exact (mem_roots hE).mp hμ

/-- Woodford (2003), Assumption 8.1 and App. C.1 (**genericity from uniqueness**): under the
perfect-foresight Assumption 8.1 the stacked pencil satisfies the genericity condition — a bounded
deterministic solution of `F x_{t+1} = G x_t` with `(Z_0, M_{−1}) = 0`, added to a solution, would
give a second solution with the same data. -/
theorem generic_of_assumption81 {P : LQProblem ιZ ιz ιτ}
    (hA81 : Assumption81 P perfectForesight 0) : GenericPencil (A0 P) (A1 P) := by
  rintro v ⟨yv, hy0, ⟨C, hC⟩, hrec⟩ hvX
  obtain ⟨y1, φ1, h1⟩ := hA81.solvable (fun _ _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
    ⟨0, fun _ _ _ => by simp⟩ (fun _ _ => perfectForesight.const _ 0)
    (fun _ => perfectForesight.const _ 0) (fun _ => perfectForesight.const _ 0)
  have hE1 := equil_of_focSystem perfectForesight P h1 (fun _ => perfectForesight.const _ 0)
  set x2 : ℕ → ((ιz ⊕ Unit) ⊕ ιZ) ⊕ (ιZ ⊕ ιz) → Unit → ℝ :=
    fun t k u => stk y1 φ1 t k u + yv t k with hx2
  have hEq2 : EquilPencilR perfectForesight (A0 P) (A1 P) (wS P fun _ _ _ => 0)
      (x0S (fun _ _ => 0) (fun _ _ => 0)) x2 := by
    obtain ⟨hs, -, -, hi, hb⟩ := hE1
    refine ⟨fun t => ?_, fun _ _ => rfl, fun _ _ => rfl, fun j => ?_, ?_⟩
    · funext k u
      have e1 := congrFun (congrFun (hs t) k) u
      have e2 := congrFun (hrec t) k
      simp only [Pi.add_apply, BKForward.mv_apply] at e1 ⊢
      change (A0 P *ᵥ fun i => stk y1 φ1 (t + 1) i u + yv (t + 1) i) k =
        (A1 P *ᵥ fun i => stk y1 φ1 t i u + yv t i) k + wS P (fun _ _ _ => 0) t k u
      have h3 : (fun i => stk y1 φ1 (t + 1) i u + yv (t + 1) i) =
          (fun i => stk y1 φ1 (t + 1) i u) + yv (t + 1) := rfl
      have h4 : (fun i => stk y1 φ1 t i u + yv t i) = (fun i => stk y1 φ1 t i u) + yv t := rfl
      change (A0 P *ᵥ fun i => stk y1 φ1 (t + 1) i u) k =
        (A1 P *ᵥ fun i => stk y1 φ1 t i u) k + wS P (fun _ _ _ => 0) t k u at e1
      rw [h3, h4, mulVec_add, mulVec_add, Pi.add_apply, Pi.add_apply, e2, e1]
      ring
    · funext u
      have e := congrFun (hi j) u
      change stk y1 φ1 0 (Sum.inr j) u + yv 0 (Sum.inr j) = _
      rw [e, hy0, hvX j]
      rcases j with j | r <;> simp [x0S]
    · obtain ⟨K, hK⟩ := hb
      exact ⟨K + C, fun t k u => (abs_add_le _ _).trans (add_le_add (hK t k u) (hC t k))⟩
  have hF2 := focSystem_of_equil perfectForesight P hEq2
  have hU := hA81.unique _ _ _ _ _ _ _ h1 hF2
  have hz : ∀ t k, yv t k = 0 := by
    intro t k
    obtain ⟨σ, rfl⟩ := eS.surjective k
    obtain ⟨hy, hφ⟩ := hU t (Nat.zero_le t)
    rcases σ with a | b
    · have e := congrFun (congrFun hy ()) a
      change y1 t () a = stk y1 φ1 t (eS (Sum.inl a)) () + yv t (eS (Sum.inl a)) at e
      rw [stk_eS] at e
      change y1 t () a = y1 t () a + _ at e
      linarith
    · have e := congrFun (congrFun hφ ()) b
      change φ1 t () b = stk y1 φ1 t (eS (Sum.inr b)) () + yv t (eS (Sum.inr b)) at e
      rw [stk_eS] at e
      change φ1 t () b = φ1 t () b + _ at e
      linarith
  rw [← hy0]
  funext k
  exact hz 0 k

/-- **Woodford (2003), Assumption 8.1 and App. C.1 (sufficiency)**: the perfect-foresight
Assumption 8.1 and no root of the Euler pencil on the unit circle give determinacy of the
stacked system under every expectation system (nonempty sample space). The count of
`OptimalRulesMeasureMultiplicity.card_closedDisk_eq` (exactly `n` roots in the closed unit disc)
becomes the Blanchard–Kahn count in the open disc. -/
theorem determinate_of_assumption81 [Nonempty Ω] (𝔼 : ExpectationSystem Ω)
    {P : LQProblem ιZ ιz ιτ} (hA81 : Assumption81 P perfectForesight 0)
    (hnu : ∀ ν : ℂ, ‖ν‖ = 1 → ¬ EulerRoot P ν) : DeterminatePencilR 𝔼 (A0 P) (A1 P) := by
  have hE := OptimalRulesMeasureMultiplicity.eulerPoly_ne_zero hA81
  exact (stack_determinate_iff_count 𝔼 P).mpr ⟨hE, (noUnit_iff P hE).mpr hnu,
    (OptimalRulesMeasureMultiplicity.card_openDisk_eq_of_noEulerRoot hA81 hnu).1,
    generic_of_assumption81 hA81⟩

/-- Woodford (2003), Assumption 8.1, p. 541 (**the corrected Assumption 8.1 from stacked
determinacy**): if the stacked system is determinate, (1.1) + (1.9) has a unique bounded solution
for every bounded adapted disturbance, every bounded `Z_0` known at `0` and every bounded `M_{−1}`
known at `0` (`InertiaAssumption81.Assumption81MB` at `t₀ = 0`). -/
theorem assumption81MB_of_determinate (𝔼 : ExpectationSystem Ω) {P : LQProblem ιZ ιz ιτ}
    (hD : DeterminatePencilR 𝔼 (A0 P) (A1 P)) : InertiaAssumption81.Assumption81MB P 𝔼 0 := by
  refine ⟨fun cc Z0 M0 hcb hca hZk hZb hMb hMk => ?_, fun cc Z0 M0 y y' φ φ' h1 h2 => ?_⟩
  · have hwb : BKForward.BoundedV (wS P cc) := by
      obtain ⟨K, hK⟩ := hcb
      refine ⟨∑ a, |(P.Tᵀ *ᵥ (P.W *ᵥ P.τstar)) a| + |K|, fun t k ω => ?_⟩
      obtain ⟨σ, rfl⟩ := eS.surjective k
      simp only [wS, Equiv.symm_apply_apply]
      rcases σ with a | (j | r)
      · exact (Finset.single_le_sum (f := fun a => |(P.Tᵀ *ᵥ (P.W *ᵥ P.τstar)) a|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ a)).trans (le_add_of_nonneg_right
            (abs_nonneg _))
      · simp only [Sum.elim_inr, liftDist, Sum.elim_inl, Pi.zero_apply, abs_zero]
        positivity
      · simp only [Sum.elim_inr, liftDist]
        exact (hK t ω r).trans ((le_abs_self K).trans (le_add_of_nonneg_left
          (Finset.sum_nonneg fun _ _ => abs_nonneg _)))
    have hwa : BKForward.AdaptedV 𝔼 (wS P cc) := by
      intro t k
      obtain ⟨σ, rfl⟩ := eS.surjective k
      have e : wS P cc t (eS σ) =
          fun ω => Sum.elim (P.Tᵀ *ᵥ (P.W *ᵥ P.τstar)) (liftDist cc t ω) σ := by
        funext ω
        simp [wS]
      rw [e]
      rcases σ with a | (j | r)
      · exact 𝔼.const t _
      · exact 𝔼.const t 0
      · exact hca t r
    obtain ⟨KZ, hKZ⟩ := hZb
    obtain ⟨KM, hKM⟩ := hMb
    obtain ⟨x, hx, -⟩ := hD (wS P cc) hwb hwa (x0S Z0 M0)
      (fun j => by rcases j with j | r; exacts [hZk j, hMk r])
      ⟨max KZ KM, fun j ω => by
        rcases j with j | r
        · exact (hKZ ω j).trans (le_max_left _ _)
        · exact (hKM ω r).trans (le_max_right _ _)⟩
    exact ⟨unY x, unΦ x, focSystem_of_equil 𝔼 P hx⟩
  · obtain ⟨hs1, ha1, hp1, hi1, hb1⟩ := focSystem_pre 𝔼 P h1
    obtain ⟨hs2, ha2, hp2, hi2, hb2⟩ := focSystem_pre 𝔼 P h2
    set x1 := stk y φ with hx1
    set x2 := stk y' φ' with hx2
    set d : ℕ → ((ιz ⊕ Unit) ⊕ ιZ) ⊕ (ιZ ⊕ ιz) → Ω → ℝ := fun t => x1 t - x2 t with hd
    have hdE : ∀ t k, 𝔼.E t (d t k) = 𝔼.E t (x1 t k) - 𝔼.E t (x2 t k) := fun t k => by
      simp only [hd, Pi.sub_apply, map_sub]
    have hEq : EquilPencilR 𝔼 (A0 P) (A1 P) (fun _ _ _ => 0) (fun _ _ => 0) d := by
      refine ⟨fun t => ?_, fun t k => ?_, fun t j => ?_, fun j => ?_, ?_⟩
      · have e : (fun i => 𝔼.E t (d (t + 1) i)) =
            (fun i => 𝔼.E t (x1 (t + 1) i)) - fun i => 𝔼.E t (x2 (t + 1) i) := by
          funext i
          simp only [hd, Pi.sub_apply, map_sub]
        rw [e, BKForward.mv_sub, hs1 t, hs2 t, hd]
        simp only [BKForward.mv_sub]
        funext k ω
        simp only [Pi.add_apply, Pi.sub_apply]
        ring
      · obtain ⟨σ, rfl⟩ := eS.surjective k
        by_cases hσ : 0 < t ∨ ∀ r, σ ≠ Sum.inr (Sum.inr r)
        · rw [hdE, ha1 t σ hσ, ha2 t σ hσ]
          rfl
        · push Not at hσ
          obtain ⟨ht, r, rfl⟩ := hσ
          obtain rfl : t = 0 := by omega
          have e : d 0 (eS (Sum.inr (Sum.inr r))) = 0 := by
            change x1 0 (Sum.inr (Sum.inr r)) - x2 0 (Sum.inr (Sum.inr r)) = 0
            rw [hi1 (Sum.inr r), hi2 (Sum.inr r), sub_self]
          rw [e, map_zero]
      · simp only [hd, Pi.sub_apply, map_sub]
        rw [hp1 t j, hp2 t j]
      · change x1 0 (Sum.inr j) - x2 0 (Sum.inr j) = _
        rw [hi1 j, hi2 j, sub_self]
        rfl
      · obtain ⟨K1, h1⟩ := hb1
        obtain ⟨K2, h2⟩ := hb2
        exact ⟨K1 + K2, fun t k ω => (abs_sub _ _).trans (add_le_add (h1 t k ω) (h2 t k ω))⟩
    have hZero : EquilPencilR 𝔼 (A0 P) (A1 P) (fun _ _ _ => 0) (fun _ _ => 0)
        (fun _ _ _ => 0) := by
      refine ⟨fun t => ?_, fun t _ => 𝔼.const t 0, fun t _ => 𝔼.const t 0, fun _ => rfl,
        ⟨0, fun _ _ _ => by simp⟩⟩
      funext k ω
      simp only [BKForward.mv_apply, 𝔼.const, Pi.add_apply, add_zero]
      rw [show (fun _ : ((ιz ⊕ Unit) ⊕ ιZ) ⊕ (ιZ ⊕ ιz) => (0 : ℝ)) = 0 from rfl, mulVec_zero,
        mulVec_zero]
    obtain ⟨z, -, hu⟩ := hD (fun _ _ _ => 0) ⟨0, fun _ _ _ => by simp⟩ (fun t _ => 𝔼.const t 0)
      (fun _ _ => 0) (fun _ => 𝔼.const 0 0) ⟨0, fun _ _ => by simp⟩
    have hd0 : d = fun _ _ _ => 0 := (hu d hEq).trans (hu _ hZero).symm
    intro t _
    have hk : ∀ σ ω, Sum.elim (y t ω) (φ t ω) σ = Sum.elim (y' t ω) (φ' t ω) σ := by
      intro σ ω
      have e := congrFun (congrFun (congrFun hd0 t) (eS σ)) ω
      change x1 t (eS σ) ω - x2 t (eS σ) ω = 0 at e
      rw [hx1, hx2, stk_eS, stk_eS] at e
      exact sub_eq_zero.mp e
    exact ⟨funext fun ω => funext fun a => hk (Sum.inl a) ω,
      funext fun ω => funext fun b => hk (Sum.inr b) ω⟩

/-- Woodford (2003), Assumption 8.1, p. 541 (**the book's Assumption 8.1 under perfect
foresight**) from determinacy of the stacked system under perfect foresight. -/
theorem assumption81_of_determinate {P : LQProblem ιZ ιz ιτ}
    (hD : DeterminatePencilR perfectForesight (A0 P) (A1 P)) :
    Assumption81 P perfectForesight 0 := by
  have hB := assumption81MB_of_determinate perfectForesight hD
  refine ⟨fun c Z0 M0 hcb hca hZk hMk => hB.solvable c Z0 M0 hcb hca hZk ?_ ?_ hMk, hB.unique⟩
  · exact ⟨∑ j, |Z0 () j|, fun u j => by
      cases u
      exact Finset.single_le_sum (f := fun j => |Z0 () j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)⟩
  · exact ⟨∑ r, |M0 () r|, fun u r => by
      cases u
      exact Finset.single_le_sum (f := fun r => |M0 () r|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ r)⟩

/-- **Woodford (2003), (1.1) + (1.9), Assumption 8.1 and App. C.1 (the exact relation)**: for any
expectation system on a nonempty sample space, the stacked system is Blanchard–Kahn determinate
**iff** the perfect-foresight Assumption 8.1 holds **and** the Euler pencil has no root on the
unit circle. In particular determinacy does not depend on the expectation system. -/
theorem stack_determinate_iff [Nonempty Ω] (𝔼 : ExpectationSystem Ω) (P : LQProblem ιZ ιz ιτ) :
    DeterminatePencilR 𝔼 (A0 P) (A1 P) ↔
      Assumption81 P perfectForesight 0 ∧ ∀ ν : ℂ, ‖ν‖ = 1 → ¬ EulerRoot P ν := by
  constructor
  · intro hD
    have hc := (stack_determinate_iff_count 𝔼 P).mp hD
    exact ⟨assumption81_of_determinate ((stack_determinate_iff_count perfectForesight P).mpr hc),
      (noUnit_iff P hc.1).mp hc.2.1⟩
  · rintro ⟨hA, hnu⟩
    exact determinate_of_assumption81 𝔼 hA hnu

/-- Woodford (2003), Assumption 8.1 and App. C.1 (**the link with the root count**): if the stacked
system is determinate, the Euler pencil has exactly `n = n_Z + n_z` roots in the **closed** unit
disc (`OptimalRulesMeasureMultiplicity.card_closedDisk_eq`) and the same `n` in the open disc —
Blanchard–Kahn's count for the `n` predetermined variables `(Z_t, M_{t−1})`. -/
theorem stack_determinate_card [Nonempty Ω] (𝔼 : ExpectationSystem Ω) {P : LQProblem ιZ ιz ιτ}
    (hD : DeterminatePencilR 𝔼 (A0 P) (A1 P)) :
    Multiset.card ((eulerPoly P).roots.filter fun r => ‖r‖ ≤ 1) = Fintype.card (ιZ ⊕ ιz) ∧
      Multiset.card ((eulerPoly P).roots.filter fun r => ‖r‖ < 1) = Fintype.card (ιZ ⊕ ιz) := by
  obtain ⟨hA, hnu⟩ := (stack_determinate_iff 𝔼 P).mp hD
  exact ⟨OptimalRulesMeasureMultiplicity.card_closedDisk_eq hA,
    (OptimalRulesMeasureMultiplicity.card_openDisk_eq_of_noEulerRoot hA hnu).1⟩

/-- Woodford (2003), Assumption 8.1 (**it does not give Blanchard–Kahn determinacy of the stacked
system**): the problem `OptimalRulesMeasureCounterexample.eBP` satisfies the perfect-foresight
Assumption 8.1, but its Euler pencil has the root `1`, so the stacked system is not determinate
(for every expectation system): some bounded forcing of the stacked rows has no bounded
equilibrium. The relation of Assumption 8.1 to Blanchard–Kahn is exactly `stack_determinate_iff`;
the closed-disc count `OptimalRulesMeasureMultiplicity.card_closedDisk_eq` holds in both cases. -/
theorem eB_not_determinate [Nonempty Ω] (𝔼 : ExpectationSystem Ω) :
    Assumption81 OptimalRulesMeasureCounterexample.eBP perfectForesight 0 ∧
      ¬ DeterminatePencilR 𝔼 (A0 OptimalRulesMeasureCounterexample.eBP)
        (A1 OptimalRulesMeasureCounterexample.eBP) := by
  refine ⟨OptimalRulesMeasureCounterexample.eB_pf, fun hD => ?_⟩
  exact ((stack_determinate_iff 𝔼 _).mp hD).2 1 (by simp) eB_eulerRoot_one

end Woodford.OptimalPolicyRules.TidyR6aStackedBK
