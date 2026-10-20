/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.PencilSplit
import OptimalPolicyRules.TargetCriterion
import OptimalPolicyRules.ExpectationsFiniteTree
import Mathlib.Algebra.Order.Star.Real

/-!
# Proposition 8.1 in general

Woodford (2003), *Interest and Prices*, Chapter 8, Section 1.4, Proposition 8.1 (pp. 552–553,
(1.18)–(1.21)) with Appendix G.1 (pp. 716–718).

Proposition 8.1 asserts matrices `Λ`, `Υ` and operators `Q(L⁻¹)`, `R(L⁻¹)` such that bounded
multipliers `φ_t = (ξ_t, M_{t-1})` and targets satisfy (1.18) for all `t ≥ t₀` if and only if
`M_t = Λ M_{t-1} + E_t Q(L⁻¹) T̃'W(τ_t − τ*)` (1.20) and
`ξ_t = Υ M_{t-1} + E_t R(L⁻¹) T̃'W(τ_t − τ*)` (1.21).

## The construction (invariant-subspace route)

From a real deflating pair `A J = Î J Ψ` (`PencilSplit.DeflatingSplit`; all eigenvalues of `Ψ`
in `|μ| < β⁻¹`, `J₁` and `K` invertible):

* `J'` applied to (1.18) gives, for `w_t = J' Î' φ_t`, the forward equation
  `w_t = β Ψ' E_t w_{t+1} + β J' x_t` with `x_t = T̃'W(τ_t − τ*)`. Its unique bounded solution is
  the forward series `F_t = ∑_k (βΨ')^k E_t β J' x_{t+k}` (`PencilSplit.eq_fwdSum`).
* Since `w_t = J₁' ξ_t + J₂' Ẽ' M_{t-1}`, this is (1.21) with `Υ = −(J₁')⁻¹ J₂' Ẽ'` and
  `R(L⁻¹)x = (J₁')⁻¹ F`.
* The `z`-rows of (1.18), with `ξ_{t+1}` from (1.21), are (1.20) with `Λ = β⁻¹ K⁻¹ Ẽ'`,
  `K = A₂₂' + A₁₂' Υ`.

No diagonalisability (Assumption 8.3) is used; the eigenvector apparatus of App. G.1 is needed
only to produce the deflating pair (module `PencilExistence`).

## A correction

The multipliers `M_t` are known at `t` (p. 540), and the equivalence holds only for multiplier
processes with that property (and adapted plans). Without it the statement is false under
uncertainty: `not_prop81Equiv_coin` shows that on the coin-flip tree no `Λ, Υ, Q, R` whatsoever
satisfy the equivalence as formalised in `TargetCriterion.Prop81.Prop81Equiv` (a mean-zero
multiplier innovation `M_{t₀}` preserves (1.18), which constrains only `E_{t₀} M_{t₀}`, but not
(1.20)). The corrected statement `Prop81EquivM` adds `M_t` known at `t` and is proved in general
(`prop81`); under perfect foresight both coincide and the original hypothesis structure
`Prop81Conclusion` is inhabited (`prop81_perfectForesight`).

## Main results

* `prop81`: Proposition 8.1 (corrected), from a `DeflatingSplit`, for any expectation system.
* `prop81_perfectForesight`: an inhabitant of the original `Prop81Conclusion` (deterministic).
* `not_prop81Equiv_coin`, `prop81Conclusion_coin_isEmpty`, `prop81M_coin`: the counterexample.
* `rank_Λmat`: `rank Λ = rank Ẽ` (fn 15, p. 554), hence `deg α ≤ rank Ẽ` (`natDegree_alpha_le`).
-/

namespace Woodford.OptimalPolicyRules.Prop81General

open Matrix GeneralSetup GeneralFOC.LQ PencilSplit TargetCriterion.Prop81 Adjugate

variable {Ω : Type*} {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-! ### The corrected statement of Proposition 8.1 -/

/-- Woodford (2003), p. 540: the multipliers `M_t` (the `z`-block of `φ_{t+1}`) are known at
date `t`, for all `t ≥ t₀`. -/
def MultKnown (𝔼 : ExpectationSystem Ω) (t0 : ℕ) (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ) : Prop :=
  ∀ t, t0 ≤ t → KnownV 𝔼 t (fun ω => Mpart (φ (t + 1) ω))

/-- Woodford (2003), Proposition 8.1, p. 553 (corrected): bounded adapted plans and bounded
multipliers with `M_t` known at `t` satisfy (1.18) for all `t ≥ t₀` iff they satisfy (1.20) and
(1.21), with `q = Qop(T̃'W(τ − τ*))`, `r = Rop(T̃'W(τ − τ*))`. -/
def Prop81EquivM (P : LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    (Λ : Matrix ιz ιz ℝ) (Υ : Matrix ιZ ιz ℝ)
    (Qop : (ℕ → Ω → ιZ ⊕ ιz → ℝ) → ℕ → Ω → ιz → ℝ)
    (Rop : (ℕ → Ω → ιZ ⊕ ιz → ℝ) → ℕ → Ω → ιZ → ℝ) : Prop :=
  ∀ y φ, BoundedV y → AdaptedV 𝔼 y → BoundedV φ → MultKnown 𝔼 t0 φ →
    (Eq118 P 𝔼 t0 y φ ↔ Eq120 t0 Λ (Qop (xproc P y)) φ ∧ Eq121 t0 Υ (Rop (xproc P y)) φ)

/-- Woodford (2003), Proposition 8.1, p. 553 (corrected): matrices `Λ`, `Υ` and operators
`Q(L⁻¹)`, `R(L⁻¹)` (mapping bounded processes to bounded adapted processes) with the
equivalence `Prop81EquivM`. -/
structure Prop81ConclusionM (P : LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω) (t0 : ℕ) where
  Λ : Matrix ιz ιz ℝ
  Υ : Matrix ιZ ιz ℝ
  Qop : (ℕ → Ω → ιZ ⊕ ιz → ℝ) → ℕ → Ω → ιz → ℝ
  Rop : (ℕ → Ω → ιZ ⊕ ιz → ℝ) → ℕ → Ω → ιZ → ℝ
  equiv : Prop81EquivM P 𝔼 t0 Λ Υ Qop Rop
  Qbounded : ∀ x, BoundedV x → BoundedV (Qop x)
  Rbounded : ∀ x, BoundedV x → BoundedV (Rop x)
  Qadapted : ∀ x, AdaptedV 𝔼 (Qop x)
  Radapted : ∀ x, BoundedV x → AdaptedV 𝔼 (Rop x)

/-! ### The operators `Q(L⁻¹)` and `R(L⁻¹)` -/

/-- Woodford (2003), App. G.1: the forcing `β J' x_t` of the forward equation for
`w_t = J' Î' φ_t`. -/
def fpart (β : ℝ) (J : Matrix (ιZ ⊕ ιz) ιZ ℝ) (x : ℕ → Ω → ιZ ⊕ ιz → ℝ) : ℕ → Ω → ιZ → ℝ :=
  fun t ω => (β • Jᵀ) *ᵥ x t ω

/-- Woodford (2003), App. G.1: the forward solution
`F_t = ∑_{k ≥ 0} (βΨ')^k E_t β J' x_{t+k}` of `w_t = βΨ' E_t w_{t+1} + β J' x_t`. -/
noncomputable def Fw (𝔼 : ExpectationSystem Ω) {S : LinearRESystem ιZ ιz} {β : ℝ}
    (D : DeflatingSplit S β) (x : ℕ → Ω → ιZ ⊕ ιz → ℝ) : ℕ → Ω → ιZ → ℝ :=
  fwdSum 𝔼 (β • D.Ψᵀ) (fpart β D.J x)

/-- Woodford (2003), eq. (1.21), p. 553: the operator `E_t R(L⁻¹)`,
`r_t = (J₁')⁻¹ ∑_{k ≥ 0} (βΨ')^k E_t β J' x_{t+k}`. -/
noncomputable def Rop (𝔼 : ExpectationSystem Ω) {S : LinearRESystem ιZ ιz} {β : ℝ}
    (D : DeflatingSplit S β) (x : ℕ → Ω → ιZ ⊕ ιz → ℝ) : ℕ → Ω → ιZ → ℝ :=
  fun t ω => ((J1 D.J)ᵀ)⁻¹ *ᵥ Fw 𝔼 D x t ω

/-- Woodford (2003), eq. (1.20), p. 553: the operator `E_t Q(L⁻¹)`,
`q_t = −K⁻¹ (E_t x^z_t + A₁₂' E_t r_{t+1})`. -/
noncomputable def Qop (𝔼 : ExpectationSystem Ω) {S : LinearRESystem ιZ ιz} {β : ℝ}
    (D : DeflatingSplit S β) (x : ℕ → Ω → ιZ ⊕ ιz → ℝ) : ℕ → Ω → ιz → ℝ :=
  fun t ω => -((Kmat S D.J)⁻¹ *ᵥ (EV 𝔼 t (fun ω' => Mpart (x t ω')) ω +
    S.A12ᵀ *ᵥ EV 𝔼 t (Rop 𝔼 D x (t + 1)) ω))

/-! ### Auxiliary facts -/

omit [DecidableEq ιZ] in
/-- Woodford (2003), p. 553: `T̃'W(τ_t − τ*)` is adapted for adapted plans. -/
theorem adaptedV_xproc (P : LQProblem ιZ ιz ιτ) {𝔼 : ExpectationSystem Ω}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : AdaptedV 𝔼 y) : AdaptedV 𝔼 (xproc P y) := by
  intro t
  have h : (fun ω => xproc P y t ω) = fun ω => (P.Ttilᵀ * (P.W * P.T)) *ᵥ y t ω +
      -(P.Ttilᵀ *ᵥ (P.W *ᵥ P.τstar)) := by
    funext ω
    simp only [xproc, mulVec_mulVec, sub_eq_add_neg, mulVec_add, mulVec_neg]
  have hc : KnownV 𝔼 t (fun _ : Ω => -(P.Ttilᵀ *ᵥ (P.W *ᵥ P.τstar))) := fun i => 𝔼.const t _
  have := knownV_mulVec_add 𝔼 (P.Ttilᵀ * (P.W * P.T)) (hy t) hc
  rw [← h] at this
  exact this

/-- Woodford (2003), eq. (1.18), p. 552: the left side of (1.18) at date `t`. -/
noncomputable def lhs118 (P : LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ) (t : ℕ) (ω : Ω) :
    ιZ ⊕ ιz → ℝ :=
  P.sys.Ahatᵀ *ᵥ EV 𝔼 t (φ (t + 1)) ω + xproc P y t ω - P.β⁻¹ • (P.sys.Ihatᵀ *ᵥ φ t ω)

/-- Woodford (2003), (1.18) and App. G.1: the `z`-rows of (1.18),
`A₁₂' E_t ξ_{t+1} + A₂₂' E_t M_t + x^z_t − β⁻¹ Ẽ' M_{t-1}`. -/
theorem Mpart_lhs118 (P : LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ) (t : ℕ) (ω : Ω) :
    Mpart (lhs118 P 𝔼 y φ t ω) =
      P.sys.A12ᵀ *ᵥ EV 𝔼 t (fun ω' => ξpart (φ (t + 1) ω')) ω +
        P.sys.A22ᵀ *ᵥ EV 𝔼 t (fun ω' => Mpart (φ (t + 1) ω')) ω + Mpart (xproc P y t ω) -
        P.β⁻¹ • (P.sys.Etᵀ *ᵥ Mpart (φ t ω)) := by
  unfold lhs118
  rw [Ahat_transpose_mulVec, Ihat_transpose_mulVec]
  rfl

/-- Woodford (2003), (1.18) and (G.4): `J'` times the left side of (1.18) is
`Ψ' E_t w_{t+1} + J' x_t − β⁻¹ w_t` with `w_t = J' Î' φ_t`. -/
theorem J_lhs118 (P : LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω)
    (D : DeflatingSplit P.sys P.β) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ)
    (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ) (t : ℕ) (ω : Ω) :
    D.Jᵀ *ᵥ lhs118 P 𝔼 y φ t ω =
      D.Ψᵀ *ᵥ EV 𝔼 t (fun ω' => (D.Jᵀ * P.sys.Ihatᵀ) *ᵥ φ (t + 1) ω') ω +
        D.Jᵀ *ᵥ xproc P y t ω - P.β⁻¹ • ((D.Jᵀ * P.sys.Ihatᵀ) *ᵥ φ t ω) := by
  unfold lhs118
  have h1 := deflate_transpose D.deflate (EV 𝔼 t (φ (t + 1)) ω)
  have h2 : EV 𝔼 t (fun ω' => (D.Jᵀ * P.sys.Ihatᵀ) *ᵥ φ (t + 1) ω') ω =
      (D.Jᵀ * P.sys.Ihatᵀ) *ᵥ EV 𝔼 t (φ (t + 1)) ω := by rw [EV_mulVec]
  rw [h2, mulVec_sub, mulVec_add, h1, mulVec_smul, ← mulVec_mulVec, ← mulVec_mulVec]

/-- Woodford (2003), App. G.1: `w_t = J' Î' φ_t = J₁' ξ_t + J₂' Ẽ' M_{t-1}`. -/
theorem w_split (S : LinearRESystem ιZ ιz) (J : Matrix (ιZ ⊕ ιz) ιZ ℝ) (v : ιZ ⊕ ιz → ℝ) :
    (Jᵀ * S.Ihatᵀ) *ᵥ v = (J1 J)ᵀ *ᵥ ξpart v + (J2 J)ᵀ *ᵥ (S.Etᵀ *ᵥ Mpart v) := by
  rw [← mulVec_mulVec, Ihat_transpose_mulVec, J_transpose_mulVec]
  rfl

/-- Woodford (2003), eq. (1.21): with `J₁` invertible, `ξ = Υ M + (J₁')⁻¹ F` iff
`J₁' ξ + J₂' Ẽ' M = F`. -/
theorem eq121_iff (S : LinearRESystem ιZ ιz) {J : Matrix (ιZ ⊕ ιz) ιZ ℝ}
    (hJ1 : (J1 J).det ≠ 0) (ξ F : ιZ → ℝ) (M : ιz → ℝ) :
    ξ = Υmat S J *ᵥ M + ((J1 J)ᵀ)⁻¹ *ᵥ F ↔ (J1 J)ᵀ *ᵥ ξ + (J2 J)ᵀ *ᵥ (S.Etᵀ *ᵥ M) = F := by
  have hu : IsUnit ((J1 J)ᵀ).det := by rw [det_transpose]; exact Ne.isUnit hJ1
  have h1 := nonsing_inv_mul _ hu
  have h2 := mul_nonsing_inv _ hu
  have hrhs : Υmat S J *ᵥ M + ((J1 J)ᵀ)⁻¹ *ᵥ F =
      ((J1 J)ᵀ)⁻¹ *ᵥ (F - (J2 J)ᵀ *ᵥ (S.Etᵀ *ᵥ M)) := by
    rw [Υmat, neg_mulVec, mulVec_sub, ← mulVec_mulVec, ← mulVec_mulVec]
    abel
  rw [hrhs]
  constructor
  · intro h
    rw [h, mulVec_mulVec, h2, one_mulVec]
    abel
  · intro h
    rw [← h, add_sub_cancel_right, mulVec_mulVec, h1, one_mulVec]

/-- Woodford (2003), eq. (1.20): with `K` invertible,
`M' = Λ M + q` (with `q = −K⁻¹(e + A₁₂' ρ)`) iff `K M' + A₁₂' ρ + e − β⁻¹ Ẽ' M = 0`. -/
theorem eq120_iff (S : LinearRESystem ιZ ιz) (β : ℝ) {J : Matrix (ιZ ⊕ ιz) ιZ ℝ}
    (hK : (Kmat S J).det ≠ 0) (M' M e : ιz → ℝ) (ρ : ιZ → ℝ) :
    M' = Λmat S β J *ᵥ M + -((Kmat S J)⁻¹ *ᵥ (e + S.A12ᵀ *ᵥ ρ)) ↔
      Kmat S J *ᵥ M' + S.A12ᵀ *ᵥ ρ + e - β⁻¹ • (S.Etᵀ *ᵥ M) = 0 := by
  have hu : IsUnit (Kmat S J).det := Ne.isUnit hK
  have h1 := nonsing_inv_mul _ hu
  have h2 := mul_nonsing_inv _ hu
  have hrhs : Λmat S β J *ᵥ M + -((Kmat S J)⁻¹ *ᵥ (e + S.A12ᵀ *ᵥ ρ)) =
      (Kmat S J)⁻¹ *ᵥ (β⁻¹ • (S.Etᵀ *ᵥ M) - (S.A12ᵀ *ᵥ ρ + e)) := by
    rw [Λmat, smul_mulVec, ← mulVec_mulVec, mulVec_sub, ← mulVec_smul, add_comm e]
    abel
  rw [hrhs]
  constructor
  · intro h
    rw [h, mulVec_mulVec, h2, one_mulVec]
    abel
  · intro h
    have : β⁻¹ • (S.Etᵀ *ᵥ M) - (S.A12ᵀ *ᵥ ρ + e) = Kmat S J *ᵥ M' := by
      rw [← sub_eq_zero, ← neg_eq_zero, ← h]
      abel
    rw [this, mulVec_mulVec, h1, one_mulVec]

/-! ### Proposition 8.1 -/

/-- Woodford (2003), Proposition 8.1, p. 553 (the equivalence, corrected): for a real deflating
pair (`DeflatingSplit`), bounded adapted plans and bounded multipliers with `M_t` known at `t`
satisfy (1.18) for all `t ≥ t₀` iff they satisfy (1.20) with `Λ = β⁻¹ K⁻¹ Ẽ'` and (1.21) with
`Υ = −(J₁')⁻¹ J₂' Ẽ'`, for any expectation system. -/
theorem prop81_equiv (P : LQProblem ιZ ιz ιτ) (D : DeflatingSplit P.sys P.β)
    (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    Prop81EquivM P 𝔼 t0 (Λmat P.sys P.β D.J) (Υmat P.sys D.J) (Qop 𝔼 D) (Rop 𝔼 D) := by
  intro y φ hyb hya hφb hmk
  set x := xproc P y with hx
  have hxb : BoundedV x := boundedV_xproc hyb
  have hxa : AdaptedV 𝔼 x := adaptedV_xproc P hya
  have hG : PowDecay (P.β • D.Ψᵀ) := D.powDecay_G P.β_pos
  have hfb : BoundedV (fpart P.β D.J x) := boundedV_mulVec _ hxb
  have hfk : ∀ t, KnownV 𝔼 t (fpart P.β D.J x t) := fun t => knownV_mulVec 𝔼 _ (hxa t)
  obtain ⟨hF, -, -⟩ := fwdSum_spec 𝔼 hG hfb
  have hβ : P.β ≠ 0 := P.β_pos.ne'
  -- the recursion of the forward solution, rescaled
  have hFrec : ∀ t ω, P.β⁻¹ • Fw 𝔼 D x t ω =
      D.Ψᵀ *ᵥ EV 𝔼 t (Fw 𝔼 D x (t + 1)) ω + D.Jᵀ *ᵥ x t ω := by
    intro t ω
    have h := hF t ω
    rw [EV_of_known 𝔼 (hfk t)] at h
    change Fw 𝔼 D x t ω = (P.β • D.Ψᵀ) *ᵥ EV 𝔼 t (Fw 𝔼 D x (t + 1)) ω +
      (P.β • D.Jᵀ) *ᵥ x t ω at h
    rw [h, smul_mulVec, smul_mulVec, ← smul_add, smul_smul, inv_mul_cancel₀ hβ, one_smul]
  set w : ℕ → Ω → ιZ → ℝ := fun t ω => (D.Jᵀ * P.sys.Ihatᵀ) *ᵥ φ t ω with hw
  -- the `z`-rows once (1.21) holds at `t + 1`
  have hMrows : ∀ t, t0 ≤ t → Eq121 t0 (Υmat P.sys D.J) (Rop 𝔼 D x) φ → ∀ ω,
      Mpart (lhs118 P 𝔼 y φ t ω) = Kmat P.sys D.J *ᵥ Mpart (φ (t + 1) ω) +
        P.sys.A12ᵀ *ᵥ EV 𝔼 t (Rop 𝔼 D x (t + 1)) ω +
        EV 𝔼 t (fun ω' => Mpart (x t ω')) ω - P.β⁻¹ • (P.sys.Etᵀ *ᵥ Mpart (φ t ω)) := by
    intro t ht h121 ω
    have hξ : (fun ω' => ξpart (φ (t + 1) ω')) =
        fun ω' => Υmat P.sys D.J *ᵥ Mpart (φ (t + 1) ω') + Rop 𝔼 D x (t + 1) ω' :=
      funext fun ω' => h121 (t + 1) (by omega) ω'
    have hM : EV 𝔼 t (fun ω' => Mpart (φ (t + 1) ω')) = fun ω' => Mpart (φ (t + 1) ω') :=
      EV_of_known 𝔼 (hmk t ht)
    have hxz : EV 𝔼 t (fun ω' => Mpart (x t ω')) = fun ω' => Mpart (x t ω') := by
      funext ω' r
      exact congrFun (hxa t (Sum.inr r)) ω'
    rw [Mpart_lhs118, hξ, EV_add, EV_mulVec, hM, hxz, Kmat, add_mulVec, mulVec_add,
      ← mulVec_mulVec]
    abel
  constructor
  · intro h118
    have hwb : BoundedV w := boundedV_mulVec _ hφb
    have hweq : ∀ t, t0 ≤ t → ∀ ω,
        w t ω = (P.β • D.Ψᵀ) *ᵥ EV 𝔼 t (w (t + 1)) ω + fpart P.β D.J x t ω := by
      intro t ht ω
      have h0 := congrArg (D.Jᵀ *ᵥ ·) (h118 t ht ω)
      change D.Jᵀ *ᵥ lhs118 P 𝔼 y φ t ω = D.Jᵀ *ᵥ 0 at h0
      rw [J_lhs118, mulVec_zero, sub_eq_zero] at h0
      change D.Ψᵀ *ᵥ EV 𝔼 t (w (t + 1)) ω + D.Jᵀ *ᵥ x t ω = P.β⁻¹ • w t ω at h0
      rw [fpart, smul_mulVec, smul_mulVec, ← smul_add, h0, smul_smul, mul_inv_cancel₀ hβ,
        one_smul]
    have hwF := eq_fwdSum 𝔼 hG hfb hwb (fun t _ => hfk t) hweq
    have h121 : Eq121 t0 (Υmat P.sys D.J) (Rop 𝔼 D x) φ := by
      intro t ht ω
      refine (eq121_iff P.sys D.J1_det _ _ _).mpr ?_
      rw [← w_split]
      exact congrFun (hwF t ht) ω
    refine ⟨fun t ht ω => ?_, h121⟩
    refine (eq120_iff P.sys P.β D.K_det _ _ _ _).mpr ?_
    rw [← hMrows t ht h121 ω]
    exact congrArg Mpart (h118 t ht ω)
  · rintro ⟨h120, h121⟩ t ht ω
    have hz : Mpart (lhs118 P 𝔼 y φ t ω) = 0 := by
      rw [hMrows t ht h121 ω]
      exact (eq120_iff P.sys P.β D.K_det _ _ _ _).mp (h120 t ht ω)
    have hwF : ∀ s, t0 ≤ s → w s = Fw 𝔼 D x s := by
      intro s hs
      funext ω'
      have := (eq121_iff P.sys D.J1_det _ _ _).mp (h121 s hs ω')
      rw [← w_split] at this
      exact this
    have hJ : D.Jᵀ *ᵥ lhs118 P 𝔼 y φ t ω = 0 := by
      rw [J_lhs118]
      change D.Ψᵀ *ᵥ EV 𝔼 t (w (t + 1)) ω + D.Jᵀ *ᵥ x t ω - P.β⁻¹ • w t ω = 0
      rw [hwF (t + 1) (by omega), hwF t ht, hFrec, sub_self]
    rw [J_transpose_mulVec] at hJ
    change (J1 D.J)ᵀ *ᵥ ξpart (lhs118 P 𝔼 y φ t ω) + (J2 D.J)ᵀ *ᵥ Mpart (lhs118 P 𝔼 y φ t ω) =
      0 at hJ
    rw [hz, mulVec_zero, add_zero] at hJ
    have hdet : ((J1 D.J)ᵀ).det ≠ 0 := by rw [det_transpose]; exact D.J1_det
    have hZ := eq_zero_of_mulVec_eq_zero hdet hJ
    funext a
    rcases a with i | r
    · exact congrFun hZ i
    · exact congrFun hz r

/-- Woodford (2003), Proposition 8.1, p. 553: the operators `Q(L⁻¹)`, `R(L⁻¹)` map bounded
processes to bounded processes, and `E_t Q(L⁻¹)`, `E_t R(L⁻¹)` are known at `t`. -/
theorem fw_spec (𝔼 : ExpectationSystem Ω) {S : LinearRESystem ιZ ιz} {β : ℝ} (hβ : 0 < β)
    (D : DeflatingSplit S β) {x : ℕ → Ω → ιZ ⊕ ιz → ℝ} (hx : BoundedV x) :
    BoundedV (Rop 𝔼 D x) ∧ AdaptedV 𝔼 (Rop 𝔼 D x) ∧ BoundedV (Qop 𝔼 D x) := by
  obtain ⟨-, hFa, hFb⟩ := fwdSum_spec 𝔼 (D.powDecay_G hβ) (boundedV_mulVec (β • D.Jᵀ) hx)
  have hRb : BoundedV (Rop 𝔼 D x) := boundedV_mulVec _ hFb
  refine ⟨hRb, fun t => knownV_mulVec 𝔼 _ (hFa t), ?_⟩
  obtain ⟨Mx, hMx⟩ := hx
  obtain ⟨MR, hMR⟩ := hRb
  have h1 : BoundedV (fun t ω => EV 𝔼 t (fun ω' => Mpart (x t ω')) ω +
      S.A12ᵀ *ᵥ EV 𝔼 t (Rop 𝔼 D x (t + 1)) ω) := by
    refine boundedV_add ⟨Mx, fun t ω r => abs_EV_le 𝔼 (fun ω' r' => hMx t ω' (Sum.inr r')) t ω r⟩
      (boundedV_mulVec (x := fun t ω => EV 𝔼 t (Rop 𝔼 D x (t + 1)) ω) _
        ⟨MR, fun t ω i => abs_EV_le 𝔼 (hMR (t + 1)) t ω i⟩)
  obtain ⟨K, hK⟩ := boundedV_mulVec (Kmat S D.J)⁻¹ h1
  exact ⟨K, fun t ω r => by
    change |(-((Kmat S D.J)⁻¹ *ᵥ _)) r| ≤ K
    rw [Pi.neg_apply, abs_neg]
    exact hK t ω r⟩

/-- Woodford (2003), Proposition 8.1, p. 553: `E_t Q(L⁻¹) x` is known at `t` for every `x`. -/
theorem qop_adapted (𝔼 : ExpectationSystem Ω) {S : LinearRESystem ιZ ιz} {β : ℝ}
    (D : DeflatingSplit S β) (x : ℕ → Ω → ιZ ⊕ ιz → ℝ) : AdaptedV 𝔼 (Qop 𝔼 D x) := by
  intro t
  have h1 := knownV_add 𝔼 (knownV_EV 𝔼 t (fun ω' => Mpart (x t ω')))
    (knownV_mulVec 𝔼 S.A12ᵀ (knownV_EV 𝔼 t (Rop 𝔼 D x (t + 1))))
  have h2 := knownV_mulVec 𝔼 (-(Kmat S D.J)⁻¹) h1
  have h3 : (fun ω => (-(Kmat S D.J)⁻¹) *ᵥ (EV 𝔼 t (fun ω' => Mpart (x t ω')) ω +
      S.A12ᵀ *ᵥ EV 𝔼 t (Rop 𝔼 D x (t + 1)) ω)) = Qop 𝔼 D x t := by
    funext ω
    rw [neg_mulVec]
    rfl
  rw [← h3]
  exact h2

/-- Woodford (2003), **Proposition 8.1**, p. 553 (corrected, proved in general): a real
deflating pair for `n_Z` roots of (1.15) inside `|μ| < β⁻¹` (`DeflatingSplit`) yields `Λ`, `Υ`,
`Q(L⁻¹)`, `R(L⁻¹)` with bounded `(φ, τ)` (`M_t` known at `t`, adapted plans) satisfying (1.18)
for `t ≥ t₀` iff they satisfy (1.20)–(1.21); the operators preserve boundedness and are
adapted. Any expectation system. -/
noncomputable def prop81 (P : LQProblem ιZ ιz ιτ) (D : DeflatingSplit P.sys P.β)
    (𝔼 : ExpectationSystem Ω) (t0 : ℕ) : Prop81ConclusionM P 𝔼 t0 where
  Λ := Λmat P.sys P.β D.J
  Υ := Υmat P.sys D.J
  Qop := Qop 𝔼 D
  Rop := Rop 𝔼 D
  equiv := prop81_equiv P D 𝔼 t0
  Qbounded := fun _ hx => (fw_spec 𝔼 P.β_pos D hx).2.2
  Rbounded := fun _ hx => (fw_spec 𝔼 P.β_pos D hx).1
  Qadapted := qop_adapted 𝔼 D
  Radapted := fun _ hx => (fw_spec 𝔼 P.β_pos D hx).2.1

/-- Woodford (2003), Proposition 8.1, p. 553: the matrices of `prop81` are the explicit
`Λ = β⁻¹ K⁻¹ Ẽ'` and `Υ = −(J₁')⁻¹ J₂' Ẽ'`. -/
theorem prop81_matrices (P : LQProblem ιZ ιz ιτ) (D : DeflatingSplit P.sys P.β)
    (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    (prop81 P D 𝔼 t0).Λ = Λmat P.sys P.β D.J ∧ (prop81 P D 𝔼 t0).Υ = Υmat P.sys D.J :=
  ⟨rfl, rfl⟩

/-! ### Perfect foresight: the original hypothesis structure is inhabited -/

/-- Woodford (2003), Proposition 8.1, p. 553, deterministic case: under perfect foresight every
plan is adapted and every multiplier is known, so the corrected statement is the original
`Prop81Equiv`; the hypothesis structure `TargetCriterion.Prop81.Prop81Conclusion` is inhabited. -/
noncomputable def prop81_perfectForesight (P : LQProblem ιZ ιz ιτ)
    (D : DeflatingSplit P.sys P.β) (t0 : ℕ) : Prop81Conclusion P perfectForesight t0 where
  Λ := Λmat P.sys P.β D.J
  Υ := Υmat P.sys D.J
  Qop := Qop perfectForesight D
  Rop := Rop perfectForesight D
  equiv := fun y φ hy hφ =>
    prop81_equiv P D perfectForesight t0 y φ hy (fun _ _ => rfl) hφ (fun _ _ _ => rfl)
  Qbounded := fun _ hx => (fw_spec perfectForesight P.β_pos D hx).2.2
  Rbounded := fun _ hx => (fw_spec perfectForesight P.β_pos D hx).1
  Qadapted := fun _ _ _ => rfl

/-! ### `rank Λ = rank Ẽ` (fn 15) and the degree of `α(L)` (E18) -/

/-- Woodford (2003), p. 553 and fn 15, p. 554: `rank Λ = rank Ẽ` for `Λ = β⁻¹ K⁻¹ Ẽ'`
(`β ≠ 0`, `K` invertible). -/
theorem rank_Λmat (S : LinearRESystem ιZ ιz) {β : ℝ} (hβ : β ≠ 0) {J : Matrix (ιZ ⊕ ιz) ιZ ℝ}
    (hK : (Kmat S J).det ≠ 0) : (Λmat S β J).rank = S.Et.rank := by
  have hs : Λmat S β J = (β⁻¹ • (Kmat S J)⁻¹) * S.Etᵀ := by
    rw [Λmat, Matrix.smul_mul]
  have hu : IsUnit (β⁻¹ • (Kmat S J)⁻¹).det := by
    rw [det_smul, det_nonsing_inv]
    refine (IsUnit.mul (IsUnit.pow _ (Ne.isUnit (inv_ne_zero hβ))) ?_)
    exact (Ne.isUnit hK).ringInverse
  rw [hs, rank_mul_eq_right_of_isUnit_det _ _ hu, rank_transpose]

/-- Woodford (2003), p. 553 (E18, corrected and made precise): for the `Λ` of Proposition 8.1,
`deg α ≤ rank Ẽ`, where `α(L) = det(I − ΛL)`; `deg B ≤ rank Ẽ` likewise. -/
theorem natDegree_alpha_le (S : LinearRESystem ιZ ιz) {β : ℝ} (hβ : β ≠ 0)
    {J : Matrix (ιZ ⊕ ιz) ιZ ℝ} (hK : (Kmat S J).det ≠ 0) :
    (alpha (Λmat S β J)).natDegree ≤ S.Et.rank ∧
      ∀ i j, (Bpoly (Λmat S β J) i j).natDegree ≤ S.Et.rank := by
  rw [← rank_Λmat S hβ hK]
  exact ⟨natDegree_alpha_le_rank _, natDegree_Bpoly_le_rank _⟩

/-! ### The uncorrected statement fails under uncertainty -/

/-- Woodford (2003), (1.1) (a minimal instance for the counterexample to the uncorrected
Proposition 8.1, and for the one to the remark on p. 553 in `Prop81Unique`): no predetermined
variable, one forward-looking variable, `E_t z_{t+1} = 2 z_t + i_t + c_t`. -/
noncomputable def coinSys : LinearRESystem Empty Unit where
  A11 := 0
  A12 := 0
  A21 := 0
  A22 := Matrix.of fun _ _ => 2
  Et := Matrix.of fun _ _ => 1
  B2 := fun _ => 1
  A22_isUnit := by
    rw [Matrix.det_unique]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  B2_ne_zero := fun h => by simpa using congrFun h ()

/-- Woodford (2003), (1.2)–(1.4) (the counterexample): `β = 1/2`, the only target is the
instrument, `W = 1`, `τ* = 0`. -/
noncomputable def coinProblem : LQProblem Empty Unit Unit where
  sys := coinSys
  β := 1 / 2
  β_pos := by norm_num
  β_lt_one := by norm_num
  Ttil := 0
  Ti := fun _ => 1
  W := 1
  τstar := 0
  W_posDef := Matrix.PosDef.one

/-- Woodford (2003), p. 540 (the counterexample): a multiplier path with `M_{t₀-1} = 0` and
`M_t = ε₁` (the first coin flip, mean zero given date-0 information) for `t ≥ t₀ = 0`. Here
`M_0` is *not* known at date 0. -/
noncomputable def coinMult (t : ℕ) (ω : Bool × Bool) : Empty ⊕ Unit → ℝ :=
  fun _ => if 1 ≤ t then ExpectationsFiniteTree.coinShock 1 ω else 0

/-- Woodford (2003), (1.18) for the counterexample: with no predetermined variables, zero
targets (`y = 0`) and `β = 1/2`, (1.18) reads `2 E_t M_t − 2 M_{t-1} = 0`. -/
theorem coin_lhs118 (φ : ℕ → Bool × Bool → Empty ⊕ Unit → ℝ) (t : ℕ) (ω : Bool × Bool) :
    lhs118 coinProblem ExpectationsFiniteTree.coinSystem 0 φ t ω (Sum.inr ()) =
      2 * ExpectationsFiniteTree.coinSystem.E t (fun ω' => φ (t + 1) ω' (Sum.inr ())) ω -
        2 * φ t ω (Sum.inr ()) := by
  simp [lhs118, coinProblem, coinSys, xproc, LinearRESystem.Ahat, LinearRESystem.Ihat, EV,
    mulVec, dotProduct, fromBlocks]

/-- Woodford (2003), (1.18) for the counterexample: both the zero multiplier path and
`coinMult` satisfy (1.18) at every date. -/
theorem coin_eq118 (φ : ℕ → Bool × Bool → Empty ⊕ Unit → ℝ)
    (hφ : ∀ t, ExpectationsFiniteTree.coinSystem.E t (fun ω' => φ (t + 1) ω' (Sum.inr ())) =
      fun ω => φ t ω (Sum.inr ())) :
    Eq118 coinProblem ExpectationsFiniteTree.coinSystem 0 0 φ := by
  intro t _ ω
  change lhs118 coinProblem ExpectationsFiniteTree.coinSystem 0 φ t ω = 0
  funext a
  rcases a with e | u
  · exact e.elim
  · rw [coin_lhs118, hφ t]
    simp

/-- Woodford (2003), p. 540 (the counterexample): `E_t M_t = M_{t-1}` for `coinMult`: at
`t = 0`, `E_0 ε₁ = 0`; for `t ≥ 1`, `ε₁` is known. -/
theorem coinMult_E (t : ℕ) :
    ExpectationsFiniteTree.coinSystem.E t (fun ω' => coinMult (t + 1) ω' (Sum.inr ())) =
      fun ω => coinMult t ω (Sum.inr ()) := by
  have h1 : (fun ω' => coinMult (t + 1) ω' (Sum.inr ())) =
      ExpectationsFiniteTree.coinShock 1 := by
    funext ω'
    simp [coinMult]
  rw [h1]
  rcases Nat.eq_zero_or_pos t with h | h
  · subst h
    have := ExpectationsFiniteTree.coinShock_mean_zero 0
    rw [this]
    funext ω
    simp [coinMult]
  · funext ω
    rw [ExpectationsFiniteTree.coinSystem,
      ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
    simp only [coinMult, show 1 ≤ t by omega, ↓reduceIte]
    exact ExpectationsFiniteTree.coinTree.condE_of_const_on_cell fun ω' hω' =>
      ExpectationsFiniteTree.coinShock_measurable 1
        (ExpectationsFiniteTree.coinTree.refines (show 1 ≤ t by omega) ω' ω hω')

/-- Woodford (2003), Proposition 8.1, p. 553 (**the uncorrected equivalence is false under
uncertainty**): on the coin-flip tree, for the problem `coinProblem`, there are no `Λ`, `Υ`,
`Q`, `R` whatsoever such that all bounded `(φ, τ)` satisfy (1.18) iff (1.20)–(1.21). The zero
multipliers and `coinMult` (whose `M_0 = ε₁` is not known at date 0) both satisfy (1.18) with
the same targets, but (1.20) at `t = 0` would force `ε₁ = q_0 = 0`. -/
theorem not_prop81Equiv_coin (Λ : Matrix Unit Unit ℝ) (Υ : Matrix Empty Unit ℝ)
    (Qop : (ℕ → Bool × Bool → Empty ⊕ Unit → ℝ) → ℕ → Bool × Bool → Unit → ℝ)
    (Rop : (ℕ → Bool × Bool → Empty ⊕ Unit → ℝ) → ℕ → Bool × Bool → Empty → ℝ) :
    ¬ Prop81Equiv coinProblem ExpectationsFiniteTree.coinSystem 0 Λ Υ Qop Rop := by
  intro h
  have hy : BoundedV (0 : ℕ → Bool × Bool → (Empty ⊕ Unit) ⊕ Unit → ℝ) := ⟨0, by simp⟩
  have hb0 : BoundedV (0 : ℕ → Bool × Bool → Empty ⊕ Unit → ℝ) := ⟨0, by simp⟩
  have hb1 : BoundedV coinMult := by
    refine ⟨1, fun t ω a => ?_⟩
    simp only [coinMult, ExpectationsFiniteTree.coinShock]
    split_ifs <;> norm_num
  have hz : ∀ t, ExpectationsFiniteTree.coinSystem.E t
      (fun ω' => (0 : ℕ → Bool × Bool → Empty ⊕ Unit → ℝ) (t + 1) ω' (Sum.inr ())) =
      fun ω => (0 : ℕ → Bool × Bool → Empty ⊕ Unit → ℝ) t ω (Sum.inr ()) :=
    fun t => ExpectationsFiniteTree.coinSystem.const t 0
  have h0 := ((h 0 0 hy hb0).mp (coin_eq118 0 hz)).1 0 le_rfl (true, true)
  have h1 := ((h 0 coinMult hy hb1).mp (coin_eq118 coinMult coinMult_E)).1 0 le_rfl (true, true)
  have hm0 : Mpart (coinMult 0 (true, true)) = 0 := by
    funext r
    simp [Mpart, coinMult]
  have hm00 : Mpart ((0 : ℕ → Bool × Bool → Empty ⊕ Unit → ℝ) 0 (true, true)) = 0 := rfl
  have hm01 : Mpart ((0 : ℕ → Bool × Bool → Empty ⊕ Unit → ℝ) (0 + 1) (true, true)) = 0 := rfl
  have hm1 : Mpart (coinMult (0 + 1) (true, true)) = fun _ => 1 := by
    funext r
    simp [Mpart, coinMult, ExpectationsFiniteTree.coinShock]
  rw [hm00, hm01, mulVec_zero, zero_add] at h0
  rw [hm0, hm1, mulVec_zero, zero_add, ← h0] at h1
  have := congrFun h1 ()
  norm_num at this

/-- Woodford (2003), Proposition 8.1 (the hypothesis structure of `TargetCriterion`): on the
coin-flip tree it is uninhabited for `coinProblem`. -/
theorem prop81Conclusion_coin_isEmpty :
    IsEmpty (Prop81Conclusion coinProblem ExpectationsFiniteTree.coinSystem 0) :=
  ⟨fun H => not_prop81Equiv_coin H.Λ H.Υ H.Qop H.Rop H.equiv⟩

/-- Woodford (2003), App. G.1 (the counterexample has `n_Z = 0`): the empty deflating pair. -/
noncomputable def coinSplit : DeflatingSplit coinProblem.sys coinProblem.β where
  J := 0
  Ψ := 0
  deflate := by
    ext i j
    exact j.elim
  eig_lt := fun μ h => by simp at h
  J1_det := by simp
  K_det := by
    change (Kmat coinSys 0).det ≠ 0
    rw [Matrix.det_unique]
    simp [Kmat, coinSys]

/-- Woodford (2003), Proposition 8.1 (corrected): for the same problem on the same tree the
corrected statement (multipliers `M_t` known at `t`) holds. -/
noncomputable def prop81M_coin :
    Prop81ConclusionM coinProblem ExpectationsFiniteTree.coinSystem 0 :=
  prop81 coinProblem coinSplit ExpectationsFiniteTree.coinSystem 0

end Woodford.OptimalPolicyRules.Prop81General
