/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.Expectations
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic

/-!
# The general linear-quadratic policy problem

Woodford (2003), *Interest and Prices*, Chapter 8, Sections 1.1–1.3 (pp. 536–550).

Giannoni and Woodford's general problem has structural equations (1.1)
`Î [Z_{t+1}; E_t z_{t+1}] = A [Z_t; z_t] + B i_t + C s_t`, with `n_Z` predetermined variables
`Z`, `n_z` forward-looking variables `z` and an instrument `i`, and a discounted quadratic loss
(1.2)–(1.4) `E_{t₀} ∑ β^{t-t₀} ½ (τ_t − τ*)' W (τ_t − τ*)`, `τ_t = T y_t`, `y = (Z, z, i)`.

## Modelling choices

* Vector-valued processes are `ℕ → Ω → (ι → ℝ)`; conditional expectations act componentwise
  (`EV`). Every definition is for an arbitrary `ExpectationSystem`.
* The (possibly infinite-dimensional) disturbance vector `s_t` enters only through `C s_t`
  (Woodford's fn 4), so the disturbance is the bounded adapted `ℝ^{n_z}`-valued process
  `c_t = C₂ s_t` (the upper block of `C` is zero, p. 537).
* The constraints are stated both in Woodford's block form (`Structural`) and in the abstract
  form `Ĩ y_{t+1} = Ã y_t + c_t` with the last block holding in conditional expectation
  (`ConstraintsHold`); `structural_iff` shows they agree. The abstract form is what the
  Lagrangian-sufficiency theorem of `GeneralFOC` uses.

## Main definitions

* `LinearRESystem`, `LQProblem`: (1.1)–(1.4), with `W ≻ 0`, `A₂₂` invertible, `B₂ ≠ 0`.
* `Feasible`, `OptimalSubjectTo`, `T0Optimal`, `TimelesslyOptimalPlan`: the definitions of
  t₀-optimality and of optimality from a timeless perspective, (1.5)–(1.6), p. 538.
* `PolicyRule` (1.13) with `IsExplicitInstrumentRule`, `IsImplicitInstrumentRule`,
  `IsTargetingRule`; `RuleDeterminate` (the definition of determinacy, p. 546, for the
  augmented system (1.14)); `RobustlyOptimal` (p. 549, (1.16)).
* `pencilPoly`, `stableCount`, `SargentWallace`: (1.15) and the Sargent–Wallace property
  (p. 547); `Assumption82Count`, `Assumption87`.

## Main results

* `structural_iff`: (1.1) in block form is the abstract constraint system.
* `rule_trichotomy`: every well-formed rule (1.13) is exactly one of an explicit instrument
  rule, an implicit instrument rule, or a targeting rule (pp. 544–545).
* `sargentWallace_assumption82`, `sargentWallace_assumption87`: the Sargent–Wallace property
  implies the first part of Assumption 8.2 (p. 552) and Assumption 8.7 (p. 556).
-/

namespace Woodford.OptimalPolicyRules.GeneralSetup

open Matrix Polynomial

variable {Ω : Type*}

/-! ### Vector-valued processes -/

/-- Woodford (2003), p. 540: the conditional expectation `E_t` applied componentwise to a
random vector. -/
def EV (𝔼 : ExpectationSystem Ω) {ι : Type*} (t : ℕ) (x : Ω → ι → ℝ) : Ω → ι → ℝ :=
  fun ω i => 𝔼.E t (fun ω' => x ω' i) ω

/-- Woodford (2003), p. 540: a random vector is known at date `t` (measurable with respect to
date-`t` information) when `E_t` leaves each component unchanged. -/
def KnownV (𝔼 : ExpectationSystem Ω) {ι : Type*} (t : ℕ) (x : Ω → ι → ℝ) : Prop :=
  ∀ i, 𝔼.E t (fun ω => x ω i) = fun ω => x ω i

/-- Woodford (2003), p. 537: an adapted vector process (`x_t` known at `t`). -/
def AdaptedV (𝔼 : ExpectationSystem Ω) {ι : Type*} (x : ℕ → Ω → ι → ℝ) : Prop :=
  ∀ t, KnownV 𝔼 t (x t)

/-- Woodford (2003), p. 546 and fn 6, p. 539: a uniformly bounded vector process. -/
def BoundedV {ι : Type*} (x : ℕ → Ω → ι → ℝ) : Prop := ∃ M, ∀ t ω i, |x t ω i| ≤ M

/-- Woodford (2003), p. 540: `E_t` of a finite linear combination of random variables. -/
theorem E_sum_mul (𝔼 : ExpectationSystem Ω) {ι : Type*} [Fintype ι] (t : ℕ) (a : ι → ℝ)
    (f : ι → Ω → ℝ) :
    𝔼.E t (fun ω => ∑ i, a i * f i ω) = fun ω => ∑ i, a i * 𝔼.E t (f i) ω := by
  have h : (fun ω => ∑ i, a i * f i ω) = ∑ i, a i • f i := by
    funext ω
    simp [Finset.sum_apply]
  rw [h, map_sum]
  funext ω
  simp [Finset.sum_apply, map_smul]

/-- Woodford (2003), p. 540: `E_t` commutes with a constant matrix, `E_t (A x) = A E_t x`. -/
theorem EV_mulVec (𝔼 : ExpectationSystem Ω) {ι κ : Type*} [Fintype ι] (t : ℕ)
    (A : Matrix κ ι ℝ) (x : Ω → ι → ℝ) :
    EV 𝔼 t (fun ω => A *ᵥ x ω) = fun ω => A *ᵥ EV 𝔼 t x ω := by
  funext ω k
  have := congrFun (E_sum_mul 𝔼 t (A k) (fun i ω => x ω i)) ω
  simpa [EV, mulVec, dotProduct] using this

/-- Woodford (2003), p. 540: a known random vector is its own conditional expectation. -/
theorem EV_of_known (𝔼 : ExpectationSystem Ω) {ι : Type*} {t : ℕ} {x : Ω → ι → ℝ}
    (hx : KnownV 𝔼 t x) : EV 𝔼 t x = x := by
  funext ω i
  exact congrFun (hx i) ω

/-- Woodford (2003), p. 540: information accumulates — what is known at `s` is known at every
`t ≥ s`. -/
theorem KnownV.mono (𝔼 : ExpectationSystem Ω) {ι : Type*} {s t : ℕ} (hst : s ≤ t)
    {x : Ω → ι → ℝ} (hx : KnownV 𝔼 s x) : KnownV 𝔼 t x := by
  intro i
  have h := 𝔼.known hst (fun ω => x ω i)
  rw [hx i] at h
  exact h

/-! ### The linear-quadratic problem (1.1)–(1.4) -/

variable (ιZ ιz ιτ : Type*) [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιz]

/-- Woodford (2003), eq. (1.1), p. 537: the structural equations
`Î [Z_{t+1}; E_t z_{t+1}] = A [Z_t; z_t] + B i_t + C s_t` with `Î = diag(I, Ẽ)`,
`A = [A₁₁ A₁₂; A₂₁ A₂₂]`, `B = [0; B₂]`. Woodford assumes `B₂ ≠ 0` (the instrument matters) and
`A₂₂` nonsingular. -/
structure LinearRESystem where
  A11 : Matrix ιZ ιZ ℝ
  A12 : Matrix ιZ ιz ℝ
  A21 : Matrix ιz ιZ ℝ
  A22 : Matrix ιz ιz ℝ
  Et : Matrix ιz ιz ℝ
  B2 : ιz → ℝ
  A22_isUnit : IsUnit A22.det
  B2_ne_zero : B2 ≠ 0

/-- Woodford (2003), eqs. (1.1)–(1.4), pp. 537–538: the linear-quadratic policy problem: the
structural equations, a discount factor `0 < β < 1`, target variables `τ_t = T y_t` with
`T = [T̃ T_i]` (p. 553) and a period loss `½ (τ_t − τ*)' W (τ_t − τ*)` with `W` symmetric
positive definite. -/
structure LQProblem where
  sys : LinearRESystem ιZ ιz
  β : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  Ttil : Matrix ιτ (ιZ ⊕ ιz) ℝ
  Ti : ιτ → ℝ
  W : Matrix ιτ ιτ ℝ
  τstar : ιτ → ℝ
  W_posDef : W.PosDef

variable {ιZ ιz ιτ}

/-- Woodford (2003), p. 538: the predetermined block `Z` of `y = (Z, z, i)`. -/
def Zpart (v : (ιZ ⊕ ιz) ⊕ Unit → ℝ) : ιZ → ℝ := fun j => v (Sum.inl (Sum.inl j))

/-- Woodford (2003), p. 538: the forward-looking block `z` of `y = (Z, z, i)`. -/
def zpart (v : (ιZ ⊕ ιz) ⊕ Unit → ℝ) : ιz → ℝ := fun j => v (Sum.inl (Sum.inr j))

/-- Woodford (2003), p. 538: the instrument `i` in `y = (Z, z, i)`. -/
def ipart (v : (ιZ ⊕ ιz) ⊕ Unit → ℝ) : ℝ := v (Sum.inr ())

namespace LinearRESystem

variable (S : LinearRESystem ιZ ιz)

/-- Woodford (2003), p. 537: the matrix `A = [A₁₁ A₁₂; A₂₁ A₂₂]` of (1.1). -/
def Ahat : Matrix (ιZ ⊕ ιz) (ιZ ⊕ ιz) ℝ := fromBlocks S.A11 S.A12 S.A21 S.A22

/-- Woodford (2003), p. 537: the matrix `Î = diag(I, Ẽ)` of (1.1). -/
def Ihat [DecidableEq ιZ] : Matrix (ιZ ⊕ ιz) (ιZ ⊕ ιz) ℝ := fromBlocks 1 0 0 S.Et

/-- Woodford (2003), p. 537: the vector `B = [0; B₂]` of (1.1). -/
def Bvec : ιZ ⊕ ιz → ℝ := Sum.elim 0 S.B2

/-- Woodford (2003), p. 540: `Ã ≡ [A B]`. -/
def Atil : Matrix (ιZ ⊕ ιz) ((ιZ ⊕ ιz) ⊕ Unit) ℝ :=
  fromCols S.Ahat (Matrix.of fun r (_ : Unit) => S.Bvec r)

/-- Woodford (2003), p. 540: `Ĩ ≡ [Î 0]`. -/
def Itil [DecidableEq ιZ] : Matrix (ιZ ⊕ ιz) ((ιZ ⊕ ιz) ⊕ Unit) ℝ := fromCols S.Ihat 0

/-- Woodford (2003), p. 540: `Ĩ y = (Z, Ẽ z)`. -/
theorem Itil_mulVec [DecidableEq ιZ] (v : (ιZ ⊕ ιz) ⊕ Unit → ℝ) :
    S.Itil *ᵥ v = Sum.elim (Zpart v) (S.Et *ᵥ zpart v) := by
  funext r
  rcases r with r | r
  · simp [Itil, Ihat, fromBlocks_mulVec, Zpart, Function.comp_def]
  · simp [Itil, Ihat, fromBlocks_mulVec, Function.comp_def]
    rfl

/-- Woodford (2003), p. 540: `Ã y = A (Z, z) + B i`, by blocks. -/
theorem Atil_mulVec (v : (ιZ ⊕ ιz) ⊕ Unit → ℝ) :
    S.Atil *ᵥ v = Sum.elim (S.A11 *ᵥ Zpart v + S.A12 *ᵥ zpart v)
      (S.A21 *ᵥ Zpart v + S.A22 *ᵥ zpart v + ipart v • S.B2) := by
  funext r
  rcases r with r | r
  · simp [Atil, Ahat, Bvec, Zpart, zpart, mulVec, dotProduct]
  · simp [Atil, Ahat, Bvec, Zpart, zpart, ipart, mulVec, dotProduct, mul_comm]

/-- Woodford (2003), eq. (1.1), p. 537, in block form, for all `t ≥ t₀`: the predetermined
block `Z_{t+1} = A₁₁ Z_t + A₁₂ z_t` and the expectational block
`Ẽ E_t z_{t+1} = A₂₁ Z_t + A₂₂ z_t + B₂ i_t + c_t` (`c_t = C₂ s_t`). -/
def Structural (𝔼 : ExpectationSystem Ω) (c : ℕ → Ω → ιz → ℝ) (t0 : ℕ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : Prop :=
  ∀ t, t0 ≤ t → ∀ ω,
    Zpart (y (t + 1) ω) = S.A11 *ᵥ Zpart (y t ω) + S.A12 *ᵥ zpart (y t ω) ∧
    S.Et *ᵥ EV 𝔼 t (fun ω' => zpart (y (t + 1) ω')) ω =
      S.A21 *ᵥ Zpart (y t ω) + S.A22 *ᵥ zpart (y t ω) + ipart (y t ω) • S.B2 + c t ω

end LinearRESystem

/-- Woodford (2003), eq. (1.1) and the Lagrangian (1.7), p. 540, in abstract form: rows
`ρ₁ ⊕ ρ₂`; the `ρ₁` rows `(Ĩ y_{t+1})_r = (Ã y_t)_r + c_{t,r}` hold exactly and the `ρ₂` rows
hold in conditional expectation, `E_t (Ĩ y_{t+1})_r = (Ã y_t)_r + c_{t,r}`, for all `t ≥ t₀`. -/
def ConstraintsHold {ρ₁ ρ₂ ν : Type*} [Fintype ν] (𝔼 : ExpectationSystem Ω)
    (Atil Itil : Matrix (ρ₁ ⊕ ρ₂) ν ℝ) (cf : ℕ → Ω → ρ₁ ⊕ ρ₂ → ℝ) (t0 : ℕ)
    (y : ℕ → Ω → ν → ℝ) : Prop :=
  ∀ t, t0 ≤ t → ∀ ω,
    (∀ r, (Itil *ᵥ y (t + 1) ω) (Sum.inl r) = (Atil *ᵥ y t ω) (Sum.inl r) + cf t ω (Sum.inl r)) ∧
    ∀ r, EV 𝔼 t (fun ω' => Itil *ᵥ y (t + 1) ω') ω (Sum.inr r) =
      (Atil *ᵥ y t ω) (Sum.inr r) + cf t ω (Sum.inr r)

/-- Woodford (2003), p. 537: the disturbance enters only the expectational rows (`C = [0; C₂]`). -/
def liftDist (c : ℕ → Ω → ιz → ℝ) : ℕ → Ω → ιZ ⊕ ιz → ℝ :=
  fun t ω => Sum.elim 0 (c t ω)

/-- Woodford (2003), eq. (1.1) and p. 540: the block form of (1.1) is the abstract constraint
system `Ĩ y_{t+1} = Ã y_t + c_t` with expectations on the `z` rows. -/
theorem structural_iff [DecidableEq ιZ] (S : LinearRESystem ιZ ιz) (𝔼 : ExpectationSystem Ω)
    (c : ℕ → Ω → ιz → ℝ) (t0 : ℕ) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) :
    S.Structural 𝔼 c t0 y ↔ ConstraintsHold 𝔼 S.Atil S.Itil (liftDist c) t0 y := by
  have hE : ∀ t ω, EV 𝔼 t (fun ω' => S.Itil *ᵥ y (t + 1) ω') ω =
      Sum.elim (EV 𝔼 t (fun ω' => Zpart (y (t + 1) ω')) ω)
        (S.Et *ᵥ EV 𝔼 t (fun ω' => zpart (y (t + 1) ω')) ω) := by
    intro t ω
    funext r
    rcases r with r | r
    · simp [EV, S.Itil_mulVec]
    · have := congrFun (congrFun (EV_mulVec 𝔼 t S.Et (fun ω' => zpart (y (t + 1) ω'))) ω) r
      simpa [EV, S.Itil_mulVec] using this
  constructor
  · intro h t ht ω
    refine ⟨fun r => ?_, fun r => ?_⟩
    · have := congrFun (h t ht ω).1 r
      simpa [S.Itil_mulVec, S.Atil_mulVec, liftDist] using this
    · have := congrFun (h t ht ω).2 r
      rw [hE]
      simpa [S.Atil_mulVec, liftDist] using this
  · intro h t ht ω
    refine ⟨funext fun r => ?_, funext fun r => ?_⟩
    · have := (h t ht ω).1 r
      simpa [S.Itil_mulVec, S.Atil_mulVec, liftDist] using this
    · have := (h t ht ω).2 r
      rw [hE] at this
      simpa [S.Atil_mulVec, liftDist] using this

namespace LQProblem

variable (P : LQProblem ιZ ιz ιτ)

/-- Woodford (2003), p. 553: `T ≡ [T̃ T_i]`, so `τ_t = T y_t` (1.4). -/
def T : Matrix ιτ ((ιZ ⊕ ιz) ⊕ Unit) ℝ := fromCols P.Ttil (Matrix.of fun a (_ : Unit) => P.Ti a)

/-- Woodford (2003), eq. (1.3), p. 537: the period loss `L(y) = ½ (Ty − τ*)' W (Ty − τ*)`. -/
noncomputable def loss (v : (ιZ ⊕ ιz) ⊕ Unit → ℝ) : ℝ :=
  (1 / 2) * ((P.T *ᵥ v - P.τstar) ⬝ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar)))

/-- Woodford (2003), eq. (1.2), p. 537: the discounted expected loss
`E_{t₀} ∑_{k ≥ 0} β^k L(y_{t₀+k})` (a genuine infinite sum; for bounded plans it converges,
see `GeneralFOC`). -/
noncomputable def J (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : Ω → ℝ :=
  𝔼.E t0 (fun ω => ∑' k, P.β ^ k * P.loss (y (t0 + k) ω))

/-- Woodford (2003), pp. 538–539 and fn 6: a feasible plan from `t₀`: a bounded adapted
process satisfying (1.1) for all `t ≥ t₀` and the initial condition `Z_{t₀} = Z₀`. -/
def Feasible (𝔼 : ExpectationSystem Ω) (c : ℕ → Ω → ιz → ℝ) (t0 : ℕ) (Z0 : Ω → ιZ → ℝ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : Prop :=
  P.sys.Structural 𝔼 c t0 y ∧ (∀ ω, Zpart (y t0 ω) = Z0 ω) ∧ BoundedV y ∧ AdaptedV 𝔼 y

/-- Woodford (2003), p. 539 and (1.6): `y` minimises (1.2) among bounded feasible plans subject
to the additional initial constraints `Ẽ z_{t₀} = ē`. -/
def OptimalSubjectTo (𝔼 : ExpectationSystem Ω) (c : ℕ → Ω → ιz → ℝ) (t0 : ℕ)
    (Z0 : Ω → ιZ → ℝ) (ebar : Ω → ιz → ℝ) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : Prop :=
  P.Feasible 𝔼 c t0 Z0 y ∧ (∀ ω, P.sys.Et *ᵥ zpart (y t0 ω) = ebar ω) ∧
    ∀ y', P.Feasible 𝔼 c t0 Z0 y' → (∀ ω, P.sys.Et *ᵥ zpart (y' t0 ω) = ebar ω) →
      ∀ ω, P.J 𝔼 t0 y ω ≤ P.J 𝔼 t0 y' ω

/-- Woodford (2003), p. 541 and fn 7: the `t₀`-optimal plan minimises (1.2) among all bounded
feasible plans, with no constraint on `z_{t₀}`. -/
def T0Optimal (𝔼 : ExpectationSystem Ω) (c : ℕ → Ω → ιz → ℝ) (t0 : ℕ) (Z0 : Ω → ιZ → ℝ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : Prop :=
  P.Feasible 𝔼 c t0 Z0 y ∧
    ∀ y', P.Feasible 𝔼 c t0 Z0 y' → ∀ ω, P.J 𝔼 t0 y ω ≤ P.J 𝔼 t0 y' ω

/-- Woodford (2003), Definition, pp. 538–539, (1.5)–(1.6): an equilibrium plan is optimal from
a timeless perspective when (1) `z_t = f⁰ + F X̄_t` for all `t ≥ t₀`, a time-invariant function
of a state vector `X̄_t` (Woodford's `(Z̄_t, s̄_t)`, which may contain extra predetermined and
exogenous variables, fn 5), and (2) it minimises (1.2) among bounded feasible plans subject to
`Ẽ z_{t₀} = ē ≡ Ẽ (f⁰ + F X̄_{t₀})`. -/
def TimelesslyOptimalPlan {κ : Type*} [Fintype κ] (𝔼 : ExpectationSystem Ω)
    (c : ℕ → Ω → ιz → ℝ) (t0 : ℕ) (Z0 : Ω → ιZ → ℝ) (Xbar : ℕ → Ω → κ → ℝ) (f0 : ιz → ℝ)
    (F : Matrix ιz κ ℝ) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : Prop :=
  (∀ t, t0 ≤ t → ∀ ω, zpart (y t ω) = f0 + F *ᵥ Xbar t ω) ∧
    P.OptimalSubjectTo 𝔼 c t0 Z0 (fun ω => P.sys.Et *ᵥ (f0 + F *ᵥ Xbar t0 ω)) y

/-- Woodford (2003), p. 539: a plan that is optimal from a timeless perspective is in
particular optimal subject to its own initial constraint (1.6). -/
theorem TimelesslyOptimalPlan.optimalSubjectTo {κ : Type*} [Fintype κ]
    {𝔼 : ExpectationSystem Ω} {c : ℕ → Ω → ιz → ℝ} {t0 : ℕ} {Z0 : Ω → ιZ → ℝ}
    {Xbar : ℕ → Ω → κ → ℝ} {f0 : ιz → ℝ} {F : Matrix ιz κ ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (h : P.TimelesslyOptimalPlan 𝔼 c t0 Z0 Xbar f0 F y) :
    P.OptimalSubjectTo 𝔼 c t0 Z0 (fun ω => P.sys.Et *ᵥ zpart (y t0 ω)) y := by
  have he : (fun ω => P.sys.Et *ᵥ zpart (y t0 ω)) =
      fun ω => P.sys.Et *ᵥ (f0 + F *ᵥ Xbar t0 ω) := by
    funext ω
    rw [h.1 t0 le_rfl ω]
  rw [he]
  exact h.2

/-- Woodford (2003), p. 539: the `t₀`-optimal plan is also optimal subject to the initial
constraint `Ẽ z_{t₀} = ē` with `ē` its own value: adding a constraint the plan satisfies cannot
make it worse. -/
theorem T0Optimal.optimalSubjectTo {𝔼 : ExpectationSystem Ω} {c : ℕ → Ω → ιz → ℝ}
    {t0 : ℕ} {Z0 : Ω → ιZ → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (h : P.T0Optimal 𝔼 c t0 Z0 y) :
    P.OptimalSubjectTo 𝔼 c t0 Z0 (fun ω => P.sys.Et *ᵥ zpart (y t0 ω)) y :=
  ⟨h.1, fun _ => rfl, fun y' hy' _ => h.2 y' hy'⟩

end LQProblem

/-! ### Policy rules (1.13), determinacy (1.14) and robustness (1.16) -/

variable (κz κZ κs : Type*)

/-- Woodford (2003), eq. (1.13), p. 543: a time-invariant rule
`φ_i i_t + φ_z z̄_t + φ_Z Z̄_t + φ_s s̄_t = φ̄`, where `z̄`, `Z̄`, `s̄` are (possibly augmented)
vectors of forward-looking, predetermined and exogenous variables. -/
structure PolicyRule where
  φi : ℝ
  φz : κz → ℝ
  φZ : κZ → ℝ
  φs : κs → ℝ
  φbar : ℝ

variable {κz κZ κs}

namespace PolicyRule

variable (R : PolicyRule κz κZ κs)

/-- Woodford (2003), eq. (1.13): the rule holds at a date with instrument `i`, forward-looking
vector `z̄`, predetermined vector `Z̄` and exogenous vector `s̄`. -/
def Holds [Fintype κz] [Fintype κZ] [Fintype κs] (i : ℝ) (zb : κz → ℝ) (Zb : κZ → ℝ)
    (sb : κs → ℝ) : Prop :=
  R.φi * i + R.φz ⬝ᵥ zb + R.φZ ⬝ᵥ Zb + R.φs ⬝ᵥ sb = R.φbar

/-- Woodford (2003), p. 544: the rule constrains date-`t` outcomes: `φ_i ≠ 0` or `φ_z ≠ 0`. -/
def WellFormed : Prop := R.φi ≠ 0 ∨ R.φz ≠ 0

/-- Woodford (2003), p. 544: an explicit instrument rule (`φ_i ≠ 0`, `φ_z = 0`). -/
def IsExplicitInstrumentRule : Prop := R.φi ≠ 0 ∧ R.φz = 0

/-- Woodford (2003), p. 544: an implicit instrument rule (`φ_i ≠ 0`, `φ_z ≠ 0`). -/
def IsImplicitInstrumentRule : Prop := R.φi ≠ 0 ∧ R.φz ≠ 0

/-- Woodford (2003), p. 545: a (pure) targeting rule (`φ_i = 0`, `φ_z ≠ 0`). -/
def IsTargetingRule : Prop := R.φi = 0 ∧ R.φz ≠ 0

/-- Woodford (2003), pp. 544–545: a well-formed rule (1.13) is exactly one of an explicit
instrument rule, an implicit instrument rule, or a targeting rule. -/
theorem rule_trichotomy (h : R.WellFormed) :
    (R.IsExplicitInstrumentRule ∧ ¬ R.IsImplicitInstrumentRule ∧ ¬ R.IsTargetingRule) ∨
    (¬ R.IsExplicitInstrumentRule ∧ R.IsImplicitInstrumentRule ∧ ¬ R.IsTargetingRule) ∨
    (¬ R.IsExplicitInstrumentRule ∧ ¬ R.IsImplicitInstrumentRule ∧ R.IsTargetingRule) := by
  unfold IsExplicitInstrumentRule IsImplicitInstrumentRule IsTargetingRule
  by_cases hi : R.φi = 0 <;> by_cases hz : R.φz = 0 <;> simp_all [WellFormed]

/-- Woodford (2003), p. 544: an explicit instrument rule can be solved for the instrument as a
function of predetermined and exogenous variables alone,
`i_t = φ_i⁻¹ (φ̄ − φ_Z Z̄_t − φ_s s̄_t)`. -/
theorem explicit_solve [Fintype κz] [Fintype κZ] [Fintype κs] (h : R.IsExplicitInstrumentRule)
    (i : ℝ) (zb : κz → ℝ) (Zb : κZ → ℝ)
    (sb : κs → ℝ) : R.Holds i zb Zb sb ↔ i = R.φi⁻¹ * (R.φbar - R.φZ ⬝ᵥ Zb - R.φs ⬝ᵥ sb) := by
  unfold Holds
  rw [h.2, zero_dotProduct]
  constructor
  · intro hh
    field_simp [h.1]
    linarith
  · intro hh
    rw [hh]
    field_simp [h.1]
    ring

/-- Woodford (2003), eq. (1.14) and the Definition on p. 546: commitment to the rule (1.13),
adjoined to the augmented structural system `S̄` (whose variables are `(Z̄, z̄, i)`), implies a
determinate equilibrium if for all bounded adapted disturbances `c̄`, `s̄` and every initial
condition `Z̄_{t₀}` known at `t₀` there is exactly one bounded adapted solution for `t ≥ t₀`. -/
def RuleDeterminate [Fintype κz] [Fintype κZ] [Fintype κs] [DecidableEq κZ] [DecidableEq κz]
    (Sb : LinearRESystem κZ κz)
    (𝔼 : ExpectationSystem Ω) (t0 : ℕ) : Prop :=
  ∀ (cb : ℕ → Ω → κz → ℝ) (sb : ℕ → Ω → κs → ℝ) (Z0 : Ω → κZ → ℝ),
    BoundedV cb → AdaptedV 𝔼 cb → BoundedV sb → AdaptedV 𝔼 sb → KnownV 𝔼 t0 Z0 →
    ∃ y : ℕ → Ω → (κZ ⊕ κz) ⊕ Unit → ℝ,
      (Sb.Structural 𝔼 cb t0 y ∧ (∀ ω, Zpart (y t0 ω) = Z0 ω) ∧ BoundedV y ∧ AdaptedV 𝔼 y ∧
        ∀ t, t0 ≤ t → ∀ ω, R.Holds (ipart (y t ω)) (zpart (y t ω)) (Zpart (y t ω)) (sb t ω)) ∧
      ∀ y' : ℕ → Ω → (κZ ⊕ κz) ⊕ Unit → ℝ,
        Sb.Structural 𝔼 cb t0 y' → (∀ ω, Zpart (y' t0 ω) = Z0 ω) → BoundedV y' →
        AdaptedV 𝔼 y' →
        (∀ t, t0 ≤ t → ∀ ω, R.Holds (ipart (y' t ω)) (zpart (y' t ω)) (Zpart (y' t ω)) (sb t ω)) →
        ∀ t, t0 ≤ t → y' t = y t

end PolicyRule

/-- Woodford (2003), Definition, pp. 549–550, (1.16): a time-invariant rule (a commitment `Rl`
relating a plan to the disturbances) is robustly optimal if, for every bounded adapted
disturbance process (this covers every composite MA(∞) disturbance (1.16) with bounded
mean-zero innovations, whatever its coefficients and innovation laws) and every initial
condition, it determines a unique bounded equilibrium and that equilibrium is optimal from a
timeless perspective. -/
def RobustlyOptimal {κ : Type*} [Fintype κ] (P : LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω)
    (t0 : ℕ) (Rl : (ℕ → Ω → ιz → ℝ) → (ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) → Prop)
    (Xbar : (ℕ → Ω → ιz → ℝ) → (ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) → ℕ → Ω → κ → ℝ) : Prop :=
  ∀ (c : ℕ → Ω → ιz → ℝ) (Z0 : Ω → ιZ → ℝ), BoundedV c → AdaptedV 𝔼 c → KnownV 𝔼 t0 Z0 →
    ∃ y, P.Feasible 𝔼 c t0 Z0 y ∧ Rl c y ∧
      (∀ y', P.Feasible 𝔼 c t0 Z0 y' → Rl c y' → ∀ t, t0 ≤ t → y' t = y t) ∧
      ∃ (f0 : ιz → ℝ) (F : Matrix ιz κ ℝ), P.TimelesslyOptimalPlan 𝔼 c t0 Z0 (Xbar c y) f0 F y

/-! ### The characteristic polynomial (1.15) and the Sargent–Wallace property -/

namespace LinearRESystem

variable (S : LinearRESystem ιZ ιz)

/-- Woodford (2003), eq. (1.15), p. 546: the characteristic polynomial `det [A − μ Î]` (over
`ℂ`). -/
noncomputable def pencilPoly [DecidableEq ιZ] : ℂ[X] :=
  (S.Ahat.map (fun a => Polynomial.C (a : ℂ)) -
    (Polynomial.X : ℂ[X]) • S.Ihat.map (fun a => Polynomial.C (a : ℂ))).det

/-- Woodford (2003), pp. 547, 552, 556: the number of roots of (1.15) with `|μ| < b`, where the
zero root is counted `n − rank A` times (the convention of p. 547) and nonzero roots are counted
with multiplicity. -/
noncomputable def stableCount [DecidableEq ιZ] (b : ℝ) : ℕ :=
  (Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank) +
    Multiset.card (S.pencilPoly.roots.filter (fun μ => μ ≠ 0 ∧ ‖μ‖ < b))

/-- Woodford (2003), Definition, p. 547: the Sargent–Wallace property — (1.15) has more than
`n_Z` roots with `|μ| < 1`. -/
def SargentWallace [DecidableEq ιZ] : Prop := Fintype.card ιZ < S.stableCount 1

/-- Woodford (2003), Assumption 8.2 (first part), p. 552: (1.15) has at least `n_Z` roots with
`|μ| < β⁻¹`. -/
def Assumption82Count [DecidableEq ιZ] (β : ℝ) : Prop := Fintype.card ιZ ≤ S.stableCount β⁻¹

/-- Woodford (2003), Assumption 8.7, p. 556: (1.15) has `n_Z + m` roots with `|μ| < β⁻¹` for
some `m ≥ 1`. -/
def Assumption87 [DecidableEq ιZ] (β : ℝ) : Prop :=
  ∃ m, 1 ≤ m ∧ S.stableCount β⁻¹ = Fintype.card ιZ + m

/-- Woodford (2003), pp. 547, 552: the root count is monotone in the radius. -/
theorem stableCount_mono [DecidableEq ιZ] {b b' : ℝ} (h : b ≤ b') :
    S.stableCount b ≤ S.stableCount b' := by
  unfold stableCount
  gcongr
  exact Multiset.monotone_filter_right _ (fun μ hμ => ⟨hμ.1, lt_of_lt_of_le hμ.2 h⟩)

/-- Woodford (2003), p. 552: "this part of Assumption 8.2 is implied by the Sargent–Wallace
property" (for `0 < β ≤ 1`). -/
theorem sargentWallace_assumption82 [DecidableEq ιZ] {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (h : S.SargentWallace) : S.Assumption82Count β := by
  have h1 : (1 : ℝ) ≤ β⁻¹ := one_le_inv₀ hβ0 |>.mpr hβ1
  exact (Nat.le_of_lt h).trans (S.stableCount_mono h1)

/-- Woodford (2003), p. 556: "Assumption 8.7 is implied by the Sargent–Wallace property" (for
`0 < β ≤ 1`). -/
theorem sargentWallace_assumption87 [DecidableEq ιZ] {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (h : S.SargentWallace) : S.Assumption87 β := by
  have h1 : (1 : ℝ) ≤ β⁻¹ := one_le_inv₀ hβ0 |>.mpr hβ1
  have h2 := S.stableCount_mono h1
  unfold SargentWallace at h
  exact ⟨S.stableCount β⁻¹ - Fintype.card ιZ, by omega, by omega⟩

end LinearRESystem

end Woodford.OptimalPolicyRules.GeneralSetup
