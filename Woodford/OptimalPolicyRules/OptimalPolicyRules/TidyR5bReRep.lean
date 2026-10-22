/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.Prop83
import OptimalPolicyRules.Prop81Unique

/-!
# Uniqueness of `Λ` and `Υ` in Proposition 8.1 when a root lies on `|μ| = β⁻¹`

Woodford (2003), *Interest and Prices*, Chapter 8, Proposition 8.1 and the remark after it
(p. 553): "In the case that there are exactly `n_Z` roots of (1.15) such that `|μᵢ| < β⁻¹`, the
matrices `Λ, Υ, Q`, and `R` are uniquely defined".

`Prop81Unique.remark_p553` proves the remark when no root lies on `|μ| = β⁻¹` (then `Λ` is
stable), and `Prop81Unique.circle_counterexample` shows that with a root on the circle bounded
multipliers need not exist. This module settles uniqueness in the circle case.

## What is proved

* `agree_on_bddOrbit`: for any two representations `H`, `H'` of the (corrected) Proposition 8.1
  under any expectation system, if (1.18) has one bounded solution (e.g. under Assumption 8.1,
  `Prop83.exists_base_of_assumption81`), then `Λ m = Λ' m` and `Υ m = Υ' m` for every `m` whose
  orbit `Λᵏ m` is bounded. So `Λ`, `Υ` are pinned down exactly on the bounded orbits of `Λ`.
* `unique_of_powBdd`: if `Λ` is power-bounded (all eigenvalues in the closed unit disc, those on
  the circle semisimple — the case of a semisimple root on `|μ| = β⁻¹` under the remark's count),
  `Λ` and `Υ` are unique.
* `reRep` (**re-representation**, perfect foresight): if `Λ'` has the same bounded homogeneous
  solutions as `Λ` and a "blow-up" forcing exists, `(Λ', Υ)` with a modified `Q'` is again a
  representation. The modified `Q'` reproduces the bounded solutions on the plans that have them
  and forces explosion on the plans that have none.
* `jordan_nonunique` (**the remark fails for `Λ` when a circle root is not semisimple**): the
  system `jSys` (`n_Z = 0`, `n_z = 2`, a double root `μ = β⁻¹ = 2` with a Jordan block; exactly
  `n_Z = 0` roots inside `|μ| < β⁻¹`) has two representations with
  `Λ = [[1, 0], [1, 1]]` and `Λ' = [[1, 0], [2, 1]]`.
* `circle_Λ_unique`, `circle_Q_nonunique`: for `Prop81Unique.circleProblem` (a simple root on the
  circle) `Λ = 1` is unique, but `Q(L⁻¹)` is not: on the plan `y = 0`, which has no bounded
  multipliers (`Prop81Unique.circle_counterexample`), two representations have different `q`.
-/

namespace Woodford.OptimalPolicyRules.TidyR5bReRep

open Matrix Polynomial GeneralSetup PencilSplit PencilEigen Prop81General
open TargetCriterion.Prop81 GeneralFOC GeneralFOC.LQ

variable {Ω : Type*} {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-! ### Agreement on bounded orbits -/

omit [Fintype ιZ] [Fintype ιτ] [DecidableEq ιZ] in
/-- Woodford (2003), (1.20) (tool): the deterministic multiplier perturbation `M_s = Λ^{s−t₀} m`,
`ξ_s = Υ M_s`. -/
noncomputable def pert (t0 : ℕ) (Λ : Matrix ιz ιz ℝ) (Υ : Matrix ιZ ιz ℝ) (m : ιz → ℝ) (s : ℕ) :
    ιZ ⊕ ιz → ℝ :=
  Sum.elim (Υ *ᵥ (Λ ^ (s - t0) *ᵥ m)) (Λ ^ (s - t0) *ᵥ m)

/-- Woodford (2003), p. 553 (the remark after Proposition 8.1, the circle case): **two
representations agree on the bounded orbits of `Λ`.** If (1.18) has a bounded solution
`(y⁰, φ⁰)` (with `M_t` known at `t`), then for every `m` with `Λᵏ m` bounded,
`Λ m = Λ' m` and `Υ m = Υ' m`, for any other representation `(Λ', Υ', Q', R')`. Any expectation
system on a nonempty sample space. -/
theorem agree_on_bddOrbit [Nonempty Ω] {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω}
    {t0 : ℕ} (H H' : Prop81ConclusionM P 𝔼 t0) {y0 : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ0 : ℕ → Ω → ιZ ⊕ ιz → ℝ} (hy0b : BoundedV y0) (hy0a : AdaptedV 𝔼 y0)
    (hφ0b : BoundedV φ0) (hφ0k : MultKnown 𝔼 t0 φ0) (h118 : Eq118 P 𝔼 t0 y0 φ0)
    (m : ιz → ℝ) (hm : ∃ K, ∀ k i, |(H.Λ ^ k *ᵥ m) i| ≤ K) :
    H.Λ *ᵥ m = H'.Λ *ᵥ m ∧ H.Υ *ᵥ m = H'.Υ *ᵥ m := by
  set ω0 : Ω := Classical.arbitrary Ω
  set h := pert t0 H.Λ H.Υ m with hh
  set φ1 : ℕ → Ω → ιZ ⊕ ιz → ℝ := fun s ω => φ0 s ω + h s with hφ1
  obtain ⟨e120, e121⟩ := (H.equiv y0 φ0 hy0b hy0a hφ0b hφ0k).mp h118
  have hMh : ∀ s, Mpart (h s) = H.Λ ^ (s - t0) *ᵥ m := fun s => rfl
  have hξh : ∀ s, ξpart (h s) = H.Υ *ᵥ (H.Λ ^ (s - t0) *ᵥ m) := fun s => rfl
  have hφ1b : BoundedV φ1 := by
    obtain ⟨K, hK⟩ := hm
    obtain ⟨K0, hK0⟩ := hφ0b
    obtain ⟨KΥ, hKΥ⟩ := exists_bound_mulVec H.Υ K
    refine ⟨K0 + max K KΥ, fun s ω a => ?_⟩
    refine (abs_add_le _ _).trans (add_le_add (hK0 s ω a) ?_)
    rcases a with a | a
    · exact (hKΥ _ (fun i => hK _ i) a).trans (le_max_right _ _)
    · exact (hK _ a).trans (le_max_left _ _)
  have hφ1k : MultKnown 𝔼 t0 φ1 := by
    intro t ht i
    have h1 := hφ0k t ht i
    have e : (fun ω => Mpart (φ1 (t + 1) ω) i) =
        (fun ω => Mpart (φ0 (t + 1) ω) i) + fun _ => Mpart (h (t + 1)) i := by
      funext ω
      rfl
    rw [e, map_add, h1, 𝔼.const]
  have h120 : Eq120 t0 H.Λ (H.Qop (xproc P y0)) φ1 := by
    intro t ht ω
    have e1 := e120 t ht ω
    change Mpart (φ0 (t + 1) ω) + Mpart (h (t + 1)) =
      H.Λ *ᵥ (Mpart (φ0 t ω) + Mpart (h t)) + H.Qop (xproc P y0) t ω
    rw [e1, hMh, hMh, mulVec_add, mulVec_mulVec, ← pow_succ',
      show t + 1 - t0 = t - t0 + 1 by omega]
    abel
  have h121 : Eq121 t0 H.Υ (H.Rop (xproc P y0)) φ1 := by
    intro t ht ω
    have e1 := e121 t ht ω
    change ξpart (φ0 t ω) + ξpart (h t) =
      H.Υ *ᵥ (Mpart (φ0 t ω) + Mpart (h t)) + H.Rop (xproc P y0) t ω
    rw [e1, hξh, hMh, mulVec_add]
    abel
  have h118' := (H.equiv y0 φ1 hy0b hy0a hφ1b hφ1k).mpr ⟨h120, h121⟩
  obtain ⟨f120, f121⟩ := (H'.equiv y0 φ1 hy0b hy0a hφ1b hφ1k).mp h118'
  obtain ⟨g120, g121⟩ := (H'.equiv y0 φ0 hy0b hy0a hφ0b hφ0k).mp h118
  have a1 := f120 t0 le_rfl ω0
  have a2 := g120 t0 le_rfl ω0
  have b1 := f121 t0 le_rfl ω0
  have b2 := g121 t0 le_rfl ω0
  change Mpart (φ0 (t0 + 1) ω0) + Mpart (h (t0 + 1)) =
    H'.Λ *ᵥ (Mpart (φ0 t0 ω0) + Mpart (h t0)) + _ at a1
  change ξpart (φ0 t0 ω0) + ξpart (h t0) =
    H'.Υ *ᵥ (Mpart (φ0 t0 ω0) + Mpart (h t0)) + _ at b1
  rw [hMh, hMh, show t0 + 1 - t0 = 1 by omega, Nat.sub_self, pow_one, pow_zero, one_mulVec,
    mulVec_add, a2] at a1
  rw [hξh, hMh, Nat.sub_self, pow_zero, one_mulVec, mulVec_add, b2] at b1
  constructor
  · have := congrArg (fun v => v - (H'.Λ *ᵥ Mpart (φ0 t0 ω0) + H'.Qop (xproc P y0) t0 ω0)) a1
    rw [show H'.Λ *ᵥ Mpart (φ0 t0 ω0) + H'.Qop (xproc P y0) t0 ω0 + H.Λ *ᵥ m -
        (H'.Λ *ᵥ Mpart (φ0 t0 ω0) + H'.Qop (xproc P y0) t0 ω0) = H.Λ *ᵥ m by abel,
      show H'.Λ *ᵥ Mpart (φ0 t0 ω0) + H'.Λ *ᵥ m + H'.Qop (xproc P y0) t0 ω0 -
        (H'.Λ *ᵥ Mpart (φ0 t0 ω0) + H'.Qop (xproc P y0) t0 ω0) = H'.Λ *ᵥ m by abel] at this
    exact this
  · have := congrArg (fun v => v - (H'.Υ *ᵥ Mpart (φ0 t0 ω0) + H'.Rop (xproc P y0) t0 ω0)) b1
    rw [show H'.Υ *ᵥ Mpart (φ0 t0 ω0) + H'.Rop (xproc P y0) t0 ω0 + H.Υ *ᵥ m -
        (H'.Υ *ᵥ Mpart (φ0 t0 ω0) + H'.Rop (xproc P y0) t0 ω0) = H.Υ *ᵥ m by abel,
      show H'.Υ *ᵥ Mpart (φ0 t0 ω0) + H'.Υ *ᵥ m + H'.Rop (xproc P y0) t0 ω0 -
        (H'.Υ *ᵥ Mpart (φ0 t0 ω0) + H'.Rop (xproc P y0) t0 ω0) = H'.Υ *ᵥ m by abel] at this
    exact this

/-- Woodford (2003), p. 553 (the remark, circle case): **if `Λ` is power-bounded** (every
orbit bounded), and (1.18) has one bounded solution, then `Λ` and `Υ` are the same in every
representation of Proposition 8.1. -/
theorem unique_of_powBdd [Nonempty Ω] {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω}
    {t0 : ℕ} (H H' : Prop81ConclusionM P 𝔼 t0) {y0 : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ0 : ℕ → Ω → ιZ ⊕ ιz → ℝ} (hy0b : BoundedV y0) (hy0a : AdaptedV 𝔼 y0)
    (hφ0b : BoundedV φ0) (hφ0k : MultKnown 𝔼 t0 φ0) (h118 : Eq118 P 𝔼 t0 y0 φ0)
    (hpb : ∃ K, ∀ k i j, |(H.Λ ^ k) i j| ≤ K) : H.Λ = H'.Λ ∧ H.Υ = H'.Υ := by
  obtain ⟨K, hK⟩ := hpb
  have hcol : ∀ j, H.Λ *ᵥ Pi.single j 1 = H'.Λ *ᵥ Pi.single j 1 ∧
      H.Υ *ᵥ Pi.single j 1 = H'.Υ *ᵥ Pi.single j 1 := fun j =>
    agree_on_bddOrbit H H' hy0b hy0a hφ0b hφ0k h118 _ ⟨K, fun k i => by
      rw [mulVec_single_one]
      exact hK k i j⟩
  refine ⟨?_, ?_⟩
  · ext i j
    have := congrFun (hcol j).1 i
    simpa [mulVec_single_one] using this
  · ext i j
    have := congrFun (hcol j).2 i
    simpa [mulVec_single_one] using this

/-- Woodford (2003), p. 553 (the remark, circle case) **under Assumption 8.1**: with a
power-bounded `Λ` (e.g. a semisimple root on `|μ| = β⁻¹` and none outside the closed disc), `Λ`
and `Υ` are unique across all representations of Proposition 8.1. -/
theorem unique_of_assumption81 [Nonempty Ω] {P : LQProblem ιZ ιz ιτ}
    {𝔼 : ExpectationSystem Ω} {t0 : ℕ} (hA : Assumption81 P 𝔼 t0)
    (H H' : Prop81ConclusionM P 𝔼 t0) (hpb : ∃ K, ∀ k i j, |(H.Λ ^ k) i j| ≤ K) :
    H.Λ = H'.Λ ∧ H.Υ = H'.Υ := by
  obtain ⟨y, φ, hy, hya, hφ, hφk, h118⟩ := Prop83.exists_base_of_assumption81 hA
  exact unique_of_powBdd H H' hy hya hφ hφk h118 hpb

/-! ### Re-representation (perfect foresight) -/

omit [DecidableEq ιz] in
/-- Woodford (2003), (1.20): a bounded sequence of multiplier vectors. -/
def BddS (D : ℕ → ιz → ℝ) : Prop := ∃ K, ∀ t i, |D t i| ≤ K

omit [DecidableEq ιz] in
/-- Woodford (2003), (1.20): `M` is a bounded solution of `M_{t+1} = Λ M_t + q_t` from `t₀`
(index `s` is `M_{s−1}`). -/
def RecSol (t0 : ℕ) (Λ : Matrix ιz ιz ℝ) (q : ℕ → ιz → ℝ) (M : ℕ → ιz → ℝ) : Prop :=
  BddS M ∧ ∀ t, t0 ≤ t → M (t + 1) = Λ *ᵥ M t + q t

omit [DecidableEq ιz] in
/-- Woodford (2003), (1.20) homogeneous: `Λ` and `Λ'` have the same bounded homogeneous solutions
`D_{t+1} = Λ D_t` from `t₀`. -/
def HomSame (t0 : ℕ) (Λ Λ' : Matrix ιz ιz ℝ) : Prop :=
  ∀ D, BddS D → ((∀ t, t0 ≤ t → D (t + 1) = Λ *ᵥ D t) ↔ (∀ t, t0 ≤ t → D (t + 1) = Λ' *ᵥ D t))

open Classical in
omit [Fintype ιZ] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), (1.20) (the modified operator `Q'`): on a plan with bounded multipliers,
`q'_t = M*_{t+1} − Λ' M*_t` for a bounded solution `M*` of `M_{t+1} = Λ M_t + q_t`; on a plan with
none, the forcing `b x`. -/
noncomputable def reQ (t0 : ℕ) (Λ Λ' : Matrix ιz ιz ℝ)
    (Q : (ℕ → Unit → ιZ ⊕ ιz → ℝ) → ℕ → Unit → ιz → ℝ)
    (b : (ℕ → Unit → ιZ ⊕ ιz → ℝ) → ℕ → ιz → ℝ) :
    (ℕ → Unit → ιZ ⊕ ιz → ℝ) → ℕ → Unit → ιz → ℝ :=
  fun x => if h : ∃ M, RecSol t0 Λ (fun t => Q x t ()) M then
    fun t _ => Classical.choose h (t + 1) - Λ' *ᵥ Classical.choose h t else fun t _ => b x t

/-- Woodford (2003), Proposition 8.1, p. 553 (**re-representation**, perfect foresight): let
`H` represent the bounded solutions of (1.18), let `Λ'` have the same bounded homogeneous
solutions as `H.Λ`, and for every bounded plan without bounded multipliers let `b x` be a bounded
forcing for which `M_{t+1} = Λ' M_t + b_t` has no bounded solution. Then `(Λ', H.Υ, reQ, H.Rop)`
also represents the bounded solutions of (1.18). -/
theorem reRep_equiv {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (H : Prop81ConclusionM P perfectForesight t0) {Λ' : Matrix ιz ιz ℝ}
    (hsame : HomSame t0 H.Λ Λ') (b : (ℕ → Unit → ιZ ⊕ ιz → ℝ) → ℕ → ιz → ℝ)
    (hb : ∀ x, BoundedV x → ¬ (∃ M, RecSol t0 H.Λ (fun t => H.Qop x t ()) M) →
      ∀ D, BddS D → ¬ ∀ t, t0 ≤ t → D (t + 1) = Λ' *ᵥ D t + b x t) :
    Prop81EquivM P perfectForesight t0 Λ' H.Υ (reQ t0 H.Λ Λ' H.Qop b) H.Rop := by
  intro y φ hyb hya hφb hφk
  set x := xproc P y with hx
  set q : ℕ → ιz → ℝ := fun t => H.Qop x t () with hq
  set m : ℕ → ιz → ℝ := fun t => Mpart (φ t ()) with hm
  have hmb : BddS m := by
    obtain ⟨K, hK⟩ := hφb
    exact ⟨K, fun t i => hK t () (Sum.inr i)⟩
  have hE120 : ∀ (L : Matrix ιz ιz ℝ) (q' : ℕ → Unit → ιz → ℝ), Eq120 t0 L q' φ ↔
      ∀ t, t0 ≤ t → m (t + 1) = L *ᵥ m t + q' t () := by
    intro L q'
    constructor
    · intro h t ht
      exact h t ht ()
    · intro h t ht ω
      cases ω
      exact h t ht
  rw [H.equiv y φ hyb hya hφb hφk, hE120, hE120]
  by_cases hs : ∃ M, RecSol t0 H.Λ q M
  · have hQ : ∀ t, reQ t0 H.Λ Λ' H.Qop b x t () =
        Classical.choose hs (t + 1) - Λ' *ᵥ Classical.choose hs t := by
      intro t
      simp only [reQ]
      rw [dite_eq_left hs]
    obtain ⟨hMb, hMr⟩ := Classical.choose_spec hs
    set M := Classical.choose hs
    have hDb : BddS (fun t => m t - M t) := by
      obtain ⟨K1, hK1⟩ := hmb
      obtain ⟨K2, hK2⟩ := hMb
      exact ⟨K1 + K2, fun t i => (abs_sub _ _).trans (add_le_add (hK1 t i) (hK2 t i))⟩
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun t ht => ?_, h2⟩
      have hD := ((hsame _ hDb).mp fun t ht => by
        rw [h1 t ht, hMr t ht, mulVec_sub]; abel) t ht
      rw [hQ]
      have : m (t + 1) = M (t + 1) + Λ' *ᵥ (m t - M t) := by rw [← hD]; abel
      rw [this, mulVec_sub]
      abel
    · rintro ⟨h1, h2⟩
      refine ⟨fun t ht => ?_, h2⟩
      have hD := ((hsame _ hDb).mpr fun t ht => by
        rw [h1 t ht, hQ, mulVec_sub]; abel) t ht
      have : m (t + 1) = M (t + 1) + H.Λ *ᵥ (m t - M t) := by rw [← hD]; abel
      rw [this, hMr t ht, mulVec_sub]
      abel
  · have hQ : ∀ t, reQ t0 H.Λ Λ' H.Qop b x t () = b x t := by
      intro t
      simp only [reQ]
      rw [dite_eq_right hs]
    constructor
    · rintro ⟨h1, -⟩
      exact absurd ⟨m, hmb, h1⟩ hs
    · rintro ⟨h1, -⟩
      exact absurd (fun t ht => by rw [h1 t ht, hQ]) (hb x (boundedV_xproc hyb) hs m hmb)

/-- Woodford (2003), Proposition 8.1 (**re-representation**, perfect foresight): the
representation `(Λ', H.Υ, reQ, H.Rop)` of `reRep_equiv` as a `Prop81ConclusionM`. Requires the
forcing `b x` to be bounded on bounded plans without bounded multipliers. -/
noncomputable def reRep {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (H : Prop81ConclusionM P perfectForesight t0) (Λ' : Matrix ιz ιz ℝ)
    (hsame : HomSame t0 H.Λ Λ') (b : (ℕ → Unit → ιZ ⊕ ιz → ℝ) → ℕ → ιz → ℝ)
    (hbb : ∀ x, BoundedV x → ¬ (∃ M, RecSol t0 H.Λ (fun t => H.Qop x t ()) M) → BddS (b x))
    (hb : ∀ x, BoundedV x → ¬ (∃ M, RecSol t0 H.Λ (fun t => H.Qop x t ()) M) →
      ∀ D, BddS D → ¬ ∀ t, t0 ≤ t → D (t + 1) = Λ' *ᵥ D t + b x t) :
    Prop81ConclusionM P perfectForesight t0 where
  Λ := Λ'
  Υ := H.Υ
  Qop := reQ t0 H.Λ Λ' H.Qop b
  Rop := H.Rop
  equiv := reRep_equiv H hsame b hb
  Qbounded := fun x hx => by
    by_cases hs : ∃ M, RecSol t0 H.Λ (fun t => H.Qop x t ()) M
    · obtain ⟨⟨K, hK⟩, -⟩ := Classical.choose_spec hs
      obtain ⟨K', hK'⟩ := exists_bound_mulVec Λ' K
      refine ⟨K + K', fun t ω i => ?_⟩
      simp only [reQ]
      rw [dite_eq_left hs]
      exact (abs_sub _ _).trans (add_le_add (hK _ i) (hK' _ (hK t) i))
    · obtain ⟨K, hK⟩ := hbb x hx hs
      refine ⟨K, fun t ω i => ?_⟩
      simp only [reQ]
      rw [dite_eq_right hs]
      exact hK t i
  Rbounded := H.Rbounded
  Qadapted := fun _ _ _ => rfl
  Radapted := H.Radapted

/-- Woodford (2003), Proposition 8.1: under perfect foresight a corrected representation is a
representation in the original sense (`TargetCriterion.Prop81.Prop81Conclusion`), since every plan
is adapted and every multiplier known. -/
noncomputable def toPlain {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (H : Prop81ConclusionM P perfectForesight t0) : Prop81Conclusion P perfectForesight t0 where
  Λ := H.Λ
  Υ := H.Υ
  Qop := H.Qop
  Rop := H.Rop
  equiv := fun y φ hy hφ => H.equiv y φ hy (fun _ _ => rfl) hφ (fun _ _ _ => rfl)
  Qbounded := H.Qbounded
  Rbounded := H.Rbounded
  Qadapted := H.Qadapted

/-! ### The empty split (`n_Z = 0`) -/

/-- Woodford (2003), App. G.1, (G.4), with no predetermined variables: the empty deflating split
(restated from `OptimalRulesMeasureModelsProp82.emptySplit`): `J`, `Ψ` empty, `K = A₂₂'`. -/
noncomputable def emptySplit' {κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : LinearRESystem Empty κ) (β : ℝ) : DeflatingSplit S β where
  J := 0
  Ψ := 0
  deflate := by
    ext i j
    exact j.elim
  eig_lt := fun μ h => by
    rw [Matrix.det_isEmpty] at h
    exact absurd h one_ne_zero
  J1_det := by
    rw [Matrix.det_isEmpty]
    exact one_ne_zero
  K_det := by
    have hK : Kmat S 0 = S.A22ᵀ := by
      ext i j
      simp [Kmat, Matrix.mul_apply]
    rw [hK, det_transpose]
    exact S.A22_isUnit.ne_zero

/-- Woodford (2003), (1.20): with no predetermined variables, `Λ = β⁻¹ (A₂₂')⁻¹ Ẽ'`. -/
theorem Λmat_empty {κ : Type*} [Fintype κ] [DecidableEq κ] (S : LinearRESystem Empty κ)
    (β : ℝ) : Λmat S β 0 = β⁻¹ • ((S.A22ᵀ)⁻¹ * S.Etᵀ) := by
  have hK : Kmat S 0 = S.A22ᵀ := by
    ext i j
    simp [Kmat, Matrix.mul_apply]
  rw [Λmat, hK]

/-! ### A Jordan block on the circle: `Λ` is not unique -/

/-- Woodford (2003), (1.20) (tool): the lower-triangular `[[1, 0], [a, 1]]`. -/
def jΛ (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; a, 1]

/-- Woodford (2003), (1.20) homogeneous: for `a ≠ 0` the bounded solutions of
`D_{t+1} = [[1, 0], [a, 1]] D_t` from `t₀` are exactly `D_{t,1} = 0`, `D_{t,2}` constant. -/
theorem jΛ_hom {a : ℝ} (ha : a ≠ 0) (t0 : ℕ) {D : ℕ → Fin 2 → ℝ} (hD : BddS D) :
    (∀ t, t0 ≤ t → D (t + 1) = jΛ a *ᵥ D t) ↔ ∀ t, t0 ≤ t → D t 0 = 0 ∧ D (t + 1) = D t := by
  have hmv : ∀ v : Fin 2 → ℝ, jΛ a *ᵥ v = ![v 0, a * v 0 + v 1] := by
    intro v
    funext i
    fin_cases i <;> simp [jΛ, mulVec, dotProduct, Fin.sum_univ_two]
  constructor
  · intro h
    have h0 : ∀ n, D (t0 + n) 0 = D t0 0 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        have := congrFun (h (t0 + n) (by omega)) 0
        rw [hmv] at this
        simp only [Matrix.cons_val_zero] at this
        rw [← add_assoc, this, ih]
    have h1 : ∀ n : ℕ, D (t0 + n) 1 = D t0 1 + n * (a * D t0 0) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have := congrFun (h (t0 + n) (by omega)) 1
        rw [hmv] at this
        simp only [Matrix.cons_val_one] at this
        rw [← add_assoc, this, ih, h0 n]
        push_cast
        ring
    have hc : D t0 0 = 0 := by
      obtain ⟨K, hK⟩ := hD
      by_contra hne
      have hpos : 0 < |a * D t0 0| := abs_pos.mpr (mul_ne_zero ha hne)
      obtain ⟨n, hn⟩ := exists_nat_gt (2 * K / |a * D t0 0|)
      have e1 := hK (t0 + n) 1
      have e2 := hK t0 1
      rw [h1 n] at e1
      have e3 : (n : ℝ) * |a * D t0 0| ≤ 2 * K := by
        have := (abs_sub (D t0 1 + n * (a * D t0 0)) (D t0 1)).trans (add_le_add e1 e2)
        rw [add_sub_cancel_left, abs_mul, Nat.abs_cast] at this
        linarith
      have := (div_lt_iff₀ hpos).mp hn
      linarith
    intro t ht
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
    refine ⟨by rw [h0 n, hc], ?_⟩
    rw [h (t0 + n) ht, hmv]
    funext i
    fin_cases i
    · simp
    · simp [h0 n, hc]
  · intro h t ht
    rw [hmv, (h t ht).2]
    funext i
    fin_cases i
    · simp
    · simp [(h t ht).1]

/-- Woodford (2003), (1.20) homogeneous: `[[1, 0], [a, 1]]` and `[[1, 0], [a', 1]]`
(`a, a' ≠ 0`) have the same bounded homogeneous solutions. -/
theorem jΛ_homSame {a a' : ℝ} (ha : a ≠ 0) (ha' : a' ≠ 0) (t0 : ℕ) :
    HomSame t0 (jΛ a) (jΛ a') := fun D hD => by
  rw [jΛ_hom ha t0 hD, jΛ_hom ha' t0 hD]

/-- Woodford (2003), (1.20): with the constant forcing `(1, 0)` the recursion
`M_{t+1} = [[1, 0], [a, 1]] M_t + (1, 0)` has no bounded solution (`M_{t,1}` grows linearly). -/
theorem jΛ_blowUp (a : ℝ) (t0 : ℕ) (D : ℕ → Fin 2 → ℝ) (hD : BddS D) :
    ¬ ∀ t, t0 ≤ t → D (t + 1) = jΛ a *ᵥ D t + ![1, 0] := by
  intro h
  have h0 : ∀ n : ℕ, D (t0 + n) 0 = D t0 0 + n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : D (t0 + n + 1) 0 = D (t0 + n) 0 + 1 := by
        have := congrFun (h (t0 + n) (by omega)) 0
        simpa [jΛ, mulVec, dotProduct, Fin.sum_univ_two] using this
      rw [← add_assoc, h1, ih]
      push_cast
      ring
  obtain ⟨K, hK⟩ := hD
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * K)
  have e1 := hK (t0 + n) 0
  have e2 := hK t0 0
  rw [h0 n] at e1
  have := (abs_sub (D t0 0 + n) (D t0 0)).trans (add_le_add e1 e2)
  rw [add_sub_cancel_left, Nat.abs_cast] at this
  linarith

/-- Woodford (2003), eq. (1.1) (the Jordan counterexample): `n_Z = 0`, `n_z = 2`,
`E_t z_{t+1} = A₂₂ z_t + B₂ i_t + c_t` with `A₂₂ = [[2, −2], [0, 2]]`, `Ẽ = I`; (1.15) has the
double root `2` with a Jordan block. -/
noncomputable def jSys : LinearRESystem Empty (Fin 2) where
  A11 := 0
  A12 := 0
  A21 := 0
  A22 := !![2, -2; 0, 2]
  Et := 1
  B2 := ![1, 1]
  A22_isUnit := by
    rw [isUnit_iff_ne_zero, det_fin_two_of]
    norm_num
  B2_ne_zero := by
    intro h
    have := congrFun h 0
    simp at this

/-- Woodford (2003), (1.2)–(1.4) (the Jordan counterexample): `β = 1/2`, targets `τ = z`, `W = I`,
`τ* = 0`. -/
noncomputable def jProblem : LQProblem Empty (Fin 2) (Fin 2) where
  sys := jSys
  β := 1 / 2
  β_pos := by norm_num
  β_lt_one := by norm_num
  Ttil := Matrix.of fun a col => Sum.elim (fun e => e.elim) (fun j => if a = j then 1 else 0) col
  Ti := 0
  W := 1
  τstar := 0
  W_posDef := Matrix.PosDef.one

/-- Woodford (2003), eq. (1.15) (the Jordan counterexample): `det(A − μÎ) = (μ − 2)²`. -/
theorem jSys_pencilPoly : jSys.pencilPoly = (X - C 2) ^ 2 := by
  refine Polynomial.funext fun μ => ?_
  rw [pencilPoly_eval, Prop83.det_empty_sum, det_fin_two]
  simp [toBlocks₂₂, LinearRESystem.Ahat, LinearRESystem.Ihat, jSys]
  ring

/-- Woodford (2003), p. 553 (the remark's count): `jSys` has exactly `n_Z = 0` roots of (1.15)
with `|μ| < β⁻¹ = 2`, and the double root `2` lies on `|μ| = β⁻¹`. -/
theorem jSys_count : jSys.stableCount (1 / 2 : ℝ)⁻¹ = Fintype.card Empty ∧
    jSys.pencilPoly.roots = {2, 2} ∧ ‖(2 : ℂ)‖ = (1 / 2 : ℝ)⁻¹ := by
  have hroots : jSys.pencilPoly.roots = {2, 2} := by
    rw [jSys_pencilPoly, roots_pow, roots_X_sub_C]
    rfl
  have hrank : jSys.Ahat.rank = Fintype.card (Empty ⊕ Fin 2) := by
    refine rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr ?_)
    rw [Prop83.det_empty_sum]
    exact jSys.A22_isUnit
  refine ⟨?_, hroots, by norm_num⟩
  unfold LinearRESystem.stableCount
  rw [hrank, Nat.sub_self, zero_add, hroots]
  norm_num [Multiset.filter_cons]

/-- Woodford (2003), Proposition 8.1 for `jProblem` (perfect foresight): the representation from
the empty split, with `Λ = β⁻¹ (A₂₂')⁻¹ = [[1, 0], [1, 1]]`. -/
noncomputable def jRep : Prop81ConclusionM jProblem perfectForesight 0 :=
  prop81 jProblem (emptySplit' jSys (1 / 2)) perfectForesight 0

/-- Woodford (2003), (1.20) (the Jordan counterexample): `Λ = [[1, 0], [1, 1]]`. -/
theorem jRep_Λ : jRep.Λ = jΛ 1 := by
  change Λmat jSys (1 / 2) 0 = jΛ 1
  rw [Λmat_empty]
  have hinv : (jSys.A22ᵀ)⁻¹ = !![1 / 2, 0; 1 / 2, 1 / 2] := by
    refine Matrix.inv_eq_right_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [jSys, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jSys, jΛ]

/-- Woodford (2003), Proposition 8.1 for `jProblem`: the second representation, with
`Λ' = [[1, 0], [2, 1]]` (`reRep`). -/
noncomputable def jRep' : Prop81ConclusionM jProblem perfectForesight 0 :=
  reRep jRep (jΛ 2) (by rw [jRep_Λ]; exact jΛ_homSame one_ne_zero two_ne_zero 0)
    (fun _ _ => ![1, 0]) (fun _ _ _ => ⟨1, fun t i => by fin_cases i <;> simp⟩)
    (fun _ _ _ D hD => jΛ_blowUp 2 0 D hD)

/-- **Woodford (2003), p. 553 (the remark after Proposition 8.1) FAILS for `Λ` when a root on
`|μ| = β⁻¹` is not semisimple**: `jProblem` has exactly `n_Z = 0` roots of (1.15) with
`|μ| < β⁻¹` and the double root `β⁻¹ = 2` (a Jordan block), and it has two representations of
the (corrected) Proposition 8.1 with different `Λ`: `[[1, 0], [1, 1]]` and `[[1, 0], [2, 1]]`. -/
theorem jordan_nonunique :
    jSys.stableCount (1 / 2 : ℝ)⁻¹ = Fintype.card Empty ∧
      (∃ l ∈ jSys.pencilPoly.roots, ‖l‖ = (1 / 2 : ℝ)⁻¹) ∧
      jRep.Λ = jΛ 1 ∧ jRep'.Λ = jΛ 2 ∧ jRep.Λ ≠ jRep'.Λ := by
  obtain ⟨h1, h2, h3⟩ := jSys_count
  refine ⟨h1, ⟨2, by rw [h2]; simp, h3⟩, jRep_Λ, rfl, ?_⟩
  rw [jRep_Λ]
  change jΛ 1 ≠ jΛ 2
  intro h
  have := congrFun (congrFun h 1) 0
  simp [jΛ] at this

/-! ### A simple root on the circle: `Λ` unique, `Q` not -/

open Prop81Unique (circleProblem circle_counterexample) in
/-- Woodford (2003), Proposition 8.1 for `Prop81Unique.circleProblem` (any expectation system):
the representation from the empty split, `Λ = β⁻¹ (A₂₂')⁻¹ Ẽ' = 1`. -/
noncomputable def cRep (𝔼 : ExpectationSystem Ω) : Prop81ConclusionM circleProblem 𝔼 0 :=
  prop81 circleProblem (emptySplit' coinSys (1 / 2)) 𝔼 0

open Prop81Unique (circleProblem) in
/-- Woodford (2003), (1.20) for `Prop81Unique.circleProblem`: `Λ = 1`. -/
theorem cRep_Λ (𝔼 : ExpectationSystem Ω) : (cRep 𝔼).Λ = 1 := by
  change Λmat coinSys (1 / 2) 0 = 1
  rw [Λmat_empty]
  have hinv : (coinSys.A22ᵀ)⁻¹ = Matrix.of fun _ _ => (1 / 2 : ℝ) := by
    refine Matrix.inv_eq_right_inv ?_
    ext i j
    simp [coinSys, Matrix.mul_apply]
  rw [hinv]
  ext i j
  simp [coinSys, Matrix.mul_apply]

open Prop81Unique (circleProblem) in
/-- Woodford (2003), (1.18) for `Prop81Unique.circleProblem`: the plan with `z_t = τ* = 1`,
`i_t = 0`, and zero multipliers, solves (1.18) (any expectation system). -/
theorem circle_base (𝔼 : ExpectationSystem Ω) :
    Eq118 circleProblem 𝔼 0
      (fun _ _ => Sum.elim (Sum.elim (fun e => e.elim) fun _ => 1) fun _ => 0) 0 := by
  intro t _ ω
  have hE : EV 𝔼 t ((0 : ℕ → Ω → Empty ⊕ Unit → ℝ) (t + 1)) ω = 0 := by
    funext r
    simp only [EV, Pi.zero_apply]
    exact congrFun (𝔼.const t 0) ω
  rw [hE]
  funext r
  rcases r with e | u
  · exact e.elim
  · simp [circleProblem, LQProblem.T, mulVec, dotProduct, Fintype.sum_sum_type]

open Prop81Unique (circleProblem) in
/-- Woodford (2003), p. 553 (the remark, circle case): **for `Prop81Unique.circleProblem` (a
simple root on `|μ| = β⁻¹`) `Λ = 1` and `Υ` are unique** — every representation of Proposition
8.1, under any expectation system on a nonempty sample space, has `Λ = 1`. -/
theorem circle_Λ_unique [Nonempty Ω] (𝔼 : ExpectationSystem Ω)
    (H : Prop81ConclusionM circleProblem 𝔼 0) : H.Λ = 1 ∧ H.Υ = (cRep 𝔼).Υ := by
  have h := unique_of_powBdd (cRep 𝔼) H
    (y0 := fun _ _ => Sum.elim (Sum.elim (fun e => e.elim) fun _ => 1) fun _ => 0)
    (φ0 := 0) ⟨1, fun t ω i => by rcases i with (e | u) | u <;> first | exact e.elim | simp⟩
    (fun t i => 𝔼.const t _) ⟨0, fun t ω i => by simp⟩ (fun t _ i => 𝔼.const t 0)
    (circle_base 𝔼) ⟨1, fun k i j => by rw [cRep_Λ, one_pow]; simp⟩
  exact ⟨h.1.symm.trans (cRep_Λ 𝔼), h.2.symm⟩

open Prop81Unique (circleProblem circle_counterexample) in
/-- Woodford (2003), (1.18) for `Prop81Unique.circleProblem` with the plan `y = 0`: no bounded
solution of `M_{t+1} = Λ M_t + q_t` exists for the `q` of any representation (otherwise (1.18)
would have a bounded multiplier solution, contradicting `Prop81Unique.circle_counterexample`). -/
theorem circle_noRecSol (H : Prop81ConclusionM circleProblem perfectForesight 0) :
    ¬ ∃ M, RecSol 0 H.Λ (fun t => H.Qop (xproc circleProblem 0) t ()) M := by
  rintro ⟨M, ⟨K, hK⟩, hM⟩
  set φ : ℕ → Unit → Empty ⊕ Unit → ℝ := fun t _ => Sum.elim (fun e => e.elim) (M t) with hφ
  have hφb : BoundedV φ :=
    ⟨K, fun t ω i => by rcases i with e | u <;> first | exact e.elim | exact hK t u⟩
  have h118 := (H.equiv 0 φ ⟨0, fun _ _ _ => by simp⟩ (fun _ _ => rfl) hφb
    (fun _ _ _ => rfl)).mpr ⟨fun t ht ω => by cases ω; exact hM t ht,
      fun t _ ω => funext fun e => e.elim⟩
  exact circle_counterexample φ h118 hφb

open Prop81Unique (circleProblem) in
/-- Woodford (2003), p. 553 (the remark, circle case): **`Q(L⁻¹)` is not unique for
`Prop81Unique.circleProblem`** (perfect foresight). The second representation `reRep` keeps
`Λ = 1` and `Υ` but doubles `q` on plans with no bounded multipliers; on the plan `y = 0` (which
has none) the two representations' `q_t` differ at some date. -/
theorem circle_Q_nonunique :
    ∃ H H' : Prop81ConclusionM circleProblem perfectForesight 0, H.Λ = H'.Λ ∧ H.Υ = H'.Υ ∧
      ∃ t, H.Qop (xproc circleProblem 0) t () ≠ H'.Qop (xproc circleProblem 0) t () := by
  set H := cRep (Ω := Unit) perfectForesight
  set b : (ℕ → Unit → Empty ⊕ Unit → ℝ) → ℕ → Unit → ℝ := fun x t => (2 : ℝ) • H.Qop x t ()
  have hbb : ∀ x, BoundedV x → ¬ (∃ M, RecSol 0 H.Λ (fun t => H.Qop x t ()) M) → BddS (b x) := by
    intro x hx _
    obtain ⟨K, hK⟩ := H.Qbounded x hx
    refine ⟨2 * K, fun t i => ?_⟩
    simp only [b, Pi.smul_apply, smul_eq_mul, abs_mul]
    norm_num
    exact hK t () i
  have hb : ∀ x, BoundedV x → ¬ (∃ M, RecSol 0 H.Λ (fun t => H.Qop x t ()) M) →
      ∀ D, BddS D → ¬ ∀ t, 0 ≤ t → D (t + 1) = H.Λ *ᵥ D t + b x t := by
    intro x _ hno D ⟨K, hK⟩ hD
    refine hno ⟨fun t => (1 / 2 : ℝ) • D t, ⟨K / 2, fun t i => ?_⟩, fun t ht => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      have := hK t i
      norm_num
      linarith
    · change (1 / 2 : ℝ) • D (t + 1) = H.Λ *ᵥ ((1 / 2 : ℝ) • D t) + H.Qop x t ()
      rw [hD t ht, mulVec_smul, smul_add]
      simp only [b, smul_smul]
      norm_num
  set H' := reRep H H.Λ (fun D _ => Iff.rfl) b hbb hb
  refine ⟨H, H', rfl, rfl, ?_⟩
  have hno := circle_noRecSol H
  have hQ' : ∀ t, H'.Qop (xproc circleProblem 0) t () =
      (2 : ℝ) • H.Qop (xproc circleProblem 0) t () := by
    intro t
    change reQ 0 H.Λ H.Λ H.Qop b (xproc circleProblem 0) t () = _
    simp only [reQ]
    rw [dite_eq_right hno]
  by_contra hall
  push Not at hall
  apply hno
  refine ⟨0, ⟨0, fun _ _ => by simp⟩, fun t _ => ?_⟩
  have h1 := hall t
  rw [hQ'] at h1
  have h2 : H.Qop (xproc circleProblem 0) t () = 0 := by
    have := congrArg (fun v => v - H.Qop (xproc circleProblem 0) t ()) h1
    simp only [sub_self] at this
    rw [two_smul, add_sub_cancel_right] at this
    exact this.symm
  simp [h2]

end Woodford.OptimalPolicyRules.TidyR5bReRep
