/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR6aReRepBase
import OptimalPolicyRules.OptimalRulesMeasure

/-!
# Proposition 8.1 representations on a probability space, and the p. 553 criterion there

Woodford (2003), *Interest and Prices*, Chapter 8, (1.18)–(1.21), Proposition 8.1 and the remark
after it (p. 553), that `Λ` and `Υ` are "uniquely defined".

The core representation `Prop81General.Prop81ConclusionM` lives on the exact expectation systems.
Here it is formalised on the conditional-expectation model
`ExpectationsMeasure.MeasExpectationSystem` (Mathlib's `condExp`, equations almost surely,
processes essentially bounded and adapted).

## Definitions

`MEq118`, `MEq120`, `MEq121` are (1.18), (1.20), (1.21) almost surely for `t ≥ t₀`;
`MMultKnown`: `M_t` is `𝓕_t`-measurable for `t ≥ t₀`. `MProp81Equiv`: bounded adapted plans and
bounded a.e.-measurable multipliers with `M_t` known at `t` satisfy (1.18) iff they satisfy
(1.20) and (1.21), with `q = Q(x)`, `r = R(x)`, `x = T̃'W(τ − τ*)`. `MProp81Conclusion` packages
`(Λ, Υ, Q, R)` with `Q, R` mapping bounded processes to bounded adapted ones.

## Results

* `mbase`: (1.18) has the bounded solution (constant plan of `TidyR6aReRepBase.exists_xproc_zero`,
  zero multipliers) on every probability space; along it every representation has `q = r = 0`
  a.s. (`mbase_QR`).
* `magree_on_bddOrbit`, `munique_of_powBdd`: two representations agree on the bounded orbits of
  `Λ`; if `Λ` is power-bounded, `(Λ, Υ)` is the same in every representation.
* `mreRep_equiv`, `mreRep`: re-representation with any `Λ'` having the same bounded homogeneous
  solutions (`TidyR5bReRep.HomSame`), on the probability space; `mconj_rep` (`Λ' = GΛG⁻¹`, `G`
  fixing the bounded orbits) and `mneg_rep` (`Λ = cI`, `|c| > 1`, `Λ' = −cI`).
* `mnot_unique_of_not_powBdd`, **`munique_iff_powBdd`**: on **every** probability space,
  `(Λ, Υ)` is the same in every representation **iff** `Λ` is power-bounded. No other
  hypothesis: a probability space is nonempty, and (1.18) always has a bounded solution.
-/

namespace Woodford.OptimalPolicyRules.TidyR6aReRepMeasure

open MeasureTheory Filter Matrix GeneralSetup Prop81General TargetCriterion.Prop81 GeneralFOC
open GeneralFOC.LQ TidyR5bReRep TidyR5bReRepConverse ExpectationsMeasure OptimalRulesMeasure
open TidyR6aReRepBase

variable {Ω : Type*} [MeasurableSpace Ω] {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz]
  [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz]

/-! ### The representation on a probability space -/

/-- Woodford (2003), eq. (1.18), p. 552, almost surely for all `t ≥ t₀`, with Mathlib's
conditional expectation. -/
def MEq118 (S : MeasExpectationSystem Ω) (P : LQProblem ιZ ιz ιτ) (t0 : ℕ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ) : Prop :=
  ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, P.sys.Ahatᵀ *ᵥ EVm S t (φ (t + 1)) ω +
    P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ y t ω - P.τstar)) - P.β⁻¹ • (P.sys.Ihatᵀ *ᵥ φ t ω) = 0

omit [Fintype ιZ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), eq. (1.20), p. 553, almost surely for all `t ≥ t₀`:
`M_t = Λ M_{t−1} + q_t`. -/
def MEq120 (S : MeasExpectationSystem Ω) (t0 : ℕ) (Λ : Matrix ιz ιz ℝ)
    (q : ℕ → Ω → ιz → ℝ) (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ) : Prop :=
  ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, Mpart (φ (t + 1) ω) = Λ *ᵥ Mpart (φ t ω) + q t ω

omit [Fintype ιZ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), eq. (1.21), p. 553, almost surely for all `t ≥ t₀`:
`ξ_t = Υ M_{t−1} + r_t`. -/
def MEq121 (S : MeasExpectationSystem Ω) (t0 : ℕ) (Υ : Matrix ιZ ιz ℝ) (r : ℕ → Ω → ιZ → ℝ)
    (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ) : Prop :=
  ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, ξpart (φ t ω) = Υ *ᵥ Mpart (φ t ω) + r t ω

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 540: the multipliers `M_t` are `𝓕_t`-measurable for `t ≥ t₀`. -/
def MMultKnown (S : MeasExpectationSystem Ω) (t0 : ℕ) (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ) : Prop :=
  ∀ t, t0 ≤ t → MKnownV S t (fun ω => Mpart (φ (t + 1) ω))

/-- Woodford (2003), Proposition 8.1, p. 553, on a probability space: bounded adapted plans and
bounded a.e.-measurable multipliers with `M_t` known at `t` satisfy (1.18) a.s. iff they satisfy
(1.20) and (1.21) a.s., with `q = Qop(T̃'W(τ − τ*))`, `r = Rop(T̃'W(τ − τ*))`. -/
def MProp81Equiv (S : MeasExpectationSystem Ω) (P : LQProblem ιZ ιz ιτ) (t0 : ℕ)
    (Λ : Matrix ιz ιz ℝ) (Υ : Matrix ιZ ιz ℝ)
    (Qop : (ℕ → Ω → ιZ ⊕ ιz → ℝ) → ℕ → Ω → ιz → ℝ)
    (Rop : (ℕ → Ω → ιZ ⊕ ιz → ℝ) → ℕ → Ω → ιZ → ℝ) : Prop :=
  ∀ y φ, MBoundedV S y → MAdaptedV S y → MBoundedV S φ → MAEMeasV S φ → MMultKnown S t0 φ →
    (MEq118 S P t0 y φ ↔ MEq120 S t0 Λ (Qop (xproc P y)) φ ∧ MEq121 S t0 Υ (Rop (xproc P y)) φ)

/-- Woodford (2003), Proposition 8.1, p. 553, on a probability space: matrices `Λ`, `Υ` and
operators `Q(L⁻¹)`, `R(L⁻¹)` (bounded processes to bounded adapted processes) with the
equivalence `MProp81Equiv`. -/
structure MProp81Conclusion (S : MeasExpectationSystem Ω) (P : LQProblem ιZ ιz ιτ) (t0 : ℕ) where
  Λ : Matrix ιz ιz ℝ
  Υ : Matrix ιZ ιz ℝ
  Qop : (ℕ → Ω → ιZ ⊕ ιz → ℝ) → ℕ → Ω → ιz → ℝ
  Rop : (ℕ → Ω → ιZ ⊕ ιz → ℝ) → ℕ → Ω → ιZ → ℝ
  equiv : MProp81Equiv S P t0 Λ Υ Qop Rop
  Qbounded : ∀ x, MBoundedV S x → MBoundedV S (Qop x)
  Rbounded : ∀ x, MBoundedV S x → MBoundedV S (Rop x)
  Qadapted : ∀ x, MAdaptedV S (Qop x)
  Radapted : ∀ x, MBoundedV S x → MAdaptedV S (Rop x)

/-! ### Tools -/

omit [DecidableEq ιZ] in
/-- Woodford (2003), (1.18) (tool): `x = T̃'W(τ − τ*)` of an essentially bounded plan is
essentially bounded. -/
theorem mboundedV_xproc {S : MeasExpectationSystem Ω} (P : LQProblem ιZ ιz ιτ)
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : MBoundedV S y) : MBoundedV S (xproc P y) := by
  obtain ⟨M, hM⟩ := hy
  obtain ⟨K1, hK1⟩ := exists_bound_mulVec P.T M
  obtain ⟨K2, hK2⟩ := exists_bound_mulVec P.W (K1 + ∑ i, |P.τstar i|)
  obtain ⟨K3, hK3⟩ := exists_bound_mulVec P.Ttilᵀ K2
  refine ⟨K3, fun t => (hM t).mono fun ω h r => hK3 _ (hK2 _ (fun a => ?_)) r⟩
  rw [Pi.sub_apply]
  refine (abs_sub _ _).trans (add_le_add (hK1 _ h a) ?_)
  exact Finset.single_le_sum (f := fun i => |P.τstar i|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ a)

/-- Woodford (2003), (1.20) (tool): countably many almost-sure statements at the dates
`t ≥ t₀` hold simultaneously almost surely. -/
theorem ae_forall_ge {μ : Measure Ω} {t0 : ℕ} {p : ℕ → Ω → Prop}
    (h : ∀ t, t0 ≤ t → ∀ᵐ ω ∂μ, p t ω) : ∀ᵐ ω ∂μ, ∀ t, t0 ≤ t → p t ω := by
  have h' : ∀ t, ∀ᵐ ω ∂μ, t0 ≤ t → p t ω := fun t => by
    by_cases ht : t0 ≤ t
    · exact (h t ht).mono fun _ hp _ => hp
    · exact Eventually.of_forall fun _ h0 => absurd h0 ht
  exact ae_all_iff.mpr h'

omit [Fintype ιz] [DecidableEq ιz] in
/-- Woodford (2003), (1.20) (tool): an essentially bounded process has bounded paths almost
surely. -/
theorem ae_bddS {S : MeasExpectationSystem Ω} {M : ℕ → Ω → ιz → ℝ} (hM : MBoundedV S M) :
    ∀ᵐ ω ∂S.μ, BddS (fun t => M t ω) := by
  obtain ⟨K, hK⟩ := hM
  filter_upwards [ae_all_iff.mpr hK] with ω h
  exact ⟨K, fun t i => h t i⟩

/-! ### The base solution of (1.18) -/

/-- Woodford (2003), (1.18), p. 552 (**a bounded solution on every probability space**): the
constant plan `v` with `T̃'W(Tv − τ*) = 0` and zero multipliers is bounded, adapted, and solves
(1.18) almost surely. -/
theorem mbase (S : MeasExpectationSystem Ω) (P : LQProblem ιZ ιz ιτ) (t0 : ℕ)
    {v : (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hv : P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar)) = 0) :
    MBoundedV S (fun (_ : ℕ) (_ : Ω) => v) ∧ MAdaptedV S (fun (_ : ℕ) (_ : Ω) => v) ∧
      MBoundedV S (fun (_ : ℕ) (_ : Ω) => (0 : ιZ ⊕ ιz → ℝ)) ∧
      MAEMeasV S (fun (_ : ℕ) (_ : Ω) => (0 : ιZ ⊕ ιz → ℝ)) ∧
      MMultKnown S t0 (fun (_ : ℕ) (_ : Ω) => (0 : ιZ ⊕ ιz → ℝ)) ∧
      MEq118 S P t0 (fun _ _ => v) (fun _ _ => 0) := by
  refine ⟨⟨∑ i, |v i|, fun _ => Eventually.of_forall fun _ i => ?_⟩,
    fun _ _ => stronglyMeasurable_const, ⟨0, fun _ => Eventually.of_forall fun _ _ => by simp⟩,
    fun _ _ => aestronglyMeasurable_const, fun _ _ _ => stronglyMeasurable_const,
    fun t _ => Eventually.of_forall fun ω => ?_⟩
  · exact Finset.single_le_sum (f := fun i => |v i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)
  · have e : EVm S t (fun _ => (0 : ιZ ⊕ ιz → ℝ)) ω = 0 := by
      funext i
      exact congrFun (S.E_const t 0) ω
    rw [e, mulVec_zero, zero_add, mulVec_zero, smul_zero, sub_zero]
    exact hv

/-- Woodford (2003), (1.20)–(1.21) (tool): along the base solution of `mbase` every
representation has `q_t = 0` and `r_t = 0` almost surely, `t ≥ t₀`. -/
theorem mbase_QR {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (H : MProp81Conclusion S P t0) {v : (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hv : P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar)) = 0) :
    (∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, H.Qop (xproc P fun _ _ => v) t ω = 0) ∧
      ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, H.Rop (xproc P fun _ _ => v) t ω = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := mbase S P t0 hv
  obtain ⟨e120, e121⟩ := (H.equiv _ _ h1 h2 h3 h4 h5).mp h6
  refine ⟨fun t ht => (e120 t ht).mono fun ω h => ?_, fun t ht => (e121 t ht).mono fun ω h => ?_⟩
  · have e0 : Mpart (0 : ιZ ⊕ ιz → ℝ) = 0 := rfl
    rw [e0, mulVec_zero, zero_add] at h
    exact h.symm
  · have e0 : Mpart (0 : ιZ ⊕ ιz → ℝ) = 0 := rfl
    have e1 : ξpart (0 : ιZ ⊕ ιz → ℝ) = 0 := rfl
    rw [e0, e1, mulVec_zero, zero_add] at h
    exact h.symm

/-! ### Uniqueness on the bounded orbits -/

/-- Woodford (2003), p. 553, the remark after Proposition 8.1, **on a probability space**: two
representations agree on the bounded orbits of `Λ`: if `Λᵏ m` is bounded, `Λ m = Λ' m` and
`Υ m = Υ' m`. -/
theorem magree_on_bddOrbit {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (H H' : MProp81Conclusion S P t0) (m : ιz → ℝ) (hm : ∃ K, ∀ k i, |(H.Λ ^ k *ᵥ m) i| ≤ K) :
    H.Λ *ᵥ m = H'.Λ *ᵥ m ∧ H.Υ *ᵥ m = H'.Υ *ᵥ m := by
  obtain ⟨v, hv⟩ := exists_xproc_zero P
  obtain ⟨h1, h2, -, -, -, -⟩ := mbase S P t0 hv
  obtain ⟨hQ, hR⟩ := mbase_QR H hv
  obtain ⟨hQ', hR'⟩ := mbase_QR H' hv
  set φ1 : ℕ → Ω → ιZ ⊕ ιz → ℝ := fun s _ => pert t0 H.Λ H.Υ m s with hφ1
  have hMh : ∀ s ω, Mpart (φ1 s ω) = H.Λ ^ (s - t0) *ᵥ m := fun _ _ => rfl
  have hξh : ∀ s ω, ξpart (φ1 s ω) = H.Υ *ᵥ (H.Λ ^ (s - t0) *ᵥ m) := fun _ _ => rfl
  have hb : MBoundedV S φ1 := by
    obtain ⟨K, hK⟩ := hm
    obtain ⟨KΥ, hKΥ⟩ := exists_bound_mulVec H.Υ K
    refine ⟨max K KΥ, fun s => Eventually.of_forall fun ω a => ?_⟩
    rcases a with a | a
    · exact (hKΥ _ (fun i => hK _ i) a).trans (le_max_right _ _)
    · exact (hK _ a).trans (le_max_left _ _)
  have ha : MAEMeasV S φ1 := fun _ _ => aestronglyMeasurable_const
  have hk : MMultKnown S t0 φ1 := fun _ _ _ => stronglyMeasurable_const
  have h120 : MEq120 S t0 H.Λ (H.Qop (xproc P fun _ _ => v)) φ1 := by
    intro t ht
    filter_upwards [hQ t ht] with ω hq
    rw [hMh _ ω, hMh _ ω, hq, add_zero, mulVec_mulVec, ← pow_succ',
      show t + 1 - t0 = t - t0 + 1 by omega]
  have h121 : MEq121 S t0 H.Υ (H.Rop (xproc P fun _ _ => v)) φ1 := by
    intro t ht
    filter_upwards [hR t ht] with ω hr
    rw [hξh _ ω, hMh _ ω, hr, add_zero]
  have h118 := (H.equiv _ _ h1 h2 hb ha hk).mpr ⟨h120, h121⟩
  obtain ⟨f120, f121⟩ := (H'.equiv _ _ h1 h2 hb ha hk).mp h118
  obtain ⟨ω, a1, a2, b1, b2⟩ := ((f120 t0 le_rfl).and ((hQ' t0 le_rfl).and
    ((f121 t0 le_rfl).and (hR' t0 le_rfl)))).exists
  rw [hMh _ ω, hMh _ ω, a2, add_zero, show t0 + 1 - t0 = 1 by omega, Nat.sub_self, pow_one,
    pow_zero, one_mulVec] at a1
  rw [hξh _ ω, hMh _ ω, b2, add_zero, Nat.sub_self, pow_zero, one_mulVec] at b1
  exact ⟨a1, b1⟩

/-- Woodford (2003), p. 553, **on a probability space**: if `Λ` is power-bounded, `Λ` and `Υ`
are the same in every representation of Proposition 8.1. -/
theorem munique_of_powBdd {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (H H' : MProp81Conclusion S P t0) (hpb : PowBdd H.Λ) : H.Λ = H'.Λ ∧ H.Υ = H'.Υ := by
  obtain ⟨K, hK⟩ := hpb
  have hcol : ∀ j, H.Λ *ᵥ Pi.single j 1 = H'.Λ *ᵥ Pi.single j 1 ∧
      H.Υ *ᵥ Pi.single j 1 = H'.Υ *ᵥ Pi.single j 1 := fun j =>
    magree_on_bddOrbit H H' _ ⟨K, fun k i => by
      rw [mulVec_single_one]
      exact hK k i j⟩
  refine ⟨?_, ?_⟩
  · ext i j
    have := congrFun (hcol j).1 i
    simpa [mulVec_single_one] using this
  · ext i j
    have := congrFun (hcol j).2 i
    simpa [mulVec_single_one] using this

/-! ### Vector tools for conditional expectations -/

omit [Fintype ιz] [DecidableEq ιz] in
/-- Woodford (2003), p. 540 (tool): a fixed matrix applied to a random vector known at `t`. -/
theorem mknownV_mulVec {S : MeasExpectationSystem Ω} {t : ℕ} {κ : Type*} [Fintype κ]
    (A : Matrix ιz κ ℝ) {a : Ω → κ → ℝ} (ha : MKnownV S t a) :
    MKnownV S t (fun ω => A *ᵥ a ω) := fun i =>
  sm_comp ha ((continuous_apply i).comp (continuous_const.matrix_mulVec continuous_id))

omit [DecidableEq ιz] in
/-- Woodford (2003), p. 540 (tool): `a − A b` for random vectors known at `t`. -/
theorem mknownV_sub_mulVec {S : MeasExpectationSystem Ω} {t : ℕ} (A : Matrix ιz ιz ℝ)
    {a b : Ω → ιz → ℝ} (ha : MKnownV S t a) (hb : MKnownV S t b) :
    MKnownV S t (fun ω => a ω - A *ᵥ b ω) := fun i =>
  sm_comp₂ ha hb (g := fun p => p.1 i - (A *ᵥ p.2) i)
    (((continuous_apply i).comp continuous_fst).sub
      ((continuous_apply i).comp (continuous_const.matrix_mulVec continuous_snd)))

omit [Fintype ιz] [DecidableEq ιz] in
/-- Woodford (2003), p. 540 (tool): information known at `s` is known at `t ≥ s`. -/
theorem mknownV_mono {S : MeasExpectationSystem Ω} {s t : ℕ} (hst : s ≤ t) {a : Ω → ιz → ℝ}
    (ha : MKnownV S s a) : MKnownV S t a := fun i => (ha i).mono (S.𝓕.mono hst)

omit [Fintype ιz] [DecidableEq ιz] in
/-- Woodford (2003), p. 540 (tool): the components of a bounded a.e.-measurable process are
integrable. -/
theorem integrable_comp {S : MeasExpectationSystem Ω} {N : ℕ → Ω → ιz → ℝ} (hb : MBoundedV S N)
    (hm : MAEMeasV S N) (t : ℕ) (i : ιz) : Integrable (fun ω => N t ω i) S.μ := by
  obtain ⟨K, hK⟩ := hb
  exact integrable_of_bound (hm t i) ((hK t).mono fun _ h => h i)

omit [DecidableEq ιz] in
/-- Woodford (2003), p. 540 (tool): `A x` has integrable components when `x` does. -/
theorem integrable_mulVec {S : MeasExpectationSystem Ω} (A : Matrix ιz ιz ℝ) {x : Ω → ιz → ℝ}
    (hx : ∀ j, Integrable (fun ω => x ω j) S.μ) (i : ιz) :
    Integrable (fun ω => (A *ᵥ x ω) i) S.μ := by
  have e : (fun ω => (A *ᵥ x ω) i) = fun ω => ∑ j, A i j * x ω j := by
    funext ω
    simp [mulVec, dotProduct]
  rw [e]
  exact integrable_finsetSum _ fun j _ => (hx j).const_mul _

omit [Fintype ιz] [DecidableEq ιz] in
/-- Woodford (2003), p. 540 (tool): `E_t` of a known integrable random vector is itself. -/
theorem EVm_of_known {S : MeasExpectationSystem Ω} {t : ℕ} {x : Ω → ιz → ℝ}
    (hk : MKnownV S t x) (hi : ∀ i, Integrable (fun ω => x ω i) S.μ) : EVm S t x = x := by
  funext ω i
  exact congrFun (S.E_of_stronglyMeasurable (hk i) (hi i)) ω

omit [Fintype ιz] [DecidableEq ιz] in
/-- Woodford (2003), p. 540 (tool): `E_t` respects a.e. equality of random vectors. -/
theorem EVm_congr [Countable ιz] {S : MeasExpectationSystem Ω} (t : ℕ) {x y : Ω → ιz → ℝ}
    (h : ∀ᵐ ω ∂S.μ, x ω = y ω) : ∀ᵐ ω ∂S.μ, EVm S t x ω = EVm S t y ω := by
  have hc : ∀ i, ∀ᵐ ω ∂S.μ, EVm S t x ω i = EVm S t y ω i := fun i =>
    S.E_congr (h.mono fun ω hω => congrFun hω i) t
  filter_upwards [ae_all_iff.mpr hc] with ω hω
  exact funext hω

omit [Fintype ιz] [DecidableEq ιz] in
/-- Woodford (2003), p. 540 (tool): `E_t` is additive on integrable random vectors (a.e.). -/
theorem EVm_add [Countable ιz] {S : MeasExpectationSystem Ω} (t : ℕ) {x y : Ω → ιz → ℝ}
    (hx : ∀ i, Integrable (fun ω => x ω i) S.μ) (hy : ∀ i, Integrable (fun ω => y ω i) S.μ) :
    ∀ᵐ ω ∂S.μ, EVm S t (fun ω => x ω + y ω) ω = EVm S t x ω + EVm S t y ω := by
  have hc : ∀ i, ∀ᵐ ω ∂S.μ, EVm S t (fun ω => x ω + y ω) ω i = EVm S t x ω i + EVm S t y ω i :=
    fun i => S.E_add (hx i) (hy i) t
  filter_upwards [ae_all_iff.mpr hc] with ω hω
  exact funext hω

/-! ### Re-representation on a probability space -/

omit [DecidableEq ιz] in
/-- Woodford (2003), (1.20), on a probability space: `N` is an essentially bounded, a.e.-measurable
solution of `N_{t+1} = Λ N_t + q_t` (a.s.) from `t₀`, with `N_{t+1}` known at `t`. -/
def RecSolMm (S : MeasExpectationSystem Ω) (t0 : ℕ) (Λ : Matrix ιz ιz ℝ)
    (q N : ℕ → Ω → ιz → ℝ) : Prop :=
  MBoundedV S N ∧ MAEMeasV S N ∧ (∀ t, t0 ≤ t → MKnownV S t (N (t + 1))) ∧
    ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, N (t + 1) ω = Λ *ᵥ N t ω + q t ω

omit [DecidableEq ιz] in
/-- Woodford (2003), (1.20) (**normalisation on a probability space**): if `q_{t₀}` is bounded and
known at `t₀`, a solution can be chosen with `N_{t₀}` known at `t₀`: replace `N_{t₀}` by
`E_{t₀} N_{t₀}`. -/
theorem mnormalize {S : MeasExpectationSystem Ω} {t0 : ℕ} {Λ : Matrix ιz ιz ℝ}
    {q : ℕ → Ω → ιz → ℝ} (hq : MKnownV S t0 (q t0)) (hqb : ∃ K, ∀ᵐ ω ∂S.μ, ∀ i, |q t0 ω i| ≤ K)
    {N : ℕ → Ω → ιz → ℝ} (hN : RecSolMm S t0 Λ q N) :
    ∃ N', RecSolMm S t0 Λ q N' ∧ MKnownV S t0 (N' t0) := by
  classical
  obtain ⟨⟨K, hK⟩, hm, hk, hr⟩ := hN
  have hint := integrable_comp ⟨K, hK⟩ hm
  set N' : ℕ → Ω → ιz → ℝ := fun t => if t = t0 then EVm S t0 (N t0) else N t with hN'
  have hNs : ∀ t, t ≠ t0 → N' t = N t := fun t h => by rw [hN']; simp [h]
  have hN0 : N' t0 = EVm S t0 (N t0) := by rw [hN']; simp
  have hqi : ∀ i, Integrable (fun ω => q t0 ω i) S.μ := fun i => by
    obtain ⟨Kq, hKq⟩ := hqb
    exact integrable_of_bound ((hq i).mono (S.𝓕.le t0)).aestronglyMeasurable
      (hKq.mono fun _ h => h i)
  refine ⟨N', ⟨⟨K, fun t => ?_⟩, fun t i => ?_, fun t ht => ?_, fun t ht => ?_⟩, ?_⟩
  · by_cases h : t = t0
    · rw [h, hN0]
      have hc : ∀ i, ∀ᵐ ω ∂S.μ, |EVm S t0 (N t0) ω i| ≤ K := fun i =>
        S.abs_E_le ((hK t0).mono fun _ h => h i) t0
      exact ae_all_iff.mpr hc
    · rw [hNs t h]
      exact hK t
  · by_cases h : t = t0
    · rw [h, hN0]
      exact ((S.stronglyMeasurable_E t0 _).mono (S.𝓕.le t0)).aestronglyMeasurable
    · rw [hNs t h]
      exact hm t i
  · rw [hNs (t + 1) (by omega)]
    exact hk t ht
  · rw [hNs (t + 1) (by omega)]
    by_cases h : t = t0
    · subst h
      rw [hN0]
      have e1 : EVm S t (N (t + 1)) = N (t + 1) := EVm_of_known (hk t le_rfl) (hint (t + 1))
      have e2 := EVm_congr (S := S) t (hr t le_rfl)
      have e3 := EVm_add (S := S) t (integrable_mulVec Λ (hint t)) hqi
      have e4 := EVm_mulVec S t Λ (hint t)
      have e5 : EVm S t (q t) = q t := EVm_of_known hq hqi
      filter_upwards [e2, e3, e4] with ω a2 a3 a4
      rw [← congrFun e1 ω, a2, a3, a4, e5]
    · rw [hNs t h]
      exact hr t ht
  · rw [hN0]
    exact fun i => S.stronglyMeasurable_E t0 _

open Classical in
omit [Fintype ιZ] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), (1.20) (the modified operator `Q'` on a probability space): on a plan whose
recursion has a solution `N` (chosen with `N_{t₀}` known at `t₀`), `q'_t = N_{t+1} − Λ' N_t` from
`t₀` on; on a plan with none, the forcing `b x`. -/
noncomputable def reQMm (S : MeasExpectationSystem Ω) (t0 : ℕ) (Λ Λ' : Matrix ιz ιz ℝ)
    (Q : (ℕ → Ω → ιZ ⊕ ιz → ℝ) → ℕ → Ω → ιz → ℝ)
    (b : (ℕ → Ω → ιZ ⊕ ιz → ℝ) → ℕ → Ω → ιz → ℝ) :
    (ℕ → Ω → ιZ ⊕ ιz → ℝ) → ℕ → Ω → ιz → ℝ :=
  fun x => if h : ∃ N, RecSolMm S t0 Λ (Q x) N ∧ MKnownV S t0 (N t0) then
    fun t ω => if t0 ≤ t then Classical.choose h (t + 1) ω - Λ' *ᵥ Classical.choose h t ω
      else Q x t ω
    else b x

/-- Woodford (2003), Proposition 8.1, p. 553 (**re-representation on a probability space**): if
`Λ'` has the same bounded homogeneous solutions as `H.Λ` (path by path) and, on every bounded
plan without a solution of the `H.Λ` recursion, the `Λ'` recursion with forcing `b x` has none
either, then `(Λ', H.Υ, reQMm, H.Rop)` represents the solutions of (1.18) a.s. -/
theorem mreRep_equiv {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (H : MProp81Conclusion S P t0) {Λ' : Matrix ιz ιz ℝ} (hsame : HomSame t0 H.Λ Λ')
    (b : (ℕ → Ω → ιZ ⊕ ιz → ℝ) → ℕ → Ω → ιz → ℝ)
    (hb : ∀ x, MBoundedV S x → ¬ (∃ N, RecSolMm S t0 H.Λ (H.Qop x) N) →
      ∀ D, ¬ RecSolMm S t0 Λ' (b x) D) :
    MProp81Equiv S P t0 Λ' H.Υ (reQMm S t0 H.Λ Λ' H.Qop b) H.Rop := by
  intro y φ hyb hya hφb hφa hφk
  set x := xproc P y with hx
  have hxb : MBoundedV S x := mboundedV_xproc P hyb
  set m : ℕ → Ω → ιz → ℝ := fun t ω => Mpart (φ t ω) with hm
  have hmb : MBoundedV S m := by
    obtain ⟨K, hK⟩ := hφb
    exact ⟨K, fun t => (hK t).mono fun _ h i => h (Sum.inr i)⟩
  have hma : MAEMeasV S m := fun t i => hφa t (Sum.inr i)
  have hE120 : ∀ (L : Matrix ιz ιz ℝ) (q' : ℕ → Ω → ιz → ℝ), MEq120 S t0 L q' φ ↔
      ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, m (t + 1) ω = L *ᵥ m t ω + q' t ω := fun _ _ => Iff.rfl
  rw [H.equiv y φ hyb hya hφb hφa hφk, hE120, hE120]
  have hqk : MKnownV S t0 (H.Qop x t0) := H.Qadapted x t0
  have hqb : ∃ K, ∀ᵐ ω ∂S.μ, ∀ i, |H.Qop x t0 ω i| ≤ K := by
    obtain ⟨K, hK⟩ := H.Qbounded x hxb
    exact ⟨K, hK t0⟩
  by_cases hs : ∃ N, RecSolMm S t0 H.Λ (H.Qop x) N ∧ MKnownV S t0 (N t0)
  · have hQ : ∀ t, t0 ≤ t → ∀ ω, reQMm S t0 H.Λ Λ' H.Qop b x t ω =
        Classical.choose hs (t + 1) ω - Λ' *ᵥ Classical.choose hs t ω := by
      intro t ht ω
      simp only [reQMm]
      rw [dite_eq_left hs]
      simp [ht]
    obtain ⟨⟨hNb, -, -, hNr⟩, -⟩ := Classical.choose_spec hs
    set N := Classical.choose hs
    have hD : ∀ᵐ ω ∂S.μ, BddS (fun t => m t ω - N t ω) := by
      filter_upwards [ae_bddS hmb, ae_bddS hNb] with ω ⟨K1, h1⟩ ⟨K2, h2⟩
      exact ⟨K1 + K2, fun t i => (abs_sub _ _).trans (add_le_add (h1 t i) (h2 t i))⟩
    have hNall := ae_forall_ge hNr
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun t ht => ?_, h2⟩
      filter_upwards [ae_forall_ge h1, hNall, hD] with ω a1 a2 a3
      have hDh := ((hsame _ a3).mp fun s hs => by
        rw [a1 s hs, a2 s hs, mulVec_sub]; abel) t ht
      rw [hQ t ht ω]
      have : m (t + 1) ω = N (t + 1) ω + Λ' *ᵥ (m t ω - N t ω) := by rw [← hDh]; abel
      rw [this, mulVec_sub]
      abel
    · rintro ⟨h1, h2⟩
      refine ⟨fun t ht => ?_, h2⟩
      filter_upwards [ae_forall_ge h1, hNall, hD] with ω a1 a2 a3
      have hDh := ((hsame _ a3).mpr fun s hs => by
        rw [a1 s hs, hQ s hs ω, mulVec_sub]; abel) t ht
      have : m (t + 1) ω = N (t + 1) ω + H.Λ *ᵥ (m t ω - N t ω) := by rw [← hDh]; abel
      rw [this, a2 t ht, mulVec_sub]
      abel
  · have hQ : reQMm S t0 H.Λ Λ' H.Qop b x = b x := by
      simp only [reQMm]
      rw [dite_eq_right hs]
    have hno : ¬ ∃ N, RecSolMm S t0 H.Λ (H.Qop x) N := fun ⟨N, hN⟩ =>
      hs (mnormalize hqk hqb hN)
    rw [hQ]
    constructor
    · rintro ⟨h1, -⟩
      exact absurd ⟨m, hmb, hma, fun t ht => hφk t ht, h1⟩ hno
    · rintro ⟨h1, -⟩
      exact absurd ⟨hmb, hma, fun t ht => hφk t ht, h1⟩ (hb x hxb hno m)

/-- Woodford (2003), Proposition 8.1 (**re-representation on a probability space**): the
representation of `mreRep_equiv` as an `MProp81Conclusion`; the forcing `b` must be adapted, and
bounded on bounded plans. -/
noncomputable def mreRep {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (H : MProp81Conclusion S P t0) (Λ' : Matrix ιz ιz ℝ) (hsame : HomSame t0 H.Λ Λ')
    (b : (ℕ → Ω → ιZ ⊕ ιz → ℝ) → ℕ → Ω → ιz → ℝ)
    (hba : ∀ x, MAdaptedV S (b x)) (hbb : ∀ x, MBoundedV S x → MBoundedV S (b x))
    (hb : ∀ x, MBoundedV S x → ¬ (∃ N, RecSolMm S t0 H.Λ (H.Qop x) N) →
      ∀ D, ¬ RecSolMm S t0 Λ' (b x) D) : MProp81Conclusion S P t0 where
  Λ := Λ'
  Υ := H.Υ
  Qop := reQMm S t0 H.Λ Λ' H.Qop b
  Rop := H.Rop
  equiv := mreRep_equiv H hsame b hb
  Qbounded := fun x hx => by
    by_cases hs : ∃ N, RecSolMm S t0 H.Λ (H.Qop x) N ∧ MKnownV S t0 (N t0)
    · obtain ⟨⟨⟨K, hK⟩, -, -, -⟩, -⟩ := Classical.choose_spec hs
      obtain ⟨K', hK'⟩ := exists_bound_mulVec Λ' K
      obtain ⟨KQ, hKQ⟩ := H.Qbounded x hx
      refine ⟨K + K' + |KQ|, fun t => ?_⟩
      filter_upwards [hK t, hK (t + 1), hKQ t] with ω a0 a1 aq
      intro i
      simp only [reQMm]
      rw [dite_eq_left hs]
      split_ifs
      · exact ((abs_sub _ _).trans (add_le_add (a1 i) (hK' _ a0 i))).trans
          (le_add_of_nonneg_right (abs_nonneg _))
      · have h2 := (abs_nonneg _).trans (a0 i)
        have h3 := (abs_nonneg _).trans (hK' _ a0 i)
        linarith [aq i, le_abs_self KQ]
    · obtain ⟨K, hK⟩ := hbb x hx
      refine ⟨K, fun t => (hK t).mono fun ω h i => ?_⟩
      simp only [reQMm]
      rw [dite_eq_right hs]
      exact h i
  Rbounded := H.Rbounded
  Qadapted := fun x t => by
    by_cases hs : ∃ N, RecSolMm S t0 H.Λ (H.Qop x) N ∧ MKnownV S t0 (N t0)
    · obtain ⟨⟨-, -, hk, -⟩, h0⟩ := Classical.choose_spec hs
      by_cases ht : t0 ≤ t
      · have e : reQMm S t0 H.Λ Λ' H.Qop b x t = fun ω =>
            Classical.choose hs (t + 1) ω - Λ' *ᵥ Classical.choose hs t ω := by
          funext ω
          simp only [reQMm]
          rw [dite_eq_left hs]
          simp [ht]
        rw [e]
        have hNt : MKnownV S t (Classical.choose hs t) := by
          rcases ht.lt_or_eq with hlt | heq
          · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
            exact mknownV_mono (Nat.le_succ s) (hk s (by omega))
          · rw [← heq]
            exact h0
        exact mknownV_sub_mulVec Λ' (hk t ht) hNt
      · have e : reQMm S t0 H.Λ Λ' H.Qop b x t = H.Qop x t := by
          funext ω
          simp only [reQMm]
          rw [dite_eq_left hs]
          simp [ht]
        rw [e]
        exact H.Qadapted x t
    · have e : reQMm S t0 H.Λ Λ' H.Qop b x = b x := by
        simp only [reQMm]
        rw [dite_eq_right hs]
      rw [e]
      exact hba x t
  Radapted := H.Radapted

/-! ### The two constructions and the exact criterion -/

/-- Woodford (2003), Proposition 8.1, p. 553 (**conjugated representation on a probability
space**): if `G` (inverse `Gi`) fixes the bounded orbits of `H.Λ`, there is a representation with
`Λ' = G Λ Gi` and the same `Υ`. -/
theorem mconj_rep {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (H : MProp81Conclusion S P t0) {G Gi : Matrix ιz ιz ℝ} (hGGi : G * Gi = 1)
    (hGiG : Gi * G = 1) (hfix : ∀ v ∈ bddOrb H.Λ, G *ᵥ v = v) :
    ∃ H' : MProp81Conclusion S P t0, H'.Λ = G * H.Λ * Gi ∧ H'.Υ = H.Υ := by
  refine ⟨mreRep H (G * H.Λ * Gi) (conj_homSame t0 hGGi hGiG hfix)
    (fun x t ω => G *ᵥ H.Qop x t ω) (fun x t => mknownV_mulVec G (H.Qadapted x t))
    (fun x hx => ?_) (fun x _ hs D hD => ?_), rfl, rfl⟩
  · obtain ⟨K, hK⟩ := H.Qbounded x hx
    obtain ⟨K', hK'⟩ := exists_bound_mulVec G K
    exact ⟨K', fun t => (hK t).mono fun _ h i => hK' _ h i⟩
  · obtain ⟨⟨K, hK⟩, hm, hk, hr⟩ := hD
    obtain ⟨K', hK'⟩ := exists_bound_mulVec Gi K
    refine hs ⟨fun t ω => Gi *ᵥ D t ω, ⟨K', fun t => (hK t).mono fun _ h i => hK' _ h i⟩,
      fun t i => ?_, fun t ht => mknownV_mulVec Gi (hk t ht), fun t ht => ?_⟩
    · exact aesm_comp (hm t) ((continuous_apply i).comp (continuous_const.matrix_mulVec
        continuous_id))
    · filter_upwards [hr t ht] with ω h
      rw [h, mulVec_add, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec,
        ← Matrix.mul_assoc, ← Matrix.mul_assoc, hGiG, Matrix.one_mul, one_mulVec]

/-- Woodford (2003), Proposition 8.1, p. 553 (**sign-flipped representation on a probability
space**): if `Λ = c I` with `|c| > 1`, then `Λ' = −c I` (same `Υ`) is also a representation;
the forcing is `(−1)^{t+1} q_t`. -/
theorem mneg_rep {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (H : MProp81Conclusion S P t0) {c : ℝ} (hΛ : H.Λ = c • 1) (hc : 1 < |c|) :
    ∃ H' : MProp81Conclusion S P t0, H'.Λ = (-c) • 1 ∧ H'.Υ = H.Υ := by
  have hc2 : 1 < |-c| := by rwa [abs_neg]
  have hsame : HomSame t0 H.Λ ((-c) • 1) := by
    intro D hD
    rw [hΛ]
    have key : ∀ (d : ℝ), 1 < |d| →
        (∀ t, t0 ≤ t → D (t + 1) = (d • (1 : Matrix ιz ιz ℝ)) *ᵥ D t) →
        ∀ (e : ℝ), ∀ t, t0 ≤ t → D (t + 1) = (e • (1 : Matrix ιz ιz ℝ)) *ᵥ D t := by
      intro d hd h e t ht
      rw [zero_of_scalar hd hD h t ht, zero_of_scalar hd hD h (t + 1) (by omega), mulVec_zero]
    exact ⟨fun h => key c hc h (-c), fun h => key (-c) hc2 h c⟩
  have hsgn : ∀ t : ℕ, ((-1 : ℝ) ^ t) * (-1) ^ t = 1 := fun t => by
    rw [← mul_pow]; norm_num
  refine ⟨mreRep H ((-c) • 1) hsame (fun x t ω => ((-1 : ℝ) ^ (t + 1)) • H.Qop x t ω)
    (fun x t i => ?_) (fun x hx => ?_) (fun x _ hs D hD => ?_), rfl, rfl⟩
  · exact (H.Qadapted x t i).const_smul ((-1 : ℝ) ^ (t + 1))
  · obtain ⟨K, hK⟩ := H.Qbounded x hx
    refine ⟨K, fun t => (hK t).mono fun ω h i => ?_⟩
    change |(((-1 : ℝ) ^ (t + 1)) • H.Qop x t ω) i| ≤ K
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact h i
  · obtain ⟨⟨K, hK⟩, hm, hk, hr⟩ := hD
    refine hs ⟨fun t ω => ((-1 : ℝ) ^ t) • D t ω, ⟨K, fun t => (hK t).mono fun ω h i => ?_⟩,
      fun t i => (hm t i).const_smul ((-1 : ℝ) ^ t), fun t ht i =>
        (hk t ht i).const_smul ((-1 : ℝ) ^ (t + 1)), fun t ht => ?_⟩
    · change |(((-1 : ℝ) ^ t) • D t ω) i| ≤ K
      rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact h i
    · filter_upwards [hr t ht] with ω h
      rw [h, hΛ]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, smul_mulVec, one_mulVec, mulVec_smul]
      linear_combination (H.Qop x t ω i) * hsgn (t + 1)

/-- Woodford (2003), p. 553, the remark after Proposition 8.1 (**general converse on a
probability space**): if `Λ` is not power-bounded, some other representation has a different
`Λ'` (and the same `Υ`). -/
theorem mnot_unique_of_not_powBdd {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ}
    {t0 : ℕ} (H : MProp81Conclusion S P t0) (hnp : ¬ PowBdd H.Λ) :
    ∃ H' : MProp81Conclusion S P t0, H'.Λ ≠ H.Λ ∧ H'.Υ = H.Υ := by
  have hne : Nonempty ιz := by
    by_contra h0
    exact hnp ⟨0, fun _ i => absurd ⟨i⟩ h0⟩
  obtain ⟨i0⟩ := hne
  by_cases hsc : ∃ c : ℝ, H.Λ = c • 1
  · obtain ⟨c, hc⟩ := hsc
    have hc1 : 1 < |c| := by
      by_contra hle
      push Not at hle
      refine hnp ⟨1, fun k i j => ?_⟩
      rw [hc, smul_pow, one_pow, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, abs_mul,
        abs_pow]
      have h1 : |c| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg c) hle
      split_ifs <;> simp [h1]
    obtain ⟨H', h1, h2⟩ := mneg_rep H hc hc1
    refine ⟨H', fun h => ?_, h2⟩
    have e := congrFun (congrFun (h1.symm.trans (h.trans hc)) i0) i0
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e
    have hc0 : c ≠ 0 := fun h0 => by rw [h0, abs_zero] at hc1; linarith
    exact hc0 (by linarith)
  · have hlt : bddOrb H.Λ < ⊤ := lt_top_iff_ne_top.mpr fun h => hnp (powBdd_of_top h)
    obtain ⟨f, hf0, hfV⟩ := (bddOrb H.Λ).exists_le_ker_of_lt_top hlt
    set w : ιz → ℝ := fun i => f (Pi.single i 1) with hw
    have hwf : ∀ v, w ⬝ᵥ v = f v := by
      intro v
      conv_rhs => rw [pi_eq_sum_univ v]
      rw [map_sum]
      simp only [map_smul, smul_eq_mul, dotProduct, hw]
      exact Finset.sum_congr rfl fun i _ => by
        rw [mul_comm]
        congr 2
        funext j
        simp only [Pi.single_apply, eq_comm]
    have hw0 : ∃ b, w b ≠ 0 := by
      by_contra hall
      push Not at hall
      refine hf0 (LinearMap.ext fun v => ?_)
      rw [← hwf, LinearMap.zero_apply, dotProduct]
      exact Finset.sum_eq_zero fun i _ => by rw [hall i, zero_mul]
    obtain ⟨b, hb⟩ := hw0
    have hnc : ∃ i, ∀ s : ℝ, s ≠ 0 →
        vecMulVec (Pi.single i s) (w ᵥ* H.Λ) ≠ vecMulVec (H.Λ *ᵥ Pi.single i s) w := by
      by_contra hall
      push Not at hall
      exact hsc ⟨_, scalar_of_comm hb hall⟩
    obtain ⟨i, hi⟩ := hnc
    obtain ⟨s, hs0, hsdet⟩ : ∃ s : ℝ, s ≠ 0 ∧ 1 + w i * s ≠ 0 := by
      by_cases h1 : 1 + w i * 1 = 0
      · refine ⟨2, two_ne_zero, ?_⟩
        intro h2
        linarith
      · exact ⟨1, one_ne_zero, h1⟩
    set u : ιz → ℝ := Pi.single i s with hu
    set G : Matrix ιz ιz ℝ := 1 + vecMulVec u w with hG
    have hdet : IsUnit G.det := by
      rw [hG, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, hu,
        dotProduct_single]
      exact isUnit_iff_ne_zero.mpr hsdet
    have hfix : ∀ v ∈ bddOrb H.Λ, G *ᵥ v = v := by
      intro v hv
      have h0 : w ⬝ᵥ v = 0 := by rw [hwf]; exact hfV hv
      rw [hG, add_mulVec, one_mulVec]
      conv_rhs => rw [← add_zero v]
      congr 1
      funext a
      simp only [mulVec, dotProduct, vecMulVec_apply, Pi.zero_apply, mul_assoc,
        ← Finset.mul_sum]
      rw [show (∑ x, w x * v x) = w ⬝ᵥ v from rfl, h0, mul_zero]
    obtain ⟨H', h1, h2⟩ := mconj_rep H (mul_nonsing_inv G hdet) (nonsing_inv_mul G hdet) hfix
    refine ⟨H', fun h => hi s hs0 ?_, h2⟩
    have hcomm : G * H.Λ = H.Λ * G := by
      calc G * H.Λ = G * H.Λ * G⁻¹ * G := by
            rw [Matrix.mul_assoc _ G⁻¹, nonsing_inv_mul G hdet, Matrix.mul_one]
        _ = H.Λ * G := by rw [← h1, h]
    rw [hG, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, vecMulVec_mul,
      mul_vecMulVec] at hcomm
    exact add_left_cancel hcomm

/-- **Woodford (2003), p. 553, the remark after Proposition 8.1 (exact criterion on the
conditional-expectation model)**: on every probability space, `Λ` and `Υ` are the same in every
representation of Proposition 8.1 iff `Λ` is power-bounded. No further hypothesis is needed: the
sample space of a probability measure is nonempty, and (1.18) always has a bounded solution
(`mbase`). -/
theorem munique_iff_powBdd {S : MeasExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (H : MProp81Conclusion S P t0) :
    (∀ H' : MProp81Conclusion S P t0, H'.Λ = H.Λ ∧ H'.Υ = H.Υ) ↔ PowBdd H.Λ := by
  constructor
  · intro hall
    by_contra hnp
    obtain ⟨H', h1, -⟩ := mnot_unique_of_not_powBdd H hnp
    exact h1 (hall H').1
  · intro hpb H'
    obtain ⟨h1, h2⟩ := munique_of_powBdd H H' hpb
    exact ⟨h1.symm, h2.symm⟩

end Woodford.OptimalPolicyRules.TidyR6aReRepMeasure
