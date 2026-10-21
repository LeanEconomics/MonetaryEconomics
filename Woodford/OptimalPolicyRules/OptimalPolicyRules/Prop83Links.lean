/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.Prop84General
import OptimalPolicyRules.PencilAssumptions

/-!
# Propositions 8.3 and 8.4 for the general representation of Proposition 8.1

Woodford (2003), *Interest and Prices*, Chapter 8, §1.4–1.5, pp. 553–559.

`Prop83.prop83` was proved for every matrix `Λ` of the (original) hypothesis structure
`TargetCriterion.Prop81.Prop81Conclusion`. Proposition 8.1 is now proved in general, in the
corrected form `Prop81General.Prop81ConclusionM` (multipliers `M_t` known at `t`, adapted plans),
which is the form that holds under uncertainty. This module connects the two.

## Main results

* `hequiv_of_prop81M`: the corrected Proposition 8.1 gives the perturbation hypothesis of
  `Prop83.prop83_of_perturbation` at any bounded solution of the first-order conditions.
* `prop83M_bounds`, `prop83M`: **Proposition 8.3 for every representation `Prop81ConclusionM`**
  (Assumptions 8.1, 8.3, 8.7; no root of (1.15) on `|λ| = β⁻¹` for the exact count).
* `prop83_of_assumptions`: Proposition 8.1 (from Assumptions 8.2 (i), 8.3, 8.4,
  `PencilAssumptions.prop81_of_assumptions`) and Proposition 8.3 together.
* `prop84M`: **Proposition 8.4** for every representation `Prop81ConclusionM`.
-/

namespace Woodford.OptimalPolicyRules.Prop83Links

open Matrix Polynomial GeneralSetup GeneralFOC GeneralFOC.LQ Adjugate
open TargetCriterion (zerosInside fwdOp lagOp prop84_conditional roots_reverse_outside
  map_reverse_ofReal)
open TargetCriterion.Prop81
open Prop81General (Prop81ConclusionM MultKnown)

variable {Ω : Type*} {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-- Woodford (2003), Proposition 8.1, p. 553 (corrected): perturbing a bounded solution `φ₀`
(with `M_t` known at `t`) of (1.18) by a bounded deterministic `h` keeps the multipliers known,
so the representation `Prop81ConclusionM` applies to `φ₀ + h`: this is the hypothesis of
`Prop83.prop83_of_perturbation`. -/
theorem hequiv_of_prop81M {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (H : Prop81ConclusionM P 𝔼 t0) {y0 : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ0 : ℕ → Ω → ιZ ⊕ ιz → ℝ} (hy0b : BoundedV y0) (hy0a : AdaptedV 𝔼 y0)
    (hφ0b : BoundedV φ0) (hφ0m : MultKnown 𝔼 t0 φ0) :
    ∀ h : ℕ → ιZ ⊕ ιz → ℝ, Prop83.BddSeq h →
      (Eq118 P 𝔼 t0 y0 (fun t ω => φ0 t ω + h (t - t0)) ↔
        Eq120 t0 H.Λ (H.Qop (xproc P y0)) (fun t ω => φ0 t ω + h (t - t0)) ∧
          Eq121 t0 H.Υ (H.Rop (xproc P y0)) (fun t ω => φ0 t ω + h (t - t0))) := by
  intro h hb
  refine H.equiv y0 _ hy0b hy0a ?_ ?_
  · obtain ⟨M, hM⟩ := hφ0b
    obtain ⟨C, hC⟩ := hb
    refine ⟨M + C, fun t ω i => (abs_add_le _ _).trans (add_le_add (hM t ω i) ?_)⟩
    have := hC (t - t0) i
    rwa [Real.norm_eq_abs] at this
  · intro t ht r
    have h1 := hφ0m t ht r
    have e : (fun ω => Mpart (φ0 (t + 1) ω + h (t + 1 - t0)) r) =
        (fun ω => Mpart (φ0 (t + 1) ω) r) + fun _ => h (t + 1 - t0) (Sum.inr r) := rfl
    rw [e, map_add, h1, 𝔼.const]

/-- **Woodford (2003), Proposition 8.3, pp. 556–557, two-sided, for every representation of the
corrected Proposition 8.1.** Under Assumptions 8.1, 8.3 and 8.7 (`n_Z + m` roots of (1.15) with
`|μ| < β⁻¹`), `α(L) = det(I − ΛL)` has at most `m` zeros inside the unit circle and at least `m`
in the closed unit disc. -/
theorem prop83M_bounds [Nonempty Ω] {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω}
    {t0 : ℕ} (H : Prop81ConclusionM P 𝔼 t0) (hA : Assumption81 P 𝔼 t0)
    (h83 : PencilEigen.Assumption83 P.sys) {m : ℕ}
    (h87 : P.sys.stableCount P.β⁻¹ = Fintype.card ιZ + m) :
    zerosInside (alpha H.Λ) ≤ m ∧
      m ≤ zerosInside (alpha H.Λ) + Prop83.zerosOnCircle (alpha H.Λ) := by
  obtain ⟨y, φ, hyb, hya, hφb, hφm, h118⟩ := Prop83.exists_base_of_assumption81 hA
  exact Prop83.bounds_of_homEquiv
    (Prop83.homEquiv_of_perturbation h118 (hequiv_of_prop81M H hyb hya hφb hφm)) P.β_pos h83 h87

/-- **Woodford (2003), Proposition 8.3, pp. 556–557, for every representation of the corrected
Proposition 8.1** (any expectation system, nonempty sample space): under Assumptions 8.1, 8.3
and 8.7, with no root of (1.15) on `|λ| = β⁻¹`, `α(L) = det(I − ΛL)` has exactly `m` zeros
inside the unit circle, and none on it. -/
theorem prop83M [Nonempty Ω] {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (H : Prop81ConclusionM P 𝔼 t0) (hA : Assumption81 P 𝔼 t0)
    (h83 : PencilEigen.Assumption83 P.sys) {m : ℕ}
    (h87 : P.sys.stableCount P.β⁻¹ = Fintype.card ιZ + m)
    (hcirc : ∀ l ∈ P.sys.pencilPoly.roots, ‖l‖ ≠ P.β⁻¹) :
    zerosInside (alpha H.Λ) = m ∧ Prop83.zerosOnCircle (alpha H.Λ) = 0 := by
  obtain ⟨y, φ, hyb, hya, hφb, hφm, h118⟩ := Prop83.exists_base_of_assumption81 hA
  have hE := Prop83.homEquiv_of_perturbation h118 (hequiv_of_prop81M H hyb hya hφb hφm)
  exact ⟨Prop83.eq_of_homEquiv hE P.β_pos h83 h87 hcirc,
    Prop83.zerosOnCircle_eq_zero hE P.β_pos h83.regular hcirc⟩

/-- Woodford (2003), (1.18), p. 540: a constant plan `y_t = v₀` with `T̃'W(T v₀ − τ*) = 0` and
zero multipliers is a bounded adapted solution of the first-order conditions (with `M_t` known
at `t`): a base point for Proposition 8.3 that needs no Assumption 8.1. -/
theorem const_base (P : LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    (v0 : (ιZ ⊕ ιz) ⊕ Unit → ℝ) (hv0 : P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v0 - P.τstar)) = 0) :
    BoundedV (fun (_ : ℕ) (_ : Ω) => v0) ∧ AdaptedV 𝔼 (fun (_ : ℕ) (_ : Ω) => v0) ∧
      BoundedV (fun (_ : ℕ) (_ : Ω) (_ : ιZ ⊕ ιz) => (0 : ℝ)) ∧
      MultKnown 𝔼 t0 (fun (_ : ℕ) (_ : Ω) (_ : ιZ ⊕ ιz) => (0 : ℝ)) ∧
      Eq118 P 𝔼 t0 (fun _ _ => v0) (fun _ _ _ => 0) := by
  refine ⟨⟨∑ i, |v0 i|, fun _ _ i =>
      Finset.single_le_sum (f := fun i => |v0 i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)⟩,
    fun t i => 𝔼.const t (v0 i), ⟨0, fun _ _ _ => by simp⟩, fun t _ _ => 𝔼.const t 0, ?_⟩
  intro t _ ω
  have e : EV 𝔼 t (fun (_ : Ω) (_ : ιZ ⊕ ιz) => (0 : ℝ)) = fun _ _ => 0 :=
    PencilSplit.EV_const 𝔼 t (fun _ => 0)
  simp only [e, hv0]
  simp [← Pi.zero_def]

/-- **Woodford (2003), Proposition 8.3, pp. 556–557, for every representation of the corrected
Proposition 8.1, without Assumption 8.1**, when a constant plan attains the targets in the sense
`T̃'W(T v₀ − τ*) = 0` (`const_base`): under Assumptions 8.3 and 8.7, with no root of (1.15) on
`|λ| = β⁻¹`, `α(L) = det(I − ΛL)` has exactly `m` zeros inside the unit circle, and none on it. -/
theorem prop83M_const [Nonempty Ω] {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (H : Prop81ConclusionM P 𝔼 t0) (v0 : (ιZ ⊕ ιz) ⊕ Unit → ℝ)
    (hv0 : P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v0 - P.τstar)) = 0)
    (h83 : PencilEigen.Assumption83 P.sys) {m : ℕ}
    (h87 : P.sys.stableCount P.β⁻¹ = Fintype.card ιZ + m)
    (hcirc : ∀ l ∈ P.sys.pencilPoly.roots, ‖l‖ ≠ P.β⁻¹) :
    zerosInside (alpha H.Λ) = m ∧ Prop83.zerosOnCircle (alpha H.Λ) = 0 := by
  obtain ⟨hyb, hya, hφb, hφm, h118⟩ := const_base P 𝔼 t0 v0 hv0
  have hE := Prop83.homEquiv_of_perturbation h118 (hequiv_of_prop81M H hyb hya hφb hφm)
  exact ⟨Prop83.eq_of_homEquiv hE P.β_pos h83 h87 hcirc,
    Prop83.zerosOnCircle_eq_zero hE P.β_pos h83.regular hcirc⟩

/-- **Woodford (2003), Propositions 8.1 and 8.3 together, pp. 553–557.** Under Assumptions 8.1,
8.2 (case (i)), 8.3, 8.4 and 8.7, with no root of (1.15) on `|λ| = β⁻¹`, Proposition 8.1 holds
and every representation it delivers has `α(L)` with exactly `m` zeros inside the unit circle. -/
theorem prop83_of_assumptions [Nonempty Ω] (P : LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω)
    (t0 : ℕ) (hA : Assumption81 P 𝔼 t0) (h82 : PencilEigen.Assumption82 P.sys P.β)
    (hi : GeneralFOC.Selection.ConjClosed h82.sel) (h83 : PencilEigen.Assumption83 P.sys)
    (h84 : PencilAssumptions.Assumption84 P.sys h82.sel) {m : ℕ}
    (h87 : P.sys.stableCount P.β⁻¹ = Fintype.card ιZ + m)
    (hcirc : ∀ l ∈ P.sys.pencilPoly.roots, ‖l‖ ≠ P.β⁻¹) :
    Nonempty (Prop81ConclusionM P 𝔼 t0) ∧
      ∀ H : Prop81ConclusionM P 𝔼 t0, zerosInside (alpha H.Λ) = m :=
  ⟨PencilAssumptions.prop81_of_assumptions P h82 hi h83 h84 𝔼 t0,
    fun H => (prop83M H hA h83 h87 hcirc).1⟩

/-- **Woodford (2003), Proposition 8.4, p. 558, for every representation of the corrected
Proposition 8.1.** Under Assumptions 8.1, 8.3 and 8.7, with no root of (1.15) on `|λ| = β⁻¹`:
`α(L) = α₁(L)α₂(L)` with `deg α₁ = m`, the zeros of `α₁` inside and those of `α₂` outside the
unit circle; for every bounded adapted `w` the bounded forward inverse `g = α̃₁(L⁻¹)⁻¹ w` exists
and is unique; and for bounded adapted instrument paths (1.28) holds at all dates `t ≥ T` iff
(1.32) does. -/
theorem prop84M [Nonempty Ω] {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (H : Prop81ConclusionM P 𝔼 t0) (hA : Assumption81 P 𝔼 t0)
    (h83 : PencilEigen.Assumption83 P.sys) {m : ℕ}
    (h87 : P.sys.stableCount P.β⁻¹ = Fintype.card ιZ + m)
    (hcirc : ∀ l ∈ P.sys.pencilPoly.roots, ‖l‖ ≠ P.β⁻¹) :
    ∃ α1 α2 : ℝ[X], alpha H.Λ = α1 * α2 ∧ α1.natDegree = m ∧
      (∀ z ∈ (α1.map Complex.ofRealHom).roots, ‖z‖ < 1) ∧
      (∀ z ∈ (α2.map Complex.ofRealHom).roots, 1 < ‖z‖) ∧
      ∀ (lam istar : ℝ) (i w : ℕ → Ω → ℝ), BoundedProc i → 𝔼.Adapted i → BoundedProc w →
        𝔼.Adapted w →
        (∃! g, BoundedProc g ∧ 𝔼.Adapted g ∧ (aeval (fwdOp 𝔼) α1.reverse) g = w) ∧
        ∀ g, BoundedProc g → 𝔼.Adapted g → (aeval (fwdOp 𝔼) α1.reverse) g = w → ∀ T,
          ((∀ t, T ≤ t → (lam • (aeval (lagOp (Ω := Ω)) (alpha H.Λ))
              (fun t ω => i t ω - istar) + w) t = 0) ↔
            (∀ t, T ≤ t → (g + lam • ((lagOp (Ω := Ω)) ^ m)
              ((aeval (lagOp (Ω := Ω)) α2) (fun t ω => i t ω - istar))) t = 0)) := by
  obtain ⟨hm, hc⟩ := prop83M H hA h83 h87 hcirc
  obtain ⟨α1, α2, hfac, hmon, hroots1, hdeg, hroots2⟩ :=
    Prop84General.exists_inside_factorization (alpha H.Λ) (alpha_ne_zero _)
  have hin : ∀ z ∈ (α1.map Complex.ofRealHom).roots, ‖z‖ < 1 := by
    intro z hz
    rw [hroots1] at hz
    exact (Multiset.mem_filter.mp hz).2
  have hrev : ∀ z ∈ (α1.reverse.map Complex.ofRealHom).roots, 1 < ‖z‖ := by
    rw [map_reverse_ofReal]
    exact roots_reverse_outside hin
  have hrev0 : α1.reverse ≠ 0 := fun h => hmon.ne_zero (reverse_eq_zero.mp h)
  refine ⟨α1, α2, hfac, hdeg.trans hm, hin,
    Prop84General.roots_cofactor_outside (alpha_ne_zero _) hfac hroots2 hc,
    fun lam istar i w hib hia hwb hwa => ⟨?_, fun g hgb hga hg T => ?_⟩⟩
  · exact Prop84General.forward_inverse_existsUnique hrev0 hrev hwb hwa
  · rw [hfac]
    exact Prop84General.prop84_from (hdeg.trans hm) hmon.ne_zero hrev hib hia hgb hga hg T

end Woodford.OptimalPolicyRules.Prop83Links
