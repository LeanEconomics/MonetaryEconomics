/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR5bReRepUncertain

/-!
# The p. 553 criterion without its two side hypotheses

Woodford (2003), *Interest and Prices*, Chapter 8, Proposition 8.1 and the remark after it
(p. 553), that `Λ` and `Υ` are "uniquely defined".

`TidyR5bReRepUncertain.unique_iff_powBdd_any` proves, for every exact expectation system, that
`Λ` and `Υ` are the same in every representation of Proposition 8.1 iff `Λ` is power-bounded,
under two hypotheses: a **nonempty** sample space and **one bounded solution of (1.18)**.

* `exists_xproc_zero`: there is always a constant plan with `T̃'W(τ − τ*) = 0` (the target
  vector `T̃'Wτ*` lies in the range of `T̃'WT̃`, since `W` is positive definite); with zero
  multipliers it solves (1.18) (`exists_base`). **The second hypothesis always holds and is
  dropped**: `unique_iff_powBdd_uncond`.
* `anyRep`, `nonempty_needed`: on an **empty** sample space every pair `(Λ, Υ)` is a
  representation, so the criterion fails as soon as there is a multiplier (`ιz` nonempty):
  **the first hypothesis is needed** (and cannot be removed).
-/

namespace Woodford.OptimalPolicyRules.TidyR6aReRepBase

open Matrix GeneralSetup Prop81General TargetCriterion.Prop81 GeneralFOC GeneralFOC.LQ
open TidyR5bReRepConverse TidyR5bReRepUncertain TidyR5bFOCNecessity

variable {Ω : Type*} {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

omit [DecidableEq ιZ] in
/-- Woodford (2003), (1.3) and (1.18) (**a rest point of the target term**): for every LQ problem
there is a plan vector `v` with `T̃'W(Tv − τ*) = 0` — it is `(u, i = 0)` with
`T̃'WT̃ u = T̃'Wτ*`, solvable because `T̃'Wτ*` is orthogonal to `ker T̃'WT̃ = ker T̃`. -/
theorem exists_xproc_zero (P : LQProblem ιZ ιz ιτ) :
    ∃ v : (ιZ ⊕ ιz) ⊕ Unit → ℝ, P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar)) = 0 := by
  classical
  set L := P.Ttilᵀ * P.W * P.Ttil with hL
  have hW : P.Wᵀ = P.W := by
    have := P.W_posDef.isHermitian.eq
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hLt : Lᵀ = L := by
    rw [hL, transpose_mul, transpose_mul, transpose_transpose, hW, Matrix.mul_assoc]
  have hd : P.Ttilᵀ *ᵥ (P.W *ᵥ P.τstar) ∈ LinearMap.range L.mulVecLin := by
    refine mem_range_of_orth L _ fun w hw => ?_
    rw [hLt] at hw
    have h0 : P.Ttil *ᵥ w = 0 := by
      by_contra hne
      have hpos := P.W_posDef.dotProduct_mulVec_pos hne
      have e : star (P.Ttil *ᵥ w) ⬝ᵥ (P.W *ᵥ (P.Ttil *ᵥ w)) = w ⬝ᵥ (L *ᵥ w) := by
        rw [star_trivial, hL, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec w P.Ttilᵀ,
          vecMul_transpose]
      rw [e, hw, dotProduct_zero] at hpos
      exact lt_irrefl _ hpos
    rw [dotProduct_mulVec, vecMul_transpose, h0, zero_dotProduct]
  obtain ⟨u, hu⟩ := hd
  refine ⟨Sum.elim u 0, ?_⟩
  have hT : P.T *ᵥ Sum.elim u 0 = P.Ttil *ᵥ u := by
    rw [LQProblem.T, fromCols_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_zero,
      add_zero]
  have hLu : P.Ttilᵀ *ᵥ (P.W *ᵥ (P.Ttil *ᵥ u)) = P.Ttilᵀ *ᵥ (P.W *ᵥ P.τstar) := by
    rw [mulVec_mulVec, mulVec_mulVec]
    exact hu
  rw [hT, mulVec_sub, mulVec_sub, hLu, sub_self]

/-- Woodford (2003), (1.18), p. 552 (**a bounded solution of (1.18) always exists**): the
constant plan of `exists_xproc_zero` with zero multipliers, under any expectation system. -/
theorem exists_base (P : LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    ∃ (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ), BoundedV y ∧
      AdaptedV 𝔼 y ∧ BoundedV φ ∧ MultKnown 𝔼 t0 φ ∧ Eq118 P 𝔼 t0 y φ := by
  obtain ⟨v, hv⟩ := exists_xproc_zero P
  refine ⟨fun _ _ => v, fun _ _ => 0, ?_, fun t i => 𝔼.const t _,
    ⟨0, fun _ _ _ => by simp⟩, fun t _ i => 𝔼.const t 0, fun t _ ω => ?_⟩
  · refine ⟨∑ i, |v i|, fun t ω i => ?_⟩
    exact Finset.single_le_sum (f := fun i => |v i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)
  · have e : EV 𝔼 t (fun _ => (0 : ιZ ⊕ ιz → ℝ)) ω = 0 := by
      funext i
      exact congrFun (𝔼.const t 0) ω
    simp only [e, mulVec_zero, zero_add, smul_zero, sub_zero]
    exact hv

/-- Woodford (2003), p. 553, the remark after Proposition 8.1 (**exact criterion, no solvability
hypothesis**): under any expectation system on a nonempty sample space, `Λ` and `Υ` are the same
in every representation of Proposition 8.1 iff `Λ` is power-bounded. -/
theorem unique_iff_powBdd_uncond [Nonempty Ω] {𝔼 : ExpectationSystem Ω}
    {P : LQProblem ιZ ιz ιτ} {t0 : ℕ} (H : Prop81ConclusionM P 𝔼 t0) :
    (∀ H' : Prop81ConclusionM P 𝔼 t0, H'.Λ = H.Λ ∧ H'.Υ = H.Υ) ↔ PowBdd H.Λ := by
  obtain ⟨y, φ, hy, hya, hφ, hφk, h118⟩ := exists_base P 𝔼 t0
  exact unique_iff_powBdd_any H hy hya hφ hφk h118

/-- Woodford (2003), Proposition 8.1 (degenerate case): on an empty sample space every pair
`(Λ, Υ)` gives a representation (all conditions are vacuous). -/
def anyRep [IsEmpty Ω] (P : LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    (Λ : Matrix ιz ιz ℝ) (Υ : Matrix ιZ ιz ℝ) : Prop81ConclusionM P 𝔼 t0 where
  Λ := Λ
  Υ := Υ
  Qop := fun _ _ ω => isEmptyElim ω
  Rop := fun _ _ ω => isEmptyElim ω
  equiv := fun _ _ _ _ _ _ =>
    ⟨fun _ => ⟨fun _ _ ω => isEmptyElim ω, fun _ _ ω => isEmptyElim ω⟩,
      fun _ _ _ ω => isEmptyElim ω⟩
  Qbounded := fun _ _ => ⟨0, fun _ ω => isEmptyElim ω⟩
  Rbounded := fun _ _ => ⟨0, fun _ ω => isEmptyElim ω⟩
  Qadapted := fun _ _ _ => funext fun ω => isEmptyElim ω
  Radapted := fun _ _ _ _ => funext fun ω => isEmptyElim ω

/-- **Woodford (2003), p. 553 (the nonempty sample space cannot be dropped)**: on an empty sample
space, with at least one multiplier, there is a representation with a power-bounded `Λ`
(`Λ = 0`) that is not the only one (`Λ = 1` is another). -/
theorem nonempty_needed [IsEmpty Ω] [Nonempty ιz] (P : LQProblem ιZ ιz ιτ)
    (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    ∃ H : Prop81ConclusionM P 𝔼 t0, PowBdd H.Λ ∧
      ¬ ∀ H' : Prop81ConclusionM P 𝔼 t0, H'.Λ = H.Λ ∧ H'.Υ = H.Υ := by
  refine ⟨anyRep P 𝔼 t0 0 0, ⟨1, fun k i j => ?_⟩, fun h => ?_⟩
  · change |((0 : Matrix ιz ιz ℝ) ^ k) i j| ≤ 1
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [pow_zero, one_apply]
      split_ifs <;> simp
    · rw [zero_pow hk.ne']
      simp
  · obtain ⟨i⟩ := ‹Nonempty ιz›
    have := congrFun (congrFun (h (anyRep P 𝔼 t0 1 0)).1 i) i
    change (1 : Matrix ιz ιz ℝ) i i = (0 : Matrix ιz ιz ℝ) i i at this
    simp at this

end Woodford.OptimalPolicyRules.TidyR6aReRepBase
