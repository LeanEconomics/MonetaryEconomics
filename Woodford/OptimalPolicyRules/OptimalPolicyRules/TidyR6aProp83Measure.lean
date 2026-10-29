/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR6aProp81Measure
import OptimalPolicyRules.TidyR5bProp83Circle
import OptimalPolicyRules.OptimalRulesMeasureSpectrum
import OptimalPolicyRules.ExpectationsMeasureIID

/-!
# The Proposition 8.3 counterexample on a genuine probability space

Woodford (2003), *Interest and Prices*, Chapter 8, Proposition 8.3 (pp. 556–557), Assumption 8.1
(p. 541), Assumptions 8.3 (App. G.1, p. 716) and 8.7 (p. 556).

`TidyR5bProp83Circle.prop83_fails_on_circle` refutes Proposition 8.3 for `p83Problem`
(`n_Z = 0`, `n_z = 2`, `β = ½`, roots `½` and `2 = β⁻¹` of (1.15)) under the **perfect-foresight**
Assumption 8.1. Here the counterexample is carried to **every** filtered probability space with
Mathlib's conditional expectation, in particular the i.i.d. coin-flip economy:

* `p83_noEulerRoot`: the Euler pencil of (1.1) + (1.9) has no root on the unit circle (its
  nonzero roots solve `ν = ½`, `ν = 4` or `2ν² − 7ν + 4 = 0`, all real and off the circle).
  Hence (`OptimalRulesMeasureSpectrum.m_assumption81MB_of_noEulerRoot`) **the full
  Assumption 8.1 holds on every probability space** (`m_p83_assumption81MB`; also the form with a
  predetermined initial multiplier, `m_p83_assumption81M`, and the book's own form whenever
  date-0 information is essentially bounded, `m_p83_assumption81`).
* `mp83Rep`: the representation of Proposition 8.1 on the probability space built from the empty
  deflating split (`TidyR6aProp81Measure.mprop81`), `Λ = diag(4, 1)`; its `α(L)` has the one zero
  `1/4` inside the unit circle (`mp83Rep_zeros`).
* `mp83Rep'`: a second representation on the same probability space with the Jordan block
  `Λ' = [[1, 0], [1, 1]]` (`TidyR6aReRepMeasure.mreRep`); `α(L) = (1 − L)²` has **no** zero inside
  the unit circle although `m = 1`.
* **`m_prop83_fails_on_circle`**: on every probability space, the full Assumption 8.1,
  Assumption 8.3 and Assumption 8.7 (`m = 1`) hold, a root lies on `|μ| = β⁻¹`, and the claim of
  Proposition 8.3 fails for the representation `mp83Rep'`; `m_prop83_fails_iid`: the same on the
  i.i.d. fair-coin economy (module ExpectationsMeasureIID).
-/

namespace Woodford.OptimalPolicyRules.TidyR6aProp83Measure

open MeasureTheory Filter Matrix Polynomial GeneralSetup GeneralFOC GeneralFOC.LQ PencilSplit
open PencilEigen Prop81General TargetCriterion.Prop81 TidyR5bReRep TidyR5bProp83Circle Adjugate
open ExpectationsMeasure OptimalRulesMeasure OptimalRulesMeasureSpectrum TidyR6aReRepMeasure
open TidyR6aProp81Measure

/-! ### No root of the Euler pencil on the unit circle -/

/-- Woodford (2003), (1.15) (tool): the quadratic `2ν² − 7ν + 4` (the second workhorse equation of
`p83Problem`) has no root on the unit circle. -/
theorem quad_ne_zero {ν : ℂ} (hν : ‖ν‖ = 1) : 2 * ν ^ 2 - 7 * ν + 4 ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, pow_two, Complex.re_ofNat,
    Complex.im_ofNat, Complex.zero_re, Complex.sub_im, Complex.add_im, Complex.mul_im,
    Complex.zero_im] at hre him
  have hn : ν.re ^ 2 + ν.im ^ 2 = 1 := by
    have := Complex.sq_norm ν
    rw [hν, Complex.normSq_apply] at this
    nlinarith
  have hb : ν.im = 0 := by
    have h1 : ν.im * (4 * ν.re - 7) = 0 := by linarith
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · nlinarith
  rw [hb] at hre hn
  nlinarith

/-- Woodford (2003), (1.3) and (1.9) for `p83Problem` (tool): `T'WT = I` (targets `(z₁, z₂, i)`,
`W = I`), over `ℂ`. -/
theorem p83_TWT (u : (Empty ⊕ Fin 2) ⊕ Unit → ℂ) :
    p83Problem.Tᵀ.map Complex.ofReal *ᵥ (p83Problem.W.map Complex.ofReal *ᵥ
      (p83Problem.T.map Complex.ofReal *ᵥ u)) = u := by
  have hW : p83Problem.W.map Complex.ofReal = 1 := by
    simp [p83Problem]
  rw [hW, one_mulVec, mulVec_mulVec]
  funext a
  rcases a with (e | j) | k
  · exact e.elim
  · fin_cases j <;> simp [p83Problem, LQProblem.T, mulVec, dotProduct, mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_three, Fin.sum_univ_two]
  · simp [p83Problem, LQProblem.T, mulVec, dotProduct, mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_three, Fin.sum_univ_two]

/-- **Woodford (2003), (1.1) + (1.9) for `p83Problem`: the Euler pencil has no root on the unit
circle.** An eigen-solution `νᵗ(u, p)` with `|ν| = 1` has `z₁ = 0` (`ν ≠ ½`), `M₁ = 0`
(`ν ≠ 4`) and `(2ν² − 7ν + 4)M₂ = 0`, hence `M₂ = 0`, `z₂ = 0`, `i = 0`. -/
theorem p83_noEulerRoot : ∀ ν : ℂ, ‖ν‖ = 1 → ¬ EulerRoot p83Problem ν := by
  rintro ν hν ⟨u, p, hne, h1, h2⟩
  rw [p83_TWT] at h2
  have a1 : ν = 2⁻¹ ∨ u (Sum.inl (Sum.inr 0)) = 0 := by
    have := congrFun h1 (Sum.inr 0)
    simpa [p83Problem, p83Sys, LinearRESystem.Atil, LinearRESystem.Itil,
      LinearRESystem.Ahat, LinearRESystem.Ihat, LinearRESystem.Bvec, mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two] using this
  have a2 : ν * u (Sum.inl (Sum.inr 1)) = 2 * u (Sum.inl (Sum.inr 1)) + u (Sum.inr ()) := by
    have := congrFun h1 (Sum.inr 1)
    simpa [p83Problem, p83Sys, LinearRESystem.Atil, LinearRESystem.Itil,
      LinearRESystem.Ahat, LinearRESystem.Ihat, LinearRESystem.Bvec, mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two] using this
  have b1 : ν * (2⁻¹ * p (Sum.inr 0)) + u (Sum.inl (Sum.inr 0)) - 2 * p (Sum.inr 0) = 0 := by
    have := congrFun h2 (Sum.inl (Sum.inr 0))
    simpa [p83Problem, p83Sys, LinearRESystem.Atil, LinearRESystem.Itil,
      LinearRESystem.Ahat, LinearRESystem.Ihat, LinearRESystem.Bvec, mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two] using this
  have b2 : ν * (2 * p (Sum.inr 1)) + u (Sum.inl (Sum.inr 1)) - 2 * p (Sum.inr 1) = 0 := by
    have := congrFun h2 (Sum.inl (Sum.inr 1))
    simpa [p83Problem, p83Sys, LinearRESystem.Atil, LinearRESystem.Itil,
      LinearRESystem.Ahat, LinearRESystem.Ihat, LinearRESystem.Bvec, mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two] using this
  have b3 : ν * p (Sum.inr 1) + u (Sum.inr ()) = 0 := by
    have := congrFun h2 (Sum.inr ())
    simpa [p83Problem, p83Sys, LinearRESystem.Atil, LinearRESystem.Itil,
      LinearRESystem.Ahat, LinearRESystem.Ihat, LinearRESystem.Bvec, mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two] using this
  have hhalf : ν ≠ 2⁻¹ := fun h => by
    rw [h] at hν
    norm_num at hν
  have hfour : ν ≠ 4 := fun h => by
    rw [h] at hν
    norm_num at hν
  have hz1 : u (Sum.inl (Sum.inr 0)) = 0 := a1.resolve_left hhalf
  have hM1 : p (Sum.inr 0) = 0 := by
    have : (ν - 4) * p (Sum.inr 0) = 0 := by linear_combination 2 * b1 - 2 * hz1
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hfour)
  have hM2 : p (Sum.inr 1) = 0 := by
    have : (2 * ν ^ 2 - 7 * ν + 4) * p (Sum.inr 1) = 0 := by
      linear_combination (ν - 2) * b2 - a2 - b3
    exact (mul_eq_zero.mp this).resolve_left (quad_ne_zero hν)
  have hi : u (Sum.inr ()) = 0 := by linear_combination b3 - ν * hM2
  have hz2 : u (Sum.inl (Sum.inr 1)) = 0 := by linear_combination b2 - (2 * ν - 2) * hM2
  rcases hne with h | h
  · apply h
    funext a
    rcases a with (e | j) | k
    · exact e.elim
    · fin_cases j
      · exact hz1
      · exact hz2
    · exact hi
  · apply h
    funext a
    rcases a with e | j
    · exact e.elim
    · fin_cases j
      · exact hM1
      · exact hM2

/-! ### The full Assumption 8.1 on every probability space -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Woodford (2003), Assumption 8.1, p. 541, for `p83Problem` on every filtered probability
space** (bounded initial multiplier known at `t₀ − 1`, the corrected full form): existence and
a.s. uniqueness of bounded solutions of (1.1) + (1.9) for every bounded adapted disturbance. -/
theorem m_p83_assumption81MB (S : MeasExpectationSystem Ω) (t0 : ℕ) :
    MAssumption81MB S p83Problem t0 :=
  m_assumption81MB_of_noEulerRoot p83_assumption81 p83_noEulerRoot S t0

/-- Woodford (2003), Assumption 8.1, p. 541, for `p83Problem` on every probability space, in the
form `OptimalRulesMeasure.MAssumption81M` (no predetermined variable, so no bound on `Z_{t₀}` is
needed). -/
theorem m_p83_assumption81M (S : MeasExpectationSystem Ω) (t0 : ℕ) :
    MAssumption81M S p83Problem t0 :=
  (assumption81M_iff (S := S) (P := p83Problem) (t0 := t0)).mpr
    ⟨m_p83_assumption81MB S t0, fun h => isEmptyElim (Classical.choice h)⟩

/-- Woodford (2003), **Assumption 8.1, p. 541, in the book's own form**, for `p83Problem` at
`t₀ = 0` on every probability space whose date-0 information is essentially bounded
(`OptimalRulesMeasure.BddInfo`; e.g. a trivial `𝓕₀`). -/
theorem m_p83_assumption81 (S : MeasExpectationSystem Ω) (hb : BddInfo S 0) :
    MAssumption81 S p83Problem 0 :=
  (assumption81_iff (S := S) (P := p83Problem) (t0 := 0)).mpr
    ⟨m_p83_assumption81MB S 0, hb, fun _ hf => hf.aestronglyMeasurable⟩

/-! ### Two representations of Proposition 8.1 on the probability space -/

/-- Woodford (2003), Proposition 8.1 for `p83Problem` on a probability space: the representation
from the empty split, `Λ = β⁻¹(A₂₂')⁻¹ = diag(4, 1)`. -/
noncomputable def mp83Rep (S : MeasExpectationSystem Ω) : MProp81Conclusion S p83Problem 0 :=
  mprop81 p83Problem (emptySplit' p83Sys (1 / 2)) S 0

/-- Woodford (2003), (1.20) for `p83Problem` on a probability space: `Λ = diag(4, 1)`. -/
theorem mp83Rep_Λ (S : MeasExpectationSystem Ω) : (mp83Rep S).Λ = !![4, 0; 0, 1] :=
  p83Rep_Λ

/-- Woodford (2003), (1.22): for the natural representation `α(L) = (1 − 4L)(1 − L)` has exactly
one zero inside the unit circle. -/
theorem mp83Rep_zeros (S : MeasExpectationSystem Ω) :
    TargetCriterion.zerosInside (alpha (mp83Rep S).Λ) = 1 := by
  rw [mp83Rep_Λ, ← p83Rep_Λ]
  exact natural_zerosInside

/-- Woodford (2003), (1.20) (tool): on a probability space, `M_{t+1} = Λ' M_t + (1, 0)` with the
Jordan block `Λ' = [[1, 0], [1, 1]]` has no essentially bounded solution. -/
theorem jordan_noRecSol (S : MeasExpectationSystem Ω) (D : ℕ → Ω → Fin 2 → ℝ) :
    ¬ RecSolMm S 0 (jΛ 1) (fun _ _ => ![1, 0]) D := by
  rintro ⟨hb, -, -, hr⟩
  obtain ⟨ω, h1, h2⟩ := ((ae_bddS hb).and (ae_forall_ge hr)).exists
  exact jΛ_blowUp 1 0 (fun t => D t ω) h1 fun t ht => h2 t ht

/-- **Woodford (2003), Proposition 8.1 for `p83Problem` on a probability space: the second
representation**, with the Jordan block `Λ' = [[1, 0], [1, 1]]` (`mreRep`): `diag(4, 1)` and `Λ'`
have the same bounded homogeneous solutions, and the forcing `(1, 0)` makes the `Λ'` recursion
explode. -/
noncomputable def mp83Rep' (S : MeasExpectationSystem Ω) : MProp81Conclusion S p83Problem 0 :=
  mreRep (mp83Rep S) (jΛ 1)
    (by
      rw [mp83Rep_Λ]
      intro D hD
      rw [diag_hom (by norm_num) 0 hD, jΛ_hom one_ne_zero 0 hD])
    (fun _ _ _ => ![1, 0]) (fun _ _ _ => stronglyMeasurable_const)
    (fun _ _ => ⟨1, fun _ => Eventually.of_forall fun _ i => by fin_cases i <;> simp⟩)
    (fun _ _ _ D => jordan_noRecSol S D)

/-- **Woodford (2003), Proposition 8.3, pp. 556–557 — the counterexample on every probability
space.** For `p83Problem` on any filtered probability space: the full Assumption 8.1 holds
(`MAssumption81MB`), Assumption 8.3 holds, Assumption 8.7 holds with `m = 1`, the root `2` of
(1.15) lies on `|μ| = β⁻¹`, the natural representation has `m = 1` zero of `α(L)` inside the unit
circle, but the representation `mp83Rep'` has `α(L) = (1 − L)²` with **none**: the claim of
Proposition 8.3 fails under the full Assumption 8.1 with genuine conditional expectations. -/
theorem m_prop83_fails_on_circle (S : MeasExpectationSystem Ω) :
    MAssumption81MB S p83Problem 0 ∧ Nonempty (Assumption83 p83Sys) ∧
      p83Sys.stableCount (1 / 2 : ℝ)⁻¹ = Fintype.card Empty + 1 ∧
      (∃ l ∈ p83Sys.pencilPoly.roots, ‖l‖ = (1 / 2 : ℝ)⁻¹) ∧
      TargetCriterion.zerosInside (alpha (mp83Rep S).Λ) = 1 ∧
      TargetCriterion.zerosInside (alpha (mp83Rep' S).Λ) = 0 := by
  obtain ⟨hc, hr, hn⟩ := p83_stableCount
  refine ⟨m_p83_assumption81MB S 0, p83_assumption83, hc, ⟨2, hr, hn⟩, mp83Rep_zeros S, ?_⟩
  change TargetCriterion.zerosInside (alpha (jΛ 1)) = 0
  exact Prop83.jordanΛ_zeros.1

/-- Woodford (2003), Proposition 8.3: the counterexample on the **i.i.d. fair-coin economy**
(`ExpectationsMeasureIID.iidSystem` with `ExpectationsMeasureIID.coin`, a genuine
infinite-horizon probability space with news at every date). -/
theorem m_prop83_fails_iid :
    MAssumption81MB (ExpectationsMeasureIID.iidSystem ExpectationsMeasureIID.coin) p83Problem 0 ∧
      TargetCriterion.zerosInside
        (alpha (mp83Rep' (ExpectationsMeasureIID.iidSystem ExpectationsMeasureIID.coin)).Λ) = 0 ∧
      p83Sys.stableCount (1 / 2 : ℝ)⁻¹ = Fintype.card Empty + 1 := by
  have h := m_prop83_fails_on_circle (ExpectationsMeasureIID.iidSystem ExpectationsMeasureIID.coin)
  exact ⟨h.1, h.2.2.2.2.2, h.2.2.1⟩

end Woodford.OptimalPolicyRules.TidyR6aProp83Measure
