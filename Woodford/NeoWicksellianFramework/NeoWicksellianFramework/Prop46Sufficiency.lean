/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.GeneralBKLinks
import NeoWicksellianFramework.Determinacy2Forward

/-!
# Proposition 4.6: sufficiency, and the corrected equivalence

Woodford (2003), *Interest and Prices*, Chapter 4, §2.2, pp. 258–260, and Appendix C.5, p. 682.
The book proves only that (2.9) and (2.13) are *necessary* for determinacy under the inertial
forward-looking rule (2.12) (`ThreeByThree.prop46_necessity`), and writes of sufficiency "I omit
analysis" (p. 682), reporting only that the conditions suffice in the numerical case of
Fig. 4.2. Here sufficiency is settled.

## Verdict

Under the book's sign restrictions (`ρ, φ_π, φ_x ≥ 0`, with `0 < β < 1`, `κ, σ > 0`; no upper
bound on `ρ`), (2.9) and (2.13) are sufficient **as soon as the rule responds to inflation or the
output gap**; with `φ_π = φ_x = 0` and `ρ > 1` both conditions hold but equilibrium is not
determinate (`prop46_printed_false`, the same degenerate case as Prop. 4.4). So:
`prop46`: determinate ⟺ (2.9) ∧ (2.13) ∧ (`φ_π > 0 ∨ φ_x > 0`).

## The argument

* (2.9) is `P(1) > 0` and (2.13) is `P(−1) < 0` (`ThreeByThree.P1_A46`, `Pm1_A46`), so a real
  root `μ ∈ (−1, 1)` exists and `P(λ) = (λ − μ)(λ² − Tλ + D)` with `|T| < 1 + D`.
* The exact identity `C15_A46`:
  `β²(A₀² − A₀A₂ + A₁ − 1) = (1 − β)(1 − ρ)(β − ρ) + (β − ρ)σ(φ_x/4 + ρκ) + ρσκ·g`,
  `g = φ_π + (1 − β)φ_x/(4κ) − (1 − ρ)` the (2.9) gap. If `ρ < β`, (2.9) gives (C.15), so Case II
  of Prop. C.2 holds (`caseII_A46`); then `D > 1`.
* If `ρ ≥ β`, `|A₀| = ρ/β ≥ 1` and `|μ| |D| = |A₀|` force `|D| > 1` (`oneInTwoOut_of_abs_A0`, a
  sufficient condition not in the book's list). Case II can genuinely fail there
  (`caseII_not_necessary_46`: `β = 1/2, κ = σ = 1, ρ = 2, φ_π = 0, φ_x = 4` has (C.15) violated),
  and then Case III′ (`|A₂| > 3`) holds instead (`cases_A46`).
* Genericity (`generic_A46`): a stable eigenvector with zero lagged-rate component is a stable
  eigenvector `(β⁻¹κ, β⁻¹ − μ)` of the exogenous-rate matrix of Prop. 4.2, so `0 < μ < 1`, and the
  rule's row forces `4β⁻¹κφ_πμ + φ_x(β⁻¹ − μ) = 0`, impossible if `φ_π > 0` or `φ_x > 0`.
* Then the Blanchard–Kahn theorem (`BlanchardKahn.determinate3_of`) gives determinacy for the
  model's IS disturbance (`prop46_sufficiency`) and, through the general theorem of
  `GeneralBKLinks`, for **every** bounded adapted forcing vector (`prop46_determinate3`,
  `prop46_determinate3_iff`). Boundary cases `P(±1) = 0` are excluded by resonance
  (`ThreeByThree.prop46_necessity`), so the equivalence is exact, with strict inequalities.

## p. 260: the later-period Clarida–Galí–Gertler rule

The book's claim that `ρ = 0.79, φ_π = 0.45, φ_x = 0.20` "implies a determinate equilibrium" rests
on the sufficiency the book did not prove; it is now a theorem for every admissible `β, κ, σ`
(`clarida_later_determinate`, `clarida_later_determinate3`; also under the contemporaneous rule
(2.8), `clarida_later_determinate44`).
-/

namespace Woodford.NeoWicksellianFramework.Prop46Sufficiency

open SchurCohn BlanchardKahn ThreeByThree GeneralBKLinks
open scoped Matrix

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Coefficients and Prop. C.2 -/

/-- Woodford (2003), App. C.5, p. 682 ((C.15) for the rule (2.12), not computed in the book):
`β²(A₀² − A₀A₂ + A₁ − 1) = (1 − β)(1 − ρ)(β − ρ) + (β − ρ)σ(φ_x/4 + ρκ) + ρσκ·g` with
`g = φ_π + (1 − β)φ_x/(4κ) − (1 − ρ)` the gap in (2.9). -/
theorem C15_A46 {β κ σ ρ φπ φx : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0) :
    C15 (ch2 (A46 β κ σ ρ φπ φx)) (ch1 (A46 β κ σ ρ φπ φx)) (ch0 (A46 β κ σ ρ φπ φx)) =
      ((1 - β) * (1 - ρ) * (β - ρ) + (β - ρ) * σ * (φx / 4 + ρ * κ) +
        ρ * σ * κ * (φπ + (1 - β) / (4 * κ) * φx - (1 - ρ))) / β ^ 2 := by
  rw [C15, ch2_A46, ch1_A46, ch0_A46]
  field_simp
  ring

/-- Woodford (2003), App. C.5, p. 682: for `ρ < β`, the Taylor principle (2.9) implies (C.15). -/
theorem C15_A46_pos {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφx : 0 ≤ φx) (hρβ : ρ < β)
    (h29 : 1 - ρ < φπ + (1 - β) / (4 * κ) * φx) :
    0 < C15 (ch2 (A46 β κ σ ρ φπ φx)) (ch1 (A46 β κ σ ρ φπ φx)) (ch0 (A46 β κ σ ρ φπ φx)) := by
  rw [C15_A46 hβ0.ne' hκ.ne']
  have t1 : 0 < (1 - β) * (1 - ρ) * (β - ρ) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have t2 : 0 ≤ (β - ρ) * σ * (φx / 4 + ρ * κ) := by
    have : 0 ≤ φx / 4 + ρ * κ := by positivity
    exact mul_nonneg (mul_nonneg (by linarith) hσ.le) this
  have t3 : 0 ≤ ρ * σ * κ * (φπ + (1 - β) / (4 * κ) * φx - (1 - ρ)) :=
    mul_nonneg (by positivity) (by linarith)
  positivity

/-- Woodford (2003), App. C.5, p. 682: for `ρ < β`, (2.9) and (2.13) give Case II of
Prop. C.2, (C.13)–(C.15) (the book's "(A.3)–(A.5)", survey E27). -/
theorem caseII_A46 {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφx : 0 ≤ φx) (hρβ : ρ < β)
    (h29 : 1 - ρ < φπ + (1 - β) / (4 * κ) * φx)
    (h213 : φπ < 1 + ρ + (1 + β) / (4 * κ) * (φx + 8 / σ * (1 + ρ))) :
    CaseII3 (ch2 (A46 β κ σ ρ φπ φx)) (ch1 (A46 β κ σ ρ φπ φx)) (ch0 (A46 β κ σ ρ φπ φx)) := by
  refine ⟨?_, ?_, C15_A46_pos hβ0 hβ1 hκ hσ hρ hφx hρβ h29⟩
  · rw [P1_A46 hβ0.ne' hκ.ne']
    exact mul_pos (by positivity) (by linarith)
  · rw [Pm1_A46 hβ0.ne' hκ.ne' hσ.ne']
    exact mul_neg_of_pos_of_neg (by positivity) (by linarith)

/-- Woodford (2003), Prop. C.2, p. 673 (a sufficient condition not in the book's list): if
`P(1) > 0`, `P(−1) < 0` and either (C.15) holds or `|A₀| ≥ 1`, the cubic has exactly one root in
the open unit disc and two outside the closed disc. With `|A₀| ≥ 1` the product of the two outer
roots is `|A₀|/|μ| > 1`. -/
theorem oneInTwoOut_of_abs_A0 {a2 a1 a0 : ℝ} (h1 : 0 < P1 a2 a1 a0) (h2 : Pm1 a2 a1 a0 < 0)
    (h : 0 < C15 a2 a1 a0 ∨ 1 ≤ |a0|) : OneInTwoOut a2 a1 a0 := by
  have hcont : ContinuousOn (cubicR a2 a1 a0) (Set.Icc (-1) 1) := by
    unfold cubicR; fun_prop
  rw [P1_eq] at h1
  rw [Pm1_eq] at h2
  obtain ⟨μ, hμI, hμ⟩ := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1) hcont
    ⟨h2.le, h1.le⟩
  have hμ1 : μ ≠ 1 := by rintro rfl; linarith
  have hμm1 : μ ≠ -1 := by rintro rfl; linarith
  have hμa : |μ| < 1 := abs_lt.mpr ⟨lt_of_le_of_ne hμI.1 (Ne.symm hμm1),
    lt_of_le_of_ne hμI.2 hμ1⟩
  obtain ⟨T, D, hs⟩ : ∃ T D : ℝ, RealSplit a2 a1 a0 μ T D := ⟨_, _, realSplit_of_root hμ⟩
  have hP := P1_of_realSplit hs
  have hM := Pm1_of_realSplit hs
  rw [P1_eq] at hP
  rw [Pm1_eq] at hM
  obtain ⟨hl, hr⟩ := abs_lt.mp hμa
  have e1 : 0 < 1 - T + D := by
    by_contra hc; push Not at hc
    have : (1 - μ) * (1 - T + D) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hc
    linarith
  have e2 : 0 < 1 + T + D := by
    by_contra hc; push Not at hc
    have : (1 + μ) * (1 + T + D) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hc
    linarith
  have hT : |T| < 1 + D := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hD : 1 < |D| := by
    rcases h with hc | ha
    · have hD1 : 1 < D := by
        by_contra hc'; push Not at hc'
        have hk := key_pos hμa hc' hT
        rw [C15_eq_of_realSplit hs] at hc
        have : (D * μ ^ 2 - T * μ + 1) * (D - 1) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hk.le (by linarith)
        linarith
      exact lt_of_lt_of_le hD1 (le_abs_self D)
    · by_contra hc'; push Not at hc'
      have e : |a0| = |μ| * |D| := by rw [hs.2.2, abs_neg, abs_mul]
      have : |μ| * |D| < 1 := by
        calc |μ| * |D| ≤ |μ| * 1 := mul_le_mul_of_nonneg_left hc' (abs_nonneg μ)
          _ < 1 := by linarith
      linarith
  refine (oneInTwoOut_iff_real _ _ _).mpr ⟨μ, T, D, hμa, ?_, hs⟩
  exact (bothOutside_iff_abs T D).mpr ⟨hD, by rwa [abs_of_pos (by linarith : (0 : ℝ) < 1 + D)]⟩

/-- Woodford (2003), Prop. 4.6, App. C.5, p. 682 (the analysis the book omits): under the sign
restrictions, (2.9) and (2.13) imply that `A` has exactly one eigenvalue inside and two outside
the unit circle. -/
theorem oneInTwoOut_A46 {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφx : 0 ≤ φx)
    (h29 : 1 - ρ < φπ + (1 - β) / (4 * κ) * φx)
    (h213 : φπ < 1 + ρ + (1 + β) / (4 * κ) * (φx + 8 / σ * (1 + ρ))) :
    OneInTwoOut (ch2 (A46 β κ σ ρ φπ φx)) (ch1 (A46 β κ σ ρ φπ φx)) (ch0 (A46 β κ σ ρ φπ φx)) := by
  by_cases hρβ : ρ < β
  · obtain ⟨h1, h2, h3⟩ := caseII_A46 hβ0 hβ1 hκ hσ hρ hφx hρβ h29 h213
    exact oneInTwoOut_of_abs_A0 h1 h2 (Or.inl h3)
  · push Not at hρβ
    have h1 : 0 < P1 (ch2 (A46 β κ σ ρ φπ φx)) (ch1 (A46 β κ σ ρ φπ φx))
        (ch0 (A46 β κ σ ρ φπ φx)) := by
      rw [P1_A46 hβ0.ne' hκ.ne']
      exact mul_pos (by positivity) (by linarith)
    have h2 : Pm1 (ch2 (A46 β κ σ ρ φπ φx)) (ch1 (A46 β κ σ ρ φπ φx))
        (ch0 (A46 β κ σ ρ φπ φx)) < 0 := by
      rw [Pm1_A46 hβ0.ne' hκ.ne' hσ.ne']
      exact mul_neg_of_pos_of_neg (by positivity) (by linarith)
    refine oneInTwoOut_of_abs_A0 h1 h2 (Or.inr ?_)
    rw [ch0_A46, abs_neg, abs_of_nonneg (by positivity)]
    rw [← div_eq_inv_mul, le_div_iff₀ hβ0]
    linarith

/-- Woodford (2003), App. C.5, p. 682 ("either (A.5) must hold or … `A₂ > 3` or `A₂ < −3`",
labels per survey E27): under the sign restrictions, (2.9) and (2.13) imply Case II or Case III′
of Prop. C.2 (Case I being impossible, `ThreeByThree.caseI_impossible_46`). -/
theorem cases_A46 {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφx : 0 ≤ φx)
    (h29 : 1 - ρ < φπ + (1 - β) / (4 * κ) * φx)
    (h213 : φπ < 1 + ρ + (1 + β) / (4 * κ) * (φx + 8 / σ * (1 + ρ))) :
    CaseII3 (ch2 (A46 β κ σ ρ φπ φx)) (ch1 (A46 β κ σ ρ φπ φx)) (ch0 (A46 β κ σ ρ φπ φx)) ∨
      CaseIII3' (ch2 (A46 β κ σ ρ φπ φx)) (ch1 (A46 β κ σ ρ φπ φx))
        (ch0 (A46 β κ σ ρ φπ φx)) := by
  rcases (oneInTwoOut_iff_cases _ _ _).mp (oneInTwoOut_A46 hβ0 hβ1 hκ hσ hρ hφx h29 h213) with
    ⟨h1, h2⟩ | h | h
  · exfalso
    have := caseI_impossible_46 hβ0 hκ hσ h1 h2
    have : 0 ≤ φx / (2 * κ) := by positivity
    have : 0 ≤ 2 * (1 + β) * (1 + ρ) / (κ * σ) := by positivity
    linarith
  · exact Or.inl h
  · exact Or.inr h

/-- Woodford (2003), App. C.5, p. 682: Case II alone does not suffice — with `β = 1/2`,
`κ = σ = 1`, `ρ = 2`, `φ_π = 0`, `φ_x = 4`, (2.9) and (2.13) hold but (C.15) fails
(`A₀² − A₀A₂ + A₁ − 1 = −3`); there `A₂ = −8`, so Case III′ applies. -/
theorem caseII_not_necessary_46 :
    ((1 : ℝ) - 2 < 0 + (1 - 1 / 2) / (4 * 1) * 4 ∧
      (0 : ℝ) < 1 + 2 + (1 + 1 / 2) / (4 * 1) * (4 + 8 / 1 * (1 + 2))) ∧
    C15 (ch2 (A46 (1 / 2) 1 1 2 0 4)) (ch1 (A46 (1 / 2) 1 1 2 0 4))
      (ch0 (A46 (1 / 2) 1 1 2 0 4)) = -3 ∧ ch2 (A46 (1 / 2) 1 1 2 0 4) = -8 := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_, ?_⟩
  · rw [C15, ch2_A46, ch1_A46, ch0_A46]; norm_num
  · rw [ch2_A46]; norm_num

/-! ### Genericity -/

/-- Woodford (2003), App. C.5, p. 682: `A v` written out. -/
theorem mulVec_A46 (β κ σ ρ φπ φx : ℝ) (v : Fin 3 → ℝ) :
    A46 β κ σ ρ φπ φx *ᵥ v = ![β⁻¹ * v 0 - β⁻¹ * κ * v 1,
      σ * β⁻¹ * (φπ - 1) * v 0 + (1 + σ * (φx / 4 - β⁻¹ * κ * (φπ - 1))) * v 1 + σ * ρ * v 2,
      β⁻¹ * φπ * v 0 + (φx / 4 - β⁻¹ * κ * φπ) * v 1 + ρ * v 2] := by
  funext i
  fin_cases i <;> simp [A46, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- Woodford (2003), Prop. 4.6 (the genericity the book leaves implicit, p. 672 fn. 2): if the
rule responds to inflation or the output gap, no eigenvector of an eigenvalue in the unit disc has
a zero lagged-interest-rate component. Such an eigenvector would be a stable eigenvector of the
exogenous-rate system of Prop. 4.2 (so `0 < μ < 1`), and the rule's row would force
`4β⁻¹κφ_πμ + φ_x(β⁻¹ − μ) = 0`. -/
theorem generic_A46 {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (hφ : 0 < φπ ∨ 0 < φx) :
    Generic (A46 β κ σ ρ φπ φx) := by
  intro μ v hμ hv h2
  rw [mulVec_A46] at hv
  have r0 : β⁻¹ * v 0 - β⁻¹ * κ * v 1 = μ * v 0 := congrFun hv 0
  have r1 : σ * β⁻¹ * (φπ - 1) * v 0 + (1 + σ * (φx / 4 - β⁻¹ * κ * (φπ - 1))) * v 1 +
      σ * ρ * v 2 = μ * v 1 := congrFun hv 1
  have r2 : β⁻¹ * φπ * v 0 + (φx / 4 - β⁻¹ * κ * φπ) * v 1 + ρ * v 2 = μ * v 2 := congrFun hv 2
  rw [h2] at r1 r2
  have hb1 : 1 < β⁻¹ := one_lt_inv₀ hβ0 |>.mpr hβ1
  have hμ1 : μ < 1 := (abs_lt.mp hμ).2
  have hQ : v 0 * (μ ^ 2 - (1 + β⁻¹ + σ * β⁻¹ * κ) * μ + β⁻¹) = 0 := by
    linear_combination (β⁻¹ * κ) * r1 - (σ * β⁻¹ * κ) * r2 +
      (1 + σ * β⁻¹ * κ - μ) * r0
  have hR : v 0 * (4 * β⁻¹ * κ * φπ * μ + φx * (β⁻¹ - μ)) = 0 := by
    linear_combination (4 * β⁻¹ * κ) * r2 - (4 * β⁻¹ * κ * φπ) * r0 + φx * r0
  have hv0 : v 0 = 0 := by
    by_contra hne
    have hQ0 : μ ^ 2 - (1 + β⁻¹ + σ * β⁻¹ * κ) * μ + β⁻¹ = 0 :=
      (mul_eq_zero.mp hQ).resolve_left hne
    have hR0 : 4 * β⁻¹ * κ * φπ * μ + φx * (β⁻¹ - μ) = 0 :=
      (mul_eq_zero.mp hR).resolve_left hne
    have hμ0 : 0 < μ := by
      by_contra hc; push Not at hc
      have : 0 ≤ -(1 + β⁻¹ + σ * β⁻¹ * κ) * μ := by
        have : 0 ≤ 1 + β⁻¹ + σ * β⁻¹ * κ := by positivity
        nlinarith
      nlinarith [sq_nonneg μ]
    rcases hφ with h | h
    · have : 0 < 4 * β⁻¹ * κ * φπ * μ := by positivity
      have : 0 ≤ φx * (β⁻¹ - μ) := mul_nonneg hφx (by linarith)
      linarith
    · have : 0 ≤ 4 * β⁻¹ * κ * φπ * μ := by positivity
      have : 0 < φx * (β⁻¹ - μ) := mul_pos h (by linarith)
      linarith
  have hv1 : v 1 = 0 := by
    rw [hv0] at r0
    have hbk : β⁻¹ * κ ≠ 0 := by positivity
    have : β⁻¹ * κ * v 1 = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hbk
  funext i
  fin_cases i
  · exact hv0
  · exact hv1
  · exact h2

/-! ### Proposition 4.6 in full -/

/-- **Proposition 4.6, sufficiency** (Woodford (2003), p. 258; App. C.5, p. 682, where the book
omits it): for `0 < β < 1`, `κ, σ > 0`, `ρ, φ_π, φ_x ≥ 0`, if the rule (2.12) satisfies (2.9) and
(2.13) and responds to inflation or the output gap, equilibrium is determinate. -/
theorem prop46_sufficiency [Nonempty Ω] {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (h29 : 1 - ρ < φπ + (1 - β) / (4 * κ) * φx)
    (h213 : φπ < 1 + ρ + (1 + β) / (4 * κ) * (φx + 8 / σ * (1 + ρ)))
    (hφ : 0 < φπ ∨ 0 < φx) : Determinate46 𝔼 β κ σ ρ φπ φx := by
  rw [determinate46_iff_for 𝔼 hβ0.ne']
  exact determinateFor_of_determinate3 𝔼
    (determinate3_of 𝔼 (oneInTwoOut_A46 hβ0 hβ1 hκ hσ hρ hφx h29 h213)
      (generic_A46 hβ0 hβ1 hκ hσ hφπ hφx hφ)) _

/-- Woodford (2003), Prop. 4.6, p. 258: a determinate equilibrium requires the rule to respond to
inflation or the output gap (with `φ_π = φ_x = 0` the rate is exogenous, Prop. 4.2). -/
theorem response_of_determinate46 [Nonempty Ω] {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β)
    (hκ : 0 < κ) (hσ : 0 < σ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (hd : Determinate46 𝔼 β κ σ ρ φπ φx) : 0 < φπ ∨ 0 < φx := by
  rw [determinate46_iff_for 𝔼 hβ0.ne'] at hd
  by_contra h
  push Not at h
  have e1 : φπ = 0 := le_antisymm h.1 hφπ
  have e2 : φx = 0 := le_antisymm h.2 hφx
  subst e1 e2
  rw [A46_zero] at hd
  exact not_generic_A44_zero hβ0 hκ hσ (generic_of_determinateFor 𝔼 hd)

/-- **Proposition 4.6, corrected and completed** (Woodford (2003), p. 258; App. C.5, p. 682): for
`0 < β < 1`, `κ, σ > 0` and `ρ, φ_π, φ_x ≥ 0`, equilibrium under the inertial forward-looking rule
(2.12) is determinate **if and only if** (2.9) and (2.13) hold and the rule responds to inflation
or the output gap. (Without the last condition sufficiency is false: `prop46_printed_false`.) -/
theorem prop46 [Nonempty Ω] {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    Determinate46 𝔼 β κ σ ρ φπ φx ↔
      (1 - ρ < φπ + (1 - β) / (4 * κ) * φx ∧
        φπ < 1 + ρ + (1 + β) / (4 * κ) * (φx + 8 / σ * (1 + ρ))) ∧ (0 < φπ ∨ 0 < φx) := by
  constructor
  · intro hd
    exact ⟨prop46_necessity 𝔼 hβ0 hβ1 hκ hσ hρ hφπ hφx hd,
      response_of_determinate46 𝔼 hβ0 hκ hσ hφπ hφx hd⟩
  · rintro ⟨⟨h29, h213⟩, hφ⟩
    exact prop46_sufficiency 𝔼 hβ0 hβ1 hκ hσ hρ hφπ hφx h29 h213 hφ

/-- Woodford (2003), Prop. 4.6, p. 258, under the extra hypothesis that the rule responds to
inflation or the output gap: (2.9) and (2.13) are necessary **and sufficient**. -/
theorem prop46_of_response [Nonempty Ω] {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (hφ : 0 < φπ ∨ 0 < φx) :
    Determinate46 𝔼 β κ σ ρ φπ φx ↔
      1 - ρ < φπ + (1 - β) / (4 * κ) * φx ∧
        φπ < 1 + ρ + (1 + β) / (4 * κ) * (φx + 8 / σ * (1 + ρ)) := by
  rw [prop46 𝔼 hβ0 hβ1 hκ hσ hρ hφπ hφx]
  exact ⟨fun h => h.1, fun h => ⟨h, hφ⟩⟩

/-- Woodford (2003), Prop. 4.6, p. 258 (**the conditions alone are not sufficient**): with
`φ_π = φ_x = 0` and `ρ > 1`, (2.9) and (2.13) hold, but the rule makes the interest rate
exogenous and equilibrium is not determinate. -/
theorem prop46_printed_false [Nonempty Ω] {β κ σ ρ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hσ : 0 < σ)
    (hρ : 1 < ρ) :
    (1 - ρ < 0 + (1 - β) / (4 * κ) * 0 ∧
      (0 : ℝ) < 1 + ρ + (1 + β) / (4 * κ) * (0 + 8 / σ * (1 + ρ))) ∧
      ¬ Determinate46 𝔼 β κ σ ρ 0 0 := by
  refine ⟨⟨by simp; linarith, by positivity⟩, fun h => ?_⟩
  rcases response_of_determinate46 𝔼 hβ0 hκ hσ le_rfl le_rfl h with h' | h' <;>
    exact lt_irrefl _ h'

/-! ### Every bounded adapted forcing: the general Blanchard–Kahn theorem -/

/-- Woodford (2003), Prop. 4.6, p. 258 (App. C.5): under the sign restrictions, (2.9), (2.13) and
a response to inflation or the gap, the matrix `A` of the forward-looking inertial system satisfies
the general Blanchard–Kahn conditions (no unit eigenvalue, one stable eigenvalue, genericity). -/
theorem prop46_bk_conditions {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (h29 : 1 - ρ < φπ + (1 - β) / (4 * κ) * φx)
    (h213 : φπ < 1 + ρ + (1 + β) / (4 * κ) * (φx + 8 / σ * (1 + ρ)))
    (hφ : 0 < φπ ∨ 0 < φx) :
    InvariantSplit.NoUnit (A46 β κ σ ρ φπ φx) ∧
      InvariantSplit.stableCount (A46 β κ σ ρ φπ φx) = 1 ∧ GenericOn (A46 β κ σ ρ φπ φx) e3 := by
  have h := (oneInTwoOut_iff_count _).mp (oneInTwoOut_A46 hβ0 hβ1 hκ hσ hρ hφx h29 h213)
  exact ⟨h.1, h.2, (generic_iff_genericOn h).mp (generic_A46 hβ0 hβ1 hκ hσ hφπ hφx hφ)⟩

/-- Woodford (2003), Prop. 4.6, p. 258, through the general theorem: under (2.9), (2.13) and a
response to inflation or the gap, the forward-looking inertial system is determinate for **every**
bounded adapted forcing vector (not only the IS disturbance of the model). -/
theorem prop46_determinate3 [Nonempty Ω] {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (h29 : 1 - ρ < φπ + (1 - β) / (4 * κ) * φx)
    (h213 : φπ < 1 + ρ + (1 + β) / (4 * κ) * (φx + 8 / σ * (1 + ρ)))
    (hφ : 0 < φπ ∨ 0 < φx) : Determinate3 𝔼 (A46 β κ σ ρ φπ φx) := by
  rw [determinate3_iff_on, determinateOn_iff, Fintype.card_fin]
  exact prop46_bk_conditions hβ0 hβ1 hκ hσ hρ hφπ hφx h29 h213 hφ

/-- Woodford (2003), Prop. 4.6, p. 258: for the forward-looking inertial system, determinacy for
every bounded adapted forcing vector holds iff (2.9) and (2.13) hold and the rule responds to
inflation or the gap — the same condition as for the model's own disturbance (`prop46`). -/
theorem prop46_determinate3_iff [Nonempty Ω] {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    Determinate3 𝔼 (A46 β κ σ ρ φπ φx) ↔
      (1 - ρ < φπ + (1 - β) / (4 * κ) * φx ∧
        φπ < 1 + ρ + (1 + β) / (4 * κ) * (φx + 8 / σ * (1 + ρ))) ∧ (0 < φπ ∨ 0 < φx) := by
  constructor
  · intro hd
    exact (prop46 𝔼 hβ0 hβ1 hκ hσ hρ hφπ hφx).mp
      ((determinate46_iff_for 𝔼 hβ0.ne').mpr (determinateFor_of_determinate3 𝔼 hd _))
  · rintro ⟨⟨h29, h213⟩, hφ⟩
    exact prop46_determinate3 𝔼 hβ0 hβ1 hκ hσ hρ hφπ hφx h29 h213 hφ

/-! ### p. 260: the later-period Clarida–Galí–Gertler rule -/

/-- Woodford (2003), p. 260: the Clarida et al. later-period rule `ρ = 0.79`, `φ_π = 0.45`,
`φ_x = 0.20`, in the forward-looking form (2.12), "implies a determinate equilibrium" — true for
every `0 < β < 1`, `κ, σ > 0` (the book's claim relied on the sufficiency it had not shown). -/
theorem clarida_later_determinate [Nonempty Ω] {β κ σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) : Determinate46 𝔼 β κ σ 0.79 0.45 0.20 := by
  obtain ⟨h29, -, h213⟩ := Determinacy2Forward.clarida_later hβ0 hβ1 hσ hκ
  unfold Determinacy2Forward.Cond29 Determinacy2.taylorLHS at h29
  unfold Determinacy2Forward.Cond213 at h213
  refine prop46_sufficiency 𝔼 hβ0 hβ1 hκ hσ (by norm_num) (by norm_num) (by norm_num) h29 ?_
    (Or.inl (by norm_num))
  rw [div_eq_mul_inv 8 σ]
  exact h213

/-- Woodford (2003), p. 260: the later-period Clarida et al. rule in the form (2.12) gives a
determinate system for every bounded adapted forcing vector. -/
theorem clarida_later_determinate3 [Nonempty Ω] {β κ σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) : Determinate3 𝔼 (A46 β κ σ 0.79 0.45 0.20) := by
  have h := (prop46 𝔼 hβ0 hβ1 hκ hσ (by norm_num) (by norm_num) (by norm_num)).mp
    (clarida_later_determinate 𝔼 hβ0 hβ1 hκ hσ)
  exact prop46_determinate3 𝔼 hβ0 hβ1 hκ hσ (by norm_num) (by norm_num) (by norm_num) h.1.1 h.1.2
    h.2

/-- Woodford (2003), pp. 255, 260: the later-period Clarida et al. coefficients are also
determinate under the contemporaneous inertial rule (2.8) (Prop. 4.4: `φ_π = 0.45 > 1 − ρ`). -/
theorem clarida_later_determinate44 [Nonempty Ω] {β κ σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) : Determinate44 𝔼 β κ σ 0.79 0.45 0.20 := by
  refine (prop44 𝔼 hβ0 hβ1 hκ hσ (by norm_num) (by norm_num) (by norm_num)).mpr
    ⟨?_, Or.inl (by norm_num)⟩
  have : 0 ≤ (1 - β) / (4 * κ) * 0.20 :=
    mul_nonneg (div_nonneg (by linarith) (by linarith)) (by norm_num)
  linarith

end Woodford.NeoWicksellianFramework.Prop46Sufficiency
