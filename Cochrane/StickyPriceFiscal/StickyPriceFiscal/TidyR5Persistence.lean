/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.TidyR5Resonant

/-!
# How the impact of an AR(1) rate rise depends on its persistence, for every `ρ`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.3, p. 131, with the
long-term-debt model of §5.2, pp. 127–129.

The book says that, to lower inflation through long-term debt, "the interest-rate rise must be
persistent and unexpected" and that a shock "believed to be long-lasting … is most likely to be
disinflationary" (p. 131). `LongTermDebt` proves these with `ρ = β` (where, in fact, the sign of
the impact does not depend on persistence, `ar1_disinflation_iff_rho_eq_beta`). This module
treats every `0 < ρ < 1`.

Write `q = 1/λ₁` (so `λ₂ = βq`) and
`P(η) = (1 − ρq) − (ρ(1 − q) + βq(1 − ρ))η`, `Q(η) = ρq[(1 + β − ρ − βq) − (1 − ρq)βη]`.

## Main results

* `impactRHS_eq_factor`: the impact response is
  `π₁(η) = (Q(η) − ω̃P(η)) / ((1 − ρη)(1 − βqη)(1 − ω̃η))`; `eqm_impact`: this is the impact of
  every equilibrium, resonant (`λ₁η = 1`) or not.
* `impact_neg_iff_omStar`: **disinflation on impact iff `ω̃ > ω*(η) = Q(η)/P(η)`**; the
  threshold runs from `ω*(0)` to `ω*(1) = ρ/λ₁` (`omStar_one`, the permanent-rise threshold of
  `LongTermDebt.ltd_disinflation_iff`), and `tendsto_impact_one` (the AR(1) impact tends to the
  permanent-rise impact `(ρ/λ₁ − ω̃)/(1 − ω̃)` as `η → 1`).
* `omStar_cross`: `Q(η₂)P(η₁) − Q(η₁)P(η₂) = (η₂ − η₁)·ρq(1 − q)(1 − βq)(1 − ρ)(ρ − β)`, hence
  the threshold is strictly decreasing in persistence iff `ρ < β` (`omStar_strictAntiOn`),
  constant iff `ρ = β` (`omStar_rho_eq_beta`), strictly increasing iff `ρ > β`
  (`omStar_strictMonoOn`).
* `ρ ≤ β`, **the book's claims hold**: `persistence_helps` (if an AR(1) rise disinflates, so
  does every more persistent one), `persistence_needed` (`ρ < β`: there are maturities for which
  a one-period rise does not disinflate while sufficiently persistent rises do),
  `persistence_magnifies` (once disinflationary, more persistence gives strictly more
  disinflation).
* `ρ > β`, **the book's claims fail**: `persistence_hurts` (if a rise disinflates, so does every
  less persistent one), and `rho_gt_beta_reversal`: with `ω̃ = ρ/λ₁` every AR(1) rise of
  persistence `η < 1` lowers inflation on impact, the permanent rise does not (impact `0`), the
  impact rises towards `0` as `η → 1`, and it is not antitone in `η`;
  `rho_gt_beta_reversal_eqm` states it for the equilibria.
-/

namespace Cochrane.StickyPriceFiscal.TidyR5Persistence

open Filter Topology NKModel TwoSidedMA FiscalNK LongTermDebt TidyR5Resonant

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), p. 131 (tool): the linear function
`P(η) = (1 − ρq) − (ρ(1 − q) + βq(1 − ρ))η`. -/
def pP (ρ β q η : ℝ) : ℝ := (1 - ρ * q) - (ρ * (1 - q) + β * q * (1 - ρ)) * η

/-- Cochrane (2023), p. 131 (tool): the linear function
`Q(η) = ρq[(1 + β − ρ − βq) − (1 − ρq)βη]`. -/
def pQ (ρ β q η : ℝ) : ℝ := ρ * q * ((1 + β - ρ - β * q) - (1 - ρ * q) * β * η)

/-- Cochrane (2023), p. 131: the maturity threshold `ω*(η) = Q(η)/P(η)` above which an AR(1)
rise of persistence `η` lowers inflation on impact. -/
noncomputable def omStar (ρ β q η : ℝ) : ℝ := pQ ρ β q η / pP ρ β q η

/-- Cochrane (2023), eq. (5.6), p. 119: `λ₂ = β/λ₁` (from `λ₁λ₂ = β`). -/
theorem lam2_eq {σ β κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    lam2 σ β κ = β * (lam1 σ β κ)⁻¹ := by
  have ha := mul_pos hσ hκ
  have hl0 : lam1 σ β κ ≠ 0 := (lam1_pos ha hβ).ne'
  have := lam_prod ha hβ
  field_simp
  linarith

/-- Cochrane (2023), p. 131 (tool): the identity `P(η) − ηQ(η) = (1 − ρq)(1 − ρη)(1 − βqη)`. -/
theorem pP_sub_pQ (ρ β q η : ℝ) :
    pP ρ β q η - η * pQ ρ β q η = (1 - ρ * q) * (1 - ρ * η) * (1 - β * q * η) := by
  unfold pP pQ
  ring

/-- Cochrane (2023), p. 131 (tool): `P(1) = (1 − ρ)(1 − βq)` and `Q(1) = ρq(1 − ρ)(1 − βq)`. -/
theorem pP_pQ_one (ρ β q : ℝ) :
    pP ρ β q 1 = (1 - ρ) * (1 - β * q) ∧ pQ ρ β q 1 = ρ * q * ((1 - ρ) * (1 - β * q)) := by
  unfold pP pQ
  constructor <;> ring

/-- Cochrane (2023), p. 131 (tool): for `0 < q < 1`, `0 < ρ < 1`, `β ≥ 0`, `βq < 1` and
`η ≤ 1`, `P(η) > 0` and `Q(η) > 0`. -/
theorem pP_pQ_pos {ρ β q η : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hβ : 0 ≤ β) (hβq : β * q < 1) (hη1 : η ≤ 1) :
    0 < pP ρ β q η ∧ 0 < pQ ρ β q η := by
  unfold pP pQ
  have hρq : ρ * q < 1 := by nlinarith
  have hc : 0 ≤ ρ * (1 - q) + β * q * (1 - ρ) := by
    have : 0 ≤ β * q := by positivity
    nlinarith
  have hb : 0 ≤ (1 - ρ * q) * β := by nlinarith
  constructor
  · have : (ρ * (1 - q) + β * q * (1 - ρ)) * η ≤ ρ * (1 - q) + β * q * (1 - ρ) :=
      mul_le_of_le_one_right hc hη1
    nlinarith
  · refine mul_pos (mul_pos hρ0 hq0) ?_
    have : (1 - ρ * q) * β * η ≤ (1 - ρ * q) * β := mul_le_of_le_one_right hb hη1
    nlinarith

/-- Cochrane (2023), p. 131 (algebraic form): with `ℓ = βq`,
`ρ/(1 − ρη)[(1 − ρq) − (1 − q)(1 − ℓ)/(1 − ℓη)] − (1 − ρq)ω̃/(1 − ω̃η)
  = (Q(η) − ω̃P(η))/((1 − ρη)(1 − βqη)(1 − ω̃η))`. -/
theorem factor_identity {ρ β q om η : ℝ} (h1 : 1 - ρ * η ≠ 0) (h2 : 1 - β * q * η ≠ 0)
    (h3 : 1 - om * η ≠ 0) :
    ρ / (1 - ρ * η) * ((1 - ρ * q) - (1 - q) * (1 - β * q) / (1 - β * q * η)) -
      (1 - ρ * q) * (om / (1 - om * η)) =
    (pQ ρ β q η - om * pP ρ β q η) / ((1 - ρ * η) * (1 - β * q * η) * (1 - om * η)) := by
  unfold pP pQ
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero h1 h2) h3)]
  have e1 : ρ / (1 - ρ * η) * (1 - ρ * η) = ρ := div_mul_cancel₀ ρ h1
  have e2 : (1 - q) * (1 - β * q) / (1 - β * q * η) * (1 - β * q * η) =
      (1 - q) * (1 - β * q) := div_mul_cancel₀ _ h2
  have e3 : om / (1 - om * η) * (1 - om * η) = om := div_mul_cancel₀ om h3
  linear_combination ((1 - ρ * q) - (1 - q) * (1 - β * q) / (1 - β * q * η)) *
      (1 - β * q * η) * (1 - om * η) * e1 - ρ * (1 - om * η) * e2 -
    (1 - ρ * q) * (1 - ρ * η) * (1 - β * q * η) * e3

/-- Cochrane (2023), p. 131: **the impact response in factored form**,
`π₁(η) = (Q(η) − ω̃P(η))/((1 − ρη)(1 − βqη)(1 − ω̃η))` with `q = 1/λ₁`. -/
theorem impactRHS_eq_factor {σ β κ ρ om η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (h1 : 1 - ρ * η ≠ 0) (h2 : 1 - β * (lam1 σ β κ)⁻¹ * η ≠ 0) (h3 : 1 - om * η ≠ 0) :
    impactRHS σ β κ ρ om η =
      (pQ ρ β (lam1 σ β κ)⁻¹ η - om * pP ρ β (lam1 σ β κ)⁻¹ η) /
        ((1 - ρ * η) * (1 - β * (lam1 σ β κ)⁻¹ * η) * (1 - om * η)) := by
  rw [impactRHS, lam2_eq hσ hκ hβ]
  exact factor_identity h1 h2 h3

/-- Cochrane (2023), §5.3, p. 131: **the impact of every AR(1) equilibrium** (`0 ≤ η < 1`,
resonant or not): the book's impact `π₁` (Lean index `π 0`) equals `impactRHS`, the closed form of
`LongTermDebt.ar1_impact`. -/
theorem eqm_impact {σ β κ ρ om η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hom0 : 0 ≤ om) (hom1 : om < 1) (hη0 : 0 ≤ η) (hη1 : η < 1)
    {x π v q rn : ℕ → Ω → ℝ}
    (h : LTD 𝔼 σ β κ ρ om (fun t _ => η ^ t) (fun _ _ => 0) 0 0 x π v q rn) (hqa : 𝔼.Adapted q)
    (hπb : BoundedProc π) (hvb : BoundedProc v) (hqb : BoundedProc q) (ω : Ω) :
    π 0 ω = impactRHS σ β κ ρ om η := by
  have ha := mul_pos hσ hκ
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  by_cases hres : lam1 σ β κ * η = 1
  · obtain ⟨he, -, -⟩ := resonant_eta hσ hκ hβ hres
    rw [(ltd_ar1_resonant 𝔼 hσ hκ hβ hρ0 hρ1 hom0 hom1 hres h hqa hπb hvb hqb 0 ω).2]
    simp only [Nat.cast_zero, mul_zero, pow_zero, mul_one, zero_add]
    rw [he]
    exact resC_eq_impactRHS hσ hκ hβ hρ0 hρ1 hom0 hom1
  · rw [(ltd_ar1 𝔼 hσ hκ hβ hρ0 hρ1 hom0 hom1 hη0 hη1 hres h hqa hπb hvb hqb 0 ω).2]
    simp only [pow_zero, mul_one]
    exact ar1_impact hσ hκ hβ (by nlinarith) (by nlinarith) (by nlinarith) hres

/-- Cochrane (2023), p. 131: the model's `q = 1/λ₁` and `βq = λ₂` satisfy the hypotheses of
`pP_pQ_pos`: `0 < q < 1`, `βq < 1`. -/
theorem q_facts {σ β κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    0 < (lam1 σ β κ)⁻¹ ∧ (lam1 σ β κ)⁻¹ < 1 ∧ β * (lam1 σ β κ)⁻¹ < 1 := by
  have ha := mul_pos hσ hκ
  have h1 := one_lt_lam1 ha hβ
  refine ⟨inv_pos.mpr (by linarith), inv_lt_one_of_one_lt₀ h1, ?_⟩
  rw [← lam2_eq hσ hκ hβ]
  exact lam2_lt_one ha hβ

/-- Cochrane (2023), §5.3, p. 131: **the sign of the impact**: for `0 ≤ η < 1`, the AR(1) rise
lowers inflation on impact iff `Q(η) < ω̃ P(η)`. -/
theorem impact_neg_iff {σ β κ ρ om η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hom0 : 0 ≤ om) (hom1 : om < 1) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    impactRHS σ β κ ρ om η < 0 ↔
      pQ ρ β (lam1 σ β κ)⁻¹ η < om * pP ρ β (lam1 σ β κ)⁻¹ η := by
  obtain ⟨hq0, hq1, hβq⟩ := q_facts hσ hκ hβ
  have d1 : 0 < 1 - ρ * η := by nlinarith
  have d2 : 0 < 1 - β * (lam1 σ β κ)⁻¹ * η := by nlinarith
  have d3 : 0 < 1 - om * η := by nlinarith
  rw [impactRHS_eq_factor hσ hκ hβ d1.ne' d2.ne' d3.ne', div_neg_iff]
  have hD : 0 < (1 - ρ * η) * (1 - β * (lam1 σ β κ)⁻¹ * η) * (1 - om * η) := by positivity
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · linarith
    · linarith
  · intro h
    exact Or.inr ⟨by linarith, hD⟩

/-- Cochrane (2023), §5.3, p. 131: **disinflation on impact iff `ω̃ > ω*(η)`**, the
persistence-dependent maturity threshold. -/
theorem impact_neg_iff_omStar {σ β κ ρ om η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hom0 : 0 ≤ om) (hom1 : om < 1) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    impactRHS σ β κ ρ om η < 0 ↔ omStar ρ β (lam1 σ β κ)⁻¹ η < om := by
  obtain ⟨hq0, hq1, hβq⟩ := q_facts hσ hκ hβ
  have hP := (pP_pQ_pos hq0 hq1 hρ0 hρ1 hβ.le hβq hη1.le).1
  rw [impact_neg_iff hσ hκ hβ hρ0 hρ1 hom0 hom1 hη0 hη1, omStar, div_lt_iff₀ hP]

/-- Cochrane (2023), p. 131 and Fig. 5.4: at full persistence the threshold is the
permanent-rise threshold, `ω*(1) = ρq = ρ/λ₁` (`LongTermDebt.ltd_disinflation_iff`). -/
theorem omStar_one {ρ β q : ℝ} (hρ1 : ρ < 1) (hβq : β * q < 1) : omStar ρ β q 1 = ρ * q := by
  rw [omStar, (pP_pQ_one ρ β q).1, (pP_pQ_one ρ β q).2]
  have : (1 - ρ) * (1 - β * q) ≠ 0 := mul_ne_zero (by linarith) (by linarith)
  exact mul_div_cancel_right₀ _ this

/-- Cochrane (2023), p. 131: **the cross-product identity** for the two linear functions,
`Q(η₂)P(η₁) − Q(η₁)P(η₂) = (η₂ − η₁) ρq(1 − q)(1 − βq)(1 − ρ)(ρ − β)`. -/
theorem omStar_cross (ρ β q η₁ η₂ : ℝ) :
    pQ ρ β q η₂ * pP ρ β q η₁ - pQ ρ β q η₁ * pP ρ β q η₂ =
      (η₂ - η₁) * (ρ * q * (1 - q) * (1 - β * q) * (1 - ρ) * (ρ - β)) := by
  unfold pP pQ
  ring

/-- Cochrane (2023), p. 131: with `ρ < β` the threshold `ω*(η)` is strictly decreasing in
persistence on `[0, 1]`: more persistent rises disinflate for more maturity structures. -/
theorem omStar_strictAntiOn {ρ β q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hβq : β * q < 1) (hρβ : ρ < β) :
    StrictAntiOn (omStar ρ β q) (Set.Icc 0 1) := by
  intro η₁ h₁ η₂ h₂ hlt
  have hβ : 0 ≤ β := by linarith
  have p1 := pP_pQ_pos hq0 hq1 hρ0 hρ1 hβ hβq h₁.2
  have p2 := pP_pQ_pos hq0 hq1 hρ0 hρ1 hβ hβq h₂.2
  have hc := omStar_cross ρ β q η₁ η₂
  have hk : 0 < ρ * q * (1 - q) * (1 - β * q) * (1 - ρ) := by
    have : 0 < 1 - q := by linarith
    have : 0 < 1 - β * q := by linarith
    have : 0 < 1 - ρ := by linarith
    positivity
  have hneg : (η₂ - η₁) * (ρ * q * (1 - q) * (1 - β * q) * (1 - ρ) * (ρ - β)) < 0 := by
    have : ρ * q * (1 - q) * (1 - β * q) * (1 - ρ) * (ρ - β) < 0 :=
      mul_neg_of_pos_of_neg hk (by linarith)
    exact mul_neg_of_pos_of_neg (by linarith) this
  unfold omStar
  rw [div_lt_div_iff₀ p2.1 p1.1]
  linarith

/-- Cochrane (2023), p. 131: with `ρ > β` the threshold `ω*(η)` is strictly **increasing** in
persistence on `[0, 1]`: more persistent rises need longer debt to disinflate. -/
theorem omStar_strictMonoOn {ρ β q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hρ1 : ρ < 1)
    (hβ : 0 ≤ β) (hβq : β * q < 1) (hβρ : β < ρ) :
    StrictMonoOn (omStar ρ β q) (Set.Icc 0 1) := by
  intro η₁ h₁ η₂ h₂ hlt
  have hρ0 : 0 < ρ := by linarith
  have p1 := pP_pQ_pos hq0 hq1 hρ0 hρ1 hβ hβq h₁.2
  have p2 := pP_pQ_pos hq0 hq1 hρ0 hρ1 hβ hβq h₂.2
  have hc := omStar_cross ρ β q η₁ η₂
  have hk : 0 < ρ * q * (1 - q) * (1 - β * q) * (1 - ρ) := by
    have : 0 < 1 - q := by linarith
    have : 0 < 1 - β * q := by linarith
    have : 0 < 1 - ρ := by linarith
    positivity
  have hpos : 0 < (η₂ - η₁) * (ρ * q * (1 - q) * (1 - β * q) * (1 - ρ) * (ρ - β)) :=
    mul_pos (by linarith) (mul_pos hk (by linarith))
  unfold omStar
  rw [div_lt_div_iff₀ p1.1 p2.1]
  linarith

/-- Cochrane (2023), p. 131: with `ρ = β` the threshold is constant, `ω*(η) = ρq` for every
`η ≤ 1` (so the sign of the impact does not depend on persistence,
`LongTermDebt.ar1_disinflation_iff_rho_eq_beta`). -/
theorem omStar_rho_eq_beta {ρ q η : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hρq : ρ * q < 1) (hη1 : η ≤ 1) : omStar ρ ρ q η = ρ * q := by
  have p := pP_pQ_pos hq0 hq1 hρ0 hρ1 hρ0.le hρq hη1
  have hc := omStar_cross ρ ρ q η 1
  rw [(pP_pQ_one ρ ρ q).1, (pP_pQ_one ρ ρ q).2, sub_self, mul_zero, mul_zero] at hc
  unfold omStar
  rw [div_eq_iff p.1.ne']
  have hne : (1 - ρ) * (1 - ρ * q) ≠ 0 := mul_ne_zero (by linarith) (by linarith)
  have : pQ ρ ρ q η * ((1 - ρ) * (1 - ρ * q)) = ρ * q * pP ρ ρ q η * ((1 - ρ) * (1 - ρ * q)) := by
    linear_combination -hc
  exact mul_right_cancel₀ hne this

/-- Cochrane (2023), §5.3, p. 131 (`ρ ≤ β`): **persistence helps**: if an AR(1) rise of
persistence `η₁` lowers inflation on impact, so does every more persistent one. -/
theorem persistence_helps {σ β κ ρ om η₁ η₂ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hρβ : ρ ≤ β) (hom0 : 0 ≤ om) (hom1 : om < 1) (h₁0 : 0 ≤ η₁)
    (h12 : η₁ ≤ η₂) (h₂1 : η₂ < 1) (h : impactRHS σ β κ ρ om η₁ < 0) :
    impactRHS σ β κ ρ om η₂ < 0 := by
  obtain ⟨hq0, hq1, hβq⟩ := q_facts hσ hκ hβ
  rw [impact_neg_iff hσ hκ hβ hρ0 hρ1 hom0 hom1 h₁0 (by linarith)] at h
  rw [impact_neg_iff hσ hκ hβ hρ0 hρ1 hom0 hom1 (by linarith) h₂1]
  set q := (lam1 σ β κ)⁻¹
  have p1 := pP_pQ_pos (η := η₁) hq0 hq1 hρ0 hρ1 hβ.le hβq (by linarith)
  have p2 := pP_pQ_pos (η := η₂) hq0 hq1 hρ0 hρ1 hβ.le hβq h₂1.le
  have hc := omStar_cross ρ β q η₁ η₂
  have hk : 0 ≤ ρ * q * (1 - q) * (1 - β * q) * (1 - ρ) := by
    have : 0 < 1 - q := by linarith
    have : 0 < 1 - β * q := by linarith
    have : 0 < 1 - ρ := by linarith
    positivity
  have hle : (η₂ - η₁) * (ρ * q * (1 - q) * (1 - β * q) * (1 - ρ) * (ρ - β)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith)
      (mul_nonpos_of_nonneg_of_nonpos hk (by linarith))
  -- Q₂ P₁ ≤ Q₁ P₂ and Q₁ < ω̃ P₁ give Q₂ P₁ < ω̃ P₂ P₁
  have : pQ ρ β q η₂ * pP ρ β q η₁ < om * pP ρ β q η₂ * pP ρ β q η₁ := by
    nlinarith [mul_lt_mul_of_pos_right h p2.1]
  exact lt_of_mul_lt_mul_right this p1.1.le

/-- Cochrane (2023), §5.3, p. 131 (`ρ > β`): **persistence hurts**: if an AR(1) rise of
persistence `η₂` lowers inflation on impact, so does every less persistent one. -/
theorem persistence_hurts {σ β κ ρ om η₁ η₂ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ1 : ρ < 1) (hβρ : β < ρ) (hom0 : 0 ≤ om) (hom1 : om < 1) (h₁0 : 0 ≤ η₁)
    (h12 : η₁ ≤ η₂) (h₂1 : η₂ < 1) (h : impactRHS σ β κ ρ om η₂ < 0) :
    impactRHS σ β κ ρ om η₁ < 0 := by
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨hq0, hq1, hβq⟩ := q_facts hσ hκ hβ
  rw [impact_neg_iff hσ hκ hβ hρ0 hρ1 hom0 hom1 (by linarith) h₂1] at h
  rw [impact_neg_iff hσ hκ hβ hρ0 hρ1 hom0 hom1 h₁0 (by linarith)]
  set q := (lam1 σ β κ)⁻¹
  have p1 := pP_pQ_pos (η := η₁) hq0 hq1 hρ0 hρ1 hβ.le hβq (by linarith)
  have p2 := pP_pQ_pos (η := η₂) hq0 hq1 hρ0 hρ1 hβ.le hβq h₂1.le
  have hc := omStar_cross ρ β q η₁ η₂
  have hk : 0 ≤ ρ * q * (1 - q) * (1 - β * q) * (1 - ρ) := by
    have : 0 < 1 - q := by linarith
    have : 0 < 1 - β * q := by linarith
    have : 0 < 1 - ρ := by linarith
    positivity
  have hle : 0 ≤ (η₂ - η₁) * (ρ * q * (1 - q) * (1 - β * q) * (1 - ρ) * (ρ - β)) :=
    mul_nonneg (by linarith) (mul_nonneg hk (by linarith))
  have : pQ ρ β q η₁ * pP ρ β q η₂ < om * pP ρ β q η₁ * pP ρ β q η₂ := by
    nlinarith [mul_lt_mul_of_pos_right h p1.1]
  exact lt_of_mul_lt_mul_right this p2.1.le

/-- Cochrane (2023), p. 131 (tool): `1/a₂ − 1/b₂ < 1/a₁ − 1/b₁` when `b₁ = b₂ + d`, `d > 0`,
`b₂ > 0`, `a₁ > b₁` and `a₂ ≥ a₁ − d`. -/
theorem recip_gap_lt {a₁ a₂ b₁ b₂ d : ℝ} (hd : 0 < d) (hb : b₁ = b₂ + d) (hb2 : 0 < b₂)
    (ha1 : b₁ < a₁) (ha2 : a₁ - d ≤ a₂) : 1 / a₂ - 1 / b₂ < 1 / a₁ - 1 / b₁ := by
  have hb1 : 0 < b₁ := by linarith
  have hA1 : 0 < a₁ := by linarith
  have hA2 : b₂ < a₂ := by linarith
  have hA2' : 0 < a₂ := by linarith
  have e1 : 1 / a₂ - 1 / a₁ = (a₁ - a₂) / (a₁ * a₂) := by field_simp
  have e2 : 1 / b₂ - 1 / b₁ = d / (b₁ * b₂) := by rw [hb]; field_simp; ring
  have s1 : (a₁ - a₂) / (a₁ * a₂) ≤ d / (a₁ * a₂) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have s2 : d / (a₁ * a₂) < d / (b₁ * b₂) :=
    div_lt_div_of_pos_left hd (by positivity) (mul_lt_mul'' ha1 hA2 hb1.le hb2.le)
  linarith

/-- Cochrane (2023), p. 131 (tool): for `Q > 0`, `ω̃ > 0`, `ω̃η < 1` and
`P − ηQ = (1 − ρq)(1 − ρη)(1 − βqη)`, the impact is
`(1 − ρq)[1/(P/Q − η) − 1/(1/ω̃ − η)]`. -/
theorem impact_recip_form {ρ β q om η : ℝ} (hQ : 0 < pQ ρ β q η) (hom : 0 < om)
    (h1 : 1 - ρ * η ≠ 0) (h2 : 1 - β * q * η ≠ 0) (h3 : 1 - om * η ≠ 0) (hρq : 1 - ρ * q ≠ 0) :
    (pQ ρ β q η - om * pP ρ β q η) / ((1 - ρ * η) * (1 - β * q * η) * (1 - om * η)) =
      (1 - ρ * q) * (1 / (pP ρ β q η / pQ ρ β q η - η) - 1 / (1 / om - η)) := by
  have hPQ := pP_sub_pQ ρ β q η
  set X := (1 - ρ * q) * (1 - ρ * η) * (1 - β * q * η) with hX
  have hXne : X ≠ 0 := mul_ne_zero (mul_ne_zero hρq h1) h2
  have r1 : 1 / (pP ρ β q η / pQ ρ β q η - η) = pQ ρ β q η / X := by
    have : pP ρ β q η / pQ ρ β q η - η = X / pQ ρ β q η := by
      rw [eq_div_iff hQ.ne', sub_mul, div_mul_cancel₀ _ hQ.ne']
      exact hPQ
    rw [this, one_div_div]
  have r2 : 1 / (1 / om - η) = om / (1 - om * η) := by
    have : 1 / om - η = (1 - om * η) / om := by
      rw [eq_div_iff hom.ne', sub_mul, div_mul_cancel₀ _ hom.ne']
      ring
    rw [this, one_div_div]
  rw [r1, r2, div_eq_iff (mul_ne_zero (mul_ne_zero h1 h2) h3)]
  have eX : pQ ρ β q η / X * X = pQ ρ β q η := div_mul_cancel₀ _ hXne
  have e3 : om / (1 - om * η) * (1 - om * η) = om := div_mul_cancel₀ om h3
  have hPe : pP ρ β q η = X + η * pQ ρ β q η := by linarith
  linear_combination (-(1 - om * η)) * eX + X * e3 - om * hPe

/-- Cochrane (2023), §5.3, p. 131 ("A sudden shock, that is believed to be long-lasting … is most
likely to be disinflationary"), `ρ ≤ β`: **persistence magnifies the disinflation**: if the
AR(1) rise of persistence `η₁` lowers inflation on impact, every more persistent rise lowers it
strictly more. -/
theorem persistence_magnifies {σ β κ ρ om η₁ η₂ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hρβ : ρ ≤ β) (hom0 : 0 ≤ om) (hom1 : om < 1) (h₁0 : 0 ≤ η₁)
    (h12 : η₁ < η₂) (h₂1 : η₂ < 1) (h : impactRHS σ β κ ρ om η₁ < 0) :
    impactRHS σ β κ ρ om η₂ < impactRHS σ β κ ρ om η₁ := by
  obtain ⟨hq0, hq1, hβq⟩ := q_facts hσ hκ hβ
  have hneg := (impact_neg_iff hσ hκ hβ hρ0 hρ1 hom0 hom1 h₁0 (by linarith)).1 h
  set q := (lam1 σ β κ)⁻¹ with hqdef
  have p1 := pP_pQ_pos (η := η₁) hq0 hq1 hρ0 hρ1 hβ.le hβq (by linarith)
  have p2 := pP_pQ_pos (η := η₂) hq0 hq1 hρ0 hρ1 hβ.le hβq h₂1.le
  have hom : 0 < om := by
    by_contra hc
    have : om = 0 := le_antisymm (not_lt.mp hc) hom0
    rw [this, zero_mul] at hneg
    linarith [p1.2]
  have hρq : 0 < 1 - ρ * q := by nlinarith
  have d : ∀ η, 0 ≤ η → η < 1 → 1 - ρ * η ≠ 0 ∧ 1 - β * q * η ≠ 0 ∧ 1 - om * η ≠ 0 :=
    fun η h0 h1 => ⟨by nlinarith, by nlinarith, by nlinarith⟩
  obtain ⟨d11, d12, d13⟩ := d η₁ h₁0 (by linarith)
  obtain ⟨d21, d22, d23⟩ := d η₂ (by linarith) h₂1
  rw [impactRHS_eq_factor hσ hκ hβ d11 d12 d13, impactRHS_eq_factor hσ hκ hβ d21 d22 d23,
    impact_recip_form p1.2 hom d11 d12 d13 hρq.ne',
    impact_recip_form p2.2 hom d21 d22 d23 hρq.ne']
  refine mul_lt_mul_of_pos_left ?_ hρq
  -- the threshold `P/Q` is nondecreasing, and `P₁/Q₁ > 1/ω̃`
  have hc := omStar_cross ρ β q η₁ η₂
  have hk : 0 ≤ ρ * q * (1 - q) * (1 - β * q) * (1 - ρ) := by
    have : 0 < 1 - q := by linarith
    have : 0 < 1 - β * q := by linarith
    have : 0 < 1 - ρ := by linarith
    positivity
  have hle : (η₂ - η₁) * (ρ * q * (1 - q) * (1 - β * q) * (1 - ρ) * (ρ - β)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith)
      (mul_nonpos_of_nonneg_of_nonpos hk (by linarith))
  have hf : pP ρ β q η₁ / pQ ρ β q η₁ ≤ pP ρ β q η₂ / pQ ρ β q η₂ := by
    rw [div_le_div_iff₀ p1.2 p2.2]
    linarith
  have hg : 1 / om < pP ρ β q η₁ / pQ ρ β q η₁ := by
    rw [div_lt_div_iff₀ hom p1.2]
    linarith
  refine recip_gap_lt (d := η₂ - η₁) (by linarith) (by ring) ?_ (by linarith) (by linarith)
  have : η₂ * om < 1 := by nlinarith
  rw [sub_pos, lt_div_iff₀ hom]
  exact this

/-- Cochrane (2023), p. 131 (tool): the factored impact
`(Q(η) − ω̃P(η))/((1 − ρη)(1 − βqη)(1 − ω̃η))` is continuous at `η = 1`, with value
`(ρq − ω̃)/(1 − ω̃)`. -/
theorem factor_tendsto_one {ρ β q om : ℝ} (hρ1 : ρ < 1) (hβq : β * q < 1) (hom1 : om < 1) :
    Tendsto (fun η => (pQ ρ β q η - om * pP ρ β q η) /
      ((1 - ρ * η) * (1 - β * q * η) * (1 - om * η))) (𝓝 1)
      (𝓝 ((ρ * q - om) / (1 - om))) := by
  have hD : (1 - ρ * 1) * (1 - β * q * 1) * (1 - om * 1) ≠ 0 := by
    simp only [mul_one]
    exact mul_ne_zero (mul_ne_zero (by linarith) (by linarith)) (by linarith)
  have hc : ContinuousAt (fun η => (pQ ρ β q η - om * pP ρ β q η) /
      ((1 - ρ * η) * (1 - β * q * η) * (1 - om * η))) 1 := by
    unfold pP pQ
    fun_prop (disch := assumption)
  have hv : (pQ ρ β q 1 - om * pP ρ β q 1) / ((1 - ρ * 1) * (1 - β * q * 1) * (1 - om * 1)) =
      (ρ * q - om) / (1 - om) := by
    rw [(pP_pQ_one ρ β q).1, (pP_pQ_one ρ β q).2]
    simp only [mul_one]
    have hne : (1 - ρ) * (1 - β * q) ≠ 0 := mul_ne_zero (by linarith) (by linarith)
    rw [show ρ * q * ((1 - ρ) * (1 - β * q)) - om * ((1 - ρ) * (1 - β * q)) =
        (ρ * q - om) * ((1 - ρ) * (1 - β * q)) by ring,
      show (1 - ρ) * (1 - β * q) * (1 - om) = (1 - om) * ((1 - ρ) * (1 - β * q)) by ring,
      mul_div_mul_right _ _ hne]
  have := hc.tendsto
  rwa [hv] at this

/-- Cochrane (2023), p. 131 and Fig. 5.4: **the AR(1) impact tends to the permanent-rise impact**
`(ρ/λ₁ − ω̃)/(1 − ω̃)` (`LongTermDebt.ltd_perm_rise` at `t = 0`) as the persistence `η → 1⁻`. -/
theorem tendsto_impact_one {σ β κ ρ om : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hom0 : 0 ≤ om) (hom1 : om < 1) :
    Tendsto (impactRHS σ β κ ρ om) (𝓝[<] 1)
      (𝓝 ((ρ * (lam1 σ β κ)⁻¹ - om) / (1 - om))) := by
  obtain ⟨hq0, hq1, hβq⟩ := q_facts hσ hκ hβ
  refine ((factor_tendsto_one hρ1 hβq hom1).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (lt_mem_nhds (by norm_num :
    (0 : ℝ) < 1))] with η hη1 hη0
  have hη1' : η < 1 := hη1
  rw [impactRHS_eq_factor hσ hκ hβ (by nlinarith) (by nlinarith) (by nlinarith)]

/-- Cochrane (2023), §5.3, p. 131 ("the interest-rate rise must be persistent"), `ρ < β`:
**persistence is needed** for some maturity structures: there is `0 ≤ ω̃ < 1` for which a
one-period (`η = 0`) rise does not lower inflation on impact while every sufficiently persistent
AR(1) rise does. -/
theorem persistence_needed {σ β κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρβ : ρ < β) (hρ1 : ρ < 1) :
    ∃ om, 0 ≤ om ∧ om < 1 ∧ 0 ≤ impactRHS σ β κ ρ om 0 ∧
      ∀ᶠ η in 𝓝[<] 1, impactRHS σ β κ ρ om η < 0 := by
  obtain ⟨hq0, hq1, hβq⟩ := q_facts hσ hκ hβ
  set q := (lam1 σ β κ)⁻¹ with hqdef
  have hanti := omStar_strictAntiOn hq0 hq1 hρ0 hρ1 hβq hρβ
  have h01 : omStar ρ β q 1 < omStar ρ β q 0 :=
    hanti ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_lt_one
  rw [omStar_one hρ1 hβq] at h01
  have hρq1 : ρ * q < 1 := by nlinarith
  set om := min ((ρ * q + omStar ρ β q 0) / 2) ((ρ * q + 1) / 2) with homdef
  have hom_gt : ρ * q < om := lt_min (by linarith) (by linarith)
  have hom_le : om ≤ omStar ρ β q 0 := (min_le_left _ _).trans (by linarith)
  have hom1 : om < 1 := (min_le_right _ _).trans_lt (by linarith)
  have hρq0 : 0 < ρ * q := by positivity
  have hom0 : 0 ≤ om := by linarith
  refine ⟨om, hom0, hom1, ?_, ?_⟩
  · by_contra hc
    push Not at hc
    have := (impact_neg_iff_omStar hσ hκ hβ hρ0 hρ1 hom0 hom1 le_rfl zero_lt_one).1 hc
    linarith
  · have ht := tendsto_impact_one hσ hκ hβ hρ0 hρ1 hom0 hom1
    have hneg : (ρ * q - om) / (1 - om) < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
    exact ht.eventually (gt_mem_nhds hneg)

/-- Cochrane (2023), §5.3, p. 131, **counterexample for `ρ > β`** to "the interest-rate rise must be
persistent" and "a shock believed to be long-lasting is most likely to be disinflationary": with
`ω̃ = ρ/λ₁`, every AR(1) rise of persistence `η ∈ [0, 1)` lowers inflation on impact, the impact
is exactly `(1 − η)ρq(1 − q)(β − ρ)/((1 − ρη)(1 − βqη)(1 − ρqη))`, it rises to `0` as `η → 1`
(the permanent rise has impact `(ρq − ω̃)/(1 − ω̃) = 0`), and so it is not antitone in `η`. -/
theorem rho_gt_beta_reversal {σ β κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hβρ : β < ρ) (hρ1 : ρ < 1) :
    let q := (lam1 σ β κ)⁻¹
    (∀ η, 0 ≤ η → η < 1 → impactRHS σ β κ ρ (ρ * q) η =
        (1 - η) * (ρ * q * (1 - q) * (β - ρ)) /
          ((1 - ρ * η) * (1 - β * q * η) * (1 - ρ * q * η)) ∧
        impactRHS σ β κ ρ (ρ * q) η < 0) ∧
      (ρ * q - ρ * q) / (1 - ρ * q) = 0 ∧
      Tendsto (impactRHS σ β κ ρ (ρ * q)) (𝓝[<] 1) (𝓝 0) ∧
      ¬ AntitoneOn (impactRHS σ β κ ρ (ρ * q)) (Set.Ico 0 1) := by
  intro q
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨hq0, hq1, hβq⟩ := q_facts hσ hκ hβ
  have hρq1 : ρ * q < 1 := by nlinarith
  have hom0 : 0 ≤ ρ * q := by positivity
  have hval : ∀ η, 0 ≤ η → η < 1 → impactRHS σ β κ ρ (ρ * q) η =
      (1 - η) * (ρ * q * (1 - q) * (β - ρ)) /
        ((1 - ρ * η) * (1 - β * q * η) * (1 - ρ * q * η)) := by
    intro η h0 h1
    rw [impactRHS_eq_factor hσ hκ hβ (by nlinarith) (by nlinarith) (by nlinarith)]
    congr 1
    unfold pP pQ
    ring
  have hneg : ∀ η, 0 ≤ η → η < 1 → impactRHS σ β κ ρ (ρ * q) η < 0 := by
    intro η h0 h1
    rw [hval η h0 h1]
    have hD : 0 < (1 - ρ * η) * (1 - β * q * η) * (1 - ρ * q * η) := by
      have : 0 < 1 - ρ * η := by nlinarith
      have : 0 < 1 - β * q * η := by nlinarith
      have : 0 < 1 - ρ * q * η := by nlinarith
      positivity
    refine div_neg_of_neg_of_pos ?_ hD
    refine mul_neg_of_pos_of_neg (by linarith) ?_
    have h1q : 0 < 1 - q := by linarith
    exact mul_neg_of_pos_of_neg (by positivity) (by linarith)
  have hlim : Tendsto (impactRHS σ β κ ρ (ρ * q)) (𝓝[<] 1) (𝓝 0) := by
    have := tendsto_impact_one hσ hκ hβ hρ0 hρ1 hom0 hρq1
    rwa [sub_self, zero_div] at this
  refine ⟨fun η h0 h1 => ⟨hval η h0 h1, hneg η h0 h1⟩, by simp, hlim, fun hanti => ?_⟩
  have h0 := hneg 0 le_rfl zero_lt_one
  have hev : ∀ᶠ η in 𝓝[<] 1, impactRHS σ β κ ρ (ρ * q) 0 < impactRHS σ β κ ρ (ρ * q) η :=
    hlim.eventually (lt_mem_nhds h0)
  have hev2 : ∀ᶠ η in 𝓝[<] (1 : ℝ), 0 < η :=
    nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨η, h1, h2, h3⟩ := (hev.and (hev2.and self_mem_nhdsWithin)).exists
  have := hanti ⟨le_rfl, zero_lt_one⟩ ⟨h2.le, h3⟩ h2.le
  linarith

/-- Cochrane (2023), §5.3, p. 131 and §5.2, Fig. 5.4, the counterexample **for the equilibria**
(`ρ > β`, `ω̃ = ρ/λ₁`): every equilibrium after an AR(1) rise `i_t = ηᵗ`, `0 ≤ η < 1`, has
impact `π₁ < 0` (the book's date 1, Lean index `π 0`), while every equilibrium after the
permanent rise has impact `π₁ = 0`. -/
theorem rho_gt_beta_reversal_eqm {σ β κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hβρ : β < ρ) (hρ1 : ρ < 1) :
    (∀ η, 0 ≤ η → η < 1 → ∀ x π v q rn,
      LTD 𝔼 σ β κ ρ (ρ * (lam1 σ β κ)⁻¹) (fun t _ => η ^ t) (fun _ _ => 0) 0 0 x π v q rn →
      𝔼.Adapted q → BoundedProc π → BoundedProc v → BoundedProc q → ∀ ω, π 0 ω < 0) ∧
    (∀ x π v q rn,
      LTD 𝔼 σ β κ ρ (ρ * (lam1 σ β κ)⁻¹) (fun _ _ => 1) (fun _ _ => 0) 0 0 x π v q rn →
      𝔼.Adapted q → BoundedProc π → BoundedProc v → BoundedProc q → ∀ ω, π 0 ω = 0) := by
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨hq0, hq1, -⟩ := q_facts hσ hκ hβ
  have hρq1 : ρ * (lam1 σ β κ)⁻¹ < 1 := by nlinarith
  have hom0 : 0 ≤ ρ * (lam1 σ β κ)⁻¹ := by positivity
  constructor
  · intro η h0 h1 x π v q rn h hqa hπb hvb hqb ω
    rw [eqm_impact 𝔼 hσ hκ hβ hρ0 hρ1 hom0 hρq1 h0 h1 h hqa hπb hvb hqb ω]
    exact ((rho_gt_beta_reversal hσ hκ hβ hβρ hρ1).1 η h0 h1).2
  · intro x π v q rn h hqa hπb hvb hqb ω
    rw [(ltd_perm_rise 𝔼 hσ hκ hβ hρ0 hρ1 hom0 hρq1 h hqa hπb hvb hqb 0 ω).2.1]
    have : 1 - ρ * (lam1 σ β κ)⁻¹ ≠ 0 := by linarith
    rw [pow_zero, mul_one, div_self this, sub_self]

end Cochrane.StickyPriceFiscal.TidyR5Persistence
