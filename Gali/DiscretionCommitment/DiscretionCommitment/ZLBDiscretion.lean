/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Mul

/-!
# Optimal discretionary policy under a zero lower bound

Galí (2015), Section 5.4 and Subsection 5.4.1, pp. 144–148.

The economy is deterministic (perfect foresight after the date-0 surprise), so all paths are
plain sequences `ℕ → ℝ`. The non-policy block is the Phillips curve (29) and the dynamic IS
equation (30); the nominal rate obeys the zero lower bound (28). The natural rate (p. 145) is
`−η` on `[0, t_Z]` and `ρ > 0` afterwards. The book calls the drop `ǫ`; we write `η` because
`ε` is the elasticity of substitution in `ϑ = κ / ε` on the same pages (correction C5-5).

## Main results

* `firstBest_rate`, `firstBest_violates_zlb`, `firstBest_eqm_of_nonneg`: the first best
  `x = π = 0` needs `i = rⁿ`, which the ZLB rules out while `rⁿ < 0` (p. 145).
* `periodKKT_sufficient`, `periodKKT_necessary`, `periodOptimal_iff_kkt`: the KKT conditions
  (31)–(33) are necessary and sufficient for the per-period problem;
  `periodOptimal_iff_sol`, `periodOptimal_exists`, `periodOptimal_unique`: its unique solution
  is `x = min υ₁ (−κ υ₀ / (κ² + ϑ))`.
* `zlb_iff_le_ups1`, `periodKKT_iff_book`, `eq33`: (32) is (28) + (30), and the KKT system in the
  book's form with `ξ₂ i = 0`.
* `eq34_matrix`, `eq34_iff`: the binding-ZLB system (34) with the matrices `A`, `B`.
* `Amat_pos`, `Bvec_pos`, `backState_neg`: the sign lemma — `A`, `B` entrywise positive, hence
  `x_t < 0`, `π_t < 0` on `[0, t_Z]`, so `ξ₂,t > 0` (p. 147).
* `disc_exists`: the path of p. 147 (`i = 0`, (34) on `[0, t_Z]`; `i = ρ`, `x = π = 0` after)
  is a discretionary equilibrium. `disc_unique`: it is the only discretionary equilibrium in
  which `(x, π)` converges to the target `(0, 0)`.
* `deflation_discEq`, `deflation_bounded`, `deflation_ne_disc`: correction — boundedness alone
  does not give uniqueness. The deflationary steady state `π = −ρ`, `i = 0` after `t_Z` (glued
  to the binding phase) is another bounded discretionary equilibrium, so the book's "from
  `t_Z + 1` onward `i_t = ρ`" (p. 146) is a selection (footnote 10's rule), not an implication.
-/

namespace Gali.DiscretionCommitment.ZLBDiscretion

/-! ## The setup, eqs. (28)–(30) -/

/-- Galí (2015), p. 145: the natural rate path, `−η` for `t ≤ t_Z` and `ρ` afterwards (the book's
drop `ǫ` is renamed `η`, C5-5). -/
noncomputable def natRate (ρ η : ℝ) (tZ t : ℕ) : ℝ := if t ≤ tZ then -η else ρ

/-- Galí (2015), p. 145: the natural rate on the shock interval. -/
theorem natRate_of_le {ρ η : ℝ} {tZ t : ℕ} (ht : t ≤ tZ) : natRate ρ η tZ t = -η := by
  simp [natRate, ht]

/-- Galí (2015), p. 145: the natural rate after the shock interval. -/
theorem natRate_of_lt {ρ η : ℝ} {tZ t : ℕ} (ht : tZ < t) : natRate ρ η tZ t = ρ := by
  simp [natRate, Nat.not_le.mpr ht]

/-- Galí (2015), eq. (29), p. 145: the (deterministic) New Keynesian Phillips curve. -/
def NKPC (β κ : ℝ) (x π : ℕ → ℝ) (t : ℕ) : Prop := π t = β * π (t + 1) + κ * x t

/-- Galí (2015), eq. (30), p. 145: the dynamic IS equation. -/
def DIS (σ : ℝ) (rn x π i : ℕ → ℝ) (t : ℕ) : Prop :=
  x t = x (t + 1) - (1 / σ) * (i t - π (t + 1) - rn t)

/-- Galí (2015), p. 152: the nominal rate implied by the dynamic IS equation,
`i_t = rⁿ_t + π_{t+1} + σ (x_{t+1} − x_t)`. -/
noncomputable def impliedRate (σ : ℝ) (rn x π : ℕ → ℝ) (t : ℕ) : ℝ :=
  rn t + π (t + 1) + σ * (x (t + 1) - x t)

/-- Galí (2015), eq. (30) and p. 152: the dynamic IS equation pins down the nominal rate. -/
theorem dis_iff {σ : ℝ} (hσ : σ ≠ 0) {rn x π i : ℕ → ℝ} {t : ℕ} :
    DIS σ rn x π i t ↔ i t = impliedRate σ rn x π t := by
  unfold DIS impliedRate
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- Galí (2015), p. 145: the first best `x = π = 0` satisfies the IS equation only with
`i_t = rⁿ_t`. -/
theorem firstBest_rate {σ : ℝ} (hσ : σ ≠ 0) {rn i : ℕ → ℝ} {t : ℕ}
    (h : DIS σ rn (fun _ => 0) (fun _ => 0) i t) : i t = rn t := by
  rw [dis_iff hσ] at h
  simp [h, impliedRate]

/-- Galí (2015), p. 145: the ZLB rules out the first best while the natural rate is negative. -/
theorem firstBest_violates_zlb {σ ρ η : ℝ} (hσ : σ ≠ 0) (hη : 0 < η) {tZ t : ℕ} (ht : t ≤ tZ)
    {i : ℕ → ℝ} :
    ¬ (DIS σ (natRate ρ η tZ) (fun _ => 0) (fun _ => 0) i t ∧ 0 ≤ i t) := by
  rintro ⟨h, hi⟩
  have := firstBest_rate hσ h
  rw [natRate_of_le ht] at this
  linarith

/-- Galí (2015), p. 145 (and Ch. 4): whenever `rⁿ_t ≥ 0`, the first best with `i_t = rⁿ_t` solves
(29), (30) and the ZLB (28). -/
theorem firstBest_eqm_of_nonneg {β κ σ : ℝ} (hσ : σ ≠ 0) {rn : ℕ → ℝ} {t : ℕ}
    (h : 0 ≤ rn t) :
    NKPC β κ (fun _ => 0) (fun _ => 0) t ∧ DIS σ rn (fun _ => 0) (fun _ => 0) rn t ∧
      0 ≤ rn t := by
  refine ⟨by simp [NKPC], ?_, h⟩
  rw [dis_iff hσ]
  simp [impliedRate]

/-! ## The per-period problem (31)–(33) -/

/-- Galí (2015), eqs. (31)–(32), p. 146: feasibility in the per-period problem,
`π = κ x + υ₀` and `x ≤ υ₁`. -/
def PeriodFeasible (κ υ0 υ1 x π : ℝ) : Prop := π = κ * x + υ0 ∧ x ≤ υ1

/-- Galí (2015), p. 146: `(x, π)` minimises `π² + ϑ x²` subject to (31)–(32). -/
def PeriodOptimal (κ ϑ υ0 υ1 x π : ℝ) : Prop :=
  PeriodFeasible κ υ0 υ1 x π ∧
    ∀ x' π', PeriodFeasible κ υ0 υ1 x' π' → π ^ 2 + ϑ * x ^ 2 ≤ π' ^ 2 + ϑ * x' ^ 2

/-- Galí (2015), p. 146: the KKT system of the per-period problem — feasibility, the two
first-order conditions `π + ξ₁ = 0`, `ϑ x − κ ξ₁ + ξ₂ = 0`, `ξ₂ ≥ 0` and slackness. -/
def PeriodKKT (κ ϑ υ0 υ1 x π ξ1 ξ2 : ℝ) : Prop :=
  PeriodFeasible κ υ0 υ1 x π ∧ π + ξ1 = 0 ∧ ϑ * x - κ * ξ1 + ξ2 = 0 ∧ 0 ≤ ξ2 ∧
    ξ2 * (υ1 - x) = 0

/-- Galí (2015), p. 146: the loss change along the constraint line,
`(κ x' + υ₀)² + ϑ x'² − (κ x + υ₀)² − ϑ x² = 2 h c + h² (κ² + ϑ)` with `h = x' − x`,
`c = κ π + ϑ x`. -/
theorem period_loss_change (κ ϑ υ0 x x' : ℝ) :
    (κ * x' + υ0) ^ 2 + ϑ * x' ^ 2 - ((κ * x + υ0) ^ 2 + ϑ * x ^ 2) =
      2 * (x' - x) * (κ * (κ * x + υ0) + ϑ * x) + (x' - x) ^ 2 * (κ ^ 2 + ϑ) := by
  ring

/-- Galí (2015), (31)–(33), p. 146: SUFFICIENCY of the KKT conditions for the per-period
problem (convexity of the loss, linearity of the constraints). -/
theorem periodKKT_sufficient {κ ϑ υ0 υ1 x π ξ1 ξ2 : ℝ} (hϑ : 0 ≤ ϑ)
    (h : PeriodKKT κ ϑ υ0 υ1 x π ξ1 ξ2) : PeriodOptimal κ ϑ υ0 υ1 x π := by
  obtain ⟨⟨hπ, hx⟩, h1, h2, h3, h4⟩ := h
  refine ⟨⟨hπ, hx⟩, fun x' π' hf => ?_⟩
  obtain ⟨hπ', hx'⟩ := hf
  have e1 : ξ1 = -π := by linarith
  have e2 : ξ2 = κ * ξ1 - ϑ * x := by linarith
  subst hπ hπ' e1
  rw [e2] at h3 h4
  have key := period_loss_change κ ϑ υ0 x x'
  have hle : 0 ≤ (κ * -(κ * x + υ0) - ϑ * x) * (υ1 - x') :=
    mul_nonneg h3 (by linarith)
  nlinarith [sq_nonneg (x' - x), mul_nonneg (sq_nonneg (x' - x)) hϑ]

/-- Galí (2015), (31)–(33), p. 146: NECESSITY of the KKT conditions for the per-period problem,
with multipliers `ξ₁ = −π`, `ξ₂ = −(κ π + ϑ x)`. -/
theorem periodKKT_necessary {κ ϑ υ0 υ1 x π : ℝ} (hϑ : 0 < ϑ)
    (h : PeriodOptimal κ ϑ υ0 υ1 x π) :
    PeriodKKT κ ϑ υ0 υ1 x π (-π) (-(κ * π + ϑ * x)) := by
  obtain ⟨⟨hπ, hx⟩, hopt⟩ := h
  have hD : 0 < κ ^ 2 + ϑ := by positivity
  subst hπ
  set c := κ * (κ * x + υ0) + ϑ * x with hc
  -- `c ≤ 0`: otherwise lowering `x` reduces the loss
  have hc0 : c ≤ 0 := by
    by_contra hneg
    push Not at hneg
    have hfe : PeriodFeasible κ υ0 υ1 (x - c / (κ ^ 2 + ϑ)) (κ * (x - c / (κ ^ 2 + ϑ)) + υ0) :=
      ⟨rfl, by have : 0 < c / (κ ^ 2 + ϑ) := div_pos hneg hD; linarith⟩
    have h1 := hopt _ _ hfe
    have h2 := period_loss_change κ ϑ υ0 x (x - c / (κ ^ 2 + ϑ))
    rw [← hc] at h2
    have h3 : 2 * (x - c / (κ ^ 2 + ϑ) - x) * c + (x - c / (κ ^ 2 + ϑ) - x) ^ 2 * (κ ^ 2 + ϑ)
        = -(c ^ 2 / (κ ^ 2 + ϑ)) := by
      field_simp
      ring
    have h4 : 0 < c ^ 2 / (κ ^ 2 + ϑ) := div_pos (by positivity) hD
    linarith
  -- slackness: if `x < υ₁` and `c < 0`, raising `x` reduces the loss
  have hslack : -c * (υ1 - x) = 0 := by
    rcases eq_or_lt_of_le hx with hxe | hxl
    · rw [hxe]; ring
    rcases eq_or_lt_of_le hc0 with hce | hcl
    · rw [hce]; ring
    exfalso
    set hstep := min (υ1 - x) (-c / (κ ^ 2 + ϑ)) with hhs
    have hpos : 0 < hstep := lt_min (by linarith) (div_pos (by linarith) hD)
    have hle1 : hstep ≤ υ1 - x := min_le_left _ _
    have hle2 : hstep ≤ -c / (κ ^ 2 + ϑ) := min_le_right _ _
    have hle2' : hstep * (κ ^ 2 + ϑ) ≤ -c := by
      rwa [le_div_iff₀ hD] at hle2
    have hfe : PeriodFeasible κ υ0 υ1 (x + hstep) (κ * (x + hstep) + υ0) :=
      ⟨rfl, by linarith⟩
    have h1 := hopt _ _ hfe
    have h2 := period_loss_change κ ϑ υ0 x (x + hstep)
    rw [← hc] at h2
    have h5 : hstep * (2 * c + hstep * (κ ^ 2 + ϑ)) < 0 :=
      mul_neg_of_pos_of_neg hpos (by linarith)
    nlinarith
  refine ⟨⟨rfl, hx⟩, by ring, by ring, by linarith, by linarith⟩

/-- Galí (2015), (31)–(33), p. 146: the KKT conditions are necessary and sufficient. -/
theorem periodOptimal_iff_kkt {κ ϑ υ0 υ1 x π : ℝ} (hϑ : 0 < ϑ) :
    PeriodOptimal κ ϑ υ0 υ1 x π ↔ ∃ ξ1 ξ2, PeriodKKT κ ϑ υ0 υ1 x π ξ1 ξ2 :=
  ⟨fun h => ⟨_, _, periodKKT_necessary hϑ h⟩,
    fun ⟨_, _, h⟩ => periodKKT_sufficient hϑ.le h⟩

/-- Galí (2015), p. 146: the explicit solution of the per-period problem,
`x = min υ₁ (−κ υ₀ / (κ² + ϑ))` (the unconstrained optimum, capped by the ZLB). -/
noncomputable def periodSol (κ ϑ υ0 υ1 : ℝ) : ℝ := min υ1 (-(κ * υ0) / (κ ^ 2 + ϑ))

/-- Galí (2015), p. 146: `(x, π)` solves the per-period problem iff `x = periodSol` and
`π = κ x + υ₀`. -/
theorem periodOptimal_iff_sol {κ ϑ υ0 υ1 x π : ℝ} (hϑ : 0 < ϑ) :
    PeriodOptimal κ ϑ υ0 υ1 x π ↔ x = periodSol κ ϑ υ0 υ1 ∧ π = κ * x + υ0 := by
  have hD : 0 < κ ^ 2 + ϑ := by positivity
  constructor
  · intro h
    obtain ⟨⟨hπ, hx⟩, -, -, h3, h4⟩ := periodKKT_necessary hϑ h
    refine ⟨?_, hπ⟩
    subst hπ
    have hxle : x ≤ -(κ * υ0) / (κ ^ 2 + ϑ) := by
      rw [le_div_iff₀ hD]; nlinarith
    rcases mul_eq_zero.mp h4 with h5 | h5
    · have hxe : x = -(κ * υ0) / (κ ^ 2 + ϑ) := by
        field_simp; linarith
      unfold periodSol
      rw [min_eq_right (hxe ▸ hx)]
      exact hxe
    · have hxe : x = υ1 := by linarith
      unfold periodSol
      rw [min_eq_left (hxe ▸ hxle)]
      exact hxe
  · rintro ⟨hx, hπ⟩
    refine periodKKT_sufficient hϑ.le (ξ1 := -π) (ξ2 := -(κ * π + ϑ * x)) ?_
    have hle1 : x ≤ υ1 := hx ▸ min_le_left _ _
    have hle2 : x ≤ -(κ * υ0) / (κ ^ 2 + ϑ) := hx ▸ min_le_right _ _
    rw [le_div_iff₀ hD] at hle2
    refine ⟨⟨hπ, hle1⟩, by ring, by ring, by rw [hπ]; nlinarith, ?_⟩
    unfold periodSol at hx
    rcases le_total υ1 (-(κ * υ0) / (κ ^ 2 + ϑ)) with hm | hm
    · rw [min_eq_left hm] at hx
      rw [hx]; ring
    · rw [min_eq_right hm] at hx
      have : κ * π + ϑ * x = 0 := by
        rw [hπ, hx]; field_simp; ring
      rw [this]; ring

/-- Galí (2015), p. 146: the per-period problem has a solution. -/
theorem periodOptimal_exists {κ ϑ : ℝ} (hϑ : 0 < ϑ) (υ0 υ1 : ℝ) :
    PeriodOptimal κ ϑ υ0 υ1 (periodSol κ ϑ υ0 υ1) (κ * periodSol κ ϑ υ0 υ1 + υ0) :=
  (periodOptimal_iff_sol hϑ).mpr ⟨rfl, rfl⟩

/-- Galí (2015), p. 146: the solution of the per-period problem is unique. -/
theorem periodOptimal_unique {κ ϑ υ0 υ1 x π x' π' : ℝ} (hϑ : 0 < ϑ)
    (h : PeriodOptimal κ ϑ υ0 υ1 x π) (h' : PeriodOptimal κ ϑ υ0 υ1 x' π') :
    x = x' ∧ π = π' := by
  rw [periodOptimal_iff_sol hϑ] at h h'
  obtain ⟨hx, hπ⟩ := h
  obtain ⟨hx', hπ'⟩ := h'
  refine ⟨hx.trans hx'.symm, ?_⟩
  rw [hπ, hπ', hx, hx']

/-! ## The per-period problem inside the model -/

/-- Galí (2015), p. 146: `υ₀,t ≡ β π_{t+1}`. -/
def ups0 (β : ℝ) (π : ℕ → ℝ) (t : ℕ) : ℝ := β * π (t + 1)

/-- Galí (2015), p. 146: `υ₁,t ≡ x_{t+1} + (1/σ)(π_{t+1} + rⁿ_t)`. -/
noncomputable def ups1 (σ : ℝ) (rn x π : ℕ → ℝ) (t : ℕ) : ℝ :=
  x (t + 1) + (π (t + 1) + rn t) / σ

/-- Galí (2015), p. 146: the implied rate is `σ (υ₁,t − x_t)`. -/
theorem impliedRate_eq {σ : ℝ} (hσ : σ ≠ 0) (rn x π : ℕ → ℝ) (t : ℕ) :
    impliedRate σ rn x π t = σ * (ups1 σ rn x π t - x t) := by
  unfold impliedRate ups1
  field_simp
  ring

/-- Galí (2015), eq. (31), p. 146: the Phillips curve (29) is (31) with `υ₀,t = β π_{t+1}`. -/
theorem nkpc_iff_eq31 {β κ : ℝ} {x π : ℕ → ℝ} {t : ℕ} :
    NKPC β κ x π t ↔ π t = κ * x t + ups0 β π t := by
  unfold NKPC ups0
  constructor <;> intro h <;> linarith

/-- Galí (2015), eq. (32), p. 146: given the IS equation (30), the ZLB (28) is `x_t ≤ υ₁,t`. -/
theorem zlb_iff_le_ups1 {σ : ℝ} (hσ : 0 < σ) {rn x π i : ℕ → ℝ} {t : ℕ}
    (hD : DIS σ rn x π i t) : 0 ≤ i t ↔ x t ≤ ups1 σ rn x π t := by
  rw [dis_iff hσ.ne', impliedRate_eq hσ.ne'] at hD
  rw [hD]
  constructor
  · intro h
    have := (mul_nonneg_iff_of_pos_left hσ).mp h
    linarith
  · intro h
    exact mul_nonneg hσ.le (by linarith)

/-- Galí (2015), p. 146: given (30), the KKT system of the per-period problem is the book's
system — the FOCs, `ξ₂ ≥ 0`, `i ≥ 0`, `ξ₂ i = 0` — together with (29). -/
theorem periodKKT_iff_book {β κ σ ϑ : ℝ} (hσ : 0 < σ) {rn x π i : ℕ → ℝ} {t : ℕ}
    (hD : DIS σ rn x π i t) (ξ1 ξ2 : ℝ) :
    PeriodKKT κ ϑ (ups0 β π t) (ups1 σ rn x π t) (x t) (π t) ξ1 ξ2 ↔
      (NKPC β κ x π t ∧ π t + ξ1 = 0 ∧ ϑ * x t - κ * ξ1 + ξ2 = 0 ∧ 0 ≤ ξ2 ∧ 0 ≤ i t ∧
        ξ2 * i t = 0) := by
  have hi : i t = σ * (ups1 σ rn x π t - x t) := by
    rw [dis_iff hσ.ne', impliedRate_eq hσ.ne'] at hD; exact hD
  have hz := zlb_iff_le_ups1 hσ hD
  unfold PeriodKKT PeriodFeasible
  rw [← nkpc_iff_eq31, hz]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2, h3, h4, h5⟩
    refine ⟨h0, h2, h3, h4, h1, ?_⟩
    rw [hi, mul_left_comm, h5, mul_zero]
  · rintro ⟨h0, h2, h3, h4, h1, h5⟩
    refine ⟨⟨h0, h1⟩, h2, h3, h4, ?_⟩
    rw [hi, mul_left_comm] at h5
    rcases mul_eq_zero.mp h5 with h | h
    · exact absurd h hσ.ne'
    · exact h

/-- Galí (2015), eq. (33), p. 146: the two first-order conditions combine to
`ϑ x_t = −κ π_t − ξ₂,t`. -/
theorem eq33 {κ ϑ x π ξ1 ξ2 : ℝ} (h1 : π + ξ1 = 0) (h2 : ϑ * x - κ * ξ1 + ξ2 = 0) :
    ϑ * x = -κ * π - ξ2 := by
  have : ξ1 = -π := by linarith
  subst this
  linarith

/-- Galí (2015), p. 146: a discretionary equilibrium under the ZLB — at every date the IS
equation (30) holds and `(x_t, π_t)` solves the per-period problem (31)–(32), taking
`υ₀,t, υ₁,t` (i.e. the future path) as given. -/
def DiscEq (β κ σ ϑ : ℝ) (rn x π i : ℕ → ℝ) : Prop :=
  ∀ t, DIS σ rn x π i t ∧ PeriodOptimal κ ϑ (ups0 β π t) (ups1 σ rn x π t) (x t) (π t)

/-- Galí (2015), pp. 145–146: a discretionary equilibrium satisfies (29) and the ZLB (28). -/
theorem DiscEq.nkpc_zlb {β κ σ ϑ : ℝ} (hσ : 0 < σ) {rn x π i : ℕ → ℝ}
    (h : DiscEq β κ σ ϑ rn x π i) (t : ℕ) : NKPC β κ x π t ∧ 0 ≤ i t := by
  obtain ⟨hD, ⟨h1, h2⟩, -⟩ := h t
  exact ⟨nkpc_iff_eq31.mpr h1, (zlb_iff_le_ups1 hσ hD).mpr h2⟩


/-- Galí (2015), p. 146: at a date where the ZLB binds (`x_t = υ₁,t`, i.e. `i_t = 0`) and the
Phillips curve holds, `κ π_t + ϑ x_t ≤ 0` (i.e. `ξ₂,t ≥ 0` in (33)) makes `(x_t, π_t)` optimal. -/
theorem binding_optimal {β κ σ ϑ : ℝ} (hϑ : 0 ≤ ϑ) {rn x π : ℕ → ℝ} {t : ℕ}
    (hb : x t = ups1 σ rn x π t) (hN : NKPC β κ x π t) (hs : κ * π t + ϑ * x t ≤ 0) :
    PeriodOptimal κ ϑ (ups0 β π t) (ups1 σ rn x π t) (x t) (π t) := by
  refine periodKKT_sufficient hϑ (ξ1 := -π t) (ξ2 := -(κ * π t + ϑ * x t)) ?_
  refine ⟨⟨nkpc_iff_eq31.mp hN, hb.le⟩, by ring, by ring, by linarith, ?_⟩
  rw [← hb]; ring

/-- Galí (2015), pp. 146–147: if `x_{t+1} = π_{t+1} = 0` and `rⁿ_t ≥ 0`, then `x_t = π_t = 0`
solves the per-period problem (the first best, with `i_t = rⁿ_t`). -/
theorem slack_zero_optimal {β κ σ ϑ : ℝ} (hσ : 0 < σ) (hϑ : 0 ≤ ϑ) {rn x π : ℕ → ℝ} {t : ℕ}
    (hx : x t = 0) (hπ : π t = 0) (hx1 : x (t + 1) = 0) (hπ1 : π (t + 1) = 0)
    (hr : 0 ≤ rn t) :
    PeriodOptimal κ ϑ (ups0 β π t) (ups1 σ rn x π t) (x t) (π t) := by
  refine periodKKT_sufficient hϑ (ξ1 := 0) (ξ2 := 0) ?_
  unfold ups0 ups1
  rw [hx, hπ, hx1, hπ1]
  refine ⟨⟨by ring, ?_⟩, by ring, by ring, le_rfl, by ring⟩
  simp only [zero_add]
  exact div_nonneg hr hσ.le

/-! ## The binding-ZLB system (34) -/

/-- Galí (2015), eq. (34), p. 147: one backward step of the binding-ZLB system,
`(x_t, π_t) = A (x_{t+1}, π_{t+1}) − B η`. -/
noncomputable def backStep (β κ σ η : ℝ) (s : ℝ × ℝ) : ℝ × ℝ :=
  (s.1 + s.2 / σ - η / σ, κ * s.1 + (β + κ / σ) * s.2 - κ * η / σ)

/-- Galí (2015), eq. (34), p. 147: `n` backward steps from the terminal state `s_T`. -/
noncomputable def backState (β κ σ η : ℝ) (sT : ℝ × ℝ) : ℕ → ℝ × ℝ
  | 0 => sT
  | n + 1 => backStep β κ σ η (backState β κ σ η sT n)

/-- Galí (2015), p. 147: the matrix `A ≡ [1, 1/σ; κ, β + κ/σ]`. -/
noncomputable def Amat (β κ σ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1 / σ; κ, β + κ / σ]

/-- Galí (2015), p. 147: the vector `B ≡ [1/σ; κ/σ]`. -/
noncomputable def Bvec (κ σ : ℝ) : Fin 2 → ℝ := ![1 / σ, κ / σ]

/-- Galí (2015), eq. (34), p. 147: `backStep` is the matrix recursion `A s − B η`. -/
theorem eq34_matrix (β κ σ η : ℝ) (s : ℝ × ℝ) :
    ![(backStep β κ σ η s).1, (backStep β κ σ η s).2] =
      Matrix.mulVec (Amat β κ σ) ![s.1, s.2] - η • Bvec κ σ := by
  ext j
  fin_cases j <;>
    simp [backStep, Amat, Bvec] <;> ring

/-- Galí (2015), eq. (34), p. 147: on `[0, t_Z]`, the Phillips curve (29) and the IS equation
(30) with `i_t = 0` are exactly the backward system (34). -/
theorem eq34_iff {β κ σ η ρ : ℝ} (hσ : σ ≠ 0) {tZ t : ℕ} (ht : t ≤ tZ) {x π i : ℕ → ℝ} :
    (NKPC β κ x π t ∧ DIS σ (natRate ρ η tZ) x π i t ∧ i t = 0) ↔
      (i t = 0 ∧ (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1))) := by
  rw [dis_iff hσ]
  unfold NKPC impliedRate backStep
  rw [natRate_of_le ht, Prod.ext_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hx : x t = x (t + 1) + π (t + 1) / σ - η / σ := by
      rw [h3] at h2
      field_simp
      linarith
    refine ⟨h3, hx, ?_⟩
    simp only
    rw [h1, hx]
    ring
  · rintro ⟨h3, hx, hπ⟩
    simp only at hx hπ
    refine ⟨?_, ?_, h3⟩
    · rw [hπ, hx]; ring
    · rw [h3, hx]; field_simp; ring

/-- Galí (2015), p. 147: the entries of `A` are positive. -/
theorem Amat_pos {β κ σ : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (i j : Fin 2) :
    0 < Amat β κ σ i j := by
  fin_cases i <;> fin_cases j
  · change (0 : ℝ) < 1; exact one_pos
  · change (0 : ℝ) < 1 / σ; positivity
  · change (0 : ℝ) < κ; exact hκ
  · change (0 : ℝ) < β + κ / σ; positivity

/-- Galí (2015), p. 147: the entries of `B` are positive. -/
theorem Bvec_pos {κ σ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (i : Fin 2) : 0 < Bvec κ σ i := by
  fin_cases i
  · change (0 : ℝ) < 1 / σ; positivity
  · change (0 : ℝ) < κ / σ; positivity

/-- Galí (2015), p. 147: the sign lemma, one step — with `A, B` entrywise positive and
`η > 0`, a nonpositive `(x_{t+1}, π_{t+1})` gives a strictly negative `(x_t, π_t)`. -/
theorem backStep_neg {β κ σ η : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (hη : 0 < η)
    {s : ℝ × ℝ} (h1 : s.1 ≤ 0) (h2 : s.2 ≤ 0) :
    (backStep β κ σ η s).1 < 0 ∧ (backStep β κ σ η s).2 < 0 := by
  unfold backStep
  have a1 : s.2 / σ ≤ 0 := div_nonpos_iff.mpr (Or.inr ⟨h2, hσ.le⟩)
  have a2 : 0 < η / σ := div_pos hη hσ
  have a3 : κ * s.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hκ.le h1
  have a4 : (β + κ / σ) * s.2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h2
  have a5 : 0 < κ * η / σ := by positivity
  exact ⟨by simp only; linarith, by simp only; linarith⟩

/-- Galí (2015), p. 147: the sign lemma — from a nonpositive terminal state, every backward
iterate of (34) is nonpositive. -/
theorem backState_nonpos {β κ σ η : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (hη : 0 < η)
    {sT : ℝ × ℝ} (h1 : sT.1 ≤ 0) (h2 : sT.2 ≤ 0) (n : ℕ) :
    (backState β κ σ η sT n).1 ≤ 0 ∧ (backState β κ σ η sT n).2 ≤ 0 := by
  induction n with
  | zero => exact ⟨h1, h2⟩
  | succ n ih =>
    have := backStep_neg hβ hκ hσ hη ih.1 ih.2
    exact ⟨this.1.le, this.2.le⟩

/-- Galí (2015), p. 147: the sign lemma — from a nonpositive terminal state (e.g. `0`), every
backward iterate of (34) is strictly negative. -/
theorem backState_neg {β κ σ η : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (hη : 0 < η)
    {sT : ℝ × ℝ} (h1 : sT.1 ≤ 0) (h2 : sT.2 ≤ 0) (n : ℕ) :
    (backState β κ σ η sT (n + 1)).1 < 0 ∧ (backState β κ σ η sT (n + 1)).2 < 0 := by
  have := backState_nonpos hβ hκ hσ hη h1 h2 n
  exact backStep_neg hβ hκ hσ hη this.1 this.2

/-- Galí (2015), p. 147: the path solving (34) backward on `[0, t_Z]` from the terminal state
`s_T` at `t_Z + 1`, and equal to `s_T` after `t_Z`. -/
noncomputable def zlbPath (β κ σ η : ℝ) (tZ : ℕ) (sT : ℝ × ℝ) (t : ℕ) : ℝ × ℝ :=
  if t ≤ tZ then backState β κ σ η sT (tZ + 1 - t) else sT

/-- Galí (2015), eq. (34), p. 147: on `[0, t_Z]` the path obeys (34). -/
theorem zlbPath_of_le {β κ σ η : ℝ} {tZ t : ℕ} {sT : ℝ × ℝ} (ht : t ≤ tZ) :
    zlbPath β κ σ η tZ sT t = backStep β κ σ η (zlbPath β κ σ η tZ sT (t + 1)) := by
  unfold zlbPath
  have e : tZ + 1 - t = (tZ + 1 - (t + 1)) + 1 := by omega
  simp only [ht, ↓reduceIte, e, backState]
  by_cases h : t + 1 ≤ tZ
  · simp only [h, ↓reduceIte]
  · have e2 : tZ + 1 - (t + 1) = 0 := by omega
    simp only [h, ↓reduceIte, e2, backState]

/-- Galí (2015), p. 147: after `t_Z` the path is at its terminal state. -/
theorem zlbPath_of_lt {β κ σ η : ℝ} {tZ t : ℕ} {sT : ℝ × ℝ} (ht : tZ < t) :
    zlbPath β κ σ η tZ sT t = sT := by
  simp [zlbPath, Nat.not_le.mpr ht]

/-- Galí (2015), p. 147: from a nonpositive terminal state the path is strictly negative on
`[0, t_Z]`. -/
theorem zlbPath_neg {β κ σ η : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (hη : 0 < η)
    {tZ t : ℕ} {sT : ℝ × ℝ} (h1 : sT.1 ≤ 0) (h2 : sT.2 ≤ 0) (ht : t ≤ tZ) :
    (zlbPath β κ σ η tZ sT t).1 < 0 ∧ (zlbPath β κ σ η tZ sT t).2 < 0 := by
  unfold zlbPath
  have e : tZ + 1 - t = (tZ - t) + 1 := by omega
  simp only [ht, ↓reduceIte, e]
  exact backState_neg hβ hκ hσ hη h1 h2 _

/-- Galí (2015), pp. 146–147: the glued path is a discretionary equilibrium on `[0, t_Z]`, with
`i_t = 0` there, whenever its terminal state is nonpositive. -/
theorem zlbPath_binding {β κ σ ϑ ρ η : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hη : 0 < η) {tZ t : ℕ} {sT : ℝ × ℝ} (h1 : sT.1 ≤ 0) (h2 : sT.2 ≤ 0)
    (ht : t ≤ tZ) :
    PeriodOptimal κ ϑ (ups0 β (fun s => (zlbPath β κ σ η tZ sT s).2) t)
        (ups1 σ (natRate ρ η tZ) (fun s => (zlbPath β κ σ η tZ sT s).1)
          (fun s => (zlbPath β κ σ η tZ sT s).2) t)
        (zlbPath β κ σ η tZ sT t).1 (zlbPath β κ σ η tZ sT t).2 ∧
      impliedRate σ (natRate ρ η tZ) (fun s => (zlbPath β κ σ η tZ sT s).1)
        (fun s => (zlbPath β κ σ η tZ sT s).2) t = 0 := by
  have hstep := zlbPath_of_le (β := β) (κ := κ) (σ := σ) (η := η) (sT := sT) ht
  have hneg := zlbPath_neg hβ hκ hσ hη h1 h2 ht
  have hx : (zlbPath β κ σ η tZ sT t).1 =
      (zlbPath β κ σ η tZ sT (t + 1)).1 + (zlbPath β κ σ η tZ sT (t + 1)).2 / σ - η / σ := by
    rw [hstep]; rfl
  have hπ : (zlbPath β κ σ η tZ sT t).2 = κ * (zlbPath β κ σ η tZ sT (t + 1)).1 +
      (β + κ / σ) * (zlbPath β κ σ η tZ sT (t + 1)).2 - κ * η / σ := by
    rw [hstep]; rfl
  constructor
  · refine binding_optimal hϑ.le ?_ ?_ ?_
    · simp only [ups1, natRate_of_le ht]
      rw [hx]; ring
    · simp only [NKPC]
      rw [hπ, hx]; ring
    · nlinarith [hneg.1, hneg.2]
  · simp only [impliedRate, natRate_of_le ht]
    rw [hx]; field_simp; ring

/-! ## Existence and uniqueness of the discretionary equilibrium -/

/-- Galí (2015), p. 147: the discretionary output gap (34) on `[0, t_Z]`, `0` afterwards. -/
noncomputable def discX (β κ σ η : ℝ) (tZ t : ℕ) : ℝ := (zlbPath β κ σ η tZ (0, 0) t).1

/-- Galí (2015), p. 147: the discretionary inflation path (34) on `[0, t_Z]`, `0` afterwards. -/
noncomputable def discPi (β κ σ η : ℝ) (tZ t : ℕ) : ℝ := (zlbPath β κ σ η tZ (0, 0) t).2

/-- Galí (2015), pp. 146–147: the discretionary nominal rate, from the IS equation. -/
noncomputable def discI (β κ σ ρ η : ℝ) (tZ : ℕ) : ℕ → ℝ :=
  impliedRate σ (natRate ρ η tZ) (discX β κ σ η tZ) (discPi β κ σ η tZ)

/-- Galí (2015), pp. 146–147: EXISTENCE — the path of p. 147 is a discretionary equilibrium
under the ZLB. On `[0, t_Z]`: `i_t = 0`, `x_t < 0`, `π_t < 0`, and `ξ₂,t = −(κ π_t + ϑ x_t) > 0`
(consistent with a binding ZLB); after `t_Z`: `x_t = π_t = 0` and `i_t = ρ`. -/
theorem disc_exists {β κ σ ϑ ρ η : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (hϑ : 0 < ϑ)
    (hρ : 0 < ρ) (hη : 0 < η) (tZ : ℕ) :
    DiscEq β κ σ ϑ (natRate ρ η tZ) (discX β κ σ η tZ) (discPi β κ σ η tZ)
        (discI β κ σ ρ η tZ) ∧
      (∀ t, t ≤ tZ → discX β κ σ η tZ t < 0 ∧ discPi β κ σ η tZ t < 0 ∧
        discI β κ σ ρ η tZ t = 0 ∧
        0 < -(κ * discPi β κ σ η tZ t + ϑ * discX β κ σ η tZ t)) ∧
      (∀ t, tZ < t → discX β κ σ η tZ t = 0 ∧ discPi β κ σ η tZ t = 0 ∧
        discI β κ σ ρ η tZ t = ρ) := by
  have hafter : ∀ t, tZ < t → discX β κ σ η tZ t = 0 ∧ discPi β κ σ η tZ t = 0 := by
    intro t ht
    simp [discX, discPi, zlbPath_of_lt ht]
  have hbind := fun t (ht : t ≤ tZ) =>
    zlbPath_binding (ϑ := ϑ) (ρ := ρ) hβ hκ hσ hϑ hη (sT := (0, 0)) le_rfl le_rfl ht
  refine ⟨fun t => ⟨(dis_iff hσ.ne').mpr rfl, ?_⟩, fun t ht => ?_, fun t ht => ?_⟩
  · rcases le_or_gt t tZ with ht | ht
    · exact (hbind t ht).1
    · exact slack_zero_optimal hσ hϑ.le (hafter t ht).1 (hafter t ht).2
        (hafter (t + 1) (by omega)).1 (hafter (t + 1) (by omega)).2
        (by rw [natRate_of_lt ht]; exact hρ.le)
  · have hneg := zlbPath_neg hβ hκ hσ hη (sT := (0, 0)) le_rfl le_rfl ht
    refine ⟨hneg.1, hneg.2, (hbind t ht).2, ?_⟩
    have := mul_neg_of_pos_of_neg hκ hneg.2
    have := mul_neg_of_pos_of_neg hϑ hneg.1
    simp only [discX, discPi]
    linarith
  · refine ⟨(hafter t ht).1, (hafter t ht).2, ?_⟩
    simp only [discI, impliedRate, natRate_of_lt ht, (hafter t ht).1,
      (hafter (t + 1) (by omega)).1, (hafter (t + 1) (by omega)).2]
    ring

/-- Galí (2015), p. 147: backward induction — a property holding from some date `N` on and
propagating from `t + 1` to `t` holds at every date. -/
theorem down_induction {P : ℕ → Prop} (N : ℕ) (hN : ∀ t, N ≤ t → P t)
    (hstep : ∀ t, P (t + 1) → P t) (t : ℕ) : P t := by
  have key : ∀ n t, N ≤ t + n → P t := by
    intro n
    induction n with
    | zero => intro t ht; exact hN t (by omega)
    | succ n ih => intro t ht; exact hstep t (ih (t + 1) (by omega))
  exact key N t (by omega)

/-- Galí (2015), pp. 146–147: UNIQUENESS — the path of p. 147 is the only discretionary
equilibrium under the ZLB in which `(x_t, π_t)` converges to the target `(0, 0)`.
(Convergence cannot be weakened to boundedness: see `deflation_discEq`.) -/
theorem disc_unique {β κ σ ϑ ρ η : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hρ : 0 < ρ) (hη : 0 < η) {tZ : ℕ} {x π i : ℕ → ℝ}
    (h : DiscEq β κ σ ϑ (natRate ρ η tZ) x π i)
    (hx : Filter.Tendsto x Filter.atTop (nhds 0)) (hπ : Filter.Tendsto π Filter.atTop (nhds 0)) :
    x = discX β κ σ η tZ ∧ π = discPi β κ σ η tZ ∧ i = discI β κ σ ρ η tZ := by
  have hD : 0 < κ ^ 2 + ϑ := by positivity
  set lam := β * ϑ / (κ ^ 2 + ϑ) with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hlam1 : lam < 1 := by
    rw [hlam, div_lt_one hD]
    nlinarith [sq_pos_of_pos hκ]
  -- Step A: eventually the ZLB is slack
  have hlim : Filter.Tendsto (fun t => x (t + 1) + (π (t + 1) + ρ) / σ +
      κ * (β * π (t + 1)) / (κ ^ 2 + ϑ)) Filter.atTop (nhds (0 + (0 + ρ) / σ + κ * (β * 0) /
        (κ ^ 2 + ϑ))) := by
    have hx1 := hx.comp (Filter.tendsto_add_atTop_nat 1)
    have hπ1 := hπ.comp (Filter.tendsto_add_atTop_nat 1)
    refine ((hx1.add ((hπ1.add_const ρ).div_const σ)).add
      (((hπ1.const_mul β).const_mul κ).div_const _))
  have hpos : (0 : ℝ) < 0 + (0 + ρ) / σ + κ * (β * 0) / (κ ^ 2 + ϑ) := by
    simp only [zero_add, mul_zero, zero_div, add_zero]
    exact div_pos hρ hσ
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (hlim.eventually (lt_mem_nhds hpos))
  set N := max T (tZ + 1) with hN
  have hslack : ∀ t, N ≤ t → x t = -(κ * (β * π (t + 1))) / (κ ^ 2 + ϑ) ∧
      π t = lam * π (t + 1) := by
    intro t ht
    have htT : T ≤ t := le_trans (le_max_left _ _) ht
    have htZ : tZ < t := by have := le_max_right T (tZ + 1); omega
    have hlt := hT t htT
    obtain ⟨hxs, hπs⟩ := (periodOptimal_iff_sol hϑ).mp (h t).2
    have hlt' : -(κ * ups0 β π t) / (κ ^ 2 + ϑ) < ups1 σ (natRate ρ η tZ) x π t := by
      simp only [ups0, ups1, natRate_of_lt htZ]
      have : -(κ * (β * π (t + 1))) / (κ ^ 2 + ϑ) =
          -(κ * (β * π (t + 1)) / (κ ^ 2 + ϑ)) := by ring
      linarith
    have hxe : x t = -(κ * (β * π (t + 1))) / (κ ^ 2 + ϑ) := by
      rw [hxs, periodSol, min_eq_right hlt'.le]; rfl
    refine ⟨hxe, ?_⟩
    rw [hπs, hxe, hlam, ups0]
    field_simp
    ring
  -- Step B: from `N` on, `π = 0` and `x = 0`
  have hiter : ∀ t, N ≤ t → ∀ k, π t = lam ^ k * π (k + t) := by
    intro t ht k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih, (hslack (k + t) (by omega)).2, pow_succ]
      have : k + t + 1 = k + 1 + t := by omega
      rw [this]; ring
  have hzero : ∀ t, N ≤ t → π t = 0 := by
    intro t ht
    have h0 : Filter.Tendsto (fun k => lam ^ k * π (k + t)) Filter.atTop (nhds (0 * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0 hlam1).mul
        (hπ.comp (Filter.tendsto_add_atTop_nat t))
    rw [mul_zero] at h0
    have h1 : Filter.Tendsto (fun _ : ℕ => π t) Filter.atTop (nhds 0) :=
      h0.congr (fun k => (hiter t ht k).symm)
    exact tendsto_const_nhds_iff.mp h1
  -- Step C: backward induction from `N`
  obtain ⟨hDE, -, hafter⟩ := disc_exists (ϑ := ϑ) hβ hκ hσ hϑ hρ hη tZ
  have hall : ∀ t, x t = discX β κ σ η tZ t ∧ π t = discPi β κ σ η tZ t := by
    refine down_induction N (fun t ht => ?_) (fun t ih => ?_)
    · have htZ : tZ < t := by have := le_max_right T (tZ + 1); omega
      refine ⟨?_, ?_⟩
      · rw [(hslack t ht).1, hzero (t + 1) (by omega), (hafter t htZ).1]; ring
      · rw [hzero t ht, (hafter t htZ).2.1]
    · have e0 : ups0 β π t = ups0 β (discPi β κ σ η tZ) t := by
        simp only [ups0, ih.2]
      have e1 : ups1 σ (natRate ρ η tZ) x π t =
          ups1 σ (natRate ρ η tZ) (discX β κ σ η tZ) (discPi β κ σ η tZ) t := by
        simp only [ups1, ih.1, ih.2]
      have h1 := (h t).2
      rw [e0, e1] at h1
      exact periodOptimal_unique hϑ h1 (hDE t).2
  have hxe : x = discX β κ σ η tZ := funext fun t => (hall t).1
  have hπe : π = discPi β κ σ η tZ := funext fun t => (hall t).2
  refine ⟨hxe, hπe, funext fun t => ?_⟩
  rw [(dis_iff hσ.ne').mp (h t).1, discI, hxe, hπe]

/-! ## Correction: boundedness alone does not give uniqueness -/

/-- Galí (2015), p. 146 (correction): the deflationary steady-state output gap
`x̄ = −(1 − β) ρ / κ`, at which `π = −ρ` and `i = 0` forever. -/
noncomputable def deflGap (β κ ρ : ℝ) : ℝ := -((1 - β) * ρ / κ)

/-- Galí (2015), p. 146 (correction): the deflationary path — (34) on `[0, t_Z]` glued to the
deflationary steady state `(x̄, −ρ)` after `t_Z`. -/
noncomputable def deflPath (β κ σ ρ η : ℝ) (tZ t : ℕ) : ℝ × ℝ :=
  zlbPath β κ σ η tZ (deflGap β κ ρ, -ρ) t

/-- Galí (2015), p. 146 (correction): the nominal rate along the deflationary path. -/
noncomputable def deflI (β κ σ ρ η : ℝ) (tZ : ℕ) : ℕ → ℝ :=
  impliedRate σ (natRate ρ η tZ) (fun t => (deflPath β κ σ ρ η tZ t).1)
    (fun t => (deflPath β κ σ ρ η tZ t).2)

/-- Galí (2015), pp. 146–147 (correction): the deflationary path is ALSO a discretionary
equilibrium under the ZLB, with `i_t = 0` at every date and `π_t = −ρ` after `t_Z`. -/
theorem deflation_discEq {β κ σ ϑ ρ η : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) (hη : 0 < η) (tZ : ℕ) :
    DiscEq β κ σ ϑ (natRate ρ η tZ) (fun t => (deflPath β κ σ ρ η tZ t).1)
        (fun t => (deflPath β κ σ ρ η tZ t).2) (deflI β κ σ ρ η tZ) ∧
      (∀ t, deflI β κ σ ρ η tZ t = 0) ∧
      (∀ t, tZ < t → (deflPath β κ σ ρ η tZ t).2 = -ρ) := by
  have hg : deflGap β κ ρ ≤ 0 := by
    unfold deflGap
    have : 0 ≤ (1 - β) * ρ / κ := div_nonneg (mul_nonneg (by linarith) hρ.le) hκ.le
    linarith
  have hafter : ∀ t, tZ < t → deflPath β κ σ ρ η tZ t = (deflGap β κ ρ, -ρ) :=
    fun t ht => zlbPath_of_lt ht
  have hbind := fun t (ht : t ≤ tZ) =>
    zlbPath_binding (ϑ := ϑ) (ρ := ρ) hβ hκ hσ hϑ hη (sT := (deflGap β κ ρ, -ρ)) hg
      (by simp only; linarith) ht
  have hi_after : ∀ t, tZ < t → deflI β κ σ ρ η tZ t = 0 := by
    intro t ht
    simp only [deflI, impliedRate, natRate_of_lt ht, hafter t ht, hafter (t + 1) (by omega)]
    ring
  refine ⟨fun t => ⟨(dis_iff hσ.ne').mpr rfl, ?_⟩, fun t => ?_, fun t ht => by
    rw [hafter t ht]⟩
  · rcases le_or_gt t tZ with ht | ht
    · exact (hbind t ht).1
    · refine binding_optimal hϑ.le ?_ ?_ ?_
      · simp only [ups1, natRate_of_lt ht, hafter t ht, hafter (t + 1) (by omega)]
        ring
      · simp only [NKPC, hafter t ht, hafter (t + 1) (by omega), deflGap]
        field_simp
        ring
      · simp only [hafter t ht]
        nlinarith
  · rcases le_or_gt t tZ with ht | ht
    · exact (hbind t ht).2
    · exact hi_after t ht

/-- Galí (2015), p. 146 (correction): the deflationary path is bounded. -/
theorem deflation_bounded (β κ σ ρ η : ℝ) (tZ : ℕ) :
    ∃ C, ∀ t, |(deflPath β κ σ ρ η tZ t).1| ≤ C ∧ |(deflPath β κ σ ρ η tZ t).2| ≤ C := by
  refine ⟨∑ s ∈ Finset.range (tZ + 1),
      (|(deflPath β κ σ ρ η tZ s).1| + |(deflPath β κ σ ρ η tZ s).2|) +
      (|deflGap β κ ρ| + |ρ|), fun t => ?_⟩
  have hS : 0 ≤ ∑ s ∈ Finset.range (tZ + 1),
      (|(deflPath β κ σ ρ η tZ s).1| + |(deflPath β κ σ ρ η tZ s).2|) :=
    Finset.sum_nonneg fun _ _ => by positivity
  rcases le_or_gt t tZ with ht | ht
  · have hle := Finset.single_le_sum
      (f := fun s => |(deflPath β κ σ ρ η tZ s).1| + |(deflPath β κ σ ρ η tZ s).2|)
      (fun _ _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))
    have a1 := abs_nonneg (deflPath β κ σ ρ η tZ t).1
    have a2 := abs_nonneg (deflPath β κ σ ρ η tZ t).2
    have a3 := abs_nonneg (deflGap β κ ρ)
    have a4 := abs_nonneg ρ
    constructor <;> linarith
  · have e : deflPath β κ σ ρ η tZ t = (deflGap β κ ρ, -ρ) := zlbPath_of_lt ht
    rw [e]
    have a3 := abs_nonneg (deflGap β κ ρ)
    have a4 := abs_nonneg ρ
    simp only [abs_neg]
    constructor <;> linarith

/-- Galí (2015), p. 146 (correction): the deflationary equilibrium differs from the path of
p. 147 (inflation at `t_Z + 1` is `−ρ ≠ 0`). Hence uniqueness among BOUNDED paths fails; the
book's "from `t_Z + 1` onward `i_t = ρ`" selects the target steady state. -/
theorem deflation_ne_disc {β κ σ ρ η : ℝ} (hρ : 0 < ρ) (tZ : ℕ) :
    (fun t => (deflPath β κ σ ρ η tZ t).2) ≠ discPi β κ σ η tZ := by
  intro h
  have := congrFun h (tZ + 1)
  simp only [deflPath, discPi, zlbPath_of_lt (Nat.lt_succ_self tZ)] at this
  linarith

end Gali.DiscretionCommitment.ZLBDiscretion
