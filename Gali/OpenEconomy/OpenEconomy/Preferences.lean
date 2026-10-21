/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Preferences of the small open economy: home-bias CES over home and foreign goods

Galí (2015), Chapter 8, §8.1.1, pp. 225–228: eqs. (2), (4), (5), the expenditure identity
`P_H C_H + P_F C_F = P C` (p. 227) and footnotes 1 and 2.

The consumption index (2) is `C = ((1−υ)^{1/η} C_H^{(η−1)/η} + υ^{1/η} C_F^{(η−1)/η})^{η/(η−1)}`
with openness `0 < υ < 1` and elasticity `η > 0`, `η ≠ 1`; the CPI is
`P = ((1−υ) P_H^{1−η} + υ P_F^{1−η})^{1/(1−η)}`.

## Main results

* `rpow_tangent_le`, `rpow_tangent_eq_iff`: the tangent-line inequality
  `(u^r − 1)/r ≤ u − 1` for `r < 1`, `r ≠ 0` (weighted AM–GM), strict unless `u = 1`.
  This one inequality covers both `η > 1` (`0 < r < 1`) and `η < 1` (`r < 0`).
* `expenditure_ge`, `expenditure_eq_iff`: eq. (5) as expenditure minimisation — every bundle
  costs at least `P · C` (its own index `C`), with equality **iff** it is on the demand
  schedules (5). For `η > 1` zero quantities are allowed (`expenditure_ge_of_one_lt`,
  `expenditure_eq_iff_of_one_lt`).
* `cesIndex_demand`, `expenditure_demand`: the demands (5) deliver `C` and cost exactly
  `P C` (p. 227).
* `cpi_isLeast`: the CPI is the least cost of one unit of the index; `cesIndex_le_of_spend`.
* `importShare`: the import share is `υ (P_F/P)^{1−η}`, equal to `υ` when `η = 1` or
  `P_H = P_F` (p. 226).
* `cesIndex_tendsto_cd` (fn. 1): as `η → 1` the index tends to
  `C_H^{1−υ} C_F^υ / ((1−υ)^{1−υ} υ^υ)`; `cpi_tendsto_cd` (fn. 2): the CPI tends to
  `P_H^{1−υ} P_F^υ`.
* `expenditureCD_ge`, `expenditureCD_eq_iff`, `cesIndexCD_demand`, `expenditureCD_demand`
  (fn. 2): at `η = 1`, with the fn-1 normalisation, `P_H^{1−υ}P_F^υ` is exactly the unit cost
  and the demands are (5) with `η = 1`.
* `Variety` (eq. (4), p. 226): Dixit–Stiglitz demand over domestic varieties on `[0, 1]`,
  restated from the Chapter 3 project, and `two_stage_expenditure`:
  `∫ P_H(i) C_H(i) di + P_F C_F = P C`.
-/

namespace Gali.OpenEconomy.Preferences

open Filter Topology

/-! ### The tangent-line inequality for `u ↦ u^r` -/

/-- Galí (2015), (5), p. 226 (the inequality behind expenditure minimisation): for `r < 1`,
`r ≠ 0` and `u ≥ 0` (with `u > 0` when `r < 0`), `(u^r − 1)/r ≤ u − 1`. -/
theorem rpow_tangent_le {r u : ℝ} (hr1 : r < 1) (hr0 : r ≠ 0) (hu : 0 ≤ u)
    (hu' : 0 < r ∨ 0 < u) : (u ^ r - 1) / r ≤ u - 1 := by
  rcases lt_or_gt_of_ne hr0 with hneg | hpos
  · have hu0 : 0 < u := hu'.resolve_left (not_lt.2 hneg.le)
    have h1r : 0 < 1 - r := by linarith
    have hw1 : 0 ≤ 1 / (1 - r) := by positivity
    have hw2 : 0 ≤ -r / (1 - r) := div_nonneg (by linarith) h1r.le
    have hw : 1 / (1 - r) + -r / (1 - r) = 1 := by field_simp; ring
    have h := Real.geom_mean_le_arith_mean2_weighted hw1 hw2 (Real.rpow_nonneg hu r) hu hw
    have hgm : (u ^ r) ^ (1 / (1 - r)) * u ^ (-r / (1 - r)) = 1 := by
      rw [← Real.rpow_mul hu, ← Real.rpow_add hu0]
      have : r * (1 / (1 - r)) + -r / (1 - r) = 0 := by field_simp; ring
      rw [this, Real.rpow_zero]
    have e : 1 / (1 - r) * u ^ r + -r / (1 - r) * u = (u ^ r - r * u) / (1 - r) := by
      field_simp
      ring
    rw [hgm, e, le_div_iff₀ h1r] at h
    rw [div_le_iff_of_neg hneg]
    nlinarith
  · have h1r : 0 ≤ 1 - r := by linarith
    have hw : r + (1 - r) = 1 := by ring
    have h := Real.geom_mean_le_arith_mean2_weighted hpos.le h1r hu zero_le_one hw
    rw [Real.one_rpow, mul_one, mul_one] at h
    rw [div_le_iff₀ hpos]
    nlinarith

/-- Galí (2015), (5), p. 226: equality in `rpow_tangent_le` holds iff `u = 1`. -/
theorem rpow_tangent_eq_iff {r u : ℝ} (hr1 : r < 1) (hr0 : r ≠ 0) (hu : 0 ≤ u)
    (hu' : 0 < r ∨ 0 < u) : (u ^ r - 1) / r = u - 1 ↔ u = 1 := by
  constructor
  swap
  · rintro rfl
    simp
  intro heq
  rcases lt_or_gt_of_ne hr0 with hneg | hpos
  · have hu0 : 0 < u := hu'.resolve_left (not_lt.2 hneg.le)
    have h1r : 0 < 1 - r := by linarith
    have hw1 : 0 < 1 / (1 - r) := by positivity
    have hw2 : 0 < -r / (1 - r) := div_pos (by linarith) h1r
    have hw : 1 / (1 - r) + -r / (1 - r) = 1 := by field_simp; ring
    have hiff := Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos hw1 hw2
      (Real.rpow_nonneg hu r) hu hw
    have hgm : (u ^ r) ^ (1 / (1 - r)) * u ^ (-r / (1 - r)) = 1 := by
      rw [← Real.rpow_mul hu, ← Real.rpow_add hu0]
      have : r * (1 / (1 - r)) + -r / (1 - r) = 0 := by field_simp; ring
      rw [this, Real.rpow_zero]
    have e : 1 / (1 - r) * u ^ r + -r / (1 - r) * u = (u ^ r - r * u) / (1 - r) := by
      field_simp
      ring
    rw [hgm, e] at hiff
    have h2 : u ^ r - r * u = 1 - r := by
      rw [div_eq_iff hneg.ne] at heq
      linarith
    have hur : u ^ r = u := hiff.1 (by rw [h2, div_self h1r.ne'])
    have hlog : r * Real.log u = Real.log u := by rw [← Real.log_rpow hu0, hur]
    have hl0 : Real.log u = 0 := by
      have : (r - 1) * Real.log u = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (by linarith)
      · exact h
    rcases Real.log_eq_zero.1 hl0 with h | h | h
    · rw [h] at hu0; exact absurd hu0 (lt_irrefl 0)
    · exact h
    · linarith
  · have h1r : 0 < 1 - r := by linarith
    have hw : r + (1 - r) = 1 := by ring
    have hiff := Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos hpos h1r hu zero_le_one hw
    rw [Real.one_rpow, mul_one, mul_one] at hiff
    refine hiff.1 ?_
    rw [div_eq_iff hpos.ne'] at heq
    linarith

/-- Galí (2015), (5), p. 226 (the aggregated tangent inequality): if positive weights
`ω₁ + ω₂ = 1` satisfy `ω₁ u^r + ω₂ v^r = 1`, then `ω₁ u + ω₂ v ≥ 1`, with equality iff
`u = v = 1`. -/
theorem weighted_tangent {r ω₁ ω₂ u v : ℝ} (hr1 : r < 1) (hr0 : r ≠ 0) (hω₁ : 0 < ω₁)
    (hω₂ : 0 < ω₂) (hω : ω₁ + ω₂ = 1) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huv : 0 < r ∨ (0 < u ∧ 0 < v)) (hc : ω₁ * u ^ r + ω₂ * v ^ r = 1) :
    1 ≤ ω₁ * u + ω₂ * v ∧ (ω₁ * u + ω₂ * v = 1 ↔ u = 1 ∧ v = 1) := by
  have hu' : 0 < r ∨ 0 < u := huv.imp_right And.left
  have hv' : 0 < r ∨ 0 < v := huv.imp_right And.right
  have h1 := rpow_tangent_le hr1 hr0 hu hu'
  have h2 := rpow_tangent_le hr1 hr0 hv hv'
  have hsum : ω₁ * ((u ^ r - 1) / r) + ω₂ * ((v ^ r - 1) / r) = 0 := by
    have : ω₁ * ((u ^ r - 1) / r) + ω₂ * ((v ^ r - 1) / r)
        = (ω₁ * u ^ r + ω₂ * v ^ r - (ω₁ + ω₂)) / r := by field_simp; ring
    rw [this, hc, hω, sub_self, zero_div]
  have k1 := mul_le_mul_of_nonneg_left h1 hω₁.le
  have k2 := mul_le_mul_of_nonneg_left h2 hω₂.le
  refine ⟨by nlinarith, ⟨fun heq => ?_, fun ⟨h1', h2'⟩ => by rw [h1', h2']; linarith⟩⟩
  have d1 : ω₁ * ((u - 1) - (u ^ r - 1) / r) = 0 := by nlinarith
  have d2 : ω₂ * ((v - 1) - (v ^ r - 1) / r) = 0 := by nlinarith
  rcases mul_eq_zero.1 d1 with h | h
  · exact absurd h hω₁.ne'
  rcases mul_eq_zero.1 d2 with h' | h'
  · exact absurd h' hω₂.ne'
  exact ⟨(rpow_tangent_eq_iff hr1 hr0 hu hu').1 (by linarith),
    (rpow_tangent_eq_iff hr1 hr0 hv hv').1 (by linarith)⟩

/-! ### The consumption index, the CPI and the demands (5) -/

/-- Galí (2015), eq. (2), p. 225: the home-bias CES consumption index
`C = ((1−υ)^{1/η} C_H^{(η−1)/η} + υ^{1/η} C_F^{(η−1)/η})^{η/(η−1)}` (for `η ≠ 1`). -/
noncomputable def cesIndex (υ η x y : ℝ) : ℝ :=
  ((1 - υ) ^ (1 / η) * x ^ ((η - 1) / η) + υ ^ (1 / η) * y ^ ((η - 1) / η)) ^ (η / (η - 1))

/-- Galí (2015), fn. 1, p. 225: the Cobb–Douglas index `C_H^{1−υ} C_F^υ/((1−υ)^{1−υ} υ^υ)`
(the `η = 1` case). -/
noncomputable def cesIndexCD (υ x y : ℝ) : ℝ :=
  x ^ (1 - υ) * y ^ υ / ((1 - υ) ^ (1 - υ) * υ ^ υ)

/-- Galí (2015), p. 226: the CPI `P = ((1−υ) P_H^{1−η} + υ P_F^{1−η})^{1/(1−η)}` (`η ≠ 1`). -/
noncomputable def cpi (υ η pH pF : ℝ) : ℝ :=
  ((1 - υ) * pH ^ (1 - η) + υ * pF ^ (1 - η)) ^ (1 / (1 - η))

/-- Galí (2015), fn. 2, p. 226: the CPI at `η = 1`, `P = P_H^{1−υ} P_F^υ`. -/
noncomputable def cpiCD (υ pH pF : ℝ) : ℝ := pH ^ (1 - υ) * pF ^ υ

/-- Galí (2015), eq. (5), p. 226: home-goods demand `C_H = (1−υ)(P_H/P)^{−η} C`. -/
noncomputable def homeDemand (υ η pH P C : ℝ) : ℝ := (1 - υ) * (pH / P) ^ (-η) * C

/-- Galí (2015), eq. (5), p. 226: imported-goods demand `C_F = υ(P_F/P)^{−η} C`. -/
noncomputable def foreignDemand (υ η pF P C : ℝ) : ℝ := υ * (pF / P) ^ (-η) * C

variable {υ η pH pF : ℝ}

/-- Galí (2015), p. 226: the CPI is positive. -/
theorem cpi_pos (hυ0 : 0 < υ) (hυ1 : υ < 1) (hpH : 0 < pH) (hpF : 0 < pF) :
    0 < cpi υ η pH pF := by
  unfold cpi
  have : 0 < 1 - υ := by linarith
  positivity

/-- Galí (2015), p. 226: `P^{1−η} = (1−υ) P_H^{1−η} + υ P_F^{1−η}`. -/
theorem cpi_rpow (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) (hpH : 0 < pH) (hpF : 0 < pF) :
    cpi υ η pH pF ^ (1 - η) = (1 - υ) * pH ^ (1 - η) + υ * pF ^ (1 - η) := by
  have : 0 < 1 - υ := by linarith
  unfold cpi
  rw [one_div]
  exact Real.rpow_inv_rpow (by positivity) (sub_ne_zero.2 (Ne.symm hη1))

/-- Galí (2015), p. 226: the expenditure shares sum to one,
`(1−υ)(P_H/P)^{1−η} + υ(P_F/P)^{1−η} = 1`. -/
theorem shares_sum (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) (hpH : 0 < pH) (hpF : 0 < pF) :
    (1 - υ) * (pH / cpi υ η pH pF) ^ (1 - η) + υ * (pF / cpi υ η pH pF) ^ (1 - η) = 1 := by
  have hP := cpi_pos (η := η) hυ0 hυ1 hpH hpF
  rw [Real.div_rpow hpH.le hP.le, Real.div_rpow hpF.le hP.le, cpi_rpow hυ0 hυ1 hη1 hpH hpF]
  have : 0 < (1 - υ) * pH ^ (1 - η) + υ * pF ^ (1 - η) := by
    have : 0 < 1 - υ := by linarith
    positivity
  field_simp

/-- Galí (2015), (5), p. 226: the CES term of a demand,
`a^{1/η} (a z^{−η} C)^{(η−1)/η} = a z^{1−η} C^{(η−1)/η}`. -/
theorem demand_term {a z C : ℝ} (hη : 0 < η) (ha : 0 < a) (hz : 0 < z) (hC : 0 ≤ C) :
    a ^ (1 / η) * (a * z ^ (-η) * C) ^ ((η - 1) / η)
      = a * z ^ (1 - η) * C ^ ((η - 1) / η) := by
  rw [Real.mul_rpow (by positivity) hC, Real.mul_rpow ha.le (by positivity),
    ← Real.rpow_mul hz.le]
  have e1 : -η * ((η - 1) / η) = 1 - η := by field_simp; ring
  rw [e1, ← mul_assoc, ← mul_assoc, ← Real.rpow_add ha]
  have e2 : 1 / η + (η - 1) / η = 1 := by field_simp; ring
  rw [e2, Real.rpow_one]

/-- Galí (2015), (5), p. 226: the cost of a demand, `p (a (p/P)^{−η} C) = a (p/P)^{1−η} P C`. -/
theorem spend_term {a p P C : ℝ} (hp : 0 < p) (hP : 0 < P) :
    p * (a * (p / P) ^ (-η) * C) = a * (p / P) ^ (1 - η) * (P * C) := by
  have hz : 0 < p / P := div_pos hp hP
  rw [sub_eq_add_neg, Real.rpow_add hz, Real.rpow_one]
  field_simp

/-- Galí (2015), p. 227: the demands (5) cost exactly `P_H C_H + P_F C_F = P C`. -/
theorem expenditure_demand (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) (hpH : 0 < pH)
    (hpF : 0 < pF) (C : ℝ) :
    pH * homeDemand υ η pH (cpi υ η pH pF) C + pF * foreignDemand υ η pF (cpi υ η pH pF) C
      = cpi υ η pH pF * C := by
  have hP := cpi_pos (η := η) hυ0 hυ1 hpH hpF
  unfold homeDemand foreignDemand
  rw [spend_term hpH hP, spend_term hpF hP, ← add_mul, shares_sum hυ0 hυ1 hη1 hpH hpF, one_mul]

/-- Galí (2015), eq. (2): `C^{(η−1)/η} = (1−υ)^{1/η} C_H^{(η−1)/η} + υ^{1/η} C_F^{(η−1)/η}`. -/
theorem cesIndex_rpow (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη : 0 < η) (hη1 : η ≠ 1) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    cesIndex υ η x y ^ ((η - 1) / η)
      = (1 - υ) ^ (1 / η) * x ^ ((η - 1) / η) + υ ^ (1 / η) * y ^ ((η - 1) / η) := by
  have : 0 < 1 - υ := by linarith
  unfold cesIndex
  rw [show η / (η - 1) = ((η - 1) / η)⁻¹ from (inv_div _ _).symm]
  exact Real.rpow_inv_rpow (by positivity)
    (div_ne_zero (sub_ne_zero.2 hη1) hη.ne')

/-- Galí (2015), eq. (5), p. 226: the demands (5) deliver exactly the index `C`. -/
theorem cesIndex_demand (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη : 0 < η) (hη1 : η ≠ 1)
    (hpH : 0 < pH) (hpF : 0 < pF) {C : ℝ} (hC : 0 ≤ C) :
    cesIndex υ η (homeDemand υ η pH (cpi υ η pH pF) C)
      (foreignDemand υ η pF (cpi υ η pH pF) C) = C := by
  have hP := cpi_pos (η := η) hυ0 hυ1 hpH hpF
  have h1υ : 0 < 1 - υ := by linarith
  unfold cesIndex homeDemand foreignDemand
  rw [demand_term hη h1υ (div_pos hpH hP) hC, demand_term hη hυ0 (div_pos hpF hP) hC,
    ← add_mul, shares_sum hυ0 hυ1 hη1 hpH hpF, one_mul,
    show η / (η - 1) = ((η - 1) / η)⁻¹ from (inv_div _ _).symm]
  exact Real.rpow_rpow_inv hC (div_ne_zero (sub_ne_zero.2 hη1) hη.ne')

/-- Galí (2015), (5): the index of a bundle with a positive quantity is positive. -/
theorem cesIndex_pos (hυ0 : 0 < υ) (hυ1 : υ < 1) {x y : ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hxy : 0 < x ∨ 0 < y) : 0 < cesIndex υ η x y := by
  have h1υ : 0 < 1 - υ := by linarith
  unfold cesIndex
  apply Real.rpow_pos_of_pos
  rcases hxy with h | h
  · have := Real.rpow_pos_of_pos h ((η - 1) / η)
    have := Real.rpow_nonneg hy ((η - 1) / η)
    positivity
  · have := Real.rpow_pos_of_pos h ((η - 1) / η)
    have := Real.rpow_nonneg hx ((η - 1) / η)
    positivity

/-- Galí (2015), eq. (5), p. 226 (core of expenditure minimisation): for a bundle with
positive index `C`, the expenditure is at least `P C`, with equality iff the bundle is the
demand schedule (5) at `C`. Quantities may be zero only when `η > 1`. -/
theorem expenditure_core (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη : 0 < η) (hη1 : η ≠ 1)
    (hpH : 0 < pH) (hpF : 0 < pF) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : 1 < η ∨ (0 < x ∧ 0 < y)) (hC : 0 < cesIndex υ η x y) :
    cpi υ η pH pF * cesIndex υ η x y ≤ pH * x + pF * y ∧
      (pH * x + pF * y = cpi υ η pH pF * cesIndex υ η x y ↔
        x = homeDemand υ η pH (cpi υ η pH pF) (cesIndex υ η x y) ∧
          y = foreignDemand υ η pF (cpi υ η pH pF) (cesIndex υ η x y)) := by
  set P := cpi υ η pH pF with hPdef
  set C := cesIndex υ η x y with hCdef
  have hP : 0 < P := cpi_pos hυ0 hυ1 hpH hpF
  have h1υ : 0 < 1 - υ := by linarith
  set r := (η - 1) / η with hr
  have hr1 : r < 1 := by rw [hr, div_lt_one hη]; linarith
  have hr0 : r ≠ 0 := div_ne_zero (sub_ne_zero.2 hη1) hη.ne'
  set zH := pH / P
  set zF := pF / P
  have hzH : 0 < zH := div_pos hpH hP
  have hzF : 0 < zF := div_pos hpF hP
  set DH := (1 - υ) * zH ^ (-η) * C with hDH
  set DF := υ * zF ^ (-η) * C with hDF
  have hDH0 : 0 < DH := by positivity
  have hDF0 : 0 < DF := by positivity
  set ω₁ := (1 - υ) * zH ^ (1 - η)
  set ω₂ := υ * zF ^ (1 - η)
  have hω₁ : 0 < ω₁ := by positivity
  have hω₂ : 0 < ω₂ := by positivity
  have hω : ω₁ + ω₂ = 1 := shares_sum hυ0 hυ1 hη1 hpH hpF
  set u := x / DH
  set v := y / DF
  have hu : 0 ≤ u := div_nonneg hx hDH0.le
  have hv : 0 ≤ v := div_nonneg hy hDF0.le
  have hxu : x = u * DH := (div_mul_cancel₀ x hDH0.ne').symm
  have hyv : y = v * DF := (div_mul_cancel₀ y hDF0.ne').symm
  have hCr : 0 < C ^ r := Real.rpow_pos_of_pos hC r
  have hc : ω₁ * u ^ r + ω₂ * v ^ r = 1 := by
    have h := cesIndex_rpow hυ0 hυ1 hη hη1 hx hy
    rw [← hCdef, ← hr] at h
    have t1 : (1 - υ) ^ (1 / η) * x ^ r = u ^ r * (ω₁ * C ^ r) := by
      rw [hxu, Real.mul_rpow hu hDH0.le, ← demand_term hη h1υ hzH hC.le]
      ring
    have t2 : υ ^ (1 / η) * y ^ r = v ^ r * (ω₂ * C ^ r) := by
      rw [hyv, Real.mul_rpow hv hDF0.le, ← demand_term hη hυ0 hzF hC.le]
      ring
    rw [t1, t2] at h
    have : C ^ r * (ω₁ * u ^ r + ω₂ * v ^ r) = C ^ r * 1 := by
      linear_combination (-1 : ℝ) * h
    exact mul_left_cancel₀ hCr.ne' this
  have huv : 0 < r ∨ (0 < u ∧ 0 < v) := by
    rcases hxy with h | ⟨h1, h2⟩
    · left; rw [hr]; exact div_pos (by linarith) hη
    · right; exact ⟨div_pos h1 hDH0, div_pos h2 hDF0⟩
  obtain ⟨hle, hiff⟩ := weighted_tangent hr1 hr0 hω₁ hω₂ hω hu hv huv hc
  have hspend : pH * x + pF * y = P * C * (ω₁ * u + ω₂ * v) := by
    rw [hxu, hyv]
    have s1 := spend_term (η := η) (a := 1 - υ) (C := C) hpH hP
    have s2 := spend_term (η := η) (a := υ) (C := C) hpF hP
    have e1 : pH * (u * DH) = u * (pH * ((1 - υ) * (pH / P) ^ (-η) * C)) := by
      rw [hDH]; ring
    have e2 : pF * (v * DF) = v * (pF * (υ * (pF / P) ^ (-η) * C)) := by
      rw [hDF]; ring
    rw [e1, e2, s1, s2]
    ring
  have hPC : 0 < P * C := mul_pos hP hC
  refine ⟨?_, ?_⟩
  · rw [hspend]
    nlinarith
  · rw [hspend]
    constructor
    · intro h
      have h1 : ω₁ * u + ω₂ * v = 1 := by
        have : P * C * (ω₁ * u + ω₂ * v) = P * C * 1 := by rw [h, mul_one]
        exact mul_left_cancel₀ hPC.ne' this
      obtain ⟨hu1, hv1⟩ := hiff.1 h1
      refine ⟨?_, ?_⟩
      · rw [hxu, hu1, one_mul]; rfl
      · rw [hyv, hv1, one_mul]; rfl
    · rintro ⟨h1, h2⟩
      have hu1 : u = 1 := by
        change x / DH = 1
        rw [div_eq_one_iff_eq hDH0.ne']
        exact h1
      have hv1 : v = 1 := by
        change y / DF = 1
        rw [div_eq_one_iff_eq hDF0.ne']
        exact h2
      rw [hiff.2 ⟨hu1, hv1⟩, mul_one]

/-- Galí (2015), eq. (5), p. 226 (**expenditure minimisation**): every bundle of positive
quantities costs at least `P · C`, where `C` is its own consumption index (2). -/
theorem expenditure_ge (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη : 0 < η) (hη1 : η ≠ 1)
    (hpH : 0 < pH) (hpF : 0 < pF) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    cpi υ η pH pF * cesIndex υ η x y ≤ pH * x + pF * y :=
  (expenditure_core hυ0 hυ1 hη hη1 hpH hpF hx.le hy.le (Or.inr ⟨hx, hy⟩)
    (cesIndex_pos hυ0 hυ1 hx.le hy.le (Or.inl hx))).1

/-- Galí (2015), eq. (5), p. 226: a bundle of positive quantities costs exactly `P · C` **iff**
it is the demand schedule `C_H = (1−υ)(P_H/P)^{−η} C`, `C_F = υ(P_F/P)^{−η} C`. -/
theorem expenditure_eq_iff (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη : 0 < η) (hη1 : η ≠ 1)
    (hpH : 0 < pH) (hpF : 0 < pF) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    pH * x + pF * y = cpi υ η pH pF * cesIndex υ η x y ↔
      x = homeDemand υ η pH (cpi υ η pH pF) (cesIndex υ η x y) ∧
        y = foreignDemand υ η pF (cpi υ η pH pF) (cesIndex υ η x y) :=
  (expenditure_core hυ0 hυ1 hη hη1 hpH hpF hx.le hy.le (Or.inr ⟨hx, hy⟩)
    (cesIndex_pos hυ0 hυ1 hx.le hy.le (Or.inl hx))).2

/-- Galí (2015), (2): with `η > 1` the empty bundle has index zero. -/
theorem cesIndex_zero (hη : 0 < η) (hη1 : 1 < η) : cesIndex υ η 0 0 = 0 := by
  have hr0 : (η - 1) / η ≠ 0 := div_ne_zero (by linarith) hη.ne'
  have he : η / (η - 1) ≠ 0 := div_ne_zero hη.ne' (by linarith)
  unfold cesIndex
  rw [Real.zero_rpow hr0, mul_zero, mul_zero, add_zero, Real.zero_rpow he]

/-- Galí (2015), eq. (5), p. 226, for `η > 1` with **nonnegative** quantities (zero
consumption of one good allowed): expenditure is at least `P · C`. -/
theorem expenditure_ge_of_one_lt (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : 1 < η)
    (hpH : 0 < pH) (hpF : 0 < pF) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    cpi υ η pH pF * cesIndex υ η x y ≤ pH * x + pF * y := by
  have hη : 0 < η := by linarith
  rcases hx.eq_or_lt with hx0 | hx0
  · rcases hy.eq_or_lt with hy0 | hy0
    · rw [← hx0, ← hy0, cesIndex_zero hη hη1]; simp
    · exact (expenditure_core hυ0 hυ1 hη hη1.ne' hpH hpF hx hy (Or.inl hη1)
        (cesIndex_pos hυ0 hυ1 hx hy (Or.inr hy0))).1
  · exact (expenditure_core hυ0 hυ1 hη hη1.ne' hpH hpF hx hy (Or.inl hη1)
      (cesIndex_pos hυ0 hυ1 hx hy (Or.inl hx0))).1

/-- Galí (2015), eq. (5), p. 226, for `η > 1` with nonnegative quantities: a bundle costs
exactly `P · C` iff it is the demand schedule (5). -/
theorem expenditure_eq_iff_of_one_lt (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : 1 < η)
    (hpH : 0 < pH) (hpF : 0 < pF) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    pH * x + pF * y = cpi υ η pH pF * cesIndex υ η x y ↔
      x = homeDemand υ η pH (cpi υ η pH pF) (cesIndex υ η x y) ∧
        y = foreignDemand υ η pF (cpi υ η pH pF) (cesIndex υ η x y) := by
  have hη : 0 < η := by linarith
  rcases hx.eq_or_lt with hx0 | hx0
  · rcases hy.eq_or_lt with hy0 | hy0
    · rw [← hx0, ← hy0, cesIndex_zero hη hη1]
      simp [homeDemand, foreignDemand]
    · exact (expenditure_core hυ0 hυ1 hη hη1.ne' hpH hpF hx hy (Or.inl hη1)
        (cesIndex_pos hυ0 hυ1 hx hy (Or.inr hy0))).2
  · exact (expenditure_core hυ0 hυ1 hη hη1.ne' hpH hpF hx hy (Or.inl hη1)
      (cesIndex_pos hυ0 hυ1 hx hy (Or.inl hx0))).2

/-- Galí (2015), p. 226: the demands (5) are positive. -/
theorem demands_pos (hυ0 : 0 < υ) (hυ1 : υ < 1) (hpH : 0 < pH) (hpF : 0 < pF) {C : ℝ}
    (hC : 0 < C) : 0 < homeDemand υ η pH (cpi υ η pH pF) C ∧
      0 < foreignDemand υ η pF (cpi υ η pH pF) C := by
  have hP := cpi_pos (η := η) hυ0 hυ1 hpH hpF
  have h1υ : 0 < 1 - υ := by linarith
  have := div_pos hpH hP
  have := div_pos hpF hP
  unfold homeDemand foreignDemand
  constructor <;> positivity

/-- Galí (2015), p. 226: **the CPI is the minimum cost of one unit of the consumption index**:
`P = min {P_H C_H + P_F C_F : C_H, C_F > 0, C(C_H, C_F) = 1}`. -/
theorem cpi_isLeast (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη : 0 < η) (hη1 : η ≠ 1)
    (hpH : 0 < pH) (hpF : 0 < pF) :
    IsLeast {e | ∃ x y, 0 < x ∧ 0 < y ∧ cesIndex υ η x y = 1 ∧ e = pH * x + pF * y}
      (cpi υ η pH pF) := by
  refine ⟨⟨homeDemand υ η pH (cpi υ η pH pF) 1, foreignDemand υ η pF (cpi υ η pH pF) 1,
    (demands_pos hυ0 hυ1 hpH hpF one_pos).1, (demands_pos hυ0 hυ1 hpH hpF one_pos).2,
    cesIndex_demand hυ0 hυ1 hη hη1 hpH hpF zero_le_one, ?_⟩, ?_⟩
  · rw [expenditure_demand hυ0 hυ1 hη1 hpH hpF, mul_one]
  · rintro e ⟨x, y, hx, hy, h1, rfl⟩
    have := expenditure_ge hυ0 hυ1 hη hη1 hpH hpF hx hy
    rwa [h1, mul_one] at this

/-- Galí (2015), (5) in dual form: with expenditure `X`, the attainable index is at most
`X / P`. -/
theorem cesIndex_le_of_spend (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη : 0 < η) (hη1 : η ≠ 1)
    (hpH : 0 < pH) (hpF : 0 < pF) {x y X : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hX : pH * x + pF * y = X) : cesIndex υ η x y ≤ X / cpi υ η pH pF := by
  rw [le_div_iff₀ (cpi_pos hυ0 hυ1 hpH hpF), mul_comm, ← hX]
  exact expenditure_ge hυ0 hυ1 hη hη1 hpH hpF hx hy

/-- Galí (2015), p. 226: the import expenditure share under (5) is `υ (P_F/P)^{1−η}`. -/
theorem importShare (hυ0 : 0 < υ) (hυ1 : υ < 1) (hpH : 0 < pH) (hpF : 0 < pF) {C : ℝ}
    (hC : 0 < C) :
    pF * foreignDemand υ η pF (cpi υ η pH pF) C / (cpi υ η pH pF * C)
      = υ * (pF / cpi υ η pH pF) ^ (1 - η) := by
  have hP := cpi_pos (η := η) hυ0 hυ1 hpH hpF
  unfold foreignDemand
  rw [spend_term hpF hP]
  field_simp

/-- Galí (2015), p. 226: when `P_H = P_F` (e.g. the symmetric steady state) the CPI equals
the common price and the import share is exactly `υ`. -/
theorem importShare_of_eq (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) (hpH : 0 < pH)
    {C : ℝ} (hC : 0 < C) :
    cpi υ η pH pH = pH ∧
      pH * foreignDemand υ η pH (cpi υ η pH pH) C / (cpi υ η pH pH * C) = υ := by
  have hcpi : cpi υ η pH pH = pH := by
    unfold cpi
    rw [show (1 - υ) * pH ^ (1 - η) + υ * pH ^ (1 - η) = pH ^ (1 - η) by ring,
      ← Real.rpow_mul hpH.le, mul_one_div_cancel (sub_ne_zero.2 (Ne.symm hη1)), Real.rpow_one]
  refine ⟨hcpi, ?_⟩
  rw [importShare hυ0 hυ1 hpH hpH hC, hcpi, div_self hpH.ne', Real.one_rpow, mul_one]

/-! ### Footnotes 1 and 2: the limit `η → 1` -/

/-- Galí (2015), fns. 1–2, pp. 225–226: for weights `a, b > 0`, `a + b = 1` and `z₁, z₂ > 0`,
the power mean `(a z₁^s + b z₂^s)^{1/s}` tends to the geometric mean `z₁^a z₂^b` as `s → 0`. -/
theorem powerMean_tendsto {a b z₁ z₂ : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hz₁ : 0 < z₁) (hz₂ : 0 < z₂) :
    Tendsto (fun s : ℝ => (a * z₁ ^ s + b * z₂ ^ s) ^ (1 / s)) (𝓝[≠] 0)
      (𝓝 (z₁ ^ a * z₂ ^ b)) := by
  set f : ℝ → ℝ := fun s => a * Real.exp (s * Real.log z₁) + b * Real.exp (s * Real.log z₂)
    with hfdef
  have hf0 : f 0 = 1 := by simp [f, hab]
  have hfpos : ∀ s, 0 < f s := fun s => by positivity
  have hfd : HasDerivAt f (a * Real.log z₁ + b * Real.log z₂) 0 := by
    have h3 := (((hasDerivAt_id' (0 : ℝ)).mul_const (Real.log z₁)).exp.const_mul a).add
      (((hasDerivAt_id' (0 : ℝ)).mul_const (Real.log z₂)).exp.const_mul b)
    simp only [zero_mul, Real.exp_zero, one_mul] at h3
    exact h3
  have hg : HasDerivAt (fun s => Real.log (f s)) (a * Real.log z₁ + b * Real.log z₂) 0 := by
    convert hfd.log (by rw [hf0]; norm_num) using 1
    rw [hf0, div_one]
  have hslope := hasDerivAt_iff_tendsto_slope_zero.1 hg
  have hlim := (Real.continuous_exp.tendsto _).comp hslope
  have hK : Real.exp (a * Real.log z₁ + b * Real.log z₂) = z₁ ^ a * z₂ ^ b := by
    rw [Real.exp_add, Real.rpow_def_of_pos hz₁, Real.rpow_def_of_pos hz₂, mul_comm a,
      mul_comm b]
  rw [hK] at hlim
  refine hlim.congr fun s => ?_
  simp only [Function.comp_apply, zero_add, hf0, Real.log_one, sub_zero, smul_eq_mul]
  have hfs : f s = a * z₁ ^ s + b * z₂ ^ s := by
    simp only [f]
    rw [Real.rpow_def_of_pos hz₁, Real.rpow_def_of_pos hz₂, mul_comm (Real.log z₁),
      mul_comm (Real.log z₂)]
  rw [Real.rpow_def_of_pos (by rw [← hfs]; exact hfpos s), ← hfs, one_div, mul_comm]

/-- Galí (2015), fn. 1, p. 225: **as `η → 1` the consumption index (2) tends to the
Cobb–Douglas index** `C_H^{1−υ} C_F^υ / ((1−υ)^{1−υ} υ^υ)` (for `C_H, C_F > 0`). -/
theorem cesIndex_tendsto_cd (hυ0 : 0 < υ) (hυ1 : υ < 1) {x y : ℝ} (hx : 0 < x)
    (hy : 0 < y) :
    Tendsto (fun η => cesIndex υ η x y) (𝓝[≠] 1) (𝓝 (cesIndexCD υ x y)) := by
  have h1υ : 0 < 1 - υ := by linarith
  have hM := powerMean_tendsto h1υ hυ0 (by ring) (div_pos hx h1υ) (div_pos hy hυ0)
  have hr : Tendsto (fun η : ℝ => (η - 1) / η) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun η : ℝ => (η - 1) / η) 1 :=
        (continuousAt_id.sub continuousAt_const).div continuousAt_id one_ne_zero
      have := hc.tendsto
      simp only [sub_self, zero_div] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    · have h0 : ∀ᶠ η in 𝓝[≠] (1 : ℝ), η ≠ 0 :=
        nhdsWithin_le_nhds (isOpen_ne.mem_nhds one_ne_zero)
      filter_upwards [h0, self_mem_nhdsWithin] with η hη0 hη1
      exact div_ne_zero (sub_ne_zero.2 hη1) hη0
  have hlim := hM.comp hr
  have htarget : (x / (1 - υ)) ^ (1 - υ) * (y / υ) ^ υ = cesIndexCD υ x y := by
    rw [cesIndexCD, Real.div_rpow hx.le h1υ.le, Real.div_rpow hy.le hυ0.le]
    field_simp
  rw [htarget] at hlim
  refine hlim.congr' ?_
  have h0 : ∀ᶠ η in 𝓝[≠] (1 : ℝ), η ≠ 0 :=
    nhdsWithin_le_nhds (isOpen_ne.mem_nhds one_ne_zero)
  filter_upwards [h0, self_mem_nhdsWithin] with η hη0 hη1
  have hη1' : η - 1 ≠ 0 := sub_ne_zero.2 hη1
  simp only [Function.comp_apply]
  unfold cesIndex
  have e1 : 1 / ((η - 1) / η) = η / (η - 1) := one_div_div _ _
  have hw : ∀ {a z : ℝ}, 0 < a → 0 < z →
      a * (z / a) ^ ((η - 1) / η) = a ^ (1 / η) * z ^ ((η - 1) / η) := by
    intro a z ha hz
    rw [Real.div_rpow hz.le ha.le]
    have : 1 / η = 1 - (η - 1) / η := by field_simp; ring
    rw [this, Real.rpow_sub ha, Real.rpow_one]
    field_simp
  rw [e1, hw h1υ hx, hw hυ0 hy]

/-- Galí (2015), fn. 2, p. 226: **as `η → 1` the CPI tends to `P_H^{1−υ} P_F^υ`**. -/
theorem cpi_tendsto_cd (hυ0 : 0 < υ) (hυ1 : υ < 1) (hpH : 0 < pH) (hpF : 0 < pF) :
    Tendsto (fun η => cpi υ η pH pF) (𝓝[≠] 1) (𝓝 (cpiCD υ pH pF)) := by
  have h1υ : 0 < 1 - υ := by linarith
  have hM := powerMean_tendsto h1υ hυ0 (by ring) hpH hpF
  have hs : Tendsto (fun η : ℝ => 1 - η) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun η : ℝ => 1 - η) 1 := continuousAt_const.sub continuousAt_id
      have := hc.tendsto
      simp only [sub_self] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    · filter_upwards [self_mem_nhdsWithin] with η hη1
      exact sub_ne_zero.2 (Ne.symm hη1)
  exact hM.comp hs

/-! ### The Cobb–Douglas case `η = 1` (fn. 2) -/

/-- Galí (2015), eq. (5) with `η = 1`: demand `C_H = (1−υ)(P_H/P)^{−1} C = (1−υ) P C / P_H`
(and symmetrically for `C_F`), with `P = P_H^{1−υ} P_F^υ`. -/
theorem cesIndexCD_demand (hυ0 : 0 < υ) (hυ1 : υ < 1) (hpH : 0 < pH) (hpF : 0 < pF)
    {C : ℝ} (hC : 0 ≤ C) :
    cesIndexCD υ (homeDemand υ 1 pH (cpiCD υ pH pF) C)
      (foreignDemand υ 1 pF (cpiCD υ pH pF) C) = C := by
  have h1υ : 0 < 1 - υ := by linarith
  have hP : 0 < cpiCD υ pH pF := by unfold cpiCD; positivity
  set P := cpiCD υ pH pF with hPdef
  unfold cesIndexCD homeDemand foreignDemand
  rw [Real.rpow_neg_one, Real.rpow_neg_one, inv_div, inv_div]
  have e1 : (1 - υ) * (P / pH) * C = (1 - υ) * (P * C / pH) := by ring
  have e2 : υ * (P / pF) * C = υ * (P * C / pF) := by ring
  rw [e1, e2, Real.mul_rpow h1υ.le (by positivity), Real.mul_rpow hυ0.le (by positivity),
    Real.div_rpow (by positivity) hpH.le, Real.div_rpow (by positivity) hpF.le,
    Real.mul_rpow hP.le hC, Real.mul_rpow hP.le hC]
  have hPC : P ^ (1 - υ) * P ^ υ = P := by
    rw [← Real.rpow_add hP]; simp
  have hCC : C ^ (1 - υ) * C ^ υ = C := by
    rcases hC.eq_or_lt with h | h
    · rw [← h, Real.zero_rpow h1υ.ne', zero_mul]
    · rw [← Real.rpow_add h]; simp
  have hPdef' : P = pH ^ (1 - υ) * pF ^ υ := rfl
  have key : (1 - υ) ^ (1 - υ) * (P ^ (1 - υ) * C ^ (1 - υ) / pH ^ (1 - υ)) *
      (υ ^ υ * (P ^ υ * C ^ υ / pF ^ υ)) / ((1 - υ) ^ (1 - υ) * υ ^ υ)
      = (P ^ (1 - υ) * P ^ υ) * (C ^ (1 - υ) * C ^ υ) / (pH ^ (1 - υ) * pF ^ υ) := by
    have : 0 < (1 - υ) ^ (1 - υ) := by positivity
    have : 0 < υ ^ υ := by positivity
    have : 0 < pH ^ (1 - υ) := by positivity
    have : 0 < pF ^ υ := by positivity
    field_simp
  rw [key, hPC, hCC, ← hPdef']
  field_simp

/-- Galí (2015), p. 227 with `η = 1`: the demands cost exactly `P C` with
`P = P_H^{1−υ} P_F^υ`. -/
theorem expenditureCD_demand (hpH : 0 < pH) (hpF : 0 < pF)
    (C : ℝ) :
    pH * homeDemand υ 1 pH (cpiCD υ pH pF) C + pF * foreignDemand υ 1 pF (cpiCD υ pH pF) C
      = cpiCD υ pH pF * C := by
  unfold homeDemand foreignDemand
  rw [Real.rpow_neg_one, Real.rpow_neg_one, inv_div, inv_div]
  field_simp
  ring

/-- Galí (2015), fn. 2, p. 226 (with the fn-1 normalisation): the index cost identity
`P · C(C_H, C_F) = (P_H C_H/(1−υ))^{1−υ} (P_F C_F/υ)^υ` at `η = 1`. -/
theorem cpiCD_mul_cesIndexCD (hυ0 : 0 < υ) (hυ1 : υ < 1) (hpH : 0 < pH) (hpF : 0 < pF)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    cpiCD υ pH pF * cesIndexCD υ x y
      = (pH * x / (1 - υ)) ^ (1 - υ) * (pF * y / υ) ^ υ := by
  have h1υ : 0 < 1 - υ := by linarith
  unfold cpiCD cesIndexCD
  rw [Real.div_rpow (by positivity) h1υ.le, Real.div_rpow (by positivity) hυ0.le,
    Real.mul_rpow hpH.le hx, Real.mul_rpow hpF.le hy]
  have : 0 < (1 - υ) ^ (1 - υ) := by positivity
  have : 0 < υ ^ υ := by positivity
  field_simp

/-- Galí (2015), fn. 2, p. 226: at `η = 1`, every bundle `C_H, C_F ≥ 0` costs at least
`P_H^{1−υ} P_F^υ · C`, `C` its Cobb–Douglas index (fn. 1): the CPI is exactly
`P_H^{1−υ}P_F^υ`. -/
theorem expenditureCD_ge (hυ0 : 0 < υ) (hυ1 : υ < 1) (hpH : 0 < pH) (hpF : 0 < pF)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    cpiCD υ pH pF * cesIndexCD υ x y ≤ pH * x + pF * y := by
  have h1υ : 0 < 1 - υ := by linarith
  rw [cpiCD_mul_cesIndexCD hυ0 hυ1 hpH hpF hx hy]
  have h := Real.geom_mean_le_arith_mean2_weighted h1υ.le hυ0.le
    (div_nonneg (mul_nonneg hpH.le hx) h1υ.le) (div_nonneg (mul_nonneg hpF.le hy) hυ0.le)
    (by ring)
  have e : (1 - υ) * (pH * x / (1 - υ)) + υ * (pF * y / υ) = pH * x + pF * y := by
    field_simp
  linarith

/-- Galí (2015), (5) and fn. 2 at `η = 1`: a bundle costs exactly `P · C` iff it is the
demand schedule `C_H = (1−υ)(P_H/P)^{−1} C`, `C_F = υ(P_F/P)^{−1} C`. -/
theorem expenditureCD_eq_iff (hυ0 : 0 < υ) (hυ1 : υ < 1) (hpH : 0 < pH) (hpF : 0 < pF)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    pH * x + pF * y = cpiCD υ pH pF * cesIndexCD υ x y ↔
      x = homeDemand υ 1 pH (cpiCD υ pH pF) (cesIndexCD υ x y) ∧
        y = foreignDemand υ 1 pF (cpiCD υ pH pF) (cesIndexCD υ x y) := by
  have h1υ : 0 < 1 - υ := by linarith
  have hP : 0 < cpiCD υ pH pF := by unfold cpiCD; positivity
  set X1 := pH * x / (1 - υ)
  set X2 := pF * y / υ
  have hX1 : 0 ≤ X1 := div_nonneg (mul_nonneg hpH.le hx) h1υ.le
  have hX2 : 0 ≤ X2 := div_nonneg (mul_nonneg hpF.le hy) hυ0.le
  have hiff := Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos h1υ hυ0 hX1 hX2 (by ring)
  have e : (1 - υ) * X1 + υ * X2 = pH * x + pF * y := by
    simp only [X1, X2]; field_simp
  have hPC := cpiCD_mul_cesIndexCD hυ0 hυ1 hpH hpF hx hy
  rw [e] at hiff
  set P := cpiCD υ pH pF
  set C := cesIndexCD υ x y
  have hdH : homeDemand υ 1 pH P C = (1 - υ) * (P * C) / pH := by
    unfold homeDemand; rw [Real.rpow_neg_one, inv_div]; ring
  have hdF : foreignDemand υ 1 pF P C = υ * (P * C) / pF := by
    unfold foreignDemand; rw [Real.rpow_neg_one, inv_div]; ring
  rw [hdH, hdF, hPC]
  set G := X1 ^ (1 - υ) * X2 ^ υ with hG
  rw [show (pH * x + pF * y = G) ↔ (G = pH * x + pF * y) from eq_comm, hiff]
  constructor
  · intro h
    have hX : G = X1 := by
      rw [hG, ← h, ← Real.rpow_add' hX1 (by norm_num : (1 - υ) + υ ≠ 0)]
      simp
    rw [hX]
    refine ⟨?_, ?_⟩
    · simp only [X1]; field_simp
    · rw [h]; simp only [X2]; field_simp
  · rintro ⟨h1, h2⟩
    have k1 : X1 = G := by simp only [X1]; rw [h1]; field_simp
    have k2 : X2 = G := by simp only [X2]; rw [h2]; field_simp
    rw [k1, k2]

namespace Variety

open MeasureTheory

variable {G : Type*} [MeasurableSpace G]

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: p. 53: the aggregate price index `P = (∫ P(i)^{1−ε} di)^{1/(1−ε)}`. -/
noncomputable def priceIndex (μ : Measure G) (ε : ℝ) (P : G → ℝ) : ℝ :=
  (∫ i, P i ^ (1 - ε) ∂μ) ^ (1 - ε)⁻¹

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: p. 52–53: the CES consumption index
`C = (∫ C(i)^{(ε−1)/ε} di)^{ε/(ε−1)}`. -/
noncomputable def cesAgg (μ : Measure G) (ε : ℝ) (c : G → ℝ) : ℝ :=
  (∫ i, c i ^ ((ε - 1) / ε) ∂μ) ^ ((ε - 1) / ε)⁻¹

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: eq. (1), p. 53: the demand schedule `C(i) = (P(i)/P)^{−ε} C`. -/
noncomputable def demand (μ : Measure G) (ε : ℝ) (P : G → ℝ) (C : ℝ) (i : G) : ℝ :=
  (P i / priceIndex μ ε P) ^ (-ε) * C

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: App. 3.1, p. 83: the exponent identity `(ε−1)/ε + 1/ε = 1`. -/
theorem r_add_inv {ε : ℝ} (hε : 1 < ε) : (ε - 1) / ε + 1 / ε = 1 := by
  have : ε ≠ 0 := by linarith
  field_simp
  ring

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: App. 3.1, p. 83: the factorisation behind `young_le`,
`c^r = (a c C^{−1/ε})^r (a^{1−ε} C^r)^{1/ε}` with `r = (ε − 1)/ε`. -/
theorem young_key {ε a c C : ℝ} (hε : 1 < ε) (ha : 0 < a) (hc : 0 ≤ c) (hC : 0 < C) :
    (a * c * C ^ (-1 / ε)) ^ ((ε - 1) / ε) * (a ^ (1 - ε) * C ^ ((ε - 1) / ε)) ^ (1 / ε)
      = c ^ ((ε - 1) / ε) := by
  have hε0 : (0 : ℝ) < ε := by linarith
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow ha.le hc,
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul ha.le,
    ← Real.rpow_mul hC.le, ← Real.rpow_mul hC.le]
  have e1 : a ^ ((ε - 1) / ε) * c ^ ((ε - 1) / ε) * C ^ (-1 / ε * ((ε - 1) / ε)) *
      (a ^ ((1 - ε) * (1 / ε)) * C ^ ((ε - 1) / ε * (1 / ε)))
      = c ^ ((ε - 1) / ε) * (a ^ ((ε - 1) / ε) * a ^ ((1 - ε) * (1 / ε))) *
        (C ^ (-1 / ε * ((ε - 1) / ε)) * C ^ ((ε - 1) / ε * (1 / ε))) := by ring
  rw [e1, ← Real.rpow_add ha, ← Real.rpow_add hC]
  have z1 : (ε - 1) / ε + (1 - ε) * (1 / ε) = 0 := by field_simp; ring
  have z2 : -1 / ε * ((ε - 1) / ε) + (ε - 1) / ε * (1 / ε) = 0 := by ring
  rw [z1, z2, Real.rpow_zero, Real.rpow_zero, mul_one, mul_one]

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: App. 3.1, p. 83: the pointwise weighted AM–GM (Young) inequality behind
expenditure minimisation. For a relative price `a > 0`, a quantity `c ≥ 0` and an aggregate
`C > 0`, `c^r ≤ r (a c C^{−1/ε}) + (1/ε) a^{1−ε} C^r` with `r = (ε − 1)/ε`. -/
theorem young_le {ε a c C : ℝ} (hε : 1 < ε) (ha : 0 < a) (hc : 0 ≤ c) (hC : 0 < C) :
    c ^ ((ε - 1) / ε) ≤
      (ε - 1) / ε * (a * c * C ^ (-1 / ε)) + 1 / ε * (a ^ (1 - ε) * C ^ ((ε - 1) / ε)) := by
  have hε0 : (0 : ℝ) < ε := by linarith
  rw [← young_key hε ha hc hC]
  exact Real.geom_mean_le_arith_mean2_weighted (div_nonneg (by linarith) hε0.le)
    (by positivity) (by positivity) (by positivity) (r_add_inv hε)

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: App. 3.1, p. 83: equality in `young_le` holds iff `c = a^{−ε} C`, i.e. iff
the quantity lies on the demand schedule (1). -/
theorem young_eq_iff {ε a c C : ℝ} (hε : 1 < ε) (ha : 0 < a) (hc : 0 ≤ c) (hC : 0 < C) :
    c ^ ((ε - 1) / ε) =
      (ε - 1) / ε * (a * c * C ^ (-1 / ε)) + 1 / ε * (a ^ (1 - ε) * C ^ ((ε - 1) / ε)) ↔
      c = a ^ (-ε) * C := by
  have hε0 : (0 : ℝ) < ε := by linarith
  rw [← young_key hε ha hc hC, Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos
    (div_pos (by linarith) hε0) (by positivity) (by positivity) (by positivity) (r_add_inv hε)]
  have hk : a * C ^ (-1 / ε) ≠ 0 := by positivity
  have hv : a ^ (1 - ε) * C ^ ((ε - 1) / ε) = a * C ^ (-1 / ε) * (a ^ (-ε) * C) := by
    have h1 : a ^ (1 - ε) = a * a ^ (-ε) := by
      rw [sub_eq_add_neg, Real.rpow_add ha, Real.rpow_one]
    have h2 : C ^ ((ε - 1) / ε) = C ^ (-1 / ε) * C := by
      have : (ε - 1) / ε = -1 / ε + 1 := by field_simp; ring
      rw [this, Real.rpow_add hC, Real.rpow_one]
    rw [h1, h2]
    ring
  rw [hv, show a * c * C ^ (-1 / ε) = a * C ^ (-1 / ε) * c by ring]
  exact mul_right_inj' hk

variable {μ : Measure G} {ε : ℝ} {P : G → ℝ}

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: p. 53: the price index is positive when `∫ P(i)^{1−ε} > 0`. -/
theorem priceIndex_pos (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) : 0 < priceIndex μ ε P :=
  Real.rpow_pos_of_pos hpos _

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: p. 53: `P^{1−ε} = ∫ P(i)^{1−ε} di`, the defining property of the index. -/
theorem priceIndex_rpow (hε : 1 < ε) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) :
    priceIndex μ ε P ^ (1 - ε) = ∫ i, P i ^ (1 - ε) ∂μ :=
  Real.rpow_inv_rpow hpos.le (by linarith)

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: p. 85 (index condition): `∫ (P(i)/P)^{1−ε} di = 1`. -/
theorem integral_relPrice_rpow (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) :
    ∫ i, (P i / priceIndex μ ε P) ^ (1 - ε) ∂μ = 1 := by
  have hI := priceIndex_pos hpos
  simp_rw [Real.div_rpow (hP _).le hI.le]
  rw [integral_div, priceIndex_rpow hε hpos, div_self hpos.ne']

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: p. 85: the relative-price integrand `(P(i)/P)^{1−ε}` is integrable. -/
theorem integrable_relPrice_rpow (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hP : ∀ i, 0 < P i)
    (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) :
    Integrable (fun i => (P i / priceIndex μ ε P) ^ (1 - ε)) μ := by
  have hI := priceIndex_pos hpos
  simp_rw [Real.div_rpow (hP _).le hI.le]
  exact hPi.div_const _

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: eq. (1) and p. 53: the demand schedule `C(i) = (P(i)/P)^{−ε} C` delivers
exactly the aggregate `C`. -/
theorem cesAgg_demand (hε : 1 < ε) (hP : ∀ i, 0 < P i) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {C : ℝ} (hC : 0 ≤ C) : cesAgg μ ε (demand μ ε P C) = C := by
  have hI := priceIndex_pos hpos
  have hε0 : (0 : ℝ) < ε := by linarith
  have hr : (ε - 1) / ε ≠ 0 := div_ne_zero (by linarith) hε0.ne'
  have hpt : ∀ i, demand μ ε P C i ^ ((ε - 1) / ε)
      = C ^ ((ε - 1) / ε) * (P i / priceIndex μ ε P) ^ (1 - ε) := by
    intro i
    have ha : 0 < P i / priceIndex μ ε P := div_pos (hP i) hI
    rw [demand, Real.mul_rpow (by positivity) hC, ← Real.rpow_mul ha.le]
    have : -ε * ((ε - 1) / ε) = 1 - ε := by field_simp; ring
    rw [this, mul_comm]
  unfold cesAgg
  simp_rw [hpt]
  rw [integral_const_mul, integral_relPrice_rpow hε hP hpos, mul_one, Real.rpow_rpow_inv hC hr]

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: p. 53: `P(i) (P(i)/P)^{−ε} C = P C (P(i)/P)^{1−ε}` pointwise. -/
theorem price_mul_demand (hP : ∀ i, 0 < P i) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) (C : ℝ)
    (i : G) : P i * demand μ ε P C i
      = priceIndex μ ε P * C * (P i / priceIndex μ ε P) ^ (1 - ε) := by
  have hI := priceIndex_pos hpos
  have ha : 0 < P i / priceIndex μ ε P := div_pos (hP i) hI
  have h1 : (P i / priceIndex μ ε P) ^ (1 - ε)
      = P i / priceIndex μ ε P * (P i / priceIndex μ ε P) ^ (-ε) := by
    rw [sub_eq_add_neg, Real.rpow_add ha, Real.rpow_one]
  rw [demand, h1]
  field_simp

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: p. 53: under the demand schedule, total expenditure is
`∫ P(i) C(i) di = P C`. -/
theorem spend_demand (hε : 1 < ε) (hP : ∀ i, 0 < P i) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    (C : ℝ) : ∫ i, P i * demand μ ε P C i ∂μ = priceIndex μ ε P * C := by
  simp_rw [price_mul_demand hP hpos C]
  rw [integral_const_mul, integral_relPrice_rpow hε hP hpos, mul_one]

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: App. 3.1, p. 83: the CES aggregate is nonnegative. -/
theorem cesAgg_nonneg {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) : 0 ≤ cesAgg μ ε c :=
  Real.rpow_nonneg (integral_nonneg fun i => Real.rpow_nonneg (hc i) _) _

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: App. 3.1, p. 83: `C^r = ∫ C(i)^r` for the CES aggregate `C`. -/
theorem cesAgg_rpow (hε : 1 < ε) {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) :
    cesAgg μ ε c ^ ((ε - 1) / ε) = ∫ i, c i ^ ((ε - 1) / ε) ∂μ :=
  Real.rpow_inv_rpow (integral_nonneg fun i => Real.rpow_nonneg (hc i) _)
    (div_ne_zero (by linarith) (by linarith))

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: App. 3.1, p. 83: the integrated Young bound. For a bundle with positive
aggregate `C`, `C^r ≤ r C^{−1/ε} (∫ P c)/P + (1/ε) C^r`. -/
theorem integrated_young (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ)
    (hC : 0 < cesAgg μ ε c) :
    Integrable (fun i => (ε - 1) / ε * (cesAgg μ ε c ^ (-1 / ε) / priceIndex μ ε P) *
        (P i * c i) + 1 / ε * cesAgg μ ε c ^ ((ε - 1) / ε) *
          (P i / priceIndex μ ε P) ^ (1 - ε)) μ ∧
      (∀ i, c i ^ ((ε - 1) / ε) ≤ (ε - 1) / ε * (cesAgg μ ε c ^ (-1 / ε) / priceIndex μ ε P) *
        (P i * c i) + 1 / ε * cesAgg μ ε c ^ ((ε - 1) / ε) *
          (P i / priceIndex μ ε P) ^ (1 - ε)) ∧
      ∫ i, ((ε - 1) / ε * (cesAgg μ ε c ^ (-1 / ε) / priceIndex μ ε P) *
        (P i * c i) + 1 / ε * cesAgg μ ε c ^ ((ε - 1) / ε) *
          (P i / priceIndex μ ε P) ^ (1 - ε)) ∂μ
        = (ε - 1) / ε * (cesAgg μ ε c ^ (-1 / ε) / priceIndex μ ε P) *
          (∫ i, P i * c i ∂μ) + 1 / ε * cesAgg μ ε c ^ ((ε - 1) / ε) := by
  have hI := priceIndex_pos hpos
  have hint1 := hpc.const_mul ((ε - 1) / ε * (cesAgg μ ε c ^ (-1 / ε) / priceIndex μ ε P))
  have hint2 := (integrable_relPrice_rpow hPi hP hpos).const_mul
    (1 / ε * cesAgg μ ε c ^ ((ε - 1) / ε))
  refine ⟨hint1.add hint2, fun i => ?_, ?_⟩
  · have h := young_le hε (div_pos (hP i) hI) (hc i) hC
    have e : (ε - 1) / ε * (cesAgg μ ε c ^ (-1 / ε) / priceIndex μ ε P) * (P i * c i)
        = (ε - 1) / ε * (P i / priceIndex μ ε P * c i * cesAgg μ ε c ^ (-1 / ε)) := by ring
    rw [e]
    linarith
  · rw [integral_add hint1 hint2, integral_const_mul, integral_const_mul,
      integral_relPrice_rpow hε hP hpos, mul_one]

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: p. 53 and App. 3.1, p. 83 (**expenditure minimisation**): any bundle
`C(·) ≥ 0` costs at least `P · C`, where `C` is its CES aggregate. -/
theorem spend_ge (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ) :
    priceIndex μ ε P * cesAgg μ ε c ≤ ∫ i, P i * c i ∂μ := by
  have hI := priceIndex_pos hpos
  have hε0 : (0 : ℝ) < ε := by linarith
  have hS : 0 ≤ ∫ i, P i * c i ∂μ := integral_nonneg fun i => mul_nonneg (hP i).le (hc i)
  rcases (cesAgg_nonneg (μ := μ) (ε := ε) hc).eq_or_lt with h0 | hC
  · rw [← h0, mul_zero]; exact hS
  obtain ⟨hint, hle, hval⟩ := integrated_young hε hP hPi hpos hc hpc hC
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun i => Real.rpow_nonneg (hc i) ((ε - 1) / ε)) hint
    (Filter.Eventually.of_forall hle)
  rw [hval, ← cesAgg_rpow hε hc] at hmono
  set C := cesAgg μ ε c
  set S := ∫ i, P i * c i ∂μ
  have hK : 0 < C ^ (-1 / ε) := Real.rpow_pos_of_pos hC _
  have hCr : C ^ ((ε - 1) / ε) = C * C ^ (-1 / ε) := by
    have : (ε - 1) / ε = 1 + -1 / ε := by field_simp; ring
    rw [this, Real.rpow_add hC, Real.rpow_one]
  rw [hCr] at hmono
  have hr : 0 < (ε - 1) / ε := div_pos (by linarith) hε0
  have h1 : (ε - 1) / ε * (C * C ^ (-1 / ε)) ≤
      (ε - 1) / ε * (C ^ (-1 / ε) * (S / priceIndex μ ε P)) := by
    have e : 1 / ε = 1 - (ε - 1) / ε := by field_simp; ring
    rw [e] at hmono
    have e2 : (ε - 1) / ε * (C ^ (-1 / ε) / priceIndex μ ε P) * S
        = (ε - 1) / ε * (C ^ (-1 / ε) * (S / priceIndex μ ε P)) := by ring
    rw [e2] at hmono
    linarith
  have h2 := le_of_mul_le_mul_left h1 hr
  rw [mul_comm C] at h2
  have h3 := le_of_mul_le_mul_left h2 hK
  rw [le_div_iff₀ hI] at h3
  linarith

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: eq. (1), p. 53 and App. 3.1, p. 83: a bundle costs exactly `P · C` (its
aggregate `C`) **if and only if** it is the demand schedule `C(i) = (P(i)/P)^{−ε} C`
almost everywhere. -/
theorem spend_eq_iff (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ) :
    ∫ i, P i * c i ∂μ = priceIndex μ ε P * cesAgg μ ε c ↔
      c =ᵐ[μ] demand μ ε P (cesAgg μ ε c) := by
  have hI := priceIndex_pos hpos
  have hε0 : (0 : ℝ) < ε := by linarith
  constructor
  swap
  · intro h
    rw [← spend_demand hε hP hpos (cesAgg μ ε c)]
    refine integral_congr_ae ?_
    filter_upwards [h] with i hi
    rw [hi]
  intro heq
  rcases (cesAgg_nonneg (μ := μ) (ε := ε) hc).eq_or_lt with h0 | hC
  · rw [← h0, mul_zero] at heq
    have hz := (integral_eq_zero_iff_of_nonneg
      (fun i => mul_nonneg (hP i).le (hc i)) hpc).1 heq
    filter_upwards [hz] with i hi
    rw [← h0, demand, mul_zero]
    simp only [Pi.zero_apply] at hi
    rcases mul_eq_zero.1 hi with h | h
    · exact absurd h (hP i).ne'
    · exact h
  obtain ⟨hint, hle, hval⟩ := integrated_young hε hP hPi hpos hc hpc hC
  set C := cesAgg μ ε c
  have hcr : Integrable (fun i => c i ^ ((ε - 1) / ε)) μ := by
    refine Integrable.of_integral_ne_zero ?_
    rw [← cesAgg_rpow hε hc]
    exact (Real.rpow_pos_of_pos hC _).ne'
  have hdiff := (integral_eq_zero_iff_of_nonneg
    (fun i => sub_nonneg.2 (hle i)) (hint.sub hcr)).1 (by
      rw [integral_sub hint hcr, hval, ← cesAgg_rpow hε hc, heq]
      have hCr : C ^ ((ε - 1) / ε) = C * C ^ (-1 / ε) := by
        have : (ε - 1) / ε = 1 + -1 / ε := by field_simp; ring
        rw [this, Real.rpow_add hC, Real.rpow_one]
      rw [hCr]
      field_simp
      ring)
  filter_upwards [hdiff] with i hi
  simp only [Pi.zero_apply, sub_eq_zero] at hi
  have := (young_eq_iff hε (div_pos (hP i) hI) (hc i) hC).1 (by
    rw [← hi]
    ring)
  rw [this, demand]

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: App. 3.1, p. 83 (dual form): for a bundle with expenditure
`∫ P(i) C(i) = X`, the attainable consumption index is at most `X / P`. -/
theorem cesAgg_le_of_spend (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ) {X : ℝ}
    (hX : ∫ i, P i * c i ∂μ = X) : cesAgg μ ε c ≤ X / priceIndex μ ε P := by
  rw [le_div_iff₀ (priceIndex_pos hpos), mul_comm, ← hX]
  exact spend_ge hε hP hPi hpos hc hpc

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: App. 3.1, p. 83 (dual form, equality): with expenditure `X`, the index
attains `X / P` iff `C(i) = (P(i)/P)^{−ε} X/P` almost everywhere. -/
theorem cesAgg_eq_iff_of_spend (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ) {X : ℝ}
    (hX : ∫ i, P i * c i ∂μ = X) :
    cesAgg μ ε c = X / priceIndex μ ε P ↔
      c =ᵐ[μ] demand μ ε P (X / priceIndex μ ε P) := by
  have hI := priceIndex_pos hpos
  constructor
  · intro h
    rw [← h]
    refine (spend_eq_iff hε hP hPi hpos hc hpc).1 ?_
    rw [h, hX]
    field_simp
  · intro h
    have hX0 : 0 ≤ X / priceIndex μ ε P := by
      rw [← hX]
      exact div_nonneg (integral_nonneg fun i => mul_nonneg (hP i).le (hc i)) hI.le
    have hagg : cesAgg μ ε c = cesAgg μ ε (demand μ ε P (X / priceIndex μ ε P)) := by
      unfold cesAgg
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [h] with i hi
      rw [hi]
    rw [hagg, cesAgg_demand hε hP hpos hX0]

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: p. 53: a positive integrable function has positive integral against a
nonzero measure (used to see that `∫ P(i)^{1−ε} > 0`). -/
theorem integral_pos_of_pos {f : G → ℝ} (hμ : μ ≠ 0) (hf : ∀ i, 0 < f i)
    (hfi : Integrable f μ) : 0 < ∫ i, f i ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun i => (hf i).le) hfi]
  have : Function.support f = Set.univ :=
    Set.eq_univ_of_forall fun i => (hf i).ne'
  rw [this]
  exact Measure.measure_univ_pos.2 hμ

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: p. 53: Lebesgue measure on the goods continuum `[0, 1]` is nonzero. -/
theorem unitInterval_ne_zero : (volume.restrict (Set.Icc (0 : ℝ) 1)) ≠ 0 := by
  rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc]
  simp

/-- Galí (2015), eq. (4), p. 226 (restated from the Chapter 3 project);
ch. 3 ref.: §3.1, p. 53 and App. 3.1, p. 83, on the book's **continuum of goods
`[0, 1]` with Lebesgue measure**: (i) every bundle `C(·) ≥ 0` costs at least `P · C`;
(ii) it costs exactly `P · C` iff `C(i) = (P(i)/P)^{−ε} C` for a.e. `i ∈ [0, 1]`;
(iii) the demand schedule attains any aggregate `C ≥ 0`; (iv) it costs `P C`. -/
theorem unitInterval_expenditure_minimisation (hε : 1 < ε) {Q : ℝ → ℝ} (hQ : ∀ i, 0 < Q i)
    (hQi : IntegrableOn (fun i => Q i ^ (1 - ε)) (Set.Icc 0 1)) {c : ℝ → ℝ}
    (hc : ∀ i, 0 ≤ c i) (hQc : IntegrableOn (fun i => Q i * c i) (Set.Icc 0 1)) :
    priceIndex (volume.restrict (Set.Icc 0 1)) ε Q * cesAgg (volume.restrict (Set.Icc 0 1)) ε c
        ≤ ∫ i in Set.Icc 0 1, Q i * c i ∧
      (∫ i in Set.Icc 0 1, Q i * c i
          = priceIndex (volume.restrict (Set.Icc 0 1)) ε Q *
            cesAgg (volume.restrict (Set.Icc 0 1)) ε c ↔
        ∀ᵐ i ∂(volume.restrict (Set.Icc 0 1)),
          c i = demand (volume.restrict (Set.Icc 0 1)) ε Q
            (cesAgg (volume.restrict (Set.Icc 0 1)) ε c) i) ∧
      (∀ C : ℝ, 0 ≤ C → cesAgg (volume.restrict (Set.Icc 0 1)) ε
        (demand (volume.restrict (Set.Icc 0 1)) ε Q C) = C) ∧
      ∀ C : ℝ, ∫ i in Set.Icc 0 1, Q i * demand (volume.restrict (Set.Icc 0 1)) ε Q C i
        = priceIndex (volume.restrict (Set.Icc 0 1)) ε Q * C := by
  have hpos := integral_pos_of_pos unitInterval_ne_zero (fun i => Real.rpow_pos_of_pos (hQ i) _)
    hQi
  exact ⟨spend_ge hε hQ hQi hpos hc hQc, spend_eq_iff hε hQ hQi hpos hc hQc,
    fun C hC => cesAgg_demand hε hQ hpos hC, spend_demand hε hQ hpos⟩

/-- Galí (2015), eqs. (4)–(5) and p. 227 (**two-stage budgeting**): with domestic varieties
`i ∈ [0, 1]` priced `Q(i)` and `P_H` their price index, the home demand `C_H` of (5) is
allocated across varieties by (4) and imports are `C_F` of (5); total spending is
`∫ P_H(i) C_H(i) di + P_F C_F = P C`. -/
theorem two_stage_expenditure {υ η ε pF : ℝ} (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1)
    (hε : 1 < ε) {Q : ℝ → ℝ} (hQ : ∀ i, 0 < Q i)
    (hQi : IntegrableOn (fun i => Q i ^ (1 - ε)) (Set.Icc 0 1)) (hpF : 0 < pF) (C : ℝ) :
    (∫ i in Set.Icc 0 1, Q i * demand (volume.restrict (Set.Icc 0 1)) ε Q
        (homeDemand υ η (priceIndex (volume.restrict (Set.Icc 0 1)) ε Q)
          (cpi υ η (priceIndex (volume.restrict (Set.Icc 0 1)) ε Q) pF) C) i)
      + pF * foreignDemand υ η pF
          (cpi υ η (priceIndex (volume.restrict (Set.Icc 0 1)) ε Q) pF) C
      = cpi υ η (priceIndex (volume.restrict (Set.Icc 0 1)) ε Q) pF * C := by
  have hpos := integral_pos_of_pos unitInterval_ne_zero (fun i => Real.rpow_pos_of_pos (hQ i) _)
    hQi
  rw [spend_demand hε hQ hpos]
  exact expenditure_demand hυ0 hυ1 hη1 (priceIndex_pos hpos) hpF C

end Variety

end Gali.OpenEconomy.Preferences
