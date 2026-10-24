/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Lattice

/-!
# Crashes and breakouts: Miller's two-period model

Cochrane (2023), Chapter 6, §6.3 *Crashes and breakouts*, pp. 193–195.

The two-period model of §1.3 (budget (1.2) `B₋₁ = P₀ s₀ + Q₀ B₀`, bond price (1.3)
`Q₀ = 1/(1+i₀) = β P₀/P₁` under perfect foresight) with the fiscal rule of §2.5.1 capped by a
maximum surplus: `s₁ = min(B₀/P*, s₁^max)`, and terminal condition `B₀/P₁ = s₁`. The central bank
sets `i₀`. Write `q = β(1 + i₀)`.

* Unconstrained regime (`s₁ < s^max`): `P₁ = P*`, `P₀ = P*/q`, independent of `s₀`; a higher
  `i₀` lowers `P₀`.
* Constrained regime (`s₁ = s^max`): `B₋₁/P₀ = s₀ + β s^max`, so deficits pass into `P₀`, `i₀`
  has no effect on `P₀` and only raises `P₁`.
* The regime switches endogenously: `s₁ < s^max` iff `q B₋₁/P* - s₀ < β s^max` (p. 194).

We prove these claims, the global formula `P₀ = max(P*/q, B₋₁/(s₀ + β s^max))` (continuous and
monotone in debt, deficits and the interest rate), existence iff `s₀ + β s^max > 0`, and exact
comparative statics in the interior of each regime. The book's claims need outstanding debt
`B₀ ≠ 0`: when `s₀ > 0` there is also an equilibrium with `B₀ = 0` (the government retires all
debt at date 0, and the rule `s₁ = B₀/P*` then does not pin `P₁`), with `s₁ = 0 < s^max` but
`P₁ ≠ P*` (`degenerate_equilibrium`, `degenerate_price0_ne`). Miller's learning model (p. 195)
is a verbal summary and is not formalised.

## Main results

* `IsEquilibrium`, `fisher`, `valuation`, `isEquilibrium_iff` (the book's equilibrium
  conditions follow from budget, bond pricing and the rule, and conversely).
* `unconstrained_regime`, `constrained_regime`, `boundary_iff`, `boundary_iff_debt`.
* `price0`, `eq_price0`, `isEquilibrium_price0`, `exists_equilibrium_iff`, `price0_unique`.
* `price0_antitoneOn_s0`, `price0_antitoneOn_i0`, `price0_monotone_debt`, `price1_monotoneOn_i0`,
  `continuousOn_price0_s0`, `continuousOn_price0_i0`.
* `hasDerivAt_price0_s0_unconstrained` (`∂P₀/∂s₀ = 0`), `hasDerivAt_price0_i0_unconstrained`
  (`∂P₀/∂i₀ < 0`), `hasDerivAt_price1_i0_unconstrained` (`∂P₁/∂i₀ = 0`),
  `hasDerivAt_price0_s0_constrained` (`∂P₀/∂s₀ < 0`), `hasDerivAt_price0_i0_constrained`
  (`∂P₀/∂i₀ = 0`), `hasDerivAt_price1_i0_constrained` (`∂P₁/∂i₀ > 0`).
* `degenerate_equilibrium`, `degenerate_price0_ne`.
-/

namespace Cochrane.FiscalConstraints.Crash

open Filter Topology

/-- Cochrane (2023), §6.3, p. 194: the capped fiscal rule `s₁ = min(B₀/P*, s₁^max)`. -/
noncomputable def surplus1 (Pst smax B0 : ℝ) : ℝ := min (B0 / Pst) smax

/-- Cochrane (2023), §6.3, p. 194 (with Ch. 1 (1.2), (1.3), p. 8): an equilibrium `(P₀, P₁, B₀)`
given `β`, the target `P*`, the cap `s^max`, initial debt `B₋₁`, the surplus `s₀` and the
interest-rate target `i₀`: positive price levels, the budget `B₋₁ = P₀ s₀ + B₀/(1+i₀)`, the bond
price `1/(1+i₀) = β P₀/P₁`, and the terminal condition `B₀/P₁ = s₁` with the capped rule. -/
def IsEquilibrium (β Pst smax Bm s0 i0 P0 P1 B0 : ℝ) : Prop :=
  0 < P0 ∧ 0 < P1 ∧ Bm = P0 * s0 + B0 / (1 + i0) ∧ 1 / (1 + i0) = β * P0 / P1 ∧
    B0 / P1 = surplus1 Pst smax B0

variable {β Pst smax Bm s0 i0 P0 P1 B0 : ℝ}

/-- Cochrane (2023), §6.3, p. 194: in equilibrium the gross nominal rate is positive,
`1 + i₀ > 0` (the bond price `β P₀/P₁` is positive). -/
theorem one_add_pos (hβ : 0 < β) (h : IsEquilibrium β Pst smax Bm s0 i0 P0 P1 B0) :
    0 < 1 + i0 := by
  obtain ⟨hP0, hP1, -, hQ, -⟩ := h
  have : 0 < 1 / (1 + i0) := by rw [hQ]; positivity
  exact one_div_pos.1 this

/-- Cochrane (2023), eq. (1.9) used in §6.3, p. 194: the interest-rate target fixes expected
inflation, `P₁ = β(1 + i₀) P₀`. -/
theorem fisher (hβ : 0 < β) (h : IsEquilibrium β Pst smax Bm s0 i0 P0 P1 B0) :
    P1 = β * (1 + i0) * P0 := by
  have hi := one_add_pos hβ h
  obtain ⟨hP0, hP1, -, hQ, -⟩ := h
  field_simp at hQ
  linarith

/-- Cochrane (2023), §6.3, p. 194: in equilibrium the valuation equation
`B₋₁/P₀ = s₀ + β s₁` holds, with `s₁ = B₀/P₁`. -/
theorem valuation (hβ : 0 < β) (h : IsEquilibrium β Pst smax Bm s0 i0 P0 P1 B0) :
    Bm / P0 = s0 + β * (B0 / P1) := by
  have hi := one_add_pos hβ h
  have hf := fisher hβ h
  obtain ⟨hP0, hP1, hB, -, -⟩ := h
  rw [hB, hf]
  field_simp

/-- Cochrane (2023), §6.3, p. 194: "Equilibrium still consists of `B₀/P₁ = s₁`,
`B₋₁/P₀ = s₀ + β s₁`": given positive prices and `1 + i₀ > 0`, the budget/pricing/rule
definition is equivalent to the Fisher relation, the terminal condition and the valuation
equation. -/
theorem isEquilibrium_iff (hβ : 0 < β) (hP0 : 0 < P0) (hP1 : 0 < P1) (hi : 0 < 1 + i0) :
    IsEquilibrium β Pst smax Bm s0 i0 P0 P1 B0 ↔
      P1 = β * (1 + i0) * P0 ∧ B0 / P1 = surplus1 Pst smax B0 ∧
        Bm / P0 = s0 + β * (B0 / P1) := by
  constructor
  · intro h
    exact ⟨fisher hβ h, h.2.2.2.2, valuation hβ h⟩
  · rintro ⟨hf, hs, hv⟩
    refine ⟨hP0, hP1, ?_, ?_, hs⟩
    · rw [hf] at hv
      field_simp at hv
      field_simp
      linarith
    · rw [hf]
      field_simp

/-- Cochrane (2023), §6.3, p. 194: in the unconstrained regime `s₁ < s^max` (with outstanding
debt `B₀ ≠ 0`) the fiscal rule delivers `P₁ = P*`, and then `P₀ = P*/(β(1 + i₀))`, unaffected by
`s₀`. -/
theorem unconstrained_regime (hβ : 0 < β) (hPst : 0 < Pst)
    (h : IsEquilibrium β Pst smax Bm s0 i0 P0 P1 B0) (hB0 : B0 ≠ 0)
    (hs : surplus1 Pst smax B0 < smax) :
    P1 = Pst ∧ P0 = Pst / (β * (1 + i0)) := by
  have hi := one_add_pos hβ h
  have hf := fisher hβ h
  obtain ⟨hP0, hP1, -, -, hT⟩ := h
  have hlt : B0 / Pst < smax := by
    unfold surplus1 at hs
    rcases min_lt_iff.1 hs with h' | h'
    · exact h'
    · exact absurd h' (lt_irrefl _)
  have hs1 : surplus1 Pst smax B0 = B0 / Pst := min_eq_left hlt.le
  rw [hs1] at hT
  have hP : P1 = Pst := by
    rw [div_eq_div_iff hP1.ne' hPst.ne'] at hT
    exact (mul_left_cancel₀ hB0 (by linarith : B0 * Pst = B0 * P1)).symm
  refine ⟨hP, ?_⟩
  rw [← hP, hf]
  field_simp

/-- Cochrane (2023), §6.3, p. 194: in the constrained regime `s₁ = s^max`,
`B₋₁/P₀ = s₀ + β s^max` and `B₀/P₁ = s^max`. -/
theorem constrained_regime (hβ : 0 < β) (h : IsEquilibrium β Pst smax Bm s0 i0 P0 P1 B0)
    (hs : surplus1 Pst smax B0 = smax) :
    Bm / P0 = s0 + β * smax ∧ B0 / P1 = smax := by
  have hv := valuation hβ h
  have hT := h.2.2.2.2
  rw [hT, hs] at hv
  exact ⟨hv, hT.trans hs⟩

/-- Cochrane (2023), §6.3, p. 194: the regime boundary. With outstanding debt `B₀ ≠ 0`, positive
initial debt and a positive cap, `s₁ < s^max` iff `β(1 + i₀) B₋₁/P* - s₀ < β s^max`. -/
theorem boundary_iff (hβ : 0 < β) (hPst : 0 < Pst) (hsmax : 0 < smax) (hBm : 0 < Bm)
    (h : IsEquilibrium β Pst smax Bm s0 i0 P0 P1 B0) (hB0 : B0 ≠ 0) :
    surplus1 Pst smax B0 < smax ↔ β * (1 + i0) * Bm / Pst - s0 < β * smax := by
  have hi := one_add_pos hβ h
  have hv := valuation hβ h
  have hf := fisher hβ h
  have hP0 := h.1
  have hP1 := h.2.1
  have hT := h.2.2.2.2
  have hq : 0 < β * (1 + i0) := mul_pos hβ hi
  constructor
  · intro hs
    obtain ⟨-, hP⟩ := unconstrained_regime hβ hPst h hB0 hs
    rw [hT, hP] at hv
    have e : Bm / (Pst / (β * (1 + i0))) = β * (1 + i0) * Bm / Pst := by
      field_simp
    rw [e] at hv
    nlinarith
  · intro hc
    by_contra hns
    have hs1 : surplus1 Pst smax B0 = smax := by
      unfold surplus1 at hns ⊢
      exact min_eq_right (by
        by_contra h'
        exact hns (min_lt_iff.2 (Or.inl (lt_of_not_ge h'))))
    have hge : smax ≤ B0 / Pst := by
      unfold surplus1 at hs1
      by_contra h'
      push Not at h'
      rw [min_eq_left h'.le] at hs1
      linarith
    rw [hT, hs1] at hv
    have hB0' : B0 = P1 * smax := by
      have := hT.trans hs1
      field_simp at this
      linarith
    have hP1ge : Pst ≤ P1 := by
      rw [hB0', le_div_iff₀ hPst] at hge
      nlinarith
    have hP0ge : Pst / (β * (1 + i0)) ≤ P0 := by
      rw [div_le_iff₀ hq]
      nlinarith
    have : Bm / P0 ≤ β * (1 + i0) * Bm / Pst := by
      rw [div_le_div_iff₀ hP0 hPst]
      rw [div_le_iff₀ hq] at hP0ge
      nlinarith
    linarith

/-- Cochrane (2023), §6.3, p. 194: "a lot of outstanding debt `B₋₁`" (printed `B₁`, survey E6.4):
the economy is in the unconstrained regime iff initial debt is below the threshold
`P*(s₀ + β s^max)/(β(1 + i₀))`. -/
theorem boundary_iff_debt (hβ : 0 < β) (hPst : 0 < Pst) (hsmax : 0 < smax) (hBm : 0 < Bm)
    (h : IsEquilibrium β Pst smax Bm s0 i0 P0 P1 B0) (hB0 : B0 ≠ 0) :
    surplus1 Pst smax B0 < smax ↔ Bm < Pst * (s0 + β * smax) / (β * (1 + i0)) := by
  have hq : 0 < β * (1 + i0) := mul_pos hβ (one_add_pos hβ h)
  rw [boundary_iff hβ hPst hsmax hBm h hB0, lt_div_iff₀ hq, sub_lt_iff_lt_add,
    div_lt_iff₀ hPst]
  constructor <;> intro h' <;> nlinarith

/-- Cochrane (2023), §6.3, p. 194: the global price-level formula
`P₀ = max(P*/(β(1 + i₀)), B₋₁/(s₀ + β s^max))`. -/
noncomputable def price0 (β Pst smax Bm s0 i0 : ℝ) : ℝ :=
  max (Pst / (β * (1 + i0))) (Bm / (s0 + β * smax))

/-- Cochrane (2023), §6.3, p. 194: the date-1 price level implied by the formula,
`P₁ = β(1 + i₀) P₀`. -/
noncomputable def price1 (β Pst smax Bm s0 i0 : ℝ) : ℝ :=
  β * (1 + i0) * price0 β Pst smax Bm s0 i0

/-- Cochrane (2023), §6.3, p. 194: in the unconstrained region the formula gives
`P₀ = P*/(β(1 + i₀))`. -/
theorem price0_eq_left (hq : 0 < β * (1 + i0)) (hPst : 0 < Pst) (hpos : 0 < s0 + β * smax)
    (hc : β * (1 + i0) * Bm / Pst - s0 ≤ β * smax) :
    price0 β Pst smax Bm s0 i0 = Pst / (β * (1 + i0)) := by
  unfold price0
  refine max_eq_left ?_
  rw [div_le_div_iff₀ hpos hq]
  rw [sub_le_iff_le_add, div_le_iff₀ hPst] at hc
  nlinarith

/-- Cochrane (2023), §6.3, p. 194: in the constrained region the formula gives
`P₀ = B₋₁/(s₀ + β s^max)`. -/
theorem price0_eq_right (hq : 0 < β * (1 + i0)) (hPst : 0 < Pst) (hpos : 0 < s0 + β * smax)
    (hc : β * smax ≤ β * (1 + i0) * Bm / Pst - s0) :
    price0 β Pst smax Bm s0 i0 = Bm / (s0 + β * smax) := by
  unfold price0
  refine max_eq_right ?_
  rw [div_le_div_iff₀ hq hpos]
  rw [le_sub_iff_add_le, le_div_iff₀ hPst] at hc
  nlinarith

/-- Cochrane (2023), §6.3, p. 194: every equilibrium with outstanding debt `B₀ ≠ 0` has
`P₀ = max(P*/(β(1 + i₀)), B₋₁/(s₀ + β s^max))`: the two regimes of §2.5.1 emerge endogenously
from one formula. -/
theorem eq_price0 (hβ : 0 < β) (hPst : 0 < Pst) (hsmax : 0 < smax) (hBm : 0 < Bm)
    (h : IsEquilibrium β Pst smax Bm s0 i0 P0 P1 B0) (hB0 : B0 ≠ 0) :
    P0 = price0 β Pst smax Bm s0 i0 := by
  have hi := one_add_pos hβ h
  have hq : 0 < β * (1 + i0) := mul_pos hβ hi
  have hv := valuation hβ h
  have hP0 := h.1
  have hT := h.2.2.2.2
  have hs1le : surplus1 Pst smax B0 ≤ smax := min_le_right _ _
  have hpos : 0 < s0 + β * smax := by
    have : 0 < Bm / P0 := div_pos hBm hP0
    rw [hT] at hv
    nlinarith
  by_cases hs : surplus1 Pst smax B0 < smax
  · have hc := (boundary_iff hβ hPst hsmax hBm h hB0).1 hs
    rw [price0_eq_left hq hPst hpos hc.le]
    exact (unconstrained_regime hβ hPst h hB0 hs).2
  · have hs1 : surplus1 Pst smax B0 = smax := le_antisymm hs1le (not_lt.1 hs)
    have hc : β * smax ≤ β * (1 + i0) * Bm / Pst - s0 := by
      by_contra h'
      exact hs ((boundary_iff hβ hPst hsmax hBm h hB0).2 (lt_of_not_ge h'))
    rw [price0_eq_right hq hPst hpos hc]
    have := (constrained_regime hβ h hs1).1
    field_simp at this ⊢
    linarith

/-- Cochrane (2023), §6.3, p. 194: when `s₀ + β s^max > 0` the formula is an equilibrium price
level: with `P₁ = β(1 + i₀) P₀` and `B₀ = P₁ (B₋₁/P₀ - s₀)/β` all conditions hold. -/
theorem isEquilibrium_price0 (hβ : 0 < β) (hPst : 0 < Pst) (hBm : 0 < Bm)
    (hsmax : 0 ≤ smax) (hi : 0 < 1 + i0) (hpos : 0 < s0 + β * smax) :
    IsEquilibrium β Pst smax Bm s0 i0 (price0 β Pst smax Bm s0 i0)
      (price1 β Pst smax Bm s0 i0)
      (price1 β Pst smax Bm s0 i0 * ((Bm / price0 β Pst smax Bm s0 i0 - s0) / β)) := by
  have hq : 0 < β * (1 + i0) := mul_pos hβ hi
  set F := price0 β Pst smax Bm s0 i0 with hF
  have hFpos : 0 < F := lt_of_lt_of_le (div_pos hPst hq) (le_max_left _ _)
  have hP1pos : 0 < β * (1 + i0) * F := mul_pos hq hFpos
  have hP1 : price1 β Pst smax Bm s0 i0 = β * (1 + i0) * F := rfl
  rw [hP1, isEquilibrium_iff hβ hFpos hP1pos hi]
  have hB : β * (1 + i0) * F * ((Bm / F - s0) / β) / (β * (1 + i0) * F) = (Bm / F - s0) / β := by
    field_simp
  refine ⟨rfl, ?_, ?_⟩
  · rw [hB]
    unfold surplus1
    by_cases hc : β * (1 + i0) * Bm / Pst - s0 ≤ β * smax
    · have hFe : F = Pst / (β * (1 + i0)) := price0_eq_left hq hPst hpos hc
      have e1 : (Bm / F - s0) / β = (β * (1 + i0) * Bm / Pst - s0) / β := by
        rw [hFe]; field_simp
      have e2 : β * (1 + i0) * F * ((Bm / F - s0) / β) / Pst = (Bm / F - s0) / β := by
        rw [hFe]; field_simp
      rw [e2]
      refine (min_eq_left ?_).symm
      rw [e1, div_le_iff₀ hβ]
      linarith
    · push Not at hc
      have hFe : F = Bm / (s0 + β * smax) := price0_eq_right hq hPst hpos hc.le
      have e1 : (Bm / F - s0) / β = smax := by
        rw [hFe]; field_simp; ring
      rw [e1]
      refine (min_eq_right ?_).symm
      have hFge : Pst / (β * (1 + i0)) ≤ F := le_max_left _ _
      rw [div_le_iff₀ hq] at hFge
      rw [le_div_iff₀ hPst]
      nlinarith [mul_le_mul_of_nonneg_left hFge hsmax]
  · rw [hB]
    field_simp
    ring

/-- Cochrane (2023), §6.3, p. 194: an equilibrium exists iff `s₀ + β s^max > 0`: if even the
maximal future surplus cannot cover the debt left after `s₀`, no price level works. -/
theorem exists_equilibrium_iff (hβ : 0 < β) (hPst : 0 < Pst) (hBm : 0 < Bm)
    (hsmax : 0 ≤ smax) (hi : 0 < 1 + i0) :
    (∃ P0 P1 B0, IsEquilibrium β Pst smax Bm s0 i0 P0 P1 B0) ↔ 0 < s0 + β * smax := by
  constructor
  · rintro ⟨P0, P1, B0, h⟩
    have hv := valuation hβ h
    have hT := h.2.2.2.2
    have hle : surplus1 Pst smax B0 ≤ smax := min_le_right _ _
    have : 0 < Bm / P0 := div_pos hBm h.1
    rw [hT] at hv
    nlinarith
  · intro hpos
    exact ⟨_, _, _, isEquilibrium_price0 hβ hPst hBm hsmax hi hpos⟩

/-- Cochrane (2023), §6.3, p. 194: uniqueness: any two equilibria with outstanding debt have the
same price levels. -/
theorem price0_unique (hβ : 0 < β) (hPst : 0 < Pst) (hsmax : 0 < smax) (hBm : 0 < Bm)
    {P0' P1' B0' : ℝ} (h : IsEquilibrium β Pst smax Bm s0 i0 P0 P1 B0) (hB0 : B0 ≠ 0)
    (h' : IsEquilibrium β Pst smax Bm s0 i0 P0' P1' B0') (hB0' : B0' ≠ 0) :
    P0 = P0' ∧ P1 = P1' := by
  have e := (eq_price0 hβ hPst hsmax hBm h hB0).trans
    (eq_price0 hβ hPst hsmax hBm h' hB0').symm
  refine ⟨e, ?_⟩
  rw [fisher hβ h, fisher hβ h', e]

/-- Cochrane (2023), §6.3, p. 194 (imprecision): with `s₀ > 0` there is also an equilibrium with
no outstanding debt, `B₀ = 0`: `P₀ = B₋₁/s₀`, `P₁ = β(1 + i₀) B₋₁/s₀`, `s₁ = 0`. -/
theorem degenerate_equilibrium (hβ : 0 < β) (hBm : 0 < Bm) (hs0 : 0 < s0) (hi : 0 < 1 + i0)
    (hsmax : 0 ≤ smax) :
    IsEquilibrium β Pst smax Bm s0 i0 (Bm / s0) (β * (1 + i0) * (Bm / s0)) 0 := by
  refine ⟨div_pos hBm hs0, mul_pos (mul_pos hβ hi) (div_pos hBm hs0), ?_, ?_, ?_⟩
  · rw [zero_div, add_zero, div_mul_cancel₀ _ hs0.ne']
  · field_simp
  · unfold surplus1
    simp [hsmax]

/-- Cochrane (2023), §6.3, p. 194 (imprecision): the degenerate `B₀ = 0` equilibrium has
`s₁ = 0 < s^max`, yet its `P₀` differs from the formula (and so `P₁ ≠ P*`) unless
`s₀ = β(1 + i₀) B₋₁/P*` exactly. -/
theorem degenerate_price0_ne (hβ : 0 < β) (hPst : 0 < Pst) (hsmax : 0 < smax) (hBm : 0 < Bm)
    (hs0 : 0 < s0) (hi : 0 < 1 + i0) (hne : s0 ≠ β * (1 + i0) * Bm / Pst) :
    Bm / s0 ≠ price0 β Pst smax Bm s0 i0 := by
  have hq : 0 < β * (1 + i0) := mul_pos hβ hi
  have hpos : 0 < s0 + β * smax := by nlinarith
  by_cases hc : β * (1 + i0) * Bm / Pst - s0 ≤ β * smax
  · rw [price0_eq_left hq hPst hpos hc]
    intro h
    apply hne
    field_simp at h ⊢
    linarith
  · push Not at hc
    rw [price0_eq_right hq hPst hpos hc.le]
    intro h
    field_simp at h
    nlinarith

/-- Cochrane (2023), §6.3, p. 194: larger deficits (lower `s₀`) weakly raise `P₀`: the formula is
antitone in `s₀` on `s₀ + β s^max > 0`. -/
theorem price0_antitoneOn_s0 (hBm : 0 ≤ Bm) (Pst i0 : ℝ) :
    AntitoneOn (fun s => price0 β Pst smax Bm s i0) (Set.Ioi (-(β * smax))) := by
  intro a ha b hb hab
  have ha' : 0 < a + β * smax := by have : -(β * smax) < a := ha; linarith
  have hb' : 0 < b + β * smax := by have : -(β * smax) < b := hb; linarith
  unfold price0
  refine max_le_max le_rfl ?_
  exact div_le_div_of_nonneg_left hBm ha' (by linarith)

/-- Cochrane (2023), §6.3, p. 194: a higher interest-rate target weakly lowers `P₀`. -/
theorem price0_antitoneOn_i0 (hβ : 0 < β) (hPst : 0 ≤ Pst) (smax Bm s0 : ℝ) :
    AntitoneOn (fun i => price0 β Pst smax Bm s0 i) (Set.Ioi (-1)) := by
  intro a ha b hb hab
  have ha' : 0 < 1 + a := by have : -1 < a := ha; linarith
  unfold price0
  refine max_le_max ?_ le_rfl
  exact div_le_div_of_nonneg_left hPst (mul_pos hβ ha') (by nlinarith)

/-- Cochrane (2023), §6.3, p. 194: more initial debt weakly raises `P₀`. -/
theorem price0_monotone_debt (hpos : 0 < s0 + β * smax) (Pst i0 : ℝ) :
    Monotone (fun B => price0 β Pst smax B s0 i0) := by
  intro a b hab
  unfold price0
  exact max_le_max le_rfl (div_le_div_of_nonneg_right hab hpos.le)

/-- Cochrane (2023), §6.3, p. 194: `P₁ = max(P*, β(1 + i₀) B₋₁/(s₀ + β s^max))` weakly rises with
the interest-rate target. -/
theorem price1_monotoneOn_i0 (hβ : 0 < β) (hBm : 0 ≤ Bm) (hpos : 0 < s0 + β * smax)
    (Pst : ℝ) : MonotoneOn (fun i => price1 β Pst smax Bm s0 i) (Set.Ioi (-1)) := by
  have key : ∀ i, -1 < i → price1 β Pst smax Bm s0 i =
      max Pst (β * (1 + i) * Bm / (s0 + β * smax)) := by
    intro i hi
    have hq : 0 < β * (1 + i) := mul_pos hβ (by linarith)
    have hi' : 1 + i ≠ 0 := by linarith
    unfold price1 price0
    rw [mul_max_of_nonneg _ _ hq.le]
    congr 1
    · field_simp
    · ring
  intro a ha b hb hab
  simp only
  rw [key a ha, key b hb]
  refine max_le_max le_rfl ?_
  apply div_le_div_of_nonneg_right _ hpos.le
  have : 0 ≤ β * Bm := mul_nonneg hβ.le hBm
  nlinarith

/-- Cochrane (2023), §6.3, p. 194: the formula is continuous in `s₀` (no jump at the regime
switch). -/
theorem continuousOn_price0_s0 (β Pst smax Bm i0 : ℝ) :
    ContinuousOn (fun s => price0 β Pst smax Bm s i0) (Set.Ioi (-(β * smax))) := by
  unfold price0
  refine ContinuousOn.sup continuousOn_const ?_
  refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
  intro s hs
  have : -(β * smax) < s := hs
  linarith

/-- Cochrane (2023), §6.3, p. 194: the formula is continuous in `i₀` on `i₀ > -1`. -/
theorem continuousOn_price0_i0 (hβ : 0 < β) (Pst smax Bm s0 : ℝ) :
    ContinuousOn (fun i => price0 β Pst smax Bm s0 i) (Set.Ioi (-1)) := by
  unfold price0
  refine ContinuousOn.sup ?_ continuousOn_const
  refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
  intro i hi
  have : -1 < i := hi
  exact (mul_pos hβ (by linarith)).ne'

/-- Cochrane (2023), §6.3, p. 194: in the interior of the unconstrained region, deficits have no
effect on `P₀`: `∂P₀/∂s₀ = 0`. -/
theorem hasDerivAt_price0_s0_unconstrained (hβ : 0 < β) (hPst : 0 < Pst) (hi : 0 < 1 + i0)
    (hpos : 0 < s0 + β * smax) (hc : β * (1 + i0) * Bm / Pst - s0 < β * smax) :
    HasDerivAt (fun s => price0 β Pst smax Bm s i0) 0 s0 := by
  have hq : 0 < β * (1 + i0) := mul_pos hβ hi
  refine (hasDerivAt_const s0 (Pst / (β * (1 + i0)))).congr_of_eventuallyEq ?_
  have h1 : ∀ᶠ s in 𝓝 s0, β * (1 + i0) * Bm / Pst - s < β * smax :=
    ContinuousAt.eventually_lt (by fun_prop) continuousAt_const hc
  have h2 : ∀ᶠ s in 𝓝 s0, 0 < s + β * smax :=
    ContinuousAt.eventually_lt continuousAt_const (by fun_prop) hpos
  filter_upwards [h1, h2] with s hs1 hs2
  exact price0_eq_left hq hPst hs2 hs1.le

/-- Cochrane (2023), §6.3, p. 194: in the interior of the unconstrained region, raising the
interest-rate target lowers `P₀`: `∂P₀/∂i₀ = -P*/(β(1 + i₀)²) < 0`. -/
theorem hasDerivAt_price0_i0_unconstrained (hβ : 0 < β) (hPst : 0 < Pst) (hi : 0 < 1 + i0)
    (hpos : 0 < s0 + β * smax) (hc : β * (1 + i0) * Bm / Pst - s0 < β * smax) :
    HasDerivAt (fun i => price0 β Pst smax Bm s0 i) (-(Pst / (β * (1 + i0) ^ 2))) i0 ∧
      -(Pst / (β * (1 + i0) ^ 2)) < 0 := by
  refine ⟨?_, by have := div_pos hPst (mul_pos hβ (pow_pos hi 2)); linarith⟩
  have hd : HasDerivAt (fun i => Pst / (β * (1 + i))) (-(Pst / (β * (1 + i0) ^ 2))) i0 := by
    have h1 : HasDerivAt (fun i => β * (1 + i)) β i0 := by
      simpa using ((hasDerivAt_id' i0).const_add 1).const_mul β
    have := (hasDerivAt_const i0 Pst).div h1 (mul_pos hβ hi).ne'
    refine this.congr_deriv ?_
    field_simp
    ring
  refine hd.congr_of_eventuallyEq ?_
  have h1 : ∀ᶠ i in 𝓝 i0, β * (1 + i) * Bm / Pst - s0 < β * smax :=
    ContinuousAt.eventually_lt (by fun_prop) continuousAt_const hc
  have h2 : ∀ᶠ i in 𝓝 i0, 0 < 1 + i :=
    ContinuousAt.eventually_lt continuousAt_const (by fun_prop) hi
  filter_upwards [h1, h2] with i hi1 hi2
  exact price0_eq_left (mul_pos hβ hi2) hPst hpos hi1.le

/-- Cochrane (2023), §6.3, p. 194: in the interior of the unconstrained region the interest rate
leaves `P₁ = P*` alone: `∂P₁/∂i₀ = 0`. -/
theorem hasDerivAt_price1_i0_unconstrained (hβ : 0 < β) (hPst : 0 < Pst) (hi : 0 < 1 + i0)
    (hpos : 0 < s0 + β * smax) (hc : β * (1 + i0) * Bm / Pst - s0 < β * smax) :
    HasDerivAt (fun i => price1 β Pst smax Bm s0 i) 0 i0 := by
  refine (hasDerivAt_const i0 Pst).congr_of_eventuallyEq ?_
  have h1 : ∀ᶠ i in 𝓝 i0, β * (1 + i) * Bm / Pst - s0 < β * smax :=
    ContinuousAt.eventually_lt (by fun_prop) continuousAt_const hc
  have h2 : ∀ᶠ i in 𝓝 i0, 0 < 1 + i :=
    ContinuousAt.eventually_lt continuousAt_const (by fun_prop) hi
  filter_upwards [h1, h2] with i hi1 hi2
  have hq : 0 < β * (1 + i) := mul_pos hβ hi2
  unfold price1
  rw [price0_eq_left hq hPst hpos hi1.le]
  field_simp

/-- Cochrane (2023), §6.3, p. 194: in the interior of the constrained region deficits flow into
`P₀`: `∂P₀/∂s₀ = -B₋₁/(s₀ + β s^max)² < 0`. -/
theorem hasDerivAt_price0_s0_constrained (hβ : 0 < β) (hPst : 0 < Pst) (hi : 0 < 1 + i0)
    (hBm : 0 < Bm) (hpos : 0 < s0 + β * smax)
    (hc : β * smax < β * (1 + i0) * Bm / Pst - s0) :
    HasDerivAt (fun s => price0 β Pst smax Bm s i0) (-(Bm / (s0 + β * smax) ^ 2)) s0 ∧
      -(Bm / (s0 + β * smax) ^ 2) < 0 := by
  have hq : 0 < β * (1 + i0) := mul_pos hβ hi
  refine ⟨?_, by have := div_pos hBm (pow_pos hpos 2); linarith⟩
  have hd : HasDerivAt (fun s => Bm / (s + β * smax)) (-(Bm / (s0 + β * smax) ^ 2)) s0 := by
    have h1 : HasDerivAt (fun s => s + β * smax) 1 s0 := (hasDerivAt_id' s0).add_const _
    have := (hasDerivAt_const s0 Bm).div h1 hpos.ne'
    refine this.congr_deriv ?_
    field_simp
    ring
  refine hd.congr_of_eventuallyEq ?_
  have h1 : ∀ᶠ s in 𝓝 s0, β * smax < β * (1 + i0) * Bm / Pst - s :=
    ContinuousAt.eventually_lt continuousAt_const (by fun_prop) hc
  have h2 : ∀ᶠ s in 𝓝 s0, 0 < s + β * smax :=
    ContinuousAt.eventually_lt continuousAt_const (by fun_prop) hpos
  filter_upwards [h1, h2] with s hs1 hs2
  exact price0_eq_right hq hPst hs2 hs1.le

/-- Cochrane (2023), §6.3, p. 194: in the interior of the constrained region the interest rate has
no effect on `P₀`: `∂P₀/∂i₀ = 0`. -/
theorem hasDerivAt_price0_i0_constrained (hβ : 0 < β) (hPst : 0 < Pst) (hi : 0 < 1 + i0)
    (hpos : 0 < s0 + β * smax) (hc : β * smax < β * (1 + i0) * Bm / Pst - s0) :
    HasDerivAt (fun i => price0 β Pst smax Bm s0 i) 0 i0 := by
  refine (hasDerivAt_const i0 (Bm / (s0 + β * smax))).congr_of_eventuallyEq ?_
  have h1 : ∀ᶠ i in 𝓝 i0, β * smax < β * (1 + i) * Bm / Pst - s0 :=
    ContinuousAt.eventually_lt continuousAt_const (by fun_prop) hc
  have h2 : ∀ᶠ i in 𝓝 i0, 0 < 1 + i :=
    ContinuousAt.eventually_lt continuousAt_const (by fun_prop) hi
  filter_upwards [h1, h2] with i hi1 hi2
  exact price0_eq_right (mul_pos hβ hi2) hPst hpos hi1.le

/-- Cochrane (2023), §6.3, p. 194: in the interior of the constrained region a higher interest
rate "just increases inflation `P₁`": `∂P₁/∂i₀ = β B₋₁/(s₀ + β s^max) > 0`. -/
theorem hasDerivAt_price1_i0_constrained (hβ : 0 < β) (hPst : 0 < Pst) (hi : 0 < 1 + i0)
    (hBm : 0 < Bm) (hpos : 0 < s0 + β * smax)
    (hc : β * smax < β * (1 + i0) * Bm / Pst - s0) :
    HasDerivAt (fun i => price1 β Pst smax Bm s0 i) (β * (Bm / (s0 + β * smax))) i0 ∧
      0 < β * (Bm / (s0 + β * smax)) := by
  refine ⟨?_, mul_pos hβ (div_pos hBm hpos)⟩
  have hd : HasDerivAt (fun i => β * (1 + i) * (Bm / (s0 + β * smax)))
      (β * (Bm / (s0 + β * smax))) i0 := by
    simpa using (((hasDerivAt_id' i0).const_add 1).const_mul β).mul_const
      (Bm / (s0 + β * smax))
  refine hd.congr_of_eventuallyEq ?_
  have h1 : ∀ᶠ i in 𝓝 i0, β * smax < β * (1 + i) * Bm / Pst - s0 :=
    ContinuousAt.eventually_lt continuousAt_const (by fun_prop) hc
  have h2 : ∀ᶠ i in 𝓝 i0, 0 < 1 + i :=
    ContinuousAt.eventually_lt continuousAt_const (by fun_prop) hi
  filter_upwards [h1, h2] with i hi1 hi2
  unfold price1
  rw [price0_eq_right (mul_pos hβ hi2) hPst hpos hi1.le]

end Cochrane.FiscalConstraints.Crash
