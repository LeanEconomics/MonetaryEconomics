/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.DebtLimitStochastic

/-!
# Managed surpluses and the determinacy of the price level: the pathwise theory

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.1, p. 197: "with an
upper limit on debt-to-GDP ratio, we must already imagine a managed surplus process. As debt
starts to grow, the government increases surpluses so as to avoid the boundary ... A plan that
exceeds the bound by a finite amount will lead to an initial price-level rise ... We are back to
global determinacy of the price level". The book specifies no surplus rule. This module specifies
the natural class and proves the path-by-path facts; `TidyR6ManagedSurplusMeasure` adds the
probability.

The debt-to-GDP ratio is `x_{t+1} = γ x_t − σ_t` (`DebtLimitStochastic.debtPath`), with
`γ = (1 + r)/(1 + g)`, `0 < γ < 1` (permanent `r < g`), and `x₀ = B/(P₀ y₀)` set by the initial
price level. A *surplus rule* is `σ_t = F_t(x_t, ω)`, such as the linear rule
`s̄ + u_t + φ (x_t − b̄)` (`linRule`). Its *boundary-avoiding modification* raises the surplus
just enough to keep debt at or below the limit `x̄`: `x_{t+1} = min x̄ (γ x_t − F_t(x_t))`
(`avoidPath`, `avoidSurplus`); the two-sided version also cuts surpluses at a floor `x_{low}`
(`bandPath`, `bandSurplus`); the capped version respects a fiscal capacity `s_{max}`
(`cappedPath`, `cappedSurplus`).

Two readings of "the government manages surpluses":

* **feedback**: the rule responds to the *actual* debt, including debt revalued by the price
  level. Then every initial debt `x₀ ≤ x̄` is sustained on every path
  (`avoidPath_within_iff`, `bandPath_within_iff`, `cappedPath_within_iff`): the price level is
  NOT determined.
* **plan**: the surplus process is the one the rule generates along the government's planned
  debt path `m` from `m₀`, and does not respond to a revaluation of debt by the price level
  (the book's "absent a rise in future surpluses"). Then actual debt is
  `x_t = m_t + γᵗ (x₀ − m₀)` (`plan_debtPath`): `x₀ ≤ m₀` is sustained on every path
  (`plan_within_of_le`), while `x₀ > m₀` breaches the limit at any date the plan touches it
  (`plan_breach_high`), and `x₀ < m₀` breaches a floor the plan touches (`plan_breach_low`).

Also: `not_within_of_capacity` (no surplus rule with capacity `s_{max} < −(1 − γ) x̄` can keep
debt within the limit, on any path), `avoid_hits_of_rule_exceeds` (the modified rule touches
the limit whenever the unmodified rule would have crossed it), the link
`avoidPath_eq_managedPath` to `DebtLimitStochastic.managedPath`, and the price-level conversions.
-/

namespace Cochrane.FiscalConstraints.TidyR6ManagedSurplus

open DebtLimitStochastic

variable {Ω : Type*}

/-! ### Surplus rules and their boundary-avoiding modifications -/

/-- Cochrane (2023), (6.4) p. 196 and p. 197: debt under an unmodified surplus rule
`σ_t = F_t(x_t, ω)`: `x_{t+1} = γ x_t − F_t(x_t, ω)`, `x_0 = x₀`. -/
noncomputable def rulePath (γ : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => x₀
  | t + 1 => fun ω => γ * rulePath γ F x₀ t ω - F t (rulePath γ F x₀ t ω) ω

/-- Cochrane (2023), p. 197: the linear surplus rule `s_t = s̄ + u_t + φ (x_t − b̄)`: a mean
`s̄`, a shock `u_{t}` and a response `φ` to the deviation of debt from a target `b̄`. -/
def linRule (sbar φ bbar : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) (x : ℝ) (ω : Ω) : ℝ :=
  sbar + u t ω + φ * (x - bbar)

/-- Cochrane (2023), p. 197: under the linear rule, next period's debt before any modification
is `(γ − φ) x − (s̄ − φ b̄ + u_t)`: the response `φ` lowers the effective root to `γ − φ`. -/
theorem linRule_response (γ sbar φ bbar : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) (x : ℝ) (ω : Ω) :
    γ * x - linRule sbar φ bbar u t x ω = (γ - φ) * x - (sbar - φ * bbar + u t ω) := by
  unfold linRule
  ring

/-- Cochrane (2023), p. 197 ("as debt starts to grow, the government increases surpluses so as
to avoid the boundary"): debt under the boundary-avoiding modification of the rule `F`,
`x_{t+1} = min x̄ (γ x_t − F_t(x_t, ω))`. -/
noncomputable def avoidPath (γ xbar : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => x₀
  | t + 1 => fun ω =>
      min xbar (γ * avoidPath γ xbar F x₀ t ω - F t (avoidPath γ xbar F x₀ t ω) ω)

/-- Cochrane (2023), p. 197: the boundary-avoiding surplus, the rule plus the extra surplus
`max 0 (γ x_t − F_t(x_t) − x̄)` needed to stay at or below `x̄`. -/
noncomputable def avoidSurplus (γ xbar : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  F t (avoidPath γ xbar F x₀ t ω) ω +
    max 0 (γ * avoidPath γ xbar F x₀ t ω - F t (avoidPath γ xbar F x₀ t ω) ω - xbar)

/-- Cochrane (2023), p. 197: `min a y = y − max 0 (y − a)`, the cap as a subtracted excess. -/
theorem min_eq_sub_max (a y : ℝ) : min a y = y - max 0 (y - a) := by
  rcases le_total y a with h | h
  · rw [min_eq_right h, max_eq_left (by linarith)]
    ring
  · rw [min_eq_left h, max_eq_right (by linarith)]
    ring

/-- Cochrane (2023), (6.4) p. 196: the modified path is the debt generated by the modified
surplus, `x_{t+1} = γ x_t − σ_t`. -/
theorem avoidPath_succ_eq (γ xbar : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) (t : ℕ) (ω : Ω) :
    avoidPath γ xbar F x₀ (t + 1) ω =
      γ * avoidPath γ xbar F x₀ t ω - avoidSurplus γ xbar F x₀ t ω := by
  change min xbar _ = _
  rw [min_eq_sub_max, avoidSurplus]
  ring

/-- Cochrane (2023), p. 197: the modified surplus is the rule's surplus whenever the rule
alone stays within the limit; it departs from the rule only to avoid the boundary. -/
theorem avoidSurplus_eq_rule {γ xbar x₀ : ℝ} {F : ℕ → ℝ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (h : γ * avoidPath γ xbar F x₀ t ω - F t (avoidPath γ xbar F x₀ t ω) ω ≤ xbar) :
    avoidSurplus γ xbar F x₀ t ω = F t (avoidPath γ xbar F x₀ t ω) ω := by
  rw [avoidSurplus, max_eq_left (by linarith), add_zero]

/-- Cochrane (2023), p. 197: the modified surplus is never below the rule's surplus. -/
theorem rule_le_avoidSurplus (γ xbar : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) (t : ℕ) (ω : Ω) :
    F t (avoidPath γ xbar F x₀ t ω) ω ≤ avoidSurplus γ xbar F x₀ t ω :=
  le_add_of_nonneg_right (le_max_left _ _)

/-- Cochrane (2023), p. 197: the earlier managed path `DebtLimitStochastic.managedPath` is the
boundary-avoiding modification of the exogenous rule `σ_t = ε_t` (no feedback on debt). -/
theorem avoidPath_eq_managedPath (γ x₀ xbar : ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    avoidPath γ xbar (fun s _ ω' => ε s ω') x₀ t ω = managedPath γ x₀ xbar ε t ω := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change min xbar (γ * avoidPath γ xbar (fun s _ ω' => ε s ω') x₀ t ω - ε t ω) =
      γ * managedPath γ x₀ xbar ε t ω -
        (ε t ω + max 0 (γ * managedPath γ x₀ xbar ε t ω - ε t ω - xbar))
    rw [ih, min_eq_sub_max]
    ring

/-- Cochrane (2023), p. 197: the two-sided modification keeps debt in the band `[x_{low}, x̄]`,
`x_{t+1} = max x_{low} (min x̄ (γ x_t − F_t(x_t, ω)))`. -/
noncomputable def bandPath (γ xlow xbar : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => x₀
  | t + 1 => fun ω => max xlow
      (min xbar (γ * bandPath γ xlow xbar F x₀ t ω - F t (bandPath γ xlow xbar F x₀ t ω) ω))

/-- Cochrane (2023), p. 197: the two-sided surplus: the rule, plus the extra surplus that keeps
debt at or below `x̄`, minus the surplus cut that keeps debt at or above `x_{low}`. -/
noncomputable def bandSurplus (γ xlow xbar : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) (t : ℕ)
    (ω : Ω) : ℝ :=
  F t (bandPath γ xlow xbar F x₀ t ω) ω +
    max 0 (γ * bandPath γ xlow xbar F x₀ t ω - F t (bandPath γ xlow xbar F x₀ t ω) ω - xbar) -
    max 0 (xlow -
      min xbar (γ * bandPath γ xlow xbar F x₀ t ω - F t (bandPath γ xlow xbar F x₀ t ω) ω))

/-- Cochrane (2023), p. 197: `max l z = z + max 0 (l − z)`, the floor as an added shortfall. -/
theorem max_eq_add_max (l z : ℝ) : max l z = z + max 0 (l - z) := by
  rcases le_total l z with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring

/-- Cochrane (2023), (6.4) p. 196: the band path is the debt generated by the band surplus. -/
theorem bandPath_succ_eq (γ xlow xbar : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) (t : ℕ) (ω : Ω) :
    bandPath γ xlow xbar F x₀ (t + 1) ω =
      γ * bandPath γ xlow xbar F x₀ t ω - bandSurplus γ xlow xbar F x₀ t ω := by
  change max xlow (min xbar _) = _
  rw [max_eq_add_max, bandSurplus, min_eq_sub_max xbar]
  ring

/-- Cochrane (2023), p. 197: debt under a boundary-avoiding rule with a fiscal capacity
`s_{max}`: `x_{t+1} = max (γ x_t − s_{max}) (min x̄ (γ x_t − F_t(x_t, ω)))`. -/
noncomputable def cappedPath (γ xbar smax : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => x₀
  | t + 1 => fun ω => max (γ * cappedPath γ xbar smax F x₀ t ω - smax)
      (min xbar (γ * cappedPath γ xbar smax F x₀ t ω - F t (cappedPath γ xbar smax F x₀ t ω) ω))

/-- Cochrane (2023), p. 197: the capped boundary-avoiding surplus
`min s_{max} (max F_t(x_t) (γ x_t − x̄))`: the government raises surpluses to avoid the boundary,
but never above its capacity `s_{max}`. -/
noncomputable def cappedSurplus (γ xbar smax : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) (t : ℕ)
    (ω : Ω) : ℝ :=
  min smax (max (F t (cappedPath γ xbar smax F x₀ t ω) ω)
    (γ * cappedPath γ xbar smax F x₀ t ω - xbar))

/-- Cochrane (2023), (6.4) p. 196: the capped path is the debt generated by the capped
surplus. -/
theorem cappedPath_succ_eq (γ xbar smax : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) (t : ℕ) (ω : Ω) :
    cappedPath γ xbar smax F x₀ (t + 1) ω =
      γ * cappedPath γ xbar smax F x₀ t ω - cappedSurplus γ xbar smax F x₀ t ω := by
  change max _ (min _ _) = _
  rw [cappedSurplus]
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- Cochrane (2023), p. 197: the capped surplus respects the capacity, `σ_t ≤ s_{max}`. -/
theorem cappedSurplus_le (γ xbar smax : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) (t : ℕ) (ω : Ω) :
    cappedSurplus γ xbar smax F x₀ t ω ≤ smax :=
  min_le_left _ _

/-! ### Feedback: the rule responds to actual debt, and every debt below the limit survives -/

/-- Cochrane (2023), p. 197: the boundary-avoiding modification keeps debt at or below `x̄`
from date 1 on, for every rule, every initial debt and every path. -/
theorem avoidPath_le (γ xbar : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) (t : ℕ) (ω : Ω) :
    avoidPath γ xbar F x₀ (t + 1) ω ≤ xbar :=
  min_le_left _ _

/-- Cochrane (2023), p. 197 (**feedback rules do not determine the price level**): under the
boundary-avoiding modification of ANY rule, debt stays within the limit forever iff the
initial debt is within it, `x₀ ≤ x̄`, on every path. -/
theorem avoidPath_within_iff (γ xbar : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) (ω : Ω) :
    (∀ t, avoidPath γ xbar F x₀ t ω ≤ xbar) ↔ x₀ ≤ xbar := by
  constructor
  · intro h
    exact h 0
  · intro h t
    cases t with
    | zero => exact h
    | succ t => exact avoidPath_le γ xbar F x₀ t ω

/-- Cochrane (2023), p. 197: the two-sided modification keeps debt in `[x_{low}, x̄]` from date 1
on, when `x_{low} ≤ x̄`. -/
theorem bandPath_mem {γ xlow xbar : ℝ} (hl : xlow ≤ xbar) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) (t : ℕ)
    (ω : Ω) :
    xlow ≤ bandPath γ xlow xbar F x₀ (t + 1) ω ∧ bandPath γ xlow xbar F x₀ (t + 1) ω ≤ xbar :=
  ⟨le_max_left _ _, max_le hl (min_le_left _ _)⟩

/-- Cochrane (2023), p. 197 (**two-sided feedback rules do not determine the price level**):
debt stays in the band forever iff the initial debt is in the band, on every path. -/
theorem bandPath_within_iff {γ xlow xbar : ℝ} (hl : xlow ≤ xbar) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ)
    (ω : Ω) :
    (∀ t, xlow ≤ bandPath γ xlow xbar F x₀ t ω ∧ bandPath γ xlow xbar F x₀ t ω ≤ xbar) ↔
      xlow ≤ x₀ ∧ x₀ ≤ xbar := by
  constructor
  · intro h
    exact h 0
  · intro h t
    cases t with
    | zero => exact h
    | succ t => exact bandPath_mem hl F x₀ t ω

/-- Cochrane (2023), p. 197 (**capacity, sufficiency**): with `0 ≤ γ` and capacity
`s_{max} ≥ −(1 − γ) x̄`, the capped boundary-avoiding rule keeps debt within the limit forever iff
`x₀ ≤ x̄`, on every path and for every rule `F`. -/
theorem cappedPath_within_iff {γ xbar smax : ℝ} (hγ0 : 0 ≤ γ) (hfeas : 0 ≤ (1 - γ) * xbar + smax)
    (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) (ω : Ω) :
    (∀ t, cappedPath γ xbar smax F x₀ t ω ≤ xbar) ↔ x₀ ≤ xbar := by
  constructor
  · intro h
    exact h 0
  · intro h t
    induction t with
    | zero => exact h
    | succ t ih =>
      change max _ (min _ _) ≤ xbar
      refine max_le ?_ (min_le_left _ _)
      nlinarith [mul_le_mul_of_nonneg_left ih hγ0]

/-- Cochrane (2023), p. 197 (**capacity, necessity**): if every surplus is at most `s_{max}` and
`s_{max} < −(1 − γ) x̄`, with `γ ≤ 1`, then debt cannot stay within the limit forever, on any
path and from any initial debt: even the maximal surplus cannot service debt at the limit. -/
theorem not_within_of_capacity {γ xbar smax x₀ : ℝ} (hγ1 : γ ≤ 1)
    (hcap : (1 - γ) * xbar + smax < 0) {σ : ℕ → Ω → ℝ} {ω : Ω} (hσ : ∀ t, σ t ω ≤ smax) :
    ¬ ∀ t, debtPath γ x₀ σ t ω ≤ xbar := by
  intro h
  set δ := -((1 - γ) * xbar + smax) with hδ
  have hδ0 : 0 < δ := by linarith
  have key : ∀ t : ℕ, xbar - debtPath γ x₀ σ t ω ≤ (xbar - x₀) - t * δ := by
    intro t
    induction t with
    | zero =>
      change xbar - x₀ ≤ _
      simp
    | succ t ih =>
      rw [debtPath_succ]
      have hy := sub_nonneg.2 (h t)
      have h1 : γ * (xbar - debtPath γ x₀ σ t ω) ≤ xbar - debtPath γ x₀ σ t ω := by
        nlinarith
      have h2 := hσ t
      push_cast
      nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((xbar - x₀) / δ)
  have hk := key n
  have hy := sub_nonneg.2 (h n)
  rw [div_lt_iff₀ hδ0] at hn
  linarith

/-! ### Plans: the surplus does not respond to a revaluation of debt -/

/-- Cochrane (2023), p. 197 ("a higher value of debt, induced by deflation"): if the surplus
process `σ` is the one generated along a planned debt path `m`, `m_{t+1} = γ m_t − σ_t`, then
actual debt from `x₀` is `x_t = m_t + γᵗ (x₀ − m₀)`: a revaluation of initial debt persists,
decaying at rate `γ`. -/
theorem plan_debtPath {γ x₀ : ℝ} {m σ : ℕ → Ω → ℝ} {ω : Ω}
    (hm : ∀ t, m (t + 1) ω = γ * m t ω - σ t ω) (t : ℕ) :
    debtPath γ x₀ σ t ω = m t ω + γ ^ t * (x₀ - m 0 ω) := by
  induction t with
  | zero =>
    change x₀ = _
    ring
  | succ t ih =>
    rw [debtPath_succ, ih, hm, pow_succ]
    ring

/-- Cochrane (2023), p. 197: actual debt under the boundary-avoiding plan from `m₀`. -/
theorem avoid_plan_debtPath (γ xbar : ℝ) (F : ℕ → ℝ → Ω → ℝ) (m₀ x₀ : ℝ) (t : ℕ) (ω : Ω) :
    debtPath γ x₀ (avoidSurplus γ xbar F m₀) t ω =
      avoidPath γ xbar F m₀ t ω + γ ^ t * (x₀ - m₀) :=
  plan_debtPath (fun s => avoidPath_succ_eq γ xbar F m₀ s ω) t

/-- Cochrane (2023), p. 197: actual debt under the two-sided plan from `m₀`. -/
theorem band_plan_debtPath (γ xlow xbar : ℝ) (F : ℕ → ℝ → Ω → ℝ) (m₀ x₀ : ℝ) (t : ℕ)
    (ω : Ω) :
    debtPath γ x₀ (bandSurplus γ xlow xbar F m₀) t ω =
      bandPath γ xlow xbar F m₀ t ω + γ ^ t * (x₀ - m₀) :=
  plan_debtPath (fun s => bandPath_succ_eq γ xlow xbar F m₀ s ω) t

/-- Cochrane (2023), p. 197 (inflation is not ruled out): if the planned path stays at or below
`x̄` and initial debt is at most the planned `m₀` (a higher price level), actual debt stays at or
below `x̄` forever, for `0 ≤ γ`. -/
theorem plan_within_of_le {γ xbar x₀ : ℝ} (hγ0 : 0 ≤ γ) {m σ : ℕ → Ω → ℝ} {ω : Ω}
    (hm : ∀ t, m (t + 1) ω = γ * m t ω - σ t ω) (hle : ∀ t, m t ω ≤ xbar) (hx : x₀ ≤ m 0 ω)
    (t : ℕ) : debtPath γ x₀ σ t ω ≤ xbar := by
  rw [plan_debtPath hm]
  have h1 : γ ^ t * (x₀ - m 0 ω) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hγ0 t) (by linarith)
  linarith [hle t]

/-- Cochrane (2023), p. 197 ("a higher value of debt, induced by deflation, will push the
government over the boundary absent a rise in future surpluses"): for `0 < γ`, if initial debt
exceeds the planned `m₀`, actual debt exceeds `x̄` at every date at which the plan touches `x̄`. -/
theorem plan_breach_high {γ xbar x₀ : ℝ} (hγ : 0 < γ) {m σ : ℕ → Ω → ℝ} {ω : Ω}
    (hm : ∀ t, m (t + 1) ω = γ * m t ω - σ t ω) (hx : m 0 ω < x₀) {t : ℕ} (ht : m t ω = xbar) :
    xbar < debtPath γ x₀ σ t ω := by
  rw [plan_debtPath hm, ht]
  have : 0 < γ ^ t * (x₀ - m 0 ω) := mul_pos (pow_pos hγ t) (by linarith)
  linarith

/-- Cochrane (2023), p. 197 (the mirror image): for `0 < γ`, if initial debt is below the
planned `m₀`, actual debt falls below `x_{low}` at every date at which the plan touches
`x_{low}`. -/
theorem plan_breach_low {γ xlow x₀ : ℝ} (hγ : 0 < γ) {m σ : ℕ → Ω → ℝ} {ω : Ω}
    (hm : ∀ t, m (t + 1) ω = γ * m t ω - σ t ω) (hx : x₀ < m 0 ω) {t : ℕ} (ht : m t ω = xlow) :
    debtPath γ x₀ σ t ω < xlow := by
  rw [plan_debtPath hm, ht]
  have : γ ^ t * (x₀ - m 0 ω) < 0 := mul_neg_of_pos_of_neg (pow_pos hγ t) (by linarith)
  linarith

/-! ### When does the plan touch the limit? -/

/-- Cochrane (2023), p. 197: the boundary-avoiding modification touches the limit `x̄` at some
date `t ≥ 1` whenever the unmodified rule from the same initial debt would have reached or
crossed `x̄` at some date `t ≥ 1`: the two paths agree until the first such date. -/
theorem avoid_hits_of_rule_exceeds {γ xbar m₀ : ℝ} {F : ℕ → ℝ → Ω → ℝ} {ω : Ω}
    (h : ∃ t, 1 ≤ t ∧ xbar ≤ rulePath γ F m₀ t ω) :
    ∃ t, 1 ≤ t ∧ avoidPath γ xbar F m₀ t ω = xbar := by
  classical
  obtain ⟨T, hT, hmin⟩ : ∃ T, (1 ≤ T ∧ xbar ≤ rulePath γ F m₀ T ω) ∧
      ∀ s < T, ¬ (1 ≤ s ∧ xbar ≤ rulePath γ F m₀ s ω) :=
    ⟨Nat.find h, Nat.find_spec h, fun s hs => Nat.find_min h hs⟩
  have heq : ∀ s < T, avoidPath γ xbar F m₀ s ω = rulePath γ F m₀ s ω := by
    intro s
    induction s with
    | zero => intro _; rfl
    | succ s ih =>
      intro hs
      have ih' := ih (by omega)
      have hlt : rulePath γ F m₀ (s + 1) ω < xbar :=
        not_le.mp (not_and.mp (hmin (s + 1) hs) (by omega))
      change min xbar (γ * avoidPath γ xbar F m₀ s ω - F s (avoidPath γ xbar F m₀ s ω) ω) = _
      rw [ih']
      exact min_eq_right hlt.le
  obtain ⟨s, rfl⟩ : ∃ s, T = s + 1 := ⟨T - 1, by omega⟩
  refine ⟨s + 1, hT.1, ?_⟩
  change min xbar (γ * avoidPath γ xbar F m₀ s ω - F s (avoidPath γ xbar F m₀ s ω) ω) = xbar
  rw [heq s (by omega)]
  exact min_eq_left hT.2

/-- Cochrane (2023), p. 197: the modified path is exactly at the limit next period whenever the
rule alone would carry debt to or above it. -/
theorem avoidPath_succ_eq_xbar {γ xbar m₀ : ℝ} {F : ℕ → ℝ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (h : xbar ≤ γ * avoidPath γ xbar F m₀ t ω - F t (avoidPath γ xbar F m₀ t ω) ω) :
    avoidPath γ xbar F m₀ (t + 1) ω = xbar :=
  min_eq_left h

/-- Cochrane (2023), p. 197: the band path is at the upper edge next period whenever the rule
alone would carry debt to or above `x̄` (for `x_{low} ≤ x̄`). -/
theorem bandPath_succ_eq_xbar {γ xlow xbar m₀ : ℝ} (hl : xlow ≤ xbar) {F : ℕ → ℝ → Ω → ℝ}
    {t : ℕ} {ω : Ω}
    (h : xbar ≤ γ * bandPath γ xlow xbar F m₀ t ω - F t (bandPath γ xlow xbar F m₀ t ω) ω) :
    bandPath γ xlow xbar F m₀ (t + 1) ω = xbar := by
  change max xlow (min xbar _) = xbar
  rw [min_eq_left h, max_eq_right hl]

/-- Cochrane (2023), p. 197: the band path is at the lower edge next period whenever the rule
alone would carry debt to or below `x_{low}`. -/
theorem bandPath_succ_eq_xlow {γ xlow xbar m₀ : ℝ} {F : ℕ → ℝ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (h : γ * bandPath γ xlow xbar F m₀ t ω - F t (bandPath γ xlow xbar F m₀ t ω) ω ≤ xlow) :
    bandPath γ xlow xbar F m₀ (t + 1) ω = xlow := by
  change max xlow (min xbar _) = xlow
  exact max_eq_left ((min_le_right _ _).trans h)

/-- Cochrane (2023), p. 197: the band path stays in `[x_{low}, x̄]` at every date when it starts
there. -/
theorem bandPath_mem_all {γ xlow xbar m₀ : ℝ} (hl : xlow ≤ xbar) (hm₀ : xlow ≤ m₀ ∧ m₀ ≤ xbar)
    (F : ℕ → ℝ → Ω → ℝ) (ω : Ω) (t : ℕ) :
    xlow ≤ bandPath γ xlow xbar F m₀ t ω ∧ bandPath γ xlow xbar F m₀ t ω ≤ xbar :=
  (bandPath_within_iff hl F m₀ ω).2 hm₀ t

/-- Cochrane (2023), p. 197: for `m ∈ [l, h]`, `a m` lies between `min (a l) (a h)` and
`max (a l) (a h)`, whatever the sign of `a`. -/
theorem mul_mem_minmax {a l h m : ℝ} (hlm : l ≤ m) (hmh : m ≤ h) :
    min (a * l) (a * h) ≤ a * m ∧ a * m ≤ max (a * l) (a * h) := by
  rcases le_total 0 a with ha | ha
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hlm ha),
      (mul_le_mul_of_nonneg_left hmh ha).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hmh ha),
      (mul_le_mul_of_nonpos_left hlm ha).trans (le_max_left _ _)⟩

/-! ### Price levels -/

/-- Cochrane (2023), p. 197: with GDP `y₀ > 0` and nominal debt `B`, initial real debt
`B/(P₀ y₀)` is at most `m > 0` iff `P₀ ≥ B/(y₀ m)`: a lower bound on debt is an upper bound on
the price level and vice versa. -/
theorem debt_le_iff_price_ge {B y₀ P₀ m : ℝ} (hy : 0 < y₀) (hP : 0 < P₀)
    (hm : 0 < m) : B / (P₀ * y₀) ≤ m ↔ B / (y₀ * m) ≤ P₀ := by
  rw [div_le_iff₀ (by positivity), div_le_iff₀ (by positivity)]
  have e : m * (P₀ * y₀) = P₀ * (y₀ * m) := by ring
  rw [e]

/-- Cochrane (2023), p. 197: initial real debt `B/(P₀ y₀)` equals `m > 0` iff
`P₀ = B/(y₀ m)`. -/
theorem debt_eq_iff_price_eq {B y₀ P₀ m : ℝ} (hy : 0 < y₀) (hP : 0 < P₀) (hm : 0 < m) :
    B / (P₀ * y₀) = m ↔ P₀ = B / (y₀ * m) := by
  rw [div_eq_iff (by positivity), eq_div_iff (by positivity)]
  have e : m * (P₀ * y₀) = P₀ * (y₀ * m) := by ring
  rw [e, eq_comm]

/-- Cochrane (2023), p. 197: initial real debt `B/(P₀ y₀)` is at least `m > 0` iff
`P₀ ≤ B/(y₀ m)`. -/
theorem le_debt_iff_price_le {B y₀ P₀ m : ℝ} (hy : 0 < y₀) (hP : 0 < P₀) (hm : 0 < m) :
    m ≤ B / (P₀ * y₀) ↔ P₀ ≤ B / (y₀ * m) := by
  rw [le_div_iff₀ (by positivity), le_div_iff₀ (by positivity)]
  have e : m * (P₀ * y₀) = P₀ * (y₀ * m) := by ring
  rw [e]

/-- Cochrane (2023), p. 197: the price level `B/(y₀ m)` is positive and carries initial real
debt exactly to `m`. -/
theorem price_spec {B y₀ m : ℝ} (hB : 0 < B) (hy : 0 < y₀) (hm : 0 < m) :
    0 < B / (y₀ * m) ∧ B / (B / (y₀ * m) * y₀) = m := by
  refine ⟨by positivity, ?_⟩
  field_simp

end Cochrane.FiscalConstraints.TidyR6ManagedSurplus
