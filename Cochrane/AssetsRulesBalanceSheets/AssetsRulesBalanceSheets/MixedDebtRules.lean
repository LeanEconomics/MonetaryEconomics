/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.FiscalTaylor
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Fiscal rules with nominal debt

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.3.5
"Fiscal rules with nominal debt", p. 271.

With real debt `b_{T−1}` and nominal debt `B_{T−1} > 0` outstanding, the one-period valuation
equation is `b_{T−1} + B_{T−1}/P_T = s(P_T)`.

## Main results

* `price_unique`: if `s` is nondecreasing on positive prices (in particular if `s` is constant —
  "a surplus rule is not strictly needed"), there is at most one positive price level;
  `multiplicity_needs_decreasing`: two distinct solutions force `s` to fall between them;
  `multiplicity_example`: with `s(P) = b + B/P` (strictly decreasing) every price level solves.
* `hasDerivAt_value`, `elasticity_value`: the elasticity of the debt value with respect to `P`
  is minus the nominal share; `ten_percent_rise`, `ten_percent_fall`: with a nominal share of
  10%, a 10% rise (fall) in `P` changes the value of the debt by `1/110 ≈ 0.91%`
  (`1/90 ≈ 1.11%`) — the book's "1%" is the first-order (elasticity) statement.
* `shock_decomposition`, `devaluationShare_strictAnti`: a surplus shock `ε` is met partly by
  inflating away nominal debt and partly by the induced fiscal tightening `γ (P₁ − P₀)`; the share
  met by devaluation, `k/(γ + k)`, falls as the surplus response `γ = s'(P)` rises.
-/

namespace Cochrane.AssetsRulesBalanceSheets.MixedDebtRules

/-- Cochrane (2023), §9.3.5, p. 271: with `B > 0` the real value `b + B/P` of the debt is strictly
decreasing in the price level. -/
theorem value_strictAntiOn {b B : ℝ} (hB : 0 < B) :
    StrictAntiOn (fun P => b + B / P) (Set.Ioi 0) := by
  intro P₁ h₁ P₂ h₂ hlt
  simp only [Set.mem_Ioi] at h₁ h₂
  simp only [add_lt_add_iff_left]
  exact div_lt_div_of_pos_left hB h₁ hlt

/-- Cochrane (2023), §9.3.5, p. 271 ("ruling out the passive possibility, which requires
`s'(P) < 0`, the price level is determined"): with nominal debt `B > 0` and a surplus that does
not fall with the price level, `b + B/P = s(P)` has at most one positive solution. -/
theorem price_unique {b B : ℝ} (hB : 0 < B) {s : ℝ → ℝ} (hs : MonotoneOn s (Set.Ioi 0))
    {P₁ P₂ : ℝ} (h₁ : 0 < P₁) (h₂ : 0 < P₂) (e₁ : b + B / P₁ = s P₁) (e₂ : b + B / P₂ = s P₂) :
    P₁ = P₂ := by
  have hf : StrictMonoOn (fun P => s P - B / P) (Set.Ioi 0) := fun P₁ h₁ P₂ h₂ hlt => by
    have h1 := value_strictAntiOn (b := 0) hB h₁ h₂ hlt
    have h2 := hs h₁ h₂ hlt.le
    simp only [zero_add] at h1
    change s P₁ - B / P₁ < s P₂ - B / P₂
    linarith
  exact PresentValue.price_unique_of_strictMonoOn (b := b) hf h₁ h₂
    (by linarith) (by linarith)

/-- Cochrane (2023), §9.3.5, p. 271 ("with any nominal debt, a surplus rule is not strictly needed
for determinacy"): with a constant surplus the positive price level is unique. -/
theorem price_unique_const {b B s : ℝ} (hB : 0 < B) {P₁ P₂ : ℝ} (h₁ : 0 < P₁) (h₂ : 0 < P₂)
    (e₁ : b + B / P₁ = s) (e₂ : b + B / P₂ = s) : P₁ = P₂ :=
  price_unique (s := fun _ => s) hB (fun _ _ _ _ _ => le_rfl) h₁ h₂ e₁ e₂

/-- Cochrane (2023), §9.3.5, p. 271: multiplicity requires `s` to fall with the price level — if
`P₁ < P₂` both solve the valuation equation, then `s(P₂) < s(P₁)`. -/
theorem multiplicity_needs_decreasing {b B : ℝ} (hB : 0 < B) {s : ℝ → ℝ} {P₁ P₂ : ℝ}
    (h₁ : 0 < P₁) (hlt : P₁ < P₂) (e₁ : b + B / P₁ = s P₁) (e₂ : b + B / P₂ = s P₂) :
    s P₂ < s P₁ := by
  have h := value_strictAntiOn (b := b) hB (Set.mem_Ioi.mpr h₁)
    (Set.mem_Ioi.mpr (h₁.trans hlt)) hlt
  simp only at h
  linarith

/-- Cochrane (2023), §9.3.5, p. 271: the passive possibility does occur when `s' < 0` — with
`s(P) = b + B/P`, which is strictly decreasing, every positive price level solves. -/
theorem multiplicity_example {b B : ℝ} (hB : 0 < B) :
    StrictAntiOn (fun P => b + B / P) (Set.Ioi 0) ∧
      ∀ P, 0 < P → b + B / P = (fun P => b + B / P) P :=
  ⟨value_strictAntiOn hB, fun _ _ => rfl⟩

/-- Cochrane (2023), §9.3.5, p. 271: the derivative of the debt value, `d(b + B/P)/dP = −B/P²`. -/
theorem hasDerivAt_value (b B : ℝ) {P : ℝ} (hP : P ≠ 0) :
    HasDerivAt (fun P => b + B / P) (-(B / P ^ 2)) P := by
  have h := HasDerivAt.const_add b (HasDerivAt.const_mul B (hasDerivAt_inv hP))
  have e : (fun P : ℝ => b + B / P) = fun y => b + B * y⁻¹ := by
    funext y
    rw [div_eq_mul_inv]
  rw [e]
  exact HasDerivAt.congr_deriv h (by field_simp)

/-- Cochrane (2023), §9.3.5, p. 271: the elasticity of the debt value with respect to the price
level is minus the nominal share, `P V'(P)/V(P) = −(B/P)/(b + B/P)`. -/
theorem elasticity_value (b B : ℝ) {P : ℝ} (hP : P ≠ 0) :
    P * (-(B / P ^ 2)) / (b + B / P) = -((B / P) / (b + B / P)) := by
  rw [show P * (-(B / P ^ 2)) = -(B / P) by field_simp]
  ring

/-- Cochrane (2023), §9.3.5, p. 271 ("if nominal debt is only 10% of all debt, then a 10% change
in the price level only affects the value of government bonds by 1%"): with nominal share
`1/10`, a 10% rise in `P` lowers the debt value by exactly `1/110` of its value. -/
theorem ten_percent_rise {b B P : ℝ} (hP : 0 < P) (hV : b + B / P ≠ 0)
    (hshare : B / P = (1 / 10) * (b + B / P)) :
    ((b + B / P) - (b + B / (11 / 10 * P))) / (b + B / P) = 1 / 110 := by
  have h1 : B / (11 / 10 * P) = (10 / 11) * (B / P) := by
    field_simp
  rw [h1, show b + B / P - (b + 10 / 11 * (B / P)) = (1 / 11) * (B / P) by ring, div_eq_iff hV]
  linarith

/-- Cochrane (2023), §9.3.5, p. 271: with nominal share `1/10`, a 10% fall in `P` raises the debt
value by exactly `1/90` of its value. -/
theorem ten_percent_fall {b B P : ℝ} (hP : 0 < P) (hV : b + B / P ≠ 0)
    (hshare : B / P = (1 / 10) * (b + B / P)) :
    ((b + B / (9 / 10 * P)) - (b + B / P)) / (b + B / P) = 1 / 90 := by
  have h1 : B / (9 / 10 * P) = (10 / 9) * (B / P) := by
    field_simp
  rw [h1, show b + 10 / 9 * (B / P) - (b + B / P) = (1 / 9) * (B / P) by ring, div_eq_iff hV]
  linarith

/-- Cochrane (2023), §9.3.5, p. 271 ("the stronger `s'(P)`, the more that inflationary fiscal
shocks are met by an induced fiscal tightening, and the less they are met by inflating away
outstanding nominal government debt"): with the rule `s(P) = s₀ + γ (P − P*)`, a surplus shock `ε`
moves the price level from `P₀` to `P₁` with `(P₁ − P₀)(γ + B/(P₀P₁)) = −ε`; the shock is split into
debt devaluation `B/P₀ − B/P₁` and fiscal tightening `γ (P₁ − P₀)`. -/
theorem shock_decomposition {b B s0 γ Pstar ε P₀ P₁ : ℝ} (h₀ : 0 < P₀) (h₁ : 0 < P₁)
    (e₀ : b + B / P₀ = s0 + γ * (P₀ - Pstar)) (e₁ : b + B / P₁ = s0 + ε + γ * (P₁ - Pstar)) :
    (P₁ - P₀) * (γ + B / (P₀ * P₁)) = -ε ∧
      ε = (B / P₁ - B / P₀) - γ * (P₁ - P₀) ∧ B / P₀ - B / P₁ = B / (P₀ * P₁) * (P₁ - P₀) := by
  have hdev : B / P₀ - B / P₁ = B / (P₀ * P₁) * (P₁ - P₀) := by
    field_simp
  refine ⟨?_, by linarith, hdev⟩
  have : ε = (B / P₁ - B / P₀) - γ * (P₁ - P₀) := by linarith
  rw [this]
  linear_combination -hdev

/-- Cochrane (2023), §9.3.5, p. 271: the share of a fiscal shock met by devaluing nominal debt,
`k/(γ + k)` with `k = B/(P₀P₁) > 0`. -/
noncomputable def devaluationShare (k γ : ℝ) : ℝ := k / (γ + k)

/-- Cochrane (2023), §9.3.5, p. 271: the devaluation share falls strictly as the surplus response
`γ ≥ 0` rises. -/
theorem devaluationShare_strictAnti {k : ℝ} (hk : 0 < k) :
    StrictAntiOn (devaluationShare k) (Set.Ici 0) := by
  intro γ₁ h₁ γ₂ h₂ hlt
  simp only [Set.mem_Ici] at h₁ h₂
  unfold devaluationShare
  exact div_lt_div_of_pos_left hk (by linarith) (by linarith)

/-- Cochrane (2023), §9.3.5, p. 271: with the decomposition of `shock_decomposition`, the debt
devaluation absorbs exactly the share `k/(γ + k)` of the shock and fiscal tightening the rest. -/
theorem devaluation_part {B γ ε P₀ P₁ : ℝ} (h₀ : 0 < P₀) (h₁ : 0 < P₁) (hγ : 0 ≤ γ) (hB : 0 < B)
    (hsplit : (P₁ - P₀) * (γ + B / (P₀ * P₁)) = -ε) :
    B / P₀ - B / P₁ = -(devaluationShare (B / (P₀ * P₁)) γ * ε) ∧
      γ * (P₁ - P₀) = -((1 - devaluationShare (B / (P₀ * P₁)) γ) * ε) := by
  have hk : 0 < B / (P₀ * P₁) := by positivity
  have hne : γ + B / (P₀ * P₁) ≠ 0 := by linarith
  have hP : P₁ - P₀ = -ε / (γ + B / (P₀ * P₁)) := by
    rw [eq_div_iff hne]
    linarith
  unfold devaluationShare
  constructor
  · have hdev : B / P₀ - B / P₁ = B / (P₀ * P₁) * (P₁ - P₀) := by
      field_simp
    rw [hdev, hP]
    field_simp
  · rw [hP]
    field_simp
    ring

end Cochrane.AssetsRulesBalanceSheets.MixedDebtRules
