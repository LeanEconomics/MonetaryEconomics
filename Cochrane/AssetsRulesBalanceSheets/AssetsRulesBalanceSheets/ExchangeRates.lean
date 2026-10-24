/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.RealDebt

/-!
# Exchange rates under the fiscal theory (Dupor 2000, Daniel 2001b)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 24, §24.3 (p. 527), assigned to
this project by the Chapters 20–25 survey (foreign-currency debt, §8.1). Two countries issue
nominal debt `B₁`, `B₂` in their own currencies, price levels `P₁`, `P₂` of a common good, so the
exchange rate (domestic currency 1 per unit of currency 2) is `e = P₁/P₂`.

## Main results

* `separate_pools_determinate`, `separate_pools_exchange_rate`: when each country repays its own
  debt from its own surpluses (`B₁/P₁ = V₁`, `B₂/P₂ = V₂`), the price levels and the exchange
  rate are determinate, `e = (B₁/V₁)/(B₂/V₂)`, the ratio of nominal debt to the present value of
  surpluses; `exchange_rate_eq_ratio_pv` states this date by date and state by state.
* `common_pool_exchange_rate_free`, `common_pool_indeterminate`: when the two currencies are
  claims on a common pool of surpluses (`B₁/P₁ + B₂/P₂ = V`), every exchange rate `e > 0` is
  consistent with equilibrium (with unique price levels given `e`), so the exchange rate is
  indeterminate.
-/

namespace Cochrane.AssetsRulesBalanceSheets.ExchangeRates

open RealDebt PresentValue

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §24.3, p. 527 (Daniel 2001b): "When two countries with separate currencies pay
off their own debts, exchange rates are determinate": with positive debts and surplus present
values there is exactly one pair of positive price levels. -/
theorem separate_pools_determinate {B₁ B₂ V₁ V₂ : ℝ} (hB₁ : 0 < B₁) (hB₂ : 0 < B₂)
    (hV₁ : 0 < V₁) (hV₂ : 0 < V₂) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧ B₁ / p.1 = V₁ ∧ B₂ / p.2 = V₂ := by
  obtain ⟨P₁, ⟨h₁, e₁⟩, u₁⟩ := valuation_price_unique hB₁ hV₁
  obtain ⟨P₂, ⟨h₂, e₂⟩, u₂⟩ := valuation_price_unique hB₂ hV₂
  refine ⟨(P₁, P₂), ⟨h₁, h₂, e₁, e₂⟩, ?_⟩
  rintro ⟨p₁, p₂⟩ ⟨k₁, k₂, f₁, f₂⟩
  exact Prod.ext (u₁ p₁ ⟨k₁, f₁⟩) (u₂ p₂ ⟨k₂, f₂⟩)

/-- Cochrane (2023), §24.3, p. 527: with separate surplus pools the exchange rate is the ratio of
each country's nominal debt to the present value of its surpluses,
`e = P₁/P₂ = (B₁/V₁)/(B₂/V₂)`. -/
theorem separate_pools_exchange_rate {B₁ B₂ V₁ V₂ P₁ P₂ : ℝ} (hP₁ : P₁ ≠ 0) (hP₂ : P₂ ≠ 0)
    (hV₁ : V₁ ≠ 0) (hV₂ : V₂ ≠ 0) (e₁ : B₁ / P₁ = V₁) (e₂ : B₂ / P₂ = V₂) :
    P₁ / P₂ = (B₁ / V₁) / (B₂ / V₂) := by
  have h1 : P₁ = B₁ / V₁ := by rw [eq_div_iff hV₁, ← e₁]; field_simp
  have h2 : P₂ = B₂ / V₂ := by rw [eq_div_iff hV₂, ← e₂]; field_simp
  rw [h1, h2]

/-- Cochrane (2023), §24.3, p. 527, at every date and state: if each country's nominal debt is
valued by its own surpluses, `B_{i,t−1}/P_{i,t} = E_t ∑ βʲ s_{i,t+j}`, the exchange rate is
`P_{1,t}/P_{2,t} = (B_{1,t−1}/PV_{1,t})/(B_{2,t−1}/PV_{2,t})`. -/
theorem exchange_rate_eq_ratio_pv {β : ℝ} {B₁ B₂ P₁ P₂ s₁ s₂ : ℕ → Ω → ℝ}
    (hP₁ : ∀ t ω, P₁ t ω ≠ 0) (hP₂ : ∀ t ω, P₂ t ω ≠ 0)
    (hv₁ : ∀ t, B₁ t / P₁ t = pv 𝔼 β s₁ t) (hv₂ : ∀ t, B₂ t / P₂ t = pv 𝔼 β s₂ t)
    (hpv₁ : ∀ t ω, pv 𝔼 β s₁ t ω ≠ 0) (hpv₂ : ∀ t ω, pv 𝔼 β s₂ t ω ≠ 0) (t : ℕ) (ω : Ω) :
    P₁ t ω / P₂ t ω = (B₁ t ω / pv 𝔼 β s₁ t ω) / (B₂ t ω / pv 𝔼 β s₂ t ω) :=
  separate_pools_exchange_rate (hP₁ t ω) (hP₂ t ω) (hpv₁ t ω) (hpv₂ t ω)
    (congrFun (hv₁ t) ω) (congrFun (hv₂ t) ω)

/-- Cochrane (2023), §24.3, p. 527 (Dupor 2000): "Two currencies vie for a common pool of
surpluses, so the exchange rate is indeterminate": for every exchange rate `e > 0` there is
exactly one pair of positive price levels with `P₁ = e P₂` satisfying the common valuation
`B₁/P₁ + B₂/P₂ = V`. -/
theorem common_pool_exchange_rate_free {B₁ B₂ V e : ℝ} (hB₁ : 0 < B₁) (hB₂ : 0 < B₂)
    (hV : 0 < V) (he : 0 < e) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧ B₁ / p.1 + B₂ / p.2 = V ∧ p.1 = e * p.2 := by
  have hq : 0 < (B₁ / e + B₂) / V := div_pos (add_pos (div_pos hB₁ he) hB₂) hV
  refine ⟨(e * ((B₁ / e + B₂) / V), (B₁ / e + B₂) / V),
    ⟨mul_pos he hq, hq, ?_, rfl⟩, ?_⟩
  · simp only
    field_simp
  · rintro ⟨p₁, p₂⟩ ⟨h₁, h₂, hval, hp⟩
    simp only at h₁ h₂ hval hp
    have hp₂ : p₂ = (B₁ / e + B₂) / V := by
      rw [hp] at hval
      rw [eq_div_iff hV.ne', ← hval]
      field_simp
    refine Prod.ext ?_ ?_
    · simp only
      rw [hp, hp₂]
    · exact hp₂

/-- Cochrane (2023), §24.3, p. 527 (Dupor 2000): with a common surplus pool, the set of
equilibrium exchange rates `P₁/P₂` is the whole positive half-line. -/
theorem common_pool_indeterminate {B₁ B₂ V : ℝ} (hB₁ : 0 < B₁) (hB₂ : 0 < B₂) (hV : 0 < V) :
    {e : ℝ | ∃ P₁ P₂ : ℝ, 0 < P₁ ∧ 0 < P₂ ∧ B₁ / P₁ + B₂ / P₂ = V ∧ e = P₁ / P₂} =
      Set.Ioi 0 := by
  ext e
  simp only [Set.mem_ofPred_eq, Set.mem_Ioi]
  constructor
  · rintro ⟨P₁, P₂, h₁, h₂, _, rfl⟩
    exact div_pos h₁ h₂
  · intro he
    obtain ⟨⟨P₁, P₂⟩, ⟨h₁, h₂, hval, hp⟩, _⟩ := common_pool_exchange_rate_free hB₁ hB₂ hV he
    simp only at h₁ h₂ hval hp
    refine ⟨P₁, P₂, h₁, h₂, hval, ?_⟩
    rw [hp]
    field_simp

end Cochrane.AssetsRulesBalanceSheets.ExchangeRates
