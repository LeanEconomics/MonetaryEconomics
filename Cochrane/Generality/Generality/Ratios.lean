/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.LongTermDebt

/-!
# Ratios to GDP and a focus on inflation

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.2, pp. 54–55, eq. (3.4)
and the three unnumbered displays.

The valuation equation `B_{t−1}/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)s_{t+j}]` (with `m ≡ β` the book's
`E_t ∑ βʲ s_{t+j}`, `LongTermDebt.pv_const`) is rewritten by dividing by a variable known at
`t`: real GDP `y_t > 0` or nominal debt `B_{t−1} > 0`. The only property of `E_t` used is the
pull-out property for date-`t` variables; no inverse `1/y_t` is assumed to be known.

Notation: `D t` is `B_{t−1}`, the nominal one-period debt outstanding at the start of `t`.

## Main results

* `E_div_known`: `E_t[W/z] = E_t[W]/z` for `z` known at `t`, `z ≠ 0`.
* `valuation_gdp_iff` (p. 54): `B_{t−1}/P_t = PV` iff
  `B_{t−1}/(P_ty_t) = ∑_j E_t[(Λ_{t+j}/Λ_t)(y_{t+j}/y_t)(s_{t+j}/y_{t+j})]`.
* `valuation_per_dollar_iff` (3.4): iff `1/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)s_{t+j}/B_{t−1}]`;
  `valuation_per_dollar_const` is (3.4) exactly as printed.
* `valuation_per_dollar_gdp_iff` (p. 55): iff
  `1/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)(y_{t+j}/y_t)(s_{t+j}/y_{t+j})] / (B_{t−1}/y_t)`.
* `E_innov_zero` (p. 54): `E_t(E_{t+1} − E_t)X = 0`; `E_innov_pv_zero` for `X = ∑ βʲs_{t+j}`.
* `flow_gdp_iff`: the flow condition in ratios to GDP.
* `gdp_growth_mono` (p. 54, "more growth means greater surpluses"): with given nonnegative
  surplus-to-GDP ratios, faster growth raises the debt-to-GDP valuation.
-/

namespace Cochrane.Generality.Ratios

open LongTermDebt

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §3.2, p. 54 ("multiplying and dividing by real GDP `y_t`"): for `z` known
at `t` and nonzero, `E_t[W/z] = E_t[W]/z` (pull-out applied to `W = z·(W/z)`). -/
theorem E_div_known (hP : 𝔼.PullOut) {t : ℕ} {z : Ω → ℝ} (hz : 𝔼.E t z = z)
    (hz0 : ∀ ξ, z ξ ≠ 0) (W : Ω → ℝ) (ξ : Ω) :
    𝔼.E t (fun ξ' => W ξ' / z ξ') ξ = 𝔼.E t W ξ / z ξ := by
  have hW : W = z * fun ξ' => W ξ' / z ξ' := by
    funext ξ'
    simp only [Pi.mul_apply]
    field_simp [hz0 ξ']
  have h := congrFun (hP t z (fun ξ' => W ξ' / z ξ') hz) ξ
  rw [← hW, Pi.mul_apply] at h
  rw [h]
  field_simp [hz0 ξ]

/-- Cochrane (2023), §3.2, p. 54: the growth-adjusted term
`(Λ_{t+j}/Λ_t)(y_{t+j}/y_t)(s_{t+j}/y_{t+j})` of the debt-to-GDP valuation. -/
noncomputable def gdpTerm (m y s : ℕ → Ω → ℝ) (t j : ℕ) : Ω → ℝ :=
  sdf m t j * fun ξ => y (t + j) ξ / y t ξ * (s (t + j) ξ / y (t + j) ξ)

/-- Cochrane (2023), §3.2, p. 54: with GDP known at `t` and positive at all dates,
`E_t[(Λ_{t+j}/Λ_t)(y_{t+j}/y_t)(s_{t+j}/y_{t+j})] = E_t[(Λ_{t+j}/Λ_t)s_{t+j}]/y_t`. -/
theorem E_gdpTerm (hP : 𝔼.PullOut) {m y s : ℕ → Ω → ℝ} {t : ℕ} (hy : 𝔼.E t (y t) = y t)
    (hy0 : ∀ k ξ, y k ξ ≠ 0) (j : ℕ) (ξ : Ω) :
    𝔼.E t (gdpTerm m y s t j) ξ = 𝔼.E t (sdf m t j * s (t + j)) ξ / y t ξ := by
  have h : gdpTerm m y s t j = fun ξ' => (sdf m t j * s (t + j)) ξ' / y t ξ' := by
    funext ξ'
    simp only [gdpTerm, Pi.mul_apply]
    have := hy0 (t + j) ξ'
    have := hy0 t ξ'
    field_simp
  rw [h, E_div_known 𝔼 hP hy (hy0 t)]

/-- Cochrane (2023), §3.2, p. 54 (first display): the valuation equation
`B_{t−1}/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)s_{t+j}]` holds iff its debt-to-GDP form
`B_{t−1}/(P_ty_t) = ∑_j E_t[(Λ_{t+j}/Λ_t)(y_{t+j}/y_t)(s_{t+j}/y_{t+j})]` holds. -/
theorem valuation_gdp_iff (hP : 𝔼.PullOut) {m y s D P : ℕ → Ω → ℝ} {t : ℕ}
    (hy : 𝔼.E t (y t) = y t) (hy0 : ∀ k ξ, y k ξ ≠ 0) :
    (∀ ξ, D t ξ / P t ξ = pv 𝔼 m s t ξ) ↔
      ∀ ξ, D t ξ / (P t ξ * y t ξ) = ∑' j, 𝔼.E t (gdpTerm m y s t j) ξ := by
  refine forall_congr' fun ξ => ?_
  simp_rw [E_gdpTerm 𝔼 hP hy hy0]
  rw [tsum_div_const, pv, div_mul_eq_div_div]
  exact ⟨fun h => by rw [h], fun h => (div_left_inj' (hy0 t ξ)).mp h⟩

/-- Cochrane (2023), eq. (3.4), p. 54: with nominal debt `B_{t−1}` known at `t` and nonzero,
the valuation equation holds iff `1/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)s_{t+j}/B_{t−1}]`, the value of
one dollar. -/
theorem valuation_per_dollar_iff (hP : 𝔼.PullOut) {m s D P : ℕ → Ω → ℝ} {t : ℕ}
    (hD : 𝔼.E t (D t) = D t) (hD0 : ∀ ξ, D t ξ ≠ 0) :
    (∀ ξ, D t ξ / P t ξ = pv 𝔼 m s t ξ) ↔
      ∀ ξ, 1 / P t ξ = ∑' j, 𝔼.E t (fun ξ' => (sdf m t j * s (t + j)) ξ' / D t ξ') ξ := by
  refine forall_congr' fun ξ => ?_
  simp_rw [E_div_known 𝔼 hP hD hD0]
  rw [tsum_div_const, pv]
  have h0 := hD0 ξ
  constructor
  · intro h
    rw [← h]
    field_simp
  · intro h
    rw [eq_div_iff h0] at h
    rw [← h]
    field_simp

/-- Cochrane (2023), eq. (3.4), p. 54, exactly as printed (`m ≡ β`):
`B_{t−1}/P_t = ∑_j βʲE_t s_{t+j}` iff `1/P_t = ∑_j βʲ E_t[s_{t+j}/B_{t−1}]`. -/
theorem valuation_per_dollar_const (hP : 𝔼.PullOut) (β : ℝ) {s D P : ℕ → Ω → ℝ} {t : ℕ}
    (hD : 𝔼.E t (D t) = D t) (hD0 : ∀ ξ, D t ξ ≠ 0) :
    (∀ ξ, D t ξ / P t ξ = ∑' j, β ^ j * 𝔼.E t (s (t + j)) ξ) ↔
      ∀ ξ, 1 / P t ξ = ∑' j, β ^ j * 𝔼.E t (fun ξ' => s (t + j) ξ' / D t ξ') ξ := by
  have h := valuation_per_dollar_iff 𝔼 hP (m := fun _ _ => β) (s := s) (P := P) hD hD0
  rw [pv_const] at h
  convert h using 3 with ξ ξ
  refine tsum_congr fun j => ?_
  rw [E_div_known 𝔼 hP hD hD0, E_div_known 𝔼 hP hD hD0, sdf_const]
  have h' : ((fun _ => β ^ j) * s (t + j) : Ω → ℝ) = β ^ j • s (t + j) := by
    funext ξ'
    simp
  rw [h', map_smul, Pi.smul_apply, smul_eq_mul, mul_div_assoc]

/-- Cochrane (2023), §3.2, p. 55 (last display): with GDP and nominal debt known at `t` and
nonzero, the valuation equation holds iff
`1/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)(y_{t+j}/y_t)(s_{t+j}/y_{t+j})] / (B_{t−1}/y_t)`. -/
theorem valuation_per_dollar_gdp_iff (hP : 𝔼.PullOut) {m y s D P : ℕ → Ω → ℝ} {t : ℕ}
    (hy : 𝔼.E t (y t) = y t) (hy0 : ∀ k ξ, y k ξ ≠ 0) (hD0 : ∀ ξ, D t ξ ≠ 0) :
    (∀ ξ, D t ξ / P t ξ = pv 𝔼 m s t ξ) ↔
      ∀ ξ, 1 / P t ξ = (∑' j, 𝔼.E t (gdpTerm m y s t j) ξ) / (D t ξ / y t ξ) := by
  rw [valuation_gdp_iff 𝔼 hP hy hy0]
  refine forall_congr' fun ξ => ?_
  have h0 := hD0 ξ
  have h1 := hy0 t ξ
  constructor
  · intro h
    rw [← h]
    by_cases hp : P t ξ = 0
    · simp [hp]
    · field_simp
  · intro h
    rw [eq_div_iff (div_ne_zero h0 h1)] at h
    rw [← h]
    by_cases hp : P t ξ = 0
    · simp [hp]
    · field_simp

/-- Cochrane (2023), §3.2, p. 54: "There can be no expected shocks to the present value of
surpluses", `E_t[(E_{t+1} − E_t)X] = 0` for every random variable `X`. -/
theorem E_innov_zero (t : ℕ) (X : Ω → ℝ) : 𝔼.E t (𝔼.E (t + 1) X - 𝔼.E t X) = 0 := by
  rw [map_sub, 𝔼.tower (Nat.le_succ t), 𝔼.E_E_self, sub_self]

/-- Cochrane (2023), §3.2, p. 54: `E_t(E_{t+1} − E_t)∑_j βʲs_{t+j} = 0`, with the sum taken
state by state. -/
theorem E_innov_pv_zero (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) :
    𝔼.E t (𝔼.E (t + 1) (fun ξ => ∑' j, β ^ j * s (t + j) ξ) -
      𝔼.E t (fun ξ => ∑' j, β ^ j * s (t + j) ξ)) = 0 :=
  E_innov_zero 𝔼 t _

/-- Cochrane (2023), §3.2, p. 54 (the flow condition in ratios to GDP): with GDP known at `t`
and positive, `x_t = s_t + E_t[m_t x_{t+1}]` iff
`x_t/y_t = s_t/y_t + E_t[m_t (y_{t+1}/y_t)(x_{t+1}/y_{t+1})]`. -/
theorem flow_gdp_iff (hP : 𝔼.PullOut) {m y s x : ℕ → Ω → ℝ} {t : ℕ}
    (hy : 𝔼.E t (y t) = y t) (hy0 : ∀ k ξ, y k ξ ≠ 0) :
    (∀ ξ, x t ξ = s t ξ + 𝔼.E t (m t * x (t + 1)) ξ) ↔
      ∀ ξ, x t ξ / y t ξ = s t ξ / y t ξ +
        𝔼.E t (m t * fun ξ' => y (t + 1) ξ' / y t ξ' * (x (t + 1) ξ' / y (t + 1) ξ')) ξ := by
  have h : ∀ ξ, 𝔼.E t (m t * fun ξ' => y (t + 1) ξ' / y t ξ' * (x (t + 1) ξ' / y (t + 1) ξ'))
      ξ = 𝔼.E t (m t * x (t + 1)) ξ / y t ξ := fun ξ => by
    have e : (m t * fun ξ' => y (t + 1) ξ' / y t ξ' * (x (t + 1) ξ' / y (t + 1) ξ')) =
        fun ξ' => (m t * x (t + 1)) ξ' / y t ξ' := by
      funext ξ'
      simp only [Pi.mul_apply]
      have := hy0 (t + 1) ξ'
      have := hy0 t ξ'
      field_simp
    rw [e, E_div_known 𝔼 hP hy (hy0 t)]
  refine forall_congr' fun ξ => ?_
  rw [h, ← add_div]
  exact ⟨fun e => by rw [e], fun e => (div_left_inj' (hy0 t ξ)).mp e⟩

/-- Cochrane (2023), §3.2, p. 54 ("More growth means greater surpluses, with surplus-to-GDP
ratios"): under perfect foresight with `0 ≤ β`, nonnegative surplus-to-GDP ratios `σ_j` and
summable valuations, a growth path `g'_j ≥ g_j` (`g_j = y_{t+j}/y_t`) gives a weakly larger
debt-to-GDP valuation `∑_j βʲ g_j σ_j`. -/
theorem gdp_growth_mono {β : ℝ} (hβ : 0 ≤ β) {g g' σ : ℕ → ℝ} (hσ : ∀ j, 0 ≤ σ j)
    (hg : ∀ j, g j ≤ g' j) (hs' : Summable fun j => β ^ j * g' j * σ j)
    (hs : Summable fun j => β ^ j * g j * σ j) :
    ∑' j, β ^ j * g j * σ j ≤ ∑' j, β ^ j * g' j * σ j :=
  Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hg j) (pow_nonneg hβ j)) (hσ j)) hs hs'

end Cochrane.Generality.Ratios
