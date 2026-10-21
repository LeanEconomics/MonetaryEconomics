/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DebtDeficitsInflation.GeneralizedHRS

/-!
# Present-value examples

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A2, §2.1, pp. 603–604:
the classic present-value calculations whose "100% R²" predictions the book uses to show how
not to test present-value relations.

## Main results

* Dividend AR(1): `dividend_pv` (`E_t ∑_{j≥1} βʲ d_{t+j} = βρ_d d_t/(1 − βρ_d)`, termwise) and
  `dividend_pv_E` (`E_t` of the infinite sum, bounded dividends).
* Permanent income: `pih_consumption`
  (`c_t − c_{t−1} = rβ(y_t − ρ_y y_{t−1})/(1 − βρ_y)`).
* AR(1) surplus lines of p. 604: `surplus_pv_ar1` (`v_t = E_t ∑ ρʲ s_{t+1+j} = η s_t/(1 − ρη)`),
  `innov_infl_ar1` (`Δπ_{t+1} = −a(ρ)ε_{t+1} = −(s_{t+1} − ηs_t)/(1 − ρη)`); survey E15: the
  printed denominator `1 − βη` is right only when `β = ρ` (`printed_p604_iff`).
-/

namespace Cochrane.DebtDeficitsInflation.PresentValueExamples

open Filter Topology
open Cochrane.DebtDeficitsInflation.Innovations
open Cochrane.DebtDeficitsInflation.LinearizedIdentities
open Cochrane.DebtDeficitsInflation.SurplusMA

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), A2 p. 603: with AR(1) dividends (`E_t d_{t+1} = ρ_d d_t`) and
`|βρ_d| < 1`, `E_t ∑_{j ≥ 1} βʲ d_{t+j} = βρ_d d_t / (1 − βρ_d)` (series of conditional
expectations). -/
theorem dividend_pv {β ρd : ℝ} (h : |β * ρd| < 1) {d : ℕ → Ω → ℝ} (hd : 𝔼.IsAR1 ρd d)
    (t : ℕ) (ω : Ω) :
    HasSum (fun j => β ^ (j + 1) * 𝔼.E t (d (t + 1 + j)) ω) (β * ρd * d t ω / (1 - β * ρd)) := by
  have hE : ∀ j, 𝔼.E t (d (t + 1 + j)) ω = ρd ^ (j + 1) * d t ω := fun j => by
    rw [show t + 1 + j = t + (j + 1) by omega, 𝔼.ar1_iterate hd]
    rfl
  have := (hasSum_geometric_of_abs_lt_one h).mul_left (β * ρd * d t ω)
  convert this using 1
  · funext j
    rw [hE, mul_pow, pow_succ, pow_succ]
    ring
  · have h1 : 1 - β * ρd ≠ 0 := by
      intro h0
      have : β * ρd = 1 := by linarith
      rw [this, abs_one] at h
      exact lt_irrefl _ h
    field_simp

/-- Cochrane (2023), A2 p. 603: the same present value as the conditional expectation of the
infinite sum, `E_t ∑_{j ≥ 1} βʲ d_{t+j} = βρ_d d_t/(1 − βρ_d)`, for bounded dividends and
`|β| < 1`, `|βρ_d| < 1`. -/
theorem dividend_pv_E {β ρd : ℝ} (hβ : |β| < 1) (h : |β * ρd| < 1) {d : ℕ → Ω → ℝ}
    (hd : 𝔼.IsAR1 ρd d) {K : ℝ} (hK : ∀ t ω, |d t ω| ≤ K) (t : ℕ) :
    𝔼.E t (fun ω => ∑' j, β ^ (j + 1) * d (t + 1 + j) ω) =
      fun ω => β * ρd * d t ω / (1 - β * ρd) := by
  funext ω
  have hgeo : Summable fun j : ℕ => |β ^ (j + 1)| := by
    have := (summable_geometric_of_lt_one (abs_nonneg β) hβ).mul_left |β|
    refine this.congr fun j => ?_
    rw [abs_pow, pow_succ]
    ring
  rw [E_tsum_abs 𝔼 hgeo (x := fun j ω' => d (t + 1 + j) ω') (fun j ω' => hK _ ω') t ω]
  exact (dividend_pv 𝔼 h hd t ω).tsum_eq

/-- Cochrane (2023), A2 p. 603 (the permanent-income model): if
`c_{t+1} = c_t + rβ ∑_{j ≥ 0} βʲ (E_{t+1} − E_t) y_{t+1+j}` and income is an AR(1)
(`E_t y_{t+1} = ρ_y y_t`), then `c_{t+1} − c_t = rβ (y_{t+1} − ρ_y y_t)/(1 − βρ_y)` (an exact,
"100% R²" relation). -/
theorem pih_consumption {β ρy rr : ℝ} (h : |β * ρy| < 1) {y c : ℕ → Ω → ℝ}
    (hy : 𝔼.IsAR1 ρy y)
    (hc : ∀ t ω, c (t + 1) ω = c t ω + rr * β * ∑' j, β ^ j * innov 𝔼 t (y (t + 1 + j)) ω)
    (t : ℕ) (ω : Ω) :
    c (t + 1) ω - c t ω = rr * β * (y (t + 1) ω - ρy * y t ω) / (1 - β * ρy) := by
  have hterm : ∀ j, β ^ j * innov 𝔼 t (y (t + 1 + j)) ω =
      (y (t + 1) ω - ρy * y t ω) * (β * ρy) ^ j := by
    intro j
    rw [innov_apply, Pi.sub_apply, show t + 1 + j = (t + 1) + j by omega, 𝔼.ar1_iterate hy,
      show t + 1 + j = t + (j + 1) by omega, 𝔼.ar1_iterate hy, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul, mul_pow, pow_succ]
    ring
  have hsum : ∑' j, β ^ j * innov 𝔼 t (y (t + 1 + j)) ω =
      (y (t + 1) ω - ρy * y t ω) / (1 - β * ρy) := by
    simp_rw [hterm]
    rw [tsum_mul_left, tsum_geometric_of_abs_lt_one h, div_eq_mul_inv]
  rw [hc t ω, hsum]
  ring

/-- Cochrane (2023), A2 p. 604 (and (4.5), p. 89): with an AR(1) surplus and `|ρη| < 1`,
`E_t ∑_{j ≥ 0} ρʲ s_{t+1+j} = η s_t/(1 − ρη)`. -/
theorem surplus_pv_ar1 {ρ η : ℝ} (h : |ρ * η| < 1) {s : ℕ → Ω → ℝ} (hs : 𝔼.IsAR1 η s)
    (t : ℕ) (ω : Ω) :
    HasSum (fun j => ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω) (η * s t ω / (1 - ρ * η)) := by
  have hE : ∀ j, 𝔼.E t (s (t + 1 + j)) ω = η ^ (j + 1) * s t ω := fun j => by
    rw [show t + 1 + j = t + (j + 1) by omega, 𝔼.ar1_iterate hs]
    rfl
  have := (hasSum_geometric_of_abs_lt_one h).mul_left (η * s t ω)
  convert this using 1
  · funext j
    rw [hE, mul_pow]
    ring
  · have h1 : 1 - ρ * η ≠ 0 := by
      intro h0
      have : ρ * η = 1 := by linarith
      rw [this, abs_one] at h
      exact lt_irrefl _ h
    field_simp

/-- Cochrane (2023), A2 p. 604, corrected (survey E15): in the simple model with an AR(1)
surplus (moving-average coefficients `ηʲ`), `Δ_{t+1}π_{t+1} = −a(ρ)ε_{t+1} =
−(s_{t+1} − η s_t)/(1 − ρη)`. -/
theorem innov_infl_ar1 {ρ c η : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {ε : ℤ → Ω → ℝ}
    (hs : IsMA (fun j => η ^ j) ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (hρ : |ρ| ≤ 1) (hρη : |ρ * η| < 1) (t : ℕ) :
    innov 𝔼 t (infl (t + 1)) = -gen (fun j => η ^ j) ρ • ε ((t : ℤ) + 1) ∧
      innov 𝔼 t (infl (t + 1)) = fun ω => -(s (t + 1) ω - η * s t ω) / (1 - ρ * η) := by
  have h1 := innov_infl_eq 𝔼 hm hT hs hε hM hρ t
  refine ⟨h1, ?_⟩
  rw [h1, gen_ar1 hρη, ar1_of_MA hs hM t]
  funext ω
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply]
  ring

/-- Cochrane (2023), A2 p. 604 (survey E15): the printed `−(s_{t+1} − η_s s_t)/(1 − βη_s)` equals
unexpected inflation, in a state with a non-zero shock and for `η ≠ 0`, iff `β = ρ`. -/
theorem printed_p604_iff {ρ c η β : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {ε : ℤ → Ω → ℝ}
    (hs : IsMA (fun j => η ^ j) ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (hρ : |ρ| ≤ 1) (hρη : |ρ * η| < 1) (hβη : 1 - β * η ≠ 0) (hη : η ≠ 0) (t : ℕ) (ω : Ω)
    (hne : ε ((t : ℤ) + 1) ω ≠ 0) :
    innov 𝔼 t (infl (t + 1)) ω = -(s (t + 1) ω - η * s t ω) / (1 - β * η) ↔ β = ρ := by
  have h1 := congrFun (innov_infl_ar1 𝔼 hm hT hs hε hM hρ hρη t).2 ω
  have he : s (t + 1) ω - η * s t ω = ε ((t : ℤ) + 1) ω := by
    have := congrFun (ar1_of_MA hs hM t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  have hρη' : 1 - ρ * η ≠ 0 := by
    intro h0
    have : ρ * η = 1 := by linarith
    rw [this, abs_one] at hρη
    exact lt_irrefl _ hρη
  rw [h1, he]
  constructor
  · intro h2
    rw [div_eq_div_iff hρη' hβη] at h2
    have h3 : ε ((t : ℤ) + 1) ω * ((β - ρ) * η) = 0 := by linarith
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd h4 hne
    · rcases mul_eq_zero.1 h4 with h5 | h5
      · linarith
      · exact absurd h5 hη
  · rintro rfl
    rfl

end Cochrane.DebtDeficitsInflation.PresentValueExamples
