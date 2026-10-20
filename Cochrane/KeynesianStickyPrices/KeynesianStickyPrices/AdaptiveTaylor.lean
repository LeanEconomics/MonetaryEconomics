/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.PersistenceFreedom

/-!
# Adaptive expectations with a Taylor rule

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.3.2 "Adaptive
expectations responses with policy rules", pp. 406–407, Figure 17.4.

With adaptive expectations, the rule `i_t = φπ_t + u_t` and an AR(1) disturbance
`u_t = η u_{t−1} + ε_t`, inflation follows the AR(2)
`(1 − (1+σκ)/(1+φσκ) L)(1 − ηL) π_t = −σκ/(1+φσκ) ε_t` (`ar2`).

Figure 17.4 (`η = 1`, a permanent disturbance from date 0, `π_{−1} = 0`):
`π_t = −(1 − cᵗ⁺¹)/(φ − 1)` with `c = (1+σκ)/(1+φσκ)` (`fig17_4_path`). For `φ > 1`
(`fig17_4_coeff`): the interest rate first rises (`fig17_4_i_zero`), inflation declines
(`fig17_4_infl_strictAnti`), the rate then falls (`fig17_4_i_strictAnti`) and reverses course
(`fig17_4_i_reverses`), and both converge to `−1/(φ − 1)` (`fig17_4_tendsto`): the disinflation is
stabilised. In general, for `φ > 1` bounded disturbances give bounded inflation and transitory
disturbances die out (`taylor_bounded`, `taylor_transitory`). If the interest rate cannot move,
inflation spirals (`peg_spiral`): a deflation spiral at the zero bound, an inflation spiral under a
too-low peg (Friedman).
-/

namespace Cochrane.KeynesianStickyPrices.AdaptiveTaylor

open Filter Topology StaticIS RulesAdaptiveRE PersistenceFreedom
open SharedTools (tendsto_zero_of_stable)

variable {Ω : Type*}

/-- Cochrane (2023), p. 406: with adaptive expectations, the rule and an AR(1) disturbance
`u_{t+1} = η u_t + ε_{t+1}`, inflation follows the AR(2)
`π_{t+2} − (c + η) π_{t+1} + cη π_t = −k ε_{t+2}`, with `c = (1+σκ)/(1+φσκ)` and
`k = σκ/(1+φσκ)`, i.e. `(1 − cL)(1 − ηL) π_t = −k ε_t`. -/
theorem ar2 {σ κ φ η : ℝ} (h : 1 + σ * κ * φ ≠ 0) {π0 : Ω → ℝ} {u ε π : ℕ → Ω → ℝ}
    (hπ : AdaptiveRule σ κ φ π0 u π) (hu : ∀ t ω, u (t + 1) ω = η * u t ω + ε (t + 1) ω)
    (t : ℕ) (ω : Ω) :
    π (t + 2) ω - ((1 + σ * κ) / (1 + σ * κ * φ) + η) * π (t + 1) ω +
      (1 + σ * κ) / (1 + σ * κ * φ) * η * π t ω =
      -(σ * κ / (1 + σ * κ * φ)) * ε (t + 2) ω := by
  have e := (adaptiveRule_iff_17_10 h π0 u π).mp hπ
  have e1 := e (t + 1) ω
  have e2 := e (t + 2) ω
  simp only [lagged] at e1 e2
  have hu2 := hu (t + 1) ω
  rw [e2, e1, hu2]
  ring

/-- Cochrane (2023), p. 406: the first form of the AR(2),
`(1 − (1+σκ)/(1+φσκ) L) π_t = −σκ/(1+φσκ) u_t`, is (17.10). -/
theorem ar1_form {σ κ φ : ℝ} (h : 1 + σ * κ * φ ≠ 0) {π0 : Ω → ℝ} {u π : ℕ → Ω → ℝ}
    (hπ : AdaptiveRule σ κ φ π0 u π) (t : ℕ) (ω : Ω) :
    π t ω - (1 + σ * κ) / (1 + σ * κ * φ) * lagged π0 π t ω =
      -(σ * κ / (1 + σ * κ * φ)) * u t ω := by
  rw [(adaptiveRule_iff_17_10 h π0 u π).mp hπ t ω]; ring

/-- Cochrane (2023), p. 406: for `φ > 1` (and `σκ > 0`) the coefficient on lagged inflation,
`c = (1+σκ)/(1+φσκ)`, lies in `(0, 1)`, and `σκ/(1+φσκ) = (1 − c)/(φ − 1)`. -/
theorem fig17_4_coeff {σ κ φ : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) :
    0 < (1 + σ * κ) / (1 + σ * κ * φ) ∧ (1 + σ * κ) / (1 + σ * κ * φ) < 1 ∧
      σ * κ / (1 + σ * κ * φ) = (1 - (1 + σ * κ) / (1 + σ * κ * φ)) / (φ - 1) := by
  have hM : 0 < 1 + σ * κ * φ := by nlinarith
  have hφ1 : φ - 1 ≠ 0 := by linarith
  refine ⟨by positivity, by rw [div_lt_one hM]; nlinarith, ?_⟩
  field_simp
  ring

/-- Cochrane (2023), Figure 17.4, p. 407: the response to a permanent disturbance (`η = 1`,
`u_t = 1` from date 0, `π_{−1} = 0`) is `π_t = −(1 − cᵗ⁺¹)/(φ − 1)`. -/
theorem fig17_4_path {σ κ φ : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) {π : ℕ → Ω → ℝ}
    (hπ : AdaptiveRule σ κ φ (fun _ => 0) (fun _ _ => 1) π) (t : ℕ) (ω : Ω) :
    π t ω = -(1 - ((1 + σ * κ) / (1 + σ * κ * φ)) ^ (t + 1)) / (φ - 1) := by
  have hM : 1 + σ * κ * φ ≠ 0 := by nlinarith
  have e := (adaptiveRule_iff_17_10 hM _ _ π).mp hπ
  obtain ⟨-, -, hk⟩ := fig17_4_coeff hσκ hφ
  set c := (1 + σ * κ) / (1 + σ * κ * φ)
  have hφ1 : φ - 1 ≠ 0 := by linarith
  induction t with
  | zero => rw [e 0 ω]; simp only [lagged, hk]; field_simp; ring
  | succ t ih => rw [e (t + 1) ω]; simp only [lagged]; rw [ih, hk]; field_simp; ring

/-- Cochrane (2023), Figure 17.4: the interest rate along the response,
`i_t = φ π_t + 1 = 1 − φ (1 − cᵗ⁺¹)/(φ − 1)`. -/
noncomputable def fig17_4_rate (σ κ φ : ℝ) (t : ℕ) : ℝ :=
  φ * (-(1 - ((1 + σ * κ) / (1 + σ * κ * φ)) ^ (t + 1)) / (φ - 1)) + 1

/-- Cochrane (2023), p. 406, "interest rates rise": on impact `i_0 = 1/(1 + φσκ) > 0`. -/
theorem fig17_4_i_zero {σ κ φ : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) :
    fig17_4_rate σ κ φ 0 = 1 / (1 + σ * κ * φ) ∧ 0 < fig17_4_rate σ κ φ 0 := by
  have hM : 0 < 1 + σ * κ * φ := by nlinarith
  obtain ⟨-, -, hk⟩ := fig17_4_coeff hσκ hφ
  have e : fig17_4_rate σ κ φ 0 = 1 / (1 + σ * κ * φ) := by
    unfold fig17_4_rate
    rw [zero_add, pow_one, neg_div, ← hk]
    set M := 1 + σ * κ * φ with hMdef
    have hM0 : M ≠ 0 := hM.ne'
    field_simp
    rw [hMdef]
    ring
  exact ⟨e, by rw [e]; positivity⟩

/-- Cochrane (2023), p. 406, "inflation declines": the inflation response is strictly
decreasing. -/
theorem fig17_4_infl_strictAnti {σ κ φ : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) :
    StrictAnti fun t : ℕ => -(1 - ((1 + σ * κ) / (1 + σ * κ * φ)) ^ (t + 1)) / (φ - 1) := by
  obtain ⟨h0, h1, -⟩ := fig17_4_coeff hσκ hφ
  intro m n hmn
  have := pow_lt_pow_right_of_lt_one₀ h0 h1 (by omega : m + 1 < n + 1)
  have hφ1 : 0 < φ - 1 := by linarith
  simp only
  rw [div_lt_div_iff_of_pos_right hφ1]
  linarith

/-- Cochrane (2023), p. 406, "interest rates then decline to catch and stabilize inflation":
the interest rate is strictly decreasing after its initial rise. -/
theorem fig17_4_i_strictAnti {σ κ φ : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) :
    StrictAnti (fig17_4_rate σ κ φ) := by
  intro m n hmn
  have := fig17_4_infl_strictAnti hσκ hφ hmn
  unfold fig17_4_rate
  have hφ0 : 0 < φ := by linarith
  nlinarith

/-- Cochrane (2023), Figure 17.4, p. 407: inflation and the interest rate converge to the same
long-run value `π_∞ = i_∞ = −1/(φ − 1)`: the disinflation is stabilised. -/
theorem fig17_4_tendsto {σ κ φ : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) :
    Tendsto (fun t : ℕ => -(1 - ((1 + σ * κ) / (1 + σ * κ * φ)) ^ (t + 1)) / (φ - 1)) atTop
      (𝓝 (-1 / (φ - 1))) ∧
      Tendsto (fig17_4_rate σ κ φ) atTop (𝓝 (-1 / (φ - 1))) := by
  obtain ⟨h0, h1, -⟩ := fig17_4_coeff hσκ hφ
  have hp : Tendsto (fun t : ℕ => ((1 + σ * κ) / (1 + σ * κ * φ)) ^ (t + 1)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1)
  have hπ : Tendsto (fun t : ℕ => -(1 - ((1 + σ * κ) / (1 + σ * κ * φ)) ^ (t + 1)) / (φ - 1))
      atTop (𝓝 (-1 / (φ - 1))) := by
    simpa using ((hp.const_sub 1).neg).div_const (φ - 1)
  refine ⟨hπ, ?_⟩
  have hφ1 : φ - 1 ≠ 0 := by linarith
  have hlim : φ * (-1 / (φ - 1)) + 1 = -1 / (φ - 1) := by field_simp; ring
  rw [← hlim]
  exact (hπ.const_mul φ).add_const 1

/-- Cochrane (2023), p. 406, "the actual interest rate quickly reverses course": the interest
rate, positive on impact, eventually becomes negative. -/
theorem fig17_4_i_reverses {σ κ φ : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) :
    0 < fig17_4_rate σ κ φ 0 ∧ ∃ T, ∀ t ≥ T, fig17_4_rate σ κ φ t < 0 := by
  refine ⟨(fig17_4_i_zero hσκ hφ).2, ?_⟩
  have hneg : -1 / (φ - 1) < 0 := div_neg_of_neg_of_pos (by norm_num) (by linarith)
  exact eventually_atTop.mp ((fig17_4_tendsto hσκ hφ).2.eventually (gt_mem_nhds hneg))

/-- Cochrane (2023), p. 406, "the seal (the central bank) [moves] its nose more than one for one":
for `φ > 1` every bounded disturbance produces bounded inflation, from any initial
condition. -/
theorem taylor_bounded {σ κ φ B M : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) {π0 : Ω → ℝ}
    {u π : ℕ → Ω → ℝ} (hπ0 : ∀ ω, |π0 ω| ≤ B) (hu : ∀ t ω, |u t ω| ≤ M)
    (hπ : AdaptiveRule σ κ φ π0 u π) : BoundedProc π := by
  have hM : 1 + σ * κ * φ ≠ 0 := by nlinarith
  exact adaptiveRule_bounded hM ((abs_coeff_lt_one_iff hσκ hM).mpr (Or.inl hφ)) hπ0 hu hπ

/-- Cochrane (2023), p. 406: for `φ > 1` a transitory disturbance (`u_t → 0` along a history)
leaves no lasting inflation: `π_t → 0`. -/
theorem taylor_transitory {σ κ φ : ℝ} (hσκ : 0 < σ * κ) (hφ : 1 < φ) {π0 : Ω → ℝ}
    {u π : ℕ → Ω → ℝ} (hπ : AdaptiveRule σ κ φ π0 u π) {ω : Ω}
    (hu : Tendsto (fun t => u t ω) atTop (𝓝 0)) : Tendsto (fun t => π t ω) atTop (𝓝 0) := by
  have hM : 1 + σ * κ * φ ≠ 0 := by nlinarith
  have hc := (abs_coeff_lt_one_iff hσκ hM).mpr (Or.inl hφ)
  have e := (adaptiveRule_iff_17_10 hM π0 u π).mp hπ
  have hf : Tendsto (fun t => -(σ * κ / (1 + σ * κ * φ)) * u (t + 1) ω) atTop (𝓝 0) := by
    simpa using ((tendsto_add_atTop_iff_nat 1).mpr hu).const_mul (-(σ * κ / (1 + σ * κ * φ)))
  exact tendsto_zero_of_stable hc (fun t => by rw [e (t + 1) ω]; simp only [lagged]; ring) hf

/-- Cochrane (2023), p. 406, "If interest rates hit the zero bound or cannot move, the model
predicts a deflation spiral" (and Friedman's too-low peg, an inflation spiral): with the rate
fixed at `ī`, inflation below `ī` falls without bound and inflation above `ī` rises without
bound. -/
theorem peg_spiral {σ κ ib : ℝ} (hσκ : 0 < σ * κ) {π0 : Ω → ℝ} {π : ℕ → Ω → ℝ}
    (h : AdaptiveEq σ κ π0 (fun _ _ => ib) π) (ω : Ω) :
    (π0 ω < ib → Tendsto (fun t => π t ω) atTop atBot) ∧
      (ib < π0 ω → Tendsto (fun t => π t ω) atTop atTop) := by
  have he : (fun t => π t ω) = fun t => ib + (1 + σ * κ) ^ (t + 1) * (π0 ω - ib) :=
    funext fun t => adaptive_peg h t ω
  have hp : Tendsto (fun t : ℕ => (1 + σ * κ) ^ (t + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by linarith)).comp (tendsto_add_atTop_nat 1)
  rw [he]
  refine ⟨fun hlt => ?_, fun hgt => ?_⟩
  · exact tendsto_atBot_add_const_left _ ib (hp.atTop_mul_const_of_neg (by linarith))
  · exact tendsto_atTop_add_const_left _ ib (hp.atTop_mul_const (by linarith))

end Cochrane.KeynesianStickyPrices.AdaptiveTaylor
