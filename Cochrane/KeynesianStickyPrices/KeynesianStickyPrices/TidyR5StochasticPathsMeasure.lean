/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR5StochasticPaths
import KeynesianStickyPrices.TidyR5ExpectationsMeasure

/-!
# The full-model paths of §17.4 on a genuine probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.4, eqs.
(17.15)–(17.18), pp. 407–410, Figures 17.5–17.6.

TidyR5StochasticPaths gave the expected-path and news forms of Figs. 17.5–17.6 for the core
`ExpectationSystem`. Here the same results hold almost surely on a probability space with a
filtration and Mathlib's conditional expectation (TidyR5ExpectationsMeasure), every model
equation holding almost everywhere (`ModelM`):

* `expected_pfEqm_ae`, `expected_path_ae`: for every date `s`, almost surely the expected paths
  `j ↦ E_s(i, x, π)_{s+j}` form a perfect-foresight equilibrium, and with essentially bounded
  rates and inflation expected inflation is `FullModel.path` for the expected rate path.
* `news_pfEqm_ae`, `news_path_ae`: almost surely the news `ΔE_{s+1}` about the whole future is a
  perfect-foresight equilibrium,
  `ΔE_{s+1} π_{s+1+j} = path(ΔE_{s+1} i_{s+1+·}, ΔE_{s+1} π_{s+1})(j)`.
* `news_rise_ae`, `news_rise_twoSided_ae` (Fig. 17.5): on the event that the date-`(s+1)` news is
  a permanent rise from horizon `T`, almost surely the inflation news is `path(1{· ≥ T}, δ)`,
  converges to one and exceeds `δ λ₁^{−j}`; with the two-sided unexpected inflation it is
  `FullModel.antPath`, with negative output news up to the rise.
-/

namespace Cochrane.KeynesianStickyPrices.TidyR5StochasticPathsMeasure

open MeasureTheory Filter Topology FullModel TidyR5ExpectationsMeasure TidyR5StochasticPaths

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), eqs. (17.15)–(17.17), p. 407, on a probability space, without disturbances:
`x_t = E_t x_{t+1} − σ r_t`, `i_t = r_t + E_t π_{t+1}`, `π_t = β E_t π_{t+1} + κ x_t` almost
everywhere, all variables integrable. -/
def ModelM (σ β κ : ℝ) (i r x π : ℕ → Ω → ℝ) : Prop :=
  (∀ t, Integrable (i t) S.μ ∧ Integrable (r t) S.μ ∧ Integrable (x t) S.μ ∧
    Integrable (π t) S.μ) ∧
  ∀ t, x t =ᵐ[S.μ] S.E t (x (t + 1)) - σ • r t ∧ i t =ᵐ[S.μ] r t + S.E t (π (t + 1)) ∧
    π t =ᵐ[S.μ] β • S.E t (π (t + 1)) + κ • x t

/-- Cochrane (2023), §17.4, pp. 407–410, on a probability space: for every date `s`, almost surely
the expected paths `j ↦ (E_s i_{s+j}, E_s x_{s+j}, E_s π_{s+j})` form a perfect-foresight
equilibrium. -/
theorem expected_pfEqm_ae {σ β κ : ℝ} {i r x π : ℕ → Ω → ℝ} (h : ModelM S σ β κ i r x π)
    (s : ℕ) :
    ∀ᵐ ω ∂S.μ, PFEqm σ β κ (fun j => S.E s (i (s + j)) ω) (fun j => S.E s (x (s + j)) ω)
      (fun j => S.E s (π (s + j)) ω) := by
  obtain ⟨hint, heq⟩ := h
  refine ae_all_iff.mpr fun j => ?_
  have hle : s ≤ s + j := Nat.le_add_right s j
  obtain ⟨h1, h2, h3⟩ := heq (s + j)
  obtain ⟨-, ir, ix, -⟩ := hint (s + j)
  have iEπ := S.integrable_E (s + j) (π (s + j + 1))
  have iEx := S.integrable_E (s + j) (x (s + j + 1))
  filter_upwards [S.E_congr h1 s, S.E_sub iEx (ir.smul σ) s, S.E_tower hle (x (s + j + 1)),
    S.E_smul σ (r (s + j)) s, S.E_congr h2 s, S.E_add ir iEπ s,
    S.E_tower hle (π (s + j + 1)), S.E_congr h3 s, S.E_add (iEπ.smul β) (ix.smul κ) s,
    S.E_smul β (S.E (s + j) (π (s + j + 1))) s, S.E_smul κ (x (s + j)) s]
    with ω a1 b1 c1 d1 a2 b2 c2 a3 b3 e3 f3
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul] at a1 b1 d1 a2 b2 a3 b3 e3 f3
  have hs : s + (j + 1) = s + j + 1 := rfl
  simp only [hs]
  exact ⟨by linear_combination a1 + b1 + c1 - d1 + σ * (a2 + b2 + c2),
    by linear_combination a3 + b3 + e3 + f3 + β * c2⟩

/-- Essential bounds pass to all expected paths at once. -/
theorem ae_bound_E {y : ℕ → Ω → ℝ} {M : ℝ} (hy : ∀ t, ∀ᵐ ω ∂S.μ, |y t ω| ≤ M) (s : ℕ) :
    ∀ᵐ ω ∂S.μ, ∀ j, |S.E s (y j) ω| ≤ M :=
  ae_all_iff.mpr fun j => S.abs_E_le (hy j) s

/-- Essential bounds pass to all news at once (`|ΔE_{s+1} y| ≤ 2M`). -/
theorem ae_bound_innov {y : ℕ → Ω → ℝ} {M : ℝ} (hy : ∀ t, ∀ᵐ ω ∂S.μ, |y t ω| ≤ M) (s : ℕ) :
    ∀ᵐ ω ∂S.μ, ∀ j, |S.innov s (y j) ω| ≤ 2 * M := by
  filter_upwards [ae_bound_E S hy (s + 1), ae_bound_E S hy s] with ω h1 h2 j
  simp only [MeasExpectationSystem.innov, Pi.sub_apply]
  exact (abs_sub _ _).trans (by linarith [h1 j, h2 j])

/-- Cochrane (2023), §17.4.1, p. 408, on a probability space: with essentially bounded rates and
inflation, almost surely expected inflation is the perfect-foresight path for the expected rate
path started at `E_s π_s`, and expected output is `(E_s π_{s+j} − β E_s π_{s+j+1})/κ`. -/
theorem expected_path_ae {σ β κ M Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β)
    {i r x π : ℕ → Ω → ℝ} (h : ModelM S σ β κ i r x π) (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ M)
    (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) (s : ℕ) :
    ∀ᵐ ω ∂S.μ, (fun j => S.E s (π (s + j)) ω) =
        path σ β κ (fun j => S.E s (i (s + j)) ω) (S.E s (π s) ω) ∧
      ∀ j, S.E s (x (s + j)) ω =
        (S.E s (π (s + j)) ω - β * S.E s (π (s + (j + 1))) ω) / κ := by
  have hκ : κ ≠ 0 := by rintro rfl; simp at ha
  filter_upwards [expected_pfEqm_ae S h s, ae_bound_E S hi s, ae_bound_E S hπ s]
    with ω he hbi hbπ
  obtain ⟨hx, hp⟩ := (pf_eqm_iff ha hκ hβ (fun j => hbi (s + j))
    ⟨Mπ, fun j => hbπ (s + j)⟩).mp he
  exact ⟨hp, hx⟩

/-- Cochrane (2023), §17.4, on a probability space: almost surely the date-`(s+1)` news about the
whole future is a perfect-foresight equilibrium. -/
theorem news_pfEqm_ae {σ β κ : ℝ} {i r x π : ℕ → Ω → ℝ} (h : ModelM S σ β κ i r x π) (s : ℕ) :
    ∀ᵐ ω ∂S.μ, PFEqm σ β κ (fun j => S.innov s (i (s + 1 + j)) ω)
      (fun j => S.innov s (x (s + 1 + j)) ω) (fun j => S.innov s (π (s + 1 + j)) ω) := by
  filter_upwards [expected_pfEqm_ae S h (s + 1), expected_pfEqm_ae S h s] with ω ha hb j
  obtain ⟨a1, a2⟩ := ha j
  obtain ⟨b1, b2⟩ := hb (j + 1)
  simp only at a1 a2 b1 b2
  rw [show s + (j + 1) = s + 1 + j by omega, show s + (j + 1 + 1) = s + 1 + (j + 1) by omega]
    at b1 b2
  simp only [MeasExpectationSystem.innov, Pi.sub_apply]
  exact ⟨by linear_combination a1 - b1, by linear_combination a2 - b2⟩

/-- Cochrane (2023), Figs. 17.5–17.6 as impulse responses, on a probability space: with essentially
bounded rates and inflation, almost surely the inflation news is the perfect-foresight path for
the rate news started at the unexpected inflation, and the output news is
`(ΔE π_{s+1+j} − β ΔE π_{s+2+j})/κ`. -/
theorem news_path_ae {σ β κ M Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i r x π : ℕ → Ω → ℝ}
    (h : ModelM S σ β κ i r x π) (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ M)
    (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) (s : ℕ) :
    ∀ᵐ ω ∂S.μ, (fun j => S.innov s (π (s + 1 + j)) ω) =
        path σ β κ (fun j => S.innov s (i (s + 1 + j)) ω) (S.innov s (π (s + 1)) ω) ∧
      ∀ j, S.innov s (x (s + 1 + j)) ω =
        (S.innov s (π (s + 1 + j)) ω - β * S.innov s (π (s + 1 + (j + 1))) ω) / κ := by
  have hκ : κ ≠ 0 := by rintro rfl; simp at ha
  filter_upwards [news_pfEqm_ae S h s, ae_bound_innov S hi s, ae_bound_innov S hπ s]
    with ω he hbi hbπ
  obtain ⟨hx, hp⟩ := (pf_eqm_iff ha hκ hβ (fun j => hbi (s + 1 + j))
    ⟨2 * Mπ, fun j => hbπ (s + 1 + j)⟩).mp he
  exact ⟨hp, hx⟩

/-- Cochrane (2023), Fig. 17.5, p. 409, on a probability space: almost surely, if the date-`(s+1)`
news is a permanent rise of expected rates from horizon `T`, the inflation news is
`path(1{· ≥ T}, δ)`, `δ = ΔE_{s+1} π_{s+1}`, converges to one and exceeds `δ λ₁^{−j}` at every
horizon `j ≥ 1`. -/
theorem news_rise_ae {σ β κ M Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i r x π : ℕ → Ω → ℝ}
    (h : ModelM S σ β κ i r x π) (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ M)
    (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) (s T : ℕ) :
    ∀ᵐ ω ∂S.μ, (∀ k, S.innov s (i (s + 1 + k)) ω = stepI T k) →
      (fun j => S.innov s (π (s + 1 + j)) ω) = path σ β κ (stepI T) (S.innov s (π (s + 1)) ω) ∧
      Tendsto (fun j => S.innov s (π (s + 1 + j)) ω) atTop (𝓝 1) ∧
      ∀ j, S.innov s (π (s + 1)) ω * (lam1 σ β κ)⁻¹ ^ (j + 1) <
        S.innov s (π (s + 1 + (j + 1))) ω := by
  filter_upwards [news_path_ae S ha hβ h hi hπ s] with ω hω hnews
  have hp := hω.1
  have hn : (fun j => S.innov s (i (s + 1 + j)) ω) = stepI T := funext hnews
  rw [hn] at hp
  set δ := S.innov s (π (s + 1)) ω
  have hb := path_bounded ha hβ (stepI_bound T) δ
  refine ⟨hp, ?_, fun j => ?_⟩
  · rw [hp]
    exact tendsto_pi ha hβ (stepI_bound T) (stepI_tendsto T) hb
      ((second_iff_factor ha hβ (stepI_bound T) hb).mpr (path_factor ha hβ _ δ))
  · have e := congrFun hp (j + 1)
    rw [e, ← path_zero_rate σ β κ δ (j + 1)]
    exact rise_raises_inflation ha hβ T δ j

/-- Cochrane (2023), Fig. 17.5, p. 409 (solid line), on a probability space: almost surely, if
moreover the unexpected inflation is the two-sided value `antPath T 0`, the inflation news is
`FullModel.antPath T` (positive, strictly increasing, below one) and the output news is negative
up to and including the rise. -/
theorem news_rise_twoSided_ae {σ β κ M Mπ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    {i r x π : ℕ → Ω → ℝ} (h : ModelM S σ β κ i r x π) (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ M)
    (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) (s T : ℕ) :
    ∀ᵐ ω ∂S.μ, (∀ k, S.innov s (i (s + 1 + k)) ω = stepI T k) →
      S.innov s (π (s + 1)) ω = antPath σ β κ T 0 →
      (fun j => S.innov s (π (s + 1 + j)) ω) = antPath σ β κ T ∧
      (∀ j, 0 < S.innov s (π (s + 1 + j)) ω ∧ S.innov s (π (s + 1 + j)) ω < 1) ∧
      StrictMono (fun j => S.innov s (π (s + 1 + j)) ω) ∧
      ∀ j, j ≤ T → S.innov s (x (s + 1 + j)) ω < 0 := by
  have ha := mul_pos hσ hκ
  filter_upwards [news_rise_ae S ha hβ h hi hπ s T, news_path_ae S ha hβ h hi hπ s]
    with ω hr hω hnews hδ
  have hant : (fun j => S.innov s (π (s + 1 + j)) ω) = antPath σ β κ T := by
    rw [(hr hnews).1, hδ]
    rfl
  refine ⟨hant, fun j => ?_, ?_, fun j hj => ?_⟩
  · rw [congrFun hant j]
    exact ⟨antPath_pos ha hβ T j, antPath_lt_one ha hβ T j⟩
  · rw [hant]; exact antPath_strictMono ha hβ T
  · rw [hω.2 j, congrFun hant j, congrFun hant (j + 1)]
    exact antPath_x_neg hσ hκ hβ hj

end Cochrane.KeynesianStickyPrices.TidyR5StochasticPathsMeasure
