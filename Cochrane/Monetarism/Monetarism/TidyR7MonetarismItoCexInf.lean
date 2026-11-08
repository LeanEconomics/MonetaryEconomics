/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR7MonetarismItoCex

/-!
# An infinite-horizon Brownian economy: transversality holds, the book's (1.33) fails

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", p. 567, eqs. (1.32)–(1.33). Non-vacuity of
`TidyR7MonetarismItoValuation.valuation_1_33_ito_book_iff` on `[0, ∞)`.

## Economy 3 (`infModel`)

On the constructed Brownian motion (`TidyR7MonetarismItoCex.bmF`), with `φ = rampDown`
(`φ = 1 − u` on `[0, 1]`, `0` after) and `I_u = ∫_0^u φ dW`: `P = 1`, `Λ = Λ/P = 1 + I`,
bonds `B = 1/3 − I` (`σ_B = −φ`, correlated with `Λ/P`), money `M = M₀ + I` (`σ_M = φ`, forced by
(1.31)), `i = i^m = 0`, surplus `0`. Then `n_0B_0 = 1/3`, and for `T ≥ 1`:
`E_0[n_TB_T] = 1/3 − ∫_0^T φ² = 0` (`inf_tvc_value`), so **the transversality condition holds**
along `T_k = k + 1` (`inf_tvc`); the bracket is `∫_0^T σ_Xσ_B = −1/3` (`inf_bracket`);
* the corrected (1.33) holds: `E_0[F^c_{T_k}] → 1/3 = n_0B_0` (`inf_corrected`);
* **the book's (1.33) fails**: `E_0[F_{T_k}] → 0 ≠ 1/3 = n_0B_0` (`inf_book_limit`,
  `inf_book_fails`); `inf_headline` collects these.
`𝓕_0` is trivial (`bmF_zero`), so `E_0` is the expectation.
-/

namespace Cochrane.Monetarism.TidyR7MonetarismItoCexInf

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoSums Cochrane.Monetarism.TidyR7ItoIntegral
  Cochrane.Monetarism.TidyR7ItoUnbounded Cochrane.Monetarism.TidyR7ItoProducts
  Cochrane.Monetarism.TidyR7ItoProcess Cochrane.Monetarism.TidyR7ItoBondStep
  Cochrane.Monetarism.TidyR7MonetarismModel Cochrane.Monetarism.TidyR7MonetarismIto
  Cochrane.Monetarism.TidyR7MonetarismItoValuation Cochrane.Monetarism.TidyR7MonetarismItoCex
  Cochrane.Monetarism.TidyR7BrownianExist Cochrane.Monetarism.TidyR7ItoBridge
  Cochrane.Monetarism.TidyR7BrownianSchauder
open scoped ENNReal NNReal

/-- Cochrane (2023), A1 §1.6, p. 567: `∫_0^1 (1 − u)² du = 1/3`. -/
theorem integral_one_sub_sq : ∫ u in (0 : ℝ)..1, (1 - u) ^ 2 = 1 / 3 := by
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ 2)]
  norm_num [integral_pow]

/-- Cochrane (2023), A1 §1.6, p. 567: `∫_0^T φ² du = 1/3` for `T ≥ 1`, `φ = rampDown`. -/
theorem integral_rampDown_sq {T : ℝ} (hT : 1 ≤ T) : ∫ u in (0 : ℝ)..T, rampDown u ^ 2 = 1 / 3 := by
  have c : Continuous fun u => rampDown u ^ 2 := continuous_ramps.1.pow 2
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1) (c.intervalIntegrable _ _)
    (c.intervalIntegrable _ _)]
  have h1 : ∫ u in (0 : ℝ)..1, rampDown u ^ 2 = ∫ u in (0 : ℝ)..1, (1 - u) ^ 2 := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le zero_le_one] at hu
    simp only [rampDown, max_eq_right (by linarith [hu.2] : (0 : ℝ) ≤ 1 - u),
      min_eq_right (by linarith [hu.1] : 1 - u ≤ 1)]
  have h2 : ∫ u in (1 : ℝ)..T, rampDown u ^ 2 = ∫ _u in (1 : ℝ)..T, (0 : ℝ) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hT] at hu
    simp only [rampDown, max_eq_left (by linarith [hu.1] : 1 - u ≤ 0),
      min_eq_right (zero_le_one' ℝ)]
    norm_num
  rw [h1, h2, integral_one_sub_sq]
  simp

/-- Cochrane (2023), A1 §1.6, p. 567: **`𝓕_0` is trivial** for the natural filtration of the
constructed Brownian motion (`W_0 = 0`), so `E_0` is the expectation. -/
theorem bmF_zero : bmF 0 = ⊥ := by
  change bmFiltration bmPath measurable_bmPath (0 : ℝ).toNNReal = ⊥
  rw [Real.toNNReal_zero, bmFiltration_eq_comap]
  have : (fun ω (r : Set.Iic (0 : ℝ≥0)) => bmPath r ω) = fun _ _ => 0 := by
    funext ω r
    have h : (r : ℝ≥0) = 0 := le_antisymm r.2 (by positivity)
    rw [h, bmPath_zero]
  rw [this]
  exact MeasurableSpace.comap_const _

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (economy 3): `I_u = ∫_0^u φ dW`. -/
noncomputable abbrev infI : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => itoInt gaussSeq bmF bmPath (fun r _ => rampDown r) 0 u ω

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (economy 3): `Λ = Λ/P = 1 + I`. -/
noncomputable abbrev infΛ : ℝ → (ℕ → ℝ) → ℝ := fun u ω => 1 + infI u ω

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (economy 3): bonds `B = 1/3 + ∫_0^· (−φ) dW`. -/
noncomputable abbrev infB : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => 1 / 3 + itoInt gaussSeq bmF bmPath (fun r _ => -1 * rampDown r) 0 u ω

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567 (economy 3): money `M = M₀ + I`. -/
noncomputable abbrev infM (M0 : ℝ) : ℝ → (ℕ → ℝ) → ℝ := fun u ω => M0 + infI u ω

/-- **Cochrane (2023), A1 §1.6, (1.31)–(1.34), pp. 567–568: economy 3 is a model with
diffusive bonds** on every `[0, T]`: `P = 1`, `Λ/P = 1 + I`, `σ_X = φ`, `B = 1/3 − I`
(`σ_B = −φ`), `M = M₀ + I` (`σ_M = φ`), `i = i^m = s = 0`. -/
theorem infModel (M0 : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ItoMonetaryModel gaussSeq bmF bmPath infΛ (constP 1) infB (infM M0) (constP 0)
      (constP 0) (constP 0) (constP 0) (fun r _ => -1 * rampDown r) (constP 0)
      (fun r _ => rampDown r) (fun r _ => rampDown r) 0 T 0 1 0 1 0 1 := by
  have hBM := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hBM measurable_bmPath
  have hD : ItoIntegrand gaussSeq bmF (fun r _ => rampDown r) 0 T 1 :=
    itoIntegrand_deterministic continuous_ramps.1.continuousOn fun u _ => abs_clamp_le _
  have hD' : ItoIntegrand gaussSeq bmF (fun r _ => -1 * rampDown r) 0 T 1 :=
    itoIntegrand_deterministic (continuous_ramps.1.const_mul (-1)).continuousOn fun u _ => by
      rw [neg_one_mul, abs_neg]; exact abs_clamp_le _
  exact
    { P_pos := fun _ _ => one_pos
      disc_ito := itoProcess_shift hBM measurable_bmPath h𝓕 le_rfl le_rfl hT hD 1
        (funext fun u => funext fun ω => by simp [disc]) (funext fun u => funext fun ω => by simp)
      bonds_ito := itoProcess_shift hBM measurable_bmPath h𝓕 le_rfl le_rfl hT hD' (1 / 3) rfl rfl
      money_ito := itoProcess_shift hBM measurable_bmPath h𝓕 le_rfl le_rfl hT hD M0 rfl rfl
      flow_drift := fun _ _ => by simp [flowRate]
      flow_diff := fun _ _ => by simp }

/-- Cochrane (2023), A1 §1.6, p. 567 (economy 3): `n_0B_0 = 1/3`. -/
theorem inf_initial (ω : ℕ → ℝ) : disc infΛ (constP 1) 0 ω * infB 0 ω = 1 / 3 := by
  have h0 : ∀ H : ℝ → (ℕ → ℝ) → ℝ, itoInt gaussSeq bmF bmPath H 0 0 = 0 := fun _ =>
    itoInt_of_le le_rfl
  simp only [disc, infΛ, infB, infI, constP, h0, Pi.zero_apply]
  norm_num

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567 (economy 3): `E[n_TB_T] = 1/3 − ∫_0^T φ² = 0`**
for `T ≥ 1` (Wiener isometry `TidyR7ItoBridge.integral_itoInt_deterministic_sq`). -/
theorem inf_tvc_value {T : ℝ} (hT : 1 ≤ T) :
    ∫ ω, disc infΛ (constP 1) T ω * infB T ω ∂gaussSeq = 0 := by
  have := isProb
  have hBM := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hBM measurable_bmPath
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hD : ItoIntegrand gaussSeq bmF (fun r _ => rampDown r) 0 T 1 :=
    itoIntegrand_deterministic continuous_ramps.1.continuousOn fun u _ => abs_clamp_le _
  have hneg := itoInt_const_mul hBM measurable_bmPath h𝓕 le_rfl hD (-1)
  have mI : MemLp (infI T) 2 gaussSeq := memLp_itoInt hBM measurable_bmPath h𝓕 le_rfl hD
  have e : (fun ω => disc infΛ (constP 1) T ω * infB T ω) =ᵐ[gaussSeq]
      fun ω => 1 / 3 + (-2 / 3) * infI T ω - infI T ω ^ 2 := by
    filter_upwards [hneg] with ω hω
    simp only [disc, infΛ, infB, constP, div_one]
    rw [hω]
    ring
  have i1 : Integrable (infI T) gaussSeq := mI.integrable one_le_two
  have i2 : Integrable (fun ω => infI T ω ^ 2) gaussSeq := mI.integrable_sq
  have h12 : Integrable (fun ω => (1 : ℝ) / 3 + -2 / 3 * infI T ω) gaussSeq :=
    (integrable_const _).add (i1.const_mul _)
  have hsplit : ∫ ω, ((1 : ℝ) / 3 + -2 / 3 * infI T ω - infI T ω ^ 2) ∂gaussSeq
      = 1 / 3 + -2 / 3 * (∫ ω, infI T ω ∂gaussSeq) - ∫ ω, infI T ω ^ 2 ∂gaussSeq := by
    rw [integral_sub h12 i2, integral_add (integrable_const _) (i1.const_mul _),
      integral_const_mul]
    simp
  rw [integral_congr_ae e, hsplit, integral_itoInt hBM measurable_bmPath h𝓕 le_rfl hD,
    integral_itoInt_deterministic_sq hBM measurable_bmPath h𝓕 le_rfl hT0
      continuous_ramps.1.continuousOn (fun u _ => abs_clamp_le _),
    integral_rampDown_sq hT]
  simp

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567 (economy 3): the transversality condition holds**,
`E_0[n_{T_k}B_{T_k}] = 0` for `T_k = k + 1`. -/
theorem inf_tvc :
    ∀ᵐ ω ∂gaussSeq, Tendsto (fun k : ℕ => gaussSeq[fun ω => disc infΛ (constP 1) ((k : ℝ) + 1) ω
      * infB ((k : ℝ) + 1) ω | bmF 0] ω) atTop (𝓝 0) := by
  have := isProb
  refine ae_of_all _ fun ω => ?_
  have e : ∀ k : ℕ, gaussSeq[fun ω => disc infΛ (constP 1) ((k : ℝ) + 1) ω
      * infB ((k : ℝ) + 1) ω | bmF 0] ω = 0 := fun k => by
    rw [bmF_zero, condExp_bot, inf_tvc_value (by have := k.cast_nonneg (α := ℝ); linarith)]
  simp_rw [e]
  exact tendsto_const_nhds

/-- **Cochrane (2023), A1 §1.6, (1.32)–(1.33), p. 567 (economy 3): the bracket**
`∫_0^T σ_Xσ_B du = −∫_0^T φ² = −1/3` for `T ≥ 1`. -/
theorem inf_bracket {T : ℝ} (hT : 1 ≤ T) (ω : ℕ → ℝ) :
    bracket (fun r _ => rampDown r) (fun r _ => -1 * rampDown r) 0 T ω = -(1 / 3) := by
  have e : (fun u => rampDown u * (-1 * rampDown u)) = fun u => -(rampDown u ^ 2) :=
    funext fun u => by ring
  simp only [bracket]
  rw [e, intervalIntegral.integral_neg, integral_rampDown_sq hT]

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567 (economy 3): the model holds on every `[0, T]`,
`T > 0`, as `TidyR7MonetarismItoValuation` requires. -/
theorem infModels (M0 : ℝ) : ∀ T, (0 : ℝ) < T →
    ItoMonetaryModel gaussSeq bmF bmPath infΛ (constP 1) infB (infM M0) (constP 0)
      (constP 0) (constP 0) (constP 0) (fun r _ => -1 * rampDown r) (constP 0)
      (fun r _ => rampDown r) (fun r _ => rampDown r) 0 T 0 1 0 1 0 1 :=
  fun _ hT => infModel M0 hT.le

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567 (economy 3): the corrected (1.33) holds**,
`E_0[F^c_{T_k}] → n_0B_0 = 1/3` a.s., `T_k = k + 1`.
An instance of `TidyR7MonetarismItoValuation.valuation_1_33_ito_seq`. -/
theorem inf_corrected (M0 : ℝ) :
    ∀ᵐ ω ∂gaussSeq, Tendsto (fun k : ℕ => gaussSeq[flowItoC gaussSeq bmF bmPath infΛ (constP 1)
      (infM M0) (constP 0) (constP 0) (constP 0) (fun r _ => rampDown r)
      (fun r _ => rampDown r) (fun r _ => -1 * rampDown r) 0 ((k : ℝ) + 1) | bmF 0] ω)
      atTop (𝓝 (disc infΛ (constP 1) 0 ω * infB 0 ω)) :=
  (valuation_1_33_ito_seq (infModels M0) isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) le_rfl
    (T := fun k : ℕ => (k : ℝ) + 1) (fun k => by positivity)).2 inf_tvc

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567 (economy 3): the book's flow has
`E_0[F_{T_k}] → 0`** a.s. (`= E_0[F^c_{T_k}] + E_0[bracket] → 1/3 − 1/3`). -/
theorem inf_book_limit (M0 : ℝ) :
    ∀ᵐ ω ∂gaussSeq, Tendsto (fun k : ℕ => gaussSeq[flowItoBook gaussSeq bmF bmPath infΛ
      (constP 1) (infM M0) (constP 0) (constP 0) (constP 0) (fun r _ => rampDown r) 0
        ((k : ℝ) + 1) | bmF 0] ω) atTop (𝓝 0) := by
  have := isProb
  have hBM := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hBM measurable_bmPath
  have hadd : ∀ᵐ ω ∂gaussSeq, ∀ k : ℕ, gaussSeq[flowItoBook gaussSeq bmF bmPath infΛ
      (constP 1) (infM M0) (constP 0) (constP 0) (constP 0) (fun r _ => rampDown r) 0
        ((k : ℝ) + 1) | bmF 0] ω =
      gaussSeq[flowItoC gaussSeq bmF bmPath infΛ (constP 1) (infM M0) (constP 0) (constP 0)
        (constP 0) (fun r _ => rampDown r) (fun r _ => rampDown r)
        (fun r _ => -1 * rampDown r) 0 ((k : ℝ) + 1) | bmF 0] ω + -(1 / 3) := by
    refine ae_all_iff.2 fun k => ?_
    have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by have := k.cast_nonneg (α := ℝ); linarith
    obtain ⟨-, i2, i3⟩ := integrable_flows (infModels M0) hBM measurable_bmPath h𝓕 le_rfl hk
    have eb : bracket (fun r _ => rampDown r) (fun r _ => -1 * rampDown r) 0 ((k : ℝ) + 1)
        = fun _ => -(1 / 3) := funext fun ω => inf_bracket hk1 ω
    have e : flowItoBook gaussSeq bmF bmPath infΛ (constP 1) (infM M0) (constP 0) (constP 0)
        (constP 0) (fun r _ => rampDown r) 0 ((k : ℝ) + 1) =
        flowItoC gaussSeq bmF bmPath infΛ (constP 1) (infM M0) (constP 0) (constP 0)
          (constP 0) (fun r _ => rampDown r) (fun r _ => rampDown r)
          (fun r _ => -1 * rampDown r) 0 ((k : ℝ) + 1)
        + bracket (fun r _ => rampDown r) (fun r _ => -1 * rampDown r) 0 ((k : ℝ) + 1) :=
      funext fun ω => by simp only [flowItoC, Pi.add_apply]; ring
    filter_upwards [condExp_add i3 i2 (bmF 0)] with ω h
    rw [e, h, Pi.add_apply, eb, condExp_const (bmF.le 0)]
  filter_upwards [inf_corrected M0, hadd] with ω h1 h2
  simp_rw [h2]
  rw [inf_initial] at h1
  have := h1.add_const (-(1 / 3 : ℝ))
  rwa [show (1 : ℝ) / 3 + -(1 / 3) = 0 by norm_num] at this

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567 (economy 3): the book's (1.33) fails** although
the transversality condition holds: `E_0[F_{T_k}]` does not converge to `n_0B_0 = 1/3` on any
set of positive probability. -/
theorem inf_book_fails (M0 : ℝ) :
    ¬ ∀ᵐ ω ∂gaussSeq, Tendsto (fun k : ℕ => gaussSeq[flowItoBook gaussSeq bmF bmPath infΛ
      (constP 1) (infM M0) (constP 0) (constP 0) (constP 0) (fun r _ => rampDown r) 0
        ((k : ℝ) + 1) | bmF 0] ω) atTop (𝓝 (disc infΛ (constP 1) 0 ω * infB 0 ω)) := by
  have := isProb
  intro h
  obtain ⟨ω, h1, h2⟩ := (h.and (inf_book_limit M0)).exists
  rw [inf_initial] at h1
  have := tendsto_nhds_unique h1 h2
  norm_num at this

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: headline (economy 3).** Transversality holds,
the corrected (1.33) holds (`E_0[F^c_{T_k}] → 1/3 = n_0B_0`), the bracket is `−1/3`, and the
book's (1.33) fails (`E_0[F_{T_k}] → 0 ≠ 1/3`). -/
theorem inf_headline (M0 : ℝ) :
    (∀ᵐ ω ∂gaussSeq, Tendsto (fun k : ℕ => gaussSeq[fun ω => disc infΛ (constP 1)
      ((k : ℝ) + 1) ω * infB ((k : ℝ) + 1) ω | bmF 0] ω) atTop (𝓝 0)) ∧
    (∀ ω, disc infΛ (constP 1) 0 ω * infB 0 ω = 1 / 3) ∧
    (∀ ω : ℕ → ℝ, bracket (fun r _ => rampDown r) (fun r _ => -1 * rampDown r) 0 1 ω = -(1 / 3)) ∧
    (∀ᵐ ω ∂gaussSeq, Tendsto (fun k : ℕ => gaussSeq[flowItoC gaussSeq bmF bmPath infΛ
      (constP 1) (infM M0) (constP 0) (constP 0) (constP 0) (fun r _ => rampDown r)
      (fun r _ => rampDown r) (fun r _ => -1 * rampDown r) 0 ((k : ℝ) + 1) | bmF 0] ω)
      atTop (𝓝 (1 / 3))) ∧
    (∀ᵐ ω ∂gaussSeq, Tendsto (fun k : ℕ => gaussSeq[flowItoBook gaussSeq bmF bmPath infΛ
      (constP 1) (infM M0) (constP 0) (constP 0) (constP 0) (fun r _ => rampDown r) 0
        ((k : ℝ) + 1) | bmF 0] ω) atTop (𝓝 0)) ∧
    ¬ (∀ᵐ ω ∂gaussSeq, Tendsto (fun k : ℕ => gaussSeq[flowItoBook gaussSeq bmF bmPath infΛ
      (constP 1) (infM M0) (constP 0) (constP 0) (constP 0) (fun r _ => rampDown r) 0
        ((k : ℝ) + 1) | bmF 0] ω) atTop (𝓝 (disc infΛ (constP 1) 0 ω * infB 0 ω))) := by
  refine ⟨inf_tvc, inf_initial, fun ω => inf_bracket le_rfl ω, ?_, inf_book_limit M0,
    inf_book_fails M0⟩
  filter_upwards [inf_corrected M0] with ω h
  rwa [inf_initial] at h

end Cochrane.Monetarism.TidyR7MonetarismItoCexInf
