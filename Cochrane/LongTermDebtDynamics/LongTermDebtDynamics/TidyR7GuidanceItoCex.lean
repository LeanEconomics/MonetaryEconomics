/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR7GuidanceItoBM

/-!
# Random future rates: the forward-guidance formula needs a correction

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.2.1, p. 561.
The book's continuous-time formula `P_0/P − 1 = e^{−(r+ϖ)T}((r+ϖ)/(i+ϖ) − 1)` is derived for a
known rate path. Under uncertainty it holds verbatim, state by state, when the path is known
(`TidyR7GuidanceItoValuation.guidance_jump_ito`, non-vacuous by
`TidyR7GuidanceItoBM.bm_guidance_jump`). Here the rate from `T` on is news revealed at `T`:
`ι = i₁` if `W_T > 0`, `ι = i₂` otherwise (`newsRate`), on the constructed Brownian motion,
with the discount factor `Λ_t = e^{−rt}(1 + κW_t)` before `T`
(`TidyR7GuidanceItoBM.bmSDF`). Write `p = P(W_T > 0)` and `m = E[W_T; W_T > 0]`
(`0 < p < 1`, `m > 0`: `newsProb_pos`, `newsProb_lt_one`, `newsMean_pos`) and
`J(x) = cfgJump r x ϖ T`.

## Main results

* `bmF_zero`, `condExp_bmF_zero`: the date-0 information is trivial, `E_0 = E`.
* `integral_news`: `E[(1 + κW_T) g(ι)] = g(i₂) + (g(i₁) − g(i₂))(p + κm)`.
* `bm_random_jump`: with constant surpluses and any price levels satisfying the valuation
  equations, `P_0/P_0' − 1 = J(i₂) + (J(i₁) − J(i₂))(p + κm)` a.s.;
  `bm_random_valuation`: such price levels exist when `0 ≤ p + κm ≤ 1`.
* **Corrections** (`bm_jensen`, `bm_covariance`, `bm_random_headline`):
  (i) even without inflation risk (`κ = 0`), the jump `pJ(i₁) + (1−p)J(i₂)` strictly exceeds
  the book's formula at the expected rate, `J(E ι)` (Jensen: `J` is strictly convex);
  (ii) with inflation risk correlated with the news (`κ ≠ 0`), the jump differs from the
  average of the book's formula over the states, `E[J(ι)]`, by the covariance
  `κm(J(i₁) − J(i₂)) = Cov(e^{rT}Λ_T/Λ_0, J(ι)) ≠ 0`: the expectation is under the `T`-forward
  measure `e^{rT}Λ_T/Λ_0`, not under the physical measure.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR7GuidanceItoCex

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.LongTermDebtDynamics.TidyR7BrownianExist
  Cochrane.LongTermDebtDynamics.TidyR7BrownianSchauder
  Cochrane.LongTermDebtDynamics.TidyR7BrownianTools
  Cochrane.LongTermDebtDynamics.TidyR7BrownianQV
  Cochrane.LongTermDebtDynamics.TidyR7GuidanceSDF
  Cochrane.LongTermDebtDynamics.TidyR7GuidanceItoValuation
  Cochrane.LongTermDebtDynamics.TidyR7GuidanceItoBM
  Cochrane.LongTermDebtDynamics.ForwardGuidance
open scoped NNReal

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: at date `0` the natural filtration of
`bmPath` is trivial (`W_0 = 0` on every path). -/
theorem bmF_zero : bmF 0 = ⊥ := by
  change bmFiltration bmPath measurable_bmPath (0 : ℝ).toNNReal = ⊥
  rw [Real.toNNReal_zero, bmFiltration_eq_comap]
  have h : (fun ω (r : Set.Iic (0 : ℝ≥0)) => bmPath r ω) = fun _ _ => 0 := by
    funext ω r
    have hr : (r : ℝ≥0) = 0 := le_antisymm r.2 bot_le
    rw [hr, bmPath_zero]
  rw [h]
  exact MeasurableSpace.comap_const _

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: with trivial date-0 information the
date-0 conditional expectation is the expectation, `E_0 f = E f`.
Mathlib `MeasureTheory.condExp_bot'` after `bmF_zero`. -/
theorem condExp_bmF_zero (f : (ℕ → ℝ) → ℝ) :
    gaussSeq[f | bmF 0] = fun _ => ∫ ω, f ω ∂gaussSeq := by
  have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
  rw [bmF_zero, condExp_bot']
  funext _
  simp

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: news at `T`.** The rate from `T` on is
`i₁` if `W_T > 0` and `i₂` otherwise. -/
noncomputable def newsRate (i₁ i₂ T : ℝ) (ω : ℕ → ℝ) : ℝ := if 0 < bmW T ω then i₁ else i₂

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the news event `{W_T > 0}`. -/
def newsSet (T : ℝ) : Set (ℕ → ℝ) := {ω | 0 < bmW T ω}

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the news event is known at `T`. -/
theorem measurableSet_newsSet_T (T : ℝ) : MeasurableSet[bmF T] (newsSet T) :=
  ((bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath).adapted T).measurable
    measurableSet_Ioi

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the news event is measurable. -/
theorem measurableSet_newsSet (T : ℝ) : MeasurableSet (newsSet T) :=
  bmF.le T _ (measurableSet_newsSet_T T)

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the news rate is known at `T`. -/
theorem stronglyMeasurable_newsRate (i₁ i₂ T : ℝ) :
    StronglyMeasurable[bmF T] (newsRate i₁ i₂ T) :=
  StronglyMeasurable.ite (measurableSet_newsSet_T T) stronglyMeasurable_const
    stronglyMeasurable_const

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the news rate takes two values. -/
theorem newsRate_finite (i₁ i₂ T : ℝ) : ∃ S : Finset ℝ, ∀ ω, newsRate i₁ i₂ T ω ∈ S :=
  ⟨{i₁, i₂}, fun ω => by unfold newsRate; split_ifs <;> simp⟩

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the probability of the news,
`p = P(W_T > 0)`. -/
noncomputable def newsProb (T : ℝ) : ℝ := gaussSeq.real (newsSet T)

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: `m = E[W_T; W_T > 0]`. -/
noncomputable def newsMean (T : ℝ) : ℝ := ∫ ω in newsSet T, bmW T ω ∂gaussSeq

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: a set of positive Lebesgue measure has
positive probability under the law of `W_T`, `T > 0`. -/
theorem gaussSeq_preimage_pos {T : ℝ} (hT : 0 < T) {A : Set ℝ} (hA : MeasurableSet A)
    (hvol : volume A ≠ 0) : gaussSeq (bmW T ⁻¹' A) ≠ 0 := by
  have hlaw := (isPreBrownianReal_bmPath.hasLaw_eval T.toNNReal).map_eq
  have hne : T.toNNReal ≠ 0 := by simpa using hT
  have h1 : gaussSeq (bmW T ⁻¹' A) = gaussianReal 0 T.toNNReal A := by
    rw [← hlaw, Measure.map_apply (measurable_bmPath _) hA]
    rfl
  rw [h1]
  exact fun h => hvol ((gaussianReal_absolutelyContinuous' 0 hne) h)

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: `p > 0` for `T > 0`. -/
theorem newsProb_pos {T : ℝ} (hT : 0 < T) : 0 < newsProb T := by
  have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
  have h := gaussSeq_preimage_pos hT measurableSet_Ioi (A := Set.Ioi 0) (by simp)
  rw [newsProb, measureReal_def]
  exact ENNReal.toReal_pos h (measure_ne_top _ _)

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: `p < 1` for `T > 0`. -/
theorem newsProb_lt_one {T : ℝ} (hT : 0 < T) : newsProb T < 1 := by
  have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
  have h := gaussSeq_preimage_pos hT measurableSet_Iic (A := Set.Iic 0) (by simp)
  have hc : (newsSet T)ᶜ = bmW T ⁻¹' Set.Iic 0 := by
    ext ω
    simp [newsSet]
  have hadd := measure_add_measure_compl (μ := gaussSeq) (measurableSet_newsSet T)
  rw [measure_univ, hc] at hadd
  have hlt : gaussSeq (newsSet T) < 1 := by
    rw [← hadd]
    exact ENNReal.lt_add_right (measure_ne_top _ _) h
  rw [newsProb, measureReal_def]
  have := ENNReal.toReal_strict_mono ENNReal.one_ne_top hlt
  simpa using this

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: `m = E[W_T; W_T > 0] > 0` for `T > 0`. -/
theorem newsMean_pos {T : ℝ} (hT : 0 < T) : 0 < newsMean T := by
  have hint : IntegrableOn (bmW T) (newsSet T) gaussSeq := (integrable_bmW T).integrableOn
  rw [newsMean, setIntegral_pos_iff_support_of_nonneg_ae
    (by filter_upwards [ae_restrict_mem (measurableSet_newsSet T)] with ω hω
        exact le_of_lt hω) hint]
  have hs : Function.support (bmW T) ∩ newsSet T = newsSet T :=
    Set.inter_eq_right.2 fun ω hω => ne_of_gt hω
  rw [hs]
  exact pos_iff_ne_zero.2 (gaussSeq_preimage_pos hT measurableSet_Ioi (A := Set.Ioi 0) (by simp))

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: expectations of functions of the news,
weighted by `1 + κW_T`**: `E[(1 + κW_T) g(ι)] = g(i₂) + (g(i₁) − g(i₂))(p + κm)`. -/
theorem integral_news (κ : ℝ) {T : ℝ} (i₁ i₂ : ℝ) (g : ℝ → ℝ) :
    ∫ ω, (1 + κ * bmW T ω) * g (newsRate i₁ i₂ T ω) ∂gaussSeq
      = g i₂ + (g i₁ - g i₂) * (newsProb T + κ * newsMean T) := by
  have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
  have hS := measurableSet_newsSet T
  have hW := integrable_bmW T
  have h1 : Integrable (fun ω => 1 + κ * bmW T ω) gaussSeq :=
    (integrable_const 1).add (hW.const_mul κ)
  have hpt : ∀ ω, (1 + κ * bmW T ω) * g (newsRate i₁ i₂ T ω) = g i₂ * (1 + κ * bmW T ω)
      + (g i₁ - g i₂) * (newsSet T).indicator (fun ω => 1 + κ * bmW T ω) ω := by
    intro ω
    by_cases h : ω ∈ newsSet T
    · have h' : 0 < bmW T ω := h
      simp only [newsRate, h', ↓reduceIte, Set.indicator_of_mem h]
      ring
    · have h' : ¬ 0 < bmW T ω := h
      simp only [newsRate, h', ↓reduceIte, Set.indicator_of_notMem h]
      ring
  simp_rw [hpt]
  rw [integral_add (h1.const_mul _) ((h1.indicator hS).const_mul _), integral_const_mul,
    integral_const_mul, integral_indicator hS, integral_add (integrable_const 1)
    (hW.const_mul κ), integral_const_mul, integral_add (integrable_const 1).integrableOn
    (hW.const_mul κ).integrableOn, integral_const_mul, setIntegral_const]
  have h0 : ∫ ω, bmW T ω ∂gaussSeq = 0 := isPreBrownianReal_bmPath.integral_eval _
  rw [h0]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one, mul_zero, add_zero]
  rw [newsProb, newsMean]


/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the forward weight of the model economy,
`e^{rT}Λ_T = 1 + κW_T`. -/
theorem exp_mul_bmSDF_T (κ r T : ℝ) (ι : (ℕ → ℝ) → ℝ) (ω : ℕ → ℝ) :
    Real.exp (r * T) * bmSDF κ r T ι T ω = 1 + κ * bmW T ω := by
  simp only [bmSDF, le_refl, ↓reduceIte, ← mul_assoc, ← Real.exp_add]
  simp

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the value of the debt with news at
`T`.** In the model economy with `ι = newsRate i₁ i₂ T` (`r, i₁, i₂ ≥ 0`, `ϖ > 0`, `T ≥ 0`), a.s.
`debtValue = V(i₂) + (V(i₁) − V(i₂))(p + κm)` with `V(x) = cfgValue r x ϖ T`. -/
theorem bm_random_debtValue (κ : ℝ) {r i₁ i₂ ϖ T : ℝ} (hr : 0 ≤ r) (hi₁ : 0 ≤ i₁) (hi₂ : 0 ≤ i₂)
    (hϖ : 0 < ϖ) (hT : 0 ≤ T) :
    ∀ᵐ ω ∂gaussSeq, debtValue gaussSeq bmF (bmSDF κ r T (newsRate i₁ i₂ T)) ϖ ω
      = cfgValue r i₂ ϖ T + (cfgValue r i₁ ϖ T - cfgValue r i₂ ϖ T)
        * (newsProb T + κ * newsMean T) := by
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  have hι0 : ∀ ω, 0 ≤ newsRate i₁ i₂ T ω := fun ω => by
    unfold newsRate; split_ifs <;> assumption
  have hG := guidanceSDF_bm κ hr hT (stronglyMeasurable_newsRate i₁ i₂ T)
    (newsRate_finite i₁ i₂ T) hι0
  have hI := integrable_debt_bm κ hr hT hϖ
    ((stronglyMeasurable_newsRate i₁ i₂ T).mono (bmF.le T)).measurable hι0
  have hV := condExp_debtValue_random hB measurable_bmPath h𝓕 hT hG (by linarith)
    (fun ω => by linarith [hι0 ω]) hI
  filter_upwards [hV] with ω hω
  have h0 : bmSDF κ r T (newsRate i₁ i₂ T) 0 ω = 1 := by simp [bmSDF, hT, bmW_zero]
  rw [debtValue, hω, condExp_bmF_zero, h0, div_one]
  simp_rw [exp_mul_bmSDF_T]
  exact integral_news κ i₁ i₂ (fun x => cfgValue r x ϖ T)

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561, with news at `T`: the price-level
jump.** In the model economy (`r > 0`, `i₁, i₂ ≥ 0`, `ϖ > 0`, `T ≥ 0`, constant surpluses `s̄ > 0`,
`B_0 = 1`), against the no-guidance economy `bmSDF κ' r T (fun _ => r)`, any positive price
levels satisfying the valuation equations have, a.s.,
`P_0/P_0' − 1 = J(i₂) + (J(i₁) − J(i₂))(p + κm)` with `J(x) = cfgJump r x ϖ T`. -/
theorem bm_random_jump (κ κ' : ℝ) {r i₁ i₂ ϖ T sbar : ℝ} (hr : 0 < r) (hi₁ : 0 ≤ i₁)
    (hi₂ : 0 ≤ i₂) (hϖ : 0 < ϖ) (hT : 0 ≤ T) (hs : 0 < sbar) {P0 P0' : (ℕ → ℝ) → ℝ}
    (hP0 : ∀ ω, 0 < P0 ω) (hP0' : ∀ ω, 0 < P0' ω)
    (hval : ∀ᵐ ω ∂gaussSeq, 1 / P0 ω * debtValue gaussSeq bmF
      (bmSDF κ r T (newsRate i₁ i₂ T)) ϖ ω = pvSurplus gaussSeq bmF r (fun _ _ => sbar) ω)
    (hval' : ∀ᵐ ω ∂gaussSeq, 1 / P0' ω * debtValue gaussSeq bmF
      (bmSDF κ' r T fun _ => r) ϖ ω = pvSurplus gaussSeq bmF r (fun _ _ => sbar) ω) :
    ∀ᵐ ω ∂gaussSeq, P0 ω / P0' ω - 1 = cfgJump r i₂ ϖ T
      + (cfgJump r i₁ ϖ T - cfgJump r i₂ ϖ T) * (newsProb T + κ * newsMean T) := by
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  have hι0 : ∀ ω, 0 ≤ newsRate i₁ i₂ T ω := fun ω => by
    unfold newsRate; split_ifs <;> assumption
  have hG := guidanceSDF_bm κ hr.le hT (stronglyMeasurable_newsRate i₁ i₂ T)
    (newsRate_finite i₁ i₂ T) hι0
  have hI := integrable_debt_bm κ hr.le hT hϖ
    ((stronglyMeasurable_newsRate i₁ i₂ T).mono (bmF.le T)).measurable hι0
  have hG' := guidanceSDF_bm κ' hr.le hT (ι := fun _ => r) stronglyMeasurable_const
    ⟨{r}, fun _ => Finset.mem_singleton_self r⟩ (fun _ => hr.le)
  have hI' := integrable_debt_bm κ' hr.le hT hϖ (ι := fun _ => r) measurable_const
    (fun _ => hr.le)
  have hj := random_jump_ito hB measurable_bmPath h𝓕 hT hϖ (by linarith)
    (fun ω => by linarith [hι0 ω]) (B0 := fun _ => 1) hG hI hG' hI' hP0 hP0' hval hval'
  have h0 : ∀ (c : ℝ) (ι : (ℕ → ℝ) → ℝ) ω, bmSDF c r T ι 0 ω = 1 := fun c ι ω => by
    simp [bmSDF, hT, bmW_zero]
  filter_upwards [hj] with ω hω
  rw [hω (by rw [h0]; exact one_ne_zero) (by rw [h0]; exact one_ne_zero)
    (by rw [pvSurplus_const hr]; positivity), condExp_bmF_zero, h0, div_one]
  simp_rw [exp_mul_bmSDF_T]
  exact integral_news κ i₁ i₂ (fun x => cfgJump r x ϖ T)

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561, with news at `T`: the valuation
equations have a solution.** If `0 ≤ p + κm ≤ 1` (for instance `κ = 0`), the constant price
levels `P_0 = (V(i₂) + (V(i₁) − V(i₂))(p + κm)) r/s̄` and `P_0' = V(r) r/s̄` are positive and
satisfy the valuation equations a.s. -/
theorem bm_random_valuation (κ κ' : ℝ) {r i₁ i₂ ϖ T sbar : ℝ} (hr : 0 < r) (hi₁ : 0 ≤ i₁)
    (hi₂ : 0 ≤ i₂) (hϖ : 0 < ϖ) (hT : 0 ≤ T) (hs : 0 < sbar)
    (hq0 : 0 ≤ newsProb T + κ * newsMean T) (hq1 : newsProb T + κ * newsMean T ≤ 1) :
    0 < (cfgValue r i₂ ϖ T + (cfgValue r i₁ ϖ T - cfgValue r i₂ ϖ T)
        * (newsProb T + κ * newsMean T)) * r / sbar
      ∧ (∀ᵐ ω ∂gaussSeq, 1 / ((cfgValue r i₂ ϖ T + (cfgValue r i₁ ϖ T - cfgValue r i₂ ϖ T)
          * (newsProb T + κ * newsMean T)) * r / sbar)
          * debtValue gaussSeq bmF (bmSDF κ r T (newsRate i₁ i₂ T)) ϖ ω
          = pvSurplus gaussSeq bmF r (fun _ _ => sbar) ω)
      ∧ 0 < cfgValue r r ϖ T * r / sbar
      ∧ (∀ᵐ ω ∂gaussSeq, 1 / (cfgValue r r ϖ T * r / sbar)
          * debtValue gaussSeq bmF (bmSDF κ' r T fun _ => r) ϖ ω
          = pvSurplus gaussSeq bmF r (fun _ _ => sbar) ω) := by
  have hV1 := cfgValue_pos (r := r) (i := i₁) (ϖ := ϖ) (T := T) hϖ (by linarith) (by linarith) hT
  have hV2 := cfgValue_pos (r := r) (i := i₂) (ϖ := ϖ) (T := T) hϖ (by linarith) (by linarith) hT
  set q := newsProb T + κ * newsMean T with hq
  have hVq : 0 < cfgValue r i₂ ϖ T + (cfgValue r i₁ ϖ T - cfgValue r i₂ ϖ T) * q := by
    have : cfgValue r i₂ ϖ T + (cfgValue r i₁ ϖ T - cfgValue r i₂ ϖ T) * q
        = (1 - q) * cfgValue r i₂ ϖ T + q * cfgValue r i₁ ϖ T := by ring
    rw [this]
    rcases hq0.lt_or_eq with h | h
    · nlinarith
    · rw [← h]; simpa using hV2
  have hP : 0 < (cfgValue r i₂ ϖ T + (cfgValue r i₁ ϖ T - cfgValue r i₂ ϖ T) * q) * r / sbar :=
    by positivity
  obtain ⟨-, hP', -, hval', -⟩ := bm_guidance_jump κ κ' (i := r) hr hr.le hϖ hT hs
  refine ⟨hP, ?_, hP', hval'⟩
  filter_upwards [bm_random_debtValue κ hr.le hi₁ hi₂ hϖ hT] with ω hω
  rw [hω, pvSurplus_const hr, ← hq]
  field_simp

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: **the jump is strictly convex in the
rate**: for `a ≠ b` with `a + ϖ, b + ϖ > 0`, `0 < p < 1`, `r + ϖ > 0`,
`J(pa + (1−p)b) < pJ(a) + (1−p)J(b)`. -/
theorem cfgJump_strictConvex {r ϖ a b p : ℝ} (T : ℝ) (hrv : 0 < r + ϖ) (ha : 0 < a + ϖ)
    (hb : 0 < b + ϖ) (hab : a ≠ b) (hp0 : 0 < p) (hp1 : p < 1) :
    cfgJump r (p * a + (1 - p) * b) ϖ T < p * cfgJump r a ϖ T + (1 - p) * cfgJump r b ϖ T := by
  have hC : 0 < p * a + (1 - p) * b + ϖ := by nlinarith
  have hE := Real.exp_pos (-(r + ϖ) * T)
  have key : p / (a + ϖ) + (1 - p) / (b + ϖ) - 1 / (p * a + (1 - p) * b + ϖ)
      = p * (1 - p) * (a - b) ^ 2 / ((a + ϖ) * (b + ϖ) * (p * a + (1 - p) * b + ϖ)) := by
    field_simp
    ring
  have hpos : 0 < p * (1 - p) * (a - b) ^ 2 / ((a + ϖ) * (b + ϖ) * (p * a + (1 - p) * b + ϖ)) := by
    have : 0 < (a - b) ^ 2 := by positivity
    have : 0 < 1 - p := by linarith
    positivity
  rw [← key] at hpos
  have e : p * cfgJump r a ϖ T + (1 - p) * cfgJump r b ϖ T - cfgJump r (p * a + (1 - p) * b) ϖ T
      = Real.exp (-(r + ϖ) * T) * (r + ϖ) * (p / (a + ϖ) + (1 - p) / (b + ϖ)
        - 1 / (p * a + (1 - p) * b + ϖ)) := by
    rw [cfgJump, cfgJump, cfgJump]
    field_simp
    ring
  have : 0 < Real.exp (-(r + ϖ) * T) * (r + ϖ) * (p / (a + ϖ) + (1 - p) / (b + ϖ)
      - 1 / (p * a + (1 - p) * b + ϖ)) := by positivity
  linarith

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the jump determines the rate,
`J(a) = J(b) → a = b` (`r + ϖ > 0`, `a + ϖ, b + ϖ > 0`). -/
theorem cfgJump_injective {r ϖ a b : ℝ} (T : ℝ) (hrv : 0 < r + ϖ) (ha : 0 < a + ϖ)
    (hb : 0 < b + ϖ) (h : cfgJump r a ϖ T = cfgJump r b ϖ T) : a = b := by
  rw [cfgJump, cfgJump] at h
  have h1 := mul_left_cancel₀ (Real.exp_pos (-(r + ϖ) * T)).ne' h
  have h2 : (r + ϖ) / (a + ϖ) = (r + ϖ) / (b + ϖ) := by linarith
  rw [div_eq_div_iff ha.ne' hb.ne'] at h2
  have := mul_left_cancel₀ hrv.ne' h2
  linarith

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the expected news rate,
`E ι = p i₁ + (1 − p) i₂`. -/
theorem integral_newsRate (i₁ i₂ T : ℝ) :
    ∫ ω, newsRate i₁ i₂ T ω ∂gaussSeq = newsProb T * i₁ + (1 - newsProb T) * i₂ := by
  have h := integral_news 0 (T := T) i₁ i₂ id
  simp only [zero_mul, add_zero, one_mul, id, zero_mul] at h
  rw [h]
  ring

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the physical expectation of the book's
jump over the news states, `E[J(ι)] = pJ(i₁) + (1 − p)J(i₂)`. -/
theorem integral_cfgJump_newsRate (r ϖ i₁ i₂ T : ℝ) :
    ∫ ω, cfgJump r (newsRate i₁ i₂ T ω) ϖ T ∂gaussSeq
      = newsProb T * cfgJump r i₁ ϖ T + (1 - newsProb T) * cfgJump r i₂ ϖ T := by
  have h := integral_news 0 (T := T) i₁ i₂ (fun x => cfgJump r x ϖ T)
  simp only [zero_mul, add_zero, one_mul] at h
  rw [h]
  ring

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the covariation correction.** In the
model economy, `E[(e^{rT}Λ_T/Λ_0) J(ι)] − E[e^{rT}Λ_T/Λ_0] E[J(ι)] = κm(J(i₁) − J(i₂))`: the
covariance of the forward weight with the book's jump (`Λ_0 = 1`, `E[e^{rT}Λ_T] = 1`). -/
theorem bm_cov_identity (κ r ϖ i₁ i₂ : ℝ) {T : ℝ} :
    ∫ ω, (1 + κ * bmW T ω) * cfgJump r (newsRate i₁ i₂ T ω) ϖ T ∂gaussSeq
      - (∫ ω, (1 + κ * bmW T ω) ∂gaussSeq) * ∫ ω, cfgJump r (newsRate i₁ i₂ T ω) ϖ T ∂gaussSeq
      = κ * newsMean T * (cfgJump r i₁ ϖ T - cfgJump r i₂ ϖ T) := by
  have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
  have h1 : ∫ ω, (1 + κ * bmW T ω) ∂gaussSeq = 1 := by
    rw [integral_add (integrable_const 1) ((integrable_bmW T).const_mul κ), integral_const_mul,
      show ∫ ω, bmW T ω ∂gaussSeq = 0 from isPreBrownianReal_bmPath.integral_eval _]
    simp
  rw [integral_news κ i₁ i₂ (fun x => cfgJump r x ϖ T), h1, integral_cfgJump_newsRate]
  ring

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: correction (i), Jensen.** Without
inflation risk (`κ = 0`), `T > 0`, `i₁ ≠ i₂` (`i₁, i₂ ≥ 0`, `r > 0`, `ϖ > 0`), every pair of
positive price levels satisfying the valuation equations has
`P_0/P_0' − 1 = E[J(ι)] > J(E ι)`: the book's formula evaluated at the expected rate path
understates the jump. -/
theorem bm_jensen (κ' : ℝ) {r i₁ i₂ ϖ T sbar : ℝ} (hr : 0 < r) (hi₁ : 0 ≤ i₁) (hi₂ : 0 ≤ i₂)
    (hne : i₁ ≠ i₂) (hϖ : 0 < ϖ) (hT : 0 < T) (hs : 0 < sbar) {P0 P0' : (ℕ → ℝ) → ℝ}
    (hP0 : ∀ ω, 0 < P0 ω) (hP0' : ∀ ω, 0 < P0' ω)
    (hval : ∀ᵐ ω ∂gaussSeq, 1 / P0 ω * debtValue gaussSeq bmF
      (bmSDF 0 r T (newsRate i₁ i₂ T)) ϖ ω = pvSurplus gaussSeq bmF r (fun _ _ => sbar) ω)
    (hval' : ∀ᵐ ω ∂gaussSeq, 1 / P0' ω * debtValue gaussSeq bmF
      (bmSDF κ' r T fun _ => r) ϖ ω = pvSurplus gaussSeq bmF r (fun _ _ => sbar) ω) :
    ∀ᵐ ω ∂gaussSeq, P0 ω / P0' ω - 1 = ∫ ω, cfgJump r (newsRate i₁ i₂ T ω) ϖ T ∂gaussSeq
      ∧ cfgJump r (∫ ω, newsRate i₁ i₂ T ω ∂gaussSeq) ϖ T < P0 ω / P0' ω - 1 := by
  filter_upwards [bm_random_jump 0 κ' hr hi₁ hi₂ hϖ hT.le hs hP0 hP0' hval hval'] with ω hω
  rw [hω, integral_cfgJump_newsRate, integral_newsRate]
  refine ⟨by ring, ?_⟩
  have h := cfgJump_strictConvex (r := r) (ϖ := ϖ) T (by linarith) (by linarith) (by linarith)
    hne (newsProb_pos hT) (newsProb_lt_one hT)
  have e : cfgJump r i₂ ϖ T + (cfgJump r i₁ ϖ T - cfgJump r i₂ ϖ T)
      * (newsProb T + 0 * newsMean T)
      = newsProb T * cfgJump r i₁ ϖ T + (1 - newsProb T) * cfgJump r i₂ ϖ T := by ring
  rw [e]
  exact h

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: correction (ii), covariation.** With
inflation risk `κ ≠ 0` and `i₁ ≠ i₂` (`T > 0`), every pair of positive price levels satisfying
the valuation equations has
`P_0/P_0' − 1 − E[J(ι)] = κm(J(i₁) − J(i₂)) ≠ 0`: averaging the book's formula over the news
states under the physical measure is wrong by the covariance `bm_cov_identity`. -/
theorem bm_covariance {κ : ℝ} (hκ : κ ≠ 0) (κ' : ℝ) {r i₁ i₂ ϖ T sbar : ℝ} (hr : 0 < r)
    (hi₁ : 0 ≤ i₁) (hi₂ : 0 ≤ i₂) (hne : i₁ ≠ i₂) (hϖ : 0 < ϖ) (hT : 0 < T) (hs : 0 < sbar)
    {P0 P0' : (ℕ → ℝ) → ℝ} (hP0 : ∀ ω, 0 < P0 ω) (hP0' : ∀ ω, 0 < P0' ω)
    (hval : ∀ᵐ ω ∂gaussSeq, 1 / P0 ω * debtValue gaussSeq bmF
      (bmSDF κ r T (newsRate i₁ i₂ T)) ϖ ω = pvSurplus gaussSeq bmF r (fun _ _ => sbar) ω)
    (hval' : ∀ᵐ ω ∂gaussSeq, 1 / P0' ω * debtValue gaussSeq bmF
      (bmSDF κ' r T fun _ => r) ϖ ω = pvSurplus gaussSeq bmF r (fun _ _ => sbar) ω) :
    ∀ᵐ ω ∂gaussSeq, P0 ω / P0' ω - 1 - ∫ ω, cfgJump r (newsRate i₁ i₂ T ω) ϖ T ∂gaussSeq
        = κ * newsMean T * (cfgJump r i₁ ϖ T - cfgJump r i₂ ϖ T)
      ∧ κ * newsMean T * (cfgJump r i₁ ϖ T - cfgJump r i₂ ϖ T) ≠ 0 := by
  filter_upwards [bm_random_jump κ κ' hr hi₁ hi₂ hϖ hT.le hs hP0 hP0' hval hval'] with ω hω
  rw [hω, integral_cfgJump_newsRate]
  refine ⟨by ring, ?_⟩
  have hJ : cfgJump r i₁ ϖ T - cfgJump r i₂ ϖ T ≠ 0 := fun h =>
    hne (cfgJump_injective (r := r) (ϖ := ϖ) T (by linarith) (by linarith) (by linarith)
      (sub_eq_zero.1 h))
  exact mul_ne_zero (mul_ne_zero hκ (newsMean_pos hT).ne') hJ

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561: the book's formula fails under
random future rates — headline.** On the constructed Brownian motion, for `T > 0`, `r > 0`,
`ϖ > 0`, `s̄ > 0` and news rates `i₁ ≠ i₂` (both `≥ 0`), there is an inflation-risk size
`κ ≠ 0` and positive price levels `P_0` (guidance with news, `bmSDF κ r T (newsRate i₁ i₂ T)`)
and `P_0'` (no guidance, `bmSDF 0 r T (fun _ => r)`) satisfying the stochastic valuation
equations, with `J(E ι) < E[J(ι)] < P_0/P_0' − 1`: neither the book's formula at the expected
rate nor its average over the news states gives the jump. -/
theorem bm_random_headline {r i₁ i₂ ϖ T sbar : ℝ} (hr : 0 < r) (hi₁ : 0 ≤ i₁) (hi₂ : 0 ≤ i₂)
    (hne : i₁ ≠ i₂) (hϖ : 0 < ϖ) (hT : 0 < T) (hs : 0 < sbar) :
    ∃ κ : ℝ, κ ≠ 0 ∧ ∃ P0 P0' : ℝ, 0 < P0 ∧ 0 < P0'
      ∧ (∀ᵐ ω ∂gaussSeq, 1 / P0 * debtValue gaussSeq bmF (bmSDF κ r T (newsRate i₁ i₂ T)) ϖ ω
          = pvSurplus gaussSeq bmF r (fun _ _ => sbar) ω)
      ∧ (∀ᵐ ω ∂gaussSeq, 1 / P0' * debtValue gaussSeq bmF (bmSDF 0 r T fun _ => r) ϖ ω
          = pvSurplus gaussSeq bmF r (fun _ _ => sbar) ω)
      ∧ cfgJump r (∫ ω, newsRate i₁ i₂ T ω ∂gaussSeq) ϖ T
          < ∫ ω, cfgJump r (newsRate i₁ i₂ T ω) ϖ T ∂gaussSeq
      ∧ ∫ ω, cfgJump r (newsRate i₁ i₂ T ω) ϖ T ∂gaussSeq < P0 / P0' - 1 := by
  have : IsProbabilityMeasure gaussSeq := isProbabilityMeasure_gaussSeq
  set p := newsProb T with hp
  set m := newsMean T with hm
  have hp0 := newsProb_pos hT
  have hp1 := newsProb_lt_one hT
  have hm0 := newsMean_pos hT
  rw [← hp] at hp0 hp1
  rw [← hm] at hm0
  set J1 := cfgJump r i₁ ϖ T with hJ1
  set J2 := cfgJump r i₂ ϖ T with hJ2
  have hJ : J1 ≠ J2 := fun h =>
    hne (cfgJump_injective (r := r) (ϖ := ϖ) T (by linarith) (by linarith) (by linarith) h)
  set κ : ℝ := if J2 < J1 then (1 - p) / (2 * m) else -(p / (2 * m)) with hκ
  have hκm : κ * m = if J2 < J1 then (1 - p) / 2 else -(p / 2) := by
    rw [hκ]
    split_ifs <;> field_simp
  have hκ0 : κ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hκm
    split_ifs at hκm <;> linarith
  have hq : 0 ≤ p + κ * m ∧ p + κ * m ≤ 1 := by
    rw [hκm]; split_ifs <;> constructor <;> linarith
  have hcov : 0 < κ * m * (J1 - J2) := by
    rw [hκm]
    split_ifs with h
    · exact mul_pos (by linarith) (by linarith)
    · have : J1 < J2 := lt_of_le_of_ne (not_lt.1 h) hJ
      nlinarith
  obtain ⟨hP, hval, hP', hval'⟩ := bm_random_valuation κ 0 hr hi₁ hi₂ hϖ hT.le hs hq.1 hq.2
  refine ⟨κ, hκ0, _, _, hP, hP', hval, hval', ?_, ?_⟩
  · rw [integral_cfgJump_newsRate, integral_newsRate]
    exact cfgJump_strictConvex T (by linarith) (by linarith) (by linarith) hne hp0 hp1
  · have hj := bm_random_jump κ 0 hr hi₁ hi₂ hϖ hT.le hs (P0 := fun _ => _) (P0' := fun _ => _)
      (fun _ => hP) (fun _ => hP') hval hval'
    obtain ⟨ω, hω⟩ := hj.exists
    rw [hω, integral_cfgJump_newsRate]
    nlinarith

end Cochrane.LongTermDebtDynamics.TidyR7GuidanceItoCex
