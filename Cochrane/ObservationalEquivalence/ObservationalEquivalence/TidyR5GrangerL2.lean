/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.TidyR5ShockL2
import ObservationalEquivalence.GrangerMeasure

/-!
# Debt Granger-causes an exogenous surplus: any filtration, square-integrable MDS shocks

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.3, p. 501 (footnote 1:
Granger causality) and pp. 501–502 ("If people learn from reading the news that surpluses will be
poor…"), and Online Appendix Chapter 2, introduction, p. 593.

`GrangerMeasure` proves the genuine Granger results for the news model `s_{t+1} = ε_t` in the
i.i.d. economy with an infinite past (`ExpectationsMeasureIIDZ.iidZSystem`), using independence.
Here the model lives in an arbitrary `MeasExpectationSystem` with shocks satisfying
`TidyR5ShockL2.ShockMDS2` (adapted, martingale differences, square-integrable, variance `σ²`; no
independence, no bound), and the value of debt is the `L²` valuation equation
`v_t = E_t ∑_j ρʲ s_{t+1+j}` (`TidyR5ShockL2.valueL2`).

## What extends and what fails

* `newsV_ae`: `v_t = ε_t` a.e.; `surplus_eq_value`: `s_{t+1} = v_t` a.e.
* `forecast_joint`: `E[s_{t+1} | s_{≤t}, v_{≤t}] = v_t` at every date.
* `forecast_own_succ`: `E[s_{t+1} | s_{≤t}] = 0` at every date `t ≥ 1` (martingale differences
  and the tower property replace independence).
* `debt_granger_causes_surplus`: debt Granger-causes surpluses;
  `surplus_not_granger_cause_debt`: surpluses do not Granger-cause debt; `granger_matches_var`:
  agreement with the VAR statements of `Granger`.
* **What fails**: at date 0 the claim `E[s_1 | s_0] = 0` is `E[ε_0 | ε_{−1}] = 0`, which concerns
  two pre-sample shocks; serially uncorrelated pre-sample shocks need not satisfy it.
  `Presample.forecast_own_zero_fails`: in the coin economy with re-indexed shocks
  `ε_{−1} = (ω_{−1} + ω_{−2})/√2`, `ε_0 = ε_{−1}² − 1`, all of `ShockMDS2` holds with `σ² = 1`, yet
  `E[s_1 | s_0] = s_1 ≠ 0`. `forecast_own_zero_of_presample` gives the date-0 statement under the
  extra pre-sample condition `E[ε_0 | ε_{−1}] = 0` (true in the i.i.d. economy,
  `iidZ_presample`). None of the causality statements is affected.
* Instances: every i.i.d. economy with finite variance (`iidZ_news_granger`), in particular normal
  shocks, which are unbounded (`gaussZ_news_granger`).
-/

namespace Cochrane.ObservationalEquivalence.TidyR5GrangerL2

open MeasureTheory ProbabilityTheory Filter
open Cochrane.ObservationalEquivalence.ExpectationsMeasure
open Cochrane.ObservationalEquivalence.ExpectationsMeasureIIDZ
open Cochrane.ObservationalEquivalence.SurplusRegression
open Cochrane.ObservationalEquivalence.SurplusRegressionMeasure
open Cochrane.ObservationalEquivalence.TidyR5ShockL2
open Cochrane.ObservationalEquivalence.Granger
open Cochrane.ObservationalEquivalence.GrangerMeasure (histSigma GrangerNonCausal measurable_hist
  histSigma_le)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {S : MeasExpectationSystem Ω} {ε : ℤ → Ω → ℝ}
  {σ2 ρ : ℝ}

/-! ### The news model -/

/-- Cochrane (2023), pp. 501–502: the news surplus `s_k = ε_{k−1}`. -/
def newsS (ε : ℤ → Ω → ℝ) (k : ℕ) : Ω → ℝ := ε ((k : ℤ) - 1)

/-- Cochrane (2023), pp. 501–502 and eq. (2.22), p. 602: the value of debt in the news model, the
`L²` valuation equation with the moving-average coefficients `newsCoeff` (`a_1 = 1`). -/
noncomputable def newsV (h : ShockMDS2 S ε σ2) (ρ : ℝ) (t : ℕ) : Ω → ℝ := valueL2 h ρ newsCoeff t

/-- Cochrane (2023), pp. 501–502: the news coefficients are square-summable. -/
theorem newsCoeff_sq : Summable fun k => newsCoeff k ^ 2 :=
  sq_summable (summable_of_finite newsCoeff_support)

/-- Cochrane (2023), pp. 501–502: the value-of-debt coefficients of the news surplus are
`b_0 = 1`, `b_m = 0` for `m ≥ 1`. -/
theorem bCoeff_news (ρ : ℝ) (m : ℕ) : bCoeff ρ newsCoeff m = if m = 0 then 1 else 0 := by
  simp only [bCoeff, bInf]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [tsum_eq_single 0 fun j hj => by simp [newsCoeff, hj]]
    simp [newsCoeff]
  · have : ∀ j, ρ ^ j * newsCoeff (m + j + 1) = 0 := fun j => by
      simp only [newsCoeff, (show m + j + 1 ≠ 1 by omega), ↓reduceIte, mul_zero]
    have hm0 : m ≠ 0 := by omega
    simp only [this, tsum_zero, hm0, ↓reduceIte]

/-- Cochrane (2023), pp. 501–502 and Online Appendix p. 593 (debt reveals the news, any
filtration): `v_t = ε_t` a.e. -/
theorem newsV_ae (h : ShockMDS2 S ε σ2) (hρ : |ρ| < 1) (t : ℕ) :
    newsV h ρ t =ᵐ[S.μ] ε t := by
  have h1 := valueL2_ae h hρ newsCoeff_sq t
  have h2 : maL2 h (bCoeff ρ newsCoeff) t = shockL2 h t := by
    rw [maL2, tsum_eq_single 0 fun m hm => by simp [bCoeff_news, hm]]
    simp [bCoeff_news]
  rw [h2] at h1
  exact h1.trans (h.memLp _).coeFn_toLp

/-- Cochrane (2023), pp. 501–502: in the news model debt forecasts the surplus perfectly,
`s_{t+1} = v_t` a.e. -/
theorem surplus_eq_value (h : ShockMDS2 S ε σ2) (hρ : |ρ| < 1) (t : ℕ) :
    newsS ε (t + 1) =ᵐ[S.μ] newsV h ρ t := by
  have e : newsS ε (t + 1) = ε t := by simp [newsS]
  rw [e]
  exact (newsV_ae h hρ t).symm

/-! ### Histories -/

/-- Cochrane (2023), pp. 501–502: the value of debt is known at `t`. -/
theorem stronglyMeasurable_newsV (h : ShockMDS2 S ε σ2) (ρ : ℝ) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (newsV h ρ t) :=
  S.stronglyMeasurable_E t _

/-- Cochrane (2023), pp. 501–502: the debt history is date-`t` information. -/
theorem histV_le (h : ShockMDS2 S ε σ2) (ρ : ℝ) (t : ℕ) :
    histSigma (newsV h ρ) t ≤ S.𝓕 t :=
  histSigma_le fun k hk => ((stronglyMeasurable_newsV h ρ k).mono (S.𝓕.mono hk)).measurable

/-- Cochrane (2023), pp. 501–502: the surplus history up to `t + 1` is date-`t` information
(`s_k = ε_{k−1}` is known at `k − 1`). -/
theorem histS_le (h : ShockMDS2 S ε σ2) (t : ℕ) : histSigma (newsS ε) (t + 1) ≤ S.𝓕 t :=
  histSigma_le fun k hk => (h.adapted _ t (by omega)).measurable

/-- Cochrane (2023), pp. 501–502: the surplus history up to `t` is date-`t` information. -/
theorem histS_le' (h : ShockMDS2 S ε σ2) (t : ℕ) : histSigma (newsS ε) t ≤ S.𝓕 t :=
  histSigma_le fun k hk => (h.adapted _ t (by omega)).measurable

/-- Cochrane (2023), p. 501 (tool): a shock is unforecastable from the joint history of two
processes observed by the previous date, `E[ε_{t+1} | x_{≤n}, y_{≤n}] = 0` when
`σ(x_{≤n}, y_{≤n}) ⊆ 𝓕_t`. -/
theorem condExp_shock_hist (h : ShockMDS2 S ε σ2) {x y : ℕ → Ω → ℝ} {t n : ℕ}
    (hm : histSigma x n ⊔ histSigma y n ≤ S.𝓕 t) :
    S.μ[ε ((t : ℤ) + 1) | histSigma x n ⊔ histSigma y n] =ᵐ[S.μ] 0 := by
  have h0 : S.μ[S.μ[ε ((t : ℤ) + 1) | S.𝓕 t] | histSigma x n ⊔ histSigma y n] =ᵐ[S.μ]
      S.μ[(0 : Ω → ℝ) | histSigma x n ⊔ histSigma y n] :=
    condExp_congr_ae (h.mds t)
  filter_upwards [(condExp_condExp_of_le (μ := S.μ) (f := ε ((t : ℤ) + 1)) hm
    (S.𝓕.le t)).symm, h0] with ω h1 h2
  rw [h1, h2, condExp_zero]

/-! ### Forecasts and Granger causality -/

/-- Cochrane (2023), pp. 501–502 (debt forecasts surpluses, any filtration): adding the history of
debt, the forecast of next period's surplus is the value of debt,
`E[s_{t+1} | s_{≤t}, v_{≤t}] = v_t` a.e. -/
theorem forecast_joint (h : ShockMDS2 S ε σ2) (hρ : |ρ| < 1) (t : ℕ) :
    S.μ[newsS ε (t + 1) | histSigma (newsS ε) t ⊔ histSigma (newsV h ρ) t]
      =ᵐ[S.μ] newsV h ρ t := by
  have hle : histSigma (newsS ε) t ⊔ histSigma (newsV h ρ) t ≤ mΩ :=
    sup_le ((histS_le' h t).trans (S.𝓕.le t)) ((histV_le h ρ t).trans (S.𝓕.le t))
  have hvm : StronglyMeasurable[histSigma (newsS ε) t ⊔ histSigma (newsV h ρ) t]
      (newsV h ρ t) :=
    ((measurable_hist (x := newsV h ρ) (t := t) le_rfl).mono
      (le_sup_right : histSigma (newsV h ρ) t ≤ histSigma (newsS ε) t ⊔ histSigma (newsV h ρ) t)
      le_rfl).stronglyMeasurable
  have hvi : Integrable (newsV h ρ t) S.μ := S.integrable_E t _
  filter_upwards [condExp_congr_ae (m := histSigma (newsS ε) t ⊔ histSigma (newsV h ρ) t)
    (surplus_eq_value h hρ t)] with ω h1
  rw [h1, condExp_of_stronglyMeasurable hle hvm hvi]

/-- Cochrane (2023), pp. 501–502 ("past surpluses do not forecast", any filtration, from date 1
on): `E[s_{t+2} | s_{≤t+1}] = 0` a.e. — to an econometrician who sees only surpluses they are
unforecastable. -/
theorem forecast_own_succ (h : ShockMDS2 S ε σ2) (t : ℕ) :
    S.μ[newsS ε (t + 2) | histSigma (newsS ε) (t + 1)] =ᵐ[S.μ] 0 := by
  have e : newsS ε (t + 2) = ε ((t : ℤ) + 1) := by
    simp only [newsS]; congr 1; push_cast; ring
  rw [e, ← sup_idem (histSigma (newsS ε) (t + 1))]
  exact condExp_shock_hist h (by rw [sup_idem]; exact histS_le h t)

/-- Cochrane (2023), pp. 501–502 (date 0): with the pre-sample condition `E[ε_0 | s_0] = 0`
(`s_0 = ε_{−1}`), past surpluses do not forecast at date 0 either. -/
theorem forecast_own_zero_of_presample
    (hpre : S.μ[ε 0 | histSigma (newsS ε) 0] =ᵐ[S.μ] 0) :
    S.μ[newsS ε 1 | histSigma (newsS ε) 0] =ᵐ[S.μ] 0 := by
  have e : newsS ε 1 = ε 0 := by simp [newsS]
  rw [e]
  exact hpre

/-- Cochrane (2023), p. 501 (tool): a shock with positive variance is not a.e. zero. -/
theorem shock_not_ae_zero (h : ShockMDS2 S ε σ2) (hσ : 0 < σ2) (k : ℤ) : ¬ ε k =ᵐ[S.μ] 0 := by
  intro h0
  have hi : ∫ ω, ε k ω ^ 2 ∂S.μ = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [h0] with ω h1
    simp only [Pi.zero_apply] at h1
    simp [h1]
  rw [h.var k] at hi
  linarith

/-- Cochrane (2023), pp. 501–502 and Online Appendix p. 593 (**debt Granger-causes surpluses**,
any filtration, square-integrable shocks): although surpluses are exogenous, the history of
debt changes the forecast of the surplus (already at date 1). -/
theorem debt_granger_causes_surplus (h : ShockMDS2 S ε σ2) (hσ : 0 < σ2) (hρ : |ρ| < 1) :
    ¬ GrangerNonCausal S.μ (newsV h ρ) (newsS ε) := by
  intro hnc
  apply shock_not_ae_zero h hσ ((0 : ℕ) + 1 : ℕ)
  have h1 := ((forecast_joint h hρ 1).symm.trans (hnc 1)).trans (forecast_own_succ h 0)
  have h2 := (newsV_ae h hρ 1).symm.trans h1
  simpa using h2

/-- Cochrane (2023), pp. 501–502 (any filtration): surpluses do not Granger-cause debt — the
forecast of `v_{t+1}` is zero with or without the surplus history. -/
theorem surplus_not_granger_cause_debt (h : ShockMDS2 S ε σ2) (hρ : |ρ| < 1) :
    GrangerNonCausal S.μ (newsS ε) (newsV h ρ) := by
  intro t
  have hJ : histSigma (newsV h ρ) t ⊔ histSigma (newsS ε) t ≤ S.𝓕 t :=
    sup_le (histV_le h ρ t) (histS_le' h t)
  have hv : newsV h ρ (t + 1) =ᵐ[S.μ] ε ((t : ℤ) + 1) := by
    have := newsV_ae h hρ (t + 1)
    simpa using this
  have h1 := (condExp_congr_ae (m := histSigma (newsV h ρ) t ⊔ histSigma (newsS ε) t) hv).trans
    (condExp_shock_hist h hJ)
  have hO : histSigma (newsV h ρ) t ⊔ histSigma (newsV h ρ) t ≤ S.𝓕 t := by
    rw [sup_idem]; exact histV_le h ρ t
  have h2 := (condExp_congr_ae (m := histSigma (newsV h ρ) t ⊔ histSigma (newsV h ρ) t) hv).trans
    (condExp_shock_hist h hO)
  rw [sup_idem] at h2
  exact h1.trans h2.symm

/-- Cochrane (2023), p. 501, footnote 1 and pp. 501–502 (**link** with `Granger`, any filtration):
the genuine Granger statements agree with the VAR statements of the abstract news model. -/
theorem granger_matches_var (h : ShockMDS2 S ε σ2) (hσ : 0 < σ2) (hρ : |ρ| < 1) :
    (¬ GrangerNonCausal S.μ (newsV h ρ) (newsS ε) ∧ ¬ OneStepNonCausal newsA 1 0 ∧
      ¬ IRFNonCausal newsA 1 0) ∧
    (GrangerNonCausal S.μ (newsS ε) (newsV h ρ) ∧ IRFNonCausal newsA 0 1) :=
  ⟨⟨debt_granger_causes_surplus h hσ hρ, news_debt_causes_surplus.1,
      news_debt_causes_surplus.2⟩,
    surplus_not_granger_cause_debt h hρ, news_surplus_not_cause_debt⟩

/-! ### Instances -/

/-- Cochrane (2023), pp. 501–502: in the i.i.d. economy the pre-sample condition holds,
`E[ε_0 | s_0] = 0` (independence). -/
theorem iidZ_presample {ν : ProbabilityMeasure ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) :
    (iidZSystem ν).μ[shockZ 0 | histSigma (newsS shockZ) 0] =ᵐ[(iidZSystem ν).μ] 0 := by
  have hI : histSigma (newsS shockZ) 0 ⊔ histSigma (newsS shockZ) 0 ≤ sigmaOf {(-1 : ℤ)} := by
    rw [sup_idem]
    exact histSigma_le fun k hk => by
      obtain rfl : k = 0 := by omega
      exact measurable_shockZ_sigmaOf (by simp)
  have := GrangerMeasure.condExp_shockZ_hist (ν := ν) hmean hI (k := 0) (by simp)
  rwa [sup_idem] at this

/-- Cochrane (2023), pp. 501–502: in every i.i.d. economy with mean-zero shocks of finite
positive variance — bounded or not — debt reveals the news, debt Granger-causes surpluses,
surpluses do not Granger-cause debt, and past surpluses do not forecast at any date. -/
theorem iidZ_news_granger {ν : ProbabilityMeasure ℝ} {σ2' : ℝ} (hν : MemLp id 2 (ν : Measure ℝ))
    (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2')
    (hσ : 0 < σ2') (hρ : |ρ| < 1) :
    (∀ t, newsS shockZ (t + 1) =ᵐ[(iidZSystem ν).μ] newsV (iidZ_shockMDS2 hν hmean hvar) ρ t) ∧
    ¬ GrangerNonCausal (iidZSystem ν).μ (newsV (iidZ_shockMDS2 hν hmean hvar) ρ) (newsS shockZ) ∧
    GrangerNonCausal (iidZSystem ν).μ (newsS shockZ) (newsV (iidZ_shockMDS2 hν hmean hvar) ρ) ∧
    ∀ t, (iidZSystem ν).μ[newsS shockZ (t + 1) | histSigma (newsS shockZ) t]
      =ᵐ[(iidZSystem ν).μ] 0 := by
  refine ⟨surplus_eq_value _ hρ, debt_granger_causes_surplus _ hσ hρ,
    surplus_not_granger_cause_debt _ hρ, fun t => ?_⟩
  rcases t with _ | t
  · exact forecast_own_zero_of_presample (iidZ_presample hmean)
  · exact forecast_own_succ (iidZ_shockMDS2 hν hmean hvar) t

/-- Cochrane (2023), pp. 501–502 (unbounded shocks): with i.i.d. normal shocks `N(0, v)`, `v > 0`
— not covered by `GrangerMeasure`, which needs bounded support — debt Granger-causes surpluses
and surpluses do not Granger-cause debt. -/
theorem gaussZ_news_granger {v : NNReal} (hv : v ≠ 0) (hρ : |ρ| < 1) :
    ¬ GrangerNonCausal (iidZSystem (gauss v)).μ (newsV (gaussZ_shockMDS2 v) ρ) (newsS shockZ) ∧
    GrangerNonCausal (iidZSystem (gauss v)).μ (newsS shockZ) (newsV (gaussZ_shockMDS2 v) ρ) :=
  ⟨debt_granger_causes_surplus _ (lt_of_le_of_ne v.2 fun e => hv (NNReal.coe_eq_zero.1 e.symm))
      hρ,
    surplus_not_granger_cause_debt _ hρ⟩

/-! ### Date 0: a counterexample with uncorrelated pre-sample shocks -/

namespace Presample

open ExpectationsMeasureIID (coin coin_mean coin_var coin_bdd coinMeasure)

/-- Cochrane (2023), p. 501 (the counterexample economy): the coin economy with an infinite past,
`ω_k = ±1` i.i.d. -/
noncomputable abbrev coinZ : MeasExpectationSystem (ℤ → ℝ) := iidZSystem coin

/-- Cochrane (2023), p. 501 (tool): a fair coin takes the values `±1`, so `x² = 1` a.e. -/
theorem coin_sq : ∀ᵐ x ∂(coin : Measure ℝ), x ^ 2 = 1 := by
  change ∀ᵐ x ∂coinMeasure, x ^ 2 = 1
  rw [ae_iff]
  have hs : MeasurableSet {x : ℝ | ¬ x ^ 2 = 1} :=
    (measurableSet_eq_fun (measurable_id.pow_const 2) measurable_const).compl
  simp only [coinMeasure, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hs,
    Set.indicator, Set.mem_ofPred_eq]
  norm_num

/-- Cochrane (2023), p. 501 (tool): in the coin economy every coordinate is `±1`, a.e. -/
theorem coinZ_sq : ∀ᵐ ω ∂coinZ.μ, ∀ j, ω j ^ 2 = 1 :=
  ae_all_iff.2 fun j =>
    (measurePreserving_eval_infinitePi (fun _ => (coin : Measure ℝ)) j).quasiMeasurePreserving.ae
      coin_sq

/-- Cochrane (2023), p. 501 (tool): an a.e. bounded measurable function is integrable in the coin
economy. -/
theorem integrable_of_bdd {f : (ℤ → ℝ) → ℝ} (hf : Measurable f) {M : ℝ}
    (hb : ∀ᵐ ω ∂coinZ.μ, |f ω| ≤ M) : Integrable f coinZ.μ :=
  Integrable.of_bound hf.aestronglyMeasurable M (hb.mono fun ω h => by rwa [Real.norm_eq_abs])

/-- Cochrane (2023), p. 501 (tool): in the coin economy `E[ω_j] = 0`. -/
theorem integral_coord (j : ℤ) : ∫ ω, ω j ∂coinZ.μ = 0 := by
  have := integral_shockZ_fun coin j (f := fun x => x) measurable_id
  rw [coin_mean] at this
  exact this

/-- Cochrane (2023), p. 501 (tool): in the coin economy `E[ω_j ω_k] = 1{j = k}`. -/
theorem integral_coord_mul (j k : ℤ) :
    ∫ ω, ω j * ω k ∂coinZ.μ = if j = k then 1 else 0 :=
  integral_shockZ_mul coin_mean coin_var coin_bdd j k

/-- Cochrane (2023), p. 501 (tool): a coordinate outside a set of dates is orthogonal to every
bounded function of the coordinates in that set. -/
theorem integral_coord_mul_sigmaOf {I : Set ℤ} {c : ℤ} (hc : c ∉ I) {g : (ℤ → ℝ) → ℝ}
    (hg : Measurable[sigmaOf I] g) {M : ℝ} (hb : ∀ᵐ ω ∂coinZ.μ, |g ω| ≤ M) :
    ∫ ω, ω c * g ω ∂coinZ.μ = 0 := by
  have hgm : Measurable g := hg.mono (sigmaOf_le I) le_rfl
  have hcm : Measurable (shockZ c) := measurable_shockZ_pi c
  have hint : Integrable (shockZ c * g) coinZ.μ := by
    refine integrable_of_bdd (hcm.mul hgm) (M := M) ?_
    filter_upwards [hb, shockZ_ae_bdd coin coin_bdd c] with ω h1 h2
    rw [Pi.mul_apply, abs_mul]
    have := abs_nonneg (g ω)
    nlinarith [abs_nonneg (shockZ c ω)]
  have hci : Integrable (shockZ c) coinZ.μ :=
    integrable_of_bdd hcm (shockZ_ae_bdd coin coin_bdd c)
  have h1 := condExp_mul_of_stronglyMeasurable_right (μ := coinZ.μ) hg.stronglyMeasurable hint hci
  have h2 := condExp_shockZ_sigmaOf (ν := coin) coin_mean hc
  calc ∫ ω, ω c * g ω ∂coinZ.μ = ∫ ω, (shockZ c * g) ω ∂coinZ.μ := rfl
    _ = ∫ ω, coinZ.μ[shockZ c * g | sigmaOf I] ω ∂coinZ.μ := (integral_condExp (sigmaOf_le I)).symm
    _ = 0 := by
      rw [integral_congr_ae (h1.trans (h2.mul (EventuallyEq.refl _ g)))]
      simp

/-- Cochrane (2023), p. 501 (the counterexample): the pre-sample shock
`ε_{−1} = (ω_{−1} + ω_{−2})/√2`. -/
noncomputable def epsM1 (ω : ℤ → ℝ) : ℝ := (ω (-1) + ω (-2)) / Real.sqrt 2

/-- Cochrane (2023), p. 501 (the counterexample): re-indexed shocks — `ε_k = ω_k` for `k ≥ 1`,
`ε_0 = ε_{−1}² − 1`, `ε_{−1} = (ω_{−1} + ω_{−2})/√2`, `ε_k = ω_{k−1}` for `k ≤ −2`. -/
noncomputable def epsC (k : ℤ) (ω : ℤ → ℝ) : ℝ :=
  if 1 ≤ k then ω k else if k = 0 then epsM1 ω ^ 2 - 1 else if k = -1 then epsM1 ω else ω (k - 1)

/-- Cochrane (2023), p. 501 (the counterexample): in-sample shocks are the coordinates. -/
theorem epsC_pos {k : ℤ} (hk : 1 ≤ k) : epsC k = shockZ k := by
  funext ω; simp [epsC, hk, shockZ]

/-- Cochrane (2023), p. 501 (the counterexample): `ε_0 = ε_{−1}² − 1`. -/
theorem epsC_zero : epsC 0 = fun ω => epsM1 ω ^ 2 - 1 := by
  funext ω; simp [epsC]

/-- Cochrane (2023), p. 501 (the counterexample): `ε_{−1} = (ω_{−1} + ω_{−2})/√2`. -/
theorem epsC_neg_one : epsC (-1) = epsM1 := by
  funext ω; simp [epsC]

/-- Cochrane (2023), p. 501 (the counterexample): `ε_k = ω_{k−1}` for `k ≤ −2`. -/
theorem epsC_le {k : ℤ} (hk : k ≤ -2) : epsC k = shockZ (k - 1) := by
  funext ω
  simp [epsC, shockZ, show ¬ 1 ≤ k by omega, show k ≠ 0 by omega, show k ≠ -1 by omega]

/-- Cochrane (2023), p. 501 (the counterexample): `ε_{−1}` is a function of `ω_{−1}, ω_{−2}`. -/
theorem measurable_epsM1 {I : Set ℤ} (h1 : (-1 : ℤ) ∈ I) (h2 : (-2 : ℤ) ∈ I) :
    Measurable[sigmaOf I] epsM1 :=
  ((measurable_shockZ_sigmaOf h1).add (measurable_shockZ_sigmaOf h2)).div_const _

/-- Cochrane (2023), p. 501 (the counterexample): on the event that every coordinate is `±1`,
`ε_{−1}² = 1 + ω_{−1}ω_{−2}`. -/
theorem epsM1_sq {ω : ℤ → ℝ} (hω : ∀ j, ω j ^ 2 = 1) : epsM1 ω ^ 2 = 1 + ω (-1) * ω (-2) := by
  have ha := hω (-1)
  have hb := hω (-2)
  rw [epsM1, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  linear_combination (ha + hb) / 2

/-- Cochrane (2023), p. 501 (the counterexample): `|ε_{−1}| ≤ 2` a.e. -/
theorem abs_epsM1 : ∀ᵐ ω ∂coinZ.μ, |epsM1 ω| ≤ 2 := by
  filter_upwards [coinZ_sq] with ω hω
  have e := epsM1_sq hω
  have ha := hω (-1)
  have hb := hω (-2)
  have hab : ω (-1) * ω (-2) ≤ 1 := by nlinarith [sq_nonneg (ω (-1) - ω (-2))]
  exact abs_le.2 ⟨by nlinarith [sq_nonneg (epsM1 ω + 2)], by nlinarith [sq_nonneg (epsM1 ω - 2)]⟩

/-- Cochrane (2023), p. 501 (the counterexample): `ε_0 = ω_{−1}ω_{−2}` a.e. -/
theorem epsC_zero_ae : epsC 0 =ᵐ[coinZ.μ] fun ω => ω (-1) * ω (-2) := by
  filter_upwards [coinZ_sq] with ω hω
  rw [epsC_zero]
  simp only
  rw [epsM1_sq hω]
  ring

/-- Cochrane (2023), p. 501 (the counterexample): every shock is bounded by 2, a.e. -/
theorem abs_epsC (k : ℤ) : ∀ᵐ ω ∂coinZ.μ, |epsC k ω| ≤ 2 := by
  filter_upwards [coinZ_sq, abs_epsM1] with ω hω hm
  have hc : ∀ j, |ω j| ≤ 2 := fun j => by
    have := hω j
    exact abs_le.2 ⟨by nlinarith [sq_nonneg (ω j + 1)], by nlinarith [sq_nonneg (ω j - 1)]⟩
  rcases (show 1 ≤ k ∨ k = 0 ∨ k = -1 ∨ k ≤ -2 by omega) with hk | rfl | rfl | hk
  · rw [epsC_pos hk]; exact hc k
  · rw [epsC_zero]
    have e := epsM1_sq hω
    have ha := hω (-1)
    have hb := hω (-2)
    simp only
    rw [e, add_sub_cancel_left, abs_mul]
    have h1 : |ω (-1)| = 1 := by
      have := sq_abs (ω (-1)); nlinarith [abs_nonneg (ω (-1))]
    have h2 : |ω (-2)| = 1 := by
      have := sq_abs (ω (-2)); nlinarith [abs_nonneg (ω (-2))]
    rw [h1, h2]; norm_num
  · rw [epsC_neg_one]; exact hm
  · rw [epsC_le hk]; exact hc _

/-- Cochrane (2023), p. 501 (the counterexample): every shock is measurable. -/
theorem measurable_epsC (k : ℤ) : Measurable (epsC k) := by
  rcases (show 1 ≤ k ∨ k = 0 ∨ k = -1 ∨ k ≤ -2 by omega) with hk | rfl | rfl | hk
  · rw [epsC_pos hk]; exact measurable_shockZ_pi k
  · rw [epsC_zero]
    exact ((measurable_epsM1 (I := Set.univ) trivial trivial).mono (sigmaOf_le _) le_rfl).pow_const
      2 |>.sub_const 1
  · rw [epsC_neg_one]
    exact (measurable_epsM1 (I := Set.univ) trivial trivial).mono (sigmaOf_le _) le_rfl
  · rw [epsC_le hk]; exact measurable_shockZ_pi _

/-- Cochrane (2023), p. 501 (the counterexample): `E[ε_{−1}] = 0`. -/
theorem integral_epsM1 : ∫ ω, epsM1 ω ∂coinZ.μ = 0 := by
  have hi : ∀ j, Integrable (fun ω : ℤ → ℝ => ω j) coinZ.μ := fun j =>
    integrable_of_bdd (measurable_pi_apply j) (shockZ_ae_bdd coin coin_bdd j)
  simp only [epsM1]
  rw [integral_div, integral_add (hi _) (hi _), integral_coord, integral_coord]
  simp

/-- Cochrane (2023), p. 501 (the counterexample): the re-indexed shocks satisfy all of
`ShockMDS` (bounded) with `σ² = 1`: adapted, martingale differences, bounded, unit variance, and
mean-zero, uncorrelated pre-sample shocks. -/
theorem epsC_shockMDS : ShockMDS coinZ epsC 1 := by
  have hint : ∀ k, Integrable (epsC k) coinZ.μ := fun k =>
    integrable_of_bdd (measurable_epsC k) (abs_epsC k)
  have hab : ∫ ω, ω (-1) * ω (-2) ∂coinZ.μ = 0 := by
    rw [integral_coord_mul]; norm_num
  refine ⟨fun k t hkt => ?_, fun t => ?_, ⟨2, abs_epsC⟩, fun k => ?_, fun k hk => ?_,
    fun j k hj hk hjk => ?_⟩
  · have hm1 : (-1 : ℤ) ∈ Set.Iic (t : ℤ) := Set.mem_Iic.2 (by omega)
    have hm2 : (-2 : ℤ) ∈ Set.Iic (t : ℤ) := Set.mem_Iic.2 (by omega)
    rcases (show 1 ≤ k ∨ k = 0 ∨ k = -1 ∨ k ≤ -2 by omega) with hk | rfl | rfl | hk
    · rw [epsC_pos hk]; exact (measurable_shockZ coin hkt).stronglyMeasurable
    · rw [epsC_zero]
      exact (((measurable_epsM1 hm1 hm2).pow_const 2).sub_const 1).stronglyMeasurable
    · rw [epsC_neg_one]; exact (measurable_epsM1 hm1 hm2).stronglyMeasurable
    · rw [epsC_le hk]; exact (measurable_shockZ coin (by omega)).stronglyMeasurable
  · rw [epsC_pos (by omega)]
    exact E_shockZ_zero coin_mean (by omega)
  · rcases (show 1 ≤ k ∨ k = 0 ∨ k = -1 ∨ k ≤ -2 by omega) with hk | rfl | rfl | hk
    · rw [epsC_pos hk]
      have := integral_shockZ_fun coin k (f := fun x => x ^ 2) (measurable_id.pow_const 2)
      rw [coin_var] at this; exact this
    · have : (fun ω => epsC 0 ω ^ 2) =ᵐ[coinZ.μ] fun _ => 1 := by
        filter_upwards [epsC_zero_ae, coinZ_sq] with ω h1 hω
        rw [h1, mul_pow, hω, hω, one_mul]
      rw [integral_congr_ae this]; simp
    · rw [epsC_neg_one]
      have : (fun ω => epsM1 ω ^ 2) =ᵐ[coinZ.μ] fun ω => 1 + ω (-1) * ω (-2) := by
        filter_upwards [coinZ_sq] with ω hω
        exact epsM1_sq hω
      rw [integral_congr_ae this, integral_add (f := fun _ => (1 : ℝ))
        (g := fun ω : ℤ → ℝ => ω (-1) * ω (-2)) (integrable_const 1)
        (integrable_of_bdd (f := fun ω : ℤ → ℝ => ω (-1) * ω (-2))
          ((measurable_pi_apply _).mul (measurable_pi_apply _)) (M := 1) ?_), hab]
      · simp
      · filter_upwards [shockZ_ae_bdd coin coin_bdd (-1), shockZ_ae_bdd coin coin_bdd (-2)] with
          ω h1 h2
        rw [abs_mul]
        exact (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one).trans (by norm_num)
    · rw [epsC_le hk]
      have := integral_shockZ_fun coin (k - 1) (f := fun x => x ^ 2) (measurable_id.pow_const 2)
      rw [coin_var] at this; exact this
  · rcases (show k = 0 ∨ k = -1 ∨ k ≤ -2 by omega) with rfl | rfl | hk
    · rw [integral_congr_ae epsC_zero_ae, hab]
    · rw [epsC_neg_one]; exact integral_epsM1
    · rw [epsC_le hk]; exact integral_coord _
  · have hpair : ∀ j k : ℤ, j ≤ -2 → (k = 0 ∨ k = -1) →
        ∫ ω, epsC j ω * epsC k ω ∂coinZ.μ = 0 := by
      intro j k hj hk
      rw [epsC_le hj]
      have hmeas : Measurable[sigmaOf {(-1 : ℤ), -2}] (epsC k) := by
        have hm1 : (-1 : ℤ) ∈ ({(-1 : ℤ), -2} : Set ℤ) := by simp
        have hm2 : (-2 : ℤ) ∈ ({(-1 : ℤ), -2} : Set ℤ) := by simp
        rcases hk with rfl | rfl
        · rw [epsC_zero]; exact ((measurable_epsM1 hm1 hm2).pow_const 2).sub_const 1
        · rw [epsC_neg_one]; exact measurable_epsM1 hm1 hm2
      exact integral_coord_mul_sigmaOf (c := j - 1) (by simp; omega) hmeas (abs_epsC k)
    have hcross : ∫ ω, epsC (-1) ω * epsC 0 ω ∂coinZ.μ = 0 := by
      have : (fun ω => epsC (-1) ω * epsC 0 ω) =ᵐ[coinZ.μ] epsM1 := by
        filter_upwards [coinZ_sq] with ω hω
        rw [epsC_neg_one, epsC_zero]
        simp only
        rw [epsM1_sq hω, add_sub_cancel_left]
        have ha := hω (-1)
        have hb := hω (-2)
        simp only [epsM1]
        field_simp
        linear_combination ω (-2) * ha + ω (-1) * hb
      rw [integral_congr_ae this]; exact integral_epsM1
    have hcomm : ∀ j k : ℤ, ∫ ω, epsC j ω * epsC k ω ∂coinZ.μ =
        ∫ ω, epsC k ω * epsC j ω ∂coinZ.μ := fun j k =>
      integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
    rcases (show j = 0 ∨ j = -1 ∨ j ≤ -2 by omega) with rfl | rfl | hj' <;>
      rcases (show k = 0 ∨ k = -1 ∨ k ≤ -2 by omega) with rfl | rfl | hk'
    · exact absurd rfl hjk
    · rw [hcomm]; exact hcross
    · rw [hcomm]; exact hpair k 0 hk' (Or.inl rfl)
    · exact hcross
    · exact absurd rfl hjk
    · rw [hcomm]; exact hpair k (-1) hk' (Or.inr rfl)
    · exact hpair j 0 hj' (Or.inl rfl)
    · exact hpair j (-1) hj' (Or.inr rfl)
    · rw [epsC_le hj', epsC_le hk', integral_shockZ_mul coin_mean coin_var coin_bdd]
      simp only [ite_eq_right_iff]
      intro h; omega

/-- Cochrane (2023), pp. 501–502 (**what fails at date 0**): in the re-indexed coin economy all
of `ShockMDS2` holds (`σ² = 1`), yet `E[s_1 | s_0] = s_1 ≠ 0`: the date-0 surplus `s_0 = ε_{−1}`
forecasts `s_1 = ε_0 = ε_{−1}² − 1` perfectly, although the two shocks are uncorrelated. The
date-0 claim "past surpluses do not forecast" needs `E[ε_0 | ε_{−1}] = 0`, which serial
uncorrelatedness does not give. -/
theorem forecast_own_zero_fails :
    Nonempty (ShockMDS2 coinZ epsC 1) ∧
      ¬ coinZ.μ[newsS epsC 1 | histSigma (newsS epsC) 0] =ᵐ[coinZ.μ] 0 := by
  have h := TidyR5ShockL2.ShockMDS.toShockMDS2 epsC_shockMDS
  refine ⟨⟨h⟩, fun h0 => ?_⟩
  have e1 : newsS epsC 1 = fun ω => newsS epsC 0 ω ^ 2 - 1 := by
    funext ω
    simp only [newsS, Nat.cast_one, sub_self, Nat.cast_zero, zero_sub]
    rw [epsC_zero, epsC_neg_one]
  have hm : StronglyMeasurable[histSigma (newsS epsC) 0] (newsS epsC 1) := by
    rw [e1]
    exact (((measurable_hist (x := newsS epsC) (t := 0) le_rfl).pow_const 2).sub_const
      1).stronglyMeasurable
  have hle : histSigma (newsS epsC) 0 ≤ MeasurableSpace.pi :=
    (histS_le' h 0).trans (coinZ.𝓕.le 0)
  rw [condExp_of_stronglyMeasurable hle hm (by simpa [newsS] using h.integrable 0)] at h0
  apply shock_not_ae_zero h one_pos 0
  simpa [newsS] using h0

end Presample

end Cochrane.ObservationalEquivalence.TidyR5GrangerL2
