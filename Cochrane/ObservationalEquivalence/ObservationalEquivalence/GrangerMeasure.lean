/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.SurplusRegressionMeasure
import ObservationalEquivalence.Granger

/-!
# Debt Granger-causes an exogenous surplus: genuine conditional expectations

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.3, p. 501 (footnote 1:
Granger causality) and pp. 501–502 ("If people learn from reading the news that surpluses will be
poor…"), and Online Appendix Chapter 2, introduction, p. 593 (debt should Granger-cause
surpluses even when surpluses are exogenous).

The module `Granger` treats the news model `s_{t+1} = ε_t` in an abstract `ExpectationSystem`
and reads Granger causality off the VAR matrix. Here the model lives in the genuine i.i.d.
economy `iidZSystem` (shocks `ε_k`, `k ∈ ℤ`, mean zero, variance `σ² > 0`, bounded), the value of
debt is the valuation equation with Mathlib's `condExp` (`SurplusRegressionMeasure.valueM`), and
Granger causality is defined with genuine conditional expectations on the σ-algebras generated
by the observed histories:

* `histSigma x t = σ(x_0, …, x_t)`;
* `GrangerNonCausal μ x y`: `E[y_{t+1} | y_{≤t}, x_{≤t}] = E[y_{t+1} | y_{≤t}]` a.e. for every `t`
  (adding the history of `x` does not change the forecast of `y`).

## Main results

* `newsV_ae`: `v_t = ε_t` a.e. (debt reveals the news); `surplus_eq_value`: `s_{t+1} = v_t` a.e.
* `forecast_own`: `E[s_{t+1} | s_{≤t}] = 0` — past surpluses do not forecast the surplus;
  `forecast_joint`: `E[s_{t+1} | s_{≤t}, v_{≤t}] = v_t` — debt forecasts it perfectly.
* `debt_granger_causes_surplus`: debt Granger-causes surpluses;
  `surplus_not_granger_cause_debt`: surpluses do not Granger-cause debt (both forecasts of
  `v_{t+1}` are zero).
* `granger_matches_var`: the genuine notions agree with the VAR statements of `Granger`
  (`news_debt_causes_surplus`, `news_surplus_not_cause_debt`); `coin_news_granger`: the coin
  economy.
-/

namespace Cochrane.ObservationalEquivalence.GrangerMeasure

open MeasureTheory ProbabilityTheory Filter
open Cochrane.ObservationalEquivalence.ExpectationsMeasure
open Cochrane.ObservationalEquivalence.ExpectationsMeasureIIDZ
open Cochrane.ObservationalEquivalence.MACovariance
open Cochrane.ObservationalEquivalence.SurplusRegression
open Cochrane.ObservationalEquivalence.SurplusRegressionMeasure
open Cochrane.ObservationalEquivalence.Granger

/-! ### Histories and Granger causality -/

variable {Ω : Type*}

/-- Cochrane (2023), p. 501, footnote 1: the information in the history of a process,
`σ(x_0, …, x_t)`. -/
abbrev histSigma (x : ℕ → Ω → ℝ) (t : ℕ) : MeasurableSpace Ω :=
  ⨆ k ∈ Set.Iic t, MeasurableSpace.comap (x k) (inferInstance : MeasurableSpace ℝ)

/-- Cochrane (2023), p. 501, footnote 1: each observation is measurable for its history. -/
theorem measurable_hist {x : ℕ → Ω → ℝ} {t k : ℕ} (hk : k ≤ t) :
    Measurable[histSigma x t] (x k) :=
  Measurable.of_comap_le (le_iSup₂ (f := fun i (_ : i ∈ Set.Iic t) =>
    MeasurableSpace.comap (x i) (inferInstance : MeasurableSpace ℝ)) k hk)

/-- Cochrane (2023), p. 501, footnote 1: a history is coarser than any σ-algebra for which the
observations are measurable. -/
theorem histSigma_le {m : MeasurableSpace Ω} {x : ℕ → Ω → ℝ} {t : ℕ}
    (h : ∀ k ≤ t, Measurable[m] (x k)) : histSigma x t ≤ m :=
  iSup₂_le fun k hk => (h k hk).comap_le

/-- Cochrane (2023), p. 501, footnote 1 (Granger non-causality with genuine conditional
expectations): `x` does not Granger-cause `y` when adding the history of `x` to that of `y`
leaves the forecast of `y_{t+1}` unchanged, `E[y_{t+1} | y_{≤t}, x_{≤t}] = E[y_{t+1} | y_{≤t}]`
a.e., at every date. -/
def GrangerNonCausal [MeasurableSpace Ω] (μ : Measure Ω) (x y : ℕ → Ω → ℝ) : Prop :=
  ∀ t, μ[y (t + 1) | histSigma y t ⊔ histSigma x t] =ᵐ[μ] μ[y (t + 1) | histSigma y t]

/-! ### The news model in the i.i.d. economy -/

/-- Cochrane (2023), pp. 501–502: the news surplus `s_t = ε_{t−1}` (the moving average
`newsCoeff` of `Granger`) in the i.i.d. economy. -/
noncomputable def newsS : ℕ → (ℤ → ℝ) → ℝ := surplus newsCoeff 1 shockZ

/-- Cochrane (2023), pp. 501–502 and eq. (2.22), p. 602: the value of debt in the news model,
`v_t = E_t ∑_j ρ^j s_{t+1+j}` (Mathlib `condExp`). -/
noncomputable def newsV (ν : ProbabilityMeasure ℝ) (ρ : ℝ) : ℕ → (ℤ → ℝ) → ℝ :=
  valueM (iidZSystem ν) ρ newsS

/-- Cochrane (2023), pp. 501–502: next period's news surplus is today's shock,
`s_{t+1} = ε_t`. -/
theorem newsS_succ (t : ℕ) : newsS (t + 1) = shockZ (t : ℤ) := by
  rw [newsS, news_surplus]
  congr 1
  push_cast
  ring

/-- Cochrane (2023), pp. 501–502: the news surplus of date `k` is known at `k − 1`:
`s_k ∈ σ(ε_j : j < k)`. -/
theorem measurable_newsS {k : ℕ} {I : Set ℤ} (hI : (k : ℤ) - 1 ∈ I) :
    Measurable[sigmaOf I] (newsS k) := by
  rw [newsS, news_surplus]
  exact measurable_shockZ_sigmaOf hI

variable {ν : ProbabilityMeasure ℝ} {σ2 B ρ : ℝ}

/-- Cochrane (2023), pp. 501–502 and Online Appendix p. 593 (debt reveals the news, genuinely):
`v_t = ε_t` a.e. -/
theorem newsV_ae (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B)
    (hρ : |ρ| < 1) (t : ℕ) : newsV ν ρ t =ᵐ[(iidZSystem ν).μ] shockZ (t : ℤ) := by
  have h := valueM_eq_finite (iidZ_shockMDS hmean hvar hbdd) hρ newsCoeff_support t
  have e : maProc (vCoeff ρ newsCoeff 1) 1 shockZ (t : ℤ) = shockZ (t : ℤ) := by
    simp [maProc, vCoeff, newsCoeff, Finset.sum_range_succ]
  rw [e] at h
  exact h

/-- Cochrane (2023), pp. 501–502: the value of debt is known at `t`. -/
theorem stronglyMeasurable_newsV (ρ : ℝ) (t : ℕ) :
    StronglyMeasurable[(iidZSystem ν).𝓕 t] (newsV ν ρ t) :=
  (iidZSystem ν).stronglyMeasurable_E t _

/-- Cochrane (2023), pp. 501–502: in the news model debt forecasts the surplus perfectly,
`s_{t+1} = v_t` a.e. -/
theorem surplus_eq_value (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B)
    (hρ : |ρ| < 1) (t : ℕ) : newsS (t + 1) =ᵐ[(iidZSystem ν).μ] newsV ν ρ t := by
  rw [newsS_succ]
  exact (newsV_ae hmean hvar hbdd hρ t).symm

/-- Cochrane (2023), p. 501 (tool): conditioning a shock on the joint history of two processes
that is generated by other shocks gives zero. -/
theorem condExp_shockZ_hist (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) {x y : ℕ → (ℤ → ℝ) → ℝ}
    {t : ℕ} {I : Set ℤ} (hmI : histSigma x t ⊔ histSigma y t ≤ sigmaOf I) {k : ℤ} (hk : k ∉ I) :
    (iidZSystem ν).μ[shockZ k | histSigma x t ⊔ histSigma y t] =ᵐ[(iidZSystem ν).μ] 0 := by
  have h0 : (iidZSystem ν).μ[(iidZSystem ν).μ[shockZ k | sigmaOf I] |
      histSigma x t ⊔ histSigma y t] =ᵐ[(iidZSystem ν).μ]
      (iidZSystem ν).μ[(0 : (ℤ → ℝ) → ℝ) | histSigma x t ⊔ histSigma y t] :=
    condExp_congr_ae (condExp_shockZ_sigmaOf hmean hk)
  filter_upwards [(condExp_condExp_of_le (μ := (iidZSystem ν).μ) (f := shockZ k) hmI
    (sigmaOf_le I)).symm, h0] with ω h1 h2
  rw [h1, h2, condExp_zero]

/-- Cochrane (2023), pp. 501–502: the surplus history is generated by shocks dated before `t`. -/
theorem histS_le (t : ℕ) : histSigma newsS t ≤ sigmaOf (Set.Iio (t : ℤ)) :=
  histSigma_le fun k hk => measurable_newsS (Set.mem_Iio.2 (by omega))

/-- Cochrane (2023), pp. 501–502: the debt history is date-`t` information. -/
theorem histV_le_filtration (ρ : ℝ) (t : ℕ) :
    histSigma (newsV ν ρ) t ≤ (iidZSystem ν).𝓕 t :=
  histSigma_le fun k hk =>
    ((stronglyMeasurable_newsV ρ k).mono ((iidZSystem ν).𝓕.mono hk)).measurable

/-- Cochrane (2023), pp. 501–502: the surplus history is date-`t` information. -/
theorem histS_le_filtration (t : ℕ) : histSigma newsS t ≤ (iidZSystem ν).𝓕 t :=
  (histS_le t).trans (sigmaOf_mono fun _ h => Set.mem_Iic.2 (Set.mem_Iio.1 h).le)

/-- Cochrane (2023), pp. 501–502 ("past surpluses do not forecast"): the forecast of next
period's surplus from past surpluses alone is zero, `E[s_{t+1} | s_{≤t}] = 0` a.e. — to an
econometrician who sees only surpluses they are white noise. -/
theorem forecast_own (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) (t : ℕ) :
    (iidZSystem ν).μ[newsS (t + 1) | histSigma newsS t] =ᵐ[(iidZSystem ν).μ] 0 := by
  rw [newsS_succ, ← sup_idem (histSigma newsS t)]
  exact condExp_shockZ_hist hmean (by rw [sup_idem]; exact histS_le t)
    fun h => lt_irrefl _ (Set.mem_Iio.1 h)

/-- Cochrane (2023), pp. 501–502 (debt forecasts surpluses): adding the history of debt, the
forecast of next period's surplus is the value of debt, `E[s_{t+1} | s_{≤t}, v_{≤t}] = v_t` a.e.
(and the forecast is perfect, `surplus_eq_value`). -/
theorem forecast_joint (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B)
    (hρ : |ρ| < 1) (t : ℕ) :
    (iidZSystem ν).μ[newsS (t + 1) | histSigma newsS t ⊔ histSigma (newsV ν ρ) t]
      =ᵐ[(iidZSystem ν).μ] newsV ν ρ t := by
  have hle : histSigma newsS t ⊔ histSigma (newsV ν ρ) t ≤ MeasurableSpace.pi :=
    sup_le ((histS_le_filtration t).trans ((iidZSystem ν).𝓕.le t))
      ((histV_le_filtration ρ t).trans ((iidZSystem ν).𝓕.le t))
  have hvm : StronglyMeasurable[histSigma newsS t ⊔ histSigma (newsV ν ρ) t] (newsV ν ρ t) :=
    ((measurable_hist (x := newsV ν ρ) (t := t) le_rfl).mono
      (le_sup_right : histSigma (newsV ν ρ) t ≤ histSigma newsS t ⊔ histSigma (newsV ν ρ) t)
      le_rfl).stronglyMeasurable
  have hvi : Integrable (newsV ν ρ t) (iidZSystem ν).μ := (iidZSystem ν).integrable_E t _
  filter_upwards [condExp_congr_ae (m := histSigma newsS t ⊔ histSigma (newsV ν ρ) t)
    (surplus_eq_value hmean hvar hbdd hρ t)] with ω h1
  rw [h1, condExp_of_stronglyMeasurable hle hvm hvi]

/-- Cochrane (2023), pp. 501–502 and Online Appendix p. 593 (**debt Granger-causes surpluses**,
with genuine conditional expectations): although surpluses are exogenous, the history of debt
changes the forecast of the surplus. -/
theorem debt_granger_causes_surplus (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) (hρ : |ρ| < 1) :
    ¬ GrangerNonCausal (iidZSystem ν).μ (newsV ν ρ) newsS := by
  intro h
  apply shockZ_not_ae_zero hvar hσ 0
  have := ((forecast_joint hmean hvar hbdd hρ 0).symm.trans (h 0)).trans (forecast_own hmean 0)
  exact (newsV_ae hmean hvar hbdd hρ 0).symm.trans this

/-- Cochrane (2023), pp. 501–502: surpluses do not Granger-cause debt — the forecast of `v_{t+1}`
is zero with or without the surplus history. -/
theorem surplus_not_granger_cause_debt (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B)
    (hρ : |ρ| < 1) : GrangerNonCausal (iidZSystem ν).μ newsS (newsV ν ρ) := by
  intro t
  have hk : ((t + 1 : ℕ) : ℤ) ∉ Set.Iic (t : ℤ) := by
    simp only [Set.mem_Iic, not_le]; omega
  have hJ : histSigma (newsV ν ρ) t ⊔ histSigma newsS t ≤ sigmaOf (Set.Iic (t : ℤ)) :=
    sup_le (histV_le_filtration ρ t) (histS_le_filtration (ν := ν) t)
  have hO : histSigma (newsV ν ρ) t ⊔ histSigma (newsV ν ρ) t ≤ sigmaOf (Set.Iic (t : ℤ)) := by
    rw [sup_idem]; exact histV_le_filtration ρ t
  have h1 := (condExp_congr_ae (m := histSigma (newsV ν ρ) t ⊔ histSigma newsS t)
    (newsV_ae hmean hvar hbdd hρ (t + 1))).trans (condExp_shockZ_hist hmean hJ hk)
  have h2 := (condExp_congr_ae (m := histSigma (newsV ν ρ) t ⊔ histSigma (newsV ν ρ) t)
    (newsV_ae hmean hvar hbdd hρ (t + 1))).trans (condExp_shockZ_hist hmean hO hk)
  rw [sup_idem] at h2
  exact h1.trans h2.symm

/-- Cochrane (2023), p. 501, footnote 1 and pp. 501–502 (**link** with `Granger`): the genuine
Granger statements agree with the VAR statements of the abstract news model — debt causes
surpluses (`news_debt_causes_surplus`), surpluses do not cause debt
(`news_surplus_not_cause_debt`). -/
theorem granger_matches_var (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) (hρ : |ρ| < 1) :
    (¬ GrangerNonCausal (iidZSystem ν).μ (newsV ν ρ) newsS ∧ ¬ OneStepNonCausal newsA 1 0 ∧
      ¬ IRFNonCausal newsA 1 0) ∧
    (GrangerNonCausal (iidZSystem ν).μ newsS (newsV ν ρ) ∧ IRFNonCausal newsA 0 1) :=
  ⟨⟨debt_granger_causes_surplus hmean hvar hσ hbdd hρ, news_debt_causes_surplus.1,
      news_debt_causes_surplus.2⟩,
    surplus_not_granger_cause_debt hmean hvar hbdd hρ, news_surplus_not_cause_debt⟩

/-- Cochrane (2023), pp. 501–502: in the fair `±1` coin economy, debt reveals the news
(`s_{t+1} = v_t`), debt Granger-causes surpluses and surpluses do not Granger-cause debt. -/
theorem coin_news_granger (hρ : |ρ| < 1) :
    (∀ t, newsS (t + 1) =ᵐ[(iidZSystem ExpectationsMeasureIID.coin).μ]
      newsV ExpectationsMeasureIID.coin ρ t) ∧
    ¬ GrangerNonCausal (iidZSystem ExpectationsMeasureIID.coin).μ
      (newsV ExpectationsMeasureIID.coin ρ) newsS ∧
    GrangerNonCausal (iidZSystem ExpectationsMeasureIID.coin).μ newsS
      (newsV ExpectationsMeasureIID.coin ρ) :=
  ⟨surplus_eq_value ExpectationsMeasureIID.coin_mean ExpectationsMeasureIID.coin_var
      ExpectationsMeasureIID.coin_bdd hρ,
    debt_granger_causes_surplus ExpectationsMeasureIID.coin_mean ExpectationsMeasureIID.coin_var
      one_pos ExpectationsMeasureIID.coin_bdd hρ,
    surplus_not_granger_cause_debt ExpectationsMeasureIID.coin_mean
      ExpectationsMeasureIID.coin_var ExpectationsMeasureIID.coin_bdd hρ⟩

end Cochrane.ObservationalEquivalence.GrangerMeasure
