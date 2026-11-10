/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.TidyR8OUPresentValue

/-!
# The innovation identities (3.46)–(3.51) with Brownian shocks

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.6.3, pp. 76–79,
eqs. (3.42)–(3.51). The book takes innovations `Δ_t = E_{t+Δ} − E_t` of the linearised value
identity (3.43) and bond-price identity (3.49) and obtains (3.46)
`Δ_t dR^n_t = ∫_0^∞ e^{−rτ}Δ_t s̃_{t+τ}dτ − ∫_0^∞ e^{−rτ}Δ_t dR_{t+τ}`, (3.50)
`Δ_t dR^n_t = −∫_0^∞ e^{−(r+ω)τ}Δ_t dR^n_{t+τ}` and the weighted-inflation identity (3.51).
`ContinuousLinear` proved them as differences of two perfect-foresight equilibria
(`ContinuousLinear.Eqm.LinearEqm`, `ContinuousLinear.news_value`, `ContinuousLinear.news_bond`,
`ContinuousLinear.news_weighted_inflation`). Here they are conditional-expectation revisions in a
stochastic economy.

## The stochastic linearised economy

`StochLinearEqm`: processes `v, q, b, R^n, π, s̃` on a filtered probability space (`R^n` is the
expected nominal return rate, the drift of `dR^n`), together with **versions of their forecasts**
`F^x_u(τ) = E_u x_τ` (`τ ≥ u`) such that, for every conditioning date `u` and almost every state,
the forecast paths `τ ↦ F^x_u(τ)` satisfy the linearised model from date `u` on
(`ContinuousLinear.Eqm.LinearEqm`: flow (3.42) in expectation, bond identity (3.48) in
expectation, the transversality conditions); the value split `v = q + b − 1` holds at every date.
This is the content of the linear model with Brownian shocks: in `dx = μ dt + σ dz` the `dz`
terms have zero conditional mean (`TidyR7ItoInnovation.expected_increment`), so expected paths
obey the drift equations — e.g. for the AR(1) surplus `E_u s_{u+τ} = e^{−ητ}s_u`
(`TidyR7ItoInnovation.forecast_condExp`), which is how the example `fiscalInflation` below is
verified.

## Main results (`0 ≤ t₀ ≤ t`, a.s.; `Δx = E_t x − E_{t₀} x`)

* `StochLinearEqm.revision_value` (**(3.46), exact at every horizon**): the innovation in the
  value of debt is
  `v_t − E_{t₀}v_t = ∫_0^∞ e^{−rτ}Δs̃_{t+τ}dτ − ∫_0^∞ e^{−rτ}ΔR'_{t+τ}dτ` (`R' = R^n − π`). With
  the flow (3.42) and no price-level diffusion, reading `v_t − E_{t₀}v_t` as the book's
  `Δ_t dR^n_t`, the `dW`-part of the bond return, is first-order by the pattern of
  `TidyR7ItoInnovation.innovation_sq_le`; no theorem here proves that identification.
* `StochLinearEqm.revision_bond` (**(3.50)**): `q_t − E_{t₀}q_t = −∫_0^∞ e^{−(r+ω)τ}ΔR^n_{t+τ}dτ`.
* `StochLinearEqm.revision_weighted_inflation` (**(3.51) with the face-value term**):
  `∫e^{−(r+ω)τ}Δπ = −∫e^{−rτ}Δs̃ + ∫(e^{−rτ} − e^{−(r+ω)τ})ΔR' + (b_t − E_{t₀}b_t)`;
  `StochLinearEqm.revision_weighted_inflation_predetermined`: the book's (3.51) verbatim when
  `b_t` is
  `𝓕_{t₀}`-measurable; `faceValue_revision_sq_le`: if `b` has no diffusion and drift bounded by
  `C`, `E[(b_t − E_{t₀}b_t)²] ≤ (2C(t − t₀))²`, so (3.51) holds to first order in `t − t₀`.
* `forecast_pv_condExp`: the forward integrals of forecasts are conditional expectations of the
  forward integrals of the actual processes, `∫_0^∞e^{−rτ}F^s̃_u(t+τ)dτ = E_u∫_0^∞e^{−rτ}s̃_{t+τ}dτ`
  (`TidyR8ConditionalFubini.condExp_integral_interchange`), so (3.46) reads
  `v_t − E_{t₀}v_t = (E_t − E_{t₀})∫e^{−rτ}s̃_{t+τ}dτ − (E_t − E_{t₀})∫e^{−rτ}(R' − r)_{t+τ}dτ`.
* `StochLinearEqm.revision_is_news` (**link to the deterministic news**): for a.e. state the
  date-`t₀` and date-`t` forecast paths are two perfect-foresight equilibria from `t` (old and
  new), so
  `ContinuousLinear.news_value`, `ContinuousLinear.news_bond` and
  `ContinuousLinear.news_weighted_inflation` apply to them verbatim.

## Non-vacuity

`fiscalInflation`: the economy `v = q = b = 1`, `R^n = r`, `s̃ = r + x`, `π = −x` with `x` the AR(1)
surplus deviation (the path version `TidyR8OUPresentValue.ouPath` of `TidyR7ItoInnovation.ou`),
forecasts `E_u x_τ = e^{−η(τ−u)}x_u`, is a `StochLinearEqm` for `r > 0`, `r + η > 0` and every
`ω`, given a motion with continuous paths (a fiscal shock absorbed entirely by expected
inflation). `fiscalInflation_surplus_news`: its surplus news is
`(σ/(r + η))e^{−ηt}∫_{t₀}^t e^{ηv}dW`,
and `bmPath_fiscalInflation_news_pos`: on the constructed motion it has positive mean square.
With `σ = 0` all revisions vanish (`TidyR7ItoInnovation.ou_sigma_zero`).
-/

namespace Cochrane.Generality.TidyR8StochasticNews

open MeasureTheory ProbabilityTheory Filter Topology Function
open Cochrane.Generality.TidyR7StieltjesSums Cochrane.Generality.TidyR7BrownianTools
  Cochrane.Generality.TidyR7BrownianQV Cochrane.Generality.TidyR7ItoL2
  Cochrane.Generality.TidyR7ItoSums Cochrane.Generality.TidyR7ItoIntegral
  Cochrane.Generality.TidyR7ItoUnbounded Cochrane.Generality.TidyR7ItoProducts
  Cochrane.Generality.TidyR7ItoProcess Cochrane.Generality.TidyR7ItoProductRule
  Cochrane.Generality.TidyR7ItoBridge Cochrane.Generality.TidyR7BrownianExist
  Cochrane.Generality.TidyR7BrownianSchauder Cochrane.Generality.TidyR7ItoDiscountFactorCex
  Cochrane.Generality.TidyR7ItoInnovation Cochrane.Generality.TidyR8ConditionalFubini
  Cochrane.Generality.ContinuousLinear
open scoped ENNReal NNReal

/-! ## Deterministic news without a predetermined face value -/

/-- Cochrane (2023), (3.42)–(3.49), pp. 76–78: a linearised equilibrium from `t₀` is one from
every later date `t` at which the value split `v_t = q_t + b_t − 1` holds. -/
theorem linearEqm_restrict {r ω t₀ t : ℝ} {v q b Rn infl s : ℝ → ℝ}
    (E : Eqm.LinearEqm r ω t₀ v q b Rn infl s) (h : t₀ ≤ t) (hv : v t = q t + b t - 1) :
    Eqm.LinearEqm r ω t v q b Rn infl s where
  flow τ hτ := E.flow τ (h.trans hτ)
  bond τ hτ := E.bond τ (h.trans hτ)
  value := hv
  tvcV := E.tvcV
  tvcQ := E.tvcQ
  intS := E.intS.mono_set (Set.Ioi_subset_Ioi h)
  intR := E.intR.mono_set (Set.Ioi_subset_Ioi h)
  intN := E.intN.mono_set (Set.Ioi_subset_Ioi h)

/-- **Cochrane (2023), (3.46), p. 77, without assuming a predetermined face value.** Between two
linearised equilibria from `t`, the news in the value of debt is the news in discounted
surpluses minus the news in discounted real returns:
`v₁_t − v₀_t = ∫_0^∞ e^{−rτ}Δs̃_{t+τ}dτ − ∫_0^∞ e^{−rτ}ΔR'_{t+τ}dτ`. With `b₁_t = b₀_t` this is
`ContinuousLinear.news_value`. -/
theorem news_value_total {r ω t : ℝ} {v₀ q₀ b₀ Rn₀ infl₀ s₀ v₁ q₁ b₁ Rn₁ infl₁ s₁ : ℝ → ℝ}
    (E₀ : Eqm.LinearEqm r ω t v₀ q₀ b₀ Rn₀ infl₀ s₀)
    (E₁ : Eqm.LinearEqm r ω t v₁ q₁ b₁ Rn₁ infl₁ s₁) :
    v₁ t - v₀ t =
      (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (s₁ (t + τ) - s₀ (t + τ))) -
        ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) *
          ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ))) := by
  rw [eqm_value E₁, eqm_value E₀]
  have hS := integral_weighted_sub (w := fun τ => Real.exp (-(r * τ)))
    (a := fun τ => s₁ (t + τ)) (c := fun τ => s₀ (t + τ)) (S := Set.Ioi 0)
    (integrableOn_shift_weighted E₁.intS) (integrableOn_shift_weighted E₀.intS)
  have hR := integral_weighted_sub (w := fun τ => Real.exp (-(r * τ)))
    (a := fun τ => Rn₁ (t + τ) - infl₁ (t + τ) - r)
    (c := fun τ => Rn₀ (t + τ) - infl₀ (t + τ) - r) (S := Set.Ioi 0)
    (integrableOn_shift_weighted (g := fun τ => Rn₁ τ - infl₁ τ - r) E₁.intR)
    (integrableOn_shift_weighted (g := fun τ => Rn₀ τ - infl₀ τ - r) E₀.intR)
  have hR' : ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) *
      ((Rn₁ (t + τ) - infl₁ (t + τ) - r) - (Rn₀ (t + τ) - infl₀ (t + τ) - r)) =
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) *
        ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ))) := by
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    ring
  beta_reduce at hS hR
  linarith

/-- **Cochrane (2023), (3.51), p. 78, without assuming a predetermined face value.** For `ω ≥ 0`,
between two linearised equilibria from `t`:
`∫_0^∞ e^{−(r+ω)τ}Δπ_{t+τ}dτ = −∫_0^∞ e^{−rτ}Δs̃_{t+τ}dτ
  + ∫_0^∞ (e^{−rτ} − e^{−(r+ω)τ})ΔR'_{t+τ}dτ + (b₁_t − b₀_t)`.
With `b₁_t = b₀_t` this is `ContinuousLinear.news_weighted_inflation`. -/
theorem news_weighted_inflation_total {r ω t : ℝ}
    {v₀ q₀ b₀ Rn₀ infl₀ s₀ v₁ q₁ b₁ Rn₁ infl₁ s₁ : ℝ → ℝ} (hω : 0 ≤ ω)
    (E₀ : Eqm.LinearEqm r ω t v₀ q₀ b₀ Rn₀ infl₀ s₀)
    (E₁ : Eqm.LinearEqm r ω t v₁ q₁ b₁ Rn₁ infl₁ s₁) :
    ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * (infl₁ (t + τ) - infl₀ (t + τ)) =
      -(∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (s₁ (t + τ) - s₀ (t + τ))) +
        (∫ τ in Set.Ioi 0, (Real.exp (-(r * τ)) - Real.exp (-((r + ω) * τ))) *
          ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ)))) +
        (b₁ t - b₀ t) := by
  have hV := news_value_total E₀ E₁
  have hB := news_bond_real E₀ E₁
  have hv₀ := E₀.value
  have hv₁ := E₁.value
  have iR : IntegrableOn (fun τ => Real.exp (-(r * τ)) *
      ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ)))) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun
      ((integrableOn_shift_weighted (g := fun τ => Rn₁ τ - infl₁ τ - r) E₁.intR).sub
        (integrableOn_shift_weighted (g := fun τ => Rn₀ τ - infl₀ τ - r) E₀.intR))
      (fun τ _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    ring
  have iM : IntegrableOn (fun τ => Real.exp (-((r + ω) * τ)) *
      ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ)))) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun
      ((eqm_int_real_bond hω E₁).sub (eqm_int_real_bond hω E₀)) (fun τ _ => ?_)
      measurableSet_Ioi
    simp only [Pi.sub_apply]
    ring
  have iP : IntegrableOn (fun τ => Real.exp (-((r + ω) * τ)) *
      (infl₁ (t + τ) - infl₀ (t + τ))) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun ((eqm_int_infl hω E₁).sub (eqm_int_infl hω E₀))
      (fun τ _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    ring
  have hsplitB : ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) *
        (((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ))) +
          (infl₁ (t + τ) - infl₀ (t + τ))) =
      (∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) *
        ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ)))) +
      ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * (infl₁ (t + τ) - infl₀ (t + τ)) := by
    rw [← integral_add iM iP]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    ring
  have hsplitW : ∫ τ in Set.Ioi 0, (Real.exp (-(r * τ)) - Real.exp (-((r + ω) * τ))) *
        ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ))) =
      (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) *
        ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ)))) -
      ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) *
        ((Rn₁ (t + τ) - infl₁ (t + τ)) - (Rn₀ (t + τ) - infl₀ (t + τ))) := by
    rw [← integral_sub iR iM]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    ring
  rw [hsplitW]
  rw [hsplitB] at hB
  linarith

/-! ## The stochastic linearised economy -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

variable (μ : Measure Ω) (𝓕 : Filtration ℝ mΩ) (r ω : ℝ) (v q b Rn infl s : ℝ → Ω → ℝ)
  (Fv Fq Fb FRn Finfl Fs : ℝ → ℝ → Ω → ℝ)

/-- **Cochrane (2023), §3.6.3, (3.42)–(3.49), pp. 76–78: a stochastic linearised equilibrium.**
Processes `v` (value), `q` (bond price), `b` (real face value), `R^n` (expected nominal return
rate), `π` (`infl`) and `s̃` (`s`), with versions `F^x_u(τ)` of the forecasts `E_u x_τ`
(`τ ≥ u ≥ 0`) such that for every `u ≥ 0` and a.e. state the forecast paths form a linearised
equilibrium from `u` (`ContinuousLinear.Eqm.LinearEqm`); the value split `v = q + b − 1` holds at
every date; `v`, `q`, `b` are adapted and integrable. -/
structure StochLinearEqm where
  fcV : ∀ u τ, 0 ≤ u → u ≤ τ → Fv u τ =ᵐ[μ] μ[v τ | 𝓕 u]
  fcQ : ∀ u τ, 0 ≤ u → u ≤ τ → Fq u τ =ᵐ[μ] μ[q τ | 𝓕 u]
  fcB : ∀ u τ, 0 ≤ u → u ≤ τ → Fb u τ =ᵐ[μ] μ[b τ | 𝓕 u]
  fcRn : ∀ u τ, 0 ≤ u → u ≤ τ → FRn u τ =ᵐ[μ] μ[Rn τ | 𝓕 u]
  fcInfl : ∀ u τ, 0 ≤ u → u ≤ τ → Finfl u τ =ᵐ[μ] μ[infl τ | 𝓕 u]
  fcS : ∀ u τ, 0 ≤ u → u ≤ τ → Fs u τ =ᵐ[μ] μ[s τ | 𝓕 u]
  path : ∀ u, 0 ≤ u → ∀ᵐ x ∂μ, Eqm.LinearEqm r ω u (fun τ => Fv u τ x)
    (fun τ => Fq u τ x) (fun τ => Fb u τ x) (fun τ => FRn u τ x) (fun τ => Finfl u τ x)
    (fun τ => Fs u τ x)
  value : ∀ τ, 0 ≤ τ → v τ =ᵐ[μ] fun x => q τ x + b τ x - 1
  adV : ∀ u, StronglyMeasurable[𝓕 u] (v u)
  adQ : ∀ u, StronglyMeasurable[𝓕 u] (q u)
  adB : ∀ u, StronglyMeasurable[𝓕 u] (b u)
  intV : ∀ u, Integrable (v u) μ
  intQ : ∀ u, Integrable (q u) μ
  intB : ∀ u, Integrable (b u) μ

variable {μ 𝓕 r ω v q b Rn infl s Fv Fq Fb FRn Finfl Fs}

namespace StochLinearEqm

variable [IsFiniteMeasure μ]
  (E : StochLinearEqm μ 𝓕 r ω v q b Rn infl s Fv Fq Fb FRn Finfl Fs)
include E

/-- Cochrane (2023), §3.6.3, p. 77: the date-`u` forecast of a date-`u` adapted variable is the
variable itself, `F^v_u(u) = v_u` a.s.
From Mathlib `condExp_of_stronglyMeasurable`. -/
theorem forecast_self_v {u : ℝ} (hu : 0 ≤ u) : Fv u u =ᵐ[μ] v u := by
  rw [← condExp_of_stronglyMeasurable (𝓕.le u) (E.adV u) (E.intV u)]
  exact E.fcV u u hu le_rfl

/-- Cochrane (2023), §3.6.3, p. 78: `F^q_u(u) = q_u` a.s. -/
theorem forecast_self_q {u : ℝ} (hu : 0 ≤ u) : Fq u u =ᵐ[μ] q u := by
  rw [← condExp_of_stronglyMeasurable (𝓕.le u) (E.adQ u) (E.intQ u)]
  exact E.fcQ u u hu le_rfl

/-- Cochrane (2023), §3.6.3, p. 77: `F^b_u(u) = b_u` a.s. -/
theorem forecast_self_b {u : ℝ} (hu : 0 ≤ u) : Fb u u =ᵐ[μ] b u := by
  rw [← condExp_of_stronglyMeasurable (𝓕.le u) (E.adB u) (E.intB u)]
  exact E.fcB u u hu le_rfl

/-- Cochrane (2023), pp. 76–77: the value split holds for forecasts, `F^v_{t₀}(t) =
F^q_{t₀}(t) + F^b_{t₀}(t) − 1` a.s. (linearity of conditional expectation).
By Mathlib `condExp_add` and `condExp_sub`. -/
theorem forecast_value {t₀ t : ℝ} (h0 : 0 ≤ t₀) (h : t₀ ≤ t) :
    ∀ᵐ x ∂μ, Fv t₀ t x = Fq t₀ t x + Fb t₀ t x - 1 := by
  have e1 := condExp_congr_ae (m := 𝓕 t₀) (E.value t (h0.trans h))
  have e2 : (fun x => q t x + b t x - 1) = q t + b t - fun _ => (1 : ℝ) := by
    funext x
    simp
  rw [e2] at e1
  filter_upwards [E.fcV t₀ t h0 h, E.fcQ t₀ t h0 h, E.fcB t₀ t h0 h, e1,
    condExp_sub (m := 𝓕 t₀) ((E.intQ t).add (E.intB t)) (integrable_const (1 : ℝ)),
    condExp_add (m := 𝓕 t₀) (E.intQ t) (E.intB t)] with x h1 h2 h3 h4 h5 h6
  rw [h1, h2, h3, h4, h5, Pi.sub_apply, h6, condExp_const (𝓕.le t₀)]
  rfl

/-- **Cochrane (2023), §3.6.3, p. 77: link to the deterministic news.** For `0 ≤ t₀ ≤ t` and a.e.
state, the date-`t₀` forecast paths (old) and the date-`t` forecast paths (new) are two
linearised equilibria from `t`; `ContinuousLinear.news_value`, `ContinuousLinear.news_bond`,
`ContinuousLinear.news_weighted_inflation` apply to them, the face value being predetermined
exactly when `F^b_{t₀}(t) = F^b_t(t)`. -/
theorem revision_is_news {t₀ t : ℝ} (h0 : 0 ≤ t₀) (h : t₀ ≤ t) :
    ∀ᵐ x ∂μ, Eqm.LinearEqm r ω t (fun τ => Fv t₀ τ x) (fun τ => Fq t₀ τ x)
        (fun τ => Fb t₀ τ x) (fun τ => FRn t₀ τ x) (fun τ => Finfl t₀ τ x) (fun τ => Fs t₀ τ x) ∧
      Eqm.LinearEqm r ω t (fun τ => Fv t τ x) (fun τ => Fq t τ x)
        (fun τ => Fb t τ x) (fun τ => FRn t τ x) (fun τ => Finfl t τ x) (fun τ => Fs t τ x) := by
  filter_upwards [E.path t₀ h0, E.path t (h0.trans h), E.forecast_value h0 h] with x h1 h2 h3
  exact ⟨linearEqm_restrict h1 h h3, h2⟩

/-- **Cochrane (2023), (3.46), p. 77: the innovation in the value of debt, exactly.** For
`0 ≤ t₀ ≤ t`, a.s.
`v_t − E_{t₀}v_t = ∫_0^∞ e^{−rτ}(F^s̃_t − F^s̃_{t₀})(t+τ)dτ
  − ∫_0^∞ e^{−rτ}((F^{R^n}_t − F^π_t) − (F^{R^n}_{t₀} − F^π_{t₀}))(t+τ)dτ`:
the news in the value of debt is the news in discounted surpluses minus the news in discounted
real returns. -/
theorem revision_value {t₀ t : ℝ} (h0 : 0 ≤ t₀) (h : t₀ ≤ t) :
    ∀ᵐ x ∂μ, v t x - μ[v t | 𝓕 t₀] x =
      (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (Fs t (t + τ) x - Fs t₀ (t + τ) x)) -
        ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) *
          ((FRn t (t + τ) x - Finfl t (t + τ) x) - (FRn t₀ (t + τ) x - Finfl t₀ (t + τ) x)) := by
  filter_upwards [E.revision_is_news h0 h, E.forecast_self_v (h0.trans h),
    E.fcV t₀ t h0 h] with x hE h1 h2
  rw [← h1, ← h2]
  exact news_value_total hE.1 hE.2

/-- **Cochrane (2023), (3.50), p. 78: the unexpected bond price.** For `0 ≤ t₀ ≤ t`, a.s.
`q_t − E_{t₀}q_t = −∫_0^∞ e^{−(r+ω)τ}(F^{R^n}_t − F^{R^n}_{t₀})(t+τ)dτ`. -/
theorem revision_bond {t₀ t : ℝ} (h0 : 0 ≤ t₀) (h : t₀ ≤ t) :
    ∀ᵐ x ∂μ, q t x - μ[q t | 𝓕 t₀] x =
      -∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) * (FRn t (t + τ) x - FRn t₀ (t + τ) x) := by
  filter_upwards [E.revision_is_news h0 h, E.forecast_self_q (h0.trans h),
    E.fcQ t₀ t h0 h] with x hE h1 h2
  rw [← h1, ← h2]
  exact news_bond hE.1 hE.2

/-- **Cochrane (2023), (3.51), p. 78: the weighted-inflation identity with the face-value
revision.** For `ω ≥ 0`, `0 ≤ t₀ ≤ t`, a.s.
`∫_0^∞ e^{−(r+ω)τ}Δπ_{t+τ}dτ = −∫_0^∞ e^{−rτ}Δs̃_{t+τ}dτ
  + ∫_0^∞ (e^{−rτ} − e^{−(r+ω)τ})ΔR'_{t+τ}dτ + (b_t − E_{t₀}b_t)`, `Δ = F_t − F_{t₀}`. -/
theorem revision_weighted_inflation (hω : 0 ≤ ω) {t₀ t : ℝ} (h0 : 0 ≤ t₀) (h : t₀ ≤ t) :
    ∀ᵐ x ∂μ, ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) *
        (Finfl t (t + τ) x - Finfl t₀ (t + τ) x) =
      -(∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (Fs t (t + τ) x - Fs t₀ (t + τ) x)) +
        (∫ τ in Set.Ioi 0, (Real.exp (-(r * τ)) - Real.exp (-((r + ω) * τ))) *
          ((FRn t (t + τ) x - Finfl t (t + τ) x) - (FRn t₀ (t + τ) x - Finfl t₀ (t + τ) x))) +
        (b t x - μ[b t | 𝓕 t₀] x) := by
  filter_upwards [E.revision_is_news h0 h, E.forecast_self_b (h0.trans h),
    E.fcB t₀ t h0 h] with x hE h1 h2
  rw [← h1, ← h2]
  exact news_weighted_inflation_total hω hE.1 hE.2

/-- **Cochrane (2023), (3.51), p. 78, verbatim: a predetermined face value.** If `b_t` is
`𝓕_{t₀}`-measurable (`ω ≥ 0`, `0 ≤ t₀ ≤ t`), a.s.
`∫_0^∞ e^{−(r+ω)τ}Δπ_{t+τ}dτ = −∫_0^∞ e^{−rτ}Δs̃_{t+τ}dτ
  + ∫_0^∞ (e^{−rτ} − e^{−(r+ω)τ})ΔR'_{t+τ}dτ`. -/
theorem revision_weighted_inflation_predetermined (hω : 0 ≤ ω) {t₀ t : ℝ} (h0 : 0 ≤ t₀)
    (h : t₀ ≤ t) (hb : StronglyMeasurable[𝓕 t₀] (b t)) :
    ∀ᵐ x ∂μ, ∫ τ in Set.Ioi 0, Real.exp (-((r + ω) * τ)) *
        (Finfl t (t + τ) x - Finfl t₀ (t + τ) x) =
      -(∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (Fs t (t + τ) x - Fs t₀ (t + τ) x)) +
        ∫ τ in Set.Ioi 0, (Real.exp (-(r * τ)) - Real.exp (-((r + ω) * τ))) *
          ((FRn t (t + τ) x - Finfl t (t + τ) x) - (FRn t₀ (t + τ) x - Finfl t₀ (t + τ) x)) := by
  filter_upwards [E.revision_weighted_inflation hω h0 h] with x hx
  rw [hx, condExp_of_stronglyMeasurable (𝓕.le t₀) hb (E.intB t), sub_self, add_zero]

end StochLinearEqm

/-! ## The face-value revision is second order -/

/-- **Cochrane (2023), (3.51), pp. 78–79 (`dB` of order `dt`): the face-value term is second
order.** If `b` is an Itô process on `[t₀, t]` (`0 ≤ t₀ ≤ t`) with drift bounded by `C` and no
diffusion, `E[(b_t − E_{t₀}b_t)²] ≤ (2C(t − t₀))²`, against `O(t − t₀)` for the `dW`-terms: (3.51)
holds to first order in `t − t₀`. From `TidyR7ItoInnovation.innovation_sq_le`. -/
theorem faceValue_revision_sq_le {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ}
    {b a : ℝ → Ω → ℝ} {t₀ t C : ℝ} (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (h0 : 0 ≤ t₀) (h : t₀ ≤ t)
    (hb : ItoProcess μ 𝓕 W b a (fun _ _ => 0) t₀ t C 0) :
    ∫ x, (b t x - μ[b t | 𝓕 t₀] x) ^ 2 ∂μ ≤ (2 * C * (t - t₀)) ^ 2 := by
  have hle := innovation_sq_le hBM hWm h𝓕 h0 h hb
  have z := itoInt_const hBM hWm h𝓕 h0 h (c := fun _ => (0 : ℝ)) stronglyMeasurable_const
    (C := 0) fun _ => by simp
  have e : (fun x => (b t x - μ[b t | 𝓕 t₀] x
      - itoInt μ 𝓕 W (fun _ _ => 0) t₀ t x) ^ 2) =ᵐ[μ]
      fun x => (b t x - μ[b t | 𝓕 t₀] x) ^ 2 := by
    filter_upwards [z] with x hx
    rw [hx, zero_mul, sub_zero]
  rw [← integral_congr_ae e]
  refine hle.trans (le_of_eq ?_)
  ring


/-! ## Forward integrals of forecasts are conditional expectations -/

/-- **Cochrane (2023), (3.43), (3.46), p. 77
(`E_u∫_0^∞e^{−rτ}s̃_{t+τ}dτ = ∫_0^∞e^{−rτ}E_us̃_{t+τ}dτ`):
the forward integral of a forecast path is the conditional expectation of the forward integral of
the actual path.** For `u ≤ t`, if `F_u(τ)` is a version of `E_u s_τ` (`τ ≥ u`), jointly
measurable for `𝓑(ℝ) ⊗ 𝓕_u` in `τ` and the state, and `e^{−rτ}s_{t+τ}` is integrable on
`(0, ∞) × Ω`, then a.s. `E_u[∫_0^∞ e^{−rτ}s_{t+τ}dτ] = ∫_0^∞ e^{−rτ}F_u(t+τ)dτ`.
`TidyR8ConditionalFubini.condExp_integral_interchange`. -/
theorem forecast_pv_condExp {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {s : ℝ → Ω → ℝ} {Fs : ℝ → ℝ → Ω → ℝ} {r u t : ℝ} (hut : u ≤ t)
    (hfc : ∀ τ, u ≤ τ → Fs u τ =ᵐ[μ] μ[s τ | 𝓕 u])
    (hX : Integrable (uncurry fun τ x => Real.exp (-(r * τ)) * s (t + τ) x)
      ((volume.restrict (Set.Ioi 0)).prod μ))
    (hY : @StronglyMeasurable (ℝ × Ω) ℝ _ (@Prod.instMeasurableSpace ℝ Ω _ (𝓕 u))
      (uncurry fun τ x => Fs u (t + τ) x)) :
    μ[fun x => ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s (t + τ) x | 𝓕 u] =ᵐ[μ]
      fun x => ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * Fs u (t + τ) x := by
  have hY' : @StronglyMeasurable (ℝ × Ω) ℝ _ (@Prod.instMeasurableSpace ℝ Ω _ (𝓕 u))
      (uncurry fun τ x => Real.exp (-(r * τ)) * Fs u (t + τ) x) := by
    let _ : MeasurableSpace Ω := 𝓕 u
    have hc : Continuous fun τ : ℝ => Real.exp (-(r * τ)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id).neg
    exact ((hc.measurable.comp measurable_fst).mul hY.measurable).stronglyMeasurable
  refine condExp_integral_interchange (𝓕.le u) hX hY'
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ hτ => ?_))
  have hτ' : (0 : ℝ) < τ := hτ
  have e : (fun x => Real.exp (-(r * τ)) * s (t + τ) x) = Real.exp (-(r * τ)) • s (t + τ) := by
    funext x
    simp [smul_eq_mul]
  rw [e]
  filter_upwards [condExp_smul (μ := μ) (Real.exp (-(r * τ))) (s (t + τ)) (𝓕 u),
    hfc (t + τ) (by linarith)] with x h1 h2
  rw [h1, Pi.smul_apply, smul_eq_mul, h2]

/-! ## Non-vacuity: a fiscal shock absorbed by expected inflation -/

/-- Cochrane (2023), §3.6.3, p. 77 (non-vacuity): the forecast `E_u x_τ = e^{−η(τ−u)}x_u` of the
AR(1) surplus deviation `x = TidyR7ItoInnovation.ou`.
The forecast of `TidyR7ItoInnovation.ou_condExp` and `TidyR7ItoInnovation.forecast_condExp`. -/
noncomputable def ouForecast (μ : Measure Ω) (𝓕 : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ℝ)
    (η σ s0 u τ : ℝ) (x : Ω) : ℝ :=
  Real.exp (-(η * (τ - u))) * ou μ 𝓕 W η σ s0 u x

variable {W : ℝ≥0 → Ω → ℝ}

/-- Cochrane (2023), pp. 76–77 (non-vacuity): `e^{−rτ}(c + e^{−η(τ−u)}X)` is integrable on
`(u, ∞)` for `r > 0`, `r + η > 0`. -/
theorem integrableOn_forecast {r η : ℝ} (hr : 0 < r) (hrη : 0 < r + η) (c X u : ℝ) :
    IntegrableOn (fun τ => Real.exp (-(r * τ)) * (c + Real.exp (-(η * (τ - u))) * X))
      (Set.Ioi u) := by
  have i1 := (integrableOn_exp_mul_Ioi (a := -r) (by linarith) u).mul_const c
  have i2 := (integrableOn_exp_mul_Ioi (a := -(r + η)) (by linarith) u).mul_const
    (Real.exp (η * u) * X)
  refine IntegrableOn.congr_fun (i1.add i2) (fun τ _ => ?_) measurableSet_Ioi
  have e : Real.exp (-(r * τ)) * Real.exp (-(η * (τ - u))) =
      Real.exp (-(r + η) * τ) * Real.exp (η * u) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  simp only [Pi.add_apply]
  rw [neg_mul r τ]
  linear_combination (-X) * e

/-- **Cochrane (2023), §3.6.3, pp. 76–79 (non-vacuity of `StochLinearEqm`): a fiscal shock
absorbed entirely by expected inflation.** With the AR(1) surplus deviation
`x_u = ouPath_u` (`ds = −ηs dt + σ dε`), the economy `v = q = b = 1`, `R^n = r`,
`s̃ = r + x`, `π = −x`, with forecasts `F^x_u(τ) = e^{−η(τ−u)}x_u`, is a stochastic linearised
equilibrium for every maturity parameter `ω`, when `r > 0`, `r + η > 0` and `W` has continuous
paths. -/
theorem fiscalInflation (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hcont : ∀ x, Continuous fun t => W t x) {r η : ℝ} (hr : 0 < r)
    (hrη : 0 < r + η) (ω σ s0 : ℝ) :
    StochLinearEqm μ 𝓕 r ω (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => r)
      (fun τ x => -TidyR8OUPresentValue.ouPath W η σ s0 τ x)
      (fun τ x => r + TidyR8OUPresentValue.ouPath W η σ s0 τ x)
      (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ _ => r)
      (fun u τ x => -ouForecast μ 𝓕 W η σ s0 u τ x)
      (fun u τ x => r + ouForecast μ 𝓕 W η σ s0 u τ x) := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have hc1 : ∀ u, μ[fun (_ : Ω) => (1 : ℝ) | 𝓕 u] = fun _ => 1 := fun u =>
    condExp_const (𝓕.le u) 1
  have hcr : ∀ u, μ[fun (_ : Ω) => r | 𝓕 u] = fun _ => r := fun u => condExp_const (𝓕.le u) r
  have hfx : ∀ u τ, 0 ≤ u → u ≤ τ → μ[TidyR8OUPresentValue.ouPath W η σ s0 τ | 𝓕 u] =ᵐ[μ]
      ouForecast μ 𝓕 W η σ s0 u τ := fun u τ hu huτ => by
    filter_upwards [condExp_congr_ae (m := 𝓕 u)
      (TidyR8OUPresentValue.ouPath_ae_eq hBM hWm h𝓕 hcont η σ s0 (hu.trans huτ)),
      ou_condExp hBM hWm h𝓕 η σ s0 hu huτ] with x h1 h2
    rw [h1, h2]
    rfl
  have hint : ∀ τ, 0 ≤ τ → Integrable (TidyR8OUPresentValue.ouPath W η σ s0 τ) μ :=
    fun τ hτ => (TidyR8OUPresentValue.integrable_ou hBM hWm h𝓕 η σ s0 τ).congr
      (TidyR8OUPresentValue.ouPath_ae_eq hBM hWm h𝓕 hcont η σ s0 hτ).symm
  exact
    { fcV := fun u _ _ _ => by rw [hc1]
      fcQ := fun u _ _ _ => by rw [hc1]
      fcB := fun u _ _ _ => by rw [hc1]
      fcRn := fun u _ _ _ => by rw [hcr]
      fcInfl := fun u τ hu huτ => by
        have e : (fun x => -TidyR8OUPresentValue.ouPath W η σ s0 τ x) =
            -TidyR8OUPresentValue.ouPath W η σ s0 τ := rfl
        rw [e]
        filter_upwards [condExp_neg (μ := μ) (TidyR8OUPresentValue.ouPath W η σ s0 τ) (𝓕 u),
          hfx u τ hu huτ] with x h1 h2
        rw [h1, Pi.neg_apply, h2]
      fcS := fun u τ hu huτ => by
        have e : (fun x => r + TidyR8OUPresentValue.ouPath W η σ s0 τ x) =
            (fun _ => r) + TidyR8OUPresentValue.ouPath W η σ s0 τ := rfl
        rw [e]
        filter_upwards [condExp_add (m := 𝓕 u) (integrable_const r) (hint τ (hu.trans huτ)),
          hfx u τ hu huτ] with x h1 h2
        rw [h1, Pi.add_apply, hcr, h2]
      path := fun u _ => ae_of_all _ fun x =>
        { flow := fun τ _ => (hasDerivAt_const τ (1 : ℝ)).congr_deriv (by ring)
          bond := fun τ _ => (hasDerivAt_const τ (1 : ℝ)).congr_deriv (by ring)
          value := by ring
          tvcV := tvc_of_bounded (t := u) (K := 1) hr fun _ _ => by simp
          tvcQ := by simp
          intS := integrableOn_forecast hr hrη r (ou μ 𝓕 W η σ s0 u x) u
          intR := (integrableOn_forecast hr hrη 0 (ou μ 𝓕 W η σ s0 u x) u).congr_fun
            (fun τ _ => by simp only [ouForecast]; ring) measurableSet_Ioi
          intN := (integrableOn_zero (s := Set.Ioi u) (μ := volume)).congr_fun
            (fun τ _ => by simp) measurableSet_Ioi }
      value := fun _ _ => ae_of_all _ fun _ => by ring
      adV := fun _ => stronglyMeasurable_const
      adQ := fun _ => stronglyMeasurable_const
      adB := fun _ => stronglyMeasurable_const
      intV := fun _ => integrable_const _
      intQ := fun _ => integrable_const _
      intB := fun _ => integrable_const _ }

/-- **Cochrane (2023), §3.6.3, p. 77, in the economy `fiscalInflation`: the surplus news is
`σ/(r + η) dε`.** For `0 ≤ t₀ ≤ t`, a.s.
`∫_0^∞ e^{−rτ}(F^s̃_t − F^s̃_{t₀})(t+τ)dτ = (σ/(r + η))e^{−ηt}∫_{t₀}^t e^{ηv}dW_v`.
Its right side is that of `TidyR7ItoInnovation.pv_innovation` and
`TidyR8OUPresentValue.pv_revision`. -/
theorem fiscalInflation_surplus_news (hBM : IsPreBrownianReal W μ)
    (hWm : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration μ W 𝓕) {r η : ℝ} (hrη : 0 < r + η)
    (σ s0 : ℝ) {t₀ t : ℝ} (h0 : 0 ≤ t₀) (h : t₀ ≤ t) :
    ∀ᵐ x ∂μ, ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) *
        ((r + ouForecast μ 𝓕 W η σ s0 t (t + τ) x) - (r + ouForecast μ 𝓕 W η σ s0 t₀ (t + τ) x)) =
      σ / (r + η) * Real.exp (-(η * t)) * itoInt μ 𝓕 W (fun v _ => Real.exp (η * v)) t₀ t x := by
  filter_upwards [ou_condExp hBM hWm h𝓕 η σ s0 h0 h, ou_innovation hBM hWm h𝓕 η σ s0 h0 h]
    with x h1 h2
  have e : ∀ τ, Real.exp (-(r * τ)) *
      ((r + ouForecast μ 𝓕 W η σ s0 t (t + τ) x) - (r + ouForecast μ 𝓕 W η σ s0 t₀ (t + τ) x)) =
      Real.exp (-(r * τ)) * (Real.exp (-(η * τ)) *
        (ou μ 𝓕 W η σ s0 t x - μ[ou μ 𝓕 W η σ s0 t | 𝓕 t₀] x)) := fun τ => by
    rw [h1]
    simp only [ouForecast]
    rw [show -(η * (t + τ - t₀)) = -(η * τ) + -(η * (t - t₀)) by ring, Real.exp_add,
      show t + τ - t = τ by ring]
    ring
  simp_rw [e]
  rw [ContinuousLinear.ar1_pv hrη, h2]
  ring

/-- **Cochrane (2023), §3.6.3, p. 77 (non-vacuity): the surplus news of `fiscalInflation` is not
zero.** On the constructed motion `bmPath`, for `σ ≠ 0`, `r > 0`, `r + η > 0`, `0 ≤ t₀ < t`, the
present-value surplus news has positive mean square; by `StochLinearEqm.revision_value` it is
matched one for one by news in discounted real returns (expected inflation), since `v ≡ 1`.
From `TidyR8OUPresentValue.bmPath_pv_revision_pos`. -/
theorem bmPath_fiscalInflation_news_pos {r η : ℝ} (hr : 0 < r) (hrη : 0 < r + η) (s0 : ℝ)
    {σ : ℝ} (hσ : σ ≠ 0) {t₀ t : ℝ} (h0 : 0 ≤ t₀) (h : t₀ < t) :
    0 < ∫ x, (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) *
        ((r + ouForecast gaussSeq bmF bmPath η σ s0 t (t + τ) x)
          - (r + ouForecast gaussSeq bmF bmPath η σ s0 t₀ (t + τ) x))) ^ 2 ∂gaussSeq := by
  have hB := isPreBrownianReal_bmPath
  have hF := bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath
  have hpos := TidyR8OUPresentValue.bmPath_pv_revision_pos hr hrη s0 hσ h0 h
  have e : (fun x => (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) *
        ((r + ouForecast gaussSeq bmF bmPath η σ s0 t (t + τ) x)
          - (r + ouForecast gaussSeq bmF bmPath η σ s0 t₀ (t + τ) x))) ^ 2) =ᵐ[gaussSeq]
      fun x => (gaussSeq[TidyR8OUPresentValue.pvPath bmPath r η σ s0 t | bmF t] x
        - gaussSeq[TidyR8OUPresentValue.pvPath bmPath r η σ s0 t | bmF t₀] x) ^ 2 := by
    filter_upwards [fiscalInflation_surplus_news hB measurable_bmPath hF hrη σ s0 h0 h.le,
      TidyR8OUPresentValue.pv_revision hB measurable_bmPath hF continuous_bmPath hr hrη σ s0 h0
        h.le] with x h1 h2
    rw [h1, h2]
  rw [integral_congr_ae e]
  exact hpos

end Cochrane.Generality.TidyR8StochasticNews
