/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.PriceDuration
import BasicNewKeynesianModel.ShockResponses

/-!
# The baseline calibration

Galí (2015), Chapter 3, pp. 67–68 (and fn. 12, p. 72). Quarterly baseline:
`β = 0.99`, `σ = 1`, `φ = 5`, `α = 1/4`, `ε = 9`, `η = 4`, `θ = 3/4`,
`φ_π = 1.5`, `φ_y = 0.125`, `ρ_v = 0.5`, and `ρ_a = 0.9` for the technology
shock. All facts below are exact rational computations.

## Main results

* `markup_baseline`: `M = ε/(ε − 1) = 9/8`, a 12.5 percent markup.
* `mean_duration_baseline`: the mean price duration is 4 quarters.
* `bigTheta_baseline`, `lambda_baseline`, `kappa_baseline`: `Θ = 1/4`,
  `λ = 103/4800 ≈ 0.0215`, `κ = 103/600 ≈ 0.1717`.
* `bullardMitra_baseline`: condition (28) holds.
* `psiYA_baseline`: `ψ_ya = 1` at `σ = 1` (fn. 12, where it is misprinted as
  `ϕ_ya`, C3-7).
* `monetary_signs_baseline`, `liquidity_effect_baseline`,
  `technology_baseline`, `employment_baseline`: signs and values of the
  response coefficients, including the corrected employment coefficient
  `≈ −0.2564` versus the printed formula's `≈ −0.1923` (C3-3).
-/

namespace Gali.BasicNewKeynesianModel.Calibration

open TaylorRuleSystem ShockResponses

/-- Galí (2015), p. 57: the desired gross markup `M = ε/(ε − 1)`. -/
noncomputable def markup (ε : ℝ) : ℝ := ε / (ε - 1)

/-- Galí (2015), p. 60: `Θ = (1 − α)/(1 − α + α ε)`. -/
noncomputable def bigTheta (α ε : ℝ) : ℝ := (1 - α) / (1 - α + α * ε)

/-- Galí (2015), p. 61: `λ = (1 − θ)(1 − βθ) Θ/θ`. -/
noncomputable def lambdaNK (β θ α ε : ℝ) : ℝ := (1 - θ) * (1 - β * θ) / θ * bigTheta α ε

/-- Galí (2015), p. 63: `κ = λ (σ + (φ + α)/(1 − α))`. -/
noncomputable def kappaNK (β θ σ φ α ε : ℝ) : ℝ := lambdaNK β θ α ε * (σ + (φ + α) / (1 - α))

/-- The baseline value of `κ` (Galí 2015, p. 67). -/
noncomputable def κ₀ : ℝ := kappaNK 0.99 0.75 1 5 0.25 9

/-- The baseline Calvo parameter `θ = 3/4` (Galí 2015, p. 67). -/
noncomputable def baselineCalvo : CalvoParam where
  θ := 3 / 4
  nonneg := by norm_num
  lt_one := by norm_num

/-- Galí (2015), p. 67: with `ε = 9` the desired markup is `M = 9/8 = 1.125`. -/
theorem markup_baseline : markup 9 = 9 / 8 ∧ markup 9 = 1.125 := by
  unfold markup; norm_num

/-- Galí (2015), pp. 67–68: `θ = 3/4` implies an average price duration of
four quarters. -/
theorem mean_duration_baseline :
    ∑' k : ℕ, ((k : ℝ) + 1) * durationProb baselineCalvo.θ k = 4 := by
  rw [baselineCalvo.mean_duration]
  simp only [baselineCalvo]
  norm_num

/-- Galí (2015), p. 67: `β = 0.99` implies a steady-state annualised real
return `β⁻⁴ − 1` of about 4 percent. -/
theorem annual_return_baseline :
    0.041 < (1 / (0.99 : ℝ)) ^ 4 - 1 ∧ (1 / (0.99 : ℝ)) ^ 4 - 1 < 0.0411 := by
  norm_num

/-- Galí (2015), p. 67: `φ = 5` is a Frisch elasticity `1/φ = 0.2`, and the
quarterly output coefficient is `φ_y = 0.5/4 = 0.125`. -/
theorem frisch_and_phiy_baseline : (1 : ℝ) / 5 = 0.2 ∧ (0.5 : ℝ) / 4 = 0.125 := by
  norm_num

/-- Galí (2015), p. 60: at `α = 1/4`, `ε = 9`, `Θ = 1/4`. -/
theorem bigTheta_baseline : bigTheta 0.25 9 = 1 / 4 := by
  unfold bigTheta; norm_num

/-- Galí (2015), p. 61: the baseline `λ = 103/4800 ∈ (0.0214, 0.0215)`. -/
theorem lambda_baseline :
    lambdaNK 0.99 0.75 0.25 9 = 103 / 4800 ∧
      0.0214 < lambdaNK 0.99 0.75 0.25 9 ∧ lambdaNK 0.99 0.75 0.25 9 < 0.0215 := by
  unfold lambdaNK bigTheta; norm_num

/-- Galí (2015), p. 63: the baseline `κ = 103/600 ∈ (0.1716, 0.1717)`. -/
theorem kappa_baseline : κ₀ = 103 / 600 ∧ 0.1716 < κ₀ ∧ κ₀ < 0.1717 := by
  unfold κ₀ kappaNK lambdaNK bigTheta; norm_num

/-- Galí (2015), eq. (28), p. 65: the baseline satisfies the Bullard–Mitra
condition `κ (φ_π − 1) + (1 − β) φ_y > 0`, so the equilibrium is
determinate. -/
theorem bullardMitra_baseline : 0 < κ₀ * (1.5 - 1) + (1 - 0.99) * 0.125 := by
  rw [kappa_baseline.1]; norm_num

/-- Galí (2015), p. 72, fn. 12 (misprinted there as `ϕ_ya`, C3-7):
`ψ_ya = (1 + φ)/(σ (1 − α) + φ + α) = 1` at `σ = 1`, for any `φ`, `α` with
`φ + 1 ≠ 0`; in particular at the baseline. -/
theorem psiYA_one_of_sigma_one {φ α : ℝ} (h : 1 + φ ≠ 0) : DIS.psiYA 1 φ α = 1 := by
  unfold DIS.psiYA
  rw [show 1 * (1 - α) + φ + α = 1 + φ by ring]
  exact div_self h

/-- Galí (2015), p. 72, fn. 12: `ψ_ya = 1` at the baseline. -/
theorem psiYA_baseline : DIS.psiYA 1 5 0.25 = 1 := psiYA_one_of_sigma_one (by norm_num)

/-- Galí (2015), pp. 66–68 (figure 3.1): at the baseline with `ρ_v = 0.5`, a
monetary tightening lowers the output gap and inflation, raises the real rate
and also raises the nominal rate (by less than its exogenous component). -/
theorem monetary_signs_baseline :
    monYgapCoef 0.99 1 κ₀ 1.5 0.125 0.5 < 0 ∧ monInflCoef 0.99 1 κ₀ 1.5 0.125 0.5 < 0 ∧
      0 < monRealCoef 0.99 1 κ₀ 1.5 0.125 0.5 ∧ 0 < monNomCoef 0.99 1 κ₀ 1.5 0.125 0.5 ∧
      monNomCoef 0.99 1 κ₀ 1.5 0.125 0.5 < 1 := by
  rw [kappa_baseline.1]
  unfold monYgapCoef monInflCoef monRealCoef monNomCoef msvLambda msvDen
  norm_num

/-- Galí (2015), p. 68: at the baseline (`η = 4`) the money supply contracts
after a tightening and the model displays a liquidity effect. -/
theorem liquidity_effect_baseline :
    monMoneyCoef 0.99 1 κ₀ 1.5 0.125 0.5 4 < 0 ∧
      monNomCoef 0.99 1 κ₀ 1.5 0.125 0.5 * monMoneyCoef 0.99 1 κ₀ 1.5 0.125 0.5 4 < 0 := by
  rw [kappa_baseline.1]
  unfold monMoneyCoef monNomCoef msvLambda msvDen
  norm_num

/-- Galí (2015), p. 72 (figure 3.3): at the baseline with `ρ_a = 0.9` the
output coefficient `κ (φ_π − ρ_a) Λ_a ≈ 0.808` lies in `(0, 1)`, and the output
gap and inflation fall after a technology improvement. -/
theorem technology_baseline :
    0.807 < techOutputCoef 0.99 1 κ₀ 1.5 0.125 0.9 ∧
      techOutputCoef 0.99 1 κ₀ 1.5 0.125 0.9 < 0.808 ∧
      techYgapCoef 0.99 1 κ₀ 1.5 0.125 0.9 1 < 0 ∧
      techInflCoef 0.99 1 κ₀ 1.5 0.125 0.9 1 < 0 := by
  rw [kappa_baseline.1]
  unfold techOutputCoef techYgapCoef techInflCoef msvLambda msvDen
  norm_num

/-- **Correction C3-3 at the baseline** (Galí 2015, p. 72): the corrected
employment coefficient is `≈ −0.2564`, the printed formula gives `≈ −0.1923`;
both are negative but they differ. -/
theorem employment_baseline :
    -0.2565 < techNCoef 0.99 1 κ₀ 1.5 0.125 0.9 5 0.25 ∧
      techNCoef 0.99 1 κ₀ 1.5 0.125 0.9 5 0.25 < -0.2564 ∧
      -0.1924 < techNCoefPrinted 0.99 1 κ₀ 1.5 0.125 0.9 5 0.25 ∧
      techNCoefPrinted 0.99 1 κ₀ 1.5 0.125 0.9 5 0.25 < -0.1923 ∧
      techNCoef 0.99 1 κ₀ 1.5 0.125 0.9 5 0.25
        ≠ techNCoefPrinted 0.99 1 κ₀ 1.5 0.125 0.9 5 0.25 := by
  rw [kappa_baseline.1]
  unfold techNCoef techNCoefPrinted msvLambda msvDen
  norm_num

end Gali.BasicNewKeynesianModel.Calibration
