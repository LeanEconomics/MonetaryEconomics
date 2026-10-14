/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyWagesPrices.LimitingCases

/-!
# Baseline calibration

Galí (2015), Chapter 6, §6.2.1 (pp. 176–177) and §6.5 (pp. 185–187).

The baseline is the Chapter 3 calibration `β = 0.99`, `σ = 1`, `φ = 5`, `α = 1/4`, `ε_p = 9`,
`θ_p = 3/4`, together with `θ_w = 3/4` (p. 176) and `ε_w = 4.5` (p. 177). Exact values:

* `lambdaP_baseline`: `λ_p = 103/4800 ≈ 0.02146`; `lambdaW_baseline`: `λ_w = 103/28200 ≈ 0.00365`.
* `kappaP_baseline`, `kappaW_baseline`: `κ_p = 103/14400`, `κ_w = 2369/84600`.
* `compositeWeight_baseline`: the weight of wage inflation in composite inflation
  `π̄ = (λ_w π^p + λ_p π^w)/(λ_p + λ_w)` is `λ_p/(λ_p + λ_w) = 47/55 ≈ 0.8545` ("0.85", p. 186).
* `gapCoeff_baseline`, `priceWeight_baseline`, `wageWeight_baseline`: the loss weights of (28)
  and (29) are `8`, `43200/103 ≈ 419.4` and `95175/103 ≈ 924.0`.

Table 6.1 (p. 186) reports **simulated** volatilities and losses; the simulation itself is
computational and not formalised. `table61_losses` recomputes the average loss (29) from the
printed standard deviations (in percent; `L` in percent of steady-state consumption) for the
seven technology-shock columns: every recomputed value lies 2–7% **below** the printed one
(e.g. `0.0296` vs `0.0330` for the optimal policy), consistent with truncated standard
deviations (survey item 11, informational, not an error). The recomputed ranking
(`table61_ranking`) agrees with the printed one except that flexible composite and flexible
wage targeting swap places (`table61_flexible_swap`: printed `0.307 > 0.305`, recomputed
`0.288 < 0.295`); the book's text does not rank these two.
-/

namespace Gali.StickyWagesPrices.Calibration

open Gali.StickyWagesPrices.Welfare Gali.StickyWagesPrices.LimitingCases
open Gali.StickyWagesPrices.WageDispersion

/-- Galí (2015), pp. 166 and 176: at the baseline, `λ_p = 103/4800`. -/
theorem lambdaP_baseline : lambdaP 0.99 0.75 0.25 9 = 103 / 4800 := by
  unfold lambdaP bigTheta
  norm_num

/-- Galí (2015), pp. 170 and 177: at the baseline, `λ_w = 103/28200`. -/
theorem lambdaW_baseline : lambdaW 0.99 0.75 5 4.5 = 103 / 28200 := by
  unfold lambdaW
  norm_num

/-- Galí (2015), p. 172: at the baseline, `κ_p = α λ_p/(1 − α) = 103/14400`. -/
theorem kappaP_baseline : kappaP 0.25 (lambdaP 0.99 0.75 0.25 9) = 103 / 14400 := by
  rw [lambdaP_baseline]
  unfold kappaP
  norm_num

/-- Galí (2015), p. 172: at the baseline, `κ_w = λ_w (σ + φ/(1 − α)) = 2369/84600`. -/
theorem kappaW_baseline : kappaW 1 5 0.25 (lambdaW 0.99 0.75 5 4.5) = 2369 / 84600 := by
  rw [lambdaW_baseline]
  unfold kappaW
  norm_num

/-- Galí (2015), p. 186 (**"wage inflation has a weight of 0.85 in composite inflation"**): at
the baseline, `λ_p/(λ_p + λ_w) = 47/55`, which lies in `(0.8545, 0.8546)` and rounds to
`0.85`. -/
theorem compositeWeight_baseline :
    lambdaP 0.99 0.75 0.25 9 / (lambdaP 0.99 0.75 0.25 9 + lambdaW 0.99 0.75 5 4.5) = 47 / 55 ∧
      (0.8545 : ℝ) < 47 / 55 ∧ (47 / 55 : ℝ) < 0.8546 ∧ |(47 / 55 : ℝ) - 0.85| < 0.005 := by
  rw [lambdaP_baseline, lambdaW_baseline]
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  rw [abs_lt]
  constructor <;> norm_num

/-- Galí (2015), p. 186: the weight of price inflation in composite inflation,
`λ_w/(λ_p + λ_w) = 8/55 ≈ 0.145`. -/
theorem compositePriceWeight_baseline :
    lambdaW 0.99 0.75 5 4.5 / (lambdaP 0.99 0.75 0.25 9 + lambdaW 0.99 0.75 5 4.5) = 8 / 55 := by
  rw [lambdaP_baseline, lambdaW_baseline]
  norm_num

/-- Galí (2015), eq. (28), p. 179: at the baseline the output-gap weight is
`σ + (φ + α)/(1 − α) = 8`. -/
theorem gapCoeff_baseline : gapCoeff 1 5 0.25 = 8 := by
  unfold gapCoeff
  norm_num

/-- Galí (2015), eq. (28), p. 179: at the baseline the price-inflation weight is
`ε_p/λ_p = 43200/103 ≈ 419.4`. -/
theorem priceWeight_baseline :
    priceWeight 0.99 0.75 0.25 9 = 43200 / 103 ∧ (419.4 : ℝ) < 43200 / 103 ∧
      (43200 / 103 : ℝ) < 419.5 := by
  unfold priceWeight
  rw [lambdaP_baseline]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- Galí (2015), eq. (28), p. 179: at the baseline the wage-inflation weight is
`ε_w(1 − α)/λ_w = 95175/103 ≈ 924.0`. -/
theorem wageWeight_baseline :
    wageWeight 0.99 0.75 0.25 5 4.5 = 95175 / 103 ∧ (924 : ℝ) < 95175 / 103 ∧
      (95175 / 103 : ℝ) < 924.1 := by
  unfold wageWeight
  rw [lambdaW_baseline]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- Galí (2015), p. 179: at the baseline the wage-inflation weight is more than twice the
price-inflation weight (`924.0` vs `419.4`), even though the composite-inflation weights favour
wage inflation by `47 : 8`. -/
theorem wageWeight_gt_priceWeight_baseline :
    2 * priceWeight 0.99 0.75 0.25 9 < wageWeight 0.99 0.75 0.25 5 4.5 := by
  rw [priceWeight_baseline.1, wageWeight_baseline.1]
  norm_num

/-- Galí (2015), eq. (29), p. 179, in the units of Table 6.1: standard deviations in percent,
loss in percent of steady-state consumption, `L = ½[8 σ(ỹ)² + 419.4 σ(π^p)² + 924.0 σ(π^w)²]/100`
with the exact baseline weights. -/
noncomputable def tableLoss (sdY sdP sdW : ℝ) : ℝ :=
  (gapCoeff 1 5 0.25 * sdY ^ 2 + priceWeight 0.99 0.75 0.25 9 * sdP ^ 2 +
    wageWeight 0.99 0.75 0.25 5 4.5 * sdW ^ 2) / 200

/-- Galí (2015), Table 6.1, p. 186 (technology shocks), **computational record**: the average
loss (29) recomputed from the printed standard deviations, against the printed `L`:
optimal `0.0296` (printed `0.0330`), strict price `0.769` (`0.78`), strict wage `0.0370`
(`0.039`), strict composite `0.0320` (`0.0337`), flexible price `0.449` (`0.47`), flexible wage
`0.295` (`0.305`), flexible composite `0.288` (`0.307`). Every recomputed value is below the
printed one. -/
theorem table61_losses :
    (0.0295 < tableLoss 0.04 0.11 0.03 ∧ tableLoss 0.04 0.11 0.03 < 0.0297) ∧
      (0.769 < tableLoss 3.38 0 0.26 ∧ tableLoss 3.38 0 0.26 < 0.770) ∧
      (0.0370 < tableLoss 0.20 0.13 0 ∧ tableLoss 0.20 0.13 0 < 0.0371) ∧
      (0.0320 < tableLoss 0 0.12 0.02 ∧ tableLoss 0 0.12 0.02 < 0.0321) ∧
      (0.448 < tableLoss 0.84 0.29 0.23 ∧ tableLoss 0.84 0.29 0.23 < 0.450) ∧
      (0.294 < tableLoss 1.18 0.24 0.16 ∧ tableLoss 1.18 0.24 0.16 < 0.295) ∧
      (0.288 < tableLoss 1.11 0.24 0.16 ∧ tableLoss 1.11 0.24 0.16 < 0.289) := by
  unfold tableLoss
  rw [gapCoeff_baseline, priceWeight_baseline.1, wageWeight_baseline.1]
  norm_num

/-- Galí (2015), Table 6.1 and p. 186 (**ranking from the recomputed losses**): optimal <
strict composite < strict wage < flexible composite < flexible wage < flexible price < strict
price. This is the printed order except for the flexible composite/wage pair. -/
theorem table61_ranking :
    tableLoss 0.04 0.11 0.03 < tableLoss 0 0.12 0.02 ∧
      tableLoss 0 0.12 0.02 < tableLoss 0.20 0.13 0 ∧
      tableLoss 0.20 0.13 0 < tableLoss 1.11 0.24 0.16 ∧
      tableLoss 1.11 0.24 0.16 < tableLoss 1.18 0.24 0.16 ∧
      tableLoss 1.18 0.24 0.16 < tableLoss 0.84 0.29 0.23 ∧
      tableLoss 0.84 0.29 0.23 < tableLoss 3.38 0 0.26 := by
  unfold tableLoss
  rw [gapCoeff_baseline, priceWeight_baseline.1, wageWeight_baseline.1]
  norm_num

/-- Galí (2015), Table 6.1, p. 186 (informational): the printed losses rank flexible wage
targeting (`0.305`) above flexible composite targeting (`0.307`), but the losses recomputed
from the printed standard deviations reverse the pair. -/
theorem table61_flexible_swap :
    (0.305 : ℝ) < 0.307 ∧ tableLoss 1.11 0.24 0.16 < tableLoss 1.18 0.24 0.16 := by
  refine ⟨by norm_num, ?_⟩
  unfold tableLoss
  rw [gapCoeff_baseline, priceWeight_baseline.1, wageWeight_baseline.1]
  norm_num

end Gali.StickyWagesPrices.Calibration
