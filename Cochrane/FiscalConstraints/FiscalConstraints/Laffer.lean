/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.ExpIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The present-value Laffer curve

Cochrane (2023), Chapter 6, §6.1 *The present-value Laffer curve*, pp. 187–190.

A flat income tax at rate `τ` on output `y` raises revenue `τ y`. The static Laffer elasticity is
`∂ log(τ y)/∂ log τ = 1 + ∂ log y/∂ log τ` (p. 189). With output growing at rate `g` and
discount rate `r > g`, the present value of revenue is
`PV = ∫₀^∞ e^{-r u} τ y e^{g u} du = τ y/(r - g)` (p. 189), and its elasticity is
`∂ log PV/∂ log τ = 1 + ∂ log y/∂ log τ + (1/(r - g)) ∂g/∂ log τ` (p. 190).

All elasticities are exact derivatives (`HasDerivAt`) with respect to `log τ`, of functions of
`v = log τ` (so `τ = e^v`); the derivative of `g` with respect to `log τ` is `τ g'(τ)`.

## Main results

* `pv_tax_eq`, `pv_tax_not_integrable`: the present value formula, and its genuine divergence
  for `r ≤ g`.
* `static_elasticity`, `output_elasticity`: the static Laffer elasticity (p. 189).
* `pv_elasticity`: the present-value elasticity of the closed form (p. 190), and
  `pv_integral_elasticity`: the same for the improper integral itself.
* `pv_elasticity_zero_of`, `pv_elasticity_nonpos_iff`, `book_top_of_curve`: the top of the
  present-value Laffer curve; with `r - g = 0.01`, `∂g/∂ log τ = -0.01` and no static effect the
  elasticity is exactly zero (p. 190).
* `log_pv_hasDerivAt_g`, `log_pv_hasDerivAt_r`, `semi_elasticity_strictAntiOn`: "r closer to g
  makes the present value more sensitive" (p. 190).
* `log_tax_ratio_bounds`, `book_growth_reduction_bounds` (survey E6.3): a rise of `τ` from 50% to
  60% is a log change of `log 1.2 ∈ (0.18, 0.19)`, not 20%, so the implied growth reduction is
  between 0.18 and 0.19 percentage points rather than 0.2.
-/

namespace Cochrane.FiscalConstraints.Laffer

open Real MeasureTheory Filter Topology
open Cochrane.FiscalConstraints.ExpIntegrals

/-- Cochrane (2023), §6.1, p. 189: the present value of tax revenue
`PV_t = ∫₀^∞ e^{-r u} τ y_t e^{g u} du = τ y_t/(r - g)` when `r > g`. -/
theorem pv_tax_eq {r g : ℝ} (h : g < r) (τ y : ℝ) :
    ∫ u in Set.Ioi (0 : ℝ), exp (-r * u) * (τ * y * exp (g * u)) = τ * y / (r - g) :=
  integral_exp_growth h (τ * y)

/-- Cochrane (2023), §6.1, p. 189: for `r ≤ g` and positive revenue the present value of tax
revenue is infinite (the integrand is not integrable). -/
theorem pv_tax_not_integrable {r g : ℝ} (h : r ≤ g) {τ y : ℝ} (hτy : τ * y ≠ 0) :
    ¬ IntegrableOn (fun u : ℝ => exp (-r * u) * (τ * y * exp (g * u))) (Set.Ioi 0) :=
  not_integrableOn_exp_growth h hτy

/-- Cochrane (2023), §6.1, p. 189: the output elasticity `∂ log y/∂ log τ = τ y'(τ)/y(τ)`, as the
exact derivative of `v ↦ log y(e^v)` at `v = log τ`. -/
theorem output_elasticity {y : ℝ → ℝ} {y' τ : ℝ} (hτ : 0 < τ) (hy : 0 < y τ)
    (hd : HasDerivAt y y' τ) :
    HasDerivAt (fun v => log (y (exp v))) (τ * y' / y τ) (log τ) := by
  have he : exp (log τ) = τ := exp_log hτ
  have h1 : HasDerivAt (fun v => y (exp v)) (y' * τ) (log τ) := by
    have := HasDerivAt.comp (log τ) (he.symm ▸ hd : HasDerivAt y y' (exp (log τ)))
      (hasDerivAt_exp (log τ))
    rwa [he] at this
  have h2 := h1.log (show y (exp (log τ)) ≠ 0 by rw [he]; exact hy.ne')
  refine h2.congr_deriv ?_
  rw [he]
  ring

/-- Cochrane (2023), §6.1, p. 189: the static Laffer elasticity
`∂ log(τ y)/∂ log τ = 1 + ∂ log y/∂ log τ`, as the exact derivative of `v ↦ log(e^v y(e^v))` at
`v = log τ`. -/
theorem static_elasticity {y : ℝ → ℝ} {y' τ : ℝ} (hτ : 0 < τ) (hy : 0 < y τ)
    (hd : HasDerivAt y y' τ) :
    HasDerivAt (fun v => log (exp v * y (exp v))) (1 + τ * y' / y τ) (log τ) := by
  have he : exp (log τ) = τ := exp_log hτ
  have h1 : HasDerivAt (fun v => y (exp v)) (y' * τ) (log τ) := by
    have := HasDerivAt.comp (log τ) (he.symm ▸ hd : HasDerivAt y y' (exp (log τ)))
      (hasDerivAt_exp (log τ))
    rwa [he] at this
  have h2 : HasDerivAt (fun v => exp v * y (exp v)) (τ * y τ + τ * (y' * τ)) (log τ) := by
    have := HasDerivAt.mul (hasDerivAt_exp (log τ)) h1
    rw [he] at this
    exact this
  have h3 := h2.log (show exp (log τ) * y (exp (log τ)) ≠ 0 by
    rw [he]; exact (mul_pos hτ hy).ne')
  refine h3.congr_deriv ?_
  rw [he]
  field_simp

/-- Cochrane (2023), §6.1, p. 190: the elasticity of the present value of tax revenue,
`∂ log PV/∂ log τ = 1 + ∂ log y/∂ log τ + (1/(r - g)) ∂g/∂ log τ`, as the exact derivative of
`v ↦ log(e^v y(e^v)/(r - g(e^v)))` at `v = log τ` (with `∂g/∂ log τ = τ g'(τ)`). -/
theorem pv_elasticity {y g : ℝ → ℝ} {y' g' τ r : ℝ} (hτ : 0 < τ) (hy : 0 < y τ)
    (hr : g τ < r) (hyd : HasDerivAt y y' τ) (hgd : HasDerivAt g g' τ) :
    HasDerivAt (fun v => log (exp v * y (exp v) / (r - g (exp v))))
      (1 + τ * y' / y τ + 1 / (r - g τ) * (τ * g')) (log τ) := by
  have he : exp (log τ) = τ := exp_log hτ
  have h1 : HasDerivAt (fun v => y (exp v)) (y' * τ) (log τ) := by
    have := HasDerivAt.comp (log τ) (he.symm ▸ hyd : HasDerivAt y y' (exp (log τ)))
      (hasDerivAt_exp (log τ))
    rwa [he] at this
  have hg1 : HasDerivAt (fun v => g (exp v)) (g' * τ) (log τ) := by
    have := HasDerivAt.comp (log τ) (he.symm ▸ hgd : HasDerivAt g g' (exp (log τ)))
      (hasDerivAt_exp (log τ))
    rwa [he] at this
  have h2 : HasDerivAt (fun v => exp v * y (exp v)) (τ * y τ + τ * (y' * τ)) (log τ) := by
    have := HasDerivAt.mul (hasDerivAt_exp (log τ)) h1
    rw [he] at this
    exact this
  have hden : HasDerivAt (fun v => r - g (exp v)) (-(g' * τ)) (log τ) := by
    simpa using hg1.const_sub r
  have hrg : r - g (exp (log τ)) ≠ 0 := by rw [he]; linarith
  have h3 := HasDerivAt.div h2 hden hrg
  have hpos : exp (log τ) * y (exp (log τ)) / (r - g (exp (log τ))) ≠ 0 := by
    rw [he]; exact (div_pos (mul_pos hτ hy) (by linarith)).ne'
  have h4 := h3.log hpos
  refine h4.congr_deriv ?_
  have hrg' : r - g τ ≠ 0 := by linarith
  simp only [Pi.div_apply, he]
  field_simp
  ring

/-- Cochrane (2023), §6.1, pp. 189–190: the present-value elasticity holds for the improper
integral `PV(τ) = ∫₀^∞ e^{-r u} τ y(τ) e^{g(τ) u} du` itself: `v ↦ log PV(e^v)` has derivative
`1 + ∂ log y/∂ log τ + (1/(r - g)) ∂g/∂ log τ` at `log τ` (the closed form holds near `τ` by
continuity of `g`). -/
theorem pv_integral_elasticity {y g : ℝ → ℝ} {y' g' τ r : ℝ} (hτ : 0 < τ) (hy : 0 < y τ)
    (hr : g τ < r) (hyd : HasDerivAt y y' τ) (hgd : HasDerivAt g g' τ) :
    HasDerivAt (fun v => log (∫ u in Set.Ioi (0 : ℝ),
        exp (-r * u) * (exp v * y (exp v) * exp (g (exp v) * u))))
      (1 + τ * y' / y τ + 1 / (r - g τ) * (τ * g')) (log τ) := by
  refine (pv_elasticity hτ hy hr hyd hgd).congr_of_eventuallyEq ?_
  have hc : ContinuousAt (fun v => g (exp v)) (log τ) := by
    have : ContinuousAt g (exp (log τ)) := by rw [exp_log hτ]; exact hgd.continuousAt
    exact this.comp (continuous_exp.continuousAt)
  have hev : ∀ᶠ v in 𝓝 (log τ), g (exp v) < r := by
    apply hc.eventually (gt_mem_nhds _)
    change g (exp (log τ)) < r
    rw [exp_log hτ]; exact hr
  filter_upwards [hev] with v hv
  rw [pv_tax_eq hv]

/-- Cochrane (2023), §6.1, p. 190: with no static effect (`∂ log y/∂ log τ = 0`) and
`∂g/∂ log τ = -(r - g)`, the present-value elasticity is exactly zero: the top of the present-value
Laffer curve. -/
theorem pv_elasticity_zero_of {r g dg : ℝ} (hrg : g < r) (hdg : dg = -(r - g)) :
    1 + 0 + 1 / (r - g) * dg = 0 := by
  have : r - g ≠ 0 := by linarith
  rw [hdg]
  field_simp
  ring

/-- Cochrane (2023), §6.1, p. 190: the present-value elasticity
`1 + ε_y + (1/(r - g)) ∂g/∂ log τ` is nonpositive (we are at or beyond the top of the
present-value Laffer curve) iff `∂g/∂ log τ ≤ -(r - g)(1 + ε_y)`. -/
theorem pv_elasticity_nonpos_iff {r g εy dg : ℝ} (hrg : g < r) :
    1 + εy + 1 / (r - g) * dg ≤ 0 ↔ dg ≤ -(r - g) * (1 + εy) := by
  have hpos : 0 < r - g := by linarith
  have key : 1 + εy + 1 / (r - g) * dg = (dg + (r - g) * (1 + εy)) / (r - g) := by
    field_simp
    ring
  rw [key, div_nonpos_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · linarith
    · linarith
  · intro h
    right
    exact ⟨by linarith, hpos.le⟩

/-- Cochrane (2023), §6.1, p. 190: the book's example: `r - g = 0.01` and
`dg/d log τ = -0.01` put us at the top of the present-value Laffer curve with no static effect. -/
theorem book_top_of_curve : (1 : ℝ) + 0 + 1 / (0.01 : ℝ) * (-0.01) = 0 := by
  norm_num

/-- Cochrane (2023), §6.1, p. 190: the semi-elasticity of the present value `c/(r - g)` with
respect to `g` is `1/(r - g)`: exact derivative of `g ↦ log(c/(r - g))`. -/
theorem log_pv_hasDerivAt_g {c r g : ℝ} (hc : 0 < c) (hrg : g < r) :
    HasDerivAt (fun h => log (c / (r - h))) (1 / (r - g)) g := by
  have hd : HasDerivAt (fun h => r - h) (-1) g := by simpa using (hasDerivAt_id g).const_sub r
  have h1 := (HasDerivAt.div (hasDerivAt_const g c) hd (by linarith : r - g ≠ 0)).log
    (div_pos hc (by linarith)).ne'
  convert h1 using 1
  have : r - g ≠ 0 := by linarith
  simp only [Pi.div_apply]
  field_simp
  ring

/-- Cochrane (2023), §6.1, p. 190: the semi-elasticity of the present value `c/(r - g)` with
respect to `r` is `-1/(r - g)`. -/
theorem log_pv_hasDerivAt_r {c r g : ℝ} (hc : 0 < c) (hrg : g < r) :
    HasDerivAt (fun q => log (c / (q - g))) (-(1 / (r - g))) r := by
  have hd : HasDerivAt (fun q => q - g) 1 r := by simpa using (hasDerivAt_id r).sub_const g
  have h1 := (HasDerivAt.div (hasDerivAt_const r c) hd (by linarith : r - g ≠ 0)).log
    (div_pos hc (by linarith)).ne'
  convert h1 using 1
  have : r - g ≠ 0 := by linarith
  simp only [Pi.div_apply]
  field_simp
  ring

/-- Cochrane (2023), §6.1, p. 190: "r closer to g makes the present value more sensitive": the
semi-elasticity `1/(r - g)` is strictly decreasing in the spread `r - g > 0`. -/
theorem semi_elasticity_strictAntiOn :
    StrictAntiOn (fun d : ℝ => 1 / d) (Set.Ioi 0) := by
  intro a ha b _ hab
  exact one_div_lt_one_div_of_lt ha hab

/-- Cochrane (2023), §6.1, p. 190 (survey E6.3): a tax-rate rise from 50% to 60% is a log change
`log(0.6/0.5) = log 1.2` with `0.18 < log 1.2 < 0.19`, not the 20% used in the text. -/
theorem log_tax_ratio_bounds :
    (0.18 : ℝ) < log (0.6 / 0.5) ∧ log (0.6 / 0.5) < 0.19 := by
  have h12 : (0.6 : ℝ) / 0.5 = 1.2 := by norm_num
  rw [h12]
  constructor
  · rw [lt_log_iff_exp_lt (by norm_num)]
    have hb := Real.exp_bound (x := 0.18) (by norm_num [abs_of_pos]) (n := 3) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
    norm_num at hb
    have := (abs_le.1 hb).2
    linarith
  · rw [log_lt_iff_lt_exp (by norm_num)]
    have := Real.quadratic_le_exp_of_nonneg (x := 0.19) (by norm_num)
    linarith

/-- Cochrane (2023), §6.1, p. 190 (survey E6.3): with `dg/d log τ = -0.01`, the growth reduction
implied by the tax-rate rise from 50% to 60% is `0.01 · log 1.2`, strictly between 0.18 and
0.19 percentage points (the book's "0.2 percentage point" uses the 20% arithmetic change). -/
theorem book_growth_reduction_bounds :
    (0.0018 : ℝ) < 0.01 * log (0.6 / 0.5) ∧ 0.01 * log (0.6 / 0.5) < 0.0019 ∧
      0.01 * log (0.6 / 0.5) ≠ (0.002 : ℝ) := by
  obtain ⟨h1, h2⟩ := log_tax_ratio_bounds
  refine ⟨by linarith, by linarith, by intro h; linarith⟩

end Cochrane.FiscalConstraints.Laffer
