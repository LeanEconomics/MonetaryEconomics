/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR7BrownianTools

/-!
# The exponential martingale `exp(σW − σ²t/2)`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.32)–(1.34). A sanity link for the positive stochastic
discount factors of (1.32)–(1.34): the lognormal SDF `exp(σW_t − σ²t/2)` (the canonical positive
diffusive `Λ`) has `E_s[Λ_t/Λ_s] = 1`. Its diffusion coefficient `σΛ` is unbounded, so it is not
an Itô process in the sense of `TidyR7ItoProcess.ItoProcess` (bounded coefficients); the
identity is proved directly from the Gaussian law of the increment (Mathlib `mgf_gaussianReal`)
and its independence of the past (`TidyR7BrownianTools.condExp_fun_increment`).

## Main results

* `integral_exp_increment`: `E[exp(σ(W_t − W_s) − σ²(t − s)/2)] = 1`, `s ≤ t`.
* `condExp_exp_increment` (**the exponential martingale property**):
  `E[exp(σ(W_t − W_s) − σ²(t − s)/2) | 𝓕_s] = 1` a.s.
* `condExp_exp_increment_bmPath`: the instance on the constructed motion.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR9ExpMartingale

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.LongTermDebtDynamics.TidyR7BrownianSchauder
  Cochrane.LongTermDebtDynamics.TidyR7BrownianExist
  Cochrane.LongTermDebtDynamics.TidyR7BrownianTools
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (the lognormal SDF has mean one): for a pre-Brownian
motion and `s ≤ t`, `E[exp(σ(W_t − W_s) − σ²(t − s)/2)] = 1`.
Mathlib `mgf_gaussianReal` at the increment.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ExpMartingale.integral_exp_increment). -/
theorem integral_exp_increment (hB : IsPreBrownianReal W P) {s t : ℝ≥0} (hst : s ≤ t)
    (σ : ℝ) :
    ∫ ω, Real.exp (σ * (W t ω - W s ω) - σ ^ 2 * ((t : ℝ) - s) / 2) ∂P = 1 := by
  have hm := mgf_gaussianReal (hB.hasLaw_sub t s) σ
  rw [coe_nndist_val, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hst))] at hm
  have e : (fun ω => Real.exp (σ * (W t ω - W s ω) - σ ^ 2 * ((t : ℝ) - s) / 2))
      = fun ω => Real.exp (σ * (W t - W s) ω) / Real.exp (σ ^ 2 * ((t : ℝ) - s) / 2) :=
    funext fun ω => by rw [Real.exp_sub]; rfl
  rw [e, integral_div]
  change mgf (W t - W s) P σ / _ = 1
  rw [hm, div_eq_one_iff_eq (Real.exp_pos _).ne']
  congr 1
  ring

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (the exponential martingale): for a pre-Brownian
motion with its natural filtration and `s ≤ t`,
`E[exp(σ(W_t − W_s) − σ²(t − s)/2) | 𝓕_s] = 1` a.s.**, i.e. `Λ_u = exp(σW_u − σ²u/2)` satisfies
`E_s[Λ_t/Λ_s] = 1`.
Uses `TidyR7BrownianTools.condExp_fun_increment`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ExpMartingale.condExp_exp_increment). -/
theorem condExp_exp_increment (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    {s t : ℝ≥0} (hst : s ≤ t) (σ : ℝ) :
    P[fun ω => Real.exp (σ * (W t ω - W s ω) - σ ^ 2 * ((t : ℝ) - s) / 2) | bmFiltration W hW s]
      =ᵐ[P] fun _ => 1 := by
  have h := condExp_fun_increment hB hW hst
    (fun x => Real.exp (σ * x - σ ^ 2 * ((t : ℝ) - s) / 2))
    (by fun_prop)
  rw [integral_exp_increment hB hst σ] at h
  exact h

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (non-vacuity): the exponential martingale property
on the constructed motion `TidyR7BrownianExist.bmPath`, from time `0` to `1`:
`E[exp(σW_1 − σ²/2) | 𝓕_0] = 1` a.s.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ExpMartingale.condExp_exp_increment_bmPath). -/
theorem condExp_exp_increment_bmPath (σ : ℝ) :
    gaussSeq[fun ω => Real.exp (σ * bmPath 1 ω - σ ^ 2 / 2)
      | bmFiltration bmPath measurable_bmPath 0] =ᵐ[gaussSeq] fun _ => 1 := by
  have h := condExp_exp_increment isPreBrownianReal_bmPath measurable_bmPath
    (s := 0) (t := 1) zero_le σ
  have e : (fun ω => Real.exp (σ * (bmPath 1 ω - bmPath 0 ω)
      - σ ^ 2 * (((1 : ℝ≥0) : ℝ) - ((0 : ℝ≥0) : ℝ)) / 2))
      = fun ω => Real.exp (σ * bmPath 1 ω - σ ^ 2 / 2) := funext fun ω => by
    rw [bmPath_zero, NNReal.coe_one, NNReal.coe_zero, sub_zero, sub_zero, mul_one]
  rw [e] at h
  exact h

end Cochrane.LongTermDebtDynamics.TidyR9ExpMartingale
