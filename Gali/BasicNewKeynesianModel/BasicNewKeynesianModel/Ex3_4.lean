/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.Expectations
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Exercise 3.4: indexation and the New Keynesian Phillips curve

Galí (2015), Chapter 3, Exercise 3.4 (pp. 91–92). Between reoptimisations a firm indexes its
price, `P_{t+k|t} = P_{t+k−1|t} Π_{t+k−1}^ω Π^{1−ω}` (`ω ∈ [0, 1]`, `Π` steady-state gross
inflation), so a price set at `t` is `P*_t X_{t,k}` at `t + k`, with
`X_{t,k} = ∏_{j<k} Π_{t+j}^ω Π^{1−ω}`. Technology is constant returns (nominal marginal cost
`Ψ_{t+k}` independent of the firm's output) and demand is `Y_{t+k|t} = (P_{t+k|t}/P_{t+k})^{−ε}
C_{t+k}`. A reoptimising firm maximises
`∑_k θᵏ E_t{Λ_{t,t+k}(1/P_{t+k})(P_{t+k|t} Y_{t+k|t} − Ψ_{t+k} Y_{t+k|t})}`.

## Main results

* (a) `dist_law_of_motion`, `integral_indexed_mix`, `indexed_recursion`: the exact law of
  motion `Π_t^{1−ε} = θ (Π_{t−1}^ω Π^{1−ω})^{1−ε} + (1 − θ)(P*_t/P_{t−1})^{1−ε}`;
  `log_infl_eq_inflFn`, `inflFn_ss`, `hasFDerivAt_inflFn`: its exact first-order form
  `π̂_t = θω π̂_{t−1} + (1 − θ)(p*_t − p_{t−1} − π)`.
* (b) `objective_eq`, `hasDerivAt_objective`: the objective is
  `x^{1−ε} A_t − x^{−ε} B_t` and its derivative is `((1 − ε)/x)` times the book-form
  first-order condition `∑ θᵏ E_t{Λ Y_{t+k|t} (P*_t X_{t,k} − M Ψ_{t+k})/P_{t+k}}`;
  `foc_iff`: the FOC holds iff `P*_t = M B_t/A_t`; `isMaxOn_iff_foc`: a price maximises the
  objective **iff** it satisfies the FOC (sufficiency via Bernoulli's inequality).
* (c) `hasDerivAt_logResetPrice`, `logResetPrice_zero`, `resetPrice_isMaxOn_iff`: along any
  perturbation of the stochastic environment around the steady state, the log of the optimal
  reset price is differentiable with derivative
  `(1 − βθ) ∑ (βθ)ᵏ E_t{ψ̂_{t+k} − ω ∑_{j<k} π̂_{t+j}}`, i.e. the log-linear rule
  `p*_t = μ + (1 − βθ) ∑ (βθ)ᵏ E_t{ψ_{t+k} − ω ∑_{j<k} π̂_{t+j}}` (up to the steady-state path).
* (d) `hybrid_nkpc`: (a) and (c) imply
  `π̂_t = γ_b π̂_{t−1} + γ_f E_t π̂_{t+1} − λ̃ μ̂_t` with `γ_b = ω/(1 + βω)`,
  `γ_f = β/(1 + βω)`, `λ̃ = λ/(1 + βω)`, `λ = (1 − θ)(1 − βθ)/θ`; `rule_of_hybrid_nkpc`: the
  converse (given (a), the hybrid NKPC implies the rule (c)), so (c) ⟺ (d) under (a).
-/

namespace Gali.BasicNewKeynesianModel.Ex3_4

open MeasureTheory Filter Topology

/-! ### (a) The price index under indexation -/

namespace PriceIndex

/-- Galí (2015), Ex. 3.4(a), p. 91: the CES price index of a price distribution `ν`,
`P = (∫ p^{1−ε} dν)^{1/(1−ε)}`. -/
noncomputable def priceIdx (ν : Measure ℝ) (ε : ℝ) : ℝ := (∫ x, x ^ (1 - ε) ∂ν) ^ (1 - ε)⁻¹

/-- Galí (2015), Ex. 3.4(a), p. 91 (**law of motion of the price distribution**). Firms
`(F, m)`; those in `S` (mass `1 − θ`) reset to `P*`, the others index their price,
`p_t(i) = I p_{t−1}(i)` with `I = Π_{t−1}^ω Π^{1−ω}`; the non-resetters are a representative
subsample (their price distribution is `θ` times the full one). Then
`ν_t = θ (I · ν_{t−1}) + (1 − θ) δ_{P*}`. -/
theorem dist_law_of_motion {F : Type*} [MeasurableSpace F] (m : Measure F) {θ I : ℝ}
    {S : Set F} (hS : MeasurableSet S) {pprev pnow : F → ℝ} (hprev : Measurable pprev)
    (hnow : Measurable pnow) {Pstar : ℝ} (hreset : ∀ i ∈ S, pnow i = Pstar)
    (hkeep : ∀ i ∉ S, pnow i = I * pprev i) (hmass : m S = ENNReal.ofReal (1 - θ))
    (hind : (m.restrict Sᶜ).map pprev = ENNReal.ofReal θ • m.map pprev) :
    m.map pnow = ENNReal.ofReal θ • (m.map pprev).map (fun x => I * x) +
      ENNReal.ofReal (1 - θ) • Measure.dirac Pstar := by
  conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := m) hS]
  rw [Measure.map_add _ _ hnow]
  have h1 : (m.restrict S).map pnow = ENNReal.ofReal (1 - θ) • Measure.dirac Pstar := by
    rw [Measure.map_congr (g := fun _ => Pstar) ((ae_restrict_iff' hS).2
      (Filter.Eventually.of_forall hreset)), Measure.map_const, Measure.restrict_apply_univ,
      hmass]
  have h2 : (m.restrict Sᶜ).map pnow = ((m.restrict Sᶜ).map pprev).map (fun x => I * x) := by
    rw [Measure.map_map (measurable_const_mul I) hprev]
    exact Measure.map_congr ((ae_restrict_iff' hS.compl).2 (Filter.Eventually.of_forall hkeep))
  rw [h1, h2, hind, Measure.map_smul, add_comm]
  exact (measurable_const_mul I).aemeasurable

/-- Galí (2015), Ex. 3.4(a), p. 91: integrating `p^{1−ε}` against the indexed Calvo mixture
gives `θ I^{1−ε} ∫ p^{1−ε} dν + (1 − θ) P*^{1−ε}`. -/
theorem integral_indexed_mix {ν : Measure ℝ} {θ I ε : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hI : 0 < I)
    (Pstar : ℝ) (hnn : ∀ᵐ x ∂ν, 0 ≤ x) (hint : Integrable (fun x : ℝ => x ^ (1 - ε)) ν) :
    ∫ x, x ^ (1 - ε) ∂(ENNReal.ofReal θ • ν.map (fun x => I * x) +
        ENNReal.ofReal (1 - θ) • Measure.dirac Pstar)
      = θ * (I ^ (1 - ε) * ∫ x, x ^ (1 - ε) ∂ν) + (1 - θ) * Pstar ^ (1 - ε) := by
  have hmeas : Measurable fun x : ℝ => x ^ (1 - ε) := measurable_id.pow_const _
  have hae : (fun x : ℝ => (I * x) ^ (1 - ε)) =ᵐ[ν] fun x => I ^ (1 - ε) * x ^ (1 - ε) := by
    filter_upwards [hnn] with x hx
    rw [Real.mul_rpow hI.le hx]
  have hcomp : Integrable ((fun x : ℝ => x ^ (1 - ε)) ∘ fun x => I * x) ν :=
    (hint.const_mul (I ^ (1 - ε))).congr hae.symm
  have hmap : Integrable (fun x : ℝ => x ^ (1 - ε)) (ν.map fun x => I * x) :=
    (integrable_map_measure hmeas.aestronglyMeasurable
      (measurable_const_mul I).aemeasurable).2 hcomp
  have hd : Integrable (fun x : ℝ => x ^ (1 - ε)) (Measure.dirac Pstar) :=
    integrable_dirac (by simp)
  rw [integral_add_measure (hmap.smul_measure ENNReal.ofReal_ne_top)
      (hd.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul, smul_eq_mul,
    integral_map (measurable_const_mul I).aemeasurable hmeas.aestronglyMeasurable,
    integral_congr_ae hae, integral_const_mul]

/-- Galí (2015), Ex. 3.4(a), p. 91 (**exact inflation dynamics under indexation**): if
`ν_t = θ (I · ν_{t−1}) + (1 − θ) δ_{P*}` with `I = Π_{t−1}^ω Π^{1−ω}`, then with
`P_s` the price index of `ν_s`,
`(P_t/P_{t−1})^{1−ε} = θ I^{1−ε} + (1 − θ)(P*/P_{t−1})^{1−ε}`. -/
theorem indexed_recursion {ε θ I : ℝ} (hε : 1 < ε) (h0 : 0 ≤ θ) (h1 : θ < 1) (hI : 0 < I)
    {νprev : Measure ℝ} {Pstar : ℝ} (hPstar : 0 < Pstar) (hnn : ∀ᵐ x ∂νprev, 0 ≤ x)
    (hint : Integrable (fun x : ℝ => x ^ (1 - ε)) νprev)
    (hpos : 0 < ∫ x, x ^ (1 - ε) ∂νprev) :
    (priceIdx (ENNReal.ofReal θ • νprev.map (fun x => I * x) +
        ENNReal.ofReal (1 - θ) • Measure.dirac Pstar) ε / priceIdx νprev ε) ^ (1 - ε)
      = θ * I ^ (1 - ε) + (1 - θ) * (Pstar / priceIdx νprev ε) ^ (1 - ε) := by
  have hmix := integral_indexed_mix h0 h1.le hI Pstar hnn hint
  have hnew : 0 < θ * (I ^ (1 - ε) * ∫ x, x ^ (1 - ε) ∂νprev) + (1 - θ) * Pstar ^ (1 - ε) := by
    have : 0 < (1 - θ) * Pstar ^ (1 - ε) :=
      mul_pos (by linarith) (Real.rpow_pos_of_pos hPstar _)
    have : 0 ≤ θ * (I ^ (1 - ε) * ∫ x, x ^ (1 - ε) ∂νprev) :=
      mul_nonneg h0 (mul_nonneg (Real.rpow_nonneg hI.le _) hpos.le)
    linarith
  have hsub : (1 : ℝ) - ε ≠ 0 := by linarith
  have hIp : 0 < priceIdx νprev ε := Real.rpow_pos_of_pos hpos _
  have hIp' : priceIdx νprev ε ^ (1 - ε) = ∫ x, x ^ (1 - ε) ∂νprev :=
    Real.rpow_inv_rpow hpos.le hsub
  have hPt : priceIdx (ENNReal.ofReal θ • νprev.map (fun x => I * x) +
      ENNReal.ofReal (1 - θ) • Measure.dirac Pstar) ε ^ (1 - ε)
      = θ * (I ^ (1 - ε) * ∫ x, x ^ (1 - ε) ∂νprev) + (1 - θ) * Pstar ^ (1 - ε) := by
    unfold priceIdx
    rw [hmix, Real.rpow_inv_rpow hnew.le hsub]
  have hPt0 : 0 ≤ priceIdx (ENNReal.ofReal θ • νprev.map (fun x => I * x) +
      ENNReal.ofReal (1 - θ) • Measure.dirac Pstar) ε := by
    unfold priceIdx
    rw [hmix]
    exact Real.rpow_nonneg hnew.le _
  rw [Real.div_rpow hPt0 hIp.le, Real.div_rpow hPstar.le hIp.le, hPt, hIp']
  field_simp

/-- Galí (2015), Ex. 3.4(a), p. 91: log gross inflation as a function of last period's log
gross inflation `v.1` and the log relative reset price `v.2 = log(P*_t/P_{t−1})`:
`(1 − ε)⁻¹ log(θ e^{(1−ε)(ω v.1 + (1−ω)π)} + (1 − θ) e^{(1−ε) v.2})`, `π = log Π`. -/
noncomputable def inflFn (θ ε ω πbar : ℝ) (v : ℝ × ℝ) : ℝ :=
  (1 - ε)⁻¹ * Real.log (θ * Real.exp ((1 - ε) * (ω * v.1 + (1 - ω) * πbar)) +
    (1 - θ) * Real.exp ((1 - ε) * v.2))

/-- Galí (2015), Ex. 3.4(a), p. 91: the exact recursion says
`log Π_t = inflFn (log Π_{t−1}, log(P*_t/P_{t−1}))`. -/
theorem log_infl_eq_inflFn {θ ε ω Pi Piprev Pibar x : ℝ} (hε : ε ≠ 1) (hPi : 0 < Pi)
    (hprev : 0 < Piprev) (hbar : 0 < Pibar) (hx : 0 < x)
    (hrec : Pi ^ (1 - ε) = θ * (Piprev ^ ω * Pibar ^ (1 - ω)) ^ (1 - ε) + (1 - θ) * x ^ (1 - ε)) :
    Real.log Pi = inflFn θ ε ω (Real.log Pibar) (Real.log Piprev, Real.log x) := by
  have hsub : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have hI : 0 < Piprev ^ ω * Pibar ^ (1 - ω) :=
    mul_pos (Real.rpow_pos_of_pos hprev _) (Real.rpow_pos_of_pos hbar _)
  have hlogI : Real.log (Piprev ^ ω * Pibar ^ (1 - ω))
      = ω * Real.log Piprev + (1 - ω) * Real.log Pibar := by
    rw [Real.log_mul (Real.rpow_pos_of_pos hprev _).ne' (Real.rpow_pos_of_pos hbar _).ne',
      Real.log_rpow hprev, Real.log_rpow hbar]
  have h := congrArg Real.log hrec
  rw [Real.log_rpow hPi, Real.rpow_def_of_pos hI, Real.rpow_def_of_pos hx, hlogI,
    mul_comm (_ + _) (1 - ε), mul_comm (Real.log x)] at h
  rw [inflFn, ← h]
  field_simp

/-- Galí (2015), Ex. 3.4(a), p. 91: at the steady state (`Π_{t−1} = Π`, `P*_t/P_{t−1} = Π`)
inflation is at its steady-state value: `inflFn (π, π) = π`. -/
theorem inflFn_ss (θ : ℝ) {ε : ℝ} (hε : ε ≠ 1) (ω πbar : ℝ) :
    inflFn θ ε ω πbar (πbar, πbar) = πbar := by
  have hsub : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have e : θ * Real.exp ((1 - ε) * (ω * πbar + (1 - ω) * πbar)) +
      (1 - θ) * Real.exp ((1 - ε) * πbar) = Real.exp ((1 - ε) * πbar) := by
    rw [show ω * πbar + (1 - ω) * πbar = πbar by ring]
    ring
  rw [inflFn, e, Real.log_exp]
  field_simp

/-- Galí (2015), Ex. 3.4(a), p. 91 (**exact first-order inflation equation**): at the steady
state `(π, π)` the Fréchet derivative of `inflFn` is `(θω, 1 − θ)`, i.e.
`π̂_t = θω π̂_{t−1} + (1 − θ)(p*_t − p_{t−1} − π)` to first order. -/
theorem hasFDerivAt_inflFn (θ : ℝ) {ε : ℝ} (hε : ε ≠ 1) (ω πbar : ℝ) :
    HasFDerivAt (inflFn θ ε ω πbar)
      ((θ * ω) • ContinuousLinearMap.fst ℝ ℝ ℝ + (1 - θ) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (πbar, πbar) := by
  have hsub : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have hf := hasFDerivAt_fst (𝕜 := ℝ) (p := (πbar, πbar))
  have hs := hasFDerivAt_snd (𝕜 := ℝ) (p := (πbar, πbar))
  have h1 := HasFDerivAt.exp (HasFDerivAt.const_mul (HasFDerivAt.const_add
    ((1 - ω) * πbar) (HasFDerivAt.const_mul hf ω)) (1 - ε))
  have h2 := HasFDerivAt.exp (HasFDerivAt.const_mul hs (1 - ε))
  have hsum := HasFDerivAt.add (HasFDerivAt.const_mul h1 θ) (HasFDerivAt.const_mul h2 (1 - θ))
  have hne : (fun v : ℝ × ℝ => θ * Real.exp ((1 - ε) * ((1 - ω) * πbar + ω * v.1)) +
      (1 - θ) * Real.exp ((1 - ε) * v.2)) (πbar, πbar) ≠ 0 := by
    have : (1 - ω) * πbar + ω * πbar = πbar := by ring
    simp only [this]
    rw [← add_mul, add_sub_cancel, one_mul]
    exact (Real.exp_pos _).ne'
  have h := HasFDerivAt.const_mul (HasFDerivAt.log hsum hne) (1 - ε)⁻¹
  have hfun : inflFn θ ε ω πbar = fun v : ℝ × ℝ => (1 - ε)⁻¹ * Real.log
      (θ * Real.exp ((1 - ε) * ((1 - ω) * πbar + ω * v.1)) +
        (1 - θ) * Real.exp ((1 - ε) * v.2)) := by
    funext v
    rw [inflFn, add_comm (ω * v.1)]
  rw [hfun]
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  have : (1 - ω) * πbar + ω * πbar = πbar := by ring
  simp only [smul_apply, add_apply, Pi.add_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul, this]
  have hden : θ * Real.exp ((1 - ε) * πbar) + (1 - θ) * Real.exp ((1 - ε) * πbar)
      = Real.exp ((1 - ε) * πbar) := by ring
  rw [hden]
  have hE : Real.exp ((1 - ε) * πbar) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

end PriceIndex

/-! ### (b) The reset-price problem and its first-order condition -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), p. 57: the desired gross markup `M = ε/(ε − 1)`. -/
noncomputable def markup (ε : ℝ) : ℝ := ε / (ε - 1)

/-- Galí (2015), Ex. 3.4, p. 91, with eq. (9), p. 56: the demand for a firm whose price at
`t + k` is `x X_{t,k}`, `Y_{t+k|t} = (x X/P)^{−ε} C`. -/
noncomputable def demand (ε x : ℝ) (X P C : Ω → ℝ) : Ω → ℝ := fun ζ => (x * X ζ / P ζ) ^ (-ε) * C ζ

/-- Galí (2015), Ex. 3.4, p. 91: real profit at `t + k` discounted by `Λ`, with constant
returns (`C(Y) = Ψ Y`): `Λ (x X Y − Ψ Y)/P`. -/
noncomputable def profit (ε x : ℝ) (Λ X P C Ψ : Ω → ℝ) : Ω → ℝ :=
  fun ζ => Λ ζ * (x * X ζ * demand ε x X P C ζ - Ψ ζ * demand ε x X P C ζ) / P ζ

/-- Galí (2015), Ex. 3.4, p. 91: the reoptimising firm's objective at date `t` as a function
of its reset price `x = P*_t`, `∑_k θᵏ E_t{profit_k}`. Its arguments are indexed by the
horizon `k`: `Λ k = Λ_{t,t+k}`, `X k = X_{t,k}`, `P k = P_{t+k}`, `C k = C_{t+k}`,
`Ψ k = Ψ_{t+k}`. -/
noncomputable def objective (θ ε : ℝ) (t : ℕ) (Λ X P C Ψ : ℕ → Ω → ℝ) (x : ℝ) : Ω → ℝ :=
  fun ζ => ∑' k, θ ^ k * 𝔼.E t (profit ε x (Λ k) (X k) (P k) (C k) (Ψ k)) ζ

/-- Galí (2015), Ex. 3.4(b), p. 92: the revenue factor `Λ X^{1−ε} P^{ε−1} C`. -/
noncomputable def revFactor (ε : ℝ) (Λ X P C : Ω → ℝ) : Ω → ℝ :=
  fun ζ => Λ ζ * X ζ ^ (1 - ε) * P ζ ^ (ε - 1) * C ζ

/-- Galí (2015), Ex. 3.4(b), p. 92: the cost factor `Λ Ψ X^{−ε} P^{ε−1} C`. -/
noncomputable def costFactor (ε : ℝ) (Λ X P C Ψ : Ω → ℝ) : Ω → ℝ :=
  fun ζ => Λ ζ * Ψ ζ * X ζ ^ (-ε) * P ζ ^ (ε - 1) * C ζ

/-- Galí (2015), Ex. 3.4(b), p. 92: `A_t = ∑ θᵏ E_t{Λ X^{1−ε} P^{ε−1} C}`. -/
noncomputable def sumA (θ ε : ℝ) (t : ℕ) (Λ X P C : ℕ → Ω → ℝ) : Ω → ℝ :=
  fun ζ => ∑' k, θ ^ k * 𝔼.E t (revFactor ε (Λ k) (X k) (P k) (C k)) ζ

/-- Galí (2015), Ex. 3.4(b), p. 92: `B_t = ∑ θᵏ E_t{Λ Ψ X^{−ε} P^{ε−1} C}`. -/
noncomputable def sumB (θ ε : ℝ) (t : ℕ) (Λ X P C Ψ : ℕ → Ω → ℝ) : Ω → ℝ :=
  fun ζ => ∑' k, θ ^ k * 𝔼.E t (costFactor ε (Λ k) (X k) (P k) (C k) (Ψ k)) ζ

/-- Galí (2015), Ex. 3.4(b), p. 92: the book-form first-order condition,
`∑ θᵏ E_t{Λ_{t,t+k} Y_{t+k|t} (P*_t X_{t,k} − M Ψ_{t+k})/P_{t+k}}`. -/
noncomputable def focSum (θ ε : ℝ) (t : ℕ) (Λ X P C Ψ : ℕ → Ω → ℝ) (x : ℝ) : Ω → ℝ :=
  fun ζ => ∑' k, θ ^ k * 𝔼.E t (fun ζ' => Λ k ζ' * demand ε x (X k) (P k) (C k) ζ' *
    (x * X k ζ' - markup ε * Ψ k ζ') / P k ζ') ζ

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(b), p. 92: demand in factored form,
`(x X/P)^{−ε} C = x^{−ε} X^{−ε} P^ε C`. -/
theorem demand_eq {ε x : ℝ} (hx : 0 < x) {X P C : Ω → ℝ} (hX : ∀ ζ, 0 < X ζ)
    (hP : ∀ ζ, 0 < P ζ) (ζ : Ω) :
    demand ε x X P C ζ = x ^ (-ε) * X ζ ^ (-ε) * P ζ ^ ε * C ζ := by
  have hX' := hX ζ
  have hP' := hP ζ
  rw [demand, Real.div_rpow (by positivity) hP'.le, Real.mul_rpow hx.le hX'.le,
    Real.rpow_neg hP'.le ε, div_inv_eq_mul]

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(b), p. 92: profit is `x^{1−ε}` times the revenue factor minus
`x^{−ε}` times the cost factor. -/
theorem profit_eq {ε x : ℝ} (hx : 0 < x) {Λ X P C Ψ : Ω → ℝ} (hX : ∀ ζ, 0 < X ζ)
    (hP : ∀ ζ, 0 < P ζ) :
    profit ε x Λ X P C Ψ =
      x ^ (1 - ε) • revFactor ε Λ X P C - x ^ (-ε) • costFactor ε Λ X P C Ψ := by
  funext ζ
  have hX' := hX ζ
  have hP' := hP ζ
  have e1 : x ^ (1 - ε) = x * x ^ (-ε) := by rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_one]
  have e2 : X ζ ^ (1 - ε) = X ζ * X ζ ^ (-ε) := by
    rw [sub_eq_add_neg, Real.rpow_add hX', Real.rpow_one]
  have e3 : P ζ ^ (ε - 1) = P ζ ^ ε / P ζ := Real.rpow_sub_one hP'.ne' ε
  simp only [profit, revFactor, costFactor, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [demand_eq hx hX hP, e1, e2, e3]
  field_simp

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(b), p. 92: the FOC integrand in factored form,
`Λ Y (x X − M Ψ)/P = x^{−ε}(x · revFactor − M · costFactor)`. -/
theorem focTerm_eq {ε x : ℝ} (hx : 0 < x) {Λ X P C Ψ : Ω → ℝ} (hX : ∀ ζ, 0 < X ζ)
    (hP : ∀ ζ, 0 < P ζ) :
    (fun ζ' => Λ ζ' * demand ε x X P C ζ' * (x * X ζ' - markup ε * Ψ ζ') / P ζ')
      = x ^ (-ε) • (x • revFactor ε Λ X P C - markup ε • costFactor ε Λ X P C Ψ) := by
  funext ζ
  have hX' := hX ζ
  have hP' := hP ζ
  have e2 : X ζ ^ (1 - ε) = X ζ * X ζ ^ (-ε) := by
    rw [sub_eq_add_neg, Real.rpow_add hX', Real.rpow_one]
  have e3 : P ζ ^ (ε - 1) = P ζ ^ ε / P ζ := Real.rpow_sub_one hP'.ne' ε
  simp only [revFactor, costFactor, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [demand_eq hx hX hP, e2, e3]
  field_simp

/-- Galí (2015), Ex. 3.4(b), p. 92: the objective is `x^{1−ε} A_t − x^{−ε} B_t` (the series
`A_t`, `B_t` being summable at the state considered). -/
theorem objective_eq {θ ε x : ℝ} (hx : 0 < x) {t : ℕ} {Λ X P C Ψ : ℕ → Ω → ℝ}
    (hX : ∀ k ζ, 0 < X k ζ) (hP : ∀ k ζ, 0 < P k ζ) {ζ : Ω}
    (hsA : Summable fun k => θ ^ k * 𝔼.E t (revFactor ε (Λ k) (X k) (P k) (C k)) ζ)
    (hsB : Summable fun k => θ ^ k * 𝔼.E t (costFactor ε (Λ k) (X k) (P k) (C k) (Ψ k)) ζ) :
    objective 𝔼 θ ε t Λ X P C Ψ x ζ
      = x ^ (1 - ε) * sumA 𝔼 θ ε t Λ X P C ζ - x ^ (-ε) * sumB 𝔼 θ ε t Λ X P C Ψ ζ := by
  unfold objective sumA sumB
  have hterm : ∀ k, θ ^ k * 𝔼.E t (profit ε x (Λ k) (X k) (P k) (C k) (Ψ k)) ζ
      = x ^ (1 - ε) * (θ ^ k * 𝔼.E t (revFactor ε (Λ k) (X k) (P k) (C k)) ζ) -
        x ^ (-ε) * (θ ^ k * 𝔼.E t (costFactor ε (Λ k) (X k) (P k) (C k) (Ψ k)) ζ) := by
    intro k
    rw [profit_eq hx (hX k) (hP k), map_sub, map_smul, map_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hterm]
  rw [(hsA.mul_left _).tsum_sub (hsB.mul_left _), tsum_mul_left, tsum_mul_left]

/-- Galí (2015), Ex. 3.4(b), p. 92: the FOC sum is `x^{−ε}(x A_t − M B_t)`. -/
theorem focSum_eq {θ ε x : ℝ} (hx : 0 < x) {t : ℕ} {Λ X P C Ψ : ℕ → Ω → ℝ}
    (hX : ∀ k ζ, 0 < X k ζ) (hP : ∀ k ζ, 0 < P k ζ) {ζ : Ω}
    (hsA : Summable fun k => θ ^ k * 𝔼.E t (revFactor ε (Λ k) (X k) (P k) (C k)) ζ)
    (hsB : Summable fun k => θ ^ k * 𝔼.E t (costFactor ε (Λ k) (X k) (P k) (C k) (Ψ k)) ζ) :
    focSum 𝔼 θ ε t Λ X P C Ψ x ζ
      = x ^ (-ε) * (x * sumA 𝔼 θ ε t Λ X P C ζ - markup ε * sumB 𝔼 θ ε t Λ X P C Ψ ζ) := by
  unfold focSum sumA sumB
  have hterm : ∀ k, θ ^ k * 𝔼.E t (fun ζ' => Λ k ζ' * demand ε x (X k) (P k) (C k) ζ' *
      (x * X k ζ' - markup ε * Ψ k ζ') / P k ζ') ζ
      = x ^ (-ε) * x * (θ ^ k * 𝔼.E t (revFactor ε (Λ k) (X k) (P k) (C k)) ζ) -
        x ^ (-ε) * markup ε *
          (θ ^ k * 𝔼.E t (costFactor ε (Λ k) (X k) (P k) (C k) (Ψ k)) ζ) := by
    intro k
    rw [focTerm_eq hx (hX k) (hP k), map_smul, map_sub, map_smul, map_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hterm]
  rw [(hsA.mul_left _).tsum_sub (hsB.mul_left _), tsum_mul_left, tsum_mul_left]
  ring

/-- Galí (2015), Ex. 3.4(b), p. 92: **the first-order condition**. The objective has
derivative `((1 − ε)/x) · ∑ θᵏ E_t{Λ Y_{t+k|t}(P*_t X_{t,k} − M Ψ_{t+k})/P_{t+k}}` at every
`x = P*_t > 0`. -/
theorem hasDerivAt_objective {θ ε x : ℝ} (hx : 0 < x) {t : ℕ} {Λ X P C Ψ : ℕ → Ω → ℝ}
    (hε : 1 < ε) (hX : ∀ k ζ, 0 < X k ζ) (hP : ∀ k ζ, 0 < P k ζ) {ζ : Ω}
    (hsA : Summable fun k => θ ^ k * 𝔼.E t (revFactor ε (Λ k) (X k) (P k) (C k)) ζ)
    (hsB : Summable fun k => θ ^ k * 𝔼.E t (costFactor ε (Λ k) (X k) (P k) (C k) (Ψ k)) ζ) :
    HasDerivAt (fun y => objective 𝔼 θ ε t Λ X P C Ψ y ζ)
      ((1 - ε) / x * focSum 𝔼 θ ε t Λ X P C Ψ x ζ) x := by
  set A := sumA 𝔼 θ ε t Λ X P C ζ
  set B := sumB 𝔼 θ ε t Λ X P C Ψ ζ
  have h1 : HasDerivAt (fun y : ℝ => y ^ (1 - ε)) ((1 - ε) * x ^ (1 - ε - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have h2 : HasDerivAt (fun y : ℝ => y ^ (-ε)) (-ε * x ^ (-ε - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have h := HasDerivAt.sub (HasDerivAt.mul_const h1 A) (HasDerivAt.mul_const h2 B)
  have heq : (fun y => objective 𝔼 θ ε t Λ X P C Ψ y ζ) =ᶠ[𝓝 x]
      fun y => y ^ (1 - ε) * A - y ^ (-ε) * B := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact objective_eq 𝔼 hy hX hP hsA hsB
  refine (h.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [focSum_eq 𝔼 hx hX hP hsA hsB, markup]
  have e1 : x ^ (1 - ε - 1) = x ^ (-ε) := by ring_nf
  have e2 : x ^ (-ε - 1) = x ^ (-ε) / x := Real.rpow_sub_one hx.ne' (-ε)
  rw [e1, e2]
  have hε1 : ε - 1 ≠ 0 := by linarith
  field_simp
  ring

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(b), p. 92: the FOC `x A − M B = 0` holds iff `x = M B/A`. -/
theorem foc_iff_closed {ε x A B : ℝ} (hx : 0 < x) (hA : 0 < A) :
    x ^ (-ε) * (x * A - markup ε * B) = 0 ↔ x = markup ε * B / A := by
  rw [mul_eq_zero, eq_div_iff hA.ne']
  constructor
  · rintro (h | h)
    · exact absurd h (Real.rpow_pos_of_pos hx _).ne'
    · linarith
  · intro h
    right
    linarith

/-- Galí (2015), Ex. 3.4(b), p. 92: **the FOC pins down the reset price**:
`∑ θᵏ E_t{Λ Y (P*_t X − M Ψ)/P} = 0` iff `P*_t = M B_t/A_t`. -/
theorem foc_iff {θ ε x : ℝ} (hx : 0 < x) {t : ℕ} {Λ X P C Ψ : ℕ → Ω → ℝ}
    (hX : ∀ k ζ, 0 < X k ζ) (hP : ∀ k ζ, 0 < P k ζ) {ζ : Ω}
    (hsA : Summable fun k => θ ^ k * 𝔼.E t (revFactor ε (Λ k) (X k) (P k) (C k)) ζ)
    (hsB : Summable fun k => θ ^ k * 𝔼.E t (costFactor ε (Λ k) (X k) (P k) (C k) (Ψ k)) ζ)
    (hA : 0 < sumA 𝔼 θ ε t Λ X P C ζ) :
    focSum 𝔼 θ ε t Λ X P C Ψ x ζ = 0 ↔
      x = markup ε * sumB 𝔼 θ ε t Λ X P C Ψ ζ / sumA 𝔼 θ ε t Λ X P C ζ := by
  rw [focSum_eq 𝔼 hx hX hP hsA hsB]
  exact foc_iff_closed hx hA

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(b), p. 92: the profit function `y^{1−ε} A − y^{−ε} B` (`A, B > 0`,
`ε > 1`) is maximised on `(0, ∞)` at `x = M B/A`; the proof is Bernoulli's inequality
`r^ε ≥ 1 + ε (r − 1)` for `r = y/x`. -/
theorem value_le_at_closed {ε A B x y : ℝ} (hε : 1 < ε) (hA : 0 < A) (hB : 0 < B)
    (hx : x = markup ε * B / A) (hy : 0 < y) :
    y ^ (1 - ε) * A - y ^ (-ε) * B ≤ x ^ (1 - ε) * A - x ^ (-ε) * B := by
  have hε1 : ε - 1 ≠ 0 := by linarith
  have hxpos : 0 < x := by
    rw [hx, markup]
    have : 0 < ε / (ε - 1) := div_pos (by linarith) (by linarith)
    positivity
  set r := y / x with hr_def
  have hr : 0 < r := div_pos hy hxpos
  have hy' : y = r * x := by rw [hr_def]; field_simp
  have hb := one_add_mul_self_le_rpow_one_add (s := r - 1) (by linarith) (p := ε) hε.le
  rw [add_sub_cancel] at hb
  have hrr : r ^ (-ε) * r ^ ε = 1 := by rw [← Real.rpow_add hr]; simp
  have hk : r ^ (-ε) * (1 + ε * (r - 1)) ≤ 1 := by
    calc r ^ (-ε) * (1 + ε * (r - 1)) ≤ r ^ (-ε) * r ^ ε :=
          mul_le_mul_of_nonneg_left hb (Real.rpow_pos_of_pos hr _).le
      _ = 1 := hrr
  rw [hy', Real.mul_rpow hr.le hxpos.le, Real.mul_rpow hr.le hxpos.le]
  have e1 : r ^ (1 - ε) = r * r ^ (-ε) := by rw [sub_eq_add_neg, Real.rpow_add hr, Real.rpow_one]
  have e2 : x ^ (1 - ε) = x * x ^ (-ε) := by
    rw [sub_eq_add_neg, Real.rpow_add hxpos, Real.rpow_one]
  rw [e1, e2]
  have hxA : x * A = ε * (ε - 1)⁻¹ * B := by rw [hx, markup]; field_simp
  have hinv : (ε - 1) * (ε - 1)⁻¹ = 1 := mul_inv_cancel₀ hε1
  have hdiff : x * x ^ (-ε) * A - x ^ (-ε) * B -
      (r * r ^ (-ε) * (x * x ^ (-ε)) * A - r ^ (-ε) * x ^ (-ε) * B)
      = x ^ (-ε) * B * (ε - 1)⁻¹ * (1 - r ^ (-ε) * (1 + ε * (r - 1))) := by
    linear_combination (x ^ (-ε) * (1 - r * r ^ (-ε))) * hxA +
      x ^ (-ε) * B * (1 - r ^ (-ε)) * hinv
  have hpos : 0 ≤ x ^ (-ε) * B * (ε - 1)⁻¹ * (1 - r ^ (-ε) * (1 + ε * (r - 1))) := by
    have : 0 < (ε - 1)⁻¹ := inv_pos.mpr (by linarith)
    have : 0 < x ^ (-ε) := Real.rpow_pos_of_pos hxpos _
    have : 0 ≤ 1 - r ^ (-ε) * (1 + ε * (r - 1)) := by linarith
    positivity
  linarith

/-- Galí (2015), Ex. 3.4(b), p. 92: **optimality ⟺ the first-order condition**. With
`A_t, B_t > 0` (summable), a reset price `x > 0` maximises the objective over all positive
prices if and only if it satisfies the FOC. -/
theorem isMaxOn_iff_foc {θ ε x : ℝ} (hε : 1 < ε) (hx : 0 < x) {t : ℕ}
    {Λ X P C Ψ : ℕ → Ω → ℝ} (hX : ∀ k ζ, 0 < X k ζ) (hP : ∀ k ζ, 0 < P k ζ) {ζ : Ω}
    (hsA : Summable fun k => θ ^ k * 𝔼.E t (revFactor ε (Λ k) (X k) (P k) (C k)) ζ)
    (hsB : Summable fun k => θ ^ k * 𝔼.E t (costFactor ε (Λ k) (X k) (P k) (C k) (Ψ k)) ζ)
    (hA : 0 < sumA 𝔼 θ ε t Λ X P C ζ) (hB : 0 < sumB 𝔼 θ ε t Λ X P C Ψ ζ) :
    IsMaxOn (fun y => objective 𝔼 θ ε t Λ X P C Ψ y ζ) (Set.Ioi 0) x ↔
      focSum 𝔼 θ ε t Λ X P C Ψ x ζ = 0 := by
  constructor
  · intro hmax
    have hloc : IsLocalMax (fun y => objective 𝔼 θ ε t Λ X P C Ψ y ζ) x :=
      hmax.isLocalMax (Ioi_mem_nhds hx)
    have h0 := hloc.hasDerivAt_eq_zero (hasDerivAt_objective 𝔼 hx hε hX hP hsA hsB)
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h (div_ne_zero (by linarith) hx.ne')
    · exact h
  · intro hfoc y hy
    have hxc := (foc_iff 𝔼 hx hX hP hsA hsB hA).1 hfoc
    change objective 𝔼 θ ε t Λ X P C Ψ y ζ ≤ objective 𝔼 θ ε t Λ X P C Ψ x ζ
    rw [objective_eq 𝔼 hy hX hP hsA hsB, objective_eq 𝔼 hx hX hP hsA hsB]
    exact value_le_at_closed hε hA hB hxc hy

/-! ### (c) Log-linearising the optimal reset price -/

/-- Galí (2015), Ex. 3.4(c), p. 92 (**differentiation under `E_t`**): if `z` is a bounded
random variable, `r ↦ E_t[e^{r z}]` has derivative `E_t[z e^{r z}]` at every `s`. The proof uses
only the axioms of `ExpectationSystem` (linearity, monotonicity, constants): the second-order
remainder is bounded uniformly in the state. -/
theorem hasDerivAt_E_exp {z : Ω → ℝ} {B : ℝ} (hz : ∀ ζ, |z ζ| ≤ B) (t : ℕ) (ζ : Ω) (s : ℝ) :
    HasDerivAt (fun r => 𝔼.E t (fun ζ' => Real.exp (r * z ζ')) ζ)
      (𝔼.E t (fun ζ' => z ζ' * Real.exp (s * z ζ')) ζ) s := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun h => 𝔼.E t (fun ζ' => Real.exp ((s + h) * z ζ')) ζ -
      𝔼.E t (fun ζ' => Real.exp (s * z ζ')) ζ -
        h • 𝔼.E t (fun ζ' => z ζ' * Real.exp (s * z ζ')) ζ) =O[𝓝 0] fun h : ℝ => h ^ 2 := by
    refine Asymptotics.IsBigO.of_bound (Real.exp (|s| * |B|) * |B| ^ 2) ?_
    have hev : ∀ᶠ h in 𝓝 (0 : ℝ), |h| * |B| ≤ 1 := by
      have hc : Tendsto (fun h : ℝ => |h| * |B|) (𝓝 0) (𝓝 0) := by
        have := (continuous_abs.tendsto (0 : ℝ)).mul_const |B|
        simpa using this
      exact hc (Iic_mem_nhds one_pos)
    filter_upwards [hev] with h hh
    have hfun : (fun ζ' => Real.exp (s * z ζ') * (Real.exp (h * z ζ') - 1 - h * z ζ'))
        = (fun ζ' => Real.exp ((s + h) * z ζ')) - (fun ζ' => Real.exp (s * z ζ')) -
          h • (fun ζ' => z ζ' * Real.exp (s * z ζ')) := by
      funext ζ'
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [add_mul, Real.exp_add]
      ring
    have key : 𝔼.E t (fun ζ' => Real.exp ((s + h) * z ζ')) ζ -
        𝔼.E t (fun ζ' => Real.exp (s * z ζ')) ζ -
          h • 𝔼.E t (fun ζ' => z ζ' * Real.exp (s * z ζ')) ζ
        = 𝔼.E t (fun ζ' => Real.exp (s * z ζ') * (Real.exp (h * z ζ') - 1 - h * z ζ')) ζ := by
      rw [hfun, map_sub, map_sub, map_smul]
      rfl
    rw [key, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, sq_abs]
    refine 𝔼.abs_E_le (fun ζ' => ?_) t ζ
    have hzB : |z ζ'| ≤ |B| := (hz ζ').trans (le_abs_self B)
    have hhz : |h * z ζ'| ≤ 1 := by
      rw [abs_mul]
      calc |h| * |z ζ'| ≤ |h| * |B| := mul_le_mul_of_nonneg_left hzB (abs_nonneg h)
        _ ≤ 1 := hh
    have e1 := Real.abs_exp_sub_one_sub_id_le hhz
    have e2 : |Real.exp (s * z ζ')| ≤ Real.exp (|s| * |B|) := by
      rw [Real.abs_exp]
      apply Real.exp_le_exp.mpr
      calc s * z ζ' ≤ |s * z ζ'| := le_abs_self _
        _ = |s| * |z ζ'| := abs_mul _ _
        _ ≤ |s| * |B| := mul_le_mul_of_nonneg_left hzB (abs_nonneg s)
    have e3 : (h * z ζ') ^ 2 ≤ |B| ^ 2 * h ^ 2 := by
      rw [mul_pow, mul_comm]
      have : z ζ' ^ 2 ≤ |B| ^ 2 := by
        rw [← sq_abs (z ζ')]
        exact pow_le_pow_left₀ (abs_nonneg _) hzB 2
      exact mul_le_mul_of_nonneg_right this (sq_nonneg h)
    rw [abs_mul]
    calc |Real.exp (s * z ζ')| * |Real.exp (h * z ζ') - 1 - h * z ζ'|
        ≤ Real.exp (|s| * |B|) * (|B| ^ 2 * h ^ 2) :=
          mul_le_mul e2 (e1.trans e3) (abs_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (|s| * |B|) * B ^ 2 * |h| ^ 2 := by rw [sq_abs B, sq_abs h]; ring
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two)

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(c), p. 92: `∑ (k + 1) qᵏ < ∞` for `0 ≤ q < 1` (deviations of the
indexation factor grow linearly with the horizon). -/
theorem summable_succ_mul_geom {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) :
    Summable fun k : ℕ => ((k : ℝ) + 1) * q ^ k := by
  have hn : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg h0]
  have hA := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have hB := summable_geometric_of_lt_one h0 h1
  refine (hA.add hB).congr fun k => ?_
  simp only [pow_one]
  ring

/-- Galí (2015), Ex. 3.4(c), p. 92: the discounted sum `∑ aᵏ E_t[e^{s zₖ}]`. -/
noncomputable def expSum (a : ℝ) (t : ℕ) (z : ℕ → Ω → ℝ) (s : ℝ) (ζ : Ω) : ℝ :=
  ∑' k, a ^ k * 𝔼.E t (fun ζ' => Real.exp (s * z k ζ')) ζ

/-- Galí (2015), Ex. 3.4(c), p. 92: a radius on which the perturbed sums converge,
`log(2/(1 + a))/(K + 1)`. -/
noncomputable def radius (a K : ℝ) : ℝ := Real.log (2 / (1 + a)) / (K + 1)

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(c), p. 92: the radius is positive. -/
theorem radius_pos {a K : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) (hK : 0 ≤ K) : 0 < radius a K := by
  unfold radius
  have : 1 < 2 / (1 + a) := by rw [one_lt_div (by linarith)]; linarith
  exact div_pos (Real.log_pos this) (by linarith)

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(c), p. 92: inside the radius, `e^{|s| K} ≤ 2/(1 + a)`. -/
theorem exp_le_of_lt_radius {a K s : ℝ} (h0 : 0 ≤ a) (hK : 0 ≤ K) (hs : |s| < radius a K) :
    Real.exp (|s| * K) ≤ 2 / (1 + a) := by
  have hpos : 0 < 2 / (1 + a) := div_pos two_pos (by linarith)
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  have hr : |s| * (K + 1) ≤ Real.log (2 / (1 + a)) := by
    have := (lt_div_iff₀ (by linarith : (0 : ℝ) < K + 1)).1 hs
    linarith
  nlinarith [abs_nonneg s]

/-- Galí (2015), Ex. 3.4(c), p. 92: `|E_t[z e^{s z}]| ≤ B e^{|s| B}` for `|z| ≤ B`. -/
theorem abs_E_mul_exp_le {z : Ω → ℝ} {B : ℝ} (hz : ∀ ζ, |z ζ| ≤ B) (t : ℕ) (s : ℝ) (ζ : Ω) :
    |𝔼.E t (fun ζ' => z ζ' * Real.exp (s * z ζ')) ζ| ≤ B * Real.exp (|s| * B) := by
  refine 𝔼.abs_E_le (fun ζ' => ?_) t ζ
  rw [abs_mul, Real.abs_exp]
  have hB : 0 ≤ B := (abs_nonneg _).trans (hz ζ')
  refine mul_le_mul (hz ζ') (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hB
  calc s * z ζ' ≤ |s * z ζ'| := le_abs_self _
    _ = |s| * |z ζ'| := abs_mul _ _
    _ ≤ |s| * B := mul_le_mul_of_nonneg_left (hz ζ') (abs_nonneg s)

/-- Galí (2015), Ex. 3.4(c), p. 92: `e^{−|s| B} ≤ E_t[e^{s z}] ≤ e^{|s| B}` for `|z| ≤ B`. -/
theorem E_exp_bounds {z : Ω → ℝ} {B : ℝ} (hz : ∀ ζ, |z ζ| ≤ B) (t : ℕ) (s : ℝ) (ζ : Ω) :
    Real.exp (-(|s| * B)) ≤ 𝔼.E t (fun ζ' => Real.exp (s * z ζ')) ζ ∧
      𝔼.E t (fun ζ' => Real.exp (s * z ζ')) ζ ≤ Real.exp (|s| * B) := by
  have hb : ∀ ζ', |s * z ζ'| ≤ |s| * B := fun ζ' => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hz ζ') (abs_nonneg s)
  have hlo : (fun _ => Real.exp (-(|s| * B))) ≤ fun ζ' => Real.exp (s * z ζ') := fun ζ' =>
    Real.exp_le_exp.mpr (by linarith [neg_abs_le (s * z ζ'), hb ζ'])
  have hhi : (fun ζ' => Real.exp (s * z ζ')) ≤ fun _ => Real.exp (|s| * B) := fun ζ' =>
    Real.exp_le_exp.mpr (by linarith [le_abs_self (s * z ζ'), hb ζ'])
  have h1 := 𝔼.mono t hlo ζ
  have h2 := 𝔼.mono t hhi ζ
  rw [𝔼.const] at h1 h2
  exact ⟨h1, h2⟩

/-- Galí (2015), Ex. 3.4(c), p. 92: inside the radius, the terms of `expSum` are dominated by
`(2/(1 + a)) (2a/(1 + a))ᵏ`, so the series converges and is positive. -/
theorem expSum_summable_pos {a K s : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) (hK : 0 ≤ K)
    {z : ℕ → Ω → ℝ} (hz : ∀ k ζ, |z k ζ| ≤ K * (k + 1)) (hs : |s| < radius a K) (t : ℕ)
    (ζ : Ω) : Summable (fun k => a ^ k * 𝔼.E t (fun ζ' => Real.exp (s * z k ζ')) ζ) ∧
      0 < expSum 𝔼 a t z s ζ := by
  set c := 2 / (1 + a) with hc
  have hc0 : 0 < c := div_pos two_pos (by linarith)
  have hac : a * c < 1 := by rw [hc, mul_div_assoc', div_lt_one (by linarith)]; linarith
  have hexp := exp_le_of_lt_radius h0 hK hs
  have hbd : ∀ k, |a ^ k * 𝔼.E t (fun ζ' => Real.exp (s * z k ζ')) ζ| ≤ c * (a * c) ^ k := by
    intro k
    have hb := (E_exp_bounds 𝔼 (hz k) t s ζ).2
    have hpos := (E_exp_bounds 𝔼 (hz k) t s ζ).1
    have hE0 : 0 ≤ 𝔼.E t (fun ζ' => Real.exp (s * z k ζ')) ζ := (Real.exp_pos _).le.trans hpos
    rw [abs_mul, abs_of_nonneg (pow_nonneg h0 k), abs_of_nonneg hE0]
    have hpow : Real.exp (|s| * (K * (k + 1))) ≤ c ^ (k + 1) := by
      rw [show |s| * (K * (k + 1)) = ((k + 1 : ℕ) : ℝ) * (|s| * K) by push_cast; ring,
        Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos _).le hexp _
    calc a ^ k * 𝔼.E t (fun ζ' => Real.exp (s * z k ζ')) ζ ≤ a ^ k * c ^ (k + 1) :=
          mul_le_mul_of_nonneg_left (hb.trans hpow) (pow_nonneg h0 k)
      _ = c * (a * c) ^ k := by ring
  have hsum : Summable (fun k => a ^ k * 𝔼.E t (fun ζ' => Real.exp (s * z k ζ')) ζ) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one (by positivity) hac).mul_left c)
      fun k => by rw [Real.norm_eq_abs]; exact hbd k
  refine ⟨hsum, ?_⟩
  unfold expSum
  refine hsum.tsum_pos (fun k => ?_) 0 ?_
  · exact mul_nonneg (pow_nonneg h0 k)
      ((Real.exp_pos _).le.trans (E_exp_bounds 𝔼 (hz k) t s ζ).1)
  · simp only [pow_zero, one_mul]
    exact (Real.exp_pos _).trans_le (E_exp_bounds 𝔼 (hz 0) t s ζ).1

/-- Galí (2015), Ex. 3.4(c), p. 92: at `s = 0` the sum is `∑ aᵏ = 1/(1 − a)`. -/
theorem expSum_zero {a : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) (t : ℕ) (z : ℕ → Ω → ℝ) (ζ : Ω) :
    expSum 𝔼 a t z 0 ζ = (1 - a)⁻¹ := by
  unfold expSum
  simp only [zero_mul, Real.exp_zero, 𝔼.const, mul_one]
  exact tsum_geometric_of_lt_one h0 h1

/-- Galí (2015), Ex. 3.4(c), p. 92 (**term-by-term differentiation**): for `|zₖ| ≤ K(k + 1)`,
`s ↦ ∑ aᵏ E_t[e^{s zₖ}]` has derivative `∑ aᵏ E_t[zₖ]` at `s = 0`. -/
theorem hasDerivAt_expSum {a K : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) (hK : 0 ≤ K)
    {z : ℕ → Ω → ℝ} (hz : ∀ k ζ, |z k ζ| ≤ K * (k + 1)) (t : ℕ) (ζ : Ω) :
    HasDerivAt (fun s => expSum 𝔼 a t z s ζ) (∑' k, a ^ k * 𝔼.E t (z k) ζ) 0 := by
  set r := radius a K
  have hr := radius_pos h0 h1 hK
  set c := 2 / (1 + a) with hc
  have hc0 : 0 < c := div_pos two_pos (by linarith)
  have hac : a * c < 1 := by rw [hc, mul_div_assoc', div_lt_one (by linarith)]; linarith
  set u : ℕ → ℝ := fun k => K * c * (((k : ℝ) + 1) * (a * c) ^ k)
  have hu : Summable u := (summable_succ_mul_geom (by positivity) hac).mul_left (K * c)
  have hmem0 : (0 : ℝ) ∈ Set.Ioo (-r) r := ⟨by linarith, hr⟩
  have hd := hasDerivAt_tsum_of_isPreconnected (g := fun k s => a ^ k *
      𝔼.E t (fun ζ' => Real.exp (s * z k ζ')) ζ)
    (g' := fun k s => a ^ k * 𝔼.E t (fun ζ' => z k ζ' * Real.exp (s * z k ζ')) ζ)
    (t := Set.Ioo (-r) r) (y₀ := 0) hu isOpen_Ioo isPreconnected_Ioo
    (fun k y _ => (hasDerivAt_E_exp 𝔼 (hz k) t ζ y).const_mul (a ^ k))
    (fun k y hy => ?_) hmem0 ?_ hmem0
  · refine hd.congr_deriv (tsum_congr fun k => ?_)
    simp only [zero_mul, Real.exp_zero, mul_one]
  · have hy' : |y| < r := abs_lt.mpr ⟨hy.1, hy.2⟩
    have hexp := exp_le_of_lt_radius h0 hK hy'
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h0 k)]
    have hb := abs_E_mul_exp_le 𝔼 (hz k) t y ζ
    have hpow : Real.exp (|y| * (K * (k + 1))) ≤ c ^ (k + 1) := by
      rw [show |y| * (K * (k + 1)) = ((k + 1 : ℕ) : ℝ) * (|y| * K) by push_cast; ring,
        Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos _).le hexp _
    calc a ^ k * |𝔼.E t (fun ζ' => z k ζ' * Real.exp (y * z k ζ')) ζ|
        ≤ a ^ k * (K * (k + 1) * c ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left hpow (by positivity)))
            (pow_nonneg h0 k)
      _ = u k := by simp only [u]; ring
  · simp only [zero_mul, Real.exp_zero, 𝔼.const, mul_one]
    exact summable_geometric_of_lt_one h0 h1

/-- Galí (2015), Ex. 3.4(c), p. 92: the series `∑ aᵏ E_t zₖ` converges for `|zₖ| ≤ K(k+1)`. -/
theorem summable_E_lin {a K : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) {z : ℕ → Ω → ℝ}
    (hz : ∀ k ζ, |z k ζ| ≤ K * (k + 1)) (t : ℕ) (ζ : Ω) :
    Summable fun k => a ^ k * 𝔼.E t (z k) ζ := by
  refine Summable.of_norm_bounded ((summable_succ_mul_geom h0 h1).mul_left K) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h0 k)]
  calc a ^ k * |𝔼.E t (z k) ζ| ≤ a ^ k * (K * (k + 1)) :=
        mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hz k) t ζ) (pow_nonneg h0 k)
    _ = K * (((k : ℝ) + 1) * a ^ k) := by ring

/-- Galí (2015), Ex. 3.4(c), p. 92: **the log ratio of two perturbed sums**:
`d/ds [log ∑ aᵏ E_t e^{s z^b_k} − log ∑ aᵏ E_t e^{s z^a_k}]` at `0` equals
`(1 − a) ∑ aᵏ (E_t z^b_k − E_t z^a_k)`. -/
theorem hasDerivAt_logRatio {a K : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) (hK : 0 ≤ K)
    {za zb : ℕ → Ω → ℝ} (hza : ∀ k ζ, |za k ζ| ≤ K * (k + 1))
    (hzb : ∀ k ζ, |zb k ζ| ≤ K * (k + 1)) (t : ℕ) (ζ : Ω) :
    HasDerivAt (fun s => Real.log (expSum 𝔼 a t zb s ζ) - Real.log (expSum 𝔼 a t za s ζ))
      ((1 - a) * ∑' k, a ^ k * (𝔼.E t (zb k) ζ - 𝔼.E t (za k) ζ)) 0 := by
  have hne : (1 - a)⁻¹ ≠ 0 := inv_ne_zero (by linarith)
  have hA := HasDerivAt.log (hasDerivAt_expSum 𝔼 h0 h1 hK hza t ζ)
    (by rw [expSum_zero 𝔼 h0 h1]; exact hne)
  have hB := HasDerivAt.log (hasDerivAt_expSum 𝔼 h0 h1 hK hzb t ζ)
    (by rw [expSum_zero 𝔼 h0 h1]; exact hne)
  refine (HasDerivAt.sub hB hA).congr_deriv ?_
  rw [expSum_zero 𝔼 h0 h1, expSum_zero 𝔼 h0 h1]
  have hs : ∑' k, a ^ k * (𝔼.E t (zb k) ζ - 𝔼.E t (za k) ζ)
      = ∑' k, a ^ k * 𝔼.E t (zb k) ζ - ∑' k, a ^ k * 𝔼.E t (za k) ζ := by
    rw [← (summable_E_lin 𝔼 h0 h1 hzb t ζ).tsum_sub (summable_E_lin 𝔼 h0 h1 hza t ζ)]
    exact tsum_congr fun k => by ring
  rw [hs]
  have h1a : (1 : ℝ) - a ≠ 0 := by linarith
  field_simp

/-! #### The model along a perturbation path -/

/-- Galí (2015), Ex. 3.4(c), p. 92: steady-state parameters. `β` discount factor, `θ` Calvo
parameter, `ε` elasticity, `ω` indexation, `πbar = log Π` steady-state inflation, and the
date-`t` steady-state logs `pbar` (price level), `cbar` (consumption), `ψbar` (nominal
marginal cost). Along the steady state `P_{t+k} = e^{pbar + kπ}`, `Ψ_{t+k} = e^{ψbar + kπ}`,
`C_{t+k} = e^{cbar}`, `Λ_{t,t+k} = βᵏ`. -/
structure SteadyState where
  β : ℝ
  θ : ℝ
  ε : ℝ
  ω : ℝ
  πbar : ℝ
  pbar : ℝ
  cbar : ℝ
  ψbar : ℝ

variable (Ω) in
/-- Galí (2015), Ex. 3.4(c), p. 92: the directions of perturbation (log deviations, indexed by
the horizon `k`): `lam k = λ̂_{t,t+k}`, `price k = p̂_{t+k}`, `cons k = ĉ_{t+k}`,
`mc k = ψ̂_{t+k}` (nominal marginal cost) and `infl j = π̂_{t+j}`. -/
structure Deviation where
  lam : ℕ → Ω → ℝ
  price : ℕ → Ω → ℝ
  cons : ℕ → Ω → ℝ
  mc : ℕ → Ω → ℝ
  infl : ℕ → Ω → ℝ

/-- Galí (2015), Ex. 3.4(c): the discount factor along the path, `βᵏ e^{s λ̂}`. -/
noncomputable def lamPath (S : SteadyState) (D : Deviation Ω) (s : ℝ) : ℕ → Ω → ℝ :=
  fun k ζ => Real.exp (k * Real.log S.β + s * D.lam k ζ)

/-- Galí (2015), Ex. 3.4(c): the price level along the path. -/
noncomputable def pPath (S : SteadyState) (D : Deviation Ω) (s : ℝ) : ℕ → Ω → ℝ :=
  fun k ζ => Real.exp (S.pbar + k * S.πbar + s * D.price k ζ)

/-- Galí (2015), Ex. 3.4(c): consumption along the path. -/
noncomputable def cPath (S : SteadyState) (D : Deviation Ω) (s : ℝ) : ℕ → Ω → ℝ :=
  fun k ζ => Real.exp (S.cbar + s * D.cons k ζ)

/-- Galí (2015), Ex. 3.4(c): nominal marginal cost along the path. -/
noncomputable def psiPath (S : SteadyState) (D : Deviation Ω) (s : ℝ) : ℕ → Ω → ℝ :=
  fun k ζ => Real.exp (S.ψbar + k * S.πbar + s * D.mc k ζ)

/-- Galí (2015), Ex. 3.4(c): gross inflation `Π_{t+j}` along the path. -/
noncomputable def inflPath (S : SteadyState) (D : Deviation Ω) (s : ℝ) : ℕ → Ω → ℝ :=
  fun j ζ => Real.exp (S.πbar + s * D.infl j ζ)

/-- Galí (2015), Ex. 3.4, p. 91: the indexation factor `X_{t,k} = ∏_{j<k} Π_{t+j}^ω Π^{1−ω}`
along the path. -/
noncomputable def xPath (S : SteadyState) (D : Deviation Ω) (s : ℝ) : ℕ → Ω → ℝ :=
  fun k ζ => ∏ j ∈ Finset.range k, inflPath S D s j ζ ^ S.ω * Real.exp S.πbar ^ (1 - S.ω)

/-- Galí (2015), Ex. 3.4(c): the deviation of `log X_{t,k}`, `ω ∑_{j<k} π̂_{t+j}`. -/
def xDev (S : SteadyState) (D : Deviation Ω) : ℕ → Ω → ℝ :=
  fun k ζ => S.ω * ∑ j ∈ Finset.range k, D.infl j ζ

/-- Galí (2015), Ex. 3.4(c): the deviation of the log revenue factor,
`λ̂ + (1 − ε) x̂ + (ε − 1) p̂ + ĉ`. -/
def aDev (S : SteadyState) (D : Deviation Ω) : ℕ → Ω → ℝ :=
  fun k ζ => D.lam k ζ + (1 - S.ε) * xDev S D k ζ + (S.ε - 1) * D.price k ζ + D.cons k ζ

/-- Galí (2015), Ex. 3.4(c): the deviation of the log cost factor, `â + ψ̂ − x̂`. -/
def bDev (S : SteadyState) (D : Deviation Ω) : ℕ → Ω → ℝ :=
  fun k ζ => aDev S D k ζ + (D.mc k ζ - xDev S D k ζ)

omit 𝔼 in
/-- Galí (2015), Ex. 3.4, p. 91: `X_{t,k} = exp(kπ + s ω ∑_{j<k} π̂_{t+j})`. -/
theorem xPath_eq (S : SteadyState) (D : Deviation Ω) (s : ℝ) (k : ℕ) (ζ : Ω) :
    xPath S D s k ζ = Real.exp (k * S.πbar + s * xDev S D k ζ) := by
  unfold xPath inflPath xDev
  have hterm : ∀ j, Real.exp (S.πbar + s * D.infl j ζ) ^ S.ω * Real.exp S.πbar ^ (1 - S.ω)
      = Real.exp (S.πbar + s * S.ω * D.infl j ζ) := by
    intro j
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  simp_rw [hterm]
  rw [← Real.exp_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, Finset.mul_sum]
  congr 1
  rw [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => by ring

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(c): the revenue factor along the path is
`e^{(ε−1) pbar + cbar} βᵏ e^{s âₖ}`. -/
theorem revFactor_path (S : SteadyState) (hβ : 0 < S.β) (D : Deviation Ω) (s : ℝ) (k : ℕ) :
    revFactor S.ε (lamPath S D s k) (xPath S D s k) (pPath S D s k) (cPath S D s k)
      = (Real.exp ((S.ε - 1) * S.pbar + S.cbar) * S.β ^ k) •
        fun ζ => Real.exp (s * aDev S D k ζ) := by
  funext ζ
  simp only [revFactor, lamPath, pPath, cPath, xPath_eq, Pi.smul_apply, smul_eq_mul]
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_log hβ, ← Real.exp_nat_mul,
    Real.exp_log hβ, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add]
  unfold aDev
  congr 1
  ring

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(c): the cost factor along the path is
`e^{ψbar + (ε−1) pbar + cbar} βᵏ e^{s b̂ₖ}`. -/
theorem costFactor_path (S : SteadyState) (hβ : 0 < S.β) (D : Deviation Ω) (s : ℝ) (k : ℕ) :
    costFactor S.ε (lamPath S D s k) (xPath S D s k) (pPath S D s k) (cPath S D s k)
        (psiPath S D s k)
      = (Real.exp (S.ψbar + (S.ε - 1) * S.pbar + S.cbar) * S.β ^ k) •
        fun ζ => Real.exp (s * bDev S D k ζ) := by
  funext ζ
  simp only [costFactor, lamPath, pPath, cPath, psiPath, xPath_eq, Pi.smul_apply, smul_eq_mul]
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_log hβ, ← Real.exp_nat_mul,
    Real.exp_log hβ, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add, ← Real.exp_add]
  unfold bDev aDev
  congr 1
  ring

/-- Galí (2015), Ex. 3.4(c): `A_t` along the path is `e^{(ε−1) pbar + cbar}` times
`∑ (βθ)ᵏ E_t e^{s âₖ}`. -/
theorem sumA_path (S : SteadyState) (hβ : 0 < S.β) (D : Deviation Ω) (t : ℕ) (s : ℝ)
    (ζ : Ω) : sumA 𝔼 S.θ S.ε t (lamPath S D s) (xPath S D s) (pPath S D s) (cPath S D s) ζ
      = Real.exp ((S.ε - 1) * S.pbar + S.cbar) * expSum 𝔼 (S.β * S.θ) t (aDev S D) s ζ := by
  unfold sumA expSum
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [revFactor_path S hβ D s k, map_smul, Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

/-- Galí (2015), Ex. 3.4(c): `B_t` along the path is `e^{ψbar + (ε−1) pbar + cbar}` times
`∑ (βθ)ᵏ E_t e^{s b̂ₖ}`. -/
theorem sumB_path (S : SteadyState) (hβ : 0 < S.β) (D : Deviation Ω) (t : ℕ) (s : ℝ)
    (ζ : Ω) : sumB 𝔼 S.θ S.ε t (lamPath S D s) (xPath S D s) (pPath S D s) (cPath S D s)
        (psiPath S D s) ζ
      = Real.exp (S.ψbar + (S.ε - 1) * S.pbar + S.cbar) *
        expSum 𝔼 (S.β * S.θ) t (bDev S D) s ζ := by
  unfold sumB expSum
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [costFactor_path S hβ D s k, map_smul, Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

/-- Galí (2015), Ex. 3.4(c), p. 92: the log of the optimal reset price `M B_t/A_t` along the
perturbation path. -/
noncomputable def logResetPrice (S : SteadyState) (D : Deviation Ω) (t : ℕ) (s : ℝ) (ζ : Ω) :
    ℝ :=
  Real.log (markup S.ε *
    sumB 𝔼 S.θ S.ε t (lamPath S D s) (xPath S D s) (pPath S D s) (cPath S D s)
      (psiPath S D s) ζ /
    sumA 𝔼 S.θ S.ε t (lamPath S D s) (xPath S D s) (pPath S D s) (cPath S D s) ζ)

/-- Galí (2015), Ex. 3.4(c): the bounds on the perturbation directions used below: all
deviations grow at most linearly in the horizon, inflation deviations are bounded. -/
def DevBounded (D : Deviation Ω) (K : ℝ) : Prop :=
  (∀ k ζ, |D.lam k ζ| ≤ K * (k + 1)) ∧ (∀ k ζ, |D.price k ζ| ≤ K * (k + 1)) ∧
    (∀ k ζ, |D.cons k ζ| ≤ K * (k + 1)) ∧ (∀ k ζ, |D.mc k ζ| ≤ K * (k + 1)) ∧
    ∀ j ζ, |D.infl j ζ| ≤ K

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(c): `|x̂ₖ| ≤ K(k + 1)` for `0 ≤ ω ≤ 1`. -/
theorem abs_xDev_le {S : SteadyState} (hω0 : 0 ≤ S.ω) (hω1 : S.ω ≤ 1) {D : Deviation Ω}
    {K : ℝ} (hK : 0 ≤ K) (hD : DevBounded D K) (k : ℕ) (ζ : Ω) :
    |xDev S D k ζ| ≤ K * (k + 1) := by
  unfold xDev
  rw [abs_mul, abs_of_nonneg hω0]
  have hs : |∑ j ∈ Finset.range k, D.infl j ζ| ≤ k * K := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ Finset.range k, |D.infl j ζ| ≤ ∑ _j ∈ Finset.range k, K :=
          Finset.sum_le_sum fun j _ => hD.2.2.2.2 j ζ
      _ = k * K := by simp
  calc S.ω * |∑ j ∈ Finset.range k, D.infl j ζ| ≤ 1 * (k * K) :=
        mul_le_mul hω1 hs (abs_nonneg _) zero_le_one
    _ ≤ K * (k + 1) := by nlinarith

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(c): `|âₖ|, |b̂ₖ| ≤ (2ε + 2) K (k + 1)`. -/
theorem abs_dev_le {S : SteadyState} (hε : 1 < S.ε) (hω0 : 0 ≤ S.ω) (hω1 : S.ω ≤ 1)
    {D : Deviation Ω} {K : ℝ} (hK : 0 ≤ K) (hD : DevBounded D K) (k : ℕ) (ζ : Ω) :
    |aDev S D k ζ| ≤ (2 * S.ε + 2) * K * (k + 1) ∧
      |bDev S D k ζ| ≤ (2 * S.ε + 2) * K * (k + 1) := by
  have hx := abs_xDev_le hω0 hω1 hK hD k ζ
  obtain ⟨h1, h2, h3, h4, -⟩ := hD
  have hk : (0 : ℝ) ≤ K * (k + 1) := by positivity
  have ha : |aDev S D k ζ| ≤ 2 * S.ε * K * (k + 1) := by
    unfold aDev
    have e1 : |(1 - S.ε) * xDev S D k ζ| ≤ (S.ε - 1) * (K * (k + 1)) := by
      rw [abs_mul, abs_of_nonpos (by linarith : 1 - S.ε ≤ 0), neg_sub]
      exact mul_le_mul_of_nonneg_left hx (by linarith)
    have e2 : |(S.ε - 1) * D.price k ζ| ≤ (S.ε - 1) * (K * (k + 1)) := by
      rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ S.ε - 1)]
      exact mul_le_mul_of_nonneg_left (h2 k ζ) (by linarith)
    calc |D.lam k ζ + (1 - S.ε) * xDev S D k ζ + (S.ε - 1) * D.price k ζ + D.cons k ζ|
        ≤ |D.lam k ζ| + |(1 - S.ε) * xDev S D k ζ| + |(S.ε - 1) * D.price k ζ| +
            |D.cons k ζ| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ K * (k + 1) + (S.ε - 1) * (K * (k + 1)) + (S.ε - 1) * (K * (k + 1)) +
            K * (k + 1) := by
          gcongr
          · exact h1 k ζ
          · exact h3 k ζ
      _ = 2 * S.ε * K * (k + 1) := by ring
  refine ⟨ha.trans (by nlinarith : 2 * S.ε * K * (k + 1) ≤ (2 * S.ε + 2) * K * (k + 1)), ?_⟩
  unfold bDev
  calc |aDev S D k ζ + (D.mc k ζ - xDev S D k ζ)|
      ≤ |aDev S D k ζ| + (|D.mc k ζ| + |xDev S D k ζ|) :=
        (abs_add_le _ _).trans (add_le_add le_rfl (abs_sub _ _))
    _ ≤ 2 * S.ε * K * (k + 1) + (K * (k + 1) + K * (k + 1)) := by
        gcongr
        exact h4 k ζ
    _ = (2 * S.ε + 2) * K * (k + 1) := by ring

/-- Galí (2015), Ex. 3.4(c), p. 92: at the steady state the reset price is
`p* = μ + ψbar` (`μ = log M`). -/
theorem logResetPrice_zero (S : SteadyState) (hβ : 0 < S.β) (hθ0 : 0 ≤ S.θ)
    (hβθ : S.β * S.θ < 1) (hε : 1 < S.ε) (D : Deviation Ω) (t : ℕ) (ζ : Ω) :
    logResetPrice 𝔼 S D t 0 ζ = Real.log (markup S.ε) + S.ψbar := by
  have ha0 : 0 ≤ S.β * S.θ := mul_nonneg hβ.le hθ0
  unfold logResetPrice
  rw [sumA_path 𝔼 S hβ D t 0 ζ, sumB_path 𝔼 S hβ D t 0 ζ, expSum_zero 𝔼 ha0 hβθ,
    expSum_zero 𝔼 ha0 hβθ]
  have hM : 0 < markup S.ε := div_pos (by linarith) (by linarith)
  have h1b : 1 - S.β * S.θ ≠ 0 := by linarith
  have e : markup S.ε * (Real.exp (S.ψbar + (S.ε - 1) * S.pbar + S.cbar) * (1 - S.β * S.θ)⁻¹) /
      (Real.exp ((S.ε - 1) * S.pbar + S.cbar) * (1 - S.β * S.θ)⁻¹)
      = markup S.ε * Real.exp S.ψbar := by
    rw [show S.ψbar + (S.ε - 1) * S.pbar + S.cbar = S.ψbar + ((S.ε - 1) * S.pbar + S.cbar)
      by ring, Real.exp_add]
    have := Real.exp_pos ((S.ε - 1) * S.pbar + S.cbar)
    field_simp
  rw [e, Real.log_mul hM.ne' (Real.exp_pos _).ne', Real.log_exp]

/-- Galí (2015), Ex. 3.4(c), p. 92: **the log-linear price-setting rule as an exact
derivative**. Perturb every variable of the reset-price problem in an arbitrary direction
`D` (with linearly bounded deviations); the log of the optimal reset price `M B_t/A_t` has
derivative
`(1 − βθ) ∑ (βθ)ᵏ E_t{ψ̂_{t+k} − ω ∑_{j<k} π̂_{t+j}}` at the steady state. Deviations of the
discount factor, the price level and consumption drop out. -/
theorem hasDerivAt_logResetPrice (S : SteadyState) (hβ : 0 < S.β) (hθ0 : 0 ≤ S.θ)
    (hβθ : S.β * S.θ < 1) (hε : 1 < S.ε) (hω0 : 0 ≤ S.ω) (hω1 : S.ω ≤ 1) (D : Deviation Ω)
    {K : ℝ} (hK : 0 ≤ K) (hD : DevBounded D K) (t : ℕ) (ζ : Ω) :
    HasDerivAt (fun s => logResetPrice 𝔼 S D t s ζ)
      ((1 - S.β * S.θ) * ∑' k, (S.β * S.θ) ^ k *
        𝔼.E t (fun ζ' => D.mc k ζ' - S.ω * ∑ j ∈ Finset.range k, D.infl j ζ') ζ) 0 := by
  have ha0 : 0 ≤ S.β * S.θ := mul_nonneg hβ.le hθ0
  have hK' : 0 ≤ (2 * S.ε + 2) * K := by nlinarith
  have hza : ∀ k ζ, |aDev S D k ζ| ≤ (2 * S.ε + 2) * K * (k + 1) :=
    fun k ζ => (abs_dev_le hε hω0 hω1 hK hD k ζ).1
  have hzb : ∀ k ζ, |bDev S D k ζ| ≤ (2 * S.ε + 2) * K * (k + 1) :=
    fun k ζ => (abs_dev_le hε hω0 hω1 hK hD k ζ).2
  have hR := hasDerivAt_logRatio 𝔼 ha0 hβθ hK' hza hzb t ζ
  have hM : 0 < markup S.ε := div_pos (by linarith) (by linarith)
  have hcont : ∀ z : ℕ → Ω → ℝ, (∀ k ζ, |z k ζ| ≤ (2 * S.ε + 2) * K * (k + 1)) →
      ∀ᶠ s in 𝓝 (0 : ℝ), expSum 𝔼 (S.β * S.θ) t z s ζ ≠ 0 := by
    intro z hz
    refine (hasDerivAt_expSum 𝔼 ha0 hβθ hK' hz t ζ).continuousAt.eventually_ne ?_
    rw [expSum_zero 𝔼 ha0 hβθ]
    exact inv_ne_zero (by linarith)
  have heq : (fun s => logResetPrice 𝔼 S D t s ζ) =ᶠ[𝓝 0] fun s =>
      (Real.log (markup S.ε) + S.ψbar) + (Real.log (expSum 𝔼 (S.β * S.θ) t (bDev S D) s ζ) -
        Real.log (expSum 𝔼 (S.β * S.θ) t (aDev S D) s ζ)) := by
    filter_upwards [hcont _ hza, hcont _ hzb] with s hsa hsb
    unfold logResetPrice
    rw [sumA_path 𝔼 S hβ D t s ζ, sumB_path 𝔼 S hβ D t s ζ]
    have e : markup S.ε * (Real.exp (S.ψbar + (S.ε - 1) * S.pbar + S.cbar) *
        expSum 𝔼 (S.β * S.θ) t (bDev S D) s ζ) /
        (Real.exp ((S.ε - 1) * S.pbar + S.cbar) * expSum 𝔼 (S.β * S.θ) t (aDev S D) s ζ)
        = markup S.ε * Real.exp S.ψbar * expSum 𝔼 (S.β * S.θ) t (bDev S D) s ζ /
          expSum 𝔼 (S.β * S.θ) t (aDev S D) s ζ := by
      rw [show S.ψbar + (S.ε - 1) * S.pbar + S.cbar = S.ψbar + ((S.ε - 1) * S.pbar + S.cbar)
        by ring, Real.exp_add]
      have := Real.exp_pos ((S.ε - 1) * S.pbar + S.cbar)
      field_simp
    rw [e, Real.log_div (mul_ne_zero (mul_ne_zero hM.ne' (Real.exp_pos _).ne') hsb) hsa,
      Real.log_mul (mul_ne_zero hM.ne' (Real.exp_pos _).ne') hsb,
      Real.log_mul hM.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  refine ((hR.const_add _).congr_of_eventuallyEq heq).congr_deriv ?_
  congr 1
  refine tsum_congr fun k => ?_
  congr 1
  rw [← Pi.sub_apply (𝔼.E t (bDev S D k)), ← map_sub]
  have hfun : bDev S D k - aDev S D k
      = fun ζ' => D.mc k ζ' - S.ω * ∑ j ∈ Finset.range k, D.infl j ζ' := by
    funext ζ'
    simp only [Pi.sub_apply, bDev, xDev]
    ring
  rw [hfun]

/-- Galí (2015), Ex. 3.4(b)–(c), p. 92: **the perturbed reset price is optimal**. Near the
steady state (`|s| < δ`), for every state, a positive price maximises the perturbed objective
if and only if it equals `exp (logResetPrice s)`, the price whose derivative is computed in
`hasDerivAt_logResetPrice`. -/
theorem resetPrice_isMaxOn_iff (S : SteadyState) (hβ : 0 < S.β) (hθ0 : 0 ≤ S.θ)
    (hβθ : S.β * S.θ < 1) (hε : 1 < S.ε) (hω0 : 0 ≤ S.ω) (hω1 : S.ω ≤ 1) (D : Deviation Ω)
    {K : ℝ} (hK : 0 ≤ K) (hD : DevBounded D K) (t : ℕ) :
    ∃ δ > 0, ∀ s, |s| < δ → ∀ ζ, ∀ x > 0,
      (IsMaxOn (fun y => objective 𝔼 S.θ S.ε t (lamPath S D s) (xPath S D s) (pPath S D s)
          (cPath S D s) (psiPath S D s) y ζ) (Set.Ioi 0) x ↔
        x = Real.exp (logResetPrice 𝔼 S D t s ζ)) := by
  have ha0 : 0 ≤ S.β * S.θ := mul_nonneg hβ.le hθ0
  have hK' : 0 ≤ (2 * S.ε + 2) * K := by nlinarith
  have hza : ∀ k ζ, |aDev S D k ζ| ≤ (2 * S.ε + 2) * K * (k + 1) :=
    fun k ζ => (abs_dev_le hε hω0 hω1 hK hD k ζ).1
  have hzb : ∀ k ζ, |bDev S D k ζ| ≤ (2 * S.ε + 2) * K * (k + 1) :=
    fun k ζ => (abs_dev_le hε hω0 hω1 hK hD k ζ).2
  refine ⟨radius (S.β * S.θ) ((2 * S.ε + 2) * K), radius_pos ha0 hβθ hK', fun s hs ζ x hx => ?_⟩
  obtain ⟨hsa, hpa⟩ := expSum_summable_pos 𝔼 ha0 hβθ hK' hza hs t ζ
  obtain ⟨hsb, hpb⟩ := expSum_summable_pos 𝔼 ha0 hβθ hK' hzb hs t ζ
  have hX : ∀ k ζ, 0 < xPath S D s k ζ := fun k ζ => by rw [xPath_eq]; exact Real.exp_pos _
  have hP : ∀ k ζ, 0 < pPath S D s k ζ := fun k ζ => Real.exp_pos _
  have hsA : Summable fun k => S.θ ^ k * 𝔼.E t (revFactor S.ε (lamPath S D s k)
      (xPath S D s k) (pPath S D s k) (cPath S D s k)) ζ := by
    refine (hsa.mul_left (Real.exp ((S.ε - 1) * S.pbar + S.cbar))).congr fun k => ?_
    rw [revFactor_path S hβ D s k, map_smul, Pi.smul_apply, smul_eq_mul, mul_pow]
    ring
  have hsB : Summable fun k => S.θ ^ k * 𝔼.E t (costFactor S.ε (lamPath S D s k)
      (xPath S D s k) (pPath S D s k) (cPath S D s k) (psiPath S D s k)) ζ := by
    refine (hsb.mul_left (Real.exp (S.ψbar + (S.ε - 1) * S.pbar + S.cbar))).congr fun k => ?_
    rw [costFactor_path S hβ D s k, map_smul, Pi.smul_apply, smul_eq_mul, mul_pow]
    ring
  have hA : 0 < sumA 𝔼 S.θ S.ε t (lamPath S D s) (xPath S D s) (pPath S D s) (cPath S D s) ζ := by
    rw [sumA_path 𝔼 S hβ D t s ζ]; exact mul_pos (Real.exp_pos _) hpa
  have hB : 0 < sumB 𝔼 S.θ S.ε t (lamPath S D s) (xPath S D s) (pPath S D s) (cPath S D s)
      (psiPath S D s) ζ := by
    rw [sumB_path 𝔼 S hβ D t s ζ]; exact mul_pos (Real.exp_pos _) hpb
  have hM : 0 < markup S.ε := div_pos (by linarith) (by linarith)
  rw [isMaxOn_iff_foc 𝔼 hε hx hX hP hsA hsB hA hB, foc_iff 𝔼 hx hX hP hsA hsB hA,
    logResetPrice, Real.exp_log (div_pos (mul_pos hM hB) hA)]

/-! ### (d) The hybrid New Keynesian Phillips curve -/

/-- Galí (2015), eq. (17), p. 61, with `α = 0` (constant returns, `Θ = 1`):
`λ = (1 − θ)(1 − βθ)/θ`. -/
noncomputable def lambdaNK (β θ : ℝ) : ℝ := (1 - θ) * (1 - β * θ) / θ

/-- Galí (2015), Ex. 3.4(d), p. 92 (used for the forward sums of (c)): `E_t` commutes with a
series whose terms are dominated, uniformly in the state, by a summable sequence. Only the
`ExpectationSystem` axioms are used (`E_t` is monotone and fixes constants, hence continuous
for the uniform norm). -/
theorem E_tsum_of_bound {y : ℕ → Ω → ℝ} {u : ℕ → ℝ} (hy : ∀ k ζ, |y k ζ| ≤ u k)
    (hu : Summable u) (t : ℕ) :
    𝔼.E t (fun ζ => ∑' k, y k ζ) = fun ζ => ∑' k, 𝔼.E t (y k) ζ := by
  funext ζ
  set F : Ω → ℝ := fun ζ => ∑' k, y k ζ with hF
  set Fn : ℕ → Ω → ℝ := fun n => ∑ k ∈ Finset.range n, y k with hFn
  set T : ℕ → ℝ := fun n => ∑' k, u (k + n) with hT
  have hTlim : Tendsto T atTop (𝓝 0) := tendsto_sum_nat_add u
  have hsy : ∀ ζ', Summable fun k => y k ζ' := fun ζ' =>
    Summable.of_norm_bounded hu fun k => by rw [Real.norm_eq_abs]; exact hy k ζ'
  have htail : ∀ n ζ', |F ζ' - Fn n ζ'| ≤ T n := by
    intro n ζ'
    have hsplit := (hsy ζ').sum_add_tsum_nat_add n
    have hFn' : Fn n ζ' = ∑ k ∈ Finset.range n, y k ζ' := by simp [hFn, Finset.sum_apply]
    rw [hFn']
    change |∑' k, y k ζ' - _| ≤ T n
    rw [← hsplit, add_sub_cancel_left]
    have hs' : Summable fun k => y (k + n) ζ' := (summable_nat_add_iff n).mpr (hsy ζ')
    have hg : Summable fun k => u (k + n) := (summable_nat_add_iff n).mpr hu
    calc |∑' k, y (k + n) ζ'| ≤ ∑' k, |y (k + n) ζ'| := by
          simpa [Real.norm_eq_abs] using
            norm_tsum_le_tsum_norm (f := fun k => y (k + n) ζ')
              (by simpa only [Real.norm_eq_abs] using hs'.abs)
      _ ≤ T n := Summable.tsum_le_tsum (fun k => hy (k + n) ζ') hs'.abs hg
  have hEFn : ∀ n, 𝔼.E t (Fn n) ζ = ∑ k ∈ Finset.range n, 𝔼.E t (y k) ζ := by
    intro n
    simp [hFn, map_sum, Finset.sum_apply]
  have hlim1 : Tendsto (fun n => 𝔼.E t (Fn n) ζ) atTop (𝓝 (𝔼.E t F ζ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hTlim
    have h := 𝔼.abs_E_le (x := F - Fn n) (fun ζ' => htail n ζ') t ζ
    rw [map_sub, Pi.sub_apply] at h
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact h
  have hsE : Summable fun k => 𝔼.E t (y k) ζ :=
    Summable.of_norm_bounded hu fun k => by rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (hy k) t ζ
  have hlim2 : Tendsto (fun n => 𝔼.E t (Fn n) ζ) atTop (𝓝 (∑' k, 𝔼.E t (y k) ζ)) := by
    simp_rw [hEFn]
    exact hsE.hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique hlim1 hlim2

/-- Galí (2015), Ex. 3.4(d): the expectation system shifted by one period, `E'_t = E_{t+1}`
(used to apply forward uniqueness to equations that hold from date `1` on). -/
def shiftE : ExpectationSystem Ω where
  E := fun t => 𝔼.E (t + 1)
  const := fun t c => 𝔼.const (t + 1) c
  mono := fun t _ _ h => 𝔼.mono (t + 1) h
  tower := fun h x => 𝔼.tower (Nat.succ_le_succ h) x
  known := fun h x => 𝔼.known (Nat.succ_le_succ h) x

/-- Galí (2015), Ex. 3.4(c)–(d): the relative term of the price-setting rule at horizon `k`,
`(p̂_{t+k} − p̂_t) − μ̂_{t+k} − ω ∑_{j<k} π̂_{t+j}`, with `p̂_{t+k} − p̂_t = ∑_{j<k} π̂_{t+1+j}`. -/
def Zrel (ω : ℝ) (infl mu : ℕ → Ω → ℝ) (t k : ℕ) : Ω → ℝ :=
  fun ζ => ∑ j ∈ Finset.range k, infl (t + 1 + j) ζ - mu (t + k) ζ -
    ω * ∑ j ∈ Finset.range k, infl (t + j) ζ

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(d): `Z_{t,0} = −μ̂_t`. -/
theorem Zrel_zero (ω : ℝ) (infl mu : ℕ → Ω → ℝ) (t : ℕ) :
    Zrel ω infl mu t 0 = fun ζ => -mu t ζ := by
  funext ζ
  simp [Zrel]

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(d): `Z_{t,k+1} = π̂_{t+1} − ω π̂_t + Z_{t+1,k}`. -/
theorem Zrel_succ (ω : ℝ) (infl mu : ℕ → Ω → ℝ) (t k : ℕ) :
    Zrel ω infl mu t (k + 1) =
      fun ζ => infl (t + 1) ζ - ω * infl t ζ + Zrel ω infl mu (t + 1) k ζ := by
  funext ζ
  simp only [Zrel, Finset.sum_range_succ']
  have e1 : ∑ j ∈ Finset.range k, infl (t + 1 + (j + 1)) ζ
      = ∑ j ∈ Finset.range k, infl (t + 1 + 1 + j) ζ :=
    Finset.sum_congr rfl fun j _ => by rw [show t + 1 + (j + 1) = t + 1 + 1 + j by omega]
  have e2 : ∑ j ∈ Finset.range k, infl (t + (j + 1)) ζ
      = ∑ j ∈ Finset.range k, infl (t + 1 + j) ζ :=
    Finset.sum_congr rfl fun j _ => by rw [show t + (j + 1) = t + 1 + j by omega]
  rw [e1, e2, show t + (k + 1) = t + 1 + k by omega]
  simp only [add_zero]
  ring

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(d): `|Z_{t,k}| ≤ 2M(k + 1)` when `|π̂|, |μ̂| ≤ M`, `0 ≤ ω ≤ 1`. -/
theorem abs_Zrel_le {ω M : ℝ} (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) (hM : 0 ≤ M)
    {infl mu : ℕ → Ω → ℝ} (hib : ∀ t ζ, |infl t ζ| ≤ M) (hmb : ∀ t ζ, |mu t ζ| ≤ M)
    (t k : ℕ) (ζ : Ω) : |Zrel ω infl mu t k ζ| ≤ 2 * M * (k + 1) := by
  have hs : ∀ m, |∑ j ∈ Finset.range k, infl (m + j) ζ| ≤ k * M := by
    intro m
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ Finset.range k, |infl (m + j) ζ| ≤ ∑ _j ∈ Finset.range k, M :=
          Finset.sum_le_sum fun j _ => hib _ ζ
      _ = k * M := by simp
  unfold Zrel
  have h1 := hs (t + 1)
  have h2 := hs t
  have h3 := hmb (t + k) ζ
  have h4 : |ω * ∑ j ∈ Finset.range k, infl (t + j) ζ| ≤ k * M := by
    rw [abs_mul, abs_of_nonneg hω0]
    calc ω * |∑ j ∈ Finset.range k, infl (t + j) ζ| ≤ 1 * (k * M) :=
          mul_le_mul hω1 h2 (abs_nonneg _) zero_le_one
      _ = k * M := one_mul _
  calc |∑ j ∈ Finset.range k, infl (t + 1 + j) ζ - mu (t + k) ζ -
        ω * ∑ j ∈ Finset.range k, infl (t + j) ζ|
      ≤ |∑ j ∈ Finset.range k, infl (t + 1 + j) ζ| + |mu (t + k) ζ| +
          |ω * ∑ j ∈ Finset.range k, infl (t + j) ζ| :=
        (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ k * M + M + k * M := by gcongr
    _ ≤ 2 * M * (k + 1) := by nlinarith

/-- Galí (2015), Ex. 3.4(c)–(d): the discounted forward sum `T_t = ∑ aᵏ E_t Z_{t,k}`. -/
noncomputable def Tsum (a ω : ℝ) (infl mu : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ζ => ∑' k, a ^ k * 𝔼.E t (Zrel ω infl mu t k) ζ

/-- Galí (2015), Ex. 3.4(d): the forward sum is bounded by `∑ aᵏ 2M(k + 1)`. -/
theorem abs_Tsum_le {a ω M : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1)
    (hM : 0 ≤ M) {infl mu : ℕ → Ω → ℝ} (hib : ∀ t ζ, |infl t ζ| ≤ M)
    (hmb : ∀ t ζ, |mu t ζ| ≤ M) (t : ℕ) (ζ : Ω) :
    |Tsum 𝔼 a ω infl mu t ζ| ≤ ∑' k : ℕ, 2 * M * (((k : ℝ) + 1) * a ^ k) := by
  have hb : ∀ k, |a ^ k * 𝔼.E t (Zrel ω infl mu t k) ζ| ≤ 2 * M * (((k : ℝ) + 1) * a ^ k) := by
    intro k
    rw [abs_mul, abs_of_nonneg (pow_nonneg h0 k)]
    calc a ^ k * |𝔼.E t (Zrel ω infl mu t k) ζ| ≤ a ^ k * (2 * M * (k + 1)) :=
          mul_le_mul_of_nonneg_left
            (𝔼.abs_E_le (abs_Zrel_le hω0 hω1 hM hib hmb t k) t ζ) (pow_nonneg h0 k)
      _ = 2 * M * (((k : ℝ) + 1) * a ^ k) := by ring
  have hg : Summable fun k : ℕ => 2 * M * (((k : ℝ) + 1) * a ^ k) :=
    (summable_succ_mul_geom h0 h1).mul_left _
  have hs : Summable fun k => |a ^ k * 𝔼.E t (Zrel ω infl mu t k) ζ| :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hb hg
  calc |Tsum 𝔼 a ω infl mu t ζ| ≤ ∑' k, |a ^ k * 𝔼.E t (Zrel ω infl mu t k) ζ| := by
        simpa [Real.norm_eq_abs, Tsum] using
          norm_tsum_le_tsum_norm (f := fun k => a ^ k * 𝔼.E t (Zrel ω infl mu t k) ζ)
            (by simpa only [Real.norm_eq_abs] using hs)
    _ ≤ _ := Summable.tsum_le_tsum hb hs hg

/-- Galí (2015), Ex. 3.4(d): **the recursion of the forward sum**,
`T_t = −μ̂_t + (a/(1 − a))(E_t π̂_{t+1} − ω π̂_t) + a E_t T_{t+1}`. -/
theorem Tsum_rec {a ω M : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1)
    (hM : 0 ≤ M) {infl mu : ℕ → Ω → ℝ} (hia : 𝔼.Adapted infl) (hma : 𝔼.Adapted mu)
    (hib : ∀ t ζ, |infl t ζ| ≤ M) (hmb : ∀ t ζ, |mu t ζ| ≤ M) (t : ℕ) :
    Tsum 𝔼 a ω infl mu t = (fun ζ => -mu t ζ) +
      (a / (1 - a)) • (𝔼.E t (infl (t + 1)) - ω • infl t) +
        a • 𝔼.E t (Tsum 𝔼 a ω infl mu (t + 1)) := by
  have hZ : ∀ s k ζ, |Zrel ω infl mu s k ζ| ≤ 2 * M * (k + 1) :=
    fun s k ζ => abs_Zrel_le hω0 hω1 hM hib hmb s k ζ
  -- `E_t` of the next forward sum
  have hET : 𝔼.E t (Tsum 𝔼 a ω infl mu (t + 1))
      = fun ζ => ∑' k, a ^ k * 𝔼.E t (Zrel ω infl mu (t + 1) k) ζ := by
    have hy : ∀ k ζ, |(a ^ k • 𝔼.E (t + 1) (Zrel ω infl mu (t + 1) k)) ζ|
        ≤ 2 * M * (((k : ℝ) + 1) * a ^ k) := by
      intro k ζ
      rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (pow_nonneg h0 k)]
      calc a ^ k * |𝔼.E (t + 1) (Zrel ω infl mu (t + 1) k) ζ| ≤ a ^ k * (2 * M * (k + 1)) :=
            mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hZ (t + 1) k) (t + 1) ζ) (pow_nonneg h0 k)
        _ = 2 * M * (((k : ℝ) + 1) * a ^ k) := by ring
    have h := E_tsum_of_bound 𝔼 hy ((summable_succ_mul_geom h0 h1).mul_left _) t
    have hl : (fun ζ => ∑' k, (a ^ k • 𝔼.E (t + 1) (Zrel ω infl mu (t + 1) k)) ζ)
        = Tsum 𝔼 a ω infl mu (t + 1) := by
      funext ζ
      simp only [Tsum, Pi.smul_apply, smul_eq_mul]
    rw [hl] at h
    rw [h]
    funext ζ
    refine tsum_congr fun k => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, 𝔼.tower (Nat.le_succ t)]
  funext ζ
  have hsum := summable_E_lin 𝔼 h0 h1 (hZ t) t ζ
  have hsum1 := summable_E_lin 𝔼 h0 h1 (hZ (t + 1)) t ζ
  have hgeo := summable_geometric_of_lt_one h0 h1
  have hterm : ∀ k, a ^ (k + 1) * 𝔼.E t (Zrel ω infl mu t (k + 1)) ζ
      = a * (𝔼.E t (infl (t + 1)) ζ - ω * infl t ζ) * a ^ k +
        a * (a ^ k * 𝔼.E t (Zrel ω infl mu (t + 1) k) ζ) := by
    intro k
    have hf : Zrel ω infl mu t (k + 1)
        = infl (t + 1) - ω • infl t + Zrel ω infl mu (t + 1) k := by
      rw [Zrel_succ]
      funext ζ'
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hf, map_add, map_sub, map_smul, hia t]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h0E : 𝔼.E t (Zrel ω infl mu t 0) ζ = -mu t ζ := by
    rw [Zrel_zero]
    have : (fun ζ => -mu t ζ) = -mu t := rfl
    rw [this, map_neg, hma t]
    rfl
  simp only [Tsum, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hET]
  rw [hsum.tsum_eq_zero_add, pow_zero, one_mul, h0E]
  simp_rw [hterm]
  rw [(hgeo.mul_left _).tsum_add (hsum1.mul_left a), tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_lt_one h0 h1]
  have h1a : (1 : ℝ) - a ≠ 0 := by linarith
  field_simp
  ring

omit 𝔼 in
/-- Galí (2015), Ex. 3.4(d): `p̂_{t+k} = p̂_t + ∑_{j<k} π̂_{t+1+j}`. -/
theorem price_add {p infl : ℕ → Ω → ℝ} (hinfl : ∀ t, infl (t + 1) = p (t + 1) - p t)
    (t k : ℕ) : p (t + k) = p t + fun ζ => ∑ j ∈ Finset.range k, infl (t + 1 + j) ζ := by
  induction k with
  | zero => funext ζ; simp
  | succ k ih =>
    funext ζ
    have h := congrFun (hinfl (t + k)) ζ
    have hi := congrFun ih ζ
    simp only [Pi.add_apply, Pi.sub_apply] at h hi ⊢
    rw [Finset.sum_range_succ, show t + 1 + k = t + k + 1 by omega, h,
      show t + (k + 1) = t + k + 1 by omega, hi]
    ring

/-- Galí (2015), Ex. 3.4(c): the price-setting rule in levels,
`(1 − βθ) ∑ (βθ)ᵏ E_t{p̂_{t+k} − μ̂_{t+k} − ω ∑_{j<k} π̂_{t+j}}`, equals `p̂_t + (1 − βθ) T_t`. -/
theorem rule_eq {a ω M : ℝ} (h0 : 0 ≤ a) (h1 : a < 1) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1)
    (hM : 0 ≤ M) {p infl mu : ℕ → Ω → ℝ} (hpa : 𝔼.Adapted p)
    (hib : ∀ t ζ, |infl t ζ| ≤ M) (hmb : ∀ t ζ, |mu t ζ| ≤ M)
    (hinfl : ∀ t, infl (t + 1) = p (t + 1) - p t) (t : ℕ) :
    ((1 - a) • fun ζ => ∑' k, a ^ k * 𝔼.E t (fun ζ' => p (t + k) ζ' - mu (t + k) ζ' -
        ω * ∑ j ∈ Finset.range k, infl (t + j) ζ') ζ)
      = p t + (1 - a) • Tsum 𝔼 a ω infl mu t := by
  have hZ : ∀ k ζ, |Zrel ω infl mu t k ζ| ≤ 2 * M * (k + 1) :=
    fun k ζ => abs_Zrel_le hω0 hω1 hM hib hmb t k ζ
  funext ζ
  have hterm : ∀ k, 𝔼.E t (fun ζ' => p (t + k) ζ' - mu (t + k) ζ' -
      ω * ∑ j ∈ Finset.range k, infl (t + j) ζ') ζ = p t ζ + 𝔼.E t (Zrel ω infl mu t k) ζ := by
    intro k
    have hf : (fun ζ' => p (t + k) ζ' - mu (t + k) ζ' -
        ω * ∑ j ∈ Finset.range k, infl (t + j) ζ') = p t + Zrel ω infl mu t k := by
      funext ζ'
      rw [price_add hinfl t k]
      simp only [Zrel, Pi.add_apply]
      ring
    rw [hf, map_add, hpa t, Pi.add_apply]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, hterm, mul_add]
  rw [((summable_geometric_of_lt_one h0 h1).mul_right (p t ζ)).tsum_add
      (summable_E_lin 𝔼 h0 h1 hZ t ζ), tsum_mul_right, tsum_geometric_of_lt_one h0 h1]
  simp only [Tsum]
  have h1a : (1 : ℝ) - a ≠ 0 := by linarith
  field_simp

/-- Galí (2015), Ex. 3.4(d), p. 92: **the hybrid New Keynesian Phillips curve**. Let the
(log-deviation) price level `p̂`, inflation `π̂_{t+1} = p̂_{t+1} − p̂_t`, the average markup
`μ̂` (so `ψ̂ = p̂ − μ̂`) and the reset price `p̂*` satisfy (a)
`π̂_{t+1} = θω π̂_t + (1 − θ)(p̂*_{t+1} − p̂_t)` and the rule (c)
`p̂*_t = (1 − βθ) ∑ (βθ)ᵏ E_t{ψ̂_{t+k} − ω ∑_{j<k} π̂_{t+j}}`. Then
`π̂_{t+1} = γ_b π̂_t + γ_f E_{t+1} π̂_{t+2} − λ̃ μ̂_{t+1}` with `γ_b = ω/(1 + βω)`,
`γ_f = β/(1 + βω)`, `λ̃ = λ/(1 + βω)`. (The handwritten 1st-edition solution obtains a
different `γ_b`; it is wrong.) -/
theorem hybrid_nkpc {β θ ω M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) (hM : 0 ≤ M) {p infl mu pstar : ℕ → Ω → ℝ}
    (hpa : 𝔼.Adapted p) (hia : 𝔼.Adapted infl) (hma : 𝔼.Adapted mu)
    (hib : ∀ t ζ, |infl t ζ| ≤ M) (hmb : ∀ t ζ, |mu t ζ| ≤ M)
    (hinfl : ∀ t, infl (t + 1) = p (t + 1) - p t)
    (ha : ∀ t, infl (t + 1) = (θ * ω) • infl t + (1 - θ) • (pstar (t + 1) - p t))
    (hc : ∀ t, pstar t = (1 - β * θ) • fun ζ => ∑' k, (β * θ) ^ k * 𝔼.E t (fun ζ' =>
      p (t + k) ζ' - mu (t + k) ζ' - ω * ∑ j ∈ Finset.range k, infl (t + j) ζ') ζ) (t : ℕ) :
    infl (t + 1) = (ω / (1 + β * ω)) • infl t + (β / (1 + β * ω)) • 𝔼.E (t + 1) (infl (t + 2)) -
      (lambdaNK β θ / (1 + β * ω)) • mu (t + 1) := by
  have ha0 : 0 ≤ β * θ := mul_nonneg hβ0 hθ0.le
  have ha1 : β * θ < 1 := by nlinarith
  -- `x_t = p̂*_t − p̂_t = (1 − βθ) T_t`
  have hx : ∀ s, pstar s - p s = (1 - β * θ) • Tsum 𝔼 (β * θ) ω infl mu s := by
    intro s
    rw [hc s, rule_eq 𝔼 ha0 ha1 hω0 hω1 hM hpa hib hmb hinfl s]
    abel
  have hrec := Tsum_rec 𝔼 ha0 ha1 hω0 hω1 hM hia hma hib hmb (t + 1)
  funext ζ
  -- (a) at `t + 1` and at `t + 2`, in terms of `x`
  have e5 : θ * infl (t + 1) ζ = θ * ω * infl t ζ +
      (1 - θ) * ((1 - β * θ) * Tsum 𝔼 (β * θ) ω infl mu (t + 1) ζ) := by
    have h1 := congrFun (ha t) ζ
    have h2 := congrFun (hinfl t) ζ
    have h3 := congrFun (hx (t + 1)) ζ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3
    linear_combination h1 - (1 - θ) * h2 + (1 - θ) * h3
  have e7 : θ * 𝔼.E (t + 1) (infl (t + 2)) ζ = θ * ω * infl (t + 1) ζ +
      (1 - θ) * ((1 - β * θ) * 𝔼.E (t + 1) (Tsum 𝔼 (β * θ) ω infl mu (t + 2)) ζ) := by
    have hE : 𝔼.E (t + 1) (infl (t + 2)) = (θ * ω) • infl (t + 1) +
        (1 - θ) • (𝔼.E (t + 1) (pstar (t + 2)) - p (t + 1)) := by
      rw [ha (t + 1), map_add, map_smul, map_smul, map_sub, hia (t + 1), hpa (t + 1)]
    have hE2 : 𝔼.E (t + 1) (pstar (t + 2)) = 𝔼.E (t + 1) (p (t + 2)) +
        (1 - β * θ) • 𝔼.E (t + 1) (Tsum 𝔼 (β * θ) ω infl mu (t + 2)) := by
      rw [← map_smul, ← map_add, ← hx (t + 2)]
      abel_nf
    have hEp : 𝔼.E (t + 1) (p (t + 2)) = 𝔼.E (t + 1) (infl (t + 2)) + p (t + 1) := by
      rw [show t + 2 = t + 1 + 1 by omega, hinfl (t + 1), map_sub, hpa (t + 1)]
      abel
    have h1 := congrFun hE ζ
    have h2 := congrFun hE2 ζ
    have h3 := congrFun hEp ζ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3
    linear_combination h1 + (1 - θ) * h2 + (1 - θ) * h3
  have e6 := congrFun hrec ζ
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e6
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, lambdaNK]
  have h1b : (1 : ℝ) - β * θ ≠ 0 := by linarith
  have hden : (1 : ℝ) + β * ω ≠ 0 := by nlinarith
  have hθ : θ ≠ 0 := hθ0.ne'
  set T1 := Tsum 𝔼 (β * θ) ω infl mu (t + 1) ζ
  set ET2 := 𝔼.E (t + 1) (Tsum 𝔼 (β * θ) ω infl mu (t + 2)) ζ
  have key : θ * (1 + β * ω) * infl (t + 1) ζ = θ * ω * infl t ζ +
      θ * β * 𝔼.E (t + 1) (infl (t + 2)) ζ - (1 - θ) * (1 - β * θ) * mu (t + 1) ζ := by
    have e6' : (1 - β * θ) * T1 = -(1 - β * θ) * mu (t + 1) ζ +
        β * θ * (𝔼.E (t + 1) (infl (t + 1 + 1)) ζ - ω * infl (t + 1) ζ) +
        β * θ * ((1 - β * θ) * ET2) := by
      rw [e6]
      field_simp
    rw [show t + 1 + 1 = t + 2 by omega] at e6'
    linear_combination e5 + (1 - θ) * e6' - β * θ * e7
  field_simp
  linear_combination key

/-- Galí (2015), Ex. 3.4(d), p. 92 (**the converse**): given the inflation equation (a), the
hybrid NKPC implies the price-setting rule (c) at every date `t ≥ 1`. Together with
`hybrid_nkpc`, under (a) the rule (c) and the hybrid NKPC are equivalent (for bounded
inflation and markups). The proof uses forward uniqueness (`forward_unique`) for
`x_t = βθ E_t x_{t+1} + f_t`, since `|βθ| < 1`. -/
theorem rule_of_hybrid_nkpc {β θ ω M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) (hM : 0 ≤ M) {p infl mu pstar : ℕ → Ω → ℝ}
    (hpa : 𝔼.Adapted p) (hia : 𝔼.Adapted infl) (hma : 𝔼.Adapted mu)
    (hib : ∀ t ζ, |infl t ζ| ≤ M) (hmb : ∀ t ζ, |mu t ζ| ≤ M)
    (hinfl : ∀ t, infl (t + 1) = p (t + 1) - p t)
    (ha : ∀ t, infl (t + 1) = (θ * ω) • infl t + (1 - θ) • (pstar (t + 1) - p t))
    (hnk : ∀ t, infl (t + 1) = (ω / (1 + β * ω)) • infl t +
      (β / (1 + β * ω)) • 𝔼.E (t + 1) (infl (t + 2)) - (lambdaNK β θ / (1 + β * ω)) • mu (t + 1))
    (t : ℕ) :
    pstar (t + 1) = (1 - β * θ) • fun ζ => ∑' k, (β * θ) ^ k * 𝔼.E (t + 1) (fun ζ' =>
      p (t + 1 + k) ζ' - mu (t + 1 + k) ζ' - ω * ∑ j ∈ Finset.range k, infl (t + 1 + j) ζ') ζ := by
  set a := β * θ with ha_def
  have ha0 : 0 ≤ a := mul_nonneg hβ0 hθ0.le
  have ha1 : a < 1 := by nlinarith
  have h1θ : (1 : ℝ) - θ ≠ 0 := by linarith
  have hden : (1 : ℝ) + β * ω ≠ 0 := by nlinarith
  -- `θ π̂_{s+1} = θω π̂_s + (1 − θ) x_{s+1}` with `x_s = p̂*_s − p̂_s`
  have f5 : ∀ s ζ, θ * infl (s + 1) ζ =
      θ * ω * infl s ζ + (1 - θ) * (pstar (s + 1) ζ - p (s + 1) ζ) := by
    intro s ζ
    have h1 := congrFun (ha s) ζ
    have h2 := congrFun (hinfl s) ζ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
    linear_combination h1 - (1 - θ) * h2
  set z₁ : ℕ → Ω → ℝ := fun s => pstar (s + 1) - p (s + 1) with hz₁
  set z₂ : ℕ → Ω → ℝ := fun s => (1 - a) • Tsum 𝔼 a ω infl mu (s + 1) with hz₂
  set u : ℕ → Ω → ℝ := fun s => (-(1 - a)) • mu (s + 1) +
    a • (𝔼.E (s + 1) (infl (s + 2)) - ω • infl (s + 1)) with hu
  have h₂ : ∀ s, z₂ s = a • (shiftE 𝔼).E s (z₂ (s + 1)) + u s := by
    intro s
    have hr := Tsum_rec 𝔼 ha0 ha1 hω0 hω1 hM hia hma hib hmb (s + 1)
    change (1 - a) • Tsum 𝔼 a ω infl mu (s + 1) =
      a • 𝔼.E (s + 1) ((1 - a) • Tsum 𝔼 a ω infl mu (s + 1 + 1)) + u s
    rw [hr, map_smul]
    funext ζ
    simp only [hu, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      show s + 1 + 1 = s + 2 by omega]
    have h1a : (1 : ℝ) - a ≠ 0 := by linarith
    field_simp
    ring
  have h₁ : ∀ s, z₁ s = a • (shiftE 𝔼).E s (z₁ (s + 1)) + u s := by
    intro s
    change pstar (s + 1) - p (s + 1) =
      a • 𝔼.E (s + 1) (pstar (s + 1 + 1) - p (s + 1 + 1)) + u s
    have hE : θ • 𝔼.E (s + 1) (infl (s + 2)) = (θ * ω) • infl (s + 1) +
        (1 - θ) • 𝔼.E (s + 1) (pstar (s + 1 + 1) - p (s + 1 + 1)) := by
      have hf : θ • infl (s + 2) = (θ * ω) • infl (s + 1) +
          (1 - θ) • (pstar (s + 1 + 1) - p (s + 1 + 1)) := by
        funext ζ
        have := f5 (s + 1) ζ
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [show s + 2 = s + 1 + 1 by omega]
        linarith
      rw [← map_smul, hf, map_add, map_smul, map_smul, hia (s + 1)]
    funext ζ
    have f7 := congrFun hE ζ
    have f5s := f5 s ζ
    have nk := congrFun (hnk s) ζ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at f7 nk
    simp only [hu, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have key : θ * (1 + β * ω) * infl (s + 1) ζ = θ * ω * infl s ζ +
        θ * β * 𝔼.E (s + 1) (infl (s + 2)) ζ - (1 - θ) * (1 - β * θ) * mu (s + 1) ζ := by
      rw [nk]
      unfold lambdaNK
      field_simp
    have hT : (1 - θ) * (pstar (s + 1) ζ - p (s + 1) ζ -
        (a * 𝔼.E (s + 1) (pstar (s + 1 + 1) - p (s + 1 + 1)) ζ +
          (-(1 - a) * mu (s + 1) ζ + a * (𝔼.E (s + 1) (infl (s + 2)) ζ - ω * infl (s + 1) ζ))))
        = 0 := by
      rw [ha_def]
      linear_combination key - f5s + β * θ * f7
    rcases mul_eq_zero.1 hT with h | h
    · exact absurd h h1θ
    · linarith
  have hb₁ : BoundedProc z₁ := by
    refine ⟨θ / (1 - θ) * (2 * M), fun s ζ => ?_⟩
    have hz : z₁ s ζ = θ / (1 - θ) * (infl (s + 1) ζ - ω * infl s ζ) := by
      simp only [hz₁, Pi.sub_apply]
      field_simp
      linear_combination -(f5 s ζ)
    rw [hz, abs_mul, abs_of_nonneg (div_nonneg hθ0.le (by linarith))]
    refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hθ0.le (by linarith))
    calc |infl (s + 1) ζ - ω * infl s ζ| ≤ |infl (s + 1) ζ| + |ω * infl s ζ| := abs_sub _ _
      _ ≤ M + M := by
          gcongr
          · exact hib _ ζ
          · rw [abs_mul, abs_of_nonneg hω0]
            calc ω * |infl s ζ| ≤ 1 * M := mul_le_mul hω1 (hib s ζ) (abs_nonneg _) zero_le_one
              _ = M := one_mul M
      _ = 2 * M := by ring
  have hb₂ : BoundedProc z₂ := by
    refine ⟨(1 - a) * ∑' k : ℕ, 2 * M * (((k : ℝ) + 1) * a ^ k), fun s ζ => ?_⟩
    simp only [hz₂, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - a)]
    exact mul_le_mul_of_nonneg_left (abs_Tsum_le 𝔼 ha0 ha1 hω0 hω1 hM hib hmb _ ζ)
      (by linarith)
  have habs : |a| < 1 := by rw [abs_of_nonneg ha0]; exact ha1
  have heq := (shiftE 𝔼).forward_unique habs h₁ h₂ hb₁ hb₂
  have hzt := congrFun heq t
  simp only [hz₁, hz₂] at hzt
  rw [rule_eq 𝔼 ha0 ha1 hω0 hω1 hM hpa hib hmb hinfl (t + 1), ← hzt]
  abel

end Gali.BasicNewKeynesianModel.Ex3_4
