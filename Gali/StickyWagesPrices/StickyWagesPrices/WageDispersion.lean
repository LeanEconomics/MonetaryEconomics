/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyWagesPrices.LaborAggregation
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Wage dispersion to second order and the wage version of Lemma 2

Galí (2015), Chapter 6, p. 171 and Appendix 6.1 (pp. 189–192).

Labour types form a probability space `(J, μ)` (the book's `[0, 1]`, or finitely many types
with weights summing to one). Log wages follow one-parameter families `w(j) = w̄ + s z(j)`
with `z` bounded and measurable, and `W` is the CES wage index (4).

## Main results

* `log_dispIntegral_second_order`: `log ∫ (X(j)/X)^e = (e(e − 1 + ε)/2) var_j x(j) + O(s³)`.
* `dW_second_order` (**p. 171, p. 190**): `d_w = ((1 − α)ε_w/2) var_j w(j) + O(s³)`, and
  `dP_second_order`: `d_p = (ε_p/(2Θ)) var_i p(i) + O(s³)` with `Θ = (1−α)/(1−α+αε_p)`.
* `relLogWage_moments`, `relLogWage_mean_second_order`, `relLogWage_sq_second_order`: p. 189,
  `∫ ŵ(j) dj = ((ε_w − 1)/2) ∫ ŵ(j)² dj + O(s³)` and `∫ ŵ(j)² = var_j w + O(s⁴)`.
* `log_integral_exp_second_order` (p. 189): `n + n²/2 = ∫ n(j) + ½ ∫ n(j)² + O(s³)` when
  `N = ∫ N(j) dj`.
* `integral_sq_employment` (p. 189): with labour demand (3) at every type, **exactly**
  `∫ n(j)² = n² + ε_w² var_j w + (d² − n²)` with `d − n = O(s²)`, hence
  `∫ n(j)² = n² + ε_w² var_j w + O(s³)` whenever aggregate employment `n = O(s)`
  (`integral_sq_employment_second_order`).
* **Lemma 2 for wages** (App. 6.1, p. 192), exact in the change of the cross-sectional mean of
  log wages `m^w`: `wageMix_var_meanChange`
  (`var_t = θ_w var_{t−1} + (θ_w/(1−θ_w))(Δm^w_t)²`), `wage_lemma2_calvo_inherited`,
  `wage_lemma2_calvo`
  (`∑ βᵗ var_j w_t(j) = θ_w/((1−βθ_w)(1−θ_w)) ∑ βᵗ (Δm^w_t)²`, convergence proved).
* `wageInflation_sub_meanChange`, `wageInflation_sq_sub_meanChange_sq`: `π^w = Δm^w + O(s²)`
  and `(π^w)² = (Δm^w)² + O(s³)`.

The Calvo law of motion of the wage cross-section used here is derived from the type-level
Calvo lottery in `WageInflation` (`wage_dist_law_of_motion`). The proofs follow the
Chapter 3 project (`PriceDispersion.lean`) and the Chapter 4 project (`Welfare.lean`), with
prices replaced by wages.
-/

namespace Gali.StickyWagesPrices.WageDispersion

open MeasureTheory ProbabilityTheory Asymptotics Filter Topology
open Gali.StickyWagesPrices.LaborAggregation

variable {J : Type*} [MeasurableSpace J]

/-- Galí (2015), App. 6.1, p. 189: the cross-sectional variance
`var_j w(j) = ∫ (w(j) − ∫ w)² dj`. -/
noncomputable def crossVar (μ : Measure J) (w : J → ℝ) : ℝ :=
  ∫ j, (w j - ∫ i, w i ∂μ) ^ 2 ∂μ

/-- Galí (2015), p. 171 (ch. 3, p. 60): `Θ = (1 − α)/(1 − α + αε)`. -/
noncomputable def bigTheta (α ε : ℝ) : ℝ := (1 - α) / (1 - α + α * ε)

variable {μ : Measure J} {ε : ℝ}

/-! ### Orders of magnitude -/

/-- Galí (2015), App. 6.1, pp. 188–190 (bookkeeping of orders): `f = O(sᵃ)` and `g = O(sᵇ)`
give `f g = O(sᵃ⁺ᵇ)` (restated from the Chapter 4 project). -/
theorem bigO_mul {f g : ℝ → ℝ} {a b : ℕ} (hf : f =O[𝓝 0] fun s => s ^ a)
    (hg : g =O[𝓝 0] fun s => s ^ b) :
    (fun s => f s * g s) =O[𝓝 0] fun s => s ^ (a + b) := by
  have := hf.mul hg
  simpa [pow_add] using this

/-- Galí (2015), App. 6.1, p. 189 ("third or higher order"): `O(sᵇ) ⊆ O(sᵃ)` for `a ≤ b`
(restated from the Chapter 4 project). -/
theorem bigO_weaken {f : ℝ → ℝ} {a b : ℕ} (hab : a ≤ b) (hf : f =O[𝓝 0] fun s => s ^ b) :
    f =O[𝓝 0] fun s => s ^ a := by
  rcases hab.lt_or_eq with h | h
  · exact hf.trans (isLittleO_pow_pow h).isBigO
  · rw [h]
    exact hf

/-- Galí (2015), App. 6.1, p. 189: a monomial `c sᵃ` is `O(sᵃ)`. -/
theorem monomial_isBigO (c : ℝ) (a : ℕ) : (fun s : ℝ => c * s ^ a) =O[𝓝 0] fun s => s ^ a :=
  (isBigO_refl _ _).const_mul_left c

/-! ### Taylor expansion of the cumulant-generating function -/

/-- Galí (2015), App. 6.1, p. 189 (via ch. 3, App. 3.4): **second-order Taylor expansion of
the cumulant-generating function** of a bounded `z`, `K(u) = (E z)u + (var z/2)u² + O(u³)`
(restated from the Chapter 3 project). -/
theorem cgf_taylor [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) :
    (fun u => cgf z μ u - (∫ j, z j ∂μ) * u - (∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ) / 2 * u ^ 2)
      =O[𝓝 0] fun u => u ^ 3 := by
  have hint := interior_integrableExpSet (μ := μ) hz hB
  have hAn : AnalyticOnNhd ℝ (cgf z μ) Set.univ := by
    have := analyticOnNhd_cgf (X := z) (μ := μ)
    rwa [hint] at this
  have hCD : ContDiff ℝ 3 (cgf z μ) := hAn.contDiff
  have hT := taylor_isLittleO_univ (x₀ := 0) hCD
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet z μ) := by
    rw [hint]
    trivial
  have hd1 : deriv (cgf z μ) 0 = ∫ j, z j ∂μ := by
    rw [deriv_cgf_zero h0]
    simp
  have hd2 : iteratedDeriv 2 (cgf z μ) 0 = ∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ := by
    rw [iteratedDeriv_two_cgf_eq_integral h0, hd1, mgf_zero]
    simp
  have heq : (fun u => cgf z μ u - (∫ j, z j ∂μ) * u -
      (∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ) / 2 * u ^ 2)
      = fun u => (cgf z μ u - taylorWithinEval (cgf z μ) 3 Set.univ 0 u) +
        iteratedDeriv 3 (cgf z μ) 0 / 6 * u ^ 3 := by
    funext u
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDerivWithin_univ,
      iteratedDeriv_zero, iteratedDeriv_one, hd1, hd2, cgf_zero, smul_eq_mul, sub_zero]
    norm_num [Nat.factorial]
    ring
  rw [heq]
  simp only [sub_zero] at hT
  exact hT.isBigO.add ((isBigO_refl _ _).const_mul_left _)

/-- Galí (2015), App. 6.1, p. 189: the Taylor remainder of `K` along a ray,
`K(a s) − (E z)(a s) − (var z/2)(a s)² = O(s³)` (restated from the Chapter 3 project). -/
theorem cgf_taylor_comp [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (a : ℝ) :
    (fun s => cgf z μ (a * s) - (∫ j, z j ∂μ) * (a * s) -
      (∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ) / 2 * (a * s) ^ 2) =O[𝓝 0] fun s => s ^ 3 := by
  have hR := cgf_taylor (μ := μ) hz hB
  have ht : Tendsto (fun s : ℝ => a * s) (𝓝 0) (𝓝 0) := by
    have := (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul a
    simpa using this
  refine (hR.comp_tendsto ht).trans ?_
  have : ((fun u : ℝ => u ^ 3) ∘ fun s => a * s) = fun s => a ^ 3 * s ^ 3 := by
    funext s
    simp only [Function.comp_apply]
    ring
  rw [this]
  exact (isBigO_refl _ _).const_mul_left _

/-- Galí (2015), App. 6.1, p. 189: a bounded measurable `z` is integrable, and so is
`(z − E z)²`. -/
theorem integrable_bounded [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) :
    Integrable z μ ∧ Integrable (fun j => (z j - ∫ i, z i ∂μ) ^ 2) μ := by
  have hzI : Integrable z μ :=
    Integrable.of_bound hz.aestronglyMeasurable B
      (Eventually.of_forall fun j => by rw [Real.norm_eq_abs]; exact hB j)
  refine ⟨hzI, ?_⟩
  set m := ∫ i, z i ∂μ
  refine Integrable.of_bound ((hz.sub measurable_const).pow_const 2).aestronglyMeasurable
    ((B + |m|) ^ 2) (Eventually.of_forall fun j => ?_)
  rw [Real.norm_eq_abs, abs_pow, sq_abs]
  have h1 : |z j - m| ≤ B + |m| := (abs_sub _ _).trans (by linarith [hB j])
  calc (z j - m) ^ 2 = |z j - m| ^ 2 := (sq_abs _).symm
    _ ≤ (B + |m|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2

/-- Galí (2015), App. 6.1, p. 189: the cross-sectional variance of `w(j) = w̄ + s z(j)` is
`s² var z` (restated from the Chapter 3 project). -/
theorem crossVar_family [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (wbar s : ℝ) :
    crossVar μ (fun j => wbar + s * z j) = s ^ 2 * ∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ := by
  have hzI := (integrable_bounded (μ := μ) hz hB).1
  have hmean : ∫ j, (wbar + s * z j) ∂μ = wbar + s * ∫ j, z j ∂μ := by
    rw [integral_add (integrable_const _) (hzI.const_mul s), integral_const, integral_const_mul]
    simp
  unfold crossVar
  beta_reduce
  rw [hmean]
  have hpt : ∀ j, (wbar + s * z j - (wbar + s * ∫ i, z i ∂μ)) ^ 2
      = s ^ 2 * (z j - ∫ i, z i ∂μ) ^ 2 := fun j => by ring
  simp_rw [hpt]
  rw [integral_const_mul]

/-- Galí (2015), App. 6.1, p. 189: along `w(j) = w̄ + s z(j)`, `var_j w = O(s²)`. -/
theorem crossVar_family_isBigO [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ j, |z j| ≤ B) (wbar : ℝ) :
    (fun s => crossVar μ (fun j => wbar + s * z j)) =O[𝓝 0] fun s => s ^ 2 := by
  have : (fun s => crossVar μ (fun j => wbar + s * z j))
      = fun s => (∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ) * s ^ 2 := by
    funext s
    rw [crossVar_family hz hB, mul_comm]
  rw [this]
  exact monomial_isBigO _ 2

/-! ### Dispersion to second order (p. 171, App. 6.1 p. 190) -/

/-- Galí (2015), p. 171 and App. 6.1, p. 190 (general form): along `x(j) = x̄ + s z(j)`,
`log ∫ (X(j)/X)^e dj = (e (e − 1 + ε)/2) var_j x(j) + O(s³)`. -/
theorem log_dispIntegral_second_order [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (e xbar : ℝ) :
    (fun s => Real.log (dispIntegral μ ε e (fun j => Real.exp (xbar + s * z j))) -
        e * (e - 1 + ε) / 2 * crossVar μ (fun j => xbar + s * z j))
      =O[𝓝 0] fun s => s ^ 3 := by
  have hcomp := cgf_taylor_comp (μ := μ) hz hB
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have heq : (fun s => Real.log (dispIntegral μ ε e (fun j => Real.exp (xbar + s * z j))) -
        e * (e - 1 + ε) / 2 * crossVar μ (fun j => xbar + s * z j))
      = fun s => (cgf z μ (e * s) - (∫ j, z j ∂μ) * (e * s) -
          (∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ) / 2 * (e * s) ^ 2) +
        (-(e / (1 - ε))) * (cgf z μ ((1 - ε) * s) - (∫ j, z j ∂μ) * ((1 - ε) * s) -
          (∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ) / 2 * ((1 - ε) * s) ^ 2) := by
    funext s
    rw [log_dispIntegral_family hz hB hε, crossVar_family hz hB]
    field_simp
    ring
  rw [heq]
  exact (hcomp e).add ((hcomp _).const_mul_left _)

/-- Galí (2015), p. 171 and App. 6.1, p. 190 (**`d_w ≃ ((1 − α)ε_w/2) var_j w(j)`**): along
the family of wage distributions `w(j) = w̄ + s z(j)` (with `W` its CES index),
`d_w(s) = ((1 − α) ε_w/2) var_j w(j) + O(s³)`. -/
theorem dW_second_order [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (α wbar : ℝ) :
    (fun s => dW μ α ε (fun j => Real.exp (wbar + s * z j)) -
        (1 - α) * ε / 2 * crossVar μ (fun j => wbar + s * z j)) =O[𝓝 0] fun s => s ^ 3 := by
  have h := (log_dispIntegral_second_order (μ := μ) hz hB hε (-ε) wbar).const_mul_left (1 - α)
  refine h.congr_left fun s => ?_
  simp only [dW, wageDisp]
  ring

/-- Galí (2015), p. 171 (**`d_p ≃ (ε_p/(2Θ)) var_i p(i)`**, as in ch. 4, App. 4.1): along
`p(i) = p̄ + s z(i)`, `d_p(s) = (ε_p/(2Θ)) var_i p(i) + O(s³)`, `Θ = (1−α)/(1−α+αε_p)`. -/
theorem dP_second_order [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (hε : 1 < ε) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (pbar : ℝ) :
    (fun s => dP μ α ε (fun j => Real.exp (pbar + s * z j)) -
        ε / (2 * bigTheta α ε) * crossVar μ (fun j => pbar + s * z j))
      =O[𝓝 0] fun s => s ^ 3 := by
  have hsubα : (1 : ℝ) - α ≠ 0 := by linarith
  have hden : 1 - α + α * ε ≠ 0 := by nlinarith
  have h := (log_dispIntegral_second_order (μ := μ) hz hB hε.ne' (-ε / (1 - α)) pbar
    ).const_mul_left (1 - α)
  refine h.congr_left fun s => ?_
  simp only [dP, priceDisp, bigTheta]
  field_simp
  ring

/-- Galí (2015), p. 171: along the wage family, `d_w = O(s²)`. -/
theorem dW_isBigO_sq [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (α wbar : ℝ) :
    (fun s => dW μ α ε (fun j => Real.exp (wbar + s * z j))) =O[𝓝 0] fun s => s ^ 2 := by
  have h := (bigO_weaken (by norm_num : 2 ≤ 3) (dW_second_order (μ := μ) hz hB hε α wbar)).add
    ((crossVar_family_isBigO (μ := μ) hz hB wbar).const_mul_left ((1 - α) * ε / 2))
  simpa using h

/-- Galí (2015), p. 171: along the wage family, `log Δ_w = O(s²)`. -/
theorem log_wageDisp_isBigO_sq [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (wbar : ℝ) :
    (fun s => Real.log (wageDisp μ ε (fun j => Real.exp (wbar + s * z j))))
      =O[𝓝 0] fun s => s ^ 2 := by
  have h := dW_isBigO_sq (μ := μ) hz hB hε 0 wbar
  simpa [dW] using h

/-! ### Relative log wages (App. 6.1, p. 189) -/

/-- Galí (2015), App. 6.1, p. 189: the relative log wage `ŵ(j) = w(j) − w` along the family
`w(j) = w̄ + s z(j)`, with `w` the log CES wage index. -/
noncomputable def relLogWage (μ : Measure J) (ε : ℝ) (z : J → ℝ) (wbar s : ℝ) (j : J) : ℝ :=
  wbar + s * z j - Real.log (cesIndex μ ε (fun i => Real.exp (wbar + s * z i)))

/-- Galí (2015), App. 6.1, p. 189: the mean of `ŵ`,
`E_j ŵ = s E z − K((1 − ε)s)/(1 − ε)`. -/
noncomputable def relLogWageMean (μ : Measure J) (ε : ℝ) (z : J → ℝ) (s : ℝ) : ℝ :=
  s * (∫ j, z j ∂μ) - cgf z μ ((1 - ε) * s) / (1 - ε)

/-- Galí (2015), App. 6.1, p. 189 (exact): `ŵ(j) = s (z(j) − E z) + E_j ŵ`. -/
theorem relLogWage_eq [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (wbar s : ℝ) (j : J) :
    relLogWage μ ε z wbar s j = s * (z j - ∫ i, z i ∂μ) + relLogWageMean μ ε z s := by
  rw [relLogWage, cesIndex_family hz hB hε, Real.log_exp, relLogWageMean]
  ring

/-- Galí (2015), App. 6.1, p. 189: `∫ (d − a (z − E z))² = d² + a² var z` for bounded `z`. -/
theorem integral_sq_affine [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (d a : ℝ) :
    ∫ j, (d - a * (z j - ∫ i, z i ∂μ)) ^ 2 ∂μ
      = d ^ 2 + a ^ 2 * ∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ := by
  obtain ⟨hzI, hz2⟩ := integrable_bounded (μ := μ) hz hB
  set m := ∫ i, z i ∂μ
  have hzc : Integrable (fun j => z j - m) μ := hzI.sub (integrable_const m)
  have hzm : ∫ j, (z j - m) ∂μ = 0 := by
    rw [integral_sub hzI (integrable_const m)]
    simp [m]
  have hsq : ∀ j, (d - a * (z j - m)) ^ 2
      = d ^ 2 + (a ^ 2 * (z j - m) ^ 2 + (-2 * a * d) * (z j - m)) := fun j => by ring
  simp_rw [hsq]
  have e1 := integral_add (μ := μ) (f := fun _ => d ^ 2)
    (g := fun j => a ^ 2 * (z j - m) ^ 2 + -2 * a * d * (z j - m)) (integrable_const _)
    ((hz2.const_mul (a ^ 2)).add (hzc.const_mul (-2 * a * d)))
  have e2 := integral_add (μ := μ) (f := fun j => a ^ 2 * (z j - m) ^ 2)
    (g := fun j => -2 * a * d * (z j - m)) (hz2.const_mul (a ^ 2)) (hzc.const_mul (-2 * a * d))
  rw [e1, e2, integral_const_mul, integral_const_mul, hzm]
  simp

/-- Galí (2015), App. 6.1, p. 189 (exact moments of `ŵ`): `E_j ŵ = relLogWageMean` and
`E_j ŵ² = var_j w + (E_j ŵ)²`. -/
theorem relLogWage_moments [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (wbar s : ℝ) :
    ∫ j, relLogWage μ ε z wbar s j ∂μ = relLogWageMean μ ε z s ∧
      ∫ j, relLogWage μ ε z wbar s j ^ 2 ∂μ
        = crossVar μ (fun j => wbar + s * z j) + relLogWageMean μ ε z s ^ 2 := by
  obtain ⟨hzI, -⟩ := integrable_bounded (μ := μ) hz hB
  simp_rw [relLogWage_eq hz hB hε wbar s]
  set m := ∫ i, z i ∂μ
  have hzm : ∫ j, (z j - m) ∂μ = 0 := by
    rw [integral_sub hzI (integrable_const m)]
    simp [m]
  refine ⟨?_, ?_⟩
  · have e1 := integral_add (μ := μ) (f := fun j => s * (z j - m))
      (g := fun _ => relLogWageMean μ ε z s) ((hzI.sub (integrable_const m)).const_mul s)
      (integrable_const _)
    rw [e1, integral_const_mul, hzm]
    simp
  · have := integral_sq_affine (μ := μ) hz hB (relLogWageMean μ ε z s) (-s)
    have e1 : ∀ j, (s * (z j - m) + relLogWageMean μ ε z s) ^ 2
        = (relLogWageMean μ ε z s - -s * (z j - m)) ^ 2 := fun j => by ring
    simp_rw [e1]
    rw [this, crossVar_family hz hB]
    ring

/-- Galí (2015), App. 6.1, p. 189: `E_j ŵ = O(s²)`. -/
theorem relLogWageMean_isBigO [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) :
    (fun s => relLogWageMean μ ε z s) =O[𝓝 0] fun s => s ^ 2 := by
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have hR := cgf_taylor_comp (μ := μ) hz hB (1 - ε)
  have : (fun s => relLogWageMean μ ε z s)
      = fun s => (-(1 - ε)⁻¹) * (cgf z μ ((1 - ε) * s) - (∫ j, z j ∂μ) * ((1 - ε) * s) -
          (∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ) / 2 * ((1 - ε) * s) ^ 2) +
        (-((1 - ε) * (∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ) / 2)) * s ^ 2 := by
    funext s
    rw [relLogWageMean]
    field_simp
    ring
  rw [this]
  exact ((bigO_weaken (by norm_num : 2 ≤ 3) hR).const_mul_left _).add (monomial_isBigO _ 2)

/-- Galí (2015), App. 6.1, p. 189 (**`∫ ŵ(j) dj = ((ε_w − 1)/2) var_j w` is of second order**):
`E_j ŵ − ((ε − 1)/2) E_j ŵ² = O(s³)`. -/
theorem relLogWage_mean_second_order [IsProbabilityMeasure μ] {z : J → ℝ}
    (hz : Measurable z) {B : ℝ} (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (wbar : ℝ) :
    (fun s => ∫ j, relLogWage μ ε z wbar s j ∂μ -
        (ε - 1) / 2 * ∫ j, relLogWage μ ε z wbar s j ^ 2 ∂μ) =O[𝓝 0] fun s => s ^ 3 := by
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have hR := cgf_taylor_comp (μ := μ) hz hB (1 - ε)
  have hE := relLogWageMean_isBigO (μ := μ) hz hB hε
  have hE2 := bigO_weaken (by norm_num : 3 ≤ 2 + 2) (bigO_mul hE hE)
  have heq : (fun s => ∫ j, relLogWage μ ε z wbar s j ∂μ -
        (ε - 1) / 2 * ∫ j, relLogWage μ ε z wbar s j ^ 2 ∂μ)
      = fun s => (-(1 - ε)⁻¹) * (cgf z μ ((1 - ε) * s) - (∫ j, z j ∂μ) * ((1 - ε) * s) -
          (∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ) / 2 * ((1 - ε) * s) ^ 2) +
        (-((ε - 1) / 2)) * (relLogWageMean μ ε z s * relLogWageMean μ ε z s) := by
    funext s
    rw [(relLogWage_moments hz hB hε wbar s).1, (relLogWage_moments hz hB hε wbar s).2,
      crossVar_family hz hB, relLogWageMean]
    field_simp
    ring
  rw [heq]
  exact (hR.const_mul_left _).add (hE2.const_mul_left _)

/-- Galí (2015), App. 6.1, p. 189: `∫ ŵ(j)² dj = var_j w + O(s⁴)`. -/
theorem relLogWage_sq_second_order [IsProbabilityMeasure μ] {z : J → ℝ}
    (hz : Measurable z) {B : ℝ} (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (wbar : ℝ) :
    (fun s => ∫ j, relLogWage μ ε z wbar s j ^ 2 ∂μ - crossVar μ (fun j => wbar + s * z j))
      =O[𝓝 0] fun s => s ^ 4 := by
  have hE := relLogWageMean_isBigO (μ := μ) hz hB hε
  refine (bigO_mul hE hE).congr_left fun s => ?_
  rw [(relLogWage_moments hz hB hε wbar s).2]
  ring

/-! ### Aggregate employment and the square of individual employment (p. 189) -/

/-- Galí (2015), App. 6.1, p. 189: with `N = ∫ N(j) dj` and `n = log N`, `n(j) = log N(j)`
(log deviations from a steady state normalised to one), the family `n(j) = s ζ(j)` gives
`n = K_ζ(s)` and `n + n²/2 = ∫ n(j) + ½ ∫ n(j)² + O(s³)`. -/
theorem log_integral_exp_second_order [IsProbabilityMeasure μ] {ζ : J → ℝ}
    (hζ : Measurable ζ) {B : ℝ} (hB : ∀ j, |ζ j| ≤ B) :
    (fun s => (Real.log (∫ j, Real.exp (s * ζ j) ∂μ) +
        Real.log (∫ j, Real.exp (s * ζ j) ∂μ) ^ 2 / 2) -
        (∫ j, s * ζ j ∂μ + (∫ j, (s * ζ j) ^ 2 ∂μ) / 2)) =O[𝓝 0] fun s => s ^ 3 := by
  obtain ⟨hζI, hζ2⟩ := integrable_bounded (μ := μ) hζ hB
  set m := ∫ j, ζ j ∂μ
  set v := ∫ j, (ζ j - m) ^ 2 ∂μ
  have hR : (fun s => cgf ζ μ s - m * s - v / 2 * s ^ 2) =O[𝓝 0] fun s => s ^ 3 :=
    cgf_taylor (μ := μ) hζ hB
  have hK : ∀ s, Real.log (∫ j, Real.exp (s * ζ j) ∂μ) = cgf ζ μ s := fun s => rfl
  have hsq : ∀ s, ∫ j, (s * ζ j) ^ 2 ∂μ = s ^ 2 * (v + m ^ 2) := by
    intro s
    have h1 : ∀ j, (s * ζ j) ^ 2 = s ^ 2 * ((ζ j - m) ^ 2 + 2 * m * (ζ j - m) + m ^ 2) :=
      fun j => by ring
    have hzc : Integrable (fun j => ζ j - m) μ := hζI.sub (integrable_const m)
    have hzm : ∫ j, (ζ j - m) ∂μ = 0 := by
      rw [integral_sub hζI (integrable_const m)]
      simp [m]
    simp_rw [h1]
    have e1 := integral_add (μ := μ) (f := fun j => (ζ j - m) ^ 2 + 2 * m * (ζ j - m))
      (g := fun _ => m ^ 2) (hζ2.add (hzc.const_mul (2 * m))) (integrable_const _)
    have e2 := integral_add (μ := μ) (f := fun j => (ζ j - m) ^ 2)
      (g := fun j => 2 * m * (ζ j - m)) hζ2 (hzc.const_mul (2 * m))
    rw [integral_const_mul, e1, e2, integral_const_mul, hzm]
    simp [v]
  have hlin : ∀ s, ∫ j, s * ζ j ∂μ = s * m := fun s => integral_const_mul s ζ
  -- `K − m s = O(s²)` and `K + m s = O(s)`
  have hA : (fun s => cgf ζ μ s - m * s) =O[𝓝 0] fun s => s ^ 2 :=
    ((bigO_weaken (by norm_num : 2 ≤ 3) hR).add (monomial_isBigO (v / 2) 2)).congr_left
      fun s => by ring
  have hB' : (fun s => cgf ζ μ s + m * s) =O[𝓝 0] fun s => s ^ 1 :=
    ((bigO_weaken (by norm_num : 1 ≤ 2) hA).add (monomial_isBigO (2 * m) 1)).congr_left
      fun s => by ring
  have hprod := bigO_mul hA hB'
  refine (hR.add (hprod.const_mul_left (1 / 2))).congr_left fun s => ?_
  rw [hK, hsq, hlin]
  ring

/-- Galí (2015), App. 6.1, p. 189 (log of labour demand (3), **exact**): with
`N(j) = (W(j)/W)^{−ε_w} N^d`, `log N(j) − log ∫ N(i) di = −ε_w ŵ(j) − log Δ_w`, where
`ŵ(j) = log W(j) − log W`. -/
theorem log_laborDemand_sub [IsProbabilityMeasure μ] {W : J → ℝ} (hW : ∀ j, 0 < W j)
    (hWi : Integrable (fun j => W j ^ (1 - ε)) μ) {Nd : ℝ} (hNd : 0 < Nd)
    (hDw : 0 < wageDisp μ ε W) (j : J) :
    Real.log (laborDemand μ ε W Nd j) - Real.log (∫ i, laborDemand μ ε W Nd i ∂μ)
      = -ε * (Real.log (W j) - Real.log (cesIndex μ ε W)) - Real.log (wageDisp μ ε W) := by
  have hpos := integral_pos_of_pos (IsProbabilityMeasure.ne_zero μ)
    (fun j => Real.rpow_pos_of_pos (hW j) (1 - ε)) hWi
  have hI := cesIndex_pos hpos
  have hint : ∫ i, laborDemand μ ε W Nd i ∂μ = wageDisp μ ε W * Nd := by
    simp only [laborDemand]
    rw [integral_mul_const, wageDisp, dispIntegral]
  have hr : 0 < W j / cesIndex μ ε W := div_pos (hW j) hI
  rw [hint, laborDemand, Real.log_mul (Real.rpow_pos_of_pos hr _).ne' hNd.ne',
    Real.log_rpow hr, Real.log_div (hW j).ne' hI.ne', Real.log_mul hDw.ne' hNd.ne']
  ring

/-- Galí (2015), App. 6.1, p. 189 (**exact form of `∫ n(j)² = n² + ε_w² var_j w`**). Along the
wage family `w(j) = w̄ + s z(j)`, let every type be on labour demand (3) with labour index
`N^d > 0`, let `n(j) = log N(j) − log N̄` and `n = log ∫ N(j) dj − log N̄` (deviations from a
steady state `N̄ > 0`). Then exactly `∫ n(j)² dj = (n − log Δ_w − ε_w E_j ŵ)² + ε_w² var_j w`. -/
theorem integral_sq_employment [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (wbar s : ℝ) {Nd Nbar : ℝ} (hNd : 0 < Nd)
    (hDw : 0 < wageDisp μ ε (fun j => Real.exp (wbar + s * z j))) :
    ∫ j, (Real.log (laborDemand μ ε (fun i => Real.exp (wbar + s * z i)) Nd j) -
        Real.log Nbar) ^ 2 ∂μ
      = (Real.log (∫ i, laborDemand μ ε (fun i => Real.exp (wbar + s * z i)) Nd i ∂μ) -
          Real.log Nbar - Real.log (wageDisp μ ε (fun j => Real.exp (wbar + s * z j))) -
          ε * relLogWageMean μ ε z s) ^ 2 + ε ^ 2 * crossVar μ (fun j => wbar + s * z j) := by
  have hWi : Integrable (fun j => Real.exp (wbar + s * z j) ^ (1 - ε)) μ := by
    have : (fun j => Real.exp (wbar + s * z j) ^ (1 - ε))
        = fun j => Real.exp ((1 - ε) * wbar) * Real.exp ((1 - ε) * s * z j) := by
      funext j
      rw [← Real.exp_mul, ← Real.exp_add]
      congr 1
      ring
    rw [this]
    exact (integrable_exp_mul hz hB _).const_mul _
  set n := Real.log (∫ i, laborDemand μ ε (fun i => Real.exp (wbar + s * z i)) Nd i ∂μ) -
    Real.log Nbar
  set δ := Real.log (wageDisp μ ε (fun j => Real.exp (wbar + s * z j)))
  have hpt : ∀ j, Real.log (laborDemand μ ε (fun i => Real.exp (wbar + s * z i)) Nd j) -
      Real.log Nbar = (n - δ - ε * relLogWageMean μ ε z s) - ε * s * (z j - ∫ i, z i ∂μ) := by
    intro j
    have h := log_laborDemand_sub (fun j => Real.exp_pos (wbar + s * z j)) hWi hNd hDw j
    have hw := relLogWage_eq (μ := μ) hz hB hε wbar s j
    rw [relLogWage] at hw
    rw [Real.log_exp] at h
    simp only [n, δ]
    linear_combination h + (-ε) * hw
  simp_rw [hpt]
  rw [integral_sq_affine hz hB, crossVar_family hz hB]
  ring

/-- Galí (2015), App. 6.1, p. 189 (**`∫ n(j)² = n² + ε_w² var_j w` up to third order**): in the
setting of `integral_sq_employment`, if aggregate employment is first order along the
perturbation (`n(s) = O(s)`) then `∫ n(j)² − n² − ε_w² var_j w = O(s³)`. -/
theorem integral_sq_employment_second_order [IsProbabilityMeasure μ] {z : J → ℝ}
    (hz : Measurable z) {B : ℝ} (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (wbar : ℝ)
    {Nd : ℝ → ℝ} (hNd : ∀ s, 0 < Nd s) {Nbar : ℝ}
    (hDw : ∀ s, 0 < wageDisp μ ε (fun j => Real.exp (wbar + s * z j)))
    (hn : (fun s => Real.log (∫ i, laborDemand μ ε (fun i => Real.exp (wbar + s * z i))
        (Nd s) i ∂μ) - Real.log Nbar) =O[𝓝 0] fun s => s ^ 1) :
    (fun s => ∫ j, (Real.log (laborDemand μ ε (fun i => Real.exp (wbar + s * z i)) (Nd s) j) -
        Real.log Nbar) ^ 2 ∂μ -
      (Real.log (∫ i, laborDemand μ ε (fun i => Real.exp (wbar + s * z i)) (Nd s) i ∂μ) -
        Real.log Nbar) ^ 2 - ε ^ 2 * crossVar μ (fun j => wbar + s * z j))
      =O[𝓝 0] fun s => s ^ 3 := by
  have hδ := log_wageDisp_isBigO_sq (μ := μ) hz hB hε wbar
  have hE := relLogWageMean_isBigO (μ := μ) hz hB hε
  have hD : (fun s => Real.log (wageDisp μ ε (fun j => Real.exp (wbar + s * z j))) +
      ε * relLogWageMean μ ε z s) =O[𝓝 0] fun s => s ^ 2 := hδ.add (hE.const_mul_left ε)
  have hS : (fun s => 2 * (Real.log (∫ i, laborDemand μ ε (fun i => Real.exp (wbar + s * z i))
        (Nd s) i ∂μ) - Real.log Nbar) - (Real.log (wageDisp μ ε (fun j => Real.exp
        (wbar + s * z j))) + ε * relLogWageMean μ ε z s)) =O[𝓝 0] fun s => s ^ 1 :=
    (hn.const_mul_left 2).sub (bigO_weaken (by norm_num : 1 ≤ 2) hD)
  refine ((bigO_mul hD hS).neg_left).congr_left fun s => ?_
  rw [integral_sq_employment hz hB hε wbar s (hNd s) (hDw s)]
  ring

/-! ### Lemma 2 for wages: the exact Calvo cross-section (App. 6.1, p. 192) -/

/-- Galí (2015), App. 6.1, p. 192 (setting of Lemma 2): an admissible cross-sectional
distribution of log wages is a probability measure with finite first and second moments. -/
def GoodDist (ν : Measure ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ Integrable (fun x => x) ν ∧ Integrable (fun x => x ^ 2) ν

/-- Galí (2015), App. 6.1, p. 192: the cross-sectional mean of log wages `m^w = ∫ w ν(dw)`. -/
noncomputable def crossMean (ν : Measure ℝ) : ℝ := ∫ x, x ∂ν

/-- Galí (2015), App. 6.1, p. 192: the cross-sectional variance of log wages `var_j w(j)`. -/
noncomputable def crossVarDist (ν : Measure ℝ) : ℝ := ∫ x, (x - crossMean ν) ^ 2 ∂ν

/-- Galí (2015), §6.1.2.2, p. 169 and App. 6.1, p. 192: the Calvo law of motion of the
cross-section of log wages, `ν_t = θ_w ν_{t−1} + (1 − θ_w) δ_{w*_t}` (derived from the
type-level Calvo lottery in `WageInflation`). -/
noncomputable def wageMix (θ : ℝ) (ν : Measure ℝ) (w : ℝ) : Measure ℝ :=
  ENNReal.ofReal θ • ν + ENNReal.ofReal (1 - θ) • Measure.dirac w

/-- Galí (2015), App. 6.1, p. 192 (restated from the Chapter 4 project): integrating against
`θ ν + (1 − θ) δ_w` gives `θ ∫ f dν + (1 − θ) f(w)`. -/
theorem integral_wageMix {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (w : ℝ)
    {f : ℝ → ℝ} (hf : Integrable f ν) :
    ∫ x, f x ∂(wageMix θ ν w) = θ * ∫ x, f x ∂ν + (1 - θ) * f w := by
  have hd : Integrable f (Measure.dirac w) := integrable_dirac (by simp)
  rw [wageMix, integral_add_measure (hf.smul_measure ENNReal.ofReal_ne_top)
      (hd.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul, smul_eq_mul]

/-- Galí (2015), App. 6.1, p. 192: `var = E w² − (E w)²` for an admissible cross-section. -/
theorem crossVarDist_eq {ν : Measure ℝ} (hg : GoodDist ν) :
    crossVarDist ν = ∫ x, x ^ 2 ∂ν - crossMean ν ^ 2 := by
  obtain ⟨hp, h1, h2⟩ := hg
  have hpt : ∀ x, (x - crossMean ν) ^ 2 = x ^ 2 + (-2 * crossMean ν) * x + crossMean ν ^ 2 :=
    fun x => by ring
  unfold crossVarDist
  simp_rw [hpt]
  have e1 := integral_add (μ := ν) (f := fun x => x ^ 2 + (-2 * crossMean ν) * x)
    (g := fun _ => crossMean ν ^ 2) (h2.add (h1.const_mul _)) (integrable_const _)
  have e2 := integral_add (μ := ν) (f := fun x => x ^ 2) (g := fun x => (-2 * crossMean ν) * x)
    h2 (h1.const_mul _)
  rw [e1, e2, integral_const_mul, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  unfold crossMean
  ring

/-- Galí (2015), App. 6.1, p. 192: the Calvo law of motion preserves admissibility. -/
theorem wageMix_good {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (w : ℝ)
    (hg : GoodDist ν) : GoodDist (wageMix θ ν w) := by
  obtain ⟨hp, hi1, hi2⟩ := hg
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · rw [wageMix, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ,
      measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      ← ENNReal.ofReal_add h0 (by linarith)]
    simp
  · exact (hi1.smul_measure ENNReal.ofReal_ne_top).add_measure
      ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
  · exact (hi2.smul_measure ENNReal.ofReal_ne_top).add_measure
      ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)

/-- Galí (2015), App. 6.1, p. 192 (exact): the mean log wage moves as
`m^w_t = θ_w m^w_{t−1} + (1 − θ_w) w*_t`, i.e. `Δm^w_t = (1 − θ_w)(w*_t − m^w_{t−1})`. -/
theorem wageMix_mean {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (w : ℝ)
    (hg : GoodDist ν) : crossMean (wageMix θ ν w) = θ * crossMean ν + (1 - θ) * w := by
  unfold crossMean
  exact integral_wageMix h0 h1 w hg.2.1

/-- Galí (2015), App. 6.1, p. 192 (**exact variance recursion**):
`var_t = θ_w var_{t−1} + θ_w(1 − θ_w)(w*_t − m^w_{t−1})²`. -/
theorem wageMix_var {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (w : ℝ)
    (hg : GoodDist ν) :
    crossVarDist (wageMix θ ν w)
      = θ * crossVarDist ν + θ * (1 - θ) * (w - crossMean ν) ^ 2 := by
  rw [crossVarDist_eq (wageMix_good h0 h1 w hg), crossVarDist_eq hg, wageMix_mean h0 h1 w hg]
  have h2 : ∫ x, x ^ 2 ∂(wageMix θ ν w) = θ * ∫ x, x ^ 2 ∂ν + (1 - θ) * w ^ 2 :=
    integral_wageMix h0 h1 w hg.2.2
  rw [h2]
  ring

/-- Galí (2015), App. 6.1, p. 192 (**exact, in terms of the change in the mean**): for
`θ_w < 1`, `var_t = θ_w var_{t−1} + (θ_w/(1 − θ_w)) (Δm^w_t)²`. -/
theorem wageMix_var_meanChange {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (w : ℝ)
    (hg : GoodDist ν) :
    crossVarDist (wageMix θ ν w)
      = θ * crossVarDist ν + θ / (1 - θ) * (crossMean (wageMix θ ν w) - crossMean ν) ^ 2 := by
  rw [wageMix_var h0 h1.le w hg, wageMix_mean h0 h1.le w hg]
  have : (1 : ℝ) - θ ≠ 0 := by linarith
  field_simp
  ring

/-- Galí (2015), App. 6.1, p. 192: along a Calvo sequence `ν_{t+1} = θ_w ν_t + (1−θ_w) δ_{w*_t}`
from an admissible `ν_0`, every cross-section is admissible. -/
theorem wage_good {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {ν : ℕ → Measure ℝ} {wstar : ℕ → ℝ}
    (hν : ∀ t, ν (t + 1) = wageMix θ (ν t) (wstar t)) (hg : GoodDist (ν 0)) :
    ∀ t, GoodDist (ν t) := by
  intro t
  induction t with
  | zero => exact hg
  | succ t ih =>
    rw [hν t]
    exact wageMix_good h0 h1 _ ih

/-- Galí (2015), App. 6.1, p. 192 (**exact recursion along the Calvo sequence**; `ν_0` is the
inherited cross-section): `var_{t+1} = θ_w var_t + (θ_w/(1−θ_w))(m^w_{t+1} − m^w_t)²`. -/
theorem wage_var_recursion {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) {ν : ℕ → Measure ℝ}
    {wstar : ℕ → ℝ} (hν : ∀ t, ν (t + 1) = wageMix θ (ν t) (wstar t)) (hg : GoodDist (ν 0))
    (t : ℕ) :
    crossVarDist (ν (t + 1))
      = θ * crossVarDist (ν t) + θ / (1 - θ) * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2 := by
  rw [hν t]
  exact wageMix_var_meanChange h0 h1 _ (wage_good h0 h1.le hν hg t)

/-- Galí (2015), App. 6.1, p. 192 (Lemma 2, partial sums; restated from the Chapter 4 project):
if `V_{t+1} = θ V_t + c q_t`, then
`∑_{t ≤ N} βᵗ V_{t+1} = θ V_0 + θβ ∑_{t < N} βᵗ V_{t+1} + c ∑_{t ≤ N} βᵗ q_t`. -/
theorem lemma2_partial {θ β c : ℝ} {V q : ℕ → ℝ} (hrec : ∀ t, V (t + 1) = θ * V t + c * q t)
    (N : ℕ) :
    ∑ t ∈ Finset.range (N + 1), β ^ t * V (t + 1)
      = θ * V 0 + θ * β * ∑ t ∈ Finset.range N, β ^ t * V (t + 1) +
        c * ∑ t ∈ Finset.range (N + 1), β ^ t * q t := by
  have h : ∀ t, β ^ (t + 1) * V (t + 1 + 1) = θ * β * (β ^ t * V (t + 1)) +
      c * (β ^ (t + 1) * q (t + 1)) := fun t => by
    rw [hrec (t + 1)]
    ring
  rw [Finset.sum_range_succ' (fun t => β ^ t * V (t + 1)),
    Finset.sum_range_succ' (fun t => β ^ t * q t), Finset.sum_congr rfl (fun t _ => h t),
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hrec 0]
  ring

/-- Galí (2015), App. 6.1, p. 192: a variance recursion `V_{t+1} = θ V_t + c q_t` with
nonnegative data stays nonnegative. -/
theorem lemma2_nonneg {θ c : ℝ} {V q : ℕ → ℝ} (hθ : 0 ≤ θ) (hc : 0 ≤ c) (hV0 : 0 ≤ V 0)
    (hq : ∀ t, 0 ≤ q t) (hrec : ∀ t, V (t + 1) = θ * V t + c * q t) : ∀ t, 0 ≤ V t := by
  intro t
  induction t with
  | zero => exact hV0
  | succ t ih =>
    rw [hrec t]
    have := mul_nonneg hc (hq t)
    have := mul_nonneg hθ ih
    linarith

/-- Galí (2015), App. 6.1, p. 192 (**Lemma 2, general form, exact**; restated from the
Chapter 4 project): if `V_{t+1} = θ V_t + c q_t` with `θ, β, c ≥ 0`, `βθ < 1`, `V_0 ≥ 0`,
`q ≥ 0` and `∑ βᵗ q_t` summable, then `∑ βᵗ V_{t+1}` converges to
`(θ V_0 + c ∑ βᵗ q_t)/(1 − βθ)`. -/
theorem lemma2_hasSum {θ β c : ℝ} {V q : ℕ → ℝ} (hθ : 0 ≤ θ) (hβ : 0 ≤ β) (hβθ : β * θ < 1)
    (hc : 0 ≤ c) (hV0 : 0 ≤ V 0) (hq : ∀ t, 0 ≤ q t)
    (hrec : ∀ t, V (t + 1) = θ * V t + c * q t) (hQ : Summable fun t => β ^ t * q t) :
    HasSum (fun t => β ^ t * V (t + 1))
      ((θ * V 0 + c * ∑' t, β ^ t * q t) / (1 - β * θ)) := by
  have hV := lemma2_nonneg hθ hc hV0 hq hrec
  have hf0 : ∀ t, 0 ≤ β ^ t * V (t + 1) := fun t => mul_nonneg (pow_nonneg hβ t) (hV _)
  have hq0 : ∀ t, 0 ≤ β ^ t * q t := fun t => mul_nonneg (pow_nonneg hβ t) (hq t)
  set Q := ∑' t, β ^ t * q t with hQdef
  have hQle : ∀ N, ∑ t ∈ Finset.range N, β ^ t * q t ≤ Q := fun N =>
    hQ.sum_le_tsum _ (fun i _ => hq0 i)
  have hpos : 0 < 1 - β * θ := by linarith
  have hQ0 : 0 ≤ Q := tsum_nonneg hq0
  have hbound : ∀ N, ∑ t ∈ Finset.range N, β ^ t * V (t + 1) ≤
      (θ * V 0 + c * Q) / (1 - β * θ) := by
    intro N
    cases N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact div_nonneg (add_nonneg (mul_nonneg hθ hV0) (mul_nonneg hc hQ0)) hpos.le
    | succ M =>
      rw [le_div_iff₀ hpos]
      have hp := lemma2_partial (β := β) hrec M
      have hmono : ∑ t ∈ Finset.range M, β ^ t * V (t + 1) ≤
          ∑ t ∈ Finset.range (M + 1), β ^ t * V (t + 1) := by
        rw [Finset.sum_range_succ]
        linarith [hf0 M]
      have h1 := mul_le_mul_of_nonneg_left hmono (mul_nonneg hθ hβ)
      have h2 := mul_le_mul_of_nonneg_left (hQle (M + 1)) hc
      nlinarith
  have hsum : Summable fun t => β ^ t * V (t + 1) := summable_of_sum_range_le hf0 hbound
  have hg : Summable fun t => β ^ t * V t := by
    refine (summable_nat_add_iff 1).1 ?_
    have : (fun t => β ^ (t + 1) * V (t + 1)) = fun t => β * (β ^ t * V (t + 1)) := by
      funext t
      ring
    rw [this]
    exact hsum.mul_left β
  have hg0 := hg.tsum_eq_zero_add
  have hshift : ∑' t, β ^ (t + 1) * V (t + 1) = β * ∑' t, β ^ t * V (t + 1) := by
    rw [← tsum_mul_left]
    congr 1
    funext t
    ring
  have hS : ∑' t, β ^ t * V (t + 1) = θ * ∑' t, β ^ t * V t + c * Q := by
    have : (fun t => β ^ t * V (t + 1)) = fun t => θ * (β ^ t * V t) + c * (β ^ t * q t) := by
      funext t
      rw [hrec t]
      ring
    rw [this, (hg.mul_left θ).tsum_add (hQ.mul_left c), tsum_mul_left, tsum_mul_left]
  rw [hg0, hshift] at hS
  simp only [pow_zero, one_mul] at hS
  have hval : ∑' t, β ^ t * V (t + 1) = (θ * V 0 + c * Q) / (1 - β * θ) := by
    rw [eq_div_iff hpos.ne']
    linarith
  rw [← hval]
  exact hsum.hasSum

/-- Galí (2015), App. 6.1, p. 192 (**Lemma 2 as used there, exact**): with no inherited
dispersion (`V_0 = 0`) and `V_{t+1} = θ V_t + (θ/(1−θ)) q_t`,
`∑ βᵗ V_{t+1} = θ/((1 − βθ)(1 − θ)) ∑ βᵗ q_t`. -/
theorem lemma2 {θ β : ℝ} {V q : ℕ → ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hV0 : V 0 = 0) (hq : ∀ t, 0 ≤ q t)
    (hrec : ∀ t, V (t + 1) = θ * V t + θ / (1 - θ) * q t) (hQ : Summable fun t => β ^ t * q t) :
    HasSum (fun t => β ^ t * V (t + 1))
      (θ / ((1 - β * θ) * (1 - θ)) * ∑' t, β ^ t * q t) := by
  have hβθ : β * θ < 1 := by nlinarith
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have h2 : 1 - β * θ ≠ 0 := by linarith
  have h := lemma2_hasSum hθ0 hβ0 hβθ (div_nonneg hθ0 (by linarith)) hV0.ge hq hrec hQ
  rw [hV0] at h
  convert h using 1
  field_simp
  ring

/-- Galí (2015), App. 6.1, p. 192 (**wage Lemma 2 with inherited dispersion, exact in
`Δm^w`**): along `ν_{t+1} = θ_w ν_t + (1 − θ_w) δ_{w*_t}` from an admissible `ν_0`,
`∑ βᵗ var_j w_{t+1}(j) = (θ_w var ν_0 + (θ_w/(1−θ_w)) ∑ βᵗ (Δm^w_t)²)/(1 − βθ_w)`. -/
theorem wage_lemma2_calvo_inherited {θ β : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {ν : ℕ → Measure ℝ} {wstar : ℕ → ℝ}
    (hν : ∀ t, ν (t + 1) = wageMix θ (ν t) (wstar t)) (hg : GoodDist (ν 0))
    (hQ : Summable fun t => β ^ t * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) :
    HasSum (fun t => β ^ t * crossVarDist (ν (t + 1)))
      ((θ * crossVarDist (ν 0) + θ / (1 - θ) *
        ∑' t, β ^ t * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) / (1 - β * θ)) := by
  have hβθ : β * θ < 1 := by nlinarith
  have hV0 : 0 ≤ crossVarDist (ν 0) := integral_nonneg fun x => sq_nonneg _
  have hc : (0 : ℝ) ≤ θ / (1 - θ) := div_nonneg hθ0 (by linarith)
  exact lemma2_hasSum (c := θ / (1 - θ)) (V := fun t => crossVarDist (ν t)) hθ0 hβ0 hβθ hc hV0
    (fun t => sq_nonneg _) (wage_var_recursion hθ0 hθ1 hν hg) hQ

/-- Galí (2015), App. 6.1, p. 192 (**wage Lemma 2, exact in `Δm^w`**): with no inherited
wage dispersion, `∑ βᵗ var_j w_t(j) = θ_w/((1 − βθ_w)(1 − θ_w)) ∑ βᵗ (Δm^w_t)²`. -/
theorem wage_lemma2_calvo {θ β : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {ν : ℕ → Measure ℝ} {wstar : ℕ → ℝ} (hν : ∀ t, ν (t + 1) = wageMix θ (ν t) (wstar t))
    (hg : GoodDist (ν 0)) (hV0 : crossVarDist (ν 0) = 0)
    (hQ : Summable fun t => β ^ t * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) :
    HasSum (fun t => β ^ t * crossVarDist (ν (t + 1)))
      (θ / ((1 - β * θ) * (1 - θ)) *
        ∑' t, β ^ t * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) :=
  lemma2 (V := fun t => crossVarDist (ν t))
    (q := fun t => (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) hθ0 hθ1 hβ0 hβ1 hV0
    (fun _ => sq_nonneg _) (wage_var_recursion hθ0 hθ1 hν hg) hQ

/-! ### `Δm^w = π^w` to first order (App. 6.1, p. 192) -/

/-- Galí (2015), App. 6.1, p. 192 (the log wage index versus the mean): along
`w(j) = w̄ + s z(j)`, `log W(s) = E_j w(j) + ((1 − ε)/2) var_j w(j) + O(s³)`. -/
theorem logWageIndex_second_order [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (wbar : ℝ) :
    (fun s => Real.log (cesIndex μ ε (fun j => Real.exp (wbar + s * z j))) -
        (wbar + s * ∫ j, z j ∂μ) - (1 - ε) / 2 * crossVar μ (fun j => wbar + s * z j))
      =O[𝓝 0] fun s => s ^ 3 := by
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have heq : (fun s => Real.log (cesIndex μ ε (fun j => Real.exp (wbar + s * z j))) -
        (wbar + s * ∫ j, z j ∂μ) - (1 - ε) / 2 * crossVar μ (fun j => wbar + s * z j))
      = fun s => (1 - ε)⁻¹ * (cgf z μ ((1 - ε) * s) - (∫ j, z j ∂μ) * ((1 - ε) * s) -
          (∫ j, (z j - ∫ i, z i ∂μ) ^ 2 ∂μ) / 2 * ((1 - ε) * s) ^ 2) := by
    funext s
    rw [cesIndex_family hz hB hε, Real.log_exp, crossVar_family hz hB]
    field_simp
    ring
  rw [heq]
  exact (cgf_taylor_comp hz hB _).const_mul_left _

/-- Galí (2015), App. 6.1, p. 192 (**`Δm^w_t = π^w_t` to first order**): for log-wage families
`w_k(j) = w̄ + s z_k(j)` at two consecutive dates, wage inflation `π^w = log W_1 − log W_0`
(CES indices) and the change in the cross-sectional mean `Δm^w = E w_1 − E w_0` differ by
`O(s²)`. -/
theorem wageInflation_sub_meanChange [IsProbabilityMeasure μ] {z₀ z₁ : J → ℝ}
    (hz₀ : Measurable z₀) (hz₁ : Measurable z₁) {B₀ B₁ : ℝ} (hB₀ : ∀ j, |z₀ j| ≤ B₀)
    (hB₁ : ∀ j, |z₁ j| ≤ B₁) (hε : ε ≠ 1) (wbar : ℝ) :
    (fun s => (Real.log (cesIndex μ ε (fun j => Real.exp (wbar + s * z₁ j))) -
        Real.log (cesIndex μ ε (fun j => Real.exp (wbar + s * z₀ j)))) -
        ((wbar + s * ∫ j, z₁ j ∂μ) - (wbar + s * ∫ j, z₀ j ∂μ))) =O[𝓝 0] fun s => s ^ 2 := by
  have e₁ := (bigO_weaken (by norm_num : 2 ≤ 3)
    (logWageIndex_second_order (μ := μ) hz₁ hB₁ hε wbar)).add
    ((crossVar_family_isBigO (μ := μ) hz₁ hB₁ wbar).const_mul_left ((1 - ε) / 2))
  have e₀ := (bigO_weaken (by norm_num : 2 ≤ 3)
    (logWageIndex_second_order (μ := μ) hz₀ hB₀ hε wbar)).add
    ((crossVar_family_isBigO (μ := μ) hz₀ hB₀ wbar).const_mul_left ((1 - ε) / 2))
  refine (e₁.sub e₀).congr_left fun s => ?_
  ring

/-- Galí (2015), App. 6.1, p. 192 (**`(π^w_t)² = (Δm^w_t)² + O(s³)`**): the squares of wage
inflation and of the change in the mean log wage agree to second order, so the wage Lemma 2
(exact in `Δm^w`) holds with `π^w` to second order. -/
theorem wageInflation_sq_sub_meanChange_sq [IsProbabilityMeasure μ] {z₀ z₁ : J → ℝ}
    (hz₀ : Measurable z₀) (hz₁ : Measurable z₁) {B₀ B₁ : ℝ} (hB₀ : ∀ j, |z₀ j| ≤ B₀)
    (hB₁ : ∀ j, |z₁ j| ≤ B₁) (hε : ε ≠ 1) (wbar : ℝ) :
    (fun s => (Real.log (cesIndex μ ε (fun j => Real.exp (wbar + s * z₁ j))) -
        Real.log (cesIndex μ ε (fun j => Real.exp (wbar + s * z₀ j)))) ^ 2 -
        ((wbar + s * ∫ j, z₁ j ∂μ) - (wbar + s * ∫ j, z₀ j ∂μ)) ^ 2) =O[𝓝 0]
      fun s => s ^ 3 := by
  have hD := wageInflation_sub_meanChange (μ := μ) hz₀ hz₁ hB₀ hB₁ hε wbar
  have hm : (fun s => (wbar + s * ∫ j, z₁ j ∂μ) - (wbar + s * ∫ j, z₀ j ∂μ)) =O[𝓝 0]
      fun s => s ^ 1 :=
    (monomial_isBigO ((∫ j, z₁ j ∂μ) - ∫ j, z₀ j ∂μ) 1).congr_left fun s => by ring
  have hsum := (bigO_weaken (by norm_num : 1 ≤ 2) hD).add (hm.const_mul_left 2)
  refine (bigO_mul hD hsum).congr_left fun s => ?_
  ring

end Gali.StickyWagesPrices.WageDispersion
