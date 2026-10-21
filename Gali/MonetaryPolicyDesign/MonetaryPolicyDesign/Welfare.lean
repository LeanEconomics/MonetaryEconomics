/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The welfare loss function

Galí (2015), Chapter 4, §4.4 (pp. 110–111) and Appendix 4.1 (pp. 117–119): the
second-order approximation to the representative household's welfare around an efficient
steady state, Lemmas 1 and 2, the loss function `W`, the average loss `L`, and the comparative
statics of the loss weights.

## Two layers

* **(A) exact algebra.** `secondOrderUtility_eq`: given an efficient steady state
  (`U_n N = −(1 − α) U_c C`, `efficiency_iff`), the exact employment identity
  `(1 − α) n = y − a + d` and `ŷ^n = ψ_ya a`, the book's second-order polynomial in log
  deviations equals
  `−(U_c C/2)[(σ + (φ+α)/(1−α))(y − ŷ^n)² + (ε/Θ) var_i p(i)] + t.i.p.` plus the explicit
  higher-order terms `K((ε/2Θ) var − d) − K((1+φ)/(2(1−α))(2(y−a)d + d²) + d z)`; the terms
  independent of policy `tip` are an explicit function of the shocks `a`, `z` only.
* **(B) the analytic bridge.** `period_utility_second_order`: for `U(C, N; Z) = (u(C) + w(N))Z`
  with `u`, `w` of class `C³` near the steady state, along any one-parameter family of
  allocations of size `s` (log deviations `O(s)`, cross-sectional price variance `O(s²)`,
  Lemma 1), period utility equals the quadratic form plus t.i.p. up to `O(s³)`
  (`Asymptotics.IsBigO`), via Mathlib's one-dimensional Taylor theorem (`taylor_two`,
  `logdev_taylor`, `exp_taylor_two`). `period_utility_second_order_dispersion` discharges the
  Lemma 1 hypotheses for an actual family of price distributions;
  `period_utility_normalised` is the book's display divided by `U_c C`.

## Lemma 1 and Lemma 2

* Lemma 1 (`dispersion_second_order`, restated from the Chapter 3 project):
  `d = (ε/(2Θ)) var_i p(i) + O(s³)`.
* Lemma 2 is proved **exactly** for the Calvo cross-section
  `ν_t = θ ν_{t−1} + (1 − θ) δ_{p*_t}` of log prices with mean `m_t`: `calvoMix_mean`,
  `calvoMix_var` give `Δm_t = (1 − θ)(p*_t − m_{t−1})` and
  `var_t = θ var_{t−1} + θ(1 − θ)(p*_t − m_{t−1})²`, hence `var_t = θ var_{t−1} + (θ/(1−θ))(Δm_t)²`
  (`calvoMix_var_meanChange`, `calvo_var_recursion`). Then `lemma2_hasSum` (any inherited
  dispersion, Yun 2005), `lemma2`, `lemma2_calvo`:
  `∑ βᵗ var_t = θ/((1 − βθ)(1 − θ)) ∑ βᵗ (Δm_t)²`, with convergence proved. The link to
  inflation is second order: `inflation_sub_meanChange` (`π_t − Δm_t = O(s²)`) and
  `inflation_sq_sub_meanChange_sq` (`π_t² − (Δm_t)² = O(s³)`).

## `W`, `L` and the weights

* `welfare_eq_loss`, `welfare_eq_loss_calvo`: `W = ½ ∑ βᵗ [(σ + (φ+α)/(1−α)) ỹ² + (ε/λ) π²]`
  (with `π = Δm`), exact given the Calvo recursion; `welfare_stationary`: `W = L/(1 − β)`.
* `gapCoeff_strictMono_sigma`, `gapCoeff_strictMono_phi`, `gapCoeff_strictMonoOn_alpha`: the
  gap coefficient increases in `σ`, `φ`, `α`. `inflWeight_strictMonoOn_eps`,
  `inflWeight_strictMonoOn_theta`: `ε/λ` increases in `ε` and `θ`.
* **C4-3.** The weight of the gap *relative* to inflation is `κ/ε` (`relWeight_eq_ratio`); its
  slope in `α` has the constant sign of `(1 − σ) − (σ + φ)(ε − 1)` (`relWeight_sub`), so it
  is strictly decreasing when `(σ + φ)(ε − 1) > 1 − σ` (`relWeight_strictAntiOn_alpha`, the
  baseline: `relWeight_baseline_strictAnti`, values `relWeight_baseline`) and increasing
  otherwise (`relWeight_strictMonoOn_alpha`). `relWeight_not_increasing_alpha` refutes the
  printed "relative weight … increasing in α" at the baseline.

-/

namespace Gali.MonetaryPolicyDesign.Welfare

open MeasureTheory ProbabilityTheory Asymptotics Filter Topology

variable {G : Type*} [MeasurableSpace G]

/-! ### Lemma 1: price dispersion to second order (restated from the Chapter 3 project) -/

/-- Galí (2015), p. 53 (restated from the Chapter 3 project): the CES price index
`P = (∫ P(i)^{1−ε} di)^{1/(1−ε)}`. -/
noncomputable def priceIndex (μ : Measure G) (ε : ℝ) (P : G → ℝ) : ℝ :=
  (∫ i, P i ^ (1 - ε) ∂μ) ^ (1 - ε)⁻¹

/-- Galí (2015), App. 4.1, p. 118 (restated from the Chapter 3 project): the dispersion term
`d = (1 − α) log ∫ (P(i)/P)^{−ε/(1−α)} di`. -/
noncomputable def dispersion (μ : Measure G) (α ε : ℝ) (P : G → ℝ) : ℝ :=
  (1 - α) * Real.log (∫ i, (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) ∂μ)

/-- Galí (2015), App. 4.1, p. 118: `Θ = (1 − α)/(1 − α + αε)`. -/
noncomputable def bigTheta (α ε : ℝ) : ℝ := (1 - α) / (1 - α + α * ε)

/-- Galí (2015), App. 4.1, p. 118 (restated from the Chapter 3 project): the cross-sectional
variance `var_i p(i) = ∫ (p(i) − ∫ p)² di`. -/
noncomputable def crossVar (μ : Measure G) (p : G → ℝ) : ℝ :=
  ∫ i, (p i - ∫ j, p j ∂μ) ^ 2 ∂μ

variable {μ : Measure G} {α ε : ℝ}

/-- Restated from the Chapter 3 project.
Galí (2015), App. 3.4, p. 85: for a bounded measurable `z` on a probability space, every
`exp(t z)` is integrable (so the moment-generating function is finite everywhere). -/
theorem integrable_exp_mul [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ i, |z i| ≤ B) (t : ℝ) : Integrable (fun i => Real.exp (t * z i)) μ := by
  refine Integrable.of_bound ((measurable_const.mul hz).exp.aestronglyMeasurable)
    (Real.exp (|t| * B)) (Filter.Eventually.of_forall fun i => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  calc t * z i ≤ |t * z i| := le_abs_self _
    _ = |t| * |z i| := abs_mul _ _
    _ ≤ |t| * B := mul_le_mul_of_nonneg_left (hB i) (abs_nonneg t)

/-- Restated from the Chapter 3 project.
Galí (2015), App. 3.4, p. 85: for bounded `z`, the cumulant-generating function is
analytic on all of `ℝ` (the domain of finiteness of the mgf is `ℝ`). -/
theorem interior_integrableExpSet [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ i, |z i| ≤ B) : interior (integrableExpSet z μ) = Set.univ := by
  have : integrableExpSet z μ = Set.univ :=
    Set.eq_univ_of_forall fun t => integrable_exp_mul hz hB t
  rw [this, interior_univ]

/-- Restated from the Chapter 3 project.
Galí (2015), App. 3.4, pp. 85–86: **second-order Taylor expansion of the cumulant
generating function** of a bounded `z`:
`K(u) = (E z) u + (var z/2) u² + O(u³)` as `u → 0`. -/
theorem cgf_taylor [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ i, |z i| ≤ B) :
    (fun u => cgf z μ u - (∫ i, z i ∂μ) * u - (∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) / 2 * u ^ 2)
      =O[nhds 0] fun u => u ^ 3 := by
  have hint := interior_integrableExpSet (μ := μ) hz hB
  have hAn : AnalyticOnNhd ℝ (cgf z μ) Set.univ := by
    have := analyticOnNhd_cgf (X := z) (μ := μ)
    rwa [hint] at this
  have hCD : ContDiff ℝ 3 (cgf z μ) := hAn.contDiff
  have hT := taylor_isLittleO_univ (x₀ := 0) hCD
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet z μ) := by
    rw [hint]
    trivial
  have hd1 : deriv (cgf z μ) 0 = ∫ i, z i ∂μ := by
    rw [deriv_cgf_zero h0]
    simp
  have hd2 : iteratedDeriv 2 (cgf z μ) 0 = ∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ := by
    rw [iteratedDeriv_two_cgf_eq_integral h0, hd1, mgf_zero]
    simp
  have heq : (fun u => cgf z μ u - (∫ i, z i ∂μ) * u -
      (∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) / 2 * u ^ 2)
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
  exact hT.isBigO.add ((Asymptotics.isBigO_refl _ _).const_mul_left _)

/-- Restated from the Chapter 3 project.
Galí (2015), App. 3.4, pp. 85–86: the Taylor remainder of `K` along a ray,
`K(a s) − (E z)(a s) − (var z/2)(a s)² = O(s³)` as `s → 0`, for every slope `a`. -/
theorem cgf_taylor_comp [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ i, |z i| ≤ B) (a : ℝ) :
    (fun s => cgf z μ (a * s) - (∫ i, z i ∂μ) * (a * s) -
      (∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) / 2 * (a * s) ^ 2) =O[nhds 0] fun s => s ^ 3 := by
  have hR := cgf_taylor (μ := μ) hz hB
  have ht : Filter.Tendsto (fun s : ℝ => a * s) (nhds 0) (nhds 0) := by
    have := (Filter.tendsto_id (x := nhds (0 : ℝ))).const_mul a
    simpa using this
  refine (hR.comp_tendsto ht).trans ?_
  have : ((fun u : ℝ => u ^ 3) ∘ fun s => a * s) = fun s => a ^ 3 * s ^ 3 := by
    funext s
    simp only [Function.comp_apply]
    ring
  rw [this]
  exact (Asymptotics.isBigO_refl _ _).const_mul_left _

/-- Restated from the Chapter 3 project.
Galí (2015), App. 3.4, p. 85: along the family `P(i) = exp(p̄ + s z(i))` the log price
index is `p = p̄ + K((1 − ε)s)/(1 − ε)`, i.e. `P = exp(p̄ + K((1−ε)s)/(1−ε))`. -/
theorem priceIndex_family [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ i, |z i| ≤ B) (hε : ε ≠ 1) (pbar s : ℝ) :
    priceIndex μ ε (fun i => Real.exp (pbar + s * z i))
      = Real.exp (pbar + cgf z μ ((1 - ε) * s) / (1 - ε)) := by
  have hM : ∀ t, 0 < mgf z μ t := fun t => mgf_pos (integrable_exp_mul hz hB t)
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have hsum : ∫ i, Real.exp (pbar + s * z i) ^ (1 - ε) ∂μ
      = Real.exp ((1 - ε) * pbar) * mgf z μ ((1 - ε) * s) := by
    have : ∀ i, Real.exp (pbar + s * z i) ^ (1 - ε)
        = Real.exp ((1 - ε) * pbar) * Real.exp ((1 - ε) * s * z i) := by
      intro i
      rw [← Real.exp_mul, ← Real.exp_add]
      congr 1
      ring
    simp_rw [this]
    rw [integral_const_mul]
    rfl
  unfold priceIndex
  rw [hsum, Real.rpow_def_of_pos (mul_pos (Real.exp_pos _) (hM _)),
    Real.log_mul (Real.exp_pos _).ne' (hM _).ne', Real.log_exp, cgf]
  congr 1
  field_simp

/-- Restated from the Chapter 3 project.
Galí (2015), App. 3.4, p. 85: along the family `P(i) = exp(p̄ + s z(i))`, the dispersion
term is exactly `d(s) = (1 − α) K(−εs/(1−α)) + (ε/(1−ε)) K((1−ε)s)`, with `K` the cumulant
generating function of `z`. -/
theorem dispersion_family_eq [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ i, |z i| ≤ B) (hε : ε ≠ 1) (hα : α ≠ 1) (pbar s : ℝ) :
    dispersion μ α ε (fun i => Real.exp (pbar + s * z i))
      = (1 - α) * cgf z μ (-ε / (1 - α) * s) + ε / (1 - ε) * cgf z μ ((1 - ε) * s) := by
  have hM : ∀ t, 0 < mgf z μ t := fun t => mgf_pos (integrable_exp_mul hz hB t)
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have hsubα : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have hidx : priceIndex μ ε (fun i => Real.exp (pbar + s * z i))
      = Real.exp (pbar + Real.log (mgf z μ ((1 - ε) * s)) / (1 - ε)) :=
    priceIndex_family hz hB hε pbar s
  have hrel : ∀ i, (Real.exp (pbar + s * z i) /
      Real.exp (pbar + Real.log (mgf z μ ((1 - ε) * s)) / (1 - ε))) ^ (-ε / (1 - α))
      = Real.exp (ε / (1 - α) * (Real.log (mgf z μ ((1 - ε) * s)) / (1 - ε))) *
        Real.exp (-ε / (1 - α) * s * z i) := by
    intro i
    rw [← Real.exp_sub, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  rw [dispersion, hidx]
  simp_rw [hrel]
  rw [integral_const_mul]
  have hm2 : ∫ i, Real.exp (-ε / (1 - α) * s * z i) ∂μ = mgf z μ (-ε / (1 - α) * s) := rfl
  rw [hm2, Real.log_mul (Real.exp_pos _).ne' (hM _).ne', Real.log_exp, cgf, cgf]
  field_simp
  ring

/-- Restated from the Chapter 3 project.
Galí (2015), App. 3.4, p. 86: the cross-sectional variance of `p(i) = p̄ + s z(i)` is
`s² var z`. -/
theorem crossVar_family [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ i, |z i| ≤ B) (pbar s : ℝ) :
    crossVar μ (fun i => pbar + s * z i) = s ^ 2 * ∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ := by
  have hzI : Integrable z μ :=
    Integrable.of_bound hz.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun i => by rw [Real.norm_eq_abs]; exact hB i)
  have hmean : ∫ i, (pbar + s * z i) ∂μ = pbar + s * ∫ i, z i ∂μ := by
    rw [integral_add (integrable_const _) (hzI.const_mul s), integral_const, integral_const_mul]
    simp
  unfold crossVar
  beta_reduce
  rw [hmean]
  have hpt : ∀ i, (pbar + s * z i - (pbar + s * ∫ j, z j ∂μ)) ^ 2
      = s ^ 2 * (z i - ∫ j, z j ∂μ) ^ 2 := fun i => by ring
  simp_rw [hpt]
  rw [integral_const_mul]

/-- Restated from the Chapter 3 project.
Galí (2015), App. 3.4, pp. 85–86 (**second-order approximation of price dispersion**):
for any probability space of goods, any bounded measurable `z` and any level `p̄`, the family
of price distributions `p(i) = p̄ + s z(i)` (with `P` its CES index, so the index condition
holds) satisfies `d(s) = (ε/(2Θ)) var_i p(i) + O(s³)` as `s → 0`,
`Θ = (1 − α)/(1 − α + αε)`. -/
theorem dispersion_second_order [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ i, |z i| ≤ B) (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) (pbar : ℝ) :
    (fun s => dispersion μ α ε (fun i => Real.exp (pbar + s * z i)) -
        ε / (2 * bigTheta α ε) * crossVar μ (fun i => pbar + s * z i))
      =O[nhds 0] fun s => s ^ 3 := by
  have hcomp := cgf_taylor_comp (μ := μ) hz hB
  have hsubε : (1 : ℝ) - ε ≠ 0 := by linarith
  have hsubα : (1 : ℝ) - α ≠ 0 := by linarith
  have hden : 1 - α + α * ε ≠ 0 := by nlinarith
  have heq : (fun s => dispersion μ α ε (fun i => Real.exp (pbar + s * z i)) -
        ε / (2 * bigTheta α ε) * crossVar μ (fun i => pbar + s * z i))
      = fun s => (1 - α) * (cgf z μ (-ε / (1 - α) * s) - (∫ i, z i ∂μ) * (-ε / (1 - α) * s) -
          (∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) / 2 * (-ε / (1 - α) * s) ^ 2) +
        ε / (1 - ε) * (cgf z μ ((1 - ε) * s) - (∫ i, z i ∂μ) * ((1 - ε) * s) -
          (∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) / 2 * ((1 - ε) * s) ^ 2) := by
    funext s
    rw [dispersion_family_eq hz hB (by linarith) (by linarith), crossVar_family hz hB, bigTheta]
    field_simp
    ring
  rw [heq]
  exact ((hcomp _).const_mul_left _).add ((hcomp _).const_mul_left _)

/-- Restated from the Chapter 3 project.
Galí (2015), p. 59 and App. 3.4: along the family `p(i) = p̄ + s z(i)`, `d(s) = O(s²)`. -/
theorem dispersion_family_isBigO_sq [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ i, |z i| ≤ B) (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) (pbar : ℝ) :
    (fun s => dispersion μ α ε (fun i => Real.exp (pbar + s * z i))) =O[nhds 0]
      fun s => s ^ 2 := by
  have h3 := dispersion_second_order (μ := μ) hz hB hε hα0 hα1 pbar
  have h32 : (fun s : ℝ => s ^ 3) =O[nhds 0] fun s => s ^ 2 :=
    (Asymptotics.isLittleO_pow_pow (by norm_num : 2 < 3)).isBigO
  have hq : (fun s => ε / (2 * bigTheta α ε) * crossVar μ (fun i => pbar + s * z i))
      =O[nhds 0] fun s => s ^ 2 := by
    have : (fun s => ε / (2 * bigTheta α ε) * crossVar μ (fun i => pbar + s * z i))
        = fun s => (ε / (2 * bigTheta α ε) * ∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) * s ^ 2 := by
      funext s
      rw [crossVar_family hz hB]
      ring
    rw [this]
    exact (Asymptotics.isBigO_refl _ _).const_mul_left _
  have := (h3.trans h32).add hq
  simpa using this


/-- Galí (2015), App. 4.1, p. 119 (Lemma 2's first-order link, the log index versus the mean):
along `p(i) = p̄ + s z(i)` the log CES price index satisfies
`log P(s) = E_i p(i) + ((1 − ε)/2) var_i p(i) + O(s³)`; in particular `log P − E_i p = O(s²)`. -/
theorem logPriceIndex_second_order [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ i, |z i| ≤ B) (hε : ε ≠ 1) (pbar : ℝ) :
    (fun s => Real.log (priceIndex μ ε (fun i => Real.exp (pbar + s * z i))) -
        (pbar + s * ∫ i, z i ∂μ) - (1 - ε) / 2 * crossVar μ (fun i => pbar + s * z i))
      =O[𝓝 0] fun s => s ^ 3 := by
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have heq : (fun s => Real.log (priceIndex μ ε (fun i => Real.exp (pbar + s * z i))) -
        (pbar + s * ∫ i, z i ∂μ) - (1 - ε) / 2 * crossVar μ (fun i => pbar + s * z i))
      = fun s => (1 - ε)⁻¹ * (cgf z μ ((1 - ε) * s) - (∫ i, z i ∂μ) * ((1 - ε) * s) -
          (∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) / 2 * ((1 - ε) * s) ^ 2) := by
    funext s
    rw [priceIndex_family hz hB hε, Real.log_exp, crossVar_family hz hB]
    field_simp
    ring
  rw [heq]
  exact (cgf_taylor_comp hz hB _).const_mul_left _

/-! ### Bookkeeping for orders of magnitude -/

/-- Orders of magnitude multiply: `f = O(sᵃ)` and `g = O(sᵇ)` give `f g = O(sᵃ⁺ᵇ)`
(used throughout App. 4.1, Galí 2015, pp. 117–119). -/
theorem bigO_mul {f g : ℝ → ℝ} {a b : ℕ} (hf : f =O[𝓝 0] fun s => s ^ a)
    (hg : g =O[𝓝 0] fun s => s ^ b) :
    (fun s => f s * g s) =O[𝓝 0] fun s => s ^ (a + b) := by
  have := hf.mul hg
  simpa [pow_add] using this

/-- Higher orders are smaller near `0`: `O(sᵇ) ⊆ O(sᵃ)` for `a ≤ b` (Galí 2015, App. 4.1,
"ignoring terms of third or higher order", p. 118). -/
theorem bigO_weaken {f : ℝ → ℝ} {a b : ℕ} (hab : a ≤ b) (hf : f =O[𝓝 0] fun s => s ^ b) :
    f =O[𝓝 0] fun s => s ^ a := by
  rcases hab.lt_or_eq with h | h
  · exact hf.trans (isLittleO_pow_pow h).isBigO
  · rw [h]
    exact hf

/-- A process that is `O(s)` tends to `0` (Galí 2015, App. 4.1: the economy stays in a
neighbourhood of the steady state). -/
theorem tendsto_zero_of_bigO {f : ℝ → ℝ} (hf : f =O[𝓝 0] fun s => s ^ 1) :
    Tendsto f (𝓝 0) (𝓝 0) := by
  have h : Tendsto (fun s : ℝ => s ^ 1) (𝓝 0) (𝓝 0) := by
    simp only [pow_one]
    exact tendsto_id
  exact hf.trans_tendsto h

/-! ### One-dimensional Taylor expansions -/

/-- Galí (2015), App. 4.1, p. 117 (**second-order Taylor expansion with a cubic remainder**):
if `f` is `C³` near `x₀`, then
`f x = f x₀ + f'(x₀)(x − x₀) + f''(x₀)/2 (x − x₀)² + O((x − x₀)³)`.
This is Mathlib's one-dimensional Taylor theorem (`taylor_isLittleO`) at order three on an open
ball, with the cubic Taylor term absorbed into the `O`. -/
theorem taylor_two {f : ℝ → ℝ} {x₀ : ℝ} (hf : ContDiffAt ℝ 3 f x₀) :
    (fun x => f x - f x₀ - deriv f x₀ * (x - x₀) - iteratedDeriv 2 f x₀ / 2 * (x - x₀) ^ 2)
      =O[𝓝 x₀] fun x => (x - x₀) ^ 3 := by
  obtain ⟨U, hU, hfU⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hs : ContDiffOn ℝ 3 f (Metric.ball x₀ r) := hfU.mono hball
  have hT := taylor_isLittleO (convex_ball x₀ r) (Metric.mem_ball_self hr) hs
  rw [nhdsWithin_eq_nhds.2 (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))] at hT
  have hx0 := Metric.mem_ball_self hr (x := x₀)
  have e1 := iteratedDerivWithin_of_isOpen (n := 1) (f := f) Metric.isOpen_ball hx0
  have e2 := iteratedDerivWithin_of_isOpen (n := 2) (f := f) Metric.isOpen_ball hx0
  have e3 := iteratedDerivWithin_of_isOpen (n := 3) (f := f) Metric.isOpen_ball hx0
  have heq : (fun x => f x - f x₀ - deriv f x₀ * (x - x₀) -
      iteratedDeriv 2 f x₀ / 2 * (x - x₀) ^ 2)
      = fun x => (f x - taylorWithinEval f 3 (Metric.ball x₀ r) x₀ x) +
        iteratedDeriv 3 f x₀ / 6 * (x - x₀) ^ 3 := by
    funext x
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDerivWithin_zero, e1, e2,
      e3, iteratedDeriv_one, smul_eq_mul]
    norm_num [Nat.factorial]
    ring
  rw [heq]
  exact hT.isBigO.add ((isBigO_refl _ _).const_mul_left _)

/-- Galí (2015), App. 4.1, p. 117: `e^x = 1 + x + x²/2 + O(x³)`, the expansion behind
`(X_t − X)/X ≃ x_t + x_t²/2`. -/
theorem exp_taylor_two :
    (fun x => Real.exp x - 1 - x - x ^ 2 / 2) =O[𝓝 0] fun x => x ^ 3 := by
  have h := taylor_two (f := Real.exp) (x₀ := 0) Real.contDiff_exp.contDiffAt
  have h2 : iteratedDeriv 2 Real.exp 0 = 1 := by
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.exp_zero]
  simp only [Real.deriv_exp, Real.exp_zero, h2, sub_zero] at h
  convert h using 2 with x
  ring

/-- Galí (2015), App. 4.1, p. 117: `e^x − 1 = O(x)`. -/
theorem exp_sub_one_bigO : (fun x => Real.exp x - 1) =O[𝓝 0] fun x => x ^ 1 := by
  have h3 := bigO_weaken (by norm_num : 1 ≤ 3) exp_taylor_two
  have h1 : (fun x : ℝ => x) =O[𝓝 0] fun x => x ^ 1 := by simpa using isBigO_refl _ _
  have h2 : (fun x : ℝ => x ^ 2 / 2) =O[𝓝 0] fun x => x ^ 1 :=
    bigO_weaken (by norm_num : 1 ≤ 2) ((isBigO_refl _ _).const_mul_left (1 / 2) |>.congr_left
      (fun x => by ring))
  have := (h3.add h1).add h2
  refine this.congr_left fun x => ?_
  ring

/-- Galí (2015), App. 4.1, p. 117 (**second-order expansion in log deviations**): if `f` is
`C³` near the steady state `X`, then with `X_t = X e^{x}`,
`f(X_t) − f(X) = f'(X) X (x + x²/2) + f''(X) X² x²/2 + O(x³)`. -/
theorem logdev_taylor {f : ℝ → ℝ} {X : ℝ} (hf : ContDiffAt ℝ 3 f X) :
    (fun x => f (X * Real.exp x) - f X - deriv f X * X * (x + x ^ 2 / 2) -
        iteratedDeriv 2 f X / 2 * X ^ 2 * x ^ 2) =O[𝓝 0] fun x => x ^ 3 := by
  have hT := taylor_two hf
  have hg : Tendsto (fun x => X * Real.exp x) (𝓝 0) (𝓝 X) := by
    have := ((Real.continuous_exp.tendsto 0).const_mul X)
    simpa using this
  have hE1 := exp_sub_one_bigO
  have h1 : (fun x => f (X * Real.exp x) - f X - deriv f X * (X * Real.exp x - X) -
      iteratedDeriv 2 f X / 2 * (X * Real.exp x - X) ^ 2) =O[𝓝 0] fun x => x ^ 3 := by
    refine (hT.comp_tendsto hg).trans ?_
    have hc : (fun x => (X * Real.exp x - X) ^ 3) =O[𝓝 0] fun x => x ^ 3 := by
      have : (fun x => (X * Real.exp x - X) ^ 3) = fun x => X ^ 3 * (Real.exp x - 1) ^ 3 := by
        funext x
        ring
      rw [this]
      have := hE1.pow 3
      simp only [← pow_mul] at this
      exact this.const_mul_left _
    exact hc
  have h2 : (fun x => deriv f X * X * (Real.exp x - 1 - x - x ^ 2 / 2)) =O[𝓝 0]
      fun x => x ^ 3 := exp_taylor_two.const_mul_left _
  have hA : (fun x => Real.exp x - 1 - x) =O[𝓝 0] fun x => x ^ 2 := by
    have : (fun x : ℝ => x ^ 2 / 2) =O[𝓝 0] fun x => x ^ 2 :=
      (isBigO_refl _ _).const_mul_left (1 / 2) |>.congr_left (fun x => by ring)
    refine ((bigO_weaken (by norm_num : 2 ≤ 3) exp_taylor_two).add this).congr_left
      fun x => ?_
    ring
  have hB : (fun x => Real.exp x - 1 + x) =O[𝓝 0] fun x => x ^ 1 :=
    hE1.add (by simpa using isBigO_refl (fun x : ℝ => x) (𝓝 0))
  have h3 : (fun x => iteratedDeriv 2 f X / 2 * X ^ 2 *
      ((Real.exp x - 1 - x) * (Real.exp x - 1 + x))) =O[𝓝 0] fun x => x ^ 3 :=
    (bigO_mul hA hB).const_mul_left _
  refine ((h1.add h2).add h3).congr_left fun x => ?_
  ring

/-! ### Layer (A): the exact algebra of App. 4.1 -/

/-- Galí (2015), p. 111 and App. 4.1, p. 118: the output-gap coefficient of the loss,
`σ + (φ + α)/(1 − α)`. -/
noncomputable def gapCoeff (σ φ α : ℝ) : ℝ := σ + (φ + α) / (1 - α)

/-- Galí (2015), App. 4.1, p. 119 (and ch. 3, p. 62): `ψ_ya = (1 + φ)/(σ(1 − α) + φ + α)`,
so that natural output is `ŷ^n_t = ψ_ya a_t`. -/
noncomputable def psiYA (σ φ α : ℝ) : ℝ := (1 + φ) / (σ * (1 - α) + φ + α)

/-- Galí (2015), App. 4.1, p. 117 (the second-order polynomial in log deviations): with
`Ū = U(C, N)`, `K = U_c C`, `U_n N`, log deviations `y` (output = consumption), `n` (hours) and
`z` (preference shifter, `Z = e^z`),
`Ū(z + z²/2) + K(y + (1−σ)/2 y²) + U_n N(n + (1+φ)/2 n²) + K y z + U_n N n z`. -/
noncomputable def secondOrderUtility (Ubar K UnN σ φ y n z : ℝ) : ℝ :=
  Ubar * (z + z ^ 2 / 2) + K * (y + (1 - σ) / 2 * y ^ 2) + UnN * (n + (1 + φ) / 2 * n ^ 2) +
    K * y * z + UnN * n * z

/-- Galí (2015), App. 4.1, pp. 118–119: the terms independent of policy ("t.i.p."), an
explicit function of the shocks `a` (technology) and `z` (preferences) only:
`Ū(z + z²/2) + K(a + a z + (Γψ_ya² − (1 + φ)/(1 − α)) a²/2)`, `Γ = σ + (φ+α)/(1−α)`. -/
noncomputable def tip (Ubar K σ φ α a z : ℝ) : ℝ :=
  Ubar * (z + z ^ 2 / 2) +
    K * (a + a * z + (gapCoeff σ φ α * psiYA σ φ α ^ 2 - (1 + φ) / (1 - α)) / 2 * a ^ 2)

/-- Galí (2015), App. 4.1, p. 118, last display: the policy-relevant quadratic form
`−(K/2)[(σ + (φ+α)/(1−α))(y − ŷ^n)² + (ε/Θ) var_i p(i)]`, with `ŷ^n = ψ_ya a`. -/
noncomputable def welfareQuadratic (K σ φ α ε y a v : ℝ) : ℝ :=
  -K / 2 * (gapCoeff σ φ α * (y - psiYA σ φ α * a) ^ 2 + ε / bigTheta α ε * v)

/-- Galí (2015), App. 4.1, p. 119: `(σ + (φ+α)/(1−α)) ψ_ya = (1 + φ)/(1 − α)`, the identity
behind `(σ + (φ+α)/(1−α)) ŷ^n_t = ((1+φ)/(1−α)) a_t`. -/
theorem gapCoeff_mul_psiYA {σ φ : ℝ} (hα : α ≠ 1) (hden : σ * (1 - α) + φ + α ≠ 0) :
    gapCoeff σ φ α * psiYA σ φ α = (1 + φ) / (1 - α) := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  unfold gapCoeff psiYA
  field_simp
  ring

/-- Galí (2015), App. 4.1, p. 118: efficiency of the steady state, `−U_n/U_c = MPN` with
`MPN = (1 − α) Y/N` and `Y = C`, is equivalent to `U_n N = −(1 − α) U_c C`. -/
theorem efficiency_iff {Uc Un C N : ℝ} (hUc : Uc ≠ 0) (hN : N ≠ 0) :
    -Un / Uc = (1 - α) * C / N ↔ Un * N = -(1 - α) * (Uc * C) := by
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    field_simp
    linarith

/-- Galí (2015), App. 4.1, pp. 117–119 (**completing the square, exact**). Suppose the steady
state is efficient, `U_n N = −(1 − α) U_c C`, and hours satisfy the exact employment identity
`(1 − α) n = y − a + d` (Ch. 3, eq. (14) before approximation). Then for every `v` (to be the
cross-sectional price variance) the second-order polynomial equals
`−(K/2)[Γ(y − ψ_ya a)² + (ε/Θ) v] + t.i.p. + K((ε/2Θ) v − d)`
`− K((1+φ)/(2(1−α))(2(y−a)d + d²) + d z)`.
The last two terms are of third order once `d − (ε/2Θ) v = O(s³)` (Lemma 1) and `d = O(s²)`. -/
theorem secondOrderUtility_eq {Ubar K UnN σ φ y n z a d v : ℝ} (hα : α ≠ 1)
    (hden : σ * (1 - α) + φ + α ≠ 0) (hUn : UnN = -(1 - α) * K)
    (hn : (1 - α) * n = y - a + d) :
    secondOrderUtility Ubar K UnN σ φ y n z
      = welfareQuadratic K σ φ α ε y a v + tip Ubar K σ φ α a z +
        K * (ε / (2 * bigTheta α ε) * v - d) -
        K * ((1 + φ) / (2 * (1 - α)) * (2 * (y - a) * d + d ^ 2) + d * z) := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have hn' : n = (y - a + d) / (1 - α) := by
    field_simp
    linarith
  have hgp := gapCoeff_mul_psiYA (σ := σ) (φ := φ) hα hden
  have hgp2 : gapCoeff σ φ α * psiYA σ φ α ^ 2 = (1 + φ) / (1 - α) * psiYA σ φ α := by
    rw [← hgp]
    ring
  have hg : gapCoeff σ φ α = σ + (φ + α) / (1 - α) := rfl
  subst hUn hn'
  unfold secondOrderUtility welfareQuadratic tip
  rw [hgp2]
  have hexp : gapCoeff σ φ α * (y - psiYA σ φ α * a) ^ 2
      = gapCoeff σ φ α * y ^ 2 - 2 * (gapCoeff σ φ α * psiYA σ φ α) * a * y +
        (1 + φ) / (1 - α) * psiYA σ φ α * a ^ 2 := by
    rw [← hgp2]
    ring
  rw [hexp, hgp, hg]
  field_simp
  ring

/-! ### Layer (B): the analytic bridge -/

/-- Galí (2015), App. 4.1, pp. 117–119 (**second-order approximation of period utility,
rigorous form**). Period utility is `U(C, N; Z) = (u(C) + w(N)) Z` (separable, `U_cn = 0`,
`Z = e^z`), with `u`, `w` of class `C³` near the steady state `(C, N)`; `σ = −U_cc C/U_c`,
`φ = U_nn N/U_n`; the steady state is efficient, `U_n N = −(1 − α) U_c C`. Consider a
one-parameter family of allocations of size `s`: log deviations `y(s)` of output, `n(s)` of
hours, shocks `a(s)`, `z(s)`, all `O(s)`, with the exact employment identity
`(1 − α) n = y − a + d`, a price-dispersion term `d(s)` and cross-sectional price variance
`v(s) = O(s²)` related by Lemma 1, `d − (ε/2Θ) v = O(s³)`. Then
`U_t − U = −(U_c C/2)[(σ + (φ+α)/(1−α))(y − ψ_ya a)² + (ε/Θ) v] + t.i.p.(a, z) + O(s³)`. -/
theorem period_utility_second_order {u w : ℝ → ℝ} {C N σ φ : ℝ} {y n a z d v : ℝ → ℝ}
    (hu : ContDiffAt ℝ 3 u C) (hw : ContDiffAt ℝ 3 w N)
    (hσ : iteratedDeriv 2 u C * C = -σ * deriv u C)
    (hφ : iteratedDeriv 2 w N * N = φ * deriv w N)
    (hEff : deriv w N * N = -(1 - α) * (deriv u C * C)) (hα : α ≠ 1)
    (hden : σ * (1 - α) + φ + α ≠ 0)
    (hy : y =O[𝓝 0] fun s => s ^ 1) (ha : a =O[𝓝 0] fun s => s ^ 1)
    (hz : z =O[𝓝 0] fun s => s ^ 1) (hv : v =O[𝓝 0] fun s => s ^ 2)
    (hd : (fun s => d s - ε / (2 * bigTheta α ε) * v s) =O[𝓝 0] fun s => s ^ 3)
    (hn : ∀ s, (1 - α) * n s = y s - a s + d s) :
    (fun s => (u (C * Real.exp (y s)) + w (N * Real.exp (n s))) * Real.exp (z s) - (u C + w N)
        - (welfareQuadratic (deriv u C * C) σ φ α ε (y s) (a s) (v s) +
          tip (u C + w N) (deriv u C * C) σ φ α (a s) (z s)))
      =O[𝓝 0] fun s => s ^ 3 := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  set K := deriv u C * C with hK
  set UnN := deriv w N * N with hUnN
  set Ubar := u C + w N with hUbar
  set c := ε / (2 * bigTheta α ε) with hc
  -- orders of the building blocks
  have hd2 : d =O[𝓝 0] fun s => s ^ 2 :=
    ((bigO_weaken (by norm_num : 2 ≤ 3) hd).add (hv.const_mul_left c)).congr_left
      fun s => by ring
  have hd1 : d =O[𝓝 0] fun s => s ^ 1 := bigO_weaken (by norm_num) hd2
  have hn1 : n =O[𝓝 0] fun s => s ^ 1 :=
    (((hy.sub ha).add hd1).const_mul_left (1 - α)⁻¹).congr_left fun s => by
      rw [← hn s]
      field_simp
  have cube : ∀ {f : ℝ → ℝ}, f =O[𝓝 0] (fun s => s ^ 1) →
      (fun s => f s ^ 3) =O[𝓝 0] fun s => s ^ 3 := fun {f} hf => by
    have := hf.pow 3
    simpa [← pow_mul] using this
  have hRu : (fun s => u (C * Real.exp (y s)) - u C - K * (y s + (1 - σ) / 2 * y s ^ 2))
      =O[𝓝 0] fun s => s ^ 3 := by
    have h := ((logdev_taylor hu).comp_tendsto (tendsto_zero_of_bigO hy)).trans (cube hy)
    refine h.congr_left fun s => ?_
    simp only [Function.comp_apply]
    linear_combination (-(C / 2 * y s ^ 2)) * hσ
  have hRw : (fun s => w (N * Real.exp (n s)) - w N - UnN * (n s + (1 + φ) / 2 * n s ^ 2))
      =O[𝓝 0] fun s => s ^ 3 := by
    have h := ((logdev_taylor hw).comp_tendsto (tendsto_zero_of_bigO hn1)).trans (cube hn1)
    refine h.congr_left fun s => ?_
    simp only [Function.comp_apply]
    linear_combination (-(N / 2 * n s ^ 2)) * hφ
  have hRe : (fun s => Real.exp (z s) - 1 - z s - z s ^ 2 / 2) =O[𝓝 0] fun s => s ^ 3 :=
    (exp_taylor_two.comp_tendsto (tendsto_zero_of_bigO hz)).trans (cube hz)
  have hez : (fun s => Real.exp (z s)) =O[𝓝 0] fun s => s ^ 0 := by
    have ht : Tendsto (fun s => Real.exp (z s)) (𝓝 0) (𝓝 1) := by
      have := (Real.continuous_exp.tendsto 0).comp (tendsto_zero_of_bigO hz)
      rw [Real.exp_zero] at this
      exact this
    simpa using ht.isBigO_one ℝ
  have hsq : ∀ {f : ℝ → ℝ}, f =O[𝓝 0] (fun s => s ^ 1) →
      (fun s => f s ^ 2) =O[𝓝 0] fun s => s ^ 2 := fun {f} hf => by
    have := hf.pow 2
    simpa [← pow_mul] using this
  have hpoly : ∀ {f : ℝ → ℝ} (k₁ k₂ : ℝ), f =O[𝓝 0] (fun s => s ^ 1) →
      (fun s => k₁ * f s + k₂ * f s ^ 2) =O[𝓝 0] fun s => s ^ 1 := fun {f} k₁ k₂ hf =>
    (hf.const_mul_left k₁).add (bigO_weaken (by norm_num) ((hsq hf).const_mul_left k₂))
  -- the exact decomposition
  have hA : ∀ s, secondOrderUtility Ubar K UnN σ φ (y s) (n s) (z s)
      = welfareQuadratic K σ φ α ε (y s) (a s) (v s) + tip Ubar K σ φ α (a s) (z s) +
        K * (c * v s - d s) -
        K * ((1 + φ) / (2 * (1 - α)) * (2 * (y s - a s) * d s + d s ^ 2) + d s * z s) :=
    fun s => secondOrderUtility_eq hα hden hEff (hn s)
  have T1 := hRe.const_mul_left Ubar
  have T2 : (fun s => (K * (1 - σ) / 2 * y s ^ 2 + UnN * (1 + φ) / 2 * n s ^ 2) *
      (z s + z s ^ 2 / 2)) =O[𝓝 0] fun s => s ^ (2 + 1) :=
    bigO_mul (((hsq hy).const_mul_left _).add ((hsq hn1).const_mul_left _))
      ((hpoly 1 (1 / 2) hz).congr_left fun s => by ring)
  have T3 : (fun s => (K * y s + UnN * n s) * (z s ^ 2 / 2)) =O[𝓝 0] fun s => s ^ (1 + 2) :=
    bigO_mul ((hy.const_mul_left _).add (hn1.const_mul_left _))
      (((hsq hz).const_mul_left (1 / 2)).congr_left fun s => by ring)
  have T4 : (fun s => (K * (y s + (1 - σ) / 2 * y s ^ 2) + UnN * (n s + (1 + φ) / 2 * n s ^ 2)) *
      (Real.exp (z s) - 1 - z s - z s ^ 2 / 2)) =O[𝓝 0] fun s => s ^ 3 :=
    bigO_weaken (by norm_num : 3 ≤ 1 + 3) (bigO_mul
      ((((hpoly 1 ((1 - σ) / 2) hy).const_mul_left K).add
        ((hpoly 1 ((1 + φ) / 2) hn1).const_mul_left UnN)).congr_left fun s => by ring) hRe)
  have T5 : (fun s => ((u (C * Real.exp (y s)) - u C - K * (y s + (1 - σ) / 2 * y s ^ 2)) +
      (w (N * Real.exp (n s)) - w N - UnN * (n s + (1 + φ) / 2 * n s ^ 2))) *
      Real.exp (z s)) =O[𝓝 0] fun s => s ^ (3 + 0) := bigO_mul (hRu.add hRw) hez
  have T6 : (fun s => K * (c * v s - d s)) =O[𝓝 0] fun s => s ^ 3 :=
    (hd.neg_left.const_mul_left K).congr_left fun s => by ring
  have T7 : (fun s => K * ((1 + φ) / (2 * (1 - α)) * (2 * (y s - a s) * d s + d s ^ 2) +
      d s * z s)) =O[𝓝 0] fun s => s ^ 3 := by
    have e1 : (fun s => 2 * (y s - a s) * d s) =O[𝓝 0] fun s => s ^ (1 + 2) :=
      (bigO_mul ((hy.sub ha).const_mul_left 2) hd2).congr_left fun s => by ring
    have e2 : (fun s => d s ^ 2) =O[𝓝 0] fun s => s ^ 3 :=
      bigO_weaken (by norm_num : 3 ≤ 2 + 2) ((bigO_mul hd2 hd2).congr_left fun s => by ring)
    have e3 : (fun s => d s * z s) =O[𝓝 0] fun s => s ^ (2 + 1) := bigO_mul hd2 hz
    exact ((((e1.add e2).const_mul_left ((1 + φ) / (2 * (1 - α)))).add e3).const_mul_left K)
  refine (((((((T1.add T2).add T3).add T4).add T5).add T6).sub T7)).congr_left fun s => ?_
  have hs := hA s
  unfold secondOrderUtility at hs
  linear_combination (-1 : ℝ) * hs

/-- Galí (2015), App. 4.1, p. 118 (**the bridge with Lemma 1 discharged**): the same
second-order statement when `d(s)` and `v(s)` are the dispersion term and the
cross-sectional variance of an actual family of price distributions `p(i) = p̄ + s ζ(i)` over
any probability space of goods (`ζ` bounded and measurable, `P` the CES index). -/
theorem period_utility_second_order_dispersion [IsProbabilityMeasure μ] {u w : ℝ → ℝ}
    {C N σ φ pbar B : ℝ} {ζ : G → ℝ} {y n a z : ℝ → ℝ} (hζ : Measurable ζ)
    (hB : ∀ i, |ζ i| ≤ B) (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) (hσ0 : 0 < σ) (hφ0 : 0 ≤ φ)
    (hu : ContDiffAt ℝ 3 u C) (hw : ContDiffAt ℝ 3 w N)
    (hσ : iteratedDeriv 2 u C * C = -σ * deriv u C)
    (hφ : iteratedDeriv 2 w N * N = φ * deriv w N)
    (hEff : deriv w N * N = -(1 - α) * (deriv u C * C))
    (hy : y =O[𝓝 0] fun s => s ^ 1) (ha : a =O[𝓝 0] fun s => s ^ 1)
    (hz : z =O[𝓝 0] fun s => s ^ 1)
    (hn : ∀ s, (1 - α) * n s = y s - a s +
      dispersion μ α ε (fun i => Real.exp (pbar + s * ζ i))) :
    (fun s => (u (C * Real.exp (y s)) + w (N * Real.exp (n s))) * Real.exp (z s) - (u C + w N)
        - (welfareQuadratic (deriv u C * C) σ φ α ε (y s) (a s)
            (crossVar μ (fun i => pbar + s * ζ i)) +
          tip (u C + w N) (deriv u C * C) σ φ α (a s) (z s)))
      =O[𝓝 0] fun s => s ^ 3 := by
  have hden : σ * (1 - α) + φ + α ≠ 0 := by
    have : 0 < σ * (1 - α) := mul_pos hσ0 (by linarith)
    linarith
  have hv : (fun s => crossVar μ (fun i => pbar + s * ζ i)) =O[𝓝 0] fun s => s ^ 2 := by
    have : (fun s => crossVar μ (fun i => pbar + s * ζ i))
        = fun s => (∫ i, (ζ i - ∫ j, ζ j ∂μ) ^ 2 ∂μ) * s ^ 2 := by
      funext s
      rw [crossVar_family hζ hB]
      ring
    rw [this]
    exact (isBigO_refl _ _).const_mul_left _
  exact period_utility_second_order hu hw hσ hφ hEff hα1.ne hden hy ha hz hv
    (dispersion_second_order hζ hB hε hα0 hα1 pbar) hn

/-- Galí (2015), App. 4.1, p. 118, normalised as in the book: with `U_c C ≠ 0`,
`(U_t − U)/(U_c C) = −½[(σ + (φ+α)/(1−α))(y − ψ_ya a)² + (ε/Θ) v] + t.i.p. + O(s³)`. -/
theorem period_utility_normalised {u w : ℝ → ℝ} {C N σ φ : ℝ} {y n a z d v : ℝ → ℝ}
    (hK : deriv u C * C ≠ 0) (hu : ContDiffAt ℝ 3 u C) (hw : ContDiffAt ℝ 3 w N)
    (hσ : iteratedDeriv 2 u C * C = -σ * deriv u C)
    (hφ : iteratedDeriv 2 w N * N = φ * deriv w N)
    (hEff : deriv w N * N = -(1 - α) * (deriv u C * C)) (hα : α ≠ 1)
    (hden : σ * (1 - α) + φ + α ≠ 0)
    (hy : y =O[𝓝 0] fun s => s ^ 1) (ha : a =O[𝓝 0] fun s => s ^ 1)
    (hz : z =O[𝓝 0] fun s => s ^ 1) (hv : v =O[𝓝 0] fun s => s ^ 2)
    (hd : (fun s => d s - ε / (2 * bigTheta α ε) * v s) =O[𝓝 0] fun s => s ^ 3)
    (hn : ∀ s, (1 - α) * n s = y s - a s + d s) :
    (fun s => ((u (C * Real.exp (y s)) + w (N * Real.exp (n s))) * Real.exp (z s) -
        (u C + w N)) / (deriv u C * C)
        - (-(1 / 2) * (gapCoeff σ φ α * (y s - psiYA σ φ α * a s) ^ 2 +
            ε / bigTheta α ε * v s) +
          tip (u C + w N) (deriv u C * C) σ φ α (a s) (z s) / (deriv u C * C)))
      =O[𝓝 0] fun s => s ^ 3 := by
  have h := (period_utility_second_order hu hw hσ hφ hEff hα hden hy ha hz hv hd
    hn).const_mul_left (deriv u C * C)⁻¹
  refine h.congr_left fun s => ?_
  unfold welfareQuadratic
  generalize deriv u C * C = K at hK ⊢
  field_simp

/-! ### Lemma 2: the exact Calvo cross-section -/

/-- Galí (2015), p. 119 (Lemma 2 setting): a cross-sectional distribution of log prices is
admissible when it is a probability measure with finite first and second moments. -/
def GoodDist (ν : Measure ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ Integrable (fun x => x) ν ∧ Integrable (fun x => x ^ 2) ν

/-- Galí (2015), p. 119: the cross-sectional mean of log prices `m = ∫ p ν(dp)`. -/
noncomputable def crossMean (ν : Measure ℝ) : ℝ := ∫ x, x ∂ν

/-- Galí (2015), p. 119: the cross-sectional variance of log prices `var_i p(i)`. -/
noncomputable def crossVarDist (ν : Measure ℝ) : ℝ := ∫ x, (x - crossMean ν) ^ 2 ∂ν

/-- Galí (2015), App. 3.2–3.3 and p. 119: the Calvo law of motion of the cross-section of log
prices, `ν_t = θ ν_{t−1} + (1 − θ) δ_{p*_t}` (derived from the firm-level model in the
Chapter 3 project, `dist_law_of_motion`). -/
noncomputable def calvoMix (θ : ℝ) (ν : Measure ℝ) (p : ℝ) : Measure ℝ :=
  ENNReal.ofReal θ • ν + ENNReal.ofReal (1 - θ) • Measure.dirac p

/-- Restated from the Chapter 3 project (`integral_calvo_mix`). Galí (2015), App. 3.2:
integrating against `θ ν + (1 − θ) δ_p` gives `θ ∫ f dν + (1 − θ) f(p)`. -/
theorem integral_calvoMix {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (p : ℝ)
    {f : ℝ → ℝ} (hf : Integrable f ν) :
    ∫ x, f x ∂(calvoMix θ ν p) = θ * ∫ x, f x ∂ν + (1 - θ) * f p := by
  have hd : Integrable f (Measure.dirac p) := integrable_dirac (by simp)
  rw [calvoMix, integral_add_measure (hf.smul_measure ENNReal.ofReal_ne_top)
      (hd.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul, smul_eq_mul]

/-- Galí (2015), p. 119: `var = E p² − (E p)²` for an admissible cross-section. -/
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

/-- Galí (2015), p. 119: the Calvo law of motion preserves admissibility. -/
theorem calvoMix_good {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (p : ℝ)
    (hg : GoodDist ν) : GoodDist (calvoMix θ ν p) := by
  obtain ⟨hp, hi1, hi2⟩ := hg
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · rw [calvoMix, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ,
      measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      ← ENNReal.ofReal_add h0 (by linarith)]
    simp
  · exact (hi1.smul_measure ENNReal.ofReal_ne_top).add_measure
      ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
  · exact (hi2.smul_measure ENNReal.ofReal_ne_top).add_measure
      ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)

/-- Galí (2015), p. 119 (exact): the cross-sectional mean moves as
`m_t = θ m_{t−1} + (1 − θ) p*_t`, i.e. `Δm_t = (1 − θ)(p*_t − m_{t−1})`. -/
theorem calvoMix_mean {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (p : ℝ)
    (hg : GoodDist ν) : crossMean (calvoMix θ ν p) = θ * crossMean ν + (1 - θ) * p := by
  unfold crossMean
  exact integral_calvoMix h0 h1 p hg.2.1

/-- Galí (2015), p. 119 (**exact variance recursion**):
`var_t = θ var_{t−1} + θ(1 − θ)(p*_t − m_{t−1})²`. -/
theorem calvoMix_var {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (p : ℝ)
    (hg : GoodDist ν) :
    crossVarDist (calvoMix θ ν p)
      = θ * crossVarDist ν + θ * (1 - θ) * (p - crossMean ν) ^ 2 := by
  rw [crossVarDist_eq (calvoMix_good h0 h1 p hg), crossVarDist_eq hg, calvoMix_mean h0 h1 p hg]
  have h2 : ∫ x, x ^ 2 ∂(calvoMix θ ν p) = θ * ∫ x, x ^ 2 ∂ν + (1 - θ) * p ^ 2 :=
    integral_calvoMix h0 h1 p hg.2.2
  rw [h2]
  ring

/-- Galí (2015), p. 119 (**exact, in terms of the change in the mean**): for `θ < 1`,
`var_t = θ var_{t−1} + (θ/(1 − θ)) (Δm_t)²` with `Δm_t = m_t − m_{t−1}`. -/
theorem calvoMix_var_meanChange {ν : Measure ℝ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (p : ℝ)
    (hg : GoodDist ν) :
    crossVarDist (calvoMix θ ν p)
      = θ * crossVarDist ν + θ / (1 - θ) * (crossMean (calvoMix θ ν p) - crossMean ν) ^ 2 := by
  rw [calvoMix_var h0 h1.le p hg, calvoMix_mean h0 h1.le p hg]
  have : (1 : ℝ) - θ ≠ 0 := by linarith
  field_simp
  ring

/-- Galí (2015), p. 119: along a Calvo sequence `ν_{t+1} = θ ν_t + (1 − θ) δ_{p*_t}` started
from an admissible `ν_0`, every cross-section is admissible. -/
theorem calvo_good {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {ν : ℕ → Measure ℝ} {pstar : ℕ → ℝ}
    (hν : ∀ t, ν (t + 1) = calvoMix θ (ν t) (pstar t)) (hg : GoodDist (ν 0)) :
    ∀ t, GoodDist (ν t) := by
  intro t
  induction t with
  | zero => exact hg
  | succ t ih =>
    rw [hν t]
    exact calvoMix_good h0 h1 _ ih

/-- Galí (2015), p. 119 (**exact recursion along the Calvo sequence**; index `t + 1` is the
book's `t`, so `ν_0` is the inherited cross-section `ν_{−1}`):
`var_{t+1} = θ var_t + (θ/(1−θ))(m_{t+1} − m_t)²`. -/
theorem calvo_var_recursion {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) {ν : ℕ → Measure ℝ}
    {pstar : ℕ → ℝ} (hν : ∀ t, ν (t + 1) = calvoMix θ (ν t) (pstar t)) (hg : GoodDist (ν 0))
    (t : ℕ) :
    crossVarDist (ν (t + 1))
      = θ * crossVarDist (ν t) + θ / (1 - θ) * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2 := by
  rw [hν t]
  exact calvoMix_var_meanChange h0 h1 _ (calvo_good h0 h1.le hν hg t)

/-- Galí (2015), p. 119 (Lemma 2, partial sums): if `V_{t+1} = θ V_t + c q_t`, then
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

/-- Galí (2015), p. 119: a variance recursion `V_{t+1} = θ V_t + c q_t` with nonnegative data
stays nonnegative. -/
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

/-- Galí (2015), p. 119 (**Lemma 2, general form, exact**): if `V_{t+1} = θ V_t + c q_t`
with `θ, β, c ≥ 0`, `βθ < 1`, `V_0 ≥ 0`, `q ≥ 0` and `∑ βᵗ q_t` summable, then
`∑ βᵗ V_{t+1}` converges and equals `(θ V_0 + c ∑ βᵗ q_t)/(1 − βθ)`. The term `θ V_0` is the
inherited dispersion of Yun (2005), cited p. 116. -/
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

/-- Galí (2015), p. 119 (**Lemma 2 as printed, exact**): with no inherited dispersion
(`V_0 = 0`, p. 102) and `V_{t+1} = θ V_t + (θ/(1−θ)) q_t`,
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

/-- Galí (2015), p. 119 (**Lemma 2 for the Calvo cross-section, exact in `Δm`**): along
`ν_{t+1} = θ ν_t + (1 − θ) δ_{p*_t}` from an admissible `ν_0` with inherited dispersion
`var ν_0`, `∑ βᵗ var_i p_{t+1}(i) = (θ var ν_0 + (θ/(1−θ)) ∑ βᵗ (Δm_t)²)/(1 − βθ)`. -/
theorem lemma2_calvo_inherited {θ β : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {ν : ℕ → Measure ℝ} {pstar : ℕ → ℝ}
    (hν : ∀ t, ν (t + 1) = calvoMix θ (ν t) (pstar t)) (hg : GoodDist (ν 0))
    (hQ : Summable fun t => β ^ t * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) :
    HasSum (fun t => β ^ t * crossVarDist (ν (t + 1)))
      ((θ * crossVarDist (ν 0) + θ / (1 - θ) *
        ∑' t, β ^ t * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) / (1 - β * θ)) := by
  have hβθ : β * θ < 1 := by nlinarith
  have hV0 : 0 ≤ crossVarDist (ν 0) := integral_nonneg fun x => sq_nonneg _
  have hc : (0 : ℝ) ≤ θ / (1 - θ) := div_nonneg hθ0 (by linarith)
  exact lemma2_hasSum (c := θ / (1 - θ)) (V := fun t => crossVarDist (ν t)) hθ0 hβ0 hβθ hc hV0
    (fun t => sq_nonneg _) (calvo_var_recursion hθ0 hθ1 hν hg) hQ

/-- Galí (2015), p. 119 (**Lemma 2 for the Calvo cross-section, as printed**): with no
inherited dispersion, `∑ βᵗ var_i p_t(i) = θ/((1−βθ)(1−θ)) ∑ βᵗ (Δm_t)²` exactly. -/
theorem lemma2_calvo {θ β : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {ν : ℕ → Measure ℝ} {pstar : ℕ → ℝ} (hν : ∀ t, ν (t + 1) = calvoMix θ (ν t) (pstar t))
    (hg : GoodDist (ν 0)) (hV0 : crossVarDist (ν 0) = 0)
    (hQ : Summable fun t => β ^ t * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) :
    HasSum (fun t => β ^ t * crossVarDist (ν (t + 1)))
      (θ / ((1 - β * θ) * (1 - θ)) *
        ∑' t, β ^ t * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) :=
  lemma2 (V := fun t => crossVarDist (ν t))
    (q := fun t => (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) hθ0 hθ1 hβ0 hβ1 hV0
    (fun _ => sq_nonneg _) (calvo_var_recursion hθ0 hθ1 hν hg) hQ

/-- Galí (2015), p. 119 (**`Δm_t = π_t` to first order**): for log-price families
`p_k(i) = p̄ + s z_k(i)` at two consecutive dates, inflation `π = log P_1 − log P_0` (CES
indices) and the change in the cross-sectional mean `Δm = E p_1 − E p_0` differ by `O(s²)`. -/
theorem inflation_sub_meanChange [IsProbabilityMeasure μ] {z₀ z₁ : G → ℝ} (hz₀ : Measurable z₀)
    (hz₁ : Measurable z₁) {B₀ B₁ : ℝ} (hB₀ : ∀ i, |z₀ i| ≤ B₀) (hB₁ : ∀ i, |z₁ i| ≤ B₁)
    (hε : ε ≠ 1) (pbar : ℝ) :
    (fun s => (Real.log (priceIndex μ ε (fun i => Real.exp (pbar + s * z₁ i))) -
        Real.log (priceIndex μ ε (fun i => Real.exp (pbar + s * z₀ i)))) -
        ((pbar + s * ∫ i, z₁ i ∂μ) - (pbar + s * ∫ i, z₀ i ∂μ))) =O[𝓝 0] fun s => s ^ 2 := by
  have hvar : ∀ {z : G → ℝ} {B : ℝ}, Measurable z → (∀ i, |z i| ≤ B) →
      (fun s => (1 - ε) / 2 * crossVar μ (fun i => pbar + s * z i)) =O[𝓝 0]
        fun s => s ^ 2 := fun {z} {B} hz hB => by
    have : (fun s => (1 - ε) / 2 * crossVar μ (fun i => pbar + s * z i))
        = fun s => ((1 - ε) / 2 * ∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) * s ^ 2 := by
      funext s
      rw [crossVar_family hz hB]
      ring
    rw [this]
    exact (isBigO_refl _ _).const_mul_left _
  have e₁ := (bigO_weaken (by norm_num : 2 ≤ 3)
    (logPriceIndex_second_order (μ := μ) hz₁ hB₁ hε pbar)).add
    (hvar hz₁ hB₁)
  have e₀ := (bigO_weaken (by norm_num : 2 ≤ 3)
    (logPriceIndex_second_order (μ := μ) hz₀ hB₀ hε pbar)).add
    (hvar hz₀ hB₀)
  refine (e₁.sub e₀).congr_left fun s => ?_
  ring

/-- Galí (2015), p. 119 (**`π_t² = (Δm_t)² + O(s³)`**): in the setting of
`inflation_sub_meanChange`, the squares of inflation and of the change in the cross-sectional
mean agree to second order, so Lemma 2 (exact in `Δm`) holds with `π` to second order. -/
theorem inflation_sq_sub_meanChange_sq [IsProbabilityMeasure μ] {z₀ z₁ : G → ℝ}
    (hz₀ : Measurable z₀) (hz₁ : Measurable z₁) {B₀ B₁ : ℝ} (hB₀ : ∀ i, |z₀ i| ≤ B₀)
    (hB₁ : ∀ i, |z₁ i| ≤ B₁) (hε : ε ≠ 1) (pbar : ℝ) :
    (fun s => (Real.log (priceIndex μ ε (fun i => Real.exp (pbar + s * z₁ i))) -
        Real.log (priceIndex μ ε (fun i => Real.exp (pbar + s * z₀ i)))) ^ 2 -
        ((pbar + s * ∫ i, z₁ i ∂μ) - (pbar + s * ∫ i, z₀ i ∂μ)) ^ 2) =O[𝓝 0]
      fun s => s ^ 3 := by
  have hD := inflation_sub_meanChange (μ := μ) hz₀ hz₁ hB₀ hB₁ hε pbar
  have hm : (fun s => (pbar + s * ∫ i, z₁ i ∂μ) - (pbar + s * ∫ i, z₀ i ∂μ)) =O[𝓝 0]
      fun s => s ^ 1 := by
    have : (fun s => (pbar + s * ∫ i, z₁ i ∂μ) - (pbar + s * ∫ i, z₀ i ∂μ))
        = fun s => ((∫ i, z₁ i ∂μ) - ∫ i, z₀ i ∂μ) * s ^ 1 := by
      funext s
      ring
    rw [this]
    exact (isBigO_refl _ _).const_mul_left _
  have hsum := (bigO_weaken (by norm_num : 1 ≤ 2) hD).add (hm.const_mul_left 2)
  refine (bigO_mul hD hsum).congr_left fun s => ?_
  ring

/-! ### The welfare loss `W` and the average loss `L` (p. 111) -/

/-- Galí (2015), ch. 3, p. 61 (used on pp. 111 and 119):
`λ = (1 − θ)(1 − βθ)Θ/θ`. -/
noncomputable def lambdaNK (β θ α ε : ℝ) : ℝ := (1 - θ) * (1 - β * θ) / θ * bigTheta α ε

/-- Galí (2015), ch. 3, p. 63: `κ = λ(σ + (φ + α)/(1 − α))`. -/
noncomputable def kappaNK (β θ σ φ α ε : ℝ) : ℝ := lambdaNK β θ α ε * gapCoeff σ φ α

/-- Galí (2015), p. 111: the period loss `½[(σ + (φ+α)/(1−α)) ỹ² + (ε/λ) π²]`. -/
noncomputable def periodLoss (β θ σ φ α ε ygap infl : ℝ) : ℝ :=
  (gapCoeff σ φ α * ygap ^ 2 + ε / lambdaNK β θ α ε * infl ^ 2) / 2

/-- Galí (2015), p. 111 (**the welfare loss `W`**, for a given path):
`W = ½ ∑ βᵗ [(σ + (φ+α)/(1−α)) ỹ_t² + (ε/λ) π_t²]`. -/
noncomputable def welfareLoss (β θ σ φ α ε : ℝ) (ygap infl : ℕ → ℝ) : ℝ :=
  ∑' t, β ^ t * periodLoss β θ σ φ α ε (ygap t) (infl t)

/-- Galí (2015), p. 111 (**the average loss per period `L`**), as a function of the
variances: `L = ½[(σ + (φ+α)/(1−α)) var(ỹ) + (ε/λ) var(π)]`. -/
noncomputable def avgLoss (β θ σ φ α ε varY varPi : ℝ) : ℝ :=
  (gapCoeff σ φ α * varY + ε / lambdaNK β θ α ε * varPi) / 2

/-- Galí (2015), p. 119: `(ε/Θ) · θ/((1 − βθ)(1 − θ)) = ε/λ`. -/
theorem inflWeight_of_dispersion {β θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1)
    (hα : α < 1) :
    ε / bigTheta α ε * (θ / ((1 - β * θ) * (1 - θ))) = ε / lambdaNK β θ α ε := by
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have h2 : 1 - β * θ ≠ 0 := by linarith
  have h3 : (1 : ℝ) - α ≠ 0 := by linarith
  unfold lambdaNK bigTheta
  field_simp

/-- Galí (2015), p. 119, last display (**`W` in terms of the output gap and the price-level
drift, exact**): if the cross-sectional variance follows the exact Calvo recursion
`V_{t+1} = θ V_t + (θ/(1−θ)) (Δm_t)²` with no inherited dispersion, then
`½ ∑ βᵗ [(σ + (φ+α)/(1−α)) ỹ_t² + (ε/Θ) var_t] = W(ỹ, Δm)`, where `W` has inflation weight
`ε/λ`. -/
theorem welfare_eq_loss {β θ σ φ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hα : α < 1) {ygap Dm V : ℕ → ℝ} (hV0 : V 0 = 0)
    (hrec : ∀ t, V (t + 1) = θ * V t + θ / (1 - θ) * Dm t ^ 2)
    (hY : Summable fun t => β ^ t * ygap t ^ 2) (hD : Summable fun t => β ^ t * Dm t ^ 2) :
    HasSum (fun t => β ^ t * ((gapCoeff σ φ α * ygap t ^ 2 + ε / bigTheta α ε * V (t + 1)) / 2))
      (welfareLoss β θ σ φ α ε ygap Dm) := by
  have hβθ : β * θ < 1 := by nlinarith
  have hL := lemma2 (q := fun t => Dm t ^ 2) hθ0.le hθ1 hβ0 hβ1 hV0 (fun _ => sq_nonneg _)
    hrec hD
  have hA := ((hY.hasSum.mul_left (gapCoeff σ φ α)).add
    (hL.mul_left (ε / bigTheta α ε))).div_const 2
  have hB := ((hY.hasSum.mul_left (gapCoeff σ φ α)).add
    (hD.hasSum.mul_left (ε / lambdaNK β θ α ε))).div_const 2
  have hW : welfareLoss β θ σ φ α ε ygap Dm = (gapCoeff σ φ α * ∑' t, β ^ t * ygap t ^ 2 +
      ε / lambdaNK β θ α ε * ∑' t, β ^ t * Dm t ^ 2) / 2 := by
    rw [← hB.tsum_eq]
    unfold welfareLoss periodLoss
    congr 1
    funext t
    ring
  rw [hW, ← inflWeight_of_dispersion hθ0 hθ1 hβθ hα]
  convert hA using 1
  · funext t
    ring
  · ring

/-- Galí (2015), pp. 111 and 119 (**`W` for the Calvo economy, exact in `Δm`**): along the
Calvo sequence of cross-sections with no inherited dispersion,
`½ ∑ βᵗ [(σ + (φ+α)/(1−α)) ỹ_t² + (ε/Θ) var_i p_t(i)] = W(ỹ, Δm)`. -/
theorem welfare_eq_loss_calvo {β θ σ φ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hα : α < 1) {ygap : ℕ → ℝ}
    {ν : ℕ → Measure ℝ} {pstar : ℕ → ℝ} (hν : ∀ t, ν (t + 1) = calvoMix θ (ν t) (pstar t))
    (hg : GoodDist (ν 0)) (hV0 : crossVarDist (ν 0) = 0)
    (hY : Summable fun t => β ^ t * ygap t ^ 2)
    (hD : Summable fun t => β ^ t * (crossMean (ν (t + 1)) - crossMean (ν t)) ^ 2) :
    HasSum (fun t => β ^ t * ((gapCoeff σ φ α * ygap t ^ 2 +
        ε / bigTheta α ε * crossVarDist (ν (t + 1))) / 2))
      (welfareLoss β θ σ φ α ε ygap fun t => crossMean (ν (t + 1)) - crossMean (ν t)) :=
  welfare_eq_loss (V := fun t => crossVarDist (ν t)) hθ0 hθ1 hβ0 hβ1 hα hV0
    (calvo_var_recursion hθ0.le hθ1 hν hg) hY hD

/-- Galí (2015), p. 111 (**from `W` to `L`**): if the expected period-`t` squared gap and
squared inflation equal stationary variances `var(ỹ)`, `var(π)` at every date, then the
discounted expected loss is `L/(1 − β)`, i.e. `L` is the average loss per period. -/
theorem welfare_stationary {β θ σ φ varY varPi : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {eY eP : ℕ → ℝ} (heY : ∀ t, eY t = varY) (heP : ∀ t, eP t = varPi) :
    HasSum (fun t => β ^ t * ((gapCoeff σ φ α * eY t + ε / lambdaNK β θ α ε * eP t) / 2))
      (avgLoss β θ σ φ α ε varY varPi / (1 - β)) := by
  have h := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right (avgLoss β θ σ φ α ε varY varPi)
  convert h using 1
  · funext t
    rw [heY, heP, avgLoss]
  · rw [div_eq_inv_mul]

/-! ### Comparative statics of the weights (p. 111) -/

/-- Galí (2015), p. 111: the output-gap coefficient `σ + (φ+α)/(1−α)` is strictly increasing
in `σ`. -/
theorem gapCoeff_strictMono_sigma (φ α : ℝ) : StrictMono fun σ => gapCoeff σ φ α := by
  intro a b h
  simp only [gapCoeff]
  linarith

/-- Galí (2015), p. 111: the output-gap coefficient is strictly increasing in `φ` (`α < 1`). -/
theorem gapCoeff_strictMono_phi (σ : ℝ) (hα : α < 1) : StrictMono fun φ => gapCoeff σ φ α := by
  intro a b h
  simp only [gapCoeff]
  have h1 : (a + α) / (1 - α) < (b + α) / (1 - α) :=
    div_lt_div_of_pos_right (by linarith) (by linarith)
  linarith

/-- Galí (2015), p. 111: the output-gap coefficient is strictly increasing in `α` on
`α < 1` (for `φ > −1`, in particular for `φ ≥ 0`). -/
theorem gapCoeff_strictMonoOn_alpha (σ : ℝ) {φ : ℝ} (hφ : -1 < φ) :
    StrictMonoOn (fun α => gapCoeff σ φ α) (Set.Iio 1) := by
  intro a ha b hb hab
  simp only [Set.mem_Iio] at ha hb
  simp only [gapCoeff]
  have h : (φ + a) / (1 - a) < (φ + b) / (1 - b) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  linarith

/-- Galí (2015), p. 111: the inflation weight in closed form,
`ε/λ = εθ(1 − α + αε)/((1 − θ)(1 − βθ)(1 − α))`. -/
theorem inflWeight_eq {β θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1) (hα : α < 1) :
    ε / lambdaNK β θ α ε
      = ε * θ * (1 - α + α * ε) / ((1 - θ) * (1 - β * θ) * (1 - α)) := by
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have h2 : 1 - β * θ ≠ 0 := by linarith
  have h3 : (1 : ℝ) - α ≠ 0 := by linarith
  unfold lambdaNK bigTheta
  field_simp

/-- Galí (2015), p. 111: the inflation weight `ε/λ` is strictly increasing in the elasticity
of substitution `ε` (on `ε > 0`, for `0 ≤ α < 1`). -/
theorem inflWeight_strictMonoOn_eps {β θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hβ1 : β < 1) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    StrictMonoOn (fun ε => ε / lambdaNK β θ α ε) (Set.Ioi 0) := by
  have hβθ : β * θ < 1 := by nlinarith
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have hΘa : 0 < 1 - α + α * a := by nlinarith
  have hΘb : 0 < 1 - α + α * b := by nlinarith
  simp only
  rw [inflWeight_eq hθ0 hθ1 hβθ hα1, inflWeight_eq hθ0 hθ1 hβθ hα1]
  have hD : 0 < (1 - θ) * (1 - β * θ) * (1 - α) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  apply div_lt_div_of_pos_right _ hD
  have hk : 0 < (b - a) * (1 - α + α * (a + b)) := mul_pos (by linarith) (by nlinarith)
  have : a * (1 - α + α * a) < b * (1 - α + α * b) := by nlinarith
  have hθ' : 0 < θ := hθ0
  nlinarith

/-- Galí (2015), p. 111: the inflation weight `ε/λ` is strictly increasing in the degree of
price stickiness `θ ∈ (0, 1)` (for `β ≤ 1`). -/
theorem inflWeight_strictMonoOn_theta {β : ℝ} (hβ1 : β ≤ 1) (hα : α < 1)
    (hε : 0 < ε) (hΘ : 0 < 1 - α + α * ε) :
    StrictMonoOn (fun θ => ε / lambdaNK β θ α ε) (Set.Ioo 0 1) := by
  intro a ha b hb hab
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  have hβa : β * a < 1 := by nlinarith
  have hβb : β * b < 1 := by nlinarith
  simp only
  rw [inflWeight_eq ha0 ha1 hβa hα, inflWeight_eq hb0 hb1 hβb hα]
  have hDa : 0 < (1 - a) * (1 - β * a) * (1 - α) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hDb : 0 < (1 - b) * (1 - β * b) * (1 - α) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  rw [div_lt_div_iff₀ hDa hDb]
  have hk : 0 < ε * (1 - α + α * ε) * (1 - α) := mul_pos (mul_pos hε hΘ) (by linarith)
  have hkey : a * ((1 - b) * (1 - β * b)) < b * ((1 - a) * (1 - β * a)) := by
    have h1 : 0 < (b - a) * (1 - β * a * b) := mul_pos (by linarith) (by nlinarith)
    nlinarith
  nlinarith

/-- Galí (2015), p. 111 and ch. 5 (`ϑ = κ/ε`): the weight of the output gap **relative** to
inflation, `(σ + (φ+α)/(1−α)) / (ε/λ) = κ/ε`. -/
noncomputable def relWeight (β θ σ φ α ε : ℝ) : ℝ := kappaNK β θ σ φ α ε / ε

/-- Galí (2015), p. 111: `κ/ε` is the ratio of the two loss coefficients. -/
theorem relWeight_eq_ratio {β θ σ φ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1)
    (hα : α < 1) (hε : 0 < ε) (hΘ : 0 < 1 - α + α * ε) :
    relWeight β θ σ φ α ε = gapCoeff σ φ α / (ε / lambdaNK β θ α ε) := by
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have h2 : 1 - β * θ ≠ 0 := by linarith
  have h3 : (1 : ℝ) - α ≠ 0 := by linarith
  unfold relWeight kappaNK lambdaNK bigTheta
  field_simp

/-- Galí (2015), p. 111 (C4-3): in closed form,
`κ/ε = ((1 − θ)(1 − βθ)/(θε)) · (σ(1 − α) + φ + α)/(1 − α + αε)`. -/
theorem relWeight_eq {β θ σ φ : ℝ} (hα : α < 1) :
    relWeight β θ σ φ α ε
      = (1 - θ) * (1 - β * θ) / (θ * ε) * ((σ * (1 - α) + φ + α) / (1 - α + α * ε)) := by
  have h3 : (1 : ℝ) - α ≠ 0 := by linarith
  unfold relWeight kappaNK lambdaNK bigTheta gapCoeff
  by_cases hε : ε = 0
  · simp [hε]
  by_cases hθ : θ = 0
  · simp [hθ]
  by_cases hΘ : 1 - α + α * ε = 0
  · simp [hΘ]
  field_simp
  ring

/-- Galí (2015), p. 111 (C4-3, exact difference): for `α₁, α₂` with `1 − αᵢ + αᵢε ≠ 0`,
`κ/ε(α₁) − κ/ε(α₂) = c (α₂ − α₁)((σ + φ)(ε − 1) − (1 − σ))/((1−α₁+α₁ε)(1−α₂+α₂ε))`,
`c = (1 − θ)(1 − βθ)/(θε)`: the sign of the slope in `α` does not depend on `α`. -/
theorem relWeight_sub {β θ σ φ α₁ α₂ : ℝ} (h₁ : α₁ < 1) (h₂ : α₂ < 1)
    (hΘ₁ : 1 - α₁ + α₁ * ε ≠ 0) (hΘ₂ : 1 - α₂ + α₂ * ε ≠ 0) :
    relWeight β θ σ φ α₁ ε - relWeight β θ σ φ α₂ ε
      = (1 - θ) * (1 - β * θ) / (θ * ε) * ((α₂ - α₁) * ((σ + φ) * (ε - 1) - (1 - σ)) /
          ((1 - α₁ + α₁ * ε) * (1 - α₂ + α₂ * ε))) := by
  rw [relWeight_eq h₁, relWeight_eq h₂, ← mul_sub, div_sub_div _ _ hΘ₁ hΘ₂]
  congr 2
  ring

/-- Galí (2015), p. 111 (**C4-3, corrected statement**): if `(σ + φ)(ε − 1) > 1 − σ` (true at
the baseline, and whenever `σ ≥ 1`), the relative weight `κ/ε` of the output gap is strictly
**decreasing** in `α` on `[0, 1)`. -/
theorem relWeight_strictAntiOn_alpha {β θ σ φ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hβ1 : β < 1) (hε : 1 < ε) (hcond : 1 - σ < (σ + φ) * (ε - 1)) :
    StrictAntiOn (fun α => relWeight β θ σ φ α ε) (Set.Ico 0 1) := by
  intro a ha b hb hab
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  have hΘa : 0 < 1 - a + a * ε := by nlinarith
  have hΘb : 0 < 1 - b + b * ε := by nlinarith
  have hβθ : β * θ < 1 := by nlinarith
  have hc : 0 < (1 - θ) * (1 - β * θ) / (θ * ε) :=
    div_pos (mul_pos (by linarith) (by linarith)) (mul_pos hθ0 (by linarith))
  have h := relWeight_sub (β := β) (θ := θ) (σ := σ) (φ := φ) hb1 ha1 hΘb.ne' hΘa.ne'
  have hpos : 0 < (a - b) * ((σ + φ) * (ε - 1) - (1 - σ)) / ((1 - b + b * ε) * (1 - a + a * ε))
      ∨ (a - b) * ((σ + φ) * (ε - 1) - (1 - σ)) / ((1 - b + b * ε) * (1 - a + a * ε)) < 0 := by
    right
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) (by linarith))
      (mul_pos hΘb hΘa)
  simp only
  rcases hpos with hp | hn
  · exact absurd hp (by
      have : (a - b) * ((σ + φ) * (ε - 1) - (1 - σ)) < 0 :=
        mul_neg_of_neg_of_pos (by linarith) (by linarith)
      exact not_lt.2 (div_nonpos_of_nonpos_of_nonneg this.le (mul_pos hΘb hΘa).le))
  · have := mul_neg_of_pos_of_neg hc hn
    linarith

/-- Galí (2015), p. 111 (C4-3, the other case): if `(σ + φ)(ε − 1) < 1 − σ`, the relative
weight `κ/ε` is strictly increasing in `α` on `[0, 1)`. -/
theorem relWeight_strictMonoOn_alpha {β θ σ φ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hβ1 : β < 1) (hε : 1 < ε) (hcond : (σ + φ) * (ε - 1) < 1 - σ) :
    StrictMonoOn (fun α => relWeight β θ σ φ α ε) (Set.Ico 0 1) := by
  intro a ha b hb hab
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  have hΘa : 0 < 1 - a + a * ε := by nlinarith
  have hΘb : 0 < 1 - b + b * ε := by nlinarith
  have hβθ : β * θ < 1 := by nlinarith
  have hc : 0 < (1 - θ) * (1 - β * θ) / (θ * ε) :=
    div_pos (mul_pos (by linarith) (by linarith)) (mul_pos hθ0 (by linarith))
  have h := relWeight_sub (β := β) (θ := θ) (σ := σ) (φ := φ) hb1 ha1 hΘb.ne' hΘa.ne'
  have hn : 0 < (a - b) * ((σ + φ) * (ε - 1) - (1 - σ)) /
      ((1 - b + b * ε) * (1 - a + a * ε)) :=
    div_pos (mul_pos_of_neg_of_neg (by linarith) (by linarith)) (mul_pos hΘb hΘa)
  simp only
  have := mul_pos hc hn
  linarith

/-- Galí (2015), p. 111 (C4-3, the baseline numbers): at `β = 0.99`, `θ = 3/4`, `σ = 1`,
`φ = 5`, `ε = 9`, the relative weight `κ/ε` equals `103/1800 ≈ 0.0572` at `α = 0`,
`103/3240 ≈ 0.0318` at `α = 0.1`, `103/5400 ≈ 0.0191` at `α = 1/4` and
`103/7560 ≈ 0.0136` at `α = 0.4`. -/
theorem relWeight_baseline :
    relWeight 0.99 0.75 1 5 0 9 = 103 / 1800 ∧ relWeight 0.99 0.75 1 5 0.1 9 = 103 / 3240 ∧
      relWeight 0.99 0.75 1 5 0.25 9 = 103 / 5400 ∧ relWeight 0.99 0.75 1 5 0.4 9 = 103 / 7560 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [relWeight_eq (by norm_num)] <;> norm_num

/-- Galí (2015), p. 111 (**C4-3, counterexample to the printed claim**): "the relative weight of
output gap fluctuations in the loss function is increasing in … α" is false at the baseline:
the relative weight `κ/ε` is not monotone increasing in `α` (it falls from `≈ 0.0572` at
`α = 0` to `≈ 0.0191` at `α = 1/4`). The *absolute* coefficient is increasing in `α`
(`gapCoeff_strictMonoOn_alpha`). -/
theorem relWeight_not_increasing_alpha :
    ¬ MonotoneOn (fun α => relWeight 0.99 0.75 1 5 α 9) (Set.Ico 0 1) := by
  intro h
  have := h (a := 0) (b := 0.25) (by norm_num) (by norm_num) (by norm_num)
  simp only at this
  rw [relWeight_baseline.1, relWeight_baseline.2.2.1] at this
  norm_num at this

/-- Galí (2015), p. 111 (C4-3): at the baseline (`σ = 1`, `φ = 5`, `ε = 9`, `β = 0.99`,
`θ = 3/4`) the relative weight `κ/ε` is strictly decreasing in `α` on all of `[0, 1)`. -/
theorem relWeight_baseline_strictAnti :
    StrictAntiOn (fun α => relWeight 0.99 0.75 1 5 α 9) (Set.Ico 0 1) :=
  relWeight_strictAntiOn_alpha (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

end Gali.MonetaryPolicyDesign.Welfare
