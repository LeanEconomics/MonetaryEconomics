/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OpenEconomy.AggregateDemand
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# The supply side of the small open economy

Galí (2015), Chapter 8, §8.2.2 (pp. 236–239).

Notation as in `AggregateDemand`: `ϖ = varpi σ η υ`, `Φ = Phi σ η υ`, `σ_υ = sigmaU σ η υ`;
`λ` is written `lam`.

## Main results

* `employment_identity`, `eq32_exact`, `eq32`, `dispersion_family_first_order`,
  `dispersion_second_order`: aggregate output and employment satisfy exactly
  `y = a + (1 − α)n − d`, where the price-dispersion term `d` is zero with zero derivative
  (indeed `O(s²)`) around a symmetric price distribution, so (32) `y = a + (1 − α)n` holds
  to first order (restated from the Chapter 3 project).
* `eq33`: the average markup (33),
  `μ = −(σ + (φ+α)/(1−α))y + υ(ϖ − 1)s + (1 + (φ+α)/(1−α))a − υz`.
* `eq34`: the Phillips curve in `y`, `s`, `a`, `z`.
* `sigma_sub_eq_sigmaU`: the key identity `σ − υ(ϖ − 1)σ_υ = σ_υ`.
* `eq35_iff`, `GammaA_pos`: natural output (35) `yⁿ = Γ_a a + Γ_z z + Γ_* y*`, `Γ_a > 0`.
* `GammaStar_unit`, `GammaZ_unit_neg`, `GammaZ_zero`: `σ = η = 1` ⇒ `Γ_* = 0`, `Γ_z < 0`
  (for `υ > 0`); `υ = 0` ⇒ `Γ_z = 0` (fn. 8).
* `sgap_eq`, `eq36`, `eq37`: `s̃ = σ_υỹ`, `μ̂ = −(σ_υ + (φ+α)/(1−α))ỹ` and the open-economy
  Phillips curve `π_H = βE π_H' + κ_υ ỹ`.
* `kappaU_zero`, `kappaU_unit`, `kappaU_strictAntiOn`: `κ_υ = κ` if `υ = 0` or `σ = η = 1`;
  `ση > 1` ⇒ `κ_υ` strictly decreasing in `υ` on `[0, 1]`.
* `eq38`, `tendsto_PsiStar`, `tendsto_PsiZ`: the natural rate (38) and `Ψ_* → 0`,
  `Ψ_z → 1` as `υ → 0`.
-/

namespace Gali.OpenEconomy.Supply

open MeasureTheory ProbabilityTheory Filter Topology Gali.OpenEconomy.AggregateDemand
  Gali.OpenEconomy.Preferences.Variety

/-! ### Aggregate output and employment, (32) (restated from the Chapter 3 project) -/

variable {G : Type*} [MeasurableSpace G]

/-- Restated from the Chapter 3 project (used for (32), p. 237).
Galí (2015), p. 59 and App. 3.4, p. 86: the price-dispersion term
`d = (1 − α) log ∫ (P(i)/P)^{−ε/(1−α)} di`. -/
noncomputable def dispersion (μ : Measure G) (α ε : ℝ) (P : G → ℝ) : ℝ :=
  (1 - α) * Real.log (∫ i, (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) ∂μ)

/-- Restated from the Chapter 3 project (used for (32), p. 237).
Galí (2015), p. 60 and App. 3.4, p. 86: `Θ = (1 − α)/(1 − α + αε)`. -/
noncomputable def bigTheta (α ε : ℝ) : ℝ := (1 - α) / (1 - α + α * ε)

/-- Restated from the Chapter 3 project (used for (32), p. 237).
Galí (2015), App. 3.4, p. 86: the cross-sectional variance
`var_i p(i) = ∫ (p(i) − ∫ p)² di`. -/
noncomputable def crossVar (μ : Measure G) (p : G → ℝ) : ℝ :=
  ∫ i, (p i - ∫ j, p j ∂μ) ^ 2 ∂μ

variable {μ : Measure G} {α ε : ℝ} {P : G → ℝ}

/-- Restated from the Chapter 3 project (used for (32), p. 237).
Galí (2015), p. 59: with production `Y(i) = A N(i)^{1−α}` (5) and output on the demand
schedule `Y(i) = (P(i)/P)^{−ε} Y` (from (1) and goods-market clearing), aggregate employment
is `N = ∫ N(i) = (Y/A)^{1/(1−α)} ∫ (P(i)/P)^{−ε/(1−α)} di`. -/
theorem employment_level (hα1 : α < 1) (hP : ∀ i, 0 < P i)
    (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) {A Y : ℝ} (hA : 0 < A) (hY : 0 ≤ Y) {N : G → ℝ}
    (hN : ∀ i, 0 ≤ N i) (hprod : ∀ i, demand μ ε P Y i = A * N i ^ (1 - α)) :
    ∫ i, N i ∂μ
      = (Y / A) ^ (1 - α)⁻¹ * ∫ i, (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) ∂μ := by
  have hI := priceIndex_pos hpos
  have hsub : (1 : ℝ) - α ≠ 0 := by linarith
  have hpt : ∀ i, N i = (Y / A) ^ (1 - α)⁻¹ * (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) := by
    intro i
    have ha : 0 < P i / priceIndex μ ε P := div_pos (hP i) hI
    have h1 : N i ^ (1 - α) = (P i / priceIndex μ ε P) ^ (-ε) * (Y / A) := by
      have := hprod i
      rw [demand] at this
      field_simp
      linarith
    rw [← Real.rpow_rpow_inv (hN i) hsub, h1, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul ha.le, div_eq_mul_inv (-ε), mul_comm]
  simp_rw [hpt]
  rw [integral_const_mul]

/-- Restated from the Chapter 3 project (used for (32), p. 237).
Galí (2015), p. 59, eq. (14) before approximation (**exact**):
`(1 − α) log N = log Y − log A + d`. -/
theorem employment_identity (hα1 : α < 1) (hP : ∀ i, 0 < P i)
    (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) {A Y : ℝ} (hA : 0 < A) (hY : 0 < Y) {N : G → ℝ}
    (hN : ∀ i, 0 ≤ N i) (hprod : ∀ i, demand μ ε P Y i = A * N i ^ (1 - α))
    (hD : 0 < ∫ i, (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) ∂μ) :
    (1 - α) * Real.log (∫ i, N i ∂μ) = Real.log Y - Real.log A + dispersion μ α ε P := by
  have hsub : (1 : ℝ) - α ≠ 0 := by linarith
  rw [employment_level hα1 hP hpos hA hY.le hN hprod, Real.log_mul (by positivity) hD.ne',
    Real.log_rpow (by positivity), Real.log_div hY.ne' hA.ne', dispersion]
  field_simp

/-- Restated from the Chapter 3 project (used for (32), p. 237).
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

/-- Restated from the Chapter 3 project (used for (32), p. 237).
Galí (2015), App. 3.4, p. 85: for bounded `z`, the cumulant-generating function is
analytic on all of `ℝ` (the domain of finiteness of the mgf is `ℝ`). -/
theorem interior_integrableExpSet [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ i, |z i| ≤ B) : interior (integrableExpSet z μ) = Set.univ := by
  have : integrableExpSet z μ = Set.univ :=
    Set.eq_univ_of_forall fun t => integrable_exp_mul hz hB t
  rw [this, interior_univ]

/-- Restated from the Chapter 3 project (used for (32), p. 237).
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

/-- Restated from the Chapter 3 project (used for (32), p. 237).
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

/-- Restated from the Chapter 3 project (used for (32), p. 237).
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

/-- Restated from the Chapter 3 project (used for (32), p. 237).
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

/-- Restated from the Chapter 3 project (used for (32), p. 237).
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

/-- Restated from the Chapter 3 project (used for (32), p. 237).
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

/-- Restated from the Chapter 3 project (used for (32), p. 237).
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

/-- Restated from the Chapter 3 project (used for (32), p. 237).
Galí (2015), p. 59 (**`d_t` vanishes to first order**): along the family
`p(i) = p̄ + s z(i)`, `d(0) = 0` and `d'(0) = 0`. -/
theorem dispersion_family_first_order [IsProbabilityMeasure μ] {z : G → ℝ}
    (hz : Measurable z) {B : ℝ} (hB : ∀ i, |z i| ≤ B) (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (pbar : ℝ) :
    dispersion μ α ε (fun i => Real.exp (pbar + 0 * z i)) = 0 ∧
      HasDerivAt (fun s => dispersion μ α ε (fun i => Real.exp (pbar + s * z i))) 0 0 := by
  have hd0 : dispersion μ α ε (fun i => Real.exp (pbar + 0 * z i)) = 0 := by
    rw [dispersion_family_eq hz hB (by linarith) (by linarith)]
    simp [cgf_zero]
  refine ⟨hd0, ?_⟩
  rw [hasDerivAt_iff_isLittleO, hd0]
  have h2 := dispersion_family_isBigO_sq (μ := μ) hz hB hε hα0 hα1 pbar
  have h21 : (fun s : ℝ => s ^ 2) =o[nhds 0] fun s => s ^ 1 :=
    Asymptotics.isLittleO_pow_pow (by norm_num : 1 < 2)
  simpa using h2.trans_isLittleO h21

/-- Galí (2015), (32), p. 237 (**exact**): with production `Y(i) = A N(i)^{1−α}` and output
on the demand schedule, `y = a + (1 − α)n − d` with `n = log ∫ N(i) di` and `d` the
price-dispersion term. -/
theorem eq32_exact (hα1 : α < 1) (hP : ∀ i, 0 < P i)
    (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) {A Y : ℝ} (hA : 0 < A) (hY : 0 < Y) {N : G → ℝ}
    (hN : ∀ i, 0 ≤ N i) (hprod : ∀ i, demand μ ε P Y i = A * N i ^ (1 - α))
    (hD : 0 < ∫ i, (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) ∂μ) :
    Real.log Y = Real.log A + (1 - α) * Real.log (∫ i, N i ∂μ) - dispersion μ α ε P := by
  rw [employment_identity hα1 hP hpos hA hY hN hprod hD]
  ring

/-- Galí (2015), **(32)**, p. 237: when the dispersion term vanishes (it is zero, with zero
derivative, at a symmetric price distribution: `dispersion_family_first_order`),
`y = a + (1 − α)n`. -/
theorem eq32 {α y a n d : ℝ} (h : y = a + (1 - α) * n - d) (hd : d = 0) :
    y = a + (1 - α) * n := by
  rw [h, hd, sub_zero]

/-! ### Markups and inflation, (33)–(34) -/

/-- Galí (2015), **(33)**, p. 237: the average markup (constants dropped)
`μ = p_H − (w − a + αn)`, with the labour supply condition (7) `w − p = σc + φn`, the CPI
identity (12) `p − p_H = υs`, risk sharing (17), goods-market clearing (25) and the
production function (32), equals
`−(σ + (φ+α)/(1−α))y + υ(ϖ − 1)s + (1 + (φ+α)/(1−α))a − υz`. -/
theorem eq33 {σ η υ φ α mu pH w p a n c s y ystar z : ℝ} (hσ : σ ≠ 0) (hα : α < 1)
    (hmu : mu = pH - (w - a + α * n)) (h7 : w - p = σ * c + φ * n) (h12 : p - pH = υ * s)
    (h17 : c = ystar + z / σ + (1 - υ) / σ * s)
    (h25 : y = (1 - υ) * c + υ * (2 - υ) * η * s + υ * ystar) (h32 : y = a + (1 - α) * n) :
    mu = -(σ + (φ + α) / (1 - α)) * y + υ * (varpi σ η υ - 1) * s
      + (1 + (φ + α) / (1 - α)) * a - υ * z := by
  have h1 : (1 : ℝ) - α ≠ 0 := by linarith
  have key : σ * (y - ystar) = (1 - υ) * z + (1 + υ * (varpi σ η υ - 1)) * s := by
    rw [h25, h17]
    unfold varpi
    field_simp
    ring
  rw [hmu]
  linear_combination (norm := skip) (-1 : ℝ) * h7 - h12 - σ * h17 + key
    + ((φ + α) / (1 - α)) * h32
  field_simp
  ring

/-- Galí (2015), p. 237: `κ ≡ λ(σ + (φ+α)/(1−α))`, the closed-economy slope of Chapter 3. -/
noncomputable def kappa (lam σ φ α : ℝ) : ℝ := lam * (σ + (φ + α) / (1 - α))

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), **(34)**, p. 237: combining (22) `π_{H,t} = βE_t π_{H,t+1} − λμ̂_t` with the
markup (33) gives
`π_{H,t} = βE_t π_{H,t+1} + κy_t − λυ(ϖ − 1)s_t − λ(1 + (φ+α)/(1−α))a_t + λυz_t`. -/
theorem eq34 {lam β σ η υ φ α : ℝ} {inflH mu y s a z : ℕ → Ω → ℝ} (t : ℕ)
    (h22 : inflH t = β • 𝔼.E t (inflH (t + 1)) - lam • mu t)
    (h33 : mu t = (-(σ + (φ + α) / (1 - α))) • y t + (υ * (varpi σ η υ - 1)) • s t
      + (1 + (φ + α) / (1 - α)) • a t - υ • z t) :
    inflH t = β • 𝔼.E t (inflH (t + 1)) + kappa lam σ φ α • y t
      - (lam * υ * (varpi σ η υ - 1)) • s t - (lam * (1 + (φ + α) / (1 - α))) • a t
      + (lam * υ) • z t := by
  rw [h22, h33]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, kappa]
  ring

/-! ### Natural output, (35) -/

/-- Galí (2015), p. 238: the denominator `σ_υ(1 − α) + φ + α` of the `Γ` coefficients. -/
noncomputable def natDen (σ η υ φ α : ℝ) : ℝ := sigmaU σ η υ * (1 - α) + φ + α

/-- Galí (2015), (35), p. 238: `Γ_a ≡ (1 + φ)/(σ_υ(1 − α) + φ + α)`. -/
noncomputable def GammaA (σ η υ φ α : ℝ) : ℝ := (1 + φ) / natDen σ η υ φ α

/-- Galí (2015), (35), p. 238: `Γ_* ≡ −υ(ϖ − 1)σ_υ(1 − α)/(σ_υ(1 − α) + φ + α)`. -/
noncomputable def GammaStar (σ η υ φ α : ℝ) : ℝ :=
  -(υ * (varpi σ η υ - 1) * sigmaU σ η υ * (1 - α)) / natDen σ η υ φ α

/-- Galí (2015), (35), p. 238: `Γ_z ≡ −υϖΦ(1 − α)/(σ_υ(1 − α) + φ + α)`. -/
noncomputable def GammaZ (σ η υ φ α : ℝ) : ℝ :=
  -(υ * varpi σ η υ * Phi σ η υ * (1 - α)) / natDen σ η υ φ α

/-- Galí (2015), p. 238: the denominator `σ_υ(1 − α) + φ + α` is positive. -/
theorem natDen_pos {σ η υ φ α : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hυ0 : 0 ≤ υ) (hυ1 : υ ≤ 1)
    (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) : 0 < natDen σ η υ φ α := by
  unfold natDen
  have := mul_pos (sigmaU_pos hσ hη hυ0 hυ1) (sub_pos.2 hα1)
  linarith

/-- Galí (2015), (35), p. 238: `Γ_a > 0`. -/
theorem GammaA_pos {σ η υ φ α : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hυ0 : 0 ≤ υ) (hυ1 : υ ≤ 1)
    (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) : 0 < GammaA σ η υ φ α :=
  div_pos (by linarith) (natDen_pos hσ hη hυ0 hυ1 hφ hα0 hα1)

/-- Galí (2015), p. 238, **the key identity** `σ − υ(ϖ − 1)σ_υ = σ_υ`. -/
theorem sigma_sub_eq_sigmaU {σ η υ : ℝ} (hD : 1 + υ * (varpi σ η υ - 1) ≠ 0) :
    σ - υ * (varpi σ η υ - 1) * sigmaU σ η υ = sigmaU σ η υ := by
  have := sigmaU_mul hD
  linear_combination -this

/-- Galí (2015), (35), p. 238: `(σ_υ + (φ+α)/(1−α))Γ_a = 1 + (φ+α)/(1−α)`. -/
theorem mul_GammaA {σ η υ φ α : ℝ} (hα : α ≠ 1) (hden : natDen σ η υ φ α ≠ 0) :
    (sigmaU σ η υ + (φ + α) / (1 - α)) * GammaA σ η υ φ α = 1 + (φ + α) / (1 - α) := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  unfold GammaA
  unfold natDen at hden ⊢
  field_simp
  ring

/-- Galí (2015), (35), p. 238: `(σ_υ + (φ+α)/(1−α))Γ_* = −υ(ϖ − 1)σ_υ`. -/
theorem mul_GammaStar {σ η υ φ α : ℝ} (hα : α ≠ 1) (hden : natDen σ η υ φ α ≠ 0) :
    (sigmaU σ η υ + (φ + α) / (1 - α)) * GammaStar σ η υ φ α
      = -(υ * (varpi σ η υ - 1) * sigmaU σ η υ) := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  unfold GammaStar
  unfold natDen at hden ⊢
  field_simp
  ring

/-- Galí (2015), (35), p. 238: `(σ_υ + (φ+α)/(1−α))Γ_z = −υϖΦ`. -/
theorem mul_GammaZ {σ η υ φ α : ℝ} (hα : α ≠ 1) (hden : natDen σ η υ φ α ≠ 0) :
    (sigmaU σ η υ + (φ + α) / (1 - α)) * GammaZ σ η υ φ α
      = -(υ * varpi σ η υ * Phi σ η υ) := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  unfold GammaZ
  unfold natDen at hden ⊢
  field_simp
  ring

/-- Galí (2015), (35), p. 238: after substituting the natural terms of trade (27), the
markup (33) at natural output equals `−(σ_υ + (φ+α)/(1−α))(yⁿ − Γ_a a − Γ_z z − Γ_*y*)`. -/
theorem markup_natural {σ η υ φ α yn a z ystar : ℝ} (hα : α ≠ 1)
    (hD : 1 + υ * (varpi σ η υ - 1) ≠ 0) (hden : natDen σ η υ φ α ≠ 0) :
    -(σ + (φ + α) / (1 - α)) * yn + υ * (varpi σ η υ - 1) *
        (sigmaU σ η υ * (yn - ystar) - (1 - υ) * Phi σ η υ * z)
      + (1 + (φ + α) / (1 - α)) * a - υ * z
    = -(sigmaU σ η υ + (φ + α) / (1 - α)) *
        (yn - (GammaA σ η υ φ α * a + GammaZ σ η υ φ α * z + GammaStar σ η υ φ α * ystar)) := by
  have pA := mul_GammaA hα hden
  have pS := mul_GammaStar hα hden
  have pZ := mul_GammaZ hα hden
  have hσD := sigmaU_mul hD
  have hΦD : Phi σ η υ * (1 + υ * (varpi σ η υ - 1)) = 1 := by
    unfold Phi
    field_simp
  linear_combination (-a) * pA + (-z) * pZ + (-ystar) * pS + yn * hσD + (υ * z) * hΦD

/-- Galí (2015), **(35)**, p. 238: with the natural terms of trade given by (27),
`sⁿ = σ_υ(yⁿ − y*) − (1 − υ)Φz`, the flexible-price markup condition (the markup (33) at its
steady-state value, zero once constants are dropped) holds **if and only if**
`yⁿ = Γ_a a + Γ_z z + Γ_* y*`. -/
theorem eq35_iff {σ η υ φ α yn sn a z ystar : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hυ0 : 0 ≤ υ)
    (hυ1 : υ ≤ 1) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (h27 : sn = sigmaU σ η υ * (yn - ystar) - (1 - υ) * Phi σ η υ * z) :
    0 = -(σ + (φ + α) / (1 - α)) * yn + υ * (varpi σ η υ - 1) * sn
      + (1 + (φ + α) / (1 - α)) * a - υ * z ↔
    yn = GammaA σ η υ φ α * a + GammaZ σ η υ φ α * z + GammaStar σ η υ φ α * ystar := by
  have hD := (one_add_mul_varpi_pos hσ hη hυ0 hυ1).ne'
  have hden := (natDen_pos hσ hη hυ0 hυ1 hφ hα0 hα1).ne'
  have hk : 0 < sigmaU σ η υ + (φ + α) / (1 - α) :=
    add_pos_of_pos_of_nonneg (sigmaU_pos hσ hη hυ0 hυ1) (div_nonneg (by linarith)
      (by linarith))
  rw [h27, markup_natural hα1.ne hD hden]
  constructor
  · intro h
    have h0 := h.symm
    rcases mul_eq_zero.1 h0 with h1 | h1
    · linarith
    · linarith
  · intro h
    rw [h]
    ring

/-- Galí (2015), p. 238: **with `σ = η = 1`, world output does not affect natural output**,
`Γ_* = 0`. -/
theorem GammaStar_unit (υ φ α : ℝ) : GammaStar 1 1 υ φ α = 0 := by
  simp [GammaStar, varpi]

/-- Galí (2015), p. 238: **with `σ = η = 1`, preference shocks lower natural output**,
`Γ_z < 0`, provided the economy is open (`υ > 0`; `Γ_z = 0` at `υ = 0`, fn. 8). -/
theorem GammaZ_unit_neg {υ φ α : ℝ} (hυ0 : 0 < υ) (hυ1 : υ ≤ 1) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) : GammaZ 1 1 υ φ α < 0 := by
  have hden := natDen_pos one_pos one_pos hυ0.le hυ1 hφ hα0 hα1
  have hΦ := Phi_pos (σ := 1) (η := 1) one_pos one_pos hυ0.le hυ1
  have hv : varpi 1 1 υ = 1 := by simp [varpi]
  unfold GammaZ
  rw [hv]
  apply div_neg_of_neg_of_pos _ hden
  have : 0 < υ * 1 * Phi 1 1 υ * (1 - α) := by
    have := sub_pos.2 hα1
    positivity
  linarith

/-- Galí (2015), fn. 8, p. 238: in the closed economy (`υ = 0`), `Γ_z = 0`. -/
theorem GammaZ_zero (σ η φ α : ℝ) : GammaZ σ η 0 φ α = 0 := by
  simp [GammaZ]

/-- Galí (2015), p. 238: in the closed economy (`υ = 0`), `Γ_* = 0`. -/
theorem GammaStar_zero (σ η φ α : ℝ) : GammaStar σ η 0 φ α = 0 := by
  simp [GammaStar]

/-! ### The open-economy New Keynesian Phillips curve, (36)–(37) -/

/-- Galí (2015), p. 238: subtracting (27) at the natural level gives the terms-of-trade gap
`s̃ = σ_υỹ`. -/
theorem sgap_eq {σ η υ s sn y yn ystar z : ℝ}
    (h27 : s = sigmaU σ η υ * (y - ystar) - (1 - υ) * Phi σ η υ * z)
    (h27n : sn = sigmaU σ η υ * (yn - ystar) - (1 - υ) * Phi σ η υ * z) :
    s - sn = sigmaU σ η υ * (y - yn) := by
  rw [h27, h27n]
  ring

/-- Galí (2015), **(36)**, p. 238: subtracting the markup (33) at the natural level from the
actual markup and using `s̃ = σ_υỹ`, `μ̂ = −(σ_υ + (φ+α)/(1−α))ỹ`. -/
theorem eq36 {σ η υ φ α mu mun y yn s sn a z ystar : ℝ}
    (hD : 1 + υ * (varpi σ η υ - 1) ≠ 0)
    (h33 : mu = -(σ + (φ + α) / (1 - α)) * y + υ * (varpi σ η υ - 1) * s
      + (1 + (φ + α) / (1 - α)) * a - υ * z)
    (h33n : mun = -(σ + (φ + α) / (1 - α)) * yn + υ * (varpi σ η υ - 1) * sn
      + (1 + (φ + α) / (1 - α)) * a - υ * z)
    (h27 : s = sigmaU σ η υ * (y - ystar) - (1 - υ) * Phi σ η υ * z)
    (h27n : sn = sigmaU σ η υ * (yn - ystar) - (1 - υ) * Phi σ η υ * z) :
    mu - mun = -(sigmaU σ η υ + (φ + α) / (1 - α)) * (y - yn) := by
  have hk := sigma_sub_eq_sigmaU hD
  have hs := sgap_eq h27 h27n
  rw [h33, h33n]
  linear_combination (υ * (varpi σ η υ - 1)) * hs - (y - yn) * hk

/-- Galí (2015), (37), p. 238: `κ_υ ≡ λ(σ_υ + (φ+α)/(1−α))`. -/
noncomputable def kappaU (lam σ η υ φ α : ℝ) : ℝ := lam * (sigmaU σ η υ + (φ + α) / (1 - α))

/-- Galí (2015), **(37)**, p. 238: the New Keynesian Phillips curve of the small open
economy. If domestic inflation satisfies (22) `π_{H,t} = βE_t π_{H,t+1} − λμ̂_t` with the
markup gap `μ̂_t = μ_t − μⁿ_t`, the markups are given by (33) at the actual and the natural
allocation, and the terms of trade by (27) in both, then
`π_{H,t} = βE_t π_{H,t+1} + κ_υ ỹ_t`, `ỹ_t = y_t − yⁿ_t`. -/
theorem eq37 {lam β σ η υ φ α : ℝ} (hD : 1 + υ * (varpi σ η υ - 1) ≠ 0)
    {inflH mu mun y yn s sn a z ystar : ℕ → Ω → ℝ} (t : ℕ)
    (h22 : inflH t = β • 𝔼.E t (inflH (t + 1)) - lam • (mu t - mun t))
    (h33 : mu t = (-(σ + (φ + α) / (1 - α))) • y t + (υ * (varpi σ η υ - 1)) • s t
      + (1 + (φ + α) / (1 - α)) • a t - υ • z t)
    (h33n : mun t = (-(σ + (φ + α) / (1 - α))) • yn t + (υ * (varpi σ η υ - 1)) • sn t
      + (1 + (φ + α) / (1 - α)) • a t - υ • z t)
    (h27 : s t = sigmaU σ η υ • (y t - ystar t) - ((1 - υ) * Phi σ η υ) • z t)
    (h27n : sn t = sigmaU σ η υ • (yn t - ystar t) - ((1 - υ) * Phi σ η υ) • z t) :
    inflH t = β • 𝔼.E t (inflH (t + 1)) + kappaU lam σ η υ φ α • (y t - yn t) := by
  rw [h22]
  funext ω
  have e1 := congrFun h33 ω
  have e2 := congrFun h33n ω
  have e3 := congrFun h27 ω
  have e4 := congrFun h27n ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 e4 ⊢
  have k := eq36 hD e1 e2 e3 e4
    (mu := mu t ω) (mun := mun t ω) (s := s t ω) (sn := sn t ω) (y := y t ω) (yn := yn t ω)
    (a := a t ω) (z := z t ω) (ystar := ystar t ω) (φ := φ) (α := α)
  unfold kappaU
  linear_combination (-lam) * k

/-- Galí (2015), p. 238: in the closed economy (`υ = 0`), `κ_υ = κ`. -/
theorem kappaU_zero (lam σ η φ α : ℝ) : kappaU lam σ η 0 φ α = kappa lam σ φ α := by
  simp [kappaU, kappa, sigmaU_zero]

/-- Galí (2015), p. 238: with `σ = η = 1`, `κ_υ = κ` for every degree of openness. -/
theorem kappaU_unit (lam υ φ α : ℝ) : kappaU lam 1 1 υ φ α = kappa lam 1 φ α := by
  simp [kappaU, kappa, sigmaU_of_sigma_mul_eta (σ := 1) (η := 1) (by norm_num)]

/-- Galí (2015), p. 239: **if `ση > 1`, an increase in openness lowers `κ_υ`**: `κ_υ` is
strictly decreasing in `υ` on `[0, 1]` (for `λ > 0`). -/
theorem kappaU_strictAntiOn {lam σ η φ α : ℝ} (hlam : 0 < lam) (hσ : 0 < σ) (hη : 0 < η)
    (h : 1 < σ * η) : StrictAntiOn (fun υ => kappaU lam σ η υ φ α) (Set.Icc 0 1) := by
  intro a ha b hb hab
  have := sigmaU_strictAntiOn hσ hη h ha hb hab
  simp only [kappaU]
  nlinarith

/-! ### The natural rate of interest, (38) -/

/-- Galí (2015), (38), p. 239: `Ψ_* ≡ σ_υ(υ(ϖ − 1) + Γ_*)`. -/
noncomputable def PsiStar (σ η υ φ α : ℝ) : ℝ :=
  sigmaU σ η υ * (υ * (varpi σ η υ - 1) + GammaStar σ η υ φ α)

/-- Galí (2015), (38), p. 239: `Ψ_z ≡ (1 − υ)Φ − σ_υΓ_z`. -/
noncomputable def PsiZ (σ η υ φ α : ℝ) : ℝ :=
  (1 - υ) * Phi σ η υ - sigmaU σ η υ * GammaZ σ η υ φ α

/-- Galí (2015), **(38)**, p. 239: combining the natural rate (30) with natural output (35)
and AR(1) technology and preference shocks (`E_t a_{t+1} = ρ_a a_t`, `E_t z_{t+1} = ρ_z z_t`),
`rⁿ_t = ρ − σ_υΓ_a(1 − ρ_a)a_t + Ψ_*E_tΔy*_{t+1} + Ψ_z(1 − ρ_z)z_t`. -/
theorem eq38 {σ η υ φ α ρ ρz ρa : ℝ} {yn a z ystar : ℕ → Ω → ℝ} (t : ℕ)
    (hyn : ∀ t, yn t = GammaA σ η υ φ α • a t + GammaZ σ η υ φ α • z t
      + GammaStar σ η υ φ α • ystar t)
    (ha : 𝔼.E t (a (t + 1)) = ρa • a t) (hz : 𝔼.E t (z (t + 1)) = ρz • z t) :
    natRate 𝔼 σ η υ ρ ρz yn ystar z t
      = (fun _ => ρ) - (sigmaU σ η υ * GammaA σ η υ φ α * (1 - ρa)) • a t
        + PsiStar σ η υ φ α • (𝔼.E t (ystar (t + 1)) - ystar t)
        + (PsiZ σ η υ φ α * (1 - ρz)) • z t := by
  unfold natRate PsiStar PsiZ
  rw [hyn (t + 1), hyn t, map_add, map_add, map_smul, map_smul, map_smul, ha, hz]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), p. 239: in the closed economy `Ψ_* = 0`. -/
theorem PsiStar_zero (σ η φ α : ℝ) : PsiStar σ η 0 φ α = 0 := by
  simp [PsiStar, GammaStar_zero]

/-- Galí (2015), p. 239: in the closed economy `Ψ_z = 1`. -/
theorem PsiZ_zero (σ η φ α : ℝ) : PsiZ σ η 0 φ α = 1 := by
  simp [PsiZ, GammaZ_zero, Phi]

/-- Galí (2015), p. 239: `σ_υ` is continuous in `υ` at `υ = 0`. -/
theorem continuousAt_sigmaU (σ η : ℝ) : ContinuousAt (fun υ => sigmaU σ η υ) 0 := by
  have hD : ContinuousAt (fun υ : ℝ => 1 + υ * (varpi σ η υ - 1)) 0 := by
    unfold varpi
    fun_prop
  have hPhi : ContinuousAt (fun υ => Phi σ η υ) 0 := continuousAt_const.div hD (by simp)
  exact continuousAt_const.mul hPhi

/-- Galí (2015), p. 239: **`lim_{υ→0} Ψ_* = 0`**. -/
theorem tendsto_PsiStar {σ η φ α : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    Tendsto (fun υ => PsiStar σ η υ φ α) (𝓝 0) (𝓝 0) := by
  have hsig := continuousAt_sigmaU σ η
  have hvar : ContinuousAt (fun υ => varpi σ η υ) 0 := by
    unfold varpi
    fun_prop
  have hden0 : natDen σ η 0 φ α ≠ 0 := by
    unfold natDen
    rw [sigmaU_zero]
    have := mul_pos hσ (sub_pos.2 hα1)
    linarith
  have hden : ContinuousAt (fun υ => natDen σ η υ φ α) 0 := by
    unfold natDen
    fun_prop
  have hG : ContinuousAt (fun υ => GammaStar σ η υ φ α) 0 := by
    unfold GammaStar
    exact ((((continuousAt_id.mul (hvar.sub continuousAt_const)).mul hsig).mul
      continuousAt_const).neg).div hden hden0
  have hP : ContinuousAt (fun υ => PsiStar σ η υ φ α) 0 := by
    unfold PsiStar
    exact hsig.mul ((continuousAt_id.mul (hvar.sub continuousAt_const)).add hG)
  have := hP.tendsto
  rwa [PsiStar_zero] at this

/-- Galí (2015), p. 239: **`lim_{υ→0} Ψ_z = 1`**. -/
theorem tendsto_PsiZ {σ η φ α : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    Tendsto (fun υ => PsiZ σ η υ φ α) (𝓝 0) (𝓝 1) := by
  have hsig := continuousAt_sigmaU σ η
  have hvar : ContinuousAt (fun υ => varpi σ η υ) 0 := by
    unfold varpi
    fun_prop
  have hD : ContinuousAt (fun υ : ℝ => 1 + υ * (varpi σ η υ - 1)) 0 :=
    continuousAt_const.add (continuousAt_id.mul (hvar.sub continuousAt_const))
  have hPhi : ContinuousAt (fun υ => Phi σ η υ) 0 := continuousAt_const.div hD (by simp)
  have hden0 : natDen σ η 0 φ α ≠ 0 := by
    unfold natDen
    rw [sigmaU_zero]
    have := mul_pos hσ (sub_pos.2 hα1)
    linarith
  have hden : ContinuousAt (fun υ => natDen σ η υ φ α) 0 := by
    unfold natDen
    fun_prop
  have hG : ContinuousAt (fun υ => GammaZ σ η υ φ α) 0 := by
    unfold GammaZ
    exact ((((continuousAt_id.mul hvar).mul hPhi).mul continuousAt_const).neg).div hden hden0
  have hP : ContinuousAt (fun υ => PsiZ σ η υ φ α) 0 := by
    unfold PsiZ
    exact ((continuousAt_const.sub continuousAt_id).mul hPhi).sub (hsig.mul hG)
  have := hP.tendsto
  rwa [PsiZ_zero] at this

end Gali.OpenEconomy.Supply
