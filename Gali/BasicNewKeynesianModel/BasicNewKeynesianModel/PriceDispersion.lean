/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.CES
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Price dispersion

Galí (2015), Chapter 3, §3.3 (pp. 58–59), eq. (14), and Appendix 3.4 (pp. 85–86).

Goods/firms form a probability space `(G, μ)` (the book's `[0, 1]` with Lebesgue measure, or
finitely many goods with weights summing to one). The dispersion term is
`d = (1 − α) log ∫ (P(i)/P)^{−ε/(1−α)} di`, with `P` the CES price index of `CES`.

## Main results

* `employment_level`, `employment_identity`: with `Y(i) = A N(i)^{1−α}` and the demand
  schedule, `N = (Y/A)^{1/(1−α)} ∫ (P(i)/P)^{−ε/(1−α)}` and hence exactly
  `(1 − α) log N = log Y − log A + d` (eq. (14) before approximation).
* `dispersion_nonneg`: `d ≥ 0` (Jensen, via a pointwise Bernoulli inequality).
* `dispersion_eq_zero_iff`, `dispersion_eq_zero_iff_const`: `d = 0` iff all prices equal
  (almost everywhere), i.e. iff `P(i) = P` a.e.
* `dispersion_second_order` (**App. 3.4**): along the family of price distributions
  `p(i) = p̄ + s z(i)` with `z` bounded and measurable (the index condition holding by
  construction of `P`), `d(s) = (ε/(2Θ)) var_i p(i) + O(s³)` as `s → 0`, with
  `Θ = (1 − α)/(1 − α + αε)`. This holds for an arbitrary probability space of goods, so in
  particular for the continuum `[0, 1]`.
* `dispersion_family_isBigO_sq`, `dispersion_family_first_order`: `d(s) = O(s²)`, `d(0) = 0`
  and `d'(0) = 0`: "`d_t` is equal to zero up to a first-order approximation" (p. 59).
* `relLogPrice_moments`, `relLogPrice_mean_second_order`, `relLogPrice_sq_second_order`: the
  intermediate steps of App. 3.4, `E_i p̂ = ((ε − 1)/2) E_i p̂² + O(s³)` and
  `E_i p̂² = var_i p + O(s⁴)`, with `p̂(i) = p(i) − p`.

The proof of the second-order result writes `d(s)` exactly in terms of the cumulant-generating
function `K` of `z`, `d(s) = (1 − α) K(−εs/(1−α)) + (ε/(1−ε)) K((1−ε)s)`, and applies
Taylor's theorem to the analytic function `K` (`K(0) = 0`, `K'(0) = E z`, `K''(0) = var z`).
-/

namespace Gali.BasicNewKeynesianModel.PriceDispersion

open MeasureTheory ProbabilityTheory Gali.BasicNewKeynesianModel.CES

variable {G : Type*} [MeasurableSpace G]

/-- Galí (2015), p. 59 and App. 3.4, p. 86: the price-dispersion term
`d = (1 − α) log ∫ (P(i)/P)^{−ε/(1−α)} di`. -/
noncomputable def dispersion (μ : Measure G) (α ε : ℝ) (P : G → ℝ) : ℝ :=
  (1 - α) * Real.log (∫ i, (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) ∂μ)

/-- Galí (2015), p. 60 and App. 3.4, p. 86: `Θ = (1 − α)/(1 − α + αε)`. -/
noncomputable def bigTheta (α ε : ℝ) : ℝ := (1 - α) / (1 - α + α * ε)

/-- Galí (2015), App. 3.4, p. 86: the cross-sectional variance
`var_i p(i) = ∫ (p(i) − ∫ p)² di`. -/
noncomputable def crossVar (μ : Measure G) (p : G → ℝ) : ℝ :=
  ∫ i, (p i - ∫ j, p j ∂μ) ^ 2 ∂μ

variable {μ : Measure G} {α ε : ℝ} {P : G → ℝ}

/-- Galí (2015), p. 59: with production `Y(i) = A N(i)^{1−α}` (5) and output on the demand
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

/-- Galí (2015), p. 59, eq. (14) before approximation (**exact**):
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

/-- Galí (2015), App. 3.4, p. 85: the exponent `q = ε/((ε − 1)(1 − α))` turning
`y(i) = (P(i)/P)^{1−ε}` into `y(i)^q = (P(i)/P)^{−ε/(1−α)}` exceeds one. -/
theorem one_lt_q (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) : 1 < ε / ((ε - 1) * (1 - α)) := by
  rw [one_lt_div (by apply mul_pos <;> linarith)]
  nlinarith

/-- Galí (2015), App. 3.4, p. 85: `(P(i)/P)^{−ε/(1−α)} = ((P(i)/P)^{1−ε})^q`. -/
theorem rpow_disp_eq (hε : 1 < ε) (hα1 : α < 1) {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-ε / (1 - α)) = (x ^ (1 - ε)) ^ (ε / ((ε - 1) * (1 - α))) := by
  rw [← Real.rpow_mul hx]
  congr 1
  have : (1 : ℝ) - α ≠ 0 := by linarith
  have : ε - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- Galí (2015), App. 3.4, p. 85: the pointwise Bernoulli bound
`(P(i)/P)^{−ε/(1−α)} ≥ 1 + q((P(i)/P)^{1−ε} − 1)`, strict unless `P(i) = P`. -/
theorem bernoulli_disp (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) {x : ℝ} (hx : 0 < x) :
    1 + ε / ((ε - 1) * (1 - α)) * (x ^ (1 - ε) - 1) ≤ x ^ (-ε / (1 - α)) ∧
      (1 + ε / ((ε - 1) * (1 - α)) * (x ^ (1 - ε) - 1) = x ^ (-ε / (1 - α)) → x = 1) := by
  have hy : 0 < x ^ (1 - ε) := Real.rpow_pos_of_pos hx _
  have hs : -1 ≤ x ^ (1 - ε) - 1 := by linarith
  rw [rpow_disp_eq hε hα1 hx.le]
  have hq := one_lt_q hε hα0 hα1
  refine ⟨by simpa using one_add_mul_self_le_rpow_one_add hs hq.le, fun heq => ?_⟩
  by_contra hne
  have hy1 : x ^ (1 - ε) - 1 ≠ 0 := by
    intro h0
    have h1 : x ^ (1 - ε) = 1 := by linarith
    have hsub : (1 : ℝ) - ε ≠ 0 := by linarith
    apply hne
    rw [← Real.rpow_rpow_inv hx.le hsub, h1, Real.one_rpow]
  have := one_add_mul_self_lt_rpow_one_add hs hy1 hq
  simp only [add_sub_cancel] at this
  linarith

/-- Galí (2015), App. 3.4, p. 85: the Bernoulli lower bound integrates to one,
`∫ (1 + q((P(i)/P)^{1−ε} − 1)) = 1`, by the index condition (probability measure). -/
theorem integral_bernoulli_lower [IsProbabilityMeasure μ] (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (q : ℝ) :
    Integrable (fun i => 1 + q * ((P i / priceIndex μ ε P) ^ (1 - ε) - 1)) μ ∧
      ∫ i, (1 + q * ((P i / priceIndex μ ε P) ^ (1 - ε) - 1)) ∂μ = 1 := by
  have hpos := integral_pos_of_pos (IsProbabilityMeasure.ne_zero μ)
    (fun i => Real.rpow_pos_of_pos (hP i) (1 - ε)) hPi
  have hy := integrable_relPrice_rpow hPi hP hpos
  have he : (fun i => 1 + q * ((P i / priceIndex μ ε P) ^ (1 - ε) - 1))
      = fun i => (1 - q) + q * (P i / priceIndex μ ε P) ^ (1 - ε) := by
    funext i
    ring
  rw [he]
  refine ⟨(integrable_const _).add (hy.const_mul q), ?_⟩
  rw [integral_add (integrable_const _) (hy.const_mul q), integral_const, integral_const_mul,
    integral_relPrice_rpow hε hP hpos]
  simp

/-- Galí (2015), App. 3.4, p. 85 (Jensen): with the index condition `∫ (P(i)/P)^{1−ε} = 1`,
`∫ (P(i)/P)^{−ε/(1−α)} ≥ 1`. -/
theorem one_le_integral_disp [IsProbabilityMeasure μ] (hε : 1 < ε) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hP : ∀ i, 0 < P i) (hPi : Integrable (fun i => P i ^ (1 - ε)) μ)
    (hD : Integrable (fun i => (P i / priceIndex μ ε P) ^ (-ε / (1 - α))) μ) :
    1 ≤ ∫ i, (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) ∂μ := by
  have hpos := integral_pos_of_pos (IsProbabilityMeasure.ne_zero μ)
    (fun i => Real.rpow_pos_of_pos (hP i) (1 - ε)) hPi
  have hI := priceIndex_pos hpos
  obtain ⟨hlow, hval⟩ := integral_bernoulli_lower hε hP hPi (ε / ((ε - 1) * (1 - α)))
  have h := integral_mono hlow hD fun i => (bernoulli_disp hε hα0 hα1 (div_pos (hP i) hI)).1
  rwa [hval] at h

/-- Galí (2015), App. 3.4, p. 85: **price dispersion is nonnegative**, `d ≥ 0`. -/
theorem dispersion_nonneg [IsProbabilityMeasure μ] (hε : 1 < ε) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hP : ∀ i, 0 < P i) (hPi : Integrable (fun i => P i ^ (1 - ε)) μ)
    (hD : Integrable (fun i => (P i / priceIndex μ ε P) ^ (-ε / (1 - α))) μ) :
    0 ≤ dispersion μ α ε P :=
  mul_nonneg (by linarith) (Real.log_nonneg (one_le_integral_disp hε hα0 hα1 hP hPi hD))

/-- Galí (2015), p. 59 and App. 3.4, p. 85: `d = 0` **iff** every price equals the index,
`P(i) = P` for almost every `i`. -/
theorem dispersion_eq_zero_iff [IsProbabilityMeasure μ] (hε : 1 < ε) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hP : ∀ i, 0 < P i) (hPi : Integrable (fun i => P i ^ (1 - ε)) μ)
    (hD : Integrable (fun i => (P i / priceIndex μ ε P) ^ (-ε / (1 - α))) μ) :
    dispersion μ α ε P = 0 ↔ ∀ᵐ i ∂μ, P i = priceIndex μ ε P := by
  have hpos := integral_pos_of_pos (IsProbabilityMeasure.ne_zero μ)
    (fun i => Real.rpow_pos_of_pos (hP i) (1 - ε)) hPi
  have hI := priceIndex_pos hpos
  have hsub : (1 : ℝ) - α ≠ 0 := by linarith
  constructor
  · intro h0
    have hlog : Real.log (∫ i, (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) ∂μ) = 0 := by
      rw [dispersion] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h hsub
      · exact h
    have h1 := one_le_integral_disp hε hα0 hα1 hP hPi hD
    have hint1 : ∫ i, (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) ∂μ = 1 := by
      rcases Real.log_eq_zero.1 hlog with h | h | h <;> [linarith; exact h; linarith]
    obtain ⟨hlow, hval⟩ := integral_bernoulli_lower hε hP hPi (ε / ((ε - 1) * (1 - α)))
    have hz := (integral_eq_zero_iff_of_nonneg (fun i => sub_nonneg.2
      (bernoulli_disp hε hα0 hα1 (div_pos (hP i) hI)).1) (hD.sub hlow)).1 (by
        rw [integral_sub hD hlow, hint1, hval, sub_self])
    filter_upwards [hz] with i hi
    simp only [Pi.zero_apply, sub_eq_zero] at hi
    have := (bernoulli_disp hε hα0 hα1 (div_pos (hP i) hI)).2 hi.symm
    rwa [div_eq_one_iff_eq hI.ne'] at this
  · intro h
    have hint1 : ∫ i, (P i / priceIndex μ ε P) ^ (-ε / (1 - α)) ∂μ = 1 := by
      rw [integral_congr_ae (g := fun _ => (1 : ℝ)) (by
        filter_upwards [h] with i hi
        rw [hi, div_self hI.ne', Real.one_rpow])]
      simp
    rw [dispersion, hint1, Real.log_one, mul_zero]

/-- Galí (2015), p. 59: `d = 0` iff all prices are equal (to some common value `c`, which
is then the price index). -/
theorem dispersion_eq_zero_iff_const [IsProbabilityMeasure μ] (hε : 1 < ε) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hP : ∀ i, 0 < P i) (hPi : Integrable (fun i => P i ^ (1 - ε)) μ)
    (hD : Integrable (fun i => (P i / priceIndex μ ε P) ^ (-ε / (1 - α))) μ) :
    dispersion μ α ε P = 0 ↔ ∃ c, ∀ᵐ i ∂μ, P i = c := by
  rw [dispersion_eq_zero_iff hε hα0 hα1 hP hPi hD]
  refine ⟨fun h => ⟨_, h⟩, fun ⟨c, hc⟩ => ?_⟩
  obtain ⟨i₀, hi₀⟩ := hc.exists
  have hc0 : 0 < c := hi₀ ▸ hP i₀
  have hidx : priceIndex μ ε P = c := by
    unfold priceIndex
    rw [integral_congr_ae (g := fun _ => c ^ (1 - ε)) (by
      filter_upwards [hc] with i hi
      rw [hi])]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    exact Real.rpow_rpow_inv hc0.le (by linarith)
  rw [hidx]
  exact hc

/-- Galí (2015), App. 3.4, p. 85: for a bounded measurable `z` on a probability space, every
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

/-- Galí (2015), App. 3.4, p. 85: for bounded `z`, the cumulant-generating function is
analytic on all of `ℝ` (the domain of finiteness of the mgf is `ℝ`). -/
theorem interior_integrableExpSet [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ i, |z i| ≤ B) : interior (integrableExpSet z μ) = Set.univ := by
  have : integrableExpSet z μ = Set.univ :=
    Set.eq_univ_of_forall fun t => integrable_exp_mul hz hB t
  rw [this, interior_univ]

/-- Galí (2015), App. 3.4, pp. 85–86: **second-order Taylor expansion of the cumulant
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

/-- Galí (2015), App. 3.4, pp. 85–86: the Taylor remainder of `K` along a ray,
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

/-- Galí (2015), App. 3.4, p. 85: along the family `P(i) = exp(p̄ + s z(i))` the log price
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

/-- Galí (2015), App. 3.4, p. 85: along the family `P(i) = exp(p̄ + s z(i))`, the dispersion
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

/-- Galí (2015), App. 3.4, p. 86: the cross-sectional variance of `p(i) = p̄ + s z(i)` is
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

/-- Galí (2015), App. 3.4, pp. 85–86 (**second-order approximation of price dispersion**):
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

/-- Galí (2015), p. 59 and App. 3.4: along the family `p(i) = p̄ + s z(i)`, `d(s) = O(s²)`. -/
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

/-- Galí (2015), p. 59 (**`d_t` vanishes to first order**): along the family
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

/-- Galí (2015), App. 3.4, p. 85: the log relative price `p̂(i) = p(i) − p` along the family
`p(i) = p̄ + s z(i)`, with `p` the log CES price index. -/
noncomputable def relLogPrice (μ : Measure G) (ε : ℝ) (z : G → ℝ) (pbar s : ℝ) (i : G) : ℝ :=
  pbar + s * z i - Real.log (priceIndex μ ε (fun j => Real.exp (pbar + s * z j)))

/-- Galí (2015), App. 3.4, pp. 85–86 (exact moments of `p̂`): `E_i p̂ = s E z − K((1−ε)s)/(1−ε)`
and `E_i p̂² = var_i p + (E_i p̂)²`. -/
theorem relLogPrice_moments [IsProbabilityMeasure μ] {z : G → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ i, |z i| ≤ B) (hε : ε ≠ 1) (pbar s : ℝ) :
    ∫ i, relLogPrice μ ε z pbar s i ∂μ
        = s * (∫ i, z i ∂μ) - cgf z μ ((1 - ε) * s) / (1 - ε) ∧
      ∫ i, relLogPrice μ ε z pbar s i ^ 2 ∂μ
        = crossVar μ (fun i => pbar + s * z i) + (∫ i, relLogPrice μ ε z pbar s i ∂μ) ^ 2 := by
  have hzI : Integrable z μ :=
    Integrable.of_bound hz.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun i => by rw [Real.norm_eq_abs]; exact hB i)
  set m := ∫ i, z i ∂μ
  have hz2 : Integrable (fun i => (z i - m) ^ 2) μ := by
    refine Integrable.of_bound ((hz.sub measurable_const).pow_const 2).aestronglyMeasurable
      ((B + |m|) ^ 2) (Filter.Eventually.of_forall fun i => ?_)
    rw [Real.norm_eq_abs, abs_pow, sq_abs]
    have h1 : |z i - m| ≤ B + |m| := (abs_sub _ _).trans (by linarith [hB i])
    calc (z i - m) ^ 2 = |z i - m| ^ 2 := (sq_abs _).symm
      _ ≤ (B + |m|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hzc : Integrable (fun i => z i - m) μ := hzI.sub (integrable_const m)
  have hzm : ∫ i, (z i - m) ∂μ = 0 := by
    rw [integral_sub hzI (integrable_const m)]
    simp [m]
  set e := s * m - cgf z μ ((1 - ε) * s) / (1 - ε)
  have hpt : ∀ i, relLogPrice μ ε z pbar s i = s * (z i - m) + e := by
    intro i
    rw [relLogPrice, priceIndex_family hz hB hε, Real.log_exp]
    ring
  have hmean : ∫ i, relLogPrice μ ε z pbar s i ∂μ = e := by
    simp_rw [hpt]
    rw [integral_add (hzc.const_mul s) (integrable_const e), integral_const_mul, hzm]
    simp
  refine ⟨hmean, ?_⟩
  rw [hmean, crossVar_family hz hB]
  have hsq : ∀ i, relLogPrice μ ε z pbar s i ^ 2
      = s ^ 2 * (z i - m) ^ 2 + (2 * s * e) * (z i - m) + e ^ 2 := by
    intro i
    rw [hpt]
    ring
  simp_rw [hsq]
  have hA : Integrable (fun i => s ^ 2 * (z i - m) ^ 2 + 2 * s * e * (z i - m)) μ :=
    (hz2.const_mul _).add (hzc.const_mul _)
  rw [integral_add hA (integrable_const _), integral_add (hz2.const_mul _) (hzc.const_mul _),
    integral_const_mul, integral_const_mul, hzm]
  simp [m]

/-- Galí (2015), App. 3.4, p. 85: `E_i p̂ = ((ε − 1)/2) E_i p̂² + O(s³)` along the family
`p(i) = p̄ + s z(i)` (the second-order consequence of the index condition). -/
theorem relLogPrice_mean_second_order [IsProbabilityMeasure μ] {z : G → ℝ}
    (hz : Measurable z) {B : ℝ} (hB : ∀ i, |z i| ≤ B) (hε : 1 < ε) (pbar : ℝ) :
    (fun s => ∫ i, relLogPrice μ ε z pbar s i ∂μ -
        (ε - 1) / 2 * ∫ i, relLogPrice μ ε z pbar s i ^ 2 ∂μ) =O[nhds 0] fun s => s ^ 3 := by
  have hsubε : (1 : ℝ) - ε ≠ 0 := by linarith
  have hR := cgf_taylor_comp (μ := μ) hz hB (1 - ε)
  set m := ∫ i, z i ∂μ
  set v := ∫ i, (z i - m) ^ 2 ∂μ
  set R : ℝ → ℝ := fun s => cgf z μ ((1 - ε) * s) - m * ((1 - ε) * s) - v / 2 * ((1 - ε) * s) ^ 2
  have hmean : ∀ s, ∫ i, relLogPrice μ ε z pbar s i ∂μ
      = -(R s / (1 - ε)) - (1 - ε) * v / 2 * s ^ 2 := by
    intro s
    rw [(relLogPrice_moments hz hB hε.ne' pbar s).1]
    simp only [R]
    field_simp
    ring
  have hE : (fun s => ∫ i, relLogPrice μ ε z pbar s i ∂μ) =O[nhds 0] fun s => s ^ 2 := by
    have h32 : (fun s : ℝ => s ^ 3) =O[nhds 0] fun s => s ^ 2 :=
      (Asymptotics.isLittleO_pow_pow (by norm_num : 2 < 3)).isBigO
    have : (fun s => ∫ i, relLogPrice μ ε z pbar s i ∂μ)
        = fun s => (-(1 - ε)⁻¹) * R s + (-((1 - ε) * v / 2)) * s ^ 2 := by
      funext s
      rw [hmean]
      field_simp
      ring
    rw [this]
    exact ((hR.trans h32).const_mul_left _).add ((Asymptotics.isBigO_refl _ _).const_mul_left _)
  have hE2 : (fun s => (∫ i, relLogPrice μ ε z pbar s i ∂μ) *
      (∫ i, relLogPrice μ ε z pbar s i ∂μ)) =O[nhds 0] fun s => s ^ 3 := by
    have h4 := hE.mul hE
    have e4 : (fun s : ℝ => s ^ 2 * s ^ 2) = fun s => s ^ 4 := by
      funext s
      ring
    rw [e4] at h4
    exact h4.trans (Asymptotics.isLittleO_pow_pow (by norm_num : 3 < 4)).isBigO
  have heq : (fun s => ∫ i, relLogPrice μ ε z pbar s i ∂μ -
        (ε - 1) / 2 * ∫ i, relLogPrice μ ε z pbar s i ^ 2 ∂μ)
      = fun s => (-(1 - ε)⁻¹) * R s + (-((ε - 1) / 2)) *
          ((∫ i, relLogPrice μ ε z pbar s i ∂μ) * (∫ i, relLogPrice μ ε z pbar s i ∂μ)) := by
    funext s
    rw [(relLogPrice_moments hz hB hε.ne' pbar s).2, crossVar_family hz hB, hmean]
    field_simp
    ring
  rw [heq]
  exact (hR.const_mul_left _).add (hE2.const_mul_left _)

/-- Galí (2015), App. 3.4, p. 86: `∫ (p(i) − p)² di ≃ var_i p(i)`; precisely, along the family
`p(i) = p̄ + s z(i)` the difference is `(E_i p̂)² = O(s⁴)`. -/
theorem relLogPrice_sq_second_order [IsProbabilityMeasure μ] {z : G → ℝ}
    (hz : Measurable z) {B : ℝ} (hB : ∀ i, |z i| ≤ B) (hε : 1 < ε) (pbar : ℝ) :
    (fun s => ∫ i, relLogPrice μ ε z pbar s i ^ 2 ∂μ - crossVar μ (fun i => pbar + s * z i))
      =O[nhds 0] fun s => s ^ 4 := by
  have hsubε : (1 : ℝ) - ε ≠ 0 := by linarith
  have hR := cgf_taylor_comp (μ := μ) hz hB (1 - ε)
  have h32 : (fun s : ℝ => s ^ 3) =O[nhds 0] fun s => s ^ 2 :=
    (Asymptotics.isLittleO_pow_pow (by norm_num : 2 < 3)).isBigO
  have hE : (fun s => ∫ i, relLogPrice μ ε z pbar s i ∂μ) =O[nhds 0] fun s => s ^ 2 := by
    have : (fun s => ∫ i, relLogPrice μ ε z pbar s i ∂μ)
        = fun s => (-(1 - ε)⁻¹) * (cgf z μ ((1 - ε) * s) - (∫ i, z i ∂μ) * ((1 - ε) * s) -
            (∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) / 2 * ((1 - ε) * s) ^ 2) +
          (-((1 - ε) * (∫ i, (z i - ∫ j, z j ∂μ) ^ 2 ∂μ) / 2)) * s ^ 2 := by
      funext s
      rw [(relLogPrice_moments hz hB hε.ne' pbar s).1]
      field_simp
      ring
    rw [this]
    exact ((hR.trans h32).const_mul_left _).add ((Asymptotics.isBigO_refl _ _).const_mul_left _)
  have heq : (fun s => ∫ i, relLogPrice μ ε z pbar s i ^ 2 ∂μ -
      crossVar μ (fun i => pbar + s * z i))
      = fun s => (∫ i, relLogPrice μ ε z pbar s i ∂μ) * (∫ i, relLogPrice μ ε z pbar s i ∂μ) := by
    funext s
    rw [(relLogPrice_moments hz hB hε.ne' pbar s).2]
    ring
  rw [heq]
  have h4 := hE.mul hE
  have e4 : (fun s : ℝ => s ^ 2 * s ^ 2) = fun s => s ^ 4 := by
    funext s
    ring
  rwa [e4] at h4

end Gali.BasicNewKeynesianModel.PriceDispersion
