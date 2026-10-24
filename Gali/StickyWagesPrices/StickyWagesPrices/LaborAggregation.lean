/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Labour aggregation, labour demand and the employment–output relation

Galí (2015), Chapter 6, §6.1.1 (pp. 164–165), eqs. (2)–(4), and §6.2 (pp. 170–171); the same
relation is restated in Appendix 6.1 (pp. 189–190).

Labour types are indexed by a measure space `(J, μ)`: the book's continuum `[0, 1]` with
Lebesgue measure is `μ = volume.restrict (Set.Icc 0 1)`, and finitely many types with weights
`w j` is `μ = Finite.weightMeasure w`. For `ε_w > 1` the labour index of a firm is
`N = (∫ N(j)^{1−1/ε_w} dj)^{ε_w/(ε_w−1)}` (2) and the wage index is
`W = (∫ W(j)^{1−ε_w} dj)^{1/(1−ε_w)}` (4). The CES machinery is restated from the Chapter 3
project (`CES.lean`), with goods and prices replaced by labour types and wages.

## Main results

* `wageBill_ge`, `wageBill_eq_iff`: every labour bundle costs at least `W · N` (its own index
  `N`), with equality **iff** it is on the labour-demand schedule (3) almost everywhere.
* `cost_min_iff`: (3) is the **unique cost minimiser**: among bundles delivering the index `N`,
  a bundle minimises the wage bill iff it equals `(W(j)/W)^{−ε_w} N` a.e.
* `laborIndex_demand`, `wageBill_demand`: (3) delivers `N` and the wage-bill identity
  `∫ W(j) N(i,j) dj = W N(i)` (p. 165).
* `unitInterval_cost_minimisation`, `Finite.finite_cost_minimisation`: the continuum `[0, 1]`
  and finitely many types with positive weights.
* `aggregate_employment`, `employment_identity`: with labour demand (3), production (1) and
  goods demand, `N = ∫∫ N(i,j) dj di = Δ_w Δ_p (Y/A)^{1/(1−α)}` **exactly**, hence
  `(1 − α) n = y − a + d_w + d_p` (pp. 170–171).
* `dW_nonneg`, `dP_nonneg`, `dW_eq_zero_iff`, `dP_eq_zero_iff` (and `_const` forms):
  `d_w, d_p ≥ 0`, with equality iff there is no wage (price) dispersion.
* `dW_family_first_order`, `dP_family_first_order`, `employment_first_order`: along
  one-parameter families of wage and price distributions `d_w`, `d_p` vanish with zero
  derivative, so `(1 − α) n = y − a` to first order (p. 171).
-/

namespace Gali.StickyWagesPrices.LaborAggregation

open MeasureTheory ProbabilityTheory

variable {J : Type*} [MeasurableSpace J]


/-- Galí (2015), eq. (4), p. 165: the wage index `W = (∫ W(j)^{1−ε} dj)^{1/(1−ε)}`. -/
noncomputable def cesIndex (μ : Measure J) (ε : ℝ) (W : J → ℝ) : ℝ :=
  (∫ j, W j ^ (1 - ε) ∂μ) ^ (1 - ε)⁻¹

/-- Galí (2015), eq. (2), p. 164: the CES labour index (2)
`N = (∫ N(j)^{(ε−1)/ε} dj)^{ε/(ε−1)}`. -/
noncomputable def laborIndex (μ : Measure J) (ε : ℝ) (n : J → ℝ) : ℝ :=
  (∫ j, n j ^ ((ε - 1) / ε) ∂μ) ^ ((ε - 1) / ε)⁻¹

/-- Galí (2015), eq. (3), p. 164: the labour-demand schedule `N(j) = (W(j)/W)^{−ε} N`. -/
noncomputable def laborDemand (μ : Measure J) (ε : ℝ) (W : J → ℝ) (N : ℝ) (j : J) : ℝ :=
  (W j / cesIndex μ ε W) ^ (-ε) * N

/-- Galí (2015), §6.1.1, p. 164: the exponent identity `(ε−1)/ε + 1/ε = 1`. -/
theorem r_add_inv {ε : ℝ} (hε : 1 < ε) : (ε - 1) / ε + 1 / ε = 1 := by
  have : ε ≠ 0 := by linarith
  field_simp
  ring

/-- Galí (2015), §6.1.1, p. 164: the factorisation behind `young_le`,
`n^r = (a n N^{−1/ε})^r (a^{1−ε} N^r)^{1/ε}` with `r = (ε − 1)/ε`. -/
theorem young_key {ε a n N : ℝ} (hε : 1 < ε) (ha : 0 < a) (hn : 0 ≤ n) (hN : 0 < N) :
    (a * n * N ^ (-1 / ε)) ^ ((ε - 1) / ε) * (a ^ (1 - ε) * N ^ ((ε - 1) / ε)) ^ (1 / ε)
      = n ^ ((ε - 1) / ε) := by
  have hε0 : (0 : ℝ) < ε := by linarith
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow ha.le hn,
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul ha.le,
    ← Real.rpow_mul hN.le, ← Real.rpow_mul hN.le]
  have e1 : a ^ ((ε - 1) / ε) * n ^ ((ε - 1) / ε) * N ^ (-1 / ε * ((ε - 1) / ε)) *
      (a ^ ((1 - ε) * (1 / ε)) * N ^ ((ε - 1) / ε * (1 / ε)))
      = n ^ ((ε - 1) / ε) * (a ^ ((ε - 1) / ε) * a ^ ((1 - ε) * (1 / ε))) *
        (N ^ (-1 / ε * ((ε - 1) / ε)) * N ^ ((ε - 1) / ε * (1 / ε))) := by ring
  rw [e1, ← Real.rpow_add ha, ← Real.rpow_add hN]
  have z1 : (ε - 1) / ε + (1 - ε) * (1 / ε) = 0 := by field_simp; ring
  have z2 : -1 / ε * ((ε - 1) / ε) + (ε - 1) / ε * (1 / ε) = 0 := by ring
  rw [z1, z2, Real.rpow_zero, Real.rpow_zero, mul_one, mul_one]

/-- Galí (2015), §6.1.1, p. 164: the pointwise weighted AM–GM (Young) inequality behind
cost minimisation. For a relative wage `a > 0`, a quantity `n ≥ 0` and an aggregate
`N > 0`, `n^r ≤ r (a n N^{−1/ε}) + (1/ε) a^{1−ε} N^r` with `r = (ε − 1)/ε`. -/
theorem young_le {ε a n N : ℝ} (hε : 1 < ε) (ha : 0 < a) (hn : 0 ≤ n) (hN : 0 < N) :
    n ^ ((ε - 1) / ε) ≤
      (ε - 1) / ε * (a * n * N ^ (-1 / ε)) + 1 / ε * (a ^ (1 - ε) * N ^ ((ε - 1) / ε)) := by
  have hε0 : (0 : ℝ) < ε := by linarith
  rw [← young_key hε ha hn hN]
  exact Real.geom_mean_le_arith_mean2_weighted (div_nonneg (by linarith) hε0.le)
    (by positivity) (by positivity) (by positivity) (r_add_inv hε)

/-- Galí (2015), §6.1.1, p. 164: equality in `young_le` holds iff `n = a^{−ε} N`, i.e. iff
the quantity lies on the labour-demand schedule (3). -/
theorem young_eq_iff {ε a n N : ℝ} (hε : 1 < ε) (ha : 0 < a) (hn : 0 ≤ n) (hN : 0 < N) :
    n ^ ((ε - 1) / ε) =
      (ε - 1) / ε * (a * n * N ^ (-1 / ε)) + 1 / ε * (a ^ (1 - ε) * N ^ ((ε - 1) / ε)) ↔
      n = a ^ (-ε) * N := by
  have hε0 : (0 : ℝ) < ε := by linarith
  rw [← young_key hε ha hn hN, Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos
    (div_pos (by linarith) hε0) (by positivity) (by positivity) (by positivity) (r_add_inv hε)]
  have hk : a * N ^ (-1 / ε) ≠ 0 := by positivity
  have hv : a ^ (1 - ε) * N ^ ((ε - 1) / ε) = a * N ^ (-1 / ε) * (a ^ (-ε) * N) := by
    have h1 : a ^ (1 - ε) = a * a ^ (-ε) := by
      rw [sub_eq_add_neg, Real.rpow_add ha, Real.rpow_one]
    have h2 : N ^ ((ε - 1) / ε) = N ^ (-1 / ε) * N := by
      have : (ε - 1) / ε = -1 / ε + 1 := by field_simp; ring
      rw [this, Real.rpow_add hN, Real.rpow_one]
    rw [h1, h2]
    ring
  rw [hv, show a * n * N ^ (-1 / ε) = a * N ^ (-1 / ε) * n by ring]
  exact mul_right_inj' hk

variable {μ : Measure J} {ε : ℝ} {W : J → ℝ}

/-- Galí (2015), §6.1.1, pp. 164–165: the wage index is positive when `∫ W(j)^{1−ε} > 0`. -/
theorem cesIndex_pos (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ) : 0 < cesIndex μ ε W :=
  Real.rpow_pos_of_pos hpos _

/-- Galí (2015), §6.1.1, pp. 164–165: `W^{1−ε} = ∫ W(j)^{1−ε} dj`, the defining property. -/
theorem cesIndex_rpow (hε : 1 < ε) (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ) :
    cesIndex μ ε W ^ (1 - ε) = ∫ j, W j ^ (1 - ε) ∂μ :=
  Real.rpow_inv_rpow hpos.le (by linarith)

/-- Galí (2015), eq. (4), p. 165 (index condition): `∫ (W(j)/W)^{1−ε} di = 1`. -/
theorem integral_relWage_rpow (hε : 1 < ε) (hW : ∀ j, 0 < W j)
    (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ) :
    ∫ j, (W j / cesIndex μ ε W) ^ (1 - ε) ∂μ = 1 := by
  have hI := cesIndex_pos hpos
  simp_rw [Real.div_rpow (hW _).le hI.le]
  rw [integral_div, cesIndex_rpow hε hpos, div_self hpos.ne']

/-- Galí (2015), eq. (4), p. 165: the relative-wage integrand `(W(j)/W)^{1−ε}` is integrable. -/
theorem integrable_relWage_rpow (hWi : Integrable (fun j => W j ^ (1 - ε)) μ) (hW : ∀ j, 0 < W j)
    (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ) :
    Integrable (fun j => (W j / cesIndex μ ε W) ^ (1 - ε)) μ := by
  have hI := cesIndex_pos hpos
  simp_rw [Real.div_rpow (hW _).le hI.le]
  exact hWi.div_const _

/-- Galí (2015), eq. (3), p. 164: the labour-demand schedule `N(j) = (W(j)/W)^{−ε} N` delivers
exactly the aggregate `N`. -/
theorem laborIndex_demand (hε : 1 < ε) (hW : ∀ j, 0 < W j) (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ)
    {N : ℝ} (hN : 0 ≤ N) : laborIndex μ ε (laborDemand μ ε W N) = N := by
  have hI := cesIndex_pos hpos
  have hε0 : (0 : ℝ) < ε := by linarith
  have hr : (ε - 1) / ε ≠ 0 := div_ne_zero (by linarith) hε0.ne'
  have hpt : ∀ j, laborDemand μ ε W N j ^ ((ε - 1) / ε)
      = N ^ ((ε - 1) / ε) * (W j / cesIndex μ ε W) ^ (1 - ε) := by
    intro j
    have ha : 0 < W j / cesIndex μ ε W := div_pos (hW j) hI
    rw [laborDemand, Real.mul_rpow (by positivity) hN, ← Real.rpow_mul ha.le]
    have : -ε * ((ε - 1) / ε) = 1 - ε := by field_simp; ring
    rw [this, mul_comm]
  unfold laborIndex
  simp_rw [hpt]
  rw [integral_const_mul, integral_relWage_rpow hε hW hpos, mul_one, Real.rpow_rpow_inv hN hr]

/-- Galí (2015), §6.1.1, pp. 164–165: `W(j) (W(j)/W)^{−ε} N = W N (W(j)/W)^{1−ε}` pointwise. -/
theorem wage_mul_demand (hW : ∀ j, 0 < W j) (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ) (N : ℝ)
    (j : J) : W j * laborDemand μ ε W N j
      = cesIndex μ ε W * N * (W j / cesIndex μ ε W) ^ (1 - ε) := by
  have hI := cesIndex_pos hpos
  have ha : 0 < W j / cesIndex μ ε W := div_pos (hW j) hI
  have h1 : (W j / cesIndex μ ε W) ^ (1 - ε)
      = W j / cesIndex μ ε W * (W j / cesIndex μ ε W) ^ (-ε) := by
    rw [sub_eq_add_neg, Real.rpow_add ha, Real.rpow_one]
  rw [laborDemand, h1]
  field_simp

/-- Galí (2015), §6.1.1, pp. 164–165: under the labour-demand schedule, the wage bill is
`∫ W(j) N(j) di = W N`. -/
theorem wageBill_demand (hε : 1 < ε) (hW : ∀ j, 0 < W j) (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ)
    (N : ℝ) : ∫ j, W j * laborDemand μ ε W N j ∂μ = cesIndex μ ε W * N := by
  simp_rw [wage_mul_demand hW hpos N]
  rw [integral_const_mul, integral_relWage_rpow hε hW hpos, mul_one]

/-- Galí (2015), §6.1.1, p. 164: the CES aggregate is nonnegative. -/
theorem laborIndex_nonneg {n : J → ℝ} (hn : ∀ j, 0 ≤ n j) : 0 ≤ laborIndex μ ε n :=
  Real.rpow_nonneg (integral_nonneg fun j => Real.rpow_nonneg (hn j) _) _

/-- Galí (2015), §6.1.1, p. 164: `N^r = ∫ N(j)^r` for the CES aggregate `N`. -/
theorem laborIndex_rpow (hε : 1 < ε) {n : J → ℝ} (hn : ∀ j, 0 ≤ n j) :
    laborIndex μ ε n ^ ((ε - 1) / ε) = ∫ j, n j ^ ((ε - 1) / ε) ∂μ :=
  Real.rpow_inv_rpow (integral_nonneg fun j => Real.rpow_nonneg (hn j) _)
    (div_ne_zero (by linarith) (by linarith))

/-- Galí (2015), §6.1.1, p. 164: the integrated Young bound. For a bundle with positive
aggregate `N`, `N^r ≤ r N^{−1/ε} (∫ W n)/W + (1/ε) N^r`. -/
theorem integrated_young (hε : 1 < ε) (hW : ∀ j, 0 < W j)
    (hWi : Integrable (fun j => W j ^ (1 - ε)) μ) (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ)
    {n : J → ℝ} (hn : ∀ j, 0 ≤ n j) (hWn : Integrable (fun j => W j * n j) μ)
    (hN : 0 < laborIndex μ ε n) :
    Integrable (fun j => (ε - 1) / ε * (laborIndex μ ε n ^ (-1 / ε) / cesIndex μ ε W) *
        (W j * n j) + 1 / ε * laborIndex μ ε n ^ ((ε - 1) / ε) *
          (W j / cesIndex μ ε W) ^ (1 - ε)) μ ∧
      (∀ j, n j ^ ((ε - 1) / ε) ≤ (ε - 1) / ε * (laborIndex μ ε n ^ (-1 / ε) / cesIndex μ ε W) *
        (W j * n j) + 1 / ε * laborIndex μ ε n ^ ((ε - 1) / ε) *
          (W j / cesIndex μ ε W) ^ (1 - ε)) ∧
      ∫ j, ((ε - 1) / ε * (laborIndex μ ε n ^ (-1 / ε) / cesIndex μ ε W) *
        (W j * n j) + 1 / ε * laborIndex μ ε n ^ ((ε - 1) / ε) *
          (W j / cesIndex μ ε W) ^ (1 - ε)) ∂μ
        = (ε - 1) / ε * (laborIndex μ ε n ^ (-1 / ε) / cesIndex μ ε W) *
          (∫ j, W j * n j ∂μ) + 1 / ε * laborIndex μ ε n ^ ((ε - 1) / ε) := by
  have hI := cesIndex_pos hpos
  have hint1 := hWn.const_mul ((ε - 1) / ε * (laborIndex μ ε n ^ (-1 / ε) / cesIndex μ ε W))
  have hint2 := (integrable_relWage_rpow hWi hW hpos).const_mul
    (1 / ε * laborIndex μ ε n ^ ((ε - 1) / ε))
  refine ⟨hint1.add hint2, fun j => ?_, ?_⟩
  · have h := young_le hε (div_pos (hW j) hI) (hn j) hN
    have e : (ε - 1) / ε * (laborIndex μ ε n ^ (-1 / ε) / cesIndex μ ε W) * (W j * n j)
        = (ε - 1) / ε * (W j / cesIndex μ ε W * n j * laborIndex μ ε n ^ (-1 / ε)) := by ring
    rw [e]
    linarith
  · rw [integral_add hint1 hint2, integral_const_mul, integral_const_mul,
      integral_relWage_rpow hε hW hpos, mul_one]

/-- Galí (2015), §6.1.1, p. 164 (**cost minimisation**): any bundle
`N(·) ≥ 0` costs at least `W · N`, where `N` is its CES aggregate. -/
theorem wageBill_ge (hε : 1 < ε) (hW : ∀ j, 0 < W j)
    (hWi : Integrable (fun j => W j ^ (1 - ε)) μ) (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ)
    {n : J → ℝ} (hn : ∀ j, 0 ≤ n j) (hWn : Integrable (fun j => W j * n j) μ) :
    cesIndex μ ε W * laborIndex μ ε n ≤ ∫ j, W j * n j ∂μ := by
  have hI := cesIndex_pos hpos
  have hε0 : (0 : ℝ) < ε := by linarith
  have hS : 0 ≤ ∫ j, W j * n j ∂μ := integral_nonneg fun j => mul_nonneg (hW j).le (hn j)
  rcases (laborIndex_nonneg (μ := μ) (ε := ε) hn).eq_or_lt with h0 | hN
  · rw [← h0, mul_zero]; exact hS
  obtain ⟨hint, hle, hval⟩ := integrated_young hε hW hWi hpos hn hWn hN
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun j => Real.rpow_nonneg (hn j) ((ε - 1) / ε)) hint
    (Filter.Eventually.of_forall hle)
  rw [hval, ← laborIndex_rpow hε hn] at hmono
  set N := laborIndex μ ε n
  set S := ∫ j, W j * n j ∂μ
  have hK : 0 < N ^ (-1 / ε) := Real.rpow_pos_of_pos hN _
  have hCr : N ^ ((ε - 1) / ε) = N * N ^ (-1 / ε) := by
    have : (ε - 1) / ε = 1 + -1 / ε := by field_simp; ring
    rw [this, Real.rpow_add hN, Real.rpow_one]
  rw [hCr] at hmono
  have hr : 0 < (ε - 1) / ε := div_pos (by linarith) hε0
  have h1 : (ε - 1) / ε * (N * N ^ (-1 / ε)) ≤
      (ε - 1) / ε * (N ^ (-1 / ε) * (S / cesIndex μ ε W)) := by
    have e : 1 / ε = 1 - (ε - 1) / ε := by field_simp; ring
    rw [e] at hmono
    have e2 : (ε - 1) / ε * (N ^ (-1 / ε) / cesIndex μ ε W) * S
        = (ε - 1) / ε * (N ^ (-1 / ε) * (S / cesIndex μ ε W)) := by ring
    rw [e2] at hmono
    linarith
  have h2 := le_of_mul_le_mul_left h1 hr
  rw [mul_comm N] at h2
  have h3 := le_of_mul_le_mul_left h2 hK
  rw [le_div_iff₀ hI] at h3
  linarith

/-- Galí (2015), eq. (3), p. 164: a bundle costs exactly `W · N` (its
aggregate `N`) **if and only if** it is the labour-demand schedule `N(j) = (W(j)/W)^{−ε} N`
almost everywhere. -/
theorem wageBill_eq_iff (hε : 1 < ε) (hW : ∀ j, 0 < W j)
    (hWi : Integrable (fun j => W j ^ (1 - ε)) μ) (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ)
    {n : J → ℝ} (hn : ∀ j, 0 ≤ n j) (hWn : Integrable (fun j => W j * n j) μ) :
    ∫ j, W j * n j ∂μ = cesIndex μ ε W * laborIndex μ ε n ↔
      n =ᵐ[μ] laborDemand μ ε W (laborIndex μ ε n) := by
  have hI := cesIndex_pos hpos
  have hε0 : (0 : ℝ) < ε := by linarith
  constructor
  swap
  · intro h
    rw [← wageBill_demand hε hW hpos (laborIndex μ ε n)]
    refine integral_congr_ae ?_
    filter_upwards [h] with j hi
    rw [hi]
  intro heq
  rcases (laborIndex_nonneg (μ := μ) (ε := ε) hn).eq_or_lt with h0 | hN
  · rw [← h0, mul_zero] at heq
    have hz := (integral_eq_zero_iff_of_nonneg
      (fun j => mul_nonneg (hW j).le (hn j)) hWn).1 heq
    filter_upwards [hz] with j hi
    rw [← h0, laborDemand, mul_zero]
    simp only [Pi.zero_apply] at hi
    rcases mul_eq_zero.1 hi with h | h
    · exact absurd h (hW j).ne'
    · exact h
  obtain ⟨hint, hle, hval⟩ := integrated_young hε hW hWi hpos hn hWn hN
  set N := laborIndex μ ε n
  have hcr : Integrable (fun j => n j ^ ((ε - 1) / ε)) μ := by
    refine Integrable.of_integral_ne_zero ?_
    rw [← laborIndex_rpow hε hn]
    exact (Real.rpow_pos_of_pos hN _).ne'
  have hdiff := (integral_eq_zero_iff_of_nonneg
    (fun j => sub_nonneg.2 (hle j)) (hint.sub hcr)).1 (by
      rw [integral_sub hint hcr, hval, ← laborIndex_rpow hε hn, heq]
      have hCr : N ^ ((ε - 1) / ε) = N * N ^ (-1 / ε) := by
        have : (ε - 1) / ε = 1 + -1 / ε := by field_simp; ring
        rw [this, Real.rpow_add hN, Real.rpow_one]
      rw [hCr]
      field_simp
      ring)
  filter_upwards [hdiff] with j hi
  simp only [Pi.zero_apply, sub_eq_zero] at hi
  have := (young_eq_iff hε (div_pos (hW j) hI) (hn j) hN).1 (by
    rw [← hi]
    ring)
  rw [this, laborDemand]

/-- Galí (2015), §6.1.1, p. 164 (dual form): for a bundle with wage bill
`∫ W(j) N(j) = X`, the attainable labour index is at most `X / W`. -/
theorem laborIndex_le_of_wageBill (hε : 1 < ε) (hW : ∀ j, 0 < W j)
    (hWi : Integrable (fun j => W j ^ (1 - ε)) μ) (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ)
    {n : J → ℝ} (hn : ∀ j, 0 ≤ n j) (hWn : Integrable (fun j => W j * n j) μ) {X : ℝ}
    (hX : ∫ j, W j * n j ∂μ = X) : laborIndex μ ε n ≤ X / cesIndex μ ε W := by
  rw [le_div_iff₀ (cesIndex_pos hpos), mul_comm, ← hX]
  exact wageBill_ge hε hW hWi hpos hn hWn

/-- Galí (2015), §6.1.1, p. 164 (dual form, equality): with wage bill `X`, the index
attains `X / W` iff `N(j) = (W(j)/W)^{−ε} X/W` almost everywhere. -/
theorem laborIndex_eq_iff_of_wageBill (hε : 1 < ε) (hW : ∀ j, 0 < W j)
    (hWi : Integrable (fun j => W j ^ (1 - ε)) μ) (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ)
    {n : J → ℝ} (hn : ∀ j, 0 ≤ n j) (hWn : Integrable (fun j => W j * n j) μ) {X : ℝ}
    (hX : ∫ j, W j * n j ∂μ = X) :
    laborIndex μ ε n = X / cesIndex μ ε W ↔
      n =ᵐ[μ] laborDemand μ ε W (X / cesIndex μ ε W) := by
  have hI := cesIndex_pos hpos
  constructor
  · intro h
    rw [← h]
    refine (wageBill_eq_iff hε hW hWi hpos hn hWn).1 ?_
    rw [h, hX]
    field_simp
  · intro h
    have hX0 : 0 ≤ X / cesIndex μ ε W := by
      rw [← hX]
      exact div_nonneg (integral_nonneg fun j => mul_nonneg (hW j).le (hn j)) hI.le
    have hagg : laborIndex μ ε n = laborIndex μ ε (laborDemand μ ε W (X / cesIndex μ ε W)) := by
      unfold laborIndex
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [h] with j hi
      rw [hi]
    rw [hagg, laborIndex_demand hε hW hpos hX0]

/-- Galí (2015), §6.1.1, pp. 164–165: a positive integrable function has positive integral against a
nonzero measure (used to see that `∫ W(j)^{1−ε} > 0`). -/
theorem integral_pos_of_pos {f : J → ℝ} (hμ : μ ≠ 0) (hf : ∀ j, 0 < f j)
    (hfi : Integrable f μ) : 0 < ∫ j, f j ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun j => (hf j).le) hfi]
  have : Function.support f = Set.univ :=
    Set.eq_univ_of_forall fun j => (hf j).ne'
  rw [this]
  exact Measure.measure_univ_pos.2 hμ

/-- Galí (2015), §6.1.1, pp. 164–165: Lebesgue measure on `[0, 1]` is nonzero. -/
theorem unitInterval_ne_zero : (volume.restrict (Set.Icc (0 : ℝ) 1)) ≠ 0 := by
  rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc]
  simp

/-- Galí (2015), §6.1.1, pp. 164–165, on the book's **continuum of labour types
`[0, 1]` with Lebesgue measure**: (i) every bundle `N(·) ≥ 0` costs at least `W · N`;
(ii) it costs exactly `W · N` iff `N(j) = (W(j)/W)^{−ε} N` for a.e. `j ∈ [0, 1]`;
(iii) the labour-demand schedule attains any aggregate `N ≥ 0`; (iv) it costs `W N`. -/
theorem unitInterval_cost_minimisation (hε : 1 < ε) {Q : ℝ → ℝ} (hQ : ∀ j, 0 < Q j)
    (hQi : IntegrableOn (fun j => Q j ^ (1 - ε)) (Set.Icc 0 1)) {n : ℝ → ℝ}
    (hn : ∀ j, 0 ≤ n j) (hQc : IntegrableOn (fun j => Q j * n j) (Set.Icc 0 1)) :
    cesIndex (volume.restrict (Set.Icc 0 1)) ε Q * laborIndex (volume.restrict (Set.Icc 0 1)) ε n
        ≤ ∫ j in Set.Icc 0 1, Q j * n j ∧
      (∫ j in Set.Icc 0 1, Q j * n j
          = cesIndex (volume.restrict (Set.Icc 0 1)) ε Q *
            laborIndex (volume.restrict (Set.Icc 0 1)) ε n ↔
        ∀ᵐ j ∂(volume.restrict (Set.Icc 0 1)),
          n j = laborDemand (volume.restrict (Set.Icc 0 1)) ε Q
            (laborIndex (volume.restrict (Set.Icc 0 1)) ε n) j) ∧
      (∀ N : ℝ, 0 ≤ N → laborIndex (volume.restrict (Set.Icc 0 1)) ε
        (laborDemand (volume.restrict (Set.Icc 0 1)) ε Q N) = N) ∧
      ∀ N : ℝ, ∫ j in Set.Icc 0 1, Q j * laborDemand (volume.restrict (Set.Icc 0 1)) ε Q N j
        = cesIndex (volume.restrict (Set.Icc 0 1)) ε Q * N := by
  have hpos := integral_pos_of_pos unitInterval_ne_zero (fun j => Real.rpow_pos_of_pos (hQ j) _)
    hQi
  exact ⟨wageBill_ge hε hQ hQi hpos hn hQc, wageBill_eq_iff hε hQ hQi hpos hn hQc,
    fun N hN => laborIndex_demand hε hQ hpos hN, wageBill_demand hε hQ hpos⟩

namespace Finite

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Galí (2015), §6.1.1, pp. 164–165 (finitely many types): the measure with weight `w j` on
type `j`, a discretisation of `[0, 1]` (e.g. `w j = 1/n`). -/
noncomputable def weightMeasure (w : ι → ℝ) : Measure ι :=
  ∑ j, ENNReal.ofReal (w j) • Measure.dirac j

/-- Galí (2015), §6.1.1, pp. 164–165: the weighted measure gives type `x` mass `w x`. -/
theorem weightMeasure_singleton {w : ι → ℝ} (x : ι) :
    weightMeasure w {x} = ENNReal.ofReal (w x) := by
  rw [weightMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single x]
  · simp
  · intro b _ hb
    simp [Measure.dirac_apply' _ (measurableSet_singleton x), hb]
  · simp

omit [MeasurableSingletonClass ι] in
/-- Galí (2015), §6.1.1, pp. 164–165: the weighted measure is finite. -/
theorem weightMeasure_univ_lt_top {w : ι → ℝ} : weightMeasure w Set.univ < ⊤ := by
  rw [weightMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact ENNReal.sum_lt_top.2 fun j _ => ENNReal.ofReal_lt_top

/-- Galí (2015), §6.1.1, pp. 164–165: every function is integrable for the weighted measure. -/
theorem integrable_weightMeasure {w : ι → ℝ} (f : ι → ℝ) : Integrable f (weightMeasure w) := by
  have : IsFiniteMeasure (weightMeasure w) := ⟨weightMeasure_univ_lt_top⟩
  exact Integrable.of_finite

/-- Galí (2015), §6.1.1, pp. 164–165: integrals against the weighted measure are weighted sums,
`∫ f = ∑ᵢ w j f j`. -/
theorem integral_weightMeasure {w : ι → ℝ} (hw : ∀ j, 0 ≤ w j) (f : ι → ℝ) :
    ∫ j, f j ∂(weightMeasure w) = ∑ j, w j * f j := by
  rw [integral_fintype (integrable_weightMeasure f)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Measure.real, weightMeasure_singleton, ENNReal.toReal_ofReal (hw j), smul_eq_mul]

/-- Galí (2015), §6.1.1, pp. 164–165, for **finitely many labour types** with weights
`w j > 0`. With `W = (∑ w W(j)^{1−ε})^{1/(1−ε)}` and `N = (∑ w N(j)^r)^{1/r}`:
(i) `∑ w W(j) N(j) ≥ W N`; (ii) equality iff `N(j) = (W(j)/W)^{−ε} N` for **every** `j`;
(iii) the labour-demand schedule attains any `N ≥ 0`; (iv) it costs exactly `W N`. -/
theorem finite_cost_minimisation [Nonempty ι] (hε : 1 < ε) {w : ι → ℝ}
    (hw : ∀ j, 0 < w j) {Q : ι → ℝ} (hQ : ∀ j, 0 < Q j) {n : ι → ℝ} (hn : ∀ j, 0 ≤ n j) :
    (∑ j, w j * Q j ^ (1 - ε)) ^ (1 - ε)⁻¹ * (∑ j, w j * n j ^ ((ε - 1) / ε)) ^ ((ε - 1) / ε)⁻¹
        ≤ ∑ j, w j * (Q j * n j) ∧
      (∑ j, w j * (Q j * n j) = (∑ j, w j * Q j ^ (1 - ε)) ^ (1 - ε)⁻¹ *
          (∑ j, w j * n j ^ ((ε - 1) / ε)) ^ ((ε - 1) / ε)⁻¹ ↔
        ∀ j, n j = (Q j / (∑ i, w i * Q i ^ (1 - ε)) ^ (1 - ε)⁻¹) ^ (-ε) *
          (∑ i, w i * n i ^ ((ε - 1) / ε)) ^ ((ε - 1) / ε)⁻¹) ∧
      (∀ N : ℝ, 0 ≤ N → (∑ j, w j *
        ((Q j / (∑ i, w i * Q i ^ (1 - ε)) ^ (1 - ε)⁻¹) ^ (-ε) * N) ^ ((ε - 1) / ε)) ^
          ((ε - 1) / ε)⁻¹ = N) ∧
      ∀ N : ℝ, ∑ j, w j * (Q j * ((Q j / (∑ i, w i * Q i ^ (1 - ε)) ^ (1 - ε)⁻¹) ^ (-ε) * N))
        = (∑ i, w i * Q i ^ (1 - ε)) ^ (1 - ε)⁻¹ * N := by
  have hw0 : ∀ j, 0 ≤ w j := fun j => (hw j).le
  have hμ : weightMeasure w ≠ 0 := by
    intro h
    obtain ⟨x⟩ := ‹Nonempty ι›
    have := weightMeasure_singleton (w := w) x
    rw [h, Measure.coe_zero, Pi.zero_apply] at this
    exact (ENNReal.ofReal_pos.2 (hw x)).ne' this.symm
  have hpos := integral_pos_of_pos hμ (fun j => Real.rpow_pos_of_pos (hQ j) (1 - ε))
    (integrable_weightMeasure _)
  have hPI : cesIndex (weightMeasure w) ε Q = (∑ i, w i * Q i ^ (1 - ε)) ^ (1 - ε)⁻¹ := by
    rw [cesIndex, integral_weightMeasure hw0]
  have hCA : ∀ d : ι → ℝ, laborIndex (weightMeasure w) ε d
      = (∑ i, w i * d i ^ ((ε - 1) / ε)) ^ ((ε - 1) / ε)⁻¹ := by
    intro d
    rw [laborIndex, integral_weightMeasure hw0]
  have hD : ∀ N j, laborDemand (weightMeasure w) ε Q N j
      = (Q j / (∑ i, w i * Q i ^ (1 - ε)) ^ (1 - ε)⁻¹) ^ (-ε) * N := by
    intro N j
    rw [laborDemand, hPI]
  have h1 := wageBill_ge hε hQ (integrable_weightMeasure _) hpos hn (integrable_weightMeasure _)
  have h2 := wageBill_eq_iff hε hQ (integrable_weightMeasure _) hpos hn (integrable_weightMeasure _)
  rw [hPI, hCA, integral_weightMeasure hw0] at h1 h2
  rw [Filter.EventuallyEq, ae_iff_of_countable] at h2
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [h2]
    constructor
    · intro h j
      rw [← hD]
      exact h j (by rw [weightMeasure_singleton]; exact (ENNReal.ofReal_pos.2 (hw j)).ne')
    · intro h j _
      rw [hD]
      exact h j
  · intro N hN
    have := laborIndex_demand hε hQ hpos hN (μ := weightMeasure w)
    rw [hCA] at this
    simpa only [hD] using this
  · intro N
    have := wageBill_demand hε hQ hpos N (μ := weightMeasure w)
    rw [integral_weightMeasure hw0, hPI] at this
    simpa only [hD] using this

end Finite


/-! ### Labour demand (3) is the unique cost minimiser -/

/-- Galí (2015), eq. (3), p. 164: the labour-demand schedule is a feasible bundle: it is
nonnegative and its wage bill is integrable. -/
theorem laborDemand_feasible (hW : ∀ j, 0 < W j) (hWi : Integrable (fun j => W j ^ (1 - ε)) μ)
    (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ) {N : ℝ} (hN : 0 ≤ N) :
    (∀ j, 0 ≤ laborDemand μ ε W N j) ∧
      Integrable (fun j => W j * laborDemand μ ε W N j) μ := by
  have hI := cesIndex_pos hpos
  refine ⟨fun j => mul_nonneg (Real.rpow_nonneg (div_pos (hW j) hI).le _) hN, ?_⟩
  simp_rw [wage_mul_demand hW hpos N]
  exact (integrable_relWage_rpow hWi hW hpos).const_mul _

/-- Galí (2015), eq. (3), p. 164 (**labour demand is the unique cost minimiser**): a firm that
needs the labour index `N ≥ 0` and uses a bundle `n(·) ≥ 0` with `N(n) = N` minimises its wage
bill `∫ W(j) n(j) dj` over all such bundles **if and only if** `n(j) = (W(j)/W)^{−ε_w} N` for
almost every `j`. -/
theorem cost_min_iff (hε : 1 < ε) (hW : ∀ j, 0 < W j)
    (hWi : Integrable (fun j => W j ^ (1 - ε)) μ) (hpos : 0 < ∫ j, W j ^ (1 - ε) ∂μ)
    {N : ℝ} (hN : 0 ≤ N) {n : J → ℝ} (hn : ∀ j, 0 ≤ n j)
    (hWn : Integrable (fun j => W j * n j) μ) (hnN : laborIndex μ ε n = N) :
    (∀ m : J → ℝ, (∀ j, 0 ≤ m j) → Integrable (fun j => W j * m j) μ →
        laborIndex μ ε m = N → ∫ j, W j * n j ∂μ ≤ ∫ j, W j * m j ∂μ) ↔
      n =ᵐ[μ] laborDemand μ ε W N := by
  obtain ⟨hd0, hdi⟩ := laborDemand_feasible hW hWi hpos hN
  constructor
  · intro hmin
    have h1 := hmin _ hd0 hdi (laborIndex_demand hε hW hpos hN)
    rw [wageBill_demand hε hW hpos N] at h1
    have h2 := wageBill_ge hε hW hWi hpos hn hWn
    rw [hnN] at h2
    have heq : ∫ j, W j * n j ∂μ = cesIndex μ ε W * laborIndex μ ε n := by
      rw [hnN]
      linarith
    have := (wageBill_eq_iff hε hW hWi hpos hn hWn).1 heq
    rwa [hnN] at this
  · intro hae m hm hWm hmN
    have hc : ∫ j, W j * n j ∂μ = cesIndex μ ε W * N := by
      rw [← wageBill_demand hε hW hpos N]
      refine integral_congr_ae ?_
      filter_upwards [hae] with j hj
      rw [hj]
    rw [hc, ← hmN]
    exact wageBill_ge hε hW hWi hpos hm hWm

/-! ### Dispersion terms and the employment–output relation (pp. 170–171) -/

/-- Galí (2015), p. 171: the dispersion integral `∫ (X(j)/X)^e dj` of a cross-section `X(·)`
with CES index `X = cesIndex μ ε X`. Wage dispersion is `Δ_w = ∫ (W(j)/W)^{−ε_w} dj`
(`e = −ε_w`); price dispersion is `Δ_p = ∫ (P(i)/P)^{−ε_p/(1−α)} di` (`e = −ε_p/(1−α)`). -/
noncomputable def dispIntegral (μ : Measure J) (ε e : ℝ) (X : J → ℝ) : ℝ :=
  ∫ j, (X j / cesIndex μ ε X) ^ e ∂μ

/-- Galí (2015), p. 171: wage dispersion `Δ_w = ∫ (W(j)/W)^{−ε_w} dj`. -/
noncomputable def wageDisp (μ : Measure J) (εw : ℝ) (W : J → ℝ) : ℝ := dispIntegral μ εw (-εw) W

/-- Galí (2015), p. 171: price dispersion `Δ_p = ∫ (P(i)/P)^{−ε_p/(1−α)} di`. -/
noncomputable def priceDisp (μ : Measure J) (α εp : ℝ) (P : J → ℝ) : ℝ :=
  dispIntegral μ εp (-εp / (1 - α)) P

/-- Galí (2015), p. 171: `d_w = (1 − α) log ∫ (W(j)/W)^{−ε_w} dj`. -/
noncomputable def dW (μ : Measure J) (α εw : ℝ) (W : J → ℝ) : ℝ :=
  (1 - α) * Real.log (wageDisp μ εw W)

/-- Galí (2015), p. 171: `d_p = (1 − α) log ∫ (P(i)/P)^{−ε_p/(1−α)} di`. -/
noncomputable def dP (μ : Measure J) (α εp : ℝ) (P : J → ℝ) : ℝ :=
  (1 - α) * Real.log (priceDisp μ α εp P)

/-- Galí (2015), p. 170: with every firm on its labour-demand schedule (3),
`N(i,j) = (W(j)/W)^{−ε_w} N(i)`, firm `i` employs `∫ N(i,j) dj = Δ_w N(i)` hours. -/
theorem firm_hours {F : Type*} {N : F → J → ℝ} {Nf : F → ℝ}
    (hdem : ∀ i j, N i j = laborDemand μ ε W (Nf i) j) (i : F) :
    ∫ j, N i j ∂μ = wageDisp μ ε W * Nf i := by
  simp_rw [hdem i, laborDemand]
  rw [integral_mul_const, wageDisp, dispIntegral]

/-- Galí (2015), pp. 170–171: with production `Y(i) = A N(i)^{1−α}` (1) and output on the
goods-demand schedule `Y(i) = (P(i)/P)^{−ε_p} Y`, `∫ N(i) di = Δ_p (Y/A)^{1/(1−α)}`
(restated from the Chapter 3 project, `employment_level`). -/
theorem firm_index_level {F : Type*} [MeasurableSpace F] {μF : Measure F} {α εp : ℝ}
    (hα1 : α < 1) {P : F → ℝ} (hP : ∀ i, 0 < P i) (hpos : 0 < ∫ i, P i ^ (1 - εp) ∂μF)
    {A Y : ℝ} (hA : 0 < A) (hY : 0 ≤ Y) {Nf : F → ℝ} (hN : ∀ i, 0 ≤ Nf i)
    (hprod : ∀ i, laborDemand μF εp P Y i = A * Nf i ^ (1 - α)) :
    ∫ i, Nf i ∂μF = (Y / A) ^ (1 - α)⁻¹ * priceDisp μF α εp P := by
  have hI := cesIndex_pos hpos
  have hsub : (1 : ℝ) - α ≠ 0 := by linarith
  have hpt : ∀ i, Nf i = (Y / A) ^ (1 - α)⁻¹ * (P i / cesIndex μF εp P) ^ (-εp / (1 - α)) := by
    intro i
    have ha : 0 < P i / cesIndex μF εp P := div_pos (hP i) hI
    have h1 : Nf i ^ (1 - α) = (P i / cesIndex μF εp P) ^ (-εp) * (Y / A) := by
      have := hprod i
      rw [laborDemand] at this
      field_simp
      linarith
    rw [← Real.rpow_rpow_inv (hN i) hsub, h1, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul ha.le, div_eq_mul_inv (-εp), mul_comm]
  simp_rw [hpt]
  rw [integral_const_mul, priceDisp, dispIntegral]

/-- Galí (2015), pp. 170–171 (**exact aggregate employment**): with labour demand (3) for every
firm, production (1) and goods demand, aggregate employment
`N = ∫∫ N(i,j) dj di = Δ_w Δ_p (Y/A)^{1/(1−α)}`. -/
theorem aggregate_employment {F : Type*} [MeasurableSpace F] {μF : Measure F} {α εp : ℝ}
    (hα1 : α < 1) {P : F → ℝ} (hP : ∀ i, 0 < P i) (hpos : 0 < ∫ i, P i ^ (1 - εp) ∂μF)
    {A Y : ℝ} (hA : 0 < A) (hY : 0 ≤ Y) {Nf : F → ℝ} (hN : ∀ i, 0 ≤ Nf i)
    (hprod : ∀ i, laborDemand μF εp P Y i = A * Nf i ^ (1 - α)) {N : F → J → ℝ}
    (hdem : ∀ i j, N i j = laborDemand μ ε W (Nf i) j) :
    ∫ i, ∫ j, N i j ∂μ ∂μF = wageDisp μ ε W * priceDisp μF α εp P * (Y / A) ^ (1 - α)⁻¹ := by
  simp_rw [firm_hours hdem]
  rw [integral_const_mul, firm_index_level hα1 hP hpos hA hY hN hprod]
  ring

/-- Galí (2015), p. 171 and App. 6.1, p. 190 (**exact employment–output relation**):
`(1 − α) n = y − a + d_w + d_p`, with `n = log ∫∫ N(i,j) dj di`, `y = log Y`, `a = log A`. -/
theorem employment_identity {F : Type*} [MeasurableSpace F] {μF : Measure F} {α εp : ℝ}
    (hα1 : α < 1) {P : F → ℝ} (hP : ∀ i, 0 < P i) (hpos : 0 < ∫ i, P i ^ (1 - εp) ∂μF)
    {A Y : ℝ} (hA : 0 < A) (hY : 0 < Y) {Nf : F → ℝ} (hN : ∀ i, 0 ≤ Nf i)
    (hprod : ∀ i, laborDemand μF εp P Y i = A * Nf i ^ (1 - α)) {N : F → J → ℝ}
    (hdem : ∀ i j, N i j = laborDemand μ ε W (Nf i) j) (hDw : 0 < wageDisp μ ε W)
    (hDp : 0 < priceDisp μF α εp P) :
    (1 - α) * Real.log (∫ i, ∫ j, N i j ∂μ ∂μF)
      = Real.log Y - Real.log A + dW μ α ε W + dP μF α εp P := by
  have hsub : (1 : ℝ) - α ≠ 0 := by linarith
  rw [aggregate_employment hα1 hP hpos hA hY.le hN hprod hdem,
    Real.log_mul (by positivity) (by positivity), Real.log_mul hDw.ne' hDp.ne',
    Real.log_rpow (by positivity), Real.log_div hY.ne' hA.ne', dW, dP]
  field_simp
  ring

/-- Galí (2015), p. 171 (via ch. 3, App. 3.4): the pointwise Bernoulli bound behind
`Δ ≥ 1`. For `ε > 1` and an exponent `e < 1 − ε`, with `q = e/(1 − ε) > 1`,
`x^e ≥ 1 + q (x^{1−ε} − 1)` for `x > 0`, with equality only at `x = 1`. -/
theorem bernoulli_disp {e : ℝ} (hε : 1 < ε) (he : e < 1 - ε) {x : ℝ} (hx : 0 < x) :
    1 + e / (1 - ε) * (x ^ (1 - ε) - 1) ≤ x ^ e ∧
      (1 + e / (1 - ε) * (x ^ (1 - ε) - 1) = x ^ e → x = 1) := by
  have hsub : (1 : ℝ) - ε < 0 := by linarith
  have hq : 1 < e / (1 - ε) := by rw [one_lt_div_of_neg hsub]; exact he
  have hy : 0 < x ^ (1 - ε) := Real.rpow_pos_of_pos hx _
  have hs : -1 ≤ x ^ (1 - ε) - 1 := by linarith
  have hrw : x ^ e = (x ^ (1 - ε)) ^ (e / (1 - ε)) := by
    rw [← Real.rpow_mul hx.le]
    congr 1
    have h1 : (1 : ℝ) - ε ≠ 0 := hsub.ne
    field_simp
  rw [hrw]
  refine ⟨by simpa using one_add_mul_self_le_rpow_one_add hs hq.le, fun heq => ?_⟩
  by_contra hne
  have hy1 : x ^ (1 - ε) - 1 ≠ 0 := by
    intro h0
    have h1 : x ^ (1 - ε) = 1 := by linarith
    apply hne
    rw [← Real.rpow_rpow_inv hx.le hsub.ne, h1, Real.one_rpow]
  have := one_add_mul_self_lt_rpow_one_add hs hy1 hq
  simp only [add_sub_cancel] at this
  linarith

/-- Galí (2015), p. 171: the Bernoulli lower bound integrates to one by the index condition
`∫ (X(j)/X)^{1−ε} = 1`. -/
theorem integral_bernoulli_lower [IsProbabilityMeasure μ] (hε : 1 < ε) {X : J → ℝ}
    (hX : ∀ j, 0 < X j) (hXi : Integrable (fun j => X j ^ (1 - ε)) μ) (q : ℝ) :
    Integrable (fun j => 1 + q * ((X j / cesIndex μ ε X) ^ (1 - ε) - 1)) μ ∧
      ∫ j, (1 + q * ((X j / cesIndex μ ε X) ^ (1 - ε) - 1)) ∂μ = 1 := by
  have hpos := integral_pos_of_pos (IsProbabilityMeasure.ne_zero μ)
    (fun j => Real.rpow_pos_of_pos (hX j) (1 - ε)) hXi
  have hy := integrable_relWage_rpow hXi hX hpos
  have he : (fun j => 1 + q * ((X j / cesIndex μ ε X) ^ (1 - ε) - 1))
      = fun j => (1 - q) + q * (X j / cesIndex μ ε X) ^ (1 - ε) := by
    funext j
    ring
  rw [he]
  refine ⟨(integrable_const _).add (hy.const_mul q), ?_⟩
  rw [integral_add (integrable_const _) (hy.const_mul q), integral_const, integral_const_mul,
    integral_relWage_rpow hε hX hpos]
  simp

/-- Galí (2015), p. 171 (Jensen): for `e < 1 − ε` the dispersion integral is at least one,
`∫ (X(j)/X)^e ≥ 1`. -/
theorem one_le_dispIntegral [IsProbabilityMeasure μ] {e : ℝ} (hε : 1 < ε) (he : e < 1 - ε)
    {X : J → ℝ} (hX : ∀ j, 0 < X j) (hXi : Integrable (fun j => X j ^ (1 - ε)) μ)
    (hD : Integrable (fun j => (X j / cesIndex μ ε X) ^ e) μ) : 1 ≤ dispIntegral μ ε e X := by
  have hpos := integral_pos_of_pos (IsProbabilityMeasure.ne_zero μ)
    (fun j => Real.rpow_pos_of_pos (hX j) (1 - ε)) hXi
  have hI := cesIndex_pos hpos
  obtain ⟨hlow, hval⟩ := integral_bernoulli_lower hε hX hXi (e / (1 - ε))
  have h := integral_mono hlow hD fun j => (bernoulli_disp hε he (div_pos (hX j) hI)).1
  rwa [hval] at h

/-- Galí (2015), p. 171: `log Δ ≥ 0` for `e < 1 − ε`. -/
theorem log_dispIntegral_nonneg [IsProbabilityMeasure μ] {e : ℝ} (hε : 1 < ε)
    (he : e < 1 - ε) {X : J → ℝ} (hX : ∀ j, 0 < X j)
    (hXi : Integrable (fun j => X j ^ (1 - ε)) μ)
    (hD : Integrable (fun j => (X j / cesIndex μ ε X) ^ e) μ) :
    0 ≤ Real.log (dispIntegral μ ε e X) :=
  Real.log_nonneg (one_le_dispIntegral hε he hX hXi hD)

/-- Galí (2015), p. 171: `log Δ = 0` **iff** there is no dispersion, `X(j) = X` a.e. -/
theorem log_dispIntegral_eq_zero_iff [IsProbabilityMeasure μ] {e : ℝ} (hε : 1 < ε)
    (he : e < 1 - ε) {X : J → ℝ} (hX : ∀ j, 0 < X j)
    (hXi : Integrable (fun j => X j ^ (1 - ε)) μ)
    (hD : Integrable (fun j => (X j / cesIndex μ ε X) ^ e) μ) :
    Real.log (dispIntegral μ ε e X) = 0 ↔ ∀ᵐ j ∂μ, X j = cesIndex μ ε X := by
  have hpos := integral_pos_of_pos (IsProbabilityMeasure.ne_zero μ)
    (fun j => Real.rpow_pos_of_pos (hX j) (1 - ε)) hXi
  have hI := cesIndex_pos hpos
  constructor
  · intro hlog
    have h1 := one_le_dispIntegral hε he hX hXi hD
    have hint1 : ∫ j, (X j / cesIndex μ ε X) ^ e ∂μ = 1 := by
      rcases Real.log_eq_zero.1 hlog with h | h | h
      · rw [dispIntegral] at h h1; linarith
      · exact h
      · rw [dispIntegral] at h h1; linarith
    obtain ⟨hlow, hval⟩ := integral_bernoulli_lower hε hX hXi (e / (1 - ε))
    have hz := (integral_eq_zero_iff_of_nonneg (fun j => sub_nonneg.2
      (bernoulli_disp hε he (div_pos (hX j) hI)).1) (hD.sub hlow)).1 (by
        rw [integral_sub hD hlow, hint1, hval, sub_self])
    filter_upwards [hz] with j hj
    simp only [Pi.zero_apply, sub_eq_zero] at hj
    have := (bernoulli_disp hε he (div_pos (hX j) hI)).2 hj.symm
    rwa [div_eq_one_iff_eq hI.ne'] at this
  · intro h
    have hint1 : ∫ j, (X j / cesIndex μ ε X) ^ e ∂μ = 1 := by
      rw [integral_congr_ae (g := fun _ => (1 : ℝ)) (by
        filter_upwards [h] with j hj
        rw [hj, div_self hI.ne', Real.one_rpow])]
      simp
    rw [dispIntegral, hint1, Real.log_one]

/-- Galí (2015), p. 171: the index of a cross-section that is a.e. equal to a constant `c` is
`c`, so "`X(j) = X` a.e." is the same as "all `X(j)` are a.e. equal". -/
theorem ae_eq_index_iff_const [IsProbabilityMeasure μ] {X : J → ℝ} (hε : ε ≠ 1)
    (hX : ∀ j, 0 < X j) :
    (∀ᵐ j ∂μ, X j = cesIndex μ ε X) ↔ ∃ c, ∀ᵐ j ∂μ, X j = c := by
  refine ⟨fun h => ⟨_, h⟩, fun ⟨c, hc⟩ => ?_⟩
  obtain ⟨j₀, hj₀⟩ := hc.exists
  have hc0 : 0 < c := hj₀ ▸ hX j₀
  have hidx : cesIndex μ ε X = c := by
    unfold cesIndex
    rw [integral_congr_ae (g := fun _ => c ^ (1 - ε)) (by
      filter_upwards [hc] with j hj
      rw [hj])]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    exact Real.rpow_rpow_inv hc0.le (sub_ne_zero.2 (Ne.symm hε))
  rw [hidx]
  exact hc

/-- Galí (2015), p. 171: the wage exponent `−ε_w` satisfies `−ε_w < 1 − ε_w`. -/
theorem wage_exponent_lt (εw : ℝ) : -εw < 1 - εw := by linarith

/-- Galí (2015), p. 171: the price exponent satisfies `−ε_p/(1 − α) < 1 − ε_p` for
`ε_p > 1`, `0 ≤ α < 1`. -/
theorem price_exponent_lt {α εp : ℝ} (hε : 1 < εp) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    -εp / (1 - α) < 1 - εp := by
  have h1 : (0 : ℝ) < 1 - α := by linarith
  rw [div_lt_iff₀ h1]
  nlinarith

/-- Galí (2015), p. 171: **wage dispersion is nonnegative**, `d_w ≥ 0` (`α < 1`). -/
theorem dW_nonneg [IsProbabilityMeasure μ] {α : ℝ} (hα1 : α < 1) (hε : 1 < ε)
    (hW : ∀ j, 0 < W j) (hWi : Integrable (fun j => W j ^ (1 - ε)) μ)
    (hD : Integrable (fun j => (W j / cesIndex μ ε W) ^ (-ε)) μ) : 0 ≤ dW μ α ε W :=
  mul_nonneg (by linarith) (log_dispIntegral_nonneg hε (wage_exponent_lt ε) hW hWi hD)

/-- Galí (2015), p. 171: `d_w = 0` **iff** there is no wage dispersion, `W(j) = W` a.e. -/
theorem dW_eq_zero_iff [IsProbabilityMeasure μ] {α : ℝ} (hα1 : α < 1) (hε : 1 < ε)
    (hW : ∀ j, 0 < W j) (hWi : Integrable (fun j => W j ^ (1 - ε)) μ)
    (hD : Integrable (fun j => (W j / cesIndex μ ε W) ^ (-ε)) μ) :
    dW μ α ε W = 0 ↔ ∀ᵐ j ∂μ, W j = cesIndex μ ε W := by
  have hsub : (1 : ℝ) - α ≠ 0 := by linarith
  rw [dW, mul_eq_zero, or_iff_right hsub, wageDisp]
  exact log_dispIntegral_eq_zero_iff hε (wage_exponent_lt ε) hW hWi hD

/-- Galí (2015), p. 171: `d_w = 0` iff all wages are (a.e.) equal. -/
theorem dW_eq_zero_iff_const [IsProbabilityMeasure μ] {α : ℝ} (hα1 : α < 1) (hε : 1 < ε)
    (hW : ∀ j, 0 < W j) (hWi : Integrable (fun j => W j ^ (1 - ε)) μ)
    (hD : Integrable (fun j => (W j / cesIndex μ ε W) ^ (-ε)) μ) :
    dW μ α ε W = 0 ↔ ∃ c, ∀ᵐ j ∂μ, W j = c := by
  rw [dW_eq_zero_iff hα1 hε hW hWi hD]
  exact ae_eq_index_iff_const hε.ne' hW

/-- Galí (2015), p. 171: **price dispersion is nonnegative**, `d_p ≥ 0` (`0 ≤ α < 1`). -/
theorem dP_nonneg [IsProbabilityMeasure μ] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hε : 1 < ε) {P : J → ℝ} (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ)
    (hD : Integrable (fun i => (P i / cesIndex μ ε P) ^ (-ε / (1 - α))) μ) :
    0 ≤ dP μ α ε P :=
  mul_nonneg (by linarith) (log_dispIntegral_nonneg hε (price_exponent_lt hε hα0 hα1) hP hPi hD)

/-- Galí (2015), p. 171: `d_p = 0` **iff** there is no price dispersion, `P(i) = P` a.e. -/
theorem dP_eq_zero_iff [IsProbabilityMeasure μ] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hε : 1 < ε) {P : J → ℝ} (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ)
    (hD : Integrable (fun i => (P i / cesIndex μ ε P) ^ (-ε / (1 - α))) μ) :
    dP μ α ε P = 0 ↔ ∀ᵐ i ∂μ, P i = cesIndex μ ε P := by
  have hsub : (1 : ℝ) - α ≠ 0 := by linarith
  rw [dP, mul_eq_zero, or_iff_right hsub, priceDisp]
  exact log_dispIntegral_eq_zero_iff hε (price_exponent_lt hε hα0 hα1) hP hPi hD

/-- Galí (2015), p. 171: `d_p = 0` iff all prices are (a.e.) equal. -/
theorem dP_eq_zero_iff_const [IsProbabilityMeasure μ] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hε : 1 < ε) {P : J → ℝ} (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ)
    (hD : Integrable (fun i => (P i / cesIndex μ ε P) ^ (-ε / (1 - α))) μ) :
    dP μ α ε P = 0 ↔ ∃ c, ∀ᵐ i ∂μ, P i = c := by
  rw [dP_eq_zero_iff hα0 hα1 hε hP hPi hD]
  exact ae_eq_index_iff_const hε.ne' hP

/-! ### First order: `d_w` and `d_p` vanish with zero derivative (p. 171) -/

/-- Galí (2015), p. 171 (via ch. 3, App. 3.4): for a bounded measurable `z` on a probability
space every `exp(t z)` is integrable. -/
theorem integrable_exp_mul [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (t : ℝ) : Integrable (fun j => Real.exp (t * z j)) μ := by
  refine Integrable.of_bound ((measurable_const.mul hz).exp.aestronglyMeasurable)
    (Real.exp (|t| * B)) (Filter.Eventually.of_forall fun j => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  calc t * z j ≤ |t * z j| := le_abs_self _
    _ = |t| * |z j| := abs_mul _ _
    _ ≤ |t| * B := mul_le_mul_of_nonneg_left (hB j) (abs_nonneg t)

/-- Galí (2015), p. 171: for bounded `z` the cumulant-generating function is analytic on `ℝ`. -/
theorem interior_integrableExpSet [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ j, |z j| ≤ B) : interior (integrableExpSet z μ) = Set.univ := by
  have : integrableExpSet z μ = Set.univ :=
    Set.eq_univ_of_forall fun t => integrable_exp_mul hz hB t
  rw [this, interior_univ]

/-- Galí (2015), p. 171: along the family `X(j) = exp(x̄ + s z(j))` the CES index is
`exp(x̄ + K((1 − ε)s)/(1 − ε))`, with `K` the cumulant-generating function of `z`
(restated from the Chapter 3 project, `priceIndex_family`). -/
theorem cesIndex_family [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (xbar s : ℝ) :
    cesIndex μ ε (fun j => Real.exp (xbar + s * z j))
      = Real.exp (xbar + cgf z μ ((1 - ε) * s) / (1 - ε)) := by
  have hM : ∀ t, 0 < mgf z μ t := fun t => mgf_pos (integrable_exp_mul hz hB t)
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have hsum : ∫ j, Real.exp (xbar + s * z j) ^ (1 - ε) ∂μ
      = Real.exp ((1 - ε) * xbar) * mgf z μ ((1 - ε) * s) := by
    have : ∀ j, Real.exp (xbar + s * z j) ^ (1 - ε)
        = Real.exp ((1 - ε) * xbar) * Real.exp ((1 - ε) * s * z j) := by
      intro j
      rw [← Real.exp_mul, ← Real.exp_add]
      congr 1
      ring
    simp_rw [this]
    rw [integral_const_mul]
    rfl
  unfold cesIndex
  rw [hsum, Real.rpow_def_of_pos (mul_pos (Real.exp_pos _) (hM _)),
    Real.log_mul (Real.exp_pos _).ne' (hM _).ne', Real.log_exp, cgf]
  congr 1
  field_simp

/-- Galí (2015), p. 171: along `X(j) = exp(x̄ + s z(j))`, **exactly**
`log ∫ (X(j)/X)^e dj = K(e s) − (e/(1 − ε)) K((1 − ε) s)`. -/
theorem log_dispIntegral_family [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (e xbar s : ℝ) :
    Real.log (dispIntegral μ ε e (fun j => Real.exp (xbar + s * z j)))
      = cgf z μ (e * s) - e / (1 - ε) * cgf z μ ((1 - ε) * s) := by
  have hM : ∀ t, 0 < mgf z μ t := fun t => mgf_pos (integrable_exp_mul hz hB t)
  have hidx : cesIndex μ ε (fun j => Real.exp (xbar + s * z j))
      = Real.exp (xbar + Real.log (mgf z μ ((1 - ε) * s)) / (1 - ε)) :=
    cesIndex_family hz hB hε xbar s
  have hrel : ∀ j, (Real.exp (xbar + s * z j) /
      Real.exp (xbar + Real.log (mgf z μ ((1 - ε) * s)) / (1 - ε))) ^ e
      = Real.exp (-(e * (Real.log (mgf z μ ((1 - ε) * s)) / (1 - ε)))) *
        Real.exp (e * s * z j) := by
    intro j
    rw [← Real.exp_sub, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  rw [dispIntegral, hidx]
  simp_rw [hrel]
  rw [integral_const_mul]
  have hm2 : ∫ j, Real.exp (e * s * z j) ∂μ = mgf z μ (e * s) := rfl
  rw [hm2, Real.log_mul (Real.exp_pos _).ne' (hM _).ne', Real.log_exp, cgf, cgf]
  ring

/-- Galí (2015), p. 171: `s ↦ K(a s)` has derivative `a E z` at `0` (`K` the cumulant
generating function of a bounded `z`). -/
theorem hasDerivAt_cgf_mul [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (a : ℝ) :
    HasDerivAt (fun s => cgf z μ (a * s)) (a * ∫ j, z j ∂μ) 0 := by
  have hint := interior_integrableExpSet (μ := μ) hz hB
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet z μ) := by
    rw [hint]
    trivial
  have hd : HasDerivAt (cgf z μ) (∫ j, z j ∂μ) (a * 0) := by
    have := (analyticAt_cgf h0).differentiableAt.hasDerivAt
    rw [deriv_cgf_zero h0] at this
    rw [mul_zero]
    simpa using this
  have hl : HasDerivAt (fun s : ℝ => a * s) a 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul a
  exact (hd.comp 0 hl).congr_deriv (by ring)

/-- Galí (2015), p. 171 (**first order**): along `X(j) = exp(x̄ + s z(j))`, the log dispersion
integral is `0` at `s = 0` and has derivative `0` there. -/
theorem log_dispIntegral_family_first_order [IsProbabilityMeasure μ] {z : J → ℝ}
    (hz : Measurable z) {B : ℝ} (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (e xbar : ℝ) :
    Real.log (dispIntegral μ ε e (fun j => Real.exp (xbar + 0 * z j))) = 0 ∧
      HasDerivAt (fun s => Real.log (dispIntegral μ ε e (fun j => Real.exp (xbar + s * z j))))
        0 0 := by
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  refine ⟨by rw [log_dispIntegral_family hz hB hε]; simp [cgf_zero], ?_⟩
  have hfun : (fun s => Real.log (dispIntegral μ ε e (fun j => Real.exp (xbar + s * z j))))
      = fun s => cgf z μ (e * s) - e / (1 - ε) * cgf z μ ((1 - ε) * s) :=
    funext fun s => log_dispIntegral_family hz hB hε e xbar s
  rw [hfun]
  have h := HasDerivAt.sub (hasDerivAt_cgf_mul (μ := μ) hz hB e)
    ((hasDerivAt_cgf_mul (μ := μ) hz hB (1 - ε)).const_mul (e / (1 - ε)))
  refine h.congr_deriv ?_
  have : e / (1 - ε) * ((1 - ε) * ∫ j, z j ∂μ) = e * ∫ j, z j ∂μ := by field_simp
  rw [this, sub_self]

/-- Galí (2015), p. 171 (**`d_w` is zero to first order**): along the family of wage
distributions `w(j) = w̄ + s z(j)`, `d_w(0) = 0` and `d_w'(0) = 0`. -/
theorem dW_family_first_order [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (α wbar : ℝ) :
    dW μ α ε (fun j => Real.exp (wbar + 0 * z j)) = 0 ∧
      HasDerivAt (fun s => dW μ α ε (fun j => Real.exp (wbar + s * z j))) 0 0 := by
  obtain ⟨h0, hd⟩ := log_dispIntegral_family_first_order (μ := μ) hz hB hε (-ε) wbar
  refine ⟨by rw [dW, wageDisp, h0, mul_zero], ?_⟩
  simpa [dW, wageDisp] using hd.const_mul (1 - α)

/-- Galí (2015), p. 171 (**`d_p` is zero to first order**): along the family of price
distributions `p(i) = p̄ + s z(i)`, `d_p(0) = 0` and `d_p'(0) = 0`. -/
theorem dP_family_first_order [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ j, |z j| ≤ B) (hε : ε ≠ 1) (α pbar : ℝ) :
    dP μ α ε (fun j => Real.exp (pbar + 0 * z j)) = 0 ∧
      HasDerivAt (fun s => dP μ α ε (fun j => Real.exp (pbar + s * z j))) 0 0 := by
  obtain ⟨h0, hd⟩ := log_dispIntegral_family_first_order (μ := μ) hz hB hε (-ε / (1 - α)) pbar
  refine ⟨by rw [dP, priceDisp, h0, mul_zero], ?_⟩
  simpa [dP, priceDisp] using hd.const_mul (1 - α)

/-- Galí (2015), p. 171 (**`(1 − α) n = y − a` to first order**): if along a perturbation `s`
the exact relation `(1 − α) n(s) = y(s) − a(s) + d_w(s) + d_p(s)` holds, with wages
`w(j) = w̄ + s z_w(j)` and prices `p(i) = p̄ + s z_p(i)`, and `y`, `a` are differentiable at
`0`, then `(1 − α) n'(0) = y'(0) − a'(0)`: the dispersion terms drop out. -/
theorem employment_first_order {F : Type*} [MeasurableSpace F] {μF : Measure F}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μF] {α εp : ℝ} (hεp : εp ≠ 1)
    (hε : ε ≠ 1) {zw : J → ℝ} (hzw : Measurable zw) {Bw : ℝ} (hBw : ∀ j, |zw j| ≤ Bw)
    {zp : F → ℝ} (hzp : Measurable zp) {Bp : ℝ} (hBp : ∀ i, |zp i| ≤ Bp) (wbar pbar : ℝ)
    {n y a : ℝ → ℝ} {y' a' : ℝ} (hy : HasDerivAt y y' 0) (ha : HasDerivAt a a' 0)
    (hn : ∀ s, (1 - α) * n s = y s - a s + dW μ α ε (fun j => Real.exp (wbar + s * zw j))
      + dP μF α εp (fun i => Real.exp (pbar + s * zp i))) :
    HasDerivAt (fun s => (1 - α) * n s) (y' - a') 0 := by
  have hw := (dW_family_first_order (μ := μ) hzw hBw hε α wbar).2
  have hp := (dP_family_first_order (μ := μF) hzp hBp hεp α pbar).2
  have h := HasDerivAt.add (HasDerivAt.add (HasDerivAt.sub hy ha) hw) hp
  have hfun : (fun s => (1 - α) * n s) = (y - a + fun s => dW μ α ε
      (fun j => Real.exp (wbar + s * zw j))) + fun s => dP μF α εp
      (fun i => Real.exp (pbar + s * zp i)) := by
    funext s
    simp only [Pi.add_apply, Pi.sub_apply]
    exact hn s
  rw [hfun]
  exact h.congr_deriv (by ring)

end Gali.StickyWagesPrices.LaborAggregation
