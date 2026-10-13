/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Dixit–Stiglitz (CES) aggregation

Galí (2015), Chapter 3, §3.1 (p. 53), eq. (12) (p. 58) and Appendix 3.1 (p. 83).

Goods are indexed by a measure space `(G, μ)`: the book's continuum `[0, 1]` with Lebesgue
measure is `μ = volume.restrict (Set.Icc 0 1)`, and a finite (discretised) set of goods with
weights `w i` is `μ = weightMeasure w`. For an elasticity of substitution `ε > 1`, write
`r = (ε − 1)/ε ∈ (0, 1)`. The consumption index is `C = (∫ C(i)^r)^{1/r}` and the price index
is `P = (∫ P(i)^{1−ε})^{1/(1−ε)}`.

## Main results

* `spend_ge`: expenditure minimisation — every bundle `C(·) ≥ 0` costs at least `P · C`,
  where `C` is the bundle's own CES aggregate.
* `spend_eq_iff`: the cost is exactly `P · C` iff `C(i) = (P(i)/P)^{−ε} C` almost everywhere
  (both directions): eq. (1).
* `cesAgg_demand`, `spend_demand`: the demand schedule (1) delivers the aggregate `C` exactly
  and costs exactly `P C` (p. 53).
* `cesAgg_le_of_spend`, `cesAgg_eq_iff_of_spend`: the book's dual form (App. 3.1): for given
  expenditure `X`, the attainable index is at most `X / P`, with equality iff
  `C(i) = (P(i)/P)^{−ε} X/P` a.e.
* `market_clearing`: eq. (12), `Y = C`, and `Y(i) = (P(i)/P)^{−ε} Y`.
* `unitInterval_expenditure_minimisation` and `finite_expenditure_minimisation`: the results
  for the continuum `[0, 1]` and for finitely many goods with positive weights.

The proof replaces the Lagrangian of App. 3.1 by a pointwise weighted AM–GM (Young) inequality
which is integrated; its strict form gives the "only if" direction, which the first-order
conditions alone do not deliver.
-/

namespace Gali.BasicNewKeynesianModel.CES

open MeasureTheory

variable {G : Type*} [MeasurableSpace G]

/-- Galí (2015), p. 53: the aggregate price index `P = (∫ P(i)^{1−ε} di)^{1/(1−ε)}`. -/
noncomputable def priceIndex (μ : Measure G) (ε : ℝ) (P : G → ℝ) : ℝ :=
  (∫ i, P i ^ (1 - ε) ∂μ) ^ (1 - ε)⁻¹

/-- Galí (2015), p. 52–53: the CES consumption index
`C = (∫ C(i)^{(ε−1)/ε} di)^{ε/(ε−1)}`. -/
noncomputable def cesAgg (μ : Measure G) (ε : ℝ) (c : G → ℝ) : ℝ :=
  (∫ i, c i ^ ((ε - 1) / ε) ∂μ) ^ ((ε - 1) / ε)⁻¹

/-- Galí (2015), eq. (1), p. 53: the demand schedule `C(i) = (P(i)/P)^{−ε} C`. -/
noncomputable def demand (μ : Measure G) (ε : ℝ) (P : G → ℝ) (C : ℝ) (i : G) : ℝ :=
  (P i / priceIndex μ ε P) ^ (-ε) * C

/-- Galí (2015), App. 3.1, p. 83: the exponent identity `(ε−1)/ε + 1/ε = 1`. -/
theorem r_add_inv {ε : ℝ} (hε : 1 < ε) : (ε - 1) / ε + 1 / ε = 1 := by
  have : ε ≠ 0 := by linarith
  field_simp
  ring

/-- Galí (2015), App. 3.1, p. 83: the factorisation behind `young_le`,
`c^r = (a c C^{−1/ε})^r (a^{1−ε} C^r)^{1/ε}` with `r = (ε − 1)/ε`. -/
theorem young_key {ε a c C : ℝ} (hε : 1 < ε) (ha : 0 < a) (hc : 0 ≤ c) (hC : 0 < C) :
    (a * c * C ^ (-1 / ε)) ^ ((ε - 1) / ε) * (a ^ (1 - ε) * C ^ ((ε - 1) / ε)) ^ (1 / ε)
      = c ^ ((ε - 1) / ε) := by
  have hε0 : (0 : ℝ) < ε := by linarith
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow ha.le hc,
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul ha.le,
    ← Real.rpow_mul hC.le, ← Real.rpow_mul hC.le]
  have e1 : a ^ ((ε - 1) / ε) * c ^ ((ε - 1) / ε) * C ^ (-1 / ε * ((ε - 1) / ε)) *
      (a ^ ((1 - ε) * (1 / ε)) * C ^ ((ε - 1) / ε * (1 / ε)))
      = c ^ ((ε - 1) / ε) * (a ^ ((ε - 1) / ε) * a ^ ((1 - ε) * (1 / ε))) *
        (C ^ (-1 / ε * ((ε - 1) / ε)) * C ^ ((ε - 1) / ε * (1 / ε))) := by ring
  rw [e1, ← Real.rpow_add ha, ← Real.rpow_add hC]
  have z1 : (ε - 1) / ε + (1 - ε) * (1 / ε) = 0 := by field_simp; ring
  have z2 : -1 / ε * ((ε - 1) / ε) + (ε - 1) / ε * (1 / ε) = 0 := by ring
  rw [z1, z2, Real.rpow_zero, Real.rpow_zero, mul_one, mul_one]

/-- Galí (2015), App. 3.1, p. 83: the pointwise weighted AM–GM (Young) inequality behind
expenditure minimisation. For a relative price `a > 0`, a quantity `c ≥ 0` and an aggregate
`C > 0`, `c^r ≤ r (a c C^{−1/ε}) + (1/ε) a^{1−ε} C^r` with `r = (ε − 1)/ε`. -/
theorem young_le {ε a c C : ℝ} (hε : 1 < ε) (ha : 0 < a) (hc : 0 ≤ c) (hC : 0 < C) :
    c ^ ((ε - 1) / ε) ≤
      (ε - 1) / ε * (a * c * C ^ (-1 / ε)) + 1 / ε * (a ^ (1 - ε) * C ^ ((ε - 1) / ε)) := by
  have hε0 : (0 : ℝ) < ε := by linarith
  rw [← young_key hε ha hc hC]
  exact Real.geom_mean_le_arith_mean2_weighted (div_nonneg (by linarith) hε0.le)
    (by positivity) (by positivity) (by positivity) (r_add_inv hε)

/-- Galí (2015), App. 3.1, p. 83: equality in `young_le` holds iff `c = a^{−ε} C`, i.e. iff
the quantity lies on the demand schedule (1). -/
theorem young_eq_iff {ε a c C : ℝ} (hε : 1 < ε) (ha : 0 < a) (hc : 0 ≤ c) (hC : 0 < C) :
    c ^ ((ε - 1) / ε) =
      (ε - 1) / ε * (a * c * C ^ (-1 / ε)) + 1 / ε * (a ^ (1 - ε) * C ^ ((ε - 1) / ε)) ↔
      c = a ^ (-ε) * C := by
  have hε0 : (0 : ℝ) < ε := by linarith
  rw [← young_key hε ha hc hC, Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos
    (div_pos (by linarith) hε0) (by positivity) (by positivity) (by positivity) (r_add_inv hε)]
  have hk : a * C ^ (-1 / ε) ≠ 0 := by positivity
  have hv : a ^ (1 - ε) * C ^ ((ε - 1) / ε) = a * C ^ (-1 / ε) * (a ^ (-ε) * C) := by
    have h1 : a ^ (1 - ε) = a * a ^ (-ε) := by
      rw [sub_eq_add_neg, Real.rpow_add ha, Real.rpow_one]
    have h2 : C ^ ((ε - 1) / ε) = C ^ (-1 / ε) * C := by
      have : (ε - 1) / ε = -1 / ε + 1 := by field_simp; ring
      rw [this, Real.rpow_add hC, Real.rpow_one]
    rw [h1, h2]
    ring
  rw [hv, show a * c * C ^ (-1 / ε) = a * C ^ (-1 / ε) * c by ring]
  exact mul_right_inj' hk

variable {μ : Measure G} {ε : ℝ} {P : G → ℝ}

/-- Galí (2015), p. 53: the price index is positive when `∫ P(i)^{1−ε} > 0`. -/
theorem priceIndex_pos (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) : 0 < priceIndex μ ε P :=
  Real.rpow_pos_of_pos hpos _

/-- Galí (2015), p. 53: `P^{1−ε} = ∫ P(i)^{1−ε} di`, the defining property of the index. -/
theorem priceIndex_rpow (hε : 1 < ε) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) :
    priceIndex μ ε P ^ (1 - ε) = ∫ i, P i ^ (1 - ε) ∂μ :=
  Real.rpow_inv_rpow hpos.le (by linarith)

/-- Galí (2015), p. 85 (index condition): `∫ (P(i)/P)^{1−ε} di = 1`. -/
theorem integral_relPrice_rpow (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) :
    ∫ i, (P i / priceIndex μ ε P) ^ (1 - ε) ∂μ = 1 := by
  have hI := priceIndex_pos hpos
  simp_rw [Real.div_rpow (hP _).le hI.le]
  rw [integral_div, priceIndex_rpow hε hpos, div_self hpos.ne']

/-- Galí (2015), p. 85: the relative-price integrand `(P(i)/P)^{1−ε}` is integrable. -/
theorem integrable_relPrice_rpow (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hP : ∀ i, 0 < P i)
    (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) :
    Integrable (fun i => (P i / priceIndex μ ε P) ^ (1 - ε)) μ := by
  have hI := priceIndex_pos hpos
  simp_rw [Real.div_rpow (hP _).le hI.le]
  exact hPi.div_const _

/-- Galí (2015), eq. (1) and p. 53: the demand schedule `C(i) = (P(i)/P)^{−ε} C` delivers
exactly the aggregate `C`. -/
theorem cesAgg_demand (hε : 1 < ε) (hP : ∀ i, 0 < P i) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {C : ℝ} (hC : 0 ≤ C) : cesAgg μ ε (demand μ ε P C) = C := by
  have hI := priceIndex_pos hpos
  have hε0 : (0 : ℝ) < ε := by linarith
  have hr : (ε - 1) / ε ≠ 0 := div_ne_zero (by linarith) hε0.ne'
  have hpt : ∀ i, demand μ ε P C i ^ ((ε - 1) / ε)
      = C ^ ((ε - 1) / ε) * (P i / priceIndex μ ε P) ^ (1 - ε) := by
    intro i
    have ha : 0 < P i / priceIndex μ ε P := div_pos (hP i) hI
    rw [demand, Real.mul_rpow (by positivity) hC, ← Real.rpow_mul ha.le]
    have : -ε * ((ε - 1) / ε) = 1 - ε := by field_simp; ring
    rw [this, mul_comm]
  unfold cesAgg
  simp_rw [hpt]
  rw [integral_const_mul, integral_relPrice_rpow hε hP hpos, mul_one, Real.rpow_rpow_inv hC hr]

/-- Galí (2015), p. 53: `P(i) (P(i)/P)^{−ε} C = P C (P(i)/P)^{1−ε}` pointwise. -/
theorem price_mul_demand (hP : ∀ i, 0 < P i) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) (C : ℝ)
    (i : G) : P i * demand μ ε P C i
      = priceIndex μ ε P * C * (P i / priceIndex μ ε P) ^ (1 - ε) := by
  have hI := priceIndex_pos hpos
  have ha : 0 < P i / priceIndex μ ε P := div_pos (hP i) hI
  have h1 : (P i / priceIndex μ ε P) ^ (1 - ε)
      = P i / priceIndex μ ε P * (P i / priceIndex μ ε P) ^ (-ε) := by
    rw [sub_eq_add_neg, Real.rpow_add ha, Real.rpow_one]
  rw [demand, h1]
  field_simp

/-- Galí (2015), p. 53: under the demand schedule, total expenditure is
`∫ P(i) C(i) di = P C`. -/
theorem spend_demand (hε : 1 < ε) (hP : ∀ i, 0 < P i) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    (C : ℝ) : ∫ i, P i * demand μ ε P C i ∂μ = priceIndex μ ε P * C := by
  simp_rw [price_mul_demand hP hpos C]
  rw [integral_const_mul, integral_relPrice_rpow hε hP hpos, mul_one]

/-- Galí (2015), App. 3.1, p. 83: the CES aggregate is nonnegative. -/
theorem cesAgg_nonneg {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) : 0 ≤ cesAgg μ ε c :=
  Real.rpow_nonneg (integral_nonneg fun i => Real.rpow_nonneg (hc i) _) _

/-- Galí (2015), App. 3.1, p. 83: `C^r = ∫ C(i)^r` for the CES aggregate `C`. -/
theorem cesAgg_rpow (hε : 1 < ε) {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) :
    cesAgg μ ε c ^ ((ε - 1) / ε) = ∫ i, c i ^ ((ε - 1) / ε) ∂μ :=
  Real.rpow_inv_rpow (integral_nonneg fun i => Real.rpow_nonneg (hc i) _)
    (div_ne_zero (by linarith) (by linarith))

/-- Galí (2015), App. 3.1, p. 83: the integrated Young bound. For a bundle with positive
aggregate `C`, `C^r ≤ r C^{−1/ε} (∫ P c)/P + (1/ε) C^r`. -/
theorem integrated_young (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ)
    (hC : 0 < cesAgg μ ε c) :
    Integrable (fun i => (ε - 1) / ε * (cesAgg μ ε c ^ (-1 / ε) / priceIndex μ ε P) *
        (P i * c i) + 1 / ε * cesAgg μ ε c ^ ((ε - 1) / ε) *
          (P i / priceIndex μ ε P) ^ (1 - ε)) μ ∧
      (∀ i, c i ^ ((ε - 1) / ε) ≤ (ε - 1) / ε * (cesAgg μ ε c ^ (-1 / ε) / priceIndex μ ε P) *
        (P i * c i) + 1 / ε * cesAgg μ ε c ^ ((ε - 1) / ε) *
          (P i / priceIndex μ ε P) ^ (1 - ε)) ∧
      ∫ i, ((ε - 1) / ε * (cesAgg μ ε c ^ (-1 / ε) / priceIndex μ ε P) *
        (P i * c i) + 1 / ε * cesAgg μ ε c ^ ((ε - 1) / ε) *
          (P i / priceIndex μ ε P) ^ (1 - ε)) ∂μ
        = (ε - 1) / ε * (cesAgg μ ε c ^ (-1 / ε) / priceIndex μ ε P) *
          (∫ i, P i * c i ∂μ) + 1 / ε * cesAgg μ ε c ^ ((ε - 1) / ε) := by
  have hI := priceIndex_pos hpos
  have hint1 := hpc.const_mul ((ε - 1) / ε * (cesAgg μ ε c ^ (-1 / ε) / priceIndex μ ε P))
  have hint2 := (integrable_relPrice_rpow hPi hP hpos).const_mul
    (1 / ε * cesAgg μ ε c ^ ((ε - 1) / ε))
  refine ⟨hint1.add hint2, fun i => ?_, ?_⟩
  · have h := young_le hε (div_pos (hP i) hI) (hc i) hC
    have e : (ε - 1) / ε * (cesAgg μ ε c ^ (-1 / ε) / priceIndex μ ε P) * (P i * c i)
        = (ε - 1) / ε * (P i / priceIndex μ ε P * c i * cesAgg μ ε c ^ (-1 / ε)) := by ring
    rw [e]
    linarith
  · rw [integral_add hint1 hint2, integral_const_mul, integral_const_mul,
      integral_relPrice_rpow hε hP hpos, mul_one]

/-- Galí (2015), p. 53 and App. 3.1, p. 83 (**expenditure minimisation**): any bundle
`C(·) ≥ 0` costs at least `P · C`, where `C` is its CES aggregate. -/
theorem spend_ge (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ) :
    priceIndex μ ε P * cesAgg μ ε c ≤ ∫ i, P i * c i ∂μ := by
  have hI := priceIndex_pos hpos
  have hε0 : (0 : ℝ) < ε := by linarith
  have hS : 0 ≤ ∫ i, P i * c i ∂μ := integral_nonneg fun i => mul_nonneg (hP i).le (hc i)
  rcases (cesAgg_nonneg (μ := μ) (ε := ε) hc).eq_or_lt with h0 | hC
  · rw [← h0, mul_zero]; exact hS
  obtain ⟨hint, hle, hval⟩ := integrated_young hε hP hPi hpos hc hpc hC
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun i => Real.rpow_nonneg (hc i) ((ε - 1) / ε)) hint
    (Filter.Eventually.of_forall hle)
  rw [hval, ← cesAgg_rpow hε hc] at hmono
  set C := cesAgg μ ε c
  set S := ∫ i, P i * c i ∂μ
  have hK : 0 < C ^ (-1 / ε) := Real.rpow_pos_of_pos hC _
  have hCr : C ^ ((ε - 1) / ε) = C * C ^ (-1 / ε) := by
    have : (ε - 1) / ε = 1 + -1 / ε := by field_simp; ring
    rw [this, Real.rpow_add hC, Real.rpow_one]
  rw [hCr] at hmono
  have hr : 0 < (ε - 1) / ε := div_pos (by linarith) hε0
  have h1 : (ε - 1) / ε * (C * C ^ (-1 / ε)) ≤
      (ε - 1) / ε * (C ^ (-1 / ε) * (S / priceIndex μ ε P)) := by
    have e : 1 / ε = 1 - (ε - 1) / ε := by field_simp; ring
    rw [e] at hmono
    have e2 : (ε - 1) / ε * (C ^ (-1 / ε) / priceIndex μ ε P) * S
        = (ε - 1) / ε * (C ^ (-1 / ε) * (S / priceIndex μ ε P)) := by ring
    rw [e2] at hmono
    linarith
  have h2 := le_of_mul_le_mul_left h1 hr
  rw [mul_comm C] at h2
  have h3 := le_of_mul_le_mul_left h2 hK
  rw [le_div_iff₀ hI] at h3
  linarith

/-- Galí (2015), eq. (1), p. 53 and App. 3.1, p. 83: a bundle costs exactly `P · C` (its
aggregate `C`) **if and only if** it is the demand schedule `C(i) = (P(i)/P)^{−ε} C`
almost everywhere. -/
theorem spend_eq_iff (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ) :
    ∫ i, P i * c i ∂μ = priceIndex μ ε P * cesAgg μ ε c ↔
      c =ᵐ[μ] demand μ ε P (cesAgg μ ε c) := by
  have hI := priceIndex_pos hpos
  have hε0 : (0 : ℝ) < ε := by linarith
  constructor
  swap
  · intro h
    rw [← spend_demand hε hP hpos (cesAgg μ ε c)]
    refine integral_congr_ae ?_
    filter_upwards [h] with i hi
    rw [hi]
  intro heq
  rcases (cesAgg_nonneg (μ := μ) (ε := ε) hc).eq_or_lt with h0 | hC
  · rw [← h0, mul_zero] at heq
    have hz := (integral_eq_zero_iff_of_nonneg
      (fun i => mul_nonneg (hP i).le (hc i)) hpc).1 heq
    filter_upwards [hz] with i hi
    rw [← h0, demand, mul_zero]
    simp only [Pi.zero_apply] at hi
    rcases mul_eq_zero.1 hi with h | h
    · exact absurd h (hP i).ne'
    · exact h
  obtain ⟨hint, hle, hval⟩ := integrated_young hε hP hPi hpos hc hpc hC
  set C := cesAgg μ ε c
  have hcr : Integrable (fun i => c i ^ ((ε - 1) / ε)) μ := by
    refine Integrable.of_integral_ne_zero ?_
    rw [← cesAgg_rpow hε hc]
    exact (Real.rpow_pos_of_pos hC _).ne'
  have hdiff := (integral_eq_zero_iff_of_nonneg
    (fun i => sub_nonneg.2 (hle i)) (hint.sub hcr)).1 (by
      rw [integral_sub hint hcr, hval, ← cesAgg_rpow hε hc, heq]
      have hCr : C ^ ((ε - 1) / ε) = C * C ^ (-1 / ε) := by
        have : (ε - 1) / ε = 1 + -1 / ε := by field_simp; ring
        rw [this, Real.rpow_add hC, Real.rpow_one]
      rw [hCr]
      field_simp
      ring)
  filter_upwards [hdiff] with i hi
  simp only [Pi.zero_apply, sub_eq_zero] at hi
  have := (young_eq_iff hε (div_pos (hP i) hI) (hc i) hC).1 (by
    rw [← hi]
    ring)
  rw [this, demand]

/-- Galí (2015), App. 3.1, p. 83 (dual form): for a bundle with expenditure
`∫ P(i) C(i) = X`, the attainable consumption index is at most `X / P`. -/
theorem cesAgg_le_of_spend (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ) {X : ℝ}
    (hX : ∫ i, P i * c i ∂μ = X) : cesAgg μ ε c ≤ X / priceIndex μ ε P := by
  rw [le_div_iff₀ (priceIndex_pos hpos), mul_comm, ← hX]
  exact spend_ge hε hP hPi hpos hc hpc

/-- Galí (2015), App. 3.1, p. 83 (dual form, equality): with expenditure `X`, the index
attains `X / P` iff `C(i) = (P(i)/P)^{−ε} X/P` almost everywhere. -/
theorem cesAgg_eq_iff_of_spend (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - ε)) μ) (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ) {X : ℝ}
    (hX : ∫ i, P i * c i ∂μ = X) :
    cesAgg μ ε c = X / priceIndex μ ε P ↔
      c =ᵐ[μ] demand μ ε P (X / priceIndex μ ε P) := by
  have hI := priceIndex_pos hpos
  constructor
  · intro h
    rw [← h]
    refine (spend_eq_iff hε hP hPi hpos hc hpc).1 ?_
    rw [h, hX]
    field_simp
  · intro h
    have hX0 : 0 ≤ X / priceIndex μ ε P := by
      rw [← hX]
      exact div_nonneg (integral_nonneg fun i => mul_nonneg (hP i).le (hc i)) hI.le
    have hagg : cesAgg μ ε c = cesAgg μ ε (demand μ ε P (X / priceIndex μ ε P)) := by
      unfold cesAgg
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [h] with i hi
      rw [hi]
    rw [hagg, cesAgg_demand hε hP hpos hX0]

/-- Galí (2015), eq. (12), p. 58: goods-market clearing `Y(i) = C(i)` for all `i`, with
households on their demand schedule, gives `Y = C` for the CES output index and
`Y(i) = (P(i)/P)^{−ε} Y`. -/
theorem market_clearing (hε : 1 < ε) (hP : ∀ i, 0 < P i)
    (hpos : 0 < ∫ i, P i ^ (1 - ε) ∂μ) {C : ℝ} (hC : 0 ≤ C) {Y : G → ℝ}
    (hclear : ∀ i, Y i = demand μ ε P C i) :
    cesAgg μ ε Y = C ∧ ∀ i, Y i = demand μ ε P (cesAgg μ ε Y) i := by
  have hY : Y = demand μ ε P C := funext hclear
  have hagg : cesAgg μ ε Y = C := by rw [hY, cesAgg_demand hε hP hpos hC]
  exact ⟨hagg, fun i => by rw [hagg, hclear]⟩

/-- Galí (2015), p. 53: a positive integrable function has positive integral against a
nonzero measure (used to see that `∫ P(i)^{1−ε} > 0`). -/
theorem integral_pos_of_pos {f : G → ℝ} (hμ : μ ≠ 0) (hf : ∀ i, 0 < f i)
    (hfi : Integrable f μ) : 0 < ∫ i, f i ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun i => (hf i).le) hfi]
  have : Function.support f = Set.univ :=
    Set.eq_univ_of_forall fun i => (hf i).ne'
  rw [this]
  exact Measure.measure_univ_pos.2 hμ

/-- Galí (2015), p. 53: Lebesgue measure on the goods continuum `[0, 1]` is nonzero. -/
theorem unitInterval_ne_zero : (volume.restrict (Set.Icc (0 : ℝ) 1)) ≠ 0 := by
  rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc]
  simp

/-- Galí (2015), §3.1, p. 53 and App. 3.1, p. 83, on the book's **continuum of goods
`[0, 1]` with Lebesgue measure**: (i) every bundle `C(·) ≥ 0` costs at least `P · C`;
(ii) it costs exactly `P · C` iff `C(i) = (P(i)/P)^{−ε} C` for a.e. `i ∈ [0, 1]`;
(iii) the demand schedule attains any aggregate `C ≥ 0`; (iv) it costs `P C`. -/
theorem unitInterval_expenditure_minimisation (hε : 1 < ε) {Q : ℝ → ℝ} (hQ : ∀ i, 0 < Q i)
    (hQi : IntegrableOn (fun i => Q i ^ (1 - ε)) (Set.Icc 0 1)) {c : ℝ → ℝ}
    (hc : ∀ i, 0 ≤ c i) (hQc : IntegrableOn (fun i => Q i * c i) (Set.Icc 0 1)) :
    priceIndex (volume.restrict (Set.Icc 0 1)) ε Q * cesAgg (volume.restrict (Set.Icc 0 1)) ε c
        ≤ ∫ i in Set.Icc 0 1, Q i * c i ∧
      (∫ i in Set.Icc 0 1, Q i * c i
          = priceIndex (volume.restrict (Set.Icc 0 1)) ε Q *
            cesAgg (volume.restrict (Set.Icc 0 1)) ε c ↔
        ∀ᵐ i ∂(volume.restrict (Set.Icc 0 1)),
          c i = demand (volume.restrict (Set.Icc 0 1)) ε Q
            (cesAgg (volume.restrict (Set.Icc 0 1)) ε c) i) ∧
      (∀ C : ℝ, 0 ≤ C → cesAgg (volume.restrict (Set.Icc 0 1)) ε
        (demand (volume.restrict (Set.Icc 0 1)) ε Q C) = C) ∧
      ∀ C : ℝ, ∫ i in Set.Icc 0 1, Q i * demand (volume.restrict (Set.Icc 0 1)) ε Q C i
        = priceIndex (volume.restrict (Set.Icc 0 1)) ε Q * C := by
  have hpos := integral_pos_of_pos unitInterval_ne_zero (fun i => Real.rpow_pos_of_pos (hQ i) _)
    hQi
  exact ⟨spend_ge hε hQ hQi hpos hc hQc, spend_eq_iff hε hQ hQi hpos hc hQc,
    fun C hC => cesAgg_demand hε hQ hpos hC, spend_demand hε hQ hpos⟩

namespace Finite

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Galí (2015), p. 53 (finitely many goods): the measure placing weight `w i` on good `i`,
a discretisation of `[0, 1]` (e.g. `w i = 1/n`). -/
noncomputable def weightMeasure (w : ι → ℝ) : Measure ι :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac i

/-- Galí (2015), p. 53: the weighted measure gives good `x` mass `w x`. -/
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
/-- Galí (2015), p. 53: the weighted measure is finite. -/
theorem weightMeasure_univ_lt_top {w : ι → ℝ} : weightMeasure w Set.univ < ⊤ := by
  rw [weightMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact ENNReal.sum_lt_top.2 fun i _ => ENNReal.ofReal_lt_top

/-- Galí (2015), p. 53: every function is integrable for the weighted measure. -/
theorem integrable_weightMeasure {w : ι → ℝ} (f : ι → ℝ) : Integrable f (weightMeasure w) := by
  have : IsFiniteMeasure (weightMeasure w) := ⟨weightMeasure_univ_lt_top⟩
  exact Integrable.of_finite

/-- Galí (2015), p. 53: integrals against the weighted measure are weighted sums,
`∫ f = ∑ᵢ w i f i`. -/
theorem integral_weightMeasure {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (f : ι → ℝ) :
    ∫ i, f i ∂(weightMeasure w) = ∑ i, w i * f i := by
  rw [integral_fintype (integrable_weightMeasure f)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.real, weightMeasure_singleton, ENNReal.toReal_ofReal (hw i), smul_eq_mul]

/-- Galí (2015), §3.1, p. 53 and App. 3.1, p. 83, for **finitely many goods** with weights
`w i > 0`. With `P = (∑ w P(i)^{1−ε})^{1/(1−ε)}` and `C = (∑ w C(i)^r)^{1/r}`:
(i) `∑ w P(i) C(i) ≥ P C`; (ii) equality iff `C(i) = (P(i)/P)^{−ε} C` for **every** `i`;
(iii) the demand schedule attains any `C ≥ 0`; (iv) it costs exactly `P C`. -/
theorem finite_expenditure_minimisation [Nonempty ι] (hε : 1 < ε) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) {Q : ι → ℝ} (hQ : ∀ i, 0 < Q i) {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) :
    (∑ i, w i * Q i ^ (1 - ε)) ^ (1 - ε)⁻¹ * (∑ i, w i * c i ^ ((ε - 1) / ε)) ^ ((ε - 1) / ε)⁻¹
        ≤ ∑ i, w i * (Q i * c i) ∧
      (∑ i, w i * (Q i * c i) = (∑ i, w i * Q i ^ (1 - ε)) ^ (1 - ε)⁻¹ *
          (∑ i, w i * c i ^ ((ε - 1) / ε)) ^ ((ε - 1) / ε)⁻¹ ↔
        ∀ i, c i = (Q i / (∑ j, w j * Q j ^ (1 - ε)) ^ (1 - ε)⁻¹) ^ (-ε) *
          (∑ j, w j * c j ^ ((ε - 1) / ε)) ^ ((ε - 1) / ε)⁻¹) ∧
      (∀ C : ℝ, 0 ≤ C → (∑ i, w i *
        ((Q i / (∑ j, w j * Q j ^ (1 - ε)) ^ (1 - ε)⁻¹) ^ (-ε) * C) ^ ((ε - 1) / ε)) ^
          ((ε - 1) / ε)⁻¹ = C) ∧
      ∀ C : ℝ, ∑ i, w i * (Q i * ((Q i / (∑ j, w j * Q j ^ (1 - ε)) ^ (1 - ε)⁻¹) ^ (-ε) * C))
        = (∑ j, w j * Q j ^ (1 - ε)) ^ (1 - ε)⁻¹ * C := by
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hw i).le
  have hμ : weightMeasure w ≠ 0 := by
    intro h
    obtain ⟨x⟩ := ‹Nonempty ι›
    have := weightMeasure_singleton (w := w) x
    rw [h, Measure.coe_zero, Pi.zero_apply] at this
    exact (ENNReal.ofReal_pos.2 (hw x)).ne' this.symm
  have hpos := integral_pos_of_pos hμ (fun i => Real.rpow_pos_of_pos (hQ i) (1 - ε))
    (integrable_weightMeasure _)
  have hPI : priceIndex (weightMeasure w) ε Q = (∑ j, w j * Q j ^ (1 - ε)) ^ (1 - ε)⁻¹ := by
    rw [priceIndex, integral_weightMeasure hw0]
  have hCA : ∀ d : ι → ℝ, cesAgg (weightMeasure w) ε d
      = (∑ j, w j * d j ^ ((ε - 1) / ε)) ^ ((ε - 1) / ε)⁻¹ := by
    intro d
    rw [cesAgg, integral_weightMeasure hw0]
  have hD : ∀ C i, demand (weightMeasure w) ε Q C i
      = (Q i / (∑ j, w j * Q j ^ (1 - ε)) ^ (1 - ε)⁻¹) ^ (-ε) * C := by
    intro C i
    rw [demand, hPI]
  have h1 := spend_ge hε hQ (integrable_weightMeasure _) hpos hc (integrable_weightMeasure _)
  have h2 := spend_eq_iff hε hQ (integrable_weightMeasure _) hpos hc (integrable_weightMeasure _)
  rw [hPI, hCA, integral_weightMeasure hw0] at h1 h2
  rw [Filter.EventuallyEq, ae_iff_of_countable] at h2
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [h2]
    constructor
    · intro h i
      rw [← hD]
      exact h i (by rw [weightMeasure_singleton]; exact (ENNReal.ofReal_pos.2 (hw i)).ne')
    · intro h i _
      rw [hD]
      exact h i
  · intro C hC
    have := cesAgg_demand hε hQ hpos hC (μ := weightMeasure w)
    rw [hCA] at this
    simpa only [hD] using this
  · intro C
    have := spend_demand hε hQ hpos C (μ := weightMeasure w)
    rw [integral_weightMeasure hw0, hPI] at this
    simpa only [hD] using this

end Finite

end Gali.BasicNewKeynesianModel.CES
