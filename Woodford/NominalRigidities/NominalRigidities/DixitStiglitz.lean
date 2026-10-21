/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Dixit–Stiglitz (CES) aggregation

Woodford (2003), *Interest and Prices*, Chapter 3: §1.1, eqs. (1.2)–(1.5), pp. 146–147 (goods);
§2.5, eqs. (2.22)–(2.23) and the demand system on p. 201 (the two-sector nested aggregator, with
footnote 61 on the Cobb–Douglas case); §4.1, eqs. (4.1)–(4.2), pp. 221–222 (labour types).

The general measure-space part (`priceIndex`, `cesAgg`, `demand`, `young_le`, `spend_ge`,
`spend_eq_iff`, `cesAgg_demand`, `spend_demand`, the dual form, the `[0, 1]` and finite
specialisations) is restated from the Galí Chapter 3 project (`BasicNewKeynesianModel/CES.lean`),
with `ε` renamed `θ`. In the code `P : G → ℝ` denotes the individual prices `p(i)`.

Goods are indexed by a measure space `(G, μ)`: the book's continuum `[0, 1]` with Lebesgue
measure is `μ = volume.restrict (Set.Icc 0 1)`; finitely many goods with weights `w i` is
`μ = Finite.weightMeasure w`. For `θ > 1` write `r = (θ − 1)/θ ∈ (0, 1)`.

## Main results

* (1.3) is the minimal unit cost: `spend_ge` (every bundle costs at least `P · C`),
  `spend_eq_iff` (exactly `P · C` iff the bundle is the demand (1.5) a.e.), `cost_isLeast`,
  `cost_minimiser_unique`, `priceIndex_isLeast_unitCost` (existence AND uniqueness of the
  minimiser); `cesAgg_demand`, `spend_demand`: demand (1.5) attains `C` and expenditure is `P C`;
  `cesAgg_le_of_spend`, `cesAgg_eq_iff_of_spend`: the dual (index-maximising) form;
  `priceIndex_const`, `cesAgg_const`: normalisation; `market_clearing`.
* Finite CES for ANY `η > 0`, `η ≠ 1` (needed since (2.22) allows `η < 1`): `amgm_lt_one`,
  `fin_gap`, `fin_cost_ge_and_eq_iff`, `fin_demand_attains`; the Cobb–Douglas case
  `cobbDouglas_cost_ge_and_eq_iff` and the limit `tendsto_cobbDouglas` (n. 61) via
  `tendsto_powerMean_geomMean`.
* The two-sector model (2.22)–(2.23) (namespace `Nested`, any finite set of sectors):
  `sectorIndex_eq`, `sectorPrice_eq`, `sector_cost` (sectoral demand
  `c(i) = n_j⁻¹ C_j (p/P_j)^{−θ}`),
  `nested_cost_ge_and_eq_iff` (two-level duality, both directions), `nested_demand_attains`,
  `nested_isLeast` (the overall index is the minimal cost of a unit of (2.22)),
  `sectorPrice_const`, `finPriceIndex_const`, `common_price_demands` (the normalisation on
  p. 201); `twoSector_split` (`[0,1] = [0,n₁] ∪ (n₁,1]`).
* Labour types (4.1)–(4.2): `labour_cost_minimisation`.

For `η < 1` the CES index is defined only for positive composites (Lean's `0 ^ r = 0` for
`r < 0` is not the economic limit), so positivity of the sectoral indices is assumed there.
-/

namespace Woodford.NominalRigidities.DixitStiglitz

open MeasureTheory

variable {G : Type*} [MeasurableSpace G]

/-- Woodford (2003), eq. (1.3), p. 146: the price index `P = (∫ p(i)^{1−θ} di)^{1/(1−θ)}`. -/
noncomputable def priceIndex (μ : Measure G) (θ : ℝ) (P : G → ℝ) : ℝ :=
  (∫ i, P i ^ (1 - θ) ∂μ) ^ (1 - θ)⁻¹

/-- Woodford (2003), eq. (1.2), p. 146: the Dixit–Stiglitz index
`C = (∫ c(i)^{(θ−1)/θ} di)^{θ/(θ−1)}`. -/
noncomputable def cesAgg (μ : Measure G) (θ : ℝ) (c : G → ℝ) : ℝ :=
  (∫ i, c i ^ ((θ - 1) / θ) ∂μ) ^ ((θ - 1) / θ)⁻¹

/-- Woodford (2003), eq. (1.5), p. 147: demand `c(i) = C (p(i)/P)^{−θ}`. -/
noncomputable def demand (μ : Measure G) (θ : ℝ) (P : G → ℝ) (C : ℝ) (i : G) : ℝ :=
  (P i / priceIndex μ θ P) ^ (-θ) * C

/-- Woodford (2003), Ch. 3 §1.1, pp. 146–147: the exponent identity `(θ−1)/θ + 1/θ = 1`. -/
theorem r_add_inv {θ : ℝ} (hθ : 1 < θ) : (θ - 1) / θ + 1 / θ = 1 := by
  have : θ ≠ 0 := by linarith
  field_simp
  ring

/-- Woodford (2003), Ch. 3 §1.1, pp. 146–147: the factorisation behind `young_le`,
`c^r = (a c C^{−1/θ})^r (a^{1−θ} C^r)^{1/θ}` with `r = (θ − 1)/θ`. -/
theorem young_key {θ a c C : ℝ} (hθ : 1 < θ) (ha : 0 < a) (hc : 0 ≤ c) (hC : 0 < C) :
    (a * c * C ^ (-1 / θ)) ^ ((θ - 1) / θ) * (a ^ (1 - θ) * C ^ ((θ - 1) / θ)) ^ (1 / θ)
      = c ^ ((θ - 1) / θ) := by
  have hθ0 : (0 : ℝ) < θ := by linarith
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow ha.le hc,
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul ha.le,
    ← Real.rpow_mul hC.le, ← Real.rpow_mul hC.le]
  have e1 : a ^ ((θ - 1) / θ) * c ^ ((θ - 1) / θ) * C ^ (-1 / θ * ((θ - 1) / θ)) *
      (a ^ ((1 - θ) * (1 / θ)) * C ^ ((θ - 1) / θ * (1 / θ)))
      = c ^ ((θ - 1) / θ) * (a ^ ((θ - 1) / θ) * a ^ ((1 - θ) * (1 / θ))) *
        (C ^ (-1 / θ * ((θ - 1) / θ)) * C ^ ((θ - 1) / θ * (1 / θ))) := by ring
  rw [e1, ← Real.rpow_add ha, ← Real.rpow_add hC]
  have z1 : (θ - 1) / θ + (1 - θ) * (1 / θ) = 0 := by field_simp; ring
  have z2 : -1 / θ * ((θ - 1) / θ) + (θ - 1) / θ * (1 / θ) = 0 := by ring
  rw [z1, z2, Real.rpow_zero, Real.rpow_zero, mul_one, mul_one]

/-- Woodford (2003), Ch. 3 §1.1, pp. 146–147: the pointwise weighted AM–GM (Young) inequality behind
expenditure minimisation. For a relative price `a > 0`, a quantity `c ≥ 0` and an aggregate
`C > 0`, `c^r ≤ r (a c C^{−1/θ}) + (1/θ) a^{1−θ} C^r` with `r = (θ − 1)/θ`. -/
theorem young_le {θ a c C : ℝ} (hθ : 1 < θ) (ha : 0 < a) (hc : 0 ≤ c) (hC : 0 < C) :
    c ^ ((θ - 1) / θ) ≤
      (θ - 1) / θ * (a * c * C ^ (-1 / θ)) + 1 / θ * (a ^ (1 - θ) * C ^ ((θ - 1) / θ)) := by
  have hθ0 : (0 : ℝ) < θ := by linarith
  rw [← young_key hθ ha hc hC]
  exact Real.geom_mean_le_arith_mean2_weighted (div_nonneg (by linarith) hθ0.le)
    (by positivity) (by positivity) (by positivity) (r_add_inv hθ)

/-- Woodford (2003), Ch. 3 §1.1, pp. 146–147: equality in `young_le` holds iff
`c = a^{−θ} C`, i.e. iff the quantity lies on the demand schedule (1.5). -/
theorem young_eq_iff {θ a c C : ℝ} (hθ : 1 < θ) (ha : 0 < a) (hc : 0 ≤ c) (hC : 0 < C) :
    c ^ ((θ - 1) / θ) =
      (θ - 1) / θ * (a * c * C ^ (-1 / θ)) + 1 / θ * (a ^ (1 - θ) * C ^ ((θ - 1) / θ)) ↔
      c = a ^ (-θ) * C := by
  have hθ0 : (0 : ℝ) < θ := by linarith
  rw [← young_key hθ ha hc hC, Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos
    (div_pos (by linarith) hθ0) (by positivity) (by positivity) (by positivity) (r_add_inv hθ)]
  have hk : a * C ^ (-1 / θ) ≠ 0 := by positivity
  have hv : a ^ (1 - θ) * C ^ ((θ - 1) / θ) = a * C ^ (-1 / θ) * (a ^ (-θ) * C) := by
    have h1 : a ^ (1 - θ) = a * a ^ (-θ) := by
      rw [sub_eq_add_neg, Real.rpow_add ha, Real.rpow_one]
    have h2 : C ^ ((θ - 1) / θ) = C ^ (-1 / θ) * C := by
      have : (θ - 1) / θ = -1 / θ + 1 := by field_simp; ring
      rw [this, Real.rpow_add hC, Real.rpow_one]
    rw [h1, h2]
    ring
  rw [hv, show a * c * C ^ (-1 / θ) = a * C ^ (-1 / θ) * c by ring]
  exact mul_right_inj' hk

variable {μ : Measure G} {θ : ℝ} {P : G → ℝ}

/-- Woodford (2003), p. 147: the price index is positive when `∫ p(i)^{1−θ} > 0`. -/
theorem priceIndex_pos (hpos : 0 < ∫ i, P i ^ (1 - θ) ∂μ) : 0 < priceIndex μ θ P :=
  Real.rpow_pos_of_pos hpos _

/-- Woodford (2003), eq. (1.3), p. 146 (used on p. 178 for any `θ ≠ 1`):
`P^{1−θ} = ∫ p(i)^{1−θ} di` when the integral is positive. -/
theorem priceIndex_rpow_of_ne (hθ : θ ≠ 1) (hpos : 0 < ∫ i, P i ^ (1 - θ) ∂μ) :
    priceIndex μ θ P ^ (1 - θ) = ∫ i, P i ^ (1 - θ) ∂μ :=
  Real.rpow_inv_rpow hpos.le (sub_ne_zero.mpr (Ne.symm hθ))

/-- Woodford (2003), p. 147: `P^{1−θ} = ∫ p(i)^{1−θ} di`, the defining property of the index. -/
theorem priceIndex_rpow (hθ : 1 < θ) (hpos : 0 < ∫ i, P i ^ (1 - θ) ∂μ) :
    priceIndex μ θ P ^ (1 - θ) = ∫ i, P i ^ (1 - θ) ∂μ :=
  priceIndex_rpow_of_ne hθ.ne' hpos

/-- Woodford (2003), eq. (1.3), p. 146 (index condition): `∫ (p(i)/P)^{1−θ} di = 1`. -/
theorem integral_relPrice_rpow (hθ : 1 < θ) (hP : ∀ i, 0 < P i)
    (hpos : 0 < ∫ i, P i ^ (1 - θ) ∂μ) :
    ∫ i, (P i / priceIndex μ θ P) ^ (1 - θ) ∂μ = 1 := by
  have hI := priceIndex_pos hpos
  simp_rw [Real.div_rpow (hP _).le hI.le]
  rw [integral_div, priceIndex_rpow hθ hpos, div_self hpos.ne']

/-- Woodford (2003), eq. (1.3), p. 146: the relative-price integrand `(p(i)/P)^{1−θ}` is
integrable. -/
theorem integrable_relPrice_rpow (hPi : Integrable (fun i => P i ^ (1 - θ)) μ) (hP : ∀ i, 0 < P i)
    (hpos : 0 < ∫ i, P i ^ (1 - θ) ∂μ) :
    Integrable (fun i => (P i / priceIndex μ θ P) ^ (1 - θ)) μ := by
  have hI := priceIndex_pos hpos
  simp_rw [Real.div_rpow (hP _).le hI.le]
  exact hPi.div_const _

/-- Woodford (2003), eq. (1.5), p. 147: the demand schedule `c(i) = (p(i)/P)^{−θ} C` delivers
exactly the aggregate `C`. -/
theorem cesAgg_demand (hθ : 1 < θ) (hP : ∀ i, 0 < P i) (hpos : 0 < ∫ i, P i ^ (1 - θ) ∂μ)
    {C : ℝ} (hC : 0 ≤ C) : cesAgg μ θ (demand μ θ P C) = C := by
  have hI := priceIndex_pos hpos
  have hθ0 : (0 : ℝ) < θ := by linarith
  have hr : (θ - 1) / θ ≠ 0 := div_ne_zero (by linarith) hθ0.ne'
  have hpt : ∀ i, demand μ θ P C i ^ ((θ - 1) / θ)
      = C ^ ((θ - 1) / θ) * (P i / priceIndex μ θ P) ^ (1 - θ) := by
    intro i
    have ha : 0 < P i / priceIndex μ θ P := div_pos (hP i) hI
    rw [demand, Real.mul_rpow (by positivity) hC, ← Real.rpow_mul ha.le]
    have : -θ * ((θ - 1) / θ) = 1 - θ := by field_simp; ring
    rw [this, mul_comm]
  unfold cesAgg
  simp_rw [hpt]
  rw [integral_const_mul, integral_relPrice_rpow hθ hP hpos, mul_one, Real.rpow_rpow_inv hC hr]

/-- Woodford (2003), p. 147: `p(i) (p(i)/P)^{−θ} C = P C (p(i)/P)^{1−θ}` pointwise. -/
theorem price_mul_demand (hP : ∀ i, 0 < P i) (hpos : 0 < ∫ i, P i ^ (1 - θ) ∂μ) (C : ℝ)
    (i : G) : P i * demand μ θ P C i
      = priceIndex μ θ P * C * (P i / priceIndex μ θ P) ^ (1 - θ) := by
  have hI := priceIndex_pos hpos
  have ha : 0 < P i / priceIndex μ θ P := div_pos (hP i) hI
  have h1 : (P i / priceIndex μ θ P) ^ (1 - θ)
      = P i / priceIndex μ θ P * (P i / priceIndex μ θ P) ^ (-θ) := by
    rw [sub_eq_add_neg, Real.rpow_add ha, Real.rpow_one]
  rw [demand, h1]
  field_simp

/-- Woodford (2003), p. 147: under the demand schedule, total expenditure is
`∫ p(i) c(i) di = P C`. -/
theorem spend_demand (hθ : 1 < θ) (hP : ∀ i, 0 < P i) (hpos : 0 < ∫ i, P i ^ (1 - θ) ∂μ)
    (C : ℝ) : ∫ i, P i * demand μ θ P C i ∂μ = priceIndex μ θ P * C := by
  simp_rw [price_mul_demand hP hpos C]
  rw [integral_const_mul, integral_relPrice_rpow hθ hP hpos, mul_one]

/-- Woodford (2003), Ch. 3 §1.1, pp. 146–147: the CES aggregate is nonnegative. -/
theorem cesAgg_nonneg {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) : 0 ≤ cesAgg μ θ c :=
  Real.rpow_nonneg (integral_nonneg fun i => Real.rpow_nonneg (hc i) _) _

/-- Woodford (2003), Ch. 3 §1.1, pp. 146–147: `C^r = ∫ c(i)^r` for the CES aggregate `C`. -/
theorem cesAgg_rpow (hθ : 1 < θ) {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) :
    cesAgg μ θ c ^ ((θ - 1) / θ) = ∫ i, c i ^ ((θ - 1) / θ) ∂μ :=
  Real.rpow_inv_rpow (integral_nonneg fun i => Real.rpow_nonneg (hc i) _)
    (div_ne_zero (by linarith) (by linarith))

/-- Woodford (2003), Ch. 3 §1.1, pp. 146–147: the integrated Young bound. For a bundle with positive
aggregate `C`, `C^r ≤ r C^{−1/θ} (∫ P c)/P + (1/θ) C^r`. -/
theorem integrated_young (hθ : 1 < θ) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - θ)) μ) (hpos : 0 < ∫ i, P i ^ (1 - θ) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ)
    (hC : 0 < cesAgg μ θ c) :
    Integrable (fun i => (θ - 1) / θ * (cesAgg μ θ c ^ (-1 / θ) / priceIndex μ θ P) *
        (P i * c i) + 1 / θ * cesAgg μ θ c ^ ((θ - 1) / θ) *
          (P i / priceIndex μ θ P) ^ (1 - θ)) μ ∧
      (∀ i, c i ^ ((θ - 1) / θ) ≤ (θ - 1) / θ * (cesAgg μ θ c ^ (-1 / θ) / priceIndex μ θ P) *
        (P i * c i) + 1 / θ * cesAgg μ θ c ^ ((θ - 1) / θ) *
          (P i / priceIndex μ θ P) ^ (1 - θ)) ∧
      ∫ i, ((θ - 1) / θ * (cesAgg μ θ c ^ (-1 / θ) / priceIndex μ θ P) *
        (P i * c i) + 1 / θ * cesAgg μ θ c ^ ((θ - 1) / θ) *
          (P i / priceIndex μ θ P) ^ (1 - θ)) ∂μ
        = (θ - 1) / θ * (cesAgg μ θ c ^ (-1 / θ) / priceIndex μ θ P) *
          (∫ i, P i * c i ∂μ) + 1 / θ * cesAgg μ θ c ^ ((θ - 1) / θ) := by
  have hI := priceIndex_pos hpos
  have hint1 := hpc.const_mul ((θ - 1) / θ * (cesAgg μ θ c ^ (-1 / θ) / priceIndex μ θ P))
  have hint2 := (integrable_relPrice_rpow hPi hP hpos).const_mul
    (1 / θ * cesAgg μ θ c ^ ((θ - 1) / θ))
  refine ⟨hint1.add hint2, fun i => ?_, ?_⟩
  · have h := young_le hθ (div_pos (hP i) hI) (hc i) hC
    have e : (θ - 1) / θ * (cesAgg μ θ c ^ (-1 / θ) / priceIndex μ θ P) * (P i * c i)
        = (θ - 1) / θ * (P i / priceIndex μ θ P * c i * cesAgg μ θ c ^ (-1 / θ)) := by ring
    rw [e]
    linarith
  · rw [integral_add hint1 hint2, integral_const_mul, integral_const_mul,
      integral_relPrice_rpow hθ hP hpos, mul_one]

/-- Woodford (2003), eq. (1.3), p. 146 and text after it (**expenditure minimisation**): any
bundle `c(·) ≥ 0` costs at least `P · C`, where `C` is its CES aggregate. -/
theorem spend_ge (hθ : 1 < θ) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - θ)) μ) (hpos : 0 < ∫ i, P i ^ (1 - θ) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ) :
    priceIndex μ θ P * cesAgg μ θ c ≤ ∫ i, P i * c i ∂μ := by
  have hI := priceIndex_pos hpos
  have hθ0 : (0 : ℝ) < θ := by linarith
  have hS : 0 ≤ ∫ i, P i * c i ∂μ := integral_nonneg fun i => mul_nonneg (hP i).le (hc i)
  rcases (cesAgg_nonneg (μ := μ) (θ := θ) hc).eq_or_lt with h0 | hC
  · rw [← h0, mul_zero]; exact hS
  obtain ⟨hint, hle, hval⟩ := integrated_young hθ hP hPi hpos hc hpc hC
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun i => Real.rpow_nonneg (hc i) ((θ - 1) / θ)) hint
    (Filter.Eventually.of_forall hle)
  rw [hval, ← cesAgg_rpow hθ hc] at hmono
  set C := cesAgg μ θ c
  set S := ∫ i, P i * c i ∂μ
  have hK : 0 < C ^ (-1 / θ) := Real.rpow_pos_of_pos hC _
  have hCr : C ^ ((θ - 1) / θ) = C * C ^ (-1 / θ) := by
    have : (θ - 1) / θ = 1 + -1 / θ := by field_simp; ring
    rw [this, Real.rpow_add hC, Real.rpow_one]
  rw [hCr] at hmono
  have hr : 0 < (θ - 1) / θ := div_pos (by linarith) hθ0
  have h1 : (θ - 1) / θ * (C * C ^ (-1 / θ)) ≤
      (θ - 1) / θ * (C ^ (-1 / θ) * (S / priceIndex μ θ P)) := by
    have e : 1 / θ = 1 - (θ - 1) / θ := by field_simp; ring
    rw [e] at hmono
    have e2 : (θ - 1) / θ * (C ^ (-1 / θ) / priceIndex μ θ P) * S
        = (θ - 1) / θ * (C ^ (-1 / θ) * (S / priceIndex μ θ P)) := by ring
    rw [e2] at hmono
    linarith
  have h2 := le_of_mul_le_mul_left h1 hr
  rw [mul_comm C] at h2
  have h3 := le_of_mul_le_mul_left h2 hK
  rw [le_div_iff₀ hI] at h3
  linarith

/-- Woodford (2003), eq. (1.5), p. 147: a bundle costs exactly `P · C` (its
aggregate `C`) **if and only if** it is the demand schedule `c(i) = (p(i)/P)^{−θ} C`
almost everywhere. -/
theorem spend_eq_iff (hθ : 1 < θ) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - θ)) μ) (hpos : 0 < ∫ i, P i ^ (1 - θ) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ) :
    ∫ i, P i * c i ∂μ = priceIndex μ θ P * cesAgg μ θ c ↔
      c =ᵐ[μ] demand μ θ P (cesAgg μ θ c) := by
  have hI := priceIndex_pos hpos
  have hθ0 : (0 : ℝ) < θ := by linarith
  constructor
  swap
  · intro h
    rw [← spend_demand hθ hP hpos (cesAgg μ θ c)]
    refine integral_congr_ae ?_
    filter_upwards [h] with i hi
    rw [hi]
  intro heq
  rcases (cesAgg_nonneg (μ := μ) (θ := θ) hc).eq_or_lt with h0 | hC
  · rw [← h0, mul_zero] at heq
    have hz := (integral_eq_zero_iff_of_nonneg
      (fun i => mul_nonneg (hP i).le (hc i)) hpc).1 heq
    filter_upwards [hz] with i hi
    rw [← h0, demand, mul_zero]
    simp only [Pi.zero_apply] at hi
    rcases mul_eq_zero.1 hi with h | h
    · exact absurd h (hP i).ne'
    · exact h
  obtain ⟨hint, hle, hval⟩ := integrated_young hθ hP hPi hpos hc hpc hC
  set C := cesAgg μ θ c
  have hcr : Integrable (fun i => c i ^ ((θ - 1) / θ)) μ := by
    refine Integrable.of_integral_ne_zero ?_
    rw [← cesAgg_rpow hθ hc]
    exact (Real.rpow_pos_of_pos hC _).ne'
  have hdiff := (integral_eq_zero_iff_of_nonneg
    (fun i => sub_nonneg.2 (hle i)) (hint.sub hcr)).1 (by
      rw [integral_sub hint hcr, hval, ← cesAgg_rpow hθ hc, heq]
      have hCr : C ^ ((θ - 1) / θ) = C * C ^ (-1 / θ) := by
        have : (θ - 1) / θ = 1 + -1 / θ := by field_simp; ring
        rw [this, Real.rpow_add hC, Real.rpow_one]
      rw [hCr]
      field_simp
      ring)
  filter_upwards [hdiff] with i hi
  simp only [Pi.zero_apply, sub_eq_zero] at hi
  have := (young_eq_iff hθ (div_pos (hP i) hI) (hc i) hC).1 (by
    rw [← hi]
    ring)
  rw [this, demand]

/-- Woodford (2003), Ch. 3 §1.1, pp. 146–147 (dual form): for a bundle with expenditure
`∫ p(i) c(i) = X`, the attainable consumption index is at most `X / P`. -/
theorem cesAgg_le_of_spend (hθ : 1 < θ) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - θ)) μ) (hpos : 0 < ∫ i, P i ^ (1 - θ) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ) {X : ℝ}
    (hX : ∫ i, P i * c i ∂μ = X) : cesAgg μ θ c ≤ X / priceIndex μ θ P := by
  rw [le_div_iff₀ (priceIndex_pos hpos), mul_comm, ← hX]
  exact spend_ge hθ hP hPi hpos hc hpc

/-- Woodford (2003), Ch. 3 §1.1, pp. 146–147 (dual form, equality): with expenditure `X`, the index
attains `X / P` iff `c(i) = (p(i)/P)^{−θ} X/P` almost everywhere. -/
theorem cesAgg_eq_iff_of_spend (hθ : 1 < θ) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - θ)) μ) (hpos : 0 < ∫ i, P i ^ (1 - θ) ∂μ)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ) {X : ℝ}
    (hX : ∫ i, P i * c i ∂μ = X) :
    cesAgg μ θ c = X / priceIndex μ θ P ↔
      c =ᵐ[μ] demand μ θ P (X / priceIndex μ θ P) := by
  have hI := priceIndex_pos hpos
  constructor
  · intro h
    rw [← h]
    refine (spend_eq_iff hθ hP hPi hpos hc hpc).1 ?_
    rw [h, hX]
    field_simp
  · intro h
    have hX0 : 0 ≤ X / priceIndex μ θ P := by
      rw [← hX]
      exact div_nonneg (integral_nonneg fun i => mul_nonneg (hP i).le (hc i)) hI.le
    have hagg : cesAgg μ θ c = cesAgg μ θ (demand μ θ P (X / priceIndex μ θ P)) := by
      unfold cesAgg
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [h] with i hi
      rw [hi]
    rw [hagg, cesAgg_demand hθ hP hpos hX0]

/-- Woodford (2003), p. 147, n. 5, and eq. (1.12), p. 151: goods-market clearing `y(i) = c(i)`
for all `i`, with households on their demand schedule, gives `Y = C` for the CES output index and
`y(i) = (p(i)/P)^{−θ} Y`. -/
theorem market_clearing (hθ : 1 < θ) (hP : ∀ i, 0 < P i)
    (hpos : 0 < ∫ i, P i ^ (1 - θ) ∂μ) {C : ℝ} (hC : 0 ≤ C) {Y : G → ℝ}
    (hclear : ∀ i, Y i = demand μ θ P C i) :
    cesAgg μ θ Y = C ∧ ∀ i, Y i = demand μ θ P (cesAgg μ θ Y) i := by
  have hY : Y = demand μ θ P C := funext hclear
  have hagg : cesAgg μ θ Y = C := by rw [hY, cesAgg_demand hθ hP hpos hC]
  exact ⟨hagg, fun i => by rw [hagg, hclear]⟩

/-- Woodford (2003), p. 147: a positive integrable function has positive integral against a
nonzero measure (used to see that `∫ p(i)^{1−θ} > 0`). -/
theorem integral_pos_of_pos {f : G → ℝ} (hμ : μ ≠ 0) (hf : ∀ i, 0 < f i)
    (hfi : Integrable f μ) : 0 < ∫ i, f i ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun i => (hf i).le) hfi]
  have : Function.support f = Set.univ :=
    Set.eq_univ_of_forall fun i => (hf i).ne'
  rw [this]
  exact Measure.measure_univ_pos.2 hμ

/-- Woodford (2003), p. 147: Lebesgue measure on the goods continuum `[0, 1]` is nonzero. -/
theorem unitInterval_ne_zero : (volume.restrict (Set.Icc (0 : ℝ) 1)) ≠ 0 := by
  rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc]
  simp

/-- Woodford (2003), eqs. (1.2)–(1.5), pp. 146–147, on the book's **continuum of goods
`[0, 1]` with Lebesgue measure**: (i) every bundle `c(·) ≥ 0` costs at least `P · C`;
(ii) it costs exactly `P · C` iff `c(i) = (p(i)/P)^{−θ} C` for a.e. `i ∈ [0, 1]`;
(iii) the demand schedule attains any aggregate `C ≥ 0`; (iv) it costs `P C`. -/
theorem unitInterval_expenditure_minimisation (hθ : 1 < θ) {Q : ℝ → ℝ} (hQ : ∀ i, 0 < Q i)
    (hQi : IntegrableOn (fun i => Q i ^ (1 - θ)) (Set.Icc 0 1)) {c : ℝ → ℝ}
    (hc : ∀ i, 0 ≤ c i) (hQc : IntegrableOn (fun i => Q i * c i) (Set.Icc 0 1)) :
    priceIndex (volume.restrict (Set.Icc 0 1)) θ Q * cesAgg (volume.restrict (Set.Icc 0 1)) θ c
        ≤ ∫ i in Set.Icc 0 1, Q i * c i ∧
      (∫ i in Set.Icc 0 1, Q i * c i
          = priceIndex (volume.restrict (Set.Icc 0 1)) θ Q *
            cesAgg (volume.restrict (Set.Icc 0 1)) θ c ↔
        ∀ᵐ i ∂(volume.restrict (Set.Icc 0 1)),
          c i = demand (volume.restrict (Set.Icc 0 1)) θ Q
            (cesAgg (volume.restrict (Set.Icc 0 1)) θ c) i) ∧
      (∀ C : ℝ, 0 ≤ C → cesAgg (volume.restrict (Set.Icc 0 1)) θ
        (demand (volume.restrict (Set.Icc 0 1)) θ Q C) = C) ∧
      ∀ C : ℝ, ∫ i in Set.Icc 0 1, Q i * demand (volume.restrict (Set.Icc 0 1)) θ Q C i
        = priceIndex (volume.restrict (Set.Icc 0 1)) θ Q * C := by
  have hpos := integral_pos_of_pos unitInterval_ne_zero (fun i => Real.rpow_pos_of_pos (hQ i) _)
    hQi
  exact ⟨spend_ge hθ hQ hQi hpos hc hQc, spend_eq_iff hθ hQ hQi hpos hc hQc,
    fun C hC => cesAgg_demand hθ hQ hpos hC, spend_demand hθ hQ hpos⟩

namespace Finite

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Woodford (2003), p. 147 (finitely many goods): the measure placing weight `w i` on good `i`,
a discretisation of `[0, 1]` (e.g. `w i = 1/n`). -/
noncomputable def weightMeasure (w : ι → ℝ) : Measure ι :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac i

/-- Woodford (2003), p. 146: the weighted measure gives good `x` mass `w x`. -/
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
/-- Woodford (2003), p. 146: the weighted measure is finite. -/
theorem weightMeasure_univ_lt_top {w : ι → ℝ} : weightMeasure w Set.univ < ⊤ := by
  rw [weightMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact ENNReal.sum_lt_top.2 fun i _ => ENNReal.ofReal_lt_top

/-- Woodford (2003), p. 146: every function is integrable for the weighted measure. -/
theorem integrable_weightMeasure {w : ι → ℝ} (f : ι → ℝ) : Integrable f (weightMeasure w) := by
  have : IsFiniteMeasure (weightMeasure w) := ⟨weightMeasure_univ_lt_top⟩
  exact Integrable.of_finite

/-- Woodford (2003), p. 146: integrals against the weighted measure are weighted sums,
`∫ f = ∑ᵢ w i f i`. -/
theorem integral_weightMeasure {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (f : ι → ℝ) :
    ∫ i, f i ∂(weightMeasure w) = ∑ i, w i * f i := by
  rw [integral_fintype (integrable_weightMeasure f)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.real, weightMeasure_singleton, ENNReal.toReal_ofReal (hw i), smul_eq_mul]

/-- Woodford (2003), eqs. (1.2)–(1.5), pp. 146–147, for **finitely many goods** with weights
`w i > 0`. With `P = (∑ w p(i)^{1−θ})^{1/(1−θ)}` and `C = (∑ w c(i)^r)^{1/r}`:
(i) `∑ w p(i) c(i) ≥ P C`; (ii) equality iff `c(i) = (p(i)/P)^{−θ} C` for **every** `i`;
(iii) the demand schedule attains any `C ≥ 0`; (iv) it costs exactly `P C`. -/
theorem finite_expenditure_minimisation [Nonempty ι] (hθ : 1 < θ) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) {Q : ι → ℝ} (hQ : ∀ i, 0 < Q i) {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) :
    (∑ i, w i * Q i ^ (1 - θ)) ^ (1 - θ)⁻¹ * (∑ i, w i * c i ^ ((θ - 1) / θ)) ^ ((θ - 1) / θ)⁻¹
        ≤ ∑ i, w i * (Q i * c i) ∧
      (∑ i, w i * (Q i * c i) = (∑ i, w i * Q i ^ (1 - θ)) ^ (1 - θ)⁻¹ *
          (∑ i, w i * c i ^ ((θ - 1) / θ)) ^ ((θ - 1) / θ)⁻¹ ↔
        ∀ i, c i = (Q i / (∑ j, w j * Q j ^ (1 - θ)) ^ (1 - θ)⁻¹) ^ (-θ) *
          (∑ j, w j * c j ^ ((θ - 1) / θ)) ^ ((θ - 1) / θ)⁻¹) ∧
      (∀ C : ℝ, 0 ≤ C → (∑ i, w i *
        ((Q i / (∑ j, w j * Q j ^ (1 - θ)) ^ (1 - θ)⁻¹) ^ (-θ) * C) ^ ((θ - 1) / θ)) ^
          ((θ - 1) / θ)⁻¹ = C) ∧
      ∀ C : ℝ, ∑ i, w i * (Q i * ((Q i / (∑ j, w j * Q j ^ (1 - θ)) ^ (1 - θ)⁻¹) ^ (-θ) * C))
        = (∑ j, w j * Q j ^ (1 - θ)) ^ (1 - θ)⁻¹ * C := by
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hw i).le
  have hμ : weightMeasure w ≠ 0 := by
    intro h
    obtain ⟨x⟩ := ‹Nonempty ι›
    have := weightMeasure_singleton (w := w) x
    rw [h, Measure.coe_zero, Pi.zero_apply] at this
    exact (ENNReal.ofReal_pos.2 (hw x)).ne' this.symm
  have hpos := integral_pos_of_pos hμ (fun i => Real.rpow_pos_of_pos (hQ i) (1 - θ))
    (integrable_weightMeasure _)
  have hPI : priceIndex (weightMeasure w) θ Q = (∑ j, w j * Q j ^ (1 - θ)) ^ (1 - θ)⁻¹ := by
    rw [priceIndex, integral_weightMeasure hw0]
  have hCA : ∀ d : ι → ℝ, cesAgg (weightMeasure w) θ d
      = (∑ j, w j * d j ^ ((θ - 1) / θ)) ^ ((θ - 1) / θ)⁻¹ := by
    intro d
    rw [cesAgg, integral_weightMeasure hw0]
  have hD : ∀ C i, demand (weightMeasure w) θ Q C i
      = (Q i / (∑ j, w j * Q j ^ (1 - θ)) ^ (1 - θ)⁻¹) ^ (-θ) * C := by
    intro C i
    rw [demand, hPI]
  have h1 := spend_ge hθ hQ (integrable_weightMeasure _) hpos hc (integrable_weightMeasure _)
  have h2 := spend_eq_iff hθ hQ (integrable_weightMeasure _) hpos hc (integrable_weightMeasure _)
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
    have := cesAgg_demand hθ hQ hpos hC (μ := weightMeasure w)
    rw [hCA] at this
    simpa only [hD] using this
  · intro C
    have := spend_demand hθ hQ hpos C (μ := weightMeasure w)
    rw [integral_weightMeasure hw0, hPI] at this
    simpa only [hD] using this

end Finite


/-! ### The price index as the minimal cost of the aggregate -/

/-- Woodford (2003), p. 146: the cost of attaining at least `C` units of the aggregate (1.2):
the set of expenditures `∫ p(i) c(i) di` over all bundles `c ≥ 0` with index `≥ C`. -/
def costSet (μ : Measure G) (θ : ℝ) (P : G → ℝ) (C : ℝ) : Set ℝ :=
  {X | ∃ c : G → ℝ, (∀ i, 0 ≤ c i) ∧ Integrable (fun i => P i * c i) μ ∧
    C ≤ cesAgg μ θ c ∧ X = ∫ i, P i * c i ∂μ}

/-- Woodford (2003), eq. (1.5), p. 147: the demand bundle is nonnegative. -/
theorem demand_nonneg (hP : ∀ i, 0 < P i) (hpos : 0 < ∫ i, P i ^ (1 - θ) ∂μ) {C : ℝ}
    (hC : 0 ≤ C) (i : G) : 0 ≤ demand μ θ P C i :=
  mul_nonneg (Real.rpow_nonneg (div_pos (hP i) (priceIndex_pos hpos)).le _) hC

/-- Woodford (2003), eq. (1.5), p. 147: expenditure on the demand bundle is integrable. -/
theorem integrable_spend_demand (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - θ)) μ) (hpos : 0 < ∫ i, P i ^ (1 - θ) ∂μ)
    (C : ℝ) : Integrable (fun i => P i * demand μ θ P C i) μ := by
  have h : (fun i => P i * demand μ θ P C i)
      = fun i => priceIndex μ θ P * C * (P i / priceIndex μ θ P) ^ (1 - θ) :=
    funext (price_mul_demand hP hpos C)
  rw [h]
  exact (integrable_relPrice_rpow hPi hP hpos).const_mul _

/-- Woodford (2003), p. 146, text after (1.3): **`P C` is the minimum cost of `C` units of the
aggregate.** It is attained (by the demand bundle (1.5)) and no feasible bundle costs less. -/
theorem cost_isLeast (hθ : 1 < θ) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - θ)) μ) (hpos : 0 < ∫ i, P i ^ (1 - θ) ∂μ) {C : ℝ}
    (hC : 0 ≤ C) : IsLeast (costSet μ θ P C) (priceIndex μ θ P * C) := by
  refine ⟨⟨demand μ θ P C, demand_nonneg hP hpos hC, integrable_spend_demand hP hPi hpos C,
    (cesAgg_demand hθ hP hpos hC).ge, (spend_demand hθ hP hpos C).symm⟩, ?_⟩
  rintro X ⟨c, hc, hpc, hCc, rfl⟩
  exact (mul_le_mul_of_nonneg_left hCc (priceIndex_pos hpos).le).trans
    (spend_ge hθ hP hPi hpos hc hpc)

/-- Woodford (2003), p. 146 (uniqueness of the cost minimiser): any bundle that attains at least
`C` units of the aggregate at cost at most `P C` coincides a.e. with the demand bundle (1.5). -/
theorem cost_minimiser_unique (hθ : 1 < θ) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - θ)) μ) (hpos : 0 < ∫ i, P i ^ (1 - θ) ∂μ) {C : ℝ}
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) (hpc : Integrable (fun i => P i * c i) μ)
    (hCc : C ≤ cesAgg μ θ c) (hmin : ∫ i, P i * c i ∂μ ≤ priceIndex μ θ P * C) :
    c =ᵐ[μ] demand μ θ P C := by
  have hI := priceIndex_pos hpos
  have h1 := spend_ge hθ hP hPi hpos hc hpc
  have hle : cesAgg μ θ c ≤ C := le_of_mul_le_mul_left (h1.trans hmin) hI
  have hagg : cesAgg μ θ c = C := le_antisymm hle hCc
  have heq : ∫ i, P i * c i ∂μ = priceIndex μ θ P * cesAgg μ θ c := by
    rw [hagg]
    exact le_antisymm hmin (by rw [← hagg]; exact h1)
  have := (spend_eq_iff hθ hP hPi hpos hc hpc).1 heq
  rwa [hagg] at this

/-- Woodford (2003), p. 146, text after (1.3): **the index (1.3) is the minimum cost of a unit of
the aggregate (1.2)**, attained exactly by the demand bundle `c(i) = (p(i)/P)^{−θ}`. -/
theorem priceIndex_isLeast_unitCost (hθ : 1 < θ) (hP : ∀ i, 0 < P i)
    (hPi : Integrable (fun i => P i ^ (1 - θ)) μ) (hpos : 0 < ∫ i, P i ^ (1 - θ) ∂μ) :
    IsLeast (costSet μ θ P 1) (priceIndex μ θ P) := by
  simpa using cost_isLeast hθ hP hPi hpos zero_le_one

/-- Woodford (2003), p. 200 (normalisation): with a common price `p̄` for every good and a
probability measure of goods, the index (1.3) equals `p̄`. -/
theorem priceIndex_const [IsProbabilityMeasure μ] (hθ : 1 < θ) {pbar : ℝ} (hp : 0 < pbar) :
    priceIndex μ θ (fun _ => pbar) = pbar := by
  unfold priceIndex
  simp only [integral_const, probReal_univ, one_smul]
  exact Real.rpow_rpow_inv hp.le (by linarith)

/-- Woodford (2003), p. 151 (symmetric allocation): with a probability measure of goods, the
index (1.2) of a constant bundle `c(i) = c̄` is `c̄`. -/
theorem cesAgg_const [IsProbabilityMeasure μ] (hθ : 1 < θ) {cbar : ℝ} (hc : 0 ≤ cbar) :
    cesAgg μ θ (fun _ => cbar) = cbar := by
  unfold cesAgg
  simp only [integral_const, probReal_univ, one_smul]
  exact Real.rpow_rpow_inv hc (div_ne_zero (by linarith) (by linarith))

/-! ### Finitely many composites: CES with any elasticity `η > 0`, `η ≠ 1`

The upper level (2.22) of the two-sector model has an elasticity `η > 0` that may be below one
(footnote 61, p. 201). For `0 < η < 1` the exponent `(η − 1)/η` is negative and the Young
inequality above is replaced by a weighted AM–GM inequality with weights `1 − η` and `η`. -/

/-- Woodford (2003), p. 201: the finite CES price index `(∑ a_j q_j^{1−η})^{1/(1−η)}`. -/
noncomputable def finPriceIndex {ι : Type*} [Fintype ι] (a q : ι → ℝ) (η : ℝ) : ℝ :=
  (∑ j, a j * q j ^ (1 - η)) ^ (1 / (1 - η))

/-- Woodford (2003), p. 201: the finite CES aggregate `(∑ a_j x_j^{(η−1)/η})^{η/(η−1)}`. -/
noncomputable def finAgg {ι : Type*} [Fintype ι] (a x : ι → ℝ) (η : ℝ) : ℝ :=
  (∑ j, a j * x j ^ ((η - 1) / η)) ^ (η / (η - 1))

/-- Woodford (2003), p. 201, n. 61 (`0 < η < 1`): the pointwise AM–GM bound
`b^{1−η} ≤ (1 − η) b z + η z^{(η−1)/η}` for a relative price `b > 0` and a relative quantity
`z > 0`. -/
theorem amgm_lt_one {η b z : ℝ} (h0 : 0 < η) (h1 : η < 1) (hb : 0 < b) (hz : 0 < z) :
    b ^ (1 - η) ≤ (1 - η) * (b * z) + η * z ^ ((η - 1) / η) := by
  have key : (b * z) ^ (1 - η) * (z ^ ((η - 1) / η)) ^ η = b ^ (1 - η) := by
    rw [Real.mul_rpow hb.le hz.le, ← Real.rpow_mul hz.le, mul_assoc, ← Real.rpow_add hz]
    have : 1 - η + (η - 1) / η * η = 0 := by field_simp; ring
    rw [this, Real.rpow_zero, mul_one]
  rw [← key]
  exact Real.geom_mean_le_arith_mean2_weighted (by linarith) h0.le (by positivity)
    (by positivity) (by ring)

/-- Woodford (2003), p. 201, n. 61 (`0 < η < 1`): equality in `amgm_lt_one` holds iff
`z = b^{−η}`, i.e. iff the composite is on its demand schedule. -/
theorem amgm_lt_one_eq_iff {η b z : ℝ} (h0 : 0 < η) (h1 : η < 1) (hb : 0 < b) (hz : 0 < z) :
    b ^ (1 - η) = (1 - η) * (b * z) + η * z ^ ((η - 1) / η) ↔ z = b ^ (-η) := by
  have key : (b * z) ^ (1 - η) * (z ^ ((η - 1) / η)) ^ η = b ^ (1 - η) := by
    rw [Real.mul_rpow hb.le hz.le, ← Real.rpow_mul hz.le, mul_assoc, ← Real.rpow_add hz]
    have : 1 - η + (η - 1) / η * η = 0 := by field_simp; ring
    rw [this, Real.rpow_zero, mul_one]
  rw [← key, Real.geom_mean_eq_arith_mean2_weighted_iff_of_pos (by linarith) h0 (by positivity)
    (by positivity) (by ring)]
  have hz' : z ^ ((η - 1) / η) = z * z ^ (-1 / η) := by
    have : (η - 1) / η = 1 + -1 / η := by field_simp; ring
    rw [this, Real.rpow_add hz, Real.rpow_one]
  rw [hz', mul_comm b z, mul_right_inj' hz.ne']
  constructor
  · intro h
    rw [h, ← Real.rpow_mul hz.le]
    have : -1 / η * -η = 1 := by field_simp
    rw [this, Real.rpow_one]
  · intro h
    rw [h, ← Real.rpow_mul hb.le]
    have : -η * (-1 / η) = 1 := by field_simp
    rw [this, Real.rpow_one]

/-- Woodford (2003), p. 146 (`η > 1`): the Young bound of `young_le` in relative variables,
`z^{(η−1)/η} ≤ ((η−1)/η) b z + (1/η) b^{1−η}`, with equality iff `z = b^{−η}`. -/
theorem young_rel {η b z : ℝ} (h1 : 1 < η) (hb : 0 < b) (hz : 0 ≤ z) :
    z ^ ((η - 1) / η) ≤ (η - 1) / η * (b * z) + 1 / η * b ^ (1 - η) ∧
      (z ^ ((η - 1) / η) = (η - 1) / η * (b * z) + 1 / η * b ^ (1 - η) ↔ z = b ^ (-η)) := by
  have h := young_le h1 hb hz one_pos
  have he := young_eq_iff h1 hb hz one_pos
  simp only [Real.one_rpow, mul_one] at h he
  exact ⟨h, he⟩

/-- Woodford (2003), p. 201: the gap representation behind finite CES duality, for any
`η > 0`, `η ≠ 1`. With `P` the finite index, `X` the finite aggregate, `b_j = q_j/P` and
`z_j = x_j/X`, there are a constant `κ > 0` and gaps `g_j ≥ 0`, vanishing exactly on the demand
schedule `x_j = (q_j/P)^{−η} X`, with `∑ a_j g_j = κ (∑ a_j b_j z_j − 1)`. -/
theorem fin_gap {ι : Type*} [Fintype ι] {η : ℝ} (h0 : 0 < η) (h1 : η ≠ 1) {a q x : ι → ℝ}
    (hq : ∀ j, 0 < q j) (hx : ∀ j, 0 < x j)
    (hS : 0 < ∑ j, a j * q j ^ (1 - η)) (hT : 0 < ∑ j, a j * x j ^ ((η - 1) / η)) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ g : ι → ℝ, (∀ j, 0 ≤ g j) ∧
      (∀ j, g j = 0 ↔ x j = (q j / finPriceIndex a q η) ^ (-η) * finAgg a x η) ∧
      ∑ j, a j * g j = κ * (∑ j, a j * (q j / finPriceIndex a q η * (x j / finAgg a x η)) - 1) := by
  set P := finPriceIndex a q η with hPdef
  set X := finAgg a x η with hXdef
  have hP : 0 < P := Real.rpow_pos_of_pos hS _
  have hX : 0 < X := Real.rpow_pos_of_pos hT _
  have hη1 : 1 - η ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  have hr : (η - 1) / η ≠ 0 := div_ne_zero (sub_ne_zero.2 h1) h0.ne'
  have hPr : P ^ (1 - η) = ∑ j, a j * q j ^ (1 - η) := by
    rw [hPdef, finPriceIndex, one_div]
    exact Real.rpow_inv_rpow hS.le hη1
  have hXr : X ^ ((η - 1) / η) = ∑ j, a j * x j ^ ((η - 1) / η) := by
    rw [hXdef, finAgg, show η / (η - 1) = ((η - 1) / η)⁻¹ from (inv_div _ _).symm]
    exact Real.rpow_inv_rpow hT.le hr
  have hsumb : ∑ j, a j * (q j / P) ^ (1 - η) = 1 := by
    simp_rw [Real.div_rpow (hq _).le hP.le, mul_div_assoc', ← Finset.sum_div, hPr]
    exact div_self hS.ne'
  have hsumz : ∑ j, a j * (x j / X) ^ ((η - 1) / η) = 1 := by
    simp_rw [Real.div_rpow (hx _).le hX.le, mul_div_assoc', ← Finset.sum_div, hXr]
    exact div_self hT.ne'
  have hzeq : ∀ j, (x j / X = (q j / P) ^ (-η)) ↔ x j = (q j / P) ^ (-η) * X := fun j =>
    div_eq_iff hX.ne'
  rcases lt_or_gt_of_ne h1 with hlt | hgt
  · refine ⟨1 - η, by linarith,
      fun j => (1 - η) * (q j / P * (x j / X)) + η * (x j / X) ^ ((η - 1) / η)
        - (q j / P) ^ (1 - η), fun j => ?_, fun j => ?_, ?_⟩
    · exact sub_nonneg.2 (amgm_lt_one h0 hlt (div_pos (hq j) hP) (div_pos (hx j) hX))
    · rw [sub_eq_zero, eq_comm, amgm_lt_one_eq_iff h0 hlt (div_pos (hq j) hP)
        (div_pos (hx j) hX), hzeq]
    · simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, hsumb]
      have e1 : ∑ j, a j * ((1 - η) * (q j / P * (x j / X)))
          = (1 - η) * ∑ j, a j * (q j / P * (x j / X)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      have e2 : ∑ j, a j * (η * (x j / X) ^ ((η - 1) / η)) = η := by
        have : ∑ j, a j * (η * (x j / X) ^ ((η - 1) / η))
            = η * ∑ j, a j * (x j / X) ^ ((η - 1) / η) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        rw [this, hsumz, mul_one]
      rw [e1, e2]
      ring
  · refine ⟨(η - 1) / η, div_pos (by linarith) h0,
      fun j => (η - 1) / η * (q j / P * (x j / X)) + 1 / η * (q j / P) ^ (1 - η)
        - (x j / X) ^ ((η - 1) / η), fun j => ?_, fun j => ?_, ?_⟩
    · exact sub_nonneg.2 (young_rel hgt (div_pos (hq j) hP) (div_pos (hx j) hX).le).1
    · rw [sub_eq_zero, eq_comm, (young_rel hgt (div_pos (hq j) hP) (div_pos (hx j) hX).le).2,
        hzeq]
    · simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, hsumz]
      have e1 : ∑ j, a j * ((η - 1) / η * (q j / P * (x j / X)))
          = (η - 1) / η * ∑ j, a j * (q j / P * (x j / X)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      have e2 : ∑ j, a j * (1 / η * (q j / P) ^ (1 - η)) = 1 / η := by
        have : ∑ j, a j * (1 / η * (q j / P) ^ (1 - η))
            = 1 / η * ∑ j, a j * (q j / P) ^ (1 - η) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        rw [this, hsumb, mul_one]
      rw [e1, e2]
      field_simp
      ring

/-- Woodford (2003), p. 201: the normalised expenditure identity
`∑ a_j q_j x_j = P X ∑ a_j (q_j/P)(x_j/X)`. -/
theorem fin_spend_rel {ι : Type*} [Fintype ι] {a q x : ι → ℝ} {P X : ℝ} (hP : 0 < P)
    (hX : 0 < X) : ∑ j, a j * (q j * x j) = P * X * ∑ j, a j * (q j / P * (x j / X)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp

/-- Woodford (2003), p. 201 (**finite CES duality, any `η > 0`, `η ≠ 1`**): for positive
weights, prices and quantities, total expenditure `∑ a_j q_j x_j` is at least `P X`, with
equality **iff** `x_j = (q_j/P)^{−η} X` for every `j`. -/
theorem fin_cost_ge_and_eq_iff {ι : Type*} [Fintype ι] [Nonempty ι] {η : ℝ} (h0 : 0 < η)
    (h1 : η ≠ 1) {a q x : ι → ℝ} (ha : ∀ j, 0 < a j) (hq : ∀ j, 0 < q j)
    (hx : ∀ j, 0 < x j) :
    finPriceIndex a q η * finAgg a x η ≤ ∑ j, a j * (q j * x j) ∧
      (∑ j, a j * (q j * x j) = finPriceIndex a q η * finAgg a x η ↔
        ∀ j, x j = (q j / finPriceIndex a q η) ^ (-η) * finAgg a x η) := by
  have hS : 0 < ∑ j, a j * q j ^ (1 - η) :=
    Finset.sum_pos (fun j _ => mul_pos (ha j) (Real.rpow_pos_of_pos (hq j) _))
      Finset.univ_nonempty
  have hT : 0 < ∑ j, a j * x j ^ ((η - 1) / η) :=
    Finset.sum_pos (fun j _ => mul_pos (ha j) (Real.rpow_pos_of_pos (hx j) _))
      Finset.univ_nonempty
  have hP : 0 < finPriceIndex a q η := Real.rpow_pos_of_pos hS _
  have hX : 0 < finAgg a x η := Real.rpow_pos_of_pos hT _
  obtain ⟨κ, hκ, g, hg0, hgeq, hgsum⟩ := fin_gap h0 h1 hq hx hS hT
  have hsum0 : 0 ≤ ∑ j, a j * g j := Finset.sum_nonneg fun j _ => mul_nonneg (ha j).le (hg0 j)
  rw [fin_spend_rel hP hX]
  set B := ∑ j, a j * (q j / finPriceIndex a q η * (x j / finAgg a x η))
  have hB : 1 ≤ B := by
    have : 0 ≤ κ * (B - 1) := hgsum ▸ hsum0
    have := (mul_nonneg_iff_of_pos_left hκ).1 this
    linarith
  have hPX : 0 < finPriceIndex a q η * finAgg a x η := mul_pos hP hX
  refine ⟨le_mul_of_one_le_right hPX.le hB, ?_⟩
  constructor
  · intro heq
    have hB1 : B = 1 := by
      have := heq
      nth_rewrite 2 [← mul_one (finPriceIndex a q η * finAgg a x η)] at this
      exact mul_left_cancel₀ hPX.ne' this
    have hz : ∑ j, a j * g j = 0 := by rw [hgsum, hB1, sub_self, mul_zero]
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (ha j).le (hg0 j))).1 hz
    intro j
    have := hall j (Finset.mem_univ j)
    exact (hgeq j).1 ((mul_eq_zero.1 this).resolve_left (ha j).ne')
  · intro hd
    have hz : ∑ j, a j * g j = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [(hgeq j).2 (hd j), mul_zero]
    rw [hgsum] at hz
    have hB1 : B = 1 := by
      rcases mul_eq_zero.1 hz with h | h
      · exact absurd h hκ.ne'
      · linarith
    rw [hB1, mul_one]

/-- Woodford (2003), p. 201: the demand schedule `x_j = (q_j/P)^{−η} X̄` attains the aggregate
`X̄ > 0` and costs exactly `P X̄` (any `η > 0`, `η ≠ 1`). -/
theorem fin_demand_attains {ι : Type*} [Fintype ι] [Nonempty ι] {η : ℝ} (h0 : 0 < η)
    (h1 : η ≠ 1) {a q : ι → ℝ} (ha : ∀ j, 0 < a j) (hq : ∀ j, 0 < q j) {Xbar : ℝ}
    (hXb : 0 < Xbar) :
    finAgg a (fun j => (q j / finPriceIndex a q η) ^ (-η) * Xbar) η = Xbar ∧
      ∑ j, a j * (q j * ((q j / finPriceIndex a q η) ^ (-η) * Xbar))
        = finPriceIndex a q η * Xbar := by
  have hS : 0 < ∑ j, a j * q j ^ (1 - η) :=
    Finset.sum_pos (fun j _ => mul_pos (ha j) (Real.rpow_pos_of_pos (hq j) _))
      Finset.univ_nonempty
  set P := finPriceIndex a q η with hPdef
  have hP : 0 < P := Real.rpow_pos_of_pos hS _
  have hη1 : 1 - η ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  have hr : (η - 1) / η ≠ 0 := div_ne_zero (sub_ne_zero.2 h1) h0.ne'
  have hPr : P ^ (1 - η) = ∑ j, a j * q j ^ (1 - η) := by
    rw [hPdef, finPriceIndex, one_div]
    exact Real.rpow_inv_rpow hS.le hη1
  have hsumb : ∑ j, a j * (q j / P) ^ (1 - η) = 1 := by
    simp_rw [Real.div_rpow (hq _).le hP.le, mul_div_assoc', ← Finset.sum_div, hPr]
    exact div_self hS.ne'
  constructor
  · have hpt : ∀ j, ((q j / P) ^ (-η) * Xbar) ^ ((η - 1) / η)
        = Xbar ^ ((η - 1) / η) * (q j / P) ^ (1 - η) := by
      intro j
      have hb : 0 < q j / P := div_pos (hq j) hP
      rw [Real.mul_rpow (Real.rpow_nonneg hb.le _) hXb.le, ← Real.rpow_mul hb.le]
      have : -η * ((η - 1) / η) = 1 - η := by field_simp; ring
      rw [this, mul_comm]
    unfold finAgg
    simp_rw [hpt, mul_left_comm (a _), ← Finset.mul_sum, hsumb, mul_one]
    rw [show η / (η - 1) = ((η - 1) / η)⁻¹ from (inv_div _ _).symm]
    exact Real.rpow_rpow_inv hXb.le hr
  · have hpt : ∀ j, a j * (q j * ((q j / P) ^ (-η) * Xbar))
        = P * Xbar * (a j * (q j / P) ^ (1 - η)) := by
      intro j
      have hb : 0 < q j / P := div_pos (hq j) hP
      have h1' : (q j / P) ^ (1 - η) = q j / P * (q j / P) ^ (-η) := by
        rw [sub_eq_add_neg, Real.rpow_add hb, Real.rpow_one]
      rw [h1']
      field_simp
    simp_rw [hpt, ← Finset.mul_sum, hsumb, mul_one]

/-! ### The Cobb–Douglas case `η = 1` (Woodford (2003), p. 201, n. 61) -/

/-- Woodford (2003), p. 201, n. 61 (**Cobb–Douglas duality**, `η = 1`): with weights `a_j > 0`
summing to one, the index `∏ x_j^{a_j}` and the price index `∏ q_j^{a_j}` satisfy
`∑ a_j q_j x_j ≥ (∏ q_j^{a_j})(∏ x_j^{a_j})`, with equality iff
`x_j = (q_j/P)^{−1} X` for every `j`. -/
theorem cobbDouglas_cost_ge_and_eq_iff {ι : Type*} [Fintype ι] {a q x : ι → ℝ}
    (ha : ∀ j, 0 < a j) (hsum : ∑ j, a j = 1) (hq : ∀ j, 0 < q j) (hx : ∀ j, 0 < x j) :
    (∏ j, q j ^ a j) * (∏ j, x j ^ a j) ≤ ∑ j, a j * (q j * x j) ∧
      (∑ j, a j * (q j * x j) = (∏ j, q j ^ a j) * (∏ j, x j ^ a j) ↔
        ∀ j, x j = (q j / ∏ k, q k ^ a k) ^ (-1 : ℝ) * ∏ k, x k ^ a k) := by
  have hprod : ∏ j, (q j * x j) ^ a j = (∏ j, q j ^ a j) * (∏ j, x j ^ a j) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => Real.mul_rpow (hq j).le (hx j).le
  have hamgm := Real.geom_mean_le_arith_mean_weighted Finset.univ a (fun j => q j * x j)
    (fun j _ => (ha j).le) hsum (fun j _ => (mul_pos (hq j) (hx j)).le)
  have hiff := Real.geom_mean_eq_arith_mean_weighted_iff_of_pos' Finset.univ a
    (fun j => q j * x j) (fun j _ => ha j) hsum (fun j _ => (mul_pos (hq j) (hx j)).le)
  rw [hprod] at hamgm hiff
  have hPq : 0 < ∏ j, q j ^ a j := Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hq j) _
  refine ⟨hamgm, ?_⟩
  constructor
  · intro heq j
    have hj := (hiff.1 heq.symm) j (Finset.mem_univ j)
    rw [heq] at hj
    have hqj := (hq j).ne'
    rw [Real.rpow_neg_one, inv_div, div_mul_eq_mul_div, eq_div_iff hqj]
    linarith
  · intro h
    have hconst : ∀ j, q j * x j = (∏ k, q k ^ a k) * ∏ k, x k ^ a k := by
      intro j
      have hqj := (hq j).ne'
      rw [h j, Real.rpow_neg_one, inv_div]
      field_simp
    have hS : ∑ i, a i * (q i * x i) = (∏ k, q k ^ a k) * ∏ k, x k ^ a k := by
      simp_rw [hconst, ← Finset.sum_mul, hsum, one_mul]
    exact hS

/-! ### The two-sector (nested) aggregator (2.22)–(2.23), §3.2.5, pp. 200–201 -/

namespace Nested

variable {J : Type*}

/-- Woodford (2003), eq. (2.23), p. 201: the normalised sector measure `ν_j = n_j⁻¹ μ|N_j`
(the goods of sector `j` with total weight one). -/
noncomputable def sectorMeasure (μ : Measure G) (N : J → Set G) (n : J → ℝ) (j : J) :
    Measure G :=
  ENNReal.ofReal (n j)⁻¹ • μ.restrict (N j)

/-- Woodford (2003), p. 200: the sectoral index
`C_j = (∫_{N_j} n_j^{−1/θ} c(i)^{(θ−1)/θ} di)^{θ/(θ−1)}`. -/
noncomputable def sectorIndex (μ : Measure G) (N : J → Set G) (n : J → ℝ) (θ : ℝ)
    (c : G → ℝ) (j : J) : ℝ :=
  (∫ i in N j, n j ^ (-1 / θ) * c i ^ ((θ - 1) / θ) ∂μ) ^ (θ / (θ - 1))

/-- Woodford (2003), eq. (2.23), p. 201: the sectoral price index
`P_j = (n_j⁻¹ ∫_{N_j} p(i)^{1−θ} di)^{1/(1−θ)}`. -/
noncomputable def sectorPrice (μ : Measure G) (N : J → Set G) (n : J → ℝ) (θ : ℝ)
    (p : G → ℝ) (j : J) : ℝ :=
  ((n j)⁻¹ * ∫ i in N j, p i ^ (1 - θ) ∂μ) ^ (1 / (1 - θ))

/-- Woodford (2003), eq. (2.22), p. 200: the upper-level index
`C = (∑_j a_j^{1/η} C_j^{(η−1)/η})^{η/(η−1)}`, with `a_j = n_j φ_j`. -/
noncomputable def upperIndex [Fintype J] (a : J → ℝ) (η : ℝ) (Cs : J → ℝ) : ℝ :=
  (∑ j, a j ^ (1 / η) * Cs j ^ ((η - 1) / η)) ^ (η / (η - 1))

variable {N : J → Set G} {n : J → ℝ}

/-- Woodford (2003), eq. (2.23), p. 201: integrals against the sector measure,
`∫ f dν_j = n_j⁻¹ ∫_{N_j} f`. -/
theorem integral_sectorMeasure {j : J} (hn : 0 < n j) (f : G → ℝ) :
    ∫ i, f i ∂sectorMeasure μ N n j = (n j)⁻¹ * ∫ i in N j, f i ∂μ := by
  rw [sectorMeasure, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 hn.le),
    smul_eq_mul]

/-- Woodford (2003), eq. (2.23), p. 201: the sector measure has the same null sets as
`μ` restricted to `N_j`. -/
theorem ae_sectorMeasure {j : J} (hn : 0 < n j) :
    ae (sectorMeasure μ N n j) = ae (μ.restrict (N j)) :=
  Measure.ae_ennreal_smul_measure_eq (ENNReal.ofReal_pos.2 (inv_pos.2 hn)).ne' _

/-- Woodford (2003), eq. (2.23), p. 201: the sectoral price index is the index (1.3) of the
sector measure. -/
theorem sectorPrice_eq {j : J} (hn : 0 < n j) (p : G → ℝ) :
    sectorPrice μ N n θ p j = priceIndex (sectorMeasure μ N n j) θ p := by
  rw [sectorPrice, priceIndex, integral_sectorMeasure hn, one_div]

/-- Woodford (2003), p. 200: the sectoral index is `n_j` times the index (1.2) of the sector
measure (so that a common quantity `c̄` gives `C_j = n_j c̄`). -/
theorem sectorIndex_eq (hθ : 1 < θ) {j : J} (hn : 0 < n j) {c : G → ℝ} (hc : ∀ i, 0 ≤ c i) :
    sectorIndex μ N n θ c j = n j * cesAgg (sectorMeasure μ N n j) θ c := by
  rw [sectorIndex, cesAgg, integral_sectorMeasure hn, integral_const_mul, inv_div]
  have hI : 0 ≤ ∫ i in N j, c i ^ ((θ - 1) / θ) ∂μ :=
    integral_nonneg fun i => Real.rpow_nonneg (hc i) _
  rw [Real.mul_rpow (Real.rpow_nonneg hn.le _) hI, Real.mul_rpow (inv_nonneg.2 hn.le) hI,
    ← mul_assoc, ← Real.rpow_mul hn.le, Real.inv_rpow hn.le, ← Real.rpow_neg hn.le]
  congr 1
  have h : -1 / θ * (θ / (θ - 1)) = 1 + -(θ / (θ - 1)) := by
    have : θ - 1 ≠ 0 := by linarith
    have : θ ≠ 0 := by linarith
    field_simp
    ring
  rw [h, Real.rpow_add hn, Real.rpow_one]

/-- Woodford (2003), eq. (2.23), p. 201: the sectoral data in the general measure setting —
positivity of `∫_{N_j} p^{1−θ}` and integrability against the sector measure. -/
theorem sector_setup {p : G → ℝ} (hp : ∀ i, 0 < p i) {j : J} (hn : 0 < n j)
    (hN : μ (N j) ≠ 0) (hpi : IntegrableOn (fun i => p i ^ (1 - θ)) (N j) μ) :
    0 < ∫ i, p i ^ (1 - θ) ∂sectorMeasure μ N n j ∧
      Integrable (fun i => p i ^ (1 - θ)) (sectorMeasure μ N n j) ∧
      0 < sectorPrice μ N n θ p j := by
  have hposN : 0 < ∫ i in N j, p i ^ (1 - θ) ∂μ :=
    integral_pos_of_pos (by rwa [Ne, Measure.restrict_eq_zero])
      (fun i => Real.rpow_pos_of_pos (hp i) _) hpi
  have hposν : 0 < ∫ i, p i ^ (1 - θ) ∂sectorMeasure μ N n j := by
    rw [integral_sectorMeasure hn]
    exact mul_pos (inv_pos.2 hn) hposN
  refine ⟨hposν, hpi.smul_measure ENNReal.ofReal_ne_top, ?_⟩
  rw [sectorPrice_eq hn]
  exact priceIndex_pos hposν

/-- Woodford (2003), eq. (2.23) and the sectoral demand `c(i) = n_j⁻¹ C_j (p(i)/P_j)^{−θ}`,
p. 201 (**sectoral cost minimisation**): the goods of sector `j` cost at least `P_j C_j`, with
equality iff demand follows the sectoral schedule a.e. on `N_j`. -/
theorem sector_cost (hθ : 1 < θ) {p : G → ℝ} (hp : ∀ i, 0 < p i) {j : J} (hn : 0 < n j)
    (hN : μ (N j) ≠ 0) (hpi : IntegrableOn (fun i => p i ^ (1 - θ)) (N j) μ) {c : G → ℝ}
    (hc : ∀ i, 0 ≤ c i) (hpc : IntegrableOn (fun i => p i * c i) (N j) μ) :
    sectorPrice μ N n θ p j * sectorIndex μ N n θ c j ≤ ∫ i in N j, p i * c i ∂μ ∧
      (∫ i in N j, p i * c i ∂μ = sectorPrice μ N n θ p j * sectorIndex μ N n θ c j ↔
        ∀ᵐ i ∂μ.restrict (N j),
          c i = 1 / n j * sectorIndex μ N n θ c j * (p i / sectorPrice μ N n θ p j) ^ (-θ)) := by
  obtain ⟨hposν, hPiν, -⟩ := sector_setup hp hn hN hpi
  have hpcν : Integrable (fun i => p i * c i) (sectorMeasure μ N n j) :=
    hpc.smul_measure ENNReal.ofReal_ne_top
  have hge := spend_ge hθ hp hPiν hposν hc hpcν
  have hiff := spend_eq_iff hθ hp hPiν hposν hc hpcν
  rw [integral_sectorMeasure hn] at hge hiff
  rw [Filter.EventuallyEq, ae_sectorMeasure hn] at hiff
  rw [sectorPrice_eq hn, sectorIndex_eq hθ hn hc]
  have hnz : n j ≠ 0 := hn.ne'
  constructor
  · calc priceIndex (sectorMeasure μ N n j) θ p * (n j * cesAgg (sectorMeasure μ N n j) θ c)
        = n j * (priceIndex (sectorMeasure μ N n j) θ p *
          cesAgg (sectorMeasure μ N n j) θ c) := by ring
      _ ≤ n j * ((n j)⁻¹ * ∫ i in N j, p i * c i ∂μ) := mul_le_mul_of_nonneg_left hge hn.le
      _ = ∫ i in N j, p i * c i ∂μ := by field_simp
  · have hpt : ∀ i, demand (sectorMeasure μ N n j) θ p (cesAgg (sectorMeasure μ N n j) θ c) i
        = 1 / n j * (n j * cesAgg (sectorMeasure μ N n j) θ c) *
          (p i / priceIndex (sectorMeasure μ N n j) θ p) ^ (-θ) := by
      intro i
      rw [demand]
      field_simp
    simp_rw [hpt] at hiff
    rw [← hiff]
    constructor
    · intro h
      rw [h]
      field_simp
    · intro h
      calc ∫ i in N j, p i * c i ∂μ = n j * ((n j)⁻¹ * ∫ i in N j, p i * c i ∂μ) := by
            field_simp
        _ = _ := by rw [h]; ring

/-- Woodford (2003), eq. (2.22), p. 200: in terms of `x_j = C_j/a_j` the upper aggregator is
the finite CES aggregate with weights `a_j`, since `a^{1/η} C^{(η−1)/η} = a (C/a)^{(η−1)/η}`. -/
theorem upperIndex_eq [Fintype J] {a : J → ℝ} {η : ℝ} (h0 : 0 < η) (ha : ∀ j, 0 < a j) {Cs : J → ℝ}
    (hC : ∀ j, 0 ≤ Cs j) : upperIndex a η Cs = finAgg a (fun j => Cs j / a j) η := by
  rw [upperIndex, finAgg]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.div_rpow (hC j) (ha j).le]
  have : a j ^ (1 / η) = a j / a j ^ ((η - 1) / η) := by
    rw [eq_div_iff (Real.rpow_pos_of_pos (ha j) _).ne', ← Real.rpow_add (ha j)]
    have : 1 / η + (η - 1) / η = 1 := by field_simp; ring
    rw [this, Real.rpow_one]
  have hpos : 0 < a j ^ ((η - 1) / η) := Real.rpow_pos_of_pos (ha j) _
  rw [this]
  field_simp

/-- Woodford (2003), eqs. (2.22)–(2.23), p. 201 (**two-level cost minimisation**): for any
`η > 0`, `η ≠ 1` and `θ > 1`, total expenditure `∑_j ∫_{N_j} p(i) c(i) di` on a bundle with
positive sectoral indices is at least `P C` (`P` the overall price index, `C` the index (2.22));
equality holds **iff** both levels follow their demand schedules:
`c(i) = n_j⁻¹ C_j (p(i)/P_j)^{−θ}` a.e. on each `N_j`, and `C_j = a_j C (P_j/P)^{−η}`. -/
theorem nested_cost_ge_and_eq_iff [Fintype J] [Nonempty J] (hθ : 1 < θ) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≠ 1) {a : J → ℝ} (ha : ∀ j, 0 < a j) {p : G → ℝ} (hp : ∀ i, 0 < p i)
    (hn : ∀ j, 0 < n j) (hN : ∀ j, μ (N j) ≠ 0)
    (hpi : ∀ j, IntegrableOn (fun i => p i ^ (1 - θ)) (N j) μ) {c : G → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hpc : ∀ j, IntegrableOn (fun i => p i * c i) (N j) μ)
    (hCpos : ∀ j, 0 < sectorIndex μ N n θ c j) :
    finPriceIndex a (sectorPrice μ N n θ p) η * upperIndex a η (sectorIndex μ N n θ c)
        ≤ ∑ j, ∫ i in N j, p i * c i ∂μ ∧
      (∑ j, ∫ i in N j, p i * c i ∂μ
          = finPriceIndex a (sectorPrice μ N n θ p) η * upperIndex a η (sectorIndex μ N n θ c)
        ↔ (∀ j, ∀ᵐ i ∂μ.restrict (N j), c i = 1 / n j * sectorIndex μ N n θ c j *
              (p i / sectorPrice μ N n θ p j) ^ (-θ)) ∧
          ∀ j, sectorIndex μ N n θ c j = a j * upperIndex a η (sectorIndex μ N n θ c) *
            (sectorPrice μ N n θ p j / finPriceIndex a (sectorPrice μ N n θ p) η) ^ (-η)) := by
  have hsec := fun j => sector_cost hθ hp (hn j) (hN j) (hpi j) hc (hpc j)
  have hPs : ∀ j, 0 < sectorPrice μ N n θ p j := fun j =>
    (sector_setup hp (hn j) (hN j) (hpi j)).2.2
  have hx : ∀ j, 0 < sectorIndex μ N n θ c j / a j := fun j => div_pos (hCpos j) (ha j)
  obtain ⟨hup, hupiff⟩ := fin_cost_ge_and_eq_iff hη0 hη1 ha hPs hx
  have hspend : ∑ j, a j * (sectorPrice μ N n θ p j * (sectorIndex μ N n θ c j / a j))
      = ∑ j, sectorPrice μ N n θ p j * sectorIndex μ N n θ c j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    have := (ha j).ne'
    field_simp
  rw [hspend, ← upperIndex_eq hη0 ha fun j => (hCpos j).le] at hup hupiff
  have hsum_le : ∑ j, sectorPrice μ N n θ p j * sectorIndex μ N n θ c j
      ≤ ∑ j, ∫ i in N j, p i * c i ∂μ := Finset.sum_le_sum fun j _ => (hsec j).1
  refine ⟨hup.trans hsum_le, ?_⟩
  constructor
  · intro heq
    have h1 := le_antisymm (hsum_le.trans heq.le) hup
    have hz : ∑ j, (∫ i in N j, p i * c i ∂μ - sectorPrice μ N n θ p j *
        sectorIndex μ N n θ c j) = 0 := by
      rw [Finset.sum_sub_distrib, heq, h1, sub_self]
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sub_nonneg.2 (hsec j).1).1 hz
    refine ⟨fun j => (hsec j).2.1 (sub_eq_zero.1 (hall j (Finset.mem_univ j))), fun j => ?_⟩
    have := hupiff.1 h1 j
    rw [div_eq_iff (ha j).ne'] at this
    rw [this]
    ring
  · rintro ⟨hd, hu⟩
    have h2 : ∀ j, ∫ i in N j, p i * c i ∂μ
        = sectorPrice μ N n θ p j * sectorIndex μ N n θ c j := fun j => (hsec j).2.2 (hd j)
    have h1 := hupiff.2 fun j => by
      have := (ha j).ne'
      rw [hu j]
      field_simp
    rw [Finset.sum_congr rfl fun j _ => h2 j, h1]

/-- Woodford (2003), p. 201 (**existence of the two-level minimiser**): if a bundle follows
`c(i) = n_j⁻¹ C*_j (p(i)/P_j)^{−θ}` on each `N_j`, where `C*_j = a_j C (P_j/P)^{−η}` for a target
`C > 0`, then its sectoral indices are `C*_j`, its upper index is `C`, and it costs `P C`. -/
theorem nested_demand_attains [Fintype J] [Nonempty J] (hθ : 1 < θ) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≠ 1) {a : J → ℝ} (ha : ∀ j, 0 < a j) {p : G → ℝ} (hp : ∀ i, 0 < p i)
    (hn : ∀ j, 0 < n j) (hN : ∀ j, μ (N j) ≠ 0) (hNm : ∀ j, MeasurableSet (N j))
    (hpi : ∀ j, IntegrableOn (fun i => p i ^ (1 - θ)) (N j) μ) {C : ℝ} (hC : 0 < C)
    {c : G → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hcN : ∀ j, ∀ i ∈ N j, c i = 1 / n j * (a j * C *
      (sectorPrice μ N n θ p j / finPriceIndex a (sectorPrice μ N n θ p) η) ^ (-η)) *
        (p i / sectorPrice μ N n θ p j) ^ (-θ)) :
    (∀ j, sectorIndex μ N n θ c j = a j * C *
      (sectorPrice μ N n θ p j / finPriceIndex a (sectorPrice μ N n θ p) η) ^ (-η)) ∧
    upperIndex a η (sectorIndex μ N n θ c) = C ∧
    (∀ j, IntegrableOn (fun i => p i * c i) (N j) μ) ∧
    ∑ j, ∫ i in N j, p i * c i ∂μ = finPriceIndex a (sectorPrice μ N n θ p) η * C := by
  have hPs : ∀ j, 0 < sectorPrice μ N n θ p j := fun j =>
    (sector_setup hp (hn j) (hN j) (hpi j)).2.2
  set P := finPriceIndex a (sectorPrice μ N n θ p) η
  set Cst : J → ℝ := fun j => a j * C * (sectorPrice μ N n θ p j / P) ^ (-η) with hCst
  have hCst_pos : ∀ j, 0 < Cst j := fun j =>
    mul_pos (mul_pos (ha j) hC) (Real.rpow_pos_of_pos (div_pos (hPs j) (Real.rpow_pos_of_pos
      (Finset.sum_pos (fun k _ => mul_pos (ha k) (Real.rpow_pos_of_pos (hPs k) _))
        Finset.univ_nonempty) _)) _)
  -- on each sector, `c` is the demand bundle of the sector measure for the target `C*_j / n_j`
  have hae : ∀ j, c =ᵐ[sectorMeasure μ N n j]
      demand (sectorMeasure μ N n j) θ p (Cst j / n j) := by
    intro j
    rw [Filter.EventuallyEq, ae_sectorMeasure (hn j)]
    filter_upwards [ae_restrict_mem (hNm j)] with i hi
    rw [hcN j i hi, demand, ← sectorPrice_eq (hn j)]
    have := (hn j).ne'
    simp only [hCst]
    field_simp
  have hsecIdx : ∀ j, sectorIndex μ N n θ c j = Cst j := by
    intro j
    obtain ⟨hposν, -, -⟩ := sector_setup hp (hn j) (hN j) (hpi j)
    rw [sectorIndex_eq hθ (hn j) hc]
    have hagg : cesAgg (sectorMeasure μ N n j) θ c
        = cesAgg (sectorMeasure μ N n j) θ (demand (sectorMeasure μ N n j) θ p (Cst j / n j)) := by
      unfold cesAgg
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hae j] with i hi
      rw [hi]
    rw [hagg, cesAgg_demand hθ hp hposν (div_pos (hCst_pos j) (hn j)).le]
    have := (hn j).ne'
    field_simp
  have hint : ∀ j, IntegrableOn (fun i => p i * c i) (N j) μ := by
    intro j
    obtain ⟨hposν, hPiν, -⟩ := sector_setup hp (hn j) (hN j) (hpi j)
    have hd := integrable_spend_demand hp hPiν hposν (Cst j / n j)
    have hc0 : ENNReal.ofReal (n j)⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 (hn j))).ne'
    have hd' : Integrable (fun i => p i * demand (sectorMeasure μ N n j) θ p (Cst j / n j) i)
        (μ.restrict (N j)) := (integrable_smul_measure hc0 ENNReal.ofReal_ne_top).1 hd
    refine hd'.congr ?_
    filter_upwards [ae_restrict_mem (hNm j)] with i hi
    rw [hcN j i hi, demand, ← sectorPrice_eq (hn j)]
    have := (hn j).ne'
    simp only [hCst]
    field_simp
  have hcost : ∀ j, ∫ i in N j, p i * c i ∂μ = sectorPrice μ N n θ p j * Cst j := by
    intro j
    obtain ⟨hposν, -, -⟩ := sector_setup hp (hn j) (hN j) (hpi j)
    have hs := spend_demand hθ hp hposν (Cst j / n j)
    rw [integral_sectorMeasure (hn j), ← sectorPrice_eq (hn j)] at hs
    have hcongr : ∫ i in N j, p i * c i ∂μ
        = ∫ i in N j, p i * demand (sectorMeasure μ N n j) θ p (Cst j / n j) i ∂μ := by
      refine setIntegral_congr_fun (hNm j) fun i hi => ?_
      rw [hcN j i hi, demand, ← sectorPrice_eq (hn j)]
      have := (hn j).ne'
      simp only [hCst]
      field_simp
    rw [hcongr]
    have := (hn j).ne'
    field_simp at hs ⊢
    linarith
  obtain ⟨hagg, hspend⟩ := fin_demand_attains hη0 hη1 ha hPs hC
  refine ⟨hsecIdx, ?_, hint, ?_⟩
  · rw [upperIndex_eq hη0 ha fun j => by rw [hsecIdx j]; exact (hCst_pos j).le]
    convert hagg using 2
    funext j
    rw [hsecIdx j, hCst]
    have := (ha j).ne'
    field_simp
    rfl
  · rw [Finset.sum_congr rfl fun j _ => hcost j, ← hspend]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hCst]
    ring

/-- Woodford (2003), p. 201 (normalisation of the sector index): if every good of sector `j`
has the price `p̄` and the sector has measure `n_j`, then `P_j = p̄`. -/
theorem sectorPrice_const (hθ : 1 < θ) {j : J} (hn : 0 < n j) (hNm : MeasurableSet (N j))
    (hμN : μ (N j) = ENNReal.ofReal (n j)) {p : G → ℝ} {pbar : ℝ} (hpbar : 0 < pbar)
    (hpN : ∀ i ∈ N j, p i = pbar) : sectorPrice μ N n θ p j = pbar := by
  rw [sectorPrice, setIntegral_congr_fun hNm (fun i hi => by rw [hpN i hi]),
    setIntegral_const, Measure.real, hμN, ENNReal.toReal_ofReal hn.le, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul, one_div]
  exact Real.rpow_rpow_inv hpbar.le (by linarith)

/-- Woodford (2003), p. 201 (normalisation of the overall index): with weights summing to one,
a common sectoral price `p̄` gives `P = p̄`. -/
theorem finPriceIndex_const [Fintype J] {a : J → ℝ} (hsum : ∑ j, a j = 1) {η : ℝ} (hη1 : η ≠ 1)
    {pbar : ℝ} (hpbar : 0 < pbar) : finPriceIndex a (fun _ => pbar) η = pbar := by
  rw [finPriceIndex, ← Finset.sum_mul, hsum, one_mul, one_div]
  exact Real.rpow_rpow_inv hpbar.le (sub_ne_zero.2 (Ne.symm hη1))

/-- Woodford (2003), p. 201 (normalisation of demands): at a common price (`P_j = P = p̄`) and
with `a_j = n_j φ_j`, the demands are `C_j = n_j φ_j C` and `c(i) = φ_j C`. -/
theorem common_price_demands {nj φj C pbar η : ℝ} (hn : 0 < nj) (hpbar : 0 < pbar) :
    nj * φj * C * (pbar / pbar) ^ (-η) = nj * φj * C ∧
      1 / nj * (nj * φj * C * (pbar / pbar) ^ (-η)) * (pbar / pbar) ^ (-θ) = φj * C := by
  rw [div_self hpbar.ne', Real.one_rpow, Real.one_rpow, mul_one, mul_one]
  refine ⟨rfl, ?_⟩
  field_simp

end Nested

/-- Woodford (2003), p. 201: the book's sectors `N₁ = [0, n₁]` and `N₂ = (n₁, 1]` partition the
goods continuum, so total expenditure is the sum of sectoral expenditures. -/
theorem twoSector_split {f : ℝ → ℝ} {n₁ : ℝ} (h0 : 0 ≤ n₁) (h1 : n₁ ≤ 1)
    (hf : IntegrableOn f (Set.Icc 0 1)) :
    ∫ i in Set.Icc 0 1, f i = (∫ i in Set.Icc 0 n₁, f i) + ∫ i in Set.Ioc n₁ 1, f i := by
  rw [← Set.Icc_union_Ioc_eq_Icc h0 h1] at hf ⊢
  exact setIntegral_union (Set.disjoint_left.2 fun x hx hx' => absurd hx.2 (not_le.2 hx'.1))
    measurableSet_Ioc (hf.mono_set Set.subset_union_left) (hf.mono_set Set.subset_union_right)

/-- Woodford (2003), eqs. (4.1)–(4.2), pp. 221–222 (**labour aggregation**): with the CES labour
index `H = (∫₀¹ h(j)^{(θ_w−1)/θ_w} dj)^{θ_w/(θ_w−1)}`, `θ_w > 1`, and the wage index
`W = (∫₀¹ w(j)^{1−θ_w} dj)^{1/(1−θ_w)}`: (i) every labour bundle costs at least `W H`; (ii) it
costs exactly `W H` iff `h(j) = H (w(j)/W)^{−θ_w}` a.e., the demand (4.2); (iii) the demand (4.2)
attains any `H ≥ 0`; (iv) the wage bill of (4.2) is `W H`. -/
theorem labour_cost_minimisation {θw : ℝ} (hθw : 1 < θw) {w : ℝ → ℝ} (hw : ∀ j, 0 < w j)
    (hwi : IntegrableOn (fun j => w j ^ (1 - θw)) (Set.Icc 0 1)) {h : ℝ → ℝ}
    (hh : ∀ j, 0 ≤ h j) (hwh : IntegrableOn (fun j => w j * h j) (Set.Icc 0 1)) :
    priceIndex (volume.restrict (Set.Icc 0 1)) θw w *
        cesAgg (volume.restrict (Set.Icc 0 1)) θw h ≤ ∫ j in Set.Icc 0 1, w j * h j ∧
      (∫ j in Set.Icc 0 1, w j * h j
          = priceIndex (volume.restrict (Set.Icc 0 1)) θw w *
            cesAgg (volume.restrict (Set.Icc 0 1)) θw h ↔
        ∀ᵐ j ∂(volume.restrict (Set.Icc 0 1)),
          h j = demand (volume.restrict (Set.Icc 0 1)) θw w
            (cesAgg (volume.restrict (Set.Icc 0 1)) θw h) j) ∧
      (∀ H : ℝ, 0 ≤ H → cesAgg (volume.restrict (Set.Icc 0 1)) θw
        (demand (volume.restrict (Set.Icc 0 1)) θw w H) = H) ∧
      ∀ H : ℝ, ∫ j in Set.Icc 0 1, w j * demand (volume.restrict (Set.Icc 0 1)) θw w H j
        = priceIndex (volume.restrict (Set.Icc 0 1)) θw w * H :=
  unitInterval_expenditure_minimisation hθw hw hwi hh hwh

namespace Nested

variable {J : Type*} {N : J → Set G} {n : J → ℝ}

/-- Woodford (2003), p. 201: the expenditures at which a bundle with positive sectoral indices
attains at least `C` units of the two-level index (2.22). -/
def nestedCostSet [Fintype J] (μ : Measure G) (N : J → Set G) (n : J → ℝ) (θ : ℝ) (a : J → ℝ)
    (η : ℝ) (p : G → ℝ) (C : ℝ) : Set ℝ :=
  {X | ∃ c : G → ℝ, (∀ i, 0 ≤ c i) ∧ (∀ j, IntegrableOn (fun i => p i * c i) (N j) μ) ∧
    (∀ j, 0 < sectorIndex μ N n θ c j) ∧ C ≤ upperIndex a η (sectorIndex μ N n θ c) ∧
    X = ∑ j, ∫ i in N j, p i * c i ∂μ}

omit [MeasurableSpace G] in
/-- Woodford (2003), p. 201: on disjoint sectors, a bundle can be prescribed sector by sector
(the sum of the sectoral indicator functions). -/
theorem exists_sectorwise [Finite J] (hdisj : Pairwise fun j k => Disjoint (N j) (N k))
    (g : J → G → ℝ) (hg : ∀ j i, 0 ≤ g j i) :
    ∃ c : G → ℝ, (∀ i, 0 ≤ c i) ∧ ∀ j, ∀ i ∈ N j, c i = g j i := by
  have := Fintype.ofFinite J
  refine ⟨fun i => ∑ j, (N j).indicator (g j) i, fun i => Finset.sum_nonneg fun j _ =>
    Set.indicator_nonneg (fun i _ => hg j i) i, fun j i hi => ?_⟩
  dsimp only
  rw [Finset.sum_eq_single j]
  · exact Set.indicator_of_mem hi _
  · intro k _ hkj
    exact Set.indicator_of_notMem (Set.disjoint_left.1 (hdisj hkj).symm hi) _
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- Woodford (2003), p. 201 (**the overall price index is the minimal cost of the two-level
aggregate**): on disjoint sectors, `P C` is the least expenditure at which `C > 0` units of the
index (2.22) can be obtained from the individual goods, for any `η > 0`, `η ≠ 1`, `θ > 1`. -/
theorem nested_isLeast [Fintype J] [Nonempty J] (hθ : 1 < θ) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≠ 1) {a : J → ℝ} (ha : ∀ j, 0 < a j) {p : G → ℝ} (hp : ∀ i, 0 < p i)
    (hn : ∀ j, 0 < n j) (hN : ∀ j, μ (N j) ≠ 0) (hNm : ∀ j, MeasurableSet (N j))
    (hdisj : Pairwise fun j k => Disjoint (N j) (N k))
    (hpi : ∀ j, IntegrableOn (fun i => p i ^ (1 - θ)) (N j) μ) {C : ℝ} (hC : 0 < C) :
    IsLeast (nestedCostSet μ N n θ a η p C) (finPriceIndex a (sectorPrice μ N n θ p) η * C) := by
  have hPs : ∀ j, 0 < sectorPrice μ N n θ p j := fun j =>
    (sector_setup hp (hn j) (hN j) (hpi j)).2.2
  have hP : 0 < finPriceIndex a (sectorPrice μ N n θ p) η :=
    Real.rpow_pos_of_pos (Finset.sum_pos (fun k _ => mul_pos (ha k)
      (Real.rpow_pos_of_pos (hPs k) _)) Finset.univ_nonempty) _
  constructor
  · obtain ⟨c, hc, hcN⟩ := exists_sectorwise hdisj
      (fun j i => 1 / n j * (a j * C *
        (sectorPrice μ N n θ p j / finPriceIndex a (sectorPrice μ N n θ p) η) ^ (-η)) *
          (p i / sectorPrice μ N n θ p j) ^ (-θ))
      (fun j i => by
        have := hn j
        have := ha j
        have := hPs j
        have := hp i
        positivity)
    obtain ⟨hidx, hup, hint, hcost⟩ :=
      nested_demand_attains hθ hη0 hη1 ha hp hn hN hNm hpi hC hc hcN
    refine ⟨c, hc, hint, fun j => ?_, hup.ge, hcost.symm⟩
    rw [hidx j]
    exact mul_pos (mul_pos (ha j) hC) (Real.rpow_pos_of_pos (div_pos (hPs j) hP) _)
  · rintro X ⟨c, hc, hpc, hCpos, hCc, rfl⟩
    exact (mul_le_mul_of_nonneg_left hCc hP.le).trans
      (nested_cost_ge_and_eq_iff hθ hη0 hη1 ha hp hn hN hpi hc hpc hCpos).1

end Nested

/-! ### The Cobb–Douglas limit `η → 1` (Woodford (2003), p. 201, n. 61) -/

/-- Woodford (2003), p. 201, n. 61: with weights summing to one, the log of the weighted sum
`r ↦ log ∑ a_j e^{ℓ_j r}` has derivative `∑ a_j ℓ_j` at `r = 0`. -/
theorem hasDerivAt_logSumExp {ι : Type*} [Fintype ι] {a ℓ : ι → ℝ} (hsum : ∑ j, a j = 1) :
    HasDerivAt (fun r => Real.log (∑ j, a j * Real.exp (ℓ j * r))) (∑ j, a j * ℓ j) 0 := by
  have hS : HasDerivAt (fun r => ∑ j, a j * Real.exp (ℓ j * r))
      (∑ j, a j * (Real.exp (ℓ j * 0) * (ℓ j * 1))) 0 :=
    HasDerivAt.fun_sum fun j _ =>
      (((hasDerivAt_id (0 : ℝ)).const_mul (ℓ j)).exp).const_mul (a j)
  have h0 : ∑ j, a j * Real.exp (ℓ j * 0) = 1 := by simp [hsum]
  have := hS.log (by rw [h0]; exact one_ne_zero)
  rw [h0] at this
  simpa using this

/-- Woodford (2003), p. 201, n. 61 (**power means tend to the geometric mean**): for weights
`a_j > 0` summing to one and `x_j > 0`, `(∑ a_j x_j^r)^{1/r} → ∏ x_j^{a_j}` as `r → 0`. -/
theorem tendsto_powerMean_geomMean {ι : Type*} [Fintype ι] {a x : ι → ℝ}
    (ha : ∀ j, 0 < a j) (hsum : ∑ j, a j = 1) (hx : ∀ j, 0 < x j) :
    Filter.Tendsto (fun r => (∑ j, a j * x j ^ r) ^ (1 / r)) (nhdsWithin (0 : ℝ) {0}ᶜ)
      (nhds (∏ j, x j ^ a j)) := by
  have hF := hasDerivAt_logSumExp (a := a) (ℓ := fun j => Real.log (x j)) hsum
  have hlim := (Real.continuous_exp.tendsto _).comp (hasDerivAt_iff_tendsto_slope.1 hF)
  have hval : Real.exp (∑ j, a j * Real.log (x j)) = ∏ j, x j ^ a j := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Real.rpow_def_of_pos (hx j), mul_comm]
  rw [hval] at hlim
  refine hlim.congr' ?_
  have hne : (Finset.univ : Finset ι).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hsum
    exact zero_ne_one hsum
  have hF0 : Real.log (∑ j, a j * Real.exp (Real.log (x j) * 0)) = 0 := by simp [hsum]
  filter_upwards with r
  have hsum' : ∑ j, a j * x j ^ r = ∑ j, a j * Real.exp (Real.log (x j) * r) :=
    Finset.sum_congr rfl fun j _ => by rw [Real.rpow_def_of_pos (hx j)]
  have hS : 0 < ∑ j, a j * x j ^ r :=
    Finset.sum_pos (fun j _ => mul_pos (ha j) (Real.rpow_pos_of_pos (hx j) _)) hne
  simp only [Function.comp_apply, slope_def_field]
  rw [hF0, sub_zero, sub_zero, ← hsum', Real.rpow_def_of_pos hS, div_eq_mul_one_div]

/-- Woodford (2003), p. 201, n. 61 (**the Cobb–Douglas limit of the upper aggregator**): with
weights `a_j > 0` summing to one and `x_j > 0`, the CES aggregate tends to `∏ x_j^{a_j}` and the
CES price index tends to `∏ q_j^{a_j}` as `η → 1`. -/
theorem tendsto_cobbDouglas {ι : Type*} [Fintype ι] {a x q : ι → ℝ} (ha : ∀ j, 0 < a j)
    (hsum : ∑ j, a j = 1) (hx : ∀ j, 0 < x j) (hq : ∀ j, 0 < q j) :
    Filter.Tendsto (fun η => finAgg a x η) (nhdsWithin (1 : ℝ) {1}ᶜ) (nhds (∏ j, x j ^ a j)) ∧
      Filter.Tendsto (fun η => finPriceIndex a q η) (nhdsWithin (1 : ℝ) {1}ᶜ)
        (nhds (∏ j, q j ^ a j)) := by
  constructor
  · have hr : Filter.Tendsto (fun η : ℝ => (η - 1) / η) (nhdsWithin (1 : ℝ) {1}ᶜ)
        (nhdsWithin (0 : ℝ) {0}ᶜ) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have hc : ContinuousAt (fun η : ℝ => (η - 1) / η) 1 :=
          (continuousAt_id.sub continuousAt_const).div continuousAt_id one_ne_zero
        have := hc.tendsto
        simp only [sub_self, zero_div] at this
        exact this.mono_left nhdsWithin_le_nhds
      · have hpos : ∀ᶠ η in nhdsWithin (1 : ℝ) {1}ᶜ, 0 < η :=
          nhdsWithin_le_nhds (lt_mem_nhds one_pos)
        filter_upwards [hpos, self_mem_nhdsWithin] with η hη hη1
        exact div_ne_zero (sub_ne_zero.2 hη1) hη.ne'
    have := (tendsto_powerMean_geomMean ha hsum hx).comp hr
    refine this.congr' (Filter.Eventually.of_forall fun η => ?_)
    simp only [Function.comp_apply, finAgg, one_div_div]
  · have hs : Filter.Tendsto (fun η : ℝ => 1 - η) (nhdsWithin (1 : ℝ) {1}ᶜ)
        (nhdsWithin (0 : ℝ) {0}ᶜ) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have hc : ContinuousAt (fun η : ℝ => 1 - η) 1 := continuousAt_const.sub continuousAt_id
        have := hc.tendsto
        simp only [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with η hη1
        exact sub_ne_zero.2 (Ne.symm hη1)
    have := (tendsto_powerMean_geomMean ha hsum hq).comp hs
    refine this.congr' (Filter.Eventually.of_forall fun η => ?_)
    simp only [Function.comp_apply, finPriceIndex]

end Woodford.NominalRigidities.DixitStiglitz
