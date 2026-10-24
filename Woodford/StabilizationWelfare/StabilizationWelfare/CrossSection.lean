/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.Moments
import StabilizationWelfare.Sequences
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Option

/-!
# The cross-section of goods: dispersion algebra

Woodford (2003), *Interest and Prices*, Chapter 6, §2 (pp. 392–405) and Appendix E.2
(pp. 694–696): the exact cross-sectional facts behind the welfare criterion.

The cross-section of differentiated goods `i` is a probability space `(G, μ)` (the book's
`i ∈ [0,1]`; a finite weighted population is the special case of a finite sum of Dirac
masses). `crossMean μ x = E_i x(i)`, `crossVar μ x = var_i x(i)`.

## Main results

* (2.12), p. 396: `log_demand` (constant-elasticity demand in logs) and `crossVar_demand`:
  `var_i log y = θ² var_i log p`; the general `crossVar_affine`.
* Two-point dispersion, p. 397: `twoPoint_var` (`ι(1−ι)(p₁ − p₂)²`, exact for a goods
  population with two price groups) and `twoPoint_subst`, the substitution
  `ι(1−ι)(p₁−p₂)² = ((1−ι)/ι)(π − E π)² + R` with an explicit remainder `twoPointRem`
  of weighted degree three (`twoPointRem_scale`).
* The Calvo mixture (E.8), p. 695, EXACT: the moment identity is proved once
  (`Moments.mix_var_meanChange`, with the finite-weight form `Moments.mix_var`); here it is
  applied to distributions on `ℝ`, `calvoMixIdx_var_meanChange` (the mixture
  `α (ν shifted by d) + (1−α) δ_{p*}`, `d = 0` for Calvo; `integral_calvoMixIdx`,
  `integrable_calvoMixIdx`, `calvoMixIdx_good`, `calvoMixIdx_mean`), and to the
  goods-population version `goods_calvo_var` (a reset set `R` of measure `1 − α` whose
  complement is representative of the old cross-section).
* Indexation (2.23)–(2.24), p. 402, EXACT: `goods_index_var` (and `Moments.mix_var` with a
  shift `d = γ π_{t−1}`): `Δ_t = α Δ_{t−1} + (α/(1−α))(P̄_t − P̄_{t−1} − γ π_{t−1})²`.
* The discounted sum, p. 400 (from the integrated recursion `Sequences.disp_integrated` and the
  Cauchy product `Sequences.disp_discounted_hasSum`): `disp_discounted_calvo`:
  `∑ βᵗ Δ_t = (α/((1−α)(1−αβ))) ∑ βᵗ π_t² + α Δ_{−1}/(1−αβ)`, the last term being the t.i.p.
  (initial dispersion).
* The CES (log-mean-exp) expansions used for (E.5) and for `P̄_t = log P_t + O(2)` (p. 695):
  `logMeanExp_sub_mean_le` (`|log P − P̄| ≤ |1−θ| Δ`) and `logMeanExp_second_order`
  (`|Ŷ − E_i ŷ − (r/2) var_i ŷ| ≤ r² B var_i ŷ`), with explicit constants, and
  `log_ces_eq` linking the Dixit–Stiglitz aggregate (2.6) to `logMeanExp`.

Throughout, "date `−1`" is index `0`: `D 0 = Δ_{−1}` and `D (t+1) = Δ_t`.
-/

namespace Woodford.StabilizationWelfare.CrossSection

open MeasureTheory Filter Topology
open Moments (mix_var_shift mix_mean_shift mix_var_meanChange)

variable {G : Type*} [MeasurableSpace G]

/-! ### Cross-sectional mean and variance -/

/-- Woodford (2003), p. 694: the cross-sectional mean `E_i x(i) = ∫ x(i) di`. -/
noncomputable def crossMean (μ : Measure G) (x : G → ℝ) : ℝ := ∫ i, x i ∂μ

/-- Woodford (2003), p. 694: the cross-sectional variance `var_i x(i)`. -/
noncomputable def crossVar (μ : Measure G) (x : G → ℝ) : ℝ :=
  ∫ i, (x i - crossMean μ x) ^ 2 ∂μ

/-- Woodford (2003), p. 694: `E_i (a + b x(i)) = a + b E_i x(i)`. -/
theorem crossMean_affine (μ : Measure G) [IsProbabilityMeasure μ] {x : G → ℝ}
    (hx : Integrable x μ) (a b : ℝ) :
    crossMean μ (fun i => a + b * x i) = a + b * crossMean μ x := by
  unfold crossMean
  rw [integral_add (integrable_const a) (hx.const_mul b), integral_const, integral_const_mul]
  simp

/-- Woodford (2003), p. 396: `var_i (a + b x(i)) = b² var_i x(i)`. -/
theorem crossVar_affine (μ : Measure G) [IsProbabilityMeasure μ] {x : G → ℝ}
    (hx : Integrable x μ) (a b : ℝ) :
    crossVar μ (fun i => a + b * x i) = b ^ 2 * crossVar μ x := by
  unfold crossVar
  rw [crossMean_affine μ hx, ← integral_const_mul]
  congr 1
  funext i
  ring

/-- Woodford (2003), p. 396: the cross-sectional variance is the second moment minus the
squared mean. -/
theorem crossVar_eq (μ : Measure G) [IsProbabilityMeasure μ] {x : G → ℝ}
    (h1 : Integrable x μ) (h2 : Integrable (fun i => x i ^ 2) μ) :
    crossVar μ x = ∫ i, x i ^ 2 ∂μ - crossMean μ x ^ 2 := by
  have hpt : ∀ i, (x i - crossMean μ x) ^ 2 =
      x i ^ 2 + (-2 * crossMean μ x) * x i + crossMean μ x ^ 2 := fun i => by ring
  unfold crossVar
  simp_rw [hpt]
  have e1 := integral_add (μ := μ) (f := fun i => x i ^ 2 + (-2 * crossMean μ x) * x i)
    (g := fun _ => crossMean μ x ^ 2) (h2.add (h1.const_mul _)) (integrable_const _)
  have e2 := integral_add (μ := μ) (f := fun i => x i ^ 2)
    (g := fun i => (-2 * crossMean μ x) * x i) h2 (h1.const_mul _)
  rw [e1, e2, integral_const_mul, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  unfold crossMean
  ring

/-- Woodford (2003), p. 396: the cross-sectional variance is nonnegative. -/
theorem crossVar_nonneg (μ : Measure G) (x : G → ℝ) : 0 ≤ crossVar μ x :=
  integral_nonneg fun _ => sq_nonneg _

/-- Woodford (2003), p. 396: `crossVar` is Mathlib's `ProbabilityTheory.variance` of the log
price (or log output) viewed as a random variable over the goods. -/
theorem crossVar_eq_variance (μ : Measure G) {x : G → ℝ} (hx : AEMeasurable x μ) :
    crossVar μ x = ProbabilityTheory.variance x μ := by
  rw [ProbabilityTheory.variance_eq_integral hx]
  rfl

/-! ### (2.12): constant-elasticity demand -/

/-- Woodford (2003), eq. (2.12), p. 396: the Dixit–Stiglitz demand
`y(i) = Y (p(i)/P)^{−θ}` is, in logs, `log y(i) = log Y − θ (log p(i) − log P)`. -/
theorem log_demand {Y P p θ : ℝ} (hY : 0 < Y) (hP : 0 < P) (hp : 0 < p) :
    Real.log (Y * (p / P) ^ (-θ)) = Real.log Y - θ * (Real.log p - Real.log P) := by
  rw [Real.log_mul hY.ne' (Real.rpow_pos_of_pos (div_pos hp hP) _).ne',
    Real.log_rpow (div_pos hp hP), Real.log_div hp.ne' hP.ne']
  ring

/-- Woodford (2003), p. 396 (consequence of (2.12)): `var_i log y(i) = θ² var_i log p(i)`. -/
theorem crossVar_demand (μ : Measure G) [IsProbabilityMeasure μ] {ly lp : G → ℝ}
    {LY LP θ : ℝ} (hlp : Integrable lp μ) (hdem : ∀ i, ly i = LY - θ * (lp i - LP)) :
    crossVar μ ly = θ ^ 2 * crossVar μ lp := by
  have : ly = fun i => (LY + θ * LP) + (-θ) * lp i := by
    funext i
    rw [hdem i]
    ring
  rw [this, crossVar_affine μ hlp, neg_sq]

/-! ### Piecewise cross-sections -/

/-- Woodford (2003), p. 695: integrating over a cross-section in which the goods of a
measurable set `R` all charge `p` and the others keep the old log price `xo`:
`∫ f(xn) = μ(R) f(p) + ∫_{Rᶜ} f(xo)`. -/
theorem integral_reset (μ : Measure G) [IsProbabilityMeasure μ] {R : Set G}
    (hR : MeasurableSet R) {p : ℝ} {xo xn : G → ℝ} (hn1 : ∀ i ∈ R, xn i = p)
    (hn2 : ∀ i ∉ R, xn i = xo i) {f : ℝ → ℝ} (hf : Integrable (fun i => f (xo i)) μ) :
    Integrable (fun i => f (xn i)) μ ∧
      ∫ i, f (xn i) ∂μ = μ.real R * f p + ∫ i in Rᶜ, f (xo i) ∂μ := by
  have heq : (fun i => f (xn i)) =
      fun i => R.indicator (fun _ => f p) i + Rᶜ.indicator (fun i => f (xo i)) i := by
    funext i
    by_cases h : i ∈ R
    · have h' : i ∉ Rᶜ := fun hc => hc h
      rw [Set.indicator_of_mem h, Set.indicator_of_notMem h', hn1 i h, add_zero]
    · have h' : i ∈ Rᶜ := h
      rw [Set.indicator_of_notMem h, Set.indicator_of_mem h', hn2 i h, zero_add]
  have hint : Integrable (fun i => f (xn i)) μ := by
    rw [heq]
    exact ((integrable_const (f p)).indicator hR).add (hf.indicator hR.compl)
  refine ⟨hint, ?_⟩
  rw [← integral_add_compl hR hint]
  have h1 : ∫ i in R, f (xn i) ∂μ = ∫ _ in R, f p ∂μ :=
    setIntegral_congr_fun hR fun i hi => by simp only [hn1 i hi]
  have h2 : ∫ i in Rᶜ, f (xn i) ∂μ = ∫ i in Rᶜ, f (xo i) ∂μ :=
    setIntegral_congr_fun hR.compl fun i hi => by simp only [hn2 i hi]
  rw [h1, h2, setIntegral_const, smul_eq_mul]

/-! ### Two-point dispersion (New Classical model, p. 397) -/

/-- Woodford (2003), p. 397 (exact): a fraction `ι` of goods at log price `p₁` and `1 − ι` at
`p₂` have mean `ι p₁ + (1−ι) p₂` and variance `ι(1−ι)(p₁ − p₂)²`. -/
theorem twoPoint_var (μ : Measure G) [IsProbabilityMeasure μ] {F : Set G}
    (hF : MeasurableSet F) {ι p₁ p₂ : ℝ} (hι : μ.real F = ι) {x : G → ℝ}
    (h1 : ∀ i ∈ F, x i = p₁) (h2 : ∀ i ∉ F, x i = p₂) :
    crossMean μ x = ι * p₁ + (1 - ι) * p₂ ∧
      crossVar μ x = ι * (1 - ι) * (p₁ - p₂) ^ 2 := by
  have hc : μ.real Fᶜ = 1 - ι := by rw [measureReal_compl hF, probReal_univ, hι]
  obtain ⟨i1, e1⟩ := integral_reset μ hF (xo := fun _ => p₂) h1 h2 (f := fun z => z)
    (integrable_const _)
  obtain ⟨i2, e2⟩ := integral_reset μ hF (xo := fun _ => p₂) h1 h2 (f := fun z => z ^ 2)
    (integrable_const _)
  rw [setIntegral_const, hc, hι, smul_eq_mul] at e1 e2
  have hm : crossMean μ x = ι * p₁ + (1 - ι) * p₂ := by
    unfold crossMean
    rw [e1]
  refine ⟨hm, ?_⟩
  rw [crossVar_eq μ i1 i2, e2, hm]
  ring

/-- Woodford (2003), p. 397: the remainder in the substitution of unexpected inflation into
the two-point variance, when `π − E_{t−1}π = ι(p₁ − p₂) + e` with `e = O(ξ²)`. -/
noncomputable def twoPointRem (ι dp e : ℝ) : ℝ := -((1 - ι) / ι) * (2 * ι * dp * e + e ^ 2)

/-- Woodford (2003), p. 397 (exact form of
`var_i log p = ((1−ι)/ι)(π − E_{t−1}π)² + O(ξ³)`): if `s = ι (p₁ − p₂) + e` then
`ι(1−ι)(p₁ − p₂)² = ((1−ι)/ι) s² + twoPointRem ι (p₁ − p₂) e`. -/
theorem twoPoint_subst {ι p₁ p₂ s e : ℝ} (hι : ι ≠ 0) (hs : s = ι * (p₁ - p₂) + e) :
    ι * (1 - ι) * (p₁ - p₂) ^ 2 = (1 - ι) / ι * s ^ 2 + twoPointRem ι (p₁ - p₂) e := by
  unfold twoPointRem
  subst hs
  field_simp
  ring

/-- Woodford (2003), p. 397: `twoPointRem` has weighted degree three (`p₁ − p₂` of weight one,
the error `e` of weight two): `R(s d, s² e) = s³ (−((1−ι)/ι))(2 ι d e + s e²)`. -/
theorem twoPointRem_scale (ι dp e s : ℝ) :
    twoPointRem ι (s * dp) (s ^ 2 * e) = s ^ 3 * (-((1 - ι) / ι) * (2 * ι * dp * e + s * e ^ 2))
    := by
  unfold twoPointRem
  ring

/-! ### The Calvo mixture of distributions on `ℝ` (measure version) -/

/-- Woodford (2003), p. 695: a cross-sectional distribution of log prices is admissible when
it is a probability measure with finite first and second moments (restated from the Galí
Chapter 4 project). -/
def GoodDist (ν : Measure ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ Integrable (fun x => x) ν ∧ Integrable (fun x => x ^ 2) ν


/-- Woodford (2003), App. E.2, p. 695 and (2.23)–(2.24), p. 402 (measure version): the
cross-section of log prices after one period of staggered pricing,
`ν_t = α (ν_{t−1} ∘ (x ↦ x + d)⁻¹) + (1 − α) δ_{p*_t}`: a fraction `α` of prices is not
reoptimised and is raised by the indexation increment `d` (`d = γ π_{t−1}`; `d = 0` is the
Calvo model, "`α` times the distribution of prices in the previous period, plus an atom of size
`1 − α` at `p*_t`"), the rest is set at `p*_t`. -/
noncomputable def calvoMixIdx (α d : ℝ) (ν : Measure ℝ) (p : ℝ) : Measure ℝ :=
  ENNReal.ofReal α • ν.map (fun x => x + d) + ENNReal.ofReal (1 - α) • Measure.dirac p

/-- Woodford (2003), App. E.2, p. 695 and p. 402: integrating against the Calvo mixture,
`∫ f d(mixture) = α ∫ f(x + d) dν + (1 − α) f(p)` whenever `f(· + d)` is `ν`-integrable (no
regularity of `f` is needed: the shift is a measurable equivalence). -/
theorem integral_calvoMixIdx {ν : Measure ℝ} {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (d p : ℝ)
    {f : ℝ → ℝ} (hf : Integrable (fun x => f (x + d)) ν) :
    ∫ x, f x ∂(calvoMixIdx α d ν p) = α * ∫ x, f (x + d) ∂ν + (1 - α) * f p := by
  have hmap : Integrable f (ν.map (MeasurableEquiv.addRight d)) :=
    (integrable_map_equiv (MeasurableEquiv.addRight d) f).mpr hf
  change ∫ x, f x ∂(ENNReal.ofReal α • ν.map (MeasurableEquiv.addRight d) +
    ENNReal.ofReal (1 - α) • Measure.dirac p) = _
  rw [integral_add_measure (hmap.smul_measure ENNReal.ofReal_ne_top)
    ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_map_equiv, integral_dirac,
    ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (by linarith)]
  simp [smul_eq_mul]

/-- Woodford (2003), App. E.2, p. 695: the Calvo mixture preserves integrability of `f` when
`f(· + d)` is integrable. -/
theorem integrable_calvoMixIdx {ν : Measure ℝ} (α d p : ℝ) {f : ℝ → ℝ}
    (hf : Integrable (fun x => f (x + d)) ν) : Integrable f (calvoMixIdx α d ν p) :=
  ((integrable_map_equiv (MeasurableEquiv.addRight d) f).mpr hf).smul_measure
    ENNReal.ofReal_ne_top |>.add_measure ((integrable_dirac (by simp)).smul_measure
    ENNReal.ofReal_ne_top)

/-- Woodford (2003), p. 402: the indexed Calvo mixture of an admissible distribution is
admissible. -/
theorem calvoMixIdx_good {ν : Measure ℝ} {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (d p : ℝ)
    (hg : GoodDist ν) : GoodDist (calvoMixIdx α d ν p) := by
  obtain ⟨hp, hi1, hi2⟩ := hg
  have hm : AEMeasurable (fun x : ℝ => x + d) ν := (measurable_add_const d).aemeasurable
  have hprob : IsProbabilityMeasure (ν.map fun x => x + d) :=
    (Measure.isProbabilityMeasure_map_iff hm).2 hp
  have j1 : Integrable (fun x => x + d) ν := hi1.add (integrable_const d)
  have j2 : Integrable (fun x => (x + d) ^ 2) ν := by
    have : (fun x : ℝ => (x + d) ^ 2) = fun x => x ^ 2 + 2 * d * x + d ^ 2 := by
      funext x; ring
    rw [this]
    exact (hi2.add (hi1.const_mul _)).add (integrable_const _)
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · rw [calvoMixIdx, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ,
      measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      ← ENNReal.ofReal_add h0 (by linarith)]
    simp
  · exact (((integrable_map_measure continuous_id.aestronglyMeasurable hm).2 j1).smul_measure
      ENNReal.ofReal_ne_top).add_measure
      ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
  · exact (((integrable_map_measure (continuous_pow 2).aestronglyMeasurable hm).2 j2).smul_measure
      ENNReal.ofReal_ne_top).add_measure
      ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)

/-- Woodford (2003), p. 402 (exact): under indexation the mean log price moves as
`P̄_t = α (P̄_{t−1} + d) + (1 − α) p*_t`. -/
theorem calvoMixIdx_mean {ν : Measure ℝ} {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (d p : ℝ)
    (hg : GoodDist ν) :
    crossMean (calvoMixIdx α d ν p) (fun x => x) =
      α * (crossMean ν (fun x => x) + d) + (1 - α) * p := by
  have := hg.1
  change ∫ x, x ∂(calvoMixIdx α d ν p) = α * (∫ x, x ∂ν + d) + (1 - α) * p
  have e := integral_add (μ := ν) (f := fun x => x) (g := fun _ => d) hg.2.1
    (integrable_const d)
  rw [integral_calvoMixIdx (f := fun x => x) h0 h1 d p
      (hg.2.1.add (integrable_const d)), e,
    integral_const]
  simp

/-- Woodford (2003), eq. (2.24), p. 402 (**measure version, exact**): for `0 ≤ α < 1`,
`Δ_t = α Δ_{t−1} + (α/(1−α))(P̄_t − P̄_{t−1} − d)²` for the indexed mixture
`α (ν_{t−1} shifted by d) + (1 − α) δ_{p*}`, with `d = γ π_{t−1}`. -/
theorem calvoMixIdx_var_meanChange {ν : Measure ℝ} {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1)
    (d p : ℝ) (hg : GoodDist ν) :
    crossVar (calvoMixIdx α d ν p) (fun x => x) = α * crossVar ν (fun x => x) +
      α / (1 - α) * (crossMean (calvoMixIdx α d ν p) (fun x => x) -
        crossMean ν (fun x => x) - d) ^ 2 := by
  have hg' := calvoMixIdx_good h0 h1.le d p hg
  have := hg.1
  have := hg'.1
  have j2 : Integrable (fun x => (x + d) ^ 2) ν := by
    have : (fun x : ℝ => (x + d) ^ 2) = fun x => x ^ 2 + 2 * d * x + d ^ 2 := by
      funext x; ring
    rw [this]
    exact (hg.2.2.add (hg.2.1.const_mul _)).add (integrable_const _)
  have hs : ∫ x, x ^ 2 ∂(calvoMixIdx α d ν p) =
      α * (∫ x, x ^ 2 ∂ν + 2 * d * crossMean ν (fun x => x) + d ^ 2) + (1 - α) * p ^ 2 := by
    rw [integral_calvoMixIdx h0 h1.le d p j2]
    have : (fun x : ℝ => (x + d) ^ 2) = fun x => x ^ 2 + 2 * d * x + d ^ 2 := by
      funext x; ring
    have e1 := integral_add (μ := ν) (f := fun x => x ^ 2 + 2 * d * x) (g := fun _ => d ^ 2)
      (hg.2.2.add (hg.2.1.const_mul _)) (integrable_const _)
    have e2 := integral_add (μ := ν) (f := fun x => x ^ 2) (g := fun x => 2 * d * x)
      hg.2.2 (hg.2.1.const_mul _)
    rw [this, e1, e2, integral_const_mul, integral_const]
    simp [crossMean]
  rw [crossVar_eq _ hg'.2.1 hg'.2.2, crossVar_eq _ hg.2.1 hg.2.2]
  exact mix_var_meanChange h1.ne (calvoMixIdx_mean h0 h1.le d p hg) hs

/-! ### The Calvo step for a population of goods -/

/-- Woodford (2003), p. 695 and (2.24), p. 402 (**goods-population version, exact**): suppose
the goods in a measurable reset set `R` of measure `1 − α` all set the log price `p`, the
others keep their old log price raised by the indexation adjustment `d`, and the non-resetting
goods are representative of the old cross-section (their first and second moments are `α`
times the population moments: the Calvo assumption that the probability of a price change is
independent of the price). Then
`P̄_t = α (P̄_{t−1} + d) + (1−α) p` and
`Δ_t = α Δ_{t−1} + (α/(1−α)) (P̄_t − P̄_{t−1} − d)²`. -/
theorem goods_index_var (μ : Measure G) [IsProbabilityMeasure μ] {R : Set G}
    (hR : MeasurableSet R) {α p d : ℝ} (hα : α ≠ 1) (hRm : μ.real R = 1 - α)
    {xo xn : G → ℝ} (h1 : Integrable xo μ) (h2 : Integrable (fun i => xo i ^ 2) μ)
    (hrep1 : ∫ i in Rᶜ, xo i ∂μ = α * ∫ i, xo i ∂μ)
    (hrep2 : ∫ i in Rᶜ, xo i ^ 2 ∂μ = α * ∫ i, xo i ^ 2 ∂μ)
    (hn1 : ∀ i ∈ R, xn i = p) (hn2 : ∀ i ∉ R, xn i = xo i + d) :
    crossMean μ xn = α * (crossMean μ xo + d) + (1 - α) * p ∧
      crossVar μ xn = α * crossVar μ xo +
        α / (1 - α) * (crossMean μ xn - crossMean μ xo - d) ^ 2 := by
  have hc : μ.real Rᶜ = α := by rw [measureReal_compl hR, probReal_univ, hRm]; ring
  obtain ⟨i1, e1⟩ := integral_reset μ hR (xo := fun i => xo i + d) hn1 hn2 (f := fun z => z)
    (h1.add (integrable_const d))
  obtain ⟨i2, e2⟩ := integral_reset μ hR (xo := fun i => xo i + d) hn1 hn2
    (f := fun z => z ^ 2)
    (by
      have : (fun i => (xo i + d) ^ 2) = fun i => xo i ^ 2 + 2 * d * xo i + d ^ 2 := by
        funext i; ring
      rw [this]
      exact (h2.add (h1.const_mul _)).add (integrable_const _))
  have s1 : ∫ i in Rᶜ, (xo i + d) ∂μ = α * crossMean μ xo + α * d := by
    have e3 := integral_add (μ := μ.restrict Rᶜ) (f := fun i => xo i) (g := fun _ => d)
      h1.integrableOn (integrable_const d).integrableOn
    rw [e3, setIntegral_const, hc, hrep1, smul_eq_mul]
    rfl
  have s2 : ∫ i in Rᶜ, (xo i + d) ^ 2 ∂μ =
      α * ∫ i, xo i ^ 2 ∂μ + 2 * d * (α * crossMean μ xo) + α * d ^ 2 := by
    have : (fun i => (xo i + d) ^ 2) = fun i => xo i ^ 2 + 2 * d * xo i + d ^ 2 := by
      funext i; ring
    have e3 := integral_add (μ := μ.restrict Rᶜ) (f := fun i => xo i ^ 2 + 2 * d * xo i)
      (g := fun _ => d ^ 2)
      (show Integrable (fun i => xo i ^ 2 + 2 * d * xo i) μ from
        h2.add (h1.const_mul _)).integrableOn
      (integrable_const _).integrableOn
    have e4 := integral_add (μ := μ.restrict Rᶜ) (f := fun i => xo i ^ 2)
      (g := fun i => 2 * d * xo i) h2.integrableOn (h1.const_mul _).integrableOn
    rw [this, e3, e4, integral_const_mul, setIntegral_const, hc, hrep1, hrep2, smul_eq_mul]
    unfold crossMean
    ring
  rw [s1, hRm] at e1
  rw [s2, hRm] at e2
  have hm : crossMean μ xn = α * (crossMean μ xo + d) + (1 - α) * p := by
    unfold crossMean at e1 ⊢
    rw [e1]
    ring
  refine ⟨hm, ?_⟩
  rw [crossVar_eq μ i1 i2, crossVar_eq μ h1 h2]
  exact mix_var_meanChange hα hm (by rw [e2]; ring)

/-- Woodford (2003), eq. (E.8), p. 695 (**goods-population version of the Calvo step,
exact**): with no indexation (`d = 0`),
`Δ_t = α Δ_{t−1} + (α/(1−α)) (P̄_t − P̄_{t−1})²`. -/
theorem goods_calvo_var (μ : Measure G) [IsProbabilityMeasure μ] {R : Set G}
    (hR : MeasurableSet R) {α p : ℝ} (hα : α ≠ 1) (hRm : μ.real R = 1 - α)
    {xo xn : G → ℝ} (h1 : Integrable xo μ) (h2 : Integrable (fun i => xo i ^ 2) μ)
    (hrep1 : ∫ i in Rᶜ, xo i ∂μ = α * ∫ i, xo i ∂μ)
    (hrep2 : ∫ i in Rᶜ, xo i ^ 2 ∂μ = α * ∫ i, xo i ^ 2 ∂μ)
    (hn1 : ∀ i ∈ R, xn i = p) (hn2 : ∀ i ∉ R, xn i = xo i) :
    crossMean μ xn = α * crossMean μ xo + (1 - α) * p ∧
      crossVar μ xn = α * crossVar μ xo +
        α / (1 - α) * (crossMean μ xn - crossMean μ xo) ^ 2 := by
  have h := goods_index_var μ hR (d := 0) hα hRm h1 h2 hrep1 hrep2 hn1
    (fun i hi => by rw [hn2 i hi, add_zero])
  simpa using h

/-! ### The discounted dispersion (p. 400) -/

/-- Woodford (2003), p. 400, display after (2.20) (**exact form**): for the Calvo recursion
`Δ_t = α Δ_{t−1} + (α/(1−α)) π_t²` (index `t + 1` is date `t`, `D 0 = Δ_{−1}`,
`infl (t+1) = π_t`) with bounded inflation, `0 ≤ α < 1`, `0 ≤ β < 1`:
`∑ βᵗ Δ_t = (α/((1−α)(1−αβ))) ∑ βᵗ π_t² + α Δ_{−1}/(1−αβ)`, the last term depending only on
the initial dispersion (t.i.p.). -/
theorem disp_discounted_calvo {α β M : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {D infl : ℕ → ℝ} (hM : ∀ t, |infl t| ≤ M)
    (hrec : ∀ t, D (t + 1) = α * D t + α / (1 - α) * infl (t + 1) ^ 2) :
    Summable (fun t => β ^ t * infl (t + 1) ^ 2) ∧
    HasSum (fun t => β ^ t * D (t + 1))
      (α / ((1 - α) * (1 - α * β)) * ∑' t, β ^ t * infl (t + 1) ^ 2 +
        α * D 0 / (1 - α * β)) := by
  have hαβ : α * β < 1 := by nlinarith
  have hq : Summable fun t => ‖β ^ t * infl (t + 1) ^ 2‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun t => ?_)
      ((summable_geometric_of_lt_one hβ0 hβ1).mul_left (M ^ 2))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 _), abs_pow, mul_comm]
    have h1 : |infl (t + 1)| ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (hM (t + 1)) 2
    exact mul_le_mul_of_nonneg_right h1 (pow_nonneg hβ0 _)
  refine ⟨hq.of_norm, ?_⟩
  have h := Sequences.disp_discounted_hasSum hα0 hβ0 hαβ hrec hq
  have hne : (1 : ℝ) - α ≠ 0 := by linarith
  have hne2 : (1 : ℝ) - α * β ≠ 0 := by linarith
  convert h using 1
  field_simp
  ring

/-! ### Log-mean-exp: the CES aggregate (2.6) and the Dixit–Stiglitz price index -/

/-- Woodford (2003), eq. (2.6), p. 393, in logs: `logMeanExp μ r x = (1/r) log ∫ e^{r x(i)} di`.
With `r = (θ−1)/θ` and `x = ŷ` it is `Ŷ = log(Y/Ȳ)` (`log_ces_eq`); with `r = 1 − θ` and
`x = log p` it is the log of the Dixit–Stiglitz price index `log P`. -/
noncomputable def logMeanExp (μ : Measure G) (r : ℝ) (x : G → ℝ) : ℝ :=
  Real.log (∫ i, Real.exp (r * x i) ∂μ) / r

/-- Woodford (2003), eq. (2.6), p. 393: the Dixit–Stiglitz (CES) aggregate
`(∫ y(i)^r di)^{1/r}`, `r = (θ−1)/θ`. -/
noncomputable def cesAgg (μ : Measure G) (r : ℝ) (y : G → ℝ) : ℝ := (∫ i, y i ^ r ∂μ) ^ r⁻¹

/-- Woodford (2003), (2.6) and p. 394: with `y(i) = Ȳ e^{ŷ(i)}`,
`Ŷ = log(Y/Ȳ) = logMeanExp μ r ŷ`. -/
theorem log_ces_eq (μ : Measure G) [IsProbabilityMeasure μ] {r Ybar : ℝ} (hr : r ≠ 0)
    (hY : 0 < Ybar) {yh : G → ℝ} (hint : Integrable (fun i => Real.exp (r * yh i)) μ) :
    Real.log (cesAgg μ r (fun i => Ybar * Real.exp (yh i)) / Ybar) = logMeanExp μ r yh := by
  have hpt : ∀ i, (Ybar * Real.exp (yh i)) ^ r = Ybar ^ r * Real.exp (r * yh i) := by
    intro i
    rw [Real.mul_rpow hY.le (Real.exp_pos _).le, ← Real.exp_mul, mul_comm (yh i)]
  have hI := integral_exp_pos (μ := μ) (f := fun i => r * yh i) hint
  unfold cesAgg logMeanExp
  simp_rw [hpt]
  rw [integral_const_mul, Real.mul_rpow (Real.rpow_nonneg hY.le _) hI.le,
    Real.rpow_rpow_inv hY.le hr, mul_div_cancel_left₀ _ hY.ne', Real.log_rpow hI]
  field_simp

/-- A bounded measurable function on a finite measure space is integrable. -/
theorem integrable_of_abs_le (μ : Measure G) [IsFiniteMeasure μ] {f : G → ℝ}
    (hf : Measurable f) {K : ℝ} (hK : ∀ i, |f i| ≤ K) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable K
    (Eventually.of_forall fun i => by rw [Real.norm_eq_abs]; exact hK i)

/-- The centred moments used by the log-mean-exp bounds: for a measurable cross-section within
`B` of its mean, `x`, `x − m`, `(x − m)²`, `e^{r(x−m)}` are integrable, `E(x − m) = 0` and
`(x − m)² ≤ B²`. -/
theorem centred_facts (μ : Measure G) [IsProbabilityMeasure μ] {x : G → ℝ} (hx : Measurable x)
    {B : ℝ} (hB : ∀ i, |x i - crossMean μ x| ≤ B) (r : ℝ) :
    Integrable x μ ∧ Integrable (fun i => x i - crossMean μ x) μ ∧
      Integrable (fun i => (x i - crossMean μ x) ^ 2) μ ∧
      Integrable (fun i => Real.exp (r * (x i - crossMean μ x))) μ ∧
      ∫ i, (x i - crossMean μ x) ∂μ = 0 ∧ crossVar μ x ≤ B ^ 2 := by
  set m := crossMean μ x with hm
  have hx1 : Integrable x μ := integrable_of_abs_le μ hx (K := |m| + B) fun i => by
    have := hB i
    have := abs_sub_abs_le_abs_sub (x i) m
    linarith
  have hz : Measurable fun i => x i - m := hx.sub_const m
  have hz1 : Integrable (fun i => x i - m) μ := hx1.sub (integrable_const m)
  have hz2 : Integrable (fun i => (x i - m) ^ 2) μ := integrable_of_abs_le μ (hz.pow_const 2)
    (K := B ^ 2) fun i => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hB i) 2
  have hze : Integrable (fun i => Real.exp (r * (x i - m))) μ :=
    integrable_of_abs_le μ (measurable_const.mul hz).exp (K := Real.exp (|r| * B)) fun i => by
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc r * (x i - m) ≤ |r * (x i - m)| := le_abs_self _
        _ = |r| * |x i - m| := abs_mul _ _
        _ ≤ |r| * B := mul_le_mul_of_nonneg_left (hB i) (abs_nonneg r)
  have h0 : ∫ i, (x i - m) ∂μ = 0 := by
    rw [integral_sub hx1 (integrable_const m), integral_const]
    simp [hm, crossMean]
  have hV : crossVar μ x ≤ B ^ 2 := by
    unfold crossVar
    rw [← hm]
    have := integral_mono hz2 (integrable_const (B ^ 2)) fun i => by
      change (x i - m) ^ 2 ≤ B ^ 2
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hB i) 2
    simpa using this
  exact ⟨hx1, hz1, hz2, hze, h0, hV⟩

/-- Woodford (2003), p. 695: `logMeanExp μ r x = P̄ + (1/r) log ∫ e^{r(x(i) − P̄)} di` with
`P̄ = E_i x(i)`: the CES index is the mean plus a "cumulant" term. -/
theorem logMeanExp_center (μ : Measure G) [IsProbabilityMeasure μ] {x : G → ℝ}
    (hx : Measurable x) {B r : ℝ} (hB : ∀ i, |x i - crossMean μ x| ≤ B) (hr : r ≠ 0) :
    logMeanExp μ r x = crossMean μ x +
      Real.log (∫ i, Real.exp (r * (x i - crossMean μ x)) ∂μ) / r := by
  obtain ⟨-, -, -, hze, -, -⟩ := centred_facts μ hx hB r
  have hI := integral_exp_pos hze
  have hpt : ∀ i, Real.exp (r * x i) =
      Real.exp (r * crossMean μ x) * Real.exp (r * (x i - crossMean μ x)) := by
    intro i
    rw [← Real.exp_add]
    ring_nf
  unfold logMeanExp
  simp_rw [hpt]
  rw [integral_const_mul, Real.log_mul (Real.exp_pos _).ne' hI.ne', Real.log_exp]
  field_simp

/-- Woodford (2003), p. 695 (Jensen): `∫ e^{r(x − P̄)} ≥ 1`. -/
theorem one_le_integral_exp_center (μ : Measure G) [IsProbabilityMeasure μ] {x : G → ℝ}
    (hx : Measurable x) {B : ℝ} (hB : ∀ i, |x i - crossMean μ x| ≤ B) (r : ℝ) :
    1 ≤ ∫ i, Real.exp (r * (x i - crossMean μ x)) ∂μ := by
  obtain ⟨-, hz1, -, hze, h0, -⟩ := centred_facts μ hx hB r
  have h := integral_mono (f := fun i => 1 + r * (x i - crossMean μ x))
    ((integrable_const 1).add (hz1.const_mul r)) hze fun i => by
    change 1 + r * (x i - crossMean μ x) ≤ Real.exp (r * (x i - crossMean μ x))
    linarith [Real.add_one_le_exp (r * (x i - crossMean μ x))]
  rw [integral_add (integrable_const 1) (hz1.const_mul r), integral_const_mul, h0] at h
  simpa using h

/-- Woodford (2003), p. 695 (**`P̄_t = log P_t + O(Δ)`, exact bound**): if the log prices lie
within `B` of their mean `P̄` and `|r| B ≤ 1`, then
`|logMeanExp μ r x − P̄| ≤ |r| var_i x(i)`. With `r = 1 − θ` this is
`|log P_t − P̄_t| ≤ |1 − θ| Δ_t`, the book's `P̄_t = log P_t + O(‖Δ^{1/2}, φ, ξ‖²)`. -/
theorem logMeanExp_sub_mean_le (μ : Measure G) [IsProbabilityMeasure μ] {x : G → ℝ}
    (hx : Measurable x) {B r : ℝ} (hB : ∀ i, |x i - crossMean μ x| ≤ B) (hr : r ≠ 0)
    (hrB : |r| * B ≤ 1) :
    |logMeanExp μ r x - crossMean μ x| ≤ |r| * crossVar μ x := by
  obtain ⟨-, hz1, hz2, hze, h0, -⟩ := centred_facts μ hx hB r
  have hlow := one_le_integral_exp_center μ hx hB r
  set m := crossMean μ x with hm
  set I := ∫ i, Real.exp (r * (x i - m)) ∂μ with hIdef
  have hup : I ≤ 1 + r ^ 2 * crossVar μ x := by
    have hint : Integrable (fun i => 1 + r * (x i - m) + r ^ 2 * (x i - m) ^ 2) μ :=
      ((integrable_const 1).add (hz1.const_mul r)).add (hz2.const_mul _)
    have h := integral_mono hze hint fun i => by
      have hb : |r * (x i - m)| ≤ 1 := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left (hB i) (abs_nonneg r)).trans hrB
      have := Real.abs_exp_sub_one_sub_id_le hb
      have := (abs_le.mp this).2
      change Real.exp (r * (x i - m)) ≤ 1 + r * (x i - m) + r ^ 2 * (x i - m) ^ 2
      nlinarith
    have e1 := integral_add (μ := μ) (f := fun i => 1 + r * (x i - m))
      (g := fun i => r ^ 2 * (x i - m) ^ 2) ((integrable_const 1).add (hz1.const_mul r))
      (hz2.const_mul _)
    have e2 := integral_add (μ := μ) (f := fun _ => (1 : ℝ)) (g := fun i => r * (x i - m))
      (integrable_const 1) (hz1.const_mul r)
    rw [e1, e2, integral_const_mul, integral_const_mul, h0] at h
    simpa [crossVar, ← hm] using h
  rw [logMeanExp_center μ hx hB hr, add_sub_cancel_left, abs_div]
  have hlog0 : 0 ≤ Real.log I := Real.log_nonneg hlow
  have hlog1 : Real.log I ≤ r ^ 2 * crossVar μ x := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < I)
    linarith
  have hra : 0 < |r| := abs_pos.mpr hr
  rw [abs_of_nonneg hlog0, div_le_iff₀ hra]
  have : r ^ 2 = |r| * |r| := by rw [← sq_abs, sq]
  calc Real.log I ≤ r ^ 2 * crossVar μ x := hlog1
    _ = |r| * crossVar μ x * |r| := by rw [this]; ring

/-- Woodford (2003), eq. (E.5), p. 694, and p. 695 (**the second-order CES expansion with an
explicit cubic bound**): if the cross-section lies within `B` of its mean and `|r| B ≤ 1/2`,
then `|logMeanExp μ r x − E_i x − (r/2) var_i x| ≤ r² B var_i x`, a term of weighted degree
three (`B` of order one, the variance of order two). With `r = 1 − θ⁻¹`, `x = ŷ` this is
(E.5): `Ŷ = E_i ŷ + ½(1 − θ⁻¹) var_i ŷ + O(‖ŷ‖³)`. -/
theorem logMeanExp_second_order (μ : Measure G) [IsProbabilityMeasure μ] {x : G → ℝ}
    (hx : Measurable x) {B r : ℝ} (hB : ∀ i, |x i - crossMean μ x| ≤ B) (hr : r ≠ 0)
    (hrB : |r| * B ≤ 1 / 2) :
    |logMeanExp μ r x - crossMean μ x - r / 2 * crossVar μ x| ≤ r ^ 2 * B * crossVar μ x := by
  obtain ⟨-, hz1, hz2, hze, h0, hVB⟩ := centred_facts μ hx hB r
  have hlow := one_le_integral_exp_center μ hx hB r
  set m := crossMean μ x with hm
  set V := crossVar μ x with hVdef
  set I := ∫ i, Real.exp (r * (x i - m)) ∂μ with hIdef
  have hV0 : 0 ≤ V := crossVar_nonneg μ x
  have := nonempty_of_isProbabilityMeasure μ
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (Classical.arbitrary G))
  have hra : 0 < |r| := abs_pos.mpr hr
  have hr2 : r ^ 2 = |r| * |r| := by rw [← sq_abs, sq]
  -- the cubic remainder of the exponential, pointwise
  set ρ : G → ℝ := fun i => Real.exp (r * (x i - m)) - 1 - r * (x i - m) -
    (r * (x i - m)) ^ 2 / 2 with hρ
  have hρint : Integrable ρ μ :=
    ((hze.sub (integrable_const 1)).sub (hz1.const_mul r)).sub
      ((hz2.const_mul (r ^ 2 / 2)).congr (Eventually.of_forall fun i => by
        change r ^ 2 / 2 * (x i - m) ^ 2 = (r * (x i - m)) ^ 2 / 2
        ring))
  have hρb : ∀ i, |ρ i| ≤ |r| * B / 4 * (r ^ 2 * (x i - m) ^ 2) := by
    intro i
    have hb : |r * (x i - m)| ≤ |r| * B := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hB i) (abs_nonneg r)
    have h1 : |Real.exp (r * (x i - m)) - 1 - r * (x i - m) - (r * (x i - m)) ^ 2 / 2| ≤
        |r * (x i - m)| ^ 3 / 4 := by
      have h2 := ExpLogCES.abs_expRem_le (x := r * (x i - m)) (hb.trans (by linarith))
      unfold ExpLogCES.expRem at h2
      have : 0 ≤ |r * (x i - m)| ^ 3 := by positivity
      linarith
    refine h1.trans ?_
    have e : |r * (x i - m)| ^ 3 = |r * (x i - m)| * (r ^ 2 * (x i - m) ^ 2) := by
      rw [pow_succ, mul_comm, ← mul_pow, sq_abs]
    rw [e]
    have : 0 ≤ r ^ 2 * (x i - m) ^ 2 := by positivity
    nlinarith
  have hIeq : I = 1 + r ^ 2 / 2 * V + ∫ i, ρ i ∂μ := by
    have hpt : (fun i => Real.exp (r * (x i - m))) =
        fun i => (1 + r * (x i - m) + r ^ 2 / 2 * (x i - m) ^ 2) + ρ i := by
      funext i
      simp only [hρ]
      ring
    rw [hIdef, hpt]
    have e1 := integral_add (μ := μ) (f := fun i => 1 + r * (x i - m) +
      r ^ 2 / 2 * (x i - m) ^ 2) (g := ρ)
      (((integrable_const 1).add (hz1.const_mul r)).add (hz2.const_mul _)) hρint
    have e2 := integral_add (μ := μ) (f := fun i => 1 + r * (x i - m))
      (g := fun i => r ^ 2 / 2 * (x i - m) ^ 2) ((integrable_const 1).add (hz1.const_mul r))
      (hz2.const_mul _)
    have e3 := integral_add (μ := μ) (f := fun _ => (1 : ℝ)) (g := fun i => r * (x i - m))
      (integrable_const 1) (hz1.const_mul r)
    rw [e1, e2, e3, integral_const_mul, integral_const_mul, h0]
    simp [hVdef, crossVar, ← hm]
  -- the bound on the integrated remainder
  have hρI : |∫ i, ρ i ∂μ| ≤ |r| * B / 4 * (r ^ 2 * V) := by
    have h := norm_integral_le_of_norm_le ((hz2.const_mul (r ^ 2)).const_mul (|r| * B / 4))
      (Eventually.of_forall fun i => by rw [Real.norm_eq_abs]; exact hρb i)
    rw [Real.norm_eq_abs, integral_const_mul, integral_const_mul] at h
    simpa [hVdef, crossVar, ← hm] using h
  set u := I - 1 with hu
  have hrV : r ^ 2 * V ≤ 1 / 4 := by
    have : r ^ 2 * V ≤ r ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_left hVB (sq_nonneg r)
    have h2 : r ^ 2 * B ^ 2 = (|r| * B) ^ 2 := by rw [mul_pow, sq_abs]
    have h3 : (|r| * B) ^ 2 ≤ (1 / 2) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (abs_nonneg r) hB0) hrB 2
    linarith
  have hrBV : |r| * B / 4 * (r ^ 2 * V) ≤ 1 / 8 * (r ^ 2 * V) := by
    have : 0 ≤ r ^ 2 * V := mul_nonneg (sq_nonneg r) hV0
    nlinarith
  have hu_le : |u| ≤ 5 / 8 * (r ^ 2 * V) := by
    have : u = r ^ 2 / 2 * V + ∫ i, ρ i ∂μ := by rw [hu, hIeq]; ring
    rw [this]
    have := abs_add_le (r ^ 2 / 2 * V) (∫ i, ρ i ∂μ)
    have hp : |r ^ 2 / 2 * V| = r ^ 2 / 2 * V := abs_of_nonneg (by positivity)
    linarith
  have hu_half : |u| ≤ 1 / 2 := by nlinarith
  have hlog : |Real.log I - u| ≤ 2 * u ^ 2 := by
    have h := ExpLogCES.abs_log_one_sub_add_le (x := -u) (by rw [abs_neg]; linarith)
    simp only [sub_neg_eq_add, abs_neg, neg_sq] at h
    have hI1 : 1 + u = I := by rw [hu]; ring
    rw [hI1] at h
    have e : Real.log I - u = Real.log I + -u := by ring
    rw [e]
    refine h.trans ?_
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ u ^ 2 := sq_nonneg u
    nlinarith [mul_nonneg this (by linarith : (0 : ℝ) ≤ 1 / 2 - |u|)]
  -- assemble
  have hmain : |Real.log I - r ^ 2 / 2 * V| ≤ |r| ^ 3 * B * V := by
    have e : Real.log I - r ^ 2 / 2 * V = (Real.log I - u) + ∫ i, ρ i ∂μ := by
      rw [hu, hIeq]; ring
    rw [e]
    have h1 := abs_add_le (Real.log I - u) (∫ i, ρ i ∂μ)
    have hu2 : u ^ 2 ≤ (5 / 8 * (r ^ 2 * V)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg u) hu_le 2
    have hq : (r ^ 2 * V) ^ 2 ≤ |r| ^ 3 * B * V / 2 := by
      have h4 : r ^ 2 * V ≤ |r| * B * (|r| * B) := by
        have : r ^ 2 * V ≤ r ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_left hVB (sq_nonneg r)
        nlinarith
      have h5 : (r ^ 2 * V) ^ 2 = r ^ 2 * V * (r ^ 2 * V) := sq _
      have h6 : 0 ≤ r ^ 2 * V := mul_nonneg (sq_nonneg r) hV0
      have h7 : r ^ 2 * V * (r ^ 2 * V) ≤ r ^ 2 * V * (|r| * B * (|r| * B)) :=
        mul_le_mul_of_nonneg_left h4 h6
      have h8 : r ^ 2 * V * (|r| * B * (|r| * B)) = |r| ^ 3 * B * V * (|r| * B) := by
        rw [hr2]; ring
      have h9 : |r| ^ 3 * B * V * (|r| * B) ≤ |r| ^ 3 * B * V * (1 / 2) :=
        mul_le_mul_of_nonneg_left hrB (by positivity)
      linarith
    have hc : |r| * B / 4 * (r ^ 2 * V) = |r| ^ 3 * B * V / 4 := by rw [hr2]; ring
    nlinarith
  rw [logMeanExp_center μ hx hB hr]
  have e : crossMean μ x + Real.log I / r - crossMean μ x - r / 2 * V =
      (Real.log I - r ^ 2 / 2 * V) / r := by
    field_simp
    ring
  rw [← hm, ← hIdef]
  rw [show m + Real.log I / r - m - r / 2 * V = (Real.log I - r ^ 2 / 2 * V) / r by
    field_simp; ring]
  rw [abs_div, div_le_iff₀ hra]
  have : r ^ 2 * B * V * |r| = |r| ^ 3 * B * V := by rw [hr2]; ring
  linarith [e]

/-- Woodford (2003), p. 695 (an `O(1)` bound for (2.11)): if `|x(i)| ≤ B` for all goods, the
CES index satisfies `|logMeanExp μ r x| ≤ B`. In particular `ŷ = O(φ, ξ)` uniformly over goods
gives `Ŷ = O(φ, ξ)` and `var_i ŷ = O(φ, ξ)²`. -/
theorem abs_logMeanExp_le (μ : Measure G) [IsProbabilityMeasure μ] {x : G → ℝ}
    (hx : Measurable x) {B r : ℝ} (hB : ∀ i, |x i| ≤ B) (hr : r ≠ 0) :
    |logMeanExp μ r x| ≤ B := by
  have hra : 0 < |r| := abs_pos.mpr hr
  have hb : ∀ i, |r * x i| ≤ |r| * B := fun i => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB i) (abs_nonneg r)
  have hint : Integrable (fun i => Real.exp (r * x i)) μ :=
    integrable_of_abs_le μ (measurable_const.mul hx).exp (K := Real.exp (|r| * B)) fun i => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hb i))
  have hup := integral_mono hint (integrable_const (Real.exp (|r| * B))) fun i =>
    Real.exp_le_exp.mpr ((le_abs_self _).trans (hb i))
  have hlo := integral_mono (integrable_const (Real.exp (-(|r| * B)))) hint fun i =>
    Real.exp_le_exp.mpr (neg_le.mp ((neg_abs_le _).trans (hb i) |> fun h => by
      have := neg_abs_le (r * x i); have := hb i; linarith))
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hup hlo
  have hI : 0 < ∫ i, Real.exp (r * x i) ∂μ := integral_exp_pos hint
  have h1 : Real.log (∫ i, Real.exp (r * x i) ∂μ) ≤ |r| * B := by
    have := Real.log_le_log hI hup
    rwa [Real.log_exp] at this
  have h2 : -(|r| * B) ≤ Real.log (∫ i, Real.exp (r * x i) ∂μ) := by
    have := Real.log_le_log (Real.exp_pos _) hlo
    rwa [Real.log_exp] at this
  unfold logMeanExp
  rw [abs_div, div_le_iff₀ hra, abs_le]
  constructor <;> nlinarith [abs_le.mpr ⟨h2, h1⟩]

end Woodford.StabilizationWelfare.CrossSection
