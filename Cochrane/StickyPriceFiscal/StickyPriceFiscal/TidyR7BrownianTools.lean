/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.TidyR7BrownianExist
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Brownian tools for the Itô integral: filtration, independent increments, martingales, moments

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for (1.32) with diffusive
bonds (chunk I5a, for the quadratic variation I5b and the Itô integral I5c).

Everything is stated for ANY pre-Brownian motion `W` on any probability space (Mathlib's
`IsPreBrownianReal W P`; a Brownian motion `hB : IsBrownianReal W P` enters through
`hB.toIsPreBrownianReal`), with each `W t` measurable (`hW`; Mathlib's predicate gives only
a.e.-measurability, and the natural filtration needs measurability; the constructed motion
`TidyR7BrownianExist.bmPath` has it, `TidyR7BrownianExist.measurable_bmPath`).

## Gaussian moments
* `integral_sq_gaussianReal`, `integral_pow_four_gaussianReal`: `∫ x² dN(0,v) = v` and
  `∫ x⁴ dN(0,v) = 3v²` (derivatives of the moment generating function `exp(v t²/2)` at `0`).
* `integral_increment_sq`, `integral_increment_pow_four`, `integrable_increment_pow_four`:
  `E[(W t − W s)²] = |t − s|`, `E[(W t − W s)⁴] = 3(t − s)²`.

## Filtration and independence (index `ℝ≥0`, Mathlib's index for Brownian motion)
* `bmFiltration W hW` = Mathlib's `Filtration.natural`, `σ(W r, r ≤ t)`;
  `stronglyAdapted_bmFiltration`; `bmFiltration_eq_comap` (`σ` of the past path on `Iic t`).
* `indepFun_increment_past`, `indep_increment_bmFiltration`: for `s ≤ t`, `W t − W s` is
  independent of `𝓕_s` (from Mathlib's weak Markov property `IsPreBrownianReal.indepFun_shift`).
* `condExp_increment`: `E[W t − W s | 𝓕_s] = 0`; `condExp_increment_sq`:
  `E[(W t − W s)² | 𝓕_s] = t − s`.
* `martingale_bm`: `W` is a martingale; `martingale_bm_sq_sub`: `W t² − t` is a martingale.

## The bridge to the index `ℝ` of Track 1 (I1–I4)
* `bmReal W t = W (max t 0)` (`Real.toNNReal`), `bmFiltrationReal W hW t = 𝓕_{max t 0}`;
  `bmReal_of_nonneg`, `continuous_bmReal`, `martingale_bmReal`, `martingale_bmReal_sq_sub`.

## Non-vacuity
* `martingale_bmPath`, `martingale_bmPath_sq_sub`: the tools applied to the constructed motion.
-/

namespace Cochrane.StickyPriceFiscal.TidyR7BrownianTools

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.StickyPriceFiscal.TidyR7BrownianSchauder Cochrane.StickyPriceFiscal.TidyR7BrownianUnit
open Cochrane.StickyPriceFiscal.TidyR7BrownianExist
open scoped ENNReal NNReal

/-! ## Gaussian moments -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (tool for the quadratic variation in (1.32) with
diffusive bonds): the derivative of `exp(v x²/2)` is `v x exp(v x²/2)`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.hasDerivAt_gaussMgf). -/
lemma hasDerivAt_gaussMgf (v x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (0 * y + v * y ^ 2 / 2))
      (v * x * Real.exp (0 * x + v * x ^ 2 / 2)) x := by
  have p2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
  have h1 : HasDerivAt (fun y : ℝ => 0 * y + v * y ^ 2 / 2) (v * x) x :=
    (((hasDerivAt_id' x).const_mul (0 : ℝ)).add ((p2.const_mul v).div_const 2)).congr_deriv
      (by ring)
  exact h1.exp.congr_deriv (by ring)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: product rule for `p(x) exp(v x²/2)`, the shape of
every derivative of the Gaussian moment generating function.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.deriv_mul_gaussMgf). -/
lemma deriv_mul_gaussMgf (v : ℝ) (p p' : ℝ → ℝ) (hp : ∀ x, HasDerivAt p (p' x) x) :
    deriv (fun x => p x * Real.exp (0 * x + v * x ^ 2 / 2))
      = fun x => (p' x + p x * (v * x)) * Real.exp (0 * x + v * x ^ 2 / 2) := by
  funext x
  exact ((hp x).mul (hasDerivAt_gaussMgf v x)).deriv.trans (by ring)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the second and fourth derivatives at `0` of the
centred Gaussian moment generating function `exp(v t²/2)` are `v` and `3 v²`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.iteratedDeriv_gaussMgf). -/
theorem iteratedDeriv_gaussMgf (v : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => Real.exp (0 * x + v * x ^ 2 / 2)) 0 = v ∧
      iteratedDeriv 4 (fun x : ℝ => Real.exp (0 * x + v * x ^ 2 / 2)) 0 = 3 * v ^ 2 := by
  set E : ℝ → ℝ := fun x => Real.exp (0 * x + v * x ^ 2 / 2) with hE
  have e0 : E = fun x => 1 * E x := by funext x; ring
  have p2 : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := fun x => by
    simpa using hasDerivAt_pow 2 x
  have p3 : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := fun x => by
    simpa using hasDerivAt_pow 3 x
  have d1 : iteratedDeriv 1 E = fun x => (v * x) * E x := by
    rw [iteratedDeriv_one, e0, hE,
      deriv_mul_gaussMgf v (fun _ => 1) (fun _ => 0) fun x => hasDerivAt_const x _]
    funext x; ring
  have d2 : iteratedDeriv 2 E = fun x => (v + v ^ 2 * x ^ 2) * E x := by
    rw [iteratedDeriv_succ, d1, hE, deriv_mul_gaussMgf v (fun x => v * x) (fun _ => v)
      fun x => ((hasDerivAt_id' x).const_mul v).congr_deriv (mul_one v)]
    funext x; ring
  have d3 : iteratedDeriv 3 E = fun x => (3 * v ^ 2 * x + v ^ 3 * x ^ 3) * E x := by
    rw [iteratedDeriv_succ, d2, hE, deriv_mul_gaussMgf v (fun x => v + v ^ 2 * x ^ 2)
      (fun x => 2 * v ^ 2 * x) fun x =>
        (((p2 x).const_mul (v ^ 2)).const_add v).congr_deriv (by ring)]
    funext x; ring
  have d4 : iteratedDeriv 4 E
      = fun x => (3 * v ^ 2 + 6 * v ^ 3 * x ^ 2 + v ^ 4 * x ^ 4) * E x := by
    rw [iteratedDeriv_succ, d3, hE, deriv_mul_gaussMgf v (fun x => 3 * v ^ 2 * x + v ^ 3 * x ^ 3)
      (fun x => 3 * v ^ 2 + 3 * v ^ 3 * x ^ 2) fun x =>
        (((hasDerivAt_id' x).const_mul (3 * v ^ 2)).add ((p3 x).const_mul (v ^ 3))).congr_deriv
          (by ring)]
    funext x; ring
  refine ⟨?_, ?_⟩
  · rw [d2, hE]; simp
  · rw [d4, hE]; simp

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the second moment of `N(0, v)` is `v`.
The mean-zero form of Mathlib `variance_id_gaussianReal` with `integral_id_gaussianReal`; compare
`TidyR7BrownianUnit.variance_of_map_eq_gaussianReal`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.integral_sq_gaussianReal). -/
theorem integral_sq_gaussianReal (v : ℝ≥0) : ∫ x, x ^ 2 ∂gaussianReal 0 v = v := by
  have h := iteratedDeriv_mgf_zero (X := id) (μ := gaussianReal 0 v) (by simp) 2
  rw [mgf_id_gaussianReal, (iteratedDeriv_gaussMgf v).1] at h
  simpa using h.symm

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (tool for the quadratic variation in (1.32) with
diffusive bonds): the fourth moment of `N(0, v)` is `3 v²`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.integral_pow_four_gaussianReal). -/
theorem integral_pow_four_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 4 ∂gaussianReal 0 v = 3 * (v : ℝ) ^ 2 := by
  have h := iteratedDeriv_mgf_zero (X := id) (μ := gaussianReal 0 v) (by simp) 4
  rw [mgf_id_gaussianReal, (iteratedDeriv_gaussMgf v).2] at h
  simpa using h.symm

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `x ↦ x⁴` is integrable for `N(0, v)`.
Generalises `TidyR7BrownianSchauder.integrable_pow_four_gaussianReal` to `N(0, v)`; an instance of
Mathlib `memLp_id_gaussianReal'`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.integrable_pow_four_gaussianReal'). -/
lemma integrable_pow_four_gaussianReal' (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 v) := by
  have h := (memLp_id_gaussianReal' (μ := 0) (v := v) ((4 : ℕ) : ℝ≥0∞)
    (by simp)).integrable_norm_pow (by norm_num)
  simpa [Real.norm_eq_abs, Even.pow_abs (by decide : Even 4)] using h

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `nndist t s` as a real number is `|t − s|`.
Restates Mathlib `coe_nndist` with `NNReal.dist_eq`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.coe_nndist_val). -/
lemma coe_nndist_val (s t : ℝ≥0) : ((nndist t.1 s.1 : ℝ≥0) : ℝ) = |(t : ℝ) - s| := by
  rw [coe_nndist, Real.dist_eq]
  rfl

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (tool for (1.32) with diffusive bonds): for a
pre-Brownian motion, `E[(W t − W s)²] = |t − s|`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.integral_increment_sq). -/
theorem integral_increment_sq (hB : IsPreBrownianReal W P) (s t : ℝ≥0) :
    ∫ ω, (W t ω - W s ω) ^ 2 ∂P = |(t : ℝ) - s| := by
  have h := (hB.hasLaw_sub t s).integral_comp (f := fun x : ℝ => x ^ 2)
    (by fun_prop : Continuous fun x : ℝ => x ^ 2).aestronglyMeasurable
  rw [integral_sq_gaussianReal, coe_nndist_val] at h
  simpa [Function.comp_def] using h

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (tool for the quadratic variation in (1.32) with
diffusive bonds): for a pre-Brownian motion, `E[(W t − W s)⁴] = 3 (t − s)²`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.integral_increment_pow_four). -/
theorem integral_increment_pow_four (hB : IsPreBrownianReal W P) (s t : ℝ≥0) :
    ∫ ω, (W t ω - W s ω) ^ 4 ∂P = 3 * ((t : ℝ) - s) ^ 2 := by
  have h := (hB.hasLaw_sub t s).integral_comp (f := fun x : ℝ => x ^ 4)
    (by fun_prop : Continuous fun x : ℝ => x ^ 4).aestronglyMeasurable
  rw [integral_pow_four_gaussianReal, coe_nndist_val, sq_abs] at h
  simpa [Function.comp_def] using h

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the fourth power of an increment is integrable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.integrable_increment_pow_four). -/
theorem integrable_increment_pow_four (hB : IsPreBrownianReal W P) (s t : ℝ≥0) :
    Integrable (fun ω => (W t ω - W s ω) ^ 4) P := by
  have h := (hB.hasLaw_sub t s).integrable_comp (f := fun x : ℝ => x ^ 4)
    (integrable_pow_four_gaussianReal' _)
  simpa [Function.comp_def] using h

/-! ## The natural filtration and independent increments -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (information for `E_t` in (1.32) with diffusive
bonds): the natural filtration `𝓕_t = σ(W r, r ≤ t)` of a process with measurable values
(Mathlib's `Filtration.natural`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.bmFiltration). -/
noncomputable def bmFiltration (W : ℝ≥0 → Ω → ℝ) (hW : ∀ t, Measurable (W t)) :
    Filtration ℝ≥0 mΩ :=
  Filtration.natural (fun t => W t) fun t => (hW t).stronglyMeasurable

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `W` is adapted to its natural filtration.
Restates Mathlib `Filtration.stronglyAdapted_natural`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.stronglyAdapted_bmFiltration). -/
theorem stronglyAdapted_bmFiltration (hW : ∀ t, Measurable (W t)) :
    StronglyAdapted (bmFiltration W hW) W :=
  Filtration.stronglyAdapted_natural _

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `𝓕_s` is the σ-algebra generated by the past path
`(W r)_{r ≤ s}`.
Restates Mathlib `Filtration.natural_eq_comap`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.bmFiltration_eq_comap). -/
theorem bmFiltration_eq_comap (hW : ∀ t, Measurable (W t)) (s : ℝ≥0) :
    bmFiltration W hW s
      = MeasurableSpace.comap (fun ω (r : Set.Iic s) => W r ω) inferInstance :=
  Filtration.natural_eq_comap _ _ s

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (the Brownian increment is news): for `s ≤ t`,
`W t − W s` is independent of the past path `(W r)_{r ≤ s}`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.indepFun_increment_past). -/
theorem indepFun_increment_past (hB : IsPreBrownianReal W P) {s t : ℝ≥0} (hst : s ≤ t) :
    IndepFun (fun ω => W t ω - W s ω) (fun ω (r : Set.Iic s) => W r ω) P := by
  have h := (hB.indepFun_shift s).comp (φ := fun f : ℝ≥0 → ℝ => f (t - s)) (ψ := id)
    (measurable_pi_apply (X := fun _ : ℝ≥0 => ℝ) (t - s)) measurable_id
  have e : s + (t - s) = t := add_tsub_cancel_of_le hst
  simpa [Function.comp_def, e] using h

/-- Cochrane (2023), A1 §1.6, pp. 567–568: for `s ≤ t`, the σ-algebra of `W t − W s` is
independent of `𝓕_s`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.indep_increment_bmFiltration). -/
theorem indep_increment_bmFiltration (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun ω => W t ω - W s ω) inferInstance)
      (bmFiltration W hW s) P := by
  rw [bmFiltration_eq_comap, ← IndepFun_iff_Indep]
  exact indepFun_increment_past hB hst

/-- Cochrane (2023), A1 §1.6, pp. 567–568: conditional expectations given `𝓕_s` of functions of
the increment `W t − W s` are their unconditional means.
A special case of Mathlib `condExp_indep_eq`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.condExp_fun_increment). -/
lemma condExp_fun_increment (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    {s t : ℝ≥0} (hst : s ≤ t) (g : ℝ → ℝ) (hg : Measurable g) :
    P[fun ω => g (W t ω - W s ω) | bmFiltration W hW s]
      =ᵐ[P] fun _ => ∫ ω, g (W t ω - W s ω) ∂P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hle : MeasurableSpace.comap (fun ω => W t ω - W s ω) inferInstance ≤ mΩ :=
    measurable_iff_comap_le.1 ((hW t).sub (hW s))
  refine condExp_indep_eq hle ((bmFiltration W hW).le s) ?_
    (indep_increment_bmFiltration hB hW hst)
  exact (hg.comp (comap_measurable _)).stronglyMeasurable

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `E[W t − W s | 𝓕_s] = 0` for `s ≤ t`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.condExp_increment). -/
theorem condExp_increment (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω => W t ω - W s ω | bmFiltration W hW s] =ᵐ[P] 0 := by
  have h := condExp_fun_increment hB hW hst id measurable_id
  have hm : ∫ ω, (W t ω - W s ω) ∂P = 0 := by
    rw [integral_sub (hB.integrable_eval t) (hB.integrable_eval s), hB.integral_eval,
      hB.integral_eval, sub_zero]
  simp only [id] at h
  rw [hm] at h
  exact h

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (the quadratic variation increment): for `s ≤ t`,
`E[(W t − W s)² | 𝓕_s] = t − s`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.condExp_increment_sq). -/
theorem condExp_increment_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω => (W t ω - W s ω) ^ 2 | bmFiltration W hW s] =ᵐ[P] fun _ => (t : ℝ) - s := by
  have h := condExp_fun_increment hB hW hst (fun x => x ^ 2) (measurable_id.pow_const 2)
  rw [integral_increment_sq hB, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hst))] at h
  exact h

/-! ## Martingales -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (`E_t dW = 0`, the driftless integrator of (1.32)
with diffusive bonds): a pre-Brownian motion is a martingale for its natural filtration.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.martingale_bm). -/
theorem martingale_bm (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t)) :
    Martingale W (bmFiltration W hW) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨stronglyAdapted_bmFiltration hW, fun s t hst => ?_⟩
  have hint := hB.integrable_eval
  have hWs : P[W s | bmFiltration W hW s] = W s :=
    condExp_of_stronglyMeasurable ((bmFiltration W hW).le s) (stronglyAdapted_bmFiltration hW s)
      (hint s)
  have hsplit : W t - W s + W s = W t := sub_add_cancel _ _
  have hadd := condExp_add ((hint t).sub (hint s)) (hint s) (bmFiltration W hW s) (μ := P)
  rw [hsplit, hWs] at hadd
  have hinc : P[W t - W s | bmFiltration W hW s] =ᵐ[P] 0 := condExp_increment hB hW hst
  filter_upwards [hadd, hinc] with ω h1 h2
  rw [h1, Pi.add_apply, h2]
  simp

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (`E_t (dW)² = dt`): for a pre-Brownian motion,
`W t² − t` is a martingale for the natural filtration.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.martingale_bm_sq_sub). -/
theorem martingale_bm_sq_sub (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t)) :
    Martingale (fun t ω => W t ω ^ 2 - (t : ℝ)) (bmFiltration W hW) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hAd := stronglyAdapted_bmFiltration hW
  refine ⟨fun t => (((hAd t).measurable.pow_const 2).sub_const _).stronglyMeasurable,
    fun s t hst => ?_⟩
  set F := bmFiltration W hW s
  have hL2 : ∀ r, MemLp (W r) 2 P := fun r => (hB.isGaussianProcess.hasGaussianLaw_eval r).memLp_two
  have hD2 : MemLp (fun ω => W t ω - W s ω) 2 P := (hL2 t).sub (hL2 s)
  set A : Ω → ℝ := fun ω => (W t ω - W s ω) ^ 2 - ((t : ℝ) - s) with hA
  set B : Ω → ℝ := W s * fun ω => 2 * (W t ω - W s ω) with hBdef
  set C : Ω → ℝ := fun ω => W s ω ^ 2 - (s : ℝ) with hC
  have hsplit : (fun ω => W t ω ^ 2 - (t : ℝ)) = A + B + C := by
    funext ω; simp only [hA, hBdef, hC, Pi.add_apply, Pi.mul_apply]; ring
  have iA : Integrable A P := hD2.integrable_sq.sub (integrable_const _)
  have iG : Integrable (fun ω => 2 * (W t ω - W s ω)) P :=
    (hD2.integrable one_le_two).const_mul 2
  have iB : Integrable B P := (hL2 s).integrable_mul (hD2.const_mul 2)
  have iC : Integrable C P := (hL2 s).integrable_sq.sub (integrable_const _)
  have hA0 : P[A | F] =ᵐ[P] 0 := by
    have h := condExp_fun_increment hB hW hst (fun x => x ^ 2 - ((t : ℝ) - s))
      ((measurable_id.pow_const 2).sub_const _)
    have hm : ∫ ω, ((W t ω - W s ω) ^ 2 - ((t : ℝ) - s)) ∂P = 0 := by
      rw [integral_sub hD2.integrable_sq (integrable_const _), integral_increment_sq hB,
        abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hst)), integral_const]
      simp
    rw [hm] at h
    exact h
  have hG0 : P[fun ω => 2 * (W t ω - W s ω) | F] =ᵐ[P] 0 := by
    have h := condExp_fun_increment hB hW hst (fun x => 2 * x) (measurable_id.const_mul 2)
    have hm : ∫ ω, 2 * (W t ω - W s ω) ∂P = 0 := by
      rw [integral_const_mul, integral_sub (hB.integrable_eval t) (hB.integrable_eval s),
        hB.integral_eval, hB.integral_eval]
      simp
    rw [hm] at h
    exact h
  have hB0 : P[B | F] =ᵐ[P] 0 := by
    have h := condExp_mul_of_stronglyMeasurable_left (m := F) (hAd s) iB iG
    filter_upwards [h, hG0] with ω h1 h2
    rw [h1, Pi.mul_apply, h2]
    simp
  have hCC : P[C | F] = C :=
    condExp_of_stronglyMeasurable ((bmFiltration W hW).le s) (μ := P)
      ((((hAd s).measurable.pow_const 2).sub_const _).stronglyMeasurable) iC
  have h1 := condExp_add (iA.add iB) iC F (μ := P)
  have h2 := condExp_add iA iB F (μ := P)
  change P[fun ω => W t ω ^ 2 - (t : ℝ) | F] =ᵐ[P] fun ω => W s ω ^ 2 - (s : ℝ)
  rw [hsplit]
  filter_upwards [h1, h2, hA0, hB0] with ω e1 e2 e3 e4
  rw [e1, Pi.add_apply, e2, Pi.add_apply, e3, e4, hCC]
  simp [hC]

/-! ## The bridge to the time index `ℝ` -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (bridge to the `ℝ`-indexed paths of Track 1): the
process on `ℝ`, `t ↦ W (max t 0)`.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7BrownianTools.bmReal). -/
def bmReal (W : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ := W t.toNNReal ω

/-- Cochrane (2023), A1 §1.6, pp. 567–568: on `t ≥ 0`, `bmReal` is `W`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.bmReal_of_nonneg). -/
lemma bmReal_of_nonneg (W : ℝ≥0 → Ω → ℝ) {t : ℝ} (ht : 0 ≤ t) (ω : Ω) :
    bmReal W t ω = W ⟨t, ht⟩ ω := by
  rw [bmReal, Real.toNNReal_of_nonneg ht]
  rfl

/-- Cochrane (2023), A1 §1.6, pp. 567–568: continuous paths of `W` give continuous paths of
`bmReal W` on `ℝ`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.continuous_bmReal). -/
lemma continuous_bmReal {ω : Ω} (h : Continuous fun t => W t ω) :
    Continuous fun t => bmReal W t ω :=
  h.comp continuous_real_toNNReal

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (bridge to the index `ℝ`): the filtration
`t ↦ 𝓕_{max t 0}` on `ℝ`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.bmFiltrationReal). -/
noncomputable def bmFiltrationReal (W : ℝ≥0 → Ω → ℝ) (hW : ∀ t, Measurable (W t)) :
    Filtration ℝ mΩ where
  seq t := bmFiltration W hW t.toNNReal
  mono' _ _ h := (bmFiltration W hW).mono (Real.toNNReal_le_toNNReal h)
  le' t := (bmFiltration W hW).le t.toNNReal

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `bmReal W` is a martingale on the index `ℝ`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.martingale_bmReal). -/
theorem martingale_bmReal (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t)) :
    Martingale (bmReal W) (bmFiltrationReal W hW) P :=
  ⟨fun t => stronglyAdapted_bmFiltration hW t.toNNReal,
    fun _ _ hst => (martingale_bm hB hW).2 _ _ (Real.toNNReal_le_toNNReal hst)⟩

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `bmReal W t ² − max t 0` is a martingale on the
index `ℝ`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.martingale_bmReal_sq_sub). -/
theorem martingale_bmReal_sq_sub (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t)) :
    Martingale (fun t ω => bmReal W t ω ^ 2 - (t.toNNReal : ℝ)) (bmFiltrationReal W hW) P :=
  ⟨fun t => (martingale_bm_sq_sub hB hW).1 t.toNNReal,
    fun _ _ hst => (martingale_bm_sq_sub hB hW).2 _ _ (Real.toNNReal_le_toNNReal hst)⟩

/-! ## Non-vacuity: the constructed motion -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (non-vacuity): the constructed Brownian motion
`TidyR7BrownianExist.bmPath` is a martingale for its natural filtration.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.martingale_bmPath). -/
theorem martingale_bmPath : Martingale bmPath (bmFiltration bmPath measurable_bmPath) gaussSeq :=
  martingale_bm isPreBrownianReal_bmPath measurable_bmPath

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (non-vacuity): `bmPath t ² − t` is a martingale.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7BrownianTools.martingale_bmPath_sq_sub). -/
theorem martingale_bmPath_sq_sub :
    Martingale (fun t ω => bmPath t ω ^ 2 - (t : ℝ)) (bmFiltration bmPath measurable_bmPath)
      gaussSeq :=
  martingale_bm_sq_sub isPreBrownianReal_bmPath measurable_bmPath

end Cochrane.StickyPriceFiscal.TidyR7BrownianTools
