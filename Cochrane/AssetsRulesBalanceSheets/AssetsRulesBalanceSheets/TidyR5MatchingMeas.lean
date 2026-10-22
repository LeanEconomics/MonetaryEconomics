/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.TidyR5Matching
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Continuous-time matching is necessary for measurable mismatch streams

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 8, §8.4, p. 250 (the
continuous-time present-value relation; matching makes real rates cancel).

The module TidyR5Matching (`TidyR5Matching.matching_necessary_cont`) proves the
continuous-time converse of `MaturityBuffer.matching_cancels` for
bounded continuous mismatch streams. Here it is extended to every **measurable** stream `y` whose
Laplace transform converges absolutely at the lowest admissible rate `r̲`
(`∫₀^∞ e^{−r̲τ} |y(τ)| dτ < ∞`; this covers essentially bounded streams for `r̲ > 0` and streams
growing more slowly than `e^{r̲τ}`), with the conclusion `y = 0` almost everywhere.

## Main results

* `G_integrableOn`: after `x = e^{−τ}`, `G(x) = x^{r̲} y(−log x)` is integrable on `(0, 1)`.
* `moments_zero_ae` (**moment uniqueness for integrable functions on `(0, 1)`**): an integrable `g`
  on `(0, 1)` with `∫ xⁿ g = 0` for all `n` vanishes a.e. Proof: Weierstrass approximation gives
  `∫ φ g = 0` for every continuous `φ`, and Mathlib's
  `ae_eq_zero_of_integral_contDiff_smul_eq_zero` (test functions) concludes.
* `laplace_unique_ae`: `∫₀^∞ e^{−(r̲+1+n)τ} y(τ) dτ = 0` for all `n` implies `y = 0` a.e. on
  `(0, ∞)`.
* `matching_necessary_meas`, `matching_necessary_bdd`, `price_insulated_only_if_matching_meas`:
  the matching-necessity theorems for this class (constant real-rate paths `λ ≥ r̲` suffice).
-/

namespace Cochrane.AssetsRulesBalanceSheets.TidyR5MatchingMeas

open MeasureTheory Filter Topology Real TidyR5Matching

/-- Cochrane (2023), §8.4, p. 250 (supporting the converse): if `e^{−r̲τ} y(τ)` is integrable on
`(0, ∞)`, then `G(x) = x^{r̲} y(−log x)` is integrable on `(0, 1)`. -/
theorem G_integrableOn {rl : ℝ} {y : ℝ → ℝ}
    (hint : IntegrableOn (fun τ => exp (-(rl * τ)) * y τ) (Set.Ioi 0)) :
    IntegrableOn (G rl y) (Set.Ioo 0 1) := by
  rw [← image_exp_neg]
  have hd : ∀ τ ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt (fun τ => exp (-τ)) (exp (-τ) * (-1))
      (Set.Ioi 0) τ := fun τ _ =>
    ((hasDerivAt_exp (-τ)).comp τ (hasDerivAt_neg τ)).hasDerivWithinAt
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd
    (fun a _ b _ h => by simpa using h)]
  have hm : AEStronglyMeasurable (fun τ => exp (-τ)) (volume.restrict (Set.Ioi 0)) :=
    (continuous_exp.comp continuous_neg).aestronglyMeasurable
  refine (hint.bdd_mul hm (c := 1) ?_).congr ?_
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with τ hτ
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_one_iff.2 (by linarith [Set.mem_Ioi.1 hτ])
  · filter_upwards with τ
    simp only [smul_eq_mul, G_exp, abs_mul, abs_of_pos (exp_pos _), abs_neg,
      abs_one, mul_one]

/-- Cochrane (2023), §8.4, p. 250 (**moment uniqueness for integrable functions**): if `g` is
integrable on `(0, 1)` and `∫_{(0,1)} xⁿ g(x) dx = 0` for every `n ∈ ℕ`, then `g = 0` a.e. on
`(0, 1)`. -/
theorem moments_zero_ae {g : ℝ → ℝ} (hg : IntegrableOn g (Set.Ioo 0 1))
    (hmom : ∀ n : ℕ, ∫ x in Set.Ioo 0 1, x ^ n * g x = 0) :
    ∀ᵐ x ∂volume, x ∈ Set.Ioo (0 : ℝ) 1 → g x = 0 := by
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ Set.Icc 0 1 := Set.Ioo_subset_Icc_self
  -- a function continuous on `[0, 1]` times `g` is integrable on `(0, 1)`
  have hmul : ∀ φ : ℝ → ℝ, ContinuousOn φ (Set.Icc 0 1) →
      IntegrableOn (fun x => φ x * g x) (Set.Ioo 0 1) := by
    intro φ hφ
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
    refine hg.bdd_mul ((hφ.mono hsub).aestronglyMeasurable measurableSet_Ioo) (c := C) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    exact hC x (hsub hx)
  have hpoly : ∀ q : Polynomial ℝ, ∫ x in Set.Ioo 0 1, q.eval x * g x = 0 := by
    intro q
    have e : (fun x => q.eval x * g x) = fun x => ∑ i ∈ Finset.range (q.natDegree + 1),
        q.coeff i * (x ^ i * g x) := by
      funext x
      rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, integral_finsetSum]
    · refine Finset.sum_eq_zero fun i _ => ?_
      rw [integral_const_mul, hmom i, mul_zero]
    · intro i _
      exact (hmul _ (continuousOn_pow i)).const_mul _
  -- every continuous test function annihilates `g`
  have hcont : ∀ φ : ℝ → ℝ, ContinuousOn φ (Set.Icc 0 1) →
      ∫ x in Set.Ioo 0 1, φ x * g x = 0 := by
    intro φ hφ
    set K := ∫ x in Set.Ioo 0 1, |g x| with hK
    have hK0 : 0 ≤ K := setIntegral_nonneg measurableSet_Ioo fun x _ => abs_nonneg _
    have hle : ∀ ε, 0 < ε → |∫ x in Set.Ioo 0 1, φ x * g x| ≤ ε * K := by
      intro ε hε
      obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn 0 1 φ hφ ε hε
      have e : ∫ x in Set.Ioo 0 1, φ x * g x = ∫ x in Set.Ioo 0 1, (φ x - q.eval x) * g x := by
        have : (fun x => (φ x - q.eval x) * g x) = fun x => φ x * g x - q.eval x * g x := by
          funext x; ring
        rw [this, integral_sub (hmul φ hφ) (hmul _ q.continuous.continuousOn), hpoly q,
          sub_zero]
      rw [e, ← Real.norm_eq_abs, hK, ← integral_const_mul]
      refine norm_integral_le_of_norm_le (hg.norm.const_mul ε) ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := hq x (hsub hx)
      rw [abs_sub_comm] at h1
      exact mul_le_mul_of_nonneg_right h1.le (abs_nonneg _)
    have h0 : |∫ x in Set.Ioo 0 1, φ x * g x| ≤ 0 := by
      by_contra hc
      push Not at hc
      have := hle (|∫ x in Set.Ioo 0 1, φ x * g x| / (2 * (K + 1))) (by positivity)
      have e2 : |∫ x in Set.Ioo 0 1, φ x * g x| / (2 * (K + 1)) * K ≤
          |∫ x in Set.Ioo 0 1, φ x * g x| / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    exact abs_nonpos_iff.1 h0
  -- test functions
  have hF : Integrable ((Set.Ioo (0 : ℝ) 1).indicator g) volume :=
    hg.integrable_indicator measurableSet_Ioo
  have hz := ae_eq_zero_of_integral_contDiff_smul_eq_zero hF.locallyIntegrable
    (μ := volume) fun φ hφ _ => by
      have e : (fun x => φ x • (Set.Ioo (0 : ℝ) 1).indicator g x) =
          (Set.Ioo (0 : ℝ) 1).indicator (fun x => φ x * g x) := by
        funext x
        by_cases hx : x ∈ Set.Ioo (0 : ℝ) 1 <;> simp [hx]
      rw [e, integral_indicator measurableSet_Ioo]
      exact hcont φ hφ.continuous.continuousOn
  filter_upwards [hz] with x hx hxs
  simpa [hxs] using hx

/-- Cochrane (2023), §8.4, p. 250 (**uniqueness of the Laplace transform for measurable
functions**): if `e^{−r̲τ} y(τ)` is integrable on `(0, ∞)` and
`∫₀^∞ e^{−(r̲+1+n)τ} y(τ) dτ = 0` for every `n ∈ ℕ`, then `y = 0` a.e. on `(0, ∞)`. -/
theorem laplace_unique_ae {rl : ℝ} {y : ℝ → ℝ}
    (hint : IntegrableOn (fun τ => exp (-(rl * τ)) * y τ) (Set.Ioi 0))
    (h : ∀ n : ℕ, ∫ τ in Set.Ioi 0, exp (-((rl + 1 + n) * τ)) * y τ = 0) :
    ∀ᵐ τ ∂(volume.restrict (Set.Ioi 0)), y τ = 0 := by
  have hGi := G_integrableOn hint
  have hG := moments_zero_ae hGi fun n => by rw [moment_eq, h n]
  -- `∫_{(0,1)} |G| = 0`
  have h0 : ∫ x in Set.Ioo 0 1, |G rl y x| = 0 :=
    setIntegral_eq_zero_of_ae_eq_zero (hG.mono fun x hx hxs => by rw [hx hxs, abs_zero])
  rw [← image_exp_neg] at h0
  have hd : ∀ τ ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt (fun τ => exp (-τ)) (exp (-τ) * (-1))
      (Set.Ioi 0) τ := fun τ _ =>
    ((hasDerivAt_exp (-τ)).comp τ (hasDerivAt_neg τ)).hasDerivWithinAt
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd
    (fun a _ b _ h => by simpa using h)] at h0
  have hfun : (fun τ => |exp (-τ) * (-1)| • |G rl y (exp (-τ))|) =
      fun τ => exp (-τ) * |exp (-(rl * τ)) * y τ| := by
    funext τ
    simp only [smul_eq_mul, G_exp, abs_mul, abs_of_pos (exp_pos _), abs_neg, abs_one, mul_one]
  rw [hfun] at h0
  have hm : AEStronglyMeasurable (fun τ => exp (-τ)) (volume.restrict (Set.Ioi 0)) :=
    (continuous_exp.comp continuous_neg).aestronglyMeasurable
  have hi : IntegrableOn (fun τ => exp (-τ) * |exp (-(rl * τ)) * y τ|) (Set.Ioi 0) := by
    refine hint.abs.bdd_mul hm (c := 1) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with τ hτ
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_one_iff.2 (by linarith [Set.mem_Ioi.1 hτ])
  have hz := (setIntegral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun τ => mul_nonneg (exp_pos _).le (abs_nonneg _)) hi).1 h0
  filter_upwards [hz] with τ hτ
  simp only [Pi.zero_apply] at hτ
  rcases mul_eq_zero.1 hτ with h1 | h1
  · exact absurd h1 (exp_pos _).ne'
  · rcases mul_eq_zero.1 (abs_eq_zero.1 h1) with h2 | h2
    · exact absurd h2 (exp_pos _).ne'
    · exact h2

/-- Cochrane (2023), §8.4, p. 250 (supporting lemma): if `e^{−r̲τ} y(τ)` is integrable on
`(0, ∞)`, so is `e^{−λτ} y(τ)` for every `λ ≥ r̲`. -/
theorem integrableOn_shift {rl l : ℝ} (hl : rl ≤ l) {y : ℝ → ℝ}
    (hint : IntegrableOn (fun τ => exp (-(rl * τ)) * y τ) (Set.Ioi 0)) :
    IntegrableOn (fun τ => exp (-(l * τ)) * y τ) (Set.Ioi 0) := by
  have hm : AEStronglyMeasurable (fun τ => exp (-((l - rl) * τ))) (volume.restrict (Set.Ioi 0)) :=
    (continuous_exp.comp ((continuous_const.mul continuous_id).neg)).aestronglyMeasurable
  refine (hint.bdd_mul hm (c := 1) ?_).congr ?_
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with τ hτ
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_one_iff.2 (by nlinarith [Set.mem_Ioi.1 hτ])
  · filter_upwards with τ
    rw [← mul_assoc, ← exp_add]
    ring_nf

/-- Cochrane (2023), §8.4, pp. 250–251 (**the continuous-time converse for measurable mismatch
streams**): let `y` be measurable with `e^{−r̲τ} y(τ)` integrable on `(0, ∞)`. If `y` has zero
present value `∫₀^∞ e^{−λτ} y(τ) dτ` along every constant real-rate path `λ ≥ r̲` (in particular,
if along every rate path `r ≥ r̲`), then `y = 0` a.e. on `(0, ∞)`. -/
theorem matching_necessary_meas {rl : ℝ} {y : ℝ → ℝ}
    (hint : IntegrableOn (fun τ => exp (-(rl * τ)) * y τ) (Set.Ioi 0))
    (h : ∀ l, rl ≤ l → ∫ τ in Set.Ioi 0, MaturityBuffer.cdisc (fun _ => l) τ * y τ = 0) :
    ∀ᵐ τ ∂(volume.restrict (Set.Ioi 0)), y τ = 0 :=
  laplace_unique_ae hint fun n => by
    have := h (rl + 1 + n) (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith)
    simpa [cdisc_const] using this

/-- Cochrane (2023), §8.4, pp. 250–251 (**essentially bounded mismatch streams**): if `y` is
measurable on `(0, ∞)`, `|y| ≤ M` a.e. there, and `y` has zero present value along every real-rate
path with rates at least `r̲ > 0`, then `y = 0` a.e. on `(0, ∞)`. -/
theorem matching_necessary_bdd {rl M : ℝ} (hrl : 0 < rl) {y : ℝ → ℝ}
    (hym : AEStronglyMeasurable y (volume.restrict (Set.Ioi 0)))
    (hyM : ∀ᵐ τ ∂(volume.restrict (Set.Ioi 0)), |y τ| ≤ M)
    (h : ∀ r : ℝ → ℝ, (∀ u, rl ≤ r u) →
      ∫ τ in Set.Ioi 0, MaturityBuffer.cdisc r τ * y τ = 0) :
    ∀ᵐ τ ∂(volume.restrict (Set.Ioi 0)), y τ = 0 := by
  have hexp : IntegrableOn (fun τ => exp (-rl * τ)) (Set.Ioi 0) := exp_neg_integrableOn_Ioi 0 hrl
  have hint : IntegrableOn (fun τ => exp (-(rl * τ)) * y τ) (Set.Ioi 0) := by
    refine (hexp.mul_const M).mono' (((continuous_exp.comp
      ((continuous_const.mul continuous_id).neg)).aestronglyMeasurable).mul hym) ?_
    filter_upwards [hyM] with τ hτ
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _), neg_mul]
    exact mul_le_mul_of_nonneg_left hτ (exp_pos _).le
  exact matching_necessary_meas hint fun l hl => h _ fun _ => hl

/-- Cochrane (2023), §8.4, pp. 250–251 (**price-level form, measurable streams**): if the real
value of debt maturing at `τ`, `x`, and the surplus `s` are measurable with `e^{−r̲τ} x(τ)` and
`e^{−r̲τ} s(τ)` integrable on `(0, ∞)`, and the valuation `(1/κ) ∫ e^{−∫r} x = ∫ e^{−∫r} s` gives
the same price level `κ ≠ 0` along every constant real-rate path `λ ≥ r̲`, then `x = κ s` a.e. on
`(0, ∞)`. -/
theorem price_insulated_only_if_matching_meas {rl κ : ℝ} (hκ : κ ≠ 0) {x s : ℝ → ℝ}
    (hx : IntegrableOn (fun τ => exp (-(rl * τ)) * x τ) (Set.Ioi 0))
    (hs : IntegrableOn (fun τ => exp (-(rl * τ)) * s τ) (Set.Ioi 0))
    (h : ∀ l, rl ≤ l →
      (∫ τ in Set.Ioi 0, MaturityBuffer.cdisc (fun _ => l) τ * x τ) / κ =
        ∫ τ in Set.Ioi 0, MaturityBuffer.cdisc (fun _ => l) τ * s τ) :
    ∀ᵐ τ ∂(volume.restrict (Set.Ioi 0)), x τ = κ * s τ := by
  have hint : IntegrableOn (fun τ => exp (-(rl * τ)) * (x τ - κ * s τ)) (Set.Ioi 0) := by
    have := hx.sub (hs.const_mul κ)
    refine this.congr (Eventually.of_forall fun τ => ?_)
    simp only [Pi.sub_apply]
    ring
  have hz := matching_necessary_meas (y := fun τ => x τ - κ * s τ) hint fun l hl => by
    have hval := h l hl
    simp only [cdisc_const] at hval ⊢
    rw [div_eq_iff hκ] at hval
    have e : (fun τ => exp (-(l * τ)) * (x τ - κ * s τ)) =
        fun τ => exp (-(l * τ)) * x τ - κ * (exp (-(l * τ)) * s τ) := by
      funext τ
      ring
    rw [e, integral_sub (integrableOn_shift hl hx) ((integrableOn_shift hl hs).const_mul κ),
      integral_const_mul, hval]
    ring
  filter_upwards [hz] with τ hτ
  linarith

end Cochrane.AssetsRulesBalanceSheets.TidyR5MatchingMeas
