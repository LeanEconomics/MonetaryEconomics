/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.MaturityBuffer
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Continuous-time matching is necessary: uniqueness of the Laplace transform

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 8, §8.4, p. 250 (the
continuous-time present-value relation and "if the maturity structure matches the surpluses, real
rates cancel").

`MaturityBuffer.matching_cancels` and `MaturityBuffer.price_insulated` prove that matching is
sufficient in continuous time; `MaturityBuffer.matching_necessary` proves the converse only in
discrete time. Here the continuous-time converse is proved, for bounded continuous maturity
mismatches, even when insulation is only required along **constant** real-rate paths. The tool is
the uniqueness of the Laplace transform, which Mathlib lacks; it is proved here for bounded
continuous functions by the substitution `x = e^{−τ}`, which turns the transform at the points
`r̲ + 1 + n` into the moments of a continuous function on `[0, 1]`, and Weierstrass approximation.

## Main results

* `moment_eq`: `∫₀¹ xⁿ G(x) dx = ∫₀^∞ e^{−(r̲+1+n)τ} y(τ) dτ`, `G(x) = x^{r̲} y(−log x)`.
* `G_continuousOn`: `G` is continuous on `[0, 1]` (with `G(0) = 0`) for bounded continuous `y`.
* `moments_zero` (**moment uniqueness on `[0, 1]`**): a continuous function on `[0, 1]` all of
  whose moments vanish is zero on `(0, 1)`.
* `laplace_unique` (**uniqueness of the Laplace transform**): a bounded function continuous on
  `[0, ∞)` whose transform vanishes at `r̲ + 1 + n` for every `n ∈ ℕ` (`r̲ > 0`) is zero on
  `[0, ∞)`.
* `matching_necessary_cont`, `matching_necessary_const`: if a bounded continuous mismatch stream
  has zero present value along every real-rate path with rates at least `r̲ > 0` (or only along
  every constant path), it is zero: matching is necessary in continuous time.
* `price_insulated_only_if_matching_cont`: if the valuation gives the same price level `κ ≠ 0` along
  every such path, the debt maturing at each date matches the surplus, `x(τ) = κ s(τ)`.
-/

namespace Cochrane.AssetsRulesBalanceSheets.TidyR5Matching

open MeasureTheory Filter Topology Real

/-! ### The substitution `x = e^{−τ}` -/

/-- Cochrane (2023), §8.4, p. 250 (supporting the converse): the image of `(0, ∞)` under
`τ ↦ e^{−τ}` is `(0, 1)`. -/
theorem image_exp_neg : (fun τ : ℝ => exp (-τ)) '' Set.Ioi 0 = Set.Ioo 0 1 := by
  ext x
  simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Ioo]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨exp_pos _, Real.exp_lt_one_iff.2 (by linarith)⟩
  · rintro ⟨h0, h1⟩
    refine ⟨-log x, by linarith [log_neg h0 h1], ?_⟩
    rw [neg_neg, exp_log h0]

/-- Cochrane (2023), §8.4, p. 250 (supporting the converse): the transformed function
`G(x) = x^{r̲} y(−log x)` for `x > 0`, `G(x) = 0` for `x ≤ 0`. -/
noncomputable def G (rl : ℝ) (y : ℝ → ℝ) (x : ℝ) : ℝ := if 0 < x then x ^ rl * y (-log x) else 0

/-- Cochrane (2023), §8.4, p. 250: `G(e^{−τ}) = e^{−r̲τ} y(τ)`. -/
theorem G_exp (rl : ℝ) (y : ℝ → ℝ) (τ : ℝ) : G rl y (exp (-τ)) = exp (-(rl * τ)) * y τ := by
  simp only [G, exp_pos, ↓reduceIte, log_exp, neg_neg]
  rw [rpow_def_of_pos (exp_pos _), log_exp]
  ring_nf

/-- Cochrane (2023), §8.4, p. 250 (**the moments of `G` are values of the Laplace transform**):
`∫_{(0,1)} xⁿ G(x) dx = ∫_{(0,∞)} e^{−(r̲+1+n)τ} y(τ) dτ`. -/
theorem moment_eq (rl : ℝ) (y : ℝ → ℝ) (n : ℕ) :
    ∫ x in Set.Ioo 0 1, x ^ n * G rl y x =
      ∫ τ in Set.Ioi 0, exp (-((rl + 1 + n) * τ)) * y τ := by
  rw [← image_exp_neg]
  have hd : ∀ τ ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt (fun τ => exp (-τ)) (exp (-τ) * (-1))
      (Set.Ioi 0) τ := fun τ _ =>
    ((hasDerivAt_exp (-τ)).comp τ (hasDerivAt_neg τ)).hasDerivWithinAt
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd
    (fun a _ b _ h => by simpa using h)]
  refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
  simp only [smul_eq_mul]
  rw [G_exp, abs_mul, abs_of_pos (exp_pos _), abs_neg, abs_one, mul_one, ← exp_nat_mul]
  rw [show exp (-((rl + 1 + n) * τ)) = exp (-τ) * exp (n * -τ) * exp (-(rl * τ)) by
    rw [← exp_add, ← exp_add]; ring_nf]
  ring

/-- Cochrane (2023), §8.4, p. 250: for `r̲ > 0` and `y` bounded and continuous on `[0, ∞)`, `G` is
continuous on `[0, 1]`. -/
theorem G_continuousOn {rl M : ℝ} (hrl : 0 < rl) {y : ℝ → ℝ} (hy : ContinuousOn y (Set.Ici 0))
    (hyM : ∀ τ, 0 ≤ τ → |y τ| ≤ M) : ContinuousOn (G rl y) (Set.Icc 0 1) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with h0 | hpos
  · -- at `0`: `|G| ≤ M x^{r̲} → 0`
    subst h0
    have hG0 : G rl y 0 = 0 := by simp [G]
    rw [ContinuousWithinAt, hG0]
    have hlim : Tendsto (fun x : ℝ => M * x ^ rl) (𝓝[Set.Icc 0 1] 0) (𝓝 0) := by
      have := ((continuousAt_rpow_const 0 rl (Or.inr hrl.le)).tendsto.const_mul M)
      rw [zero_rpow hrl.ne', mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with x' hx'
    simp only [G, Real.norm_eq_abs]
    split_ifs with h
    · rw [abs_mul, abs_of_pos (rpow_pos_of_pos h rl), mul_comm]
      exact mul_le_mul_of_nonneg_right (hyM _ (by
        have := log_nonpos hx'.1 hx'.2; linarith)) (rpow_pos_of_pos h rl).le
    · simp only [abs_zero]
      have := hx'.1
      have : x' = 0 := by linarith
      subst this
      rw [zero_rpow hrl.ne', mul_zero]
  · -- at `x > 0`
    have hmaps : Set.MapsTo (fun x => -log x) (Set.Icc 0 1) (Set.Ici 0) := fun x' hx' => by
      have := log_nonpos hx'.1 hx'.2
      simp only [Set.mem_Ici]
      linarith
    have hlog : ContinuousWithinAt (fun x => -log x) (Set.Icc 0 1) x :=
      (continuousAt_log hpos.ne').neg.continuousWithinAt
    have hyc : ContinuousWithinAt (fun x => y (-log x)) (Set.Icc 0 1) x :=
      ContinuousWithinAt.comp (f := fun x => -log x) (hy _ (hmaps hx)) hlog hmaps
    have hpow : ContinuousWithinAt (fun x : ℝ => x ^ rl) (Set.Icc 0 1) x :=
      (continuousAt_rpow_const x rl (Or.inl hpos.ne')).continuousWithinAt
    refine (hpow.mul hyc).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hpos)] with x' hx'
      simp [G, Set.mem_Ioi.1 hx']
    · simp [G, hpos]

/-! ### Moment uniqueness on `[0, 1]` -/

/-- Cochrane (2023), §8.4, p. 250 (**moment uniqueness**, via Weierstrass approximation): if `g` is
continuous on `[0, 1]` and `∫_{(0,1)} xⁿ g(x) dx = 0` for every `n ∈ ℕ`, then `g = 0` on
`(0, 1)`. -/
theorem moments_zero {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc 0 1))
    (hmom : ∀ n : ℕ, ∫ x in Set.Ioo 0 1, x ^ n * g x = 0) : ∀ x ∈ Set.Ioo (0 : ℝ) 1, g x = 0 := by
  have hcpt : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  obtain ⟨B, hB⟩ := hcpt.exists_bound_of_continuousOn hg
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ Set.Icc 0 1 := Set.Ioo_subset_Icc_self
  have hint : ∀ f : ℝ → ℝ, ContinuousOn f (Set.Icc 0 1) → IntegrableOn f (Set.Ioo 0 1) :=
    fun f hf => (hf.integrableOn_Icc).mono_set hsub
  -- polynomial moments vanish
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
      exact (hint _ ((continuousOn_pow i).mul hg)).const_mul _
  -- `∫ g² = 0`
  have hsq : ∫ x in Set.Ioo 0 1, g x * g x = 0 := by
    have hnn : 0 ≤ ∫ x in Set.Ioo 0 1, g x * g x :=
      setIntegral_nonneg measurableSet_Ioo fun x _ => mul_self_nonneg _
    have hle : ∀ ε, 0 < ε → ∫ x in Set.Ioo 0 1, g x * g x ≤ B * ε := by
      intro ε hε
      obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn 0 1 g hg ε hε
      have h1 : ∫ x in Set.Ioo 0 1, g x * g x =
          ∫ x in Set.Ioo 0 1, g x * (g x - q.eval x) := by
        have hgq := hpoly q
        have hi1 : IntegrableOn (fun x => g x * g x) (Set.Ioo 0 1) := hint _ (hg.mul hg)
        have hi2 : IntegrableOn (fun x => q.eval x * g x) (Set.Ioo 0 1) :=
          hint _ (q.continuous.continuousOn.mul hg)
        have : (fun x => g x * (g x - q.eval x)) = fun x => g x * g x - q.eval x * g x := by
          funext x; ring
        rw [this, integral_sub hi1 hi2, hgq, sub_zero]
      rw [h1]
      have hb := norm_setIntegral_le_of_norm_le_const (μ := volume)
        (s := Set.Ioo (0 : ℝ) 1) (f := fun x => g x * (g x - q.eval x)) (C := B * ε)
        (by simp) (fun x hx => by
          rw [Real.norm_eq_abs, abs_mul]
          have h2 := hq x (hsub hx)
          rw [abs_sub_comm] at h2
          exact mul_le_mul (hB x (hsub hx)) h2.le (abs_nonneg _)
            ((abs_nonneg _).trans (hB x (hsub hx))))
      rw [Real.volume_real_Ioo_of_le zero_le_one, sub_zero, mul_one] at hb
      exact (le_abs_self _).trans hb
    have hB0 : 0 ≤ B := by
      have := hB 0 ⟨le_rfl, zero_le_one⟩
      exact (norm_nonneg _).trans this
    have hle0 : ∫ x in Set.Ioo 0 1, g x * g x ≤ 0 := by
      by_contra hc
      push Not at hc
      rcases eq_or_lt_of_le hB0 with hB0' | hBpos
      · have := hle 1 one_pos
        rw [← hB0', zero_mul] at this
        linarith
      · have := hle ((∫ x in Set.Ioo 0 1, g x * g x) / (2 * B)) (by positivity)
        have e : B * ((∫ x in Set.Ioo 0 1, g x * g x) / (2 * B)) =
            (∫ x in Set.Ioo 0 1, g x * g x) / 2 := by
          field_simp
        rw [e] at this
        linarith
    linarith
  -- hence `g² = 0` a.e. on `(0, 1)`, and everywhere by continuity
  have hae : (fun x => g x * g x) =ᵐ[volume.restrict (Set.Ioo 0 1)] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun x => mul_self_nonneg _)
      (hint _ (hg.mul hg))).1 hsq
  have heq := Measure.eqOn_of_ae_eq hae ((hg.mul hg).mono hsub) continuousOn_const
    (by rw [isOpen_Ioo.interior_eq]; exact subset_closure)
  intro x hx
  have := heq hx
  simp only [Pi.zero_apply] at this
  exact mul_self_eq_zero.1 this

/-! ### Uniqueness of the Laplace transform -/

/-- Cochrane (2023), §8.4, p. 250 (**uniqueness of the Laplace transform**, the tool for the
continuous-time converse): let `r̲ > 0` and `y` bounded and continuous on `[0, ∞)`. If
`∫₀^∞ e^{−(r̲+1+n)τ} y(τ) dτ = 0` for every `n ∈ ℕ`, then `y(τ) = 0` for every `τ ≥ 0`. -/
theorem laplace_unique {rl M : ℝ} (hrl : 0 < rl) {y : ℝ → ℝ} (hy : ContinuousOn y (Set.Ici 0))
    (hyM : ∀ τ, 0 ≤ τ → |y τ| ≤ M)
    (h : ∀ n : ℕ, ∫ τ in Set.Ioi 0, exp (-((rl + 1 + n) * τ)) * y τ = 0) :
    ∀ τ, 0 ≤ τ → y τ = 0 := by
  have hG := moments_zero (G_continuousOn hrl hy hyM) fun n => by rw [moment_eq, h n]
  have hpos : ∀ τ, 0 < τ → y τ = 0 := fun τ hτ => by
    have hx : exp (-τ) ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨exp_pos _, Real.exp_lt_one_iff.2 (by linarith)⟩
    have := hG _ hx
    rw [G_exp] at this
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 (exp_pos _).ne'
    · exact h1
  intro τ hτ
  rcases eq_or_lt_of_le hτ with h0 | h0
  · subst h0
    have hc : Tendsto y (𝓝[>] 0) (𝓝 (y 0)) :=
      ((hy 0 (Set.mem_Ici.2 le_rfl)).mono Set.Ioi_subset_Ici_self).tendsto
    have hz : Tendsto y (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [self_mem_nhdsWithin] with τ' hτ'
        exact (hpos τ' hτ').symm)
    exact tendsto_nhds_unique hc hz
  · exact hpos τ h0

/-! ### Matching is necessary in continuous time -/

/-- Cochrane (2023), §8.4, p. 250: along the constant real-rate path `r ≡ λ` the continuous-time
discount factor is `e^{−λτ}`. -/
theorem cdisc_const (l τ : ℝ) : MaturityBuffer.cdisc (fun _ => l) τ = exp (-(l * τ)) := by
  simp only [MaturityBuffer.cdisc, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring_nf

/-- Cochrane (2023), §8.4, pp. 250–251 (**the continuous-time converse, constant paths
suffice**): if a mismatch stream `y`, bounded and continuous on `[0, ∞)`, has zero present value
`∫₀^∞ e^{−λτ} y(τ) dτ = 0` along every constant real-rate path `λ ≥ r̲ > 0`, then `y = 0` on
`[0, ∞)`. -/
theorem matching_necessary_const {rl M : ℝ} (hrl : 0 < rl) {y : ℝ → ℝ}
    (hy : ContinuousOn y (Set.Ici 0)) (hyM : ∀ τ, 0 ≤ τ → |y τ| ≤ M)
    (h : ∀ l, rl ≤ l → ∫ τ in Set.Ioi 0, MaturityBuffer.cdisc (fun _ => l) τ * y τ = 0) :
    ∀ τ, 0 ≤ τ → y τ = 0 :=
  laplace_unique hrl hy hyM fun n => by
    have := h (rl + 1 + n) (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith)
    simpa [cdisc_const] using this

/-- Cochrane (2023), §8.4, pp. 250–251 (**the continuous-time converse of
`MaturityBuffer.matching_cancels`**):
if a bounded continuous mismatch stream has zero present value along every real-rate path with
rates at least `r̲ > 0`, it is zero on `[0, ∞)`. -/
theorem matching_necessary_cont {rl M : ℝ} (hrl : 0 < rl) {y : ℝ → ℝ}
    (hy : ContinuousOn y (Set.Ici 0)) (hyM : ∀ τ, 0 ≤ τ → |y τ| ≤ M)
    (h : ∀ r : ℝ → ℝ, (∀ u, rl ≤ r u) →
      ∫ τ in Set.Ioi 0, MaturityBuffer.cdisc r τ * y τ = 0) :
    ∀ τ, 0 ≤ τ → y τ = 0 :=
  matching_necessary_const hrl hy hyM fun _ hl => h _ fun _ => hl

/-- Cochrane (2023), §8.4, p. 250 (supporting the price-level form): a function bounded and
continuous on `[0, ∞)`, discounted at a constant rate `λ > 0`, is integrable on `(0, ∞)`. -/
theorem integrableOn_disc {l M : ℝ} (hl : 0 < l) {x : ℝ → ℝ} (hx : ContinuousOn x (Set.Ici 0))
    (hxM : ∀ τ, 0 ≤ τ → |x τ| ≤ M) :
    IntegrableOn (fun τ => exp (-(l * τ)) * x τ) (Set.Ioi 0) := by
  have hexp : IntegrableOn (fun τ => exp (-l * τ)) (Set.Ioi 0) := exp_neg_integrableOn_Ioi 0 hl
  refine (hexp.mul_const M).mono' ?_ ?_
  · exact ((continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn.mul
      (hx.mono Set.Ioi_subset_Ici_self)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with τ hτ
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _), neg_mul]
    exact mul_le_mul_of_nonneg_left (hxM τ (le_of_lt hτ)) (exp_pos _).le

/-- Cochrane (2023), §8.4, pp. 250–251 (**price-level form of the continuous-time converse**):
let the real value of debt maturing at `τ` (per unit of the current price level), `x`, and the
surplus `s` be bounded and continuous on `[0, ∞)`. If the valuation
`(1/κ) ∫₀^∞ e^{−∫r} x = ∫₀^∞ e^{−∫r} s` gives the same price level `κ ≠ 0` along every real-rate
path with rates at least `r̲ > 0` (constant paths suffice), then the maturity structure matches the
surpluses exactly: `x(τ) = κ s(τ)` for every `τ ≥ 0`. -/
theorem price_insulated_only_if_matching_cont {rl Mx Ms κ : ℝ} (hrl : 0 < rl) (hκ : κ ≠ 0)
    {x s : ℝ → ℝ} (hx : ContinuousOn x (Set.Ici 0)) (hs : ContinuousOn s (Set.Ici 0))
    (hxM : ∀ τ, 0 ≤ τ → |x τ| ≤ Mx) (hsM : ∀ τ, 0 ≤ τ → |s τ| ≤ Ms)
    (h : ∀ r : ℝ → ℝ, (∀ u, rl ≤ r u) →
      (∫ τ in Set.Ioi 0, MaturityBuffer.cdisc r τ * x τ) / κ =
        ∫ τ in Set.Ioi 0, MaturityBuffer.cdisc r τ * s τ) :
    ∀ τ, 0 ≤ τ → x τ = κ * s τ := by
  have hzero := matching_necessary_const hrl (y := fun τ => x τ - κ * s τ) (M := Mx + |κ| * Ms)
    (hx.sub (hs.const_smul κ)) (fun τ hτ => by
      calc |x τ - κ * s τ| ≤ |x τ| + |κ * s τ| := abs_sub _ _
        _ ≤ Mx + |κ| * Ms := by
          rw [abs_mul]
          exact add_le_add (hxM τ hτ) (mul_le_mul_of_nonneg_left (hsM τ hτ) (abs_nonneg κ)))
    (fun l hl => by
      have hl0 : 0 < l := hrl.trans_le hl
      have hval := h (fun _ => l) fun _ => hl
      simp only [cdisc_const] at hval ⊢
      rw [div_eq_iff hκ] at hval
      have e : (fun τ => exp (-(l * τ)) * (x τ - κ * s τ)) =
          fun τ => exp (-(l * τ)) * x τ - κ * (exp (-(l * τ)) * s τ) := by
        funext τ
        ring
      rw [e, integral_sub (integrableOn_disc hl0 hx hxM)
        ((integrableOn_disc hl0 hs hsM).const_mul κ), integral_const_mul, hval]
      ring)
  intro τ hτ
  have := hzero τ hτ
  linarith

end Cochrane.AssetsRulesBalanceSheets.TidyR5Matching
