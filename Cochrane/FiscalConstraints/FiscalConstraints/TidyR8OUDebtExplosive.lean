/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.TidyR7OrnsteinUhlenbeck
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# With `r > g` the a.s. unboundedness of (6.5) debt fails

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.1, p. 197 ("So at some
point the future debt-to-GDP ratio following (6.5) will eventually exceed any bound"), with the
debt equation (6.4)–(6.5), p. 196, `ḃ = ab − s`, `a = r − g`.

The book makes the claim for permanent `r < g` (`a < 0`), where it is proved almost surely in
TidyR8OUDebtUnbounded. The claim does not extend to `r > g`: there debt is
`b_t = e^{at}(b_0 − ∫_0^t e^{−au}s_u du)` and the discounted surplus integral converges, so a
large enough mean surplus keeps debt bounded with positive probability.

## Main results (`a = r − g > 0`, `η > 0`, any `σ`, `b_0`; surplus started at its mean `s_0 = s̄`)

* `measurable_ouNoise_uncurry`: the OU noise is jointly measurable in `(ω, t)`;
* `integral_ouNoise_sq_le`: `E[(OU noise at t)²] ≤ 1/(2η)`;
* `lintegral_ouNoiseTail_le`: the random variable
  `R = ∫_0^∞ e^{−au}|σ·noise_u|du` (`ouNoiseTail`) has `E R ≤ V/a`, `V = (1 + σ²/(2η))/2`
  (Tonelli);
* `abs_integral_le_ouNoiseTail`: on `{R < ∞}`, `|∫_0^t e^{−au}σ·noise_u du| ≤ R` for all `t ≥ 0`;
* **`ouDebtProc_bounded_half`**: if `b_0 + (1 + σ²/(2η))/a ≤ s̄/a`, then with probability at
  least `1/2` debt stays at or below `s̄/a` at every date (Markov's inequality);
* **`ouDebtProc_not_ae_unbounded`**: hence for every `a > 0` there are surplus parameters for
  which "debt a.s. eventually exceeds any bound" is false;
* non-vacuity on bmPath with `r − g = +1%`, `η = σ = 1`, `b_0 = 0`, `s̄ = 3/2`:
  `bmPath_ouDebt_bounded_half`.
-/

namespace Cochrane.FiscalConstraints.TidyR8OUDebtExplosive

open Real MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.FiscalConstraints.TidyR7OUPath Cochrane.FiscalConstraints.TidyR7WienerGaussian
open Cochrane.FiscalConstraints.TidyR7OrnsteinUhlenbeck
open Cochrane.FiscalConstraints.TidyR7BrownianTools
open Cochrane.FiscalConstraints.LinearODE
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

/-! ### Joint measurability -/

/-- Cochrane (2023), p. 197 (tool): with measurable values and continuous paths, the driving
process is jointly measurable in `(ω, t)`.
From Mathlib `measurable_uncurry_of_continuous_of_measurable`. -/
theorem measurable_bmReal_uncurry (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) :
    Measurable fun p : Ω × ℝ => bmReal W p.2 p.1 :=
  (measurable_uncurry_of_continuous_of_measurable (u := fun (t : ℝ) (ω : Ω) => bmReal W t ω)
    (fun ω => continuous_bmReal (hcont ω)) (fun t => hW t.toNNReal)).comp measurable_swap

/-- Cochrane (2023), p. 197: the primitive `∫_0^t e^{ηu}W_u du` is measurable in `ω`. -/
theorem measurable_ouPrim (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω)
    (η t : ℝ) : Measurable fun ω => ouPrim η (fun u => bmReal W u ω) t := by
  have hj : StronglyMeasurable fun p : Ω × ℝ => exp (η * p.2) * bmReal W p.2 p.1 :=
    ((by fun_prop : Measurable fun p : Ω × ℝ => exp (η * p.2)).mul
      (measurable_bmReal_uncurry hW hcont)).stronglyMeasurable
  have h1 := hj.integral_prod_right' (ν := volume.restrict (Set.Ioc 0 t))
  have h2 := hj.integral_prod_right' (ν := volume.restrict (Set.Ioc t 0))
  exact h1.measurable.sub h2.measurable

/-- Cochrane (2023), p. 197: the OU noise at a date is measurable in `ω`.
Strengthens the measurability behind `TidyR7OrnsteinUhlenbeck.aemeasurable_ouProc`. -/
theorem measurable_ouNoise (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω)
    (η t : ℝ) : Measurable fun ω => ouNoise η (fun u => bmReal W u ω) t :=
  (hW t.toNNReal).sub (((measurable_ouPrim hW hcont η t).const_mul (exp (-η * t))).const_mul η)

/-- Cochrane (2023), p. 197: the OU noise is jointly measurable in `(ω, t)`. -/
theorem measurable_ouNoise_uncurry (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (η : ℝ) :
    Measurable fun p : Ω × ℝ => ouNoise η (fun u => bmReal W u p.1) p.2 :=
  (measurable_uncurry_of_continuous_of_measurable
    (u := fun (t : ℝ) (ω : Ω) => ouNoise η (fun u => bmReal W u ω) t)
    (fun ω => continuous_ouNoise η (continuous_bmReal (hcont ω)))
    (fun t => measurable_ouNoise hW hcont η t)).comp measurable_swap

/-! ### Moments of the noise -/

/-- Cochrane (2023), p. 197: the OU noise is square integrable at every date `t > 0`.
`TidyR7WienerGaussian.memLp_wienerBP` applied to the noise. -/
theorem memLp_ouNoise (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) (η : ℝ) {t : ℝ}
    (ht : 0 < t) : MemLp (fun ω => ouNoise η (fun u => bmReal W u ω) t) 2 P := by
  have h := (memLp_wienerBP (P := P) hB hW hcont (hasDerivAt_expMul η)
    (by fun_prop : Continuous fun u => exp (η * u) * η) le_rfl ht).const_mul (exp (-η * t))
  refine h.congr_norm (measurable_ouNoise hW hcont η t).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  rw [ouNoise_eq_wienerBP hW0 η ω t]

/-- **Cochrane (2023), p. 197: the second moment of the OU noise is at most `1/(2η)`.**
From `TidyR7WienerGaussian.integral_wienerBP_sq` and `TidyR7OrnsteinUhlenbeck.ouNoise_eq_wienerBP`;
the noise form of `TidyR7OrnsteinUhlenbeck.variance_ouProc`. -/
theorem integral_ouNoise_sq_le (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {η : ℝ} (hη : 0 < η)
    {t : ℝ} (ht : 0 < t) :
    ∫ ω, ouNoise η (fun u => bmReal W u ω) t ^ 2 ∂P ≤ 1 / (2 * η) := by
  have hsq := integral_wienerBP_sq (P := P) hB hW hcont (hasDerivAt_expMul η)
    (by fun_prop : Continuous fun u => exp (η * u) * η) le_rfl ht
  rw [integral_exp_sq hη.ne' 0 t, mul_zero, exp_zero] at hsq
  have e : (fun ω => ouNoise η (fun u => bmReal W u ω) t ^ 2) = fun ω => exp (-η * t) ^ 2
      * wienerBP W (fun u => exp (η * u)) (fun u => exp (η * u) * η) 0 t ω ^ 2 := by
    funext ω
    rw [ouNoise_eq_wienerBP hW0 η ω t, mul_pow]
  rw [e, integral_const_mul, hsq]
  have e1 : exp (-η * t) ^ 2 * exp (2 * η * t) = 1 := by
    rw [sq, ← exp_add, ← exp_add]; ring_nf; exact exp_zero
  have hp : 0 ≤ exp (-η * t) ^ 2 := sq_nonneg _
  rw [show exp (-η * t) ^ 2 * ((exp (2 * η * t) - 1) / (2 * η))
    = (exp (-η * t) ^ 2 * exp (2 * η * t) - exp (-η * t) ^ 2) / (2 * η) by ring, e1]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-! ### The discounted noise integral -/

/-- Cochrane (2023), (6.5), p. 197: the discounted absolute noise
`R = ∫_0^∞ e^{−au}|σ·noise_u| du` (a lower integral, possibly `∞`). -/
noncomputable def ouNoiseTail (a η σ : ℝ) (W : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ u in Set.Ioi 0, ENNReal.ofReal (exp (-a * u) * |σ * ouNoise η (fun v => bmReal W v ω) u|)

/-- Cochrane (2023), (6.5), p. 197: the integrand of `ouNoiseTail` is jointly measurable. -/
theorem measurable_ouNoiseTail_integrand (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (a η σ : ℝ) :
    Measurable fun p : Ω × ℝ =>
      ENNReal.ofReal (exp (-a * p.2) * |σ * ouNoise η (fun v => bmReal W v p.1) p.2|) :=
  ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable fun p : Ω × ℝ => exp (-a * p.2)).mul
    (continuous_abs.measurable.comp ((measurable_ouNoise_uncurry hW hcont η).const_mul σ)))

/-- Cochrane (2023), (6.5), p. 197: `R` is measurable. -/
theorem measurable_ouNoiseTail (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (a η σ : ℝ) :
    Measurable (ouNoiseTail a η σ W) :=
  (measurable_ouNoiseTail_integrand hW hcont a η σ).lintegral_prod_right'

/-- **Cochrane (2023), (6.5), p. 197: `E R ≤ V/a`** with `V = (1 + σ²/(2η))/2`, for `a > 0`
(Tonelli, `|x| ≤ (1 + x²)/2` and `integral_ouNoise_sq_le`). -/
theorem lintegral_ouNoiseTail_le (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {a η : ℝ} (ha : 0 < a)
    (hη : 0 < η) (σ : ℝ) :
    ∫⁻ ω, ouNoiseTail a η σ W ω ∂P ≤ ENNReal.ofReal ((1 + σ ^ 2 / (2 * η)) / 2 / a) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set V := (1 + σ ^ 2 / (2 * η)) / 2 with hV
  have hV0 : 0 ≤ V := by positivity
  have hinner : ∀ u ∈ Set.Ioi (0 : ℝ), ∫⁻ ω, ENNReal.ofReal (exp (-a * u)
      * |σ * ouNoise η (fun v => bmReal W v ω) u|) ∂P ≤ ENNReal.ofReal (exp (-a * u) * V) := by
    intro u hu
    have hm := memLp_ouNoise hB hW hcont hW0 η hu
    have hint : Integrable (fun ω => exp (-a * u)
        * ((1 + (σ * ouNoise η (fun v => bmReal W v ω) u) ^ 2) / 2)) P := by
      have h2 := (hm.const_mul σ).integrable_sq
      exact (((integrable_const 1).add h2).div_const 2).const_mul _
    calc ∫⁻ ω, ENNReal.ofReal (exp (-a * u) * |σ * ouNoise η (fun v => bmReal W v ω) u|) ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (exp (-a * u)
            * ((1 + (σ * ouNoise η (fun v => bmReal W v ω) u) ^ 2) / 2)) ∂P := by
          refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
          refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
          set x := σ * ouNoise η (fun v => bmReal W v ω) u
          nlinarith [sq_nonneg (|x| - 1), sq_abs x]
      _ = ENNReal.ofReal (∫ ω, exp (-a * u)
            * ((1 + (σ * ouNoise η (fun v => bmReal W v ω) u) ^ 2) / 2) ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal hint
            (Eventually.of_forall fun ω => by positivity)).symm
      _ ≤ ENNReal.ofReal (exp (-a * u) * V) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [integral_const_mul]
          refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
          rw [integral_div, integral_add (integrable_const 1)
            (hm.const_mul σ).integrable_sq, integral_const]
          simp only [probReal_univ, smul_eq_mul, one_mul, mul_pow]
          rw [integral_const_mul]
          have hs := integral_ouNoise_sq_le hB hW hcont hW0 hη hu
          have : σ ^ 2 * ∫ ω, ouNoise η (fun v => bmReal W v ω) u ^ 2 ∂P
              ≤ σ ^ 2 * (1 / (2 * η)) := mul_le_mul_of_nonneg_left hs (sq_nonneg σ)
          rw [hV]
          have e : σ ^ 2 * (1 / (2 * η)) = σ ^ 2 / (2 * η) := by ring
          linarith
  have hswap := lintegral_lintegral_swap (μ := P) (ν := volume.restrict (Set.Ioi (0 : ℝ)))
    (f := fun ω u => ENNReal.ofReal (exp (-a * u) * |σ * ouNoise η (fun v => bmReal W v ω) u|))
    (measurable_ouNoiseTail_integrand hW hcont a η σ).aemeasurable
  have hexp : IntegrableOn (fun u : ℝ => exp (-a * u) * V) (Set.Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 ha).mul_const V
  calc ∫⁻ ω, ouNoiseTail a η σ W ω ∂P
      = ∫⁻ u in Set.Ioi 0, ∫⁻ ω, ENNReal.ofReal (exp (-a * u)
          * |σ * ouNoise η (fun v => bmReal W v ω) u|) ∂P := hswap
    _ ≤ ∫⁻ u in Set.Ioi 0, ENNReal.ofReal (exp (-a * u) * V) :=
        setLIntegral_mono' measurableSet_Ioi hinner
    _ = ENNReal.ofReal (∫ u in Set.Ioi 0, exp (-a * u) * V) :=
        (ofReal_integral_eq_lintegral_ofReal hexp
          (Eventually.of_forall fun u => by positivity)).symm
    _ = ENNReal.ofReal (V / a) := by
        rw [integral_mul_const, integral_exp_mul_Ioi (by linarith : -a < 0), mul_zero, exp_zero]
        congr 1
        field_simp

/-- Cochrane (2023), (6.5), p. 197: on `{R < ∞}`, the discounted noise integral is bounded by
`R` at every date `t ≥ 0`: `|∫_0^t e^{−au}σ·noise_u du| ≤ R`. -/
theorem abs_integral_le_ouNoiseTail (hcont : ∀ ω, Continuous fun t => W t ω) (a η σ : ℝ)
    {ω : Ω} (hR : ouNoiseTail a η σ W ω ≠ ∞) {t : ℝ} (ht : 0 ≤ t) :
    |∫ u in (0 : ℝ)..t, exp (-a * u) * (σ * ouNoise η (fun v => bmReal W v ω) u)|
      ≤ (ouNoiseTail a η σ W ω).toReal := by
  set f : ℝ → ℝ := fun u => exp (-a * u) * (σ * ouNoise η (fun v => bmReal W v ω) u) with hf
  have hfc : Continuous f := by
    have := continuous_ouNoise η (continuous_bmReal (hcont ω))
    rw [hf]
    fun_prop
  have habs : ∀ u, |f u| = exp (-a * u) * |σ * ouNoise η (fun v => bmReal W v ω) u| := fun u => by
    rw [hf, abs_mul, abs_of_pos (exp_pos _)]
  refine (intervalIntegral.abs_integral_le_integral_abs ht).trans ?_
  rw [intervalIntegral.integral_of_le ht, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun u => abs_nonneg (f u))
    (hfc.abs.aestronglyMeasurable)]
  refine ENNReal.toReal_mono hR ?_
  simp only [habs, ouNoiseTail]
  exact lintegral_mono_set Set.Ioc_subset_Ioi_self

/-! ### Debt stays bounded with probability at least one half -/

/-- Cochrane (2023), (6.5), p. 197: with the surplus started at its mean (`s_0 = s̄`), debt is
`b_t = e^{at}b_0 − s̄(e^{at} − 1)/a − e^{at}∫_0^t e^{−au}σ·noise_u du` (`a ≠ 0`).
`TidyR7OrnsteinUhlenbeck.ouDebtProc_eq` at `s_0 = s̄`. -/
theorem ouDebtProc_eq_of_mean (hcont : ∀ ω, Continuous fun t => W t ω) {a : ℝ} (ha : a ≠ 0)
    (η sbar σ b0 : ℝ) (ω : Ω) (t : ℝ) :
    ouDebtProc a η sbar sbar σ b0 W t ω = exp (a * t) * b0 - sbar * (exp (a * t) - 1) / a
      - exp (a * t)
        * ∫ u in (0 : ℝ)..t, exp (-a * u) * (σ * ouNoise η (fun v => bmReal W v ω) u) := by
  have hw := continuous_bmReal (hcont ω)
  have hmean : ouMean η sbar sbar = fun _ => sbar := by
    funext u
    simp [ouMean]
  have hI : ∫ u in (0 : ℝ)..t, exp (-a * u) = (1 - exp (-a * t)) / a := by
    have hd : ∀ x ∈ Set.uIcc (0 : ℝ) t,
        HasDerivAt (fun u => -exp (-a * u) / a) (exp (-a * x)) x := fun x _ => by
      have h := (((hasDerivAt_id' x).const_mul (-a)).exp.neg).div_const a
      refine h.congr_deriv ?_
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun u => exp (-a * u)).intervalIntegrable 0 t)]
    simp only [mul_zero, exp_zero]
    ring
  have he : exp (a * t) * exp (-a * t) = 1 := by rw [← exp_add]; ring_nf; exact exp_zero
  have hσI : (∫ u in (0 : ℝ)..t, exp (-a * u) * (σ * ouNoise η (fun v => bmReal W v ω) u))
      = σ * ∫ u in (0 : ℝ)..t, exp (-a * u) * ouNoise η (fun v => bmReal W v ω) u := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext u
    ring
  simp only [ouDebtProc]
  rw [ouDebt_eq a b0 hw, debtMean, hmean, debtNoise, hσI, vocFrom,
    intervalIntegral.integral_mul_const, hI]
  have he' : exp (a * t) * exp (-(a * t)) = 1 := by rw [← exp_add]; simp
  simp only [mul_zero, exp_zero, one_mul]
  field_simp
  linear_combination sbar * he'

/-- **Cochrane (2023), p. 197, corrected for `r > g`: debt stays bounded with probability at
least one half.** For `a = r − g > 0`, `η > 0`, any `σ`, `b_0`, the surplus started at its mean
`s_0 = s̄`, and a mean surplus with `b_0 + (1 + σ²/(2η))/a ≤ s̄/a`: with probability at least
`1/2`, `b_t ≤ s̄/a` at every date `t ≥ 0`. -/
theorem ouDebtProc_bounded_half (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {a η : ℝ} (ha : 0 < a)
    (hη : 0 < η) (σ b0 : ℝ) {sbar : ℝ} (hs : b0 + (1 + σ ^ 2 / (2 * η)) / a ≤ sbar / a) :
    2⁻¹ ≤ P {ω | ∀ t, 0 ≤ t → ouDebtProc a η sbar sbar σ b0 W t ω ≤ sbar / a} := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set V := (1 + σ ^ 2 / (2 * η)) / 2 with hV
  have hV0 : 0 < V := by positivity
  set K := 2 * (V / a) with hK
  have hK0 : 0 < K := by positivity
  have hKs : b0 + K ≤ sbar / a := by
    rw [hK, hV]
    have : 2 * ((1 + σ ^ 2 / (2 * η)) / 2 / a) = (1 + σ ^ 2 / (2 * η)) / a := by ring
    linarith
  set R := ouNoiseTail a η σ W
  have hRm := measurable_ouNoiseTail hW hcont a η σ
  -- Markov: `P(R ≥ K) ≤ 1/2`
  have hmk : P {ω | ENNReal.ofReal K ≤ R ω} ≤ 2⁻¹ := by
    refine (meas_ge_le_lintegral_div hRm.aemeasurable (by simpa using hK0)
      ENNReal.ofReal_ne_top).trans ?_
    refine ENNReal.div_le_of_le_mul ?_
    rw [hK, ENNReal.ofReal_mul (by norm_num), ← mul_assoc, ENNReal.ofReal_ofNat,
      ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    exact lintegral_ouNoiseTail_le hB hW hcont hW0 ha hη σ
  have hgood : P {ω | R ω < ENNReal.ofReal K} ≥ 2⁻¹ := by
    have hc : {ω | R ω < ENNReal.ofReal K} = {ω | ENNReal.ofReal K ≤ R ω}ᶜ := by
      ext ω
      simp
    rw [hc, prob_compl_eq_one_sub (measurableSet_le measurable_const hRm)]
    calc (2⁻¹ : ℝ≥0∞) = 1 - 2⁻¹ := ENNReal.one_sub_inv_two.symm
      _ ≤ 1 - P {ω | ENNReal.ofReal K ≤ R ω} := tsub_le_tsub_left hmk 1
  refine hgood.trans (measure_mono fun ω hω t ht => ?_)
  simp only [Set.mem_ofPred_eq] at hω
  have hRne : R ω ≠ ∞ := ne_top_of_lt hω
  have hRK : (R ω).toReal ≤ K := ENNReal.toReal_le_of_le_ofReal hK0.le hω.le
  have hbound := abs_integral_le_ouNoiseTail hcont a η σ hRne ht
  rw [ouDebtProc_eq_of_mean hcont ha.ne' η sbar σ b0 ω t]
  set e := exp (a * t)
  have he0 : 0 < e := exp_pos _
  have hkey : sbar * (e - 1) / a = e * (sbar / a) - sbar / a := by ring
  have h1 := (abs_le.1 (hbound.trans hRK)).1
  have h2 : e * (b0 + K - sbar / a) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos he0.le (by linarith)
  nlinarith

/-- **Cochrane (2023), p. 197: the almost-sure claim fails for every `r > g`.** For
`a = r − g > 0`, `η > 0` and any `σ`, `b_0`, with the mean surplus `s̄ = ab_0 + 1 + σ²/(2η)`
(and `s_0 = s̄`), it is false that almost surely debt eventually exceeds every bound. -/
theorem ouDebtProc_not_ae_unbounded (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {a η : ℝ} (ha : 0 < a)
    (hη : 0 < η) (σ b0 : ℝ) :
    ¬ ∀ᵐ ω ∂P, ∀ M : ℝ, ∃ᶠ t in atTop, M < ouDebtProc a η (a * b0 + (1 + σ ^ 2 / (2 * η)))
      (a * b0 + (1 + σ ^ 2 / (2 * η))) σ b0 W t ω := by
  intro hae
  set sbar := a * b0 + (1 + σ ^ 2 / (2 * η))
  have hs : b0 + (1 + σ ^ 2 / (2 * η)) / a ≤ sbar / a := by
    change b0 + _ ≤ (a * b0 + (1 + σ ^ 2 / (2 * η))) / a
    rw [add_div (a * b0) (1 + σ ^ 2 / (2 * η)) a, mul_div_cancel_left₀ _ ha.ne']
  have hhalf := ouDebtProc_bounded_half hB hW hcont hW0 ha hη σ b0 hs
  have h0 : P {ω | ∀ t, 0 ≤ t → ouDebtProc a η sbar sbar σ b0 W t ω ≤ sbar / a} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with ω hω hall
    obtain ⟨t, ht1, ht2⟩ := ((hω (sbar / a)).and_eventually (eventually_ge_atTop 0)).exists
    exact absurd (hall t ht2) (not_le.2 ht1)
  rw [h0] at hhalf
  exact absurd hhalf (by simp)

/-! ### Non-vacuity on the constructed Brownian motion -/

open Cochrane.FiscalConstraints.TidyR7BrownianExist
open Cochrane.FiscalConstraints.TidyR7BrownianSchauder

/-- Cochrane (2023), p. 197 (non-vacuity): on bmPath, with `r − g = +1%`, `η = σ = 1`, `b_0 = 0`
and `s_0 = s̄ = 3/2`, with probability at least `1/2` debt never exceeds `150`. -/
theorem bmPath_ouDebt_bounded_half :
    2⁻¹ ≤ gaussSeq {ω | ∀ t, 0 ≤ t → ouDebtProc (1 / 100) 1 (3 / 2) (3 / 2) 1 0 bmPath t ω
      ≤ 3 / 2 / (1 / 100)} :=
  ouDebtProc_bounded_half isPreBrownianReal_bmPath measurable_bmPath continuous_bmPath
    bmPath_zero (by norm_num) one_pos 1 0 (by norm_num)

end Cochrane.FiscalConstraints.TidyR8OUDebtExplosive
