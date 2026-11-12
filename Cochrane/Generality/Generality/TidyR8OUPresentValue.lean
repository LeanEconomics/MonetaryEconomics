/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.TidyR7ItoInnovation
import Generality.TidyR8ConditionalFubini
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The present value of the actual AR(1) surplus path: `E_t∫_0^∞ e^{−rτ}s_{t+τ}dτ = s_t/(r + η)`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.6.3, p. 77 (the
AR(1) example after (3.44)–(3.45)): for `ds = −ηs dt + σ dε`,
`E_t∫_0^∞ e^{−rτ}s_{t+τ}dτ = ∫_0^∞ e^{−(r+η)τ}s_t dτ = s_t/(r + η)`, and the innovation of the
present value is `σ/(r + η) dε`. `TidyR7ItoInnovation.pv_expected_path` proved the first equality
for the forecast path `τ ↦ E_t s_{t+τ}` only. Here the integral is over the **actual stochastic
path**, and `E_t` is moved inside by the conditional Fubini theorem
(`TidyR8ConditionalFubini.condExp_integral_interchange`).

## A path-regular version of the surplus

`TidyR7ItoInnovation.ou` is defined through an Itô integral, which is an a.s. class for each `u`,
so `τ ↦ s_{t+τ}(ω)` is not a path. For a Brownian motion with continuous paths,
`ouPath` is the pathwise formula obtained by integrating the Wiener integral by parts,
`s_u = e^{−ηu}(s₀ + σ(e^{ηu}W_u − W_0 − η∫_0^u e^{ηv}W_v dv))`:
* `ouI_byParts`: a.s. `∫_0^u e^{ηv}dW_v = e^{ηu}W_u − W_0 − η∫_0^u e^{ηv}W_v dv` (Itô's product
  rule for `e^{ηu}·W_u`, `TidyR7ItoProductRule.product_rule_pathwise`);
* `ouPath_ae_eq`: `ouPath` is a modification of `ou` (`ouPath_u = ou_u` a.s. for each `u ≥ 0`);
* `continuous_ouPath`, `measurable_ouPath`, `measurable_uncurry_pv`: continuous paths and joint
  measurability, so `∫_0^∞ e^{−rτ}s_{t+τ}(ω) dτ` is a genuine path integral.

## Main results (`0 < r`, `0 < r + η`)

* `integral_abs_ou_le`: `E|s_u| ≤ e^{−ηu}|s₀| + |σ|(1 + u)e^{max(−η,0)u}`;
  `integrable_uncurry_pv`: `∫_0^∞ e^{−rτ}E|s_{t+τ}| dτ < ∞` (in product form), hence
  `pv_integrable_ae`: for a.e. `ω` the discounted path is Lebesgue integrable on `(0, ∞)`;
* `pv_condExp` (**p. 77**): a.s. `E_t[∫_0^∞ e^{−rτ}s_{t+τ}dτ] = s_t/(r + η)`;
* `pv_revision` (**the innovation `σ/(r + η) dε` as an exact identity of conditional
  expectations**): for `0 ≤ q ≤ t`, a.s.
  `E_t[PV_t] − E_q[PV_t] = (σ/(r + η))e^{−ηt}∫_q^t e^{ηv}dW_v`, and
  `pv_revision_sq_le` (`η ≥ 0`): it is within mean square `σ²η²(t − q)³/(r + η)²` of
  `(σ/(r + η))(W_t − W_q)`;
* `pv_sigma_zero`: with `σ = 0` the path is deterministic and `PV_t = e^{−ηt}s₀/(r + η)` for
  every `ω` (`ContinuousLinear.ar1_pv`).

## Hypotheses and non-vacuity

The results assume `r > 0` besides the book's `r + η > 0` (for `η ≤ 0` the latter implies the
former). For `η > 0` the variance of `s_u` tends to `σ²/(2η)`, so `E|s_u|` does not vanish and
`r > 0` is what makes `∫_0^∞e^{−rτ}E|s_{t+τ}|dτ` finite; that the interchange fails for `r ≤ 0`
is not proved here. On the constructed motion `bmPath`
(continuous paths for every `ω`), `bmPath_pv_revision_pos`: the revision has positive mean square
for `σ ≠ 0`, `0 ≤ q < t`.
-/

namespace Cochrane.Generality.TidyR8OUPresentValue

open MeasureTheory ProbabilityTheory Filter Topology Function
open Cochrane.Generality.TidyR7StieltjesSums Cochrane.Generality.TidyR7BrownianTools
  Cochrane.Generality.TidyR7BrownianQV Cochrane.Generality.TidyR7ItoL2
  Cochrane.Generality.TidyR7ItoSums Cochrane.Generality.TidyR7ItoIntegral
  Cochrane.Generality.TidyR7ItoUnbounded Cochrane.Generality.TidyR7ItoProducts
  Cochrane.Generality.TidyR7ItoProcess Cochrane.Generality.TidyR7ItoProductRule
  Cochrane.Generality.TidyR7ItoBridge Cochrane.Generality.TidyR7BrownianExist
  Cochrane.Generality.TidyR7ItoDiscountFactorCex Cochrane.Generality.TidyR7ItoInnovation
  Cochrane.Generality.TidyR8ConditionalFubini Cochrane.Generality.TidyR7BrownianSchauder
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → ℝ}

/-! ## The pathwise AR(1) surplus -/

/-- **Cochrane (2023), §3.6.3, p. 77: the AR(1) surplus as a path.** The pathwise formula
`s_u = e^{−ηu}(s₀ + σ(e^{ηu}W_u − W_0 − η∫_0^u e^{ηv}W_v dv))`, the integration by parts of
`e^{−ηu}(s₀ + σ∫_0^u e^{ηv}dW_v)` (`ouPath_ae_eq`). -/
noncomputable def ouPath (W : ℝ≥0 → Ω → ℝ) (η σ s0 u : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-(η * u)) * (s0 + σ * (Real.exp (η * u) * bmReal W u ω - bmReal W 0 ω
    - η * ∫ v in (0 : ℝ)..u, Real.exp (η * v) * bmReal W v ω))

/-- **Cochrane (2023), §3.6.3, p. 77: the present value of the actual surplus path**,
`PV_t(ω) = ∫_0^∞ e^{−rτ}s_{t+τ}(ω) dτ`. -/
noncomputable def pvPath (W : ℝ≥0 → Ω → ℝ) (r η σ s0 t : ℝ) (ω : Ω) : ℝ :=
  ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * ouPath W η σ s0 (t + τ) ω

/-- Cochrane (2023), §3.6.3, p. 77: `u ↦ e^{ηu}` has derivative `ηe^{ηu}`.
The same fact as `ContinuousLinear.hasDerivAt_expDisc`; Mathlib `HasDerivAt.exp`. -/
theorem hasDerivAt_exp_mul (η u : ℝ) :
    HasDerivAt (fun u => Real.exp (η * u)) (η * Real.exp (η * u)) u :=
  (((hasDerivAt_id u).const_mul η).exp).congr_deriv (by simp; ring)

/-- **Cochrane (2023), §3.6.3, p. 77: the Wiener integral by parts.** If `W` has continuous
paths, for `u ≥ 0`, a.s. `∫_0^u e^{ηv}dW_v = e^{ηu}W_u − W_0 − η∫_0^u e^{ηv}W_v dv`.
Itô's product rule for `e^{ηu}·W_u` (`TidyR7ItoProductRule.product_rule_pathwise`). -/
theorem ouI_byParts (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω) (η : ℝ) {u : ℝ}
    (hu : 0 ≤ u) :
    ouI μ 𝓕 W η u =ᵐ[μ] fun ω => Real.exp (η * u) * bmReal W u ω - bmReal W 0 ω
      - η * ∫ v in (0 : ℝ)..u, Real.exp (η * v) * bmReal W v ω := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  rcases hu.lt_or_eq with hu | hu
  · have cE : Continuous fun v => Real.exp (η * v) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have gc : Continuous fun v => η * Real.exp (η * v) := continuous_const.mul cE
    obtain ⟨Cg, hCg⟩ := exists_bound_Icc gc 0 u
    have hX : ItoProcess μ 𝓕 W (fun v _ => Real.exp (η * v))
        (fun v _ => η * Real.exp (η * v)) (fun _ _ => 0) 0 u Cg 0 :=
      itoProcess_det hBM hWm h𝓕 le_rfl gc.continuousOn hCg
        (fun v _ => ftc_split (hasDerivAt_exp_mul η) gc 0 v)
    have hY := itoProcess_bm (t := u) hBM hWm h𝓕 (le_refl (0 : ℝ))
    have hpr := product_rule_pathwise hBM hWm h𝓕 le_rfl hu hX hY
      (ae_of_all _ fun _ => cE.continuousOn)
      (ae_of_all _ fun ω => (continuous_bmReal (hcont ω)).continuousOn)
    have e1 : (fun v (ω : Ω) => (fun v (_ : Ω) => Real.exp (η * v)) v ω
        * (fun _ _ => (1 : ℝ)) v ω) = fun v _ => Real.exp (η * v) := by
      funext v ω
      simp
    have e2 : (fun v ω => bmReal W v ω * (fun _ _ => (0 : ℝ)) v ω) = fun _ _ => 0 := by
      funext v ω
      simp
    have z := itoInt_const hBM hWm h𝓕 le_rfl hu.le (c := fun _ => (0 : ℝ))
      stronglyMeasurable_const (C := 0) fun _ => by simp
    rw [e1, e2] at hpr
    filter_upwards [hpr, z] with ω h0 h1
    rw [h1] at h0
    simp only [ouI, mul_zero, intervalIntegral.integral_zero, zero_add, zero_mul, add_zero,
      Real.exp_zero, one_mul] at h0 ⊢
    have e3 : ∫ v in (0 : ℝ)..u, bmReal W v ω * (η * Real.exp (η * v)) =
        η * ∫ v in (0 : ℝ)..u, Real.exp (η * v) * bmReal W v ω := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext v
      ring
    rw [e3] at h0
    linarith
  · subst hu
    refine ae_of_all _ fun ω => ?_
    simp [ouI, itoInt_of_le]

/-- **Cochrane (2023), §3.6.3, p. 77: the pathwise surplus is a modification of the AR(1)
process.** If `W` has continuous paths, `ouPath_u = ou_u` a.s. for every `u ≥ 0`. -/
theorem ouPath_ae_eq (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω) (η σ s0 : ℝ) {u : ℝ}
    (hu : 0 ≤ u) : ouPath W η σ s0 u =ᵐ[μ] ou μ 𝓕 W η σ s0 u := by
  filter_upwards [ouI_byParts hBM hWm h𝓕 hcont η hu] with ω h
  simp only [ouPath, ou, h]

/-- Cochrane (2023), §3.6.3, p. 77: the surplus path `u ↦ ouPath_u(ω)` is continuous when the
Brownian path is (Mathlib `intervalIntegral.continuous_primitive`). -/
theorem continuous_ouPath {ω : Ω} (hcont : Continuous fun t => W t ω) (η σ s0 : ℝ) :
    Continuous fun u => ouPath W η σ s0 u ω := by
  have hb := continuous_bmReal hcont
  have hi : Continuous fun v => Real.exp (η * v) * bmReal W v ω :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hb
  have hp := intervalIntegral.continuous_primitive (μ := volume)
    (fun a b => hi.intervalIntegrable a b) 0
  unfold ouPath
  fun_prop

/-- Cochrane (2023), §3.6.3, p. 77: `(v, ω) ↦ e^{ηv}W_v(ω)` is jointly measurable when `W` has
continuous paths (Mathlib `measurable_uncurry_of_continuous_of_measurable`). -/
theorem measurable_uncurry_expW (hWm : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (η : ℝ) :
    Measurable (uncurry fun v ω => Real.exp (η * v) * bmReal W v ω) :=
  measurable_uncurry_of_continuous_of_measurable
    (fun ω => (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (continuous_bmReal (hcont ω)))
    (fun _ => measurable_const.mul (hWm _))

/-- Cochrane (2023), §3.6.3, p. 77: each `ouPath_u` is measurable when `W` has continuous paths
(the time integral is measurable in `ω`, Mathlib `StronglyMeasurable.integral_prod_left`). -/
theorem measurable_ouPath (hWm : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω)
    (η σ s0 u : ℝ) : Measurable (ouPath W η σ s0 u) := by
  have hj := (measurable_uncurry_expW hWm hcont η).stronglyMeasurable
  have h1 := hj.integral_prod_left (μ := volume.restrict (Set.Ioc 0 u))
  have h2 := hj.integral_prod_left (μ := volume.restrict (Set.Ioc u 0))
  have hI : Measurable fun ω => ∫ v in (0 : ℝ)..u, Real.exp (η * v) * bmReal W v ω :=
    (h1.sub h2).measurable
  unfold ouPath
  exact measurable_const.mul (measurable_const.add (measurable_const.mul
    (((measurable_const.mul (hWm _)).sub (hWm _)).sub (measurable_const.mul hI))))

/-- Cochrane (2023), §3.6.3, p. 77: the discounted surplus `(τ, ω) ↦ e^{−rτ}s_{t+τ}(ω)` is
jointly measurable when `W` has continuous paths. -/
theorem measurable_uncurry_pv (hWm : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (r η σ s0 t : ℝ) :
    Measurable (uncurry fun τ ω => Real.exp (-(r * τ)) * ouPath W η σ s0 (t + τ) ω) :=
  measurable_uncurry_of_continuous_of_measurable
    (fun ω => (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
      ((continuous_ouPath (hcont ω) η σ s0).comp (continuous_const.add continuous_id)))
    (fun _ => measurable_const.mul (measurable_ouPath hWm hcont η σ s0 _))

/-! ## Integrability: `∫_0^∞ e^{−rτ}E|s_{t+τ}| dτ < ∞` -/

/-- Cochrane (2023), §3.6.3, p. 77: the AR(1) surplus at a date is integrable. -/
theorem integrable_ou (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (η σ s0 u : ℝ) : Integrable (ou μ 𝓕 W η σ s0 u) μ := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have hI := (memLp_itoInt hBM hWm h𝓕 le_rfl (ouIntegrand (μ := μ) (𝓕 := 𝓕) η u)).integrable
    one_le_two
  refine ((integrable_const (Real.exp (-(η * u)) * s0)).add
    (hI.const_mul (Real.exp (-(η * u)) * σ))).congr (ae_of_all _ fun ω => ?_)
  simp only [ou, ouI, Pi.add_apply]
  ring

/-- Cochrane (2023), §3.6.3, p. 77: the AR(1) surplus at date `t` is `𝓕_t`-measurable (the
Wiener integral is adapted, `TidyR7ItoIntegral.stronglyMeasurable_itoInt`). -/
theorem stronglyMeasurable_ou (η σ s0 t : ℝ) :
    StronglyMeasurable[𝓕 t] (ou μ 𝓕 W η σ s0 t) := by
  unfold ou ouI
  exact stronglyMeasurable_const.mul
    (stronglyMeasurable_const.add (stronglyMeasurable_const.mul stronglyMeasurable_itoInt))

/-- **Cochrane (2023), §3.6.3, p. 77: the mean absolute surplus.** For `u ≥ 0`,
`E|s_u| ≤ e^{−ηu}|s₀| + |σ|(1 + u)e^{max(−η,0)u}` (Wiener isometry and Cauchy–Schwarz). -/
theorem integral_abs_ou_le (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (η σ s0 : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    ∫ ω, |ou μ 𝓕 W η σ s0 u ω| ∂μ ≤
      Real.exp (-(η * u)) * |s0| + |σ| * ((1 + u) * Real.exp (max (-η) 0 * u)) := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  set a := max (-η) 0 with ha
  have hmem := memLp_itoInt hBM hWm h𝓕 le_rfl (ouIntegrand (μ := μ) (𝓕 := 𝓕) η u)
  have hsq := sq_integral_abs_le hmem
  have hI2 := integral_itoInt_deterministic_sq hBM hWm h𝓕 le_rfl hu (C := Real.exp (|η| * u))
    (h := fun v => Real.exp (η * v))
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    (fun v hv => abs_exp_le η hv)
  have hpt : ∀ v ∈ Set.Icc 0 u, (Real.exp (-(η * u)) * Real.exp (η * v)) ^ 2 ≤
      Real.exp (a * u) ^ 2 := fun v hv => by
    have h1 : Real.exp (-(η * u)) * Real.exp (η * v) ≤ Real.exp (a * u) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have h2 : -η ≤ a := le_max_left _ _
      have h3 : 0 ≤ a := le_max_right _ _
      nlinarith [hv.1, hv.2]
    exact pow_le_pow_left₀ (by positivity) h1 2
  have hbd : ∫ v in (0 : ℝ)..u, (Real.exp (-(η * u)) * Real.exp (η * v)) ^ 2 ≤
      u * Real.exp (a * u) ^ 2 := by
    have := intervalIntegral.integral_mono_on (μ := volume) hu
      (f := fun v => (Real.exp (-(η * u)) * Real.exp (η * v)) ^ 2)
      ((((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
        ).pow 2).intervalIntegrable _ _) intervalIntegrable_const hpt
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  have hsplit : ∫ v in (0 : ℝ)..u, (Real.exp (-(η * u)) * Real.exp (η * v)) ^ 2 =
      Real.exp (-(η * u)) ^ 2 * ∫ v in (0 : ℝ)..u, Real.exp (η * v) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext v
    ring
  have hA : Real.exp (-(η * u)) * ∫ ω, |ouI μ 𝓕 W η u ω| ∂μ ≤ (1 + u) * Real.exp (a * u) := by
    have h0 : 0 ≤ Real.exp (-(η * u)) * ∫ ω, |ouI μ 𝓕 W η u ω| ∂μ :=
      mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => abs_nonneg _)
    have h1 : 0 ≤ (1 + u) * Real.exp (a * u) := by positivity
    refine (pow_le_pow_iff_left₀ h0 h1 two_ne_zero).1 ?_
    have hI2' : ∫ ω, ouI μ 𝓕 W η u ω ^ 2 ∂μ = ∫ v in (0 : ℝ)..u, Real.exp (η * v) ^ 2 := hI2
    calc (Real.exp (-(η * u)) * ∫ ω, |ouI μ 𝓕 W η u ω| ∂μ) ^ 2
        = Real.exp (-(η * u)) ^ 2 * (∫ ω, |ouI μ 𝓕 W η u ω| ∂μ) ^ 2 := by ring
      _ ≤ Real.exp (-(η * u)) ^ 2 * ∫ ω, ouI μ 𝓕 W η u ω ^ 2 ∂μ :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ ≤ u * Real.exp (a * u) ^ 2 := by rw [hI2', ← hsplit]; exact hbd
      _ ≤ ((1 + u) * Real.exp (a * u)) ^ 2 := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
  have hIi : Integrable (fun ω => |ouI μ 𝓕 W η u ω|) μ := (hmem.integrable one_le_two).abs
  have hg : Integrable (fun ω => Real.exp (-(η * u)) * |s0| +
      |σ| * (Real.exp (-(η * u)) * |ouI μ 𝓕 W η u ω|)) μ :=
    (integrable_const _).add ((hIi.const_mul _).const_mul _)
  have hle := integral_mono_of_nonneg (ae_of_all _ fun ω => abs_nonneg _) hg
    (ae_of_all _ fun ω => by
      change |ou μ 𝓕 W η σ s0 u ω| ≤ _
      have e : ou μ 𝓕 W η σ s0 u ω =
          Real.exp (-(η * u)) * s0 + σ * (Real.exp (-(η * u)) * ouI μ 𝓕 W η u ω) := by
        simp only [ou]
        ring
      rw [e]
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)])
  rw [integral_add (integrable_const _) ((hIi.const_mul _).const_mul _), integral_const,
    integral_const_mul, integral_const_mul] at hle
  simp only [probReal_univ, smul_eq_mul, one_mul] at hle
  calc ∫ ω, |ou μ 𝓕 W η σ s0 u ω| ∂μ
      ≤ Real.exp (-(η * u)) * |s0| +
        |σ| * (Real.exp (-(η * u)) * ∫ ω, |ouI μ 𝓕 W η u ω| ∂μ) := hle
    _ ≤ _ := by gcongr

/-- Cochrane (2023), §3.6.3, p. 77: the dominating function
`e^{−rτ}(e^{−η(t+τ)}|s₀| + |σ|(1 + t + τ)e^{max(−η,0)(t+τ)})` is integrable on `(0, ∞)` for
`r > 0`, `r + η > 0`. -/
theorem integrableOn_pv_bound {r η : ℝ} (hr : 0 < r) (hrη : 0 < r + η) (σ s0 t : ℝ) :
    IntegrableOn (fun τ => Real.exp (-(r * τ)) * (Real.exp (-(η * (t + τ))) * |s0| +
      |σ| * ((1 + (t + τ)) * Real.exp (max (-η) 0 * (t + τ))))) (Set.Ioi 0) := by
  set a := max (-η) 0 with ha
  have hc : 0 < r - a := by
    rcases le_total (-η) 0 with h | h
    · rw [ha, max_eq_right h]; linarith
    · rw [ha, max_eq_left h]; linarith
  have i1 := (integrableOn_exp_mul_Ioi (a := -(r + η)) (by linarith) 0).const_mul
    (|s0| * Real.exp (-(η * t)))
  have i2 := (integrableOn_exp_mul_Ioi (a := -(r - a)) (by linarith) 0).const_mul
    (|σ| * (1 + t) * Real.exp (a * t))
  have i3 : IntegrableOn (fun τ : ℝ => τ * Real.exp (-(r - a) * τ)) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := r - a)
      (by norm_num) one_pos hc
    refine h.congr_fun (fun τ _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul]
  have i3' := i3.const_mul (|σ| * Real.exp (a * t))
  refine IntegrableOn.congr_fun ((i1.add i2).add i3') (fun τ _ => ?_) measurableSet_Ioi
  have e1 : Real.exp (-(r * τ)) * Real.exp (-(η * (t + τ))) =
      Real.exp (-(η * t)) * Real.exp (-(r + η) * τ) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(r * τ)) * Real.exp (a * (t + τ)) =
      Real.exp (a * t) * Real.exp (-(r - a) * τ) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  simp only [Pi.add_apply]
  linear_combination (-|s0|) * e1 - (|σ| * (1 + t + τ)) * e2

/-- **Cochrane (2023), §3.6.3, p. 77 (`∫_0^∞ e^{−rτ}E|s_{t+τ}|dτ < ∞`):** for `r > 0`,
`r + η > 0`, `t ≥ 0` and `W` with continuous paths, the discounted surplus
`(τ, ω) ↦ e^{−rτ}s_{t+τ}(ω)` is integrable on `(0, ∞) × Ω`. -/
theorem integrable_uncurry_pv (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω) {r η : ℝ}
    (hr : 0 < r) (hrη : 0 < r + η) (σ s0 : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (uncurry fun τ ω => Real.exp (-(r * τ)) * ouPath W η σ s0 (t + τ) ω)
      ((volume.restrict (Set.Ioi 0)).prod μ) := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have hm := measurable_uncurry_pv hWm hcont r η σ s0 t
  have hae : ∀ τ ∈ Set.Ioi (0 : ℝ), ouPath W η σ s0 (t + τ) =ᵐ[μ] ou μ 𝓕 W η σ s0 (t + τ) :=
    fun τ hτ => ouPath_ae_eq hBM hWm h𝓕 hcont η σ s0 (by linarith [hτ.out])
  refine integrable_uncurry_of_integral_abs hm.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ hτ => ?_)) ?_
  · exact ((integrable_ou hBM hWm h𝓕 η σ s0 (t + τ)).congr (hae τ hτ).symm).const_mul _
  refine Integrable.mono' (integrableOn_pv_bound hr hrη σ s0 t)
    (StronglyMeasurable.integral_prod_right
      (f := fun τ ω => |Real.exp (-(r * τ)) * ouPath W η σ s0 (t + τ) ω|)
      (by exact (continuous_abs.measurable.comp hm).stronglyMeasurable)).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ hτ => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
  have e : ∫ ω, |Real.exp (-(r * τ)) * ouPath W η σ s0 (t + τ) ω| ∂μ =
      Real.exp (-(r * τ)) * ∫ ω, |ou μ 𝓕 W η σ s0 (t + τ) ω| ∂μ := by
    simp_rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [integral_const_mul]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hae τ hτ] with ω hω
    rw [hω]
  rw [e]
  exact mul_le_mul_of_nonneg_left
    (integral_abs_ou_le hBM hWm h𝓕 η σ s0 (by linarith [hτ.out] : 0 ≤ t + τ))
    (Real.exp_pos _).le

/-- **Cochrane (2023), §3.6.3, p. 77: the present value of the actual path is a genuine
integral.** For a.e. `ω`, `τ ↦ e^{−rτ}s_{t+τ}(ω)` is Lebesgue integrable on `(0, ∞)` (`r > 0`,
`r + η > 0`, `t ≥ 0`). -/
theorem pv_integrable_ae (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω) {r η : ℝ}
    (hr : 0 < r) (hrη : 0 < r + η) (σ s0 : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂μ, IntegrableOn (fun τ => Real.exp (-(r * τ)) * ouPath W η σ s0 (t + τ) ω)
      (Set.Ioi 0) := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have h := integrable_uncurry_pv hBM hWm h𝓕 hcont hr hrη σ s0 ht
  exact ((integrable_prod_iff' h.aestronglyMeasurable).1 h).1

/-! ## `E_t ∫ = ∫ E_t`: the present value and its innovation -/

/-- **Cochrane (2023), §3.6.3, p. 77: `E_t∫_0^∞ e^{−rτ}s_{t+τ}dτ = s_t/(r + η)` over the actual
stochastic path.** For `r > 0`, `r + η > 0`, `t ≥ 0` and `W` with continuous paths, a.s.
`E_t[PV_t] = s_t/(r + η)`. The conditional Fubini theorem
(`TidyR8ConditionalFubini.condExp_integral_interchange`) with the version
`Y(τ, ω) = e^{−rτ}e^{−ητ}s_t(ω)` of `E_t[e^{−rτ}s_{t+τ}]` (`TidyR7ItoInnovation.forecast_condExp`),
then `ContinuousLinear.ar1_pv`. -/
theorem pv_condExp (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω) {r η : ℝ}
    (hr : 0 < r) (hrη : 0 < r + η) (σ s0 : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ[pvPath W r η σ s0 t | 𝓕 t] =ᵐ[μ] fun ω => ouPath W η σ s0 t ω / (r + η) := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  set Y : ℝ → Ω → ℝ := fun τ ω => Real.exp (-(r * τ)) *
    (Real.exp (-(η * τ)) * ou μ 𝓕 W η σ s0 t ω) with hYdef
  have hsm := stronglyMeasurable_ou (μ := μ) (𝓕 := 𝓕) (W := W) η σ s0 t
  have hY : @StronglyMeasurable (ℝ × Ω) ℝ _ (@Prod.instMeasurableSpace ℝ Ω _ (𝓕 t))
      (uncurry Y) := by
    let _ : MeasurableSpace Ω := 𝓕 t
    have hc : Continuous fun τ : ℝ => Real.exp (-(r * τ)) * Real.exp (-(η * τ)) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)
    have hm : Measurable fun p : ℝ × Ω =>
        (Real.exp (-(r * p.1)) * Real.exp (-(η * p.1))) * ou μ 𝓕 W η σ s0 t p.2 :=
      (hc.measurable.comp measurable_fst).mul (hsm.measurable.comp measurable_snd)
    have e : uncurry Y = fun p : ℝ × Ω =>
        (Real.exp (-(r * p.1)) * Real.exp (-(η * p.1))) * ou μ 𝓕 W η σ s0 t p.2 := by
      funext p
      obtain ⟨τ, ω⟩ := p
      simp only [hYdef, uncurry_apply_pair]
      ring
    rw [e]
    exact hm.stronglyMeasurable
  have hXY : ∀ᵐ τ ∂(volume.restrict (Set.Ioi (0 : ℝ))), Y τ =ᵐ[μ]
      μ[fun ω => Real.exp (-(r * τ)) * ouPath W η σ s0 (t + τ) ω | 𝓕 t] := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ hτ => ?_)
    have hτ' : (0 : ℝ) < τ := hτ
    have e : (fun ω => Real.exp (-(r * τ)) * ouPath W η σ s0 (t + τ) ω) =
        Real.exp (-(r * τ)) • ouPath W η σ s0 (t + τ) := by
      funext ω
      simp [smul_eq_mul]
    rw [e]
    filter_upwards [condExp_smul (μ := μ) (Real.exp (-(r * τ))) (ouPath W η σ s0 (t + τ)) (𝓕 t),
      condExp_congr_ae (m := 𝓕 t) (ouPath_ae_eq hBM hWm h𝓕 hcont η σ s0
        (by linarith : 0 ≤ t + τ)),
      forecast_condExp hBM hWm h𝓕 η σ s0 hτ'.le ht] with ω h1 h2 h3
    rw [h1, Pi.smul_apply, smul_eq_mul, h2, h3]
  have hX := integrable_uncurry_pv hBM hWm h𝓕 hcont hr hrη σ s0 ht
  have hI := condExp_integral_interchange (𝓕.le t) hX hY hXY
  filter_upwards [hI, ouPath_ae_eq hBM hWm h𝓕 hcont η σ s0 ht] with ω h1 h2
  change μ[fun ω => ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * ouPath W η σ s0 (t + τ) ω | 𝓕 t] ω
    = _
  rw [h1, h2]
  exact ContinuousLinear.ar1_pv hrη

/-- **Cochrane (2023), §3.6.3, p. 77: the innovation of the present value is `σ/(r + η) dε`,
exactly, as a revision of conditional expectations.** For `0 ≤ q ≤ t`, `r > 0`, `r + η > 0`, a.s.
`E_t[PV_t] − E_q[PV_t] = (σ/(r + η))e^{−ηt}∫_q^t e^{ηv}dW_v`, the `dW`-loading at `v` being
`(σ/(r + η))e^{−η(t−v)} → σ/(r + η)` as `v → t`. Tower property, `pv_condExp`,
`TidyR7ItoInnovation.pv_innovation`. -/
theorem pv_revision (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω) {r η : ℝ}
    (hr : 0 < r) (hrη : 0 < r + η) (σ s0 : ℝ) {q t : ℝ} (hq : 0 ≤ q) (hqt : q ≤ t) :
    (fun ω => μ[pvPath W r η σ s0 t | 𝓕 t] ω - μ[pvPath W r η σ s0 t | 𝓕 q] ω) =ᵐ[μ]
      fun ω => σ / (r + η) * Real.exp (-(η * t))
        * itoInt μ 𝓕 W (fun v _ => Real.exp (η * v)) q t ω := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have ht : 0 ≤ t := hq.trans hqt
  have h1 := pv_condExp hBM hWm h𝓕 hcont hr hrη σ s0 ht
  have hpath := ouPath_ae_eq hBM hWm h𝓕 hcont η σ s0 ht
  have h2 : (fun ω => ouPath W η σ s0 t ω / (r + η)) =ᵐ[μ]
      fun ω => ou μ 𝓕 W η σ s0 t ω / (r + η) := by
    filter_upwards [hpath] with ω hω
    rw [hω]
  have htower := condExp_condExp_of_le (μ := μ) (f := pvPath W r η σ s0 t) (𝓕.mono hqt) (𝓕.le t)
  have hq' : μ[pvPath W r η σ s0 t | 𝓕 q] =ᵐ[μ]
      μ[fun ω => ou μ 𝓕 W η σ s0 t ω / (r + η) | 𝓕 q] :=
    htower.symm.trans (condExp_congr_ae (h1.trans h2))
  filter_upwards [h1, h2, hq', pv_innovation hBM hWm h𝓕 r η σ s0 hq hqt] with ω e1 e2 e3 e4
  rw [e1, e2, e3, e4]

/-- **Cochrane (2023), §3.6.3, eq. (3.45), p. 77: the revision is `σ/(r + η)(W_t − W_q)` to first
order.** For `η ≥ 0`, `r > 0`, `0 ≤ q ≤ t`:
`E[(E_t PV_t − E_q PV_t − (σ/(r + η))(W_t − W_q))²] ≤ σ²η²(t − q)³/(r + η)²`, against
`E[((σ/(r + η))(W_t − W_q))²] = σ²(t − q)/(r + η)²`.
The bound of `TidyR7ItoInnovation.pv_innovation_sq_le`, from which it is proved. -/
theorem pv_revision_sq_le (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω) {r η : ℝ}
    (hr : 0 < r) (hη : 0 ≤ η) (σ s0 : ℝ) {q t : ℝ} (hq : 0 ≤ q) (hqt : q ≤ t) :
    ∫ ω, (μ[pvPath W r η σ s0 t | 𝓕 t] ω - μ[pvPath W r η σ s0 t | 𝓕 q] ω
      - σ / (r + η) * incr W q t ω) ^ 2 ∂μ ≤ σ ^ 2 * η ^ 2 * (t - q) ^ 3 / (r + η) ^ 2 := by
  have hrη : 0 < r + η := by linarith
  have hb := pv_innovation_sq_le hBM hWm h𝓕 r hη hrη.ne' σ s0 hq hqt
  have e : (fun ω => (μ[pvPath W r η σ s0 t | 𝓕 t] ω - μ[pvPath W r η σ s0 t | 𝓕 q] ω
      - σ / (r + η) * incr W q t ω) ^ 2) =ᵐ[μ] fun ω => (ou μ 𝓕 W η σ s0 t ω / (r + η)
        - μ[fun ω => ou μ 𝓕 W η σ s0 t ω / (r + η) | 𝓕 q] ω - σ / (r + η) * incr W q t ω) ^ 2 := by
    filter_upwards [pv_revision hBM hWm h𝓕 hcont hr hrη σ s0 hq hqt,
      pv_innovation hBM hWm h𝓕 r η σ s0 hq hqt] with ω h1 h2
    rw [h1, ← h2]
  rw [integral_congr_ae e]
  exact hb

/-- **Cochrane (2023), §3.6.3, p. 77 (`σ = 0`): the deterministic AR(1).** With no shocks the
surplus path is `e^{−ηu}s₀` for every `ω` and `PV_t = e^{−ηt}s₀/(r + η)`
(`ContinuousLinear.ar1_pv`): there is nothing to forecast and no innovation.
Its first part restates `TidyR7ItoInnovation.ou_sigma_zero` for `ouPath`. -/
theorem pv_sigma_zero {r η : ℝ} (hrη : 0 < r + η) (s0 t : ℝ) (ω : Ω) :
    (∀ u, ouPath W η 0 s0 u ω = Real.exp (-(η * u)) * s0) ∧
      pvPath W r η 0 s0 t ω = Real.exp (-(η * t)) * s0 / (r + η) := by
  have h : ∀ u, ouPath W η 0 s0 u ω = Real.exp (-(η * u)) * s0 := fun u => by
    simp [ouPath]
  refine ⟨h, ?_⟩
  have e : ∀ τ, Real.exp (-(r * τ)) * ouPath W η 0 s0 (t + τ) ω =
      Real.exp (-(r * τ)) * (Real.exp (-(η * τ)) * (Real.exp (-(η * t)) * s0)) := fun τ => by
    rw [h, show -(η * (t + τ)) = -(η * τ) + -(η * t) by ring, Real.exp_add]
    ring
  simp only [pvPath, e]
  exact ContinuousLinear.ar1_pv hrη

/-! ## Non-vacuity on the constructed Brownian motion -/

/-- **Cochrane (2023), §3.6.3, p. 77 (non-vacuity): the present-value revision is not zero.** On
the constructed motion `bmPath` (continuous paths, `continuous_bmPath`), for `σ ≠ 0`, `r > 0`,
`r + η > 0`, `0 ≤ q < t`: `E[(E_t PV_t − E_q PV_t)²] > 0`.
A rescaling of `TidyR7ItoInnovation.ou_bmPath_innovation_pos`. -/
theorem bmPath_pv_revision_pos {r η : ℝ} (hr : 0 < r) (hrη : 0 < r + η) (s0 : ℝ) {σ : ℝ}
    (hσ : σ ≠ 0) {q t : ℝ} (hq : 0 ≤ q) (hqt : q < t) :
    0 < ∫ ω, (gaussSeq[pvPath bmPath r η σ s0 t | bmF t] ω
      - gaussSeq[pvPath bmPath r η σ s0 t | bmF q] ω) ^ 2 ∂gaussSeq := by
  have hB := isPreBrownianReal_bmPath
  have hF := bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath
  have hpos := ou_bmPath_innovation_pos η s0 hσ hq hqt
  have e : (fun ω => (gaussSeq[pvPath bmPath r η σ s0 t | bmF t] ω
      - gaussSeq[pvPath bmPath r η σ s0 t | bmF q] ω) ^ 2) =ᵐ[gaussSeq]
      fun ω => (1 / (r + η)) ^ 2 * (ou gaussSeq bmF bmPath η σ s0 t ω
        - gaussSeq[ou gaussSeq bmF bmPath η σ s0 t | bmF q] ω) ^ 2 := by
    filter_upwards [pv_revision hB measurable_bmPath hF continuous_bmPath hr hrη σ s0 hq hqt.le,
      ou_innovation hB measurable_bmPath hF η σ s0 hq hqt.le] with ω h1 h2
    rw [h1, h2]
    field_simp
  rw [integral_congr_ae e, integral_const_mul]
  have : 0 < (1 / (r + η)) ^ 2 := by positivity
  positivity

end Cochrane.Generality.TidyR8OUPresentValue
