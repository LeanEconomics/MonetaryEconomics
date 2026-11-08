/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.TidyR7OUPath
import FiscalConstraints.TidyR7WienerGaussian
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# The continuous-time AR(1) (Ornstein–Uhlenbeck) surplus and the debt limit

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.1, p. 197: "Suppose we
generate the surplus by an AR(1), `ds_t = −η(s_t − s̄) + σ_s dz_s`. An AR(1) ranges over the
entire real line, as does the integral of an AR(1) (6.5). So at some point the future
debt-to-GDP ratio following (6.5) will eventually exceed any bound."

Driving process: any pre-Brownian motion `W` (Mathlib's `ProbabilityTheory.IsPreBrownianReal`)
with measurable
values, continuous paths and `W_0 = 0` — e.g. `TidyR7BrownianExist.bmPath` on gaussSeq.

## Main results

* `ouProc` (the OU surplus driven by `W`), `ouProc_integral_eq` (it solves
  `s_t = s_0 − η∫_0^t (s_u − s̄)du + σW_t` on every path), `ouProc_unique`.
* `ouProc_ae_eq_itoInt`: `s_t = s̄ + e^{−ηt}(s_0 − s̄) + σe^{−ηt}∫_0^t e^{ηu} dW_u` a.s., with
  the Itô (Wiener) integral `TidyR7ItoIntegral.itoInt`.
* **`ouProc_hasLaw`**: `s_t ~ N(s̄ + e^{−ηt}(s_0 − s̄), σ²(1 − e^{−2ηt})/(2η))`; `integral_ouProc`,
  `variance_ouProc`.
* Stationary limit: `tendsto_ouMean`, `tendsto_ouVar`, **`tendsto_integral_ouProc`** (the law of
  `s_t` converges weakly to `N(s̄, σ²/(2η))`).
* "An AR(1) ranges over the entire real line": **`ouProc_mem_open_pos`** (every non-empty open
  set has positive probability at every date `t > 0`), `ouProc_gt_pos`, `ouProc_lt_pos`.
* "As does the integral of an AR(1) (6.5)": with corrected (6.5) debt
  `b_t = e^{at}b_0 − ∫_0^t e^{a(t−u)}s_u du`, **`ouDebtProc_hasLaw`** (Gaussian with variance
  `σ²∫_0^t G_t²`, non-degenerate, `debtVar_ne_zero`), **`ouDebtProc_mem_open_pos`**,
  `ouDebtProc_gt_pos`, and **`ouDebtProc_not_sustainable`**: for every limit `M` the event that
  debt never exceeds `M` has probability `< 1`. These hold for every `a = r − g` and every
  initial debt.
* Non-vacuity on bmPath: `bmPath_ouProc_hasLaw`, `bmPath_ouDebt_not_sustainable`.

The almost-sure statement "debt eventually exceeds any bound" is proved for the sampled process
in TidyR7OUSampled.
-/

namespace Cochrane.FiscalConstraints.TidyR7OrnsteinUhlenbeck

open Real MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.FiscalConstraints.TidyR7OUPath Cochrane.FiscalConstraints.TidyR7WienerGaussian
open Cochrane.FiscalConstraints.TidyR7BrownianTools Cochrane.FiscalConstraints.TidyR7BrownianQV
open Cochrane.FiscalConstraints.TidyR7ItoIntegral
open scoped ENNReal NNReal BoundedContinuousFunction

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

/-- Cochrane (2023), p. 197 (**the OU surplus process**): `s_t(ω)`, the solution of
`ds = −η(s − s̄)dt + σ dW` from `s_0`, driven by the path `t ↦ W_t(ω)`. -/
noncomputable def ouProc (η sbar s0 σ : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ouPath η sbar s0 σ (fun u => bmReal W u ω) t

/-- Cochrane (2023), p. 197: the variance `σ²(1 − e^{−2ηt})/(2η)` of the OU surplus at date `t`. -/
noncomputable def ouVar (η σ t : ℝ) : ℝ≥0 := (σ ^ 2 * (1 - exp (-2 * η * t)) / (2 * η)).toNNReal

/-- **Cochrane (2023), p. 197: the OU process solves its SDE** on every path:
`s_t = s_0 − η∫_0^t (s_u − s̄)du + σW_t`.
Restates `TidyR7OUPath.ouPath_integral_eq` path by path. -/
theorem ouProc_integral_eq (hcont : ∀ ω, Continuous fun t => W t ω) (η sbar s0 σ : ℝ) (ω : Ω)
    (t : ℝ) :
    ouProc η sbar s0 σ W t ω
      = s0 - η * (∫ u in (0 : ℝ)..t, (ouProc η sbar s0 σ W u ω - sbar)) + σ * bmReal W t ω :=
  ouPath_integral_eq (continuous_bmReal (hcont ω)) t

/-- Cochrane (2023), p. 197: the OU process starts at `s_0` when `W_0 = 0`. -/
theorem ouProc_zero (hW0 : ∀ ω, W 0 ω = 0) (η sbar s0 σ : ℝ) (ω : Ω) :
    ouProc η sbar s0 σ W 0 ω = s0 := by
  simp [ouProc, ouPath_zero, bmReal, hW0]

/-- **Cochrane (2023), p. 197: pathwise uniqueness.** A process with continuous paths solving
`X_t = s_0 − η∫_0^t (X_u − s̄)du + σW_t` on every path is the OU process.
Restates `TidyR7OUPath.ouPath_unique` path by path. -/
theorem ouProc_unique (hcont : ∀ ω, Continuous fun t => W t ω) {η sbar s0 σ : ℝ}
    {X : ℝ → Ω → ℝ} (hX : ∀ ω, Continuous fun t => X t ω)
    (h : ∀ ω t, X t ω = s0 - η * (∫ u in (0 : ℝ)..t, (X u ω - sbar)) + σ * bmReal W t ω) :
    X = ouProc η sbar s0 σ W := by
  funext t ω
  have := ouPath_unique (sbar := sbar) (continuous_bmReal (hcont ω)) (hX ω) (h ω)
  exact congrFun this t

/-- Cochrane (2023), p. 197: `u ↦ e^{ηu}` has derivative `e^{ηx}η`.
From Mathlib `HasDerivAt.exp`. -/
theorem hasDerivAt_expMul (η x : ℝ) : HasDerivAt (fun u => exp (η * u)) (exp (η * x) * η) x := by
  simpa using ((hasDerivAt_id' x).const_mul η).exp

/-- Cochrane (2023), p. 197: the OU noise on a Brownian path is `e^{−ηt}` times the by-parts
Wiener integral `∫_0^t e^{ηu} dW_u` (when `W_0 = 0`). -/
theorem ouNoise_eq_wienerBP (hW0 : ∀ ω, W 0 ω = 0) (η : ℝ) (ω : Ω) (t : ℝ) :
    ouNoise η (fun u => bmReal W u ω) t
      = exp (-η * t) * wienerBP W (fun u => exp (η * u)) (fun u => exp (η * u) * η) 0 t ω := by
  have hb0 : bmReal W 0 ω = 0 := by simp [bmReal, hW0]
  have hint : (∫ u in (0 : ℝ)..t, bmReal W u ω * (exp (η * u) * η))
      = η * ∫ u in (0 : ℝ)..t, exp (η * u) * bmReal W u ω := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext u
    ring
  have he : exp (-η * t) * exp (η * t) = 1 := by rw [← exp_add]; ring_nf; exact exp_zero
  simp only [ouNoise, ouPrim, wienerBP, hint, hb0, mul_zero, sub_zero]
  linear_combination (-(bmReal W t ω)) * he

/-- Cochrane (2023), p. 197: the OU process is its mean path plus `σe^{−ηt}` times the Wiener
integral, path by path. -/
theorem ouProc_eq (hW0 : ∀ ω, W 0 ω = 0) (η sbar s0 σ t : ℝ) :
    ouProc η sbar s0 σ W t = fun ω => ouMean η sbar s0 t
      + σ * exp (-η * t) * wienerBP W (fun u => exp (η * u)) (fun u => exp (η * u) * η) 0 t ω := by
  funext ω
  simp only [ouProc, ouPath, ouNoise_eq_wienerBP hW0]
  ring

/-- **Cochrane (2023), p. 197: the explicit Wiener-integral solution.** For `t > 0`, almost
surely `s_t = s̄ + e^{−ηt}(s_0 − s̄) + σe^{−ηt}∫_0^t e^{ηu} dW_u` with the Itô integral, for any
admissible filtration. -/
theorem ouProc_ae_eq_itoInt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    {𝓕 : Filtration ℝ mΩ} (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (η sbar s0 σ : ℝ) {t : ℝ} (ht : 0 < t) :
    ouProc η sbar s0 σ W t =ᵐ[P] fun ω => sbar + exp (-η * t) * (s0 - sbar)
      + σ * exp (-η * t) * itoInt P 𝓕 W (fun u _ => exp (η * u)) 0 t ω := by
  have hae := itoInt_ae_eq_wienerBP hB hW h𝓕 hcont (hasDerivAt_expMul η)
    (by fun_prop : Continuous fun u => exp (η * u) * η) le_rfl ht
  filter_upwards [hae] with ω hω
  rw [ouProc_eq hW0, hω]
  rfl

/-! ### The law of the OU surplus -/

/-- Cochrane (2023), p. 197 (tool): an affine image `m + cY` of `Y ~ N(0, v)` is
`N(m, c²v)`.
From Mathlib `gaussianReal_map_const_mul` and `gaussianReal_map_add_const`. -/
theorem map_affine_gaussian {Y : Ω → ℝ} (hY : AEMeasurable Y P) {v : ℝ≥0}
    (hv : P.map Y = gaussianReal 0 v) (m c : ℝ) :
    P.map (fun ω => m + c * Y ω) = gaussianReal m (.mk (c ^ 2) (sq_nonneg _) * v) := by
  have e1 : P.map (fun ω => m + c * Y ω) = (P.map Y).map (fun x => m + c * x) := by
    rw [AEMeasurable.map_map_of_aemeasurable
      (by fun_prop : AEMeasurable (fun x : ℝ => m + c * x) (P.map Y)) hY]
    rfl
  have e2 : (fun x : ℝ => m + c * x) = (fun x => x + m) ∘ (fun x => c * x) := by
    funext x
    simp only [Function.comp_apply]
    ring
  rw [e1, hv, e2, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_add_const]
  simp

/-- Cochrane (2023), p. 197: `∫_a^b (e^{ηu})² du = (e^{2ηb} − e^{2ηa})/(2η)` for `η ≠ 0`. -/
theorem integral_exp_sq {η : ℝ} (hη : η ≠ 0) (a b : ℝ) :
    ∫ u in a..b, exp (η * u) ^ 2 = (exp (2 * η * b) - exp (2 * η * a)) / (2 * η) := by
  have hd : ∀ x, HasDerivAt (fun u => exp (2 * η * u) / (2 * η)) (exp (η * x) ^ 2) x := by
    intro x
    have h := ((hasDerivAt_id' x).const_mul (2 * η)).exp.div_const (2 * η)
    refine h.congr_deriv ?_
    rw [sq, ← exp_add]
    field_simp
    ring_nf
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((by fun_prop : Continuous fun u => exp (η * u) ^ 2).intervalIntegrable a b)]
  ring

/-- Cochrane (2023), p. 197: the OU process is almost everywhere measurable. -/
theorem aemeasurable_ouProc (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) (η sbar s0 σ : ℝ) {t : ℝ}
    (ht : 0 < t) : AEMeasurable (ouProc η sbar s0 σ W t) P := by
  rw [ouProc_eq hW0]
  have := (memLp_wienerBP (P := P) hB hW hcont (hasDerivAt_expMul η)
    (by fun_prop : Continuous fun u => exp (η * u) * η) le_rfl ht).aestronglyMeasurable
    |>.aemeasurable
  fun_prop

/-- **Cochrane (2023), p. 197: the law of the OU surplus.** For `η > 0` and `t > 0`,
`s_t ~ N(s̄ + e^{−ηt}(s_0 − s̄), σ²(1 − e^{−2ηt})/(2η))`. -/
theorem ouProc_hasLaw (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {η : ℝ} (hη : 0 < η)
    (sbar s0 σ : ℝ) {t : ℝ} (ht : 0 < t) :
    P.map (ouProc η sbar s0 σ W t) = gaussianReal (ouMean η sbar s0 t) (ouVar η σ t) := by
  have hY := (memLp_wienerBP (P := P) hB hW hcont (hasDerivAt_expMul η)
    (by fun_prop : Continuous fun u => exp (η * u) * η) le_rfl ht).aestronglyMeasurable
    |>.aemeasurable
  have hlaw := map_wienerBP (P := P) hB hW hcont (hasDerivAt_expMul η)
    (by fun_prop : Continuous fun u => exp (η * u) * η) le_rfl ht
  rw [ouProc_eq hW0]
  have h := map_affine_gaussian hY hlaw (ouMean η sbar s0 t) (σ * exp (-η * t))
  simp only [mul_assoc] at h ⊢
  rw [h]
  congr 1
  have hI := integral_exp_sq hη.ne' 0 t
  have hpos : 0 ≤ ∫ u in (0 : ℝ)..t, exp (η * u) ^ 2 := by
    rw [hI, mul_zero, exp_zero]
    have : 1 ≤ exp (2 * η * t) := one_le_exp (by positivity)
    exact div_nonneg (by linarith) (by positivity)
  have hv : 0 ≤ σ ^ 2 * (1 - exp (-2 * η * t)) / (2 * η) := by
    have : exp (-2 * η * t) ≤ 1 := exp_le_one_iff.2 (by nlinarith)
    exact div_nonneg (mul_nonneg (sq_nonneg σ) (by linarith)) (by positivity)
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hpos, ouVar, Real.coe_toNNReal _ hv, hI,
    mul_zero, exp_zero]
  have e1 : exp (-η * t) ^ 2 = exp (-2 * η * t) := by rw [sq, ← exp_add]; ring_nf
  have e2 : exp (-2 * η * t) * exp (2 * η * t) = 1 := by rw [← exp_add]; ring_nf; exact exp_zero
  rw [mul_pow, e1]
  have e3 : σ ^ 2 * exp (-2 * η * t) * ((exp (2 * η * t) - 1) / (2 * η))
      = σ ^ 2 * (exp (-2 * η * t) * exp (2 * η * t) - exp (-2 * η * t)) / (2 * η) := by ring
  rw [e3, e2]

/-- Cochrane (2023), p. 197: the mean of the OU surplus is `s̄ + e^{−ηt}(s_0 − s̄)`. -/
theorem integral_ouProc (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {η : ℝ} (hη : 0 < η)
    (sbar s0 σ : ℝ) {t : ℝ} (ht : 0 < t) :
    ∫ ω, ouProc η sbar s0 σ W t ω ∂P = ouMean η sbar s0 t := by
  have hm := aemeasurable_ouProc (P := P) hB hW hcont hW0 η sbar s0 σ ht
  calc ∫ ω, ouProc η sbar s0 σ W t ω ∂P = ∫ x, x ∂(P.map (ouProc η sbar s0 σ W t)) :=
        (integral_map hm aestronglyMeasurable_id).symm
    _ = ouMean η sbar s0 t := by
        rw [ouProc_hasLaw hB hW hcont hW0 hη sbar s0 σ ht, integral_id_gaussianReal]

/-- Cochrane (2023), p. 197: the variance of the OU surplus is `σ²(1 − e^{−2ηt})/(2η)`. -/
theorem variance_ouProc (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {η : ℝ} (hη : 0 < η)
    (sbar s0 σ : ℝ) {t : ℝ} (ht : 0 < t) :
    Var[ouProc η sbar s0 σ W t; P] = ouVar η σ t := by
  have hm := aemeasurable_ouProc (P := P) hB hW hcont hW0 η sbar s0 σ ht
  rw [← variance_id_map hm, ouProc_hasLaw hB hW hcont hW0 hη sbar s0 σ ht,
    variance_id_gaussianReal]

/-! ### The stationary limit -/

/-- Cochrane (2023), p. 197: the mean path converges to `s̄` (`η > 0`). -/
theorem tendsto_ouMean {η : ℝ} (hη : 0 < η) (sbar s0 : ℝ) :
    Tendsto (ouMean η sbar s0) atTop (𝓝 sbar) := by
  have h : Tendsto (fun t => exp (-η * t)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  have := (h.mul_const (s0 - sbar)).const_add sbar
  rw [zero_mul, add_zero] at this
  exact this

/-- Cochrane (2023), p. 197: the variance converges to the stationary variance `σ²/(2η)`. -/
theorem tendsto_ouVar {η : ℝ} (hη : 0 < η) (σ : ℝ) :
    Tendsto (fun t => (ouVar η σ t : ℝ)) atTop (𝓝 (σ ^ 2 / (2 * η))) := by
  have h : Tendsto (fun t => exp (-2 * η * t)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  have h2 : Tendsto (fun t => σ ^ 2 * (1 - exp (-2 * η * t)) / (2 * η)) atTop
      (𝓝 (σ ^ 2 / (2 * η))) := by
    have := ((h.const_sub 1).const_mul (σ ^ 2)).div_const (2 * η)
    simpa using this
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  have : exp (-2 * η * t) ≤ 1 := exp_le_one_iff.2 (by nlinarith)
  rw [ouVar, Real.coe_toNNReal _ (div_nonneg (mul_nonneg (sq_nonneg σ) (by linarith))
    (by positivity))]

/-- Cochrane (2023), p. 197 (tool): `N(m, v)` is the image of `N(0, 1)` under `x ↦ m + √v x`.
From Mathlib `gaussianReal_map_const_mul` and `gaussianReal_map_add_const`. -/
theorem gaussianReal_eq_map (m : ℝ) (v : ℝ≥0) :
    gaussianReal m v = (gaussianReal 0 1).map (fun x => m + √(v : ℝ) * x) := by
  have e2 : (fun x : ℝ => m + √(v : ℝ) * x) = (fun x => x + m) ∘ (fun x => √(v : ℝ) * x) := by
    funext x
    simp only [Function.comp_apply]
    ring
  rw [e2, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_add_const]
  congr 1
  · ring
  · ext
    simp

/-- **Cochrane (2023), p. 197: the stationary limit.** For `η > 0` the law of `s_t` converges
weakly to the stationary law `N(s̄, σ²/(2η))`: `E f(s_t) → ∫ f dN(s̄, σ²/(2η))` for every bounded
continuous `f`. -/
theorem tendsto_integral_ouProc (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {η : ℝ} (hη : 0 < η)
    (sbar s0 σ : ℝ) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun t => ∫ x, f x ∂(P.map (ouProc η sbar s0 σ W t))) atTop
      (𝓝 (∫ x, f x ∂gaussianReal sbar (σ ^ 2 / (2 * η)).toNNReal)) := by
  have hrep : ∀ (m : ℝ) (v : ℝ≥0), ∫ x, f x ∂gaussianReal m v
      = ∫ x, f (m + √(v : ℝ) * x) ∂gaussianReal 0 1 := by
    intro m v
    rw [gaussianReal_eq_map m v, integral_map (by fun_prop) (by fun_prop)]
  have hlim : Tendsto (fun t => ∫ x, f (ouMean η sbar s0 t + √(ouVar η σ t : ℝ) * x)
      ∂gaussianReal 0 1) atTop
      (𝓝 (∫ x, f (sbar + √((σ ^ 2 / (2 * η)).toNNReal : ℝ) * x) ∂gaussianReal 0 1)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => ‖f‖)
      (Eventually.of_forall fun t => by fun_prop)
      (Eventually.of_forall fun t => ae_of_all _ fun x => f.norm_coe_le_norm _)
      (integrable_const _) (ae_of_all _ fun x => ?_)
    have hv : Tendsto (fun t => √(ouVar η σ t : ℝ)) atTop
        (𝓝 (√((σ ^ 2 / (2 * η)).toNNReal : ℝ))) := by
      rw [Real.coe_toNNReal _ (div_nonneg (sq_nonneg σ) (by positivity))]
      exact (continuous_sqrt.tendsto _).comp (tendsto_ouVar hη σ)
    exact (f.continuous.tendsto _).comp ((tendsto_ouMean hη sbar s0).add (hv.mul_const x))
  rw [hrep]
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [ouProc_hasLaw hB hW hcont hW0 hη sbar s0 σ ht, hrep]

/-! ### "An AR(1) ranges over the entire real line" -/

/-- Cochrane (2023), p. 197: the OU variance is positive at `t > 0` when `σ ≠ 0`, `η > 0`. -/
theorem ouVar_ne_zero {η σ t : ℝ} (hη : 0 < η) (hσ : σ ≠ 0) (ht : 0 < t) : ouVar η σ t ≠ 0 := by
  have h1 : exp (-2 * η * t) < 1 := exp_lt_one_iff.2 (by nlinarith)
  have : 0 < σ ^ 2 * (1 - exp (-2 * η * t)) / (2 * η) :=
    div_pos (mul_pos (pow_pos (abs_pos.2 hσ) 2 |>.trans_eq (sq_abs σ)) (by linarith))
      (by positivity)
  exact (Real.toNNReal_pos.2 this).ne'

/-- Cochrane (2023), p. 197 (tool): a non-degenerate Gaussian charges every non-empty open set.
From Mathlib `gaussianReal_absolutelyContinuous'`. -/
theorem gaussianReal_open_pos (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {U : Set ℝ} (hU : IsOpen U)
    (hne : U.Nonempty) : 0 < gaussianReal m v U := by
  rw [pos_iff_ne_zero]
  intro h0
  exact (hU.measure_pos volume hne).ne' (gaussianReal_absolutelyContinuous' m hv h0)

/-- **Cochrane (2023), p. 197: "an AR(1) ranges over the entire real line".** For `η > 0`,
`σ ≠ 0` and every date `t > 0`, the OU surplus lies in any non-empty open set with positive
probability. -/
theorem ouProc_mem_open_pos (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {η σ : ℝ} (hη : 0 < η)
    (hσ : σ ≠ 0) (sbar s0 : ℝ) {t : ℝ} (ht : 0 < t) {U : Set ℝ} (hU : IsOpen U)
    (hne : U.Nonempty) : 0 < P {ω | ouProc η sbar s0 σ W t ω ∈ U} := by
  have hm := aemeasurable_ouProc (P := P) hB hW hcont hW0 η sbar s0 σ ht
  have h := Measure.map_apply_of_aemeasurable hm hU.measurableSet
  rw [ouProc_hasLaw hB hW hcont hW0 hη sbar s0 σ ht] at h
  rw [show {ω | ouProc η sbar s0 σ W t ω ∈ U} = ouProc η sbar s0 σ W t ⁻¹' U from rfl, ← h]
  exact gaussianReal_open_pos _ (ouVar_ne_zero hη hσ ht) hU hne

/-- Cochrane (2023), p. 197: surpluses above any level occur with positive probability. -/
theorem ouProc_gt_pos (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {η σ : ℝ} (hη : 0 < η)
    (hσ : σ ≠ 0) (sbar s0 : ℝ) {t : ℝ} (ht : 0 < t) (M : ℝ) :
    0 < P {ω | M < ouProc η sbar s0 σ W t ω} :=
  ouProc_mem_open_pos hB hW hcont hW0 hη hσ sbar s0 ht isOpen_Ioi Set.nonempty_Ioi

/-- Cochrane (2023), p. 197: deficits of any size occur with positive probability. -/
theorem ouProc_lt_pos (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {η σ : ℝ} (hη : 0 < η)
    (hσ : σ ≠ 0) (sbar s0 : ℝ) {t : ℝ} (ht : 0 < t) (M : ℝ) :
    0 < P {ω | ouProc η sbar s0 σ W t ω < M} :=
  ouProc_mem_open_pos hB hW hcont hW0 hη hσ sbar s0 ht isOpen_Iio Set.nonempty_Iio

/-! ### "As does the integral of an AR(1) (6.5)": debt -/

/-- Cochrane (2023), (6.5), p. 197: the debt-to-GDP ratio `b_t(ω)` with the OU surplus,
`b_t = e^{at}b_0 − ∫_0^t e^{a(t−u)}s_u du`, `a = r − g`. -/
noncomputable def ouDebtProc (a η sbar s0 σ b0 : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ouDebt a η sbar s0 σ b0 (fun u => bmReal W u ω) t

/-- Cochrane (2023), (6.5), p. 197: the variance `σ²∫_0^t G_t(r)² dr` of debt at date `t`. -/
noncomputable def debtVar (a η σ t : ℝ) : ℝ≥0 :=
  (σ ^ 2 * ∫ r in (0 : ℝ)..t, debtG a η t r ^ 2).toNNReal

/-- Cochrane (2023), (6.4), p. 196: on every path, debt solves `ḃ = ab − s` with the OU
surplus.
Restates `TidyR7OUPath.ouDebt_hasDerivAt` path by path. -/
theorem ouDebtProc_hasDerivAt (hcont : ∀ ω, Continuous fun t => W t ω) (a η sbar s0 σ b0 : ℝ)
    (ω : Ω) (t : ℝ) :
    HasDerivAt (fun t => ouDebtProc a η sbar s0 σ b0 W t ω)
      (a * ouDebtProc a η sbar s0 σ b0 W t ω - ouProc η sbar s0 σ W t ω) t :=
  ouDebt_hasDerivAt a b0 (continuous_bmReal (hcont ω)) t

/-- Cochrane (2023), (6.5), p. 197: debt is its deterministic part minus `σ` times the Wiener
integral `∫_0^t G_t dW` (by parts), path by path. -/
theorem ouDebtProc_eq (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0)
    (a η sbar s0 σ b0 t : ℝ) :
    ouDebtProc a η sbar s0 σ b0 W t = fun ω => debtMean a η sbar s0 b0 t
      + (-σ) * wienerBP W (debtG a η t) (fun r => -debtKernel a η t r) 0 t ω := by
  funext ω
  have hb0 : bmReal W 0 ω = 0 := by simp [bmReal, hW0]
  have hint : (∫ u in (0 : ℝ)..t, bmReal W u ω * -debtKernel a η t u)
      = -∫ u in (0 : ℝ)..t, bmReal W u ω * debtKernel a η t u := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext u
    ring
  simp only [ouDebtProc, ouDebt_eq a b0 (continuous_bmReal (hcont ω)),
    debtNoise_eq_integral a η (continuous_bmReal (hcont ω)), wienerBP, debtG_self, hb0, hint]
  ring

/-- Cochrane (2023), (6.5), p. 197: the debt process is almost everywhere measurable. -/
theorem aemeasurable_ouDebtProc (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) (a η sbar s0 σ b0 : ℝ)
    {t : ℝ} (ht : 0 < t) : AEMeasurable (ouDebtProc a η sbar s0 σ b0 W t) P := by
  rw [ouDebtProc_eq hcont hW0]
  have := (memLp_wienerBP (P := P) hB hW hcont (hasDerivAt_debtG a η t)
    (continuous_debtKernel a η t).neg le_rfl ht).aestronglyMeasurable.aemeasurable
  fun_prop

/-- **Cochrane (2023), (6.5), p. 197: the law of debt with an OU surplus.** For `t > 0`,
`b_t ~ N(debtMean, σ²∫_0^t G_t²)`, for every `a = r − g`, `η`, `s̄`, `s_0`, `b_0`. -/
theorem ouDebtProc_hasLaw (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) (a η sbar s0 σ b0 : ℝ)
    {t : ℝ} (ht : 0 < t) :
    P.map (ouDebtProc a η sbar s0 σ b0 W t)
      = gaussianReal (debtMean a η sbar s0 b0 t) (debtVar a η σ t) := by
  have hY := (memLp_wienerBP (P := P) hB hW hcont (hasDerivAt_debtG a η t)
    (continuous_debtKernel a η t).neg le_rfl ht).aestronglyMeasurable.aemeasurable
  have hlaw := map_wienerBP (P := P) hB hW hcont (hasDerivAt_debtG a η t)
    (continuous_debtKernel a η t).neg le_rfl ht
  rw [ouDebtProc_eq hcont hW0, map_affine_gaussian hY hlaw]
  congr 1
  have hpos : 0 ≤ ∫ r in (0 : ℝ)..t, debtG a η t r ^ 2 :=
    intervalIntegral.integral_nonneg ht.le fun r _ => sq_nonneg _
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hpos, debtVar,
    Real.coe_toNNReal _ (mul_nonneg (sq_nonneg σ) hpos), neg_sq]

/-- Cochrane (2023), (6.5), p. 197: the debt variance is positive when `σ ≠ 0`, `t > 0`. -/
theorem debtVar_ne_zero (a η : ℝ) {σ t : ℝ} (hσ : σ ≠ 0) (ht : 0 < t) : debtVar a η σ t ≠ 0 := by
  have : 0 < σ ^ 2 * ∫ r in (0 : ℝ)..t, debtG a η t r ^ 2 :=
    mul_pos (pow_pos (abs_pos.2 hσ) 2 |>.trans_eq (sq_abs σ)) (integral_debtG_sq_pos a η ht)
  exact (Real.toNNReal_pos.2 this).ne'

/-- **Cochrane (2023), p. 197: "as does the integral of an AR(1) (6.5)".** With an OU surplus
(`σ ≠ 0`), at every date `t > 0` the debt-to-GDP ratio lies in any non-empty open set with
positive probability, for every `a = r − g` and every initial debt. -/
theorem ouDebtProc_mem_open_pos (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) (a η sbar s0 b0 : ℝ)
    {σ : ℝ} (hσ : σ ≠ 0) {t : ℝ} (ht : 0 < t) {U : Set ℝ} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < P {ω | ouDebtProc a η sbar s0 σ b0 W t ω ∈ U} := by
  have hm := aemeasurable_ouDebtProc (P := P) hB hW hcont hW0 a η sbar s0 σ b0 ht
  have h := Measure.map_apply_of_aemeasurable hm hU.measurableSet
  rw [ouDebtProc_hasLaw hB hW hcont hW0 a η sbar s0 σ b0 ht] at h
  rw [show {ω | ouDebtProc a η sbar s0 σ b0 W t ω ∈ U} = ouDebtProc a η sbar s0 σ b0 W t ⁻¹' U
    from rfl, ← h]
  exact gaussianReal_open_pos _ (debtVar_ne_zero a η hσ ht) hU hne

/-- Cochrane (2023), p. 197: at every date `t > 0` debt exceeds any bound `M` with positive
probability. -/
theorem ouDebtProc_gt_pos (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) (a η sbar s0 b0 : ℝ)
    {σ : ℝ} (hσ : σ ≠ 0) {t : ℝ} (ht : 0 < t) (M : ℝ) :
    0 < P {ω | M < ouDebtProc a η sbar s0 σ b0 W t ω} :=
  ouDebtProc_mem_open_pos hB hW hcont hW0 a η sbar s0 b0 hσ ht isOpen_Ioi Set.nonempty_Ioi

/-- **Cochrane (2023), p. 197: "the initial value of debt `b_0/y_0` in (6.5) is not
sustainable".** With an OU surplus (`σ ≠ 0`), for every debt limit `M`, the event that debt
never exceeds `M` has probability strictly less than one — for every `a = r − g`, every
initial debt and every OU parameter. -/
theorem ouDebtProc_not_sustainable (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) (a η sbar s0 b0 : ℝ)
    {σ : ℝ} (hσ : σ ≠ 0) (M : ℝ) :
    P {ω | ∀ t, 0 < t → ouDebtProc a η sbar s0 σ b0 W t ω ≤ M} < 1 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm := aemeasurable_ouDebtProc (P := P) hB hW hcont hW0 a η sbar s0 σ b0 one_pos
  set μ := gaussianReal (debtMean a η sbar s0 b0 1) (debtVar a η σ 1)
  have hle : P {ω | ∀ t, 0 < t → ouDebtProc a η sbar s0 σ b0 W t ω ≤ M}
      ≤ μ (Set.Iic M) := by
    have h := Measure.map_apply_of_aemeasurable hm (measurableSet_Iic (a := M))
    rw [ouDebtProc_hasLaw hB hW hcont hW0 a η sbar s0 σ b0 one_pos] at h
    rw [h]
    exact measure_mono fun ω hω => hω 1 one_pos
  have hpos : 0 < μ (Set.Ioi M) :=
    gaussianReal_open_pos _ (debtVar_ne_zero a η hσ one_pos) isOpen_Ioi Set.nonempty_Ioi
  have hc : μ (Set.Iic M) = 1 - μ (Set.Ioi M) := by
    rw [← prob_compl_eq_one_sub (μ := μ) (measurableSet_Ioi (a := M)), Set.compl_Ioi]
  refine hle.trans_lt ?_
  rw [hc]
  exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hpos.ne'

/-! ### Non-vacuity on the constructed Brownian motion -/

open Cochrane.FiscalConstraints.TidyR7BrownianExist
open Cochrane.FiscalConstraints.TidyR7BrownianSchauder

/-- Cochrane (2023), p. 197 (non-vacuity): on the constructed Brownian motion bmPath on
gaussSeq, the OU surplus has the Gaussian law of `ouProc_hasLaw`. -/
theorem bmPath_ouProc_hasLaw {η : ℝ} (hη : 0 < η) (sbar s0 σ : ℝ) {t : ℝ} (ht : 0 < t) :
    gaussSeq.map (ouProc η sbar s0 σ bmPath t)
      = gaussianReal (ouMean η sbar s0 t) (ouVar η σ t) :=
  ouProc_hasLaw isPreBrownianReal_bmPath measurable_bmPath continuous_bmPath bmPath_zero hη
    sbar s0 σ ht

/-- Cochrane (2023), p. 197 (non-vacuity): on bmPath, with `η = σ = 1`, the surplus ranges over
the whole line: positive probability of exceeding any `M` at date `1`. -/
theorem bmPath_ouProc_gt_pos (sbar s0 M : ℝ) :
    0 < gaussSeq {ω | M < ouProc 1 sbar s0 1 bmPath 1 ω} :=
  ouProc_gt_pos isPreBrownianReal_bmPath measurable_bmPath continuous_bmPath bmPath_zero one_pos
    one_ne_zero sbar s0 one_pos M

/-- Cochrane (2023), p. 197 (non-vacuity): on bmPath, with `r − g = −1%`, `η = σ = 1`, no
debt limit is respected with probability one. -/
theorem bmPath_ouDebt_not_sustainable (sbar s0 b0 M : ℝ) :
    gaussSeq {ω | ∀ t, 0 < t → ouDebtProc (-1 / 100) 1 sbar s0 1 b0 bmPath t ω ≤ M} < 1 :=
  ouDebtProc_not_sustainable isPreBrownianReal_bmPath measurable_bmPath continuous_bmPath
    bmPath_zero _ _ sbar s0 b0 one_ne_zero M

end Cochrane.FiscalConstraints.TidyR7OrnsteinUhlenbeck
