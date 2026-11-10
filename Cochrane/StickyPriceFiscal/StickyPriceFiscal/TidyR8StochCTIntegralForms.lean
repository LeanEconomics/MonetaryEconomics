/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.TidyR8StochKernel

/-!
# The integral forms of p. 163, deterministic and with Brownian shocks

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.7, p. 163.

The book integrates (5.85) and (5.86) forward to
`x_t = −σE_t∫_0^∞(i_{t+τ} − π_{t+τ})dτ` and `π_t = κE_t∫_0^∞ e^{−ρτ}x_{t+τ}dτ`.
`CTSimple.ct_is_integral` proves the first only under `x_T → 0`, and `CTSimple.ct_pc_integral`
the second for `ρ > 0`.

**The printed IS form is false for a permanent interest-rate shock when `ρ ≠ 0`.** After a
permanent rate change output does not return to `0`: the long-run Phillips curve `ρπ = κx`
with `π_∞ = i_∞` gives `x_∞ = ρi_∞/κ` (`R_x(τ) → ρσ_i/κ`). The correct statement is
`x_t = x_∞ − σ∫_0^∞(i − π)`, i.e. `x_t = (ρ/κ)E_t i_∞ − σE_t∫_0^∞(i − π)`; the printed form
holds iff `x_∞ = 0` (a transitory shock, or `ρ = 0`). The Phillips-curve form holds for every
`ρ > 0` also under uncertainty; at `ρ = 0` it needs `+π_∞`.

## Main results

Deterministic (the book's continuous-time model of `CTSimple`):
* `is_integral_general` (`x_t = x_∞ − σ∫(i − π)` whenever `x_T → x_∞`),
  `is_printed_iff` (the printed form iff `x_∞ = 0`);
* `fisherian_equilibrium` (a permanent rate rise `i₀` with no fiscal news: `π = i₀`,
  `x = ρi₀/κ`, `v = 0`, an equilibrium of `CTSimple.IsCTEquilibrium`) and
  **`printed_is_counterexample`** (it violates the printed IS form whenever `ρi₀ ≠ 0`);
  `step_is_corrected` (every step equilibrium satisfies `x_t = ρi₀/κ − σ∫(i − π)`);
* `pc_rho_zero_corrected`, `printed_pc_counterexample_rho_zero` (at `ρ = 0`,
  `π_t = π_∞ + κ∫x`, and the printed form fails).

With Brownian shocks (`dε_m = σ_i dW`, `dε_s = σ_s dW`, T8's explicit solution):
* `condExp_isProc` (`E_t∫_t^T(i − π) = −(A/λ₂)(1 − e^{−λ₂(T−t)})Y_t`);
* **`is_corrected_L1`** (`E_t∫_t^T σ(i − π) + x_t − (ρ/κ)i_t → 0` in `L¹`) and
  `condExp_x_limit` (`E_t x_T → (ρ/κ)i_t`): `x_t = lim E_t x_T − σ lim E_t∫_t^T(i − π)`;
* **`printed_is_fails`**: for `ρσ_i ≠ 0`, `t > 0`, the `L¹` distance between `x(t)` and
  `−σE_t∫_t^T(i − π)` converges to `|ρ/κ|E|i_t| > 0`;
* `pc_identity` (on every path,
  `κ∫_t^T e^{−ρ(τ−t)}x = π_t − e^{−ρ(T−t)}π_T + R_π(0)∫e^{−ρ(τ−t)}dW`),
  **`pc_integral_L1`** (`ρ > 0`: `κE_t∫_t^T e^{−ρ(τ−t)}x → π_t` in `L¹`, the printed form),
  `pc_rho_zero_L1` (`ρ = 0`: `κE_t∫_t^T x + i_t → π_t`);
* non-vacuity on `bmPath`: `bmPath_printed_is_fails`.
-/

namespace Cochrane.StickyPriceFiscal.TidyR8StochCTIntegralForms

open Real MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.StickyPriceFiscal.TidyR7StieltjesSums Cochrane.StickyPriceFiscal.TidyR7BrownianTools
open Cochrane.StickyPriceFiscal.TidyR7BrownianQV Cochrane.StickyPriceFiscal.TidyR7ItoIntegral
open Cochrane.StickyPriceFiscal.TidyR7ItoBridge Cochrane.StickyPriceFiscal.TidyR7BrownianExist
open Cochrane.StickyPriceFiscal.TidyR7BrownianSchauder Cochrane.StickyPriceFiscal.TidyR7ItoSums
open Cochrane.StickyPriceFiscal.TidyR7StochCTPath Cochrane.StickyPriceFiscal.TidyR7StochCTBrownian
open Cochrane.StickyPriceFiscal.TidyR7StochCTUnique Cochrane.StickyPriceFiscal.TidyR8StochKernel
open Cochrane.StickyPriceFiscal.CTSimple
open scoped ENNReal NNReal

/-! ### Deterministic: the IS form -/

/-- **Cochrane (2023), §5.7, p. 163, corrected: the integrated IS curve with its limit term.**
Along a solution of (5.91)–(5.92), if `x_T → x_∞` and `i − infl` is integrable on `(t, ∞)`, then
`x_t = x_∞ − σ∫_0^∞(i_{t+τ} − π_{t+τ})dτ`.
Generalises `CTSimple.ct_is_integral` (the case `x_∞ = 0`). -/
theorem is_integral_general {σ κ ρ t xinf : ℝ} {i x infl : ℝ → ℝ} (h : IsCTSolution σ κ ρ i x infl)
    (ht : 0 ≤ t) (hx : Tendsto x atTop (𝓝 xinf))
    (hint : IntegrableOn (fun τ => i τ - infl τ) (Set.Ioi t)) :
    x t = xinf - σ * ∫ τ in Set.Ioi 0, (i (t + τ) - infl (t + τ)) := by
  have hl := tendsto_of_deriv_Ioi (G := x) (g := fun τ => σ * (i τ - infl τ))
    (h.1.mono (Set.Ici_subset_Ici.2 ht)) (fun τ hτ => (h.2.2 τ (by linarith)).1)
    (hint.const_mul σ)
  have hu := tendsto_nhds_unique hl hx
  rw [integral_const_mul] at hu
  rw [integral_Ioi_shift (fun τ => i τ - infl τ) t]
  linarith

/-- Cochrane (2023), §5.7, p. 163: **the printed IS form holds iff output returns to zero**:
under the hypotheses of `is_integral_general`, `x_t = −σ∫(i − infl)` iff `x_∞ = 0`. -/
theorem is_printed_iff {σ κ ρ t xinf : ℝ} {i x infl : ℝ → ℝ} (h : IsCTSolution σ κ ρ i x infl)
    (ht : 0 ≤ t) (hx : Tendsto x atTop (𝓝 xinf))
    (hint : IntegrableOn (fun τ => i τ - infl τ) (Set.Ioi t)) :
    x t = -σ * ∫ τ in Set.Ioi 0, (i (t + τ) - infl (t + τ)) ↔ xinf = 0 := by
  rw [is_integral_general h ht hx hint]
  constructor <;> intro h' <;> linarith

/-- **Cochrane (2023), p. 166 (the Fisherian response to a permanent rate rise with no fiscal
news)**: for `κ ≠ 0` and `r ∈ ℝ`, `infl = i₀`, `x = ρi₀/κ`, `v = 0` is an equilibrium of the
continuous-time model (`CTSimple.IsCTEquilibrium` with `v₀ = 0`, `s̃ = 0`). -/
theorem fisherian_equilibrium {r σ κ ρ : ℝ} (hκ : κ ≠ 0) (i0 : ℝ) :
    IsCTEquilibrium r σ κ ρ 0 (fun _ => i0) (fun _ => 0) (fun _ => ρ * i0 / κ) (fun _ => i0)
      (fun _ => 0) := by
  refine ⟨⟨⟨continuousOn_const, continuousOn_const, fun t _ => ⟨?_, ?_⟩⟩,
    ⟨|ρ * i0 / κ|, fun _ _ => le_rfl⟩, ⟨|i0|, fun _ _ => le_rfl⟩⟩,
    continuousOn_const, fun t _ => ?_, rfl, ?_⟩
  · exact (hasDerivAt_const t _).congr_deriv (by ring)
  · exact (hasDerivAt_const t _).congr_deriv (by field_simp; ring)
  · exact (hasDerivAt_const t _).congr_deriv (by ring)
  · simp

/-- **Cochrane (2023), §5.7, p. 163: the printed integrated IS curve is false.** In the
equilibrium `fisherian_equilibrium` (a permanent rate rise `i₀`, `ρi₀ ≠ 0`), `i − infl = 0`, so the
printed right-hand side `−σ∫_0^∞(i − infl)` is `0`, while `x_t = ρi₀/κ ≠ 0`. -/
theorem printed_is_counterexample {σ κ ρ i0 : ℝ} (hκ : κ ≠ 0) (hρi : ρ * i0 ≠ 0) (t : ℝ) :
    (fun _ : ℝ => ρ * i0 / κ) t ≠
      -σ * ∫ τ in Set.Ioi 0, ((fun _ : ℝ => i0) (t + τ) - (fun _ : ℝ => i0) (t + τ)) := by
  simp only [sub_self, integral_zero, mul_zero]
  exact div_ne_zero hρi hκ

/-- **Cochrane (2023), pp. 163 and 166: the corrected IS form in the step example.** For `κ, σ > 0`,
every equilibrium after a step to `i₀`, `s̃₀` satisfies, for `t ≥ 0`,
`x_t = ρi₀/κ − σ∫_0^∞(i_{t+τ} − π_{t+τ})dτ`: the limit term is `x_∞ = ρi₀/κ`. -/
theorem step_is_corrected {r σ κ ρ v0 i0 s0 : ℝ} {x infl v : ℝ → ℝ} (hκ : 0 < κ)
    (hσ : 0 < σ) (h : IsCTEquilibrium r σ κ ρ v0 (fun _ => i0) (fun _ => s0) x infl v) {t : ℝ}
    (ht : 0 ≤ t) :
    x t = ρ * i0 / κ - σ * ∫ τ in Set.Ioi 0, ((fun _ => i0) (t + τ) - infl (t + τ)) := by
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  have hfam := ct_step_family hκ hσ h.1
  have hπ := fun τ hτ => (hfam τ hτ).1
  have hxl : Tendsto x atTop (𝓝 (ρ * i0 / κ)) := by
    have he : Tendsto (fun τ => Real.exp (-(lam2 ρ κ σ * τ))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop h2)
    have := ((he.const_mul (lam1 ρ κ σ * (infl 0 - i0))).add_const (ρ * i0)).div_const κ
    simp only [mul_zero, zero_add] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with τ hτ
    rw [(hfam τ hτ).2]
  have hint : IntegrableOn (fun τ => (fun _ => i0) τ - infl τ) (Set.Ioi t) := by
    have h0 : IntegrableOn (fun τ => -(infl 0 - i0) * Real.exp (-(lam2 ρ κ σ * τ)))
        (Set.Ioi 0) := (integrableOn_exp_Ioi h2).const_mul _
    have hI : IntegrableOn (fun τ => -(infl 0 - i0) * Real.exp (-(lam2 ρ κ σ * τ))) (Set.Ioi t) :=
      h0.mono_set (Set.Ioi_subset_Ioi ht)
    refine hI.congr_fun (fun τ hτ => ?_) measurableSet_Ioi
    simp only
    rw [hπ τ (le_of_lt (lt_of_le_of_lt ht hτ))]
    ring
  exact is_integral_general h.1.1 ht hxl hint

/-! ### Deterministic: the Phillips-curve form at `ρ = 0` -/

/-- Cochrane (2023), §5.7, p. 163, at `ρ = 0`: along a solution with `ρ = 0`, if `π_T → π_∞`
and `x` is integrable on `(t, ∞)`, then `π_t = π_∞ + κ∫_0^∞ x_{t+τ}dτ`. -/
theorem pc_rho_zero_corrected {σ κ t πinf : ℝ} {i x infl : ℝ → ℝ} (h : IsCTSolution σ κ 0 i x infl)
    (ht : 0 ≤ t) (hπ : Tendsto infl atTop (𝓝 πinf)) (hint : IntegrableOn x (Set.Ioi t)) :
    infl t = πinf + κ * ∫ τ in Set.Ioi 0, x (t + τ) := by
  have hl := tendsto_of_deriv_Ioi (G := infl) (g := fun τ => -(κ * x τ))
    (h.2.1.mono (Set.Ici_subset_Ici.2 ht))
    (fun τ hτ => ((h.2.2 τ (by linarith)).2).congr_deriv (by ring)) (hint.const_mul κ).neg
  have hu := tendsto_nhds_unique hl hπ
  rw [integral_neg, integral_const_mul] at hu
  rw [integral_Ioi_shift x t]
  linarith

/-- Cochrane (2023), §5.7, p. 163: **at `ρ = 0` the printed Phillips-curve form fails** for a
permanent rate rise: in `fisherian_equilibrium` with `ρ = 0`, `x = 0`, so
`κ∫_0^∞ e^{−0·τ}x = 0 ≠ i₀ = π_t`. -/
theorem printed_pc_counterexample_rho_zero {κ i0 : ℝ} (hi : i0 ≠ 0) (t : ℝ) :
    (fun _ : ℝ => i0) t ≠
      κ * ∫ τ in Set.Ioi 0, Real.exp (-(0 * τ)) * (fun _ : ℝ => 0 * i0 / κ) (t + τ) := by
  simp only [zero_mul, zero_div, mul_zero, integral_zero]
  exact hi

/-! ### With Brownian shocks -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ} {r σ κ ρ σi σs : ℝ}

/-- Cochrane (2023), p. 163: the real-rate integral `∫_t^T (i_τ − π_τ) dτ` on the Brownian
path. -/
noncomputable def isProc (r σ κ ρ σi σs : ℝ) (W : ℝ≥0 → Ω → ℝ) (t T : ℝ) (ω : Ω) : ℝ :=
  ∫ u in t..T, (iProc σi W u ω - piProc r σ κ ρ σi σs W u ω)

/-- Cochrane (2023), p. 163, on every path: `∫_t^T (i − π) = −(A/λ₂)((W − Y)_T − (W − Y)_t)`
(`A` = `TidyR7StochCTPath.fiscalLoad`, `W − Y` = `kerProc W 1 (−1) λ₂`). -/
theorem isProc_eq (hκ : 0 < κ) (hσ : 0 < σ) (hcont : ∀ ω, Continuous fun t => W t ω)
    (t T : ℝ) (ω : Ω) :
    isProc r σ κ ρ σi σs W t T ω = -(fiscalLoad r σ κ ρ σs / lam2 ρ κ σ)
      * (kerProc W 1 (-1) (lam2 ρ κ σ) T ω - kerProc W 1 (-1) (lam2 ρ κ σ) t ω) := by
  have h2 := (lam2_pos (ρ := ρ) hκ hσ).ne'
  have hw := continuous_bmReal (hcont ω)
  have hI := ouNoise_incr (lam2 ρ κ σ) hw t T
  have e : (fun u => iProc σi W u ω - piProc r σ κ ρ σi σs W u ω)
      = fun u => -fiscalLoad r σ κ ρ σs * ouNoise (lam2 ρ κ σ) (fun u => bmReal W u ω) u := by
    funext u
    simp only [iProc, iPath, piProc, piPath]
    ring
  simp only [isProc, kerProc]
  rw [e, intervalIntegral.integral_const_mul]
  field_simp
  linear_combination (-fiscalLoad r σ κ ρ σs) * hI

/-- Cochrane (2023), p. 163: the real-rate integral is integrable. -/
theorem integrable_isProc (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hκ : 0 < κ) (hσ : 0 < σ) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    Integrable (isProc r σ κ ρ σi σs W t T) P := by
  have e : isProc r σ κ ρ σi σs W t T = fun ω => -(fiscalLoad r σ κ ρ σs / lam2 ρ κ σ)
      * (kerProc W 1 (-1) (lam2 ρ κ σ) T ω - kerProc W 1 (-1) (lam2 ρ κ σ) t ω) := by
    funext ω
    exact isProc_eq hκ hσ hcont t T ω
  rw [e]
  exact ((integrable_kerProc (𝓕 := 𝓕) hB hW h𝓕 hcont hW0 _ _ _ (ht.trans htT)).sub
    (integrable_kerProc (𝓕 := 𝓕) hB hW h𝓕 hcont hW0 _ _ _ ht)).const_mul _

/-- **Cochrane (2023), p. 163: the forecast of the real-rate integral.** For `0 ≤ t ≤ T`, a.s.
`E_t∫_t^T(i − π) = −(A/λ₂)(1 − e^{−λ₂(T−t)})Y_t`. -/
theorem condExp_isProc (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hκ : 0 < κ) (hσ : 0 < σ) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    P[isProc r σ κ ρ σi σs W t T | 𝓕 t] =ᵐ[P] fun ω =>
      -(fiscalLoad r σ κ ρ σs / lam2 ρ κ σ) * (1 - exp (-(lam2 ρ κ σ * (T - t))))
        * kerProc W 0 1 (lam2 ρ κ σ) t ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set lm := lam2 ρ κ σ
  have iT := integrable_kerProc (𝓕 := 𝓕) hB hW h𝓕 hcont hW0 1 (-1) lm (ht.trans htT)
  have it := integrable_kerProc (𝓕 := 𝓕) hB hW h𝓕 hcont hW0 1 (-1) lm ht
  have hm := aesm_kerProc hB hW h𝓕 hcont hW0 1 (-1) lm ht
  have e : isProc r σ κ ρ σi σs W t T = (-(fiscalLoad r σ κ ρ σs / lm))
      • (kerProc W 1 (-1) lm T - kerProc W 1 (-1) lm t) := by
    funext ω
    rw [isProc_eq hκ hσ hcont t T ω]
    rfl
  rw [e]
  filter_upwards [condExp_smul (μ := P) (-(fiscalLoad r σ κ ρ σs / lm))
      (kerProc W 1 (-1) lm T - kerProc W 1 (-1) lm t) (𝓕 t),
    condExp_sub iT it (𝓕 t), condExp_kerProc hB hW h𝓕 hcont hW0 1 (-1) lm ht htT,
    condExp_of_aestronglyMeasurable' (𝓕.le t) hm it] with ω h1 h2 h3 h4
  rw [h1, Pi.smul_apply, h2, Pi.sub_apply, h3, h4]
  simp only [kerProc, smul_eq_mul]
  ring

/-- Cochrane (2023), p. 163 (tool): `x_t − (ρ/κ)i_t = (σA/λ₂)Y_t` on every path. -/
theorem x_sub_i (hκ : 0 < κ) (hσ : 0 < σ) (t : ℝ) (ω : Ω) :
    xProc r σ κ ρ σi σs W t ω - ρ / κ * iProc σi W t ω
      = σ * fiscalLoad r σ κ ρ σs / lam2 ρ κ σ * kerProc W 0 1 (lam2 ρ κ σ) t ω := by
  have h2 := (lam2_pos (ρ := ρ) hκ hσ).ne'
  have hm := lam_mul (ρ := ρ) hκ hσ
  simp only [xProc, xPath, iProc, iPath, kerProc]
  field_simp
  linear_combination (fiscalLoad r σ κ ρ σs * ouNoise (lam2 ρ κ σ)
    (fun u => bmReal W u ω) t) * hm

/-- **Cochrane (2023), p. 163, corrected, under uncertainty.** For `κ, σ > 0` and `t ≥ 0`,
`x_t − (ρ/κ)i_t + σE_t∫_t^T(i − π) → 0` in `L¹` as `T → ∞`: `x_t = (ρ/κ)i_t − σE_t∫_t^∞(i − π)`,
the limit term being `(ρ/κ)E_t i_∞ = (ρ/κ)i_t`. -/
theorem is_corrected_L1 (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hκ : 0 < κ) (hσ : 0 < σ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun T => ∫ ω, |xProc r σ κ ρ σi σs W t ω - ρ / κ * iProc σi W t ω
      + σ * P[isProc r σ κ ρ σi σs W t T | 𝓕 t] ω| ∂P) atTop (𝓝 0) := by
  set lm := lam2 ρ κ σ
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  set c := σ * fiscalLoad r σ κ ρ σs / lm
  set M := ∫ ω, |kerProc W 0 1 lm t ω| ∂P
  have he : Tendsto (fun T => |c| * M * exp (-(lm * (T - t)))) atTop (𝓝 0) := by
    have : Tendsto (fun T => lm * (T - t)) atTop atTop :=
      (tendsto_atTop_add_const_right _ (-t) tendsto_id).const_mul_atTop h2
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp this).const_mul (|c| * M)
    simpa using this
  refine he.congr' ?_
  filter_upwards [eventually_ge_atTop t] with T hT
  symm
  rw [show |c| * M * exp (-(lm * (T - t))) = ∫ ω, (|c| * exp (-(lm * (T - t))))
      * |kerProc W 0 1 lm t ω| ∂P by rw [integral_const_mul]; ring]
  refine integral_congr_ae ?_
  filter_upwards [condExp_isProc (r := r) (σi := σi) (σs := σs) hB hW h𝓕 hcont hW0 hκ hσ ht hT]
    with ω hω
  rw [hω]
  have e := x_sub_i (r := r) (ρ := ρ) (σi := σi) (σs := σs) (W := W) hκ hσ t ω
  have key : xProc r σ κ ρ σi σs W t ω - ρ / κ * iProc σi W t ω + σ * (-(fiscalLoad r σ κ ρ σs
      / lm) * (1 - exp (-(lm * (T - t)))) * kerProc W 0 1 lm t ω)
      = c * exp (-(lm * (T - t))) * kerProc W 0 1 lm t ω := by
    rw [e]
    simp only [c]
    ring
  rw [key, abs_mul, abs_mul, abs_of_pos (exp_pos _)]

/-- **Cochrane (2023), p. 163: the limit term is `lim_T E_t x_T = (ρ/κ)i_t`.** For `κ, σ > 0`,
`t ≥ 0`, `E_t x_T → (ρ/κ)i_t` in `L¹` as `T → ∞`. -/
theorem condExp_x_limit (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hκ : 0 < κ) (hσ : 0 < σ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun T => ∫ ω, |P[xProc r σ κ ρ σi σs W T | 𝓕 t] ω - ρ / κ * iProc σi W t ω| ∂P)
      atTop (𝓝 0) := by
  set lm := lam2 ρ κ σ
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  set c := σ * fiscalLoad r σ κ ρ σs / lm
  set M := ∫ ω, |kerProc W 0 1 lm t ω| ∂P
  have he : Tendsto (fun T => |c| * M * exp (-(lm * (T - t)))) atTop (𝓝 0) := by
    have : Tendsto (fun T => lm * (T - t)) atTop atTop :=
      (tendsto_atTop_add_const_right _ (-t) tendsto_id).const_mul_atTop h2
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp this).const_mul (|c| * M)
    simpa using this
  refine he.congr' ?_
  filter_upwards [eventually_ge_atTop t] with T hT
  symm
  rw [show |c| * M * exp (-(lm * (T - t))) = ∫ ω, (|c| * exp (-(lm * (T - t))))
      * |kerProc W 0 1 lm t ω| ∂P by rw [integral_const_mul]; ring]
  refine integral_congr_ae ?_
  rw [xProc_eq_ker]
  filter_upwards [condExp_kerProc hB hW h𝓕 hcont hW0 (ρ * σi / κ)
    (lam1 ρ κ σ * fiscalLoad r σ κ ρ σs / κ) lm ht hT] with ω hω
  rw [hω]
  have hm := lam_mul (ρ := ρ) hκ hσ
  have key : kerProc W (ρ * σi / κ) (lam1 ρ κ σ * fiscalLoad r σ κ ρ σs / κ
      * exp (-(lm * (T - t)))) lm t ω - ρ / κ * iProc σi W t ω
      = c * exp (-(lm * (T - t))) * kerProc W 0 1 lm t ω := by
    simp only [kerProc, iProc, iPath, c, lm]
    field_simp
    linear_combination (fiscalLoad r σ κ ρ σs * exp (-(lam2 ρ κ σ * (T - t)))
      * ouNoise (lam2 ρ κ σ) (fun u => bmReal W u ω) t) * hm
  rw [key, abs_mul, abs_mul, abs_of_pos (exp_pos _)]

/-- Cochrane (2023), §5.7 (tool): if `∫|f_T − g| → 0` then `∫|f_T| → ∫|g|`. -/
theorem tendsto_integral_abs_of_L1 {f : ℝ → Ω → ℝ} {g : Ω → ℝ} (hf : ∀ T, Integrable (f T) P)
    (hg : Integrable g P) (h : Tendsto (fun T => ∫ ω, |f T ω - g ω| ∂P) atTop (𝓝 0)) :
    Tendsto (fun T => ∫ ω, |f T ω| ∂P) atTop (𝓝 (∫ ω, |g ω| ∂P)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun T => ?_) h
  rw [Real.norm_eq_abs, ← integral_sub (hf T).abs hg.abs]
  refine (abs_integral_le_integral_abs).trans (integral_mono ((hf T).abs.sub hg.abs).abs
    ((hf T).sub hg).abs fun ω => ?_)
  exact abs_abs_sub_abs_le_abs_sub _ _

/-- Cochrane (2023), §5.7, p. 164 (tool): for `t > 0`, `E|W_t| > 0` (from `E[W_t²] = t`). -/
theorem integral_abs_bm_pos (hB : IsPreBrownianReal W P) (hW0 : ∀ ω, W 0 ω = 0) {t : ℝ}
    (ht : 0 < t) : 0 < ∫ ω, |bmReal W t ω| ∂P := by
  have hi : Integrable (bmReal W t) P := hB.integrable_eval _
  refine lt_of_le_of_ne (integral_nonneg fun _ => abs_nonneg _) fun h0 => ?_
  have hz : (fun ω => |bmReal W t ω|) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _ => abs_nonneg _) hi.abs).1 h0.symm
  have hsq := integral_incr_sq hB le_rfl ht.le
  have hb0 : ∀ ω, bmReal W 0 ω = 0 := fun ω => by simp [bmReal, hW0]
  have e : (fun ω => incr W 0 t ω ^ 2) =ᵐ[P] 0 := by
    filter_upwards [hz] with ω hω
    simp only [Pi.zero_apply, abs_eq_zero] at hω
    simp [incr, hω, hb0]
  rw [integral_congr_ae e] at hsq
  simp only [Pi.zero_apply, integral_zero] at hsq
  linarith

/-- **Cochrane (2023), §5.7, p. 163: the printed integrated IS curve fails under uncertainty.**
For `κ, σ > 0`, `t > 0`, the `L¹` distance between `x(t)` and the printed
`−σE_t∫_t^T(i − π)` converges to `|ρ/κ|·E|i_t|`, which is positive when `ρσ_i ≠ 0`. -/
theorem printed_is_fails (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hκ : 0 < κ) (hσ : 0 < σ) (hρi : ρ * σi ≠ 0) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun T => ∫ ω, |xProc r σ κ ρ σi σs W t ω + σ * P[isProc r σ κ ρ σi σs W t T
      | 𝓕 t] ω| ∂P) atTop (𝓝 (∫ ω, |ρ / κ * iProc σi W t ω| ∂P)) ∧
      0 < ∫ ω, |ρ / κ * iProc σi W t ω| ∂P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hxi : Integrable (xProc r σ κ ρ σi σs W t) P := by
    rw [xProc_eq_ker]
    exact integrable_kerProc hB hW h𝓕 hcont hW0 _ _ _ ht.le
  have hii : Integrable (iProc σi W t) P := by
    rw [iProc_eq_ker σi 0]
    exact integrable_kerProc hB hW h𝓕 hcont hW0 _ _ _ ht.le
  refine ⟨tendsto_integral_abs_of_L1 (fun T => hxi.add (integrable_condExp.const_mul σ))
    (hii.const_mul _) ?_, ?_⟩
  · refine (is_corrected_L1 (r := r) (ρ := ρ) (σi := σi) (σs := σs) hB hW h𝓕 hcont hW0 hκ hσ
    ht.le).congr fun T => ?_
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only
    ring_nf
  · have e : (fun ω => |ρ / κ * iProc σi W t ω|) = fun ω => |ρ / κ * σi| * |bmReal W t ω| := by
      funext ω
      simp only [iProc, iPath]
      rw [← abs_mul]
      ring_nf
    rw [e, integral_const_mul]
    have hc : 0 < |ρ / κ * σi| := by
      rw [abs_pos]
      intro h0
      apply hρi
      have := hκ.ne'
      field_simp at h0
      linarith
    exact mul_pos hc (integral_abs_bm_pos hB hW0 ht)

/-! ### The Phillips-curve form with Brownian shocks -/

/-- Cochrane (2023), p. 163: `∫_t^T e^{−ρ(τ−t)}x_τ dτ` on the Brownian path. -/
noncomputable def pcProc (r σ κ ρ σi σs : ℝ) (W : ℝ≥0 → Ω → ℝ) (t T : ℝ) (ω : Ω) : ℝ :=
  ∫ τ in t..T, exp (-(ρ * (τ - t))) * xProc r σ κ ρ σi σs W τ ω

/-- Cochrane (2023), (5.86), p. 162: the `C¹` part `π − R_π(0)w` has derivative `ρπ − κx`. -/
theorem pi_sub_hasDerivAt {w : ℝ → ℝ} (hκ : 0 < κ) (hw : Continuous w) (t : ℝ) :
    HasDerivAt (fun u => piPath r σ κ ρ σi σs w u - respPi r σ κ ρ σi σs 0 * w u)
      (ρ * piPath r σ κ ρ σi σs w t - κ * xPath r σ κ ρ σi σs w t) t := by
  have h := (hasDerivAt_sub_ouNoise (lam2 ρ κ σ) hw t).const_mul (-fiscalLoad r σ κ ρ σs)
  have hf : (fun u => piPath r σ κ ρ σi σs w u - respPi r σ κ ρ σi σs 0 * w u)
      = fun u => -fiscalLoad r σ κ ρ σs * (w u - ouNoise (lam2 ρ κ σ) w u) := by
    funext u
    simp only [piPath, respPi_zero]
    ring
  rw [hf]
  refine h.congr_deriv ?_
  have hs := lam_sub ρ κ σ
  simp only [piPath, xPath]
  field_simp
  linear_combination (fiscalLoad r σ κ ρ σs * ouNoise (lam2 ρ κ σ) w t) * hs

/-- **Cochrane (2023), p. 163, on every path**: `κ∫_t^T e^{−ρ(τ−t)}x_τ dτ
= π_t − e^{−ρ(T−t)}π_T + R_π(0)∫_t^T e^{−ρ(τ−t)} dW_τ` (by parts). -/
theorem pc_identity (hκ : 0 < κ) (hcont : ∀ ω, Continuous fun t => W t ω) (t T : ℝ) (ω : Ω) :
    κ * pcProc r σ κ ρ σi σs W t T ω = piProc r σ κ ρ σi σs W t ω
      - exp (-(ρ * (T - t))) * piProc r σ κ ρ σi σs W T ω
      + respPi r σ κ ρ σi σs 0 * expWiener ρ W t T ω := by
  have hw := continuous_bmReal (hcont ω)
  set w := fun u => bmReal W u ω
  have c1 := continuous_piPath (r := r) (σ := σ) (κ := κ) (ρ := ρ) (σi := σi) (σs := σs) hw
  have c2 := continuous_xPath (r := r) (σ := σ) (κ := κ) (ρ := ρ) (σi := σi) (σs := σs) hw
  have hB := discounted_byParts (fun x => pi_sub_hasDerivAt (r := r) (σ := σ) (ρ := ρ)
    (σi := σi) (σs := σs) hκ hw x) ((c1.const_mul ρ).sub (c2.const_mul κ)) hw ρ
    (respPi r σ κ ρ σi σs 0) t T
  have e1 : ∀ τ, piPath r σ κ ρ σi σs w τ - respPi r σ κ ρ σi σs 0 * w τ
      + respPi r σ κ ρ σi σs 0 * w τ = piPath r σ κ ρ σi σs w τ := fun τ => by ring
  simp only [e1] at hB
  have e2 : (fun τ => exp (-(ρ * (τ - t))) * (ρ * piPath r σ κ ρ σi σs w τ
      - (ρ * piPath r σ κ ρ σi σs w τ - κ * xPath r σ κ ρ σi σs w τ)))
      = fun τ => κ * (exp (-(ρ * (τ - t))) * xPath r σ κ ρ σi σs w τ) := by
    funext τ
    ring
  rw [e2, intervalIntegral.integral_const_mul] at hB
  simp only [pcProc, xProc, piProc, expWiener]
  rw [hB]

/-- **Cochrane (2023), p. 163, conditional on date-`t` information**: for `0 ≤ t ≤ T`,
`κE_t∫_t^T e^{−ρ(τ−t)}x = π_t − e^{−ρ(T−t)}E_tπ_T` a.s. -/
theorem condExp_pcProc (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hκ : 0 < κ) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    (fun ω => κ * P[pcProc r σ κ ρ σi σs W t T | 𝓕 t] ω) =ᵐ[P] fun ω =>
      piProc r σ κ ρ σi σs W t ω - exp (-(ρ * (T - t))) * P[piProc r σ κ ρ σi σs W T | 𝓕 t] ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have ip : ∀ τ, 0 ≤ τ → Integrable (piProc r σ κ ρ σi σs W τ) P := fun τ hτ => by
    rw [piProc_eq_ker]
    exact integrable_kerProc hB hW h𝓕 hcont hW0 _ _ _ hτ
  have hpm : AEStronglyMeasurable[𝓕 t] (piProc r σ κ ρ σi σs W t) P := by
    rw [piProc_eq_ker]
    exact aesm_kerProc hB hW h𝓕 hcont hW0 _ _ _ ht
  have iE := integrable_expWiener hB hW h𝓕 hcont ρ ht htT
  have i1 := (ip t ht).sub ((ip T (ht.trans htT)).smul (exp (-(ρ * (T - t)))))
  have e : pcProc r σ κ ρ σi σs W t T = κ⁻¹ • ((piProc r σ κ ρ σi σs W t
      - (exp (-(ρ * (T - t)))) • piProc r σ κ ρ σi σs W T)
        + (respPi r σ κ ρ σi σs 0) • expWiener ρ W t T) := by
    funext ω
    have := pc_identity (r := r) (σ := σ) (ρ := ρ) (σi := σi) (σs := σs) hκ hcont t T ω
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    rw [← this]
    field_simp
  rw [e]
  filter_upwards [condExp_smul (μ := P) κ⁻¹ ((piProc r σ κ ρ σi σs W t
      - (exp (-(ρ * (T - t)))) • piProc r σ κ ρ σi σs W T)
        + (respPi r σ κ ρ σi σs 0) • expWiener ρ W t T) (𝓕 t),
    condExp_add i1 (iE.smul (respPi r σ κ ρ σi σs 0)) (𝓕 t),
    condExp_sub (ip t ht) ((ip T (ht.trans htT)).smul (exp (-(ρ * (T - t))))) (𝓕 t),
    condExp_of_aestronglyMeasurable' (𝓕.le t) hpm (ip t ht),
    condExp_smul (μ := P) (exp (-(ρ * (T - t)))) (piProc r σ κ ρ σi σs W T) (𝓕 t),
    condExp_smul (μ := P) (respPi r σ κ ρ σi σs 0) (expWiener ρ W t T) (𝓕 t),
    condExp_expWiener hB hW h𝓕 hcont ρ ht htT] with ω h0 h1 h2 h3 h4 h5 h6
  rw [h0, Pi.smul_apply, h1, Pi.add_apply, h2, Pi.sub_apply, h3, h4, h5]
  simp only [Pi.smul_apply, smul_eq_mul, h6, Pi.zero_apply, mul_zero, add_zero]
  field_simp

/-- Cochrane (2023), (5.94), p. 164: inflation is the two-mode process with no second mode.
Restates `TidyR7StochCTBrownian.piProc_eq_ker`. -/
theorem piProc_eq_ker2 : piProc r σ κ ρ σi σs W
    = fun t => ker2Proc W σi (fiscalLoad r σ κ ρ σs) (lam2 ρ κ σ) 0 0 t := by
  funext t ω
  simp [piProc, piPath, ker2Proc, kerProc]

/-- **Cochrane (2023), p. 163: the integrated Phillips curve under uncertainty (`ρ > 0`).** For
`κ, σ > 0`, `t ≥ 0`: `κE_t∫_t^T e^{−ρ(τ−t)}x_τ dτ → π_t` in `L¹` as `T → ∞`, i.e.
`π_t = κE_t∫_0^∞ e^{−ρτ}x_{t+τ}dτ` as printed.
The stochastic version of `CTSimple.ct_pc_integral`. -/
theorem pc_integral_L1 (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 < ρ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun T => ∫ ω, |κ * P[pcProc r σ κ ρ σi σs W t T | 𝓕 t] ω
      - piProc r σ κ ρ σi σs W t ω| ∂P) atTop (𝓝 0) := by
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  set K := (|σi| + |fiscalLoad r σ κ ρ σs| + |(0 : ℝ)|) ^ 2
  refine squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _)
    ?_ (tendsto_exp_mul_affine hρ t K)
  filter_upwards [eventually_ge_atTop t] with T hT
  have hcond := condExp_pcProc (r := r) (σ := σ) (ρ := ρ) (σi := σi) (σs := σs)
    hB hW h𝓕 hcont hW0 hκ ht hT
  have e : ∫ ω, |κ * P[pcProc r σ κ ρ σi σs W t T | 𝓕 t] ω - piProc r σ κ ρ σi σs W t ω| ∂P
      = exp (-(ρ * (T - t))) * ∫ ω, |P[piProc r σ κ ρ σi σs W T | 𝓕 t] ω| ∂P := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hcond] with ω hω
    rw [hω, sub_sub_cancel_left, abs_neg, abs_mul, abs_of_pos (exp_pos _)]
  rw [e]
  refine mul_le_mul_of_nonneg_left ((integral_abs_condExp_le _).trans ?_) (exp_pos _).le
  rw [piProc_eq_ker2]
  exact integral_abs_ker2Proc_le hB hW h𝓕 hcont hW0 h2.le le_rfl (ht.trans hT)

/-- **Cochrane (2023), p. 163, at `ρ = 0`, under uncertainty: the corrected Phillips form.**
For `κ, σ > 0`, `t ≥ 0`: `κE_t∫_t^T x_τ dτ + i_t → π_t` in `L¹` (`π_t = κE_t∫_0^∞ x + E_tπ_∞`,
`E_tπ_∞ = i_t`). -/
theorem pc_rho_zero_L1 (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hκ : 0 < κ) (hσ : 0 < σ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun T => ∫ ω, |κ * P[pcProc r σ κ 0 σi σs W t T | 𝓕 t] ω + iProc σi W t ω
      - piProc r σ κ 0 σi σs W t ω| ∂P) atTop (𝓝 0) := by
  set lm := lam2 0 κ σ
  have h2 := lam2_pos (ρ := 0) hκ hσ
  set c := fiscalLoad r σ κ 0 σs
  set M := ∫ ω, |kerProc W 0 1 lm t ω| ∂P
  have he : Tendsto (fun T => |c| * M * exp (-(lm * (T - t)))) atTop (𝓝 0) := by
    have : Tendsto (fun T => lm * (T - t)) atTop atTop :=
      (tendsto_atTop_add_const_right _ (-t) tendsto_id).const_mul_atTop h2
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp this).const_mul (|c| * M)
    simpa using this
  refine he.congr' ?_
  filter_upwards [eventually_ge_atTop t] with T hT
  symm
  rw [show |c| * M * exp (-(lm * (T - t))) = ∫ ω, (|c| * exp (-(lm * (T - t))))
      * |kerProc W 0 1 lm t ω| ∂P by rw [integral_const_mul]; ring]
  refine integral_congr_ae ?_
  have hpk := condExp_kerProc (𝓕 := 𝓕) hB hW h𝓕 hcont hW0 σi c lm ht hT
  have epk : piProc r σ κ 0 σi σs W T = kerProc W σi c lm T := rfl
  rw [← epk] at hpk
  filter_upwards [condExp_pcProc (r := r) (σ := σ) (ρ := 0) (σi := σi) (σs := σs)
    hB hW h𝓕 hcont hW0 hκ ht hT, hpk] with ω hω hk
  rw [hω, hk]
  simp only [kerProc, iProc, iPath, c, lm, zero_mul, neg_zero, exp_zero, one_mul, zero_add]
  rw [show piProc r σ κ 0 σi σs W t ω - (σi * bmReal W t ω + fiscalLoad r σ κ 0 σs
      * exp (-(lam2 0 κ σ * (T - t))) * ouNoise (lam2 0 κ σ) (fun u => bmReal W u ω) t)
      + σi * bmReal W t ω - piProc r σ κ 0 σi σs W t ω = -(fiscalLoad r σ κ 0 σs)
      * exp (-(lam2 0 κ σ * (T - t))) * ouNoise (lam2 0 κ σ) (fun u => bmReal W u ω) t by ring]
  rw [abs_mul, abs_mul, abs_neg, abs_of_pos (exp_pos _)]

/-! ### Non-vacuity -/

/-- **Cochrane (2023), p. 163 (non-vacuity on the constructed motion `bmPath`)**: for
`κ, σ > 0`, `ρσ_i ≠ 0` and `t > 0`, the printed IS form misses `x(t)` by a positive `L¹`
distance in the limit, while the corrected form holds. -/
theorem bmPath_printed_is_fails (hκ : 0 < κ) (hσ : 0 < σ) (hρi : ρ * σi ≠ 0) {t : ℝ}
    (ht : 0 < t) :
    0 < ∫ ω, |ρ / κ * iProc σi bmPath t ω| ∂gaussSeq ∧
      Tendsto (fun T => ∫ ω, |xProc r σ κ ρ σi σs bmPath t ω - ρ / κ * iProc σi bmPath t ω
        + σ * gaussSeq[isProc r σ κ ρ σi σs bmPath t T
          | bmFiltrationReal bmPath measurable_bmPath t] ω| ∂gaussSeq) atTop (𝓝 0) := by
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  exact ⟨(printed_is_fails (r := r) (σs := σs) hB measurable_bmPath h𝓕 continuous_bmPath
      bmPath_zero hκ hσ hρi ht).2,
    is_corrected_L1 hB measurable_bmPath h𝓕 continuous_bmPath bmPath_zero hκ hσ ht.le⟩

end Cochrane.StickyPriceFiscal.TidyR8StochCTIntegralForms
