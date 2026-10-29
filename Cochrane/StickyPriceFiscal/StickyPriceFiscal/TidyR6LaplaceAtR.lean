/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.TidyR6OperatorCalculus

/-!
# The Hansen–Sargent operator at `z = r`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.7.2, p. 168: the forecast
operator `(L(D) − L(r))/(r − D)`.

`TidyR6OperatorCalculus.lap_fwd_div` identifies the transform of the forecast path with
`(L(z) − L(r))/(r − z)` for `z ≠ r`; at `z = r` the identity `lap_fwd` degenerates. Here the
value at `z = r` is computed and shown to be the removable-singularity value:

* **`lap_fwd_at_r_value`**: `L_fwd(r) = ∫_0^∞ τ e^{−rτ} ℓ(τ) dτ`;
* `lap_continuousAt`: the Laplace transform of a function of exponential order `a` is continuous
  at every `z > a`;
* **`tendsto_hs_quotient`**: `(L(z) − L(r))/(r − z) → ∫_0^∞ τ e^{−rτ} ℓ(τ) dτ` as `z → r`;
* **`hasDerivAt_lap`**: `L'(r) = −∫_0^∞ τ e^{−rτ} ℓ(τ) dτ`, so the operator at `D = r` is
  `−L'(r)` (`lap_fwd_eq_neg_deriv`).
-/

namespace Cochrane.StickyPriceFiscal.TidyR6LaplaceAtR

open Filter Topology MeasureTheory Cochrane.StickyPriceFiscal.CTSimple
  Cochrane.StickyPriceFiscal.TidyR6OperatorCalculus

/-- Cochrane (2023), p. 168 (tool): `τ e^{−bτ} ≤ (2/b) e^{−(b/2)τ}` for `b > 0`. -/
theorem mul_exp_le {b : ℝ} (hb : 0 < b) (τ : ℝ) :
    τ * Real.exp (-(b * τ)) ≤ 2 / b * Real.exp (-(b / 2 * τ)) := by
  have h1 : b / 2 * τ ≤ Real.exp (b / 2 * τ) := (Real.add_one_le_exp _).trans' (by linarith)
  have h2 : Real.exp (-(b * τ)) = (Real.exp (b / 2 * τ))⁻¹ * Real.exp (-(b / 2 * τ)) := by
    rw [← Real.exp_neg, ← Real.exp_add]
    ring_nf
  rw [h2]
  have hp := Real.exp_pos (b / 2 * τ)
  have hq := Real.exp_pos (-(b / 2 * τ))
  have : τ * (Real.exp (b / 2 * τ))⁻¹ ≤ 2 / b := by
    rw [mul_inv_le_iff₀ hp]
    calc τ = 2 / b * (b / 2 * τ) := by field_simp
      _ ≤ 2 / b * Real.exp (b / 2 * τ) := mul_le_mul_of_nonneg_left h1 (by positivity)
  calc τ * ((Real.exp (b / 2 * τ))⁻¹ * Real.exp (-(b / 2 * τ)))
      = τ * (Real.exp (b / 2 * τ))⁻¹ * Real.exp (-(b / 2 * τ)) := by ring
    _ ≤ 2 / b * Real.exp (-(b / 2 * τ)) := mul_le_mul_of_nonneg_right this hq.le

/-- Cochrane (2023), p. 168 (tool): `τ e^{−rτ} ℓ(τ)` is integrable on `(0, ∞)` for `r > a`. -/
theorem integrableOn_mul_lap {ℓ : ℝ → ℝ} {C a r : ℝ} (hℓ : ExpOrder ℓ C a) (hr : a < r) :
    IntegrableOn (fun τ => τ * (Real.exp (-(r * τ)) * ℓ τ)) (Set.Ioi 0) := by
  have hb : 0 < r - a := by linarith
  have hC : 0 ≤ C := by
    have := hℓ.2 0 le_rfl
    simp only [mul_zero, Real.exp_zero, mul_one] at this
    exact (abs_nonneg _).trans this
  have hm : AEStronglyMeasurable (fun τ => τ * (Real.exp (-(r * τ)) * ℓ τ))
      (volume.restrict (Set.Ioi 0)) := by
    have := hℓ.1
    exact (by fun_prop : Continuous fun τ => τ * (Real.exp (-(r * τ)) * ℓ τ)).aestronglyMeasurable
  refine Integrable.mono' ((integrableOn_exp_Ioi (a := (r - a) / 2) (by linarith)).const_mul
    (C * (2 / (r - a)))) hm ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono fun τ (hτ : 0 < τ) => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hτ, abs_of_pos (Real.exp_pos _)]
  calc τ * (Real.exp (-(r * τ)) * |ℓ τ|) ≤ τ * (Real.exp (-(r * τ)) * (C * Real.exp (a * τ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hℓ.2 τ hτ.le)
          (Real.exp_pos _).le) hτ.le
    _ = C * (τ * Real.exp (-((r - a) * τ))) := by
        rw [show Real.exp (-((r - a) * τ)) = Real.exp (-(r * τ)) * Real.exp (a * τ) by
          rw [← Real.exp_add]; ring_nf]
        ring
    _ ≤ C * (2 / (r - a) * Real.exp (-((r - a) / 2 * τ))) :=
        mul_le_mul_of_nonneg_left (mul_exp_le hb τ) hC
    _ = C * (2 / (r - a)) * Real.exp (-((r - a) / 2 * τ)) := by ring

/-- Cochrane (2023), p. 168 (`(L(D) − L(r))/(r − D)` at `D = r`), **the value at `z = r`**: the
transform of the forecast path at `r` is `∫_0^∞ τ e^{−rτ} ℓ(τ) dτ`. -/
theorem lap_fwd_at_r_value {ℓ : ℝ → ℝ} {C a r : ℝ} (hℓ : ExpOrder ℓ C a) (hr : a < r) :
    lap (fwd ℓ r) r = ∫ τ in Set.Ioi 0, τ * (Real.exp (-(r * τ)) * ℓ τ) := by
  have hra : 0 < r - a := by linarith
  -- `G(σ) = e^{−rσ} fwd(σ) = L(r) − ∫_0^σ e^{−rs} ℓ(s) ds`
  set G : ℝ → ℝ := fun σ => lap ℓ r - ∫ s in (0 : ℝ)..σ, Real.exp (-(r * s)) * ℓ s
  have hgc : Continuous fun s => Real.exp (-(r * s)) * ℓ s := by have := hℓ.1; fun_prop
  have hGd : ∀ σ, HasDerivAt G (-(Real.exp (-(r * σ)) * ℓ σ)) σ := fun σ =>
    (HasDerivAt.sub (hasDerivAt_const σ (lap ℓ r)) (hgc.integral_hasStrictDerivAt 0 σ).hasDerivAt
      ).congr_deriv (by ring)
  have hGeq : ∀ σ, 0 ≤ σ → Real.exp (-(r * σ)) * fwd ℓ r σ = G σ := by
    intro σ hσ
    rw [fwd_eq hℓ hr hσ, ← mul_assoc, ← Real.exp_add]
    simp only [neg_add_cancel, Real.exp_zero, one_mul]
    rfl
  have hGb : ∀ σ, 0 ≤ σ → |G σ| ≤ C / (r - a) * Real.exp (-((r - a) * σ)) := by
    intro σ hσ
    rw [← hGeq σ hσ, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-(r * σ)) * |fwd ℓ r σ| ≤
          Real.exp (-(r * σ)) * (C * Real.exp (a * σ) / (r - a)) :=
          mul_le_mul_of_nonneg_left (fwd_bound hℓ hr hσ) (Real.exp_pos _).le
      _ = C / (r - a) * Real.exp (-((r - a) * σ)) := by
          rw [show Real.exp (-((r - a) * σ)) = Real.exp (-(r * σ)) * Real.exp (a * σ) by
            rw [← Real.exp_add]; ring_nf]
          ring
  have hC : 0 ≤ C := by
    have := hℓ.2 0 le_rfl
    simp only [mul_zero, Real.exp_zero, mul_one] at this
    exact (abs_nonneg _).trans this
  -- integrability of `G` and of `σ ↦ σ e^{−rσ} ℓ(σ)`
  have hGi : IntegrableOn G (Set.Ioi 0) := by
    have hm : AEStronglyMeasurable G (volume.restrict (Set.Ioi 0)) :=
      (continuous_iff_continuousAt.2 fun σ => (hGd σ).continuousAt).aestronglyMeasurable
    refine Integrable.mono' ((integrableOn_exp_Ioi hra).const_mul (C / (r - a))) hm ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun σ (hσ : 0 < σ) => ?_
    rw [Real.norm_eq_abs]
    exact hGb σ hσ.le
  have hHi := integrableOn_mul_lap hℓ hr
  -- integrate `F(σ) = σ G(σ)`
  have hF : ∀ σ ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun x => x * G x)
      (G σ - σ * (Real.exp (-(r * σ)) * ℓ σ)) σ := fun σ _ =>
    ((hasDerivAt_id σ).mul (hGd σ)).congr_deriv (by simp only [id]; ring)
  have hFc : ContinuousWithinAt (fun x => x * G x) (Set.Ici 0) 0 :=
    (continuous_id.mul (continuous_iff_continuousAt.2 fun σ =>
      (hGd σ).continuousAt)).continuousWithinAt
  have hlim : Tendsto (fun x => x * G x) atTop (𝓝 0) := by
    have h0 : Tendsto (fun σ : ℝ => C / (r - a) * (2 / (r - a)) *
        Real.exp (-((r - a) / 2 * σ))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by linarith : 0 < (r - a) / 2))).const_mul
        (C / (r - a) * (2 / (r - a)))
      rw [mul_zero] at this
      exact this
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [eventually_ge_atTop 0] with σ hσ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hσ]
    calc σ * |G σ| ≤ σ * (C / (r - a) * Real.exp (-((r - a) * σ))) :=
          mul_le_mul_of_nonneg_left (hGb σ hσ) hσ
      _ = C / (r - a) * (σ * Real.exp (-((r - a) * σ))) := by ring
      _ ≤ C / (r - a) * (2 / (r - a) * Real.exp (-((r - a) / 2 * σ))) :=
          mul_le_mul_of_nonneg_left (mul_exp_le hra σ) (div_nonneg hC hra.le)
      _ = C / (r - a) * (2 / (r - a)) * Real.exp (-((r - a) / 2 * σ)) := by ring
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto hFc hF (hGi.sub hHi) hlim
  rw [integral_sub hGi hHi] at hI
  simp only [zero_mul, sub_zero] at hI
  have hlapG : lap (fwd ℓ r) r = ∫ σ in Set.Ioi 0, G σ :=
    setIntegral_congr_fun measurableSet_Ioi fun σ (hσ : 0 < σ) => hGeq σ hσ.le
  rw [hlapG]
  linarith

/-- Cochrane (2023), p. 168 (tool): the Laplace transform of a function of exponential order `a`
is continuous at every `z > a`. -/
theorem lap_continuousAt {g : ℝ → ℝ} {C a z0 : ℝ} (hg : ExpOrder g C a) (hz : a < z0) :
    ContinuousAt (lap g) z0 := by
  set b := (a + z0) / 2
  have hb : a < b := by simp only [b]; linarith
  have hbz : b < z0 := by simp only [b]; linarith
  unfold lap
  refine continuousAt_of_dominated (bound := fun x => C * Real.exp (-((b - a) * x))) ?_ ?_
    ((integrableOn_exp_Ioi (by linarith)).const_mul C) ?_
  · exact Eventually.of_forall fun z => by
      have := hg.1
      exact (by fun_prop : Continuous fun τ => Real.exp (-(z * τ)) * g τ).aestronglyMeasurable
  · filter_upwards [lt_mem_nhds hbz] with z hz'
    refine (ae_restrict_mem measurableSet_Ioi).mono fun τ (hτ : 0 < τ) => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-(z * τ)) * |g τ| ≤ Real.exp (-(b * τ)) * (C * Real.exp (a * τ)) :=
          mul_le_mul (Real.exp_le_exp.2 (by nlinarith)) (hg.2 τ hτ.le) (abs_nonneg _)
            (Real.exp_pos _).le
      _ = C * Real.exp (-((b - a) * τ)) := by
          rw [mul_left_comm, ← Real.exp_add]
          ring_nf
  · exact Eventually.of_forall fun τ => by fun_prop

/-- Cochrane (2023), p. 168, **the removable singularity of `(L(D) − L(r))/(r − D)`**: as
`z → r` (`z ≠ r`), `(L(z) − L(r))/(r − z) → ∫_0^∞ τ e^{−rτ} ℓ(τ) dτ`, the transform of the
forecast path at `r` (`lap_fwd_at_r_value`). -/
theorem tendsto_hs_quotient {ℓ : ℝ → ℝ} {C a r : ℝ} (hℓ : ExpOrder ℓ C a) (hr : a < r) :
    Tendsto (fun z => (lap ℓ z - lap ℓ r) / (r - z)) (𝓝[≠] r)
      (𝓝 (∫ τ in Set.Ioi 0, τ * (Real.exp (-(r * τ)) * ℓ τ))) := by
  have hfo : ExpOrder (fwdFormula ℓ r) (C / (r - a)) a := by
    refine ⟨continuous_iff_continuousAt.2 fun σ =>
      (fwdFormula_hasDerivAt hℓ.1 r σ).continuousAt, fun σ hσ => ?_⟩
    have e : fwdFormula ℓ r σ = fwd ℓ r σ := (fwd_eq hℓ hr hσ).symm
    rw [e, div_mul_eq_mul_div]
    exact fwd_bound hℓ hr hσ
  have hlapeq : ∀ z, lap (fwd ℓ r) z = lap (fwdFormula ℓ r) z := fun z =>
    setIntegral_congr_fun measurableSet_Ioi fun σ (hσ : 0 < σ) => by
      simp only [fwd_eq hℓ hr hσ.le, fwdFormula]
  have hc := lap_continuousAt hfo hr
  rw [← lap_fwd_at_r_value hℓ hr, hlapeq]
  refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (lt_mem_nhds hr)] with z hzr hza
  rw [← hlapeq, lap_fwd_div hℓ hr hza hzr]

/-- Cochrane (2023), p. 168: **the derivative of the transfer function**:
`L'(r) = −∫_0^∞ τ e^{−rτ} ℓ(τ) dτ` for every `r > a`. -/
theorem hasDerivAt_lap {ℓ : ℝ → ℝ} {C a r : ℝ} (hℓ : ExpOrder ℓ C a) (hr : a < r) :
    HasDerivAt (lap ℓ) (-∫ τ in Set.Ioi 0, τ * (Real.exp (-(r * τ)) * ℓ τ)) r := by
  rw [hasDerivAt_iff_tendsto_slope]
  refine (tendsto_hs_quotient hℓ hr).neg.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hne : z - r ≠ 0 := sub_ne_zero.2 hz
  have hne' : r - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
  rw [slope_def_field]
  field_simp
  ring

/-- Cochrane (2023), p. 168: at `D = r` the forecast operator `(L(D) − L(r))/(r − D)` is
`−L'(r)`: `L_fwd(r) = −L'(r)`. -/
theorem lap_fwd_eq_neg_deriv {ℓ : ℝ → ℝ} {C a r : ℝ} (hℓ : ExpOrder ℓ C a) (hr : a < r) :
    lap (fwd ℓ r) r = -deriv (lap ℓ) r := by
  rw [(hasDerivAt_lap hℓ hr).deriv, neg_neg, lap_fwd_at_r_value hℓ hr]

end Cochrane.StickyPriceFiscal.TidyR6LaplaceAtR
