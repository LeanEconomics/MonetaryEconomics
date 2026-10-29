/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.CTSurplus
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The operator calculus `L(D)` of §5.7.2 for general responses and general shocks

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.7.2, pp. 167–169
(the Hansen–Sargent formulas `E_t ∫_0^∞ e^{−rτ} s_{t+τ} dτ = [(L(D) − L(r))/(r − D)] Dε_t` and
`Δ_t ∫_0^∞ e^{−rτ} s_{t+τ} dτ = L(r) Dε_t`, p. 168).

`CTSurplus` proves these for exponential-sum responses only (`CTSurplus.hs_pv`,
`CTSurplus.hs_innovation`). Here `s_t = L(D) Dε_t` means `s_t = ∫ ℓ(t − u) dε_u` for an impulse
response `ℓ`, and `L` is its
**Laplace transform** `L(z) = ∫_0^∞ e^{−zτ} ℓ(τ) dτ` (`lap`). The class of responses is
`ExpOrder ℓ C a`: `ℓ` continuous with `|ℓ(τ)| ≤ C e^{aτ}` on `[0, ∞)` (every bounded continuous
response has `a = 0`; any `a < r` is allowed, so `L` exists on `z > a` — the Laplace-transformable
class). Shocks: an initial jump `e₀` at date `0` and a bounded continuous shock density `e` on
`[0, ∞)` (deterministic paths after the news; "news" = the difference of two perfect-foresight
paths that agree before the news date). No Itô calculus is used or needed: diffusion shocks
`dε` are outside this deterministic framework.

## Main results

* `integrableOn_lap`, `lap`: the transform exists for `z > a`.
* The forward solution `fwd ℓ r σ = ∫_0^∞ e^{−rτ} ℓ(σ+τ) dτ` (the present value of the response
  `σ` periods after a unit shock, `CTSimple.fwdInt`): `fwd_eq`, `fwd_hasDerivAt`
  (`fwd' = r fwd − ℓ`), `fwd_continuousOn`, `fwd_bound` (`|fwd(σ)| ≤ C e^{aσ}/(r − a)`),
  `fwd_tvc`, **`fwd_unique`** (the solution of `w' = rw − ℓ` satisfying the transversality
  condition is exactly `fwd`: the operator `1/(r − D)` of the forward solution).
* **`innovation`**: `fwd ℓ r 0 = L(r)`: the present-value innovation of a unit shock is `L(r)`.
* **`lap_fwd`, `lap_fwd_div`**: the transform of `fwd` is `(L(z) − L(r))/(r − z)` for every
  `z > a`, `z ≠ r`: the forecast is the response of the operator `(L(D) − L(r))/(r − D)`;
  `lap_fwd_at_r`: at `z = r` the identity degenerates to `0 = 0`.
* General shock paths: `sPath` (`s_t = e₀ℓ(t) + ∫_0^t ℓ(t − u) e(u) du`), `forecast` (the
  date-`t` forecast of the surplus path, future shocks set to zero), **`hs_general`**: the
  date-`t` forecast of the present value is `e₀ fwd(t) + ∫_0^t fwd(t − u) e(u) du`, the response
  of `(L(D) − L(r))/(r − D)` to the same shocks; **`innovation_general`**: a jump `j` in `ε` at
  date `t` changes the date-`t` present-value forecast by exactly `L(r) j`.
* `expSum_expOrder`: the exponential-sum responses of `CTSurplus` belong to the class, and
  `innovation_expSum` recovers `CTSurplus.hs_innovation` from `innovation`.
* `forecast_self`, `forecast_eq_truncated`: the forecast is today's surplus at `x = t` and is the
  surplus path of the shock history truncated at `t`.
-/

namespace Cochrane.StickyPriceFiscal.TidyR6OperatorCalculus

open Filter Topology MeasureTheory Cochrane.StickyPriceFiscal.CTSimple

/-- Cochrane (2023), §5.7.2, p. 168 (the operators `L(D)` the book manipulates): an impulse
response `ℓ` that is continuous and of exponential order `a`, `|ℓ(τ)| ≤ C e^{aτ}` for `τ ≥ 0`. -/
def ExpOrder (ℓ : ℝ → ℝ) (C a : ℝ) : Prop :=
  Continuous ℓ ∧ ∀ τ, 0 ≤ τ → |ℓ τ| ≤ C * Real.exp (a * τ)

/-- Cochrane (2023), §5.7.2, p. 168: the transfer function of `L(D)`, the Laplace transform
`L(z) = ∫_0^∞ e^{−zτ} ℓ(τ) dτ`. -/
noncomputable def lap (ℓ : ℝ → ℝ) (z : ℝ) : ℝ := ∫ τ in Set.Ioi 0, Real.exp (-(z * τ)) * ℓ τ

/-- Cochrane (2023), p. 168 (the forecast operator `1/(r − D)` applied to the response): the
present value `∫_0^∞ e^{−rτ} ℓ(σ + τ) dτ` of the response `σ` periods after a unit shock. -/
noncomputable def fwd (ℓ : ℝ → ℝ) (r σ : ℝ) : ℝ := fwdInt r ℓ σ

/-- Cochrane (2023), p. 168 (tool): `e^{−zτ}ℓ(τ)` is integrable on `(c, ∞)` for `c ≥ 0` and
`z > a`. -/
theorem integrableOn_lap {ℓ : ℝ → ℝ} {C a z c : ℝ} (hℓ : ExpOrder ℓ C a) (hz : a < z)
    (hc : 0 ≤ c) : IntegrableOn (fun τ => Real.exp (-(z * τ)) * ℓ τ) (Set.Ioi c) := by
  have hm : AEStronglyMeasurable (fun τ => Real.exp (-(z * τ)) * ℓ τ)
      (volume.restrict (Set.Ioi c)) :=
    ((by fun_prop : Continuous fun τ : ℝ => Real.exp (-(z * τ))).mul hℓ.1).aestronglyMeasurable
  refine Integrable.mono' ((integrableOn_exp_mul_Ioi (a := -(z - a)) (by linarith) c).const_mul C)
    hm ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono fun τ (hτ : c < τ) => ?_
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
  calc Real.exp (-(z * τ)) * |ℓ τ| ≤ Real.exp (-(z * τ)) * (C * Real.exp (a * τ)) :=
        mul_le_mul_of_nonneg_left (hℓ.2 τ (by linarith)) (Real.exp_pos _).le
    _ = C * Real.exp (-(z - a) * τ) := by
        rw [mul_left_comm, ← Real.exp_add]
        ring_nf

/-- Cochrane (2023), p. 168 (tool): `fwd ℓ r σ = e^{rσ}(L(r) − ∫_0^σ e^{−rs} ℓ(s) ds)` for
`σ ≥ 0`. -/
theorem fwd_eq {ℓ : ℝ → ℝ} {C a r σ : ℝ} (hℓ : ExpOrder ℓ C a) (hr : a < r) (hσ : 0 ≤ σ) :
    fwd ℓ r σ = Real.exp (r * σ) * (lap ℓ r - ∫ s in (0 : ℝ)..σ, Real.exp (-(r * s)) * ℓ s) := by
  rw [fwd, fwdInt, integral_exp_shift, lap,
    ← intervalIntegral.integral_interval_add_Ioi (integrableOn_lap hℓ hr le_rfl)
      (integrableOn_lap hℓ hr hσ)]
  ring

/-- Cochrane (2023), p. 168 (tool): the right-hand side of `fwd_eq` as a function on all of `ℝ`
(continuously differentiable). -/
noncomputable def fwdFormula (ℓ : ℝ → ℝ) (r σ : ℝ) : ℝ :=
  Real.exp (r * σ) * (lap ℓ r - ∫ s in (0 : ℝ)..σ, Real.exp (-(r * s)) * ℓ s)

/-- Cochrane (2023), p. 168 (tool): the formula has derivative `r·formula − ℓ` everywhere. -/
theorem fwdFormula_hasDerivAt {ℓ : ℝ → ℝ} (hc : Continuous ℓ) (r σ : ℝ) :
    HasDerivAt (fwdFormula ℓ r) (r * fwdFormula ℓ r σ - ℓ σ) σ := by
  have hgc : Continuous fun s => Real.exp (-(r * s)) * ℓ s := by fun_prop
  have hP := HasDerivAt.sub (hasDerivAt_const σ (lap ℓ r))
    (hgc.integral_hasStrictDerivAt 0 σ).hasDerivAt
  have h := (hasDerivAt_expPos r σ).mul hP
  refine h.congr_deriv ?_
  have hinv : Real.exp (r * σ) * Real.exp (-(r * σ)) = 1 := by
    rw [← Real.exp_add]; simp
  simp only [fwdFormula, Pi.sub_apply]
  linear_combination (-(ℓ σ)) * hinv

/-- Cochrane (2023), p. 168: **the forward solution solves `w' = rw − ℓ`** after the shock: for
`σ > 0`, `fwd' (σ) = r fwd(σ) − ℓ(σ)`. -/
theorem fwd_hasDerivAt {ℓ : ℝ → ℝ} {C a r σ : ℝ} (hℓ : ExpOrder ℓ C a) (hr : a < r)
    (hσ : 0 < σ) : HasDerivAt (fwd ℓ r) (r * fwd ℓ r σ - ℓ σ) σ := by
  have he : fwd ℓ r =ᶠ[𝓝 σ] fwdFormula ℓ r := by
    filter_upwards [lt_mem_nhds hσ] with x hx
    exact fwd_eq hℓ hr hx.le
  rw [he.eq_of_nhds]
  exact (fwdFormula_hasDerivAt hℓ.1 r σ).congr_of_eventuallyEq he

/-- Cochrane (2023), p. 168 (tool): the forward solution is continuous on `[0, ∞)`. -/
theorem fwd_continuousOn {ℓ : ℝ → ℝ} {C a r : ℝ} (hℓ : ExpOrder ℓ C a) (hr : a < r) :
    ContinuousOn (fwd ℓ r) (Set.Ici 0) := by
  have hcf : Continuous (fwdFormula ℓ r) :=
    continuous_iff_continuousAt.2 fun σ => (fwdFormula_hasDerivAt hℓ.1 r σ).continuousAt
  exact hcf.continuousOn.congr fun σ hσ => fwd_eq hℓ hr hσ

/-- Cochrane (2023), p. 168 (tool): `|fwd ℓ r σ| ≤ C e^{aσ}/(r − a)` for `σ ≥ 0`. -/
theorem fwd_bound {ℓ : ℝ → ℝ} {C a r σ : ℝ} (hℓ : ExpOrder ℓ C a) (hr : a < r) (hσ : 0 ≤ σ) :
    |fwd ℓ r σ| ≤ C * Real.exp (a * σ) / (r - a) := by
  have hra : 0 < r - a := by linarith
  have hint := (integrableOn_exp_mul_Ioi (a := -(r - a)) (by linarith) 0).const_mul
    (C * Real.exp (a * σ))
  rw [fwd, fwdInt, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hint ?_).trans (le_of_eq ?_)
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun τ (hτ : 0 < τ) => ?_
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
    calc Real.exp (-(r * τ)) * |ℓ (σ + τ)| ≤
          Real.exp (-(r * τ)) * (C * Real.exp (a * (σ + τ))) :=
          mul_le_mul_of_nonneg_left (hℓ.2 _ (by linarith)) (Real.exp_pos _).le
      _ = C * Real.exp (a * σ) * Real.exp (-(r - a) * τ) := by
          rw [mul_left_comm, mul_assoc, ← Real.exp_add, ← Real.exp_add]
          ring_nf
  · rw [integral_const_mul]
    have := integral_exp_Ioi hra
    simp only [neg_mul] at this ⊢
    rw [this]
    ring

/-- Cochrane (2023), p. 168: the forward solution satisfies the transversality condition
`e^{−rσ} fwd(σ) → 0`. -/
theorem fwd_tvc {ℓ : ℝ → ℝ} {C a r : ℝ} (hℓ : ExpOrder ℓ C a) (hr : a < r) :
    Tendsto (fun σ => Real.exp (-(r * σ)) * fwd ℓ r σ) atTop (𝓝 0) := by
  have hra : 0 < r - a := by linarith
  have h0 : Tendsto (fun σ : ℝ => C / (r - a) * Real.exp (-((r - a) * σ))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hra)).const_mul (C / (r - a))
    rw [mul_zero] at this
    exact this
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [eventually_ge_atTop 0] with σ hσ
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
  calc Real.exp (-(r * σ)) * |fwd ℓ r σ| ≤
        Real.exp (-(r * σ)) * (C * Real.exp (a * σ) / (r - a)) :=
        mul_le_mul_of_nonneg_left (fwd_bound hℓ hr hσ) (Real.exp_pos _).le
    _ = C / (r - a) * Real.exp (-((r - a) * σ)) := by
        rw [mul_div_assoc', mul_left_comm, ← Real.exp_add]
        ring_nf

/-- Cochrane (2023), p. 168 (`1/(r − D)`, the forward solution): **existence and uniqueness**.
If `w` is continuous on `[0, ∞)` and `w' = rw − ℓ` on `(0, ∞)`, then `w` satisfies the
transversality condition `e^{−rσ}w_σ → 0` iff `w = fwd ℓ r` on `[0, ∞)`; and `fwd ℓ r` is such a
solution. -/
theorem fwd_unique {ℓ w : ℝ → ℝ} {C a r : ℝ} (hℓ : ExpOrder ℓ C a) (hr : a < r)
    (hc : ContinuousOn w (Set.Ici 0)) (hd : ∀ σ, 0 < σ → HasDerivAt w (r * w σ - ℓ σ) σ) :
    Tendsto (fun σ => Real.exp (-(r * σ)) * w σ) atTop (𝓝 0) ↔
      ∀ σ, 0 ≤ σ → w σ = fwd ℓ r σ := by
  constructor
  · intro h σ hσ
    have := (tvc_iff_forward (t := σ) (hc.mono (Set.Ici_subset_Ici.2 hσ))
      (fun τ hτ => hd τ (by linarith)) (integrableOn_lap hℓ hr hσ)).1 h
    rw [this]
    rfl
  · intro h
    refine (fwd_tvc hℓ hr).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with σ hσ
    rw [h σ hσ]

/-- Cochrane (2023), p. 168: **the present-value innovation is `L(r)`**: the present value of the
response at the shock date is the transfer function at `r`, `fwd ℓ r 0 = L(r)`, for every
response of exponential order. -/
theorem innovation (ℓ : ℝ → ℝ) (r : ℝ) : fwd ℓ r 0 = lap ℓ r := by
  simp [fwd, fwdInt, lap]

/-- Cochrane (2023), p. 168: **the Hansen–Sargent operator identity for every response of
exponential order**: for `z > a` (and `r > a`), the transform of the forecast path `fwd ℓ r`
satisfies `(r − z) · L_fwd(z) = L(z) − L(r)`. -/
theorem lap_fwd {ℓ : ℝ → ℝ} {C a r z : ℝ} (hℓ : ExpOrder ℓ C a) (hr : a < r) (hz : a < z) :
    (r - z) * lap (fwd ℓ r) z = lap ℓ z - lap ℓ r := by
  have hza : 0 < z - a := by linarith
  have hra : 0 < r - a := by linarith
  -- the transform of `fwd` exists
  have hfo : ExpOrder (fwdFormula ℓ r) (C / (r - a)) a := by
    refine ⟨continuous_iff_continuousAt.2 fun σ =>
      (fwdFormula_hasDerivAt hℓ.1 r σ).continuousAt, fun σ hσ => ?_⟩
    have e : fwdFormula ℓ r σ = fwd ℓ r σ := (fwd_eq hℓ hr hσ).symm
    rw [e, div_mul_eq_mul_div]
    exact fwd_bound hℓ hr hσ
  have hlapeq : lap (fwd ℓ r) z = lap (fwdFormula ℓ r) z := by
    refine setIntegral_congr_fun measurableSet_Ioi fun σ (hσ : 0 < σ) => ?_
    simp only [fwd_eq hℓ hr hσ.le, fwdFormula]
  rw [hlapeq]
  have hI1 := integrableOn_lap hfo hz le_rfl
  have hI2 := integrableOn_lap hℓ hz le_rfl
  -- integrate the derivative of `e^{−zσ} F(σ)`
  have hderiv : ∀ σ ∈ Set.Ioi (0 : ℝ), HasDerivAt
      (fun x => Real.exp (-(z * x)) * fwdFormula ℓ r x)
      ((r - z) * (Real.exp (-(z * σ)) * fwdFormula ℓ r σ) - Real.exp (-(z * σ)) * ℓ σ) σ :=
    fun σ _ => ((hasDerivAt_expNeg z σ).mul (fwdFormula_hasDerivAt hℓ.1 r σ)).congr_deriv
      (by ring)
  have hcont : ContinuousWithinAt (fun x => Real.exp (-(z * x)) * fwdFormula ℓ r x)
      (Set.Ici 0) 0 :=
    ((by fun_prop : Continuous fun x : ℝ => Real.exp (-(z * x))).mul hfo.1).continuousWithinAt
  have hlim : Tendsto (fun x => Real.exp (-(z * x)) * fwdFormula ℓ r x) atTop (𝓝 0) := by
    have h0 : Tendsto (fun σ : ℝ => C / (r - a) * Real.exp (-((z - a) * σ))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hza)).const_mul (C / (r - a))
      rw [mul_zero] at this
      exact this
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [eventually_ge_atTop 0] with σ hσ
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
    calc Real.exp (-(z * σ)) * |fwdFormula ℓ r σ| ≤
          Real.exp (-(z * σ)) * (C / (r - a) * Real.exp (a * σ)) :=
          mul_le_mul_of_nonneg_left (hfo.2 σ hσ) (Real.exp_pos _).le
      _ = C / (r - a) * Real.exp (-((z - a) * σ)) := by
          rw [mul_left_comm, ← Real.exp_add]
          ring_nf
  have hint : IntegrableOn (fun σ => (r - z) * (Real.exp (-(z * σ)) * fwdFormula ℓ r σ) -
      Real.exp (-(z * σ)) * ℓ σ) (Set.Ioi 0) := (hI1.const_mul (r - z)).sub hI2
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  rw [integral_sub (hI1.const_mul (r - z)) hI2, integral_const_mul] at h
  have h0 : fwdFormula ℓ r 0 = lap ℓ r := by simp [fwdFormula]
  simp only [mul_zero, neg_zero, Real.exp_zero, one_mul, h0] at h
  simp only [lap] at h ⊢
  linarith

/-- Cochrane (2023), p. 168, `E_t ∫ e^{−rτ}s_{t+τ}dτ = [(L(D) − L(r))/(r − D)] Dε_t`: the forecast
path has transfer function `(L(z) − L(r))/(r − z)` for every `z > a`, `z ≠ r`. -/
theorem lap_fwd_div {ℓ : ℝ → ℝ} {C a r z : ℝ} (hℓ : ExpOrder ℓ C a) (hr : a < r) (hz : a < z)
    (hzr : z ≠ r) : lap (fwd ℓ r) z = (lap ℓ z - lap ℓ r) / (r - z) := by
  have hne : r - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzr)
  rw [← lap_fwd hℓ hr hz]
  field_simp

/-- Cochrane (2023), p. 168: at `z = r` the operator identity `(r − z)L_fwd(z) = L(z) − L(r)`
carries no information (both sides vanish); the value there is the limit of the right side. -/
theorem lap_fwd_at_r {ℓ : ℝ → ℝ} {C a r : ℝ} (hℓ : ExpOrder ℓ C a) (hr : a < r) :
    (r - r) * lap (fwd ℓ r) r = lap ℓ r - lap ℓ r := by
  rw [lap_fwd hℓ hr hr]

/-! ### General shock paths -/

/-- Cochrane (2023), (5.100)–(5.101), p. 168 (`s_t = L(D)Dε_t = ∫ ℓ(t − u) dε_u`): the surplus path
after a jump `e₀` in `ε` at date `0` and a shock density `e` on `(0, t]`,
`s_t = e₀ ℓ(t) + ∫_0^t ℓ(t − u) e(u) du`. -/
noncomputable def sPath (ℓ e : ℝ → ℝ) (e0 t : ℝ) : ℝ :=
  e0 * ℓ t + ∫ u in (0 : ℝ)..t, ℓ (t - u) * e u

/-- Cochrane (2023), p. 168 (`E_t s_x`): the date-`t` forecast of the surplus at date `x ≥ t`,
with the shocks after `t` set to zero, `e₀ ℓ(x) + ∫_0^t ℓ(x − u) e(u) du`. -/
noncomputable def forecast (ℓ e : ℝ → ℝ) (e0 t x : ℝ) : ℝ :=
  e0 * ℓ x + ∫ u in (0 : ℝ)..t, ℓ (x - u) * e u

/-- Cochrane (2023), p. 168: the forecast of today's surplus is today's surplus. -/
theorem forecast_self (ℓ e : ℝ → ℝ) (e0 t : ℝ) : forecast ℓ e e0 t t = sPath ℓ e e0 t := rfl

/-- Cochrane (2023), p. 168 (the forecast is a perfect-foresight path): for `0 ≤ t ≤ x`, the
forecast equals the surplus path of the shock history truncated at `t` (density `e` up to `t`,
zero afterwards). -/
theorem forecast_eq_truncated {ℓ e : ℝ → ℝ} (hℓ : Continuous ℓ) (he : Continuous e)
    (e0 : ℝ) {t x : ℝ} (ht : 0 ≤ t) (htx : t ≤ x) :
    forecast ℓ e e0 t x = sPath ℓ ((Set.Iic t).indicator e) e0 x := by
  simp only [forecast, sPath]
  congr 1
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u => ℓ (x - u) * (Set.Iic t).indicator e u)
      volume a b := by
    intro a b
    have h : (fun u => ℓ (x - u) * (Set.Iic t).indicator e u) =
        (Set.Iic t).indicator (fun u => ℓ (x - u) * e u) := by
      funext u
      by_cases hu : u ∈ Set.Iic t <;> simp [Set.indicator, hu]
    rw [h, intervalIntegrable_iff]
    exact ((by fun_prop : Continuous fun u => ℓ (x - u) * e u).integrableOn_uIoc).indicator
      measurableSet_Iic
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 t) (hint t x)]
  have h2 : ∫ u in t..x, ℓ (x - u) * (Set.Iic t).indicator e u = 0 := by
    rw [intervalIntegral.integral_of_le htx]
    refine (setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_).trans (integral_zero _ _)
    have : u ∉ Set.Iic t := fun h => absurd (Set.mem_Iic.1 h) (not_le.2 hu.1)
    simp [Set.indicator, this]
  rw [h2, add_zero]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [Set.uIcc_of_le ht] at hu
  simp [Set.indicator, hu.2]

/-- Cochrane (2023), p. 168 (tool): the discounted forecast is integrable, and the double
integral over `τ > 0`, `u ∈ (0, t]` is absolutely convergent. -/
theorem pv_integrable {ℓ e : ℝ → ℝ} {C a r M t : ℝ} (hℓ : ExpOrder ℓ C a) (hr : a < r)
    (he : Continuous e) (hM : ∀ u, 0 ≤ u → |e u| ≤ M) :
    Integrable (Function.uncurry fun τ u => Real.exp (-(r * τ)) * ℓ (t + τ - u) * e u)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioc 0 t))) := by
  have hC : 0 ≤ C := by
    have := hℓ.2 0 le_rfl
    simp only [mul_zero, Real.exp_zero, mul_one] at this
    exact (abs_nonneg _).trans this
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 le_rfl)
  set K := C * M * Real.exp (|a| * t)
  have hg : Integrable (fun p : ℝ × ℝ => K * Real.exp (-(r - a) * p.1) * 1)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioc 0 t))) :=
    Integrable.mul_prod (f := fun τ => K * Real.exp (-(r - a) * τ)) (g := fun _ => (1 : ℝ))
      ((integrableOn_exp_mul_Ioi (a := -(r - a)) (by linarith) 0).const_mul K)
      (integrable_const 1)
  have hm : AEStronglyMeasurable
      (Function.uncurry fun τ u => Real.exp (-(r * τ)) * ℓ (t + τ - u) * e u)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioc 0 t))) := by
    refine Continuous.aestronglyMeasurable ?_
    have h1 := hℓ.1
    simp only [Function.uncurry_def]
    fun_prop
  refine Integrable.mono' hg hm ?_
  rw [Measure.prod_restrict]
  refine (ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioc)).mono fun p hp => ?_
  obtain ⟨hτ, hu⟩ := hp
  simp only [Set.mem_Ioi] at hτ
  change ‖Real.exp (-(r * p.1)) * ℓ (t + p.1 - p.2) * e p.2‖ ≤ K * Real.exp (-(r - a) * p.1) * 1
  rw [mul_one, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 : |ℓ (t + p.1 - p.2)| ≤ C * Real.exp (a * (t + p.1 - p.2)) :=
    hℓ.2 _ (by linarith [hu.2])
  have h2 : Real.exp (a * (t + p.1 - p.2)) ≤ Real.exp (|a| * t) * Real.exp (a * p.1) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have : a * (t - p.2) ≤ |a| * t := by
      calc a * (t - p.2) ≤ |a| * (t - p.2) :=
            mul_le_mul_of_nonneg_right (le_abs_self a) (by linarith [hu.2])
        _ ≤ |a| * t := mul_le_mul_of_nonneg_left (by linarith [hu.1]) (abs_nonneg a)
    nlinarith
  calc Real.exp (-(r * p.1)) * |ℓ (t + p.1 - p.2)| * |e p.2|
      ≤ Real.exp (-(r * p.1)) * (C * (Real.exp (|a| * t) * Real.exp (a * p.1))) * M := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (h1.trans
          (mul_le_mul_of_nonneg_left h2 hC)) (Real.exp_pos _).le) (hM _ hu.1.le)
          (abs_nonneg _) (by positivity)
    _ = K * Real.exp (-(r - a) * p.1) := by
        simp only [K]
        rw [show Real.exp (-(r - a) * p.1) = Real.exp (-(r * p.1)) * Real.exp (a * p.1) by
          rw [← Real.exp_add]; ring_nf]
        ring

/-- Cochrane (2023), p. 168 (tool): `τ ↦ e^{−rτ}ℓ(t + τ)` is integrable on `(0, ∞)`. -/
theorem shift_integrable {ℓ : ℝ → ℝ} {C a r t : ℝ} (hℓ : ExpOrder ℓ C a) (hr : a < r)
    (ht : 0 ≤ t) : IntegrableOn (fun τ => Real.exp (-(r * τ)) * ℓ (t + τ)) (Set.Ioi 0) := by
  have h := integrableOn_lap hℓ hr ht
  have e := integral_exp_shift r t ℓ
  have hm : AEStronglyMeasurable (fun τ => Real.exp (-(r * τ)) * ℓ (t + τ))
      (volume.restrict (Set.Ioi 0)) := by
    have := hℓ.1
    exact (by fun_prop : Continuous fun τ => Real.exp (-(r * τ)) * ℓ (t + τ)).aestronglyMeasurable
  refine Integrable.mono' ((integrableOn_exp_mul_Ioi (a := -(r - a)) (by linarith) 0).const_mul
    (C * Real.exp (a * t))) hm ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono fun τ (hτ : 0 < τ) => ?_
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
  calc Real.exp (-(r * τ)) * |ℓ (t + τ)| ≤ Real.exp (-(r * τ)) * (C * Real.exp (a * (t + τ))) :=
        mul_le_mul_of_nonneg_left (hℓ.2 _ (by linarith)) (Real.exp_pos _).le
    _ = C * Real.exp (a * t) * Real.exp (-(r - a) * τ) := by
        rw [mul_left_comm, mul_assoc, ← Real.exp_add, ← Real.exp_add]
        ring_nf

/-- Cochrane (2023), p. 168 (tool): the discounted forecast splits into the initial-jump term
and the integral over past shock densities. -/
theorem pv_integrand_eq (ℓ e : ℝ → ℝ) (r e0 : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (fun τ => Real.exp (-(r * τ)) * forecast ℓ e e0 t (t + τ)) =
      fun τ => e0 * (Real.exp (-(r * τ)) * ℓ (t + τ)) +
        ∫ u in Set.Ioc 0 t, Real.exp (-(r * τ)) * ℓ (t + τ - u) * e u := by
  funext τ
  simp only [forecast]
  rw [intervalIntegral.integral_of_le ht, mul_add, ← integral_const_mul]
  congr 1
  · ring
  · refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only
    ring

/-- Cochrane (2023), p. 168, **Hansen–Sargent for general shock paths**:
`E_t ∫_0^∞ e^{−rτ} s_{t+τ} dτ = [(L(D) − L(r))/(r − D)] Dε_t`. For every response of
exponential order `a < r`, initial jump `e₀` and bounded continuous shock density `e`, the
date-`t` forecast of the present value equals `e₀ fwd(t) + ∫_0^t fwd(t − u) e(u) du`: the
response of the operator whose transfer function is `(L(z) − L(r))/(r − z)` (`lap_fwd_div`) to the
same shocks. -/
theorem hs_general {ℓ e : ℝ → ℝ} {C a r M t : ℝ} (hℓ : ExpOrder ℓ C a) (hr : a < r)
    (he : Continuous e) (hM : ∀ u, 0 ≤ u → |e u| ≤ M) (e0 : ℝ) (ht : 0 ≤ t) :
    ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * forecast ℓ e e0 t (t + τ) =
      e0 * fwd ℓ r t + ∫ u in (0 : ℝ)..t, fwd ℓ r (t - u) * e u := by
  have hF := pv_integrable (t := t) hℓ hr he hM
  have hA := shift_integrable hℓ hr ht
  have hB : Integrable (fun τ => ∫ u in Set.Ioc 0 t, Real.exp (-(r * τ)) * ℓ (t + τ - u) * e u)
      (volume.restrict (Set.Ioi 0)) := hF.integral_prod_left
  have hfun := pv_integrand_eq ℓ e r e0 ht
  rw [hfun, integral_add (hA.const_mul e0) hB, integral_const_mul,
    integral_integral_swap hF, intervalIntegral.integral_of_le ht]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
  rw [fwd, fwdInt, ← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only
  rw [show t + τ - u = t - u + τ by ring]

/-- Cochrane (2023), p. 168, `Δ_t ∫_0^∞ e^{−rτ}s_{t+τ}dτ = L(r)Dε_t`, **for general shock
paths**: if at date `t` the shock `ε` jumps by `j` (news at `t`: the forecasts with and without
the jump agree on every shock before `t`), the date-`t` present-value forecast changes by exactly
`L(r) j`. -/
theorem innovation_general {ℓ e : ℝ → ℝ} {C a r M t : ℝ} (hℓ : ExpOrder ℓ C a) (hr : a < r)
    (he : Continuous e) (hM : ∀ u, 0 ≤ u → |e u| ≤ M) (e0 j : ℝ) (ht : 0 ≤ t) :
    (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * (forecast ℓ e e0 t (t + τ) + j * ℓ (t + τ - t))) -
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * forecast ℓ e e0 t (t + τ) = lap ℓ r * j := by
  have hF := pv_integrable (t := t) hℓ hr he hM
  have hA := shift_integrable hℓ hr ht
  have hB : Integrable (fun τ => ∫ u in Set.Ioc 0 t, Real.exp (-(r * τ)) * ℓ (t + τ - u) * e u)
      (volume.restrict (Set.Ioi 0)) := hF.integral_prod_left
  have hI : IntegrableOn (fun τ => Real.exp (-(r * τ)) * forecast ℓ e e0 t (t + τ))
      (Set.Ioi 0) := by
    rw [pv_integrand_eq ℓ e r e0 ht]
    exact (hA.const_mul e0).add hB
  have hL : IntegrableOn (fun τ => Real.exp (-(r * τ)) * ℓ τ) (Set.Ioi 0) :=
    integrableOn_lap hℓ hr le_rfl
  have hfun : (fun τ => Real.exp (-(r * τ)) * (forecast ℓ e e0 t (t + τ) + j * ℓ (t + τ - t))) =
      fun τ => Real.exp (-(r * τ)) * forecast ℓ e e0 t (t + τ) +
        j * (Real.exp (-(r * τ)) * ℓ τ) := by
    funext τ
    rw [add_sub_cancel_left]
    ring
  rw [hfun, integral_add hI (hL.const_mul j), integral_const_mul, lap]
  ring

/-! ### The exponential-sum class of `CTSurplus` -/

/-- Cochrane (2023), p. 168: the exponential-sum responses `Σ_k c_k e^{−d_k t}` of `CTSurplus`
are of exponential order `a = Σ_k |d_k|` with constant `Σ_k |c_k|`. -/
theorem expSum_expOrder {n : ℕ} (c d : Fin n → ℝ) :
    ExpOrder (CTSurplus.expSum c d) (∑ k, |c k|) (∑ k, |d k|) := by
  refine ⟨by unfold CTSurplus.expSum; fun_prop, fun τ hτ => ?_⟩
  unfold CTSurplus.expSum
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [Real.exp_le_exp]
  have h1 : -d k ≤ ∑ k, |d k| :=
    (neg_le_abs (d k)).trans (Finset.single_le_sum (fun k _ => abs_nonneg (d k))
      (Finset.mem_univ k))
  nlinarith

/-- Cochrane (2023), p. 168: the general innovation theorem recovers `CTSurplus.hs_innovation`:
for exponential sums, `fwd(0) = L(r) = Σ_k c_k/(r + d_k)`. -/
theorem innovation_expSum {n : ℕ} (c d : Fin n → ℝ) {r : ℝ} (h : ∀ k, 0 < r + d k) :
    fwd (CTSurplus.expSum c d) r 0 = CTSurplus.lagOp c d r := by
  rw [innovation, lap, CTSurplus.hs_innovation c d h]

end Cochrane.StickyPriceFiscal.TidyR6OperatorCalculus
