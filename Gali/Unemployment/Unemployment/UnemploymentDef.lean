/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Unemployment.Expectations
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Introducing unemployment: participation, the unemployment rate and the wage Phillips curve

Galí (2015), Chapter 7, §7.1.2, pp. 204–207. Taking logs of the participation condition (5)
gives, type by type and **exactly**, `w(j) − p = σ c + φ l(j) + ξ` (`ξ = log χ`); integrating
over `j` gives, again exactly, `∫ w(j) dj − p = σ c + φ ∫ l(j) dj + ξ`. The aggregate
participation equation (6), `w − p = σ c + φ l + ξ`, replaces `∫ w(j)` by the log wage index
`w` and `∫ l(j)` by the log labour force `l = log ∫ L(j) dj`: this is the ONLY approximation,
and it is first order (survey error 4) — along any family of wage distributions
`w(j) = w̄ + s z(j)` the residual of (6) vanishes with zero derivative at `s = 0`.

The unemployment rate (7) is `u ≡ l − n`, so `1 − N/L = 1 − e^{−u}`, within `u²/2` of `u`
for `u ≥ 0` (fn. 6). The average wage markup `μ^w = (w − p) − (σ c + φ n + ξ)` then
satisfies (8) `μ^w = φ u` exactly; the natural rate (10) is `uⁿ = μ^w/φ`; and the wage NKPC
(4) becomes the New Keynesian wage Phillips curve (11) `π^w = β E π^w' − λ_w φ (u − uⁿ)`.
With flexible wages (`θ_w = 0`) the wage markup is constant and `u ≡ uⁿ` (p. 206).

## Main results

* `eq6_type`: (5) in levels ⇒ `w(j) − p = σ c + φ l(j) + ξ` exactly.
* `eq6_integrated`: the exact aggregate relation `∫ w(j) − p = σ c + φ ∫ l(j) + ξ`.
* `eq6_residual_eq`: the residual of (6) is exactly `(w − ∫ w(j)) − φ (l − ∫ l(j))`.
* `wageIndex_first_order`, `laborForce_first_order`, `eq6_first_order`: the two aggregation
  gaps and the residual of (6) are zero with zero derivative at the symmetric point.
* `unemploymentRate_eq`, `rate_le_u`, `abs_rate_sub_u_le` (fn. 6), and
  `abs_rate_sub_u_bound_fails_neg`: the bound `u²/2` fails for negative `u`.
* `eq8_iff`: given the definition of `μ^w` and (7), (6) ⇔ (8) `μ^w = φ u`.
* `natRate_eq`, `natRate_pos`: (10) `uⁿ = μ^w/φ` and `uⁿ > 0` when `μ^w > 0`.
* `wageNKPC_iff_eq11`: (4) ⇔ (11) given (8) and (10).
* `flexible_iff`, `flexible_unemployment_constant`, `fluctuations_require_rigidity`: with
  `θ_w = 0`, the wage-setting rule holds iff `μ̂^w ≡ 0` iff `u ≡ uⁿ`; hence a deviation of `u`
  from `uⁿ` requires `θ_w ≠ 0`.
* `sticky_unemployment_gap_consistent`: conversely, with sticky wages every bounded adapted
  unemployment-gap path is consistent with (11), with a unique bounded wage-inflation path.
-/

namespace Gali.Unemployment.UnemploymentDef

open MeasureTheory ProbabilityTheory

/-! ### (6) type by type and integrated: exact -/

/-- Galí (2015), eq. (5) ⇒ (6) type by type, p. 204: taking logs of
`W(j)/P = χ C^σ L(j)^φ` (all positive) gives **exactly**
`log W(j) − log P = σ log C + φ log L(j) + log χ`. -/
theorem eq6_type {W P C L χ σ φ : ℝ} (hW : 0 < W) (hP : 0 < P) (hC : 0 < C) (hL : 0 < L)
    (hχ : 0 < χ) (h5 : W / P = χ * C ^ σ * L ^ φ) :
    Real.log W - Real.log P = σ * Real.log C + φ * Real.log L + Real.log χ := by
  have h := congrArg Real.log h5
  rw [Real.log_div hW.ne' hP.ne', Real.log_mul (mul_pos hχ (Real.rpow_pos_of_pos hC σ)).ne'
    (Real.rpow_pos_of_pos hL φ).ne', Real.log_mul hχ.ne' (Real.rpow_pos_of_pos hC σ).ne',
    Real.log_rpow hC, Real.log_rpow hL] at h
  linarith

variable {J : Type*} [MeasurableSpace J] {μ : Measure J}

/-- Galí (2015), eq. (6), p. 204 (**exact integrated form**): if `w(j) − p = σ c + φ l(j) + ξ`
for every type `j` and `l` is integrable for the probability measure of types (the book's
`[0, 1]`), then `∫ w(j) dj − p = σ c + φ ∫ l(j) dj + ξ` exactly. -/
theorem eq6_integrated [IsProbabilityMeasure μ] {w l : J → ℝ} {p σ c φ ξ : ℝ}
    (hl : Integrable l μ) (h6 : ∀ j, w j - p = σ * c + φ * l j + ξ) :
    ∫ j, w j ∂μ - p = σ * c + φ * ∫ j, l j ∂μ + ξ := by
  have hw : w = fun j => (p + σ * c + ξ) + φ * l j := funext fun j => by linarith [h6 j]
  rw [hw, integral_add (integrable_const _) (hl.const_mul φ), integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-! ### The aggregation gaps are first order -/

/-- Galí (2015), eq. (4) of Chapter 6, p. 165: the wage index
`W = (∫ W(j)^{1−ε_w} dj)^{1/(1−ε_w)}` (restated from the Chapter 6 project,
`LaborAggregation.cesIndex`). -/
noncomputable def cesIndex (μ : Measure J) (ε : ℝ) (W : J → ℝ) : ℝ :=
  (∫ j, W j ^ (1 - ε) ∂μ) ^ (1 - ε)⁻¹

/-- Galí (2015), p. 204: the aggregate labour force `L = ∫ L(j) dj`, with `L(j) = exp l(j)`. -/
noncomputable def laborForceAgg (μ : Measure J) (l : J → ℝ) : ℝ := ∫ j, Real.exp (l j) ∂μ

/-- Galí (2015), p. 204 (tool): bounded measurable `z` has integrable exponentials
(restated from the Chapter 6 project, `LaborAggregation.integrable_exp_mul`). -/
theorem integrable_exp_mul [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (t : ℝ) : Integrable (fun j => Real.exp (t * z j)) μ := by
  refine Integrable.of_bound ((measurable_const.mul hz).exp.aestronglyMeasurable)
    (Real.exp (|t| * B)) (Filter.Eventually.of_forall fun j => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  calc t * z j ≤ |t * z j| := le_abs_self _
    _ = |t| * |z j| := abs_mul _ _
    _ ≤ |t| * B := mul_le_mul_of_nonneg_left (hB j) (abs_nonneg t)

/-- Galí (2015), p. 204 (tool): a bounded measurable `z` is integrable. -/
theorem integrable_of_bound [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) : Integrable z μ :=
  Integrable.of_bound hz.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun j => by rw [Real.norm_eq_abs]; exact hB j)

/-- Galí (2015), p. 204 (tool): `s ↦ K(a s)` has derivative `a ∫ z` at `0`, `K` the
cumulant-generating function of a bounded `z` (restated from the Chapter 6 project,
`LaborAggregation.hasDerivAt_cgf_mul`). -/
theorem hasDerivAt_cgf_mul [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (a : ℝ) :
    HasDerivAt (fun s => cgf z μ (a * s)) (a * ∫ j, z j ∂μ) 0 := by
  have hset : integrableExpSet z μ = Set.univ :=
    Set.eq_univ_of_forall fun t => integrable_exp_mul hz hB t
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet z μ) := by
    rw [hset, interior_univ]
    trivial
  have hd : HasDerivAt (cgf z μ) (∫ j, z j ∂μ) (a * 0) := by
    have := (analyticAt_cgf h0).differentiableAt.hasDerivAt
    rw [deriv_cgf_zero h0] at this
    rw [mul_zero]
    simpa using this
  have hl : HasDerivAt (fun s : ℝ => a * s) a 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul a
  exact (hd.comp 0 hl).congr_deriv (by ring)

/-- Galí (2015), p. 204: along `W(j) = exp(w̄ + s z(j))`, **exactly**
`log W = w̄ + K((1 − ε) s)/(1 − ε)`, `K` the cumulant-generating function of `z`. -/
theorem log_cesIndex_family [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) {ε : ℝ} (hε : ε ≠ 1) (wbar s : ℝ) :
    Real.log (cesIndex μ ε (fun j => Real.exp (wbar + s * z j)))
      = wbar + cgf z μ ((1 - ε) * s) / (1 - ε) := by
  have hM : ∀ t, 0 < mgf z μ t := fun t => mgf_pos (integrable_exp_mul hz hB t)
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have hsum : ∫ j, Real.exp (wbar + s * z j) ^ (1 - ε) ∂μ
      = Real.exp ((1 - ε) * wbar) * mgf z μ ((1 - ε) * s) := by
    have : ∀ j, Real.exp (wbar + s * z j) ^ (1 - ε)
        = Real.exp ((1 - ε) * wbar) * Real.exp ((1 - ε) * s * z j) := by
      intro j
      rw [← Real.exp_mul, ← Real.exp_add]
      congr 1
      ring
    simp_rw [this]
    rw [integral_const_mul]
    rfl
  have hpos : 0 < Real.exp ((1 - ε) * wbar) * mgf z μ ((1 - ε) * s) :=
    mul_pos (Real.exp_pos _) (hM _)
  unfold cesIndex
  rw [hsum, Real.log_rpow hpos, Real.log_mul (Real.exp_pos _).ne' (hM _).ne', Real.log_exp, cgf]
  field_simp

/-- Galí (2015), p. 204: along `l(j) = l̄ + s z(j)`, **exactly**
`log ∫ exp l(j) dj = l̄ + K(s)`. -/
theorem log_laborForce_family [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) (lbar s : ℝ) :
    Real.log (laborForceAgg μ (fun j => lbar + s * z j)) = lbar + cgf z μ s := by
  have hM : 0 < mgf z μ s := mgf_pos (integrable_exp_mul hz hB s)
  have hsum : laborForceAgg μ (fun j => lbar + s * z j) = Real.exp lbar * mgf z μ s := by
    unfold laborForceAgg
    simp_rw [Real.exp_add]
    rw [integral_const_mul]
    rfl
  rw [hsum, Real.log_mul (Real.exp_pos _).ne' hM.ne', Real.log_exp, cgf]

/-- Galí (2015), p. 204 (**`w ≃ ∫ w(j) dj` is first order**): along `w(j) = w̄ + s z(j)` with
bounded measurable `z`, the gap `log W(s) − ∫ w(j) dj` is `0` at `s = 0` with derivative `0`. -/
theorem wageIndex_first_order [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ j, |z j| ≤ B) {ε : ℝ} (hε : ε ≠ 1) (wbar : ℝ) :
    Real.log (cesIndex μ ε (fun j => Real.exp (wbar + 0 * z j))) - ∫ j, (wbar + 0 * z j) ∂μ
        = 0 ∧
      HasDerivAt (fun s => Real.log (cesIndex μ ε (fun j => Real.exp (wbar + s * z j)))
        - ∫ j, (wbar + s * z j) ∂μ) 0 0 := by
  have hzi := integrable_of_bound (μ := μ) hz hB
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have hint : ∀ s, ∫ j, (wbar + s * z j) ∂μ = wbar + s * ∫ j, z j ∂μ := fun s => by
    rw [integral_add (integrable_const _) (hzi.const_mul s), integral_const_mul]
    simp
  have hfun : (fun s => Real.log (cesIndex μ ε (fun j => Real.exp (wbar + s * z j)))
      - ∫ j, (wbar + s * z j) ∂μ)
      = fun s => cgf z μ ((1 - ε) * s) / (1 - ε) - s * ∫ j, z j ∂μ := funext fun s => by
    rw [log_cesIndex_family hz hB hε, hint]
    ring
  refine ⟨by rw [log_cesIndex_family hz hB hε, hint]; simp [cgf_zero], ?_⟩
  rw [hfun]
  have h1 := (hasDerivAt_cgf_mul (μ := μ) hz hB (1 - ε)).div_const (1 - ε)
  have h2 := (hasDerivAt_id (0 : ℝ)).mul_const (∫ j, z j ∂μ)
  refine (HasDerivAt.sub h1 h2).congr_deriv ?_
  field_simp
  simp

/-- Galí (2015), p. 204 (**`l ≃ ∫ l(j) dj` is first order**): along `l(j) = l̄ + s z(j)` with
bounded measurable `z`, the gap `log ∫ L(j) dj − ∫ l(j) dj` is `0` at `s = 0` with
derivative `0`. -/
theorem laborForce_first_order [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z)
    {B : ℝ} (hB : ∀ j, |z j| ≤ B) (lbar : ℝ) :
    Real.log (laborForceAgg μ (fun j => lbar + 0 * z j)) - ∫ j, (lbar + 0 * z j) ∂μ = 0 ∧
      HasDerivAt (fun s => Real.log (laborForceAgg μ (fun j => lbar + s * z j))
        - ∫ j, (lbar + s * z j) ∂μ) 0 0 := by
  have hzi := integrable_of_bound (μ := μ) hz hB
  have hint : ∀ s, ∫ j, (lbar + s * z j) ∂μ = lbar + s * ∫ j, z j ∂μ := fun s => by
    rw [integral_add (integrable_const _) (hzi.const_mul s), integral_const_mul]
    simp
  have hfun : (fun s => Real.log (laborForceAgg μ (fun j => lbar + s * z j))
      - ∫ j, (lbar + s * z j) ∂μ) = fun s => cgf z μ (1 * s) - s * ∫ j, z j ∂μ :=
    funext fun s => by
      rw [log_laborForce_family hz hB, hint, one_mul]
      ring
  refine ⟨by rw [log_laborForce_family hz hB, hint]; simp [cgf_zero], ?_⟩
  rw [hfun]
  have h1 := hasDerivAt_cgf_mul (μ := μ) hz hB 1
  have h2 := (hasDerivAt_id (0 : ℝ)).mul_const (∫ j, z j ∂μ)
  refine (HasDerivAt.sub h1 h2).congr_deriv ?_
  simp

/-- Galí (2015), eq. (6), p. 204 (**the residual of (6) is exactly the aggregation gaps**): if
(6) holds type by type and `l(·)` is integrable, then for any aggregate `w`, `l`,
`(w − p) − (σ c + φ l + ξ) = (w − ∫ w(j)) − φ (l − ∫ l(j))`. -/
theorem eq6_residual_eq [IsProbabilityMeasure μ] {wj lj : J → ℝ} {p σ c φ ξ : ℝ}
    (hl : Integrable lj μ) (h6 : ∀ j, wj j - p = σ * c + φ * lj j + ξ) (w l : ℝ) :
    (w - p) - (σ * c + φ * l + ξ) = (w - ∫ j, wj j ∂μ) - φ * (l - ∫ j, lj j ∂μ) := by
  have := eq6_integrated hl h6
  linear_combination this

/-- Galí (2015), eq. (6), p. 204 (**(6) holds to first order**, survey error 4). Let wages be
`w(j) = w̄ + s z(j)` (`z` bounded measurable), let each type's labour force `l(j)` satisfy the
exact type-by-type relation (6), and let `w = log W` (the wage index, `ε_w ≠ 1`) and
`l = log ∫ L(j) dj`. Then the residual `R(s) = (w − p) − (σ c + φ l + ξ)` of the aggregate
equation (6) satisfies `R(0) = 0` and `R'(0) = 0`. -/
theorem eq6_first_order [IsProbabilityMeasure μ] {z : J → ℝ} (hz : Measurable z) {B : ℝ}
    (hB : ∀ j, |z j| ≤ B) {ε σ φ p c ξ wbar : ℝ} (hε : ε ≠ 1) (hφ : φ ≠ 0)
    {lj : ℝ → J → ℝ} (h6 : ∀ s j, wbar + s * z j - p = σ * c + φ * lj s j + ξ) :
    (Real.log (cesIndex μ ε (fun j => Real.exp (wbar + 0 * z j))) - p)
        - (σ * c + φ * Real.log (laborForceAgg μ (lj 0)) + ξ) = 0 ∧
      HasDerivAt (fun s => (Real.log (cesIndex μ ε (fun j => Real.exp (wbar + s * z j))) - p)
        - (σ * c + φ * Real.log (laborForceAgg μ (lj s)) + ξ)) 0 0 := by
  set lbar := (wbar - p - σ * c - ξ) / φ
  have hlj : ∀ s, lj s = fun j => lbar + (s / φ) * z j := fun s => funext fun j => by
    have := h6 s j
    simp only [lbar]
    field_simp
    linear_combination -this
  have hsubε : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have hR : ∀ s, (Real.log (cesIndex μ ε (fun j => Real.exp (wbar + s * z j))) - p)
      - (σ * c + φ * Real.log (laborForceAgg μ (lj s)) + ξ)
      = cgf z μ ((1 - ε) * s) / (1 - ε) - φ * cgf z μ (φ⁻¹ * s) := fun s => by
    rw [log_cesIndex_family hz hB hε, hlj s, log_laborForce_family hz hB]
    simp only [lbar]
    rw [show s / φ = φ⁻¹ * s by ring]
    field_simp
    ring
  refine ⟨by rw [hR 0]; simp [cgf_zero], ?_⟩
  rw [funext hR]
  have h1 := (hasDerivAt_cgf_mul (μ := μ) hz hB (1 - ε)).div_const (1 - ε)
  have h2 := (hasDerivAt_cgf_mul (μ := μ) hz hB φ⁻¹).const_mul φ
  refine (HasDerivAt.sub h1 h2).congr_deriv ?_
  field_simp
  ring

/-! ### The unemployment rate (7) and footnote 6 -/

/-- Galí (2015), eq. (7) and fn. 6, p. 205: with `u = l − n = log L − log N`
(`N, L > 0`), the conventional unemployment rate is `1 − N/L = 1 − e^{−u}`. -/
theorem unemploymentRate_eq {N L : ℝ} (hN : 0 < N) (hL : 0 < L) :
    1 - N / L = 1 - Real.exp (-(Real.log L - Real.log N)) := by
  rw [neg_sub, Real.exp_sub, Real.exp_log hN, Real.exp_log hL]

/-- Galí (2015), fn. 6, p. 205: `1 − e^{−u} ≤ u` for every `u`. -/
theorem rate_le_u (u : ℝ) : 1 - Real.exp (-u) ≤ u := by
  have := Real.add_one_le_exp (-u)
  linarith

/-- Galí (2015), fn. 6, p. 205 (tool): `e^{−u} ≤ 1 − u + u²/2` for `u ≥ 0`. -/
theorem exp_neg_le_quadratic {u : ℝ} (hu : 0 ≤ u) : Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 := by
  set g : ℝ → ℝ := fun x => 1 - x + x ^ 2 / 2 - Real.exp (-x)
  have hg : ∀ x, HasDerivAt g (-1 + x + Real.exp (-x)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => 1 - y + y ^ 2 / 2) (-1 + x) x := by
      have a := ((hasDerivAt_id x).const_sub 1).add ((hasDerivAt_pow 2 x).div_const 2)
      refine a.congr_deriv ?_
      simp
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
      have := (hasDerivAt_neg x).exp
      simpa [mul_comm] using this
    exact (HasDerivAt.sub h1 h2).congr_deriv (by ring)
  have hmono : Monotone g := by
    refine monotone_of_deriv_nonneg (fun x => (hg x).differentiableAt) fun x => ?_
    rw [(hg x).deriv]
    have := Real.add_one_le_exp (-x)
    linarith
  have h := hmono hu
  simp only [g] at h
  norm_num at h
  linarith

/-- Galí (2015), fn. 6, p. 205: `1 − N/L = 1 − e^{−u} ≃ u` near zero, quantitatively:
`|1 − e^{−u} − u| ≤ u²/2` for every `u ≥ 0`. -/
theorem abs_rate_sub_u_le {u : ℝ} (hu : 0 ≤ u) : |1 - Real.exp (-u) - u| ≤ u ^ 2 / 2 := by
  have h1 := rate_le_u u
  have h2 := exp_neg_le_quadratic hu
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- Galí (2015), fn. 6, p. 205 (the bound is one-sided): for negative `u` the bound `u²/2`
fails; at `u = −1`, `|1 − e − (−1)| > 1/2`. -/
theorem abs_rate_sub_u_bound_fails_neg :
    (-1 : ℝ) ^ 2 / 2 < |1 - Real.exp (-(-1)) - (-1)| := by
  rw [neg_neg]
  have he := Real.exp_one_gt_d9
  rw [abs_of_neg (by linarith)]
  norm_num
  linarith

/-! ### (8) and (10) -/

/-- Galí (2015), p. 205: the average wage markup `μ^w = (w − p) − (σ c + φ n + ξ)`. -/
def wageMarkup (σ φ ξ w p c n : ℝ) : ℝ := (w - p) - (σ * c + φ * n + ξ)

/-- Galí (2015), eq. (8), p. 205: given the definition of `μ^w` and (7) `u = l − n`, the
participation equation (6) holds **iff** `μ^w = φ u`; so (8) is exact given (6). -/
theorem eq8_iff {σ φ ξ w p c n l : ℝ} :
    w - p = σ * c + φ * l + ξ ↔ wageMarkup σ φ ξ w p c n = φ * (l - n) := by
  unfold wageMarkup
  constructor <;> intro h <;> linarith

/-- Galí (2015), eq. (10), p. 206: the natural rate of unemployment, `uⁿ = μ^w/φ`. -/
noncomputable def natRate (μw φ : ℝ) : ℝ := μw / φ

/-- Galí (2015), eq. (10), p. 206: absent wage rigidities the markup equals its desired value
`μ^w`, and by (8) `φ u = μ^w` iff `u = uⁿ = μ^w/φ` (`φ ≠ 0`). -/
theorem natRate_eq {μw φ u : ℝ} (hφ : φ ≠ 0) : φ * u = μw ↔ u = natRate μw φ := by
  unfold natRate
  constructor
  · intro h
    rw [← h]
    field_simp
  · intro h
    rw [h]
    field_simp

/-- Galí (2015), p. 206: market power in the labour market (`μ^w > 0`) implies a positive
natural rate of unemployment, `uⁿ > 0` (for `φ > 0`). -/
theorem natRate_pos {μw φ : ℝ} (hμ : 0 < μw) (hφ : 0 < φ) : 0 < natRate μw φ :=
  div_pos hμ hφ

/-- Galí (2015), eqs. (8), (10), p. 206: the markup gap is proportional to the unemployment
gap, `μ^w_t − μ^w = φ (u_t − uⁿ)`, for `φ ≠ 0`. -/
theorem markupGap_eq {μw φ u : ℝ} (hφ : φ ≠ 0) : φ * u - μw = φ * (u - natRate μw φ) := by
  unfold natRate
  field_simp

/-! ### The New Keynesian wage Phillips curve (11) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (4), p. 203 (= Chapter 6 eq. (15), restated): the wage NKPC
`π^w_t = β E_t π^w_{t+1} − λ_w μ̂^w_t`, `μ̂^w_t = μ^w_t − μ^w`. -/
def WageNKPC (β lamW : ℝ) (pw muhat : ℕ → Ω → ℝ) : Prop :=
  ∀ t, pw t = β • 𝔼.E t (pw (t + 1)) - lamW • muhat t

/-- Galí (2015), eq. (11), p. 207: the New Keynesian wage Phillips curve
`π^w_t = β E_t π^w_{t+1} − λ_w φ (u_t − uⁿ)`. -/
def WagePhillips (β lamW φ un : ℝ) (pw u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, pw t = β • 𝔼.E t (pw (t + 1)) - (lamW * φ) • (u t - fun _ => un)

/-- Galí (2015), eqs. (4), (8), (10), (11), pp. 203–207: if the average wage markup satisfies
(8) `μ^w_t = φ u_t` at every date and `μ̂^w_t = μ^w_t − μ^w`, then the wage NKPC (4) holds
**iff** the wage Phillips curve (11) holds with `uⁿ = μ^w/φ` (`φ ≠ 0`). -/
theorem wageNKPC_iff_eq11 {β lamW φ μw : ℝ} (hφ : φ ≠ 0) {pw u muW : ℕ → Ω → ℝ}
    (h8 : ∀ t, muW t = φ • u t) :
    WageNKPC 𝔼 β lamW pw (fun t => muW t - fun _ => μw) ↔
      WagePhillips 𝔼 β lamW φ (natRate μw φ) pw u := by
  have hk : ∀ t, lamW • (muW t - fun _ => μw) = (lamW * φ) • (u t - fun _ => natRate μw φ) :=
    fun t => by
      rw [h8 t]
      funext x
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [mul_assoc, ← markupGap_eq hφ]
  unfold WageNKPC WagePhillips
  simp only [hk]

/-! ### Flexible wages: `u ≡ uⁿ` (p. 206) -/

/-- Galí (2015), eq. (13) of Chapter 6, p. 169 (restated): the recursive wage-setting rule
`w*_{t+1} = βθ_w E_{t+1} w*_{t+2} + (1 − βθ_w)(w_{t+1} − (1 + ε_wφ)⁻¹ μ̂^w_{t+1})`. -/
def ResetRule (β θ ε φ : ℝ) (wstar w muhat : ℕ → Ω → ℝ) : Prop :=
  ∀ t, wstar (t + 1) = (β * θ) • 𝔼.E (t + 1) (wstar (t + 2)) +
    (1 - β * θ) • (w (t + 1) - (1 + ε * φ)⁻¹ • muhat (t + 1))

/-- Galí (2015), eq. (14) of Chapter 6, p. 169 (restated): the wage index law of motion
`w_{t+1} = θ_w w_t + (1 − θ_w) w*_{t+1}`. -/
def IndexLaw (θ : ℝ) (w wstar : ℕ → Ω → ℝ) : Prop :=
  ∀ t, w (t + 1) = θ • w t + (1 - θ) • wstar (t + 1)

/-- Galí (2015), p. 206 (**flexible wages**): with `θ_w = 0` (every wage reset every period),
`1 + ε_wφ ≠ 0` and the index law, the wage-setting rule holds iff the markup gap is
identically zero, `μ̂^w_{t+1} = 0` for all `t`. -/
theorem flexible_iff {β ε φ : ℝ} (hεφ : 1 + ε * φ ≠ 0) {wstar w muhat : ℕ → Ω → ℝ}
    (h14 : IndexLaw 0 w wstar) :
    ResetRule 𝔼 β 0 ε φ wstar w muhat ↔ ∀ t, muhat (t + 1) = 0 := by
  have hw : ∀ t, w (t + 1) = wstar (t + 1) := fun t => by
    have := h14 t
    simpa using this
  have hinv : (1 + ε * φ)⁻¹ ≠ 0 := inv_ne_zero hεφ
  unfold ResetRule
  simp only [mul_zero, zero_smul, sub_zero, one_smul, zero_add]
  constructor
  · intro h t
    have e := h t
    rw [hw t] at e
    have e2 : (1 + ε * φ)⁻¹ • muhat (t + 1) = 0 := sub_eq_self.mp e.symm
    exact (smul_eq_zero.mp e2).resolve_left hinv
  · intro h t
    rw [h t, smul_zero, sub_zero, hw t]

/-- Galí (2015), p. 206 (**with flexible wages unemployment equals its natural rate**): with
`θ_w = 0`, the index law and the wage-setting rule, and (8) `μ^w_t = φ u_t` with
`μ̂^w_t = μ^w_t − μ^w`, the unemployment rate is `u_{t+1} = uⁿ` at every date (`φ ≠ 0`).
Conversely `u ≡ uⁿ` makes the wage-setting rule hold. -/
theorem flexible_unemployment_constant {β ε φ μw : ℝ} (hφ : φ ≠ 0) (hεφ : 1 + ε * φ ≠ 0)
    {wstar w u muW : ℕ → Ω → ℝ} (h14 : IndexLaw 0 w wstar) (h8 : ∀ t, muW t = φ • u t) :
    ResetRule 𝔼 β 0 ε φ wstar w (fun t => muW t - fun _ => μw) ↔
      ∀ t, u (t + 1) = fun _ => natRate μw φ := by
  rw [flexible_iff 𝔼 hεφ h14]
  refine forall_congr' fun t => ?_
  rw [h8 (t + 1)]
  constructor
  · intro h
    funext x
    have e := congrFun h x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e
    exact (natRate_eq hφ).mp (by linarith)
  · intro h
    funext x
    have e := congrFun h x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [e, natRate]
    field_simp
    ring

/-- Galí (2015), p. 206 (**unemployment fluctuations require nominal wage rigidity**): if the
wage-setting rule and index law hold with stickiness `θ_w`, (8) holds, and at some date the
unemployment rate differs from its natural rate, then `θ_w ≠ 0`. -/
theorem fluctuations_require_rigidity {β θ ε φ μw : ℝ} (hφ : φ ≠ 0) (hεφ : 1 + ε * φ ≠ 0)
    {wstar w u muW : ℕ → Ω → ℝ} (h14 : IndexLaw θ w wstar) (h8 : ∀ t, muW t = φ • u t)
    (h13 : ResetRule 𝔼 β θ ε φ wstar w (fun t => muW t - fun _ => μw))
    (hdev : ∃ t, u (t + 1) ≠ fun _ => natRate μw φ) : θ ≠ 0 := by
  rintro rfl
  obtain ⟨t, ht⟩ := hdev
  exact ht (((flexible_unemployment_constant 𝔼 hφ hεφ h14 h8).mp h13) t)

/-- Galí (2015), pp. 206–207 (**with sticky wages any bounded unemployment gap is possible**):
for `0 ≤ β < 1` and any bounded adapted path `u` (any `λ_w`, `φ`), the wage Phillips curve (11)
has exactly one bounded wage-inflation solution, the forward sum
`π^w_t = −λ_w φ ∑_k β^k E_t (u_{t+k} − uⁿ)`; so (11) by itself does not pin `u` to `uⁿ`. -/
theorem sticky_unemployment_gap_consistent {β lamW φ un M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {u : ℕ → Ω → ℝ} (hu : ∀ t x, |u t x| ≤ M) (hua : 𝔼.Adapted u) :
    ∃! pw : ℕ → Ω → ℝ, BoundedProc pw ∧ WagePhillips 𝔼 β lamW φ un pw u := by
  set g : ℕ → Ω → ℝ := fun t => -((lamW * φ) • (u t - fun _ => un))
  have hg : ∀ t x, |g t x| ≤ |lamW| * |φ| * (M + |un|) := fun t x => by
    simp only [g, Pi.neg_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_neg, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    exact (abs_sub _ _).trans (by linarith [hu t x])
  have hga : 𝔼.Adapted g := fun t => by
    simp only [g, map_neg, map_smul, map_sub, hua t, 𝔼.const]
  have heq : ∀ pw : ℕ → Ω → ℝ, WagePhillips 𝔼 β lamW φ un pw u ↔
      ∀ t, pw t = β • 𝔼.E t (pw (t + 1)) + g t := fun pw => by
    unfold WagePhillips
    simp only [g, sub_eq_add_neg]
  refine ⟨𝔼.forwardSeries β g, ⟨𝔼.forwardSeries_bounded hβ0 hβ1 hg,
    (heq _).mpr fun t => 𝔼.forwardSeries_solves hβ0 hβ1 hg hga t⟩, ?_⟩
  rintro pw ⟨hb, hpw⟩
  exact 𝔼.eq_forwardSeries hβ0 hβ1 hg hga ((heq pw).mp hpw) hb

end Gali.Unemployment.UnemploymentDef
