/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# The dispersion terms behind (4.10) are second order

Woodford (2003), *Interest and Prices*, Chapter 3, §4.1, pp. 222–225: the log MRS of the
supplier of labour type `j` "can be written in the form `log v_t + ν log(h_t(j)/H_t)`, where
`v_t` is the geometric average of the MRS across different types of labor" (p. 223), and (4.10)
(p. 224) gives `v̂_t` from aggregate output through the hours `f⁻¹(Y/A)` needed to produce it.
Both steps drop dispersion terms: the geometric mean of the MRS is not the MRS at the CES labour
aggregate `H_t` of (4.1) when hours differ across types (wage dispersion), and `H_t` is not
`f⁻¹(Y_t/A_t)` when output differs across goods (price dispersion). The book does not discuss
them; its log-linear claims say they do not matter to first order. This module makes that
precise, with types forming any probability space `(J, m)` (the book's `[0, 1]`) and
log-deviations bounded by `B`:

* `log_integral_exp_bounds`: `0 ≤ log ∫ e^{x e} − x ∫ e ≤ x² B²` for `|x| B ≤ 1` — the
  dispersion functional is nonnegative and quadratic.
* `log_ces_eq`: the log of the CES aggregate `(∫ hʳ)^{1/r}` of `h = H̄ e^{s e}`.
* `logMRS_type_eq`: with isoelastic disutility (`log v_h(h) = log k + ν log h`, the
  case in which the book's `ν log(h_t(j)/H_t)` is exact), the type-`j` log MRS is
  `log v_t + ν log(h_t(j)/H_t) + ν D_h`, `D_h = log H_t − ∫ log h_t(j) dj`, and
  `hoursGap_bounds`: `0 ≤ D_h ≤ r s² B²`.
* `outputGap_bounds`: with isoelastic technology `h = (y/A)^φ`, the labour aggregate
  `H = ∫ (y_i/A)^φ di` exceeds `(Y/A)^φ` by `D_y` with `−φρ s² B² ≤ D_y ≤ φ² s² B²` (`ρ` the CES
  exponent of (1.2)).
* `logv_decomposition`: `log v_t = log k − log u_c + νφ(log Y_t − log A_t) + ν D_y − ν D_h` —
  the exact counterpart of (4.10)'s first-order relation.
* `hasDerivAt_hoursGap`, `hasDerivAt_outputGap`: both gaps have derivative `0` along any
  dispersion perturbation, so they drop out of the log-linearisation (4.10).
-/

namespace Woodford.NominalRigidities.TidyR5Dispersion

open MeasureTheory Filter Topology Asymptotics

variable {J : Type*} [MeasurableSpace J] (m : Measure J) [IsProbabilityMeasure m]

/-- Woodford (2003), §4.1, p. 223 (the dispersion functional): `D(x) = log ∫ e^{x e} dm − x ∫ e dm`
for a log-deviation profile `e` across types. -/
noncomputable def dispFn (e : J → ℝ) (x : ℝ) : ℝ :=
  Real.log (∫ j, Real.exp (x * e j) ∂m) - x * ∫ j, e j ∂m

omit [IsProbabilityMeasure m] in
/-- Woodford (2003), §4.1: `e^{x e}` is integrable for a bounded measurable profile `e`. -/
theorem integrable_exp_mul [IsFiniteMeasure m] {e : J → ℝ} (he : AEStronglyMeasurable e m)
    {B : ℝ} (hB : ∀ j, |e j| ≤ B) (x : ℝ) : Integrable (fun j => Real.exp (x * e j)) m := by
  refine Integrable.of_bound (Real.continuous_exp.comp_aestronglyMeasurable
    (he.const_mul x)) (Real.exp (|x| * B)) (Eventually.of_forall fun j => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.mpr ((le_abs_self _).trans ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hB j) (abs_nonneg x)

omit [IsProbabilityMeasure m] in
/-- Woodford (2003), §4.1: a bounded measurable profile is integrable. -/
theorem integrable_of_bdd [IsFiniteMeasure m] {e : J → ℝ} (he : AEStronglyMeasurable e m)
    {B : ℝ} (hB : ∀ j, |e j| ≤ B) : Integrable e m :=
  Integrable.of_bound he B (Eventually.of_forall fun j => by rw [Real.norm_eq_abs]; exact hB j)

/-- Woodford (2003), §4.1, pp. 223–224 (**the dispersion terms are nonnegative and quadratic**):
for a measurable profile `|e| ≤ B` and `|x| B ≤ 1`,
`0 ≤ log ∫ e^{x e} − x ∫ e ≤ x² B²`. -/
theorem log_integral_exp_bounds {e : J → ℝ} (he : AEStronglyMeasurable e m) {B : ℝ}
    (hB : ∀ j, |e j| ≤ B) {x : ℝ} (hx : |x| * B ≤ 1) :
    0 ≤ dispFn m e x ∧ dispFn m e x ≤ x ^ 2 * B ^ 2 := by
  have hI := integrable_exp_mul m he hB x
  have hei := integrable_of_bdd m he hB
  set μe := ∫ j, e j ∂m
  set I := ∫ j, Real.exp (x * e j) ∂m
  have hIpos : 0 < I := integral_exp_pos hI
  constructor
  · -- Jensen through `e^y ≥ 1 + y`
    have hlow : Real.exp (x * μe) ≤ I := by
      have h1 : ∀ j, Real.exp (x * μe) * (1 + (x * e j - x * μe)) ≤ Real.exp (x * e j) := by
        intro j
        have := Real.add_one_le_exp (x * e j - x * μe)
        rw [Real.exp_sub] at this
        have hp := Real.exp_pos (x * μe)
        rw [le_div_iff₀ hp] at this
        linarith
      have i1 : Integrable (fun j => x * e j - x * μe) m :=
        (hei.const_mul x).sub (integrable_const _)
      have h2 : ∫ j, Real.exp (x * μe) * (1 + (x * e j - x * μe)) ∂m = Real.exp (x * μe) := by
        rw [integral_const_mul, integral_add (integrable_const _) i1,
          integral_sub (hei.const_mul x) (integrable_const _), integral_const_mul]
        simp [μe]
      rw [← h2]
      exact integral_mono (((integrable_const 1).add i1).const_mul _) hI h1
    have := Real.log_le_log (Real.exp_pos _) hlow
    rw [Real.log_exp] at this
    unfold dispFn
    linarith
  · -- `e^y ≤ 1 + y + y²` for `|y| ≤ 1`
    have hup : I ≤ 1 + x * μe + x ^ 2 * B ^ 2 := by
      have h1 : ∀ j, Real.exp (x * e j) ≤ 1 + x * e j + x ^ 2 * B ^ 2 := by
        intro j
        have hy : |x * e j| ≤ 1 := by
          rw [abs_mul]
          exact (mul_le_mul_of_nonneg_left (hB j) (abs_nonneg x)).trans hx
        have h := Real.abs_exp_sub_one_sub_id_le hy
        have hsq : (x * e j) ^ 2 ≤ x ^ 2 * B ^ 2 := by
          rw [mul_pow]
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg x)
          have := hB j
          have h0 : 0 ≤ |e j| := abs_nonneg _
          nlinarith [sq_abs (e j)]
        have := (abs_le.mp h).2
        linarith
      have i1 : Integrable (fun j => 1 + x * e j) m := (integrable_const _).add (hei.const_mul x)
      have h2 : ∫ j, (1 + x * e j + x ^ 2 * B ^ 2) ∂m = 1 + x * μe + x ^ 2 * B ^ 2 := by
        rw [integral_add i1 (integrable_const _),
          integral_add (integrable_const _) (hei.const_mul x), integral_const_mul]
        simp [μe]
      rw [← h2]
      exact integral_mono hI (i1.add (integrable_const _)) h1
    have := Real.log_le_sub_one_of_pos hIpos
    unfold dispFn
    linarith

omit [IsProbabilityMeasure m] in
/-- Woodford (2003), §4.1, eq. (4.1), p. 221 (the CES labour aggregate in logs): for hours
`h_j = H̄ e^{s e_j}` and `r ≠ 0`, `log (∫ h_jʳ dj)^{1/r} = log H̄ + r⁻¹ log ∫ e^{r s e_j} dj`. -/
theorem log_ces_eq {e : J → ℝ} {Hbar : ℝ} (hH : 0 < Hbar) {r : ℝ} (hr : r ≠ 0) (s : ℝ)
    (hpos : 0 < ∫ j, Real.exp (r * s * e j) ∂m) :
    Real.log ((∫ j, (Hbar * Real.exp (s * e j)) ^ r ∂m) ^ (1 / r))
      = Real.log Hbar + r⁻¹ * Real.log (∫ j, Real.exp (r * s * e j) ∂m) := by
  have hpt : ∀ j, (Hbar * Real.exp (s * e j)) ^ r = Hbar ^ r * Real.exp (r * s * e j) := by
    intro j
    rw [Real.mul_rpow hH.le (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2
    ring
  simp_rw [hpt]
  rw [integral_const_mul, Real.log_rpow (mul_pos (Real.rpow_pos_of_pos hH r) hpos),
    Real.log_mul (Real.rpow_pos_of_pos hH r).ne' hpos.ne', Real.log_rpow hH]
  field_simp

/-- Woodford (2003), §4.1, p. 223 (**the hours-dispersion term**):
`D_h = log H − ∫ log h_j dj` for `h_j = H̄ e^{s e_j}` and the CES aggregate `H` of (4.1) with
exponent `r = (θ_w − 1)/θ_w`, written `r⁻¹ D(r s)`. -/
noncomputable def hoursGap (e : J → ℝ) (r s : ℝ) : ℝ := r⁻¹ * dispFn m e (r * s)

/-- Woodford (2003), §4.1, p. 223: `D_h` is the gap between the log CES aggregate and the
average log hours, `log H − ∫ log h_j = r⁻¹ log ∫ e^{r s e} − s ∫ e`. -/
theorem hoursGap_eq {e : J → ℝ} {Hbar : ℝ} (hH : 0 < Hbar) {r : ℝ} (hr : r ≠ 0) (s : ℝ)
    (hei : Integrable e m) :
    (Real.log Hbar + r⁻¹ * Real.log (∫ j, Real.exp (r * s * e j) ∂m))
      - ∫ j, Real.log (Hbar * Real.exp (s * e j)) ∂m = hoursGap m e r s := by
  have hpt : ∀ j, Real.log (Hbar * Real.exp (s * e j)) = Real.log Hbar + s * e j := by
    intro j
    rw [Real.log_mul hH.ne' (Real.exp_pos _).ne', Real.log_exp]
  simp_rw [hpt]
  rw [integral_add (integrable_const _) (hei.const_mul s), integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  unfold hoursGap dispFn
  field_simp
  ring

/-- Woodford (2003), §4.1, p. 223 (**`D_h` is nonnegative and second order**): for
`0 < r ≤ 1` and `|r s| B ≤ 1`, `0 ≤ D_h ≤ r s² B²`. -/
theorem hoursGap_bounds {e : J → ℝ} (he : AEStronglyMeasurable e m) {B : ℝ}
    (hB : ∀ j, |e j| ≤ B) {r s : ℝ} (hr : 0 < r) (hx : |r * s| * B ≤ 1) :
    0 ≤ hoursGap m e r s ∧ hoursGap m e r s ≤ r * s ^ 2 * B ^ 2 := by
  obtain ⟨h0, h1⟩ := log_integral_exp_bounds m he hB hx
  unfold hoursGap
  refine ⟨mul_nonneg (inv_nonneg.mpr hr.le) h0, ?_⟩
  calc r⁻¹ * dispFn m e (r * s) ≤ r⁻¹ * ((r * s) ^ 2 * B ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hr.le)
    _ = r * s ^ 2 * B ^ 2 := by field_simp

/-- Woodford (2003), §4.1, p. 223 (**the book's form of the type-`j` log MRS, made exact**):
with isoelastic disutility, `log MRS_j = k₀ + ν log h_j` (`k₀ = log k − log u_c`), the geometric
average `log v = ∫ log MRS_j dj` and any `log H`,
`log MRS_j = log v + ν (log h_j − log H) + ν (log H − ∫ log h)`. The book's
`log v_t + ν log(h_t(j)/H_t)` is therefore exact up to `ν D_h` (`hoursGap_eq`). -/
theorem logMRS_type_eq {h : J → ℝ} (hi : Integrable (fun j => Real.log (h j)) m)
    (k0 ν logH : ℝ) (j : J) :
    k0 + ν * Real.log (h j) = (∫ i, (k0 + ν * Real.log (h i)) ∂m)
      + ν * (Real.log (h j) - logH) + ν * (logH - ∫ i, Real.log (h i) ∂m) := by
  rw [integral_add (integrable_const _) (hi.const_mul ν), integral_const_mul, integral_const]
  simp only [smul_eq_mul, probReal_univ, one_mul]
  ring

/-- Woodford (2003), §4.1, p. 224 (**the output-dispersion term**): with output
`y_i = Ȳ e^{s e_i}`, the Dixit–Stiglitz aggregate `Y` of (1.2) with exponent
`ρ = (θ − 1)/θ`, and isoelastic labour requirements `(y_i/A)^φ`,
`D_y = log ∫ (y_i/A)^φ di − φ (log Y − log A) = D(φ s) − (φ/ρ) D(ρ s)`. -/
noncomputable def outputGap (e : J → ℝ) (φ ρ s : ℝ) : ℝ :=
  dispFn m e (φ * s) - φ / ρ * dispFn m e (ρ * s)

omit [IsProbabilityMeasure m] in
/-- Woodford (2003), §4.1, p. 224: `D_y` is the gap between log labour input
`log ∫ (y_i/A)^φ di` and `φ (log Y − log A)`, with `log Y = log Ȳ + ρ⁻¹ log ∫ e^{ρ s e}`. -/
theorem outputGap_eq {e : J → ℝ} {Ybar A : ℝ} (hY : 0 < Ybar) (hA : 0 < A) {φ ρ : ℝ}
    (hρ : ρ ≠ 0) (s : ℝ) (hpos : 0 < ∫ j, Real.exp (φ * s * e j) ∂m) :
    Real.log (∫ j, (Ybar * Real.exp (s * e j) / A) ^ φ ∂m)
      - φ * ((Real.log Ybar + ρ⁻¹ * Real.log (∫ j, Real.exp (ρ * s * e j) ∂m)) - Real.log A)
      = outputGap m e φ ρ s := by
  have hpt : ∀ j, (Ybar * Real.exp (s * e j) / A) ^ φ
      = (Ybar / A) ^ φ * Real.exp (φ * s * e j) := by
    intro j
    rw [mul_div_right_comm, Real.mul_rpow (div_pos hY hA).le (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2
    ring
  simp_rw [hpt]
  have hYA := div_pos hY hA
  rw [integral_const_mul, Real.log_mul (Real.rpow_pos_of_pos hYA φ).ne' hpos.ne',
    Real.log_rpow hYA, Real.log_div hY.ne' hA.ne']
  unfold outputGap dispFn
  simp_rw [mul_assoc]
  field_simp
  ring

/-- Woodford (2003), §4.1, p. 224 (**`D_y` is second order**): for `φ > 0`, `ρ > 0`,
`|φ s| B ≤ 1` and `|ρ s| B ≤ 1`, `−φρ s² B² ≤ D_y ≤ φ² s² B²`. -/
theorem outputGap_bounds {e : J → ℝ} (he : AEStronglyMeasurable e m) {B : ℝ}
    (hB : ∀ j, |e j| ≤ B) {φ ρ s : ℝ} (hφ : 0 < φ) (hρ : 0 < ρ) (hx1 : |φ * s| * B ≤ 1)
    (hx2 : |ρ * s| * B ≤ 1) :
    -(φ * ρ * s ^ 2 * B ^ 2) ≤ outputGap m e φ ρ s ∧
      outputGap m e φ ρ s ≤ φ ^ 2 * s ^ 2 * B ^ 2 := by
  obtain ⟨a0, a1⟩ := log_integral_exp_bounds m he hB hx1
  obtain ⟨b0, b1⟩ := log_integral_exp_bounds m he hB hx2
  have hc : 0 ≤ φ / ρ := (div_pos hφ hρ).le
  unfold outputGap
  constructor
  · have : φ / ρ * dispFn m e (ρ * s) ≤ φ / ρ * ((ρ * s) ^ 2 * B ^ 2) :=
      mul_le_mul_of_nonneg_left b1 hc
    have e1 : φ / ρ * ((ρ * s) ^ 2 * B ^ 2) = φ * ρ * s ^ 2 * B ^ 2 := by field_simp
    linarith
  · have : 0 ≤ φ / ρ * dispFn m e (ρ * s) := mul_nonneg hc b0
    have e1 : (φ * s) ^ 2 * B ^ 2 = φ ^ 2 * s ^ 2 * B ^ 2 := by ring
    linarith

/-- Woodford (2003), eq. (4.10), p. 224 (**the exact geometric-average MRS**): with isoelastic
disutility (`log MRS_j = log k − log u_c + ν log h_j`), if the labour market clears
(`log H = log ∫ (y_i/A)^φ di` for the CES aggregate `H` of the hours `h_j`), then
`log v = log k − log u_c + νφ (log Y − log A) + ν D_y − ν D_h`, where
`D_h = log H − ∫ log h_j` and `D_y = log H − φ(log Y − log A)`: (4.10)'s first-order relation
plus the two dispersion terms. -/
theorem logv_decomposition {h : J → ℝ}
    (hi : Integrable (fun j => Real.log (h j)) m) (logk loguc ν φ logH logY logA : ℝ) :
    ∫ j, (logk - loguc + ν * Real.log (h j)) ∂m
      = logk - loguc + ν * φ * (logY - logA) + ν * (logH - φ * (logY - logA))
        - ν * (logH - ∫ j, Real.log (h j) ∂m) := by
  rw [integral_add (integrable_const _) (hi.const_mul ν), integral_const_mul, integral_const]
  simp only [smul_eq_mul, probReal_univ, one_mul]
  ring

/-! ### Both gaps drop out of the log-linearisation -/

/-- Woodford (2003), §4.1 (second-order terms have zero derivative): if `F 0 = 0` and
`|F s| ≤ K s²` for `|s| ≤ δ`, `δ > 0`, then `F` has derivative `0` at `0`. -/
theorem hasDerivAt_zero_of_sq_bound {F : ℝ → ℝ} (h0 : F 0 = 0) {δ K : ℝ} (hδ : 0 < δ)
    (hb : ∀ s, |s| ≤ δ → |F s| ≤ K * s ^ 2) : HasDerivAt F 0 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, h0, sub_zero, smul_zero]
  have hO : F =O[𝓝 0] fun s : ℝ => s ^ 2 := by
    refine IsBigO.of_bound K ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) hδ] with s hs
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hs
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg s)]
    exact hb s hs
  exact hO.trans_isLittleO (isLittleO_pow_id (by norm_num))

/-- Woodford (2003), §4.1, p. 223 and (4.10), p. 224 (**hours dispersion drops out to first
order**): along `h_j = H̄ e^{s e_j}`, `s ↦ D_h(s)` has derivative `0` at `s = 0`. -/
theorem hasDerivAt_hoursGap {e : J → ℝ} (he : AEStronglyMeasurable e m) {B : ℝ} (hB0 : 0 < B)
    (hB : ∀ j, |e j| ≤ B) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => hoursGap m e r s) 0 0 := by
  refine hasDerivAt_zero_of_sq_bound ?_ (δ := (r * B)⁻¹) (K := r * B ^ 2)
    (inv_pos.mpr (mul_pos hr hB0)) fun s hs => ?_
  · simp [hoursGap, dispFn]
  · have hx : |r * s| * B ≤ 1 := by
      rw [abs_mul, abs_of_pos hr]
      have h' := mul_le_mul_of_nonneg_left hs (mul_pos hr hB0).le
      rw [mul_inv_cancel₀ (mul_pos hr hB0).ne'] at h'
      nlinarith
    obtain ⟨h0, h1⟩ := hoursGap_bounds m he hB hr hx
    rw [abs_of_nonneg h0]
    linarith

/-- Woodford (2003), (4.10), p. 224 (**output dispersion drops out to first order**): along
`y_i = Ȳ e^{s e_i}`, `s ↦ D_y(s)` has derivative `0` at `s = 0`. -/
theorem hasDerivAt_outputGap {e : J → ℝ} (he : AEStronglyMeasurable e m) {B : ℝ} (hB0 : 0 < B)
    (hB : ∀ j, |e j| ≤ B) {φ ρ : ℝ} (hφ : 0 < φ) (hρ : 0 < ρ) :
    HasDerivAt (fun s => outputGap m e φ ρ s) 0 0 := by
  set M := max φ ρ
  have hM : 0 < M := lt_max_of_lt_left hφ
  refine hasDerivAt_zero_of_sq_bound ?_ (δ := (M * B)⁻¹) (K := (φ ^ 2 + φ * ρ) * B ^ 2)
    (inv_pos.mpr (mul_pos hM hB0)) fun s hs => ?_
  · simp [outputGap, dispFn]
  · have hs' := mul_le_mul_of_nonneg_left hs (mul_pos hM hB0).le
    rw [mul_inv_cancel₀ (mul_pos hM hB0).ne'] at hs'
    have hx1 : |φ * s| * B ≤ 1 := by
      rw [abs_mul, abs_of_pos hφ]
      have : φ ≤ M := le_max_left _ _
      nlinarith [abs_nonneg s]
    have hx2 : |ρ * s| * B ≤ 1 := by
      rw [abs_mul, abs_of_pos hρ]
      have : ρ ≤ M := le_max_right _ _
      nlinarith [abs_nonneg s]
    obtain ⟨h0, h1⟩ := outputGap_bounds m he hB hφ hρ hx1 hx2
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg s, sq_nonneg B, mul_pos hφ hρ]

end Woodford.NominalRigidities.TidyR5Dispersion
