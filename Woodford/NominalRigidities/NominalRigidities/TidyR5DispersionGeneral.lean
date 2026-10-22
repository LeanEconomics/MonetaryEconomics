/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.TidyR5Dispersion
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# The dispersion terms behind (4.10) are second order for general preferences and technology

Woodford (2003), *Interest and Prices*, Chapter 3, §4.1, pp. 222–225. `TidyR5Dispersion` treats
isoelastic disutility and technology. Here the disutility of work and the production function
are general. Types form any probability space `(J, m)`; log-deviations `e` are measurable with
`|e| ≤ B`, and the dispersion parameter is `s`.

* **Hours dispersion.** `ℓ(x) = log v_h(eˣ)` (the log marginal disutility at log hours `x`).
  The log of the geometric-average MRS minus the log MRS at the CES aggregate `H` of (4.1) is
  `hoursGapGen(s) = ∫ ℓ(L + s e_j) dj − ℓ(log H(s))`, with
  `log H(s) = L + r⁻¹ log ∫ e^{r s e}` (`TidyR5Dispersion.log_ces_eq`).
* **Output dispersion.** `χ(x) > 0` is the labour needed to produce log output `x` (in the book,
  `f⁻¹(eˣ/A)`). With output `L + s e_i` across goods and the Dixit–Stiglitz aggregate
  `log Y(s) = L + ρ⁻¹ log ∫ e^{ρ s e}`, the gap between log labour input and the labour (4.10)
  uses is `outputGapGen(s) = log ∫ χ(L + s e_i) di − log χ(log Y(s))`.

Hypotheses: `ℓ` and `χ` are differentiable with derivatives `ℓ'` and `χ'` that are Lipschitz
(constant `C`) on a neighbourhood of `L` (for instance, `C²` functions).

* `quad_remainder`: `|φ(L + y) − φ(L) − φ'(L) y| ≤ C y²` (mean value theorem).
* `integral_quad_remainder`: the same for `∫ φ(L + s e)`.
* `hoursGapGen_sq_bound`, `outputGapGen_sq_bound`: both gaps are `O(s²)`.
* `hasDerivAt_hoursGapGen`, `hasDerivAt_outputGapGen`: both have derivative `0` at `s = 0`, so
  they drop out of the log-linear relation (4.10).
-/

namespace Woodford.NominalRigidities.TidyR5DispersionGeneral

open MeasureTheory Filter Topology TidyR5Dispersion

/-- Woodford (2003), §4.1 (the second-order remainder used for (4.10)): if `φ` has derivative
`φ'` everywhere and `|φ'(x) − φ'(L)| ≤ C |x − L|` for `|x − L| ≤ δ`, then for `|y| ≤ δ`,
`|φ(L + y) − φ(L) − φ'(L) y| ≤ C y²`. -/
theorem quad_remainder {φ φ' : ℝ → ℝ} (hφ : ∀ x, HasDerivAt φ (φ' x) x) {L δ C : ℝ}
    (hC : 0 ≤ C) (hlip : ∀ x, |x - L| ≤ δ → |φ' x - φ' L| ≤ C * |x - L|) {y : ℝ} (hy : |y| ≤ δ) :
    |φ (L + y) - φ L - φ' L * y| ≤ C * y ^ 2 := by
  set g : ℝ → ℝ := fun u => φ (L + u) - φ L - φ' L * u
  have hg : ∀ u, HasDerivAt g (φ' (L + u) - φ' L) u := by
    intro u
    have h1 : HasDerivAt (fun u => φ (L + u)) (φ' (L + u)) u :=
      HasDerivAt.comp_const_add L u (hφ (L + u))
    have h2 : HasDerivAt (fun u => φ' L * u) (φ' L) u := by
      simpa using (hasDerivAt_id u).const_mul (φ' L)
    exact HasDerivAt.sub (HasDerivAt.sub_const (φ L) h1) h2
  have hmem : ∀ u ∈ Set.uIcc 0 y, |u| ≤ |y| := by
    intro u hu
    rcases Set.mem_uIcc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
    · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith
  have hbound : ∀ u ∈ Set.uIcc 0 y, ‖φ' (L + u) - φ' L‖ ≤ C * |y| := by
    intro u hu
    have hu' := hmem u hu
    have h := hlip (L + u) (by rw [add_sub_cancel_left]; exact hu'.trans hy)
    rw [add_sub_cancel_left] at h
    rw [Real.norm_eq_abs]
    exact h.trans (mul_le_mul_of_nonneg_left hu' hC)
  have hmv := (convex_uIcc (0 : ℝ) y).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (hg u).hasDerivWithinAt) hbound Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [g, add_zero, mul_zero, sub_self, sub_zero, Real.norm_eq_abs] at hmv
  calc |φ (L + y) - φ L - φ' L * y| ≤ C * |y| * |y| := hmv
    _ = C * y ^ 2 := by rw [mul_assoc, abs_mul_abs_self, sq]

variable {J : Type*} [MeasurableSpace J] (m : Measure J) [IsProbabilityMeasure m]

/-- Woodford (2003), §4.1: under the hypotheses of `quad_remainder` and `|s| B ≤ δ`, the map
`j ↦ φ(L + s e_j)` is integrable. -/
theorem integrable_comp {φ φ' : ℝ → ℝ} (hφ : ∀ x, HasDerivAt φ (φ' x) x) {L δ C : ℝ}
    (hC : 0 ≤ C) (hlip : ∀ x, |x - L| ≤ δ → |φ' x - φ' L| ≤ C * |x - L|) {e : J → ℝ}
    (he : AEStronglyMeasurable e m) {B : ℝ} (hB : ∀ j, |e j| ≤ B) {s : ℝ} (hs : |s| * B ≤ δ) :
    Integrable (fun j => φ (L + s * e j)) m := by
  have hcont : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hφ x).continuousAt
  refine Integrable.of_bound (hcont.comp_aestronglyMeasurable (he.const_mul s |>.const_add L))
    (|φ L| + |φ' L| * (|s| * B) + C * (s * B) ^ 2) (Eventually.of_forall fun j => ?_)
  have hy : |s * e j| ≤ |s| * B := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB j) (abs_nonneg s)
  have hq := quad_remainder hφ hC hlip (hy.trans hs)
  have hC : C * (s * e j) ^ 2 ≤ C * (s * B) ^ 2 := by
    refine mul_le_mul_of_nonneg_left ?_ hC
    rw [mul_pow, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg s)
    have := hB j
    nlinarith [sq_abs (e j), abs_nonneg (e j)]
  rw [Real.norm_eq_abs]
  have h1 : |φ' L * (s * e j)| ≤ |φ' L| * (|s| * B) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
  have := abs_sub_abs_le_abs_sub (φ (L + s * e j)) (φ L + φ' L * (s * e j))
  rw [show φ (L + s * e j) - (φ L + φ' L * (s * e j)) = φ (L + s * e j) - φ L - φ' L * (s * e j)
    by ring] at this
  have h2 := abs_add_le (φ L) (φ' L * (s * e j))
  linarith

/-- Woodford (2003), §4.1 (**averaging across types to second order**): under the hypotheses of
`quad_remainder`, for `|s| B ≤ δ`,
`|∫ φ(L + s e) − φ(L) − φ'(L) s ∫ e| ≤ C s² B²`. -/
theorem integral_quad_remainder {φ φ' : ℝ → ℝ} (hφ : ∀ x, HasDerivAt φ (φ' x) x) {L δ C : ℝ}
    (hC : 0 ≤ C) (hlip : ∀ x, |x - L| ≤ δ → |φ' x - φ' L| ≤ C * |x - L|) {e : J → ℝ}
    (he : AEStronglyMeasurable e m) {B : ℝ} (hB : ∀ j, |e j| ≤ B) {s : ℝ} (hs : |s| * B ≤ δ) :
    |∫ j, φ (L + s * e j) ∂m - φ L - φ' L * s * ∫ j, e j ∂m| ≤ C * s ^ 2 * B ^ 2 := by
  have hi := integrable_comp m hφ hC hlip he hB hs
  have hei := integrable_of_bdd m he hB
  have i1 : Integrable (fun j => φ (L + s * e j) - φ L) m := hi.sub (integrable_const _)
  have i2 : Integrable (fun j => φ' L * (s * e j)) m := (hei.const_mul s).const_mul _
  have heq : ∫ j, φ (L + s * e j) ∂m - φ L - φ' L * s * ∫ j, e j ∂m
      = ∫ j, (φ (L + s * e j) - φ L - φ' L * (s * e j)) ∂m := by
    rw [integral_sub i1 i2, integral_sub hi (integrable_const _), integral_const_mul,
      integral_const_mul, integral_const]
    simp only [smul_eq_mul, probReal_univ, one_mul]
    ring
  rw [heq, ← Real.norm_eq_abs]
  have h := norm_integral_le_of_norm_le_const (μ := m)
    (f := fun j => φ (L + s * e j) - φ L - φ' L * (s * e j)) (C := C * s ^ 2 * B ^ 2)
    (Eventually.of_forall fun j => by
      rw [Real.norm_eq_abs]
      have hy : |s * e j| ≤ |s| * B := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB j) (abs_nonneg s)
      refine (quad_remainder hφ hC hlip (hy.trans hs)).trans ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hC
      rw [mul_pow]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg s)
      have := hB j
      nlinarith [sq_abs (e j), abs_nonneg (e j)])
  simpa using h

/-- Woodford (2003), §4.1: the log CES aggregate in deviation from `L`,
`y(r, s) = r⁻¹ log ∫ e^{r s e}`, equals `s ∫ e + r⁻¹ D(r s)`. -/
noncomputable def cesDev (e : J → ℝ) (r s : ℝ) : ℝ :=
  r⁻¹ * Real.log (∫ j, Real.exp (r * s * e j) ∂m)

/-- Woodford (2003), §4.1: for `0 < r` and `|r s| B ≤ 1`, `|y(r, s) − s ∫ e| ≤ r s² B²`
and `|y(r, s)| ≤ |s| B + r s² B²`. -/
theorem cesDev_bounds {e : J → ℝ} (he : AEStronglyMeasurable e m) {B : ℝ}
    (hB : ∀ j, |e j| ≤ B) {r s : ℝ} (hr : 0 < r) (hx : |r * s| * B ≤ 1) :
    |cesDev m e r s - s * ∫ j, e j ∂m| ≤ r * s ^ 2 * B ^ 2 ∧
      |cesDev m e r s| ≤ |s| * B + r * s ^ 2 * B ^ 2 := by
  obtain ⟨h0, h1⟩ := hoursGap_bounds m he hB hr hx
  have heq : cesDev m e r s - s * ∫ j, e j ∂m = hoursGap m e r s := by
    unfold cesDev hoursGap dispFn
    field_simp
  have hfirst : |cesDev m e r s - s * ∫ j, e j ∂m| ≤ r * s ^ 2 * B ^ 2 := by
    rw [heq, abs_of_nonneg h0]; exact h1
  refine ⟨hfirst, ?_⟩
  have hint : |∫ j, e j ∂m| ≤ B := by
    have := norm_integral_le_of_norm_le_const (μ := m) (f := e) (C := B)
      (Eventually.of_forall fun j => by rw [Real.norm_eq_abs]; exact hB j)
    simpa using this
  have hse : |s * ∫ j, e j ∂m| ≤ |s| * B := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hint (abs_nonneg s)
  have := abs_sub_abs_le_abs_sub (cesDev m e r s) (s * ∫ j, e j ∂m)
  linarith

/-- Woodford (2003), §4.1, p. 223 (**the hours-dispersion gap, general disutility**):
`∫ ℓ(L + s e_j) dj − ℓ(L + y(r, s))`, the log geometric-average MRS minus the log MRS at the CES
labour aggregate, with `ℓ(x) = log v_h(eˣ)`. -/
noncomputable def hoursGapGen (ℓ : ℝ → ℝ) (L : ℝ) (e : J → ℝ) (r s : ℝ) : ℝ :=
  ∫ j, ℓ (L + s * e j) ∂m - ℓ (L + cesDev m e r s)

/-- Woodford (2003), §4.1, p. 223 (**the hours-dispersion gap is second order**): with
`ℓ` differentiable, `ℓ'` `C`-Lipschitz on `|x − L| ≤ δ`, `0 < r ≤ 1`, `B > 0`, and
`|s| ≤ min (δ/(2B)) (1/(rB))`, `|hoursGapGen(s)| ≤ (5C + |ℓ'(L)| r) B² s²`. -/
theorem hoursGapGen_sq_bound {ℓ ℓ' : ℝ → ℝ} (hℓ : ∀ x, HasDerivAt ℓ (ℓ' x) x) {L δ C : ℝ}
    (hC : 0 ≤ C) (hlip : ∀ x, |x - L| ≤ δ → |ℓ' x - ℓ' L| ≤ C * |x - L|) {e : J → ℝ}
    (he : AEStronglyMeasurable e m) {B : ℝ} (hB0 : 0 < B) (hB : ∀ j, |e j| ≤ B) {r : ℝ}
    (hr : 0 < r) {s : ℝ} (hs1 : |s| * B ≤ δ / 2) (hs2 : r * |s| * B ≤ 1) :
    |hoursGapGen m ℓ L e r s| ≤ (5 * C + |ℓ' L| * r) * B ^ 2 * s ^ 2 := by
  have hδ : 0 ≤ δ := by have := mul_nonneg (abs_nonneg s) hB0.le; linarith
  have hx : |r * s| * B ≤ 1 := by rw [abs_mul, abs_of_pos hr]; linarith
  obtain ⟨hd1, hd2⟩ := cesDev_bounds m he hB hr hx
  set y := cesDev m e r s
  set μe := ∫ j, e j ∂m
  have hsB : r * s ^ 2 * B ^ 2 ≤ |s| * B := by
    have : r * s ^ 2 * B ^ 2 = (r * |s| * B) * (|s| * B) := by
      rw [← sq_abs s]; ring
    rw [this]
    exact mul_le_of_le_one_left (by positivity) hs2
  have hy : |y| ≤ 2 * (|s| * B) := by linarith
  have hyδ : |y| ≤ δ := by linarith
  have h1 := integral_quad_remainder m hℓ hC hlip he hB (s := s) (by linarith)
  have h2 := quad_remainder hℓ hC hlip hyδ
  have hy2 : y ^ 2 ≤ 4 * (B ^ 2 * s ^ 2) := by
    have hyabs : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
    have e2 : (2 * (|s| * B)) ^ 2 = 4 * (B ^ 2 * s ^ 2) := by rw [← sq_abs s]; ring
    rw [hyabs, ← e2]
    exact pow_le_pow_left₀ (abs_nonneg y) hy 2
  have h3 : |ℓ' L * (s * μe - y)| ≤ |ℓ' L| * r * B ^ 2 * s ^ 2 := by
    rw [abs_mul, abs_sub_comm]
    calc |ℓ' L| * |y - s * μe| ≤ |ℓ' L| * (r * s ^ 2 * B ^ 2) :=
          mul_le_mul_of_nonneg_left hd1 (abs_nonneg _)
      _ = |ℓ' L| * r * B ^ 2 * s ^ 2 := by ring
  have hsplit : hoursGapGen m ℓ L e r s
      = (∫ j, ℓ (L + s * e j) ∂m - ℓ L - ℓ' L * s * μe)
        - (ℓ (L + y) - ℓ L - ℓ' L * y) + ℓ' L * (s * μe - y) := by
    unfold hoursGapGen; ring
  rw [hsplit]
  have hCy : C * y ^ 2 ≤ 4 * C * B ^ 2 * s ^ 2 :=
    calc C * y ^ 2 ≤ C * (4 * (B ^ 2 * s ^ 2)) := mul_le_mul_of_nonneg_left hy2 hC
      _ = 4 * C * B ^ 2 * s ^ 2 := by ring
  calc _ ≤ |∫ j, ℓ (L + s * e j) ∂m - ℓ L - ℓ' L * s * μe| + |ℓ (L + y) - ℓ L - ℓ' L * y|
        + |ℓ' L * (s * μe - y)| := by
        have := abs_add_le (∫ j, ℓ (L + s * e j) ∂m - ℓ L - ℓ' L * s * μe
          - (ℓ (L + y) - ℓ L - ℓ' L * y)) (ℓ' L * (s * μe - y))
        have := abs_sub (∫ j, ℓ (L + s * e j) ∂m - ℓ L - ℓ' L * s * μe)
          (ℓ (L + y) - ℓ L - ℓ' L * y)
        linarith
    _ ≤ C * s ^ 2 * B ^ 2 + 4 * C * B ^ 2 * s ^ 2 + |ℓ' L| * r * B ^ 2 * s ^ 2 := by
        linarith
    _ = (5 * C + |ℓ' L| * r) * B ^ 2 * s ^ 2 := by ring

/-- Woodford (2003), (4.10), p. 224 (**hours dispersion drops out to first order, general
disutility**): `s ↦ hoursGapGen(s)` has derivative `0` at `s = 0`. -/
theorem hasDerivAt_hoursGapGen {ℓ ℓ' : ℝ → ℝ} (hℓ : ∀ x, HasDerivAt ℓ (ℓ' x) x) {L δ C : ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hlip : ∀ x, |x - L| ≤ δ → |ℓ' x - ℓ' L| ≤ C * |x - L|)
    {e : J → ℝ} (he : AEStronglyMeasurable e m) {B : ℝ} (hB0 : 0 < B) (hB : ∀ j, |e j| ≤ B)
    {r : ℝ} (hr : 0 < r) : HasDerivAt (fun s => hoursGapGen m ℓ L e r s) 0 0 := by
  refine hasDerivAt_zero_of_sq_bound ?_ (δ := min (δ / (2 * B)) (1 / (r * B)))
    (K := (5 * C + |ℓ' L| * r) * B ^ 2) (lt_min (by positivity) (by positivity)) fun s hs => ?_
  · simp [hoursGapGen, cesDev]
  · have hs1 : |s| * B ≤ δ / 2 := by
      have := (hs.trans (min_le_left _ _))
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    have hs2 : r * |s| * B ≤ 1 := by
      have := (hs.trans (min_le_right _ _))
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    exact hoursGapGen_sq_bound m hℓ hC hlip he hB0 hB hr hs1 hs2

omit [IsProbabilityMeasure m] in
/-- Woodford (2003), §4.1 (a log bound): if `a, b ≥ c > 0` then `|log a − log b| ≤ |a − b|/c`. -/
theorem abs_log_sub_le {a b c : ℝ} (hc : 0 < c) (ha : c ≤ a) (hb : c ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / c := by
  have ha0 : 0 < a := lt_of_lt_of_le hc ha
  have hb0 : 0 < b := lt_of_lt_of_le hc hb
  have h1 : Real.log a - Real.log b ≤ (a - b) / b := by
    rw [← Real.log_div ha0.ne' hb0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
    rw [sub_div, div_self hb0.ne'] ; linarith
  have h2 : Real.log b - Real.log a ≤ (b - a) / a := by
    rw [← Real.log_div hb0.ne' ha0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    rw [sub_div, div_self ha0.ne'] ; linarith
  have k1 : (a - b) / b ≤ |a - b| / c := by
    rcases le_total 0 (a - b) with h | h
    · rw [abs_of_nonneg h]; exact div_le_div_of_nonneg_left h hc hb
    · have : (a - b) / b ≤ 0 := div_nonpos_of_nonpos_of_nonneg h hb0.le
      exact this.trans (div_nonneg (abs_nonneg _) hc.le)
  have k2 : (b - a) / a ≤ |a - b| / c := by
    rcases le_total 0 (b - a) with h | h
    · rw [abs_sub_comm, abs_of_nonneg h]; exact div_le_div_of_nonneg_left h hc ha
    · have : (b - a) / a ≤ 0 := div_nonpos_of_nonpos_of_nonneg h ha0.le
      exact this.trans (div_nonneg (abs_nonneg _) hc.le)
  rw [abs_le]
  constructor <;> linarith

/-- Woodford (2003), §4.1, p. 224 (**the output-dispersion gap, general technology**):
`log ∫ χ(L + s e_i) di − log χ(L + y(ρ, s))`, log labour input minus the log labour needed for
the Dixit–Stiglitz aggregate, with `χ(x)` the labour required for log output `x`. -/
noncomputable def outputGapGen (χ : ℝ → ℝ) (L : ℝ) (e : J → ℝ) (ρ s : ℝ) : ℝ :=
  Real.log (∫ j, χ (L + s * e j) ∂m) - Real.log (χ (L + cesDev m e ρ s))

/-- Woodford (2003), §4.1, p. 224 (**the output-dispersion gap is second order**): with `χ`
differentiable, `χ(L) > 0`, `χ'` `C`-Lipschitz on `|x − L| ≤ δ`, `0 < ρ`, `B > 0`, and `|s|`
small (`|s| B ≤ δ/2`, `ρ|s|B ≤ 1`, `|s| ≤ 1`, `|s| Q ≤ χ(L)/4` with
`Q = 2|χ'(L)| B + 4 C B² + 1`), `|outputGapGen(s)| ≤ 2(5C + |χ'(L)| ρ) B² s² / χ(L)`. -/
theorem outputGapGen_sq_bound {χ χ' : ℝ → ℝ} (hχ : ∀ x, HasDerivAt χ (χ' x) x) {L δ C : ℝ}
    (hC : 0 ≤ C) (hlip : ∀ x, |x - L| ≤ δ → |χ' x - χ' L| ≤ C * |x - L|) (hχL : 0 < χ L)
    {e : J → ℝ} (he : AEStronglyMeasurable e m) {B : ℝ} (hB0 : 0 < B) (hB : ∀ j, |e j| ≤ B)
    {ρ : ℝ} (hρ : 0 < ρ) {s : ℝ} (hs1 : |s| * B ≤ δ / 2) (hs2 : ρ * |s| * B ≤ 1)
    (hs3 : |s| ≤ 1) (hs4 : |s| * (2 * |χ' L| * B + 4 * C * B ^ 2 + 1) ≤ χ L / 4) :
    |outputGapGen m χ L e ρ s| ≤ 2 * (5 * C + |χ' L| * ρ) * B ^ 2 * s ^ 2 / χ L := by
  have hδ : 0 ≤ δ := by have := mul_nonneg (abs_nonneg s) hB0.le; linarith
  have hx : |ρ * s| * B ≤ 1 := by rw [abs_mul, abs_of_pos hρ]; linarith
  obtain ⟨hd1, hd2⟩ := cesDev_bounds m he hB hρ hx
  set y := cesDev m e ρ s
  set μe := ∫ j, e j ∂m
  set Φ := ∫ j, χ (L + s * e j) ∂m
  have hsB : ρ * s ^ 2 * B ^ 2 ≤ |s| * B := by
    have : ρ * s ^ 2 * B ^ 2 = (ρ * |s| * B) * (|s| * B) := by rw [← sq_abs s]; ring
    rw [this]; exact mul_le_of_le_one_left (by positivity) hs2
  have hy : |y| ≤ 2 * (|s| * B) := by linarith
  have hyδ : |y| ≤ δ := by linarith
  have h1 := integral_quad_remainder m hχ hC hlip he hB (s := s) (by linarith)
  have h2 := quad_remainder hχ hC hlip hyδ
  have hy2 : y ^ 2 ≤ 4 * (B ^ 2 * s ^ 2) := by
    have hyabs : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
    have e2 : (2 * (|s| * B)) ^ 2 = 4 * (B ^ 2 * s ^ 2) := by rw [← sq_abs s]; ring
    rw [hyabs, ← e2]
    exact pow_le_pow_left₀ (abs_nonneg y) hy 2
  have hint : |μe| ≤ B := by
    have := norm_integral_le_of_norm_le_const (μ := m) (f := e) (C := B)
      (Eventually.of_forall fun j => by rw [Real.norm_eq_abs]; exact hB j)
    simpa using this
  have hs2' : s ^ 2 ≤ |s| := by rw [← sq_abs s, sq]; exact mul_le_of_le_one_left (abs_nonneg s) hs3
  have hCy : C * y ^ 2 ≤ 4 * C * B ^ 2 * s ^ 2 :=
    calc C * y ^ 2 ≤ C * (4 * (B ^ 2 * s ^ 2)) := mul_le_mul_of_nonneg_left hy2 hC
      _ = 4 * C * B ^ 2 * s ^ 2 := by ring
  have hQe : |s| * (2 * |χ' L| * B + 4 * C * B ^ 2 + 1)
      = (2 * |χ' L| * B * |s| + 4 * C * B ^ 2 * |s|) + |s| := by ring
  have hsq1 : C * B ^ 2 * s ^ 2 ≤ C * B ^ 2 * |s| :=
    mul_le_mul_of_nonneg_left hs2' (mul_nonneg hC (sq_nonneg B))
  -- both arguments of the logs stay above `χ(L)/2`
  have hΦ : χ L / 2 ≤ Φ := by
    have hlin : |χ' L * s * μe| ≤ |χ' L| * B * |s| := by
      rw [abs_mul, abs_mul]
      calc |χ' L| * |s| * |μe| ≤ |χ' L| * |s| * B :=
            mul_le_mul_of_nonneg_left hint (mul_nonneg (abs_nonneg _) (abs_nonneg s))
        _ = |χ' L| * B * |s| := by ring
    have t1 : -(|χ' L| * B * |s|) ≤ χ' L * s * μe := by
      linarith [neg_abs_le (χ' L * s * μe)]
    have t2 := (abs_le.mp h1).1
    have t3 : C * s ^ 2 * B ^ 2 ≤ C * B ^ 2 * |s| := by
      calc C * s ^ 2 * B ^ 2 = C * B ^ 2 * s ^ 2 := by ring
        _ ≤ C * B ^ 2 * |s| := hsq1
    have t4 : |χ' L| * B * |s| + C * B ^ 2 * |s| ≤ χ L / 4 := by
      have : |χ' L| * B * |s| + C * B ^ 2 * |s|
          ≤ |s| * (2 * |χ' L| * B + 4 * C * B ^ 2 + 1) := by
        nlinarith [abs_nonneg s, abs_nonneg (χ' L), mul_nonneg hC (sq_nonneg B),
          mul_nonneg (abs_nonneg (χ' L)) hB0.le]
      linarith
    linarith
  have hΨ : χ L / 2 ≤ χ (L + y) := by
    have hlin : |χ' L * y| ≤ |χ' L| * (2 * (|s| * B)) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
    have t1 : -(|χ' L| * (2 * (|s| * B))) ≤ χ' L * y := by
      linarith [neg_abs_le (χ' L * y)]
    have t2 := (abs_le.mp h2).1
    have hq : C * y ^ 2 ≤ 4 * C * B ^ 2 * |s| := by
      have h4 : 4 * C * B ^ 2 * s ^ 2 ≤ 4 * C * B ^ 2 * |s| :=
        mul_le_mul_of_nonneg_left hs2' (by positivity)
      linarith
    have t4 : |χ' L| * (2 * (|s| * B)) + 4 * C * B ^ 2 * |s| ≤ χ L / 4 := by
      have : |χ' L| * (2 * (|s| * B)) + 4 * C * B ^ 2 * |s|
          ≤ |s| * (2 * |χ' L| * B + 4 * C * B ^ 2 + 1) := by
        nlinarith [abs_nonneg s, abs_nonneg (χ' L), mul_nonneg hC (sq_nonneg B),
          mul_nonneg (abs_nonneg (χ' L)) hB0.le]
      linarith
    linarith
  -- the difference of the arguments is second order
  have hdiff : |Φ - χ (L + y)| ≤ (5 * C + |χ' L| * ρ) * B ^ 2 * s ^ 2 := by
    have h3 : |χ' L * (s * μe - y)| ≤ |χ' L| * ρ * B ^ 2 * s ^ 2 := by
      rw [abs_mul, abs_sub_comm]
      calc |χ' L| * |y - s * μe| ≤ |χ' L| * (ρ * s ^ 2 * B ^ 2) :=
            mul_le_mul_of_nonneg_left hd1 (abs_nonneg _)
        _ = |χ' L| * ρ * B ^ 2 * s ^ 2 := by ring
    have hsplit : Φ - χ (L + y) = (Φ - χ L - χ' L * s * μe) - (χ (L + y) - χ L - χ' L * y)
        + χ' L * (s * μe - y) := by ring
    rw [hsplit]
    have k1 := abs_add_le ((Φ - χ L - χ' L * s * μe) - (χ (L + y) - χ L - χ' L * y))
      (χ' L * (s * μe - y))
    have k2 := abs_sub (Φ - χ L - χ' L * s * μe) (χ (L + y) - χ L - χ' L * y)
    have e5 : (5 * C + |χ' L| * ρ) * B ^ 2 * s ^ 2
        = C * s ^ 2 * B ^ 2 + 4 * C * B ^ 2 * s ^ 2 + |χ' L| * ρ * B ^ 2 * s ^ 2 := by ring
    linarith
  have hc : 0 < χ L / 2 := by linarith
  have hl := abs_log_sub_le hc hΦ hΨ
  unfold outputGapGen
  calc _ ≤ |Φ - χ (L + y)| / (χ L / 2) := hl
    _ ≤ (5 * C + |χ' L| * ρ) * B ^ 2 * s ^ 2 / (χ L / 2) :=
        div_le_div_of_nonneg_right hdiff hc.le
    _ = 2 * (5 * C + |χ' L| * ρ) * B ^ 2 * s ^ 2 / χ L := by field_simp

/-- Woodford (2003), (4.10), p. 224 (**output dispersion drops out to first order, general
technology**): `s ↦ outputGapGen(s)` has derivative `0` at `s = 0`. -/
theorem hasDerivAt_outputGapGen {χ χ' : ℝ → ℝ} (hχ : ∀ x, HasDerivAt χ (χ' x) x) {L δ C : ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hlip : ∀ x, |x - L| ≤ δ → |χ' x - χ' L| ≤ C * |x - L|)
    (hχL : 0 < χ L) {e : J → ℝ} (he : AEStronglyMeasurable e m) {B : ℝ} (hB0 : 0 < B)
    (hB : ∀ j, |e j| ≤ B) {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (fun s => outputGapGen m χ L e ρ s) 0 0 := by
  set Q := 2 * |χ' L| * B + 4 * C * B ^ 2 + 1
  have hQ : 0 < Q := by positivity
  refine hasDerivAt_zero_of_sq_bound ?_
    (δ := min (min (δ / (2 * B)) (1 / (ρ * B))) (min 1 (χ L / (4 * Q))))
    (K := 2 * (5 * C + |χ' L| * ρ) * B ^ 2 / χ L)
    (lt_min (lt_min (by positivity) (by positivity)) (lt_min one_pos (by positivity)))
    fun s hs => ?_
  · simp [outputGapGen, cesDev]
  · have hsa := hs.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hsb := hs.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hsc := hs.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hsd := hs.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at hsa hsb hsd
    have h := outputGapGen_sq_bound m hχ hC hlip hχL he hB0 hB hρ (s := s) (by linarith)
      (by linarith) hsc (by linarith)
    calc _ ≤ 2 * (5 * C + |χ' L| * ρ) * B ^ 2 * s ^ 2 / χ L := h
      _ = 2 * (5 * C + |χ' L| * ρ) * B ^ 2 / χ L * s ^ 2 := by ring

end Woodford.NominalRigidities.TidyR5DispersionGeneral
