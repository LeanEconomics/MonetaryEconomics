/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.ExpectationsMeasure
import OptimalPolicyRules.InflTargetStickyWages

/-!
# Complex conditional expectations and the stage solutions of (2.20) on a probability space

Woodford (2003), *Interest and Prices*, Chapter 8, §2.2, (2.20), p. 567, and App. G.7: the
optimal plan of the sticky-wage model is found by factoring `P(𝒵)`,
`𝒵 = (1 − βF)(1 − L)`, into stages `(𝒵 − Zᵢ)`, each solved by a backward recursion in a stable
root `μᵢ` and a forward (expectational) recursion in `βμᵢ`. The roots may be complex.

The module InflTargetStickyWages does this for an exact expectation system. Here the same stages are
solved on a filtered probability space with Mathlib's conditional expectation
(`ExpectationsMeasure.MeasExpectationSystem`), every equation holding almost surely.

* `CE`: the conditional expectation applied to real and imaginary parts; `CE_lin`, `KnownC.cmul`,
  `CE_of_known`, `CE_tower`, `CE_congr`, `CE_norm_le`, `CE_ofReal` (a.s. linearity, the law of
  iterated expectations, bounds).
* `fwdC_solves`: for `‖a‖ < 1` and a bounded adapted complex `h`, `v_t = E_t ∑ₖ aᵏ h_{t+k}`
  solves `v_t = a E_t v_{t+1} + h_t` a.s.
* `ZC`: the operator `𝒵`; `stage_exists`: if `βμ² − (1 + β − Z)μ + 1 = 0` with `‖μ‖ < 1`,
  `(𝒵 − Z) y = h` has a bounded adapted solution (a.s.).
* `cubic_exists`: the third-order equation `(𝒵 − Z₁)(𝒵 − Z₂)(𝒵 − Z₃) w = H` (in expanded form)
  has a bounded adapted solution when every `Zᵢ` has a stable `μᵢ`.
-/

namespace Woodford.OptimalPolicyRules.TidyR5bCondExpC

open MeasureTheory Filter Topology ExpectationsMeasure InflTargetStickyWages InflTargetInertia

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-! ### The complexified conditional expectation -/

/-- Woodford (2003), App. G.7: the conditional expectation applied to the real and imaginary
parts of a complex random variable. -/
noncomputable def CE (t : ℕ) (z : Ω → ℂ) : Ω → ℂ :=
  fun ω => ⟨S.E t (fun ω' => (z ω').re) ω, S.E t (fun ω' => (z ω').im) ω⟩

/-- Woodford (2003), App. G.7: a complex random variable with integrable real and imaginary
parts. -/
def IntC (z : Ω → ℂ) : Prop :=
  Integrable (fun ω => (z ω).re) S.μ ∧ Integrable (fun ω => (z ω).im) S.μ

/-- Woodford (2003), App. G.7: a complex random variable known at `t`. -/
def KnownC (t : ℕ) (z : Ω → ℂ) : Prop :=
  StronglyMeasurable[S.𝓕 t] (fun ω => (z ω).re) ∧ StronglyMeasurable[S.𝓕 t] (fun ω => (z ω).im)

/-- Woodford (2003), App. G.7: an adapted complex process. -/
def AdC (z : ℕ → Ω → ℂ) : Prop := ∀ t, KnownC S t (z t)

/-- Woodford (2003), App. G.7: an essentially bounded complex process. -/
def BdC (z : ℕ → Ω → ℂ) : Prop := ∃ M, ∀ t, ∀ᵐ ω ∂S.μ, ‖z t ω‖ ≤ M

variable {S}

/-- Woodford (2003), App. G.7 (tool): what is known at `s` is known at `t ≥ s`. -/
theorem KnownC.mono {s t : ℕ} (hst : s ≤ t) {z : Ω → ℂ} (h : KnownC S s z) : KnownC S t z :=
  ⟨h.1.mono (S.𝓕.mono hst), h.2.mono (S.𝓕.mono hst)⟩

/-- Woodford (2003), App. G.7 (tool): a known complex random variable `a z + b w`. -/
theorem KnownC.lin {t : ℕ} {z w : Ω → ℂ} (hz : KnownC S t z) (hw : KnownC S t w) (a b : ℂ) :
    KnownC S t (fun ω => a * z ω + b * w ω) := by
  refine ⟨?_, ?_⟩
  · have : (fun ω => (a * z ω + b * w ω).re) = fun ω =>
        a.re * (z ω).re - a.im * (z ω).im + (b.re * (w ω).re - b.im * (w ω).im) := by
      funext ω; simp
    rw [this]
    exact ((hz.1.const_mul _).sub (hz.2.const_mul _)).add ((hw.1.const_mul _).sub
      (hw.2.const_mul _))
  · have : (fun ω => (a * z ω + b * w ω).im) = fun ω =>
        a.re * (z ω).im + a.im * (z ω).re + (b.re * (w ω).im + b.im * (w ω).re) := by
      funext ω; simp
    rw [this]
    exact ((hz.2.const_mul _).add (hz.1.const_mul _)).add ((hw.2.const_mul _).add
      (hw.1.const_mul _))

/-- Woodford (2003), App. G.7 (tool): constants are known. -/
theorem KnownC.const (t : ℕ) (c : ℂ) : KnownC S t (fun _ => c) :=
  ⟨stronglyMeasurable_const, stronglyMeasurable_const⟩

/-- Woodford (2003), App. G.7 (tool): a known, essentially bounded complex random variable has
integrable parts. -/
theorem intC_of {t : ℕ} {z : Ω → ℂ} (hk : KnownC S t z) {M : ℝ}
    (hb : ∀ᵐ ω ∂S.μ, ‖z ω‖ ≤ M) : IntC S z :=
  ⟨Integrable.of_bound ((hk.1.mono (S.𝓕.le t)).aestronglyMeasurable) M
      (hb.mono fun ω h => by rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans h),
    Integrable.of_bound ((hk.2.mono (S.𝓕.le t)).aestronglyMeasurable) M
      (hb.mono fun ω h => by rw [Real.norm_eq_abs]; exact (Complex.abs_im_le_norm _).trans h)⟩

/-- Woodford (2003), App. G.7 (tool): integrable parts are preserved by `a z + b w`. -/
theorem IntC.lin {z w : Ω → ℂ} (hz : IntC S z) (hw : IntC S w) (a b : ℂ) :
    IntC S (fun ω => a * z ω + b * w ω) := by
  refine ⟨?_, ?_⟩
  · have : (fun ω => (a * z ω + b * w ω).re) = fun ω =>
        a.re * (z ω).re - a.im * (z ω).im + (b.re * (w ω).re - b.im * (w ω).im) := by
      funext ω; simp
    rw [this]
    exact ((hz.1.const_mul _).sub (hz.2.const_mul _)).add ((hw.1.const_mul _).sub
      (hw.2.const_mul _))
  · have : (fun ω => (a * z ω + b * w ω).im) = fun ω =>
        a.re * (z ω).im + a.im * (z ω).re + (b.re * (w ω).im + b.im * (w ω).re) := by
      funext ω; simp
    rw [this]
    exact ((hz.2.const_mul _).add (hz.1.const_mul _)).add ((hw.2.const_mul _).add
      (hw.1.const_mul _))

/-- Woodford (2003), App. G.7: `CE_t z` is known at `t`. -/
theorem knownC_CE (t : ℕ) (z : Ω → ℂ) : KnownC S t (CE S t z) :=
  ⟨S.stronglyMeasurable_E t _, S.stronglyMeasurable_E t _⟩

/-- Woodford (2003), App. G.7: `CE_t z` has integrable parts. -/
theorem intC_CE (t : ℕ) (z : Ω → ℂ) : IntC S (CE S t z) :=
  ⟨S.integrable_E t _, S.integrable_E t _⟩

/-- Woodford (2003), App. G.7: what is known at `t` is its own forecast (exactly). -/
theorem CE_of_known {t : ℕ} {z : Ω → ℂ} (hk : KnownC S t z) (hi : IntC S z) : CE S t z = z := by
  funext ω
  apply Complex.ext
  · change S.E t (fun ω' => (z ω').re) ω = (z ω).re
    rw [S.E_of_stronglyMeasurable hk.1 hi.1]
  · change S.E t (fun ω' => (z ω').im) ω = (z ω).im
    rw [S.E_of_stronglyMeasurable hk.2 hi.2]

/-- Woodford (2003), App. G.7: `CE_t (a z + b w) = a CE_t z + b CE_t w` a.s. -/
theorem CE_lin {z w : Ω → ℂ} (hz : IntC S z) (hw : IntC S w) (a b : ℂ) (t : ℕ) :
    CE S t (fun ω => a * z ω + b * w ω) =ᵐ[S.μ]
      fun ω => a * CE S t z ω + b * CE S t w ω := by
  have er : (fun ω => (a * z ω + b * w ω).re) = (a.re • fun ω => (z ω).re) -
      (a.im • fun ω => (z ω).im) + ((b.re • fun ω => (w ω).re) - (b.im • fun ω => (w ω).im)) := by
    funext ω; simp
  have ei : (fun ω => (a * z ω + b * w ω).im) = (a.re • fun ω => (z ω).im) +
      (a.im • fun ω => (z ω).re) + ((b.re • fun ω => (w ω).im) + (b.im • fun ω => (w ω).re)) := by
    funext ω; simp
  have i1 := hz.1.smul a.re
  have i2 := hz.2.smul a.im
  have i3 := hw.1.smul b.re
  have i4 := hw.2.smul b.im
  have i5 := hz.2.smul a.re
  have i6 := hz.1.smul a.im
  have i7 := hw.2.smul b.re
  have i8 := hw.1.smul b.im
  filter_upwards [S.E_add (i1.sub i2) (i3.sub i4) t, S.E_sub i1 i2 t, S.E_sub i3 i4 t,
    S.E_add (i5.add i6) (i7.add i8) t, S.E_add i5 i6 t, S.E_add i7 i8 t,
    S.E_smul a.re (fun ω => (z ω).re) t, S.E_smul a.im (fun ω => (z ω).im) t,
    S.E_smul b.re (fun ω => (w ω).re) t, S.E_smul b.im (fun ω => (w ω).im) t,
    S.E_smul a.re (fun ω => (z ω).im) t, S.E_smul a.im (fun ω => (z ω).re) t,
    S.E_smul b.re (fun ω => (w ω).im) t, S.E_smul b.im (fun ω => (w ω).re) t]
    with ω h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  apply Complex.ext
  · change S.E t (fun ω => (a * z ω + b * w ω).re) ω = _
    rw [er, h1, Pi.add_apply, h2, h3, Pi.sub_apply, Pi.sub_apply, h7, h8, h9, h10]
    simp [CE]
  · change S.E t (fun ω => (a * z ω + b * w ω).im) ω = _
    rw [ei, h4, Pi.add_apply, h5, h6, Pi.add_apply, Pi.add_apply, h11, h12, h13, h14]
    simp [CE]

/-- Woodford (2003), App. G.7: the law of iterated expectations, `CE_s CE_t = CE_s` (`s ≤ t`),
a.s. -/
theorem CE_tower {s t : ℕ} (hst : s ≤ t) (z : Ω → ℂ) :
    CE S s (CE S t z) =ᵐ[S.μ] CE S s z := by
  filter_upwards [S.E_tower hst (fun ω => (z ω).re), S.E_tower hst (fun ω => (z ω).im)]
    with ω h1 h2
  exact Complex.ext h1 h2

/-- Woodford (2003), App. G.7: `CE_t` respects a.s. equality. -/
theorem CE_congr {z w : Ω → ℂ} (h : z =ᵐ[S.μ] w) (t : ℕ) : CE S t z =ᵐ[S.μ] CE S t w := by
  have hr : (fun ω => (z ω).re) =ᵐ[S.μ] fun ω => (w ω).re := h.mono fun ω h => by simp only [h]
  have hi : (fun ω => (z ω).im) =ᵐ[S.μ] fun ω => (w ω).im := h.mono fun ω h => by simp only [h]
  filter_upwards [S.E_congr hr t, S.E_congr hi t] with ω h1 h2
  exact Complex.ext h1 h2

/-- Woodford (2003), App. G.7: `‖CE_t z‖ ≤ 2M` a.s. when `‖z‖ ≤ M` a.s. -/
theorem CE_norm_le {z : Ω → ℂ} {M : ℝ} (h : ∀ᵐ ω ∂S.μ, ‖z ω‖ ≤ M) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, ‖CE S t z ω‖ ≤ 2 * M := by
  have hr : ∀ᵐ ω ∂S.μ, |(z ω).re| ≤ M := h.mono fun ω h => (Complex.abs_re_le_norm _).trans h
  have hi : ∀ᵐ ω ∂S.μ, |(z ω).im| ≤ M := h.mono fun ω h => (Complex.abs_im_le_norm _).trans h
  filter_upwards [S.abs_E_le hr t, S.abs_E_le hi t] with ω h1 h2
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  change |S.E t _ ω| + |S.E t _ ω| ≤ 2 * M
  linarith

/-- Woodford (2003), App. G.7: on real random variables `CE_t` is `E_t`. -/
theorem CE_ofReal (t : ℕ) (x : Ω → ℝ) :
    CE S t (fun ω => (x ω : ℂ)) = fun ω => (S.E t x ω : ℂ) := by
  funext ω
  apply Complex.ext
  · rfl
  · change S.E t (fun ω' => ((x ω' : ℂ)).im) ω = 0
    simp only [Complex.ofReal_im]
    rw [S.E_const t 0]

/-- Woodford (2003), App. G.7 (tool): a known complex random variable `a z`. -/
theorem KnownC.cmul {t : ℕ} {z : Ω → ℂ} (hz : KnownC S t z) (a : ℂ) :
    KnownC S t (fun ω => a * z ω) := by
  have := hz.lin (KnownC.const t 0) a 0
  simpa using this

/-- Woodford (2003), App. G.7 (tool): a complex random variable with measurable parts is a.e.
strongly measurable. -/
theorem aesm_of_knownC {t : ℕ} {z : Ω → ℂ} (hz : KnownC S t z) :
    AEStronglyMeasurable z S.μ := by
  have e : z = fun ω => ((z ω).re : ℂ) + ((z ω).im : ℂ) * Complex.I :=
    funext fun ω => (Complex.re_add_im _).symm
  rw [e]
  exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
    (hz.1.mono (S.𝓕.le t)).aestronglyMeasurable).add
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hz.2.mono (S.𝓕.le t)).aestronglyMeasurable).mul_const _)

/-! ### Forward solutions with a complex discount factor -/

omit [MeasurableSpace Ω] in
/-- Woodford (2003), (2.20): the realised forward sum `∑ₖ aᵏ h_{t+k}`. -/
noncomputable def fwdSum (a : ℂ) (h : ℕ → Ω → ℂ) (t : ℕ) : Ω → ℂ :=
  fun ω => ∑' k, a ^ k * h (t + k) ω

/-- Woodford (2003), (2.20) (tool): a complex geometric series with bounded terms is summable. -/
theorem summable_geomC {a : ℂ} (ha : ‖a‖ < 1) {x : ℕ → ℂ} {M : ℝ} (hx : ∀ k, ‖x k‖ ≤ M) :
    Summable (fun k => a ^ k * x k) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg a) ha).mul_right M)
    (fun k => by
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (hx k) (pow_nonneg (norm_nonneg a) k))

/-- Woodford (2003), (2.20) (tool): `‖∑ aᵏ xₖ‖ ≤ M / (1 − ‖a‖)`. -/
theorem norm_tsum_geomC_le {a : ℂ} (ha : ‖a‖ < 1) {x : ℕ → ℂ} {M : ℝ} (hx : ∀ k, ‖x k‖ ≤ M) :
    ‖∑' k, a ^ k * x k‖ ≤ M / (1 - ‖a‖) := by
  rw [div_eq_inv_mul]
  refine tsum_of_norm_bounded ((hasSum_geometric_of_lt_one (norm_nonneg a) ha).mul_right M)
    (fun k => ?_)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (hx k) (pow_nonneg (norm_nonneg a) k)

omit [MeasurableSpace Ω] in
/-- Woodford (2003), (2.20): the realised forward sum satisfies `D_t = h_t + a D_{t+1}` wherever
it converges. -/
theorem fwdSum_succ {a : ℂ} {h : ℕ → Ω → ℂ} {t : ℕ} {ω : Ω}
    (hs : Summable (fun k => a ^ k * h (t + k) ω)) :
    fwdSum a h t ω = h t ω + a * fwdSum a h (t + 1) ω := by
  unfold fwdSum
  rw [hs.tsum_eq_zero_add, pow_zero, one_mul, add_zero, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun k => ?_
  rw [show t + (k + 1) = t + 1 + k by omega, pow_succ]
  ring

/-- Woodford (2003), (2.20): the realised forward sum of a bounded adapted process is a.s.
bounded and has integrable parts. -/
theorem fwdSum_spec {a : ℂ} (ha : ‖a‖ < 1) {h : ℕ → Ω → ℂ} (hm : AdC S h) {M : ℝ}
    (hb : ∀ t, ∀ᵐ ω ∂S.μ, ‖h t ω‖ ≤ M) (t : ℕ) :
    IntC S (fwdSum a h t) ∧ ∀ᵐ ω ∂S.μ, ‖fwdSum a h t ω‖ ≤ M / (1 - ‖a‖) := by
  have hbd : ∀ᵐ ω ∂S.μ, ‖fwdSum a h t ω‖ ≤ M / (1 - ‖a‖) := by
    filter_upwards [ae_all_iff.2 hb] with ω hω
    exact norm_tsum_geomC_le ha fun k => hω (t + k)
  have hD : AEStronglyMeasurable (fwdSum a h t) S.μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun N ω => ∑ k ∈ Finset.range N, a ^ k * h (t + k) ω)
      (fun N => Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
        (aesm_of_knownC (hm (t + k))).const_mul _) ?_
    filter_upwards [ae_all_iff.2 hb] with ω hω
    exact (summable_geomC ha fun k => hω (t + k)).hasSum.tendsto_sum_nat
  refine ⟨⟨Integrable.of_bound (Complex.continuous_re.comp_aestronglyMeasurable hD)
      (M / (1 - ‖a‖)) (hbd.mono fun ω h => ?_),
    Integrable.of_bound (Complex.continuous_im.comp_aestronglyMeasurable hD)
      (M / (1 - ‖a‖)) (hbd.mono fun ω h => ?_)⟩, hbd⟩
  · rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans h
  · rw [Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm _).trans h

variable (S) in
/-- Woodford (2003), (2.20): the forward solution `v_t = E_t ∑ₖ aᵏ h_{t+k}`. -/
noncomputable def fwdC (a : ℂ) (h : ℕ → Ω → ℂ) (t : ℕ) : Ω → ℂ := CE S t (fwdSum a h t)

/-- **Woodford (2003), (2.20) (the forward solution on a probability space)**: for `‖a‖ < 1`
and a bounded adapted complex `h`, `v_t = a E_t v_{t+1} + h_t` a.s. -/
theorem fwdC_solves {a : ℂ} (ha : ‖a‖ < 1) {h : ℕ → Ω → ℂ} (hm : AdC S h) {M : ℝ}
    (hb : ∀ t, ∀ᵐ ω ∂S.μ, ‖h t ω‖ ≤ M) (t : ℕ) :
    fwdC S a h t =ᵐ[S.μ] fun ω => a * CE S t (fwdC S a h (t + 1)) ω + h t ω := by
  have hI : IntC S (fwdSum a h (t + 1)) := (fwdSum_spec ha hm hb (t + 1)).1
  have hIh : IntC S (h t) := intC_of (hm t) (hb t)
  have hrec : fwdSum a h t =ᵐ[S.μ] fun ω => 1 * h t ω + a * fwdSum a h (t + 1) ω := by
    filter_upwards [ae_all_iff.2 hb] with ω hω
    rw [fwdSum_succ (summable_geomC ha fun k => hω (t + k)), one_mul]
  filter_upwards [CE_congr hrec t, CE_lin hIh hI 1 a t,
    CE_tower (Nat.le_succ t) (fwdSum a h (t + 1))] with ω h1 h2 h3
  change CE S t (fwdSum a h t) ω = a * CE S t (CE S (t + 1) (fwdSum a h (t + 1))) ω + h t ω
  rw [h1, h2, h3, CE_of_known (hm t) hIh]
  ring

/-- Woodford (2003), (2.20): the forward solution is a.s. bounded by `2M/(1 − ‖a‖)`. -/
theorem fwdC_bdd {a : ℂ} (ha : ‖a‖ < 1) {h : ℕ → Ω → ℂ} (hm : AdC S h) {M : ℝ}
    (hb : ∀ t, ∀ᵐ ω ∂S.μ, ‖h t ω‖ ≤ M) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, ‖fwdC S a h t ω‖ ≤ 2 * (M / (1 - ‖a‖)) :=
  CE_norm_le (fwdSum_spec ha hm hb t).2 t

/-! ### One stage `(𝒵 − Z) y = h` -/

variable (S) in
/-- Woodford (2003), (2.20): the operator `𝒵 = (1 − βF)(1 − L)` with conditional expectations,
`(𝒵y)_t = (1 + β) y_t − β E_t y_{t+1} − y_{t−1}` (with `y_{−1} = y₀`). -/
noncomputable def ZC (β : ℝ) (y₀ : Ω → ℂ) (y : ℕ → Ω → ℂ) (t : ℕ) : Ω → ℂ :=
  fun ω => (1 + β : ℂ) * y t ω - β * CE S t (y (t + 1)) ω - lagC y₀ y t ω

/-- Woodford (2003), (2.20): `𝒵` is linear a.s. -/
theorem ZC_lin (β : ℝ) (a b : ℂ) (y₀ z₀ : Ω → ℂ) {y z : ℕ → Ω → ℂ} (t : ℕ)
    (hy : IntC S (y (t + 1))) (hz : IntC S (z (t + 1))) :
    ZC S β (fun ω => a * y₀ ω + b * z₀ ω) (fun s ω => a * y s ω + b * z s ω) t =ᵐ[S.μ]
      fun ω => a * ZC S β y₀ y t ω + b * ZC S β z₀ z t ω := by
  filter_upwards [CE_lin hy hz a b t] with ω h
  have hL : lagC (fun ω => a * y₀ ω + b * z₀ ω) (fun s ω => a * y s ω + b * z s ω) t ω =
      a * lagC y₀ y t ω + b * lagC z₀ z t ω := by cases t <;> rfl
  simp only [ZC]
  rw [h, hL]
  ring

/-- Woodford (2003), (2.20): `𝒵` respects a.s. equality of processes and initial values. -/
theorem ZC_congr (β : ℝ) {y₀ z₀ : Ω → ℂ} {y z : ℕ → Ω → ℂ} (h0 : y₀ =ᵐ[S.μ] z₀)
    (h : ∀ t, y t =ᵐ[S.μ] z t) (t : ℕ) : ZC S β y₀ y t =ᵐ[S.μ] ZC S β z₀ z t := by
  have hL : lagC y₀ y t =ᵐ[S.μ] lagC z₀ z t := by
    cases t with
    | zero => exact h0
    | succ t => exact h t
  filter_upwards [h t, CE_congr (h (t + 1)) t, hL] with ω h1 h2 h3
  simp only [ZC]
  rw [h1, h2, h3]

/-- Woodford (2003), (2.20) (tool): the complex backward recursion is adapted. -/
theorem backRecC_adC {μ : ℂ} {y₀ : Ω → ℂ} (hy₀ : KnownC S 0 y₀) {v : ℕ → Ω → ℂ}
    (hv : AdC S v) : AdC S (backRecC μ y₀ v) := by
  intro t
  induction t with
  | zero =>
    have e : backRecC μ y₀ v 0 = fun ω => μ * y₀ ω + 1 * v 0 ω := by
      funext ω; simp [backRecC]
    rw [e]
    exact hy₀.lin (hv 0) μ 1
  | succ t ih =>
    have e : backRecC μ y₀ v (t + 1) = fun ω => μ * backRecC μ y₀ v t ω + 1 * v (t + 1) ω := by
      funext ω; simp [backRecC]
    rw [e]
    exact (ih.mono (Nat.le_succ t)).lin (hv (t + 1)) μ 1

/-- Woodford (2003), (2.20) (tool): for `‖μ‖ < 1` the complex backward recursion is a.s.
bounded. -/
theorem backRecC_bdd {μ : ℂ} (hμ : ‖μ‖ < 1) {y₀ : Ω → ℂ} {Y : ℝ}
    (hy₀ : ∀ᵐ ω ∂S.μ, ‖y₀ ω‖ ≤ Y) {v : ℕ → Ω → ℂ} {W : ℝ}
    (hv : ∀ t, ∀ᵐ ω ∂S.μ, ‖v t ω‖ ≤ W) :
    ∀ t, ∀ᵐ ω ∂S.μ, ‖backRecC μ y₀ v t ω‖ ≤ max Y (W / (1 - ‖μ‖)) := by
  set B := max Y (W / (1 - ‖μ‖))
  have h1a : 0 < 1 - ‖μ‖ := by linarith
  have hWB : W ≤ (1 - ‖μ‖) * B := by
    have : W / (1 - ‖μ‖) ≤ B := le_max_right _ _
    rwa [div_le_iff₀ h1a, mul_comm] at this
  have step : ∀ (y w : ℂ), ‖y‖ ≤ B → ‖w‖ ≤ W → ‖μ * y + w‖ ≤ B := by
    intro y w hy hw
    calc ‖μ * y + w‖ ≤ ‖μ‖ * ‖y‖ + ‖w‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul]
      _ ≤ ‖μ‖ * B + W := add_le_add (mul_le_mul_of_nonneg_left hy (norm_nonneg _)) hw
      _ ≤ B := by linarith
  have hall : ∀ᵐ ω ∂S.μ, ∀ t, ‖backRecC μ y₀ v t ω‖ ≤ B := by
    filter_upwards [hy₀, ae_all_iff.2 hv] with ω h0 hω
    intro t
    induction t with
    | zero =>
      change ‖μ * y₀ ω + v 0 ω‖ ≤ B
      exact step _ _ (h0.trans (le_max_left _ _)) (hω 0)
    | succ t ih =>
      change ‖μ * backRecC μ y₀ v t ω + v (t + 1) ω‖ ≤ B
      exact step _ _ ih (hω (t + 1))
  intro t
  filter_upwards [hall] with ω h
  exact h t

/-- **Woodford (2003), (2.20) (one factor of `P(𝒵)` on a probability space)**: if
`βμ² − (1 + β − Z)μ + 1 = 0` with `‖μ‖ < 1`, then for a bounded adapted complex `h` and a
bounded initial value known at date `0`, `(𝒵 − Z) y = h` has a bounded adapted solution (a.s.):
`y = (1 − μL)⁻¹ μ (1 − βμF)⁻¹ h`. -/
theorem stage_exists {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {Z μ : ℂ}
    (hroot : (β : ℂ) * μ ^ 2 - (1 + β - Z) * μ + 1 = 0) (hμ : ‖μ‖ < 1) {h : ℕ → Ω → ℂ}
    (hha : AdC S h) (hhb : BdC S h) {y₀ : Ω → ℂ} (hy₀k : KnownC S 0 y₀) {Y : ℝ}
    (hy₀b : ∀ᵐ ω ∂S.μ, ‖y₀ ω‖ ≤ Y) :
    ∃ y, AdC S y ∧ BdC S y ∧ ∀ t, ∀ᵐ ω ∂S.μ, ZC S β y₀ y t ω - Z * y t ω = h t ω := by
  have hμ0 : μ ≠ 0 := by
    rintro rfl; simp at hroot
  have hβμ : ‖(β : ℂ) * μ‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβ0]
    nlinarith [norm_nonneg μ]
  obtain ⟨H, hH⟩ := hhb
  set g : ℕ → Ω → ℂ := fun s ω => μ * h s ω with hg
  have hga : AdC S g := fun s => (hha s).cmul μ
  have hgb : ∀ t, ∀ᵐ ω ∂S.μ, ‖g t ω‖ ≤ ‖μ‖ * H := fun t => (hH t).mono fun ω h => by
    simp only [hg, norm_mul]
    exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
  set v := fwdC S ((β : ℂ) * μ) g with hv
  have hva : AdC S v := fun t => knownC_CE t _
  have hvb := fwdC_bdd hβμ hga hgb
  set y := backRecC μ y₀ v with hy
  have hya : AdC S y := backRecC_adC hy₀k hva
  have hyb := backRecC_bdd hμ hy₀b hvb
  have hq : ∀ t ω, y t ω - μ * lagC y₀ y t ω = v t ω := by
    intro t ω
    have := congrFun (backRecC_eq μ y₀ v t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [hy, this]
    ring
  have hyI : ∀ t, IntC S (y t) := fun t => intC_of (hya t) (hyb t)
  have hvI : ∀ t, IntC S (v t) := fun t => intC_of (hva t) (hvb t)
  refine ⟨y, hya, ⟨_, hyb⟩, fun t => ?_⟩
  have hyf : y (t + 1) = fun ω => μ * y t ω + 1 * v (t + 1) ω := by
    funext ω
    have := hq (t + 1) ω
    simp only [lagC_succ] at this
    linear_combination this
  have hCEy : CE S t (y (t + 1)) =ᵐ[S.μ] fun ω => μ * y t ω + 1 * CE S t (v (t + 1)) ω := by
    rw [hyf]
    filter_upwards [CE_lin (hyI t) (hvI (t + 1)) μ 1 t] with ω h1
    rw [h1, CE_of_known (hya t) (hyI t)]
  filter_upwards [fwdC_solves hβμ hga hgb t, hCEy] with ω e1 e2
  have e3 := hq t ω
  change v t ω = (β : ℂ) * μ * CE S t (v (t + 1)) ω + μ * h t ω at e1
  have key : μ * (ZC S β y₀ y t ω - Z * y t ω - h t ω) = 0 := by
    simp only [ZC]
    rw [e2]
    linear_combination e1 + e3 - (y t ω) * hroot
  rcases mul_eq_zero.1 key with h0 | h0
  · exact absurd h0 hμ0
  · linear_combination h0

/-- Woodford (2003), (2.20): `𝒵` of an adapted process with an initial value known at `0` is
adapted. -/
theorem ZC_adC (β : ℝ) {y₀ : Ω → ℂ} (hy₀ : KnownC S 0 y₀) {y : ℕ → Ω → ℂ} (hy : AdC S y) :
    AdC S (ZC S β y₀ y) := by
  intro t
  have hl : KnownC S t (lagC y₀ y t) := by
    cases t with
    | zero => exact hy₀
    | succ t => exact (hy t).mono (Nat.le_succ t)
  have e : ZC S β y₀ y t = fun ω => 1 * ((1 + β : ℂ) * y t ω + (-(β : ℂ)) *
      CE S t (y (t + 1)) ω) + (-1) * lagC y₀ y t ω := by
    funext ω; simp only [ZC]; ring
  rw [e]
  exact ((hy t).lin (knownC_CE t _) _ _).lin hl _ _

/-- Woodford (2003), (2.20): `𝒵` of a bounded process with a bounded initial value is
bounded. -/
theorem ZC_bdC (β : ℝ) (hβ : 0 ≤ β) {y₀ : Ω → ℂ} {Y : ℝ} (hy₀ : ∀ᵐ ω ∂S.μ, ‖y₀ ω‖ ≤ Y)
    {y : ℕ → Ω → ℂ} {M : ℝ} (hy : ∀ t, ∀ᵐ ω ∂S.μ, ‖y t ω‖ ≤ M) :
    BdC S (ZC S β y₀ y) := by
  refine ⟨(1 + β) * M + β * (2 * M) + max Y M, fun t => ?_⟩
  have hl : ∀ᵐ ω ∂S.μ, ‖lagC y₀ y t ω‖ ≤ max Y M := by
    cases t with
    | zero => exact hy₀.mono fun ω h => h.trans (le_max_left _ _)
    | succ t => exact (hy t).mono fun ω h => h.trans (le_max_right _ _)
  filter_upwards [hy t, CE_norm_le (hy (t + 1)) t, hl] with ω h1 h2 h3
  have n1 : ‖(1 + β : ℂ)‖ = 1 + β := by
    rw [show (1 + (β : ℂ)) = ((1 + β : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have n2 : ‖(β : ℂ)‖ = β := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβ]
  simp only [ZC]
  refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) h3)
  · rw [norm_mul, n1]
    exact mul_le_mul_of_nonneg_left h1 (by linarith)
  · rw [norm_mul, n2]
    exact mul_le_mul_of_nonneg_left h2 hβ

/-! ### The third-order equation -/

/-- **Woodford (2003), (2.20) (the cubic operator equation on a probability space)**: if each
`Zᵢ` has a root `μᵢ`, `‖μᵢ‖ < 1`, of `βμ² − (1 + β − Zᵢ)μ + 1 = 0`, then for a bounded adapted
`H` and bounded initial values known at `0`, `𝒵³w − e₁𝒵²w + e₂𝒵w − e₃w = H` (`eᵢ` the
elementary symmetric functions of the `Zᵢ`) has a bounded adapted solution (a.s.). -/
theorem cubic_exists {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {Z1 Z2 Z3 μ1 μ2 μ3 : ℂ}
    (r1 : (β : ℂ) * μ1 ^ 2 - (1 + β - Z1) * μ1 + 1 = 0) (n1 : ‖μ1‖ < 1)
    (r2 : (β : ℂ) * μ2 ^ 2 - (1 + β - Z2) * μ2 + 1 = 0) (n2 : ‖μ2‖ < 1)
    (r3 : (β : ℂ) * μ3 ^ 2 - (1 + β - Z3) * μ3 + 1 = 0) (n3 : ‖μ3‖ < 1)
    {H : ℕ → Ω → ℂ} (hHa : AdC S H) (hHb : BdC S H) {w₀ s₁ s₂ : Ω → ℂ}
    (kw : KnownC S 0 w₀) (k1 : KnownC S 0 s₁) (k2 : KnownC S 0 s₂) {B : ℝ}
    (bw : ∀ᵐ ω ∂S.μ, ‖w₀ ω‖ ≤ B) (b1 : ∀ᵐ ω ∂S.μ, ‖s₁ ω‖ ≤ B)
    (b2 : ∀ᵐ ω ∂S.μ, ‖s₂ ω‖ ≤ B) :
    ∃ w, AdC S w ∧ BdC S w ∧ ∀ t, ∀ᵐ ω ∂S.μ,
      ZC S β s₂ (ZC S β s₁ (ZC S β w₀ w)) t ω - (Z1 + Z2 + Z3) * ZC S β s₁ (ZC S β w₀ w) t ω +
        (Z1 * Z2 + Z1 * Z3 + Z2 * Z3) * ZC S β w₀ w t ω - Z1 * Z2 * Z3 * w t ω = H t ω := by
  set u1₀ : Ω → ℂ := fun ω => 1 * s₁ ω + -Z3 * w₀ ω with hu1
  set u2₀ : Ω → ℂ := fun ω => 1 * (1 * s₂ ω + -(Z2 + Z3) * s₁ ω) + Z2 * Z3 * w₀ ω with hu2
  have ku1 : KnownC S 0 u1₀ := k1.lin kw _ _
  have ku2 : KnownC S 0 u2₀ := (k2.lin k1 _ _).lin kw _ _
  have bu1 : ∀ᵐ ω ∂S.μ, ‖u1₀ ω‖ ≤ B + ‖Z3‖ * B := by
    filter_upwards [b1, bw] with ω h1 h2
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, norm_one, one_mul]; exact h1
    · rw [norm_mul, norm_neg]; exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  have bu2 : ∀ᵐ ω ∂S.μ, ‖u2₀ ω‖ ≤ (B + ‖Z2 + Z3‖ * B) + ‖Z2 * Z3‖ * B := by
    filter_upwards [b2, b1, bw] with ω h1 h2 h3
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, norm_one, one_mul]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul, norm_one, one_mul]; exact h1
      · rw [norm_mul, norm_neg]; exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
  obtain ⟨U2, a2, ⟨K2, bb2⟩, e1⟩ := stage_exists hβ0 hβ1 r1 n1 hHa hHb ku2 bu2
  obtain ⟨U1, a1, ⟨K1, bb1⟩, e2⟩ := stage_exists hβ0 hβ1 r2 n2 a2 ⟨K2, bb2⟩ ku1 bu1
  obtain ⟨w, aw, ⟨Kw, bbw⟩, e3⟩ := stage_exists hβ0 hβ1 r3 n3 a1 ⟨K1, bb1⟩ kw bw
  have I1 : ∀ t, IntC S (U1 t) := fun t => intC_of (a1 t) (bb1 t)
  have I2 : ∀ t, IntC S (U2 t) := fun t => intC_of (a2 t) (bb2 t)
  have Iw : ∀ t, IntC S (w t) := fun t => intC_of (aw t) (bbw t)
  set W1 := ZC S β w₀ w with hW1def
  obtain ⟨KW1, bbW1⟩ := ZC_bdC β hβ0 bw bbw
  have aW1 : AdC S W1 := ZC_adC β kw aw
  have IW1 : ∀ t, IntC S (W1 t) := fun t => intC_of (aW1 t) (bbW1 t)
  have hW1 : ∀ t, W1 t =ᵐ[S.μ] fun ω => 1 * U1 t ω + Z3 * w t ω := fun t => by
    filter_upwards [e3 t] with ω h
    rw [← h]; ring
  have hs1 : s₁ = fun ω => 1 * u1₀ ω + Z3 * w₀ ω := by funext ω; simp only [hu1]; ring
  have hW2 : ∀ t, ZC S β s₁ W1 t =ᵐ[S.μ]
      fun ω => 1 * (1 * U2 t ω + Z2 * U1 t ω) + Z3 * W1 t ω := by
    intro t
    have c1 := ZC_congr (S := S) β (EventuallyEq.of_eq hs1) hW1 t
    filter_upwards [c1, ZC_lin β 1 Z3 u1₀ w₀ t (I1 (t + 1)) (Iw (t + 1)), e2 t] with ω h1 h2 h3
    rw [h1, h2, ← h3]
    ring
  set V : ℕ → Ω → ℂ := fun s ω => 1 * U2 s ω + Z2 * U1 s ω with hVdef
  have IV : ∀ t, IntC S (V t) := fun t => (I2 t).lin (I1 t) 1 Z2
  have hV : ∀ t, ZC S β (fun ω => 1 * u2₀ ω + Z2 * u1₀ ω) V t =ᵐ[S.μ]
      fun ω => 1 * (H t ω + Z1 * U2 t ω) + Z2 * (U2 t ω + Z2 * U1 t ω) := by
    intro t
    filter_upwards [ZC_lin β 1 Z2 u2₀ u1₀ t (I2 (t + 1)) (I1 (t + 1)), e1 t, e2 t]
      with ω h1 h2 h3
    rw [h1, ← h2, ← h3]
    ring
  have hs2 : s₂ = fun ω => 1 * (fun ω => 1 * u2₀ ω + Z2 * u1₀ ω) ω + Z3 * s₁ ω := by
    funext ω; simp only [hu1, hu2]; ring
  have hW3 : ∀ t, ZC S β s₂ (ZC S β s₁ W1) t =ᵐ[S.μ]
      fun ω => 1 * (1 * (H t ω + Z1 * U2 t ω) + Z2 * (U2 t ω + Z2 * U1 t ω)) +
        Z3 * ZC S β s₁ W1 t ω := by
    intro t
    have c1 := ZC_congr (S := S) β (EventuallyEq.of_eq hs2) hW2 t
    filter_upwards [c1, ZC_lin β 1 Z3 (fun ω => 1 * u2₀ ω + Z2 * u1₀ ω) s₁ t (IV (t + 1))
      (IW1 (t + 1)), hV t] with ω h1 h2 h3
    rw [h1, h2, h3]
  refine ⟨w, aw, ⟨Kw, bbw⟩, fun t => ?_⟩
  filter_upwards [hW3 t, hW2 t, hW1 t] with ω h1 h2 h3
  rw [h1, h2]
  change 1 * (1 * (H t ω + Z1 * U2 t ω) + Z2 * (U2 t ω + Z2 * U1 t ω)) +
    Z3 * (1 * (1 * U2 t ω + Z2 * U1 t ω) + Z3 * W1 t ω) - (Z1 + Z2 + Z3) *
    (1 * (1 * U2 t ω + Z2 * U1 t ω) + Z3 * W1 t ω) + (Z1 * Z2 + Z1 * Z3 + Z2 * Z3) * W1 t ω -
    Z1 * Z2 * Z3 * w t ω = H t ω
  rw [h3]
  ring

end Woodford.OptimalPolicyRules.TidyR5bCondExpC
