/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR5bCondExpC
import OptimalPolicyRules.TidyR5bStickyMeasure

/-!
# The exact determinacy region for (2.20) on a probability space (`κ_w ≠ κ_p`)

Woodford (2003), *Interest and Prices*, Chapter 8, §2.2, (2.11)–(2.20), pp. 565–567.

`TidyR5bStickyMeasure.stableRoots_of_exists_meas` proves the "only if" half of the root condition
on a filtered probability space with Mathlib's conditional expectation. This module proves the
"if" half there, porting the construction of `InflTargetStickyWages.foc_existsUnique`
(factor `P(𝒵)` into three stages, solve the cubic equation in the real wage, and read off the
plan and multipliers) to almost-sure equations:

* `Zm`: the operator `𝒵` with conditional expectations on real processes; `re_ZC`: it is the
  real part of `TidyR5bCondExpC.ZC`; `Zm_comb6`: it is linear a.s.
* `cubicR_exists`: the real third-order equation has a bounded adapted solution (the real part
  of `TidyR5bCondExpC.cubic_exists`).
* `exists_meas_of_stableRoots`: under the root condition `InflTargetStickyWages.StableRoots`, for
  every bounded adapted disturbance and constant initial multipliers there is a bounded adapted
  plan with bounded adapted multipliers satisfying (2.11)–(2.13) and (2.16)–(2.19) a.s.
* `exists_meas_iff_stableRoots`: **the full a.s. criterion** — such solutions exist for all data
  iff the root condition holds (equivalently every root of `P` lies outside the ellipse).
-/

namespace Woodford.OptimalPolicyRules.TidyR5bStickyExists

open MeasureTheory Filter Topology ExpectationsMeasure InflTargetStickyWages InflTargetInertia
open TidyR5bCondExpC TidyR5bStickyMeasure

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-! ### The operator `𝒵` on real processes -/

/-- Woodford (2003), (2.20): `(𝒵y)_t = (1 + β) y_t − β E_t y_{t+1} − y_{t−1}` with Mathlib's
conditional expectation. -/
noncomputable def Zm (β : ℝ) (y₀ : Ω → ℝ) (y : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (1 + β) * y t ω - β * S.E t (y (t + 1)) ω - lagW y₀ y t ω

variable {S}

/-- Woodford (2003), (2.20): the real part of the complex `𝒵` is the real `𝒵` of the real
parts. -/
theorem re_ZC (β : ℝ) (y₀ : Ω → ℂ) (y : ℕ → Ω → ℂ) :
    (fun t ω => (ZC S β y₀ y t ω).re) =
      Zm S β (fun ω => (y₀ ω).re) (fun t ω => (y t ω).re) := by
  funext t ω
  have hl : (lagC y₀ y t ω).re = lagW (fun ω => (y₀ ω).re) (fun t ω => (y t ω).re) t ω := by
    cases t <;> rfl
  simp only [ZC, Zm, Complex.sub_re, Complex.mul_re, Complex.add_re, Complex.one_re,
    Complex.ofReal_re, Complex.one_im, Complex.add_im, Complex.ofReal_im, hl]
  simp [CE]

/-- Woodford (2003), (2.20) (tool): `E_t` of a combination of six integrable variables and a
constant, a.s. -/
theorem E_comb6 (t : ℕ) (a1 a2 a3 a4 a5 a6 k : ℝ) {y1 y2 y3 y4 y5 y6 : Ω → ℝ}
    (i1 : Integrable y1 S.μ) (i2 : Integrable y2 S.μ) (i3 : Integrable y3 S.μ)
    (i4 : Integrable y4 S.μ) (i5 : Integrable y5 S.μ) (i6 : Integrable y6 S.μ) :
    S.E t (fun ω => a1 * y1 ω + a2 * y2 ω + a3 * y3 ω + a4 * y4 ω + a5 * y5 ω + a6 * y6 ω +
      k) =ᵐ[S.μ] fun ω => a1 * S.E t y1 ω + a2 * S.E t y2 ω + a3 * S.E t y3 ω +
        a4 * S.E t y4 ω + a5 * S.E t y5 ω + a6 * S.E t y6 ω + k := by
  have e : (fun ω => a1 * y1 ω + a2 * y2 ω + a3 * y3 ω + a4 * y4 ω + a5 * y5 ω + a6 * y6 ω +
      k) = a1 • y1 + a2 • y2 + a3 • y3 + a4 • y4 + a5 • y5 + a6 • y6 + (fun _ => k) := by
    funext ω; simp
  have j1 := i1.smul a1
  have j2 := i2.smul a2
  have j3 := i3.smul a3
  have j4 := i4.smul a4
  have j5 := i5.smul a5
  have j6 := i6.smul a6
  have jc : Integrable (fun _ : Ω => k) S.μ := integrable_const k
  rw [e]
  filter_upwards [S.E_add (((((j1.add j2).add j3).add j4).add j5).add j6) jc t,
    S.E_add ((((j1.add j2).add j3).add j4).add j5) j6 t,
    S.E_add (((j1.add j2).add j3).add j4) j5 t, S.E_add ((j1.add j2).add j3) j4 t,
    S.E_add (j1.add j2) j3 t, S.E_add j1 j2 t, S.E_smul a1 y1 t, S.E_smul a2 y2 t,
    S.E_smul a3 y3 t, S.E_smul a4 y4 t, S.E_smul a5 y5 t, S.E_smul a6 y6 t]
    with ω h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, Pi.add_apply, h4, Pi.add_apply, h5,
    Pi.add_apply, h6, Pi.add_apply, h7, h8, h9, h10, h11, h12, S.E_const t k]
  simp

/-- Woodford (2003), (2.20): `𝒵` of a combination of six processes plus a constant (with the
combined initial value) is the combination of the `𝒵`s, a.s. -/
theorem Zm_comb6 (β : ℝ) (a1 a2 a3 a4 a5 a6 k : ℝ) {y1 y2 y3 y4 y5 y6 z : ℕ → Ω → ℝ}
    {i1 i2 i3 i4 i5 i6 z₀ : Ω → ℝ}
    (hz : ∀ t ω, z t ω = a1 * y1 t ω + a2 * y2 t ω + a3 * y3 t ω + a4 * y4 t ω +
      a5 * y5 t ω + a6 * y6 t ω + k)
    (hz₀ : ∀ ω, z₀ ω = a1 * i1 ω + a2 * i2 ω + a3 * i3 ω + a4 * i4 ω + a5 * i5 ω +
      a6 * i6 ω + k) (t : ℕ)
    (I1 : Integrable (y1 (t + 1)) S.μ) (I2 : Integrable (y2 (t + 1)) S.μ)
    (I3 : Integrable (y3 (t + 1)) S.μ) (I4 : Integrable (y4 (t + 1)) S.μ)
    (I5 : Integrable (y5 (t + 1)) S.μ) (I6 : Integrable (y6 (t + 1)) S.μ) :
    Zm S β z₀ z t =ᵐ[S.μ] fun ω => a1 * Zm S β i1 y1 t ω + a2 * Zm S β i2 y2 t ω +
      a3 * Zm S β i3 y3 t ω + a4 * Zm S β i4 y4 t ω + a5 * Zm S β i5 y5 t ω +
      a6 * Zm S β i6 y6 t ω := by
  have hf : z (t + 1) = fun ω => a1 * y1 (t + 1) ω + a2 * y2 (t + 1) ω + a3 * y3 (t + 1) ω +
      a4 * y4 (t + 1) ω + a5 * y5 (t + 1) ω + a6 * y6 (t + 1) ω + k := funext (hz (t + 1))
  have hl : ∀ ω, lagW z₀ z t ω = a1 * lagW i1 y1 t ω + a2 * lagW i2 y2 t ω +
      a3 * lagW i3 y3 t ω + a4 * lagW i4 y4 t ω + a5 * lagW i5 y5 t ω +
      a6 * lagW i6 y6 t ω + k := by
    intro ω
    cases t with
    | zero => exact hz₀ ω
    | succ t => exact hz t ω
  filter_upwards [E_comb6 t a1 a2 a3 a4 a5 a6 k I1 I2 I3 I4 I5 I6] with ω h
  simp only [Zm]
  rw [hf, h, hl ω, hz t ω]
  ring

/-- Woodford (2003), (2.20): `𝒵` of an adapted process with an initial value known at `0` is
adapted. -/
theorem Zm_adapted (β : ℝ) {y₀ : Ω → ℝ} (h0 : StronglyMeasurable[S.𝓕 0] y₀) {y : ℕ → Ω → ℝ}
    (hy : StronglyAdapted S.𝓕 y) : StronglyAdapted S.𝓕 (Zm S β y₀ y) := by
  intro t
  have hl : StronglyMeasurable[S.𝓕 t] (lagW y₀ y t) := by
    cases t with
    | zero => exact h0
    | succ t => exact (hy t).mono (S.𝓕.mono (Nat.le_succ t))
  exact (((hy t).const_mul _).sub ((S.stronglyMeasurable_E t _).const_mul _)).sub hl

/-- Woodford (2003), (2.20): `𝒵` of a bounded process with a bounded initial value is bounded. -/
theorem Zm_bdd (β : ℝ) (hβ : 0 ≤ β) {y₀ : Ω → ℝ} {B : ℝ} (h0 : ∀ᵐ ω ∂S.μ, |y₀ ω| ≤ B)
    {y : ℕ → Ω → ℝ} (hy : S.BddProc y) : S.BddProc (Zm S β y₀ y) := by
  obtain ⟨M, hM⟩ := hy
  refine ⟨(1 + β) * M + β * M + max B M, fun t => ?_⟩
  have hl : ∀ᵐ ω ∂S.μ, |lagW y₀ y t ω| ≤ max B M := by
    cases t with
    | zero => exact h0.mono fun ω h => h.trans (le_max_left _ _)
    | succ t => exact (hM t).mono fun ω h => h.trans (le_max_right _ _)
  filter_upwards [hM t, S.abs_E_le (hM (t + 1)) t, hl] with ω h1 h2 h3
  simp only [Zm]
  refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add ?_ ?_)) h3)
  · rw [abs_mul, abs_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_left h1 (by linarith)
  · rw [abs_mul, abs_of_nonneg hβ]
    exact mul_le_mul_of_nonneg_left h2 hβ

/-- Woodford (2003), (2.20) (tool): a combination of six bounded adapted processes plus a
constant is bounded and adapted. -/
theorem comb6M (a1 a2 a3 a4 a5 a6 k : ℝ) {y1 y2 y3 y4 y5 y6 z : ℕ → Ω → ℝ}
    (h1 : StronglyAdapted S.𝓕 y1) (h2 : StronglyAdapted S.𝓕 y2) (h3 : StronglyAdapted S.𝓕 y3)
    (h4 : StronglyAdapted S.𝓕 y4) (h5 : StronglyAdapted S.𝓕 y5) (h6 : StronglyAdapted S.𝓕 y6)
    (b1 : S.BddProc y1) (b2 : S.BddProc y2) (b3 : S.BddProc y3) (b4 : S.BddProc y4)
    (b5 : S.BddProc y5) (b6 : S.BddProc y6)
    (hz : ∀ t ω, z t ω = a1 * y1 t ω + a2 * y2 t ω + a3 * y3 t ω + a4 * y4 t ω +
      a5 * y5 t ω + a6 * y6 t ω + k) : StronglyAdapted S.𝓕 z ∧ S.BddProc z := by
  obtain ⟨M1, hM1⟩ := b1
  obtain ⟨M2, hM2⟩ := b2
  obtain ⟨M3, hM3⟩ := b3
  obtain ⟨M4, hM4⟩ := b4
  obtain ⟨M5, hM5⟩ := b5
  obtain ⟨M6, hM6⟩ := b6
  refine ⟨fun t => ?_, ⟨|a1| * M1 + |a2| * M2 + |a3| * M3 + |a4| * M4 + |a5| * M5 +
    |a6| * M6 + |k|, fun t => ?_⟩⟩
  · have e : z t = fun ω => a1 * y1 t ω + a2 * y2 t ω + a3 * y3 t ω + a4 * y4 t ω +
        a5 * y5 t ω + a6 * y6 t ω + k := funext (hz t)
    rw [e]
    exact ((((((h1 t).const_mul _).add ((h2 t).const_mul _)).add ((h3 t).const_mul _)).add
      ((h4 t).const_mul _)).add ((h5 t).const_mul _)).add ((h6 t).const_mul _) |>.add
      stronglyMeasurable_const
  · filter_upwards [hM1 t, hM2 t, hM3 t, hM4 t, hM5 t, hM6 t] with ω e1 e2 e3 e4 e5 e6
    rw [hz]
    have e : ∀ (a : ℝ) (v : ℝ) (M : ℝ), |v| ≤ M → |a * v| ≤ |a| * M := fun a v M h => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left h (abs_nonneg a)
    have := e a1 _ _ e1
    have := e a2 _ _ e2
    have := e a3 _ _ e3
    have := e a4 _ _ e4
    have := e a5 _ _ e5
    have := e a6 _ _ e6
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ?_ le_rfl
    refine (abs_add_le _ _).trans (add_le_add ?_ (by assumption))
    refine (abs_add_le _ _).trans (add_le_add ?_ (by assumption))
    refine (abs_add_le _ _).trans (add_le_add ?_ (by assumption))
    refine (abs_add_le _ _).trans (add_le_add ?_ (by assumption))
    exact (abs_add_le _ _).trans (add_le_add (by assumption) (by assumption))

/-- Woodford (2003), (2.20): the real third-order equation in `𝒵`, a.s. -/
def RCub (β p3 p2 p1 p0 : ℝ) (w₀ s₁ s₂ : Ω → ℝ) (F w : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ∀ᵐ ω ∂S.μ, p3 * Zm S β s₂ (Zm S β s₁ (Zm S β w₀ w)) t ω +
    p2 * Zm S β s₁ (Zm S β w₀ w) t ω + p1 * Zm S β w₀ w t ω + p0 * w t ω = F t ω

/-- **Woodford (2003), (2.20) (the real cubic equation on a probability space)**: with Vieta's
relations for `p₃Z³ + p₂Z² + p₁Z + p₀` and a stable `μᵢ` for each root, a bounded adapted forcing
and constant initial values give a bounded adapted solution (the real part of the complex
solution of `TidyR5bCondExpC.cubic_exists`). -/
theorem cubicR_exists {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {p3 p2 p1 p0 : ℝ} (hp3 : p3 ≠ 0)
    {Z1 Z2 Z3 μ1 μ2 μ3 : ℂ} (hv1 : Z1 + Z2 + Z3 = ((-(p2 / p3) : ℝ) : ℂ))
    (hv2 : Z1 * Z2 + Z1 * Z3 + Z2 * Z3 = ((p1 / p3 : ℝ) : ℂ))
    (hv3 : Z1 * Z2 * Z3 = ((-(p0 / p3) : ℝ) : ℂ))
    (r1 : (β : ℂ) * μ1 ^ 2 - (1 + β - Z1) * μ1 + 1 = 0) (n1 : ‖μ1‖ < 1)
    (r2 : (β : ℂ) * μ2 ^ 2 - (1 + β - Z2) * μ2 + 1 = 0) (n2 : ‖μ2‖ < 1)
    (r3 : (β : ℂ) * μ3 ^ 2 - (1 + β - Z3) * μ3 + 1 = 0) (n3 : ‖μ3‖ < 1)
    {F : ℕ → Ω → ℝ} (hFa : StronglyAdapted S.𝓕 F) (hFb : S.BddProc F) (cw c1 c2 : ℝ) :
    ∃ w, StronglyAdapted S.𝓕 w ∧ S.BddProc w ∧
      RCub (S := S) β p3 p2 p1 p0 (fun _ => cw) (fun _ => c1) (fun _ => c2) F w := by
  obtain ⟨M, hM⟩ := hFb
  set H : ℕ → Ω → ℂ := fun t ω => ((F t ω / p3 : ℝ) : ℂ) with hH
  have hHa : AdC S H := fun t => ⟨by
    change StronglyMeasurable[S.𝓕 t] (fun ω => ((F t ω / p3 : ℝ) : ℂ).re)
    simp only [Complex.ofReal_re, div_eq_mul_inv]
    exact (hFa t).mul_const _, by
    change StronglyMeasurable[S.𝓕 t] (fun ω => ((F t ω / p3 : ℝ) : ℂ).im)
    simp only [Complex.ofReal_im]
    exact stronglyMeasurable_const⟩
  have hHb : BdC S H := ⟨M / |p3|, fun t => (hM t).mono fun ω h => by
    simp only [hH, Complex.norm_real, Real.norm_eq_abs, abs_div]
    exact div_le_div_of_nonneg_right h (abs_nonneg _)⟩
  have kc : ∀ c : ℝ, KnownC S 0 (fun _ => (c : ℂ)) := fun c => KnownC.const 0 _
  set B := max (max |cw| |c1|) |c2| with hB
  have bc : ∀ c : ℝ, |c| ≤ B → ∀ᵐ ω ∂S.μ, ‖(fun _ : Ω => (c : ℂ)) ω‖ ≤ B := fun c hc =>
    Eventually.of_forall fun ω => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hc
  obtain ⟨wc, ha, ⟨K, hb⟩, hcub⟩ := cubic_exists hβ0 hβ1 r1 n1 r2 n2 r3 n3 hHa hHb
    (kc cw) (kc c1) (kc c2) (bc cw ((le_max_left _ _).trans (le_max_left _ _)))
    (bc c1 ((le_max_right _ _).trans (le_max_left _ _))) (bc c2 (le_max_right _ _))
  rw [hv1, hv2, hv3] at hcub
  refine ⟨fun t ω => (wc t ω).re, fun t => (ha t).1, ⟨K, fun t => (hb t).mono fun ω h =>
    (Complex.abs_re_le_norm _).trans h⟩, fun t => ?_⟩
  filter_upwards [hcub t] with ω h
  have hre := congrArg Complex.re h
  have e1 := congrFun (congrFun (re_ZC (S := S) β (fun _ => (cw : ℂ)) wc) t) ω
  have e2 := congrFun (congrFun (re_ZC (S := S) β (fun _ => (c1 : ℂ))
    (ZC S β (fun _ => (cw : ℂ)) wc)) t) ω
  have e3 := congrFun (congrFun (re_ZC (S := S) β (fun _ => (c2 : ℂ))
    (ZC S β (fun _ => (c1 : ℂ)) (ZC S β (fun _ => (cw : ℂ)) wc))) t) ω
  have f1 := re_ZC (S := S) β (fun _ => (cw : ℂ)) wc
  have f2 := re_ZC (S := S) β (fun _ => (c1 : ℂ)) (ZC S β (fun _ => (cw : ℂ)) wc)
  simp only [Complex.ofReal_re] at e1 e2 e3 f1 f2
  rw [f1] at e2 f2
  rw [f2] at e3
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, hH] at hre
  rw [e1, e2, e3] at hre
  field_simp at hre
  linear_combination hre

/-! ### From the cubic equation back to the plan and multipliers -/

variable (S) in
/-- Woodford (2003), (2.20): the forcing of the cubic equation in the real wage
(`InflTargetStickyWages.forcingF` with conditional expectations). -/
noncomputable def forcingFm (P : SW) (u wn : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => ca0 P * Zm S P.beta (fun _ => 0) wn t ω +
    P.lx * (P.xip + P.xiw) * Zm S P.beta (fun _ => 0) (Zm S P.beta (fun _ => 0) wn) t ω +
    (P.kw - P.kp) * P.lx * Zm S P.beta (fun _ => 0) (Zm S P.beta (fun _ => 0) u) t ω +
    (P.xip + P.xiw) * ca0 P * wn t ω +
    P.lx * (P.xip + P.xiw) ^ 2 * Zm S P.beta (fun _ => 0) wn t ω +
    (P.xip + P.xiw) * (P.kw - P.kp) * P.lx * Zm S P.beta (fun _ => 0) u t ω -
    (P.kw - P.kp) * cb0 P * wn t ω

variable (S) in
/-- Woodford (2003), (2.13) and (2.20): the output gap implied by the real wage. -/
noncomputable def xOfM (P : SW) (w₀ : Ω → ℝ) (u wn w : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => (Zm S P.beta w₀ w t ω + (P.xip + P.xiw) * (w t ω - wn t ω)) / (P.kw - P.kp) -
    u t ω

variable (S) in
/-- Woodford (2003), (2.18)–(2.20): `g = ξ_p φ_p − ξ_w φ_w` implied by the real wage. -/
noncomputable def gOfM (P : SW) (w₀ mp₀ mw₀ : Ω → ℝ) (u wn w : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => (P.lx * Zm S P.beta (initS1 P w₀ mp₀ mw₀) (Zm S P.beta w₀ w) t ω +
    ca1 P * Zm S P.beta w₀ w t ω + ca0 P * w t ω - ca0 P * wn t ω -
    P.lx * (P.xip + P.xiw) * Zm S P.beta (fun _ => 0) wn t ω -
    (P.kw - P.kp) * P.lx * Zm S P.beta (fun _ => 0) u t ω) / (P.kw - P.kp) ^ 2

variable (S) in
/-- Woodford (2003), (2.18)–(2.19): the multiplier `φ_p`. -/
noncomputable def mpOfM (P : SW) (w₀ mp₀ mw₀ : Ω → ℝ) (u wn w : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => (P.xiw * (P.lx * (xOfM S P w₀ u wn w t ω - P.xstar)) +
    P.kw * gOfM S P w₀ mp₀ mw₀ u wn w t ω) / Dst P

variable (S) in
/-- Woodford (2003), (2.18)–(2.19): the multiplier `φ_w`. -/
noncomputable def mwOfM (P : SW) (w₀ mp₀ mw₀ : Ω → ℝ) (u wn w : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => (P.xip * (P.lx * (xOfM S P w₀ u wn w t ω - P.xstar)) -
    P.kp * gOfM S P w₀ mp₀ mw₀ u wn w t ω) / Dst P

variable (S) in
/-- Woodford (2003), (2.19): the multiplier `υ_t = E_t ∑ βʲ g_{t+j}`. -/
noncomputable def upsOfM (P : SW) (w₀ mp₀ mw₀ : Ω → ℝ) (u wn w : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  S.forwardSol P.beta (gOfM S P w₀ mp₀ mw₀ u wn w)

variable (S) in
/-- Woodford (2003), (2.16): price inflation `π = −(Δφ_p + υ)/λ_p`. -/
noncomputable def piOfM (P : SW) (w₀ mp₀ mw₀ : Ω → ℝ) (u wn w : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => -(mpOfM S P w₀ mp₀ mw₀ u wn w t ω - lagW mp₀ (mpOfM S P w₀ mp₀ mw₀ u wn w) t ω +
    upsOfM S P w₀ mp₀ mw₀ u wn w t ω) / P.lp

variable (S) in
/-- Woodford (2003), (2.17): wage inflation `π^w = −(Δφ_w − υ)/λ_w`. -/
noncomputable def piwOfM (P : SW) (w₀ mp₀ mw₀ : Ω → ℝ) (u wn w : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => -(mwOfM S P w₀ mp₀ mw₀ u wn w t ω - lagW mw₀ (mwOfM S P w₀ mp₀ mw₀ u wn w) t ω -
    upsOfM S P w₀ mp₀ mw₀ u wn w t ω) / P.lw

/-- **Woodford (2003), (2.11)–(2.19) ⇐ the cubic equation, on a probability space**: if the real
wage `w` is a bounded adapted a.s. solution of the cubic equation with the initial values implied
by constant `(w_{t₀−1}, φ_{p,t₀−1}, φ_{w,t₀−1}) = (c_w, a, b)`, then
`(piOfM, piwOfM, xOfM, w)` is a bounded adapted plan satisfying (2.11)–(2.13) a.s., and with the
bounded adapted multipliers `(mpOfM, mwOfM, upsOfM)` the first-order conditions hold a.s. -/
theorem cubic_imp_focM {P : SW} (hβ0 : 0 ≤ P.beta) (hβ1 : P.beta < 1) (hlx : P.lx ≠ 0)
    (hlp : P.lp ≠ 0) (hlw : P.lw ≠ 0) (hc : P.kw - P.kp ≠ 0) (hD : Dst P ≠ 0) (cw a b : ℝ)
    {u wn w : ℕ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u) (hub : S.BddProc u)
    (hwna : StronglyAdapted S.𝓕 wn) (hwnb : S.BddProc wn)
    (hcub : RCub (S := S) P.beta P.lx (cp2 P) (cp1 P) (cp0 P) (fun _ => cw)
      (initS1 P (fun _ => cw) (fun _ => a) (fun _ => b))
      (initS2 P (fun _ => cw) (fun _ => a) (fun _ => b)) (forcingFm S P u wn) w)
    (hwa : StronglyAdapted S.𝓕 w) (hwb : S.BddProc w) :
    PlanSWM S P (fun _ => cw) u wn
        (piOfM S P (fun _ => cw) (fun _ => a) (fun _ => b) u wn w)
        (piwOfM S P (fun _ => cw) (fun _ => a) (fun _ => b) u wn w)
        (xOfM S P (fun _ => cw) u wn w) w ∧
      FOCswM S P (fun _ => a) (fun _ => b)
        (piOfM S P (fun _ => cw) (fun _ => a) (fun _ => b) u wn w)
        (piwOfM S P (fun _ => cw) (fun _ => a) (fun _ => b) u wn w)
        (xOfM S P (fun _ => cw) u wn w)
        (mpOfM S P (fun _ => cw) (fun _ => a) (fun _ => b) u wn w)
        (mwOfM S P (fun _ => cw) (fun _ => a) (fun _ => b) u wn w)
        (upsOfM S P (fun _ => cw) (fun _ => a) (fun _ => b) u wn w) := by
  set w₀ : Ω → ℝ := fun _ => cw with hw₀
  set mp₀ : Ω → ℝ := fun _ => a with hmp₀
  set mw₀ : Ω → ℝ := fun _ => b with hmw₀
  set c := P.kw - P.kp with hcdef
  set ξ := P.xip + P.xiw with hξ
  set s1 := initS1 P w₀ mp₀ mw₀ with hs1
  set s2 := initS2 P w₀ mp₀ mw₀ with hs2
  set i0 : Ω → ℝ := fun _ => 0 with hi0
  have hβa : |P.beta| < 1 := by rw [abs_of_nonneg hβ0]; exact hβ1
  have It : ∀ {y : ℕ → Ω → ℝ}, StronglyAdapted S.𝓕 y → S.BddProc y → ∀ t,
      Integrable (y t) S.μ := fun ha hb t => integrable_of_adapted S ha hb t
  have cK : ∀ k : ℝ, StronglyMeasurable[S.𝓕 0] (fun _ : Ω => k) := fun k =>
    stronglyMeasurable_const
  have cB : ∀ k : ℝ, ∀ᵐ ω ∂S.μ, |(fun _ : Ω => k) ω| ≤ |k| := fun k =>
    Eventually.of_forall fun ω => le_rfl
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, s1 = fun _ => K1 :=
    ⟨(P.kw - P.kp) / P.lx * (P.kp * a + P.kw * b + P.lx * P.xstar) - (P.xip + P.xiw) * cw,
      by funext ω; simp only [hs1, initS1, hw₀, hmp₀, hmw₀]⟩
  have s1K : StronglyMeasurable[S.𝓕 0] s1 := by rw [hK1]; exact stronglyMeasurable_const
  have s1B : ∀ᵐ ω ∂S.μ, |s1 ω| ≤ |K1| := Eventually.of_forall fun ω => by rw [hK1]
  set z0 : ℕ → Ω → ℝ := fun _ _ => 0 with hz0
  have z0a : StronglyAdapted S.𝓕 z0 := fun t => stronglyMeasurable_const
  have z0b : S.BddProc z0 := ⟨0, fun t => Eventually.of_forall fun ω => by simp [hz0]⟩
  -- the processes
  set W1 := Zm S P.beta w₀ w with hW1
  set W2 := Zm S P.beta s1 W1 with hW2
  set W3 := Zm S P.beta s2 W2 with hW3
  set Zn := Zm S P.beta i0 wn with hZn
  set Zu := Zm S P.beta i0 u with hZu
  set ZZn := Zm S P.beta i0 Zn with hZZn
  set ZZu := Zm S P.beta i0 Zu with hZZu
  have aW1 : StronglyAdapted S.𝓕 W1 := Zm_adapted P.beta (cK cw) hwa
  have bW1 : S.BddProc W1 := Zm_bdd P.beta hβ0 (cB cw) hwb
  have aW2 : StronglyAdapted S.𝓕 W2 := Zm_adapted P.beta s1K aW1
  have bW2 : S.BddProc W2 := Zm_bdd P.beta hβ0 s1B bW1
  have aZn : StronglyAdapted S.𝓕 Zn := Zm_adapted P.beta (cK 0) hwna
  have bZn : S.BddProc Zn := Zm_bdd P.beta hβ0 (cB 0) hwnb
  have aZu : StronglyAdapted S.𝓕 Zu := Zm_adapted P.beta (cK 0) hua
  have bZu : S.BddProc Zu := Zm_bdd P.beta hβ0 (cB 0) hub
  set x := xOfM S P w₀ u wn w with hx
  set g := gOfM S P w₀ mp₀ mw₀ u wn w with hg
  set mp := mpOfM S P w₀ mp₀ mw₀ u wn w with hmp
  set mw := mwOfM S P w₀ mp₀ mw₀ u wn w with hmw
  set ups := upsOfM S P w₀ mp₀ mw₀ u wn w with hups
  set π := piOfM S P w₀ mp₀ mw₀ u wn w with hπ
  set πw := piwOfM S P w₀ mp₀ mw₀ u wn w with hπw
  obtain ⟨xa, xb⟩ := comb6M (S := S) (1 / c) (ξ / c) (-(ξ / c)) (-1) 0 0 0 aW1 hwa hwna hua
    hua hua bW1 hwb hwnb hub hub hub (z := x) (fun t ω => by
      simp only [hx, xOfM, ← hcdef, ← hξ]; field_simp; ring)
  obtain ⟨ga, gb⟩ := comb6M (S := S) (P.lx / c ^ 2) (ca1 P / c ^ 2) (ca0 P / c ^ 2)
    (-(ca0 P / c ^ 2)) (-(P.lx * ξ / c ^ 2)) (-(c * P.lx / c ^ 2)) 0 aW2 aW1 hwa hwna aZn aZu
    bW2 bW1 hwb hwnb bZn bZu (z := g) (fun t ω => by
      simp only [hg, gOfM, ← hcdef, ← hξ, ← hs1]; field_simp; ring)
  obtain ⟨mpa, mpb⟩ := comb6M (S := S) (P.xiw * P.lx / Dst P) (P.kw / Dst P) 0 0 0 0
    (-(P.xiw * P.lx * P.xstar / Dst P)) xa ga xa xa xa xa xb gb xb xb xb xb (z := mp)
    (fun t ω => by simp only [hmp, mpOfM]; field_simp; ring)
  obtain ⟨mwa, mwb⟩ := comb6M (S := S) (P.xip * P.lx / Dst P) (-(P.kp / Dst P)) 0 0 0 0
    (-(P.xip * P.lx * P.xstar / Dst P)) xa ga xa xa xa xa xb gb xb xb xb xb (z := mw)
    (fun t ω => by simp only [hmw, mwOfM]; field_simp; ring)
  obtain ⟨G, hG⟩ := gb
  have upsa : StronglyAdapted S.𝓕 ups := S.forwardSol_adapted P.beta g
  have upsb : S.BddProc ups := S.forwardSol_bdd hβa hG
  have upss := S.forwardSol_solves hβa ga hG
  have lmpa : StronglyAdapted S.𝓕 (lagW mp₀ mp) := fun t => by
    cases t with
    | zero => exact (cK a).mono (S.𝓕.mono (Nat.zero_le 0))
    | succ t => exact (mpa t).mono (S.𝓕.mono (Nat.le_succ t))
  have lmwa : StronglyAdapted S.𝓕 (lagW mw₀ mw) := fun t => by
    cases t with
    | zero => exact (cK b).mono (S.𝓕.mono (Nat.zero_le 0))
    | succ t => exact (mwa t).mono (S.𝓕.mono (Nat.le_succ t))
  obtain ⟨Mp, hMp⟩ := mpb
  obtain ⟨Mw, hMw⟩ := mwb
  have lmpb : S.BddProc (lagW mp₀ mp) := ⟨max |a| Mp, fun t => by
    cases t with
    | zero => exact Eventually.of_forall fun ω => le_max_left _ _
    | succ t => exact (hMp t).mono fun ω h => h.trans (le_max_right _ _)⟩
  have lmwb : S.BddProc (lagW mw₀ mw) := ⟨max |b| Mw, fun t => by
    cases t with
    | zero => exact Eventually.of_forall fun ω => le_max_left _ _
    | succ t => exact (hMw t).mono fun ω h => h.trans (le_max_right _ _)⟩
  obtain ⟨πa, πb⟩ := comb6M (S := S) (-1 / P.lp) (1 / P.lp) (-1 / P.lp) 0 0 0 0 mpa lmpa
    upsa upsa upsa upsa ⟨Mp, hMp⟩ lmpb upsb upsb upsb upsb (z := π)
    (fun t ω => by simp only [hπ, piOfM]; field_simp; ring)
  obtain ⟨πwa, πwb⟩ := comb6M (S := S) (-1 / P.lw) (1 / P.lw) (1 / P.lw) 0 0 0 0 mwa lmwa
    upsa upsa upsa upsa ⟨Mw, hMw⟩ lmwb upsb upsb upsb upsb (z := πw)
    (fun t ω => by simp only [hπw, piwOfM]; field_simp; ring)
  have hD' : P.kp * P.xiw + P.kw * P.xip ≠ 0 := hD
  have hDi : (P.kp * P.xiw + P.kw * P.xip) * (P.kp * P.xiw + P.kw * P.xip)⁻¹ = 1 :=
    mul_inv_cancel₀ hD'
  have IW1 := It aW1 bW1
  have IW2 := It aW2 bW2
  have Iw := It hwa hwb
  have Iwn := It hwna hwnb
  have Iu := It hua hub
  have IZn := It aZn bZn
  have IZu := It aZu bZu
  have Iz0 := It z0a z0b
  have Ix := It xa xb
  have Ig := It ga ⟨G, hG⟩
  have Imp := It mpa ⟨Mp, hMp⟩
  have Imw := It mwa ⟨Mw, hMw⟩
  have Iups := It upsa upsb
  have Iπ := It πa πb
  have Iπw := It πwa πwb
  have Ilx : ∀ t, Integrable (fun ω => P.lx * (x t ω - P.xstar)) S.μ := fun t =>
    ((Ix t).sub (integrable_const _)).const_mul _
  -- basic identities
  have hS : ∀ t ω, c * (x t ω + u t ω) = W1 t ω + ξ * (w t ω - wn t ω) := fun t ω => by
    simp only [hx, xOfM, ← hcdef, ← hξ]; field_simp; ring
  have hcg : ∀ t ω, c ^ 2 * g t ω = P.lx * W2 t ω + ca1 P * W1 t ω + ca0 P * w t ω -
      ca0 P * wn t ω - P.lx * ξ * Zn t ω - c * P.lx * Zu t ω := fun t ω => by
    simp only [hg, gOfM, ← hcdef, ← hξ, ← hs1]; field_simp; rfl
  have hgmp : ∀ t ω, P.xip * mp t ω - P.xiw * mw t ω = g t ω := fun t ω => by
    simp only [hmp, mpOfM, hmw, mwOfM, Dst, ← hg]
    linear_combination (g t ω) * hDi
  have ZX : ∀ t, ∀ᵐ ω ∂S.μ, c * Zm S P.beta (fun ω => P.kp * mp₀ ω + P.kw * mw₀ ω)
      (fun t ω => P.lx * (x t ω - P.xstar)) t ω =
      P.lx * W2 t ω + P.lx * ξ * W1 t ω - P.lx * ξ * Zn t ω - c * P.lx * Zu t ω := by
    intro t
    have := Zm_comb6 (S := S) P.beta (P.lx / c) (P.lx * ξ / c) (-(P.lx * ξ / c)) (-P.lx) 0 0
      (-(P.lx * P.xstar)) (y1 := W1) (y2 := w) (y3 := wn) (y4 := u) (y5 := z0) (y6 := z0)
      (i1 := s1) (i2 := w₀) (i3 := i0) (i4 := i0) (i5 := i0) (i6 := i0)
      (z := fun t ω => P.lx * (x t ω - P.xstar))
      (z₀ := fun ω => P.kp * mp₀ ω + P.kw * mw₀ ω) (fun t ω => ?_) (fun ω => ?_) t
      (IW1 (t + 1)) (Iw (t + 1)) (Iwn (t + 1)) (Iu (t + 1)) (Iz0 (t + 1)) (Iz0 (t + 1))
    · filter_upwards [this] with ω h
      rw [h]; field_simp; ring
    · have h := hS t ω
      field_simp
      linear_combination P.lx * h
    · simp only [hs1, initS1, hi0, ← hcdef, ← hξ]
      field_simp
      ring
  have ZG : ∀ t, ∀ᵐ ω ∂S.μ, c ^ 2 * Zm S P.beta (fun ω => P.xip * mp₀ ω - P.xiw * mw₀ ω) g t ω =
      P.lx * W3 t ω + ca1 P * W2 t ω + ca0 P * W1 t ω - ca0 P * Zn t ω - P.lx * ξ * ZZn t ω -
        c * P.lx * ZZu t ω := by
    intro t
    have := Zm_comb6 (S := S) P.beta (P.lx / c ^ 2) (ca1 P / c ^ 2) (ca0 P / c ^ 2)
      (-(ca0 P / c ^ 2)) (-(P.lx * ξ / c ^ 2)) (-(c * P.lx / c ^ 2)) 0
      (y1 := W2) (y2 := W1) (y3 := w) (y4 := wn) (y5 := Zn) (y6 := Zu)
      (i1 := s2) (i2 := s1) (i3 := w₀) (i4 := i0) (i5 := i0) (i6 := i0)
      (z := g) (z₀ := fun ω => P.xip * mp₀ ω - P.xiw * mw₀ ω) (fun t ω => ?_) (fun ω => ?_) t
      (IW2 (t + 1)) (IW1 (t + 1)) (Iw (t + 1)) (Iwn (t + 1)) (IZn (t + 1)) (IZu (t + 1))
    · filter_upwards [this] with ω h
      rw [h]; field_simp; ring
    · have := hcg t ω
      field_simp
      linear_combination this
    · simp only [hs2, initS2, hi0, ← hcdef, ← hs1]
      field_simp
      ring
  have Zmp : ∀ t, ∀ᵐ ω ∂S.μ, Dst P * Zm S P.beta mp₀ mp t ω = P.xiw * Zm S P.beta
      (fun ω => P.kp * mp₀ ω + P.kw * mw₀ ω) (fun t ω => P.lx * (x t ω - P.xstar)) t ω +
      P.kw * Zm S P.beta (fun ω => P.xip * mp₀ ω - P.xiw * mw₀ ω) g t ω := by
    intro t
    have := Zm_comb6 (S := S) P.beta (P.xiw / Dst P) (P.kw / Dst P) 0 0 0 0 0
      (y1 := fun t ω => P.lx * (x t ω - P.xstar)) (y2 := g) (y3 := z0) (y4 := z0) (y5 := z0)
      (y6 := z0) (i1 := fun ω => P.kp * mp₀ ω + P.kw * mw₀ ω)
      (i2 := fun ω => P.xip * mp₀ ω - P.xiw * mw₀ ω) (i3 := i0) (i4 := i0) (i5 := i0)
      (i6 := i0) (z := mp) (z₀ := mp₀) (fun t ω => ?_) (fun ω => ?_) t
      (Ilx (t + 1)) (Ig (t + 1)) (Iz0 (t + 1)) (Iz0 (t + 1)) (Iz0 (t + 1)) (Iz0 (t + 1))
    · filter_upwards [this] with ω h
      rw [h]; field_simp; ring
    · simp only [hmp, mpOfM, ← hx, ← hg]; field_simp; ring
    · simp only [Dst]; linear_combination (-mp₀ ω) * hDi
  have Zmw : ∀ t, ∀ᵐ ω ∂S.μ, Dst P * Zm S P.beta mw₀ mw t ω = P.xip * Zm S P.beta
      (fun ω => P.kp * mp₀ ω + P.kw * mw₀ ω) (fun t ω => P.lx * (x t ω - P.xstar)) t ω -
      P.kp * Zm S P.beta (fun ω => P.xip * mp₀ ω - P.xiw * mw₀ ω) g t ω := by
    intro t
    have := Zm_comb6 (S := S) P.beta (P.xip / Dst P) (-(P.kp / Dst P)) 0 0 0 0 0
      (y1 := fun t ω => P.lx * (x t ω - P.xstar)) (y2 := g) (y3 := z0) (y4 := z0) (y5 := z0)
      (y6 := z0) (i1 := fun ω => P.kp * mp₀ ω + P.kw * mw₀ ω)
      (i2 := fun ω => P.xip * mp₀ ω - P.xiw * mw₀ ω) (i3 := i0) (i4 := i0) (i5 := i0)
      (i6 := i0) (z := mw) (z₀ := mw₀) (fun t ω => ?_) (fun ω => ?_) t
      (Ilx (t + 1)) (Ig (t + 1)) (Iz0 (t + 1)) (Iz0 (t + 1)) (Iz0 (t + 1)) (Iz0 (t + 1))
    · filter_upwards [this] with ω h
      rw [h]; field_simp; ring
    · simp only [hmw, mwOfM, ← hx, ← hg]; field_simp; ring
    · simp only [Dst]; linear_combination (-mw₀ ω) * hDi
  -- (G) and (H)
  have Gm : ∀ t, ∀ᵐ ω ∂S.μ, Zm S P.beta (fun ω => P.kp * mp₀ ω + P.kw * mw₀ ω)
      (fun t ω => P.lx * (x t ω - P.xstar)) t ω = c * g t ω -
      P.lp * P.kp * (P.kp * (x t ω + u t ω) + P.xip * (w t ω - wn t ω)) -
      P.lw * P.kw * (P.kw * (x t ω + u t ω) + P.xiw * (wn t ω - w t ω)) := by
    intro t
    filter_upwards [ZX t] with ω h1
    have h2 := hcg t ω
    have h3 := hS t ω
    have : c * (Zm S P.beta (fun ω => P.kp * mp₀ ω + P.kw * mw₀ ω)
      (fun t ω => P.lx * (x t ω - P.xstar)) t ω - (c * g t ω -
      P.lp * P.kp * (P.kp * (x t ω + u t ω) + P.xip * (w t ω - wn t ω)) -
      P.lw * P.kw * (P.kw * (x t ω + u t ω) + P.xiw * (wn t ω - w t ω)))) = 0 := by
      simp only [ca1, ca0, Dst] at h2
      rw [hcdef, hξ] at *
      linear_combination h1 - h2 + (P.lp * P.kp ^ 2 + P.lw * P.kw ^ 2) * h3
    have := (mul_eq_zero.1 this).resolve_left hc
    linarith
  have Hm : ∀ t, ∀ᵐ ω ∂S.μ, Zm S P.beta (fun ω => P.xip * mp₀ ω - P.xiw * mw₀ ω) g t ω =
      -(P.lp * P.xip * (P.kp * (x t ω + u t ω) + P.xip * (w t ω - wn t ω))) +
      P.lw * P.xiw * (P.kw * (x t ω + u t ω) + P.xiw * (wn t ω - w t ω)) - ξ * g t ω := by
    intro t
    filter_upwards [ZG t, hcub t] with ω h1 h4'
    have h2 := hcg t ω
    have h3 := hS t ω
    have h4 : P.lx * W3 t ω + cp2 P * W2 t ω + cp1 P * W1 t ω + cp0 P * w t ω =
        ca0 P * Zn t ω + P.lx * ξ * ZZn t ω + c * P.lx * ZZu t ω + ξ * ca0 P * wn t ω +
        P.lx * ξ ^ 2 * Zn t ω + ξ * c * P.lx * Zu t ω - c * cb0 P * wn t ω := h4'
    have : c ^ 2 * (Zm S P.beta (fun ω => P.xip * mp₀ ω - P.xiw * mw₀ ω) g t ω -
      (-(P.lp * P.xip * (P.kp * (x t ω + u t ω) + P.xip * (w t ω - wn t ω))) +
      P.lw * P.xiw * (P.kw * (x t ω + u t ω) + P.xiw * (wn t ω - w t ω)) - ξ * g t ω)) =
        0 := by
      simp only [cp2, cp1, cp0, ca1, ca0, cb0, Dst] at h1 h2 h4
      rw [hcdef, hξ] at *
      linear_combination h1 + (P.xip + P.xiw) * h2 + h4 -
        (P.kw - P.kp) * (P.lw * P.xiw * P.kw - P.lp * P.xip * P.kp) * h3
    have := (mul_eq_zero.1 this).resolve_left (pow_ne_zero 2 hc)
    linarith
  have E1 : ∀ t, ∀ᵐ ω ∂S.μ, Zm S P.beta mp₀ mp t ω + g t ω =
      -(P.lp * (P.kp * (x t ω + u t ω) + P.xip * (w t ω - wn t ω))) := by
    intro t
    filter_upwards [Zmp t, Gm t, Hm t] with ω h1 h2 h3
    have : Dst P * (Zm S P.beta mp₀ mp t ω + g t ω +
        P.lp * (P.kp * (x t ω + u t ω) + P.xip * (w t ω - wn t ω))) = 0 := by
      simp only [Dst] at *
      rw [hcdef, hξ] at *
      linear_combination h1 + P.xiw * h2 + P.kw * h3
    have := (mul_eq_zero.1 this).resolve_left hD
    linarith
  have E2 : ∀ t, ∀ᵐ ω ∂S.μ, Zm S P.beta mw₀ mw t ω - g t ω =
      -(P.lw * (P.kw * (x t ω + u t ω) + P.xiw * (wn t ω - w t ω))) := by
    intro t
    filter_upwards [Zmw t, Gm t, Hm t] with ω h1 h2 h3
    have : Dst P * (Zm S P.beta mw₀ mw t ω - g t ω +
        P.lw * (P.kw * (x t ω + u t ω) + P.xiw * (wn t ω - w t ω))) = 0 := by
      simp only [Dst] at *
      rw [hcdef, hξ] at *
      linear_combination h1 + P.xip * h2 - P.kp * h3
    have := (mul_eq_zero.1 this).resolve_left hD
    linarith
  -- the first-order conditions
  have f1 : ∀ t ω, P.lp * π t ω + mp t ω - lagW mp₀ mp t ω + ups t ω = 0 := by
    intro t ω
    simp only [hπ, piOfM, ← hmp, ← hups]
    field_simp
    ring
  have f2 : ∀ t ω, P.lw * πw t ω + mw t ω - lagW mw₀ mw t ω - ups t ω = 0 := by
    intro t ω
    simp only [hπw, piwOfM, ← hmw, ← hups]
    field_simp
    ring
  have f4 : ∀ t, ∀ᵐ ω ∂S.μ, ups t ω = P.xip * mp t ω - P.xiw * mw t ω +
      P.beta * S.E t (ups (t + 1)) ω := by
    intro t
    filter_upwards [upss t] with ω h
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    change ups t ω = P.beta * S.E t (ups (t + 1)) ω + g t ω at h
    rw [hgmp t ω]
    linarith
  have hfoc : FOCswM S P mp₀ mw₀ π πw x mp mw ups := by
    refine ⟨fun t => Eventually.of_forall fun ω => f1 t ω,
      fun t => Eventually.of_forall fun ω => f2 t ω, fun t => Eventually.of_forall fun ω => ?_,
      f4, mpa, mwa, upsa, ⟨Mp, hMp⟩, ⟨Mw, hMw⟩, upsb⟩
    change P.lx * (x t ω - P.xstar) - P.kp * mp t ω - P.kw * mw t ω = 0
    simp only [hmp, mpOfM, hmw, mwOfM, Dst, ← hx, ← hg]
    linear_combination (-(P.lx * (x t ω - P.xstar))) * hDi
  -- conditional expectations of next-period inflation
  have hmpE : ∀ t, S.E t (mp t) = mp t := fun t => S.E_of_stronglyMeasurable (mpa t) (Imp t)
  have hmwE : ∀ t, S.E t (mw t) = mw t := fun t => S.E_of_stronglyMeasurable (mwa t) (Imw t)
  have hwE : ∀ t, S.E t (w t) = w t := fun t => S.E_of_stronglyMeasurable (hwa t) (Iw t)
  have hEπ : ∀ t, ∀ᵐ ω ∂S.μ, P.lp * S.E t (π (t + 1)) ω =
      -(S.E t (mp (t + 1)) ω - mp t ω + S.E t (ups (t + 1)) ω) := by
    intro t
    have hf : π (t + 1) = fun ω => (-1 / P.lp) * mp (t + 1) ω + (1 / P.lp) * mp t ω +
        (-1 / P.lp) * ups (t + 1) ω + 0 * mp t ω + 0 * mp t ω + 0 * mp t ω + 0 := by
      funext ω
      simp only [hπ, piOfM, lagW_succ, ← hmp, ← hups]
      field_simp
      ring
    filter_upwards [E_comb6 (S := S) t (-1 / P.lp) (1 / P.lp) (-1 / P.lp) 0 0 0 0
      (Imp (t + 1)) (Imp t) (Iups (t + 1)) (Imp t) (Imp t) (Imp t)] with ω h
    rw [hf, h, hmpE t]
    field_simp
    ring
  have hEπw : ∀ t, ∀ᵐ ω ∂S.μ, P.lw * S.E t (πw (t + 1)) ω =
      -(S.E t (mw (t + 1)) ω - mw t ω - S.E t (ups (t + 1)) ω) := by
    intro t
    have hf : πw (t + 1) = fun ω => (-1 / P.lw) * mw (t + 1) ω + (1 / P.lw) * mw t ω +
        (1 / P.lw) * ups (t + 1) ω + 0 * mw t ω + 0 * mw t ω + 0 * mw t ω + 0 := by
      funext ω
      simp only [hπw, piwOfM, lagW_succ, ← hmw, ← hups]
      field_simp
      ring
    filter_upwards [E_comb6 (S := S) t (-1 / P.lw) (1 / P.lw) (1 / P.lw) 0 0 0 0
      (Imw (t + 1)) (Imw t) (Iups (t + 1)) (Imw t) (Imw t) (Imw t)] with ω h
    rw [hf, h, hmwE t]
    field_simp
    ring
  have hpe : ∀ t, π t =ᵐ[S.μ] fun ω => P.kp * (x t ω + u t ω) + P.xip * (w t ω - wn t ω) +
      P.beta * S.E t (π (t + 1)) ω := by
    intro t
    filter_upwards [E1 t, hEπ t, f4 t] with ω h1 h2 h4
    have h3 := f1 t ω
    have h5 := hgmp t ω
    have : P.lp * (π t ω - (P.kp * (x t ω + u t ω) + P.xip * (w t ω - wn t ω) +
        P.beta * S.E t (π (t + 1)) ω)) = 0 := by
      simp only [Zm] at h1
      linear_combination h3 - h1 - P.beta * h2 - h4 - h5
    have := (mul_eq_zero.1 this).resolve_left hlp
    linarith
  have hwe : ∀ t, πw t =ᵐ[S.μ] fun ω => P.kw * (x t ω + u t ω) + P.xiw * (wn t ω - w t ω) +
      P.beta * S.E t (πw (t + 1)) ω := by
    intro t
    filter_upwards [E2 t, hEπw t, f4 t] with ω h1 h2 h4
    have h3 := f2 t ω
    have h5 := hgmp t ω
    have : P.lw * (πw t ω - (P.kw * (x t ω + u t ω) + P.xiw * (wn t ω - w t ω) +
        P.beta * S.E t (πw (t + 1)) ω)) = 0 := by
      simp only [Zm] at h1
      linear_combination h3 - h1 - P.beta * h2 + h4 + h5
    have := (mul_eq_zero.1 this).resolve_left hlw
    linarith
  -- the real-wage identity, by forward uniqueness
  have lwa : StronglyAdapted S.𝓕 (lagW w₀ w) := fun t => by
    cases t with
    | zero => exact (cK cw).mono (S.𝓕.mono (Nat.zero_le 0))
    | succ t => exact (hwa t).mono (S.𝓕.mono (Nat.le_succ t))
  obtain ⟨Mw', hMw'⟩ := hwb
  have lwb : S.BddProc (lagW w₀ w) := ⟨max |cw| Mw', fun t => by
    cases t with
    | zero => exact Eventually.of_forall fun ω => le_max_left _ _
    | succ t => exact (hMw' t).mono fun ω h => h.trans (le_max_right _ _)⟩
  set d : ℕ → Ω → ℝ := fun t ω => w t ω - lagW w₀ w t ω - πw t ω + π t ω with hd
  obtain ⟨da, db⟩ := comb6M (S := S) 1 (-1) (-1) 1 0 0 0 hwa lwa πwa πa πa πa ⟨Mw', hMw'⟩ lwb
    πwb πb πb πb (z := d) (fun t ω => by simp only [hd]; ring)
  have hdE : S.Solves P.beta (fun _ _ => 0) d := by
    intro t
    have hf : d (t + 1) = fun ω => 1 * w (t + 1) ω + (-1) * w t ω + (-1) * πw (t + 1) ω +
        1 * π (t + 1) ω + 0 * w t ω + 0 * w t ω + 0 := by
      funext ω; simp only [hd, lagW_succ]; ring
    filter_upwards [E_comb6 (S := S) t 1 (-1) (-1) 1 0 0 0 (Iw (t + 1)) (Iw t) (Iπw (t + 1))
      (Iπ (t + 1)) (Iw t) (Iw t), hpe t, hwe t] with ω hE h1 h2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hf, hE, hwE t]
    have h3 := hS t ω
    have hW : W1 t ω = (1 + P.beta) * w t ω - P.beta * S.E t (w (t + 1)) ω -
        lagW w₀ w t ω := rfl
    simp only [hd]
    rw [hcdef, hξ] at *
    linear_combination h1 - h2 - hW - h3
  have hzero : S.Solves P.beta (fun _ _ => 0) (fun _ _ => 0) := by
    intro t
    refine Eventually.of_forall fun ω => ?_
    simp [S.E_const t 0]
  have hz := S.forward_unique hβa hdE hzero
    (fun t => ((da t).mono (S.𝓕.le t)).aestronglyMeasurable)
    (fun t => aestronglyMeasurable_const) ⟨_, db.choose_spec⟩
    ⟨0, fun t => Eventually.of_forall fun ω => by simp⟩
  have hwi : ∀ t, w t =ᵐ[S.μ] fun ω => lagW w₀ w t ω + πw t ω - π t ω := by
    intro t
    filter_upwards [hz t] with ω h
    simp only [hd] at h
    linarith
  exact ⟨⟨hpe, hwe, hwi, πa, πwa, xa, hwa, πb, πwb, xb, ⟨Mw', hMw'⟩⟩, hfoc⟩

variable (S) in
/-- **Woodford (2003), (2.11)–(2.20), `κ_w ≠ κ_p`, on a probability space (the "if" half)**:
under the root condition `InflTargetStickyWages.StableRoots`, for every bounded adapted
disturbance `(u, w^n)` and constant initial multipliers `(a, b)` (with `w_{t₀−1} = 0`), there is
a bounded adapted plan with bounded adapted multipliers satisfying (2.11)–(2.13) and
(2.16)–(2.19) almost surely, with Mathlib's conditional expectation. -/
theorem exists_meas_of_stableRoots {P : SW} (hβ0 : 0 < P.beta) (hβ1 : P.beta < 1)
    (hlx : 0 < P.lx) (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hkp : 0 < P.kp) (hkw : 0 < P.kw)
    (hxip : 0 < P.xip) (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp) (hR : StableRoots P)
    (u wn : ℕ → Ω → ℝ) (hu : S.BddProc u) (hua : StronglyAdapted S.𝓕 u) (hwn : S.BddProc wn)
    (hwna : StronglyAdapted S.𝓕 wn) (a b : ℝ) :
    ∃ π πw x w mp mw ups, PlanSWM S P (fun _ => 0) u wn π πw x w ∧
      FOCswM S P (fun _ => a) (fun _ => b) π πw x mp mw ups := by
  have hc : P.kw - P.kp ≠ 0 := sub_ne_zero.2 hne
  have hD : Dst P ≠ 0 := by unfold Dst; positivity
  obtain ⟨Z1, Z2, Z3, hv1, hv2, hv3⟩ := cubic_vieta_exists (p2 := cp2 P) (p1 := cp1 P)
    (p0 := cp0 P) hlx.ne'
  have hfac := charP_factor hlx.ne' hv1 hv2 hv3
  obtain ⟨μ1, r1, n1⟩ := hR Z1 (by rw [hfac]; ring)
  obtain ⟨μ2, r2, n2⟩ := hR Z2 (by rw [hfac]; ring)
  obtain ⟨μ3, r3, n3⟩ := hR Z3 (by rw [hfac]; ring)
  have cK : StronglyMeasurable[S.𝓕 0] (fun _ : Ω => (0 : ℝ)) := stronglyMeasurable_const
  have cB : ∀ᵐ ω ∂S.μ, |(fun _ : Ω => (0 : ℝ)) ω| ≤ 0 :=
    Eventually.of_forall fun ω => by simp
  have aZn := Zm_adapted (S := S) P.beta cK hwna
  have bZn := Zm_bdd (S := S) P.beta hβ0.le cB hwn
  have aZu := Zm_adapted (S := S) P.beta cK hua
  have bZu := Zm_bdd (S := S) P.beta hβ0.le cB hu
  have aZZn := Zm_adapted (S := S) P.beta cK aZn
  have bZZn := Zm_bdd (S := S) P.beta hβ0.le cB bZn
  have aZZu := Zm_adapted (S := S) P.beta cK aZu
  have bZZu := Zm_bdd (S := S) P.beta hβ0.le cB bZu
  obtain ⟨Fa, Fb⟩ := comb6M (S := S) (ca0 P + P.lx * (P.xip + P.xiw) ^ 2)
    (P.lx * (P.xip + P.xiw)) ((P.kw - P.kp) * P.lx)
    ((P.xip + P.xiw) * ca0 P - (P.kw - P.kp) * cb0 P) ((P.xip + P.xiw) * (P.kw - P.kp) * P.lx)
    0 0 aZn aZZn aZZu hwna aZu aZu bZn bZZn bZZu hwn bZu bZu (z := forcingFm S P u wn)
    (fun t ω => by simp only [forcingFm]; ring)
  set c1 : ℝ := (P.kw - P.kp) / P.lx * (P.kp * a + P.kw * b + P.lx * P.xstar) -
    (P.xip + P.xiw) * 0 with hc1
  set c2 : ℝ := ((P.kw - P.kp) ^ 2 * (P.xip * a - P.xiw * b) - ca1 P * c1 - ca0 P * 0) / P.lx
    with hc2
  have e1 : initS1 P (fun _ => 0) (fun _ => a) (fun _ => b) = fun (_ : Ω) => c1 := by
    funext ω; rfl
  have e2 : initS2 P (fun _ => 0) (fun _ => a) (fun _ => b) = fun (_ : Ω) => c2 := by
    funext ω; rfl
  obtain ⟨w, hwa, hwb, hcub⟩ := cubicR_exists (S := S) hβ0.le hβ1 hlx.ne' hv1 hv2 hv3 r1 n1 r2
    n2 r3 n3 Fa Fb 0 c1 c2
  rw [← e1, ← e2] at hcub
  exact ⟨_, _, _, w, _, _, _, cubic_imp_focM hβ0.le hβ1 hlx.ne' hlp.ne' hlw.ne' hc hD 0 a b
    hua hu hwna hwn hcub hwa hwb⟩

variable (S) in
/-- **Woodford (2003), (2.20), `κ_w ≠ κ_p` (the exact region on a probability space)**: on every
filtered probability space with Mathlib's conditional expectation, bounded adapted plans with
bounded adapted multipliers satisfying (2.11)–(2.13) and (2.16)–(2.19) almost surely exist for
every bounded adapted disturbance and every pair of constant initial multipliers **iff** the root
condition `InflTargetStickyWages.StableRoots` holds (every root of `P` outside the ellipse,
`InflTargetStickyWages.stable_iff_ellForm`). -/
theorem exists_meas_iff_stableRoots {P : SW} (hβ0 : 0 < P.beta) (hβ1 : P.beta < 1)
    (hlx : 0 < P.lx) (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hkp : 0 < P.kp) (hkw : 0 < P.kw)
    (hxip : 0 < P.xip) (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp) :
    (∀ u wn : ℕ → Ω → ℝ, S.BddProc u → StronglyAdapted S.𝓕 u → S.BddProc wn →
      StronglyAdapted S.𝓕 wn → ∀ a b : ℝ, ∃ π πw x w mp mw ups,
        PlanSWM S P (fun _ => 0) u wn π πw x w ∧
        FOCswM S P (fun _ => a) (fun _ => b) π πw x mp mw ups) ↔ StableRoots P :=
  ⟨stableRoots_of_exists_meas S hβ0 hβ1 hlx hlp hlw hkp hkw hxip hxiw hne,
    fun hR u wn hu hua hwn hwna a b => exists_meas_of_stableRoots S hβ0 hβ1 hlx hlp hlw hkp hkw
      hxip hxiw hne hR u wn hu hua hwn hwna a b⟩

end Woodford.OptimalPolicyRules.TidyR5bStickyExists
