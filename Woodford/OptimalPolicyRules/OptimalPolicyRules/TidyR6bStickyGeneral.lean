/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR5bStickyExists
import OptimalPolicyRules.TidyR6bRuleSystemMeasure

/-!
# The (2.20) region for `κ_w ≠ κ_p` on a probability space: general initial values, uniqueness

Woodford (2003), *Interest and Prices*, Chapter 8, §2.2, (2.11)–(2.20), pp. 565–567, on every
filtered probability space with Mathlib's conditional expectation (`TidyR5bStickyMeasure.PlanSWM`,
`TidyR5bStickyMeasure.FOCswM`).

`TidyR5bStickyExists.exists_meas_iff_stableRoots` proves existence under the root condition for
the initial values `w_{t₀−1} = 0` and constant initial multipliers. This module completes the
result:

* `cubicR_existsG`, `cubic_imp_focMG`, `exists_meas_of_stableRootsG`: **existence for every
  essentially bounded `𝓕₀`-measurable initial values** `(w_{t₀−1}, φ_{p,t₀−1}, φ_{w,t₀−1})`.
* `uniqueM`: **a.s. uniqueness** by forecast transfer — at almost every outcome the date-`n`
  conditional forecasts of the difference of two solutions form a bounded perfect-foresight
  solution with zero data, hence vanish (`pf_zero`, from `InflTargetStickyWages.foc_existsUnique`
  at a one-point sample space), so the difference vanishes a.s. at date `n`.
* `existsUniqueM_of_stableRoots`, `existsUniqueM_iff_stableRoots`: under `StableRoots`, for every
  bounded adapted disturbance and every essentially bounded initial values known at date 0 there
  is exactly one (a.s.) bounded adapted plan with bounded adapted multipliers satisfying
  (2.11)–(2.13) and (2.16)–(2.19) a.s.; and this holds for all data iff `StableRoots`.
-/

namespace Woodford.OptimalPolicyRules.TidyR6bStickyGeneral

open MeasureTheory Filter Topology ExpectationsMeasure InflTargetStickyWages InflTargetInertia
open TidyR5bCondExpC TidyR5bStickyMeasure TidyR5bStickyExists

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-! ### Existence for general initial values -/

/-- **Woodford (2003), (2.20) (the real cubic equation on a probability space), general initial
values**: with Vieta's relations for `p₃Z³ + p₂Z² + p₁Z + p₀` and a stable `μᵢ` for each root, a
bounded adapted forcing and essentially bounded initial values known at date 0 give a bounded
adapted solution (the real part of the complex solution of `TidyR5bCondExpC.cubic_exists`). -/
theorem cubicR_existsG {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {p3 p2 p1 p0 : ℝ} (hp3 : p3 ≠ 0)
    {Z1 Z2 Z3 μ1 μ2 μ3 : ℂ} (hv1 : Z1 + Z2 + Z3 = ((-(p2 / p3) : ℝ) : ℂ))
    (hv2 : Z1 * Z2 + Z1 * Z3 + Z2 * Z3 = ((p1 / p3 : ℝ) : ℂ))
    (hv3 : Z1 * Z2 * Z3 = ((-(p0 / p3) : ℝ) : ℂ))
    (r1 : (β : ℂ) * μ1 ^ 2 - (1 + β - Z1) * μ1 + 1 = 0) (n1 : ‖μ1‖ < 1)
    (r2 : (β : ℂ) * μ2 ^ 2 - (1 + β - Z2) * μ2 + 1 = 0) (n2 : ‖μ2‖ < 1)
    (r3 : (β : ℂ) * μ3 ^ 2 - (1 + β - Z3) * μ3 + 1 = 0) (n3 : ‖μ3‖ < 1)
    {F : ℕ → Ω → ℝ} (hFa : StronglyAdapted S.𝓕 F) (hFb : S.BddProc F) {w0 s1 s2 : Ω → ℝ}
    (k0 : StronglyMeasurable[S.𝓕 0] w0) (k1 : StronglyMeasurable[S.𝓕 0] s1)
    (k2 : StronglyMeasurable[S.𝓕 0] s2) {B : ℝ} (b0 : ∀ᵐ ω ∂S.μ, |w0 ω| ≤ B)
    (b1 : ∀ᵐ ω ∂S.μ, |s1 ω| ≤ B) (b2 : ∀ᵐ ω ∂S.μ, |s2 ω| ≤ B) :
    ∃ w, StronglyAdapted S.𝓕 w ∧ S.BddProc w ∧ RCub (S := S) β p3 p2 p1 p0 w0 s1 s2 F w := by
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
  have kc : ∀ {s : Ω → ℝ}, StronglyMeasurable[S.𝓕 0] s → KnownC S 0 (fun ω => (s ω : ℂ)) :=
    fun hs => ⟨by simpa only [Complex.ofReal_re] using hs, by
      simp only [Complex.ofReal_im]
      exact stronglyMeasurable_const⟩
  have bc : ∀ {s : Ω → ℝ}, (∀ᵐ ω ∂S.μ, |s ω| ≤ B) →
      ∀ᵐ ω ∂S.μ, ‖(fun ω => (s ω : ℂ)) ω‖ ≤ B := fun hs =>
    hs.mono fun ω h => by rw [Complex.norm_real, Real.norm_eq_abs]; exact h
  obtain ⟨wc, ha, ⟨K, hb⟩, hcub⟩ := cubic_exists hβ0 hβ1 r1 n1 r2 n2 r3 n3 hHa hHb
    (kc k0) (kc k1) (kc k2) (bc b0) (bc b1) (bc b2)
  rw [hv1, hv2, hv3] at hcub
  refine ⟨fun t ω => (wc t ω).re, fun t => (ha t).1, ⟨K, fun t => (hb t).mono fun ω h =>
    (Complex.abs_re_le_norm _).trans h⟩, fun t => ?_⟩
  filter_upwards [hcub t] with ω h
  have hre := congrArg Complex.re h
  have e1 := congrFun (congrFun (re_ZC (S := S) β (fun ω => (w0 ω : ℂ)) wc) t) ω
  have e2 := congrFun (congrFun (re_ZC (S := S) β (fun ω => (s1 ω : ℂ))
    (ZC S β (fun ω => (w0 ω : ℂ)) wc)) t) ω
  have e3 := congrFun (congrFun (re_ZC (S := S) β (fun ω => (s2 ω : ℂ))
    (ZC S β (fun ω => (s1 ω : ℂ)) (ZC S β (fun ω => (w0 ω : ℂ)) wc))) t) ω
  have f1 := re_ZC (S := S) β (fun ω => (w0 ω : ℂ)) wc
  have f2 := re_ZC (S := S) β (fun ω => (s1 ω : ℂ)) (ZC S β (fun ω => (w0 ω : ℂ)) wc)
  simp only [Complex.ofReal_re] at e1 e2 e3 f1 f2
  rw [f1] at e2 f2
  rw [f2] at e3
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, hH] at hre
  rw [e1, e2, e3] at hre
  field_simp at hre
  linear_combination hre

/-- **Woodford (2003), (2.11)–(2.19) ⇐ the cubic equation, on a probability space, general initial
values**: if the real wage `w` is a bounded adapted a.s. solution of the cubic equation with the
initial values implied by essentially bounded `(w_{t₀−1}, φ_{p,t₀−1}, φ_{w,t₀−1})` known at date 0,
then `(piOfM, piwOfM, xOfM, w)` is a bounded adapted plan satisfying (2.11)–(2.13) a.s., and with
the bounded adapted multipliers `(mpOfM, mwOfM, upsOfM)` the first-order conditions hold a.s.
(the construction of `TidyR5bStickyExists.cubic_imp_focM`). -/
theorem cubic_imp_focMG {P : SW} (hβ0 : 0 ≤ P.beta) (hβ1 : P.beta < 1) (hlx : P.lx ≠ 0)
    (hlp : P.lp ≠ 0) (hlw : P.lw ≠ 0) (hc : P.kw - P.kp ≠ 0) (hD : Dst P ≠ 0)
    {w₀ mp₀ mw₀ : Ω → ℝ} (kw0 : StronglyMeasurable[S.𝓕 0] w₀)
    (kmp0 : StronglyMeasurable[S.𝓕 0] mp₀) (kmw0 : StronglyMeasurable[S.𝓕 0] mw₀) {B : ℝ}
    (bw0 : ∀ᵐ ω ∂S.μ, |w₀ ω| ≤ B) (bmp0 : ∀ᵐ ω ∂S.μ, |mp₀ ω| ≤ B)
    (bmw0 : ∀ᵐ ω ∂S.μ, |mw₀ ω| ≤ B)
    {u wn w : ℕ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u) (hub : S.BddProc u)
    (hwna : StronglyAdapted S.𝓕 wn) (hwnb : S.BddProc wn)
    (hcub : RCub (S := S) P.beta P.lx (cp2 P) (cp1 P) (cp0 P) w₀
      (initS1 P w₀ mp₀ mw₀)
      (initS2 P w₀ mp₀ mw₀) (forcingFm S P u wn) w)
    (hwa : StronglyAdapted S.𝓕 w) (hwb : S.BddProc w) :
    PlanSWM S P w₀ u wn
        (piOfM S P w₀ mp₀ mw₀ u wn w)
        (piwOfM S P w₀ mp₀ mw₀ u wn w)
        (xOfM S P w₀ u wn w) w ∧
      FOCswM S P mp₀ mw₀
        (piOfM S P w₀ mp₀ mw₀ u wn w)
        (piwOfM S P w₀ mp₀ mw₀ u wn w)
        (xOfM S P w₀ u wn w)
        (mpOfM S P w₀ mp₀ mw₀ u wn w)
        (mwOfM S P w₀ mp₀ mw₀ u wn w)
        (upsOfM S P w₀ mp₀ mw₀ u wn w) := by
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
  have es1 : s1 = fun ω => (P.kw - P.kp) / P.lx * P.kp * mp₀ ω +
      (P.kw - P.kp) / P.lx * P.kw * mw₀ ω + (-(P.xip + P.xiw)) * w₀ ω +
      (P.kw - P.kp) / P.lx * (P.lx * P.xstar) := by
    funext ω
    simp only [hs1, initS1]
    ring
  have s1K : StronglyMeasurable[S.𝓕 0] s1 := by
    rw [es1]
    exact (((kmp0.const_mul _).add (kmw0.const_mul _)).add (kw0.const_mul _)).add
      stronglyMeasurable_const
  have s1B : ∀ᵐ ω ∂S.μ, |s1 ω| ≤ |(P.kw - P.kp) / P.lx * P.kp| * B +
      |(P.kw - P.kp) / P.lx * P.kw| * B + |(-(P.xip + P.xiw))| * B +
      |(P.kw - P.kp) / P.lx * (P.lx * P.xstar)| := by
    filter_upwards [bw0, bmp0, bmw0] with ω h0 h1 h2
    rw [es1]
    exact TidyR6bRuleSystemMeasure.abs_lin3_le h1 h2 h0
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
  have aW1 : StronglyAdapted S.𝓕 W1 := Zm_adapted P.beta kw0 hwa
  have bW1 : S.BddProc W1 := Zm_bdd P.beta hβ0 bw0 hwb
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
    | zero => exact kmp0.mono (S.𝓕.mono (Nat.zero_le 0))
    | succ t => exact (mpa t).mono (S.𝓕.mono (Nat.le_succ t))
  have lmwa : StronglyAdapted S.𝓕 (lagW mw₀ mw) := fun t => by
    cases t with
    | zero => exact kmw0.mono (S.𝓕.mono (Nat.zero_le 0))
    | succ t => exact (mwa t).mono (S.𝓕.mono (Nat.le_succ t))
  obtain ⟨Mp, hMp⟩ := mpb
  obtain ⟨Mw, hMw⟩ := mwb
  have lmpb : S.BddProc (lagW mp₀ mp) := ⟨max B Mp, fun t => by
    cases t with
    | zero => exact bmp0.mono fun ω h => h.trans (le_max_left _ _)
    | succ t => exact (hMp t).mono fun ω h => h.trans (le_max_right _ _)⟩
  have lmwb : S.BddProc (lagW mw₀ mw) := ⟨max B Mw, fun t => by
    cases t with
    | zero => exact bmw0.mono fun ω h => h.trans (le_max_left _ _)
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
    | zero => exact kw0.mono (S.𝓕.mono (Nat.zero_le 0))
    | succ t => exact (hwa t).mono (S.𝓕.mono (Nat.le_succ t))
  obtain ⟨Mw', hMw'⟩ := hwb
  have lwb : S.BddProc (lagW w₀ w) := ⟨max B Mw', fun t => by
    cases t with
    | zero => exact bw0.mono fun ω h => h.trans (le_max_left _ _)
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


/-- Woodford (2003), (2.20) (tool): an affine function of three essentially bounded variables
known at date 0 is known at date 0 and essentially bounded. -/
theorem affine3 {w₀ mp₀ mw₀ : Ω → ℝ} (kw0 : StronglyMeasurable[S.𝓕 0] w₀)
    (kmp0 : StronglyMeasurable[S.𝓕 0] mp₀) (kmw0 : StronglyMeasurable[S.𝓕 0] mw₀) {B : ℝ}
    (bw0 : ∀ᵐ ω ∂S.μ, |w₀ ω| ≤ B) (bmp0 : ∀ᵐ ω ∂S.μ, |mp₀ ω| ≤ B)
    (bmw0 : ∀ᵐ ω ∂S.μ, |mw₀ ω| ≤ B) (a b d e : ℝ) :
    StronglyMeasurable[S.𝓕 0] (fun ω => a * mp₀ ω + b * mw₀ ω + d * w₀ ω + e) ∧
      ∀ᵐ ω ∂S.μ, |a * mp₀ ω + b * mw₀ ω + d * w₀ ω + e| ≤ |a| * B + |b| * B + |d| * B + |e| :=
  ⟨(((kmp0.const_mul a).add (kmw0.const_mul b)).add (kw0.const_mul d)).add
      stronglyMeasurable_const,
    by
      filter_upwards [bw0, bmp0, bmw0] with ω h0 h1 h2
      exact TidyR6bRuleSystemMeasure.abs_lin3_le h1 h2 h0⟩

omit [MeasurableSpace Ω] in
/-- Woodford (2003), (2.20): the initial value `(𝒵w)_{t₀−1}` (`InflTargetStickyWages.initS1`) is
affine in `(φ_{p,t₀−1}, φ_{w,t₀−1}, w_{t₀−1})`. -/
theorem initS1_eq (P : SW) (w₀ mp₀ mw₀ : Ω → ℝ) :
    initS1 P w₀ mp₀ mw₀ = fun ω => (P.kw - P.kp) / P.lx * P.kp * mp₀ ω +
      (P.kw - P.kp) / P.lx * P.kw * mw₀ ω + (-(P.xip + P.xiw)) * w₀ ω +
      (P.kw - P.kp) / P.lx * (P.lx * P.xstar) := by
  funext ω
  simp only [initS1]
  ring

omit [MeasurableSpace Ω] in
/-- Woodford (2003), (2.20): the initial value `(𝒵²w)_{t₀−1}` (`InflTargetStickyWages.initS2`) is
affine in `(φ_{p,t₀−1}, φ_{w,t₀−1}, w_{t₀−1})`. -/
theorem initS2_eq (P : SW) (w₀ mp₀ mw₀ : Ω → ℝ) :
    initS2 P w₀ mp₀ mw₀ = fun ω =>
      ((P.kw - P.kp) ^ 2 * P.xip - ca1 P * ((P.kw - P.kp) / P.lx * P.kp)) / P.lx * mp₀ ω +
      (-((P.kw - P.kp) ^ 2 * P.xiw) - ca1 P * ((P.kw - P.kp) / P.lx * P.kw)) / P.lx * mw₀ ω +
      (-(ca1 P * (-(P.xip + P.xiw))) - ca0 P) / P.lx * w₀ ω +
      (-(ca1 P * ((P.kw - P.kp) / P.lx * (P.lx * P.xstar)))) / P.lx := by
  funext ω
  simp only [initS2, initS1]
  ring

variable (S) in
/-- **Woodford (2003), (2.11)–(2.20), `κ_w ≠ κ_p`, on a probability space (the "if" half), for
general initial values**: under the root condition `InflTargetStickyWages.StableRoots`, for every
bounded adapted disturbance `(u, w^n)` and every essentially bounded initial values
`(w_{t₀−1}, φ_{p,t₀−1}, φ_{w,t₀−1})` known at date 0, there is a bounded adapted plan with bounded
adapted multipliers satisfying (2.11)–(2.13) and (2.16)–(2.19) almost surely. -/
theorem exists_meas_of_stableRootsG {P : SW} (hβ0 : 0 < P.beta) (hβ1 : P.beta < 1)
    (hlx : 0 < P.lx) (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hkp : 0 < P.kp) (hkw : 0 < P.kw)
    (hxip : 0 < P.xip) (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp) (hR : StableRoots P)
    (u wn : ℕ → Ω → ℝ) (hu : S.BddProc u) (hua : StronglyAdapted S.𝓕 u) (hwn : S.BddProc wn)
    (hwna : StronglyAdapted S.𝓕 wn) {w₀ mp₀ mw₀ : Ω → ℝ} (kw0 : StronglyMeasurable[S.𝓕 0] w₀)
    (kmp0 : StronglyMeasurable[S.𝓕 0] mp₀) (kmw0 : StronglyMeasurable[S.𝓕 0] mw₀) {B : ℝ}
    (bw0 : ∀ᵐ ω ∂S.μ, |w₀ ω| ≤ B) (bmp0 : ∀ᵐ ω ∂S.μ, |mp₀ ω| ≤ B)
    (bmw0 : ∀ᵐ ω ∂S.μ, |mw₀ ω| ≤ B) :
    ∃ π πw x w mp mw ups, PlanSWM S P w₀ u wn π πw x w ∧
      FOCswM S P mp₀ mw₀ π πw x mp mw ups := by
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
  obtain ⟨k1, b1⟩ := affine3 kw0 kmp0 kmw0 bw0 bmp0 bmw0 ((P.kw - P.kp) / P.lx * P.kp)
    ((P.kw - P.kp) / P.lx * P.kw) (-(P.xip + P.xiw)) ((P.kw - P.kp) / P.lx * (P.lx * P.xstar))
  obtain ⟨k2, b2⟩ := affine3 kw0 kmp0 kmw0 bw0 bmp0 bmw0
    (((P.kw - P.kp) ^ 2 * P.xip - ca1 P * ((P.kw - P.kp) / P.lx * P.kp)) / P.lx)
    ((-((P.kw - P.kp) ^ 2 * P.xiw) - ca1 P * ((P.kw - P.kp) / P.lx * P.kw)) / P.lx)
    ((-(ca1 P * (-(P.xip + P.xiw))) - ca0 P) / P.lx)
    ((-(ca1 P * ((P.kw - P.kp) / P.lx * (P.lx * P.xstar)))) / P.lx)
  set B1 := |(P.kw - P.kp) / P.lx * P.kp| * B + |(P.kw - P.kp) / P.lx * P.kw| * B +
    |-(P.xip + P.xiw)| * B + |(P.kw - P.kp) / P.lx * (P.lx * P.xstar)| with hB1
  set B2 := |((P.kw - P.kp) ^ 2 * P.xip - ca1 P * ((P.kw - P.kp) / P.lx * P.kp)) / P.lx| * B +
    |(-((P.kw - P.kp) ^ 2 * P.xiw) - ca1 P * ((P.kw - P.kp) / P.lx * P.kw)) / P.lx| * B +
    |(-(ca1 P * (-(P.xip + P.xiw))) - ca0 P) / P.lx| * B +
    |(-(ca1 P * ((P.kw - P.kp) / P.lx * (P.lx * P.xstar)))) / P.lx| with hB2
  obtain ⟨w, hwa, hwb, hcub⟩ := cubicR_existsG (S := S) hβ0.le hβ1 hlx.ne' hv1 hv2 hv3 r1 n1
    r2 n2 r3 n3 Fa Fb kw0 (s1 := initS1 P w₀ mp₀ mw₀) (s2 := initS2 P w₀ mp₀ mw₀)
    (by rw [initS1_eq]; exact k1) (by rw [initS2_eq]; exact k2) (B := max (max B B1) B2)
    (bw0.mono fun ω h => h.trans ((le_max_left _ _).trans (le_max_left _ _)))
    (by
      rw [initS1_eq]
      exact b1.mono fun ω h => h.trans ((le_max_right _ _).trans (le_max_left _ _)))
    (by
      rw [initS2_eq]
      exact b2.mono fun ω h => h.trans (le_max_right _ _))
  exact ⟨_, _, _, w, _, _, _, cubic_imp_focMG hβ0.le hβ1 hlx.ne' hlp.ne' hlw.ne' hc hD kw0 kmp0
    kmw0 bw0 bmp0 bmw0 hua hu hwna hwn hcub hwa hwb⟩

/-! ### Uniqueness by forecast transfer -/

/-- Woodford (2003), p. 540 (law of iterated expectations, tool): the date-`n` forecast of an a.s.
linear relation `y⁰_m = a₁y¹_m + a₂y²_m + a₃y³_m + bE_m z_{m+1}` at a date `m ≥ n` is the same
relation between the date-`n` forecasts. -/
theorem fc_lin {n m : ℕ} (hnm : n ≤ m) {y0 y1 y2 y3 z : ℕ → Ω → ℝ} (a1 a2 a3 b : ℝ)
    (h : y0 m =ᵐ[S.μ] fun ω => a1 * y1 m ω + a2 * y2 m ω + a3 * y3 m ω +
      b * S.E m (z (m + 1)) ω)
    (i1 : Integrable (y1 m) S.μ) (i2 : Integrable (y2 m) S.μ) (i3 : Integrable (y3 m) S.μ) :
    ∀ᵐ ω ∂S.μ, S.E n (y0 m) ω = a1 * S.E n (y1 m) ω + a2 * S.E n (y2 m) ω +
      a3 * S.E n (y3 m) ω + b * S.E n (z (m + 1)) ω := by
  filter_upwards [S.E_congr h n, TidyR5aLambdaXZeroMeasure.E_lin4 S n a1 a2 a3 b i1 i2 i3
    (S.integrable_E m (z (m + 1))), S.E_tower hnm (z (m + 1))] with ω e1 e2 e3
  rw [e1, e2, e3]

/-- Woodford (2003), (2.15)–(2.19) (tool): the parameters with `x* = 0` (the homogeneous problem
satisfied by the difference of two plans). -/
def P0 (P : SW) : SW := { P with xstar := 0 }

/-- **Woodford (2003), (2.20), uniqueness under perfect foresight with zero data**: under the root
condition, a bounded perfect-foresight solution of (2.11)–(2.13) and (2.16)–(2.19) with zero
disturbances, zero initial values and `x* = 0` is zero
(`InflTargetStickyWages.foc_existsUnique` at a one-point sample space). -/
theorem pf_zero {P : SW} (hβ0 : 0 < P.beta) (hβ1 : P.beta < 1) (hlx : 0 < P.lx)
    (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hkp : 0 < P.kp) (hkw : 0 < P.kw) (hxip : 0 < P.xip)
    (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp) (hR : StableRoots P)
    {π πw x w mp mw ups : ℕ → Unit → ℝ}
    (hp : PlanSW perfectForesight (P0 P) (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) π πw x w)
    (hf : FOCsw perfectForesight (P0 P) (fun _ => 0) (fun _ => 0) π πw x mp mw ups)
    (hupsb : BoundedProc ups) :
    ∀ t, π t () = 0 ∧ πw t () = 0 ∧ x t () = 0 ∧ w t () = 0 ∧ mp t () = 0 ∧ mw t () = 0 ∧
      ups t () = 0 := by
  have hz : BoundedProc (fun (_ : ℕ) (_ : Unit) => (0 : ℝ)) := ⟨0, fun _ _ => by simp⟩
  have hza : perfectForesight.Adapted (fun (_ : ℕ) (_ : Unit) => (0 : ℝ)) := fun _ => rfl
  obtain ⟨π0, πw0, x0, w0, mp0, mw0, ups0, -, huniq⟩ := foc_existsUnique (P := P0 P)
    perfectForesight hβ0 hβ1 hlx hlp hlw hkp hkw hxip hxiw hne hR hz hza hz hza
    (w₀ := fun _ => 0) (mp₀ := fun _ => 0) (mw₀ := fun _ => 0) ⟨0, fun _ => by simp⟩
    ⟨0, fun _ => by simp⟩ ⟨0, fun _ => by simp⟩ rfl rfl rfl
  have hl0 : ∀ t ω, lagW (fun (_ : Unit) => (0 : ℝ)) (fun (_ : ℕ) (_ : Unit) => (0 : ℝ)) t ω =
      0 := by
    intro t ω
    cases t <;> rfl
  have hzp : PlanSW perfectForesight (P0 P) (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0)
      (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) :=
    ⟨fun t ω => by
      change (0 : ℝ) = (P0 P).kp * (0 + 0) + (P0 P).xip * (0 - 0) + (P0 P).beta * 0
      ring, fun t ω => by
      change (0 : ℝ) = (P0 P).kw * (0 + 0) + (P0 P).xiw * (0 - 0) + (P0 P).beta * 0
      ring, fun t ω => by rw [hl0]; simp, hza, hza, hza, hza, hz, hz, hz, hz⟩
  have hzf : FOCsw perfectForesight (P0 P) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
      (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) := by
    intro t ω
    simp only [hl0, P0]
    refine ⟨by ring, by ring, by ring, ?_⟩
    change (0 : ℝ) = P.xip * 0 - P.xiw * 0 + P.beta * 0
    ring
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := huniq _ _ _ _ _ _ _ hp hf (fun t => rfl) (fun t => rfl)
    hupsb
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := huniq _ _ _ _ _ _ _ hzp hzf hza hza hz
  intro t
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a1, ← b1]
  · rw [a2, ← b2]
  · rw [a3, ← b3]
  · rw [a4, ← b4]
  · rw [a5, ← b5]
  · rw [a6, ← b6]
  · rw [a7, ← b7]

/-- Woodford (2003), (2.11)–(2.19) (tool): the difference of two bounded adapted processes is
bounded and adapted. -/
theorem sub_spec {y y' : ℕ → Ω → ℝ} (ha : StronglyAdapted S.𝓕 y) (ha' : StronglyAdapted S.𝓕 y')
    (hb : S.BddProc y) (hb' : S.BddProc y') :
    StronglyAdapted S.𝓕 (fun t ω => y t ω - y' t ω) ∧ S.BddProc (fun t ω => y t ω - y' t ω) := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨M', hM'⟩ := hb'
  exact ⟨fun t => (ha t).sub (ha' t), M + M', fun t => by
    filter_upwards [hM t, hM' t] with ω h1 h2
    exact (abs_sub _ _).trans (add_le_add h1 h2)⟩

omit [MeasurableSpace Ω] in
/-- Woodford (2003), (2.11)–(2.19) (tool): the difference of two lags with the same initial value
is the lag of the difference with initial value 0. -/
theorem lagW_sub (z₀ : Ω → ℝ) (y y' : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    lagW z₀ y t ω - lagW z₀ y' t ω = lagW (fun _ => 0) (fun t ω => y t ω - y' t ω) t ω := by
  cases t with
  | zero => exact sub_self _
  | succ s => rfl

variable (S) in
/-- **Woodford (2003), (2.11)–(2.20), `κ_w ≠ κ_p`, on a probability space: a.s. uniqueness.**
Under the root condition, two bounded adapted plans with bounded adapted multipliers satisfying
(2.11)–(2.13) and (2.16)–(2.19) a.s. with the same disturbances and the same initial values
`(w_{t₀−1}, φ_{p,t₀−1}, φ_{w,t₀−1})` agree a.s. at every date. Forecast transfer: at almost every
outcome the date-`n` conditional forecasts of the differences form a bounded perfect-foresight
solution with zero data (`pf_zero`), and by induction the lags at `n` vanish a.s. -/
theorem uniqueM {P : SW} (hβ0 : 0 < P.beta) (hβ1 : P.beta < 1) (hlx : 0 < P.lx)
    (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hkp : 0 < P.kp) (hkw : 0 < P.kw) (hxip : 0 < P.xip)
    (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp) (hR : StableRoots P) {u wn : ℕ → Ω → ℝ}
    {w₀ mp₀ mw₀ : Ω → ℝ} {π πw x w mp mw ups π' πw' x' w' mp' mw' ups' : ℕ → Ω → ℝ}
    (h1 : PlanSWM S P w₀ u wn π πw x w) (f1 : FOCswM S P mp₀ mw₀ π πw x mp mw ups)
    (h2 : PlanSWM S P w₀ u wn π' πw' x' w') (f2 : FOCswM S P mp₀ mw₀ π' πw' x' mp' mw' ups') :
    ∀ t, π t =ᵐ[S.μ] π' t ∧ πw t =ᵐ[S.μ] πw' t ∧ x t =ᵐ[S.μ] x' t ∧ w t =ᵐ[S.μ] w' t ∧
      mp t =ᵐ[S.μ] mp' t ∧ mw t =ᵐ[S.μ] mw' t ∧ ups t =ᵐ[S.μ] ups' t := by
  obtain ⟨P1, P2, P3, πa, πwa, xa, wa, πb, πwb, xb, wb⟩ := h1
  obtain ⟨Q1, Q2, Q3, πa', πwa', xa', wa', πb', πwb', xb', wb'⟩ := h2
  obtain ⟨F1, F2, F3, F4, mpa, mwa, upsa, mpb, mwb, upsb⟩ := f1
  obtain ⟨G1, G2, G3, G4, mpa', mwa', upsa', mpb', mwb', upsb'⟩ := f2
  have hlx0 : P.lx ≠ 0 := hlx.ne'
  -- the differences
  have Iπ := integrable_of_adapted S πa πb
  have Iπ' := integrable_of_adapted S πa' πb'
  have Iπw := integrable_of_adapted S πwa πwb
  have Iπw' := integrable_of_adapted S πwa' πwb'
  have Iups := integrable_of_adapted S upsa upsb
  have Iups' := integrable_of_adapted S upsa' upsb'
  obtain ⟨dπa, dπb⟩ := sub_spec πa πa' πb πb'
  obtain ⟨dπwa, dπwb⟩ := sub_spec πwa πwa' πwb πwb'
  obtain ⟨dxa, dxb⟩ := sub_spec xa xa' xb xb'
  obtain ⟨dwa, dwb⟩ := sub_spec wa wa' wb wb'
  obtain ⟨dmpa, dmpb⟩ := sub_spec mpa mpa' mpb mpb'
  obtain ⟨dmwa, dmwb⟩ := sub_spec mwa mwa' mwb mwb'
  obtain ⟨dupsa, dupsb⟩ := sub_spec upsa upsa' upsb upsb'
  set dπw : ℕ → Ω → ℝ := fun t ω => πw t ω - πw' t ω with hdπw
  set dx : ℕ → Ω → ℝ := fun t ω => x t ω - x' t ω with hdx
  set dw : ℕ → Ω → ℝ := fun t ω => w t ω - w' t ω with hdw
  set dmp : ℕ → Ω → ℝ := fun t ω => mp t ω - mp' t ω with hdmp
  set dmw : ℕ → Ω → ℝ := fun t ω => mw t ω - mw' t ω with hdmw
  set dups : ℕ → Ω → ℝ := fun t ω => ups t ω - ups' t ω with hdups
  set dπ' : ℕ → Ω → ℝ := fun t ω => π t ω - π' t ω with hdπ'
  set Lw : ℕ → Ω → ℝ := lagW (fun _ => 0) dw with hLw
  set Lmp : ℕ → Ω → ℝ := lagW (fun _ => 0) dmp with hLmp
  set Lmw : ℕ → Ω → ℝ := lagW (fun _ => 0) dmw with hLmw
  have Idπ := integrable_of_adapted S dπa dπb
  have Idπw := integrable_of_adapted S dπwa dπwb
  have Idx := integrable_of_adapted S dxa dxb
  have Idw := integrable_of_adapted S dwa dwb
  have Idmp := integrable_of_adapted S dmpa dmpb
  have Idmw := integrable_of_adapted S dmwa dmwb
  have Idups := integrable_of_adapted S dupsa dupsb
  have lagK : ∀ {d : ℕ → Ω → ℝ}, StronglyAdapted S.𝓕 d → S.BddProc d → ∀ n,
      StronglyMeasurable[S.𝓕 n] (lagW (fun _ => 0) d n) ∧
        Integrable (lagW (fun _ => 0) d n) S.μ := by
    intro d hda hdb n
    cases n with
    | zero => exact ⟨stronglyMeasurable_const, integrable_const _⟩
    | succ s => exact ⟨(hda s).mono (S.𝓕.mono (Nat.le_succ s)), integrable_of_adapted S hda hdb s⟩
  -- the homogeneous a.s. equations
  have eP1 : ∀ m, dπ' m =ᵐ[S.μ] fun ω => P.kp * dx m ω + P.xip * dw m ω + 0 * dw m ω +
      P.beta * S.E m (dπ' (m + 1)) ω := fun m => by
    filter_upwards [P1 m, Q1 m, S.E_sub (Iπ (m + 1)) (Iπ' (m + 1)) m] with ω e1 e2 e3
    have e3' : S.E m (dπ' (m + 1)) ω = S.E m (π (m + 1)) ω - S.E m (π' (m + 1)) ω := e3
    rw [e3']
    simp only [hdπ', hdx, hdw]
    linear_combination e1 - e2
  have eP2 : ∀ m, dπw m =ᵐ[S.μ] fun ω => P.kw * dx m ω + (-P.xiw) * dw m ω + 0 * dw m ω +
      P.beta * S.E m (dπw (m + 1)) ω := fun m => by
    filter_upwards [P2 m, Q2 m, S.E_sub (Iπw (m + 1)) (Iπw' (m + 1)) m] with ω e1 e2 e3
    have e3' : S.E m (dπw (m + 1)) ω = S.E m (πw (m + 1)) ω - S.E m (πw' (m + 1)) ω := e3
    rw [e3']
    simp only [hdπw, hdx, hdw]
    linear_combination e1 - e2
  have eP3 : ∀ m, dw m =ᵐ[S.μ] fun ω => 1 * Lw m ω + 1 * dπw m ω + (-1) * dπ' m ω +
      0 * S.E m (dw (m + 1)) ω := fun m => by
    filter_upwards [P3 m, Q3 m] with ω e1 e2
    have hl := lagW_sub w₀ w w' m ω
    simp only [hLw, hdw, hdπw, hdπ']
    rw [← hl]
    linear_combination e1 - e2
  have eF1 : ∀ m, dmp m =ᵐ[S.μ] fun ω => (-P.lp) * dπ' m ω + 1 * Lmp m ω + (-1) * dups m ω +
      0 * S.E m (dmp (m + 1)) ω := fun m => by
    filter_upwards [F1 m, G1 m] with ω e1 e2
    simp only [Pi.zero_apply] at e1 e2
    have hl := lagW_sub mp₀ mp mp' m ω
    simp only [hLmp, hdmp, hdπ', hdups]
    rw [← hl]
    linear_combination e1 - e2
  have eF2 : ∀ m, dmw m =ᵐ[S.μ] fun ω => (-P.lw) * dπw m ω + 1 * Lmw m ω + 1 * dups m ω +
      0 * S.E m (dmw (m + 1)) ω := fun m => by
    filter_upwards [F2 m, G2 m] with ω e1 e2
    simp only [Pi.zero_apply] at e1 e2
    have hl := lagW_sub mw₀ mw mw' m ω
    simp only [hLmw, hdmw, hdπw, hdups]
    rw [← hl]
    linear_combination e1 - e2
  have eF3 : ∀ m, dx m =ᵐ[S.μ] fun ω => (P.kp / P.lx) * dmp m ω + (P.kw / P.lx) * dmw m ω +
      0 * dmw m ω + 0 * S.E m (dx (m + 1)) ω := fun m => by
    filter_upwards [F3 m, G3 m] with ω e1 e2
    simp only [Pi.zero_apply] at e1 e2
    simp only [hdx, hdmp, hdmw]
    field_simp
    linear_combination e1 - e2
  have eF4 : ∀ m, dups m =ᵐ[S.μ] fun ω => P.xip * dmp m ω + (-P.xiw) * dmw m ω + 0 * dmw m ω +
      P.beta * S.E m (dups (m + 1)) ω := fun m => by
    filter_upwards [F4 m, G4 m, S.E_sub (Iups (m + 1)) (Iups' (m + 1)) m] with ω e1 e2 e3
    have e3' : S.E m (dups (m + 1)) ω = S.E m (ups (m + 1)) ω - S.E m (ups' (m + 1)) ω := e3
    rw [e3']
    simp only [hdups, hdmp, hdmw]
    linear_combination e1 - e2
  -- the step: the forecasts at `n` vanish
  have step : ∀ n, (∀ᵐ ω ∂S.μ, Lw n ω = 0) → (∀ᵐ ω ∂S.μ, Lmp n ω = 0) →
      (∀ᵐ ω ∂S.μ, Lmw n ω = 0) → ∀ᵐ ω ∂S.μ, dπ' n ω = 0 ∧ dπw n ω = 0 ∧ dx n ω = 0 ∧
        dw n ω = 0 ∧ dmp n ω = 0 ∧ dmw n ω = 0 ∧ dups n ω = 0 := by
    intro n hLw hLmp hLmw
    have hk : ∀ k, n ≤ n + k := fun k => Nat.le_add_right n k
    have c1 := fun k => fc_lin (hk k) _ _ _ _ (eP1 (n + k)) (Idx _) (Idw _) (Idw _)
    have c2 := fun k => fc_lin (hk k) _ _ _ _ (eP2 (n + k)) (Idx _) (Idw _) (Idw _)
    have c3 := fun k => fc_lin (hk k) _ _ _ _ (eP3 (n + k)) (lagK dwa dwb _).2 (Idπw _) (Idπ _)
    have c4 := fun k => fc_lin (hk k) _ _ _ _ (eF1 (n + k)) (Idπ _) (lagK dmpa dmpb _).2
      (Idups _)
    have c5 := fun k => fc_lin (hk k) _ _ _ _ (eF2 (n + k)) (Idπw _) (lagK dmwa dmwb _).2
      (Idups _)
    have c6 := fun k => fc_lin (hk k) _ _ _ _ (eF3 (n + k)) (Idmp _) (Idmw _) (Idmw _)
    have c7 := fun k => fc_lin (hk k) _ _ _ _ (eF4 (n + k)) (Idmp _) (Idmw _) (Idmw _)
    have eLw : S.E n (Lw n) = Lw n := S.E_of_stronglyMeasurable (lagK dwa dwb n).1
      (lagK dwa dwb n).2
    have eLmp : S.E n (Lmp n) = Lmp n := S.E_of_stronglyMeasurable (lagK dmpa dmpb n).1
      (lagK dmpa dmpb n).2
    have eLmw : S.E n (Lmw n) = Lmw n := S.E_of_stronglyMeasurable (lagK dmwa dmwb n).1
      (lagK dmwa dmwb n).2
    obtain ⟨B1, hB1⟩ := dπb
    obtain ⟨B2, hB2⟩ := dπwb
    obtain ⟨B3, hB3⟩ := dxb
    obtain ⟨B4, hB4⟩ := dwb
    obtain ⟨B5, hB5⟩ := dmpb
    obtain ⟨B6, hB6⟩ := dmwb
    obtain ⟨B7, hB7⟩ := dupsb
    have hE0 : ∀ {d : ℕ → Ω → ℝ}, StronglyMeasurable[S.𝓕 n] (d n) → Integrable (d n) S.μ →
        S.E n (d n) = d n := fun hm hi => S.E_of_stronglyMeasurable hm hi
    filter_upwards [ae_all_iff.2 c1, ae_all_iff.2 c2, ae_all_iff.2 c3, ae_all_iff.2 c4,
      ae_all_iff.2 c5, ae_all_iff.2 c6, ae_all_iff.2 c7,
      ae_all_iff.2 fun k => S.abs_E_le (hB1 (n + k)) n,
      ae_all_iff.2 fun k => S.abs_E_le (hB2 (n + k)) n,
      ae_all_iff.2 fun k => S.abs_E_le (hB3 (n + k)) n,
      ae_all_iff.2 fun k => S.abs_E_le (hB4 (n + k)) n,
      ae_all_iff.2 fun k => S.abs_E_le (hB5 (n + k)) n,
      ae_all_iff.2 fun k => S.abs_E_le (hB6 (n + k)) n,
      ae_all_iff.2 fun k => S.abs_E_le (hB7 (n + k)) n, hLw, hLmp, hLmw]
      with ω h1 h2 h3 h4 h5 h6 h7 b1 b2 b3 b4 b5 b6 b7 l1 l2 l3
    -- the perfect-foresight forecast paths
    set fπ : ℕ → Unit → ℝ := fun k _ => S.E n (dπ' (n + k)) ω with hfπ
    set fπw : ℕ → Unit → ℝ := fun k _ => S.E n (dπw (n + k)) ω with hfπw
    set fx : ℕ → Unit → ℝ := fun k _ => S.E n (dx (n + k)) ω with hfx
    set fw : ℕ → Unit → ℝ := fun k _ => S.E n (dw (n + k)) ω with hfw
    set fmp : ℕ → Unit → ℝ := fun k _ => S.E n (dmp (n + k)) ω with hfmp
    set fmw : ℕ → Unit → ℝ := fun k _ => S.E n (dmw (n + k)) ω with hfmw
    set fups : ℕ → Unit → ℝ := fun k _ => S.E n (dups (n + k)) ω with hfups
    have lw0 : S.E n (Lw (n + 0)) ω = 0 := by rw [add_zero, eLw]; exact l1
    have lmp0 : S.E n (Lmp (n + 0)) ω = 0 := by rw [add_zero, eLmp]; exact l2
    have lmw0 : S.E n (Lmw (n + 0)) ω = 0 := by rw [add_zero, eLmw]; exact l3
    have hlagf : ∀ {d : ℕ → Ω → ℝ} {f : ℕ → Unit → ℝ}, (∀ k, f k () = S.E n (d (n + k)) ω) →
        S.E n (lagW (fun _ => 0) d (n + 0)) ω = 0 →
        ∀ t, S.E n (lagW (fun _ => 0) d (n + t)) ω = lagW (fun _ => 0) f t () := by
      intro d f hf h0 t
      cases t with
      | zero => exact h0
      | succ j => exact (hf j).symm
    have hw' := hlagf (d := dw) (f := fw) (fun _ => rfl) lw0
    have hmp' := hlagf (d := dmp) (f := fmp) (fun _ => rfl) lmp0
    have hmw' := hlagf (d := dmw) (f := fmw) (fun _ => rfl) lmw0
    have hp : PlanSW perfectForesight (P0 P) (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) fπ fπw
        fx fw := by
      refine ⟨fun t _ => ?_, fun t _ => ?_, fun t _ => ?_, fun _ => rfl, fun _ => rfl,
        fun _ => rfl, fun _ => rfl, ⟨B1, fun t _ => b1 t⟩, ⟨B2, fun t _ => b2 t⟩,
        ⟨B3, fun t _ => b3 t⟩, ⟨B4, fun t _ => b4 t⟩⟩
      · change S.E n (dπ' (n + t)) ω = P.kp * (S.E n (dx (n + t)) ω + 0) +
          P.xip * (S.E n (dw (n + t)) ω - 0) + P.beta * S.E n (dπ' (n + t + 1)) ω
        rw [h1 t]
        ring
      · change S.E n (dπw (n + t)) ω = P.kw * (S.E n (dx (n + t)) ω + 0) +
          P.xiw * (0 - S.E n (dw (n + t)) ω) + P.beta * S.E n (dπw (n + t + 1)) ω
        rw [h2 t]
        ring
      · change S.E n (dw (n + t)) ω = lagW (fun _ => 0) fw t () + S.E n (dπw (n + t)) ω -
          S.E n (dπ' (n + t)) ω
        rw [h3 t, ← hw' t]
        ring
    have hf : FOCsw perfectForesight (P0 P) (fun _ => 0) (fun _ => 0) fπ fπw fx fmp fmw fups := by
      intro t _
      refine ⟨?_, ?_, ?_, ?_⟩
      · change P.lp * S.E n (dπ' (n + t)) ω + S.E n (dmp (n + t)) ω -
          lagW (fun _ => 0) fmp t () + S.E n (dups (n + t)) ω = 0
        rw [h4 t, ← hmp' t]
        ring
      · change P.lw * S.E n (dπw (n + t)) ω + S.E n (dmw (n + t)) ω -
          lagW (fun _ => 0) fmw t () - S.E n (dups (n + t)) ω = 0
        rw [h5 t, ← hmw' t]
        ring
      · change P.lx * (S.E n (dx (n + t)) ω - 0) - P.kp * S.E n (dmp (n + t)) ω -
          P.kw * S.E n (dmw (n + t)) ω = 0
        rw [h6 t]
        field_simp
        ring
      · change S.E n (dups (n + t)) ω = P.xip * S.E n (dmp (n + t)) ω -
          P.xiw * S.E n (dmw (n + t)) ω + P.beta * S.E n (dups (n + t + 1)) ω
        rw [h7 t]
        ring
    obtain ⟨z1, z2, z3, z4, z5, z6, z7⟩ := pf_zero hβ0 hβ1 hlx hlp hlw hkp hkw hxip hxiw hne hR
      hp hf ⟨B7, fun t _ => b7 t⟩ 0
    change S.E n (dπ' (n + 0)) ω = 0 at z1
    change S.E n (dπw (n + 0)) ω = 0 at z2
    change S.E n (dx (n + 0)) ω = 0 at z3
    change S.E n (dw (n + 0)) ω = 0 at z4
    change S.E n (dmp (n + 0)) ω = 0 at z5
    change S.E n (dmw (n + 0)) ω = 0 at z6
    change S.E n (dups (n + 0)) ω = 0 at z7
    rw [add_zero] at z1 z2 z3 z4 z5 z6 z7
    rw [hE0 (dπa n) (Idπ n)] at z1
    rw [hE0 (dπwa n) (Idπw n)] at z2
    rw [hE0 (dxa n) (Idx n)] at z3
    rw [hE0 (dwa n) (Idw n)] at z4
    rw [hE0 (dmpa n) (Idmp n)] at z5
    rw [hE0 (dmwa n) (Idmw n)] at z6
    rw [hE0 (dupsa n) (Idups n)] at z7
    exact ⟨z1, z2, z3, z4, z5, z6, z7⟩
  -- induction on the date
  have hz : ∀ n, ∀ᵐ ω ∂S.μ, dπ' n ω = 0 ∧ dπw n ω = 0 ∧ dx n ω = 0 ∧ dw n ω = 0 ∧
      dmp n ω = 0 ∧ dmw n ω = 0 ∧ dups n ω = 0 := by
    intro n
    induction n with
    | zero =>
      exact step 0 (Eventually.of_forall fun _ => rfl) (Eventually.of_forall fun _ => rfl)
        (Eventually.of_forall fun _ => rfl)
    | succ m ih =>
      exact step (m + 1) (ih.mono fun ω h => h.2.2.2.1) (ih.mono fun ω h => h.2.2.2.2.1)
        (ih.mono fun ω h => h.2.2.2.2.2.1)
  intro t
  refine ⟨(hz t).mono fun ω h => sub_eq_zero.mp h.1, (hz t).mono fun ω h => sub_eq_zero.mp h.2.1,
    (hz t).mono fun ω h => sub_eq_zero.mp h.2.2.1,
    (hz t).mono fun ω h => sub_eq_zero.mp h.2.2.2.1,
    (hz t).mono fun ω h => sub_eq_zero.mp h.2.2.2.2.1,
    (hz t).mono fun ω h => sub_eq_zero.mp h.2.2.2.2.2.1,
    (hz t).mono fun ω h => sub_eq_zero.mp h.2.2.2.2.2.2⟩

/-! ### Existence and uniqueness -/

variable (S) in
/-- **Woodford (2003), (2.11)–(2.20), `κ_w ≠ κ_p`, on every filtered probability space: existence
and a.s. uniqueness for general initial values.** Under the root condition
`InflTargetStickyWages.StableRoots`, for every bounded adapted disturbance `(u, w^n)` and every
essentially bounded initial values `(w_{t₀−1}, φ_{p,t₀−1}, φ_{w,t₀−1})` known at date 0, there is a
bounded adapted plan with bounded adapted multipliers satisfying (2.11)–(2.13) and (2.16)–(2.19)
a.s., and every other such plan agrees with it a.s. at every date. -/
theorem existsUniqueM_of_stableRoots {P : SW} (hβ0 : 0 < P.beta) (hβ1 : P.beta < 1)
    (hlx : 0 < P.lx) (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hkp : 0 < P.kp) (hkw : 0 < P.kw)
    (hxip : 0 < P.xip) (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp) (hR : StableRoots P)
    (u wn : ℕ → Ω → ℝ) (hu : S.BddProc u) (hua : StronglyAdapted S.𝓕 u) (hwn : S.BddProc wn)
    (hwna : StronglyAdapted S.𝓕 wn) {w₀ mp₀ mw₀ : Ω → ℝ} (kw0 : StronglyMeasurable[S.𝓕 0] w₀)
    (kmp0 : StronglyMeasurable[S.𝓕 0] mp₀) (kmw0 : StronglyMeasurable[S.𝓕 0] mw₀) {B : ℝ}
    (bw0 : ∀ᵐ ω ∂S.μ, |w₀ ω| ≤ B) (bmp0 : ∀ᵐ ω ∂S.μ, |mp₀ ω| ≤ B)
    (bmw0 : ∀ᵐ ω ∂S.μ, |mw₀ ω| ≤ B) :
    ∃ π πw x w mp mw ups, (PlanSWM S P w₀ u wn π πw x w ∧
      FOCswM S P mp₀ mw₀ π πw x mp mw ups) ∧
      ∀ π' πw' x' w' mp' mw' ups', PlanSWM S P w₀ u wn π' πw' x' w' →
        FOCswM S P mp₀ mw₀ π' πw' x' mp' mw' ups' →
        ∀ t, π' t =ᵐ[S.μ] π t ∧ πw' t =ᵐ[S.μ] πw t ∧ x' t =ᵐ[S.μ] x t ∧ w' t =ᵐ[S.μ] w t ∧
          mp' t =ᵐ[S.μ] mp t ∧ mw' t =ᵐ[S.μ] mw t ∧ ups' t =ᵐ[S.μ] ups t := by
  obtain ⟨π, πw, x, w, mp, mw, ups, hp, hf⟩ := exists_meas_of_stableRootsG S hβ0 hβ1 hlx hlp hlw
    hkp hkw hxip hxiw hne hR u wn hu hua hwn hwna kw0 kmp0 kmw0 bw0 bmp0 bmw0
  exact ⟨π, πw, x, w, mp, mw, ups, ⟨hp, hf⟩, fun π' πw' x' w' mp' mw' ups' hp' hf' =>
    uniqueM S hβ0 hβ1 hlx hlp hlw hkp hkw hxip hxiw hne hR hp' hf' hp hf⟩

variable (S) in
/-- **Woodford (2003), (2.20), `κ_w ≠ κ_p` (the exact region on a probability space, full
form)**: on every filtered probability space with Mathlib's conditional expectation, for every
bounded adapted disturbance and every essentially bounded initial values known at date 0 there is
an a.s. unique bounded adapted plan with bounded adapted multipliers satisfying (2.11)–(2.13) and
(2.16)–(2.19) a.s. **iff** the root condition `InflTargetStickyWages.StableRoots` holds. -/
theorem existsUniqueM_iff_stableRoots {P : SW} (hβ0 : 0 < P.beta) (hβ1 : P.beta < 1)
    (hlx : 0 < P.lx) (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hkp : 0 < P.kp) (hkw : 0 < P.kw)
    (hxip : 0 < P.xip) (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp) :
    (∀ u wn : ℕ → Ω → ℝ, S.BddProc u → StronglyAdapted S.𝓕 u → S.BddProc wn →
      StronglyAdapted S.𝓕 wn → ∀ w₀ mp₀ mw₀ : Ω → ℝ, StronglyMeasurable[S.𝓕 0] w₀ →
      StronglyMeasurable[S.𝓕 0] mp₀ → StronglyMeasurable[S.𝓕 0] mw₀ → ∀ B : ℝ,
      (∀ᵐ ω ∂S.μ, |w₀ ω| ≤ B) → (∀ᵐ ω ∂S.μ, |mp₀ ω| ≤ B) → (∀ᵐ ω ∂S.μ, |mw₀ ω| ≤ B) →
      ∃ π πw x w mp mw ups, (PlanSWM S P w₀ u wn π πw x w ∧
        FOCswM S P mp₀ mw₀ π πw x mp mw ups) ∧
        ∀ π' πw' x' w' mp' mw' ups', PlanSWM S P w₀ u wn π' πw' x' w' →
          FOCswM S P mp₀ mw₀ π' πw' x' mp' mw' ups' →
          ∀ t, π' t =ᵐ[S.μ] π t ∧ πw' t =ᵐ[S.μ] πw t ∧ x' t =ᵐ[S.μ] x t ∧ w' t =ᵐ[S.μ] w t ∧
            mp' t =ᵐ[S.μ] mp t ∧ mw' t =ᵐ[S.μ] mw t ∧ ups' t =ᵐ[S.μ] ups t) ↔
      StableRoots P := by
  refine ⟨fun h => stableRoots_of_exists_meas S hβ0 hβ1 hlx hlp hlw hkp hkw hxip hxiw hne
    fun u wn hu hua hwn hwna a b => ?_, fun hR u wn hu hua hwn hwna w₀ mp₀ mw₀ kw0 kmp0 kmw0 B
      bw0 bmp0 bmw0 => existsUniqueM_of_stableRoots S hβ0 hβ1 hlx hlp hlw hkp hkw hxip hxiw hne
        hR u wn hu hua hwn hwna kw0 kmp0 kmw0 bw0 bmp0 bmw0⟩
  obtain ⟨π, πw, x, w, mp, mw, ups, ⟨hp, hf⟩, -⟩ := h u wn hu hua hwn hwna (fun _ => 0)
    (fun _ => a) (fun _ => b) stronglyMeasurable_const stronglyMeasurable_const
    stronglyMeasurable_const (|a| + |b|) (Eventually.of_forall fun _ => by
      simp only [abs_zero]
      positivity) (Eventually.of_forall fun _ => by linarith [abs_nonneg b])
    (Eventually.of_forall fun _ => by linarith [abs_nonneg a])
  exact ⟨π, πw, x, w, mp, mw, ups, hp, hf⟩

end Woodford.OptimalPolicyRules.TidyR6bStickyGeneral
