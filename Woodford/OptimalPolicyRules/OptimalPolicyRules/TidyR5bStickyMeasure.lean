/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR5bStickyBoundary
import OptimalPolicyRules.ExpectationsMeasure

/-!
# The determinacy region for `κ_w ≠ κ_p` on a genuine probability space

Woodford (2003), *Interest and Prices*, Chapter 8, §2.2, pp. 565–567, (2.11)–(2.20).

The model (2.11)–(2.13) and the first-order conditions (2.16)–(2.19) are stated on a filtered
probability space (`ExpectationsMeasure.MeasExpectationSystem`, Mathlib's `condExp`), with every
equation holding almost surely and every process essentially bounded and adapted
(`PlanSWM`, `FOCswM`). This covers genuine infinite-horizon uncertainty (for instance the i.i.d.
systems of the module ExpectationsMeasureIID), which the exact `ExpectationSystem` cannot carry.

The tool is the unconditional mean path `ŷ_t = ∫ y_t dP` (`meanPath`): by
`ExpectationsMeasure.MeasExpectationSystem.integral_E` (`∫ E_t x = ∫ x`) and linearity of the
integral, the mean path of an almost-sure solution is a perfect-foresight solution of the
mean disturbances (`planSWM_mean`, `focSWM_mean`), and a deterministic disturbance is its own
mean.

## Main results

* `stableRoots_of_exists_meas`: **the "only if" half of the exact region on a probability
  space** — if a bounded adapted plan satisfying the first-order conditions almost surely exists
  for every bounded adapted disturbance process and every pair of constant initial multipliers,
  then the root condition `InflTargetStickyWages.StableRoots` holds.
* `foc_not_exists_boundary_meas`: on the ellipse the resonant path `u_t = Re μᵗ` has no such
  plan, on any filtered probability space.
* `not_exists_meas_of_not_stableRoots`: outside the root condition some bounded adapted data
  have no almost-sure solution.
-/

namespace Woodford.OptimalPolicyRules.TidyR5bStickyMeasure

open MeasureTheory InflTargetInertia InflTargetStickyWages TidyR5bStickyBoundary
open ExpectationsMeasure

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Woodford (2003), (2.11)–(2.13), on a filtered probability space: the three structural
equations hold almost surely at every date, and `π, π^w, x, w` are adapted and essentially
bounded. -/
def PlanSWM (P : SW) (w₀ : Ω → ℝ) (u wn π πw x w : ℕ → Ω → ℝ) : Prop :=
  (∀ t, π t =ᵐ[S.μ] fun ω => P.kp * (x t ω + u t ω) + P.xip * (w t ω - wn t ω) +
    P.beta * S.E t (π (t + 1)) ω) ∧
  (∀ t, πw t =ᵐ[S.μ] fun ω => P.kw * (x t ω + u t ω) + P.xiw * (wn t ω - w t ω) +
    P.beta * S.E t (πw (t + 1)) ω) ∧
  (∀ t, w t =ᵐ[S.μ] fun ω => lagW w₀ w t ω + πw t ω - π t ω) ∧
  StronglyAdapted S.𝓕 π ∧ StronglyAdapted S.𝓕 πw ∧ StronglyAdapted S.𝓕 x ∧
  StronglyAdapted S.𝓕 w ∧ S.BddProc π ∧ S.BddProc πw ∧ S.BddProc x ∧ S.BddProc w

/-- Woodford (2003), (2.16)–(2.19), on a filtered probability space: the first-order conditions
hold almost surely at every date (initial multipliers `mp₀, mw₀`), with adapted, essentially
bounded multipliers. -/
def FOCswM (P : SW) (mp₀ mw₀ : Ω → ℝ) (π πw x mp mw ups : ℕ → Ω → ℝ) : Prop :=
  (∀ t, (fun ω => P.lp * π t ω + mp t ω - lagW mp₀ mp t ω + ups t ω) =ᵐ[S.μ] 0) ∧
  (∀ t, (fun ω => P.lw * πw t ω + mw t ω - lagW mw₀ mw t ω - ups t ω) =ᵐ[S.μ] 0) ∧
  (∀ t, (fun ω => P.lx * (x t ω - P.xstar) - P.kp * mp t ω - P.kw * mw t ω) =ᵐ[S.μ] 0) ∧
  (∀ t, ups t =ᵐ[S.μ] fun ω => P.xip * mp t ω - P.xiw * mw t ω +
    P.beta * S.E t (ups (t + 1)) ω) ∧
  StronglyAdapted S.𝓕 mp ∧ StronglyAdapted S.𝓕 mw ∧ StronglyAdapted S.𝓕 ups ∧
  S.BddProc mp ∧ S.BddProc mw ∧ S.BddProc ups

/-- Woodford (2003), §2.2 (unconditional means): the mean path `ŷ_t = ∫ y_t dP` as a
perfect-foresight process. -/
noncomputable def meanPath (y : ℕ → Ω → ℝ) : ℕ → Unit → ℝ :=
  fun t _ => ∫ ω, y t ω ∂S.μ

/-- Woodford (2003), §2.2: an adapted, essentially bounded process is integrable at every
date. -/
theorem integrable_of_adapted {y : ℕ → Ω → ℝ} (ha : StronglyAdapted S.𝓕 y) (hb : S.BddProc y)
    (t : ℕ) : Integrable (y t) S.μ := by
  obtain ⟨M, hM⟩ := hb
  exact Integrable.of_bound ((ha t).mono (S.𝓕.le t)).aestronglyMeasurable M
    ((hM t).mono fun ω h => by rwa [Real.norm_eq_abs])

/-- Woodford (2003), §2.2: the mean path of an essentially bounded process is bounded. -/
theorem meanPath_bounded {y : ℕ → Ω → ℝ} (hb : S.BddProc y) : BoundedProc (meanPath S y) := by
  obtain ⟨M, hM⟩ := hb
  refine ⟨M, fun t _ => ?_⟩
  have h := norm_integral_le_of_norm_le_const (μ := S.μ) (f := y t) (C := M)
    ((hM t).mono fun ω h => by rwa [Real.norm_eq_abs])
  simpa [meanPath] using h

/-- Woodford (2003), §2.2: a deterministic process is its own mean. -/
theorem meanPath_const (g : ℕ → Unit → ℝ) : meanPath S (fun t _ => g t ()) = g := by
  funext t ω
  cases ω
  simp [meanPath]

/-- Woodford (2003), §2.2: the mean of a lag with a constant initial value is the lag of the
mean. -/
theorem integral_lagW (c : ℝ) (y : ℕ → Ω → ℝ) (t : ℕ) :
    ∫ ω, lagW (fun _ => c) y t ω ∂S.μ = lagW (fun _ => c) (meanPath S y) t () := by
  cases t with
  | zero => simp
  | succ t => rfl

/-- Woodford (2003), §2.2: an adapted, essentially bounded lag is integrable. -/
theorem integrable_lagW (c : ℝ) {y : ℕ → Ω → ℝ} (ha : StronglyAdapted S.𝓕 y)
    (hb : S.BddProc y) (t : ℕ) : Integrable (lagW (fun _ => c) y t) S.μ := by
  cases t with
  | zero => exact integrable_const c
  | succ t => exact integrable_of_adapted S ha hb t

/-- Woodford (2003), (2.11)–(2.13) (unconditional means): the mean path of an almost-sure plan
(constant `w_{t₀−1}`) is a bounded perfect-foresight plan for the mean disturbances. -/
theorem planSWM_mean (P : SW) (c : ℝ) {u wn π πw x w : ℕ → Ω → ℝ}
    (hp : PlanSWM S P (fun _ => c) u wn π πw x w) (hu : ∀ t, Integrable (u t) S.μ)
    (hwn : ∀ t, Integrable (wn t) S.μ) :
    PlanSW perfectForesight P (fun _ => c) (meanPath S u) (meanPath S wn) (meanPath S π)
      (meanPath S πw) (meanPath S x) (meanPath S w) := by
  obtain ⟨h1, h2, h3, hπa, hπwa, hxa, hwa, hπb, hπwb, hxb, hwb⟩ := hp
  have iπ := integrable_of_adapted S hπa hπb
  have iπw := integrable_of_adapted S hπwa hπwb
  have ix := integrable_of_adapted S hxa hxb
  have iw := integrable_of_adapted S hwa hwb
  refine ⟨fun t _ => ?_, fun t _ => ?_, fun t _ => ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, meanPath_bounded S hπb, meanPath_bounded S hπwb, meanPath_bounded S hxb,
    meanPath_bounded S hwb⟩
  · have i1 : Integrable (fun ω => P.kp * (x t ω + u t ω)) S.μ := ((ix t).add (hu t)).const_mul _
    have i2 : Integrable (fun ω => P.xip * (w t ω - wn t ω)) S.μ :=
      ((iw t).sub (hwn t)).const_mul _
    have i12 : Integrable (fun ω => P.kp * (x t ω + u t ω) + P.xip * (w t ω - wn t ω)) S.μ :=
      i1.add i2
    have i3 : Integrable (fun ω => P.beta * S.E t (π (t + 1)) ω) S.μ :=
      (S.integrable_E t _).const_mul _
    have e := integral_congr_ae (h1 t)
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_add (ix t) (hu t), integral_sub (iw t) (hwn t),
      S.integral_E] at e
    exact e
  · have i1 : Integrable (fun ω => P.kw * (x t ω + u t ω)) S.μ := ((ix t).add (hu t)).const_mul _
    have i2 : Integrable (fun ω => P.xiw * (wn t ω - w t ω)) S.μ :=
      ((hwn t).sub (iw t)).const_mul _
    have i12 : Integrable (fun ω => P.kw * (x t ω + u t ω) + P.xiw * (wn t ω - w t ω)) S.μ :=
      i1.add i2
    have i3 : Integrable (fun ω => P.beta * S.E t (πw (t + 1)) ω) S.μ :=
      (S.integrable_E t _).const_mul _
    have e := integral_congr_ae (h2 t)
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_add (ix t) (hu t), integral_sub (hwn t) (iw t),
      S.integral_E] at e
    exact e
  · have il := integrable_lagW S c hwa hwb t
    have i12 : Integrable (fun ω => lagW (fun _ => c) w t ω + πw t ω) S.μ := il.add (iπw t)
    have e := integral_congr_ae (h3 t)
    rw [integral_sub i12 (iπ t), integral_add il (iπw t), integral_lagW] at e
    exact e

/-- Woodford (2003), (2.16)–(2.19) (unconditional means): the mean paths of a plan and
multipliers satisfying the first-order conditions almost surely (constant initial multipliers)
satisfy the perfect-foresight first-order conditions. -/
theorem focSWM_mean (P : SW) (a b : ℝ) {π πw x mp mw ups : ℕ → Ω → ℝ}
    (hπ : ∀ t, Integrable (π t) S.μ) (hπw : ∀ t, Integrable (πw t) S.μ)
    (hx : ∀ t, Integrable (x t) S.μ) (hf : FOCswM S P (fun _ => a) (fun _ => b) π πw x mp mw ups) :
    FOCsw perfectForesight P (fun _ => a) (fun _ => b) (meanPath S π) (meanPath S πw)
      (meanPath S x) (meanPath S mp) (meanPath S mw) (meanPath S ups) := by
  obtain ⟨f1, f2, f3, f4, hmpa, hmwa, hupa, hmpb, hmwb, hupb⟩ := hf
  have imp := integrable_of_adapted S hmpa hmpb
  have imw := integrable_of_adapted S hmwa hmwb
  have iup := integrable_of_adapted S hupa hupb
  intro t _
  refine ⟨?_, ?_, ?_, ?_⟩
  · have ia : Integrable (fun ω => P.lp * π t ω) S.μ := (hπ t).const_mul _
    have il := integrable_lagW S a hmpa hmpb t
    have i2 : Integrable (fun ω => P.lp * π t ω + mp t ω) S.μ := ia.add (imp t)
    have i3 : Integrable (fun ω => P.lp * π t ω + mp t ω - lagW (fun _ => a) mp t ω) S.μ :=
      i2.sub il
    have e := integral_congr_ae (f1 t)
    rw [integral_add i3 (iup t), integral_sub i2 il, integral_add ia (imp t), integral_const_mul,
      integral_lagW] at e
    simpa [meanPath] using e
  · have ia : Integrable (fun ω => P.lw * πw t ω) S.μ := (hπw t).const_mul _
    have il := integrable_lagW S b hmwa hmwb t
    have i2 : Integrable (fun ω => P.lw * πw t ω + mw t ω) S.μ := ia.add (imw t)
    have i3 : Integrable (fun ω => P.lw * πw t ω + mw t ω - lagW (fun _ => b) mw t ω) S.μ :=
      i2.sub il
    have e := integral_congr_ae (f2 t)
    rw [integral_sub i3 (iup t), integral_sub i2 il, integral_add ia (imw t), integral_const_mul,
      integral_lagW] at e
    simpa [meanPath] using e
  · have ixs : Integrable (fun ω => x t ω - P.xstar) S.μ := (hx t).sub (integrable_const _)
    have ia : Integrable (fun ω => P.lx * (x t ω - P.xstar)) S.μ := ixs.const_mul _
    have ib : Integrable (fun ω => P.kp * mp t ω) S.μ := (imp t).const_mul _
    have ic : Integrable (fun ω => P.kw * mw t ω) S.μ := (imw t).const_mul _
    have iab : Integrable (fun ω => P.lx * (x t ω - P.xstar) - P.kp * mp t ω) S.μ := ia.sub ib
    have e := integral_congr_ae (f3 t)
    rw [integral_sub iab ic, integral_sub ia ib, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_sub (hx t) (integrable_const _)] at e
    simpa [meanPath] using e
  · have ib : Integrable (fun ω => P.xip * mp t ω) S.μ := (imp t).const_mul _
    have ic : Integrable (fun ω => P.xiw * mw t ω) S.μ := (imw t).const_mul _
    have ibc : Integrable (fun ω => P.xip * mp t ω - P.xiw * mw t ω) S.μ := ib.sub ic
    have id : Integrable (fun ω => P.beta * S.E t (ups (t + 1)) ω) S.μ :=
      (S.integrable_E t _).const_mul _
    have e := integral_congr_ae (f4 t)
    rw [integral_add ibc id, integral_sub ib ic, integral_const_mul, integral_const_mul,
      integral_const_mul, S.integral_E] at e
    exact e

/-- Woodford (2003), §2.2: a deterministic process is adapted and essentially bounded. -/
theorem det_adapted_bdd (g : ℕ → ℝ) {M : ℝ} (hg : ∀ t, |g t| ≤ M) :
    StronglyAdapted S.𝓕 (fun t (_ : Ω) => g t) ∧ S.BddProc (fun t (_ : Ω) => g t) :=
  ⟨fun _ => stronglyMeasurable_const, ⟨M, fun t => Filter.Eventually.of_forall fun _ => hg t⟩⟩

/-- **Woodford (2003), §2.2, `κ_w ≠ κ_p` (THE "ONLY IF" HALF OF THE EXACT REGION ON A
PROBABILITY SPACE)**: on any filtered probability space, if for every bounded adapted
disturbance process and every pair of constant initial multipliers (`w_{t₀−1} = 0`) there is a
bounded adapted plan with bounded adapted multipliers satisfying (2.11)–(2.13) and the
first-order conditions (2.16)–(2.19) almost surely, then the root condition `StableRoots P`
holds. -/
theorem stableRoots_of_exists_meas {P : SW} (hβ0 : 0 < P.beta) (hβ1 : P.beta < 1)
    (hlx : 0 < P.lx) (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hkp : 0 < P.kp) (hkw : 0 < P.kw)
    (hxip : 0 < P.xip) (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp)
    (h : ∀ u wn : ℕ → Ω → ℝ, S.BddProc u → StronglyAdapted S.𝓕 u → S.BddProc wn →
      StronglyAdapted S.𝓕 wn → ∀ a b : ℝ, ∃ π πw x w mp mw ups,
        PlanSWM S P (fun _ => 0) u wn π πw x w ∧
        FOCswM S P (fun _ => a) (fun _ => b) π πw x mp mw ups) :
    StableRoots P := by
  refine (determinacy_iff_stableRoots hβ0 hβ1 hlx hlp hlw hkp hkw hxip hxiw hne).1 ?_
  intro u wn hu hwn a b
  obtain ⟨Mu, hMu⟩ := hu
  obtain ⟨Mw, hMw⟩ := hwn
  obtain ⟨hua, hub⟩ := det_adapted_bdd S (fun t => u t ()) (fun t => hMu t ())
  obtain ⟨hwa, hwb⟩ := det_adapted_bdd S (fun t => wn t ()) (fun t => hMw t ())
  obtain ⟨π, πw, x, w, mp, mw, ups, hp, hf⟩ := h _ _ hub hua hwb hwa a b
  have hpm := planSWM_mean S P 0 hp (integrable_of_adapted S hua hub)
    (integrable_of_adapted S hwa hwb)
  rw [meanPath_const, meanPath_const] at hpm
  obtain ⟨-, -, -, hπa, hπwa, hxa, -, hπb, hπwb, hxb, -⟩ := hp
  exact ⟨_, _, _, _, _, _, _, hpm, focSWM_mean S P a b (integrable_of_adapted S hπa hπb)
    (integrable_of_adapted S hπwa hπwb) (integrable_of_adapted S hxa hxb) hf⟩

/-- **Woodford (2003), (2.16)–(2.19), `κ_w ≠ κ_p` (FAILURE ON THE BOUNDARY, probability
space)**: if a root `Z₁` of `P` has a factor root `μ` on the unit circle, then on any filtered
probability space the cost-push path `u_t = Re μᵗ` (with `w^n = 0`) has no bounded adapted
plan with bounded adapted multipliers satisfying the first-order conditions almost surely (zero
predetermined values). -/
theorem foc_not_exists_boundary_meas {P : SW} (hβ0 : 0 < P.beta) (hβ1 : P.beta < 1)
    (hlx : 0 < P.lx) (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hkp : 0 < P.kp) (hkw : 0 < P.kw)
    (hxip : 0 < P.xip) (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp) {Z1 Z2 Z3 : ℂ}
    (hv1 : Z1 + Z2 + Z3 = ((-(cp2 P / P.lx) : ℝ) : ℂ))
    (hv2 : Z1 * Z2 + Z1 * Z3 + Z2 * Z3 = ((cp1 P / P.lx : ℝ) : ℂ))
    (hv3 : Z1 * Z2 * Z3 = ((-(cp0 P / P.lx) : ℝ) : ℂ)) {μ : ℂ}
    (hr : (P.beta : ℂ) * μ ^ 2 - (1 + P.beta - Z1) * μ + 1 = 0) (hμ1 : ‖μ‖ = 1) :
    ¬ ∃ π πw x w mp mw ups, PlanSWM S P (fun _ => 0) (fun t _ => (μ ^ t).re) (fun _ _ => 0)
      π πw x w ∧ FOCswM S P (fun _ => 0) (fun _ => 0) π πw x mp mw ups := by
  rintro ⟨π, πw, x, w, mp, mw, ups, hp, hf⟩
  apply foc_not_exists_boundary hβ0 hβ1 hlx hlp hlw hkp hkw hxip hxiw hne hv1 hv2 hv3 hr hμ1
  obtain ⟨hua, hub⟩ := det_adapted_bdd S (fun t => (μ ^ t).re) (M := 1) fun t =>
    (Complex.abs_re_le_norm _).trans (by rw [norm_pow, hμ1, one_pow])
  obtain ⟨hwa, hwb⟩ := det_adapted_bdd S (fun _ => (0 : ℝ)) (M := 0) fun _ => by simp
  have hpm := planSWM_mean S P 0 hp (integrable_of_adapted S hua hub)
    (integrable_of_adapted S hwa hwb)
  rw [meanPath_const S (fun t _ => (μ ^ t).re), meanPath_const S (fun _ _ => (0 : ℝ))] at hpm
  obtain ⟨-, -, -, hπa, hπwa, hxa, -, hπb, hπwb, hxb, -⟩ := hp
  exact ⟨_, _, _, _, _, _, _, hpm, focSWM_mean S P 0 0 (integrable_of_adapted S hπa hπb)
    (integrable_of_adapted S hπwa hπwb) (integrable_of_adapted S hxa hxb) hf⟩

/-- Woodford (2003), §2.2, `κ_w ≠ κ_p` (probability space): outside the root condition some
bounded adapted disturbance and constant initial multipliers have no bounded adapted
almost-sure plan satisfying the first-order conditions. -/
theorem not_exists_meas_of_not_stableRoots {P : SW} (hβ0 : 0 < P.beta) (hβ1 : P.beta < 1)
    (hlx : 0 < P.lx) (hlp : 0 < P.lp) (hlw : 0 < P.lw) (hkp : 0 < P.kp) (hkw : 0 < P.kw)
    (hxip : 0 < P.xip) (hxiw : 0 < P.xiw) (hne : P.kw ≠ P.kp) (hR : ¬ StableRoots P) :
    ∃ u wn : ℕ → Ω → ℝ, S.BddProc u ∧ StronglyAdapted S.𝓕 u ∧ S.BddProc wn ∧
      StronglyAdapted S.𝓕 wn ∧ ∃ a b : ℝ, ¬ ∃ π πw x w mp mw ups,
        PlanSWM S P (fun _ => 0) u wn π πw x w ∧
        FOCswM S P (fun _ => a) (fun _ => b) π πw x mp mw ups := by
  by_contra hc
  push Not at hc
  exact hR (stableRoots_of_exists_meas S hβ0 hβ1 hlx hlp hlw hkp hkw hxip hxiw hne
    fun u wn hu hua hwn hwna a b => hc u wn hu hua hwn hwna a b)

end Woodford.OptimalPolicyRules.TidyR5bStickyMeasure
