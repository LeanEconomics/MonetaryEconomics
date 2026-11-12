/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.TidyR7StochCTBrownian

/-!
# Existence and uniqueness of the stochastic continuous-time equilibrium

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.7 and §5.7.1,
pp. 162–167, (5.85)–(5.96).

"As in discrete time, solving the model involves solving the `dδ_t` expectational errors in
terms of the `dε_t` shocks" (p. 164), and with no price-level jumps "`v₀` is predetermined" and
the valuation equation picks the unique path (p. 166). Here the shocks are Brownian,
`dε_m = σ_i dW`, `dε_s = σ_s dW`, and an equilibrium (`StochCTEq`) is any triple of processes
`(x, π, v)` with continuous paths, measurable and adapted values, `E|·|` growing at most linearly
(the stochastic counterpart of the bounded paths and transversality condition of
`CTSimple.IsCTEquilibrium`) that satisfies the book's `E_t dx = σ(i − π)dt`,
`E_t dπ = (ρπ − κx)dt` (with arbitrary expectational errors), the debt equation
`dv = (rv + i − π − s̃)dt` with no error term, and `v₀ = 0`.

## Main results

* **`feedback_rule`** (the stochastic (5.96), with debt as the state): in every equilibrium,
  for every `t ≥ 0`, a.s. `π_t = i_t + (r + λ₂)(v_t − s̃_t/r)` and
  `x_t = (λ₁(π_t − i_t) + ρ i_t)/κ`. Proved by taking `∫_A` over `A ∈ 𝓕_t` (Fubini), which turns
  the `E_t d`-equations into the deterministic system of `CTSimple` from date `t`, killing the
  unstable root `λ₁` and the debt root `r` by linear growth (`CTSimple.tvc_iff_forward`).
* **`stochCTEq_exists`**: the explicit solution `(xProc, piProc, vProc)` of
  `TidyR7StochCTBrownian` is an equilibrium.
* **`stochCTEq_unique`**: every equilibrium equals it: for every `t ≥ 0`, a.s. `x_t`, `π_t`,
  `v_t` are the explicit Wiener-integral solution (and so, by `responses_ito`, the book's
  responses integrated against `dW`).
* Non-vacuity: `bmPath_stochCTEq` (on the constructed motion `bmPath`).
-/

namespace Cochrane.StickyPriceFiscal.TidyR7StochCTUnique

open Real MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.StickyPriceFiscal.TidyR7StieltjesSums Cochrane.StickyPriceFiscal.TidyR7BrownianTools
open Cochrane.StickyPriceFiscal.TidyR7BrownianQV Cochrane.StickyPriceFiscal.TidyR7ItoL2
open Cochrane.StickyPriceFiscal.TidyR7ItoSums Cochrane.StickyPriceFiscal.TidyR7ItoIntegral
open Cochrane.StickyPriceFiscal.TidyR7ItoBridge Cochrane.StickyPriceFiscal.TidyR7BrownianExist
open Cochrane.StickyPriceFiscal.TidyR7StochCTPath Cochrane.StickyPriceFiscal.CTSimple
open Cochrane.StickyPriceFiscal.TidyR7StochCTBrownian
open Cochrane.StickyPriceFiscal.TidyR7BrownianSchauder
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ}

/-! ### Regular processes and Fubini -/

/-- Cochrane (2023), §5.7, p. 164: a **regular process** on `[0, ∞)`: continuous paths,
measurable values, integrable at every `t ≥ 0`, with `E|F_t| ≤ C(1 + t)`. -/
def RegProc (P : Measure Ω) (F : ℝ → Ω → ℝ) : Prop :=
  (∀ ω, Continuous fun t => F t ω) ∧ (∀ t, Measurable (F t)) ∧
    (∀ t, 0 ≤ t → Integrable (F t) P) ∧ ∃ C, ∀ t, 0 ≤ t → ∫ ω, |F t ω| ∂P ≤ C * (1 + t)

/-- Cochrane (2023), §5.7, p. 164: the growth constant of a regular process is nonnegative. -/
theorem RegProc.exists_nonneg {F : ℝ → Ω → ℝ} (hF : RegProc P F) :
    ∃ C, 0 ≤ C ∧ ∀ t, 0 ≤ t → ∫ ω, |F t ω| ∂P ≤ C * (1 + t) := by
  obtain ⟨C, hC⟩ := hF.2.2.2
  have h0 := hC 0 le_rfl
  have : 0 ≤ ∫ ω, |F 0 ω| ∂P := integral_nonneg fun _ => abs_nonneg _
  exact ⟨C, by linarith, hC⟩

/-- Cochrane (2023), §5.7, p. 164: linear combinations of regular processes are regular. -/
theorem RegProc.lin {F G : ℝ → Ω → ℝ} (hF : RegProc P F) (hG : RegProc P G) (a b : ℝ) :
    RegProc P fun t ω => a * F t ω + b * G t ω := by
  obtain ⟨C, hC0, hC⟩ := hF.exists_nonneg
  obtain ⟨D, hD0, hD⟩ := hG.exists_nonneg
  refine ⟨fun ω => ((hF.1 ω).const_mul a).add ((hG.1 ω).const_mul b),
    fun t => ((hF.2.1 t).const_mul a).add ((hG.2.1 t).const_mul b),
    fun t ht => ((hF.2.2.1 t ht).const_mul a).add ((hG.2.2.1 t ht).const_mul b),
    |a| * C + |b| * D, fun t ht => ?_⟩
  have i1 := (hF.2.2.1 t ht).abs
  have i2 := (hG.2.2.1 t ht).abs
  calc ∫ ω, |a * F t ω + b * G t ω| ∂P
      ≤ ∫ ω, (|a| * |F t ω| + |b| * |G t ω|) ∂P :=
        integral_mono ((((hF.2.2.1 t ht).const_mul a).add
          ((hG.2.2.1 t ht).const_mul b)).abs) ((i1.const_mul _).add (i2.const_mul _))
          fun ω => by
            have := abs_add_le (a * F t ω) (b * G t ω)
            rw [abs_mul, abs_mul] at this
            exact this
    _ = |a| * ∫ ω, |F t ω| ∂P + |b| * ∫ ω, |G t ω| ∂P := by
        rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ |a| * (C * (1 + t)) + |b| * (D * (1 + t)) :=
        add_le_add (mul_le_mul_of_nonneg_left (hC t ht) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (hD t ht) (abs_nonneg _))
    _ = (|a| * C + |b| * D) * (1 + t) := by ring

/-- Cochrane (2023), §5.7, p. 164: a process with continuous paths and measurable values is
jointly measurable in `(t, ω)`.
Restates Mathlib `measurable_uncurry_of_continuous_of_measurable`. -/
theorem measurable_uncurry_proc {F : ℝ → Ω → ℝ} (hc : ∀ ω, Continuous fun t => F t ω)
    (hm : ∀ t, Measurable (F t)) : Measurable (Function.uncurry F) :=
  measurable_uncurry_of_continuous_of_measurable hc hm

/-- Cochrane (2023), §5.7, p. 164: the time integral `ω ↦ ∫_a^b F_u(ω) du` of such a process is
measurable. -/
theorem measurable_intervalIntegral_proc {F : ℝ → Ω → ℝ} (hc : ∀ ω, Continuous fun t => F t ω)
    (hm : ∀ t, Measurable (F t)) (a b : ℝ) : Measurable fun ω => ∫ u in a..b, F u ω := by
  have h := (measurable_uncurry_proc hc hm).stronglyMeasurable
  have h1 := (h.integral_prod_left (μ := volume.restrict (Set.Ioc a b))).measurable
  have h2 := (h.integral_prod_left (μ := volume.restrict (Set.Ioc b a))).measurable
  exact h1.sub h2

/-- Cochrane (2023), §5.7, p. 164: `u ↦ ∫_A F_u dP` is measurable. -/
theorem measurable_setIntegral_proc {F : ℝ → Ω → ℝ} (hc : ∀ ω, Continuous fun t => F t ω)
    (hm : ∀ t, Measurable (F t)) [IsFiniteMeasure P] (A : Set Ω) :
    Measurable fun u => ∫ ω in A, F u ω ∂P :=
  ((measurable_uncurry_proc hc hm).stronglyMeasurable.integral_prod_right
    (ν := P.restrict A)).measurable

/-- Cochrane (2023), §5.7, p. 164: for a regular process and `u ≥ 0`,
`|∫_A F_u dP| ≤ C(1 + u)`. -/
theorem abs_setIntegral_le {F : ℝ → Ω → ℝ} (hF : RegProc P F) {C : ℝ}
    (hC : ∀ t, 0 ≤ t → ∫ ω, |F t ω| ∂P ≤ C * (1 + t)) (A : Set Ω) {u : ℝ} (hu : 0 ≤ u) :
    |∫ ω in A, F u ω ∂P| ≤ C * (1 + u) := by
  refine (abs_integral_le_integral_abs).trans ((setIntegral_le_integral (hF.2.2.1 u hu).abs
    (Eventually.of_forall fun _ => abs_nonneg _)).trans (hC u hu))

/-- **Cochrane (2023), §5.7, p. 163 (Fubini for the book's time integrals).** For a regular
process, `0 ≤ a ≤ b` and measurable `A`: `ω ↦ ∫_a^b F_u du` is integrable and
`∫_A ∫_a^b F_u du dP = ∫_a^b ∫_A F_u dP du`.
Fubini (Mathlib `integral_prod`) for regular processes. -/
theorem fubini_proc [IsProbabilityMeasure P] {F : ℝ → Ω → ℝ} (hF : RegProc P F) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) {A : Set Ω} :
    Integrable (fun ω => ∫ u in a..b, F u ω) P ∧
      ∫ ω in A, (∫ u in a..b, F u ω) ∂P = ∫ u in a..b, ∫ ω in A, F u ω ∂P := by
  obtain ⟨C, hC0, hC⟩ := hF.exists_nonneg
  have hmeas := measurable_uncurry_proc hF.1 hF.2.1
  have hint : ∀ B : Set Ω, Integrable (Function.uncurry F)
      ((volume.restrict (Set.uIoc a b)).prod (P.restrict B)) := by
    intro B
    rw [Set.uIoc_of_le hab]
    refine (integrable_prod_iff hmeas.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_
      exact (hF.2.2.1 u (ha.trans hu.1.le)).restrict
    · refine IntegrableOn.of_bound measure_Ioc_lt_top
        ((hmeas.norm.stronglyMeasurable.integral_prod_right
          (ν := P.restrict B)).aestronglyMeasurable)
        (C * (1 + b)) (ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_)
      have hu0 : 0 ≤ u := ha.trans hu.1.le
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      simp only [Function.uncurry_apply_pair, Real.norm_eq_abs]
      refine (setIntegral_le_integral (hF.2.2.1 u hu0).abs
        (Eventually.of_forall fun _ => abs_nonneg _)).trans ((hC u hu0).trans ?_)
      exact mul_le_mul_of_nonneg_left (by linarith [hu.2]) hC0
  refine ⟨?_, ?_⟩
  · have h := (hint Set.univ).integral_prod_right
    rw [Measure.restrict_univ] at h
    refine h.congr (Eventually.of_forall fun ω => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab]
  · exact (intervalIntegral_integral_swap (hint A)).symm

/-! ### Two deterministic lemmas -/

/-- Cochrane (2023), §5.7, p. 164 (tool): a measurable `f` with `|f u| ≤ K(1 + u)` on
`[t, ∞)` (`0 ≤ t`, `0 ≤ K`) gives an everywhere locally integrable `u ↦ f(max u t)`. -/
theorem intervalIntegrable_clamp {f : ℝ → ℝ} (hm : Measurable f) {t K : ℝ} (ht : 0 ≤ t)
    (hK : 0 ≤ K) (hb : ∀ u, t ≤ u → |f u| ≤ K * (1 + u)) (a b : ℝ) :
    IntervalIntegrable (fun u => f (max u t)) volume a b := by
  refine (intervalIntegrable_const (c := K * (1 + |a| + |b| + t))).mono_fun
    (hm.comp (measurable_id.max measurable_const)).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_uIoc fun u hu => ?_)
  have hu' : |u| ≤ |a| + |b| := by
    rcases le_total a b with h | h
    · rw [Set.uIoc_of_le h] at hu
      rw [abs_le]
      constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith [hu.1, hu.2]
    · rw [Set.uIoc_of_ge h] at hu
      rw [abs_le]
      constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith [hu.1, hu.2]
  have hmax : max u t ≤ |a| + |b| + t := by
    rcases le_total u t with h | h
    · rw [max_eq_right h]; linarith [abs_nonneg a, abs_nonneg b]
    · rw [max_eq_left h]; linarith [le_abs_self u]
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ K * (1 + |a| + |b| + t))]
  calc |f (max u t)| ≤ K * (1 + max u t) := hb _ (le_max_right _ _)
    _ ≤ K * (1 + |a| + |b| + t) := mul_le_mul_of_nonneg_left (by linarith) hK

/-- Cochrane (2023), §5.7.1, p. 165 (tool): `e^{−aT}K(1 + T) → 0` for `a > 0`.
`TidyR7StochCTBrownian.tendsto_exp_mul_affine` at `t = 0`. -/
theorem tendsto_exp_neg_mul_lin {a : ℝ} (ha : 0 < a) (K : ℝ) :
    Tendsto (fun T => exp (-(a * T)) * (K * (1 + T))) atTop (𝓝 0) := by
  have h1 := tendsto_exp_mul_affine ha 0 K
  have h2 : Tendsto (fun T => exp (-(a * T))) atTop (𝓝 0) :=
    tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop ha)
  have h3 := h1.add (h2.const_mul (K - 1))
  simp only [mul_zero, add_zero] at h3
  refine h3.congr fun T => ?_
  simp only [sub_zero]
  ring

/-- **Cochrane (2023), A1 §1.12, p. 580 ("we solve forward"): the unstable root.** If `f` is
measurable, `|f u| ≤ K(1 + u)` on `[t, ∞)` and `f τ − f t = a∫_t^τ f` for all `τ ≥ t`, with
`a > 0`, then `f t = 0`.
Built on `CTSimple.tvc_iff_forward`. -/
theorem unstable_zero {f : ℝ → ℝ} (hm : Measurable f) {t K a : ℝ} (ht : 0 ≤ t) (hK : 0 ≤ K)
    (ha : 0 < a) (hb : ∀ u, t ≤ u → |f u| ≤ K * (1 + u))
    (heq : ∀ τ, t ≤ τ → f τ - f t = a * ∫ u in t..τ, f u) : f t = 0 := by
  set g : ℝ → ℝ := fun u => f (max u t) with hg
  have hgi := intervalIntegrable_clamp hm ht hK hb
  have hFc : Continuous fun τ => ∫ u in t..τ, g u := intervalIntegral.continuous_primitive hgi t
  set v : ℝ → ℝ := fun τ => f t + a * ∫ u in t..τ, g u with hv
  have hvc : Continuous v := continuous_const.add (hFc.const_mul a)
  have hgf : ∀ τ, t ≤ τ → ∫ u in t..τ, g u = ∫ u in t..τ, f u := fun τ hτ =>
    intervalIntegral.integral_congr fun u hu => by
      rw [Set.uIcc_of_le hτ] at hu
      simp only [hg, max_eq_left hu.1]
  have hvf : ∀ τ, t ≤ τ → v τ = f τ := fun τ hτ => by
    simp only [hv, hgf τ hτ]
    linarith [heq τ hτ]
  have hgv : ∀ τ, t ≤ τ → g τ = v τ := fun τ hτ => by
    rw [hvf τ hτ]
    simp only [hg, max_eq_left hτ]
  have hd : ∀ τ, t < τ → HasDerivAt v (a * v τ - 0) τ := by
    intro τ hτ
    have hev : g =ᶠ[𝓝 τ] v := (eventually_gt_nhds hτ).mono fun u hu => hgv u hu.le
    have hca : ContinuousAt g τ := (hvc.continuousAt).congr hev.symm
    have hD := intervalIntegral.integral_hasDerivAt_right (hgi t τ)
      ((hm.comp (measurable_id.max measurable_const)).stronglyMeasurable.stronglyMeasurableAtFilter)
      hca
    refine ((hD.const_mul a).const_add (f t)).congr_deriv ?_
    have e := hgv τ hτ.le
    simp only [hg] at e
    rw [e, sub_zero]
  have hint : IntegrableOn (fun τ => exp (-(a * τ)) * (0 : ℝ)) (Set.Ioi t) := by
    simp only [mul_zero]
    exact integrableOn_zero
  have htvc : Tendsto (fun T => exp (-(a * T)) * v T) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_exp_neg_mul_lin ha K)
    filter_upwards [eventually_ge_atTop t] with T hT
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _), hvf T hT]
    exact mul_le_mul_of_nonneg_left (hb T hT) (exp_pos _).le
  have h := (tvc_iff_forward (f := fun _ => (0 : ℝ)) hvc.continuousOn hd hint).1 htvc
  simp only [mul_zero, integral_zero] at h
  rw [← hvf t le_rfl, h]

/-- **Cochrane (2023), A1 §1.12, p. 580 ("we solve backward"): a stable root from a zero
start.** If `f` is measurable, `|f u| ≤ K(1 + u)` on `[0, ∞)` and `f τ = c∫_0^τ f` for all
`τ ≥ 0`, then `f τ = 0` for all `τ ≥ 0`.
Built on `CTSimple.ode_backward` and `CTSimple.decay_unique`. -/
theorem stable_zero {f : ℝ → ℝ} (hm : Measurable f) {K c : ℝ} (hK : 0 ≤ K)
    (hb : ∀ u, 0 ≤ u → |f u| ≤ K * (1 + u)) (heq : ∀ τ, 0 ≤ τ → f τ = c * ∫ u in (0 : ℝ)..τ, f u)
    {τ : ℝ} (hτ : 0 ≤ τ) : f τ = 0 := by
  set g : ℝ → ℝ := fun u => f (max u 0) with hg
  have hgi := intervalIntegrable_clamp hm le_rfl hK hb
  have hFc : Continuous fun τ => ∫ u in (0 : ℝ)..τ, g u :=
    intervalIntegral.continuous_primitive hgi 0
  set v : ℝ → ℝ := fun τ => c * ∫ u in (0 : ℝ)..τ, g u with hv
  have hvc : Continuous v := hFc.const_mul c
  have hgf : ∀ τ, 0 ≤ τ → ∫ u in (0 : ℝ)..τ, g u = ∫ u in (0 : ℝ)..τ, f u := fun τ hτ =>
    intervalIntegral.integral_congr fun u hu => by
      rw [Set.uIcc_of_le hτ] at hu
      simp only [hg, max_eq_left hu.1]
  have hvf : ∀ τ, 0 ≤ τ → v τ = f τ := fun τ hτ => by
    simp only [hv, hgf τ hτ]
    exact (heq τ hτ).symm
  have hgv : ∀ τ, 0 ≤ τ → g τ = v τ := fun τ hτ => by
    rw [hvf τ hτ]
    simp only [hg, max_eq_left hτ]
  have hd : ∀ τ, 0 < τ → HasDerivAt v (-(-c) * v τ + 0) τ := by
    intro τ hτ
    have hev : g =ᶠ[𝓝 τ] v := (eventually_gt_nhds hτ).mono fun u hu => hgv u hu.le
    have hca : ContinuousAt g τ := (hvc.continuousAt).congr hev.symm
    have hD := intervalIntegral.integral_hasDerivAt_right (hgi 0 τ)
      ((hm.comp (measurable_id.max measurable_const)).stronglyMeasurable.stronglyMeasurableAtFilter)
      hca
    refine (hD.const_mul c).congr_deriv ?_
    have e := hgv τ hτ.le
    simp only [hg] at e
    rw [e]
    ring
  have h := (ode_backward (b := -c) (z := fun _ => (0 : ℝ)) continuous_const).1
    ⟨hvc.continuousOn, hd⟩ τ hτ
  have h0 : v 0 = 0 := by simp [hv]
  have hb0 : bwdInt (-c) (fun _ => (0 : ℝ)) τ = 0 := by simp [bwdInt]
  rw [h0, hb0, mul_zero, add_zero] at h
  rw [← hvf τ hτ, h]

/-! ### The equilibrium -/

variable (P 𝓕 W) (r σ κ ρ σi σs : ℝ) (x infl v : ℝ → Ω → ℝ)

/-- **Cochrane (2023), (5.85)–(5.90), pp. 162–166: a stochastic equilibrium** with Brownian
shocks `dε_m = σ_i dW`, `dε_s = σ_s dW`: regular adapted processes `x, π, v` satisfying
`E_t dx = σ(i − π)dt`, `E_t dπ = (ρπ − κx)dt` (with ANY expectational errors), the debt
equation `dv = (rv + i − π − s̃)dt` with no error term on every path, and `v₀ = 0` (debt is
predetermined: no price-level jump at the news date). -/
structure StochCTEq where
  regX : RegProc P x
  regPi : RegProc P infl
  regV : RegProc P v
  adaptX : ∀ t, 0 ≤ t → AEStronglyMeasurable[𝓕 t] (x t) P
  adaptPi : ∀ t, 0 ≤ t → AEStronglyMeasurable[𝓕 t] (infl t) P
  adaptV : ∀ t, 0 ≤ t → AEStronglyMeasurable[𝓕 t] (v t) P
  isCurve : ∀ t T, 0 ≤ t → t ≤ T → P[fun ω => x T ω - x t ω | 𝓕 t]
    =ᵐ[P] P[fun ω => ∫ u in t..T, σ * (iProc σi W u ω - infl u ω) | 𝓕 t]
  phillips : ∀ t T, 0 ≤ t → t ≤ T → P[fun ω => infl T ω - infl t ω | 𝓕 t]
    =ᵐ[P] P[fun ω => ∫ u in t..T, (ρ * infl u ω - κ * x u ω) | 𝓕 t]
  debt : ∀ ω t T, v T ω - v t ω
    = ∫ u in t..T, (r * v u ω + iProc σi W u ω - infl u ω - sProc σs W u ω)
  v0 : ∀ ω, v 0 ω = 0

variable {P 𝓕 W r σ κ ρ σi σs x infl v}

/-! ### The explicit solution is regular -/

/-- Cochrane (2023), §5.7, p. 164: `c W + d Y` has measurable values. -/
theorem measurable_kerProc (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω)
    (c d η t : ℝ) : Measurable (kerProc W c d η t) := by
  have hbm : ∀ u, Measurable (bmReal W u) := fun u => hW _
  have hI := measurable_intervalIntegral_proc (F := fun u ω => exp (η * u) * bmReal W u ω)
    (fun ω => by have := continuous_bmReal (hcont ω); fun_prop)
    (fun u => (hbm u).const_mul _) 0 t
  have : kerProc W c d η t = fun ω => c * bmReal W t ω
      + d * (bmReal W t ω - η * (exp (-η * t) * ∫ u in (0 : ℝ)..t, exp (η * u) * bmReal W u ω)) :=
    rfl
  rw [this]
  exact ((hbm t).const_mul c).add (((hbm t).sub
    (((hI.const_mul (exp (-η * t)))).const_mul η)).const_mul d)

/-- Cochrane (2023), §5.7, p. 164: `c W + d Y` is a regular process. -/
theorem regProc_kerProc (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {η : ℝ} (hη : 0 ≤ η) (c d : ℝ) : RegProc P (kerProc W c d η) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨fun ω => ?_, measurable_kerProc hW hcont c d η,
    fun t ht => integrable_kerProc hB hW h𝓕 hcont hW0 c d η ht,
    max 1 ((|c| + |d|) ^ 2), fun t ht => ?_⟩
  · have hw := continuous_bmReal (hcont ω)
    have := continuous_ouNoise η hw
    unfold kerProc
    fun_prop
  have hm := memLp_kerProc hB hW h𝓕 hcont hW0 c d η ht (𝓕 := 𝓕)
  have hsq := hm.integrable_sq
  have h1 : ∫ ω, |kerProc W c d η t ω| ∂P ≤ ∫ ω, (1 + kerProc W c d η t ω ^ 2) ∂P :=
    integral_mono (hm.integrable one_le_two).abs ((integrable_const 1).add hsq) fun ω => by
      have := abs_nonneg (kerProc W c d η t ω)
      have := sq_abs (kerProc W c d η t ω)
      nlinarith
  rw [integral_add (integrable_const 1) hsq, integral_kerProc_sq hB hW h𝓕 hcont hW0 c d η ht]
    at h1
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h1
  have h2 : ∫ u in (0 : ℝ)..t, kerFn c d η (t - u) ^ 2 ≤ ∫ u in (0 : ℝ)..t, (|c| + |d|) ^ 2 := by
    refine intervalIntegral.integral_mono_on ht
      (((continuous_kerFn c d η t).pow 2).intervalIntegrable 0 t) intervalIntegrable_const
      fun u hu => ?_
    have he : exp (-(η * (t - u))) ≤ 1 := exp_le_one_iff.2 (by nlinarith [hu.2])
    have he0 := exp_pos (-(η * (t - u)))
    have hk : |kerFn c d η (t - u)| ≤ |c| + |d| := by
      unfold kerFn
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_mul, abs_of_pos he0]
      exact mul_le_of_le_one_right (abs_nonneg _) he
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hk 2
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h2
  have hM1 := le_max_left 1 ((|c| + |d|) ^ 2)
  have hM2 := le_max_right 1 ((|c| + |d|) ^ 2)
  nlinarith

/-- Cochrane (2023), (5.89)–(5.90), pp. 162–163: the shocks `i = σ_iW`, `s̃ = σ_sW` as kernels
`(c, 0)`. -/
theorem iProc_eq_ker (σi : ℝ) (η : ℝ) : iProc σi W = kerProc W σi 0 η := by
  funext t ω
  simp [iProc, iPath, kerProc]

/-! ### The feedback rule -/

/-- Cochrane (2023), §5.7, p. 164 (`E_t dW = 0` in integrated form): for `0 ≤ t ≤ u` and
`A ∈ 𝓕_t`, `∫_A W_u = ∫_A W_t`.
The set-integral form of `TidyR7BrownianTools.martingale_bm`. -/
theorem setIntegral_bm_eq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {t u : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) {A : Set Ω}
    (hA : MeasurableSet[𝓕 t] A) : ∫ ω in A, bmReal W u ω ∂P = ∫ ω in A, bmReal W t ω ∂P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h := setIntegral_condExp (𝓕.le t) (integrable_incr hB t u) hA
  rw [setIntegral_congr_ae (𝓕.le t A hA) ((condExp_incr hB hW h𝓕 ht htu).mono
    fun ω hω _ => hω)] at h
  simp only [Pi.zero_apply, integral_zero] at h
  have hi : ∀ τ, Integrable (bmReal W τ) P := fun τ => hB.integrable_eval _
  have : ∫ ω in A, incr W t u ω ∂P
      = ∫ ω in A, bmReal W u ω ∂P - ∫ ω in A, bmReal W t ω ∂P :=
    integral_sub (hi u).integrableOn (hi t).integrableOn
  linarith

/-- Cochrane (2023), §5.7, p. 163: the `E_t d`-equation integrated over `A ∈ 𝓕_t`:
if `E_t[X_T − X_t] = E_t[∫_t^T G]` then `∫_A X_T − ∫_A X_t = ∫_t^T ∫_A G_u du`. -/
theorem setIntegral_of_condExp [IsProbabilityMeasure P] {X G : ℝ → Ω → ℝ} (hX : RegProc P X)
    (hG : RegProc P G) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) {A : Set Ω}
    (hA : MeasurableSet[𝓕 t] A)
    (h : P[fun ω => X T ω - X t ω | 𝓕 t] =ᵐ[P] P[fun ω => ∫ u in t..T, G u ω | 𝓕 t]) :
    ∫ ω in A, X T ω ∂P - ∫ ω in A, X t ω ∂P = ∫ u in t..T, ∫ ω in A, G u ω ∂P := by
  have hXi : Integrable (fun ω => X T ω - X t ω) P :=
    (hX.2.2.1 T (ht.trans htT)).sub (hX.2.2.1 t ht)
  obtain ⟨hDi, hfub⟩ := fubini_proc (A := A) hG ht htT
  have e1 := setIntegral_condExp (𝓕.le t) hXi hA
  have e2 := setIntegral_condExp (𝓕.le t) hDi hA
  rw [setIntegral_congr_ae (𝓕.le t A hA) (h.mono fun ω hω _ => hω), e2] at e1
  rw [← hfub, e1, integral_sub (hX.2.2.1 T (ht.trans htT)).integrableOn
    (hX.2.2.1 t ht).integrableOn]

/-- Cochrane (2023), §5.7, p. 164: a path identity integrated over any measurable `A`:
if `X_T − X_t = ∫_t^T G` on every path then `∫_A X_T − ∫_A X_t = ∫_t^T ∫_A G_u du`. -/
theorem setIntegral_of_path [IsProbabilityMeasure P] {X G : ℝ → Ω → ℝ} (hX : RegProc P X)
    (hG : RegProc P G) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) {A : Set Ω}
    (h : ∀ ω, X T ω - X t ω = ∫ u in t..T, G u ω) :
    ∫ ω in A, X T ω ∂P - ∫ ω in A, X t ω ∂P = ∫ u in t..T, ∫ ω in A, G u ω ∂P := by
  rw [← (fubini_proc (A := A) hG ht htT).2, ← integral_sub (hX.2.2.1 T (ht.trans htT)).integrableOn
    (hX.2.2.1 t ht).integrableOn]
  congr 1
  funext ω
  exact h ω

/-- Cochrane (2023), §5.7, p. 164: regularity transports along equal processes. -/
theorem RegProc.congr {F G : ℝ → Ω → ℝ} (hF : RegProc P F) (h : F = G) : RegProc P G := h ▸ hF

/-- Cochrane (2023), §5.7, p. 164: `∫_A` of a linear combination, for `u ≥ 0`. -/
theorem setIntegral_lin {F G : ℝ → Ω → ℝ} (hF : RegProc P F) (hG : RegProc P G) (a b : ℝ)
    (A : Set Ω) {u : ℝ} (hu : 0 ≤ u) :
    ∫ ω in A, (a * F u ω + b * G u ω) ∂P = a * ∫ ω in A, F u ω ∂P + b * ∫ ω in A, G u ω ∂P := by
  rw [integral_add ((hF.2.2.1 u hu).integrableOn.const_mul a)
    ((hG.2.2.1 u hu).integrableOn.const_mul b), integral_const_mul, integral_const_mul]

/-- Cochrane (2023), §5.7, p. 164: `u ↦ ∫_A F_u` is interval integrable on `[a, b] ⊆ [0, ∞)`. -/
theorem intervalIntegrable_setIntegral [IsFiniteMeasure P] {F : ℝ → Ω → ℝ} (hF : RegProc P F)
    (A : Set Ω) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u => ∫ ω in A, F u ω ∂P) volume a b := by
  obtain ⟨C, hC0, hC⟩ := hF.exists_nonneg
  refine (intervalIntegrable_const (c := C * (1 + b))).mono_fun
    (measurable_setIntegral_proc hF.1 hF.2.1 A).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_uIoc fun u hu => ?_)
  rw [Set.uIoc_of_le hab] at hu
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg hC0 (by linarith) : (0 : ℝ) ≤ C * (1 + b))]
  exact (abs_setIntegral_le hF hC A (ha.trans hu.1.le)).trans
    (mul_le_mul_of_nonneg_left (by linarith [hu.2]) hC0)

/-- Cochrane (2023), (5.89), p. 162: the interest rate `σ_iW` is regular. -/
theorem regProc_iProc (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (σi : ℝ) : RegProc P (iProc σi W) := by
  rw [iProc_eq_ker σi 0]
  exact regProc_kerProc (𝓕 := 𝓕) hB hW h𝓕 hcont hW0 le_rfl σi 0

/-- Cochrane (2023), (5.90), p. 163: the surplus `σ_sW` is regular. -/
theorem regProc_sProc (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (σs : ℝ) : RegProc P (sProc σs W) := by
  have : sProc σs W = iProc σs W := rfl
  rw [this]
  exact regProc_iProc hB hW h𝓕 hcont hW0 σs

/-- Cochrane (2023), §5.7, p. 164: `∫_A σ_i W_u = ∫_A σ_i W_t` for `0 ≤ t ≤ u`, `A ∈ 𝓕_t`. -/
theorem setIntegral_iProc_eq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (c : ℝ) {t u : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) {A : Set Ω}
    (hA : MeasurableSet[𝓕 t] A) : ∫ ω in A, iProc c W u ω ∂P = ∫ ω in A, iProc c W t ω ∂P := by
  simp only [iProc, iPath]
  rw [integral_const_mul, integral_const_mul, setIntegral_bm_eq hB hW h𝓕 ht htu hA]

/-- **Cochrane (2023), A1 §1.12, p. 580 (the unstable root `λ₁` is solved forward), under
uncertainty.** In every equilibrium, for `s ≥ 0` and `A ∈ 𝓕_s`,
`∫_A π_s − (κ/λ₁)∫_A x_s − (λ₂/λ₁)∫_A i_s = 0`. -/
theorem unstable_combination_zero (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hκ : 0 < κ) (hσ : 0 < σ)
    (h : StochCTEq P W 𝓕 r σ κ ρ σi σs x infl v) {s : ℝ} (hs : 0 ≤ s) {A : Set Ω}
    (hA : MeasurableSet[𝓕 s] A) :
    ∫ ω in A, infl s ω ∂P - κ / lam1 ρ κ σ * ∫ ω in A, x s ω ∂P
      - lam2 ρ κ σ / lam1 ρ κ σ * ∫ ω in A, iProc σi W s ω ∂P = 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h1 := lam1_pos (ρ := ρ) hκ hσ
  have hm := lam_mul (ρ := ρ) hκ hσ
  have hsub := lam_sub ρ κ σ
  have hI := regProc_iProc hB hW h𝓕 hcont hW0 σi
  set SP := fun u => ∫ ω in A, infl u ω ∂P
  set SX := fun u => ∫ ω in A, x u ω ∂P
  set SI := fun u => ∫ ω in A, iProc σi W u ω ∂P
  set f := fun u => SP u - κ / lam1 ρ κ σ * SX u - lam2 ρ κ σ / lam1 ρ κ σ * SI u with hf
  have hG1 : RegProc P fun u ω => ρ * infl u ω - κ * x u ω :=
    (h.regPi.lin h.regX ρ (-κ)).congr (by funext u ω; ring)
  have hG2 : RegProc P fun u ω => σ * (iProc σi W u ω - infl u ω) :=
    (hI.lin h.regPi σ (-σ)).congr (by funext u ω; ring)
  obtain ⟨Cp, hCp0, hCp⟩ := h.regPi.exists_nonneg
  obtain ⟨Cx, hCx0, hCx⟩ := h.regX.exists_nonneg
  obtain ⟨Ci, hCi0, hCi⟩ := hI.exists_nonneg
  have hmeas : Measurable f :=
    ((measurable_setIntegral_proc h.regPi.1 h.regPi.2.1 A).sub
      ((measurable_setIntegral_proc h.regX.1 h.regX.2.1 A).const_mul _)).sub
      ((measurable_setIntegral_proc hI.1 hI.2.1 A).const_mul _)
  have hbound : ∀ u, s ≤ u → |f u| ≤ (Cp + |κ / lam1 ρ κ σ| * Cx
      + |lam2 ρ κ σ / lam1 ρ κ σ| * Ci) * (1 + u) := by
    intro u hu
    have hu0 : 0 ≤ u := hs.trans hu
    have a1 := abs_setIntegral_le h.regPi hCp A hu0
    have a2 := abs_setIntegral_le h.regX hCx A hu0
    have a3 := abs_setIntegral_le hI hCi A hu0
    calc |f u| ≤ |SP u| + |κ / lam1 ρ κ σ| * |SX u| + |lam2 ρ κ σ / lam1 ρ κ σ| * |SI u| := by
          simp only [hf]
          refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans ?_) ?_)
          · rw [abs_mul]
          · rw [abs_mul]
      _ ≤ Cp * (1 + u) + |κ / lam1 ρ κ σ| * (Cx * (1 + u))
          + |lam2 ρ κ σ / lam1 ρ κ σ| * (Ci * (1 + u)) :=
          add_le_add (add_le_add a1 (mul_le_mul_of_nonneg_left a2 (abs_nonneg _)))
            (mul_le_mul_of_nonneg_left a3 (abs_nonneg _))
      _ = _ := by ring
  refine unstable_zero hmeas hs (add_nonneg (add_nonneg hCp0 (mul_nonneg (abs_nonneg _) hCx0))
    (mul_nonneg (abs_nonneg _) hCi0)) h1 hbound fun τ hτ => ?_
  have hA' : ∀ u, s ≤ u → MeasurableSet[𝓕 u] A := fun u hu => 𝓕.mono hu A hA
  have ePC := setIntegral_of_condExp h.regPi hG1 hs hτ hA (h.phillips s τ hs hτ)
  have eIS := setIntegral_of_condExp h.regX hG2 hs hτ hA (h.isCurve s τ hs hτ)
  have eI := setIntegral_iProc_eq hB hW h𝓕 σi hs hτ hA
  have i1 := intervalIntegrable_setIntegral hG1 A hs hτ
  have i2 := intervalIntegrable_setIntegral hG2 A hs hτ
  have hcomb : f τ - f s = (∫ u in s..τ, ∫ ω in A, (ρ * infl u ω - κ * x u ω) ∂P)
      - κ / lam1 ρ κ σ * ∫ u in s..τ, ∫ ω in A, σ * (iProc σi W u ω - infl u ω) ∂P := by
    simp only [hf, SP, SX, SI]
    rw [← ePC, ← eIS, eI]
    ring
  rw [hcomb, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub i1
    (i2.const_mul _), ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [Set.uIcc_of_le hτ] at hu
  have hu0 : 0 ≤ u := hs.trans hu.1
  have l1 := setIntegral_lin h.regPi h.regX ρ (-κ) A hu0
  have l2 := setIntegral_lin hI h.regPi σ (-σ) A hu0
  have e1 : (∫ ω in A, (ρ * infl u ω - κ * x u ω) ∂P) = ρ * SP u - κ * SX u := by
    rw [show (fun ω => ρ * infl u ω - κ * x u ω) = fun ω => ρ * infl u ω + -κ * x u ω by
      funext ω; ring, l1]
    ring
  have e2 : (∫ ω in A, σ * (iProc σi W u ω - infl u ω) ∂P) = σ * (SI u - SP u) := by
    rw [show (fun ω => σ * (iProc σi W u ω - infl u ω))
      = fun ω => σ * iProc σi W u ω + -σ * infl u ω by funext ω; ring, l2]
    ring
  have hl1 := h1.ne'
  have key : κ / lam1 ρ κ σ * (σ * (SI u - SP u)) = lam2 ρ κ σ * (SI u - SP u) := by
    rw [← mul_assoc, show κ / lam1 ρ κ σ * σ = lam2 ρ κ σ by
      field_simp; linear_combination (-1 : ℝ) * hm]
  have k2 : lam1 ρ κ σ * (κ / lam1 ρ κ σ * SX u) = κ * SX u := by field_simp
  have k3 : lam1 ρ κ σ * (lam2 ρ κ σ / lam1 ρ κ σ * SI u) = lam2 ρ κ σ * SI u := by field_simp
  simp only [e1, e2, hf]
  rw [key]
  linear_combination (-SP u) * hsub + k2 + k3

/-- **Cochrane (2023), (5.95)–(5.96), pp. 165–166 (the debt root `r`), under uncertainty.** In
every equilibrium (`r > 0`), for `t ≥ 0` and `A ∈ 𝓕_t`,
`∫_A v_t − (∫_A s̃_t)/r − (∫_A π_t − ∫_A i_t)/(r + λ₂) = 0`. -/
theorem debt_combination_zero (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hr : 0 < r) (hκ : 0 < κ) (hσ : 0 < σ)
    (h : StochCTEq P W 𝓕 r σ κ ρ σi σs x infl v) {t : ℝ} (ht : 0 ≤ t) {A : Set Ω}
    (hA : MeasurableSet[𝓕 t] A) :
    ∫ ω in A, v t ω ∂P - (∫ ω in A, sProc σs W t ω ∂P) / r
      - (∫ ω in A, infl t ω ∂P - ∫ ω in A, iProc σi W t ω ∂P) / (r + lam2 ρ κ σ) = 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h1 := lam1_pos (ρ := ρ) hκ hσ
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  have hsub := lam_sub ρ κ σ
  have hI := regProc_iProc hB hW h𝓕 hcont hW0 σi
  have hS := regProc_sProc hB hW h𝓕 hcont hW0 σs
  set SP := fun u => ∫ ω in A, infl u ω ∂P
  set SX := fun u => ∫ ω in A, x u ω ∂P
  set SI := fun u => ∫ ω in A, iProc σi W u ω ∂P
  set SS := fun u => ∫ ω in A, sProc σs W u ω ∂P
  set SV := fun u => ∫ ω in A, v u ω ∂P
  set g := fun u => SV u - SS u / r - (SP u - SI u) / (r + lam2 ρ κ σ) with hg
  have hG1 : RegProc P fun u ω => ρ * infl u ω - κ * x u ω :=
    (h.regPi.lin h.regX ρ (-κ)).congr (by funext u ω; ring)
  have hGv : RegProc P fun u ω => r * v u ω + iProc σi W u ω - infl u ω - sProc σs W u ω :=
    ((h.regV.lin hI r 1).lin (h.regPi.lin hS 1 1) 1 (-1)).congr (by funext u ω; ring)
  obtain ⟨Cp, hCp0, hCp⟩ := h.regPi.exists_nonneg
  obtain ⟨Cv, hCv0, hCv⟩ := h.regV.exists_nonneg
  obtain ⟨Ci, hCi0, hCi⟩ := hI.exists_nonneg
  obtain ⟨Cs, hCs0, hCs⟩ := hS.exists_nonneg
  have hmeas : Measurable g :=
    (((measurable_setIntegral_proc h.regV.1 h.regV.2.1 A).sub
      ((measurable_setIntegral_proc hS.1 hS.2.1 A).div_const _)).sub
      (((measurable_setIntegral_proc h.regPi.1 h.regPi.2.1 A).sub
        (measurable_setIntegral_proc hI.1 hI.2.1 A)).div_const _))
  have hrl : 0 < r + lam2 ρ κ σ := by linarith
  have hbound : ∀ u, t ≤ u → |g u| ≤ (Cv + Cs / r + (Cp + Ci) / (r + lam2 ρ κ σ)) * (1 + u) := by
    intro u hu
    have hu0 : 0 ≤ u := ht.trans hu
    have a1 := abs_setIntegral_le h.regV hCv A hu0
    have a2 := abs_setIntegral_le hS hCs A hu0
    have a3 := abs_setIntegral_le h.regPi hCp A hu0
    have a4 := abs_setIntegral_le hI hCi A hu0
    have b2 : |SS u / r| ≤ Cs * (1 + u) / r := by
      rw [abs_div, abs_of_pos hr]
      exact div_le_div_of_nonneg_right a2 hr.le
    have b3 : |(SP u - SI u) / (r + lam2 ρ κ σ)|
        ≤ (Cp * (1 + u) + Ci * (1 + u)) / (r + lam2 ρ κ σ) := by
      rw [abs_div, abs_of_pos hrl]
      exact div_le_div_of_nonneg_right ((abs_sub _ _).trans (add_le_add a3 a4)) hrl.le
    calc |g u| ≤ |SV u| + |SS u / r| + |(SP u - SI u) / (r + lam2 ρ κ σ)| :=
          (abs_sub _ _).trans (add_le_add ((abs_sub _ _)) le_rfl)
      _ ≤ Cv * (1 + u) + Cs * (1 + u) / r + (Cp * (1 + u) + Ci * (1 + u)) / (r + lam2 ρ κ σ) :=
          add_le_add (add_le_add a1 b2) b3
      _ = _ := by ring
  refine unstable_zero hmeas ht (add_nonneg (add_nonneg hCv0 (div_nonneg hCs0 hr.le))
    (div_nonneg (add_nonneg hCp0 hCi0) hrl.le)) hr hbound fun τ hτ => ?_
  have ePC := setIntegral_of_condExp h.regPi hG1 ht hτ hA (h.phillips t τ ht hτ)
  have eV := setIntegral_of_path (A := A) h.regV hGv ht hτ (fun ω => h.debt ω t τ)
  have eI := setIntegral_iProc_eq hB hW h𝓕 σi ht hτ hA
  have eS := setIntegral_iProc_eq hB hW h𝓕 σs ht hτ hA
  have i1 := intervalIntegrable_setIntegral hG1 A ht hτ
  have iv := intervalIntegrable_setIntegral hGv A ht hτ
  have hcomb : g τ - g t = (∫ u in t..τ, ∫ ω in A, (r * v u ω + iProc σi W u ω - infl u ω
        - sProc σs W u ω) ∂P)
      - (∫ u in t..τ, ∫ ω in A, (ρ * infl u ω - κ * x u ω) ∂P) / (r + lam2 ρ κ σ) := by
    have eS' : SS τ = SS t := eS
    have eI' : SI τ = SI t := eI
    simp only [hg, eS', eI']
    rw [← ePC, ← eV]
    simp only [SV, SP]
    ring
  rw [hcomb, ← intervalIntegral.integral_div, ← intervalIntegral.integral_sub iv
    (i1.div_const _), ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [Set.uIcc_of_le hτ] at hu
  have hu0 : 0 ≤ u := ht.trans hu.1
  have hU := unstable_combination_zero hB hW h𝓕 hcont hW0 hκ hσ h hu0 (𝓕.mono hu.1 A hA)
  have l1 := setIntegral_lin h.regPi h.regX ρ (-κ) A hu0
  have e1 : (∫ ω in A, (ρ * infl u ω - κ * x u ω) ∂P) = ρ * SP u - κ * SX u := by
    rw [show (fun ω => ρ * infl u ω - κ * x u ω) = fun ω => ρ * infl u ω + -κ * x u ω by
      funext ω; ring, l1]
    ring
  have ev : (∫ ω in A, (r * v u ω + iProc σi W u ω - infl u ω - sProc σs W u ω) ∂P)
      = r * SV u + SI u - SP u - SS u := by
    have la := setIntegral_lin h.regV hI r 1 A hu0
    have lb := setIntegral_lin h.regPi hS 1 1 A hu0
    have lc := setIntegral_lin (h.regV.lin hI r 1) (h.regPi.lin hS 1 1) 1 (-1) A hu0
    rw [show (fun ω => r * v u ω + iProc σi W u ω - infl u ω - sProc σs W u ω)
      = fun ω => 1 * (r * v u ω + 1 * iProc σi W u ω) + -1 * (1 * infl u ω + 1 * sProc σs W u ω)
      by funext ω; ring, lc, la, lb]
    ring
  have hl1 := h1.ne'
  have hr0 := hr.ne'
  have hD0 := hrl.ne'
  have hU' : SP u - κ / lam1 ρ κ σ * SX u - lam2 ρ κ σ / lam1 ρ κ σ * SI u = 0 := hU
  have k2 : lam1 ρ κ σ * (κ / lam1 ρ κ σ * SX u) = κ * SX u := by field_simp
  have k3 : lam1 ρ κ σ * (lam2 ρ κ σ / lam1 ρ κ σ * SI u) = lam2 ρ κ σ * SI u := by field_simp
  have hκX : κ * SX u = lam1 ρ κ σ * SP u - lam2 ρ κ σ * SI u := by
    linear_combination (-lam1 ρ κ σ) * hU' - k2 - k3
  have e3 : ρ * SP u - κ * SX u = -lam2 ρ κ σ * (SP u - SI u) := by
    linear_combination (-1 : ℝ) * hκX + (-SP u) * hsub
  simp only [e1, ev, hg]
  rw [e3]
  field_simp
  ring

/-- Cochrane (2023), (5.96), p. 166: `∫_A (i + D(v − s̃/r)) = ∫_A i + D(∫_A v − (∫_A s̃)/r)`. -/
theorem setIntegral_feedback {I V S : ℝ → Ω → ℝ} (hI : RegProc P I) (hV : RegProc P V)
    (hS : RegProc P S) (D r : ℝ) (A : Set Ω) {u : ℝ} (hu : 0 ≤ u) :
    ∫ ω in A, (I u ω + D * (V u ω - S u ω / r)) ∂P
      = ∫ ω in A, I u ω ∂P + D * (∫ ω in A, V u ω ∂P - (∫ ω in A, S u ω ∂P) / r) := by
  rw [show (fun ω => I u ω + D * (V u ω - S u ω / r))
      = fun ω => 1 * I u ω + D * (1 * V u ω + (-(1 / r)) * S u ω) by funext ω; ring,
    setIntegral_lin hI (hV.lin hS 1 (-(1 / r))) 1 D A hu, setIntegral_lin hV hS 1 (-(1 / r)) A hu]
  ring

/-- **Cochrane (2023), (5.96), p. 166, under uncertainty: the feedback rule.** In every
equilibrium (`r, κ, σ > 0`), for every `t ≥ 0`, almost surely
`π_t = i_t + (r + λ₂)(v_t − s̃_t/r)` and `x_t = (λ₁(π_t − i_t) + ρ i_t)/κ`: inflation and output
are pinned by the (predetermined) value of debt and the shocks, as in (5.96) with `v₀ = v_t`.
Generalises the first conjunct of `CTSimple.ct_step_debt`. -/
theorem feedback_rule (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hr : 0 < r) (hκ : 0 < κ) (hσ : 0 < σ)
    (h : StochCTEq P W 𝓕 r σ κ ρ σi σs x infl v) {t : ℝ} (ht : 0 ≤ t) :
    infl t =ᵐ[P] (fun ω => iProc σi W t ω + (r + lam2 ρ κ σ) * (v t ω - sProc σs W t ω / r)) ∧
      x t =ᵐ[P] fun ω => (lam1 ρ κ σ * (infl t ω - iProc σi W t ω) + ρ * iProc σi W t ω) / κ := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h1 := lam1_pos (ρ := ρ) hκ hσ
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  have hsub := lam_sub ρ κ σ
  have hI := regProc_iProc hB hW h𝓕 hcont hW0 σi
  have hS := regProc_sProc hB hW h𝓕 hcont hW0 σs
  have hIm : AEStronglyMeasurable[𝓕 t] (iProc σi W t) P :=
    ((h𝓕.adapted t).const_mul σi).aestronglyMeasurable
  have hSm : AEStronglyMeasurable[𝓕 t] (fun ω => sProc σs W t ω / r) P := by
    have := (((h𝓕.adapted t).const_mul σs).mul_const r⁻¹).aestronglyMeasurable (μ := P)
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp [sProc, sPath, div_eq_mul_inv]
  have hrl : 0 < r + lam2 ρ κ σ := by linarith
  constructor
  · refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (𝓕.le t)
      (fun _ _ _ => (h.regPi.2.2.1 t ht).integrableOn)
      (fun _ _ _ => ((hI.2.2.1 t ht).add (((h.regV.2.2.1 t ht).sub
        ((hS.2.2.1 t ht).div_const r)).const_mul _)).integrableOn)
      (fun A hA _ => ?_) (h.adaptPi t ht)
      (hIm.add (((h.adaptV t ht).sub hSm).const_mul _))
    rw [setIntegral_feedback hI h.regV hS _ r A ht]
    have hG := debt_combination_zero hB hW h𝓕 hcont hW0 hr hκ hσ h ht hA
    field_simp at hG
    field_simp
    linear_combination (-1 : ℝ) * hG
  · have hlin : (fun ω => (lam1 ρ κ σ * (infl t ω - iProc σi W t ω) + ρ * iProc σi W t ω) / κ)
        = fun ω => lam1 ρ κ σ / κ * infl t ω + (ρ - lam1 ρ κ σ) / κ * iProc σi W t ω := by
      funext ω
      ring
    rw [hlin]
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (𝓕.le t)
      (fun _ _ _ => (h.regX.2.2.1 t ht).integrableOn)
      (fun _ _ _ => (((h.regPi.2.2.1 t ht).const_mul _).add
        ((hI.2.2.1 t ht).const_mul _)).integrableOn)
      (fun A hA _ => ?_) (h.adaptX t ht)
      (((h.adaptPi t ht).const_mul _).add (hIm.const_mul _))
    rw [setIntegral_lin h.regPi hI _ _ A ht]
    have hU := unstable_combination_zero hB hW h𝓕 hcont hW0 hκ hσ h ht hA
    have hl1 := h1.ne'
    have hk := hκ.ne'
    set SP := ∫ ω in A, infl t ω ∂P
    set SX := ∫ ω in A, x t ω ∂P
    set SI := ∫ ω in A, iProc σi W t ω ∂P
    have k2 : lam1 ρ κ σ * (κ / lam1 ρ κ σ * SX) = κ * SX := by field_simp
    have k3 : lam1 ρ κ σ * (lam2 ρ κ σ / lam1 ρ κ σ * SI) = lam2 ρ κ σ * SI := by field_simp
    have hκX : κ * SX = lam1 ρ κ σ * SP - lam2 ρ κ σ * SI := by
      linear_combination (-lam1 ρ κ σ) * hU - k2 - k3
    have k4 : κ * (lam1 ρ κ σ / κ * SP + (ρ - lam1 ρ κ σ) / κ * SI)
        = lam1 ρ κ σ * SP + (ρ - lam1 ρ κ σ) * SI := by field_simp
    refine mul_left_cancel₀ hk ?_
    linear_combination hκX - k4 + SI * hsub

/-! ### Existence and uniqueness -/

/-- Cochrane (2023), (5.96), p. 166: the explicit inflation obeys the feedback rule exactly,
`π_t = i_t + (r + λ₂)(v_t − s̃_t/r)` on every path.
Generalises the first conjunct of `CTSimple.ct_step_debt`. -/
theorem piProc_feedback (hr : r ≠ 0) (t : ℝ) (ω : Ω) :
    piProc r σ κ ρ σi σs W t ω
      = iProc σi W t ω + (r + lam2 ρ κ σ) * (vProc r σ κ ρ σs W t ω - sProc σs W t ω / r) := by
  simp only [piProc, piPath, iProc, iPath, vProc, vPath, sProc, sPath, fiscalLoad]
  field_simp
  ring

/-- Cochrane (2023), p. 166: the explicit output obeys `x_t = (λ₁(π_t − i_t) + ρ i_t)/κ` on every
path. -/
theorem xProc_feedback (t : ℝ) (ω : Ω) :
    xProc r σ κ ρ σi σs W t ω
      = (lam1 ρ κ σ * (piProc r σ κ ρ σi σs W t ω - iProc σi W t ω) + ρ * iProc σi W t ω) / κ := by
  simp only [xProc, xPath, piProc, piPath, iProc, iPath]
  ring

/-- **Cochrane (2023), §5.7.1, pp. 164–166: existence.** The explicit Wiener-integral solution
`(xProc, piProc, vProc)` is an equilibrium (`r, κ, σ > 0`). -/
theorem stochCTEq_exists (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hr : 0 < r) (hκ : 0 < κ) (hσ : 0 < σ) :
    StochCTEq P W 𝓕 r σ κ ρ σi σs (xProc r σ κ ρ σi σs W) (piProc r σ κ ρ σi σs W)
      (vProc r σ κ ρ σs W) := by
  have h2 := (lam2_pos (ρ := ρ) hκ hσ).le
  refine ⟨?_, ?_, ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_,
    fun t T ht htT => (ito_book_equations hB hW h𝓕 hcont hW0 hr.ne' hκ hσ ht htT).1,
    fun t T ht htT => (ito_book_equations hB hW h𝓕 hcont hW0 hr.ne' hκ hσ ht htT).2.1,
    fun ω t T => v_incr hr.ne' (continuous_bmReal (hcont ω)) t T, fun ω => ?_⟩
  · rw [xProc_eq_ker]
    exact regProc_kerProc hB hW h𝓕 hcont hW0 h2 _ _
  · rw [piProc_eq_ker]
    exact regProc_kerProc hB hW h𝓕 hcont hW0 h2 _ _
  · rw [vProc_eq_ker]
    exact regProc_kerProc hB hW h𝓕 hcont hW0 h2 _ _
  · rw [xProc_eq_ker]
    exact aesm_kerProc hB hW h𝓕 hcont hW0 _ _ _ ht
  · rw [piProc_eq_ker]
    exact aesm_kerProc hB hW h𝓕 hcont hW0 _ _ _ ht
  · rw [vProc_eq_ker]
    exact aesm_kerProc hB hW h𝓕 hcont hW0 _ _ _ ht
  · exact (path_zero (r := r) (σ := σ) (κ := κ) (ρ := ρ) (σi := σi) (σs := σs)
      (w := fun u => bmReal W u ω) (by simp [bmReal, hW0])).2.2.1

/-- **Cochrane (2023), §5.7.1, pp. 164–166: uniqueness.** Every equilibrium (`r, κ, σ > 0`)
coincides with the explicit solution: for every `t ≥ 0`, almost surely `x_t = xProc_t`,
`π_t = piProc_t`, `v_t = vProc_t`. With `responses_ito` this says that the unique equilibrium
is the book's impulse responses integrated against `dW`. -/
theorem stochCTEq_unique (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hr : 0 < r) (hκ : 0 < κ) (hσ : 0 < σ)
    (h : StochCTEq P W 𝓕 r σ κ ρ σi σs x infl v) {t : ℝ} (ht : 0 ≤ t) :
    x t =ᵐ[P] xProc r σ κ ρ σi σs W t ∧ infl t =ᵐ[P] piProc r σ κ ρ σi σs W t ∧
      v t =ᵐ[P] vProc r σ κ ρ σs W t := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h2 := lam2_pos (ρ := ρ) hκ hσ
  have hstar := stochCTEq_exists (ρ := ρ) (σi := σi) (σs := σs) hB hW h𝓕 hcont hW0 hr hκ hσ
  have hI := regProc_iProc hB hW h𝓕 hcont hW0 σi
  have hS := regProc_sProc hB hW h𝓕 hcont hW0 σs
  -- the value of debt
  have hv : ∀ τ, 0 ≤ τ → v τ =ᵐ[P] vProc r σ κ ρ σs W τ := by
    intro τ hτ
    have hzero : ∀ A : Set Ω, MeasurableSet A →
        ∫ ω in A, v τ ω ∂P - ∫ ω in A, vProc r σ κ ρ σs W τ ω ∂P = 0 := by
      intro A _
      set g := fun u => ∫ ω in A, v u ω ∂P - ∫ ω in A, vProc r σ κ ρ σs W u ω ∂P with hg
      obtain ⟨Cv, hCv0, hCv⟩ := h.regV.exists_nonneg
      obtain ⟨Cw, hCw0, hCw⟩ := hstar.regV.exists_nonneg
      have hmeas : Measurable g := (measurable_setIntegral_proc h.regV.1 h.regV.2.1 A).sub
        (measurable_setIntegral_proc hstar.regV.1 hstar.regV.2.1 A)
      have hbound : ∀ u, 0 ≤ u → |g u| ≤ (Cv + Cw) * (1 + u) := fun u hu =>
        (abs_sub _ _).trans ((add_le_add (abs_setIntegral_le h.regV hCv A hu)
          (abs_setIntegral_le hstar.regV hCw A hu)).trans_eq (by ring))
      refine stable_zero (c := -lam2 ρ κ σ) hmeas (add_nonneg hCv0 hCw0) hbound
        (fun T hT => ?_) hτ
      have hGv : RegProc P fun u ω => r * v u ω + iProc σi W u ω - infl u ω - sProc σs W u ω :=
        ((h.regV.lin hI r 1).lin (h.regPi.lin hS 1 1) 1 (-1)).congr (by funext u ω; ring)
      have hGw : RegProc P fun u ω => r * vProc r σ κ ρ σs W u ω + iProc σi W u ω
          - piProc r σ κ ρ σi σs W u ω - sProc σs W u ω :=
        ((hstar.regV.lin hI r 1).lin (hstar.regPi.lin hS 1 1) 1 (-1)).congr
          (by funext u ω; ring)
      have e1 := setIntegral_of_path (A := A) h.regV hGv le_rfl hT (fun ω => h.debt ω 0 T)
      have e2 := setIntegral_of_path (A := A) hstar.regV hGw le_rfl hT
        (fun ω => hstar.debt ω 0 T)
      have z1 : ∫ ω in A, v 0 ω ∂P = 0 := by simp [h.v0]
      have z2 : ∫ ω in A, vProc r σ κ ρ σs W 0 ω ∂P = 0 := by simp [hstar.v0]
      have hg0 : g T = (∫ u in (0 : ℝ)..T, ∫ ω in A,
          (r * v u ω + iProc σi W u ω - infl u ω - sProc σs W u ω) ∂P)
          - ∫ u in (0 : ℝ)..T, ∫ ω in A, (r * vProc r σ κ ρ σs W u ω + iProc σi W u ω
            - piProc r σ κ ρ σi σs W u ω - sProc σs W u ω) ∂P := by
        simp only [hg]
        rw [← e1, ← e2, z1, z2]
        ring
      rw [hg0, ← intervalIntegral.integral_sub (intervalIntegrable_setIntegral hGv A le_rfl hT)
        (intervalIntegrable_setIntegral hGw A le_rfl hT), ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le hT] at hu
      have hu0 := hu.1
      have hfb := (feedback_rule hB hW h𝓕 hcont hW0 hr hκ hσ h hu0).1
      have ep : ∫ ω in A, infl u ω ∂P = ∫ ω in A, iProc σi W u ω ∂P
          + (r + lam2 ρ κ σ) * (∫ ω in A, v u ω ∂P - (∫ ω in A, sProc σs W u ω ∂P) / r) := by
        rw [setIntegral_congr_ae (by assumption) (hfb.mono fun ω hω _ => hω)]
        exact setIntegral_feedback hI h.regV hS _ r A hu0
      have ew : ∫ ω in A, piProc r σ κ ρ σi σs W u ω ∂P = ∫ ω in A, iProc σi W u ω ∂P
          + (r + lam2 ρ κ σ) * (∫ ω in A, vProc r σ κ ρ σs W u ω ∂P
            - (∫ ω in A, sProc σs W u ω ∂P) / r) := by
        rw [show (fun ω => piProc r σ κ ρ σi σs W u ω) = fun ω => iProc σi W u ω
            + (r + lam2 ρ κ σ) * (vProc r σ κ ρ σs W u ω - sProc σs W u ω / r) by
          funext ω; exact piProc_feedback hr.ne' u ω]
        exact setIntegral_feedback hI hstar.regV hS _ r A hu0
      have la : ∀ {V Q : ℝ → Ω → ℝ}, RegProc P V → RegProc P Q →
          ∫ ω in A, (r * V u ω + iProc σi W u ω - Q u ω - sProc σs W u ω) ∂P
            = r * ∫ ω in A, V u ω ∂P + ∫ ω in A, iProc σi W u ω ∂P - ∫ ω in A, Q u ω ∂P
              - ∫ ω in A, sProc σs W u ω ∂P := by
        intro V Q hV hQ
        rw [show (fun ω => r * V u ω + iProc σi W u ω - Q u ω - sProc σs W u ω)
          = fun ω => 1 * (r * V u ω + 1 * iProc σi W u ω)
            + -1 * (1 * Q u ω + 1 * sProc σs W u ω) by funext ω; ring,
          setIntegral_lin (hV.lin hI r 1) (hQ.lin hS 1 1) 1 (-1) A hu0,
          setIntegral_lin hV hI r 1 A hu0, setIntegral_lin hQ hS 1 1 A hu0]
        ring
      rw [la h.regV h.regPi, la hstar.regV hstar.regPi, ep, ew]
      simp only [hg]
      ring
    have hint : Integrable (fun ω => v τ ω - vProc r σ κ ρ σs W τ ω) P :=
      (h.regV.2.2.1 τ hτ).sub (hstar.regV.2.2.1 τ hτ)
    have hae := hint.ae_eq_zero_of_forall_setIntegral_eq_zero fun A hA _ => by
      rw [integral_sub (h.regV.2.2.1 τ hτ).integrableOn (hstar.regV.2.2.1 τ hτ).integrableOn]
      exact hzero A hA
    filter_upwards [hae] with ω hω
    simp only [Pi.zero_apply] at hω
    linarith
  have hvt := hv t ht
  have hpt : infl t =ᵐ[P] piProc r σ κ ρ σi σs W t := by
    filter_upwards [(feedback_rule hB hW h𝓕 hcont hW0 hr hκ hσ h ht).1, hvt] with ω h1 h2
    rw [h1, h2, piProc_feedback hr.ne' t ω]
  refine ⟨?_, hpt, hvt⟩
  filter_upwards [(feedback_rule hB hW h𝓕 hcont hW0 hr hκ hσ h ht).2, hpt] with ω h1 h2
  rw [h1, h2, xProc_feedback t ω]

/-- **Cochrane (2023), §5.7.1, pp. 164–166 (non-vacuity)**: on the constructed motion `bmPath`
(on `gaussSeq`, natural filtration) the equilibrium exists, and every equilibrium equals it. -/
theorem bmPath_stochCTEq (hr : 0 < r) (hκ : 0 < κ) (hσ : 0 < σ) :
    StochCTEq gaussSeq bmPath (bmFiltrationReal bmPath measurable_bmPath) r σ κ ρ σi σs
        (xProc r σ κ ρ σi σs bmPath) (piProc r σ κ ρ σi σs bmPath) (vProc r σ κ ρ σs bmPath) ∧
      ∀ x' infl' v' : ℝ → (ℕ → ℝ) → ℝ,
        StochCTEq gaussSeq bmPath (bmFiltrationReal bmPath measurable_bmPath) r σ κ ρ σi σs
          x' infl' v' → ∀ t, 0 ≤ t →
          x' t =ᵐ[gaussSeq] xProc r σ κ ρ σi σs bmPath t ∧
          infl' t =ᵐ[gaussSeq] piProc r σ κ ρ σi σs bmPath t ∧
          v' t =ᵐ[gaussSeq] vProc r σ κ ρ σs bmPath t := by
  have hB := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hB measurable_bmPath
  exact ⟨stochCTEq_exists hB measurable_bmPath h𝓕 continuous_bmPath bmPath_zero hr hκ hσ,
    fun _ _ _ h t ht => stochCTEq_unique hB measurable_bmPath h𝓕 continuous_bmPath bmPath_zero
      hr hκ hσ h ht⟩

end Cochrane.StickyPriceFiscal.TidyR7StochCTUnique
