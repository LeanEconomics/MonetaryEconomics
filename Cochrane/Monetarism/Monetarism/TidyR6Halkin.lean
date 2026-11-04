/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Halkin's counterexample: the transversality condition is not necessary in general

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix Chapter 4, (4.17),
pp. 640–641: the Hamiltonian conditions include the transversality condition
`lim e^{−δt}m_tµ_t = 0`. `TidyR6Pontryagin.tvc_necessary` proves it necessary under a scaling
condition (Kamihigashi 2001). This module shows that some such condition is needed: in the
minimal infinite-horizon problem of Halkin (1974) an optimum exists at which NO costate
satisfying the adjoint equation meets the transversality condition.

## The problem

State `x`, continuous control `u_t ∈ [0, 1]`, `ẋ = (1 − x)u`, `x_0 = 0`; maximise
`∫_0^∞ (1 − x_t)u_t dt` (`HalkinFeasible`). The Hamiltonian is `H = (1 + λ)(1 − x)u`, the adjoint
equation `λ̇ = −∂H/∂x = (1 + λ)u`.

## Main results

* `halkin_one_sub_pos`: along every feasible path `1 − x_t = e^{−∫_0^t u} > 0`.
* `halkin_value_le_one`: every feasible plan with integrable objective has value `≤ 1`.
* `halkin_optimal`: `u ≡ 1`, `x_t = 1 − e^{−t}` is feasible with value `1`, hence optimal.
* `halkin_no_tvc`: along it, every solution of the adjoint equation `λ̇ = 1 + λ` has
  `λ_tx_t ↛ 0` (and `λ_t ↛ 0`): the transversality condition fails for every costate.
-/

namespace Cochrane.Monetarism.TidyR6Halkin

open MeasureTheory Filter Topology

/-- Cochrane (2023), A4 (4.17), p. 640 (Halkin's problem): a feasible plan: continuous control
with values in `[0, 1]`, `x_0 = 0` and `ẋ = (1 − x)u` everywhere. -/
def HalkinFeasible (u x : ℝ → ℝ) : Prop :=
  Continuous u ∧ (∀ t, 0 ≤ u t ∧ u t ≤ 1) ∧ x 0 = 0 ∧ ∀ t, HasDerivAt x ((1 - x t) * u t) t

/-- Cochrane (2023), A4 (4.17), p. 640 (Halkin's problem): along a feasible path
`1 − x_t = e^{−∫_0^t u}`, in particular `x_t < 1`. -/
theorem halkin_one_sub_pos {u x : ℝ → ℝ} (h : HalkinFeasible u x) (t : ℝ) :
    1 - x t = Real.exp (-∫ r in (0 : ℝ)..t, u r) ∧ x t < 1 := by
  obtain ⟨hu, -, hx0, hxd⟩ := h
  set U : ℝ → ℝ := fun t => ∫ r in (0 : ℝ)..t, u r with hU
  have hUd : ∀ t, HasDerivAt U (u t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hu.intervalIntegrable _ _)
      hu.aestronglyMeasurable.stronglyMeasurableAtFilter hu.continuousAt
  set z : ℝ → ℝ := fun t => (1 - x t) * Real.exp (U t) with hz
  have hzd : ∀ t, HasDerivAt z 0 t := by
    intro t
    have := ((hxd t).const_sub 1).mul ((hUd t).exp)
    convert this using 1
    ring
  have hconst : ∀ t, z t = z 0 := fun t =>
    is_const_of_deriv_eq_zero (fun t => (hzd t).differentiableAt) (fun t => (hzd t).deriv) t 0
  have hz0 : z 0 = 1 := by simp [hz, hU, hx0]
  have e : 1 - x t = Real.exp (-U t) := by
    have h1 := hconst t
    rw [hz0] at h1
    simp only [hz] at h1
    have hp := (Real.exp_pos (U t)).ne'
    rw [Real.exp_neg]
    field_simp
    exact h1
  refine ⟨e, ?_⟩
  have := Real.exp_pos (-U t)
  linarith

/-- Cochrane (2023), A4 (4.17), p. 640 (Halkin's problem): every feasible plan whose objective
is integrable on `(0, ∞)` has value at most `1` (the integrand is `ẋ` and `x < 1`). -/
theorem halkin_value_le_one {u x : ℝ → ℝ} (h : HalkinFeasible u x)
    (hi : IntegrableOn (fun t => (1 - x t) * u t) (Set.Ioi 0)) :
    ∫ t in Set.Ioi 0, (1 - x t) * u t ≤ 1 := by
  have hcont : Continuous fun t => (1 - x t) * u t :=
    (continuous_const.sub (continuous_iff_continuousAt.2 fun t =>
      (h.2.2.2 t).continuousAt)).mul h.1
  have hftc : ∀ T, ∫ t in (0 : ℝ)..T, (1 - x t) * u t = x T := by
    intro T
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => h.2.2.2 t)
      (hcont.intervalIntegrable _ _), h.2.2.1, sub_zero]
  have hlim := intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id
  simp only [id, hftc] at hlim
  exact le_of_tendsto' hlim fun T => (halkin_one_sub_pos h T).2.le

/-- **Cochrane (2023), A4 (4.17), p. 640 (Halkin's problem): an optimum.** `u ≡ 1`,
`x_t = 1 − e^{−t}` is feasible, its objective `∫_0^∞ e^{−t} dt = 1` is integrable, and no
feasible plan with integrable objective does better. -/
theorem halkin_optimal :
    HalkinFeasible (fun _ => 1) (fun t => 1 - Real.exp (-t)) ∧
      IntegrableOn (fun t => (1 - (1 - Real.exp (-t))) * 1) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi 0, (1 - (1 - Real.exp (-t))) * 1 = 1 ∧
      ∀ u x, HalkinFeasible u x → IntegrableOn (fun t => (1 - x t) * u t) (Set.Ioi 0) →
        ∫ t in Set.Ioi 0, (1 - x t) * u t ≤
          ∫ t in Set.Ioi 0, (1 - (1 - Real.exp (-t))) * 1 := by
  have e : (fun t : ℝ => (1 - (1 - Real.exp (-t))) * 1) = fun t => Real.exp (-t) := by
    funext t; ring
  have hval : ∫ t in Set.Ioi 0, (1 - (1 - Real.exp (-t))) * 1 = 1 := by
    rw [e]; exact integral_exp_neg_Ioi_zero
  refine ⟨⟨continuous_const, fun _ => ⟨zero_le_one, le_rfl⟩, by simp, fun t => ?_⟩, ?_, hval,
    fun u x h hi => ?_⟩
  · have := ((hasDerivAt_neg' t).exp).const_sub 1
    convert this using 1
    ring
  · rw [e]; exact integrableOn_exp_neg_Ioi 0
  · rw [hval]; exact halkin_value_le_one h hi

/-- **Cochrane (2023), A4 (4.17), pp. 640–641: the transversality condition fails at Halkin's
optimum.** Along `u ≡ 1`, `x_t = 1 − e^{−t}`, every solution of the adjoint equation
`λ̇ = −∂H/∂x = 1 + λ` violates both `λ_tx_t → 0` and `λ_t → 0`. -/
theorem halkin_no_tvc {lam : ℝ → ℝ} (hlam : ∀ t, HasDerivAt lam (1 + lam t) t) :
    ¬ Tendsto (fun t => lam t * (1 - Real.exp (-t))) atTop (𝓝 0) ∧
      ¬ Tendsto lam atTop (𝓝 0) := by
  -- `(1 + λ_t)e^{−t}` is constant
  set C := 1 + lam 0 with hC
  have hz : ∀ t, (1 + lam t) * Real.exp (-t) = C := by
    have hd : ∀ t, HasDerivAt (fun t => (1 + lam t) * Real.exp (-t)) 0 t := by
      intro t
      have := ((hlam t).const_add 1).mul ((hasDerivAt_neg' t).exp)
      convert this using 1
      ring
    intro t
    have := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv)
      t 0
    simpa [hC] using this
  have hexp : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hlamx : ∀ t, lam t * (1 - Real.exp (-t)) =
      (C - Real.exp (-t)) * (Real.exp (-t))⁻¹ * (1 - Real.exp (-t)) := by
    intro t
    have hpos := Real.exp_pos (-t)
    have : lam t = (C - Real.exp (-t)) * (Real.exp (-t))⁻¹ := by
      rw [← hz t]; field_simp; ring
    rw [this]
  -- if `λx → 0` or `λ → 0`, then `C = 0`, so `λ ≡ −1`
  have hC0 : ∀ f : ℝ → ℝ, Tendsto f atTop (𝓝 0) →
      (∀ t, f t = lam t * (1 - Real.exp (-t))) ∨ (∀ t, f t = lam t) → C = 0 := by
    intro f hf hform
    have hmul : Tendsto (fun t => f t * Real.exp (-t)) atTop (𝓝 0) := by
      simpa using hf.mul hexp
    have hCt : Tendsto (fun t => (1 + lam t) * Real.exp (-t)) atTop (𝓝 C) := by
      simp only [hz]; exact tendsto_const_nhds
    have hother : Tendsto (fun t => (1 + lam t) * Real.exp (-t)) atTop (𝓝 0) := by
      rcases hform with hform | hform
      · -- `(1 + λ)e^{−t} = f e^{−t}/(1 − e^{−t}) + e^{−t}` eventually
        have h1 : Tendsto (fun t => f t * Real.exp (-t) / (1 - Real.exp (-t)) + Real.exp (-t))
            atTop (𝓝 (0 / (1 - 0) + 0)) :=
          (hmul.div (tendsto_const_nhds.sub hexp) (by norm_num)).add hexp
        simp only [sub_zero, zero_div, add_zero] at h1
        refine h1.congr' ?_
        filter_upwards [eventually_gt_atTop 0] with t ht
        have hlt : Real.exp (-t) < 1 := by
          have := Real.exp_lt_exp.2 (show -t < 0 by linarith); rwa [Real.exp_zero] at this
        have hne : 1 - Real.exp (-t) ≠ 0 := by linarith
        rw [hform t]
        field_simp
        ring
      · have h1 : Tendsto (fun t => f t * Real.exp (-t) + Real.exp (-t)) atTop (𝓝 (0 + 0)) :=
          hmul.add hexp
        simp only [add_zero] at h1
        refine h1.congr fun t => ?_
        rw [hform t]; ring
    exact tendsto_nhds_unique hCt hother
  have hlam1 : C = 0 → ∀ t, lam t = -1 := by
    intro h0 t
    have := hz t
    rw [h0] at this
    have hpos := (Real.exp_pos (-t)).ne'
    have : 1 + lam t = 0 := by
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h hpos
    linarith
  constructor
  · intro htend
    have hc := hC0 _ htend (Or.inl fun t => rfl)
    have hm1 := hlam1 hc
    have h2 : Tendsto (fun t => lam t * (1 - Real.exp (-t))) atTop (𝓝 (-1 * (1 - 0))) := by
      simp only [hm1]
      exact tendsto_const_nhds.mul (tendsto_const_nhds.sub hexp)
    have := tendsto_nhds_unique htend h2
    norm_num at this
  · intro htend
    have hc := hC0 _ htend (Or.inr fun t => rfl)
    have hm1 := hlam1 hc
    have h2 : Tendsto lam atTop (𝓝 (-1)) := by
      have : lam = fun _ => -1 := funext hm1
      rw [this]; exact tendsto_const_nhds
    have := tendsto_nhds_unique htend h2
    norm_num at this

end Cochrane.Monetarism.TidyR6Halkin
