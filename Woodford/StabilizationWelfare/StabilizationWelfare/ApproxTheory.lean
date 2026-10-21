/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.ExpLogCES
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Operator.Asymptotics
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Asymptotics.Prod
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Approximation of loss functions (Chapter 6, §1)

Woodford (2003), *Interest and Prices*, Chapter 6, §1 "Approximation of Loss Functions and
Optimal Policies", pp. 383–392, eqs. (1.1)–(1.10) and footnote 7.

Setting. The endogenous variables `x̃ = x − x̄` (in a normed space `X`) and the disturbances
`ξ` (in `Ξ`) are random variables on a finite state space `Ω` with probabilities `p`, and depend
on a parameter `a` that tends along a filter `l`; their size is measured by `s a → 0`
(Woodford's `‖ϕ, ξ‖`). Welfare is `U : X × Ξ → ℝ`, expanded at `z̄ = (x̄, 0)` with
`Ū = U z̄`, gradient `L = DU(z̄)` and Hessian `B = D²U(z̄)`.

## Main results

* (1.2) The multivariate second-order Taylor expansion with a cubic remainder for `C³` `U`
  (`taylor2_multivar_bound`, `taylor2_multivar_isBigO_of_contDiff`); with only `C²` the
  remainder is `o(‖z‖²)` (`taylor2_multivar_isLittleO`,
  `taylor2_multivar_isLittleO_of_contDiff_two`), and not `O(‖z‖³)` in
  general (`not_taylor2_multivar_isBigO_of_contDiff_two`) — survey error 19.
* (1.3) Corrected: `E[U] = Ū + U_x E[x̃] + ½ tr{U_zz var z} + ½ E[z]′U_zz E[z] + O(3)`
  (`expected_utility_corrected`, exact part `expect_quadApprox`); the printed formula drops the
  last term, which is second order: `printed13_false` (survey error 18). The trace
  form of the variance term is `expect_quadForm_eq_trace`.
* Footnote 7: `E[U] = U⁽⁰⁾ + O(‖ϕ, ξ‖²)` holds (`expected_utility_sub_U0_isBigO_sq`) but the
  printed `O(‖ϕ, ξ‖³)` is false (`fn7_false`).
* `E[U] = U⁽¹⁾ + U_x E[x̃ − x̃⁰] + O(3)` with the corrected `U⁽¹⁾` (which carries
  `½ x̃⁰′U_xx x̃⁰`, `U1_eq_printed_add`): `expected_utility_eq_U1_add`; false with the printed
  `U⁽¹⁾` (`U1printed_false`).
* (1.5)–(1.6): `U_x(x̄; 0) = 0` makes `U⁽¹⁾` a valid second-order approximation
  (`expected_utility_eq_U1_of_ux_eq_zero`) and gives correct welfare rankings
  (`welfare_ranking_U1`); without it `U⁽¹⁾` cannot rank policies with the same `x̃⁰`
  (`U1_fails_without_ux_zero`).
* (1.7)–(1.8): `U_x(x̄; Φ) = O(Φ)` is equivalent, for a smooth family, to `U_x(x̄; 0) = 0`
  (`isBigO_id_iff_eq_zero`); then `U_x E[x̃ − x̃⁰] = O(3)` (`ux_mul_isBigO`), and expanding
  jointly in `(Φ, x, ξ)` gives `E[U] = U⁽¹⁾ + O(Φ, ϕ, ξ³)`
  (`expected_utility_eq_U1_of_ux_param`).
* (1.9)–(1.10) Benigno–Woodford: `E[U] = Ū + E[z̃′ V z̃] + O(3)` with `V = ½ U_zz + W`
  (`benigno_woodford`); `E[U] = V⁽¹⁾ + V_xx(x̃⁰, x̃⁰) + O(3)` (`benigno_woodford_V1`), so the
  printed `V⁽¹⁾` is valid when `x̃⁰ = 0` (`benigno_woodford_V1_of_x0_eq_zero`) but not in
  general (`V1printed_false`).
-/

namespace Woodford.StabilizationWelfare.ApproxTheory

open Filter Topology Asymptotics
open Woodford.StabilizationWelfare.OneParamTaylor

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## (1.2): multivariate Taylor expansion -/

/-- Woodford (2003), eq. (1.2), p. 385: the quadratic approximation
`Ū + U_z z + ½ z′U_zz z` to `U(z̄ + z)` with coefficients `u0`, `L`, `B`. -/
noncomputable def quadApprox (u0 : ℝ) (L : F →L[ℝ] ℝ) (B : F →L[ℝ] F →L[ℝ] ℝ) (z : F) : ℝ :=
  u0 + L z + 1 / 2 * B z z

/-- Woodford (2003), eq. (1.2), p. 385 (analytic core): if `U` has first and second derivatives
`U1`, `U2` along the segment `[z̄, z̄ + z]` and `‖U2(z̄ + s z) − U2 z̄‖ ≤ C` there, then
`|U(z̄ + z) − (Ū + U_z z + ½ z′U_zz z)| ≤ C ‖z‖²`. -/
theorem taylor2_multivar_segment_le {U : F → ℝ} {U1 : F → F →L[ℝ] ℝ}
    {U2 : F → F →L[ℝ] F →L[ℝ] ℝ} {zbar z : F} {C : ℝ}
    (hU : ∀ s : ℝ, |s| ≤ 1 → HasFDerivAt U (U1 (zbar + s • z)) (zbar + s • z))
    (hU1 : ∀ s : ℝ, |s| ≤ 1 → HasFDerivAt U1 (U2 (zbar + s • z)) (zbar + s • z))
    (hC : ∀ s : ℝ, |s| ≤ 1 → ‖U2 (zbar + s • z) - U2 zbar‖ ≤ C) :
    |U (zbar + z) - quadApprox (U zbar) (U1 zbar) (U2 zbar) z| ≤ C * ‖z‖ ^ 2 := by
  have hpath : ∀ s : ℝ, HasDerivAt (fun s : ℝ => zbar + s • z) z s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const z).const_add zbar
  have key := taylor2_remainder_le (r := 1) (C := C * ‖z‖ ^ 2) (ε := 1)
    (f := fun s => U (zbar + s • z)) (f1 := fun s => U1 (zbar + s • z) z)
    (f2 := fun s => U2 (zbar + s • z) z z)
    (fun s hs => ?_) (fun s hs => ?_) (fun s hs => ?_) (by simp)
  · simpa [quadApprox] using key
  · have hs' : |s| ≤ 1 := by simpa using hs
    exact (hU s hs').comp_hasDerivAt s (hpath s)
  · have hs' : |s| ≤ 1 := by simpa using hs
    have h1 : HasDerivAt (fun s : ℝ => U1 (zbar + s • z)) (U2 (zbar + s • z) z) s :=
      (hU1 s hs').comp_hasDerivAt s (hpath s)
    have h2 := HasDerivAt.clm_apply (c := fun s : ℝ => U1 (zbar + s • z)) (u := fun _ => z) h1
      (hasDerivAt_const s z)
    refine h2.congr_deriv ?_
    simp
  · have hs' : |s| ≤ 1 := by simpa using hs
    have e : U2 (zbar + s • z) z z - U2 (zbar + (0 : ℝ) • z) z z =
        (U2 (zbar + s • z) - U2 zbar) z z := by simp
    rw [e]
    calc |(U2 (zbar + s • z) - U2 zbar) z z|
        ≤ ‖U2 (zbar + s • z) - U2 zbar‖ * ‖z‖ * ‖z‖ := by
          simpa [Real.norm_eq_abs] using
            ContinuousLinearMap.le_opNorm₂ (U2 (zbar + s • z) - U2 zbar) z z
      _ ≤ C * ‖z‖ * ‖z‖ := by gcongr; exact hC s hs'
      _ = C * ‖z‖ ^ 2 := by ring

/-- Woodford (2003), eq. (1.2), p. 385, with a Lipschitz Hessian: if on the ball `B(z̄, δ)`
`U` has derivatives `U1`, `U2` with `‖U2 w − U2 z̄‖ ≤ K ‖w − z̄‖` (`K ≥ 0`), then for
`‖z‖ < δ`, `|U(z̄ + z) − (Ū + U_z z + ½ z′U_zz z)| ≤ K ‖z‖³`. -/
theorem taylor2_multivar_bound {U : F → ℝ} {U1 : F → F →L[ℝ] ℝ}
    {U2 : F → F →L[ℝ] F →L[ℝ] ℝ} {zbar : F} {δ K : ℝ} (hK0 : 0 ≤ K)
    (hU : ∀ w ∈ Metric.ball zbar δ, HasFDerivAt U (U1 w) w)
    (hU1 : ∀ w ∈ Metric.ball zbar δ, HasFDerivAt U1 (U2 w) w)
    (hK : ∀ w ∈ Metric.ball zbar δ, ‖U2 w - U2 zbar‖ ≤ K * ‖w - zbar‖)
    {z : F} (hz : ‖z‖ < δ) :
    |U (zbar + z) - quadApprox (U zbar) (U1 zbar) (U2 zbar) z| ≤ K * ‖z‖ ^ 3 := by
  have hmem : ∀ s : ℝ, |s| ≤ 1 → zbar + s • z ∈ Metric.ball zbar δ := fun s hs => by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    calc |s| * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
      _ < δ := by simpa using hz
  have key := taylor2_multivar_segment_le (C := K * ‖z‖)
    (fun s hs => hU _ (hmem s hs)) (fun s hs => hU1 _ (hmem s hs)) (fun s hs => ?_)
  · calc _ ≤ K * ‖z‖ * ‖z‖ ^ 2 := key
      _ = K * ‖z‖ ^ 3 := by ring
  · calc ‖U2 (zbar + s • z) - U2 zbar‖ ≤ K * ‖zbar + s • z - zbar‖ := hK _ (hmem s hs)
      _ = K * (|s| * ‖z‖) := by rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      _ ≤ K * (1 * ‖z‖) := by gcongr
      _ = K * ‖z‖ := by ring

/-- Woodford (2003), eq. (1.2), p. 385, for `C³` welfare: the second-order Taylor remainder
`U(z̄ + z) − (Ū + U_z z + ½ z′U_zz z)` is `O(‖z‖³)` as `z → 0`. -/
theorem taylor2_multivar_isBigO_of_contDiff {U : F → ℝ} (hU : ContDiff ℝ 3 U) (zbar : F) :
    (fun z => U (zbar + z) - quadApprox (U zbar) (fderiv ℝ U zbar)
      (fderiv ℝ (fderiv ℝ U) zbar) z) =O[𝓝 0] (fun z => ‖z‖ ^ 3) := by
  have h1 : ContDiff ℝ 2 (fderiv ℝ U) := hU.fderiv_right (by norm_num)
  have h2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ U)) := h1.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := h2.contDiffAt.exists_lipschitzOnWith (x := zbar)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 ht
  refine IsBigO.of_bound K ?_
  filter_upwards [Metric.ball_mem_nhds (0 : F) hδ] with z hz
  have hz' : ‖z‖ < δ := by simpa using hz
  have key := taylor2_multivar_bound (U1 := fderiv ℝ U) (U2 := fderiv ℝ (fderiv ℝ U))
    (zbar := zbar) (δ := δ) K.coe_nonneg
    (fun w _ => (hU.differentiable (by norm_num) w).hasFDerivAt)
    (fun w _ => (h1.differentiable (by norm_num) w).hasFDerivAt) (fun w hw => ?_) hz'
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_norm]
    exact key
  · have := hK.dist_le_mul w (hball hw) zbar (hball (Metric.mem_ball_self hδ))
    simpa [dist_eq_norm] using this

/-- Woodford (2003), eq. (1.2), p. 385 (analytic core, first-derivative form): if `U` has
derivative `U1` along the segment `[z̄, z̄ + z]` and
`|U1(z̄ + s z) z − U1(z̄) z − s B(z, z)| ≤ C` for `|s| ≤ 1`, then
`|U(z̄ + z) − (Ū + U1(z̄) z + ½ B(z, z))| ≤ C`. -/
theorem taylor2_multivar_firstDeriv_le {U : F → ℝ} {U1 : F → F →L[ℝ] ℝ}
    {B : F →L[ℝ] F →L[ℝ] ℝ} {zbar z : F} {C : ℝ}
    (hU : ∀ s : ℝ, |s| ≤ 1 → HasFDerivAt U (U1 (zbar + s • z)) (zbar + s • z))
    (hC : ∀ s : ℝ, |s| ≤ 1 → |U1 (zbar + s • z) z - U1 zbar z - s * B z z| ≤ C) :
    |U (zbar + z) - quadApprox (U zbar) (U1 zbar) B z| ≤ C := by
  have hpath : ∀ s : ℝ, HasDerivAt (fun s : ℝ => zbar + s • z) z s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const z).const_add zbar
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s : ℝ => U (zbar + s • z) - s * U1 zbar z - s ^ 2 / 2 * B z z)
    (f' := fun s : ℝ => U1 (zbar + s • z) z - U1 zbar z - s * B z z)
    (s := Metric.closedBall (0 : ℝ) 1) (C := C) (fun s hs => ?_) (fun s hs => ?_)
    (convex_closedBall 0 1) (Metric.mem_closedBall_self zero_le_one)
    (show (1 : ℝ) ∈ Metric.closedBall (0 : ℝ) 1 by simp)
  · simp only [one_smul, zero_smul, add_zero, one_mul, zero_mul, sub_zero, one_pow,
      Real.norm_eq_abs] at key
    have e : U (zbar + z) - U1 zbar z - 1 / 2 * B z z - (U zbar - 0 ^ 2 / 2 * B z z) =
        U (zbar + z) - quadApprox (U zbar) (U1 zbar) B z := by
      simp [quadApprox]
      ring
    rw [← e]
    simpa using key
  · have hs' : |s| ≤ 1 := by simpa using hs
    have h1 := (hU s hs').comp_hasDerivAt s (hpath s)
    have h2 := HasDerivAt.sub (HasDerivAt.sub h1 ((hasDerivAt_id s).mul_const (U1 zbar z)))
      (((hasDerivAt_pow 2 s).div_const 2).mul_const (B z z))
    refine (h2.congr_deriv ?_).hasDerivWithinAt
    simp only [Nat.cast_ofNat]
    ring
  · have hs' : |s| ≤ 1 := by simpa using hs
    simpa [Real.norm_eq_abs] using hC s hs'

/-- Woodford (2003), eq. (1.2), p. 385, under the book's literal hypothesis "at least twice
differentiable" (survey error 19): if `U` is differentiable near `z̄` with derivative `U1`, and
`U1` is differentiable at `z̄` with derivative `B`, the Taylor remainder is `o(‖z‖²)` — only
this, not `O(‖z‖³)`. -/
theorem taylor2_multivar_isLittleO {U : F → ℝ} {U1 : F → F →L[ℝ] ℝ}
    {B : F →L[ℝ] F →L[ℝ] ℝ} {zbar : F} (hU : ∀ᶠ w in 𝓝 zbar, HasFDerivAt U (U1 w) w)
    (hU1 : HasFDerivAt U1 B zbar) :
    (fun z => U (zbar + z) - quadApprox (U zbar) (U1 zbar) B z) =o[𝓝 0]
      (fun z => ‖z‖ ^ 2) := by
  refine isLittleO_iff.2 fun c hc => ?_
  have h2 := isLittleO_iff.1 (hasFDerivAt_iff_isLittleO_nhds_zero.1 hU1) hc
  have h3 : ∀ᶠ v in 𝓝 (0 : F), HasFDerivAt U (U1 (zbar + v)) (zbar + v) := by
    have ht : Tendsto (fun v : F => zbar + v) (𝓝 0) (𝓝 zbar) := by
      have hc : Continuous (fun v : F => zbar + v) := by fun_prop
      simpa using hc.tendsto (0 : F)
    exact ht.eventually hU
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h2.and h3)
  filter_upwards [Metric.ball_mem_nhds (0 : F) hδ] with z hz
  have hz' : ‖z‖ < δ := by simpa using hz
  have hmem : ∀ s : ℝ, |s| ≤ 1 → s • z ∈ Metric.ball (0 : F) δ := fun s hs => by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs]
    calc |s| * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
      _ < δ := by simpa using hz'
  have key := taylor2_multivar_firstDeriv_le (B := B) (C := c * ‖z‖ ^ 2)
    (fun s hs => (hball _ (hmem s hs)).2) (fun s hs => ?_)
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_norm]
    exact key
  · have hb := (hball _ (hmem s hs)).1
    have e : U1 (zbar + s • z) z - U1 zbar z - s * B z z =
        (U1 (zbar + s • z) - U1 zbar - B (s • z)) z := by simp
    rw [e]
    have hsz : ‖s • z‖ ≤ ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |s| * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
        _ = ‖z‖ := one_mul _
    calc |(U1 (zbar + s • z) - U1 zbar - B (s • z)) z|
        ≤ ‖U1 (zbar + s • z) - U1 zbar - B (s • z)‖ * ‖z‖ := by
          simpa [Real.norm_eq_abs] using
            (U1 (zbar + s • z) - U1 zbar - B (s • z)).le_opNorm z
      _ ≤ c * ‖s • z‖ * ‖z‖ := by gcongr
      _ ≤ c * ‖z‖ * ‖z‖ := by gcongr
      _ = c * ‖z‖ ^ 2 := by ring

/-- Woodford (2003), eq. (1.2), p. 385, for `C²` welfare: the Taylor remainder is `o(‖z‖²)`
(survey error 19: this is all that "at least twice differentiable" gives). -/
theorem taylor2_multivar_isLittleO_of_contDiff_two {U : F → ℝ} (hU : ContDiff ℝ 2 U)
    (zbar : F) :
    (fun z => U (zbar + z) - quadApprox (U zbar) (fderiv ℝ U zbar)
      (fderiv ℝ (fderiv ℝ U) zbar) z) =o[𝓝 0] (fun z => ‖z‖ ^ 2) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ U) := hU.fderiv_right (by norm_num)
  exact taylor2_multivar_isLittleO
    (Eventually.of_forall fun w => (hU.differentiable (by norm_num) w).hasFDerivAt)
    (h1.differentiable (by norm_num) zbar).hasFDerivAt

/-- Woodford (2003), eq. (1.2), p. 385 (survey error 19, counterexample): the `C²` function
`x ↦ x^{5/2}` on `ℝ` has a second-order Taylor remainder at `0` that is NOT `O(‖z‖³)`; so
"at least twice differentiable" does not justify the printed `O(‖ϕ, ξ‖³)` residual. -/
theorem not_taylor2_multivar_isBigO_of_contDiff_two :
    ∃ U : ℝ → ℝ, ContDiff ℝ 2 U ∧
      ¬ (fun z => U (0 + z) - quadApprox (U 0) (fderiv ℝ U 0)
        (fderiv ℝ (fderiv ℝ U) 0) z) =O[𝓝 0] (fun z => ‖z‖ ^ 3) := by
  obtain ⟨f, hf, hnot⟩ := not_taylor2_isBigO_of_contDiff_two
  refine ⟨f, hf, fun H => hnot ?_⟩
  have h1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hfd : fderiv ℝ f = fun x =>
      ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ) (deriv f x) := by
    funext x
    rw [((hf.differentiable (by norm_num) x).hasDerivAt.hasFDerivAt).fderiv]
    rfl
  have hfd2 : fderiv ℝ (fderiv ℝ f) 0 = (ContinuousLinearMap.smulRightL ℝ ℝ ℝ
      (1 : ℝ →L[ℝ] ℝ)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight (deriv (deriv f) 0)) := by
    rw [hfd]
    exact ((ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).hasFDerivAt.comp 0
      (h1.differentiable (by norm_num) 0).hasDerivAt.hasFDerivAt).fderiv
  refine (H.congr_left fun z => ?_).trans (isBigO_of_le _ fun z => ?_)
  · rw [hfd2, hfd]
    simp [quadApprox]
    ring
  · simp

/-! ## Expectations of linear and quadratic forms -/

variable {Ω : Type*} [Fintype Ω]

/-- Woodford (2003), eq. (1.3), p. 386: `E[B(z, v)] = B(E z, v)` for a bilinear form. -/
theorem expect_bilin_left (p : Ω → ℝ) (B : F →L[ℝ] F →L[ℝ] ℝ) (z : Ω → F) (v : F) :
    expect p (fun ω => B (z ω) v) = B (expect p z) v := by
  simp [expect, map_sum, map_smul]

/-- Woodford (2003), eq. (1.3), p. 386: `E[B(v, z)] = B(v, E z)` for a bilinear form. -/
theorem expect_bilin_right (p : Ω → ℝ) (B : F →L[ℝ] F →L[ℝ] ℝ) (z : Ω → F) (v : F) :
    expect p (fun ω => B v (z ω)) = B v (expect p z) := by
  simp [expect, map_sum, map_smul]

/-- Woodford (2003), eq. (1.3), p. 386 (the identity behind survey error 18): for a bilinear form
`B` and probability weights, `E[B(z, z)] = E[B(z − E z, z − E z)] + B(E z, E z)` — the
uncentred second moment is the variance term PLUS the mean term. -/
theorem expect_bilin_centered {p : Ω → ℝ} (hp1 : ∑ ω, p ω = 1) (B : F →L[ℝ] F →L[ℝ] ℝ)
    (z : Ω → F) :
    expect p (fun ω => B (z ω) (z ω)) =
      expect p (fun ω => B (z ω - expect p z) (z ω - expect p z)) +
        B (expect p z) (expect p z) := by
  set m := expect p z
  have h : ∀ ω, B (z ω - m) (z ω - m) = B (z ω) (z ω) - B (z ω) m - B m (z ω) + B m m :=
    fun ω => by simp [map_sub]; ring
  have e : expect p (fun ω => B (z ω - m) (z ω - m)) =
      expect p (fun ω => B (z ω) (z ω) - B (z ω) m - B m (z ω) + B m m) :=
    congrArg _ (funext h)
  rw [e, expect_add, expect_sub, expect_sub, expect_bilin_left, expect_bilin_right,
    expect_const hp1]
  ring

/-- Woodford (2003), eq. (1.3), p. 386: the expectation of the quadratic approximation,
`E[Ū + L z + ½ B(z, z)] = Ū + L(E z) + ½ E[B(z, z)]`. -/
theorem expect_quadApprox {p : Ω → ℝ} (hp1 : ∑ ω, p ω = 1) (u0 : ℝ) (L : F →L[ℝ] ℝ)
    (B : F →L[ℝ] F →L[ℝ] ℝ) (z : Ω → F) :
    expect p (fun ω => quadApprox u0 L B (z ω)) =
      u0 + L (expect p z) + 1 / 2 * expect p (fun ω => B (z ω) (z ω)) := by
  have e : (fun ω => quadApprox u0 L B (z ω)) =
      fun ω => (u0 + L (z ω)) + (1 / 2 : ℝ) • B (z ω) (z ω) := by
    funext ω; simp [quadApprox]
  rw [e, expect_add, expect_add, expect_const hp1, expect_smul, OneParamTaylor.map_expect,
    smul_eq_mul]

/-- Woodford (2003), eq. (1.3), p. 386, AS PRINTED: `Ū + U_z E[z] + ½ tr{U_zz var[z]}`, where
`tr{U_zz var[z]} = E[(z − E z)′U_zz(z − E z)]` (with `z = (x̃, ξ)` and `E ξ = 0` this is
`Ū + U_x E[x̃] + ½ tr{U_xx var x} + tr{U_xξ cov(ξ, x̃)} + ½ tr{U_ξξ var ξ}`). -/
noncomputable def printed13 (p : Ω → ℝ) (u0 : ℝ) (L : F →L[ℝ] ℝ) (B : F →L[ℝ] F →L[ℝ] ℝ)
    (z : Ω → F) : ℝ :=
  u0 + L (expect p z) + 1 / 2 * expect p (fun ω => B (z ω - expect p z) (z ω - expect p z))

/-- Woodford (2003), eq. (1.3), p. 386, CORRECTED (survey error 18): the printed formula plus
the dropped mean term `½ E[z]′U_zz E[z]` (equal to `½ E[x̃]′U_xx E[x̃]` when `E ξ = 0`). -/
noncomputable def corrected13 (p : Ω → ℝ) (u0 : ℝ) (L : F →L[ℝ] ℝ)
    (B : F →L[ℝ] F →L[ℝ] ℝ) (z : Ω → F) : ℝ :=
  printed13 p u0 L B z + 1 / 2 * B (expect p z) (expect p z)

/-- Woodford (2003), eq. (1.3), p. 386: the expectation of the quadratic approximation is
EXACTLY the corrected formula. -/
theorem expect_quadApprox_eq_corrected {p : Ω → ℝ} (hp1 : ∑ ω, p ω = 1) (u0 : ℝ)
    (L : F →L[ℝ] ℝ) (B : F →L[ℝ] F →L[ℝ] ℝ) (z : Ω → F) :
    expect p (fun ω => quadApprox u0 L B (z ω)) = corrected13 p u0 L B z := by
  rw [expect_quadApprox hp1, expect_bilin_centered hp1, corrected13, printed13]
  ring

/-- Woodford (2003), eq. (1.3), p. 386: the trace form of the variance term. For a matrix `M`
and random vectors `z` with mean `m`, `E[(z − m)′M(z − m)] = tr{M var[z]}`, where
`var[z] = E[(z − m)(z − m)′]`. -/
theorem expect_quadForm_eq_trace {n : Type*} [Fintype n] (p : Ω → ℝ) (M : Matrix n n ℝ)
    (z : Ω → n → ℝ) (m : n → ℝ) :
    ∑ ω, p ω * dotProduct (z ω - m) (M.mulVec (z ω - m)) =
      Matrix.trace (M * ∑ ω, p ω • Matrix.vecMulVec (z ω - m) (z ω - m)) := by
  have h : ∀ v : n → ℝ, dotProduct v (M.mulVec v) = Matrix.trace (M * Matrix.vecMulVec v v) :=
    fun v => by
    rw [Matrix.trace_mul_comm, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec,
      Matrix.dotProduct_mulVec, dotProduct_comm]
  simp only [h, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul]

/-! ## Order bookkeeping -/

/-- Woodford (2003), §1, p. 386 (orders of bilinear terms): if `f = O(g)` and `h = O(k)` then
`B(f, h) = O(g k)` for a bounded bilinear form `B`. -/
theorem bilin_isBigO {α : Type*} {l : Filter α} (B : F →L[ℝ] F →L[ℝ] ℝ) {f h : α → F}
    {g k : α → ℝ} (hf : f =O[l] g) (hh : h =O[l] k) :
    (fun a => B (f a) (h a)) =O[l] (fun a => g a * k a) := by
  have h1 : (fun a => B (f a) (h a)) =O[l] (fun a => ‖f a‖ * ‖h a‖) := by
    refine IsBigO.of_bound ‖B‖ (Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs (‖f a‖ * ‖h a‖), abs_of_nonneg (by positivity), ← mul_assoc]
    exact B.le_opNorm₂ (f a) (h a)
  exact h1.trans (hf.norm_left.mul hh.norm_left)

/-- Woodford (2003), eq. (1.8), p. 389: if `c(a) = O(g)` (a family of linear functionals, e.g.
`U_x(x̄; Φ) = O(Φ)`) and `v(a) = O(k)` (e.g. `E[x̃ − x̃⁰] = O(2)`), then `c(a) v(a) = O(g k)`. -/
theorem clm_apply_isBigO {α : Type*} {l : Filter α} {c : α → F →L[ℝ] ℝ} {v : α → F}
    {g k : α → ℝ} (hc : c =O[l] g) (hv : v =O[l] k) :
    (fun a => c a (v a)) =O[l] (fun a => g a * k a) := by
  have h1 : (fun a => c a (v a)) =O[l] (fun a => ‖c a‖ * ‖v a‖) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs (‖c a‖ * ‖v a‖), abs_of_nonneg (by positivity), one_mul]
    exact (c a).le_opNorm (v a)
  exact h1.trans (hc.norm_left.mul hv.norm_left)

/-- Woodford (2003), (1.8), p. 389: `U_x E[x̃ − x̃⁰] = O(‖Φ, ϕ, ξ‖³)` when `U_x = O(‖Φ‖)` and
`E[x̃ − x̃⁰] = O(‖ϕ, ξ‖²)` (sizes dominated by `s`). -/
theorem ux_mul_isBigO {α : Type*} {l : Filter α} {s : α → ℝ} {c : α → F →L[ℝ] ℝ}
    {v : α → F} (hc : c =O[l] s) (hv : v =O[l] (fun a => s a ^ 2)) :
    (fun a => c a (v a)) =O[l] (fun a => s a ^ 3) :=
  (clm_apply_isBigO hc hv).congr_right fun a => by ring

/-- Woodford (2003), (1.7), p. 389: for a differentiable family `g` (e.g. `Φ ↦ U_x(x̄; Φ)`),
`g(Φ) = O(Φ)` as `Φ → 0` if and only if `g(0) = 0`. So in a smooth one-parameter family the
condition (1.7) is exactly the vanishing of the gradient in the undistorted economy. -/
theorem isBigO_id_iff_eq_zero {P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {g : P → G} {D : P →L[ℝ] G}
    (hg : HasFDerivAt g D 0) : g =O[𝓝 0] (fun Φ => Φ) ↔ g 0 = 0 := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := h.bound
    simpa using hc.self_of_nhds
  · intro h0
    refine hg.isBigO_sub.congr (fun Φ => by simp [h0]) (fun Φ => by simp)

/-- Woodford (2003), (1.7), p. 389: for `C²` welfare `U(Φ, x)` depending on structural
parameters `Φ`, `U_x(x̄; Φ) = O(Φ)` if and only if `U_x(x̄; 0) = 0`. -/
theorem ux_isBigO_iff {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] {U : P × X → ℝ} (hU : ContDiff ℝ 2 U) (xbar : X) :
    (fun Φ : P => (fderiv ℝ U (Φ, xbar)).comp (ContinuousLinearMap.inr ℝ P X)) =O[𝓝 0]
      (fun Φ => Φ) ↔ (fderiv ℝ U ((0 : P), xbar)).comp (ContinuousLinearMap.inr ℝ P X) = 0 := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ U) := hU.fderiv_right (by norm_num)
  have hd : DifferentiableAt ℝ
      (fun Φ : P => (fderiv ℝ U (Φ, xbar)).comp (ContinuousLinearMap.inr ℝ P X)) 0 := by
    have hc : DifferentiableAt ℝ (fun Φ : P => fderiv ℝ U (Φ, xbar)) 0 :=
      (h1.differentiable (by norm_num) _).comp (0 : P)
        (differentiableAt_id.prodMk (differentiableAt_const xbar))
    exact hc.clm_comp (differentiableAt_const _)
  exact isBigO_id_iff_eq_zero hd.hasFDerivAt

/-! ## The expected Taylor remainder -/

/-- Woodford (2003), eqs. (1.2)–(1.3), pp. 385–386: for `C³` welfare and random deviations
`z = (x̃, ξ)` of size `O(s)` in every state, `E[U(z̄ + z)] − E[Ū + U_z z + ½ z′U_zz z]` is
`O(s³)`. -/
theorem expect_taylor_remainder {α : Type*} {l : Filter α} {s : α → ℝ} (p : Ω → ℝ)
    {U : F → ℝ} (hU : ContDiff ℝ 3 U) (zbar : F) (hs : Tendsto s l (𝓝 0))
    {z : α → Ω → F} (hz : ∀ ω, (fun a => z a ω) =O[l] s) :
    (fun a => expect p (fun ω => U (zbar + z a ω)) - expect p (fun ω => quadApprox (U zbar)
      (fderiv ℝ U zbar) (fderiv ℝ (fderiv ℝ U) zbar) (z a ω))) =O[l] (fun a => s a ^ 3) := by
  have h : ∀ ω, (fun a => U (zbar + z a ω) - quadApprox (U zbar) (fderiv ℝ U zbar)
      (fderiv ℝ (fderiv ℝ U) zbar) (z a ω)) =O[l] (fun a => s a ^ 3) := fun ω =>
    ((taylor2_multivar_isBigO_of_contDiff hU zbar).comp_tendsto
      ((hz ω).trans_tendsto hs)).trans ((hz ω).norm_left.pow 3)
  refine (isBigO_expect p h).congr_left fun a => ?_
  rw [expect_sub]

/-- Woodford (2003), eqs. (1.2)–(1.3), pp. 385–386, under `C²` only: the expected Taylor
remainder is `O(s²)` (in fact `o(s²)`). -/
theorem expect_taylor_remainder_two {α : Type*} {l : Filter α} {s : α → ℝ} (p : Ω → ℝ)
    {U : F → ℝ} (hU : ContDiff ℝ 2 U) (zbar : F) (hs : Tendsto s l (𝓝 0))
    {z : α → Ω → F} (hz : ∀ ω, (fun a => z a ω) =O[l] s) :
    (fun a => expect p (fun ω => U (zbar + z a ω)) - expect p (fun ω => quadApprox (U zbar)
      (fderiv ℝ U zbar) (fderiv ℝ (fderiv ℝ U) zbar) (z a ω))) =O[l] (fun a => s a ^ 2) := by
  have h : ∀ ω, (fun a => U (zbar + z a ω) - quadApprox (U zbar) (fderiv ℝ U zbar)
      (fderiv ℝ (fderiv ℝ U) zbar) (z a ω)) =O[l] (fun a => s a ^ 2) := fun ω =>
    ((taylor2_multivar_isLittleO_of_contDiff_two hU zbar).isBigO.comp_tendsto
      ((hz ω).trans_tendsto hs)).trans ((hz ω).norm_left.pow 2)
  refine (isBigO_expect p h).congr_left fun a => ?_
  rw [expect_sub]

/-- Woodford (2003), eq. (1.3), p. 386, CORRECTED (survey error 18): for `C³` welfare,
`E[U] = Ū + U_z E[z] + ½ tr{U_zz var z} + ½ E[z]′U_zz E[z] + O(s³)`. -/
theorem expected_utility_corrected {α : Type*} {l : Filter α} {s : α → ℝ} {p : Ω → ℝ}
    (hp1 : ∑ ω, p ω = 1) {U : F → ℝ} (hU : ContDiff ℝ 3 U) (zbar : F) (hs : Tendsto s l (𝓝 0))
    {z : α → Ω → F} (hz : ∀ ω, (fun a => z a ω) =O[l] s) :
    (fun a => expect p (fun ω => U (zbar + z a ω)) - corrected13 p (U zbar) (fderiv ℝ U zbar)
      (fderiv ℝ (fderiv ℝ U) zbar) (z a)) =O[l] (fun a => s a ^ 3) := by
  refine (expect_taylor_remainder p hU zbar hs hz).congr_left fun a => ?_
  rw [expect_quadApprox_eq_corrected hp1]

/-! ## The counterexample economy: `U(x, ξ) = x²`, `x̃ = x̃⁰ = ϕ` deterministic -/

/-- The counterexample welfare function `U(x, ξ) = x · x` on `ℝ × ℝ` (used against the printed
(1.3), footnote 7, `U⁽¹⁾` and `V⁽¹⁾`; Woodford (2003), §1, pp. 386–391). -/
def cexU (z : ℝ × ℝ) : ℝ := z.1 * z.1

/-- Woodford (2003), §1, p. 386: the counterexample welfare function is smooth. -/
theorem cexU_contDiff : ContDiff ℝ 3 cexU := by
  unfold cexU
  fun_prop

/-- Woodford (2003), §1, p. 386: the gradient of the counterexample welfare function vanishes at
the expansion point `(x̄, 0) = (0, 0)` (so condition (1.6) even holds). -/
theorem cexU_fderiv : fderiv ℝ cexU 0 = 0 := by
  have h : HasFDerivAt cexU ((0 : ℝ × ℝ).1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (0 : ℝ × ℝ).1 • ContinuousLinearMap.fst ℝ ℝ ℝ) 0 :=
    (hasFDerivAt_fst (p := (0 : ℝ × ℝ)) (𝕜 := ℝ)).mul (hasFDerivAt_fst (p := (0 : ℝ × ℝ)))
  rw [h.fderiv]
  simp

/-- Woodford (2003), eq. (1.3), p. 386 (survey error 18, counterexample): for
`U(x, ξ) = x²` and the deterministic deviation `x̃ = ϕ` (`ξ = 0`), `E[U] = ϕ²` while the printed
formula gives `0`; the error `ϕ²` is second order, not `O(ϕ³)`. -/
theorem printed13_false :
    ¬ (fun a : ℝ => expect (fun _ : Unit => (1 : ℝ)) (fun _ => cexU (0 + (a, 0))) -
      printed13 (fun _ : Unit => (1 : ℝ)) (cexU 0) (fderiv ℝ cexU 0) (fderiv ℝ (fderiv ℝ cexU) 0)
        (fun _ => (a, 0))) =O[𝓝 0] (fun a => a ^ 3) := by
  intro h
  refine sq_not_isBigO_cube (h.congr_left fun a => ?_)
  simp [expect, printed13, cexU, cexU_fderiv]
  ring

/-- Woodford (2003), eq. (1.3), p. 386: in the same economy the corrected formula is exact
(`E[U] − corrected = 0`). -/
theorem corrected13_cex_exact (a : ℝ) :
    expect (fun _ : Unit => (1 : ℝ)) (fun _ => cexU (0 + (a, 0))) -
      corrected13 (fun _ : Unit => (1 : ℝ)) (cexU 0) (fderiv ℝ cexU 0)
        (fderiv ℝ (fderiv ℝ cexU) 0) (fun _ => (a, 0)) = 0 := by
  have h2 : fderiv ℝ (fderiv ℝ cexU) 0 (a, 0) (a, 0) = 2 * (a * a) := by
    have hd : fderiv ℝ cexU = fun z : ℝ × ℝ =>
        z.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + z.1 • ContinuousLinearMap.fst ℝ ℝ ℝ := by
      funext z
      have h : HasFDerivAt cexU (z.1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
          z.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) z :=
        (hasFDerivAt_fst (p := z) (𝕜 := ℝ)).mul (hasFDerivAt_fst (p := z))
      exact h.fderiv
    have hdd : HasFDerivAt (fderiv ℝ cexU)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) +
          (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ)) 0 := by
      rw [hd]
      have h1 : HasFDerivAt (fun z : ℝ × ℝ => z.1 • ContinuousLinearMap.fst ℝ ℝ ℝ)
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ)) 0 :=
        (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.smul_const (ContinuousLinearMap.fst ℝ ℝ ℝ)
      exact h1.add h1
    rw [hdd.fderiv]
    simp
    ring
  simp [expect, corrected13, printed13, cexU, cexU_fderiv, h2]

/-! ## The linear approximation (1.1), `U⁽⁰⁾` and `U⁽¹⁾` -/

variable {X Ξ : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]

/-- Woodford (2003), eq. (1.3), p. 386: the expectation of a pair is the pair of expectations. -/
theorem expect_prod (p : Ω → ℝ) (f : Ω → X) (g : Ω → Ξ) :
    expect p (fun ω => (f ω, g ω)) = (expect p f, expect p g) := by
  ext <;> simp [expect, Prod.fst_sum, Prod.snd_sum]

/-- Woodford (2003), eq. (1.4), p. 386: the linear approximation `x̃⁽¹⁾ = x̃⁰ + A ξ`, paired
with the disturbance: `z⁽¹⁾ = (x̃⁰ + A ξ, ξ)`. -/
def linSol (x0 : X) (A : Ξ →L[ℝ] X) (ξ : Ω → Ξ) (ω : Ω) : X × Ξ := (x0 + A (ξ ω), ξ ω)

/-- Woodford (2003), footnote 7, p. 386: the zeroth-order criterion `U⁽⁰⁾ = Ū + U_x x̃⁰`. -/
def U0 (u0 : ℝ) (L : X × Ξ →L[ℝ] ℝ) (x0 : X) : ℝ := u0 + L (x0, 0)

/-- Woodford (2003), p. 386, CORRECTED: `U⁽¹⁾` is the expected quadratic approximation evaluated
at the linear solution, `E[Ū + U_z z⁽¹⁾ + ½ z⁽¹⁾′U_zz z⁽¹⁾]`. -/
noncomputable def U1 (p : Ω → ℝ) (u0 : ℝ) (L : X × Ξ →L[ℝ] ℝ)
    (B : X × Ξ →L[ℝ] X × Ξ →L[ℝ] ℝ) (x0 : X) (A : Ξ →L[ℝ] X) (ξ : Ω → Ξ) : ℝ :=
  expect p (fun ω => quadApprox u0 L B (linSol x0 A ξ ω))

/-- Woodford (2003), p. 386, AS PRINTED:
`U⁽¹⁾ = Ū + U_x x̃⁰ + ½ tr{U_xx AΣA′} + tr{U_xξ ΣA′} + ½ tr{U_ξξ Σ}`, i.e.
`Ū + U_x x̃⁰ + ½ E[(Aξ, ξ)′U_zz(Aξ, ξ)]`. -/
noncomputable def U1printed (p : Ω → ℝ) (u0 : ℝ) (L : X × Ξ →L[ℝ] ℝ)
    (B : X × Ξ →L[ℝ] X × Ξ →L[ℝ] ℝ) (x0 : X) (A : Ξ →L[ℝ] X) (ξ : Ω → Ξ) : ℝ :=
  u0 + L (x0, 0) + 1 / 2 * expect p (fun ω => B (A (ξ ω), ξ ω) (A (ξ ω), ξ ω))

/-- Woodford (2003), p. 391, AS PRINTED:
`V⁽¹⁾ = Ū + tr{V_xx AΣA′} + 2 tr{V_xξ ΣA′} + tr{V_ξξ Σ} = Ū + E[(Aξ, ξ)′V(Aξ, ξ)]`. -/
noncomputable def V1printed (p : Ω → ℝ) (u0 : ℝ) (V : X × Ξ →L[ℝ] X × Ξ →L[ℝ] ℝ)
    (A : Ξ →L[ℝ] X) (ξ : Ω → Ξ) : ℝ :=
  u0 + expect p (fun ω => V (A (ξ ω), ξ ω) (A (ξ ω), ξ ω))

/-- Woodford (2003), eq. (1.4), p. 386: with `E ξ = 0`, the linear solution has mean `(x̃⁰, 0)`. -/
theorem expect_linSol {p : Ω → ℝ} (hp1 : ∑ ω, p ω = 1) (x0 : X) (A : Ξ →L[ℝ] X)
    {ξ : Ω → Ξ} (hEξ : expect p ξ = 0) : expect p (linSol x0 A ξ) = (x0, 0) := by
  have e : linSol x0 A ξ = fun ω => (x0 + A (ξ ω), ξ ω) := rfl
  rw [e, expect_prod, expect_add, expect_const hp1, ← OneParamTaylor.map_expect, hEξ, map_zero,
    add_zero]

/-- Woodford (2003), p. 386 (survey error 18): the corrected `U⁽¹⁾` equals the printed one plus
the dropped term `½ x̃⁰′U_xx x̃⁰`, which is `O(ϕ²)`. -/
theorem U1_eq_printed_add {p : Ω → ℝ} (hp1 : ∑ ω, p ω = 1) (u0 : ℝ) (L : X × Ξ →L[ℝ] ℝ)
    (B : X × Ξ →L[ℝ] X × Ξ →L[ℝ] ℝ) (x0 : X) (A : Ξ →L[ℝ] X) {ξ : Ω → Ξ}
    (hEξ : expect p ξ = 0) :
    U1 p u0 L B x0 A ξ = U1printed p u0 L B x0 A ξ + 1 / 2 * B (x0, 0) (x0, 0) := by
  unfold U1
  rw [expect_quadApprox_eq_corrected hp1]
  unfold corrected13 printed13 U1printed
  rw [expect_linSol hp1 x0 A hEξ]
  have e : ∀ ω, linSol x0 A ξ ω - (x0, 0) = (A (ξ ω), ξ ω) := fun ω => by simp [linSol]
  simp only [e]

omit [Fintype Ω] in
/-- Woodford (2003), eq. (1.1), p. 385: the order bounds implied by the linear approximation
`x̃ = x̃⁰ + A ξ + O(ϕ, ξ²)` with `x̃⁰ = O(ϕ)`, `ξ = O(ξ)`: the linear solution `z⁽¹⁾` and the true
`z = (x̃, ξ)` are `O(s)`, and their difference `d = z − z⁽¹⁾` is `O(s²)`. -/
theorem firstOrder_bounds {α : Type*} {l : Filter α} {s : α → ℝ} (hs : Tendsto s l (𝓝 0))
    {xt : α → Ω → X} {ξ : α → Ω → Ξ} {x0 : α → X} {A : Ξ →L[ℝ] X}
    (hξ : ∀ ω, (fun a => ξ a ω) =O[l] s) (hx0 : x0 =O[l] s)
    (h11 : ∀ ω, (fun a => xt a ω - (x0 a + A (ξ a ω))) =O[l] (fun a => s a ^ 2)) (ω : Ω) :
    (fun a => linSol (x0 a) A (ξ a) ω) =O[l] s ∧ (fun a => (xt a ω, ξ a ω)) =O[l] s ∧
      (fun a => (xt a ω - (x0 a + A (ξ a ω)), (0 : Ξ))) =O[l] (fun a => s a ^ 2) := by
  have hz1 : (fun a => linSol (x0 a) A (ξ a) ω) =O[l] s :=
    (hx0.add ((A.isBigO_comp _ _).trans (hξ ω))).prod_left (hξ ω)
  have hd : (fun a => (xt a ω - (x0 a + A (ξ a ω)), (0 : Ξ))) =O[l] (fun a => s a ^ 2) :=
    (h11 ω).prod_left (isBigO_zero _ _)
  have hs2 : (fun a => s a ^ 2) =O[l] s := pow_succ_isBigO_self hs 1
  refine ⟨hz1, (hz1.add (hd.trans hs2)).congr_left fun a => ?_, hd⟩
  ext <;> simp [linSol]

/-- Woodford (2003), (1.3)–(1.4), p. 386 (algebra): the quadratic approximation at
`z⁽¹⁾ + d` is that at `z⁽¹⁾` plus `L d + ½ (B(d, z⁽¹⁾ + d) + B(z⁽¹⁾, d))`. -/
theorem quadApprox_add (u0 : ℝ) (L : F →L[ℝ] ℝ) (B : F →L[ℝ] F →L[ℝ] ℝ) (z1 d : F) :
    quadApprox u0 L B (z1 + d) =
      quadApprox u0 L B z1 + L d + 1 / 2 * (B d (z1 + d) + B z1 d) := by
  simp only [quadApprox, map_add, add_apply]
  ring

/-- Woodford (2003), (1.1), p. 385: with `E ξ = 0`,
`E[(x̃ − x̃⁰ − A ξ, 0)] = (E[x̃ − x̃⁰], 0)`. -/
theorem expect_resid {p : Ω → ℝ} (hp1 : ∑ ω, p ω = 1) (xt : Ω → X) (x0 : X) (A : Ξ →L[ℝ] X)
    {ξ : Ω → Ξ} (hEξ : expect p ξ = 0) :
    expect p (fun ω => (xt ω - (x0 + A (ξ ω)), (0 : Ξ))) =
      (expect p (fun ω => xt ω - x0), 0) := by
  have e : (fun ω => xt ω - (x0 + A (ξ ω))) = fun ω => (xt ω - x0) - A (ξ ω) := by
    funext ω; abel
  rw [expect_prod, e, expect_sub, ← OneParamTaylor.map_expect, hEξ, map_zero, sub_zero,
    expect_const hp1]

/-- Woodford (2003), p. 386: `E[U] = U⁽¹⁾ + U_x E[x̃ − x̃⁰] + O(‖ϕ, ξ‖³)` for `C³` welfare,
with the CORRECTED `U⁽¹⁾` (the expected quadratic approximation at the linear solution (1.4)).
Hypotheses: (1.1) `x̃ = x̃⁰ + A ξ + O(s²)`, `x̃⁰ = O(s)`, `ξ = O(s)`, `E ξ = 0`. -/
theorem expected_utility_eq_U1_add {α : Type*} {l : Filter α} {s : α → ℝ} {p : Ω → ℝ}
    (hp1 : ∑ ω, p ω = 1) {U : X × Ξ → ℝ} (hU : ContDiff ℝ 3 U) (xbar : X)
    (hs : Tendsto s l (𝓝 0)) {xt : α → Ω → X} {ξ : α → Ω → Ξ} {x0 : α → X} {A : Ξ →L[ℝ] X}
    (hEξ : ∀ a, expect p (ξ a) = 0) (hξ : ∀ ω, (fun a => ξ a ω) =O[l] s) (hx0 : x0 =O[l] s)
    (h11 : ∀ ω, (fun a => xt a ω - (x0 a + A (ξ a ω))) =O[l] (fun a => s a ^ 2)) :
    (fun a => expect p (fun ω => U ((xbar, 0) + (xt a ω, ξ a ω))) -
      (U1 p (U (xbar, 0)) (fderiv ℝ U (xbar, 0)) (fderiv ℝ (fderiv ℝ U) (xbar, 0)) (x0 a) A (ξ a) +
        (fderiv ℝ U (xbar, 0)).comp (ContinuousLinearMap.inl ℝ X Ξ)
          (expect p (fun ω => xt a ω - x0 a)))) =O[l] (fun a => s a ^ 3) := by
  set L := fderiv ℝ U (xbar, 0)
  set B := fderiv ℝ (fderiv ℝ U) (xbar, 0)
  have hb := firstOrder_bounds hs hξ hx0 h11
  have T := expect_taylor_remainder p hU (xbar, 0) hs (fun ω => (hb ω).2.1)
  have R : ∀ ω, (fun a => 1 / 2 * (B (xt a ω - (x0 a + A (ξ a ω)), (0 : Ξ)) (xt a ω, ξ a ω) +
      B (linSol (x0 a) A (ξ a) ω) (xt a ω - (x0 a + A (ξ a ω)), (0 : Ξ)))) =O[l]
      (fun a => s a ^ 3) := fun ω =>
    (((bilin_isBigO B (hb ω).2.2 (hb ω).2.1).congr_right fun a => by ring).add
      ((bilin_isBigO B (hb ω).1 (hb ω).2.2).congr_right fun a => by ring)).const_mul_left _
  refine (T.add (isBigO_expect p R)).congr_left fun a => ?_
  have hz : ∀ ω, (xt a ω, ξ a ω) =
      linSol (x0 a) A (ξ a) ω + (xt a ω - (x0 a + A (ξ a ω)), (0 : Ξ)) := fun ω => by
    ext <;> simp [linSol]
  have hq : expect p (fun ω => quadApprox (U (xbar, 0)) L B (xt a ω, ξ a ω)) =
      U1 p (U (xbar, 0)) L B (x0 a) A (ξ a) +
        L (expect p (fun ω => (xt a ω - (x0 a + A (ξ a ω)), (0 : Ξ)))) +
        expect p (fun ω => 1 / 2 * (B (xt a ω - (x0 a + A (ξ a ω)), (0 : Ξ)) (xt a ω, ξ a ω) +
          B (linSol (x0 a) A (ξ a) ω) (xt a ω - (x0 a + A (ξ a ω)), (0 : Ξ)))) := by
    have e : (fun ω => quadApprox (U (xbar, 0)) L B (xt a ω, ξ a ω)) = fun ω =>
        (quadApprox (U (xbar, 0)) L B (linSol (x0 a) A (ξ a) ω) +
          L (xt a ω - (x0 a + A (ξ a ω)), (0 : Ξ))) +
        1 / 2 * (B (xt a ω - (x0 a + A (ξ a ω)), (0 : Ξ)) (xt a ω, ξ a ω) +
          B (linSol (x0 a) A (ξ a) ω) (xt a ω - (x0 a + A (ξ a ω)), (0 : Ξ))) := by
      funext ω
      rw [hz ω, quadApprox_add, ← hz ω]
    rw [e, expect_add, expect_add, ← OneParamTaylor.map_expect]
    rfl
  rw [hq, expect_resid hp1 _ _ A (hEξ a)]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  ring

/-- Woodford (2003), eqs. (1.5)–(1.6), pp. 386–387: if `U_x(x̄; 0) = 0` then
`E[U] = U⁽¹⁾ + O(‖ϕ, ξ‖³)`: the linear solution suffices for a second-order approximation of
expected welfare. -/
theorem expected_utility_eq_U1_of_ux_eq_zero {α : Type*} {l : Filter α} {s : α → ℝ}
    {p : Ω → ℝ} (hp1 : ∑ ω, p ω = 1) {U : X × Ξ → ℝ} (hU : ContDiff ℝ 3 U) (xbar : X)
    (hUx : (fderiv ℝ U (xbar, 0)).comp (ContinuousLinearMap.inl ℝ X Ξ) = 0)
    (hs : Tendsto s l (𝓝 0)) {xt : α → Ω → X} {ξ : α → Ω → Ξ} {x0 : α → X} {A : Ξ →L[ℝ] X}
    (hEξ : ∀ a, expect p (ξ a) = 0) (hξ : ∀ ω, (fun a => ξ a ω) =O[l] s) (hx0 : x0 =O[l] s)
    (h11 : ∀ ω, (fun a => xt a ω - (x0 a + A (ξ a ω))) =O[l] (fun a => s a ^ 2)) :
    (fun a => expect p (fun ω => U ((xbar, 0) + (xt a ω, ξ a ω))) -
      U1 p (U (xbar, 0)) (fderiv ℝ U (xbar, 0)) (fderiv ℝ (fderiv ℝ U) (xbar, 0)) (x0 a) A (ξ a))
      =O[l] (fun a => s a ^ 3) := by
  refine (expected_utility_eq_U1_add hp1 hU xbar hs hEξ hξ hx0 h11).congr_left fun a => ?_
  rw [hUx]
  simp

/-- Woodford (2003), §1, p. 387 (welfare ranking): if each policy's expected welfare equals its
approximation up to `O(s³)` (e.g. `U⁽¹⁾` under (1.6)) and the approximations differ by at least
`c s²` with `c > 0`, then the first policy is strictly better for all small enough
disturbances. -/
theorem welfare_ranking_of_approx {α : Type*} {l : Filter α} {s WA WB VA VB : α → ℝ} {c : ℝ}
    (hs : Tendsto s l (𝓝 0)) (hc : 0 < c) (hne : ∀ᶠ a in l, s a ≠ 0)
    (hA : (fun a => WA a - VA a) =O[l] (fun a => s a ^ 3))
    (hB : (fun a => WB a - VB a) =O[l] (fun a => s a ^ 3))
    (hgap : ∀ᶠ a in l, c * s a ^ 2 ≤ VA a - VB a) : ∀ᶠ a in l, WB a < WA a :=
  eventually_lt_of_quadratic_gap (q := fun a => VA a - VB a) hs hc hgap hne
    ((hA.sub hB).congr_left fun a => by ring)

/-- Woodford (2003), (1.7)–(1.8), p. 389 (joint expansion in the distortion parameters): let the
endogenous vector be `x = (Φ, y)`, where the structural parameters `Φ` (deterministic, `O(s)`)
are carried along exactly by the linear solution. If `U_y(x̄; 0) = 0` — equivalently
`U_y(x̄; Φ) = O(Φ)` by `ux_isBigO_iff` — then `E[U] = U⁽¹⁾ + O(‖Φ, ϕ, ξ‖³)`, where `U⁽¹⁾`
(computed jointly in `(Φ, y, ξ)`) involves only the linear solution `y⁰ + A_y ξ`. -/
theorem expected_utility_eq_U1_of_ux_param {P Y : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {α : Type*} {l : Filter α}
    {s : α → ℝ} {p : Ω → ℝ} (hp1 : ∑ ω, p ω = 1) {U : (P × Y) × Ξ → ℝ} (hU : ContDiff ℝ 3 U)
    (ybar : Y)
    (hUy : ((fderiv ℝ U (((0 : P), ybar), 0)).comp (ContinuousLinearMap.inl ℝ (P × Y) Ξ)).comp
      (ContinuousLinearMap.inr ℝ P Y) = 0)
    (hs : Tendsto s l (𝓝 0)) {Φ : α → P} {y : α → Ω → Y} {ξ : α → Ω → Ξ} {y0 : α → Y}
    {Ay : Ξ →L[ℝ] Y} (hEξ : ∀ a, expect p (ξ a) = 0) (hξ : ∀ ω, (fun a => ξ a ω) =O[l] s)
    (hΦ : Φ =O[l] s) (hy0 : y0 =O[l] s)
    (h11 : ∀ ω, (fun a => y a ω - (y0 a + Ay (ξ a ω))) =O[l] (fun a => s a ^ 2)) :
    (fun a => expect p (fun ω => U ((((0 : P), ybar), 0) + ((Φ a, y a ω), ξ a ω))) -
      U1 p (U (((0 : P), ybar), 0)) (fderiv ℝ U (((0 : P), ybar), 0))
        (fderiv ℝ (fderiv ℝ U) (((0 : P), ybar), 0)) (Φ a, y0 a)
        ((ContinuousLinearMap.inr ℝ P Y).comp Ay) (ξ a)) =O[l] (fun a => s a ^ 3) := by
  have h11' : ∀ ω, (fun a => (Φ a, y a ω) - ((Φ a, y0 a) +
      ((ContinuousLinearMap.inr ℝ P Y).comp Ay) (ξ a ω))) =O[l] (fun a => s a ^ 2) := fun ω =>
    ((isBigO_zero _ _).prod_left (h11 ω)).congr_left fun a => by ext <;> simp
  have key := expected_utility_eq_U1_add (xt := fun a ω => (Φ a, y a ω))
    (x0 := fun a => (Φ a, y0 a)) hp1 hU ((0 : P), ybar) hs hEξ hξ (hΦ.prod_left hy0) h11'
  refine key.congr_left fun a => ?_
  have e : expect p (fun ω => (Φ a, y a ω) - (Φ a, y0 a)) =
      ContinuousLinearMap.inr ℝ P Y (expect p (fun ω => y a ω - y0 a)) := by
    have e1 : (fun ω => (Φ a, y a ω) - (Φ a, y0 a)) = fun ω => ((0 : P), y a ω - y0 a) := by
      funext ω; ext <;> simp
    rw [e1, expect_prod, show expect p (fun _ => (0 : P)) = 0 by simp [expect]]
    simp only [ContinuousLinearMap.inr_apply]
  have h0 : (fderiv ℝ U (((0 : P), ybar), 0)).comp (ContinuousLinearMap.inl ℝ (P × Y) Ξ)
      (expect p (fun ω => (Φ a, y a ω) - (Φ a, y0 a))) = 0 := by
    rw [e, ← ContinuousLinearMap.comp_apply, hUy, zero_apply]
  rw [h0, add_zero]

/-! ## Footnote 7 -/

/-- Woodford (2003), footnote 7, p. 386, CORRECTED: for `C²` welfare and (1.1),
`E[U] = U⁽⁰⁾ + O(‖ϕ, ξ‖²)` with `U⁽⁰⁾ = Ū + U_x x̃⁰` — the residual is second order (not third
order as printed). -/
theorem expected_utility_sub_U0_isBigO_sq {α : Type*} {l : Filter α} {s : α → ℝ} {p : Ω → ℝ}
    (hp1 : ∑ ω, p ω = 1) {U : X × Ξ → ℝ} (hU : ContDiff ℝ 2 U) (xbar : X)
    (hs : Tendsto s l (𝓝 0)) {xt : α → Ω → X} {ξ : α → Ω → Ξ} {x0 : α → X} {A : Ξ →L[ℝ] X}
    (hEξ : ∀ a, expect p (ξ a) = 0) (hξ : ∀ ω, (fun a => ξ a ω) =O[l] s) (hx0 : x0 =O[l] s)
    (h11 : ∀ ω, (fun a => xt a ω - (x0 a + A (ξ a ω))) =O[l] (fun a => s a ^ 2)) :
    (fun a => expect p (fun ω => U ((xbar, 0) + (xt a ω, ξ a ω))) -
      U0 (U (xbar, 0)) (fderiv ℝ U (xbar, 0)) (x0 a)) =O[l] (fun a => s a ^ 2) := by
  set L := fderiv ℝ U (xbar, 0)
  set B := fderiv ℝ (fderiv ℝ U) (xbar, 0)
  have hb := firstOrder_bounds hs hξ hx0 h11
  have T := expect_taylor_remainder_two p hU (xbar, 0) hs (fun ω => (hb ω).2.1)
  have R1 : (fun a => L (expect p (fun ω => (xt a ω - (x0 a + A (ξ a ω)), (0 : Ξ))))) =O[l]
      (fun a => s a ^ 2) :=
    (L.isBigO_comp _ _).trans (isBigO_expect p fun ω => (hb ω).2.2)
  have R2 : (fun a => 1 / 2 * expect p (fun ω => B (xt a ω, ξ a ω) (xt a ω, ξ a ω))) =O[l]
      (fun a => s a ^ 2) :=
    (isBigO_expect p fun ω => (bilin_isBigO B (hb ω).2.1 (hb ω).2.1).congr_right
      fun a => by ring).const_mul_left _
  refine ((T.add R1).add R2).congr_left fun a => ?_
  rw [expect_quadApprox hp1, expect_resid hp1 _ _ A (hEξ a), expect_prod, hEξ a, expect_sub,
    expect_const hp1]
  have e : L (expect p (xt a), 0) = L (x0 a, 0) + L (expect p (xt a) - x0 a, 0) := by
    rw [← map_add]
    congr 1
    ext <;> simp
  rw [e, U0]
  ring

/-- Woodford (2003), footnote 7, p. 386 (counterexample): in the economy `U(x, ξ) = x²`,
`x̃ = x̃⁰ = ϕ`, `ξ = 0` (which satisfies (1.1) exactly, see `cex_firstOrder`),
`E[U] − U⁽⁰⁾ = ϕ²`, which is NOT `O(‖ϕ, ξ‖³)`. -/
theorem fn7_false :
    ¬ (fun a : ℝ => expect (fun _ : Unit => (1 : ℝ)) (fun _ => cexU ((0, 0) + (a, 0))) -
      U0 (cexU (0, 0)) (fderiv ℝ cexU (0, 0)) a) =O[𝓝 0] (fun a => a ^ 3) := by
  intro h
  refine sq_not_isBigO_cube (h.congr_left fun a => ?_)
  have h0 : ((0 : ℝ), (0 : ℝ)) = 0 := rfl
  simp [expect, U0, cexU, h0, cexU_fderiv]
  ring

/-- Woodford (2003), (1.1), p. 385: the counterexample data `x̃ = x̃⁰ = ϕ`, `A = 0`, `ξ = 0`
(one state, probability one) satisfy every hypothesis of the positive theorems. -/
theorem cex_firstOrder :
    (∀ _a : ℝ, expect (fun _ : Unit => (1 : ℝ)) (fun _ => (0 : ℝ)) = 0) ∧
      (∀ _ω : Unit, (fun _a : ℝ => (0 : ℝ)) =O[𝓝 0] (fun a : ℝ => a)) ∧
      ((fun a : ℝ => a) =O[𝓝 0] (fun a : ℝ => a)) ∧
      (∀ _ω : Unit, (fun a : ℝ => a - (a + (0 : ℝ →L[ℝ] ℝ) 0)) =O[𝓝 0] (fun a : ℝ => a ^ 2)) :=
  ⟨fun _ => by simp [expect], fun _ => isBigO_zero _ _, isBigO_refl _ _,
    fun _ => (isBigO_zero _ _).congr_left fun a => by simp⟩

/-- Woodford (2003), p. 386 (survey error 18, counterexample to the printed `U⁽¹⁾`): in the same
economy `E[U] − (U⁽¹⁾_printed + U_x E[x̃ − x̃⁰]) = ϕ²`, not `O(ϕ³)`; the corrected `U⁽¹⁾` adds
exactly the missing `½ x̃⁰′U_xx x̃⁰ = ϕ²` (`U1_eq_printed_add`). -/
theorem U1printed_false :
    ¬ (fun a : ℝ => expect (fun _ : Unit => (1 : ℝ)) (fun _ => cexU ((0, 0) + (a, 0))) -
      (U1printed (fun _ : Unit => (1 : ℝ)) (cexU (0, 0)) (fderiv ℝ cexU (0, 0))
        (fderiv ℝ (fderiv ℝ cexU) (0, 0)) a (0 : ℝ →L[ℝ] ℝ) (fun _ => 0) +
        (fderiv ℝ cexU (0, 0)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)
          (expect (fun _ : Unit => (1 : ℝ)) (fun _ => a - a)))) =O[𝓝 0] (fun a => a ^ 3) := by
  intro h
  refine sq_not_isBigO_cube (h.congr_left fun a => ?_)
  have h0 : ((0 : ℝ), (0 : ℝ)) = 0 := rfl
  simp [expect, U1printed, cexU, h0, cexU_fderiv]
  ring

/-- Woodford (2003), (1.5), p. 386: without `U_x = 0`, `U⁽¹⁾` cannot rank policies. With
`U(x, ξ) = x` (so `U_x = 1`), `ξ = ±σ` with probability ½ each, `x̃⁰ = 0`, `A = 1`, policy A
`x̃ = ξ + ξ²` and policy B `x̃ = ξ` both satisfy (1.1) with the same `(x̃⁰, A)` — hence the same
`U⁽¹⁾` — yet `E[U_A] − E[U_B] = σ²`, a second-order welfare difference. -/
theorem U1_fails_without_ux_zero :
    (∀ σ : ℝ, expect (fun _ : Bool => (1 / 2 : ℝ))
        (fun b => (if b then σ else -σ) + (if b then σ else -σ) ^ 2) -
      expect (fun _ : Bool => (1 / 2 : ℝ)) (fun b => if b then σ else -σ) = σ ^ 2) ∧
    (∀ σ : ℝ, expect (fun _ : Bool => (1 / 2 : ℝ)) (fun b => if b then σ else -σ) = 0) ∧
    (∀ b : Bool, (fun σ : ℝ => ((if b then σ else -σ) + (if b then σ else -σ) ^ 2) -
      (0 + (if b then σ else -σ))) =O[𝓝 0] (fun σ => σ ^ 2)) ∧
    ¬ (fun σ : ℝ => expect (fun _ : Bool => (1 / 2 : ℝ))
        (fun b => (if b then σ else -σ) + (if b then σ else -σ) ^ 2) -
      expect (fun _ : Bool => (1 / 2 : ℝ)) (fun b => if b then σ else -σ)) =O[𝓝 0]
        (fun σ => σ ^ 3) := by
  have hd : ∀ σ : ℝ, expect (fun _ : Bool => (1 / 2 : ℝ))
      (fun b => (if b then σ else -σ) + (if b then σ else -σ) ^ 2) -
      expect (fun _ : Bool => (1 / 2 : ℝ)) (fun b => if b then σ else -σ) = σ ^ 2 := by
    intro σ
    simp [expect]
    ring
  refine ⟨hd, fun σ => by simp [expect], fun b => ?_, fun h =>
    sq_not_isBigO_cube (h.congr_left hd)⟩
  refine (isBigO_refl (fun σ : ℝ => σ ^ 2) _).congr_left fun σ => ?_
  cases b <;> simp

/-! ## Benigno–Woodford (1.9)–(1.10) -/

/-- Woodford (2003), (1.9)–(1.10), pp. 390–391 (Benigno–Woodford): if the structural relations
give (1.10) `U_x E[x̃] = E[z̃′W z̃] + O(s³)`, then (1.9)
`E[U] = Ū + E[z̃′V z̃] + O(s³)` with `V = ½ U_zz + W` — no linear terms. -/
theorem benigno_woodford {α : Type*} {l : Filter α} {s : α → ℝ} {p : Ω → ℝ}
    (hp1 : ∑ ω, p ω = 1) {U : X × Ξ → ℝ} (hU : ContDiff ℝ 3 U) (xbar : X)
    (hs : Tendsto s l (𝓝 0)) {xt : α → Ω → X} {ξ : α → Ω → Ξ}
    (hEξ : ∀ a, expect p (ξ a) = 0) (hz : ∀ ω, (fun a => (xt a ω, ξ a ω)) =O[l] s)
    (W : X × Ξ →L[ℝ] X × Ξ →L[ℝ] ℝ)
    (h110 : (fun a => (fderiv ℝ U (xbar, 0)).comp (ContinuousLinearMap.inl ℝ X Ξ)
      (expect p (xt a)) - expect p (fun ω => W (xt a ω, ξ a ω) (xt a ω, ξ a ω))) =O[l]
      (fun a => s a ^ 3)) :
    (fun a => expect p (fun ω => U ((xbar, 0) + (xt a ω, ξ a ω))) -
      (U (xbar, 0) + expect p (fun ω => ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ U) (xbar, 0) + W)
        (xt a ω, ξ a ω) (xt a ω, ξ a ω)))) =O[l] (fun a => s a ^ 3) := by
  have T := expect_taylor_remainder p hU (xbar, 0) hs hz
  refine (T.add h110).congr_left fun a => ?_
  rw [expect_quadApprox hp1, expect_prod, hEξ a]
  have e : (fun ω => ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ U) (xbar, 0) + W)
      (xt a ω, ξ a ω) (xt a ω, ξ a ω)) = fun ω =>
      (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ U) (xbar, 0) (xt a ω, ξ a ω) (xt a ω, ξ a ω) +
        W (xt a ω, ξ a ω) (xt a ω, ξ a ω) := by
    funext ω; simp
  rw [e, expect_add, expect_smul, smul_eq_mul]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  ring

/-- Woodford (2003), p. 391 (`V⁽¹⁾`): under (1.1) and (1.10),
`E[U] = V⁽¹⁾_printed + V_xx(x̃⁰, x̃⁰) + O(s³)` with `V = ½ U_zz + W`; the extra mean term is the
caveat on the printed `V⁽¹⁾`. -/
theorem benigno_woodford_V1 {α : Type*} {l : Filter α} {s : α → ℝ} {p : Ω → ℝ}
    (hp1 : ∑ ω, p ω = 1) {U : X × Ξ → ℝ} (hU : ContDiff ℝ 3 U) (xbar : X)
    (hs : Tendsto s l (𝓝 0)) {xt : α → Ω → X} {ξ : α → Ω → Ξ} {x0 : α → X} {A : Ξ →L[ℝ] X}
    (hEξ : ∀ a, expect p (ξ a) = 0) (hξ : ∀ ω, (fun a => ξ a ω) =O[l] s) (hx0 : x0 =O[l] s)
    (h11 : ∀ ω, (fun a => xt a ω - (x0 a + A (ξ a ω))) =O[l] (fun a => s a ^ 2))
    (W : X × Ξ →L[ℝ] X × Ξ →L[ℝ] ℝ)
    (h110 : (fun a => (fderiv ℝ U (xbar, 0)).comp (ContinuousLinearMap.inl ℝ X Ξ)
      (expect p (xt a)) - expect p (fun ω => W (xt a ω, ξ a ω) (xt a ω, ξ a ω))) =O[l]
      (fun a => s a ^ 3)) :
    (fun a => expect p (fun ω => U ((xbar, 0) + (xt a ω, ξ a ω))) -
      (V1printed p (U (xbar, 0)) ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ U) (xbar, 0) + W) A (ξ a) +
        ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ U) (xbar, 0) + W) (x0 a, 0) (x0 a, 0))) =O[l]
      (fun a => s a ^ 3) := by
  have hb := firstOrder_bounds hs hξ hx0 h11
  have BW := benigno_woodford hp1 hU xbar hs hEξ (fun ω => (hb ω).2.1) W h110
  set V := (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ U) (xbar, 0) + W
  have R : ∀ ω, (fun a => V (xt a ω - (x0 a + A (ξ a ω)), (0 : Ξ)) (xt a ω, ξ a ω) +
      V (linSol (x0 a) A (ξ a) ω) (xt a ω - (x0 a + A (ξ a ω)), (0 : Ξ))) =O[l]
      (fun a => s a ^ 3) := fun ω =>
    ((bilin_isBigO V (hb ω).2.2 (hb ω).2.1).congr_right fun a => by ring).add
      ((bilin_isBigO V (hb ω).1 (hb ω).2.2).congr_right fun a => by ring)
  refine (BW.add (isBigO_expect p R)).congr_left fun a => ?_
  have hz : ∀ ω, (xt a ω, ξ a ω) =
      linSol (x0 a) A (ξ a) ω + (xt a ω - (x0 a + A (ξ a ω)), (0 : Ξ)) := fun ω => by
    ext <;> simp [linSol]
  have hsplit : ∀ ω, V (xt a ω, ξ a ω) (xt a ω, ξ a ω) =
      V (linSol (x0 a) A (ξ a) ω) (linSol (x0 a) A (ξ a) ω) +
        (V (xt a ω - (x0 a + A (ξ a ω)), (0 : Ξ)) (xt a ω, ξ a ω) +
          V (linSol (x0 a) A (ξ a) ω) (xt a ω - (x0 a + A (ξ a ω)), (0 : Ξ))) := fun ω => by
    conv_lhs => rw [hz ω]
    conv_rhs => rw [hz ω]
    simp only [map_add, add_apply]
    ring
  have hV1 : expect p (fun ω => V (linSol (x0 a) A (ξ a) ω) (linSol (x0 a) A (ξ a) ω)) =
      V1printed p (U (xbar, 0)) V A (ξ a) - U (xbar, 0) + V (x0 a, 0) (x0 a, 0) := by
    rw [expect_bilin_centered hp1, expect_linSol hp1 _ A (hEξ a)]
    have e : ∀ ω, linSol (x0 a) A (ξ a) ω - (x0 a, 0) = (A (ξ a ω), ξ a ω) := fun ω => by
      simp [linSol]
    simp only [e, V1printed]
    ring
  rw [show (fun ω => V (xt a ω, ξ a ω) (xt a ω, ξ a ω)) = fun ω =>
      V (linSol (x0 a) A (ξ a) ω) (linSol (x0 a) A (ξ a) ω) +
        (V (xt a ω - (x0 a + A (ξ a ω)), (0 : Ξ)) (xt a ω, ξ a ω) +
          V (linSol (x0 a) A (ξ a) ω) (xt a ω - (x0 a + A (ξ a ω)), (0 : Ξ))) from
      funext hsplit, expect_add, hV1]
  ring

/-- Woodford (2003), p. 391: when policies do not move the deterministic outcome (`x̃⁰ = 0`), the
printed `V⁽¹⁾` is a valid second-order approximation: `E[U] = V⁽¹⁾ + O(s³)`. -/
theorem benigno_woodford_V1_of_x0_eq_zero {α : Type*} {l : Filter α} {s : α → ℝ}
    {p : Ω → ℝ} (hp1 : ∑ ω, p ω = 1) {U : X × Ξ → ℝ} (hU : ContDiff ℝ 3 U) (xbar : X)
    (hs : Tendsto s l (𝓝 0)) {xt : α → Ω → X} {ξ : α → Ω → Ξ} {A : Ξ →L[ℝ] X}
    (hEξ : ∀ a, expect p (ξ a) = 0) (hξ : ∀ ω, (fun a => ξ a ω) =O[l] s)
    (h11 : ∀ ω, (fun a => xt a ω - A (ξ a ω)) =O[l] (fun a => s a ^ 2))
    (W : X × Ξ →L[ℝ] X × Ξ →L[ℝ] ℝ)
    (h110 : (fun a => (fderiv ℝ U (xbar, 0)).comp (ContinuousLinearMap.inl ℝ X Ξ)
      (expect p (xt a)) - expect p (fun ω => W (xt a ω, ξ a ω) (xt a ω, ξ a ω))) =O[l]
      (fun a => s a ^ 3)) :
    (fun a => expect p (fun ω => U ((xbar, 0) + (xt a ω, ξ a ω))) -
      V1printed p (U (xbar, 0)) ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ U) (xbar, 0) + W) A (ξ a))
      =O[l] (fun a => s a ^ 3) := by
  have key := benigno_woodford_V1 (x0 := fun _ => (0 : X)) (A := A) hp1 hU xbar hs hEξ hξ
    (isBigO_zero _ _) (fun ω => (h11 ω).congr_left fun a => by simp) W h110
  refine key.congr_left fun a => ?_
  have h0 : ((0 : X), (0 : Ξ)) = 0 := rfl
  simp [h0]

/-- Woodford (2003), p. 391 (caveat, counterexample): for `U(x, ξ) = x²`, `W = 0` (so (1.10)
holds: `U_x = 0`), and `x̃ = x̃⁰ = ϕ`, `ξ = 0`, `E[U] − V⁽¹⁾_printed = ϕ²`, not `O(ϕ³)`: the
printed `V⁽¹⁾` needs `x̃⁰ = 0` (or the extra term `V_xx(x̃⁰, x̃⁰)`). -/
theorem V1printed_false :
    ¬ (fun a : ℝ => expect (fun _ : Unit => (1 : ℝ)) (fun _ => cexU ((0, 0) + (a, 0))) -
      V1printed (fun _ : Unit => (1 : ℝ)) (cexU (0, 0))
        ((1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ cexU) (0, 0) + 0) (0 : ℝ →L[ℝ] ℝ) (fun _ => 0))
      =O[𝓝 0] (fun a => a ^ 3) := by
  intro h
  refine sq_not_isBigO_cube (h.congr_left fun a => ?_)
  have h0 : ((0 : ℝ), (0 : ℝ)) = 0 := rfl
  simp [expect, V1printed, cexU, h0]
  ring

/-- Woodford (2003), (1.10), p. 391: in the counterexample economy (1.10) holds with `W = 0`,
since `U_x(x̄; 0) = 0`. -/
theorem cex_h110 (a : ℝ) :
    (fderiv ℝ cexU (0, 0)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)
      (expect (fun _ : Unit => (1 : ℝ)) (fun _ => a)) -
      expect (fun _ : Unit => (1 : ℝ))
        (fun _ => (0 : ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] ℝ) (a, 0) (a, 0)) = 0 := by
  have h0 : ((0 : ℝ), (0 : ℝ)) = 0 := rfl
  simp [expect, h0, cexU_fderiv]

end Woodford.StabilizationWelfare.ApproxTheory
