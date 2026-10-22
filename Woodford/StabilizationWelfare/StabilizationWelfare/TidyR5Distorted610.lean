/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR5DistortedTools

/-!
# Proposition 6.10 expanded around the distorted steady state

Woodford (2003), *Interest and Prices*, Chapter 6, §4.3, Proposition 6.10, (4.24), p. 436, and
Appendix E.6, (E.26)–(E.31), pp. 703–705; the distorted steady state is (2.9), p. 394, and the
efficient-output gap `x* = Φ/(σ⁻¹ + ω) + O(Φ²)` is (2.17), p. 399.

`BridgeExtensions.prop610_actual` expands the ACTUAL two-sector utility around the EFFICIENT
steady state `Y*`. The book expands around the DISTORTED steady state `Ȳ` of an economy with
distortion `Φ`, which must itself be small (`Φ = O(ε)`) for the expansion to be second order.
This module carries out that change of expansion point:

* `hasDerivAt_dY`, `contDiff_dY`: `Y ↦ u_c(Y, 0)` is `C²` with derivative `u_cc(Y, 0)`.
* **`distorted_ss`**: along a branch of distorted steady states
  `v_y(Ȳ_b) = (1 − Φ_b)u_c(Ȳ_b)`, `Ȳ_b → Y*`, the log gap `log(Ȳ_b/Y*)` is `O(ε)` and equals
  `−x*_b = −Φ_b/(σ⁻¹ + ω)` up to `O(ε²)`.
* `logY2_shift`, `periodU2_shift`: measuring every output relative to `Ȳ_b` instead of `Y*`
  is a shift of all log deviations by the constant `log(Ȳ_b/Y*)`; the actual utility is the same
  function of the actual outputs.
* **`prop610_distorted`**: the actual period utility, with every output measured relative to
  the distorted steady state `Ȳ_b`, is
  `t.i.p. − ½Y*u_c·loss610Φ + O(ε³)`, where `loss610Φ` is (4.24) with the target
  `Ŷ − Ŷⁿ − x*`, `x* = Φ/(σ⁻¹ + ω)` (`loss610Phi`).
* **`prop610_distorted_layerB`**: the same with the loss evaluated at the first-order solution
  (Layer B).
-/

namespace Woodford.StabilizationWelfare.TidyR5Distorted610

open Filter Topology Asymptotics
open BridgeExtensions TidyR5DistortedTools
open ExpLogCES (crossVar)

variable {B : Type*} {L : Filter B} {s : B → ℝ}
variable {Ξ : Type*}

/-! ## Changing the reference output -/

/-- Woodford (2003), App. E.6, p. 703: the log two-sector aggregate does not depend on the
reference output, and shifting both sectoral log indices by `c` shifts it by `c`. -/
theorem logY2_shift {n1 η : ℝ} (hn0 : 0 < n1) (hn1 : n1 < 1) (hη : 0 < η) (hη1 : η ≠ 1)
    {Ybar Ybar' : ℝ} (hY : 0 < Ybar) (hY' : 0 < Ybar') (f1 f2 Y1 Y2 c : ℝ) :
    logY2 n1 η Ybar' f1 f2 (Y1 + c) (Y2 + c) = logY2 n1 η Ybar f1 f2 Y1 Y2 + c := by
  have hr : (η - 1) / η ≠ 0 := div_ne_zero (sub_ne_zero.mpr hη1) hη.ne'
  have hn2 : 0 < 1 - n1 := by linarith
  unfold logY2
  rw [TwoSectorWelfare.log_upperCES hn0 hn1 hη hη1 hY',
    TwoSectorWelfare.log_upperCES hn0 hn1 hη hη1 hY]
  simp only [TwoSectorWelfare.lse, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_mul]
  set r := (η - 1) / η with hrd
  have e1 : Real.exp (η⁻¹ * f1 + r * (Y1 + c)) =
      Real.exp (η⁻¹ * f1 + r * Y1) * Real.exp (r * c) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (η⁻¹ * f2 + r * (Y2 + c)) =
      Real.exp (η⁻¹ * f2 + r * Y2) * Real.exp (r * c) := by
    rw [← Real.exp_add]; ring_nf
  rw [e1, e2]
  have hpos : 0 < n1 * Real.exp (η⁻¹ * f1 + r * Y1) + (1 - n1) * Real.exp (η⁻¹ * f2 + r * Y2) :=
    by positivity
  rw [show n1 * (Real.exp (η⁻¹ * f1 + r * Y1) * Real.exp (r * c)) +
      (1 - n1) * (Real.exp (η⁻¹ * f2 + r * Y2) * Real.exp (r * c)) = Real.exp (r * c) *
      (n1 * Real.exp (η⁻¹ * f1 + r * Y1) + (1 - n1) * Real.exp (η⁻¹ * f2 + r * Y2)) by ring,
    Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp, mul_add, ← mul_assoc,
    inv_mul_cancel₀ hr, one_mul, add_comm]

variable {ι : Type*} [Fintype ι]

/-- Woodford (2003), §4.3, p. 436 (**the actual utility does not depend on the reference
output**): the two-sector period utility with outputs `y_j(i) = Ȳ e^{ŷ_j(i)}` equals the one
with reference output `Y*` and log deviations `ŷ_j(i) + log(Ȳ/Y*)`. -/
theorem periodU2_shift {n1 η θ : ℝ} (hn0 : 0 < n1) (hn1 : n1 < 1) (hη : 0 < η) (hη1 : η ≠ 1)
    (hθ : θ ≠ 1) {w1 w2 : ι → ℝ} (hw10 : ∀ i, 0 ≤ w1 i) (hw11 : ∑ i, w1 i = 1)
    (hw20 : ∀ i, 0 ≤ w2 i) (hw21 : ∑ i, w2 i = 1) (u v : ℝ × Ξ → ℝ) {Ys Yb : ℝ} (hYs : 0 < Ys)
    (hYb : 0 < Yb) (f1 f2 : ℝ) (yd1 yd2 : ι → ℝ) (xu xv1 xv2 : Ξ) :
    periodU2 u v n1 η θ Ys w1 w2 f1 f2 (fun i => yd1 i + Real.log (Yb / Ys))
        (fun i => yd2 i + Real.log (Yb / Ys)) xu xv1 xv2 =
      periodU2 u v n1 η θ Yb w1 w2 f1 f2 yd1 yd2 xu xv1 xv2 := by
  have hy : ∀ x, Ys * Real.exp (x + Real.log (Yb / Ys)) = Yb * Real.exp x := fun x => by
    rw [Real.exp_add, Real.exp_log (div_pos hYb hYs)]
    field_simp
  unfold periodU2
  rw [logYidx_shift hw10 hw11 hθ, logYidx_shift hw20 hw21 hθ,
    logY2_shift hn0 hn1 hη hη1 hYb hYs, hy]
  simp only [hy]

variable [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]

/-! ## The marginal utility as a function of the level -/

/-- Woodford (2003), (E.2), p. 692: `Y ↦ u_c(Y, 0)` has derivative `u_cc(Y, 0)`. -/
theorem hasDerivAt_dY {U : ℝ × Ξ → ℝ} (hU : ContDiff ℝ 2 U) (Y : ℝ) :
    HasDerivAt (fun y => dY U (y, 0)) (dYY U (Y, 0)) Y := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ U) := hU.fderiv_right (m := 1) (by norm_num)
  have hF : HasFDerivAt (fderiv ℝ U) (fderiv ℝ (fderiv ℝ U) (Y, 0)) (Y, 0) :=
    (h1.differentiable (by norm_num) (Y, 0)).hasFDerivAt
  have hγ : HasDerivAt (fun y : ℝ => ((y, (0 : Ξ)) : ℝ × Ξ)) ((1 : ℝ), (0 : Ξ)) Y :=
    (hasDerivAt_id' Y).prodMk (hasDerivAt_const Y (0 : Ξ))
  exact ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : Ξ))).hasFDerivAt).comp_hasDerivAt Y
    (hF.comp_hasDerivAt Y hγ)

/-- Woodford (2003), (E.2), p. 692: for `C³` utility, `Y ↦ u_c(Y, 0)` is `C²`. -/
theorem contDiff_dY {U : ℝ × Ξ → ℝ} (hU : ContDiff ℝ 3 U) :
    ContDiff ℝ 2 (fun y => dY U (y, 0)) :=
  ((hU.fderiv_right (m := 2) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const

/-! ## The distorted steady state -/

/-- **Woodford (2003), (2.9) and (2.17), pp. 394, 399 (the distorted steady state).** At the
efficient steady state `v_y = u_c`, `σ⁻¹ = −Y*u_cc/u_c`, `ω = Y*v_yy/v_y`. Along a branch of
distorted steady states `v_y(Ȳ_b) = (1 − Φ_b)u_c(Ȳ_b)` with `Ȳ_b → Y*` and `Φ_b = O(ε)`, the log
gap `c_b = log(Ȳ_b/Y*)` is `O(ε)` and `c_b + x*_b = O(ε²)`, `x*_b = Φ_b/(σ⁻¹ + ω)`
(`Prop61.xStarLin`). -/
theorem distorted_ss (hs : Tendsto s L (𝓝 0)) {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u)
    (hv : ContDiff ℝ 3 v) {Ys σi ω : ℝ} (hY : 0 < Ys) (hσω : σi + ω ≠ 0)
    (huc : dY u (Ys, 0) ≠ 0) (hucc : dYY u (Ys, 0) = -(σi * dY u (Ys, 0) / Ys))
    (hvy : dY v (Ys, 0) = dY u (Ys, 0)) (hvyy : dYY v (Ys, 0) = ω * dY v (Ys, 0) / Ys)
    {Yb Phi : B → ℝ} (hYb : Tendsto Yb L (𝓝 Ys))
    (hFOC : ∀ b, dY v (Yb b, 0) = (1 - Phi b) * dY u (Yb b, 0))
    (hPhi : Phi =O[L] fun b => s b ^ 1) :
    (fun b => Real.log (Yb b / Ys)) =O[L] (fun b => s b ^ 1) ∧
      (fun b => Real.log (Yb b / Ys) + Prop61.xStarLin σi ω (Phi b)) =O[L]
        fun b => s b ^ 2 := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by norm_num)
  set κ := (σi + ω) * dY u (Ys, 0) / Ys with hκd
  have hκ : κ ≠ 0 := div_ne_zero (mul_ne_zero hσω huc) hY.ne'
  have hh : ContDiffAt ℝ 2 (fun y => dY v (y, 0) - dY u (y, 0)) Ys :=
    ((contDiff_dY hv).sub (contDiff_dY hu)).contDiffAt
  have hd : deriv (fun y => dY v (y, 0) - dY u (y, 0)) Ys = κ := by
    have hD : HasDerivAt (fun y => dY v (y, 0) - dY u (y, 0)) (dYY v (Ys, 0) - dYY u (Ys, 0))
        Ys := (hasDerivAt_dY hv2 Ys).sub (hasDerivAt_dY hu2 Ys)
    rw [hD.deriv, hvyy, hucc, hvy, hκd]
    field_simp
    ring
  obtain ⟨h1, h2⟩ := ss_first_order (k := fun y => dY u (y, 0)) hh hd hκ
    (by simp only [hvy, sub_self]) (hasDerivAt_dY hu2 Ys).differentiableAt hYb
    (fun b => by simp only [hFOC]; ring) hPhi
  have hl := log_move hY hs h1
  have hc : (fun b => Real.log (Yb b / Ys)) =O[L] fun b => s b ^ 1 :=
    ((o_weaken hs (by norm_num : 1 ≤ 2) hl).add (h1.const_mul_left Ys⁻¹)).congr_left
      fun b => by ring
  refine ⟨hc, (hl.add (h2.const_mul_left (κ * Ys)⁻¹)).congr_left fun b => ?_⟩
  simp only [Prop61.xStarLin, hκd]
  field_simp
  ring

/-! ## Proposition 6.10 around the distorted steady state -/

/-- Woodford (2003), (4.24) and (E.31) with `Φ > 0`: the quadratic form of Proposition 6.10
around the distorted steady state,
`(σ⁻¹ + ω)(Ŷ − Ŷⁿ − x*)² + n₁n₂(η⁻¹ + ω)((Ŷ₂ − Ŷ₁) − (Ŷ₂ⁿ − Ŷ₁ⁿ))² + (θ⁻¹ + ω)(n₁V₁ + n₂V₂)`,
`x* = Φ/(σ⁻¹ + ω)` (the form of `TwoSectorWelfare.prop_6_10_layerA`). -/
noncomputable def loss610Phi (σi ω θi ηi n1 Phi g q1 q2 d Y Y1 Y2 V1 V2 : ℝ) : ℝ :=
  loss610 σi ω θi ηi n1 g q1 q2 d (Y - Prop61.xStarLin σi ω Phi) Y1 Y2 V1 V2

/-- **Woodford (2003), Proposition 6.10, (4.24)/(E.26)–(E.31), pp. 436, 703–705, expanded
around the DISTORTED steady state.** The economy has distortion `Φ_b = O(ε)` and distorted
steady state `Ȳ_b` (`v_y(Ȳ_b) = (1 − Φ_b)u_c(Ȳ_b)`, `Ȳ_b → Y*`); every output is measured
relative to `Ȳ_b`: `y_j(i) = Ȳ_b e^{ŷ_j(i)}`, with `Ŷ_j`, `Ŷ`, `Vⱼ` the exact indices of these
distorted-steady-state deviations. The coefficients `σ⁻¹, ω` and the disturbances `g, q_j` are
those of the efficient point `Y*` (re-evaluating all of them at `Ȳ_b` changes the expansion by
`O(ε³)` only: prop610_distorted_local in TidyR5DistortedLocal). Then the actual period utility is
`t.i.p. − ½Y*u_c·loss610Φ + O(ε³)`, with the target `Ŷ − Ŷⁿ − x*`, `x* = Φ/(σ⁻¹ + ω)`, and the
t.i.p. `tip2 + Y*u_c·tip610` a function of the disturbances only. -/
theorem prop610_distorted (hs : Tendsto s L (𝓝 0)) {n1 η θ : ℝ} (hn0 : 0 < n1) (hn1 : n1 < 1)
    (hη : 0 < η) (hη1 : η ≠ 1) (hθ : θ ≠ 1) {w1 w2 : ι → ℝ} (hw10 : ∀ i, 0 ≤ w1 i)
    (hw11 : ∑ i, w1 i = 1) (hw20 : ∀ i, 0 ≤ w2 i) (hw21 : ∑ i, w2 i = 1)
    {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v) {Ys σi ω : ℝ}
    (hY : 0 < Ys) (hσω : σi + ω ≠ 0) (hηω : η⁻¹ + ω ≠ 0) (huc : dY u (Ys, 0) ≠ 0)
    (hucc : dYY u (Ys, 0) = -(σi * dY u (Ys, 0) / Ys))
    (hvy : dY v (Ys, 0) = dY u (Ys, 0))
    (hvyy : dYY v (Ys, 0) = ω * dY v (Ys, 0) / Ys)
    {Yb Phi : B → ℝ} (hYb0 : ∀ b, 0 < Yb b) (hYb : Tendsto Yb L (𝓝 Ys))
    (hFOC : ∀ b, dY v (Yb b, 0) = (1 - Phi b) * dY u (Yb b, 0))
    (hPhi : Phi =O[L] fun b => s b ^ 1)
    {yd1 yd2 : B → ι → ℝ} {f1 f2 g q1 q2 : B → ℝ} {xu xv1 xv2 : B → Ξ}
    (hnorm : ∀ b, n1 * Real.exp (f1 b) + (1 - n1) * Real.exp (f2 b) = 1)
    (hg : ∀ b, dYXi u (Ys, 0) (xu b) = σi * dY u (Ys, 0) * g b)
    (hq1 : ∀ b, dYXi v (Ys, 0) (xv1 b) = -(ω * dY v (Ys, 0) * q1 b))
    (hq2 : ∀ b, dYXi v (Ys, 0) (xv2 b) = -(ω * dY v (Ys, 0) * q2 b))
    (hyd1 : yd1 =O[L] fun b => s b ^ 1) (hyd2 : yd2 =O[L] fun b => s b ^ 1)
    (hf1 : f1 =O[L] fun b => s b ^ 1) (hf2 : f2 =O[L] fun b => s b ^ 1)
    (hgO : g =O[L] fun b => s b ^ 1) (hq1O : q1 =O[L] fun b => s b ^ 1)
    (hq2O : q2 =O[L] fun b => s b ^ 1) (hxu : xu =O[L] fun b => s b ^ 1)
    (hxv1 : xv1 =O[L] fun b => s b ^ 1) (hxv2 : xv2 =O[L] fun b => s b ^ 1) :
    (fun b => periodU2 u v n1 η θ (Yb b) w1 w2 (f1 b) (f2 b) (yd1 b) (yd2 b) (xu b) (xv1 b)
        (xv2 b) -
      (tip2 u v n1 Ys (xu b) (xv1 b) (xv2 b) + Ys * dY u (Ys, 0) *
        (TwoSectorWelfare.tip610 σi ω η⁻¹ n1 0 (g b) (q1 b) (q2 b) (f2 b - f1 b)
            (tauAgg η⁻¹ n1 (f1 b) (f2 b)) -
          loss610Phi σi ω θ⁻¹ η⁻¹ n1 (Phi b) (g b) (q1 b) (q2 b) (f2 b - f1 b)
            (logY2 n1 η (Yb b) (f1 b) (f2 b) (logYidx w1 θ (yd1 b)) (logYidx w2 θ (yd2 b)))
            (logYidx w1 θ (yd1 b)) (logYidx w2 θ (yd2 b)) (crossVar w1 (yd1 b))
            (crossVar w2 (yd2 b)) / 2))) =O[L] fun b => s b ^ 3 := by
  obtain ⟨hc, hcx⟩ := distorted_ss hs hu hv hY hσω huc hucc hvy hvyy hYb hFOC hPhi
  set c := fun b => Real.log (Yb b / Ys) with hcd
  have he1 : (fun b => fun i => yd1 b i + c b) =O[L] fun b => s b ^ 1 :=
    isBigO_pi.2 fun i => (coord_o hyd1 i).add hc
  have he2 : (fun b => fun i => yd2 b i + c b) =O[L] fun b => s b ^ 1 :=
    isBigO_pi.2 fun i => (coord_o hyd2 i).add hc
  have hW := prop610_actual hs hn0 hn1 hη hη1 hθ hw10 hw11 hw20 hw21 hu hv hY hσω hηω hucc hvy
    hvyy hnorm hg hq1 hq2 he1 he2 hf1 hf2 hgO hq1O hq2O hxu hxv1 hxv2
  -- the distorted output gap is first order
  set Y1d := fun b => logYidx w1 θ (yd1 b) with hY1d
  set Y2d := fun b => logYidx w2 θ (yd2 b) with hY2d
  have hY1O : Y1d =O[L] fun b => s b ^ 1 := logYidx_o hs hw10 hw11 hθ hyd1
  have hY2O : Y2d =O[L] fun b => s b ^ 1 := logYidx_o hs hw20 hw21 hθ hyd2
  have hd : (fun b => f2 b - f1 b) =O[L] fun b => s b ^ 1 := hf2.sub hf1
  have hτO : (fun b => tauAgg η⁻¹ n1 (f1 b) (f2 b)) =O[L] fun b => s b ^ 2 :=
    (((S_o hs hf1 hf2 hnorm).const_mul_left ((1 - η⁻¹)⁻¹ * η⁻¹)).add
      ((o_pow hd 2).const_mul_left (n1 * (1 - n1) * (1 - η⁻¹)⁻¹ * (η⁻¹) ^ 2 / 2))).congr_left
        fun b => by simp only [tauAgg]
  have hdY := hY2O.sub hY1O
  have hET : (fun b => TwoSectorWelfare.ET η⁻¹ n1 (f2 b - f1 b) (Y1d b) (Y2d b)
      (tauAgg η⁻¹ n1 (f1 b) (f2 b))) =O[L] fun b => s b ^ 2 :=
    ((((o_mul hd hdY (by norm_num : 1 + 1 = 2)).const_mul_left (η⁻¹ * n1 * (1 - n1))).add
      ((o_pow hdY 2).const_mul_left (n1 * (1 - n1) * (1 - η⁻¹) / 2))).add hτO).congr_left
        fun b => by unfold TwoSectorWelfare.ET; ring
  have hA := aggAtom_o hs hn0 hn1 hη hη1 hY hf1 hf2 hY1O hY2O (Ybar := Ys)
  have hYdO : (fun b => logY2 n1 η (Yb b) (f1 b) (f2 b) (Y1d b) (Y2d b)) =O[L]
      fun b => s b ^ 1 := by
    refine ((((o_weaken hs (by norm_num : 1 ≤ 3) hA).add ((hY1O.const_mul_left n1).add
      (hY2O.const_mul_left (1 - n1)))).add (o_weaken hs (by norm_num : 1 ≤ 2) hET))).congr_left
        fun b => ?_
    have e := logY2_shift hn0 hn1 hη hη1 hY (hYb0 b) (f1 b) (f2 b) (Y1d b) (Y2d b) 0
    simp only [add_zero] at e
    rw [e]
    simp only [aggAtom]
    ring
  have hnat : (fun b => TwoSectorWelfare.natY σi ω n1 (g b) (q1 b) (q2 b))
      =O[L] fun b => s b ^ 1 :=
    (((hgO.const_mul_left σi).add (((hq1O.const_mul_left n1).add
      (hq2O.const_mul_left (1 - n1))).const_mul_left ω)).const_mul_left (σi + ω)⁻¹).congr_left
        fun b => by unfold TwoSectorWelfare.natY; ring
  have hx : (fun b => Prop61.xStarLin σi ω (Phi b)) =O[L] fun b => s b ^ 1 :=
    (hPhi.const_mul_left (σi + ω)⁻¹).congr_left fun b => by
      simp only [Prop61.xStarLin]; ring
  have hgap : (fun b => 2 * (logY2 n1 η (Yb b) (f1 b) (f2 b) (Y1d b) (Y2d b) -
      TwoSectorWelfare.natY σi ω n1 (g b) (q1 b) (q2 b)) + c b -
        Prop61.xStarLin σi ω (Phi b)) =O[L] fun b => s b ^ 1 :=
    ((((hYdO.sub hnat).const_mul_left 2).add hc).sub hx)
  have hdiff := (o_mul hcx hgap (by norm_num : 2 + 1 = 3)).const_mul_left
    (Ys * dY u (Ys, 0) * (σi + ω) / 2)
  refine (hW.sub hdiff).congr_left fun b => ?_
  have s1 := logYidx_shift hw10 hw11 hθ (c b) (yd1 b)
  have s2 := logYidx_shift hw20 hw21 hθ (c b) (yd2 b)
  have s3 := logY2_shift hn0 hn1 hη hη1 (hYb0 b) hY (f1 b) (f2 b) (Y1d b) (Y2d b) (c b)
  have v1 : crossVar w1 (fun i => yd1 b i + c b) = crossVar w1 (yd1 b) := by
    rw [← ExpLogCES.crossVar_const_add hw11 (c b) (yd1 b)]
    congr 1
    funext i
    ring
  have v2 : crossVar w2 (fun i => yd2 b i + c b) = crossVar w2 (yd2 b) := by
    rw [← ExpLogCES.crossVar_const_add hw21 (c b) (yd2 b)]
    congr 1
    funext i
    ring
  have pU := periodU2_shift hn0 hn1 hη hη1 hθ hw10 hw11 hw20 hw21 u v hY (hYb0 b) (f1 b) (f2 b)
    (yd1 b) (yd2 b) (xu b) (xv1 b) (xv2 b)
  simp only [hcd] at s1 s2 s3 v1 v2 ⊢
  simp only [hY1d, hY2d] at s3 ⊢
  rw [pU, s1, s2, s3, v1, v2]
  simp only [loss610Phi, loss610]
  ring

/-- **Woodford (2003), Proposition 6.10, (4.24)/(E.26), LAYER B around the distorted steady
state**: under the hypotheses of `prop610_distorted`, if the family has a first-order solution
(`Φ = εΦ¹ + O(ε²)`, `g, q_j, d = ε × first order + O(ε²)`, the distorted-steady-state deviations
`Ŷ, Ŷ_j = ε × first order + O(ε²)`, `ŷ_j = εŷ_j¹ + O(ε²)`, all first-order objects bounded), then
`W(ε) = t.i.p.(ε) − (ε²/2)·Y*u_c·loss610Φ(first-order solution) + O(ε³)`. -/
theorem prop610_distorted_layerB (hs : Tendsto s L (𝓝 0)) {n1 η θ : ℝ} (hn0 : 0 < n1)
    (hn1 : n1 < 1) (hη : 0 < η) (hη1 : η ≠ 1) (hθ : θ ≠ 1) {w1 w2 : ι → ℝ}
    (hw10 : ∀ i, 0 ≤ w1 i) (hw11 : ∑ i, w1 i = 1) (hw20 : ∀ i, 0 ≤ w2 i)
    (hw21 : ∑ i, w2 i = 1) {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    {Ys σi ω : ℝ} (hY : 0 < Ys) (hσω : σi + ω ≠ 0) (hηω : η⁻¹ + ω ≠ 0)
    (huc : dY u (Ys, 0) ≠ 0) (hucc : dYY u (Ys, 0) = -(σi * dY u (Ys, 0) / Ys))
    (hvy : dY v (Ys, 0) = dY u (Ys, 0))
    (hvyy : dYY v (Ys, 0) = ω * dY v (Ys, 0) / Ys)
    {Yb Phi : B → ℝ} (hYb0 : ∀ b, 0 < Yb b) (hYb : Tendsto Yb L (𝓝 Ys))
    (hFOC : ∀ b, dY v (Yb b, 0) = (1 - Phi b) * dY u (Yb b, 0))
    {yd1 yd2 y1f y2f : B → ι → ℝ} {f1 f2 g q1 q2 Phif gf q1f q2f df Yf Y1f Y2f : B → ℝ}
    {xu xv1 xv2 : B → Ξ}
    (hnorm : ∀ b, n1 * Real.exp (f1 b) + (1 - n1) * Real.exp (f2 b) = 1)
    (hg : ∀ b, dYXi u (Ys, 0) (xu b) = σi * dY u (Ys, 0) * g b)
    (hq1 : ∀ b, dYXi v (Ys, 0) (xv1 b) = -(ω * dY v (Ys, 0) * q1 b))
    (hq2 : ∀ b, dYXi v (Ys, 0) (xv2 b) = -(ω * dY v (Ys, 0) * q2 b))
    (hyd1 : yd1 =O[L] fun b => s b ^ 1) (hyd2 : yd2 =O[L] fun b => s b ^ 1)
    (hf1 : f1 =O[L] fun b => s b ^ 1) (hf2 : f2 =O[L] fun b => s b ^ 1)
    (hxu : xu =O[L] fun b => s b ^ 1)
    (hxv1 : xv1 =O[L] fun b => s b ^ 1) (hxv2 : xv2 =O[L] fun b => s b ^ 1)
    (bPhi : Phif =O[L] fun _ => (1 : ℝ))
    (bg : gf =O[L] fun _ => (1 : ℝ)) (bq1 : q1f =O[L] fun _ => (1 : ℝ))
    (bq2 : q2f =O[L] fun _ => (1 : ℝ)) (bd : df =O[L] fun _ => (1 : ℝ))
    (bY : Yf =O[L] fun _ => (1 : ℝ)) (bY1 : Y1f =O[L] fun _ => (1 : ℝ))
    (bY2 : Y2f =O[L] fun _ => (1 : ℝ)) (by1 : y1f =O[L] fun _ => (1 : ℝ))
    (by2 : y2f =O[L] fun _ => (1 : ℝ))
    (hPhid : (fun b => Phi b - s b * Phif b) =O[L] fun b => s b ^ 2)
    (hgd : (fun b => g b - s b * gf b) =O[L] fun b => s b ^ 2)
    (hq1d : (fun b => q1 b - s b * q1f b) =O[L] fun b => s b ^ 2)
    (hq2d : (fun b => q2 b - s b * q2f b) =O[L] fun b => s b ^ 2)
    (hdd : (fun b => (f2 b - f1 b) - s b * df b) =O[L] fun b => s b ^ 2)
    (hYd : (fun b => logY2 n1 η (Yb b) (f1 b) (f2 b) (logYidx w1 θ (yd1 b))
      (logYidx w2 θ (yd2 b)) - s b * Yf b) =O[L] fun b => s b ^ 2)
    (hY1d : (fun b => logYidx w1 θ (yd1 b) - s b * Y1f b) =O[L] fun b => s b ^ 2)
    (hY2d : (fun b => logYidx w2 θ (yd2 b) - s b * Y2f b) =O[L] fun b => s b ^ 2)
    (hy1d : (fun b => yd1 b - s b • y1f b) =O[L] fun b => s b ^ 2)
    (hy2d : (fun b => yd2 b - s b • y2f b) =O[L] fun b => s b ^ 2) :
    (fun b => periodU2 u v n1 η θ (Yb b) w1 w2 (f1 b) (f2 b) (yd1 b) (yd2 b) (xu b) (xv1 b)
        (xv2 b) -
      ((tip2 u v n1 Ys (xu b) (xv1 b) (xv2 b) + Ys * dY u (Ys, 0) *
        TwoSectorWelfare.tip610 σi ω η⁻¹ n1 0 (g b) (q1 b) (q2 b) (f2 b - f1 b)
          (tauAgg η⁻¹ n1 (f1 b) (f2 b))) -
        s b ^ 2 / 2 * (Ys * dY u (Ys, 0) * loss610Phi σi ω θ⁻¹ η⁻¹ n1 (Phif b) (gf b) (q1f b)
          (q2f b) (df b) (Yf b) (Y1f b) (Y2f b) (crossVar w1 (y1f b)) (crossVar w2 (y2f b)))))
      =O[L] fun b => s b ^ 3 := by
  have fo : ∀ (x x1 : B → ℝ), (fun b => x b - s b * x1 b) =O[L] (fun b => s b ^ 2) →
      x1 =O[L] (fun _ => (1 : ℝ)) → x =O[L] fun b => s b ^ 1 := fun x x1 hd h1 =>
    ((o_weaken hs (by norm_num : 1 ≤ 2) hd).add
      (((isBigO_refl s L).mul h1).congr_right fun b => by ring)).congr_left fun b => by ring
  have hW := prop610_distorted hs hn0 hn1 hη hη1 hθ hw10 hw11 hw20 hw21 hu hv hY hσω hηω huc
    hucc hvy hvyy hYb0 hYb hFOC (fo Phi Phif hPhid bPhi) hnorm hg hq1 hq2 hyd1 hyd2 hf1 hf2
    (fo g gf hgd bg) (fo q1 q1f hq1d bq1) (fo q2 q2f hq2d bq2) hxu hxv1 hxv2
  have hYx : (fun b => (logY2 n1 η (Yb b) (f1 b) (f2 b) (logYidx w1 θ (yd1 b))
      (logYidx w2 θ (yd2 b)) - Prop61.xStarLin σi ω (Phi b)) -
        s b * (Yf b - Prop61.xStarLin σi ω (Phif b))) =O[L] fun b => s b ^ 2 :=
    (hYd.sub (hPhid.const_mul_left (σi + ω)⁻¹)).congr_left fun b => by
      simp only [Prop61.xStarLin]; ring
  have bYx : (fun b => Yf b - Prop61.xStarLin σi ω (Phif b)) =O[L] fun _ => (1 : ℝ) :=
    (bY.sub (bPhi.const_mul_left (σi + ω)⁻¹)).congr_left fun b => by
      simp only [Prop61.xStarLin]; ring
  have hL := loss610_first_order hs σi ω θ⁻¹ η⁻¹ n1 hgd hq1d hq2d hdd hYx hY1d hY2d
    (crossVar_first_order hs hw10 hw11 hy1d by1) (crossVar_first_order hs hw20 hw21 hy2d by2)
    bg bq1 bq2 bd bYx bY1 bY2
  exact bridge_first_order (hW.congr_left fun b => by simp only [loss610Phi]; ring) hL

end Woodford.StabilizationWelfare.TidyR5Distorted610
