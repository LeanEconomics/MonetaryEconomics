/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR5Distorted610

/-!
# Proposition 6.10 with the coefficients of the distorted steady state

Woodford (2003), *Interest and Prices*, Chapter 6, §4.3, Proposition 6.10, (4.24), p. 436, and
§2.1, pp. 393–394: in the book every coefficient of the quadratic loss (`σ⁻¹ = −Ȳu_cc/u_c`,
`ω = Ȳv_yy/v_y`, the composite disturbances `g`, `q_{j}`, the weight `Ȳu_c`, and
`x* = Φ/(σ⁻¹ + ω)`) is evaluated at the DISTORTED steady state `Ȳ`.

`TidyR5Distorted610.prop610_distorted` measures the variables from `Ȳ_b` but keeps the
coefficients of the efficient point `Y*`. This module shows that re-evaluating every coefficient
at `Ȳ_b` changes the expansion by `O(ε³)` only (**`prop610_distorted_local`**):

* `inv_move`, `ratio_move`, `div_move`: moving coefficients of a quadratic form;
* `coeff_move`: `Ȳ_bu_c(Ȳ_b) − Y*u_c(Y*)`, `σ⁻¹(Ȳ_b) − σ⁻¹`, `ω(Ȳ_b) − ω` are `O(ε)`;
* `loss610Phi_move`, `loss610Phi_o`: the loss with `O(ε)`-moved coefficients and `O(ε²)`-moved
  disturbances differs by `O(ε³)`, and the loss is `O(ε²)`.
-/

namespace Woodford.StabilizationWelfare.TidyR5DistortedLocal

open Filter Topology Asymptotics
open BridgeExtensions TidyR5DistortedTools TidyR5Distorted610
open ExpLogCES (crossVar)

variable {B : Type*} {L : Filter B} {s : B → ℝ}

/-! ## Moving coefficients -/

/-- Woodford (2003), App. E (moving coefficients): if `D_b − D = O(ε)` and `D ≠ 0` then
`D_b⁻¹` is bounded and `D_b⁻¹ − D⁻¹ = O(ε)`. -/
theorem inv_move (hs : Tendsto s L (𝓝 0)) {D : ℝ} (hD : D ≠ 0) {Db : B → ℝ}
    (hDb : (fun b => Db b - D) =O[L] fun b => s b ^ 1) :
    (fun b => (Db b)⁻¹) =O[L] (fun _ => (1 : ℝ)) ∧
      (fun b => (Db b)⁻¹ - D⁻¹) =O[L] fun b => s b ^ 1 := by
  have hT : Tendsto Db L (𝓝 D) := by
    have := (tendsto_of_o_one hs hDb).add_const D
    simpa using this
  exact ⟨(hT.inv₀ hD).isBigO_one ℝ,
    ((hasDerivAt_inv hD).isBigO_sub.comp_tendsto hT).trans hDb⟩

/-- Woodford (2003), App. E: a ratio `N_b/D_b` with `N_b − N = O(ε²)`, `N = O(ε)`,
`D_b − D = O(ε)`, `D ≠ 0` moves by `O(ε²)`. -/
theorem ratio_move (hs : Tendsto s L (𝓝 0)) {D : ℝ} (hD : D ≠ 0) {Db N Nb : B → ℝ}
    (hDb : (fun b => Db b - D) =O[L] fun b => s b ^ 1)
    (hN : N =O[L] fun b => s b ^ 1) (hNb : (fun b => Nb b - N b) =O[L] fun b => s b ^ 2) :
    (fun b => Nb b / Db b - N b / D) =O[L] fun b => s b ^ 2 := by
  obtain ⟨h1, h2⟩ := inv_move hs hD hDb
  refine (((h1.mul hNb).congr_right fun b => by ring).add
    (o_mul hN h2 (by norm_num : 1 + 1 = 2))).congr_left fun b => ?_
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- Woodford (2003), App. E (the composite disturbances at the distorted point): if `a_b → a ≠ 0`
with `a_b − a = O(ε)`, `x = O(ε)` and `a_bx_b − ax = O(ε²)`, then `x_b − x = O(ε²)`. -/
theorem div_move (hs : Tendsto s L (𝓝 0)) {a : ℝ} (ha : a ≠ 0) {ab x xb : B → ℝ}
    (hab : (fun b => ab b - a) =O[L] fun b => s b ^ 1) (hx : x =O[L] fun b => s b ^ 1)
    (hprod : (fun b => ab b * xb b - a * x b) =O[L] fun b => s b ^ 2) :
    (fun b => xb b - x b) =O[L] fun b => s b ^ 2 := by
  have hT : Tendsto ab L (𝓝 a) := by
    have := (tendsto_of_o_one hs hab).add_const a
    simpa using this
  have hne : ∀ᶠ b in L, ab b ≠ 0 := hT.eventually_ne ha
  refine (((hT.inv₀ ha).isBigO_one ℝ).mul (hprod.sub (o_mul hab hx
    (by norm_num : 1 + 1 = 2)))).congr' ?_ (Eventually.of_forall fun b => by ring)
  filter_upwards [hne] with b hb
  field_simp
  ring

/-- Woodford (2003), (E.31), p. 705: the loss `loss610Phi` is `O(ε²)` when its first-order
arguments are `O(ε)` and the dispersions `O(ε²)`. -/
theorem loss610Phi_o (σi ω θi ηi n1 : ℝ) {Phi g q1 q2 d Y Y1 Y2 V1 V2 : B → ℝ}
    (hPhi : Phi =O[L] fun b => s b ^ 1) (hg : g =O[L] fun b => s b ^ 1)
    (hq1 : q1 =O[L] fun b => s b ^ 1) (hq2 : q2 =O[L] fun b => s b ^ 1)
    (hd : d =O[L] fun b => s b ^ 1) (hY : Y =O[L] fun b => s b ^ 1)
    (hY1 : Y1 =O[L] fun b => s b ^ 1) (hY2 : Y2 =O[L] fun b => s b ^ 1)
    (hV1 : V1 =O[L] fun b => s b ^ 2) (hV2 : V2 =O[L] fun b => s b ^ 2) :
    (fun b => loss610Phi σi ω θi ηi n1 (Phi b) (g b) (q1 b) (q2 b) (d b) (Y b) (Y1 b) (Y2 b)
      (V1 b) (V2 b)) =O[L] fun b => s b ^ 2 := by
  have z1 : (fun b => Y b - Prop61.xStarLin σi ω (Phi b) -
      TwoSectorWelfare.natY σi ω n1 (g b) (q1 b) (q2 b)) =O[L] fun b => s b ^ 1 :=
    ((hY.sub (hPhi.const_mul_left (σi + ω)⁻¹)).sub (((hg.const_mul_left σi).add
      (((hq1.const_mul_left n1).add (hq2.const_mul_left (1 - n1))).const_mul_left
        ω)).const_mul_left (σi + ω)⁻¹)).congr_left fun b => by
      simp only [Prop61.xStarLin, TwoSectorWelfare.natY]; ring
  have z2 : (fun b => (Y2 b - Y1 b) - TwoSectorWelfare.natD ηi ω (d b) (q1 b) (q2 b))
      =O[L] fun b => s b ^ 1 :=
    ((hY2.sub hY1).sub (((hd.const_mul_left ηi).add ((hq2.sub hq1).const_mul_left
      ω)).const_mul_left (ηi + ω)⁻¹)).congr_left fun b => by
      simp only [TwoSectorWelfare.natD]; ring
  refine ((((o_pow z1 2).const_mul_left (σi + ω)).add ((o_pow z2 2).const_mul_left
    (n1 * (1 - n1) * (ηi + ω)))).add (((hV1.const_mul_left n1).add
      (hV2.const_mul_left (1 - n1))).const_mul_left (θi + ω))).congr_left fun b => ?_
  simp only [loss610Phi, loss610]

/-- Woodford (2003), (4.24) and (E.31) (**coefficients at the distorted point**): if the
coefficients move by `O(ε)` (`σ⁻¹_b − σ⁻¹`, `ω_b − ω`) and the composite disturbances by
`O(ε²)` (`g_b − g`, `q_{j,b} − q_j`), the loss `loss610Phi` (including its target
`x* = Φ/(σ⁻¹ + ω)`) changes by `O(ε³)` along any family with first-order arguments. -/
theorem loss610Phi_move (hs : Tendsto s L (𝓝 0)) {σi ω θi ηi n1 : ℝ} (hσω : σi + ω ≠ 0)
    (hηω : ηi + ω ≠ 0) {σb ωb Phi g q1 q2 gb q1b q2b d Y Y1 Y2 V1 V2 : B → ℝ}
    (hσb : (fun b => σb b - σi) =O[L] fun b => s b ^ 1)
    (hωb : (fun b => ωb b - ω) =O[L] fun b => s b ^ 1)
    (hgb : (fun b => gb b - g b) =O[L] fun b => s b ^ 2)
    (hq1b : (fun b => q1b b - q1 b) =O[L] fun b => s b ^ 2)
    (hq2b : (fun b => q2b b - q2 b) =O[L] fun b => s b ^ 2)
    (hPhi : Phi =O[L] fun b => s b ^ 1) (hg : g =O[L] fun b => s b ^ 1)
    (hq1 : q1 =O[L] fun b => s b ^ 1) (hq2 : q2 =O[L] fun b => s b ^ 1)
    (hd : d =O[L] fun b => s b ^ 1) (hY : Y =O[L] fun b => s b ^ 1)
    (hY1 : Y1 =O[L] fun b => s b ^ 1) (hY2 : Y2 =O[L] fun b => s b ^ 1)
    (hV1 : V1 =O[L] fun b => s b ^ 2) (hV2 : V2 =O[L] fun b => s b ^ 2) :
    (fun b => loss610Phi (σb b) (ωb b) θi ηi n1 (Phi b) (gb b) (q1b b) (q2b b) (d b) (Y b)
        (Y1 b) (Y2 b) (V1 b) (V2 b) -
      loss610Phi σi ω θi ηi n1 (Phi b) (g b) (q1 b) (q2 b) (d b) (Y b) (Y1 b) (Y2 b) (V1 b)
        (V2 b)) =O[L] fun b => s b ^ 3 := by
  have bd1 : (fun _ : B => (1 : ℝ)) =O[L] (fun _ => (1 : ℝ)) := isBigO_refl _ _
  have hσbB : σb =O[L] (fun _ => (1 : ℝ)) :=
    ((o_weaken hs (by norm_num : 0 ≤ 1) hσb).add (isBigO_const_const σi one_ne_zero L)
      |>.congr_right fun b => by ring).congr_left fun b => by ring
  have hωbB : ωb =O[L] (fun _ => (1 : ℝ)) :=
    ((o_weaken hs (by norm_num : 0 ≤ 1) hωb).add (isBigO_const_const ω one_ne_zero L)
      |>.congr_right fun b => by ring).congr_left fun b => by ring
  -- the first term
  have hDb : (fun b => (σb b + ωb b) - (σi + ω)) =O[L] fun b => s b ^ 1 :=
    (hσb.add hωb).congr_left fun b => by ring
  set Q := fun b => n1 * q1 b + (1 - n1) * q2 b with hQ
  set Qb := fun b => n1 * q1b b + (1 - n1) * q2b b with hQb
  have hQO : Q =O[L] fun b => s b ^ 1 := (hq1.const_mul_left n1).add (hq2.const_mul_left _)
  have hQbd : (fun b => Qb b - Q b) =O[L] fun b => s b ^ 2 :=
    ((hq1b.const_mul_left n1).add (hq2b.const_mul_left (1 - n1))).congr_left fun b => by
      simp only [hQ, hQb]; ring
  have hNO : (fun b => σi * g b + ω * Q b) =O[L] fun b => s b ^ 1 :=
    (hg.const_mul_left σi).add (hQO.const_mul_left ω)
  have hNbd : (fun b => (σb b * gb b + ωb b * Qb b) - (σi * g b + ω * Q b)) =O[L]
      fun b => s b ^ 2 :=
    ((((hσbB.mul hgb).congr_right fun b => by ring).add (o_mul hσb hg
      (by norm_num : 1 + 1 = 2))).add (((hωbB.mul hQbd).congr_right fun b => by ring).add
        (o_mul hωb hQO (by norm_num : 1 + 1 = 2)))).congr_left fun b => by ring
  have hnat := ratio_move hs hσω hDb hNO hNbd
  have hPhid : (fun b => Phi b - Phi b) =O[L] fun b => s b ^ 2 :=
    (isBigO_zero _ _).congr_left fun b => by ring
  have hx := ratio_move hs hσω hDb hPhi hPhid
  have hz : (fun b => (Y b - Prop61.xStarLin (σb b) (ωb b) (Phi b) -
      TwoSectorWelfare.natY (σb b) (ωb b) n1 (gb b) (q1b b) (q2b b)) -
      (Y b - Prop61.xStarLin σi ω (Phi b) - TwoSectorWelfare.natY σi ω n1 (g b) (q1 b) (q2 b)))
      =O[L] fun b => s b ^ 2 :=
    (hx.add hnat).neg_left.congr_left fun b => by
      simp only [Prop61.xStarLin, TwoSectorWelfare.natY, hQ, hQb]; ring
  have hz' : (fun b => Y b - Prop61.xStarLin σi ω (Phi b) -
      TwoSectorWelfare.natY σi ω n1 (g b) (q1 b) (q2 b)) =O[L] fun b => s b ^ 1 :=
    ((hY.sub (hPhi.const_mul_left (σi + ω)⁻¹)).sub (hNO.const_mul_left (σi + ω)⁻¹)).congr_left
      fun b => by simp only [Prop61.xStarLin, TwoSectorWelfare.natY, hQ]; ring
  have t1 := sq_move (c := fun b => σb b + ωb b) (c' := fun _ => σi + ω) hs hDb
    (isBigO_const_const (σi + ω) one_ne_zero L) hz hz'
  -- the second term
  have hEb : (fun b => (ηi + ωb b) - (ηi + ω)) =O[L] fun b => s b ^ 1 :=
    hωb.congr_left fun b => by ring
  have hMO : (fun b => ηi * d b + ω * (q2 b - q1 b)) =O[L] fun b => s b ^ 1 :=
    (hd.const_mul_left ηi).add ((hq2.sub hq1).const_mul_left ω)
  have hMbd : (fun b => (ηi * d b + ωb b * (q2b b - q1b b)) - (ηi * d b + ω * (q2 b - q1 b)))
      =O[L] fun b => s b ^ 2 :=
    (((hωbB.mul (hq2b.sub hq1b)).congr_right fun b => by ring).add (o_mul hωb (hq2.sub hq1)
      (by norm_num : 1 + 1 = 2))).congr_left fun b => by ring
  have hnatD := ratio_move hs hηω hEb hMO hMbd
  have hw : (fun b => ((Y2 b - Y1 b) - TwoSectorWelfare.natD ηi (ωb b) (d b) (q1b b) (q2b b)) -
      ((Y2 b - Y1 b) - TwoSectorWelfare.natD ηi ω (d b) (q1 b) (q2 b))) =O[L]
      fun b => s b ^ 2 :=
    hnatD.neg_left.congr_left fun b => by simp only [TwoSectorWelfare.natD]; ring
  have hw' : (fun b => (Y2 b - Y1 b) - TwoSectorWelfare.natD ηi ω (d b) (q1 b) (q2 b))
      =O[L] fun b => s b ^ 1 :=
    ((hY2.sub hY1).sub (hMO.const_mul_left (ηi + ω)⁻¹)).congr_left fun b => by
      simp only [TwoSectorWelfare.natD]; ring
  have t2 := sq_move (c := fun b => n1 * (1 - n1) * (ηi + ωb b))
    (c' := fun _ => n1 * (1 - n1) * (ηi + ω)) hs
    ((hEb.const_mul_left (n1 * (1 - n1))).congr_left fun b => by ring)
    (isBigO_const_const (n1 * (1 - n1) * (ηi + ω)) one_ne_zero L) hw hw'
  -- the third term
  have t3 := mul_move (c := fun b => θi + ωb b) (c' := fun _ => θi + ω)
    (hωb.congr_left fun b => by ring) ((hV1.const_mul_left n1).add (hV2.const_mul_left (1 - n1)))
  refine ((t1.add t2).add t3).congr_left fun b => ?_
  simp only [loss610Phi, loss610]
  ring

/-! ## The coefficients at the distorted steady state -/

variable {Ξ : Type*} [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]

/-- Woodford (2003), (E.2), p. 692: for `C³` utility, `Y ↦ u_cc(Y, 0)` is differentiable. -/
theorem differentiable_dYY {U : ℝ × Ξ → ℝ} (hU : ContDiff ℝ 3 U) :
    Differentiable ℝ (fun y => dYY U (y, 0)) := by
  have h : ContDiff ℝ 1 (fun y : ℝ => fderiv ℝ (fderiv ℝ U) (y, (0 : Ξ))) :=
    ((hU.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).comp
      (contDiff_id.prodMk contDiff_const)
  exact ((h.clm_apply contDiff_const).clm_apply contDiff_const).differentiable (by norm_num)

/-- Woodford (2003), (2.6), p. 393 and (E.2) (**the coefficients move by `O(ε)`**): along
`Ȳ_b − Y* = O(ε)`, the weight `Ȳ_bu_c(Ȳ_b)` and the elasticity `−Ȳ_bu_cc(Ȳ_b)/u_c(Ȳ_b)` move by
`O(ε)` from their values at `Y*` (`u_c(Y*) ≠ 0`). -/
theorem coeff_move {U : ℝ × Ξ → ℝ} (hU : ContDiff ℝ 3 U) {Ys : ℝ}
    (huc : dY U (Ys, 0) ≠ 0) {Yb : B → ℝ} (hs : Tendsto s L (𝓝 0))
    (h1 : (fun b => Yb b - Ys) =O[L] fun b => s b ^ 1) :
    (fun b => Yb b * dY U (Yb b, 0) - Ys * dY U (Ys, 0)) =O[L] (fun b => s b ^ 1) ∧
      (fun b => Yb b * dYY U (Yb b, 0) / dY U (Yb b, 0) - Ys * dYY U (Ys, 0) / dY U (Ys, 0))
        =O[L] fun b => s b ^ 1 := by
  have hT : Tendsto Yb L (𝓝 Ys) := by
    have := (tendsto_of_o_one hs h1).add_const Ys
    simpa using this
  have hD : HasDerivAt (fun y => dY U (y, 0)) (dYY U (Ys, 0)) Ys :=
    hasDerivAt_dY (hU.of_le (by norm_num)) Ys
  have hDD : DifferentiableAt ℝ (fun y => dYY U (y, 0)) Ys := differentiable_dYY hU Ys
  refine ⟨((((hasDerivAt_id' Ys).mul hD).isBigO_sub).comp_tendsto hT).trans h1, ?_⟩
  exact (((((hasDerivAt_id' Ys).mul hDD.hasDerivAt).div hD huc).isBigO_sub).comp_tendsto
    hT).trans h1

/-- **Woodford (2003), Proposition 6.10, (4.24), p. 436, with every coefficient at the
distorted steady state.** Under the hypotheses of `prop610_distorted` (with `σ⁻¹, ω ≠ 0`), let
the coefficients and composite disturbances be those of `Ȳ_b`: `σ⁻¹_b = −Ȳ_bu_cc/u_c`,
`ω_b = Ȳ_bv_yy/v_y` and `g_{b}`, `q_{j,b}` defined by `u_{cξ}ξ = σ⁻¹_bu_cg_b`,
`v_{yξ}ξ_j = −ω_bv_yq_{j,b}`, all at `(Ȳ_b, 0)`. Then the actual period utility is
`t.i.p. − ½Ȳ_bu_c(Ȳ_b)·loss610Φ(σ⁻¹_b, ω_b, g_b, q_{j,b}) + O(ε³)`, the target being
`Ŷ − Ŷⁿ_b − x*_b`, `x*_b = Φ_b/(σ⁻¹_b + ω_b)`. -/
theorem prop610_distorted_local {ι : Type*} [Fintype ι] (hs : Tendsto s L (𝓝 0)) {n1 η θ : ℝ}
    (hn0 : 0 < n1) (hn1 : n1 < 1) (hη : 0 < η) (hη1 : η ≠ 1) (hθ : θ ≠ 1) {w1 w2 : ι → ℝ}
    (hw10 : ∀ i, 0 ≤ w1 i) (hw11 : ∑ i, w1 i = 1) (hw20 : ∀ i, 0 ≤ w2 i)
    (hw21 : ∑ i, w2 i = 1) {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    {Ys σi ω : ℝ} (hY : 0 < Ys) (hσω : σi + ω ≠ 0) (hηω : η⁻¹ + ω ≠ 0) (hσ0 : σi ≠ 0)
    (hω0 : ω ≠ 0) (huc : dY u (Ys, 0) ≠ 0)
    (hucc : dYY u (Ys, 0) = -(σi * dY u (Ys, 0) / Ys))
    (hvy : dY v (Ys, 0) = dY u (Ys, 0))
    (hvyy : dYY v (Ys, 0) = ω * dY v (Ys, 0) / Ys)
    {Yb Phi σb ωb : B → ℝ} (hYb0 : ∀ b, 0 < Yb b) (hYb : Tendsto Yb L (𝓝 Ys))
    (hFOC : ∀ b, dY v (Yb b, 0) = (1 - Phi b) * dY u (Yb b, 0))
    (hPhi : Phi =O[L] fun b => s b ^ 1)
    (hσb : ∀ b, dYY u (Yb b, 0) = -(σb b * dY u (Yb b, 0) / Yb b))
    (hωb : ∀ b, dYY v (Yb b, 0) = ωb b * dY v (Yb b, 0) / Yb b)
    {yd1 yd2 : B → ι → ℝ} {f1 f2 g q1 q2 gb q1b q2b : B → ℝ} {xu xv1 xv2 : B → Ξ}
    (hnorm : ∀ b, n1 * Real.exp (f1 b) + (1 - n1) * Real.exp (f2 b) = 1)
    (hg : ∀ b, dYXi u (Ys, 0) (xu b) = σi * dY u (Ys, 0) * g b)
    (hq1 : ∀ b, dYXi v (Ys, 0) (xv1 b) = -(ω * dY v (Ys, 0) * q1 b))
    (hq2 : ∀ b, dYXi v (Ys, 0) (xv2 b) = -(ω * dY v (Ys, 0) * q2 b))
    (hgb : ∀ b, dYXi u (Yb b, 0) (xu b) = σb b * dY u (Yb b, 0) * gb b)
    (hq1b : ∀ b, dYXi v (Yb b, 0) (xv1 b) = -(ωb b * dY v (Yb b, 0) * q1b b))
    (hq2b : ∀ b, dYXi v (Yb b, 0) (xv2 b) = -(ωb b * dY v (Yb b, 0) * q2b b))
    (hyd1 : yd1 =O[L] fun b => s b ^ 1) (hyd2 : yd2 =O[L] fun b => s b ^ 1)
    (hf1 : f1 =O[L] fun b => s b ^ 1) (hf2 : f2 =O[L] fun b => s b ^ 1)
    (hgO : g =O[L] fun b => s b ^ 1) (hq1O : q1 =O[L] fun b => s b ^ 1)
    (hq2O : q2 =O[L] fun b => s b ^ 1) (hxu : xu =O[L] fun b => s b ^ 1)
    (hxv1 : xv1 =O[L] fun b => s b ^ 1) (hxv2 : xv2 =O[L] fun b => s b ^ 1) :
    (fun b => periodU2 u v n1 η θ (Yb b) w1 w2 (f1 b) (f2 b) (yd1 b) (yd2 b) (xu b) (xv1 b)
        (xv2 b) -
      ((tip2 u v n1 Ys (xu b) (xv1 b) (xv2 b) + Ys * dY u (Ys, 0) *
        TwoSectorWelfare.tip610 σi ω η⁻¹ n1 0 (g b) (q1 b) (q2 b) (f2 b - f1 b)
          (tauAgg η⁻¹ n1 (f1 b) (f2 b))) -
        Yb b * dY u (Yb b, 0) * loss610Phi (σb b) (ωb b) θ⁻¹ η⁻¹ n1 (Phi b) (gb b) (q1b b)
          (q2b b) (f2 b - f1 b)
          (logY2 n1 η (Yb b) (f1 b) (f2 b) (logYidx w1 θ (yd1 b)) (logYidx w2 θ (yd2 b)))
          (logYidx w1 θ (yd1 b)) (logYidx w2 θ (yd2 b)) (crossVar w1 (yd1 b))
          (crossVar w2 (yd2 b)) / 2)) =O[L] fun b => s b ^ 3 := by
  have hW := prop610_distorted hs hn0 hn1 hη hη1 hθ hw10 hw11 hw20 hw21 hu hv hY hσω hηω huc
    hucc hvy hvyy hYb0 hYb hFOC hPhi hnorm hg hq1 hq2 hyd1 hyd2 hf1 hf2 hgO hq1O hq2O hxu hxv1
    hxv2
  -- `Ȳ_b − Y* = O(ε)`
  obtain ⟨hc, -⟩ := distorted_ss hs hu hv hY hσω huc hucc hvy hvyy hYb hFOC hPhi
  have haO : (fun b => Yb b - Ys) =O[L] fun b => s b ^ 1 := by
    have h0 := (Real.hasDerivAt_exp 0).isBigO_sub.comp_tendsto (tendsto_of_o_one hs hc)
    have h : (fun b => Real.exp (Real.log (Yb b / Ys)) - 1) =O[L] fun b => s b ^ 1 :=
      (h0.congr (fun b => by simp) (fun b => by simp)).trans hc
    refine (h.const_mul_left Ys).congr_left fun b => ?_
    rw [Real.exp_log (div_pos (hYb0 b) hY)]
    field_simp
  -- the coefficients
  have hvc : dY v (Ys, 0) ≠ 0 := by rw [hvy]; exact huc
  obtain ⟨hK, hσr⟩ := coeff_move hu huc hs haO
  obtain ⟨-, hωr⟩ := coeff_move hv hvc hs haO
  have hT : Tendsto Yb L (𝓝 Ys) := hYb
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by norm_num)
  have hucT : Tendsto (fun b => dY u (Yb b, 0)) L (𝓝 (dY u (Ys, 0))) :=
    (hasDerivAt_dY hu2 Ys).continuousAt.tendsto.comp hT
  have hvcT : Tendsto (fun b => dY v (Yb b, 0)) L (𝓝 (dY v (Ys, 0))) :=
    (hasDerivAt_dY hv2 Ys).continuousAt.tendsto.comp hT
  have hσbO : (fun b => σb b - σi) =O[L] fun b => s b ^ 1 := by
    refine (hσr.neg_left).congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [hucT.eventually_ne huc] with b hb
    have e := hσb b
    have hYb' := (hYb0 b).ne'
    rw [hucc]
    field_simp at e ⊢
    linear_combination -e
  have hωbO : (fun b => ωb b - ω) =O[L] fun b => s b ^ 1 := by
    refine hωr.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [hvcT.eventually_ne hvc] with b hb
    have e := hωb b
    have hYb' := (hYb0 b).ne'
    rw [hvyy]
    field_simp at e ⊢
    linear_combination e
  -- the composite disturbances
  have hucO : (fun b => dY u (Yb b, 0) - dY u (Ys, 0)) =O[L] fun b => s b ^ 1 :=
    ((hasDerivAt_dY hu2 Ys).isBigO_sub.comp_tendsto hT).trans haO
  have hvcO : (fun b => dY v (Yb b, 0) - dY v (Ys, 0)) =O[L] fun b => s b ^ 1 :=
    ((hasDerivAt_dY hv2 Ys).isBigO_sub.comp_tendsto hT).trans haO
  have hσbB : σb =O[L] (fun _ => (1 : ℝ)) :=
    ((o_weaken hs (by norm_num : 0 ≤ 1) hσbO).add (isBigO_const_const σi one_ne_zero L)
      |>.congr_right fun b => by ring).congr_left fun b => by ring
  have hωbB : ωb =O[L] (fun _ => (1 : ℝ)) :=
    ((o_weaken hs (by norm_num : 0 ≤ 1) hωbO).add (isBigO_const_const ω one_ne_zero L)
      |>.congr_right fun b => by ring).congr_left fun b => by ring
  have hab : (fun b => σb b * dY u (Yb b, 0) - σi * dY u (Ys, 0)) =O[L] fun b => s b ^ 1 :=
    (((hσbB.mul hucO).congr_right fun b => by ring).add
      (hσbO.const_mul_left (dY u (Ys, 0)))).congr_left fun b => by ring
  have hav : (fun b => -(ωb b * dY v (Yb b, 0)) - -(ω * dY v (Ys, 0))) =O[L]
      fun b => s b ^ 1 :=
    (((hωbB.mul hvcO).congr_right fun b => by ring).add
      (hωbO.const_mul_left (dY v (Ys, 0)))).neg_left.congr_left fun b => by ring
  have hXi : ∀ {U : ℝ × Ξ → ℝ} (_ : ContDiff ℝ 3 U) {ξ : B → Ξ}
      (_ : ξ =O[L] fun b => s b ^ 1),
      (fun b => dYXi U (Yb b, 0) (ξ b) - dYXi U (Ys, 0) (ξ b)) =O[L] fun b => s b ^ 2 :=
    fun hU _ hξ => (dYXi_move hU hT _).trans (o_mul haO hξ.norm_left (by norm_num : 1 + 1 = 2))
  have hgbd := div_move hs (mul_ne_zero hσ0 huc) hab hgO
    (xb := gb) ((hXi hu hxu).congr_left fun b => by rw [hgb, hg])
  have hq1bd := div_move hs (neg_ne_zero.2 (mul_ne_zero hω0 hvc)) hav hq1O (xb := q1b)
    ((hXi hv hxv1).congr_left fun b => by rw [hq1b, hq1]; ring)
  have hq2bd := div_move hs (neg_ne_zero.2 (mul_ne_zero hω0 hvc)) hav hq2O (xb := q2b)
    ((hXi hv hxv2).congr_left fun b => by rw [hq2b, hq2]; ring)
  -- the loss
  have hY1O := logYidx_o hs hw10 hw11 hθ hyd1
  have hY2O := logYidx_o hs hw20 hw21 hθ hyd2
  have hYdO : (fun b => logY2 n1 η (Yb b) (f1 b) (f2 b) (logYidx w1 θ (yd1 b))
      (logYidx w2 θ (yd2 b))) =O[L] fun b => s b ^ 1 := by
    have hτO : (fun b => tauAgg η⁻¹ n1 (f1 b) (f2 b)) =O[L] fun b => s b ^ 2 :=
      (((S_o hs hf1 hf2 hnorm).const_mul_left ((1 - η⁻¹)⁻¹ * η⁻¹)).add
        ((o_pow (hf2.sub hf1) 2).const_mul_left
          (n1 * (1 - n1) * (1 - η⁻¹)⁻¹ * (η⁻¹) ^ 2 / 2))).congr_left
          fun b => by simp only [tauAgg]
    have hdY := hY2O.sub hY1O
    have hET : (fun b => TwoSectorWelfare.ET η⁻¹ n1 (f2 b - f1 b) (logYidx w1 θ (yd1 b))
        (logYidx w2 θ (yd2 b)) (tauAgg η⁻¹ n1 (f1 b) (f2 b))) =O[L] fun b => s b ^ 2 :=
      ((((o_mul (hf2.sub hf1) hdY (by norm_num : 1 + 1 = 2)).const_mul_left
        (η⁻¹ * n1 * (1 - n1))).add ((o_pow hdY 2).const_mul_left
          (n1 * (1 - n1) * (1 - η⁻¹) / 2))).add hτO).congr_left
            fun b => by unfold TwoSectorWelfare.ET; ring
    have hA := aggAtom_o hs hn0 hn1 hη hη1 hY hf1 hf2 hY1O hY2O (Ybar := Ys)
    refine ((((o_weaken hs (by norm_num : 1 ≤ 3) hA).add ((hY1O.const_mul_left n1).add
      (hY2O.const_mul_left (1 - n1)))).add (o_weaken hs (by norm_num : 1 ≤ 2) hET))).congr_left
        fun b => ?_
    have e := logY2_shift hn0 hn1 hη hη1 hY (hYb0 b) (f1 b) (f2 b) (logYidx w1 θ (yd1 b))
      (logYidx w2 θ (yd2 b)) 0
    simp only [add_zero] at e
    rw [e]
    simp only [aggAtom]
    ring
  have hV1 := crossVar_o hw10 hw11 hyd1
  have hV2 := crossVar_o hw20 hw21 hyd2
  have hLm := loss610Phi_move hs hσω hηω (θi := θ⁻¹) (n1 := n1) hσbO hωbO hgbd hq1bd hq2bd hPhi
    hgO hq1O hq2O (hf2.sub hf1) hYdO hY1O hY2O hV1 hV2
  have hLo := loss610Phi_o σi ω θ⁻¹ η⁻¹ n1 hPhi hgO hq1O hq2O (hf2.sub hf1) hYdO hY1O hY2O hV1 hV2
  have hKB : (fun b => Yb b * dY u (Yb b, 0)) =O[L] (fun _ => (1 : ℝ)) :=
    ((o_weaken hs (by norm_num : 0 ≤ 1) hK).add
      (isBigO_const_const (Ys * dY u (Ys, 0)) one_ne_zero L)
      |>.congr_right fun b => by ring).congr_left fun b => by ring
  have hKL := ((hKB.mul hLm).congr_right (fun b => by ring)).add
    (o_mul hK hLo (by norm_num : 1 + 2 = 3))
  refine (hW.add (hKL.const_mul_left (1 / 2))).congr_left fun b => ?_
  ring

end Woodford.StabilizationWelfare.TidyR5DistortedLocal
