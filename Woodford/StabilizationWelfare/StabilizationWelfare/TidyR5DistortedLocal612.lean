/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR5DistortedLocal
import StabilizationWelfare.TidyR5Distorted612

/-!
# Proposition 6.12 with the coefficients of the distorted steady state

Woodford (2003), *Interest and Prices*, Chapter 6, §4.4, Proposition 6.12, (4.28), p. 444, and
Appendix E.8, (E.33)–(E.36), pp. 707–708: every coefficient of the loss (`σ⁻¹`, `ν = H̄v_hh/v_h`,
`φ_h`, `ω_p`, `ω = ω_p + νφ_h`, the disturbances `g`, `h̄` and the weight `Ȳu_c`) is evaluated at
the distorted steady state.

`TidyR5Distorted612.prop612_distorted` keeps the coefficients of the efficient point. Here every
coefficient is re-evaluated at `(Ȳ_b, H̄_b)` with the renormalised labour requirement
`G_b(z) = G(z + c_b)/G(c_b)`: `φ_{h,b} = G′(c_b)/G(c_b)`,
`φ_{h,b}(1 + ω_{p,b}) = G″(c_b)/G(c_b)`, and the expansion changes by `O(ε³)` only
(**`prop612_distorted_local`**).

* `bdd_move`, `mul_move1`, `quot_move1`: products and quotients of `O(ε)`-moving coefficients.
* `loss612Phi_o`, `loss612Phi_move`: the loss is `O(ε²)`, and `O(ε)`-moved coefficients with
  `O(ε²)`-moved disturbances change it by `O(ε³)`.
-/

namespace Woodford.StabilizationWelfare.TidyR5DistortedLocal612

open Filter Topology Asymptotics
open BridgeExtensions TidyR5DistortedTools TidyR5Distorted610 TidyR5Distorted612
  TidyR5DistortedLocal
open ExpLogCES (crossVar)

variable {B : Type*} {L : Filter B} {s : B → ℝ}

/-! ## Moving coefficients -/

/-- Woodford (2003), App. E: a coefficient within `O(ε)` of a constant is bounded. -/
theorem bdd_move (hs : Tendsto s L (𝓝 0)) {A : ℝ} {Ab : B → ℝ}
    (h : (fun b => Ab b - A) =O[L] fun b => s b ^ 1) : Ab =O[L] fun _ => (1 : ℝ) :=
  ((o_weaken hs (by norm_num : 0 ≤ 1) h).add (isBigO_const_const A one_ne_zero L)
    |>.congr_right fun b => by ring).congr_left fun b => by ring

/-- Woodford (2003), App. E: the product of two `O(ε)`-moving coefficients moves by `O(ε)`. -/
theorem mul_move1 (hs : Tendsto s L (𝓝 0)) {A C : ℝ} {Ab Cb : B → ℝ}
    (hA : (fun b => Ab b - A) =O[L] fun b => s b ^ 1)
    (hC : (fun b => Cb b - C) =O[L] fun b => s b ^ 1) :
    (fun b => Ab b * Cb b - A * C) =O[L] fun b => s b ^ 1 :=
  ((((bdd_move hs hA).mul hC).congr_right fun b => by ring).add
    (hA.const_mul_left C)).congr_left fun b => by ring

/-- Woodford (2003), App. E: the quotient of two `O(ε)`-moving coefficients moves by `O(ε)` when
the limit denominator is nonzero. -/
theorem quot_move1 (hs : Tendsto s L (𝓝 0)) {A D : ℝ} (hD : D ≠ 0) {Ab Db : B → ℝ}
    (hA : (fun b => Ab b - A) =O[L] fun b => s b ^ 1)
    (hDb : (fun b => Db b - D) =O[L] fun b => s b ^ 1) :
    (fun b => Ab b / Db b - A / D) =O[L] fun b => s b ^ 1 := by
  obtain ⟨h1, h2⟩ := inv_move hs hD hDb
  refine ((mul_move1 hs hA (h2 : (fun b => (Db b)⁻¹ - D⁻¹) =O[L] _))).congr_left fun b => ?_
  simp only [div_eq_mul_inv]

/-! ## The loss of Proposition 6.12 -/

/-- Woodford (2003), (4.28)/(E.33): `loss612Phi` is `O(ε²)` when its first-order arguments are
`O(ε)` and the dispersions `O(ε²)`. -/
theorem loss612Phi_o (σi ω ν θp ωp θw φh : ℝ) {Phi g a hb Y Vp Vw : B → ℝ}
    (hPhi : Phi =O[L] fun b => s b ^ 1) (hg : g =O[L] fun b => s b ^ 1)
    (ha : a =O[L] fun b => s b ^ 1) (hhb : hb =O[L] fun b => s b ^ 1)
    (hY : Y =O[L] fun b => s b ^ 1) (hVp : Vp =O[L] fun b => s b ^ 2)
    (hVw : Vw =O[L] fun b => s b ^ 2) :
    (fun b => loss612Phi σi ω ν θp ωp θw φh (Phi b) (g b) (a b) (hb b) (Y b) (Vp b) (Vw b))
      =O[L] fun b => s b ^ 2 := by
  have z : (fun b => Y b - Prop61.xStarLin σi ω (Phi b) -
      StickyWageWelfare.natY612 σi ω ν (g b) (a b) (hb b)) =O[L] fun b => s b ^ 1 :=
    ((hY.sub (hPhi.const_mul_left (σi + ω)⁻¹)).sub ((((hg.const_mul_left σi).add
      (ha.const_mul_left (1 + ω))).add (hhb.const_mul_left ν)).const_mul_left
        (σi + ω)⁻¹)).congr_left fun b => by
      simp only [Prop61.xStarLin, StickyWageWelfare.natY612]; ring
  refine (((o_pow z 2).const_mul_left (σi + ω)).add (hVp.const_mul_left
    (θp * (1 + ωp * θp))) |>.add (hVw.const_mul_left (θw / φh * (1 + ν * θw)))).congr_left
      fun b => ?_
  simp only [loss612Phi, loss612]

/-- Woodford (2003), (4.28) and (E.33) (**coefficients at the distorted point**): if the
coefficients `σ⁻¹, ω, ν, ω_p, φ_h` move by `O(ε)` (`φ_h ≠ 0`) and the disturbances `g, h̄` by
`O(ε²)`, the loss `loss612Phi` (including its target `x* = Φ/(σ⁻¹ + ω)`) changes by `O(ε³)`. -/
theorem loss612Phi_move (hs : Tendsto s L (𝓝 0)) {σi ω ν θp ωp θw φh : ℝ}
    (hσω : σi + ω ≠ 0) (hφ : φh ≠ 0) {σb ωb νb ωpb φhb Phi g a hb gb hbb Y Vp Vw : B → ℝ}
    (hσb : (fun b => σb b - σi) =O[L] fun b => s b ^ 1)
    (hωb : (fun b => ωb b - ω) =O[L] fun b => s b ^ 1)
    (hνb : (fun b => νb b - ν) =O[L] fun b => s b ^ 1)
    (hωpb : (fun b => ωpb b - ωp) =O[L] fun b => s b ^ 1)
    (hφb : (fun b => φhb b - φh) =O[L] fun b => s b ^ 1)
    (hgb : (fun b => gb b - g b) =O[L] fun b => s b ^ 2)
    (hhbb : (fun b => hbb b - hb b) =O[L] fun b => s b ^ 2)
    (hPhi : Phi =O[L] fun b => s b ^ 1) (hg : g =O[L] fun b => s b ^ 1)
    (ha : a =O[L] fun b => s b ^ 1) (hhb : hb =O[L] fun b => s b ^ 1)
    (hY : Y =O[L] fun b => s b ^ 1) (hVp : Vp =O[L] fun b => s b ^ 2)
    (hVw : Vw =O[L] fun b => s b ^ 2) :
    (fun b => loss612Phi (σb b) (ωb b) (νb b) θp (ωpb b) θw (φhb b) (Phi b) (gb b) (a b)
        (hbb b) (Y b) (Vp b) (Vw b) -
      loss612Phi σi ω ν θp ωp θw φh (Phi b) (g b) (a b) (hb b) (Y b) (Vp b) (Vw b))
      =O[L] fun b => s b ^ 3 := by
  have hDb : (fun b => (σb b + ωb b) - (σi + ω)) =O[L] fun b => s b ^ 1 :=
    (hσb.add hωb).congr_left fun b => by ring
  have hNO : (fun b => σi * g b + (1 + ω) * a b + ν * hb b) =O[L] fun b => s b ^ 1 :=
    ((hg.const_mul_left σi).add (ha.const_mul_left (1 + ω))).add (hhb.const_mul_left ν)
  have hNbd : (fun b => (σb b * gb b + (1 + ωb b) * a b + νb b * hbb b) -
      (σi * g b + (1 + ω) * a b + ν * hb b)) =O[L] fun b => s b ^ 2 :=
    ((((((bdd_move hs hσb).mul hgb).congr_right fun b => by ring).add
      (o_mul hσb hg (by norm_num : 1 + 1 = 2))).add (o_mul hωb ha (by norm_num : 1 + 1 = 2))).add
      ((((bdd_move hs hνb).mul hhbb).congr_right fun b => by ring).add
        (o_mul hνb hhb (by norm_num : 1 + 1 = 2)))).congr_left fun b => by ring
  have hnat := ratio_move hs hσω hDb hNO hNbd
  have hx := ratio_move hs hσω hDb hPhi ((isBigO_zero _ _).congr_left fun b => by ring :
    (fun b => Phi b - Phi b) =O[L] fun b => s b ^ 2)
  have hz : (fun b => (Y b - Prop61.xStarLin (σb b) (ωb b) (Phi b) -
      StickyWageWelfare.natY612 (σb b) (ωb b) (νb b) (gb b) (a b) (hbb b)) -
      (Y b - Prop61.xStarLin σi ω (Phi b) -
        StickyWageWelfare.natY612 σi ω ν (g b) (a b) (hb b))) =O[L] fun b => s b ^ 2 :=
    (hx.add hnat).neg_left.congr_left fun b => by
      simp only [Prop61.xStarLin, StickyWageWelfare.natY612]; ring
  have hz' : (fun b => Y b - Prop61.xStarLin σi ω (Phi b) -
      StickyWageWelfare.natY612 σi ω ν (g b) (a b) (hb b)) =O[L] fun b => s b ^ 1 :=
    ((hY.sub (hPhi.const_mul_left (σi + ω)⁻¹)).sub (hNO.const_mul_left (σi + ω)⁻¹)).congr_left
      fun b => by simp only [Prop61.xStarLin, StickyWageWelfare.natY612]; ring
  have t1 := sq_move (c := fun b => σb b + ωb b) (c' := fun _ => σi + ω) hs hDb
    (isBigO_const_const (σi + ω) one_ne_zero L) hz hz'
  have t2 := mul_move (c := fun b => θp * (1 + ωpb b * θp)) (c' := fun _ => θp * (1 + ωp * θp))
    ((hωpb.const_mul_left (θp ^ 2)).congr_left fun b => by ring) hVp
  have hcw : (fun b => θw / φhb b * (1 + νb b * θw) - θw / φh * (1 + ν * θw)) =O[L]
      fun b => s b ^ 1 :=
    (quot_move1 hs hφ ((mul_move1 hs (isBigO_zero _ _ |>.congr_left fun b => by ring :
      (fun b => θw - θw) =O[L] fun b => s b ^ 1) ((hνb.const_mul_left θw).congr_left
        fun b => by ring : (fun b => (1 + νb b * θw) - (1 + ν * θw)) =O[L] _))) hφb).congr_left
      fun b => by ring
  have t3 := mul_move (c := fun b => θw / φhb b * (1 + νb b * θw))
    (c' := fun _ => θw / φh * (1 + ν * θw)) hcw hVw
  refine ((t1.add t2).add t3).congr_left fun b => ?_
  simp only [loss612Phi, loss612]
  ring

/-! ## The coefficients at the distorted steady state -/

variable {Ξ : Type*} [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]
variable {ι : Type*} [Fintype ι] {J : Type*} [Fintype J]

/-- **Woodford (2003), Proposition 6.12, (4.28), p. 444, with every coefficient at the distorted
steady state.** Under the hypotheses of `prop612_distorted` (with `σ⁻¹, ν ≠ 0`, `H* > 0`), let
`c_b = log(Ȳ_b/Y*)`, `H̄_b = H*G(c_b)` and let the coefficients be those of `(Ȳ_b, H̄_b)`:
`u_cc = −σ⁻¹_bu_c/Ȳ_b`, `v_hh = ν_bv_h/H̄_b`, `φ_{h,b} = G′(c_b)/G(c_b)`,
`G″(c_b)/G(c_b) = φ_{h,b}(1 + ω_{p,b})`, `ω_b = ω_{p,b} + ν_bφ_{h,b}`, and the disturbances
`g_{b}`, `h̄_b` defined by `u_{cξ}ξ = σ⁻¹_bu_cg_b`, `v_{hξ}ξ = −ν_bv_hh̄_b` at `(Ȳ_b, H̄_b)`.
Then the actual period utility is `t.i.p. − ½Ȳ_bu_c(Ȳ_b)·loss612Φ(local coefficients) + O(ε³)`. -/
theorem prop612_distorted_local (hs : Tendsto s L (𝓝 0)) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {ωt : J → ℝ} (hωt0 : ∀ j, 0 ≤ ωt j) (hωt1 : ∑ j, ωt j = 1)
    {θp θw : ℝ} (hθp : θp ≠ 0) (hθp1 : θp ≠ 1) (hθw1 : θw ≠ 1)
    {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 3 G) (hG0 : G 0 = 1) (hGpos : ∀ z, 0 < G z)
    {σi ω ν ωp φh Ys Hs : ℝ}
    (hG1 : fderiv ℝ G 0 1 = φh) (hG2 : fderiv ℝ (fderiv ℝ G) 0 1 1 = φh * (1 + ωp))
    (hω : ω = ωp + ν * φh) (hφ : φh ≠ 0) (hσω : σi + ω ≠ 0) (hYs : 0 < Ys) (hHs : 0 < Hs)
    (hσ0 : σi ≠ 0) (hν0 : ν ≠ 0)
    (huc : dY u (Ys, 0) ≠ 0) (hucc : dYY u (Ys, 0) = -(σi * dY u (Ys, 0) / Ys))
    (hvhh : dYY v (Hs, 0) = ν * dY v (Hs, 0) / Hs)
    (hss : Hs * dY v (Hs, 0) * φh = Ys * dY u (Ys, 0))
    {Yb Phi σb νb φhb ωpb : B → ℝ} (hYb0 : ∀ b, 0 < Yb b) (hYb : Tendsto Yb L (𝓝 Ys))
    (hFOC : ∀ b, Hs * G (Real.log (Yb b / Ys)) * dY v (Hs * G (Real.log (Yb b / Ys)), 0) *
      (deriv G (Real.log (Yb b / Ys)) / G (Real.log (Yb b / Ys))) =
        (1 - Phi b) * Yb b * dY u (Yb b, 0))
    (hPhi : Phi =O[L] fun b => s b ^ 1)
    (hσb : ∀ b, dYY u (Yb b, 0) = -(σb b * dY u (Yb b, 0) / Yb b))
    (hνb : ∀ b, dYY v (Hs * G (Real.log (Yb b / Ys)), 0) =
      νb b * dY v (Hs * G (Real.log (Yb b / Ys)), 0) / (Hs * G (Real.log (Yb b / Ys))))
    (hφb : ∀ b, φhb b = deriv G (Real.log (Yb b / Ys)) / G (Real.log (Yb b / Ys)))
    (hωpb : ∀ b, fderiv ℝ (fderiv ℝ G) (Real.log (Yb b / Ys)) 1 1 / G (Real.log (Yb b / Ys)) =
      φhb b * (1 + ωpb b))
    {yd : B → ι → ℝ} {lw : B → J → ℝ} {a g hb gb hbb : B → ℝ} {xu xv : B → Ξ}
    (hg : ∀ b, dYXi u (Ys, 0) (xu b) = σi * dY u (Ys, 0) * g b)
    (hhb : ∀ b, dYXi v (Hs, 0) (xv b) = -(ν * dY v (Hs, 0) * hb b))
    (hgb : ∀ b, dYXi u (Yb b, 0) (xu b) = σb b * dY u (Yb b, 0) * gb b)
    (hhbb : ∀ b, dYXi v (Hs * G (Real.log (Yb b / Ys)), 0) (xv b) =
      -(νb b * dY v (Hs * G (Real.log (Yb b / Ys)), 0) * hbb b))
    (hyd : yd =O[L] fun b => s b ^ 1) (hlw : lw =O[L] fun b => s b ^ 1)
    (ha : a =O[L] fun b => s b ^ 1) (hgO : g =O[L] fun b => s b ^ 1)
    (hhbO : hb =O[L] fun b => s b ^ 1) (hxu : xu =O[L] fun b => s b ^ 1)
    (hxv : xv =O[L] fun b => s b ^ 1) :
    (fun b => periodU12 u v w ωt θp θw (Yb b) (Hs * G (Real.log (Yb b / Ys)))
        (fun z => G (z + Real.log (Yb b / Ys)) / G (Real.log (Yb b / Ys))) (a b) (yd b) (lw b)
        (xu b) (xv b) -
      ((tip12 u v Ys Hs (xu b) (xv b) + Ys * dY u (Ys, 0) *
        StickyWageWelfare.tip612 σi ω ν 0 (g b) (a b) (hb b)) -
        Yb b * dY u (Yb b, 0) * loss612Phi (σb b) (ωpb b + νb b * φhb b) (νb b) θp (ωpb b) θw
          (φhb b) (Phi b) (gb b) (a b) (hbb b) (logYidx w θp (yd b))
          (crossVar w (yd b) / θp ^ 2) (crossVar ωt (lw b)) / 2)) =O[L] fun b => s b ^ 3 := by
  have hW := prop612_distorted hs hw0 hw1 hωt0 hωt1 hθp hθp1 hθw1 hu hv hG hG0 hGpos hG1 hG2 hω
    hφ hσω hYs huc hucc hvhh hss hYb0 hYb hFOC hPhi hg hhb hyd hlw ha hgO hhbO hxu hxv
  obtain ⟨hc, -⟩ := distorted_ss612 hu hv hG hG0 hGpos hG1 hG2 hω hσω hYs huc hucc hvhh hss
    hYb0 hYb hFOC hPhi
  set c := fun b => Real.log (Yb b / Ys) with hcd
  set Hb := fun b => Hs * G (c b) with hHbd
  have hc0 : Tendsto c L (𝓝 0) := tendsto_of_o_one hs hc
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by norm_num)
  have hvh0 : dY v (Hs, 0) ≠ 0 := fun h => by
    have := hss; rw [h, mul_zero, zero_mul] at this
    exact mul_ne_zero hYs.ne' huc this.symm
  -- `Ȳ_b − Y* = O(ε)` and `H̄_b − H* = O(ε)`
  have haO : (fun b => Yb b - Ys) =O[L] fun b => s b ^ 1 := by
    have h0 := (Real.hasDerivAt_exp 0).isBigO_sub.comp_tendsto hc0
    have h : (fun b => Real.exp (c b) - 1) =O[L] fun b => s b ^ 1 :=
      (h0.congr (fun b => by simp) (fun b => by simp)).trans hc
    refine (h.const_mul_left Ys).congr_left fun b => ?_
    simp only [hcd]
    rw [Real.exp_log (div_pos (hYb0 b) hYs)]
    field_simp
  have hGd : DifferentiableAt ℝ G 0 := hG.differentiable (by norm_num) 0
  have hHO : (fun b => Hb b - Hs) =O[L] fun b => s b ^ 1 := by
    have h := (hGd.hasDerivAt.isBigO_sub.comp_tendsto hc0).trans
      (hc.congr_left fun b => by simp)
    refine (h.const_mul_left Hs).congr_left fun b => ?_
    simp only [hHbd, Function.comp_apply, hG0]; ring
  have hYT : Tendsto Yb L (𝓝 Ys) := hYb
  have hHT : Tendsto Hb L (𝓝 Hs) := by
    have := (tendsto_of_o_one hs hHO).add_const Hs
    simpa using this
  -- the coefficients
  obtain ⟨hK, hσr⟩ := coeff_move hu huc hs haO
  obtain ⟨-, hνr⟩ := coeff_move hv hvh0 hs hHO
  have hucT : Tendsto (fun b => dY u (Yb b, 0)) L (𝓝 (dY u (Ys, 0))) :=
    (hasDerivAt_dY hu2 Ys).continuousAt.tendsto.comp hYT
  have hvcT : Tendsto (fun b => dY v (Hb b, 0)) L (𝓝 (dY v (Hs, 0))) :=
    (hasDerivAt_dY hv2 Hs).continuousAt.tendsto.comp hHT
  have hσbO : (fun b => σb b - σi) =O[L] fun b => s b ^ 1 := by
    refine (hσr.neg_left).congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [hucT.eventually_ne huc] with b hb
    have e := hσb b
    have hYb' := (hYb0 b).ne'
    rw [hucc]
    field_simp at e ⊢
    linear_combination -e
  have hνbO : (fun b => νb b - ν) =O[L] fun b => s b ^ 1 := by
    refine hνr.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [hvcT.eventually_ne hvh0] with b hb
    have e := hνb b
    have hH' : Hb b ≠ 0 := (mul_pos hHs (hGpos _)).ne'
    simp only [hHbd, hcd] at hb hH' ⊢
    rw [e, hvhh]
    have hG' := (hGpos (Real.log (Yb b / Ys))).ne'
    field_simp
  -- `φ_h` and `ω_p`
  have hG1c : ContDiff ℝ 2 (fun x => fderiv ℝ G x 1) :=
    (hG.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
  have hG2c : ContDiff ℝ 1 (fun x => fderiv ℝ (fderiv ℝ G) x 1 1) :=
    (((hG.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiff_const).clm_apply contDiff_const
  have hφd : HasDerivAt (fun x => fderiv ℝ G x 1 / G x)
      ((deriv (fun x => fderiv ℝ G x 1) 0 * G 0 - fderiv ℝ G 0 1 * deriv G 0) / G 0 ^ 2) 0 :=
    ((hG1c.differentiable (by norm_num) 0).hasDerivAt).div hGd.hasDerivAt (by rw [hG0]; norm_num)
  have hφbO : (fun b => φhb b - φh) =O[L] fun b => s b ^ 1 := by
    refine ((hφd.isBigO_sub.comp_tendsto hc0).trans (hc.congr_left fun b => by simp)).congr_left
      fun b => ?_
    simp only [Function.comp_apply, hφb, hG0, div_one, hG1]
    rfl
  have hRd : HasDerivAt (fun x => fderiv ℝ (fderiv ℝ G) x 1 1 / G x)
      ((deriv (fun x => fderiv ℝ (fderiv ℝ G) x 1 1) 0 * G 0 -
        fderiv ℝ (fderiv ℝ G) 0 1 1 * deriv G 0) / G 0 ^ 2) 0 :=
    ((hG2c.differentiable (by norm_num) 0).hasDerivAt).div hGd.hasDerivAt
      (by rw [hG0]; norm_num)
  have hRO : (fun b => fderiv ℝ (fderiv ℝ G) (c b) 1 1 / G (c b) - φh * (1 + ωp)) =O[L]
      fun b => s b ^ 1 :=
    ((hRd.isBigO_sub.comp_tendsto hc0).trans (hc.congr_left fun b => by simp)).congr_left
      fun b => by simp only [Function.comp_apply, hG0, div_one, hG2]
  have hωpbO : (fun b => ωpb b - ωp) =O[L] fun b => s b ^ 1 := by
    have hq := quot_move1 hs hφ hRO hφbO
    have hφT : Tendsto φhb L (𝓝 φh) := by
      have := (tendsto_of_o_one hs hφbO).add_const φh
      simpa using this
    refine hq.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [hφT.eventually_ne hφ] with b hb
    rw [hωpb b]
    field_simp
    ring
  have hωbO : (fun b => (ωpb b + νb b * φhb b) - ω) =O[L] fun b => s b ^ 1 :=
    (hωpbO.add (mul_move1 hs hνbO hφbO)).congr_left fun b => by rw [hω]; ring
  -- the composite disturbances
  have hucO : (fun b => dY u (Yb b, 0) - dY u (Ys, 0)) =O[L] fun b => s b ^ 1 :=
    ((hasDerivAt_dY hu2 Ys).isBigO_sub.comp_tendsto hYT).trans haO
  have hvcO : (fun b => dY v (Hb b, 0) - dY v (Hs, 0)) =O[L] fun b => s b ^ 1 :=
    ((hasDerivAt_dY hv2 Hs).isBigO_sub.comp_tendsto hHT).trans hHO
  have hgbd := div_move hs (mul_ne_zero hσ0 huc) (mul_move1 hs hσbO hucO) hgO (xb := gb)
    (((dYXi_move hu hYT xu).trans (o_mul haO hxu.norm_left
      (by norm_num : 1 + 1 = 2))).congr_left fun b => by rw [hgb, hg])
  have hhbbd := div_move hs (neg_ne_zero.2 (mul_ne_zero hν0 hvh0))
    (ab := fun b => -(νb b * dY v (Hb b, 0)))
    ((mul_move1 hs hνbO hvcO).neg_left.congr_left fun b => by ring) hhbO (xb := hbb)
    (((dYXi_move hv hHT xv).trans (o_mul hHO hxv.norm_left
      (by norm_num : 1 + 1 = 2))).congr_left fun b => by
        simp only [hHbd, hcd] at *; rw [hhbb, hhb]; ring)
  -- the loss
  have hYO := logYidx_o hs hw0 hw1 hθp1 hyd
  have hVp : (fun b => crossVar w (yd b) / θp ^ 2) =O[L] fun b => s b ^ 2 :=
    ((crossVar_o hw0 hw1 hyd).const_mul_left (θp ^ 2)⁻¹).congr_left fun b => by ring
  have hVw := crossVar_o hωt0 hωt1 hlw
  have hLm := loss612Phi_move hs hσω hφ (θp := θp) (θw := θw) hσbO hωbO hνbO hωpbO hφbO hgbd
    hhbbd hPhi hgO ha hhbO hYO hVp hVw
  have hLo := loss612Phi_o σi ω ν θp ωp θw φh hPhi hgO ha hhbO hYO hVp hVw
  have hKL := (((bdd_move hs hK).mul hLm).congr_right (fun b => by ring)).add
    (o_mul hK hLo (by norm_num : 1 + 2 = 3))
  refine (hW.add (hKL.const_mul_left (1 / 2))).congr_left fun b => ?_
  ring

end Woodford.StabilizationWelfare.TidyR5DistortedLocal612
