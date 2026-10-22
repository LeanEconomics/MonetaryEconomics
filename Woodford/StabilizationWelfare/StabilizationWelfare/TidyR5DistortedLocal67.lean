/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR5DistortedLocal612
import StabilizationWelfare.TidyR5Distorted67

/-!
# Proposition 6.7 with the coefficients of the distorted steady state

Woodford (2003), *Interest and Prices*, Chapter 6, §4.1, Proposition 6.7, (4.9), p. 422,
(4.4)–(4.6), pp. 420–421, and Appendix E.4, (E.15)–(E.18), pp. 699–700: in the book the coefficients
`σ⁻¹ = −Ȳu_cc/u_c`, `χ = m̄u_cm/u_c`, `(η_iv̄)⁻¹ = −m̄²u_mm/(Ȳu_c)`, `v̄ = Ȳ/m̄`, `ω`, `η_y`, the
disturbances `g`, `εᵐ`, `q` and the weight `Ȳu_c` are those of the DISTORTED steady state.

`TidyR5Distorted67.prop67_distorted` keeps the coefficients of the satiated efficient point. Here
every coefficient is re-evaluated at `(Ȳ_b, m̄_b)` (`η_y` is taken as `χη_iv̄` there, i.e. `e₃ = 0`;
by `loss49_move` any other choice within `O(ε)`, such as the book's `η_y = χη_iv̄ + e₃` with
`e₃ = O(Δ̄)`, gives the same expansion), and the expansion changes by `O(ε³)` only
(**`prop67_distorted_local`**).

* `diff_move`, `d2_move`: values and second derivatives at a moving point.
* `loss49_txDist_eq`, `loss49_o`, `loss49_move`: the loss (4.9) at the distorted point is
  `O(ε²)`, and `O(ε)`-moved coefficients with `O(ε²)`-moved disturbances change it by `O(ε³)`.
-/

namespace Woodford.StabilizationWelfare.TidyR5DistortedLocal67

open Filter Topology Asymptotics
open BridgeExtensions TidyR5DistortedTools TidyR5Distorted610 TidyR5Distorted67
  TidyR5DistortedLocal TidyR5DistortedLocal612
open ExpLogCES (crossVar)

variable {B : Type*} {L : Filter B} {s : B → ℝ}

/-! ## The loss (4.9) with moving coefficients -/

/-- Woodford (2003), (4.4)–(4.6) and (4.9): the loss at the distorted point written out,
`Ω_mc(Ŷ − (σ⁻¹g + ωq + χεᵐ + Φ + s_mη_y)/Ω_mc)² + v̄⁻¹η_i(d + Δ̄)² + (θ⁻¹ + ω)V`. -/
theorem loss49_txDist_eq (σ ω θ χ ηi v ηy Y d g q eps Phi Δ V m : ℝ) :
    Transactions.loss49 ⟨σ, ω, θ, χ, ηi, v, ηy⟩
        (txDist ⟨σ, ω, θ, χ, ηi, v, ηy⟩ Y d g q eps Phi Δ V m) =
      (σ + ω - χ * ηy) * (Y - (σ * g + ω * q + χ * eps + (Phi + Δ / v * ηy)) /
        (σ + ω - χ * ηy)) ^ 2 + ηi / v * (d + Δ) ^ 2 + (θ + ω) * V := by
  simp only [Transactions.loss49, txDist, Transactions.natRate, Transactions.xStar,
    Transactions.sM, Transactions.omegaMC]
  ring

/-- Woodford (2003), (4.9): the loss at the distorted point is `O(ε²)` when its first-order
arguments are `O(ε)` and the dispersion `O(ε²)`. -/
theorem loss49_o (σ ω θ χ ηi v ηy : ℝ) {Y d g q eps Phi Δ V m : B → ℝ}
    (hY : Y =O[L] fun b => s b ^ 1) (hd : d =O[L] fun b => s b ^ 1)
    (hg : g =O[L] fun b => s b ^ 1) (hq : q =O[L] fun b => s b ^ 1)
    (heps : eps =O[L] fun b => s b ^ 1) (hPhi : Phi =O[L] fun b => s b ^ 1)
    (hΔ : Δ =O[L] fun b => s b ^ 1) (hV : V =O[L] fun b => s b ^ 2) :
    (fun b => Transactions.loss49 ⟨σ, ω, θ, χ, ηi, v, ηy⟩
      (txDist ⟨σ, ω, θ, χ, ηi, v, ηy⟩ (Y b) (d b) (g b) (q b) (eps b) (Phi b) (Δ b) (V b) (m b)))
      =O[L] fun b => s b ^ 2 := by
  have hN : (fun b => σ * g b + ω * q b + χ * eps b + (Phi b + Δ b / v * ηy)) =O[L]
      fun b => s b ^ 1 :=
    (((hg.const_mul_left σ).add (hq.const_mul_left ω)).add (heps.const_mul_left χ)).add
      (hPhi.add ((hΔ.const_mul_left (ηy / v)).congr_left fun b => by ring))
  have z : (fun b => Y b - (σ * g b + ω * q b + χ * eps b + (Phi b + Δ b / v * ηy)) /
      (σ + ω - χ * ηy)) =O[L] fun b => s b ^ 1 :=
    (hY.sub (hN.const_mul_left (σ + ω - χ * ηy)⁻¹)).congr_left fun b => by ring
  refine ((((o_pow z 2).const_mul_left (σ + ω - χ * ηy)).add
    ((o_pow (hd.add hΔ) 2).const_mul_left (ηi / v))).add (hV.const_mul_left (θ + ω))).congr_left
      fun b => ?_
  rw [loss49_txDist_eq]

/-- Woodford (2003), (4.9) and (E.16) (**coefficients at the distorted point**): if
`σ⁻¹, ω, χ, η_i, v̄, η_y` move by `O(ε)` (`Ω_mc ≠ 0`, `v̄ ≠ 0`) and `g, q, εᵐ` by `O(ε²)`, the loss
(4.9) at the distorted point (including `x* = (Φ + s_mη_y)/Ω_mc`) changes by `O(ε³)`. -/
theorem loss49_move (hs : Tendsto s L (𝓝 0)) {σ ω θ χ ηi v ηy : ℝ}
    (hΩ : σ + ω - χ * ηy ≠ 0) (hv : v ≠ 0)
    {σb ωb χb ηib vb ηyb Y d g q eps gb qb epsb Phi Δ V m : B → ℝ}
    (hσb : (fun b => σb b - σ) =O[L] fun b => s b ^ 1)
    (hωb : (fun b => ωb b - ω) =O[L] fun b => s b ^ 1)
    (hχb : (fun b => χb b - χ) =O[L] fun b => s b ^ 1)
    (hηib : (fun b => ηib b - ηi) =O[L] fun b => s b ^ 1)
    (hvb : (fun b => vb b - v) =O[L] fun b => s b ^ 1)
    (hηyb : (fun b => ηyb b - ηy) =O[L] fun b => s b ^ 1)
    (hgb : (fun b => gb b - g b) =O[L] fun b => s b ^ 2)
    (hqb : (fun b => qb b - q b) =O[L] fun b => s b ^ 2)
    (hepsb : (fun b => epsb b - eps b) =O[L] fun b => s b ^ 2)
    (hY : Y =O[L] fun b => s b ^ 1) (hd : d =O[L] fun b => s b ^ 1)
    (hg : g =O[L] fun b => s b ^ 1) (hq : q =O[L] fun b => s b ^ 1)
    (heps : eps =O[L] fun b => s b ^ 1) (hPhi : Phi =O[L] fun b => s b ^ 1)
    (hΔ : Δ =O[L] fun b => s b ^ 1) (hV : V =O[L] fun b => s b ^ 2) :
    (fun b => Transactions.loss49 ⟨σb b, ωb b, θ, χb b, ηib b, vb b, ηyb b⟩
        (txDist ⟨σb b, ωb b, θ, χb b, ηib b, vb b, ηyb b⟩ (Y b) (d b) (gb b) (qb b) (epsb b)
          (Phi b) (Δ b) (V b) (m b)) -
      Transactions.loss49 ⟨σ, ω, θ, χ, ηi, v, ηy⟩
        (txDist ⟨σ, ω, θ, χ, ηi, v, ηy⟩ (Y b) (d b) (g b) (q b) (eps b) (Phi b) (Δ b) (V b)
          (m b))) =O[L] fun b => s b ^ 3 := by
  have hDb : (fun b => (σb b + ωb b - χb b * ηyb b) - (σ + ω - χ * ηy)) =O[L]
      fun b => s b ^ 1 :=
    ((hσb.add hωb).sub (mul_move1 hs hχb hηyb)).congr_left fun b => by ring
  have hr : (fun b => ηyb b / vb b - ηy / v) =O[L] fun b => s b ^ 1 := quot_move1 hs hv hηyb hvb
  have hNO : (fun b => σ * g b + ω * q b + χ * eps b + (Phi b + Δ b / v * ηy)) =O[L]
      fun b => s b ^ 1 :=
    (((hg.const_mul_left σ).add (hq.const_mul_left ω)).add (heps.const_mul_left χ)).add
      (hPhi.add ((hΔ.const_mul_left (ηy / v)).congr_left fun b => by ring))
  have hNbd : (fun b => (σb b * gb b + ωb b * qb b + χb b * epsb b + (Phi b + Δ b / vb b * ηyb b))
      - (σ * g b + ω * q b + χ * eps b + (Phi b + Δ b / v * ηy))) =O[L] fun b => s b ^ 2 := by
    have t : ∀ {cb xb x : B → ℝ} {c : ℝ}, (fun b => cb b - c) =O[L] (fun b => s b ^ 1) →
        (fun b => xb b - x b) =O[L] (fun b => s b ^ 2) → x =O[L] (fun b => s b ^ 1) →
        (fun b => cb b * xb b - c * x b) =O[L] fun b => s b ^ 2 := fun hc hxd hx =>
      ((((bdd_move hs hc).mul hxd).congr_right fun b => by ring).add
        (o_mul hc hx (by norm_num : 1 + 1 = 2))).congr_left fun b => by ring
    refine ((((t hσb hgb hg).add (t hωb hqb hq)).add (t hχb hepsb heps)).add
      (o_mul hΔ hr (by norm_num : 1 + 1 = 2))).congr_left fun b => ?_
    simp only [div_eq_mul_inv]
    ring
  have hnat := ratio_move hs hΩ hDb hNO hNbd
  have hz : (fun b => (Y b - (σb b * gb b + ωb b * qb b + χb b * epsb b +
      (Phi b + Δ b / vb b * ηyb b)) / (σb b + ωb b - χb b * ηyb b)) -
      (Y b - (σ * g b + ω * q b + χ * eps b + (Phi b + Δ b / v * ηy)) / (σ + ω - χ * ηy)))
      =O[L] fun b => s b ^ 2 := hnat.neg_left.congr_left fun b => by ring
  have hz' : (fun b => Y b - (σ * g b + ω * q b + χ * eps b + (Phi b + Δ b / v * ηy)) /
      (σ + ω - χ * ηy)) =O[L] fun b => s b ^ 1 :=
    (hY.sub (hNO.const_mul_left (σ + ω - χ * ηy)⁻¹)).congr_left fun b => by ring
  have t1 := sq_move (c := fun b => σb b + ωb b - χb b * ηyb b) (c' := fun _ => σ + ω - χ * ηy)
    hs hDb (isBigO_const_const _ one_ne_zero L) hz hz'
  have t2 := mul_move (c := fun b => ηib b / vb b) (c' := fun _ => ηi / v)
    (quot_move1 hs hv hηib hvb) (V := fun b => (d b + Δ b) ^ 2) (o_pow (hd.add hΔ) 2)
  have t3 := mul_move (c := fun b => θ + ωb b) (c' := fun _ => θ + ω)
    (hωb.congr_left fun b => by ring) hV
  refine ((t1.add t2).add t3).congr_left fun b => ?_
  rw [loss49_txDist_eq, loss49_txDist_eq]
  ring

/-! ## Values and second derivatives at a moving point -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Woodford (2003), App. E: a function differentiable at `z₀` moves by `O(ε)` along
`z_b − z₀ = O(ε)`. -/
theorem diff_move {f : E → ℝ} {z0 : E} (hf : DifferentiableAt ℝ f z0) {zb : B → E}
    (hs : Tendsto s L (𝓝 0)) (hz : (fun b => zb b - z0) =O[L] fun b => s b ^ 1) :
    (fun b => f (zb b) - f z0) =O[L] fun b => s b ^ 1 := by
  have hT : Tendsto zb L (𝓝 z0) := by
    have := (tendsto_of_o_one hs hz).add_const z0
    simpa using this
  exact (hf.hasFDerivAt.isBigO_sub.comp_tendsto hT).trans hz

/-- Woodford (2003), (E.15) at a moving point: for `C³` `Ũ`, the second derivative applied to a
fixed direction and an `O(ε)` disturbance direction moves by `O(ε²)` along `z_b − z₀ = O(ε)`. -/
theorem d2_move {U : E → ℝ} (hU : ContDiff ℝ 3 U) {z0 : E} {zb : B → E}
    (hs : Tendsto s L (𝓝 0)) (hz : (fun b => zb b - z0) =O[L] fun b => s b ^ 1) (w : E)
    {ξ : B → E} (hξ : ξ =O[L] fun b => s b ^ 1) :
    (fun b => (fderiv ℝ (fderiv ℝ U) (zb b) w (ξ b) + fderiv ℝ (fderiv ℝ U) (zb b) (ξ b) w) -
      (fderiv ℝ (fderiv ℝ U) z0 w (ξ b) + fderiv ℝ (fderiv ℝ U) z0 (ξ b) w)) =O[L]
      fun b => s b ^ 2 := by
  have h2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ U)) :=
    (hU.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  have hT : Tendsto zb L (𝓝 z0) := by
    have := (tendsto_of_o_one hs hz).add_const z0
    simpa using this
  have hD := ((move_isBigO h2 hT).trans hz).norm_left
  have hm := o_mul hD hξ.norm_left (by norm_num : 1 + 1 = 2)
  refine (IsBigO.of_bound 1 (Eventually.of_forall fun b => ?_)).trans
    (hm.const_mul_left (2 * ‖w‖))
  set Dl := fderiv ℝ (fderiv ℝ U) (zb b) - fderiv ℝ (fderiv ℝ U) z0 with hDl
  have e : (fderiv ℝ (fderiv ℝ U) (zb b) w (ξ b) + fderiv ℝ (fderiv ℝ U) (zb b) (ξ b) w) -
      (fderiv ℝ (fderiv ℝ U) z0 w (ξ b) + fderiv ℝ (fderiv ℝ U) z0 (ξ b) w) =
      Dl w (ξ b) + Dl (ξ b) w := by
    simp only [hDl, FunLike.coe_sub, Pi.sub_apply]; ring
  have b1 : ‖Dl w (ξ b)‖ ≤ ‖Dl‖ * ‖w‖ * ‖ξ b‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
  have b2 : ‖Dl (ξ b) w‖ ≤ ‖Dl‖ * ‖ξ b‖ * ‖w‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
  rw [e, one_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  rw [Real.norm_eq_abs] at b1 b2
  have hab := abs_add_le (Dl w (ξ b)) (Dl (ξ b) w)
  have hnn : 0 ≤ ‖Dl‖ * ‖ξ b‖ := by positivity
  rw [abs_of_nonneg (by positivity : 0 ≤ 2 * ‖w‖ * (‖Dl‖ * ‖ξ b‖))]
  nlinarith [norm_nonneg w]

variable {Ξ : Type*} [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]

/-- **Woodford (2003), Proposition 6.7, (4.9), p. 422, with every coefficient at the distorted
steady state.** Under the hypotheses of `prop67_distorted` (with `σ⁻¹, ω ≠ 0`), let the
coefficients be those of `z_b = (Ȳ_b, m̄_b, 0)`: `ũ_cc = −σ⁻¹_bũ_c/Ȳ_b`,
`ũ_cm + ũ_mc = 2χ_bũ_c/m̄_b`, `ũ_mm = −Ȳ_bũ_c/(η_{i,b}v̄_b)/m̄_b²`, `v̄_bm̄_b = Ȳ_b`,
`v_yy = ω_bv_y/Ȳ_b`, `η_{y,b} = χ_bη_{i,b}v̄_b`, and the disturbances `g_{b}`, `εᵐ_b`, `q_{b}`
defined at `z_{b}` as `g`, `εᵐ`, `q` are at the satiated point. Then the actual period utility is
`t.i.p. − ½Ȳ_bũ_c(z_b)·(4.9)(local coefficients) + O(ε³)`. -/
theorem prop67_distorted_local (hs : Tendsto s L (𝓝 0)) {ι : Type*} [Fintype ι] {w : ι → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {θ : ℝ} (hθ : θ ≠ 1) {U Ut : ℝ × ℝ × Ξ → ℝ}
    (hUt : ContDiff ℝ 3 Ut) {ms : ℝ} (hms : 0 < ms) (hEq : Set.EqOn U Ut {z | z.2.1 ≤ ms})
    {v : ℝ × Ξ → ℝ} (hv : ContDiff ℝ 3 v) {Ys : ℝ} (hYs : 0 < Ys)
    (P : Transactions.TxParams) (hθi : P.thetaInv = θ⁻¹) (hvel : P.vbar * ms = Ys)
    (hey : P.etaY = P.chi * P.etaI * P.vbar) (hΩ : Transactions.omegaMC P ≠ 0)
    (hi : P.etaI ≠ 0) (hvb : P.vbar ≠ 0) (hσ0 : P.sigInv ≠ 0) (hω0 : P.omega ≠ 0)
    (huc : fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) ≠ 0)
    (hsat : fderiv ℝ Ut (Ys, ms, 0) (0, 1, 0) = 0)
    (h11 : fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (1, 0, 0) (1, 0, 0) =
      -(P.sigInv * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / Ys))
    (h12 : fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (1, 0, 0) (0, 1, 0) +
      fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 1, 0) (1, 0, 0) =
        2 * (P.chi * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / ms))
    (h22 : fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 1, 0) (0, 1, 0) =
      -(Ys * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / (P.etaI * P.vbar) / ms ^ 2))
    (hvy : dY v (Ys, 0) = fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0))
    (hvyy : dYY v (Ys, 0) = P.omega * dY v (Ys, 0) / Ys)
    {Yb mb Phi dbar : B → ℝ} (hYb0 : ∀ b, 0 < Yb b) (hmb0 : ∀ b, 0 < mb b)
    (hYb : Tendsto Yb L (𝓝 Ys)) (hmb : Tendsto mb L (𝓝 ms))
    (hPhi : Phi =O[L] fun b => s b ^ 1) (hdbar : dbar =O[L] fun b => s b ^ 1)
    (hF1 : ∀ b, dY v (Yb b, 0) = (1 - Phi b) * fderiv ℝ Ut (Yb b, mb b, 0) (1, 0, 0))
    (hF2 : ∀ b, fderiv ℝ Ut (Yb b, mb b, 0) (0, 1, 0) =
      (1 - Real.exp (-dbar b)) * fderiv ℝ Ut (Yb b, mb b, 0) (1, 0, 0))
    {σb ωb χb ηib vb ηyb : B → ℝ}
    (hσb : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Yb b, mb b, 0) (1, 0, 0) (1, 0, 0) =
      -(σb b * fderiv ℝ Ut (Yb b, mb b, 0) (1, 0, 0) / Yb b))
    (hχb : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Yb b, mb b, 0) (1, 0, 0) (0, 1, 0) +
      fderiv ℝ (fderiv ℝ Ut) (Yb b, mb b, 0) (0, 1, 0) (1, 0, 0) =
        2 * (χb b * fderiv ℝ Ut (Yb b, mb b, 0) (1, 0, 0) / mb b))
    (h22b : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Yb b, mb b, 0) (0, 1, 0) (0, 1, 0) =
      -(Yb b * fderiv ℝ Ut (Yb b, mb b, 0) (1, 0, 0) / (ηib b * vb b) / mb b ^ 2))
    (hvelb : ∀ b, vb b * mb b = Yb b) (hωb : ∀ b, dYY v (Yb b, 0) = ωb b * dY v (Yb b, 0) / Yb b)
    (heyb : ∀ b, ηyb b = χb b * ηib b * vb b)
    {yd : B → ι → ℝ} {md d g q eps gb qb epsb : B → ℝ} {xu xv : B → Ξ}
    (hg : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (1, 0, 0) (0, 0, xu b) +
      fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 0, xu b) (1, 0, 0) =
        2 * (P.sigInv * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) * g b))
    (heps : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 1, 0) (0, 0, xu b) +
      fderiv ℝ (fderiv ℝ Ut) (Ys, ms, 0) (0, 0, xu b) (0, 1, 0) =
        2 * (Ys * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) / (P.etaI * P.vbar) / ms * eps b))
    (hq : ∀ b, dYXi v (Ys, 0) (xv b) = -(P.omega * dY v (Ys, 0) * q b))
    (hgb : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Yb b, mb b, 0) (1, 0, 0) (0, 0, xu b) +
      fderiv ℝ (fderiv ℝ Ut) (Yb b, mb b, 0) (0, 0, xu b) (1, 0, 0) =
        2 * (σb b * fderiv ℝ Ut (Yb b, mb b, 0) (1, 0, 0) * gb b))
    (hepsb : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Yb b, mb b, 0) (0, 1, 0) (0, 0, xu b) +
      fderiv ℝ (fderiv ℝ Ut) (Yb b, mb b, 0) (0, 0, xu b) (0, 1, 0) =
        2 * (Yb b * fderiv ℝ Ut (Yb b, mb b, 0) (1, 0, 0) / (ηib b * vb b) / mb b * epsb b))
    (hqb : ∀ b, dYXi v (Yb b, 0) (xv b) = -(ωb b * dY v (Yb b, 0) * qb b))
    (hyd : yd =O[L] fun b => s b ^ 1) (hmd : md =O[L] fun b => s b ^ 1)
    (hd : d =O[L] fun b => s b ^ 1) (hgO : g =O[L] fun b => s b ^ 1)
    (hqO : q =O[L] fun b => s b ^ 1) (hepsO : eps =O[L] fun b => s b ^ 1)
    (hxu : xu =O[L] fun b => s b ^ 1) (hxv : xv =O[L] fun b => s b ^ 1)
    (hr : (fun b => md b - (P.etaY * logYidx w θ (yd b) - P.etaI * d b + eps b))
      =O[L] fun b => s b ^ 2)
    (hleft : ∀ᶠ b in L, md b + Real.log (mb b / ms) ≤ 0) :
    (fun b => periodUT U v w θ (Yb b) (mb b) (yd b) (md b) (xu b) (xv b) -
      ((tipT Ut v Ys ms (xu b) (xv b) + Ys * fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) *
        Transactions.tip P (g b) (q b) (eps b) 0 0) -
        Yb b * fderiv ℝ Ut (Yb b, mb b, 0) (1, 0, 0) *
          Transactions.loss49 ⟨σb b, ωb b, P.thetaInv, χb b, ηib b, vb b, ηyb b⟩
            (txDist ⟨σb b, ωb b, P.thetaInv, χb b, ηib b, vb b, ηyb b⟩ (logYidx w θ (yd b))
              (d b) (gb b) (qb b) (epsb b) (Phi b) (1 - Real.exp (-dbar b))
              (crossVar w (yd b)) (md b)) / 2)) =O[L] fun b => s b ^ 3 := by
  have hW := prop67_distorted hs hw0 hw1 hθ hUt hms hEq hv hYs P hθi hvel hey hΩ hi hvb huc
    hsat h11 h12 h22 hvy hvyy hYb0 hmb0 hYb hmb hPhi hdbar hF1 hF2 hg heps hq hyd hmd hd hgO hqO
    hepsO hxu hxv hr hleft
  set Δ := fun b => 1 - Real.exp (-dbar b) with hΔdef
  have hΔd : (fun b => Δ b - dbar b) =O[L] fun b => s b ^ 2 :=
    (BridgeLinks.exp_sub_one_sub_o hs hdbar.neg_left).neg_left.congr_left fun b => by
      simp only [hΔdef]; ring
  have hΔ : Δ =O[L] fun b => s b ^ 1 :=
    ((o_weaken hs (by norm_num : 1 ≤ 2) hΔd).add hdbar).congr_left fun b => by ring
  obtain ⟨haO, hcO⟩ := distorted_ss67_first hs hUt hv hYs hms P hvel hey hΩ hi hvb huc hsat h11
    h12 h22 hvy hvyy hYb hmb hPhi hΔ hF1 hF2
  set z0 : ℝ × ℝ × Ξ := (Ys, ms, 0) with hz0
  set zb : B → ℝ × ℝ × Ξ := fun b => (Yb b, mb b, 0) with hzb
  have hz : (fun b => zb b - z0) =O[L] fun b => s b ^ 1 :=
    (haO.prod_left (hcO.prod_left (isBigO_zero _ _))).congr_left fun b => by
      simp only [hzb, hz0, Prod.mk_sub_mk, sub_zero]
  have hF2c : ContDiff ℝ 2 (fderiv ℝ Ut) := hUt.fderiv_right (m := 2) (by norm_num)
  have hD2c : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ Ut)) := hF2c.fderiv_right (m := 1) (by norm_num)
  have dv : ∀ (e1 e2 : ℝ × ℝ × Ξ), DifferentiableAt ℝ
      (fun z => fderiv ℝ (fderiv ℝ Ut) z e1 e2) z0 := fun e1 e2 =>
    ((hD2c.clm_apply contDiff_const).clm_apply contDiff_const).differentiable (by norm_num) z0
  have hYO : (fun b => Yb b - Ys) =O[L] fun b => s b ^ 1 := haO
  set uc := fderiv ℝ Ut (Ys, ms, 0) (1, 0, 0) with huc_def
  have huO : (fun b => fderiv ℝ Ut (zb b) (1, 0, 0) - uc) =O[L] fun b => s b ^ 1 :=
    diff_move ((hF2c.clm_apply contDiff_const).differentiable (by norm_num) z0) hs hz
  have hzT : Tendsto zb L (𝓝 z0) := by
    have := (tendsto_of_o_one hs hz).add_const z0
    simpa using this
  have hucT : Tendsto (fun b => fderiv ℝ Ut (zb b) (1, 0, 0)) L (𝓝 uc) := by
    have := (tendsto_of_o_one hs huO).add_const uc
    simpa using this
  have hU11 := diff_move (dv (1, 0, 0) (1, 0, 0)) hs hz
  have hU12 : (fun b => (fderiv ℝ (fderiv ℝ Ut) (zb b) (1, 0, 0) (0, 1, 0) +
      fderiv ℝ (fderiv ℝ Ut) (zb b) (0, 1, 0) (1, 0, 0)) -
      (fderiv ℝ (fderiv ℝ Ut) z0 (1, 0, 0) (0, 1, 0) +
        fderiv ℝ (fderiv ℝ Ut) z0 (0, 1, 0) (1, 0, 0))) =O[L] fun b => s b ^ 1 :=
    ((diff_move (dv (1, 0, 0) (0, 1, 0)) hs hz).add
      (diff_move (dv (0, 1, 0) (1, 0, 0)) hs hz)).congr_left fun b => by ring
  have hU22 := diff_move (dv (0, 1, 0) (0, 1, 0)) hs hz
  have hmO : (fun b => mb b - ms) =O[L] fun b => s b ^ 1 := hcO
  -- `σ⁻¹_b`
  have hσbO : (fun b => σb b - P.sigInv) =O[L] fun b => s b ^ 1 := by
    have h := quot_move1 hs huc (mul_move1 hs (hYO.neg_left.congr_left fun b => by ring :
      (fun b => -Yb b - -Ys) =O[L] _) hU11) huO
    refine h.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [hucT.eventually_ne huc] with b hb
    have e := hσb b
    have hY' := (hYb0 b).ne'
    simp only [hzb] at hb ⊢
    rw [e, h11]
    field_simp
  -- `χ_b`
  have hχbO : (fun b => χb b - P.chi) =O[L] fun b => s b ^ 1 := by
    have h := quot_move1 hs (mul_ne_zero two_ne_zero huc) (mul_move1 hs hmO hU12)
      ((huO.const_mul_left 2).congr_left fun b => by ring :
        (fun b => 2 * fderiv ℝ Ut (zb b) (1, 0, 0) - 2 * uc) =O[L] fun b => s b ^ 1)
    refine h.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [hucT.eventually_ne huc] with b hb
    have e := hχb b
    have hm' := (hmb0 b).ne'
    simp only [hzb] at hb ⊢
    rw [e, h12]
    field_simp
  -- `η_{i,b}v̄_b`
  have hU22z : fderiv ℝ (fderiv ℝ Ut) z0 (0, 1, 0) (0, 1, 0) ≠ 0 := by
    rw [hz0, h22]
    exact neg_ne_zero.2 (div_ne_zero (div_ne_zero (mul_ne_zero hYs.ne' huc)
      (mul_ne_zero hi hvb)) (pow_ne_zero 2 hms.ne'))
  have hU22T : Tendsto (fun b => fderiv ℝ (fderiv ℝ Ut) (zb b) (0, 1, 0) (0, 1, 0)) L
      (𝓝 (fderiv ℝ (fderiv ℝ Ut) z0 (0, 1, 0) (0, 1, 0))) :=
    (dv (0, 1, 0) (0, 1, 0)).continuousAt.tendsto.comp hzT
  have hπO : (fun b => ηib b * vb b - P.etaI * P.vbar) =O[L] fun b => s b ^ 1 := by
    have hden := mul_ne_zero hU22z (pow_ne_zero 2 hms.ne')
    have hm2 : (fun b => mb b ^ 2 - ms ^ 2) =O[L] fun b => s b ^ 1 :=
      (mul_move1 hs hmO hmO).congr_left fun b => by ring
    have h := quot_move1 hs hden (mul_move1 hs (hYO.neg_left.congr_left fun b => by ring :
      (fun b => -Yb b - -Ys) =O[L] _) huO) (mul_move1 hs hU22 hm2)
    refine h.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [hU22T.eventually_ne hU22z, hucT.eventually_ne huc] with b hb hb2
    have e := h22b b
    have hm' := (hmb0 b).ne'
    have hY' := (hYb0 b).ne'
    simp only [hzb] at hb hb2 ⊢
    have hπ : ηib b * vb b ≠ 0 := by
      intro h0; rw [h0, div_zero, zero_div, neg_zero] at e; exact hb e
    rw [e, h22]
    field_simp
  have hvbO : (fun b => vb b - P.vbar) =O[L] fun b => s b ^ 1 := by
    have h := quot_move1 hs hms.ne' hYO hmO
    refine h.congr_left fun b => ?_
    have e := hvelb b
    have hm' := (hmb0 b).ne'
    rw [← hvel, ← e]
    field_simp
  have hηibO : (fun b => ηib b - P.etaI) =O[L] fun b => s b ^ 1 := by
    have h := quot_move1 hs hvb hπO hvbO
    have hvT : Tendsto vb L (𝓝 P.vbar) := by
      have := (tendsto_of_o_one hs hvbO).add_const P.vbar
      simpa using this
    refine h.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [hvT.eventually_ne hvb] with b hb
    field_simp
  have hηybO : (fun b => ηyb b - P.etaY) =O[L] fun b => s b ^ 1 :=
    (mul_move1 hs (mul_move1 hs hχbO hηibO) hvbO).congr_left fun b => by rw [heyb, hey]
  -- `ω_b`
  have hvc : dY v (Ys, 0) ≠ 0 := by rw [hvy]; exact huc
  have hv2 : ContDiff ℝ 2 v := hv.of_le (by norm_num)
  obtain ⟨-, hωr⟩ := coeff_move hv hvc hs hYO
  have hvcT : Tendsto (fun b => dY v (Yb b, 0)) L (𝓝 (dY v (Ys, 0))) :=
    (hasDerivAt_dY hv2 Ys).continuousAt.tendsto.comp hYb
  have hωbO : (fun b => ωb b - P.omega) =O[L] fun b => s b ^ 1 := by
    refine hωr.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [hvcT.eventually_ne hvc] with b hb
    have e := hωb b
    have hY' := (hYb0 b).ne'
    rw [hvyy, e]
    field_simp
  -- the disturbances
  have hξ : (fun b => (((0 : ℝ), (0 : ℝ), xu b) : ℝ × ℝ × Ξ)) =O[L] fun b => s b ^ 1 :=
    (isBigO_zero _ _).prod_left ((isBigO_zero _ _).prod_left hxu)
  have hgbd := div_move hs (mul_ne_zero two_ne_zero (mul_ne_zero hσ0 huc))
    (ab := fun b => 2 * (σb b * fderiv ℝ Ut (zb b) (1, 0, 0)))
    ((mul_move1 hs hσbO huO).const_mul_left 2 |>.congr_left fun b => by ring) hgO (xb := gb)
    ((d2_move hUt hs hz (1, 0, 0) hξ).congr_left fun b => by
      simp only [hzb, hz0] at *; rw [hgb, hg]; ring)
  have hab_e : (fun b => 2 * (Yb b * fderiv ℝ Ut (zb b) (1, 0, 0) / (ηib b * vb b) / mb b) -
      2 * (Ys * uc / (P.etaI * P.vbar) / ms)) =O[L] fun b => s b ^ 1 :=
    ((quot_move1 hs hms.ne' (quot_move1 hs (mul_ne_zero hi hvb) (mul_move1 hs hYO huO) hπO)
      hmO).const_mul_left 2).congr_left fun b => by ring
  have hepsbd := div_move hs (mul_ne_zero two_ne_zero (div_ne_zero (div_ne_zero
    (mul_ne_zero hYs.ne' huc) (mul_ne_zero hi hvb)) hms.ne')) hab_e hepsO (xb := epsb)
    ((d2_move hUt hs hz (0, 1, 0) hξ).congr_left fun b => by
      simp only [hzb, hz0] at *; rw [hepsb, heps]; ring)
  have hvcO : (fun b => dY v (Yb b, 0) - dY v (Ys, 0)) =O[L] fun b => s b ^ 1 :=
    ((hasDerivAt_dY hv2 Ys).isBigO_sub.comp_tendsto hYb).trans hYO
  have hqbd := div_move hs (neg_ne_zero.2 (mul_ne_zero hω0 hvc))
    (ab := fun b => -(ωb b * dY v (Yb b, 0)))
    ((mul_move1 hs hωbO hvcO).neg_left.congr_left fun b => by ring) hqO (xb := qb)
    (((dYXi_move hv hYb xv).trans (o_mul hYO hxv.norm_left
      (by norm_num : 1 + 1 = 2))).congr_left fun b => by rw [hqb, hq]; ring)
  -- the loss
  have hYdO := logYidx_o hs hw0 hw1 hθ hyd
  have hV := crossVar_o hw0 hw1 hyd
  have hLm := loss49_move hs (θ := P.thetaInv) (m := md) hΩ hvb hσbO hωbO hχbO hηibO hvbO
    hηybO hgbd hqbd hepsbd hYdO hd hgO hqO hepsO hPhi hΔ hV
  have hLo := loss49_o P.sigInv P.omega P.thetaInv P.chi P.etaI P.vbar P.etaY (m := md) hYdO hd
    hgO hqO hepsO hPhi hΔ hV
  have hK : (fun b => Yb b * fderiv ℝ Ut (zb b) (1, 0, 0) - Ys * uc) =O[L] fun b => s b ^ 1 :=
    mul_move1 hs hYO huO
  have hKL := (((bdd_move hs hK).mul hLm).congr_right (fun b => by ring)).add
    (o_mul hK hLo (by norm_num : 1 + 2 = 3))
  refine (hW.add (hKL.const_mul_left (1 / 2))).congr_left fun b => ?_
  simp only [hzb, hΔdef]
  ring

end Woodford.StabilizationWelfare.TidyR5DistortedLocal67
