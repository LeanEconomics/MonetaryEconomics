/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.BridgeExtensions

/-!
# Expanding around a distorted steady state: tools

Woodford (2003), *Interest and Prices*, Chapter 6, §2.1 (p. 394: the expansion is around the
distorted steady state `Ȳ`, with `x* = log(Y*/Ȳ) = Φ/(σ⁻¹ + ω) + O(Φ²)`, (2.17)) and §4.3–§4.4,
Appendix E.6–E.8.

The Layer-B theorems of BridgeExtensions for Propositions 6.7, 6.10 and 6.12 expand around the
EFFICIENT steady state. The book expands around the DISTORTED steady state `Ȳ(Φ)` of an economy
whose distortion `Φ` is itself small. Along a family `Φ_b = O(s)`, `Ȳ_b → Y*`, this module
supplies the bookkeeping that moves an expansion from `Y*` to `Ȳ_b`:

* `move_isBigO`: a `C¹` map moves by `O(‖z_b − z*‖)`; for utility functions on `ℝ × Ξ`,
  `dY_move`, `dYY_move` (`O(Ȳ_b − Y*)`) and `dYXi_move` (`O((Ȳ_b − Y*)‖ξ‖)`).
* `rev_bound` and **`ss_first_order`**: from a first-order condition `h(Ȳ_b) = −Φ_b k(Ȳ_b)` with
  `h(Y*) = 0`, `h′(Y*) = κ ≠ 0`, the distorted steady state satisfies `Ȳ_b − Y* = O(s)` and
  `κ(Ȳ_b − Y*) + Φ_b k(Y*) = O(s²)` (the first-order formula for `x*`).
* `log_move`: `log(Ȳ_b/Y*) − (Ȳ_b − Y*)/Y* = O(s²)`.
* `sq_move`, `mul_move`, `quad_first`: the coefficient and variable changes of a quadratic loss.
* `logYidx_shift`: shifting every good's log output by `c` shifts the log output index by `c`.
-/

namespace Woodford.StabilizationWelfare.TidyR5DistortedTools

open Filter Topology Asymptotics
open BridgeExtensions

variable {B : Type*} {L : Filter B} {s : B → ℝ}

/-! ## Moving the expansion point -/

/-- Woodford (2003), App. E (moving expansion point): a `C¹` map moves by `O(‖z_b − z*‖)`. -/
theorem move_isBigO {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {Φ : F → G} (hΦ : ContDiff ℝ 1 Φ) {z0 : F} {zb : B → F}
    (hz : Tendsto zb L (𝓝 z0)) : (fun b => Φ (zb b) - Φ z0) =O[L] fun b => zb b - z0 :=
  ((hΦ.differentiable one_ne_zero z0).hasFDerivAt.isBigO_sub).comp_tendsto hz

variable {Ξ : Type*} [NormedAddCommGroup Ξ]

/-- The pair `(y, 0) ∈ ℝ × Ξ` has norm `|y|`. -/
theorem norm_pair (y : ℝ) : ‖((y : ℝ), (0 : Ξ))‖ = |y| := by
  rw [Prod.norm_def, norm_zero, Real.norm_eq_abs, max_eq_left (abs_nonneg _)]

/-- The pair `(0, ξ) ∈ ℝ × Ξ` has norm `‖ξ‖`. -/
theorem norm_pair' (ξ : Ξ) : ‖((0 : ℝ), ξ)‖ = ‖ξ‖ := by
  rw [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]

/-- The base points `(Ȳ_b, 0)` converge when `Ȳ_b` does, and differ by `O(Ȳ_b − Y*)`. -/
theorem pt_move {Ys : ℝ} {Yb : B → ℝ} :
    (fun b => ((Yb b, (0 : Ξ)) : ℝ × Ξ) - (Ys, 0)) =O[L] fun b => Yb b - Ys :=
  IsBigO.of_bound 1 (Eventually.of_forall fun b => by
    rw [Prod.mk_sub_mk, sub_zero, norm_pair, one_mul, Real.norm_eq_abs])

variable [NormedSpace ℝ Ξ]

/-- Woodford (2003), (E.2) at a moving point: `u_c(Ȳ_b) − u_c(Y*) = O(Ȳ_b − Y*)`. -/
theorem dY_move {U : ℝ × Ξ → ℝ} (hU : ContDiff ℝ 3 U) {Ys : ℝ} {Yb : B → ℝ}
    (hY : Tendsto Yb L (𝓝 Ys)) :
    (fun b => dY U (Yb b, 0) - dY U (Ys, 0)) =O[L] fun b => Yb b - Ys := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ U) :=
    (hU.fderiv_right (m := 2) (by norm_num)).of_le (by norm_num)
  have hz : Tendsto (fun b => ((Yb b, (0 : Ξ)) : ℝ × Ξ)) L (𝓝 (Ys, 0)) :=
    hY.prodMk_nhds tendsto_const_nhds
  have h := (move_isBigO h1 hz).trans pt_move
  refine (IsBigO.of_bound 1 (Eventually.of_forall fun b => ?_)).trans h
  rw [one_mul]
  change ‖(fderiv ℝ U (Yb b, 0) - fderiv ℝ U (Ys, 0)) (1, 0)‖ ≤ _
  refine ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
  rw [norm_pair, abs_one, mul_one]

/-- Woodford (2003), (E.2) at a moving point: `u_cc(Ȳ_b) − u_cc(Y*) = O(Ȳ_b − Y*)`. -/
theorem dYY_move {U : ℝ × Ξ → ℝ} (hU : ContDiff ℝ 3 U) {Ys : ℝ} {Yb : B → ℝ}
    (hY : Tendsto Yb L (𝓝 Ys)) :
    (fun b => dYY U (Yb b, 0) - dYY U (Ys, 0)) =O[L] fun b => Yb b - Ys := by
  have h2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ U)) :=
    (hU.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  have hz : Tendsto (fun b => ((Yb b, (0 : Ξ)) : ℝ × Ξ)) L (𝓝 (Ys, 0)) :=
    hY.prodMk_nhds tendsto_const_nhds
  have h := (move_isBigO h2 hz).trans pt_move
  refine (IsBigO.of_bound 1 (Eventually.of_forall fun b => ?_)).trans h
  rw [one_mul]
  change ‖((fderiv ℝ (fderiv ℝ U) (Yb b, 0) - fderiv ℝ (fderiv ℝ U) (Ys, 0)) (1, 0)) (1, 0)‖ ≤ _
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  rw [norm_pair, abs_one, mul_one]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by rw [norm_pair, abs_one, mul_one])

/-- Woodford (2003), (E.2) at a moving point: the cross derivative moves by
`O((Ȳ_b − Y*)‖ξ‖)`. -/
theorem dYXi_move {U : ℝ × Ξ → ℝ} (hU : ContDiff ℝ 3 U) {Ys : ℝ} {Yb : B → ℝ}
    (hY : Tendsto Yb L (𝓝 Ys)) (ξ : B → Ξ) :
    (fun b => dYXi U (Yb b, 0) (ξ b) - dYXi U (Ys, 0) (ξ b)) =O[L]
      fun b => (Yb b - Ys) * ‖ξ b‖ := by
  have h2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ U)) :=
    (hU.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  have hz : Tendsto (fun b => ((Yb b, (0 : Ξ)) : ℝ × Ξ)) L (𝓝 (Ys, 0)) :=
    hY.prodMk_nhds tendsto_const_nhds
  have h := (move_isBigO h2 hz).trans pt_move
  have hm := h.norm_left.mul (isBigO_refl (fun b => ‖ξ b‖) L)
  refine (IsBigO.of_bound 1 (Eventually.of_forall fun b => ?_)).trans hm
  set D := fderiv ℝ (fderiv ℝ U) (Yb b, 0) - fderiv ℝ (fderiv ℝ U) (Ys, 0) with hD
  have e : dYXi U (Yb b, 0) (ξ b) - dYXi U (Ys, 0) (ξ b) = (D (1, 0) (0, ξ b) +
      D (0, ξ b) (1, 0)) / 2 := by
    simp only [dYXi, hD, FunLike.coe_sub, Pi.sub_apply]; ring
  have b1 : ‖D (1, 0) (0, ξ b)‖ ≤ ‖D‖ * ‖ξ b‖ := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [norm_pair']
    refine mul_le_mul_of_nonneg_right ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
      (norm_nonneg _)
    rw [norm_pair, abs_one, mul_one]
  have b2 : ‖D (0, ξ b) (1, 0)‖ ≤ ‖D‖ * ‖ξ b‖ := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [norm_pair, abs_one, mul_one]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by rw [norm_pair'])
  rw [e, one_mul, norm_mul, norm_norm, norm_norm, Real.norm_eq_abs, abs_div, abs_two]
  have := abs_add_le (D (1, 0) (0, ξ b)) (D (0, ξ b) (1, 0))
  rw [Real.norm_eq_abs] at b1 b2
  linarith

/-! ## The distorted steady state -/

/-- Woodford (2003), (2.17), p. 399 (the inverse bound): if `h(Y*) = 0` and
`h(x) − κ(x − Y*) = O((x − Y*)²)` with `κ ≠ 0`, then `x − Y* = O(h(x))` near `Y*`. -/
theorem rev_bound {h : ℝ → ℝ} {Ys κ : ℝ} (hκ : κ ≠ 0)
    (hT : (fun x => h x - κ * (x - Ys)) =O[𝓝 Ys] fun x => (x - Ys) ^ 2) :
    (fun x => x - Ys) =O[𝓝 Ys] h := by
  obtain ⟨C, hC⟩ := hT.bound
  have hC1 : 0 ≤ max C 0 := le_max_right _ _
  have hk : 0 < |κ| := abs_pos.mpr hκ
  have hnear : ∀ᶠ x in 𝓝 Ys, |x - Ys| ≤ |κ| / (2 * (max C 0 + 1)) := by
    have : Metric.ball Ys (|κ| / (2 * (max C 0 + 1))) ∈ 𝓝 Ys :=
      Metric.ball_mem_nhds _ (by positivity)
    filter_upwards [this] with x hx
    rw [Metric.mem_ball, Real.dist_eq] at hx
    exact hx.le
  refine IsBigO.of_bound (2 / |κ|) ?_
  filter_upwards [hC, hnear] with x h1 h2
  simp only [Real.norm_eq_abs, abs_pow] at h1 ⊢
  have h3 : |κ * (x - Ys)| ≤ |h x| + C * |x - Ys| ^ 2 := by
    have := abs_sub_abs_le_abs_sub (κ * (x - Ys)) (h x)
    rw [abs_sub_comm] at this
    linarith
  have h4 : C * |x - Ys| ^ 2 ≤ |κ| / 2 * |x - Ys| := by
    have hx0 := abs_nonneg (x - Ys)
    have : C * |x - Ys| ^ 2 ≤ max C 0 * |x - Ys| ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    have h5 : max C 0 * |x - Ys| ≤ |κ| / 2 := by
      calc max C 0 * |x - Ys| ≤ (max C 0 + 1) * (|κ| / (2 * (max C 0 + 1))) :=
            mul_le_mul (by linarith) h2 hx0 (by linarith)
        _ = |κ| / 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right h5 hx0]
  rw [abs_mul] at h3
  have h6 : |κ| * |x - Ys| ≤ 2 * |h x| := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hk]
  linarith [mul_comm |x - Ys| |κ|]

/-- **Woodford (2003), (2.9) and (2.17), pp. 394, 399 (the distorted steady state to first
order).** Let `h` be `C²` near `Y*` with `h(Y*) = 0` and `h′(Y*) = κ ≠ 0`, `k` differentiable at
`Y*`, and let the distorted steady states `Ȳ_b → Y*` satisfy the first-order condition
`h(Ȳ_b) = −Φ_b k(Ȳ_b)` with `Φ_b = O(s)`. Then `Ȳ_b − Y* = O(s)` and
`κ(Ȳ_b − Y*) + Φ_b k(Y*) = O(s²)`. -/
theorem ss_first_order {h k : ℝ → ℝ} {Ys κ : ℝ} (hh : ContDiffAt ℝ 2 h Ys) (hd : deriv h Ys = κ)
    (hκ : κ ≠ 0) (h0 : h Ys = 0) (hk : DifferentiableAt ℝ k Ys) {Yb Phi : B → ℝ}
    (hYb : Tendsto Yb L (𝓝 Ys)) (hFOC : ∀ b, h (Yb b) = -(Phi b * k (Yb b)))
    (hPhi : Phi =O[L] fun b => s b ^ 1) :
    (fun b => Yb b - Ys) =O[L] (fun b => s b ^ 1) ∧
      (fun b => κ * (Yb b - Ys) + Phi b * k Ys) =O[L] fun b => s b ^ 2 := by
  have hT0 := OneParamTaylor.taylor_one_bigO hh
  rw [hd] at hT0
  have hT : (fun x => h x - κ * (x - Ys)) =O[𝓝 Ys] fun x => (x - Ys) ^ 2 :=
    hT0.congr_left fun x => by rw [h0, sub_zero]
  have hkb : (fun b => k (Yb b)) =O[L] fun _ => (1 : ℝ) :=
    (hk.continuousAt.tendsto.comp hYb).isBigO_one ℝ
  have h1 : (fun b => Yb b - Ys) =O[L] fun b => s b ^ 1 := by
    have := (rev_bound hκ hT).comp_tendsto hYb
    refine this.trans ?_
    have e : (h ∘ Yb) = fun b => -(Phi b * k (Yb b)) := funext hFOC
    rw [e]
    exact ((hPhi.mul hkb).neg_left).congr_right fun b => by ring
  refine ⟨h1, ?_⟩
  have h2 := (hT.comp_tendsto hYb).trans (o_pow h1 2)
  have hkd : (fun b => k (Yb b) - k Ys) =O[L] fun b => s b ^ 1 :=
    ((hk.hasDerivAt.isBigO_sub).comp_tendsto hYb).trans h1
  have h3 := o_mul hPhi hkd (by norm_num : 1 + 1 = 2)
  refine (h2.neg_left.sub h3).congr_left fun b => ?_
  simp only [Function.comp_apply, hFOC]
  ring

/-- Woodford (2003), (2.9), p. 394: `log(Ȳ_b/Y*) − (Ȳ_b − Y*)/Y* = O(s²)` when
`Ȳ_b − Y* = O(s)`. -/
theorem log_move {Ys : ℝ} (hYs : 0 < Ys) {Yb : B → ℝ} (hs : Tendsto s L (𝓝 0))
    (h1 : (fun b => Yb b - Ys) =O[L] fun b => s b ^ 1) :
    (fun b => Real.log (Yb b / Ys) - (Yb b - Ys) / Ys) =O[L] fun b => s b ^ 2 := by
  have hc : ContDiffAt ℝ 2 (fun x => Real.log (x / Ys)) Ys := by
    have h1 : ContDiffAt ℝ 2 (fun x : ℝ => x / Ys) Ys := contDiffAt_id.div_const Ys
    exact h1.log (by positivity)
  have hT := OneParamTaylor.taylor_one_bigO hc
  have hdv : deriv (fun x => Real.log (x / Ys)) Ys = 1 / Ys := by
    have h := ((hasDerivAt_id' Ys).div_const Ys).log (by positivity : Ys / Ys ≠ 0)
    rw [h.deriv]
    field_simp
  rw [hdv] at hT
  have hYt : Tendsto Yb L (𝓝 Ys) := by
    have := tendsto_of_o_one hs h1
    simpa using this.add_const Ys
  refine ((hT.comp_tendsto hYt).trans (o_pow h1 2)).congr_left fun b => ?_
  simp only [Function.comp_apply, div_self hYs.ne', Real.log_one, sub_zero]
  ring

/-! ## Changing the coefficients and the variables of a quadratic loss -/

/-- Woodford (2003), App. E (the loss at the distorted point versus the efficient point): if
`c − c′ = O(s)`, `c′ = O(1)`, `z − z′ = O(s²)` and `z′ = O(s)`, then `cz² − c′z′² = O(s³)`. -/
theorem sq_move (hs : Tendsto s L (𝓝 0)) {c c' z z' : B → ℝ}
    (hc : (fun b => c b - c' b) =O[L] fun b => s b ^ 1) (hc' : c' =O[L] fun _ => (1 : ℝ))
    (hz : (fun b => z b - z' b) =O[L] fun b => s b ^ 2) (hz' : z' =O[L] fun b => s b ^ 1) :
    (fun b => c b * z b ^ 2 - c' b * z' b ^ 2) =O[L] fun b => s b ^ 3 := by
  have hz1 : z =O[L] fun b => s b ^ 1 :=
    ((o_weaken hs (by norm_num : 1 ≤ 2) hz).add hz').congr_left fun b => by ring
  have t1 := o_mul hc (o_pow hz1 2) (by norm_num : 1 + 2 = 3)
  have t2 : (fun b => z b ^ 2 - z' b ^ 2) =O[L] fun b => s b ^ 3 :=
    (o_mul hz (hz1.add hz') (by norm_num : 2 + 1 = 3)).congr_left fun b => by ring
  have t3 := hc'.mul t2
  refine (t1.add (t3.congr_right fun b => by ring)).congr_left fun b => ?_
  ring

/-- Woodford (2003), App. E: if `c − c′ = O(s)`, `c′ = O(1)` and `V = O(s²)` then
`cV − c′V = O(s³)`. -/
theorem mul_move {c c' V : B → ℝ} (hc : (fun b => c b - c' b) =O[L] fun b => s b ^ 1)
    (hV : V =O[L] fun b => s b ^ 2) :
    (fun b => c b * V b - c' b * V b) =O[L] fun b => s b ^ 3 :=
  (o_mul hc hV (by norm_num : 1 + 2 = 3)).congr_left fun b => by ring

/-- Woodford (2003), (2.10)–(2.11) with moving coefficients: if `c = O(1)`,
`z − s z₁ = O(s²)` and `z₁ = O(1)`, then `cz² − s²c z₁² = O(s³)`. -/
theorem quad_first (hs : Tendsto s L (𝓝 0)) {c z z1 : B → ℝ} (hc : c =O[L] fun _ => (1 : ℝ))
    (hz : (fun b => z b - s b * z1 b) =O[L] fun b => s b ^ 2) (hz1 : z1 =O[L] fun _ => (1 : ℝ)) :
    (fun b => c b * z b ^ 2 - s b ^ 2 * (c b * z1 b ^ 2)) =O[L] fun b => s b ^ 3 :=
  (hc.mul (sq_sub_o hs hz hz1)).congr (fun b => by ring) (fun b => by ring)

/-! ## Shifting the cross-section -/

variable {ι : Type*} [Fintype ι]

/-- Woodford (2003), (2.6), p. 393 (**the output index is homogeneous**): shifting every good's
log output by `c` shifts the log Dixit–Stiglitz index by `c` (`θ ≠ 1`). -/
theorem logYidx_shift {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {θ : ℝ}
    (hθ : θ ≠ 1) (c : ℝ) (yh : ι → ℝ) :
    logYidx w θ (fun i => yh i + c) = logYidx w θ yh + c := by
  have hr : (1 : ℝ) - θ⁻¹ ≠ 0 := by
    intro h
    apply hθ
    have : θ⁻¹ = 1 := by linarith
    simpa using congrArg (·⁻¹) this
  unfold logYidx
  rw [ExpLogCES.log_cesIndex_exp hw0 hw1, ExpLogCES.log_cesIndex_exp hw0 hw1]
  unfold ExpLogCES.cumulant ExpLogCES.cesMoment
  have e : ∑ i, w i * Real.exp ((1 - θ⁻¹) * (yh i + c)) =
      Real.exp ((1 - θ⁻¹) * c) * ∑ i, w i * Real.exp ((1 - θ⁻¹) * yh i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (1 - θ⁻¹) * (yh i + c) = (1 - θ⁻¹) * yh i + (1 - θ⁻¹) * c by ring, Real.exp_add]
    ring
  have hpos : 0 < ∑ i, w i * Real.exp ((1 - θ⁻¹) * yh i) :=
    ExpLogCES.cesMoment_pos hw0 hw1 _ _
  rw [e, Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp, mul_add, one_div,
    ← mul_assoc, inv_mul_cancel₀ hr, one_mul, add_comm]

end Woodford.StabilizationWelfare.TidyR5DistortedTools
