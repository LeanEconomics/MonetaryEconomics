/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.Links
import StabilizationWelfare.StickyWageWelfare
import StabilizationWelfare.ApproxTheory

/-!
# The Layer-B bridge for Propositions 6.7–6.8 and 6.10–6.15

Woodford (2003), *Interest and Prices*, Chapter 6, §4.1 (pp. 420–426), §4.3 (pp. 435–443),
§4.4 (pp. 443–448), §5 (pp. 455–463) and Appendix E.4, E.6–E.8 (pp. 698–708); survey §4,
Layer B ("one-parameter Taylor bridge").

The Layer-A modules prove the book's second-order welfare formulas as EXACT polynomial
identities with explicit "t.i.p." and remainders of weighted degree three. This module connects
the ACTUAL period utility of each model to those quadratic losses along a one-parameter family
(amplitude `s`, or `ε`):
`W(ε) = t.i.p.(ε) − (ε²/2)·Ȳu_c·L(first-order solution) + O(ε³)`,
where `t.i.p.(ε)` depends on the disturbances only (it contains `W(0) + εW′(0)` whenever the
linear term is policy-independent), and then derives the welfare ranking.

## Method

* Orders along an ARBITRARY filter `L` with amplitude `s → 0` (`o_mul`, `o_weaken`, `o_pow`,
  `expRem_o`, `rlog_o`); the remainders of every Layer-A identity are shown to be `O(s³)` for
  ANY family with first-order variables `O(s)` and second-order ones `O(s²)`, and arbitrary
  third-order atoms (`R51_o`, `txRemainder_o`, `R610_o`, `R612_o`, `nowA_o`, `restA_o`,
  `rho2A_o`), not only along weighted rays.
* The Taylor step from the actual utility: `taylor_family_moving`, `taylor_family` (`C³`
  utility, eq. (1.2)), `taylor_family_of_eqOn` (ONE-SIDED, for satiation in money),
  `quadApprox_prod`, `quadApprox_triple`, `uTaylor_family`, `uTaylor_family_exp`; the
  aggregation atoms (Dixit–Stiglitz `cesAtom_o`, two-sector aggregator `aggAtom_o` with
  `S_o`, labour index `labourAtom_o`, wage index via `Links.CES.priceAtom_isBigO`) are `O(s³)`.
* Uniformity in the date and the state for discounted sums: a family is `UProc l X g` when
  `X = O(g)` along `l ×ˢ ⊤` (ONE constant for all `(t, ω)`). This is the assumption made for
  every infinite-horizon statement: each first-order variable is bounded by `C|ε|` for all dates
  and states. It is the book's "bounded fluctuations" (§2, p. 394) and is NOT implied by
  smoothness in `ε` at each date; with it the period results (proved for an arbitrary filter)
  apply on `l ×ˢ ⊤`, conditional expectations keep the bound (`condE_o`), and geometric
  discounting turns it into an `O(ε³)` bound for the discounted sum (`dsum_o`, `tsum_o`).
* Rankings: `ranking_of_common`, `ranking_layerB`, `ranking_via_loss` (through
  `OneParamTaylor.welfare_ranking_of_loss`), `first_order_ranking`, `prop615_ranking`.

## Main results

* Large distortions (§5; `Φ_y` FIXED, the family in the disturbances only):
  `eq51_actual` ((5.1) from primitives: the hypothesis `h51` of `LargeDistortions.prop614`
  discharged up to `O(s³)`), `R51_o` (arbitrary third-order atoms), `prop614_layerB`
  (Prop. 6.14, actual path), `loss614_first_order` and `prop614_first_order` (the LINEAR term
  does not vanish: welfare moves at first order with `Ȳu_cΦ_y∑βᵗE_0Ŷ₁`), `remAS_o` (the
  remainder of the derived (5.4) is `O(ε³)` uniformly), `prop615_layerB`, `loss615_first_order`,
  `prop615_first_order` (with (5.4) the loss is purely quadratic and a first-order solution
  suffices), `prop615_ranking`.
* Transactions frictions (§4.1): the base point is the efficient steady state AT SATIATION;
  `prop67_actual` (Prop. 6.7 from the actual utility, one-sided at `m̄`), `prop67_layerB`,
  `two_sided_fails`, `two_sided_fails_A61` (a family approaching satiation from the right
  violates the expansion), `prop68_layerB`, `loss410_first_order` (Prop. 6.8).
* Two sectors (§4.3): `prop610_actual`, `loss610_first_order`, `prop610_layerB`,
  `prop611_layerB`, `loss425_first_order`.
* Sticky wages (§4.4): `prop612_actual`, `loss612_first_order`, `prop612_layerB`,
  `prop613_layerB`, `loss429_first_order`.
* Generic: `bridge_first_order`, `discounted_first_order`, `tsum_sq_first_order`,
  `crossVar_first_order`, `expect_layerB` (finite state space of paths), `curve_first_order`,
  `curve_o`, `curve_first_order_pi` (a `C²` family satisfies the order hypotheses).

For the small-distortion models (6.7, 6.10, 6.12) the expansion point is the efficient steady
state (`Φ_y = 0`, and `Δ̄ = 0` for 6.7): the distortions and the interest differential enter
through the variables, which are deviations from that point, so Woodford's `x*` and `Δ̄` are
absorbed (`x − x*` becomes `Ŷ − Ŷⁿ` measured from the efficient level, and `î − îᵐ + Δ̄` the
total interest differential).
-/

namespace Woodford.StabilizationWelfare.BridgeExtensions

open Filter Topology Asymptotics
open ExpLogCES (crossMean crossVar expRem rlog)

/-! ## Orders of magnitude along an arbitrary filter -/

variable {B : Type*} {L : Filter B} {s : B → ℝ}

/-- Woodford (2003), (2.11), p. 395 (orders along any filter): `O(sᵐ) · O(sⁿ) = O(sᵐ⁺ⁿ)`. -/
theorem o_mul {f g : B → ℝ} {m n k : ℕ} (hf : f =O[L] fun b => s b ^ m)
    (hg : g =O[L] fun b => s b ^ n) (hk : m + n = k) :
    (fun b => f b * g b) =O[L] fun b => s b ^ k := by
  subst hk
  exact (hf.mul hg).congr_right fun b => by ring

/-- Woodford (2003), (2.11), p. 395 (orders along any filter): `O(sⁿ) ⊆ O(sᵐ)` for `m ≤ n`
when `s → 0`. -/
theorem o_weaken (hs : Tendsto s L (𝓝 0)) {f : B → ℝ} {m n : ℕ} (hmn : m ≤ n)
    (hf : f =O[L] fun b => s b ^ n) : f =O[L] fun b => s b ^ m := by
  refine hf.trans ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have h1 : (fun b => s b ^ k) =O[L] (fun _ => (1 : ℝ)) := (hs.pow k).isBigO_one ℝ
  have h2 := (isBigO_refl (fun b => s b ^ m) L).mul h1
  refine h2.congr (fun b => by ring) (fun b => by ring)

/-- Woodford (2003), p. 385: a first-order quantity tends to zero with the amplitude `s`. -/
theorem tendsto_of_o_one (hs : Tendsto s L (𝓝 0)) {E : Type*} [NormedAddCommGroup E]
    {f : B → E} (hf : f =O[L] fun b => s b ^ 1) : Tendsto f L (𝓝 0) :=
  hf.trans_tendsto (by simpa using hs.pow 1)

/-- Woodford (2003), App. E, p. 693: powers of a first-order quantity, `fⁿ = O(sⁿ)`. -/
theorem o_pow {f : B → ℝ} (hf : f =O[L] fun b => s b ^ 1) (n : ℕ) :
    (fun b => f b ^ n) =O[L] fun b => s b ^ n :=
  (hf.pow n).congr_right fun b => by ring

/-- Woodford (2003), App. E, p. 693: the exponential atom `r₃(x) = eˣ − 1 − x − x²/2` of a
first-order quantity is of third order. -/
theorem expRem_o (hs : Tendsto s L (𝓝 0)) {x : B → ℝ} (hx : x =O[L] fun b => s b ^ 1) :
    (fun b => expRem (x b)) =O[L] fun b => s b ^ 3 := by
  have h := ExpLogCES.exp_taylor2_isBigO.comp_tendsto (tendsto_of_o_one hs hx)
  refine (h.trans (o_pow hx 3)).congr_left fun b => ?_
  simp only [Function.comp, expRem]
  ring

/-- Woodford (2003), App. E, p. 693: the log atom `rlog(u) = log(1 + u) − u + u²/2` of a
first-order quantity is of third order. -/
theorem rlog_o (hs : Tendsto s L (𝓝 0)) {x : B → ℝ} (hx : x =O[L] fun b => s b ^ 1) :
    (fun b => rlog (x b)) =O[L] fun b => s b ^ 3 := by
  have h := ExpLogCES.log_taylor2_isBigO.comp_tendsto (tendsto_of_o_one hs hx)
  refine (h.trans (o_pow hx 3)).congr_left fun b => ?_
  simp only [Function.comp, rlog]
  ring

/-! ## Second-order Taylor expansion of the actual utility along a family -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Woodford (2003), eq. (1.2), p. 385, along a one-parameter family with a MOVING base point:
if `U` is `C³`, the expansion points `z̄_b` converge to `z̄₀` and the deviations `z_b` are
`O(s)`, then `U(z̄_b + z_b) − [U(z̄_b) + DU(z̄_b) z_b + ½ D²U(z̄_b)(z_b, z_b)] = O(s³)`. The
constant is uniform because `D²U` is Lipschitz on a fixed ball around `z̄₀`. (A moving base
point is the steady state of a distorted economy whose distortion shrinks with `s`.) -/
theorem taylor_family_moving {U : F → ℝ} (hU : ContDiff ℝ 3 U) {z0 : F} {zb z : B → F}
    (hzb : Tendsto zb L (𝓝 z0)) (hs : Tendsto s L (𝓝 0)) (hz : z =O[L] fun b => s b ^ 1) :
    (fun b => U (zb b + z b) - ApproxTheory.quadApprox (U (zb b)) (fderiv ℝ U (zb b))
      (fderiv ℝ (fderiv ℝ U) (zb b)) (z b)) =O[L] fun b => s b ^ 3 := by
  have h1 : ContDiff ℝ 2 (fderiv ℝ U) := hU.fderiv_right (by norm_num)
  have h2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ U)) := h1.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := h2.contDiffAt.exists_lipschitzOnWith (x := z0)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 ht
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hz0 : Tendsto z L (𝓝 0) := tendsto_of_o_one hs hz
  have hzn : (fun b => ‖z b‖ ^ 3) =O[L] fun b => s b ^ 3 :=
    (hz.norm_left.pow 3).congr_right fun b => by ring
  refine (IsBigO.of_bound K ?_).trans hzn
  filter_upwards [hzb.eventually_mem (Metric.ball_mem_nhds z0 hδ2),
    hz0.eventually_mem (Metric.ball_mem_nhds 0 hδ2)] with b hb hzb'
  have hsub : Metric.ball (zb b) (δ / 2) ⊆ Metric.ball z0 δ := by
    intro w hw
    rw [Metric.mem_ball] at hw hb ⊢
    calc dist w z0 ≤ dist w (zb b) + dist (zb b) z0 := dist_triangle _ _ _
      _ < δ / 2 + δ / 2 := add_lt_add hw hb
      _ = δ := by ring
  have hzb0 : zb b ∈ Metric.ball z0 δ := hsub (Metric.mem_ball_self hδ2)
  have key := ApproxTheory.taylor2_multivar_bound (U1 := fderiv ℝ U)
    (U2 := fderiv ℝ (fderiv ℝ U)) (zbar := zb b) (δ := δ / 2) K.coe_nonneg
    (fun w _ => (hU.differentiable (by norm_num) w).hasFDerivAt)
    (fun w _ => (h1.differentiable (by norm_num) w).hasFDerivAt)
    (fun w hw => by
      have := hK.dist_le_mul w (hball (hsub hw)) (zb b) (hball hzb0)
      simpa [dist_eq_norm] using this)
    (by simpa using hzb')
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_norm]
  exact key

/-- Woodford (2003), eq. (1.2), p. 385, along a one-parameter family with a fixed base point
`z̄`: `U(z̄ + z_b) − [Ū + DU z_b + ½ D²U(z_b, z_b)] = O(s³)` when `z_b = O(s)`. -/
theorem taylor_family {U : F → ℝ} (hU : ContDiff ℝ 3 U) (zbar : F) (hs : Tendsto s L (𝓝 0))
    {z : B → F} (hz : z =O[L] fun b => s b ^ 1) :
    (fun b => U (zbar + z b) - ApproxTheory.quadApprox (U zbar) (fderiv ℝ U zbar)
      (fderiv ℝ (fderiv ℝ U) zbar) (z b)) =O[L] fun b => s b ^ 3 :=
  taylor_family_moving (zb := fun _ => zbar) hU tendsto_const_nhds hs hz

/-- Woodford (2003), Assumption 6.1 and (E.15), p. 699 (ONE-SIDED expansion): if the actual
utility `U` agrees on a set `S` (e.g. `m ≤ m̄`, the region below satiation) with a `C³`
function `Ũ` (its smooth extension from that side), and the family eventually stays in `S`,
then `U` has the second-order expansion of `Ũ` along the family, with the one-sided derivatives
of `U` (those of `Ũ`) as coefficients. -/
theorem taylor_family_of_eqOn {U Ut : F → ℝ} (hU : ContDiff ℝ 3 Ut) {S : Set F}
    (hEq : Set.EqOn U Ut S) (zbar : F) (hs : Tendsto s L (𝓝 0)) {z : B → F}
    (hz : z =O[L] fun b => s b ^ 1) (hS : ∀ᶠ b in L, zbar + z b ∈ S) :
    (fun b => U (zbar + z b) - ApproxTheory.quadApprox (Ut zbar) (fderiv ℝ Ut zbar)
      (fderiv ℝ (fderiv ℝ Ut) zbar) (z b)) =O[L] fun b => s b ^ 3 := by
  refine (taylor_family hU zbar hs hz).congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [hS] with b hb
  rw [hEq hb]

/-! ### Utility of a level and a disturbance: the coefficients of (E.2)–(E.3) -/

variable {Ξ : Type*} [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]

/-- Woodford (2003), (E.2), p. 692: the marginal utility `u_c = ∂U/∂Y` at `z`. -/
noncomputable def dY (U : ℝ × Ξ → ℝ) (z : ℝ × Ξ) : ℝ := fderiv ℝ U z (1, 0)

/-- Woodford (2003), (E.2), p. 692: the second derivative `u_cc = ∂²U/∂Y²` at `z`. -/
noncomputable def dYY (U : ℝ × Ξ → ℝ) (z : ℝ × Ξ) : ℝ := fderiv ℝ (fderiv ℝ U) z (1, 0) (1, 0)

/-- Woodford (2003), (E.2), p. 692: the shock derivative `u_ξ ξ̃` at `z`. -/
noncomputable def dXi (U : ℝ × Ξ → ℝ) (z : ℝ × Ξ) (ξ : Ξ) : ℝ := fderiv ℝ U z (0, ξ)

/-- Woodford (2003), (E.2), p. 692: the (symmetrised) cross derivative `u_cξ ξ̃` at `z`. -/
noncomputable def dYXi (U : ℝ × Ξ → ℝ) (z : ℝ × Ξ) (ξ : Ξ) : ℝ :=
  (fderiv ℝ (fderiv ℝ U) z (1, 0) (0, ξ) + fderiv ℝ (fderiv ℝ U) z (0, ξ) (1, 0)) / 2

/-- Woodford (2003), (E.2), p. 692: the shock quadratic form `ξ̃′u_ξξ ξ̃` at `z`. -/
noncomputable def dXiXi (U : ℝ × Ξ → ℝ) (z : ℝ × Ξ) (ξ : Ξ) : ℝ :=
  fderiv ℝ (fderiv ℝ U) z (0, ξ) (0, ξ)

/-- Woodford (2003), (E.2)–(E.3), pp. 692–693: on `ℝ × Ξ` the quadratic approximation of
eq. (1.2) at `(Ȳ, 0)` is exactly the book's polynomial `Prop61.uTaylor` in the level deviation
`Ỹ` with the derivatives `u_c`, `u_cc`, `u_ξξ̃`, `u_cξξ̃`, `ξ̃′u_ξξξ̃`. -/
theorem quadApprox_prod (U : ℝ × Ξ → ℝ) (z : ℝ × Ξ) (a : ℝ) (ξ : Ξ) :
    ApproxTheory.quadApprox (U z) (fderiv ℝ U z) (fderiv ℝ (fderiv ℝ U) z) (a, ξ) =
      Prop61.uTaylor (U z) (dY U z) (dYY U z) (dXi U z ξ) (dYXi U z ξ) (dXiXi U z ξ) a := by
  have e : ((a, ξ) : ℝ × Ξ) = a • ((1 : ℝ), (0 : Ξ)) + ((0 : ℝ), ξ) := by
    ext <;> simp
  rw [e]
  simp only [ApproxTheory.quadApprox, Prop61.uTaylor, dY, dYY, dXi, dYXi, dXiXi, map_add,
    map_smul, add_apply, smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), (E.2), p. 692, as an analytic statement: for `C³` utility `U(Y, ξ)` and a
family with level deviation `Ỹ_b = O(s)` and disturbance `ξ_b = O(s)`,
`U(Ȳ + Ỹ_b, ξ_b) − uTaylor(Ỹ_b) = O(s³)`, the coefficients being the actual derivatives. -/
theorem uTaylor_family {U : ℝ × Ξ → ℝ} (hU : ContDiff ℝ 3 U) (Ybar : ℝ)
    (hs : Tendsto s L (𝓝 0)) {Yt : B → ℝ} {ξ : B → Ξ} (hY : Yt =O[L] fun b => s b ^ 1)
    (hξ : ξ =O[L] fun b => s b ^ 1) :
    (fun b => U (Ybar + Yt b, ξ b) - Prop61.uTaylor (U (Ybar, 0)) (dY U (Ybar, 0))
      (dYY U (Ybar, 0)) (dXi U (Ybar, 0) (ξ b)) (dYXi U (Ybar, 0) (ξ b))
      (dXiXi U (Ybar, 0) (ξ b)) (Yt b)) =O[L] fun b => s b ^ 3 := by
  have h := taylor_family (z := fun b => (Yt b, ξ b)) hU (Ybar, 0) hs (hY.prod_left hξ)
  refine h.congr_left fun b => ?_
  rw [quadApprox_prod]
  simp

/-- Woodford (2003), (E.2), p. 692, in log deviations: with `Y = Ȳ e^{x}` and
`Ỹ = Ȳ(x + x²/2 + r₃(x))` (`Prop61.levelDev_eq`), `U(Ȳe^{x_b}, ξ_b) − uTaylor(Ỹ_b) = O(s³)`. -/
theorem uTaylor_family_exp {U : ℝ × Ξ → ℝ} (hU : ContDiff ℝ 3 U) (Ybar : ℝ)
    (hs : Tendsto s L (𝓝 0)) {x : B → ℝ} {ξ : B → Ξ} (hx : x =O[L] fun b => s b ^ 1)
    (hξ : ξ =O[L] fun b => s b ^ 1) :
    (fun b => U (Ybar * Real.exp (x b), ξ b) - Prop61.uTaylor (U (Ybar, 0)) (dY U (Ybar, 0))
      (dYY U (Ybar, 0)) (dXi U (Ybar, 0) (ξ b)) (dYXi U (Ybar, 0) (ξ b))
      (dXiXi U (Ybar, 0) (ξ b)) (Ybar * (x b + x b ^ 2 / 2 + expRem (x b))))
      =O[L] fun b => s b ^ 3 := by
  have hYt : (fun b => Ybar * (Real.exp (x b) - 1)) =O[L] fun b => s b ^ 1 := by
    have h2 := o_weaken hs (by norm_num : 1 ≤ 2) (o_pow hx 2)
    have h3 := o_weaken hs (by norm_num : 1 ≤ 3) (expRem_o hs hx)
    refine (((hx.add (h2.const_mul_left (1 / 2))).add h3).const_mul_left Ybar).congr_left
      fun b => ?_
    rw [ExpLogCES.exp_sub_one_eq]
    ring
  refine (uTaylor_family hU Ybar hs hYt hξ).congr_left fun b => ?_
  have e1 : Ybar + Ybar * (Real.exp (x b) - 1) = Ybar * Real.exp (x b) := by ring
  have e2 : Ybar * (Real.exp (x b) - 1) = Ybar * (x b + x b ^ 2 / 2 + expRem (x b)) := by
    rw [ExpLogCES.exp_sub_one_eq]
  rw [e1, e2]

/-! ## Large distortions (§5): the period utility (5.1) from primitives -/

variable {ι : Type*} [Fintype ι]

/-- Woodford (2003), eq. (2.6), p. 393: `Ŷ = log(Y/Ȳ)`, the log of the Dixit–Stiglitz index
(elasticity `θ`) of the relative outputs `e^{ŷ(i)} = y(i)/Ȳ`. -/
noncomputable def logYidx (w : ι → ℝ) (θ : ℝ) (yh : ι → ℝ) : ℝ :=
  Real.log (ExpLogCES.cesIndex w (1 - θ⁻¹) (fun i => Real.exp (yh i)))

/-- Woodford (2003), App. E, p. 693: each good's `ŷ(i)` is `O(s)` when the cross-section is
`O(s)` in the sup norm. -/
theorem coord_o {yh : B → ι → ℝ} (hyh : yh =O[L] fun b => s b ^ 1) (i : ι) :
    (fun b => yh b i) =O[L] fun b => s b ^ 1 :=
  (IsBigO.of_bound 1 (Eventually.of_forall fun b => by
    rw [one_mul]; exact norm_le_pi_norm (yh b) i)).trans hyh

/-- Woodford (2003), App. E, p. 693: `E_i ŷ = O(s)`. -/
theorem crossMean_o {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {yh : B → ι → ℝ}
    (hyh : yh =O[L] fun b => s b ^ 1) : (fun b => crossMean w (yh b)) =O[L] fun b => s b ^ 1 :=
  (IsBigO.of_bound 1 (Eventually.of_forall fun b => by
    rw [one_mul, Real.norm_eq_abs]; exact ExpLogCES.abs_crossMean_le hw0 hw1 (yh b))).trans hyh

/-- Woodford (2003), App. E, p. 693: `var_i ŷ = O(s²)`. -/
theorem crossVar_o {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {yh : B → ι → ℝ}
    (hyh : yh =O[L] fun b => s b ^ 1) : (fun b => crossVar w (yh b)) =O[L] fun b => s b ^ 2 := by
  refine (IsBigO.of_bound 1 (Eventually.of_forall fun b => ?_)).trans
    ((hyh.norm_left.pow 2).congr_right fun b => by ring)
  have h := ExpLogCES.crossVar_le hw0 hw1 (yh b)
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h.1, abs_pow, abs_norm]
  exact h.2

/-- Woodford (2003), (E.5), p. 694: the log output index `Ŷ` of an `O(s)` cross-section is
`O(s)`. -/
theorem logYidx_o (hs : Tendsto s L (𝓝 0)) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {θ : ℝ} (hθ : θ ≠ 1) {yh : B → ι → ℝ}
    (hyh : yh =O[L] fun b => s b ^ 1) :
    (fun b => logYidx w θ (yh b)) =O[L] fun b => s b ^ 1 := by
  have h := (ExpLogCES.log_outputIndex_expansion hw0 hw1 hθ).comp_tendsto
    (tendsto_of_o_one hs hyh)
  have h3 : (fun b => ‖yh b‖ ^ 3) =O[L] fun b => s b ^ 3 :=
    (hyh.norm_left.pow 3).congr_right fun b => by ring
  have hr := o_weaken hs (by norm_num : 1 ≤ 3) (h.trans h3)
  have hm := crossMean_o hw0 hw1 hyh
  have hv := o_weaken hs (by norm_num : 1 ≤ 2) (crossVar_o hw0 hw1 hyh)
  refine ((hr.add hm).add (hv.const_mul_left (1 / 2 * (1 - θ⁻¹)))).congr_left fun b => ?_
  simp only [Function.comp, logYidx]
  ring

/-- Woodford (2003), (E.5), p. 694: the CES atom `r_C` of an `O(s)` cross-section is `O(s³)`
(`Links.CES.cesAtom_isBigO` along the family). -/
theorem cesAtom_o (hs : Tendsto s L (𝓝 0)) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {θ : ℝ} (hθ : θ ≠ 1) {yh : B → ι → ℝ}
    (hyh : yh =O[L] fun b => s b ^ 1) :
    (fun b => Links.CES.cesAtom w θ (yh b)) =O[L] fun b => s b ^ 3 :=
  ((Links.CES.cesAtom_isBigO hw0 hw1 hθ).comp_tendsto (tendsto_of_o_one hs hyh)).trans
    ((hyh.norm_left.pow 3).congr_right fun b => by ring)

/-- Woodford (2003), (E.2): the remainder `Ru` is `O(s³)` whenever `g, Ŷ = O(s)` and its atom
`r = O(s³)` (the atom need not be `s³` times a constant). -/
theorem Ru_o (hs : Tendsto s L (𝓝 0)) (σ : ℝ) {g Y r : B → ℝ}
    (hg : g =O[L] fun b => s b ^ 1) (hY : Y =O[L] fun b => s b ^ 1)
    (hr : r =O[L] fun b => s b ^ 3) :
    (fun b => Prop61.Ru σ (g b) (Y b) (r b)) =O[L] fun b => s b ^ 3 := by
  have hA : (fun b => Y b ^ 2 / 2 + r b) =O[L] fun b => s b ^ 2 :=
    (((o_pow hY 2).const_mul_left (1 / 2)).add (o_weaken hs (by norm_num) hr)).congr_left
      fun b => by ring
  have hB : (fun b => 2 * Y b + (Y b ^ 2 / 2 + r b)) =O[L] fun b => s b ^ 1 :=
    (hY.const_mul_left 2).add (o_weaken hs (by norm_num) hA)
  have h1 := o_mul hA hB (by norm_num : 2 + 1 = 3)
  have h2 := o_mul hg hA (by norm_num : 1 + 2 = 3)
  refine ((hr.sub (h1.const_mul_left (σ / 2))).add (h2.const_mul_left σ)).congr_left
    fun b => ?_
  unfold Prop61.Ru
  ring

/-- Woodford (2003), (E.3) with `Φ` absorbed in the coefficients (§5): the remainder
`Rv 0` is `O(s³)` whenever `q, ŷ = O(s)` and its atom `r = O(s³)`. -/
theorem Rv0_o (hs : Tendsto s L (𝓝 0)) (ω : ℝ) {q y r : B → ℝ}
    (hq : q =O[L] fun b => s b ^ 1) (hy : y =O[L] fun b => s b ^ 1)
    (hr : r =O[L] fun b => s b ^ 3) :
    (fun b => Prop61.Rv 0 ω (q b) (y b) (r b)) =O[L] fun b => s b ^ 3 := by
  have hA : (fun b => y b ^ 2 / 2 + r b) =O[L] fun b => s b ^ 2 :=
    (((o_pow hy 2).const_mul_left (1 / 2)).add (o_weaken hs (by norm_num) hr)).congr_left
      fun b => by ring
  have hB : (fun b => 2 * y b + (y b ^ 2 / 2 + r b)) =O[L] fun b => s b ^ 1 :=
    (hy.const_mul_left 2).add (o_weaken hs (by norm_num) hA)
  have h1 := o_mul hA hB (by norm_num : 2 + 1 = 3)
  have h2 := o_mul hq hA (by norm_num : 1 + 2 = 3)
  refine ((hr.add (h1.const_mul_left (ω / 2))).sub (h2.const_mul_left ω)).congr_left
    fun b => ?_
  unfold Prop61.Rv
  ring

/-- Woodford (2003), (5.1)/(E.5): the aggregation remainder `Rint` is `O(s³)` whenever
`q, Ŷ = O(s)`, `var_i ŷ = O(s²)` and the CES atom `r_C = O(s³)`. -/
theorem Rint_o (hs : Tendsto s L (𝓝 0)) (θ ω : ℝ) {q Y V rC : B → ℝ}
    (hq : q =O[L] fun b => s b ^ 1) (hY : Y =O[L] fun b => s b ^ 1)
    (hV : V =O[L] fun b => s b ^ 2) (hrC : rC =O[L] fun b => s b ^ 3) :
    (fun b => LargeDistortions.Rint θ ω (q b) (Y b) (V b) (rC b)) =O[L] fun b => s b ^ 3 := by
  have hD : (fun b => rC b - (1 - θ⁻¹) / 2 * V b) =O[L] fun b => s b ^ 2 :=
    (o_weaken hs (by norm_num) hrC).sub (hV.const_mul_left _)
  have h1 := o_weaken hs (by norm_num : 3 ≤ 4) (o_mul hD hD (by norm_num : 2 + 2 = 4))
  have h2 := o_mul hY hD (by norm_num : 1 + 2 = 3)
  have h3 := o_mul hq hD (by norm_num : 1 + 2 = 3)
  refine ((hrC.add ((h1.add (h2.const_mul_left 2)).const_mul_left ((1 + ω) / 2))).sub
    (h3.const_mul_left ω)).congr_left fun b => ?_
  unfold LargeDistortions.Rint
  ring

/-- Woodford (2003), (5.1), p. 455 ("`O(‖ξ‖³)`" with ARBITRARY third-order atoms; `Φ_y` fixed,
not small): if `g, q, Ŷ = O(s)`, `var_i ŷ = O(s²)` and the atoms `r₃(Ŷ)`, `r_C` and the
integrated per-good remainder are `O(s³)` — any functions of that order, not necessarily
`s³` times constants as in `LargeDistortions.R51_scaling` — then `R51 = O(s³)`. -/
theorem R51_o (hs : Tendsto s L (𝓝 0)) (σ ω θ Φ : ℝ) {g q Y V rY rC Rvbar : B → ℝ}
    (hg : g =O[L] fun b => s b ^ 1) (hq : q =O[L] fun b => s b ^ 1)
    (hY : Y =O[L] fun b => s b ^ 1) (hV : V =O[L] fun b => s b ^ 2)
    (hrY : rY =O[L] fun b => s b ^ 3) (hrC : rC =O[L] fun b => s b ^ 3)
    (hRv : Rvbar =O[L] fun b => s b ^ 3) :
    (fun b => LargeDistortions.R51 σ ω θ Φ (g b) (q b) (Y b) (V b) (rY b) (rC b) (Rvbar b))
      =O[L] fun b => s b ^ 3 := by
  have h := (Ru_o hs σ hg hY hrY).sub
    ((hRv.add (Rint_o hs θ ω hq hY hV hrC)).const_mul_left (1 - Φ))
  refine h.congr_left fun b => ?_
  unfold LargeDistortions.R51
  ring

/-- Woodford (2003), (5.1): the policy-independent part of the period utility,
`[ū + u_ξξ̃ + ½ξ̃′u_ξξξ̃] − [v̄ + v_ξξ̃ + ½ξ̃′v_ξξξ̃]` (a function of the disturbances only). -/
noncomputable def tip51 (u v : ℝ × Ξ → ℝ) (Ybar : ℝ) (xu xv : Ξ) : ℝ :=
  (u (Ybar, 0) + dXi u (Ybar, 0) xu + dXiXi u (Ybar, 0) xu / 2) -
    (v (Ybar, 0) + dXi v (Ybar, 0) xv + dXiXi v (Ybar, 0) xv / 2)

/-- Woodford (2003), §2, eq. (2.1) and §5, p. 455: the ACTUAL period utility
`u(Y; ξ) − ∫ v(y(i); ξ) di` of a finite weighted cross-section of goods with outputs
`y(i) = Ȳe^{ŷ(i)}` and the Dixit–Stiglitz aggregate `Y = Ȳe^{Ŷ}` (`logYidx`); the disturbances
`ξ_u`, `ξ_v` enter `u` and `v`. -/
noncomputable def periodU (u v : ℝ × Ξ → ℝ) (w : ι → ℝ) (θ Ybar : ℝ) (yh : ι → ℝ)
    (xu xv : Ξ) : ℝ :=
  u (Ybar * Real.exp (logYidx w θ yh), xu) - ∑ i, w i * v (Ybar * Real.exp (yh i), xv)

/-- Woodford (2003), eq. (5.1), p. 455, PROVED from primitives (Layer B; this discharges the
hypothesis `h51` of `LargeDistortions.prop614`/`prop615` up to `O(s³)`): let `u, v` be `C³`
on `ℝ × Ξ`, expanded at the steady state `(Ȳ, 0)`, where `σ⁻¹ = −Ȳu_cc/u_c`,
`v_y = (1 − Φ_y)u_c` with `Φ_y` FIXED (not small) and `ω = Ȳv_yy/v_y`; let the composite
disturbances be `g = u_cξ ξ_u/(σ⁻¹u_c)` and `q = −v_yξ ξ_v/(ωv_y)` (the book's definitions,
stated as `hg`, `hq`). Along any family with `ŷ(i) = O(s)` uniformly in `i` and disturbances
`O(s)`, the actual period utility is
`−(Ȳu_c/2)·quad51(Ŷ, var_i ŷ) + tip51(ξ) + O(s³)`, `Ŷ` the exact log CES index. -/
theorem eq51_actual (hs : Tendsto s L (𝓝 0)) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {θ : ℝ} (hθ : θ ≠ 1) {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u)
    (hv : ContDiff ℝ 3 v) {Ybar σ ω Φ : ℝ}
    (hucc : dYY u (Ybar, 0) = -(σ * dY u (Ybar, 0) / Ybar))
    (hvy : dY v (Ybar, 0) = (1 - Φ) * dY u (Ybar, 0))
    (hvyy : dYY v (Ybar, 0) = ω * dY v (Ybar, 0) / Ybar)
    {yh : B → ι → ℝ} {xu xv : B → Ξ} {g q : B → ℝ}
    (hyh : yh =O[L] fun b => s b ^ 1) (hxu : xu =O[L] fun b => s b ^ 1)
    (hxv : xv =O[L] fun b => s b ^ 1) (hgO : g =O[L] fun b => s b ^ 1)
    (hqO : q =O[L] fun b => s b ^ 1)
    (hg : ∀ b, dYXi u (Ybar, 0) (xu b) = σ * dY u (Ybar, 0) * g b)
    (hq : ∀ b, dYXi v (Ybar, 0) (xv b) = -(ω * dY v (Ybar, 0) * q b)) :
    (fun b => periodU u v w θ Ybar (yh b) (xu b) (xv b) -
      (-(Ybar * dY u (Ybar, 0) / 2) * LargeDistortions.quad51 σ ω θ Φ (g b) (q b)
          (logYidx w θ (yh b)) (crossVar w (yh b)) + tip51 u v Ybar (xu b) (xv b)))
      =O[L] fun b => s b ^ 3 := by
  have hYO := logYidx_o hs hw0 hw1 hθ hyh
  have hu1 := uTaylor_family_exp hu Ybar hs hYO hxu
  have hvs := IsBigO.fun_sum (s := Finset.univ) fun i _ =>
    (uTaylor_family_exp hv Ybar hs (coord_o hyh i) hxv).const_mul_left (w i)
  have hRv : (fun b => ∑ i, w i * Prop61.Rv 0 ω (q b) (yh b i) (expRem (yh b i)))
      =O[L] fun b => s b ^ 3 :=
    IsBigO.fun_sum (s := Finset.univ) fun i _ =>
      (Rv0_o hs ω hqO (coord_o hyh i) (expRem_o hs (coord_o hyh i))).const_mul_left (w i)
  have hR := R51_o hs σ ω θ Φ hgO hqO hYO (crossVar_o hw0 hw1 hyh) (expRem_o hs hYO)
    (cesAtom_o hs hw0 hw1 hθ hyh) hRv
  refine ((hu1.sub hvs).add (hR.const_mul_left (Ybar * dY u (Ybar, 0)))).congr_left
    fun b => ?_
  have key := Links.CES.eq51_ces w hw1 (Ybar := Ybar) (ucxi := dYXi u (Ybar, 0) (xu b))
    (vyxi := dYXi v (Ybar, 0) (xv b)) hucc (hg b) hvy hvyy (hq b) (u (Ybar, 0))
    (dXi u (Ybar, 0) (xu b)) (dXiXi u (Ybar, 0) (xu b)) (v (Ybar, 0))
    (dXi v (Ybar, 0) (xv b)) (dXiXi v (Ybar, 0) (xv b)) (logYidx w θ (yh b))
    (expRem (logYidx w θ (yh b))) (yh b) (fun i => expRem (yh b i)) rfl
  have hsum : ∑ i, w i * (v (Ybar * Real.exp (yh b i), xv b) -
      Prop61.uTaylor (v (Ybar, 0)) (dY v (Ybar, 0)) (dYY v (Ybar, 0)) (dXi v (Ybar, 0) (xv b))
        (dYXi v (Ybar, 0) (xv b)) (dXiXi v (Ybar, 0) (xv b))
        (Ybar * (yh b i + yh b i ^ 2 / 2 + expRem (yh b i)))) =
      ∑ i, w i * v (Ybar * Real.exp (yh b i), xv b) -
        ∑ i, w i * Prop61.vTaylor (v (Ybar, 0)) (dY v (Ybar, 0)) (dYY v (Ybar, 0))
          (dXi v (Ybar, 0) (xv b)) (dYXi v (Ybar, 0) (xv b)) (dXiXi v (Ybar, 0) (xv b))
          (Ybar * (yh b i + yh b i ^ 2 / 2 + expRem (yh b i))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold Prop61.uTaylor Prop61.vTaylor
    ring
  rw [hsum]
  unfold periodU tip51
  linear_combination (-1 : ℝ) * key

/-- Woodford (2003), (5.1): the policy-independent terms are a first-order perturbation of
their value without disturbances, `tip51(ξ) − tip51(0) = O(s)` when `ξ = O(s)`. -/
theorem tip51_o (hs : Tendsto s L (𝓝 0)) (u v : ℝ × Ξ → ℝ) (Ybar : ℝ) {xu xv : B → Ξ}
    (hxu : xu =O[L] fun b => s b ^ 1) (hxv : xv =O[L] fun b => s b ^ 1) :
    (fun b => tip51 u v Ybar (xu b) (xv b) - tip51 u v Ybar 0 0) =O[L] fun b => s b ^ 1 := by
  have hz : ∀ x : B → Ξ, x =O[L] (fun b => s b ^ 1) →
      (fun b => ((0 : ℝ), x b)) =O[L] fun b => s b ^ 1 := fun x hx =>
    (isBigO_zero (fun b => s b ^ 1) L).prod_left hx
  have h1 : ∀ (U : ℝ × Ξ → ℝ) (x : B → Ξ), x =O[L] (fun b => s b ^ 1) →
      (fun b => dXi U (Ybar, 0) (x b)) =O[L] fun b => s b ^ 1 := fun U x hx =>
    ((fderiv ℝ U (Ybar, 0)).isBigO_comp _ L).trans (hz x hx)
  have h2 : ∀ (U : ℝ × Ξ → ℝ) (x : B → Ξ), x =O[L] (fun b => s b ^ 1) →
      (fun b => dXiXi U (Ybar, 0) (x b)) =O[L] fun b => s b ^ 1 := fun U x hx =>
    o_weaken hs (by norm_num : 1 ≤ 2) ((ApproxTheory.bilin_isBigO
      (fderiv ℝ (fderiv ℝ U) (Ybar, 0)) (hz x hx) (hz x hx)).congr_right fun b => by ring)
  refine ((((h1 u xu hxu).add ((h2 u xu hxu).const_mul_left (1 / 2))).sub
    ((h1 v xv hxv).add ((h2 v xv hxv).const_mul_left (1 / 2))))).congr_left fun b => ?_
  simp only [tip51, dXi, dXiXi, Prod.mk_zero_zero, map_zero]
  ring

/-! ## Uniformity in the date and the state: discounted sums

Woodford's `O(‖ξ‖³)` for a discounted sum `∑βᵗE_0 R_t` needs the per-period remainder to be
`O(ε³)` UNIFORMLY in the date `t` and the state: we assume every first-order variable is
bounded by `C|ε|` for all `t` and all states (the book's "bounded fluctuations" of
§2, p. 394; for a finite state space and stationary shock processes this is a bound on
finitely many coefficient vectors). Formally a family `X : A → ℕ → Ω → E` is `UProc l X g`
when `X = O(g)` along the product filter `l ×ˢ ⊤` on `A × (ℕ × Ω)`, i.e. with ONE constant
for all `(t, ω)`. The period-utility results above, proved for an arbitrary filter, then apply
verbatim with `L = l ×ˢ ⊤`, and the geometric weights turn the uniform bound into an `O(ε³)`
bound for the discounted sum (`dsum_o`). -/

variable {A : Type*} {l : Filter A} {e : A → ℝ}

/-- Woodford (2003), §2, p. 394 (uniform orders): a family of processes is `O(g)` uniformly in
the date and the state. -/
def UProc {Ω E : Type*} [Norm E] (l : Filter A) (X : A → ℕ → Ω → E) (g : A → ℝ) : Prop :=
  (fun p : A × (ℕ × Ω) => X p.1 p.2.1 p.2.2) =O[l ×ˢ (⊤ : Filter (ℕ × Ω))] fun p => g p.1

/-- Woodford (2003), §2, p. 394: a uniform order bound gives ONE constant for every index. -/
theorem uniform_bound {J : Type*} {f : A × J → ℝ} {g : A → ℝ}
    (h : f =O[l ×ˢ (⊤ : Filter J)] fun p => g p.1) :
    ∃ C, ∀ᶠ a in l, ∀ j, |f (a, j)| ≤ C * |g a| := by
  obtain ⟨C, hC⟩ := h.bound
  refine ⟨C, ?_⟩
  rw [Filter.prod_top, Filter.eventually_comap] at hC
  filter_upwards [hC] with a ha j
  simpa [Real.norm_eq_abs] using ha (a, j) rfl

/-- Woodford (2003), §2, p. 394: the amplitude, viewed on `A × (ℕ × Ω)`, still tends to `0`. -/
theorem tendsto_amp {J : Type*} (he : Tendsto e l (𝓝 0)) :
    Tendsto (fun p : A × J => e p.1) (l ×ˢ (⊤ : Filter J)) (𝓝 0) :=
  he.comp tendsto_fst

/-- Woodford (2003), (5.2), p. 456 (uniform orders and discounting): if `X_t(ω) = O(g)`
uniformly in `(t, ω)` and `0 ≤ β < 1`, then `∑βᵗE_0 X_t = O(g)`. -/
theorem dsum_o {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {X : A → ℕ → Ω → ℝ} {g : A → ℝ} (h : UProc l X g) (w0 : Ω) :
    (fun a => Sequences.dsum 𝔼 β (X a) w0) =O[l] g := by
  obtain ⟨C, hC⟩ := uniform_bound h
  refine IsBigO.of_bound (C / (1 - β)) ?_
  filter_upwards [hC] with a ha
  have hb : ∀ t, |𝔼.E 0 (X a t) w0| ≤ C * |g a| := fun t =>
    𝔼.abs_E_le (fun ω => ha (t, ω)) 0 w0
  have h1 := Sequences.abs_tsum_le hb hβ0 hβ1
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  unfold Sequences.dsum
  calc _ ≤ C * |g a| / (1 - β) := h1
    _ = C / (1 - β) * |g a| := by ring

/-- Woodford (2003), (5.4) (the `β E_t` part of the remainder): conditional expectations keep
uniform orders: if `X = O(g)` uniformly then so is `E_t X_{t+1}`. -/
theorem condE_o {Ω : Type*} (𝔼 : ExpectationSystem Ω) {X : A → ℕ → Ω → ℝ} {g : A → ℝ}
    (h : UProc l X g) : UProc l (fun a t => 𝔼.E t (X a (t + 1))) g := by
  obtain ⟨C, hC⟩ := uniform_bound h
  refine IsBigO.of_bound C ?_
  rw [Filter.prod_top, Filter.eventually_comap]
  filter_upwards [hC] with a ha p hp
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hp]
  exact 𝔼.abs_E_le (fun ω => ha (p.2.1 + 1, ω)) _ _

/-- Woodford (2003), §2, p. 394: a uniformly `O(eᵏ)` family plus a constant is a bounded
process for every amplitude close enough to `0`. -/
theorem bdd_of_o {Ω : Type*} (he : Tendsto e l (𝓝 0)) {X : A → ℕ → Ω → ℝ} {k : ℕ} (c : ℝ)
    (h : UProc l (fun a t ω => X a t ω - c) fun a => e a ^ k) :
    ∀ᶠ a in l, BoundedProc (X a) := by
  obtain ⟨C, hC⟩ := uniform_bound (g := fun a => e a ^ k)
    (f := fun p : A × (ℕ × Ω) => X p.1 p.2.1 p.2.2 - c) h
  have h1 : ∀ᶠ a in l, |e a| ≤ 1 := by
    filter_upwards [he.eventually (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)] with a ha
    simpa [Real.dist_eq] using ha
  filter_upwards [hC, h1] with a ha h1a
  refine ⟨|c| + |C|, fun t ω => ?_⟩
  have hb := ha (t, ω)
  have hp : |e a ^ k| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) h1a
  have hC' : C * |e a ^ k| ≤ |C| := by
    calc C * |e a ^ k| ≤ |C| * |e a ^ k| :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg _)
      _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left hp (abs_nonneg C)
      _ = |C| := mul_one _
  have := abs_sub_abs_le_abs_sub (X a t ω) c
  linarith

/-- Woodford (2003), (5.2): `∑βᵗE_0X_t − ∑βᵗE_0Y_t = ∑βᵗE_0(X_t − Y_t)` for bounded
processes. -/
theorem dsum_sub {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β : ℝ} (hβ : |β| < 1)
    {X Y : ℕ → Ω → ℝ} (hX : BoundedProc X) (hY : BoundedProc Y) (w0 : Ω) :
    Sequences.dsum 𝔼 β X w0 - Sequences.dsum 𝔼 β Y w0 =
      Sequences.dsum 𝔼 β (fun t => X t - Y t) w0 := by
  have h := (Sequences.hasSum_dsum 𝔼 hβ hX w0).sub (Sequences.hasSum_dsum 𝔼 hβ hY w0)
  refine (h.congr_fun fun t => ?_).tsum_eq.symm
  simp only [map_sub, Pi.sub_apply]
  ring

/-- Woodford (2003), §2, p. 394: a uniformly `O(eᵏ)` family is a bounded process for every
amplitude close enough to `0`. -/
theorem bdd_of_o0 {Ω : Type*} (he : Tendsto e l (𝓝 0)) {X : A → ℕ → Ω → ℝ} {k : ℕ}
    (h : UProc l X fun a => e a ^ k) : ∀ᶠ a in l, BoundedProc (X a) :=
  bdd_of_o he 0 ((show (fun p : A × (ℕ × Ω) => X p.1 p.2.1 p.2.2) =O[l ×ˢ ⊤]
    fun p => e p.1 ^ k from h).congr_left fun p => by simp)

/-! ## Proposition 6.14 (Layer B): large distortions, the loss with a linear term -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), **Proposition 6.14**, (5.2)–(5.3), p. 456, LAYER B (from the ACTUAL
utility, `Φ_y` fixed, the family in the disturbances only). For each amplitude `a` the economy
has goods' log outputs `ŷ_t(i)`, disturbances `ξ_u, ξ_v` (composite `g, q` as in
`eq51_actual`), inflation `π`, mean-price inflation `π̄` and price dispersion `D`
(`D_{t+1} = Δ_t`), obeying (2.12) (`hV`) and the Calvo law (`hD`). If every first-order
variable is `O(ε)`, `π̄ − π = O(ε²)` (Prop. 6.3, `Links.CES.eDisc_isBigO`) and `D = O(ε²)`,
all UNIFORMLY in the date and state (`UProc`), then
`∑βᵗE_0 U_t = −Ω ∑βᵗE_0 L_t + t.i.p. + O(ε³)`, where `U_t` is the actual period utility
`u(Y_t; ξ_t) − ∫v(y_t(i); ξ_t)di`, `L_t = π_t² + λ_yyŶ_t² − 2γ_tŶ_t` is evaluated on the
actual path (it has a LINEAR term in `Ŷ` because `Φ_y` is not small, see
`prop614_first_order`), and the t.i.p. `∑βᵗE_0 tip51 − Ω(1−α)E_0Δ_{−1}` depends only on the
disturbances and the initial dispersion. -/
theorem prop614_layerB {α β θ ω σ Φ Ybar : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ : 0 < θ) (hθ1 : θ ≠ 1) (hω : 0 < ω) (hσ : 0 < σ) (hΦ : Φ < 1)
    (he : Tendsto e l (𝓝 0)) {wt : ι → ℝ} (hw0 : ∀ i, 0 ≤ wt i) (hw1 : ∑ i, wt i = 1)
    {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    (hucc : dYY u (Ybar, 0) = -(σ * dY u (Ybar, 0) / Ybar))
    (hvy : dY v (Ybar, 0) = (1 - Φ) * dY u (Ybar, 0))
    (hvyy : dYY v (Ybar, 0) = ω * dY v (Ybar, 0) / Ybar)
    {yh : A → ℕ → Ω → ι → ℝ} {xu xv : A → ℕ → Ω → Ξ} {g q infl D pib : A → ℕ → Ω → ℝ}
    (hyh : UProc l yh fun a => e a ^ 1) (hxu : UProc l xu fun a => e a ^ 1)
    (hxv : UProc l xv fun a => e a ^ 1) (hgO : UProc l g fun a => e a ^ 1)
    (hqO : UProc l q fun a => e a ^ 1) (hiO : UProc l infl fun a => e a ^ 1)
    (hpO : UProc l (fun a t z => pib a t z - infl a t z) fun a => e a ^ 2)
    (hDO : UProc l D fun a => e a ^ 2)
    (hg : ∀ a t z, dYXi u (Ybar, 0) (xu a t z) = σ * dY u (Ybar, 0) * g a t z)
    (hq : ∀ a t z, dYXi v (Ybar, 0) (xv a t z) = -(ω * dY v (Ybar, 0) * q a t z))
    (hV : ∀ a t, (fun z => crossVar wt (yh a t z)) = θ ^ 2 • D a (t + 1))
    (hD : ∀ a t, D a (t + 1) = α • D a t + (α / (1 - α)) • pib a t ^ 2) (w0 : Ω) :
    (fun a => Sequences.dsum 𝔼 β
        (fun t z => periodU u v wt θ Ybar (yh a t z) (xu a t z) (xv a t z)) w0 -
      (-LargeDistortions.OmegaW Ybar (dY u (Ybar, 0)) (Moments.calvoKappa α β ω θ σ) θ Φ ω σ *
          Sequences.dsum 𝔼 β (LargeDistortions.loss614 (Moments.calvoKappa α β ω θ σ) θ Φ ω σ
            (infl a) (fun t z => logYidx wt θ (yh a t z)) (g a) (q a)) w0 +
        (Sequences.dsum 𝔼 β (fun t z => tip51 u v Ybar (xu a t z) (xv a t z)) w0 -
          LargeDistortions.OmegaW Ybar (dY u (Ybar, 0)) (Moments.calvoKappa α β ω θ σ) θ Φ ω σ *
            (1 - α) * 𝔼.E 0 (D a 0) w0)))
      =O[l] fun a => e a ^ 3 := by
  have hs := tendsto_amp (J := ℕ × Ω) he
  have hβ : |β| < 1 := by rw [abs_lt]; constructor <;> linarith
  set Om := LargeDistortions.OmegaW Ybar (dY u (Ybar, 0)) (Moments.calvoKappa α β ω θ σ) θ Φ ω σ
    with hOm
  -- the per-period remainder, uniformly `O(ε³)` by `eq51_actual`
  set R : A → ℕ → Ω → ℝ := fun a t z =>
    periodU u v wt θ Ybar (yh a t z) (xu a t z) (xv a t z) -
      (-(Ybar * dY u (Ybar, 0) / 2) * LargeDistortions.quad51 σ ω θ Φ (g a t z) (q a t z)
        (logYidx wt θ (yh a t z)) (crossVar wt (yh a t z)) +
          tip51 u v Ybar (xu a t z) (xv a t z)) with hR
  have hRO : UProc l R fun a => e a ^ 3 :=
    eq51_actual (L := l ×ˢ ⊤) (s := fun p : A × (ℕ × Ω) => e p.1) hs hw0 hw1 hθ1 hu hv hucc
      hvy hvyy (yh := fun p => yh p.1 p.2.1 p.2.2) (xu := fun p => xu p.1 p.2.1 p.2.2)
      (xv := fun p => xv p.1 p.2.1 p.2.2) (g := fun p => g p.1 p.2.1 p.2.2)
      (q := fun p => q p.1 p.2.1 p.2.2) hyh hxu hxv hgO hqO (fun p => hg _ _ _)
      (fun p => hq _ _ _)
  -- the inflation-measure discrepancy, uniformly `O(ε³)`
  have hpO' : (fun p : A × (ℕ × Ω) => pib p.1 p.2.1 p.2.2 - infl p.1 p.2.1 p.2.2)
      =O[l ×ˢ ⊤] fun p => e p.1 ^ 2 := hpO
  have hiO' : (fun p : A × (ℕ × Ω) => infl p.1 p.2.1 p.2.2)
      =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 := hiO
  have hPO : UProc l (fun a t => pib a t ^ 2 - infl a t ^ 2) fun a => e a ^ 3 := by
    have h1 := (o_weaken hs (by norm_num : 1 ≤ 2) hpO').add (hiO'.const_mul_left 2)
    refine (o_mul hpO' h1 (by norm_num : 2 + 1 = 3)).congr_left fun p => ?_
    simp only [Pi.sub_apply, Pi.pow_apply]
    ring
  -- boundedness for amplitudes near `0`
  have bY := bdd_of_o0 (X := fun a t z => logYidx wt θ (yh a t z)) he
    (logYidx_o (L := l ×ˢ ⊤) (s := fun p : A × (ℕ × Ω) => e p.1) hs hw0 hw1 hθ1
      (yh := fun p => yh p.1 p.2.1 p.2.2) hyh)
  have bi := bdd_of_o0 he hiO
  have bg := bdd_of_o0 he hgO
  have bq := bdd_of_o0 he hqO
  have bD := bdd_of_o0 he hDO
  have bp := bdd_of_o0 (X := pib) he
    (((o_weaken hs (by norm_num : 1 ≤ 2) hpO').add hiO').congr_left fun p => by ring)
  have bt := bdd_of_o (X := fun a t z => tip51 u v Ybar (xu a t z) (xv a t z)) he
    (tip51 u v Ybar 0 0) (tip51_o (L := l ×ˢ ⊤) (s := fun p : A × (ℕ × Ω) => e p.1) hs u v Ybar
      (xu := fun p => xu p.1 p.2.1 p.2.2) (xv := fun p => xv p.1 p.2.1 p.2.2) hxu hxv)
  have bR := bdd_of_o0 he hRO
  have hev : ∀ᶠ a in l, Sequences.dsum 𝔼 β
        (fun t z => periodU u v wt θ Ybar (yh a t z) (xu a t z) (xv a t z)) w0 -
      (-Om * Sequences.dsum 𝔼 β (LargeDistortions.loss614 (Moments.calvoKappa α β ω θ σ) θ Φ ω σ
            (infl a) (fun t z => logYidx wt θ (yh a t z)) (g a) (q a)) w0 +
        (Sequences.dsum 𝔼 β (fun t z => tip51 u v Ybar (xu a t z) (xv a t z)) w0 -
          Om * (1 - α) * 𝔼.E 0 (D a 0) w0)) =
      Sequences.dsum 𝔼 β (R a) w0 -
        Om * Sequences.dsum 𝔼 β (fun t => pib a t ^ 2 - infl a t ^ 2) w0 := by
    filter_upwards [bY, bi, bg, bq, bD, bp, bt, bR] with a hYb hib hgb hqb hDb hpb htb hRb
    have h51 : ∀ t, (fun z => periodU u v wt θ Ybar (yh a t z) (xu a t z) (xv a t z)) =
        (fun z => -(Ybar * dY u (Ybar, 0) / 2) * LargeDistortions.quad51 σ ω θ Φ (g a t z)
          (q a t z) (logYidx wt θ (yh a t z)) (crossVar wt (yh a t z))) +
          (fun z => tip51 u v Ybar (xu a t z) (xv a t z)) + R a t := by
      intro t
      funext z
      simp only [Pi.add_apply, hR]
      ring
    have h := LargeDistortions.prop614 𝔼 hα0 hα1 hβ0 hβ1 hθ hω hσ hΦ hYb hib hgb hqb hDb hpb htb
      hRb h51 (hV a) (hD a) w0
    rw [h, ← dsum_sub 𝔼 hβ (Sequences.bdd_sq hpb) (Sequences.bdd_sq hib)]
    ring
  exact ((dsum_o 𝔼 hβ0.le hβ1 hRO w0).sub
    ((dsum_o 𝔼 hβ0.le hβ1 hPO w0).const_mul_left Om)).congr'
      (hev.mono fun a ha => ha.symm) (Eventually.of_forall fun _ => rfl)

/-! ## Welfare rankings and first-order solutions -/

/-- Woodford (2003), §1, pp. 386–389 (welfare ranking along any filter, with common
policy-independent terms `T`): if `W_X = T − ε² k L_X + O(ε³)` for both policies, `k > 0`,
`ε → 0`, `ε ≠ 0` eventually, and `L_A < L_B`, then `W_B < W_A` eventually. -/
theorem ranking_of_common (he : Tendsto e l (𝓝 0)) (hne : ∀ᶠ a in l, e a ≠ 0)
    {WA WB T : A → ℝ} {k LA LB : ℝ} (hk : 0 < k)
    (hA : (fun a => WA a - (T a - e a ^ 2 * (k * LA))) =O[l] fun a => e a ^ 3)
    (hB : (fun a => WB a - (T a - e a ^ 2 * (k * LB))) =O[l] fun a => e a ^ 3)
    (hL : LA < LB) : ∀ᶠ a in l, WB a < WA a := by
  refine OneParamTaylor.eventually_lt_of_quadratic_gap (s := e)
    (q := fun a => e a ^ 2 * (k * (LB - LA))) (c := k * (LB - LA)) he
    (mul_pos hk (by linarith)) (Eventually.of_forall fun a => le_of_eq (by ring)) hne ?_
  exact (hA.sub hB).congr_left fun a => by ring

/-- Woodford (2003), §1, pp. 386–389, in the form of `OneParamTaylor.welfare_ranking_of_loss`:
if the common policy-independent terms have a second-order expansion
`T(ε) = w₀ + εw₁ + (ε²/2)τ + O(ε³)` and `W_X = T − ε² k L_X + O(ε³)`, then `W_X` has the
expansion required by `welfare_ranking_of_loss` (with weight `2k` and loss `L_X − τ/(2k)`), and
`L_A < L_B` gives `W_B < W_A` for all small `ε > 0`. -/
theorem ranking_via_loss {WA WB T : ℝ → ℝ} {w0 w1 τ k LA LB : ℝ} (hk : 0 < k)
    (hT : (fun ε => T ε - (w0 + ε * w1 + ε ^ 2 / 2 * τ)) =O[𝓝 0] fun ε => ε ^ 3)
    (hA : (fun ε => WA ε - (T ε - ε ^ 2 * (k * LA))) =O[𝓝 0] fun ε => ε ^ 3)
    (hB : (fun ε => WB ε - (T ε - ε ^ 2 * (k * LB))) =O[𝓝 0] fun ε => ε ^ 3)
    (hL : LA < LB) : ∀ᶠ ε in 𝓝[>] 0, WB ε < WA ε := by
  have h2k : (0 : ℝ) < 2 * k := by linarith
  refine OneParamTaylor.welfare_ranking_of_loss (w0 := w0) (w1 := w1) (k := 2 * k)
    (LA := LA - τ / (2 * k)) (LB := LB - τ / (2 * k)) h2k ?_ ?_ (by linarith)
  · refine (hA.add hT).congr_left fun ε => ?_
    field_simp
    ring
  · refine (hB.add hT).congr_left fun ε => ?_
    field_simp
    ring

/-- Woodford (2003), §5, p. 456 (a FIRST-order welfare ranking): if `W_A − W_B = εc + O(ε²)`
with `c > 0` and `ε > 0` eventually, then `W_B < W_A` eventually. -/
theorem eventually_lt_of_linear_gap (he : Tendsto e l (𝓝 0)) (hpos : ∀ᶠ a in l, 0 < e a)
    {WA WB : A → ℝ} {c : ℝ} (hc : 0 < c)
    (hR : (fun a => WA a - WB a - e a * c) =O[l] fun a => e a ^ 2) :
    ∀ᶠ a in l, WB a < WA a := by
  have h2 : (fun a => e a ^ 2) =o[l] fun a => e a := by
    have := ((isLittleO_one_iff ℝ).2 he).mul_isBigO (isBigO_refl (fun a => e a) l)
    exact this.congr (fun a => by ring) (fun a => by ring)
  filter_upwards [isLittleO_iff.1 (hR.trans_isLittleO h2) (half_pos hc), hpos] with a ha hp
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp] at ha
  have := neg_abs_le (WA a - WB a - e a * c)
  nlinarith

/-- Woodford (2003), App. E (first-order solutions): if `x = εx₁ + O(ε²)` with `x₁` bounded,
then `x² = ε²x₁² + O(ε³)`. -/
theorem sq_sub_o (hs : Tendsto s L (𝓝 0)) {x x1 : B → ℝ}
    (hd : (fun b => x b - s b * x1 b) =O[L] fun b => s b ^ 2)
    (h1 : x1 =O[L] fun _ => (1 : ℝ)) :
    (fun b => x b ^ 2 - s b ^ 2 * x1 b ^ 2) =O[L] fun b => s b ^ 3 := by
  have hsx : (fun b => s b * x1 b) =O[L] fun b => s b ^ 1 :=
    ((isBigO_refl s L).mul h1).congr_right fun b => by ring
  have hsum : (fun b => x b - s b * x1 b + 2 * (s b * x1 b)) =O[L] fun b => s b ^ 1 :=
    (o_weaken hs (by norm_num : 1 ≤ 2) hd).add (hsx.const_mul_left 2)
  exact (o_mul hd hsum (by norm_num : 2 + 1 = 3)).congr_left fun b => by ring

/-- Woodford (2003), §2, p. 394: a bounded process, constant in the amplitude, is `O(1)`
uniformly. -/
theorem uproc_of_bdd {Ω' : Type*} {X : ℕ → Ω' → ℝ} (hX : BoundedProc X) :
    UProc l (fun _ => X) fun _ => (1 : ℝ) := by
  obtain ⟨M, hM⟩ := hX
  refine IsBigO.of_bound M (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, norm_one, mul_one]
  exact hM _ _

/-- Woodford (2003), (5.2): `∑βᵗE_0(cX_t) = c ∑βᵗE_0X_t` for a bounded process. -/
theorem dsum_smul {β : ℝ} (hβ : |β| < 1) {X : ℕ → Ω → ℝ} (hX : BoundedProc X) (c : ℝ)
    (w0 : Ω) : Sequences.dsum 𝔼 β (fun t => c • X t) w0 = c * Sequences.dsum 𝔼 β X w0 := by
  have h := (Sequences.hasSum_dsum 𝔼 hβ hX w0).mul_left c
  refine (h.congr_fun fun t => ?_).tsum_eq
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), Prop. 6.14, p. 456 (THE LINEAR TERM DOES NOT VANISH): when `Φ_y ≠ 0`,
the loss (5.3) evaluated along a family with first-order solution `Ŷ = εŶ₁ + O(ε²)`
(`π, g, q = O(ε)`, uniformly) is FIRST order: `∑βᵗE_0L_t = −2γ̄ ε ∑βᵗE_0Ŷ₁ + O(ε²)` with
`γ̄ = (κ/θ)Φ_y/((1−Φ_y)(ω+σ⁻¹))`. Hence the quadratic terms of (5.3) cannot be evaluated from a
first-order solution alone: the welfare ranking depends on `∑βᵗE_0Ŷ₁` at first order
(`prop614_first_order`). -/
theorem loss614_first_order {κ θ Φ ω σ β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (he : Tendsto e l (𝓝 0)) {infl Y g q : A → ℕ → Ω → ℝ} {Y1 : ℕ → Ω → ℝ}
    (hY1 : BoundedProc Y1) (hiO : UProc l infl fun a => e a ^ 1)
    (hgO : UProc l g fun a => e a ^ 1) (hqO : UProc l q fun a => e a ^ 1)
    (hYd : UProc l (fun a t z => Y a t z - e a * Y1 t z) fun a => e a ^ 2) (w0 : Ω) :
    (fun a => Sequences.dsum 𝔼 β (LargeDistortions.loss614 κ θ Φ ω σ (infl a) (Y a) (g a) (q a))
        w0 - e a * (-2 * (κ / θ * Φ / ((1 - Φ) * (ω + σ))) * Sequences.dsum 𝔼 β Y1 w0))
      =O[l] fun a => e a ^ 2 := by
  have hs := tendsto_amp (J := ℕ × Ω) he
  have hβ : |β| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hYd' : (fun p : A × (ℕ × Ω) => Y p.1 p.2.1 p.2.2 - e p.1 * Y1 p.2.1 p.2.2)
      =O[l ×ˢ ⊤] fun p => e p.1 ^ 2 := hYd
  have hY1' : (fun p : A × (ℕ × Ω) => Y1 p.2.1 p.2.2) =O[l ×ˢ ⊤] fun _ => (1 : ℝ) :=
    uproc_of_bdd hY1
  have hsY1 : (fun p : A × (ℕ × Ω) => e p.1 * Y1 p.2.1 p.2.2) =O[l ×ˢ ⊤]
      fun p => e p.1 ^ 1 := ((isBigO_refl _ _).mul hY1').congr_right fun p => by ring
  have hYO : (fun p : A × (ℕ × Ω) => Y p.1 p.2.1 p.2.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 :=
    ((o_weaken hs (by norm_num : 1 ≤ 2) hYd').add hsY1).congr_left fun p => by ring
  have hiO' : (fun p : A × (ℕ × Ω) => infl p.1 p.2.1 p.2.2) =O[l ×ˢ ⊤]
      fun p => e p.1 ^ 1 := hiO
  have hgO' : (fun p : A × (ℕ × Ω) => g p.1 p.2.1 p.2.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 := hgO
  have hqO' : (fun p : A × (ℕ × Ω) => q p.1 p.2.1 p.2.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 := hqO
  set gb := κ / θ * Φ / ((1 - Φ) * (ω + σ)) with hgb
  set c := κ / θ / ((1 - Φ) * (ω + σ)) with hc
  have hD : UProc l (fun a t z => LargeDistortions.loss614 κ θ Φ ω σ (infl a) (Y a) (g a) (q a)
      t z - (-2 * gb) * (e a * Y1 t z)) fun a => e a ^ 2 := by
    have t1 := o_mul hiO' hiO' (by norm_num : 1 + 1 = 2)
    have t2 := o_mul hYO hYO (by norm_num : 1 + 1 = 2)
    have t3 := o_mul hgO' hYO (by norm_num : 1 + 1 = 2)
    have t4 := o_mul hqO' hYO (by norm_num : 1 + 1 = 2)
    refine ((((t1.add (t2.const_mul_left (LargeDistortions.lamYY κ θ Φ ω σ))).sub
      (hYd'.const_mul_left (2 * gb))).sub (t3.const_mul_left (2 * c * σ))).sub
      (t4.const_mul_left (2 * c * ((1 - Φ) * ω)))).congr_left fun p => ?_
    simp only [LargeDistortions.loss614, LargeDistortions.gamT, hgb, hc]
    ring
  have bY : ∀ᶠ a in l, BoundedProc (Y a) := bdd_of_o0 he hYO
  have bi := bdd_of_o0 he hiO
  have bg := bdd_of_o0 he hgO
  have bq := bdd_of_o0 he hqO
  have hev : ∀ᶠ a in l, Sequences.dsum 𝔼 β (fun t z => LargeDistortions.loss614 κ θ Φ ω σ
        (infl a) (Y a) (g a) (q a) t z - (-2 * gb) * (e a * Y1 t z)) w0 =
      Sequences.dsum 𝔼 β (LargeDistortions.loss614 κ θ Φ ω σ (infl a) (Y a) (g a) (q a)) w0 -
        e a * (-2 * gb * Sequences.dsum 𝔼 β Y1 w0) := by
    filter_upwards [bY, bi, bg, bq] with a hYb hib hgb' hqb
    have hL : BoundedProc (LargeDistortions.loss614 κ θ Φ ω σ (infl a) (Y a) (g a) (q a)) := by
      have bI : ∀ i, BoundedProc (![infl a, Y a, g a, q a] i) := by
        intro i; fin_cases i <;> assumption
      exact Sequences.bdd_congr (Sequences.bdd_of_continuous
        (fun v => v 0 ^ 2 + LargeDistortions.lamYY κ θ Φ ω σ * v 1 ^ 2 -
          2 * LargeDistortions.gamT κ θ Φ ω σ (v 2) (v 3) * v 1)
        (by unfold LargeDistortions.gamT; fun_prop) _ bI) (fun t z => by
          simp [LargeDistortions.loss614])
    have hS : BoundedProc (fun t => ((-2 * gb) * e a) • Y1 t) := by
      obtain ⟨M, hM⟩ := hY1
      exact ⟨|(-2 * gb) * e a| * M, fun t z => by
        simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hM t z) (by positivity)⟩
    have h1 := dsum_smul 𝔼 hβ hY1 ((-2 * gb) * e a) w0
    have h2 := dsum_sub 𝔼 hβ hL hS w0
    rw [show e a * (-2 * gb * Sequences.dsum 𝔼 β Y1 w0) =
      (-2 * gb) * e a * Sequences.dsum 𝔼 β Y1 w0 by ring, ← h1, h2]
    congr 1
    funext t z
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  exact (dsum_o 𝔼 hβ0 hβ1 hD w0).congr' hev (Eventually.of_forall fun _ => rfl)

/-- Woodford (2003), Prop. 6.14, p. 456 (first-order welfare under large distortions): under
the hypotheses of `prop614_layerB`, if output has the first-order solution
`Ŷ = εŶ₁ + O(ε²)` uniformly (`Ŷ₁` bounded), then
`∑βᵗE_0U_t = t.i.p. + ε·Ȳu_cΦ_y·∑βᵗE_0Ŷ₁ + O(ε²)`: with `Φ_y ≠ 0` welfare is affected at FIRST
order by the policy's effect on discounted average output (the linear term of (5.3) does not
vanish), which is why Proposition 6.15 eliminates it with (5.4). -/
theorem prop614_first_order {α β θ ω σ Φ Ybar : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : 0 < θ) (hθ1 : θ ≠ 1) (hω : 0 < ω) (hσ : 0 < σ)
    (hΦ : Φ < 1) (he : Tendsto e l (𝓝 0)) {wt : ι → ℝ} (hw0 : ∀ i, 0 ≤ wt i)
    (hw1 : ∑ i, wt i = 1) {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    (hucc : dYY u (Ybar, 0) = -(σ * dY u (Ybar, 0) / Ybar))
    (hvy : dY v (Ybar, 0) = (1 - Φ) * dY u (Ybar, 0))
    (hvyy : dYY v (Ybar, 0) = ω * dY v (Ybar, 0) / Ybar)
    {yh : A → ℕ → Ω → ι → ℝ} {xu xv : A → ℕ → Ω → Ξ} {g q infl D pib : A → ℕ → Ω → ℝ}
    {Y1 : ℕ → Ω → ℝ} (hY1 : BoundedProc Y1)
    (hyh : UProc l yh fun a => e a ^ 1) (hxu : UProc l xu fun a => e a ^ 1)
    (hxv : UProc l xv fun a => e a ^ 1) (hgO : UProc l g fun a => e a ^ 1)
    (hqO : UProc l q fun a => e a ^ 1) (hiO : UProc l infl fun a => e a ^ 1)
    (hpO : UProc l (fun a t z => pib a t z - infl a t z) fun a => e a ^ 2)
    (hDO : UProc l D fun a => e a ^ 2)
    (hYd : UProc l (fun a t z => logYidx wt θ (yh a t z) - e a * Y1 t z) fun a => e a ^ 2)
    (hg : ∀ a t z, dYXi u (Ybar, 0) (xu a t z) = σ * dY u (Ybar, 0) * g a t z)
    (hq : ∀ a t z, dYXi v (Ybar, 0) (xv a t z) = -(ω * dY v (Ybar, 0) * q a t z))
    (hV : ∀ a t, (fun z => crossVar wt (yh a t z)) = θ ^ 2 • D a (t + 1))
    (hD : ∀ a t, D a (t + 1) = α • D a t + (α / (1 - α)) • pib a t ^ 2) (w0 : Ω) :
    (fun a => Sequences.dsum 𝔼 β
        (fun t z => periodU u v wt θ Ybar (yh a t z) (xu a t z) (xv a t z)) w0 -
      ((Sequences.dsum 𝔼 β (fun t z => tip51 u v Ybar (xu a t z) (xv a t z)) w0 -
          LargeDistortions.OmegaW Ybar (dY u (Ybar, 0)) (Moments.calvoKappa α β ω θ σ) θ Φ ω σ *
            (1 - α) * 𝔼.E 0 (D a 0) w0) +
        e a * (Ybar * dY u (Ybar, 0) * Φ * Sequences.dsum 𝔼 β Y1 w0)))
      =O[l] fun a => e a ^ 2 := by
  have h1 := o_weaken he (by norm_num : 2 ≤ 3) (prop614_layerB 𝔼 hα0 hα1 hβ0 hβ1 hθ hθ1 hω hσ
    hΦ he hw0 hw1 hu hv hucc hvy hvyy hyh hxu hxv hgO hqO hiO hpO hDO hg hq hV hD w0)
  have h2 := loss614_first_order 𝔼 (κ := Moments.calvoKappa α β ω θ σ) (θ := θ) (Φ := Φ)
    (ω := ω) (σ := σ) hβ0.le hβ1 he hY1 hiO hgO hqO hYd w0
  have hκ : Moments.calvoKappa α β ω θ σ ≠ 0 := by
    unfold Moments.calvoKappa
    have : 0 < 1 - α * β := by nlinarith
    have : 0 < 1 - α := by linarith
    have : 0 < 1 + ω * θ := by nlinarith
    positivity
  have h1Φ : 1 - Φ ≠ 0 := by linarith
  have hωσ : ω + σ ≠ 0 := by linarith
  have key : LargeDistortions.OmegaW Ybar (dY u (Ybar, 0)) (Moments.calvoKappa α β ω θ σ) θ Φ ω σ *
      (2 * (Moments.calvoKappa α β ω θ σ / θ * Φ / ((1 - Φ) * (ω + σ)))) =
      Ybar * dY u (Ybar, 0) * Φ := by
    unfold LargeDistortions.OmegaW
    field_simp
  refine (h1.sub (h2.const_mul_left (LargeDistortions.OmegaW Ybar (dY u (Ybar, 0))
    (Moments.calvoKappa α β ω θ σ) θ Φ ω σ))).congr_left fun a => ?_
  linear_combination (-(e a * Sequences.dsum 𝔼 β Y1 w0)) * key

/-- Woodford (2003), §5, p. 456 (first-order welfare ranking): if two policies give
`W_X = T + εc_X + O(ε²)` with the same policy-independent `T` and `c_B < c_A`, then `A` is
strictly better for every small amplitude `ε > 0` (e.g. `c_X = Ȳu_cΦ_y∑βᵗE_0Ŷ₁ˣ` from
`prop614_first_order`). -/
theorem first_order_ranking (he : Tendsto e l (𝓝 0)) (hpos : ∀ᶠ a in l, 0 < e a)
    {WA WB T : A → ℝ} {cA cB : ℝ} (hA : (fun a => WA a - (T a + e a * cA)) =O[l] fun a => e a ^ 2)
    (hB : (fun a => WB a - (T a + e a * cB)) =O[l] fun a => e a ^ 2) (h : cB < cA) :
    ∀ᶠ a in l, WB a < WA a :=
  eventually_lt_of_linear_gap he hpos (c := cA - cB) (by linarith)
    ((hA.sub hB).congr_left fun a => by ring)

/-! ## Proposition 6.15 (Layer B): the remainder of (5.4) along a family -/

/-- Woodford (2003), (5.4) (Benigno–Woodford): the weight-two `h = x − (α/(1−α))π` is `O(s²)`
for first-order `π, x` and third-order exponential atoms (any functions of that order). -/
theorem hA_o (hs : Tendsto s L (𝓝 0)) (α θ : ℝ) {p x A1 A2 : B → ℝ}
    (hp : p =O[L] fun b => s b ^ 1) (hx : x =O[L] fun b => s b ^ 1)
    (hA1 : A1 =O[L] fun b => s b ^ 3) (hA2 : A2 =O[L] fun b => s b ^ 3) :
    (fun b => LargeDistortions.hA α θ (p b) (x b) (A1 b) (A2 b)) =O[L] fun b => s b ^ 2 := by
  refine ((((o_pow hp 2).const_mul_left ((θ - 1) * (α / (1 - α)) / 2)).add
    ((o_pow hx 2).const_mul_left ((θ - 1) / 2))).add ((o_weaken hs (by norm_num : 2 ≤ 3)
      ((hA1.const_mul_left (α / (1 - α))).add hA2)).const_mul_left (θ - 1)⁻¹)).congr_left
        fun b => ?_
  unfold LargeDistortions.hA
  ring

/-- Woodford (2003), (5.4): `h₃ = O(s³)`. -/
theorem h3A_o (hs : Tendsto s L (𝓝 0)) (α θ : ℝ) {p x A1 A2 : B → ℝ}
    (hp : p =O[L] fun b => s b ^ 1) (hx : x =O[L] fun b => s b ^ 1)
    (hA1 : A1 =O[L] fun b => s b ^ 3) (hA2 : A2 =O[L] fun b => s b ^ 3) :
    (fun b => LargeDistortions.h3A α θ (p b) (x b) (A1 b) (A2 b)) =O[L] fun b => s b ^ 3 := by
  have hx' := hx.add (hp.const_mul_left (α / (1 - α)))
  refine (((o_mul (hA_o hs α θ hp hx hA1 hA2) hx' (by norm_num : 2 + 1 = 3)).const_mul_left
    ((θ - 1) / 2)).add (((hA1.const_mul_left (α / (1 - α))).add hA2).const_mul_left
      (θ - 1)⁻¹)).congr_left fun b => ?_
  unfold LargeDistortions.h3A
  ring

/-- Woodford (2003), (5.4): the date-`t` part `nowA` of the AS remainder is `O(s³)` for
first-order `π, x, S` and third-order atoms. -/
theorem nowA_o (hs : Tendsto s L (𝓝 0)) (α β θ ω : ℝ) {p x S A1 A2 rK rF rk rf : B → ℝ}
    (hp : p =O[L] fun b => s b ^ 1) (hx : x =O[L] fun b => s b ^ 1)
    (hS : S =O[L] fun b => s b ^ 1) (hA1 : A1 =O[L] fun b => s b ^ 3)
    (hA2 : A2 =O[L] fun b => s b ^ 3) (hrK : rK =O[L] fun b => s b ^ 3)
    (hrF : rF =O[L] fun b => s b ^ 3) (hrk : rk =O[L] fun b => s b ^ 3)
    (hrf : rf =O[L] fun b => s b ^ 3) :
    (fun b => LargeDistortions.nowA α β θ ω (p b) (x b) (S b) (A1 b) (A2 b) (rK b) (rF b)
      (rk b) (rf b)) =O[L] fun b => s b ^ 3 := by
  have hAS := o_mul (hA_o hs α θ hp hx hA1 hA2) hS (by norm_num : 2 + 1 = 3)
  refine ((((h3A_o hs α θ hp hx hA1 hA2).add hAS).const_mul_left (-(α / (1 - α))⁻¹)).sub
    ((hrK.sub hrF).const_mul_left (α / (1 - α) * (1 + ω * θ))⁻¹) |>.add
      ((hrk.sub hrf).const_mul_left (Moments.calvoXi α β ω θ))).congr_left fun b => ?_
  unfold LargeDistortions.nowA
  ring

/-- Woodford (2003), (5.4): the date-`(t+1)` part `restA` of the AS remainder is `O(s³)`. -/
theorem restA_o (hs : Tendsto s L (𝓝 0)) (α θ ω : ℝ) {p x S A1 A2 rKn rFn : B → ℝ}
    (hp : p =O[L] fun b => s b ^ 1) (hx : x =O[L] fun b => s b ^ 1)
    (hS : S =O[L] fun b => s b ^ 1) (hA1 : A1 =O[L] fun b => s b ^ 3)
    (hA2 : A2 =O[L] fun b => s b ^ 3) (hrK : rKn =O[L] fun b => s b ^ 3)
    (hrF : rFn =O[L] fun b => s b ^ 3) :
    (fun b => LargeDistortions.restA α θ ω (p b) (x b) (S b) (A1 b) (A2 b) (rKn b) (rFn b))
      =O[L] fun b => s b ^ 3 := by
  have hpS := (hp.const_mul_left ((θ - 1 + θ * (1 + ω)) / 2)).add hS
  have hAS := o_mul (hA_o hs α θ hp hx hA1 hA2) hpS (by norm_num : 2 + 1 = 3)
  refine ((((h3A_o hs α θ hp hx hA1 hA2).add hAS).const_mul_left (1 - α)).add
    ((hrK.sub hrF).const_mul_left ((1 - α) / (1 + ω * θ)))).congr_left fun b => ?_
  unfold LargeDistortions.restA
  ring

/-- Woodford (2003), (5.4) under Assumption 6.2: the weight-three part `f₃` of `f̂` is
`O(s³)`. -/
theorem f3A_o (hs : Tendsto s L (𝓝 0)) (σ sC : ℝ) {Y G rY rl : B → ℝ}
    (hY : Y =O[L] fun b => s b ^ 1) (hG : G =O[L] fun b => s b ^ 1)
    (hrY : rY =O[L] fun b => s b ^ 3) (hrl : rl =O[L] fun b => s b ^ 3) :
    (fun b => LargeDistortions.f3A σ sC (Y b) (G b) (rY b) (rl b)) =O[L] fun b => s b ^ 3 := by
  have hA : (fun b => Y b ^ 2 / 2 + rY b) =O[L] fun b => s b ^ 2 :=
    (((o_pow hY 2).const_mul_left (1 / 2)).add (o_weaken hs (by norm_num) hrY)).congr_left
      fun b => by ring
  have hB : (fun b => 2 * (Y b - G b) + (Y b ^ 2 / 2 + rY b)) =O[L] fun b => s b ^ 1 :=
    ((hY.sub hG).const_mul_left 2).add (o_weaken hs (by norm_num) hA)
  refine (((hrY.const_mul_left (-σ)).add ((o_mul hA hB (by norm_num : 2 + 1 = 3)).const_mul_left
    (σ / (2 * sC)))).sub (hrl.const_mul_left (sC * σ))).congr_left fun b => ?_
  unfold LargeDistortions.f3A
  ring

/-- Woodford (2003), (5.4) under Assumption 6.2: the weight-three remainder `ρ₂` of the AS
expansion (`LargeDistortions.as_expand`) is `O(s³)` for first-order `Ŷ, Ĝ, ĉ, τ̂` and
third-order atoms. -/
theorem rho2A_o (hs : Tendsto s L (𝓝 0)) (α β θ ω σ sC : ℝ) {Y G cb tau rY rl : B → ℝ}
    (hY : Y =O[L] fun b => s b ^ 1) (hG : G =O[L] fun b => s b ^ 1)
    (hcb : cb =O[L] fun b => s b ^ 1) (htau : tau =O[L] fun b => s b ^ 1)
    (hrY : rY =O[L] fun b => s b ^ 3) (hrl : rl =O[L] fun b => s b ^ 3) :
    (fun b => LargeDistortions.rho2A α β θ ω σ sC (Y b) (G b) (cb b) (tau b) (rY b) (rl b))
      =O[L] fun b => s b ^ 3 := by
  have hf := f3A_o hs σ sC hY hG hrY hrl
  have hQ : (fun b => -(σ / 2) * Y b ^ 2 + σ / (2 * sC) * (Y b - G b) ^ 2 +
      LargeDistortions.f3A σ sC (Y b) (G b) (rY b) (rl b)) =O[L] fun b => s b ^ 2 :=
    (((o_pow hY 2).const_mul_left (-(σ / 2))).add
      ((o_pow (hY.sub hG) 2).const_mul_left (σ / (2 * sC)))).add
      (o_weaken hs (by norm_num) hf)
  have hP : (fun b => 2 * ((1 - σ) * Y b + σ * (G b + sC * cb b) + tau b) +
      (-(σ / 2) * Y b ^ 2 + σ / (2 * sC) * (Y b - G b) ^ 2 +
        LargeDistortions.f3A σ sC (Y b) (G b) (rY b) (rl b))) =O[L] fun b => s b ^ 1 :=
    ((((hY.const_mul_left (1 - σ)).add ((hG.add (hcb.const_mul_left sC)).const_mul_left σ)).add
      htau).const_mul_left 2).add (o_weaken hs (by norm_num) hQ)
  refine ((hf.add ((o_mul hQ hP (by norm_num : 2 + 1 = 3)).const_mul_left (1 / 2))).const_mul_left
    (-Moments.calvoXi α β ω θ)).congr_left fun b => ?_
  unfold LargeDistortions.rho2A
  ring

/-- Woodford (2003), (5.4) under Assumption 6.2: the argument `z/s_C` of the log atom is
first order. -/
theorem zA_o (hs : Tendsto s L (𝓝 0)) (sC : ℝ) {Y G : B → ℝ}
    (hY : Y =O[L] fun b => s b ^ 1) (hG : G =O[L] fun b => s b ^ 1) :
    (fun b => LargeDistortions.zA sC (Y b) (G b)) =O[L] fun b => s b ^ 1 := by
  refine ((((hY.add ((o_weaken hs (by norm_num : 1 ≤ 2) (o_pow hY 2)).const_mul_left (1 / 2))).add
    (o_weaken hs (by norm_num : 1 ≤ 3) (expRem_o hs hY))).sub hG).const_mul_left
      sC⁻¹).congr_left fun b => ?_
  unfold LargeDistortions.zA
  ring

/-- Woodford (2003), eq. (5.4), p. 458: the remainder process `remAS` of the derived (5.4) is
`O(ε³)` UNIFORMLY in the date and the state, for any family in which `π, x, F̂, K̂, f̂, k̂, Ŷ, Ĝ,
ĉ, τ̂` are uniformly `O(ε)` (its conditional-expectation part by `condE_o`). -/
theorem remAS_o (he : Tendsto e l (𝓝 0)) (α β θ ω σ sC : ℝ)
    {infl xr F K f k Y G cb tau : A → ℕ → Ω → ℝ} (hi : UProc l infl fun a => e a ^ 1)
    (hx : UProc l xr fun a => e a ^ 1) (hF : UProc l F fun a => e a ^ 1)
    (hK : UProc l K fun a => e a ^ 1) (hf : UProc l f fun a => e a ^ 1)
    (hk : UProc l k fun a => e a ^ 1) (hY : UProc l Y fun a => e a ^ 1)
    (hG : UProc l G fun a => e a ^ 1) (hcb : UProc l cb fun a => e a ^ 1)
    (htau : UProc l tau fun a => e a ^ 1) :
    UProc l (fun a => LargeDistortions.remAS 𝔼 α β θ ω σ sC (infl a) (xr a) (F a) (K a) (f a)
      (k a) (Y a) (G a) (cb a) (tau a)) fun a => e a ^ 3 := by
  have hs := tendsto_amp (J := ℕ × Ω) he
  have hS : UProc l (fun a t z => (K a t z + F a t z) / 2) fun a => e a ^ 1 :=
    ((show (fun p : A × (ℕ × Ω) => K p.1 p.2.1 p.2.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 from hK).add
      hF).const_mul_left (1 / 2) |>.congr_left fun p => by ring
  have ex : ∀ X : A → ℕ → Ω → ℝ, UProc l X (fun a => e a ^ 1) →
      UProc l (fun a t z => expRem (X a t z)) fun a => e a ^ 3 := fun X hX =>
    expRem_o (L := l ×ˢ ⊤) (s := fun p : A × (ℕ × Ω) => e p.1) hs hX
  have lin : ∀ (c : ℝ) (X Z : A → ℕ → Ω → ℝ), UProc l X (fun a => e a ^ 1) →
      UProc l Z (fun a => e a ^ 1) → UProc l (fun a t z => c * X a t z + Z a t z)
        fun a => e a ^ 1 := fun c X Z hX hZ =>
    ((show (fun p : A × (ℕ × Ω) => X p.1 p.2.1 p.2.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1
      from hX).const_mul_left c).add hZ
  have hneg : UProc l (fun a t z => -((θ - 1) * xr a t z)) fun a => e a ^ 1 :=
    ((show (fun p : A × (ℕ × Ω) => xr p.1 p.2.1 p.2.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1
      from hx).const_mul_left (θ - 1)).neg_left
  have hpth : UProc l (fun a t z => (θ - 1) * infl a t z) fun a => e a ^ 1 :=
    (show (fun p : A × (ℕ × Ω) => infl p.1 p.2.1 p.2.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1
      from hi).const_mul_left (θ - 1)
  have hnow := nowA_o (L := l ×ˢ ⊤) (s := fun p : A × (ℕ × Ω) => e p.1) hs α β θ ω hi hx hS
    (ex _ hpth) (ex _ hneg) (ex _ hK) (ex _ hF) (ex _ hk) (ex _ hf)
  have hrest : UProc l (fun a => LargeDistortions.restP α θ ω (infl a) (xr a) (F a) (K a))
      fun a => e a ^ 3 :=
    restA_o (L := l ×ˢ ⊤) (s := fun p : A × (ℕ × Ω) => e p.1) hs α θ ω hi hx hS (ex _ hpth)
      (ex _ hneg) (ex _ (lin (θ * (1 + ω)) infl K hi hK)) (ex _ (lin (θ - 1) infl F hi hF))
  have hE := condE_o 𝔼 hrest
  have hrho := rho2A_o (L := l ×ˢ ⊤) (s := fun p : A × (ℕ × Ω) => e p.1) hs α β θ ω σ sC hY hG
    hcb htau (ex _ hY) (rlog_o hs (zA_o (L := l ×ˢ ⊤) (s := fun p : A × (ℕ × Ω) => e p.1) hs sC
      (Y := fun p => Y p.1 p.2.1 p.2.2) (G := fun p => G p.1 p.2.1 p.2.2) hY hG))
  refine ((hnow.add ((show (fun p : A × (ℕ × Ω) => 𝔼.E p.2.1
      (LargeDistortions.restP α θ ω (infl p.1) (xr p.1) (F p.1) (K p.1) (p.2.1 + 1)) p.2.2)
      =O[l ×ˢ ⊤] fun p => e p.1 ^ 3 from hE).const_mul_left β)).add hrho).congr_left
        fun p => ?_
  simp only [LargeDistortions.remAS, LargeDistortions.rhoP]

/-- Woodford (2003), (5.5), p. 458: the transitory term
`W_0 = 2Ω(γ̄/κ)E_0[π_0 + Q_0]`, `π_0 + Q_0 = V_0 + (μ_π/2)π_0²` (the date-0 left side of (5.4)). -/
noncomputable def W0615 (α β θ ω σ Φ Ybar uc : ℝ) (infl F K : ℕ → Ω → ℝ) (w0 : Ω) : ℝ :=
  2 * LargeDistortions.OmegaW Ybar uc (Moments.calvoKappa α β ω θ σ) θ Φ ω σ *
    LargeDistortions.gbarC θ ω σ Φ *
      𝔼.E 0 (fun w => LargeDistortions.Vp α θ infl F K 0 w + θ * (1 + ω) / 2 * infl 0 w ^ 2) w0

/-- Woodford (2003), (5.5), p. 458: the terms independent of policy of Proposition 6.15 (functions
of the disturbances and of the initial dispersion `Δ_{−1}` only). -/
noncomputable def tip615 (α β θ ω σ sC Φ Ybar uc : ℝ) (tipU D G cb q muw tau : ℕ → Ω → ℝ)
    (w0 : Ω) : ℝ :=
  Sequences.dsum 𝔼 β tipU w0 -
    LargeDistortions.OmegaW Ybar uc (Moments.calvoKappa α β ω θ σ) θ Φ ω σ * (1 - α) *
      𝔼.E 0 (D 0) w0 +
    LargeDistortions.OmegaTilde Ybar uc α β θ ω σ Φ * LargeDistortions.lamTilde α β θ ω σ sC Φ *
      Sequences.dsum 𝔼 β (fun t w =>
        LargeDistortions.YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) ^ 2)
        w0 +
    2 * LargeDistortions.OmegaW Ybar uc (Moments.calvoKappa α β ω θ σ) θ Φ ω σ *
      LargeDistortions.gbarC θ ω σ Φ * Moments.calvoKappa α β ω θ σ *
      Sequences.dsum 𝔼 β (fun t w =>
        LargeDistortions.YnA ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w)) w0 -
    2 * LargeDistortions.OmegaW Ybar uc (Moments.calvoKappa α β ω θ σ) θ Φ ω σ *
      LargeDistortions.gbarC θ ω σ Φ *
      Sequences.dsum 𝔼 β (fun t w =>
        LargeDistortions.tipASA α β θ ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w)) w0

/-- Woodford (2003), **Proposition 6.15**, (5.5)–(5.8), pp. 458–459, LAYER B (from the ACTUAL
utility, `Φ_y ∈ [0, 1)` fixed, the family in the disturbances only, the exact Calvo model under
Assumption 6.2 holding for every amplitude): with every first-order variable `O(ε)`,
`π̄ − π = O(ε²)` and `D = O(ε²)` UNIFORMLY in the date and state,
`∑βᵗE_0U_t = W_0 − Ω̃ ∑βᵗE_0 L̃_t + t.i.p. + O(ε³)`, `L̃_t = π_t² + λ̃(Ŷ_t − Ŷ*_t)²` PURELY
quadratic (the linear term of (5.3) is gone, eliminated with (5.4); its remainder `remAS` is
`O(ε³)` by `remAS_o`). -/
theorem prop615_layerB {α β θ ω σ sC Φ Ybar : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ : 1 < θ) (hω : 0 < ω) (hσ : 0 < σ) (hsC : 0 < sC) (hΦ0 : 0 ≤ Φ)
    (hΦ : Φ < 1) (hMd : LargeDistortions.Mden ω σ sC Φ ≠ 0)
    (he : Tendsto e l (𝓝 0)) {wt : ι → ℝ} (hw0 : ∀ i, 0 ≤ wt i) (hw1 : ∑ i, wt i = 1)
    {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    (hucc : dYY u (Ybar, 0) = -(σ * dY u (Ybar, 0) / Ybar))
    (hvy : dY v (Ybar, 0) = (1 - Φ) * dY u (Ybar, 0))
    (hvyy : dYY v (Ybar, 0) = ω * dY v (Ybar, 0) / Ybar)
    {yh : A → ℕ → Ω → ι → ℝ} {xu xv : A → ℕ → Ω → Ξ}
    {infl xr F K f k G cb q muw tau D pib : A → ℕ → Ω → ℝ}
    (hM : ∀ a, LargeDistortions.CalvoModel.CalvoAS 𝔼 α β θ ω σ sC (infl a) (xr a) (F a) (K a)
      (f a) (k a) (fun t z => logYidx wt θ (yh a t z)) (G a) (cb a) (q a) (muw a) (tau a))
    (hyh : UProc l yh fun a => e a ^ 1) (hxu : UProc l xu fun a => e a ^ 1)
    (hxv : UProc l xv fun a => e a ^ 1) (hiO : UProc l infl fun a => e a ^ 1)
    (hxrO : UProc l xr fun a => e a ^ 1) (hFO : UProc l F fun a => e a ^ 1)
    (hKO : UProc l K fun a => e a ^ 1) (hfO : UProc l f fun a => e a ^ 1)
    (hkO : UProc l k fun a => e a ^ 1) (hGO : UProc l G fun a => e a ^ 1)
    (hcbO : UProc l cb fun a => e a ^ 1) (hqO : UProc l q fun a => e a ^ 1)
    (hmO : UProc l muw fun a => e a ^ 1) (htO : UProc l tau fun a => e a ^ 1)
    (hpO : UProc l (fun a t z => pib a t z - infl a t z) fun a => e a ^ 2)
    (hDO : UProc l D fun a => e a ^ 2)
    (hg : ∀ a t z, dYXi u (Ybar, 0) (xu a t z) =
      σ * dY u (Ybar, 0) * (G a t z + sC * cb a t z))
    (hq : ∀ a t z, dYXi v (Ybar, 0) (xv a t z) = -(ω * dY v (Ybar, 0) * q a t z))
    (hV : ∀ a t, (fun z => crossVar wt (yh a t z)) = θ ^ 2 • D a (t + 1))
    (hD : ∀ a t, D a (t + 1) = α • D a t + (α / (1 - α)) • pib a t ^ 2) (w0 : Ω) :
    (fun a => Sequences.dsum 𝔼 β
        (fun t z => periodU u v wt θ Ybar (yh a t z) (xu a t z) (xv a t z)) w0 -
      (W0615 𝔼 α β θ ω σ Φ Ybar (dY u (Ybar, 0)) (infl a) (F a) (K a) w0 -
        LargeDistortions.OmegaTilde Ybar (dY u (Ybar, 0)) α β θ ω σ Φ *
          Sequences.dsum 𝔼 β (LargeDistortions.loss615 α β θ ω σ sC Φ (infl a)
            (fun t z => logYidx wt θ (yh a t z)) (G a) (cb a) (q a) (muw a) (tau a)) w0 +
        tip615 𝔼 α β θ ω σ sC Φ Ybar (dY u (Ybar, 0))
          (fun t z => tip51 u v Ybar (xu a t z) (xv a t z)) (D a) (G a) (cb a) (q a) (muw a)
          (tau a) w0))
      =O[l] fun a => e a ^ 3 := by
  have hs := tendsto_amp (J := ℕ × Ω) he
  have hβ : |β| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hθ0 : 0 < θ := by linarith
  set Om := LargeDistortions.OmegaW Ybar (dY u (Ybar, 0)) (Moments.calvoKappa α β ω θ σ) θ Φ ω σ
    with hOm
  set gb := LargeDistortions.gbarC θ ω σ Φ with hgb
  set R : A → ℕ → Ω → ℝ := fun a t z =>
    periodU u v wt θ Ybar (yh a t z) (xu a t z) (xv a t z) -
      (-(Ybar * dY u (Ybar, 0) / 2) * LargeDistortions.quad51 σ ω θ Φ
        (G a t z + sC * cb a t z) (q a t z)
        (logYidx wt θ (yh a t z)) (crossVar wt (yh a t z)) +
          tip51 u v Ybar (xu a t z) (xv a t z)) with hR
  have hG' : (fun p : A × (ℕ × Ω) => G p.1 p.2.1 p.2.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 := hGO
  have hcb' : (fun p : A × (ℕ × Ω) => cb p.1 p.2.1 p.2.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 :=
    hcbO
  have hgO : UProc l (fun a t z => G a t z + sC * cb a t z) fun a => e a ^ 1 :=
    hG'.add (hcb'.const_mul_left sC)
  have hRO : UProc l R fun a => e a ^ 3 :=
    eq51_actual (L := l ×ˢ ⊤) (s := fun p : A × (ℕ × Ω) => e p.1) hs hw0 hw1 hθ.ne' hu hv hucc
      hvy hvyy (yh := fun p => yh p.1 p.2.1 p.2.2) (xu := fun p => xu p.1 p.2.1 p.2.2)
      (xv := fun p => xv p.1 p.2.1 p.2.2)
      (g := fun p => G p.1 p.2.1 p.2.2 + sC * cb p.1 p.2.1 p.2.2)
      (q := fun p => q p.1 p.2.1 p.2.2) hyh hxu hxv hgO hqO (fun p => hg _ _ _)
      (fun p => hq _ _ _)
  have hpO' : (fun p : A × (ℕ × Ω) => pib p.1 p.2.1 p.2.2 - infl p.1 p.2.1 p.2.2)
      =O[l ×ˢ ⊤] fun p => e p.1 ^ 2 := hpO
  have hiO' : (fun p : A × (ℕ × Ω) => infl p.1 p.2.1 p.2.2)
      =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 := hiO
  have hPO : UProc l (fun a t => pib a t ^ 2 - infl a t ^ 2) fun a => e a ^ 3 := by
    have h1 := (o_weaken hs (by norm_num : 1 ≤ 2) hpO').add (hiO'.const_mul_left 2)
    refine (o_mul hpO' h1 (by norm_num : 2 + 1 = 3)).congr_left fun p => ?_
    simp only [Pi.sub_apply, Pi.pow_apply]
    ring
  have hYO := logYidx_o (L := l ×ˢ ⊤) (s := fun p : A × (ℕ × Ω) => e p.1) hs hw0 hw1 hθ.ne'
    (yh := fun p => yh p.1 p.2.1 p.2.2) hyh
  have hAS := remAS_o 𝔼 he α β θ ω σ sC (Y := fun a t z => logYidx wt θ (yh a t z)) hiO hxrO
    hFO hKO hfO hkO hYO hGO hcbO htO
  -- boundedness for amplitudes near `0`
  have bY := bdd_of_o0 (X := fun a t z => logYidx wt θ (yh a t z)) he hYO
  have bi := bdd_of_o0 he hiO
  have bF := bdd_of_o0 he hFO
  have bK := bdd_of_o0 he hKO
  have bG := bdd_of_o0 he hGO
  have bcb := bdd_of_o0 he hcbO
  have bq := bdd_of_o0 he hqO
  have bm := bdd_of_o0 he hmO
  have bt := bdd_of_o0 he htO
  have bD := bdd_of_o0 he hDO
  have bp := bdd_of_o0 (X := pib) he
    (((o_weaken hs (by norm_num : 1 ≤ 2) hpO').add hiO').congr_left fun p => by ring)
  have bT := bdd_of_o (X := fun a t z => tip51 u v Ybar (xu a t z) (xv a t z)) he
    (tip51 u v Ybar 0 0) (tip51_o (L := l ×ˢ ⊤) (s := fun p : A × (ℕ × Ω) => e p.1) hs u v Ybar
      (xu := fun p => xu p.1 p.2.1 p.2.2) (xv := fun p => xv p.1 p.2.1 p.2.2) hxu hxv)
  have bR := bdd_of_o0 he hRO
  have hev : ∀ᶠ a in l, Sequences.dsum 𝔼 β
        (fun t z => periodU u v wt θ Ybar (yh a t z) (xu a t z) (xv a t z)) w0 -
      (W0615 𝔼 α β θ ω σ Φ Ybar (dY u (Ybar, 0)) (infl a) (F a) (K a) w0 -
        LargeDistortions.OmegaTilde Ybar (dY u (Ybar, 0)) α β θ ω σ Φ *
          Sequences.dsum 𝔼 β (LargeDistortions.loss615 α β θ ω σ sC Φ (infl a)
            (fun t z => logYidx wt θ (yh a t z)) (G a) (cb a) (q a) (muw a) (tau a)) w0 +
        tip615 𝔼 α β θ ω σ sC Φ Ybar (dY u (Ybar, 0))
          (fun t z => tip51 u v Ybar (xu a t z) (xv a t z)) (D a) (G a) (cb a) (q a) (muw a)
          (tau a) w0) =
      Sequences.dsum 𝔼 β (R a) w0 -
        Om * Sequences.dsum 𝔼 β (fun t => pib a t ^ 2 - infl a t ^ 2) w0 -
        2 * Om * gb * Sequences.dsum 𝔼 β (LargeDistortions.remAS 𝔼 α β θ ω σ sC (infl a) (xr a)
          (F a) (K a) (f a) (k a) (fun t z => logYidx wt θ (yh a t z)) (G a) (cb a) (tau a))
          w0 := by
    filter_upwards [bY, bi, bF, bK, bG, bcb, bq, bm, bt, bD, bp, bT, bR] with a hYb hib hFb hKb
      hGb hcbb hqb hmb htb hDb hpb hTb hRb
    have h51 : ∀ t, (fun z => periodU u v wt θ Ybar (yh a t z) (xu a t z) (xv a t z)) =
        (fun z => -(Ybar * dY u (Ybar, 0) / 2) * LargeDistortions.quad51 σ ω θ Φ
          (G a t z + sC * cb a t z) (q a t z) (logYidx wt θ (yh a t z))
          (crossVar wt (yh a t z))) + (fun z => tip51 u v Ybar (xu a t z) (xv a t z)) + R a t := by
      intro t
      funext z
      simp only [Pi.add_apply, hR]
      ring
    have h := LargeDistortions.prop615 𝔼 hα0 hα1 hβ0 hβ1 hθ hω hσ hsC hΦ0 hΦ hMd (hM a) hib hFb
      hKb hYb hGb hcbb hqb hmb htb hDb hpb hTb hRb h51 (hV a) (hD a) w0
    rw [h, ← dsum_sub 𝔼 hβ (Sequences.bdd_sq hpb) (Sequences.bdd_sq hib)]
    unfold W0615 tip615
    ring
  exact (((dsum_o 𝔼 hβ0.le hβ1 hRO w0).sub ((dsum_o 𝔼 hβ0.le hβ1 hPO w0).const_mul_left Om)).sub
    ((dsum_o 𝔼 hβ0.le hβ1 hAS w0).const_mul_left (2 * Om * gb))).congr'
      (hev.mono fun a ha => ha.symm) (Eventually.of_forall fun _ => rfl)

/-- Woodford (2003), App. E (first-order solutions): `X = εX₁ + O(ε²)` uniformly with `X₁`
bounded gives `X = O(ε)` uniformly. -/
theorem first_order_o (he : Tendsto e l (𝓝 0)) {X : A → ℕ → Ω → ℝ} {X1 : ℕ → Ω → ℝ}
    (hX1 : BoundedProc X1) (hd : UProc l (fun a t z => X a t z - e a * X1 t z) fun a => e a ^ 2) :
    UProc l X fun a => e a ^ 1 := by
  have hs := tendsto_amp (J := ℕ × Ω) he
  have h1 : (fun p : A × (ℕ × Ω) => e p.1 * X1 p.2.1 p.2.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 :=
    ((isBigO_refl _ _).mul (uproc_of_bdd (l := l) hX1)).congr_right fun p => by ring
  exact ((o_weaken hs (by norm_num : 1 ≤ 2) (show (fun p : A × (ℕ × Ω) =>
    X p.1 p.2.1 p.2.2 - e p.1 * X1 p.2.1 p.2.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2 from hd)).add
      h1).congr_left fun p => by ring

/-- Woodford (2003), (5.8), p. 458: the target `Ŷ*` is linear in the disturbances,
`Ŷ*(x − cx₁) = Ŷ*(x) − cŶ*(x₁)`. -/
theorem YstarA_sub_mul (α β θ ω σ sC Φ c G cb q muw tau G1 cb1 q1 muw1 tau1 : ℝ) :
    LargeDistortions.YstarA α β θ ω σ sC Φ (G - c * G1) (cb - c * cb1) (q - c * q1)
        (muw - c * muw1) (tau - c * tau1) =
      LargeDistortions.YstarA α β θ ω σ sC Φ G cb q muw tau -
        c * LargeDistortions.YstarA α β θ ω σ sC Φ G1 cb1 q1 muw1 tau1 := by
  unfold LargeDistortions.YstarA LargeDistortions.YnA
  ring

/-- Woodford (2003), (5.8): the target `Ŷ*` of disturbances of order `sᵏ` is of order `sᵏ`. -/
theorem YstarA_o (α β θ ω σ sC Φ : ℝ) {n : ℕ} {G cb q muw tau : B → ℝ}
    (hG : G =O[L] fun b => s b ^ n) (hcb : cb =O[L] fun b => s b ^ n)
    (hq : q =O[L] fun b => s b ^ n) (hm : muw =O[L] fun b => s b ^ n)
    (ht : tau =O[L] fun b => s b ^ n) :
    (fun b => LargeDistortions.YstarA α β θ ω σ sC Φ (G b) (cb b) (q b) (muw b) (tau b))
      =O[L] fun b => s b ^ n := by
  have hYn := ((((hq.const_mul_left ω).add ((hG.add (hcb.const_mul_left sC)).const_mul_left σ)).sub
    hm).add ht).const_mul_left (ω + σ)⁻¹
  refine ((((hYn.const_mul_left (LargeDistortions.omega1 α β θ ω σ sC Φ)).sub
    (hG.const_mul_left (LargeDistortions.omega2 ω σ sC Φ))).add
    (hm.const_mul_left (LargeDistortions.omega3 ω σ sC Φ))).sub
    (ht.const_mul_left (LargeDistortions.Mden ω σ sC Φ)⁻¹)).congr_left fun b => ?_
  unfold LargeDistortions.YstarA LargeDistortions.YnA
  ring

/-- Woodford (2003), (5.6)–(5.8): along a family whose first-order solution is
`(π₁, Ŷ₁, Ĝ₁, ĉ₁, q₁, μ̂ʷ₁, τ̂₁)` (each variable `= ε × first order + O(ε²)` uniformly), the
PURELY QUADRATIC loss `L̃` of Proposition 6.15 satisfies
`∑βᵗE_0L̃_t = ε² ∑βᵗE_0L̃(first-order solution)_t + O(ε³)`. -/
theorem loss615_first_order {α β θ ω σ sC Φ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (he : Tendsto e l (𝓝 0)) {infl Y G cb q muw tau : A → ℕ → Ω → ℝ}
    {infl1 Y1 G1 cb1 q1 muw1 tau1 : ℕ → Ω → ℝ} (hi1 : BoundedProc infl1)
    (hY1 : BoundedProc Y1) (hG1 : BoundedProc G1) (hcb1 : BoundedProc cb1)
    (hq1 : BoundedProc q1) (hm1 : BoundedProc muw1) (ht1 : BoundedProc tau1)
    (hid : UProc l (fun a t z => infl a t z - e a * infl1 t z) fun a => e a ^ 2)
    (hYd : UProc l (fun a t z => Y a t z - e a * Y1 t z) fun a => e a ^ 2)
    (hGd : UProc l (fun a t z => G a t z - e a * G1 t z) fun a => e a ^ 2)
    (hcbd : UProc l (fun a t z => cb a t z - e a * cb1 t z) fun a => e a ^ 2)
    (hqd : UProc l (fun a t z => q a t z - e a * q1 t z) fun a => e a ^ 2)
    (hmd : UProc l (fun a t z => muw a t z - e a * muw1 t z) fun a => e a ^ 2)
    (htd : UProc l (fun a t z => tau a t z - e a * tau1 t z) fun a => e a ^ 2) (w0 : Ω) :
    (fun a => Sequences.dsum 𝔼 β (LargeDistortions.loss615 α β θ ω σ sC Φ (infl a) (Y a) (G a)
        (cb a) (q a) (muw a) (tau a)) w0 - e a ^ 2 * Sequences.dsum 𝔼 β
        (LargeDistortions.loss615 α β θ ω σ sC Φ infl1 Y1 G1 cb1 q1 muw1 tau1) w0)
      =O[l] fun a => e a ^ 3 := by
  have hs := tendsto_amp (J := ℕ × Ω) he
  have hβ : |β| < 1 := by rw [abs_lt]; constructor <;> linarith
  set Ys := fun (G cb q muw tau : ℝ) => LargeDistortions.YstarA α β θ ω σ sC Φ G cb q muw tau
    with hYs
  -- the gap and its first-order solution
  have hgap1 : BoundedProc (fun t z => Y1 t z - Ys (G1 t z) (cb1 t z) (q1 t z) (muw1 t z)
      (tau1 t z)) := by
    have bI : ∀ i, BoundedProc (![Y1, G1, cb1, q1, muw1, tau1] i) := by
      intro i; fin_cases i <;> assumption
    exact Sequences.bdd_congr (Sequences.bdd_of_continuous
      (fun v => v 0 - Ys (v 1) (v 2) (v 3) (v 4) (v 5))
      (by simp only [hYs]; unfold LargeDistortions.YstarA LargeDistortions.YnA; fun_prop) _ bI)
      (fun t z => by simp)
  have hgd : (fun p : A × (ℕ × Ω) => (Y p.1 p.2.1 p.2.2 - Ys (G p.1 p.2.1 p.2.2)
      (cb p.1 p.2.1 p.2.2) (q p.1 p.2.1 p.2.2) (muw p.1 p.2.1 p.2.2) (tau p.1 p.2.1 p.2.2)) -
      e p.1 * (Y1 p.2.1 p.2.2 - Ys (G1 p.2.1 p.2.2) (cb1 p.2.1 p.2.2) (q1 p.2.1 p.2.2)
        (muw1 p.2.1 p.2.2) (tau1 p.2.1 p.2.2))) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2 := by
    refine ((show (fun p : A × (ℕ × Ω) => Y p.1 p.2.1 p.2.2 - e p.1 * Y1 p.2.1 p.2.2)
      =O[l ×ˢ ⊤] fun p => e p.1 ^ 2 from hYd).sub
      (YstarA_o α β θ ω σ sC Φ hGd hcbd hqd hmd htd)).congr_left fun p => ?_
    simp only [hYs]
    rw [YstarA_sub_mul]
    ring
  have hsq1 := sq_sub_o hs hid (uproc_of_bdd (l := l) hi1)
  have hsq2 := sq_sub_o hs hgd (uproc_of_bdd (l := l) hgap1)
  have hD : UProc l (fun a t z => LargeDistortions.loss615 α β θ ω σ sC Φ (infl a) (Y a) (G a)
      (cb a) (q a) (muw a) (tau a) t z - e a ^ 2 * LargeDistortions.loss615 α β θ ω σ sC Φ
        infl1 Y1 G1 cb1 q1 muw1 tau1 t z) fun a => e a ^ 3 :=
    (hsq1.add (hsq2.const_mul_left (LargeDistortions.lamTilde α β θ ω σ sC Φ))).congr_left
      fun p => by simp only [LargeDistortions.loss615, hYs]; ring
  -- boundedness
  have bL1 : BoundedProc (LargeDistortions.loss615 α β θ ω σ sC Φ infl1 Y1 G1 cb1 q1 muw1
      tau1) := by
    have bI : ∀ i, BoundedProc (![infl1, Y1, G1, cb1, q1, muw1, tau1] i) := by
      intro i; fin_cases i <;> assumption
    exact Sequences.bdd_congr (Sequences.bdd_of_continuous
      (fun v => v 0 ^ 2 + LargeDistortions.lamTilde α β θ ω σ sC Φ *
        (v 1 - Ys (v 2) (v 3) (v 4) (v 5) (v 6)) ^ 2)
      (by simp only [hYs]; unfold LargeDistortions.YstarA LargeDistortions.YnA; fun_prop) _ bI)
      (fun t z => by simp [LargeDistortions.loss615, hYs])
  have bi := bdd_of_o0 he (first_order_o he hi1 hid)
  have bY := bdd_of_o0 he (first_order_o he hY1 hYd)
  have bG := bdd_of_o0 he (first_order_o he hG1 hGd)
  have bcb := bdd_of_o0 he (first_order_o he hcb1 hcbd)
  have bq := bdd_of_o0 he (first_order_o he hq1 hqd)
  have bm := bdd_of_o0 he (first_order_o he hm1 hmd)
  have bt := bdd_of_o0 he (first_order_o he ht1 htd)
  have hev : ∀ᶠ a in l, Sequences.dsum 𝔼 β (fun t z => LargeDistortions.loss615 α β θ ω σ sC Φ
        (infl a) (Y a) (G a) (cb a) (q a) (muw a) (tau a) t z - e a ^ 2 *
          LargeDistortions.loss615 α β θ ω σ sC Φ infl1 Y1 G1 cb1 q1 muw1 tau1 t z) w0 =
      Sequences.dsum 𝔼 β (LargeDistortions.loss615 α β θ ω σ sC Φ (infl a) (Y a) (G a)
        (cb a) (q a) (muw a) (tau a)) w0 - e a ^ 2 * Sequences.dsum 𝔼 β
        (LargeDistortions.loss615 α β θ ω σ sC Φ infl1 Y1 G1 cb1 q1 muw1 tau1) w0 := by
    filter_upwards [bi, bY, bG, bcb, bq, bm, bt] with a hib hYb hGb hcbb hqb hmb htb
    have hL : BoundedProc (LargeDistortions.loss615 α β θ ω σ sC Φ (infl a) (Y a) (G a) (cb a)
        (q a) (muw a) (tau a)) := by
      have bI : ∀ i, BoundedProc (![infl a, Y a, G a, cb a, q a, muw a, tau a] i) := by
        intro i; fin_cases i <;> assumption
      exact Sequences.bdd_congr (Sequences.bdd_of_continuous
        (fun v => v 0 ^ 2 + LargeDistortions.lamTilde α β θ ω σ sC Φ *
          (v 1 - Ys (v 2) (v 3) (v 4) (v 5) (v 6)) ^ 2)
        (by simp only [hYs]; unfold LargeDistortions.YstarA LargeDistortions.YnA; fun_prop) _ bI)
        (fun t z => by simp [LargeDistortions.loss615, hYs])
    have hS : BoundedProc (fun t => (e a ^ 2) • LargeDistortions.loss615 α β θ ω σ sC Φ infl1 Y1
        G1 cb1 q1 muw1 tau1 t) := by
      obtain ⟨M, hM⟩ := bL1
      exact ⟨|e a ^ 2| * M, fun t z => by
        simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hM t z) (abs_nonneg _)⟩
    rw [← dsum_smul 𝔼 hβ bL1, dsum_sub 𝔼 hβ hL hS]
    rfl
  exact (dsum_o 𝔼 hβ0 hβ1 hD w0).congr' hev (Eventually.of_forall fun _ => rfl)

/-- Woodford (2003), **Proposition 6.15**, (5.5)–(5.8), LAYER B with the FIRST-ORDER solution:
under the hypotheses of `prop615_layerB`, if `(π, Ŷ, Ĝ, ĉ, q, μ̂ʷ, τ̂)` have the first-order
solution `ε(π₁, Ŷ₁, Ĝ₁, ĉ₁, q₁, μ̂ʷ₁, τ̂₁) + O(ε²)` uniformly, then
`∑βᵗE_0U_t = W_0 − (ε²) Ω̃ ∑βᵗE_0 L̃(first-order solution)_t + t.i.p. + O(ε³)`: because (5.4)
removed the linear term, a first-order solution suffices to evaluate welfare to second order
(contrast `prop614_first_order`). -/
theorem prop615_first_order {α β θ ω σ sC Φ Ybar : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : 1 < θ) (hω : 0 < ω) (hσ : 0 < σ) (hsC : 0 < sC)
    (hΦ0 : 0 ≤ Φ) (hΦ : Φ < 1) (hMd : LargeDistortions.Mden ω σ sC Φ ≠ 0)
    (he : Tendsto e l (𝓝 0)) {wt : ι → ℝ} (hw0 : ∀ i, 0 ≤ wt i) (hw1 : ∑ i, wt i = 1)
    {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    (hucc : dYY u (Ybar, 0) = -(σ * dY u (Ybar, 0) / Ybar))
    (hvy : dY v (Ybar, 0) = (1 - Φ) * dY u (Ybar, 0))
    (hvyy : dYY v (Ybar, 0) = ω * dY v (Ybar, 0) / Ybar)
    {yh : A → ℕ → Ω → ι → ℝ} {xu xv : A → ℕ → Ω → Ξ}
    {infl xr F K f k G cb q muw tau D pib : A → ℕ → Ω → ℝ}
    {infl1 Y1 G1 cb1 q1 muw1 tau1 : ℕ → Ω → ℝ} (hi1 : BoundedProc infl1)
    (hY1 : BoundedProc Y1) (hG1 : BoundedProc G1) (hcb1 : BoundedProc cb1)
    (hq1 : BoundedProc q1) (hm1 : BoundedProc muw1) (ht1 : BoundedProc tau1)
    (hM : ∀ a, LargeDistortions.CalvoModel.CalvoAS 𝔼 α β θ ω σ sC (infl a) (xr a) (F a) (K a)
      (f a) (k a) (fun t z => logYidx wt θ (yh a t z)) (G a) (cb a) (q a) (muw a) (tau a))
    (hyh : UProc l yh fun a => e a ^ 1) (hxu : UProc l xu fun a => e a ^ 1)
    (hxv : UProc l xv fun a => e a ^ 1)
    (hxrO : UProc l xr fun a => e a ^ 1) (hFO : UProc l F fun a => e a ^ 1)
    (hKO : UProc l K fun a => e a ^ 1) (hfO : UProc l f fun a => e a ^ 1)
    (hkO : UProc l k fun a => e a ^ 1)
    (hid : UProc l (fun a t z => infl a t z - e a * infl1 t z) fun a => e a ^ 2)
    (hYd : UProc l (fun a t z => logYidx wt θ (yh a t z) - e a * Y1 t z) fun a => e a ^ 2)
    (hGd : UProc l (fun a t z => G a t z - e a * G1 t z) fun a => e a ^ 2)
    (hcbd : UProc l (fun a t z => cb a t z - e a * cb1 t z) fun a => e a ^ 2)
    (hqd : UProc l (fun a t z => q a t z - e a * q1 t z) fun a => e a ^ 2)
    (hmd : UProc l (fun a t z => muw a t z - e a * muw1 t z) fun a => e a ^ 2)
    (htd : UProc l (fun a t z => tau a t z - e a * tau1 t z) fun a => e a ^ 2)
    (hpO : UProc l (fun a t z => pib a t z - infl a t z) fun a => e a ^ 2)
    (hDO : UProc l D fun a => e a ^ 2)
    (hg : ∀ a t z, dYXi u (Ybar, 0) (xu a t z) =
      σ * dY u (Ybar, 0) * (G a t z + sC * cb a t z))
    (hq : ∀ a t z, dYXi v (Ybar, 0) (xv a t z) = -(ω * dY v (Ybar, 0) * q a t z))
    (hV : ∀ a t, (fun z => crossVar wt (yh a t z)) = θ ^ 2 • D a (t + 1))
    (hD : ∀ a t, D a (t + 1) = α • D a t + (α / (1 - α)) • pib a t ^ 2) (w0 : Ω) :
    (fun a => Sequences.dsum 𝔼 β
        (fun t z => periodU u v wt θ Ybar (yh a t z) (xu a t z) (xv a t z)) w0 -
      (W0615 𝔼 α β θ ω σ Φ Ybar (dY u (Ybar, 0)) (infl a) (F a) (K a) w0 -
        e a ^ 2 * (LargeDistortions.OmegaTilde Ybar (dY u (Ybar, 0)) α β θ ω σ Φ *
          Sequences.dsum 𝔼 β (LargeDistortions.loss615 α β θ ω σ sC Φ infl1 Y1 G1 cb1 q1 muw1
            tau1) w0) +
        tip615 𝔼 α β θ ω σ sC Φ Ybar (dY u (Ybar, 0))
          (fun t z => tip51 u v Ybar (xu a t z) (xv a t z)) (D a) (G a) (cb a) (q a) (muw a)
          (tau a) w0))
      =O[l] fun a => e a ^ 3 := by
  have h1 := prop615_layerB 𝔼 hα0 hα1 hβ0 hβ1 hθ hω hσ hsC hΦ0 hΦ hMd he hw0 hw1 hu hv hucc hvy
    hvyy hM hyh hxu hxv (first_order_o he hi1 hid) hxrO hFO hKO hfO hkO
    (first_order_o he hG1 hGd) (first_order_o he hcb1 hcbd) (first_order_o he hq1 hqd)
    (first_order_o he hm1 hmd) (first_order_o he ht1 htd) hpO hDO hg hq hV hD w0
  have h2 := loss615_first_order 𝔼 (α := α) (β := β) (θ := θ) (ω := ω) (σ := σ) (sC := sC)
    (Φ := Φ) hβ0.le hβ1 he hi1 hY1 hG1 hcb1 hq1 hm1 ht1 hid hYd hGd hcbd hqd hmd htd w0
  refine (h1.sub (h2.const_mul_left (LargeDistortions.OmegaTilde Ybar (dY u (Ybar, 0)) α β θ ω
    σ Φ))).congr_left fun a => ?_
  ring

/-- Woodford (2003), Proposition 6.15 and pp. 459–460 (the WELFARE RANKING): for two policies
facing the same disturbances and initial dispersion (same t.i.p.) and consistent with the same
initial commitment (same transitory term `W_0`), each with the expansion of
`prop615_first_order`, the policy whose first-order solution has the smaller discounted loss
`∑βᵗE_0L̃` gives strictly higher welfare for every small amplitude `ε ≠ 0` (`Ω̃ > 0`,
`LargeDistortions.OmegaTilde_pos`). -/
theorem prop615_ranking {α β θ ω σ Φ Ybar uc : ℝ} (hY : 0 < Ybar) (huc : 0 < uc)
    (hα0 : 0 < α) (hα1 : α < 1) (hβ1 : β < 1) (hθ : 0 < θ) (hω : 0 < ω) (hσ : 0 < σ)
    (hΦ0 : 0 ≤ Φ) (hΦ : Φ < 1) (he : Tendsto e l (𝓝 0)) (hne : ∀ᶠ a in l, e a ≠ 0)
    {WA WB W0 T : A → ℝ} {LA LB : ℝ}
    (hA : (fun a => WA a - (W0 a - e a ^ 2 * (LargeDistortions.OmegaTilde Ybar uc α β θ ω σ Φ *
      LA) + T a)) =O[l] fun a => e a ^ 3)
    (hB : (fun a => WB a - (W0 a - e a ^ 2 * (LargeDistortions.OmegaTilde Ybar uc α β θ ω σ Φ *
      LB) + T a)) =O[l] fun a => e a ^ 3)
    (hL : LA < LB) : ∀ᶠ a in l, WB a < WA a :=
  ranking_of_common he hne (T := fun a => W0 a + T a)
    (LargeDistortions.OmegaTilde_pos hY huc hα0 hα1 hβ1 hθ hω hσ hΦ0 hΦ)
    (hA.congr_left fun a => by ring) (hB.congr_left fun a => by ring) hL

/-! ## Proposition 6.7 (Layer B): transactions frictions, expansion at satiation

The base point is the steady state of the economy without distortions (`Φ_y = 0`) and AT
SATIATION in real balances (`Δ̄ = 0`, `m = m̄`). Along the family the interest differential
`î − îᵐ` (total, measured from satiation; Woodford's `î − îᵐ + Δ̄`) is `O(ε)`, real balances
stay BELOW satiation (`m̂ ≤ 0`), and the utility of money is replaced by its `C³` extension from
the left (`taylor_family_of_eqOn`): `u_m(m̄) = 0` and `u_mm(m̄−) < 0` are one-sided derivatives
(Assumption 6.1). The Layer-A identity `Transactions.prop_6_7_layerA` is used at this base point
(`Φ_y = Δ̄ = e₂ = e₃ = 0`); Woodford's `x*` and `Δ̄` are absorbed in the variables, which are
deviations from the efficient satiated point. -/

/-- Woodford (2003), (E.15), p. 699: the first and second derivatives of `U(Y, m, ξ)` along the
coordinate directions `e₁ = (1, 0, 0)`, `e₂ = (0, 1, 0)` and the disturbance `(0, 0, ξ)`
give the quadratic approximation of eq. (1.2) on `ℝ × ℝ × Ξ`. -/
theorem quadApprox_triple (U : ℝ × ℝ × Ξ → ℝ) (z : ℝ × ℝ × Ξ) (a c : ℝ) (ξ : Ξ) :
    ApproxTheory.quadApprox (U z) (fderiv ℝ U z) (fderiv ℝ (fderiv ℝ U) z) (a, c, ξ) =
      U z + fderiv ℝ U z (1, 0, 0) * a + fderiv ℝ U z (0, 1, 0) * c + fderiv ℝ U z (0, 0, ξ) +
        1 / 2 * (fderiv ℝ (fderiv ℝ U) z (1, 0, 0) (1, 0, 0) * a ^ 2 +
          (fderiv ℝ (fderiv ℝ U) z (1, 0, 0) (0, 1, 0) +
            fderiv ℝ (fderiv ℝ U) z (0, 1, 0) (1, 0, 0)) * (a * c) +
          fderiv ℝ (fderiv ℝ U) z (0, 1, 0) (0, 1, 0) * c ^ 2 +
          (fderiv ℝ (fderiv ℝ U) z (1, 0, 0) (0, 0, ξ) +
            fderiv ℝ (fderiv ℝ U) z (0, 0, ξ) (1, 0, 0)) * a +
          (fderiv ℝ (fderiv ℝ U) z (0, 1, 0) (0, 0, ξ) +
            fderiv ℝ (fderiv ℝ U) z (0, 0, ξ) (0, 1, 0)) * c +
          fderiv ℝ (fderiv ℝ U) z (0, 0, ξ) (0, 0, ξ)) := by
  have e : ((a, c, ξ) : ℝ × ℝ × Ξ) =
      a • ((1 : ℝ), (0 : ℝ), (0 : Ξ)) + c • ((0 : ℝ), (1 : ℝ), (0 : Ξ)) +
        ((0 : ℝ), (0 : ℝ), ξ) := by
    ext <;> simp
  rw [e]
  simp only [ApproxTheory.quadApprox, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), (E.15)–(E.17), pp. 699–700: the cubic discrepancy between the utility
expansion in LEVEL deviations `Ȳ(Ŷ + Ŷ²/2 + r₃)`, `m̄(m̂ + m̂²/2 + r₃)` at satiation (where
`u_m = 0`) and the book's polynomial in `Ŷ`, `m̂` (`smS = s_mσ_m⁻¹ = (η_iv̄)⁻¹`). -/
noncomputable def txAtom (σ χ smS g eps Y m rY rm : ℝ) : ℝ :=
  ((Y + Y ^ 2 / 2 + rY) - σ / 2 * (Y + Y ^ 2 / 2 + rY) ^ 2 +
      χ * (Y + Y ^ 2 / 2 + rY) * (m + m ^ 2 / 2 + rm) - smS / 2 * (m + m ^ 2 / 2 + rm) ^ 2 +
      σ * g * (Y + Y ^ 2 / 2 + rY) + smS * eps * (m + m ^ 2 / 2 + rm)) -
    (Y + (1 - σ) / 2 * Y ^ 2 + σ * g * Y - smS / 2 * m ^ 2 + χ * m * Y + smS * eps * m)

/-- Woodford (2003), (E.15): `txAtom = O(s³)` for first-order `Ŷ, m̂, g, εᵐ` and third-order
exponential atoms. -/
theorem txAtom_o (hs : Tendsto s L (𝓝 0)) (σ χ smS : ℝ) {g eps Y m rY rm : B → ℝ}
    (hg : g =O[L] fun b => s b ^ 1) (heps : eps =O[L] fun b => s b ^ 1)
    (hY : Y =O[L] fun b => s b ^ 1) (hm : m =O[L] fun b => s b ^ 1)
    (hrY : rY =O[L] fun b => s b ^ 3) (hrm : rm =O[L] fun b => s b ^ 3) :
    (fun b => txAtom σ χ smS (g b) (eps b) (Y b) (m b) (rY b) (rm b)) =O[L] fun b => s b ^ 3 := by
  have hA : (fun b => Y b ^ 2 / 2 + rY b) =O[L] fun b => s b ^ 2 :=
    (((o_pow hY 2).const_mul_left (1 / 2)).add (o_weaken hs (by norm_num) hrY)).congr_left
      fun b => by ring
  have hC : (fun b => m b ^ 2 / 2 + rm b) =O[L] fun b => s b ^ 2 :=
    (((o_pow hm 2).const_mul_left (1 / 2)).add (o_weaken hs (by norm_num) hrm)).congr_left
      fun b => by ring
  have hA1 : (fun b => 2 * Y b + (Y b ^ 2 / 2 + rY b)) =O[L] fun b => s b ^ 1 :=
    (hY.const_mul_left 2).add (o_weaken hs (by norm_num) hA)
  have hC1 : (fun b => 2 * m b + (m b ^ 2 / 2 + rm b)) =O[L] fun b => s b ^ 1 :=
    (hm.const_mul_left 2).add (o_weaken hs (by norm_num) hC)
  have hm1 : (fun b => m b + (m b ^ 2 / 2 + rm b)) =O[L] fun b => s b ^ 1 :=
    hm.add (o_weaken hs (by norm_num) hC)
  have t1 := o_mul hA hA1 (by norm_num : 2 + 1 = 3)
  have t2 := o_mul hA hm1 (by norm_num : 2 + 1 = 3)
  have t3 := o_mul hY hC (by norm_num : 1 + 2 = 3)
  have t4 := o_mul hC hC1 (by norm_num : 2 + 1 = 3)
  have t5 := o_mul hg hA (by norm_num : 1 + 2 = 3)
  have t6 := o_mul heps hC (by norm_num : 1 + 2 = 3)
  refine (((((hrY.sub (t1.const_mul_left (σ / 2))).add ((t2.add t3).const_mul_left χ)).sub
    (t4.const_mul_left (smS / 2))).add (t5.const_mul_left σ)).add
    (t6.const_mul_left smS)).congr_left fun b => ?_
  unfold txAtom
  ring

/-- Woodford (2003), (E.3)–(E.5), p. 694, at `Φ_y = 0`: the cubic discrepancy between the
integrated disutility (exact mean `m₁ + r_C`, per-good remainders `Rv`) and the book's
polynomial in `m₁ = Ŷ − ½(1 − θ⁻¹)var_i ŷ`. -/
noncomputable def vAtom (ω q m1 rC Rvbar : ℝ) : ℝ :=
  rC + (1 + ω) / 2 * (2 * m1 * rC + rC ^ 2) - ω * q * rC + Rvbar

/-- Woodford (2003), (E.3)–(E.5): `vAtom = O(s³)`. -/
theorem vAtom_o (hs : Tendsto s L (𝓝 0)) (ω : ℝ) {q m1 rC Rvbar : B → ℝ}
    (hq : q =O[L] fun b => s b ^ 1) (hm1 : m1 =O[L] fun b => s b ^ 1)
    (hrC : rC =O[L] fun b => s b ^ 3) (hRv : Rvbar =O[L] fun b => s b ^ 3) :
    (fun b => vAtom ω (q b) (m1 b) (rC b) (Rvbar b)) =O[L] fun b => s b ^ 3 := by
  have h1 := o_weaken hs (by norm_num : 3 ≤ 4) (o_mul hm1 hrC (by norm_num : 1 + 3 = 4))
  have h2 := o_weaken hs (by norm_num : 3 ≤ 6) (o_mul hrC hrC (by norm_num : 3 + 3 = 6))
  have h3 := o_weaken hs (by norm_num : 3 ≤ 4) (o_mul hq hrC (by norm_num : 1 + 3 = 4))
  refine (((hrC.add (((h1.const_mul_left 2).add h2).const_mul_left ((1 + ω) / 2))).sub
    (h3.const_mul_left ω)).add hRv).congr_left fun b => ?_
  unfold vAtom
  ring

/-- Woodford (2003), (4.9) and (E.15)–(E.18): the explicit remainder `Transactions.remainder`
is `O(s³)` along ANY family in which `Ŷ, î − îᵐ, g, q, εᵐ, Φ_y, Δ̄, e₂, e₃` are `O(s)` and
`var_i ŷ`, the money-demand residual `r` are `O(s²)` (not only along weighted rays as in
`Transactions.remainder_isBigO`). -/
theorem txRemainder_o (hs : Tendsto s L (𝓝 0)) (P : Transactions.TxParams)
    {x : B → Transactions.TxPoint}
    (hY : (fun b => (x b).Y) =O[L] fun b => s b ^ 1)
    (hd : (fun b => (x b).d) =O[L] fun b => s b ^ 1)
    (hg : (fun b => (x b).g) =O[L] fun b => s b ^ 1)
    (hq : (fun b => (x b).q) =O[L] fun b => s b ^ 1)
    (heps : (fun b => (x b).eps) =O[L] fun b => s b ^ 1)
    (hPhi : (fun b => (x b).Phi) =O[L] fun b => s b ^ 1)
    (hDel : (fun b => (x b).Delta) =O[L] fun b => s b ^ 1)
    (hV : (fun b => (x b).V) =O[L] fun b => s b ^ 2)
    (hr : (fun b => (x b).r) =O[L] fun b => s b ^ 2)
    (he2 : (fun b => (x b).e2) =O[L] fun b => s b ^ 1)
    (he3 : (fun b => (x b).e3) =O[L] fun b => s b ^ 1) :
    (fun b => Transactions.remainder P 1 (x b)) =O[L] fun b => s b ^ 3 := by
  have hr1 := o_weaken hs (by norm_num : 1 ≤ 2) hr
  have hm : (fun b => P.etaY * (x b).Y - P.etaI * (x b).d + (x b).eps + 1 * (x b).r)
      =O[L] fun b => s b ^ 1 :=
    (((hY.const_mul_left P.etaY).sub (hd.const_mul_left P.etaI)).add heps).add
      (hr1.const_mul_left 1)
  have hm2 := o_mul hm hm (by norm_num : 1 + 1 = 2)
  have hgm := o_mul hg hm (by norm_num : 1 + 1 = 2)
  have hem := o_mul heps hm (by norm_num : 1 + 1 = 2)
  have hA : (fun b => Transactions.remA P 1 (x b)) =O[L] fun b => s b ^ 3 :=
    ((o_mul hDel (((hm2.const_mul_left (1 / 2)).add (hgm.const_mul_left P.sigInv)).add
      (hem.const_mul_left P.chi)) (by norm_num : 1 + 2 = 3)).const_mul_left
        P.vbar⁻¹).congr_left fun b => by unfold Transactions.remA; ring
  have hB : (fun b => Transactions.remB P 1 (x b)) =O[L] fun b => s b ^ 3 :=
    (o_mul he2 (hem.sub (hm2.const_mul_left (1 / 2))) (by norm_num : 1 + 2 = 3)).congr_left
      fun b => by unfold Transactions.remB; ring
  have hlin : (fun b => P.etaY * (x b).Y - P.etaI * (x b).d) =O[L] fun b => s b ^ 1 :=
    (hY.const_mul_left P.etaY).sub (hd.const_mul_left P.etaI)
  have hC : (fun b => Transactions.remC P 1 (x b)) =O[L] fun b => s b ^ 3 := by
    have c1 := o_mul hDel hr (by norm_num : 1 + 2 = 3)
    have c2 := o_mul hr hY (by norm_num : 2 + 1 = 3)
    have c3 := o_mul hlin hr (by norm_num : 1 + 2 = 3)
    have c4 := o_weaken hs (by norm_num : 3 ≤ 4) (o_mul hr hr (by norm_num : 2 + 2 = 4))
    refine ((((c1.const_mul_left P.vbar⁻¹).add (c2.const_mul_left P.chi)).sub
      (c3.const_mul_left (1 / (P.etaI * P.vbar)))).sub
      (c4.const_mul_left (1 / (P.etaI * P.vbar) / 2))).congr_left fun b => ?_
    unfold Transactions.remC
    ring
  have hD : (fun b => Transactions.remD P (x b)) =O[L] fun b => s b ^ 3 := by
    have d1 := o_mul hd hY (by norm_num : 1 + 1 = 2)
    have d2 := o_mul hY hY (by norm_num : 1 + 1 = 2)
    refine (o_mul he3 ((d1.const_mul_left (1 / (P.etaI * P.vbar) * P.etaI)).sub
      (d2.const_mul_left (1 / (P.etaI * P.vbar) / 2 * P.etaY))) (by norm_num : 1 + 2 = 3)
      ).congr_left fun b => ?_
    unfold Transactions.remD
    ring
  have hE : (fun b => Transactions.remE P 1 (x b)) =O[L] fun b => s b ^ 3 := by
    have e1 := o_mul hPhi hV (by norm_num : 1 + 2 = 3)
    have e2' := o_mul hY hV (by norm_num : 1 + 2 = 3)
    have e3' := o_weaken hs (by norm_num : 3 ≤ 4) (o_mul hV hV (by norm_num : 2 + 2 = 4))
    have e4 := o_mul hq hV (by norm_num : 1 + 2 = 3)
    refine ((((e1.const_mul_left ((1 - P.thetaInv) / 2)).sub
      (e2'.const_mul_left ((1 + P.omega) * ((1 - P.thetaInv) / 2)))).add
      (e3'.const_mul_left ((1 + P.omega) / 2 * ((1 - P.thetaInv) / 2) ^ 2))).add
      (e4.const_mul_left (P.omega * ((1 - P.thetaInv) / 2)))).congr_left fun b => ?_
    unfold Transactions.remE
    ring
  exact ((((hA.add hB).add hC).add hD).sub hE).congr_left fun b => by
    unfold Transactions.remainder; ring

/-- Woodford (2003), §4.1, eq. (4.1)–(4.2), p. 420: the ACTUAL period utility with transactions
frictions, `u(Y, m; ξ) − ∫v(y(i); ξ)di`, for outputs `y(i) = Ȳe^{ŷ(i)}`, the Dixit–Stiglitz
aggregate `Y = Ȳe^{Ŷ}` and real balances `m = m̄e^{m̂}`. -/
noncomputable def periodUT (U : ℝ × ℝ × Ξ → ℝ) (v : ℝ × Ξ → ℝ) (w : ι → ℝ) (θ Ybar mbar : ℝ)
    (yh : ι → ℝ) (mh : ℝ) (xu xv : Ξ) : ℝ :=
  U (Ybar * Real.exp (logYidx w θ yh), mbar * Real.exp mh, xu) -
    ∑ i, w i * v (Ybar * Real.exp (yh i), xv)

/-- Woodford (2003), (E.15) and (E.3): the policy-independent terms of the expansion at the
satiated steady state `(Ȳ, m̄, 0)` (functions of the disturbances only). -/
noncomputable def tipT (Ut : ℝ × ℝ × Ξ → ℝ) (v : ℝ × Ξ → ℝ) (Ybar mbar : ℝ) (xu xv : Ξ) : ℝ :=
  (Ut (Ybar, mbar, 0) + fderiv ℝ Ut (Ybar, mbar, 0) (0, 0, xu) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xu) (0, 0, xu) / 2) -
    (v (Ybar, 0) + dXi v (Ybar, 0) xv + dXiXi v (Ybar, 0) xv / 2)

/-- Woodford (2003), App. E.4: the expansion point of `Transactions.prop_6_7_layerA` at the
satiated efficient steady state (`Φ_y = Δ̄ = e₂ = e₃ = 0`), with the money-demand residual
`r` given by `m̂ = η_yŶ − η_i(î − îᵐ) + εᵐ + r` (eq. (4.1)). -/
def txSat (P : Transactions.TxParams) (Y d g q eps V m : ℝ) : Transactions.TxPoint :=
  ⟨Y, d, g, q, eps, 0, 0, V, m - (P.etaY * Y - P.etaI * d + eps), 0, 0⟩

/-- Woodford (2003), **Proposition 6.7**, eq. (4.9), p. 422, LAYER B from the ACTUAL utility,
with the ONE-SIDED expansion at satiation (Assumption 6.1, (E.15)–(E.18)): the utility `U` of
output, real balances and disturbances coincides for `m ≤ m̄` with a `C³` function `Ũ` (its
extension from below satiation), `u_m(m̄) = 0`; `v` is `C³`; the coefficients at the
efficient satiated steady state `(Ȳ, m̄, 0)` define `σ⁻¹`, `χ`, `s_mσ_m⁻¹ = (η_iv̄)⁻¹`, `ω` and
the composite disturbances `g`, `εᵐ`, `q` (`h11`–`hq`); `η_y = χη_iv̄` there ((E.16)). Along any
family with `ŷ(i), m̂, î − îᵐ, ξ = O(s)`, the money-demand residual `O(s²)` and real balances
BELOW satiation (`m̂ ≤ 0`, i.e. `Δ̄ = εΔ₁ > 0`), the actual period utility is
`t.i.p. + Ȳu_c[tip − ½(4.9)] + O(s³)`, with the quadratic form (4.9)
`Ω_mc(Ŷ − Ŷⁿ)² + v̄⁻¹η_i(î − îᵐ)² + (θ⁻¹ + ω) var_i ŷ`. -/
theorem prop67_actual (hs : Tendsto s L (𝓝 0)) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {θ : ℝ} (hθ : θ ≠ 1) {U Ut : ℝ × ℝ × Ξ → ℝ} (hUt : ContDiff ℝ 3 Ut)
    {mbar : ℝ} (hmbar : 0 < mbar) (hEq : Set.EqOn U Ut {z | z.2.1 ≤ mbar})
    {v : ℝ × Ξ → ℝ} (hv : ContDiff ℝ 3 v) {Ybar : ℝ}
    (P : Transactions.TxParams) (hθi : P.thetaInv = θ⁻¹)
    (hey : P.etaY = P.chi * P.etaI * P.vbar) (hΩ : Transactions.omegaMC P ≠ 0)
    (hi : P.etaI ≠ 0) (hvb : P.vbar ≠ 0)
    (hsat : fderiv ℝ Ut (Ybar, mbar, 0) (0, 1, 0) = 0)
    (h11 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (1, 0, 0) =
      -(P.sigInv * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / Ybar))
    (h12 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (0, 1, 0) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (1, 0, 0) =
        2 * (P.chi * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / mbar))
    (h22 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (0, 1, 0) =
      -(Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / (P.etaI * P.vbar) / mbar ^ 2))
    (hvy : dY v (Ybar, 0) = fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0))
    (hvyy : dYY v (Ybar, 0) = P.omega * dY v (Ybar, 0) / Ybar)
    {yh : B → ι → ℝ} {mh d g q eps : B → ℝ} {xu xv : B → Ξ}
    (hg : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (0, 0, xu b) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xu b) (1, 0, 0) =
        2 * (P.sigInv * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) * g b))
    (heps : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (0, 0, xu b) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xu b) (0, 1, 0) =
        2 * (Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / (P.etaI * P.vbar) / mbar * eps b))
    (hq : ∀ b, dYXi v (Ybar, 0) (xv b) = -(P.omega * dY v (Ybar, 0) * q b))
    (hyh : yh =O[L] fun b => s b ^ 1) (hmh : mh =O[L] fun b => s b ^ 1)
    (hd : d =O[L] fun b => s b ^ 1) (hgO : g =O[L] fun b => s b ^ 1)
    (hqO : q =O[L] fun b => s b ^ 1) (hepsO : eps =O[L] fun b => s b ^ 1)
    (hxu : xu =O[L] fun b => s b ^ 1) (hxv : xv =O[L] fun b => s b ^ 1)
    (hr : (fun b => mh b - (P.etaY * logYidx w θ (yh b) - P.etaI * d b + eps b))
      =O[L] fun b => s b ^ 2)
    (hleft : ∀ᶠ b in L, mh b ≤ 0) :
    (fun b => periodUT U v w θ Ybar mbar (yh b) (mh b) (xu b) (xv b) -
      (tipT Ut v Ybar mbar (xu b) (xv b) + Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) *
        (Transactions.tip P (g b) (q b) (eps b) 0 0 - Transactions.loss49 P
          (txSat P (logYidx w θ (yh b)) (d b) (g b) (q b) (eps b) (crossVar w (yh b)) (mh b)) /
            2))) =O[L] fun b => s b ^ 3 := by
  set z0 : ℝ × ℝ × Ξ := (Ybar, mbar, 0) with hz0
  set uc := fderiv ℝ Ut z0 (1, 0, 0) with huc
  set smS := 1 / (P.etaI * P.vbar) with hsmS
  set Yh := fun b => logYidx w θ (yh b) with hYh
  have hYO : Yh =O[L] fun b => s b ^ 1 := logYidx_o hs hw0 hw1 hθ hyh
  have lev : ∀ (c : ℝ) (x : B → ℝ), x =O[L] (fun b => s b ^ 1) →
      (fun b => c * (Real.exp (x b) - 1)) =O[L] fun b => s b ^ 1 := fun c x hx => by
    have h2 := o_weaken hs (by norm_num : 1 ≤ 2) (o_pow hx 2)
    have h3 := o_weaken hs (by norm_num : 1 ≤ 3) (expRem_o hs hx)
    refine (((hx.add (h2.const_mul_left (1 / 2))).add h3).const_mul_left c).congr_left
      fun b => ?_
    rw [ExpLogCES.exp_sub_one_eq]
    ring
  -- (1) the one-sided Taylor expansion of `U` at satiation
  have hU1 := taylor_family_of_eqOn hUt hEq z0 hs
    (z := fun b => (Ybar * (Real.exp (Yh b) - 1), mbar * (Real.exp (mh b) - 1), xu b))
    ((lev Ybar Yh hYO).prod_left ((lev mbar mh hmh).prod_left hxu)) (by
      filter_upwards [hleft] with b hb
      have h1 : Real.exp (mh b) ≤ 1 := Real.exp_le_one_iff.mpr hb
      change (z0 + _).2.1 ≤ mbar
      simp only [hz0, Prod.snd_add, Prod.fst_add]
      nlinarith)
  -- (2) the disutility, good by good
  have hvs := IsBigO.fun_sum (s := Finset.univ) fun i _ =>
    (uTaylor_family_exp hv Ybar hs (coord_o hyh i) hxv).const_mul_left (w i)
  -- (3) the cubic atoms and the Layer-A remainder
  have hRv : (fun b => ∑ i, w i * Prop61.Rv 0 P.omega (q b) (yh b i) (expRem (yh b i)))
      =O[L] fun b => s b ^ 3 :=
    IsBigO.fun_sum (s := Finset.univ) fun i _ =>
      (Rv0_o hs P.omega hqO (coord_o hyh i) (expRem_o hs (coord_o hyh i))).const_mul_left (w i)
  have hV := crossVar_o hw0 hw1 hyh
  have hm1 : (fun b => Yh b - (1 - θ⁻¹) / 2 * crossVar w (yh b)) =O[L] fun b => s b ^ 1 :=
    hYO.sub ((o_weaken hs (by norm_num : 1 ≤ 2) hV).const_mul_left _)
  have hA1 := txAtom_o hs P.sigInv P.chi smS hgO hepsO hYO hmh (expRem_o hs hYO)
    (expRem_o hs hmh)
  have hA2 := vAtom_o hs P.omega hqO hm1 (cesAtom_o hs hw0 hw1 hθ hyh) hRv
  have hzero : (fun _ : B => (0 : ℝ)) =O[L] fun b => s b ^ 1 := isBigO_zero _ _
  have hA3 := txRemainder_o hs P
    (x := fun b => txSat P (Yh b) (d b) (g b) (q b) (eps b) (crossVar w (yh b)) (mh b))
    hYO hd hgO hqO hepsO hzero hzero hV hr hzero hzero
  refine (((hU1.sub hvs).add (((hA1.sub hA2).add hA3).const_mul_left (Ybar * uc)))).congr_left
    fun b => ?_
  -- (4) the exact identity at `b`
  have key := Transactions.prop_6_7_layerA P hΩ hi hvb
    (txSat P (Yh b) (d b) (g b) (q b) (eps b) (crossVar w (yh b)) (mh b))
    (by simp only [txSat]; rw [hey]; ring)
  have eU : z0 + (Ybar * (Real.exp (Yh b) - 1), mbar * (Real.exp (mh b) - 1), xu b) =
      (Ybar * Real.exp (Yh b), mbar * Real.exp (mh b), xu b) := by
    simp only [hz0, Prod.mk_add_mk, zero_add]
    congr 1 <;> [ring; (congr 1; ring)]
  have eQ : ApproxTheory.quadApprox (Ut z0) (fderiv ℝ Ut z0) (fderiv ℝ (fderiv ℝ Ut) z0)
      (Ybar * (Real.exp (Yh b) - 1), mbar * (Real.exp (mh b) - 1), xu b) =
      (Ut z0 + fderiv ℝ Ut z0 (0, 0, xu b) +
        fderiv ℝ (fderiv ℝ Ut) z0 (0, 0, xu b) (0, 0, xu b) / 2) +
      Ybar * uc * (Transactions.uTaylor P
        (txSat P (Yh b) (d b) (g b) (q b) (eps b) (crossVar w (yh b)) (mh b)) +
        txAtom P.sigInv P.chi smS (g b) (eps b) (Yh b) (mh b) (expRem (Yh b))
          (expRem (mh b))) := by
    rw [quadApprox_triple, hsat, h11, h12, h22, hg b, heps b, ExpLogCES.exp_sub_one_eq,
      ExpLogCES.exp_sub_one_eq]
    simp only [Transactions.uTaylor, txAtom, txSat, Transactions.mHat, Transactions.sM,
      Transactions.smSig, hsmS]
    field_simp
    ring
  have eV : ∑ i, w i * Prop61.uTaylor (v (Ybar, 0)) (dY v (Ybar, 0)) (dYY v (Ybar, 0))
      (dXi v (Ybar, 0) (xv b)) (dYXi v (Ybar, 0) (xv b)) (dXiXi v (Ybar, 0) (xv b))
      (Ybar * (yh b i + yh b i ^ 2 / 2 + expRem (yh b i))) =
      (v (Ybar, 0) + dXi v (Ybar, 0) (xv b) + dXiXi v (Ybar, 0) (xv b) / 2) +
      Ybar * uc * (Transactions.vTaylor P
        (txSat P (Yh b) (d b) (g b) (q b) (eps b) (crossVar w (yh b)) (mh b)) +
        vAtom P.omega (q b) (Yh b - (1 - θ⁻¹) / 2 * crossVar w (yh b))
          (Links.CES.cesAtom w θ (yh b))
          (∑ i, w i * Prop61.Rv 0 P.omega (q b) (yh b i) (expRem (yh b i)))) := by
    have hper : ∀ i, w i * Prop61.uTaylor (v (Ybar, 0)) (dY v (Ybar, 0)) (dYY v (Ybar, 0))
        (dXi v (Ybar, 0) (xv b)) (dYXi v (Ybar, 0) (xv b)) (dXiXi v (Ybar, 0) (xv b))
        (Ybar * (yh b i + yh b i ^ 2 / 2 + expRem (yh b i))) =
        (v (Ybar, 0) + dXi v (Ybar, 0) (xv b) + dXiXi v (Ybar, 0) (xv b) / 2) * w i +
          Ybar * uc * (w i * Prop61.Tv 0 P.omega (q b) (yh b i) +
            w i * Prop61.Rv 0 P.omega (q b) (yh b i) (expRem (yh b i))) := by
      intro i
      rw [Prop61.uTaylor, hvyy, hq b, hvy]
      unfold Prop61.Tv Prop61.Rv
      field_simp
      ring
    rw [Finset.sum_congr rfl fun i _ => hper i]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hw1]
    rw [TwoSectorWelfare.sum_Tv hw1, Links.CES.ces_relation w θ (yh b)]
    simp only [Transactions.vTaylor, Transactions.mOne, txSat, vAtom, TwoSectorWelfare.TvSec,
      hθi, hYh, logYidx]
    ring
  have hsum : ∑ i, w i * (v (Ybar * Real.exp (yh b i), xv b) -
      Prop61.uTaylor (v (Ybar, 0)) (dY v (Ybar, 0)) (dYY v (Ybar, 0)) (dXi v (Ybar, 0) (xv b))
        (dYXi v (Ybar, 0) (xv b)) (dXiXi v (Ybar, 0) (xv b))
        (Ybar * (yh b i + yh b i ^ 2 / 2 + expRem (yh b i)))) =
      ∑ i, w i * v (Ybar * Real.exp (yh b i), xv b) -
        ∑ i, w i * Prop61.uTaylor (v (Ybar, 0)) (dY v (Ybar, 0)) (dYY v (Ybar, 0))
          (dXi v (Ybar, 0) (xv b)) (dYXi v (Ybar, 0) (xv b)) (dXiXi v (Ybar, 0) (xv b))
          (Ybar * (yh b i + yh b i ^ 2 / 2 + expRem (yh b i))) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have htip : Transactions.tip P
      (txSat P (Yh b) (d b) (g b) (q b) (eps b) (crossVar w (yh b)) (mh b)).g
      (txSat P (Yh b) (d b) (g b) (q b) (eps b) (crossVar w (yh b)) (mh b)).q
      (txSat P (Yh b) (d b) (g b) (q b) (eps b) (crossVar w (yh b)) (mh b)).eps
      (txSat P (Yh b) (d b) (g b) (q b) (eps b) (crossVar w (yh b)) (mh b)).Phi
      (txSat P (Yh b) (d b) (g b) (q b) (eps b) (crossVar w (yh b)) (mh b)).Delta =
      Transactions.tip P (g b) (q b) (eps b) 0 0 := rfl
  rw [htip] at key
  simp only [periodUT, tipT]
  rw [← hz0, hsum, eV, eU, eQ]
  linear_combination (-(Ybar * uc)) * key

/-- Woodford (2003), Assumption 6.1, p. 422: above satiation the marginal utility of money is
zero, so utility is FLAT in `m` on `[m̄, ∞)` (for a utility `U` with derivative `u_m`). -/
theorem flat_above_satiation (A0 : Transactions.Assumption61) {U : ℝ → ℝ}
    (hU : ∀ m, HasDerivAt U (A0.um m) m) (c : ℝ) (hc : 0 ≤ c) :
    U (A0.mbar + c) = U A0.mbar := by
  rcases hc.eq_or_lt with h | h
  · rw [← h, add_zero]
  obtain ⟨ζ, hζ, hζeq⟩ := exists_hasDerivAt_eq_slope U A0.um (by linarith : A0.mbar < A0.mbar + c)
    (fun x _ => (hU x).continuousAt.continuousWithinAt) (fun x _ => hU x)
  rw [A0.um_sat ζ hζ.1.le] at hζeq
  have hne : A0.mbar + c - A0.mbar ≠ 0 := by linarith
  have := (eq_div_iff hne).mp hζeq
  linarith

/-- Woodford (2003), Assumption 6.1 and (E.15) (survey §4, Layer B for Prop. 6.7): the
expansion at satiation is ONE-SIDED. If utility is flat above satiation
(`flat_above_satiation`) while the one-sided second derivative `B = u_mm(m̄−)` is nonzero, the
expansion `U(m̄) + 0·(m − m̄) + ½B(m − m̄)²` of the left extension FAILS for a family approaching
from the right: its remainder `−½Bε²` is not `O(ε³)` as `ε → 0⁺`. So the family must approach
satiation from the left (`Δ̄ = εΔ₁ > 0`). -/
theorem two_sided_fails {U : ℝ → ℝ} {mbar B : ℝ} (hB : B ≠ 0)
    (hflat : ∀ c, 0 ≤ c → U (mbar + c) = U mbar) :
    ¬ (fun ε => U (mbar + ε) - (U mbar + ε ^ 2 / 2 * B)) =O[𝓝[>] 0] fun ε => ε ^ 3 := by
  intro h
  have h1 : (fun ε : ℝ => ε ^ 2) =O[𝓝[>] 0] fun ε => ε ^ 3 := by
    refine (h.const_mul_left (-2 / B)).congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hflat ε (le_of_lt hε)]
    field_simp
    ring
  have h3 : (fun ε : ℝ => ε ^ 3) =o[𝓝[>] 0] fun ε => ε ^ 2 := by
    have ht : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    exact ((isLittleO_one_iff ℝ).2 ht).mul_isBigO (isBigO_refl (fun ε : ℝ => ε ^ 2) _)
      |>.congr (fun ε => by ring) (fun ε => by ring)
  refine h3.not_isBigO ?_ h1
  have : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ 3 ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact pow_ne_zero 3 (ne_of_gt hε)
  exact this.frequently

/-- Woodford (2003), Assumption 6.1: `two_sided_fails` for the utility of money of
Assumption 6.1, with `B = u_mm(m̄−) < 0`. -/
theorem two_sided_fails_A61 (A0 : Transactions.Assumption61) {U : ℝ → ℝ}
    (hU : ∀ m, HasDerivAt U (A0.um m) m) :
    ¬ (fun ε => U (A0.mbar + ε) - (U A0.mbar + ε ^ 2 / 2 * A0.ummL)) =O[𝓝[>] 0]
      fun ε => ε ^ 3 :=
  two_sided_fails A0.ummL_neg.ne (flat_above_satiation A0 hU)

/-- Woodford (2003), App. E.1 (first-order solutions): if the cross-section is
`ŷ = εŷ₁ + O(ε²)` with `ŷ₁` bounded, then `var_i ŷ = ε² var_i ŷ₁ + O(ε³)`. -/
theorem crossVar_first_order (hs : Tendsto s L (𝓝 0)) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {y y1 : B → ι → ℝ}
    (hd : (fun b => y b - s b • y1 b) =O[L] fun b => s b ^ 2)
    (h1 : y1 =O[L] fun _ => (1 : ℝ)) :
    (fun b => crossVar w (y b) - s b ^ 2 * crossVar w (y1 b)) =O[L] fun b => s b ^ 3 := by
  have hc : ∀ i, (fun b => (y b i - crossMean w (y b)) - s b * (y1 b i - crossMean w (y1 b)))
      =O[L] fun b => s b ^ 2 := by
    intro i
    have hm : (fun b => crossMean w (y b - s b • y1 b)) =O[L] fun b => s b ^ 2 :=
      (IsBigO.of_bound 1 (Eventually.of_forall fun b => by
        rw [one_mul, Real.norm_eq_abs]
        exact ExpLogCES.abs_crossMean_le hw0 hw1 _)).trans hd
    have hi : (fun b => y b i - s b * y1 b i) =O[L] fun b => s b ^ 2 :=
      (IsBigO.of_bound 1 (Eventually.of_forall fun b => by
        rw [one_mul]
        simpa using norm_le_pi_norm (y b - s b • y1 b) i)).trans hd
    refine (hi.sub hm).congr_left fun b => ?_
    simp only [crossMean, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have : ∑ x, w x * (y b x - s b * y1 b x) = ∑ x, w x * y b x - s b * ∑ x, w x * y1 b x := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [this]
    ring
  have h1c : ∀ i, (fun b => y1 b i - crossMean w (y1 b)) =O[L] fun _ => (1 : ℝ) := by
    intro i
    have hcoord : (fun b => y1 b i) =O[L] fun _ => (1 : ℝ) :=
      (IsBigO.of_bound 1 (Eventually.of_forall fun b => by
        rw [one_mul]; exact norm_le_pi_norm (y1 b) i)).trans h1
    have hmean : (fun b => crossMean w (y1 b)) =O[L] fun _ => (1 : ℝ) :=
      (IsBigO.of_bound 1 (Eventually.of_forall fun b => by
        rw [one_mul, Real.norm_eq_abs]; exact ExpLogCES.abs_crossMean_le hw0 hw1 _)).trans h1
    exact hcoord.sub hmean
  refine (IsBigO.fun_sum (s := Finset.univ) fun i _ =>
    (sq_sub_o hs (hc i) (h1c i)).const_mul_left (w i)).congr_left fun b => ?_
  simp only [crossVar, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Woodford (2003), (4.9), p. 422: along a family with first-order solution
`(Ŷ₁, (î − îᵐ)₁, g₁, q₁, εᵐ₁, var_i ŷ₁)` (each variable `= ε × first order + O(ε²)`, the variance
`= ε² var₁ + O(ε³)`), the quadratic form (4.9) at the satiated point satisfies
`(4.9)(ε) = ε²(4.9)(first-order solution) + O(ε³)`. -/
theorem loss49_first_order (hs : Tendsto s L (𝓝 0)) (P : Transactions.TxParams)
    {Y d g q eps V m Y1 d1 g1 q1 eps1 V1 m1 : B → ℝ}
    (hY : (fun b => Y b - s b * Y1 b) =O[L] fun b => s b ^ 2)
    (hd : (fun b => d b - s b * d1 b) =O[L] fun b => s b ^ 2)
    (hg : (fun b => g b - s b * g1 b) =O[L] fun b => s b ^ 2)
    (hq : (fun b => q b - s b * q1 b) =O[L] fun b => s b ^ 2)
    (heps : (fun b => eps b - s b * eps1 b) =O[L] fun b => s b ^ 2)
    (hV : (fun b => V b - s b ^ 2 * V1 b) =O[L] fun b => s b ^ 3)
    (hY1 : Y1 =O[L] fun _ => (1 : ℝ)) (hd1 : d1 =O[L] fun _ => (1 : ℝ))
    (hg1 : g1 =O[L] fun _ => (1 : ℝ)) (hq1 : q1 =O[L] fun _ => (1 : ℝ))
    (heps1 : eps1 =O[L] fun _ => (1 : ℝ)) :
    (fun b => Transactions.loss49 P (txSat P (Y b) (d b) (g b) (q b) (eps b) (V b) (m b)) -
      s b ^ 2 * Transactions.loss49 P
        (txSat P (Y1 b) (d1 b) (g1 b) (q1 b) (eps1 b) (V1 b) (m1 b))) =O[L] fun b => s b ^ 3 := by
  set c1 := P.sigInv / Transactions.omegaMC P
  set c2 := P.omega / Transactions.omegaMC P
  set c3 := P.chi / Transactions.omegaMC P
  have hG : (fun b => (Y b - (c1 * g b + c2 * q b + c3 * eps b)) -
      s b * (Y1 b - (c1 * g1 b + c2 * q1 b + c3 * eps1 b))) =O[L] fun b => s b ^ 2 :=
    (hY.sub (((hg.const_mul_left c1).add (hq.const_mul_left c2)).add
      (heps.const_mul_left c3))).congr_left fun b => by ring
  have hG1 : (fun b => Y1 b - (c1 * g1 b + c2 * q1 b + c3 * eps1 b)) =O[L] fun _ => (1 : ℝ) :=
    hY1.sub (((hg1.const_mul_left c1).add (hq1.const_mul_left c2)).add (heps1.const_mul_left c3))
  refine ((((sq_sub_o hs hG hG1).const_mul_left (Transactions.omegaMC P)).add
    ((sq_sub_o hs hd hd1).const_mul_left (P.etaI / P.vbar))).add
    (hV.const_mul_left (P.thetaInv + P.omega))).congr_left fun b => ?_
  simp only [Transactions.loss49, txSat, Transactions.natRate, Transactions.xStar,
    Transactions.sM, c1, c2, c3]
  ring

/-- Woodford (2003), §1 (survey §4, Layer B): the generic bridge. If the actual welfare is
`T − (K/2) L(ε) + O(ε³)` (Layer A plus the Taylor step) and the loss satisfies
`L(ε) = ε² L₁ + O(ε³)` (first-order solution), then `W = T − (ε²/2) K L₁ + O(ε³)`. -/
theorem bridge_first_order {W T Lq L1 : B → ℝ} {K : ℝ}
    (hW : (fun b => W b - (T b - K * Lq b / 2)) =O[L] fun b => s b ^ 3)
    (hL : (fun b => Lq b - s b ^ 2 * L1 b) =O[L] fun b => s b ^ 3) :
    (fun b => W b - (T b - s b ^ 2 / 2 * (K * L1 b))) =O[L] fun b => s b ^ 3 :=
  (hW.sub (hL.const_mul_left (K / 2))).congr_left fun b => by ring

/-- Woodford (2003), **Proposition 6.7**, eq. (4.9), p. 422, LAYER B: under the hypotheses of
`prop67_actual`, if the family has the first-order solution
`(ŷ₁(i), Ŷ₁, (î − îᵐ)₁, g₁, q₁, εᵐ₁)` (`ŷ = εŷ₁ + O(ε²)` etc., all first-order objects bounded),
then the actual period utility is
`W(ε) = t.i.p.(ε) − (ε²/2)·Ȳu_c·(4.9)(first-order solution) + O(ε³)`, where the t.i.p.
`tipT + Ȳu_c·Transactions.tip` depends on the disturbances only. -/
theorem prop67_layerB (hs : Tendsto s L (𝓝 0)) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {θ : ℝ} (hθ : θ ≠ 1) {U Ut : ℝ × ℝ × Ξ → ℝ} (hUt : ContDiff ℝ 3 Ut)
    {mbar : ℝ} (hmbar : 0 < mbar) (hEq : Set.EqOn U Ut {z | z.2.1 ≤ mbar})
    {v : ℝ × Ξ → ℝ} (hv : ContDiff ℝ 3 v) {Ybar : ℝ}
    (P : Transactions.TxParams) (hθi : P.thetaInv = θ⁻¹)
    (hey : P.etaY = P.chi * P.etaI * P.vbar) (hΩ : Transactions.omegaMC P ≠ 0)
    (hi : P.etaI ≠ 0) (hvb : P.vbar ≠ 0)
    (hsat : fderiv ℝ Ut (Ybar, mbar, 0) (0, 1, 0) = 0)
    (h11 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (1, 0, 0) =
      -(P.sigInv * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / Ybar))
    (h12 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (0, 1, 0) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (1, 0, 0) =
        2 * (P.chi * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / mbar))
    (h22 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (0, 1, 0) =
      -(Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / (P.etaI * P.vbar) / mbar ^ 2))
    (hvy : dY v (Ybar, 0) = fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0))
    (hvyy : dYY v (Ybar, 0) = P.omega * dY v (Ybar, 0) / Ybar)
    {yh y1 : B → ι → ℝ} {mh d g q eps Y1 d1 g1 q1 eps1 : B → ℝ} {xu xv : B → Ξ}
    (hg : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (0, 0, xu b) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xu b) (1, 0, 0) =
        2 * (P.sigInv * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) * g b))
    (heps : ∀ b, fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (0, 0, xu b) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xu b) (0, 1, 0) =
        2 * (Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / (P.etaI * P.vbar) / mbar * eps b))
    (hq : ∀ b, dYXi v (Ybar, 0) (xv b) = -(P.omega * dY v (Ybar, 0) * q b))
    (hyh : yh =O[L] fun b => s b ^ 1) (hmh : mh =O[L] fun b => s b ^ 1)
    (hxu : xu =O[L] fun b => s b ^ 1) (hxv : xv =O[L] fun b => s b ^ 1)
    (hr : (fun b => mh b - (P.etaY * logYidx w θ (yh b) - P.etaI * d b + eps b))
      =O[L] fun b => s b ^ 2)
    (hleft : ∀ᶠ b in L, mh b ≤ 0)
    (hy1 : y1 =O[L] fun _ => (1 : ℝ)) (hY1 : Y1 =O[L] fun _ => (1 : ℝ))
    (hd1 : d1 =O[L] fun _ => (1 : ℝ)) (hg1 : g1 =O[L] fun _ => (1 : ℝ))
    (hq1 : q1 =O[L] fun _ => (1 : ℝ)) (heps1 : eps1 =O[L] fun _ => (1 : ℝ))
    (hyd : (fun b => yh b - s b • y1 b) =O[L] fun b => s b ^ 2)
    (hYd : (fun b => logYidx w θ (yh b) - s b * Y1 b) =O[L] fun b => s b ^ 2)
    (hdd : (fun b => d b - s b * d1 b) =O[L] fun b => s b ^ 2)
    (hgd : (fun b => g b - s b * g1 b) =O[L] fun b => s b ^ 2)
    (hqd : (fun b => q b - s b * q1 b) =O[L] fun b => s b ^ 2)
    (hepsd : (fun b => eps b - s b * eps1 b) =O[L] fun b => s b ^ 2) :
    (fun b => periodUT U v w θ Ybar mbar (yh b) (mh b) (xu b) (xv b) -
      ((tipT Ut v Ybar mbar (xu b) (xv b) + Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) *
        Transactions.tip P (g b) (q b) (eps b) 0 0) -
        s b ^ 2 / 2 * (Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) * Transactions.loss49 P
          (txSat P (Y1 b) (d1 b) (g1 b) (q1 b) (eps1 b) (crossVar w (y1 b)) 0))))
      =O[L] fun b => s b ^ 3 := by
  have fo : ∀ (x x1 : B → ℝ), (fun b => x b - s b * x1 b) =O[L] (fun b => s b ^ 2) →
      x1 =O[L] (fun _ => (1 : ℝ)) → x =O[L] fun b => s b ^ 1 := fun x x1 hd h1 =>
    ((o_weaken hs (by norm_num : 1 ≤ 2) hd).add
      (((isBigO_refl s L).mul h1).congr_right fun b => by ring)).congr_left fun b => by ring
  have hW := prop67_actual hs hw0 hw1 hθ hUt hmbar hEq hv P hθi hey hΩ hi hvb hsat h11 h12 h22
    hvy hvyy hg heps hq hyh hmh (fo d d1 hdd hd1) (fo g g1 hgd hg1) (fo q q1 hqd hq1)
    (fo eps eps1 hepsd heps1) hxu hxv hr hleft
  have hL := loss49_first_order hs P (m := mh) (m1 := fun _ => 0) hYd hdd hgd hqd hepsd
    (crossVar_first_order hs hw0 hw1 hyd hy1) hY1 hd1 hg1 hq1 heps1
  exact bridge_first_order (hW.congr_left fun b => by ring) hL

/-- Woodford (2003), Propositions 6.7, 6.10 and 6.12 and §1, pp. 386–389 (the WELFARE
RANKING): for two policies facing the same disturbances (same t.i.p.), each with a Layer-B
expansion `W = T − (ε²/2)K L(first-order solution) + O(ε³)` (`prop67_layerB`,
`prop610_layerB`, `prop612_layerB`) with `K = Ȳu_c > 0`, the policy whose first-order solution
has the smaller quadratic loss is strictly better for every small `ε ≠ 0`. -/
theorem ranking_layerB {A' : Type*} {l' : Filter A'} {e' : A' → ℝ}
    (he : Tendsto e' l' (𝓝 0)) (hne : ∀ᶠ a in l', e' a ≠ 0) {K : ℝ} (hK : 0 < K)
    {WA WB T : A' → ℝ} {LA LB : ℝ}
    (hA : (fun a => WA a - (T a - e' a ^ 2 / 2 * (K * LA))) =O[l'] fun a => e' a ^ 3)
    (hB : (fun a => WB a - (T a - e' a ^ 2 / 2 * (K * LB))) =O[l'] fun a => e' a ^ 3)
    (hL : LA < LB) : ∀ᶠ a in l', WB a < WA a :=
  ranking_of_common he hne (WA := WA) (WB := WB) (T := T) (k := K / 2) (by linarith)
    (hA.congr_left fun a => by ring) (hB.congr_left fun a => by ring) hL

/-! ## Discounted sums along deterministic paths (Propositions 6.8, 6.11, 6.13)

For the propositions whose Layer-A statements are about real sequences (`Transactions.prop_6_8`,
`TwoSectorWelfare.prop_6_11`, `StickyWageWelfare.prop_6_13`), uncertainty is a finite state
space of PATHS: each path is a sequence, the discounted sum along a path is a `tsum`, and the
expectation is a finite weighted sum (`OneParamTaylor.expect`, `isBigO_expect`). Uniformity:
the period remainder must be `O(ε³)` uniformly in the date along each path (filter
`l ×ˢ ⊤` on `A × ℕ`); with finitely many paths this is uniformity in `(t, ω)`. -/

/-- Woodford (2003), (4.10)–(4.11), p. 423 (uniform orders and discounting along a path): if
`f_t = O(g)` uniformly in `t` and `0 ≤ β < 1`, then `∑βᵗf_t = O(g)`. -/
theorem tsum_o {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f : A → ℕ → ℝ} {g : A → ℝ}
    (h : (fun p : A × ℕ => f p.1 p.2) =O[l ×ˢ (⊤ : Filter ℕ)] fun p => g p.1) :
    (fun a => ∑' t, β ^ t * f a t) =O[l] g := by
  obtain ⟨C, hC⟩ := uniform_bound h
  refine IsBigO.of_bound (C / (1 - β)) ?_
  filter_upwards [hC] with a ha
  have h1 := Sequences.abs_tsum_le (f := f a) (fun t => ha t) hβ0 hβ1
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  calc _ ≤ C * |g a| / (1 - β) := h1
    _ = C / (1 - β) * |g a| := by ring

/-- Woodford (2003), §2, p. 394: a sequence family that is uniformly `O(eᵏ)` is bounded for
every amplitude close enough to `0`. -/
theorem seq_bdd_of_o (he : Tendsto e l (𝓝 0)) {f : A → ℕ → ℝ} {k : ℕ}
    (h : (fun p : A × ℕ => f p.1 p.2) =O[l ×ˢ (⊤ : Filter ℕ)] fun p => e p.1 ^ k) :
    ∀ᶠ a in l, Sequences.Bdd (f a) := by
  obtain ⟨C, hC⟩ := uniform_bound (g := fun a => e a ^ k) h
  have h1 : ∀ᶠ a in l, |e a| ≤ 1 := by
    filter_upwards [he.eventually (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)] with a ha
    simpa [Real.dist_eq] using ha
  filter_upwards [hC, h1] with a ha h1a
  refine ⟨|C|, fun t => ?_⟩
  have hp : |e a ^ k| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) h1a
  calc |f a t| ≤ C * |e a ^ k| := ha t
    _ ≤ |C| * |e a ^ k| := mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg _)
    _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left hp (abs_nonneg C)
    _ = |C| := mul_one _

/-- Woodford (2003), **Proposition 6.8**, (4.10)–(4.11), p. 423, LAYER B along a path: if the
period utility has the expansion of `prop67_actual` (`W = τ − (K/2)(4.9) + O(ε³)`, `τ`
policy-independent, `K = Ȳu_c`) UNIFORMLY in the date (that theorem applies verbatim on the
filter `l ×ˢ ⊤`), the first-order variables are uniformly `O(ε)`, the
mean-price inflation `π̄` satisfies `π̄ − π = O(ε²)` and the Calvo dispersion law
`∑βᵗvar_i ŷ_t = θ²(ψ∑βᵗπ̄_t² + T₀)` holds (`T₀` policy-independent), then
`∑βᵗW_t = ∑βᵗτ_t − (K/2)[Λ ∑βᵗL_t + (θ⁻¹ + ω)θ²T₀] + O(ε³)` with `L_t` the loss (4.10)
evaluated at the actual path (with `π`, not `π̄`) and `Λ = θ(1 + ωθ)ψ > 0`. -/
theorem prop68_layerB (P : Transactions.TxParams) {α β θ K : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ : 0 < θ) (hθi : P.thetaInv = 1 / θ) (hω : 0 ≤ P.omega)
    (hΩ : 0 < Transactions.omegaMC P) (hv : P.vbar ≠ 0) (he : Tendsto e l (𝓝 0))
    {W τ Y d g q eps V pib infl : A → ℕ → ℝ} {T0 : A → ℝ} (hτ : ∀ a, Sequences.Bdd (τ a))
    (hP : (fun p : A × ℕ => W p.1 p.2 - (τ p.1 p.2 - K * Transactions.loss49 P
      (txSat P (Y p.1 p.2) (d p.1 p.2) (g p.1 p.2) (q p.1 p.2) (eps p.1 p.2) (V p.1 p.2) 0) / 2))
      =O[l ×ˢ ⊤] fun p => e p.1 ^ 3)
    (hY : (fun p : A × ℕ => Y p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hd : (fun p : A × ℕ => d p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hg : (fun p : A × ℕ => g p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hq : (fun p : A × ℕ => q p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (heps : (fun p : A × ℕ => eps p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hi : (fun p : A × ℕ => infl p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hpO : (fun p : A × ℕ => pib p.1 p.2 - infl p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2)
    (hV : ∀ a, HasSum (fun t => β ^ t * V a t)
      (θ ^ 2 * (Moments.calvoK α β * ∑' t, β ^ t * pib a t ^ 2 + T0 a))) :
    (fun a => ∑' t, β ^ t * W a t - (∑' t, β ^ t * τ a t - K / 2 *
      (θ * (1 + P.omega * θ) * Moments.calvoK α β * ∑' t, β ^ t * Transactions.loss410 P α β θ
        (infl a t) (Y a t - Transactions.natRate P (g a t) (q a t) (eps a t)) (d a t) +
        (P.thetaInv + P.omega) * θ ^ 2 * T0 a))) =O[l] fun a => e a ^ 3 := by
  have hs := tendsto_amp (J := ℕ) he
  set R : A → ℕ → ℝ := fun a t => W a t - (τ a t - K * Transactions.loss49 P
    (txSat P (Y a t) (d a t) (g a t) (q a t) (eps a t) (V a t) 0) / 2) with hR
  set X : A → ℕ → ℝ := fun a t => Y a t - Transactions.natRate P (g a t) (q a t) (eps a t)
    with hX
  have hXO : (fun p : A × ℕ => X p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 :=
    (hY.sub ((((hg.const_mul_left P.sigInv).add (hq.const_mul_left P.omega)).add
      (heps.const_mul_left P.chi)).const_mul_left (Transactions.omegaMC P)⁻¹)).congr_left
        fun p => by simp only [hX, Transactions.natRate]; ring
  have hpib : (fun p : A × ℕ => pib p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 :=
    ((o_weaken hs (by norm_num : 1 ≤ 2) hpO).add hi).congr_left fun p => by ring
  have hPO : (fun p : A × ℕ => pib p.1 p.2 ^ 2 - infl p.1 p.2 ^ 2)
      =O[l ×ˢ ⊤] fun p => e p.1 ^ 3 :=
    (o_mul hpO ((o_weaken hs (by norm_num : 1 ≤ 2) hpO).add (hi.const_mul_left 2))
      (by norm_num : 2 + 1 = 3)).congr_left fun p => by ring
  have bR := seq_bdd_of_o (f := R) he hP
  have bX := seq_bdd_of_o (f := fun a t => X a t ^ 2) he (o_pow hXO 2)
  have bI := seq_bdd_of_o (f := fun a t => d a t ^ 2) he (o_pow hd 2)
  have bp := seq_bdd_of_o (f := fun a t => pib a t ^ 2) he (o_pow hpib 2)
  have bi := seq_bdd_of_o (f := fun a t => infl a t ^ 2) he (o_pow hi 2)
  have hev : ∀ᶠ a in l, ∑' t, β ^ t * W a t - (∑' t, β ^ t * τ a t - K / 2 *
      (θ * (1 + P.omega * θ) * Moments.calvoK α β * ∑' t, β ^ t * Transactions.loss410 P α β θ
        (infl a t) (X a t) (d a t) + (P.thetaInv + P.omega) * θ ^ 2 * T0 a)) =
      ∑' t, β ^ t * R a t - K / 2 * (θ * (1 + P.omega * θ) * Moments.calvoK α β) *
        ∑' t, β ^ t * (pib a t ^ 2 - infl a t ^ 2) := by
    filter_upwards [bR, bX, bI, bp, bi] with a hRa hXa hIa hpa hia
    have sR := (hRa.summable hβ0 hβ1).hasSum
    have sX := (hXa.summable hβ0 hβ1).hasSum
    have sI := (hIa.summable hβ0 hβ1).hasSum
    have sP := (hpa.summable hβ0 hβ1).hasSum
    have si := (hia.summable hβ0 hβ1).hasSum
    have sτ := ((hτ a).summable hβ0 hβ1).hasSum
    obtain ⟨h1, -⟩ := Transactions.prop_6_8 P hα0 hα1 hβ1 hθ hθi hω hΩ hv sX sI sP (hV a)
    have hW : HasSum (fun t => β ^ t * W a t)
        (∑' t, β ^ t * τ a t - K / 2 * (θ * (1 + P.omega * θ) * Moments.calvoK α β *
          (∑' t, β ^ t * pib a t ^ 2 + Transactions.lambdaX P α β θ * ∑' t, β ^ t * X a t ^ 2 +
            Transactions.lambdaI P (Transactions.lambdaX P α β θ) * ∑' t, β ^ t * d a t ^ 2) +
          (P.thetaInv + P.omega) * θ ^ 2 * T0 a) + ∑' t, β ^ t * R a t) := by
      refine ((sτ.sub (h1.mul_left (K / 2))).add sR).congr_fun fun t => ?_
      simp only [hR, hX, Transactions.loss49, txSat, Transactions.xStar, Transactions.sM]
      ring
    have hL : HasSum (fun t => β ^ t * Transactions.loss410 P α β θ (infl a t) (X a t) (d a t))
        (∑' t, β ^ t * infl a t ^ 2 + Transactions.lambdaX P α β θ * ∑' t, β ^ t * X a t ^ 2 +
          Transactions.lambdaI P (Transactions.lambdaX P α β θ) * ∑' t, β ^ t * d a t ^ 2) := by
      refine ((si.add (sX.mul_left (Transactions.lambdaX P α β θ))).add
        (sI.mul_left (Transactions.lambdaI P (Transactions.lambdaX P α β θ)))).congr_fun
          fun t => ?_
      simp only [Transactions.loss410]
      ring
    have hD : HasSum (fun t => β ^ t * (pib a t ^ 2 - infl a t ^ 2))
        (∑' t, β ^ t * pib a t ^ 2 - ∑' t, β ^ t * infl a t ^ 2) :=
      (sP.sub si).congr_fun fun t => by ring
    rw [hW.tsum_eq, hL.tsum_eq, hD.tsum_eq]
    ring
  exact ((tsum_o (f := R) hβ0 hβ1 hP).sub ((tsum_o hβ0 hβ1 hPO).const_mul_left
    (K / 2 * (θ * (1 + P.omega * θ) * Moments.calvoK α β)))).congr'
      (hev.mono fun a ha => ha.symm) (Eventually.of_forall fun _ => rfl)

/-- Woodford (2003), (4.10), p. 423, with a first-order solution along a path: if
`π = επ₁ + O(ε²)`, `x − x* = ε(x − x*)₁ + O(ε²)` and `î − îᵐ = ε(î − îᵐ)₁ + O(ε²)` uniformly
(first-order sequences bounded), then `∑βᵗL_t = ε²∑βᵗL_t(first-order solution) + O(ε³)`. -/
theorem loss410_first_order (P : Transactions.TxParams) {α β θ : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (he : Tendsto e l (𝓝 0)) {infl xg d : A → ℕ → ℝ} {infl1 xg1 d1 : ℕ → ℝ}
    (hi1 : Sequences.Bdd infl1) (hx1 : Sequences.Bdd xg1) (hd1 : Sequences.Bdd d1)
    (hid : (fun p : A × ℕ => infl p.1 p.2 - e p.1 * infl1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2)
    (hxd : (fun p : A × ℕ => xg p.1 p.2 - e p.1 * xg1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2)
    (hdd : (fun p : A × ℕ => d p.1 p.2 - e p.1 * d1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2) :
    (fun a => ∑' t, β ^ t * Transactions.loss410 P α β θ (infl a t) (xg a t) (d a t) -
      e a ^ 2 * ∑' t, β ^ t * Transactions.loss410 P α β θ (infl1 t) (xg1 t) (d1 t))
      =O[l] fun a => e a ^ 3 := by
  have hs := tendsto_amp (J := ℕ) he
  have b1 : ∀ {u : ℕ → ℝ}, Sequences.Bdd u →
      (fun p : A × ℕ => u p.2) =O[l ×ˢ ⊤] fun _ => (1 : ℝ) := fun {u} hu => by
    obtain ⟨M, hM⟩ := hu
    exact IsBigO.of_bound M (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, norm_one, mul_one]; exact hM _)
  have hD : (fun p : A × ℕ => Transactions.loss410 P α β θ (infl p.1 p.2) (xg p.1 p.2) (d p.1 p.2)
      - e p.1 ^ 2 * Transactions.loss410 P α β θ (infl1 p.2) (xg1 p.2) (d1 p.2))
      =O[l ×ˢ ⊤] fun p => e p.1 ^ 3 :=
    (((sq_sub_o hs hid (b1 hi1)).add ((sq_sub_o hs hxd (b1 hx1)).const_mul_left
      (Transactions.lambdaX P α β θ))).add ((sq_sub_o hs hdd (b1 hd1)).const_mul_left
      (Transactions.lambdaI P (Transactions.lambdaX P α β θ)))).congr_left fun p => by
        simp only [Transactions.loss410]; ring
  have hfo : ∀ {x : A → ℕ → ℝ} {x1 : ℕ → ℝ}, Sequences.Bdd x1 →
      (fun p : A × ℕ => x p.1 p.2 - e p.1 * x1 p.2) =O[l ×ˢ ⊤] (fun p => e p.1 ^ 2) →
      (fun p : A × ℕ => x p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 := fun {x} {x1} h1 hd =>
    ((o_weaken hs (by norm_num : 1 ≤ 2) hd).add
      (((isBigO_refl (fun p : A × ℕ => e p.1) _).mul (b1 h1)).congr_right fun p => by
        ring)).congr_left fun p => by ring
  have hL1 : Sequences.Bdd (fun t => Transactions.loss410 P α β θ (infl1 t) (xg1 t) (d1 t)) := by
    obtain ⟨M1, hM1⟩ := hi1
    obtain ⟨M2, hM2⟩ := hx1
    obtain ⟨M3, hM3⟩ := hd1
    refine ⟨M1 ^ 2 + |Transactions.lambdaX P α β θ| * M2 ^ 2 +
      |Transactions.lambdaI P (Transactions.lambdaX P α β θ)| * M3 ^ 2, fun t => ?_⟩
    have e1 : |infl1 t| ^ 2 ≤ M1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hM1 t) 2
    have e2 : |xg1 t| ^ 2 ≤ M2 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hM2 t) 2
    have e3 : |d1 t| ^ 2 ≤ M3 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hM3 t) 2
    unfold Transactions.loss410
    calc _ ≤ |infl1 t ^ 2| + |Transactions.lambdaX P α β θ * xg1 t ^ 2| +
          |Transactions.lambdaI P (Transactions.lambdaX P α β θ) * d1 t ^ 2| :=
          abs_add_three _ _ _
      _ = |infl1 t| ^ 2 + |Transactions.lambdaX P α β θ| * |xg1 t| ^ 2 +
          |Transactions.lambdaI P (Transactions.lambdaX P α β θ)| * |d1 t| ^ 2 := by
          simp only [abs_mul, abs_pow]
      _ ≤ _ := by gcongr
  have bL := seq_bdd_of_o (f := fun a t => Transactions.loss410 P α β θ (infl a t) (xg a t)
    (d a t)) he ((((o_mul (hfo hi1 hid) (hfo hi1 hid) (by norm_num : 1 + 1 = 2)).add
      ((o_mul (hfo hx1 hxd) (hfo hx1 hxd) (by norm_num : 1 + 1 = 2)).const_mul_left
        (Transactions.lambdaX P α β θ))).add
      ((o_mul (hfo hd1 hdd) (hfo hd1 hdd) (by norm_num : 1 + 1 = 2)).const_mul_left
        (Transactions.lambdaI P (Transactions.lambdaX P α β θ)))).congr_left fun p => by
          simp only [Transactions.loss410]; ring)
  have hev : ∀ᶠ a in l, ∑' t, β ^ t * (Transactions.loss410 P α β θ (infl a t) (xg a t) (d a t)
      - e a ^ 2 * Transactions.loss410 P α β θ (infl1 t) (xg1 t) (d1 t)) =
      ∑' t, β ^ t * Transactions.loss410 P α β θ (infl a t) (xg a t) (d a t) -
        e a ^ 2 * ∑' t, β ^ t * Transactions.loss410 P α β θ (infl1 t) (xg1 t) (d1 t) := by
    filter_upwards [bL] with a ha
    have h1 := (ha.summable hβ0 hβ1).hasSum
    have h2 := ((hL1.summable hβ0 hβ1).hasSum).mul_left (e a ^ 2)
    exact ((h1.sub h2).congr_fun fun t => by ring).tsum_eq
  exact (tsum_o hβ0 hβ1 hD).congr' hev (Eventually.of_forall fun _ => rfl)

/-! ## Proposition 6.10 (Layer B): two sectors, from the actual utility

The base point is the efficient steady state (`Φ_y = 0`); the two-sector aggregate is the exact
CES aggregator `TwoSectorWelfare.upperCES` of the sectoral Dixit–Stiglitz indices, with the
sectoral preference shocks `φ_j = e^{φ̂_j}` normalised by `n₁φ₁ + n₂φ₂ = 1` (Ch. 3, p. 201). -/

/-- Woodford (2003), App. E.6, p. 703: the log two-sector aggregate `Ŷ = log(Y/Ȳ)` with
sectoral log indices `Ŷ_j` and preference shocks `φ̂_j`. -/
noncomputable def logY2 (n1 η Ybar f1 f2 Y1 Y2 : ℝ) : ℝ :=
  Real.log (TwoSectorWelfare.upperCES n1 η (Real.exp (1 * f1)) (Real.exp (1 * f2))
    (n1 * Ybar * Real.exp (1 * Y1)) ((1 - n1) * Ybar * Real.exp (1 * Y2)) / Ybar)

/-- Woodford (2003), (E.27), p. 703: the exogenous second-order term `τ` of the aggregator
expansion, `r⁻¹η⁻¹S + ½n₁n₂r⁻¹η⁻²(φ̂₂ − φ̂₁)²` with `S = n₁φ̂₁ + n₂φ̂₂`, `r = 1 − η⁻¹`
(`TwoSectorWelfare.upperCES_E27`). -/
noncomputable def tauAgg (ηi n1 f1 f2 : ℝ) : ℝ :=
  (1 - ηi)⁻¹ * ηi * (n1 * f1 + (1 - n1) * f2) +
    n1 * (1 - n1) * (1 - ηi)⁻¹ * ηi ^ 2 / 2 * (f2 - f1) ^ 2

/-- Woodford (2003), (E.27): the third-order remainder of the two-sector aggregator,
`Ŷ − [n₁Ŷ₁ + n₂Ŷ₂ + ET]`. -/
noncomputable def aggAtom (n1 η Ybar f1 f2 Y1 Y2 : ℝ) : ℝ :=
  logY2 n1 η Ybar f1 f2 Y1 Y2 - (n1 * Y1 + (1 - n1) * Y2 +
    TwoSectorWelfare.ET η⁻¹ n1 (f2 - f1) Y1 Y2 (tauAgg η⁻¹ n1 f1 f2))

/-- Woodford (2003), (E.27), p. 703 (the "`O(3)`" of the two-sector aggregator): for
first-order sectoral indices and preference shocks the aggregator remainder is `O(s³)`
(from `ExpLogCES.cumulant_expansion` and the exact log form `TwoSectorWelfare.log_upperCES`). -/
theorem aggAtom_o (hs : Tendsto s L (𝓝 0)) {n1 η Ybar : ℝ} (hn0 : 0 < n1) (hn1 : n1 < 1)
    (hη : 0 < η) (hη1 : η ≠ 1) (hY : 0 < Ybar) {f1 f2 Y1 Y2 : B → ℝ}
    (hf1 : f1 =O[L] fun b => s b ^ 1) (hf2 : f2 =O[L] fun b => s b ^ 1)
    (hY1 : Y1 =O[L] fun b => s b ^ 1) (hY2 : Y2 =O[L] fun b => s b ^ 1) :
    (fun b => aggAtom n1 η Ybar (f1 b) (f2 b) (Y1 b) (Y2 b)) =O[L] fun b => s b ^ 3 := by
  have hr : (1 : ℝ) - η⁻¹ ≠ 0 := by
    intro h
    apply hη1
    have : η⁻¹ = 1 := by linarith
    simpa using congrArg (·⁻¹) this
  have hr' : (η - 1) / η = 1 - η⁻¹ := by field_simp
  have hn2 : 0 < 1 - n1 := by linarith
  have hw0 : ∀ i, 0 ≤ (![n1, 1 - n1] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> simp [hn0.le, hn2.le]
  have hw1 : ∑ i, (![n1, 1 - n1] : Fin 2 → ℝ) i = 1 := by simp [Fin.sum_univ_two]
  set z : B → Fin 2 → ℝ := fun b => ![η⁻¹ * f1 b + (1 - η⁻¹) * Y1 b,
    η⁻¹ * f2 b + (1 - η⁻¹) * Y2 b] with hz
  have hzO : z =O[L] fun b => s b ^ 1 := by
    rw [isBigO_pi]
    intro i
    fin_cases i
    · exact (hf1.const_mul_left _).add (hY1.const_mul_left _)
    · exact (hf2.const_mul_left _).add (hY2.const_mul_left _)
  have hc := (ExpLogCES.cumulant_expansion hw0 hw1 one_ne_zero).comp_tendsto
    (tendsto_of_o_one hs hzO)
  have h3 : (fun b => ‖z b‖ ^ 3) =O[L] fun b => s b ^ 3 :=
    (hzO.norm_left.pow 3).congr_right fun b => by ring
  refine ((hc.trans h3).const_mul_left (1 - η⁻¹)⁻¹).congr_left fun b => ?_
  have hlog := TwoSectorWelfare.log_upperCES hn0 hn1 hη hη1 hY (f1 b) (f2 b) (Y1 b) (Y2 b) 1
  simp only [Function.comp, aggAtom, logY2]
  rw [hlog, hr']
  simp only [TwoSectorWelfare.lse, ExpLogCES.cumulant, ExpLogCES.cesMoment, ExpLogCES.crossMean,
    ExpLogCES.crossVar, hz, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_mul, TwoSectorWelfare.ET, tauAgg]
  field_simp
  ring

/-- Woodford (2003), p. 201 (the normalisation `n₁φ₁ + n₂φ₂ = 1`): the size-weighted mean
`S = n₁φ̂₁ + n₂φ̂₂` of first-order preference shocks is `O(s²)`. -/
theorem S_o (hs : Tendsto s L (𝓝 0)) {n1 : ℝ} {f1 f2 : B → ℝ}
    (hf1 : f1 =O[L] fun b => s b ^ 1) (hf2 : f2 =O[L] fun b => s b ^ 1)
    (hnorm : ∀ b, n1 * Real.exp (f1 b) + (1 - n1) * Real.exp (f2 b) = 1) :
    (fun b => n1 * f1 b + (1 - n1) * f2 b) =O[L] fun b => s b ^ 2 := by
  have h1 := ((o_pow hf1 2).const_mul_left (1 / 2)).add
    (o_weaken hs (by norm_num : 2 ≤ 3) (expRem_o hs hf1))
  have h2 := ((o_pow hf2 2).const_mul_left (1 / 2)).add
    (o_weaken hs (by norm_num : 2 ≤ 3) (expRem_o hs hf2))
  refine ((h1.const_mul_left n1).add (h2.const_mul_left (1 - n1))).neg_left.congr_left
    fun b => ?_
  have e1 := ExpLogCES.exp_sub_one_eq (f1 b)
  have e2 := ExpLogCES.exp_sub_one_eq (f2 b)
  have hb := hnorm b
  linear_combination n1 * e1 + (1 - n1) * e2 - hb

/-- Woodford (2003), (E.31), p. 705: the remainder of Proposition 6.10 is `O(s³)` along ANY
family with `Φ, q_j, Ŷ_j, d = O(s)` and `V_j, τ = O(s²)` (not only along weighted rays). -/
theorem R610_o (hs : Tendsto s L (𝓝 0)) (ω θi ηi n1 : ℝ)
    {Phi q1 q2 Y1 Y2 V1 V2 d τ : B → ℝ} (hPhi : Phi =O[L] fun b => s b ^ 1)
    (hq1 : q1 =O[L] fun b => s b ^ 1) (hq2 : q2 =O[L] fun b => s b ^ 1)
    (hY1 : Y1 =O[L] fun b => s b ^ 1) (hY2 : Y2 =O[L] fun b => s b ^ 1)
    (hV1 : V1 =O[L] fun b => s b ^ 2) (hV2 : V2 =O[L] fun b => s b ^ 2)
    (hd : d =O[L] fun b => s b ^ 1) (hτ : τ =O[L] fun b => s b ^ 2) :
    (fun b => TwoSectorWelfare.R610 ω θi ηi n1 (Phi b) (q1 b) (q2 b) (Y1 b) (Y2 b) (V1 b)
      (V2 b) (d b) (τ b)) =O[L] fun b => s b ^ 3 := by
  have hdY := hY2.sub hY1
  have hET : (fun b => TwoSectorWelfare.ET ηi n1 (d b) (Y1 b) (Y2 b) (τ b))
      =O[L] fun b => s b ^ 2 :=
    ((((o_mul hd hdY (by norm_num : 1 + 1 = 2)).const_mul_left (ηi * n1 * (1 - n1))).add
      ((o_pow hdY 2).const_mul_left (n1 * (1 - n1) * (1 - ηi) / 2))).add hτ).congr_left
        fun b => by unfold TwoSectorWelfare.ET; ring
  have hnY := (hY1.const_mul_left n1).add (hY2.const_mul_left (1 - n1))
  have hnq := (hq1.const_mul_left n1).add (hq2.const_mul_left (1 - n1))
  have hsec : ∀ {q Y V : B → ℝ}, q =O[L] (fun b => s b ^ 1) → Y =O[L] (fun b => s b ^ 1) →
      V =O[L] (fun b => s b ^ 2) → (fun b => TwoSectorWelfare.Rsec ω θi (Phi b) (q b) (Y b)
        (V b)) =O[L] fun b => s b ^ 3 := fun {q} {Y} {V} hq hY hV =>
    ((((o_mul hPhi hV (by norm_num : 1 + 2 = 3)).const_mul_left ((1 - θi) / 2)).sub
      ((o_mul hY hV (by norm_num : 1 + 2 = 3)).const_mul_left ((1 + ω) * (1 - θi) / 2))).add
      ((o_weaken hs (by norm_num : 3 ≤ 4) (o_mul hV hV (by norm_num : 2 + 2 = 4))).const_mul_left
        ((1 + ω) * (1 - θi) ^ 2 / 8)) |>.add
      ((o_mul hq hV (by norm_num : 1 + 2 = 3)).const_mul_left (ω * (1 - θi) / 2))).congr_left
        fun b => by unfold TwoSectorWelfare.Rsec; ring
  refine (((((o_mul hPhi hET (by norm_num : 1 + 2 = 3)).neg_left.add
    ((o_mul hnY hET (by norm_num : 1 + 2 = 3)).const_mul_left (1 + ω))).add
    ((o_weaken hs (by norm_num : 3 ≤ 4) (o_mul hET hET (by norm_num : 2 + 2 = 4))).const_mul_left
      ((1 + ω) / 2))).sub ((o_mul hnq hET (by norm_num : 1 + 2 = 3)).const_mul_left ω)).sub
    (((hsec hq1 hY1 hV1).const_mul_left n1).add
      ((hsec hq2 hY2 hV2).const_mul_left (1 - n1)))).congr_left fun b => ?_
  unfold TwoSectorWelfare.R610
  ring

/-- Woodford (2003), (4.24)/(E.31): the quadratic form of Proposition 6.10 at the efficient
steady state (`x* = 0`),
`(σ⁻¹ + ω)(Ŷ − Ŷⁿ)² + n₁n₂(η⁻¹ + ω)((Ŷ₂ − Ŷ₁) − (Ŷ₂ⁿ − Ŷ₁ⁿ))² + (θ⁻¹ + ω)(n₁V₁ + n₂V₂)`. -/
noncomputable def loss610 (σi ω θi ηi n1 g q1 q2 d Y Y1 Y2 V1 V2 : ℝ) : ℝ :=
  (σi + ω) * (Y - TwoSectorWelfare.natY σi ω n1 g q1 q2) ^ 2 +
    n1 * (1 - n1) * (ηi + ω) * ((Y2 - Y1) - TwoSectorWelfare.natD ηi ω d q1 q2) ^ 2 +
    (θi + ω) * (n1 * V1 + (1 - n1) * V2)

/-- Woodford (2003), §4.3, p. 436: the ACTUAL period utility of the two-sector model,
`u(Y; ξ) − [n₁ ∫ v(y₁(i); ξ₁)di + n₂ ∫ v(y₂(i); ξ₂)di]`, `Y` the two-sector aggregate. -/
noncomputable def periodU2 (u v : ℝ × Ξ → ℝ) (n1 η θ Ybar : ℝ) (w1 w2 : ι → ℝ) (f1 f2 : ℝ)
    (yh1 yh2 : ι → ℝ) (xu xv1 xv2 : Ξ) : ℝ :=
  u (Ybar * Real.exp (logY2 n1 η Ybar f1 f2 (logYidx w1 θ yh1) (logYidx w2 θ yh2)), xu) -
    (n1 * ∑ i, w1 i * v (Ybar * Real.exp (yh1 i), xv1) +
      (1 - n1) * ∑ i, w2 i * v (Ybar * Real.exp (yh2 i), xv2))

/-- Woodford (2003), (E.29)–(E.31): the policy-independent terms of the actual expansion
(functions of the disturbances only). -/
noncomputable def tip2 (u v : ℝ × Ξ → ℝ) (n1 Ybar : ℝ) (xu xv1 xv2 : Ξ) : ℝ :=
  (u (Ybar, 0) + dXi u (Ybar, 0) xu + dXiXi u (Ybar, 0) xu / 2) -
    (n1 * (v (Ybar, 0) + dXi v (Ybar, 0) xv1 + dXiXi v (Ybar, 0) xv1 / 2) +
      (1 - n1) * (v (Ybar, 0) + dXi v (Ybar, 0) xv2 + dXiXi v (Ybar, 0) xv2 / 2))

/-- Woodford (2003), **Proposition 6.10**, (4.24)/(E.26), pp. 436, 703–705, from the ACTUAL
utility (Layer B, period form): `u, v` are `C³` on `ℝ × Ξ` at the efficient steady state
(`v_y = u_c`, `σ⁻¹ = −Ȳu_cc/u_c`, `ω = Ȳv_yy/v_y`); `g`, `q_j` are the composite disturbances
(`hg`, `hq1`, `hq2`); the aggregate is the exact two-sector CES aggregate of the exact sectoral
Dixit–Stiglitz indices, with normalised preference shocks (`hnorm`). Along any family with
`ŷ_j(i), φ̂_j, ξ = O(s)`, the actual period utility is
`t.i.p. + Ȳu_c[tip610 − ½ loss610] + O(s³)` where `loss610` is (E.31) at the efficient point,
evaluated at the exact `Ŷ`, `Ŷ_j`, `var_iʲ ŷ`. The aggregation remainders (CES atoms of both
sectors, the two-sector atom `aggAtom`) are all `O(s³)`. -/
theorem prop610_actual (hs : Tendsto s L (𝓝 0)) {n1 η θ : ℝ} (hn0 : 0 < n1) (hn1 : n1 < 1)
    (hη : 0 < η) (hη1 : η ≠ 1) (hθ : θ ≠ 1) {w1 w2 : ι → ℝ} (hw10 : ∀ i, 0 ≤ w1 i)
    (hw11 : ∑ i, w1 i = 1) (hw20 : ∀ i, 0 ≤ w2 i) (hw21 : ∑ i, w2 i = 1)
    {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v) {Ybar σi ω : ℝ}
    (hY : 0 < Ybar) (hσω : σi + ω ≠ 0) (hηω : η⁻¹ + ω ≠ 0)
    (hucc : dYY u (Ybar, 0) = -(σi * dY u (Ybar, 0) / Ybar))
    (hvy : dY v (Ybar, 0) = dY u (Ybar, 0))
    (hvyy : dYY v (Ybar, 0) = ω * dY v (Ybar, 0) / Ybar)
    {yh1 yh2 : B → ι → ℝ} {f1 f2 g q1 q2 : B → ℝ} {xu xv1 xv2 : B → Ξ}
    (hnorm : ∀ b, n1 * Real.exp (f1 b) + (1 - n1) * Real.exp (f2 b) = 1)
    (hg : ∀ b, dYXi u (Ybar, 0) (xu b) = σi * dY u (Ybar, 0) * g b)
    (hq1 : ∀ b, dYXi v (Ybar, 0) (xv1 b) = -(ω * dY v (Ybar, 0) * q1 b))
    (hq2 : ∀ b, dYXi v (Ybar, 0) (xv2 b) = -(ω * dY v (Ybar, 0) * q2 b))
    (hyh1 : yh1 =O[L] fun b => s b ^ 1) (hyh2 : yh2 =O[L] fun b => s b ^ 1)
    (hf1 : f1 =O[L] fun b => s b ^ 1) (hf2 : f2 =O[L] fun b => s b ^ 1)
    (hgO : g =O[L] fun b => s b ^ 1) (hq1O : q1 =O[L] fun b => s b ^ 1)
    (hq2O : q2 =O[L] fun b => s b ^ 1) (hxu : xu =O[L] fun b => s b ^ 1)
    (hxv1 : xv1 =O[L] fun b => s b ^ 1) (hxv2 : xv2 =O[L] fun b => s b ^ 1) :
    (fun b => periodU2 u v n1 η θ Ybar w1 w2 (f1 b) (f2 b) (yh1 b) (yh2 b) (xu b) (xv1 b)
        (xv2 b) -
      (tip2 u v n1 Ybar (xu b) (xv1 b) (xv2 b) + Ybar * dY u (Ybar, 0) *
        (TwoSectorWelfare.tip610 σi ω η⁻¹ n1 0 (g b) (q1 b) (q2 b) (f2 b - f1 b)
            (tauAgg η⁻¹ n1 (f1 b) (f2 b)) -
          loss610 σi ω θ⁻¹ η⁻¹ n1 (g b) (q1 b) (q2 b) (f2 b - f1 b)
            (logY2 n1 η Ybar (f1 b) (f2 b) (logYidx w1 θ (yh1 b)) (logYidx w2 θ (yh2 b)))
            (logYidx w1 θ (yh1 b)) (logYidx w2 θ (yh2 b)) (crossVar w1 (yh1 b))
            (crossVar w2 (yh2 b)) / 2))) =O[L] fun b => s b ^ 3 := by
  set K := Ybar * dY u (Ybar, 0) with hK
  set Y1h := fun b => logYidx w1 θ (yh1 b) with hY1h
  set Y2h := fun b => logYidx w2 θ (yh2 b) with hY2h
  set V1 := fun b => crossVar w1 (yh1 b) with hV1
  set V2 := fun b => crossVar w2 (yh2 b) with hV2
  set τ' := fun b => tauAgg η⁻¹ n1 (f1 b) (f2 b) with hτ'
  set Yp := fun b => n1 * Y1h b + (1 - n1) * Y2h b +
    TwoSectorWelfare.ET η⁻¹ n1 (f2 b - f1 b) (Y1h b) (Y2h b) (τ' b) with hYp
  set Yh := fun b => logY2 n1 η Ybar (f1 b) (f2 b) (Y1h b) (Y2h b) with hYh
  have hY1O : Y1h =O[L] fun b => s b ^ 1 := logYidx_o hs hw10 hw11 hθ hyh1
  have hY2O : Y2h =O[L] fun b => s b ^ 1 := logYidx_o hs hw20 hw21 hθ hyh2
  have hV1O : V1 =O[L] fun b => s b ^ 2 := crossVar_o hw10 hw11 hyh1
  have hV2O : V2 =O[L] fun b => s b ^ 2 := crossVar_o hw20 hw21 hyh2
  have hd : (fun b => f2 b - f1 b) =O[L] fun b => s b ^ 1 := hf2.sub hf1
  have hτO : τ' =O[L] fun b => s b ^ 2 :=
    (((S_o hs hf1 hf2 hnorm).const_mul_left ((1 - η⁻¹)⁻¹ * η⁻¹)).add
      ((o_pow hd 2).const_mul_left (n1 * (1 - n1) * (1 - η⁻¹)⁻¹ * (η⁻¹) ^ 2 / 2))).congr_left
        fun b => by simp only [hτ', tauAgg]
  have hdY := hY2O.sub hY1O
  have hET : (fun b => TwoSectorWelfare.ET η⁻¹ n1 (f2 b - f1 b) (Y1h b) (Y2h b) (τ' b))
      =O[L] fun b => s b ^ 2 :=
    ((((o_mul hd hdY (by norm_num : 1 + 1 = 2)).const_mul_left (η⁻¹ * n1 * (1 - n1))).add
      ((o_pow hdY 2).const_mul_left (n1 * (1 - n1) * (1 - η⁻¹) / 2))).add hτO).congr_left
        fun b => by unfold TwoSectorWelfare.ET; ring
  have hYpO : Yp =O[L] fun b => s b ^ 1 :=
    ((hY1O.const_mul_left n1).add (hY2O.const_mul_left (1 - n1))).add
      (o_weaken hs (by norm_num : 1 ≤ 2) hET)
  have hA := aggAtom_o hs hn0 hn1 hη hη1 hY hf1 hf2 hY1O hY2O (Ybar := Ybar)
  have hA' : (fun b => Yh b - Yp b) =O[L] fun b => s b ^ 3 := hA
  have hYhO : Yh =O[L] fun b => s b ^ 1 :=
    ((o_weaken hs (by norm_num : 1 ≤ 3) hA').add hYpO).congr_left fun b => by ring
  -- the Taylor steps
  have hu1 := uTaylor_family_exp hu Ybar hs hYhO hxu
  have hvs1 := IsBigO.fun_sum (s := Finset.univ) fun i _ =>
    (uTaylor_family_exp hv Ybar hs (coord_o hyh1 i) hxv1).const_mul_left (w1 i)
  have hvs2 := IsBigO.fun_sum (s := Finset.univ) fun i _ =>
    (uTaylor_family_exp hv Ybar hs (coord_o hyh2 i) hxv2).const_mul_left (w2 i)
  -- the cubic pieces
  have hRu := Ru_o hs σi hgO hYhO (expRem_o hs hYhO)
  have hTu : (fun b => (Yh b - Yp b) * (1 + (1 - σi) / 2 * (Yh b + Yp b) + σi * g b))
      =O[L] fun b => s b ^ 3 :=
    (o_mul hA' (((isBigO_const_const (1 : ℝ) one_ne_zero L).add
      ((o_weaken hs (by norm_num : 0 ≤ 1) (hYhO.add hYpO)).const_mul_left ((1 - σi) / 2))).add
      ((o_weaken hs (by norm_num : 0 ≤ 1) hgO).const_mul_left σi) |>.congr_right
        fun b => by ring) (by norm_num : 3 + 0 = 3))
  have hRv1 : (fun b => ∑ i, w1 i * Prop61.Rv 0 ω (q1 b) (yh1 b i) (expRem (yh1 b i)))
      =O[L] fun b => s b ^ 3 :=
    IsBigO.fun_sum (s := Finset.univ) fun i _ =>
      (Rv0_o hs ω hq1O (coord_o hyh1 i) (expRem_o hs (coord_o hyh1 i))).const_mul_left (w1 i)
  have hRv2 : (fun b => ∑ i, w2 i * Prop61.Rv 0 ω (q2 b) (yh2 b i) (expRem (yh2 b i)))
      =O[L] fun b => s b ^ 3 :=
    IsBigO.fun_sum (s := Finset.univ) fun i _ =>
      (Rv0_o hs ω hq2O (coord_o hyh2 i) (expRem_o hs (coord_o hyh2 i))).const_mul_left (w2 i)
  have hm1 : (fun b => TwoSectorWelfare.meanE28 θ⁻¹ (Y1h b) (V1 b)) =O[L] fun b => s b ^ 1 :=
    (hY1O.sub ((o_weaken hs (by norm_num : 1 ≤ 2) hV1O).const_mul_left
      ((1 - θ⁻¹) / 2))).congr_left
      fun b => by unfold TwoSectorWelfare.meanE28; ring
  have hm2 : (fun b => TwoSectorWelfare.meanE28 θ⁻¹ (Y2h b) (V2 b)) =O[L] fun b => s b ^ 1 :=
    (hY2O.sub ((o_weaken hs (by norm_num : 1 ≤ 2) hV2O).const_mul_left
      ((1 - θ⁻¹) / 2))).congr_left
      fun b => by unfold TwoSectorWelfare.meanE28; ring
  have hvA1 := vAtom_o hs ω hq1O hm1 (cesAtom_o hs hw10 hw11 hθ hyh1) hRv1
  have hvA2 := vAtom_o hs ω hq2O hm2 (cesAtom_o hs hw20 hw21 hθ hyh2) hRv2
  have hzero : (fun _ : B => (0 : ℝ)) =O[L] fun b => s b ^ 1 := isBigO_zero _ _
  have hR610 := R610_o hs ω θ⁻¹ η⁻¹ n1 hzero hq1O hq2O hY1O hY2O hV1O hV2O hd hτO
  have hnat : (fun b => TwoSectorWelfare.natY σi ω n1 (g b) (q1 b) (q2 b))
      =O[L] fun b => s b ^ 1 :=
    (((hgO.const_mul_left σi).add (((hq1O.const_mul_left n1).add
      (hq2O.const_mul_left (1 - n1))).const_mul_left ω)).const_mul_left (σi + ω)⁻¹).congr_left
        fun b => by unfold TwoSectorWelfare.natY; ring
  have hLd : (fun b => (σi + ω) / 2 * ((Yh b - Yp b) *
      ((Yh b - TwoSectorWelfare.natY σi ω n1 (g b) (q1 b) (q2 b)) +
        (Yp b - TwoSectorWelfare.natY σi ω n1 (g b) (q1 b) (q2 b)))))
      =O[L] fun b => s b ^ 3 :=
    (o_weaken hs (by norm_num : 3 ≤ 4) (o_mul hA' ((hYhO.sub hnat).add (hYpO.sub hnat))
      (by norm_num : 3 + 1 = 4))).const_mul_left _
  refine ((((hu1.sub ((hvs1.const_mul_left n1).add (hvs2.const_mul_left (1 - n1)))).add
    ((((((hRu.add hTu).sub (hvA1.const_mul_left n1)).sub (hvA2.const_mul_left (1 - n1))).add
      hR610).add hLd).const_mul_left K)))).congr_left fun b => ?_
  -- the exact identity at `b`
  have key := TwoSectorWelfare.prop_6_10_layerA (σi := σi) (ω := ω) (θi := θ⁻¹) (ηi := η⁻¹)
    (n1 := n1) hσω hηω (Y := Yp b) (Y1 := Y1h b) (Y2 := Y2h b) (V1 := V1 b) (V2 := V2 b)
    (g := g b) (q1 := q1 b) (q2 := q2 b) (d := f2 b - f1 b) (τ := τ' b) (Phi := 0) rfl
  have eU := Prop61.uTaylor_eq_of_coeffs (ubar := u (Ybar, 0)) (Lu := dXi u (Ybar, 0) (xu b))
    (Qu := dXiXi u (Ybar, 0) (xu b)) (Y := Yh b) (r := expRem (Yh b)) hucc (hg b)
  have eV : ∀ (wj : ι → ℝ), ∑ i, wj i = 1 → ∀ (yj : ι → ℝ) (xvj : Ξ) (qj : ℝ),
      dYXi v (Ybar, 0) xvj = -(ω * dY v (Ybar, 0) * qj) →
      ∑ i, wj i * Prop61.uTaylor (v (Ybar, 0)) (dY v (Ybar, 0)) (dYY v (Ybar, 0))
        (dXi v (Ybar, 0) xvj) (dYXi v (Ybar, 0) xvj) (dXiXi v (Ybar, 0) xvj)
        (Ybar * (yj i + yj i ^ 2 / 2 + expRem (yj i))) =
      (v (Ybar, 0) + dXi v (Ybar, 0) xvj + dXiXi v (Ybar, 0) xvj / 2) +
      K * (TwoSectorWelfare.TvSec ω 0 qj
          (TwoSectorWelfare.meanE28 θ⁻¹ (logYidx wj θ yj) (crossVar wj yj)) (crossVar wj yj) +
        vAtom ω qj (TwoSectorWelfare.meanE28 θ⁻¹ (logYidx wj θ yj) (crossVar wj yj))
          (Links.CES.cesAtom wj θ yj)
          (∑ i, wj i * Prop61.Rv 0 ω qj (yj i) (expRem (yj i)))) := by
    intro wj hwj yj xvj qj hqj
    have hper : ∀ i, wj i * Prop61.uTaylor (v (Ybar, 0)) (dY v (Ybar, 0)) (dYY v (Ybar, 0))
        (dXi v (Ybar, 0) xvj) (dYXi v (Ybar, 0) xvj) (dXiXi v (Ybar, 0) xvj)
        (Ybar * (yj i + yj i ^ 2 / 2 + expRem (yj i))) =
        (v (Ybar, 0) + dXi v (Ybar, 0) xvj + dXiXi v (Ybar, 0) xvj / 2) * wj i +
          K * (wj i * Prop61.Tv 0 ω qj (yj i) +
            wj i * Prop61.Rv 0 ω qj (yj i) (expRem (yj i))) := by
      intro i
      rw [Prop61.uTaylor, hvyy, hqj, hvy]
      unfold Prop61.Tv Prop61.Rv
      field_simp
      ring
    rw [Finset.sum_congr rfl fun i _ => hper i]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hwj]
    rw [TwoSectorWelfare.sum_Tv hwj, Links.CES.ces_relation wj θ yj]
    simp only [vAtom, TwoSectorWelfare.TvSec, TwoSectorWelfare.meanE28, logYidx]
    ring
  have e1 := eV w1 hw11 (yh1 b) (xv1 b) (q1 b) (hq1 b)
  have e2 := eV w2 hw21 (yh2 b) (xv2 b) (q2 b) (hq2 b)
  have hsum : ∀ (wj : ι → ℝ) (yj : ι → ℝ) (xvj : Ξ), ∑ i, wj i * (v (Ybar * Real.exp (yj i), xvj) -
      Prop61.uTaylor (v (Ybar, 0)) (dY v (Ybar, 0)) (dYY v (Ybar, 0)) (dXi v (Ybar, 0) xvj)
        (dYXi v (Ybar, 0) xvj) (dXiXi v (Ybar, 0) xvj)
        (Ybar * (yj i + yj i ^ 2 / 2 + expRem (yj i)))) =
      ∑ i, wj i * v (Ybar * Real.exp (yj i), xvj) -
        ∑ i, wj i * Prop61.uTaylor (v (Ybar, 0)) (dY v (Ybar, 0)) (dYY v (Ybar, 0))
          (dXi v (Ybar, 0) xvj) (dYXi v (Ybar, 0) xvj) (dXiXi v (Ybar, 0) xvj)
          (Ybar * (yj i + yj i ^ 2 / 2 + expRem (yj i))) := fun wj yj xvj => by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [hsum]
  rw [e1, e2, eU]
  simp only [periodU2, tip2, loss610, TwoSectorWelfare.TvSec, Prop61.Tu, Prop61.xStarLin,
    hYp, hYh, hY1h, hY2h, hV1, hV2, hτ'] at key ⊢
  linear_combination (-K) * key

/-- Woodford (2003), (E.31)/(4.24): the quadratic form of Proposition 6.10 along a family with a
first-order solution (`Ŷ, Ŷ_j, g, q_j, d = ε × first order + O(ε²)`,
`V_j = ε² V_j¹ + O(ε³)`) is `ε²` times its value at the first-order solution, up to `O(ε³)`. -/
theorem loss610_first_order (hs : Tendsto s L (𝓝 0)) (σi ω θi ηi n1 : ℝ)
    {g q1 q2 d Y Y1 Y2 V1 V2 gf q1f q2f df Yf Y1f Y2f V1f V2f : B → ℝ}
    (hg : (fun b => g b - s b * gf b) =O[L] fun b => s b ^ 2)
    (hq1 : (fun b => q1 b - s b * q1f b) =O[L] fun b => s b ^ 2)
    (hq2 : (fun b => q2 b - s b * q2f b) =O[L] fun b => s b ^ 2)
    (hd : (fun b => d b - s b * df b) =O[L] fun b => s b ^ 2)
    (hY : (fun b => Y b - s b * Yf b) =O[L] fun b => s b ^ 2)
    (hY1 : (fun b => Y1 b - s b * Y1f b) =O[L] fun b => s b ^ 2)
    (hY2 : (fun b => Y2 b - s b * Y2f b) =O[L] fun b => s b ^ 2)
    (hV1 : (fun b => V1 b - s b ^ 2 * V1f b) =O[L] fun b => s b ^ 3)
    (hV2 : (fun b => V2 b - s b ^ 2 * V2f b) =O[L] fun b => s b ^ 3)
    (bg : gf =O[L] fun _ => (1 : ℝ)) (bq1 : q1f =O[L] fun _ => (1 : ℝ))
    (bq2 : q2f =O[L] fun _ => (1 : ℝ)) (bd : df =O[L] fun _ => (1 : ℝ))
    (bY : Yf =O[L] fun _ => (1 : ℝ)) (bY1 : Y1f =O[L] fun _ => (1 : ℝ))
    (bY2 : Y2f =O[L] fun _ => (1 : ℝ)) :
    (fun b => loss610 σi ω θi ηi n1 (g b) (q1 b) (q2 b) (d b) (Y b) (Y1 b) (Y2 b) (V1 b) (V2 b) -
      s b ^ 2 * loss610 σi ω θi ηi n1 (gf b) (q1f b) (q2f b) (df b) (Yf b) (Y1f b) (Y2f b)
        (V1f b) (V2f b)) =O[L] fun b => s b ^ 3 := by
  set a1 := σi / (σi + ω)
  set a2 := ω * n1 / (σi + ω)
  set a3 := ω * (1 - n1) / (σi + ω)
  set c1 := ηi / (ηi + ω)
  set c2 := ω / (ηi + ω)
  have hG1 : (fun b => (Y b - (a1 * g b + a2 * q1 b + a3 * q2 b)) -
      s b * (Yf b - (a1 * gf b + a2 * q1f b + a3 * q2f b))) =O[L] fun b => s b ^ 2 :=
    (hY.sub (((hg.const_mul_left a1).add (hq1.const_mul_left a2)).add
      (hq2.const_mul_left a3))).congr_left fun b => by ring
  have bG1 : (fun b => Yf b - (a1 * gf b + a2 * q1f b + a3 * q2f b)) =O[L] fun _ => (1 : ℝ) :=
    bY.sub (((bg.const_mul_left a1).add (bq1.const_mul_left a2)).add (bq2.const_mul_left a3))
  have hG2 : (fun b => ((Y2 b - Y1 b) - (c1 * d b + c2 * (q2 b - q1 b))) -
      s b * ((Y2f b - Y1f b) - (c1 * df b + c2 * (q2f b - q1f b)))) =O[L] fun b => s b ^ 2 :=
    ((hY2.sub hY1).sub ((hd.const_mul_left c1).add ((hq2.sub hq1).const_mul_left c2))).congr_left
      fun b => by ring
  have bG2 : (fun b => (Y2f b - Y1f b) - (c1 * df b + c2 * (q2f b - q1f b)))
      =O[L] fun _ => (1 : ℝ) :=
    (bY2.sub bY1).sub ((bd.const_mul_left c1).add ((bq2.sub bq1).const_mul_left c2))
  refine ((((sq_sub_o hs hG1 bG1).const_mul_left (σi + ω)).add
    ((sq_sub_o hs hG2 bG2).const_mul_left (n1 * (1 - n1) * (ηi + ω)))).add
    (((hV1.const_mul_left n1).add (hV2.const_mul_left (1 - n1))).const_mul_left
      (θi + ω))).congr_left fun b => ?_
  simp only [loss610, TwoSectorWelfare.natY, TwoSectorWelfare.natD, a1, a2, a3, c1, c2]
  ring

/-- Woodford (2003), **Proposition 6.10**, (4.24)/(E.26), LAYER B: under the hypotheses of
`prop610_actual`, if the family has a first-order solution (each first-order variable
`= ε × (bounded first-order value) + O(ε²)`, sectoral cross-sections `ŷ_j = εŷ_j¹ + O(ε²)`), then
`W(ε) = t.i.p.(ε) − (ε²/2)·Ȳu_c·loss610(first-order solution) + O(ε³)`. -/
theorem prop610_layerB (hs : Tendsto s L (𝓝 0)) {n1 η θ : ℝ} (hn0 : 0 < n1) (hn1 : n1 < 1)
    (hη : 0 < η) (hη1 : η ≠ 1) (hθ : θ ≠ 1) {w1 w2 : ι → ℝ} (hw10 : ∀ i, 0 ≤ w1 i)
    (hw11 : ∑ i, w1 i = 1) (hw20 : ∀ i, 0 ≤ w2 i) (hw21 : ∑ i, w2 i = 1)
    {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v) {Ybar σi ω : ℝ}
    (hY : 0 < Ybar) (hσω : σi + ω ≠ 0) (hηω : η⁻¹ + ω ≠ 0)
    (hucc : dYY u (Ybar, 0) = -(σi * dY u (Ybar, 0) / Ybar))
    (hvy : dY v (Ybar, 0) = dY u (Ybar, 0))
    (hvyy : dYY v (Ybar, 0) = ω * dY v (Ybar, 0) / Ybar)
    {yh1 yh2 y1f y2f : B → ι → ℝ} {f1 f2 g q1 q2 gf q1f q2f df Yf Y1f Y2f : B → ℝ}
    {xu xv1 xv2 : B → Ξ}
    (hnorm : ∀ b, n1 * Real.exp (f1 b) + (1 - n1) * Real.exp (f2 b) = 1)
    (hg : ∀ b, dYXi u (Ybar, 0) (xu b) = σi * dY u (Ybar, 0) * g b)
    (hq1 : ∀ b, dYXi v (Ybar, 0) (xv1 b) = -(ω * dY v (Ybar, 0) * q1 b))
    (hq2 : ∀ b, dYXi v (Ybar, 0) (xv2 b) = -(ω * dY v (Ybar, 0) * q2 b))
    (hyh1 : yh1 =O[L] fun b => s b ^ 1) (hyh2 : yh2 =O[L] fun b => s b ^ 1)
    (hf1 : f1 =O[L] fun b => s b ^ 1) (hf2 : f2 =O[L] fun b => s b ^ 1)
    (hxu : xu =O[L] fun b => s b ^ 1)
    (hxv1 : xv1 =O[L] fun b => s b ^ 1) (hxv2 : xv2 =O[L] fun b => s b ^ 1)
    (bg : gf =O[L] fun _ => (1 : ℝ)) (bq1 : q1f =O[L] fun _ => (1 : ℝ))
    (bq2 : q2f =O[L] fun _ => (1 : ℝ)) (bd : df =O[L] fun _ => (1 : ℝ))
    (bY : Yf =O[L] fun _ => (1 : ℝ)) (bY1 : Y1f =O[L] fun _ => (1 : ℝ))
    (bY2 : Y2f =O[L] fun _ => (1 : ℝ)) (by1 : y1f =O[L] fun _ => (1 : ℝ))
    (by2 : y2f =O[L] fun _ => (1 : ℝ))
    (hgd : (fun b => g b - s b * gf b) =O[L] fun b => s b ^ 2)
    (hq1d : (fun b => q1 b - s b * q1f b) =O[L] fun b => s b ^ 2)
    (hq2d : (fun b => q2 b - s b * q2f b) =O[L] fun b => s b ^ 2)
    (hdd : (fun b => (f2 b - f1 b) - s b * df b) =O[L] fun b => s b ^ 2)
    (hYd : (fun b => logY2 n1 η Ybar (f1 b) (f2 b) (logYidx w1 θ (yh1 b))
      (logYidx w2 θ (yh2 b)) - s b * Yf b) =O[L] fun b => s b ^ 2)
    (hY1d : (fun b => logYidx w1 θ (yh1 b) - s b * Y1f b) =O[L] fun b => s b ^ 2)
    (hY2d : (fun b => logYidx w2 θ (yh2 b) - s b * Y2f b) =O[L] fun b => s b ^ 2)
    (hy1d : (fun b => yh1 b - s b • y1f b) =O[L] fun b => s b ^ 2)
    (hy2d : (fun b => yh2 b - s b • y2f b) =O[L] fun b => s b ^ 2) :
    (fun b => periodU2 u v n1 η θ Ybar w1 w2 (f1 b) (f2 b) (yh1 b) (yh2 b) (xu b) (xv1 b)
        (xv2 b) -
      ((tip2 u v n1 Ybar (xu b) (xv1 b) (xv2 b) + Ybar * dY u (Ybar, 0) *
        TwoSectorWelfare.tip610 σi ω η⁻¹ n1 0 (g b) (q1 b) (q2 b) (f2 b - f1 b)
          (tauAgg η⁻¹ n1 (f1 b) (f2 b))) -
        s b ^ 2 / 2 * (Ybar * dY u (Ybar, 0) * loss610 σi ω θ⁻¹ η⁻¹ n1 (gf b) (q1f b) (q2f b)
          (df b) (Yf b) (Y1f b) (Y2f b) (crossVar w1 (y1f b)) (crossVar w2 (y2f b)))))
      =O[L] fun b => s b ^ 3 := by
  have fo : ∀ (x x1 : B → ℝ), (fun b => x b - s b * x1 b) =O[L] (fun b => s b ^ 2) →
      x1 =O[L] (fun _ => (1 : ℝ)) → x =O[L] fun b => s b ^ 1 := fun x x1 hd h1 =>
    ((o_weaken hs (by norm_num : 1 ≤ 2) hd).add
      (((isBigO_refl s L).mul h1).congr_right fun b => by ring)).congr_left fun b => by ring
  have hW := prop610_actual hs hn0 hn1 hη hη1 hθ hw10 hw11 hw20 hw21 hu hv hY hσω hηω hucc hvy
    hvyy hnorm hg hq1 hq2 hyh1 hyh2 hf1 hf2 (fo g gf hgd bg) (fo q1 q1f hq1d bq1)
    (fo q2 q2f hq2d bq2) hxu hxv1 hxv2
  have hL := loss610_first_order hs σi ω θ⁻¹ η⁻¹ n1 hgd hq1d hq2d hdd hYd hY1d hY2d
    (crossVar_first_order hs hw10 hw11 hy1d by1) (crossVar_first_order hs hw20 hw21 hy2d by2)
    bg bq1 bq2 bd bY bY1 bY2
  exact bridge_first_order (hW.congr_left fun b => by ring) hL

/-- Woodford (2003), (4.10), (4.25), (4.29) (discounted quadratic losses with a first-order
solution): for a loss `∑_k c_k z_k²` whose arguments are `z_k = εz_k¹ + O(ε²)` uniformly in
the date (first-order sequences bounded),
`∑βᵗ∑_k c_k z_{k,t}² = ε²∑βᵗ∑_k c_k (z¹_{k,t})² + O(ε³)`. -/
theorem tsum_sq_first_order {n : ℕ} (c : Fin n → ℝ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (he : Tendsto e l (𝓝 0)) {z : Fin n → A → ℕ → ℝ} {z1 : Fin n → ℕ → ℝ}
    (h1 : ∀ k, Sequences.Bdd (z1 k))
    (hd : ∀ k, (fun p : A × ℕ => z k p.1 p.2 - e p.1 * z1 k p.2) =O[l ×ˢ ⊤]
      fun p => e p.1 ^ 2) :
    (fun a => ∑' t, β ^ t * ∑ k, c k * z k a t ^ 2 -
      e a ^ 2 * ∑' t, β ^ t * ∑ k, c k * z1 k t ^ 2) =O[l] fun a => e a ^ 3 := by
  have hs := tendsto_amp (J := ℕ) he
  have b1 : ∀ k, (fun p : A × ℕ => z1 k p.2) =O[l ×ˢ ⊤] fun _ => (1 : ℝ) := fun k => by
    obtain ⟨M, hM⟩ := h1 k
    exact IsBigO.of_bound M (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, norm_one, mul_one]; exact hM _)
  have hO : ∀ k, (fun p : A × ℕ => z k p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 := fun k =>
    ((o_weaken hs (by norm_num : 1 ≤ 2) (hd k)).add
      (((isBigO_refl (fun p : A × ℕ => e p.1) _).mul (b1 k)).congr_right fun p => by
        ring)).congr_left fun p => by ring
  have hD : (fun p : A × ℕ => ∑ k, c k * z k p.1 p.2 ^ 2 - e p.1 ^ 2 * ∑ k, c k * z1 k p.2 ^ 2)
      =O[l ×ˢ ⊤] fun p => e p.1 ^ 3 :=
    (IsBigO.fun_sum (s := Finset.univ) fun k _ =>
      (sq_sub_o hs (hd k) (b1 k)).const_mul_left (c k)).congr_left fun p => by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
  have hL1 : Sequences.Bdd (fun t => ∑ k, c k * z1 k t ^ 2) := by
    choose M hM using h1
    refine ⟨∑ k, |c k| * M k ^ 2, fun t => ?_⟩
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hM k t) 2) (abs_nonneg _)
  have bL := seq_bdd_of_o (f := fun a t => ∑ k, c k * z k a t ^ 2) he
    (IsBigO.fun_sum (s := Finset.univ) fun k _ => (o_pow (hO k) 2).const_mul_left (c k))
  have hev : ∀ᶠ a in l, ∑' t, β ^ t * (∑ k, c k * z k a t ^ 2 -
      e a ^ 2 * ∑ k, c k * z1 k t ^ 2) =
      ∑' t, β ^ t * ∑ k, c k * z k a t ^ 2 - e a ^ 2 * ∑' t, β ^ t * ∑ k, c k * z1 k t ^ 2 := by
    filter_upwards [bL] with a ha
    have h1' := (ha.summable hβ0 hβ1).hasSum
    have h2' := ((hL1.summable hβ0 hβ1).hasSum).mul_left (e a ^ 2)
    exact ((h1'.sub h2').congr_fun fun t => by ring).tsum_eq
  exact (tsum_o hβ0 hβ1 hD).congr' hev (Eventually.of_forall fun _ => rfl)

/-- Woodford (2003), **Proposition 6.11**, (4.25)/(E.32), p. 437, LAYER B along a path: if the
period utility has the expansion of `prop610_actual` uniformly in the date
(`W = τ − (K/2)[(σ⁻¹+ω)(x − x*)² + n₁n₂η(1+ωη)(p̂_R − p̂_Rⁿ)² + θ(1+ωθ)(n₁Δ₁ + n₂Δ₂)] + O(ε³)`,
which is (E.31) with `V_j = θ²Δ_j` and `Ŷ₂ − Ŷ₁ − (Ŷ₂ⁿ − Ŷ₁ⁿ) = −η(p̂_R − p̂_Rⁿ)`, see
`TwoSectorWelfare.prop_6_10`), the sectoral dispersions follow the exact Calvo laws, the
first-order variables are uniformly `O(ε)`, `Δ_j = O(ε²)` and `π̄_j − π_j = O(ε²)`, then
`∑βᵗW_t = −Ω∑βᵗL_t + t.i.p. + O(ε³)` with `L` the loss (4.25) on the actual path
(`TwoSectorWelfare.prop_6_11` supplies the identity, this theorem the order of its remainder). -/
theorem prop611_layerB {K σi ω θ η n1 β α1 α2 xs : ℝ} (ha10 : 0 < α1) (ha11 : α1 < 1)
    (ha20 : 0 < α2) (ha21 : α2 < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hn0 : 0 < n1) (hn1 : n1 < 1)
    (hθ : 0 < θ) (hωθ : 0 < 1 + ω * θ) (hσω : 0 < σi + ω) (he : Tendsto e l (𝓝 0))
    {W τ x gR π1 π2 pb1 pb2 Δ1 Δ2 : A → ℕ → ℝ} {Δ1m Δ2m : A → ℝ}
    (hτ : ∀ a, Sequences.Bdd (τ a))
    (hP : (fun p : A × ℕ => W p.1 p.2 - (τ p.1 p.2 - K / 2 * ((σi + ω) * (x p.1 p.2 - xs) ^ 2 +
      n1 * (1 - n1) * η * (1 + ω * η) * gR p.1 p.2 ^ 2 +
      θ * (1 + ω * θ) * (n1 * Δ1 p.1 p.2 + (1 - n1) * Δ2 p.1 p.2)))) =O[l ×ˢ ⊤]
        fun p => e p.1 ^ 3)
    (hx : (fun p : A × ℕ => x p.1 p.2 - xs) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hgR : (fun p : A × ℕ => gR p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hπ1 : (fun p : A × ℕ => π1 p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hπ2 : (fun p : A × ℕ => π2 p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hΔ1 : (fun p : A × ℕ => Δ1 p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2)
    (hΔ2 : (fun p : A × ℕ => Δ2 p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2)
    (hp1 : (fun p : A × ℕ => pb1 p.1 p.2 - π1 p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2)
    (hp2 : (fun p : A × ℕ => pb2 p.1 p.2 - π2 p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2)
    (h10 : ∀ a, Δ1 a 0 = α1 * Δ1m a + α1 / (1 - α1) * pb1 a 0 ^ 2)
    (h1s : ∀ a t, Δ1 a (t + 1) = α1 * Δ1 a t + α1 / (1 - α1) * pb1 a (t + 1) ^ 2)
    (h20 : ∀ a, Δ2 a 0 = α2 * Δ2m a + α2 / (1 - α2) * pb2 a 0 ^ 2)
    (h2s : ∀ a t, Δ2 a (t + 1) = α2 * Δ2 a t + α2 / (1 - α2) * pb2 a (t + 1) ^ 2) :
    (fun a => ∑' t, β ^ t * W a t -
      (-(K / 2 * (θ * (σi + ω) / TwoSectorWelfare.kappaH n1 (Moments.calvoKappa α1 β ω θ σi)
          (Moments.calvoKappa α2 β ω θ σi))) *
        ∑' t, β ^ t * TwoSectorWelfare.loss425
          (TwoSectorWelfare.wJ n1 (Moments.calvoKappa α1 β ω θ σi)
            (TwoSectorWelfare.kappaH n1 (Moments.calvoKappa α1 β ω θ σi)
              (Moments.calvoKappa α2 β ω θ σi)))
          (TwoSectorWelfare.wJ (1 - n1) (Moments.calvoKappa α2 β ω θ σi)
            (TwoSectorWelfare.kappaH n1 (Moments.calvoKappa α1 β ω θ σi)
              (Moments.calvoKappa α2 β ω θ σi)))
          (TwoSectorWelfare.lamX (TwoSectorWelfare.kappaH n1 (Moments.calvoKappa α1 β ω θ σi)
            (Moments.calvoKappa α2 β ω θ σi)) θ)
          (TwoSectorWelfare.lamR n1 η ω σi (TwoSectorWelfare.kappaH n1
            (Moments.calvoKappa α1 β ω θ σi) (Moments.calvoKappa α2 β ω θ σi)) θ)
          (π1 a t) (π2 a t) (x a t) xs (gR a t) +
        (∑' t, β ^ t * τ a t - K / 2 * (θ * (1 + ω * θ)) *
          (n1 * (α1 * Δ1m a / (1 - α1 * β)) + (1 - n1) * (α2 * Δ2m a / (1 - α2 * β))))))
      =O[l] fun a => e a ^ 3 := by
  have hs := tendsto_amp (J := ℕ) he
  set R : A → ℕ → ℝ := fun a t => W a t - (τ a t - K / 2 * ((σi + ω) * (x a t - xs) ^ 2 +
      n1 * (1 - n1) * η * (1 + ω * η) * gR a t ^ 2 +
      θ * (1 + ω * θ) * (n1 * Δ1 a t + (1 - n1) * Δ2 a t))) with hR
  have pb1O := ((o_weaken hs (by norm_num : 1 ≤ 2) hp1).add hπ1).congr_left fun p => by ring
  have pb2O := ((o_weaken hs (by norm_num : 1 ≤ 2) hp2).add hπ2).congr_left fun p => by ring
  have sq : ∀ {pb π : A → ℕ → ℝ},
      (fun p : A × ℕ => pb p.1 p.2 - π p.1 p.2) =O[l ×ˢ ⊤] (fun p => e p.1 ^ 2) →
      (fun p : A × ℕ => π p.1 p.2) =O[l ×ˢ ⊤] (fun p => e p.1 ^ 1) →
      (fun p : A × ℕ => pb p.1 p.2 ^ 2 - π p.1 p.2 ^ 2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 3 :=
    fun {pb} {π} hd hπ => (o_mul hd ((o_weaken hs (by norm_num : 1 ≤ 2) hd).add
      (hπ.const_mul_left 2)) (by norm_num : 2 + 1 = 3)).congr_left fun p => by ring
  have bR := seq_bdd_of_o (f := R) he hP
  have bx := seq_bdd_of_o (f := fun a t => x a t - xs) he hx
  have bg := seq_bdd_of_o he hgR
  have bπ1 := seq_bdd_of_o he hπ1
  have bπ2 := seq_bdd_of_o he hπ2
  have bp1 := seq_bdd_of_o (f := pb1) he pb1O
  have bp2 := seq_bdd_of_o (f := pb2) he pb2O
  have bΔ1 := seq_bdd_of_o he hΔ1
  have bΔ2 := seq_bdd_of_o he hΔ2
  have hev : ∀ᶠ a in l, ∑' t, β ^ t * W a t -
      (-(K / 2 * (θ * (σi + ω) / TwoSectorWelfare.kappaH n1 (Moments.calvoKappa α1 β ω θ σi)
          (Moments.calvoKappa α2 β ω θ σi))) *
        ∑' t, β ^ t * TwoSectorWelfare.loss425
          (TwoSectorWelfare.wJ n1 (Moments.calvoKappa α1 β ω θ σi)
            (TwoSectorWelfare.kappaH n1 (Moments.calvoKappa α1 β ω θ σi)
              (Moments.calvoKappa α2 β ω θ σi)))
          (TwoSectorWelfare.wJ (1 - n1) (Moments.calvoKappa α2 β ω θ σi)
            (TwoSectorWelfare.kappaH n1 (Moments.calvoKappa α1 β ω θ σi)
              (Moments.calvoKappa α2 β ω θ σi)))
          (TwoSectorWelfare.lamX (TwoSectorWelfare.kappaH n1 (Moments.calvoKappa α1 β ω θ σi)
            (Moments.calvoKappa α2 β ω θ σi)) θ)
          (TwoSectorWelfare.lamR n1 η ω σi (TwoSectorWelfare.kappaH n1
            (Moments.calvoKappa α1 β ω θ σi) (Moments.calvoKappa α2 β ω θ σi)) θ)
          (π1 a t) (π2 a t) (x a t) xs (gR a t) +
        (∑' t, β ^ t * τ a t - K / 2 * (θ * (1 + ω * θ)) *
          (n1 * (α1 * Δ1m a / (1 - α1 * β)) + (1 - n1) * (α2 * Δ2m a / (1 - α2 * β))))) =
      ∑' t, β ^ t * R a t - K / 2 * (θ * (σi + ω)) *
        (n1 / Moments.calvoKappa α1 β ω θ σi * ∑' t, β ^ t * (pb1 a t ^ 2 - π1 a t ^ 2) +
          (1 - n1) / Moments.calvoKappa α2 β ω θ σi *
            ∑' t, β ^ t * (pb2 a t ^ 2 - π2 a t ^ 2)) := by
    filter_upwards [bR, bx, bg, bπ1, bπ2, bp1, bp2, bΔ1, bΔ2] with a hRa hxa hga h1a h2a hp1a
      hp2a hd1a hd2a
    have hxa' : Sequences.Bdd (x a) := by
      obtain ⟨M, hM⟩ := hxa
      exact ⟨M + |xs|, fun t => by
        have := abs_sub_abs_le_abs_sub (x a t) xs
        have := hM t
        linarith [abs_nonneg xs]⟩
    have h := TwoSectorWelfare.prop_6_11 (U := W a) (tipU := τ a) (R := R a) (K := K) (xs := xs)
      (η := η) (σi := σi) (ω := ω) (θ := θ) (n1 := n1) (β := β) (x := x a) (gR := gR a)
      (Δ1 := Δ1 a) (Δ2 := Δ2 a)
      ha10 ha11 ha20 ha21 hβ0 hβ1 hn0 hn1 hθ hωθ hσω (fun t => by simp only [hR]; ring)
      (h10 a) (h1s a) (h20 a) (h2s a) hxa' hga h1a h2a hp1a hp2a hd1a hd2a (hτ a) hRa
    dsimp only at h
    rw [h]
    ring
  exact ((tsum_o hβ0 hβ1 (f := R) hP).sub
    ((((tsum_o hβ0 hβ1 (sq hp1 hπ1)).const_mul_left (n1 / Moments.calvoKappa α1 β ω θ σi)).add
      ((tsum_o hβ0 hβ1 (sq hp2 hπ2)).const_mul_left
        ((1 - n1) / Moments.calvoKappa α2 β ω θ σi))).const_mul_left
          (K / 2 * (θ * (σi + ω))))).congr' (hev.mono fun a ha => ha.symm)
      (Eventually.of_forall fun _ => rfl)

/-- Woodford (2003), §4.3 and §4.4 (discounted losses with a first-order solution): the generic
discounted bridge. If `∑βᵗW = −Ω∑βᵗL(ε) + T + O(ε³)` (Layer A plus uniform remainders, e.g.
`prop611_layerB`, `prop613_layerB`) and `∑βᵗL(ε) = ε²∑βᵗL₁ + O(ε³)` (`tsum_sq_first_order`),
then `∑βᵗW = T − ε²Ω∑βᵗL₁ + O(ε³)`. -/
theorem discounted_first_order {W T SL SL1 : A → ℝ} {Om : ℝ}
    (h1 : (fun a => W a - (-Om * SL a + T a)) =O[l] fun a => e a ^ 3)
    (h2 : (fun a => SL a - e a ^ 2 * SL1 a) =O[l] fun a => e a ^ 3) :
    (fun a => W a - (T a - e a ^ 2 * (Om * SL1 a))) =O[l] fun a => e a ^ 3 :=
  (h1.sub (h2.const_mul_left Om)).congr_left fun a => by ring

/-! ## Proposition 6.12 (Layer B): sticky wages, from the actual utility -/

/-- Woodford (2003), (E.36), p. 708: the log labour index `Ĥ = log ∑ w_i G(ŷ_i − a)`, where
`H̄G(ŷ − a) = f⁻¹(y/A)` is the labour requirement of a good with output `y = Ȳe^{ŷ}` and
technology `A = Āe^{a}` (`G(0) = 1`). -/
noncomputable def logHidx (w : ι → ℝ) (G : ℝ → ℝ) (a : ℝ) (yh : ι → ℝ) : ℝ :=
  Real.log (∑ i, w i * G (yh i - a))

/-- Woodford (2003), (E.36), p. 708 (the "`O(3)`" of the labour index): if `G` is `C³` with
`G(0) = 1`, `G′(0) = φ_h`, `G″(0) = φ_h(1 + ω_p)` (`StickyWageWelfare.labor_requirement_coeffs`),
then for first-order `ŷ(i)` and `a`,
`Ĥ = HT(E_iŷ, a, var_iŷ) + O(s³)` with `HT` the second-order polynomial of (E.36). -/
theorem labourAtom_o (hs : Tendsto s L (𝓝 0)) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {G : ℝ → ℝ} (hG : ContDiff ℝ 3 G) (hG0 : G 0 = 1) {φh ωp : ℝ}
    (hG1 : fderiv ℝ G 0 1 = φh) (hG2 : fderiv ℝ (fderiv ℝ G) 0 1 1 = φh * (1 + ωp))
    {yh : B → ι → ℝ} {a : B → ℝ} (hyh : yh =O[L] fun b => s b ^ 1)
    (ha : a =O[L] fun b => s b ^ 1) :
    (fun b => logHidx w G (a b) (yh b) - StickyWageWelfare.HT φh ωp (crossMean w (yh b)) (a b)
      (crossVar w (yh b))) =O[L] fun b => s b ^ 3 := by
  set g2 := φh * (1 + ωp) with hg2
  have hu : ∀ i, (fun b => yh b i - a b) =O[L] fun b => s b ^ 1 := fun i => (coord_o hyh i).sub ha
  -- the Taylor remainder of `G` good by good
  have hT : ∀ i, (fun b => G (yh b i - a b) - (1 + φh * (yh b i - a b) +
      g2 / 2 * (yh b i - a b) ^ 2)) =O[L] fun b => s b ^ 3 := by
    intro i
    refine (taylor_family hG 0 hs (hu i)).congr_left fun b => ?_
    have e1 : fderiv ℝ G 0 (yh b i - a b) = (yh b i - a b) * φh := by
      rw [show yh b i - a b = (yh b i - a b) • (1 : ℝ) by simp, map_smul, hG1, smul_eq_mul]
      simp
    have e2 : fderiv ℝ (fderiv ℝ G) 0 (yh b i - a b) (yh b i - a b) =
        (yh b i - a b) ^ 2 * g2 := by
      rw [show yh b i - a b = (yh b i - a b) • (1 : ℝ) by simp, map_smul, map_smul,
        smul_apply, hG2, smul_eq_mul, smul_eq_mul]
      simp only [smul_eq_mul, mul_one, hg2]
      ring
    simp only [ApproxTheory.quadApprox, zero_add, hG0, e1, e2]
    ring
  set Eu := fun b => crossMean w (yh b) - a b with hEu
  set Eu2 := fun b => ∑ i, w i * (yh b i - a b) ^ 2 with hEu2
  set ER := fun b => ∑ i, w i * (G (yh b i - a b) - (1 + φh * (yh b i - a b) +
      g2 / 2 * (yh b i - a b) ^ 2)) with hER
  have hEuO : Eu =O[L] fun b => s b ^ 1 := (crossMean_o hw0 hw1 hyh).sub ha
  have hEu2O : Eu2 =O[L] fun b => s b ^ 2 :=
    IsBigO.fun_sum (s := Finset.univ) fun i _ => (o_pow (hu i) 2).const_mul_left (w i)
  have hERO : ER =O[L] fun b => s b ^ 3 :=
    IsBigO.fun_sum (s := Finset.univ) fun i _ => (hT i).const_mul_left (w i)
  -- `X = ∑ w_i G(u_i) − 1 = φ_h E u + (g₂/2) E u² + ER`
  have hX : ∀ b, ∑ i, w i * G (yh b i - a b) - 1 = φh * Eu b + g2 / 2 * Eu2 b + ER b := by
    intro b
    have hsplit : ER b = ∑ i, w i * G (yh b i - a b) - ∑ i, w i -
        φh * ∑ i, w i * (yh b i - a b) - g2 / 2 * Eu2 b := by
      simp only [hER, hEu2, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hlin : ∑ i, w i * (yh b i - a b) = Eu b := by
      simp only [hEu, crossMean, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
    rw [hsplit, hlin, hw1]
    ring
  have hP : (fun b => φh * Eu b + g2 / 2 * Eu2 b) =O[L] fun b => s b ^ 1 :=
    (hEuO.const_mul_left φh).add ((o_weaken hs (by norm_num : 1 ≤ 2) hEu2O).const_mul_left _)
  have hXO : (fun b => φh * Eu b + g2 / 2 * Eu2 b + ER b) =O[L] fun b => s b ^ 1 :=
    hP.add (o_weaken hs (by norm_num : 1 ≤ 3) hERO)
  have hlog := (ExpLogCES.log_taylor2_isBigO.comp_tendsto (tendsto_of_o_one hs hXO)).trans
    (o_pow hXO 3)
  -- the polynomial part
  have hvar : ∀ b, Eu2 b = Eu b ^ 2 + crossVar w (yh b) := by
    intro b
    rw [ExpLogCES.crossVar_eq hw1]
    simp only [hEu, hEu2, crossMean]
    have e : ∑ i, w i * (yh b i - a b) ^ 2 = ∑ i, w i * yh b i ^ 2 -
        2 * a b * ∑ i, w i * yh b i + a b ^ 2 * ∑ i, w i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, hw1]
    ring
  have hQ : (fun b => -(1 / 2) * ((g2 / 2 * Eu2 b) * (2 * (φh * Eu b) + g2 / 2 * Eu2 b)))
      =O[L] fun b => s b ^ 3 :=
    (o_mul (hEu2O.const_mul_left (g2 / 2)) ((hEuO.const_mul_left (2 * φh)).add
      ((o_weaken hs (by norm_num : 1 ≤ 2) hEu2O).const_mul_left (g2 / 2)))
      (by norm_num : 2 + 1 = 3)).const_mul_left (-(1 / 2)) |>.congr_left fun b => by ring
  have hR2 : (fun b => ER b - ER b * (2 * (φh * Eu b + g2 / 2 * Eu2 b) + ER b) / 2)
      =O[L] fun b => s b ^ 3 :=
    hERO.sub ((o_weaken hs (by norm_num : 3 ≤ 4) (o_mul hERO
      ((hP.const_mul_left 2).add (o_weaken hs (by norm_num : 1 ≤ 3) hERO))
      (by norm_num : 3 + 1 = 4))).const_mul_left (1 / 2)) |>.congr_left fun b => by ring
  refine ((hlog.add hQ).add hR2).congr_left fun b => ?_
  simp only [Function.comp, logHidx, StickyWageWelfare.HT]
  rw [show ∑ i, w i * G (yh b i - a b) = 1 + (∑ i, w i * G (yh b i - a b) - 1) by ring, hX b]
  have hv := hvar b
  have hEub : crossMean w (yh b) - a b = Eu b := rfl
  rw [hEub]
  rw [hv] at *
  simp only [hg2]
  ring

/-- Woodford (2003), (E.33), p. 707: the remainder of Proposition 6.12 is `O(s³)` along ANY
family with `Φ, Ŷ, a, h̄ = O(s)` and `V_p, V_w = O(s²)` (not only along weighted rays). -/
theorem R612_o (hs : Tendsto s L (𝓝 0)) (ω ν θp ωp θw φh : ℝ) {Phi Y a hb Vp Vw : B → ℝ}
    (hPhi : Phi =O[L] fun b => s b ^ 1) (hY : Y =O[L] fun b => s b ^ 1)
    (ha : a =O[L] fun b => s b ^ 1) (hhb : hb =O[L] fun b => s b ^ 1)
    (hVp : Vp =O[L] fun b => s b ^ 2) (hVw : Vw =O[L] fun b => s b ^ 2) :
    (fun b => StickyWageWelfare.R612 ω ν θp ωp θw φh (Phi b) (Y b) (a b) (hb b) (Vp b) (Vw b))
      =O[L] fun b => s b ^ 3 := by
  have hu := hY.sub ha
  have hR36 : (fun b => StickyWageWelfare.R36 φh ωp θp (Y b - a b) (Vp b))
      =O[L] fun b => s b ^ 3 :=
    (((o_mul hu hVp (by norm_num : 1 + 2 = 3)).const_mul_left
      ((1 + ωp - φh) * φh * (θp * (θp - 1) / 2))).neg_left.add
      ((o_weaken hs (by norm_num : 3 ≤ 4) (o_mul hVp hVp (by norm_num : 2 + 2 = 4))).const_mul_left
        ((1 + ωp - φh) * φh / 2 * (θp * (θp - 1) / 2) ^ 2))).congr_left fun b => by
      unfold StickyWageWelfare.R36; ring
  have hE2 : (fun b => StickyWageWelfare.E2 φh ωp θp (Y b - a b) (Vp b))
      =O[L] fun b => s b ^ 2 :=
    ((((o_pow hu 2).const_mul_left ((1 + ωp - φh) * φh / 2)).add
      (hVp.const_mul_left ((1 + ωp * θp) * θp * φh / 2))).add
      (o_weaken hs (by norm_num : 2 ≤ 3) hR36)).congr_left fun b => by
        unfold StickyWageWelfare.E2; ring
  have hC3 : (fun b => StickyWageWelfare.C3 ν φh (hb b) (Y b - a b)
      (StickyWageWelfare.E2 φh ωp θp (Y b - a b) (Vp b))) =O[L] fun b => s b ^ 3 :=
    ((((o_mul hu hE2 (by norm_num : 1 + 2 = 3)).const_mul_left ((1 + ν) * φh)).add
      ((o_weaken hs (by norm_num : 3 ≤ 4) (o_mul hE2 hE2 (by norm_num : 2 + 2 = 4))).const_mul_left
        ((1 + ν) / 2))).sub ((o_mul hhb hE2 (by norm_num : 1 + 2 = 3)).const_mul_left
        ν)).congr_left fun b => by unfold StickyWageWelfare.C3; ring
  have hH : (fun b => φh * (Y b - a b) + StickyWageWelfare.E2 φh ωp θp (Y b - a b) (Vp b))
      =O[L] fun b => s b ^ 1 :=
    (hu.const_mul_left φh).add (o_weaken hs (by norm_num : 1 ≤ 2) hE2)
  have hR34 : (fun b => StickyWageWelfare.R34 ν θw (φh * (Y b - a b) +
      StickyWageWelfare.E2 φh ωp θp (Y b - a b) (Vp b)) (hb b) (Vw b))
      =O[L] fun b => s b ^ 3 :=
    ((((o_mul hH hVw (by norm_num : 1 + 2 = 3)).const_mul_left ((1 + ν) / 2 * θw * (1 - θw))).add
      ((o_weaken hs (by norm_num : 3 ≤ 4) (o_mul hVw hVw (by norm_num : 2 + 2 = 4))).const_mul_left
        ((1 + ν) / 8 * θw ^ 2 * (1 - θw) ^ 2))).sub
      ((o_mul hhb hVw (by norm_num : 1 + 2 = 3)).const_mul_left (ν * θw * (1 - θw) / 2))).congr_left
        fun b => by unfold StickyWageWelfare.R34; ring
  have hQ2 : (fun b => StickyWageWelfare.Q2 ω ν θp ωp θw φh (Y b - a b) (hb b) (Vp b) (Vw b))
      =O[L] fun b => s b ^ 2 :=
    (((((o_pow hu 2).const_mul_left ((1 + ω) / 2)).sub
      ((o_mul hhb hu (by norm_num : 1 + 1 = 2)).const_mul_left ν)).add
      (hVp.const_mul_left (θp * (1 + ωp * θp) / 2))).add
      (hVw.const_mul_left (θw * (1 + ν * θw) / (2 * φh)))).congr_left fun b => by
        unfold StickyWageWelfare.Q2; ring
  have hX := (hC3.add hR36).add hR34
  refine ((o_mul hPhi hQ2 (by norm_num : 1 + 2 = 3)).sub ((hX.const_mul_left φh⁻¹).sub
    ((o_weaken hs (by norm_num : 3 ≤ 4) (o_mul hPhi hX (by norm_num : 1 + 3 = 4))).const_mul_left
      φh⁻¹))).congr_left fun b => ?_
  unfold StickyWageWelfare.R612
  ring

variable {J : Type*} [Fintype J]

/-- Woodford (2003), §4.4, p. 443 and (E.34): the log wage index
`log(W/W̄) = log(∑ w_j e^{(1−θ_w)lw_j})^{1/(1−θ_w)}` of the log relative wages `lw_j`. -/
noncomputable def logWidx (ωt : J → ℝ) (θw : ℝ) (lw : J → ℝ) : ℝ :=
  Real.log (ExpLogCES.cesIndex ωt (1 - θw) (fun j => Real.exp (lw j)))

/-- Woodford (2003), §4.4, eq. (4.27)–(4.28), p. 444: the ACTUAL period utility of the
sticky-wage model, `u(Y; ξ) − ∫ v(h(j); ξ)dj`, with goods' outputs `Ȳe^{ŷ(i)}`, the labour
index `H = H̄e^{Ĥ}` (`logHidx`), wages `w_j = W̄e^{lw_j}`, the wage index `W` (`logWidx`) and
labour demands `ĥ(j) = Ĥ − θ_w(lw_j − log(W/W̄))`. -/
noncomputable def periodU12 (u v : ℝ × Ξ → ℝ) (w : ι → ℝ) (ωt : J → ℝ) (θp θw Ybar Hbar : ℝ)
    (G : ℝ → ℝ) (a : ℝ) (yh : ι → ℝ) (lw : J → ℝ) (xu xv : Ξ) : ℝ :=
  u (Ybar * Real.exp (logYidx w θp yh), xu) -
    ∑ j, ωt j * v (Hbar * Real.exp (logHidx w G a yh - θw * (lw j - logWidx ωt θw lw)), xv)

/-- Woodford (2003), (E.33): the policy-independent terms of the actual expansion. -/
noncomputable def tip12 (u v : ℝ × Ξ → ℝ) (Ybar Hbar : ℝ) (xu xv : Ξ) : ℝ :=
  (u (Ybar, 0) + dXi u (Ybar, 0) xu + dXiXi u (Ybar, 0) xu / 2) -
    (v (Hbar, 0) + dXi v (Hbar, 0) xv + dXiXi v (Hbar, 0) xv / 2)

/-- Woodford (2003), (4.28)/(E.33): the quadratic form of Proposition 6.12 at the efficient
steady state (`x* = 0`),
`(σ⁻¹ + ω)(Ŷ − Ŷⁿ)² + θ_p(1 + ω_pθ_p)V_p + θ_wφ_h⁻¹(1 + νθ_w)V_w`. -/
noncomputable def loss612 (σi ω ν θp ωp θw φh g a hb Y Vp Vw : ℝ) : ℝ :=
  (σi + ω) * (Y - StickyWageWelfare.natY612 σi ω ν g a hb) ^ 2 + θp * (1 + ωp * θp) * Vp +
    θw / φh * (1 + ν * θw) * Vw

/-- Woodford (2003), **Proposition 6.12**, (4.28)/(E.33), pp. 444, 707–708, from the ACTUAL
utility (Layer B, period form): `u, v` `C³` at the efficient steady state, labour requirement
`H̄G(ŷ − a) = f⁻¹(y/A)` with `G` `C³`, `G(0) = 1`, `G′(0) = φ_h`, `G″(0) = φ_h(1 + ω_p)`;
`σ⁻¹ = −Ȳu_cc/u_c`, `ν = H̄v_hh/v_h`, `ω = ω_p + νφ_h`, the efficient steady state
`H̄v_hφ_h = Ȳu_c` ((E.33) at `Φ_y = 0`), composite disturbances `g`, `h̄`. Along any family with
`ŷ(i), a, lw_j, ξ = O(s)`, the actual period utility is
`t.i.p. + Ȳu_c[tip612 − ½ loss612] + O(s³)` with `V_p = var_i ŷ/θ_p²` (= `var_i log p` by
(2.12)) and `V_w = var_j lw`. All aggregation remainders (output CES atom, labour-index atom
`labourAtom_o`, wage-index atom `Links.CES.priceAtom`) are `O(s³)`. -/
theorem prop612_actual (hs : Tendsto s L (𝓝 0)) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {ωt : J → ℝ} (hωt0 : ∀ j, 0 ≤ ωt j) (hωt1 : ∑ j, ωt j = 1)
    {θp θw : ℝ} (hθp : θp ≠ 0) (hθp1 : θp ≠ 1) (hθw1 : θw ≠ 1)
    {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 3 G) (hG0 : G 0 = 1) {σi ω ν ωp φh Ybar Hbar : ℝ}
    (hG1 : fderiv ℝ G 0 1 = φh) (hG2 : fderiv ℝ (fderiv ℝ G) 0 1 1 = φh * (1 + ωp))
    (hω : ω = ωp + ν * φh) (hφ : φh ≠ 0) (hσω : σi + ω ≠ 0)
    (hucc : dYY u (Ybar, 0) = -(σi * dY u (Ybar, 0) / Ybar))
    (hvhh : dYY v (Hbar, 0) = ν * dY v (Hbar, 0) / Hbar)
    (hss : Hbar * dY v (Hbar, 0) * φh = Ybar * dY u (Ybar, 0))
    {yh : B → ι → ℝ} {lw : B → J → ℝ} {a g hb : B → ℝ} {xu xv : B → Ξ}
    (hg : ∀ b, dYXi u (Ybar, 0) (xu b) = σi * dY u (Ybar, 0) * g b)
    (hhb : ∀ b, dYXi v (Hbar, 0) (xv b) = -(ν * dY v (Hbar, 0) * hb b))
    (hyh : yh =O[L] fun b => s b ^ 1) (hlw : lw =O[L] fun b => s b ^ 1)
    (ha : a =O[L] fun b => s b ^ 1) (hgO : g =O[L] fun b => s b ^ 1)
    (hhbO : hb =O[L] fun b => s b ^ 1) (hxu : xu =O[L] fun b => s b ^ 1)
    (hxv : xv =O[L] fun b => s b ^ 1) :
    (fun b => periodU12 u v w ωt θp θw Ybar Hbar G (a b) (yh b) (lw b) (xu b) (xv b) -
      (tip12 u v Ybar Hbar (xu b) (xv b) + Ybar * dY u (Ybar, 0) *
        (StickyWageWelfare.tip612 σi ω ν 0 (g b) (a b) (hb b) -
          loss612 σi ω ν θp ωp θw φh (g b) (a b) (hb b) (logYidx w θp (yh b))
            (crossVar w (yh b) / θp ^ 2) (crossVar ωt (lw b)) / 2))) =O[L] fun b => s b ^ 3 := by
  set K := Ybar * dY u (Ybar, 0) with hK
  set Kh := Hbar * dY v (Hbar, 0) with hKh0
  have hKh : Kh = K / φh := by rw [eq_div_iff hφ]; exact hss
  set Y := fun b => logYidx w θp (yh b) with hY
  set Vy := fun b => crossVar w (yh b) with hVy
  set Vw := fun b => crossVar ωt (lw b) with hVw
  set Hh := fun b => logHidx w G (a b) (yh b) with hHh
  set lW := fun b => logWidx ωt θw (lw b) with hlW
  set Hp := fun b => StickyWageWelfare.HT φh ωp (TwoSectorWelfare.meanE28 θp⁻¹ (Y b) (Vy b)) (a b)
    (Vy b) with hHp
  set pA := fun b => Links.CES.priceAtom ωt θw (lw b) with hpA
  have hYO : Y =O[L] fun b => s b ^ 1 := logYidx_o hs hw0 hw1 hθp1 hyh
  have hVyO : Vy =O[L] fun b => s b ^ 2 := crossVar_o hw0 hw1 hyh
  have hVwO : Vw =O[L] fun b => s b ^ 2 := crossVar_o hωt0 hωt1 hlw
  have hrC := cesAtom_o hs hw0 hw1 hθp1 hyh
  have hmE : (fun b => TwoSectorWelfare.meanE28 θp⁻¹ (Y b) (Vy b) - a b) =O[L] fun b => s b ^ 1 :=
    ((hYO.sub ((o_weaken hs (by norm_num : 1 ≤ 2) hVyO).const_mul_left ((1 - θp⁻¹) / 2))).sub
      ha).congr_left fun b => by unfold TwoSectorWelfare.meanE28; ring
  -- the labour index: `Ĥ − Hp = O(s³)`
  have hH1 := labourAtom_o hs hw0 hw1 hG hG0 hG1 hG2 hyh ha
  have hH2 : (fun b => StickyWageWelfare.HT φh ωp (crossMean w (yh b)) (a b) (Vy b) - Hp b)
      =O[L] fun b => s b ^ 3 := by
    have hc2 : (fun b => φh + (1 + ωp - φh) * φh / 2 * (2 * (TwoSectorWelfare.meanE28 θp⁻¹ (Y b)
        (Vy b) - a b) + Links.CES.cesAtom w θp (yh b))) =O[L] fun b => s b ^ 0 :=
      ((isBigO_const_const φh one_ne_zero L).congr_right (fun b => by ring)).add
        ((o_weaken hs (by norm_num : 0 ≤ 1) ((hmE.const_mul_left 2).add
          (o_weaken hs (by norm_num : 1 ≤ 3) hrC))).const_mul_left _)
    refine (o_mul hrC hc2 (by norm_num : 3 + 0 = 3)).congr_left fun b => ?_
    have hrel := Links.CES.ces_relation w θp (yh b)
    simp only [hHp, StickyWageWelfare.HT, TwoSectorWelfare.meanE28, hY, hVy, logYidx] at hrel ⊢
    rw [hrel]
    ring
  have hHd : (fun b => Hh b - Hp b) =O[L] fun b => s b ^ 3 :=
    (hH1.add hH2).congr_left fun b => by simp only [hHh, hVy]; ring
  have hHpO : Hp =O[L] fun b => s b ^ 1 :=
    (((hmE.const_mul_left φh).add ((o_weaken hs (by norm_num : 1 ≤ 2) (o_pow hmE 2)).const_mul_left
      ((1 + ωp - φh) * φh / 2))).add ((o_weaken hs (by norm_num : 1 ≤ 2) hVyO).const_mul_left
        ((1 + ωp) * φh / 2))).congr_left fun b => by simp only [hHp, StickyWageWelfare.HT]
  have hHhO : Hh =O[L] fun b => s b ^ 1 :=
    ((o_weaken hs (by norm_num : 1 ≤ 3) hHd).add hHpO).congr_left fun b => by ring
  -- the wage index
  have hpAO : pA =O[L] fun b => s b ^ 3 := by
    have h0 : Tendsto lw L (𝓝 (fun _ => (0 : ℝ))) := tendsto_of_o_one hs hlw
    refine ((Links.CES.priceAtom_isBigO hωt0 hωt1 hθw1 0).comp_tendsto h0).trans ?_
    refine ((hlw.norm_left.pow 3).congr_right fun b => by ring).congr_left fun b => ?_
    simp only [Function.comp]
    congr 2
    ext j
    simp
  have hlWO : lW =O[L] fun b => s b ^ 1 :=
    (((crossMean_o hωt0 hωt1 hlw).add ((o_weaken hs (by norm_num : 1 ≤ 2) hVwO).const_mul_left
      ((1 - θw) / 2))).add (o_weaken hs (by norm_num : 1 ≤ 3) hpAO)).congr_left fun b => by
        simp only [hpA, Links.CES.priceAtom, hlW, logWidx, hVw]; ring
  have hhj : ∀ j, (fun b => Hh b - θw * (lw b j - lW b)) =O[L] fun b => s b ^ 1 := fun j =>
    hHhO.sub (((coord_o hlw j).sub hlWO).const_mul_left θw)
  -- the Taylor steps
  have hu1 := uTaylor_family_exp hu Ybar hs hYO hxu
  have hvs := IsBigO.fun_sum (s := Finset.univ) fun j _ =>
    (uTaylor_family_exp hv Hbar hs (hhj j) hxv).const_mul_left (ωt j)
  have hRu := Ru_o hs σi hgO hYO (expRem_o hs hYO)
  have hRv : (fun b => ∑ j, ωt j * Prop61.Rv 0 ν (hb b) (Hh b - θw * (lw b j - lW b))
      (expRem (Hh b - θw * (lw b j - lW b)))) =O[L] fun b => s b ^ 3 :=
    IsBigO.fun_sum (s := Finset.univ) fun j _ =>
      (Rv0_o hs ν hhbO (hhj j) (expRem_o hs (hhj j))).const_mul_left (ωt j)
  have hR612 := R612_o hs ω ν θp ωp θw φh (Vp := fun b => Vy b / θp ^ 2) (isBigO_zero _ _) hYO
    ha hhbO ((hVyO.const_mul_left (θp ^ 2)⁻¹).congr_left fun b => by ring) hVwO
  -- the difference of the two `TvhMom` arguments
  set m1 := fun b => Hh b - θw * (crossMean ωt (lw b) - lW b) with hm1
  set m2 := fun b => Hp b - θw * (-((1 - θw) / 2) * Vw b) with hm2
  have hm12 : (fun b => m1 b - m2 b) =O[L] fun b => s b ^ 3 :=
    (hHd.add (hpAO.const_mul_left θw)).congr_left fun b => by
      simp only [hm1, hm2, hpA, Links.CES.priceAtom, hlW, logWidx, hVw]; ring
  have hm1O : m1 =O[L] fun b => s b ^ 1 :=
    hHhO.sub (((crossMean_o hωt0 hωt1 hlw).sub hlWO).const_mul_left θw)
  have hm2O : m2 =O[L] fun b => s b ^ 1 :=
    hHpO.sub ((o_weaken hs (by norm_num : 1 ≤ 2) hVwO).const_mul_left (θw * (-((1 - θw) / 2))))
      |>.congr_left fun b => by ring
  have hΔ : (fun b => (m1 b - m2 b) * (1 + (1 + ν) / 2 * (m1 b + m2 b) - ν * hb b))
      =O[L] fun b => s b ^ 3 :=
    o_mul hm12 (((isBigO_const_const (1 : ℝ) one_ne_zero L).congr_right (fun b => by ring)).add
      ((o_weaken hs (by norm_num : 0 ≤ 1) (hm1O.add hm2O)).const_mul_left ((1 + ν) / 2)) |>.sub
      ((o_weaken hs (by norm_num : 0 ≤ 1) hhbO).const_mul_left ν)) (by norm_num : 3 + 0 = 3)
  refine ((((hu1.sub hvs).add (hRu.const_mul_left K)).sub
    ((hΔ.add hRv).const_mul_left Kh)).add (hR612.const_mul_left K)).congr_left fun b => ?_
  -- the exact identities at `b`
  have eU := Prop61.uTaylor_eq_of_coeffs (ubar := u (Ybar, 0)) (Lu := dXi u (Ybar, 0) (xu b))
    (Qu := dXiXi u (Ybar, 0) (xu b)) (Y := Y b) (r := expRem (Y b)) hucc (hg b)
  have hper : ∀ j, ωt j * Prop61.uTaylor (v (Hbar, 0)) (dY v (Hbar, 0)) (dYY v (Hbar, 0))
      (dXi v (Hbar, 0) (xv b)) (dYXi v (Hbar, 0) (xv b)) (dXiXi v (Hbar, 0) (xv b))
      (Hbar * ((Hh b - θw * (lw b j - lW b)) + (Hh b - θw * (lw b j - lW b)) ^ 2 / 2 +
        expRem (Hh b - θw * (lw b j - lW b)))) =
      (v (Hbar, 0) + dXi v (Hbar, 0) (xv b) + dXiXi v (Hbar, 0) (xv b) / 2) * ωt j +
        Kh * (ωt j * StickyWageWelfare.Tvh ν (hb b) ((Hh b + θw * lW b) + -θw * lw b j) +
          ωt j * Prop61.Rv 0 ν (hb b) (Hh b - θw * (lw b j - lW b))
            (expRem (Hh b - θw * (lw b j - lW b)))) := by
    intro j
    rw [Prop61.uTaylor, hvhh, hhb b]
    unfold StickyWageWelfare.Tvh Prop61.Rv
    simp only [hKh0]
    field_simp
    ring
  have eV : ∑ j, ωt j * Prop61.uTaylor (v (Hbar, 0)) (dY v (Hbar, 0)) (dYY v (Hbar, 0))
      (dXi v (Hbar, 0) (xv b)) (dYXi v (Hbar, 0) (xv b)) (dXiXi v (Hbar, 0) (xv b))
      (Hbar * ((Hh b - θw * (lw b j - lW b)) + (Hh b - θw * (lw b j - lW b)) ^ 2 / 2 +
        expRem (Hh b - θw * (lw b j - lW b)))) =
      (v (Hbar, 0) + dXi v (Hbar, 0) (xv b) + dXiXi v (Hbar, 0) (xv b) / 2) +
        Kh * (StickyWageWelfare.TvhMom ν (hb b) (m1 b) (θw ^ 2 * Vw b) +
          ∑ j, ωt j * Prop61.Rv 0 ν (hb b) (Hh b - θw * (lw b j - lW b))
            (expRem (Hh b - θw * (lw b j - lW b)))) := by
    rw [Finset.sum_congr rfl fun j _ => hper j]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hωt1]
    rw [StickyWageWelfare.sum_Tvh hωt1, Moments.crossMean_affine hωt1,
      Moments.crossVar_affine hωt1]
    simp only [hm1, hVw, neg_sq]
    ring_nf
  have key := StickyWageWelfare.prop_6_12_layerA (θw := θw) hω hφ hσω hθp 0 (Y b) (g b) (a b)
    (hb b) (Vy b / θp ^ 2) (Vw b)
  dsimp only at key
  have hθ2 : θp ^ 2 * (Vy b / θp ^ 2) = Vy b := by field_simp
  rw [hθ2] at key
  have e34 := StickyWageWelfare.E34 ν θw (Hp b) (hb b) (Vw b)
  have hsum : ∑ j, ωt j * (v (Hbar * Real.exp (Hh b - θw * (lw b j - lW b)), xv b) -
      Prop61.uTaylor (v (Hbar, 0)) (dY v (Hbar, 0)) (dYY v (Hbar, 0)) (dXi v (Hbar, 0) (xv b))
        (dYXi v (Hbar, 0) (xv b)) (dXiXi v (Hbar, 0) (xv b))
        (Hbar * ((Hh b - θw * (lw b j - lW b)) + (Hh b - θw * (lw b j - lW b)) ^ 2 / 2 +
          expRem (Hh b - θw * (lw b j - lW b))))) =
      ∑ j, ωt j * v (Hbar * Real.exp (Hh b - θw * (lw b j - lW b)), xv b) -
        ∑ j, ωt j * Prop61.uTaylor (v (Hbar, 0)) (dY v (Hbar, 0)) (dYY v (Hbar, 0))
          (dXi v (Hbar, 0) (xv b)) (dYXi v (Hbar, 0) (xv b)) (dXiXi v (Hbar, 0) (xv b))
          (Hbar * ((Hh b - θw * (lw b j - lW b)) + (Hh b - θw * (lw b j - lW b)) ^ 2 / 2 +
            expRem (Hh b - θw * (lw b j - lW b)))) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum, eV, eU, hKh]
  simp only [periodU12, tip12, loss612, StickyWageWelfare.TvhMom, StickyWageWelfare.W34,
    Prop61.xStarLin, hm2, hHp, hY, hVy, hHh, hlW] at key e34 ⊢
  linear_combination (-K) * key + (K / φh) * e34

/-- Woodford (2003), (4.28)/(E.33): the quadratic form of Proposition 6.12 along a family with a
first-order solution (`Ŷ, g, a, h̄ = ε × first order + O(ε²)`, `V_p, V_w = ε² × first order
+ O(ε³)`) is `ε²` times its value at the first-order solution, up to `O(ε³)`. -/
theorem loss612_first_order (hs : Tendsto s L (𝓝 0)) (σi ω ν θp ωp θw φh : ℝ)
    {g a hb Y Vp Vw gf af hbf Yf Vpf Vwf : B → ℝ}
    (hg : (fun b => g b - s b * gf b) =O[L] fun b => s b ^ 2)
    (ha : (fun b => a b - s b * af b) =O[L] fun b => s b ^ 2)
    (hhb : (fun b => hb b - s b * hbf b) =O[L] fun b => s b ^ 2)
    (hY : (fun b => Y b - s b * Yf b) =O[L] fun b => s b ^ 2)
    (hVp : (fun b => Vp b - s b ^ 2 * Vpf b) =O[L] fun b => s b ^ 3)
    (hVw : (fun b => Vw b - s b ^ 2 * Vwf b) =O[L] fun b => s b ^ 3)
    (bg : gf =O[L] fun _ => (1 : ℝ)) (ba : af =O[L] fun _ => (1 : ℝ))
    (bhb : hbf =O[L] fun _ => (1 : ℝ)) (bY : Yf =O[L] fun _ => (1 : ℝ)) :
    (fun b => loss612 σi ω ν θp ωp θw φh (g b) (a b) (hb b) (Y b) (Vp b) (Vw b) -
      s b ^ 2 * loss612 σi ω ν θp ωp θw φh (gf b) (af b) (hbf b) (Yf b) (Vpf b) (Vwf b))
      =O[L] fun b => s b ^ 3 := by
  set c1 := σi / (σi + ω)
  set c2 := (1 + ω) / (σi + ω)
  set c3 := ν / (σi + ω)
  have hG : (fun b => (Y b - (c1 * g b + c2 * a b + c3 * hb b)) -
      s b * (Yf b - (c1 * gf b + c2 * af b + c3 * hbf b))) =O[L] fun b => s b ^ 2 :=
    (hY.sub (((hg.const_mul_left c1).add (ha.const_mul_left c2)).add
      (hhb.const_mul_left c3))).congr_left fun b => by ring
  have bG : (fun b => Yf b - (c1 * gf b + c2 * af b + c3 * hbf b)) =O[L] fun _ => (1 : ℝ) :=
    bY.sub (((bg.const_mul_left c1).add (ba.const_mul_left c2)).add (bhb.const_mul_left c3))
  refine ((((sq_sub_o hs hG bG).const_mul_left (σi + ω)).add
    (hVp.const_mul_left (θp * (1 + ωp * θp)))).add
    (hVw.const_mul_left (θw / φh * (1 + ν * θw)))).congr_left fun b => ?_
  simp only [loss612, StickyWageWelfare.natY612, c1, c2, c3]
  ring

/-- Woodford (2003), **Proposition 6.12**, (4.28)/(E.33), LAYER B: under the hypotheses of
`prop612_actual`, if the family has a first-order solution (`ŷ = εŷ¹ + O(ε²)`,
`lw = εlw¹ + O(ε²)`, `Ŷ, g, a, h̄ = ε × first order + O(ε²)`, all first-order objects bounded),
then `W(ε) = t.i.p.(ε) − (ε²/2)·Ȳu_c·loss612(first-order solution) + O(ε³)`. -/
theorem prop612_layerB (hs : Tendsto s L (𝓝 0)) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {ωt : J → ℝ} (hωt0 : ∀ j, 0 ≤ ωt j) (hωt1 : ∑ j, ωt j = 1)
    {θp θw : ℝ} (hθp : θp ≠ 0) (hθp1 : θp ≠ 1) (hθw1 : θw ≠ 1)
    {u v : ℝ × Ξ → ℝ} (hu : ContDiff ℝ 3 u) (hv : ContDiff ℝ 3 v)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 3 G) (hG0 : G 0 = 1) {σi ω ν ωp φh Ybar Hbar : ℝ}
    (hG1 : fderiv ℝ G 0 1 = φh) (hG2 : fderiv ℝ (fderiv ℝ G) 0 1 1 = φh * (1 + ωp))
    (hω : ω = ωp + ν * φh) (hφ : φh ≠ 0) (hσω : σi + ω ≠ 0)
    (hucc : dYY u (Ybar, 0) = -(σi * dY u (Ybar, 0) / Ybar))
    (hvhh : dYY v (Hbar, 0) = ν * dY v (Hbar, 0) / Hbar)
    (hss : Hbar * dY v (Hbar, 0) * φh = Ybar * dY u (Ybar, 0))
    {yh y1 : B → ι → ℝ} {lw lw1 : B → J → ℝ} {a g hb af gf hbf Yf : B → ℝ} {xu xv : B → Ξ}
    (hg : ∀ b, dYXi u (Ybar, 0) (xu b) = σi * dY u (Ybar, 0) * g b)
    (hhb : ∀ b, dYXi v (Hbar, 0) (xv b) = -(ν * dY v (Hbar, 0) * hb b))
    (hyh : yh =O[L] fun b => s b ^ 1) (hlw : lw =O[L] fun b => s b ^ 1)
    (hxu : xu =O[L] fun b => s b ^ 1) (hxv : xv =O[L] fun b => s b ^ 1)
    (by1 : y1 =O[L] fun _ => (1 : ℝ)) (blw1 : lw1 =O[L] fun _ => (1 : ℝ))
    (ba : af =O[L] fun _ => (1 : ℝ)) (bg : gf =O[L] fun _ => (1 : ℝ))
    (bhb : hbf =O[L] fun _ => (1 : ℝ)) (bY : Yf =O[L] fun _ => (1 : ℝ))
    (hyd : (fun b => yh b - s b • y1 b) =O[L] fun b => s b ^ 2)
    (hlwd : (fun b => lw b - s b • lw1 b) =O[L] fun b => s b ^ 2)
    (had : (fun b => a b - s b * af b) =O[L] fun b => s b ^ 2)
    (hgd : (fun b => g b - s b * gf b) =O[L] fun b => s b ^ 2)
    (hhbd : (fun b => hb b - s b * hbf b) =O[L] fun b => s b ^ 2)
    (hYd : (fun b => logYidx w θp (yh b) - s b * Yf b) =O[L] fun b => s b ^ 2) :
    (fun b => periodU12 u v w ωt θp θw Ybar Hbar G (a b) (yh b) (lw b) (xu b) (xv b) -
      ((tip12 u v Ybar Hbar (xu b) (xv b) + Ybar * dY u (Ybar, 0) *
        StickyWageWelfare.tip612 σi ω ν 0 (g b) (a b) (hb b)) -
        s b ^ 2 / 2 * (Ybar * dY u (Ybar, 0) * loss612 σi ω ν θp ωp θw φh (gf b) (af b) (hbf b)
          (Yf b) (crossVar w (y1 b) / θp ^ 2) (crossVar ωt (lw1 b)))))
      =O[L] fun b => s b ^ 3 := by
  have fo : ∀ (x x1 : B → ℝ), (fun b => x b - s b * x1 b) =O[L] (fun b => s b ^ 2) →
      x1 =O[L] (fun _ => (1 : ℝ)) → x =O[L] fun b => s b ^ 1 := fun x x1 hd h1 =>
    ((o_weaken hs (by norm_num : 1 ≤ 2) hd).add
      (((isBigO_refl s L).mul h1).congr_right fun b => by ring)).congr_left fun b => by ring
  have hW := prop612_actual hs hw0 hw1 hωt0 hωt1 hθp hθp1 hθw1 hu hv hG hG0 hG1 hG2 hω hφ hσω
    hucc hvhh hss hg hhb hyh hlw (fo a af had ba) (fo g gf hgd bg) (fo hb hbf hhbd bhb) hxu hxv
  have hVp : (fun b => crossVar w (yh b) / θp ^ 2 - s b ^ 2 * (crossVar w (y1 b) / θp ^ 2))
      =O[L] fun b => s b ^ 3 :=
    ((crossVar_first_order hs hw0 hw1 hyd by1).const_mul_left (θp ^ 2)⁻¹).congr_left
      fun b => by ring
  have hL := loss612_first_order hs σi ω ν θp ωp θw φh hgd had hhbd hYd
    (Vp := fun b => crossVar w (yh b) / θp ^ 2) (Vpf := fun b => crossVar w (y1 b) / θp ^ 2)
    hVp (crossVar_first_order hs hωt0 hωt1 hlwd blw1) bg ba bhb bY
  exact bridge_first_order (hW.congr_left fun b => by ring) hL

/-- Woodford (2003), **Proposition 6.13**, (4.29), p. 445, LAYER B along a path: if the period
utility has the expansion of `prop612_actual` uniformly in the date
(`W = τ − (K/2)[(σ⁻¹+ω)(x − x*)² + θ_p(1+ω_pθ_p)Δ_p + θ_wφ_h⁻¹(1+νθ_w)Δ_w] + O(ε³)`), price and
wage dispersions follow the exact Calvo laws, first-order variables are uniformly `O(ε)`,
`Δ_p, Δ_w = O(ε²)` and `π̄ − π, π̄_w − π_w = O(ε²)`, then `∑βᵗW_t = −Ω∑βᵗL_t + t.i.p. + O(ε³)`
with `L` the loss (4.29) on the actual path (`StickyWageWelfare.prop_6_13` supplies the
identity). -/
theorem prop613_layerB {K σi ω θp ωp θw ν φh β αp αw xs : ℝ} (hap0 : 0 < αp) (hap1 : αp < 1)
    (haw0 : 0 < αw) (haw1 : αw < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθp : 0 < θp) (hθw : 0 < θw)
    (hφ : 0 < φh) (hωθ : 0 < 1 + ωp * θp) (hνθ : 0 < 1 + ν * θw) (hσω : 0 < σi + ω)
    (he : Tendsto e l (𝓝 0))
    {W τ x π πw pb wb Δp Δw : A → ℕ → ℝ} {Δpm Δwm : A → ℝ} (hτ : ∀ a, Sequences.Bdd (τ a))
    (hP : (fun p : A × ℕ => W p.1 p.2 - (τ p.1 p.2 - K / 2 * ((σi + ω) * (x p.1 p.2 - xs) ^ 2 +
      θp * (1 + ωp * θp) * Δp p.1 p.2 + θw / φh * (1 + ν * θw) * Δw p.1 p.2))) =O[l ×ˢ ⊤]
        fun p => e p.1 ^ 3)
    (hx : (fun p : A × ℕ => x p.1 p.2 - xs) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hπ : (fun p : A × ℕ => π p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hπw : (fun p : A × ℕ => πw p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 1)
    (hΔp : (fun p : A × ℕ => Δp p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2)
    (hΔw : (fun p : A × ℕ => Δw p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2)
    (hp : (fun p : A × ℕ => pb p.1 p.2 - π p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2)
    (hw : (fun p : A × ℕ => wb p.1 p.2 - πw p.1 p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2)
    (hp0 : ∀ a, Δp a 0 = αp * Δpm a + αp / (1 - αp) * pb a 0 ^ 2)
    (hps : ∀ a t, Δp a (t + 1) = αp * Δp a t + αp / (1 - αp) * pb a (t + 1) ^ 2)
    (hw0 : ∀ a, Δw a 0 = αw * Δwm a + αw / (1 - αw) * wb a 0 ^ 2)
    (hws : ∀ a t, Δw a (t + 1) = αw * Δw a t + αw / (1 - αw) * wb a (t + 1) ^ 2) :
    (fun a => ∑' t, β ^ t * W a t -
      (-(K / 2 * StickyWageWelfare.Dsum θp (Moments.calvoXi αp β ωp θp) θw φh
          (Moments.calvoXi αw β ν θw)) *
        ∑' t, β ^ t * StickyWageWelfare.loss429
          (StickyWageWelfare.lamP θp (Moments.calvoXi αp β ωp θp) θw φh
            (Moments.calvoXi αw β ν θw))
          (StickyWageWelfare.lamW θp (Moments.calvoXi αp β ωp θp) θw φh
            (Moments.calvoXi αw β ν θw))
          (StickyWageWelfare.lamX613 σi ω θp (Moments.calvoXi αp β ωp θp) θw φh
            (Moments.calvoXi αw β ν θw)) (π a t) (πw a t) (x a t) xs +
        (∑' t, β ^ t * τ a t - K / 2 * (θp * (1 + ωp * θp) * (αp * Δpm a / (1 - αp * β)) +
          θw / φh * (1 + ν * θw) * (αw * Δwm a / (1 - αw * β))))))
      =O[l] fun a => e a ^ 3 := by
  have hs := tendsto_amp (J := ℕ) he
  set R : A → ℕ → ℝ := fun a t => W a t - (τ a t - K / 2 * ((σi + ω) * (x a t - xs) ^ 2 +
      θp * (1 + ωp * θp) * Δp a t + θw / φh * (1 + ν * θw) * Δw a t)) with hR
  have pbO := ((o_weaken hs (by norm_num : 1 ≤ 2) hp).add hπ).congr_left fun p => by ring
  have wbO := ((o_weaken hs (by norm_num : 1 ≤ 2) hw).add hπw).congr_left fun p => by ring
  have sq : ∀ {pb π : A → ℕ → ℝ},
      (fun p : A × ℕ => pb p.1 p.2 - π p.1 p.2) =O[l ×ˢ ⊤] (fun p => e p.1 ^ 2) →
      (fun p : A × ℕ => π p.1 p.2) =O[l ×ˢ ⊤] (fun p => e p.1 ^ 1) →
      (fun p : A × ℕ => pb p.1 p.2 ^ 2 - π p.1 p.2 ^ 2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 3 :=
    fun {pb} {π} hd hπ => (o_mul hd ((o_weaken hs (by norm_num : 1 ≤ 2) hd).add
      (hπ.const_mul_left 2)) (by norm_num : 2 + 1 = 3)).congr_left fun p => by ring
  have bR := seq_bdd_of_o (f := R) he hP
  have bx := seq_bdd_of_o (f := fun a t => x a t - xs) he hx
  have bπ := seq_bdd_of_o he hπ
  have bπw := seq_bdd_of_o he hπw
  have bp := seq_bdd_of_o (f := pb) he pbO
  have bw := seq_bdd_of_o (f := wb) he wbO
  have bΔp := seq_bdd_of_o he hΔp
  have bΔw := seq_bdd_of_o he hΔw
  have hev : ∀ᶠ a in l, ∑' t, β ^ t * W a t -
      (-(K / 2 * StickyWageWelfare.Dsum θp (Moments.calvoXi αp β ωp θp) θw φh
          (Moments.calvoXi αw β ν θw)) *
        ∑' t, β ^ t * StickyWageWelfare.loss429
          (StickyWageWelfare.lamP θp (Moments.calvoXi αp β ωp θp) θw φh
            (Moments.calvoXi αw β ν θw))
          (StickyWageWelfare.lamW θp (Moments.calvoXi αp β ωp θp) θw φh
            (Moments.calvoXi αw β ν θw))
          (StickyWageWelfare.lamX613 σi ω θp (Moments.calvoXi αp β ωp θp) θw φh
            (Moments.calvoXi αw β ν θw)) (π a t) (πw a t) (x a t) xs +
        (∑' t, β ^ t * τ a t - K / 2 * (θp * (1 + ωp * θp) * (αp * Δpm a / (1 - αp * β)) +
          θw / φh * (1 + ν * θw) * (αw * Δwm a / (1 - αw * β))))) =
      ∑' t, β ^ t * R a t - K / 2 * (θp / Moments.calvoXi αp β ωp θp *
        ∑' t, β ^ t * (pb a t ^ 2 - π a t ^ 2) + θw / φh / Moments.calvoXi αw β ν θw *
          ∑' t, β ^ t * (wb a t ^ 2 - πw a t ^ 2)) := by
    filter_upwards [bR, bx, bπ, bπw, bp, bw, bΔp, bΔw] with a hRa hxa hπa hπwa hpa hwa hΔpa hΔwa
    have hxa' : Sequences.Bdd (x a) := by
      obtain ⟨M, hM⟩ := hxa
      exact ⟨M + |xs|, fun t => by
        have := abs_sub_abs_le_abs_sub (x a t) xs
        have := hM t
        linarith [abs_nonneg xs]⟩
    have h := StickyWageWelfare.prop_6_13 (U := W a) (tipU := τ a) (R := R a) (K := K)
      (xs := xs) (σi := σi) (ω := ω) (θp := θp) (ωp := ωp) (θw := θw) (ν := ν) (φh := φh)
      (β := β) (x := x a) (Δp := Δp a) (Δw := Δw a)
      hap0 hap1 haw0 haw1 hβ0 hβ1 hθp hθw hφ hωθ hνθ hσω (fun t => by simp only [hR]; ring)
      (hp0 a) (hps a) (hw0 a) (hws a) hxa' hπa hπwa hpa hwa hΔpa hΔwa (hτ a) hRa
    dsimp only at h
    rw [h]
    ring
  exact ((tsum_o hβ0 hβ1 (f := R) hP).sub
    ((((tsum_o hβ0 hβ1 (sq hp hπ)).const_mul_left (θp / Moments.calvoXi αp β ωp θp)).add
      ((tsum_o hβ0 hβ1 (sq hw hπw)).const_mul_left
        (θw / φh / Moments.calvoXi αw β ν θw))).const_mul_left (K / 2))).congr'
      (hev.mono fun a ha => ha.symm) (Eventually.of_forall fun _ => rfl)

/-- Woodford (2003), (4.25), p. 437 (Proposition 6.11 with a first-order solution): along a
path whose first-order solution is `(π₁¹, π₂¹, (x − x*)¹, (p̂_R − p̂_Rⁿ)¹)` (bounded, each variable
`= ε × first order + O(ε²)` uniformly), `∑βᵗL_t = ε²∑βᵗL_t(first-order solution) + O(ε³)`;
with `prop611_layerB` and `discounted_first_order` this is the first-order form of
Proposition 6.11. -/
theorem loss425_first_order {w1 w2 lx lR xs β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (he : Tendsto e l (𝓝 0)) {π1 π2 x gR : A → ℕ → ℝ} {π1f π2f xgf gRf : ℕ → ℝ}
    (b1 : Sequences.Bdd π1f) (b2 : Sequences.Bdd π2f) (b3 : Sequences.Bdd xgf)
    (b4 : Sequences.Bdd gRf)
    (h1 : (fun p : A × ℕ => π1 p.1 p.2 - e p.1 * π1f p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2)
    (h2 : (fun p : A × ℕ => π2 p.1 p.2 - e p.1 * π2f p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2)
    (h3 : (fun p : A × ℕ => (x p.1 p.2 - xs) - e p.1 * xgf p.2) =O[l ×ˢ ⊤]
      fun p => e p.1 ^ 2)
    (h4 : (fun p : A × ℕ => gR p.1 p.2 - e p.1 * gRf p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2) :
    (fun a => ∑' t, β ^ t * TwoSectorWelfare.loss425 w1 w2 lx lR (π1 a t) (π2 a t) (x a t) xs
        (gR a t) -
      e a ^ 2 * ∑' t, β ^ t * TwoSectorWelfare.loss425 w1 w2 lx lR (π1f t) (π2f t)
        (xgf t + xs) xs (gRf t)) =O[l] fun a => e a ^ 3 := by
  have h := tsum_sq_first_order ![w1, w2, lx, lR] hβ0 hβ1 he
    (z := ![π1, π2, fun a t => x a t - xs, gR]) (z1 := ![π1f, π2f, xgf, gRf])
    (fun k => by fin_cases k <;> assumption) (fun k => by
      fin_cases k
      · simpa using h1
      · simpa using h2
      · simpa using h3
      · simpa using h4)
  refine h.congr_left fun a => ?_
  simp only [TwoSectorWelfare.loss425, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, add_sub_cancel_right]

/-- Woodford (2003), (4.29), p. 445 (Proposition 6.13 with a first-order solution): along a
path whose first-order solution is `(π¹, π_w¹, (x − x*)¹)` (bounded, each variable
`= ε × first order + O(ε²)` uniformly), `∑βᵗL_t = ε²∑βᵗL_t(first-order solution) + O(ε³)`;
with `prop613_layerB` and `discounted_first_order` this is the first-order form of
Proposition 6.13. -/
theorem loss429_first_order {lp lw lx xs β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (he : Tendsto e l (𝓝 0)) {π πw x : A → ℕ → ℝ} {πf πwf xgf : ℕ → ℝ}
    (b1 : Sequences.Bdd πf) (b2 : Sequences.Bdd πwf) (b3 : Sequences.Bdd xgf)
    (h1 : (fun p : A × ℕ => π p.1 p.2 - e p.1 * πf p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2)
    (h2 : (fun p : A × ℕ => πw p.1 p.2 - e p.1 * πwf p.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ 2)
    (h3 : (fun p : A × ℕ => (x p.1 p.2 - xs) - e p.1 * xgf p.2) =O[l ×ˢ ⊤]
      fun p => e p.1 ^ 2) :
    (fun a => ∑' t, β ^ t * StickyWageWelfare.loss429 lp lw lx (π a t) (πw a t) (x a t) xs -
      e a ^ 2 * ∑' t, β ^ t * StickyWageWelfare.loss429 lp lw lx (πf t) (πwf t) (xgf t + xs) xs)
      =O[l] fun a => e a ^ 3 := by
  have h := tsum_sq_first_order ![lp, lw, lx] hβ0 hβ1 he
    (z := ![π, πw, fun a t => x a t - xs]) (z1 := ![πf, πwf, xgf])
    (fun k => by fin_cases k <;> assumption) (fun k => by
      fin_cases k
      · simpa using h1
      · simpa using h2
      · simpa using h3)
  refine h.congr_left fun a => ?_
  simp only [StickyWageWelfare.loss429, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    add_sub_cancel_right]

/-- Woodford (2003), §1, p. 385 (a finite state space of paths): if the welfare expansion holds
along every path `ω` (`W(ω) − V(ω) = O(ε³)`), it holds for expected welfare
`E[W] − E[V] = O(ε³)` (`OneParamTaylor.isBigO_expect`); this turns the path-wise Layer-B
statements (`prop68_layerB`, `prop611_layerB`, `prop613_layerB`) into statements about
expected discounted utility `E_0 ∑βᵗU_t`. -/
theorem expect_layerB {Ω' : Type*} [Fintype Ω'] (p : Ω' → ℝ) {W V : A → Ω' → ℝ}
    (h : ∀ ω, (fun a => W a ω - V a ω) =O[l] fun a => e a ^ 3) :
    (fun a => OneParamTaylor.expect p (W a) - OneParamTaylor.expect p (V a))
      =O[l] fun a => e a ^ 3 :=
  (OneParamTaylor.isBigO_expect p h).congr_left fun a => by
    rw [← OneParamTaylor.expect_sub]

/-! ## One-parameter families: a `C²` curve satisfies the order hypotheses

The theorems above are stated for any family with explicit order bounds. A one-parameter `C²`
(in particular `C³`) family through the steady state satisfies them, with first-order solution
its derivative at `ε = 0` (cf. `OneParamTaylor.secondDeriv_param_curve_indep`: the second-order
welfare term depends on the curve only through this first derivative). -/

/-- Woodford (2003), §1, pp. 385–389 (survey §4, B1): a `C²` curve through `0` is
`f(ε) = εf′(0) + O(ε²)`: its first-order solution is `f′(0)`. -/
theorem curve_first_order {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (h0 : f 0 = 0) :
    (fun ε => f ε - ε * deriv f 0) =O[𝓝 0] fun ε => ε ^ 2 :=
  (OneParamTaylor.taylor_one_bigO hf.contDiffAt).congr (fun ε => by rw [h0]; ring)
    (fun ε => by ring)

/-- Woodford (2003), §1, p. 385: a `C²` curve through `0` is `O(ε)`. -/
theorem curve_o {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (h0 : f 0 = 0) :
    f =O[𝓝 0] fun ε => ε ^ 1 :=
  ((o_weaken (s := fun ε : ℝ => ε) tendsto_id (by norm_num : 1 ≤ 2)
    (curve_first_order hf h0)).add ((isBigO_refl (fun ε : ℝ => ε ^ 1) (𝓝 0)).const_mul_left
      (deriv f 0))).congr_left (fun ε => by ring)

/-- Woodford (2003), App. E.1: a cross-section moving along `C²` curves through `0` is
`ŷ(ε) = εŷ′(0) + O(ε²)` in the sup norm. -/
theorem curve_first_order_pi {f : ℝ → ι → ℝ} (hf : ∀ i, ContDiff ℝ 2 fun ε => f ε i)
    (h0 : ∀ i, f 0 i = 0) :
    (fun ε => f ε - ε • fun i => deriv (fun ε => f ε i) 0) =O[𝓝 0] fun ε => ε ^ 2 := by
  rw [isBigO_pi]
  intro i
  simpa using curve_first_order (hf i) (h0 i)

end Woodford.StabilizationWelfare.BridgeExtensions
