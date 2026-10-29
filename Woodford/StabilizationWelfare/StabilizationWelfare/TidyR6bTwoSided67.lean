/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR6bAlongModel

/-!
# Propositions 6.7–6.8 without the one-sided satiation hypothesis

Woodford (2003), *Interest and Prices*, Chapter 6, §4.1, Propositions 6.7–6.8, (4.9)–(4.10),
pp. 422–423, Assumption 6.1, and Appendix E.4.

`BridgeExtensions.prop67_actual` and
`SmoothInSigmaMeasureProps.prop67_measure`/`SmoothInSigmaMeasureProps.prop68_measure`
expand the ACTUAL utility, flat above satiation, using its smooth extension from below; they
need real balances at or below satiation along the family (`hleft`). Along a perturbation
equilibrium this holds only if real balances do not move at first order
(`TidyR6bAlongModel.hleft_first_order_zero`, `TidyR6bAlongModel.hleft_money_demand`). Here are the
two-sided
versions, for a utility that is `C³` THROUGH satiation (restated from those modules; the only
change is the two-sided Taylor family `BridgeExtensions.taylor_family`):

* **`TidyR6bTwoSided67.Family.prop67_smooth`**,
  **`TidyR6bTwoSided67.Family.prop67_layerB_smooth`**: Layer B of Proposition 6.7 along any family,
  real balances on either side of `m̄`.
* **`prop67_measure_smooth`**, **`prop68_measure_smooth`**: Propositions 6.7 and 6.8 along the
  perturbation equilibrium on the i.i.d. probability space, without `hleft`.
* **`prop68_model_smooth`**: Proposition 6.8 along the equilibrium of a model, two-sided, with
  the Calvo law of dispersion and the discrepancy derived from the model.
-/

namespace Woodford.StabilizationWelfare.TidyR6bTwoSided67

open Filter Topology Asymptotics MeasureTheory
open ExpLogCES (crossMean crossVar expRem rlog)
open BridgeExtensions

namespace Family

variable {B : Type*} {L : Filter B} {s : B → ℝ}
variable {Ξ : Type*} [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]
variable {ι : Type*} [Fintype ι]

/-- Woodford (2003), **Proposition 6.7**, eq. (4.9), p. 422, LAYER B, TWO-SIDED (restated from
`BridgeExtensions.prop67_actual` without the one-sided hypothesis): the utility `Ũ` of output,
real balances and disturbances is `C³` through satiation, `ũ_m(m̄) = 0`; `v` is `C³`; the
coefficients at the
efficient satiated steady state `(Ȳ, m̄, 0)` define `σ⁻¹`, `χ`, `s_mσ_m⁻¹ = (η_iv̄)⁻¹`, `ω` and
the composite disturbances `g`, `εᵐ`, `q` (`h11`–`hq`); `η_y = χη_iv̄` there ((E.16)). Along any
family with `ŷ(i), m̂, î − îᵐ, ξ = O(s)` and the money-demand residual `O(s²)`, with real
balances on EITHER side of satiation, the period utility is
`t.i.p. + Ȳu_c[tip − ½(4.9)] + O(s³)`, with the quadratic form (4.9)
`Ω_mc(Ŷ − Ŷⁿ)² + v̄⁻¹η_i(î − îᵐ)² + (θ⁻¹ + ω) var_i ŷ`. -/
theorem prop67_smooth (hs : Tendsto s L (𝓝 0)) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {θ : ℝ} (hθ : θ ≠ 1) {Ut : ℝ × ℝ × Ξ → ℝ} (hUt : ContDiff ℝ 3 Ut)
    {mbar : ℝ} (hmbar : 0 < mbar)
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
 :
    (fun b => periodUT Ut v w θ Ybar mbar (yh b) (mh b) (xu b) (xv b) -
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
  -- (1) the two-sided Taylor expansion of `Ũ` at satiation
  have hU1 := taylor_family hUt z0 hs
    (z := fun b => (Ybar * (Real.exp (Yh b) - 1), mbar * (Real.exp (mh b) - 1), xu b))
    ((lev Ybar Yh hYO).prod_left ((lev mbar mh hmh).prod_left hxu))
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


/-- Woodford (2003), **Proposition 6.7**, eq. (4.9), p. 422, LAYER B, TWO-SIDED (restated from
`BridgeExtensions.prop67_layerB`): under the hypotheses of
`TidyR6bTwoSided67.Family.prop67_smooth`, if the family has
the first-order solution
`(ŷ₁(i), Ŷ₁, (î − îᵐ)₁, g₁, q₁, εᵐ₁)` (`ŷ = εŷ₁ + O(ε²)` etc., all first-order objects bounded),
then the actual period utility is
`W(ε) = t.i.p.(ε) − (ε²/2)·Ȳu_c·(4.9)(first-order solution) + O(ε³)`, where the t.i.p.
`tipT + Ȳu_c·Transactions.tip` depends on the disturbances only. -/
theorem prop67_layerB_smooth (hs : Tendsto s L (𝓝 0)) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {θ : ℝ} (hθ : θ ≠ 1) {Ut : ℝ × ℝ × Ξ → ℝ} (hUt : ContDiff ℝ 3 Ut)
    {mbar : ℝ} (hmbar : 0 < mbar)
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
    (hy1 : y1 =O[L] fun _ => (1 : ℝ)) (hY1 : Y1 =O[L] fun _ => (1 : ℝ))
    (hd1 : d1 =O[L] fun _ => (1 : ℝ)) (hg1 : g1 =O[L] fun _ => (1 : ℝ))
    (hq1 : q1 =O[L] fun _ => (1 : ℝ)) (heps1 : eps1 =O[L] fun _ => (1 : ℝ))
    (hyd : (fun b => yh b - s b • y1 b) =O[L] fun b => s b ^ 2)
    (hYd : (fun b => logYidx w θ (yh b) - s b * Y1 b) =O[L] fun b => s b ^ 2)
    (hdd : (fun b => d b - s b * d1 b) =O[L] fun b => s b ^ 2)
    (hgd : (fun b => g b - s b * g1 b) =O[L] fun b => s b ^ 2)
    (hqd : (fun b => q b - s b * q1 b) =O[L] fun b => s b ^ 2)
    (hepsd : (fun b => eps b - s b * eps1 b) =O[L] fun b => s b ^ 2) :
    (fun b => periodUT Ut v w θ Ybar mbar (yh b) (mh b) (xu b) (xv b) -
      ((tipT Ut v Ybar mbar (xu b) (xv b) + Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) *
        Transactions.tip P (g b) (q b) (eps b) 0 0) -
        s b ^ 2 / 2 * (Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) * Transactions.loss49 P
          (txSat P (Y1 b) (d1 b) (g1 b) (q1 b) (eps1 b) (crossVar w (y1 b)) 0))))
      =O[L] fun b => s b ^ 3 := by
  have fo : ∀ (x x1 : B → ℝ), (fun b => x b - s b * x1 b) =O[L] (fun b => s b ^ 2) →
      x1 =O[L] (fun _ => (1 : ℝ)) → x =O[L] fun b => s b ^ 1 := fun x x1 hd h1 =>
    ((o_weaken hs (by norm_num : 1 ≤ 2) hd).add
      (((isBigO_refl s L).mul h1).congr_right fun b => by ring)).congr_left fun b => by ring
  have hW := prop67_smooth hs hw0 hw1 hθ hUt hmbar hv P hθi hey hΩ hi hvb hsat h11 h12 h22
    hvy hvyy hg heps hq hyh hmh (fo d d1 hdd hd1) (fo g g1 hgd hg1) (fo q q1 hqd hq1)
    (fo eps eps1 hepsd heps1) hxu hxv hr
  have hL := loss49_first_order hs P (m := mh) (m1 := fun _ => 0) hYd hdd hgd hqd hepsd
    (crossVar_first_order hs hw0 hw1 hyd hy1) hY1 hd1 hg1 hq1 heps1
  exact bridge_first_order (hW.congr_left fun b => by ring) hL



end Family

open Family
open SmoothInSigmaMeasure (Hist adSub)
open SmoothInSigma (Bd pbar norm_apply_le)
open SmoothInSigmaMeasurePath (histOf)
open SmoothInSigmaMeasureWelfare (ypath y1path readout_first readout_second readout_bdd)
open SmoothInSigmaMeasureProps
open BridgeExtensions (UProc)

variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Woodford (2003), **Proposition 6.7**, eq. (4.9), p. 422, ALONG THE EQUILIBRIUM on the i.i.d.
probability space, TWO-SIDED (restated from `SmoothInSigmaMeasureProps.prop67_measure` without
`hleft`, for a utility that is `C³` through satiation): under the hypotheses of
`TidyR6bTwoSided67.Family.prop67_layerB_smooth` on preferences, let the decision vector carry,
through `C²`
readouts vanishing at `ȳ`, log outputs, real balances `m̂`, the interest differential, the
composite disturbances and the shocks. The model's equations are the composites (`hg`, `heps`,
`hq`) and the money demand `m̂ = M(Ŷ, î − îᵐ, εᵐ)` (eq. (4.1)); real balances may lie on
either side of satiation. Then the actual period utility is
`t.i.p. − (ε²/2)·Ȳu_c·loss49(first-order solution) + O(ε³)` UNIFORMLY in the date and the path;
the money-demand residual is of second order (`SmoothInSigmaMeasureProps.fderiv_money_residual`). -/
theorem prop67_measure_smooth {ι Ξ : Type} [Fintype ι] [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]
    {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {θ : ℝ} (hθ : θ ≠ 1)
    {Ut : ℝ × ℝ × Ξ → ℝ} (hUt : ContDiff ℝ 3 Ut) {mbar : ℝ} (hmbar : 0 < mbar)
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
    (hvy : BridgeExtensions.dY v (Ybar, 0) = fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0))
    (hvyy : BridgeExtensions.dYY v (Ybar, 0) = P.omega * BridgeExtensions.dY v (Ybar, 0) / Ybar)
    {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = SmoothInSigmaMeasure.MModel.ubar ybar)
    (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    {yhR : Y → ι → ℝ} {mhR dR gR qR epsR : Y → ℝ} {xuR xvR : Y → Ξ}
    (cyh : ContDiffAt ℝ 2 yhR ybar) (cmh : ContDiffAt ℝ 2 mhR ybar)
    (cd : ContDiffAt ℝ 2 dR ybar) (cg : ContDiffAt ℝ 2 gR ybar) (cq : ContDiffAt ℝ 2 qR ybar)
    (ceps : ContDiffAt ℝ 2 epsR ybar) (cxu : ContDiffAt ℝ 2 xuR ybar)
    (cxv : ContDiffAt ℝ 2 xvR ybar)
    (zyh : yhR ybar = 0) (zmh : mhR ybar = 0) (zd : dR ybar = 0) (zg : gR ybar = 0)
    (zq : qR ybar = 0) (zeps : epsR ybar = 0) (zxu : xuR ybar = 0) (zxv : xvR ybar = 0)
    (hg : ∀ y, fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (0, 0, xuR y) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xuR y) (1, 0, 0) =
        2 * (P.sigInv * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) * gR y))
    (heps : ∀ y, fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (0, 0, xuR y) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xuR y) (0, 1, 0) =
        2 * (Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / (P.etaI * P.vbar) / mbar * epsR y))
    (hq : ∀ y, BridgeExtensions.dYXi v (Ybar, 0) (xvR y) =
      -(P.omega * BridgeExtensions.dY v (Ybar, 0) * qR y))
    {mdem : ℝ × ℝ × ℝ → ℝ} {Lmd : ℝ × ℝ × ℝ →L[ℝ] ℝ}
    (hLmd : ∀ a b c, Lmd (a, b, c) = P.etaY * a - P.etaI * b + c)
    (hmd : HasFDerivAt mdem Lmd 0)
    (hm : ∀ y, mhR y = mdem (BridgeExtensions.logYidx w θ (yhR y), dR y, epsR y))
 :
    UProc (𝓝 0) (fun ε t ω' => rem67 Ut Ut v w θ Ybar mbar P (yhR (ypath ψ ybar ε t ω'))
      (mhR (ypath ψ ybar ε t ω')) (xuR (ypath ψ ybar ε t ω')) (xvR (ypath ψ ybar ε t ω'))
      (gR (ypath ψ ybar ε t ω')) (qR (ypath ψ ybar ε t ω')) (epsR (ypath ψ ybar ε t ω'))
      (fderiv ℝ (fun y => BridgeExtensions.logYidx w θ (yhR y)) ybar (y1path ψ ybar t ω'))
      (fderiv ℝ dR ybar (y1path ψ ybar t ω')) (fderiv ℝ gR ybar (y1path ψ ybar t ω'))
      (fderiv ℝ qR ybar (y1path ψ ybar t ω')) (fderiv ℝ epsR ybar (y1path ψ ybar t ω'))
      (fderiv ℝ yhR ybar (y1path ψ ybar t ω')) ε) fun ε => ε ^ 3 := by
  have hs : Tendsto (fun b : ℝ × (ℕ × (ℕ → ℝ)) => b.1)
      ((𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ × (ℕ → ℝ)))) (𝓝 0) := tendsto_fst
  have cY := SmoothInSigmaMeasureWelfare.contDiffAt_logYidx hw1 θ cyh zyh
  have zY : (fun y => BridgeExtensions.logYidx w θ (yhR y)) ybar = 0 := by
    simp only [zyh]; exact SmoothInSigmaMeasureWelfare.logYidx_zero hw1 θ
  have cT : ContDiffAt ℝ 2 (fun y => (BridgeExtensions.logYidx w θ (yhR y), dR y, epsR y))
      ybar := cY.prodMk (cd.prodMk ceps)
  have hres := fderiv_money_residual hLmd hmd ((cT.differentiableAt (by norm_num)).hasFDerivAt)
    (by simp only [zY, zd, zeps]; rfl) hm
  have cr : ContDiffAt ℝ 2 (fun y => mhR y - (P.etaY * BridgeExtensions.logYidx w θ (yhR y) -
      P.etaI * dR y + epsR y)) ybar :=
    cmh.sub (((contDiffAt_const.mul cY).sub (contDiffAt_const.mul cd)).add ceps)
  have zr : (fun y => mhR y - (P.etaY * BridgeExtensions.logYidx w θ (yhR y) -
      P.etaI * dR y + epsR y)) ybar = 0 := by
    simp only [zmh, zd, zeps]
    rw [show BridgeExtensions.logYidx w θ (yhR ybar) = 0 from zY]
    ring
  have hr : (fun b : ℝ × (ℕ × (ℕ → ℝ)) => mhR (ypath ψ ybar b.1 b.2.1 b.2.2) -
      (P.etaY * BridgeExtensions.logYidx w θ (yhR (ypath ψ ybar b.1 b.2.1 b.2.2)) -
        P.etaI * dR (ypath ψ ybar b.1 b.2.1 b.2.2) + epsR (ypath ψ ybar b.1 b.2.1 b.2.2)))
      =O[(𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ × (ℕ → ℝ)))] fun b => b.1 ^ 2 := by
    refine (readout_second hbase hψ2 cr zr).congr_left fun b => ?_
    simp only [hres, zero_apply, smul_zero, sub_zero]
  exact prop67_layerB_smooth hs hw0 hw1 hθ hUt hmbar hv P hθi hey hΩ hi hvb hsat
    h11 h12 h22 hvy hvyy (fun b => hg _) (fun b => heps _) (fun b => hq _)
    (readout_first hbase hψ2 cyh zyh) (readout_first hbase hψ2 cmh zmh)
    (readout_first hbase hψ2 cxu zxu) (readout_first hbase hψ2 cxv zxv) hr
    (readout_bdd ψ ybar yhR) (readout_bdd ψ ybar _) (readout_bdd ψ ybar dR)
    (readout_bdd ψ ybar gR) (readout_bdd ψ ybar qR) (readout_bdd ψ ybar epsR)
    (readout_second hbase hψ2 cyh zyh) (readout_second hbase hψ2 cY zY)
    (readout_second hbase hψ2 cd zd) (readout_second hbase hψ2 cg zg)
    (readout_second hbase hψ2 cq zq) (readout_second hbase hψ2 ceps zeps)


/-- Woodford (2003), **Proposition 6.8**, (4.10), p. 423, ALONG THE EQUILIBRIUM on the i.i.d.
probability space, TWO-SIDED (restated from `SmoothInSigmaMeasureProps.prop68_measure` without
`hleft`): under the hypotheses of `prop67_measure_smooth`, with in addition inflation `π`,
mean-price inflation `π̄` and relative prices as `C²` readouts vanishing at `ȳ`, and along the
equilibrium (small amplitudes) the exact Calvo law of price dispersion (`Δ = var_i ŷ/θ²`) and
the mean/index discrepancy, `E[∑βᵗU_t] = E[∑βᵗ t.i.p._t − (K/2)θ(1+ωθ)k∑βᵗL_t] + O(ε³)`, with
`L` the loss (4.10) on the actual path; real balances may lie on either side of satiation. -/
theorem prop68_measure_smooth [FiniteDimensional ℝ Y] (ν0 : ProbabilityMeasure ℝ) {ι Ξ : Type}
    [Fintype ι] [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]
    {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {θ α β : ℝ} (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {Ut : ℝ × ℝ × Ξ → ℝ} (hUt : ContDiff ℝ 3 Ut) {mbar : ℝ} (hmbar : 0 < mbar)
    {v : ℝ × Ξ → ℝ} (hv : ContDiff ℝ 3 v) {Ybar : ℝ}
    (P : Transactions.TxParams) (hθi : P.thetaInv = θ⁻¹)
    (hey : P.etaY = P.chi * P.etaI * P.vbar) (hΩ : 0 < Transactions.omegaMC P)
    (hωP : 0 ≤ P.omega) (hi : P.etaI ≠ 0) (hvb : P.vbar ≠ 0)
    (hsat : fderiv ℝ Ut (Ybar, mbar, 0) (0, 1, 0) = 0)
    (h11 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (1, 0, 0) =
      -(P.sigInv * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / Ybar))
    (h12 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (0, 1, 0) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (1, 0, 0) =
        2 * (P.chi * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / mbar))
    (h22 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (0, 1, 0) =
      -(Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / (P.etaI * P.vbar) / mbar ^ 2))
    (hvy : BridgeExtensions.dY v (Ybar, 0) = fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0))
    (hvyy : BridgeExtensions.dYY v (Ybar, 0) = P.omega * BridgeExtensions.dY v (Ybar, 0) / Ybar)
    {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = SmoothInSigmaMeasure.MModel.ubar ybar)
    (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    {yhR rpR : Y → ι → ℝ} {mhR dR gR qR epsR inflR pibR : Y → ℝ} {xuR xvR : Y → Ξ}
    (cyh : ContDiffAt ℝ 2 yhR ybar) (crp : ContDiffAt ℝ 2 rpR ybar)
    (cmh : ContDiffAt ℝ 2 mhR ybar)
    (cd : ContDiffAt ℝ 2 dR ybar) (cg : ContDiffAt ℝ 2 gR ybar) (cq : ContDiffAt ℝ 2 qR ybar)
    (ceps : ContDiffAt ℝ 2 epsR ybar) (ci : ContDiffAt ℝ 2 inflR ybar)
    (cp : ContDiffAt ℝ 2 pibR ybar) (cxu : ContDiffAt ℝ 2 xuR ybar)
    (cxv : ContDiffAt ℝ 2 xvR ybar)
    (zyh : yhR ybar = 0) (zrp : rpR ybar = 0) (zmh : mhR ybar = 0) (zd : dR ybar = 0)
    (zg : gR ybar = 0) (zq : qR ybar = 0) (zeps : epsR ybar = 0) (zi : inflR ybar = 0)
    (zp : pibR ybar = 0) (zxu : xuR ybar = 0) (zxv : xvR ybar = 0)
    (hg : ∀ y, fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (0, 0, xuR y) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xuR y) (1, 0, 0) =
        2 * (P.sigInv * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) * gR y))
    (heps : ∀ y, fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (0, 0, xuR y) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xuR y) (0, 1, 0) =
        2 * (Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / (P.etaI * P.vbar) / mbar * epsR y))
    (hq : ∀ y, BridgeExtensions.dYXi v (Ybar, 0) (xvR y) =
      -(P.omega * BridgeExtensions.dY v (Ybar, 0) * qR y))
    {mdem : ℝ × ℝ × ℝ → ℝ} {Lmd : ℝ × ℝ × ℝ →L[ℝ] ℝ}
    (hLmd : ∀ a b c, Lmd (a, b, c) = P.etaY * a - P.etaI * b + c)
    (hmd : HasFDerivAt mdem Lmd 0)
    (hm : ∀ y, mhR y = mdem (BridgeExtensions.logYidx w θ (yhR y), dR y, epsR y))
    (hlaw : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t ω',
      crossVar w (yhR (ypath ψ ybar ε t ω')) / θ ^ 2 = α * (crossVar w (yhR (match t with
        | 0 => ybar
        | k + 1 => ypath ψ ybar ε k ω')) / θ ^ 2) + α / (1 - α) * pibR (ypath ψ ybar ε t ω') ^ 2)
    (hdisc : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t ω',
      pibR (ypath ψ ybar ε t ω') - inflR (ypath ψ ybar ε t ω') =
        discF w θ (fun i => rpR (ypath ψ ybar ε t ω') i + inflR (ypath ψ ybar ε t ω'))
          (rpR (match t with
            | 0 => ybar
            | k + 1 => ypath ψ ybar ε k ω'))) :
    (fun ε => ∫ ω', rem68 Ut Ut v w α β θ Ybar mbar P (fun t => yhR (ypath ψ ybar ε t ω'))
      (fun t => mhR (ypath ψ ybar ε t ω')) (fun t => xuR (ypath ψ ybar ε t ω'))
      (fun t => xvR (ypath ψ ybar ε t ω')) (fun t => dR (ypath ψ ybar ε t ω'))
      (fun t => gR (ypath ψ ybar ε t ω')) (fun t => qR (ypath ψ ybar ε t ω'))
      (fun t => epsR (ypath ψ ybar ε t ω')) (fun t => inflR (ypath ψ ybar ε t ω'))
      ∂(ExpectationsMeasureIID.iidSystem ν0).μ) =O[𝓝 0] fun ε => ε ^ 3 := by
  classical
  set L2 := ((𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ → ℝ))) ×ˢ (⊤ : Filter ℕ) with hL2
  set K := Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) with hK
  have hs2 : Tendsto (fun b : (ℝ × (ℕ → ℝ)) × ℕ => b.1.1) L2 (𝓝 0) :=
    tendsto_fst.comp tendsto_fst
  -- the period expansion along the path, from Proposition 6.7
  have cY := SmoothInSigmaMeasureWelfare.contDiffAt_logYidx hw1 θ cyh zyh
  have zY : (fun y => BridgeExtensions.logYidx w θ (yhR y)) ybar = 0 := by
    simp only [zyh]; exact SmoothInSigmaMeasureWelfare.logYidx_zero hw1 θ
  have cT : ContDiffAt ℝ 2 (fun y => (BridgeExtensions.logYidx w θ (yhR y), dR y, epsR y))
      ybar := cY.prodMk (cd.prodMk ceps)
  have hres := fderiv_money_residual hLmd hmd ((cT.differentiableAt (by norm_num)).hasFDerivAt)
    (by simp only [zY, zd, zeps]; rfl) hm
  have cr : ContDiffAt ℝ 2 (fun y => mhR y - (P.etaY * BridgeExtensions.logYidx w θ (yhR y) -
      P.etaI * dR y + epsR y)) ybar :=
    cmh.sub (((contDiffAt_const.mul cY).sub (contDiffAt_const.mul cd)).add ceps)
  have zr : (fun y => mhR y - (P.etaY * BridgeExtensions.logYidx w θ (yhR y) -
      P.etaI * dR y + epsR y)) ybar = 0 := by
    simp only [zmh, zd, zeps]
    rw [show BridgeExtensions.logYidx w θ (yhR ybar) = 0 from zY]
    ring
  have hr : UProc (𝓝 0) (fun ε t ω => mhR (ypath ψ ybar ε t ω) -
      (P.etaY * BridgeExtensions.logYidx w θ (yhR (ypath ψ ybar ε t ω)) -
        P.etaI * dR (ypath ψ ybar ε t ω) + epsR (ypath ψ ybar ε t ω))) fun ε => ε ^ 2 := by
    refine (readout_second hbase hψ2 cr zr).congr_left fun b => ?_
    simp only [hres, zero_apply, smul_zero, sub_zero]
  have h67 := prop67_smooth (L := L2) (s := fun b => b.1.1) hs2 hw0 hw1 hθ1
    hUt hmbar hv P hθi hey hΩ.ne' hi hvb hsat h11 h12 h22 hvy hvyy
    (yh := fun b => yhR (ypath ψ ybar b.1.1 b.2 b.1.2))
    (mh := fun b => mhR (ypath ψ ybar b.1.1 b.2 b.1.2))
    (d := fun b => dR (ypath ψ ybar b.1.1 b.2 b.1.2))
    (g := fun b => gR (ypath ψ ybar b.1.1 b.2 b.1.2))
    (q := fun b => qR (ypath ψ ybar b.1.1 b.2 b.1.2))
    (eps := fun b => epsR (ypath ψ ybar b.1.1 b.2 b.1.2))
    (xu := fun b => xuR (ypath ψ ybar b.1.1 b.2 b.1.2))
    (xv := fun b => xvR (ypath ψ ybar b.1.1 b.2 b.1.2))
    (fun b => hg _) (fun b => heps _) (fun b => hq _)
    (uproc_lift2 (readout_first hbase hψ2 cyh zyh)) (uproc_lift2 (readout_first hbase hψ2 cmh zmh))
    (uproc_lift2 (readout_first hbase hψ2 cd zd)) (uproc_lift2 (readout_first hbase hψ2 cg zg))
    (uproc_lift2 (readout_first hbase hψ2 cq zq))
    (uproc_lift2 (readout_first hbase hψ2 ceps zeps))
    (uproc_lift2 (readout_first hbase hψ2 cxu zxu))
    (uproc_lift2 (readout_first hbase hψ2 cxv zxv)) (uproc_lift2 hr)
  -- second-order dispersion and discrepancy
  have cD : ContDiffAt ℝ 2 (fun y => crossVar w (yhR y) / θ ^ 2) ybar :=
    (contDiffAt_crossVar w cyh).div_const _
  have hpO := disc_second_order hw0 hw1 hθ1 hbase hψ2 crp ci zrp zi hdisc
  -- uniform bounds for small amplitudes
  have cτ : ContDiffAt ℝ 2 (fun y => (xuR y, xvR y, gR y, qR y, epsR y)) ybar :=
    cxu.prodMk (cxv.prodMk (cg.prodMk (cq.prodMk ceps)))
  have zτ : (fun y => (xuR y, xvR y, gR y, qR y, epsR y)) ybar = 0 := by
    simp [zxu, zxv, zg, zq, zeps]
  obtain ⟨Mτ, hMτ⟩ := eventually_bdd_comp (uproc_lift2 (readout_first hbase hψ2 cτ zτ))
    (φ := fun x => BridgeExtensions.tipT Ut v Ybar mbar x.1 x.2.1 +
      K * Transactions.tip P x.2.2.1 x.2.2.2.1 x.2.2.2.2 0 0)
    (((continuous_tipT Ut v Ybar mbar).comp (continuous_fst.prodMk
      (continuous_fst.comp continuous_snd))).add (continuous_const.mul (by
        unfold Transactions.tip Transactions.natRate Transactions.xStar Transactions.sM
        fun_prop))).continuousAt
  obtain ⟨Mp, hMp⟩ := eventually_bdd_comp (uproc_lift2 (readout_first hbase hψ2 cp zp))
    (φ := fun x => x) continuous_id.continuousAt
  obtain ⟨MV, hMV⟩ := eventually_bdd_comp (uproc_lift2 (readout_first hbase hψ2 cyh zyh))
    (φ := fun x => crossVar w x) (by unfold crossVar ExpLogCES.crossMean; fun_prop)
  obtain ⟨ρ, hρ, hρs⟩ := Metric.eventually_nhds_iff.1 hlaw
  set Pm : ℝ × (ℕ → ℝ) → Prop := fun a => dist a.1 0 < ρ ∧
    (∀ t, |BridgeExtensions.tipT Ut v Ybar mbar (xuR (ypath ψ ybar a.1 t a.2)) (xvR
        (ypath ψ ybar a.1 t a.2)) +
      K * Transactions.tip P (gR (ypath ψ ybar a.1 t a.2)) (qR (ypath ψ ybar a.1 t a.2)) (epsR
          (ypath ψ ybar a.1 t a.2)) 0 0| ≤ Mτ) ∧
    (∀ t, |pibR (ypath ψ ybar a.1 t a.2)| ≤ Mp) ∧ (∀ t, |crossVar w (yhR
        (ypath ψ ybar a.1 t a.2))| ≤ MV) with hPmd
  have hPm : ∀ᶠ a in (𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ → ℝ)), Pm a :=
    (tendsto_fst.eventually (Metric.ball_mem_nhds (0 : ℝ) hρ)).and (hMτ.and (hMp.and hMV))
  set W : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if Pm a then BridgeExtensions.periodUT Ut v w θ
    Ybar mbar (yhR (ypath ψ ybar a.1 t a.2)) (mhR (ypath ψ ybar a.1 t a.2)) (xuR
        (ypath ψ ybar a.1 t a.2)) (xvR (ypath ψ ybar a.1 t a.2)) else 0 with hW
  set τ : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if Pm a then
    BridgeExtensions.tipT Ut v Ybar mbar (xuR (ypath ψ ybar a.1 t a.2)) (xvR
        (ypath ψ ybar a.1 t a.2)) +
      K * Transactions.tip P (gR (ypath ψ ybar a.1 t a.2)) (qR (ypath ψ ybar a.1 t a.2)) (epsR
          (ypath ψ ybar a.1 t a.2)) 0 0 else 0 with hτd
  set Yv : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if Pm a then
    BridgeExtensions.logYidx w θ (yhR (ypath ψ ybar a.1 t a.2)) else 0 with hYv
  set dv : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if Pm a then dR
      (ypath ψ ybar a.1 t a.2) else 0 with hdv
  set gv : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if Pm a then gR
      (ypath ψ ybar a.1 t a.2) else 0 with hgv
  set qv : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if Pm a then qR
      (ypath ψ ybar a.1 t a.2) else 0 with hqv
  set ev : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if Pm a then epsR
      (ypath ψ ybar a.1 t a.2) else 0 with hev
  set Vv : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if Pm a then crossVar w (yhR
      (ypath ψ ybar a.1 t a.2)) else 0 with hVv
  set pv : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if Pm a then pibR
      (ypath ψ ybar a.1 t a.2) else 0 with hpv
  set iv : ℝ × (ℕ → ℝ) → ℕ → ℝ := fun a t => if Pm a then inflR
      (ypath ψ ybar a.1 t a.2) else 0 with hiv
  have hτb : ∀ a, Sequences.Bdd (τ a) := fun a => ⟨max Mτ 0, fun t => by
    by_cases h : Pm a
    · simp only [hτd, h, ↓reduceIte]; exact (h.2.1 t).trans (le_max_left _ _)
    · simp [hτd, h]⟩
  have hPc : (fun p : (ℝ × (ℕ → ℝ)) × ℕ => W p.1 p.2 - (τ p.1 p.2 - K * Transactions.loss49 P
      (BridgeExtensions.txSat P (Yv p.1 p.2) (dv p.1 p.2) (gv p.1 p.2) (qv p.1 p.2)
        (ev p.1 p.2) (Vv p.1 p.2) 0) / 2)) =O[L2] fun p => p.1.1 ^ 3 := by
    refine h67.congr' ?_ (Eventually.of_forall fun _ => rfl)
    filter_upwards [tendsto_fst.eventually hPm] with b hb
    simp only [hW, hτd, hYv, hdv, hgv, hqv, hev, hVv, hb, ↓reduceIte]
    simp only [Transactions.loss49, BridgeExtensions.txSat]
    ring
  have m1 : ∀ {R : Y → ℝ}, ContDiffAt ℝ 2 R ybar → R ybar = 0 →
      (fun p : (ℝ × (ℕ → ℝ)) × ℕ => if Pm p.1 then R (ypath ψ ybar p.1.1 p.2 p.1.2) else 0)
        =O[L2] fun p => p.1.1 ^ 1 := fun {R} hR hR0 =>
    isBigO_mask2 (uproc_lift2 (readout_first hbase hψ2 hR hR0)) hPm
  have hpp : (fun p : (ℝ × (ℕ → ℝ)) × ℕ => pv p.1 p.2 - iv p.1 p.2) =O[L2]
      fun p => p.1.1 ^ 2 := by
    refine (isBigO_mask2 (uproc_lift2 hpO) hPm).congr_left fun p => ?_
    by_cases h : Pm p.1 <;> simp [hpv, hiv, h]
  have hθ' : P.thetaInv = 1 / θ := by rw [hθi, one_div]
  have hVs : ∀ a, HasSum (fun t => β ^ t * Vv a t)
      (θ ^ 2 * (Moments.calvoK α β * ∑' t, β ^ t * pv a t ^ 2 + (fun _ => (0 : ℝ)) a)) :=
    fun a => by
    by_cases h : Pm a
    · have hbdd : Sequences.Bdd (pv a) := ⟨Mp, fun t => by
        simp only [hpv, h, ↓reduceIte]; exact h.2.2.1 t⟩
      have hrec : ∀ t, Vv a t / θ ^ 2 = α * Sequences.lagS 0 (fun t => Vv a t / θ ^ 2) t +
          α / (1 - α) * pv a t ^ 2 := fun t => by
        have hl := (hρs h.1) t a.2
        cases t with
        | zero =>
          simp only [hVv, hpv, h, ↓reduceIte, Sequences.lagS_zero]
          rw [hl, zyh, crossVar_zero, zero_div, mul_zero]
        | succ k =>
          simp only [hVv, hpv, h, ↓reduceIte, Sequences.lagS_succ]
          exact hl
      have hd := Sequences.disp_discounted hβ0 hβ1 hα0.le hα1 hbdd hrec
      have hsum : Summable fun t => β ^ t * Vv a t := by
        refine Sequences.Bdd.summable (a := Vv a) ⟨MV, fun t => ?_⟩ hβ0 hβ1
        simp only [hVv, h, ↓reduceIte]; exact h.2.2.2 t
      convert hsum.hasSum using 1
      have hθ2 : θ ^ 2 ≠ 0 := by positivity
      have h2 : ∑' t, β ^ t * Vv a t = θ ^ 2 * ∑' t, β ^ t * (Vv a t / θ ^ 2) := by
        rw [← tsum_mul_left]
        congr 1
        funext t
        field_simp
      rw [h2, hd, Moments.calvoK]
      have hab : 1 - α * β ≠ 0 := by nlinarith
      have ha1 : 1 - α ≠ 0 := by linarith
      field_simp
      ring
    · have h0 : ∀ t, Vv a t = 0 := fun t => by simp [hVv, h]
      have h1 : ∀ t, pv a t = 0 := fun t => by simp [hpv, h]
      simp only [h0, h1, mul_zero]
      simp
  have hcore := BridgeExtensions.prop68_layerB (K := K) (T0 := fun _ => (0 : ℝ))
    (l := (𝓝 (0 : ℝ)) ×ˢ (⊤ : Filter (ℕ → ℝ))) (e := fun a => a.1) P hα0 hα1 hβ0 hβ1 hθ hθ'
    hωP hΩ hvb tendsto_fst hτb hPc
    ((m1 cY zY).congr_left fun p => rfl) (m1 cd zd) (m1 cg zg) (m1 cq zq) (m1 ceps zeps)
    (m1 ci zi) hpp hVs
  refine integral_isBigO _ (hcore.congr' ?_ (Eventually.of_forall fun _ => rfl))
  filter_upwards [hPm] with a ha
  simp only [hW, hτd, hYv, hdv, hgv, hqv, hev, hiv, ha, ↓reduceIte, rem68, mul_zero, add_zero, hK]


open SmoothInSigmaMeasure (MModel) in
/-- **Woodford (2003), Proposition 6.8, (4.10), p. 423, along the equilibrium OF A MODEL,
TWO-SIDED**: as `prop68_measure_smooth` (no one-sided satiation hypothesis, a utility `C³` through
satiation), with the Calvo law of dispersion and the mean-price discrepancy derived from the
model's period conditions (`TidyR6bAlongModel.static_on_path`). -/
theorem prop68_model_smooth [FiniteDimensional ℝ Y] {Z : Type} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [CompleteSpace Z] (ν0 : ProbabilityMeasure ℝ) {ι Ξ : Type}
    [Fintype ι] [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]
    {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {θ α β : ℝ} (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {Ut : ℝ × ℝ × Ξ → ℝ} (hUt : ContDiff ℝ 3 Ut) {mbar : ℝ} (hmbar : 0 < mbar)
    {v : ℝ × Ξ → ℝ} (hv : ContDiff ℝ 3 v) {Ybar : ℝ}
    (P : Transactions.TxParams) (hθi : P.thetaInv = θ⁻¹)
    (hey : P.etaY = P.chi * P.etaI * P.vbar) (hΩ : 0 < Transactions.omegaMC P)
    (hωP : 0 ≤ P.omega) (hi : P.etaI ≠ 0) (hvb : P.vbar ≠ 0)
    (hsat : fderiv ℝ Ut (Ybar, mbar, 0) (0, 1, 0) = 0)
    (h11 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (1, 0, 0) =
      -(P.sigInv * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / Ybar))
    (h12 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (0, 1, 0) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (1, 0, 0) =
        2 * (P.chi * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / mbar))
    (h22 : fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (0, 1, 0) =
      -(Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / (P.etaI * P.vbar) / mbar ^ 2))
    (hvy : BridgeExtensions.dY v (Ybar, 0) = fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0))
    (hvyy : BridgeExtensions.dYY v (Ybar, 0) = P.omega * BridgeExtensions.dY v (Ybar, 0) / Ybar)
    {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} {ybar : Y}
    {N : MModel Unit Y Z} (hN : N.Std) (hc : Continuous N.f) (hψ : N.LocalSol ybar ψ)
    (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    {yhR rpR : Y → ι → ℝ} {mhR dR gR qR epsR inflR pibR : Y → ℝ} {xuR xvR : Y → Ξ}
    (cyh : ContDiffAt ℝ 2 yhR ybar) (crp : ContDiffAt ℝ 2 rpR ybar)
    (cmh : ContDiffAt ℝ 2 mhR ybar)
    (cd : ContDiffAt ℝ 2 dR ybar) (cg : ContDiffAt ℝ 2 gR ybar) (cq : ContDiffAt ℝ 2 qR ybar)
    (ceps : ContDiffAt ℝ 2 epsR ybar) (ci : ContDiffAt ℝ 2 inflR ybar)
    (cp : ContDiffAt ℝ 2 pibR ybar) (cxu : ContDiffAt ℝ 2 xuR ybar)
    (cxv : ContDiffAt ℝ 2 xvR ybar)
    (zyh : yhR ybar = 0) (zrp : rpR ybar = 0) (zmh : mhR ybar = 0) (zd : dR ybar = 0)
    (zg : gR ybar = 0) (zq : qR ybar = 0) (zeps : epsR ybar = 0) (zi : inflR ybar = 0)
    (zp : pibR ybar = 0) (zxu : xuR ybar = 0) (zxv : xvR ybar = 0)
    (hg : ∀ y, fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (1, 0, 0) (0, 0, xuR y) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xuR y) (1, 0, 0) =
        2 * (P.sigInv * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) * gR y))
    (heps : ∀ y, fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 1, 0) (0, 0, xuR y) +
      fderiv ℝ (fderiv ℝ Ut) (Ybar, mbar, 0) (0, 0, xuR y) (0, 1, 0) =
        2 * (Ybar * fderiv ℝ Ut (Ybar, mbar, 0) (1, 0, 0) / (P.etaI * P.vbar) / mbar * epsR y))
    (hq : ∀ y, BridgeExtensions.dYXi v (Ybar, 0) (xvR y) =
      -(P.omega * BridgeExtensions.dY v (Ybar, 0) * qR y))
    {mdem : ℝ × ℝ × ℝ → ℝ} {Lmd : ℝ × ℝ × ℝ →L[ℝ] ℝ}
    (hLmd : ∀ a b c, Lmd (a, b, c) = P.etaY * a - P.etaI * b + c)
    (hmd : HasFDerivAt mdem Lmd 0)
    (hm : ∀ y, mhR y = mdem (BridgeExtensions.logYidx w θ (yhR y), dR y, epsR y))
    (πD πP : Z →L[ℝ] ℝ)
    (hπD : ∀ a b c x e, πD (N.f (a, b, c, x, e)) = crossVar w (yhR b) / θ ^ 2 -
      (α * (crossVar w (yhR c) / θ ^ 2) + α / (1 - α) * pibR b ^ 2))
    (hπP : ∀ a b c x e, πP (N.f (a, b, c, x, e)) =
      pibR b - inflR b - discF w θ (fun i => rpR b i + inflR b) (rpR c)) :
    (fun ε => ∫ ω', rem68 Ut Ut v w α β θ Ybar mbar P (fun t => yhR (ypath ψ ybar ε t ω'))
      (fun t => mhR (ypath ψ ybar ε t ω')) (fun t => xuR (ypath ψ ybar ε t ω'))
      (fun t => xvR (ypath ψ ybar ε t ω')) (fun t => dR (ypath ψ ybar ε t ω'))
      (fun t => gR (ypath ψ ybar ε t ω')) (fun t => qR (ypath ψ ybar ε t ω'))
      (fun t => epsR (ypath ψ ybar ε t ω')) (fun t => inflR (ypath ψ ybar ε t ω'))
      ∂(ExpectationsMeasureIID.iidSystem ν0).μ) =O[𝓝 0] fun ε => ε ^ 3  := by
  have hlaw := TidyR6bAlongModel.static_on_path hN hc hψ πD hπD
  have hdisc := TidyR6bAlongModel.static_on_path hN hc hψ πP hπP
  refine prop68_measure_smooth ν0 hw0 hw1 hθ hθ1 hα0 hα1 hβ0 hβ1 hUt hmbar hv P hθi hey hΩ hωP hi
    hvb hsat h11 h12 h22 hvy hvyy hψ.base hψ2 cyh crp cmh cd cg cq ceps ci cp cxu cxv zyh zrp
    zmh zd zg zq zeps zi zp zxu zxv hg heps hq hLmd hmd hm ?_ ?_
  · filter_upwards [hlaw] with ε h t ω
    have := h t ω
    cases t <;> (simp only at this ⊢; linarith)
  · filter_upwards [hdisc] with ε h t ω
    have := h t ω
    cases t <;> (simp only at this ⊢; linarith)

end Woodford.StabilizationWelfare.TidyR6bTwoSided67
