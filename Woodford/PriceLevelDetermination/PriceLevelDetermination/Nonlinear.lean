/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.LocalIFT
import PriceLevelDetermination.NonSeparable
import PriceLevelDetermination.Transversality

/-!
# Nonlinear local determinacy for Chapter 2, §2.3 and §3

Woodford (2003), *Interest and Prices*, Chapter 2, §2.3 (Props. 2.7–2.8, pp. 94–97) and §3
(Props. 2.11–2.13, pp. 103–117), with Appendix A.3 (pp. 630–635) and A.7, A.8, A.11–A.13
(pp. 639–646). The linear modules prove these propositions for the log-linear models; the book's
statements are about the **exact** model ("there is also a locally unique solution to the exact
equilibrium relations", A.11, p. 645; "accurate up to a residual of order `O(ξ²)`"). This
module proves the exact perfect-foresight versions on `ℓ∞`.

## Generic theory

The general implicit-function machinery for the class `F(x_t, x_{t+1}, e_t) = 0` (vector
disturbances `e_t`, local `C¹`/`C²` hypotheses via a bump cut-off) lives in `LocalIFT`
(`LocalIFT.local_determinacy_loc`, `LocalIFT.second_order_loc`, `LocalIFT.local_indeterminacy_loc`,
`LocalIFT.linSol3`, `LocalIFT.isUnit_TOp_iff`, ...). This module adds:

* Inverting a nonlinear inertial rule `ĵ_t = ψ(π_t, ĵ_{t−1}, ν_t)` for inflation near the steady
  state (`solveRule`, `solveRule_local`, `contDiffAt_solveRule`, `hasFDerivAt_solveRule`).

## Applications (exact perfect-foresight models)

* **Prop. 2.11** (money-growth targeting): `MGEq` ((1.21), (3.3) ⟺ (3.5) by
  `mg_money_demand_iff`), `FMG`, `hasFDerivAt_FMG`, `mg_local_determinacy`,
  `mg_smooth_dependence`, `mg_second_order` ((A.30)), `mg_priceLevel_second_order` ((3.7));
  coefficients equal the money-demand elasticities of (3.6): `mg_coeffs_eq`, `lm_partials3`.
* **(1.21) → (3.11)** as an exact derivative: `euler311`, `euler_iff_euler311`,
  `hasFDerivAt_euler311`; with (3.5) substituted: `lamI`, `hasFDerivAt_lamI`, `lamI_coeffs`
  (`∂λ/∂ĵ = −χη_i`, the source of (3.12)).
* **Prop. 2.12** (Wicksellian rule, non-separable utility): `NSWEq`, `FW`, `slopes_FW`
  (`a = A212`, `b = −B212`), `nsw_local_determinacy` (exact condition `|B| < |A|`),
  `prop_2_12_exact` (under (3.16)), `nsw_local_indeterminacy`, `nsw_smooth_dependence`,
  `linSol3_FW_apply`, `nsw_second_order` ((3.17)).
* **Prop. 2.13** (inertial rule, non-separable utility): `NSIEq`, `F13`, `slopes_F13`
  (`γ₀/φ_π`, `−γ₁/φ_π`), `nsi_local_determinacy`, `prop_2_13_cond`, `nsi_local_indeterminacy`,
  `nsi_smooth_dependence`, `linSol3_F13_apply`, `nsi_second_order` ((3.20)).
* **Prop. 2.8** (inertial rule, cashless): `InertialEq`, `F8`, `slopes_F8`,
  `inertial_local_determinacy`, `inertial_local_indeterminacy`, `prop_2_8_cond`,
  `inertial_smooth_dependence`, `linSol3_F8_apply`, `inertial_second_order` ((2.15)).
* **Prop. 2.7** (rule on smoothed inflation): `SmoothEq`, `F7`, `slopes_F7`,
  `smooth_local_determinacy`, `smooth_local_indeterminacy`, `prop_2_7_cond`,
  `smooth_smooth_dependence`, `linSol3_F7_apply`, `smooth_second_order` ((2.10)).
* Transversality: `tvc_iff_tvcDebt` (`LocalIFT.TVC` is `Equilibrium.TVCDebt` under perfect
  foresight).

All `O(ξ²)` statements assume `C²` (erratum E18, `LocalIFT.not_second_order_of_C1`). Boundary
cases `|a| = |b|` are not decided by the linearisation and are not claimed. The stochastic `L∞`
version is not treated.
-/

namespace Woodford.PriceLevelDetermination.Nonlinear

open scoped ENNReal Topology
open Woodford.PriceLevelDetermination.LocalIFT (Linf mk mk_apply abs_apply_le norm_le_of_abs_le
  Seq mkS mkS_apply norm_seq_le Solves slopeA slopeB slopeC ne_zero_of_abs_lt linSol3
  linSol3_apply local_determinacy_loc second_order_loc local_indeterminacy_loc
  slopes_of_hasFDerivAt)

/-! ### Proposition 2.11: money-growth targeting (§3.3, pp. 106–108; A.11, pp. 644–645)

Exact perfect-foresight model with additively separable utility: (1.21)
`1 + i_t = u_c(t)/(β u_c(t+1)) · P_{t+1}/P_t` (with `u_c(t) = u_c(Y_t; ξ_t)` exogenous), and the
money-demand condition (3.3) `u_m/u_c (Y_t, M_t/P_t; ξ_t) = Δ_t = (i_t − iᵐ_t)/(1 + i_t)`, which
is (3.5) `M_t/P_t = L(Y_t, Δ_t; ξ_t)` solved for `Δ_t` (`mg_money_demand_iff`), given exogenous
`{Mˢ_t, iᵐ_t}`. In `x_t = log(M_t/(P_t m̄))` (log real balances) it is the scalar forward
equation `(1 − R(Ȳe^{ŷ}, m̄eˣ, ξ)) e^{x + w} − β(1 + īᵐ) e^{x'} = 0`, with
`w_t = r̂_t + μ_{t+1} − îᵐ_t` (`r̂_t = log(u_c(t)/u_c(t+1))`, `μ_{t+1} = log(M_{t+1}/M_t)`,
`îᵐ_t = log((1 + iᵐ_t)/(1 + īᵐ))`). `R = u_m/u_c` is the inverse of `L` in `Δ`. -/

/-- Woodford (2003), (3.3) and (1.21), pp. 72, 104, A.11 p. 644: the exact period equilibrium
condition of money-growth targeting in `(x_t, x_{t+1}, (ŷ_t, ξ_t, w_t))`. -/
noncomputable def FMG (β ibm Ybar mbar : ℝ) (R : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ × (ℝ × ℝ × ℝ)) :
    ℝ :=
  (1 - R (Ybar * Real.exp p.2.2.1, mbar * Real.exp p.1, p.2.2.2.1)) *
    Real.exp (p.1 + p.2.2.2.2) - β * (1 + ibm) * Real.exp p.2.1

/-- Woodford (2003), p. 106: at the steady state `u_m/u_c(Ȳ, m̄; 0) = Δ̄ = 1 − β(1 + īᵐ)`, the
period condition holds with no disturbances. -/
theorem FMG_zero {β ibm Ybar mbar : ℝ} {R : ℝ × ℝ × ℝ → ℝ}
    (hss : R (Ybar, mbar, 0) = 1 - β * (1 + ibm)) : FMG β ibm Ybar mbar R 0 = 0 := by
  simp [FMG, hss]

/-- Woodford (2003), (3.3), p. 104: if `u_m/u_c` is `Cⁿ` near the steady state, so is the
period condition. -/
theorem contDiffAt_FMG {β ibm Ybar mbar : ℝ} {R : ℝ × ℝ × ℝ → ℝ} {n : ℕ}
    (hR : ContDiffAt ℝ n R (Ybar, mbar, 0)) : ContDiffAt ℝ n (FMG β ibm Ybar mbar R) 0 := by
  have hg : ContDiff ℝ n (fun p : ℝ × ℝ × (ℝ × ℝ × ℝ) =>
      ((Ybar * Real.exp p.2.2.1, mbar * Real.exp p.1, p.2.2.2.1) : ℝ × ℝ × ℝ)) := by
    fun_prop
  have hg0 : (fun p : ℝ × ℝ × (ℝ × ℝ × ℝ) =>
      ((Ybar * Real.exp p.2.2.1, mbar * Real.exp p.1, p.2.2.2.1) : ℝ × ℝ × ℝ)) 0 =
      (Ybar, mbar, 0) := by simp
  have hR' : ContDiffAt ℝ n R ((fun p : ℝ × ℝ × (ℝ × ℝ × ℝ) =>
      ((Ybar * Real.exp p.2.2.1, mbar * Real.exp p.1, p.2.2.2.1) : ℝ × ℝ × ℝ)) 0) := by
    rw [hg0]
    exact hR
  have hc := hR'.comp (0 : ℝ × ℝ × (ℝ × ℝ × ℝ)) hg.contDiffAt
  have he1 : ContDiffAt ℝ n (fun p : ℝ × ℝ × (ℝ × ℝ × ℝ) => Real.exp (p.1 + p.2.2.2.2)) 0 := by
    fun_prop
  have he2 : ContDiffAt ℝ n (fun p : ℝ × ℝ × (ℝ × ℝ × ℝ) => β * (1 + ibm) * Real.exp p.2.1) 0 := by
    fun_prop
  exact ((contDiffAt_const.sub hc).mul he1).sub he2

/-- Woodford (2003), (3.6) and (A.29), pp. 107, 645, **exact derivative of the money-growth
equilibrium condition** at the steady state: with `R_Y, R_m, R_ξ` the partials of `u_m/u_c`,
`DF(x, x', (ŷ, ξ, w)) = β(1 + īᵐ)(x + w) − m̄ R_m x − Ȳ R_Y ŷ − R_ξ ξ − β(1 + īᵐ) x'`. -/
theorem hasFDerivAt_FMG {β ibm Ybar mbar : ℝ} {R : ℝ × ℝ × ℝ → ℝ}
    (hR : DifferentiableAt ℝ R (Ybar, mbar, 0)) (hss : R (Ybar, mbar, 0) = 1 - β * (1 + ibm)) :
    ∃ F' : ℝ × ℝ × (ℝ × ℝ × ℝ) →L[ℝ] ℝ, HasFDerivAt (FMG β ibm Ybar mbar R) F' 0 ∧
      ∀ x x' y z w : ℝ, F' (x, x', (y, z, w)) = β * (1 + ibm) * (x + w) -
        mbar * fderiv ℝ R (Ybar, mbar, 0) (0, 1, 0) * x -
        Ybar * fderiv ℝ R (Ybar, mbar, 0) (1, 0, 0) * y -
        fderiv ℝ R (Ybar, mbar, 0) (0, 0, 1) * z - β * (1 + ibm) * x' := by
  set D := fderiv ℝ R (Ybar, mbar, 0) with hD
  let G := ℝ × ℝ × (ℝ × ℝ × ℝ)
  let X1 : G →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ × ℝ × ℝ)
  let X2 : G →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ × ℝ)).comp
    (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ × ℝ))
  let S3 : G →L[ℝ] ℝ × ℝ × ℝ := (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ)).comp
    (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ × ℝ))
  let Y1 : G →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp S3
  let Z1 : G →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp S3)
  let W1 : G →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp S3)
  have hYe := (Y1.hasFDerivAt (x := 0)).exp.const_mul Ybar
  have hMe := (X1.hasFDerivAt (x := 0)).exp.const_mul mbar
  have hg := hYe.prodMk (hMe.prodMk (Z1.hasFDerivAt (x := 0)))
  have hg0 : ((Ybar * Real.exp (Y1 0), mbar * Real.exp (X1 0), Z1 0) : ℝ × ℝ × ℝ) =
      (Ybar, mbar, 0) := by simp
  have hR' : HasFDerivAt R D ((Ybar * Real.exp (Y1 0), mbar * Real.exp (X1 0), Z1 0)) := by
    rw [hg0]
    exact hR.hasFDerivAt
  have hc := hR'.comp (0 : G) hg
  have h1 := ((hc.const_sub 1).mul ((X1.hasFDerivAt (x := 0)).add
    (W1.hasFDerivAt (x := 0))).exp).sub ((X2.hasFDerivAt (x := 0)).exp.const_mul (β * (1 + ibm)))
  refine ⟨_, h1, fun x x' y z w => ?_⟩
  simp only [sub_apply, add_apply, smul_apply, neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, smul_eq_mul]
  rw [MoneyGrowth.clm3_apply]
  simp [X1, X2, S3, Y1, Z1, W1, hss]
  ring

/-- Woodford (2003), (A.29), p. 645: the slopes of the money-growth condition:
`a = β(1 + īᵐ) − m̄ R_m`, `b = −β(1 + īᵐ)`, `c(ŷ, ξ, w) = −Ȳ R_Y ŷ − R_ξ ξ + β(1 + īᵐ) w`. -/
theorem slopes_FMG {β ibm Ybar mbar : ℝ} {R : ℝ × ℝ × ℝ → ℝ}
    (hR : DifferentiableAt ℝ R (Ybar, mbar, 0)) (hss : R (Ybar, mbar, 0) = 1 - β * (1 + ibm)) :
    slopeA (FMG β ibm Ybar mbar R) =
        β * (1 + ibm) - mbar * fderiv ℝ R (Ybar, mbar, 0) (0, 1, 0) ∧
      slopeB (FMG β ibm Ybar mbar R) = -(β * (1 + ibm)) ∧
      ∀ y z w : ℝ, slopeC (FMG β ibm Ybar mbar R) (y, z, w) =
        -(Ybar * fderiv ℝ R (Ybar, mbar, 0) (1, 0, 0) * y) -
          fderiv ℝ R (Ybar, mbar, 0) (0, 0, 1) * z + β * (1 + ibm) * w := by
  obtain ⟨F', hF', hv⟩ := hasFDerivAt_FMG hR hss
  obtain ⟨ha, hb, hc⟩ := slopes_of_hasFDerivAt hF'
  refine ⟨?_, ?_, fun y z w => by rw [hc, hv]; ring⟩
  · rw [ha]
    change F' (1, 0, ((0 : ℝ), (0 : ℝ), (0 : ℝ))) = _
    rw [hv]
    ring
  · rw [hb]
    change F' (0, 1, ((0 : ℝ), (0 : ℝ), (0 : ℝ))) = _
    rw [hv]
    ring


/-- Woodford (2003), Definition p. 105 with (1.21), (3.3), p. 104, perfect foresight, separable
utility: a **money-growth-targeting equilibrium** is a positive price level `P` and an interest
rate `i` with `1 + i_t = u_c(t)/(β u_c(t+1)) · P_{t+1}/P_t` and
`u_m/u_c(Y_t, M_t/P_t; ξ_t) = (i_t − iᵐ_t)/(1 + i_t)` for all `t ≥ 0`, given exogenous `u_c > 0`,
`Mˢ > 0`, `iᵐ`, `Y`, `ξ`. (The transversality conditions (1.24), (3.4) are not imposed, as in
the book's proof, A.11 p. 644.) -/
def MGEq (β : ℝ) (R : ℝ × ℝ × ℝ → ℝ) (uc M im Y ξ P i : ℕ → ℝ) : Prop :=
  (∀ t, 0 < P t) ∧ (∀ t, 1 + i t = uc t / (β * uc (t + 1)) * (P (t + 1) / P t)) ∧
    ∀ t, R (Y t, M t / P t, ξ t) = (i t - im t) / (1 + i t)

/-- Woodford (2003), A.11, p. 644: the composite disturbance `w_t = r̂_t + μ_{t+1} − îᵐ_t` of the
money-growth model, `r̂_t = log(u_c(t)/u_c(t+1))`, `μ_{t+1} = log(M_{t+1}/M_t)`,
`îᵐ_t = log((1 + iᵐ_t)/(1 + īᵐ))`. -/
noncomputable def wMG (ibm : ℝ) (uc M im : ℕ → ℝ) (t : ℕ) : ℝ :=
  Real.log (uc t / uc (t + 1)) + Real.log (M (t + 1) / M t) - Real.log ((1 + im t) / (1 + ibm))

/-- Woodford (2003), (3.3)–(3.5), p. 104: with `L` the solution of `u_m/u_c(Y, m; ξ) = Δ` (fn. 38)
and `u_m/u_c` strictly decreasing in real balances, the conditions (3.5) `m = L(Y, Δ; ξ)` and
(3.3) `u_m/u_c(Y, m; ξ) = Δ` are equivalent for `m > 0` (so `MGEq` is the book's definition with
(3.5)). -/
theorem mg_money_demand_iff {R L : ℝ × ℝ × ℝ → ℝ} {Y Δ ξ m : ℝ}
    (hanti : StrictAntiOn (fun m' => R (Y, m', ξ)) (Set.Ioi 0)) (hL : 0 < L (Y, Δ, ξ))
    (hLsol : R (Y, L (Y, Δ, ξ), ξ) = Δ) (hm : 0 < m) : m = L (Y, Δ, ξ) ↔ R (Y, m, ξ) = Δ := by
  constructor
  · rintro rfl
    exact hLsol
  · intro h
    exact MoneyGrowth.lm_unique (R := fun m' => R (Y, m', ξ)) hanti hm hL h hLsol

/-- Woodford (2003), (3.3) and (1.21), A.11 p. 644: one date of the money-growth equilibrium
conditions, in levels and as the period condition `FMG = 0` in log real balances. -/
theorem mg_step {β ibm Ybar mbar : ℝ} {R : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β) (hibm : 0 < 1 + ibm)
    (hYb : 0 < Ybar) (hm : 0 < mbar) {P0 P1 M0 M1 u0 u1 Y ξ im i : ℝ} (hP0 : 0 < P0)
    (hP1 : 0 < P1) (hM0 : 0 < M0) (hM1 : 0 < M1) (hu0 : 0 < u0) (hu1 : 0 < u1) (hY : 0 < Y)
    (him : 0 < 1 + im) (hi : 1 + i = u0 / (β * u1) * (P1 / P0)) :
    R (Y, M0 / P0, ξ) = (i - im) / (1 + i) ↔
      FMG β ibm Ybar mbar R (Real.log (M0 / (P0 * mbar)), Real.log (M1 / (P1 * mbar)),
        (Real.log (Y / Ybar), ξ, Real.log (u0 / u1) + Real.log (M1 / M0) -
          Real.log ((1 + im) / (1 + ibm)))) = 0 := by
  have e1 : Ybar * Real.exp (Real.log (Y / Ybar)) = Y := by
    rw [Real.exp_log (by positivity)]
    field_simp
  have e2 : mbar * Real.exp (Real.log (M0 / (P0 * mbar))) = M0 / P0 := by
    rw [Real.exp_log (by positivity)]
    field_simp
  have e3 : Real.exp (Real.log (M0 / (P0 * mbar)) + (Real.log (u0 / u1) + Real.log (M1 / M0) -
      Real.log ((1 + im) / (1 + ibm)))) =
      M0 / (P0 * mbar) * (u0 / u1 * (M1 / M0) / ((1 + im) / (1 + ibm))) := by
    rw [Real.exp_add, Real.exp_sub, Real.exp_add, Real.exp_log (by positivity),
      Real.exp_log (by positivity), Real.exp_log (by positivity), Real.exp_log (by positivity)]
  have e4 : Real.exp (Real.log (M1 / (P1 * mbar))) = M1 / (P1 * mbar) :=
    Real.exp_log (by positivity)
  simp only [FMG]
  rw [e1, e2, e3, e4]
  set r := R (Y, M0 / P0, ξ) with hr
  set A := M0 / (P0 * mbar) * (u0 / u1 * (M1 / M0) / ((1 + im) / (1 + ibm))) with hA
  have hApos : 0 < A := by positivity
  have hI : 0 < 1 + i := by rw [hi]; positivity
  have key : β * (1 + ibm) * (M1 / (P1 * mbar)) = A * ((1 + im) / (1 + i)) := by
    rw [hA, hi]
    field_simp
  rw [key]
  constructor
  · intro h
    rw [h]
    field_simp
    ring
  · intro h
    have h2 : (1 - r - (1 + im) / (1 + i)) * A = 0 := by linarith
    have h3 : 1 - r - (1 + im) / (1 + i) = 0 :=
      (mul_eq_zero.mp h2).resolve_right hApos.ne'
    field_simp
    field_simp at h3
    linarith

/-- Woodford (2003), A.11, p. 644: `|w_t| ≤ 3δ` when `r̂`, `μ`, `îᵐ` are each within `δ`. -/
theorem abs_wMG_le {ibm δ : ℝ} {uc M im : ℕ → ℝ} (hr : ∀ t, |Real.log (uc t / uc (t + 1))| ≤ δ)
    (hμ : ∀ t, |Real.log (M (t + 1) / M t)| ≤ δ)
    (him : ∀ t, |Real.log ((1 + im t) / (1 + ibm))| ≤ δ) (t : ℕ) :
    |wMG ibm uc M im t| ≤ 3 * δ := by
  have h1 := hr t
  have h2 := hμ t
  have h3 := him t
  simp only [wMG]
  have := abs_add_le (Real.log (uc t / uc (t + 1))) (Real.log (M (t + 1) / M t))
  have := abs_sub (Real.log (uc t / uc (t + 1)) + Real.log (M (t + 1) / M t))
    (Real.log ((1 + im t) / (1 + ibm)))
  linarith

/-- Woodford (2003), App. A.3, p. 632: a triple whose coordinates are bounded by `K` has norm at
most `K`. -/
theorem norm_triple_le {a b c K : ℝ} (ha : |a| ≤ K) (hb : |b| ≤ K) (hc : |c| ≤ K) :
    ‖((a, b, c) : ℝ × ℝ × ℝ)‖ ≤ K := by
  rw [norm_prod_le_iff, norm_prod_le_iff, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
  exact ⟨ha, hb, hc⟩

/-- Woodford (2003), A.11, p. 644: the disturbance sequence `(ŷ_t, ξ_t, w_t)` of the money-growth
model as an element of `ℓ∞(ℝ³)`, given a uniform bound. -/
noncomputable def eMG (Ybar ibm : ℝ) (uc M im Y ξ : ℕ → ℝ) (K : ℝ)
    (hK : ∀ t, ‖((Real.log (Y t / Ybar), ξ t, wMG ibm uc M im t) : ℝ × ℝ × ℝ)‖ ≤ K) :
    Seq (ℝ × ℝ × ℝ) :=
  mkS (fun t => (Real.log (Y t / Ybar), ξ t, wMG ibm uc M im t)) ⟨K, hK⟩

/-- Woodford (2003), Prop. 2.11, p. 107 (A.11): `|b| < |a|` for the money-growth condition
whenever `u_m/u_c` is strictly decreasing in real balances at the steady state (`R_m < 0`,
equivalently `η_i > 0`). -/
theorem mg_slope_cond {β ibm Ybar mbar : ℝ} {R : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hibm : 0 < 1 + ibm) (hm : 0 < mbar) (hR : DifferentiableAt ℝ R (Ybar, mbar, 0))
    (hss : R (Ybar, mbar, 0) = 1 - β * (1 + ibm))
    (hRm : fderiv ℝ R (Ybar, mbar, 0) (0, 1, 0) < 0) :
    |slopeB (FMG β ibm Ybar mbar R)| < |slopeA (FMG β ibm Ybar mbar R)| := by
  obtain ⟨ha, hb, -⟩ := slopes_FMG hR hss
  have hpos : 0 < β * (1 + ibm) := mul_pos hβ hibm
  have hmr : 0 < -(mbar * fderiv ℝ R (Ybar, mbar, 0) (0, 1, 0)) := by
    have := mul_neg_of_pos_of_neg hm hRm
    linarith
  rw [ha, hb, abs_neg, abs_of_pos hpos, abs_of_pos (by linarith)]
  linarith

/-- Woodford (2003), **Proposition 2.11**, pp. 107–108 and A.11, p. 645 ("there is also a locally
unique solution to the exact equilibrium relations (1.21) and (3.5)"), **exact
perfect-foresight version**. Let `u_m/u_c = R` be `C¹` near the steady state `(Ȳ, m̄, 0)` with
`R(Ȳ, m̄, 0) = Δ̄ = 1 − β(1 + īᵐ)` and `R_m < 0` (normal goods, so `η_i > 0`). Then there are
`ε, δ > 0` such that whenever `ŷ_t`, `ξ_t`, `r̂_t`, `μ_{t+1}` and `îᵐ_t` all stay within `δ`,
there is an equilibrium with `|log(M_t/(P_t m̄))| ≤ ε` for all `t` (so `P_t/M_t` stays in an
open set `𝒫`), and any two such equilibria coincide (prices and interest rates). -/
theorem mg_local_determinacy {β ibm Ybar mbar : ℝ} {R : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hibm : 0 < 1 + ibm) (hYb : 0 < Ybar) (hm : 0 < mbar) (hR : ContDiffAt ℝ 1 R (Ybar, mbar, 0))
    (hss : R (Ybar, mbar, 0) = 1 - β * (1 + ibm))
    (hRm : fderiv ℝ R (Ybar, mbar, 0) (0, 1, 0) < 0) :
    ∃ ε > 0, ∃ δ > 0, ∀ uc M im Y ξ : ℕ → ℝ, (∀ t, 0 < uc t) → (∀ t, 0 < M t) →
      (∀ t, 0 < 1 + im t) → (∀ t, 0 < Y t) →
      (∀ t, |Real.log (Y t / Ybar)| ≤ δ) → (∀ t, |ξ t| ≤ δ) →
      (∀ t, |Real.log (uc t / uc (t + 1))| ≤ δ) → (∀ t, |Real.log (M (t + 1) / M t)| ≤ δ) →
      (∀ t, |Real.log ((1 + im t) / (1 + ibm))| ≤ δ) →
      (∃ P i : ℕ → ℝ, MGEq β R uc M im Y ξ P i ∧ ∀ t, |Real.log (M t / (P t * mbar))| ≤ ε) ∧
      ∀ P i P' i' : ℕ → ℝ, MGEq β R uc M im Y ξ P i → MGEq β R uc M im Y ξ P' i' →
        (∀ t, |Real.log (M t / (P t * mbar))| ≤ ε) →
        (∀ t, |Real.log (M t / (P' t * mbar))| ≤ ε) → P = P' ∧ i = i' := by
  have hRd : DifferentiableAt ℝ R (Ybar, mbar, 0) := hR.differentiableAt one_ne_zero
  obtain ⟨ε, hε, -, δ, hδ, -, X, -, -, hX⟩ := local_determinacy_loc (contDiffAt_FMG hR)
    (FMG_zero hss) (mg_slope_cond hβ hibm hm hRd hss hRm) one_pos
  refine ⟨ε / 2, half_pos hε, δ / 4, by positivity,
    fun uc M im Y ξ huc hM him hY hYd hξd hrd hμd himd => ?_⟩
  have hK : ∀ t, ‖((Real.log (Y t / Ybar), ξ t, wMG ibm uc M im t) : ℝ × ℝ × ℝ)‖ ≤ 3 * (δ / 4) :=
    fun t => norm_triple_le (by linarith [hYd t]) (by linarith [hξd t])
      (abs_wMG_le hrd hμd himd t)
  set e := eMG Ybar ibm uc M im Y ξ (3 * (δ / 4)) hK with he
  have hen : ‖e‖ < δ := lt_of_le_of_lt (norm_seq_le (by positivity) hK) (by linarith)
  obtain ⟨hXn, hXs, -, huniq⟩ := hX e hen
  have hstep : ∀ P i : ℕ → ℝ, MGEq β R uc M im Y ξ P i → ∀ t,
      FMG β ibm Ybar mbar R (Real.log (M t / (P t * mbar)), Real.log (M (t + 1) / (P (t + 1) *
        mbar)), e t) = 0 := by
    rintro P i ⟨hP, hF, hD⟩ t
    exact (mg_step hβ hibm hYb hm (hP t) (hP (t + 1)) (hM t) (hM (t + 1)) (huc t) (huc (t + 1))
      (hY t) (him t) (hF t)).mp (hD t)
  have hclass : ∀ P i : ℕ → ℝ, MGEq β R uc M im Y ξ P i →
      ∀ hb : (∀ t, |Real.log (M t / (P t * mbar))| ≤ ε / 2),
      mk (fun t => Real.log (M t / (P t * mbar))) ⟨ε / 2, hb⟩ = X e := fun P i hE hb =>
    huniq _ (lt_of_le_of_lt (norm_le_of_abs_le (by positivity) hb) (half_lt_self hε))
      (fun t => hstep P i hE t)
  refine ⟨?_, ?_⟩
  · set x := X e with hx
    have hlog : ∀ t, Real.log (M t / (M t / (mbar * Real.exp (x t)) * mbar)) = x t := fun t => by
      rw [show M t / (M t / (mbar * Real.exp (x t)) * mbar) = Real.exp (x t) by
        field_simp [(hM t).ne']]
      exact Real.log_exp _
    have hPpos : ∀ t, 0 < M t / (mbar * Real.exp (x t)) := fun t => by
      have := hM t
      positivity
    refine ⟨fun t => M t / (mbar * Real.exp (x t)),
      fun t => uc t / (β * uc (t + 1)) * (M (t + 1) / (mbar * Real.exp (x (t + 1))) /
        (M t / (mbar * Real.exp (x t)))) - 1, ⟨hPpos, fun t => by ring, fun t => ?_⟩,
      fun t => ?_⟩
    · refine (mg_step hβ hibm hYb hm (hPpos t) (hPpos (t + 1)) (hM t) (hM (t + 1)) (huc t)
        (huc (t + 1)) (hY t) (him t) (by ring)).mpr ?_
      rw [hlog t, hlog (t + 1)]
      exact hXs t
    · rw [hlog t]
      exact (abs_apply_le x t).trans hXn.le
  · intro P i P' i' hE hE' hb hb'
    have hb2 : ∀ t, |Real.log (M t / (P t * mbar))| ≤ ε / 2 := hb
    have hb2' : ∀ t, |Real.log (M t / (P' t * mbar))| ≤ ε / 2 := hb'
    have hlog : ∀ t, Real.log (M t / (P t * mbar)) = Real.log (M t / (P' t * mbar)) := fun t =>
      congrArg (fun y : Linf => y t) ((hclass P i hE hb2).trans (hclass P' i' hE' hb2').symm)
    have hPP : P = P' := funext fun t => by
      have hpos1 : 0 < M t / (P t * mbar) := by have := hE.1 t; have := hM t; positivity
      have hpos2 : 0 < M t / (P' t * mbar) := by have := hE'.1 t; have := hM t; positivity
      have h := Real.log_injOn_pos (Set.mem_Ioi.mpr hpos1) (Set.mem_Ioi.mpr hpos2) (hlog t)
      have h1 := (hE.1 t).ne'
      have h2 := (hE'.1 t).ne'
      have h3 := (hM t).ne'
      field_simp at h
      nlinarith [h]
    refine ⟨hPP, funext fun t => ?_⟩
    have h1 := hE.2.1 t
    have h2 := hE'.2.1 t
    rw [hPP] at h1
    linarith

/-- Woodford (2003), Prop. 2.11, p. 107 and App. A.3, p. 633 (`C¹` dependence): in sequence space
the money-growth equilibrium `x = X(ŷ, ξ, w)` (log real balances) is a `C¹` function of the
disturbances near zero, with `X(0) = 0` and derivative at zero the log-linear solution (A.30). -/
theorem mg_smooth_dependence {β ibm Ybar mbar : ℝ} {R : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hibm : 0 < 1 + ibm) (hm : 0 < mbar) (hR : ContDiffAt ℝ 1 R (Ybar, mbar, 0))
    (hss : R (Ybar, mbar, 0) = 1 - β * (1 + ibm))
    (hRm : fderiv ℝ R (Ybar, mbar, 0) (0, 1, 0) < 0) :
    ∃ δ > 0, ∃ X : Seq (ℝ × ℝ × ℝ) → Linf, X 0 = 0 ∧
      HasFDerivAt X (linSol3 (FMG β ibm Ybar mbar R)) 0 ∧
      ∀ e : Seq (ℝ × ℝ × ℝ), ‖e‖ < δ → Solves (FMG β ibm Ybar mbar R) e (X e) ∧
        ContDiffAt ℝ 1 X e := by
  obtain ⟨ε, hε, -, δ, hδ, -, X, hX0, hXd, hX⟩ := local_determinacy_loc (contDiffAt_FMG hR)
    (FMG_zero hss) (mg_slope_cond hβ hibm hm (hR.differentiableAt one_ne_zero) hss hRm) one_pos
  exact ⟨δ, hδ, X, hX0, hXd, fun e he => ⟨(hX e he).2.1, (hX e he).2.2.1⟩⟩

/-- Woodford (2003), (3.6), p. 107: the interest semielasticity of money demand computed from
`R = u_m/u_c`: `η_i = −β(1 + īᵐ)/(m̄ R_m)` (`= −(1 − Δ̄)/(m̄ R_m)`). -/
noncomputable def etaIR (β ibm mbar : ℝ) (D : ℝ × ℝ × ℝ →L[ℝ] ℝ) : ℝ :=
  -(β * (1 + ibm)) / (mbar * D (0, 1, 0))

/-- Woodford (2003), (3.6), p. 107: the income elasticity from `R`: `η_y = −Ȳ R_Y/(m̄ R_m)`. -/
noncomputable def etaYR (Ybar mbar : ℝ) (D : ℝ × ℝ × ℝ →L[ℝ] ℝ) : ℝ :=
  -(Ybar * D (1, 0, 0)) / (mbar * D (0, 1, 0))

/-- Woodford (2003), (3.6), p. 107: the money-demand-shock coefficient from `R`:
`(1/m̄) ∂L/∂ξ = −R_ξ/(m̄ R_m)`. -/
noncomputable def epsR (mbar : ℝ) (D : ℝ × ℝ × ℝ →L[ℝ] ℝ) : ℝ :=
  -D (0, 0, 1) / (mbar * D (0, 1, 0))

/-- Woodford (2003), (3.5)–(3.6), pp. 104–107 (implicit differentiation, three variables): if
`R(Y, L(Y, Δ, ξ), ξ) = Δ` near `(Ȳ, Δ̄, 0)`, then `R_Y + R_m L_Y = 0`, `R_m L_Δ = 1` and
`R_ξ + R_m L_ξ = 0` (extends `MoneyGrowth.lm_partials` to the money-demand shock). -/
theorem lm_partials3 {R L : ℝ × ℝ × ℝ → ℝ} {D L' : ℝ × ℝ × ℝ →L[ℝ] ℝ} {Ybar Δbar : ℝ}
    (hR : HasFDerivAt R D (Ybar, L (Ybar, Δbar, 0), 0)) (hL : HasFDerivAt L L' (Ybar, Δbar, 0))
    (hid : ∀ᶠ y in 𝓝 ((Ybar, Δbar, 0) : ℝ × ℝ × ℝ), R (y.1, L y, y.2.2) = y.2.1) :
    D (1, 0, 0) + D (0, 1, 0) * L' (1, 0, 0) = 0 ∧ D (0, 1, 0) * L' (0, 1, 0) = 1 ∧
      D (0, 0, 1) + D (0, 1, 0) * L' (0, 0, 1) = 0 := by
  let Q : ℝ × ℝ × ℝ →L[ℝ] ℝ × ℝ × ℝ := (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
    (L'.prod ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))
  have hq : HasFDerivAt (fun y : ℝ × ℝ × ℝ => ((y.1, L y, y.2.2) : ℝ × ℝ × ℝ)) Q
      (Ybar, Δbar, 0) :=
    hasFDerivAt_fst.prodMk (hL.prodMk (hasFDerivAt_snd.snd))
  have hk := hR.comp ((Ybar, Δbar, 0) : ℝ × ℝ × ℝ) hq
  have hk2 : HasFDerivAt (fun y : ℝ × ℝ × ℝ => R (y.1, L y, y.2.2))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      (Ybar, Δbar, 0) :=
    (hasFDerivAt_snd.fst).congr_of_eventuallyEq hid
  have heq := hk.unique hk2
  have e1 := congrArg (fun G : ℝ × ℝ × ℝ →L[ℝ] ℝ => G (1, 0, 0)) heq
  have e2 := congrArg (fun G : ℝ × ℝ × ℝ →L[ℝ] ℝ => G (0, 1, 0)) heq
  have e3 := congrArg (fun G : ℝ × ℝ × ℝ →L[ℝ] ℝ => G (0, 0, 1)) heq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Q] at e1 e2 e3
  rw [MoneyGrowth.clm3_apply] at e1 e2 e3
  refine ⟨by linarith, by linarith, by linarith⟩

/-- Woodford (2003), (3.6), p. 107: **the coefficients of the exact money-growth condition are the
money-demand elasticities of (3.6)**: if `L` is the money-demand function (3.5), i.e. `R(Y, L, ξ)
= Δ` near the steady state with `L(Ȳ, Δ̄, 0) = m̄`, then `etaIR`, `etaYR`, `epsR` are
`MoneyGrowth.etaI`, `etaY`, `epsCoef` of `hasFDerivAt_moneyDemand`. -/
theorem mg_coeffs_eq {β ibm Ybar mbar : ℝ} {R L : ℝ × ℝ × ℝ → ℝ} {L' : ℝ × ℝ × ℝ →L[ℝ] ℝ}
    (hR : DifferentiableAt ℝ R (Ybar, mbar, 0))
    (hL : HasFDerivAt L L' (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hid : ∀ᶠ y in 𝓝 ((Ybar, 1 - β * (1 + ibm), 0) : ℝ × ℝ × ℝ), R (y.1, L y, y.2.2) = y.2.1) :
    etaIR β ibm mbar (fderiv ℝ R (Ybar, mbar, 0)) = MoneyGrowth.etaI L' mbar (1 - β * (1 + ibm)) ∧
      etaYR Ybar mbar (fderiv ℝ R (Ybar, mbar, 0)) = MoneyGrowth.etaY L' Ybar mbar ∧
      epsR mbar (fderiv ℝ R (Ybar, mbar, 0)) = MoneyGrowth.epsCoef L' mbar := by
  have hR' : HasFDerivAt R (fderiv ℝ R (Ybar, mbar, 0)) (Ybar, L (Ybar, 1 - β * (1 + ibm), 0), 0) :=
    by rw [hLss]; exact hR.hasFDerivAt
  obtain ⟨h1, h2, h3⟩ := lm_partials3 hR' hL hid
  set D := fderiv ℝ R (Ybar, mbar, 0)
  have hm0 : D (0, 1, 0) ≠ 0 := by
    intro h
    rw [h, zero_mul] at h2
    exact zero_ne_one h2
  have hLD : L' (0, 1, 0) = 1 / D (0, 1, 0) := by field_simp; linarith
  have hLY : L' (1, 0, 0) = -D (1, 0, 0) / D (0, 1, 0) := by field_simp; linarith
  have hLx : L' (0, 0, 1) = -D (0, 0, 1) / D (0, 1, 0) := by field_simp; linarith
  refine ⟨?_, ?_, ?_⟩
  · simp only [etaIR, MoneyGrowth.etaI, hLD]
    field_simp
    ring
  · simp only [etaYR, MoneyGrowth.etaY, hLY]
    field_simp
  · simp only [epsR, MoneyGrowth.epsCoef, hLx]
    field_simp

/-- Woodford (2003), (3.7), p. 108: `ϕ_k = (η_i/(1 + η_i))ᵏ (1 + η_i)⁻¹` whenever `1 + η_i ≠ 0`. -/
theorem phi_eq_div (ηi : ℝ) (h : 1 + ηi ≠ 0) (k : ℕ) :
    MoneyGrowth.phi ηi k = (ηi / (1 + ηi)) ^ k * (1 + ηi)⁻¹ := by
  rw [MoneyGrowth.phi, div_pow, pow_succ]
  field_simp

/-- Woodford (2003), (A.30), p. 645, **the first-order term of the exact money-growth equilibrium
is (A.30)**: `x̂_t = ∑_j ϕ_j (η_y ŷ_{t+j} + ε ξ_{t+j} − η_i w_{t+j})` with
`ϕ_j = η_iʲ/(1 + η_i)^{j+1}` (`MoneyGrowth.phi`). -/
theorem linSol3_FMG_apply {β ibm Ybar mbar : ℝ} {R : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hibm : 0 < 1 + ibm) (hm : 0 < mbar) (hR : DifferentiableAt ℝ R (Ybar, mbar, 0))
    (hss : R (Ybar, mbar, 0) = 1 - β * (1 + ibm))
    (hRm : fderiv ℝ R (Ybar, mbar, 0) (0, 1, 0) < 0) (e : Seq (ℝ × ℝ × ℝ)) (t : ℕ) :
    linSol3 (FMG β ibm Ybar mbar R) e t =
      ∑' k, MoneyGrowth.phi (etaIR β ibm mbar (fderiv ℝ R (Ybar, mbar, 0))) k *
        (etaYR Ybar mbar (fderiv ℝ R (Ybar, mbar, 0)) * (e (t + k)).1 +
          epsR mbar (fderiv ℝ R (Ybar, mbar, 0)) * (e (t + k)).2.1 -
          etaIR β ibm mbar (fderiv ℝ R (Ybar, mbar, 0)) * (e (t + k)).2.2) := by
  have hab := mg_slope_cond hβ hibm hm hR hss hRm
  obtain ⟨ha, hb, hc⟩ := slopes_FMG hR hss
  rw [linSol3_apply hab, ← neg_mul, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  set D := fderiv ℝ R (Ybar, mbar, 0) with hD
  set c := β * (1 + ibm) with hcdef
  set ηi := etaIR β ibm mbar D with hηi
  have hc0 : 0 < c := mul_pos hβ hibm
  have hRm0 : D (0, 1, 0) ≠ 0 := hRm.ne
  have hmD : mbar * D (0, 1, 0) < 0 := mul_neg_of_pos_of_neg hm hRm
  have hmD0 : mbar * D (0, 1, 0) ≠ 0 := hmD.ne
  have ha0 : c - mbar * D (0, 1, 0) ≠ 0 := by linarith
  have h1e : 1 + ηi = (mbar * D (0, 1, 0) - c) / (mbar * D (0, 1, 0)) := by
    rw [hηi, etaIR]
    field_simp
    ring
  have h1 : 1 + ηi ≠ 0 := by
    rw [h1e]
    exact div_ne_zero (by linarith) hmD0
  have hq : -slopeB (FMG β ibm Ybar mbar R) / slopeA (FMG β ibm Ybar mbar R) = ηi / (1 + ηi) := by
    have ha0' : mbar * D (0, 1, 0) - c ≠ 0 := by linarith
    rw [ha, hb, h1e, hηi, etaIR, ← hcdef]
    field_simp
    ring
  have hcf : ∀ y z w : ℝ, -(slopeA (FMG β ibm Ybar mbar R))⁻¹ *
      slopeC (FMG β ibm Ybar mbar R) (y, z, w) =
      (1 + ηi)⁻¹ * (etaYR Ybar mbar D * y + epsR mbar D * z - ηi * w) := by
    intro y z w
    have ha0' : mbar * D (0, 1, 0) - c ≠ 0 := by linarith
    rw [ha, hc, h1e, hηi, etaIR, etaYR, epsR, ← hcdef]
    field_simp
    ring
  have hk := hcf (e (t + k)).1 (e (t + k)).2.1 (e (t + k)).2.2
  simp only [Prod.mk.eta] at hk
  rw [phi_eq_div ηi h1 k, hq, show -(slopeA (FMG β ibm Ybar mbar R))⁻¹ * ((ηi / (1 + ηi)) ^ k *
    slopeC (FMG β ibm Ybar mbar R) (e (t + k))) = (ηi / (1 + ηi)) ^ k *
    (-(slopeA (FMG β ibm Ybar mbar R))⁻¹ * slopeC (FMG β ibm Ybar mbar R) (e (t + k))) by ring, hk]
  ring

/-- Woodford (2003), A.11, p. 645, auxiliary: the weights `ϕ_j` against a bounded sequence give a
summable series. -/
theorem summable_phi_mul {ηi K : ℝ} (hηi : 0 < ηi) {y : ℕ → ℝ} (hy : ∀ j, |y j| ≤ K) :
    Summable (fun j => MoneyGrowth.phi ηi j * y j) := by
  have hq0 : 0 ≤ ηi / (1 + ηi) := by positivity
  have hq1 : ηi / (1 + ηi) < 1 := by rw [div_lt_one (by linarith)]; linarith
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0 hq1).mul_left
    ((1 - ηi / (1 + ηi)) * K)) (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul, MoneyGrowth.phi_eq ηi hηi j,
    abs_of_nonneg (mul_nonneg (by linarith) (pow_nonneg hq0 j))]
  calc (1 - ηi / (1 + ηi)) * (ηi / (1 + ηi)) ^ j * |y j| ≤
      (1 - ηi / (1 + ηi)) * (ηi / (1 + ηi)) ^ j * K :=
        mul_le_mul_of_nonneg_left (hy j) (mul_nonneg (by linarith) (pow_nonneg hq0 j))
    _ = _ := by ring

/-- Woodford (2003), (3.7) from (A.30), A.11 p. 645 (summation by parts): for `log M` with bounded
growth `μ_{s+1} = log M_{s+1} − log M_s` and bounded `g`,
`log M_t − ∑_j ϕ_j (g_{t+j} − η_i μ_{t+j+1}) = ∑_j ϕ_j (log M_{t+j} − g_{t+j})`. -/
theorem phi_sum_by_parts {ηi K Kg : ℝ} (hηi : 0 < ηi) {lM g : ℕ → ℝ}
    (hμ : ∀ s, |lM (s + 1) - lM s| ≤ K) (hg : ∀ s, |g s| ≤ Kg) (t : ℕ) :
    lM t - ∑' j, MoneyGrowth.phi ηi j * (g (t + j) - ηi * (lM (t + j + 1) - lM (t + j))) =
      ∑' j, MoneyGrowth.phi ηi j * (lM (t + j) - g (t + j)) := by
  set α := ηi / (1 + ηi) with hα
  have hα0 : 0 ≤ α := by positivity
  have hα1 : |α| < 1 := by
    rw [abs_of_nonneg hα0, div_lt_one (by linarith)]
    linarith
  have hx : ∀ j, |lM (t + (j + 1)) - lM (t + j)| ≤ K := fun j => by
    rw [← add_assoc]
    exact hμ (t + j)
  have habel := ForwardSolution.abel_tsum hα1 (x := fun j => lM (t + j)) hx
  have hS1 : Summable (fun j => α ^ j * lM (t + j)) := ForwardSolution.summable_geom_mul hα1 hx
  have hSg : Summable (fun j => MoneyGrowth.phi ηi j * g (t + j)) :=
    summable_phi_mul hηi (fun j => hg (t + j))
  have hSμ : Summable (fun j => MoneyGrowth.phi ηi j * (lM (t + j + 1) - lM (t + j))) :=
    summable_phi_mul hηi (fun j => hμ (t + j))
  have hphi : ∀ j, MoneyGrowth.phi ηi j = (1 - α) * α ^ j := fun j => MoneyGrowth.phi_eq ηi hηi j
  have hSM : Summable (fun j => MoneyGrowth.phi ηi j * lM (t + j)) := by
    refine (hS1.mul_left (1 - α)).congr fun j => ?_
    rw [hphi]
    ring
  have hkey : ηi * (1 - α) = α := by
    rw [hα]
    field_simp
    ring
  have hmu : ∀ j, ηi * (MoneyGrowth.phi ηi j * (lM (t + j + 1) - lM (t + j))) =
      α ^ (j + 1) * (lM (t + (j + 1)) - lM (t + j)) := fun j => by
    rw [hphi, show t + (j + 1) = t + j + 1 by ring, pow_succ]
    linear_combination (α ^ j * (lM (t + j + 1) - lM (t + j))) * hkey
  have e1 : ∑' j, MoneyGrowth.phi ηi j * (g (t + j) - ηi * (lM (t + j + 1) - lM (t + j))) =
      ∑' j, MoneyGrowth.phi ηi j * g (t + j) -
        ∑' j, α ^ (j + 1) * (lM (t + (j + 1)) - lM (t + j)) := by
    rw [← tsum_congr hmu, ← hSg.tsum_sub (hSμ.mul_left ηi)]
    exact tsum_congr fun j => by ring
  have e2 : ∑' j, MoneyGrowth.phi ηi j * (lM (t + j) - g (t + j)) =
      ∑' j, MoneyGrowth.phi ηi j * lM (t + j) - ∑' j, MoneyGrowth.phi ηi j * g (t + j) := by
    rw [← hSM.tsum_sub hSg]
    exact tsum_congr fun j => by ring
  have e3 : ∑' j, MoneyGrowth.phi ηi j * lM (t + j) = (1 - α) * ∑' j, α ^ j * lM (t + j) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by rw [hphi]; ring
  rw [e1, e2, e3, habel]
  simp only [add_zero]
  ring

/-- Woodford (2003), **Proposition 2.11**, pp. 107–108, A.11 p. 645 ("a log-linear approximation …
accurate up to a residual of order `O(ξ²)`"), exact perfect-foresight version with the `C²`
hypothesis of E18, in real balances: every equilibrium near the steady state satisfies
`|log(M_t/(P_t m̄)) − ∑_j ϕ_j (η_y ŷ_{t+j} + ε ξ_{t+j} − η_i w_{t+j})| ≤ C ξ²` when all
primitive disturbances are bounded by `ξ < δ` ((A.30), with `η_y, η_i, ε` as in (3.6)). -/
theorem mg_second_order {β ibm Ybar mbar : ℝ} {R : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hibm : 0 < 1 + ibm) (hYb : 0 < Ybar) (hm : 0 < mbar) (hR : ContDiffAt ℝ 2 R (Ybar, mbar, 0))
    (hss : R (Ybar, mbar, 0) = 1 - β * (1 + ibm))
    (hRm : fderiv ℝ R (Ybar, mbar, 0) (0, 1, 0) < 0) :
    ∃ ε > 0, ∃ δ > 0, ∃ C : ℝ, ∀ uc M im Y ξ : ℕ → ℝ, ∀ ξb : ℝ, (∀ t, 0 < uc t) →
      (∀ t, 0 < M t) → (∀ t, 0 < 1 + im t) → (∀ t, 0 < Y t) → ξb < δ →
      (∀ t, |Real.log (Y t / Ybar)| ≤ ξb) → (∀ t, |ξ t| ≤ ξb) →
      (∀ t, |Real.log (uc t / uc (t + 1))| ≤ ξb) → (∀ t, |Real.log (M (t + 1) / M t)| ≤ ξb) →
      (∀ t, |Real.log ((1 + im t) / (1 + ibm))| ≤ ξb) →
      ∀ P i : ℕ → ℝ, MGEq β R uc M im Y ξ P i → (∀ t, |Real.log (M t / (P t * mbar))| ≤ ε) →
      ∀ t, |Real.log (M t / (P t * mbar)) -
        ∑' k, MoneyGrowth.phi (etaIR β ibm mbar (fderiv ℝ R (Ybar, mbar, 0))) k *
          (etaYR Ybar mbar (fderiv ℝ R (Ybar, mbar, 0)) * Real.log (Y (t + k) / Ybar) +
            epsR mbar (fderiv ℝ R (Ybar, mbar, 0)) * ξ (t + k) -
            etaIR β ibm mbar (fderiv ℝ R (Ybar, mbar, 0)) * wMG ibm uc M im (t + k))| ≤
        C * ξb ^ 2 := by
  have hR1 : ContDiffAt ℝ 1 R (Ybar, mbar, 0) := hR.of_le (by norm_num)
  have hRd : DifferentiableAt ℝ R (Ybar, mbar, 0) := hR1.differentiableAt one_ne_zero
  obtain ⟨ε, hε, -, δ, hδ, -, C, hC⟩ := second_order_loc (contDiffAt_FMG hR) (FMG_zero hss)
    (mg_slope_cond hβ hibm hm hRd hss hRm) one_pos
  refine ⟨ε / 2, half_pos hε, δ / 4, by positivity, 9 * max C 0,
    fun uc M im Y ξ ξb huc hM him hY hξb hYd hξd hrd hμd himd P i hE hbd t => ?_⟩
  have hξ0 : 0 ≤ ξb := (abs_nonneg _).trans (hξd 0)
  have hK : ∀ t, ‖((Real.log (Y t / Ybar), ξ t, wMG ibm uc M im t) : ℝ × ℝ × ℝ)‖ ≤ 3 * ξb :=
    fun t => norm_triple_le (by linarith [hYd t]) (by linarith [hξd t])
      (abs_wMG_le hrd hμd himd t)
  set e := eMG Ybar ibm uc M im Y ξ (3 * ξb) hK with he
  have hen3 : ‖e‖ ≤ 3 * ξb := norm_seq_le (by positivity) hK
  have hen : ‖e‖ < δ := lt_of_le_of_lt hen3 (by linarith)
  have hsol : Solves (FMG β ibm Ybar mbar R) e
      (mk (fun t => Real.log (M t / (P t * mbar))) ⟨ε / 2, hbd⟩) := by
    intro s
    obtain ⟨hP, hF, hD⟩ := hE
    exact (mg_step hβ hibm hYb hm (hP s) (hP (s + 1)) (hM s) (hM (s + 1)) (huc s) (huc (s + 1))
      (hY s) (him s) (hF s)).mp (hD s)
  have hbound := hC e hen _ (lt_of_le_of_lt (norm_le_of_abs_le (by positivity) hbd)
    (half_lt_self hε)) hsol
  have hcoord := abs_apply_le (mk (fun t => Real.log (M t / (P t * mbar))) ⟨ε / 2, hbd⟩ -
    linSol3 (FMG β ibm Ybar mbar R) e) t
  simp only [lp.coeFn_sub, Pi.sub_apply, mk_apply] at hcoord
  rw [linSol3_FMG_apply hβ hibm hm hRd hss hRm] at hcoord
  refine hcoord.trans (hbound.trans ?_)
  have hsq : ‖e‖ ^ 2 ≤ 9 * ξb ^ 2 := by nlinarith [norm_nonneg e]
  calc C * ‖e‖ ^ 2 ≤ max C 0 * ‖e‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    _ ≤ max C 0 * (9 * ξb ^ 2) := mul_le_mul_of_nonneg_left hsq (le_max_right _ _)
    _ = 9 * max C 0 * ξb ^ 2 := by ring

/-- Woodford (2003), Prop. 2.11, eq. (3.7)/(A.26), p. 108: the composite disturbance
`u_t = η_y Ŷ_t − η_i r̂_t + εᵐ_t − η_i log(1 + īᵐ)` (exact perfect-foresight form, with
`r̂_t = log(u_c(t)/u_c(t+1))` and `εᵐ_t = ε ξ_t`). -/
noncomputable def uMG (ηy ηi εc Ybar ibm : ℝ) (uc Y ξ : ℕ → ℝ) (t : ℕ) : ℝ :=
  ηy * Real.log (Y t / Ybar) - ηi * Real.log (uc t / uc (t + 1)) + εc * ξ t -
    ηi * Real.log (1 + ibm)

/-- Woodford (2003), **Proposition 2.11, eq. (3.7)**, p. 108, exact perfect-foresight version
(`C²`, E18): every equilibrium near the steady state satisfies
`|log P_t − (∑_j ϕ_j [log M_{t+j} − η_i log(1 + iᵐ_{t+j}) − u_{t+j}] − log m̄)| ≤ C ξ²`
when all primitive disturbances are bounded by `ξ < δ`; the series converges although `log M`
may trend. -/
theorem mg_priceLevel_second_order {β ibm Ybar mbar : ℝ} {R : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hibm : 0 < 1 + ibm) (hYb : 0 < Ybar) (hm : 0 < mbar) (hR : ContDiffAt ℝ 2 R (Ybar, mbar, 0))
    (hss : R (Ybar, mbar, 0) = 1 - β * (1 + ibm))
    (hRm : fderiv ℝ R (Ybar, mbar, 0) (0, 1, 0) < 0) :
    ∃ ε > 0, ∃ δ > 0, ∃ C : ℝ, ∀ uc M im Y ξ : ℕ → ℝ, ∀ ξb : ℝ, (∀ t, 0 < uc t) →
      (∀ t, 0 < M t) → (∀ t, 0 < 1 + im t) → (∀ t, 0 < Y t) → ξb < δ →
      (∀ t, |Real.log (Y t / Ybar)| ≤ ξb) → (∀ t, |ξ t| ≤ ξb) →
      (∀ t, |Real.log (uc t / uc (t + 1))| ≤ ξb) → (∀ t, |Real.log (M (t + 1) / M t)| ≤ ξb) →
      (∀ t, |Real.log ((1 + im t) / (1 + ibm))| ≤ ξb) →
      ∀ P i : ℕ → ℝ, MGEq β R uc M im Y ξ P i → (∀ t, |Real.log (M t / (P t * mbar))| ≤ ε) →
      ∀ t, |Real.log (P t) -
        (∑' j, MoneyGrowth.phi (etaIR β ibm mbar (fderiv ℝ R (Ybar, mbar, 0))) j *
          (Real.log (M (t + j)) -
            etaIR β ibm mbar (fderiv ℝ R (Ybar, mbar, 0)) * Real.log (1 + im (t + j)) -
            uMG (etaYR Ybar mbar (fderiv ℝ R (Ybar, mbar, 0)))
              (etaIR β ibm mbar (fderiv ℝ R (Ybar, mbar, 0)))
              (epsR mbar (fderiv ℝ R (Ybar, mbar, 0))) Ybar ibm uc Y ξ (t + j)) -
          Real.log mbar)| ≤ C * ξb ^ 2 := by
  obtain ⟨ε, hε, δ, hδ, C, hC⟩ := mg_second_order hβ hibm hYb hm hR hss hRm
  refine ⟨ε, hε, δ, hδ, C,
    fun uc M im Y ξ ξb huc hM him hY hξb hYd hξd hrd hμd himd P i hE hbd t => ?_⟩
  have h := hC uc M im Y ξ ξb huc hM him hY hξb hYd hξd hrd hμd himd P i hE hbd t
  set D := fderiv ℝ R (Ybar, mbar, 0)
  set ηi := etaIR β ibm mbar D with hηi
  set ηy := etaYR Ybar mbar D
  set εc := epsR mbar D
  have hηpos : 0 < ηi := by
    have hmr : mbar * D (0, 1, 0) < 0 := mul_neg_of_pos_of_neg hm hRm
    exact div_pos_of_neg_of_neg (by nlinarith [mul_pos hβ hibm]) hmr
  set g : ℕ → ℝ := fun s => ηi * Real.log (1 + im s) + uMG ηy ηi εc Ybar ibm uc Y ξ s with hgdef
  set lM : ℕ → ℝ := fun s => Real.log (M s) with hlM
  have hξ0 : 0 ≤ ξb := (abs_nonneg _).trans (hξd 0)
  have hgb : ∀ s, |g s| ≤ |ηy| * ξb + |ηi| * ξb + |εc| * ξb + |ηi| * ξb := by
    intro s
    have e1 : g s = ηy * Real.log (Y s / Ybar) - ηi * Real.log (uc s / uc (s + 1)) +
        εc * ξ s + ηi * Real.log ((1 + im s) / (1 + ibm)) := by
      simp only [hgdef, uMG]
      rw [Real.log_div (him s).ne' hibm.ne']
      ring
    rw [e1]
    have a1 : |ηy * Real.log (Y s / Ybar)| ≤ |ηy| * ξb := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hYd s) (abs_nonneg _)
    have a2 : |ηi * Real.log (uc s / uc (s + 1))| ≤ |ηi| * ξb := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hrd s) (abs_nonneg _)
    have a3 : |εc * ξ s| ≤ |εc| * ξb := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hξd s) (abs_nonneg _)
    have a4 : |ηi * Real.log ((1 + im s) / (1 + ibm))| ≤ |ηi| * ξb := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (himd s) (abs_nonneg _)
    have b1 := abs_sub (ηy * Real.log (Y s / Ybar)) (ηi * Real.log (uc s / uc (s + 1)))
    have b2 := abs_add_le (ηy * Real.log (Y s / Ybar) - ηi * Real.log (uc s / uc (s + 1)))
      (εc * ξ s)
    have b3 := abs_add_le (ηy * Real.log (Y s / Ybar) - ηi * Real.log (uc s / uc (s + 1)) +
      εc * ξ s) (ηi * Real.log ((1 + im s) / (1 + ibm)))
    linarith
  have hμ : ∀ s, |lM (s + 1) - lM s| ≤ ξb := fun s => by
    simp only [hlM]
    rw [← Real.log_div (hM (s + 1)).ne' (hM s).ne']
    exact hμd s
  have hparts := phi_sum_by_parts hηpos hμ hgb t
  have hf : ∀ j, ηy * Real.log (Y (t + j) / Ybar) + εc * ξ (t + j) -
      ηi * wMG ibm uc M im (t + j) =
      g (t + j) - ηi * (lM (t + j + 1) - lM (t + j)) := fun j => by
    simp only [hgdef, hlM, uMG, wMG]
    rw [Real.log_div (him (t + j)).ne' hibm.ne', Real.log_div (hM (t + j + 1)).ne'
      (hM (t + j)).ne']
    ring
  have hsum : ∀ j, Real.log (M (t + j)) - ηi * Real.log (1 + im (t + j)) -
      uMG ηy ηi εc Ybar ibm uc Y ξ (t + j) = lM (t + j) - g (t + j) := fun j => by
    simp only [hgdef, hlM]
    ring
  simp only [hf] at h
  simp only [hsum]
  rw [← hparts]
  have hx : Real.log (M t / (P t * mbar)) = Real.log (M t) - Real.log (P t) - Real.log mbar := by
    rw [Real.log_div (hM t).ne' (mul_pos (hE.1 t) hm).ne', Real.log_mul (hE.1 t).ne' hm.ne']
    ring
  rw [hx] at h
  have e : Real.log (P t) - (lM t - ∑' j, MoneyGrowth.phi ηi j * (g (t + j) - ηi *
      (lM (t + j + 1) - lM (t + j))) - Real.log mbar) =
      -(Real.log (M t) - Real.log (P t) - Real.log mbar - ∑' j, MoneyGrowth.phi ηi j *
        (g (t + j) - ηi * (lM (t + j + 1) - lM (t + j)))) := by
    simp only [hlM]
    ring
  rw [e, abs_neg]
  exact h

/-! ### Solving a nonlinear inertial rule for inflation (local inverse in `π`)

A nonlinear version of (2.12), p. 96: `ĵ_t = ψ(π_t, ĵ_{t−1}, ν_t)` with `ĵ = log(β(1 + i))`,
`π = log Π`; its log-linearisation is `ĵ_t = φ_π π_t + ρ ĵ_{t−1} + c ν_t`. For `φ_π ≠ 0` the rule
can be solved locally for `π_t = Θ(ĵ_t, ĵ_{t−1}, ν_t)` (A.8, p. 641: "inverting (2.12)"). -/

/-- Woodford (2003), (2.12), p. 96: the augmented rule map `(π, ĵ₋, ν) ↦ (ψ(π, ĵ₋, ν), ĵ₋, ν)`. -/
def ruleAug (ψ : ℝ × ℝ × ℝ → ℝ) (q : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (ψ q, q.2)

/-- Woodford (2003), (2.12), p. 96: the derivative of the augmented rule map at the steady
state. -/
noncomputable def ruleD (ψ : ℝ × ℝ × ℝ → ℝ) : ℝ × ℝ × ℝ →L[ℝ] ℝ × ℝ × ℝ :=
  (fderiv ℝ ψ 0).prod (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- Woodford (2003), A.8, p. 641 ("inverting (2.12)"): the inverse of `ruleD`,
`(u, v) ↦ (φ_π⁻¹ (u − Dψ(0, v)), v)`. -/
noncomputable def ruleDInv (ψ : ℝ × ℝ × ℝ → ℝ) : ℝ × ℝ × ℝ →L[ℝ] ℝ × ℝ × ℝ :=
  ((fderiv ℝ ψ 0 (1, 0, 0))⁻¹ • (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) -
    (fderiv ℝ ψ 0).comp ((ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))).prod (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- Woodford (2003), (2.12), p. 96: `Dψ(0)(π, v) = φ_π π + Dψ(0)(0, v)`. -/
theorem fderiv_split (ψ : ℝ × ℝ × ℝ → ℝ) (π : ℝ) (v : ℝ × ℝ) :
    fderiv ℝ ψ 0 (π, v) = π * fderiv ℝ ψ 0 (1, 0, 0) + fderiv ℝ ψ 0 (0, v) := by
  have h : ((π, v) : ℝ × ℝ × ℝ) = π • ((1 : ℝ), (0 : ℝ × ℝ)) + ((0 : ℝ), v) := by
    ext <;> simp
  rw [h, map_add, map_smul, smul_eq_mul]
  rfl

/-- Woodford (2003), A.8, p. 641: `ruleDInv` is a left inverse of `ruleD` (`φ_π ≠ 0`). -/
theorem ruleDInv_ruleD {ψ : ℝ × ℝ × ℝ → ℝ} (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0)
    (q : ℝ × ℝ × ℝ) : ruleDInv ψ (ruleD ψ q) = q := by
  refine Prod.ext ?_ rfl
  change (fderiv ℝ ψ 0 (1, 0, 0))⁻¹ * (fderiv ℝ ψ 0 q - fderiv ℝ ψ 0 (0, q.2)) = q.1
  have h := fderiv_split ψ q.1 q.2
  simp only [Prod.mk.eta] at h
  rw [h]
  field_simp
  ring

/-- Woodford (2003), A.8, p. 641: `ruleDInv` is a right inverse of `ruleD` (`φ_π ≠ 0`). -/
theorem ruleD_ruleDInv {ψ : ℝ × ℝ × ℝ → ℝ} (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0)
    (q : ℝ × ℝ × ℝ) : ruleD ψ (ruleDInv ψ q) = q := by
  refine Prod.ext ?_ rfl
  change fderiv ℝ ψ 0 ((fderiv ℝ ψ 0 (1, 0, 0))⁻¹ * (q.1 - fderiv ℝ ψ 0 (0, q.2)), q.2) = q.1
  rw [fderiv_split]
  field_simp
  ring

/-- Woodford (2003), A.8, p. 641: for `φ_π ≠ 0` the derivative of the augmented rule map is a
continuous linear equivalence. -/
noncomputable def ruleDEquiv (ψ : ℝ × ℝ × ℝ → ℝ) (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) :
    (ℝ × ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ × ℝ) :=
  ContinuousLinearEquiv.equivOfInverse (ruleD ψ) (ruleDInv ψ) (ruleDInv_ruleD hφ)
    (ruleD_ruleDInv hφ)

/-- Woodford (2003), (2.12), p. 96: the augmented rule map has derivative `ruleD` at `0`. -/
theorem hasFDerivAt_ruleAug {ψ : ℝ × ℝ × ℝ → ℝ} (hψ : DifferentiableAt ℝ ψ 0) :
    HasFDerivAt (ruleAug ψ) (ruleD ψ) 0 :=
  hψ.hasFDerivAt.prodMk hasFDerivAt_snd

/-- Woodford (2003), A.8, p. 641: the augmented rule map has derivative `ruleDEquiv` at `0`. -/
theorem hasFDerivAt_ruleAug' {ψ : ℝ × ℝ × ℝ → ℝ} (hψ : DifferentiableAt ℝ ψ 0)
    (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) :
    HasFDerivAt (ruleAug ψ) (ruleDEquiv ψ hφ : _ →L[ℝ] _) 0 :=
  hasFDerivAt_ruleAug hψ

/-- Woodford (2003), (2.12), p. 96: the augmented rule map is `Cⁿ` near `0` when `ψ` is. -/
theorem contDiffAt_ruleAug {ψ : ℝ × ℝ × ℝ → ℝ} {n : ℕ} (hψ : ContDiffAt ℝ n ψ 0) :
    ContDiffAt ℝ n (ruleAug ψ) 0 :=
  hψ.prodMk contDiffAt_snd

/-- Woodford (2003), A.8, p. 641: the local homeomorphism inverting the augmented rule map (inverse
function theorem). -/
noncomputable def ruleHomeo (ψ : ℝ × ℝ × ℝ → ℝ) (hψ : ContDiffAt ℝ 1 ψ 0)
    (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) : OpenPartialHomeomorph (ℝ × ℝ × ℝ) (ℝ × ℝ × ℝ) :=
  ((contDiffAt_ruleAug (n := 1) hψ).hasStrictFDerivAt'
    (hasFDerivAt_ruleAug' (hψ.differentiableAt one_ne_zero) hφ) one_ne_zero).toOpenPartialHomeomorph
    (ruleAug ψ)

/-- Woodford (2003), A.8, p. 641: the local homeomorphism is the augmented rule map. -/
theorem ruleHomeo_coe {ψ : ℝ × ℝ × ℝ → ℝ} (hψ : ContDiffAt ℝ 1 ψ 0)
    (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) : ⇑(ruleHomeo ψ hψ hφ) = ruleAug ψ := rfl

/-- Woodford (2003), A.8, p. 641 ("inverting (2.12)"): the rule solved for inflation,
`π = Θ(ĵ, ĵ₋, ν)`. -/
noncomputable def solveRule (ψ : ℝ × ℝ × ℝ → ℝ) (hψ : ContDiffAt ℝ 1 ψ 0)
    (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) (q : ℝ × ℝ × ℝ) : ℝ :=
  ((ruleHomeo ψ hψ hφ).symm q).1

/-- Woodford (2003), A.8, p. 641: the steady state lies in the source of `ruleHomeo`. -/
theorem zero_mem_ruleHomeo_source {ψ : ℝ × ℝ × ℝ → ℝ} (hψ : ContDiffAt ℝ 1 ψ 0)
    (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) : (0 : ℝ × ℝ × ℝ) ∈ (ruleHomeo ψ hψ hφ).source := by
  unfold ruleHomeo
  exact HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _

/-- Woodford (2003), A.8, p. 641: the steady state lies in the target of `ruleHomeo`. -/
theorem zero_mem_ruleHomeo_target {ψ : ℝ × ℝ × ℝ → ℝ} (hψ : ContDiffAt ℝ 1 ψ 0)
    (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) (h0 : ψ 0 = 0) :
    (0 : ℝ × ℝ × ℝ) ∈ (ruleHomeo ψ hψ hφ).target := by
  have h := (ruleHomeo ψ hψ hφ).map_source (zero_mem_ruleHomeo_source hψ hφ)
  have e : ruleHomeo ψ hψ hφ 0 = 0 := by
    rw [ruleHomeo_coe]
    simp [ruleAug, h0]
  rwa [e] at h

/-- Woodford (2003), A.8, p. 641: the local inverse maps the steady state to itself. -/
theorem ruleHomeo_symm_zero {ψ : ℝ × ℝ × ℝ → ℝ} (hψ : ContDiffAt ℝ 1 ψ 0)
    (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) (h0 : ψ 0 = 0) : (ruleHomeo ψ hψ hφ).symm 0 = 0 := by
  have h := (ruleHomeo ψ hψ hφ).left_inv (zero_mem_ruleHomeo_source hψ hφ)
  have e : ruleHomeo ψ hψ hφ 0 = 0 := by
    rw [ruleHomeo_coe]
    simp [ruleAug, h0]
  rwa [e] at h

/-- Woodford (2003), A.8, p. 641: `Θ(0) = 0`. -/
theorem solveRule_zero {ψ : ℝ × ℝ × ℝ → ℝ} (hψ : ContDiffAt ℝ 1 ψ 0)
    (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) (h0 : ψ 0 = 0) : solveRule ψ hψ hφ 0 = 0 := by
  rw [solveRule, ruleHomeo_symm_zero hψ hφ h0]
  rfl

/-- Woodford (2003), A.8, p. 641: if the rule is `Cⁿ` near the steady state, so is `Θ`. -/
theorem contDiffAt_solveRule {ψ : ℝ × ℝ × ℝ → ℝ} (hψ : ContDiffAt ℝ 1 ψ 0)
    (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) (h0 : ψ 0 = 0) {n : ℕ} (hψn : ContDiffAt ℝ n ψ 0) :
    ContDiffAt ℝ n (solveRule ψ hψ hφ) 0 := by
  have hs : ContDiffAt ℝ n (ruleHomeo ψ hψ hφ).symm 0 := by
    refine (ruleHomeo ψ hψ hφ).contDiffAt_symm (f₀' := ruleDEquiv ψ hφ)
      (zero_mem_ruleHomeo_target hψ hφ h0) ?_ ?_
    · rw [ruleHomeo_symm_zero hψ hφ h0, ruleHomeo_coe]
      exact hasFDerivAt_ruleAug' (hψ.differentiableAt one_ne_zero) hφ
    · rw [ruleHomeo_symm_zero hψ hφ h0, ruleHomeo_coe]
      exact contDiffAt_ruleAug hψn
  exact contDiffAt_fst.comp 0 hs

/-- Woodford (2003), A.8, p. 641: the derivative of `Θ` at the steady state,
`(u, v) ↦ φ_π⁻¹ (u − Dψ(0)(0, v))`. -/
theorem hasFDerivAt_solveRule {ψ : ℝ × ℝ × ℝ → ℝ} (hψ : ContDiffAt ℝ 1 ψ 0)
    (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) (h0 : ψ 0 = 0) :
    HasFDerivAt (solveRule ψ hψ hφ)
      ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp (ruleDInv ψ)) 0 := by
  have hs : HasFDerivAt (ruleHomeo ψ hψ hφ).symm ((ruleDEquiv ψ hφ).symm : _ →L[ℝ] _) 0 := by
    refine (ruleHomeo ψ hψ hφ).hasFDerivAt_symm (zero_mem_ruleHomeo_target hψ hφ h0) ?_
    rw [ruleHomeo_symm_zero hψ hφ h0, ruleHomeo_coe]
    exact hasFDerivAt_ruleAug' (hψ.differentiableAt one_ne_zero) hφ
  exact (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt.comp 0 hs

/-- Woodford (2003), A.8, p. 641 (local equivalence of the rule and its inverse): there is `ρ > 0`
such that on the ball of radius `ρ`, `Θ(ψ(π, v), v) = π` and `ψ(Θ(u, v), v) = u`. -/
theorem solveRule_local {ψ : ℝ × ℝ × ℝ → ℝ} (hψ : ContDiffAt ℝ 1 ψ 0)
    (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) (h0 : ψ 0 = 0) :
    ∃ ρ > 0, (∀ q : ℝ × ℝ × ℝ, ‖q‖ < ρ → solveRule ψ hψ hφ (ψ q, q.2) = q.1) ∧
      ∀ q : ℝ × ℝ × ℝ, ‖q‖ < ρ → ψ (solveRule ψ hψ hφ q, q.2) = q.1 := by
  set H := ruleHomeo ψ hψ hφ with hH
  obtain ⟨ρ₁, hρ₁, hs⟩ :=
    Metric.mem_nhds_iff.mp (H.open_source.mem_nhds (zero_mem_ruleHomeo_source hψ hφ))
  obtain ⟨ρ₂, hρ₂, ht⟩ :=
    Metric.mem_nhds_iff.mp (H.open_target.mem_nhds (zero_mem_ruleHomeo_target hψ hφ h0))
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun q hq => ?_, fun q hq => ?_⟩
  · have hqs : q ∈ H.source := hs (by
      rw [Metric.mem_ball, dist_zero_right]; exact lt_of_lt_of_le hq (min_le_left _ _))
    have h := H.left_inv hqs
    change (H.symm (ruleAug ψ q)).1 = q.1
    rw [← ruleHomeo_coe hψ hφ, ← hH, h]
  · have hqt : q ∈ H.target := ht (by
      rw [Metric.mem_ball, dist_zero_right]; exact lt_of_lt_of_le hq (min_le_right _ _))
    have h : ruleAug ψ (H.symm q) = q := by
      rw [← ruleHomeo_coe hψ hφ, ← hH]
      exact H.right_inv hqt
    have h2 : (H.symm q).2 = q.2 := by
      have := congrArg Prod.snd h
      exact this
    have h1 : ψ (H.symm q) = q.1 := by
      have := congrArg Prod.fst h
      exact this
    have hq' : H.symm q = (solveRule ψ hψ hφ q, q.2) := Prod.ext rfl h2
    rw [← hq']
    exact h1

/-- Woodford (2003), A.8, p. 641: `Θ` is continuous at the steady state, so it maps small
arguments to small values. -/
theorem solveRule_small {ψ : ℝ × ℝ × ℝ → ℝ} (hψ : ContDiffAt ℝ 1 ψ 0)
    (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) (h0 : ψ 0 = 0) {κ : ℝ} (hκ : 0 < κ) :
    ∃ ρ > 0, ∀ q : ℝ × ℝ × ℝ, ‖q‖ < ρ → |solveRule ψ hψ hφ q| < κ := by
  have hc := (hasFDerivAt_solveRule hψ hφ h0).continuousAt
  have ht := hc.tendsto
  rw [solveRule_zero hψ hφ h0] at ht
  obtain ⟨ρ, hρ, h⟩ := Metric.eventually_nhds_iff.mp
    (ht.eventually (Metric.ball_mem_nhds (0 : ℝ) hκ))
  refine ⟨ρ, hρ, fun q hq => ?_⟩
  have := h (show dist q 0 < ρ by rwa [dist_zero_right])
  rwa [Real.dist_eq, sub_zero] at this

/-- Woodford (2003), (2.12), p. 96: `φ_π = ∂ψ/∂π` at the steady state. -/
noncomputable def phiPi (ψ : ℝ × ℝ × ℝ → ℝ) : ℝ := fderiv ℝ ψ 0 (1, 0, 0)

/-- Woodford (2003), (2.12), p. 96: `ρ = ∂ψ/∂ĵ_{t−1}` at the steady state. -/
noncomputable def rhoR (ψ : ℝ × ℝ × ℝ → ℝ) : ℝ := fderiv ℝ ψ 0 (0, 1, 0)

/-- Woodford (2003), (2.12), p. 96: the coefficient of the policy disturbance `ν` in the rule. -/
noncomputable def nuR (ψ : ℝ × ℝ × ℝ → ℝ) : ℝ := fderiv ℝ ψ 0 (0, 0, 1)

/-- Woodford (2003), A.8, p. 641: the derivative of `Θ` in coordinates,
`DΘ(0)(u, v, w) = φ_π⁻¹ (u − ρ v − c w)`. -/
theorem solveRule_deriv_apply {ψ : ℝ × ℝ × ℝ → ℝ} (u v w : ℝ) :
    ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp (ruleDInv ψ)) (u, v, w) =
      (phiPi ψ)⁻¹ * (u - rhoR ψ * v - nuR ψ * w) := by
  have h : ((0 : ℝ), v, w) = v • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) + w • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  change (fderiv ℝ ψ 0 (1, 0, 0))⁻¹ * (u - fderiv ℝ ψ 0 ((0 : ℝ), v, w)) = _
  rw [h, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, phiPi, rhoR, nuR]
  ring

/-! ### Propositions 2.7–2.8: inertial rules in the exact cashless model (§2.3, pp. 94–97)

Proposition 2.8: (1.21) under perfect foresight, `1 + i_t = u_c(t)/(β u_c(t+1)) Π_{t+1}`, and the
nonlinear inertial rule `ĵ_t = ψ(π_t, ĵ_{t−1}, ν_t)` (`ĵ = log(β(1 + i))`, `π = log Π`), whose
log-linearisation is (2.12). With `π_{t+1} = Θ(ĵ_{t+1}, ĵ_t, ν_{t+1})` this is the scalar forward
equation in the interest rate `ĵ_t − r̂_t − Θ(ĵ_{t+1}, ĵ_t, ν_{t+1}) = 0`, the nonlinear form of the
A.8 equation `(φ_π + ρ) î_t = î_{t+1} + …` (p. 641). The predetermined `i_{−1}` only enters
`π_0 = Θ(ĵ_0, ĵ_{−1}, ν_0)`. -/

/-- Woodford (2003), A.8, p. 641: the linear map `(x, x', (r, ν)) ↦ (x', x, ν)` feeding the
inverted rule `Θ(ĵ_{t+1}, ĵ_t, ν_{t+1})`. -/
noncomputable def lagMap : ℝ × ℝ × (ℝ × ℝ) →L[ℝ] ℝ × ℝ × ℝ :=
  ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ))).prod
    ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ × ℝ)).prod ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ)))))

/-- Woodford (2003), A.8, p. 641: coordinates of `lagMap`. -/
theorem lagMap_apply (p : ℝ × ℝ × (ℝ × ℝ)) : lagMap p = (p.2.1, p.1, p.2.2.2) := rfl

/-- Woodford (2003), A.8, p. 641, exact form: the period condition of the inertial-rule model in
`(ĵ_t, ĵ_{t+1}, (r̂_t, ν_{t+1}))`. -/
noncomputable def F8 (ψ : ℝ × ℝ × ℝ → ℝ) (hψ : ContDiffAt ℝ 1 ψ 0)
    (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) (p : ℝ × ℝ × (ℝ × ℝ)) : ℝ :=
  p.1 - p.2.2.1 - solveRule ψ hψ hφ (lagMap p)

/-- Woodford (2003), A.8, p. 641: the steady state solves the period condition. -/
theorem F8_zero {ψ : ℝ × ℝ × ℝ → ℝ} (hψ : ContDiffAt ℝ 1 ψ 0)
    (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) (h0 : ψ 0 = 0) : F8 ψ hψ hφ 0 = 0 := by
  have h := solveRule_zero hψ hφ h0
  simp only [F8, Prod.fst_zero, Prod.snd_zero, sub_zero, zero_sub, neg_eq_zero, map_zero]
  exact h

/-- Woodford (2003), A.8, p. 641: the period condition is `Cⁿ` near the steady state when the
rule is. -/
theorem contDiffAt_F8 {ψ : ℝ × ℝ × ℝ → ℝ} (hψ : ContDiffAt ℝ 1 ψ 0)
    (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) (h0 : ψ 0 = 0) {n : ℕ} (hψn : ContDiffAt ℝ n ψ 0) :
    ContDiffAt ℝ n (F8 ψ hψ hφ) 0 := by
  have hΘ : ContDiffAt ℝ n (solveRule ψ hψ hφ) (lagMap 0) := by
    rw [map_zero]
    exact contDiffAt_solveRule hψ hφ h0 hψn
  have h1 : ContDiffAt ℝ n (fun p : ℝ × ℝ × (ℝ × ℝ) => p.1 - p.2.2.1) 0 := by fun_prop
  exact h1.sub (hΘ.comp 0 lagMap.contDiff.contDiffAt)

/-- Woodford (2003), A.8, p. 641, **exact derivative**: `DF(x, x', (r, ν)) =
x − r − φ_π⁻¹ (x' − ρ x − c ν)`. -/
theorem hasFDerivAt_F8 {ψ : ℝ × ℝ × ℝ → ℝ} (hψ : ContDiffAt ℝ 1 ψ 0)
    (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) (h0 : ψ 0 = 0) :
    ∃ F' : ℝ × ℝ × (ℝ × ℝ) →L[ℝ] ℝ, HasFDerivAt (F8 ψ hψ hφ) F' 0 ∧
      ∀ x x' r ν : ℝ, F' (x, x', (r, ν)) =
        x - r - (phiPi ψ)⁻¹ * (x' - rhoR ψ * x - nuR ψ * ν) := by
  let G := ℝ × ℝ × (ℝ × ℝ)
  let Lm : G →L[ℝ] ℝ × ℝ × ℝ := lagMap
  let X1 : G →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ × ℝ)
  let R1 : G →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ)))
  have hΘ : HasFDerivAt (solveRule ψ hψ hφ)
      ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp (ruleDInv ψ)) (Lm 0) := by
    rw [map_zero]
    exact hasFDerivAt_solveRule hψ hφ h0
  have h := ((X1.hasFDerivAt (x := 0)).sub (R1.hasFDerivAt (x := 0))).sub
    (hΘ.comp (0 : G) Lm.hasFDerivAt)
  refine ⟨_, h, fun x x' r ν => ?_⟩
  simp only [sub_apply, ContinuousLinearMap.comp_apply]
  have e : Lm (x, x', (r, ν)) = (x', x, ν) := rfl
  have hd := solveRule_deriv_apply (ψ := ψ) x' x ν
  simp only [ContinuousLinearMap.comp_apply] at hd
  rw [e, hd]
  rfl

/-- Woodford (2003), A.8, p. 641: the slopes of the inertial-rule condition,
`a = 1 + ρ/φ_π`, `b = −1/φ_π`, `c(r, ν) = −r + (c_ν/φ_π) ν`. -/
theorem slopes_F8 {ψ : ℝ × ℝ × ℝ → ℝ} (hψ : ContDiffAt ℝ 1 ψ 0)
    (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) (h0 : ψ 0 = 0) :
    slopeA (F8 ψ hψ hφ) = 1 + rhoR ψ * (phiPi ψ)⁻¹ ∧ slopeB (F8 ψ hψ hφ) = -(phiPi ψ)⁻¹ ∧
      ∀ r ν : ℝ, slopeC (F8 ψ hψ hφ) (r, ν) = -r + nuR ψ * (phiPi ψ)⁻¹ * ν := by
  obtain ⟨F', hF', hv⟩ := hasFDerivAt_F8 hψ hφ h0
  obtain ⟨ha, hb, hc⟩ := slopes_of_hasFDerivAt hF'
  refine ⟨?_, ?_, fun r ν => by rw [hc, hv]; ring⟩
  · rw [ha]
    change F' (1, 0, ((0 : ℝ), (0 : ℝ))) = _
    rw [hv]
    ring
  · rw [hb]
    change F' (0, 1, ((0 : ℝ), (0 : ℝ))) = _
    rw [hv]
    ring

/-- Woodford (2003), (A.22), p. 641: for `φ_π ≠ 0`, `|b| < |a|` for the inertial-rule condition iff
`|φ_π + ρ| > 1`. -/
theorem inertial_slope_iff {φ ρ : ℝ} (hφ : φ ≠ 0) :
    |-φ⁻¹| < |1 + ρ * φ⁻¹| ↔ 1 < |φ + ρ| := by
  have hpos : 0 < |φ| := abs_pos.mpr hφ
  have e1 : |-φ⁻¹| = 1 / |φ| := by rw [abs_neg, abs_inv, one_div]
  have e2 : |1 + ρ * φ⁻¹| = |φ + ρ| / |φ| := by
    rw [← abs_div]
    congr 1
    field_simp
  rw [e1, e2, div_lt_div_iff_of_pos_right hpos]

/-- Woodford (2003), (A.22), p. 641: for `φ_π ≠ 0`, `|a| < |b|` iff `|φ_π + ρ| < 1`. -/
theorem inertial_slope_iff' {φ ρ : ℝ} (hφ : φ ≠ 0) :
    |1 + ρ * φ⁻¹| < |-φ⁻¹| ↔ |φ + ρ| < 1 := by
  have hpos : 0 < |φ| := abs_pos.mpr hφ
  have e1 : |-φ⁻¹| = 1 / |φ| := by rw [abs_neg, abs_inv, one_div]
  have e2 : |1 + ρ * φ⁻¹| = |φ + ρ| / |φ| := by
    rw [← abs_div]
    congr 1
    field_simp
  rw [e1, e2, div_lt_div_iff_of_pos_right hpos]

/-- Woodford (2003), (2.12), p. 96, with `i_{−1}` predetermined: the lagged log gross interest
rate `ĵ_{t−1} = log(β(1 + i_{t−1}))`. -/
noncomputable def jLag (β im1 : ℝ) (i : ℕ → ℝ) : ℕ → ℝ
  | 0 => Real.log (β * (1 + im1))
  | t + 1 => Real.log (β * (1 + i t))

/-- Woodford (2003), (1.21) and (2.12), pp. 72, 96, perfect foresight: an **inertial-rule
equilibrium** given the predetermined `i_{−1}`: positive gross inflation `Π` and interest rates `i`
with `1 + i_t = u_c(t)/(β u_c(t+1)) Π_{t+1}` and `log(β(1 + i_t)) = ψ(log Π_t, log(β(1 + i_{t−1})),
ν_t)` for all `t ≥ 0`. -/
def InertialEq (β : ℝ) (ψ : ℝ × ℝ × ℝ → ℝ) (uc ν : ℕ → ℝ) (im1 : ℝ) (Infl i : ℕ → ℝ) :
    Prop :=
  (∀ t, 0 < Infl t) ∧ (∀ t, 1 + i t = uc t / (β * uc (t + 1)) * Infl (t + 1)) ∧
    ∀ t, Real.log (β * (1 + i t)) = ψ (Real.log (Infl t), jLag β im1 i t, ν t)

/-- Woodford (2003), (2.11)/(A.8): the inflation path built from an interest-rate path,
`Π_0 = e^{θ₀}`, `Π_{t+1} = e^{ĵ_t − r̂_t}`. -/
noncomputable def inflPath (θ0 : ℝ) (x r : ℕ → ℝ) : ℕ → ℝ
  | 0 => Real.exp θ0
  | t + 1 => Real.exp (x t - r t)

/-- Woodford (2003), (1.21), p. 72: in logs the Fisher relation is `ĵ_t = r̂_t + π_{t+1}`. -/
theorem fisher_log {β u0 u1 Q1 i : ℝ} (hβ : 0 < β) (hu0 : 0 < u0) (hu1 : 0 < u1) (hQ : 0 < Q1)
    (h : 1 + i = u0 / (β * u1) * Q1) :
    Real.log (β * (1 + i)) = Real.log (u0 / u1) + Real.log Q1 := by
  rw [h, ← Real.log_mul (by positivity) hQ.ne']
  congr 1
  field_simp

/-- Woodford (2003), **Proposition 2.8**, p. 96 and A.8, pp. 640–641, **exact perfect-foresight
version** (determinacy half): let the nonlinear inertial rule `ψ` be `C¹` near the steady state,
`ψ(0) = 0`, with `φ_π ≠ 0` and `|φ_π + ρ| > 1` (which under `φ_π, ρ ≥ 0` is `φ_π > 0 ∧
φ_π + ρ > 1`, (2.13)). Then there are `ε, ε_π, δ > 0` such that whenever `r̂_t`, `ν_t` and the
predetermined `ĵ_{−1}` are within `δ`, there is an equilibrium with `|ĵ_t| ≤ ε` and `|π_t| ≤ ε_π`,
and it is the only one in that neighbourhood. -/
theorem inertial_local_determinacy {β : ℝ} {ψ : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hψ : ContDiffAt ℝ 1 ψ 0) (h0 : ψ 0 = 0) (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0)
    (hdet : 1 < |phiPi ψ + rhoR ψ|) :
    ∃ ε > 0, ∃ εP > 0, ∃ δ > 0, ∀ uc ν : ℕ → ℝ, ∀ im1 : ℝ, (∀ t, 0 < uc t) → 0 < 1 + im1 →
      (∀ t, |Real.log (uc t / uc (t + 1))| ≤ δ) → (∀ t, |ν t| ≤ δ) →
      |Real.log (β * (1 + im1))| ≤ δ →
      (∃ Infl i : ℕ → ℝ, InertialEq β ψ uc ν im1 Infl i ∧
        ∀ t, |Real.log (β * (1 + i t))| ≤ ε ∧ |Real.log (Infl t)| ≤ εP) ∧
      ∀ Infl i Infl' i' : ℕ → ℝ, InertialEq β ψ uc ν im1 Infl i →
        InertialEq β ψ uc ν im1 Infl' i' →
        (∀ t, |Real.log (β * (1 + i t))| ≤ ε ∧ |Real.log (Infl t)| ≤ εP) →
        (∀ t, |Real.log (β * (1 + i' t))| ≤ ε ∧ |Real.log (Infl' t)| ≤ εP) →
        Infl = Infl' ∧ i = i' := by
  obtain ⟨ρΘ, hρΘ, hL, hR⟩ := solveRule_local hψ hφ h0
  obtain ⟨ρc, hρc, hsmall⟩ := solveRule_small hψ hφ h0 (half_pos hρΘ)
  obtain ⟨ha, hb, -⟩ := slopes_F8 hψ hφ h0
  have hab : |slopeB (F8 ψ hψ hφ)| < |slopeA (F8 ψ hψ hφ)| := by
    rw [ha, hb]
    exact (inertial_slope_iff hφ).mpr hdet
  set η := min ρΘ ρc / 4 with hη
  have hη0 : 0 < η := by positivity
  have hηΘ : η < ρΘ / 2 := by have := min_le_left ρΘ ρc; linarith
  have hηc : η < ρc := by have := min_le_right ρΘ ρc; linarith
  obtain ⟨ε, hε, hεη, δ, hδ, hδη, X, -, -, hX⟩ :=
    local_determinacy_loc (contDiffAt_F8 hψ hφ h0 hψ) (F8_zero hψ hφ h0) hab hη0
  refine ⟨ε / 2, half_pos hε, ρΘ / 2, half_pos hρΘ, δ / 2, half_pos hδ,
    fun uc ν im1 huc him1 hr hν hj => ?_⟩
  have hK : ∀ t, ‖((Real.log (uc t / uc (t + 1)), ν (t + 1)) : ℝ × ℝ)‖ ≤ δ / 2 := fun t => by
    rw [norm_prod_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
    exact ⟨hr t, hν (t + 1)⟩
  set e : Seq (ℝ × ℝ) := mkS (fun t => ((Real.log (uc t / uc (t + 1)), ν (t + 1)) : ℝ × ℝ))
    ⟨δ / 2, hK⟩ with he
  have hen : ‖e‖ < δ := lt_of_le_of_lt (norm_seq_le (by positivity) hK) (half_lt_self hδ)
  obtain ⟨hXn, hXs, -, huniq⟩ := hX e hen
  have hnorm3 : ∀ a b c : ℝ, |a| < ρΘ → |b| < ρΘ → |c| < ρΘ →
      ‖((a, b, c) : ℝ × ℝ × ℝ)‖ < ρΘ := fun a b c ha hb hc => by
    rw [Prod.norm_mk, Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_lt ha (max_lt hb hc)
  -- every small equilibrium gives a solution of the period condition
  have hsolve : ∀ Infl i : ℕ → ℝ, InertialEq β ψ uc ν im1 Infl i →
      (∀ t, |Real.log (β * (1 + i t))| ≤ ε / 2 ∧ |Real.log (Infl t)| ≤ ρΘ / 2) → ∀ t,
      Real.log (β * (1 + i t)) - Real.log (uc t / uc (t + 1)) -
        solveRule ψ hψ hφ (Real.log (β * (1 + i (t + 1))), Real.log (β * (1 + i t)), ν (t + 1)) =
          0 := by
    rintro Infl i ⟨hP, hF, hrule⟩ hbd t
    have hfl := fisher_log hβ (huc t) (huc (t + 1)) (hP (t + 1)) (hF t)
    have hq : ‖((Real.log (Infl (t + 1)), Real.log (β * (1 + i t)), ν (t + 1)) : ℝ × ℝ × ℝ)‖ <
        ρΘ := hnorm3 _ _ _ (by linarith [(hbd (t + 1)).2]) (by linarith [(hbd t).1])
          (by linarith [hν (t + 1)])
    have h1 := hL _ hq
    have hr1 := hrule (t + 1)
    simp only [jLag] at hr1
    rw [← hr1] at h1
    simp only at h1
    rw [h1, hfl]
    ring
  have hclass : ∀ Infl i : ℕ → ℝ, InertialEq β ψ uc ν im1 Infl i →
      ∀ hbd : (∀ t, |Real.log (β * (1 + i t))| ≤ ε / 2 ∧ |Real.log (Infl t)| ≤ ρΘ / 2),
      mk (fun t => Real.log (β * (1 + i t))) ⟨ε / 2, fun t => (hbd t).1⟩ = X e :=
    fun Infl i hE hbd => huniq _
      (lt_of_le_of_lt (norm_le_of_abs_le (by positivity) (fun t => (hbd t).1)) (half_lt_self hε))
      (fun t => hsolve Infl i hE hbd t)
  refine ⟨?_, ?_⟩
  · set x := X e with hx
    set j1 := Real.log (β * (1 + im1)) with hj1
    set θ0 := solveRule ψ hψ hφ (x 0, j1, ν 0) with hθ0
    set Infl := inflPath θ0 x (fun t => Real.log (uc t / uc (t + 1))) with hInfl
    have hxj : ∀ t, Real.log (β * (1 + (Real.exp (x t) / β - 1))) = x t := fun t => by
      rw [show β * (1 + (Real.exp (x t) / β - 1)) = Real.exp (x t) by field_simp; ring,
        Real.log_exp]
    have hxt : ∀ t, |x t| < ε / 2 := fun t => lt_of_le_of_lt (abs_apply_le x t) hXn
    have hθ0b : |θ0| < ρΘ / 2 := hsmall _ (by
      rw [Prod.norm_mk, Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_lt (by linarith [hxt 0]) (max_lt (by linarith) (by linarith [hν 0])))
    refine ⟨Infl, fun t => Real.exp (x t) / β - 1, ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩,
      fun t => ⟨by rw [hxj]; exact (hxt t).le, ?_⟩⟩
    · cases t <;> exact Real.exp_pos _
    · change 1 + (Real.exp (x t) / β - 1) = uc t / (β * uc (t + 1)) *
        Real.exp (x t - Real.log (uc t / uc (t + 1)))
      rw [Real.exp_sub, Real.exp_log (div_pos (huc t) (huc (t + 1)))]
      have := huc t
      have := huc (t + 1)
      field_simp
      ring
    · rw [hxj]
      cases t with
      | zero =>
        change x 0 = ψ (Real.log (Real.exp θ0), j1, ν 0)
        rw [Real.log_exp, hθ0]
        exact (hR _ (hnorm3 _ _ _ (by linarith [hxt 0]) (by linarith) (by linarith [hν 0]))).symm
      | succ t =>
        change x (t + 1) = ψ (Real.log (Real.exp (x t - Real.log (uc t / uc (t + 1)))),
          Real.log (β * (1 + (Real.exp (x t) / β - 1))), ν (t + 1))
        rw [Real.log_exp, hxj]
        have hs := hXs t
        simp only [F8, he, mkS_apply, lagMap_apply] at hs
        rw [show x t - Real.log (uc t / uc (t + 1)) = solveRule ψ hψ hφ (x (t + 1), x t, ν (t + 1))
          by linarith]
        exact (hR _ (hnorm3 _ _ _ (by linarith [hxt (t + 1)]) (by linarith [hxt t])
          (by linarith [hν (t + 1)]))).symm
    · cases t with
      | zero =>
        change |Real.log (Real.exp θ0)| ≤ ρΘ / 2
        rw [Real.log_exp]
        exact hθ0b.le
      | succ t =>
        change |Real.log (Real.exp (x t - Real.log (uc t / uc (t + 1))))| ≤ ρΘ / 2
        rw [Real.log_exp]
        have := abs_sub (x t) (Real.log (uc t / uc (t + 1)))
        linarith [hxt t, hr t]
  · intro Infl i Infl' i' hE hE' hb hb'
    have hlog : ∀ t, Real.log (β * (1 + i t)) = Real.log (β * (1 + i' t)) := fun t =>
      congrArg (fun y : Linf => y t) ((hclass Infl i hE hb).trans (hclass Infl' i' hE' hb').symm)
    have hpos : ∀ (I : ℕ → ℝ) (j : ℕ → ℝ), InertialEq β ψ uc ν im1 I j → ∀ t, 0 < β * (1 + j t) :=
      fun I j h t => by
        rw [h.2.1 t]
        have := huc t
        have := huc (t + 1)
        have := h.1 (t + 1)
        positivity
    have hii : i = i' := funext fun t => by
      have h := Real.log_injOn_pos (Set.mem_Ioi.mpr (hpos _ _ hE t))
        (Set.mem_Ioi.mpr (hpos _ _ hE' t)) (hlog t)
      have := hβ.ne'
      field_simp at h
      linarith
    refine ⟨funext fun t => ?_, hii⟩
    cases t with
    | zero =>
      have q1 := hL ((Real.log (Infl 0), Real.log (β * (1 + im1)), ν 0) : ℝ × ℝ × ℝ)
        (hnorm3 _ _ _ (by linarith [(hb 0).2]) (by linarith) (by linarith [hν 0]))
      have q2 := hL ((Real.log (Infl' 0), Real.log (β * (1 + im1)), ν 0) : ℝ × ℝ × ℝ)
        (hnorm3 _ _ _ (by linarith [(hb' 0).2]) (by linarith) (by linarith [hν 0]))
      have r1 := hE.2.2 0
      have r2 := hE'.2.2 0
      simp only [jLag] at r1 r2
      rw [← r1] at q1
      rw [← r2, ← hii] at q2
      simp only at q1 q2
      have hl : Real.log (Infl 0) = Real.log (Infl' 0) := q1.symm.trans q2
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr (hE.1 0)) (Set.mem_Ioi.mpr (hE'.1 0)) hl
    | succ t =>
      have h1 := hE.2.1 t
      have h2 := hE'.2.1 t
      rw [hii] at h1
      have hu : 0 < uc t / (β * uc (t + 1)) := by
        have := huc t
        have := huc (t + 1)
        positivity
      have := h1.symm.trans h2
      exact mul_left_cancel₀ hu.ne' this

/-- Woodford (2003), A.8, p. 641: near the steady state every inertial-rule equilibrium solves the
period condition `F8` (the rule is inverted with `Θ`). -/
theorem inertial_solves {β ρΘ : ℝ} {ψ : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β) {hψ : ContDiffAt ℝ 1 ψ 0}
    {hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0}
    (hL : ∀ q : ℝ × ℝ × ℝ, ‖q‖ < ρΘ → solveRule ψ hψ hφ (ψ q, q.2) = q.1)
    {uc ν Infl i : ℕ → ℝ} {im1 : ℝ} (huc : ∀ t, 0 < uc t) (hE : InertialEq β ψ uc ν im1 Infl i)
    (hb : ∀ t, |Real.log (Infl t)| < ρΘ ∧ |Real.log (β * (1 + i t))| < ρΘ ∧ |ν t| < ρΘ) (t : ℕ) :
    Real.log (β * (1 + i t)) - Real.log (uc t / uc (t + 1)) -
      solveRule ψ hψ hφ (Real.log (β * (1 + i (t + 1))), Real.log (β * (1 + i t)), ν (t + 1)) =
        0 := by
  obtain ⟨hP, hF, hrule⟩ := hE
  have hfl := fisher_log hβ (huc t) (huc (t + 1)) (hP (t + 1)) (hF t)
  have hq : ‖((Real.log (Infl (t + 1)), Real.log (β * (1 + i t)), ν (t + 1)) : ℝ × ℝ × ℝ)‖ <
      ρΘ := by
    rw [Prod.norm_mk, Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_lt (hb (t + 1)).1 (max_lt (hb t).2.1 (hb (t + 1)).2.2)
  have h1 := hL _ hq
  have hr1 := hrule (t + 1)
  simp only [jLag] at hr1
  rw [← hr1] at h1
  simp only at h1
  rw [h1, hfl]
  ring

/-- Woodford (2003), A.8, p. 641: conversely, a small solution `ĵ` of the period condition `F8`
gives an inertial-rule equilibrium, with `i_t = β⁻¹ e^{ĵ_t} − 1`, `Π_{t+1} = e^{ĵ_t − r̂_t}` and
`Π_0 = e^{Θ(ĵ_0, ĵ_{−1}, ν_0)}`. -/
theorem inertialEq_of_solution {β ρΘ : ℝ} {ψ : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β)
    {hψ : ContDiffAt ℝ 1 ψ 0} {hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0}
    (hR : ∀ q : ℝ × ℝ × ℝ, ‖q‖ < ρΘ → ψ (solveRule ψ hψ hφ q, q.2) = q.1)
    {uc ν x : ℕ → ℝ} {im1 : ℝ} (huc : ∀ t, 0 < uc t)
    (hsol : ∀ t, x t - Real.log (uc t / uc (t + 1)) -
      solveRule ψ hψ hφ (x (t + 1), x t, ν (t + 1)) = 0)
    (hx : ∀ t, |x t| < ρΘ) (hν : ∀ t, |ν t| < ρΘ) (hj : |Real.log (β * (1 + im1))| < ρΘ) :
    InertialEq β ψ uc ν im1
      (inflPath (solveRule ψ hψ hφ (x 0, Real.log (β * (1 + im1)), ν 0)) x
        (fun t => Real.log (uc t / uc (t + 1)))) (fun t => Real.exp (x t) / β - 1) ∧
      ∀ t, Real.log (β * (1 + (Real.exp (x t) / β - 1))) = x t := by
  have hxj : ∀ t, Real.log (β * (1 + (Real.exp (x t) / β - 1))) = x t := fun t => by
    rw [show β * (1 + (Real.exp (x t) / β - 1)) = Real.exp (x t) by field_simp; ring,
      Real.log_exp]
  have hnorm3 : ∀ a b c : ℝ, |a| < ρΘ → |b| < ρΘ → |c| < ρΘ →
      ‖((a, b, c) : ℝ × ℝ × ℝ)‖ < ρΘ := fun a b c ha hb hc => by
    rw [Prod.norm_mk, Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_lt ha (max_lt hb hc)
  refine ⟨⟨fun t => ?_, fun t => ?_, fun t => ?_⟩, hxj⟩
  · cases t <;> exact Real.exp_pos _
  · change 1 + (Real.exp (x t) / β - 1) = uc t / (β * uc (t + 1)) *
      Real.exp (x t - Real.log (uc t / uc (t + 1)))
    rw [Real.exp_sub, Real.exp_log (div_pos (huc t) (huc (t + 1)))]
    have := huc t
    have := huc (t + 1)
    field_simp
    ring
  · rw [hxj]
    cases t with
    | zero =>
      change x 0 = ψ (Real.log (Real.exp (solveRule ψ hψ hφ (x 0, Real.log (β * (1 + im1)), ν 0))),
        Real.log (β * (1 + im1)), ν 0)
      rw [Real.log_exp]
      exact (hR _ (hnorm3 _ _ _ (hx 0) hj (hν 0))).symm
    | succ t =>
      change x (t + 1) = ψ (Real.log (Real.exp (x t - Real.log (uc t / uc (t + 1)))),
        Real.log (β * (1 + (Real.exp (x t) / β - 1))), ν (t + 1))
      rw [Real.log_exp, hxj]
      rw [show x t - Real.log (uc t / uc (t + 1)) = solveRule ψ hψ hφ (x (t + 1), x t, ν (t + 1))
        by linarith [hsol t]]
      exact (hR _ (hnorm3 _ _ _ (hx (t + 1)) (hx t) (hν (t + 1)))).symm

/-- Woodford (2003), **Proposition 2.8**, p. 96 and A.8, p. 641 (indeterminacy half: "If
`φ_π > 0` but `0 < φ_π + ρ < 1`, there is an uncountably infinite number of solutions"),
**exact perfect-foresight version**: if `φ_π ≠ 0` and `|φ_π + ρ| < 1`, then with constant
fundamentals (`u_c ≡ 1`, `ν ≡ 0`, `i_{−1} = ī`) every initial interest rate `ĵ_0 = c` with
`|c| ≤ r` starts an exact equilibrium staying within `ε` of the steady state; distinct `c` give
distinct equilibria. -/
theorem inertial_local_indeterminacy {β : ℝ} {ψ : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hψ : ContDiffAt ℝ 1 ψ 0) (h0 : ψ 0 = 0) (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0)
    (hind : |phiPi ψ + rhoR ψ| < 1) :
    ∀ ε > 0, ∃ r > 0, ∀ c : ℝ, |c| ≤ r → ∃ Infl i : ℕ → ℝ,
      InertialEq β ψ (fun _ => 1) (fun _ => 0) (β⁻¹ - 1) Infl i ∧
        Real.log (β * (1 + i 0)) = c ∧
        ∀ t, |Real.log (β * (1 + i t))| ≤ ε ∧ |Real.log (Infl t)| ≤ ε := by
  intro ε hε
  obtain ⟨ρΘ, hρΘ, -, hR⟩ := solveRule_local hψ hφ h0
  obtain ⟨ρc, hρc, hsmall⟩ := solveRule_small hψ hφ h0 hε
  obtain ⟨ha, hb, -⟩ := slopes_F8 hψ hφ h0
  have hab : |slopeA (F8 ψ hψ hφ)| < |slopeB (F8 ψ hψ hφ)| := by
    rw [ha, hb]
    exact (inertial_slope_iff' hφ).mpr hind
  set ε' := min ε (min ρΘ ρc) / 2 with hε'
  have hε'0 : 0 < ε' := by positivity
  have hε'ε : ε' < ε := by have := min_le_left ε (min ρΘ ρc); linarith
  have hε'Θ : ε' < ρΘ := by
    have := min_le_right ε (min ρΘ ρc); have := min_le_left ρΘ ρc; linarith
  have hε'c : ε' < ρc := by
    have := min_le_right ε (min ρΘ ρc); have := min_le_right ρΘ ρc; linarith
  obtain ⟨r, hr, hx⟩ := local_indeterminacy_loc (contDiffAt_F8 hψ hφ h0 hψ) (F8_zero hψ hφ h0)
    hab ε' hε'0
  refine ⟨r, hr, fun c hc => ?_⟩
  obtain ⟨x, hxs, hxn, hx0⟩ := hx c hc
  have hxt : ∀ t, |x t| ≤ ε' := fun t => (abs_apply_le x t).trans hxn
  have hj : Real.log (β * (1 + (β⁻¹ - 1))) = 0 := by
    rw [show β * (1 + (β⁻¹ - 1)) = 1 by field_simp; ring, Real.log_one]
  have hsol : ∀ t, x t - Real.log ((fun _ : ℕ => (1 : ℝ)) t / (fun _ : ℕ => (1 : ℝ)) (t + 1)) -
      solveRule ψ hψ hφ (x (t + 1), x t, (fun _ : ℕ => (0 : ℝ)) (t + 1)) = 0 := fun t => by
    have h := hxs t
    simp only [F8, lagMap_apply, lp.coeFn_zero, Pi.zero_apply, Prod.fst_zero,
      Prod.snd_zero] at h
    simpa using h
  obtain ⟨hE, hxj⟩ := inertialEq_of_solution (ρΘ := ρΘ) (uc := fun _ => 1) (ν := fun _ => 0)
    (im1 := β⁻¹ - 1) hβ hR (fun _ => one_pos) hsol
    (fun t => lt_of_le_of_lt (hxt t) hε'Θ) (fun _ => by simpa using hρΘ)
    (by rw [hj, abs_zero]; exact hρΘ)
  refine ⟨_, _, hE, by rw [hxj, hx0], fun t => ⟨by rw [hxj]; linarith [hxt t], ?_⟩⟩
  cases t with
  | zero =>
    change |Real.log (Real.exp (solveRule ψ hψ hφ (x 0, Real.log (β * (1 + (β⁻¹ - 1))), 0)))| ≤ ε
    rw [Real.log_exp, hj]
    refine (hsmall _ ?_).le
    rw [Prod.norm_mk, Prod.norm_mk, Real.norm_eq_abs, norm_zero, max_eq_left (le_refl _),
      max_eq_left (abs_nonneg _)]
    linarith [hxt 0]
  | succ t =>
    change |Real.log (Real.exp (x t - Real.log (1 / 1)))| ≤ ε
    rw [Real.log_exp, div_one, Real.log_one, sub_zero]
    linarith [hxt t]

/-- Woodford (2003), Prop. 2.8, p. 96 and App. A.3, p. 633 (`C¹` dependence): the interest-rate
path `ĵ = X(r̂, ν)` of the exact inertial-rule model is a `C¹` function of the disturbances near
zero, with `X(0) = 0` and derivative the log-linear solution (2.15). -/
theorem inertial_smooth_dependence {ψ : ℝ × ℝ × ℝ → ℝ} (hψ : ContDiffAt ℝ 1 ψ 0) (h0 : ψ 0 = 0)
    (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) (hdet : 1 < |phiPi ψ + rhoR ψ|) :
    ∃ δ > 0, ∃ X : Seq (ℝ × ℝ) → Linf, X 0 = 0 ∧ HasFDerivAt X (linSol3 (F8 ψ hψ hφ)) 0 ∧
      ∀ e : Seq (ℝ × ℝ), ‖e‖ < δ → Solves (F8 ψ hψ hφ) e (X e) ∧ ContDiffAt ℝ 1 X e := by
  obtain ⟨ha, hb, -⟩ := slopes_F8 hψ hφ h0
  have hab : |slopeB (F8 ψ hψ hφ)| < |slopeA (F8 ψ hψ hφ)| := by
    rw [ha, hb]
    exact (inertial_slope_iff hφ).mpr hdet
  obtain ⟨ε, hε, -, δ, hδ, -, X, hX0, hXd, hX⟩ :=
    local_determinacy_loc (contDiffAt_F8 hψ hφ h0 hψ) (F8_zero hψ hφ h0) hab one_pos
  exact ⟨δ, hδ, X, hX0, hXd, fun e he => ⟨(hX e he).2.1, (hX e he).2.2.1⟩⟩

/-- Woodford (2003), (2.15), p. 96, exact first-order term: the log-linear interest-rate path is
`ĵ_t = ∑_k (φ_π + ρ)^{−(k+1)} (φ_π r̂_{t+k} − c ν_{t+k+1})`. -/
theorem linSol3_F8_apply {ψ : ℝ × ℝ × ℝ → ℝ} (hψ : ContDiffAt ℝ 1 ψ 0) (h0 : ψ 0 = 0)
    (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) (hdet : 1 < |phiPi ψ + rhoR ψ|) (e : Seq (ℝ × ℝ))
    (t : ℕ) :
    linSol3 (F8 ψ hψ hφ) e t = ∑' k, ((phiPi ψ + rhoR ψ)⁻¹) ^ (k + 1) *
      (phiPi ψ * (e (t + k)).1 - nuR ψ * (e (t + k)).2) := by
  obtain ⟨ha, hb, hc⟩ := slopes_F8 hψ hφ h0
  have hab : |slopeB (F8 ψ hψ hφ)| < |slopeA (F8 ψ hψ hφ)| := by
    rw [ha, hb]
    exact (inertial_slope_iff hφ).mpr hdet
  have hs0 : phiPi ψ + rhoR ψ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hdet
    linarith
  rw [linSol3_apply hab, ← neg_mul, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hv : e (t + k) = ((e (t + k)).1, (e (t + k)).2) := rfl
  rw [ha, hb, hv, hc]
  have hφ' : phiPi ψ ≠ 0 := hφ
  rw [pow_succ]
  field_simp
  ring

/-- Woodford (2003), **Proposition 2.8**, p. 96 ("a log-linear approximation to the equilibrium
evolution … (2.14), (2.15)"), exact perfect-foresight version with the `C²` hypothesis of E18:
every inertial-rule equilibrium near the steady state satisfies
`|ĵ_t − ∑_k (φ_π + ρ)^{−(k+1)} (φ_π r̂_{t+k} − c ν_{t+k+1})| ≤ C ξ²` when `r̂`, `ν` are bounded by
`ξ < δ`. -/
theorem inertial_second_order {β : ℝ} {ψ : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hψ : ContDiffAt ℝ 1 ψ 0) (hψ2 : ContDiffAt ℝ 2 ψ 0) (h0 : ψ 0 = 0)
    (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) (hdet : 1 < |phiPi ψ + rhoR ψ|) :
    ∃ ε > 0, ∃ δ > 0, ∃ C : ℝ, ∀ uc ν : ℕ → ℝ, ∀ im1 ξb : ℝ, (∀ t, 0 < uc t) → ξb < δ →
      (∀ t, |Real.log (uc t / uc (t + 1))| ≤ ξb) → (∀ t, |ν t| ≤ ξb) →
      ∀ Infl i : ℕ → ℝ, InertialEq β ψ uc ν im1 Infl i →
      (∀ t, |Real.log (β * (1 + i t))| ≤ ε ∧ |Real.log (Infl t)| ≤ ε) →
      ∀ t, |Real.log (β * (1 + i t)) - ∑' k, ((phiPi ψ + rhoR ψ)⁻¹) ^ (k + 1) *
        (phiPi ψ * Real.log (uc (t + k) / uc (t + k + 1)) - nuR ψ * ν (t + k + 1))| ≤
        C * ξb ^ 2 := by
  obtain ⟨ρΘ, hρΘ, hL, -⟩ := solveRule_local hψ hφ h0
  obtain ⟨ha, hb, -⟩ := slopes_F8 hψ hφ h0
  have hab : |slopeB (F8 ψ hψ hφ)| < |slopeA (F8 ψ hψ hφ)| := by
    rw [ha, hb]
    exact (inertial_slope_iff hφ).mpr hdet
  obtain ⟨ε, hε, hεη, δ, hδ, hδη, C, hC⟩ :=
    second_order_loc (contDiffAt_F8 hψ hφ h0 hψ2) (F8_zero hψ hφ h0) hab (half_pos hρΘ)
  refine ⟨ε / 2, half_pos hε, δ / 2, half_pos hδ, max C 0,
    fun uc ν im1 ξb huc hξb hr hν Infl i hE hbd t => ?_⟩
  have hξ0 : 0 ≤ ξb := (abs_nonneg _).trans (hν 0)
  have hK : ∀ t, ‖((Real.log (uc t / uc (t + 1)), ν (t + 1)) : ℝ × ℝ)‖ ≤ ξb := fun t => by
    rw [norm_prod_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
    exact ⟨hr t, hν (t + 1)⟩
  set e : Seq (ℝ × ℝ) := mkS (fun t => ((Real.log (uc t / uc (t + 1)), ν (t + 1)) : ℝ × ℝ))
    ⟨ξb, hK⟩ with he
  have hen : ‖e‖ ≤ ξb := norm_seq_le hξ0 hK
  have hsol : Solves (F8 ψ hψ hφ) e
      (mk (fun t => Real.log (β * (1 + i t))) ⟨ε / 2, fun t => (hbd t).1⟩) := fun s =>
    inertial_solves (ρΘ := ρΘ) hβ hL huc hE (fun t => ⟨by linarith [(hbd t).2],
      by linarith [(hbd t).1], by linarith [hν t]⟩) s
  have hbound := hC e (lt_of_le_of_lt hen (by linarith)) _
    (lt_of_le_of_lt (norm_le_of_abs_le (by positivity) (fun t => (hbd t).1)) (half_lt_self hε))
    hsol
  have hcoord := abs_apply_le (mk (fun t => Real.log (β * (1 + i t))) ⟨ε / 2, fun t => (hbd t).1⟩ -
    linSol3 (F8 ψ hψ hφ) e) t
  simp only [lp.coeFn_sub, Pi.sub_apply, mk_apply] at hcoord
  rw [linSol3_F8_apply hψ h0 hφ hdet] at hcoord
  simp only [he, mkS_apply] at hcoord
  refine hcoord.trans (hbound.trans ?_)
  calc C * ‖e‖ ^ 2 ≤ max C 0 * ‖e‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    _ ≤ max C 0 * ξb ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hen 2) (le_max_right _ _)

/-! ### Non-separable utility (§3.4, pp. 111–117): `(1.21) → (3.11) → (3.12)` as exact derivatives

With `u_c = u_c(Y, m; ξ)`, the perfect-foresight Euler equation (1.21) reads
`log(β(1 + i_t)) = λ_t − λ_{t+1} + π_{t+1}`, `λ = log u_c(Y, m; ξ)`. Its derivative is (3.11)
(`euler311`, `hasFDerivAt_euler311`, composing `NonSeparable.hasFDerivAt_logMU`). Substituting
the money-demand relation (3.5) `m = L(Y, Δ; ξ)` with `Δ = 1 − β(1 + īᵐ)e^{−ĵ}`
(`iᵐ = īᵐ`), `λ` becomes the function `lamI(ĵ, ŷ, ξ)` of the interest rate, whose derivative
`−χ η_i ĵ + (−σ⁻¹ + χ η_y) ŷ + (χ ε + u_cξ/u_c) ξ` is the substitution of (3.6) into (3.11), i.e.
the source of (3.12) (`lamI_coeffs`). -/

/-- Woodford (2003), (1.21) and (3.11), pp. 72, 114, perfect foresight: the right-hand side of the
log Euler equation `log(β(1 + i_t)) = λ_t − λ_{t+1} + π_{t+1}` as a function of
`((ŷ_t, m̂_t), (ŷ_{t+1}, m̂_{t+1}), π_{t+1})`, with `λ = NonSeparable.logMU`. -/
noncomputable def euler311 (Uc : ℝ × ℝ → ℝ) (Ybar mbar : ℝ) (v : (ℝ × ℝ) × (ℝ × ℝ) × ℝ) : ℝ :=
  NonSeparable.logMU Uc Ybar mbar v.1 - NonSeparable.logMU Uc Ybar mbar v.2.1 + v.2.2

/-- Woodford (2003), (1.21), p. 72 with `u_c(Y, m)`: the exact perfect-foresight Euler equation
`1 + i_t = u_c(t)/(β u_c(t+1)) Π_{t+1}` is `log(β(1 + i_t)) = euler311(…)` in log deviations. -/
theorem euler_iff_euler311 {Uc : ℝ × ℝ → ℝ} {β Ybar mbar Y0 Y1 m0 m1 Q1 i : ℝ} (hβ : 0 < β)
    (hY : 0 < Ybar) (hm : 0 < mbar) (hY0 : 0 < Y0) (hY1 : 0 < Y1) (hm0 : 0 < m0) (hm1 : 0 < m1)
    (hQ : 0 < Q1) (hU0 : 0 < Uc (Y0, m0)) (hU1 : 0 < Uc (Y1, m1)) (hi : 0 < 1 + i) :
    1 + i = Uc (Y0, m0) / (β * Uc (Y1, m1)) * Q1 ↔
      Real.log (β * (1 + i)) = euler311 Uc Ybar mbar
        ((Real.log (Y0 / Ybar), Real.log (m0 / mbar)), (Real.log (Y1 / Ybar),
          Real.log (m1 / mbar)), Real.log Q1) := by
  have e : ∀ Y m : ℝ, 0 < Y → 0 < m →
      NonSeparable.logMU Uc Ybar mbar (Real.log (Y / Ybar), Real.log (m / mbar)) =
        Real.log (Uc (Y, m)) - Real.log (Uc (Ybar, mbar)) := fun Y m hY' hm' => by
    simp only [NonSeparable.logMU]
    rw [Real.exp_log (by positivity), Real.exp_log (by positivity)]
    congr 3
    field_simp
  simp only [euler311]
  rw [e Y0 m0 hY0 hm0, e Y1 m1 hY1 hm1]
  have hR : 0 < Uc (Y0, m0) / (β * Uc (Y1, m1)) * Q1 := by positivity
  constructor
  · intro h
    rw [h, show β * (Uc (Y0, m0) / (β * Uc (Y1, m1)) * Q1) = Uc (Y0, m0) / Uc (Y1, m1) * Q1 by
      field_simp, Real.log_mul (by positivity) hQ.ne', Real.log_div hU0.ne' hU1.ne']
    ring
  · intro h
    have h' : Real.log (β * (1 + i)) = Real.log (β * (Uc (Y0, m0) / (β * Uc (Y1, m1)) * Q1)) := by
      rw [h, show β * (Uc (Y0, m0) / (β * Uc (Y1, m1)) * Q1) = Uc (Y0, m0) / Uc (Y1, m1) * Q1 by
        field_simp, Real.log_mul (by positivity) hQ.ne', Real.log_div hU0.ne' hU1.ne']
      ring
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr (mul_pos hβ hi))
      (Set.mem_Ioi.mpr (mul_pos hβ hR)) h'
    have hβ' := hβ.ne'
    field_simp at this ⊢
    linarith

/-- Woodford (2003), **(1.21) → (3.11)**, p. 114, as an exact derivative (task: the analogue of
`LogLinear.fisher_composite_deriv` with real-balance effects): if `u_c` is differentiable at
`(Ȳ, m̄)` with `u_c > 0`, the derivative of the exact log Euler equation at the steady state is
`σ⁻¹(ŷ_{t+1} − ŷ_t) + π_{t+1} − χ(m̂_{t+1} − m̂_t)`, i.e. (3.11)
`î_t = r̂_t + π_{t+1} − χ(m̂_{t+1} − m̂_t)` with `r̂_t = σ⁻¹(Ŷ_{t+1} − Ŷ_t)` (1.33). -/
theorem hasFDerivAt_euler311 {Uc : ℝ × ℝ → ℝ} {U' : ℝ × ℝ →L[ℝ] ℝ} {Ybar mbar : ℝ}
    (hU : HasFDerivAt Uc U' (Ybar, mbar)) (hpos : 0 < Uc (Ybar, mbar)) :
    ∃ G' : (ℝ × ℝ) × (ℝ × ℝ) × ℝ →L[ℝ] ℝ, HasFDerivAt (euler311 Uc Ybar mbar) G' 0 ∧
      ∀ y m y' m' π : ℝ, G' ((y, m), (y', m'), π) =
        -(U' (1, 0)) * Ybar / Uc (Ybar, mbar) * (y' - y) + π -
          NonSeparable.chi mbar (Uc (Ybar, mbar)) (U' (0, 1)) * (m' - m) := by
  obtain ⟨D, hD, hDv⟩ := NonSeparable.hasFDerivAt_logMU hU hpos
  let P1 : (ℝ × ℝ) × (ℝ × ℝ) × ℝ →L[ℝ] ℝ × ℝ := ContinuousLinearMap.fst ℝ (ℝ × ℝ) ((ℝ × ℝ) × ℝ)
  let P2 : (ℝ × ℝ) × (ℝ × ℝ) × ℝ →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ((ℝ × ℝ) × ℝ))
  let P3 : (ℝ × ℝ) × (ℝ × ℝ) × ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ((ℝ × ℝ) × ℝ))
  have hD1 : HasFDerivAt (NonSeparable.logMU Uc Ybar mbar) D (P1 0) := by rw [map_zero]; exact hD
  have hD2 : HasFDerivAt (NonSeparable.logMU Uc Ybar mbar) D (P2 0) := by rw [map_zero]; exact hD
  have h := ((hD1.comp 0 P1.hasFDerivAt).sub (hD2.comp 0 P2.hasFDerivAt)).add P3.hasFDerivAt
  refine ⟨_, h, fun y m y' m' π => ?_⟩
  simp only [add_apply, sub_apply, ContinuousLinearMap.comp_apply]
  rw [show P1 ((y, m), (y', m'), π) = (y, m) from rfl, show P2 ((y, m), (y', m'), π) = (y', m')
    from rfl, show P3 ((y, m), (y', m'), π) = π from rfl, hDv, hDv]
  simp only
  ring

/-- Woodford (2003), (3.5), (3.11), pp. 104, 114: log marginal utility of consumption as a
function of `(ĵ, ŷ, ξ)` once real balances are given by money demand (3.5) with `iᵐ = īᵐ`,
`λ = log u_c(Ȳe^{ŷ}, L(Ȳe^{ŷ}, 1 − β(1 + īᵐ)e^{−ĵ}, ξ), ξ)` (`Δ = (i − īᵐ)/(1 + i)`). -/
noncomputable def lamI (β ibm Ybar : ℝ) (L Uc : ℝ × ℝ × ℝ → ℝ) (q : ℝ × ℝ × ℝ) : ℝ :=
  Real.log (Uc (Ybar * Real.exp q.2.1,
    L (Ybar * Real.exp q.2.1, 1 - β * (1 + ibm) * Real.exp (-q.1), q.2.2), q.2.2))

/-- Woodford (2003), (3.5), p. 104: the real balances inside `lamI` are `L(Y, Δ, ξ)` with
`Δ = (i − īᵐ)/(1 + i)` when `ĵ = log(β(1 + i))`. -/
theorem spread_of_j {β ibm i : ℝ} (hβ : 0 < β) (hi : 0 < 1 + i) :
    1 - β * (1 + ibm) * Real.exp (-Real.log (β * (1 + i))) = (i - ibm) / (1 + i) := by
  rw [Real.exp_neg, Real.exp_log (mul_pos hβ hi)]
  field_simp
  ring

/-- Woodford (2003), (3.11), p. 114: `lamI` is `Cⁿ` near the steady state when money demand and
`u_c` are. -/
theorem contDiffAt_lamI {β ibm Ybar mbar : ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ} {n : ℕ}
    (hL : ContDiffAt ℝ n L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ n Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0)) :
    ContDiffAt ℝ n (lamI β ibm Ybar L Uc) 0 := by
  have hg1 : ContDiff ℝ n (fun q : ℝ × ℝ × ℝ =>
      ((Ybar * Real.exp q.2.1, 1 - β * (1 + ibm) * Real.exp (-q.1), q.2.2) : ℝ × ℝ × ℝ)) := by
    fun_prop
  have hL' : ContDiffAt ℝ n L ((fun q : ℝ × ℝ × ℝ =>
      ((Ybar * Real.exp q.2.1, 1 - β * (1 + ibm) * Real.exp (-q.1), q.2.2) : ℝ × ℝ × ℝ)) 0) := by
    simpa using hL
  have hLc := hL'.comp (0 : ℝ × ℝ × ℝ) hg1.contDiffAt
  have hg2 : ContDiffAt ℝ n (fun q : ℝ × ℝ × ℝ => ((Ybar * Real.exp q.2.1,
      L (Ybar * Real.exp q.2.1, 1 - β * (1 + ibm) * Real.exp (-q.1), q.2.2), q.2.2) :
      ℝ × ℝ × ℝ)) 0 :=
    (by fun_prop : ContDiffAt ℝ n (fun q : ℝ × ℝ × ℝ => Ybar * Real.exp q.2.1) 0).prodMk
      (hLc.prodMk (by fun_prop))
  have h20 : (fun q : ℝ × ℝ × ℝ => ((Ybar * Real.exp q.2.1,
      L (Ybar * Real.exp q.2.1, 1 - β * (1 + ibm) * Real.exp (-q.1), q.2.2), q.2.2) :
      ℝ × ℝ × ℝ)) 0 = (Ybar, mbar, 0) := by simp [hLss]
  have hU' : ContDiffAt ℝ n Uc ((fun q : ℝ × ℝ × ℝ => ((Ybar * Real.exp q.2.1,
      L (Ybar * Real.exp q.2.1, 1 - β * (1 + ibm) * Real.exp (-q.1), q.2.2), q.2.2) :
      ℝ × ℝ × ℝ)) 0) := by rw [h20]; exact hU
  have hc := hU'.comp (0 : ℝ × ℝ × ℝ) hg2
  refine hc.log ?_
  simpa [hLss] using hUpos.ne'

/-- Woodford (2003), (3.6) substituted into (3.11), p. 114, **exact derivative**: with
`L' = DL(Ȳ, Δ̄, 0)` and `U' = Du_c(Ȳ, m̄, 0)`,
`Dλ(dĵ, dŷ, dξ) = [U'₁ Ȳ dŷ + U'₂ (L'₁ Ȳ dŷ + L'₂ β(1 + īᵐ) dĵ + L'₃ dξ) + U'₃ dξ] / u_c`. -/
theorem hasFDerivAt_lamI {β ibm Ybar mbar : ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ}
    (hL : DifferentiableAt ℝ L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : DifferentiableAt ℝ Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0)) :
    ∃ D : ℝ × ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (lamI β ibm Ybar L Uc) D 0 ∧
      ∀ j y x : ℝ, D (j, y, x) =
        (fderiv ℝ Uc (Ybar, mbar, 0) (1, 0, 0) * Ybar * y +
          fderiv ℝ Uc (Ybar, mbar, 0) (0, 1, 0) *
            (fderiv ℝ L (Ybar, 1 - β * (1 + ibm), 0) (1, 0, 0) * Ybar * y +
              fderiv ℝ L (Ybar, 1 - β * (1 + ibm), 0) (0, 1, 0) * (β * (1 + ibm)) * j +
              fderiv ℝ L (Ybar, 1 - β * (1 + ibm), 0) (0, 0, 1) * x) +
          fderiv ℝ Uc (Ybar, mbar, 0) (0, 0, 1) * x) / Uc (Ybar, mbar, 0) := by
  set L' := fderiv ℝ L (Ybar, 1 - β * (1 + ibm), 0) with hL'
  set U' := fderiv ℝ Uc (Ybar, mbar, 0) with hU'
  let J : ℝ × ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
  let Yp : ℝ × ℝ × ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  let Xp : ℝ × ℝ × ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  have hYe := (Yp.hasFDerivAt (x := 0)).exp.const_mul Ybar
  have hDe := ((J.hasFDerivAt (x := 0)).neg.exp.const_mul (β * (1 + ibm))).const_sub 1
  have hg1 := hYe.prodMk (hDe.prodMk (Xp.hasFDerivAt (x := 0)))
  have h10 : ((Ybar * Real.exp (Yp 0), 1 - β * (1 + ibm) * Real.exp (-J 0), Xp 0) :
      ℝ × ℝ × ℝ) = (Ybar, 1 - β * (1 + ibm), 0) := by simp
  have hLd : HasFDerivAt L L' ((Ybar * Real.exp (Yp 0), 1 - β * (1 + ibm) * Real.exp (-J 0),
      Xp 0)) := by rw [h10]; exact hL.hasFDerivAt
  have hLc := hLd.comp (0 : ℝ × ℝ × ℝ) hg1
  have hg2 := hYe.prodMk (hLc.prodMk (Xp.hasFDerivAt (x := 0)))
  have h20 : ((Ybar * Real.exp (Yp 0), (L ∘ fun q : ℝ × ℝ × ℝ => ((Ybar * Real.exp (Yp q),
      1 - β * (1 + ibm) * Real.exp (-J q), Xp q) : ℝ × ℝ × ℝ)) 0, Xp 0) : ℝ × ℝ × ℝ) =
      (Ybar, mbar, 0) := by simp [hLss]
  have hUd : HasFDerivAt Uc U' ((Ybar * Real.exp (Yp 0), (L ∘ fun q : ℝ × ℝ × ℝ =>
      ((Ybar * Real.exp (Yp q), 1 - β * (1 + ibm) * Real.exp (-J q), Xp q) : ℝ × ℝ × ℝ)) 0,
      Xp 0)) := by rw [h20]; exact hU.hasFDerivAt
  have hUc := hUd.comp (0 : ℝ × ℝ × ℝ) hg2
  have hne : (Uc ∘ fun q : ℝ × ℝ × ℝ => ((Ybar * Real.exp (Yp q), (L ∘ fun q : ℝ × ℝ × ℝ =>
      ((Ybar * Real.exp (Yp q), 1 - β * (1 + ibm) * Real.exp (-J q), Xp q) : ℝ × ℝ × ℝ)) q,
      Xp q) : ℝ × ℝ × ℝ)) 0 ≠ 0 := by
    simpa [J, Yp, Xp, hLss] using hUpos.ne'
  have hlog := hUc.log hne
  refine ⟨_, hlog, fun j y x => ?_⟩
  simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    smul_eq_mul, Function.comp_apply]
  rw [MoneyGrowth.clm3_apply U', MoneyGrowth.clm3_apply L']
  simp [J, Yp, Xp, hLss]
  field_simp

/-- Woodford (2003), (3.10)–(3.12), pp. 113–114, **the coefficients of `Dλ` are those of (3.12)**:
`∂λ/∂ĵ = −χ η_i`, `∂λ/∂ŷ = −σ⁻¹ + χ η_y`, `∂λ/∂ξ = χ ε + u_cξ/u_c`, with `χ = m̄ u_cm/u_c`
(`NonSeparable.chi`), `η_i, η_y, ε` the money-demand coefficients of (3.6)
(`MoneyGrowth.etaI`, `etaY`, `epsCoef`) and `σ⁻¹ = −u_cc Ȳ/u_c`. -/
theorem lamI_coeffs {β ibm Ybar mbar : ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ} (hm : 0 < mbar)
    {D : ℝ × ℝ × ℝ →L[ℝ] ℝ}
    (hD : ∀ j y x : ℝ, D (j, y, x) =
        (fderiv ℝ Uc (Ybar, mbar, 0) (1, 0, 0) * Ybar * y +
          fderiv ℝ Uc (Ybar, mbar, 0) (0, 1, 0) *
            (fderiv ℝ L (Ybar, 1 - β * (1 + ibm), 0) (1, 0, 0) * Ybar * y +
              fderiv ℝ L (Ybar, 1 - β * (1 + ibm), 0) (0, 1, 0) * (β * (1 + ibm)) * j +
              fderiv ℝ L (Ybar, 1 - β * (1 + ibm), 0) (0, 0, 1) * x) +
          fderiv ℝ Uc (Ybar, mbar, 0) (0, 0, 1) * x) / Uc (Ybar, mbar, 0))
    (hUpos : 0 < Uc (Ybar, mbar, 0)) :
    D (1, 0, 0) = -(NonSeparable.chi mbar (Uc (Ybar, mbar, 0)) (fderiv ℝ Uc (Ybar, mbar, 0)
        (0, 1, 0)) * MoneyGrowth.etaI (fderiv ℝ L (Ybar, 1 - β * (1 + ibm), 0)) mbar
          (1 - β * (1 + ibm))) ∧
      D (0, 1, 0) = -(-(fderiv ℝ Uc (Ybar, mbar, 0) (1, 0, 0)) * Ybar / Uc (Ybar, mbar, 0)) +
        NonSeparable.chi mbar (Uc (Ybar, mbar, 0)) (fderiv ℝ Uc (Ybar, mbar, 0) (0, 1, 0)) *
          MoneyGrowth.etaY (fderiv ℝ L (Ybar, 1 - β * (1 + ibm), 0)) Ybar mbar ∧
      D (0, 0, 1) = NonSeparable.chi mbar (Uc (Ybar, mbar, 0)) (fderiv ℝ Uc (Ybar, mbar, 0)
          (0, 1, 0)) * MoneyGrowth.epsCoef (fderiv ℝ L (Ybar, 1 - β * (1 + ibm), 0)) mbar +
        fderiv ℝ Uc (Ybar, mbar, 0) (0, 0, 1) / Uc (Ybar, mbar, 0) := by
  have hU0 := hUpos.ne'
  have hm0 := hm.ne'
  refine ⟨?_, ?_, ?_⟩ <;> rw [hD] <;>
    simp only [NonSeparable.chi, MoneyGrowth.etaI, MoneyGrowth.etaY, MoneyGrowth.epsCoef] <;>
    field_simp <;> ring

/-! ### Proposition 2.12: Wicksellian rule with non-separable utility (pp. 115–116, A.12)

Exact perfect-foresight model: (1.21) with `u_c(Y_t, m_t; ξ_t)`, the money-demand relation (3.5)
`m_t = L(Y_t, Δ_t; ξ_t)` with `Δ_t = (i_t − īᵐ)/(1 + i_t)` (interest on money fixed at `īᵐ`), and
the Wicksellian rule (1.30) `i_t = φ(P_t/P*_t; ν_t)`. In `p_t = log(P_t/P*_t)` it is the scalar
forward equation
`ĵ(p_t, ν_t) − λ(ĵ(p_t, ν_t), ŷ_t, ξ_t) + λ(ĵ(p_{t+1}, ν_{t+1}), ŷ_{t+1}, ξ_{t+1}) + p_t − p_{t+1}
 − π*_{t+1} = 0`, `ĵ = LocalIFT.logRule`, `λ = lamI`. -/

/-- Woodford (2003), (1.30), p. 77: the log rule is `Cⁿ` near the steady state when `φ` is `Cⁿ`
near `(1, 0)` (local version of `LocalIFT.contDiff_logRule`). -/
theorem contDiffAt_logRule {β : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β) (hss : 1 + φ (1, 0) = β⁻¹)
    {n : ℕ} (hφ : ContDiffAt ℝ n φ (1, 0)) : ContDiffAt ℝ n (LocalIFT.logRule β φ) 0 := by
  have hg : ContDiff ℝ n (fun p : ℝ × ℝ => ((Real.exp p.1, p.2) : ℝ × ℝ)) := by fun_prop
  have hφ' : ContDiffAt ℝ n φ ((fun p : ℝ × ℝ => ((Real.exp p.1, p.2) : ℝ × ℝ)) 0) := by
    simpa using hφ
  have hc := hφ'.comp (0 : ℝ × ℝ) hg.contDiffAt
  have hne : (1 + (φ ∘ fun p : ℝ × ℝ => ((Real.exp p.1, p.2) : ℝ × ℝ)) 0) ≠ 0 := by
    simp [hss, hβ.ne']
  exact ((contDiffAt_const.add hc).log hne).add contDiffAt_const

/-- Woodford (2003), (1.34), p. 81: the derivative of the log rule at the steady state is
`(a, ν) ↦ φ_p a + c_ν ν` (`LocalIFT.elast`, `LocalIFT.elastNu`). -/
theorem fderiv_logRule_apply {β : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β) (hss : 1 + φ (1, 0) = β⁻¹)
    (hφd : DifferentiableAt ℝ φ (1, 0)) (a ν : ℝ) :
    fderiv ℝ (LocalIFT.logRule β φ) 0 (a, ν) =
      LocalIFT.elast β φ * a + LocalIFT.elastNu β φ * ν := by
  obtain ⟨h1, h2⟩ := LocalIFT.slopes_logRule hβ hss hφd
  rw [LocalIFT.fderiv_zero_apply, h1, h2]

/-- Woodford (2003), (1.21), (3.5), (1.30), A.12 p. 645: the exact period condition of the
Wicksellian model with non-separable utility, in `(p_t, p_{t+1}, (s_t, s_{t+1}, π*_{t+1}))` with
`s = (ν, ŷ, ξ)`. -/
noncomputable def FW (β ibm Ybar : ℝ) (φ : ℝ × ℝ → ℝ) (L Uc : ℝ × ℝ × ℝ → ℝ)
    (p : ℝ × ℝ × ((ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ) × ℝ)) : ℝ :=
  LocalIFT.logRule β φ (p.1, p.2.2.1.1) -
    lamI β ibm Ybar L Uc (LocalIFT.logRule β φ (p.1, p.2.2.1.1), p.2.2.1.2.1, p.2.2.1.2.2) +
    lamI β ibm Ybar L Uc (LocalIFT.logRule β φ (p.2.1, p.2.2.2.1.1), p.2.2.2.1.2.1,
      p.2.2.2.1.2.2) + p.1 - p.2.1 - p.2.2.2.2

/-- Woodford (2003), A.12, p. 645: the steady state solves the period condition. -/
theorem FW_zero {β ibm Ybar : ℝ} {φ : ℝ × ℝ → ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ}
    (hss : 1 + φ (1, 0) = β⁻¹) : FW β ibm Ybar φ L Uc 0 = 0 := by
  have h := LocalIFT.logRule_zero (β := β) hss
  simp only [FW, Prod.fst_zero, Prod.snd_zero, Prod.mk_zero_zero, h]
  ring

/-- Woodford (2003), A.12, p. 645: the period condition is `Cⁿ` near the steady state. -/
theorem contDiffAt_FW {β ibm Ybar mbar : ℝ} {φ : ℝ × ℝ → ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ} {n : ℕ}
    (hβ : 0 < β) (hss : 1 + φ (1, 0) = β⁻¹) (hφ : ContDiffAt ℝ n φ (1, 0))
    (hL : ContDiffAt ℝ n L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ n Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0)) :
    ContDiffAt ℝ n (FW β ibm Ybar φ L Uc) 0 := by
  have hR := contDiffAt_logRule hβ hss hφ
  have hΛ := contDiffAt_lamI hL hLss hU hUpos
  have hR0 := LocalIFT.logRule_zero (β := β) hss
  let G := ℝ × ℝ × ((ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ) × ℝ)
  let X1 : G →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ _
  let X2 : G →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ _).comp (ContinuousLinearMap.snd ℝ ℝ _)
  let E3 : G →L[ℝ] (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ) × ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ _).comp (ContinuousLinearMap.snd ℝ ℝ _)
  let S : G →L[ℝ] ℝ × ℝ × ℝ := (ContinuousLinearMap.fst ℝ _ _).comp E3
  let S' : G →L[ℝ] ℝ × ℝ × ℝ :=
    (ContinuousLinearMap.fst ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp E3)
  let PI : G →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp E3)
  let Nu : (ℝ × ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ _
  let Yy : (ℝ × ℝ × ℝ) →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (ContinuousLinearMap.snd ℝ ℝ _)
  let Xx : (ℝ × ℝ × ℝ) →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    (ContinuousLinearMap.snd ℝ ℝ _)
  let A : G →L[ℝ] ℝ × ℝ := X1.prod (Nu.comp S)
  let A' : G →L[ℝ] ℝ × ℝ := X2.prod (Nu.comp S')
  have hRA : ContDiffAt ℝ n (LocalIFT.logRule β φ) (A 0) := by rw [map_zero]; exact hR
  have hRA' : ContDiffAt ℝ n (LocalIFT.logRule β φ) (A' 0) := by rw [map_zero]; exact hR
  have hJ := hRA.comp (0 : G) A.contDiff.contDiffAt
  have hJ' := hRA'.comp (0 : G) A'.contDiff.contDiffAt
  have hB := hJ.prodMk ((Yy.comp S).contDiff.contDiffAt.prodMk (Xx.comp S).contDiff.contDiffAt)
  have hB' := hJ'.prodMk ((Yy.comp S').contDiff.contDiffAt.prodMk
    (Xx.comp S').contDiff.contDiffAt)
  have hB0 : ((LocalIFT.logRule β φ ∘ A) 0, (Yy.comp S) 0, (Xx.comp S) 0) =
      (0 : ℝ × ℝ × ℝ) := by
    simp [hR0]
  have hB0' : ((LocalIFT.logRule β φ ∘ A') 0, (Yy.comp S') 0, (Xx.comp S') 0) =
      (0 : ℝ × ℝ × ℝ) := by
    simp [hR0]
  have hΛB : ContDiffAt ℝ n (lamI β ibm Ybar L Uc)
      ((LocalIFT.logRule β φ ∘ A) 0, (Yy.comp S) 0, (Xx.comp S) 0) := by rw [hB0]; exact hΛ
  have hΛB' : ContDiffAt ℝ n (lamI β ibm Ybar L Uc)
      ((LocalIFT.logRule β φ ∘ A') 0, (Yy.comp S') 0, (Xx.comp S') 0) := by rw [hB0']; exact hΛ
  have h := ((((hJ.sub (hΛB.comp (0 : G) hB)).add (hΛB'.comp (0 : G) hB')).add
    X1.contDiff.contDiffAt).sub X2.contDiff.contDiffAt).sub PI.contDiff.contDiffAt
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => rfl)

/-- Woodford (2003), (A.32), p. 645, **exact derivative** of the Wicksellian condition with
non-separable utility: with `ĵ' = φ_p dp + c_ν dν` and `Λ_j, Λ_y, Λ_ξ` the partials of `lamI`,
`DF = ĵ'(1 − Λ_j) − Λ_y dŷ − Λ_ξ dξ + Λ_j ĵ'₊ + Λ_y dŷ₊ + Λ_ξ dξ₊ + dp − dp₊ − dπ*`. -/
theorem hasFDerivAt_FW {β ibm Ybar mbar : ℝ} {φ : ℝ × ℝ → ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ}
    (hβ : 0 < β) (hss : 1 + φ (1, 0) = β⁻¹) (hφ : ContDiffAt ℝ 1 φ (1, 0))
    (hL : ContDiffAt ℝ 1 L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ 1 Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0)) :
    ∃ F' : ℝ × ℝ × ((ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ) × ℝ) →L[ℝ] ℝ,
      HasFDerivAt (FW β ibm Ybar φ L Uc) F' 0 ∧
      ∀ x x' ν y ξ ν' y' ξ' π : ℝ, F' (x, x', ((ν, y, ξ), (ν', y', ξ'), π)) =
        (LocalIFT.elast β φ * x + LocalIFT.elastNu β φ * ν) *
            (1 - fderiv ℝ (lamI β ibm Ybar L Uc) 0 (1, 0, 0)) -
          fderiv ℝ (lamI β ibm Ybar L Uc) 0 (0, 1, 0) * y -
          fderiv ℝ (lamI β ibm Ybar L Uc) 0 (0, 0, 1) * ξ +
          fderiv ℝ (lamI β ibm Ybar L Uc) 0 (1, 0, 0) *
            (LocalIFT.elast β φ * x' + LocalIFT.elastNu β φ * ν') +
          fderiv ℝ (lamI β ibm Ybar L Uc) 0 (0, 1, 0) * y' +
          fderiv ℝ (lamI β ibm Ybar L Uc) 0 (0, 0, 1) * ξ' + x - x' - π := by
  have hφd : DifferentiableAt ℝ φ (1, 0) := hφ.differentiableAt one_ne_zero
  have hRd := ((contDiffAt_logRule hβ hss hφ).differentiableAt one_ne_zero).hasFDerivAt
  have hΛd := ((contDiffAt_lamI hL hLss hU hUpos).differentiableAt one_ne_zero).hasFDerivAt
  have hR0 := LocalIFT.logRule_zero (β := β) hss
  set DR := fderiv ℝ (LocalIFT.logRule β φ) 0 with hDR
  set DL := fderiv ℝ (lamI β ibm Ybar L Uc) 0 with hDL
  let G := ℝ × ℝ × ((ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ) × ℝ)
  let X1 : G →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ _
  let X2 : G →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ _).comp (ContinuousLinearMap.snd ℝ ℝ _)
  let E3 : G →L[ℝ] (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ) × ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ _).comp (ContinuousLinearMap.snd ℝ ℝ _)
  let S : G →L[ℝ] ℝ × ℝ × ℝ := (ContinuousLinearMap.fst ℝ _ _).comp E3
  let S' : G →L[ℝ] ℝ × ℝ × ℝ :=
    (ContinuousLinearMap.fst ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp E3)
  let PI : G →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp E3)
  let Nu : (ℝ × ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ _
  let Yy : (ℝ × ℝ × ℝ) →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (ContinuousLinearMap.snd ℝ ℝ _)
  let Xx : (ℝ × ℝ × ℝ) →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    (ContinuousLinearMap.snd ℝ ℝ _)
  let A : G →L[ℝ] ℝ × ℝ := X1.prod (Nu.comp S)
  let A' : G →L[ℝ] ℝ × ℝ := X2.prod (Nu.comp S')
  have hRA : HasFDerivAt (LocalIFT.logRule β φ) DR (A 0) := by rw [map_zero]; exact hRd
  have hRA' : HasFDerivAt (LocalIFT.logRule β φ) DR (A' 0) := by rw [map_zero]; exact hRd
  have hJ := hRA.comp (0 : G) A.hasFDerivAt
  have hJ' := hRA'.comp (0 : G) A'.hasFDerivAt
  have hB := hJ.prodMk (((Yy.comp S).hasFDerivAt (x := 0)).prodMk ((Xx.comp S).hasFDerivAt))
  have hB' := hJ'.prodMk (((Yy.comp S').hasFDerivAt (x := 0)).prodMk ((Xx.comp S').hasFDerivAt))
  have hB0 : ((LocalIFT.logRule β φ ∘ A) 0, (Yy.comp S) 0, (Xx.comp S) 0) =
      (0 : ℝ × ℝ × ℝ) := by
    simp [hR0]
  have hB0' : ((LocalIFT.logRule β φ ∘ A') 0, (Yy.comp S') 0, (Xx.comp S') 0) =
      (0 : ℝ × ℝ × ℝ) := by
    simp [hR0]
  have hΛB : HasFDerivAt (lamI β ibm Ybar L Uc) DL
      ((LocalIFT.logRule β φ ∘ A) 0, (Yy.comp S) 0, (Xx.comp S) 0) := by rw [hB0]; exact hΛd
  have hΛB' : HasFDerivAt (lamI β ibm Ybar L Uc) DL
      ((LocalIFT.logRule β φ ∘ A') 0, (Yy.comp S') 0, (Xx.comp S') 0) := by rw [hB0']; exact hΛd
  have h := ((((hJ.sub (hΛB.comp (0 : G) hB)).add (hΛB'.comp (0 : G) hB')).add
    (X1.hasFDerivAt (x := 0))).sub (X2.hasFDerivAt (x := 0))).sub (PI.hasFDerivAt (x := 0))
  refine ⟨_, h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => ?_), ?_⟩
  · simp only [FW, Function.comp_apply, Pi.sub_apply, Pi.add_apply]
    rfl
  intro x x' ν y ξ ν' y' ξ' π
  simp only [add_apply, sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply]
  change DR (x, ν) - DL (DR (x, ν), y, ξ) + DL (DR (x', ν'), y', ξ') + x - x' - π = _
  rw [MoneyGrowth.clm3_apply DL (DR (x, ν)) y ξ, MoneyGrowth.clm3_apply DL (DR (x', ν')) y' ξ',
    hDR, fderiv_logRule_apply hβ hss hφd, fderiv_logRule_apply hβ hss hφd]
  ring

/-- Woodford (2003), (3.10), p. 113: `χ = m̄ u_cm/u_c` computed from `u_c(Y, m; ξ)` at the steady
state (`NonSeparable.chi`). -/
noncomputable def chiNS (Ybar mbar : ℝ) (Uc : ℝ × ℝ × ℝ → ℝ) : ℝ :=
  NonSeparable.chi mbar (Uc (Ybar, mbar, 0)) (fderiv ℝ Uc (Ybar, mbar, 0) (0, 1, 0))

/-- Woodford (2003), (3.6), p. 107: `η_i` computed from the money-demand function at the steady
state with `Δ̄ = 1 − β(1 + īᵐ)` (`MoneyGrowth.etaI`). -/
noncomputable def etaNS (β ibm mbar Ybar : ℝ) (L : ℝ × ℝ × ℝ → ℝ) : ℝ :=
  MoneyGrowth.etaI (fderiv ℝ L (Ybar, 1 - β * (1 + ibm), 0)) mbar (1 - β * (1 + ibm))

/-- Woodford (2003), (3.12), p. 114: `∂λ/∂ĵ = −χ η_i` at the steady state. -/
theorem lamI_j {β ibm Ybar mbar : ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ} (hm : 0 < mbar)
    (hL : DifferentiableAt ℝ L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : DifferentiableAt ℝ Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0)) :
    fderiv ℝ (lamI β ibm Ybar L Uc) 0 (1, 0, 0) =
      -(chiNS Ybar mbar Uc * etaNS β ibm mbar Ybar L) := by
  obtain ⟨D, hD, hDv⟩ := hasFDerivAt_lamI hL hLss hU hUpos
  rw [hD.fderiv]
  exact (lamI_coeffs hm hDv hUpos).1

/-- Woodford (2003), (A.32), p. 645: the slopes of the exact Wicksellian condition with
non-separable utility are `a = 1 + (1 + η_i χ) φ_p = A212` and `b = −(1 + η_i χ φ_p) = −B212`
(`NonSeparable.A212`, `B212`), and `c` is as in `hasFDerivAt_FW`. -/
theorem slopes_FW {β ibm Ybar mbar : ℝ} {φ : ℝ × ℝ → ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ}
    (hβ : 0 < β) (hm : 0 < mbar) (hss : 1 + φ (1, 0) = β⁻¹) (hφ : ContDiffAt ℝ 1 φ (1, 0))
    (hL : ContDiffAt ℝ 1 L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ 1 Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0)) :
    slopeA (FW β ibm Ybar φ L Uc) = NonSeparable.A212 (etaNS β ibm mbar Ybar L)
        (chiNS Ybar mbar Uc) (LocalIFT.elast β φ) ∧
      slopeB (FW β ibm Ybar φ L Uc) = -NonSeparable.B212 (etaNS β ibm mbar Ybar L)
        (chiNS Ybar mbar Uc) (LocalIFT.elast β φ) := by
  obtain ⟨F', hF', hv⟩ := hasFDerivAt_FW hβ hss hφ hL hLss hU hUpos
  obtain ⟨ha, hb, -⟩ := slopes_of_hasFDerivAt hF'
  have hj := lamI_j hm (hL.differentiableAt one_ne_zero) hLss (hU.differentiableAt one_ne_zero)
    hUpos
  refine ⟨?_, ?_⟩
  · rw [ha]
    change F' (1, 0, (((0 : ℝ), (0 : ℝ), (0 : ℝ)), ((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0 : ℝ))) = _
    rw [hv, hj, NonSeparable.A212]
    ring
  · rw [hb]
    change F' (0, 1, (((0 : ℝ), (0 : ℝ), (0 : ℝ)), ((0 : ℝ), (0 : ℝ), (0 : ℝ)), (0 : ℝ))) = _
    rw [hv, hj, NonSeparable.B212]
    ring

/-- Woodford (2003), Definition p. 105 with (1.21), (3.5), (1.30), perfect foresight: a
**Wicksellian equilibrium with non-separable utility** and interest on money fixed at `īᵐ`:
positive prices `P`, interest rates `i` and real balances `m` with `i_t = φ(P_t/P*_t; ν_t)`,
`m_t = L(Y_t, (i_t − īᵐ)/(1 + i_t); ξ_t)` and
`1 + i_t = u_c(Y_t, m_t; ξ_t)/(β u_c(Y_{t+1}, m_{t+1}; ξ_{t+1})) · P_{t+1}/P_t`. -/
def NSWEq (β ibm : ℝ) (φ : ℝ × ℝ → ℝ) (L Uc : ℝ × ℝ × ℝ → ℝ) (Y ξ ν Pstar P i m : ℕ → ℝ) :
    Prop :=
  (∀ t, 0 < P t) ∧ (∀ t, i t = φ (P t / Pstar t, ν t)) ∧
    (∀ t, m t = L (Y t, (i t - ibm) / (1 + i t), ξ t)) ∧
    ∀ t, 1 + i t = Uc (Y t, m t, ξ t) / (β * Uc (Y (t + 1), m (t + 1), ξ (t + 1))) *
      (P (t + 1) / P t)

/-- Woodford (2003), (1.30) and (3.5): at a date with `1 + i > 0`, the log rule and `lamI` evaluate
to `log(β(1 + i))` and `log u_c(Y, m; ξ)`. -/
theorem lamI_at {β ibm Ybar : ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β) (hYb : 0 < Ybar)
    {Y ξ i : ℝ} (hY : 0 < Y) (hi : 0 < 1 + i) :
    lamI β ibm Ybar L Uc (Real.log (β * (1 + i)), Real.log (Y / Ybar), ξ) =
      Real.log (Uc (Y, L (Y, (i - ibm) / (1 + i), ξ), ξ)) := by
  have e1 : Ybar * Real.exp (Real.log (Y / Ybar)) = Y := by
    rw [Real.exp_log (by positivity)]
    field_simp
  simp only [lamI]
  rw [e1, spread_of_j hβ hi]

/-- Woodford (2003), (1.30), p. 77: `ĵ(log(P/P*), ν) = log(β(1 + φ(P/P*; ν)))`. -/
theorem logRule_at {β : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β) {A ν : ℝ} (hA : 0 < A)
    (hpos : 0 < 1 + φ (A, ν)) :
    LocalIFT.logRule β φ (Real.log A, ν) = Real.log (β * (1 + φ (A, ν))) := by
  simp only [LocalIFT.logRule]
  rw [Real.exp_log hA, Real.log_mul hβ.ne' hpos.ne']
  ring

/-- Woodford (2003), (1.21), (3.5), (1.30), A.12 p. 645: one date of the Wicksellian equilibrium
with non-separable utility, in levels and as the period condition `FW = 0`. -/
theorem nsw_step {β ibm Ybar : ℝ} {φ : ℝ × ℝ → ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hYb : 0 < Ybar) {P0 P1 S0 S1 Y0 Y1 ν0 ν1 ξ0 ξ1 : ℝ} (hP0 : 0 < P0) (hP1 : 0 < P1)
    (hS0 : 0 < S0) (hS1 : 0 < S1) (hY0 : 0 < Y0) (hY1 : 0 < Y1)
    (hi0 : 0 < 1 + φ (P0 / S0, ν0)) (hi1 : 0 < 1 + φ (P1 / S1, ν1))
    (hU0 : 0 < Uc (Y0, L (Y0, (φ (P0 / S0, ν0) - ibm) / (1 + φ (P0 / S0, ν0)), ξ0), ξ0))
    (hU1 : 0 < Uc (Y1, L (Y1, (φ (P1 / S1, ν1) - ibm) / (1 + φ (P1 / S1, ν1)), ξ1), ξ1)) :
    1 + φ (P0 / S0, ν0) =
        Uc (Y0, L (Y0, (φ (P0 / S0, ν0) - ibm) / (1 + φ (P0 / S0, ν0)), ξ0), ξ0) /
          (β * Uc (Y1, L (Y1, (φ (P1 / S1, ν1) - ibm) / (1 + φ (P1 / S1, ν1)), ξ1), ξ1)) *
          (P1 / P0) ↔
      FW β ibm Ybar φ L Uc (Real.log (P0 / S0), Real.log (P1 / S1),
        ((ν0, Real.log (Y0 / Ybar), ξ0), (ν1, Real.log (Y1 / Ybar), ξ1),
          Real.log (S1 / S0))) = 0 := by
  set U0 := Uc (Y0, L (Y0, (φ (P0 / S0, ν0) - ibm) / (1 + φ (P0 / S0, ν0)), ξ0), ξ0) with hU0d
  set U1 := Uc (Y1, L (Y1, (φ (P1 / S1, ν1) - ibm) / (1 + φ (P1 / S1, ν1)), ξ1), ξ1) with hU1d
  have hj0 := logRule_at (β := β) hβ (div_pos hP0 hS0) hi0
  have hj1 := logRule_at (β := β) hβ (div_pos hP1 hS1) hi1
  have hl0 := lamI_at (ibm := ibm) (L := L) (Uc := Uc) (ξ := ξ0) hβ hYb hY0 hi0
  have hl1 := lamI_at (ibm := ibm) (L := L) (Uc := Uc) (ξ := ξ1) hβ hYb hY1 hi1
  simp only [FW]
  rw [hj0, hj1, hl0, hl1, ← hU0d, ← hU1d, Real.log_div hP0.ne' hS0.ne',
    Real.log_div hP1.ne' hS1.ne', Real.log_div hS1.ne' hS0.ne']
  have key : Real.log (β * (U0 / (β * U1) * (P1 / P0))) =
      Real.log U0 - Real.log U1 + Real.log P1 - Real.log P0 := by
    rw [show β * (U0 / (β * U1) * (P1 / P0)) = U0 / U1 * (P1 / P0) by field_simp,
      Real.log_mul (by positivity) (by positivity), Real.log_div hU0.ne' hU1.ne',
      Real.log_div hP1.ne' hP0.ne']
    ring
  constructor
  · intro h
    rw [h, key]
    ring
  · intro h
    have h' : Real.log (β * (1 + φ (P0 / S0, ν0))) = Real.log (β * (U0 / (β * U1) * (P1 / P0))) :=
      by rw [key]; linarith
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr (mul_pos hβ hi0))
      (Set.mem_Ioi.mpr (by positivity)) h'
    have hβ' := hβ.ne'
    field_simp at this ⊢
    linarith

/-- Woodford (2003), A.12, p. 645: near the steady state the gross interest rate and the marginal
utility of consumption are positive (so the log form of the equilibrium conditions is valid). -/
theorem nsw_pos_radius {β ibm Ybar mbar : ℝ} {φ : ℝ × ℝ → ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ}
    (hβ : 0 < β) (hss : 1 + φ (1, 0) = β⁻¹) (hφ : ContDiffAt ℝ 1 φ (1, 0))
    (hL : ContDiffAt ℝ 1 L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ 1 Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0)) :
    ∃ ρ > 0, ∀ x ν y ξ : ℝ, |x| < ρ → |ν| < ρ → |y| < ρ → |ξ| < ρ →
      0 < 1 + φ (Real.exp x, ν) ∧ 0 < Uc (Ybar * Real.exp y, L (Ybar * Real.exp y,
        1 - β * (1 + ibm) * Real.exp (-LocalIFT.logRule β φ (x, ν)), ξ), ξ) := by
  have hR0 := LocalIFT.logRule_zero (β := β) hss
  have hRc := (contDiffAt_logRule hβ hss hφ).continuousAt
  let g1 : ℝ × ℝ × ℝ × ℝ → ℝ := fun q => 1 + φ (Real.exp q.1, q.2.1)
  let g2 : ℝ × ℝ × ℝ × ℝ → ℝ := fun q => Uc (Ybar * Real.exp q.2.2.1, L (Ybar * Real.exp q.2.2.1,
    1 - β * (1 + ibm) * Real.exp (-LocalIFT.logRule β φ (q.1, q.2.1)), q.2.2.2), q.2.2.2)
  have hR0' : LocalIFT.logRule β φ (0, 0) = 0 := hR0
  have hc1 : ContinuousAt g1 0 :=
    continuousAt_const.add (hφ.continuousAt.comp_of_eq
      (f := fun q : ℝ × ℝ × ℝ × ℝ => ((Real.exp q.1, q.2.1) : ℝ × ℝ)) (by fun_prop) (by simp))
  have hRq : ContinuousAt (fun q : ℝ × ℝ × ℝ × ℝ => LocalIFT.logRule β φ (q.1, q.2.1)) 0 :=
    hRc.comp_of_eq (f := fun q : ℝ × ℝ × ℝ × ℝ => ((q.1, q.2.1) : ℝ × ℝ)) (by fun_prop)
      (by simp)
  have hin1 : ContinuousAt (fun q : ℝ × ℝ × ℝ × ℝ => ((Ybar * Real.exp q.2.2.1,
      1 - β * (1 + ibm) * Real.exp (-LocalIFT.logRule β φ (q.1, q.2.1)), q.2.2.2) :
      ℝ × ℝ × ℝ)) 0 :=
    (by fun_prop : ContinuousAt (fun q : ℝ × ℝ × ℝ × ℝ => Ybar * Real.exp q.2.2.1) 0).prodMk
      ((continuousAt_const.sub (continuousAt_const.mul hRq.neg.rexp)).prodMk (by fun_prop))
  have hLq : ContinuousAt (fun q : ℝ × ℝ × ℝ × ℝ => L ((Ybar * Real.exp q.2.2.1,
      1 - β * (1 + ibm) * Real.exp (-LocalIFT.logRule β φ (q.1, q.2.1)), q.2.2.2) :
      ℝ × ℝ × ℝ)) 0 :=
    hL.continuousAt.comp_of_eq hin1 (by simp [hR0'])
  have hin2 : ContinuousAt (fun q : ℝ × ℝ × ℝ × ℝ => ((Ybar * Real.exp q.2.2.1,
      L (Ybar * Real.exp q.2.2.1, 1 - β * (1 + ibm) * Real.exp (-LocalIFT.logRule β φ
        (q.1, q.2.1)), q.2.2.2), q.2.2.2) : ℝ × ℝ × ℝ)) 0 :=
    (by fun_prop : ContinuousAt (fun q : ℝ × ℝ × ℝ × ℝ => Ybar * Real.exp q.2.2.1) 0).prodMk
      (hLq.prodMk (by fun_prop))
  have hc2 : ContinuousAt g2 0 :=
    hU.continuousAt.comp_of_eq hin2 (by simp [hR0', hLss])
  have hp1 : 0 < g1 0 := by simp [g1, hss, hβ]
  have hp2 : 0 < g2 0 := by simpa [g2, hR0', hLss] using hUpos
  obtain ⟨ρ, hρ, hρP⟩ := Metric.eventually_nhds_iff.mp
    ((hc1.eventually (lt_mem_nhds hp1)).and (hc2.eventually (lt_mem_nhds hp2)))
  refine ⟨ρ, hρ, fun x ν y ξ hx hν hy hξ => ?_⟩
  have hd : dist ((x, ν, y, ξ) : ℝ × ℝ × ℝ × ℝ) 0 < ρ := by
    rw [dist_zero_right, Prod.norm_mk, Prod.norm_mk, Prod.norm_mk, Real.norm_eq_abs,
      Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_lt hx (max_lt hν (max_lt hy hξ))
  exact hρP hd

/-- Woodford (2003), A.12, p. 645: positivity of `1 + i` and `u_c` at a date where `P/P*`, `ν`,
`Y/Ȳ`, `ξ` are close to the steady state. -/
theorem nsw_pos_at {β ibm Ybar : ℝ} {φ : ℝ × ℝ → ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hYb : 0 < Ybar) {ρ : ℝ}
    (hpos : ∀ x ν y ξ : ℝ, |x| < ρ → |ν| < ρ → |y| < ρ → |ξ| < ρ →
      0 < 1 + φ (Real.exp x, ν) ∧ 0 < Uc (Ybar * Real.exp y, L (Ybar * Real.exp y,
        1 - β * (1 + ibm) * Real.exp (-LocalIFT.logRule β φ (x, ν)), ξ), ξ))
    {A Y ν ξ : ℝ} (hA : 0 < A) (hY : 0 < Y) (h1 : |Real.log A| < ρ) (h2 : |ν| < ρ)
    (h3 : |Real.log (Y / Ybar)| < ρ) (h4 : |ξ| < ρ) :
    0 < 1 + φ (A, ν) ∧ 0 < Uc (Y, L (Y, (φ (A, ν) - ibm) / (1 + φ (A, ν)), ξ), ξ) := by
  obtain ⟨p1, p2⟩ := hpos _ _ _ _ h1 h2 h3 h4
  rw [Real.exp_log hA] at p1
  have e1 : Ybar * Real.exp (Real.log (Y / Ybar)) = Y := by
    rw [Real.exp_log (by positivity)]
    field_simp
  rw [e1, logRule_at hβ hA p1, spread_of_j hβ p1] at p2
  exact ⟨p1, p2⟩

/-- Woodford (2003), A.12, p. 645: the disturbance vector `(s_t, s_{t+1}, π*_{t+1})` of the
Wicksellian model, `s = (ν, log(Y/Ȳ), ξ)`. -/
noncomputable def eWt (Ybar : ℝ) (Y ξ ν Pstar : ℕ → ℝ) (t : ℕ) :
    (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ) × ℝ :=
  ((ν t, Real.log (Y t / Ybar), ξ t), (ν (t + 1), Real.log (Y (t + 1) / Ybar), ξ (t + 1)),
    Real.log (Pstar (t + 1) / Pstar t))

/-- Woodford (2003), A.12, p. 645: the disturbance vector is bounded by the bound on its
primitive components. -/
theorem norm_eWt_le {Ybar d : ℝ} {Y ξ ν Pstar : ℕ → ℝ} (hY : ∀ t, |Real.log (Y t / Ybar)| ≤ d)
    (hξ : ∀ t, |ξ t| ≤ d) (hν : ∀ t, |ν t| ≤ d)
    (hP : ∀ t, |Real.log (Pstar (t + 1) / Pstar t)| ≤ d) (t : ℕ) :
    ‖eWt Ybar Y ξ ν Pstar t‖ ≤ d := by
  simp only [eWt]
  refine norm_prod_le_iff.mpr ⟨norm_triple_le (hν t) (hY t) (hξ t),
    norm_prod_le_iff.mpr ⟨norm_triple_le (hν (t + 1)) (hY (t + 1)) (hξ (t + 1)), ?_⟩⟩
  rw [Real.norm_eq_abs]
  exact hP t

/-- Woodford (2003), **Proposition 2.12**, p. 115 and A.12, pp. 645–646, **exact
perfect-foresight version**, under the exact (A.32) condition
`|1 + η_i χ φ_p| < |1 + (1 + η_i χ) φ_p|`: if `φ`, `L`, `u_c` are `C¹` near the steady state,
there are `ε, δ > 0` such that whenever `log(Y_t/Ȳ)`, `ξ_t`, `ν_t` and `π*_{t+1}` stay within `δ`,
there is an equilibrium with `|log(P_t/P*_t)| ≤ ε`, and any two such equilibria coincide (prices,
interest rates and real balances). -/
theorem nsw_local_determinacy {β ibm Ybar mbar : ℝ} {φ : ℝ × ℝ → ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ}
    (hβ : 0 < β) (hYb : 0 < Ybar) (hm : 0 < mbar) (hss : 1 + φ (1, 0) = β⁻¹)
    (hφ : ContDiffAt ℝ 1 φ (1, 0)) (hL : ContDiffAt ℝ 1 L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ 1 Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0))
    (hAB : |NonSeparable.B212 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc)
      (LocalIFT.elast β φ)| < |NonSeparable.A212 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc)
        (LocalIFT.elast β φ)|) :
    ∃ ε > 0, ∃ δ > 0, ∀ Y ξ ν Pstar : ℕ → ℝ, (∀ t, 0 < Y t) → (∀ t, 0 < Pstar t) →
      (∀ t, |Real.log (Y t / Ybar)| ≤ δ) → (∀ t, |ξ t| ≤ δ) → (∀ t, |ν t| ≤ δ) →
      (∀ t, |Real.log (Pstar (t + 1) / Pstar t)| ≤ δ) →
      (∃ P i m : ℕ → ℝ, NSWEq β ibm φ L Uc Y ξ ν Pstar P i m ∧
        ∀ t, |Real.log (P t / Pstar t)| ≤ ε) ∧
      ∀ P i m P' i' m' : ℕ → ℝ, NSWEq β ibm φ L Uc Y ξ ν Pstar P i m →
        NSWEq β ibm φ L Uc Y ξ ν Pstar P' i' m' →
        (∀ t, |Real.log (P t / Pstar t)| ≤ ε) → (∀ t, |Real.log (P' t / Pstar t)| ≤ ε) →
        P = P' ∧ i = i' ∧ m = m' := by
  obtain ⟨ρ, hρ, hpos⟩ := nsw_pos_radius hβ hss hφ hL hLss hU hUpos
  obtain ⟨ha, hb⟩ := slopes_FW hβ hm hss hφ hL hLss hU hUpos
  have hab : |slopeB (FW β ibm Ybar φ L Uc)| < |slopeA (FW β ibm Ybar φ L Uc)| := by
    rw [ha, hb, abs_neg]
    exact hAB
  obtain ⟨ε, hε, hεη, δ, hδ, hδη, X, -, -, hX⟩ :=
    local_determinacy_loc (contDiffAt_FW hβ hss hφ hL hLss hU hUpos) (FW_zero hss) hab
      (half_pos hρ)
  refine ⟨ε / 2, half_pos hε, δ / 2, half_pos hδ,
    fun Y ξ ν Pstar hY hPs hYd hξd hνd hPd => ?_⟩
  have hK := norm_eWt_le hYd hξd hνd hPd
  set e : Seq ((ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ) × ℝ) := mkS (eWt Ybar Y ξ ν Pstar) ⟨δ / 2, hK⟩ with he
  have hen : ‖e‖ < δ := lt_of_le_of_lt (norm_seq_le (by positivity) hK) (half_lt_self hδ)
  obtain ⟨hXn, hXs, -, huniq⟩ := hX e hen
  have hsmall : ∀ t, |ν t| < ρ ∧ |Real.log (Y t / Ybar)| < ρ ∧ |ξ t| < ρ := fun t =>
    ⟨by linarith [hνd t], by linarith [hYd t], by linarith [hξd t]⟩
  have hposA : ∀ A : ℝ, ∀ t, 0 < A → |Real.log A| < ρ →
      0 < 1 + φ (A, ν t) ∧ 0 < Uc (Y t, L (Y t, (φ (A, ν t) - ibm) / (1 + φ (A, ν t)), ξ t), ξ t) :=
    fun A t hA hAl => nsw_pos_at hβ hYb hpos hA (hY t) hAl (hsmall t).1 (hsmall t).2.1
      (hsmall t).2.2
  have hstep : ∀ P i m : ℕ → ℝ, NSWEq β ibm φ L Uc Y ξ ν Pstar P i m →
      (∀ t, |Real.log (P t / Pstar t)| ≤ ε / 2) → ∀ t,
      FW β ibm Ybar φ L Uc (Real.log (P t / Pstar t), Real.log (P (t + 1) / Pstar (t + 1)),
        e t) = 0 := by
    rintro P i m ⟨hP, hi, hmm, hF⟩ hb t
    have hA0 := hposA _ t (div_pos (hP t) (hPs t)) (by linarith [hb t])
    have hA1 := hposA _ (t + 1) (div_pos (hP (t + 1)) (hPs (t + 1))) (by linarith [hb (t + 1)])
    have h := hF t
    rw [hmm t, hmm (t + 1), hi t, hi (t + 1)] at h
    exact (nsw_step hβ hYb (hP t) (hP (t + 1)) (hPs t) (hPs (t + 1)) (hY t) (hY (t + 1))
      hA0.1 hA1.1 hA0.2 hA1.2).mp h
  have hclass : ∀ P i m : ℕ → ℝ, NSWEq β ibm φ L Uc Y ξ ν Pstar P i m →
      ∀ hb : (∀ t, |Real.log (P t / Pstar t)| ≤ ε / 2),
      mk (fun t => Real.log (P t / Pstar t)) ⟨ε / 2, hb⟩ = X e := fun P i m hE hb =>
    huniq _ (lt_of_le_of_lt (norm_le_of_abs_le (by positivity) hb) (half_lt_self hε))
      (fun t => hstep P i m hE hb t)
  refine ⟨?_, ?_⟩
  · set x := X e with hx
    have hxt : ∀ t, |x t| < ε / 2 := fun t => lt_of_le_of_lt (abs_apply_le x t) hXn
    have hPd : ∀ t, Pstar t * Real.exp (x t) / Pstar t = Real.exp (x t) := fun t =>
      mul_div_cancel_left₀ _ (hPs t).ne'
    have hp : ∀ t, Real.log (Pstar t * Real.exp (x t) / Pstar t) = x t := fun t => by
      rw [hPd, Real.log_exp]
    have hA : ∀ t, 0 < 1 + φ (Pstar t * Real.exp (x t) / Pstar t, ν t) ∧
        0 < Uc (Y t, L (Y t, (φ (Pstar t * Real.exp (x t) / Pstar t, ν t) - ibm) /
          (1 + φ (Pstar t * Real.exp (x t) / Pstar t, ν t)), ξ t), ξ t) := fun t =>
      hposA _ t (by have := hPs t; positivity) (by rw [hp]; linarith [hxt t, hεη])
    refine ⟨fun t => Pstar t * Real.exp (x t),
      fun t => φ (Pstar t * Real.exp (x t) / Pstar t, ν t),
      fun t => L (Y t, (φ (Pstar t * Real.exp (x t) / Pstar t, ν t) - ibm) /
        (1 + φ (Pstar t * Real.exp (x t) / Pstar t, ν t)), ξ t),
      ⟨fun t => by have := hPs t; positivity, fun t => rfl, fun t => rfl, fun t => ?_⟩,
      fun t => by rw [hp]; exact (hxt t).le⟩
    refine (nsw_step hβ hYb (by have := hPs t; positivity) (by have := hPs (t + 1); positivity)
      (hPs t) (hPs (t + 1)) (hY t) (hY (t + 1)) (hA t).1 (hA (t + 1)).1 (hA t).2
      (hA (t + 1)).2).mpr ?_
    rw [hp t, hp (t + 1)]
    exact hXs t
  · intro P i m P' i' m' hE hE' hb hb'
    have hb2 : ∀ t, |Real.log (P t / Pstar t)| ≤ ε / 2 := hb
    have hb2' : ∀ t, |Real.log (P' t / Pstar t)| ≤ ε / 2 := hb'
    have hlog : ∀ t, Real.log (P t / Pstar t) = Real.log (P' t / Pstar t) := fun t =>
      congrArg (fun y : Linf => y t) ((hclass P i m hE hb2).trans (hclass P' i' m' hE' hb2').symm)
    have hPP : P = P' := funext fun t => by
      have h := Real.log_injOn_pos (Set.mem_Ioi.mpr (div_pos (hE.1 t) (hPs t)))
        (Set.mem_Ioi.mpr (div_pos (hE'.1 t) (hPs t))) (hlog t)
      exact (div_left_inj' (hPs t).ne').mp h
    have hii : i = i' := funext fun t => by rw [hE.2.1 t, hE'.2.1 t, hPP]
    exact ⟨hPP, hii, funext fun t => by rw [hE.2.2.1 t, hE'.2.2.1 t, hii]⟩

/-- Woodford (2003), **Proposition 2.12**, p. 115 (book form): under (3.16) `χ > −1/(2η_i)` with
`η_i > 0`, the exact Wicksellian model with non-separable utility is locally determinate for
every `φ_p > 0` (via `NonSeparable.abs_B_lt_A`). -/
theorem prop_2_12_exact {β ibm Ybar mbar : ℝ} {φ : ℝ × ℝ → ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ}
    (hβ : 0 < β) (hYb : 0 < Ybar) (hm : 0 < mbar) (hss : 1 + φ (1, 0) = β⁻¹)
    (hφ : ContDiffAt ℝ 1 φ (1, 0)) (hL : ContDiffAt ℝ 1 L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ 1 Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0))
    (hηi : 0 < etaNS β ibm mbar Ybar L)
    (h316 : -1 / (2 * etaNS β ibm mbar Ybar L) < chiNS Ybar mbar Uc)
    (hφp : 0 < LocalIFT.elast β φ) :
    ∃ ε > 0, ∃ δ > 0, ∀ Y ξ ν Pstar : ℕ → ℝ, (∀ t, 0 < Y t) → (∀ t, 0 < Pstar t) →
      (∀ t, |Real.log (Y t / Ybar)| ≤ δ) → (∀ t, |ξ t| ≤ δ) → (∀ t, |ν t| ≤ δ) →
      (∀ t, |Real.log (Pstar (t + 1) / Pstar t)| ≤ δ) →
      (∃ P i m : ℕ → ℝ, NSWEq β ibm φ L Uc Y ξ ν Pstar P i m ∧
        ∀ t, |Real.log (P t / Pstar t)| ≤ ε) ∧
      ∀ P i m P' i' m' : ℕ → ℝ, NSWEq β ibm φ L Uc Y ξ ν Pstar P i m →
        NSWEq β ibm φ L Uc Y ξ ν Pstar P' i' m' →
        (∀ t, |Real.log (P t / Pstar t)| ≤ ε) → (∀ t, |Real.log (P' t / Pstar t)| ≤ ε) →
        P = P' ∧ i = i' ∧ m = m' :=
  nsw_local_determinacy hβ hYb hm hss hφ hL hLss hU hUpos
    (NonSeparable.abs_B_lt_A hηi h316 hφp)

/-- Woodford (2003), Prop. 2.12 and fn. 55, p. 121 (indeterminacy when the (A.32) condition
fails strictly), **exact perfect-foresight version**: if
`|1 + (1 + η_i χ) φ_p| < |1 + η_i χ φ_p|`, then with constant fundamentals (`Y ≡ Ȳ`, `ξ ≡ 0`,
`ν ≡ 0`, `P* ≡ 1`) every initial `log P_0 = c` with `|c| ≤ r` starts an exact equilibrium within
`ε` of the steady state; distinct `c` give distinct equilibria. -/
theorem nsw_local_indeterminacy {β ibm Ybar mbar : ℝ} {φ : ℝ × ℝ → ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ}
    (hβ : 0 < β) (hYb : 0 < Ybar) (hm : 0 < mbar) (hss : 1 + φ (1, 0) = β⁻¹)
    (hφ : ContDiffAt ℝ 1 φ (1, 0)) (hL : ContDiffAt ℝ 1 L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ 1 Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0))
    (hBA : |NonSeparable.A212 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc)
      (LocalIFT.elast β φ)| < |NonSeparable.B212 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc)
        (LocalIFT.elast β φ)|) :
    ∀ ε > 0, ∃ r > 0, ∀ c : ℝ, |c| ≤ r → ∃ P i m : ℕ → ℝ,
      NSWEq β ibm φ L Uc (fun _ => Ybar) (fun _ => 0) (fun _ => 0) (fun _ => 1) P i m ∧
        Real.log (P 0) = c ∧ ∀ t, |Real.log (P t)| ≤ ε := by
  intro ε hε
  obtain ⟨ρ, hρ, hpos⟩ := nsw_pos_radius hβ hss hφ hL hLss hU hUpos
  obtain ⟨ha, hb⟩ := slopes_FW hβ hm hss hφ hL hLss hU hUpos
  have hab : |slopeA (FW β ibm Ybar φ L Uc)| < |slopeB (FW β ibm Ybar φ L Uc)| := by
    rw [ha, hb, abs_neg]
    exact hBA
  set ε' := min ε (ρ / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (half_pos hρ)
  obtain ⟨r, hr, hx⟩ := local_indeterminacy_loc (contDiffAt_FW hβ hss hφ hL hLss hU hUpos)
    (FW_zero hss) hab ε' hε'0
  refine ⟨r, hr, fun c hc => ?_⟩
  obtain ⟨x, hxs, hxn, hx0⟩ := hx c hc
  have hxt : ∀ t, |x t| ≤ ε' := fun t => (abs_apply_le x t).trans hxn
  have hl1 : Real.log (Ybar / Ybar) = 0 := by rw [div_self hYb.ne', Real.log_one]
  have hA : ∀ t, 0 < 1 + φ (Real.exp (x t) / 1, 0) ∧
      0 < Uc (Ybar, L (Ybar, (φ (Real.exp (x t) / 1, 0) - ibm) / (1 + φ (Real.exp (x t) / 1, 0)),
        0), 0) := fun t =>
    nsw_pos_at hβ hYb hpos (by positivity) hYb
      (by rw [div_one, Real.log_exp]; linarith [hxt t, min_le_right ε (ρ / 2)])
      (by rw [abs_zero]; exact hρ) (by rw [hl1, abs_zero]; exact hρ) (by rw [abs_zero]; exact hρ)
  refine ⟨fun t => Real.exp (x t), fun t => φ (Real.exp (x t) / 1, 0),
    fun t => L (Ybar, (φ (Real.exp (x t) / 1, 0) - ibm) / (1 + φ (Real.exp (x t) / 1, 0)), 0),
    ⟨fun t => Real.exp_pos _, fun t => rfl, fun t => rfl, fun t => ?_⟩,
    by rw [Real.log_exp, hx0], fun t => ?_⟩
  · refine (nsw_step (S0 := 1) (S1 := 1) hβ hYb (Real.exp_pos _) (Real.exp_pos _) one_pos one_pos
      hYb hYb (hA t).1 (hA (t + 1)).1 (hA t).2 (hA (t + 1)).2).mpr ?_
    have h := hxs t
    simp only [div_one, Real.log_exp, hl1, Real.log_one]
    convert h using 2
    simp only [lp.coeFn_zero, Pi.zero_apply, Prod.mk_zero_zero]
  · rw [Real.log_exp]
    exact (hxt t).trans (min_le_left _ _)

/-- Woodford (2003), A.12, p. 645: near the steady state every Wicksellian equilibrium with
non-separable utility solves the period condition `FW` date by date. -/
theorem nsw_solves {β ibm Ybar ρ : ℝ} {φ : ℝ × ℝ → ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hYb : 0 < Ybar)
    (hpos : ∀ x ν y ξ : ℝ, |x| < ρ → |ν| < ρ → |y| < ρ → |ξ| < ρ →
      0 < 1 + φ (Real.exp x, ν) ∧ 0 < Uc (Ybar * Real.exp y, L (Ybar * Real.exp y,
        1 - β * (1 + ibm) * Real.exp (-LocalIFT.logRule β φ (x, ν)), ξ), ξ))
    {Y ξ ν Pstar P i m : ℕ → ℝ} (hY : ∀ t, 0 < Y t) (hPs : ∀ t, 0 < Pstar t)
    (hE : NSWEq β ibm φ L Uc Y ξ ν Pstar P i m)
    (hb : ∀ t, |Real.log (P t / Pstar t)| < ρ ∧ |ν t| < ρ ∧ |Real.log (Y t / Ybar)| < ρ ∧
      |ξ t| < ρ) (t : ℕ) :
    FW β ibm Ybar φ L Uc (Real.log (P t / Pstar t), Real.log (P (t + 1) / Pstar (t + 1)),
      eWt Ybar Y ξ ν Pstar t) = 0 := by
  obtain ⟨hP, hi, hmm, hF⟩ := hE
  have hA0 := nsw_pos_at hβ hYb hpos (div_pos (hP t) (hPs t)) (hY t) (hb t).1 (hb t).2.1
    (hb t).2.2.1 (hb t).2.2.2
  have hA1 := nsw_pos_at hβ hYb hpos (div_pos (hP (t + 1)) (hPs (t + 1))) (hY (t + 1))
    (hb (t + 1)).1 (hb (t + 1)).2.1 (hb (t + 1)).2.2.1 (hb (t + 1)).2.2.2
  have h := hF t
  rw [hmm t, hmm (t + 1), hi t, hi (t + 1)] at h
  exact (nsw_step hβ hYb (hP t) (hP (t + 1)) (hPs t) (hPs (t + 1)) (hY t) (hY (t + 1))
    hA0.1 hA1.1 hA0.2 hA1.2).mp h

/-- Woodford (2003), Prop. 2.12, p. 115 and App. A.3, p. 633 (`C¹` dependence): in sequence space
the exact Wicksellian equilibrium with non-separable utility, `p = X(e)`, is `C¹` in the
disturbances near zero, with `X(0) = 0` and derivative the log-linear solution (3.17). -/
theorem nsw_smooth_dependence {β ibm Ybar mbar : ℝ} {φ : ℝ × ℝ → ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ}
    (hβ : 0 < β) (hm : 0 < mbar) (hss : 1 + φ (1, 0) = β⁻¹)
    (hφ : ContDiffAt ℝ 1 φ (1, 0)) (hL : ContDiffAt ℝ 1 L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ 1 Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0))
    (hAB : |NonSeparable.B212 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc)
      (LocalIFT.elast β φ)| < |NonSeparable.A212 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc)
        (LocalIFT.elast β φ)|) :
    ∃ δ > 0, ∃ X : Seq ((ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ) × ℝ) → Linf, X 0 = 0 ∧
      HasFDerivAt X (linSol3 (FW β ibm Ybar φ L Uc)) 0 ∧
      ∀ e, ‖e‖ < δ → Solves (FW β ibm Ybar φ L Uc) e (X e) ∧ ContDiffAt ℝ 1 X e := by
  obtain ⟨ha, hb⟩ := slopes_FW hβ hm hss hφ hL hLss hU hUpos
  have hab : |slopeB (FW β ibm Ybar φ L Uc)| < |slopeA (FW β ibm Ybar φ L Uc)| := by
    rw [ha, hb, abs_neg]
    exact hAB
  obtain ⟨ε, hε, -, δ, hδ, -, X, hX0, hXd, hX⟩ :=
    local_determinacy_loc (contDiffAt_FW hβ hss hφ hL hLss hU hUpos) (FW_zero hss) hab one_pos
  exact ⟨δ, hδ, X, hX0, hXd, fun e he => ⟨(hX e he).2.1, (hX e he).2.2.1⟩⟩

/-- Woodford (2003), (3.17)–(3.19), p. 116 and (A.32), p. 645, **the first-order term of the exact
Wicksellian equilibrium**: with `A = A212`, `B = B212`,
`p̂_t = ∑_k Bᵏ/A^{k+1} [π*_{t+k+1} + Λ_y (ŷ_{t+k} − ŷ_{t+k+1}) + Λ_ξ (ξ_{t+k} − ξ_{t+k+1})
 − c_ν((1 + η_i χ) ν_{t+k} − η_i χ ν_{t+k+1})]` (the `r̃` terms of (3.12) are the `Λ` terms). -/
theorem linSol3_FW_apply {β ibm Ybar mbar : ℝ} {φ : ℝ × ℝ → ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ}
    (hβ : 0 < β) (hm : 0 < mbar) (hss : 1 + φ (1, 0) = β⁻¹)
    (hφ : ContDiffAt ℝ 1 φ (1, 0)) (hL : ContDiffAt ℝ 1 L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ 1 Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0))
    (hAB : |NonSeparable.B212 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc)
      (LocalIFT.elast β φ)| < |NonSeparable.A212 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc)
        (LocalIFT.elast β φ)|) (e : Seq ((ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ) × ℝ)) (t : ℕ) :
    linSol3 (FW β ibm Ybar φ L Uc) e t = ∑' k,
      (NonSeparable.B212 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc) (LocalIFT.elast β φ) /
        NonSeparable.A212 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc) (LocalIFT.elast β φ))
          ^ k / NonSeparable.A212 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc)
            (LocalIFT.elast β φ) *
        ((e (t + k)).2.2 + fderiv ℝ (lamI β ibm Ybar L Uc) 0 (0, 1, 0) *
          ((e (t + k)).1.2.1 - (e (t + k)).2.1.2.1) +
          fderiv ℝ (lamI β ibm Ybar L Uc) 0 (0, 0, 1) * ((e (t + k)).1.2.2 - (e (t + k)).2.1.2.2) -
          LocalIFT.elastNu β φ * ((1 + etaNS β ibm mbar Ybar L * chiNS Ybar mbar Uc) *
            (e (t + k)).1.1 - etaNS β ibm mbar Ybar L * chiNS Ybar mbar Uc *
              (e (t + k)).2.1.1)) := by
  obtain ⟨ha, hb⟩ := slopes_FW hβ hm hss hφ hL hLss hU hUpos
  have hab : |slopeB (FW β ibm Ybar φ L Uc)| < |slopeA (FW β ibm Ybar φ L Uc)| := by
    rw [ha, hb, abs_neg]
    exact hAB
  obtain ⟨F', hF', hv⟩ := hasFDerivAt_FW hβ hss hφ hL hLss hU hUpos
  obtain ⟨-, -, hc⟩ := slopes_of_hasFDerivAt hF'
  have hj := lamI_j hm (hL.differentiableAt one_ne_zero) hLss (hU.differentiableAt one_ne_zero)
    hUpos
  rw [linSol3_apply hab, ← neg_mul, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hv' : e (t + k) = (((e (t + k)).1.1, (e (t + k)).1.2.1, (e (t + k)).1.2.2),
      ((e (t + k)).2.1.1, (e (t + k)).2.1.2.1, (e (t + k)).2.1.2.2), (e (t + k)).2.2) := rfl
  rw [hc, hv', hv, ha, hb, hj]
  simp only [NonSeparable.A212]
  have hA0 : NonSeparable.A212 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc)
      (LocalIFT.elast β φ) ≠ 0 := ne_zero_of_abs_lt hAB
  simp only [NonSeparable.A212] at hA0
  simp only [NonSeparable.B212]
  field_simp
  ring

/-- Woodford (2003), **Proposition 2.12**, p. 116 ("a log-linear approximation to the locally
unique equilibrium price process is given by (3.17)"), exact perfect-foresight version with the
`C²` hypothesis of E18: every equilibrium near the steady state satisfies
`|log(P_t/P*_t) − p̂_t| ≤ C ξ²` (`p̂` as in `linSol3_FW_apply`) when all primitive
disturbances are bounded by `ξ < δ`. -/
theorem nsw_second_order {β ibm Ybar mbar : ℝ} {φ : ℝ × ℝ → ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ}
    (hβ : 0 < β) (hYb : 0 < Ybar) (hm : 0 < mbar) (hss : 1 + φ (1, 0) = β⁻¹)
    (hφ : ContDiffAt ℝ 2 φ (1, 0)) (hL : ContDiffAt ℝ 2 L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ 2 Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0))
    (hAB : |NonSeparable.B212 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc)
      (LocalIFT.elast β φ)| < |NonSeparable.A212 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc)
        (LocalIFT.elast β φ)|) :
    ∃ ε > 0, ∃ δ > 0, ∃ C : ℝ, ∀ Y ξ ν Pstar : ℕ → ℝ, ∀ ξb : ℝ, (∀ t, 0 < Y t) →
      (∀ t, 0 < Pstar t) → ξb < δ → (∀ t, |Real.log (Y t / Ybar)| ≤ ξb) →
      (∀ t, |ξ t| ≤ ξb) → (∀ t, |ν t| ≤ ξb) →
      (∀ t, |Real.log (Pstar (t + 1) / Pstar t)| ≤ ξb) →
      ∀ P i m : ℕ → ℝ, NSWEq β ibm φ L Uc Y ξ ν Pstar P i m →
      (∀ t, |Real.log (P t / Pstar t)| ≤ ε) → ∀ t,
      |Real.log (P t / Pstar t) - ∑' k,
        (NonSeparable.B212 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc) (LocalIFT.elast β φ) /
          NonSeparable.A212 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc) (LocalIFT.elast β φ))
            ^ k / NonSeparable.A212 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc)
              (LocalIFT.elast β φ) *
          (Real.log (Pstar (t + k + 1) / Pstar (t + k)) +
            fderiv ℝ (lamI β ibm Ybar L Uc) 0 (0, 1, 0) *
              (Real.log (Y (t + k) / Ybar) - Real.log (Y (t + k + 1) / Ybar)) +
            fderiv ℝ (lamI β ibm Ybar L Uc) 0 (0, 0, 1) * (ξ (t + k) - ξ (t + k + 1)) -
            LocalIFT.elastNu β φ * ((1 + etaNS β ibm mbar Ybar L * chiNS Ybar mbar Uc) *
              ν (t + k) - etaNS β ibm mbar Ybar L * chiNS Ybar mbar Uc * ν (t + k + 1)))| ≤
        C * ξb ^ 2 := by
  have hφ1 : ContDiffAt ℝ 1 φ (1, 0) := hφ.of_le (by norm_num)
  have hL1 : ContDiffAt ℝ 1 L (Ybar, 1 - β * (1 + ibm), 0) := hL.of_le (by norm_num)
  have hU1 : ContDiffAt ℝ 1 Uc (Ybar, mbar, 0) := hU.of_le (by norm_num)
  obtain ⟨ρ, hρ, hpos⟩ := nsw_pos_radius hβ hss hφ1 hL1 hLss hU1 hUpos
  obtain ⟨ha, hb⟩ := slopes_FW hβ hm hss hφ1 hL1 hLss hU1 hUpos
  have hab : |slopeB (FW β ibm Ybar φ L Uc)| < |slopeA (FW β ibm Ybar φ L Uc)| := by
    rw [ha, hb, abs_neg]
    exact hAB
  obtain ⟨ε, hε, hεη, δ, hδ, hδη, C, hC⟩ :=
    second_order_loc (contDiffAt_FW hβ hss hφ hL hLss hU hUpos) (FW_zero hss) hab (half_pos hρ)
  refine ⟨ε / 2, half_pos hε, δ, hδ, max C 0,
    fun Y ξ ν Pstar ξb hY hPs hξb hYd hξd hνd hPd P i m hE hbd t => ?_⟩
  have hξ0 : 0 ≤ ξb := (abs_nonneg _).trans (hξd 0)
  have hK := norm_eWt_le hYd hξd hνd hPd
  set e : Seq ((ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ) × ℝ) := mkS (eWt Ybar Y ξ ν Pstar) ⟨ξb, hK⟩ with he
  have hen : ‖e‖ ≤ ξb := norm_seq_le hξ0 hK
  have hsol : Solves (FW β ibm Ybar φ L Uc) e
      (mk (fun t => Real.log (P t / Pstar t)) ⟨ε / 2, hbd⟩) := fun s =>
    nsw_solves hβ hYb hpos hY hPs hE (fun t => ⟨by linarith [hbd t], by linarith [hνd t],
      by linarith [hYd t], by linarith [hξd t]⟩) s
  have hbound := hC e (lt_of_le_of_lt hen hξb) _
    (lt_of_le_of_lt (norm_le_of_abs_le (by positivity) hbd) (half_lt_self hε)) hsol
  have hcoord := abs_apply_le (mk (fun t => Real.log (P t / Pstar t)) ⟨ε / 2, hbd⟩ -
    linSol3 (FW β ibm Ybar φ L Uc) e) t
  simp only [lp.coeFn_sub, Pi.sub_apply, mk_apply] at hcoord
  rw [linSol3_FW_apply hβ hm hss hφ1 hL1 hLss hU1 hUpos hAB] at hcoord
  simp only [he, mkS_apply, eWt] at hcoord
  refine hcoord.trans (hbound.trans ?_)
  calc C * ‖e‖ ^ 2 ≤ max C 0 * ‖e‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    _ ≤ max C 0 * ξb ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hen 2) (le_max_right _ _)

/-! ### Proposition 2.13: inertial rule with non-separable utility (pp. 116–117, A.13)

Exact perfect-foresight model: (1.21) with `u_c(Y_t, m_t; ξ_t)`, money demand (3.5) with
`iᵐ = īᵐ`, and the nonlinear inertial rule `ĵ_t = ψ(π_t, ĵ_{t−1}, ν_t)`. With
`λ = lamI` and `π_{t+1} = Θ(ĵ_{t+1}, ĵ_t, ν_{t+1})` it is the scalar forward equation
`ĵ_t − λ(ĵ_t, ŷ_t, ξ_t) + λ(ĵ_{t+1}, ŷ_{t+1}, ξ_{t+1}) − Θ(ĵ_{t+1}, ĵ_t, ν_{t+1}) = 0`, the
nonlinear form of (A.33), p. 646. -/

/-- Woodford (2003), A.13, p. 646: `(x, x', ((y, ξ), (y', ξ'), ν)) ↦ (x', x, ν)`. -/
noncomputable def lagMap13 : ℝ × ℝ × ((ℝ × ℝ) × (ℝ × ℝ) × ℝ) →L[ℝ] ℝ × ℝ × ℝ :=
  ((ContinuousLinearMap.fst ℝ ℝ _).comp (ContinuousLinearMap.snd ℝ ℝ _)).prod
    ((ContinuousLinearMap.fst ℝ ℝ _).prod ((ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp
      ((ContinuousLinearMap.snd ℝ (ℝ × ℝ) _).comp ((ContinuousLinearMap.snd ℝ ℝ _).comp
        (ContinuousLinearMap.snd ℝ ℝ _)))))

/-- Woodford (2003), A.13, p. 646: `(x, x', ((y, ξ), …)) ↦ (x, y, ξ)`. -/
noncomputable def curMap13 : ℝ × ℝ × ((ℝ × ℝ) × (ℝ × ℝ) × ℝ) →L[ℝ] ℝ × ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ _).prod ((ContinuousLinearMap.fst ℝ (ℝ × ℝ) _).comp
    ((ContinuousLinearMap.snd ℝ ℝ _).comp (ContinuousLinearMap.snd ℝ ℝ _)))

/-- Woodford (2003), A.13, p. 646: `(x, x', (…, (y', ξ'), ν)) ↦ (x', y', ξ')`. -/
noncomputable def nextMap13 : ℝ × ℝ × ((ℝ × ℝ) × (ℝ × ℝ) × ℝ) →L[ℝ] ℝ × ℝ × ℝ :=
  ((ContinuousLinearMap.fst ℝ ℝ _).comp (ContinuousLinearMap.snd ℝ ℝ _)).prod
    ((ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).comp ((ContinuousLinearMap.snd ℝ (ℝ × ℝ) _).comp
      ((ContinuousLinearMap.snd ℝ ℝ _).comp (ContinuousLinearMap.snd ℝ ℝ _))))

/-- Woodford (2003), A.13, p. 646, exact form: the period condition of the inertial-rule model
with non-separable utility in `(ĵ_t, ĵ_{t+1}, ((ŷ_t, ξ_t), (ŷ_{t+1}, ξ_{t+1}), ν_{t+1}))`. -/
noncomputable def F13 (β ibm Ybar : ℝ) (L Uc : ℝ × ℝ × ℝ → ℝ) (ψ : ℝ × ℝ × ℝ → ℝ)
    (hψ : ContDiffAt ℝ 1 ψ 0) (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0)
    (p : ℝ × ℝ × ((ℝ × ℝ) × (ℝ × ℝ) × ℝ)) : ℝ :=
  p.1 - lamI β ibm Ybar L Uc (curMap13 p) + lamI β ibm Ybar L Uc (nextMap13 p) -
    solveRule ψ hψ hφ (lagMap13 p)

/-- Woodford (2003), A.13, p. 646: the steady state solves the period condition. -/
theorem F13_zero {β ibm Ybar : ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ} {ψ : ℝ × ℝ × ℝ → ℝ}
    (hψ : ContDiffAt ℝ 1 ψ 0) (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) (h0 : ψ 0 = 0) :
    F13 β ibm Ybar L Uc ψ hψ hφ 0 = 0 := by
  simp only [F13, map_zero, solveRule_zero hψ hφ h0, Prod.fst_zero]
  ring

/-- Woodford (2003), A.13, p. 646: the period condition is `Cⁿ` near the steady state. -/
theorem contDiffAt_F13 {β ibm Ybar mbar : ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ} {ψ : ℝ × ℝ × ℝ → ℝ}
    (hψ : ContDiffAt ℝ 1 ψ 0) (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) (h0 : ψ 0 = 0) {n : ℕ}
    (hψn : ContDiffAt ℝ n ψ 0) (hL : ContDiffAt ℝ n L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ n Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0)) :
    ContDiffAt ℝ n (F13 β ibm Ybar L Uc ψ hψ hφ) 0 := by
  have hΛ := contDiffAt_lamI hL hLss hU hUpos
  have hΛc : ContDiffAt ℝ n (lamI β ibm Ybar L Uc) (curMap13 0) := by rw [map_zero]; exact hΛ
  have hΛn : ContDiffAt ℝ n (lamI β ibm Ybar L Uc) (nextMap13 0) := by rw [map_zero]; exact hΛ
  have hΘ : ContDiffAt ℝ n (solveRule ψ hψ hφ) (lagMap13 0) := by
    rw [map_zero]
    exact contDiffAt_solveRule hψ hφ h0 hψn
  have h1 : ContDiffAt ℝ n (fun p : ℝ × ℝ × ((ℝ × ℝ) × (ℝ × ℝ) × ℝ) => p.1) 0 := by fun_prop
  exact ((h1.sub (hΛc.comp 0 curMap13.contDiff.contDiffAt)).add
    (hΛn.comp 0 nextMap13.contDiff.contDiffAt)).sub (hΘ.comp 0 lagMap13.contDiff.contDiffAt)

/-- Woodford (2003), (A.33), p. 646, **exact derivative**: with `Λ = Dλ(0)`,
`DF(x, x', ((y, ξ), (y', ξ'), ν)) = x − Λ(x, y, ξ) + Λ(x', y', ξ') − φ_π⁻¹(x' − ρ x − c ν)`. -/
theorem hasFDerivAt_F13 {β ibm Ybar mbar : ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ} {ψ : ℝ × ℝ × ℝ → ℝ}
    (hψ : ContDiffAt ℝ 1 ψ 0) (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) (h0 : ψ 0 = 0)
    (hL : ContDiffAt ℝ 1 L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ 1 Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0)) :
    ∃ F' : ℝ × ℝ × ((ℝ × ℝ) × (ℝ × ℝ) × ℝ) →L[ℝ] ℝ,
      HasFDerivAt (F13 β ibm Ybar L Uc ψ hψ hφ) F' 0 ∧
      ∀ x x' y ξ y' ξ' ν : ℝ, F' (x, x', ((y, ξ), (y', ξ'), ν)) =
        x - fderiv ℝ (lamI β ibm Ybar L Uc) 0 (x, y, ξ) +
          fderiv ℝ (lamI β ibm Ybar L Uc) 0 (x', y', ξ') -
          (phiPi ψ)⁻¹ * (x' - rhoR ψ * x - nuR ψ * ν) := by
  have hΛd := ((contDiffAt_lamI hL hLss hU hUpos).differentiableAt one_ne_zero).hasFDerivAt
  have hΛc : HasFDerivAt (lamI β ibm Ybar L Uc) (fderiv ℝ (lamI β ibm Ybar L Uc) 0)
      (curMap13 0) := by rw [map_zero]; exact hΛd
  have hΛn : HasFDerivAt (lamI β ibm Ybar L Uc) (fderiv ℝ (lamI β ibm Ybar L Uc) 0)
      (nextMap13 0) := by rw [map_zero]; exact hΛd
  have hΘ : HasFDerivAt (solveRule ψ hψ hφ)
      ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp (ruleDInv ψ)) (lagMap13 0) := by
    rw [map_zero]
    exact hasFDerivAt_solveRule hψ hφ h0
  let X1 : ℝ × ℝ × ((ℝ × ℝ) × (ℝ × ℝ) × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ _
  have h := (((X1.hasFDerivAt (x := 0)).sub (hΛc.comp 0 curMap13.hasFDerivAt)).add
    (hΛn.comp 0 nextMap13.hasFDerivAt)).sub (hΘ.comp 0 lagMap13.hasFDerivAt)
  refine ⟨_, h, fun x x' y ξ y' ξ' ν => ?_⟩
  simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply]
  have hd := solveRule_deriv_apply (ψ := ψ) x' x ν
  simp only [ContinuousLinearMap.comp_apply] at hd
  have e1 : lagMap13 (x, x', ((y, ξ), (y', ξ'), ν)) = (x', x, ν) := rfl
  have e2 : curMap13 (x, x', ((y, ξ), (y', ξ'), ν)) = (x, y, ξ) := rfl
  have e3 : nextMap13 (x, x', ((y, ξ), (y', ξ'), ν)) = (x', y', ξ') := rfl
  rw [e1, e2, e3, hd]
  rfl

/-- Woodford (2003), (A.33), p. 646: the slopes of the exact inertial-rule condition with
non-separable utility, `a = 1 + χη_i + ρ/φ_π = γ₀/φ_π` and `b = −(χη_i + 1/φ_π) = −γ₁/φ_π`
(`NonSeparable.gamma0`, `gamma1`). -/
theorem slopes_F13 {β ibm Ybar mbar : ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ} {ψ : ℝ × ℝ × ℝ → ℝ}
    (hψ : ContDiffAt ℝ 1 ψ 0) (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) (h0 : ψ 0 = 0) (hm : 0 < mbar)
    (hL : ContDiffAt ℝ 1 L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ 1 Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0)) :
    slopeA (F13 β ibm Ybar L Uc ψ hψ hφ) = NonSeparable.gamma0 (etaNS β ibm mbar Ybar L)
        (chiNS Ybar mbar Uc) (phiPi ψ) (rhoR ψ) / phiPi ψ ∧
      slopeB (F13 β ibm Ybar L Uc ψ hψ hφ) = -(NonSeparable.gamma1 (etaNS β ibm mbar Ybar L)
        (chiNS Ybar mbar Uc) (phiPi ψ) / phiPi ψ) ∧
      ∀ y ξ y' ξ' ν : ℝ, slopeC (F13 β ibm Ybar L Uc ψ hψ hφ) ((y, ξ), (y', ξ'), ν) =
        -(fderiv ℝ (lamI β ibm Ybar L Uc) 0 (0, 1, 0) * (y - y') +
          fderiv ℝ (lamI β ibm Ybar L Uc) 0 (0, 0, 1) * (ξ - ξ')) + nuR ψ / phiPi ψ * ν := by
  obtain ⟨F', hF', hv⟩ := hasFDerivAt_F13 hψ hφ h0 hL hLss hU hUpos
  obtain ⟨ha, hb, hc⟩ := slopes_of_hasFDerivAt hF'
  have hj := lamI_j hm (hL.differentiableAt one_ne_zero) hLss (hU.differentiableAt one_ne_zero)
    hUpos
  have hφ' : phiPi ψ ≠ 0 := hφ
  set DL := fderiv ℝ (lamI β ibm Ybar L Uc) 0 with hDL
  refine ⟨?_, ?_, fun y ξ y' ξ' ν => ?_⟩
  · rw [ha]
    change F' (1, 0, (((0 : ℝ), (0 : ℝ)), ((0 : ℝ), (0 : ℝ)), (0 : ℝ))) = _
    rw [hv, MoneyGrowth.clm3_apply DL 1 0 0, MoneyGrowth.clm3_apply DL 0 0 0, hj]
    simp only [NonSeparable.gamma0]
    field_simp
    ring
  · rw [hb]
    change F' (0, 1, (((0 : ℝ), (0 : ℝ)), ((0 : ℝ), (0 : ℝ)), (0 : ℝ))) = _
    rw [hv, MoneyGrowth.clm3_apply DL 0 0 0, MoneyGrowth.clm3_apply DL 1 0 0, hj]
    simp only [NonSeparable.gamma1]
    field_simp
    ring
  · rw [hc, hv, MoneyGrowth.clm3_apply DL 0 y ξ, MoneyGrowth.clm3_apply DL 0 y' ξ']
    field_simp
    ring

/-- Woodford (2003), A.13, p. 646: for `φ_π ≠ 0`, `|b| < |a|` iff `|γ₁| < |γ₀|`. -/
theorem gamma_slope_iff {a b g0 g1 φ : ℝ} (hφ : φ ≠ 0) (ha : a = g0 / φ) (hb : b = -(g1 / φ)) :
    |b| < |a| ↔ |g1| < |g0| := by
  have hpos : 0 < |φ| := abs_pos.mpr hφ
  rw [ha, hb, abs_neg, abs_div, abs_div, div_lt_div_iff_of_pos_right hpos]

/-- Woodford (2003), (3.3), p. 104: near the steady state the marginal utility of consumption,
with real balances from (3.5), is positive. -/
theorem nsi_pos_radius {β ibm Ybar mbar : ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ}
    (hL : ContDiffAt ℝ 1 L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ 1 Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0)) :
    ∃ ρ > 0, ∀ j y ξ : ℝ, |j| < ρ → |y| < ρ → |ξ| < ρ →
      0 < Uc (Ybar * Real.exp y, L (Ybar * Real.exp y, 1 - β * (1 + ibm) * Real.exp (-j), ξ),
        ξ) := by
  have hin1 : ContinuousAt (fun q : ℝ × ℝ × ℝ => ((Ybar * Real.exp q.2.1,
      1 - β * (1 + ibm) * Real.exp (-q.1), q.2.2) : ℝ × ℝ × ℝ)) 0 := by fun_prop
  have hLq : ContinuousAt (fun q : ℝ × ℝ × ℝ => L ((Ybar * Real.exp q.2.1,
      1 - β * (1 + ibm) * Real.exp (-q.1), q.2.2) : ℝ × ℝ × ℝ)) 0 :=
    hL.continuousAt.comp_of_eq hin1 (by simp)
  have hin2 : ContinuousAt (fun q : ℝ × ℝ × ℝ => ((Ybar * Real.exp q.2.1, L (Ybar *
      Real.exp q.2.1, 1 - β * (1 + ibm) * Real.exp (-q.1), q.2.2), q.2.2) : ℝ × ℝ × ℝ)) 0 :=
    (by fun_prop : ContinuousAt (fun q : ℝ × ℝ × ℝ => Ybar * Real.exp q.2.1) 0).prodMk
      (hLq.prodMk (by fun_prop))
  have hc : ContinuousAt (fun q : ℝ × ℝ × ℝ => Uc (Ybar * Real.exp q.2.1, L (Ybar *
      Real.exp q.2.1, 1 - β * (1 + ibm) * Real.exp (-q.1), q.2.2), q.2.2)) 0 :=
    hU.continuousAt.comp_of_eq hin2 (by simp [hLss])
  have hp : 0 < (fun q : ℝ × ℝ × ℝ => Uc (Ybar * Real.exp q.2.1, L (Ybar *
      Real.exp q.2.1, 1 - β * (1 + ibm) * Real.exp (-q.1), q.2.2), q.2.2)) 0 := by
    simpa [hLss] using hUpos
  obtain ⟨ρ, hρ, hρP⟩ := Metric.eventually_nhds_iff.mp (hc.eventually (lt_mem_nhds hp))
  refine ⟨ρ, hρ, fun j y ξ hj hy hξ => ?_⟩
  have hd : dist ((j, y, ξ) : ℝ × ℝ × ℝ) 0 < ρ := by
    rw [dist_zero_right, Prod.norm_mk, Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_eq_abs]
    exact max_lt hj (max_lt hy hξ)
  exact hρP hd

/-- Woodford (2003), A.13, p. 646: coordinates of the maps feeding `F13`. -/
theorem maps13_apply (x x' y ξ y' ξ' ν : ℝ) :
    curMap13 (x, x', ((y, ξ), (y', ξ'), ν)) = (x, y, ξ) ∧
      nextMap13 (x, x', ((y, ξ), (y', ξ'), ν)) = (x', y', ξ') ∧
      lagMap13 (x, x', ((y, ξ), (y', ξ'), ν)) = (x', x, ν) := ⟨rfl, rfl, rfl⟩

/-- Woodford (2003), (1.21), (3.5) and (2.12), pp. 72, 104, 96, perfect foresight: an
**inertial-rule equilibrium with non-separable utility** (interest on money `īᵐ`, predetermined
`i_{−1}`): positive inflation `Π`, gross rates `1 + i > 0` and real balances `m` with
`m_t = L(Y_t, (i_t − īᵐ)/(1 + i_t); ξ_t)`,
`1 + i_t = u_c(Y_t, m_t; ξ_t)/(β u_c(Y_{t+1}, m_{t+1}; ξ_{t+1})) Π_{t+1}` and
`log(β(1 + i_t)) = ψ(log Π_t, log(β(1 + i_{t−1})), ν_t)`. -/
def NSIEq (β ibm : ℝ) (L Uc ψ : ℝ × ℝ × ℝ → ℝ) (Y ξ ν : ℕ → ℝ) (im1 : ℝ) (Infl i m : ℕ → ℝ) :
    Prop :=
  (∀ t, 0 < Infl t) ∧ (∀ t, 0 < 1 + i t) ∧ (∀ t, m t = L (Y t, (i t - ibm) / (1 + i t), ξ t)) ∧
    (∀ t, 1 + i t = Uc (Y t, m t, ξ t) / (β * Uc (Y (t + 1), m (t + 1), ξ (t + 1))) *
      Infl (t + 1)) ∧
    ∀ t, Real.log (β * (1 + i t)) = ψ (Real.log (Infl t), jLag β im1 i t, ν t)

/-- Woodford (2003), A.13, p. 646: the disturbance vector `((ŷ_t, ξ_t), (ŷ_{t+1}, ξ_{t+1}),
ν_{t+1})`. -/
noncomputable def e13t (Ybar : ℝ) (Y ξ ν : ℕ → ℝ) (t : ℕ) : (ℝ × ℝ) × (ℝ × ℝ) × ℝ :=
  ((Real.log (Y t / Ybar), ξ t), (Real.log (Y (t + 1) / Ybar), ξ (t + 1)), ν (t + 1))

/-- Woodford (2003), A.13, p. 646: the disturbance vector is bounded by the bound on its
components. -/
theorem norm_e13t_le {Ybar d : ℝ} {Y ξ ν : ℕ → ℝ} (hY : ∀ t, |Real.log (Y t / Ybar)| ≤ d)
    (hξ : ∀ t, |ξ t| ≤ d) (hν : ∀ t, |ν t| ≤ d) (t : ℕ) : ‖e13t Ybar Y ξ ν t‖ ≤ d := by
  simp only [e13t]
  refine norm_prod_le_iff.mpr ⟨norm_prod_le_iff.mpr ⟨?_, ?_⟩,
    norm_prod_le_iff.mpr ⟨norm_prod_le_iff.mpr ⟨?_, ?_⟩, ?_⟩⟩ <;> rw [Real.norm_eq_abs]
  exacts [hY t, hξ t, hY (t + 1), hξ (t + 1), hν (t + 1)]

/-- Woodford (2003), (3.3), p. 104: positivity of `u_c` at a date close to the steady state,
in the economy's variables. -/
theorem nsi_pos_at {β ibm Ybar ρ : ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β) (hYb : 0 < Ybar)
    (hpos : ∀ j y ξ : ℝ, |j| < ρ → |y| < ρ → |ξ| < ρ →
      0 < Uc (Ybar * Real.exp y, L (Ybar * Real.exp y, 1 - β * (1 + ibm) * Real.exp (-j), ξ), ξ))
    {Y ξ i : ℝ} (hY : 0 < Y) (hi : 0 < 1 + i) (h1 : |Real.log (β * (1 + i))| < ρ)
    (h2 : |Real.log (Y / Ybar)| < ρ) (h3 : |ξ| < ρ) :
    0 < Uc (Y, L (Y, (i - ibm) / (1 + i), ξ), ξ) := by
  have h := hpos _ _ _ h1 h2 h3
  have e1 : Ybar * Real.exp (Real.log (Y / Ybar)) = Y := by
    rw [Real.exp_log (by positivity)]
    field_simp
  rwa [e1, spread_of_j hβ hi] at h

/-- Woodford (2003), A.13, p. 646: near the steady state every inertial-rule equilibrium with
non-separable utility solves the period condition `F13` date by date. -/
theorem nsi_solves {β ibm Ybar ρ ρΘ : ℝ} {L Uc ψ : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β) (hYb : 0 < Ybar)
    {hψ : ContDiffAt ℝ 1 ψ 0} {hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0}
    (hpos : ∀ j y ξ : ℝ, |j| < ρ → |y| < ρ → |ξ| < ρ →
      0 < Uc (Ybar * Real.exp y, L (Ybar * Real.exp y, 1 - β * (1 + ibm) * Real.exp (-j), ξ), ξ))
    (hL : ∀ q : ℝ × ℝ × ℝ, ‖q‖ < ρΘ → solveRule ψ hψ hφ (ψ q, q.2) = q.1)
    {Y ξ ν Infl i m : ℕ → ℝ} {im1 : ℝ} (hY : ∀ t, 0 < Y t)
    (hE : NSIEq β ibm L Uc ψ Y ξ ν im1 Infl i m)
    (hb : ∀ t, |Real.log (β * (1 + i t))| < min ρ ρΘ ∧ |Real.log (Infl t)| < ρΘ ∧
      |ν t| < ρΘ ∧ |Real.log (Y t / Ybar)| < ρ ∧ |ξ t| < ρ) (t : ℕ) :
    F13 β ibm Ybar L Uc ψ hψ hφ (Real.log (β * (1 + i t)), Real.log (β * (1 + i (t + 1))),
      e13t Ybar Y ξ ν t) = 0 := by
  obtain ⟨hP, hi, hmm, hF, hrule⟩ := hE
  have hU0 := nsi_pos_at hβ hYb hpos (hY t) (hi t) (lt_of_lt_of_le (hb t).1 (min_le_left _ _))
    (hb t).2.2.2.1 (hb t).2.2.2.2
  have hU1 := nsi_pos_at hβ hYb hpos (hY (t + 1)) (hi (t + 1))
    (lt_of_lt_of_le (hb (t + 1)).1 (min_le_left _ _)) (hb (t + 1)).2.2.2.1 (hb (t + 1)).2.2.2.2
  rw [← hmm t] at hU0
  rw [← hmm (t + 1)] at hU1
  have hl0 := lamI_at (ibm := ibm) (L := L) (Uc := Uc) (ξ := ξ t) hβ hYb (hY t) (hi t)
  have hl1 := lamI_at (ibm := ibm) (L := L) (Uc := Uc) (ξ := ξ (t + 1)) hβ hYb (hY (t + 1))
    (hi (t + 1))
  rw [← hmm t] at hl0
  rw [← hmm (t + 1)] at hl1
  have hq : ‖((Real.log (Infl (t + 1)), Real.log (β * (1 + i t)), ν (t + 1)) : ℝ × ℝ × ℝ)‖ <
      ρΘ := by
    rw [Prod.norm_mk, Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_lt (hb (t + 1)).2.1 (max_lt (lt_of_lt_of_le (hb t).1 (min_le_right _ _))
      (hb (t + 1)).2.2.1)
  have h1 := hL _ hq
  have hr1 := hrule (t + 1)
  simp only [jLag] at hr1
  rw [← hr1] at h1
  simp only at h1
  have hfl : Real.log (β * (1 + i t)) =
      Real.log (Uc (Y t, m t, ξ t)) - Real.log (Uc (Y (t + 1), m (t + 1), ξ (t + 1))) +
        Real.log (Infl (t + 1)) := by
    rw [hF t, show β * (Uc (Y t, m t, ξ t) / (β * Uc (Y (t + 1), m (t + 1), ξ (t + 1))) *
      Infl (t + 1)) = Uc (Y t, m t, ξ t) / Uc (Y (t + 1), m (t + 1), ξ (t + 1)) * Infl (t + 1) by
        field_simp, Real.log_mul (by positivity) (hP (t + 1)).ne', Real.log_div hU0.ne' hU1.ne']
  simp only [F13, e13t, (maps13_apply _ _ _ _ _ _ _).1, (maps13_apply _ _ _ _ _ _ _).2.1,
    (maps13_apply _ _ _ _ _ _ _).2.2]
  rw [hl0, hl1, h1, hfl]
  ring

/-- Woodford (2003), (1.21), p. 72: the algebra of the Fisher relation in levels,
`β⁻¹eᵃ = U₀/(β U₁) · e^{a − (log U₀ − log U₁)}`. -/
theorem fisher_aux {β a U0 U1 : ℝ} (hβ : 0 < β) (hU0 : 0 < U0) (hU1 : 0 < U1) :
    1 + (Real.exp a / β - 1) = U0 / (β * U1) * Real.exp (a - (Real.log U0 - Real.log U1)) := by
  rw [Real.exp_sub, Real.exp_sub, Real.exp_log hU0, Real.exp_log hU1]
  field_simp
  ring

/-- Woodford (2003), A.13, p. 646: conversely, a small solution `ĵ` of `F13` gives an
inertial-rule equilibrium with non-separable utility. -/
theorem nsiEq_of_solution {β ibm Ybar ρ ρΘ : ℝ} {L Uc ψ : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hYb : 0 < Ybar) {hψ : ContDiffAt ℝ 1 ψ 0} {hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0}
    (hpos : ∀ j y ξ : ℝ, |j| < ρ → |y| < ρ → |ξ| < ρ →
      0 < Uc (Ybar * Real.exp y, L (Ybar * Real.exp y, 1 - β * (1 + ibm) * Real.exp (-j), ξ), ξ))
    (hR : ∀ q : ℝ × ℝ × ℝ, ‖q‖ < ρΘ → ψ (solveRule ψ hψ hφ q, q.2) = q.1)
    {Y ξ ν x : ℕ → ℝ} {im1 : ℝ} (hY : ∀ t, 0 < Y t)
    (hsol : ∀ t, F13 β ibm Ybar L Uc ψ hψ hφ (x t, x (t + 1), e13t Ybar Y ξ ν t) = 0)
    (hx : ∀ t, |x t| < min ρ ρΘ) (hν : ∀ t, |ν t| < ρΘ) (hYs : ∀ t, |Real.log (Y t / Ybar)| < ρ)
    (hξ : ∀ t, |ξ t| < ρ) (hj : |Real.log (β * (1 + im1))| < ρΘ) :
    NSIEq β ibm L Uc ψ Y ξ ν im1
      (inflPath (solveRule ψ hψ hφ (x 0, Real.log (β * (1 + im1)), ν 0)) x
        (fun t => lamI β ibm Ybar L Uc (x t, Real.log (Y t / Ybar), ξ t) -
          lamI β ibm Ybar L Uc (x (t + 1), Real.log (Y (t + 1) / Ybar), ξ (t + 1))))
      (fun t => Real.exp (x t) / β - 1)
      (fun t => L (Y t, ((Real.exp (x t) / β - 1) - ibm) / (1 + (Real.exp (x t) / β - 1)), ξ t)) ∧
      (∀ t, Real.log (β * (1 + (Real.exp (x t) / β - 1))) = x t) ∧
      ∀ t, Real.log (inflPath (solveRule ψ hψ hφ (x 0, Real.log (β * (1 + im1)), ν 0)) x
        (fun t => lamI β ibm Ybar L Uc (x t, Real.log (Y t / Ybar), ξ t) -
          lamI β ibm Ybar L Uc (x (t + 1), Real.log (Y (t + 1) / Ybar), ξ (t + 1))) (t + 1)) =
        solveRule ψ hψ hφ (x (t + 1), x t, ν (t + 1)) := by
  have hβx : ∀ t, β * (1 + (Real.exp (x t) / β - 1)) = Real.exp (x t) := fun t => by
    field_simp
    ring
  have hxj : ∀ t, Real.log (β * (1 + (Real.exp (x t) / β - 1))) = x t := fun t => by
    rw [hβx, Real.log_exp]
  have hi : ∀ t, 0 < 1 + (Real.exp (x t) / β - 1) := fun t => by
    have := Real.exp_pos (x t)
    rw [show 1 + (Real.exp (x t) / β - 1) = Real.exp (x t) / β by ring]
    positivity
  have hnorm3 : ∀ a b c : ℝ, |a| < ρΘ → |b| < ρΘ → |c| < ρΘ →
      ‖((a, b, c) : ℝ × ℝ × ℝ)‖ < ρΘ := fun a b c ha hb hc => by
    rw [Prod.norm_mk, Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_lt ha (max_lt hb hc)
  have hU : ∀ t, 0 < Uc (Y t, L (Y t, ((Real.exp (x t) / β - 1) - ibm) /
      (1 + (Real.exp (x t) / β - 1)), ξ t), ξ t) := fun t => by
    have h1 : |Real.log (β * (1 + (Real.exp (x t) / β - 1)))| < ρ := by
      rw [hxj]
      exact lt_of_lt_of_le (hx t) (min_le_left _ _)
    exact nsi_pos_at hβ hYb hpos (hY t) (hi t) h1 (hYs t) (hξ t)
  have hl : ∀ t, lamI β ibm Ybar L Uc (x t, Real.log (Y t / Ybar), ξ t) =
      Real.log (Uc (Y t, L (Y t, ((Real.exp (x t) / β - 1) - ibm) /
        (1 + (Real.exp (x t) / β - 1)), ξ t), ξ t)) := fun t => by
    rw [← lamI_at hβ hYb (hY t) (hi t), hxj]
  have hΘ : ∀ t, x t - lamI β ibm Ybar L Uc (x t, Real.log (Y t / Ybar), ξ t) +
      lamI β ibm Ybar L Uc (x (t + 1), Real.log (Y (t + 1) / Ybar), ξ (t + 1)) =
        solveRule ψ hψ hφ (x (t + 1), x t, ν (t + 1)) := fun t => by
    have h := hsol t
    simp only [F13, e13t, (maps13_apply _ _ _ _ _ _ _).1, (maps13_apply _ _ _ _ _ _ _).2.1,
      (maps13_apply _ _ _ _ _ _ _).2.2] at h
    linarith
  have hinfl : ∀ t, Real.log (inflPath (solveRule ψ hψ hφ (x 0, Real.log (β * (1 + im1)), ν 0)) x
      (fun t => lamI β ibm Ybar L Uc (x t, Real.log (Y t / Ybar), ξ t) -
        lamI β ibm Ybar L Uc (x (t + 1), Real.log (Y (t + 1) / Ybar), ξ (t + 1))) (t + 1)) =
      solveRule ψ hψ hφ (x (t + 1), x t, ν (t + 1)) := fun t => by
    change Real.log (Real.exp (x t - (lamI β ibm Ybar L Uc (x t, Real.log (Y t / Ybar), ξ t) -
      lamI β ibm Ybar L Uc (x (t + 1), Real.log (Y (t + 1) / Ybar), ξ (t + 1))))) = _
    rw [Real.log_exp, ← hΘ t]
    ring
  refine ⟨⟨fun t => ?_, hi, fun t => rfl, fun t => ?_, fun t => ?_⟩, hxj, hinfl⟩
  · cases t <;> exact Real.exp_pos _
  · change 1 + (Real.exp (x t) / β - 1) = _ / _ * Real.exp (x t - (lamI β ibm Ybar L Uc
      (x t, Real.log (Y t / Ybar), ξ t) - lamI β ibm Ybar L Uc (x (t + 1),
        Real.log (Y (t + 1) / Ybar), ξ (t + 1))))
    rw [hl t, hl (t + 1)]
    exact fisher_aux hβ (hU t) (hU (t + 1))
  · rw [hxj]
    cases t with
    | zero =>
      change x 0 = ψ (Real.log (Real.exp (solveRule ψ hψ hφ (x 0, Real.log (β * (1 + im1)),
        ν 0))), Real.log (β * (1 + im1)), ν 0)
      rw [Real.log_exp]
      exact (hR _ (hnorm3 _ _ _ (lt_of_lt_of_le (hx 0) (min_le_right _ _)) hj (hν 0))).symm
    | succ t =>
      change x (t + 1) = ψ (Real.log (inflPath (solveRule ψ hψ hφ (x 0, Real.log (β * (1 + im1)),
        ν 0)) x (fun t => lamI β ibm Ybar L Uc (x t, Real.log (Y t / Ybar), ξ t) -
          lamI β ibm Ybar L Uc (x (t + 1), Real.log (Y (t + 1) / Ybar), ξ (t + 1))) (t + 1)),
        Real.log (β * (1 + (Real.exp (x t) / β - 1))), ν (t + 1))
      rw [hinfl t, hxj]
      exact (hR _ (hnorm3 _ _ _ (lt_of_lt_of_le (hx (t + 1)) (min_le_right _ _))
        (lt_of_lt_of_le (hx t) (min_le_right _ _)) (hν (t + 1)))).symm

/-- Woodford (2003), **Proposition 2.13**, p. 116 and A.13, p. 646, **exact perfect-foresight
version** (determinacy half), under the exact (A.33) condition `|γ₁| < |γ₀|` with `φ_π ≠ 0`:
if `ψ`, `L`, `u_c` are `C¹` near the steady state, there are `ε, ε_π, δ > 0` such that whenever
`log(Y_t/Ȳ)`, `ξ_t`, `ν_t` and the predetermined `ĵ_{−1}` are within `δ` there is an
equilibrium with `|ĵ_t| ≤ ε`, `|π_t| ≤ ε_π`, and it is the only one in that neighbourhood. -/
theorem nsi_local_determinacy {β ibm Ybar mbar : ℝ} {L Uc ψ : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hYb : 0 < Ybar) (hm : 0 < mbar) (hψ : ContDiffAt ℝ 1 ψ 0) (h0 : ψ 0 = 0)
    (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) (hL : ContDiffAt ℝ 1 L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ 1 Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0))
    (hγ : |NonSeparable.gamma1 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc) (phiPi ψ)| <
      |NonSeparable.gamma0 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc) (phiPi ψ) (rhoR ψ)|) :
    ∃ ε > 0, ∃ εP > 0, ∃ δ > 0, ∀ Y ξ ν : ℕ → ℝ, ∀ im1 : ℝ, (∀ t, 0 < Y t) →
      (∀ t, |Real.log (Y t / Ybar)| ≤ δ) → (∀ t, |ξ t| ≤ δ) → (∀ t, |ν t| ≤ δ) →
      |Real.log (β * (1 + im1))| ≤ δ →
      (∃ Infl i m : ℕ → ℝ, NSIEq β ibm L Uc ψ Y ξ ν im1 Infl i m ∧
        ∀ t, |Real.log (β * (1 + i t))| ≤ ε ∧ |Real.log (Infl t)| ≤ εP) ∧
      ∀ Infl i m Infl' i' m' : ℕ → ℝ, NSIEq β ibm L Uc ψ Y ξ ν im1 Infl i m →
        NSIEq β ibm L Uc ψ Y ξ ν im1 Infl' i' m' →
        (∀ t, |Real.log (β * (1 + i t))| ≤ ε ∧ |Real.log (Infl t)| ≤ εP) →
        (∀ t, |Real.log (β * (1 + i' t))| ≤ ε ∧ |Real.log (Infl' t)| ≤ εP) →
        Infl = Infl' ∧ i = i' ∧ m = m' := by
  obtain ⟨ρU, hρU, hposU⟩ := nsi_pos_radius hL hLss hU hUpos
  obtain ⟨ρΘ, hρΘ, hLΘ, hRΘ⟩ := solveRule_local hψ hφ h0
  obtain ⟨ρc, hρc, hsmall⟩ := solveRule_small hψ hφ h0 (half_pos hρΘ)
  obtain ⟨ha, hb, -⟩ := slopes_F13 hψ hφ h0 hm hL hLss hU hUpos
  have hab : |slopeB (F13 β ibm Ybar L Uc ψ hψ hφ)| < |slopeA (F13 β ibm Ybar L Uc ψ hψ hφ)| :=
    (gamma_slope_iff hφ ha hb).mpr hγ
  set η := min (min ρU ρΘ) ρc / 4 with hη
  have hη0 : 0 < η := by positivity
  have hηU : η < ρU / 2 := by
    have := min_le_left (min ρU ρΘ) ρc; have := min_le_left ρU ρΘ; linarith
  have hηΘ : η < ρΘ / 2 := by
    have := min_le_left (min ρU ρΘ) ρc; have := min_le_right ρU ρΘ; linarith
  have hηc : η < ρc := by have := min_le_right (min ρU ρΘ) ρc; linarith
  obtain ⟨ε, hε, hεη, δ, hδ, hδη, X, -, -, hX⟩ :=
    local_determinacy_loc (contDiffAt_F13 hψ hφ h0 hψ hL hLss hU hUpos) (F13_zero hψ hφ h0) hab
      hη0
  refine ⟨ε / 2, half_pos hε, ρΘ / 2, half_pos hρΘ, δ / 2, half_pos hδ,
    fun Y ξ ν im1 hY hYd hξd hνd hj => ?_⟩
  have hK := norm_e13t_le hYd hξd hνd
  set e : Seq ((ℝ × ℝ) × (ℝ × ℝ) × ℝ) := mkS (e13t Ybar Y ξ ν) ⟨δ / 2, hK⟩ with he
  have hen : ‖e‖ < δ := lt_of_le_of_lt (norm_seq_le (by positivity) hK) (half_lt_self hδ)
  obtain ⟨hXn, hXs, -, huniq⟩ := hX e hen
  have hminU : ∀ a : ℝ, |a| ≤ η → |a| < min ρU ρΘ := fun a ha => lt_min (by linarith)
    (by linarith)
  have hclass : ∀ Infl i m : ℕ → ℝ, NSIEq β ibm L Uc ψ Y ξ ν im1 Infl i m →
      ∀ hbd : (∀ t, |Real.log (β * (1 + i t))| ≤ ε / 2 ∧ |Real.log (Infl t)| ≤ ρΘ / 2),
      mk (fun t => Real.log (β * (1 + i t))) ⟨ε / 2, fun t => (hbd t).1⟩ = X e :=
    fun Infl i m hE hbd => huniq _
      (lt_of_le_of_lt (norm_le_of_abs_le (by positivity) (fun t => (hbd t).1)) (half_lt_self hε))
      (fun t => nsi_solves hβ hYb hposU hLΘ hY hE (fun s => ⟨hminU _ (by linarith [(hbd s).1]),
        by linarith [(hbd s).2], by linarith [hνd s], by linarith [hYd s], by linarith [hξd s]⟩)
        t)
  refine ⟨?_, ?_⟩
  · set x := X e with hx
    have hxt : ∀ t, |x t| < ε / 2 := fun t => lt_of_le_of_lt (abs_apply_le x t) hXn
    obtain ⟨hE, hxj, hinfl⟩ := nsiEq_of_solution (im1 := im1) hβ hYb hposU hRΘ hY hXs
      (fun t => hminU _ (by linarith [hxt t])) (fun t => by linarith [hνd t])
      (fun t => by linarith [hYd t]) (fun t => by linarith [hξd t]) (by linarith)
    refine ⟨_, _, _, hE, fun t => ⟨by rw [hxj]; exact (hxt t).le, ?_⟩⟩
    have hq : ∀ a b c : ℝ, |a| ≤ η → |b| ≤ η → |c| ≤ η →
        |solveRule ψ hψ hφ (a, b, c)| < ρΘ / 2 := fun a b c ha hb hc => hsmall _ (by
      rw [Prod.norm_mk, Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_lt (by linarith) (max_lt (by linarith) (by linarith)))
    cases t with
    | zero =>
      change |Real.log (Real.exp (solveRule ψ hψ hφ (x 0, Real.log (β * (1 + im1)), ν 0)))| ≤ _
      rw [Real.log_exp]
      exact (hq _ _ _ (by linarith [hxt 0]) (by linarith) (by linarith [hνd 0])).le
    | succ t =>
      rw [hinfl t]
      exact (hq _ _ _ (by linarith [hxt (t + 1)]) (by linarith [hxt t])
        (by linarith [hνd (t + 1)])).le
  · intro Infl i m Infl' i' m' hE hE' hb hb'
    have hlog : ∀ t, Real.log (β * (1 + i t)) = Real.log (β * (1 + i' t)) := fun t =>
      congrArg (fun y : Linf => y t) ((hclass Infl i m hE hb).trans
        (hclass Infl' i' m' hE' hb').symm)
    have hii : i = i' := funext fun t => by
      have h := Real.log_injOn_pos (Set.mem_Ioi.mpr (mul_pos hβ (hE.2.1 t)))
        (Set.mem_Ioi.mpr (mul_pos hβ (hE'.2.1 t))) (hlog t)
      have := hβ.ne'
      field_simp at h
      linarith
    have hmm : m = m' := funext fun t => by rw [hE.2.2.1 t, hE'.2.2.1 t, hii]
    refine ⟨funext fun t => ?_, hii, hmm⟩
    cases t with
    | zero =>
      have hn : ∀ a : ℝ, |a| ≤ ρΘ / 2 → ‖((a, Real.log (β * (1 + im1)), ν 0) : ℝ × ℝ × ℝ)‖ <
          ρΘ := fun a ha => by
        rw [Prod.norm_mk, Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
        exact max_lt (by linarith) (max_lt (by linarith) (by linarith [hνd 0]))
      have q1 := hLΘ _ (hn _ (hb 0).2)
      have q2 := hLΘ _ (hn _ (hb' 0).2)
      have r1 := hE.2.2.2.2 0
      have r2 := hE'.2.2.2.2 0
      simp only [jLag] at r1 r2
      rw [← r1] at q1
      rw [← r2, ← hii] at q2
      simp only at q1 q2
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr (hE.1 0)) (Set.mem_Ioi.mpr (hE'.1 0))
        (q1.symm.trans q2)
    | succ t =>
      have h1 := hE.2.2.2.1 t
      have h2 := hE'.2.2.2.1 t
      rw [hii, hmm] at h1
      have hne : Uc (Y t, m' t, ξ t) / (β * Uc (Y (t + 1), m' (t + 1), ξ (t + 1))) ≠ 0 := by
        intro h
        rw [h, zero_mul] at h2
        linarith [hE'.2.1 t]
      exact mul_left_cancel₀ hne (h1.symm.trans h2)

/-- Woodford (2003), **Proposition 2.13**, p. 116 (book form): under (3.16) `χ > −1/(2η_i)`,
`η_i > 0`, `ρ ≥ 0`, an inertial rule with `φ_π > 0` and `φ_π + ρ > 1` (2.13) gives local
determinacy of the exact model (`|γ₁| < |γ₀|` via `NonSeparable.gamma_add_pos`, `gamma_sub`). -/
theorem prop_2_13_cond {ηi χ φπ ρ : ℝ} (hηi : 0 < ηi) (hχ : -1 / (2 * ηi) < χ) (hφ : 0 < φπ)
    (hρ : 0 ≤ ρ) (h213 : 1 < φπ + ρ) :
    |NonSeparable.gamma1 ηi χ φπ| < |NonSeparable.gamma0 ηi χ φπ ρ| := by
  rw [ForwardSolution.abs_lt_abs_iff_of_add_pos (NonSeparable.gamma_add_pos hηi hχ hφ.le hρ)]
  have := NonSeparable.gamma_sub ηi χ φπ ρ
  linarith

/-- Woodford (2003), Prop. 2.13, p. 116 (indeterminacy half), **exact perfect-foresight version**:
if `φ_π ≠ 0` and `|γ₀| < |γ₁|`, then with constant fundamentals (`Y ≡ Ȳ`, `ξ ≡ 0`, `ν ≡ 0`,
`i_{−1} = ī`) every initial interest rate `ĵ_0 = c` with `|c| ≤ r` starts an exact equilibrium
within `ε` of the steady state; distinct `c` give distinct equilibria. -/
theorem nsi_local_indeterminacy {β ibm Ybar mbar : ℝ} {L Uc ψ : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hYb : 0 < Ybar) (hm : 0 < mbar) (hψ : ContDiffAt ℝ 1 ψ 0) (h0 : ψ 0 = 0)
    (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) (hL : ContDiffAt ℝ 1 L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ 1 Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0))
    (hγ : |NonSeparable.gamma0 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc) (phiPi ψ) (rhoR ψ)| <
      |NonSeparable.gamma1 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc) (phiPi ψ)|) :
    ∀ ε > 0, ∃ r > 0, ∀ c : ℝ, |c| ≤ r → ∃ Infl i m : ℕ → ℝ,
      NSIEq β ibm L Uc ψ (fun _ => Ybar) (fun _ => 0) (fun _ => 0) (β⁻¹ - 1) Infl i m ∧
        Real.log (β * (1 + i 0)) = c ∧
        ∀ t, |Real.log (β * (1 + i t))| ≤ ε ∧ |Real.log (Infl t)| ≤ ε := by
  intro ε hε
  obtain ⟨ρU, hρU, hposU⟩ := nsi_pos_radius hL hLss hU hUpos
  obtain ⟨ρΘ, hρΘ, -, hRΘ⟩ := solveRule_local hψ hφ h0
  obtain ⟨ρc, hρc, hsmall⟩ := solveRule_small hψ hφ h0 hε
  obtain ⟨ha, hb, -⟩ := slopes_F13 hψ hφ h0 hm hL hLss hU hUpos
  have hab : |slopeA (F13 β ibm Ybar L Uc ψ hψ hφ)| < |slopeB (F13 β ibm Ybar L Uc ψ hψ hφ)| := by
    have hpos : 0 < |phiPi ψ| := abs_pos.mpr hφ
    rw [ha, hb, abs_neg, abs_div, abs_div, div_lt_div_iff_of_pos_right hpos]
    exact hγ
  set ε' := min ε (min (min ρU ρΘ) ρc) / 2 with hε'
  have hε'0 : 0 < ε' := by positivity
  have hm1 := min_le_left ε (min (min ρU ρΘ) ρc)
  have hm2 := min_le_right ε (min (min ρU ρΘ) ρc)
  have hm3 := min_le_left (min ρU ρΘ) ρc
  have hm4 := min_le_right (min ρU ρΘ) ρc
  have hm5 := min_le_left ρU ρΘ
  have hm6 := min_le_right ρU ρΘ
  obtain ⟨r, hr, hx⟩ := local_indeterminacy_loc
    (contDiffAt_F13 hψ hφ h0 hψ hL hLss hU hUpos) (F13_zero hψ hφ h0) hab ε' hε'0
  refine ⟨r, hr, fun c hc => ?_⟩
  obtain ⟨x, hxs, hxn, hx0⟩ := hx c hc
  have hxt : ∀ t, |x t| ≤ ε' := fun t => (abs_apply_le x t).trans hxn
  have hl1 : Real.log (Ybar / Ybar) = 0 := by rw [div_self hYb.ne', Real.log_one]
  have hj : Real.log (β * (1 + (β⁻¹ - 1))) = 0 := by
    rw [show β * (1 + (β⁻¹ - 1)) = 1 by field_simp; ring, Real.log_one]
  have hsol : ∀ t, F13 β ibm Ybar L Uc ψ hψ hφ (x t, x (t + 1),
      e13t Ybar (fun _ => Ybar) (fun _ => 0) (fun _ => 0) t) = 0 := fun t => by
    have h := hxs t
    simp only [e13t, hl1]
    convert h using 2
    simp only [lp.coeFn_zero, Pi.zero_apply, Prod.mk_zero_zero]
  obtain ⟨hE, hxj, hinfl⟩ := nsiEq_of_solution (im1 := β⁻¹ - 1) (ν := fun _ => 0) hβ hYb hposU
    hRΘ (fun _ => hYb) hsol (fun t => lt_min (by linarith [hxt t]) (by linarith [hxt t]))
    (fun _ => by simpa using hρΘ) (fun _ => by rw [hl1, abs_zero]; exact hρU)
    (fun _ => by simpa using hρU) (by rw [hj, abs_zero]; exact hρΘ)
  refine ⟨_, _, _, hE, by rw [hxj, hx0], fun t => ⟨by rw [hxj]; linarith [hxt t], ?_⟩⟩
  have hq : ∀ a b : ℝ, |a| ≤ ε' → |b| ≤ ε' → |solveRule ψ hψ hφ (a, b, 0)| < ε :=
    fun a b ha hb => hsmall _ (by
      rw [Prod.norm_mk, Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs, norm_zero]
      exact max_lt (by linarith) (max_lt (by linarith) (by linarith)))
  cases t with
  | zero =>
    change |Real.log (Real.exp (solveRule ψ hψ hφ (x 0, Real.log (β * (1 + (β⁻¹ - 1))), 0)))| ≤ ε
    rw [Real.log_exp, hj]
    exact (hq _ _ (hxt 0) (by rw [abs_zero]; linarith)).le
  | succ t =>
    rw [hinfl t]
    exact (hq _ _ (hxt (t + 1)) (hxt t)).le

/-- Woodford (2003), Prop. 2.13, p. 116 and App. A.3, p. 633 (`C¹` dependence): in sequence space
the exact interest-rate path `ĵ = X(e)` is `C¹` in the disturbances near zero, with `X(0) = 0`
and derivative the log-linear solution (3.20). -/
theorem nsi_smooth_dependence {β ibm Ybar mbar : ℝ} {L Uc ψ : ℝ × ℝ × ℝ → ℝ} (hm : 0 < mbar)
    (hψ : ContDiffAt ℝ 1 ψ 0) (h0 : ψ 0 = 0)
    (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) (hL : ContDiffAt ℝ 1 L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ 1 Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0))
    (hγ : |NonSeparable.gamma1 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc) (phiPi ψ)| <
      |NonSeparable.gamma0 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc) (phiPi ψ) (rhoR ψ)|) :
    ∃ δ > 0, ∃ X : Seq ((ℝ × ℝ) × (ℝ × ℝ) × ℝ) → Linf, X 0 = 0 ∧
      HasFDerivAt X (linSol3 (F13 β ibm Ybar L Uc ψ hψ hφ)) 0 ∧
      ∀ e, ‖e‖ < δ → Solves (F13 β ibm Ybar L Uc ψ hψ hφ) e (X e) ∧ ContDiffAt ℝ 1 X e := by
  obtain ⟨ha, hb, -⟩ := slopes_F13 hψ hφ h0 hm hL hLss hU hUpos
  obtain ⟨ε, hε, -, δ, hδ, -, X, hX0, hXd, hX⟩ :=
    local_determinacy_loc (contDiffAt_F13 hψ hφ h0 hψ hL hLss hU hUpos) (F13_zero hψ hφ h0)
      ((gamma_slope_iff hφ ha hb).mpr hγ) one_pos
  exact ⟨δ, hδ, X, hX0, hXd, fun e he => ⟨(hX e he).2.1, (hX e he).2.2.1⟩⟩

/-- Woodford (2003), (3.20)–(3.22), p. 117 and (A.33), p. 646, **the first-order term of the exact
inertial-rule equilibrium with non-separable utility**:
`ĵ_t = ∑_k γ₁ᵏ/γ₀^{k+1} (φ_π r̃_{t+k} − c ν_{t+k+1})` with
`r̃_s = Λ_y (ŷ_s − ŷ_{s+1}) + Λ_ξ (ξ_s − ξ_{s+1})` (the composite of (3.12)). -/
theorem linSol3_F13_apply {β ibm Ybar mbar : ℝ} {L Uc ψ : ℝ × ℝ × ℝ → ℝ} (hm : 0 < mbar)
    (hψ : ContDiffAt ℝ 1 ψ 0) (h0 : ψ 0 = 0)
    (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) (hL : ContDiffAt ℝ 1 L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ 1 Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0))
    (hγ : |NonSeparable.gamma1 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc) (phiPi ψ)| <
      |NonSeparable.gamma0 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc) (phiPi ψ) (rhoR ψ)|)
    (e : Seq ((ℝ × ℝ) × (ℝ × ℝ) × ℝ)) (t : ℕ) :
    linSol3 (F13 β ibm Ybar L Uc ψ hψ hφ) e t = ∑' k,
      (NonSeparable.gamma1 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc) (phiPi ψ) /
        NonSeparable.gamma0 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc) (phiPi ψ) (rhoR ψ))
          ^ k / NonSeparable.gamma0 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc) (phiPi ψ)
            (rhoR ψ) *
        (phiPi ψ * (fderiv ℝ (lamI β ibm Ybar L Uc) 0 (0, 1, 0) *
            ((e (t + k)).1.1 - (e (t + k)).2.1.1) +
          fderiv ℝ (lamI β ibm Ybar L Uc) 0 (0, 0, 1) * ((e (t + k)).1.2 - (e (t + k)).2.1.2)) -
          nuR ψ * (e (t + k)).2.2) := by
  obtain ⟨ha, hb, hc⟩ := slopes_F13 hψ hφ h0 hm hL hLss hU hUpos
  have hab := (gamma_slope_iff hφ ha hb).mpr hγ
  have hg0 : NonSeparable.gamma0 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc) (phiPi ψ)
      (rhoR ψ) ≠ 0 := ne_zero_of_abs_lt hγ
  have hφ' : phiPi ψ ≠ 0 := hφ
  rw [linSol3_apply hab, ← neg_mul, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hv : e (t + k) = (((e (t + k)).1.1, (e (t + k)).1.2), ((e (t + k)).2.1.1,
      (e (t + k)).2.1.2), (e (t + k)).2.2) := rfl
  rw [hv, hc, ha, hb]
  simp only
  field_simp
  ring

/-- Woodford (2003), **Proposition 2.13**, p. 117 ("a log-linear approximation … is given by
(3.20)"), exact perfect-foresight version with the `C²` hypothesis of E18: every equilibrium near
the steady state satisfies `|ĵ_t − ĵ̂_t| ≤ C ξ²` (`ĵ̂` as in `linSol3_F13_apply`) when the
disturbances are bounded by `ξ < δ`. -/
theorem nsi_second_order {β ibm Ybar mbar : ℝ} {L Uc ψ : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hYb : 0 < Ybar) (hm : 0 < mbar) (hψ : ContDiffAt ℝ 1 ψ 0) (hψ2 : ContDiffAt ℝ 2 ψ 0)
    (h0 : ψ 0 = 0) (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0)
    (hL : ContDiffAt ℝ 2 L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ 2 Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0))
    (hγ : |NonSeparable.gamma1 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc) (phiPi ψ)| <
      |NonSeparable.gamma0 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc) (phiPi ψ) (rhoR ψ)|) :
    ∃ ε > 0, ∃ δ > 0, ∃ C : ℝ, ∀ Y ξ ν : ℕ → ℝ, ∀ im1 ξb : ℝ, (∀ t, 0 < Y t) → ξb < δ →
      (∀ t, |Real.log (Y t / Ybar)| ≤ ξb) → (∀ t, |ξ t| ≤ ξb) → (∀ t, |ν t| ≤ ξb) →
      ∀ Infl i m : ℕ → ℝ, NSIEq β ibm L Uc ψ Y ξ ν im1 Infl i m →
      (∀ t, |Real.log (β * (1 + i t))| ≤ ε ∧ |Real.log (Infl t)| ≤ ε) → ∀ t,
      |Real.log (β * (1 + i t)) - ∑' k,
        (NonSeparable.gamma1 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc) (phiPi ψ) /
          NonSeparable.gamma0 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc) (phiPi ψ) (rhoR ψ))
            ^ k / NonSeparable.gamma0 (etaNS β ibm mbar Ybar L) (chiNS Ybar mbar Uc) (phiPi ψ)
              (rhoR ψ) *
          (phiPi ψ * (fderiv ℝ (lamI β ibm Ybar L Uc) 0 (0, 1, 0) *
              (Real.log (Y (t + k) / Ybar) - Real.log (Y (t + k + 1) / Ybar)) +
            fderiv ℝ (lamI β ibm Ybar L Uc) 0 (0, 0, 1) * (ξ (t + k) - ξ (t + k + 1))) -
            nuR ψ * ν (t + k + 1))| ≤ C * ξb ^ 2 := by
  have hL1 : ContDiffAt ℝ 1 L (Ybar, 1 - β * (1 + ibm), 0) := hL.of_le (by norm_num)
  have hU1 : ContDiffAt ℝ 1 Uc (Ybar, mbar, 0) := hU.of_le (by norm_num)
  obtain ⟨ρU, hρU, hposU⟩ := nsi_pos_radius hL1 hLss hU1 hUpos
  obtain ⟨ρΘ, hρΘ, hLΘ, -⟩ := solveRule_local hψ hφ h0
  obtain ⟨ha, hb, -⟩ := slopes_F13 hψ hφ h0 hm hL1 hLss hU1 hUpos
  have hab := (gamma_slope_iff hφ ha hb).mpr hγ
  set η := min ρU ρΘ / 2 with hη
  have hη0 : 0 < η := by positivity
  have hηU : η < ρU := by have := min_le_left ρU ρΘ; linarith
  have hηΘ : η < ρΘ := by have := min_le_right ρU ρΘ; linarith
  obtain ⟨ε, hε, hεη, δ, hδ, hδη, C, hC⟩ :=
    second_order_loc (contDiffAt_F13 hψ hφ h0 hψ2 hL hLss hU hUpos) (F13_zero hψ hφ h0) hab hη0
  refine ⟨ε / 2, half_pos hε, δ, hδ, max C 0,
    fun Y ξ ν im1 ξb hY hξb hYd hξd hνd Infl i m hE hbd t => ?_⟩
  have hξ0 : 0 ≤ ξb := (abs_nonneg _).trans (hξd 0)
  have hK := norm_e13t_le hYd hξd hνd
  set e : Seq ((ℝ × ℝ) × (ℝ × ℝ) × ℝ) := mkS (e13t Ybar Y ξ ν) ⟨ξb, hK⟩ with he
  have hen : ‖e‖ ≤ ξb := norm_seq_le hξ0 hK
  have hsol : Solves (F13 β ibm Ybar L Uc ψ hψ hφ) e
      (mk (fun t => Real.log (β * (1 + i t))) ⟨ε / 2, fun t => (hbd t).1⟩) := fun s =>
    nsi_solves hβ hYb hposU hLΘ hY hE (fun s => ⟨lt_min (by linarith [(hbd s).1])
      (by linarith [(hbd s).1]), by linarith [(hbd s).2], by linarith [hνd s],
      by linarith [hYd s], by linarith [hξd s]⟩) s
  have hbound := hC e (lt_of_le_of_lt hen hξb) _
    (lt_of_le_of_lt (norm_le_of_abs_le (by positivity) (fun t => (hbd t).1)) (half_lt_self hε))
    hsol
  have hcoord := abs_apply_le (mk (fun t => Real.log (β * (1 + i t)))
    ⟨ε / 2, fun t => (hbd t).1⟩ - linSol3 (F13 β ibm Ybar L Uc ψ hψ hφ) e) t
  simp only [lp.coeFn_sub, Pi.sub_apply, mk_apply] at hcoord
  rw [linSol3_F13_apply hm hψ h0 hφ hL1 hLss hU1 hUpos hγ] at hcoord
  simp only [he, mkS_apply, e13t] at hcoord
  refine hcoord.trans (hbound.trans ?_)
  calc C * ‖e‖ ^ 2 ≤ max C 0 * ‖e‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    _ ≤ max C 0 * ξb ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hen 2) (le_max_right _ _)

/-! ### Proposition 2.7: a rule on smoothed inflation (§2.3, p. 95, A.7)

Exact cashless perfect-foresight model: (1.21) and the nonlinear rule `i_t = φ(Π̄_t; ν_t)` on the
smoothed (geometric moving-average) inflation measure (2.8),
`log Π̄_t = δ log Π̄_{t−1} + (1 − δ) log Π_t` with `Π̄_{−1}` given. In `x_t = log Π̄_t` it is
`(1 − δ)(ĵ(x_t, ν_t) − r̂_t) + δ x_t − x_{t+1} = 0`, the nonlinear form of (A.20) (this is in
LocalIFT's class `g(x_t, ν_t) − x_{t+1} = w_t`; we use the local version of the theory). -/

/-- Woodford (2003), (2.8), p. 94, recursive form p. 95: the log smoothed inflation measure,
`π̄_t = δ π̄_{t−1} + (1 − δ) log Π_t`, with `π̄_{−1}` given. -/
noncomputable def smoothLog (dl pbm1 : ℝ) (Infl : ℕ → ℝ) : ℕ → ℝ
  | 0 => dl * pbm1 + (1 - dl) * Real.log (Infl 0)
  | t + 1 => dl * smoothLog dl pbm1 Infl t + (1 - dl) * Real.log (Infl (t + 1))

/-- Woodford (2003), (1.21) and (2.9), pp. 72, 95, perfect foresight: an equilibrium under a rule on
smoothed inflation: positive `Π` and `i` with `1 + i_t = u_c(t)/(β u_c(t+1)) Π_{t+1}` and
`i_t = φ(Π̄_t; ν_t)`. -/
def SmoothEq (β dl : ℝ) (φ : ℝ × ℝ → ℝ) (uc ν : ℕ → ℝ) (pbm1 : ℝ) (Infl i : ℕ → ℝ) : Prop :=
  (∀ t, 0 < Infl t) ∧ (∀ t, 1 + i t = uc t / (β * uc (t + 1)) * Infl (t + 1)) ∧
    ∀ t, i t = φ (Real.exp (smoothLog dl pbm1 Infl t), ν t)

/-- Woodford (2003), (A.20), p. 640, exact form: the period condition in
`(π̄_t, π̄_{t+1}, (ν_t, r̂_t))`. -/
noncomputable def F7 (β dl : ℝ) (φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ × (ℝ × ℝ)) : ℝ :=
  (1 - dl) * (LocalIFT.logRule β φ (p.1, p.2.2.1) - p.2.2.2) + dl * p.1 - p.2.1

/-- Woodford (2003), (A.20), p. 640: the steady state solves the period condition. -/
theorem F7_zero {β dl : ℝ} {φ : ℝ × ℝ → ℝ} (hss : 1 + φ (1, 0) = β⁻¹) : F7 β dl φ 0 = 0 := by
  have h := LocalIFT.logRule_zero (β := β) hss
  have h' : LocalIFT.logRule β φ (0, 0) = 0 := h
  simp [F7, h']

/-- Woodford (2003), (A.20), p. 640: the period condition is `Cⁿ` near the steady state. -/
theorem contDiffAt_F7 {β dl : ℝ} {φ : ℝ × ℝ → ℝ} {n : ℕ} (hβ : 0 < β)
    (hss : 1 + φ (1, 0) = β⁻¹) (hφ : ContDiffAt ℝ n φ (1, 0)) :
    ContDiffAt ℝ n (F7 β dl φ) 0 := by
  have hR := contDiffAt_logRule hβ hss hφ
  let A : ℝ × ℝ × (ℝ × ℝ) →L[ℝ] ℝ × ℝ := (ContinuousLinearMap.fst ℝ ℝ _).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((ContinuousLinearMap.snd ℝ ℝ _).comp
      (ContinuousLinearMap.snd ℝ ℝ _)))
  have hRA : ContDiffAt ℝ n (LocalIFT.logRule β φ) (A 0) := by rw [map_zero]; exact hR
  have hc := hRA.comp (0 : ℝ × ℝ × (ℝ × ℝ)) A.contDiff.contDiffAt
  have hr : ContDiffAt ℝ n (fun p : ℝ × ℝ × (ℝ × ℝ) => p.2.2.2) 0 := by fun_prop
  have hx : ContDiffAt ℝ n (fun p : ℝ × ℝ × (ℝ × ℝ) => dl * p.1) 0 := by fun_prop
  have hx' : ContDiffAt ℝ n (fun p : ℝ × ℝ × (ℝ × ℝ) => p.2.1) 0 := by fun_prop
  have h := (((contDiffAt_const (c := 1 - dl)).mul (hc.sub hr)).add hx).sub hx'
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => rfl)

/-- Woodford (2003), (A.20), p. 640, **exact derivative**: `DF(x, x', (ν, r)) =
(1 − δ)(Φ_π x + c_ν ν − r) + δ x − x'`. -/
theorem hasFDerivAt_F7 {β dl : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β) (hss : 1 + φ (1, 0) = β⁻¹)
    (hφ : ContDiffAt ℝ 1 φ (1, 0)) :
    ∃ F' : ℝ × ℝ × (ℝ × ℝ) →L[ℝ] ℝ, HasFDerivAt (F7 β dl φ) F' 0 ∧
      ∀ x x' ν r : ℝ, F' (x, x', (ν, r)) = (1 - dl) * (LocalIFT.elast β φ * x +
        LocalIFT.elastNu β φ * ν - r) + dl * x - x' := by
  have hRd := ((contDiffAt_logRule hβ hss hφ).differentiableAt one_ne_zero).hasFDerivAt
  let A : ℝ × ℝ × (ℝ × ℝ) →L[ℝ] ℝ × ℝ := (ContinuousLinearMap.fst ℝ ℝ _).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((ContinuousLinearMap.snd ℝ ℝ _).comp
      (ContinuousLinearMap.snd ℝ ℝ _)))
  let Rr : ℝ × ℝ × (ℝ × ℝ) →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    ((ContinuousLinearMap.snd ℝ ℝ _).comp (ContinuousLinearMap.snd ℝ ℝ _))
  let X1 : ℝ × ℝ × (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ _
  let X2 : ℝ × ℝ × (ℝ × ℝ) →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ _).comp
    (ContinuousLinearMap.snd ℝ ℝ _)
  have hRA : HasFDerivAt (LocalIFT.logRule β φ) (fderiv ℝ (LocalIFT.logRule β φ) 0) (A 0) := by
    rw [map_zero]; exact hRd
  have h := ((((hRA.comp 0 A.hasFDerivAt).sub (Rr.hasFDerivAt (x := 0))).const_mul (1 - dl)).add
    ((X1.hasFDerivAt (x := 0)).const_mul dl)).sub (X2.hasFDerivAt (x := 0))
  refine ⟨_, h, fun x x' ν r => ?_⟩
  simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  change (1 - dl) * (fderiv ℝ (LocalIFT.logRule β φ) 0 (x, ν) - r) + dl * x - x' = _
  rw [fderiv_logRule_apply hβ hss (hφ.differentiableAt one_ne_zero)]

/-- Woodford (2003), (A.20), p. 640: the slopes `a = δ + (1 − δ)Φ_π`, `b = −1`,
`c(ν, r) = (1 − δ)(c_ν ν − r)`. -/
theorem slopes_F7 {β dl : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β) (hss : 1 + φ (1, 0) = β⁻¹)
    (hφ : ContDiffAt ℝ 1 φ (1, 0)) :
    slopeA (F7 β dl φ) = dl + (1 - dl) * LocalIFT.elast β φ ∧ slopeB (F7 β dl φ) = -1 ∧
      ∀ ν r : ℝ, slopeC (F7 β dl φ) (ν, r) = (1 - dl) * (LocalIFT.elastNu β φ * ν - r) := by
  obtain ⟨F', hF', hv⟩ := hasFDerivAt_F7 (dl := dl) hβ hss hφ
  obtain ⟨ha, hb, hc⟩ := slopes_of_hasFDerivAt hF'
  refine ⟨?_, ?_, fun ν r => by rw [hc, hv]; ring⟩
  · rw [ha]
    change F' (1, 0, ((0 : ℝ), (0 : ℝ))) = _
    rw [hv]
    ring
  · rw [hb]
    change F' (0, 1, ((0 : ℝ), (0 : ℝ))) = _
    rw [hv]
    ring

/-- Woodford (2003), A.7, p. 640: for `0 ≤ δ < 1` and `Φ_π ≥ 0`, `δ + (1 − δ)Φ_π > 1` iff
`Φ_π > 1` (the Taylor principle), and `< 1` iff `Φ_π < 1`. -/
theorem smooth_cond_iff {dl Φ : ℝ} (hdl0 : 0 ≤ dl) (hdl1 : dl < 1) (hΦ : 0 ≤ Φ) :
    (1 < |dl + (1 - dl) * Φ| ↔ 1 < Φ) ∧ (|dl + (1 - dl) * Φ| < 1 ↔ Φ < 1) := by
  have hpos : 0 ≤ dl + (1 - dl) * Φ := by nlinarith
  rw [abs_of_nonneg hpos]
  refine ⟨⟨fun h => ?_, fun h => by nlinarith⟩, ⟨fun h => ?_, fun h => by nlinarith⟩⟩
  · by_contra h'
    push Not at h'
    nlinarith
  · by_contra h'
    push Not at h'
    nlinarith

/-- Woodford (2003), (2.8), p. 95: the smoothed measure of the inflation path built from
`x`, `Π_0 = e^{(x_0 − δ π̄_{−1})/(1 − δ)}`, `Π_{t+1} = e^{(x_{t+1} − δ x_t)/(1 − δ)}`, is `x`. -/
noncomputable def inflOfSmooth (dl pbm1 : ℝ) (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => Real.exp ((x 0 - dl * pbm1) / (1 - dl))
  | t + 1 => Real.exp ((x (t + 1) - dl * x t) / (1 - dl))

/-- Woodford (2003), (2.8)/(2.11), p. 95: `smoothLog` of `inflOfSmooth x` is `x` (`δ < 1`). -/
theorem smoothLog_inflOfSmooth {dl pbm1 : ℝ} (hdl : dl < 1) (x : ℕ → ℝ) (t : ℕ) :
    smoothLog dl pbm1 (inflOfSmooth dl pbm1 x) t = x t := by
  have h1 : (1 - dl) ≠ 0 := by linarith
  induction t with
  | zero =>
    simp only [smoothLog, inflOfSmooth, Real.log_exp]
    field_simp
    ring
  | succ n ih =>
    simp only [smoothLog, inflOfSmooth, Real.log_exp, ih]
    field_simp
    ring

/-- Woodford (2003), (2.11), p. 95: inflation in terms of the smoothed measure,
`log Π_{t+1} = (π̄_{t+1} − δ π̄_t)/(1 − δ)`. -/
theorem log_infl_succ {dl pbm1 : ℝ} (hdl : dl < 1) (Infl : ℕ → ℝ) (t : ℕ) :
    Real.log (Infl (t + 1)) =
      (smoothLog dl pbm1 Infl (t + 1) - dl * smoothLog dl pbm1 Infl t) / (1 - dl) := by
  have h1 : (1 - dl) ≠ 0 := by linarith
  simp only [smoothLog]
  field_simp
  ring

/-- Woodford (2003), **Proposition 2.7**, p. 95 and A.7, pp. 639–640, **exact perfect-foresight
version** (determinacy half): with `0 ≤ δ < 1`, `φ` `C¹` near `(1, 0)`,
`1 + φ(1; 0) = β⁻¹` and `|δ + (1 − δ)Φ_π| > 1` (for `Φ_π ≥ 0`: `Φ_π > 1`), there are `ε, δ₀ > 0`
such that whenever `r̂_t` and `ν_t` stay within `δ₀` there is an equilibrium with smoothed
inflation `|log Π̄_t| ≤ ε`, and it is the only one in that neighbourhood. -/
theorem smooth_local_determinacy {β dl : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β) (hdl : dl < 1)
    (hss : 1 + φ (1, 0) = β⁻¹) (hφ : ContDiffAt ℝ 1 φ (1, 0))
    (hdet : 1 < |dl + (1 - dl) * LocalIFT.elast β φ|) :
    ∃ ε > 0, ∃ δ > 0, ∀ uc ν : ℕ → ℝ, ∀ pbm1 : ℝ, (∀ t, 0 < uc t) →
      (∀ t, |Real.log (uc t / uc (t + 1))| ≤ δ) → (∀ t, |ν t| ≤ δ) →
      (∃ Infl i : ℕ → ℝ, SmoothEq β dl φ uc ν pbm1 Infl i ∧
        ∀ t, |smoothLog dl pbm1 Infl t| ≤ ε) ∧
      ∀ Infl i Infl' i' : ℕ → ℝ, SmoothEq β dl φ uc ν pbm1 Infl i →
        SmoothEq β dl φ uc ν pbm1 Infl' i' → (∀ t, |smoothLog dl pbm1 Infl t| ≤ ε) →
        (∀ t, |smoothLog dl pbm1 Infl' t| ≤ ε) → Infl = Infl' ∧ i = i' := by
  have hRc := (contDiffAt_logRule hβ hss hφ).continuousAt
  have hc1 : ContinuousAt (fun q : ℝ × ℝ => 1 + φ (Real.exp q.1, q.2)) 0 :=
    continuousAt_const.add (hφ.continuousAt.comp_of_eq
      (f := fun q : ℝ × ℝ => ((Real.exp q.1, q.2) : ℝ × ℝ)) (by fun_prop) (by simp))
  have hp1 : 0 < (fun q : ℝ × ℝ => 1 + φ (Real.exp q.1, q.2)) 0 := by simp [hss, hβ]
  obtain ⟨ρ, hρ, hρP⟩ := Metric.eventually_nhds_iff.mp (hc1.eventually (lt_mem_nhds hp1))
  have hpos : ∀ x ν : ℝ, |x| < ρ → |ν| < ρ → 0 < 1 + φ (Real.exp x, ν) := by
    intro x ν hx hν
    have hd : dist ((x, ν) : ℝ × ℝ) 0 < ρ := by
      rw [dist_zero_right, Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_lt hx hν
    exact hρP hd
  obtain ⟨ha, hb, -⟩ := slopes_F7 (dl := dl) hβ hss hφ
  have hab : |slopeB (F7 β dl φ)| < |slopeA (F7 β dl φ)| := by
    rw [ha, hb, abs_neg, abs_one]
    exact hdet
  have hF1 : ContDiffAt ℝ 1 (F7 β dl φ) 0 := contDiffAt_F7 hβ hss hφ
  obtain ⟨ε, hε, hεη, δ, hδ, hδη, X, -, -, hX⟩ :=
    local_determinacy_loc hF1 (F7_zero hss) hab (half_pos hρ)
  refine ⟨ε / 2, half_pos hε, δ / 2, half_pos hδ, fun uc ν pbm1 huc hr hν => ?_⟩
  have hK : ∀ t, ‖((ν t, Real.log (uc t / uc (t + 1))) : ℝ × ℝ)‖ ≤ δ / 2 := fun t => by
    rw [norm_prod_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
    exact ⟨hν t, hr t⟩
  set e : Seq (ℝ × ℝ) := mkS (fun t => ((ν t, Real.log (uc t / uc (t + 1))) : ℝ × ℝ))
    ⟨δ / 2, hK⟩ with he
  have hen : ‖e‖ < δ := lt_of_le_of_lt (norm_seq_le (by positivity) hK) (half_lt_self hδ)
  obtain ⟨hXn, hXs, -, huniq⟩ := hX e hen
  have h1dl : (1 - dl) ≠ 0 := by linarith
  -- one date, in levels and in logs
  have hstep : ∀ (Infl : ℕ → ℝ) (i : ℕ → ℝ) (t : ℕ), 0 < Infl (t + 1) →
      0 < 1 + φ (Real.exp (smoothLog dl pbm1 Infl t), ν t) →
      (1 + φ (Real.exp (smoothLog dl pbm1 Infl t), ν t) =
        uc t / (β * uc (t + 1)) * Infl (t + 1) ↔
        F7 β dl φ (smoothLog dl pbm1 Infl t, smoothLog dl pbm1 Infl (t + 1),
          (ν t, Real.log (uc t / uc (t + 1)))) = 0) := by
    intro Infl _ t hI hp
    have hu : 0 < uc t / (β * uc (t + 1)) * Infl (t + 1) := by
      have := huc t; have := huc (t + 1); positivity
    have hlr : LocalIFT.logRule β φ (smoothLog dl pbm1 Infl t, ν t) =
        Real.log (β * (1 + φ (Real.exp (smoothLog dl pbm1 Infl t), ν t))) := by
      simp only [LocalIFT.logRule]
      rw [Real.log_mul hβ.ne' hp.ne']
      ring
    have hlI := log_infl_succ (pbm1 := pbm1) hdl Infl t
    simp only [F7]
    rw [hlr]
    constructor
    · intro h
      rw [h, show β * (uc t / (β * uc (t + 1)) * Infl (t + 1)) = uc t / uc (t + 1) * Infl (t + 1)
        by field_simp, Real.log_mul (by have := huc t; have := huc (t + 1); positivity) hI.ne']
      rw [hlI]
      field_simp
      ring
    · intro h
      have h' : Real.log (β * (1 + φ (Real.exp (smoothLog dl pbm1 Infl t), ν t))) =
          Real.log (β * (uc t / (β * uc (t + 1)) * Infl (t + 1))) := by
        rw [show β * (uc t / (β * uc (t + 1)) * Infl (t + 1)) = uc t / uc (t + 1) * Infl (t + 1)
          by field_simp, Real.log_mul (by have := huc t; have := huc (t + 1); positivity) hI.ne',
          hlI]
        have h2 : (1 - dl) * (Real.log (β * (1 + φ (Real.exp (smoothLog dl pbm1 Infl t), ν t))) -
            Real.log (uc t / uc (t + 1))) = smoothLog dl pbm1 Infl (t + 1) -
              dl * smoothLog dl pbm1 Infl t := by linarith
        field_simp
        linarith
      have := Real.log_injOn_pos (Set.mem_Ioi.mpr (mul_pos hβ hp))
        (Set.mem_Ioi.mpr (mul_pos hβ hu)) h'
      exact mul_left_cancel₀ hβ.ne' this
  have hclass : ∀ Infl i : ℕ → ℝ, SmoothEq β dl φ uc ν pbm1 Infl i →
      ∀ hb : (∀ t, |smoothLog dl pbm1 Infl t| ≤ ε / 2),
      mk (fun t => smoothLog dl pbm1 Infl t) ⟨ε / 2, hb⟩ = X e := by
    intro Infl i ⟨hP, hF, hi⟩ hb
    refine huniq _ (lt_of_le_of_lt (norm_le_of_abs_le (by positivity) hb) (half_lt_self hε))
      (fun t => ?_)
    have hp : 0 < 1 + φ (Real.exp (smoothLog dl pbm1 Infl t), ν t) := by
      rw [← hi t, hF t]
      have := huc t; have := huc (t + 1); have := hP (t + 1); positivity
    have h := hF t
    rw [hi t] at h
    exact (hstep Infl i t (hP (t + 1)) hp).mp h
  refine ⟨?_, ?_⟩
  · set x := X e with hx
    have hxt : ∀ t, |x t| < ε / 2 := fun t => lt_of_le_of_lt (abs_apply_le x t) hXn
    have hsm := smoothLog_inflOfSmooth (pbm1 := pbm1) hdl (fun t => x t)
    have hpx : ∀ t, 0 < 1 + φ (Real.exp (x t), ν t) := fun t =>
      hpos _ _ (by linarith [hxt t]) (by linarith [hν t])
    refine ⟨inflOfSmooth dl pbm1 (fun t => x t),
      fun t => φ (Real.exp (smoothLog dl pbm1 (inflOfSmooth dl pbm1 (fun t => x t)) t), ν t),
      ⟨fun t => ?_, fun t => ?_, fun t => rfl⟩, fun t => ?_⟩
    · cases t <;> exact Real.exp_pos _
    · have hI : 0 < inflOfSmooth dl pbm1 (fun t => x t) (t + 1) := Real.exp_pos _
      refine (hstep _ (fun _ => 0) t hI (by rw [hsm]; exact hpx t)).mpr ?_
      rw [hsm, hsm]
      exact hXs t
    · rw [hsm]
      exact (hxt t).le
  · intro Infl i Infl' i' hE hE' hb hb'
    have hb2 : ∀ t, |smoothLog dl pbm1 Infl t| ≤ ε / 2 := hb
    have hb2' : ∀ t, |smoothLog dl pbm1 Infl' t| ≤ ε / 2 := hb'
    have hS : ∀ t, smoothLog dl pbm1 Infl t = smoothLog dl pbm1 Infl' t := fun t =>
      congrArg (fun y : Linf => y t) ((hclass Infl i hE hb2).trans (hclass Infl' i' hE' hb2').symm)
    have hlog : ∀ t, Real.log (Infl t) = Real.log (Infl' t) := fun t => by
      cases t with
      | zero =>
        have h := hS 0
        simp only [smoothLog] at h
        have : (1 - dl) * Real.log (Infl 0) = (1 - dl) * Real.log (Infl' 0) := by linarith
        exact mul_left_cancel₀ h1dl this
      | succ t => rw [log_infl_succ hdl, log_infl_succ hdl, hS, hS]
    have hII : Infl = Infl' := funext fun t =>
      Real.log_injOn_pos (Set.mem_Ioi.mpr (hE.1 t)) (Set.mem_Ioi.mpr (hE'.1 t)) (hlog t)
    exact ⟨hII, funext fun t => by rw [hE.2.2 t, hE'.2.2 t, hII]⟩

/-- Woodford (2003), **Proposition 2.7**, p. 95 (book form): with `0 ≤ δ < 1` and `Φ_π ≥ 0`, the
exact model is locally determinate when `Φ_π > 1` (`smooth_local_determinacy`) — the condition of
`smooth_cond_iff` — and locally indeterminate when `Φ_π < 1` (`smooth_local_indeterminacy`). -/
theorem prop_2_7_cond {β dl : ℝ} {φ : ℝ × ℝ → ℝ} (hdl0 : 0 ≤ dl) (hdl1 : dl < 1)
    (hΦ : 0 ≤ LocalIFT.elast β φ) :
    (1 < |dl + (1 - dl) * LocalIFT.elast β φ| ↔ 1 < LocalIFT.elast β φ) ∧
      (|dl + (1 - dl) * LocalIFT.elast β φ| < 1 ↔ LocalIFT.elast β φ < 1) :=
  smooth_cond_iff hdl0 hdl1 hΦ

/-- Woodford (2003), Prop. 2.7, p. 95 (indeterminacy half), **exact perfect-foresight version**: if
`|δ + (1 − δ)Φ_π| < 1` (for `Φ_π ≥ 0`: `Φ_π < 1`), then with constant fundamentals and
`π̄_{−1} = 0`, every initial smoothed inflation `π̄_0 = c` with `|c| ≤ r` starts an exact
equilibrium within `ε` of the steady state; distinct `c` give distinct equilibria. -/
theorem smooth_local_indeterminacy {β dl : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β) (hdl : dl < 1)
    (hss : 1 + φ (1, 0) = β⁻¹) (hφ : ContDiffAt ℝ 1 φ (1, 0))
    (hind : |dl + (1 - dl) * LocalIFT.elast β φ| < 1) :
    ∀ ε > 0, ∃ r > 0, ∀ c : ℝ, |c| ≤ r → ∃ Infl i : ℕ → ℝ,
      SmoothEq β dl φ (fun _ => 1) (fun _ => 0) 0 Infl i ∧ smoothLog dl 0 Infl 0 = c ∧
        ∀ t, |smoothLog dl 0 Infl t| ≤ ε := by
  intro ε hε
  have hc1 : ContinuousAt (fun q : ℝ × ℝ => 1 + φ (Real.exp q.1, q.2)) 0 :=
    continuousAt_const.add (hφ.continuousAt.comp_of_eq
      (f := fun q : ℝ × ℝ => ((Real.exp q.1, q.2) : ℝ × ℝ)) (by fun_prop) (by simp))
  have hp1 : 0 < (fun q : ℝ × ℝ => 1 + φ (Real.exp q.1, q.2)) 0 := by simp [hss, hβ]
  obtain ⟨ρ, hρ, hρP⟩ := Metric.eventually_nhds_iff.mp (hc1.eventually (lt_mem_nhds hp1))
  have hpos : ∀ x : ℝ, |x| < ρ → 0 < 1 + φ (Real.exp x, 0) := by
    intro x hx
    have hd : dist ((x, 0) : ℝ × ℝ) 0 < ρ := by
      rw [dist_zero_right, Prod.norm_mk, Real.norm_eq_abs, norm_zero,
        max_eq_left (abs_nonneg _)]
      exact hx
    exact hρP hd
  obtain ⟨ha, hb, -⟩ := slopes_F7 (dl := dl) hβ hss hφ
  have hab : |slopeA (F7 β dl φ)| < |slopeB (F7 β dl φ)| := by
    rw [ha, hb, abs_neg, abs_one]
    exact hind
  have hF1 : ContDiffAt ℝ 1 (F7 β dl φ) 0 := contDiffAt_F7 hβ hss hφ
  set ε' := min ε (ρ / 2) with hε'
  obtain ⟨r, hr, hx⟩ := local_indeterminacy_loc hF1 (F7_zero hss) hab ε' (lt_min hε (half_pos hρ))
  refine ⟨r, hr, fun c hc => ?_⟩
  obtain ⟨x, hxs, hxn, hx0⟩ := hx c hc
  have hxt : ∀ t, |x t| ≤ ε' := fun t => (abs_apply_le x t).trans hxn
  have hsm := smoothLog_inflOfSmooth (pbm1 := 0) hdl (fun t => x t)
  have h1dl : (1 - dl) ≠ 0 := by linarith
  refine ⟨inflOfSmooth dl 0 (fun t => x t),
    fun t => φ (Real.exp (smoothLog dl 0 (inflOfSmooth dl 0 (fun t => x t)) t), 0),
    ⟨fun t => ?_, fun t => ?_, fun t => rfl⟩, by rw [hsm, hx0], fun t => ?_⟩
  · cases t <;> exact Real.exp_pos _
  · beta_reduce
    rw [hsm]
    have hp := hpos (x t) (by linarith [hxt t, min_le_right ε (ρ / 2)])
    have h := hxs t
    simp only [F7, lp.coeFn_zero, Pi.zero_apply, Prod.fst_zero, Prod.snd_zero, sub_zero] at h
    have hl : LocalIFT.logRule β φ (x t, 0) = Real.log (β * (1 + φ (Real.exp (x t), 0))) := by
      simp only [LocalIFT.logRule]
      rw [Real.log_mul hβ.ne' hp.ne']
      ring
    rw [hl] at h
    have hI : Real.log (inflOfSmooth dl 0 (fun t => x t) (t + 1)) =
        (x (t + 1) - dl * x t) / (1 - dl) := Real.log_exp _
    have h' : Real.log (β * (1 + φ (Real.exp (x t), 0))) =
        Real.log (β * (1 / (β * 1) * inflOfSmooth dl 0 (fun t => x t) (t + 1))) := by
      rw [show β * (1 / (β * 1) * inflOfSmooth dl 0 (fun t => x t) (t + 1)) =
        inflOfSmooth dl 0 (fun t => x t) (t + 1) by field_simp, hI]
      field_simp
      linarith
    have hIp : 0 < inflOfSmooth dl 0 (fun t => x t) (t + 1) := Real.exp_pos _
    have hIp' : 0 < β * (1 / (β * 1) * inflOfSmooth dl 0 (fun t => x t) (t + 1)) := by
      positivity
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr (mul_pos hβ hp)) (Set.mem_Ioi.mpr hIp') h'
    exact mul_left_cancel₀ hβ.ne' this
  · rw [hsm]
    exact (hxt t).trans (min_le_left _ _)

/-- Woodford (2003), A.7, p. 640: every equilibrium under a rule on smoothed inflation solves the
period condition `F7` date by date (no smallness needed: `1 + i > 0` follows from (1.21)). -/
theorem smooth_solves {β dl : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β) (hdl : dl < 1)
    {uc ν Infl i : ℕ → ℝ} {pbm1 : ℝ} (huc : ∀ t, 0 < uc t)
    (hE : SmoothEq β dl φ uc ν pbm1 Infl i) (t : ℕ) :
    F7 β dl φ (smoothLog dl pbm1 Infl t, smoothLog dl pbm1 Infl (t + 1),
      (ν t, Real.log (uc t / uc (t + 1)))) = 0 := by
  obtain ⟨hP, hF, hi⟩ := hE
  have hp : 0 < 1 + φ (Real.exp (smoothLog dl pbm1 Infl t), ν t) := by
    rw [← hi t, hF t]
    have := huc t; have := huc (t + 1); have := hP (t + 1); positivity
  have hlr : LocalIFT.logRule β φ (smoothLog dl pbm1 Infl t, ν t) =
      Real.log (β * (1 + φ (Real.exp (smoothLog dl pbm1 Infl t), ν t))) := by
    simp only [LocalIFT.logRule]
    rw [Real.log_mul hβ.ne' hp.ne']
    ring
  have hfl := fisher_log hβ (huc t) (huc (t + 1)) (hP (t + 1)) (hF t)
  rw [hi t] at hfl
  have hlI := log_infl_succ (pbm1 := pbm1) hdl Infl t
  have h1dl : (1 - dl) ≠ 0 := by linarith
  simp only [F7]
  rw [hlr, hfl, hlI]
  field_simp
  ring

/-- Woodford (2003), Prop. 2.7, p. 95 and App. A.3, p. 633 (`C¹` dependence): in sequence space the
exact smoothed-inflation path `π̄ = X(ν, r̂)` is `C¹` in the disturbances near zero, with
`X(0) = 0` and derivative the log-linear solution (2.10). -/
theorem smooth_smooth_dependence {β dl : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hss : 1 + φ (1, 0) = β⁻¹) (hφ : ContDiffAt ℝ 1 φ (1, 0))
    (hdet : 1 < |dl + (1 - dl) * LocalIFT.elast β φ|) :
    ∃ δ > 0, ∃ X : Seq (ℝ × ℝ) → Linf, X 0 = 0 ∧ HasFDerivAt X (linSol3 (F7 β dl φ)) 0 ∧
      ∀ e : Seq (ℝ × ℝ), ‖e‖ < δ → Solves (F7 β dl φ) e (X e) ∧ ContDiffAt ℝ 1 X e := by
  obtain ⟨ha, hb, -⟩ := slopes_F7 (dl := dl) hβ hss hφ
  have hab : |slopeB (F7 β dl φ)| < |slopeA (F7 β dl φ)| := by
    rw [ha, hb, abs_neg, abs_one]
    exact hdet
  obtain ⟨ε, hε, -, δ, hδ, -, X, hX0, hXd, hX⟩ :=
    local_determinacy_loc (contDiffAt_F7 hβ hss hφ) (F7_zero hss) hab one_pos
  exact ⟨δ, hδ, X, hX0, hXd, fun e he => ⟨(hX e he).2.1, (hX e he).2.2.1⟩⟩

/-- Woodford (2003), (2.10)/(A.18), p. 95, **the first-order term of the exact smoothed-inflation
equilibrium**: `π̄̂_t = (1 − δ) ∑_k (δ + (1 − δ)Φ_π)^{−(k+1)} (r̂_{t+k} − c_ν ν_{t+k})`
(with the book's normalisation `c_ν ν = ī`, fn. 15). -/
theorem linSol3_F7_apply {β dl : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hss : 1 + φ (1, 0) = β⁻¹) (hφ : ContDiffAt ℝ 1 φ (1, 0))
    (hdet : 1 < |dl + (1 - dl) * LocalIFT.elast β φ|) (e : Seq (ℝ × ℝ)) (t : ℕ) :
    linSol3 (F7 β dl φ) e t = (1 - dl) * ∑' k, ((dl + (1 - dl) * LocalIFT.elast β φ)⁻¹) ^ (k + 1) *
      ((e (t + k)).2 - LocalIFT.elastNu β φ * (e (t + k)).1) := by
  obtain ⟨ha, hb, hc⟩ := slopes_F7 (dl := dl) hβ hss hφ
  have hab : |slopeB (F7 β dl φ)| < |slopeA (F7 β dl φ)| := by
    rw [ha, hb, abs_neg, abs_one]
    exact hdet
  have hD : dl + (1 - dl) * LocalIFT.elast β φ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hdet
    linarith
  rw [linSol3_apply hab, ← neg_mul, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hv : e (t + k) = ((e (t + k)).1, (e (t + k)).2) := rfl
  rw [hv, hc, ha, hb, pow_succ]
  field_simp
  ring

/-- Woodford (2003), **Proposition 2.7**, p. 95 ("a log-linear approximation to the equilibrium
evolution of the smoothed inflation process is given by (2.10)"), exact perfect-foresight version
with the `C²` hypothesis of E18: every equilibrium near the steady state satisfies
`|log Π̄_t − (1 − δ) ∑_k (δ + (1 − δ)Φ_π)^{−(k+1)} (r̂_{t+k} − c_ν ν_{t+k})| ≤ C ξ²` when the
disturbances are bounded by `ξ < δ₀`. -/
theorem smooth_second_order {β dl : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β) (hdl : dl < 1)
    (hss : 1 + φ (1, 0) = β⁻¹) (hφ : ContDiffAt ℝ 2 φ (1, 0))
    (hdet : 1 < |dl + (1 - dl) * LocalIFT.elast β φ|) :
    ∃ ε > 0, ∃ δ > 0, ∃ C : ℝ, ∀ uc ν : ℕ → ℝ, ∀ pbm1 ξb : ℝ, (∀ t, 0 < uc t) → ξb < δ →
      (∀ t, |Real.log (uc t / uc (t + 1))| ≤ ξb) → (∀ t, |ν t| ≤ ξb) →
      ∀ Infl i : ℕ → ℝ, SmoothEq β dl φ uc ν pbm1 Infl i →
      (∀ t, |smoothLog dl pbm1 Infl t| ≤ ε) → ∀ t,
      |smoothLog dl pbm1 Infl t - (1 - dl) * ∑' k,
        ((dl + (1 - dl) * LocalIFT.elast β φ)⁻¹) ^ (k + 1) *
          (Real.log (uc (t + k) / uc (t + k + 1)) - LocalIFT.elastNu β φ * ν (t + k))| ≤
        C * ξb ^ 2 := by
  have hφ1 : ContDiffAt ℝ 1 φ (1, 0) := hφ.of_le (by norm_num)
  obtain ⟨ha, hb, -⟩ := slopes_F7 (dl := dl) hβ hss hφ1
  have hab : |slopeB (F7 β dl φ)| < |slopeA (F7 β dl φ)| := by
    rw [ha, hb, abs_neg, abs_one]
    exact hdet
  obtain ⟨ε, hε, -, δ, hδ, -, C, hC⟩ :=
    second_order_loc (contDiffAt_F7 hβ hss hφ) (F7_zero hss) hab one_pos
  refine ⟨ε / 2, half_pos hε, δ, hδ, max C 0,
    fun uc ν pbm1 ξb huc hξb hr hν Infl i hE hbd t => ?_⟩
  have hξ0 : 0 ≤ ξb := (abs_nonneg _).trans (hν 0)
  have hK : ∀ t, ‖((ν t, Real.log (uc t / uc (t + 1))) : ℝ × ℝ)‖ ≤ ξb := fun t => by
    rw [norm_prod_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
    exact ⟨hν t, hr t⟩
  set e : Seq (ℝ × ℝ) := mkS (fun t => ((ν t, Real.log (uc t / uc (t + 1))) : ℝ × ℝ))
    ⟨ξb, hK⟩ with he
  have hen : ‖e‖ ≤ ξb := norm_seq_le hξ0 hK
  have hsol : Solves (F7 β dl φ) e (mk (fun t => smoothLog dl pbm1 Infl t) ⟨ε / 2, hbd⟩) :=
    fun s => smooth_solves hβ hdl huc hE s
  have hbound := hC e (lt_of_le_of_lt hen hξb) _
    (lt_of_le_of_lt (norm_le_of_abs_le (by positivity) hbd) (half_lt_self hε)) hsol
  have hcoord := abs_apply_le (mk (fun t => smoothLog dl pbm1 Infl t) ⟨ε / 2, hbd⟩ -
    linSol3 (F7 β dl φ) e) t
  simp only [lp.coeFn_sub, Pi.sub_apply, mk_apply] at hcoord
  rw [linSol3_F7_apply hβ hss hφ1 hdet] at hcoord
  simp only [he, mkS_apply] at hcoord
  refine hcoord.trans (hbound.trans ?_)
  calc C * ‖e‖ ^ 2 ≤ max C 0 * ‖e‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    _ ≤ max C 0 * ξb ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hen 2) (le_max_right _ _)

/-! ### Transversality: `LocalIFT.TVC` is (1.24) under perfect foresight -/

/-- Woodford (2003), eq. (1.24), p. 72: **the perfect-foresight transversality condition
`LocalIFT.TVC` is exactly `Equilibrium.TVCDebt` for the perfect-foresight expectation system**
(processes on the one-point state space, `E_t` the identity); the condition is the same at every
date `t`, so the date quantifier of `TVCDebt` is vacuous. -/
theorem tvc_iff_tvcDebt (β : ℝ) (uc D P : ℕ → ℝ) :
    LocalIFT.TVC β uc D P ↔
      Equilibrium.TVCDebt perfectForesight β (fun T _ => uc T) (fun T _ => P T)
        (fun T _ => D T) := by
  have e : (fun T => β ^ T * uc T * D T / P T) =
      fun T => β ^ T * perfectForesight.E 0 (fun _ : Unit => uc T * D T / P T) () := by
    funext T
    change β ^ T * uc T * D T / P T = β ^ T * (uc T * D T / P T)
    ring
  constructor
  · intro h t ω
    have e' : (fun T => β ^ T * perfectForesight.E t
        (fun ω' => (fun T (_ : Unit) => uc T) T ω' * (fun T (_ : Unit) => D T) T ω' /
          (fun T (_ : Unit) => P T) T ω') ω) = fun T => β ^ T * uc T * D T / P T := by
      funext T
      change β ^ T * (uc T * D T / P T) = β ^ T * uc T * D T / P T
      ring
    rw [e']
    exact h
  · intro h
    have h0 := h 0 ()
    have e' : (fun T => β ^ T * perfectForesight.E 0
        (fun ω' => (fun T (_ : Unit) => uc T) T ω' * (fun T (_ : Unit) => D T) T ω' /
          (fun T (_ : Unit) => P T) T ω') ()) = fun T => β ^ T * uc T * D T / P T := by
      funext T
      change β ^ T * (uc T * D T / P T) = β ^ T * uc T * D T / P T
      ring
    rw [e'] at h0
    exact h0

/-- Woodford (2003), **Proposition 2.8**, p. 96 (book form): for `φ_π > 0` the exact-model
condition `|φ_π + ρ| > 1` of `inertial_local_determinacy` is (2.13) `φ_π + ρ > 1`, and the
condition `|φ_π + ρ| < 1` of `inertial_local_indeterminacy` is `φ_π + ρ < 1` (for `ρ ≥ 0`). -/
theorem prop_2_8_cond {φπ ρ : ℝ} (hφ : 0 < φπ) (hρ : 0 ≤ ρ) :
    (1 < |φπ + ρ| ↔ 1 < φπ + ρ) ∧ (|φπ + ρ| < 1 ↔ φπ + ρ < 1) := by
  rw [abs_of_pos (by linarith)]
  exact ⟨Iff.rfl, Iff.rfl⟩

end Woodford.PriceLevelDetermination.Nonlinear
