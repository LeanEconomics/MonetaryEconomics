/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.CostPush
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import StabilizationWelfare.ForwardSolution
import StabilizationWelfare.Sequences
import StabilizationWelfare.Moments

/-!
# The case of larger distortions

Woodford (2003), *Interest and Prices*, Chapter 6, §5, pp. 455–463 (no small-`Φ_y`
assumption), with Benigno and Woodford (2003) for (5.4).

Following the survey's Layer A, every second-order statement is an EXACT identity: Taylor
polynomials are evaluated at exact level deviations (`eˣ − 1 = x + x²/2 + r₃(x)`), "t.i.p." is an
explicit function of the disturbances and initial conditions, and "O(3)" is an explicit remainder
whose weighted degree is at least three, proved by a scaling lemma (rescaling the first-order
variables by `s`, the cross-sectional variance by `s²` and the atoms `r₃`, `rlog`, `r_C` by `s³`
multiplies it by `s³`); the atoms themselves are cubic (`ExpLogCES.abs_expRem_le`,
`ExpLogCES.abs_rlog_le`; `r₃ = ExpLogCES.expRem`). Discounted
sums are genuine `tsum`s of `E_0`-expectations of bounded processes, for an arbitrary
`ExpectationSystem`.

## Main results

* (5.1): `eq51_exact` (the period utility, all `Φ_y` terms kept, remainder `R51` with
  `R51_scaling`, `R51_isBigO`). Survey error 17 CONFIRMED: the printed linear term has the wrong
  sign (`quad51Printed_sub`, `eq51_printed_sign_wrong`, and `eq51_printed_false`: the printed
  form differs from the exact one by a first-order term, so it is not `t.i.p. + O(3)`).
* The small-`Φ_y` substitutions and the reduction of (5.1) to (2.10): `small_phi_coeff`,
  `small_phi_linear`, `quad51_small_phi`, `smallPhiRem_scaling`.
* Calvo dispersion (for Prop. 6.14): the moment identity (E.8) is `Moments.mix_var_meanChange`,
  (2.12) is `Moments.crossVar_demand`, the discounted recursion `Sequences.dispersion_tsum`;
  here `pib_sq_scaling`. The Taylor polynomials `ũ`, `ṽ` of (E.2)–(E.3) and their remainders
  are Proposition 6.1's (`Prop61.uTaylor_eq_of_coeffs`, `Prop61.vTaylor_eq_of_coeffs`).
* Proposition 6.14, (5.2)–(5.3): `prop614` (with `λ_yy = lamYY`, `γ_t = gamT`, `Ω = OmegaW > 0`,
  `OmegaW_pos`); the completed square with `g* > 0`: `loss614_square`, `lamYY_pos_iff`,
  `lamYY_pos_of_sigma_ge_one`, `gstar_pos`, `gstar_strictMonoOn` (increasing in `Φ_y`),
  `Ytil_linear`.
* Assumption 6.2: `uIso`, `vIso`, `fIso`, `hasDerivAt_uIso`, `uc_elasticity_iso`
  (`σ⁻¹ = σ̃/s_C`), `fIso_inverse`, `vtilde_iso`, `omega_iso` (`ω = φ_h(1+ν) − 1`), and the EXACT
  log forms of the Calvo cost and revenue terms `log_k_iso`, `log_f_iso`, `consumption_ratio`.
* (5.4) DERIVED IN FULL from the exact Calvo model (the book does not prove it):
  the Calvo conditions in log deviations (`PriceIndexEq`, `ResetPriceEq`, `RecEq`, obtained from
  levels in `priceIndex_of_levels`, `resetPrice_of_levels`, `recEq_of_levels`; bundled with the
  isoelastic forms in `CalvoModel.CalvoAS`); the one-period second-order AS relation
  `second_order_AS`
  (`V_t = κ̃(k̂−f̂)(1+(k̂+f̂)/2) + (βθ(1+ω)/2)E_tπ²_{t+1} + βE_tV_{t+1} + ρ_t`, from
  the algebraic identities `xr_eq_of_priceIndex`, `next_identity`, `now_identity`; remainder
  scaling `nowA_scaling`, `restA_scaling`, `E_scaling`); the expansion in output and
  disturbances `as_expand` (`μ_y = muY`, `δ = deltaA`, `rho2A_scaling`); and the forward
  integration `eq54` (with `forward_real`), giving (5.4) with `μ_π = θ(1+ω)`.
* The Calvo conditions themselves DERIVED from the Calvo model (`calvoAS_of_primitives`): the
  Chapter 3 reset problem is restated (`resetObjective`, `resetFOC`, `hasDerivAt_resetObjective`,
  `foc_of_isLocalMax`, with `hasDerivAt_E_of_remainder`, `remainder_le_of_lipschitz_deriv`,
  `hasDerivAt_E`, `hasDerivAt_tsum_E`); under Assumption 6.2 (`profIso`, `hasDerivAt_profIso`,
  `sdf`, `sdf_dprof_eq`) its first-order condition is `(θ−1)[−D₁F_t + D₂K_t]`
  (`resetFOC_iso`), giving `K_t = x_t^{1+ωθ}F_t` (`resetPrice_of_foc`,
  `resetPrice_of_isLocalMax`, `resetPriceEq_of_foc`); the infinite-sum definitions of `F`, `K`
  (`growth`, `fwdSum`) satisfy the recursions by the tower property (`fwdSum_rec`,
  `recEq_of_fwdSum`; pull-out property assumed, as it is not implied by the axioms).
  `eq54_of_primitives` gives (5.4) from these primitives in a single statement.
* Proposition 6.15, (5.5)–(5.8): `prop615`, from (5.1), the Calvo dispersion law and the
  derived (5.4). The printed coefficients are VERIFIED: `lamTilde_eq` ((5.7)), `ystar_eq`
  ((5.8), via `N_eq`, `lamTilde_eq_M`, `omega1_eq`, `omega2_eq`, `omega3_eq`); `Ω̃ > 0`
  (`OmegaTilde_pos`); (5.9) `loss615_gap`.
* (5.10) and the coefficients: `lamTilde_pos_iff`, `Mden_pos_iff`, `cond510_eventually_phi`,
  `cond510_eventually_sC`, `omega1_ge_one`, `omega1_gt_one_iff` (the book's "`Ḡ > 0` gives
  `ω₁ > 1`" needs `Φ_y > 0`), `omega2_pos`, `omega3_pos`, `phi_zero_case`, `sC_one_case`.
* (5.11): `costPush511`, `costPush511_eq`, `as_gap_511` (the AS relation in the welfare-relevant
  gap), `costPush511_phi_zero` (reduces to (4.39)), `costPush511_sC_one`.

Footnote 73 is reflected in `YstarA`: cost-side wedges `μ̂ʷ` (wage markups, wage-income taxes,
American-style sales taxes) enter with `ω₃`; a revenue-side (VAT-style) wedge `τ̂` enters with
`−1/M` instead. The claim that the optimal long-run inflation rate is zero for any `Φ_y`
(pp. 460, 462–463) belongs to Chapter 7 and is out of scope.
-/

namespace Woodford.StabilizationWelfare.LargeDistortions

open Filter Topology Asymptotics
open Sequences
open ExpLogCES (crossMean crossVar crossVar_mul expRem exp_sub_one_eq abs_expRem_le rlog
  abs_rlog_le)
open Moments (calvoKappa calvoXi calvoKappa_eq crossVar_demand)
open OneParamTaylor (not_isBigO_linear isBigO_cube_of_scaling)
open Prop61 (uTaylor vTaylor Ru RuQ Ru_scale Rv RvQ Rv_scale)

/-! ### (5.1): the period utility without dropping `Φ_y` (Layer A) -/

/-- The weight-three remainder created by the CES aggregation (E.5)
`E_i ŷ = Ŷ − ½(1 − θ⁻¹) var_i ŷ + r_C`. -/
noncomputable def Rint (θ ω q Y V rC : ℝ) : ℝ :=
  rC + (1 + ω) / 2 * ((rC - (1 - θ⁻¹) / 2 * V) ^ 2 + 2 * Y * (rC - (1 - θ⁻¹) / 2 * V))
    - ω * q * (rC - (1 - θ⁻¹) / 2 * V)

/-- Woodford (2003), (5.1): the complete weight-three remainder (divided by `Ȳu_c`). -/
noncomputable def R51 (σ ω θ Φ g q Y V rY rC Rvbar : ℝ) : ℝ :=
  Ru σ g Y rY - (1 - Φ) * (Rvbar + Rint θ ω q Y V rC)

/-- Woodford (2003), (5.1), p. 455: the quadratic part of the period utility (divided by
`−Ȳu_c/2`) with the CORRECTED sign of the linear term,
`[σ⁻¹ + ω − Φ_y(1+ω)]Ŷ² − 2[Φ_y + σ⁻¹g + (1−Φ_y)ωq]Ŷ + (1−Φ_y)(θ⁻¹+ω) var_i ŷ`. -/
noncomputable def quad51 (σ ω θ Φ g q Y V : ℝ) : ℝ :=
  (σ + ω - Φ * (1 + ω)) * Y ^ 2 - 2 * (Φ + σ * g + (1 - Φ) * ω * q) * Y
    + (1 - Φ) * (θ⁻¹ + ω) * V

/-- Woodford (2003), (5.1) as PRINTED (PDF p. 455): the linear term has a `+` sign. -/
noncomputable def quad51Printed (σ ω θ Φ g q Y V : ℝ) : ℝ :=
  (σ + ω - Φ * (1 + ω)) * Y ^ 2 + 2 * (Φ + σ * g + (1 - Φ) * ω * q) * Y
    + (1 - Φ) * (θ⁻¹ + ω) * V

/-- Woodford (2003), eq. (5.1), p. 455, as an EXACT identity (Layer A) without dropping any
`Φ_y` term: the period utility `ũ(Y) − ∫ṽ(y(i))di`, with both Taylor polynomials evaluated at
the exact level deviations `Ȳ(eˣ − 1) = Ȳ(x + x²/2 + r₃(x))`, the steady-state relation
`v_y = (1 − Φ_y)u_c` ((2.7)–(2.8)), and the CES relation (E.5)
`E_i ŷ = Ŷ − ½(1 − θ⁻¹) var_i ŷ + r_C`, equals
`−(Ȳu_c/2) quad51 + t.i.p. + Ȳu_c R51`, where `t.i.p.` depends only on the disturbances and
`R51` is of weight at least three (`R51_scaling`). The linear term is `−2[...]Ŷ`. -/
theorem eq51_exact {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∑ i, w i = 1)
    {Ybar uc ucc ucxi vy vyy vyxi σ ω θ Φ g q : ℝ}
    (hucc : ucc = -(σ * uc / Ybar)) (hucxi : ucxi = σ * uc * g) (hvy : vy = (1 - Φ) * uc)
    (hvyy : vyy = ω * vy / Ybar) (hvyxi : vyxi = -(ω * vy * q))
    (ubar uxi uxixi vbar vxi vxixi Y rY rC : ℝ) (yh ry : ι → ℝ)
    (hC : crossMean w yh = Y - (1 - θ⁻¹) / 2 * crossVar w yh + rC) :
    uTaylor ubar uc ucc uxi ucxi uxixi (Ybar * (Y + Y ^ 2 / 2 + rY)) -
        ∑ i, w i * vTaylor vbar vy vyy vxi vyxi vxixi (Ybar * (yh i + yh i ^ 2 / 2 + ry i)) =
      -(Ybar * uc / 2) * quad51 σ ω θ Φ g q Y (crossVar w yh) +
        ((ubar + uxi + uxixi / 2) - (vbar + vxi + vxixi / 2)) +
        Ybar * uc *
          R51 σ ω θ Φ g q Y (crossVar w yh) rY rC (∑ i, w i * Rv 0 ω q (yh i) (ry i)) := by
  rw [Prop61.uTaylor_eq_of_coeffs hucc hucxi]
  have hv : ∀ i, w i * vTaylor vbar vy vyy vxi vyxi vxixi (Ybar * (yh i + yh i ^ 2 / 2 + ry i)) =
      (vbar + vxi + vxixi / 2) * w i + Ybar * vy * (w i * yh i) +
        Ybar * vy * ((1 + ω) / 2) * (w i * yh i ^ 2) - Ybar * vy * (ω * q) * (w i * yh i) +
        Ybar * vy * (w i * Rv 0 ω q (yh i) (ry i)) := by
    intro i
    rw [Prop61.vTaylor_eq_of_coeffs (Φ := 0) (uc := vy) (by ring) hvyy hvyxi]
    unfold Prop61.Tv
    ring
  rw [Finset.sum_congr rfl fun i _ => hv i]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hw, Moments.sum_sq_eq hw]
  have hm : ∑ i, w i * yh i = crossMean w yh := rfl
  rw [hm, hC, hvy]
  unfold quad51 R51 Rint Prop61.Tu
  ring

/-- Woodford (2003), (5.1), PDF p. 455 (survey error 17, CONFIRMED): the printed sign of the
linear term is wrong. The printed quadratic form differs from the correct one by
`4[Φ_y + σ⁻¹g + (1−Φ_y)ωq]Ŷ`, which is nonzero (e.g. `Φ_y = 1/2`, `g = q = 0`, `Ŷ = 1`), so the
printed (5.1) cannot equal the exact expansion `eq51_exact` (whose remainder is of third
order): at `Φ_y = 1/2, σ⁻¹ = ω = θ⁻¹ = 1, g = q = 0, var = 0` and `Ŷ = s`, the correct
quadratic form is `s² − s` and the printed one is `s² + s`, which differ by `2s`, a FIRST-order
amount. -/
theorem eq51_printed_sign_wrong :
    quad51Printed 1 1 1 (1 / 2) 0 0 1 0 - quad51 1 1 1 (1 / 2) 0 0 1 0 = 2 ∧
      ∀ s : ℝ, quad51Printed 1 1 1 (1 / 2) 0 0 s 0 - quad51 1 1 1 (1 / 2) 0 0 s 0 = 2 * s := by
  unfold quad51Printed quad51
  constructor
  · norm_num
  · intro s; norm_num; ring

/-- Woodford (2003), (5.1), PDF p. 455 (survey error 17): the PRINTED expansion is false. Along
the ray `Ŷ = s` with no disturbances (`g = q = 0`, so every t.i.p. is a constant `c`) and no
dispersion, at `Φ_y = 1/2`, `σ⁻¹ = ω = θ⁻¹ = 1`, the printed and the correct quadratic forms differ
by `2s`, which is not `c + O(s³)` for any constant `c`; since the correct form is exact up to a
remainder that is `O(s³)` (`eq51_exact`, `R51_isBigO`), the printed (5.1) cannot hold. -/
theorem eq51_printed_false (c : ℝ) :
    ¬ (fun s : ℝ => quad51Printed 1 1 1 (1 / 2) 0 0 s 0 - quad51 1 1 1 (1 / 2) 0 0 s 0 + c)
      =O[𝓝 0] fun s => s ^ 3 := by
  have h := not_isBigO_linear (a := 2) (by norm_num) c
  intro h'
  apply h
  refine h'.congr_left fun s => ?_
  rw [eq51_printed_sign_wrong.2 s]

/-- Woodford (2003), (5.1) printed vs correct, in general: the two quadratic forms differ by
exactly `4[Φ_y + σ⁻¹g + (1−Φ_y)ωq]Ŷ`, a term of FIRST order in `Ŷ` whenever `Φ_y ≠ 0`; so the
printed expression is not a valid second-order approximation unless that bracket vanishes. -/
theorem quad51Printed_sub (σ ω θ Φ g q Y V : ℝ) :
    quad51Printed σ ω θ Φ g q Y V - quad51 σ ω θ Φ g q Y V =
      4 * (Φ + σ * g + (1 - Φ) * ω * q) * Y := by
  unfold quad51Printed quad51; ring

/-- Woodford (2003), p. 455: the small-`Φ_y` substitution
`σ⁻¹ + ω − Φ_y(1+ω) = (σ⁻¹ + ω) + O(Φ_y)`: the difference is exactly `−Φ_y(1+ω)`. -/
theorem small_phi_coeff (σ ω Φ : ℝ) : (σ + ω - Φ * (1 + ω)) - (σ + ω) = -(Φ * (1 + ω)) := by
  ring

/-- Woodford (2003), p. 455: the small-`Φ_y` substitution
`Φ_y + σ⁻¹g + (1−Φ_y)ωq = (σ⁻¹+ω)(x* + Ŷⁿ) + O(‖Φ_y, ξ‖²)` with `x* = Φ_y/(σ⁻¹+ω)` and
`Ŷⁿ = (σ⁻¹g + ωq)/(σ⁻¹+ω)` ((E.6)): the difference is exactly `−Φ_y ω q`, of second order. -/
theorem small_phi_linear {σ ω : ℝ} (h : σ + ω ≠ 0) (Φ g q : ℝ) :
    (Φ + σ * g + (1 - Φ) * ω * q) - (σ + ω) * (Φ / (σ + ω) + (σ * g + ω * q) / (σ + ω)) =
      -(Φ * ω * q) := by
  field_simp; ring

/-- Woodford (2003), p. 455–456: with the two substitutions, (5.1) reduces to (2.10):
`quad51 = (σ⁻¹+ω)(Ŷ − Ŷⁿ − x*)² + (θ⁻¹+ω) var − t.i.p. − R_Φ`, where the t.i.p. is
`(σ⁻¹+ω)(Ŷⁿ + x*)²` and `R_Φ = Φ_y(1+ω)Ŷ² − 2Φ_yωqŶ + Φ_y(θ⁻¹+ω) var` has weight three when
`Φ_y` is an expansion parameter (`smallPhiRem_scaling`). -/
theorem quad51_small_phi {σ ω : ℝ} (h : σ + ω ≠ 0) (θ Φ g q Y V : ℝ) :
    quad51 σ ω θ Φ g q Y V =
      (σ + ω) * (Y - (σ * g + ω * q) / (σ + ω) - Φ / (σ + ω)) ^ 2 + (θ⁻¹ + ω) * V
        - (σ + ω) * ((σ * g + ω * q) / (σ + ω) + Φ / (σ + ω)) ^ 2
        - (Φ * (1 + ω) * Y ^ 2 - 2 * Φ * ω * q * Y + Φ * (θ⁻¹ + ω) * V) := by
  unfold quad51; field_simp; ring

/-- Woodford (2003), p. 455: the remainder of the small-`Φ_y` reduction has weight three
(`Φ_y, Ŷ, q` weight one, the variance weight two): exact scaling identity. -/
theorem smallPhiRem_scaling (ω θ Φ q Y V s : ℝ) :
    (s * Φ) * (1 + ω) * (s * Y) ^ 2 - 2 * (s * Φ) * ω * (s * q) * (s * Y) +
        (s * Φ) * (θ⁻¹ + ω) * (s ^ 2 * V) =
      s ^ 3 * (Φ * (1 + ω) * Y ^ 2 - 2 * Φ * ω * q * Y + Φ * (θ⁻¹ + ω) * V) := by
  ring

/-! #### Weighted degree of the (5.1) remainder: the scaling lemma -/

/-- The rescaled `R_int`. -/
noncomputable def RintQ (s θ ω q Y V rC : ℝ) : ℝ :=
  rC + (1 + ω) / 2 * (s * (s * rC - (1 - θ⁻¹) / 2 * V) ^ 2 + 2 * Y * (s * rC - (1 - θ⁻¹) / 2 * V))
    - ω * q * (s * rC - (1 - θ⁻¹) / 2 * V)

/-- Scaling lemma for `R_int`: weight three (`V` has weight two, `r_C` weight three). -/
theorem Rint_scaling (s θ ω q Y V rC : ℝ) :
    Rint θ ω (s * q) (s * Y) (s ^ 2 * V) (s ^ 3 * rC) = s ^ 3 * RintQ s θ ω q Y V rC := by
  unfold Rint RintQ; ring

/-- Woodford (2003), (5.1), "O(‖ŷ, ξ̃‖³)" made precise (Layer A scaling lemma): rescaling
`Ŷ, ŷ(i), g, q` by `s` and the atoms `r₃(Ŷ), r₃(ŷ(i)), r_C` by `s³` multiplies the remainder
`R51` by `s³` (the cross-sectional variance rescales by `s²`, `ExpLogCES.crossVar_mul`). -/
theorem R51_scaling {ι : Type*} [Fintype ι] (w : ι → ℝ) (s σ ω θ Φ g q Y rY rC : ℝ)
    (yh ry : ι → ℝ) :
    R51 σ ω θ Φ (s * g) (s * q) (s * Y) (crossVar w fun i => s * yh i) (s ^ 3 * rY) (s ^ 3 * rC)
        (∑ i, w i * Rv 0 ω (s * q) (s * yh i) (s ^ 3 * ry i)) =
      s ^ 3 * (RuQ σ g Y rY s - (1 - Φ) * ((∑ i, w i * RvQ 0 ω q (yh i) (ry i) s) +
        RintQ s θ ω q Y (crossVar w yh) rC)) := by
  rw [crossVar_mul]
  unfold R51
  rw [Ru_scale, Rint_scaling]
  have hRv : ∀ y r, Rv 0 ω (s * q) (s * y) (s ^ 3 * r) = s ^ 3 * RvQ 0 ω q y r s :=
    fun y r => by simpa only [mul_zero] using Rv_scale 0 ω q y r s
  simp only [hRv]
  rw [show (∑ i, w i * (s ^ 3 * RvQ 0 ω q (yh i) (ry i) s)) =
      s ^ 3 * ∑ i, w i * RvQ 0 ω q (yh i) (ry i) s by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
  ring

/-- Woodford (2003), (5.1): along a ray `(sŶ, sŷ(i), sg, sq)` with atoms `s³ r`, the remainder
is `O(s³)` (the analytic content of "O(‖ŷ, ξ̃‖³)"). -/
theorem R51_isBigO {ι : Type*} [Fintype ι] (w : ι → ℝ) (σ ω θ Φ g q Y rY rC : ℝ)
    (yh ry : ι → ℝ) :
    (fun s => R51 σ ω θ Φ (s * g) (s * q) (s * Y) (crossVar w fun i => s * yh i) (s ^ 3 * rY)
        (s ^ 3 * rC) (∑ i, w i * Rv 0 ω (s * q) (s * yh i) (s ^ 3 * ry i))) =O[𝓝 0]
      fun s => s ^ 3 := by
  refine isBigO_cube_of_scaling (fun s => R51_scaling w s σ ω θ Φ g q Y rY rC yh ry) ?_
  apply Continuous.continuousAt
  unfold RuQ RvQ RintQ
  fun_prop

/-! ### Discounted sums -/

/-- Woodford (2003), Prop. 6.3 (App. E.2): replacing `P̄_t − P̄_{t−1}` by `π_t` costs only a
weight-three term. With `e_t = (P̄_t − P̄_{t−1}) − π_t` (of weight two by the price-index
expansion `log P_t = P̄_t + ½(1−θ)Δ_t + O(3)`), `(π + e)² − π² = 2πe + e²`, and rescaling
`π ↦ sπ`, `e ↦ s²e` multiplies it by `s³`. -/
theorem pib_sq_scaling (p e s : ℝ) :
    ((s * p) + s ^ 2 * e) ^ 2 - (s * p) ^ 2 = s ^ 3 * (2 * p * e + s * e ^ 2) := by
  ring

/-! ### Expected discounted sums of processes -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Proposition 6.14 -/

/-- Woodford (2003), Prop. 6.14, p. 456: `λ_yy = (κ/θ)(ω+σ⁻¹−Φ_y(1+ω))/((1−Φ_y)(ω+σ⁻¹))`. -/
noncomputable def lamYY (κ θ Φ ω σ : ℝ) : ℝ :=
  κ / θ * (ω + σ - Φ * (1 + ω)) / ((1 - Φ) * (ω + σ))

/-- Woodford (2003), Prop. 6.14, p. 456:
`γ_t = (κ/θ)(Φ_y + σ⁻¹g_t + (1−Φ_y)ωq_t)/((1−Φ_y)(ω+σ⁻¹))`. -/
noncomputable def gamT (κ θ Φ ω σ g q : ℝ) : ℝ :=
  κ / θ * (Φ + σ * g + (1 - Φ) * ω * q) / ((1 - Φ) * (ω + σ))

/-- Woodford (2003), (5.2): the normalising constant
`Ω = (Ȳu_c/2)(1−Φ_y)θ(ω+σ⁻¹)/κ` (with `κ` from Chapter 3, this is
`(Ȳu_c/2)(1−Φ_y)(θ⁻¹+ω)θ² α/((1−α)(1−αβ))`, the weight on `∑βᵗπ²`). -/
noncomputable def OmegaW (Ybar uc κ θ Φ ω σ : ℝ) : ℝ :=
  Ybar * uc / 2 * ((1 - Φ) * θ * (ω + σ) / κ)

/-- Woodford (2003), (5.3), p. 456: the period loss `L_t = π_t² + λ_yy Ŷ_t² − 2γ_t Ŷ_t`. -/
noncomputable def loss614 (κ θ Φ ω σ : ℝ) (infl Y g q : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun w => infl t w ^ 2 + lamYY κ θ Φ ω σ * Y t w ^ 2 - 2 * gamT κ θ Φ ω σ (g t w) (q t w) * Y t w

/-- Woodford (2003), (5.2): `Ω > 0`. -/
theorem OmegaW_pos {Ybar uc α β θ ω σ Φ : ℝ} (hY : 0 < Ybar) (huc : 0 < uc) (hα0 : 0 < α)
    (hα1 : α < 1) (hβ1 : β < 1) (hθ : 0 < θ) (hω : 0 < ω) (hσ : 0 < σ)
    (hΦ : Φ < 1) : 0 < OmegaW Ybar uc (calvoKappa α β ω θ σ) θ Φ ω σ := by
  have hab : 0 < 1 - α * β := by nlinarith
  have hk : 0 < calvoKappa α β ω θ σ := by
    unfold calvoKappa
    have : 0 < 1 - α := by linarith
    positivity
  unfold OmegaW
  have : 0 < 1 - Φ := by linarith
  positivity

/-- Woodford (2003), Proposition 6.14, eqs. (5.2)–(5.3), p. 456 (no small-`Φ_y` assumption).
Hypotheses: the period utility satisfies (5.1) (`h51`, with remainder `R`; `eq51_exact` gives
`R = Ȳu_c R51`, of weight three), the dispersion of log output is `θ²` times that of log prices
(`hV`, eq. (2.12), `crossVar_demand`; `D t = Δ_{t−1}`), and price dispersion follows the exact
Calvo recursion (`hD`, (E.8) with `pib t = P̄_t − P̄_{t−1}`, `Moments.mix_var_meanChange`). Then the
expected discounted utility is `−Ω ∑βᵗ L_t + t.i.p. + R`, with `L_t = π_t² + λ_yy Ŷ_t² − 2γ_tŶ_t`;
the t.i.p. is `∑βᵗE_0(t.i.p._t) − Ω(1−α)E_0 Δ_{−1}` and the remainder is
`∑βᵗE_0 R_t − Ω ∑βᵗE_0(P̄-inflation² − π²)` (weight three, `pib_sq_scaling`). -/
theorem prop614 {α β θ ω σ Φ Ybar uc : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ : 0 < θ) (hω : 0 < ω) (hσ : 0 < σ) (hΦ : Φ < 1)
    {U Y infl g q V D pib tipU R : ℕ → Ω → ℝ}
    (hYb : BoundedProc Y) (hib : BoundedProc infl) (hgb : BoundedProc g) (hqb : BoundedProc q)
    (hDb : BoundedProc D) (hpb : BoundedProc pib) (htb : BoundedProc tipU)
    (hRb : BoundedProc R)
    (h51 : ∀ t, U t = (fun w => -(Ybar * uc / 2) *
        quad51 σ ω θ Φ (g t w) (q t w) (Y t w) (V t w)) + tipU t + R t)
    (hV : ∀ t, V t = θ ^ 2 • D (t + 1))
    (hD : ∀ t, D (t + 1) = α • D t + (α / (1 - α)) • pib t ^ 2) (w : Ω) :
    dsum 𝔼 β U w =
      -OmegaW Ybar uc (calvoKappa α β ω θ σ) θ Φ ω σ *
          dsum 𝔼 β (loss614 (calvoKappa α β ω θ σ) θ Φ ω σ infl Y g q) w +
        (dsum 𝔼 β tipU w -
          OmegaW Ybar uc (calvoKappa α β ω θ σ) θ Φ ω σ * (1 - α) * 𝔼.E 0 (D 0) w) +
        (dsum 𝔼 β R w - OmegaW Ybar uc (calvoKappa α β ω θ σ) θ Φ ω σ *
          (dsum 𝔼 β (fun t => pib t ^ 2) w - dsum 𝔼 β (fun t => infl t ^ 2) w)) := by
  have hβ : |β| < 1 := by rw [abs_lt]; constructor <;> linarith
  -- bounded building blocks
  have bY2 := bdd_sq hYb
  have bgY := bdd_mul hgb hYb
  have bqY := bdd_mul hqb hYb
  have bpi2 := bdd_sq hib
  have bpib2 := bdd_sq hpb
  -- sums
  have sY := hasSum_dsum 𝔼 hβ hYb w
  have sY2 := hasSum_dsum 𝔼 hβ bY2 w
  have sgY := hasSum_dsum 𝔼 hβ bgY w
  have sqY := hasSum_dsum 𝔼 hβ bqY w
  have spi2 := hasSum_dsum 𝔼 hβ bpi2 w
  have spib2 := hasSum_dsum 𝔼 hβ bpib2 w
  have stip := hasSum_dsum 𝔼 hβ htb w
  have sR := hasSum_dsum 𝔼 hβ hRb w
  -- the dispersion sum
  obtain ⟨MD, hMD⟩ := hDb
  obtain ⟨Mp, hMp⟩ := bpib2
  have hdrec : ∀ t, 𝔼.E 0 (D (t + 1)) w =
      α * 𝔼.E 0 (D t) w + α / (1 - α) * 𝔼.E 0 (pib t ^ 2) w := by
    intro t
    rw [hD t, map_add, map_smul, map_smul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul]
  have hdisp := dispersion_tsum hβ (fun t => abs_E0_le 𝔼 hMD w t)
    (fun t => abs_E0_le 𝔼 (X := fun t => pib t ^ 2) hMp w t) hdrec
  have sD : HasSum (fun t => β ^ t * 𝔼.E 0 (D (t + 1)) w)
      (∑' t, β ^ t * 𝔼.E 0 (D (t + 1)) w) :=
    (summable_geom_bdd hβ (fun t => abs_E0_le 𝔼 hMD w (t + 1))).hasSum
  -- E_0 of the period utility
  have hUt : ∀ t, 𝔼.E 0 (U t) w =
      -(Ybar * uc / 2) * ((σ + ω - Φ * (1 + ω)) * 𝔼.E 0 (Y t ^ 2) w
        - 2 * Φ * 𝔼.E 0 (Y t) w - 2 * σ * 𝔼.E 0 (g t * Y t) w
        - 2 * ((1 - Φ) * ω) * 𝔼.E 0 (q t * Y t) w
        + (1 - Φ) * (θ⁻¹ + ω) * θ ^ 2 * 𝔼.E 0 (D (t + 1)) w)
      + 𝔼.E 0 (tipU t) w + 𝔼.E 0 (R t) w := by
    intro t
    have hf : (fun w => -(Ybar * uc / 2) * quad51 σ ω θ Φ (g t w) (q t w) (Y t w) (V t w)) =
        (-(Ybar * uc / 2) * (σ + ω - Φ * (1 + ω))) • (Y t ^ 2)
        - (-(Ybar * uc / 2) * (2 * Φ)) • Y t - (-(Ybar * uc / 2) * (2 * σ)) • (g t * Y t)
        - (-(Ybar * uc / 2) * (2 * ((1 - Φ) * ω))) • (q t * Y t)
        + (-(Ybar * uc / 2) * ((1 - Φ) * (θ⁻¹ + ω) * θ ^ 2)) • D (t + 1) := by
      funext x
      simp only [quad51, hV t, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply,
        Pi.pow_apply, smul_eq_mul]
      ring
    rw [h51 t, hf]
    simp only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  -- E_0 of the loss
  have hLt : ∀ t, 𝔼.E 0 (loss614 (calvoKappa α β ω θ σ) θ Φ ω σ infl Y g q t) w =
      𝔼.E 0 (infl t ^ 2) w + lamYY (calvoKappa α β ω θ σ) θ Φ ω σ * 𝔼.E 0 (Y t ^ 2) w
        - 2 * (calvoKappa α β ω θ σ / θ / ((1 - Φ) * (ω + σ))) *
          (Φ * 𝔼.E 0 (Y t) w + σ * 𝔼.E 0 (g t * Y t) w + (1 - Φ) * ω * 𝔼.E 0 (q t * Y t) w) := by
    intro t
    have hf : loss614 (calvoKappa α β ω θ σ) θ Φ ω σ infl Y g q t =
        infl t ^ 2 + lamYY (calvoKappa α β ω θ σ) θ Φ ω σ • (Y t ^ 2)
        - (2 * (calvoKappa α β ω θ σ / θ / ((1 - Φ) * (ω + σ))) * Φ) • Y t
        - (2 * (calvoKappa α β ω θ σ / θ / ((1 - Φ) * (ω + σ))) * σ) • (g t * Y t)
        - (2 * (calvoKappa α β ω θ σ / θ / ((1 - Φ) * (ω + σ))) * ((1 - Φ) * ω)) • (q t * Y t) := by
      funext x
      simp only [loss614, gamT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply,
        Pi.pow_apply, smul_eq_mul]
      ring
    rw [hf]
    simp only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  -- assemble
  set κ := calvoKappa α β ω θ σ with hκ
  set Om := OmegaW Ybar uc κ θ Φ ω σ with hOm
  have hU : HasSum (fun t => β ^ t * 𝔼.E 0 (U t) w)
      (-(Ybar * uc / 2) * ((σ + ω - Φ * (1 + ω)) * dsum 𝔼 β (fun t => Y t ^ 2) w
        - 2 * Φ * dsum 𝔼 β Y w - 2 * σ * dsum 𝔼 β (fun t => g t * Y t) w
        - 2 * ((1 - Φ) * ω) * dsum 𝔼 β (fun t => q t * Y t) w
        + (1 - Φ) * (θ⁻¹ + ω) * θ ^ 2 * ∑' t, β ^ t * 𝔼.E 0 (D (t + 1)) w)
      + dsum 𝔼 β tipU w + dsum 𝔼 β R w) := by
    have := ((((((sY2.mul_left (σ + ω - Φ * (1 + ω))).sub (sY.mul_left (2 * Φ))).sub
      (sgY.mul_left (2 * σ))).sub (sqY.mul_left (2 * ((1 - Φ) * ω)))).add
      (sD.mul_left ((1 - Φ) * (θ⁻¹ + ω) * θ ^ 2))).mul_left (-(Ybar * uc / 2))).add stip
      |>.add sR
    convert this using 1
    funext t
    rw [hUt t]
    ring
  have hL : HasSum (fun t => β ^ t *
        𝔼.E 0 (loss614 κ θ Φ ω σ infl Y g q t) w)
      (dsum 𝔼 β (fun t => infl t ^ 2) w + lamYY κ θ Φ ω σ * dsum 𝔼 β (fun t => Y t ^ 2) w
        - 2 * (κ / θ / ((1 - Φ) * (ω + σ))) * (Φ * dsum 𝔼 β Y w
          + σ * dsum 𝔼 β (fun t => g t * Y t) w
          + (1 - Φ) * ω * dsum 𝔼 β (fun t => q t * Y t) w)) := by
    have := ((spi2.add (sY2.mul_left (lamYY κ θ Φ ω σ))).sub
      (((sY.mul_left Φ).add (sgY.mul_left σ)).add (sqY.mul_left ((1 - Φ) * ω))
        |>.mul_left (2 * (κ / θ / ((1 - Φ) * (ω + σ))))))
    convert this using 1
    funext t
    rw [hLt t]
    ring
  have eU : dsum 𝔼 β U w = _ := hU.tsum_eq
  have eL : dsum 𝔼 β (loss614 κ θ Φ ω σ infl Y g q) w = _ := hL.tsum_eq
  rw [eU, eL]
  -- the dispersion identity
  have hab : 1 - α * β ≠ 0 := by nlinarith
  have h1a : 1 - α ≠ 0 := by linarith
  have hD' : ∑' t, β ^ t * 𝔼.E 0 (D (t + 1)) w = (α * 𝔼.E 0 (D 0) w + α / (1 - α) *
      dsum 𝔼 β (fun t => pib t ^ 2) w) / (1 - α * β) := by
    rw [eq_div_iff hab, mul_comm]; exact hdisp
  rw [hD']
  rw [hOm, hκ]
  unfold OmegaW lamYY calvoKappa
  have h1Φ : 1 - Φ ≠ 0 := by linarith
  have hωσ : ω + σ ≠ 0 := by linarith
  have h1ωθ : 1 + ω * θ ≠ 0 := by nlinarith
  field_simp
  ring

/-! ### The loss (5.3) as a gap with a positive target when `λ_yy > 0` -/

/-- Woodford (2003), p. 456: the positive constant `g* = Φ_y/(ω + σ⁻¹ − Φ_y(1+ω))`. -/
noncomputable def gstar (Φ ω σ : ℝ) : ℝ := Φ / (ω + σ - Φ * (1 + ω))

/-- Woodford (2003), p. 456: the mean-zero exogenous term
`Ỹ_t = (σ⁻¹g_t + (1−Φ_y)ωq_t)/(ω + σ⁻¹ − Φ_y(1+ω))` (linear in the mean-zero disturbances). -/
noncomputable def Ytil (Φ ω σ g q : ℝ) : ℝ := (σ * g + (1 - Φ) * ω * q) / (ω + σ - Φ * (1 + ω))

/-- Woodford (2003), p. 456: when `λ_yy ≠ 0`, `L_t = π_t² + λ_yy(Ŷ_t − Ỹ_t − g*)² + t.i.p.`, the
t.i.p. being `−λ_yy(Ỹ_t + g*)²`. -/
theorem loss614_square {κ θ Φ ω σ : ℝ} (hθ : θ ≠ 0) (hΦ : 1 - Φ ≠ 0)
    (hc : ω + σ ≠ 0) (hden : ω + σ - Φ * (1 + ω) ≠ 0) (p Y g q : ℝ) :
    p ^ 2 + lamYY κ θ Φ ω σ * Y ^ 2 - 2 * gamT κ θ Φ ω σ g q * Y =
      p ^ 2 + lamYY κ θ Φ ω σ * (Y - Ytil Φ ω σ g q - gstar Φ ω σ) ^ 2 -
        lamYY κ θ Φ ω σ * (Ytil Φ ω σ g q + gstar Φ ω σ) ^ 2 := by
  unfold lamYY gamT Ytil gstar
  field_simp
  ring

/-- Woodford (2003), p. 456 ("except in the case of very large `Φ_y`"): for `κ, θ > 0`,
`Φ_y < 1` and `ω + σ⁻¹ > 0`, `λ_yy > 0` iff `Φ_y(1+ω) < ω + σ⁻¹`. -/
theorem lamYY_pos_iff {κ θ Φ ω σ : ℝ} (hκ : 0 < κ) (hθ : 0 < θ) (hΦ : Φ < 1)
    (hc : 0 < ω + σ) : 0 < lamYY κ θ Φ ω σ ↔ Φ * (1 + ω) < ω + σ := by
  unfold lamYY
  have hd : 0 < (1 - Φ) * (ω + σ) := mul_pos (by linarith) hc
  rw [div_pos_iff_of_pos_right hd, mul_pos_iff_of_pos_left (div_pos hκ hθ)]
  constructor <;> intro h <;> linarith

/-- Woodford (2003), p. 456: if `σ⁻¹ ≥ 1` then `λ_yy > 0` for EVERY `Φ_y ∈ [0, 1)`. -/
theorem lamYY_pos_of_sigma_ge_one {κ θ Φ ω σ : ℝ} (hκ : 0 < κ) (hθ : 0 < θ)
    (hΦ : Φ < 1) (hω : 0 < ω) (hσ : 1 ≤ σ) : 0 < lamYY κ θ Φ ω σ := by
  rw [lamYY_pos_iff hκ hθ hΦ (by linarith)]
  nlinarith

/-- Woodford (2003), p. 456: `g* > 0` for `Φ_y > 0` when `λ_yy > 0`. -/
theorem gstar_pos {Φ ω σ : ℝ} (hΦ : 0 < Φ) (h : Φ * (1 + ω) < ω + σ) : 0 < gstar Φ ω σ := by
  unfold gstar; exact div_pos hΦ (by linarith)

/-- Woodford (2003), p. 456: `g*` is increasing in `Φ_y` on the region where `λ_yy > 0`. -/
theorem gstar_strictMonoOn {ω σ : ℝ} (hc : 0 < ω + σ) :
    StrictMonoOn (fun Φ => gstar Φ ω σ) {Φ | Φ * (1 + ω) < ω + σ} := by
  intro a ha b hb hab
  simp only [Set.mem_ofPred_eq] at ha hb
  simp only [gstar]
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-! ### Assumption 6.2: isoelastic preferences and technology -/

/-- Woodford (2003), Assumption 6.2, p. 457: `u(C; ξ) = (1 − σ̃)⁻¹ C̄^σ̃ C^{1−σ̃}`. -/
noncomputable def uIso (σt Cbar C : ℝ) : ℝ := (1 - σt)⁻¹ * Cbar ^ σt * C ^ (1 - σt)

/-- Woodford (2003), Assumption 6.2, p. 457: `v(h; ξ) = λ h̄^{−ν} h^{1+ν}`. -/
noncomputable def vIso (lam hbar ν h : ℝ) : ℝ := lam * hbar ^ (-ν) * h ^ (1 + ν)

/-- Woodford (2003), Assumption 6.2, p. 457: `f(h) = h^{1/φ_h}`. -/
noncomputable def fIso (φh h : ℝ) : ℝ := h ^ (1 / φh)

/-- Woodford (2003), Assumption 6.2: the marginal utility `u_c = C̄^σ̃ C^{−σ̃}`. -/
theorem hasDerivAt_uIso {σt Cbar C : ℝ} (hσ : σt ≠ 1) (hC : 0 < C) :
    HasDerivAt (uIso σt Cbar) (Cbar ^ σt * C ^ (-σt)) C := by
  have h := (Real.hasDerivAt_rpow_const (p := 1 - σt) (Or.inl hC.ne')).const_mul
    ((1 - σt)⁻¹ * Cbar ^ σt)
  have h1 : (1 : ℝ) - σt ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ)
  refine h.congr_deriv ?_
  rw [show (1 : ℝ) - σt - 1 = -σt by ring]
  field_simp

/-- Woodford (2003), Assumption 6.2 and p. 458: the marginal utility `u_c(C) = C̄^σ̃ C^{−σ̃}` has
elasticity `−C u_cc/u_c = σ̃`; with `C̄ = s_C Ȳ` (no output dispersion in steady state) the
elasticity with respect to output is `σ⁻¹ = −Ȳ u_cc/u_c = σ̃/s_C`. -/
theorem uc_elasticity_iso {σt Cbar Ybar sC : ℝ} (hCbar : 0 < Cbar) (hY : 0 < Ybar)
    (hs : 0 < sC) :
    HasDerivAt (fun C => Cbar ^ σt * C ^ (-σt)) (Cbar ^ σt * (-σt * (sC * Ybar) ^ (-σt - 1)))
        (sC * Ybar) ∧
      -(Ybar * (Cbar ^ σt * (-σt * (sC * Ybar) ^ (-σt - 1))) /
        (Cbar ^ σt * (sC * Ybar) ^ (-σt))) = σt / sC := by
  have hC : 0 < sC * Ybar := mul_pos hs hY
  refine ⟨(Real.hasDerivAt_rpow_const (p := -σt) (Or.inl hC.ne')).const_mul _, ?_⟩
  rw [Real.rpow_sub_one hC.ne']
  have h1 : 0 < Cbar ^ σt := Real.rpow_pos_of_pos hCbar σt
  have h2 : 0 < (sC * Ybar) ^ (-σt) := Real.rpow_pos_of_pos hC (-σt)
  field_simp

/-- Woodford (2003), Assumption 6.2: inverting the production function, `f⁻¹(z) = z^{φ_h}`. -/
theorem fIso_inverse {φh z : ℝ} (hφ : φh ≠ 0) (hz : 0 ≤ z) : fIso φh (z ^ φh) = z := by
  unfold fIso
  rw [← Real.rpow_mul hz, mul_one_div_cancel hφ, Real.rpow_one]

/-- Woodford (2003), Assumption 6.2, p. 457: the disutility of supplying `y` with technology `A`,
`ṽ(y) = v(f⁻¹(y/A)) = λ h̄^{−ν} (y/A)^{φ_h(1+ν)}`. -/
theorem vtilde_iso {lam hbar ν φh y A : ℝ} (hy : 0 ≤ y) (hA : 0 ≤ A) :
    vIso lam hbar ν ((y / A) ^ φh) = lam * hbar ^ (-ν) * (y / A) ^ (φh * (1 + ν)) := by
  unfold vIso
  rw [← Real.rpow_mul (div_nonneg hy hA)]

/-- Woodford (2003), Assumption 6.2 and eq. (2.7): `ṽ_y(y) ∝ y^{φ_h(1+ν)−1}`, so the elasticity
of real marginal cost with respect to own output is `ω = y ṽ_yy/ṽ_y = φ_h(1+ν) − 1`. -/
theorem omega_iso {K e y : ℝ} (hK : K ≠ 0) (hy : 0 < y) :
    HasDerivAt (fun z => K * z ^ (e - 1)) (K * ((e - 1) * y ^ (e - 1 - 1))) y ∧
      y * (K * ((e - 1) * y ^ (e - 1 - 1))) / (K * y ^ (e - 1)) = e - 1 := by
  refine ⟨(Real.hasDerivAt_rpow_const (p := e - 1) (Or.inl hy.ne')).const_mul K, ?_⟩
  rw [Real.rpow_sub_one hy.ne' (e - 1)]
  have : 0 < y ^ (e - 1) := Real.rpow_pos_of_pos hy _
  field_simp

/-- Woodford (2003), Assumption 6.2 and Benigno–Woodford: the cost term of the Calvo
reset-price condition `k = (θ/(θ−1)) μ^w Y ṽ_y(Y)` with `ṽ_y(Y) = c h̄^{−ν} A^{−(1+ω)} Y^ω`
is EXACTLY log-linear: `log(k_t/k̄) = (1+ω) log(Y_t/Ȳ) + log(μ^w_t/μ̄^w)
− ν log(h̄_t/h̄) − (1+ω) log(A_t/Ā)`. (Writing `ωq_t = ν ĥ_t + (1+ω)â_t`, this is
`k̂_t = (1+ω)Ŷ_t − ωq_t + μ̂_t`, the hypothesis `costK` of `CalvoAS`.) -/
theorem log_k_iso {θ c ω μ μb Y Yb h hb A Ab ν : ℝ} (hθ : 0 < θ / (θ - 1)) (hc : 0 < c)
    (hμ : 0 < μ) (hμb : 0 < μb) (hY : 0 < Y) (hYb : 0 < Yb) (hh : 0 < h) (hhb : 0 < hb)
    (hA : 0 < A) (hAb : 0 < Ab) :
    Real.log ((θ / (θ - 1) * μ * Y * (c * h ^ (-ν) * A ^ (-(1 + ω)) * Y ^ ω)) /
        (θ / (θ - 1) * μb * Yb * (c * hb ^ (-ν) * Ab ^ (-(1 + ω)) * Yb ^ ω))) =
      (1 + ω) * Real.log (Y / Yb) + Real.log (μ / μb) - ν * Real.log (h / hb)
        - (1 + ω) * Real.log (A / Ab) := by
  have p1 := Real.rpow_pos_of_pos hh (-ν)
  have p2 := Real.rpow_pos_of_pos hA (-(1 + ω))
  have p3 := Real.rpow_pos_of_pos hY ω
  have p4 := Real.rpow_pos_of_pos hhb (-ν)
  have p5 := Real.rpow_pos_of_pos hAb (-(1 + ω))
  have p6 := Real.rpow_pos_of_pos hYb ω
  rw [Real.log_div (by positivity) (by positivity)]
  simp only [Real.log_mul, Real.log_rpow, hθ.ne', hc.ne', hμ.ne', hμb.ne', hY.ne', hYb.ne',
    p1.ne', p2.ne', p3.ne', p4.ne', p5.ne', p6.ne', ne_eq,
    not_false_eq_true, mul_ne_zero_iff, and_self, hY, hYb, hh, hhb, hA, hAb]
  rw [Real.log_div hY.ne' hYb.ne', Real.log_div hμ.ne' hμb.ne', Real.log_div hh.ne' hhb.ne',
    Real.log_div hA.ne' hAb.ne']
  ring

/-- Woodford (2003), Assumption 6.2 and Benigno–Woodford: the revenue term
`f = (1−τ) Y u_c(Y − G; C̄)` with `u_c = C̄^σ̃ (Y − G)^{−σ̃}` satisfies, EXACTLY,
`log(f_t/f̄) = log((1−τ_t)/(1−τ̄)) + Ŷ_t + σ̃ log(C̄_t/C̄) − σ̃ log((Y_t−G_t)/(Ȳ−Ḡ))`. -/
theorem log_f_iso {σt τ τb Y Yb Cb Cbb G Gb : ℝ} (hτ : 0 < 1 - τ) (hτb : 0 < 1 - τb)
    (hY : 0 < Y) (hYb : 0 < Yb) (hC : 0 < Cb) (hCb : 0 < Cbb) (hG : 0 < Y - G)
    (hGb : 0 < Yb - Gb) :
    Real.log (((1 - τ) * Y * (Cb ^ σt * (Y - G) ^ (-σt))) /
        ((1 - τb) * Yb * (Cbb ^ σt * (Yb - Gb) ^ (-σt)))) =
      Real.log ((1 - τ) / (1 - τb)) + Real.log (Y / Yb) + σt * Real.log (Cb / Cbb)
        - σt * Real.log ((Y - G) / (Yb - Gb)) := by
  have p1 := Real.rpow_pos_of_pos hC σt
  have p2 := Real.rpow_pos_of_pos hG (-σt)
  have p3 := Real.rpow_pos_of_pos hCb σt
  have p4 := Real.rpow_pos_of_pos hGb (-σt)
  rw [Real.log_div (by positivity) (by positivity)]
  simp only [Real.log_mul, Real.log_rpow, hτ.ne', hτb.ne', hY.ne', hYb.ne', p1.ne', p2.ne',
    p3.ne', p4.ne', ne_eq, not_false_eq_true, mul_ne_zero_iff, and_self, hC, hCb, hG, hGb]
  rw [Real.log_div hτ.ne' hτb.ne', Real.log_div hY.ne' hYb.ne', Real.log_div hC.ne' hCb.ne',
    Real.log_div hG.ne' hGb.ne']
  ring

/-- Woodford (2003), p. 458 (notation of Benigno–Woodford): with `Ŷ = log(Y/Ȳ)`,
`Ĝ = (G − Ḡ)/Ȳ` and `s_C = (Ȳ − Ḡ)/Ȳ`, `(Y − G)/(Ȳ − Ḡ) = (e^Ŷ − (1 − s_C) − Ĝ)/s_C` exactly. -/
theorem consumption_ratio {Y Yb G Gb : ℝ} (hY : 0 < Y) (hYb : 0 < Yb) (hs : Yb - Gb ≠ 0) :
    (Y - G) / (Yb - Gb) =
      (Real.exp (Real.log (Y / Yb)) - (1 - (Yb - Gb) / Yb) - (G - Gb) / Yb) / ((Yb - Gb) / Yb) := by
  rw [Real.exp_log (div_pos hY hYb)]
  field_simp
  ring

/-! ### Bounded processes: continuous functions of bounded processes are bounded -/

/-! ### (5.4): the second-order aggregate-supply relation of the Calvo model -/

/-- Woodford (2003), §5 (Benigno–Woodford): the exact Calvo price-index relation
`1 = αΠ_t^{θ−1} + (1−α)(p*_t/P_t)^{1−θ}` in logs (`π_t = log Π_t`, `x_t = log(p*_t/P_t)`):
`α(e^{(θ−1)π_t} − 1) + (1−α)(e^{−(θ−1)x_t} − 1) = 0` (restated from Chapter 3). -/
def PriceIndexEq (α θ : ℝ) (infl xr : ℕ → Ω → ℝ) : Prop :=
  ∀ t w, α * (Real.exp ((θ - 1) * infl t w) - 1) +
    (1 - α) * (Real.exp (-((θ - 1) * xr t w)) - 1) = 0

/-- Woodford (2003), §5 (Benigno–Woodford): the optimal reset price under the isoelastic
Assumption 6.2, `(p*_t/P_t)^{1+ωθ} = K_t/F_t`, in log deviations: `(1+ωθ)x_t = K̂_t − F̂_t`
(restated from Chapter 3). -/
def ResetPriceEq (ω θ : ℝ) (xr F K : ℕ → Ω → ℝ) : Prop :=
  ∀ t w, (1 + ω * θ) * xr t w = K t w - F t w

/-- Woodford (2003), §5 (Benigno–Woodford): the recursive form of the discounted sums
`F_t = f_t + αβ E_t[Π_{t+1}^{e} F_{t+1}]` (with `e = θ − 1` for `F`, `e = θ(1+ω)` for `K`), in log
deviations from the steady state `F̄ = f̄/(1−αβ)`:
`e^{F̂_t} − 1 = (1−αβ)(e^{f̂_t} − 1) + αβ E_t(e^{eπ_{t+1} + F̂_{t+1}} − 1)`. -/
def RecEq (α β e : ℝ) (infl F f : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (fun w => Real.exp (F t w) - 1) = (1 - α * β) • (fun w => Real.exp (f t w) - 1) +
    (α * β) • 𝔼.E t (fun w => Real.exp (e * infl (t + 1) w + F (t + 1) w) - 1)

/-- The weight-two quantity `h = x − (α/(1−α))π` implied by the price index (explicit
polynomial in `π, x` and the exponential atoms `A₁ = r₃((θ−1)π)`, `A₂ = r₃(−(θ−1)x)`). -/
noncomputable def hA (α θ p x A1 A2 : ℝ) : ℝ :=
  (θ - 1) * (α / (1 - α)) / 2 * p ^ 2 + (θ - 1) / 2 * x ^ 2 + (α / (1 - α) * A1 + A2) / (θ - 1)

/-- The weight-three quantity `h₃ = h − (θ−1)α/(2(1−α)²) π²`. -/
noncomputable def h3A (α θ p x A1 A2 : ℝ) : ℝ :=
  (θ - 1) / 2 * hA α θ p x A1 A2 * (x + α / (1 - α) * p) + (α / (1 - α) * A1 + A2) / (θ - 1)

/-- Woodford (2003), (5.4) and p. 459 (Benigno–Woodford): the second-order inflation variable
`V_t = π_t + (θ−1)/(2(1−α)) π_t² + π_t S_t`, `S_t = (K̂_t + F̂_t)/2` (a forward-looking date-`t`
variable; the term `π_0 S_0` is the source of Woodford's `π_0 Z_0` term in `W_0`). -/
noncomputable def VA (α θ p S : ℝ) : ℝ := p + (θ - 1) / (2 * (1 - α)) * p ^ 2 + p * S

/-- The date-`t+1` part of the weight-three remainder of the second-order AS relation. -/
noncomputable def restA (α θ ω p x S A1 A2 rKn rFn : ℝ) : ℝ :=
  (1 - α) * (h3A α θ p x A1 A2 + hA α θ p x A1 A2 * ((θ - 1 + θ * (1 + ω)) / 2 * p + S))
    + (1 - α) / (1 + ω * θ) * (rKn - rFn)

/-- The date-`t` part of the weight-three remainder of the second-order AS relation. -/
noncomputable def nowA (α β θ ω p x S A1 A2 rK rF rk rf : ℝ) : ℝ :=
  -(h3A α θ p x A1 A2 + hA α θ p x A1 A2 * S) / (α / (1 - α))
    - (rK - rF) / (α / (1 - α) * (1 + ω * θ)) + calvoXi α β ω θ * (rk - rf)

/-- The price index gives `x = (α/(1−α))π + h` exactly. -/
theorem xr_eq_of_priceIndex {α θ p x : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hθ : θ ≠ 1)
    (h : α * (Real.exp ((θ - 1) * p) - 1) + (1 - α) * (Real.exp (-((θ - 1) * x)) - 1) = 0) :
    x = α / (1 - α) * p + hA α θ p x (expRem ((θ - 1) * p)) (expRem (-((θ - 1) * x))) := by
  rw [exp_sub_one_eq, exp_sub_one_eq] at h
  have ha : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ
  have h1 : 1 - α ≠ 0 := by linarith
  have h0 : α ≠ 0 := hα0.ne'
  unfold hA
  linear_combination (norm := skip) (-1 / ((θ - 1) * (1 - α))) * h
  field_simp
  ring

/-- The date-`t+1` identity behind the second-order AS relation (pure algebra): given the price
index (`x = (α/(1−α))π + h`) and the reset-price condition (`(1+ωθ)x = K − F`),
`(e^{θ(1+ω)π + K} − 1) − (e^{(θ−1)π + F} − 1) = ((1+ωθ)/(1−α))(V + θ(1+ω)π²/2 + rest)`. -/
theorem next_identity {α θ ω p x F K : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hθ : θ ≠ 1)
    (hν : 1 + ω * θ ≠ 0)
    (E1 : x = α / (1 - α) * p + hA α θ p x (expRem ((θ - 1) * p)) (expRem (-((θ - 1) * x))))
    (E2 : (1 + ω * θ) * x = K - F) :
    (Real.exp (θ * (1 + ω) * p + K) - 1) - (Real.exp ((θ - 1) * p + F) - 1) =
      (1 + ω * θ) / (1 - α) * (VA α θ p ((K + F) / 2) + θ * (1 + ω) / 2 * p ^ 2 +
        restA α θ ω p x ((K + F) / 2) (expRem ((θ - 1) * p)) (expRem (-((θ - 1) * x)))
          (expRem (θ * (1 + ω) * p + K)) (expRem ((θ - 1) * p + F))) := by
  have hK : K = F + (1 + ω * θ) * x := by linarith
  subst hK
  rw [exp_sub_one_eq, exp_sub_one_eq]
  have ha : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ
  have h1 : 1 - α ≠ 0 := by linarith
  have h0 : α ≠ 0 := hα0.ne'
  have hν' : 1 + θ * ω ≠ 0 := by rwa [mul_comm] at hν
  unfold VA restA h3A
  linear_combination (norm := skip) ((1 + ω * θ) * (1 + (θ - 1 + θ * (1 + ω)) / 2 * p +
    (F + (1 + ω * θ) * x + F) / 2 + (θ - 1) / 2 * (x + α / (1 - α) * p))) * E1
  unfold hA
  field_simp
  ring

/-- The date-`t` identity behind the second-order AS relation (pure algebra). -/
theorem now_identity {α β θ ω p x F K f k EV Ep ER : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hθ : θ ≠ 1) (hν : 1 + ω * θ ≠ 0)
    (E1 : x = α / (1 - α) * p + hA α θ p x (expRem ((θ - 1) * p)) (expRem (-((θ - 1) * x))))
    (E2 : (1 + ω * θ) * x = K - F)
    (hstar : (Real.exp K - 1) - (Real.exp F - 1) =
      (1 - α * β) * ((Real.exp k - 1) - (Real.exp f - 1)) +
        α * β * ((1 + ω * θ) / (1 - α) * (EV + θ * (1 + ω) / 2 * Ep + ER))) :
    VA α θ p ((K + F) / 2) =
      calvoXi α β ω θ * (k - f) * (1 + (k + f) / 2) + β * (θ * (1 + ω)) / 2 * Ep + β * EV +
        (nowA α β θ ω p x ((K + F) / 2) (expRem ((θ - 1) * p)) (expRem (-((θ - 1) * x)))
          (expRem K) (expRem F)
          (expRem k) (expRem f) + β * ER) := by
  have hK : K = F + (1 + ω * θ) * x := by linarith
  subst hK
  rw [exp_sub_one_eq, exp_sub_one_eq, exp_sub_one_eq, exp_sub_one_eq] at hstar
  have ha : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ
  have h1 : 1 - α ≠ 0 := by linarith
  have h0 : α ≠ 0 := hα0.ne'
  have hν' : 1 + θ * ω ≠ 0 := by rwa [mul_comm] at hν
  unfold VA nowA h3A calvoXi
  linear_combination (norm := skip) (1 / (α / (1 - α) * (1 + ω * θ))) * hstar -
    (1 / (α / (1 - α)) * (1 + (F + (1 + ω * θ) * x + F) / 2 +
      (θ - 1) / 2 * (x + α / (1 - α) * p))) * E1
  unfold hA
  field_simp
  ring

/-- Woodford (2003), (5.4): the process `V_t` of `VA`. -/
noncomputable def Vp (α θ : ℝ) (infl F K : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun w => VA α θ (infl t w) ((K t w + F t w) / 2)

/-- The date-`t` process of the date-`(t+1)` remainder part. -/
noncomputable def restP (α θ ω : ℝ) (infl xr F K : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun w => restA α θ ω (infl t w) (xr t w) ((K t w + F t w) / 2) (expRem ((θ - 1) * infl t w))
    (expRem (-((θ - 1) * xr t w))) (expRem (θ * (1 + ω) * infl t w + K t w))
    (expRem ((θ - 1) * infl t w + F t w))

/-- Woodford (2003), (5.4): the weight-three remainder `ρ_t` of the second-order AS relation
(date-`t` atoms plus `β E_t` of the date-`(t+1)` part). -/
noncomputable def rhoP (α β θ ω : ℝ) (infl xr F K f k : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun w => nowA α β θ ω (infl t w) (xr t w) ((K t w + F t w) / 2) (expRem ((θ - 1) * infl t w))
      (expRem (-((θ - 1) * xr t w))) (expRem (K t w)) (expRem (F t w)) (expRem (k t w))
      (expRem (f t w)) +
    β * 𝔼.E t (restP α θ ω infl xr F K (t + 1)) w

/-- Woodford (2003), §5, p. 457 ("a quadratic approximation to the aggregate supply relation"),
derived IN FULL from the exact Calvo equilibrium conditions (Benigno–Woodford): under the price
index, reset-price and recursive `F`/`K` conditions,
`V_t = κ̃(k̂_t − f̂_t)(1 + (k̂_t + f̂_t)/2) + (βθ(1+ω)/2) E_t π_{t+1}² + β E_t V_{t+1} + ρ_t`
EXACTLY, with `ρ_t` an explicit remainder of weight three (`nowA_scaling`, `restA_scaling`). -/
theorem second_order_AS {α β θ ω : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hθ : θ ≠ 1)
    (hν : 1 + ω * θ ≠ 0) {infl xr F K f k : ℕ → Ω → ℝ} (hP : PriceIndexEq α θ infl xr)
    (hR : ResetPriceEq ω θ xr F K) (hF : RecEq 𝔼 α β (θ - 1) infl F f)
    (hK : RecEq 𝔼 α β (θ * (1 + ω)) infl K k) (t : ℕ) :
    Vp α θ infl F K t =
      (fun w => calvoXi α β ω θ * (k t w - f t w) * (1 + (k t w + f t w) / 2)) +
        (β * (θ * (1 + ω)) / 2) • 𝔼.E t (fun w => infl (t + 1) w ^ 2) +
        β • 𝔼.E t (Vp α θ infl F K (t + 1)) + rhoP 𝔼 α β θ ω infl xr F K f k t := by
  have hnext : (fun w => Real.exp (θ * (1 + ω) * infl (t + 1) w + K (t + 1) w) - 1) =
      (fun w => Real.exp ((θ - 1) * infl (t + 1) w + F (t + 1) w) - 1) +
        ((1 + ω * θ) / (1 - α)) • (Vp α θ infl F K (t + 1) +
          (θ * (1 + ω) / 2) • (fun w => infl (t + 1) w ^ 2) + restP α θ ω infl xr F K (t + 1)) := by
    funext w
    have E1 := xr_eq_of_priceIndex hα0 hα1 hθ (hP (t + 1) w)
    have h := next_identity hα0 hα1 hθ hν E1 (hR (t + 1) w)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Vp, restP]
    linear_combination h
  have hE : 𝔼.E t (fun w => Real.exp (θ * (1 + ω) * infl (t + 1) w + K (t + 1) w) - 1) =
      𝔼.E t (fun w => Real.exp ((θ - 1) * infl (t + 1) w + F (t + 1) w) - 1) +
        ((1 + ω * θ) / (1 - α)) • (𝔼.E t (Vp α θ infl F K (t + 1)) +
          (θ * (1 + ω) / 2) • 𝔼.E t (fun w => infl (t + 1) w ^ 2) +
            𝔼.E t (restP α θ ω infl xr F K (t + 1))) := by
    rw [hnext, map_add, map_smul, map_add, map_add, map_smul]
  funext w
  have hFw := congrFun (hF t) w
  have hKw := congrFun (hK t) w
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hFw hKw
  have hEw := congrFun hE w
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hEw
  have hstar : (Real.exp (K t w) - 1) - (Real.exp (F t w) - 1) =
      (1 - α * β) * ((Real.exp (k t w) - 1) - (Real.exp (f t w) - 1)) +
        α * β * ((1 + ω * θ) / (1 - α) * (𝔼.E t (Vp α θ infl F K (t + 1)) w +
          θ * (1 + ω) / 2 * 𝔼.E t (fun w => infl (t + 1) w ^ 2) w +
            𝔼.E t (restP α θ ω infl xr F K (t + 1)) w)) := by
    rw [hKw, hFw, hEw]; ring
  have E1 := xr_eq_of_priceIndex hα0 hα1 hθ (hP t w)
  have key := now_identity (β := β) hα0 hα1 hθ hν E1 (hR t w) hstar
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Vp, rhoP]
  rw [key]

/-! #### Weighted degree of the AS remainder: scaling lemmas -/

/-- The rescaled date-`t` remainder. -/
noncomputable def nowQ (s α β θ ω p x S A1 A2 rK rF rk rf : ℝ) : ℝ :=
  -((θ - 1) / 2 * hA α θ p x (s * A1) (s * A2) * (x + α / (1 - α) * p) +
      (α / (1 - α) * A1 + A2) / (θ - 1) + hA α θ p x (s * A1) (s * A2) * S) / (α / (1 - α))
    - (rK - rF) / (α / (1 - α) * (1 + ω * θ)) + calvoXi α β ω θ * (rk - rf)

/-- The rescaled date-`(t+1)` remainder. -/
noncomputable def restQ (s α θ ω p x S A1 A2 rKn rFn : ℝ) : ℝ :=
  (1 - α) * ((θ - 1) / 2 * hA α θ p x (s * A1) (s * A2) * (x + α / (1 - α) * p) +
      (α / (1 - α) * A1 + A2) / (θ - 1) +
      hA α θ p x (s * A1) (s * A2) * ((θ - 1 + θ * (1 + ω)) / 2 * p + S))
    + (1 - α) / (1 + ω * θ) * (rKn - rFn)

/-- `h` has weight two. -/
theorem hA_scaling (s α θ p x A1 A2 : ℝ) :
    hA α θ (s * p) (s * x) (s ^ 3 * A1) (s ^ 3 * A2) = s ^ 2 * hA α θ p x (s * A1) (s * A2) := by
  unfold hA; ring

/-- Scaling lemma for the date-`t` AS remainder: weight three (`π, x, S` weight one, the
exponential atoms weight three). -/
theorem nowA_scaling (s α β θ ω p x S A1 A2 rK rF rk rf : ℝ) :
    nowA α β θ ω (s * p) (s * x) (s * S) (s ^ 3 * A1) (s ^ 3 * A2) (s ^ 3 * rK) (s ^ 3 * rF)
        (s ^ 3 * rk) (s ^ 3 * rf) = s ^ 3 * nowQ s α β θ ω p x S A1 A2 rK rF rk rf := by
  unfold nowA nowQ h3A
  rw [hA_scaling]
  ring

/-- Scaling lemma for the date-`(t+1)` AS remainder: weight three. -/
theorem restA_scaling (s α θ ω p x S A1 A2 rKn rFn : ℝ) :
    restA α θ ω (s * p) (s * x) (s * S) (s ^ 3 * A1) (s ^ 3 * A2) (s ^ 3 * rKn) (s ^ 3 * rFn) =
      s ^ 3 * restQ s α θ ω p x S A1 A2 rKn rFn := by
  unfold restA restQ h3A
  rw [hA_scaling]
  ring

/-! #### From `k̂ − f̂` to output and disturbances (Assumption 6.2) -/

/-- Woodford (2003), (5.4): the natural rate `Ŷⁿ = (ωq + σ⁻¹g − μ̂ʷ + τ̂)/(ω + σ⁻¹)` with
`g = Ĝ + s_C ĉ` (`ĉ` the preference shock `log C̄_t/C̄`, `μ̂ʷ` the cost-side markup/wedge, `τ̂` the
revenue-tax wedge `log((1−τ_t)/(1−τ̄))`). -/
noncomputable def YnA (ω σ sC G cb q muw tau : ℝ) : ℝ :=
  (ω * q + σ * (G + sC * cb) - muw + tau) / (ω + σ)

/-- Woodford (2003), (5.4): `μ_y = κ̃[σ⁻¹(1 − s_C⁻¹) + (1+ω)² − (1−σ⁻¹)²]`. -/
noncomputable def muY (α β θ ω σ sC : ℝ) : ℝ :=
  calvoXi α β ω θ * (σ * (1 - 1 / sC) + (1 + ω) ^ 2 - (1 - σ) ^ 2)

/-- Woodford (2003), (5.4): the composite disturbance
`δ_t = −κ̃[(σ⁻¹/s_C)Ĝ + (1+ω)(−ωq + μ̂ʷ) − (1−σ⁻¹)(σ⁻¹g + τ̂)]` (mean zero). -/
noncomputable def deltaA (α β θ ω σ sC G cb q muw tau : ℝ) : ℝ :=
  -(calvoXi α β ω θ * (σ / sC * G + (1 + ω) * (-(ω * q) + muw) -
    (1 - σ) * (σ * (G + sC * cb) + tau)))

/-- Woodford (2003), (5.4): the per-period t.i.p. of the AS expansion. -/
noncomputable def tipASA (α β θ ω σ sC G cb q muw tau : ℝ) : ℝ :=
  calvoXi α β ω θ * (-(σ / (2 * sC)) * G ^ 2 +
    ((-(ω * q) + muw) ^ 2 - (σ * (G + sC * cb) + tau) ^ 2) / 2)

/-- The weight-three part `f₃` of `f̂` (atoms `r₃(Ŷ)` and the log remainder). -/
noncomputable def f3A (σ sC Y G rY rl : ℝ) : ℝ :=
  -(σ * rY) + σ / (2 * sC) * (Y ^ 2 / 2 + rY) * (2 * (Y - G) + Y ^ 2 / 2 + rY) - sC * σ * rl

/-- The weight-three remainder of the AS expansion. -/
noncomputable def rho2A (α β θ ω σ sC Y G cb tau rY rl : ℝ) : ℝ :=
  -(calvoXi α β ω θ * (f3A σ sC Y G rY rl +
    (-(σ / 2) * Y ^ 2 + σ / (2 * sC) * (Y - G) ^ 2 + f3A σ sC Y G rY rl) *
      (2 * ((1 - σ) * Y + σ * (G + sC * cb) + tau) + (-(σ / 2) * Y ^ 2 +
        σ / (2 * sC) * (Y - G) ^ 2 + f3A σ sC Y G rY rl)) / 2))

/-- The argument of the log remainder: `z/s_C` with `z = e^Ŷ − 1 − Ĝ`. -/
noncomputable def zA (sC Y G : ℝ) : ℝ := (Y + Y ^ 2 / 2 + expRem Y - G) / sC

/-- Woodford (2003), (5.4) under Assumption 6.2 (Layer A): with the EXACT isoelastic forms
`k̂ = (1+ω)Ŷ − ωq + μ̂ʷ` (`log_k_iso`) and
`f̂ = Ŷ + s_Cσ⁻¹ĉ + τ̂ − s_Cσ⁻¹ log((e^Ŷ − (1−s_C) − Ĝ)/s_C)` (`log_f_iso`, `consumption_ratio`,
`σ̃ = s_Cσ⁻¹`),
`κ̃(k̂−f̂)(1 + (k̂+f̂)/2) = κ(Ŷ − Ŷⁿ) + (μ_y/2)Ŷ² − δŶ + t.i.p. + ρ₂` exactly, `ρ₂` of weight
three (`rho2A_scaling`). -/
theorem as_expand {α β θ ω σ sC : ℝ} (hs : sC ≠ 0) (hc : ω + σ ≠ 0) (Y G cb q muw tau : ℝ) :
    calvoXi α β ω θ * (((1 + ω) * Y - ω * q + muw) -
        (Y + sC * σ * cb + tau - sC * σ * Real.log ((Real.exp Y - (1 - sC) - G) / sC))) *
      (1 + (((1 + ω) * Y - ω * q + muw) +
        (Y + sC * σ * cb + tau - sC * σ * Real.log ((Real.exp Y - (1 - sC) - G) / sC))) / 2) =
    calvoKappa α β ω θ σ * (Y - YnA ω σ sC G cb q muw tau) + muY α β θ ω σ sC / 2 * Y ^ 2 -
      deltaA α β θ ω σ sC G cb q muw tau * Y + tipASA α β θ ω σ sC G cb q muw tau +
      rho2A α β θ ω σ sC Y G cb tau (expRem Y) (rlog (zA sC Y G)) := by
  have hl : Real.log ((Real.exp Y - (1 - sC) - G) / sC) =
      zA sC Y G - zA sC Y G ^ 2 / 2 + rlog (zA sC Y G) := by
    have harg : (Real.exp Y - (1 - sC) - G) / sC = 1 + zA sC Y G := by
      unfold zA
      rw [show Real.exp Y = 1 + (Real.exp Y - 1) by ring, exp_sub_one_eq]
      field_simp
      ring
    rw [harg]; unfold rlog; ring
  rw [hl, calvoKappa_eq]
  unfold YnA muY deltaA tipASA rho2A f3A zA
  field_simp
  ring

/-- The rescaled `f₃`. -/
noncomputable def f3Q (s σ sC Y G rY rl : ℝ) : ℝ :=
  -(σ * rY) + σ / (2 * sC) * (Y ^ 2 / 2 + s * rY) * (2 * (Y - G) + s * Y ^ 2 / 2 + s ^ 2 * rY)
    - sC * σ * rl

/-- The rescaled AS-expansion remainder. -/
noncomputable def rho2Q (s α β θ ω σ sC Y G cb tau rY rl : ℝ) : ℝ :=
  -(calvoXi α β ω θ * (f3Q s σ sC Y G rY rl +
    (-(σ / 2) * Y ^ 2 + σ / (2 * sC) * (Y - G) ^ 2 + s * f3Q s σ sC Y G rY rl) *
      (2 * ((1 - σ) * Y + σ * (G + sC * cb) + tau) + s * (-(σ / 2) * Y ^ 2 +
        σ / (2 * sC) * (Y - G) ^ 2) + s ^ 2 * f3Q s σ sC Y G rY rl) / 2))

/-- Scaling lemma for the AS-expansion remainder: weight three (`Ŷ, Ĝ, ĉ, τ̂` weight one, the
atoms `r₃(Ŷ)` and `rlog` weight three). -/
theorem rho2A_scaling (s α β θ ω σ sC Y G cb tau rY rl : ℝ) :
    rho2A α β θ ω σ sC (s * Y) (s * G) (s * cb) (s * tau) (s ^ 3 * rY) (s ^ 3 * rl) =
      s ^ 3 * rho2Q s α β θ ω σ sC Y G cb tau rY rl := by
  unfold rho2A rho2Q f3A f3Q
  ring

/-! #### The Calvo model under Assumption 6.2, and (5.4) forward-integrated -/

/-- Woodford (2003), Assumption 6.2: the exact revenue term `f̂_t` of the Calvo reset-price
condition, `Ŷ + s_Cσ⁻¹ĉ + τ̂ − s_Cσ⁻¹ log((e^Ŷ − (1−s_C) − Ĝ)/s_C)` (`log_f_iso`). -/
noncomputable def fhatIso (σ sC Y G cb tau : ℝ) : ℝ :=
  Y + sC * σ * cb + tau - sC * σ * Real.log ((Real.exp Y - (1 - sC) - G) / sC)

namespace CalvoModel

variable (α β θ ω σ sC : ℝ) (infl xr F K f k Y G cb q muw tau : ℕ → Ω → ℝ)

/-- Woodford (2003), §5, pp. 457–458 (Benigno–Woodford 2003): the EXACT equilibrium conditions
of the Calvo model of Chapter 3 under Assumption 6.2, in log deviations from the zero-inflation
steady state (no small-`Φ_y` assumption): the price index, the optimal reset price, the
recursions for `F` and `K`, and the isoelastic forms of `k̂` and `f̂`. -/
structure CalvoAS where
  priceIndex : PriceIndexEq α θ infl xr
  resetPrice : ResetPriceEq ω θ xr F K
  recF : RecEq 𝔼 α β (θ - 1) infl F f
  recK : RecEq 𝔼 α β (θ * (1 + ω)) infl K k
  costK : ∀ t w, k t w = (1 + ω) * Y t w - ω * q t w + muw t w
  revF : ∀ t w, f t w = fhatIso σ sC (Y t w) (G t w) (cb t w) (tau t w)

end CalvoModel

/-- Woodford (2003), (5.4): the weight-three remainder process of (5.4). -/
noncomputable def remAS (α β θ ω σ sC : ℝ) (infl xr F K f k Y G cb tau : ℕ → Ω → ℝ) (t : ℕ) :
    Ω → ℝ :=
  fun w => rhoP 𝔼 α β θ ω infl xr F K f k t w +
    rho2A α β θ ω σ sC (Y t w) (G t w) (cb t w) (tau t w) (expRem (Y t w))
      (rlog (zA sC (Y t w) (G t w)))

/-- Woodford (2003), eq. (5.4), p. 458, DERIVED IN FULL from the exact Calvo model under
Assumption 6.2 (the book only cites Benigno and Woodford (2003)):
`E_0[π_0 + Q_0] = κ ∑βᵗE_0(Ŷ_t − Ŷⁿ_t) + (μ_y/2)∑βᵗE_0Ŷ_t² − ∑βᵗE_0 δ_tŶ_t
  + (μ_π/2)∑βᵗE_0π_t² + t.i.p. + R`, with `μ_π = θ(1+ω)`, `μ_y = muY`, `δ = deltaA`,
`π_0 + Q_0 = V_0 + (μ_π/2)π_0²` (so `Q_0 = ((θ−1)/(2(1−α)) + μ_π/2)π_0² + π_0S_0`,
`S_0 = (K̂_0+F̂_0)/2` a forward-looking date-0 variable; `π_0S_0` is Woodford's `π_0 Z_0`
term), t.i.p. `= ∑βᵗE_0 tipASA` and remainder
`R = ∑βᵗE_0 remAS` of weight three. All processes bounded; `E_0` may be dropped on the left when
`V_0 + (μ_π/2)π_0²` is known at date 0. -/
theorem eq54 {α β θ ω σ sC : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 1) (hν : 1 + ω * θ ≠ 0) (hs : sC ≠ 0) (hc : ω + σ ≠ 0)
    {infl xr F K f k Y G cb q muw tau : ℕ → Ω → ℝ}
    (hM : CalvoModel.CalvoAS 𝔼 α β θ ω σ sC infl xr F K f k Y G cb q muw tau)
    (hib : BoundedProc infl) (hFb : BoundedProc F) (hKb : BoundedProc K) (hYb : BoundedProc Y)
    (hGb : BoundedProc G) (hcb : BoundedProc cb) (hqb : BoundedProc q) (hmb : BoundedProc muw)
    (htb : BoundedProc tau) (w : Ω) :
    𝔼.E 0 (fun w => Vp α θ infl F K 0 w + θ * (1 + ω) / 2 * infl 0 w ^ 2) w =
      calvoKappa α β ω θ σ * dsum 𝔼 β (fun t w => Y t w -
          YnA ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w)) w
        + muY α β θ ω σ sC / 2 * dsum 𝔼 β (fun t w => Y t w ^ 2) w
        - dsum 𝔼 β (fun t w => deltaA α β θ ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w) *
            Y t w) w
        + θ * (1 + ω) / 2 * dsum 𝔼 β (fun t w => infl t w ^ 2) w
        + dsum 𝔼 β (fun t w => tipASA α β θ ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w)) w
        + dsum 𝔼 β (remAS 𝔼 α β θ ω σ sC infl xr F K f k Y G cb tau) w := by
  have hβ : |β| < 1 := by rw [abs_lt]; constructor <;> linarith
  set b : ℝ := θ * (1 + ω) with hb
  set P1 : ℕ → Ω → ℝ := fun t w => Y t w - YnA ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w)
    with hP1
  set P2 : ℕ → Ω → ℝ := fun t w => Y t w ^ 2 with hP2
  set P3 : ℕ → Ω → ℝ := fun t w =>
    deltaA α β θ ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w) * Y t w with hP3
  set P4 : ℕ → Ω → ℝ := fun t w =>
    tipASA α β θ ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w) with hP4
  set P5 : ℕ → Ω → ℝ := fun t w => infl t w ^ 2 with hP5
  set Rm := remAS 𝔼 α β θ ω σ sC infl xr F K f k Y G cb tau with hRm
  -- boundedness
  have bX : ∀ i, BoundedProc (![Y, G, cb, q, muw, tau] i) := by
    intro i; fin_cases i <;> assumption
  have b1 : BoundedProc P1 := bdd_congr (bdd_of_continuous
    (fun v => v 0 - YnA ω σ sC (v 1) (v 2) (v 3) (v 4) (v 5)) (by unfold YnA; fun_prop) _ bX)
    (fun t w => by simp [P1])
  have b2 : BoundedProc P2 := bdd_congr (bdd_sq hYb) (fun t w => by simp [P2])
  have b3 : BoundedProc P3 := bdd_congr (bdd_of_continuous
    (fun v => deltaA α β θ ω σ sC (v 1) (v 2) (v 3) (v 4) (v 5) * v 0)
    (by unfold deltaA; fun_prop) _ bX) (fun t w => by simp [P3])
  have b4 : BoundedProc P4 := bdd_congr (bdd_of_continuous
    (fun v => tipASA α β θ ω σ sC (v 1) (v 2) (v 3) (v 4) (v 5))
    (by unfold tipASA; fun_prop) _ bX) (fun t w => by simp [P4])
  have b5 : BoundedProc P5 := bdd_congr (bdd_sq hib) (fun t w => by simp [P5])
  have bV : BoundedProc (Vp α θ infl F K) := by
    have bI : ∀ i, BoundedProc (![infl, F, K] i) := by
      intro i; fin_cases i <;> assumption
    exact bdd_congr (bdd_of_continuous (fun v => VA α θ (v 0) ((v 2 + v 1) / 2))
      (by unfold VA; fun_prop) _ bI) (fun t w => by simp [Vp])
  -- the second-order AS relation, applied with E_0
  have hstep : ∀ t, 𝔼.E 0 (Vp α θ infl F K t) w - β * 𝔼.E 0 (Vp α θ infl F K (t + 1)) w =
      calvoKappa α β ω θ σ * 𝔼.E 0 (P1 t) w + muY α β θ ω σ sC / 2 * 𝔼.E 0 (P2 t) w -
        𝔼.E 0 (P3 t) w + 𝔼.E 0 (P4 t) w + β * b / 2 * 𝔼.E 0 (P5 (t + 1)) w +
        𝔼.E 0 (Rm t) w := by
    intro t
    have h := second_order_AS 𝔼 hα0 hα1 hθ hν hM.priceIndex hM.resetPrice hM.recF hM.recK t
    have hmain : (fun w => calvoXi α β ω θ * (k t w - f t w) * (1 + (k t w + f t w) / 2)) +
        rhoP 𝔼 α β θ ω infl xr F K f k t =
        calvoKappa α β ω θ σ • P1 t + (muY α β θ ω σ sC / 2) • P2 t - P3 t + P4 t + Rm t := by
      funext x
      have hx := as_expand (α := α) (β := β) (θ := θ) hs hc (Y t x) (G t x) (cb t x) (q t x)
        (muw t x) (tau t x)
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, P1, P2, P3, P4, Rm,
        remAS]
      rw [hM.costK t x, hM.revF t x]
      unfold fhatIso
      rw [hx]
      ring
    have hV : Vp α θ infl F K t - β • 𝔼.E t (Vp α θ infl F K (t + 1)) =
        calvoKappa α β ω θ σ • P1 t + (muY α β θ ω σ sC / 2) • P2 t - P3 t + P4 t + Rm t +
          (β * b / 2) • 𝔼.E t (P5 (t + 1)) := by
      rw [← hmain, h]
      simp only [P5]
      abel
    have h0 := congrArg (fun X => 𝔼.E 0 X w) hV
    simp only [map_sub, map_add, map_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, 𝔼.tower (Nat.zero_le t)] at h0
    linear_combination h0
  -- forward integration
  obtain ⟨MV, hMV⟩ := bV
  have hv : ∀ t, |𝔼.E 0 (Vp α θ infl F K t) w| ≤ MV := fun t => abs_E0_le 𝔼 hMV w t
  set d : ℕ → ℝ := fun t =>
    𝔼.E 0 (Vp α θ infl F K t) w - β * 𝔼.E 0 (Vp α θ infl F K (t + 1)) w with hd
  have hfw := forward_real hβ hv (d := d) (fun t => by simp only [d]; ring)
  have hdb : ∀ t, |d t| ≤ MV + |β| * MV := by
    intro t
    simp only [d]
    calc |𝔼.E 0 (Vp α θ infl F K t) w - β * 𝔼.E 0 (Vp α θ infl F K (t + 1)) w|
        ≤ |𝔼.E 0 (Vp α θ infl F K t) w| + |β * 𝔼.E 0 (Vp α θ infl F K (t + 1)) w| :=
          abs_sub _ _
      _ ≤ MV + |β| * MV := by
          rw [abs_mul]
          exact add_le_add (hv t) (mul_le_mul_of_nonneg_left (hv (t + 1)) (abs_nonneg β))
  have sd : HasSum (fun t => β ^ t * d t) (𝔼.E 0 (Vp α θ infl F K 0) w) := by
    rw [hfw]; exact (summable_geom_bdd hβ hdb).hasSum
  -- the pieces
  have s1 := hasSum_dsum 𝔼 hβ b1 w
  have s2 := hasSum_dsum 𝔼 hβ b2 w
  have s3 := hasSum_dsum 𝔼 hβ b3 w
  have s4 := hasSum_dsum 𝔼 hβ b4 w
  have s5 := hasSum_dsum 𝔼 hβ b5 w
  obtain ⟨M5, hM5⟩ := b5
  have sum5 : Summable (fun t => β ^ t * 𝔼.E 0 (P5 t) w) :=
    summable_geom_bdd hβ (fun t => abs_E0_le 𝔼 hM5 w t)
  have sum5s : Summable (fun t => β ^ t * 𝔼.E 0 (P5 (t + 1)) w) :=
    summable_geom_bdd hβ (fun t => abs_E0_le 𝔼 hM5 w (t + 1))
  have hshift := tsum_geom_shift sum5
  have s5s : HasSum (fun t => β ^ t * (β * b / 2 * 𝔼.E 0 (P5 (t + 1)) w))
      (b / 2 * (dsum 𝔼 β P5 w - 𝔼.E 0 (P5 0) w)) := by
    have := sum5s.hasSum.mul_left (β * b / 2)
    convert this using 1
    · funext t; ring
    · have e : dsum 𝔼 β P5 w = 𝔼.E 0 (P5 0) w + β * ∑' t, β ^ t * 𝔼.E 0 (P5 (t + 1)) w :=
        hshift
      rw [e]; ring
  have sR : HasSum (fun t => β ^ t * 𝔼.E 0 (Rm t) w)
      (𝔼.E 0 (Vp α θ infl F K 0) w - (calvoKappa α β ω θ σ * dsum 𝔼 β P1 w +
        muY α β θ ω σ sC / 2 * dsum 𝔼 β P2 w - dsum 𝔼 β P3 w + dsum 𝔼 β P4 w +
        b / 2 * (dsum 𝔼 β P5 w - 𝔼.E 0 (P5 0) w))) := by
    have := sd.sub (((((s1.mul_left (calvoKappa α β ω θ σ)).add
      (s2.mul_left (muY α β θ ω σ sC / 2))).sub
      s3).add s4).add s5s)
    convert this using 1
    funext t
    have := hstep t
    simp only [d]
    rw [this]
    ring
  have eR : dsum 𝔼 β Rm w = _ := sR.tsum_eq
  -- assemble
  have hL : 𝔼.E 0 (fun w => Vp α θ infl F K 0 w + θ * (1 + ω) / 2 * infl 0 w ^ 2) w =
      𝔼.E 0 (Vp α θ infl F K 0) w + b / 2 * 𝔼.E 0 (P5 0) w := by
    have : (fun w => Vp α θ infl F K 0 w + θ * (1 + ω) / 2 * infl 0 w ^ 2) =
        Vp α θ infl F K 0 + (b / 2) • P5 0 := by
      funext x; simp [P5, hb]
    rw [this, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hL, eR]
  ring

/-! ### Proposition 6.15 -/

/-- Woodford (2003), eq. (5.7), p. 458, as printed:
`λ̃ = (κ/θ)[1 − Φ_y(s_C⁻¹ − 1)/(ω + σ⁻¹ + Φ_y(1 − σ⁻¹)) · σ⁻¹/(ω + σ⁻¹)]`. -/
noncomputable def lamTilde (α β θ ω σ sC Φ : ℝ) : ℝ :=
  calvoKappa α β ω θ σ / θ * (1 - Φ * (1 / sC - 1) / (ω + σ + Φ * (1 - σ)) * (σ / (ω + σ)))

/-- Woodford (2003), p. 459: the common denominator
`M = ω + σ⁻¹ + Φ_y(1 − σ⁻¹) − Φ_y(s_C⁻¹ − 1)σ⁻¹/(ω + σ⁻¹)` of `ω₂, ω₃` (nonzero iff `λ̃ ≠ 0`). -/
noncomputable def Mden (ω σ sC Φ : ℝ) : ℝ :=
  ω + σ + Φ * (1 - σ) - Φ * (1 / sC - 1) * σ / (ω + σ)

/-- Woodford (2003), p. 459: `ω₁ = κ/(λ̃θ)`. -/
noncomputable def omega1 (α β θ ω σ sC Φ : ℝ) : ℝ :=
  calvoKappa α β ω θ σ / (lamTilde α β θ ω σ sC Φ * θ)

/-- Woodford (2003), p. 459, as printed:
`ω₂ = Φ_y s_C⁻¹σ⁻¹/((ω + σ⁻¹)² + Φ_y[(1 − σ⁻¹)(ω + σ⁻¹) − (s_C⁻¹ − 1)σ⁻¹])`. -/
noncomputable def omega2 (ω σ sC Φ : ℝ) : ℝ :=
  Φ * (1 / sC) * σ / ((ω + σ) ^ 2 + Φ * ((1 - σ) * (ω + σ) - (1 / sC - 1) * σ))

/-- Woodford (2003), p. 459, as printed:
`ω₃ = (1 − Φ_y)/((ω + σ⁻¹) + Φ_y[(1 − σ⁻¹) − (s_C⁻¹ − 1)σ⁻¹(ω + σ⁻¹)⁻¹])`. -/
noncomputable def omega3 (ω σ sC Φ : ℝ) : ℝ :=
  (1 - Φ) / ((ω + σ) + Φ * ((1 - σ) - (1 / sC - 1) * σ * (ω + σ)⁻¹))

/-- Woodford (2003), eq. (5.8), p. 458, generalised: the target
`Ŷ*_t = ω₁Ŷⁿ_t − ω₂Ĝ_t + ω₃μ̂ʷ_t − τ̂_t/M`; for a revenue-tax wedge `τ̂ ≡ 0` (the case of
footnote 73: all wedges on the cost side) this is exactly (5.8). -/
noncomputable def YstarA (α β θ ω σ sC Φ G cb q muw tau : ℝ) : ℝ :=
  omega1 α β θ ω σ sC Φ * YnA ω σ sC G cb q muw tau - omega2 ω σ sC Φ * G +
    omega3 ω σ sC Φ * muw - tau / Mden ω σ sC Φ

/-- Woodford (2003), eq. (5.6): `L̃_t = π_t² + λ̃(Ŷ_t − Ŷ*_t)²`. -/
noncomputable def loss615 (α β θ ω σ sC Φ : ℝ) (infl Y G cb q muw tau : ℕ → Ω → ℝ) (t : ℕ) :
    Ω → ℝ :=
  fun w => infl t w ^ 2 + lamTilde α β θ ω σ sC Φ *
    (Y t w - YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w)) ^ 2

/-- Woodford (2003), (5.5): `Ω̃ = Ω(1 + Φ_y(1+ω)/((1−Φ_y)(ω+σ⁻¹)))` (`> 0`, `OmegaTilde_pos`). -/
noncomputable def OmegaTilde (Ybar uc α β θ ω σ Φ : ℝ) : ℝ :=
  OmegaW Ybar uc (calvoKappa α β ω θ σ) θ Φ ω σ * (1 + Φ * (1 + ω) / ((1 - Φ) * (ω + σ)))

/-- Woodford (2003), (5.5): the coefficient `γ̄/κ = Φ_y/((1−Φ_y)θ(ω+σ⁻¹))` of the transitory
term. -/
noncomputable def gbarC (θ ω σ Φ : ℝ) : ℝ := Φ / ((1 - Φ) * θ * (ω + σ))

/-- Woodford (2003), (5.5): `Ω̃ > 0`. -/
theorem OmegaTilde_pos {Ybar uc α β θ ω σ Φ : ℝ} (hY : 0 < Ybar) (huc : 0 < uc) (hα0 : 0 < α)
    (hα1 : α < 1) (hβ1 : β < 1) (hθ : 0 < θ) (hω : 0 < ω) (hσ : 0 < σ) (hΦ0 : 0 ≤ Φ)
    (hΦ : Φ < 1) : 0 < OmegaTilde Ybar uc α β θ ω σ Φ := by
  unfold OmegaTilde
  have h1 := OmegaW_pos hY huc hα0 hα1 hβ1 hθ hω hσ hΦ (β := β)
  have h2 : 0 ≤ Φ * (1 + ω) / ((1 - Φ) * (ω + σ)) :=
    div_nonneg (mul_nonneg hΦ0 (by linarith)) (mul_pos (by linarith) (by linarith)).le
  positivity

/-- Woodford (2003), eq. (5.7) VERIFIED: eliminating `∑βᵗŶ_t` with (5.4) turns the weights
`(1, λ_yy)` of (5.3) into `(1 + γ̄μ_π/κ, λ_yy + γ̄μ_y/κ)` (`γ̄ = κΦ_y/((1−Φ_y)θ(ω+σ⁻¹))`,
`μ_π = θ(1+ω)`, `μ_y = muY`); their ratio is exactly the printed `λ̃`. -/
theorem lamTilde_eq {α β θ ω σ sC Φ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hθ : 0 < θ) (hω : 0 < ω) (hσ : 0 < σ) (hs : 0 < sC) (hΦ0 : 0 ≤ Φ) (hΦ : Φ < 1) :
    lamTilde α β θ ω σ sC Φ * (1 + gbarC θ ω σ Φ * (θ * (1 + ω))) =
      lamYY (calvoKappa α β ω θ σ) θ Φ ω σ + gbarC θ ω σ Φ * muY α β θ ω σ sC := by
  have hc : ω + σ ≠ 0 := by linarith
  have hD : ω + σ + Φ * (1 - σ) ≠ 0 := by nlinarith
  have h1Φ : 1 - Φ ≠ 0 := by linarith
  have hν : 1 + ω * θ ≠ 0 := by nlinarith
  have hν' : 1 + θ * ω ≠ 0 := by nlinarith
  have hα : α ≠ 0 := hα0.ne'
  unfold lamTilde gbarC lamYY muY calvoKappa calvoXi
  field_simp
  ring

/-- Woodford (2003), p. 459: `λ̃ = (κ/θ) M/(ω + σ⁻¹ + Φ_y(1−σ⁻¹))`. -/
theorem lamTilde_eq_M {α β θ ω σ sC Φ : ℝ} (hc : ω + σ ≠ 0) (hD : ω + σ + Φ * (1 - σ) ≠ 0) :
    lamTilde α β θ ω σ sC Φ = calvoKappa α β ω θ σ / θ * Mden ω σ sC Φ / (ω + σ + Φ * (1 - σ)) := by
  unfold lamTilde Mden
  field_simp

/-- Woodford (2003), p. 459: `ω₁ = (ω + σ⁻¹ + Φ_y(1−σ⁻¹))/M`. -/
theorem omega1_eq {α β θ ω σ sC Φ : ℝ} (hκ : calvoKappa α β ω θ σ ≠ 0) (hθ : θ ≠ 0)
    (hc : ω + σ ≠ 0) (hD : ω + σ + Φ * (1 - σ) ≠ 0) (hM : Mden ω σ sC Φ ≠ 0) :
    omega1 α β θ ω σ sC Φ = (ω + σ + Φ * (1 - σ)) / Mden ω σ sC Φ := by
  unfold omega1
  rw [lamTilde_eq_M hc hD]
  field_simp

/-- Woodford (2003), p. 459: `ω₂ = Φ_y s_C⁻¹σ⁻¹/((ω + σ⁻¹)M)`. -/
theorem omega2_eq {ω σ sC Φ : ℝ} (hc : ω + σ ≠ 0) :
    omega2 ω σ sC Φ = Φ * (1 / sC) * σ / ((ω + σ) * Mden ω σ sC Φ) := by
  unfold omega2 Mden
  congr 1
  field_simp
  ring

/-- Woodford (2003), p. 459: `ω₃ = (1 − Φ_y)/M`. -/
theorem omega3_eq (ω σ sC Φ : ℝ) : omega3 ω σ sC Φ = (1 - Φ) / Mden ω σ sC Φ := by
  unfold omega3 Mden
  ring

/-- Woodford (2003), p. 459: the combined quadratic weight `λ_yy + γ̄μ_y/κ` equals
`κ M/((1−Φ_y)θ(ω+σ⁻¹))`. -/
theorem N_eq {α β θ ω σ sC Φ : ℝ} (hθ : θ ≠ 0) (hc : ω + σ ≠ 0) (h1Φ : 1 - Φ ≠ 0) (hs : sC ≠ 0)
    (hα : α ≠ 0) (hν : 1 + ω * θ ≠ 0) :
    lamYY (calvoKappa α β ω θ σ) θ Φ ω σ + gbarC θ ω σ Φ * muY α β θ ω σ sC =
      calvoKappa α β ω θ σ / ((1 - Φ) * θ * (ω + σ)) * Mden ω σ sC Φ := by
  have hν' : 1 + θ * ω ≠ 0 := by rwa [mul_comm] at hν
  unfold lamYY gbarC muY calvoKappa calvoXi Mden
  field_simp
  ring

/-- Woodford (2003), eq. (5.8) VERIFIED: completing the square in
`(λ_yy + γ̄μ_y/κ)Ŷ² − 2(γ̃_t + γ̄δ_t/κ)Ŷ` (`γ̃_t = (κ/θ)(σ⁻¹g_t + (1−Φ_y)ωq_t)/((1−Φ_y)(ω+σ⁻¹))`,
`g = Ĝ + s_Cĉ`) gives the target `Ŷ* = (γ̃ + γ̄δ/κ)/(λ_yy + γ̄μ_y/κ)`, which is exactly
`ω₁Ŷⁿ − ω₂Ĝ + ω₃μ̂ʷ − τ̂/M` with the printed `ω₁, ω₂, ω₃`. -/
theorem ystar_eq {α β θ ω σ sC Φ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ1 : β < 1)
    (hθ : 0 < θ) (hω : 0 < ω) (hσ : 0 < σ) (hs : 0 < sC) (hΦ0 : 0 ≤ Φ) (hΦ : Φ < 1)
    (hM : Mden ω σ sC Φ ≠ 0) (G cb q muw tau : ℝ) :
    (lamYY (calvoKappa α β ω θ σ) θ Φ ω σ + gbarC θ ω σ Φ * muY α β θ ω σ sC) *
        YstarA α β θ ω σ sC Φ G cb q muw tau =
      calvoKappa α β ω θ σ / θ * (σ * (G + sC * cb) + (1 - Φ) * ω * q) / ((1 - Φ) * (ω + σ)) +
        gbarC θ ω σ Φ * deltaA α β θ ω σ sC G cb q muw tau := by
  have hc : ω + σ ≠ 0 := by linarith
  have hD : ω + σ + Φ * (1 - σ) ≠ 0 := by nlinarith
  have h1Φ : 1 - Φ ≠ 0 := by linarith
  have hν : 1 + ω * θ ≠ 0 := by nlinarith
  have hν' : 1 + θ * ω ≠ 0 := by nlinarith
  have hα : α ≠ 0 := hα0.ne'
  have hab : 1 - α * β ≠ 0 := by nlinarith
  have h1a : 1 - α ≠ 0 := by linarith
  have hκ : calvoKappa α β ω θ σ ≠ 0 := by
    unfold calvoKappa
    exact mul_ne_zero (div_ne_zero (mul_ne_zero h1a hab) hα) (div_ne_zero hc hν)
  rw [N_eq hθ.ne' hc h1Φ hs.ne' hα hν]
  unfold YstarA
  rw [omega1_eq hκ hθ.ne' hc hD hM, omega2_eq hc, omega3_eq]
  unfold gbarC deltaA YnA calvoKappa calvoXi
  field_simp
  ring

/-- Woodford (2003), Proposition 6.15, eqs. (5.5)–(5.8), pp. 458–459, PROVED from (5.1)
(`h51`), the Calvo dispersion law (`hV`, `hD`, as in Proposition 6.14) and the exact Calvo model
under Assumption 6.2 (`hM`, through the derived (5.4), `eq54`), for any `Φ_y ∈ [0, 1)`:
`∑βᵗE_0U_t = W_0 − Ω̃ ∑βᵗE_0 L̃_t + t.i.p. + R` with `L̃_t = π_t² + λ̃(Ŷ_t − Ŷ*_t)²`, `λ̃` as
printed in (5.7), `Ŷ*` as printed in (5.8) (plus `−τ̂/M` for a revenue-tax wedge),
`Ω̃ = OmegaTilde > 0`, the transitory term `W_0 = 2Ω(γ̄/κ) E_0[π_0 + Q_0]` (`π_0 + Q_0` the
date-0 left side of (5.4)), t.i.p. depending only on disturbances and `Δ_{−1}`, and `R` of weight
three. Hypothesis `hMd : M ≠ 0` (i.e. `λ̃ ≠ 0`) is needed for `ω₁, ω₂, ω₃` to be defined; the
book leaves it implicit. -/
theorem prop615 {α β θ ω σ sC Φ Ybar uc : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ : 1 < θ) (hω : 0 < ω) (hσ : 0 < σ) (hs : 0 < sC) (hΦ0 : 0 ≤ Φ)
    (hΦ : Φ < 1) (hMd : Mden ω σ sC Φ ≠ 0)
    {U V D pib tipU R infl xr F K f k Y G cb q muw tau : ℕ → Ω → ℝ}
    (hM : CalvoModel.CalvoAS 𝔼 α β θ ω σ sC infl xr F K f k Y G cb q muw tau)
    (hib : BoundedProc infl) (hFb : BoundedProc F) (hKb : BoundedProc K) (hYb : BoundedProc Y)
    (hGb : BoundedProc G) (hcb : BoundedProc cb) (hqb : BoundedProc q) (hmb : BoundedProc muw)
    (htb : BoundedProc tau) (hDb : BoundedProc D) (hpb : BoundedProc pib)
    (hTb : BoundedProc tipU) (hRb : BoundedProc R)
    (h51 : ∀ t, U t = (fun w => -(Ybar * uc / 2) *
        quad51 σ ω θ Φ (G t w + sC * cb t w) (q t w) (Y t w) (V t w)) + tipU t + R t)
    (hV : ∀ t, V t = θ ^ 2 • D (t + 1))
    (hD : ∀ t, D (t + 1) = α • D t + (α / (1 - α)) • pib t ^ 2) (w : Ω) :
    dsum 𝔼 β U w =
      2 * OmegaW Ybar uc (calvoKappa α β ω θ σ) θ Φ ω σ * gbarC θ ω σ Φ *
          𝔼.E 0 (fun w => Vp α θ infl F K 0 w + θ * (1 + ω) / 2 * infl 0 w ^ 2) w
        - OmegaTilde Ybar uc α β θ ω σ Φ *
          dsum 𝔼 β (loss615 α β θ ω σ sC Φ infl Y G cb q muw tau) w
        + (dsum 𝔼 β tipU w
          - OmegaW Ybar uc (calvoKappa α β ω θ σ) θ Φ ω σ * (1 - α) * 𝔼.E 0 (D 0) w
          + OmegaTilde Ybar uc α β θ ω σ Φ * lamTilde α β θ ω σ sC Φ *
            dsum 𝔼 β (fun t w =>
              YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) ^ 2) w
          + 2 * OmegaW Ybar uc (calvoKappa α β ω θ σ) θ Φ ω σ * gbarC θ ω σ Φ *
            calvoKappa α β ω θ σ *
            dsum 𝔼 β (fun t w => YnA ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w)) w
          - 2 * OmegaW Ybar uc (calvoKappa α β ω θ σ) θ Φ ω σ * gbarC θ ω σ Φ *
            dsum 𝔼 β (fun t w => tipASA α β θ ω σ sC (G t w) (cb t w) (q t w) (muw t w)
              (tau t w)) w)
        + (dsum 𝔼 β R w - OmegaW Ybar uc (calvoKappa α β ω θ σ) θ Φ ω σ *
            (dsum 𝔼 β (fun t => pib t ^ 2) w - dsum 𝔼 β (fun t => infl t ^ 2) w)
          - 2 * OmegaW Ybar uc (calvoKappa α β ω θ σ) θ Φ ω σ * gbarC θ ω σ Φ *
            dsum 𝔼 β (remAS 𝔼 α β θ ω σ sC infl xr F K f k Y G cb tau) w) := by
  have hβ : |β| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hθ0 : 0 < θ := by linarith
  have hc : ω + σ ≠ 0 := by linarith
  have h1Φ : 1 - Φ ≠ 0 := by linarith
  have hν : 1 + ω * θ ≠ 0 := by nlinarith
  set κ := calvoKappa α β ω θ σ with hκ
  set Om := OmegaW Ybar uc κ θ Φ ω σ with hOm
  set gb := gbarC θ ω σ Φ with hgb
  set lt := lamTilde α β θ ω σ sC Φ with hlt
  set b : ℝ := θ * (1 + ω) with hb
  -- welfare side: Proposition 6.14
  have hg : BoundedProc (fun t w => G t w + sC * cb t w) := by
    have bI : ∀ i, BoundedProc (![G, cb] i) := by intro i; fin_cases i <;> assumption
    exact bdd_congr (bdd_of_continuous (fun v => v 0 + sC * v 1) (by fun_prop) _ bI)
      (fun t w => by simp)
  have h614 := prop614 𝔼 hα0 hα1 hβ0 hβ1 hθ0 hω hσ hΦ hYb hib hg hqb hDb hpb hTb hRb
    (g := fun t w => G t w + sC * cb t w) h51 hV hD w
  rw [← hκ, ← hOm] at h614
  -- supply side: (5.4)
  have h54 := eq54 𝔼 hα0 hα1 hβ0 hβ1 (by linarith : θ ≠ 1) hν hs.ne' hc hM hib hFb hKb hYb hGb
    hcb hqb hmb htb w
  -- bounded building blocks
  have bX : ∀ i, BoundedProc (![Y, G, cb, q, muw, tau] i) := by
    intro i; fin_cases i <;> assumption
  have bY2 := bdd_sq hYb
  have bpi2 : BoundedProc (fun t w => infl t w ^ 2) :=
    bdd_congr (bdd_sq hib) (fun t w => by simp)
  have bgY := bdd_mul hg hYb
  have bqY := bdd_mul hqb hYb
  have bYn : BoundedProc (fun t w => YnA ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w)) :=
    bdd_congr (bdd_of_continuous (fun v => YnA ω σ sC (v 1) (v 2) (v 3) (v 4) (v 5))
      (by unfold YnA; fun_prop) _ bX) (fun t w => by simp)
  have bdY : BoundedProc (fun t w =>
      deltaA α β θ ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w) * Y t w) :=
    bdd_congr (bdd_of_continuous (fun v => deltaA α β θ ω σ sC (v 1) (v 2) (v 3) (v 4) (v 5) * v 0)
      (by unfold deltaA; fun_prop) _ bX) (fun t w => by simp)
  have bsY : BoundedProc (fun t w =>
      YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) * Y t w) :=
    bdd_congr (bdd_of_continuous
      (fun v => YstarA α β θ ω σ sC Φ (v 1) (v 2) (v 3) (v 4) (v 5) * v 0)
      (by unfold YstarA YnA; fun_prop) _ bX) (fun t w => by simp)
  have bs2 : BoundedProc (fun t w =>
      YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) ^ 2) :=
    bdd_congr (bdd_of_continuous
      (fun v => YstarA α β θ ω σ sC Φ (v 1) (v 2) (v 3) (v 4) (v 5) ^ 2)
      (by unfold YstarA YnA; fun_prop) _ bX) (fun t w => by simp)
  have sY := hasSum_dsum 𝔼 hβ hYb w
  have sY2 := hasSum_dsum 𝔼 hβ bY2 w
  have spi2 := hasSum_dsum 𝔼 hβ bpi2 w
  have sgY := hasSum_dsum 𝔼 hβ bgY w
  have sqY := hasSum_dsum 𝔼 hβ bqY w
  have sYn := hasSum_dsum 𝔼 hβ bYn w
  have sdY := hasSum_dsum 𝔼 hβ bdY w
  have ssY := hasSum_dsum 𝔼 hβ bsY w
  have ss2 := hasSum_dsum 𝔼 hβ bs2 w
  -- (B) the loss of Proposition 6.14 in terms of the sums
  have eL : dsum 𝔼 β (loss614 κ θ Φ ω σ infl Y (fun t w => G t w + sC * cb t w) q) w =
      dsum 𝔼 β (fun t w => infl t w ^ 2) w + lamYY κ θ Φ ω σ * dsum 𝔼 β (fun t => Y t ^ 2) w
        - 2 * (κ / θ / ((1 - Φ) * (ω + σ))) * (Φ * dsum 𝔼 β Y w
          + σ * dsum 𝔼 β (fun t => (fun t w => G t w + sC * cb t w) t * Y t) w
          + (1 - Φ) * ω * dsum 𝔼 β (fun t => q t * Y t) w) := by
    refine HasSum.tsum_eq ?_
    have := (spi2.add (sY2.mul_left (lamYY κ θ Φ ω σ))).sub
      ((((sY.mul_left Φ).add (sgY.mul_left σ)).add (sqY.mul_left ((1 - Φ) * ω))).mul_left
        (2 * (κ / θ / ((1 - Φ) * (ω + σ)))))
    convert this using 1
    funext t
    have hf : loss614 κ θ Φ ω σ infl Y (fun t w => G t w + sC * cb t w) q t =
        (fun w => infl t w ^ 2) + lamYY κ θ Φ ω σ • (Y t ^ 2)
        - (2 * (κ / θ / ((1 - Φ) * (ω + σ))) * Φ) • Y t
        - (2 * (κ / θ / ((1 - Φ) * (ω + σ))) * σ) • ((fun t w => G t w + sC * cb t w) t * Y t)
        - (2 * (κ / θ / ((1 - Φ) * (ω + σ))) * ((1 - Φ) * ω)) • (q t * Y t) := by
      funext x
      simp only [loss614, gamT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply,
        Pi.pow_apply, smul_eq_mul]
      ring
    rw [hf]
    simp only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  -- (C) the first term of (5.4)
  have eP1 : dsum 𝔼 β (fun t w => Y t w -
      YnA ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w)) w =
      dsum 𝔼 β Y w - dsum 𝔼 β (fun t w => YnA ω σ sC (G t w) (cb t w) (q t w) (muw t w)
        (tau t w)) w := by
    refine HasSum.tsum_eq ?_
    convert sY.sub sYn using 1
    funext t
    have : (fun w => Y t w - YnA ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w)) =
        Y t - (fun w => YnA ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w)) := rfl
    dsimp only
    rw [this, map_sub, Pi.sub_apply]
    ring
  -- (D) the new loss
  have eLt : dsum 𝔼 β (loss615 α β θ ω σ sC Φ infl Y G cb q muw tau) w =
      dsum 𝔼 β (fun t w => infl t w ^ 2) w + lt * (dsum 𝔼 β (fun t => Y t ^ 2) w
        - 2 * dsum 𝔼 β (fun t w =>
          YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) * Y t w) w
        + dsum 𝔼 β (fun t w =>
          YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) ^ 2) w) := by
    refine HasSum.tsum_eq ?_
    have := spi2.add (((sY2.sub (ssY.mul_left 2)).add ss2).mul_left lt)
    convert this using 1
    funext t
    have hf : loss615 α β θ ω σ sC Φ infl Y G cb q muw tau t =
        (fun w => infl t w ^ 2) + lt • (Y t ^ 2) - (lt * 2) • (fun w =>
          YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) * Y t w)
        + lt • (fun w =>
          YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) ^ 2) := by
      funext x
      simp only [loss615, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.pow_apply,
        smul_eq_mul, hlt]
      ring
    rw [hf]
    simp only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  -- (E) completing the square, summed: `N ∑ Ŷ*Ŷ = ∑ γ̃Ŷ + (γ̄/κ) ∑ δŶ`
  have hE : (lamYY κ θ Φ ω σ + gb * muY α β θ ω σ sC) * dsum 𝔼 β (fun t w =>
        YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) * Y t w) w =
      κ / θ / ((1 - Φ) * (ω + σ)) * (σ * dsum 𝔼 β (fun t =>
          (fun t w => G t w + sC * cb t w) t * Y t) w
        + (1 - Φ) * ω * dsum 𝔼 β (fun t => q t * Y t) w)
      + gb * dsum 𝔼 β (fun t w =>
          deltaA α β θ ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w) * Y t w) w := by
    have h1 := ssY.mul_left (lamYY κ θ Φ ω σ + gb * muY α β θ ω σ sC)
    have h2 := ((sgY.mul_left σ).add (sqY.mul_left ((1 - Φ) * ω))).mul_left
      (κ / θ / ((1 - Φ) * (ω + σ)))
    have h3 := sdY.mul_left gb
    refine h1.unique ?_
    convert h2.add h3 using 1
    · funext t
      have hpt : (fun w => (lamYY κ θ Φ ω σ + gb * muY α β θ ω σ sC) *
          (YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) * Y t w)) =
          (κ / θ / ((1 - Φ) * (ω + σ)) * σ) • ((fun t w => G t w + sC * cb t w) t * Y t) +
          (κ / θ / ((1 - Φ) * (ω + σ)) * ((1 - Φ) * ω)) • (q t * Y t) +
          gb • (fun w =>
            deltaA α β θ ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w) * Y t w) := by
        funext x
        have hy := ystar_eq (β := β) hα0 hα1 hβ1 hθ0 hω hσ hs hΦ0 hΦ hMd (G t x) (cb t x)
          (q t x) (muw t x) (tau t x)
        simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
        rw [← mul_assoc, hy]
        ring
      have hE0 := congrArg (fun X => 𝔼.E 0 X w) hpt
      simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hE0
      have hl : 𝔼.E 0 (fun w => (lamYY κ θ Φ ω σ + gb * muY α β θ ω σ sC) *
          (YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) * Y t w)) w =
          (lamYY κ θ Φ ω σ + gb * muY α β θ ω σ sC) * 𝔼.E 0 (fun w =>
            YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) * Y t w) w := by
        have : (fun w => (lamYY κ θ Φ ω σ + gb * muY α β θ ω σ sC) *
            (YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) * Y t w)) =
            (lamYY κ θ Φ ω σ + gb * muY α β θ ω σ sC) • (fun w =>
              YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) * Y t w) :=
          rfl
        rw [this, map_smul, Pi.smul_apply, smul_eq_mul]
      rw [hl] at hE0
      linear_combination (β ^ t) * hE0
  -- (F) the weight
  have hF := lamTilde_eq (β := β) (sC := sC) hα0 hα1 hθ0 hω hσ hs hΦ0 hΦ
  rw [← hlt, ← hgb, ← hκ] at hF
  -- assemble
  rw [h614, eL, h54, eP1, eLt]
  unfold OmegaTilde
  have e1 : dsum 𝔼 β (fun t => infl t ^ 2) w = dsum 𝔼 β (fun t w => infl t w ^ 2) w := rfl
  have e2 : dsum 𝔼 β (fun t w => Y t w ^ 2) w = dsum 𝔼 β (fun t => Y t ^ 2) w := rfl
  rw [e1, e2]
  have hgk : gb * κ = κ / θ / ((1 - Φ) * (ω + σ)) * Φ := by
    rw [hgb]; unfold gbarC; field_simp
  have hbg : 1 + Φ * (1 + ω) / ((1 - Φ) * (ω + σ)) = 1 + gb * (θ * (1 + ω)) := by
    rw [hgb]; unfold gbarC; field_simp
  rw [hbg]
  linear_combination (Om * (dsum 𝔼 β (fun t => Y t ^ 2) w - 2 * dsum 𝔼 β (fun t w =>
      YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) * Y t w) w)) * hF
    + (-2 * Om) * hE + (-2 * Om * dsum 𝔼 β Y w) * hgk

/-! #### The log-deviation Calvo conditions from levels -/

/-- Woodford (2003), Chapter 3 (restated): the Calvo price index
`P_t^{1−θ} = αP_{t−1}^{1−θ} + (1−α)(p*_t)^{1−θ}` (in logs `lP`, `lp*`) is `PriceIndexEq` with
`π_t = lP_t − lP_{t−1}` and `x_t = lp*_t − lP_t`. -/
theorem priceIndex_of_levels {α θ lP lPm lps : ℝ}
    (h : Real.exp ((1 - θ) * lP) =
      α * Real.exp ((1 - θ) * lPm) + (1 - α) * Real.exp ((1 - θ) * lps)) :
    α * (Real.exp ((θ - 1) * (lP - lPm)) - 1) + (1 - α) * (Real.exp (-((θ - 1) * (lps - lP))) - 1)
      = 0 := by
  have e1 : Real.exp ((θ - 1) * (lP - lPm)) =
      Real.exp ((1 - θ) * lPm) / Real.exp ((1 - θ) * lP) := by
    rw [← Real.exp_sub]; ring_nf
  have e2 : Real.exp (-((θ - 1) * (lps - lP))) =
      Real.exp ((1 - θ) * lps) / Real.exp ((1 - θ) * lP) := by
    rw [← Real.exp_sub]; ring_nf
  rw [e1, e2]
  have hp := Real.exp_pos ((1 - θ) * lP)
  field_simp
  linear_combination -h

/-- Woodford (2003), Chapter 3 (restated): the reset-price condition `K_t = x_t^{1+ωθ} F_t` in
levels, with `K_t = K̄e^{K̂_t}`, `F_t = K̄e^{F̂_t}` (steady state `K̄ = F̄ > 0`) and
`x_t = e^{x̂_t}`,
is `ResetPriceEq`: `(1+ωθ)x̂_t = K̂_t − F̂_t`. -/
theorem resetPrice_of_levels {ω θ Kb Kh Fh xh : ℝ} (hK : 0 < Kb)
    (h : Kb * Real.exp Kh = Real.exp xh ^ (1 + ω * θ) * (Kb * Real.exp Fh)) :
    (1 + ω * θ) * xh = Kh - Fh := by
  rw [← Real.exp_mul, mul_comm (Real.exp _), mul_assoc, ← Real.exp_add] at h
  have h2 := mul_left_cancel₀ hK.ne' h
  have := Real.exp_injective h2
  linarith

/-- Woodford (2003), Chapter 3 (restated): the level recursion
`F_t = f_t + αβ E_t[Π_{t+1}^{e} F_{t+1}]` with `F_t = F̄e^{F̂_t}`, `f_t = f̄e^{f̂_t}` and the steady
state `F̄ = f̄/(1−αβ)` (`f̄ ≠ 0`, `αβ ≠ 1`) is exactly `RecEq`. -/
theorem recEq_of_levels {α β e fb : ℝ} (hf : fb ≠ 0) (hab : 1 - α * β ≠ 0)
    {infl F f : ℕ → Ω → ℝ}
    (h : ∀ t, (fun w => fb / (1 - α * β) * Real.exp (F t w)) =
      (fun w => fb * Real.exp (f t w)) + (α * β) • 𝔼.E t (fun w =>
        Real.exp (e * infl (t + 1) w) * (fb / (1 - α * β) * Real.exp (F (t + 1) w)))) :
    RecEq 𝔼 α β e infl F f := by
  intro t
  have ht := h t
  have hfun : (fun w => Real.exp (e * infl (t + 1) w) * (fb / (1 - α * β) * Real.exp (F (t + 1) w)))
      = (fb / (1 - α * β)) • ((fun w => Real.exp (e * infl (t + 1) w + F (t + 1) w) - 1) +
        fun _ => 1) := by
    funext w
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Real.exp_add]
    ring
  rw [hfun, map_smul, map_add, 𝔼.const] at ht
  funext w
  have hw := congrFun ht w
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hw ⊢
  have hk : fb / (1 - α * β) ≠ 0 := div_ne_zero hf hab
  field_simp at hw
  field_simp
  linear_combination hw

/-! ### (5.10), the coefficients `ω₁, ω₂, ω₃`, special cases and the cost-push term (5.11) -/

/-- Woodford (2003), eq. (5.10), p. 460: the condition
`Φ_y(s_C⁻¹ − 1)σ⁻¹/(ω + σ⁻¹) < ω + (1 − Φ_y)σ⁻¹ + Φ_y`. -/
def Cond510 (ω σ sC Φ : ℝ) : Prop :=
  Φ * (1 / sC - 1) * σ / (ω + σ) < ω + (1 - Φ) * σ + Φ

/-- Woodford (2003), p. 460: `λ̃ > 0` iff (5.10) (for `κ, θ > 0`, `ω, σ⁻¹ > 0`, `0 ≤ Φ_y < 1`). -/
theorem lamTilde_pos_iff {α β θ ω σ sC Φ : ℝ} (hκ : 0 < calvoKappa α β ω θ σ) (hθ : 0 < θ)
    (hω : 0 < ω) (hσ : 0 < σ) (hΦ0 : 0 ≤ Φ) (hΦ : Φ < 1) :
    0 < lamTilde α β θ ω σ sC Φ ↔ Cond510 ω σ sC Φ := by
  have hc : 0 < ω + σ := by linarith
  have hD : 0 < ω + σ + Φ * (1 - σ) := by nlinarith
  unfold lamTilde Cond510
  rw [mul_pos_iff_of_pos_left (div_pos hκ hθ), sub_pos]
  rw [show Φ * (1 / sC - 1) / (ω + σ + Φ * (1 - σ)) * (σ / (ω + σ)) =
      (Φ * (1 / sC - 1) * σ / (ω + σ)) / (ω + σ + Φ * (1 - σ)) by field_simp]
  rw [div_lt_one hD]
  constructor <;> intro h <;> linarith

/-- Woodford (2003), p. 460: (5.10) is equivalent to `M > 0` (`M = Mden`). -/
theorem Mden_pos_iff {ω σ sC Φ : ℝ} :
    0 < Mden ω σ sC Φ ↔ Cond510 ω σ sC Φ := by
  unfold Mden Cond510
  constructor <;> intro h <;> nlinarith

/-- Woodford (2003), p. 460: "this condition necessarily holds for all `Φ_y` small enough". -/
theorem cond510_eventually_phi {ω σ sC : ℝ} (hω : 0 < ω) (hσ : 0 < σ) :
    ∀ᶠ Φ in 𝓝 (0 : ℝ), Cond510 ω σ sC Φ := by
  unfold Cond510
  refine ContinuousAt.eventually_lt (f := fun Φ => Φ * (1 / sC - 1) * σ / (ω + σ))
    (g := fun Φ => ω + (1 - Φ) * σ + Φ) (by fun_prop) (by fun_prop) ?_
  simp only [zero_mul, zero_div, sub_zero, one_mul, add_zero]
  linarith

/-- Woodford (2003), p. 460: (5.10) holds "for all values of `s_C` close enough to one". -/
theorem cond510_eventually_sC {ω σ Φ : ℝ} (hω : 0 < ω) (hσ : 0 < σ) (hΦ0 : 0 ≤ Φ)
    (hΦ : Φ < 1) : ∀ᶠ s in 𝓝 (1 : ℝ), Cond510 ω σ s Φ := by
  unfold Cond510
  have hcont : ContinuousAt (fun s : ℝ => Φ * (1 / s - 1) * σ / (ω + σ)) 1 := by
    have : ContinuousAt (fun s : ℝ => 1 / s) 1 :=
      continuousAt_const.div continuousAt_id (by norm_num)
    exact (((continuousAt_const.mul (this.sub continuousAt_const)).mul continuousAt_const).div
      continuousAt_const (by linarith))
  refine ContinuousAt.eventually_lt (f := fun s : ℝ => Φ * (1 / s - 1) * σ / (ω + σ))
    (g := fun _ => ω + (1 - Φ) * σ + Φ) hcont continuousAt_const ?_
  simp only [div_one, sub_self, mul_zero, zero_mul, zero_div]
  nlinarith

/-- Woodford (2003), p. 460: under (5.10), `ω₁ ≥ 1` (for `0 ≤ Φ_y < 1`, `0 < s_C ≤ 1`). -/
theorem omega1_ge_one {α β θ ω σ sC Φ : ℝ} (hκ : 0 < calvoKappa α β ω θ σ) (hθ : 0 < θ)
    (hω : 0 < ω) (hσ : 0 < σ) (hs0 : 0 < sC) (hs1 : sC ≤ 1) (hΦ0 : 0 ≤ Φ) (hΦ : Φ < 1)
    (h : Cond510 ω σ sC Φ) : 1 ≤ omega1 α β θ ω σ sC Φ := by
  have hc : 0 < ω + σ := by linarith
  have hD : 0 < ω + σ + Φ * (1 - σ) := by nlinarith
  have hM := (Mden_pos_iff (ω := ω) (σ := σ) (sC := sC) (Φ := Φ)).mpr h
  rw [omega1_eq hκ.ne' hθ.ne' hc.ne' hD.ne' hM.ne', le_div_iff₀ hM, one_mul]
  unfold Mden
  have : 0 ≤ Φ * (1 / sC - 1) * σ / (ω + σ) := by
    apply div_nonneg _ hc.le
    apply mul_nonneg (mul_nonneg hΦ0 _) hσ.le
    rw [sub_nonneg, le_div_iff₀ hs0]; linarith
  linarith

/-- Woodford (2003), p. 462 ("In the case that `Ḡ > 0`, moreover, `ω₁ > 1`"), made precise:
under (5.10), `ω₁ > 1` iff `Φ_y > 0` and `s_C < 1`. (At `Φ_y = 0`, `ω₁ = 1` even when `Ḡ > 0`;
the book's statement presumes `Φ_y > 0`.) -/
theorem omega1_gt_one_iff {α β θ ω σ sC Φ : ℝ} (hκ : 0 < calvoKappa α β ω θ σ) (hθ : 0 < θ)
    (hω : 0 < ω) (hσ : 0 < σ) (hs0 : 0 < sC) (hs1 : sC ≤ 1) (hΦ0 : 0 ≤ Φ) (hΦ : Φ < 1)
    (h : Cond510 ω σ sC Φ) : 1 < omega1 α β θ ω σ sC Φ ↔ 0 < Φ ∧ sC < 1 := by
  have hc : 0 < ω + σ := by linarith
  have hD : 0 < ω + σ + Φ * (1 - σ) := by nlinarith
  have hM := (Mden_pos_iff (ω := ω) (σ := σ) (sC := sC) (Φ := Φ)).mpr h
  rw [omega1_eq hκ.ne' hθ.ne' hc.ne' hD.ne' hM.ne', lt_div_iff₀ hM, one_mul]
  unfold Mden
  rw [show Φ * (1 / sC - 1) * σ / (ω + σ) = Φ * σ * (1 - sC) / (sC * (ω + σ)) by
    field_simp]
  have hsc : 0 < sC * (ω + σ) := mul_pos hs0 hc
  constructor
  · intro hlt
    have hpos : 0 < Φ * σ * (1 - sC) / (sC * (ω + σ)) := by linarith
    rw [div_pos_iff_of_pos_right hsc] at hpos
    refine ⟨?_, ?_⟩
    · by_contra hn
      have : Φ = 0 := le_antisymm (not_lt.mp hn) hΦ0
      rw [this] at hpos; simp at hpos
    · by_contra hn
      have : sC = 1 := le_antisymm hs1 (not_lt.mp hn)
      rw [this] at hpos; simp at hpos
  · rintro ⟨hp, hs⟩
    have : 0 < Φ * σ * (1 - sC) / (sC * (ω + σ)) :=
      div_pos (mul_pos (mul_pos hp hσ) (by linarith)) hsc
    linarith

/-- Woodford (2003), p. 460: under (5.10), `ω₂ > 0` for any `0 < Φ_y < 1`. -/
theorem omega2_pos {ω σ sC Φ : ℝ} (hω : 0 < ω) (hσ : 0 < σ) (hs0 : 0 < sC) (hΦ0 : 0 < Φ)
    (h : Cond510 ω σ sC Φ) : 0 < omega2 ω σ sC Φ := by
  have hc : 0 < ω + σ := by linarith
  have hM := (Mden_pos_iff (ω := ω) (σ := σ) (sC := sC) (Φ := Φ)).mpr h
  rw [omega2_eq hc.ne']
  exact div_pos (mul_pos (mul_pos hΦ0 (by positivity)) hσ) (mul_pos hc hM)

/-- Woodford (2003), p. 460: under (5.10), `ω₃ > 0` for `Φ_y < 1`. -/
theorem omega3_pos {ω σ sC Φ : ℝ} (hΦ : Φ < 1)
    (h : Cond510 ω σ sC Φ) : 0 < omega3 ω σ sC Φ := by
  have hM := (Mden_pos_iff (ω := ω) (σ := σ) (sC := sC) (Φ := Φ)).mpr h
  rw [omega3_eq]
  exact div_pos (by linarith) hM

/-- Woodford (2003), p. 461: when `Φ_y = 0`, `λ̃ = κ/θ`, `ω₁ = 1`, `ω₂ = 0`,
`ω₃ = (ω + σ⁻¹)⁻¹`. -/
theorem phi_zero_case {α β θ ω σ sC : ℝ} (hκ : calvoKappa α β ω θ σ ≠ 0) (hθ : θ ≠ 0) :
    lamTilde α β θ ω σ sC 0 = calvoKappa α β ω θ σ / θ ∧ omega1 α β θ ω σ sC 0 = 1 ∧
      omega2 ω σ sC 0 = 0 ∧ omega3 ω σ sC 0 = (ω + σ)⁻¹ := by
  refine ⟨by unfold lamTilde; simp, ?_, by unfold omega2; simp, by unfold omega3; simp⟩
  unfold omega1 lamTilde
  simp only [zero_mul, zero_div, sub_zero, mul_one]
  field_simp

/-- Woodford (2003), p. 461: when `Ḡ = 0` (`s_C = 1`), `λ̃ = κ/θ` and `ω₁ = 1`. -/
theorem sC_one_case {α β θ ω σ Φ : ℝ} (hκ : calvoKappa α β ω θ σ ≠ 0) (hθ : θ ≠ 0) :
    lamTilde α β θ ω σ 1 Φ = calvoKappa α β ω θ σ / θ ∧ omega1 α β θ ω σ 1 Φ = 1 := by
  refine ⟨by unfold lamTilde; simp, ?_⟩
  unfold omega1 lamTilde
  simp only [div_one, sub_self, mul_zero, zero_div, zero_mul, sub_zero, mul_one]
  field_simp

/-- Woodford (2003), eq. (5.11), p. 461: the cost-push term
`u_t = κ(Ŷ*_t − Ŷⁿ_t) = κ(ω₁ − 1)Ŷⁿ_t − κω₂Ĝ_t + κω₃μ̂_t` (`− κτ̂_t/M` for a revenue-tax
wedge). -/
noncomputable def costPush511 (α β θ ω σ sC Φ G cb q muw tau : ℝ) : ℝ :=
  calvoKappa α β ω θ σ * (YstarA α β θ ω σ sC Φ G cb q muw tau - YnA ω σ sC G cb q muw tau)

/-- Woodford (2003), eq. (5.11): the expanded form of the cost-push term. -/
theorem costPush511_eq (α β θ ω σ sC Φ G cb q muw tau : ℝ) :
    costPush511 α β θ ω σ sC Φ G cb q muw tau =
      calvoKappa α β ω θ σ * (omega1 α β θ ω σ sC Φ - 1) * YnA ω σ sC G cb q muw tau
        - calvoKappa α β ω θ σ * omega2 ω σ sC Φ * G + calvoKappa α β ω θ σ * omega3 ω σ sC Φ * muw
        - calvoKappa α β ω θ σ * tau / Mden ω σ sC Φ := by
  unfold costPush511 YstarA; ring

/-- Woodford (2003), eq. (5.11), p. 461: in terms of the welfare-relevant gap `x_t = Ŷ_t − Ŷ*_t`
the AS relation (4.35) `π_t = κ(Ŷ_t − Ŷⁿ_t) + βE_tπ_{t+1}` is EXACTLY (4.38)
`π_t = κx_t + βE_tπ_{t+1} + u_t` with the cost-push term (5.11). -/
theorem as_gap_511 {α β θ ω σ sC Φ : ℝ} {infl Y G cb q muw tau : ℕ → Ω → ℝ} :
    CostPush.ASNatural 𝔼 (calvoKappa α β ω θ σ) β infl Y
        (fun t w => YnA ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w)) ↔
      CostPush.ASGap 𝔼 (calvoKappa α β ω θ σ) β infl
        (fun t w => Y t w - YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w))
        (fun t w => costPush511 α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w)) := by
  have key : ∀ t, calvoKappa α β ω θ σ • (Y t - fun w => YnA ω σ sC (G t w) (cb t w) (q t w)
      (muw t w) (tau t w)) = calvoKappa α β ω θ σ • (fun w => Y t w -
        YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w)) +
        fun w => costPush511 α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w) := by
    intro t; funext w
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, costPush511]
    ring
  constructor
  · intro h t; rw [h t, key t]; abel
  · intro h t; rw [h t, key t]; abel

/-- Woodford (2003), p. 461: when `Φ_y = 0` the cost-push term (5.11) reduces to (4.39),
`u_t = κ(μ̂ʷ_t − τ̂_t)/(ω + σ⁻¹)` (`μ̂ = μ̂ʷ − τ̂` the composite markup). -/
theorem costPush511_phi_zero {α β θ ω σ sC : ℝ} (hκ : calvoKappa α β ω θ σ ≠ 0) (hθ : θ ≠ 0)
    (hc : ω + σ ≠ 0) (G cb q muw tau : ℝ) :
    costPush511 α β θ ω σ sC 0 G cb q muw tau = calvoKappa α β ω θ σ * (muw - tau) / (ω + σ) := by
  rw [costPush511_eq]
  obtain ⟨_, h1, h2, h3⟩ := phi_zero_case (sC := sC) hκ hθ
  rw [h1, h2, h3]
  unfold Mden
  simp only [zero_mul, zero_div, sub_zero, add_zero]
  field_simp
  ring

/-- Woodford (2003), p. 461: when `Ḡ = 0` (`s_C = 1`), `ω₁ = 1` and
`u_t = −κω₂Ĝ_t + κω₃μ̂_t` (`− κτ̂_t/M`): only government purchases (and wedges) create a
cost-push term. -/
theorem costPush511_sC_one {α β θ ω σ Φ : ℝ} (hκ : calvoKappa α β ω θ σ ≠ 0) (hθ : θ ≠ 0)
    (G cb q muw tau : ℝ) :
    costPush511 α β θ ω σ 1 Φ G cb q muw tau =
      -(calvoKappa α β ω θ σ * omega2 ω σ 1 Φ * G) + calvoKappa α β ω θ σ * omega3 ω σ 1 Φ * muw
        - calvoKappa α β ω θ σ * tau / Mden ω σ 1 Φ := by
  rw [costPush511_eq, (sC_one_case (Φ := Φ) hκ hθ).2]
  ring

/-- Woodford (2003), (5.9), p. 460: `L̃_t = π_t² + λ̃x_t²` with the welfare-relevant gap
`x_t = Ŷ_t − Ŷ*_t`. -/
theorem loss615_gap (α β θ ω σ sC Φ : ℝ) (infl Y G cb q muw tau : ℕ → Ω → ℝ) (t : ℕ) (w : Ω) :
    loss615 α β θ ω σ sC Φ infl Y G cb q muw tau t w =
      infl t w ^ 2 + lamTilde α β θ ω σ sC Φ *
        (Y t w - YstarA α β θ ω σ sC Φ (G t w) (cb t w) (q t w) (muw t w) (tau t w)) ^ 2 := rfl

/-- Woodford (2003), p. 456: `Ỹ_t` is linear in the disturbances (hence mean zero when they
are). -/
theorem Ytil_linear (Φ ω σ g q : ℝ) :
    Ytil Φ ω σ g q = σ / (ω + σ - Φ * (1 + ω)) * g + (1 - Φ) * ω / (ω + σ - Φ * (1 + ω)) * q := by
  unfold Ytil; ring

/-- The Layer-A scaling of the remainders passes through conditional expectations:
`E_t(s³X) = s³E_tX`. -/
theorem E_scaling (t : ℕ) (s : ℝ) (X : Ω → ℝ) :
    𝔼.E t (fun w => s ^ 3 * X w) = s ^ 3 • 𝔼.E t X := by
  rw [show (fun w => s ^ 3 * X w) = s ^ 3 • X from rfl, map_smul]

/-! ### The Calvo reset-price problem (restated from the Woodford Chapter 3 project) -/

/-- Woodford (2003), eq. (2.2), p. 178 (**the reset-price objective**): the genuine infinite
discounted sum `∑_{k ≥ 0} αᵏ E_t[Q_{t,t+k} Π(p, p^I_{t+k}, P_{t+k}; Y_{t+k}, ξ̃_{t+k})]`, where
`prof k ω p` is the horizon-`k` nominal profit (1.17) at the state `ω` when the price is `p`,
and `Q k` is the stochastic discount factor `Q_{t,t+k}`. -/
noncomputable def resetObjective (α : ℝ) (Q : ℕ → Ω → ℝ) (prof : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (p : ℝ) : Ω → ℝ :=
  fun ω => ∑' k, α ^ k * 𝔼.E t (fun ω' => Q k ω' * prof k ω' p) ω

/-- Woodford (2003), eq. (2.3), p. 179: the left-hand side of the first-order condition,
`∑_{k ≥ 0} αᵏ E_t[Q_{t,t+k} Π₁(p, …)]`, where `dprof k ω p` is the marginal profit `Π₁`. -/
noncomputable def resetFOC (α : ℝ) (Q : ℕ → Ω → ℝ) (dprof : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (p : ℝ) : Ω → ℝ :=
  fun ω => ∑' k, α ^ k * 𝔼.E t (fun ω' => Q k ω' * dprof k ω' p) ω

/-- Woodford (2003), p. 179 (differentiating (2.2) under `E_t`; restated from the Woodford Chapter 3
project): if the second-order remainder of `z ↦ g z` at `x` is bounded by `C h²` uniformly in the
state, then `z ↦ E_t[g z]` has derivative `E_t[g']` at `x`. -/
theorem hasDerivAt_E_of_remainder {g : ℝ → Ω → ℝ} {g' : Ω → ℝ} {x C δ : ℝ} (hδ : 0 < δ)
    (hrem : ∀ h, |h| < δ → ∀ ω, |g (x + h) ω - g x ω - h * g' ω| ≤ C * h ^ 2)
    (t : ℕ) (ω : Ω) :
    HasDerivAt (fun z => 𝔼.E t (g z) ω) (𝔼.E t g' ω) x := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun h => 𝔼.E t (g (x + h)) ω - 𝔼.E t (g x) ω - h • 𝔼.E t g' ω)
      =O[𝓝 0] fun h : ℝ => h ^ 2 := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
    have hh' : |h| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hh
    have key : 𝔼.E t (g (x + h)) ω - 𝔼.E t (g x) ω - h • 𝔼.E t g' ω
        = 𝔼.E t (g (x + h) - g x - h • g') ω := by
      simp [map_sub, map_smul]
    rw [key, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, sq_abs]
    exact 𝔼.abs_E_le (fun ω' => by simpa [smul_eq_mul] using hrem h hh' ω') t ω
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two)

omit 𝔼 in
/-- Woodford (2003), p. 179 (restated from the Woodford Chapter 3 project): a Lipschitz bound on
the derivative bounds the second-order remainder, `|f(x+h) − f(x) − h f'(x)| ≤ L h²`. -/
theorem remainder_le_of_lipschitz_deriv {f f' : ℝ → ℝ} {x r L : ℝ} (hL0 : 0 ≤ L)
    (hf : ∀ y ∈ Metric.ball x r, HasDerivAt f (f' y) y)
    (hL : ∀ y ∈ Metric.ball x r, |f' y - f' x| ≤ L * |y - x|) {h : ℝ} (hh : |h| < r) :
    |f (x + h) - f x - h * f' x| ≤ L * h ^ 2 := by
  have hsub : Metric.closedBall x |h| ⊆ Metric.ball x r :=
    Metric.closedBall_subset_ball hh
  have hd : ∀ y ∈ Metric.closedBall x |h|,
      HasDerivWithinAt (fun z => f z - z * f' x) (f' y - f' x) (Metric.closedBall x |h|) y := by
    intro y hy
    have h1 := hf y (hsub hy)
    have h2 : HasDerivAt (fun z : ℝ => z * f' x) (f' x) y := by
      simpa using (hasDerivAt_id y).mul_const (f' x)
    exact (HasDerivAt.sub h1 h2).hasDerivWithinAt
  have hb : ∀ y ∈ Metric.closedBall x |h|, ‖f' y - f' x‖ ≤ L * |h| := by
    intro y hy
    rw [Real.norm_eq_abs]
    refine (hL y (hsub hy)).trans (mul_le_mul_of_nonneg_left ?_ hL0)
    simpa [Metric.mem_closedBall, Real.dist_eq] using hy
  have hx : x ∈ Metric.closedBall x |h| := Metric.mem_closedBall_self (abs_nonneg h)
  have hxh : x + h ∈ Metric.closedBall x |h| := by
    simp [Metric.mem_closedBall]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (convex_closedBall x |h|) hx hxh
  rw [Real.norm_eq_abs, Real.norm_eq_abs, add_sub_cancel_left] at this
  calc |f (x + h) - f x - h * f' x| = |f (x + h) - (x + h) * f' x - (f x - x * f' x)| := by
        ring_nf
    _ ≤ L * |h| * |h| := this
    _ = L * h ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- Woodford (2003), p. 179 (differentiation under `E_t`, Lipschitz form; restated from the Woodford
Chapter 3 project): if `z ↦ g z ω` has derivative `g' z ω` near `x`, Lipschitz at `x` uniformly in
the state, then `z ↦ E_t[g z]` has derivative `E_t[g' x]` at `x`. -/
theorem hasDerivAt_E {g g' : ℝ → Ω → ℝ} {x r L : ℝ} (hr : 0 < r) (hL0 : 0 ≤ L)
    (hg : ∀ y ∈ Metric.ball x r, ∀ ω, HasDerivAt (fun z => g z ω) (g' y ω) y)
    (hL : ∀ y ∈ Metric.ball x r, ∀ ω, |g' y ω - g' x ω| ≤ L * |y - x|) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun z => 𝔼.E t (g z) ω) (𝔼.E t (g' x) ω) x :=
  hasDerivAt_E_of_remainder 𝔼 hr (fun _ hh ω' => remainder_le_of_lipschitz_deriv hL0
    (fun y hy => hg y hy ω') (fun y hy => hL y hy ω') hh) t ω

/-- Woodford (2003), eqs. (2.2)–(2.3), p. 179 (term-by-term differentiation of a discounted sum
of conditional expectations; restated from the Woodford Chapter 3 project): `z ↦ ∑ₖ αᵏ E_t[gₖ z]`
has derivative `∑ₖ αᵏ E_t[g'ₖ x]` on an open interval `U`, provided each `g'ₖ` is locally
Lipschitz uniformly in the state and dominated by `uₖ` with `∑ |α|ᵏ uₖ < ∞`, and the series
converges at one point of `U`. -/
theorem hasDerivAt_tsum_E {α : ℝ} {g g' : ℕ → ℝ → Ω → ℝ} {U : Set ℝ} {u : ℕ → ℝ}
    (hU : IsOpen U) (hU' : IsPreconnected U)
    (hg : ∀ k, ∀ y ∈ U, ∀ ω, HasDerivAt (fun z => g k z ω) (g' k y ω) y)
    (hLip : ∀ k, ∀ y ∈ U, ∃ L, 0 ≤ L ∧ ∃ r > 0,
      ∀ z ∈ Metric.ball y r, ∀ ω, |g' k z ω - g' k y ω| ≤ L * |z - y|)
    (hdom : ∀ k, ∀ y ∈ U, ∀ ω, |g' k y ω| ≤ u k) (hu : Summable fun k => |α| ^ k * u k)
    {y₀ : ℝ} (hy₀ : y₀ ∈ U) (t : ℕ) (ω : Ω)
    (hs : Summable fun k => α ^ k * 𝔼.E t (g k y₀) ω) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (fun z => ∑' k, α ^ k * 𝔼.E t (g k z) ω)
      (∑' k, α ^ k * 𝔼.E t (g' k x) ω) x := by
  refine hasDerivAt_tsum_of_isPreconnected (u := fun k => |α| ^ k * u k)
    (g := fun k z => α ^ k * 𝔼.E t (g k z) ω) (g' := fun k z => α ^ k * 𝔼.E t (g' k z) ω)
    hu hU hU' (fun k y hy => ?_) (fun k y hy => ?_) hy₀ hs hx
  · obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.mp hU y hy
    obtain ⟨L, hL0, r, hr, hL⟩ := hLip k y hy
    have hsub : Metric.ball y (min r r₁) ⊆ Metric.ball y r₁ :=
      Metric.ball_subset_ball (min_le_right _ _)
    have hsub' : Metric.ball y (min r r₁) ⊆ Metric.ball y r :=
      Metric.ball_subset_ball (min_le_left _ _)
    exact (hasDerivAt_E 𝔼 (lt_min hr hr₁) hL0 (fun z hz ω' => hg k z (hball (hsub hz)) ω')
      (fun z hz ω' => hL z (hsub' hz) ω') t ω).const_mul (α ^ k)
  · rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hdom k y hy) t ω)
      (pow_nonneg (abs_nonneg α) k)

/-- Woodford (2003), eqs. (2.2)–(2.3), p. 179 (**the derivative of the reset-price objective**):
under local-Lipschitz and domination hypotheses on discounted marginal profits
`Q_{t,t+k} Π₁`, and convergence of (2.2) at one price, the objective (2.2) has derivative
`∑ₖ αᵏ E_t[Q_{t,t+k} Π₁(p, …)]` at every price of an open interval `U`. -/
theorem hasDerivAt_resetObjective {α : ℝ} {Q : ℕ → Ω → ℝ} {prof dprof : ℕ → Ω → ℝ → ℝ}
    {U : Set ℝ} (hU : IsOpen U) (hU' : IsPreconnected U)
    (hprof : ∀ k ω, ∀ y ∈ U, HasDerivAt (prof k ω) (dprof k ω y) y)
    (hLip : ∀ k, ∀ y ∈ U, ∃ L, 0 ≤ L ∧ ∃ r > 0, ∀ z ∈ Metric.ball y r, ∀ ω,
      |Q k ω * dprof k ω z - Q k ω * dprof k ω y| ≤ L * |z - y|)
    {u : ℕ → ℝ} (hdom : ∀ k, ∀ y ∈ U, ∀ ω, |Q k ω * dprof k ω y| ≤ u k)
    (hu : Summable fun k => |α| ^ k * u k) {y₀ : ℝ} (hy₀ : y₀ ∈ U) (t : ℕ) (ω : Ω)
    (hs : Summable fun k => α ^ k * 𝔼.E t (fun ω' => Q k ω' * prof k ω' y₀) ω)
    {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (fun p => resetObjective 𝔼 α Q prof t p ω) (resetFOC 𝔼 α Q dprof t x ω) x :=
  hasDerivAt_tsum_E 𝔼 (g := fun k z ω' => Q k ω' * prof k ω' z)
    (g' := fun k z ω' => Q k ω' * dprof k ω' z) hU hU'
    (fun k y hy ω' => (hprof k ω' y hy).const_mul (Q k ω')) hLip hdom hu hy₀ t ω hs hx

/-- Woodford (2003), eq. (2.3), p. 179 (**the first-order condition is necessary**): if `p` is
a local maximum of the objective (2.2) at which it has the derivative of
`hasDerivAt_resetObjective`, then `∑ₖ αᵏ E_t[Q_{t,t+k} Π₁(p, …)] = 0`. -/
theorem foc_of_isLocalMax {α : ℝ} {Q : ℕ → Ω → ℝ} {prof dprof : ℕ → Ω → ℝ → ℝ} {t : ℕ}
    {ω : Ω} {x : ℝ}
    (hder : HasDerivAt (fun p => resetObjective 𝔼 α Q prof t p ω) (resetFOC 𝔼 α Q dprof t x ω) x)
    (hmax : IsLocalMax (fun p => resetObjective 𝔼 α Q prof t p ω) x) :
    resetFOC 𝔼 α Q dprof t x ω = 0 :=
  hmax.hasDerivAt_eq_zero hder

/-! ### The recursive forms of `F` and `K` from their infinite-sum definitions -/

/-- Woodford (2003), §5 (Benigno–Woodford): the cumulated price growth
`Π_{t,t+k}^a = (P_{t+k}/P_t)^a = exp(a(log P_{t+k} − log P_t))`. -/
noncomputable def growth (a : ℝ) (lP : ℕ → Ω → ℝ) (t k : ℕ) : Ω → ℝ :=
  fun w => Real.exp (a * (lP (t + k) w - lP t w))

/-- Woodford (2003), §5 (Benigno–Woodford): the genuine infinite-horizon sums
`F_t = E_t ∑_{k ≥ 0} (αβ)ᵏ f_{t+k} Π_{t,t+k}^{θ−1}` and
`K_t = E_t ∑ (αβ)ᵏ k_{t+k} Π_{t,t+k}^{θ(1+ω)}`
(with `a = θ − 1`, resp. `θ(1+ω)`), written as `∑ₖ (αβ)ᵏ E_t[x_{t+k} Π_{t,t+k}^a]`. -/
noncomputable def fwdSum (α β a : ℝ) (lP x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun w => ∑' k, (α * β) ^ k * 𝔼.E t (fun w' => x (t + k) w' * growth a lP t k w') w

omit 𝔼 in
/-- `Π_{t,t+k+1}^a = Π_{t,t+1}^a Π_{t+1,t+1+k}^a`. -/
theorem growth_succ (a : ℝ) (lP : ℕ → Ω → ℝ) (t k : ℕ) (w : Ω) :
    growth a lP t (k + 1) w = growth a lP t 1 w * growth a lP (t + 1) k w := by
  unfold growth
  rw [← Real.exp_add, show t + (k + 1) = t + 1 + k by omega]
  congr 1
  ring

omit 𝔼 in
/-- `Π_{t,t}^a = 1`. -/
theorem growth_zero (a : ℝ) (lP : ℕ → Ω → ℝ) (t : ℕ) (w : Ω) : growth a lP t 0 w = 1 := by
  simp [growth]

/-- Woodford (2003), §5 (Benigno–Woodford; by the tower property): for any `ExpectationSystem`
with the pull-out property, if `x_t` is known at `t`, `Π_{t,t+1}^a` is known at `t+1`, and the
discounted terms are dominated, `|x_{t+k} Π_{t,t+k}^a| ≤ Cρᵏ` with `0 ≤ αβρ < 1`, then the
infinite sum satisfies the recursion `F_t = x_t + αβ E_t[Π_{t,t+1}^a F_{t+1}]`. -/
theorem fwdSum_rec {α β a C ρ : ℝ} (hab0 : 0 ≤ α * β) (hρ0 : 0 ≤ ρ) (habρ : α * β * ρ < 1)
    {lP x : ℕ → Ω → ℝ} (hPO : 𝔼.PullOut) (hxa : ∀ t, 𝔼.E t (x t) = x t)
    (hgk : ∀ t, 𝔼.E (t + 1) (growth a lP t 1) = growth a lP t 1)
    (hdom : ∀ t k w, |x (t + k) w * growth a lP t k w| ≤ C * ρ ^ k) (t : ℕ) :
    fwdSum 𝔼 α β a lP x t =
      x t + (α * β) • 𝔼.E t (fun w => growth a lP t 1 w * fwdSum 𝔼 α β a lP x (t + 1) w) := by
  set q := α * β with hq
  set X : ℕ → ℕ → Ω → ℝ := fun s k w => x (s + k) w * growth a lP s k w with hX
  have hqρ0 : 0 ≤ q * ρ := mul_nonneg hab0 hρ0
  have hgeo : Summable (fun k : ℕ => C * (q * ρ) ^ k) :=
    (summable_geometric_of_lt_one hqρ0 habρ).mul_left C
  have hbound : ∀ s k w, |q ^ k * 𝔼.E s (X s k) w| ≤ C * (q * ρ) ^ k := by
    intro s k w
    rw [abs_mul, abs_of_nonneg (pow_nonneg hab0 k)]
    have := 𝔼.abs_E_le (fun w' => hdom s k w') s w
    calc q ^ k * |𝔼.E s (X s k) w| ≤ q ^ k * (C * ρ ^ k) :=
          mul_le_mul_of_nonneg_left this (pow_nonneg hab0 k)
      _ = C * (q * ρ) ^ k := by rw [mul_pow]; ring
  have hsum : ∀ s w, Summable (fun k => q ^ k * 𝔼.E s (X s k) w) := fun s w =>
    Summable.of_norm_bounded hgeo (fun k => by rw [Real.norm_eq_abs]; exact hbound s k w)
  -- the date-(t+1) sum, multiplied by `Π_{t,t+1}^a`, as one series
  have hX1 : ∀ k, growth a lP t 1 * X (t + 1) k = X t (k + 1) := by
    intro k; funext w
    change growth a lP t 1 w * (x (t + 1 + k) w * growth a lP (t + 1) k w) =
      x (t + (k + 1)) w * growth a lP t (k + 1) w
    rw [growth_succ a lP t k, show t + (k + 1) = t + 1 + k by omega]
    ring
  have hinner : (fun w => growth a lP t 1 w * fwdSum 𝔼 α β a lP x (t + 1) w) =
      fun w => ∑' k, q ^ k * 𝔼.E (t + 1) (X t (k + 1)) w := by
    funext w
    simp only [fwdSum]
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    have h := congrFun (hPO (t + 1) (growth a lP t 1) (X (t + 1) k) (hgk t)) w
    rw [hX1 k] at h
    simp only [Pi.mul_apply] at h
    rw [h]
    simp only [hX, hq]
    ring
  have hdomi : ∀ k w, |q ^ k * 𝔼.E (t + 1) (X t (k + 1)) w| ≤ C * ρ * (q * ρ) ^ k := by
    intro k w
    rw [abs_mul, abs_of_nonneg (pow_nonneg hab0 k)]
    have := 𝔼.abs_E_le (fun w' => hdom t (k + 1) w') (t + 1) w
    calc q ^ k * |𝔼.E (t + 1) (X t (k + 1)) w| ≤ q ^ k * (C * ρ ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left this (pow_nonneg hab0 k)
      _ = C * ρ * (q * ρ) ^ k := by rw [mul_pow]; ring
  have hgeo2 : Summable (fun k : ℕ => C * ρ * (q * ρ) ^ k) :=
    (summable_geometric_of_lt_one hqρ0 habρ).mul_left (C * ρ)
  funext w
  have hE := ForwardSolution.E_tsum_dom 𝔼 hgeo2
    (f := fun k w => q ^ k * 𝔼.E (t + 1) (X t (k + 1)) w) hdomi t w
  have hEk : ∀ k, 𝔼.E t (fun w => q ^ k * 𝔼.E (t + 1) (X t (k + 1)) w) w =
      q ^ k * 𝔼.E t (X t (k + 1)) w := by
    intro k
    have : (fun w => q ^ k * 𝔼.E (t + 1) (X t (k + 1)) w) = q ^ k • 𝔼.E (t + 1) (X t (k + 1)) :=
      rfl
    rw [this, map_smul, 𝔼.tower (Nat.le_succ t), Pi.smul_apply, smul_eq_mul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hinner, hE]
  simp_rw [hEk]
  -- split off the `k = 0` term
  have h0 : 𝔼.E t (X t 0) = x t := by
    have : X t 0 = x t := by
      funext w'; simp only [hX, Nat.add_zero, growth_zero, mul_one]
    rw [this, hxa t]
  simp only [fwdSum]
  rw [(hsum t w).tsum_eq_zero_add, pow_zero, one_mul]
  change 𝔼.E t (X t 0) w + _ = _
  rw [h0, ← tsum_mul_left]
  congr 1
  exact tsum_congr fun k => by simp only [hX]; ring

/-- Woodford (2003), §5 (Benigno–Woodford): the infinite-sum definition of `F` (or `K`) gives the
log-deviation recursion `RecEq` used in `CalvoModel.CalvoAS`, with
`π_{t+1} = log P_{t+1} − log P_t`,
`x_t = x̄e^{x̂_t}` and `F_t = (x̄/(1−αβ))e^{F̂_t}` (the steady state of the sum). -/
theorem recEq_of_fwdSum {α β a C ρ xb : ℝ} (hab0 : 0 ≤ α * β) (hρ0 : 0 ≤ ρ)
    (habρ : α * β * ρ < 1) (hxb : xb ≠ 0) (hab : 1 - α * β ≠ 0)
    {lP x infl Fh xh : ℕ → Ω → ℝ} (hPO : 𝔼.PullOut) (hxa : ∀ t, 𝔼.E t (x t) = x t)
    (hgk : ∀ t, 𝔼.E (t + 1) (growth a lP t 1) = growth a lP t 1)
    (hdom : ∀ t k w, |x (t + k) w * growth a lP t k w| ≤ C * ρ ^ k)
    (hinfl : ∀ t w, infl (t + 1) w = lP (t + 1) w - lP t w)
    (hx : ∀ t w, x t w = xb * Real.exp (xh t w))
    (hF : ∀ t w, fwdSum 𝔼 α β a lP x t w = xb / (1 - α * β) * Real.exp (Fh t w)) :
    RecEq 𝔼 α β a infl Fh xh := by
  refine recEq_of_levels 𝔼 hxb hab (fun t => ?_)
  have h := fwdSum_rec 𝔼 hab0 hρ0 habρ hPO hxa hgk hdom t
  have e1 : (fun w => xb / (1 - α * β) * Real.exp (Fh t w)) = fwdSum 𝔼 α β a lP x t := by
    funext w; rw [hF]
  have e2 : (fun w => xb * Real.exp (xh t w)) = x t := by funext w; rw [hx]
  have e3 : (fun w => Real.exp (a * infl (t + 1) w) *
      (xb / (1 - α * β) * Real.exp (Fh (t + 1) w))) =
      fun w => growth a lP t 1 w * fwdSum 𝔼 α β a lP x (t + 1) w := by
    funext w; rw [hF, hinfl]; simp [growth]
  rw [e1, e2, e3]
  exact h

/-! ### The reset-price condition `K = x^{1+ωθ}F` from the Calvo first-order condition -/

/-- Woodford (2003), Chapter 3 (1.17) under Assumption 6.2 (firm-specific labour): the nominal
profit at horizon `k` as a function of the log reset price `l`, with demand
`y = Y(p/P)^{−θ}` (`log y = lY − θ(l − lP)`), revenue tax `τ`, and cost `(P/u_c)μ ṽ(y)` with
`ṽ(y) = c_v y^{1+ω}` (`vtilde_iso`); its derivative in the price is the firm's marginal profit
at the equilibrium wage of its specific labour. -/
noncomputable def profIso (θ ω tau lY lP uc mu cv l : ℝ) : ℝ :=
  (1 - tau) * Real.exp (l + lY - θ * (l - lP)) -
    Real.exp lP / uc * mu * cv * Real.exp ((1 + ω) * (lY - θ * (l - lP)))

/-- The marginal profit `∂Π/∂ log p`. -/
noncomputable def dprofIso (θ ω tau lY lP uc mu cv l : ℝ) : ℝ :=
  (1 - tau) * (1 - θ) * Real.exp (l + lY - θ * (l - lP)) +
    θ * (1 + ω) * (Real.exp lP / uc * mu * cv) * Real.exp ((1 + ω) * (lY - θ * (l - lP)))

omit 𝔼 in
/-- Woodford (2003), eq. (2.3) ingredients: the derivative of the isoelastic profit. -/
theorem hasDerivAt_profIso (θ ω tau lY lP uc mu cv l : ℝ) :
    HasDerivAt (fun z => profIso θ ω tau lY lP uc mu cv z)
      (dprofIso θ ω tau lY lP uc mu cv l) l := by
  have h1 : HasDerivAt (fun z : ℝ => z + lY - θ * (z - lP)) (1 - θ) l := by
    have := HasDerivAt.sub ((hasDerivAt_id l).add_const lY)
      (((hasDerivAt_id l).sub_const lP).const_mul θ)
    exact this.congr_deriv (by ring)
  have h2 : HasDerivAt (fun z : ℝ => (1 + ω) * (lY - θ * (z - lP))) ((1 + ω) * (-θ)) l := by
    have := ((((hasDerivAt_id l).sub_const lP).const_mul θ).const_sub lY).const_mul (1 + ω)
    exact this.congr_deriv (by ring)
  have := HasDerivAt.sub ((h1.exp).const_mul (1 - tau))
    ((h2.exp).const_mul (Real.exp lP / uc * mu * cv))
  refine this.congr_deriv ?_
  unfold dprofIso
  ring

/-- Woodford (2003), p. 178: the stochastic discount factor for nominal payoffs
`Q_{t,t+k} = βᵏ (u_c(t+k)/P_{t+k})/(u_c(t)/P_t)`. -/
noncomputable def sdf (β : ℝ) (uc lP : ℕ → Ω → ℝ) (t k : ℕ) : Ω → ℝ :=
  fun w => β ^ k * (uc (t + k) w * Real.exp (-lP (t + k) w)) * (Real.exp (lP t w) / uc t w)

/-- Benigno–Woodford: the revenue term `f = (1−τ)u_c Y` of the reset-price condition. -/
noncomputable def fLev (tau uc lY : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun w => (1 - tau t w) * uc t w * Real.exp (lY t w)

/-- Benigno–Woodford: the cost term `k = (θ/(θ−1))μ Y ṽ_y(Y) = (θ/(θ−1))μ c_v(1+ω)Y^{1+ω}`. -/
noncomputable def kLev (θ ω : ℝ) (mu cv lY : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun w => θ / (θ - 1) * mu t w * cv t w * (1 + ω) * Real.exp ((1 + ω) * lY t w)

/-- The horizon-`k` discounted marginal profit of the reset problem (2.3). -/
noncomputable def dprofP (θ ω : ℝ) (tau lY lP uc mu cv : ℕ → Ω → ℝ) (t k : ℕ) (w : Ω)
    (l : ℝ) : ℝ :=
  dprofIso θ ω (tau (t + k) w) (lY (t + k) w) (lP (t + k) w) (uc (t + k) w) (mu (t + k) w)
    (cv (t + k) w) l

/-- The horizon-`k` nominal profit of the reset problem (2.2). -/
noncomputable def profP (θ ω : ℝ) (tau lY lP uc mu cv : ℕ → Ω → ℝ) (t k : ℕ) (w : Ω)
    (l : ℝ) : ℝ :=
  profIso θ ω (tau (t + k) w) (lY (t + k) w) (lP (t + k) w) (uc (t + k) w) (mu (t + k) w)
    (cv (t + k) w) l

omit 𝔼 in
/-- Woodford (2003), eq. (2.3) under Assumption 6.2 (Benigno–Woodford, pointwise): each discounted
marginal profit `Q_{t,t+k}Π₁` splits as
`βᵏ(θ−1)[−D₁ f_{t+k}Π_{t,t+k}^{θ−1} + D₂ k_{t+k}Π_{t,t+k}^{θ(1+ω)}]` with date-`t` factors
`D₁ = (P_t/u_c(t))(p/P_t)^{1−θ}`, `D₂ = (P_t/u_c(t))(p/P_t)^{−θ(1+ω)}`. -/
theorem sdf_dprof_eq {β θ ω l : ℝ} (hθ : θ ≠ 1) {tau lY lP uc mu cv : ℕ → Ω → ℝ} (t k : ℕ)
    (w : Ω) (huc : uc (t + k) w ≠ 0) :
    sdf β uc lP t k w * dprofP θ ω tau lY lP uc mu cv t k w l =
      β ^ k * (θ - 1) * (
        -(Real.exp (lP t w) / uc t w * Real.exp ((1 - θ) * (l - lP t w))) *
          (fLev tau uc lY (t + k) w * growth (θ - 1) lP t k w) +
        Real.exp (lP t w) / uc t w * Real.exp (-(θ * (1 + ω)) * (l - lP t w)) *
          (kLev θ ω mu cv lY (t + k) w * growth (θ * (1 + ω)) lP t k w)) := by
  have ha : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ
  have e1 : Real.exp (-lP (t + k) w) * Real.exp (l + lY (t + k) w - θ * (l - lP (t + k) w)) =
      Real.exp (lY (t + k) w) * Real.exp ((θ - 1) * (lP (t + k) w - lP t w)) *
        Real.exp ((1 - θ) * (l - lP t w)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have e2 : Real.exp ((1 + ω) * (lY (t + k) w - θ * (l - lP (t + k) w))) =
      Real.exp ((1 + ω) * lY (t + k) w) * Real.exp (θ * (1 + ω) * (lP (t + k) w - lP t w)) *
        Real.exp (-(θ * (1 + ω)) * (l - lP t w)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have e3 : Real.exp (-lP (t + k) w) * Real.exp (lP (t + k) w) = 1 := by
    rw [← Real.exp_add]; simp
  simp only [sdf, dprofP, dprofIso, fLev, kLev, growth]
  rw [e2]
  generalize Real.exp (-lP (t + k) w) = Em at e1 e3 ⊢
  generalize Real.exp (lP (t + k) w) = Ep at e3 ⊢
  generalize Real.exp (l + lY (t + k) w - θ * (l - lP (t + k) w)) = E1 at e1 ⊢
  generalize Real.exp (lY (t + k) w) = Y1 at e1 ⊢
  generalize Real.exp ((θ - 1) * (lP (t + k) w - lP t w)) = G1 at e1 ⊢
  generalize Real.exp ((1 - θ) * (l - lP t w)) = X1 at e1 ⊢
  generalize Real.exp ((1 + ω) * lY (t + k) w) = Y2
  generalize Real.exp (θ * (1 + ω) * (lP (t + k) w - lP t w)) = G2
  generalize Real.exp (-(θ * (1 + ω)) * (l - lP t w)) = X2
  generalize Real.exp (lP t w) = Et
  linear_combination (norm := skip)
    (β ^ k * uc (t + k) w * (Et / uc t w) * (1 - tau (t + k) w) * (1 - θ)) * e1 +
    (β ^ k * uc (t + k) w * (Et / uc t w) * θ * (1 + ω) * (1 / uc (t + k) w) * mu (t + k) w *
      cv (t + k) w * (Y2 * G2 * X2)) * e3
  field_simp
  ring

/-- Woodford (2003), eq. (2.3) under Assumption 6.2 (Benigno–Woodford): the first-order condition
of the reset problem is `(θ−1)[−D₁ F_t + D₂ K_t]`, with `F_t`, `K_t` the infinite sums
`fwdSum` and date-`t` factors `D₁ = (P_t/u_c(t))(p/P_t)^{1−θ}`,
`D₂ = (P_t/u_c(t))(p/P_t)^{−θ(1+ω)}`.
Hypotheses: the pull-out property, every function of `(log P_t, u_c(t))` is known at `t`, and
the discounted terms are dominated by `Cρᵏ` with `αβρ < 1`. -/
theorem resetFOC_iso {α β θ ω C ρ : ℝ} (hθ : θ ≠ 1) (hab0 : 0 ≤ α * β) (hρ0 : 0 ≤ ρ)
    (habρ : α * β * ρ < 1) {tau lY lP uc mu cv : ℕ → Ω → ℝ} (hPO : 𝔼.PullOut)
    (hknown : ∀ t (φ : ℝ → ℝ → ℝ),
      𝔼.E t (fun w => φ (lP t w) (uc t w)) = fun w => φ (lP t w) (uc t w))
    (huc : ∀ t w, uc t w ≠ 0)
    (hdF : ∀ t k w, |fLev tau uc lY (t + k) w * growth (θ - 1) lP t k w| ≤ C * ρ ^ k)
    (hdK : ∀ t k w, |kLev θ ω mu cv lY (t + k) w * growth (θ * (1 + ω)) lP t k w| ≤ C * ρ ^ k)
    (t : ℕ) (l : ℝ) (w : Ω) :
    resetFOC 𝔼 α (sdf β uc lP t) (dprofP θ ω tau lY lP uc mu cv t) t l w =
      (θ - 1) * (-(Real.exp (lP t w) / uc t w * Real.exp ((1 - θ) * (l - lP t w))) *
          fwdSum 𝔼 α β (θ - 1) lP (fLev tau uc lY) t w +
        Real.exp (lP t w) / uc t w * Real.exp (-(θ * (1 + ω)) * (l - lP t w)) *
          fwdSum 𝔼 α β (θ * (1 + ω)) lP (kLev θ ω mu cv lY) t w) := by
  set D1 : Ω → ℝ := fun w => Real.exp (lP t w) / uc t w * Real.exp ((1 - θ) * (l - lP t w))
    with hD1
  set D2 : Ω → ℝ := fun w => Real.exp (lP t w) / uc t w *
    Real.exp (-(θ * (1 + ω)) * (l - lP t w)) with hD2
  have hk1 : 𝔼.E t D1 = D1 :=
    hknown t (fun x y => Real.exp x / y * Real.exp ((1 - θ) * (l - x)))
  have hk2 : 𝔼.E t D2 = D2 :=
    hknown t (fun x y => Real.exp x / y * Real.exp (-(θ * (1 + ω)) * (l - x)))
  set Fk : ℕ → Ω → ℝ := fun k w => fLev tau uc lY (t + k) w * growth (θ - 1) lP t k w with hFk
  set Kk : ℕ → Ω → ℝ := fun k w =>
    kLev θ ω mu cv lY (t + k) w * growth (θ * (1 + ω)) lP t k w with hKk
  have hterm : ∀ k, α ^ k * 𝔼.E t (fun w' => sdf β uc lP t k w' *
      dprofP θ ω tau lY lP uc mu cv t k w' l) w =
      (θ - 1) * -D1 w * ((α * β) ^ k * 𝔼.E t (Fk k) w) +
        (θ - 1) * D2 w * ((α * β) ^ k * 𝔼.E t (Kk k) w) := by
    intro k
    have hf : (fun w' => sdf β uc lP t k w' * dprofP θ ω tau lY lP uc mu cv t k w' l) =
        (β ^ k * (θ - 1)) • (-(D1 * Fk k) + D2 * Kk k) := by
      funext w'
      rw [sdf_dprof_eq hθ t k w' (huc (t + k) w')]
      simp only [Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Pi.mul_apply, smul_eq_mul, hD1, hD2,
        hFk, hKk]
      ring
    rw [hf, map_smul, map_add, map_neg, hPO t D1 (Fk k) hk1, hPO t D2 (Kk k) hk2]
    simp only [Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Pi.mul_apply, smul_eq_mul]
    rw [mul_pow]
    ring
  have hbd : ∀ (X : ℕ → Ω → ℝ), (∀ k w, |X k w| ≤ C * ρ ^ k) →
      HasSum (fun k => (α * β) ^ k * 𝔼.E t (X k) w) (∑' k, (α * β) ^ k * 𝔼.E t (X k) w) := by
    intro X hX
    refine (Summable.of_norm_bounded ((summable_geometric_of_lt_one (mul_nonneg hab0 hρ0)
      habρ).mul_left C) (fun k => ?_)).hasSum
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hab0 k)]
    calc (α * β) ^ k * |𝔼.E t (X k) w| ≤ (α * β) ^ k * (C * ρ ^ k) :=
          mul_le_mul_of_nonneg_left (𝔼.abs_E_le (fun w' => hX k w') t w) (pow_nonneg hab0 k)
      _ = C * (α * β * ρ) ^ k := by rw [mul_pow]; ring
  have sF := hbd Fk (fun k w => hdF t k w)
  have sK := hbd Kk (fun k w => hdK t k w)
  have hs := (sF.mul_left ((θ - 1) * -D1 w)).add (sK.mul_left ((θ - 1) * D2 w))
  unfold resetFOC
  rw [tsum_congr hterm, hs.tsum_eq]
  simp only [fwdSum, hFk, hKk, hD1, hD2]
  ring

/-- Woodford (2003), §5 (Benigno–Woodford) — **the reset-price condition `K_t = x_t^{1+ωθ}F_t`**:
if the reset log price `l` satisfies the first-order condition (2.3) of the Calvo reset problem
under Assumption 6.2, then `K_t = exp((1+ωθ)(l − log P_t)) F_t` for the infinite sums `F`, `K`. -/
theorem resetPrice_of_foc {α β θ ω C ρ : ℝ} (hθ : θ ≠ 1) (hab0 : 0 ≤ α * β) (hρ0 : 0 ≤ ρ)
    (habρ : α * β * ρ < 1) {tau lY lP uc mu cv : ℕ → Ω → ℝ} (hPO : 𝔼.PullOut)
    (hknown : ∀ t (φ : ℝ → ℝ → ℝ),
      𝔼.E t (fun w => φ (lP t w) (uc t w)) = fun w => φ (lP t w) (uc t w))
    (huc : ∀ t w, uc t w ≠ 0)
    (hdF : ∀ t k w, |fLev tau uc lY (t + k) w * growth (θ - 1) lP t k w| ≤ C * ρ ^ k)
    (hdK : ∀ t k w, |kLev θ ω mu cv lY (t + k) w * growth (θ * (1 + ω)) lP t k w| ≤ C * ρ ^ k)
    {t : ℕ} {l : ℝ} {w : Ω}
    (hfoc : resetFOC 𝔼 α (sdf β uc lP t) (dprofP θ ω tau lY lP uc mu cv t) t l w = 0) :
    fwdSum 𝔼 α β (θ * (1 + ω)) lP (kLev θ ω mu cv lY) t w =
      Real.exp ((1 + ω * θ) * (l - lP t w)) * fwdSum 𝔼 α β (θ - 1) lP (fLev tau uc lY) t w := by
  rw [resetFOC_iso 𝔼 hθ hab0 hρ0 habρ hPO hknown huc hdF hdK t l w] at hfoc
  have ha : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ
  have hA : Real.exp (lP t w) / uc t w ≠ 0 := div_ne_zero (Real.exp_pos _).ne' (huc t w)
  have h2 : Real.exp (-(θ * (1 + ω)) * (l - lP t w)) * Real.exp ((1 + ω * θ) * (l - lP t w)) =
      Real.exp ((1 - θ) * (l - lP t w)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE : Real.exp (-(θ * (1 + ω)) * (l - lP t w)) ≠ 0 := (Real.exp_pos _).ne'
  have key : Real.exp (lP t w) / uc t w * Real.exp (-(θ * (1 + ω)) * (l - lP t w)) *
      (fwdSum 𝔼 α β (θ * (1 + ω)) lP (kLev θ ω mu cv lY) t w -
        Real.exp ((1 + ω * θ) * (l - lP t w)) * fwdSum 𝔼 α β (θ - 1) lP (fLev tau uc lY) t w)
      = 0 := by
    have := mul_eq_zero.mp hfoc
    rcases this with h | h
    · exact absurd h ha
    · linear_combination h - (Real.exp (lP t w) / uc t w *
        fwdSum 𝔼 α β (θ - 1) lP (fLev tau uc lY) t w) * h2
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (mul_ne_zero hA hE)
  · linarith

/-- Woodford (2003), eqs. (2.2)–(2.3) and §5 (Benigno–Woodford): if the log reset price `l` is a
local maximum of the GENUINE infinite-horizon Calvo objective (2.2) under Assumption 6.2
(`resetObjective` with the isoelastic profits `profP`, differentiable term by term under the
regularity hypotheses of `hasDerivAt_resetObjective`), then `K_t = x_t^{1+ωθ}F_t` with
`x_t = exp(l − log P_t)`. -/
theorem resetPrice_of_isLocalMax {α β θ ω C ρ : ℝ} (hθ : θ ≠ 1) (hab0 : 0 ≤ α * β)
    (hρ0 : 0 ≤ ρ) (habρ : α * β * ρ < 1) {tau lY lP uc mu cv : ℕ → Ω → ℝ} (hPO : 𝔼.PullOut)
    (hknown : ∀ t (φ : ℝ → ℝ → ℝ),
      𝔼.E t (fun w => φ (lP t w) (uc t w)) = fun w => φ (lP t w) (uc t w))
    (huc : ∀ t w, uc t w ≠ 0)
    (hdF : ∀ t k w, |fLev tau uc lY (t + k) w * growth (θ - 1) lP t k w| ≤ C * ρ ^ k)
    (hdK : ∀ t k w, |kLev θ ω mu cv lY (t + k) w * growth (θ * (1 + ω)) lP t k w| ≤ C * ρ ^ k)
    {t : ℕ} {w : Ω} {U : Set ℝ} (hU : IsOpen U) (hU' : IsPreconnected U)
    (hLip : ∀ k, ∀ y ∈ U, ∃ L, 0 ≤ L ∧ ∃ r > 0, ∀ z ∈ Metric.ball y r, ∀ w',
      |sdf β uc lP t k w' * dprofP θ ω tau lY lP uc mu cv t k w' z -
        sdf β uc lP t k w' * dprofP θ ω tau lY lP uc mu cv t k w' y| ≤ L * |z - y|)
    {u : ℕ → ℝ} (hdomQ : ∀ k, ∀ y ∈ U, ∀ w',
      |sdf β uc lP t k w' * dprofP θ ω tau lY lP uc mu cv t k w' y| ≤ u k)
    (hu : Summable fun k => |α| ^ k * u k) {y₀ : ℝ} (hy₀ : y₀ ∈ U)
    (hs : Summable fun k => α ^ k * 𝔼.E t (fun w' => sdf β uc lP t k w' *
      profP θ ω tau lY lP uc mu cv t k w' y₀) w)
    {l : ℝ} (hl : l ∈ U)
    (hmax : IsLocalMax (fun p => resetObjective 𝔼 α (sdf β uc lP t)
      (profP θ ω tau lY lP uc mu cv t) t p w) l) :
    fwdSum 𝔼 α β (θ * (1 + ω)) lP (kLev θ ω mu cv lY) t w =
      Real.exp ((1 + ω * θ) * (l - lP t w)) * fwdSum 𝔼 α β (θ - 1) lP (fLev tau uc lY) t w := by
  have hder := hasDerivAt_resetObjective 𝔼 (Q := sdf β uc lP t)
    (prof := profP θ ω tau lY lP uc mu cv t) (dprof := dprofP θ ω tau lY lP uc mu cv t)
    hU hU' (fun k w' y _ => hasDerivAt_profIso θ ω _ _ _ _ _ _ y) hLip hdomQ hu hy₀ t w hs hl
  exact resetPrice_of_foc 𝔼 hθ hab0 hρ0 habρ hPO hknown huc hdF hdK
    (foc_of_isLocalMax 𝔼 hder hmax)

/-- Woodford (2003), §5: the reset-price condition in log deviations, `ResetPriceEq`, DERIVED
from the Calvo first-order condition: if the reset log price `lps` satisfies (2.3) at every date
and state, `F_t = F̄e^{F̂_t}` and `K_t = F̄e^{K̂_t}` (common steady state `F̄ = K̄ > 0`) and
`x̂_t = lps_t − log P_t`, then `(1+ωθ)x̂_t = K̂_t − F̂_t`. -/
theorem resetPriceEq_of_foc {α β θ ω C ρ Fb : ℝ} (hθ : θ ≠ 1) (hab0 : 0 ≤ α * β)
    (hρ0 : 0 ≤ ρ) (habρ : α * β * ρ < 1) (hFb : 0 < Fb) {tau lY lP uc mu cv lps xr Fh Kh :
      ℕ → Ω → ℝ} (hPO : 𝔼.PullOut)
    (hknown : ∀ t (φ : ℝ → ℝ → ℝ),
      𝔼.E t (fun w => φ (lP t w) (uc t w)) = fun w => φ (lP t w) (uc t w))
    (huc : ∀ t w, uc t w ≠ 0)
    (hdF : ∀ t k w, |fLev tau uc lY (t + k) w * growth (θ - 1) lP t k w| ≤ C * ρ ^ k)
    (hdK : ∀ t k w, |kLev θ ω mu cv lY (t + k) w * growth (θ * (1 + ω)) lP t k w| ≤ C * ρ ^ k)
    (hfoc : ∀ t w,
      resetFOC 𝔼 α (sdf β uc lP t) (dprofP θ ω tau lY lP uc mu cv t) t (lps t w) w = 0)
    (hF : ∀ t w, fwdSum 𝔼 α β (θ - 1) lP (fLev tau uc lY) t w = Fb * Real.exp (Fh t w))
    (hK : ∀ t w, fwdSum 𝔼 α β (θ * (1 + ω)) lP (kLev θ ω mu cv lY) t w = Fb * Real.exp (Kh t w))
    (hx : ∀ t w, xr t w = lps t w - lP t w) :
    ResetPriceEq ω θ xr Fh Kh := by
  intro t w
  have h := resetPrice_of_foc 𝔼 hθ hab0 hρ0 habρ hPO hknown huc hdF hdK (hfoc t w)
  rw [hF, hK, ← hx] at h
  exact resetPrice_of_levels hFb (by rw [h, ← Real.exp_mul, mul_comm (xr t w)])

/-- Woodford (2003), §5: **the exact Calvo model under Assumption 6.2 from primitives.** Our
`CalvoModel.CalvoAS` (used for (5.4)) is obtained from: the Calvo price index in levels
(`hidx`, giving `PriceIndexEq` by `priceIndex_of_levels`), the first-order condition of the reset
problem at every date and state (`hfoc`, giving `ResetPriceEq` by `resetPriceEq_of_foc`), the
infinite-sum DEFINITIONS of `F` and `K` (`hF`, `hK`, giving `RecEq` by `recEq_of_fwdSum`), and
the isoelastic forms of `k̂`, `f̂` (`costK`, `revF`; `log_k_iso`, `log_f_iso`). Dates: `lPprev t`
is `log P_{t−1}` (`lPprev 0` the initial price level), `π_t = log P_t − log P_{t−1}`,
`x̂_t = log p*_t − log P_t`. With `eq54` this derives (5.4) from the Calvo model. -/
theorem calvoAS_of_primitives {α β θ ω σ sC C ρ fb : ℝ} (hθ : θ ≠ 1) (hab0 : 0 ≤ α * β)
    (hρ0 : 0 ≤ ρ) (habρ : α * β * ρ < 1) (hfb : 0 < fb) (hab : 1 - α * β ≠ 0)
    (hab1 : 0 < 1 - α * β)
    {tau lY lP lPprev uc mu cv lps infl xr F K f k Y G cb q muw tau' : ℕ → Ω → ℝ}
    (hPO : 𝔼.PullOut)
    (hknown : ∀ t (φ : ℝ → ℝ → ℝ),
      𝔼.E t (fun w => φ (lP t w) (uc t w)) = fun w => φ (lP t w) (uc t w))
    (huc : ∀ t w, uc t w ≠ 0)
    (hfa : ∀ t, 𝔼.E t (fLev tau uc lY t) = fLev tau uc lY t)
    (hka : ∀ t, 𝔼.E t (kLev θ ω mu cv lY t) = kLev θ ω mu cv lY t)
    (hgF : ∀ t, 𝔼.E (t + 1) (growth (θ - 1) lP t 1) = growth (θ - 1) lP t 1)
    (hgK : ∀ t, 𝔼.E (t + 1) (growth (θ * (1 + ω)) lP t 1) = growth (θ * (1 + ω)) lP t 1)
    (hdF : ∀ t k w, |fLev tau uc lY (t + k) w * growth (θ - 1) lP t k w| ≤ C * ρ ^ k)
    (hdK : ∀ t k w, |kLev θ ω mu cv lY (t + k) w * growth (θ * (1 + ω)) lP t k w| ≤ C * ρ ^ k)
    (hidx : ∀ t w, Real.exp ((1 - θ) * lP t w) = α * Real.exp ((1 - θ) * lPprev t w) +
      (1 - α) * Real.exp ((1 - θ) * lps t w))
    (hprev : ∀ t w, lPprev (t + 1) w = lP t w)
    (hinfl : ∀ t w, infl t w = lP t w - lPprev t w)
    (hfoc : ∀ t w, resetFOC 𝔼 α (sdf β uc lP t) (dprofP θ ω tau lY lP uc mu cv t) t
      (lps t w) w = 0)
    (hxr0 : ∀ t w, xr t w = lps t w - lP t w)
    (hfl : ∀ t w, fLev tau uc lY t w = fb * Real.exp (f t w))
    (hkl : ∀ t w, kLev θ ω mu cv lY t w = fb * Real.exp (k t w))
    (hF : ∀ t w, fwdSum 𝔼 α β (θ - 1) lP (fLev tau uc lY) t w =
      fb / (1 - α * β) * Real.exp (F t w))
    (hK : ∀ t w, fwdSum 𝔼 α β (θ * (1 + ω)) lP (kLev θ ω mu cv lY) t w =
      fb / (1 - α * β) * Real.exp (K t w))
    (costK : ∀ t w, k t w = (1 + ω) * Y t w - ω * q t w + muw t w)
    (revF : ∀ t w, f t w = fhatIso σ sC (Y t w) (G t w) (cb t w) (tau' t w)) :
    CalvoModel.CalvoAS 𝔼 α β θ ω σ sC infl xr F K f k Y G cb q muw tau' where
  priceIndex := by
    intro t w
    have h := priceIndex_of_levels (hidx t w)
    rw [hinfl, hxr0]
    exact h
  resetPrice := resetPriceEq_of_foc 𝔼 hθ hab0 hρ0 habρ (div_pos hfb hab1) hPO hknown huc
    hdF hdK hfoc hF hK hxr0
  recF := recEq_of_fwdSum 𝔼 hab0 hρ0 habρ hfb.ne' hab hPO hfa hgF hdF
    (fun t w => by rw [hinfl, hprev]) hfl hF
  recK := recEq_of_fwdSum 𝔼 hab0 hρ0 habρ hfb.ne' hab hPO hka hgK hdK
    (fun t w => by rw [hinfl, hprev]) hkl hK
  costK := costK
  revF := revF

/-- **Woodford (2003), eq. (5.4), p. 458, from the primitives of the Calvo model** (Benigno and
Woodford (2003); the book gives no proof): under Assumption 6.2, if every supplier that resets
chooses a stationary point of the infinite-horizon reset objective (`hfoc`), the Dixit–Stiglitz
index aggregates old and reset prices (`hidx`), and `F`, `K` are the infinite discounted sums
(`hF`, `hK`), then the second-order aggregate-supply relation (5.4) holds: the Calvo conditions
are derived by `calvoAS_of_primitives` and integrated forward by `eq54`. -/
theorem eq54_of_primitives {α β θ ω σ sC C ρ fb : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ : θ ≠ 1) (hν : 1 + ω * θ ≠ 0) (hs : sC ≠ 0) (hc : ω + σ ≠ 0)
    (hρ0 : 0 ≤ ρ) (habρ : α * β * ρ < 1) (hfb : 0 < fb)
    {tauF lY lP lPprev uc mu cv lps infl xr F K f k Y G cb q muw tau : ℕ → Ω → ℝ}
    (hPO : 𝔼.PullOut)
    (hknown : ∀ t (φ : ℝ → ℝ → ℝ),
      𝔼.E t (fun w => φ (lP t w) (uc t w)) = fun w => φ (lP t w) (uc t w))
    (huc : ∀ t w, uc t w ≠ 0)
    (hfa : ∀ t, 𝔼.E t (fLev tauF uc lY t) = fLev tauF uc lY t)
    (hka : ∀ t, 𝔼.E t (kLev θ ω mu cv lY t) = kLev θ ω mu cv lY t)
    (hgF : ∀ t, 𝔼.E (t + 1) (growth (θ - 1) lP t 1) = growth (θ - 1) lP t 1)
    (hgK : ∀ t, 𝔼.E (t + 1) (growth (θ * (1 + ω)) lP t 1) = growth (θ * (1 + ω)) lP t 1)
    (hdF : ∀ t k w, |fLev tauF uc lY (t + k) w * growth (θ - 1) lP t k w| ≤ C * ρ ^ k)
    (hdK : ∀ t k w, |kLev θ ω mu cv lY (t + k) w * growth (θ * (1 + ω)) lP t k w| ≤ C * ρ ^ k)
    (hidx : ∀ t w, Real.exp ((1 - θ) * lP t w) = α * Real.exp ((1 - θ) * lPprev t w) +
      (1 - α) * Real.exp ((1 - θ) * lps t w))
    (hprev : ∀ t w, lPprev (t + 1) w = lP t w)
    (hinfl : ∀ t w, infl t w = lP t w - lPprev t w)
    (hfoc : ∀ t w, resetFOC 𝔼 α (sdf β uc lP t) (dprofP θ ω tauF lY lP uc mu cv t) t
      (lps t w) w = 0)
    (hxr0 : ∀ t w, xr t w = lps t w - lP t w)
    (hfl : ∀ t w, fLev tauF uc lY t w = fb * Real.exp (f t w))
    (hkl : ∀ t w, kLev θ ω mu cv lY t w = fb * Real.exp (k t w))
    (hF : ∀ t w, fwdSum 𝔼 α β (θ - 1) lP (fLev tauF uc lY) t w =
      fb / (1 - α * β) * Real.exp (F t w))
    (hK : ∀ t w, fwdSum 𝔼 α β (θ * (1 + ω)) lP (kLev θ ω mu cv lY) t w =
      fb / (1 - α * β) * Real.exp (K t w))
    (costK : ∀ t w, k t w = (1 + ω) * Y t w - ω * q t w + muw t w)
    (revF : ∀ t w, f t w = fhatIso σ sC (Y t w) (G t w) (cb t w) (tau t w))
    (hib : BoundedProc infl) (hFb : BoundedProc F) (hKb : BoundedProc K) (hYb : BoundedProc Y)
    (hGb : BoundedProc G) (hcb : BoundedProc cb) (hqb : BoundedProc q) (hmb : BoundedProc muw)
    (htb : BoundedProc tau) (w : Ω) :
    𝔼.E 0 (fun w => Vp α θ infl F K 0 w + θ * (1 + ω) / 2 * infl 0 w ^ 2) w =
      calvoKappa α β ω θ σ * dsum 𝔼 β (fun t w => Y t w -
          YnA ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w)) w
        + muY α β θ ω σ sC / 2 * dsum 𝔼 β (fun t w => Y t w ^ 2) w
        - dsum 𝔼 β (fun t w => deltaA α β θ ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w) *
            Y t w) w
        + θ * (1 + ω) / 2 * dsum 𝔼 β (fun t w => infl t w ^ 2) w
        + dsum 𝔼 β (fun t w => tipASA α β θ ω σ sC (G t w) (cb t w) (q t w) (muw t w) (tau t w)) w
        + dsum 𝔼 β (remAS 𝔼 α β θ ω σ sC infl xr F K f k Y G cb tau) w := by
  have hab1 : 0 < 1 - α * β := by nlinarith
  have hM := calvoAS_of_primitives 𝔼 hθ (by positivity) hρ0 habρ hfb hab1.ne' hab1 hPO hknown huc
    hfa hka hgF hgK hdF hdK hidx hprev hinfl hfoc hxr0 hfl hkl hF hK costK revF
  exact eq54 𝔼 hα0 hα1 hβ0 hβ1 hθ hν hs hc hM hib hFb hKb hYb hGb hcb hqb hmb htb w

end Woodford.StabilizationWelfare.LargeDistortions
