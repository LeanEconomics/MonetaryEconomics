/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.Prop61
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Time-varying tax wedges or markups: inefficient supply shocks

Woodford (2003), *Interest and Prices*, Chapter 6, §4.5, pp. 448–455, eqs. (4.32)–(4.39) and
footnotes 67 and 71.

## Main results

* (4.32)–(4.34): the relative supply price `ptilde`, the natural rate `IsNaturalRate`
  (`p̃(Yⁿ, Yⁿ; ξ, μ) = 1`) and the efficient level `IsEfficient` (`ṽ_y/ũ_c = 1`); in logs
  they read `log μ + F(log Yⁿ, ξ) = 0` and `F(log Yᵉ, ξ) = 0` with `F = log ṽ_y − log ũ_c`
  (`isNaturalRate_iff_log`, `isEfficient_iff_log`).
* `hasDerivAt_logMRS`: `∂F/∂ log Y = ω + σ⁻¹` at the steady state, from the derivatives of
  `ṽ_y` and `ũ_c` (the elasticities of Chapter 3).
* `log Yⁿ = log Yᵉ − (ω+σ⁻¹)⁻¹ log μ + O(2)` as EXACT derivative statements:
  `hasDerivAt_naturalRate` (fixed disturbances; differentiability of the implicit natural
  rate is DERIVED from continuity), `hasDerivAt_naturalRate_elasticities` (the slope identified
  as `−(ω+σ⁻¹)⁻¹` from `ṽ_y`, `ũ_c`), `hasDerivAt_natural_sub_efficient`, and
  `hasFDerivAt_natural_sub_efficient` (jointly in
  `(log μ, ξ̃)` for disturbances in any normed space: the map
  `(m, ξ) ↦ log Yⁿ(m, ξ) − log Yᵉ(ξ)` has Fréchet derivative `−(ω+σ⁻¹)⁻¹ dm` at `0`, so all
  `ξ̃`-terms and all cross terms are of second order); `implicit_natural_efficient` derives the
  existence, local uniqueness and differentiability of `log Yⁿ`, `log Yᵉ` from Mathlib's
  implicit-function theorem for a `C¹` marginal-rate-of-substitution map (with
  `isInvertible_of_apply_one`), so nothing about the implicit functions is assumed.
* Footnote 67: `log μ̄ = Φ_y + O(Φ_y²)` (`hasDerivAt_log_mubar`, `abs_log_mubar_sub_le`), and
  the efficient gap `x* = log Y* − log Ȳ` has derivative `(ω+σ⁻¹)⁻¹` in `Φ_y`
  (`hasDerivAt_xstar`, eq. (2.9) recovered).
* (4.35)–(4.39) in the linear model: `asNatural_iff_asGap` (the AS relation (4.35) in terms of
  `Ŷ − Ŷⁿ` is equivalent to (4.38) in terms of the welfare-relevant gap (4.37), with the
  cost-push term (4.39) `u_t = κ μ̂_t/(ω+σ⁻¹)`), `loss_436_eq_222` ((4.36) is (2.22)),
  `stabilize_both_iff` (inflation and the welfare-relevant gap can both be stabilised iff
  `μ̂ ≡ 0`).
* Footnote 71 (arithmetic only): `annualized_loss`, `targeting_of_stable_index`,
  `ngdp_index_eq`, `lambdaOfPhi`, `ngdp_lambda_calibrated` (`16 κ = 0.384 ≈ 0.38`).

The claim of footnote 71 that complete stabilisation of `log P_t + φ x_t` is the optimal
commitment policy for the weight `λ = 16κφ` (the efficient frontier of Figure 6.6) is the
optimal targeting rule of Chapter 7 and is out of scope here; only its arithmetic and the
identity linking the stabilised index to the targeting rule are formalised. Figure 6.6 is
numerical.
-/

namespace Woodford.StabilizationWelfare.CostPush

open Filter Topology
open Prop61 (omegaEl sigmaInvEl)

/-! ### (4.32)–(4.34): natural and efficient output -/

/-- Woodford (2003), eq. (4.32), p. 449: the relative price at which the supplier of good `i`
would supply `y`, `p̃(y, Y; ξ, μ) = μ ṽ_y(y; ξ)/ũ_c(Y; ξ)`, with `μ` the composite markup. -/
noncomputable def ptilde {E : Type*} (vy uc : ℝ → E → ℝ) (μ y Y : ℝ) (ξ : E) : ℝ :=
  μ * vy y ξ / uc Y ξ

/-- Woodford (2003), eq. (4.33), p. 450: `Yⁿ` is the flexible-price (natural) level of output,
`p̃(Yⁿ, Yⁿ; ξ, μ) = 1`. -/
def IsNaturalRate {E : Type*} (vy uc : ℝ → E → ℝ) (μ Yn : ℝ) (ξ : E) : Prop :=
  ptilde vy uc μ Yn Yn ξ = 1

/-- Woodford (2003), eq. (4.34), p. 450: `Yᵉ` is the efficient level of output,
`ṽ_y(Yᵉ; ξ)/ũ_c(Yᵉ; ξ) = 1`. -/
def IsEfficient {E : Type*} (vy uc : ℝ → E → ℝ) (Ye : ℝ) (ξ : E) : Prop :=
  vy Ye ξ / uc Ye ξ = 1

/-- Woodford (2003), p. 450: the log marginal rate of substitution between supply and
consumption as a function of log output, `F(y, ξ) = log ṽ_y(eʸ; ξ) − log ũ_c(eʸ; ξ)`. -/
noncomputable def logMRS {E : Type*} (vy uc : ℝ → E → ℝ) (y : ℝ) (ξ : E) : ℝ :=
  Real.log (vy (Real.exp y) ξ) - Real.log (uc (Real.exp y) ξ)

/-- Woodford (2003), (4.33), p. 450: in logs the natural rate solves `log μ + F(log Yⁿ, ξ) = 0`
(all of `μ, ṽ_y, ũ_c` positive). -/
theorem isNaturalRate_iff_log {E : Type*} {vy uc : ℝ → E → ℝ} {μ Yn : ℝ} {ξ : E}
    (hμ : 0 < μ) (hYn : 0 < Yn) (hv : 0 < vy Yn ξ) (hu : 0 < uc Yn ξ) :
    IsNaturalRate vy uc μ Yn ξ ↔ Real.log μ + logMRS vy uc (Real.log Yn) ξ = 0 := by
  unfold IsNaturalRate ptilde logMRS
  rw [Real.exp_log hYn]
  have hpos : 0 < μ * vy Yn ξ / uc Yn ξ := by positivity
  constructor
  · intro h
    have := congrArg Real.log h
    rw [Real.log_div (by positivity) hu.ne', Real.log_mul hμ.ne' hv.ne', Real.log_one] at this
    linarith
  · intro h
    have hl : Real.log (μ * vy Yn ξ / uc Yn ξ) = 0 := by
      rw [Real.log_div (by positivity) hu.ne', Real.log_mul hμ.ne' hv.ne']
      linarith
    have := Real.exp_log hpos
    rw [hl, Real.exp_zero] at this
    exact this.symm

/-- Woodford (2003), (4.34), p. 450: in logs the efficient level solves `F(log Yᵉ, ξ) = 0`. -/
theorem isEfficient_iff_log {E : Type*} {vy uc : ℝ → E → ℝ} {Ye : ℝ} {ξ : E}
    (hYe : 0 < Ye) (hv : 0 < vy Ye ξ) (hu : 0 < uc Ye ξ) :
    IsEfficient vy uc Ye ξ ↔ logMRS vy uc (Real.log Ye) ξ = 0 := by
  unfold IsEfficient logMRS
  rw [Real.exp_log hYe]
  constructor
  · intro h
    have := congrArg Real.log h
    rw [Real.log_div hv.ne' hu.ne', Real.log_one] at this
    exact this
  · intro h
    have hl : Real.log (vy Ye ξ / uc Ye ξ) = 0 := by
      rw [Real.log_div hv.ne' hu.ne']; exact h
    have := Real.exp_log (div_pos hv hu)
    rw [hl, Real.exp_zero] at this
    exact this.symm

/-- Woodford (2003), p. 450 ("log-linearizing both (4.33) and (4.34)"): the log marginal rate
of substitution has slope `ω + σ⁻¹` in log output at the steady state `Ȳ`. -/
theorem hasDerivAt_logMRS {vy uc : ℝ → ℝ} {Ybar vyy ucc : ℝ} (hY : 0 < Ybar)
    (hv : 0 < vy Ybar) (hu : 0 < uc Ybar) (hvd : HasDerivAt vy vyy Ybar)
    (hud : HasDerivAt uc ucc Ybar) :
    HasDerivAt (fun y => Real.log (vy (Real.exp y)) - Real.log (uc (Real.exp y)))
      (omegaEl Ybar (vy Ybar) vyy + sigmaInvEl Ybar (uc Ybar) ucc) (Real.log Ybar) := by
  have he : HasDerivAt Real.exp Ybar (Real.log Ybar) := by
    have := Real.hasDerivAt_exp (Real.log Ybar)
    rwa [Real.exp_log hY] at this
  have hv' : HasDerivAt vy vyy (Real.exp (Real.log Ybar)) := by rwa [Real.exp_log hY]
  have hu' : HasDerivAt uc ucc (Real.exp (Real.log Ybar)) := by rwa [Real.exp_log hY]
  have hv0 : (vy ∘ Real.exp) (Real.log Ybar) ≠ 0 := by
    rw [Function.comp_apply, Real.exp_log hY]; exact hv.ne'
  have hu0 : (uc ∘ Real.exp) (Real.log Ybar) ≠ 0 := by
    rw [Function.comp_apply, Real.exp_log hY]; exact hu.ne'
  have h1 := (hv'.comp (Real.log Ybar) he).log hv0
  have h2 := (hu'.comp (Real.log Ybar) he).log hu0
  have h3 := HasDerivAt.sub h1 h2
  refine h3.congr_deriv ?_
  simp only [Function.comp_apply, Real.exp_log hY, omegaEl, sigmaInvEl]
  ring

/-- Woodford (2003), p. 450: `log Yⁿ = log Yᵉ − (ω + σ⁻¹)⁻¹ log μ + O(2)` for given disturbances,
as an exact derivative statement. If `yN(m)` is the log natural rate when `log μ = m`
(i.e. `m + F(yN m) = 0` near `m = 0`), `yN` is continuous at `0`, and `F` has slope
`c = ω + σ⁻¹ ≠ 0` at `yN 0 = log Yᵉ`, then `yN` is differentiable at `0` with derivative
`−c⁻¹` (differentiability is derived, not assumed). -/
theorem hasDerivAt_naturalRate {F yN : ℝ → ℝ} {c : ℝ} (hcont : ContinuousAt yN 0)
    (hF : HasDerivAt F c (yN 0)) (hc : c ≠ 0) (hN : ∀ᶠ m in 𝓝 0, m + F (yN m) = 0) :
    HasDerivAt yN (-c⁻¹) 0 := by
  have hf : HasDerivAt (fun y => -F y) (-c) (yN 0) := hF.neg
  have hinv := HasDerivAt.of_local_left_inverse hcont hf (neg_ne_zero.mpr hc)
    (hN.mono fun m hm => by linarith)
  rwa [inv_neg] at hinv

/-- Woodford (2003), p. 450, with the slope identified from primitives: for given disturbances
(`ṽ_y`, `ũ_c` functions of output alone), if `yN(m)` is the log natural rate at `log μ = m`
(`m + log ṽ_y(e^{yN}) − log ũ_c(e^{yN}) = 0` near `0`), continuous at `0`, and `Ȳ = e^{yN 0}`,
then `d yN/d log μ = −(ω + σ⁻¹)⁻¹` with `ω = Ȳ v_yy/v_y`, `σ⁻¹ = −Ȳ u_cc/u_c`. -/
theorem hasDerivAt_naturalRate_elasticities {vy uc yN : ℝ → ℝ} {vyy ucc : ℝ}
    (hv : 0 < vy (Real.exp (yN 0))) (hu : 0 < uc (Real.exp (yN 0)))
    (hvd : HasDerivAt vy vyy (Real.exp (yN 0))) (hud : HasDerivAt uc ucc (Real.exp (yN 0)))
    (hc : omegaEl (Real.exp (yN 0)) (vy (Real.exp (yN 0))) vyy +
      sigmaInvEl (Real.exp (yN 0)) (uc (Real.exp (yN 0))) ucc ≠ 0)
    (hcont : ContinuousAt yN 0)
    (hN : ∀ᶠ m in 𝓝 0, m + (Real.log (vy (Real.exp (yN m))) -
      Real.log (uc (Real.exp (yN m)))) = 0) :
    HasDerivAt yN (-(omegaEl (Real.exp (yN 0)) (vy (Real.exp (yN 0))) vyy +
      sigmaInvEl (Real.exp (yN 0)) (uc (Real.exp (yN 0))) ucc)⁻¹) 0 := by
  have hF := hasDerivAt_logMRS (Real.exp_pos (yN 0)) hv hu hvd hud
  rw [Real.log_exp] at hF
  exact hasDerivAt_naturalRate hcont hF hc hN

/-- Woodford (2003), p. 450: the same statement for the gap `log Yⁿ − log Yᵉ`, where
`log Yᵉ = yN 0` is the efficient level (the natural rate at `μ = 1`):
`log Yⁿ(μ) − log Yᵉ` has derivative `−(ω + σ⁻¹)⁻¹` in `log μ` at `μ = 1`. -/
theorem hasDerivAt_natural_sub_efficient {F yN : ℝ → ℝ} {c : ℝ} (hcont : ContinuousAt yN 0)
    (hF : HasDerivAt F c (yN 0)) (hc : c ≠ 0) (hN : ∀ᶠ m in 𝓝 0, m + F (yN m) = 0) :
    HasDerivAt (fun m => yN m - yN 0) (-c⁻¹) 0 := by
  have := (hasDerivAt_naturalRate hcont hF hc hN).sub_const (yN 0)
  exact this

/-- Woodford (2003), p. 450: `log Yⁿ = log Yᵉ − (ω + σ⁻¹)⁻¹ log μ + O(‖log μ, ξ̃‖²)` jointly in the
markup and the disturbances `ξ̃` (in any real normed space). Let `yN(m, ξ)` be the log natural
rate (`m + F(yN, ξ) = 0`), `yE(ξ)` the log efficient level (`F(yE, ξ) = 0`), both equal to
`ȳ` at `0` and differentiable there (as the implicit-function theorem provides), and let
`F` have Fréchet derivative `F'` at `(ȳ, 0)` with `F'(1, 0) = c ≠ 0`. Then
`(m, ξ) ↦ yN(m, ξ) − yE(ξ)` has derivative `−c⁻¹ dm`: the disturbances have no first-order
effect on the gap, so every `ξ̃`-term and every `log μ · ξ̃` term is of second order. -/
theorem hasFDerivAt_natural_sub_efficient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × E → ℝ} {F' : ℝ × E →L[ℝ] ℝ} {yN : ℝ × E → ℝ} {yE : E → ℝ}
    {DN : ℝ × E →L[ℝ] ℝ} {DE : E →L[ℝ] ℝ} {ybar c : ℝ}
    (hN0 : yN 0 = ybar) (hE0 : yE 0 = ybar) (hF : HasFDerivAt F F' (ybar, 0))
    (hc : F' (1, 0) = c) (hc0 : c ≠ 0) (hDN : HasFDerivAt yN DN 0) (hDE : HasFDerivAt yE DE 0)
    (hN : ∀ᶠ p in 𝓝 (0 : ℝ × E), p.1 + F (yN p, p.2) = 0)
    (hE : ∀ᶠ ξ in 𝓝 (0 : E), F (yE ξ, ξ) = 0) :
    HasFDerivAt (fun p : ℝ × E => yN p - yE p.2)
      (-c⁻¹ • ContinuousLinearMap.fst ℝ ℝ E) 0 := by
  -- the derivative of the natural-rate identity vanishes
  have hgN : HasFDerivAt (fun p : ℝ × E => (yN p, p.2))
      (DN.prod (ContinuousLinearMap.snd ℝ ℝ E)) 0 := hDN.prodMk hasFDerivAt_snd
  have hF1 : HasFDerivAt F F' ((fun p : ℝ × E => (yN p, p.2)) 0) := by
    simpa [hN0] using hF
  have hcompN := hF1.comp (0 : ℝ × E) hgN
  have hidN : HasFDerivAt (fun p : ℝ × E => p.1 + F (yN p, p.2))
      (ContinuousLinearMap.fst ℝ ℝ E + F'.comp (DN.prod (ContinuousLinearMap.snd ℝ ℝ E))) 0 :=
    hasFDerivAt_fst.add hcompN
  have hzeroN : HasFDerivAt (fun p : ℝ × E => p.1 + F (yN p, p.2)) (0 : ℝ × E →L[ℝ] ℝ) 0 :=
    (hasFDerivAt_const (0 : ℝ) (0 : ℝ × E)).congr_of_eventuallyEq hN
  have hEqN := hidN.unique hzeroN
  -- the derivative of the efficient-level identity vanishes
  have hgE : HasFDerivAt (fun ξ : E => (yE ξ, ξ)) (DE.prod (ContinuousLinearMap.id ℝ E)) 0 :=
    hDE.prodMk (hasFDerivAt_id 0)
  have hF2 : HasFDerivAt F F' ((fun ξ : E => (yE ξ, ξ)) 0) := by
    simpa [hE0] using hF
  have hcompE := HasFDerivAt.comp (f := fun ξ : E => (yE ξ, ξ)) (0 : E) hF2 hgE
  have hzeroE : HasFDerivAt (fun ξ : E => F (yE ξ, ξ)) (0 : E →L[ℝ] ℝ) 0 :=
    (hasFDerivAt_const (0 : ℝ) (0 : E)).congr_of_eventuallyEq hE
  have hEqE := hcompE.unique hzeroE
  -- linearity of `F'` in its first slot
  have hlin : ∀ (a : ℝ) (ξ : E), F' (a, ξ) = a * c + F' (0, ξ) := by
    intro a ξ
    have : ((a, ξ) : ℝ × E) = a • ((1 : ℝ), (0 : E)) + ((0 : ℝ), ξ) := by
      ext <;> simp
    rw [this, map_add, map_smul, hc, smul_eq_mul]
  have hDE' : HasFDerivAt (fun p : ℝ × E => yE p.2) (DE.comp (ContinuousLinearMap.snd ℝ ℝ E)) 0 :=
    hDE.comp (0 : ℝ × E) hasFDerivAt_snd
  refine (hDN.sub hDE').congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  have e1 := congrArg (fun L : ℝ × E →L[ℝ] ℝ => L v) hEqN
  have e2 := congrArg (fun L : E →L[ℝ] ℝ => L v.2) hEqE
  simp only [add_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_snd', zero_apply] at e1
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_id', id_eq, zero_apply] at e2
  rw [hlin] at e1 e2
  simp only [sub_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_snd', smul_apply, ContinuousLinearMap.coe_fst',
    smul_eq_mul]
  field_simp
  linear_combination e1 - e2

/-- An invertibility criterion used for the implicit-function theorem: a continuous linear map
`ℝ → ℝ` with `L 1 = c ≠ 0` is invertible. -/
theorem isInvertible_of_apply_one {L : ℝ →L[ℝ] ℝ} {c : ℝ} (hL : L 1 = c) (hc : c ≠ 0) :
    L.IsInvertible := by
  refine ContinuousLinearMap.IsInvertible.of_inverse (g := c⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    ?_ ?_
  · refine ContinuousLinearMap.ext_ring ?_
    have h1 : L c⁻¹ = c⁻¹ * L 1 := by
      rw [← smul_eq_mul c⁻¹ (L 1), ← map_smul, smul_eq_mul, mul_one]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, mul_one]
    rw [h1, hL]
    field_simp
  · refine ContinuousLinearMap.ext_ring ?_
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, hL]
    field_simp

/-- Woodford (2003), p. 450 (**natural and efficient output exist and are differentiable**): if
the log marginal rate of substitution `F(y, ξ) = log ṽ_y − log ũ_c` is `C¹` at the steady state
`(ȳ, 0)` with `F(ȳ, 0) = 0` and slope `∂F/∂y = c = ω + σ⁻¹ ≠ 0` there, then by Mathlib's
implicit-function theorem there are a log natural rate `yN(log μ, ξ)` and a log efficient level
`yE(ξ)`, equal to `ȳ` at `0`, solving (4.33) and (4.34) near `0`, locally the UNIQUE solutions,
and `(m, ξ) ↦ yN(m, ξ) − yE(ξ)` has Fréchet derivative `−c⁻¹ dm` at `0`: `log Yⁿ = log Yᵉ −
(ω+σ⁻¹)⁻¹ log μ + O(‖log μ, ξ̃‖²)`, with differentiability derived, not assumed. -/
theorem implicit_natural_efficient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {F : ℝ × E → ℝ} {ybar c : ℝ} (hF : ContDiffAt ℝ 1 F (ybar, 0))
    (hF0 : F (ybar, 0) = 0) (hc : fderiv ℝ F (ybar, 0) (1, 0) = c) (hc0 : c ≠ 0) :
    ∃ yN : ℝ × E → ℝ, ∃ yE : E → ℝ, yN 0 = ybar ∧ yE 0 = ybar ∧
      (∀ᶠ p in 𝓝 (0 : ℝ × E), p.1 + F (yN p, p.2) = 0) ∧
      (∀ᶠ ξ in 𝓝 (0 : E), F (yE ξ, ξ) = 0) ∧
      (∀ᶠ v in 𝓝 (((0 : ℝ × E)), ybar), v.1.1 + F (v.2, v.1.2) = 0 ↔ yN v.1 = v.2) ∧
      (∀ᶠ v in 𝓝 ((0 : E), ybar), F (v.2, v.1) = 0 ↔ yE v.1 = v.2) ∧
      HasFDerivAt (fun p : ℝ × E => yN p - yE p.2)
        (-c⁻¹ • ContinuousLinearMap.fst ℝ ℝ E) 0 := by
  have pn : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
  set F' := fderiv ℝ F (ybar, 0) with hF'
  have hFd : HasFDerivAt F F' (ybar, 0) := (hF.differentiableAt pn).hasFDerivAt
  -- the natural-rate equation
  set fN : (ℝ × E) × ℝ → ℝ := fun v => v.1.1 + F (v.2, v.1.2) with hfN
  set uN : (ℝ × E) × ℝ := ((0 : ℝ × E), ybar) with huN
  have cN : ContDiffAt ℝ 1 fN uN := by
    have h1 : ContDiffAt ℝ 1 (fun v : (ℝ × E) × ℝ => (v.2, v.1.2)) uN := by fun_prop
    exact (contDiffAt_fst.comp uN contDiffAt_fst).add (hF.comp uN h1)
  set LN : (ℝ × E) × ℝ →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ E).comp
      (ContinuousLinearMap.fst ℝ (ℝ × E) ℝ) + F'.comp ((ContinuousLinearMap.snd ℝ (ℝ × E) ℝ).prod
        ((ContinuousLinearMap.snd ℝ ℝ E).comp (ContinuousLinearMap.fst ℝ (ℝ × E) ℝ))) with hLN
  have dN : HasFDerivAt fN LN uN := by
    have h1 : HasFDerivAt (fun v : (ℝ × E) × ℝ => (v.2, v.1.2))
        ((ContinuousLinearMap.snd ℝ (ℝ × E) ℝ).prod
          ((ContinuousLinearMap.snd ℝ ℝ E).comp (ContinuousLinearMap.fst ℝ (ℝ × E) ℝ))) uN :=
      hasFDerivAt_snd.prodMk (hasFDerivAt_snd.comp uN hasFDerivAt_fst)
    exact (hasFDerivAt_fst.comp uN hasFDerivAt_fst).add (hFd.comp uN h1)
  have invN : (fderiv ℝ fN uN ∘L ContinuousLinearMap.inr ℝ (ℝ × E) ℝ).IsInvertible := by
    rw [dN.fderiv]
    refine isInvertible_of_apply_one (c := c) ?_ hc0
    simp [hLN, hc]
  set yN := cN.implicitFunction pn invN with hyN
  -- the efficient-level equation
  set fE : E × ℝ → ℝ := fun v => F (v.2, v.1) with hfE
  set uE : E × ℝ := ((0 : E), ybar) with huE
  have cE : ContDiffAt ℝ 1 fE uE := by
    have h1 : ContDiffAt ℝ 1 (fun v : E × ℝ => (v.2, v.1)) uE := by fun_prop
    exact hF.comp uE h1
  set LE : E × ℝ →L[ℝ] ℝ := F'.comp ((ContinuousLinearMap.snd ℝ E ℝ).prod
    (ContinuousLinearMap.fst ℝ E ℝ)) with hLE
  have dE : HasFDerivAt fE LE uE :=
    hFd.comp uE (hasFDerivAt_snd.prodMk hasFDerivAt_fst)
  have invE : (fderiv ℝ fE uE ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible := by
    rw [dE.fderiv]
    refine isInvertible_of_apply_one (c := c) ?_ hc0
    simp [hLE, hc]
  set yE := cE.implicitFunction pn invE with hyE
  have hN0 : yN 0 = ybar := cN.implicitFunction_apply_self pn invN
  have hE0 : yE 0 = ybar := cE.implicitFunction_apply_self pn invE
  have hNev : ∀ᶠ p in 𝓝 (0 : ℝ × E), p.1 + F (yN p, p.2) = 0 := by
    have := cN.eventually_apply_implicitFunction pn invN
    refine this.mono fun p hp => ?_
    simpa [fN, uN, hF0] using hp
  have hEev : ∀ᶠ ξ in 𝓝 (0 : E), F (yE ξ, ξ) = 0 := by
    have := cE.eventually_apply_implicitFunction pn invE
    refine this.mono fun ξ hξ => ?_
    simpa [fE, uE, hF0] using hξ
  have hNiff : ∀ᶠ v in 𝓝 (((0 : ℝ × E)), ybar), v.1.1 + F (v.2, v.1.2) = 0 ↔ yN v.1 = v.2 := by
    have := cN.eventually_apply_eq_iff_implicitFunction pn invN
    refine this.mono fun v hv => ?_
    simpa [fN, uN, hF0] using hv
  have hEiff : ∀ᶠ v in 𝓝 ((0 : E), ybar), F (v.2, v.1) = 0 ↔ yE v.1 = v.2 := by
    have := cE.eventually_apply_eq_iff_implicitFunction pn invE
    refine this.mono fun v hv => ?_
    simpa [fE, uE, hF0] using hv
  have hDN := (cN.hasStrictFDerivAt_implicitFunction pn invN).hasFDerivAt
  have hDE := (cE.hasStrictFDerivAt_implicitFunction pn invE).hasFDerivAt
  refine ⟨yN, yE, hN0, hE0, hNev, hEev, hNiff, hEiff, ?_⟩
  exact hasFDerivAt_natural_sub_efficient hN0 hE0 hFd hc hc0 hDN hDE hNev hEev

/-! ### Footnote 67 and eq. (2.9): the steady-state markup and the efficient gap -/

/-- Woodford (2003), footnote 67, p. 451: the steady-state composite markup
`μ̄ = 1/(1 − Φ_y)` (from `ṽ_y/ũ_c = 1 − Φ_y`, eq. (2.8)), in logs. -/
noncomputable def logMubar (Φ : ℝ) : ℝ := Real.log (1 / (1 - Φ))

/-- Woodford (2003), footnote 67, p. 451: `log μ̄ = Φ_y + O(Φ_y²)`, derivative form:
`log μ̄` vanishes at `Φ_y = 0` with slope one. -/
theorem hasDerivAt_log_mubar : logMubar 0 = 0 ∧ HasDerivAt logMubar 1 0 := by
  refine ⟨by simp [logMubar], ?_⟩
  have hfun : logMubar = fun Φ => -Real.log (1 - Φ) := by
    funext Φ; simp [logMubar, one_div, Real.log_inv]
  have h := (((hasDerivAt_id (0 : ℝ)).const_sub 1).log (by norm_num)).neg
  rw [hfun]
  exact h.congr_deriv (by norm_num)

/-- Woodford (2003), footnote 67, p. 451: the explicit second-order bound
`|log μ̄ − Φ_y| ≤ Φ_y²/(1 − |Φ_y|)` for `|Φ_y| < 1`. -/
theorem abs_log_mubar_sub_le {Φ : ℝ} (hΦ : |Φ| < 1) :
    |logMubar Φ - Φ| ≤ Φ ^ 2 / (1 - |Φ|) := by
  have hl : logMubar Φ = -Real.log (1 - Φ) := by
    simp [logMubar, one_div, Real.log_inv]
  rw [hl, show -Real.log (1 - Φ) - Φ = -(Real.log (1 - Φ) + Φ) by ring, abs_neg]
  exact ExpLogCES.abs_log_one_sub_add_le hΦ

/-- Woodford (2003), eq. (2.9), p. 394, recovered from (4.33)–(4.34): with `yN(m)` the log
natural rate at `log μ = m` (no disturbances) and `log Ȳ = yN(log μ̄(Φ_y))`, the efficient gap
`x*(Φ_y) = log Y* − log Ȳ` (with `log Y* = yN 0`) has derivative `(ω + σ⁻¹)⁻¹` at `Φ_y = 0`,
i.e. `x* = Φ_y/(ω + σ⁻¹) + O(Φ_y²)`. -/
theorem hasDerivAt_xstar {F yN : ℝ → ℝ} {c : ℝ} (hcont : ContinuousAt yN 0)
    (hF : HasDerivAt F c (yN 0)) (hc : c ≠ 0) (hN : ∀ᶠ m in 𝓝 0, m + F (yN m) = 0) :
    HasDerivAt (fun Φ => yN 0 - yN (logMubar Φ)) c⁻¹ 0 := by
  have hyN := hasDerivAt_naturalRate hcont hF hc hN
  obtain ⟨h0, hd⟩ := hasDerivAt_log_mubar
  have hyN' : HasDerivAt yN (-c⁻¹) (logMubar 0) := by rwa [h0]
  have := (hyN'.comp (0 : ℝ) hd).const_sub (yN 0)
  simpa using this

/-! ### (4.35)–(4.39): the linear model with a cost-push term -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), eq. (4.35), p. 450: `π_t = κ(Ŷ_t − Ŷⁿ_t) + β E_t π_{t+1}`. -/
def ASNatural (κ β : ℝ) (infl y yn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = κ • (y t - yn t) + β • 𝔼.E t (infl (t + 1))

/-- Woodford (2003), eq. (4.38), p. 451: `π_t = κ x_t + β E_t π_{t+1} + u_t`. -/
def ASGap (κ β : ℝ) (infl x u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = κ • x t + β • 𝔼.E t (infl (t + 1)) + u t

/-- Woodford (2003), eq. (4.37), p. 451: the welfare-relevant output gap
`x_t = log Y_t − log Yᵉ_t + x*` (`y`, `ye` are log levels measured from `log Ȳ`). -/
def welfareGap (y ye : ℕ → Ω → ℝ) (xstar : ℝ) (t : ℕ) : Ω → ℝ :=
  y t - ye t + fun _ => xstar

/-- Woodford (2003), eq. (4.39), p. 451: the cost-push shock `u_t = κ μ̂_t/(ω + σ⁻¹)`. -/
noncomputable def costPush (κ c : ℝ) (muhat : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (κ / c) • muhat t

omit 𝔼 in
/-- Woodford (2003), pp. 450–451: the linearised (4.33)–(4.34) relation
`Ŷⁿ_t = Ŷᵉ_t − x* − (ω+σ⁻¹)⁻¹ μ̂_t` (from `log Yⁿ = log Yᵉ − (ω+σ⁻¹)⁻¹ log μ` with
`log μ_t = log μ̄ + μ̂_t` and `x* = (ω+σ⁻¹)⁻¹ log μ̄`) makes `Ŷ − Ŷⁿ = x + (ω+σ⁻¹)⁻¹ μ̂`. -/
theorem gap_natural_eq {c xstar : ℝ} {y yn ye muhat : ℕ → Ω → ℝ}
    (hN : ∀ t, yn t = ye t - (fun _ => xstar) - c⁻¹ • muhat t) (t : ℕ) :
    y t - yn t = welfareGap y ye xstar t + c⁻¹ • muhat t := by
  rw [hN t]; unfold welfareGap; abel

/-- Woodford (2003), eqs. (4.35), (4.38), (4.39), pp. 450–451: given the linearised relation
between the natural and efficient rates, the AS relation (4.35) in terms of `Ŷ − Ŷⁿ` holds iff
(4.38) holds for the welfare-relevant gap (4.37) with the cost-push term (4.39). -/
theorem asNatural_iff_asGap {κ β c xstar : ℝ} {infl y yn ye muhat : ℕ → Ω → ℝ}
    (hN : ∀ t, yn t = ye t - (fun _ => xstar) - c⁻¹ • muhat t) :
    ASNatural 𝔼 κ β infl y yn ↔
      ASGap 𝔼 κ β infl (welfareGap y ye xstar) (costPush κ c muhat) := by
  have key : ∀ t, κ • (y t - yn t) =
      κ • welfareGap y ye xstar t + costPush κ c muhat t := by
    intro t
    rw [gap_natural_eq hN t, smul_add, smul_smul, costPush, div_eq_mul_inv]
  constructor
  · intro h t; rw [h t, key t]; abel
  · intro h t; rw [h t, key t]; abel

omit 𝔼 in
/-- Woodford (2003), eqs. (4.36)–(4.37) and (2.22), p. 451: the loss
`π_t² + λ(log Y_t − log Yᵉ_t)²` (4.36) is (2.22) `π_t² + λ(x_t − x*)²` for the welfare-relevant
gap (4.37). -/
theorem loss_436_eq_222 (lam xstar : ℝ) (infl y ye : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    infl t ω ^ 2 + lam * (y t ω - ye t ω) ^ 2 =
      infl t ω ^ 2 + lam * (welfareGap y ye xstar t ω - xstar) ^ 2 := by
  simp [welfareGap]

/-- Woodford (2003), p. 452: with a cost-push term it is "no longer possible to simultaneously
stabilize both inflation and the welfare-relevant output gap": `π ≡ 0` and `x ≡ 0` satisfy
(4.38)–(4.39) iff `μ̂ ≡ 0` (for `κ ≠ 0`, `ω + σ⁻¹ ≠ 0`). -/
theorem stabilize_both_iff {κ β c : ℝ} (hκ : κ ≠ 0) (hc : c ≠ 0) (muhat : ℕ → Ω → ℝ) :
    ASGap 𝔼 κ β (fun _ => 0) (fun _ => 0) (costPush κ c muhat) ↔ ∀ t, muhat t = 0 := by
  constructor
  · intro h t
    have ht := h t
    have hz : 𝔼.E t (0 : Ω → ℝ) = 0 := map_zero _
    simp only [smul_zero, zero_add] at ht
    rw [hz, smul_zero, zero_add, costPush] at ht
    have hk : κ / c ≠ 0 := div_ne_zero hκ hc
    have := ht.symm
    rwa [smul_eq_zero, or_iff_right hk] at this
  · intro h t
    have hz : 𝔼.E t (0 : Ω → ℝ) = 0 := map_zero _
    simp only [costPush, h t, smul_zero, zero_add]
    rw [hz, smul_zero, add_zero]

/-! ### Footnote 71: arithmetic -/

/-- Woodford (2003), footnote 69 and footnote 71, p. 452/454: losses are reported for the
annualised inflation rate `4π_t`, so the quarterly loss `π² + λ_q x²` is `1/16` of
`(4π)² + 16 λ_q x²`; the reported weight is `λ = 16 λ_q`. -/
theorem annualized_loss (pq lamq x : ℝ) :
    pq ^ 2 + lamq * x ^ 2 = ((4 * pq) ^ 2 + (16 * lamq) * x ^ 2) / 16 := by ring

/-- Woodford (2003), footnote 71, p. 454: the weight `λ = 16κφ` that makes complete
stabilisation of `log P_t + φ x_t` optimal (the optimality itself is Chapter 7). -/
def lambdaOfPhi (κ φ : ℝ) : ℝ := 16 * κ * φ

/-- Woodford (2003), footnote 71, p. 454: complete stabilisation of `log P_t + φ x_t` is the
same as the targeting rule `π_t + φ(x_t − x_{t−1}) = 0` for `t ≥ 1` (with `π_t = p_t − p_{t−1}`). -/
theorem targeting_of_stable_index {p x : ℕ → ℝ} {φ C : ℝ} (h : ∀ t, p t + φ * x t = C)
    (t : ℕ) : (p (t + 1) - p t) + φ * (x (t + 1) - x t) = 0 := by
  have h1 := h (t + 1); have h0 := h t
  linear_combination h1 - h0

/-- Woodford (2003), footnote 71, p. 454: when `Yᵉ` is constant, `x_t = Ŷ_t + const`, so
nominal GDP `log P_t + Ŷ_t` differs from the index `log P_t + x_t` (`φ = 1`) by a constant:
nominal GDP targeting is the case `φ = 1`. -/
theorem ngdp_index_eq (p yhat : ℕ → ℝ) (ye xstar : ℝ) (t : ℕ) :
    p t + yhat t = (p t + 1 * (yhat t - ye + xstar)) + (ye - xstar) := by ring

/-- Woodford (2003), footnote 71, p. 454: nominal GDP targeting (`φ = 1`) corresponds to
`λ = 16κ`, which at the calibration `κ = 0.024` (Table 6.1) is `0.384 ≈ 0.38`. -/
theorem ngdp_lambda_calibrated :
    lambdaOfPhi 0.024 1 = 0.384 ∧ |lambdaOfPhi 0.024 1 - 0.38| < 0.005 := by
  unfold lambdaOfPhi
  constructor
  · norm_num
  · rw [abs_lt]; constructor <;> norm_num

end Woodford.StabilizationWelfare.CostPush
