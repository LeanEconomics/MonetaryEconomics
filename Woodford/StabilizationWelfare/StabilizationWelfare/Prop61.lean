/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.CrossSection
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Order.Compact

/-!
# Proposition 6.1: output-gap stability and welfare

Woodford (2003), *Interest and Prices*, Chapter 6, §2.1 (pp. 392–396) and Appendix E.1
(pp. 692–694).

## Definitions (2.3)–(2.8)

`periodUtility` (2.3), `uTilde` (2.4), `vTilde` (2.5), `realMC` (2.7), the elasticities
`omegaEl` (`ω = Ȳ ṽ_yy/ṽ_y`) and `sigmaInvEl` (`σ⁻¹ = −Ȳ u_cc/u_c`), the shock composites
`gShock` (`g = −u_cξ ξ/(Ȳ u_cc)`) and `qShock` (`q = −v_yξ ξ/(Ȳ v_yy)`), and the steady
state (2.8) `s(Ȳ, Ȳ; 0) = 1 − Φ`.

## (2.9) as an exact derivative

`logMC_hasStrictDerivAt`: `z ↦ log s(e^z, e^z; 0)` has derivative `ω + σ⁻¹` at `log Y*`.
`steadyState_family`: the steady state is a genuine smooth family `Φ ↦ Ȳ(Φ)` (inverse function
theorem), it solves (2.8) for all small `Φ`, it is locally unique, and
`d log(Ȳ/Y*)/dΦ = −1/(ω + σ⁻¹)` at `Φ = 0` (2.9). `eq29_littleO` gives the first-order form
`log(Ȳ/Y*) = −Φ/(ω+σ⁻¹) + o(Φ)`, and `eq29_O2` the book's `O(Φ²)` remainder when `ṽ_y`,
`u_c` are `C²` (via `OneParamTaylor.taylor_one_bigO` and `eq29_bigO`). With the elasticities
evaluated at the moving steady state, `xstar_rem`/`eq29_xstar` give
`x*(Φ) − Φ/(σ⁻¹(Φ) + ω(Φ)) = O(Φ²)`, and `prop61_phiDep` states Proposition 6.1 with
`Φ`-dependent coefficients. This is how the survey's imprecision 26
(`Ȳ` moves with the expansion parameter `Φ`) is handled: the elasticities `σ⁻¹`, `ω` in the
identities below are those at the current steady state `Ȳ(Φ)`, and `lossQ_freeze` bounds the
effect of freezing them at `Φ = 0` by `Φ` times a quadratic (weighted degree three).

## Layer A: Proposition 6.1 as an exact identity

* (E.2) `uTaylor_eq`, (E.3) `vTaylor_eq`, (E.4) `integral_Tv`: the second-order Taylor
  polynomials of `ũ`, `ṽ` in log deviations, with all remainders explicit (the coefficient
  forms `uTaylor_eq_of_coeffs`, `vTaylor_eq_of_coeffs` need no nondegeneracy; they are the
  (E.2)/(E.3) identities used by the other propositions of the chapter; the exponential
  remainder `expRem` and its cubic bound are `ExpLogCES.expRem`, `ExpLogCES.abs_expRem_le`).
* **Theorem A1** `thmA1`: `Tu − E_i Tv = −½[(σ⁻¹+ω)(x − x*)² + (θ⁻¹+ω) var_i ŷ] + tip + R3`,
  where `tipA` depends only on `(g, q, Φ)` and `R3` is an explicit polynomial of weighted degree
  at least three (`R3_scale`: `R3(sY, s²V, sg, sq, sΦ, s³e, s²n, s²k) = s³ R3Q(s, …)`; weights:
  `Ŷ, g, q, Φ` one; `var_i ŷ`, the natural-rate error `n` and the `x*` error `k` two; the
  (E.5) error `e` three). `Ru_scale`, `Rv_scale`: the same for the remainders of (E.2), (E.3).
* `prop61_layerA` (**Proposition 6.1, (2.10)/(E.1), exact**): the Taylor polynomial of
  `U_t = ũ(Y_t) − ∫ ṽ(y_t(i)) di` equals
  `Ȳ u_c {−½[(σ⁻¹+ω)(x_t − x*)² + (θ⁻¹+ω) var_i ŷ_t(i)] + R}` plus t.i.p., with
  `R = R3 + Ru − ∫ Rv` explicit; `prop61_ces` adds the CES aggregate `Ŷ = logMeanExp` and the
  explicit bound `|e| ≤ r² B var_i ŷ` on the (E.5) error.
* (2.11) `R3_isBigO`, `eq211_orders`, `eq211_remainder`: if `Φ`, `g`, `q` are
  `O(s)` and `ŷ(i)` is uniformly `O(s)` (`s` bounding `φ, ξ`), then `R3 = O(s³)`.
* (2.13) `lossQ_disp`: `(θ⁻¹+ω) θ² Δ = θ(1+ωθ) Δ`, giving `prop61_disp`.
-/

namespace Woodford.StabilizationWelfare.Prop61

open MeasureTheory Filter Topology Asymptotics
open Woodford.StabilizationWelfare.CrossSection
open OneParamTaylor (taylor_one_bigO bigO_mul bigO_weaken)
open ExpLogCES (expRem)

variable {G : Type*} [MeasurableSpace G]

/-! ### Definitions (2.3)–(2.8) -/

/-- Woodford (2003), eq. (2.3), p. 392: period utility as a function of production,
`U_t = ũ(Y_t; ξ̃_t) − ∫₀¹ ṽ(y_t(i); ξ̃_t) di`. -/
noncomputable def periodUtility (μ : Measure G) (ut vt : ℝ → ℝ) (Y : ℝ) (y : G → ℝ) : ℝ :=
  ut Y - ∫ i, vt (y i) ∂μ

/-- Woodford (2003), eq. (2.4), p. 393: `ũ(Y; ξ̃) = u(Y − G; ξ)`. -/
def uTilde (u : ℝ → ℝ) (Gov Y : ℝ) : ℝ := u (Y - Gov)

/-- Woodford (2003), eq. (2.5), p. 393: `ṽ(y; ξ̃) = v(f⁻¹(y/A); ξ)`. -/
noncomputable def vTilde (v finv : ℝ → ℝ) (A y : ℝ) : ℝ := v (finv (y / A))

/-- Woodford (2003), p. 392 ((2.2) to (2.3)): using `C = Y − G` and `y(i) = A f(h(i))`
(so `h(i) = f⁻¹(y(i)/A)`), `u(C) − ∫ v(h(i)) di = ũ(Y) − ∫ ṽ(y(i)) di`. -/
theorem utility_of_production (μ : Measure G) {u v finv : ℝ → ℝ} {C Gov A Y : ℝ}
    {y h : G → ℝ} (hC : C = Y - Gov) (hinv : ∀ i, finv (y i / A) = h i) :
    u C - ∫ i, v (h i) ∂μ = periodUtility μ (uTilde u Gov) (vTilde v finv A) Y y := by
  unfold periodUtility uTilde vTilde
  simp only [hinv, hC]

/-- Woodford (2003), eq. (2.7), p. 393: real marginal cost `s(y, Y; ξ̃) = ṽ_y(y)/u_c(Y)`. -/
noncomputable def realMC (vy uc : ℝ → ℝ) (y Y : ℝ) : ℝ := vy y / uc Y

/-- Woodford (2003), p. 393: `ω = Ȳ ṽ_yy/ṽ_y`, the elasticity of `ṽ_y` (of real marginal cost
with respect to own output). -/
noncomputable def omegaEl (Ybar vy vyy : ℝ) : ℝ := Ybar * vyy / vy

/-- Woodford (2003), p. 393: `σ⁻¹ = −Ȳ u_cc/u_c`. -/
noncomputable def sigmaInvEl (Ybar uc ucc : ℝ) : ℝ := -(Ybar * ucc / uc)

/-- Woodford (2003), App. E, p. 693: `g_t = −u_cξ ξ̃_t/(Ȳ u_cc)` (here `Cu` is the value of
`u_cξ ξ̃_t`). -/
noncomputable def gShock (Ybar ucc Cu : ℝ) : ℝ := -(Cu / (Ybar * ucc))

/-- Woodford (2003), App. E, p. 693: `q_t = −v_yξ ξ̃_t/(Ȳ v_yy)` (here `Cv` is the value of
`v_yξ ξ̃_t`). -/
noncomputable def qShock (Ybar vyy Cv : ℝ) : ℝ := -(Cv / (Ybar * vyy))

/-- Woodford (2003), eq. (2.8), p. 393: `Ȳ` is the steady state for the overall distortion
`Φ`, `s(Ȳ, Ȳ; 0) = 1 − Φ`. -/
def IsSteadyState (vy uc : ℝ → ℝ) (Φ Ybar : ℝ) : Prop := realMC vy uc Ybar Ybar = 1 - Φ

/-! ### (2.9): the steady state as a smooth family in `Φ` -/

/-- Woodford (2003), p. 394: `z ↦ log s(e^z, e^z; 0)`, real marginal cost along symmetric
output levels `Y = e^z`. -/
noncomputable def logMC (vy uc : ℝ → ℝ) (z : ℝ) : ℝ :=
  Real.log (realMC vy uc (Real.exp z) (Real.exp z))

/-- Woodford (2003), p. 393 (the elasticities of real marginal cost, exact derivative): if
`ṽ_y`, `u_c` are strictly differentiable at `Y > 0` with positive values, then
`d log s(e^z, e^z; 0)/dz = ω + σ⁻¹` at `z = log Y`. -/
theorem logMC_hasStrictDerivAt {vy uc : ℝ → ℝ} {Y vyy ucc : ℝ} (hY : 0 < Y)
    (hv : 0 < vy Y) (hu : 0 < uc Y) (hdv : HasStrictDerivAt vy vyy Y)
    (hdu : HasStrictDerivAt uc ucc Y) :
    HasStrictDerivAt (logMC vy uc) (omegaEl Y (vy Y) vyy + sigmaInvEl Y (uc Y) ucc)
      (Real.log Y) := by
  have he : HasStrictDerivAt Real.exp Y (Real.log Y) := by
    simpa [Real.exp_log hY] using Real.hasStrictDerivAt_exp (Real.log Y)
  have hel : Real.exp (Real.log Y) = Y := Real.exp_log hY
  have hdv' : HasStrictDerivAt vy vyy (Real.exp (Real.log Y)) := by rwa [hel]
  have hdu' : HasStrictDerivAt uc ucc (Real.exp (Real.log Y)) := by rwa [hel]
  have h1 := hdv'.comp (Real.log Y) he
  have h2 := hdu'.comp (Real.log Y) he
  have hu' : (uc ∘ Real.exp) (Real.log Y) ≠ 0 := by
    rw [Function.comp_apply, hel]
    exact hu.ne'
  have h3 := h1.div h2 hu'
  have hq : (fun z => (vy ∘ Real.exp) z / (uc ∘ Real.exp) z) (Real.log Y) ≠ 0 := by
    simp only [Function.comp, hel]
    exact (div_pos hv hu).ne'
  have h4 := h3.log hq
  unfold logMC realMC
  convert h4 using 1
  · rfl
  · simp only [Function.comp_apply, Pi.div_apply, hel, omegaEl, sigmaInvEl]
    field_simp
    ring

/-- Woodford (2003), (2.8)–(2.9), pp. 393–394 (**the steady state as a smooth family, and
(2.9) as an exact derivative**). Let `Y* > 0` be efficient, `s(Y*, Y*; 0) = 1`, with
`ṽ_y`, `u_c` strictly differentiable there and `ω + σ⁻¹ ≠ 0`. Then there is a function
`z(Φ) = log Ȳ(Φ)` with `z(0) = log Y*`, which for all small `Φ` solves (2.8)
`s(Ȳ(Φ), Ȳ(Φ); 0) = 1 − Φ`, is the only solution near `log Y*`, and satisfies
`d log(Ȳ/Y*)/dΦ = −1/(ω + σ⁻¹)` at `Φ = 0` (strict derivative). -/
theorem steadyState_family {vy uc : ℝ → ℝ} {Ystar vyy ucc : ℝ} (hY : 0 < Ystar)
    (hv : 0 < vy Ystar) (hu : 0 < uc Ystar) (hdv : HasStrictDerivAt vy vyy Ystar)
    (hdu : HasStrictDerivAt uc ucc Ystar) (heff : realMC vy uc Ystar Ystar = 1)
    (hden : omegaEl Ystar (vy Ystar) vyy + sigmaInvEl Ystar (uc Ystar) ucc ≠ 0) :
    ∃ z : ℝ → ℝ, z 0 = Real.log Ystar ∧
      (∀ᶠ Φ in 𝓝 0, IsSteadyState vy uc Φ (Real.exp (z Φ))) ∧
      (∀ᶠ w in 𝓝 (Real.log Ystar), ∀ Φ, logMC vy uc w = Real.log (1 - Φ) → w = z Φ) ∧
      HasStrictDerivAt (fun Φ => Real.log (Real.exp (z Φ) / Ystar))
        (-(omegaEl Ystar (vy Ystar) vyy + sigmaInvEl Ystar (uc Ystar) ucc)⁻¹) 0 := by
  set f' := omegaEl Ystar (vy Ystar) vyy + sigmaInvEl Ystar (uc Ystar) ucc with hf'
  have hf := logMC_hasStrictDerivAt hY hv hu hdv hdu
  have hfa : logMC vy uc (Real.log Ystar) = 0 := by
    unfold logMC
    rw [Real.exp_log hY, heff, Real.log_one]
  set g := HasStrictDerivAt.localInverse (logMC vy uc) f' (Real.log Ystar) hf hden with hg
  have hleft := hf.eventually_left_inverse hden
  have hright := hf.eventually_right_inverse hden
  have hgd := hf.to_localInverse hden
  rw [hfa] at hright hgd
  have hl0 : Real.log (1 - 0) = 0 := by simp
  have hlogd : HasStrictDerivAt (fun Φ : ℝ => Real.log (1 - Φ)) (-1 / (1 - 0)) 0 :=
    ((hasStrictDerivAt_id (0 : ℝ)).const_sub 1).log (by norm_num)
  have hgd' : HasStrictDerivAt g f'⁻¹ (Real.log (1 - 0)) := by rw [hl0]; exact hgd
  have hzd := hgd'.comp 0 hlogd
  have hlogc : Tendsto (fun Φ : ℝ => Real.log (1 - Φ)) (𝓝 0) (𝓝 0) := by
    have := (HasDerivAt.continuousAt (HasStrictDerivAt.hasDerivAt hlogd)).tendsto
    simpa using this
  have hz0 : g 0 = Real.log Ystar := by
    have := hleft.self_of_nhds
    rwa [hfa] at this
  refine ⟨fun Φ => g (Real.log (1 - Φ)), by simpa using hz0, ?_, ?_, ?_⟩
  · -- the family solves (2.8)
    have hR := hlogc.eventually hright
    have hzc : Tendsto (fun Φ => g (Real.log (1 - Φ))) (𝓝 0) (𝓝 (Real.log Ystar)) := by
      have := (HasDerivAt.continuousAt (HasStrictDerivAt.hasDerivAt hzd)).tendsto
      simp only [Function.comp_apply, sub_zero, Real.log_one, hz0] at this
      exact this
    have hratio : ContinuousAt (fun w => vy (Real.exp w) / uc (Real.exp w)) (Real.log Ystar) := by
      have he := Real.continuous_exp.continuousAt (x := Real.log Ystar)
      have hv' : ContinuousAt vy (Real.exp (Real.log Ystar)) := by
        rw [Real.exp_log hY]; exact HasDerivAt.continuousAt (HasStrictDerivAt.hasDerivAt hdv)
      have hu' : ContinuousAt uc (Real.exp (Real.log Ystar)) := by
        rw [Real.exp_log hY]; exact HasDerivAt.continuousAt (HasStrictDerivAt.hasDerivAt hdu)
      exact (hv'.comp he).div (hu'.comp he) (by simp [Real.exp_log hY, hu.ne'])
    have hpos0 : 0 < vy (Real.exp (Real.log Ystar)) / uc (Real.exp (Real.log Ystar)) := by
      rw [Real.exp_log hY]; exact div_pos hv hu
    have hpos := hzc.eventually (hratio.eventually (lt_mem_nhds hpos0))
    have h1 : ∀ᶠ Φ in 𝓝 (0 : ℝ), 0 < 1 - Φ := by
      have : Tendsto (fun Φ : ℝ => 1 - Φ) (𝓝 0) (𝓝 1) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_id (x := 𝓝 (0 : ℝ)))
      exact this.eventually (lt_mem_nhds one_pos)
    filter_upwards [hR, hpos, h1] with Φ hΦ hp h1
    unfold IsSteadyState realMC
    unfold logMC realMC at hΦ
    exact Real.log_injOn_pos (Set.mem_Ioi.2 hp) (Set.mem_Ioi.2 h1) hΦ
  · -- local uniqueness
    filter_upwards [hleft] with w hw Φ hΦ
    rw [← hw, hΦ]
  · -- (2.9)
    have heq : (fun Φ => Real.log (Real.exp (g (Real.log (1 - Φ))) / Ystar)) =
        fun Φ => g (Real.log (1 - Φ)) - Real.log Ystar := by
      funext Φ
      rw [Real.log_div (Real.exp_pos _).ne' hY.ne', Real.log_exp]
    rw [heq]
    have h := hzd.sub_const (Real.log Ystar)
    rw [show f'⁻¹ * (-1 / (1 - 0)) = -f'⁻¹ by ring] at h
    exact h

/-- Woodford (2003), eq. (2.9), p. 394 (**the first-order form**): if `F(Φ) = log(Ȳ(Φ)/Y*)` has
derivative `−1/(ω + σ⁻¹)` at `0` and `F(0) = 0`, then
`log(Ȳ/Y*) = −Φ/(ω + σ⁻¹) + o(Φ)`. (The book's `O(Φ²)` needs one more derivative.) -/
theorem eq29_littleO {F : ℝ → ℝ} {c : ℝ} (hF : HasDerivAt F (-c⁻¹) 0) (hF0 : F 0 = 0) :
    (fun Φ => F Φ + Φ / c) =o[𝓝 0] fun Φ => Φ := by
  have h := hasDerivAt_iff_isLittleO.mp hF
  simp only [hF0, sub_zero, smul_eq_mul] at h
  refine h.congr_left fun Φ => ?_
  rw [div_eq_mul_inv]
  ring

/-- Woodford (2003), eq. (2.9), p. 394 (**the `O(Φ²)` remainder, abstract form**): if `h` has
the first-order expansion `h w − h z* − f'(w − z*) = O((w − z*)²)` with `f' ≠ 0`, `h z* = 0`,
and `z` is differentiable at `0` with `z(0) = z*` and `h(z(Φ)) = log(1 − Φ)` for small `Φ`,
then `z(Φ) − z* = −Φ/f' + O(Φ²)`. -/
theorem eq29_bigO {h z : ℝ → ℝ} {zs f' d : ℝ} (hf' : f' ≠ 0)
    (hT : (fun w => h w - h zs - f' * (w - zs)) =O[𝓝 zs] fun w => (w - zs) ^ 2)
    (hz0 : z 0 = zs) (hzd : HasDerivAt z d 0) (hh0 : h zs = 0)
    (hsol : ∀ᶠ Φ in 𝓝 0, h (z Φ) = Real.log (1 - Φ)) :
    (fun Φ => z Φ - zs + Φ / f') =O[𝓝 0] fun Φ => Φ ^ 2 := by
  have hzt : Tendsto z (𝓝 0) (𝓝 zs) := by
    rw [← hz0]
    exact (HasDerivAt.continuousAt hzd).tendsto
  have h1 : (fun Φ => z Φ - zs) =O[𝓝 0] fun Φ => Φ := by
    have := HasDerivAt.isBigO_sub hzd
    simp only [hz0, sub_zero] at this
    exact this
  have h2 : (fun Φ => h (z Φ) - h zs - f' * (z Φ - zs)) =O[𝓝 0] fun Φ => Φ ^ 2 :=
    (hT.comp_tendsto hzt).trans (h1.pow 2)
  have h3 : (fun Φ : ℝ => Real.log (1 - Φ) + Φ) =O[𝓝 0] fun Φ => Φ ^ 2 :=
    ExpLogCES.istar_expansion.congr_left fun Φ => by ring
  have h4 := (h3.sub h2).const_mul_left f'⁻¹
  refine h4.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [hsol] with Φ hΦ
  rw [hΦ, hh0]
  field_simp
  ring

/-- Woodford (2003), **eq. (2.9), p. 394, with the book's `O(Φ²)` remainder**: if `ṽ_y` and
`u_c` are `C²` at the efficient level `Y*` (positive, `s(Y*, Y*; 0) = 1`, `ω + σ⁻¹ ≠ 0`), the
steady-state family of `steadyState_family` satisfies
`log(Ȳ(Φ)/Y*) = −Φ/(ω + σ⁻¹) + O(Φ²)`. -/
theorem eq29_O2 {vy uc : ℝ → ℝ} {Ystar : ℝ} (hY : 0 < Ystar) (hv : 0 < vy Ystar)
    (hu : 0 < uc Ystar) (hv2 : ContDiffAt ℝ 2 vy Ystar) (hu2 : ContDiffAt ℝ 2 uc Ystar)
    (heff : realMC vy uc Ystar Ystar = 1)
    (hden : omegaEl Ystar (vy Ystar) (deriv vy Ystar) +
      sigmaInvEl Ystar (uc Ystar) (deriv uc Ystar) ≠ 0) :
    ∃ z : ℝ → ℝ, z 0 = Real.log Ystar ∧
      (∀ᶠ Φ in 𝓝 0, IsSteadyState vy uc Φ (Real.exp (z Φ))) ∧
      (fun Φ => Real.log (Real.exp (z Φ) / Ystar) +
        Φ / (omegaEl Ystar (vy Ystar) (deriv vy Ystar) +
          sigmaInvEl Ystar (uc Ystar) (deriv uc Ystar))) =O[𝓝 0] fun Φ => Φ ^ 2 := by
  set f' := omegaEl Ystar (vy Ystar) (deriv vy Ystar) +
    sigmaInvEl Ystar (uc Ystar) (deriv uc Ystar) with hf'
  have hdv : HasStrictDerivAt vy (deriv vy Ystar) Ystar := hv2.hasStrictDerivAt (by norm_num)
  have hdu : HasStrictDerivAt uc (deriv uc Ystar) Ystar := hu2.hasStrictDerivAt (by norm_num)
  obtain ⟨z, hz0, hss, -, hder⟩ := steadyState_family hY hv hu hdv hdu heff hden
  have hel : Real.exp (Real.log Ystar) = Ystar := Real.exp_log hY
  have hC2 : ContDiffAt ℝ 2 (logMC vy uc) (Real.log Ystar) := by
    have hexp : ContDiffAt ℝ 2 Real.exp (Real.log Ystar) := Real.contDiff_exp.contDiffAt
    have hv' : ContDiffAt ℝ 2 vy (Real.exp (Real.log Ystar)) := by rwa [hel]
    have hu' : ContDiffAt ℝ 2 uc (Real.exp (Real.log Ystar)) := by rwa [hel]
    have hq := (hv'.comp _ hexp).div (hu'.comp _ hexp) (by simpa [hel] using hu.ne')
    exact hq.log (by simpa [hel] using (div_pos hv hu).ne')
  have hder1 : deriv (logMC vy uc) (Real.log Ystar) = f' :=
    (logMC_hasStrictDerivAt hY hv hu hdv hdu).hasDerivAt.deriv
  have hT := taylor_one_bigO hC2
  rw [hder1] at hT
  have hh0 : logMC vy uc (Real.log Ystar) = 0 := by
    unfold logMC
    rw [hel, heff, Real.log_one]
  have hsol : ∀ᶠ Φ in 𝓝 0, logMC vy uc (z Φ) = Real.log (1 - Φ) := by
    filter_upwards [hss] with Φ hΦ
    unfold IsSteadyState at hΦ
    unfold logMC
    rw [hΦ]
  have hzd : HasDerivAt z (-f'⁻¹) 0 := by
    convert hder.hasDerivAt.add_const (Real.log Ystar) using 1
    funext x
    rw [Real.log_div (Real.exp_pos _).ne' hY.ne', Real.log_exp]
    ring
  refine ⟨z, hz0, hss, ?_⟩
  have := eq29_bigO hden hT hz0 hzd hh0 hsol
  refine this.congr_left fun Φ => ?_
  rw [Real.log_div (Real.exp_pos _).ne' hY.ne', Real.log_exp]

/-- Woodford (2003), p. 394 and imprecision 26 of the survey: the quadratic form of (2.10),
`(σ⁻¹ + ω) X² + (θ⁻¹ + ω) V`. -/
noncomputable def lossQ (sinv omega θ X V : ℝ) : ℝ := (sinv + omega) * X ^ 2 + (θ⁻¹ + omega) * V

/-- Woodford (2003), Prop. 6.1, p. 394 (**freezing the coefficients at `Φ = 0`**): the
elasticities `σ⁻¹(Φ)`, `ω(Φ)` are evaluated at the steady state `Ȳ(Φ)`, which moves with `Φ`.
If they are Lipschitz in `Φ` (`|σ⁻¹(Φ) − σ⁻¹(0)| ≤ L|Φ|`, `|ω(Φ) − ω(0)| ≤ L|Φ|`), replacing them
by their `Φ = 0` values changes the loss by at most `2 L |Φ| (X² + |V|)`, a term of weighted
degree three. -/
theorem lossQ_freeze {a0 aΦ w0 wΦ θ X V L Φ : ℝ} (ha : |aΦ - a0| ≤ L * |Φ|)
    (hw : |wΦ - w0| ≤ L * |Φ|) :
    |lossQ aΦ wΦ θ X V - lossQ a0 w0 θ X V| ≤ 2 * L * |Φ| * (X ^ 2 + |V|) := by
  unfold lossQ
  have e : (aΦ + wΦ) * X ^ 2 + (θ⁻¹ + wΦ) * V - ((a0 + w0) * X ^ 2 + (θ⁻¹ + w0) * V) =
      ((aΦ - a0) + (wΦ - w0)) * X ^ 2 + (wΦ - w0) * V := by ring
  rw [e]
  have hX : 0 ≤ X ^ 2 := sq_nonneg X
  have h1 : |((aΦ - a0) + (wΦ - w0)) * X ^ 2| ≤ 2 * L * |Φ| * X ^ 2 := by
    rw [abs_mul, abs_of_nonneg hX]
    have := abs_add_le (aΦ - a0) (wΦ - w0)
    nlinarith
  have h2 : |(wΦ - w0) * V| ≤ L * |Φ| * |V| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hw (abs_nonneg V)
  have h3 := abs_add_le (((aΦ - a0) + (wΦ - w0)) * X ^ 2) ((wΦ - w0) * V)
  have hL : 0 ≤ L * |Φ| := (abs_nonneg _).trans hw
  nlinarith [abs_nonneg V]

/-! ### Layer A: the Taylor-coefficient identities (E.2)–(E.4) -/

/-- Woodford (2003), p. 693: `Ỹ = Y − Ȳ = Ȳ (Ŷ + Ŷ²/2 + expRem Ŷ)` exactly, `Y = Ȳ e^Ŷ`. -/
theorem levelDev_eq (Ybar Y : ℝ) :
    Ybar * Real.exp Y - Ybar = Ybar * (Y + Y ^ 2 / 2 + expRem Y) := by
  rw [← ExpLogCES.exp_sub_one_eq]
  ring

/-- Woodford (2003), eq. (E.2), first line, p. 692: the second-order Taylor polynomial of
`ũ(Y; ξ̃)` at `(Ȳ, 0)` in the level deviation `Ỹ`, with `Lu = u_ξ ξ̃`, `Cu = u_cξ ξ̃`,
`Qu = ξ̃' u_ξξ ξ̃`. -/
noncomputable def uTaylor (ubar uc ucc Lu Cu Qu Ytil : ℝ) : ℝ :=
  ubar + uc * Ytil + Lu + ucc / 2 * Ytil ^ 2 + Cu * Ytil + Qu / 2

/-- Woodford (2003), eq. (E.2), last line: the policy-relevant part
`Ŷ + ½(1 − σ⁻¹) Ŷ² + σ⁻¹ g Ŷ` (normalised by `Ȳ u_c`). -/
noncomputable def Tu (sinv g Y : ℝ) : ℝ := Y + (1 - sinv) / 2 * Y ^ 2 + sinv * g * Y

/-- Woodford (2003), eq. (E.2): the explicit remainder of (E.2) (normalised by `Ȳ u_c`), with
`r = expRem Ŷ`. -/
noncomputable def Ru (sinv g Y r : ℝ) : ℝ :=
  r - sinv / 2 * ((Y + Y ^ 2 / 2 + r) ^ 2 - Y ^ 2) + sinv * g * (Y ^ 2 / 2 + r)

/-- Woodford (2003), eq. (E.2), p. 692 (**exact, in terms of the coefficients**): if
`u_cc = −σ⁻¹u_c/Ȳ` and `u_cξ ξ̃ = σ⁻¹u_c g` (the definitions of `σ⁻¹` and `g`), then at
`Ỹ = Ȳ(Ŷ + Ŷ²/2 + r)`, `ũ-Taylor = (ū + u_ξ ξ̃ + ½ ξ̃' u_ξξ ξ̃) + Ȳ u_c [Tu + Ru]`; the first
bracket is t.i.p. No nondegeneracy (not even `Ȳ ≠ 0`) is needed. -/
theorem uTaylor_eq_of_coeffs {ubar uc ucc Lu Cu Qu Ybar sinv g Y r : ℝ}
    (hucc : ucc = -(sinv * uc / Ybar)) (hCu : Cu = sinv * uc * g) :
    uTaylor ubar uc ucc Lu Cu Qu (Ybar * (Y + Y ^ 2 / 2 + r)) =
      (ubar + Lu + Qu / 2) + Ybar * uc * (Tu sinv g Y + Ru sinv g Y r) := by
  subst hucc hCu
  unfold uTaylor Tu Ru
  field_simp
  ring

/-- Woodford (2003), eq. (E.2), p. 692 (**exact**): with `σ⁻¹ = −Ȳ u_cc/u_c`,
`g = −u_cξ ξ̃/(Ȳ u_cc)` and `Ỹ = Ȳ(Ŷ + Ŷ²/2 + r)`,
`ũ-Taylor = (ū + u_ξ ξ̃ + ½ ξ̃' u_ξξ ξ̃) + Ȳ u_c [Tu + Ru]`; the first bracket is t.i.p. -/
theorem uTaylor_eq {ubar uc ucc Lu Cu Qu Ybar Y r : ℝ} (hY : Ybar ≠ 0) (huc : uc ≠ 0)
    (hucc : ucc ≠ 0) :
    uTaylor ubar uc ucc Lu Cu Qu (Ybar * (Y + Y ^ 2 / 2 + r)) =
      (ubar + Lu + Qu / 2) + Ybar * uc *
        (Tu (sigmaInvEl Ybar uc ucc) (gShock Ybar ucc Cu) Y +
          Ru (sigmaInvEl Ybar uc ucc) (gShock Ybar ucc Cu) Y r) :=
  uTaylor_eq_of_coeffs (by unfold sigmaInvEl; field_simp)
    (by unfold sigmaInvEl gShock; field_simp)

/-- Woodford (2003), eq. (E.3), first line, p. 693: the second-order Taylor polynomial of
`ṽ(y; ξ̃)` at `(Ȳ, 0)` in the level deviation `ỹ`, with `Lv = v_ξ ξ̃`, `Cv = v_yξ ξ̃`,
`Qv = ξ̃' v_ξξ ξ̃`. -/
noncomputable def vTaylor (vbar vy vyy Lv Cv Qv ytil : ℝ) : ℝ :=
  vbar + vy * ytil + Lv + vyy / 2 * ytil ^ 2 + Cv * ytil + Qv / 2

/-- Woodford (2003), eq. (E.3), last line: the policy-relevant part
`(1 − Φ) ŷ + ½(1 + ω) ŷ² − ω q ŷ` (normalised by `Ȳ u_c`). -/
noncomputable def Tv (Φ omega q y : ℝ) : ℝ := (1 - Φ) * y + (1 + omega) / 2 * y ^ 2 - omega * q * y

/-- Woodford (2003), eq. (E.3): the explicit remainder (normalised by `Ȳ u_c`), including the
dropped `Φ × (quadratic)` terms ("terms of higher than second order given that `Φ` is an
expansion parameter", p. 694). -/
noncomputable def Rv (Φ omega q y r : ℝ) : ℝ :=
  (1 - Φ) * (r + omega / 2 * ((y + y ^ 2 / 2 + r) ^ 2 - y ^ 2) - omega * q * (y ^ 2 / 2 + r)) -
    Φ * ((1 + omega) / 2 * y ^ 2 - omega * q * y)

/-- Woodford (2003), eq. (E.3), p. 693 (**exact, in terms of the coefficients**): with the
steady-state condition `ṽ_y = (1 − Φ) u_c` ((2.7)–(2.8)), `v_yy = ωv_y/Ȳ`,
`v_yξ ξ̃ = −ωv_y q` (the definitions of `ω` and `q`) and `ỹ = Ȳ(ŷ + ŷ²/2 + r)`,
`ṽ-Taylor = (v̄ + v_ξ ξ̃ + ½ ξ̃' v_ξξ ξ̃) + Ȳ u_c [Tv + Rv]`; no nondegeneracy is needed. -/
theorem vTaylor_eq_of_coeffs {vbar vy vyy Lv Cv Qv Ybar uc Φ omega q y r : ℝ}
    (hvy : vy = (1 - Φ) * uc) (hvyy : vyy = omega * vy / Ybar)
    (hCv : Cv = -(omega * vy * q)) :
    vTaylor vbar vy vyy Lv Cv Qv (Ybar * (y + y ^ 2 / 2 + r)) =
      (vbar + Lv + Qv / 2) + Ybar * uc * (Tv Φ omega q y + Rv Φ omega q y r) := by
  subst hvyy hCv
  subst hvy
  unfold vTaylor Tv Rv
  field_simp
  ring

/-- Woodford (2003), eq. (E.3), p. 693 (**exact**): with the steady-state condition
`ṽ_y = (1 − Φ) u_c` ((2.7)–(2.8)), `ω = Ȳ ṽ_yy/ṽ_y`, `q = −v_yξ ξ̃/(Ȳ v_yy)` and
`ỹ = Ȳ(ŷ + ŷ²/2 + r)`, `ṽ-Taylor = (v̄ + v_ξ ξ̃ + ½ ξ̃' v_ξξ ξ̃) + Ȳ u_c [Tv + Rv]`. -/
theorem vTaylor_eq {vbar vy vyy Lv Cv Qv Ybar uc Φ y r : ℝ} (hY : Ybar ≠ 0)
    (hvy : vy = (1 - Φ) * uc) (hvy0 : vy ≠ 0) (hvyy : vyy ≠ 0) :
    vTaylor vbar vy vyy Lv Cv Qv (Ybar * (y + y ^ 2 / 2 + r)) =
      (vbar + Lv + Qv / 2) + Ybar * uc *
        (Tv Φ (omegaEl Ybar vy vyy) (qShock Ybar vyy Cv) y +
          Rv Φ (omegaEl Ybar vy vyy) (qShock Ybar vyy Cv) y r) :=
  vTaylor_eq_of_coeffs hvy (by unfold omegaEl; field_simp)
    (by unfold omegaEl qShock; field_simp)

/-- Woodford (2003), eq. (E.4), p. 694 (**exact**): integrating the policy-relevant part of
(E.3) over goods, `E_i Tv(ŷ(i)) = (1 − Φ) E_i ŷ + ½(1+ω)((E_i ŷ)² + var_i ŷ) − ω q E_i ŷ`. -/
theorem integral_Tv (μ : Measure G) [IsProbabilityMeasure μ] {yh : G → ℝ}
    (h1 : Integrable yh μ) (h2 : Integrable (fun i => yh i ^ 2) μ) (Φ omega q : ℝ) :
    ∫ i, Tv Φ omega q (yh i) ∂μ =
      (1 - Φ) * crossMean μ yh + (1 + omega) / 2 * (crossVar μ yh + crossMean μ yh ^ 2) -
        omega * q * crossMean μ yh := by
  have hpt : (fun i => Tv Φ omega q (yh i)) =
      fun i => ((1 - Φ - omega * q) * yh i) + (1 + omega) / 2 * yh i ^ 2 := by
    funext i
    unfold Tv
    ring
  rw [hpt, integral_add (h1.const_mul _) (h2.const_mul _), integral_const_mul,
    integral_const_mul, crossVar_eq μ h1 h2]
  unfold crossMean
  ring

/-! ### Theorem A1 (Proposition 6.1, exact polynomial identity) -/

/-- Woodford (2003), (E.6), p. 694: the first-order natural rate
`Ŷⁿ = (σ⁻¹ g + ω q)/(σ⁻¹ + ω)`. -/
noncomputable def natLin (sinv omega g q : ℝ) : ℝ := (sinv * g + omega * q) / (sinv + omega)

/-- Woodford (2003), (2.9)/(2.17): the first-order efficient gap `x* = Φ/(σ⁻¹ + ω)`. -/
noncomputable def xStarLin (sinv omega Φ : ℝ) : ℝ := Φ / (sinv + omega)

/-- Woodford (2003), (E.1): the terms independent of policy produced by completing the square,
`½(σ⁻¹ + ω)(Ŷⁿ + x*)²`, a function of the exogenous `g`, `q`, `Φ` only. -/
noncomputable def tipA (sinv omega g q Φ : ℝ) : ℝ :=
  (sinv + omega) / 2 * (natLin sinv omega g q + xStarLin sinv omega Φ) ^ 2

/-- Woodford (2003), (E.1)–(E.6) (**the explicit remainder of Theorem A1**). Arguments:
`Y = Ŷ`, `V = var_i ŷ`, `e` the (E.5) error (`E_i ŷ = Ŷ − ½(1−θ⁻¹)V − e`), `n` the error in
(E.6) (true natural rate `= natLin + n`), `k` the error in (2.9) (true `x* = xStarLin + k`). -/
noncomputable def R3 (sinv omega θ g q Φ Y V e n k : ℝ) : ℝ :=
  -Φ * ((1 - θ⁻¹) / 2 * V + e) + e -
    (1 + omega) / 2 * ((Y - (1 - θ⁻¹) / 2 * V - e) ^ 2 - Y ^ 2) -
    omega * q * ((1 - θ⁻¹) / 2 * V + e) -
    (sinv + omega) * (Y - natLin sinv omega g q - xStarLin sinv omega Φ) * (n + k) +
    (sinv + omega) / 2 * (n + k) ^ 2

/-- Woodford (2003), Prop. 6.1, App. E.1 (**Theorem A1, exact**): with
`E_i ŷ = Ŷ − ½(1 − θ⁻¹) var_i ŷ − e`, the true natural rate `Ŷⁿ = natLin + n`, the true
efficient gap `x* = xStarLin + k` and `x = Ŷ − Ŷⁿ`,
`Tu(Ŷ) − E_i Tv(ŷ) = −½[(σ⁻¹ + ω)(x − x*)² + (θ⁻¹ + ω) var_i ŷ] + tipA(g, q, Φ) + R3`. -/
theorem thmA1 {sinv omega θ g q Φ Y V e n k : ℝ} (hden : sinv + omega ≠ 0) :
    Tu sinv g Y - ((1 - Φ) * (Y - (1 - θ⁻¹) / 2 * V - e) +
        (1 + omega) / 2 * (V + (Y - (1 - θ⁻¹) / 2 * V - e) ^ 2) -
        omega * q * (Y - (1 - θ⁻¹) / 2 * V - e)) =
      -(1 / 2) * lossQ sinv omega θ
          ((Y - (natLin sinv omega g q + n)) - (xStarLin sinv omega Φ + k)) V +
        tipA sinv omega g q Φ + R3 sinv omega θ g q Φ Y V e n k := by
  unfold Tu lossQ tipA R3 natLin xStarLin
  field_simp
  ring

/-- Woodford (2003), App. E.1: the cofactor of `s³` in `R3` under the weighted scaling. -/
noncomputable def R3Q (sinv omega θ g q Φ Y V e n k s : ℝ) : ℝ :=
  -Φ * ((1 - θ⁻¹) / 2 * V + s * e) + e -
    (1 + omega) / 2 * (-2 * Y * ((1 - θ⁻¹) / 2 * V + s * e) +
      s * ((1 - θ⁻¹) / 2 * V + s * e) ^ 2) -
    omega * q * ((1 - θ⁻¹) / 2 * V + s * e) -
    (sinv + omega) * (Y - natLin sinv omega g q - xStarLin sinv omega Φ) * (n + k) +
    (sinv + omega) / 2 * s * (n + k) ^ 2

/-- Woodford (2003), (E.1) "`O(‖Φ, ŷ, ξ̃‖³)`" (**the scaling lemma: `R3` has weighted degree at
least three**): substituting `(sŶ, s²V, sg, sq, sΦ, s³e, s²n, s²k)` multiplies `R3` by `s³`
times the polynomial `R3Q`. -/
theorem R3_scale (sinv omega θ g q Φ Y V e n k s : ℝ) :
    R3 sinv omega θ (s * g) (s * q) (s * Φ) (s * Y) (s ^ 2 * V) (s ^ 3 * e) (s ^ 2 * n)
        (s ^ 2 * k) =
      s ^ 3 * R3Q sinv omega θ g q Φ Y V e n k s := by
  unfold R3 R3Q natLin xStarLin
  ring

/-- Woodford (2003), (E.2): the cofactor of `s³` in `Ru` under the weighted scaling. -/
noncomputable def RuQ (sinv g Y r s : ℝ) : ℝ :=
  r - sinv / 2 * ((Y ^ 2 / 2 + s * r) * (2 * Y + s * (Y ^ 2 / 2 + s * r))) +
    sinv * g * (Y ^ 2 / 2 + s * r)

/-- Woodford (2003), (E.2) (**scaling lemma**): `Ru(sg, sŶ, s³r) = s³ RuQ`. -/
theorem Ru_scale (sinv g Y r s : ℝ) :
    Ru sinv (s * g) (s * Y) (s ^ 3 * r) = s ^ 3 * RuQ sinv g Y r s := by
  unfold Ru RuQ
  ring

/-- Woodford (2003), (E.3): the cofactor of `s³` in `Rv` under the weighted scaling. -/
noncomputable def RvQ (Φ omega q y r s : ℝ) : ℝ :=
  (1 - s * Φ) * (r + omega / 2 * ((y ^ 2 / 2 + s * r) * (2 * y + s * (y ^ 2 / 2 + s * r))) -
      omega * q * (y ^ 2 / 2 + s * r)) -
    Φ * ((1 + omega) / 2 * y ^ 2 - omega * q * y)

/-- Woodford (2003), (E.3) (**scaling lemma**): `Rv(sΦ, sq, sŷ, s³r) = s³ RvQ`. -/
theorem Rv_scale (Φ omega q y r s : ℝ) :
    Rv (s * Φ) omega (s * q) (s * y) (s ^ 3 * r) = s ^ 3 * RvQ Φ omega q y r s := by
  unfold Rv RvQ
  ring

/-- Woodford (2003), (E.4) (**scaling lemma for the integrated remainder**): if every good's
`ŷ(i) = s y₁(i)` and `r(i) = s³ r₁(i)`, then `E_i Rv = s³ E_i RvQ`. -/
theorem integral_Rv_scale (μ : Measure G) (Φ omega q s : ℝ) (y₁ r₁ : G → ℝ) :
    ∫ i, Rv (s * Φ) omega (s * q) (s * y₁ i) (s ^ 3 * r₁ i) ∂μ =
      s ^ 3 * ∫ i, RvQ Φ omega q (y₁ i) (r₁ i) s ∂μ := by
  simp_rw [Rv_scale]
  exact integral_const_mul _ _

/-! ### Proposition 6.1 assembled (Layer A) -/

/-- Woodford (2003), (E.5), p. 694: the residual of the CES expansion,
`e = Ŷ − E_i ŷ − ½(1 − θ⁻¹) var_i ŷ` (bounded by `CrossSection.logMeanExp_second_order`). -/
noncomputable def eRes (μ : Measure G) (θ Y : ℝ) (yh : G → ℝ) : ℝ :=
  Y - crossMean μ yh - (1 - θ⁻¹) / 2 * crossVar μ yh

/-- A continuous function of a bounded measurable cross-section is integrable. -/
theorem integrable_comp_of_bounded (μ : Measure G) [IsFiniteMeasure μ] {yh : G → ℝ}
    (hyh : Measurable yh) {B : ℝ} (hB : ∀ i, |yh i| ≤ B) {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable (fun i => g (yh i)) μ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -B) (b := B)).exists_bound_of_continuousOn
    hg.continuousOn
  refine integrable_of_abs_le μ (hg.measurable.comp hyh) (K := C) fun i => ?_
  have := hC (yh i) ⟨(abs_le.mp (hB i)).1, (abs_le.mp (hB i)).2⟩
  rwa [Real.norm_eq_abs] at this

/-- Woodford (2003), **Proposition 6.1, eq. (2.10)/(E.1), p. 394 (Layer A, exact)**. Let the
cross-section of log outputs `ŷ(i) = log(y(i)/Ȳ)` be measurable and bounded, let the steady
state satisfy `ṽ_y = (1 − Φ) u_c` ((2.7)–(2.8)), and let `Ŷ` be any value of log aggregate
output, `Ŷⁿ` the true natural rate and `x*` the true efficient gap. Then the second-order Taylor
polynomial of `U_t = ũ(Y_t) − ∫ ṽ(y_t(i)) di` (with `Y_t = Ȳ e^Ŷ`, `y_t(i) = Ȳ e^{ŷ(i)}`) equals
`t.i.p. + Ȳ u_c {−½[(σ⁻¹ + ω)(x − x*)² + (θ⁻¹ + ω) var_i ŷ] + R}`, `x = Ŷ − Ŷⁿ`, where the
t.i.p. is `(ū + u_ξξ̃ + ½ξ̃'u_ξξξ̃) − (v̄ + v_ξξ̃ + ½ξ̃'v_ξξξ̃) + Ȳ u_c tipA(g, q, Φ)` and
`R = R3 + Ru − E_i Rv` has weighted degree at least three (`R3_scale`, `Ru_scale`,
`integral_Rv_scale`). The coefficients `σ⁻¹`, `ω` are those at the steady state `Ȳ` for the
given `Φ` (imprecision 26; see `steadyState_family`, `lossQ_freeze`). -/
theorem prop61_layerA (μ : Measure G) [IsProbabilityMeasure μ] {yh : G → ℝ}
    (hyh : Measurable yh) {B : ℝ} (hB : ∀ i, |yh i| ≤ B)
    {ubar uc ucc Lu Cu Qu vbar vy vyy Lv Cv Qv Ybar Φ θ Y Ynat xstar : ℝ}
    (hY : Ybar ≠ 0) (huc : uc ≠ 0) (hucc : ucc ≠ 0) (hvy : vy = (1 - Φ) * uc)
    (hvy0 : vy ≠ 0) (hvyy : vyy ≠ 0)
    (hden : sigmaInvEl Ybar uc ucc + omegaEl Ybar vy vyy ≠ 0) :
    uTaylor ubar uc ucc Lu Cu Qu (Ybar * Real.exp Y - Ybar) -
        ∫ i, vTaylor vbar vy vyy Lv Cv Qv (Ybar * Real.exp (yh i) - Ybar) ∂μ =
      ((ubar + Lu + Qu / 2) - (vbar + Lv + Qv / 2) +
          Ybar * uc * tipA (sigmaInvEl Ybar uc ucc) (omegaEl Ybar vy vyy) (gShock Ybar ucc Cu)
            (qShock Ybar vyy Cv) Φ) +
        Ybar * uc * (-(1 / 2) * lossQ (sigmaInvEl Ybar uc ucc) (omegaEl Ybar vy vyy) θ
            ((Y - Ynat) - xstar) (crossVar μ yh) +
          (R3 (sigmaInvEl Ybar uc ucc) (omegaEl Ybar vy vyy) θ (gShock Ybar ucc Cu)
              (qShock Ybar vyy Cv) Φ Y (crossVar μ yh) (eRes μ θ Y yh)
              (Ynat - natLin (sigmaInvEl Ybar uc ucc) (omegaEl Ybar vy vyy)
                (gShock Ybar ucc Cu) (qShock Ybar vyy Cv))
              (xstar - xStarLin (sigmaInvEl Ybar uc ucc) (omegaEl Ybar vy vyy) Φ) +
            Ru (sigmaInvEl Ybar uc ucc) (gShock Ybar ucc Cu) Y (expRem Y) -
            ∫ i, Rv Φ (omegaEl Ybar vy vyy) (qShock Ybar vyy Cv) (yh i) (expRem (yh i)) ∂μ)) := by
  set a := sigmaInvEl Ybar uc ucc
  set w := omegaEl Ybar vy vyy
  set g := gShock Ybar ucc Cu
  set q := qShock Ybar vyy Cv
  have h1 : Integrable yh μ := integrable_comp_of_bounded μ hyh hB (g := fun y => y)
    continuous_id
  have h2 : Integrable (fun i => yh i ^ 2) μ := integrable_comp_of_bounded μ hyh hB
    (g := fun y => y ^ 2) (continuous_pow 2)
  have hTv : Integrable (fun i => Tv Φ w q (yh i)) μ := integrable_comp_of_bounded μ hyh hB
    (g := fun y => Tv Φ w q y) (by unfold Tv; fun_prop)
  have hRv : Integrable (fun i => Rv Φ w q (yh i) (expRem (yh i))) μ :=
    integrable_comp_of_bounded μ hyh hB (g := fun y => Rv Φ w q y (expRem y))
      (by unfold Rv expRem; fun_prop)
  rw [levelDev_eq, uTaylor_eq hY huc hucc]
  have hpt : ∀ i, vTaylor vbar vy vyy Lv Cv Qv (Ybar * Real.exp (yh i) - Ybar) =
      (vbar + Lv + Qv / 2) + Ybar * uc * (Tv Φ w q (yh i) + Rv Φ w q (yh i) (expRem (yh i))) :=
    fun i => by rw [levelDev_eq, vTaylor_eq hY hvy hvy0 hvyy]
  simp_rw [hpt]
  have e1 := integral_add (μ := μ) (f := fun _ => vbar + Lv + Qv / 2)
    (g := fun i => Ybar * uc * (Tv Φ w q (yh i) + Rv Φ w q (yh i) (expRem (yh i))))
    (integrable_const _)
    ((show Integrable (fun i => Tv Φ w q (yh i) + Rv Φ w q (yh i) (expRem (yh i))) μ from
      hTv.add hRv).const_mul (Ybar * uc))
  have e2 := integral_add (μ := μ) (f := fun i => Tv Φ w q (yh i))
    (g := fun i => Rv Φ w q (yh i) (expRem (yh i))) hTv hRv
  rw [e1, integral_const, integral_const_mul, e2, integral_Tv μ h1 h2]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  have hA := thmA1 (sinv := a) (omega := w) (θ := θ) (g := g) (q := q) (Φ := Φ) (Y := Y)
    (V := crossVar μ yh) (e := eRes μ θ Y yh) (n := Ynat - natLin a w g q)
    (k := xstar - xStarLin a w Φ) hden
  have hm : crossMean μ yh = Y - (1 - θ⁻¹) / 2 * crossVar μ yh - eRes μ θ Y yh := by
    unfold eRes
    ring
  have hx : (Y - (natLin a w g q + (Ynat - natLin a w g q))) -
      (xStarLin a w Φ + (xstar - xStarLin a w Φ)) = (Y - Ynat) - xstar := by ring
  rw [hx, ← hm] at hA
  have hcomm : crossVar μ yh + crossMean μ yh ^ 2 = crossVar μ yh + crossMean μ yh ^ 2 := rfl
  clear hcomm
  linear_combination Ybar * uc * hA

/-- Woodford (2003), Prop. 6.1 with (E.5) (**the CES aggregate and the bound on the (E.5)
error**): with `Ŷ = log(Y/Ȳ) = logMeanExp μ (1 − θ⁻¹) ŷ` (the Dixit–Stiglitz aggregate (2.6),
`log_ces_eq`), the identity of `prop61_layerA` holds, and if the cross-section lies within `B'`
of its mean with `|1 − θ⁻¹| B' ≤ 1/2`, the (E.5) error satisfies
`|e| ≤ (1 − θ⁻¹)² B' var_i ŷ` (weighted degree three). -/
theorem prop61_ces (μ : Measure G) [IsProbabilityMeasure μ] {yh : G → ℝ} (hyh : Measurable yh)
    {θ B' : ℝ} (hθ : θ ≠ 1) (hB' : ∀ i, |yh i - crossMean μ yh| ≤ B')
    (hrB : |1 - θ⁻¹| * B' ≤ 1 / 2) :
    |eRes μ θ (logMeanExp μ (1 - θ⁻¹) yh) yh| ≤ (1 - θ⁻¹) ^ 2 * B' * crossVar μ yh := by
  have hr : (1 : ℝ) - θ⁻¹ ≠ 0 := by
    intro h
    apply hθ
    have : θ⁻¹ = 1 := by linarith
    simpa using this
  have h := logMeanExp_second_order μ hyh hB' hr hrB
  unfold eRes
  convert h using 2

/-! ### (2.11): orders of magnitude -/

/-- Woodford (2003), (2.10)–(2.11) (**`R3 = O(‖Φ, ŷ, ξ̃‖³)` along any family**): if `Ŷ, g, q, Φ`
are `O(s)`, `var_i ŷ`, `n`, `k` are `O(s²)` and the (E.5) error `e` is `O(s³)`, then
`R3 = O(s³)`. With `s` a bound on `(Φ, ŷ, ξ̃)` this is (2.10); with `s` a bound on
`(Φ, φ, ξ̃)` and `ŷ = O(φ, ξ̃)` (`eq211_orders`) it is (2.11). -/
theorem R3_isBigO {sinv omega θ : ℝ} {g q Φ Y V e n k : ℝ → ℝ}
    (hg : g =O[𝓝 0] fun s => s ^ 1) (hq : q =O[𝓝 0] fun s => s ^ 1)
    (hΦ : Φ =O[𝓝 0] fun s => s ^ 1) (hY : Y =O[𝓝 0] fun s => s ^ 1)
    (hV : V =O[𝓝 0] fun s => s ^ 2) (he : e =O[𝓝 0] fun s => s ^ 3)
    (hn : n =O[𝓝 0] fun s => s ^ 2) (hk : k =O[𝓝 0] fun s => s ^ 2) :
    (fun s => R3 sinv omega θ (g s) (q s) (Φ s) (Y s) (V s) (e s) (n s) (k s))
      =O[𝓝 0] fun s => s ^ 3 := by
  set c := (1 - θ⁻¹) / 2
  have hW : (fun s => c * V s + e s) =O[𝓝 0] fun s => s ^ 2 :=
    (hV.const_mul_left c).add (bigO_weaken (by norm_num) he)
  have hA : (fun s => Y s - natLin sinv omega (g s) (q s) - xStarLin sinv omega (Φ s))
      =O[𝓝 0] fun s => s ^ 1 := by
    have h1 : (fun s => natLin sinv omega (g s) (q s)) =O[𝓝 0] fun s => s ^ 1 := by
      unfold natLin
      have := ((hg.const_mul_left sinv).add (hq.const_mul_left omega)).const_mul_left
        (sinv + omega)⁻¹
      refine this.congr_left fun s => ?_
      ring
    have h2 : (fun s => xStarLin sinv omega (Φ s)) =O[𝓝 0] fun s => s ^ 1 := by
      unfold xStarLin
      refine (hΦ.const_mul_left (sinv + omega)⁻¹).congr_left fun s => ?_
      ring
    exact (hY.sub h1).sub h2
  have hB : (fun s => n s + k s) =O[𝓝 0] fun s => s ^ 2 := hn.add hk
  have t1 := bigO_mul hΦ hW (by norm_num : 1 + 2 = 3)
  have t2 := bigO_mul hY hW (by norm_num : 1 + 2 = 3)
  have t3 := bigO_mul hW hW (by norm_num : 2 + 2 = 4)
  have t4 := bigO_mul hq hW (by norm_num : 1 + 2 = 3)
  have t5 := bigO_mul hA hB (by norm_num : 1 + 2 = 3)
  have t6 := bigO_mul hB hB (by norm_num : 2 + 2 = 4)
  have h := ((((((t1.const_mul_left (-1)).add he).add
    ((t2.const_mul_left ((1 + omega) / 2 * 2)).add
      ((bigO_weaken (by norm_num : 3 ≤ 4) t3).const_mul_left (-((1 + omega) / 2))))).add
    (t4.const_mul_left (-omega))).add (t5.const_mul_left (-(sinv + omega)))).add
    ((bigO_weaken (by norm_num : 3 ≤ 4) t6).const_mul_left ((sinv + omega) / 2)))
  refine h.congr_left fun s => ?_
  unfold R3
  ring

/-- Woodford (2003), p. 395 (**(2.11): the endogenous orders from a uniform bound on
`ŷ`**): if every good's `ŷ_s(i)` is bounded by `C|s|` (the book's `ŷ = O(φ, ξ̃)`, `s` bounding
`φ, ξ̃`), then `Ŷ = logMeanExp μ r ŷ_s = O(s)`, `var_i ŷ_s = O(s²)` and the (E.5) error is
`O(s³)`. -/
theorem eq211_orders (μ : Measure G) [IsProbabilityMeasure μ] {yh : ℝ → G → ℝ}
    (hyh : ∀ s, Measurable (yh s)) {C θ : ℝ} (hC : ∀ s i, |yh s i| ≤ C * |s|)
    (hθ : θ ≠ 1) :
    ((fun s => logMeanExp μ (1 - θ⁻¹) (yh s)) =O[𝓝 0] fun s => s ^ 1) ∧
      ((fun s => crossVar μ (yh s)) =O[𝓝 0] fun s => s ^ 2) ∧
      ((fun s => eRes μ θ (logMeanExp μ (1 - θ⁻¹) (yh s)) (yh s)) =O[𝓝 0] fun s => s ^ 3) := by
  have hr : (1 : ℝ) - θ⁻¹ ≠ 0 := by
    intro h
    apply hθ
    have : θ⁻¹ = 1 := by linarith
    simpa using this
  have hmean : ∀ s, |crossMean μ (yh s)| ≤ C * |s| := fun s => by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := yh s) (C := C * |s|)
      (Eventually.of_forall fun i => by rw [Real.norm_eq_abs]; exact hC s i)
    simpa [crossMean] using this
  have hcen : ∀ s i, |yh s i - crossMean μ (yh s)| ≤ 2 * C * |s| := fun s i => by
    have := abs_sub (yh s i) (crossMean μ (yh s))
    linarith [hC s i, hmean s]
  have hVb : ∀ s, crossVar μ (yh s) ≤ (2 * C * |s|) ^ 2 := fun s =>
    (centred_facts μ (hyh s) (hcen s) 0).2.2.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · refine IsBigO.of_bound C (Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, pow_one]
    exact abs_logMeanExp_le μ (hyh s) (hC s) hr
  · refine IsBigO.of_bound (4 * C ^ 2) (Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (crossVar_nonneg _ _), abs_pow,
      sq_abs]
    have := hVb s
    nlinarith [sq_abs s]
  · -- near `0`, `|1 − θ⁻¹| · 2C|s| ≤ 1/2`
    have hev : ∀ᶠ s in 𝓝 (0 : ℝ), |1 - θ⁻¹| * (2 * C * |s|) ≤ 1 / 2 := by
      have hc : Tendsto (fun s : ℝ => |1 - θ⁻¹| * (2 * C * |s|)) (𝓝 0) (𝓝 0) := by
        have : Continuous fun s : ℝ => |1 - θ⁻¹| * (2 * C * |s|) := by fun_prop
        simpa using this.tendsto 0
      exact hc.eventually (ge_mem_nhds (by norm_num))
    refine IsBigO.of_bound ((1 - θ⁻¹) ^ 2 * (2 * |C|) * (2 * C) ^ 2) ?_
    filter_upwards [hev] with s hs
    have h := prop61_ces μ (hyh s) hθ (hcen s) hs
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
    refine h.trans ?_
    have hV0 := crossVar_nonneg μ (yh s)
    have h2C : 2 * C * |s| ≤ 2 * |C| * |s| := by
      have := le_abs_self C
      nlinarith [abs_nonneg s]
    have hr2 : 0 ≤ (1 - θ⁻¹) ^ 2 := sq_nonneg _
    have e1 : (1 - θ⁻¹) ^ 2 * (2 * |C|) * (2 * C) ^ 2 * |s| ^ 3 =
        (1 - θ⁻¹) ^ 2 * (2 * |C| * |s|) * (2 * C * |s|) ^ 2 := by
      ring
    rw [e1]
    have hVb' := hVb s
    have hp : 0 ≤ (1 - θ⁻¹) ^ 2 * (2 * |C| * |s|) := by positivity
    calc (1 - θ⁻¹) ^ 2 * (2 * C * |s|) * crossVar μ (yh s)
        ≤ (1 - θ⁻¹) ^ 2 * (2 * |C| * |s|) * crossVar μ (yh s) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2C hr2) hV0
      _ ≤ (1 - θ⁻¹) ^ 2 * (2 * |C| * |s|) * (2 * C * |s|) ^ 2 :=
          mul_le_mul_of_nonneg_left hVb' hp

/-- Woodford (2003), eq. (2.11), p. 395 (**the remainder in terms of `(Φ, φ, ξ̃)`**): if `Φ`,
`g`, `q` are `O(s)`, the natural-rate and efficient-gap errors `n`, `k` are `O(s²)`, and the
cross-section `ŷ_s(i)` is uniformly `O(s)`, then the remainder `R3` of Proposition 6.1
evaluated at `Ŷ = logMeanExp`, `V = var_i ŷ`, `e = eRes` is `O(s³)`. -/
theorem eq211_remainder (μ : Measure G) [IsProbabilityMeasure μ] {yh : ℝ → G → ℝ}
    (hyh : ∀ s, Measurable (yh s)) {C θ sinv omega : ℝ} (hC : ∀ s i, |yh s i| ≤ C * |s|)
    (hθ : θ ≠ 1) {g q Φ n k : ℝ → ℝ}
    (hg : g =O[𝓝 0] fun s => s ^ 1) (hq : q =O[𝓝 0] fun s => s ^ 1)
    (hΦ : Φ =O[𝓝 0] fun s => s ^ 1) (hn : n =O[𝓝 0] fun s => s ^ 2)
    (hk : k =O[𝓝 0] fun s => s ^ 2) :
    (fun s => R3 sinv omega θ (g s) (q s) (Φ s) (logMeanExp μ (1 - θ⁻¹) (yh s))
        (crossVar μ (yh s)) (eRes μ θ (logMeanExp μ (1 - θ⁻¹) (yh s)) (yh s)) (n s) (k s))
      =O[𝓝 0] fun s => s ^ 3 := by
  obtain ⟨hY, hV, he⟩ := eq211_orders μ hyh hC hθ
  exact R3_isBigO hg hq hΦ hY hV he hn hk

/-! ### (2.13): the dispersion of prices -/

/-- Woodford (2003), eq. (2.13), p. 396: `(θ⁻¹ + ω) θ² = θ(1 + ωθ)`, so with
`var_i ŷ = θ² var_i log p` ((2.12)) the loss becomes
`(σ⁻¹ + ω)(x − x*)² + θ(1 + ωθ) var_i log p`. -/
theorem lossQ_disp {sinv omega θ X Δ : ℝ} (hθ : θ ≠ 0) :
    lossQ sinv omega θ X (θ ^ 2 * Δ) = (sinv + omega) * X ^ 2 + θ * (1 + omega * θ) * Δ := by
  unfold lossQ
  field_simp

/-- Woodford (2003), eq. (2.13), p. 396 (**exact**): combining Theorem A1 with
`var_i ŷ = θ² var_i log p` (`CrossSection.crossVar_demand`), `Tu − E_i Tv` equals
`−½[(σ⁻¹ + ω)(x − x*)² + θ(1 + ωθ) Δ] + tipA + R3` with `Δ = var_i log p`. -/
theorem prop61_disp {sinv omega θ g q Φ Y Δ e n k : ℝ} (hden : sinv + omega ≠ 0)
    (hθ : θ ≠ 0) :
    Tu sinv g Y - ((1 - Φ) * (Y - (1 - θ⁻¹) / 2 * (θ ^ 2 * Δ) - e) +
        (1 + omega) / 2 * (θ ^ 2 * Δ + (Y - (1 - θ⁻¹) / 2 * (θ ^ 2 * Δ) - e) ^ 2) -
        omega * q * (Y - (1 - θ⁻¹) / 2 * (θ ^ 2 * Δ) - e)) =
      -(1 / 2) * ((sinv + omega) *
          ((Y - (natLin sinv omega g q + n)) - (xStarLin sinv omega Φ + k)) ^ 2 +
          θ * (1 + omega * θ) * Δ) +
        tipA sinv omega g q Φ + R3 sinv omega θ g q Φ Y (θ ^ 2 * Δ) e n k := by
  rw [thmA1 hden, lossQ_disp hθ]

/-! ### The efficient gap with `Φ`-dependent coefficients (imprecision 26) -/

/-- Woodford (2003), (2.9)/(2.17), p. 394 (**the `x*` remainder with moving coefficients,
abstract form**): if `F(Φ) = log(Ȳ(Φ)/Y*)` satisfies `F + Φ/c₀ = O(Φ²)` and the coefficient sum
`c(Φ) = σ⁻¹(Φ) + ω(Φ)` (evaluated at `Ȳ(Φ)`) satisfies `c − c₀ = O(Φ)` with `c₀ ≠ 0`, then the
true efficient gap `x*(Φ) = −F(Φ)` differs from `Φ/c(Φ)` by `O(Φ²)`. -/
theorem xstar_rem {F c : ℝ → ℝ} {c0 : ℝ} (hc0 : c0 ≠ 0)
    (hF : (fun Φ => F Φ + Φ / c0) =O[𝓝 0] fun Φ => Φ ^ 2)
    (hc : (fun Φ => c Φ - c0) =O[𝓝 0] fun Φ => Φ) :
    (fun Φ => -F Φ - Φ / c Φ) =O[𝓝 0] fun Φ => Φ ^ 2 := by
  have hct : Tendsto c (𝓝 0) (𝓝 c0) :=
    tendsto_sub_nhds_zero_iff.mp (hc.trans_tendsto tendsto_id)
  have hinv : (fun Φ => (c0 * c Φ)⁻¹) =O[𝓝 0] fun _ => (1 : ℝ) :=
    ((tendsto_const_nhds.mul hct).inv₀ (mul_ne_zero hc0 hc0)).isBigO_one ℝ
  have hprod : (fun Φ => Φ * (c Φ - c0) * (c0 * c Φ)⁻¹) =O[𝓝 0] fun Φ => Φ ^ 2 := by
    have := ((isBigO_refl (fun Φ : ℝ => Φ) (𝓝 0)).mul hc).mul hinv
    refine this.congr_right fun Φ => ?_
    ring
  have hne := hct.eventually_ne hc0
  refine (hF.neg_left.add hprod).congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [hne] with Φ hΦ
  field_simp
  ring

/-- Woodford (2003), (2.9) and (2.17), p. 394 (**the efficient gap with the elasticities at the
current steady state**): under the hypotheses of `eq29_O2`, if `σ⁻¹` and `ω` as functions `A`,
`W` of log output are such that `A + W − (ω + σ⁻¹)(Y*) = O(log Y − log Y*)` (e.g. Lipschitz),
then along the steady-state family `x*(Φ) = log(Y*/Ȳ(Φ))` satisfies
`x*(Φ) − Φ/(σ⁻¹(Φ) + ω(Φ)) = O(Φ²)`, with `σ⁻¹(Φ) = A(log Ȳ(Φ))`, `ω(Φ) = W(log Ȳ(Φ))`. -/
theorem eq29_xstar {vy uc A W : ℝ → ℝ} {Ystar : ℝ} (hY : 0 < Ystar) (hv : 0 < vy Ystar)
    (hu : 0 < uc Ystar) (hv2 : ContDiffAt ℝ 2 vy Ystar) (hu2 : ContDiffAt ℝ 2 uc Ystar)
    (heff : realMC vy uc Ystar Ystar = 1)
    (hden : omegaEl Ystar (vy Ystar) (deriv vy Ystar) +
      sigmaInvEl Ystar (uc Ystar) (deriv uc Ystar) ≠ 0)
    (hAW : (fun w => A w + W w - (omegaEl Ystar (vy Ystar) (deriv vy Ystar) +
      sigmaInvEl Ystar (uc Ystar) (deriv uc Ystar))) =O[𝓝 (Real.log Ystar)]
        fun w => w - Real.log Ystar) :
    ∃ z : ℝ → ℝ, z 0 = Real.log Ystar ∧
      (∀ᶠ Φ in 𝓝 0, IsSteadyState vy uc Φ (Real.exp (z Φ))) ∧
      (fun Φ => Real.log (Ystar / Real.exp (z Φ)) - xStarLin (A (z Φ)) (W (z Φ)) Φ)
        =O[𝓝 0] fun Φ => Φ ^ 2 := by
  set f' := omegaEl Ystar (vy Ystar) (deriv vy Ystar) +
    sigmaInvEl Ystar (uc Ystar) (deriv uc Ystar)
  obtain ⟨z, hz0, hss, hO⟩ := eq29_O2 hY hv hu hv2 hu2 heff hden
  have hO1 : (fun Φ => Real.log (Real.exp (z Φ) / Ystar) + Φ / f') =O[𝓝 0] fun Φ => Φ := by
    simpa using bigO_weaken (by norm_num : 1 ≤ 2) hO
  have hz1 : (fun Φ => z Φ - Real.log Ystar) =O[𝓝 0] fun Φ => Φ := by
    refine (hO1.sub ((isBigO_refl (fun Φ : ℝ => Φ) (𝓝 0)).const_mul_left f'⁻¹)).congr_left
      fun Φ => ?_
    rw [Real.log_div (Real.exp_pos _).ne' hY.ne', Real.log_exp]
    ring
  have hzt : Tendsto z (𝓝 0) (𝓝 (Real.log Ystar)) :=
    tendsto_sub_nhds_zero_iff.mp (hz1.trans_tendsto tendsto_id)
  have hc : (fun Φ => A (z Φ) + W (z Φ) - f') =O[𝓝 0] fun Φ => Φ :=
    (hAW.comp_tendsto hzt).trans hz1
  refine ⟨z, hz0, hss, ?_⟩
  have h := xstar_rem (F := fun Φ => Real.log (Real.exp (z Φ) / Ystar))
    (c := fun Φ => A (z Φ) + W (z Φ)) hden hO hc
  refine h.congr_left fun Φ => ?_
  unfold xStarLin
  rw [Real.log_div hY.ne' (Real.exp_pos _).ne', Real.log_div (Real.exp_pos _).ne' hY.ne']
  ring

/-- Woodford (2003), **Proposition 6.1 with `Φ`-dependent coefficients (Layer A)**: for
coefficient families `σ⁻¹(Φ)`, `ω(Φ)` (the elasticities at `Ȳ(Φ)`), the Theorem A1 identity
holds at every `Φ` with the true efficient gap `x*(Φ)` and the error
`k(Φ) = x*(Φ) − Φ/(σ⁻¹(Φ) + ω(Φ))`; and if `x* − Φ/c₀ = O(Φ²)` ((2.9), `eq29_O2`) and
`σ⁻¹(Φ) + ω(Φ) − c₀ = O(Φ)`, then `k = O(Φ²)`: weight two, as `R3_scale` requires. -/
theorem prop61_phiDep {a w g q Y V e n xstar : ℝ → ℝ} {θ c0 : ℝ}
    (hden : ∀ Φ, a Φ + w Φ ≠ 0) (hc0 : c0 ≠ 0)
    (hx : (fun Φ => xstar Φ - Φ / c0) =O[𝓝 0] fun Φ => Φ ^ 2)
    (hc : (fun Φ => a Φ + w Φ - c0) =O[𝓝 0] fun Φ => Φ) :
    (∀ Φ, Tu (a Φ) (g Φ) (Y Φ) - ((1 - Φ) * (Y Φ - (1 - θ⁻¹) / 2 * V Φ - e Φ) +
        (1 + w Φ) / 2 * (V Φ + (Y Φ - (1 - θ⁻¹) / 2 * V Φ - e Φ) ^ 2) -
        w Φ * q Φ * (Y Φ - (1 - θ⁻¹) / 2 * V Φ - e Φ)) =
      -(1 / 2) * lossQ (a Φ) (w Φ) θ
          ((Y Φ - (natLin (a Φ) (w Φ) (g Φ) (q Φ) + n Φ)) - xstar Φ) (V Φ) +
        tipA (a Φ) (w Φ) (g Φ) (q Φ) Φ +
        R3 (a Φ) (w Φ) θ (g Φ) (q Φ) Φ (Y Φ) (V Φ) (e Φ) (n Φ)
          (xstar Φ - xStarLin (a Φ) (w Φ) Φ)) ∧
      (fun Φ => xstar Φ - xStarLin (a Φ) (w Φ) Φ) =O[𝓝 0] fun Φ => Φ ^ 2 := by
  refine ⟨fun Φ => ?_, ?_⟩
  · have h := thmA1 (θ := θ) (g := g Φ) (q := q Φ) (Φ := Φ) (Y := Y Φ) (V := V Φ) (e := e Φ)
      (n := n Φ) (k := xstar Φ - xStarLin (a Φ) (w Φ) Φ) (hden Φ)
    rwa [show xStarLin (a Φ) (w Φ) Φ + (xstar Φ - xStarLin (a Φ) (w Φ) Φ) = xstar Φ by ring]
      at h
  · have hF : (fun Φ => -xstar Φ + Φ / c0) =O[𝓝 0] fun Φ => Φ ^ 2 :=
      hx.neg_left.congr_left fun Φ => by ring
    have h := xstar_rem (F := fun Φ => -xstar Φ) (c := fun Φ => a Φ + w Φ) hc0 hF hc
    refine h.congr_left fun Φ => ?_
    unfold xStarLin
    ring

end Woodford.StabilizationWelfare.Prop61
