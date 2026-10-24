/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.Expectations
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Log-linear equations as exact derivatives

Woodford (2003), *Interest and Prices*, Chapter 2, §1.2, eqs. (1.21), (1.32)–(1.34),
pp. 71, 79–81, and §2.2, eqs. (2.4)–(2.5), pp. 90–91; Appendix A, §A.3, pp. 630–635.

Each log-linear equation of §§1–2 of Chapter 2 is shown to be the exact first derivative, at the
zero-inflation steady state, of the corresponding nonlinear equilibrium condition.

## Main results

* `fisher_log_form`: the exact Fisher equation (1.21) is equivalent to
  `î_t = −log E_t[exp(λ_{t+1} − λ_t − π_{t+1})]`, with `î_t = log((1 + i_t)/(1 + ī))`,
  `λ = log(u_c/ū_c)` and `π_{t+1} = log(P_{t+1}/P_t)`.
* (1.32), general state space: `hasDerivAt_log_E_exp` and `fisher_deriv` — along every bounded
  direction the map `ε ↦ −log E_t[exp(ε X)]` has derivative `−E_t X` at `0`, so the derivative of
  the exact Fisher map is `r̂_t + E_t π_{t+1}` with `r̂_t = λ_t − E_t λ_{t+1}`.
* (1.33): `hasFDerivAt_lambda`, the derivative of `log u_c(Ȳ e^Ŷ; ξ)` at the steady state is
  `−σ⁻¹(Ŷ − g)`, `σ = −u_c/(u_cc Ȳ)`, `g = −u_cξ ξ/(Ȳ u_cc)`; with government purchases
  (`hasFDerivAt_lambda_G`) it is `−σ⁻¹(Ŷ − g)` with `σ = s_C σ_C` and `g = Ĝ + s_C c̄`.
* (1.32)+(1.33) together, finite state space: `fisher_composite_deriv` — the exact Fisher map
  (1.21), with every exogenous and endogenous deviation scaled by `ε`, has derivative
  `r̂_t + E_t π_{t+1}`, `r̂_t = σ⁻¹ E_t[(Ŷ_{t+1} − g_{t+1}) − (Ŷ_t − g_t)]`, at `ε = 0`
  (via `hasDerivAt_E`: on a finite state space `E_t` commutes with differentiation).
* (1.34): `hasFDerivAt_wicksell`, the derivative of `log((1 + φ(e^{P̂}; ν))/(1 + ī))` is
  `φ_p P̂ + ν` with `φ_p = β ∂φ/∂(P/P*)`, under footnote 15's normalisation `∂φ/∂ν = β⁻¹`.
* (2.5): `hasFDerivAt_taylor`, the derivative of the Taylor rule (2.4) in logs is
  `φ_π(π − π*) + ν = ī_t + φ_π π` with `ī_t = ν − φ_π π*`.

Coverage: equations (3.6) and (3.11) have their nonlinear form in §3 (monetary frictions) and are
left to the money chain.

Precision (recorded): the coefficient `φ_p` (resp. `φ_π`) of the log-linear rule is the elasticity
of `1 + φ` (equivalently `φ'(1)/(1 + ī)`), not of `φ` itself as worded on p. 81 (resp. p. 91):
`î` is the log deviation of `1 + i`, not of `i`.
-/

namespace Woodford.PriceLevelDetermination.LogLinear

open Filter Topology Asymptotics

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The exact Fisher equation (1.21) in logs -/

/-- Woodford (2003), eq. (1.21), p. 71: the exact Fisher equation at date `t`,
`1 + i_t = β⁻¹ {E_t[u_c(Y_{t+1}; ξ_{t+1}) P_t / (u_c(Y_t; ξ_t) P_{t+1})]}⁻¹`, with `uc t` the
marginal utility of income at date `t`. -/
def FisherExact (β : ℝ) (i uc P : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, 1 + i t ω = β⁻¹ * (𝔼.E t (fun ω' => uc (t + 1) ω' * P t ω' / (uc t ω' * P (t + 1) ω')) ω)⁻¹

/-- Woodford (2003), eqs. (1.21) and (1.32), pp. 71, 79–80: with positive marginal utilities and
prices, and `1 + ī = β⁻¹` (zero steady-state inflation), (1.21) holds iff
`î_t = −log E_t[exp(λ_{t+1} − λ_t − π_{t+1})]`, where `î_t = log((1 + i_t)/(1 + ī))`,
`λ_s = log(u_c,s/ū_c)` and `π_{t+1} = log(P_{t+1}/P_t)`. -/
theorem fisher_log_form {β ucbar : ℝ} (hβ : 0 < β) (hu : 0 < ucbar) {i uc P : ℕ → Ω → ℝ}
    (t : ℕ) (huc : ∀ s ω, 0 < uc s ω) (hP : ∀ s ω, 0 < P s ω) (hi : ∀ ω, 0 < 1 + i t ω)
    (hE : ∀ ω, 0 < 𝔼.E t (fun ω' => uc (t + 1) ω' * P t ω' / (uc t ω' * P (t + 1) ω')) ω) :
    FisherExact 𝔼 β i uc P t ↔ ∀ ω, Real.log ((1 + i t ω) / β⁻¹) =
      -Real.log (𝔼.E t (fun ω' => Real.exp (Real.log (uc (t + 1) ω' / ucbar) -
        Real.log (uc t ω' / ucbar) - Real.log (P (t + 1) ω' / P t ω'))) ω) := by
  have hX : (fun ω' => Real.exp (Real.log (uc (t + 1) ω' / ucbar) -
      Real.log (uc t ω' / ucbar) - Real.log (P (t + 1) ω' / P t ω'))) =
      fun ω' => uc (t + 1) ω' * P t ω' / (uc t ω' * P (t + 1) ω') := by
    funext ω'
    have h1 := huc (t + 1) ω'
    have h2 := huc t ω'
    have h3 := hP t ω'
    have h4 := hP (t + 1) ω'
    rw [Real.exp_sub, Real.exp_sub, Real.exp_log (by positivity), Real.exp_log (by positivity),
      Real.exp_log (by positivity)]
    field_simp
  rw [hX]
  refine forall_congr' fun ω => ?_
  have hE' := hE ω
  have hi' := hi ω
  rw [← Real.log_inv, div_inv_eq_mul]
  constructor
  · intro h
    rw [h]
    congr 1
    field_simp
  · intro h
    have h' := Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity))
      (Set.mem_Ioi.mpr (inv_pos.mpr hE')) h
    rw [← h']
    field_simp

/-! ### (1.32): the derivative of the stochastic Fisher map -/

/-- Woodford (2003), §A.3, p. 634 (derivative of an expectation, general state space): for a
bounded random variable `X`, `ε ↦ E_t[exp(ε X)]` has derivative `E_t X` at `0`. The proof
bounds the remainder `exp(εX) − 1 − εX` by `ε² K²` uniformly and uses that `E_t` is a sup-norm
contraction. -/
theorem hasDerivAt_E_exp {K : ℝ} {X : Ω → ℝ} (hX : ∀ ω, |X ω| ≤ K) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => 𝔼.E t (fun ω' => Real.exp (ε * X ω')) ω) (𝔼.E t X ω) 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hK : 0 ≤ |K| := abs_nonneg K
  have hbig : (fun h : ℝ => 𝔼.E t (fun ω' => Real.exp ((0 + h) * X ω')) ω -
      𝔼.E t (fun ω' => Real.exp (0 * X ω')) ω - h • 𝔼.E t X ω) =O[𝓝 0] fun h => h ^ 2 := by
    refine IsBigO.of_bound (|K| ^ 2) ?_
    have hball : Metric.ball (0 : ℝ) (1 / (|K| + 1)) ∈ 𝓝 (0 : ℝ) :=
      Metric.ball_mem_nhds 0 (by positivity)
    filter_upwards [hball] with h hh
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
    have hrem : ∀ ω', |Real.exp (h * X ω') - 1 - h * X ω'| ≤ |K| ^ 2 * h ^ 2 := by
      intro ω'
      have hx : |h * X ω'| ≤ 1 := by
        rw [abs_mul]
        have h1 : |X ω'| ≤ |K| := (hX ω').trans (le_abs_self K)
        have h2 : |h| * (|K| + 1) ≤ 1 := by
          rw [lt_div_iff₀ (by positivity)] at hh
          exact hh.le
        nlinarith [abs_nonneg h, abs_nonneg (X ω')]
      refine (Real.abs_exp_sub_one_sub_id_le hx).trans ?_
      rw [mul_pow, mul_comm (|K| ^ 2)]
      have : X ω' ^ 2 ≤ |K| ^ 2 := by
        rw [← sq_abs (X ω')]
        exact pow_le_pow_left₀ (abs_nonneg _) ((hX ω').trans (le_abs_self K)) 2
      exact mul_le_mul_of_nonneg_left this (sq_nonneg h)
    have heq : 𝔼.E t (fun ω' => Real.exp ((0 + h) * X ω')) ω -
        𝔼.E t (fun ω' => Real.exp (0 * X ω')) ω - h • 𝔼.E t X ω =
        𝔼.E t (fun ω' => Real.exp (h * X ω') - 1 - h * X ω') ω := by
      have hfun : (fun ω' => Real.exp (h * X ω') - 1 - h * X ω') =
          (fun ω' => Real.exp (h * X ω')) - (fun _ => (1 : ℝ)) - h • X := by
        funext ω'
        simp
      rw [hfun, map_sub, map_sub, map_smul, 𝔼.const]
      simp [𝔼.const]
    rw [heq, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h)]
    exact 𝔼.abs_E_le hrem t ω
  exact hbig.trans_isLittleO (isLittleO_pow_id (by norm_num))

/-- Woodford (2003), eq. (1.32) and §A.3, pp. 79, 634: for a bounded `X`,
`ε ↦ −log E_t[exp(ε X)]` has derivative `−E_t X` at `0`. -/
theorem hasDerivAt_log_E_exp {K : ℝ} {X : Ω → ℝ} (hX : ∀ ω, |X ω| ≤ K) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => -Real.log (𝔼.E t (fun ω' => Real.exp (ε * X ω')) ω))
      (-𝔼.E t X ω) 0 := by
  have h1 : 𝔼.E t (fun ω' => Real.exp (0 * X ω')) ω = 1 := by
    simp only [zero_mul, Real.exp_zero]
    rw [𝔼.const]
  have h := (hasDerivAt_E_exp 𝔼 hX t ω).log (by rw [h1]; exact one_ne_zero)
  rw [h1, div_one] at h
  exact h.neg

/-- Woodford (2003), eq. (1.32), p. 79 (general state space): along a bounded direction
`(λ, π)` of log deviations, the exact Fisher map `ε ↦ −log E_t[exp(ε(λ_{t+1} − λ_t − π_{t+1}))]`
(see `fisher_log_form`) has derivative `r̂_t + E_t π_{t+1}` at the steady state, where
`r̂_t = λ_t − E_t λ_{t+1}` (λ adapted): this is (1.32), `î_t = r̂_t + E_t π_{t+1}`. -/
theorem fisher_deriv {K : ℝ} {lam π : ℕ → Ω → ℝ} (hla : 𝔼.Adapted lam) (t : ℕ)
    (hb : ∀ ω, |lam (t + 1) ω - lam t ω - π (t + 1) ω| ≤ K) (ω : Ω) :
    HasDerivAt (fun ε => -Real.log (𝔼.E t (fun ω' => Real.exp
      (ε * (lam (t + 1) ω' - lam t ω' - π (t + 1) ω'))) ω))
      ((lam t ω - 𝔼.E t (lam (t + 1)) ω) + 𝔼.E t (π (t + 1)) ω) 0 := by
  have h := hasDerivAt_log_E_exp 𝔼 (X := fun ω' => lam (t + 1) ω' - lam t ω' - π (t + 1) ω')
    hb t ω
  convert h using 1
  have hfun : (fun ω' => lam (t + 1) ω' - lam t ω' - π (t + 1) ω') =
      lam (t + 1) - lam t - π (t + 1) := rfl
  rw [hfun, map_sub, map_sub, hla t]
  simp only [Pi.sub_apply]
  ring

/-! ### Finite state spaces: `E_t` commutes with differentiation -/

/-- Woodford (2003), §A.3, p. 634 (finite state space): if each `ε ↦ f ε ω` has derivative
`g ω` at `x`, then `ε ↦ E_t(f ε) ω` has derivative `E_t g ω` (on a finite state space `E_t` is
a continuous linear map). -/
theorem hasDerivAt_E [Finite Ω] {f : ℝ → Ω → ℝ} {g : Ω → ℝ} {x : ℝ}
    (hf : ∀ ω, HasDerivAt (fun ε => f ε ω) (g ω) x) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => 𝔼.E t (f ε) ω) (𝔼.E t g ω) x := by
  have := Fintype.ofFinite Ω
  have hF : HasDerivAt f g x := hasDerivAt_pi.mpr hf
  have hL := (LinearMap.toContinuousLinearMap (𝔼.E t)).hasFDerivAt.comp_hasDerivAt x hF
  have := hasDerivAt_pi.mp hL ω
  simpa using this

/-! ### (1.33): the marginal utility of income -/

/-- Woodford (2003), eq. (1.33), p. 80: the log deviation of marginal utility,
`λ(Ŷ, ξ) = log u_c(Ȳ e^Ŷ; ξ) − log u_c(Ȳ; 0)`. -/
noncomputable def lambda (uc : ℝ × ℝ → ℝ) (Ybar : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.log (uc (Ybar * Real.exp p.1, p.2)) - Real.log (uc (Ybar, 0))

/-- Woodford (2003), eq. (1.33), p. 80: the derivative of `λ(Ŷ, ξ)` at the steady state is
`−σ⁻¹(Ŷ − g)`, with `σ = −u_c/(u_cc Ȳ)` and `g = −u_cξ ξ/(Ȳ u_cc)`. Here `u_cc ≠ 0` (the book
assumes `u_cc < 0`, making `σ > 0`). -/
theorem hasFDerivAt_lambda {uc : ℝ × ℝ → ℝ} {Ybar ucc ucxi : ℝ} (hY : 0 < Ybar)
    (hu : 0 < uc (Ybar, 0)) (hcc : ucc ≠ 0)
    (huc : HasFDerivAt uc (ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ucxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar, 0)) :
    HasFDerivAt (lambda uc Ybar) ((-(-uc (Ybar, 0) / (ucc * Ybar))⁻¹) •
      (ContinuousLinearMap.fst ℝ ℝ ℝ - (-ucxi / (Ybar * ucc)) • ContinuousLinearMap.snd ℝ ℝ ℝ))
      0 := by
  set h : ℝ × ℝ → ℝ × ℝ := fun p => (Ybar * Real.exp p.1, p.2) with hh
  have hd : HasFDerivAt h ((Ybar * Real.exp (0 : ℝ × ℝ).1) •
      ContinuousLinearMap.fst ℝ ℝ ℝ |>.prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) 0 := by
    have h1 := (hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ))).exp.const_mul Ybar
    refine HasFDerivAt.prodMk ?_ hasFDerivAt_snd
    convert h1 using 1
    rw [smul_smul]
  have h0 : h 0 = (Ybar, 0) := by simp [hh]
  have huc' : HasFDerivAt uc (ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ucxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (h 0) := by rw [h0]; exact huc
  have hcomp := (huc'.comp (0 : ℝ × ℝ) hd).log
    (by rw [Function.comp_apply, h0]; exact hu.ne')
  have hfin := hcomp.sub_const (Real.log (uc (Ybar, 0)))
  refine hfin.congr_fderiv ?_
  ext
  · simp [h0]
    field_simp
  · simp [h0]
    field_simp

/-- Woodford (2003), eq. (1.33) with government purchases, p. 80: `λ(Ŷ, Ĝ, ξ) =
log u_c(Ȳ e^Ŷ − Ḡ − Ȳ Ĝ; ξ) − log u_c(C̄; 0)`, with `C̄ = Ȳ − Ḡ` and `Ĝ = (G − Ḡ)/Ȳ`. -/
noncomputable def lambdaG (uc : ℝ × ℝ → ℝ) (Ybar Gbar : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  Real.log (uc (Ybar * Real.exp p.1 - Gbar - Ybar * p.2.1, p.2.2)) -
    Real.log (uc (Ybar - Gbar, 0))

/-- Woodford (2003), eq. (1.33) with government purchases, p. 80: the derivative of
`λ(Ŷ, Ĝ, ξ)` at the steady state is `−σ⁻¹(Ŷ − g)` with `σ = s_C σ_C`, `s_C = C̄/Ȳ`,
`σ_C = −u_c/(u_cc C̄)`, and `g = Ĝ + s_C c̄`, `c̄ = −u_cξ ξ/(C̄ u_cc)`. -/
theorem hasFDerivAt_lambdaG {uc : ℝ × ℝ → ℝ} {Ybar Gbar ucc ucxi : ℝ} (hY : 0 < Ybar)
    (hC : 0 < Ybar - Gbar) (hu : 0 < uc (Ybar - Gbar, 0)) (hcc : ucc ≠ 0)
    (huc : HasFDerivAt uc (ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ucxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar - Gbar, 0)) :
    HasFDerivAt (lambdaG uc Ybar Gbar)
      ((-(((Ybar - Gbar) / Ybar) * (-uc (Ybar - Gbar, 0) / (ucc * (Ybar - Gbar))))⁻¹) •
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) -
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
          ((Ybar - Gbar) / Ybar * (-ucxi / ((Ybar - Gbar) * ucc))) •
            (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))) 0 := by
  set h : ℝ × ℝ × ℝ → ℝ × ℝ := fun p => (Ybar * Real.exp p.1 - Gbar - Ybar * p.2.1, p.2.2)
    with hh
  have hd1 : HasFDerivAt (fun p : ℝ × ℝ × ℝ => Ybar * Real.exp p.1 - Gbar - Ybar * p.2.1)
      (Ybar • Real.exp (0 : ℝ × ℝ × ℝ).1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) -
        Ybar • ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))) 0 := by
    have h1 := ((hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ))).exp.const_mul Ybar).sub_const
      Gbar
    have h2 := ((hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ).2)).comp (0 : ℝ × ℝ × ℝ)
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ)))).const_mul Ybar
    exact h1.sub h2
  have hd2 : HasFDerivAt (fun p : ℝ × ℝ × ℝ => p.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) 0 :=
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ).2)).comp (0 : ℝ × ℝ × ℝ)
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ)))
  have hd := hd1.prodMk hd2
  have h0 : h 0 = (Ybar - Gbar, 0) := by simp [hh]
  have huc' : HasFDerivAt uc (ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ucxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (h 0) := by rw [h0]; exact huc
  have hcomp := (huc'.comp (0 : ℝ × ℝ × ℝ) hd).log
    (by rw [Function.comp_apply, h0]; exact hu.ne')
  have hfin := hcomp.sub_const (Real.log (uc (Ybar - Gbar, 0)))
  refine hfin.congr_fderiv ?_
  have hC' : Ybar - Gbar ≠ 0 := hC.ne'
  ext
  · simp [h0]
    field_simp
  · simp [h0]
    field_simp
  · simp [h0]
    field_simp

/-! ### (1.32) + (1.33): the composite derivative on a finite state space -/

/-- Woodford (2003), eqs. (1.21), (1.32)–(1.33), pp. 71, 79–80 (finite state space): scale the
exogenous deviations `(Ŷ, ξ)` and the inflation path `π` by `ε`; the exact Fisher map
`ε ↦ −log E_t[exp(λ(εŶ_{t+1}, εξ_{t+1}) − λ(εŶ_t, εξ_t) − ε π_{t+1})]` (see `fisher_log_form`)
has derivative `E_t[Dλ(Ŷ_t, ξ_t) − Dλ(Ŷ_{t+1}, ξ_{t+1})] + E_t π_{t+1}` at `ε = 0`. -/
theorem fisher_composite_deriv [Finite Ω] {lam : ℝ × ℝ → ℝ} {Dlam : ℝ × ℝ →L[ℝ] ℝ}
    (hlam : HasFDerivAt lam Dlam 0) (hlam0 : lam 0 = 0) (Yh xi π : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) :
    HasDerivAt (fun ε => -Real.log (𝔼.E t (fun ω' => Real.exp
      (lam (ε * Yh (t + 1) ω', ε * xi (t + 1) ω') - lam (ε * Yh t ω', ε * xi t ω') -
        ε * π (t + 1) ω')) ω))
      (𝔼.E t (fun ω' => Dlam (Yh t ω', xi t ω') - Dlam (Yh (t + 1) ω', xi (t + 1) ω') +
        π (t + 1) ω') ω) 0 := by
  have hdir : ∀ a b : ℝ, HasDerivAt (fun ε : ℝ => lam (ε * a, ε * b)) (Dlam (a, b)) 0 := by
    intro a b
    have hp : HasDerivAt (fun ε : ℝ => (ε * a, ε * b)) (a, b) 0 :=
      (hasDerivAt_mul_const a).prodMk (hasDerivAt_mul_const b)
    have he : (fun ε : ℝ => (ε * a, ε * b)) 0 = 0 := by simp
    have hl : HasFDerivAt lam Dlam ((fun ε : ℝ => (ε * a, ε * b)) 0) := by
      rw [he]; exact hlam
    exact hl.comp_hasDerivAt (0 : ℝ) hp
  have hpt : ∀ ω', HasDerivAt (fun ε => Real.exp (lam (ε * Yh (t + 1) ω', ε * xi (t + 1) ω') -
      lam (ε * Yh t ω', ε * xi t ω') - ε * π (t + 1) ω'))
      (Dlam (Yh (t + 1) ω', xi (t + 1) ω') - Dlam (Yh t ω', xi t ω') - π (t + 1) ω') 0 := by
    intro ω'
    have h := (((hdir (Yh (t + 1) ω') (xi (t + 1) ω')).sub (hdir (Yh t ω') (xi t ω'))).sub
      (hasDerivAt_mul_const (π (t + 1) ω'))).exp
    simpa [hlam0] using h
  have hE := hasDerivAt_E 𝔼 hpt t ω
  have h1 : 𝔼.E t (fun ω' => Real.exp (lam (0 * Yh (t + 1) ω', 0 * xi (t + 1) ω') -
      lam (0 * Yh t ω', 0 * xi t ω') - 0 * π (t + 1) ω')) ω = 1 := by
    simp only [zero_mul, Prod.mk_zero_zero, hlam0, sub_self, Real.exp_zero]
    rw [𝔼.const]
  have hlog := hE.log (by rw [h1]; exact one_ne_zero)
  rw [h1, div_one] at hlog
  convert hlog.neg using 1
  have hfun : (fun ω' => Dlam (Yh t ω', xi t ω') - Dlam (Yh (t + 1) ω', xi (t + 1) ω') +
      π (t + 1) ω') = -(fun ω' => Dlam (Yh (t + 1) ω', xi (t + 1) ω') -
        Dlam (Yh t ω', xi t ω') - π (t + 1) ω') := by
    funext ω'
    simp only [Pi.neg_apply]
    ring
  rw [hfun, map_neg]
  rfl

/-- Woodford (2003), eqs. (1.32)–(1.33), pp. 79–80 (finite state space): with
`λ = log u_c(Ȳ e^Ŷ; ξ) − log u_c(Ȳ; 0)` (whose derivative is `−σ⁻¹(Ŷ − g)`,
`hasFDerivAt_lambda`), the derivative of the exact Fisher map (1.21) is
`r̂_t + E_t π_{t+1}` with `r̂_t = σ⁻¹ E_t[(Ŷ_{t+1} − g_{t+1}) − (Ŷ_t − g_t)]`, `g = gc ξ`. -/
theorem fisher_composite_deriv_1_33 [Finite Ω] {lam : ℝ × ℝ → ℝ} {σ gc : ℝ}
    (hlam : HasFDerivAt lam ((-σ⁻¹) • (ContinuousLinearMap.fst ℝ ℝ ℝ -
      gc • ContinuousLinearMap.snd ℝ ℝ ℝ)) 0) (hlam0 : lam 0 = 0) (Yh xi π : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => -Real.log (𝔼.E t (fun ω' => Real.exp
      (lam (ε * Yh (t + 1) ω', ε * xi (t + 1) ω') - lam (ε * Yh t ω', ε * xi t ω') -
        ε * π (t + 1) ω')) ω))
      (σ⁻¹ * 𝔼.E t (fun ω' => (Yh (t + 1) ω' - gc * xi (t + 1) ω') -
        (Yh t ω' - gc * xi t ω')) ω + 𝔼.E t (π (t + 1)) ω) 0 := by
  convert fisher_composite_deriv 𝔼 hlam hlam0 Yh xi π t ω using 1
  have hfun : (fun ω' => ((-σ⁻¹) • (ContinuousLinearMap.fst ℝ ℝ ℝ -
      gc • ContinuousLinearMap.snd ℝ ℝ ℝ)) (Yh t ω', xi t ω') -
      ((-σ⁻¹) • (ContinuousLinearMap.fst ℝ ℝ ℝ - gc • ContinuousLinearMap.snd ℝ ℝ ℝ))
        (Yh (t + 1) ω', xi (t + 1) ω') + π (t + 1) ω') =
      σ⁻¹ • (fun ω' => (Yh (t + 1) ω' - gc * xi (t + 1) ω') - (Yh t ω' - gc * xi t ω')) +
        π (t + 1) := by
    funext ω'
    simp
    ring
  rw [hfun, map_add, map_smul]
  rfl

/-! ### (1.34): the Wicksellian rule -/

/-- Woodford (2003), eqs. (1.30) and (1.34), pp. 77, 81: the Wicksellian rule in logs,
`(P̂, ν) ↦ î = log((1 + φ(e^{P̂}; ν))/(1 + ī)) = log(β(1 + φ(e^{P̂}; ν)))`, with
`1 + ī = β⁻¹`. -/
noncomputable def wicksellLog (φ : ℝ × ℝ → ℝ) (β : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.log (β * (1 + φ (Real.exp p.1, p.2)))

/-- Woodford (2003), eq. (1.34) and fn. 15, p. 81: if `1 + φ(1; 0) = β⁻¹` (zero-inflation steady
state, p. 78) and `φ` has partial derivatives `φ₁` (in `P/P*`) and `∂φ/∂ν = β⁻¹` (fn. 15's
normalisation), then the derivative of the rule in logs is `φ_p P̂ + ν` with `φ_p = β φ₁`. -/
theorem hasFDerivAt_wicksell {φ : ℝ × ℝ → ℝ} {β φ1 : ℝ} (hβ : 0 < β)
    (hss : 1 + φ (1, 0) = β⁻¹)
    (hφ : HasFDerivAt φ (φ1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
      β⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ) (1, 0)) :
    HasFDerivAt (wicksellLog φ β) ((β * φ1) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ContinuousLinearMap.snd ℝ ℝ ℝ) 0 := by
  set h : ℝ × ℝ → ℝ × ℝ := fun p => (Real.exp p.1, p.2) with hh
  have hd : HasFDerivAt h ((Real.exp (0 : ℝ × ℝ).1 • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ)) 0 :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ))).exp.prodMk hasFDerivAt_snd
  have h0 : h 0 = (1, 0) := by simp [hh]
  have hφ' : HasFDerivAt φ (φ1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
      β⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ) (h 0) := by rw [h0]; exact hφ
  have hval : β * (1 + φ (h 0)) ≠ 0 := by
    rw [h0, hss]
    exact mul_ne_zero hβ.ne' (inv_ne_zero hβ.ne')
  have hcomp := (((hφ'.comp (0 : ℝ × ℝ) hd).const_add 1).const_mul β).log hval
  refine hcomp.congr_fderiv ?_
  ext
  · simp [h0, hss]
    field_simp
  · simp [h0, hss]
    field_simp

/-! ### (2.4)–(2.5): the Taylor rule -/

/-- Woodford (2003), eqs. (2.4)–(2.5), pp. 90–91: the Taylor rule in logs,
`(π, π*, ν) ↦ î = log((1 + φ(e^{π − π*}; ν))/(1 + ī)) = log(β(1 + φ(e^{π − π*}; ν)))`, with
`1 + ī = β⁻¹`. -/
noncomputable def taylorLog (φ : ℝ × ℝ → ℝ) (β : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  Real.log (β * (1 + φ (Real.exp (p.1 - p.2.1), p.2.2)))

/-- Woodford (2003), eqs. (2.4)–(2.5), pp. 90–91: with `φ(1; 0) = β⁻¹ − 1`, `∂φ/∂ν = β⁻¹` and
`φ_π = β φ₁`, the derivative of the Taylor rule in logs is `φ_π(π − π*) + ν`, i.e.
`î_t = ī_t + φ_π π_t` with `ī_t = ν_t − φ_π π*_t`. -/
theorem hasFDerivAt_taylor {φ : ℝ × ℝ → ℝ} {β φ1 : ℝ} (hβ : 0 < β)
    (hss : φ (1, 0) = β⁻¹ - 1)
    (hφ : HasFDerivAt φ (φ1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
      β⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ) (1, 0)) (p : ℝ × ℝ × ℝ) :
    HasFDerivAt (taylorLog φ β) ((β * φ1) • (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) -
      (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) 0 ∧
    ((β * φ1) * (p.1 - p.2.1) + p.2.2 = (p.2.2 - (β * φ1) * p.2.1) + (β * φ1) * p.1) := by
  refine ⟨?_, by ring⟩
  set h : ℝ × ℝ × ℝ → ℝ × ℝ := fun p => (Real.exp (p.1 - p.2.1), p.2.2) with hh
  have hsub : HasFDerivAt (fun p : ℝ × ℝ × ℝ => p.1 - p.2.1)
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) -
        (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) 0 :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ))).sub
      ((hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ).2)).comp (0 : ℝ × ℝ × ℝ)
        (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ))))
  have hd2 : HasFDerivAt (fun p : ℝ × ℝ × ℝ => p.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) 0 :=
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ).2)).comp (0 : ℝ × ℝ × ℝ)
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ)))
  have hd := hsub.exp.prodMk hd2
  have h0 : h 0 = (1, 0) := by simp [hh]
  have hφ' : HasFDerivAt φ (φ1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
      β⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ) (h 0) := by rw [h0]; exact hφ
  have hval : β * (1 + φ (h 0)) ≠ 0 := by
    rw [h0, hss, add_sub_cancel]
    exact mul_ne_zero hβ.ne' (inv_ne_zero hβ.ne')
  have hcomp := (((hφ'.comp (0 : ℝ × ℝ × ℝ) hd).const_add 1).const_mul β).log hval
  refine hcomp.congr_fderiv ?_
  ext
  · simp [h0, hss]
    field_simp
  · simp [h0, hss]
    field_simp
  · simp [h0, hss]
    field_simp

end Woodford.PriceLevelDetermination.LogLinear
