/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.Determinacy2
import NeoWicksellianFramework.NaturalRate
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Money and aggregate demand

Woodford (2003), *Interest and Prices*, Chapter 4, §3, pp. 295–311 (with the determinacy
results of App. C.1–C.2, pp. 670–677, that §3 relies on).

## The LM relation (§3.1)

* (3.1)–(3.2): `MoneyFOC`, `spreadOf`, `foc_iff_lm` (with `U_m/U_c` strictly decreasing in real
  balances the first-order condition is exactly `Mˢ/P = L(Y, Δ; ξ)`); `spreadOf_eq`, `spread`
  (`Δ` depends on interest rates only through `î − îᵐ`), `spread_const_iff`.
* (3.3) as an exact derivative: `hasFDerivAt_moneyDemand` (`η_y`, `η_i` defined as `etaY`,
  `etaI`), signs `lm_partials`, `eta_pos`; the linear relation `LM`.
* p. 297, money under price stability: `priceStability_iff` (`π ≡ 0`, `x ≡ 0` iff `î = r̂ⁿ`),
  `rnat_ar1`, `money_priceStability`; the four shocks `ynat_productivity`, `ynat_laborSupply`,
  `ynat_government`, `ynat_consumption`; `procyclical_productivity`,
  `procyclical_laborSupply` (procyclical money, more procyclical than under an interest-rate
  peg), `procyclical_government`, `procyclical_consumption` (procyclical iff
  `η_iω(1 − ρ) < η_y`: "if sufficiently persistent").

## Real-balance effects (§3.2)

* (3.4)–(3.5): `Euler`, `euler_log_form`, `logMU`, `chi`, `hasFDerivAt_logMU`,
  `hasDerivAt_E`, `euler_composite_deriv`, `euler_deriv_35` (on a finite state space (3.5) is
  the exact derivative of (3.4)), `IS35`, `is35_of_deriv`, `is35_of_lambda`.
* (3.6): `is35_iff_X`, `is36` (forward solution as a limit of partial sums).
* (3.7)–(3.8): `v38`, `IS37`, `is35_iff_37`.
* Footnote 62 (corrected): `fn62_constSpread`, `fn62_marginalUtility`, `fn62_printed_fails`.
* (3.9)–(3.10): `rn39`, `natural_rate_39`, `rn39_chi_zero`, `IS310`, `is37_iff_310`.
* (3.11)–(3.13): `logSupply`, `hasFDerivAt_logSupply`, `logMC`, `hasFDerivAt_logMC`,
  `mc_deriv_form`, `mcAvg`, `epsMC`, `ynat313`, `mc311`, `mc311_phi`, `ynat313_flex`,
  `ynat313_chi_zero`; **error E10**: `printed312_iff`, `printed312_fails_calibration`,
  `printed312_not_pos`.
* (3.14) and the bounds: `AS314`, `kappa314`, `as314_of_mc`, `kappa314_pos`, `bounds_pos`.
* Constant spread (pp. 304–305): `is310_constSpread`, `as314_constSpread`, `sigmaTilde`.
* Numbers: `phi_calibration`, `chiSigma_calibration`, `fn65_calibration`.
* Footnote 71 (**error E11**): `fn71_steadyState`, `fn71_printed_iff`.

## Determinacy (App. C.1–C.2 and footnote 70)

* The `2 × 2` determinacy theory (`BlanchardKahn.fwd_existsUnique`, `fwdDeterminate_iff`) and
  Proposition 4.3 for the basic model (`Determinacy2.prop_4_3`, with the canonical model
  (1.12)–(1.14) `BasicModel.IS112`, `BasicModel.NKPCurve`, `Determinacy2.taylorRate`) are
  imported; determinacy of a model is `Determinacy2.ModelDeterminate`.
* Constant spread: `money_constSpread_determinate` (determinate iff (2.7), from
  `Determinacy2.prop_4_3` with `σ̃ = (σ⁻¹ − η_yχ)⁻¹`).
* Footnote 70 (`îᵐ = 0`): `M70`, `N70`, `Eq70`, `eq70_iff_solves` (through
  `BlanchardKahn.solvesMN_iff`), `determinate70_iff`, `solveMN70_zero`, `fn70` (determinacy
  status unchanged for all small `χ` whenever (2.7) holds or fails strictly).

Corrections recorded: E10 ((3.12) prints `η_i` for `η_y`), E11 (fn. 71 sign), fn. 62 (the
reinterpreted disturbance is `(σ⁻¹g + χεᵐ)/(σ⁻¹ − η_yχ)`, not `g + σχεᵐ`), p. 305 ("(3.4)" for
(3.10)), p. 304 (`ϕ > 0` needs `χ > 0`).
-/

namespace Woodford.NeoWicksellianFramework.Money

open Filter Topology Determinacy2 BlanchardKahn
open BasicModel (IS112 NKPCurve xbar rnHat)
open NaturalRate (qLin gLin ynLin)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (3.1)–(3.3): money demand -/

/-- Woodford (2003), eq. (3.1), p. 295: the household's first-order condition for money,
`U_m(C, m; ξ)/U_c(C, m; ξ) = (i − iᵐ)/(1 + i)`. -/
def MoneyFOC (Um Uc : ℝ → ℝ → ℝ → ℝ) (C m ξ i im : ℝ) : Prop :=
  Um C m ξ / Uc C m ξ = (i - im) / (1 + i)

/-- Woodford (2003), eq. (3.2), p. 295: the interest differential `Δ = (i − iᵐ)/(1 + i)`. -/
noncomputable def spreadOf (i im : ℝ) : ℝ := (i - im) / (1 + i)

/-- Woodford (2003), eqs. (3.1)–(3.2), pp. 295–296: if the money-demand function `L` solves
`U_m/U_c(Y, L(Y, Δ, ξ); ξ) = Δ` and `U_m/U_c` is strictly decreasing in real balances on
`m > 0` (the normal-goods hypothesis of Chapter 2), then with goods-market clearing `C = Y`
the first-order condition (3.1) at real balances `Mˢ/P > 0` is equivalent to the LM equation
(3.2) `Mˢ/P = L(Y, Δ; ξ)`. -/
theorem foc_iff_lm {Um Uc : ℝ → ℝ → ℝ → ℝ} {L : ℝ × ℝ × ℝ → ℝ}
    (hL : ∀ Y Δ ξ, Um Y (L (Y, Δ, ξ)) ξ / Uc Y (L (Y, Δ, ξ)) ξ = Δ)
    (hLpos : ∀ Y Δ ξ, 0 < L (Y, Δ, ξ))
    (hanti : ∀ Y ξ, StrictAntiOn (fun m => Um Y m ξ / Uc Y m ξ) (Set.Ioi 0))
    {Y ξ i im M P : ℝ} (hMP : 0 < M / P) :
    MoneyFOC Um Uc Y (M / P) ξ i im ↔ M / P = L (Y, spreadOf i im, ξ) := by
  unfold MoneyFOC spreadOf
  constructor
  · intro h
    refine (hanti Y ξ).injOn (Set.mem_Ioi.mpr hMP) (Set.mem_Ioi.mpr (hLpos _ _ _)) ?_
    rw [h, hL]
  · intro h
    rw [h, hL]

/-- Woodford (2003), (3.2)–(3.3), pp. 295–296: the interest differential
`Δ = 1 − (1 + iᵐ)/(1 + i)` in terms of the log deviations `î = log((1 + i)/(1 + ī))`,
`îᵐ = log((1 + iᵐ)/(1 + īᵐ))`, where `1 + ī = β⁻¹` and `Δ̄ = 1 − β(1 + īᵐ)` (restated from the
Chapter 2 project). -/
noncomputable def spread (Δbar ihat imhat : ℝ) : ℝ := 1 - (1 - Δbar) * Real.exp (imhat - ihat)

/-- Woodford (2003), (3.2), p. 295: with `1 + i = β⁻¹ e^{î}` and `1 + iᵐ = (1 + īᵐ) e^{îᵐ}`,
`(i − iᵐ)/(1 + i) = spread Δ̄ î îᵐ` for `Δ̄ = 1 − β(1 + īᵐ)`: the differential depends on the
interest rates only through `î − îᵐ` (restated from the Chapter 2 project). -/
theorem spreadOf_eq {β ibm ih imh : ℝ} (hβ : 0 < β) :
    spreadOf (β⁻¹ * Real.exp ih - 1) ((1 + ibm) * Real.exp imh - 1) =
      spread (1 - β * (1 + ibm)) ih imh := by
  unfold spreadOf spread
  rw [Real.exp_sub]
  have := Real.exp_pos ih
  field_simp
  ring

/-- Woodford (2003), p. 304: holding the differential at `Δ = Δ̄ < 1` is exactly `î = îᵐ`
(not only to first order; restated from the Chapter 2 project). -/
theorem spread_const_iff {Δbar ih imh : ℝ} (hΔ : Δbar < 1) :
    spread Δbar ih imh = Δbar ↔ ih = imh := by
  unfold spread
  constructor
  · intro h
    have h1 : Real.exp (imh - ih) = 1 := by
      have : (1 - Δbar) * Real.exp (imh - ih) = (1 - Δbar) * 1 := by linarith
      exact mul_left_cancel₀ (by linarith) this
    rw [Real.exp_eq_one_iff] at h1
    linarith
  · rintro rfl
    simp

/-- Woodford (2003), (3.3), p. 296: a linear functional on `ℝ³` is determined by its values on
the coordinate vectors (restated from the Chapter 2 project). -/
theorem clm3_apply (L' : ℝ × ℝ × ℝ →L[ℝ] ℝ) (a b c : ℝ) :
    L' (a, b, c) = a * L' (1, 0, 0) + b * L' (0, 1, 0) + c * L' (0, 0, 1) := by
  have h : ((a, b, c) : ℝ × ℝ × ℝ) = a • (1, 0, 0) + b • (0, 1, 0) + c • (0, 0, 1) := by
    ext <;> simp
  rw [h, map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]

/-- Woodford (2003), (3.3), p. 296: a linear functional on `ℝ²` is determined by its values on
the coordinate vectors (restated from the Chapter 2 project). -/
theorem clm2_apply (R' : ℝ × ℝ →L[ℝ] ℝ) (a b : ℝ) :
    R' (a, b) = a * R' (1, 0) + b * R' (0, 1) := by
  have h : ((a, b) : ℝ × ℝ) = a • (1, 0) + b • (0, 1) := by ext <;> simp
  rw [h, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- Woodford (2003), (3.2)–(3.3), pp. 295–296: log real money demand
`log(L(Ȳ e^{ŷ}, Δ(î, îᵐ), ξ)/m̄)` as a function of the log deviations `(ŷ, î, îᵐ, ξ)`. -/
noncomputable def moneyDemandLog (L : ℝ × ℝ × ℝ → ℝ) (Ybar mbar Δbar : ℝ)
    (x : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  Real.log (L (Ybar * Real.exp x.1, spread Δbar x.2.1 x.2.2.1, x.2.2.2)) - Real.log mbar

/-- Woodford (2003), (3.3), p. 296: the income elasticity `η_y = (Ȳ/m̄) ∂L/∂Y`. -/
noncomputable def etaY (L' : ℝ × ℝ × ℝ →L[ℝ] ℝ) (Ybar mbar : ℝ) : ℝ := Ybar / mbar * L' (1, 0, 0)

/-- Woodford (2003), (3.3), p. 296: the interest semielasticity `η_i = −((1 − Δ̄)/m̄) ∂L/∂Δ`. -/
noncomputable def etaI (L' : ℝ × ℝ × ℝ →L[ℝ] ℝ) (mbar Δbar : ℝ) : ℝ :=
  -((1 - Δbar) / mbar * L' (0, 1, 0))

/-- Woodford (2003), (3.3), p. 296: the coefficient `(1/m̄) ∂L/∂ξ` of the money-demand
disturbance `εᵐ`. -/
noncomputable def epsCoef (L' : ℝ × ℝ × ℝ →L[ℝ] ℝ) (mbar : ℝ) : ℝ := L' (0, 0, 1) / mbar

/-- Woodford (2003), eq. (3.3), p. 296 (exact derivative): if `L` is differentiable at the
steady state `(Ȳ, Δ̄, 0)` with `L(Ȳ, Δ̄, 0) = m̄ > 0`, the derivative of log real money demand in
`(ŷ, î, îᵐ, ξ)` at zero is `η_y ŷ − η_i(î − îᵐ) + (1/m̄) L_ξ ξ` (restated from the Chapter 2
project). -/
theorem hasFDerivAt_moneyDemand {L : ℝ × ℝ × ℝ → ℝ} {L' : ℝ × ℝ × ℝ →L[ℝ] ℝ}
    {Ybar mbar Δbar : ℝ} (hL : HasFDerivAt L L' (Ybar, Δbar, 0))
    (hss : L (Ybar, Δbar, 0) = mbar) (hm : 0 < mbar) :
    ∃ G' : ℝ × ℝ × ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (moneyDemandLog L Ybar mbar Δbar) G' 0 ∧
      ∀ v, G' v = etaY L' Ybar mbar * v.1 - etaI L' mbar Δbar * (v.2.1 - v.2.2.1) +
        epsCoef L' mbar * v.2.2.2 := by
  let P1 : ℝ × ℝ × ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ × ℝ)
  let P2 : ℝ × ℝ × ℝ × ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ))
  let P3 : ℝ × ℝ × ℝ × ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ)))
  let P4 : ℝ × ℝ × ℝ × ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ)))
  have hY := (P1.hasFDerivAt (x := 0)).exp.const_mul Ybar
  have hS := (((P3.hasFDerivAt (x := 0)).sub (P2.hasFDerivAt (x := 0))).exp.const_mul
    (1 - Δbar)).const_sub 1
  have hg := hY.prodMk (hS.prodMk (P4.hasFDerivAt (x := 0)))
  have hg0 : ((Ybar * Real.exp (P1 0), 1 - (1 - Δbar) * Real.exp (P3 0 - P2 0), P4 0) :
      ℝ × ℝ × ℝ) = (Ybar, Δbar, 0) := by simp
  rw [← hg0] at hL
  have hc := hL.comp (0 : ℝ × ℝ × ℝ × ℝ) hg
  have hne : (L ∘ fun x => (Ybar * Real.exp (P1 x), 1 - (1 - Δbar) * Real.exp (P3 x - P2 x),
      P4 x)) 0 ≠ 0 := by
    simp only [Function.comp_apply]
    rw [hg0, hss]
    exact hm.ne'
  have hlog := (hc.log hne).sub_const (Real.log mbar)
  refine ⟨_, hlog, fun v => ?_⟩
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, smul_eq_mul]
  rw [clm3_apply]
  simp [P1, P2, P3, P4, etaY, etaI, epsCoef, hss]
  field_simp
  ring

/-- Woodford (2003), (3.2)–(3.3), pp. 295–296 (signs by implicit differentiation): if
`R = U_m/U_c` is differentiable at `(Ȳ, m̄)` and `R(Y, L(Y, Δ, 0)) = Δ` near `(Ȳ, Δ̄)`, then
`R_c + R_m L_Y = 0` and `R_m L_Δ = 1` (restated from the Chapter 2 project). -/
theorem lm_partials {R : ℝ × ℝ → ℝ} {R' : ℝ × ℝ →L[ℝ] ℝ} {L : ℝ × ℝ × ℝ → ℝ}
    {L' : ℝ × ℝ × ℝ →L[ℝ] ℝ} {Ybar Δbar : ℝ} (hR : HasFDerivAt R R' (Ybar, L (Ybar, Δbar, 0)))
    (hL : HasFDerivAt L L' (Ybar, Δbar, 0))
    (hid : ∀ᶠ y in 𝓝 ((Ybar, Δbar) : ℝ × ℝ), R (y.1, L (y.1, y.2, 0)) = y.2) :
    R' (1, 0) + R' (0, 1) * L' (1, 0, 0) = 0 ∧ R' (0, 1) * L' (0, 1, 0) = 1 := by
  let Q : ℝ × ℝ →L[ℝ] ℝ × ℝ × ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod 0)
  have hq : HasFDerivAt (fun y : ℝ × ℝ => ((y.1, y.2, 0) : ℝ × ℝ × ℝ)) Q (Ybar, Δbar) :=
    Q.hasFDerivAt
  have hLq := hL.comp ((Ybar, Δbar) : ℝ × ℝ) hq
  have hh := (hasFDerivAt_fst (p := ((Ybar, Δbar) : ℝ × ℝ))).prodMk hLq
  have hk := hR.comp ((Ybar, Δbar) : ℝ × ℝ) hh
  have hk2 : HasFDerivAt (fun y : ℝ × ℝ => R (y.1, L (y.1, y.2, 0)))
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar, Δbar) :=
    (hasFDerivAt_snd (p := ((Ybar, Δbar) : ℝ × ℝ))).congr_of_eventuallyEq hid
  have heq := hk.unique hk2
  have e1 := congrArg (fun F : ℝ × ℝ →L[ℝ] ℝ => F (1, 0)) heq
  have e2 := congrArg (fun F : ℝ × ℝ →L[ℝ] ℝ => F (0, 1)) heq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Q] at e1 e2
  simp only [zero_apply] at e1 e2
  rw [clm2_apply] at e1 e2
  simp only [zero_mul, one_mul, zero_add] at e1 e2
  constructor
  · linarith
  · linarith

/-- Woodford (2003), (3.3), p. 296: the signs `η_y > 0`, `η_i > 0`, from `U_m/U_c` strictly
increasing in consumption (`R_c > 0`) and strictly decreasing in real balances (`R_m < 0`) at
the steady state, through `lm_partials`, given `Ȳ, m̄ > 0` and `Δ̄ < 1` (restated from the
Chapter 2 project). -/
theorem eta_pos {R' : ℝ × ℝ →L[ℝ] ℝ} {L' : ℝ × ℝ × ℝ →L[ℝ] ℝ} {Ybar mbar Δbar : ℝ}
    (h1 : R' (1, 0) + R' (0, 1) * L' (1, 0, 0) = 0) (h2 : R' (0, 1) * L' (0, 1, 0) = 1)
    (hRc : 0 < R' (1, 0)) (hRm : R' (0, 1) < 0) (hY : 0 < Ybar) (hm : 0 < mbar)
    (hΔ : Δbar < 1) : 0 < etaY L' Ybar mbar ∧ 0 < etaI L' mbar Δbar := by
  have hLY : 0 < L' (1, 0, 0) := by
    by_contra h
    push Not at h
    nlinarith
  have hLD : L' (0, 1, 0) < 0 := by
    by_contra h
    push Not at h
    nlinarith
  unfold etaY etaI
  constructor
  · positivity
  · have : 0 < (1 - Δbar) / mbar := div_pos (by linarith) hm
    nlinarith

/-- Woodford (2003), eq. (3.3), p. 296: the log-linear LM relation
`m̂_t = η_y Ŷ_t − η_i(î_t − îᵐ_t) + εᵐ_t`. -/
def LM (ηy ηi : ℝ) (Y i im e mh : ℕ → Ω → ℝ) : Prop :=
  ∀ t, mh t = ηy • Y t - ηi • (i t - im t) + e t

/-! ### p. 297: the money supply under price stability -/


/-- Woodford (2003), p. 297 (with §2.1, p. 248): under price stability, `π ≡ 0` and `x ≡ 0`
solve the Phillips curve, and they solve the IS relation exactly when the nominal rate tracks
the natural rate, `î = r̂ⁿ` (`σ ≠ 0`). -/
theorem priceStability_iff {σ κ β : ℝ} (hσ : σ ≠ 0) {i rn : ℕ → Ω → ℝ} :
    NKPCurve 𝔼 β κ 0 0 ∧ (IS112 𝔼 σ 0 i 0 rn ↔ i = rn) := by
  refine ⟨fun t => by simp, ?_⟩
  unfold IS112
  constructor
  · intro h
    funext t ω
    have h1 := congrFun (h t) ω
    simp only [Pi.zero_apply, map_zero, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      zero_sub, sub_zero] at h1
    have : σ * (i t ω - rn t ω) = 0 := by linarith
    rcases mul_eq_zero.mp this with h2 | h2
    · exact absurd h2 hσ
    · linarith
  · rintro rfl t
    funext ω
    simp

/-- Woodford (2003), p. 297, with (1.15) and Prop. 4.1, p. 250: if a single AR(1) disturbance
`s` (persistence `ρ`) moves `g_t = c_g s_t` and `Ŷⁿ_t = c_Y s_t`, the natural rate of interest is
`r̂ⁿ_t = σ⁻¹(1 − ρ)(c_g − c_Y) s_t`; in particular it vanishes as `ρ → 1`. -/
theorem rnat_ar1 {σinv ρ cg cY : ℝ} {s : ℕ → Ω → ℝ} (hs : 𝔼.IsAR1 ρ s) (t : ℕ) :
    rnHat 𝔼 σinv⁻¹ (fun t => cg • s t) (fun t => cY • s t) t =
      (σinv * (1 - ρ) * (cg - cY)) • s t := by
  unfold rnHat
  rw [inv_inv, ← sub_smul, ← sub_smul, map_smul, hs.2 t, smul_smul]
  funext ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), p. 297: under price stability (`î = r̂ⁿ`, `Ŷ = Ŷⁿ`), with no interest on
money (`îᵐ = 0`) and no money-demand shock, the LM relation (3.3) requires
`m̂_t = [η_y c_Y − η_i σ⁻¹(1 − ρ)(c_g − c_Y)] s_t` for a single AR(1) disturbance as in
`rnat_ar1`. -/
theorem money_priceStability {σinv ρ cg cY ηy ηi : ℝ} {s mh : ℕ → Ω → ℝ} (hs : 𝔼.IsAR1 ρ s)
    (hLM : LM ηy ηi (fun t => cY • s t) (rnHat 𝔼 σinv⁻¹ (fun t => cg • s t) (fun t => cY • s t))
      0 0 mh) (t : ℕ) :
    mh t = (ηy * cY - ηi * (σinv * (1 - ρ) * (cg - cY))) • s t := by
  rw [hLM t, rnat_ar1 𝔼 hs t]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
  ring

/-- Woodford (2003), p. 249: a productivity shock `a` moves the natural rate of output by
`Ŷⁿ = ((1 + ω)/(σ⁻¹ + ω)) a` (with `g = 0`, `h̄ = 0`, `ω ≠ 0`). -/
theorem ynat_productivity {σinv ω ν : ℝ} (hω : ω ≠ 0) (a : ℝ) :
    ynLin σinv⁻¹ ω 0 (qLin ω ν a 0) = (1 + ω) / (σinv + ω) * a := by
  unfold ynLin qLin
  simp only [inv_inv]
  field_simp
  ring

/-- Woodford (2003), p. 249: a labour-supply shock `h̄` moves the natural rate of output by
`Ŷⁿ = (ν/(σ⁻¹ + ω)) h̄` (`ω ≠ 0`). -/
theorem ynat_laborSupply {σinv ω ν : ℝ} (hω : ω ≠ 0) (h : ℝ) :
    ynLin σinv⁻¹ ω 0 (qLin ω ν 0 h) = ν / (σinv + ω) * h := by
  unfold ynLin qLin
  simp only [inv_inv]
  field_simp
  ring

/-- Woodford (2003), p. 249: a government-purchase shock `Ĝ` (so `g = Ĝ`) moves the natural
rate of output by `Ŷⁿ = (σ⁻¹/(σ⁻¹ + ω)) Ĝ`. -/
theorem ynat_government {σinv ω ν : ℝ} (G : ℝ) :
    ynLin σinv⁻¹ ω (gLin 0 G 0) (qLin ω ν 0 0) = σinv / (σinv + ω) * G := by
  unfold ynLin qLin gLin
  simp only [inv_inv]
  ring

/-- Woodford (2003), p. 249: a consumption-demand shock `c̄` (so `g = s_C c̄`) moves the
natural rate of output by `Ŷⁿ = (σ⁻¹ s_C/(σ⁻¹ + ω)) c̄`. -/
theorem ynat_consumption {σinv ω ν sC : ℝ} (c : ℝ) :
    ynLin σinv⁻¹ ω (gLin sC 0 c) (qLin ω ν 0 0) = σinv * sC / (σinv + ω) * c := by
  unfold ynLin qLin gLin
  simp only [inv_inv]
  ring

/-- Woodford (2003), p. 297, citing Ireland (1996): under price stability a temporary
productivity shock (`0 ≤ ρ < 1`, `c_g = 0`, `c_Y = (1 + ω)/(σ⁻¹ + ω)`) raises output and
lowers the natural rate of interest, and money moves procyclically: the money response
coefficient is positive, and strictly larger than the response `η_y c_Y` that holding the nominal
interest rate unchanged at the same output response would require. -/
theorem procyclical_productivity {σinv ω ρ ηy ηi : ℝ} (hσ : 0 < σinv) (hω : 0 < ω)
    (hρ : ρ < 1) (hηy : 0 < ηy) (hηi : 0 < ηi) :
    let cY := (1 + ω) / (σinv + ω)
    0 < cY ∧ σinv * (1 - ρ) * (0 - cY) < 0 ∧
      ηy * cY < ηy * cY - ηi * (σinv * (1 - ρ) * (0 - cY)) ∧
      0 < ηy * cY - ηi * (σinv * (1 - ρ) * (0 - cY)) := by
  intro cY
  have hc : 0 < cY := div_pos (by linarith) (by linarith)
  have h1 : 0 < 1 - ρ := by linarith
  have h2 : σinv * (1 - ρ) * (0 - cY) < 0 := by
    have := mul_pos (mul_pos hσ h1) hc
    linarith
  refine ⟨hc, h2, ?_, ?_⟩
  · nlinarith
  · nlinarith

/-- Woodford (2003), p. 297: the same holds for a temporary labour-supply shock
(`c_Y = ν/(σ⁻¹ + ω)`, `ν > 0`). -/
theorem procyclical_laborSupply {σinv ω ν ρ ηy ηi : ℝ} (hσ : 0 < σinv) (hω : 0 < ω)
    (hν : 0 < ν) (hρ : ρ < 1) (hηy : 0 < ηy) (hηi : 0 < ηi) :
    let cY := ν / (σinv + ω)
    0 < cY ∧ σinv * (1 - ρ) * (0 - cY) < 0 ∧
      ηy * cY < ηy * cY - ηi * (σinv * (1 - ρ) * (0 - cY)) ∧
      0 < ηy * cY - ηi * (σinv * (1 - ρ) * (0 - cY)) := by
  intro cY
  have hc : 0 < cY := div_pos hν (by linarith)
  have h1 : 0 < 1 - ρ := by linarith
  have h2 : σinv * (1 - ρ) * (0 - cY) < 0 := by
    have := mul_pos (mul_pos hσ h1) hc
    linarith
  refine ⟨hc, h2, ?_, ?_⟩
  · nlinarith
  · nlinarith

/-- Woodford (2003), p. 297: for a government-purchase shock (`c_g = 1`,
`c_Y = σ⁻¹/(σ⁻¹ + ω)`) the natural rate of interest rises (`ρ < 1`), so the money response is
smaller than `η_y c_Y`; money is procyclical iff the shock is persistent enough,
`η_i ω (1 − ρ) < η_y` — "the result depends upon parameter values". -/
theorem procyclical_government {σinv ω ρ ηy ηi : ℝ} (hσ : 0 < σinv) (hω : 0 < ω)
    (hρ : ρ < 1) (hηi : 0 < ηi) :
    let cY := σinv / (σinv + ω)
    0 < cY ∧ 0 < σinv * (1 - ρ) * (1 - cY) ∧
      ηy * cY - ηi * (σinv * (1 - ρ) * (1 - cY)) < ηy * cY ∧
      (0 < ηy * cY - ηi * (σinv * (1 - ρ) * (1 - cY)) ↔ ηi * ω * (1 - ρ) < ηy) := by
  intro cY
  have hs : 0 < σinv + ω := by linarith
  have hc : 0 < cY := div_pos hσ hs
  have h1c : 1 - cY = ω / (σinv + ω) := by
    simp only [cY]; field_simp; ring
  have h1 : 0 < 1 - ρ := by linarith
  have hpos : 0 < σinv * (1 - ρ) * (1 - cY) := by
    rw [h1c]; exact mul_pos (mul_pos hσ h1) (div_pos hω hs)
  refine ⟨hc, hpos, by nlinarith, ?_⟩
  have hid : ηy * cY - ηi * (σinv * (1 - ρ) * (1 - cY)) =
      σinv / (σinv + ω) * (ηy - ηi * ω * (1 - ρ)) := by
    rw [h1c]; simp only [cY]; field_simp
  rw [hid]
  constructor
  · intro h
    have := (pos_iff_pos_of_mul_pos h).mp (div_pos hσ hs)
    linarith
  · intro h
    exact mul_pos (div_pos hσ hs) (by linarith)

/-- Woodford (2003), p. 297: for a consumption-demand shock (`c_g = s_C`,
`c_Y = σ⁻¹ s_C/(σ⁻¹ + ω)`, `s_C > 0`) the conclusions are those for government purchases:
money is procyclical iff `η_i ω (1 − ρ) < η_y`. -/
theorem procyclical_consumption {σinv ω ρ ηy ηi sC : ℝ} (hσ : 0 < σinv) (hω : 0 < ω)
    (hρ : ρ < 1) (hηi : 0 < ηi) (hsC : 0 < sC) :
    let cY := σinv * sC / (σinv + ω)
    0 < cY ∧ 0 < σinv * (1 - ρ) * (sC - cY) ∧
      ηy * cY - ηi * (σinv * (1 - ρ) * (sC - cY)) < ηy * cY ∧
      (0 < ηy * cY - ηi * (σinv * (1 - ρ) * (sC - cY)) ↔ ηi * ω * (1 - ρ) < ηy) := by
  intro cY
  have hs : 0 < σinv + ω := by linarith
  have hc : 0 < cY := div_pos (mul_pos hσ hsC) hs
  have h1c : sC - cY = sC * ω / (σinv + ω) := by
    simp only [cY]; field_simp; ring
  have h1 : 0 < 1 - ρ := by linarith
  have hpos : 0 < σinv * (1 - ρ) * (sC - cY) := by
    rw [h1c]; exact mul_pos (mul_pos hσ h1) (div_pos (mul_pos hsC hω) hs)
  refine ⟨hc, hpos, by nlinarith, ?_⟩
  have hid : ηy * cY - ηi * (σinv * (1 - ρ) * (sC - cY)) =
      σinv * sC / (σinv + ω) * (ηy - ηi * ω * (1 - ρ)) := by
    rw [h1c]; simp only [cY]; field_simp
  rw [hid]
  have hk : 0 < σinv * sC / (σinv + ω) := div_pos (mul_pos hσ hsC) hs
  constructor
  · intro h
    have := (pos_iff_pos_of_mul_pos h).mp hk
    linarith
  · intro h
    exact mul_pos hk (by linarith)

/-! ### (3.4)–(3.6): the Euler equation with nonseparable utility -/

/-- Woodford (2003), eq. (3.4), p. 301: the exact Euler equation at date `t`,
`1 + i_t = β⁻¹ {E_t[U_c(Y_{t+1}, M_{t+1}/P_{t+1}; ξ_{t+1}) P_t /
(U_c(Y_t, M_t/P_t; ξ_t) P_{t+1})]}⁻¹`, where `uc s` is the marginal utility of income
`U_c(Y_s, M_s/P_s; ξ_s)` at date `s`. -/
def Euler (β : ℝ) (i uc P : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, 1 + i t ω = β⁻¹ * (𝔼.E t (fun ω' => uc (t + 1) ω' * P t ω' / (uc t ω' * P (t + 1) ω')) ω)⁻¹

/-- Woodford (2003), eq. (3.4), p. 301 (logs): with positive marginal utilities and prices and
`1 + ī = β⁻¹`, (3.4) holds iff `î_t = −log E_t[exp(λ_{t+1} − λ_t − π_{t+1})]`, where
`î_t = log((1 + i_t)/(1 + ī))`, `λ_s = log(u_c,s/ū_c)` and `π_{t+1} = log(P_{t+1}/P_t)`
(the log form of the Euler equation, `BasicModel.euler_log_form`, with the price index
re-dated). -/
theorem euler_log_form {β ucbar : ℝ} (hβ : 0 < β) (hu : 0 < ucbar) {i uc P : ℕ → Ω → ℝ}
    (t : ℕ) (huc : ∀ s ω, 0 < uc s ω) (hP : ∀ s ω, 0 < P s ω) (hi : ∀ ω, 0 < 1 + i t ω)
    (hE : ∀ ω, 0 < 𝔼.E t (fun ω' => uc (t + 1) ω' * P t ω' / (uc t ω' * P (t + 1) ω')) ω) :
    Euler 𝔼 β i uc P t ↔ ∀ ω, Real.log ((1 + i t ω) / β⁻¹) =
      -Real.log (𝔼.E t (fun ω' => Real.exp (Real.log (uc (t + 1) ω' / ucbar) -
        Real.log (uc t ω' / ucbar) - Real.log (P (t + 1) ω' / P t ω'))) ω) := by
  have h := BasicModel.euler_log_form 𝔼 hβ hu (i := i) (m := uc) (P := fun s => P (s - 1)) t huc
    (fun s => hP (s - 1)) hi (by simpa using hE)
  simp only [Nat.add_sub_cancel, show t + 2 - 1 = t + 1 by omega] at h
  unfold Euler
  rw [h]
  refine forall_congr' fun ω => ?_
  rw [div_inv_eq_mul, mul_comm]

/-- Woodford (2003), (3.5), p. 301: the log marginal utility of income
`log U_c(Ȳ e^{Ŷ}, m̄ e^{m̂}; ξ) − log U_c(Ȳ, m̄; 0)` as a function of `(Ŷ, m̂, ξ)`. -/
noncomputable def logMU (Uc : ℝ × ℝ × ℝ → ℝ) (Ybar mbar : ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  Real.log (Uc (Ybar * Real.exp x.1, mbar * Real.exp x.2.1, x.2.2)) -
    Real.log (Uc (Ybar, mbar, 0))

/-- Woodford (2003), p. 301: `χ ≡ m̄ U_cm/U_c` at the steady state. -/
noncomputable def chi (mbar uc ucm : ℝ) : ℝ := mbar * ucm / uc

/-- Woodford (2003), (3.5), p. 301 (exact derivative): if `U_c` is differentiable at the steady
state `(Ȳ, m̄, 0)` with `U_c > 0` there, the derivative of `logMU` at zero is
`(Ŷ, m̂, ξ) ↦ −σ⁻¹ Ŷ + χ m̂ + (U_cξ/U_c) ξ`, with `σ⁻¹ = −U_cc Ȳ/U_c` and `χ = m̄ U_cm/U_c`
(generalising the Chapter 2 project's `hasFDerivAt_logMU` by the preference shock `ξ`). -/
theorem hasFDerivAt_logMU {Uc : ℝ × ℝ × ℝ → ℝ} {U' : ℝ × ℝ × ℝ →L[ℝ] ℝ} {Ybar mbar : ℝ}
    (hU : HasFDerivAt Uc U' (Ybar, mbar, 0)) (hpos : 0 < Uc (Ybar, mbar, 0)) :
    ∃ G' : ℝ × ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (logMU Uc Ybar mbar) G' 0 ∧
      ∀ v, G' v = -(-(U' (1, 0, 0)) * Ybar / Uc (Ybar, mbar, 0)) * v.1 +
        chi mbar (Uc (Ybar, mbar, 0)) (U' (0, 1, 0)) * v.2.1 +
        U' (0, 0, 1) / Uc (Ybar, mbar, 0) * v.2.2 := by
  let P1 : ℝ × ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
  let P2 : ℝ × ℝ × ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  let P3 : ℝ × ℝ × ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  have hY := (P1.hasFDerivAt (x := 0)).exp.const_mul Ybar
  have hM := (P2.hasFDerivAt (x := 0)).exp.const_mul mbar
  have hg := hY.prodMk (hM.prodMk (P3.hasFDerivAt (x := 0)))
  have hg0 : ((Ybar * Real.exp (P1 0), mbar * Real.exp (P2 0), P3 0) : ℝ × ℝ × ℝ) =
      (Ybar, mbar, 0) := by simp
  rw [← hg0] at hU
  have hc := hU.comp (0 : ℝ × ℝ × ℝ) hg
  have hne : (Uc ∘ fun x => (Ybar * Real.exp (P1 x), mbar * Real.exp (P2 x), P3 x)) 0 ≠ 0 := by
    simp only [Function.comp_apply]
    rw [hg0]
    exact hpos.ne'
  have hlog := (hc.log hne).sub_const (Real.log (Uc (Ybar, mbar, 0)))
  refine ⟨_, hlog, fun v => ?_⟩
  simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    smul_eq_mul]
  rw [clm3_apply]
  simp [P1, P2, P3, chi]
  field_simp

/-- Woodford (2003), App. A, §A.3, p. 634 (finite state space): if each `ε ↦ f ε ω` has
derivative `g ω` at `x`, then `ε ↦ E_t(f ε) ω` has derivative `E_t g ω` (restated from the
Chapter 2 project). -/
theorem hasDerivAt_E [Finite Ω] {f : ℝ → Ω → ℝ} {g : Ω → ℝ} {x : ℝ}
    (hf : ∀ ω, HasDerivAt (fun ε => f ε ω) (g ω) x) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => 𝔼.E t (f ε) ω) (𝔼.E t g ω) x := by
  have := Fintype.ofFinite Ω
  have hF : HasDerivAt f g x := hasDerivAt_pi.mpr hf
  have hL := (LinearMap.toContinuousLinearMap (𝔼.E t)).hasFDerivAt.comp_hasDerivAt x hF
  have := hasDerivAt_pi.mp hL ω
  simpa using this

/-- Woodford (2003), eqs. (3.4)–(3.5), p. 301 (finite state space): scale every deviation
`v_s` (here `(Ŷ_s, m̂_s, ξ_s)`) and the inflation path `π` by `ε`; for any log marginal
utility map `λ` with `λ(0) = 0` and derivative `Dλ` at `0`, the exact Euler map (3.4) in logs,
`ε ↦ −log E_t[exp(λ(ε v_{t+1}) − λ(ε v_t) − ε π_{t+1})]` (`euler_log_form`), has derivative
`E_t[Dλ v_t − Dλ v_{t+1} + π_{t+1}]` at `ε = 0`. -/
theorem euler_composite_deriv [Finite Ω] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {lam : V → ℝ} {Dlam : V →L[ℝ] ℝ} (hlam : HasFDerivAt lam Dlam 0) (hlam0 : lam 0 = 0)
    (v : ℕ → Ω → V) (π : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => -Real.log (𝔼.E t (fun ω' => Real.exp
      (lam (ε • v (t + 1) ω') - lam (ε • v t ω') - ε * π (t + 1) ω')) ω))
      (𝔼.E t (fun ω' => Dlam (v t ω') - Dlam (v (t + 1) ω') + π (t + 1) ω') ω) 0 := by
  have hdir : ∀ a : V, HasDerivAt (fun ε : ℝ => lam (ε • a)) (Dlam a) 0 := by
    intro a
    have hp : HasDerivAt (fun ε : ℝ => ε • a) a 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const a
    have he : (fun ε : ℝ => ε • a) 0 = 0 := by simp
    have hl : HasFDerivAt lam Dlam ((fun ε : ℝ => ε • a) 0) := by
      rw [he]; exact hlam
    exact hl.comp_hasDerivAt (0 : ℝ) hp
  have hpt : ∀ ω', HasDerivAt (fun ε => Real.exp (lam (ε • v (t + 1) ω') - lam (ε • v t ω') -
      ε * π (t + 1) ω')) (Dlam (v (t + 1) ω') - Dlam (v t ω') - π (t + 1) ω') 0 := by
    intro ω'
    have h := (HasDerivAt.sub (HasDerivAt.sub (hdir (v (t + 1) ω')) (hdir (v t ω')))
      (hasDerivAt_mul_const (π (t + 1) ω'))).exp
    simpa [hlam0] using h
  have hE := hasDerivAt_E 𝔼 hpt t ω
  have h1 : 𝔼.E t (fun ω' => Real.exp (lam ((0 : ℝ) • v (t + 1) ω') - lam ((0 : ℝ) • v t ω') -
      0 * π (t + 1) ω')) ω = 1 := by
    simp only [zero_smul, zero_mul, hlam0, sub_self, Real.exp_zero]
    rw [𝔼.const]
  have hlog := hE.log (by rw [h1]; exact one_ne_zero)
  rw [h1, div_one] at hlog
  convert hlog.neg using 1
  have hfun : (fun ω' => Dlam (v t ω') - Dlam (v (t + 1) ω') + π (t + 1) ω') =
      -(fun ω' => Dlam (v (t + 1) ω') - Dlam (v t ω') - π (t + 1) ω') := by
    funext ω'
    simp only [Pi.neg_apply]
    ring
  rw [hfun, map_neg]
  rfl

/-- Woodford (2003), eq. (3.5), p. 301: the log-linear Euler equation
`î_t = σ⁻¹[E_t(Ŷ_{t+1} − g_{t+1}) − (Ŷ_t − g_t)] − χ(E_t m̂_{t+1} − m̂_t) + E_t π_{t+1}`. -/
def IS35 (σinv χ : ℝ) (Y g mh π i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = σinv • (𝔼.E t (Y (t + 1) - g (t + 1)) - (Y t - g t)) -
    χ • (𝔼.E t (mh (t + 1)) - mh t) + 𝔼.E t (π (t + 1))

/-- Woodford (2003), eqs. (3.4)–(3.5), p. 301 (finite state space): with the marginal utility
`logMU` (derivative `−σ⁻¹ Ŷ + χ m̂ + g_ξ ξ`, `hasFDerivAt_logMU`) and `g_t = (g_ξ/σ⁻¹) ξ_t`, the
derivative of the exact Euler map (3.4) along the scaled deviations is
`E_t[σ⁻¹((Ŷ_{t+1} − g_{t+1}) − (Ŷ_t − g_t)) − χ(m̂_{t+1} − m̂_t) + π_{t+1}]`: the right-hand
side of (3.5) (`is35_of_deriv`). -/
theorem euler_deriv_35 [Finite Ω] {lam : ℝ × ℝ × ℝ → ℝ} {G' : ℝ × ℝ × ℝ →L[ℝ] ℝ}
    {σinv χ gξ : ℝ} (hσ : σinv ≠ 0) (hlam : HasFDerivAt lam G' 0) (hlam0 : lam 0 = 0)
    (hG : ∀ v, G' v = -σinv * v.1 + χ * v.2.1 + gξ * v.2.2) (Y mh ξ π : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) :
    HasDerivAt (fun ε => -Real.log (𝔼.E t (fun ω' => Real.exp
      (lam (ε • (Y (t + 1) ω', mh (t + 1) ω', ξ (t + 1) ω')) -
        lam (ε • (Y t ω', mh t ω', ξ t ω')) - ε * π (t + 1) ω')) ω))
      (𝔼.E t (fun ω' => σinv * ((Y (t + 1) ω' - gξ / σinv * ξ (t + 1) ω') -
        (Y t ω' - gξ / σinv * ξ t ω')) - χ * (mh (t + 1) ω' - mh t ω') + π (t + 1) ω') ω) 0 := by
  convert euler_composite_deriv 𝔼 hlam hlam0 (fun s ω' => (Y s ω', mh s ω', ξ s ω')) π t ω
    using 2
  funext ω'
  rw [hG, hG]
  field_simp
  ring

/-- Woodford (2003), eq. (3.5), p. 301: for adapted `Ŷ`, `g`, `m̂`, the derivative in
`euler_deriv_35` is exactly the right-hand side of (3.5), so the log-linear Euler equation
`î_t = [derivative]` is (3.5). -/
theorem is35_of_deriv {σinv χ : ℝ} {Y g mh π i : ℕ → Ω → ℝ} (hY : 𝔼.Adapted Y)
    (hg : 𝔼.Adapted g) (hm : 𝔼.Adapted mh)
    (hi : ∀ t, i t = 𝔼.E t (fun ω' => σinv * ((Y (t + 1) ω' - g (t + 1) ω') -
      (Y t ω' - g t ω')) - χ * (mh (t + 1) ω' - mh t ω') + π (t + 1) ω')) :
    IS35 𝔼 σinv χ Y g mh π i := by
  intro t
  rw [hi t]
  have h : (fun ω' => σinv * ((Y (t + 1) ω' - g (t + 1) ω') - (Y t ω' - g t ω')) -
      χ * (mh (t + 1) ω' - mh t ω') + π (t + 1) ω') =
      σinv • ((Y (t + 1) - g (t + 1)) - (Y t - g t)) - χ • (mh (t + 1) - mh t) + π (t + 1) := by
    funext ω'
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [h]
  simp only [map_add, map_sub, map_smul, hY t, hg t, hm t]

/-- Woodford (2003), (3.5), p. 301: the log-linear Euler equation in terms of the log marginal
utility, `î_t = λ̂_t − E_t λ̂_{t+1} + E_t π_{t+1}`, with `λ̂ = −σ⁻¹(Ŷ − g) + χ m̂`, is (3.5)
(restated from the Chapter 2 project's (3.11)). -/
theorem is35_of_lambda {σinv χ : ℝ} {Y g mh lam π i : ℕ → Ω → ℝ}
    (hlam : ∀ t, lam t = -σinv • (Y t - g t) + χ • mh t)
    (heul : ∀ t, i t = lam t - 𝔼.E t (lam (t + 1)) + 𝔼.E t (π (t + 1))) :
    IS35 𝔼 σinv χ Y g mh π i := by
  intro t
  rw [heul t, hlam t, hlam (t + 1)]
  funext ω
  simp only [map_add, map_sub, map_smul, map_neg, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, Pi.neg_apply, smul_eq_mul, neg_smul]
  ring

/-- Woodford (2003), (3.6), p. 301: (3.5) is the one-step form
`X_t = E_t X_{t+1} − σ(î_t − E_t π_{t+1})` of `X = Ŷ − g − χσ m̂` (`σ⁻¹ ≠ 0`). -/
theorem is35_iff_X {σinv χ : ℝ} (hσ : σinv ≠ 0) {Y g mh π i : ℕ → Ω → ℝ} :
    IS35 𝔼 σinv χ Y g mh π i ↔ ∀ t, Y t - g t - (χ * σinv⁻¹) • mh t =
      𝔼.E t (Y (t + 1) - g (t + 1) - (χ * σinv⁻¹) • mh (t + 1)) -
        σinv⁻¹ • (i t - 𝔼.E t (π (t + 1))) := by
  unfold IS35
  refine forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [map_sub, map_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h
    rw [h]
    field_simp
    ring
  · intro h
    have h' : σinv * (Y t ω - g t ω - χ * σinv⁻¹ * mh t ω) = σinv *
        (𝔼.E t (Y (t + 1)) ω - 𝔼.E t (g (t + 1)) ω - χ * σinv⁻¹ * 𝔼.E t (mh (t + 1)) ω -
          σinv⁻¹ * (i t ω - 𝔼.E t (π (t + 1)) ω)) := by rw [h]
    field_simp at h'
    linear_combination h'

/-- Woodford (2003), eq. (3.6), p. 301: solving (3.5) forward. For an adapted rate `î`, if the
long-run forecasts converge, `E_t Ŷ_{t+k} → Ŷ_∞`, `E_t g_{t+k} → 0`, `E_t m̂_{t+k} → 0`, then the
partial sums of `∑_j E_t[î_{t+j} − π_{t+j+1}]` converge, to a limit `S` with
`Ŷ_t = Ŷ_∞ + g_t + χσ m̂_t − σ S` (an honest limit of partial sums, not assumed summable). -/
theorem is36 {σinv χ : ℝ} (hσ : σinv ≠ 0) {Y g mh π i : ℕ → Ω → ℝ}
    (hi : 𝔼.Adapted i)
    (h35 : IS35 𝔼 σinv χ Y g mh π i) (t : ℕ) (ω : Ω) {Yinf : ℝ}
    (hYl : Tendsto (fun k => 𝔼.E t (Y (t + k)) ω) atTop (𝓝 Yinf))
    (hgl : Tendsto (fun k => 𝔼.E t (g (t + k)) ω) atTop (𝓝 0))
    (hml : Tendsto (fun k => 𝔼.E t (mh (t + k)) ω) atTop (𝓝 0)) :
    ∃ S, Tendsto (fun k => ∑ j ∈ Finset.range k,
        (𝔼.E t (i (t + j)) ω - 𝔼.E t (π (t + j + 1)) ω)) atTop (𝓝 S) ∧
      Y t ω = Yinf + g t ω + χ * σinv⁻¹ * mh t ω - σinv⁻¹ * S := by
  set X : ℕ → Ω → ℝ := fun s => Y s - g s - (χ * σinv⁻¹) • mh s with hX
  set u : ℕ → Ω → ℝ := fun s => -(σinv⁻¹ • (i s - 𝔼.E s (π (s + 1)))) with hu
  have hua : 𝔼.Adapted u := by
    intro s
    simp only [hu, map_neg, map_smul, map_sub, hi s, 𝔼.E_E_self]
  have hsol : ForwardSolution.Solves 𝔼 1 u X := by
    intro s
    have := (is35_iff_X 𝔼 hσ).mp h35 s
    simp only [hX, hu, one_smul]
    rw [this]
    abel
  have hit := ForwardSolution.iterate_A15 𝔼 hua hsol t
  have hterm : ∀ j, (𝔼.E t (u (t + j))) ω =
      -σinv⁻¹ * (𝔼.E t (i (t + j)) ω - 𝔼.E t (π (t + j + 1)) ω) := by
    intro j
    simp only [hu, map_neg, map_smul, map_sub, 𝔼.tower (Nat.le_add_right t j), Pi.neg_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hXl : Tendsto (fun k => 𝔼.E t (X (t + k)) ω) atTop (𝓝 (Yinf - 0 - χ * σinv⁻¹ * 0)) := by
    have : (fun k => 𝔼.E t (X (t + k)) ω) = fun k => 𝔼.E t (Y (t + k)) ω -
        𝔼.E t (g (t + k)) ω - χ * σinv⁻¹ * 𝔼.E t (mh (t + k)) ω := by
      funext k
      simp only [hX, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [this]
    exact (hYl.sub hgl).sub (hml.const_mul _)
  have hk : ∀ k, ∑ j ∈ Finset.range k, (𝔼.E t (i (t + j)) ω - 𝔼.E t (π (t + j + 1)) ω) =
      σinv * (𝔼.E t (X (t + k)) ω - X t ω) := by
    intro k
    have h := congrFun (hit k) ω
    simp only [one_pow, one_smul, Pi.add_apply, Finset.sum_apply] at h
    simp_rw [hterm] at h
    rw [← Finset.mul_sum] at h
    rw [h]
    field_simp
    ring
  refine ⟨σinv * (Yinf - X t ω), ?_, ?_⟩
  · simp_rw [hk]
    have := (hXl.sub_const (X t ω)).const_mul σinv
    simpa using this
  · simp only [hX, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

/-! ### (3.7)–(3.8): eliminating real balances -/

/-- Woodford (2003), eq. (3.8), p. 302: the composite disturbance
`v_t = −σ⁻¹(E_t g_{t+1} − g_t) − χ(E_t εᵐ_{t+1} − εᵐ_t)`. -/
def v38 (σinv χ : ℝ) (g e : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => -(σinv • (𝔼.E t (g (t + 1)) - g t)) - χ • (𝔼.E t (e (t + 1)) - e t)

/-- Woodford (2003), eq. (3.7), p. 301:
`(1 + η_iχ) î_t = (σ⁻¹ − η_yχ)(E_t Ŷ_{t+1} − Ŷ_t) + E_t π_{t+1} + η_iχ E_t î_{t+1}
− η_iχ(E_t îᵐ_{t+1} − îᵐ_t) + v_t`. -/
def IS37 (σinv ηy ηi χ : ℝ) (Y π i im v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (1 + ηi * χ) • i t = (σinv - ηy * χ) • (𝔼.E t (Y (t + 1)) - Y t) +
    𝔼.E t (π (t + 1)) + (ηi * χ) • 𝔼.E t (i (t + 1)) -
      (ηi * χ) • (𝔼.E t (im (t + 1)) - im t) + v t

/-- Woodford (2003), eqs. (3.3), (3.5), (3.7)–(3.8), pp. 296–302: given the LM relation (3.3),
the Euler equation (3.5) is equivalent to (3.7) with the disturbance (3.8). -/
theorem is35_iff_37 {σinv ηy ηi χ : ℝ} {Y g e mh π i im : ℕ → Ω → ℝ}
    (hLM : LM ηy ηi Y i im e mh) :
    IS35 𝔼 σinv χ Y g mh π i ↔ IS37 𝔼 σinv ηy ηi χ Y π i im (v38 𝔼 σinv χ g e) := by
  unfold IS35 IS37
  refine forall_congr' fun t => ?_
  rw [hLM (t + 1), hLM t, funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [v38, map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  constructor
  · intro h; linear_combination (1 + ηi * χ) * h - ηi * χ * h
  · intro h; linear_combination h

/-- Woodford (2003), fn. 62, p. 302 (corrected): with a constant interest differential,
`îᵐ = î`, (3.7) is exactly the form (1.7) of the Euler equation,
`î_t = σ̃⁻¹[E_t(Ŷ_{t+1} − g̃_{t+1}) − (Ŷ_t − g̃_t)] + E_t π_{t+1}`, with
`σ̃⁻¹ = σ⁻¹ − η_yχ` (as printed) but `g̃ = (σ⁻¹ g + χ εᵐ)/(σ⁻¹ − η_yχ)`; the footnote's
`g̃ = g + σχεᵐ` is correct only when `η_yχ = 0` (`fn62_printed_fails`). This `g̃` is the one
for which `−σ̃⁻¹(Ŷ − g̃)` is the log marginal utility of income under a constant differential,
as the footnote intends (`fn62_marginalUtility`). -/
theorem fn62_constSpread {σinv ηy ηi χ : ℝ} (hs : σinv - ηy * χ ≠ 0)
    {Y g e π i : ℕ → Ω → ℝ} :
    IS37 𝔼 σinv ηy ηi χ Y π i i (v38 𝔼 σinv χ g e) ↔
      ∀ t, i t = (σinv - ηy * χ) • (𝔼.E t (Y (t + 1) -
        (σinv - ηy * χ)⁻¹ • (σinv • g (t + 1) + χ • e (t + 1))) -
        (Y t - (σinv - ηy * χ)⁻¹ • (σinv • g t + χ • e t))) + 𝔼.E t (π (t + 1)) := by
  unfold IS37
  refine forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [v38, map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    have hs' : (σinv - ηy * χ) * (σinv - ηy * χ)⁻¹ = 1 := mul_inv_cancel₀ hs
    linear_combination h - (σinv * (𝔼.E t (g (t + 1)) ω - g t ω) +
      χ * (𝔼.E t (e (t + 1)) ω - e t ω)) * hs'

/-- Woodford (2003), fn. 62, p. 302: under a constant differential the LM relation gives
`m̂ = η_y Ŷ + εᵐ`, and the log marginal utility of income `−σ⁻¹(Ŷ − g) + χ m̂` equals
`−σ̃⁻¹(Ŷ − g̃)` with `σ̃⁻¹ = σ⁻¹ − η_yχ` and `g̃ = (σ⁻¹ g + χ εᵐ)/(σ⁻¹ − η_yχ)`. -/
theorem fn62_marginalUtility {σinv ηy χ Y g e : ℝ} (hs : σinv - ηy * χ ≠ 0) :
    -σinv * (Y - g) + χ * (ηy * Y + e) =
      -(σinv - ηy * χ) * (Y - (σinv * g + χ * e) / (σinv - ηy * χ)) := by
  have h := mul_div_cancel₀ (σinv * g + χ * e) hs
  linear_combination -h

/-- Woodford (2003), fn. 62, p. 302 (counterexample): with `σ = 1`, `η_y = η_i = 1`,
`χ = 1/2`, no money-demand shock, `Ŷ ≡ 0`, `π ≡ 0`, a one-period shock `g_0 = 1` and the
constant-differential policy `îᵐ = î` with `î_0 = 1`, `î_t = 0` for `t ≥ 1`, relation (3.7)
holds under perfect foresight, but the footnote's form (1.7) with `σ⁻¹ − η_yχ` and
`g + σχεᵐ = g` fails at `t = 0`. -/
theorem fn62_printed_fails :
    let g : ℕ → Unit → ℝ := fun t _ => if t = 0 then 1 else 0
    let i : ℕ → Unit → ℝ := fun t _ => if t = 0 then 1 else 0
    IS37 perfectForesight 1 1 1 (1 / 2) 0 0 i i (v38 perfectForesight 1 (1 / 2) g 0) ∧
      ¬ ∀ t, i t = (1 - 1 * (1 / 2 : ℝ)) • (perfectForesight.E t ((0 : ℕ → Unit → ℝ) (t + 1) -
        (g (t + 1) + (1 : ℝ)⁻¹ • (1 / 2 : ℝ) • (0 : ℕ → Unit → ℝ) (t + 1))) -
        ((0 : ℕ → Unit → ℝ) t - (g t + (1 : ℝ)⁻¹ • (1 / 2 : ℝ) • (0 : ℕ → Unit → ℝ) t))) +
        perfectForesight.E t ((0 : ℕ → Unit → ℝ) (t + 1)) := by
  intro g i
  refine ⟨fun t => ?_, fun h => ?_⟩
  · funext u
    simp only [v38, perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul, g, i]
    rcases t with _ | t
    · simp; norm_num
    · simp
  · have h0 := congrFun (h 0) ()
    simp [perfectForesight, g, i] at h0
    norm_num at h0

/-! ### (3.9)–(3.10): the natural rate of interest and the gap IS relation -/

/-- Woodford (2003), eq. (3.9), p. 302: the natural rate of interest under a constant
differential, `r̂ⁿ_t = (σ⁻¹ − η_yχ)(E_t Ŷⁿ_{t+1} − Ŷⁿ_t) − σ⁻¹(E_t g_{t+1} − g_t)
− χ(E_t εᵐ_{t+1} − εᵐ_t)`. -/
def rn39 (σinv ηy χ : ℝ) (Yn g e : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (σinv - ηy * χ) • (𝔼.E t (Yn (t + 1)) - Yn t) - σinv • (𝔼.E t (g (t + 1)) - g t) -
    χ • (𝔼.E t (e (t + 1)) - e t)

/-- Woodford (2003), (3.9), p. 302: if (3.7) holds under flexible prices with a constant
differential (`Ŷ = Ŷⁿ`, `îᵐ = î`), the real rate `î_t − E_t π_{t+1}` is `r̂ⁿ_t` of (3.9). -/
theorem natural_rate_39 {σinv ηy ηi χ : ℝ} {Yn g e π i : ℕ → Ω → ℝ}
    (h : IS37 𝔼 σinv ηy ηi χ Yn π i i (v38 𝔼 σinv χ g e)) (t : ℕ) :
    i t - 𝔼.E t (π (t + 1)) = rn39 𝔼 σinv ηy χ Yn g e t := by
  have h1 := h t
  funext ω
  have h2 := congrFun h1 ω
  simp only [v38, rn39, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
    smul_eq_mul] at h2 ⊢
  linear_combination h2

/-- Woodford (2003), p. 302: with `χ = 0`, (3.9) is the earlier definition (1.15). -/
theorem rn39_chi_zero {σinv ηy : ℝ} (Yn g e : ℕ → Ω → ℝ) :
    rn39 𝔼 σinv ηy 0 Yn g e = rnHat 𝔼 σinv⁻¹ g Yn := by
  funext t ω
  simp only [rn39, rnHat, inv_inv, map_sub, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), eq. (3.10), p. 302: the gap IS relation
`(1 − ση_yχ) x_t = (1 − ση_yχ) E_t x_{t+1} − σ(î_t − E_t π_{t+1} − r̂ⁿ_t)
+ ση_iχ[E_t(î_{t+1} − îᵐ_{t+1}) − (î_t − îᵐ_t)]` (`σ = σinv⁻¹`). -/
def IS310 (σinv ηy ηi χ : ℝ) (x π i im rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (1 - σinv⁻¹ * ηy * χ) • x t = (1 - σinv⁻¹ * ηy * χ) • 𝔼.E t (x (t + 1)) -
    σinv⁻¹ • (i t - 𝔼.E t (π (t + 1)) - rn t) +
      (σinv⁻¹ * ηi * χ) • ((𝔼.E t (i (t + 1)) - 𝔼.E t (im (t + 1))) - (i t - im t))

/-- Woodford (2003), (3.7), (3.9)–(3.10), p. 302: with the output gap `x = Ŷ − Ŷⁿ` and the
natural rate (3.9), relation (3.7) is equivalent to (3.10) (`σ⁻¹ ≠ 0`). -/
theorem is37_iff_310 {σinv ηy ηi χ : ℝ} (hσ : σinv ≠ 0) {Y Yn g e π i im : ℕ → Ω → ℝ} :
    IS37 𝔼 σinv ηy ηi χ Y π i im (v38 𝔼 σinv χ g e) ↔
      IS310 𝔼 σinv ηy ηi χ (fun t => Y t - Yn t) π i im (rn39 𝔼 σinv ηy χ Yn g e) := by
  unfold IS37 IS310
  refine forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [v38, rn39, map_sub, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    field_simp at h
    linear_combination h

/-! ### (3.11)–(3.14): marginal cost and the aggregate-supply relation -/

/-- Woodford (2003), p. 303: the log real marginal disutility of output supply
`log Ψ(Ȳ e^{ŷ}, ζ) − log Ψ(Ȳ, 0)`, with `Ψ = v_h/(A f')` evaluated at the labour needed for
output `y` and supply disturbances `ζ`. -/
noncomputable def logSupply (Psi : ℝ × ℝ → ℝ) (Ybar : ℝ) (x : ℝ × ℝ) : ℝ :=
  Real.log (Psi (Ybar * Real.exp x.1, x.2)) - Real.log (Psi (Ybar, 0))

/-- Woodford (2003), p. 303 (exact derivative): the derivative of `logSupply` at zero is
`(ŷ, ζ) ↦ ω ŷ + ψ ζ` with `ω = Ψ_y Ȳ/Ψ` (the elasticity of Chapter 3) and `ψ = Ψ_ζ/Ψ`. -/
theorem hasFDerivAt_logSupply {Psi : ℝ × ℝ → ℝ} {Ψ' : ℝ × ℝ →L[ℝ] ℝ} {Ybar : ℝ}
    (hΨ : HasFDerivAt Psi Ψ' (Ybar, 0)) (hpos : 0 < Psi (Ybar, 0)) :
    ∃ G' : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (logSupply Psi Ybar) G' 0 ∧
      ∀ v, G' v = Ψ' (1, 0) * Ybar / Psi (Ybar, 0) * v.1 + Ψ' (0, 1) / Psi (Ybar, 0) * v.2 := by
  let P1 : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let P2 : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have hY := (P1.hasFDerivAt (x := 0)).exp.const_mul Ybar
  have hg := hY.prodMk (P2.hasFDerivAt (x := 0))
  have hg0 : ((Ybar * Real.exp (P1 0), P2 0) : ℝ × ℝ) = (Ybar, 0) := by simp
  rw [← hg0] at hΨ
  have hc := hΨ.comp (0 : ℝ × ℝ) hg
  have hne : (Psi ∘ fun x => (Ybar * Real.exp (P1 x), P2 x)) 0 ≠ 0 := by
    simp only [Function.comp_apply]
    rw [hg0]
    exact hpos.ne'
  have hlog := (hc.log hne).sub_const (Real.log (Psi (Ybar, 0)))
  refine ⟨_, hlog, fun v => ?_⟩
  simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    smul_eq_mul]
  rw [clm2_apply]
  simp [P1, P2]
  field_simp

/-- Woodford (2003), p. 303: the log real marginal cost of supplying good `i`,
`log s(i) = log Ψ(y(i), ζ) − log U_c(Y, m; ξ)` (from the labour supply
`w(i) = v_h/U_c(C, m; ξ)`), in deviations `((ŷ(i), ζ), (Ŷ, m̂, ξ))`. -/
noncomputable def logMC (Psi : ℝ × ℝ → ℝ) (Uc : ℝ × ℝ × ℝ → ℝ) (Ybar mbar : ℝ)
    (p : (ℝ × ℝ) × (ℝ × ℝ × ℝ)) : ℝ :=
  logSupply Psi Ybar p.1 - logMU Uc Ybar mbar p.2

/-- Woodford (2003), p. 303 (exact derivative): the log real marginal cost has derivative
`ω ŷ(i) + ψ ζ − (−σ⁻¹ Ŷ + χ m̂ + g_ξ ξ)` at the steady state, which is
`ω(ŷ(i) − q) + σ⁻¹(Ŷ − g) − χ m̂` with `q = −ψ ζ/ω`, `g = g_ξ ξ/σ⁻¹` (`mc_deriv_form`). -/
theorem hasFDerivAt_logMC {Psi : ℝ × ℝ → ℝ} {Ψ' : ℝ × ℝ →L[ℝ] ℝ} {Uc : ℝ × ℝ × ℝ → ℝ}
    {U' : ℝ × ℝ × ℝ →L[ℝ] ℝ} {Ybar mbar : ℝ} (hΨ : HasFDerivAt Psi Ψ' (Ybar, 0))
    (hΨpos : 0 < Psi (Ybar, 0)) (hU : HasFDerivAt Uc U' (Ybar, mbar, 0))
    (hUpos : 0 < Uc (Ybar, mbar, 0)) :
    ∃ D : (ℝ × ℝ) × (ℝ × ℝ × ℝ) →L[ℝ] ℝ, HasFDerivAt (logMC Psi Uc Ybar mbar) D 0 ∧
      ∀ p, D p = Ψ' (1, 0) * Ybar / Psi (Ybar, 0) * p.1.1 + Ψ' (0, 1) / Psi (Ybar, 0) * p.1.2 -
        (-(-(U' (1, 0, 0)) * Ybar / Uc (Ybar, mbar, 0)) * p.2.1 +
          chi mbar (Uc (Ybar, mbar, 0)) (U' (0, 1, 0)) * p.2.2.1 +
          U' (0, 0, 1) / Uc (Ybar, mbar, 0) * p.2.2.2) := by
  obtain ⟨G1, hG1, hG1v⟩ := hasFDerivAt_logSupply hΨ hΨpos
  obtain ⟨G2, hG2, hG2v⟩ := hasFDerivAt_logMU hU hUpos
  have h1 : HasFDerivAt (fun p : (ℝ × ℝ) × (ℝ × ℝ × ℝ) => logSupply Psi Ybar p.1)
      (G1.comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ × ℝ))) 0 :=
    (show HasFDerivAt (logSupply Psi Ybar) G1 ((0 : (ℝ × ℝ) × (ℝ × ℝ × ℝ)).1) from hG1).comp
      (0 : (ℝ × ℝ) × (ℝ × ℝ × ℝ)) hasFDerivAt_fst
  have h2 : HasFDerivAt (fun p : (ℝ × ℝ) × (ℝ × ℝ × ℝ) => logMU Uc Ybar mbar p.2)
      (G2.comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ × ℝ))) 0 :=
    (show HasFDerivAt (logMU Uc Ybar mbar) G2 ((0 : (ℝ × ℝ) × (ℝ × ℝ × ℝ)).2) from hG2).comp
      (0 : (ℝ × ℝ) × (ℝ × ℝ × ℝ)) hasFDerivAt_snd
  refine ⟨_, h1.sub h2, fun p => ?_⟩
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', hG1v, hG2v]

/-- Woodford (2003), p. 303: the derivative in `hasFDerivAt_logMC` in the book's notation,
`ω ŷ + ψ ζ − (−σ⁻¹ Ŷ + χ m̂ + g_ξ ξ) = ω(ŷ − q) + σ⁻¹(Ŷ − g) − χ m̂` with `q = −ψ ζ/ω` and
`g = g_ξ ξ/σ⁻¹` (`ω, σ⁻¹ ≠ 0`). -/
theorem mc_deriv_form {ω ψ σinv χ gξ y ζ Y mh ξ : ℝ} (hω : ω ≠ 0) (hσ : σinv ≠ 0) :
    ω * y + ψ * ζ - (-σinv * Y + χ * mh + gξ * ξ) =
      ω * (y - (-ψ * ζ / ω)) + σinv * (Y - gξ * ξ / σinv) - χ * mh := by
  field_simp
  ring

/-- Woodford (2003), p. 303: average real marginal cost (each `ŷ(i)` replaced by its average
`Ŷ`), `ŝ = ω(Ŷ − q) + σ⁻¹(Ŷ − g) − χ m̂`. -/
def mcAvg (ω σinv χ Y q g mh : ℝ) : ℝ := ω * (Y - q) + σinv * (Y - g) - χ * mh

/-- Woodford (2003), eq. (3.12), p. 303 (corrected): the elasticity of average marginal cost
with respect to output, `ε_mc = ω + σ⁻¹ − η_yχ` (the book prints `η_i` for `η_y`). -/
def epsMC (ω σinv ηy χ : ℝ) : ℝ := ω + σinv - ηy * χ

/-- Woodford (2003), eq. (3.13), p. 303: the natural rate of output
`Ŷⁿ = (ω q + σ⁻¹ g + χ εᵐ)/ε_mc`. -/
noncomputable def ynat313 (ω σinv χ q g e εmc : ℝ) : ℝ := (ω * q + σinv * g + χ * e) / εmc

/-- Woodford (2003), eqs. (3.11)–(3.13), p. 303 (corrected): substituting (3.3) for `m̂`,
average marginal cost is `ŝ = ε_mc(Ŷ − Ŷⁿ) + η_iχ(î − îᵐ)` with `ε_mc = ω + σ⁻¹ − η_yχ ≠ 0`. -/
theorem mc311 {ω σinv ηy ηi χ Y q g e i im : ℝ} (hε : epsMC ω σinv ηy χ ≠ 0) :
    mcAvg ω σinv χ Y q g (ηy * Y - ηi * (i - im) + e) =
      epsMC ω σinv ηy χ * (Y - ynat313 ω σinv χ q g e (epsMC ω σinv ηy χ)) +
        ηi * χ * (i - im) := by
  unfold ynat313
  rw [mul_sub (epsMC ω σinv ηy χ) Y, mul_div_cancel₀ _ hε]
  unfold mcAvg epsMC
  ring

/-- Woodford (2003), p. 303: (3.11) in the form `ŝ = ε_mc[x + ϕ(î − îᵐ)]`, with the gap
`x = Ŷ − Ŷⁿ` and `ϕ = η_iχ/ε_mc`. -/
theorem mc311_phi {ω σinv ηy ηi χ Y q g e i im : ℝ} (hε : epsMC ω σinv ηy χ ≠ 0) :
    mcAvg ω σinv χ Y q g (ηy * Y - ηi * (i - im) + e) =
      epsMC ω σinv ηy χ * ((Y - ynat313 ω σinv χ q g e (epsMC ω σinv ηy χ)) +
        ηi * χ / epsMC ω σinv ηy χ * (i - im)) := by
  rw [mc311 hε, mul_add, ← mul_assoc, mul_div_cancel₀ _ hε]

/-- Woodford (2003), (3.13), p. 303: under flexible prices (`ŝ = 0`: every firm at its desired
markup) and a constant differential (`î = îᵐ`), output is `Ŷⁿ` of (3.13). -/
theorem ynat313_flex {ω σinv ηy ηi χ Y q g e i : ℝ} (hε : epsMC ω σinv ηy χ ≠ 0)
    (hs : mcAvg ω σinv χ Y q g (ηy * Y - ηi * (i - i) + e) = 0) :
    Y = ynat313 ω σinv χ q g e (epsMC ω σinv ηy χ) := by
  rw [mc311 hε, sub_self, mul_zero, add_zero] at hs
  rcases mul_eq_zero.mp hs with h | h
  · exact absurd h hε
  · linarith

/-- Woodford (2003), p. 303: with `χ = 0`, (3.13) is the earlier formula (2.2). -/
theorem ynat313_chi_zero {ω σinv ηy q g e : ℝ} :
    ynat313 ω σinv 0 q g e (epsMC ω σinv ηy 0) = ynLin σinv⁻¹ ω g q := by
  unfold ynat313 epsMC ynLin
  simp only [inv_inv]
  ring_nf

/-- Woodford (2003), eq. (3.12), p. 303 (**error E10**): the printed elasticity
`ε'_mc = ω + σ⁻¹ − η_iχ` makes (3.11) (with (3.13) built on `ε'_mc`) an identity in all the
variables only if `η_iχ = η_yχ`, i.e. only when `χ = 0` or `η_i = η_y`. -/
theorem printed312_iff {ω σinv ηy ηi χ : ℝ} (hε' : ω + σinv - ηi * χ ≠ 0) :
    (∀ Y q g e i im : ℝ, mcAvg ω σinv χ Y q g (ηy * Y - ηi * (i - im) + e) =
      (ω + σinv - ηi * χ) * (Y - ynat313 ω σinv χ q g e (ω + σinv - ηi * χ)) +
        ηi * χ * (i - im)) ↔ ηi * χ = ηy * χ := by
  constructor
  · intro h
    have h1 := h 1 0 0 0 0 0
    simp only [mcAvg, ynat313, mul_zero, add_zero, zero_div, sub_zero, mul_one, sub_self] at h1
    linarith
  · intro hc Y q g e i im
    have he : ω + σinv - ηi * χ = epsMC ω σinv ηy χ := by unfold epsMC; rw [hc]
    rw [he] at hε' ⊢
    exact mc311 hε'

/-- Woodford (2003), (3.12), pp. 303–306 (**error E10**, the book's own calibration): with
`ω = 0.47`, `σ⁻¹ = 0.16` (Table 5.1), `η_y = 1`, `η_i = 28`, `χ = 0.02` (p. 306) the correct
elasticity is `ε_mc = 0.61`, the printed one `0.07`, and the printed (3.11)–(3.13) fail. -/
theorem printed312_fails_calibration :
    epsMC 0.47 0.16 1 0.02 = (0.61 : ℝ) ∧ (0.47 + 0.16 - 28 * 0.02 : ℝ) = 0.07 ∧
      ¬ (∀ Y q g e i im : ℝ, mcAvg 0.47 0.16 0.02 Y q g (1 * Y - 28 * (i - im) + e) =
        (0.47 + 0.16 - 28 * 0.02) * (Y - ynat313 0.47 0.16 0.02 q g e (0.47 + 0.16 - 28 * 0.02)) +
          28 * 0.02 * (i - im)) := by
  refine ⟨by unfold epsMC; norm_num, by norm_num, fun h => ?_⟩
  have := (printed312_iff (ω := 0.47) (σinv := 0.16) (ηy := 1) (ηi := 28) (χ := 0.02)
    (by norm_num)).mp h
  norm_num at this

/-- Woodford (2003), p. 304: under `η_y, η_i > 0` and the bounds `0 ≤ χ < η_y⁻¹(ω + σ⁻¹)`,
`ε_mc > 0` and `ϕ = η_iχ/ε_mc ≥ 0`, with `ϕ > 0` exactly when `χ > 0` (the book's "both
positive" needs `χ > 0` for `ϕ`). -/
theorem bounds_pos {ω σinv ηy ηi χ : ℝ} (hηy : 0 < ηy) (hηi : 0 < ηi) (hχ0 : 0 ≤ χ)
    (hχ : χ < ηy⁻¹ * (ω + σinv)) :
    0 < epsMC ω σinv ηy χ ∧ 0 ≤ ηi * χ / epsMC ω σinv ηy χ ∧
      (0 < ηi * χ / epsMC ω σinv ηy χ ↔ 0 < χ) := by
  have hε : 0 < epsMC ω σinv ηy χ := by
    unfold epsMC
    have := mul_lt_mul_of_pos_left hχ hηy
    rw [← mul_assoc, mul_inv_cancel₀ hηy.ne', one_mul] at this
    linarith
  refine ⟨hε, div_nonneg (mul_nonneg hηi.le hχ0) hε.le, ?_⟩
  constructor
  · intro h
    rcases hχ0.lt_or_eq with h1 | h1
    · exact h1
    · rw [← h1, mul_zero, zero_div] at h; exact absurd h (lt_irrefl 0)
  · intro h
    exact div_pos (mul_pos hηi h) hε

/-- Woodford (2003), p. 304 (supporting E10): the bound `χ < η_y⁻¹(ω + σ⁻¹)` does not make the
printed `ω + σ⁻¹ − η_iχ` positive: `ω + σ⁻¹ = 0.63`, `η_y = 1`, `η_i = 28`, `χ = 0.1`. -/
theorem printed312_not_pos :
    (0 : ℝ) ≤ 0.1 ∧ (0.1 : ℝ) < 1⁻¹ * (0.47 + 0.16) ∧ (0.47 + 0.16 - 28 * 0.1 : ℝ) < 0 := by
  norm_num

/-- Woodford (2003), eq. (3.14), p. 304: `π_t = κ[x_t + ϕ(î_t − îᵐ_t)] + β E_t π_{t+1}`. -/
def AS314 (κ ϕ β : ℝ) (x π i im : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t = κ • (x t + ϕ • (i t - im t)) + β • 𝔼.E t (π (t + 1))

/-- Woodford (2003), p. 304: `κ = [(1 − α)(1 − αβ)/α] ε_mc/(1 + ωθ)`. -/
noncomputable def kappa314 (α β ω θ εmc : ℝ) : ℝ := (1 - α) * (1 - α * β) / α * (εmc / (1 + ω * θ))

/-- Woodford (2003), (3.14), p. 304: the Calvo relation of Chapter 3 in terms of average
marginal cost, `π_t = ξ ŝ_t + β E_t π_{t+1}` with `ξ = (1 − α)(1 − αβ)/(α(1 + ωθ))`, together
with `ŝ = ε_mc[x + ϕ(î − îᵐ)]` (`mc311_phi`), gives (3.14) with `κ = ξ ε_mc`. -/
theorem as314_of_mc {α β ω θ εmc ϕ : ℝ} {x π i im s : ℕ → Ω → ℝ}
    (hNK : ∀ t, π t = ((1 - α) * (1 - α * β) / α / (1 + ω * θ)) • s t + β • 𝔼.E t (π (t + 1)))
    (hs : ∀ t, s t = εmc • (x t + ϕ • (i t - im t))) :
    AS314 𝔼 (kappa314 α β ω θ εmc) ϕ β x π i im := by
  intro t
  rw [hNK t, hs t, smul_smul]
  congr 2
  unfold kappa314
  ring

/-- Woodford (2003), p. 304: `κ > 0` for `0 < α < 1`, `β < 1`, `ωθ ≥ 0` and `ε_mc > 0`. -/
theorem kappa314_pos {α β ω θ εmc : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ1 : β < 1)
    (hωθ : 0 ≤ ω * θ) (hε : 0 < εmc) : 0 < kappa314 α β ω θ εmc := by
  unfold kappa314
  have h1 : 0 < 1 - α * β := by nlinarith
  have h2 : 0 < 1 - α := by linarith
  positivity

/-! ### Constant spread: reduction to the basic model (p. 304–305) -/

/-- Woodford (2003), pp. 304–305: with a constant differential (`îᵐ = î`), the gap IS
relation (3.10) is exactly (1.12) with interest sensitivity `σ̃ = (σ⁻¹ − η_yχ)⁻¹` (the text's
"IS relation (3.4)" on p. 305 must be (3.10): (3.4) is the nonlinear Euler equation). -/
theorem is310_constSpread {σinv ηy ηi χ : ℝ} (hσ : σinv ≠ 0) (hs : σinv - ηy * χ ≠ 0)
    {x π i rn : ℕ → Ω → ℝ} :
    IS310 𝔼 σinv ηy ηi χ x π i i rn ↔ IS112 𝔼 (σinv - ηy * χ)⁻¹ x i π rn := by
  unfold IS310 IS112
  refine forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_self, Pi.zero_apply,
    mul_zero, add_zero]
  have hk : 1 - σinv⁻¹ * ηy * χ = σinv⁻¹ * (σinv - ηy * χ) := by field_simp
  rw [hk]
  constructor
  · intro h
    field_simp
    field_simp at h
    linear_combination h
  · intro h
    rw [h]
    field_simp

/-- Woodford (2003), p. 304: with a constant differential (`îᵐ = î`), (3.14) is exactly
the New Keynesian Phillips curve (1.10)/(1.13). -/
theorem as314_constSpread {κ ϕ β : ℝ} {x π i : ℕ → Ω → ℝ} :
    AS314 𝔼 κ ϕ β x π i i ↔ NKPCurve 𝔼 β κ π x := by
  unfold AS314 NKPCurve
  refine forall_congr' fun t => ?_
  rw [sub_self, smul_zero, add_zero]

/-- Woodford (2003), p. 305: `σ̃ = (σ⁻¹ − η_yχ)⁻¹ = σ/(1 − ση_yχ)`, and for `σ, η_y > 0` it is
positive iff `χ < (η_yσ)⁻¹`, "the empirically realistic case". -/
theorem sigmaTilde {σ ηy χ : ℝ} (hσ : 0 < σ) (hηy : 0 < ηy) :
    (σ⁻¹ - ηy * χ)⁻¹ = σ / (1 - σ * ηy * χ) ∧ (0 < (σ⁻¹ - ηy * χ)⁻¹ ↔ χ < (ηy * σ)⁻¹) := by
  constructor
  · have h : 1 - σ * ηy * χ = σ * (σ⁻¹ - ηy * χ) := by field_simp
    rw [h, div_mul_cancel_left₀ hσ.ne']
  · rw [inv_pos, sub_pos, show (ηy * σ)⁻¹ = σ⁻¹ / ηy by rw [mul_inv, div_eq_mul_inv, mul_comm],
      lt_div_iff₀ hηy, mul_comm χ ηy]

/-! ### Calibration (pp. 304–311) and footnote 71 -/

/-- Woodford (2003), p. 306 and fn. 69: with `χ = 0.02`, `η_i = 28` (quarters) and
`ε_mc = 0.63`, `ϕ = (0.02)(28)/(0.63) ≈ 0.89` quarters, i.e. `ϕ/4 ≈ 0.22` years. -/
theorem phi_calibration :
    (0.885 : ℝ) < 0.02 * 28 / 0.63 ∧ (0.02 * 28 / 0.63 : ℝ) < 0.895 ∧
      (0.2215 : ℝ) < 0.02 * 28 / 0.63 / 4 ∧ (0.02 * 28 / 0.63 / 4 : ℝ) < 0.2225 := by
  norm_num

/-- Woodford (2003), p. 311 (and p. 305): with `χ = 0.02` and `σ⁻¹ = 0.16` (Table 5.1),
`χσ = 0.125`, which the text rounds to `0.13`; and `χ < (η_yσ)⁻¹` (`η_y = 1`), the realistic
case of p. 305. -/
theorem chiSigma_calibration :
    (0.02 : ℝ) * (0.16 : ℝ)⁻¹ = 0.125 ∧ |(0.125 : ℝ) - 0.13| ≤ 0.005 ∧
      (0.02 : ℝ) < (1 * (0.16 : ℝ)⁻¹)⁻¹ := by
  refine ⟨by norm_num, ?_, by norm_num⟩
  rw [abs_le]
  constructor <;> norm_num

/-- Woodford (2003), fn. 65, p. 304: `ε_mc ≈ 0.63` and `χη_y ≈ 0.01` give `σ⁻¹ + ω ≈ 0.64`
under the corrected (3.12), `ε_mc = ω + σ⁻¹ − η_yχ` (the footnote uses `η_y`, supporting E10). -/
theorem fn65_calibration {ω σinv : ℝ} (h : epsMC ω σinv 1 0.01 = 0.63) : σinv + ω = 0.64 := by
  unfold epsMC at h
  linarith

/-- Woodford (2003), fn. 71, p. 306 (corrected, **error E11**): a constant path
`π ≡ π̄`, `x ≡ x̄`, `î ≡ ī` with no disturbances (`r̂ⁿ = 0`, `îᵐ = 0`) satisfies (3.10) and
(3.14) iff `ī = π̄` and `x̄ = (1 − β)π̄/κ − ϕπ̄` (the footnote prints `+ ϕπ̄`). -/
theorem fn71_steadyState [Nonempty Ω] {σinv ηy ηi χ κ ϕ β pb xb ib : ℝ} (hσ : σinv ≠ 0)
    (hκ : κ ≠ 0) :
    (IS310 𝔼 σinv ηy ηi χ (fun _ _ => xb) (fun _ _ => pb) (fun _ _ => ib) 0 0 ∧
      AS314 𝔼 κ ϕ β (fun _ _ => xb) (fun _ _ => pb) (fun _ _ => ib) 0) ↔
      ib = pb ∧ xb = (1 - β) * pb / κ - ϕ * pb := by
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have hc : ∀ (t : ℕ) (c : ℝ), 𝔼.E t (fun _ => c) = fun _ => c := 𝔼.const
  unfold IS310 AS314
  simp only [hc, Pi.zero_apply, map_zero]
  constructor
  · rintro ⟨h1, h2⟩
    have e1 := congrFun (h1 0) ω
    have e2 := congrFun (h2 0) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
      sub_self, mul_zero, add_zero, sub_zero] at e1 e2
    have hib : ib = pb := by
      have : σinv⁻¹ * (ib - pb) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (inv_ne_zero hσ)
      · linarith
    refine ⟨hib, ?_⟩
    rw [hib] at e2
    field_simp
    linear_combination -e2
  · rintro ⟨hib, hxb⟩
    refine ⟨fun t => ?_, fun t => ?_⟩
    · funext ω'
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, hib]
      ring
    · funext ω'
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, hib, hxb]
      field_simp
      ring

/-- Woodford (2003), fn. 71, p. 306 (**error E11**): the printed target
`x̄ = (1 − β)π̄/κ + ϕπ̄` coincides with the steady-state value `(1 − β)π̄/κ − ϕπ̄` only when
`ϕπ̄ = 0`, i.e. never for `χ > 0` and a nonzero inflation target. -/
theorem fn71_printed_iff {κ ϕ β pb : ℝ} :
    (1 - β) * pb / κ + ϕ * pb = (1 - β) * pb / κ - ϕ * pb ↔ ϕ * pb = 0 := by
  constructor <;> intro h <;> linarith

/-- Woodford (2003), pp. 304–305, with fn. 70: when the interest paid on money keeps the
differential constant (`îᵐ = î`), the model (3.10), (3.14), (1.14) is determinate iff the
Taylor principle (2.7) holds — whatever `χ` in `0 ≤ η_yχ < σ⁻¹` (so that `σ̃ > 0`): the real
balance effect only rescales `σ` to `σ̃ = (σ⁻¹ − η_yχ)⁻¹`, which (2.7) does not involve. -/
theorem money_constSpread_determinate [Nonempty Ω] {σinv ηy ηi χ κ ϕ β φπ φx πb : ℝ}
    (hσ : 0 < σinv) (hs : 0 < σinv - ηy * χ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    ModelDeterminate 𝔼 (fun rn ib π x =>
        IS310 𝔼 σinv ηy ηi χ x π (taylorRate β κ φπ φx πb ib π x)
          (taylorRate β κ φπ φx πb ib π x) rn ∧
        AS314 𝔼 κ ϕ β x π (taylorRate β κ φπ φx πb ib π x)
          (taylorRate β κ φπ φx πb ib π x)) ↔
      1 < taylorLHS β κ φπ φx := by
  rw [← prop_4_3 𝔼 (σ := (σinv - ηy * χ)⁻¹) hβ0 hβ1 (inv_pos.mpr hs) hκ hφπ hφx πb]
  unfold ModelDeterminate TaylorEqm
  simp only [is310_constSpread 𝔼 hσ.ne' hs.ne', as314_constSpread]

/-! ### Footnote 70: determinacy with real-balance effects (`îᵐ = 0`) -/

/-- Woodford (2003), eq. (1.14), p. 246: the Taylor rule
`î_t = ī_t + φ_π(π_t − π̄) + φ_x(x_t − x̄)/4` with an arbitrary gap target `x̄` (fn. 71 uses
`x̄ = (1 − β)π̄/κ − ϕπ̄`; with `x̄ = BasicModel.xbar` it is `Determinacy2.taylorRate`). -/
noncomputable def taylor (ib : ℕ → Ω → ℝ) (φπ φx πb xb : ℝ) (π x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => ib t + φπ • (π t - fun _ => πb) + (φx / 4) • (x t - fun _ => xb)

/-- Woodford (2003), (3.10), (3.14), (1.14), pp. 302–304, with `îᵐ = 0`: the matrix `M`
multiplying `(π_t − π̄, x_t − x̄)`, with `σ = σ⁻¹⁻¹`, `k = ση_iχ`, `d = 1 − ση_yχ`. -/
noncomputable def M70 (σinv ηy ηi χ κ ϕ φπ φx : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 - κ * ϕ * φπ, -(κ + κ * ϕ * φx / 4);
    (σinv⁻¹ + σinv⁻¹ * ηi * χ) * φπ, (1 - σinv⁻¹ * ηy * χ) + (σinv⁻¹ + σinv⁻¹ * ηi * χ) * φx / 4]

/-- Woodford (2003), (3.10), (3.14), (1.14), pp. 302–304, with `îᵐ = 0`: the matrix `N`
multiplying `E_t(π_{t+1} − π̄, x_{t+1} − x̄)`. -/
noncomputable def N70 (σinv ηy ηi χ β φπ φx : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![β, 0; σinv⁻¹ + σinv⁻¹ * ηi * χ * φπ, (1 - σinv⁻¹ * ηy * χ) + σinv⁻¹ * ηi * χ * φx / 4]

/-- Woodford (2003), fn. 71, p. 306 (corrected): the gap target `x̄ = (1 − β)π̄/κ − ϕπ̄`. -/
noncomputable def xbar70 (κ β ϕ πb : ℝ) : ℝ := (1 - β) * πb / κ - ϕ * πb

/-- Woodford (2003), (3.10), (3.14), (1.14), pp. 302–306: the model with real-balance
effects when the interest on money is fixed (`îᵐ = 0`, the U.S. arrangement of p. 305). -/
def Eq70 (σinv ηy ηi χ κ ϕ β φπ φx πb : ℝ) (rn ib π x : ℕ → Ω → ℝ) : Prop :=
  IS310 𝔼 σinv ηy ηi χ x π (taylor ib φπ φx πb (xbar70 κ β ϕ πb) π x) 0 rn ∧
    AS314 𝔼 κ ϕ β x π (taylor ib φπ φx πb (xbar70 κ β ϕ πb) π x) 0

/-- Woodford (2003), pp. 302–306: the disturbance vector of the `îᵐ = 0` model,
`f = (κϕ(ī − π̄), σ(r̂ⁿ + π̄ − ī) + ση_iχ(E_t ī_{t+1} − ī_t))`. -/
noncomputable def f70 (σinv ηi χ κ ϕ πb : ℝ) (rn ib : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun t => ![(κ * ϕ) • (ib t - fun _ => πb),
    σinv⁻¹ • (rn t + (fun _ => πb) - ib t) + (σinv⁻¹ * ηi * χ) • (𝔼.E t (ib (t + 1)) - ib t)]

/-- Woodford (2003), (3.10), (3.14), (1.14), pp. 302–306: for `κ ≠ 0` and `det M ≠ 0`, the
`îᵐ = 0` model is the forward system `z_t = M⁻¹N E_t z_{t+1} + M⁻¹ f_t`. -/
theorem eq70_iff_solves {σinv ηy ηi χ κ ϕ β φπ φx πb : ℝ} (hκ : κ ≠ 0)
    (hM : det2 (M70 σinv ηy ηi χ κ ϕ φπ φx) ≠ 0) {rn ib π x : ℕ → Ω → ℝ} :
    Eq70 𝔼 σinv ηy ηi χ κ ϕ β φπ φx πb rn ib π x ↔
      𝔼.Solves (solveMN (M70 σinv ηy ηi χ κ ϕ φπ φx) (N70 σinv ηy ηi χ β φπ φx))
        (wMN (M70 σinv ηy ηi χ κ ϕ φπ φx) (f70 𝔼 σinv ηi χ κ ϕ πb rn ib))
        (devStack π x πb (xbar70 κ β ϕ πb)) := by
  rw [← solvesMN_iff 𝔼 hM]
  have hxb : κ * xbar70 κ β ϕ πb = (1 - β) * πb - κ * ϕ * πb := by
    unfold xbar70; field_simp
  have hc : ∀ (t : ℕ) (c : ℝ), 𝔼.E t (fun _ => c) = fun _ => c := 𝔼.const
  unfold Eq70 IS310 AS314
  constructor
  · rintro ⟨h1, h2⟩ t ω
    have e1 := congrFun (h1 t) ω
    have e2 := congrFun (h2 t) ω
    simp only [taylor, map_add, map_sub, map_smul, hc, map_zero, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, Pi.zero_apply, smul_eq_mul, sub_zero] at e1 e2
    simp only [M70, N70, f70, devStack, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, map_sub, hc,
      Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · linear_combination e2 + hxb
    · linear_combination e1
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have k := (h t ω).2
      simp only [M70, N70, f70, devStack, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, map_sub, hc,
        Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at k
      simp only [taylor, map_add, map_sub, map_smul, hc, map_zero, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, Pi.zero_apply, smul_eq_mul, sub_zero]
      linear_combination k
    · have k := (h t ω).1
      simp only [M70, N70, f70, devStack, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, map_sub, hc,
        Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at k
      simp only [taylor, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, Pi.zero_apply, smul_eq_mul, sub_zero]
      linear_combination k - hxb

/-- Woodford (2003), pp. 302–306: the disturbance vector of the `îᵐ = 0` model is bounded and
adapted for bounded adapted `r̂ⁿ`, `ī`. -/
theorem f70_bounded_adapted {σinv ηi χ κ ϕ πb : ℝ} {rn ib : ℕ → Ω → ℝ} (hrn : BoundedProc rn)
    (hib : BoundedProc ib) (harn : 𝔼.Adapted rn) (haib : 𝔼.Adapted ib) :
    BoundedVec (f70 𝔼 σinv ηi χ κ ϕ πb rn ib) ∧ 𝔼.AdaptedVec (f70 𝔼 σinv ηi χ κ ϕ πb rn ib) := by
  obtain ⟨M1, h1⟩ := hrn
  obtain ⟨M2, h2⟩ := hib
  refine ⟨⟨|κ * ϕ| * (M2 + |πb|) + (|σinv⁻¹| * (M1 + |πb| + M2) +
    |σinv⁻¹ * ηi * χ| * (M2 + M2)), fun t i ω => ?_⟩, fun t i => ?_⟩
  · have e2 := h2 t ω
    have e1 := h1 t ω
    have eE := 𝔼.abs_E_le (h2 (t + 1)) t ω
    have hM2 : 0 ≤ M2 := (abs_nonneg _).trans e2
    have hM1 : 0 ≤ M1 := (abs_nonneg _).trans e1
    have p1 : 0 ≤ |κ * ϕ| * (M2 + |πb|) := by positivity
    have p2 : 0 ≤ |σinv⁻¹| * (M1 + |πb| + M2) := by positivity
    have p3 : 0 ≤ |σinv⁻¹ * ηi * χ| * (M2 + M2) := by positivity
    have q1 : |ib t ω - πb| ≤ M2 + |πb| := (abs_sub _ _).trans (by linarith)
    have q2 : |rn t ω + πb - ib t ω| ≤ M1 + |πb| + M2 :=
      (abs_sub _ _).trans (by linarith [abs_add_le (rn t ω) πb])
    have q3 : |𝔼.E t (ib (t + 1)) ω - ib t ω| ≤ M2 + M2 := (abs_sub _ _).trans (by linarith)
    fin_cases i
    · simp only [f70, Fin.zero_eta, Matrix.cons_val_zero, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul]
      rw [abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left q1 (abs_nonneg (κ * ϕ))]
    · simp only [f70, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.add_apply,
        Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left q2 (abs_nonneg σinv⁻¹),
        mul_le_mul_of_nonneg_left q3 (abs_nonneg (σinv⁻¹ * ηi * χ))]
  · fin_cases i <;> simp [f70, map_sub, map_add, 𝔼.const, harn t, haib t, 𝔼.E_E_self]

/-- Woodford (2003), fn. 70, p. 306: with real-balance effects and `îᵐ = 0`, determinacy holds
iff `M⁻¹N` satisfies the Schur–Cohn condition (`κ ≠ 0`, `det M ≠ 0`). -/
theorem determinate70_iff [Nonempty Ω] {σinv ηy ηi χ κ ϕ β φπ φx πb : ℝ} (hκ : κ ≠ 0)
    (hM : det2 (M70 σinv ηy ηi χ κ ϕ φπ φx) ≠ 0) :
    ModelDeterminate 𝔼 (Eq70 𝔼 σinv ηy ηi χ κ ϕ β φπ φx πb) ↔
      SchurStable (tr2 (solveMN (M70 σinv ηy ηi χ κ ϕ φπ φx) (N70 σinv ηy ηi χ β φπ φx)))
        (det2 (solveMN (M70 σinv ηy ηi χ κ ϕ φπ φx) (N70 σinv ηy ηi χ β φπ φx))) := by
  refine modelDeterminate_iff_of_reduction 𝔼 (fun rn ib π x => eq70_iff_solves 𝔼 hκ hM)
    (fun rn ib h1 h2 h3 h4 => ?_) ⟨0, fun _ _ => πb, ⟨0, fun t ω => by simp⟩,
      ⟨|πb|, fun t ω => le_rfl⟩, fun t => by simp, fun t => by simp [𝔼.const], ?_⟩
  · obtain ⟨b, a⟩ := f70_bounded_adapted 𝔼 (σinv := σinv) (ηi := ηi) (χ := χ) (κ := κ)
      (ϕ := ϕ) (πb := πb) h1 h2 h3 h4
    exact wMN_bounded_adapted 𝔼 _ b a
  · have hf : f70 𝔼 σinv ηi χ κ ϕ πb 0 (fun _ _ => πb) = 0 := by
      funext t i ω
      fin_cases i <;> simp [f70, 𝔼.const]
    rw [hf]
    funext t i ω
    fin_cases i <;> simp [wMN]

/-- Woodford (2003), fn. 70, p. 306: at `χ = 0` (so `ϕ = 0`) the `îᵐ = 0` model is the basic
model: `det M = Δ` and `M⁻¹N = B` (`taylorB`) with `σ = σ⁻¹⁻¹`. -/
theorem solveMN70_zero {σinv ηy ηi κ β φπ φx : ℝ} :
    det2 (M70 σinv ηy ηi 0 κ 0 φπ φx) = taylorDelta σinv⁻¹ κ φπ φx ∧
      solveMN (M70 σinv ηy ηi 0 κ 0 φπ φx) (N70 σinv ηy ηi 0 β φπ φx) =
        taylorB β σinv⁻¹ κ φπ φx := by
  have hd : det2 (M70 σinv ηy ηi 0 κ 0 φπ φx) = taylorDelta σinv⁻¹ κ φπ φx := by
    simp only [det2, M70, taylorDelta, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  refine ⟨hd, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [solveMN, taylorB, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one] <;>
    rw [hd] <;>
    simp only [M70, N70, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    ring

/-- **Footnote 70** (Woodford (2003), p. 306), made precise: fix the calibrated `ε_mc` and let
`ϕ = η_iχ/ε_mc`. With the interest on money fixed (`îᵐ = 0`), for every Taylor rule (1.14)
that satisfies the Taylor principle (2.7) strictly, the model (3.10), (3.14), (1.14) is
determinate for all `χ` near zero, and for every rule that violates it strictly it is
indeterminate for all `χ` near zero: the determinacy conditions are continuous in `χ`, so the set
of determinate rules is "nearly the same" for small real-balance effects. -/
theorem fn70 [Nonempty Ω] {σinv ηy ηi εmc κ β φπ φx πb : ℝ} (hσ : 0 < σinv) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    (1 < φπ + (1 - β) * φx / (4 * κ) →
      ∀ᶠ χ in 𝓝 (0 : ℝ),
        ModelDeterminate 𝔼 (Eq70 𝔼 σinv ηy ηi χ κ (ηi * χ / εmc) β φπ φx πb)) ∧
    (φπ + (1 - β) * φx / (4 * κ) < 1 →
      ∀ᶠ χ in 𝓝 (0 : ℝ),
        ¬ ModelDeterminate 𝔼 (Eq70 𝔼 σinv ηy ηi χ κ (ηi * χ / εmc) β φπ φx πb)) := by
  have hσ' : 0 < σinv⁻¹ := inv_pos.mpr hσ
  have hΔpos : 0 < taylorDelta σinv⁻¹ κ φπ φx := taylorDelta_pos hσ' hκ hφπ hφx
  have hMc : ∀ i j, Continuous (fun χ : ℝ => M70 σinv ηy ηi χ κ (ηi * χ / εmc) φπ φx i j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [M70, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta,
        Fin.mk_one] <;>
      fun_prop
  have hNc : ∀ i j, Continuous (fun χ : ℝ => N70 σinv ηy ηi χ β φπ φx i j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [N70, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta,
        Fin.mk_one] <;>
      fun_prop
  have hdetc : Continuous (fun χ : ℝ => det2 (M70 σinv ηy ηi χ κ (ηi * χ / εmc) φπ φx)) := by
    unfold det2
    exact ((hMc 0 0).mul (hMc 1 1)).sub ((hMc 0 1).mul (hMc 1 0))
  have hz : ηi * (0 : ℝ) / εmc = 0 := by simp
  obtain ⟨hd0, hA0⟩ := solveMN70_zero (σinv := σinv) (ηy := ηy) (ηi := ηi) (κ := κ) (β := β)
    (φπ := φπ) (φx := φx)
  have hdet0 : det2 (M70 σinv ηy ηi 0 κ (ηi * 0 / εmc) φπ φx) ≠ 0 := by
    rw [hz, hd0]; exact hΔpos.ne'
  have hSc : ∀ i j, ContinuousAt (fun χ : ℝ => solveMN (M70 σinv ηy ηi χ κ (ηi * χ / εmc) φπ φx)
      (N70 σinv ηy ηi χ β φπ φx) i j) 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [solveMN, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta,
        Fin.mk_one] <;>
      exact ContinuousAt.div (Continuous.continuousAt (by
        first
        | exact ((hMc 1 1).mul (hNc 0 0)).sub ((hMc 0 1).mul (hNc 1 0))
        | exact ((hMc 1 1).mul (hNc 0 1)).sub ((hMc 0 1).mul (hNc 1 1))
        | exact ((hMc 0 0).mul (hNc 1 0)).sub ((hMc 1 0).mul (hNc 0 0))
        | exact ((hMc 0 0).mul (hNc 1 1)).sub ((hMc 1 0).mul (hNc 0 1))))
        hdetc.continuousAt hdet0
  set A := fun χ : ℝ => solveMN (M70 σinv ηy ηi χ κ (ηi * χ / εmc) φπ φx)
    (N70 σinv ηy ηi χ β φπ φx) with hAdef
  have hTc : ContinuousAt (fun χ => tr2 (A χ)) 0 := (hSc 0 0).add (hSc 1 1)
  have hDc : ContinuousAt (fun χ => det2 (A χ)) 0 :=
    ((hSc 0 0).mul (hSc 1 1)).sub ((hSc 0 1).mul (hSc 1 0))
  have hA00 : A 0 = taylorB β σinv⁻¹ κ φπ φx := by simp only [hAdef]; rw [hz, hA0]
  have hne : ∀ᶠ χ in 𝓝 (0 : ℝ), det2 (M70 σinv ηy ηi χ κ (ηi * χ / εmc) φπ φx) ≠ 0 :=
    hdetc.continuousAt.eventually_ne hdet0
  constructor
  · intro hTP
    obtain ⟨h1, h2⟩ := (taylorB_schurStable_iff hβ0 hβ1 hσ' hκ hφπ hφx).mpr
      (by rw [taylorLHS_eq]; exact hTP)
    rw [← hA00] at h1 h2
    have e1 : ∀ᶠ χ in 𝓝 (0 : ℝ), |det2 (A χ)| < 1 :=
      (continuous_abs.continuousAt.comp hDc).eventually_lt continuousAt_const h1
    have e2 : ∀ᶠ χ in 𝓝 (0 : ℝ), |tr2 (A χ)| < 1 + det2 (A χ) :=
      (continuous_abs.continuousAt.comp hTc).eventually_lt (continuousAt_const.add hDc) h2
    filter_upwards [e1, e2, hne] with χ h1 h2 h3
    exact (determinate70_iff 𝔼 hκ.ne' h3).mpr ⟨h1, h2⟩
  · intro hTP
    have h0 : 1 + det2 (A 0) < tr2 (A 0) := by
      rw [hA00, taylorB_tr, taylorB_det hΔpos.ne']
      have e1 : 1 + β / taylorDelta σinv⁻¹ κ φπ φx - (1 + β + σinv⁻¹ * κ + β * σinv⁻¹ * φx / 4) /
          taylorDelta σinv⁻¹ κ φπ φx = (κ * σinv⁻¹) * (φπ + (1 - β) * φx / (4 * κ) - 1) /
          taylorDelta σinv⁻¹ κ φπ φx := by
        unfold taylorDelta
        field_simp
        ring
      have : (κ * σinv⁻¹) * (φπ + (1 - β) * φx / (4 * κ) - 1) / taylorDelta σinv⁻¹ κ φπ φx < 0 :=
        div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos hκ hσ') (by linarith)) hΔpos
      linarith
    have e : ∀ᶠ χ in 𝓝 (0 : ℝ), 1 + det2 (A χ) < tr2 (A χ) :=
      (continuousAt_const.add hDc).eventually_lt hTc h0
    filter_upwards [e, hne] with χ h1 h3
    rw [determinate70_iff 𝔼 hκ.ne' h3]
    rintro ⟨-, h2⟩
    linarith [le_abs_self (tr2 (A χ))]

end Woodford.NeoWicksellianFramework.Money
