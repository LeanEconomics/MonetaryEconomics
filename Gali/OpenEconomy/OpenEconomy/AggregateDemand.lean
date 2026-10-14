/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OpenEconomy.Identities
import OpenEconomy.Expectations
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Aggregate demand in the small open economy

Galí (2015), Chapter 8, §8.1.3 (p. 234) and §8.2.1 (pp. 234–236).

The openness index is `υ ∈ [0, 1]`, `η > 0` is the elasticity of substitution between
domestic and foreign goods and `σ > 0` the inverse intertemporal elasticity. The book's
coefficients are `ϖ = ση + (1 − υ)(ση − 1)` (`varpi`), `Φ = 1/(1 + υ(ϖ − 1))` (`Phi`) and
`σ_υ = σΦ` (`sigmaU`).

## Main results

* `one_add_mul_varpi`, `Phi_pos`, `sigmaU_pos`: `1 + υ(ϖ − 1) = (1 − υ)² + υ(2 − υ)ση > 0`,
  so `Φ > 0` and `σ_υ > 0` (p. 235).
* `cpi_self`, `cpiCD_self`: at the symmetric steady state the CPI (`Preferences.cpi`,
  `Preferences.cpiCD`) equals `P_H`; identity (12) itself is `Identities.log_cpi_eq`,
  `Identities.hasDerivAt_cpiGap` and (exact at `η = 1`) `Identities.log_cpiCD_eq`.
* `exports_eq`, `trade_balanced_ss`, `netExports_ss`: exports `X = υ S^η Y*` and balanced
  trade at the symmetric steady state (p. 234).
* `eq24`: goods-market clearing (23) aggregates exactly to (24).
* `log_eq24`, `eq25`, `eq25_ces`, `eq25_cd`: log output is `logOutput υ η h c s y*` exactly
  (`h` the log relative price of (12)), and (25) `y = (1 − υ)c + υ(2 − υ)ηs + υy*` is its
  exact (Fréchet) derivative at the symmetric steady state, CES or Cobb–Douglas.
* `eq26`: the Euler equation in domestic inflation, from (11) and (13).
* `eq27`: the terms of trade `s = σ_υ(y − y*) − (1 − υ)Φz` from (17) and (25).
* `eq26_iff_eq28`: given (17) and (25), (26) is equivalent to the open-economy dynamic IS
  equation (28).
* `sigmaU_strictAntiOn`: if `ση > 1`, `σ_υ` is strictly decreasing in `υ` on `[0, 1]`
  (p. 235).
* `eq28_iff_eq29`: the gap form (29) with the natural rate (30).
* `hasFDerivAt_netExports`, `eq31`, `nxCoef_eq_zero`: (31)
  `nx = υ(ϖ/σ − 1)s − (υ/σ)z`, and `nx` does not depend on `s` when `σ = η = 1`.
* `nxCoef_one_nonpos`, `nxCoef_counterexample`, `not_large_openness_improves`: the p. 236
  claim that a large `υ` makes a terms-of-trade depreciation improve the trade balance is
  false (with `σ = 1`, `η = 0.9` the coefficient is negative for every `υ ∈ (0, 1]`).
  Corrected statements: `nxCoef_eventually_pos` (`η > 1` ⇒ positive for `υ` near `1`) and
  `nxCoef_pos_iff` (for fixed `υ ∈ (0, 1]`, positive iff `η > (σ + 1 − υ)/((2 − υ)σ)`).

The CES variety aggregation (`priceIndex`, `cesAgg`, `demand`, `cesAgg_demand`) is imported
from `Preferences.Variety`.
-/

namespace Gali.OpenEconomy.AggregateDemand

open MeasureTheory Filter Topology Preferences Preferences.Variety Identities

/-! ### The openness coefficients `ϖ`, `Φ`, `σ_υ` -/

/-- Galí (2015), p. 235: `ϖ ≡ ση + (1 − υ)(ση − 1)`. -/
def varpi (σ η υ : ℝ) : ℝ := σ * η + (1 - υ) * (σ * η - 1)

/-- Galí (2015), p. 235: `Φ ≡ 1/(1 + υ(ϖ − 1))`. -/
noncomputable def Phi (σ η υ : ℝ) : ℝ := 1 / (1 + υ * (varpi σ η υ - 1))

/-- Galí (2015), p. 235: `σ_υ ≡ σΦ`. -/
noncomputable def sigmaU (σ η υ : ℝ) : ℝ := σ * Phi σ η υ

/-- Galí (2015), p. 235: `ϖ − 1 = (2 − υ)(ση − 1)`. -/
theorem varpi_sub_one (σ η υ : ℝ) : varpi σ η υ - 1 = (2 - υ) * (σ * η - 1) := by
  unfold varpi
  ring

/-- Galí (2015), p. 235: `1 + υ(ϖ − 1) = (1 − υ)² + υ(2 − υ)ση`. -/
theorem one_add_mul_varpi (σ η υ : ℝ) :
    1 + υ * (varpi σ η υ - 1) = (1 - υ) ^ 2 + υ * (2 - υ) * (σ * η) := by
  unfold varpi
  ring

/-- Galí (2015), p. 235: for `σ, η > 0` and `υ ∈ [0, 1]`, `1 + υ(ϖ − 1) > 0`. -/
theorem one_add_mul_varpi_pos {σ η υ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hυ0 : 0 ≤ υ)
    (hυ1 : υ ≤ 1) : 0 < 1 + υ * (varpi σ η υ - 1) := by
  rw [one_add_mul_varpi]
  have hse : 0 < σ * η := mul_pos hσ hη
  rcases eq_or_lt_of_le hυ1 with h | h
  · subst h
    norm_num
    exact hse
  · have h1 : 0 < (1 - υ) ^ 2 := by
      have : 0 < 1 - υ := by linarith
      positivity
    have h2 : 0 ≤ υ * (2 - υ) * (σ * η) :=
      mul_nonneg (mul_nonneg hυ0 (by linarith)) hse.le
    linarith

/-- Galí (2015), p. 235: `Φ > 0`. -/
theorem Phi_pos {σ η υ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hυ0 : 0 ≤ υ) (hυ1 : υ ≤ 1) :
    0 < Phi σ η υ :=
  one_div_pos.2 (one_add_mul_varpi_pos hσ hη hυ0 hυ1)

/-- Galí (2015), p. 235: `σ_υ > 0`. -/
theorem sigmaU_pos {σ η υ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hυ0 : 0 ≤ υ) (hυ1 : υ ≤ 1) :
    0 < sigmaU σ η υ :=
  mul_pos hσ (Phi_pos hσ hη hυ0 hυ1)

/-- Galí (2015), p. 235: `σ_υ (1 + υ(ϖ − 1)) = σ`. -/
theorem sigmaU_mul {σ η υ : ℝ} (hD : 1 + υ * (varpi σ η υ - 1) ≠ 0) :
    sigmaU σ η υ * (1 + υ * (varpi σ η υ - 1)) = σ := by
  unfold sigmaU Phi
  field_simp

/-- Galí (2015), p. 239: if `ση > 1` (and `υ < 2`, in particular `υ ∈ [0, 1]`), `ϖ > 1`. -/
theorem one_lt_varpi {σ η υ : ℝ} (h : 1 < σ * η) (hυ : υ < 2) : 1 < varpi σ η υ := by
  have := varpi_sub_one σ η υ
  have : 0 < (2 - υ) * (σ * η - 1) := mul_pos (by linarith) (by linarith)
  linarith

/-- Galí (2015), p. 235: in the closed economy (`υ = 0`), `σ_υ = σ`. -/
theorem sigmaU_zero (σ η : ℝ) : sigmaU σ η 0 = σ := by
  simp [sigmaU, Phi]

/-- Galí (2015), p. 235: with `ση = 1` (e.g. `σ = η = 1`), `ϖ = 1`, `Φ = 1`, `σ_υ = σ` for
every degree of openness. -/
theorem sigmaU_of_sigma_mul_eta {σ η : ℝ} (h : σ * η = 1) (υ : ℝ) : sigmaU σ η υ = σ := by
  simp [sigmaU, Phi, varpi, h]

/-- Galí (2015), p. 235: **if `ση > 1`, `σ_υ` is strictly decreasing in the degree of
openness `υ` on `[0, 1]`**, so openness raises the interest sensitivity `1/σ_υ` of output. -/
theorem sigmaU_strictAntiOn {σ η : ℝ} (hσ : 0 < σ) (hη : 0 < η) (h : 1 < σ * η) :
    StrictAntiOn (sigmaU σ η) (Set.Icc 0 1) := by
  intro a ha b hb hab
  have hDa := one_add_mul_varpi_pos hσ hη ha.1 ha.2
  have hlt : 1 + a * (varpi σ η a - 1) < 1 + b * (varpi σ η b - 1) := by
    rw [varpi_sub_one, varpi_sub_one]
    have : 0 < (σ * η - 1) * ((b - a) * (2 - a - b)) :=
      mul_pos (by linarith) (mul_pos (by linarith) (by linarith [hb.2]))
    nlinarith
  unfold sigmaU Phi
  exact mul_lt_mul_of_pos_left (one_div_lt_one_div_of_lt hDa hlt) hσ

/-! ### The consumer price index and identity (12)

The CES consumer price index is `Preferences.cpi` (`η ≠ 1`), its Cobb–Douglas limit
`Preferences.cpiCD` (`η = 1`); the exact identity (12) and its first-order form are
`Identities.log_cpi_eq`, `Identities.hasDerivAt_cpiGap` and `Identities.log_cpiCD_eq`. -/

/-- Galí (2015), p. 227: a convex combination of positive numbers is positive. -/
theorem convex_comb_pos {υ a b : ℝ} (hυ0 : 0 ≤ υ) (hυ1 : υ ≤ 1) (ha : 0 < a) (hb : 0 < b) :
    0 < (1 - υ) * a + υ * b := by
  rcases eq_or_lt_of_le hυ1 with h | h
  · subst h
    simpa using hb
  · have : 0 < (1 - υ) * a := mul_pos (by linarith) ha
    have : 0 ≤ υ * b := mul_nonneg hυ0 hb.le
    linarith

/-- Galí (2015), p. 234: at the symmetric steady state `P_F = P_H` the CES consumer price
index equals `P_H` (any `υ`, `η ≠ 1`). -/
theorem cpi_self {υ η P : ℝ} (hη : η ≠ 1) (hP : 0 < P) : cpi υ η P P = P := by
  have h1 : (1 : ℝ) - η ≠ 0 := sub_ne_zero.2 (Ne.symm hη)
  unfold cpi
  rw [show (1 - υ) * P ^ (1 - η) + υ * P ^ (1 - η) = P ^ (1 - η) by ring, one_div,
    Real.rpow_rpow_inv hP.le h1]

/-- Galí (2015), fn. 2, p. 226, and p. 234: at the symmetric steady state `P_F = P_H` the
Cobb–Douglas consumer price index (`η = 1`) equals `P_H`. -/
theorem cpiCD_self {υ P : ℝ} (hP : 0 < P) : cpiCD υ P P = P := by
  unfold cpiCD
  rw [← Real.rpow_add hP]
  simp

/-! ### Exports and the steady-state trade balance (p. 234) -/

/-- Galí (2015), p. 234: with the law of one price `P_F = ℰP*`, exports
`X = υ(P_H/(ℰP*))^{−η}Y*` equal `υS^ηY*`, `S = P_F/P_H`. -/
theorem exports_eq {υ η PH PF ℰ Pstar Ystar : ℝ} (hPH : 0 < PH) (hE : 0 < ℰ)
    (hPs : 0 < Pstar) (hLOP : PF = ℰ * Pstar) :
    υ * (PH / (ℰ * Pstar)) ^ (-η) * Ystar = υ * (PF / PH) ^ η * Ystar := by
  rw [hLOP, Real.rpow_neg (div_pos hPH (mul_pos hE hPs)).le, ← Real.inv_rpow
    (div_pos hPH (mul_pos hE hPs)).le, inv_div]

/-- Galí (2015), p. 234: **trade is balanced at the symmetric steady state**: with `S = 1`
(`P_F = P_H`), the CPI `P_c` then equal to `P_H` (`cpi_self` for the CES index, `cpiCD_self`
for the Cobb–Douglas one), imports `C_F = υ(P_F/P_c)^{−η}C`, exports `X = υS^ηY*` and risk
sharing `C = Y*`, the value of exports equals the value of imports, `P_H X = P_F C_F`. -/
theorem trade_balanced_ss {υ η PH PF Pc C CF X Ystar : ℝ} (hPH : 0 < PH) (hS : PF = PH)
    (hPc : Pc = PH) (hC : C = Ystar) (hCF : CF = υ * (PF / Pc) ^ (-η) * C)
    (hX : X = υ * (PF / PH) ^ η * Ystar) :
    PH * X = PF * CF := by
  subst hS hC hPc
  rw [hCF, hX, div_self hPH.ne']
  simp

/-- Galí (2015), p. 234 and p. 236: at the symmetric steady state (CPI `P_c = P_H`, by
`cpi_self` or `cpiCD_self`) output equals consumption and net exports `Y − (P_c/P_H)C` are
zero. -/
theorem netExports_ss {υ η PH Pc Y C Ystar : ℝ} (hPH : 0 < PH) (hPc : Pc = PH)
    (hC : C = Ystar)
    (hY : Y = (1 - υ) * (PH / Pc) ^ (-η) * C + υ * (PH / PH) ^ η * Ystar) :
    Y = C ∧ Y - Pc / PH * C = 0 := by
  subst hPc
  rw [div_self hPH.ne'] at hY ⊢
  simp only [Real.one_rpow, mul_one] at hY
  subst hC
  constructor <;> linarith

/-! ### Goods-market clearing: (23) and (24)

The CES variety aggregation (`priceIndex`, `cesAgg`, `demand`, `cesAgg_demand`) is
`Preferences.Variety`. -/

variable {G : Type*} [MeasurableSpace G]

/-- Galí (2015), (23) and **(24)**, pp. 234–235 (exact): if each domestic good `i` clears its
market, `Y(i) = C_H(i) + X(i)` with `C_H(i) = (P_H(i)/P_H)^{−ε}(1 − υ)(P_H/P)^{−η}C` and
`X(i) = (P_H(i)/P_H)^{−ε}υS^ηY*`, then aggregate output is
`Y = (1 − υ)(P_H/P)^{−η}C + υS^ηY*`. -/
theorem eq24 {μ : Measure G} {ε υ η P C S Ystar : ℝ} {PHi CH X Y : G → ℝ} (hε : 1 < ε)
    (hP : ∀ i, 0 < PHi i) (hpos : 0 < ∫ i, PHi i ^ (1 - ε) ∂μ) (hυ0 : 0 ≤ υ) (hυ1 : υ ≤ 1)
    (hPc : 0 < P) (hC : 0 ≤ C) (hS : 0 ≤ S) (hYs : 0 ≤ Ystar)
    (hCH : ∀ i, CH i = (PHi i / priceIndex μ ε PHi) ^ (-ε) *
      ((1 - υ) * (priceIndex μ ε PHi / P) ^ (-η) * C))
    (hX : ∀ i, X i = (PHi i / priceIndex μ ε PHi) ^ (-ε) * (υ * S ^ η * Ystar))
    (hY : ∀ i, Y i = CH i + X i) :
    cesAgg μ ε Y = (1 - υ) * (priceIndex μ ε PHi / P) ^ (-η) * C + υ * S ^ η * Ystar := by
  have hI := priceIndex_pos hpos
  have hYd : Y = demand μ ε PHi
      ((1 - υ) * (priceIndex μ ε PHi / P) ^ (-η) * C + υ * S ^ η * Ystar) := by
    funext i
    rw [hY, hCH, hX, demand]
    ring
  rw [hYd]
  refine cesAgg_demand hε hP hpos (add_nonneg (mul_nonneg (mul_nonneg (by linarith)
    (Real.rpow_nonneg (div_pos hI hPc).le _)) hC) (mul_nonneg (mul_nonneg hυ0
    (Real.rpow_nonneg hS _)) hYs))

/-! ### Log-linear goods-market clearing (25) as an exact derivative -/

/-- Galí (2015), (24), p. 235, in logs: `log Y` as a function of `c = log C`, the log terms of
trade `s` and `y* = log Y*`, `log[(1 − υ)e^{c + η h(s)} + υe^{ηs + y*}]`, where
`h(s) = log(P/P_H)` is the log relative price of (12): `Identities.cpiGap υ η` for the CES
index (`η ≠ 1`) and `s ↦ υs` for the Cobb–Douglas index (`η = 1`). -/
noncomputable def logOutput (υ η : ℝ) (h : ℝ → ℝ) (c s ystar : ℝ) : ℝ :=
  Real.log ((1 - υ) * Real.exp (c + η * h s) + υ * Real.exp (η * s + ystar))

/-- Galí (2015), (24), p. 235 (exact): for a consumer price index `P_c` with log relative
price `h`, `log P_c − log P_H = h(p_F − p_H)` (identity (12): `Identities.log_cpi_eq` for the
CES index, `Identities.log_cpiCD_eq` for the Cobb–Douglas one), `log Y` is `logOutput`
evaluated at `c`, `s = p_F − p_H` and `y*`. -/
theorem log_eq24 {υ η PH PF Pc C Ystar Y : ℝ} {h : ℝ → ℝ} (hPH : 0 < PH) (hPF : 0 < PF)
    (hP : 0 < Pc) (hC : 0 < C) (hYs : 0 < Ystar)
    (hL : Real.log Pc - Real.log PH = h (Real.log PF - Real.log PH))
    (hY : Y = (1 - υ) * (PH / Pc) ^ (-η) * C + υ * (PF / PH) ^ η * Ystar) :
    Real.log Y
      = logOutput υ η h (Real.log C) (Real.log PF - Real.log PH) (Real.log Ystar) := by
  have e1 : (PH / Pc) ^ (-η) * C
      = Real.exp (Real.log C + η * h (Real.log PF - Real.log PH)) := by
    rw [Real.exp_add, Real.exp_log hC, ← hL, Real.rpow_def_of_pos (div_pos hPH hP),
      Real.log_div hPH.ne' hP.ne', mul_comm C]
    congr 2
    ring
  have e2 : (PF / PH) ^ η * Ystar
      = Real.exp (η * (Real.log PF - Real.log PH) + Real.log Ystar) := by
    rw [Real.exp_add, Real.exp_log hYs, Real.rpow_def_of_pos (div_pos hPF hPH),
      Real.log_div hPF.ne' hPH.ne', mul_comm (Real.log PF - Real.log PH)]
  unfold logOutput
  rw [hY, mul_assoc (1 - υ), e1, mul_assoc υ, e2]

/-- Galí (2015), (25), p. 235: the linear map
`(c, s, y*) ↦ (1 − υ)c + υ(2 − υ)ηs + υy*`. -/
noncomputable def eq25Map (υ η : ℝ) : ℝ × ℝ × ℝ →L[ℝ] ℝ :=
  (1 - υ) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
    + (υ * (2 - υ) * η) •
      (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
    + υ • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- Galí (2015), (25), p. 235: `eq25Map` evaluated. -/
theorem eq25Map_apply (υ η c s ys : ℝ) :
    eq25Map υ η (c, s, ys) = (1 - υ) * c + υ * (2 - υ) * η * s + υ * ys := by
  simp [eq25Map]

/-- Galí (2015), p. 234: at the symmetric steady state (`c = y* = ȳ`, `s = 0`), log output is
`ȳ`, i.e. `Y = C = Y*`. -/
theorem logOutput_ss (υ η ybar : ℝ) {h : ℝ → ℝ} (h0 : h 0 = 0) :
    logOutput υ η h ybar 0 ybar = ybar := by
  unfold logOutput
  rw [h0]
  have : (1 - υ) * Real.exp (ybar + η * 0) + υ * Real.exp (η * 0 + ybar) = Real.exp ybar := by
    simp only [mul_zero, add_zero, zero_add]
    ring
  rw [this, Real.log_exp]

/-- Galí (2015), **(25)**, p. 235: `y = (1 − υ)c + υ(2 − υ)ηs + υy*` is the exact
(Fréchet) derivative of log (24) at the symmetric steady state `(c, s, y*) = (ȳ, 0, ȳ)`,
for every log relative price `h` with `h(0) = 0` and `h'(0) = υ` (the first-order form of
(12)), in particular in the CES case (`eq25_ces`) and the Cobb–Douglas case (`eq25_cd`). -/
theorem eq25 (υ η ybar : ℝ) {h : ℝ → ℝ} (h0 : h 0 = 0) (hd : HasDerivAt h υ 0) :
    HasFDerivAt (fun x : ℝ × ℝ × ℝ => logOutput υ η h x.1 x.2.1 x.2.2) (eq25Map υ η)
      (ybar, 0, ybar) := by
  have h1 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))
      (ybar, (0 : ℝ), ybar) := hasFDerivAt_fst
  have h2 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      (ybar, (0 : ℝ), ybar) := hasFDerivAt_snd.fst
  have h3 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      (ybar, (0 : ℝ), ybar) := hasFDerivAt_snd.snd
  have hL : HasFDerivAt (fun x : ℝ × ℝ × ℝ => h x.2.1)
      (υ • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      (ybar, (0 : ℝ), ybar) := HasDerivAt.comp_hasFDerivAt (f := fun x : ℝ × ℝ × ℝ => x.2.1)
        (ybar, (0 : ℝ), ybar) hd h2
  have hA := h1.add (hL.const_mul η)
  have hB := (h2.const_mul η).add h3
  have hF := (hA.exp.const_mul (1 - υ)).add (hB.exp.const_mul υ)
  have hne : (1 - υ) * Real.exp (ybar + η * h 0) +
      υ * Real.exp (η * 0 + ybar) ≠ 0 := by
    rw [h0]
    simp only [mul_zero, add_zero, zero_add]
    ring_nf
    exact (Real.exp_pos _).ne'
  have hlog := hF.log hne
  refine hlog.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun x => ?_
  obtain ⟨c, s, ys⟩ := x
  rw [eq25Map_apply]
  simp only [Pi.add_apply, FunLike.coe_smul, FunLike.coe_add, Pi.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul]
  rw [h0]
  simp only [mul_zero, add_zero, zero_add]
  rw [show (1 - υ) * Real.exp ybar + υ * Real.exp ybar = Real.exp ybar by ring]
  have he := (Real.exp_pos ybar).ne'
  field_simp
  ring

/-- Galí (2015), **(25)**, p. 235, CES case (`η ≠ 1`, `0 < υ < 1`): with the exact CES log
relative price `h = Identities.cpiGap υ η` of (12), (25) is the derivative of log (24). -/
theorem eq25_ces {υ η : ℝ} (hυ0 : 0 < υ) (hυ1 : υ < 1) (hη1 : η ≠ 1) (ybar : ℝ) :
    HasFDerivAt (fun x : ℝ × ℝ × ℝ => logOutput υ η (cpiGap υ η) x.1 x.2.1 x.2.2)
      (eq25Map υ η) (ybar, 0, ybar) :=
  eq25 υ η ybar (cpiGap_zero hυ0 hυ1) (hasDerivAt_cpiGap hυ0 hυ1 hη1)

/-- Galí (2015), **(25)**, p. 235, Cobb–Douglas case (`η = 1`, fn. 4, p. 229): with the exact
log relative price `h(s) = υs` of (12), (25) is the derivative of log (24). -/
theorem eq25_cd (υ ybar : ℝ) :
    HasFDerivAt (fun x : ℝ × ℝ × ℝ => logOutput υ 1 (fun s => υ * s) x.1 x.2.1 x.2.2)
      (eq25Map υ 1) (ybar, 0, ybar) :=
  eq25 υ 1 ybar (mul_zero υ) (by simpa using (hasDerivAt_id' (0 : ℝ)).const_mul υ)

/-! ### The terms of trade (27) and net exports (31) -/

/-- Galí (2015), **(27)**, p. 235: combining risk sharing (17)
`c = y* + z/σ + ((1 − υ)/σ)s` with (25) gives `s = σ_υ(y − y*) − (1 − υ)Φz`. -/
theorem eq27 {σ η υ c s y ystar z : ℝ} (hσ : σ ≠ 0) (hD : 1 + υ * (varpi σ η υ - 1) ≠ 0)
    (h17 : c = ystar + z / σ + (1 - υ) / σ * s)
    (h25 : y = (1 - υ) * c + υ * (2 - υ) * η * s + υ * ystar) :
    s = sigmaU σ η υ * (y - ystar) - (1 - υ) * Phi σ η υ * z := by
  have key : σ * (y - ystar) = (1 - υ) * z + (1 + υ * (varpi σ η υ - 1)) * s := by
    rw [h25, h17]
    unfold varpi
    field_simp
    ring
  unfold sigmaU Phi
  field_simp
  linear_combination -key

/-- Galí (2015), p. 236: the coefficient `υ(ϖ/σ − 1)` of the terms of trade in (31). -/
noncomputable def nxCoef (σ η υ : ℝ) : ℝ := υ * (varpi σ η υ / σ - 1)

/-- Galí (2015), **(31)**, p. 236: with `nx = y − c − υs` (the first-order net-export
identity, `hasFDerivAt_netExports`), (17) and (25), `nx = υ(ϖ/σ − 1)s − (υ/σ)z`. -/
theorem eq31 {σ η υ c s y ystar z nx : ℝ} (hσ : σ ≠ 0)
    (h17 : c = ystar + z / σ + (1 - υ) / σ * s)
    (h25 : y = (1 - υ) * c + υ * (2 - υ) * η * s + υ * ystar) (hnx : nx = y - c - υ * s) :
    nx = nxCoef σ η υ * s - υ / σ * z := by
  rw [hnx, h25, h17]
  unfold nxCoef varpi
  field_simp
  ring

/-- Galí (2015), p. 236: net exports in terms of domestic output relative to steady-state
output, `nx = (Y − (P/P_H)C)/Ȳ`, written in logs `y`, `c` and `s` (`ȳ = log Ȳ`), where `h`
is the log relative price `log(P/P_H)` of (12) as a function of `s` (see `logOutput`). -/
noncomputable def netExports (h : ℝ → ℝ) (ybar y c s : ℝ) : ℝ :=
  (Real.exp y - Real.exp (c + h s)) / Real.exp ybar

/-- Galí (2015), p. 236 (exact): for a CPI `P_c` with `log P_c − log P_H = h(p_F − p_H)`
(`Identities.log_cpi_eq`, `Identities.log_cpiCD_eq`), `(Y − (P_c/P_H)C)/Ȳ` is `netExports`
in logs. -/
theorem netExports_eq {PH PF Pc C Y Ybar : ℝ} {h : ℝ → ℝ} (hPH : 0 < PH) (hP : 0 < Pc)
    (hC : 0 < C) (hY : 0 < Y) (hYb : 0 < Ybar)
    (hL : Real.log Pc - Real.log PH = h (Real.log PF - Real.log PH)) :
    (Y - Pc / PH * C) / Ybar = netExports h (Real.log Ybar) (Real.log Y)
      (Real.log C) (Real.log PF - Real.log PH) := by
  unfold netExports
  rw [Real.exp_log hY, Real.exp_log hYb, Real.exp_add, Real.exp_log hC,
    ← hL, Real.exp_sub, Real.exp_log hP, Real.exp_log hPH, mul_comm C]

/-- Galí (2015), p. 236: the linear map `(y, c, s) ↦ y − c − υs`. -/
noncomputable def nxMap (υ : ℝ) : ℝ × ℝ × ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
    - (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
    - υ • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- Galí (2015), p. 236: `nxMap` evaluated. -/
theorem nxMap_apply (υ y c s : ℝ) : nxMap υ (y, c, s) = y - c - υ * s := by
  simp [nxMap]

/-- Galí (2015), p. 236: **`nx = y − c − υs` to first order**: net exports vanish at the
symmetric steady state `(y, c, s) = (ȳ, ȳ, 0)`, and their exact derivative there is
`(y, c, s) ↦ y − c − υs`, for every log relative price `h` with `h(0) = 0`, `h'(0) = υ` (CES:
`Identities.cpiGap_zero`, `Identities.hasDerivAt_cpiGap`; Cobb–Douglas: `h(s) = υs`). -/
theorem hasFDerivAt_netExports (υ ybar : ℝ) {h : ℝ → ℝ} (h0 : h 0 = 0)
    (hd : HasDerivAt h υ 0) :
    netExports h ybar ybar ybar 0 = 0 ∧
      HasFDerivAt (fun x : ℝ × ℝ × ℝ => netExports h ybar x.1 x.2.1 x.2.2) (nxMap υ)
        (ybar, ybar, 0) := by
  refine ⟨by simp [netExports, h0], ?_⟩
  have h1 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))
      (ybar, ybar, (0 : ℝ)) := hasFDerivAt_fst
  have h2 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      (ybar, ybar, (0 : ℝ)) := hasFDerivAt_snd.fst
  have h3 : HasFDerivAt (fun x : ℝ × ℝ × ℝ => x.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      (ybar, ybar, (0 : ℝ)) := hasFDerivAt_snd.snd
  have hL : HasFDerivAt (fun x : ℝ × ℝ × ℝ => h x.2.2)
      (υ • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      (ybar, ybar, (0 : ℝ)) := HasDerivAt.comp_hasFDerivAt (f := fun x : ℝ × ℝ × ℝ => x.2.2)
        (ybar, ybar, (0 : ℝ)) hd h3
  have hF := HasFDerivAt.mul_const (HasFDerivAt.sub h1.exp (h2.add hL).exp) (Real.exp ybar)⁻¹
  have hfun : (fun x : ℝ × ℝ × ℝ => netExports h ybar x.1 x.2.1 x.2.2) = fun x =>
      (Real.exp x.1 - Real.exp (x.2.1 + h x.2.2)) * (Real.exp ybar)⁻¹ := by
    funext x
    simp [netExports, div_eq_mul_inv]
  rw [hfun]
  refine hF.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun x => ?_
  obtain ⟨y, c, s⟩ := x
  rw [nxMap_apply]
  simp only [h0, FunLike.coe_smul, FunLike.coe_add, Pi.smul_apply,
    FunLike.coe_sub, Pi.sub_apply, Pi.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, add_zero]
  have he := (Real.exp_pos ybar).ne'
  field_simp
  ring

/-- Galí (2015), p. 236: **with `σ = η = 1`, net exports are invariant to the terms of trade**:
the coefficient of `s` in (31) is zero and `nx = −υz`. -/
theorem nxCoef_eq_zero (υ : ℝ) : nxCoef 1 1 υ = 0 := by
  simp [nxCoef, varpi]

/-- Galí (2015), p. 236: at `σ = η = 1`, (31) reads `nx = −υz`. -/
theorem eq31_unit {υ c s y ystar z nx : ℝ} (h17 : c = ystar + z / 1 + (1 - υ) / 1 * s)
    (h25 : y = (1 - υ) * c + υ * (2 - υ) * 1 * s + υ * ystar) (hnx : nx = y - c - υ * s) :
    nx = -υ * z := by
  rw [eq31 one_ne_zero h17 h25 hnx, nxCoef_eq_zero]
  ring

/-- Galí (2015), p. 236, **correction (error 2)**: at full openness `υ = 1` the coefficient of
the terms of trade is `η − 1`, so for `η ≤ 1` a depreciation never improves the trade balance
there, however open the economy. -/
theorem nxCoef_one_nonpos {σ η : ℝ} (hσ : 0 < σ) (hη : η ≤ 1) : nxCoef σ η 1 ≤ 0 := by
  have : nxCoef σ η 1 = η - 1 := by
    unfold nxCoef varpi
    field_simp
    ring
  linarith

/-- Galí (2015), p. 236, **counterexample (error 2)**: with `σ = 1` and `η = 0.9` the
coefficient `υ(ϖ/σ − 1)` of the terms of trade in (31) is negative for every
`υ ∈ (0, 1]`: a depreciation worsens the trade balance however large `υ` is. -/
theorem nxCoef_counterexample {υ : ℝ} (hυ0 : 0 < υ) (hυ1 : υ ≤ 1) :
    nxCoef 1 (9 / 10) υ < 0 := by
  unfold nxCoef varpi
  norm_num
  nlinarith

/-- Galí (2015), p. 236, **the printed claim is false (error 2)**: it is not true that a
sufficiently large `υ` makes a terms-of-trade depreciation improve the trade balance
(`σ = 1`, `η = 0.9`). -/
theorem not_large_openness_improves :
    ¬ ∃ u0 < (1 : ℝ), ∀ υ, u0 < υ → υ ≤ 1 → 0 < nxCoef 1 (9 / 10) υ := by
  rintro ⟨u0, hu0, h⟩
  have h1 := h 1 hu0 le_rfl
  linarith [nxCoef_counterexample one_pos (le_refl (1 : ℝ))]

/-- Galí (2015), p. 236, **corrected statement (error 2), part 1**: if `η > 1`, the trade
balance improves with a depreciation (`nxCoef > 0`) for all `υ` close enough to `1`. -/
theorem nxCoef_eventually_pos {σ η : ℝ} (hσ : 0 < σ) (hη : 1 < η) :
    ∀ᶠ υ in 𝓝 1, 0 < nxCoef σ η υ := by
  have hc : Continuous fun υ => nxCoef σ η υ := by
    unfold nxCoef varpi
    fun_prop
  have h1 : 0 < nxCoef σ η 1 := by
    have : nxCoef σ η 1 = η - 1 := by
      unfold nxCoef varpi
      field_simp
      ring
    linarith
  exact (hc.tendsto 1).eventually (lt_mem_nhds h1)

/-- Galí (2015), p. 236, **corrected statement (error 2), part 2**: for a given degree of
openness `υ ∈ (0, 1]`, a depreciation improves the trade balance iff
`η > (σ + 1 − υ)/((2 − υ)σ)`. -/
theorem nxCoef_pos_iff {σ η υ : ℝ} (hσ : 0 < σ) (hυ0 : 0 < υ) (hυ1 : υ ≤ 1) :
    0 < nxCoef σ η υ ↔ (σ + 1 - υ) / ((2 - υ) * σ) < η := by
  have e : nxCoef σ η υ = υ / σ * ((2 - υ) * σ * η - (σ + 1 - υ)) := by
    unfold nxCoef varpi
    field_simp
    ring
  have hd : 0 < (2 - υ) * σ := mul_pos (by linarith) hσ
  rw [e, mul_pos_iff_of_pos_left (div_pos hυ0 hσ), div_lt_iff₀ hd]
  constructor <;> intro h <;> linarith

/-! ### The dynamic IS equation (26)–(30) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), **(26)**, p. 235: the Euler equation (11) with CPI inflation, combined with
(13) `π_{t+1} = π_{H,t+1} + υΔs_{t+1}` (and `s` known at `t`), gives the Euler equation in
domestic inflation,
`c_t = E_t c_{t+1} − σ⁻¹(i_t − E_t π_{H,t+1} − ρ) + (υ/σ)E_tΔs_{t+1} + σ⁻¹(1 − ρ_z)z_t`. -/
theorem eq26 {σ υ ρ ρz : ℝ} {c i infl inflH s z : ℕ → Ω → ℝ} (t : ℕ)
    (h11 : c t = 𝔼.E t (c (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - fun _ => ρ)
      + (σ⁻¹ * (1 - ρz)) • z t)
    (h13 : infl (t + 1) = inflH (t + 1) + υ • (s (t + 1) - s t)) (hs : 𝔼.E t (s t) = s t) :
    c t = 𝔼.E t (c (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (inflH (t + 1)) - fun _ => ρ)
      + (υ / σ) • (𝔼.E t (s (t + 1)) - s t) + (σ⁻¹ * (1 - ρz)) • z t := by
  rw [h11, h13, map_add, map_smul, map_sub, hs]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), (27), p. 235, for processes: (17) and (25) at date `t` give
`s_t = σ_υ(y_t − y*_t) − (1 − υ)Φz_t`. -/
theorem eq27_proc {σ η υ : ℝ} (hσ : σ ≠ 0) (hD : 1 + υ * (varpi σ η υ - 1) ≠ 0)
    {c s y ystar z : ℕ → Ω → ℝ} (t : ℕ)
    (h17 : c t = ystar t + σ⁻¹ • z t + ((1 - υ) / σ) • s t)
    (h25 : y t = (1 - υ) • c t + (υ * (2 - υ) * η) • s t + υ • ystar t) :
    s t = sigmaU σ η υ • (y t - ystar t) - ((1 - υ) * Phi σ η υ) • z t := by
  funext ω
  have a := congrFun h17 ω
  have b := congrFun h25 ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b ⊢
  rw [eq27 hσ hD (c := c t ω) (s := s t ω) (y := y t ω) (ystar := ystar t ω) (z := z t ω)
    (by rw [a]; ring) b]

/-- Galí (2015), (26)–(28), p. 235: the algebraic identity behind (28): after substituting
(17) and (27) (at `t` and, in expectation, at `t + 1`, with `E_t z_{t+1} = ρ_z z_t`), the
(26) residual equals `Φ` times the (28) residual. Here `R = i_t − E_t π_{H,t+1} − ρ`. -/
theorem key_eq26_eq28 {σ η υ ρz : ℝ} (hσ : σ ≠ 0) (hD : 1 + υ * (varpi σ η υ - 1) ≠ 0)
    (y Ey ys Eys z R : ℝ) :
    (ys + σ⁻¹ * z + (1 - υ) / σ * (sigmaU σ η υ * (y - ys) - (1 - υ) * Phi σ η υ * z))
      - ((Eys + σ⁻¹ * (ρz * z) + (1 - υ) / σ *
          (sigmaU σ η υ * (Ey - Eys) - (1 - υ) * Phi σ η υ * (ρz * z)))
        - σ⁻¹ * R + υ / σ * ((sigmaU σ η υ * (Ey - Eys) - (1 - υ) * Phi σ η υ * (ρz * z))
          - (sigmaU σ η υ * (y - ys) - (1 - υ) * Phi σ η υ * z)) + σ⁻¹ * (1 - ρz) * z)
    = Phi σ η υ * (y - (Ey - (sigmaU σ η υ)⁻¹ * R + υ * (varpi σ η υ - 1) * (Eys - ys)
        + (1 - υ) / σ * (1 - ρz) * z)) := by
  unfold sigmaU Phi
  field_simp
  ring

/-- Galí (2015), **(28)**, p. 235: given risk sharing (17) and goods-market clearing (25) at
all dates and `E_t z_{t+1} = ρ_z z_t`, the Euler equation (26) holds at `t` **if and only
if** the open-economy dynamic IS equation holds at `t`:
`y_t = E_t y_{t+1} − σ_υ⁻¹(i_t − E_t π_{H,t+1} − ρ) + υ(ϖ − 1)E_tΔy*_{t+1}
+ ((1 − υ)/σ)(1 − ρ_z)z_t`. -/
theorem eq26_iff_eq28 {σ η υ ρ ρz : ℝ} (hσ : σ ≠ 0) (hD : 1 + υ * (varpi σ η υ - 1) ≠ 0)
    {c s y ystar i inflH z : ℕ → Ω → ℝ}
    (h17 : ∀ t, c t = ystar t + σ⁻¹ • z t + ((1 - υ) / σ) • s t)
    (h25 : ∀ t, y t = (1 - υ) • c t + (υ * (2 - υ) * η) • s t + υ • ystar t) (t : ℕ)
    (hz : 𝔼.E t (z (t + 1)) = ρz • z t) :
    (c t = 𝔼.E t (c (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (inflH (t + 1)) - fun _ => ρ)
      + (υ / σ) • (𝔼.E t (s (t + 1)) - s t) + (σ⁻¹ * (1 - ρz)) • z t) ↔
    (y t = 𝔼.E t (y (t + 1)) - (sigmaU σ η υ)⁻¹ • (i t - 𝔼.E t (inflH (t + 1)) - fun _ => ρ)
      + (υ * (varpi σ η υ - 1)) • (𝔼.E t (ystar (t + 1)) - ystar t)
      + ((1 - υ) / σ * (1 - ρz)) • z t) := by
  have hs : ∀ t, s t = sigmaU σ η υ • (y t - ystar t) - ((1 - υ) * Phi σ η υ) • z t :=
    fun t => eq27_proc hσ hD t (h17 t) (h25 t)
  have hc' : 𝔼.E t (c (t + 1)) = 𝔼.E t (ystar (t + 1)) + σ⁻¹ • (ρz • z t)
      + ((1 - υ) / σ) • 𝔼.E t (s (t + 1)) := by
    rw [h17 (t + 1), map_add, map_add, map_smul, map_smul, hz]
  have hs' : 𝔼.E t (s (t + 1)) = sigmaU σ η υ • (𝔼.E t (y (t + 1)) - 𝔼.E t (ystar (t + 1)))
      - ((1 - υ) * Phi σ η υ) • (ρz • z t) := by
    rw [hs (t + 1), map_sub, map_smul, map_smul, map_sub, hz]
  have hΦ : Phi σ η υ ≠ 0 := one_div_ne_zero hD
  rw [hc', hs', h17 t, hs t]
  constructor
  · intro h
    funext ω
    have e := congrFun h ω
    have k := key_eq26_eq28 (ρz := ρz) hσ hD (y t ω) (𝔼.E t (y (t + 1)) ω) (ystar t ω)
      (𝔼.E t (ystar (t + 1)) ω) (z t ω) (i t ω - 𝔼.E t (inflH (t + 1)) ω - ρ)
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    have h0 : Phi σ η υ * (y t ω - (𝔼.E t (y (t + 1)) ω
        - (sigmaU σ η υ)⁻¹ * (i t ω - 𝔼.E t (inflH (t + 1)) ω - ρ)
        + υ * (varpi σ η υ - 1) * (𝔼.E t (ystar (t + 1)) ω - ystar t ω)
        + (1 - υ) / σ * (1 - ρz) * z t ω)) = 0 := by
      linear_combination -k + e
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact absurd h1 hΦ
    · linear_combination h1
  · intro h
    funext ω
    have e := congrFun h ω
    have k := key_eq26_eq28 (ρz := ρz) hσ hD (y t ω) (𝔼.E t (y (t + 1)) ω) (ystar t ω)
      (𝔼.E t (ystar (t + 1)) ω) (z t ω) (i t ω - 𝔼.E t (inflH (t + 1)) ω - ρ)
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    linear_combination k + Phi σ η υ * e

/-- Galí (2015), **(30)**, p. 235: the natural rate of interest of the small open economy,
`rⁿ_t = ρ + σ_υE_tΔyⁿ_{t+1} + σ_υυ(ϖ − 1)E_tΔy*_{t+1} + Φ(1 − υ)(1 − ρ_z)z_t`. -/
noncomputable def natRate (σ η υ ρ ρz : ℝ) (yn ystar z : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (fun _ => ρ) + sigmaU σ η υ • (𝔼.E t (yn (t + 1)) - yn t)
    + (sigmaU σ η υ * (υ * (varpi σ η υ - 1))) • (𝔼.E t (ystar (t + 1)) - ystar t)
    + (Phi σ η υ * (1 - υ) * (1 - ρz)) • z t

/-- Galí (2015), **(29)**, p. 235: with the output gap `ỹ = y − yⁿ`, the dynamic IS equation
(28) at `t` is equivalent to
`ỹ_t = E_t ỹ_{t+1} − σ_υ⁻¹(i_t − E_t π_{H,t+1} − rⁿ_t)`, `rⁿ` as in (30). -/
theorem eq28_iff_eq29 {σ η υ ρ ρz : ℝ} (hσ : σ ≠ 0) (hD : 1 + υ * (varpi σ η υ - 1) ≠ 0)
    {y yn ygap ystar i inflH z : ℕ → Ω → ℝ} (hgap : ∀ t, ygap t = y t - yn t) (t : ℕ) :
    (y t = 𝔼.E t (y (t + 1)) - (sigmaU σ η υ)⁻¹ • (i t - 𝔼.E t (inflH (t + 1)) - fun _ => ρ)
      + (υ * (varpi σ η υ - 1)) • (𝔼.E t (ystar (t + 1)) - ystar t)
      + ((1 - υ) / σ * (1 - ρz)) • z t) ↔
    ygap t = 𝔼.E t (ygap (t + 1))
      - (sigmaU σ η υ)⁻¹ • (i t - 𝔼.E t (inflH (t + 1)) - natRate 𝔼 σ η υ ρ ρz yn ystar z t) := by
  rw [hgap t, hgap (t + 1), map_sub]
  unfold natRate
  have hΦ : Phi σ η υ ≠ 0 := one_div_ne_zero hD
  constructor
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    unfold sigmaU Phi at e ⊢
    field_simp at e ⊢
    linear_combination e
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    unfold sigmaU Phi at e ⊢
    field_simp at e ⊢
    linear_combination e

end Gali.OpenEconomy.AggregateDemand
