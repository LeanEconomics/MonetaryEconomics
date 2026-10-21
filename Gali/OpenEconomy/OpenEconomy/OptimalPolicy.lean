/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OpenEconomy.TaylorRule
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Optimal monetary policy in the small open economy: the special case `σ = η = 1`

Galí (2015), Chapter 8, §8.4, pp. 244–249.

## Main results

* **The consumption/output possibilities set** (p. 246). `consumption_possibilities`: with
  `σ = η = 1`, `Z ≡ 1`, `ϑ = 1`, the CPI `P = P_H^{1−υ} P_F^υ` (fn. 2), the risk-sharing
  condition (16) `C = C* 𝒬` with `𝒬 = P_F/P`, `C* = Y*` and market clearing (24)
  `Y = (1−υ)(P_H/P)^{−η} C + υ S^η Y*` imply, **exactly and nonlinearly**, `Y = S Y*`,
  `C S^υ = Y` and `C = Y^{1−υ} (Y*)^υ`.
* **The planner** (p. 246). `plannerWelfare_le`, `plannerWelfare_lt`,
  `planner_optimal_iff`, `planner_existsUnique`: welfare `log C − N^{1+φ}/(1+φ)` along the
  possibilities set is maximised **iff** `C N^φ = (1−υ)(1−α) C/N` (MRS = MRT,
  `hasDerivAt_frontier`) **iff** `N = [(1−υ)(1−α)]^{1/(1+φ)}` (`optEmployment`), the unique
  maximiser, for every realisation of `A` and `Y*`.
* **The flexible-price markup** (p. 246). `markup_eq`: `ℳ = P_H/((1−τ)W/MPN)
  = (1−α)(Y/N)/((1−τ) C N^φ S^υ) = (1−α)/((1−τ) N^{1+φ})`; `printedFirstLine_eq`,
  `printedFirstLine_eq_markup_iff`: the printed first line `P_H/(W/MPN)` omits `(1 − τ)` and
  agrees with the other two only if `τ = 0` (survey error 5).
* **The optimal subsidy** (p. 247). `flexEmployment_eq_opt_iff`: the flexible-price
  allocation is the efficient one **iff** `(1−τ)(1−υ)ℳ = 1`; `flex_optimal`;
  `optSubsidy_lt_closed` (the book's "smaller than necessary to offset market power");
  `optSubsidy_neg_iff`: the "subsidy" is negative **iff** `υ > 1/ε`;
  `optSubsidy_calibration`: at `ε = 9`, `υ = 0.4` it is `τ = −13/27`, a 48% employment
  **tax** (survey error 4).
* **SDIT is optimal** (p. 247). `divine_coincidence`: along a bounded equilibrium of the
  open-economy NKPC (37) and DIS (29), `ỹ ≡ 0 ⟺ π_H ≡ 0`; `optimal_policy`: any
  discounted quadratic loss `∑ βᵗ (a ỹ² + b π_H²)` (`a, b > 0`, the form (43)) is `≥ 0`,
  attained (zero) by SDIT with `i = rⁿ`, and zero loss forces SDIT.
* **Implementation, eq. (42)** (pp. 247–248). `TaylorRule.schurStable_AU_iff` (Bullard–Mitra,
  `σ_υ, κ_υ`), `rule42_unique`: under `i = rⁿ + φ_π π_H` with `φ_π > 1`, `ỹ = π_H = 0`,
  `i = rⁿ` is the **unique** bounded equilibrium; `rule42_not_determinate`: with
  `0 ≤ φ_π ≤ 1` it is not; `exogRule_not_determinate`, `exogRule_not_unique`: `i = rⁿ` is
  indeterminate (another bounded equilibrium next to every one).
* **Macroeconomic implications** (p. 248), for **general** `σ, η` (definitions
  `AggregateDemand.varpi`, `AggregateDemand.Phi`, `AggregateDemand.sigmaU`, `Supply.natDen`,
  `Supply.GammaA`, `Supply.GammaZ`, `Supply.GammaStar` of pp. 235, 238; eq. (27) from (17) and
  (25) is `AggregateDemand.eq27`; the positivity lemmas `..._of_lt_one` cover `η ≥ 0`,
  `0 ≤ υ < 1`): `markup_eq33` (eq. (33)),
  `natural_output_iff` (eq. (35) is the unique flexible-price output), `GammaA_pos_of_lt_one`,
  `natural_tot_eq`, `tot_tech_coeff_pos` (technology ⇒ real depreciation),
  `tot_pref_coeff_neg` (`σ_υ Γ_z − (1−υ)Φ < 0` for **all** admissible parameters, so a
  preference shock appreciates), `dit_exchange_rate_cpi` (`e^{DIT} = sⁿ − p*`,
  `p^{DIT} = υ sⁿ = υ(e^{DIT} + p*)`).
-/

namespace Gali.OpenEconomy.OptimalPolicy

open Filter Topology
open Gali.OpenEconomy.Preferences (cpiCD)
open Gali.OpenEconomy.AggregateDemand (varpi Phi sigmaU one_add_mul_varpi)
open Gali.OpenEconomy.Supply (natDen GammaA GammaZ GammaStar sigma_sub_eq_sigmaU)
open Gali.OpenEconomy.TaylorRule (NKPC omegaU AU stack boundedVec_stack adaptedVec_stack tr2_AU
  det2_AU schurStable_AU_iff)

/-! ### The consumption/output possibilities set (p. 246) -/

/-- Galí (2015), p. 229: the terms of trade `S = P_F/P_H`. -/
noncomputable def tot (PH PF : ℝ) : ℝ := PF / PH

/-- Galí (2015), fn. 2 and p. 230 (`η = 1`, exact): `P_F/P = S^{1−υ}` and `P_H/P = S^{−υ}`. -/
theorem relPrices_cpi {υ PH PF : ℝ} (hH : 0 < PH) (hF : 0 < PF) :
    PF / cpiCD υ PH PF = tot PH PF ^ (1 - υ) ∧ PH / cpiCD υ PH PF = tot PH PF ^ (-υ) := by
  unfold cpiCD tot
  have h1 : PF = PF ^ (1 - υ) * PF ^ υ := by
    rw [← Real.rpow_add hF, sub_add_cancel, Real.rpow_one]
  have h2 : PH = PH ^ (1 - υ) * PH ^ υ := by
    rw [← Real.rpow_add hH, sub_add_cancel, Real.rpow_one]
  have a1 := Real.rpow_pos_of_pos hH (1 - υ)
  have a2 := Real.rpow_pos_of_pos hF υ
  have a3 := Real.rpow_pos_of_pos hH υ
  have a4 := Real.rpow_pos_of_pos hF (1 - υ)
  refine ⟨?_, ?_⟩
  · rw [Real.div_rpow hF.le hH.le, div_eq_div_iff (by positivity) a1.ne']
    nth_rewrite 1 [h1]
    ring
  · rw [Real.rpow_neg (div_pos hF hH).le, Real.div_rpow hF.le hH.le, inv_div,
      div_eq_div_iff (by positivity) a2.ne']
    nth_rewrite 1 [h2]
    ring

/-- Galí (2015), p. 246 (**the exact consumption/output possibilities set**). With
`σ = η = 1`, `Z ≡ 1` and `ϑ = 1`: the CPI (fn. 2), the risk-sharing condition (16)
`C = C* (P_F/P)` (with `P_F = ℰP*`, so `P_F/P` is the real exchange rate), `C* = Y*`
(p. 231) and market clearing (24) `Y = (1−υ)(P_H/P)^{−η} C + υ S^η Y*` imply
`Y = S Y*`, `C S^υ = Y` and `C = Y^{1−υ} (Y*)^υ`, exactly. -/
theorem consumption_possibilities {υ η PH PF C Cstar Ystar Y : ℝ} (hH : 0 < PH) (hF : 0 < PF)
    (hYs : 0 < Ystar) (hη : η = 1) (hrs : C = Cstar * (PF / cpiCD υ PH PF))
    (hCs : Cstar = Ystar)
    (hmc : Y = (1 - υ) * (PH / cpiCD υ PH PF) ^ (-η) * C + υ * tot PH PF ^ η * Ystar) :
    Y = tot PH PF * Ystar ∧ C * tot PH PF ^ υ = Y ∧ C = Y ^ (1 - υ) * Ystar ^ υ := by
  subst hη
  rw [hCs] at hrs
  obtain ⟨e1, e2⟩ := relPrices_cpi (υ := υ) hH hF
  have hS : 0 < tot PH PF := div_pos hF hH
  rw [e1] at hrs
  rw [e2, ← Real.rpow_mul hS.le, Real.rpow_one] at hmc
  have hSS : tot PH PF ^ (-υ * -1) * tot PH PF ^ (1 - υ) = tot PH PF := by
    rw [← Real.rpow_add hS, show -υ * -1 + (1 - υ) = 1 by ring, Real.rpow_one]
  have hCS : C * tot PH PF ^ υ = Ystar * tot PH PF := by
    rw [hrs, mul_assoc, ← Real.rpow_add hS, show 1 - υ + υ = 1 by ring, Real.rpow_one]
  have hY : Y = tot PH PF * Ystar := by
    rw [hmc, hrs]
    linear_combination (1 - υ) * Ystar * hSS
  refine ⟨hY, by rw [hCS, hY]; ring, ?_⟩
  have hSY : tot PH PF = Y / Ystar := by rw [hY]; field_simp
  have hY0 : 0 < Y := by rw [hY]; positivity
  have := Real.rpow_pos_of_pos hYs (1 - υ)
  rw [hrs, hSY, Real.div_rpow hY0.le hYs.le, mul_div_assoc', div_eq_iff this.ne', mul_assoc,
    ← Real.rpow_add hYs, show υ + (1 - υ) = 1 by ring, Real.rpow_one]
  ring

/-- Galí (2015), p. 246, in logs: `log C = (1−υ) log Y + υ log Y*` (exact). -/
theorem log_consumption {υ Y Ystar : ℝ} (hY : 0 < Y) (hYs : 0 < Ystar) :
    Real.log (Y ^ (1 - υ) * Ystar ^ υ) = (1 - υ) * Real.log Y + υ * Real.log Ystar := by
  rw [Real.log_mul (Real.rpow_pos_of_pos hY _).ne' (Real.rpow_pos_of_pos hYs _).ne',
    Real.log_rpow hY, Real.log_rpow hYs]

/-! ### The planner's problem (p. 246) -/

/-- Galí (2015), p. 246: consumption along the possibilities set as a function of employment,
`C(N) = (A N^{1−α})^{1−υ} (Y*)^υ`. -/
noncomputable def frontierC (υ α A Ystar N : ℝ) : ℝ := (A * N ^ (1 - α)) ^ (1 - υ) * Ystar ^ υ

/-- Galí (2015), p. 246: the planner's objective `U(C, N) = log C − N^{1+φ}/(1+φ)` (`σ = 1`,
`Z ≡ 1`) along the possibilities set. -/
noncomputable def plannerWelfare (υ φ α A Ystar N : ℝ) : ℝ :=
  Real.log (frontierC υ α A Ystar N) - N ^ (1 + φ) / (1 + φ)

/-- Galí (2015), p. 246: the efficient level of employment
`N = [(1 − υ)(1 − α)]^{1/(1+φ)}`. -/
noncomputable def optEmployment (υ φ α : ℝ) : ℝ := ((1 - υ) * (1 - α)) ^ (1 + φ)⁻¹

/-- Galí (2015), p. 246: `log C(N) = (1−υ)(log A + (1−α) log N) + υ log Y*`. -/
theorem log_frontierC {υ α A Ystar N : ℝ} (hA : 0 < A) (hYs : 0 < Ystar) (hN : 0 < N) :
    Real.log (frontierC υ α A Ystar N)
      = (1 - υ) * (Real.log A + (1 - α) * Real.log N) + υ * Real.log Ystar := by
  have hY : 0 < A * N ^ (1 - α) := mul_pos hA (Real.rpow_pos_of_pos hN _)
  rw [frontierC, log_consumption hY hYs, Real.log_mul hA.ne' (Real.rpow_pos_of_pos hN _).ne',
    Real.log_rpow hN]

/-- Galí (2015), p. 246: `C(N) > 0`. -/
theorem frontierC_pos {υ α A Ystar N : ℝ} (hA : 0 < A) (hYs : 0 < Ystar) (hN : 0 < N) :
    0 < frontierC υ α A Ystar N :=
  mul_pos (Real.rpow_pos_of_pos (mul_pos hA (Real.rpow_pos_of_pos hN _)) _)
    (Real.rpow_pos_of_pos hYs _)

/-- Galí (2015), p. 246 (**the marginal rate of transformation**): along the possibilities
set `dC/dN = (1−υ)(1−α) C/N`. -/
theorem hasDerivAt_frontier {υ α A Ystar N : ℝ} (hA : 0 < A) (hYs : 0 < Ystar) (hN : 0 < N) :
    HasDerivAt (frontierC υ α A Ystar)
      ((1 - υ) * (1 - α) * frontierC υ α A Ystar N / N) N := by
  set k := (1 - α) * (1 - υ) with hk
  have heq : (fun n => A ^ (1 - υ) * Ystar ^ υ * n ^ k) =ᶠ[𝓝 N] frontierC υ α A Ystar := by
    filter_upwards [Ioi_mem_nhds hN] with n hn
    simp only [frontierC]
    rw [Real.mul_rpow hA.le (Real.rpow_nonneg (le_of_lt hn) _), ← Real.rpow_mul hn.le]
    ring
  refine (((Real.hasDerivAt_rpow_const (p := k) (Or.inl hN.ne')).const_mul
    (A ^ (1 - υ) * Ystar ^ υ)).congr_of_eventuallyEq heq.symm).congr_deriv ?_
  rw [← heq.eq_of_nhds, Real.rpow_sub_one hN.ne', show (1 - υ) * (1 - α) = k by rw [hk]; ring]
  field_simp

/-- Galí (2015), p. 246: the derivative of the planner's objective,
`U_c dC/dN + U_n = (1−υ)(1−α)/N − N^φ` (with `U_c = 1/C`, `U_n = −N^φ`). -/
theorem hasDerivAt_plannerWelfare {υ φ α A Ystar N : ℝ} (hφ : 0 ≤ φ) (hA : 0 < A)
    (hYs : 0 < Ystar) (hN : 0 < N) :
    HasDerivAt (plannerWelfare υ φ α A Ystar) ((1 - υ) * (1 - α) / N - N ^ φ) N := by
  have hC := frontierC_pos (υ := υ) (α := α) hA hYs hN
  have h1 := (hasDerivAt_frontier (υ := υ) (α := α) hA hYs hN).log hC.ne'
  have h2 : HasDerivAt (fun n : ℝ => n ^ (1 + φ) / (1 + φ)) (N ^ φ) N := by
    refine ((Real.hasDerivAt_rpow_const (p := 1 + φ) (Or.inr (by linarith))).div_const
      (1 + φ)).congr_deriv ?_
    rw [show (1 : ℝ) + φ - 1 = φ by ring]
    field_simp
  refine (HasDerivAt.sub h1 h2).congr_deriv ?_
  field_simp

/-- Galí (2015), p. 246: `N^{1+φ} = (1−υ)(1−α)` at the efficient employment level. -/
theorem optEmployment_rpow {υ φ α : ℝ} (hυ : υ < 1) (hα : α < 1) (hφ : 0 ≤ φ) :
    optEmployment υ φ α ^ (1 + φ) = (1 - υ) * (1 - α) := by
  have hk : 0 ≤ (1 - υ) * (1 - α) := mul_nonneg (by linarith) (by linarith)
  rw [optEmployment, Real.rpow_inv_rpow hk (by linarith)]

/-- Galí (2015), p. 246: efficient employment is positive. -/
theorem optEmployment_pos {υ φ α : ℝ} (hυ : υ < 1) (hα : α < 1) : 0 < optEmployment υ φ α :=
  Real.rpow_pos_of_pos (mul_pos (by linarith) (by linarith)) _

/-- Galí (2015), p. 246 (**the optimality condition**): for `C, N > 0`,
`C N^φ = (1−υ)(1−α) C/N` (i.e. `−U_n/U_c = MRT`) **iff** `N = [(1−υ)(1−α)]^{1/(1+φ)}`. -/
theorem foc_iff {υ φ α C N : ℝ} (hυ : υ < 1) (hα : α < 1) (hφ : 0 ≤ φ) (hC : 0 < C)
    (hN : 0 < N) :
    C * N ^ φ = (1 - υ) * (1 - α) * C / N ↔ N = optEmployment υ φ α := by
  have hk : 0 < (1 - υ) * (1 - α) := mul_pos (by linarith) (by linarith)
  have hNN : N ^ (1 + φ) = N ^ φ * N := by
    rw [Real.rpow_add hN, Real.rpow_one, mul_comm]
  constructor
  · intro h
    have h2 : N ^ (1 + φ) = (1 - υ) * (1 - α) := by
      rw [hNN]
      field_simp at h
      nlinarith
    rw [optEmployment, ← h2, Real.rpow_rpow_inv hN.le (by linarith)]
  · intro h
    have h2 : N ^ φ * N = (1 - υ) * (1 - α) := by
      rw [← hNN, h, optEmployment_rpow hυ hα hφ]
    rw [eq_div_iff hN.ne']
    linear_combination C * h2

/-- Galí (2015), p. 246 (**sufficiency, with strictness**): for every `N > 0`,
`W(N) ≤ W(N*)`, with equality only at `N = N*` (strictly below otherwise), where
`N* = [(1−υ)(1−α)]^{1/(1+φ)}`. -/
theorem plannerWelfare_le {υ φ α A Ystar N : ℝ} (hυ : υ < 1) (hα : α < 1) (hφ : 0 ≤ φ)
    (hA : 0 < A) (hYs : 0 < Ystar) (hN : 0 < N) :
    plannerWelfare υ φ α A Ystar N ≤ plannerWelfare υ φ α A Ystar (optEmployment υ φ α) ∧
      (N ≠ optEmployment υ φ α →
        plannerWelfare υ φ α A Ystar N < plannerWelfare υ φ α A Ystar (optEmployment υ φ α)) := by
  set Ns := optEmployment υ φ α with hNs
  have hNs0 : 0 < Ns := optEmployment_pos hυ hα
  have hk : 0 < (1 - υ) * (1 - α) := mul_pos (by linarith) (by linarith)
  have hNk := optEmployment_rpow hυ hα hφ
  rw [← hNs] at hNk
  set x := N / Ns with hx
  have hx0 : 0 < x := div_pos hN hNs0
  have hNx : N = Ns * x := by rw [hx]; field_simp
  have hpow : N ^ (1 + φ) = (1 - υ) * (1 - α) * x ^ (1 + φ) := by
    rw [hNx, Real.mul_rpow hNs0.le hx0.le, hNk]
  have hbern : 1 + (1 + φ) * (x - 1) ≤ x ^ (1 + φ) := by
    have := one_add_mul_self_le_rpow_one_add (s := x - 1) (by linarith) (p := 1 + φ)
      (by linarith)
    simpa using this
  have hlog : Real.log N - Real.log Ns = Real.log x := by
    rw [hx, Real.log_div hN.ne' hNs0.ne']
  have hdiff : plannerWelfare υ φ α A Ystar N - plannerWelfare υ φ α A Ystar Ns
      = (1 - υ) * (1 - α) * (Real.log x - (x ^ (1 + φ) - 1) / (1 + φ)) := by
    unfold plannerWelfare
    rw [log_frontierC hA hYs hN, log_frontierC hA hYs hNs0, hpow, hNk, ← hlog]
    field_simp
    ring
  have hφ1 : (0 : ℝ) < 1 + φ := by linarith
  have hb : x - 1 ≤ (x ^ (1 + φ) - 1) / (1 + φ) := by
    rw [le_div_iff₀ hφ1]
    nlinarith
  constructor
  · have hl := Real.log_le_sub_one_of_pos hx0
    have : plannerWelfare υ φ α A Ystar N - plannerWelfare υ φ α A Ystar Ns ≤ 0 := by
      rw [hdiff]
      exact mul_nonpos_of_nonneg_of_nonpos hk.le (by linarith)
    linarith
  · intro hne
    have hx1 : x ≠ 1 := by
      intro h1
      apply hne
      rw [hNx, h1, mul_one]
    have hl := Real.log_lt_sub_one_of_pos hx0 hx1
    have : plannerWelfare υ φ α A Ystar N - plannerWelfare υ φ α A Ystar Ns < 0 := by
      rw [hdiff]
      exact mul_neg_of_pos_of_neg hk (by linarith)
    linarith

/-- Galí (2015), p. 246 (**necessary and sufficient**): `N > 0` maximises the planner's
objective over all `N' > 0` **iff** the optimality condition `C N^φ = (1−υ)(1−α) C/N` holds
**iff** `N = [(1−υ)(1−α)]^{1/(1+φ)}`. -/
theorem planner_optimal_iff {υ φ α A Ystar N : ℝ} (hυ : υ < 1) (hα : α < 1) (hφ : 0 ≤ φ)
    (hA : 0 < A) (hYs : 0 < Ystar) (hN : 0 < N) :
    ((∀ N', 0 < N' → plannerWelfare υ φ α A Ystar N' ≤ plannerWelfare υ φ α A Ystar N) ↔
      frontierC υ α A Ystar N * N ^ φ = (1 - υ) * (1 - α) * frontierC υ α A Ystar N / N) ∧
    (frontierC υ α A Ystar N * N ^ φ = (1 - υ) * (1 - α) * frontierC υ α A Ystar N / N ↔
      N = optEmployment υ φ α) := by
  have hfoc := foc_iff hυ hα hφ (frontierC_pos (υ := υ) (α := α) hA hYs hN) hN
  refine ⟨?_, hfoc⟩
  rw [hfoc]
  constructor
  · intro hmax
    by_contra hne
    have h1 := (plannerWelfare_le hυ hα hφ hA hYs hN).2 hne
    have h2 := hmax (optEmployment υ φ α) (optEmployment_pos hυ hα)
    linarith
  · rintro rfl N' hN'
    exact (plannerWelfare_le hυ hα hφ hA hYs hN').1

/-- Galí (2015), p. 246 (**existence and uniqueness**): for every realisation of `A > 0` and
`Y* > 0`, exactly one `N > 0` maximises the planner's objective, and it is the constant
`[(1−υ)(1−α)]^{1/(1+φ)}`. -/
theorem planner_existsUnique {υ φ α A Ystar : ℝ} (hυ : υ < 1) (hα : α < 1) (hφ : 0 ≤ φ)
    (hA : 0 < A) (hYs : 0 < Ystar) :
    ∃! N, 0 < N ∧ ∀ N', 0 < N' → plannerWelfare υ φ α A Ystar N' ≤
      plannerWelfare υ φ α A Ystar N := by
  refine ⟨optEmployment υ φ α, ⟨optEmployment_pos hυ hα,
    fun N' hN' => (plannerWelfare_le hυ hα hφ hA hYs hN').1⟩, ?_⟩
  rintro N ⟨hN, hmax⟩
  exact ((planner_optimal_iff hυ hα hφ hA hYs hN).1.trans
    (planner_optimal_iff hυ hα hφ hA hYs hN).2).1 hmax

/-! ### The flexible-price markup and the optimal subsidy (pp. 246–247) -/

/-- Galí (2015), p. 246 (corrected first line): the gross price markup
`ℳ = P_H/((1−τ) W/MPN)`, with marginal cost `(1−τ)W/MPN` net of the employment subsidy. -/
noncomputable def markupH (τ PH W mpn : ℝ) : ℝ := PH / ((1 - τ) * (W / mpn))

/-- Galí (2015), p. 246, first line **as printed**: `P_H/(W/MPN)` (no subsidy). -/
noncomputable def printedFirstLine (PH W mpn : ℝ) : ℝ := PH / (W / mpn)

/-- Galí (2015), p. 246 (**the flexible-price markup**): with `P_H = P S^{−υ}` (fn. 2),
labour supply `W/P = C N^φ` (eq. (7), `σ = 1`), `MPN = (1−α) Y/N` and `C S^υ = Y`
(`consumption_possibilities`), the markup satisfies
`ℳ = (1−α)(Y/N)/((1−τ) C N^φ S^υ) = (1−α)/((1−τ) N^{1+φ})`. -/
theorem markup_eq {υ φ α τ P PH W C N Y S : ℝ} (hP : 0 < P) (hC : 0 < C) (hN : 0 < N)
    (hS : 0 < S) (hτ : τ < 1) (hPH : PH = P * S ^ (-υ)) (hW : W = P * (C * N ^ φ))
    (hCS : C * S ^ υ = Y) :
    markupH τ PH W ((1 - α) * Y / N)
        = (1 - α) * (Y / N) / ((1 - τ) * (C * N ^ φ) * S ^ υ) ∧
      ((1 - α) * (Y / N) / ((1 - τ) * (C * N ^ φ) * S ^ υ)
        = (1 - α) / ((1 - τ) * N ^ (1 + φ))) := by
  have hSu := Real.rpow_pos_of_pos hS υ
  have hNφ := Real.rpow_pos_of_pos hN φ
  have hneg : S ^ (-υ) = (S ^ υ)⁻¹ := Real.rpow_neg hS.le υ
  have h1τ : (1 : ℝ) - τ ≠ 0 := by linarith
  have hNN : N ^ (1 + φ) = N * N ^ φ := by rw [Real.rpow_add hN, Real.rpow_one]
  refine ⟨?_, ?_⟩
  · rcases eq_or_ne α 1 with hα | hα
    · subst hα
      simp [markupH]
    · have h1α : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
      have hY : Y ≠ 0 := by rw [← hCS]; positivity
      unfold markupH
      rw [hPH, hW, hneg]
      field_simp
  · rw [hNN, ← hCS]
    field_simp

/-- Galí (2015), p. 246 (survey error 5): under the same assumptions the printed first line
`P_H/(W/MPN)` equals `(1−α)/N^{1+φ}`, i.e. the markup computed **without** the subsidy. -/
theorem printedFirstLine_eq {υ φ α P PH W C N Y S : ℝ} (hP : 0 < P) (hC : 0 < C) (hN : 0 < N)
    (hS : 0 < S) (hPH : PH = P * S ^ (-υ)) (hW : W = P * (C * N ^ φ))
    (hCS : C * S ^ υ = Y) :
    printedFirstLine PH W ((1 - α) * Y / N) = (1 - α) / N ^ (1 + φ) := by
  have h := (markup_eq (τ := 0) (α := α) hP hC hN hS (by norm_num) hPH hW hCS)
  have e : printedFirstLine PH W ((1 - α) * Y / N) = markupH 0 PH W ((1 - α) * Y / N) := by
    simp [printedFirstLine, markupH]
  rw [e, h.1, h.2]
  simp

/-- Galí (2015), p. 246 (survey error 5): the printed first line agrees with the (correct)
second and third lines **iff** `τ = 0` (given `α < 1`); so with a nonzero subsidy the first
line must read `P_H/((1−τ)W/MPN)`. -/
theorem printedFirstLine_eq_markup_iff {υ φ α τ P PH W C N Y S : ℝ} (hα : α < 1) (hP : 0 < P)
    (hC : 0 < C) (hN : 0 < N) (hS : 0 < S) (hτ : τ < 1) (hPH : PH = P * S ^ (-υ))
    (hW : W = P * (C * N ^ φ)) (hCS : C * S ^ υ = Y) :
    printedFirstLine PH W ((1 - α) * Y / N) = markupH τ PH W ((1 - α) * Y / N) ↔ τ = 0 := by
  rw [printedFirstLine_eq hP hC hN hS hPH hW hCS, (markup_eq hP hC hN hS hτ hPH hW hCS).1,
    (markup_eq hP hC hN hS hτ hPH hW hCS).2]
  have hNφ := Real.rpow_pos_of_pos hN (1 + φ)
  have h1α : (0 : ℝ) < 1 - α := by linarith
  have h1τ : (0 : ℝ) < 1 - τ := by linarith
  constructor
  · intro h
    field_simp at h
    nlinarith
  · rintro rfl
    simp

/-- Galí (2015), p. 246: the desired (flexible-price) gross markup `ℳ = ε/(ε − 1)`. -/
noncomputable def desiredMarkup (ε : ℝ) : ℝ := ε / (ε - 1)

/-- Galí (2015), p. 246: the desired markup exceeds one (`ε > 1`). -/
theorem one_lt_desiredMarkup {ε : ℝ} (hε : 1 < ε) : 1 < desiredMarkup ε := by
  rw [desiredMarkup, one_lt_div (by linarith)]
  linarith

/-- Galí (2015), pp. 246–247: in the flexible-price equilibrium the markup equals `ℳ > 0`,
so `(1−α)/((1−τ)N^{1+φ}) = ℳ`; then the flexible-price allocation is the efficient one
`N = [(1−υ)(1−α)]^{1/(1+φ)}` **iff** `(1−τ)(1−υ)ℳ = 1`. -/
theorem flexEmployment_eq_opt_iff {υ φ α τ M N : ℝ} (hυ : υ < 1) (hα : α < 1) (hφ : 0 ≤ φ)
    (hτ : τ < 1) (hN : 0 < N) (hflex : (1 - α) / ((1 - τ) * N ^ (1 + φ)) = M) :
    N = optEmployment υ φ α ↔ (1 - τ) * (1 - υ) * M = 1 := by
  have hNφ := Real.rpow_pos_of_pos hN (1 + φ)
  have h1τ : (0 : ℝ) < 1 - τ := by linarith
  have h1α : (0 : ℝ) < 1 - α := by linarith
  have h1υ : (0 : ℝ) < 1 - υ := by linarith
  have hf : (1 - α) = M * ((1 - τ) * N ^ (1 + φ)) := by
    rw [← hflex, div_mul_cancel₀]
    positivity
  constructor
  · intro h
    rw [h, optEmployment_rpow hυ hα hφ] at hf
    have : (1 - α) * ((1 - τ) * (1 - υ) * M - 1) = 0 := by linear_combination -hf
    rcases mul_eq_zero.1 this with h0 | h0
    · linarith
    · linarith
  · intro h
    have hN2 : N ^ (1 + φ) = (1 - υ) * (1 - α) := by
      linear_combination (-(1 - υ)) * hf - N ^ (1 + φ) * h
    rw [optEmployment, ← hN2, Real.rpow_rpow_inv hN.le (by linarith)]

/-- Galí (2015), p. 247 (**the flexible-price allocation is optimal**): with
`(1−τ)(1−υ)ℳ = 1`, employment in the flexible-price equilibrium maximises the planner's
objective at every date, whatever the realisations of `A` and `Y*`. -/
theorem flex_optimal {υ φ α τ M N A Ystar : ℝ} (hυ : υ < 1) (hα : α < 1) (hφ : 0 ≤ φ)
    (hτ : τ < 1) (hN : 0 < N) (hA : 0 < A) (hYs : 0 < Ystar)
    (hflex : (1 - α) / ((1 - τ) * N ^ (1 + φ)) = M) (hsub : (1 - τ) * (1 - υ) * M = 1) :
    ∀ N', 0 < N' → plannerWelfare υ φ α A Ystar N' ≤ plannerWelfare υ φ α A Ystar N := by
  have h := (flexEmployment_eq_opt_iff hυ hα hφ hτ hN hflex).2 hsub
  intro N' hN'
  rw [h]
  exact (plannerWelfare_le hυ hα hφ hA hYs hN').1

/-- Galí (2015), p. 247: the optimal employment subsidy `τ = 1 − 1/((1−υ)ℳ)`. -/
noncomputable def optSubsidy (υ M : ℝ) : ℝ := 1 - 1 / ((1 - υ) * M)

/-- Galí (2015), p. 247: `(1−τ)(1−υ)ℳ = 1` **iff** `τ = 1 − 1/((1−υ)ℳ)`. -/
theorem subsidy_iff {υ τ M : ℝ} (hυ : υ < 1) (hM : 0 < M) :
    (1 - τ) * (1 - υ) * M = 1 ↔ τ = optSubsidy υ M := by
  have h : (0 : ℝ) < (1 - υ) * M := mul_pos (by linarith) hM
  unfold optSubsidy
  constructor
  · intro h1
    have h2 : 1 - τ = 1 / ((1 - υ) * M) := by
      rw [eq_div_iff h.ne']
      linear_combination h1
    linarith
  · intro h1
    rw [h1, sub_sub_cancel, mul_assoc, one_div_mul_cancel h.ne']

/-- Galí (2015), p. 247 (**"the required subsidy is smaller than necessary to offset firms'
market power"**): for `0 < υ < 1` and `ℳ > 0`, `1 − 1/((1−υ)ℳ) < 1 − 1/ℳ`, the latter being
the closed-economy subsidy (`(1−τ)ℳ = 1`). -/
theorem optSubsidy_lt_closed {υ M : ℝ} (hυ0 : 0 < υ) (hυ1 : υ < 1) (hM : 0 < M) :
    optSubsidy υ M < 1 - 1 / M := by
  unfold optSubsidy
  have h1 : (1 - υ) * M < M := by nlinarith
  have h2 : 0 < (1 - υ) * M := mul_pos (by linarith) hM
  have := one_div_lt_one_div_of_lt h2 h1
  linarith

/-- Galí (2015), p. 247 (survey error 4): with `ℳ = ε/(ε−1)`, `ε > 1`, `0 ≤ υ < 1`, the
optimal "subsidy" is **negative** (a tax on employment) **iff** `υ > 1/ε`. -/
theorem optSubsidy_neg_iff {υ ε : ℝ} (hε : 1 < ε) (hυ1 : υ < 1) :
    optSubsidy υ (desiredMarkup ε) < 0 ↔ 1 / ε < υ := by
  unfold optSubsidy desiredMarkup
  have hε0 : (0 : ℝ) < ε := by linarith
  have hε1 : (0 : ℝ) < ε - 1 := by linarith
  have h1υ : (0 : ℝ) < 1 - υ := by linarith
  have hpos : 0 < (1 - υ) * (ε / (ε - 1)) := by positivity
  rw [sub_neg, lt_div_iff₀ hpos, div_lt_iff₀ hε0]
  constructor
  · intro h
    have : (1 - υ) * ε < ε - 1 := by
      field_simp at h
      linarith
    linarith
  · intro h
    rw [one_mul, mul_div_assoc', div_lt_one hε1]
    linarith

/-- Galí (2015), pp. 247 and 250 (survey error 4): at the book's calibration `ε = 9`
(`ℳ = 1.125`) and `υ = 0.4` the optimal instrument is `τ = −13/27 ≈ −0.48`: a 48%
employment **tax**, whereas the closed-economy subsidy is `1/9 > 0`. -/
theorem optSubsidy_calibration :
    optSubsidy (2 / 5) (desiredMarkup 9) = -13 / 27 ∧ optSubsidy (2 / 5) (desiredMarkup 9) < 0 ∧
      optSubsidy (2 / 5) (desiredMarkup 9) < -(48 / 100) ∧
      1 - 1 / desiredMarkup 9 = 1 / 9 := by
  unfold optSubsidy desiredMarkup
  norm_num

/-! ### SDIT is optimal (p. 247) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (29), p. 235: the open-economy dynamic IS equation
`ỹ_t = E_t ỹ_{t+1} − σ_υ⁻¹ (i_t − E_t π_{H,t+1} − rⁿ_t)`. -/
def DIS (συ : ℝ) (ygap i inflH rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ygap t = 𝔼.E t (ygap (t + 1)) - συ⁻¹ • (i t - 𝔼.E t (inflH (t + 1)) - rn t)

/-- Galí (2015), p. 247: an equilibrium of the non-policy block, (29) and (37), given the
interest-rate path `i`. -/
def Equilibrium (β συ κυ : ℝ) (rn ygap inflH i : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β κυ ygap inflH ∧ DIS 𝔼 συ ygap i inflH rn

/-- Galí (2015), p. 247: `ỹ ≡ π_H ≡ 0` is an equilibrium **iff** `i_t = rⁿ_t` for all `t`
(`σ_υ ≠ 0`). Adapted from the Chapter 4 project. -/
theorem zero_equilibrium_iff {β συ κυ : ℝ} (hσ : συ ≠ 0) (rn i : ℕ → Ω → ℝ) :
    Equilibrium 𝔼 β συ κυ rn 0 0 i ↔ ∀ t, i t = rn t := by
  constructor
  · rintro ⟨-, hd⟩ t
    have h := hd t
    simp only [Pi.zero_apply, map_zero, zero_sub, sub_zero] at h
    have h2 : συ⁻¹ • (i t - rn t) = 0 := by
      have := congrArg Neg.neg h
      simp only [neg_zero, neg_neg] at this
      exact this.symm
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact absurd (inv_eq_zero.1 h3) hσ
    · exact sub_eq_zero.1 h3
  · intro h
    refine ⟨fun t => by simp, fun t => ?_⟩
    simp [h t]

/-- Galí (2015), p. 247: a closed output gap and bounded domestic inflation force
`π_H ≡ 0` (eq. (37), `|β| < 1`). Adapted from the Chapter 4 project. -/
theorem inflH_zero_of_gap_zero {β κυ : ℝ} (hβ : |β| < 1) {inflH : ℕ → Ω → ℝ}
    (hp : NKPC 𝔼 β κυ 0 inflH) (hb : BoundedProc inflH) : inflH = 0 := by
  have h0 : ∀ t, (0 : ℕ → Ω → ℝ) t = β • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + 0 := fun t => by
    simp
  refine 𝔼.forward_unique hβ (u := 0) (fun t => ?_) h0 hb ⟨0, fun _ _ => by simp⟩
  rw [hp t]
  simp

/-- Galí (2015), p. 247: `π_H ≡ 0` forces `ỹ ≡ 0` (eq. (37), `κ_υ ≠ 0`). -/
theorem gap_zero_of_inflH_zero {β κυ : ℝ} (hκ : κυ ≠ 0) {ygap : ℕ → Ω → ℝ}
    (hp : NKPC 𝔼 β κυ ygap 0) : ygap = 0 := by
  funext t
  have h := hp t
  simp only [Pi.zero_apply, map_zero, smul_zero, zero_add] at h
  rcases smul_eq_zero.1 h.symm with h1 | h1
  · exact absurd h1 hκ
  · exact h1

/-- Galí (2015), p. 247 (**"(37) then implies that domestic prices are also stabilized"**):
along any equilibrium with bounded domestic inflation, `ỹ ≡ 0 ⟺ π_H ≡ 0`, and then
`i = rⁿ`. -/
theorem divine_coincidence {β συ κυ : ℝ} (hβ : |β| < 1) (hσ : συ ≠ 0) (hκ : κυ ≠ 0)
    {rn ygap inflH i : ℕ → Ω → ℝ} (heq : Equilibrium 𝔼 β συ κυ rn ygap inflH i)
    (hb : BoundedProc inflH) :
    (ygap = 0 ↔ inflH = 0) ∧ (ygap = 0 → ∀ t, i t = rn t) := by
  have hiff : ygap = 0 ↔ inflH = 0 := by
    constructor
    · intro hy
      subst hy
      exact inflH_zero_of_gap_zero 𝔼 hβ heq.1 hb
    · intro hπ
      subst hπ
      exact gap_zero_of_inflH_zero 𝔼 hκ heq.1
  refine ⟨hiff, fun hy => ?_⟩
  have hπ := hiff.1 hy
  subst hy
  subst hπ
  exact (zero_equilibrium_iff 𝔼 hσ rn i).1 heq

/-- Galí (2015), eq. (43), p. 249: the discounted quadratic loss along a state `ω`,
`∑ₜ βᵗ (a ỹ_t² + b π_{H,t}²)` (in (43), `a = ((1−υ)/2)(1+φ)/(1−α)`, `b = ((1−υ)/2) ε/λ`). -/
noncomputable def pathLoss (a b β : ℝ) (ygap inflH : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑' t, β ^ t * (a * ygap t ω ^ 2 + b * inflH t ω ^ 2)

omit 𝔼 in
/-- Galí (2015), p. 249: for bounded processes and `0 ≤ β < 1` the loss series converges.
Adapted from the Chapter 4 project. -/
theorem pathLoss_summable {a b β : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {ygap inflH : ℕ → Ω → ℝ} (hy : BoundedProc ygap) (hπ : BoundedProc inflH) (ω : Ω) :
    Summable fun t => β ^ t * (a * ygap t ω ^ 2 + b * inflH t ω ^ 2) := by
  obtain ⟨M₁, hM₁⟩ := hy
  obtain ⟨M₂, hM₂⟩ := hπ
  refine Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hβ0 t)
    (add_nonneg (mul_nonneg ha (sq_nonneg _)) (mul_nonneg hb (sq_nonneg _))))
    (fun t => mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left (sq_le_sq' (abs_le.1 (hM₁ t ω)).1 (abs_le.1 (hM₁ t ω)).2) ha)
      (mul_le_mul_of_nonneg_left (sq_le_sq' (abs_le.1 (hM₂ t ω)).1 (abs_le.1 (hM₂ t ω)).2) hb))
      (pow_nonneg hβ0 t))
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (a * M₁ ^ 2 + b * M₂ ^ 2))

omit 𝔼 in
/-- Galí (2015), p. 249: the loss is nonnegative (`a, b, β ≥ 0`). -/
theorem pathLoss_nonneg {a b β : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hβ0 : 0 ≤ β)
    (ygap inflH : ℕ → Ω → ℝ) (ω : Ω) : 0 ≤ pathLoss a b β ygap inflH ω :=
  tsum_nonneg fun t => mul_nonneg (pow_nonneg hβ0 t)
    (add_nonneg (mul_nonneg ha (sq_nonneg _)) (mul_nonneg hb (sq_nonneg _)))

omit 𝔼 in
/-- Galí (2015), p. 247: SDIT (`ỹ ≡ π_H ≡ 0`) has zero loss. -/
theorem pathLoss_zero (a b β : ℝ) (ω : Ω) : pathLoss a b β (0 : ℕ → Ω → ℝ) 0 ω = 0 := by
  simp [pathLoss]

omit 𝔼 in
/-- Galí (2015), p. 247: with `a, b, β > 0` and a summable loss, the loss is zero **iff**
`ỹ_t(ω) = π_{H,t}(ω) = 0` for all `t`. Adapted from the Chapter 4 project. -/
theorem pathLoss_eq_zero_iff {a b β : ℝ} (ha : 0 < a) (hb : 0 < b) (hβ0 : 0 < β)
    {ygap inflH : ℕ → Ω → ℝ} {ω : Ω}
    (hs : Summable fun t => β ^ t * (a * ygap t ω ^ 2 + b * inflH t ω ^ 2)) :
    pathLoss a b β ygap inflH ω = 0 ↔ ∀ t, ygap t ω = 0 ∧ inflH t ω = 0 := by
  have hnn : ∀ t, 0 ≤ β ^ t * (a * ygap t ω ^ 2 + b * inflH t ω ^ 2) := fun t =>
    mul_nonneg (pow_nonneg hβ0.le t)
      (add_nonneg (mul_nonneg ha.le (sq_nonneg _)) (mul_nonneg hb.le (sq_nonneg _)))
  rw [pathLoss, ← hs.hasSum_iff, hasSum_zero_iff_of_nonneg hnn]
  constructor
  · intro h t
    have h1 := congrFun h t
    simp only [Pi.zero_apply] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (pow_ne_zero _ hβ0.ne')
    · have hy := mul_nonneg ha.le (sq_nonneg (ygap t ω))
      have hπ := mul_nonneg hb.le (sq_nonneg (inflH t ω))
      have e1 : a * ygap t ω ^ 2 = 0 := by linarith
      have e2 : b * inflH t ω ^ 2 = 0 := by linarith
      exact ⟨pow_eq_zero_iff (n := 2) two_ne_zero |>.1
          ((mul_eq_zero.1 e1).resolve_left ha.ne'),
        pow_eq_zero_iff (n := 2) two_ne_zero |>.1 ((mul_eq_zero.1 e2).resolve_left hb.ne')⟩
  · intro h
    funext t
    simp [(h t).1, (h t).2]

/-- Galí (2015), p. 247 and eq. (43), p. 249 (**SDIT is the optimal policy**): for any loss
`∑ βᵗ (a ỹ² + b π_H²)` with `a, b > 0`, `0 < β < 1`: (i) every outcome has nonnegative loss in
every state and in expectation `E_0`, and the SDIT outcome attains the minimum; (ii) SDIT
with `i = rⁿ` is an equilibrium; (iii) any bounded equilibrium with zero loss in every state is
SDIT (`ỹ ≡ π_H ≡ 0`) with `i = rⁿ`. -/
theorem optimal_policy {a b β συ κυ : ℝ} (ha : 0 < a) (hb : 0 < b) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hσ : συ ≠ 0) (rn : ℕ → Ω → ℝ) :
    (∀ ygap inflH : ℕ → Ω → ℝ, (∀ ω, 0 ≤ pathLoss a b β ygap inflH ω) ∧
        ∀ ω, 𝔼.E 0 (pathLoss a b β (0 : ℕ → Ω → ℝ) 0) ω
          ≤ 𝔼.E 0 (pathLoss a b β ygap inflH) ω) ∧
      Equilibrium 𝔼 β συ κυ rn 0 0 rn ∧
      ∀ ygap inflH i : ℕ → Ω → ℝ, Equilibrium 𝔼 β συ κυ rn ygap inflH i →
        BoundedProc ygap → BoundedProc inflH → (∀ ω, pathLoss a b β ygap inflH ω = 0) →
        ygap = 0 ∧ inflH = 0 ∧ ∀ t, i t = rn t := by
  refine ⟨fun ygap inflH => ⟨pathLoss_nonneg ha.le hb.le hβ0.le ygap inflH, fun ω => ?_⟩,
    (zero_equilibrium_iff 𝔼 hσ rn rn).2 fun _ => rfl, ?_⟩
  · have h0 : pathLoss a b β (0 : ℕ → Ω → ℝ) 0 = fun _ => (0 : ℝ) :=
      funext fun ω => pathLoss_zero a b β ω
    have := 𝔼.mono 0 (pathLoss_nonneg ha.le hb.le hβ0.le ygap inflH) ω
    rw [h0]
    simpa [𝔼.const] using this
  · intro ygap inflH i heq hy hπ hzero
    have hall : ∀ t ω, ygap t ω = 0 ∧ inflH t ω = 0 := fun t ω =>
      ((pathLoss_eq_zero_iff ha hb hβ0
        (pathLoss_summable ha.le hb.le hβ0.le hβ1 hy hπ ω)).1 (hzero ω)) t
    have hy0 : ygap = 0 := funext fun t => funext fun ω => (hall t ω).1
    have hπ0 : inflH = 0 := funext fun t => funext fun ω => (hall t ω).2
    refine ⟨hy0, hπ0, ?_⟩
    subst hy0
    subst hπ0
    exact (zero_equilibrium_iff 𝔼 hσ rn i).1 heq

/-! ### Implementation: rule (42) (pp. 247–248) -/

/-- Galí (2015), eq. (42), p. 247, with an optional output-gap response (as in eq. (39)):
`i_t = rⁿ_t + φ_π π_{H,t} + φ_y ỹ_t`; (42) itself is the case `φ_y = 0`. -/
def TaylorRule (φπ φy : ℝ) (i rn inflH ygap : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = rn t + φπ • inflH t + φy • ygap t

/-- Galí (2015), eq. (40), p. 240 (with `rⁿ` in the rule, as in (42)): given the rule, the
NKPC (37) and the DIS (29) hold iff `x_t = A_υ E_t x_{t+1}` (`σ_υ ≠ 0`,
`σ_υ + φ_y + κ_υφ_π ≠ 0`). Adapted from the Chapter 4 project. -/
theorem nk_iff_solves {β συ κυ φπ φy : ℝ} (hσ : συ ≠ 0) (hS : συ + φy + κυ * φπ ≠ 0)
    {rn ygap inflH i : ℕ → Ω → ℝ} (hrule : TaylorRule φπ φy i rn inflH ygap) :
    Equilibrium 𝔼 β συ κυ rn ygap inflH i ↔
      𝔼.Solves (AU β συ κυ φπ φy) 0 (stack ygap inflH) := by
  have hinv : συ * συ⁻¹ = 1 := mul_inv_cancel₀ hσ
  constructor
  · rintro ⟨hp, hd⟩ t j
    funext ω
    have e := congrFun (hd t) ω
    have p := congrFun (hp t) ω
    have r := congrFun (hrule t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e p r
    have s : (συ + φy) * ygap t ω + φπ * inflH t ω
        = συ * 𝔼.E t (ygap (t + 1)) ω + 𝔼.E t (inflH (t + 1)) ω := by
      linear_combination συ * e - r - (i t ω - 𝔼.E t (inflH (t + 1)) ω - rn t ω) * hinv
    fin_cases j
    · simp [stack, AU, omegaU]
      field_simp
      linear_combination s - φπ * p
    · simp [stack, AU, omegaU]
      field_simp
      linear_combination κυ * s + (συ + φy) * p
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have e0 := congrFun (h t 0) ω
      have e1 := congrFun (h t 1) ω
      simp [stack, AU, omegaU] at e0 e1
      field_simp at e0 e1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      apply mul_left_cancel₀ hS
      linear_combination e1 - κυ * e0
    · have e0 := congrFun (h t 0) ω
      have e1 := congrFun (h t 1) ω
      have r := congrFun (hrule t) ω
      simp [stack, AU, omegaU] at e0 e1
      field_simp at e0 e1
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at r ⊢
      have s : (συ + φy) * ygap t ω + φπ * inflH t ω
          = συ * 𝔼.E t (ygap (t + 1)) ω + 𝔼.E t (inflH (t + 1)) ω := by
        apply mul_left_cancel₀ hS
        linear_combination (συ + φy) * e0 + φπ * e1
      rw [r]
      linear_combination συ⁻¹ * s - (ygap t ω - 𝔼.E t (ygap (t + 1)) ω) * hinv

/-- Galí (2015), pp. 247–248 (**rule (42) implements SDIT uniquely**): under
`i_t = rⁿ_t + φ_π π_{H,t} + φ_y ỹ_t` with `κ_υ(φ_π − 1) + (1 − β)φ_y > 0` (in particular
(42), `φ_y = 0`, `φ_π > 1`: `rule42_unique`), the SDIT outcome `ỹ = π_H = 0`, `i = rⁿ` is
the **unique** equilibrium with bounded adapted output gap and domestic inflation. -/
theorem equilibrium_iff_zero {β συ κυ φπ φy : ℝ} (hσ : 0 < συ) (hκ : 0 < κυ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (h41 : 0 < κυ * (φπ - 1) + (1 - β) * φy)
    {rn ygap inflH i : ℕ → Ω → ℝ} (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted inflH)
    (hba : BoundedProc ygap) (hbb : BoundedProc inflH) :
    (Equilibrium 𝔼 β συ κυ rn ygap inflH i ∧ TaylorRule φπ φy i rn inflH ygap) ↔
      ygap = 0 ∧ inflH = 0 ∧ i = rn := by
  have hS : συ + φy + κυ * φπ ≠ 0 := by positivity
  have hr0 : TaylorRule φπ φy rn rn (0 : ℕ → Ω → ℝ) 0 := fun t => by simp
  constructor
  · rintro ⟨he, hr⟩
    have hx := (nk_iff_solves 𝔼 hσ.ne' hS hr).mp he
    have h0 := (nk_iff_solves 𝔼 (β := β) hσ.ne' hS hr0).mp
      ((zero_equilibrium_iff 𝔼 (β := β) (κυ := κυ) hσ.ne' rn rn).2 fun _ => rfl)
    have heq := 𝔼.system_unique ((schurStable_AU_iff hσ hκ hβ0 hβ1 hφπ hφy).mpr h41) hx h0
      (adaptedVec_stack 𝔼 ha hb) (adaptedVec_stack 𝔼 (fun t => by simp) (fun t => by simp))
      (boundedVec_stack hba hbb) (boundedVec_stack ⟨0, fun t ω => by simp⟩
        ⟨0, fun t ω => by simp⟩)
    have h1 : ygap = 0 := funext fun t => by
      simpa [stack] using congrFun (congrFun heq t) 0
    have h2 : inflH = 0 := funext fun t => by
      simpa [stack] using congrFun (congrFun heq t) 1
    refine ⟨h1, h2, funext fun t => ?_⟩
    rw [hr t, h1, h2]
    simp
  · rintro ⟨h1, h2, h3⟩
    rw [h1, h2, h3]
    exact ⟨(zero_equilibrium_iff 𝔼 hσ.ne' rn rn).2 fun _ => rfl, hr0⟩

/-- Galí (2015), eq. (42), pp. 247–248 (**implementation of SDIT**): under
`i_t = rⁿ_t + φ_π π_{H,t}` with `φ_π > 1`, `ỹ = π_H = 0` and `i = rⁿ` is the unique
equilibrium with bounded adapted output gap and domestic inflation; in it the term `φ_π π_H`
vanishes, so `i = rⁿ` (p. 248). -/
theorem rule42_unique {β συ κυ φπ : ℝ} (hσ : 0 < συ) (hκ : 0 < κυ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφπ : 1 < φπ) {rn ygap inflH i : ℕ → Ω → ℝ} (ha : 𝔼.Adapted ygap)
    (hb : 𝔼.Adapted inflH) (hba : BoundedProc ygap) (hbb : BoundedProc inflH) :
    (Equilibrium 𝔼 β συ κυ rn ygap inflH i ∧ TaylorRule φπ 0 i rn inflH ygap) ↔
      ygap = 0 ∧ inflH = 0 ∧ i = rn :=
  equilibrium_iff_zero 𝔼 hσ hκ hβ0 hβ1 (by linarith) le_rfl
    (by have := mul_pos hκ (sub_pos.2 hφπ); linarith) ha hb hba hbb

/-- Galí (2015), p. 247 (sharpness of `φ_π > 1` in (42)): with `0 ≤ φ_π ≤ 1` and `φ_y = 0`
the system (40) is **not** determinate. -/
theorem rule42_not_determinate [Nonempty Ω] {β συ κυ φπ : ℝ} (hσ : 0 < συ) (hκ : 0 < κυ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ0 : 0 ≤ φπ) (hφπ1 : φπ ≤ 1) :
    ¬ 𝔼.Determinate (AU β συ κυ φπ 0) := by
  rw [𝔼.determinate_iff, schurStable_AU_iff hσ hκ hβ0 hβ1 hφπ0 le_rfl]
  have := mul_nonpos_of_nonneg_of_nonpos hκ.le (sub_nonpos.2 hφπ1)
  linarith

/-- Galí (2015), eq. (10) of Ch. 4 with `σ ↦ σ_υ`, `κ ↦ κ_υ` (p. 247): under `i = rⁿ` the
system is `x_t = A_O E_t x_{t+1}`, `A_O = [[1, 1/σ_υ], [κ_υ, β + κ_υ/σ_υ]]`. -/
noncomputable def AO (β συ κυ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 1 / συ; κυ, β + κυ / συ]

/-- Galí (2015), p. 247: under `i = rⁿ`, the NKPC (37) and the DIS (29) hold iff `(ỹ, π_H)`
solves `x_t = A_O E_t x_{t+1}`. Adapted from the Chapter 4 project. -/
theorem nk_iff_solves_exog {β συ κυ : ℝ} {rn ygap inflH : ℕ → Ω → ℝ} :
    Equilibrium 𝔼 β συ κυ rn ygap inflH rn ↔ 𝔼.Solves (AO β συ κυ) 0 (stack ygap inflH) := by
  constructor
  · rintro ⟨hp, hd⟩ t j
    funext ω
    have e := congrFun (hd t) ω
    have p := congrFun (hp t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e p
    fin_cases j
    · simp [stack, AO]
      linear_combination e
    · simp [stack, AO]
      linear_combination p + κυ * e
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have e0 := congrFun (h t 0) ω
      have e1 := congrFun (h t 1) ω
      simp [stack, AO] at e0 e1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e1 - κυ * e0
    · have e0 := congrFun (h t 0) ω
      simp [stack, AO] at e0
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e0

omit 𝔼 in
/-- Galí (2015), p. 247 (via Ch. 4, p. 105): `A_O` fails the Schur–Cohn condition, since
`tr A_O = 1 + det A_O + κ_υ/σ_υ > 1 + det A_O`. -/
theorem not_schurStable_AO {β συ κυ : ℝ} (hσ : 0 < συ) (hκ : 0 < κυ) :
    ¬ SchurStable (tr2 (AO β συ κυ)) (det2 (AO β συ κυ)) := by
  rintro ⟨-, hT⟩
  have htr : tr2 (AO β συ κυ) = 1 + β + κυ / συ := by simp [tr2, AO]; ring
  have hdet : det2 (AO β συ κυ) = β := by simp [det2, AO]; field_simp; ring
  rw [htr, hdet] at hT
  have := div_pos hκ hσ
  have := le_abs_self (1 + β + κυ / συ)
  linarith

/-- Galí (2015), p. 247 (**`i_t = rⁿ_t` is associated with an indeterminate equilibrium**):
for `σ_υ, κ_υ > 0` the system under `i = rⁿ` is not determinate. -/
theorem exogRule_not_determinate [Nonempty Ω] {β συ κυ : ℝ} (hσ : 0 < συ) (hκ : 0 < κυ) :
    ¬ 𝔼.Determinate (AO β συ κυ) := by
  rw [𝔼.determinate_iff]
  exact not_schurStable_AO hσ hκ

/-- Galí (2015), p. 247 (**`i = rⁿ` does not guarantee full price stability**): next to every
equilibrium under `i = rⁿ` with bounded adapted output gap and domestic inflation (e.g. SDIT
itself) there is another one, with a different output gap or domestic inflation path. -/
theorem exogRule_not_unique [Nonempty Ω] {β συ κυ : ℝ} (hσ : 0 < συ) (hκ : 0 < κυ)
    {rn ygap inflH : ℕ → Ω → ℝ} (he : Equilibrium 𝔼 β συ κυ rn ygap inflH rn)
    (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted inflH) (hba : BoundedProc ygap)
    (hbb : BoundedProc inflH) :
    ∃ ygap' inflH', Equilibrium 𝔼 β συ κυ rn ygap' inflH' rn ∧
      𝔼.Adapted ygap' ∧ 𝔼.Adapted inflH' ∧ BoundedProc ygap' ∧ BoundedProc inflH' ∧
      (ygap' ≠ ygap ∨ inflH' ≠ inflH) := by
  have hx := (nk_iff_solves_exog 𝔼).mp he
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ := 𝔼.system_not_unique (not_schurStable_AO hσ hκ) hx
    (adaptedVec_stack 𝔼 ha hb) (boundedVec_stack hba hbb)
  have hst : stack (fun t => y t 0) (fun t => y t 1) = y := by
    funext t j
    fin_cases j <;> rfl
  refine ⟨fun t => y t 0, fun t => y t 1, (nk_iff_solves_exog 𝔼).mpr (hst ▸ hy),
    fun t => hay t 0, fun t => hay t 1, ⟨M, fun t ω => hM t 0 ω⟩,
    ⟨M, fun t ω => hM t 1 ω⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hst, hcon.1, hcon.2]

/-! ### Macroeconomic implications for general `σ, η` (pp. 235, 238, 248) -/

/-- Galí (2015), p. 235: `1 + υ(ϖ − 1) > 0` for `0 ≤ υ < 1`, `σ > 0`, `η ≥ 0`. -/
theorem one_add_mul_varpi_pos_of_lt_one {σ η υ : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hυ0 : 0 ≤ υ)
    (hυ1 : υ < 1) :
    0 < 1 + υ * (varpi σ η υ - 1) := by
  rw [one_add_mul_varpi]
  have h1 : 0 < (1 - υ) ^ 2 := by have : 0 < 1 - υ := by linarith
                                  positivity
  have h2 : 0 ≤ υ * (2 - υ) * (σ * η) :=
    mul_nonneg (mul_nonneg hυ0 (by linarith)) (mul_nonneg hσ.le hη)
  linarith

/-- Galí (2015), p. 235: `Φ > 0`. -/
theorem Phi_pos_of_lt_one {σ η υ : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hυ0 : 0 ≤ υ) (hυ1 : υ < 1) :
    0 < Phi σ η υ :=
  one_div_pos.2 (one_add_mul_varpi_pos_of_lt_one hσ hη hυ0 hυ1)

/-- Galí (2015), p. 235: `σ_υ > 0`. -/
theorem sigmaU_pos_of_lt_one {σ η υ : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hυ0 : 0 ≤ υ) (hυ1 : υ < 1) :
    0 < sigmaU σ η υ :=
  mul_pos hσ (Phi_pos_of_lt_one hσ hη hυ0 hυ1)

/-- Galí (2015), p. 238: the denominator `σ_υ(1 − α) + φ + α` is positive. -/
theorem natDen_pos_of_lt_one {σ η υ φ α : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hυ0 : 0 ≤ υ) (hυ1 : υ < 1)
    (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) : 0 < natDen σ η υ φ α := by
  have := mul_pos (sigmaU_pos_of_lt_one hσ hη hυ0 hυ1) (by linarith : (0 : ℝ) < 1 - α)
  unfold natDen
  linarith

/-- Galí (2015), p. 235, `1/Φ − 1 = υ(ϖ − 1)` (used in (33)). -/
theorem inv_Phi_sub_one {σ η υ : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hυ0 : 0 ≤ υ) (hυ1 : υ < 1) :
    1 / Phi σ η υ - 1 = υ * (varpi σ η υ - 1) := by
  have h := one_add_mul_varpi_pos_of_lt_one hσ hη hυ0 hυ1
  unfold Phi
  field_simp
  ring

/-- Galí (2015), eq. (33), p. 237: the average markup
`μ = −(σc + φn) − υs + a − αn`, with (17), (27) and `y = a + (1 − α)n` (32), equals
`−(σ + (φ+α)/(1−α)) y + υ(ϖ − 1)s + (1 + (φ+α)/(1−α)) a − υz`. -/
theorem markup_eq33 {σ η υ φ α c y ystar s z a n μ : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η)
    (hυ0 : 0 ≤ υ) (hυ1 : υ < 1) (hα1 : α < 1)
    (hμ : μ = -(σ * c + φ * n) - υ * s + a - α * n)
    (h17 : c = ystar + z / σ + (1 - υ) / σ * s)
    (h27 : s = sigmaU σ η υ * (y - ystar) - (1 - υ) * Phi σ η υ * z)
    (h32 : y = a + (1 - α) * n) :
    μ = -(σ + (φ + α) / (1 - α)) * y + υ * (varpi σ η υ - 1) * s +
      (1 + (φ + α) / (1 - α)) * a - υ * z := by
  have hP := Phi_pos_of_lt_one hσ hη hυ0 hυ1
  have hinv := inv_Phi_sub_one hσ hη hυ0 hυ1
  have h1α : (1 : ℝ) - α ≠ 0 := by linarith
  have hn : n = (y - a) / (1 - α) := by rw [h32]; field_simp; ring
  have hys : σ * ystar = σ * y - (s + (1 - υ) * Phi σ η υ * z) / Phi σ η υ := by
    rw [h27]; unfold sigmaU; field_simp; ring
  rw [hμ, h17, hn, ← hinv]
  field_simp
  field_simp at hys
  linear_combination (-(1 - α)) * hys

/-- Galí (2015), eq. (35), p. 238 (**natural output**): at flexible prices the markup gap is
zero, so with `sⁿ = σ_υ(yⁿ − y*) − (1−υ)Φz` (eq. (27)) the flexible-price condition
`0 = −(σ + (φ+α)/(1−α)) yⁿ + υ(ϖ − 1)sⁿ + (1 + (φ+α)/(1−α)) a − υz` (eq. (33)) holds **iff**
`yⁿ = Γ_a a + Γ_z z + Γ_* y*`. -/
theorem natural_output_iff {σ η υ φ α a z ystar yn : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η)
    (hυ0 : 0 ≤ υ) (hυ1 : υ < 1) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 = -(σ + (φ + α) / (1 - α)) * yn +
        υ * (varpi σ η υ - 1) * (sigmaU σ η υ * (yn - ystar) - (1 - υ) * Phi σ η υ * z) +
        (1 + (φ + α) / (1 - α)) * a - υ * z ↔
      yn = GammaA σ η υ φ α * a + GammaZ σ η υ φ α * z + GammaStar σ η υ φ α * ystar := by
  have hkey := sigma_sub_eq_sigmaU (one_add_mul_varpi_pos_of_lt_one hσ hη hυ0 hυ1).ne'
  have hvz : υ * varpi σ η υ * Phi σ η υ
      = υ * ((varpi σ η υ - 1) * ((1 - υ) * Phi σ η υ)) + υ := by
    have h := one_add_mul_varpi_pos_of_lt_one hσ hη hυ0 hυ1
    unfold Phi
    field_simp
    ring
  have hD := natDen_pos_of_lt_one hσ hη hυ0 hυ1 hφ hα0 hα1
  have h1α : (0 : ℝ) < 1 - α := by linarith
  unfold GammaA GammaZ GammaStar
  unfold natDen at hD ⊢
  rw [hvz]
  generalize varpi σ η υ = w at *
  generalize Phi σ η υ = P at *
  generalize sigmaU σ η υ = sU at *
  obtain rfl : σ = sU + υ * (w - 1) * sU := by linarith
  have hc : (sU * (1 - α) + φ + α) / (1 - α) ≠ 0 := (div_pos hD h1α).ne'
  have hid : -(sU + υ * (w - 1) * sU + (φ + α) / (1 - α)) * yn +
        υ * (w - 1) * (sU * (yn - ystar) - (1 - υ) * P * z) + (1 + (φ + α) / (1 - α)) * a -
        υ * z
      = (sU * (1 - α) + φ + α) / (1 - α) *
        ((1 + φ) / (sU * (1 - α) + φ + α) * a +
          -((υ * ((w - 1) * ((1 - υ) * P)) + υ) * (1 - α)) / (sU * (1 - α) + φ + α) * z +
          -(υ * (w - 1) * sU * (1 - α)) / (sU * (1 - α) + φ + α) * ystar - yn) := by
    field_simp
    ring
  rw [hid]
  constructor
  · intro h
    have := (mul_eq_zero.1 h.symm).resolve_left hc
    linarith
  · intro h
    rw [← h]
    ring

/-- Galí (2015), p. 248: `Γ_a > 0`, so domestic (natural) output always rises after a positive
domestic technology shock. -/
theorem GammaA_pos_of_lt_one {σ η υ φ α : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hυ0 : 0 ≤ υ) (hυ1 : υ < 1)
    (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) : 0 < GammaA σ η υ φ α :=
  div_pos (by linarith) (natDen_pos_of_lt_one hσ hη hυ0 hυ1 hφ hα0 hα1)

/-- Galí (2015), p. 248: the natural terms of trade
`sⁿ = σ_υ(yⁿ − y*) − (1−υ)Φz = σ_υΓ_a a + σ_υ(Γ_* − 1)y* + [σ_υΓ_z − (1−υ)Φ]z`. -/
theorem natural_tot_eq (σ η υ φ α a z ystar : ℝ) :
    sigmaU σ η υ * ((GammaA σ η υ φ α * a + GammaZ σ η υ φ α * z +
        GammaStar σ η υ φ α * ystar) - ystar) - (1 - υ) * Phi σ η υ * z
      = sigmaU σ η υ * GammaA σ η υ φ α * a + sigmaU σ η υ * (GammaStar σ η υ φ α - 1) * ystar +
        (sigmaU σ η υ * GammaZ σ η υ φ α - (1 - υ) * Phi σ η υ) * z := by
  ring

/-- Galí (2015), p. 248 (**technology ⇒ real depreciation**): given world output, the
coefficient `σ_υΓ_a` of `a` in `sⁿ` is positive, and so is that of the real exchange rate
`q = (1 − υ)s` (p. 230). -/
theorem tot_tech_coeff_pos {σ η υ φ α : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hυ0 : 0 ≤ υ)
    (hυ1 : υ < 1) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < sigmaU σ η υ * GammaA σ η υ φ α ∧ 0 < (1 - υ) * (sigmaU σ η υ * GammaA σ η υ φ α) := by
  have h := mul_pos (sigmaU_pos_of_lt_one hσ hη hυ0 hυ1)
    (GammaA_pos_of_lt_one hσ hη hυ0 hυ1 hφ hα0 hα1)
  exact ⟨h, mul_pos (by linarith) h⟩

/-- Galí (2015), p. 248 (**preference shocks ⇒ real appreciation, for all parameters**):
`σ_υΓ_z − (1 − υ)Φ < 0` whenever `σ > 0`, `η ≥ 0`, `0 ≤ υ < 1`, `φ ≥ 0`, `0 ≤ α < 1`
(the book asserts the sign without proof; `ϖ` may be negative, but `ϖ ≥ −(1 − υ)`). -/
theorem tot_pref_coeff_neg {σ η υ φ α : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hυ0 : 0 ≤ υ)
    (hυ1 : υ < 1) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    sigmaU σ η υ * GammaZ σ η υ φ α - (1 - υ) * Phi σ η υ < 0 := by
  have hD := natDen_pos_of_lt_one hσ hη hυ0 hυ1 hφ hα0 hα1
  have hP := Phi_pos_of_lt_one hσ hη hυ0 hυ1
  have hS := sigmaU_pos_of_lt_one hσ hη hυ0 hυ1
  have h1α : (0 : ℝ) < 1 - α := by linarith
  have h1υ : (0 : ℝ) < 1 - υ := by linarith
  have hw : 0 ≤ varpi σ η υ + (1 - υ) := by
    have : varpi σ η υ + (1 - υ) = (2 - υ) * (σ * η) := by unfold varpi; ring
    rw [this]
    exact mul_nonneg (by linarith) (mul_nonneg hσ.le hη)
  have k1 : 0 ≤ sigmaU σ η υ * υ * (1 - α) * (varpi σ η υ + (1 - υ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hS.le hυ0) h1α.le) hw
  have k2 : 0 < (1 - υ) ^ 2 * sigmaU σ η υ * (1 - α) := by positivity
  have k3 : 0 ≤ (1 - υ) * (φ + α) := mul_nonneg h1υ.le (by linarith)
  have hkey : 0 < sigmaU σ η υ * υ * varpi σ η υ * (1 - α) + (1 - υ) * natDen σ η υ φ α := by
    have e : sigmaU σ η υ * υ * varpi σ η υ * (1 - α) + (1 - υ) * natDen σ η υ φ α
        = sigmaU σ η υ * υ * (1 - α) * (varpi σ η υ + (1 - υ)) +
          (1 - υ) ^ 2 * sigmaU σ η υ * (1 - α) + (1 - υ) * (φ + α) := by
      unfold natDen; ring
    rw [e]
    linarith
  have e2 : sigmaU σ η υ * GammaZ σ η υ φ α - (1 - υ) * Phi σ η υ
      = -(Phi σ η υ * (sigmaU σ η υ * υ * varpi σ η υ * (1 - α) +
          (1 - υ) * natDen σ η υ φ α) / natDen σ η υ φ α) := by
    unfold GammaZ
    field_simp
    ring
  rw [e2]
  exact neg_neg_of_pos (div_pos (mul_pos hP hkey) hD)

/-- Galí (2015), pp. 238 and 248 (**the special case `σ = η = 1`**): `ϖ = Φ = σ_υ = 1`,
`Γ_a = 1`, `Γ_* = 0`, `Γ_z = −υ(1−α)/(1+φ)`; hence `yⁿ = a − (υ(1−α)/(1+φ)) z` and the
coefficient of `y*` in `sⁿ` is `σ_υ(Γ_* − 1) = −1`. -/
theorem special_case (υ φ α : ℝ) (hφ : 0 ≤ φ) :
    varpi 1 1 υ = 1 ∧ Phi 1 1 υ = 1 ∧ sigmaU 1 1 υ = 1 ∧ GammaA 1 1 υ φ α = 1 ∧
      GammaStar 1 1 υ φ α = 0 ∧ GammaZ 1 1 υ φ α = -(υ * (1 - α)) / (1 + φ) ∧
      sigmaU 1 1 υ * (GammaStar 1 1 υ φ α - 1) = -1 := by
  have hv : varpi 1 1 υ = 1 := by unfold varpi; ring
  have hP : Phi 1 1 υ = 1 := by unfold Phi; rw [hv]; ring
  have hS : sigmaU 1 1 υ = 1 := by unfold sigmaU; rw [hP]; ring
  have hD : natDen 1 1 υ φ α = 1 + φ := by unfold natDen; rw [hS]; ring
  have h1 : (1 : ℝ) + φ ≠ 0 := by linarith
  have hst : GammaStar 1 1 υ φ α = 0 := by unfold GammaStar; rw [hv]; ring
  refine ⟨hv, hP, hS, ?_, hst, ?_, ?_⟩
  · unfold GammaA; rw [hD]; field_simp
  · unfold GammaZ; rw [hD, hv, hP]; ring
  · rw [hS, hst]; ring

/-- Galí (2015), p. 248 (**the nominal exchange rate and the CPI under DIT**). Along a
realisation, let `p_H` start at the normalisation `p_{H,0} = 0` and accumulate domestic
inflation, `p_{H,t+1} = p_{H,t} + π_{H,t+1}`; let `s = e + p* − p_H` (eq. (14)),
`p = p_H + υs` (eq. (12)), and let `s − sⁿ = σ_υ(y − yⁿ)` (eq. (27) at actual and natural
values). Under SDIT (`π_H ≡ 0`, `ỹ ≡ 0`): `e_t = sⁿ_t − p*_t` and
`p_t = υ sⁿ_t = υ(e_t + p*_t)`. -/
theorem dit_exchange_rate_cpi {υ συ : ℝ} {pH inflH s e pstar p sn ygap : ℕ → ℝ}
    (hpH0 : pH 0 = 0) (hpH : ∀ t, pH (t + 1) = pH t + inflH (t + 1))
    (h14 : ∀ t, s t = e t + pstar t - pH t) (h12 : ∀ t, p t = pH t + υ * s t)
    (h27 : ∀ t, s t - sn t = συ * ygap t) (hsdit : ∀ t, inflH t = 0) (hgap : ∀ t, ygap t = 0)
    (t : ℕ) : e t = sn t - pstar t ∧ p t = υ * sn t ∧ p t = υ * (e t + pstar t) := by
  have hp0 : ∀ t, pH t = 0 := by
    intro t
    induction t with
    | zero => exact hpH0
    | succ n ih => rw [hpH n, ih, hsdit]; ring
  have hs : s t = sn t := by have := h27 t; rw [hgap t] at this; linarith
  have he : e t = sn t - pstar t := by have := h14 t; rw [hp0 t] at this; linarith
  refine ⟨he, ?_, ?_⟩
  · rw [h12 t, hp0 t, hs]; ring
  · rw [h12 t, hp0 t, hs, he]; ring

end Gali.OpenEconomy.OptimalPolicy
