/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OpenEconomy.RiskSharing
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Exercise 8.1: a small open economy under financial autarky

Galí (2015), Chapter 8, Exercise 8.1, pp. 258–259. No international trade in assets (trade is
balanced, `p_t + c_t = p_{H,t} + y_t`), a constant world price level (`p*_t = 0`), the CPI
`p_t = (1 − υ) p_{H,t} + υ e_t`, the terms of trade `s_t = e_t − p_{H,t}` with
`s_t = y_t − y*_t` (unit elasticity of substitution), technology `y_t = a_t + n_t`, perfect
competition with flexible prices and wages, labour supply `w_t − p_t = σ c_t + φ n_t`, and money
demand `m_t − p_t = c_t`.

## Microfoundations (necessity and sufficiency)

* `firm_optimum_iff`: under perfect competition and `Y = A N`, hours `N > 0` maximise profits
  iff `W = P_H A`; in logs `w_t − p_{H,t} = a_t` (`firm_log_iff`); profits are then zero.
* `household_optimum_iff`: the household's static problem along its budget line
  `P C = W N + X` is solved at `C, N > 0` iff `W/P = C^σ N^φ` (concavity for sufficiency, the
  first-order condition for necessity; restated from the Chapter 2 project, without the
  preference shifter); `labour_supply_log_iff` gives `w − p = σ c + φ n` exactly.
* `budget_tradeBalance`, `tradeBalance_log_iff`: with no assets, the budget
  `P C = W N + Π` and the firm's profits `Π = P_H Y − W N` give balanced trade `P C = P_H Y`,
  i.e. `p + c = p_H + y` exactly.
* `tot_of_marketClearing`, `tot_log_iff`: with unit-elastic (Cobb–Douglas) demand, goods-market
  clearing `P_H Y = (1 − υ) P C + υ ℰ P* Y*` and balanced trade give `Y = S Y*`, i.e.
  `s = y − y*` (for `υ > 0`); the Cobb–Douglas CPI is exactly log-linear
  (`Identities.log_cpiCD_eq`).

## Part (a)

* `StaticEq`: the exercise's eight log equations at one date and state.
* `staticEq_iff`: they hold iff `y = [(1 + φ) a + υ (1 − σ) y*]/(υ + σ (1 − υ) + φ)`,
  `c = (1 − υ) y + υ y*`, `n = y − a`, `s = y − y*`, `e = m − y*`, `p_H = m − y`,
  `p = m − c`, `w = m − y + a`; `staticEq_existsUnique`, `equilibrium_iff` (processes).
* `denom_pos`: `υ + σ (1 − υ) + φ > 0` for `σ > 0`, `υ ∈ [0, 1]`, `φ ≥ 0`.
* `outputSol_sigma_one`: with `σ = 1`, `y = a` regardless of `y*`; `outputSol_indep_iff`: output
  is independent of world output iff `υ = 0` or `σ = 1`.
* `money_neutral_real`, `exchangeRate_one_for_one`: money is neutral for `y, c, n, s`; the
  nominal exchange rate `e = m − y*` moves one-for-one with money and does not depend on
  technology.

## Part (b)

* `peg_iff`, `peg_existsUnique`, `pegEquilibrium_iff`: under a fixed exchange rate `e_t = ē_t`
  the money supply is endogenous and uniquely equal to `m_t = ē_t + y*_t`; the real allocation
  is the same as in (a) (`peg_same_real_allocation`), and `p_H = ē + y* − y`.

## Part (c)

Part (c) asks for a verbal discussion (imperfect competition, sticky prices); it has no formal
content and is not formalised.
-/

namespace Gali.OpenEconomy.Ex8_1

open Filter Topology

/-! ### The competitive firm -/

/-- Galí (2015), Ex. 8.1, p. 259: profits of a competitive firm with technology `Y = A N`,
`P_H A N − W N`. -/
def profit (PH W A N : ℝ) : ℝ := PH * (A * N) - W * N

/-- Galí (2015), Ex. 8.1, p. 259 (perfect competition, **necessity and sufficiency**): hours
`N > 0` maximise profits over all `N' ≥ 0` iff the wage equals the value of the marginal
product, `W = P_H A`. -/
theorem firm_optimum_iff {PH W A N : ℝ} (hN : 0 < N) :
    (∀ N', 0 ≤ N' → profit PH W A N' ≤ profit PH W A N) ↔ W = PH * A := by
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := h (N + 1) (by linarith)
      unfold profit at this
      nlinarith
    · have := h (N / 2) (by linarith)
      unfold profit at this
      nlinarith
  · intro h N' _
    unfold profit
    rw [h]
    ring_nf
    rfl

/-- Galí (2015), Ex. 8.1, p. 259: at the competitive wage `W = P_H A` profits are zero. -/
theorem profit_zero {PH W A N : ℝ} (h : W = PH * A) : profit PH W A N = 0 := by
  unfold profit; rw [h]; ring

/-- Galí (2015), Ex. 8.1, p. 259 (**exact**): for positive levels, `W = P_H A` iff
`w − p_H = a` in logs. -/
theorem firm_log_iff {PH W A : ℝ} (hPH : 0 < PH) (hW : 0 < W) (hA : 0 < A) :
    W = PH * A ↔ Real.log W - Real.log PH = Real.log A := by
  rw [← Real.log_injOn_pos.eq_iff hW (mul_pos hPH hA), Real.log_mul hPH.ne' hA.ne']
  constructor <;> intro h <;> linarith

/-! ### The household's static problem (restated from the Chapter 2 project) -/

/-- Galí (2015), p. 20 (used in Ex. 8.1): disutility of labour `N^{1+φ}/(1+φ)`. -/
noncomputable def disutilN (φ N : ℝ) : ℝ := N ^ (1 + φ) / (1 + φ)

/-- Galí (2015), p. 20 (used in Ex. 8.1): period utility `u(C) − N^{1+φ}/(1+φ)`, with `u` the
CRRA utility of consumption `RiskSharing.periodUtility`. -/
noncomputable def periodUtility (σ φ C N : ℝ) : ℝ :=
  RiskSharing.periodUtility σ C - disutilN φ N

/-- Galí (2015), eq. (7), p. 21: marginal disutility of labour `N^φ` (restated from the
Chapter 2 project). -/
theorem hasDerivAt_disutilN {φ : ℝ} (hφ : 0 ≤ φ) (N : ℝ) :
    HasDerivAt (disutilN φ) (N ^ φ) N := by
  refine ((Real.hasDerivAt_rpow_const (x := N) (p := 1 + φ) (Or.inr (by linarith))).div_const
    (1 + φ)).congr_deriv ?_
  rw [show (1 : ℝ) + φ - 1 = φ by ring]
  have : (1 : ℝ) + φ ≠ 0 := by linarith
  field_simp

/-- Galí (2015), p. 18: a differentiable function on `(0, ∞)` with nonincreasing derivative
lies below its tangent lines (restated from the Chapter 2 project). -/
theorem le_tangent {f f' : ℝ → ℝ} {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hcont : ContinuousOn f (Set.uIcc x y)) (hd : ∀ z, 0 < z → HasDerivAt f (f' z) z)
    (hanti : AntitoneOn f' (Set.Ioi 0)) : f y ≤ f x + f' x * (y - x) := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' hxy
      (by rwa [Set.uIcc_of_le hxy.le] at hcont) (fun z hz => hd z (hx.trans hz.1))
    have hle : f' c ≤ f' x := hanti hx (hx.trans hc.1) hc.1.le
    have hpos : 0 < y - x := sub_pos.2 hxy
    rw [eq_div_iff hpos.ne'] at hcs
    nlinarith
  · simp
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' hxy
      (by rwa [Set.uIcc_of_ge hxy.le] at hcont) (fun z hz => hd z (lt_of_le_of_lt hy hz.1))
    have hle : f' x ≤ f' c := hanti (lt_of_le_of_lt hy hc.1) hx hc.2.le
    have hpos : 0 < x - y := sub_pos.2 hxy
    rw [eq_div_iff hpos.ne'] at hcs
    nlinarith

/-- Galí (2015), p. 18: the disutility of labour is convex for `φ ≥ 0`:
`v(x) + x^φ (y − x) ≤ v(y)` (restated from the Chapter 2 project). -/
theorem disutilN_tangent_le {φ : ℝ} (hφ : 0 ≤ φ) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    disutilN φ x + x ^ φ * (y - x) ≤ disutilN φ y := by
  have h := le_tangent (f := fun N => -disutilN φ N) (f' := fun N => -N ^ φ) hx hy
    (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 1 + φ)).div_const
      (1 + φ)).neg.continuousOn) (fun z _ => (hasDerivAt_disutilN hφ z).neg)
    (fun a ha b _ hab => neg_le_neg (Real.rpow_le_rpow (le_of_lt ha) hab hφ))
  linarith

/-- Galí (2015), eq. (7), p. 21, used in Ex. 8.1 (**necessity**): if hours `N` are a local
optimum along the budget line `P C = W N + X` with `C > 0`, then `W/P = N^φ C^σ`. -/
theorem static_foc_necessary {σ φ P W X C N : ℝ} (hφ : 0 ≤ φ) (hP : 0 < P) (hC : 0 < C)
    (hbud : P * C = W * N + X)
    (hloc : IsLocalMax (fun N' => periodUtility σ φ ((W * N' + X) / P) N') N) :
    W / P = N ^ φ * C ^ σ := by
  have hCeq : (W * N + X) / P = C := by rw [← hbud]; field_simp
  have hin : HasDerivAt (fun N' : ℝ => (W * N' + X) / P) (W / P) N := by
    have := (((hasDerivAt_id N).const_mul W).add_const X).div_const P
    simpa using this
  have hu : HasDerivAt (RiskSharing.periodUtility σ) (((W * N + X) / P) ^ (-σ))
      ((W * N + X) / P) :=
    RiskSharing.hasDerivAt_periodUtility σ (by rw [hCeq]; exact hC)
  have hg : HasDerivAt (fun N' => periodUtility σ φ ((W * N' + X) / P) N')
      (C ^ (-σ) * (W / P) - N ^ φ) N := by
    have := HasDerivAt.sub (hu.comp N hin) (hasDerivAt_disutilN hφ N)
    rw [hCeq] at this
    exact this
  have h0 := hloc.hasDerivAt_eq_zero hg
  have h1 : C ^ (-σ) * (W / P) = N ^ φ := by linarith
  have hCs : C ^ σ * C ^ (-σ) = 1 := by
    rw [Real.rpow_neg hC.le]
    exact mul_inv_cancel₀ (Real.rpow_pos_of_pos hC σ).ne'
  calc W / P = (C ^ σ * C ^ (-σ)) * (W / P) := by rw [hCs, one_mul]
    _ = N ^ φ * C ^ σ := by rw [mul_assoc, h1, mul_comm]

/-- Galí (2015), p. 19, used in Ex. 8.1: a global optimum of the static problem over feasible
plans (`N' ≥ 0`, `C' = (W N' + X)/P > 0`) with `N, C > 0` is a local optimum along the budget
line (restated from the Chapter 2 project). -/
theorem static_isLocalMax_of_optimal {σ φ P W X C N : ℝ} (hP : 0 < P) (hN : 0 < N)
    (hC : 0 < C) (hbud : P * C = W * N + X)
    (hopt : ∀ N', 0 ≤ N' → 0 < (W * N' + X) / P →
      periodUtility σ φ ((W * N' + X) / P) N' ≤ periodUtility σ φ C N) :
    IsLocalMax (fun N' => periodUtility σ φ ((W * N' + X) / P) N') N := by
  have hCeq : (W * N + X) / P = C := by rw [← hbud]; field_simp
  have hcont : Continuous fun N' : ℝ => (W * N' + X) / P := by fun_prop
  have h1 : ∀ᶠ N' in 𝓝 N, 0 < (W * N' + X) / P :=
    (hcont.tendsto N).eventually_const_lt (by rw [hCeq]; exact hC)
  filter_upwards [h1, eventually_gt_nhds hN] with N' h1' h2'
  rw [hCeq]
  exact hopt N' h2'.le h1'

/-- Galí (2015), eq. (7), p. 21, used in Ex. 8.1 (**sufficiency**, by concavity): if
`W/P = N^φ C^σ` at `(C, N)` with `C, N > 0` on the budget line, then `(C, N)` maximises utility
among all feasible plans. -/
theorem static_foc_sufficient {σ φ P W X C N : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hP : 0 < P)
    (hN : 0 < N) (hC : 0 < C) (hbud : P * C = W * N + X)
    (hfoc : W / P = N ^ φ * C ^ σ) {N' : ℝ} (hN' : 0 ≤ N') (hC' : 0 < (W * N' + X) / P) :
    periodUtility σ φ ((W * N' + X) / P) N' ≤ periodUtility σ φ C N := by
  have hu := RiskSharing.periodUtility_tangent hσ hC' hC
  have hv := disutilN_tangent_le hφ hN hN'
  have hdiff : (W * N' + X) / P - C = W / P * (N' - N) := by
    rw [show C = (W * N + X) / P by rw [← hbud]; field_simp]
    field_simp
    ring
  have hkey : C ^ (-σ) * (W / P) = N ^ φ := by
    rw [hfoc, Real.rpow_neg hC.le]
    field_simp [(Real.rpow_pos_of_pos hC σ).ne']
  unfold periodUtility
  rw [hdiff] at hu
  nlinarith

/-- Galí (2015), Ex. 8.1, p. 259 (labour supply, **necessity and sufficiency**): for `σ > 0`,
`φ ≥ 0`, a point with `C, N > 0` on the budget line `P C = W N + X` solves the household's
static problem iff `W/P = N^φ C^σ`. -/
theorem household_optimum_iff {σ φ P W X C N : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hP : 0 < P)
    (hN : 0 < N) (hC : 0 < C) (hbud : P * C = W * N + X) :
    (∀ N', 0 ≤ N' → 0 < (W * N' + X) / P →
      periodUtility σ φ ((W * N' + X) / P) N' ≤ periodUtility σ φ C N) ↔
      W / P = N ^ φ * C ^ σ :=
  ⟨fun h => static_foc_necessary hφ hP hC hbud (static_isLocalMax_of_optimal hP hN hC hbud h),
    fun h _ hN' hC' => static_foc_sufficient hσ hφ hP hN hC hbud h hN' hC'⟩

/-- Galí (2015), Ex. 8.1, p. 259 (**exact**): for positive levels `W/P = N^φ C^σ` iff
`w − p = σ c + φ n` (restated from the Chapter 2 project). -/
theorem labour_supply_log_iff {σ φ W P C N : ℝ} (hW : 0 < W) (hP : 0 < P) (hC : 0 < C)
    (hN : 0 < N) :
    W / P = N ^ φ * C ^ σ ↔
      Real.log W - Real.log P = σ * Real.log C + φ * Real.log N := by
  have h1 : (0 : ℝ) < W / P := div_pos hW hP
  have h2 : (0 : ℝ) < N ^ φ * C ^ σ :=
    mul_pos (Real.rpow_pos_of_pos hN φ) (Real.rpow_pos_of_pos hC σ)
  rw [← Real.log_injOn_pos.eq_iff h1 h2, Real.log_div hW.ne' hP.ne',
    Real.log_mul (Real.rpow_pos_of_pos hN φ).ne' (Real.rpow_pos_of_pos hC σ).ne',
    Real.log_rpow hN, Real.log_rpow hC]
  constructor <;> intro h <;> linarith

/-! ### Balanced trade, the terms of trade and the CPI -/

/-- Galí (2015), Ex. 8.1, p. 258: with no assets the household spends its wage bill plus the
profits of the domestic firm, `P C = W N + Π` with `Π = P_H Y − W N`; with `Y = A N` this is
balanced trade, `P C = P_H Y`. -/
theorem budget_tradeBalance {P C W N PH A Y : ℝ} (hY : Y = A * N)
    (hbud : P * C = W * N + profit PH W A N) : P * C = PH * Y := by
  rw [hbud, hY]; unfold profit; ring

/-- Galí (2015), Ex. 8.1, p. 258 (**exact**): balanced trade `P C = P_H Y` iff
`p + c = p_H + y` in logs. -/
theorem tradeBalance_log_iff {P C PH Y : ℝ} (hP : 0 < P) (hC : 0 < C) (hPH : 0 < PH)
    (hY : 0 < Y) :
    P * C = PH * Y ↔ Real.log P + Real.log C = Real.log PH + Real.log Y := by
  rw [← Real.log_injOn_pos.eq_iff (mul_pos hP hC) (mul_pos hPH hY), Real.log_mul hP.ne' hC.ne',
    Real.log_mul hPH.ne' hY.ne']

/-- Galí (2015), Ex. 8.1, p. 259 (unit elasticity): with Cobb–Douglas demand, home spending on
home goods is `(1 − υ) P C` and exports are worth `υ ℰ P* Y*`; goods-market clearing
`P_H Y = (1 − υ) P C + υ ℰ P* Y*` and balanced trade `P C = P_H Y` give `P_H Y = ℰ P* Y*`
(`υ > 0`), i.e. `Y = S Y*` with `S = ℰ P*/P_H`. -/
theorem tot_of_marketClearing {υ P C PH Y Ecal Pstar Ystar : ℝ} (hυ : 0 < υ)
    (hmc : PH * Y = (1 - υ) * (P * C) + υ * (Ecal * Pstar * Ystar)) (htb : P * C = PH * Y) :
    PH * Y = Ecal * Pstar * Ystar := by
  rw [htb] at hmc
  have : υ * (PH * Y) = υ * (Ecal * Pstar * Ystar) := by linarith
  exact mul_left_cancel₀ hυ.ne' this

/-- Galí (2015), Ex. 8.1, p. 259 (**exact**): `P_H Y = ℰ P* Y*` iff
`s = e + p* − p_H = y − y*` in logs. -/
theorem tot_log_iff {PH Y Ecal Pstar Ystar : ℝ} (hPH : 0 < PH) (hY : 0 < Y) (hE : 0 < Ecal)
    (hPs : 0 < Pstar) (hYs : 0 < Ystar) :
    PH * Y = Ecal * Pstar * Ystar ↔
      Real.log Ecal + Real.log Pstar - Real.log PH = Real.log Y - Real.log Ystar := by
  rw [← Real.log_injOn_pos.eq_iff (mul_pos hPH hY) (mul_pos (mul_pos hE hPs) hYs),
    Real.log_mul hPH.ne' hY.ne',
    Real.log_mul (mul_pos hE hPs).ne' hYs.ne', Real.log_mul hE.ne' hPs.ne']
  constructor <;> intro h <;> linarith

/-- Galí (2015), Ex. 8.1, p. 259 (**microfoundations of the supply block**): for positive
levels with the no-asset budget `P C = W N + Π`, the firm's optimum and the household's
optimum hold iff, in logs, `w − p_H = a` and `w − p = σ c + φ n` (balanced trade
`p + c = p_H + y` is `tradeBalance_log`). -/
theorem micro_iff {σ φ P C W N PH A : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hP : 0 < P)
    (hC : 0 < C) (hW : 0 < W) (hN : 0 < N) (hPH : 0 < PH) (hA : 0 < A)
    (hbud : P * C = W * N + profit PH W A N) :
    ((∀ N', 0 ≤ N' → profit PH W A N' ≤ profit PH W A N) ∧
      (∀ N', 0 ≤ N' → 0 < (W * N' + profit PH W A N) / P →
        periodUtility σ φ ((W * N' + profit PH W A N) / P) N' ≤ periodUtility σ φ C N)) ↔
      (Real.log W - Real.log PH = Real.log A ∧
        Real.log W - Real.log P = σ * Real.log C + φ * Real.log N) := by
  rw [firm_optimum_iff hN, household_optimum_iff hσ hφ hP hN hC hbud,
    firm_log_iff hPH hW hA, labour_supply_log_iff hW hP hC hN]

/-- Galí (2015), Ex. 8.1, p. 258: balanced trade in logs, `p + c = p_H + y`, for positive
levels satisfying the no-asset budget with `Y = A N`. -/
theorem tradeBalance_log {P C W N PH A Y : ℝ} (hP : 0 < P) (hC : 0 < C) (hPH : 0 < PH)
    (hY0 : 0 < Y) (hY : Y = A * N) (hbud : P * C = W * N + profit PH W A N) :
    Real.log P + Real.log C = Real.log PH + Real.log Y :=
  (tradeBalance_log_iff hP hC hPH hY0).1 (budget_tradeBalance hY hbud)

/-! ### Part (a): the log-linear equilibrium -/

/-- Galí (2015), Ex. 8.1, pp. 258–259: the equilibrium conditions at one date (and state):
balanced trade, the CPI (`p* = 0`), the terms of trade (definition and `s = y − y*`),
technology, labour supply, the competitive firm `w − p_H = a`, and money demand. -/
def StaticEq (υ σ φ a ys m y c n w p pH e s : ℝ) : Prop :=
  p + c = pH + y ∧ p = (1 - υ) * pH + υ * e ∧ s = e - pH ∧ s = y - ys ∧ y = a + n ∧
    w - p = σ * c + φ * n ∧ w - pH = a ∧ m - p = c

/-- Galí (2015), Ex. 8.1(a): the denominator `υ + σ (1 − υ) + φ`. -/
def denom (υ σ φ : ℝ) : ℝ := υ + σ * (1 - υ) + φ

/-- Galí (2015), Ex. 8.1(a): equilibrium output
`y = [(1 + φ) a + υ (1 − σ) y*]/(υ + σ (1 − υ) + φ)`. -/
noncomputable def outputSol (υ σ φ a ys : ℝ) : ℝ :=
  ((1 + φ) * a + υ * (1 - σ) * ys) / denom υ σ φ

/-- Galí (2015), Ex. 8.1(a): `υ + σ (1 − υ) + φ > 0` for `σ > 0`, `0 ≤ υ ≤ 1`, `φ ≥ 0`. -/
theorem denom_pos {υ σ φ : ℝ} (hσ : 0 < σ) (hυ0 : 0 ≤ υ) (hυ1 : υ ≤ 1) (hφ : 0 ≤ φ) :
    0 < denom υ σ φ := by
  unfold denom
  rcases hυ0.lt_or_eq with h | h
  · nlinarith
  · subst h; linarith

/-- Galí (2015), Ex. 8.1(a): in every equilibrium consumption is
`c = (1 − υ) y + υ y*` (from balanced trade, the CPI and the terms of trade). -/
theorem consumption_eq {υ σ φ a ys m y c n w p pH e s : ℝ}
    (h : StaticEq υ σ φ a ys m y c n w p pH e s) : c = (1 - υ) * y + υ * ys := by
  obtain ⟨h1, h2, h3, h4, -, -, -, -⟩ := h
  linear_combination h1 - h2 + υ * h3 - υ * h4

/-- **Ex. 8.1(a)** (Galí 2015, p. 259): with `υ + σ (1 − υ) + φ ≠ 0`, the equilibrium
conditions hold iff `y = [(1 + φ) a + υ (1 − σ) y*]/(υ + σ (1 − υ) + φ)`,
`c = (1 − υ) y + υ y*`, `n = y − a`, `s = y − y*`, `e = m − y*`, `p_H = m − y`, `p = m − c`
and `w = m − y + a`. -/
theorem staticEq_iff {υ σ φ a ys m y c n w p pH e s : ℝ} (hD : denom υ σ φ ≠ 0) :
    StaticEq υ σ φ a ys m y c n w p pH e s ↔
      y = outputSol υ σ φ a ys ∧ c = (1 - υ) * y + υ * ys ∧ n = y - a ∧ s = y - ys ∧
        e = m - ys ∧ pH = m - y ∧ p = m - c ∧ w = m - y + a := by
  constructor
  · intro h
    have hc := consumption_eq h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
    have hy : denom υ σ φ * y = (1 + φ) * a + υ * (1 - σ) * ys := by
      unfold denom
      linear_combination h7 - h6 - h2 + υ * h3 - υ * h4 - σ * hc + φ * h5
    refine ⟨?_, hc, by linarith, h4, ?_, ?_, by linarith, ?_⟩
    · unfold outputSol
      rw [eq_div_iff hD]; linear_combination hy
    · linear_combination (1 - υ) * h4 - hc - h2 + (υ - 1) * h3 - h8
    · linear_combination -υ * h4 - hc - h2 + υ * h3 - h8
    · linear_combination -υ * h4 - hc - h2 + υ * h3 - h8 + h7
  · rintro ⟨hy, hc, hn, hs, he, hpH, hp, hw⟩
    have hyD : denom υ σ φ * y = (1 + φ) * a + υ * (1 - σ) * ys := by
      rw [hy]; unfold outputSol; field_simp
    unfold denom at hyD
    refine ⟨by linarith, ?_, by linarith, hs, by linarith, ?_, by linarith, by linarith⟩
    · rw [hp, hpH, he, hc]; ring
    · rw [hw, hp, hc, hn]
      linear_combination -hyD

/-- Galí (2015), Ex. 8.1(a): for every technology level, world output and money supply there is
exactly one equilibrium `(y, c, n, w, p, p_H, e, s)`. -/
theorem staticEq_existsUnique {υ σ φ : ℝ} (hD : denom υ σ φ ≠ 0) (a ys m : ℝ) :
    ∃ y c n w p pH e s, StaticEq υ σ φ a ys m y c n w p pH e s ∧
      ∀ y' c' n' w' p' pH' e' s', StaticEq υ σ φ a ys m y' c' n' w' p' pH' e' s' →
        y' = y ∧ c' = c ∧ n' = n ∧ w' = w ∧ p' = p ∧ pH' = pH ∧ e' = e ∧ s' = s := by
  set y := outputSol υ σ φ a ys
  set c := (1 - υ) * y + υ * ys
  refine ⟨y, c, y - a, m - y + a, m - c, m - y, m - ys, y - ys,
    (staticEq_iff hD).2 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  intro y' c' n' w' p' pH' e' s' h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := (staticEq_iff hD).1 h
  subst h1
  refine ⟨rfl, h2, h3, h8, ?_, h6, h5, h4⟩
  rw [h7, h2]

/-- Galí (2015), Ex. 8.1(a), p. 259: with `σ = 1` output is `y = a`, independent of world
output (and of `υ`, `φ`, provided `φ ≠ −1`). -/
theorem outputSol_sigma_one {υ φ : ℝ} (hφ : 1 + φ ≠ 0) (a ys : ℝ) :
    outputSol υ 1 φ a ys = a := by
  unfold outputSol denom
  rw [show υ + 1 * (1 - υ) + φ = 1 + φ by ring, show (1 : ℝ) - 1 = 0 by ring]
  field_simp
  ring

/-- Galí (2015), Ex. 8.1(a), p. 259: equilibrium output is independent of world output iff
`υ = 0` (a closed economy) or `σ = 1` (log utility). -/
theorem outputSol_indep_iff {υ σ φ : ℝ} (hD : denom υ σ φ ≠ 0) (a : ℝ) :
    (∀ ys ys', outputSol υ σ φ a ys = outputSol υ σ φ a ys') ↔ υ = 0 ∨ σ = 1 := by
  constructor
  · intro h
    have h01 := h 0 1
    unfold outputSol at h01
    rw [div_left_inj' hD] at h01
    have : υ * (1 - σ) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (h | h) ys ys' <;> unfold outputSol <;> rw [h] <;> ring

/-- Galí (2015), Ex. 8.1(a): the response of output to world output,
`∂y/∂y* = υ (1 − σ)/(υ + σ (1 − υ) + φ)`, negative for `σ > 1` and positive for `σ < 1`
(with `υ > 0` and a positive denominator). -/
theorem outputSol_ystar_slope {υ σ φ : ℝ} (a ys : ℝ) :
    outputSol υ σ φ a ys = outputSol υ σ φ a 0 + υ * (1 - σ) / denom υ σ φ * ys := by
  unfold outputSol; ring

/-- Galí (2015), Ex. 8.1(a): the response of output to technology is
`(1 + φ)/(υ + σ (1 − υ) + φ) > 0`. -/
theorem outputSol_a_slope_pos {υ σ φ : ℝ} (hσ : 0 < σ) (hυ0 : 0 ≤ υ) (hυ1 : υ ≤ 1)
    (hφ : 0 ≤ φ) : 0 < (1 + φ) / denom υ σ φ ∧
      ∀ a ys, outputSol υ σ φ a ys = (1 + φ) / denom υ σ φ * a + outputSol υ σ φ 0 ys := by
  refine ⟨div_pos (by linarith) (denom_pos hσ hυ0 hυ1 hφ), fun a ys => ?_⟩
  unfold outputSol; ring

/-- Galí (2015), Ex. 8.1(a): money is neutral for the real allocation: two equilibria with the
same technology and world output but different money supplies have the same output,
consumption, employment and terms of trade. -/
theorem money_neutral_real {υ σ φ a ys m m' y c n w p pH e s y' c' n' w' p' pH' e' s' : ℝ}
    (hD : denom υ σ φ ≠ 0) (h : StaticEq υ σ φ a ys m y c n w p pH e s)
    (h' : StaticEq υ σ φ a ys m' y' c' n' w' p' pH' e' s') :
    y' = y ∧ c' = c ∧ n' = n ∧ s' = s := by
  obtain ⟨hy, hc, hn, hs, -⟩ := (staticEq_iff hD).1 h
  obtain ⟨hy', hc', hn', hs', -⟩ := (staticEq_iff hD).1 h'
  have e1 : y' = y := hy'.trans hy.symm
  refine ⟨e1, by rw [hc, hc', e1], by rw [hn, hn', e1], by rw [hs, hs', e1]⟩

/-- Galí (2015), Ex. 8.1(a): the nominal exchange rate `e = m − y*` moves one-for-one with the
money supply and does not depend on technology: `e − e' = m − m'` across equilibria with the
same world output. -/
theorem exchangeRate_one_for_one {υ σ φ a a' ys m m' y c n w p pH e s y' c' n' w' p' pH' e'
    s' : ℝ} (hD : denom υ σ φ ≠ 0) (h : StaticEq υ σ φ a ys m y c n w p pH e s)
    (h' : StaticEq υ σ φ a' ys m' y' c' n' w' p' pH' e' s') : e - e' = m - m' := by
  have he := ((staticEq_iff hD).1 h).2.2.2.2.1
  have he' := ((staticEq_iff hD).1 h').2.2.2.2.1
  rw [he, he']; ring

/-! ### Part (a) for processes -/

variable {Ω : Type*}

/-- Galí (2015), Ex. 8.1, pp. 258–259: an equilibrium of the financially autarkic economy:
`StaticEq` holds at every date and state. Prices are flexible and there are no assets, so the
model is static date by date. -/
def Equilibrium (υ σ φ : ℝ) (a ys m y c n w p pH e s : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, StaticEq υ σ φ (a t ω) (ys t ω) (m t ω) (y t ω) (c t ω) (n t ω) (w t ω) (p t ω)
    (pH t ω) (e t ω) (s t ω)

/-- **Ex. 8.1(a)** (Galí 2015, p. 259), processes: with an exogenous money supply the
equilibrium processes are uniquely `y_t = [(1 + φ) a_t + υ (1 − σ) y*_t]/(υ + σ (1 − υ) + φ)`,
`c_t = (1 − υ) y_t + υ y*_t`, `n_t = y_t − a_t`, `s_t = y_t − y*_t`, `e_t = m_t − y*_t`,
`p_{H,t} = m_t − y_t`, `p_t = m_t − c_t`, `w_t = m_t − y_t + a_t`. -/
theorem equilibrium_iff {υ σ φ : ℝ} (hD : denom υ σ φ ≠ 0) {a ys m y c n w p pH e s :
    ℕ → Ω → ℝ} :
    Equilibrium υ σ φ a ys m y c n w p pH e s ↔
      y = (fun t ω => outputSol υ σ φ (a t ω) (ys t ω)) ∧
        c = (fun t => (1 - υ) • y t + υ • ys t) ∧ n = (fun t => y t - a t) ∧
        s = (fun t => y t - ys t) ∧ e = (fun t => m t - ys t) ∧ pH = (fun t => m t - y t) ∧
        p = (fun t => m t - c t) ∧ w = (fun t => m t - y t + a t) := by
  constructor
  · intro h
    have k := fun t ω => (staticEq_iff hD).1 (h t ω)
    refine ⟨funext fun t => funext fun ω => (k t ω).1, funext fun t => funext fun ω => ?_,
      funext fun t => funext fun ω => (k t ω).2.2.1,
      funext fun t => funext fun ω => (k t ω).2.2.2.1,
      funext fun t => funext fun ω => (k t ω).2.2.2.2.1,
      funext fun t => funext fun ω => (k t ω).2.2.2.2.2.1,
      funext fun t => funext fun ω => (k t ω).2.2.2.2.2.2.1,
      funext fun t => funext fun ω => (k t ω).2.2.2.2.2.2.2⟩
    simpa using (k t ω).2.1
  · rintro ⟨hy, hc, hn, hs, he, hpH, hp, hw⟩ t ω
    subst hy hc hn hs he hpH hp hw
    exact (staticEq_iff hD).2 ⟨rfl, by simp, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Part (b): a fixed exchange rate -/

/-- **Ex. 8.1(b)** (Galí 2015, p. 259): under a fixed exchange rate `e = ē` the money supply is
endogenous: the equilibrium conditions with `e = ē` hold iff the money supply is
`m = ē + y*` and the rest of the allocation is as in (a), with `p_H = ē + y* − y`. -/
theorem peg_iff {υ σ φ a ys ebar m y c n w p pH s : ℝ} (hD : denom υ σ φ ≠ 0) :
    StaticEq υ σ φ a ys m y c n w p pH ebar s ↔
      m = ebar + ys ∧ y = outputSol υ σ φ a ys ∧ c = (1 - υ) * y + υ * ys ∧ n = y - a ∧
        s = y - ys ∧ pH = ebar + ys - y ∧ p = ebar + ys - c ∧ w = ebar + ys - y + a := by
  rw [staticEq_iff hD]
  constructor
  · rintro ⟨hy, hc, hn, hs, he, hpH, hp, hw⟩
    exact ⟨by linarith, hy, hc, hn, hs, by linarith, by linarith, by linarith⟩
  · rintro ⟨hm, hy, hc, hn, hs, hpH, hp, hw⟩
    subst hm
    exact ⟨hy, hc, hn, hs, by ring, hpH, hp, hw⟩

/-- **Ex. 8.1(b)** (Galí 2015, p. 259): for every peg `ē` there is exactly one money supply,
`m = ē + y*`, consistent with an equilibrium. -/
theorem peg_existsUnique {υ σ φ : ℝ} (hD : denom υ σ φ ≠ 0) (a ys ebar : ℝ) :
    ∃! m, ∃ y c n w p pH s, StaticEq υ σ φ a ys m y c n w p pH ebar s := by
  refine ⟨ebar + ys, ?_, ?_⟩
  · obtain ⟨y, c, n, w, p, pH, e, s, h, -⟩ := staticEq_existsUnique hD a ys (ebar + ys)
    have he : e = ebar := by
      have := ((staticEq_iff hD).1 h).2.2.2.2.1
      linarith
    subst he
    exact ⟨y, c, n, w, p, pH, s, h⟩
  · rintro m ⟨y, c, n, w, p, pH, s, h⟩
    exact ((peg_iff hD).1 h).1

/-- Galí (2015), Ex. 8.1(b): the peg leaves the real allocation of (a) unchanged: an
equilibrium under the peg and one under any exogenous money supply (same technology and world
output) have the same output, consumption, employment and terms of trade. -/
theorem peg_same_real_allocation {υ σ φ a ys ebar m m' y c n w p pH s y' c' n' w' p' pH' e'
    s' : ℝ} (hD : denom υ σ φ ≠ 0) (h : StaticEq υ σ φ a ys m y c n w p pH ebar s)
    (h' : StaticEq υ σ φ a ys m' y' c' n' w' p' pH' e' s') :
    y' = y ∧ c' = c ∧ n' = n ∧ s' = s :=
  money_neutral_real hD h h'

/-- **Ex. 8.1(b)** (Galí 2015, p. 259), processes: under a fixed exchange-rate regime
`e_t = ē_t` the equilibrium money supply is uniquely `m_t = ē_t + y*_t`; the real allocation is
as in (a) and `p_{H,t} = ē_t + y*_t − y_t`. -/
theorem pegEquilibrium_iff {υ σ φ : ℝ} (hD : denom υ σ φ ≠ 0) {a ys ebar m y c n w p pH s :
    ℕ → Ω → ℝ} :
    Equilibrium υ σ φ a ys m y c n w p pH ebar s ↔
      m = (fun t => ebar t + ys t) ∧ y = (fun t ω => outputSol υ σ φ (a t ω) (ys t ω)) ∧
        c = (fun t => (1 - υ) • y t + υ • ys t) ∧ n = (fun t => y t - a t) ∧
        s = (fun t => y t - ys t) ∧ pH = (fun t => ebar t + ys t - y t) ∧
        p = (fun t => ebar t + ys t - c t) ∧ w = (fun t => ebar t + ys t - y t + a t) := by
  rw [equilibrium_iff hD]
  constructor
  · rintro ⟨hy, hc, hn, hs, he, hpH, hp, hw⟩
    subst he
    refine ⟨funext fun t => (sub_add_cancel _ _).symm, hy, hc, hn, hs, ?_, ?_, ?_⟩
    · rw [hpH]; funext t; rw [sub_add_cancel]
    · rw [hp]; funext t; rw [sub_add_cancel]
    · rw [hw]; funext t; rw [sub_add_cancel]
  · rintro ⟨hm, hy, hc, hn, hs, hpH, hp, hw⟩
    subst hm
    refine ⟨hy, hc, hn, hs, ?_, hpH, hp, hw⟩
    funext t
    exact (add_sub_cancel_right _ _).symm

end Gali.OpenEconomy.Ex8_1
