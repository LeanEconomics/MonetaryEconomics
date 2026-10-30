/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.TidyR6MoneyHouseholdTree
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Both halves of (22.2) from the derived money model, with explicit remainders

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, eq. (22.2), p. 495 (the
Fisher equation `i_t = E_tπ_{t+1}` and the flow condition
`ρv_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}`), obtained from the nonlinear conditions that the
household problem delivers (`TidyR6MoneyHouseholdEqm`): the bond-pricing equation
`Q_t = βP_tE_t[1/P_{t+1}]` and the government flow `W_t = P_ts̄_t + Q_tW_{t+1}`. The
linearisation follows Cochrane (2023), §3.5, eq. (3.17), p. 63, and Online Appendix eqs.
(1.9)–(1.13), p. 558; its scalar steps (`log_one_add_sub_le` … `remF_bound`) are restated from
the AssetsRulesBalanceSheets project (its module TidyR6Linearise).

Variables: `i_t = −log Q_t` (the log nominal rate), `π_{t+1} = log P_{t+1} − log P_t`, and
`v_t = log(Q_tW_{t+1}/P_t)`, the log market value of debt at the end of `t`.

## Main results

* `flow_log_exact`: the government flow is exactly
  `v_t + i_t − π_{t+1} = log(s̄_{t+1} + e^{v_{t+1}})`, the exact flow (1.9) with zero growth; hence
  (`flow_lin`) `v_t + i_t − π_{t+1} = κ + ρv_{t+1} + s̃_{t+1} + R_{t+1}` with `|R| ≤ 2η² + ρδ_v²`.
* `fisher_scalar`, `fisher_lin_core`, `fisher_lin_meas`: the bond-pricing equation gives
  `i_t + log β = E_tπ_{t+1} + J_t` with the Jensen remainder `|J_t| ≤ 9δ²` when
  `|π_{t+1} − π̄| ≤ δ ≤ 1/4`, on every `ExpectationSystem` with pull-out and almost surely on any
  probability space.
* `consistent_core` (**both halves of (22.2) exactly, with the remainders in the surplus and the
  rate**): on every `ExpectationSystem` with pull-out, the path
  `(π, i + log β − J, v, s̃ + R + κ + log β − J)` satisfies `StarredModel.Consistent` exactly.
* Links to the derived equilibrium: `derived_lin_meas` (any probability space, almost surely) and
  `derived_consistent_tree` (every finite tree, every node, `StarredModel.Consistent` for the
  tree's expectation system).
-/

namespace Cochrane.ObservationalEquivalence.TidyR6MoneyHouseholdFlowLin

open Real Filter Topology MeasureTheory
open Cochrane.ObservationalEquivalence.ExpectationsMeasure
open Cochrane.ObservationalEquivalence.TidyR6MoneyHousehold
open Cochrane.ObservationalEquivalence.TidyR6MoneyHouseholdEqm

/-! ### The scalar linearisation with an explicit remainder (restated) -/

/-- Cochrane (2023), Online Appendix eq. (1.9), p. 558 (Taylor step for the logarithm; restated
from the AssetsRulesBalanceSheets project): for
`|u| ≤ 1/2`, `|log(1 + u) − u| ≤ 2u²`. -/
theorem log_one_add_sub_le {u : ℝ} (hu : |u| ≤ 1 / 2) : |log (1 + u) - u| ≤ 2 * u ^ 2 := by
  have hx : |(-u)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero,
    div_one, sub_neg_eq_add, abs_neg] at h
  have e : -u + log (1 + u) = log (1 + u) - u := by ring
  rw [e] at h
  refine h.trans ?_
  have h1 : 1 / 2 ≤ 1 - |u| := by linarith
  rw [div_le_iff₀ (by linarith), sq_abs]
  nlinarith [sq_nonneg u]

/-- Cochrane (2023), Online Appendix eq. (1.9), p. 558 (Taylor step for the exponential): for `|z| ≤
1`, `|eᶻ − 1| ≤ 2|z|`. Restated from the AssetsRulesBalanceSheets project. -/
theorem exp_sub_one_le {z : ℝ} (hz : |z| ≤ 1) : |exp z - 1| ≤ 2 * |z| := by
  have h := Real.abs_exp_sub_one_sub_id_le hz
  have h2 : z ^ 2 ≤ |z| := by
    rw [← sq_abs]
    nlinarith [abs_nonneg z]
  calc |exp z - 1| = |(exp z - 1 - z) + z| := by ring_nf
    _ ≤ |exp z - 1 - z| + |z| := abs_add_le _ _
    _ ≤ 2 * |z| := by linarith

/-- Cochrane (2023), Online Appendix eqs. (1.9)–(1.11), p. 558 (**the linearisation with
remainder**): for `c > 0`, `A = c + ȳ > 0`, `|z| ≤ 1` and `u = (c(eᶻ − 1) + (y − ȳ))/A` with `|u| ≤
1/2`, `log(c eᶻ + y) = log A + (c/A) z + (y − ȳ)/A + R` with `|R| ≤ 2u² + (c/A) z²`. Restated from
the AssetsRulesBalanceSheets project. -/
theorem log_lin {c ybar z y : ℝ} (hc : 0 < c) (hA : 0 < c + ybar) (hz : |z| ≤ 1)
    (hu : |(c * (exp z - 1) + (y - ybar)) / (c + ybar)| ≤ 1 / 2) :
    |log (c * exp z + y) - (log (c + ybar) + c / (c + ybar) * z + (y - ybar) / (c + ybar))| ≤
      2 * ((c * (exp z - 1) + (y - ybar)) / (c + ybar)) ^ 2 + c / (c + ybar) * z ^ 2 := by
  set A := c + ybar with hAdef
  set u := (c * (exp z - 1) + (y - ybar)) / A with hudef
  have hu1 : 0 < 1 + u := by
    have := neg_abs_le u
    linarith
  have he : c * exp z + y = A * (1 + u) := by
    rw [hudef]
    field_simp
    ring
  have hlog : log (c * exp z + y) = log A + log (1 + u) := by
    rw [he, Real.log_mul hA.ne' hu1.ne']
  have hdiff : log (c * exp z + y) - (log A + c / A * z + (y - ybar) / A) =
      (log (1 + u) - u) + c / A * (exp z - 1 - z) := by
    rw [hlog, hudef]
    field_simp
    ring
  rw [hdiff]
  have hρ : 0 < c / A := div_pos hc hA
  calc |(log (1 + u) - u) + c / A * (exp z - 1 - z)|
      ≤ |log (1 + u) - u| + |c / A * (exp z - 1 - z)| := abs_add_le _ _
    _ ≤ 2 * u ^ 2 + c / A * z ^ 2 := by
      refine add_le_add (log_one_add_sub_le hu) ?_
      rw [abs_mul, abs_of_pos hρ]
      exact mul_le_mul_of_nonneg_left (Real.abs_exp_sub_one_sub_id_le hz) hρ.le

/-- Cochrane (2023), Online Appendix eqs. (1.9)–(1.11), p. 558 (**the explicit second-order
bound**): with `ρ = c/A`, if `|z| ≤ δ_z ≤ 1`, `|y − ȳ| ≤ δ_y` and `η = 2ρδ_z + δ_y/A ≤ 1/2`, the
remainder of `log_lin` is at most `2η² + ρδ_z²`. Restated from the AssetsRulesBalanceSheets project.
-/
theorem log_lin_bound {c ybar z y δz δy : ℝ} (hc : 0 < c) (hA : 0 < c + ybar) (hz : |z| ≤ δz)
    (hδz : δz ≤ 1) (hy : |y - ybar| ≤ δy)
    (hη : 2 * (c / (c + ybar)) * δz + δy / (c + ybar) ≤ 1 / 2) :
    |log (c * exp z + y) - (log (c + ybar) + c / (c + ybar) * z + (y - ybar) / (c + ybar))| ≤
      2 * (2 * (c / (c + ybar)) * δz + δy / (c + ybar)) ^ 2 + c / (c + ybar) * δz ^ 2 := by
  set A := c + ybar with hAdef
  have hρ : 0 < c / A := div_pos hc hA
  have hz1 : |z| ≤ 1 := hz.trans hδz
  have hδz0 : 0 ≤ δz := (abs_nonneg z).trans hz
  have hδy0 : 0 ≤ δy := (abs_nonneg _).trans hy
  have hu : |(c * (exp z - 1) + (y - ybar)) / A| ≤ 2 * (c / A) * δz + δy / A := by
    rw [add_div]
    have h1 : |c * (exp z - 1) / A| ≤ 2 * (c / A) * δz := by
      rw [abs_div, abs_of_pos hA, abs_mul, abs_of_pos hc]
      have := exp_sub_one_le hz1
      rw [div_le_iff₀ hA]
      have : c * |exp z - 1| ≤ c * (2 * δz) :=
        mul_le_mul_of_nonneg_left (this.trans (by linarith)) hc.le
      have e : 2 * (c / A) * δz * A = c * (2 * δz) := by field_simp
      linarith
    have h2 : |(y - ybar) / A| ≤ δy / A := by
      rw [abs_div, abs_of_pos hA]
      exact div_le_div_of_nonneg_right hy hA.le
    calc |c * (exp z - 1) / A + (y - ybar) / A| ≤ |c * (exp z - 1) / A| + |(y - ybar) / A| :=
          abs_add_le _ _
      _ ≤ 2 * (c / A) * δz + δy / A := add_le_add h1 h2
      _ = 2 * (c / A) * δz + δy / A := rfl
  have hu' : |(c * (exp z - 1) + (y - ybar)) / A| ≤ 1 / 2 := hu.trans hη
  refine (log_lin hc hA hz1 hu').trans (add_le_add ?_ ?_)
  · have h0 : 0 ≤ |(c * (exp z - 1) + (y - ybar)) / A| := abs_nonneg _
    have := pow_le_pow_left₀ h0 hu 2
    rw [sq_abs] at this
    linarith
  · refine mul_le_mul_of_nonneg_left ?_ hρ.le
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg z) hz 2

/-- Cochrane (2023), Online Appendix eq. (1.11), p. 558: the linear coefficients are the exact
partial derivatives at the expansion point: `∂/∂z log(c eᶻ + ȳ)|_{z=0} = c/A` and `∂/∂y log(c +
y)|_{y=ȳ} = 1/A`. Restated from the AssetsRulesBalanceSheets project. -/
theorem log_lin_hasDerivAt {c ybar : ℝ} (hA : 0 < c + ybar) :
    HasDerivAt (fun z => log (c * exp z + ybar)) (c / (c + ybar)) 0 ∧
      HasDerivAt (fun y => log (c + y)) (1 / (c + ybar)) ybar := by
  constructor
  · have h1 : HasDerivAt (fun z => c * exp z + ybar) (c * exp 0) 0 :=
      ((hasDerivAt_exp 0).const_mul c).add_const ybar
    have h2 := h1.log (by simpa using hA.ne')
    simpa using h2
  · have h1 : HasDerivAt (fun y => c + y) 1 ybar := (hasDerivAt_id ybar).const_add c
    have h2 := h1.log (by simpa using hA.ne')
    simpa using h2

/-! ### The flow identity (3.17), restated -/

/-- Cochrane (2023), Online Appendix eq. (1.11), p. 558: `A = e^{v̄} + s̄y`. Restated from the
AssetsRulesBalanceSheets project. -/
noncomputable def A0 (vbar sybar : ℝ) : ℝ := exp vbar + sybar

/-- Cochrane (2023), Online Appendix eq. (1.12), p. 558: the linearisation constant `ρ =
e^{v̄}/(e^{v̄} + s̄y)` (`= e^{−(r − g)}` at a steady state). Restated from the
AssetsRulesBalanceSheets project. -/
noncomputable def rho (vbar sybar : ℝ) : ℝ := exp vbar / A0 vbar sybar

/-- Cochrane (2023), Online Appendix eq. (1.11), p. 558: the constant of the linearised flow, `κ =
log A − ρ v̄ − s̄y/A`. Restated from the AssetsRulesBalanceSheets project. -/
noncomputable def kap (vbar sybar : ℝ) : ℝ :=
  log (A0 vbar sybar) - rho vbar sybar * vbar - sybar / A0 vbar sybar

/-- Cochrane (2023), Online Appendix eq. (1.13), p. 558: the scaled surplus `s̃ = sy/A = ρ
sy/e^{v̄}`. Restated from the AssetsRulesBalanceSheets project. -/
noncomputable def stil {Ω : Type*} (vbar sybar : ℝ) (sy : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  sy t ω / A0 vbar sybar

/-- Cochrane (2023), Online Appendix eqs. (1.9)–(1.13), p. 558: the remainder of the linearised
flow, `R_t = log(sy_t + e^{v_t}) − κ − ρ v_t − s̃_t`. Restated from the AssetsRulesBalanceSheets
project. -/
noncomputable def remF {Ω : Type*} (vbar sybar : ℝ) (v sy : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  log (sy t ω + exp (v t ω)) - kap vbar sybar - rho vbar sybar * v t ω - stil vbar sybar sy t ω

/-- Cochrane (2023), Online Appendix eq. (1.12), p. 558: for a positive steady-state surplus `s̄y >
0`, `0 < ρ < 1` and `A > 0`. Restated from the AssetsRulesBalanceSheets project. -/
theorem rho_mem {vbar sybar : ℝ} (hs : 0 < sybar) :
    0 < A0 vbar sybar ∧ 0 < rho vbar sybar ∧ rho vbar sybar < 1 := by
  have he := exp_pos vbar
  have hA : 0 < A0 vbar sybar := by unfold A0; linarith
  refine ⟨hA, div_pos he hA, ?_⟩
  rw [rho, div_lt_one hA]
  unfold A0
  linarith

/-- Cochrane (2023), eq. (3.17), p. 63, and Online Appendix eq. (1.11), p. 558 (**the linearised
flow, exactly**): if the exact flow (1.9) `v_t + r_{t+1} − g_{t+1} = log(sy_{t+1} + e^{v_{t+1}})`
holds, then `v_t + r_{t+1} − g_{t+1} = κ + ρ v_{t+1} + s̃_{t+1} + R_{t+1}` with `R = remF`. Restated
from the AssetsRulesBalanceSheets project. -/
theorem flow_exact {Ω : Type*} {vbar sybar : ℝ} {v r g sy : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (h : v t ω + r (t + 1) ω - g (t + 1) ω = log (sy (t + 1) ω + exp (v (t + 1) ω))) :
    v t ω + r (t + 1) ω - g (t + 1) ω = kap vbar sybar + rho vbar sybar * v (t + 1) ω +
      stil vbar sybar sy (t + 1) ω + remF vbar sybar v sy (t + 1) ω := by
  rw [h]
  unfold remF
  ring

/-- Cochrane (2023), Online Appendix eqs. (1.9)–(1.13), p. 558 (**the remainder bound**): if `|v_t −
v̄| ≤ δ_v ≤ 1`, `|sy_t − s̄y| ≤ δ_s` and `η = 2ρδ_v + δ_s/A ≤ 1/2`, then `|R_t| ≤ 2η² + ρδ_v²`.
Restated from the AssetsRulesBalanceSheets project. -/
theorem remF_bound {Ω : Type*} {vbar sybar δv δs : ℝ} (hs : 0 < sybar) {v sy : ℕ → Ω → ℝ}
    {t : ℕ} {ω : Ω} (hv : |v t ω - vbar| ≤ δv) (hδv : δv ≤ 1) (hsy : |sy t ω - sybar| ≤ δs)
    (hη : 2 * rho vbar sybar * δv + δs / A0 vbar sybar ≤ 1 / 2) :
    |remF vbar sybar v sy t ω| ≤
      2 * (2 * rho vbar sybar * δv + δs / A0 vbar sybar) ^ 2 + rho vbar sybar * δv ^ 2 := by
  have hA : 0 < exp vbar + sybar := (rho_mem (vbar := vbar) hs).1
  have h := log_lin_bound (c := exp vbar) (ybar := sybar) (z := v t ω - vbar) (y := sy t ω)
    (exp_pos vbar) hA hv hδv hsy hη
  have e1 : exp vbar * exp (v t ω - vbar) + sy t ω = sy t ω + exp (v t ω) := by
    rw [← exp_add]
    ring_nf
  rw [e1] at h
  have e2 : remF vbar sybar v sy t ω = log (sy t ω + exp (v t ω)) -
      (log (exp vbar + sybar) + exp vbar / (exp vbar + sybar) * (v t ω - vbar) +
        (sy t ω - sybar) / (exp vbar + sybar)) := by
    unfold remF kap stil rho A0
    field_simp
    ring
  rw [e2]
  exact h


/-! ### The model's variables -/

/-- Cochrane (2023), eq. (22.2), p. 495: the log nominal rate `i_t = −log Q_t`. -/
noncomputable def iL {Ω : Type*} (Q : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ := -log (Q t ω)

/-- Cochrane (2023), eq. (22.2), p. 495: log inflation `π_t = log P_t − log P_{t−1}` (`0` at
date `0`). -/
noncomputable def piL {Ω : Type*} (P : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  log (P t ω) - log (P (t - 1) ω)

/-- Cochrane (2023), eq. (22.2), p. 495: the log market value of debt at the end of `t`,
`v_t = log(Q_tW_{t+1}/P_t)`. -/
noncomputable def vL {Ω : Type*} (P Q W : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  log (Q t ω * W (t + 1) ω / P t ω)

/-- Cochrane (2023), eq. (22.2), p. 495, and (1.9), p. 558 (**the exact flow in logs**): if
`W_{t+1} = P_{t+1}s̄_{t+1} + Q_{t+1}W_{t+2}` with positive prices, bond prices and liabilities,
then `v_t + i_t − π_{t+1} = log(s̄_{t+1} + e^{v_{t+1}})`. -/
theorem flow_log_exact {Ω : Type*} {P Q W s : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (hP0 : 0 < P t ω) (hP1 : 0 < P (t + 1) ω) (hQ0 : 0 < Q t ω) (hQ1 : 0 < Q (t + 1) ω)
    (hW1 : 0 < W (t + 1) ω) (hW2 : 0 < W (t + 2) ω)
    (hflow : W (t + 1) ω = P (t + 1) ω * s (t + 1) ω + Q (t + 1) ω * W (t + 1 + 1) ω) :
    vL P Q W t ω + iL Q t ω - piL P (t + 1) ω = log (s (t + 1) ω + exp (vL P Q W (t + 1) ω)) := by
  have hV : 0 < Q (t + 1) ω * W (t + 1 + 1) ω / P (t + 1) ω := div_pos (mul_pos hQ1 hW2) hP1
  simp only [vL, iL, piL, Nat.add_sub_cancel]
  rw [exp_log hV]
  have e1 : s (t + 1) ω + Q (t + 1) ω * W (t + 1 + 1) ω / P (t + 1) ω =
      W (t + 1) ω / P (t + 1) ω := by
    rw [hflow]; field_simp
  rw [e1, log_div (mul_pos hQ0 hW1).ne' hP0.ne', log_mul hQ0.ne' hW1.ne',
    log_div hW1.ne' hP1.ne']
  ring

/-- Cochrane (2023), eq. (22.2), p. 495, and (3.17), p. 63 (**the linearised flow with
remainder**): under the hypotheses of `flow_log_exact`,
`v_t + i_t − π_{t+1} = κ + ρv_{t+1} + s̃_{t+1} + R_{t+1}`, and if `|v_{t+1} − v̄| ≤ δ_v ≤ 1`,
`|s̄_{t+1} − s̄y| ≤ δ_s`, `η = 2ρδ_v + δ_s/A ≤ 1/2` and `s̄y > 0`, then
`|R_{t+1}| ≤ 2η² + ρδ_v²`. -/
theorem flow_lin {Ω : Type*} {P Q W s : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω} {vbar sybar δv δs : ℝ}
    (hP0 : 0 < P t ω) (hP1 : 0 < P (t + 1) ω) (hQ0 : 0 < Q t ω) (hQ1 : 0 < Q (t + 1) ω)
    (hW1 : 0 < W (t + 1) ω) (hW2 : 0 < W (t + 2) ω)
    (hflow : W (t + 1) ω = P (t + 1) ω * s (t + 1) ω + Q (t + 1) ω * W (t + 1 + 1) ω)
    (hs : 0 < sybar) (hv : |vL P Q W (t + 1) ω - vbar| ≤ δv) (hδv : δv ≤ 1)
    (hsy : |s (t + 1) ω - sybar| ≤ δs)
    (hη : 2 * rho vbar sybar * δv + δs / A0 vbar sybar ≤ 1 / 2) :
    vL P Q W t ω + iL Q t ω - piL P (t + 1) ω = kap vbar sybar +
      rho vbar sybar * vL P Q W (t + 1) ω + stil vbar sybar s (t + 1) ω +
      remF vbar sybar (vL P Q W) s (t + 1) ω ∧
    |remF vbar sybar (vL P Q W) s (t + 1) ω| ≤
      2 * (2 * rho vbar sybar * δv + δs / A0 vbar sybar) ^ 2 + rho vbar sybar * δv ^ 2 :=
  ⟨by
    have := flow_log_exact hP0 hP1 hQ0 hQ1 hW1 hW2 hflow
    unfold remF
    rw [← this]
    ring,
    remF_bound hs hv hδv hsy hη⟩

/-! ### The Fisher half: a Jensen remainder -/

/-- Cochrane (2023), eq. (22.2), p. 495 (the scalar Jensen step): if `a = 1 − m + r` with
`|m| ≤ δ`, `|r| ≤ δ²` and `0 ≤ δ ≤ 1/4`, then `|−log a − m| ≤ 9δ²`. -/
theorem fisher_scalar {a m r δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4) (ha : a = 1 - m + r)
    (hm : |m| ≤ δ) (hr : |r| ≤ δ ^ 2) : |-log a - m| ≤ 9 * δ ^ 2 := by
  set u := -m + r with hu
  have hu1 : |u| ≤ δ + δ ^ 2 := (abs_add_le _ _).trans (by rw [abs_neg]; linarith)
  have hu2 : |u| ≤ 1 / 2 := hu1.trans (by nlinarith)
  have h := log_one_add_sub_le hu2
  have e : -log a - m = -(log (1 + u) - u) - r := by rw [ha, hu]; ring_nf
  rw [e]
  have hsq : u ^ 2 ≤ (δ + δ ^ 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg u) hu1 2
  calc |-(log (1 + u) - u) - r| ≤ |log (1 + u) - u| + |r| := by
        rw [sub_eq_add_neg]; refine (abs_add_le _ _).trans ?_; rw [abs_neg, abs_neg]
    _ ≤ 2 * (δ + δ ^ 2) ^ 2 + δ ^ 2 := by linarith
    _ ≤ 9 * δ ^ 2 := by
      have h1 : (1 + δ) ^ 2 ≤ 2 := by nlinarith
      have h2 : (δ + δ ^ 2) ^ 2 = δ ^ 2 * (1 + δ) ^ 2 := by ring
      nlinarith [sq_nonneg δ]

variable {Ω : Type*}

/-- Cochrane (2023), eq. (22.2), p. 495 (**the Fisher half, any expectation system**): with the
pull-out property, adapted positive prices and the bond-pricing equation
`Q_t = βP_tE_t[1/P_{t+1}]` (`β > 0`), if `|π_{t+1} − π̄| ≤ δ ≤ 1/4` in every state, then
`|i_t + log β − E_tπ_{t+1}| ≤ 9δ²`. -/
theorem fisher_lin_core (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {β δ pibar : ℝ}
    (hβ : 0 < β) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4) {P Q : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω)
    (hPa : 𝔼.Adapted P)
    (hF : ∀ t ω, Q t ω = β * P t ω * 𝔼.E t (fun ω => (P (t + 1) ω)⁻¹) ω) (t : ℕ)
    (hπ : ∀ ω, |piL P (t + 1) ω - pibar| ≤ δ) (ω : Ω) :
    |iL Q t ω + log β - 𝔼.E t (piL P (t + 1)) ω| ≤ 9 * δ ^ 2 := by
  set x : Ω → ℝ := fun ω => piL P (t + 1) ω - pibar with hx
  set R : Ω → ℝ := fun ω => exp (-x ω) - 1 + x ω with hR
  have hRb : ∀ ω, |R ω| ≤ δ ^ 2 := fun ω => by
    have hz : |-x ω| ≤ 1 := by rw [abs_neg]; exact (hπ ω).trans (by linarith)
    have h := Real.abs_exp_sub_one_sub_id_le hz
    have e : R ω = exp (-x ω) - 1 - -x ω := by simp only [hR]; ring
    rw [e]
    refine h.trans ?_
    rw [neg_sq, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hπ ω) 2
  -- `E_t[e^{−π_{t+1}}] = Q_t/β`
  have hEexp : 𝔼.E t (fun ω => exp (-piL P (t + 1) ω)) ω = Q t ω / β := by
    have e1 : (fun ω => exp (-piL P (t + 1) ω)) = P t * fun ω => (P (t + 1) ω)⁻¹ := by
      funext ω'
      simp only [piL, Nat.add_sub_cancel, neg_sub, exp_sub, exp_log (hP t ω'),
        exp_log (hP (t + 1) ω'), Pi.mul_apply, div_eq_mul_inv]
    rw [e1, hpo t _ _ (hPa t), Pi.mul_apply, hF t ω]
    field_simp
  -- decompose `e^{−π} = e^{−π̄}(1 − x + R)`
  have hdec : (fun ω => exp (-piL P (t + 1) ω)) =
      exp (-pibar) • ((fun _ => (1 : ℝ)) - x + R) := by
    funext ω'
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, hR, hx]
    rw [show ∀ y : ℝ, 1 - y + (exp (-y) - 1 + y) = exp (-y) from fun y => by ring, ← exp_add]
    congr 1
    ring
  have hEdec : 𝔼.E t (fun ω => exp (-piL P (t + 1) ω)) ω =
      exp (-pibar) * (1 - 𝔼.E t x ω + 𝔼.E t R ω) := by
    rw [hdec, map_smul, map_add, map_sub, 𝔼.const]
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  have hEpi : 𝔼.E t (piL P (t + 1)) ω = pibar + 𝔼.E t x ω := by
    have e : piL P (t + 1) = (fun _ => pibar) + x := by funext ω'; simp [hx]
    rw [e, map_add, 𝔼.const]; rfl
  have hQpos : 0 < Q t ω := by
    have := hEexp ▸ (𝔼.mono t (fun ω' => (exp_pos _).le) ω : _)
    rw [hF t ω]
    have h0 : 0 < 𝔼.E t (fun ω => exp (-piL P (t + 1) ω)) ω := by
      have hle : (fun _ : Ω => exp (-(pibar + δ))) ≤ fun ω => exp (-piL P (t + 1) ω) :=
        fun ω' => exp_le_exp.2 (by linarith [(abs_le.1 (hπ ω')).2])
      have := 𝔼.mono t hle ω
      rw [𝔼.const] at this
      exact lt_of_lt_of_le (exp_pos _) this
    rw [hEexp] at h0
    rw [hF t ω] at h0
    have : 0 < β * P t ω * 𝔼.E t (fun ω => (P (t + 1) ω)⁻¹) ω := by
      have := div_pos_iff.1 h0
      rcases this with h | h
      · exact h.1
      · linarith [h.2]
    exact this
  have hiL : iL Q t ω + log β = pibar - log (1 - 𝔼.E t x ω + 𝔼.E t R ω) := by
    have hq : Q t ω = β * (exp (-pibar) * (1 - 𝔼.E t x ω + 𝔼.E t R ω)) := by
      rw [← hEdec, hEexp]; field_simp
    have ha : 0 < 1 - 𝔼.E t x ω + 𝔼.E t R ω := by
      have := hQpos; rw [hq] at this
      exact pos_of_mul_pos_right (pos_of_mul_pos_right this hβ.le) (exp_pos _).le
    simp only [iL]
    rw [hq, log_mul hβ.ne' (mul_pos (exp_pos _) ha).ne', log_mul (exp_pos _).ne' ha.ne',
      log_exp]
    ring
  rw [hiL, hEpi]
  have := fisher_scalar (a := 1 - 𝔼.E t x ω + 𝔼.E t R ω) (m := 𝔼.E t x ω) (r := 𝔼.E t R ω)
    hδ0 hδ rfl (𝔼.abs_E_le hπ t ω) (𝔼.abs_E_le hRb t ω)
  have e : pibar - log (1 - 𝔼.E t x ω + 𝔼.E t R ω) - (pibar + 𝔼.E t x ω) =
      -log (1 - 𝔼.E t x ω + 𝔼.E t R ω) - 𝔼.E t x ω := by ring
  rw [e]
  exact this

/-- Cochrane (2023), eq. (22.2), p. 495 (**the Fisher half on a probability space**): with
adapted, almost surely positive prices, integrable `1/P_{t+1}`, the bond-pricing equation
`Q_t = βP_tE_t[1/P_{t+1}]` almost surely (`β > 0`) and `|π_{t+1} − π̄| ≤ δ ≤ 1/4` almost surely,
`|i_t + log β − E_tπ_{t+1}| ≤ 9δ²` almost surely. -/
theorem fisher_lin_meas [MeasurableSpace Ω] {S : MeasExpectationSystem Ω} {β δ pibar : ℝ}
    (hβ : 0 < β) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4) {P Q : ℕ → Ω → ℝ}
    (hPa : StronglyAdapted S.𝓕 P) (hP : ∀ t, ∀ᵐ ω ∂S.μ, 0 < P t ω)
    (hinv : ∀ t, Integrable (fun ω => (P t ω)⁻¹) S.μ)
    (hF : ∀ t, ∀ᵐ ω ∂S.μ, Q t ω = β * P t ω * S.E t (fun ω => (P (t + 1) ω)⁻¹) ω) (t : ℕ)
    (hπ : ∀ᵐ ω ∂S.μ, |piL P (t + 1) ω - pibar| ≤ δ) :
    ∀ᵐ ω ∂S.μ, |iL Q t ω + log β - S.E t (piL P (t + 1)) ω| ≤ 9 * δ ^ 2 := by
  have hpe : piL P (t + 1) = fun ω => log (P (t + 1) ω) - log (P t ω) := by
    funext ω; simp [piL]
  have hm : Measurable (piL P (t + 1)) := by
    rw [hpe]
    exact (((hPa (t + 1)).mono (S.𝓕.le _)).measurable.log).sub
      (((hPa t).mono (S.𝓕.le _)).measurable.log)
  set x : Ω → ℝ := fun ω => piL P (t + 1) ω - pibar with hx
  set R : Ω → ℝ := fun ω => exp (-x ω) - 1 + x ω with hR
  have hxm : Measurable x := hm.sub measurable_const
  have hRm : Measurable R := ((hxm.neg.exp).sub measurable_const).add hxm
  have hRb : ∀ᵐ ω ∂S.μ, |R ω| ≤ δ ^ 2 := by
    filter_upwards [hπ] with ω h
    have hz : |-x ω| ≤ 1 := by rw [abs_neg]; exact h.trans (by linarith)
    have e : R ω = exp (-x ω) - 1 - -x ω := by simp only [hR]; ring
    rw [e]
    refine (Real.abs_exp_sub_one_sub_id_le hz).trans ?_
    rw [neg_sq, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hxi : Integrable x S.μ := Integrable.of_bound hxm.aestronglyMeasurable δ
    (hπ.mono fun ω h => by rwa [Real.norm_eq_abs])
  have hRi : Integrable R S.μ := Integrable.of_bound hRm.aestronglyMeasurable (δ ^ 2)
    (hRb.mono fun ω h => by rwa [Real.norm_eq_abs])
  -- `e^{−π_{t+1}} = e^{−π̄}(1 − x + R)` everywhere
  have hdec : (fun ω => exp (-piL P (t + 1) ω)) =
      exp (-pibar) • ((fun _ => (1 : ℝ)) - x + R) := by
    funext ω'
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, hR, hx]
    rw [show ∀ y : ℝ, 1 - y + (exp (-y) - 1 + y) = exp (-y) from fun y => by ring, ← exp_add]
    congr 1
    ring
  have hei : Integrable (fun ω => exp (-piL P (t + 1) ω)) S.μ := by
    rw [hdec]; exact (((integrable_const 1).sub hxi).add hRi).smul _
  -- `E_t[e^{−π_{t+1}}] = P_tE_t[1/P_{t+1}]`
  have hprod : (P t * fun ω => (P (t + 1) ω)⁻¹) =ᵐ[S.μ] fun ω => exp (-piL P (t + 1) ω) := by
    filter_upwards [hP t, hP (t + 1)] with ω h0 h1
    simp only [Pi.mul_apply, piL, Nat.add_sub_cancel, neg_sub, exp_sub, exp_log h0,
      exp_log h1, div_eq_mul_inv]
  have hpull := condExp_mul_of_stronglyMeasurable_left (hPa t) (hei.congr hprod.symm)
    (hinv (t + 1))
  have hpe' : piL P (t + 1) = (fun _ => pibar) + x := by funext ω'; simp [hx]
  filter_upwards [hF t, hpull, S.E_congr hprod t,
    S.E_smul (exp (-pibar)) ((fun _ => (1 : ℝ)) - x + R) t,
    S.E_add ((integrable_const 1).sub hxi) hRi t, S.E_sub (integrable_const 1) hxi t,
    S.E_add (integrable_const pibar) hxi t, S.abs_E_le hπ t, S.abs_E_le hRb t]
    with ω h1 h2 h3 h5 h6 h7 h8 h9 h10
  have hEx : |S.E t x ω| ≤ δ := h9
  have ha : 0 < 1 - S.E t x ω + S.E t R ω := by
    have := abs_le.1 hEx; have := abs_le.1 h10; nlinarith
  have hq : Q t ω = β * (exp (-pibar) * (1 - S.E t x ω + S.E t R ω)) := by
    have e2 : S.E t (P t * fun ω => (P (t + 1) ω)⁻¹) ω =
        P t ω * S.E t (fun ω => (P (t + 1) ω)⁻¹) ω := h2
    rw [h1, mul_assoc, ← e2, h3, hdec, h5, Pi.smul_apply, smul_eq_mul, h6, Pi.add_apply, h7,
      Pi.sub_apply, S.E_const]
  have hEp : S.E t (piL P (t + 1)) ω = pibar + S.E t x ω := by
    rw [hpe', h8, Pi.add_apply, S.E_const]
  rw [hEp]
  simp only [iL]
  rw [hq, log_mul hβ.ne' (mul_pos (exp_pos _) ha).ne', log_mul (exp_pos _).ne' ha.ne', log_exp]
  have := fisher_scalar (a := 1 - S.E t x ω + S.E t R ω) (m := S.E t x ω) (r := S.E t R ω)
    hδ0 hδ rfl hEx h10
  have e : -(log β + (-pibar + log (1 - S.E t x ω + S.E t R ω))) + log β - (pibar + S.E t x ω) =
      -log (1 - S.E t x ω + S.E t R ω) - S.E t x ω := by ring
  rw [e]
  exact this

/-! ### Both halves of (22.2) -/

/-- Cochrane (2023), eq. (22.2), p. 495: the Fisher remainder
`J_t = i_t + log β − E_tπ_{t+1}`. -/
noncomputable def fisherRem (𝔼 : ExpectationSystem Ω) (β : ℝ) (P Q : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) : ℝ :=
  iL Q t ω + log β - 𝔼.E t (piL P (t + 1)) ω

/-- Cochrane (2023), eq. (22.2), p. 495: the surplus of the linear model, `s̃_{t+1}` plus the
flow remainder `R_{t+1}`, the linearisation constant `κ + log β` and minus the Fisher remainder
`J_t` (`0` at date `0`). -/
noncomputable def sOut (𝔼 : ExpectationSystem Ω) (β vbar sybar : ℝ) (P Q W s : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun ω => stil vbar sybar s (t + 1) ω + remF vbar sybar (vL P Q W) s (t + 1) ω +
      kap vbar sybar + log β - fisherRem 𝔼 β P Q t ω

/-- Cochrane (2023), eq. (22.2), p. 495: the path in the variables of the linear model — log
inflation, the rate `i_t = log(1/Q_t) + log β − J_t = E_tπ_{t+1}`, the log market value of debt
and the surplus `sOut`. -/
noncomputable def linOutcome (𝔼 : ExpectationSystem Ω) (β vbar sybar : ℝ)
    (P Q W s : ℕ → Ω → ℝ) : StarredModel.Outcome Ω where
  pi := piL P
  i := fun t ω => iL Q t ω + log β - fisherRem 𝔼 β P Q t ω
  v := vL P Q W
  s := sOut 𝔼 β vbar sybar P Q W s

/-- Cochrane (2023), eq. (22.2), p. 495 (**both halves of (22.2), exactly, with remainders**):
on every expectation system, if the nonlinear flow `W_t = P_ts̄_t + Q_tW_{t+1}` holds with
positive prices, bond prices and liabilities, the path `linOutcome` satisfies the Fisher
equation and the flow condition of (22.2) exactly (`StarredModel.Consistent`) with
`ρ = e^{v̄}/(e^{v̄} + s̄y)`. The remainders it carries are bounded by `fisher_lin_core`
(`|J_t| ≤ 9δ²`) and `flow_lin` (`|R_t| ≤ 2η² + ρδ_v²`). -/
theorem consistent_core (𝔼 : ExpectationSystem Ω) (β vbar sybar : ℝ) {P Q W s : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (hQ : ∀ t ω, 0 < Q t ω) (hW : ∀ t ω, 0 < W t ω)
    (hflow : ∀ t ω, W t ω = P t ω * s t ω + Q t ω * W (t + 1) ω) :
    StarredModel.Consistent 𝔼 (rho vbar sybar) (linOutcome 𝔼 β vbar sybar P Q W s) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · funext ω
    simp only [linOutcome, fisherRem]
    ring
  · funext ω
    have h := flow_log_exact (hP t ω) (hP (t + 1) ω) (hQ t ω) (hQ (t + 1) ω) (hW (t + 1) ω)
      (hW (t + 2) ω) (hflow (t + 1) ω)
    simp only [linOutcome, sOut, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    unfold remF
    rw [← h]
    ring

/-! ### Links to the derived equilibrium -/

/-- Cochrane (2023), eq. (22.2), p. 495, and §22.1, p. 496 (**on a probability space**): in a
derived equilibrium with positive debt and positive bond prices, at every date almost surely,
the Fisher half holds up to `9δ²` when `|π_{t+1} − π̄| ≤ δ ≤ 1/4`, and the flow half holds
exactly as `v_t + i_t − π_{t+1} = κ + ρv_{t+1} + s̃_{t+1} + R_{t+1}` (with `W` the liabilities
and `s̄` the seigniorage-inclusive surplus), the remainder being bounded by `flow_lin`. -/
theorem derived_lin_meas [MeasurableSpace Ω] {S : MeasExpectationSystem Ω} {e : Econ Ω}
    {B M : ℕ → Ω → ℝ} (hreg : EconReg S e) (hBpos : ∀ t, ∀ᵐ ω ∂S.μ, 0 < B t ω)
    (hQ : ∀ t, ∀ᵐ ω ∂S.μ, 0 < e.Q t ω) (h : DerivedEqm S e B M) (vbar sybar : ℝ) (t : ℕ) :
    ((∀ {δ pibar : ℝ}, 0 ≤ δ → δ ≤ 1 / 4 → (∀ᵐ ω ∂S.μ, |piL e.P (t + 1) ω - pibar| ≤ δ) →
      ∀ᵐ ω ∂S.μ, |iL e.Q t ω + log e.β - S.E t (piL e.P (t + 1)) ω| ≤ 9 * δ ^ 2) ∧
    ∀ᵐ ω ∂S.μ, vL e.P e.Q (wealth e.W0 B M) t ω + iL e.Q t ω - piL e.P (t + 1) ω =
      kap vbar sybar + rho vbar sybar * vL e.P e.Q (wealth e.W0 B M) (t + 1) ω +
      stil vbar sybar (sbar e M) (t + 1) ω +
      remF vbar sybar (vL e.P e.Q (wealth e.W0 B M)) (sbar e M) (t + 1) ω) := by
  obtain ⟨hF, -, hMm, -, -⟩ := imposed_of_derived hreg hBpos h
  have hflow := (optimal_iff_foc (p := hhPlan e B M) hreg hBpos).1 h |>.1.2.1
  have hWpos : ∀ k, ∀ᵐ ω ∂S.μ, 0 < wealth e.W0 B M (k + 1) ω := fun k => by
    filter_upwards [hBpos k, hMm k, hreg.2.2.1 k] with ω hb hm hP
    have : 0 < mmin e k ω := div_pos (mul_pos hP.1 hP.2.2) hP.2.1
    change 0 < B k ω + M k ω
    linarith
  refine ⟨fun hδ0 hδ hπ => fisher_lin_meas hreg.1.1 hδ0 hδ hreg.2.1.1
    (fun t => (hreg.2.2.1 t).mono fun ω h => h.1) (fun t => (hreg.2.2.2.1 t).1) hF t hπ, ?_⟩
  filter_upwards [hreg.2.2.1 t, hreg.2.2.1 (t + 1), hQ t, hQ (t + 1), hWpos t, hWpos (t + 1),
    flow_of_hhFlow hreg hflow (t + 1)] with ω hP0 hP1 hQ0 hQ1 hW1 hW2 hfl
  have hx := flow_log_exact (s := sbar e M) hP0.1 hP1.1 hQ0 hQ1 hW1 hW2 hfl
  unfold remF
  rw [← hx]
  ring

/-- Cochrane (2023), eq. (22.2), p. 495 (**on every finite tree**): in a derived equilibrium
with positive debt, prices and bond prices at every node, the path `linOutcome` (built from the
tree's expectation system, the liabilities `W` and the surplus `s̄`) satisfies both halves of
(22.2) exactly at every node, and the Fisher remainder is at most `9δ²` where
`|π_{t+1} − π̄| ≤ δ ≤ 1/4`. -/
theorem derived_consistent_tree [Fintype Ω] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (T : ExpectationsFiniteTree.FiniteTree Ω) {e : Econ Ω} {B M : ℕ → Ω → ℝ}
    (hreg : EconReg (TreeBridge.treeSystem T) e) (hBa : T.toExpectationSystem.Adapted B)
    (hMa : T.toExpectationSystem.Adapted M) (hBpos : ∀ t ω, 0 < B t ω)
    (hP : ∀ t ω, 0 < e.P t ω) (hQ : ∀ t ω, 0 < e.Q t ω)
    (h : DerivedEqm (TreeBridge.treeSystem T) e B M) (vbar sybar : ℝ) :
    StarredModel.Consistent T.toExpectationSystem (rho vbar sybar)
      (linOutcome T.toExpectationSystem e.β vbar sybar e.P e.Q (wealth e.W0 B M) (sbar e M)) ∧
    ∀ {δ pibar : ℝ} (t : ℕ), 0 ≤ δ → δ ≤ 1 / 4 → (∀ ω, |piL e.P (t + 1) ω - pibar| ≤ δ) →
      ∀ ω, |fisherRem T.toExpectationSystem e.β e.P e.Q t ω| ≤ 9 * δ ^ 2 := by
  have hBpos' : ∀ t, ∀ᵐ ω ∂(TreeBridge.treeSystem T).μ, 0 < B t ω := fun t =>
    (TidyR6MoneyHouseholdTree.ae_iff_forall T).2 (hBpos t)
  obtain ⟨-, -, hMm, -, -⟩ := imposed_of_derived hreg hBpos' h
  have hflow := (optimal_iff_foc (p := hhPlan e B M) hreg hBpos').1 h |>.1.2.1
  have hfl : ∀ t ω, wealth e.W0 B M t ω =
      e.P t ω * sbar e M t ω + e.Q t ω * wealth e.W0 B M (t + 1) ω := fun t =>
    (TidyR6MoneyHouseholdTree.ae_iff_forall T).1 (flow_of_hhFlow hreg hflow t)
  have hMm' : ∀ t ω, mmin e t ω ≤ M t ω := fun t =>
    (TidyR6MoneyHouseholdTree.ae_iff_forall T).1 (hMm t)
  have hV : ∀ t ω, 0 < e.V t ω ∧ 0 < e.y t ω := fun t ω =>
    ((TidyR6MoneyHouseholdTree.ae_iff_forall T).1 (hreg.2.2.1 t) ω).2
  -- liabilities are positive from date 1 on; at date 0 they enter only through `W_1`
  have hW : ∀ t ω, 0 < wealth e.W0 B M (t + 1) ω := fun t ω => by
    have : 0 < mmin e t ω := div_pos (mul_pos (hP t ω) (hV t ω).2) (hV t ω).1
    change 0 < B t ω + M t ω
    linarith [hMm' t ω, hBpos t ω]
  refine ⟨⟨fun t => ?_, fun t => ?_⟩, fun t hδ0 hδ hπ ω => ?_⟩
  · funext ω
    simp only [linOutcome, fisherRem]
    ring
  · funext ω
    have hx := flow_log_exact (s := sbar e M) (hP t ω) (hP (t + 1) ω) (hQ t ω) (hQ (t + 1) ω)
      (hW t ω) (hW (t + 1) ω) (hfl (t + 1) ω)
    simp only [linOutcome, sOut, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    unfold remF
    rw [← hx]
    ring
  · have hF := ((TidyR6MoneyHouseholdTree.tree_derived_iff T hreg hBa hMa hBpos).1 h).1
    have hPa : T.toExpectationSystem.Adapted e.P :=
      (TidyR6MoneyHouseholdTree.adapted_iff T).1 hreg.2.1.1
    exact fisher_lin_core T.toExpectationSystem (ExpectationsFiniteTree.finiteTree_pullOut T)
      hreg.1.1 hδ0 hδ hP hPa hF t hπ ω

end Cochrane.ObservationalEquivalence.TidyR6MoneyHouseholdFlowLin
