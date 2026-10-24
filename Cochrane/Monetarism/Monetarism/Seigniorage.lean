/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.UnpleasantArithmetic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Seigniorage, hyperinflation and monetary history

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.7 (pp. 457–458,
eq. (19.41)) and §19.8 (pp. 459–464), with the precise claim V2 of Chapter 11 (p. 317).
Steady states in continuous time are deterministic exponential paths with exact derivatives.

## Main results

* Steady-state seigniorage: `steady_seigniorage` (`−s/y = (1/(Py))dM/dt = (π + g)/V(r + π)`),
  `revenue`, `revenue_hasDerivAt`, `revenue_elasticity`
  (`d log(−s)/d log π = π/(π + g) − d log V/d log π`), `money_demand_elasticity`,
  `revenue_foc_iff` (the revenue maximum is where the velocity elasticity equals `π/(π + g)`),
  `e16_unit_iff` (survey E16: that is one only when `g = 0`), `revenue_deriv_pos_iff`,
  `laffer_decreasing` (past the point where the velocity elasticity exceeds `π/(π + g)`, more
  inflation yields less revenue).
* The Cagan example `V = e^{a(r+π)}`, `g = 0`: `cagRev`, `cagan_velocity_elasticity`
  (`= aπ`), `cagan_revenue_le` and `cagan_revenue_lt` (unique global maximum at `π = 1/a`),
  `cagan_example_two` (`a = 2` peaks at `π = 0.5`), `cagan_revenue_tendsto_zero`,
  `cagRev_strictMonoOn`, `cagRev_strictAntiOn`, `no_steady_state_above_max` (asking for more
  than the maximum leaves no steady state), `two_steady_states` (below the maximum there is one
  steady state on each side of the peak).
* Ch11 V2 (p. 317): `v2_price_level` (with `P_0 = D/(S + PV seigniorage)`), `v2_cagan` (raising
  money growth lowers `P_0` below the Laffer peak and raises it beyond).
* §19.8 Baumol–Tobin (p. 460): `btCost`, `bt_min` (square-root rule `M = √(A/i)` uniquely
  minimises `iM + A/M`), `bt_interest_elasticity` (`−1/2`), `bt_income_elasticity` (`1/2`),
  `bt_lm_slope` (unit LM slope); `cia_income_elasticity` (cash in advance: unit income
  elasticity, zero interest elasticity).
* §19.8, p. 462, survey E23: `e23_real_loss` (a 40% price rise devalues nominal debt by
  `1 − 1/1.4 = 2/7 ≈ 29%`, not 40%).
-/

namespace Cochrane.Monetarism.Seigniorage

open Filter Topology

/-! ### §19.7: steady-state seigniorage -/

/-- Cochrane (2023), eq. (19.41) and p. 458: in a steady state with `M_t = M_0e^{(π+g)t}`,
`P_t = P_0e^{πt}`, `y_t = y_0e^{gt}` and constant velocity `V = V(r + π)` with
`M_0V = P_0y_0`, money demand holds at every date, `dM/dt = (π + g)M_t`, and seigniorage as a
share of output is `(1/(P_ty_t))dM/dt = (π + g)/V`. -/
theorem steady_seigniorage {M0 P0 y0 π g V : ℝ} (hP0 : 0 < P0) (hy0 : 0 < y0) (hV : 0 < V)
    (hq : M0 * V = P0 * y0) (t : ℝ) :
    HasDerivAt (fun τ => M0 * Real.exp ((π + g) * τ))
        (M0 * Real.exp ((π + g) * t) * (π + g)) t ∧
      M0 * Real.exp ((π + g) * t) * V = P0 * Real.exp (π * t) * (y0 * Real.exp (g * t)) ∧
      1 / (P0 * Real.exp (π * t) * (y0 * Real.exp (g * t))) *
        (M0 * Real.exp ((π + g) * t) * (π + g)) = (π + g) / V := by
  have he : Real.exp ((π + g) * t) = Real.exp (π * t) * Real.exp (g * t) := by
    rw [← Real.exp_add]; ring_nf
  have hd : HasDerivAt (fun τ => M0 * Real.exp ((π + g) * τ))
      (M0 * (Real.exp ((π + g) * t) * (π + g))) t := by
    have h1 : HasDerivAt (fun τ => (π + g) * τ) (π + g) t := by
      simpa using (hasDerivAt_id t).const_mul (π + g)
    exact h1.exp.const_mul M0
  refine ⟨by rw [← mul_assoc] at hd; exact hd, ?_, ?_⟩
  · rw [he]
    have : M0 * V = P0 * y0 := hq
    linear_combination (Real.exp (π * t) * Real.exp (g * t)) * this
  · rw [he]
    have h1 := Real.exp_pos (π * t)
    have h2 := Real.exp_pos (g * t)
    have hM0 : M0 = P0 * y0 / V := by field_simp; linarith
    rw [hM0]
    field_simp

/-- Cochrane (2023), p. 458: steady-state seigniorage revenue as a share of output,
`R(π) = (π + g)/V(r + π)`. -/
noncomputable def revenue (V : ℝ → ℝ) (r g π : ℝ) : ℝ := (π + g) / V (r + π)

/-- Cochrane (2023), p. 458: the derivative of revenue in inflation,
`R'(π) = (V − (π + g)V')/V²`. -/
theorem revenue_hasDerivAt {V : ℝ → ℝ} {V' r g π : ℝ} (hV : HasDerivAt V V' (r + π))
    (hV0 : V (r + π) ≠ 0) :
    HasDerivAt (revenue V r g) ((V (r + π) - (π + g) * V') / V (r + π) ^ 2) π := by
  have hn : HasDerivAt (fun x => x + g) 1 π := by simpa using (hasDerivAt_id π).add_const g
  have hd : HasDerivAt (fun x => V (r + x)) V' π := HasDerivAt.comp_const_add r π hV
  have h := hn.div hd hV0
  have e : revenue V r g = (fun x => x + g) / fun x => V (r + x) := by
    funext x
    simp [revenue]
  rw [e]
  convert h using 1
  ring

/-- Cochrane (2023), p. 458: `d log(−s)/d log π = π/(π + g) − d log V/d log π`, i.e.
`πR'(π)/R(π) = π/(π + g) − πV'/V`. -/
theorem revenue_elasticity {V : ℝ → ℝ} {V' r g π : ℝ} (hV0 : V (r + π) ≠ 0)
    (hpg : π + g ≠ 0) :
    π * ((V (r + π) - (π + g) * V') / V (r + π) ^ 2) / revenue V r g π =
      π / (π + g) - π * V' / V (r + π) := by
  unfold revenue
  field_simp

/-- Cochrane (2023), p. 458 (`d log V/d log π = −d log(M/Py)/d log π`): the elasticity of money
demand `M/(Py) = 1/V` is minus the elasticity of velocity. -/
theorem money_demand_elasticity {V : ℝ → ℝ} {V' r π : ℝ} (hV : HasDerivAt V V' (r + π))
    (hV0 : V (r + π) ≠ 0) :
    HasDerivAt (fun x => 1 / V (r + x)) (-V' / V (r + π) ^ 2) π ∧
      π * (-V' / V (r + π) ^ 2) / (1 / V (r + π)) = -(π * V' / V (r + π)) := by
  have hd : HasDerivAt (fun x => V (r + x)) V' π := HasDerivAt.comp_const_add r π hV
  refine ⟨?_, by field_simp⟩
  have h := hd.inv hV0
  have e : (fun x => 1 / V (r + x)) = fun x => (V (r + x))⁻¹ := by
    funext x
    simp
  rw [e]
  convert h using 1

/-- Cochrane (2023), p. 458 ("Maximum revenue occurs where the elasticity of velocity is
roughly one"): for `π ≠ 0`, `π + g ≠ 0`, `V ≠ 0`, `R'(π) = 0` iff the velocity elasticity
`πV'/V` equals `π/(π + g)`. -/
theorem revenue_foc_iff {V : ℝ → ℝ} {V' r g π : ℝ} (hV0 : V (r + π) ≠ 0) (hπ : π ≠ 0)
    (hpg : π + g ≠ 0) :
    (V (r + π) - (π + g) * V') / V (r + π) ^ 2 = 0 ↔ π * V' / V (r + π) = π / (π + g) := by
  rw [div_eq_zero_iff, div_eq_div_iff hV0 hpg]
  constructor
  · rintro (h | h)
    · linear_combination (-π) * h
    · exact absurd h (pow_ne_zero 2 hV0)
  · intro h
    left
    have : π * (V' * (π + g) - V (r + π)) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hπ
    · linarith

/-- Cochrane (2023), p. 458, survey E16: the revenue-maximising velocity elasticity
`π/(π + g)` equals one only when output does not grow (`g = 0`), hence "roughly one". -/
theorem e16_unit_iff {π g : ℝ} (hpg : π + g ≠ 0) : π / (π + g) = 1 ↔ g = 0 := by
  rw [div_eq_one_iff_eq hpg]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 458 ("If the rise in velocity is larger than the rise in inflation,
more inflation leads to less revenue"): for `π > 0`, `π + g > 0`, `V > 0`, revenue rises with
inflation iff the velocity elasticity is below `π/(π + g)`. -/
theorem revenue_deriv_pos_iff {V : ℝ → ℝ} {V' r g π : ℝ} (hV0 : 0 < V (r + π)) (hπ : 0 < π)
    (hpg : 0 < π + g) :
    0 < (V (r + π) - (π + g) * V') / V (r + π) ^ 2 ↔ π * V' / V (r + π) < π / (π + g) := by
  rw [div_pos_iff_of_pos_right (by positivity), div_lt_div_iff₀ hV0 hpg]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- Cochrane (2023), pp. 457–458 ("Past a unit-elasticity point, printing more money produces
less seigniorage revenue … Seigniorage has a Laffer limit"): if from `π*` on velocity is
differentiable and positive, `π > 0`, `π + g > 0`, and the velocity elasticity exceeds
`π/(π + g)`, revenue is strictly decreasing on `[π*, ∞)`. -/
theorem laffer_decreasing {V V' : ℝ → ℝ} {r g ps : ℝ} (hps : 0 < ps) (hpg : 0 < ps + g)
    (hV : ∀ π, ps ≤ π → HasDerivAt V (V' (r + π)) (r + π) ∧ 0 < V (r + π))
    (hel : ∀ π, ps ≤ π → π / (π + g) < π * V' (r + π) / V (r + π)) :
    StrictAntiOn (revenue V r g) (Set.Ici ps) := by
  have hd : ∀ π, ps ≤ π → HasDerivAt (revenue V r g)
      ((V (r + π) - (π + g) * V' (r + π)) / V (r + π) ^ 2) π := fun π h =>
    revenue_hasDerivAt (hV π h).1 (hV π h).2.ne'
  refine strictAntiOn_of_deriv_neg (convex_Ici ps)
    (fun π h => (hd π h).continuousAt.continuousWithinAt) fun π h => ?_
  rw [interior_Ici] at h
  have h' : ps ≤ π := le_of_lt h
  rw [(hd π h').deriv]
  have hn := (revenue_deriv_pos_iff (V' := V' (r + π)) (g := g) (hV π h').2 (by linarith)
    (by linarith)).not
  have hne : (V (r + π) - (π + g) * V' (r + π)) / V (r + π) ^ 2 ≠ 0 := by
    intro h0
    have := (revenue_foc_iff (V' := V' (r + π)) (g := g) (hV π h').2.ne' (by linarith)
      (by linarith)).mp h0
    linarith [hel π h']
  push Not at hn
  exact lt_of_le_of_ne (hn.mpr (hel π h').le) hne

/-! ### The Cagan example `V = e^{a(r+π)}`, `g = 0` -/

/-- Cochrane (2023), p. 458 (Cagan example, survey item): revenue `π/e^{a(r+π)}`. -/
noncomputable def cagRev (a r π : ℝ) : ℝ := π / Real.exp (a * (r + π))

/-- Cochrane (2023), p. 458: `cagRev` is `revenue` with `V(x) = e^{ax}` and `g = 0`. -/
theorem cagRev_eq (a r π : ℝ) : cagRev a r π = revenue (fun x => Real.exp (a * x)) r 0 π := by
  simp [cagRev, revenue]

/-- Cochrane (2023), p. 458: for `V = e^{ax}` the elasticity of velocity is
`πV'(r + π)/V(r + π) = aπ`, so the first-order condition is `aπ = 1`. -/
theorem cagan_velocity_elasticity (a r π : ℝ) :
    HasDerivAt (fun x => Real.exp (a * x)) (a * Real.exp (a * (r + π))) (r + π) ∧
      π * (a * Real.exp (a * (r + π))) / Real.exp (a * (r + π)) = a * π := by
  refine ⟨?_, by field_simp⟩
  have h := ((hasDerivAt_id (r + π)).const_mul a).exp
  simpa [mul_comm] using h

/-- Cochrane (2023), p. 458 (Cagan example): the revenue is at most its value at `π = 1/a`. -/
theorem cagan_revenue_le {a : ℝ} (ha : 0 < a) (r π : ℝ) : cagRev a r π ≤ cagRev a r (1 / a) := by
  unfold cagRev
  rw [div_le_div_iff₀ (Real.exp_pos _) (Real.exp_pos _)]
  have e1 : Real.exp (a * (r + 1 / a)) = Real.exp (a * r) * Real.exp 1 := by
    rw [← Real.exp_add]; congr 1; field_simp
  have e2 : Real.exp (a * (r + π)) = Real.exp (a * r) * (Real.exp (a * π - 1) * Real.exp 1) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [e1, e2]
  have h := Real.add_one_le_exp (a * π - 1)
  have hr := Real.exp_pos (a * r)
  have he := Real.exp_pos 1
  have key : a * π ≤ Real.exp (a * π - 1) := by linarith
  have : π ≤ 1 / a * Real.exp (a * π - 1) := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ ha]
    linarith
  calc π * (Real.exp (a * r) * Real.exp 1) ≤
      1 / a * Real.exp (a * π - 1) * (Real.exp (a * r) * Real.exp 1) :=
        mul_le_mul_of_nonneg_right this (by positivity)
    _ = 1 / a * (Real.exp (a * r) * (Real.exp (a * π - 1) * Real.exp 1)) := by ring

/-- Cochrane (2023), p. 458 (Cagan example): the maximum at `π = 1/a` is strict — every other
inflation rate yields strictly less revenue. -/
theorem cagan_revenue_lt {a : ℝ} (ha : 0 < a) (r : ℝ) {π : ℝ} (hπ : π ≠ 1 / a) :
    cagRev a r π < cagRev a r (1 / a) := by
  unfold cagRev
  rw [div_lt_div_iff₀ (Real.exp_pos _) (Real.exp_pos _)]
  have e1 : Real.exp (a * (r + 1 / a)) = Real.exp (a * r) * Real.exp 1 := by
    rw [← Real.exp_add]; congr 1; field_simp
  have e2 : Real.exp (a * (r + π)) = Real.exp (a * r) * (Real.exp (a * π - 1) * Real.exp 1) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [e1, e2]
  have hne : a * π - 1 ≠ 0 := by
    intro h
    apply hπ
    field_simp
    linarith
  have h := Real.add_one_lt_exp hne
  have hr := Real.exp_pos (a * r)
  have he := Real.exp_pos 1
  have : π < 1 / a * Real.exp (a * π - 1) := by
    rw [div_mul_eq_mul_div, one_mul, lt_div_iff₀ ha]
    linarith
  calc π * (Real.exp (a * r) * Real.exp 1) <
      1 / a * Real.exp (a * π - 1) * (Real.exp (a * r) * Real.exp 1) :=
        mul_lt_mul_of_pos_right this (by positivity)
    _ = 1 / a * (Real.exp (a * r) * (Real.exp (a * π - 1) * Real.exp 1)) := by ring

/-- Cochrane (2023), p. 458 (survey numerical check: "argmax 0.5 for `a = 2`"): with `a = 2`
revenue peaks at `π = 1/2`. -/
theorem cagan_example_two (r π : ℝ) (hπ : π ≠ 1 / 2) : cagRev 2 r π < cagRev 2 r (1 / 2) :=
  cagan_revenue_lt (by norm_num) r hπ

/-- Cochrane (2023), p. 458 (Cagan example): revenue vanishes as inflation goes to infinity. -/
theorem cagan_revenue_tendsto_zero {a : ℝ} (ha : 0 < a) (r : ℝ) :
    Tendsto (cagRev a r) atTop (𝓝 0) := by
  have h1 : Tendsto (fun π : ℝ => (a * π) ^ (1 : ℕ) * Real.exp (-(a * π))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp (tendsto_id.const_mul_atTop ha)
  have h2 := h1.const_mul (Real.exp (-(a * r)) / a)
  rw [mul_zero] at h2
  refine h2.congr fun π => ?_
  unfold cagRev
  rw [show a * (r + π) = a * r + a * π by ring, Real.exp_add, Real.exp_neg, Real.exp_neg]
  field_simp

/-- Cochrane (2023), p. 458 (Cagan example): the derivative of revenue,
`(1 − aπ)/e^{a(r+π)}`. -/
theorem cagRev_hasDerivAt (a r π : ℝ) :
    HasDerivAt (cagRev a r) ((1 - a * π) / Real.exp (a * (r + π))) π := by
  have he : HasDerivAt (fun x => Real.exp (a * (r + x))) (Real.exp (a * (r + π)) * a) π := by
    have h := (((hasDerivAt_id π).const_add r).const_mul a).exp
    simpa using h
  have h := (hasDerivAt_id' π).div he (Real.exp_pos _).ne'
  have e : cagRev a r = (fun x => x) / fun x => Real.exp (a * (r + x)) := by
    funext x
    simp [cagRev]
  rw [e]
  convert h using 1
  field_simp

/-- Cochrane (2023), p. 458 (Cagan example): revenue strictly increases with inflation up to
the peak `1/a`. -/
theorem cagRev_strictMonoOn {a : ℝ} (ha : 0 < a) (r : ℝ) :
    StrictMonoOn (cagRev a r) (Set.Icc 0 (1 / a)) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 (1 / a))
    (fun π _ => (cagRev_hasDerivAt a r π).continuousAt.continuousWithinAt) fun π h => ?_
  rw [interior_Icc] at h
  rw [(cagRev_hasDerivAt a r π).deriv]
  have : a * π < 1 := by
    have := h.2
    rw [lt_div_iff₀ ha] at this
    linarith
  exact div_pos (by linarith) (Real.exp_pos _)

/-- Cochrane (2023), p. 458 (Cagan example): beyond the peak `1/a`, revenue strictly decreases
with inflation. -/
theorem cagRev_strictAntiOn {a : ℝ} (ha : 0 < a) (r : ℝ) :
    StrictAntiOn (cagRev a r) (Set.Ici (1 / a)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici (1 / a))
    (fun π _ => (cagRev_hasDerivAt a r π).continuousAt.continuousWithinAt) fun π h => ?_
  rw [interior_Ici] at h
  rw [(cagRev_hasDerivAt a r π).deriv]
  have : 1 < a * π := by
    have := Set.mem_Ioi.mp h
    rw [div_lt_iff₀ ha] at this
    linarith
  exact div_neg_of_neg_of_pos (by linarith) (Real.exp_pos _)

/-- Cochrane (2023), p. 458 ("When the government then tries to squeeze one more cent of revenue
from the inflation tax, inflation jumps to infinity"): a revenue requirement above the maximum
has no steady state. -/
theorem no_steady_state_above_max {a r ρ : ℝ} (ha : 0 < a) (hρ : cagRev a r (1 / a) < ρ) :
    ∀ π, cagRev a r π ≠ ρ := fun π h => by
  have := cagan_revenue_le ha r π
  linarith

/-- Cochrane (2023), pp. 457–458: every revenue requirement strictly between `0` and the
maximum has a steady state below the peak and another beyond it (the Laffer curve has two
sides). -/
theorem two_steady_states {a r ρ : ℝ} (ha : 0 < a) (hρ0 : 0 < ρ)
    (hρ : ρ < cagRev a r (1 / a)) :
    (∃ π1, 0 < π1 ∧ π1 < 1 / a ∧ cagRev a r π1 = ρ) ∧
      ∃ π2, 1 / a < π2 ∧ cagRev a r π2 = ρ := by
  have hcont : Continuous (cagRev a r) := by
    unfold cagRev
    exact continuous_id.div (Real.continuous_exp.comp (continuous_const.mul
      (continuous_const.add continuous_id))) fun _ => (Real.exp_pos _).ne'
  have h0 : cagRev a r 0 = 0 := by simp [cagRev]
  have ha' : (0 : ℝ) ≤ 1 / a := by positivity
  constructor
  · obtain ⟨π1, hπ1, hv⟩ := intermediate_value_Icc ha' hcont.continuousOn
      ⟨by rw [h0]; exact hρ0.le, hρ.le⟩
    refine ⟨π1, lt_of_le_of_ne hπ1.1 ?_, lt_of_le_of_ne hπ1.2 ?_, hv⟩
    · rintro rfl; rw [h0] at hv; linarith
    · rintro rfl; linarith
  · obtain ⟨N, hN, hN'⟩ := ((cagan_revenue_tendsto_zero ha r).eventually
      (gt_mem_nhds hρ0)).and (eventually_gt_atTop (1 / a)) |>.exists
    obtain ⟨π2, hπ2, hv⟩ := intermediate_value_Icc' hN'.le hcont.continuousOn
      ⟨hN.le, hρ.le⟩
    refine ⟨π2, lt_of_le_of_ne hπ2.1 ?_, hv⟩
    rintro rfl; linarith

/-! ### Chapter 11, V2: seigniorage and the initial price level -/

/-- Cochrane (2023), §11.2, p. 317 (V2: "raising `M` adds future seigniorage revenue, which
lowers the initial price level"): with `P_0 = D/(S + Σ)`, `D > 0`, the initial price level is
strictly decreasing in the present value `Σ` of seigniorage (where `S + Σ > 0`). -/
theorem v2_price_level {D S : ℝ} (hD : 0 < D) {S1 S2 : ℝ} (h1 : 0 < S + S1) (h : S1 < S2) :
    D / (S + S2) < D / (S + S1) :=
  div_lt_div_of_pos_left hD h1 (by linarith)

/-- Cochrane (2023), §11.2, p. 317 (V2: "Once past the hyperinflationary point on the
inflation-tax Laffer curve, raising `M` lowers seigniorage revenue and creates both current and
future inflation"): in the Cagan example with `P_0 = D/(S + c·R(π))` (`c > 0` the present-value
factor, `S > 0`), raising steady money growth lowers `P_0` below the peak `1/a` and raises it
beyond. -/
theorem v2_cagan {a r D S c : ℝ} (ha : 0 < a) (hD : 0 < D) (hS : 0 < S) (hc : 0 < c) :
    (∀ π1 π2, 0 ≤ π1 → π1 < π2 → π2 ≤ 1 / a →
      D / (S + c * cagRev a r π2) < D / (S + c * cagRev a r π1)) ∧
    (∀ π1 π2, 1 / a ≤ π1 → π1 < π2 →
      D / (S + c * cagRev a r π1) < D / (S + c * cagRev a r π2)) := by
  have hnn : ∀ π, 0 ≤ π → 0 ≤ cagRev a r π := fun π h => div_nonneg h (Real.exp_pos _).le
  constructor
  · intro π1 π2 h1 h12 h2
    have := cagRev_strictMonoOn ha r ⟨h1, by linarith⟩ ⟨by linarith, h2⟩ h12
    exact v2_price_level hD (by nlinarith [hnn π1 h1]) (by nlinarith)
  · intro π1 π2 h1 h12
    have := cagRev_strictAntiOn ha r (Set.mem_Ici.mpr h1) (Set.mem_Ici.mpr (by linarith)) h12
    have h0 : 0 ≤ π2 := by linarith [show (0 : ℝ) ≤ 1 / a by positivity]
    exact v2_price_level hD (by nlinarith [hnn π2 h0]) (by nlinarith)

/-! ### §19.8: Baumol–Tobin and cash in advance -/

/-- Cochrane (2023), §19.8, p. 460 (Allais–Baumol–Tobin inventory model): holding average cash
`M` costs forgone interest `iM` plus trips to the bank `A/M` (`A = bPy/2`). -/
noncomputable def btCost (i A M : ℝ) : ℝ := i * M + A / M

/-- Cochrane (2023), §19.8, p. 460: for `i, A > 0` the square-root rule `M* = √(A/i)` is the
unique minimiser of `iM + A/M` over `M > 0`. -/
theorem bt_min {i A : ℝ} (hi : 0 < i) (hA : 0 < A) :
    0 < Real.sqrt (A / i) ∧ ∀ M, 0 < M → btCost i A (Real.sqrt (A / i)) ≤ btCost i A M ∧
      (btCost i A M = btCost i A (Real.sqrt (A / i)) ↔ M = Real.sqrt (A / i)) := by
  set s := Real.sqrt i with hs
  set q := Real.sqrt A with hq
  have hs0 : 0 < s := Real.sqrt_pos.mpr hi
  have hq0 : 0 < q := Real.sqrt_pos.mpr hA
  have hss : s ^ 2 = i := Real.sq_sqrt hi.le
  have hqq : q ^ 2 = A := Real.sq_sqrt hA.le
  have hM : Real.sqrt (A / i) = q / s := by rw [Real.sqrt_div hA.le]
  have key : ∀ M, 0 < M → btCost i A M - btCost i A (q / s) = (s * M - q) ^ 2 / M := by
    intro M hM0
    unfold btCost
    rw [← hss, ← hqq]
    field_simp
    ring
  rw [hM]
  refine ⟨div_pos hq0 hs0, fun M hM0 => ⟨?_, ?_⟩⟩
  · have := key M hM0
    have : 0 ≤ (s * M - q) ^ 2 / M := div_nonneg (sq_nonneg _) hM0.le
    linarith
  · constructor
    · intro h
      have := key M hM0
      rw [h, sub_self] at this
      have h2 : (s * M - q) ^ 2 = 0 := by
        rcases div_eq_zero_iff.mp this.symm with h3 | h3
        · exact h3
        · exact absurd h3 hM0.ne'
      have : s * M = q := by nlinarith [sq_nonneg (s * M - q)]
      field_simp
      linarith
    · rintro rfl
      rfl

/-- Cochrane (2023), §19.8, p. 460 ("This model produces an interest … elasticity that [is] a
half"): `log M* = log √(K/i)` has derivative `−1/2` in `log i`. -/
theorem bt_interest_elasticity {K : ℝ} (hK : 0 < K) (x : ℝ) :
    HasDerivAt (fun z => Real.log (Real.sqrt (K / Real.exp z))) (-1 / 2) x := by
  have e : (fun z => Real.log (Real.sqrt (K / Real.exp z))) = fun z => (Real.log K - z) / 2 := by
    funext z
    rw [Real.log_sqrt (div_nonneg hK.le (Real.exp_pos z).le),
      Real.log_div hK.ne' (Real.exp_pos z).ne', Real.log_exp]
  rw [e]
  have h := ((hasDerivAt_id x).const_sub (Real.log K)).div_const 2
  simpa [neg_div] using h

/-- Cochrane (2023), §19.8, p. 460 ("… and income elasticity that are each a half"):
`log √(Ky)` has derivative `1/2` in `log y`. -/
theorem bt_income_elasticity {K : ℝ} (hK : 0 < K) (x : ℝ) :
    HasDerivAt (fun z => Real.log (Real.sqrt (K * Real.exp z))) (1 / 2) x := by
  have e : (fun z => Real.log (Real.sqrt (K * Real.exp z))) = fun z => (Real.log K + z) / 2 := by
    funext z
    rw [Real.log_sqrt (mul_nonneg hK.le (Real.exp_pos z).le),
      Real.log_mul hK.ne' (Real.exp_pos z).ne', Real.log_exp]
  rw [e]
  have h := ((hasDerivAt_id x).const_add (Real.log K)).div_const 2
  simpa using h

/-- Cochrane (2023), §19.8, p. 460 ("the slope of the LM curve is the ratio of income to
interest elasticities of money demand … This model gives a unit slope"). -/
theorem bt_lm_slope : (1 / 2 : ℝ) / |(-1 / 2 : ℝ)| = 1 := by norm_num [abs_of_neg]

/-- Cochrane (2023), §19.8, p. 460 ("the simple cash in advance model is notable as a theory
with a unit income and zero interest elasticity"): with `M = Py/V`, `log M` has derivative `1`
in `log y`, and does not depend on the interest rate. -/
theorem cia_income_elasticity {c : ℝ} (hc : 0 < c) (x : ℝ) :
    HasDerivAt (fun z => Real.log (c * Real.exp z)) 1 x := by
  have e : (fun z => Real.log (c * Real.exp z)) = fun z => Real.log c + z := by
    funext z
    rw [Real.log_mul hc.ne' (Real.exp_pos z).ne', Real.log_exp]
  rw [e]
  simpa using (hasDerivAt_id x).const_add (Real.log c)

/-- Cochrane (2023), §19.8, p. 462, survey E23: "The resulting 40% cumulative price-level rise
… devalued WWII debt by 40%" — a 40% rise in the price level lowers the real value of nominal
debt by `1 − 1/1.4 = 2/7 ≈ 28.6%`, not 40%. -/
theorem e23_real_loss : (1 : ℝ) - 1 / (14 / 10) = 2 / 7 ∧ (2 / 7 : ℝ) ≠ 4 / 10 ∧
    |(2 / 7 : ℝ) - 286 / 1000| < 1 / 1000 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [abs_lt]
  constructor <;> norm_num

end Cochrane.Monetarism.Seigniorage
