/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ClassicalMonetaryModel.MIUNonseparable
import ClassicalMonetaryModel.ExpectationsFiniteTree

/-!
# Optimal monetary policy with money in the utility function: the Friedman rule

Galí (2015), Chapter 2, §2.5.3 (pp. 40–42), with fn. 13.

## The planner

The planner solves the static problem `max U(C, M/P, N)` subject to `C = A N^{1−α}` (p. 40).

* `planner_foc_necessary`: for a **general** differentiable `U` (derivative `L`, so
  `U_c = L(1,0,0)`, `U_m = L(0,1,0)`, `U_n = L(0,0,1)`), an optimum with `N, M/P > 0`
  satisfies (49) `−U_n = (1 − α) A N^{−α} U_c` and (50) `U_m = 0`; `planner_foc_ratio` is
  (49) in the printed ratio form.
* `planner_optimum_iff`: for an additively separable utility `u(C) + v(m) − h(N)` with `u, v`
  concave, `u' ≥ 0` and `h` convex, (49)–(50) are **necessary and sufficient**.
* `no_planner_optimum_isoelastic`: with the book's own isoelastic utility of real balances
  `U_m > 0` everywhere, so (50) never holds: efficiency needs a satiation level.

## Decentralisation and the Friedman rule

* `decentralised_49`: (49) holds in any decentralised equilibrium ((4) with (14)), whatever
  the policy.
* `decentralised_efficient_iff`: given (33), `U_m = 0` at every date iff `i_t = 0` at every
  date (the Friedman rule); `decentralised_optimal_iff_friedman`: with the separable utility
  the decentralised allocation solves the planner's problem iff `i = 0`.
* `friedman_steady_state_inflation`: under the Friedman rule the steady state has `π = −ρ`
  (and `Π = β`), deflation for `ρ > 0`.

## Indeterminacy under `i = 0` (p. 41)

* `friedman_euler_iff`, `friedman_equilibrium_iff`: with `i ≡ 0`, (43) and (47) hold iff
  `π_{t+1} = −ρ − σ ψ_ya E_t Δa_{t+1} + ξ_{t+1}` for a martingale-difference sequence `ξ`.
* `friedman_indeterminate`: next to every equilibrium there is a different one (initial
  inflation, hence the price level, is free); `friedman_sunspot_coin`: under genuine
  uncertainty (two coin flips) a non-degenerate sunspot `ξ` gives a different equilibrium.

## Fn. 13 (and exercise 2.6): `î_t = φ_π π̂_t` in the MIU model

* `ruleSystem_iff`: the system reduces to `(1 + φ_π s) E_t π_{t+1} = φ_π (1 + s) π_t + g_t`,
  `s = ϖ + σ ψ_yi = ϖ(φ + α)/D ≥ 0` (`s_eq`).
* `fn13_unique`, `fn13_exists` (`φ_π > 1`: exactly one bounded solution) and
  `fn13_not_unique` (`0 ≤ φ_π ≤ 1`: a second bounded solution next to any solution).

## The rule `i_t = φ (r_{t−1} + π_t)` (p. 42)

In the **log-linear** model (Fisher equation (22), survey item C2-5):
`lagged_rule_unique` (`φ > 1`: every bounded solution has `i ≡ 0`, `π_t = −r_{t−1}`),
`lagged_rule_exists`, and `inflation_rule_implies_zero_rate`.
-/

namespace Gali.ClassicalMonetaryModel.FriedmanRule

open Filter Topology

/-! ### The planner's problem -/

/-- Galí (2015), eqs. (49)–(50), p. 40 (**necessity, general utility**): if `(N, m)` with
`N, m > 0` maximises `U(A N'^{1−α}, m', N')` over `N', m' > 0` and `U` is differentiable at
the optimum with derivative `L`, then `−U_n = (1 − α) A N^{−α} U_c` and `U_m = 0`. -/
theorem planner_foc_necessary {U : ℝ × ℝ × ℝ → ℝ} {L : ℝ × ℝ × ℝ →L[ℝ] ℝ} {A α N m : ℝ}
    (hN : 0 < N) (hm : 0 < m) (hU : HasFDerivAt U L (A * N ^ (1 - α), m, N))
    (hopt : ∀ N' m', 0 < N' → 0 < m' →
      U (A * N' ^ (1 - α), m', N') ≤ U (A * N ^ (1 - α), m, N)) :
    -L (0, 0, 1) = (1 - α) * A * N ^ (-α) * L (1, 0, 0) ∧ L (0, 1, 0) = 0 := by
  constructor
  · have hc : HasDerivAt (fun N' : ℝ => (A * N' ^ (1 - α), m, N'))
        ((1 - α) * A * N ^ (-α), 0, 1) N := by
      have h1 := (Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hN.ne')).const_mul A
      have h2 := (hasDerivAt_const N m).prodMk (hasDerivAt_id N)
      refine (h1.prodMk h2).congr_deriv ?_
      rw [show (1 : ℝ) - α - 1 = -α by ring]
      ext <;> simp
      ring
    have hloc : IsLocalMax (fun N' : ℝ => U (A * N' ^ (1 - α), m, N')) N := by
      filter_upwards [eventually_gt_nhds hN] with N' hN'
      exact hopt N' m hN' hm
    have h0 := hloc.hasDerivAt_eq_zero (hU.comp_hasDerivAt N hc)
    have hv : (((1 - α) * A * N ^ (-α), 0, 1) : ℝ × ℝ × ℝ)
        = ((1 - α) * A * N ^ (-α)) • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) + ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [hv, map_add, map_smul, smul_eq_mul] at h0
    linarith
  · have hc : HasDerivAt (fun m' : ℝ => (A * N ^ (1 - α), m', N)) (0, 1, 0) m :=
      (hasDerivAt_const m _).prodMk ((hasDerivAt_id m).prodMk (hasDerivAt_const m N))
    have hloc : IsLocalMax (fun m' : ℝ => U (A * N ^ (1 - α), m', N)) m := by
      filter_upwards [eventually_gt_nhds hm] with m' hm'
      exact hopt N m' hN hm'
    exact hloc.hasDerivAt_eq_zero (hU.comp_hasDerivAt m hc)

/-- Galí (2015), eq. (49), p. 40, ratio form: with `U_c ≠ 0`,
`−U_n/U_c = (1 − α) A N^{−α}`. -/
theorem planner_foc_ratio {Uc Un A α N : ℝ} (hUc : Uc ≠ 0)
    (h : -Un = (1 - α) * A * N ^ (-α) * Uc) : -Un / Uc = (1 - α) * A * N ^ (-α) := by
  rw [h, mul_div_assoc, div_self hUc, mul_one]

/-- A differentiable function on `(0, ∞)` with nonincreasing derivative lies below its
tangents at positive points (Galí (2015), p. 40: concavity of the planner's problem). -/
theorem tangent_of_deriv {f f' : ℝ → ℝ} {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hd : ∀ z, 0 < z → HasDerivAt f (f' z) z) (hanti : AntitoneOn f' (Set.Ioi 0)) :
    f y ≤ f x + f' x * (y - x) := by
  refine MIUSeparable.le_tangent hx hy.le (fun z hz => ?_) hd hanti
  have hz0 : 0 < z := by
    rcases Set.mem_uIcc.1 hz with h | h
    · exact lt_of_lt_of_le hx h.1
    · exact lt_of_lt_of_le hy h.1
  exact (hd z hz0).continuousAt.continuousWithinAt

/-- Galí (2015), p. 40: the technology `A N^{1−α}` (`A > 0`, `0 ≤ α < 1`) is concave:
`A N'^{1−α} ≤ A N^{1−α} + (1 − α) A N^{−α} (N' − N)` for `N, N' > 0`. -/
theorem production_le_tangent {A α N N' : ℝ} (hA : 0 < A) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hN : 0 < N) (hN' : 0 < N') :
    A * N' ^ (1 - α) ≤ A * N ^ (1 - α) + (1 - α) * A * N ^ (-α) * (N' - N) := by
  have h := tangent_of_deriv (f := fun z => A * z ^ (1 - α))
    (f' := fun z => (1 - α) * A * z ^ (-α)) hN hN' (fun z hz => ?_) ?_
  · simpa using h
  · refine ((Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hz.ne')).const_mul A).congr_deriv ?_
    rw [show (1 : ℝ) - α - 1 = -α by ring]
    ring
  · intro a ha b _ hab
    have h1 : (0 : ℝ) ≤ (1 - α) * A := mul_nonneg (by linarith) hA.le
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha hab (by linarith)) h1

/-- Galí (2015), eqs. (49)–(50), p. 40 (**necessary and sufficient**, separable utility
`u(C) + v(m) − h(N)`): with `u`, `v` differentiable and concave on `(0, ∞)`, `u'(C) ≥ 0`,
`h` differentiable and convex on `(0, ∞)`, `A > 0`, `0 ≤ α < 1`, the point `(N, m)` maximises
`u(A N'^{1−α}) + v(m') − h(N')` over `N', m' > 0` iff
`h'(N) = (1 − α) A N^{−α} u'(C)` (eq. (49)) and `v'(m) = 0` (eq. (50)). -/
theorem planner_optimum_iff {u v h u' v' h' : ℝ → ℝ} {A α N m : ℝ} (hA : 0 < A)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hN : 0 < N) (hm : 0 < m)
    (hu : ∀ z, 0 < z → HasDerivAt u (u' z) z) (hu_anti : AntitoneOn u' (Set.Ioi 0))
    (hu_pos : 0 ≤ u' (A * N ^ (1 - α)))
    (hv : ∀ z, 0 < z → HasDerivAt v (v' z) z) (hv_anti : AntitoneOn v' (Set.Ioi 0))
    (hh : ∀ z, 0 < z → HasDerivAt h (h' z) z) (hh_mono : MonotoneOn h' (Set.Ioi 0)) :
    (∀ N' m', 0 < N' → 0 < m' →
      u (A * N' ^ (1 - α)) + v m' - h N' ≤ u (A * N ^ (1 - α)) + v m - h N) ↔
      (h' N = (1 - α) * A * N ^ (-α) * u' (A * N ^ (1 - α)) ∧ v' m = 0) := by
  have hC : 0 < A * N ^ (1 - α) := mul_pos hA (Real.rpow_pos_of_pos hN _)
  constructor
  · intro hopt
    constructor
    · have hd1 : HasDerivAt (fun N' : ℝ => A * N' ^ (1 - α)) ((1 - α) * A * N ^ (-α)) N := by
        refine ((Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hN.ne')).const_mul A).congr_deriv
          ?_
        rw [show (1 : ℝ) - α - 1 = -α by ring]
        ring
      have hg : HasDerivAt (fun N' => u (A * N' ^ (1 - α)) + v m - h N')
          (u' (A * N ^ (1 - α)) * ((1 - α) * A * N ^ (-α)) - h' N) N :=
        HasDerivAt.sub (((hu _ hC).comp N hd1).add_const (v m)) (hh N hN)
      have hloc : IsLocalMax (fun N' => u (A * N' ^ (1 - α)) + v m - h N') N := by
        filter_upwards [eventually_gt_nhds hN] with N' hN'
        exact hopt N' m hN' hm
      have h0 := hloc.hasDerivAt_eq_zero hg
      linarith
    · have hg : HasDerivAt (fun m' => u (A * N ^ (1 - α)) + v m' - h N) (v' m) m := by
        have := ((hv m hm).const_add (u (A * N ^ (1 - α)))).sub_const (h N)
        exact this
      have hloc : IsLocalMax (fun m' => u (A * N ^ (1 - α)) + v m' - h N) m := by
        filter_upwards [eventually_gt_nhds hm] with m' hm'
        exact hopt N m' hN hm'
      exact hloc.hasDerivAt_eq_zero hg
  · rintro ⟨h49, h50⟩ N' m' hN' hm'
    have hC' : 0 < A * N' ^ (1 - α) := mul_pos hA (Real.rpow_pos_of_pos hN' _)
    have t1 := tangent_of_deriv hC hC' hu hu_anti
    have t2 := tangent_of_deriv hm hm' hv hv_anti
    have t3 := tangent_of_deriv (f := fun z => -h z) (f' := fun z => -h' z) hN hN'
      (fun z hz => (hh z hz).neg) (fun a ha b hb hab => neg_le_neg (hh_mono ha hb hab))
    have tp := production_le_tangent hA hα0 hα1 hN hN'
    rw [h50, zero_mul, add_zero] at t2
    have k := mul_le_mul_of_nonneg_left (sub_le_sub_right tp (A * N ^ (1 - α))) hu_pos
    have e : u' (A * N ^ (1 - α)) * (A * N ^ (1 - α) + (1 - α) * A * N ^ (-α) * (N' - N)
        - A * N ^ (1 - α)) = h' N * (N' - N) := by
      rw [h49]
      ring
    linarith

/-- Galí (2015), p. 40 (**(50) needs satiation**): with the isoelastic utility of real
balances of §2.5.1, `v = ((M/P)^{1−ν} − 1)/(1 − ν)` (`ν > 0`), `U_m = m^{−ν} > 0` everywhere,
so (50) never holds and the planner's problem has no solution: no `(N, m)` with `N, m > 0`
maximises `u(A N'^{1−α}) + v(m') − h(N')`. -/
theorem no_planner_optimum_isoelastic {u h : ℝ → ℝ} {ν A α N m : ℝ} (hN : 0 < N) (hm : 0 < m) :
    ¬ ∀ N' m', 0 < N' → 0 < m' →
      u (A * N' ^ (1 - α)) + MIUSeparable.utilPow ν m' - h N'
        ≤ u (A * N ^ (1 - α)) + MIUSeparable.utilPow ν m - h N := by
  intro hopt
  have hg : HasDerivAt (fun m' => u (A * N ^ (1 - α)) + MIUSeparable.utilPow ν m' - h N)
      (m ^ (-ν)) m :=
    ((MIUSeparable.hasDerivAt_utilPow ν hm).const_add (u (A * N ^ (1 - α)))).sub_const (h N)
  have hloc : IsLocalMax (fun m' => u (A * N ^ (1 - α)) + MIUSeparable.utilPow ν m' - h N) m := by
    filter_upwards [eventually_gt_nhds hm] with m' hm'
    exact hopt N m' hN hm'
  exact (Real.rpow_pos_of_pos hm (-ν)).ne' (hloc.hasDerivAt_eq_zero hg)

/-! ### Decentralisation and the Friedman rule -/

/-- Galí (2015), p. 41: in a decentralised equilibrium, the household's labour supply (4)
`−U_n/U_c = W/P` and the firm's labour demand (14) `W/P = (1 − α) A N^{−α}` together give
the efficiency condition (49), whatever monetary policy is. -/
theorem decentralised_49 {Uc Un W P A α N : ℝ} (h4 : -Un / Uc = W / P)
    (h14 : W / P = (1 - α) * A * N ^ (-α)) : -Un / Uc = (1 - α) * A * N ^ (-α) := by
  rw [h4, h14]

/-- Galí (2015), p. 41: `1 − e^{−i} = 0` iff `i = 0`. -/
theorem one_sub_exp_neg_eq_zero_iff (i : ℝ) : 1 - Real.exp (-i) = 0 ↔ i = 0 := by
  rw [sub_eq_zero, eq_comm, Real.exp_eq_one_iff, neg_eq_zero]

/-- Galí (2015), p. 41 (**the Friedman rule**): if the household's money condition (33)
`U_m = (1 − e^{−i}) U_c` holds at every date with `U_c ≠ 0`, the efficiency condition (50)
`U_m = 0` holds at every date iff `i_t = 0` at every date. -/
theorem decentralised_efficient_iff {Uc Um i : ℕ → ℝ} (hUc : ∀ t, Uc t ≠ 0)
    (h33 : ∀ t, Um t = (1 - Real.exp (-i t)) * Uc t) :
    (∀ t, Um t = 0) ↔ ∀ t, i t = 0 := by
  refine forall_congr' fun t => ?_
  rw [h33 t, mul_eq_zero, or_iff_left (hUc t), one_sub_exp_neg_eq_zero_iff]

/-- Galí (2015), p. 41 (**the Friedman rule, global form**): with the separable utility of
`planner_optimum_iff` and `u'(C) > 0`, a decentralised allocation satisfying (49) (from (4)
and (14)) and the money condition (33) `v'(m) = (1 − e^{−i}) u'(C)` solves the planner's
problem iff `i = 0`. -/
theorem decentralised_optimal_iff_friedman {u v h u' v' h' : ℝ → ℝ} {A α N m i : ℝ}
    (hA : 0 < A) (hα0 : 0 ≤ α) (hα1 : α < 1) (hN : 0 < N) (hm : 0 < m)
    (hu : ∀ z, 0 < z → HasDerivAt u (u' z) z) (hu_anti : AntitoneOn u' (Set.Ioi 0))
    (hu_pos : 0 < u' (A * N ^ (1 - α)))
    (hv : ∀ z, 0 < z → HasDerivAt v (v' z) z) (hv_anti : AntitoneOn v' (Set.Ioi 0))
    (hh : ∀ z, 0 < z → HasDerivAt h (h' z) z) (hh_mono : MonotoneOn h' (Set.Ioi 0))
    (h49 : h' N = (1 - α) * A * N ^ (-α) * u' (A * N ^ (1 - α)))
    (h33 : v' m = (1 - Real.exp (-i)) * u' (A * N ^ (1 - α))) :
    (∀ N' m', 0 < N' → 0 < m' →
      u (A * N' ^ (1 - α)) + v m' - h N' ≤ u (A * N ^ (1 - α)) + v m - h N) ↔ i = 0 := by
  rw [planner_optimum_iff hA hα0 hα1 hN hm hu hu_anti hu_pos.le hv hv_anti hh hh_mono, h33,
    mul_eq_zero, or_iff_left hu_pos.ne', one_sub_exp_neg_eq_zero_iff]
  exact and_iff_right h49

/-- Galí (2015), p. 41: in a steady state with constant consumption the Euler equation reads
`e^{−i} = e^{−ρ} e^{−π}` (`Q = β/Π`); under the Friedman rule `i = 0` this gives `π = −ρ`,
i.e. `Π = e^π = β`, and deflation `π < 0` when `ρ > 0`. -/
theorem friedman_steady_state_inflation {i ρ π : ℝ}
    (hE : Real.exp (-i) = Real.exp (-ρ) * Real.exp (-π)) (hi : i = 0) :
    π = -ρ ∧ Real.exp π = Real.exp (-ρ) ∧ (0 < ρ → π < 0) := by
  rw [← Real.exp_add, Real.exp_eq_exp, hi] at hE
  have hπ : π = -ρ := by linarith
  exact ⟨hπ, by rw [hπ], fun h => by linarith⟩

/-! ### Indeterminacy under `i = 0` -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), p. 41 (the log-linear model): with `i ≡ 0`, output from (43)
`y_t = ψ_ya a_t + ψ_y` and adapted technology, the Euler equation (47) holds iff
`E_t π_{t+1} = −ρ − σ ψ_ya (E_t a_{t+1} − a_t)` at every date. -/
theorem friedman_euler_iff {σ ϖ ρ ψya ψy : ℝ} (hσ : σ ≠ 0) {a y infl : ℕ → Ω → ℝ}
    (hy : ∀ t, y t = ψya • a t + fun _ => ψy) :
    MIUNonseparable.EulerLinear 𝔼 σ ϖ ρ y (fun _ => 0) infl ↔
      ∀ t, 𝔼.E t (infl (t + 1)) = (fun _ => -ρ) - (σ * ψya) • (𝔼.E t (a (t + 1)) - a t) := by
  unfold MIUNonseparable.EulerLinear
  refine forall_congr' fun t => ?_
  rw [hy t, hy (t + 1), map_add, map_smul, 𝔼.const]
  simp only [funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_self, mul_zero,
    sub_zero, map_zero, Pi.zero_apply]
  constructor
  · intro h
    field_simp at h
    linear_combination -h
  · intro h
    field_simp
    linear_combination -h

/-- Galí (2015), p. 41 (**indeterminacy under `i = 0`**): with `i ≡ 0`, `y_t = ψ_ya a_t + ψ_y`
and `σ ≠ 0`, inflation is an equilibrium iff there is a martingale-difference sequence `ξ`
(`E_t ξ_{t+1} = 0`) with `π_{t+1} = −ρ − σ ψ_ya E_t Δa_{t+1} + ξ_{t+1}` at every date; any such
`ξ` gives an equilibrium. -/
theorem friedman_equilibrium_iff {σ ϖ ρ ψya ψy : ℝ} (hσ : σ ≠ 0) {a y infl : ℕ → Ω → ℝ}
    (haA : 𝔼.Adapted a) (hy : ∀ t, y t = ψya • a t + fun _ => ψy) :
    MIUNonseparable.EulerLinear 𝔼 σ ϖ ρ y (fun _ => 0) infl ↔
      ∃ ξ : ℕ → Ω → ℝ, (∀ t, 𝔼.E t (ξ (t + 1)) = 0) ∧ ∀ t,
        infl (t + 1) = (fun _ => -ρ) - (σ * ψya) • (𝔼.E t (a (t + 1)) - a t) + ξ (t + 1) := by
  rw [friedman_euler_iff 𝔼 hσ hy]
  have hEf : ∀ t, 𝔼.E t ((fun _ => -ρ) - (σ * ψya) • (𝔼.E t (a (t + 1)) - a t))
      = (fun _ => -ρ) - (σ * ψya) • (𝔼.E t (a (t + 1)) - a t) := by
    intro t
    rw [map_sub, 𝔼.const, map_smul, map_sub, ExpectationSystem.E_E_self, haA t]
  constructor
  · intro h
    refine ⟨fun s => match s with
      | 0 => 0
      | t + 1 => infl (t + 1) - ((fun _ => -ρ) - (σ * ψya) • (𝔼.E t (a (t + 1)) - a t)),
      fun t => ?_, fun t => ?_⟩
    · simp only
      rw [map_sub, h t, hEf t, sub_self]
    · simp only
      abel
  · rintro ⟨ξ, hξ, hπ⟩ t
    rw [hπ t, map_add, hξ t, add_zero, hEf t]

/-- Galí (2015), p. 41 (**two distinct equilibria under `i = 0`**): next to any equilibrium
inflation process there is a different one, obtained by changing date-0 inflation (hence
the initial price level) by any `c ≠ 0`; nothing in (43), (47) pins it down. -/
theorem friedman_indeterminate [Nonempty Ω] {σ ϖ ρ : ℝ} {y infl : ℕ → Ω → ℝ}
    (h : MIUNonseparable.EulerLinear 𝔼 σ ϖ ρ y (fun _ => 0) infl) {c : ℝ} (hc : c ≠ 0) :
    ∃ infl' : ℕ → Ω → ℝ, MIUNonseparable.EulerLinear 𝔼 σ ϖ ρ y (fun _ => 0) infl' ∧
      infl' ≠ infl := by
  refine ⟨fun s => match s with
    | 0 => infl 0 + fun (_ : Ω) => c
    | t + 1 => infl (t + 1), fun t => h t, fun he => hc ?_⟩
  have := congrFun (congrFun he 0) (Classical.arbitrary Ω)
  simpa using this

/-- Galí (2015), p. 41 (**a genuine sunspot**): under the two-coin-flip expectation system,
with constant technology and `i ≡ 0`, both the fundamental path `π_{t+1} = −ρ` and the sunspot
path `π_{t+1} = −ρ + ε_{t+1}` (`ε` the mean-zero coin-flip shock) are equilibria, and they
differ at date 1. -/
theorem friedman_sunspot_coin {σ ϖ ρ ψy : ℝ} (hσ : σ ≠ 0) :
    MIUNonseparable.EulerLinear ExpectationsFiniteTree.coinSystem σ ϖ ρ (fun _ _ => ψy)
        (fun _ => 0) (fun _ _ => -ρ) ∧
      MIUNonseparable.EulerLinear ExpectationsFiniteTree.coinSystem σ ϖ ρ (fun _ _ => ψy)
        (fun _ => 0) (fun t ω => -ρ + ExpectationsFiniteTree.coinShock t ω) ∧
      (fun t ω => -ρ + ExpectationsFiniteTree.coinShock t ω) ≠
        fun (_ : ℕ) (_ : Bool × Bool) => -ρ := by
  set 𝔼c := ExpectationsFiniteTree.coinSystem with h𝔼c
  have hy : ∀ _ : ℕ, (fun _ : Bool × Bool => ψy) = (0 : ℝ) • (fun _ : Bool × Bool => (0 : ℝ))
      + fun _ => ψy := fun _ => by
    funext ω
    simp
  have haA : 𝔼c.Adapted (fun _ _ => 0) := fun t => by
    rw [show (fun _ : Bool × Bool => (0 : ℝ)) = fun _ => 0 from rfl, 𝔼c.const]
  refine ⟨?_, ?_, ?_⟩
  · refine (friedman_equilibrium_iff 𝔼c hσ (a := fun _ _ => 0) haA hy).2
      ⟨fun _ => 0, fun t => map_zero _, fun t => ?_⟩
    funext ω
    simp [𝔼c.const]
  · refine (friedman_equilibrium_iff 𝔼c hσ (a := fun _ _ => 0) haA hy).2
      ⟨ExpectationsFiniteTree.coinShock, fun t => ExpectationsFiniteTree.coinShock_mean_zero t,
        fun t => ?_⟩
    funext ω
    simp [𝔼c.const]
  · intro he
    have := congrFun (congrFun he 1) (true, true)
    simp [ExpectationsFiniteTree.coinShock] at this

/-! ### Fn. 13: the rule `î_t = φ_π π̂_t` in the MIU model -/

/-- Galí (2015), fn. 13, p. 41 (exercise 2.6): the composite coefficient
`s = ϖ + σ ψ_yi = ϖ(φ + α)/D`. -/
theorem s_eq {ϖ σ φ α : ℝ} (hD : MIUNonseparable.bigD σ φ α ≠ 0) :
    ϖ + σ * MIUNonseparable.psiYi ϖ σ φ α = ϖ * (φ + α) / MIUNonseparable.bigD σ φ α := by
  unfold MIUNonseparable.psiYi
  field_simp
  unfold MIUNonseparable.bigD
  ring

/-- Galí (2015), fn. 13, p. 41: `s ≥ 0` for `ϖ ≥ 0`, `φ + α ≥ 0`, `D > 0`. -/
theorem s_nonneg {ϖ σ φ α : ℝ} (hD : 0 < MIUNonseparable.bigD σ φ α) (hϖ : 0 ≤ ϖ)
    (hφα : 0 ≤ φ + α) : 0 ≤ ϖ + σ * MIUNonseparable.psiYi ϖ σ φ α := by
  rw [s_eq hD.ne']
  exact div_nonneg (mul_nonneg hϖ hφα) hD.le

/-- Galí (2015), fn. 13, p. 41 (the log-linear model, deviations): output (43)
`ŷ = ψ_ya a + ψ_yi î`, the Euler equation (47) and the rule `î_t = φ_π π̂_t`. -/
def RuleSystem (σ ϖ ψya ψyi phiPi : ℝ) (a infl : ℕ → Ω → ℝ) : Prop :=
  MIUNonseparable.EulerLinear 𝔼 σ ϖ 0 (fun t => ψya • a t + ψyi • (phiPi • infl t))
    (fun t => phiPi • infl t) infl

/-- Galí (2015), fn. 13, p. 41: the node-wise algebra behind `ruleSystem_iff`. -/
theorem rule_real {σ ϖ ψya ψyi φπ at' Ea πt Eπ : ℝ} (hσ : σ ≠ 0) :
    ψya * at' + ψyi * (φπ * πt) = ψya * Ea + ψyi * (φπ * Eπ)
      - σ⁻¹ * (φπ * πt - Eπ - ϖ * (φπ * Eπ - φπ * πt) - 0) ↔
    (1 + φπ * (ϖ + σ * ψyi)) * Eπ = φπ * (1 + (ϖ + σ * ψyi)) * πt + σ * ψya * (at' - Ea) := by
  rw [← sub_eq_zero, ← sub_eq_zero (a := (1 + φπ * (ϖ + σ * ψyi)) * Eπ)]
  have key : ψya * at' + ψyi * (φπ * πt) - (ψya * Ea + ψyi * (φπ * Eπ)
      - σ⁻¹ * (φπ * πt - Eπ - ϖ * (φπ * Eπ - φπ * πt) - 0))
      = -σ⁻¹ * ((1 + φπ * (ϖ + σ * ψyi)) * Eπ
        - (φπ * (1 + (ϖ + σ * ψyi)) * πt + σ * ψya * (at' - Ea))) := by
    field_simp
    ring
  rw [key, neg_mul, neg_eq_zero, mul_eq_zero, or_iff_right (inv_ne_zero hσ)]

/-- Galí (2015), fn. 13, p. 41 (exercise 2.6): for `σ ≠ 0` the system holds iff
`(1 + φ_π s) E_t π_{t+1} = φ_π (1 + s) π_t + σ ψ_ya (a_t − E_t a_{t+1})`, `s = ϖ + σ ψ_yi`. -/
theorem ruleSystem_iff {σ ϖ ψya ψyi phiPi : ℝ} (hσ : σ ≠ 0) (a infl : ℕ → Ω → ℝ) :
    RuleSystem 𝔼 σ ϖ ψya ψyi phiPi a infl ↔ ∀ t,
      (1 + phiPi * (ϖ + σ * ψyi)) • 𝔼.E t (infl (t + 1))
        = (phiPi * (1 + (ϖ + σ * ψyi))) • infl t + (σ * ψya) • (a t - 𝔼.E t (a (t + 1))) := by
  unfold RuleSystem MIUNonseparable.EulerLinear
  refine forall_congr' fun t => ?_
  simp only [map_add, map_smul, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact rule_real hσ

/-- Galí (2015), fn. 13, p. 41 (**uniqueness for `φ_π > 1`**): with `s ≥ 0` and `σ ≠ 0`, two
bounded solutions of the system coincide. -/
theorem fn13_unique {σ ϖ ψya ψyi phiPi : ℝ} (hσ : σ ≠ 0) (hs : 0 ≤ ϖ + σ * ψyi)
    (hφ : 1 < phiPi) {a infl₁ infl₂ : ℕ → Ω → ℝ}
    (h₁ : RuleSystem 𝔼 σ ϖ ψya ψyi phiPi a infl₁) (h₂ : RuleSystem 𝔼 σ ϖ ψya ψyi phiPi a infl₂)
    (hb₁ : BoundedProc infl₁) (hb₂ : BoundedProc infl₂) : infl₁ = infl₂ := by
  set s := ϖ + σ * ψyi with hsdef
  have hpos : 0 < phiPi * (1 + s) := by nlinarith
  set c := (1 + phiPi * s) / (phiPi * (1 + s)) with hc
  have hc0 : 0 ≤ c := div_nonneg (by nlinarith) hpos.le
  have hc1 : c < 1 := (div_lt_one hpos).2 (by nlinarith)
  have e₁ := (ruleSystem_iff 𝔼 hσ a infl₁).1 h₁
  have e₂ := (ruleSystem_iff 𝔼 hσ a infl₂).1 h₂
  have hf : ∀ {π : ℕ → Ω → ℝ}, (∀ t, (1 + phiPi * s) • 𝔼.E t (π (t + 1))
      = (phiPi * (1 + s)) • π t + (σ * ψya) • (a t - 𝔼.E t (a (t + 1)))) →
      ∀ t, π t = c • 𝔼.E t (π (t + 1)) + (-(σ * ψya) / (phiPi * (1 + s))) •
        (a t - 𝔼.E t (a (t + 1))) := by
    intro π e t
    funext ω
    have := congrFun (e t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [hc]
    field_simp
    linear_combination -this
  have habs : |c| < 1 := by rw [abs_of_nonneg hc0]; exact hc1
  exact 𝔼.forward_unique habs (hf e₁) (hf e₂) hb₁ hb₂

/-- Galí (2015), fn. 13, p. 41 (**existence for `φ_π > 1`**): with bounded adapted technology,
the forward series is a bounded solution of the system. -/
theorem fn13_exists {σ ϖ ψya ψyi phiPi M : ℝ} (hσ : σ ≠ 0) (hs : 0 ≤ ϖ + σ * ψyi)
    (hφ : 1 < phiPi) {a : ℕ → Ω → ℝ} (haA : 𝔼.Adapted a) (hab : ∀ t ω, |a t ω| ≤ M) :
    ∃ infl : ℕ → Ω → ℝ, RuleSystem 𝔼 σ ϖ ψya ψyi phiPi a infl ∧ BoundedProc infl ∧
      𝔼.Adapted infl := by
  set s := ϖ + σ * ψyi with hsdef
  have hpos : 0 < phiPi * (1 + s) := by nlinarith
  set c := (1 + phiPi * s) / (phiPi * (1 + s)) with hc
  have hc0 : 0 ≤ c := div_nonneg (by nlinarith) hpos.le
  have hc1 : c < 1 := (div_lt_one hpos).2 (by nlinarith)
  set k := -(σ * ψya) / (phiPi * (1 + s)) with hk
  set u : ℕ → Ω → ℝ := fun t => k • (a t - 𝔼.E t (a (t + 1))) with hu
  have hub : ∀ t ω, |u t ω| ≤ |k| * (M + M) := by
    intro t ω
    simp only [hu, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hab t ω) ?_))
      (abs_nonneg k)
    exact 𝔼.abs_E_le (hab (t + 1)) t ω
  have huA : 𝔼.Adapted u := by
    intro t
    simp only [hu]
    rw [map_smul, map_sub, haA t, ExpectationSystem.E_E_self]
  refine ⟨𝔼.forwardSeries c u, ?_, 𝔼.forwardSeries_bounded hc0 hc1 hub,
    MIUNonseparable.forwardSeries_adapted 𝔼 hc0 hc1 hub⟩
  rw [ruleSystem_iff 𝔼 hσ]
  intro t
  have hsol := 𝔼.forwardSeries_solves hc0 hc1 hub huA t
  rw [hsol]
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu, Pi.sub_apply]
  rw [hc, hk]
  field_simp
  ring

/-- Galí (2015), fn. 13, p. 41 (**multiplicity for `0 ≤ φ_π ≤ 1`**): with `s ≥ 0`,
`σ ≠ 0`, next to any bounded solution there is a different bounded solution
`π_t + c^t`, `c = φ_π(1 + s)/(1 + φ_π s) ∈ [0, 1]` (a self-fulfilling deterministic path). -/
theorem fn13_not_unique [Nonempty Ω] {σ ϖ ψya ψyi phiPi : ℝ} (hσ : σ ≠ 0)
    (hs : 0 ≤ ϖ + σ * ψyi) (hφ0 : 0 ≤ phiPi) (hφ1 : phiPi ≤ 1) {a infl : ℕ → Ω → ℝ}
    (h : RuleSystem 𝔼 σ ϖ ψya ψyi phiPi a infl) (hb : BoundedProc infl) :
    ∃ infl' : ℕ → Ω → ℝ, RuleSystem 𝔼 σ ϖ ψya ψyi phiPi a infl' ∧ BoundedProc infl' ∧
      infl' ≠ infl := by
  set s := ϖ + σ * ψyi with hsdef
  have hden : 0 < 1 + phiPi * s := by nlinarith
  set c := phiPi * (1 + s) / (1 + phiPi * s) with hc
  have hc0 : 0 ≤ c := div_nonneg (by nlinarith) hden.le
  have hc1 : c ≤ 1 := (div_le_one hden).2 (by nlinarith)
  obtain ⟨M, hM⟩ := hb
  have e := (ruleSystem_iff 𝔼 hσ a infl).1 h
  refine ⟨fun t => infl t + fun _ => c ^ t, ?_, ⟨M + 1, fun t ω => ?_⟩, fun he => ?_⟩
  · rw [ruleSystem_iff 𝔼 hσ]
    intro t
    rw [map_add, 𝔼.const, smul_add, e t]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hc, pow_succ]
    field_simp
    ring
  · simp only [Pi.add_apply]
    refine (abs_add_le _ _).trans (add_le_add (hM t ω) ?_)
    rw [abs_of_nonneg (pow_nonneg hc0 t)]
    exact pow_le_one₀ hc0 hc1
  · have := congrFun (congrFun he 0) (Classical.arbitrary Ω)
    simp at this

/-! ### The rule `i_t = φ (r_{t−1} + π_t)` (p. 42), in the log-linear model -/

/-- Galí (2015), p. 42 (**uniqueness**, log-linear model): with the Fisher equation (22)
`i_t = r_t + E_t π_{t+1}`, an adapted real rate `r`, the rule `i_t = φ (r_{t−1} + π_t)`
(`r_{−1}` given) and `φ > 1`, every bounded nominal rate is `i ≡ 0`, and then
`π_0 = −r_{−1}`, `π_{t+1} = −r_t`. -/
theorem lagged_rule_unique {φ rm1 : ℝ} (hφ : 1 < φ) {r i infl : ℕ → Ω → ℝ}
    (hrA : 𝔼.Adapted r) (hF : ∀ t, i t = r t + 𝔼.E t (infl (t + 1)))
    (hR0 : i 0 = φ • ((fun _ => rm1) + infl 0)) (hR : ∀ t, i (t + 1) = φ • (r t + infl (t + 1)))
    (hib : BoundedProc i) :
    i = 0 ∧ infl 0 = (fun _ => -rm1) ∧ ∀ t, infl (t + 1) = -r t := by
  have hφ0 : φ ≠ 0 := by linarith
  have heq : ∀ t, i t = φ⁻¹ • 𝔼.E t (i (t + 1)) + 0 := by
    intro t
    rw [hR t, map_smul, map_add, hrA t, ← hF t, smul_smul, inv_mul_cancel₀ hφ0, one_smul,
      add_zero]
  have hz : ∀ t, (0 : ℕ → Ω → ℝ) t = φ⁻¹ • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + 0 := by
    intro t
    simp
  have habs : |φ⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith : (0 : ℝ) < φ)]
    exact inv_lt_one_of_one_lt₀ hφ
  have hi0 : i = 0 := 𝔼.forward_unique habs heq hz hib ⟨0, fun _ _ => by simp⟩
  refine ⟨hi0, ?_, fun t => ?_⟩
  · have h := hR0
    rw [hi0] at h
    funext ω
    have := congrFun h ω
    simp only [Pi.zero_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this
    have := (mul_eq_zero.1 this.symm).resolve_left hφ0
    linarith
  · have h := hR t
    rw [hi0] at h
    funext ω
    have := congrFun h ω
    simp only [Pi.zero_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this
    have := (mul_eq_zero.1 this.symm).resolve_left hφ0
    simp only [Pi.neg_apply]
    linarith

/-- Galí (2015), p. 42 (**existence**, log-linear model): `i ≡ 0`, `π_0 = −r_{−1}`,
`π_{t+1} = −r_t` satisfies the Fisher equation and the rule; inflation is adapted and is
bounded when `r` is. -/
theorem lagged_rule_exists (φ rm1 : ℝ) {r : ℕ → Ω → ℝ} (hrA : 𝔼.Adapted r) :
    let infl : ℕ → Ω → ℝ := fun s => match s with
      | 0 => fun _ => -rm1
      | t + 1 => -r t
    (∀ t, (0 : ℕ → Ω → ℝ) t = r t + 𝔼.E t (infl (t + 1))) ∧
      (0 : ℕ → Ω → ℝ) 0 = φ • ((fun _ => rm1) + infl 0) ∧
      (∀ t, (0 : ℕ → Ω → ℝ) (t + 1) = φ • (r t + infl (t + 1))) ∧ 𝔼.Adapted infl ∧
      (BoundedProc r → BoundedProc infl) := by
  intro infl
  refine ⟨fun t => ?_, ?_, fun t => ?_, fun t => ?_, fun ⟨M, hM⟩ => ⟨max M |rm1|, ?_⟩⟩
  · simp only [infl, map_neg, hrA t]
    simp
  · funext ω
    simp [infl]
  · funext ω
    simp [infl]
  · rcases t with _ | t
    · simp only [infl]
      exact 𝔼.const 0 (-rm1)
    · simp only [infl]
      rw [map_neg, ← hrA t, 𝔼.known (Nat.le_succ t)]
  · intro t ω
    rcases t with _ | t
    · simp [infl]
    · simp only [infl, Pi.neg_apply, abs_neg]
      exact (hM t ω).trans (le_max_left _ _)

/-- Galí (2015), p. 42: more generally, any policy that makes inflation move one-for-one and
inversely with the lagged real rate, `π_{t+1} = −r_t`, implies a zero nominal rate through
the Fisher equation (22), for adapted `r`. -/
theorem inflation_rule_implies_zero_rate {r i infl : ℕ → Ω → ℝ} (hrA : 𝔼.Adapted r)
    (hF : ∀ t, i t = r t + 𝔼.E t (infl (t + 1))) (hπ : ∀ t, infl (t + 1) = -r t) :
    ∀ t, i t = 0 := by
  intro t
  rw [hF t, hπ t, map_neg, hrA t, add_neg_cancel]

end Gali.ClassicalMonetaryModel.FriedmanRule
