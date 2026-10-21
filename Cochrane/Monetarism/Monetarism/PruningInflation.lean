/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.PruningDeflation
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Pruning inflationary equilibria: timing conventions

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix, Chapter 3, §3.2 and
§3.2.1 "Timing conventions in the inflationary equilibria", eqs. (3.3)–(3.5), pp. 618–621, with
(19.20)–(19.23), pp. 443–444. Perfect foresight.

Real balances relative to output `m_t = M_t/(P_t y) = M_t q_t/y`, where `q_t = 1/P_t ≥ 0` is the
value of money; `q_t = 0` (an infinite price level) is demonetisation and is `m_t = 0`.
With `A = (1+µ)/β = (1+δ)(1+µ)`, the map of (19.21) is `g(m) = A(1 − θm^{−γ})m`
(`PruningDeflation.ratioMap`), the demonetisation level is `m_p = θ^{1/γ}` (the pole
`x = θ^{−1/γ}` of (19.23)), and `m̄` is the inflationary steady state.

## Main results

* (3.3), "the price level eventually explodes to infinity in finite time":
  `finite_time_explosion`, `no_positive_path_below`, `explosion_x_form`.
* "there is not a continuum of inflationary equilibria, but a countable number": the equilibrium
  notion `IsEqm` (q-form, first-order condition at every date with valued money),
  `eqm_of_value` (from `q_t`), the terminal condition `terminal_balance`/`terminal_price`
  (`M_T = P_T y θ^{1/γ}`); the backward sequence `backward_exists`, `backward_unique`;
  the complete classification `eqm_initial_iff` (equilibrium initial real balances are
  `[m̄, ∞) ∪ {z_T : T ∈ ℕ}`), `eqm_demonetises`, `inflationary_initial_countable`,
  `backward_strictMono` (distinct `T`, distinct `P_0`), `backward_tendsto` (accumulating at
  `m̄`), `not_eqm_of_lt_wp`, `not_eqm_between`.
* (3.4)–(3.5): `md_discrete_iff`, `md_discrete_tendsto`, `md_cont_tendsto`,
  `md_ratio`, `md_ratio_tendsto`; the modified utility `modU`, its exact partial derivatives
  `modU_hasDerivAt_c`, `modU_hasDerivAt_m` (from `MoneyInUtility.hasDerivAt_power`), and
  `modified_foc_iff` (3.5); the inverse power demand is `MoneyInUtility.power_demand_iff`.
* p. 621: the new difference equation `new_map_of_foc`, steady state `new_fixed_iff`, the
  x-form `new_x_form`, positivity `new_map_pos` ("never goes to infinity in finite time"),
  `new_inflation_tendsto_zero`, `new_inflation_rate_tendsto`, and the continuum
  `new_inflationary_continuum`.
-/

namespace Cochrane.Monetarism.PruningInflation

open Filter Topology
open Cochrane.Monetarism.PruningDeflation
open Cochrane.Monetarism.MoneyInUtility (power_demand_iff hasDerivAt_power)

/-! ## The demonetisation level and the shape of the map -/

/-- Cochrane (2023), p. 619: the demonetisation level of real balances `m_p = θ^{1/γ}`
satisfies `θ m_p^{−γ} = 1`. -/
theorem wp_spec {θ γ : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) : θ * (θ ^ (1 / γ)) ^ (-γ) = 1 := by
  rw [← Real.rpow_mul hθ.le, show 1 / γ * -γ = -1 by field_simp, Real.rpow_neg_one]
  field_simp

/-- Cochrane (2023), p. 619: `g(m_p) = 0` — the value of money next period is zero. -/
theorem ratioMap_wp {β μ θ γ : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) :
    ratioMap β μ θ γ (θ ^ (1 / γ)) = 0 := by
  unfold ratioMap; rw [wp_spec hθ hγ]; ring

/-- Cochrane (2023), p. 619: for `m > 0`, `θm^{−γ} ≤ 1` iff `m ≥ m_p`. -/
theorem le_one_iff {θ γ m : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) (hm : 0 < m) :
    θ * m ^ (-γ) ≤ 1 ↔ θ ^ (1 / γ) ≤ m := by
  have hw := wp_spec hθ hγ
  have hwp : 0 < θ ^ (1 / γ) := by positivity
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have := Real.rpow_lt_rpow_of_neg hm hcon (by linarith : -γ < 0)
    nlinarith
  · intro h
    have := Real.rpow_le_rpow_of_nonpos hwp h (by linarith : -γ ≤ 0)
    nlinarith

/-- Cochrane (2023), p. 619: below the demonetisation level the map is negative,
`0 < m < m_p ⇒ g(m) < 0` (a negative next-period value of money is impossible). -/
theorem ratioMap_neg {β μ θ γ m : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ) (hγ : 0 < γ)
    (hm : 0 < m) (hlt : m < θ ^ (1 / γ)) : ratioMap β μ θ γ m < 0 := by
  have h1 : 1 < θ * m ^ (-γ) := by
    by_contra hcon; push Not at hcon
    exact absurd ((le_one_iff hθ hγ hm).mp hcon) (not_le.mpr hlt)
  unfold ratioMap
  have hA : 0 < (1 + μ) / β := div_pos hμ hβ
  have : (1 + μ) / β * (1 - θ * m ^ (-γ)) < 0 := mul_neg_of_pos_of_neg hA (by linarith)
  exact mul_neg_of_neg_of_pos this hm

/-- Cochrane (2023), Figure 19.1, p. 444: the map is strictly increasing on `[m_p, ∞)`. -/
theorem ratioMap_strictMonoOn {β μ θ γ : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) : StrictMonoOn (ratioMap β μ θ γ) (Set.Ici (θ ^ (1 / γ))) := by
  intro a ha b hb hab
  have hwp : 0 < θ ^ (1 / γ) := by positivity
  have ha0 : 0 < a := lt_of_lt_of_le hwp ha
  have hb0 : 0 < b := lt_trans ha0 hab
  have hA : 0 < (1 + μ) / β := div_pos hμ hβ
  have hfa : 0 ≤ 1 - θ * a ^ (-γ) := by linarith [(le_one_iff hθ hγ ha0).mpr ha]
  have hab' : b ^ (-γ) < a ^ (-γ) := Real.rpow_lt_rpow_of_neg ha0 hab (by linarith)
  have hfb : 1 - θ * a ^ (-γ) < 1 - θ * b ^ (-γ) := by nlinarith
  unfold ratioMap
  have h1 : (1 - θ * a ^ (-γ)) * a ≤ (1 - θ * a ^ (-γ)) * b :=
    mul_le_mul_of_nonneg_left hab.le hfa
  have h2 : (1 - θ * a ^ (-γ)) * b < (1 - θ * b ^ (-γ)) * b := mul_lt_mul_of_pos_right hfb hb0
  have := mul_lt_mul_of_pos_left (lt_of_le_of_lt h1 h2) hA
  linarith

/-- Cochrane (2023), Figure 19.1, p. 444: the map is continuous on `(0, ∞)`. -/
theorem ratioMap_continuousOn {β μ θ γ : ℝ} :
    ContinuousOn (ratioMap β μ θ γ) (Set.Ioi 0) := by
  unfold ratioMap
  refine ContinuousOn.mul (continuousOn_const.mul (continuousOn_const.sub
    (continuousOn_const.mul ?_))) continuousOn_id
  exact fun x hx => (Real.continuousAt_rpow_const x (-γ)
    (Or.inl (ne_of_gt hx))).continuousWithinAt

/-- Cochrane (2023), p. 444: the inflationary steady state lies above the demonetisation
level, `m_p < m̄`, when `β < 1 + µ`. -/
theorem wp_lt_ms {β μ θ γ ms : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ) (hγ : 0 < γ)
    (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) : θ ^ (1 / γ) < ms := by
  have h1 : θ * ms ^ (-γ) < 1 := by rw [hss]; have := div_pos hβ hμ; linarith
  rcases lt_or_ge (θ ^ (1 / γ)) ms with h | h
  · exact h
  · exfalso
    rcases h.lt_or_eq with h' | h'
    · have := Real.rpow_lt_rpow_of_neg hms h' (by linarith : -γ < 0)
      have hw := wp_spec hθ hγ
      nlinarith
    · rw [h', wp_spec hθ hγ] at h1; linarith

/-- Cochrane (2023), p. 444, "dynamics are unstable around `P y/M`": on `[m_p, m̄)` the map lies
below the diagonal, `g(m) < m`. -/
theorem ratioMap_lt_self {β μ θ γ ms m : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) (hm : 0 < m) (hlt : m < ms) :
    ratioMap β μ θ γ m < m := by
  have hA : 0 < (1 + μ) / β := div_pos hμ hβ
  have h1 : ms ^ (-γ) < m ^ (-γ) := Real.rpow_lt_rpow_of_neg hm hlt (by linarith)
  have h2 : (1 + μ) / β * (1 - θ * ms ^ (-γ)) = 1 := by rw [hss]; field_simp; ring
  have h3 : (1 + μ) / β * (1 - θ * m ^ (-γ)) < 1 := by nlinarith [mul_lt_mul_of_pos_left h1 hθ]
  unfold ratioMap
  nlinarith

/-- Cochrane (2023), p. 444: on `[m̄, ∞)` the map lies on or above the diagonal. -/
theorem self_le_ratioMap {β μ θ γ ms m : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) (hle : ms ≤ m) :
    m ≤ ratioMap β μ θ γ m := by
  have hA : 0 < (1 + μ) / β := div_pos hμ hβ
  have hm : 0 < m := lt_of_lt_of_le hms hle
  have h1 : m ^ (-γ) ≤ ms ^ (-γ) := Real.rpow_le_rpow_of_nonpos hms hle (by linarith)
  have h2 : (1 + μ) / β * (1 - θ * ms ^ (-γ)) = 1 := by rw [hss]; field_simp; ring
  have h3 : 1 ≤ (1 + μ) / β * (1 - θ * m ^ (-γ)) := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hθ.le]
  unfold ratioMap
  nlinarith

/-- Cochrane (2023), p. 444: the only positive fixed point of the map is `m̄`. -/
theorem fixed_unique {β μ θ γ ms L : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hγ : 0 < γ)
    (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) (hθ : 0 < θ) (hL : 0 < L)
    (hfix : ratioMap β μ θ γ L = L) : L = ms := by
  have h := (fixed_iff hβ hμ hL).mp hfix
  rcases lt_trichotomy L ms with h1 | h1 | h1
  · have := Real.rpow_lt_rpow_of_neg hL h1 (by linarith : -γ < 0); nlinarith
  · exact h1
  · have := Real.rpow_lt_rpow_of_neg hms h1 (by linarith : -γ < 0); nlinarith

/-! ## (3.3): finite-time explosion -/

/-- Cochrane (2023), eq. (3.3), p. 619, "For `P_0y/M_0 > P̄y/M`, the price level eventually
explodes to infinity in finite time. The denominator goes to zero or worse": every forward
orbit from `0 < m₀ < m̄` reaches `m_T ≤ m_p = θ^{1/γ}` (i.e. `1 − θx_T^γ ≤ 0`) at a finite
date, staying above `m_p` before. (Survey E22: the printed condition `P_0y/M_0 > PM/M`
should read `> P̄y/M`.) -/
theorem finite_time_explosion {β μ θ γ ms m0 : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) (hm0 : 0 < m0)
    (hlt : m0 < ms) :
    ∃ T, (ratioMap β μ θ γ)^[T] m0 ≤ θ ^ (1 / γ) ∧
      ∀ t < T, θ ^ (1 / γ) < (ratioMap β μ θ γ)^[t] m0 := by
  set g := ratioMap β μ θ γ with hg
  set z : ℕ → ℝ := fun t => g^[t] m0 with hz
  have hzs : ∀ t, z (t + 1) = g (z t) := fun t => Function.iterate_succ_apply' _ _ _
  have hex : ∃ T, z T ≤ θ ^ (1 / γ) := by
    by_contra hcon
    push Not at hcon
    have hwp : 0 < θ ^ (1 / γ) := by positivity
    have hA : 0 < (1 + μ) / β := div_pos hμ hβ
    set r := (1 + μ) / β * (1 - θ * m0 ^ (-γ)) with hr
    have hm0wp : θ ^ (1 / γ) < m0 := by simpa [hz] using hcon 0
    have hr0 : 0 ≤ r := by
      have := (le_one_iff hθ hγ hm0).mpr hm0wp.le
      exact mul_nonneg hA.le (by linarith)
    have hr1 : r < 1 := by
      have h1 : ms ^ (-γ) < m0 ^ (-γ) := Real.rpow_lt_rpow_of_neg hm0 hlt (by linarith)
      have h2 : (1 + μ) / β * (1 - θ * ms ^ (-γ)) = 1 := by rw [hss]; field_simp; ring
      rw [hr]; nlinarith [mul_lt_mul_of_pos_left h1 hθ]
    have hbound : ∀ t, z t ≤ m0 ∧ z t ≤ r ^ t * m0 := by
      intro t
      induction t with
      | zero => simp [hz]
      | succ n ih =>
        have hzn : 0 < z n := lt_trans hwp (hcon n)
        have hle : m0 ^ (-γ) ≤ z n ^ (-γ) := Real.rpow_le_rpow_of_nonpos hzn ih.1 (by linarith)
        have hstep : z (n + 1) ≤ r * z n := by
          rw [hzs, hg]; unfold ratioMap
          have : (1 + μ) / β * (1 - θ * z n ^ (-γ)) ≤ r := by
            rw [hr]; apply mul_le_mul_of_nonneg_left _ hA.le; nlinarith
          nlinarith
        constructor
        · nlinarith
        · rw [pow_succ]; nlinarith [pow_nonneg hr0 n]
    have hlim : Tendsto (fun t => r ^ t * m0) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const m0
    obtain ⟨t, ht⟩ := (hlim.eventually (gt_mem_nhds hwp)).exists
    linarith [(hbound t).2, hcon t]
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, fun t ht => ?_⟩
  have := Nat.find_min hex ht
  push Not at this
  exact this

/-- Cochrane (2023), eq. (3.3), p. 619: `m ≤ m_p` iff the denominator of (3.3) is non-positive,
`1 − θ x^γ ≤ 0` with `x = P y/M = 1/m`. -/
theorem explosion_x_form {θ γ m : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) (hm : 0 < m) :
    m ≤ θ ^ (1 / γ) ↔ 1 - θ * (1 / m) ^ γ ≤ 0 := by
  have hinv : (1 / m) ^ γ = m ^ (-γ) := by
    rw [Real.rpow_neg hm.le, one_div, Real.inv_rpow hm.le]
  rw [hinv]
  have hwp : 0 < θ ^ (1 / γ) := by positivity
  constructor
  · intro h
    have := Real.rpow_le_rpow_of_nonpos hm h (by linarith : -γ ≤ 0)
    have hw := wp_spec hθ hγ
    nlinarith
  · intro h
    by_contra hcon
    push Not at hcon
    have := (le_one_iff hθ hγ hm).mpr hcon.le
    have h2 : θ * m ^ (-γ) = 1 := by linarith
    have h3 := Real.rpow_lt_rpow_of_neg hwp hcon (by linarith : -γ < 0)
    have hw := wp_spec hθ hγ
    nlinarith

/-- Cochrane (2023), eq. (3.3), p. 619: no perfect-foresight path with valued money at every
date starts below the steady state, `¬(IsMPath m ∧ m₀ < m̄)`. -/
theorem no_positive_path_below {β μ θ γ ms : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ))
    (hpath : IsMPath β μ θ γ m) : ms ≤ m 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨T, hT, -⟩ := finite_time_explosion hβ hμ hθ hγ hss (hpath 0).1 hcon
  have horbit : ∀ t, m t = (ratioMap β μ θ γ)^[t] (m 0) := by
    intro t
    induction t with
    | zero => rfl
    | succ n ih => rw [(hpath n).2, ih, Function.iterate_succ_apply']
  rw [← horbit] at hT
  have hpos := (hpath (T + 1)).1
  rw [(hpath T).2] at hpos
  rcases hT.lt_or_eq with h | h
  · linarith [ratioMap_neg hβ hμ hθ hγ (hpath T).1 h]
  · rw [h, ratioMap_wp hθ hγ] at hpos; linarith

/-! ## Equilibria with demonetisation: countably many inflationary equilibria -/

/-- Cochrane (2023), §3.2.1, p. 619: a perfect-foresight equilibrium in real balances
`m_t = M_tq_t/y ≥ 0` (`q_t = 1/P_t` the value of money). While money is valued (`m_t > 0`) the
first-order condition (19.21) holds; once money is worthless it stays worthless. -/
def IsEqm (β μ θ γ : ℝ) (m : ℕ → ℝ) : Prop :=
  ∀ t, 0 ≤ m t ∧ (0 < m t → m (t + 1) = ratioMap β μ θ γ (m t)) ∧ (m t = 0 → m (t + 1) = 0)

/-- Cochrane (2023), (19.21) in value-of-money form, p. 619: with `M_t = (1+µ)M_{t−1} > 0`,
`q_t ≥ 0`, the condition `θ(M_tq_t/y)^{−γ} = 1 − βq_{t+1}/q_t` whenever `q_t > 0` (a finite
price level), and `q_{t+1} = 0` after `q_t = 0`, the real balances `M_tq_t/y` form an `IsEqm`. -/
theorem eqm_of_value {β μ θ γ y : ℝ} {M q : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hy : 0 < y)
    (hM : ∀ t, 0 < M t) (hgrow : ∀ t, M (t + 1) = (1 + μ) * M t) (hq : ∀ t, 0 ≤ q t)
    (hfoc : ∀ t, 0 < q t → θ * (M t * q t / y) ^ (-γ) = 1 - β * q (t + 1) / q t)
    (hzero : ∀ t, q t = 0 → q (t + 1) = 0) :
    IsEqm β μ θ γ (fun t => M t * q t / y) := by
  intro t
  have hMt := hM t
  refine ⟨by have := hq t; positivity, fun hpos => ?_, fun h0 => ?_⟩
  · have hqt : 0 < q t := by
      by_contra h; push Not at h
      have : q t = 0 := le_antisymm h (hq t)
      simp [this] at hpos
    unfold ratioMap
    dsimp only
    rw [hfoc t hqt, hgrow]
    field_simp
    ring
  · have hqt : q t = 0 := by
      have : M t * q t = 0 := by
        have := div_eq_zero_iff.mp h0
        rcases this with h | h
        · exact h
        · exact absurd h hy.ne'
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hMt.ne'
      · exact h
    simp [hzero t hqt]

/-- Cochrane (2023), p. 619, "If consumers know that the price level will be infinite at time
`T + 1`, then money demand at time `T` is `M_T = P_T y θ^{1/γ}`": in an equilibrium with
`m_T > 0` and `m_{T+1} = 0`, `m_T = θ^{1/γ}`. -/
theorem terminal_balance {β μ θ γ : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) (heqm : IsEqm β μ θ γ m) {T : ℕ} (hT : 0 < m T) (hT1 : m (T + 1) = 0) :
    m T = θ ^ (1 / γ) := by
  have h := (heqm T).2.1 hT
  rw [hT1] at h
  unfold ratioMap at h
  have hA : 0 < (1 + μ) / β := div_pos hμ hβ
  have h1 : θ * m T ^ (-γ) = 1 := by
    have : (1 + μ) / β * (1 - θ * m T ^ (-γ)) = 0 := by
      rcases mul_eq_zero.mp h.symm with h2 | h2
      · exact h2
      · exact absurd h2 hT.ne'
    rcases mul_eq_zero.mp this with h2 | h2
    · exact absurd h2 hA.ne'
    · linarith
  have h2 : m T ^ (-γ) = (θ ^ (1 / γ)) ^ (-γ) :=
    mul_left_cancel₀ hθ.ne' (h1.trans (wp_spec hθ hγ).symm)
  have h3 := congrArg (fun z => z ^ (-γ)⁻¹) h2
  rwa [Real.rpow_rpow_inv hT.le (by linarith),
    Real.rpow_rpow_inv (by positivity) (by linarith)] at h3

/-- Cochrane (2023), p. 619, "so the last period price level is `P_T = (M_T/y) θ^{−1/γ}`". -/
theorem terminal_price {θ γ y MT PT : ℝ} (hθ : 0 < θ) (hy : 0 < y) (hP : 0 < PT)
    (h : MT / (PT * y) = θ ^ (1 / γ)) : PT = MT / y * θ ^ (-(1 / γ)) := by
  rw [Real.rpow_neg hθ.le, ← h]
  have : MT ≠ 0 := by
    intro h0; rw [h0, zero_div] at h; have : 0 < θ ^ (1 / γ) := by positivity
    linarith
  field_simp

/-- Cochrane (2023), p. 619, "We work back from this terminal condition": the backward
sequence `z_0 = m_p = θ^{1/γ}`, `g(z_{k+1}) = z_k`, `m_p ≤ z_k < m̄`. -/
def IsBackward (β μ θ γ ms : ℝ) (z : ℕ → ℝ) : Prop :=
  z 0 = θ ^ (1 / γ) ∧ (∀ k, ratioMap β μ θ γ (z (k + 1)) = z k) ∧
    ∀ k, θ ^ (1 / γ) ≤ z k ∧ z k < ms

/-- Cochrane (2023), p. 619: the backward recursion from the terminal condition is
well-defined: a backward sequence exists. -/
theorem backward_exists {β μ θ γ ms : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) :
    ∃ z, IsBackward β μ θ γ ms z := by
  set g := ratioMap β μ θ γ with hg
  set wp := θ ^ (1 / γ) with hwpdef
  have hwp : 0 < wp := by positivity
  have hwpms := wp_lt_ms hβ hμ hθ hγ hms hss
  have hgms : g ms = ms := (fixed_iff hβ hμ hms).mpr hss
  have hpre : ∀ y : ℝ, ∃ x : ℝ, y ∈ Set.Ico 0 ms → x ∈ Set.Ico wp ms ∧ g x = y := by
    intro y
    by_cases hy : y ∈ Set.Ico 0 ms
    · have hc : ContinuousOn g (Set.Icc wp ms) :=
        ratioMap_continuousOn.mono fun x hx => lt_of_lt_of_le hwp hx.1
      have hlo : g wp ≤ y := by rw [hg, ratioMap_wp hθ hγ]; exact hy.1
      have hhi : y ≤ g ms := by rw [hgms]; exact hy.2.le
      obtain ⟨x, hx, hgx⟩ := intermediate_value_Icc hwpms.le hc ⟨hlo, hhi⟩
      refine ⟨x, fun _ => ⟨⟨hx.1, ?_⟩, hgx⟩⟩
      rcases hx.2.lt_or_eq with h | h
      · exact h
      · rw [h, hgms] at hgx; exact absurd hgx.symm (ne_of_lt hy.2)
    · exact ⟨0, fun h => absurd h hy⟩
  choose pre hpre using hpre
  set z : ℕ → ℝ := fun k => pre^[k] wp with hz
  have hzs : ∀ k, z (k + 1) = pre (z k) := fun k => Function.iterate_succ_apply' _ _ _
  have hmem : ∀ k, z k ∈ Set.Ico wp ms := by
    intro k
    induction k with
    | zero => exact ⟨le_rfl, hwpms⟩
    | succ n ih =>
      rw [hzs]; exact (hpre _ ⟨le_trans hwp.le ih.1, ih.2⟩).1
  refine ⟨z, rfl, fun k => ?_, fun k => hmem k⟩
  rw [hzs]
  exact (hpre _ ⟨le_trans hwp.le (hmem k).1, (hmem k).2⟩).2

/-- Cochrane (2023), p. 619: the backward sequence is unique (the map is injective on
`[m_p, ∞)`). -/
theorem backward_unique {β μ θ γ ms : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) {z z' : ℕ → ℝ} (hz : IsBackward β μ θ γ ms z)
    (hz' : IsBackward β μ θ γ ms z') : z = z' := by
  funext k
  induction k with
  | zero => rw [hz.1, hz'.1]
  | succ n ih =>
    have h : ratioMap β μ θ γ (z (n + 1)) = ratioMap β μ θ γ (z' (n + 1)) := by
      rw [hz.2.1, hz'.2.1, ih]
    exact (ratioMap_strictMonoOn hβ hμ hθ hγ).injOn (hz.2.2 (n + 1)).1 (hz'.2.2 (n + 1)).1 h

/-- Cochrane (2023), p. 619, "For each such `T` there is a different `P_0y/M_0`": the backward
sequence is strictly increasing. -/
theorem backward_strictMono {β μ θ γ ms : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) {z : ℕ → ℝ}
    (hz : IsBackward β μ θ γ ms z) : StrictMono z := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  have hwp : 0 < θ ^ (1 / γ) := by positivity
  have h := ratioMap_lt_self hβ hμ hθ hγ hss (lt_of_lt_of_le hwp (hz.2.2 (k + 1)).1)
    (hz.2.2 (k + 1)).2
  rw [hz.2.1] at h
  exact h

/-- Cochrane (2023), p. 619 and Figure 3.1: the initial real balances of the inflationary
equilibria accumulate at the steady state, `z_T → m̄`. -/
theorem backward_tendsto {β μ θ γ ms : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) {z : ℕ → ℝ}
    (hz : IsBackward β μ θ γ ms z) : Tendsto z atTop (𝓝 ms) := by
  have hmono := (backward_strictMono hβ hμ hθ hγ hss hz).monotone
  have hbdd : BddAbove (Set.range z) := ⟨ms, by rintro _ ⟨k, rfl⟩; exact (hz.2.2 k).2.le⟩
  have hlim := tendsto_atTop_ciSup hmono hbdd
  set L := ⨆ k, z k with hL
  have hwp : 0 < θ ^ (1 / γ) := by positivity
  have hL0 : 0 < L := lt_of_lt_of_le hwp (le_trans (hz.2.2 0).1 (le_ciSup hbdd 0))
  have hc : ContinuousAt (ratioMap β μ θ γ) L :=
    ratioMap_continuousOn.continuousAt (Ioi_mem_nhds hL0)
  have h1 : Tendsto (fun k => ratioMap β μ θ γ (z (k + 1))) atTop (𝓝 (ratioMap β μ θ γ L)) :=
    hc.tendsto.comp ((tendsto_add_atTop_iff_nat 1).mpr hlim)
  have h2 : Tendsto (fun k => ratioMap β μ θ γ (z (k + 1))) atTop (𝓝 L) := by
    simpa only [hz.2.1] using hlim
  have hfix := tendsto_nhds_unique h1 h2
  rw [← fixed_unique hβ hμ hγ hms hss hθ hL0 hfix]
  exact hlim

/-- Cochrane (2023), p. 619: every equilibrium starting below the steady state demonetises in
finite time: there is `T` with `m_t > 0` for `t ≤ T`, `m_T = θ^{1/γ}`, `m_{T+1} = 0`, and the
initial balances equal the backward value `z_T`. -/
theorem eqm_demonetises {β μ θ γ ms : ℝ} {m z : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ))
    (hz : IsBackward β μ θ γ ms z) (heqm : IsEqm β μ θ γ m) (h0 : 0 < m 0) (hlt : m 0 < ms) :
    ∃ T, (∀ t ≤ T, 0 < m t) ∧ m T = θ ^ (1 / γ) ∧ m (T + 1) = 0 ∧ m 0 = z T := by
  set g := ratioMap β μ θ γ with hg
  set wp := θ ^ (1 / γ) with hwpdef
  have hwp : 0 < wp := by positivity
  have hex : ∃ T, m T ≤ wp := by
    by_contra hcon
    push Not at hcon
    have hpath : IsMPath β μ θ γ m := fun t =>
      ⟨lt_trans hwp (hcon t), (heqm t).2.1 (lt_trans hwp (hcon t))⟩
    exact absurd (no_positive_path_below hβ hμ hθ hγ hss hpath) (not_le.mpr hlt)
  classical
  set T := Nat.find hex with hTdef
  have hTle : m T ≤ wp := Nat.find_spec hex
  have hbefore : ∀ t < T, wp < m t := fun t ht => by
    have := Nat.find_min hex ht; push Not at this; exact this
  have hTpos : 0 < m T := by
    rcases Nat.eq_zero_or_pos T with h | h
    · rw [h]; exact h0
    · obtain ⟨n, hn⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
      have hn' : wp < m n := hbefore n (by omega)
      rw [hn, (heqm n).2.1 (lt_trans hwp hn')]
      have := (ratioMap_strictMonoOn hβ hμ hθ hγ) (Set.mem_Ici.mpr le_rfl)
        (Set.mem_Ici.mpr hn'.le) hn'
      rw [ratioMap_wp hθ hγ] at this
      exact this
  have hTeq : m T = wp := by
    rcases hTle.lt_or_eq with h | h
    · have h1 := (heqm (T + 1)).1
      rw [(heqm T).2.1 hTpos] at h1
      linarith [ratioMap_neg hβ hμ hθ hγ hTpos h]
    · exact h
  have hT1 : m (T + 1) = 0 := by
    rw [(heqm T).2.1 hTpos, hTeq, hwpdef, ratioMap_wp hθ hγ]
  have hpos : ∀ t ≤ T, 0 < m t := by
    intro t ht
    rcases ht.lt_or_eq with h | h
    · exact lt_trans hwp (hbefore t h)
    · rw [h]; exact hTpos
  refine ⟨T, hpos, hTeq, hT1, ?_⟩
  have hback : ∀ k ≤ T, m (T - k) = z k := by
    intro k
    induction k with
    | zero => intro _; rw [Nat.sub_zero, hTeq, hz.1]
    | succ n ih =>
      intro hn
      have hm1 : wp < m (T - (n + 1)) := hbefore _ (by omega)
      have hstep : ratioMap β μ θ γ (m (T - (n + 1))) = m (T - n) := by
        rw [← (heqm _).2.1 (lt_trans hwp hm1)]
        congr 1; omega
      rw [ih (by omega), ← hz.2.1 n] at hstep
      exact (ratioMap_strictMonoOn hβ hμ hθ hγ).injOn hm1.le (hz.2.2 (n + 1)).1 hstep
  simpa using hback T le_rfl

/-- Cochrane (2023), p. 619: conversely, for every `T` the path `m_t = z_{T−t}` (`t ≤ T`),
`m_t = 0` (`t > T`) is an equilibrium: valued money until `T`, demonetisation at `T + 1`. -/
theorem eqm_of_backward {β μ θ γ ms : ℝ} {z : ℕ → ℝ} (hθ : 0 < θ) (hγ : 0 < γ)
    (hz : IsBackward β μ θ γ ms z) (T : ℕ) :
    IsEqm β μ θ γ (fun t => if t ≤ T then z (T - t) else 0) := by
  have hwp : 0 < θ ^ (1 / γ) := by positivity
  intro t
  by_cases ht : t ≤ T
  · have hzpos : 0 < z (T - t) := lt_of_lt_of_le hwp (hz.2.2 _).1
    simp only [ht, ↓reduceIte]
    refine ⟨hzpos.le, fun _ => ?_, fun h => absurd h hzpos.ne'⟩
    by_cases ht1 : t + 1 ≤ T
    · simp only [ht1, ↓reduceIte]
      have : T - t = (T - (t + 1)) + 1 := by omega
      rw [this, hz.2.1]
    · simp only [ht1, ↓reduceIte]
      have : T - t = 0 := by omega
      rw [this, hz.1, ratioMap_wp hθ hγ]
  · have ht1 : ¬ t + 1 ≤ T := by omega
    simp only [ht, ht1, ↓reduceIte]
    exact ⟨le_rfl, fun h => absurd h (lt_irrefl 0), by simp⟩

/-- Cochrane (2023), §19.3.2, p. 444, and p. 619: from `m₀ ≥ m̄` the forward orbit is an
equilibrium that never demonetises. -/
theorem eqm_of_ge {β μ θ γ ms m0 : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ) (hγ : 0 < γ)
    (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) (hm0 : ms ≤ m0) :
    IsEqm β μ θ γ (fun t => (ratioMap β μ θ γ)^[t] m0) ∧
      ∀ t, ms ≤ (ratioMap β μ θ γ)^[t] m0 := by
  have hge : ∀ t, ms ≤ (ratioMap β μ θ γ)^[t] m0 := by
    intro t
    induction t with
    | zero => exact hm0
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans ih (self_le_ratioMap hβ hμ hθ hγ hms hss ih)
  refine ⟨fun t => ⟨le_trans hms.le (hge t), fun _ => Function.iterate_succ_apply' _ _ _,
    fun h => absurd h (ne_of_gt (lt_of_lt_of_le hms (hge t)))⟩, hge⟩

/-- Cochrane (2023), p. 619, "there is not a continuum of inflationary equilibria, but a
countable number": the complete classification. Positive initial real balances `m₀` start an
equilibrium iff `m₀ ≥ m̄` or `m₀ = z_T` for some `T`. -/
theorem eqm_initial_iff {β μ θ γ ms m0 : ℝ} {z : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ))
    (hz : IsBackward β μ θ γ ms z) (hm0 : 0 < m0) :
    (∃ m, IsEqm β μ θ γ m ∧ m 0 = m0) ↔ ms ≤ m0 ∨ ∃ T, m0 = z T := by
  constructor
  · rintro ⟨m, heqm, rfl⟩
    rcases le_or_gt ms (m 0) with h | h
    · exact Or.inl h
    · obtain ⟨T, -, -, -, hT⟩ := eqm_demonetises hβ hμ hθ hγ hss hz heqm hm0 h
      exact Or.inr ⟨T, hT⟩
  · rintro (h | ⟨T, rfl⟩)
    · exact ⟨_, (eqm_of_ge hβ hμ hθ hγ hms hss h).1, rfl⟩
    · exact ⟨_, eqm_of_backward hθ hγ hz T, by simp⟩

/-- Cochrane (2023), p. 619: the set of initial real balances of inflationary equilibria
(`0 < m₀ < m̄`) is exactly the range of the backward sequence, hence countable. -/
theorem inflationary_initial_countable {β μ θ γ ms : ℝ} {z : ℕ → ℝ} (hβ : 0 < β)
    (hμ : 0 < 1 + μ) (hθ : 0 < θ) (hγ : 0 < γ) (hms : 0 < ms)
    (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) (hz : IsBackward β μ θ γ ms z) :
    {m0 | 0 < m0 ∧ m0 < ms ∧ ∃ m, IsEqm β μ θ γ m ∧ m 0 = m0} = Set.range z ∧
      {m0 | 0 < m0 ∧ m0 < ms ∧ ∃ m, IsEqm β μ θ γ m ∧ m 0 = m0}.Countable := by
  have hwp : 0 < θ ^ (1 / γ) := by positivity
  have hset : {m0 | 0 < m0 ∧ m0 < ms ∧ ∃ m, IsEqm β μ θ γ m ∧ m 0 = m0} = Set.range z := by
    ext m0
    constructor
    · rintro ⟨h0, hlt, hex⟩
      rcases (eqm_initial_iff hβ hμ hθ hγ hms hss hz h0).mp hex with h | ⟨T, hT⟩
      · exact absurd h (not_le.mpr hlt)
      · exact ⟨T, hT.symm⟩
    · rintro ⟨T, rfl⟩
      have hzT : 0 < z T := lt_of_lt_of_le hwp (hz.2.2 T).1
      exact ⟨hzT, (hz.2.2 T).2,
        (eqm_initial_iff hβ hμ hθ hγ hms hss hz hzT).mpr (Or.inr ⟨T, rfl⟩)⟩
  exact ⟨hset, hset ▸ Set.countable_range z⟩

/-- Cochrane (2023), p. 619: initial real balances below the demonetisation level start no
equilibrium. -/
theorem not_eqm_of_lt_wp {β μ θ γ m0 : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) (hm0 : 0 < m0) (hlt : m0 < θ ^ (1 / γ)) :
    ¬ ∃ m, IsEqm β μ θ γ m ∧ m 0 = m0 := by
  rintro ⟨m, heqm, rfl⟩
  have h1 := (heqm 1).1
  rw [(heqm 0).2.1 hm0] at h1
  linarith [ratioMap_neg hβ hμ hθ hγ hm0 hlt]

/-- Cochrane (2023), p. 619, "not a continuum": initial real balances strictly between the first
two backward values `z_0 = θ^{1/γ}` and `z_1` start no equilibrium; and the inflationary
initial values are a countable subset of the uncountable interval `(0, m̄)`. -/
theorem not_eqm_between {β μ θ γ ms m0 : ℝ} {z : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ))
    (hz : IsBackward β μ θ γ ms z) (h1 : z 0 < m0) (h2 : m0 < z 1) :
    (¬ ∃ m, IsEqm β μ θ γ m ∧ m 0 = m0) ∧ ¬ (Set.Ioo 0 ms).Countable := by
  have hwp : 0 < θ ^ (1 / γ) := by positivity
  have hm0 : 0 < m0 := lt_trans (by rw [hz.1]; exact hwp) h1
  have hmono := backward_strictMono hβ hμ hθ hγ hss hz
  refine ⟨fun hex => ?_, by rw [Cardinal.Real.Ioo_countable_iff]; linarith⟩
  rcases (eqm_initial_iff hβ hμ hθ hγ hms hss hz hm0).mp hex with h | ⟨T, hT⟩
  · linarith [(hz.2.2 1).2]
  · rcases Nat.eq_zero_or_pos T with h0 | h0
    · rw [hT, h0] at h1; exact lt_irrefl _ h1
    · have := hmono.monotone (Nat.one_le_iff_ne_zero.mpr h0.ne')
      rw [← hT] at this; linarith

/-! ## (3.4)–(3.5): discrete versus continuous money demand -/

/-- Cochrane (2023), eq. (3.4), p. 620: discrete-time money demand per unit of nominal income,
`M/(Py) = ((1/θ) i/(1+i))^{−1/γ}`. -/
noncomputable def mdDisc (θ γ i : ℝ) : ℝ := (1 / θ * (i / (1 + i))) ^ (-(1 / γ))

/-- Cochrane (2023), eq. (3.5), p. 620: continuous-time money demand per unit of nominal
income, `M/(Py) = (i/θ)^{−1/γ}`. -/
noncomputable def mdCont (θ γ i : ℝ) : ℝ := (i / θ) ^ (-(1 / γ))

/-- Cochrane (2023), eqs. (19.16), (19.20), (3.4), pp. 443, 620: with power utility and `c = y`,
`u_m/u_c = θ(M/(Py))^{−γ} = i/(1+i)` iff `M/(Py) = ((1/θ) i/(1+i))^{−1/γ}`. -/
theorem md_discrete_iff {θ γ i m : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) (hi : 0 < i) (hm : 0 < m) :
    θ * m ^ (-γ) = i / (1 + i) ↔ m = mdDisc θ γ i := by
  unfold mdDisc
  rw [power_demand_iff hθ hγ.ne' (by positivity) hm, div_eq_mul_inv (i / (1 + i)), one_div,
    mul_comm]
  simp only [one_div]

/-- Cochrane (2023), p. 620, "As inflation and interest rates approach infinity, real money
demand `M_t/P_t` in (3.4) approaches a constant": `mdDisc → θ^{1/γ}` as `i → ∞`. -/
theorem md_discrete_tendsto {θ γ : ℝ} (hθ : 0 < θ) :
    Tendsto (mdDisc θ γ) atTop (𝓝 (θ ^ (1 / γ))) := by
  have h1 : Tendsto (fun i : ℝ => i / (1 + i)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun i : ℝ => (1 + i)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1 tendsto_id)
    have h2 : Tendsto (fun i : ℝ => 1 - (1 + i)⁻¹) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub h0
    rw [sub_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with i hi
    field_simp
    ring
  have h3 : Tendsto (fun i : ℝ => 1 / θ * (i / (1 + i))) atTop (𝓝 (1 / θ * 1)) :=
    h1.const_mul _
  have hc : ContinuousAt (fun x : ℝ => x ^ (-(1 / γ))) (1 / θ * 1) :=
    Real.continuousAt_rpow_const _ _ (Or.inl (by positivity))
  have h4 := hc.tendsto.comp h3
  have h5 : (1 / θ * 1) ^ (-(1 / γ)) = θ ^ (1 / γ) := by
    rw [mul_one, one_div, Real.inv_rpow hθ.le, Real.rpow_neg hθ.le, inv_inv]
  rw [h5] at h4
  exact h4

/-- Cochrane (2023), p. 620, "real money demand in (3.5) smoothly approaches zero":
`mdCont → 0` as `i → ∞`. -/
theorem md_cont_tendsto {θ γ : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) :
    Tendsto (mdCont θ γ) atTop (𝓝 0) := by
  have h1 : Tendsto (fun i : ℝ => i / θ) atTop atTop :=
    tendsto_id.atTop_div_const hθ
  exact (tendsto_rpow_neg_atTop (by positivity : 0 < 1 / γ)).comp h1

/-- Cochrane (2023), p. 620, "For small `i_t`, the difference between `i_t` and `i_t/(1+i_t)` is
minor": the ratio of (3.4) to (3.5) is `(1+i)^{1/γ}`. -/
theorem md_ratio {θ γ i : ℝ} (hθ : 0 < θ) (hi : 0 < i) :
    mdDisc θ γ i / mdCont θ γ i = (1 + i) ^ (1 / γ) := by
  unfold mdDisc mdCont
  have h : 1 / θ * (i / (1 + i)) = i / θ * (1 + i)⁻¹ := by field_simp
  rw [h, Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity),
    Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + i), inv_inv]
  have : 0 < (i / θ) ^ (-(1 / γ)) := Real.rpow_pos_of_pos (by positivity) _
  field_simp

/-- Cochrane (2023), p. 620: the ratio of (3.4) to (3.5) tends to one as `i → 0⁺`. -/
theorem md_ratio_tendsto {θ γ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun i => mdDisc θ γ i / mdCont θ γ i) (𝓝[>] 0) (𝓝 1) := by
  have hc : ContinuousAt (fun i : ℝ => (1 + i) ^ (1 / γ)) 0 :=
    (continuousAt_const.add continuousAt_id).rpow_const (Or.inl (by norm_num))
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simp only [add_zero, Real.one_rpow] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with i hi
  exact (md_ratio hθ hi).symm

/-- Cochrane (2023), p. 620: the modified utility
`u(c, m) = c^{1−γ}/(1−γ) + θ/(1−γ)·(1/(1+i))·m^{1−γ}` (`m = M/P`). -/
noncomputable def modU (θ γ i c m : ℝ) : ℝ :=
  c ^ (1 - γ) / (1 - γ) + θ / (1 - γ) * (1 / (1 + i)) * m ^ (1 - γ)

/-- Cochrane (2023), p. 620: exact derivative of the modified utility in `c`:
`u_c = c^{−γ}` (`γ ≠ 1`, `c > 0`). -/
theorem modU_hasDerivAt_c {θ γ i c m : ℝ} (hγ : γ ≠ 1) (hc : 0 < c) :
    HasDerivAt (fun c => modU θ γ i c m) (c ^ (-γ)) c :=
  (hasDerivAt_power hγ hc).add_const (θ / (1 - γ) * (1 / (1 + i)) * m ^ (1 - γ))

/-- Cochrane (2023), p. 620: exact derivative of the modified utility in `m`:
`u_m = θ/(1+i)·m^{−γ}`. -/
theorem modU_hasDerivAt_m {θ γ i c m : ℝ} (hγ : γ ≠ 1) (hm : 0 < m) :
    HasDerivAt (fun m => modU θ γ i c m) (θ / (1 + i) * m ^ (-γ)) m := by
  have h := ((hasDerivAt_power hγ hm).const_mul (θ * (1 / (1 + i)))).const_add
    (c ^ (1 - γ) / (1 - γ))
  convert h using 1
  · funext z
    unfold modU
    ring
  · ring

/-- Cochrane (2023), eq. (3.5), p. 620, "Now, the first-order condition `u_m/u_c = i/(1+i)`
becomes, in equilibrium `c_t = y_t`, (3.5)": with the modified utility,
`u_m/u_c = i/(1+i)` iff `m = c (i/θ)^{−1/γ}`. -/
theorem modified_foc_iff {θ γ i c m : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) (hi : 0 < i) (hc : 0 < c)
    (hm : 0 < m) : θ / (1 + i) * m ^ (-γ) / c ^ (-γ) = i / (1 + i) ↔ m = c * mdCont θ γ i := by
  have hcpos : 0 < c ^ (-γ) := Real.rpow_pos_of_pos hc _
  have h1 : θ / (1 + i) * m ^ (-γ) / c ^ (-γ) = i / (1 + i) ↔ θ * (m / c) ^ (-γ) = i := by
    rw [Real.div_rpow hm.le hc.le]
    constructor
    · intro h; field_simp at h ⊢; linarith
    · intro h; field_simp at h ⊢; linarith
  rw [h1, power_demand_iff hθ hγ.ne' hi (div_pos hm hc), div_eq_iff hc.ne']
  unfold mdCont
  constructor <;> intro h <;> linarith

/-! ## p. 621: the new difference equation — no finite-time explosion -/

/-- Cochrane (2023), p. 621: the modified map `m ↦ A m/(1 + θm^{−γ})`, `A = (1+µ)/β`. -/
noncomputable def newMap (β μ θ γ m : ℝ) : ℝ := (1 + μ) / β * m / (1 + θ * m ^ (-γ))

/-- Cochrane (2023), p. 621, first display: with the modified utility the first-order
condition `θ(M_t/(P_ty))^{−γ} = (1/β)(P_{t+1}/P_t) − 1` and `M_{t+1} = (1+µ)M_t` give
`m_{t+1} = A m_t/(1 + θm_t^{−γ})`. -/
theorem new_map_of_foc {β μ θ γ y : ℝ} {M P : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hy : 0 < y) (hM : ∀ t, 0 < M t) (hP : ∀ t, 0 < P t)
    (hgrow : ∀ t, M (t + 1) = (1 + μ) * M t) (t : ℕ)
    (hfoc : θ * (M t / (P t * y)) ^ (-γ) = 1 / β * (P (t + 1) / P t) - 1) :
    M (t + 1) / (P (t + 1) * y) = newMap β μ θ γ (M t / (P t * y)) := by
  unfold newMap
  rw [hfoc, hgrow, show 1 + (1 / β * (P (t + 1) / P t) - 1) = P (t + 1) / (β * P t) by
    field_simp; ring]
  have := hM t; have := hP t; have := hP (t + 1)
  field_simp

/-- Cochrane (2023), p. 621: the steady state of the modified model,
`θ(M/(Py))^{−γ} = (1+δ)(1+µ) − 1`. -/
theorem new_fixed_iff {β μ θ γ m : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ) (hm : 0 < m) :
    newMap β μ θ γ m = m ↔ θ * m ^ (-γ) = (1 + μ) / β - 1 := by
  have hD : 0 < 1 + θ * m ^ (-γ) := by have := Real.rpow_pos_of_pos hm (-γ); positivity
  have hA : 0 < (1 + μ) / β := div_pos hμ hβ
  unfold newMap
  rw [div_eq_iff hD.ne']
  constructor
  · intro h
    have : (1 + μ) / β = 1 + θ * m ^ (-γ) :=
      mul_right_cancel₀ hm.ne' (by linarith : (1 + μ) / β * m = (1 + θ * m ^ (-γ)) * m)
    linarith
  · intro h
    rw [show 1 + θ * m ^ (-γ) = (1 + μ) / β by linarith]
    ring

/-- Cochrane (2023), p. 621, display "in place of (19.23)": with `θ x̄^γ = A − 1`, the modified
map in `x = 1/m` is `x_{t+1} = x_t(1 + θx_t^γ)/(1 + θx̄^γ)`. -/
theorem new_x_form {β μ θ γ m xbar : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hm : 0 < m) (hss : θ * xbar ^ γ = (1 + μ) / β - 1) :
    1 / newMap β μ θ γ m = 1 / m * (1 + θ * (1 / m) ^ γ) / (1 + θ * xbar ^ γ) := by
  have hinv : m ^ (-γ) = (1 / m) ^ γ := by
    rw [Real.rpow_neg hm.le, one_div, Real.inv_rpow hm.le]
  unfold newMap
  rw [hinv, hss]
  have : 0 < (1 / m) ^ γ := Real.rpow_pos_of_pos (by positivity) _
  have hμ' : (1 + μ) ≠ 0 := hμ.ne'
  rw [show 1 + ((1 + μ) / β - 1) = (1 + μ) / β by ring]
  field_simp

/-- Cochrane (2023), p. 621, "the price level never goes to infinity in finite time": the
modified map sends `(0, ∞)` into itself, so every `m₀ > 0` starts a path defined for all
dates. -/
theorem new_map_pos {β μ θ γ m : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ) (hm : 0 < m) :
    0 < newMap β μ θ γ m := by
  unfold newMap
  have := Real.rpow_pos_of_pos hm (-γ)
  positivity

/-- Cochrane (2023), p. 621, "a continuum of inflationary equilibria that go on forever": with
`A > 1`, from `0 < m₀ < m̄` real balances fall strictly and tend to zero, never reaching zero. -/
theorem new_inflation_tendsto_zero {β μ θ γ ms m0 : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hss : θ * ms ^ (-γ) = (1 + μ) / β - 1)
    (hm0 : 0 < m0) (hlt : m0 < ms) :
    (∀ t, 0 < (newMap β μ θ γ)^[t] m0) ∧ StrictAnti (fun t => (newMap β μ θ γ)^[t] m0) ∧
      Tendsto (fun t => (newMap β μ θ γ)^[t] m0) atTop (𝓝 0) := by
  set g := newMap β μ θ γ with hg
  set z : ℕ → ℝ := fun t => g^[t] m0 with hz
  have hzs : ∀ t, z (t + 1) = g (z t) := fun t => Function.iterate_succ_apply' _ _ _
  have hpos : ∀ t, 0 < z t := by
    intro t
    induction t with
    | zero => simpa [hz] using hm0
    | succ n ih => rw [hzs]; exact new_map_pos hβ hμ hθ ih
  have hbelow : ∀ x, 0 < x → x < ms → g x < x := by
    intro x hx hxl
    have h1 : ms ^ (-γ) < x ^ (-γ) := Real.rpow_lt_rpow_of_neg hx hxl (by linarith)
    have h2 : (1 + μ) / β < 1 + θ * x ^ (-γ) := by nlinarith [mul_lt_mul_of_pos_left h1 hθ]
    rw [hg]; unfold newMap
    have h3 : 0 < 1 + θ * x ^ (-γ) := by have := Real.rpow_pos_of_pos hx (-γ); positivity
    rw [div_lt_iff₀ h3]
    nlinarith
  have hstep : ∀ t, z t < ms ∧ z (t + 1) < z t := by
    intro t
    induction t with
    | zero =>
      have h0 : z 0 = m0 := rfl
      exact ⟨by rw [h0]; exact hlt, by rw [hzs, h0]; exact hbelow m0 hm0 hlt⟩
    | succ n ih =>
      have h1 : z (n + 1) < ms := lt_trans ih.2 ih.1
      exact ⟨h1, by rw [hzs (n + 1)]; exact hbelow _ (hpos _) h1⟩
  have hanti : StrictAnti z := strictAnti_nat_of_succ_lt fun n => (hstep n).2
  refine ⟨hpos, hanti, ?_⟩
  have hbdd : BddBelow (Set.range z) := ⟨0, by rintro _ ⟨k, rfl⟩; exact (hpos k).le⟩
  have hlim := tendsto_atTop_ciInf hanti.antitone hbdd
  set L := ⨅ k, z k with hL
  have hL0 : 0 ≤ L := le_ciInf fun k => (hpos k).le
  rcases hL0.lt_or_eq with hL0 | hL0
  · exfalso
    have hc : ContinuousAt g L := by
      rw [hg]; unfold newMap
      have hcd : ContinuousAt (fun x : ℝ => 1 + θ * x ^ (-γ)) L :=
        continuousAt_const.add (continuousAt_const.mul
          (Real.continuousAt_rpow_const L (-γ) (Or.inl hL0.ne')))
      have := Real.rpow_pos_of_pos hL0 (-γ)
      exact ((continuousAt_const.mul continuousAt_id).div hcd (by positivity))
    have h1 : Tendsto (fun k => g (z k)) atTop (𝓝 (g L)) := hc.tendsto.comp hlim
    have h2 : Tendsto (fun k => g (z k)) atTop (𝓝 L) := by
      simpa only [← hzs] using (tendsto_add_atTop_iff_nat 1).mpr hlim
    have hfix := tendsto_nhds_unique h1 h2
    have hLlt : L < ms := lt_of_le_of_lt (ciInf_le hbdd 0) (hstep 0).1
    have := hbelow L hL0 hLlt
    linarith
  · rw [hL0]; exact hlim

/-- Cochrane (2023), p. 621: along these inflationary paths inflation
`P_{t+1}/P_t = (1+µ)m_t/m_{t+1} = β(1 + θm_t^{−γ})` rises without bound, but the price level is
finite at every date. -/
theorem new_inflation_rate_tendsto {β μ θ γ ms m0 : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hss : θ * ms ^ (-γ) = (1 + μ) / β - 1)
    (hm0 : 0 < m0) (hlt : m0 < ms) :
    (∀ t, (1 + μ) * ((newMap β μ θ γ)^[t] m0) / ((newMap β μ θ γ)^[t + 1] m0) =
      β * (1 + θ * ((newMap β μ θ γ)^[t] m0) ^ (-γ))) ∧
    Tendsto (fun t => β * (1 + θ * ((newMap β μ θ γ)^[t] m0) ^ (-γ))) atTop atTop := by
  obtain ⟨hpos, -, hlim⟩ := new_inflation_tendsto_zero hβ hμ hθ hγ hss hm0 hlt
  refine ⟨fun t => ?_, ?_⟩
  · rw [Function.iterate_succ_apply']
    have hw := hpos t
    set w := (newMap β μ θ γ)^[t] m0 with hwdef
    unfold newMap
    have := Real.rpow_pos_of_pos hw (-γ)
    field_simp
  · have hpos' : Tendsto (fun t => (newMap β μ θ γ)^[t] m0) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hpos⟩
    have h1 : Tendsto (fun x : ℝ => x ^ (-γ)) (𝓝[>] 0) atTop :=
      tendsto_rpow_neg_nhdsGT_zero (by linarith)
    have h3 := (h1.comp hpos').const_mul_atTop hθ
    have h4 := tendsto_atTop_add_const_left atTop 1 h3
    exact h4.const_mul_atTop hβ

/-- Cochrane (2023), p. 621, "in particular a continuum of inflationary equilibria": every
`m₀ ∈ (0, m̄)` starts a distinct inflationary path with valued money at every date; the set of
such initial values, the interval `(0, m̄)`, is uncountable. -/
theorem new_inflationary_continuum {β μ θ γ ms : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = (1 + μ) / β - 1) :
    (∀ m0 ∈ Set.Ioo 0 ms, ∀ t, 0 < (newMap β μ θ γ)^[t] m0 ∧
      Tendsto (fun t => (newMap β μ θ γ)^[t] m0) atTop (𝓝 0)) ∧
      Set.InjOn (fun m0 => fun t => (newMap β μ θ γ)^[t] m0) (Set.Ioo 0 ms) ∧
      ¬ (Set.Ioo 0 ms).Countable := by
  refine ⟨fun m0 hm t => ⟨(new_inflation_tendsto_zero hβ hμ hθ hγ hss hm.1 hm.2).1 t,
    (new_inflation_tendsto_zero hβ hμ hθ hγ hss hm.1 hm.2).2.2⟩, ?_, ?_⟩
  · intro a _ b _ hab
    have := congrFun hab 0
    simpa using this
  · rw [Cardinal.Real.Ioo_countable_iff]; linarith

end Cochrane.Monetarism.PruningInflation
