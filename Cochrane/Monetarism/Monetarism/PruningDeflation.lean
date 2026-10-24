/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.MoneyTargetingDynamics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Field

/-!
# Pruning deflationary equilibria

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix, Chapter 3
"Pruning multiple monetary equilibria", §3.1 (pp. 612–618), with the money-in-utility model of
§19.3 (eqs. (19.10), (19.12), (19.18)–(19.23), pp. 439–445). Perfect foresight throughout,
as in the book ("so that initial inflation is the only indeterminacy").

Real balances relative to output are `m_t = M_t/(P_t y)`; the power utility (19.20) gives
`u_m/u_c = θ m^{−γ}`. The (19.23) map in `x = 1/m` is the canonical `MoneyInUtility.nextX`;
`Links` proves that the paths, steady states, deflations and explosions here are those of
`MoneyInUtility` and `MoneyTargetingDynamics` read in `m = 1/x`.

## Main results

* `foc_power_iff`, `ratio_of_foc` (19.18)/(19.21) and the p. 612 display:
  `m_{t+1}/m_t = (1+δ)(1+µ)(1 − θ x_t^γ)` with `x = 1/m = P y/M`; `eq1923_iff` is (19.23)
  (the map is conjugate by `m ↦ 1/m` to the canonical `MoneyInUtility.nextX`);
  `ratio_strictAntiOn`, `ratio_tendsto` give "↗ (1+δ)(1+µ) as `x ↘ 0`".
* Steady state: `steady_exists_unique`.
* Deflationary paths (`m₀ > m̄`): `deflation_growth`, `deflation_tendsto_atTop`,
  `deflation_path_exists`.
* The transversality condition, survey error **E17**: along a deflationary path
  `β^{T+1}M_T/(P_{T+1}y)` tends to zero iff `µ < 0` (`tvc_tendsto_zero_iff`); at `µ = 0` it
  converges to a positive constant (`tvc_mu_zero`), for `µ > 0` it diverges (`tvc_mu_pos`).
  The book's text says the objection "only applies to … µ > 0" and that for "µ ≤ 0"
  deflationary equilibria survive: false at `µ = 0`. For `β < 1 + µ < 1` deflationary
  equilibria form a continuum (`deflation_continuum`); for `1 + µ ≤ β` there are none
  (`no_deflation_of_le_beta`), so "−δ < µ < 0" must be `−δ/(1+δ) < µ < 0`
  (`survival_threshold`).
* §3.1.1 (no debt, satiation): `deflation_at_satiation`, (3.1) `flow_nodebt_iff`, the
  telescoped present-value identities `pv_finite`, `pv_finite_telescoped`,
  `final_money_eq`, the growing terminal term `tvc_term_growth`, `pv_surplus_tendsto_bot`,
  `no_eqm_positive_growth`, `passive_requires_negative_growth`, `tvc_iff_money_vanishes`,
  `tvc_limit`, `tvc_iff_pv`, and the determinate price level
  `price_level_determined`, `no_price_level_of_nonpos_pv`.
* §3.1.2 (open-market operations): `omo_total_debt`, `omo_real_debt_const`, `omo_bonds`,
  `omo_bonds_eventually_neg`, `omo_explode`, `omo_tvc`,
  `omo_pv`.
* §3.1.3 (valued money): the last-period first-order condition `last_period_foc`, its
  sufficiency `last_period_foc_sufficient`, the power case `last_period_power_demand`; the
  separable comparative static `separable_money_demand_rises`; the iterated budget constraint
  with interest `iterated_budget`.
-/

namespace Cochrane.Monetarism.PruningDeflation

open Filter Topology

/-! ## Primitives: power money-in-utility (19.20) and the difference equation (19.21) -/

/-- Cochrane (2023), eq. (19.20), p. 443: the marginal utility of money `θ m^{−γ}`. -/
noncomputable def umPow (θ γ m : ℝ) : ℝ := θ * m ^ (-γ)

/-- Cochrane (2023), eq. (19.20), p. 443: the marginal utility of consumption `c^{−γ}`. -/
noncomputable def ucPow (γ c : ℝ) : ℝ := c ^ (-γ)

/-- Cochrane (2023), eqs. (19.18)–(19.21), p. 444: with power utility,
`u_m(M/P)/u_c(y) = θ (M/(P y))^{−γ}`. -/
theorem um_div_uc_pow {θ γ M P y : ℝ} (hM : 0 < M) (hP : 0 < P) (hy : 0 < y) :
    umPow θ γ (M / P) / ucPow γ y = θ * (M / (P * y)) ^ (-γ) := by
  unfold umPow ucPow
  have h1 : M / (P * y) = (M / P) / y := by field_simp
  rw [h1, Real.div_rpow (by positivity) hy.le]
  ring

/-- Cochrane (2023), eq. (19.18), p. 442, with power utility (19.21), p. 444: the
money-demand condition `u_m/u_c = 1 − β P_t/P_{t+1}` in the power case. -/
theorem foc_power_iff {β θ γ M P P' y : ℝ} (hM : 0 < M) (hP : 0 < P) (hy : 0 < y) :
    umPow θ γ (M / P) / ucPow γ y = 1 - β * P / P' ↔
      θ * (M / (P * y)) ^ (-γ) = 1 - β * P / P' := by
  rw [um_div_uc_pow hM hP hy]

/-- Cochrane (2023), Online Appendix p. 612: the gross growth of real balances
`(1+µ)/β · (1 − θ m^{−γ})`, i.e. `(1+δ)(1+µ)(1 − θ x^γ)` with `x = 1/m`. -/
noncomputable def ratioMap (β μ θ γ m : ℝ) : ℝ := (1 + μ) / β * (1 - θ * m ^ (-γ)) * m

/-- Cochrane (2023), Online Appendix p. 612, display: from (19.21) with `M_{t+1} = (1+µ)M_t`,
`m_{t+1} = (1+µ)/β · (1 − θ m_t^{−γ}) m_t`, where `m_t = M_t/(P_t y)`. -/
theorem ratio_of_foc {β μ θ γ y : ℝ} {M P : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hy : 0 < y)
    (hM : ∀ t, 0 < M t) (hP : ∀ t, 0 < P t) (hgrow : ∀ t, M (t + 1) = (1 + μ) * M t) (t : ℕ)
    (hfoc : θ * (M t / (P t * y)) ^ (-γ) = 1 - β * P t / P (t + 1)) :
    M (t + 1) / (P (t + 1) * y) = ratioMap β μ θ γ (M t / (P t * y)) := by
  unfold ratioMap
  rw [hfoc, hgrow]
  have := hM t; have := hP t; have := hP (t + 1)
  field_simp
  ring

/-- Cochrane (2023), Online Appendix p. 612: `(1+µ)/β = (1+δ)(1+µ)` when `β = 1/(1+δ)`. -/
theorem growth_factor_eq {β δ μ : ℝ} (hδ : 0 < 1 + δ) (hβ : β = 1 / (1 + δ)) :
    (1 + μ) / β = (1 + δ) * (1 + μ) := by
  rw [hβ]; field_simp

/-- Cochrane (2023), Online Appendix p. 612, "as `P_t y/M_t ↘ 0`, `(M_{t+1}/P_{t+1}y)/(M_t/P_t y)`
`↗ (1+δ)(1+µ)`": the gross growth `(1+µ)/β · (1 − θ x^γ)` is strictly decreasing in `x > 0`. -/
theorem ratio_strictAntiOn {β μ θ γ : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) :
    StrictAntiOn (fun x : ℝ => (1 + μ) / β * (1 - θ * x ^ γ)) (Set.Ioi 0) := by
  intro a ha b _ hab
  have h1 : a ^ γ < b ^ γ := Real.rpow_lt_rpow (le_of_lt ha) hab hγ
  have h2 : 0 < (1 + μ) / β := div_pos hμ hβ
  simp only
  nlinarith [mul_lt_mul_of_pos_left h1 hθ]

/-- Cochrane (2023), Online Appendix p. 612: the limit `(1+µ)/β · (1 − θ x^γ) → (1+µ)/β` as
`x → 0⁺`. -/
theorem ratio_tendsto {β μ θ γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun x : ℝ => (1 + μ) / β * (1 - θ * x ^ γ)) (𝓝[>] 0) (𝓝 ((1 + μ) / β)) := by
  have hc : ContinuousAt (fun x : ℝ => (1 + μ) / β * (1 - θ * x ^ γ)) 0 :=
    continuousAt_const.mul (continuousAt_const.sub
      (continuousAt_const.mul (Real.continuousAt_rpow_const 0 γ (Or.inr hγ.le))))
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simpa [Real.zero_rpow hγ.ne'] using h

/-- Cochrane (2023), eq. (19.23), p. 444 (and (3.3), p. 619): in `x = P y/M = 1/m` the
difference equation reads `x_{t+1} = x_t (1 − θ x̄^γ)/(1 − θ x_t^γ)` with
`θ x̄^γ = 1 − β/(1+µ)` (19.22), i.e. the real-balance map is conjugate by `m ↦ 1/m` to the
canonical (19.23) map `MoneyInUtility.nextX`. -/
theorem eq1923_iff {β μ θ γ m m' xbar : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hm : 0 < m)
    (hden : θ * (1 / m) ^ γ ≠ 1) (hss : θ * xbar ^ γ = 1 - β / (1 + μ)) :
    m' = ratioMap β μ θ γ m ↔ 1 / m' = MoneyInUtility.nextX θ γ xbar (1 / m) := by
  unfold MoneyInUtility.nextX
  have hinv : m ^ (-γ) = (1 / m) ^ γ := by
    rw [Real.rpow_neg hm.le, one_div, Real.inv_rpow hm.le]
  unfold ratioMap
  rw [hinv, hss]
  have hd : 1 - θ * (1 / m) ^ γ ≠ 0 := sub_ne_zero.mpr (Ne.symm hden)
  constructor
  · intro h
    rw [h]
    field_simp
    ring
  · intro h
    have hm' : m' ≠ 0 := by
      intro h0
      rw [h0, div_zero] at h
      have : 1 / m * (1 - (1 - β / (1 + μ))) / (1 - θ * (1 / m) ^ γ) ≠ 0 := by
        have : (1 - (1 - β / (1 + μ))) = β / (1 + μ) := by ring
        rw [this]
        exact div_ne_zero (mul_ne_zero (by positivity) (by positivity)) hd
      exact this h.symm
    field_simp at h
    field_simp
    linarith

/-! ## Steady states -/

/-- Cochrane (2023), eq. (19.19)/(19.22), p. 444: for `m > 0`, `m` is a fixed point of the
real-balance map iff `θ m^{−γ} = 1 − β/(1+µ)`. -/
theorem fixed_iff {β μ θ γ m : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hm : 0 < m) :
    ratioMap β μ θ γ m = m ↔ θ * m ^ (-γ) = 1 - β / (1 + μ) := by
  unfold ratioMap
  constructor
  · intro h
    have h1 : (1 + μ) / β * (1 - θ * m ^ (-γ)) = 1 := by
      have := mul_right_cancel₀ hm.ne' (h.trans (one_mul m).symm)
      exact this
    field_simp at h1
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- Cochrane (2023), eq. (19.22), p. 444: when `β < 1 + µ` there is exactly one positive
inflationary steady state `m̄ = (θ/(1 − β/(1+µ)))^{1/γ}`. -/
theorem steady_exists_unique {β μ θ γ : ℝ} (hβ : 0 < β) (hμβ : β < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) : ∃! ms : ℝ, 0 < ms ∧ θ * ms ^ (-γ) = 1 - β / (1 + μ) := by
  have hμ : 0 < 1 + μ := by linarith
  have hk : 0 < 1 - β / (1 + μ) := by
    rw [sub_pos, div_lt_one hμ]; exact hμβ
  refine ⟨(θ / (1 - β / (1 + μ))) ^ (1 / γ), ⟨by positivity, ?_⟩, ?_⟩
  · rw [← Real.rpow_mul (by positivity), show 1 / γ * -γ = -1 by field_simp,
      Real.rpow_neg_one]
    field_simp
  · rintro y ⟨hy, hyss⟩
    have h1 : y ^ (-γ) = (1 - β / (1 + μ)) / θ := by
      rw [eq_div_iff hθ.ne']; linarith
    have h2 : y = ((1 - β / (1 + μ)) / θ) ^ (-γ)⁻¹ := by
      rw [← h1, Real.rpow_rpow_inv hy.le (by linarith)]
    rw [h2, show (-γ)⁻¹ = -(1 / γ) by field_simp, Real.rpow_neg (by positivity),
      ← Real.inv_rpow (by positivity), inv_div]

/-! ## Paths of real balances -/

/-- Cochrane (2023), Online Appendix p. 612: a perfect-foresight path of real balances
`m_t = M_t/(P_t y) > 0` obeying (19.21) with constant money growth. -/
def IsMPath (β μ θ γ : ℝ) (m : ℕ → ℝ) : Prop :=
  ∀ t, 0 < m t ∧ m (t + 1) = ratioMap β μ θ γ (m t)

/-- Cochrane (2023), Online Appendix p. 612: along a deflationary path (`m₀ > m̄`) real balances
grow at least geometrically, `m_t ≥ rᵗ m₀` with `r = (1+µ)/β (1 − θ m₀^{−γ}) > 1`. -/
theorem deflation_growth {β μ θ γ ms : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ))
    (hpath : IsMPath β μ θ γ m) (h0 : ms < m 0) :
    1 < (1 + μ) / β * (1 - θ * m 0 ^ (-γ)) ∧
      ∀ t, m 0 ≤ m t ∧ ((1 + μ) / β * (1 - θ * m 0 ^ (-γ))) ^ t * m 0 ≤ m t := by
  set r := (1 + μ) / β * (1 - θ * m 0 ^ (-γ)) with hr
  have hA : 0 < (1 + μ) / β := div_pos hμ hβ
  have hlt : m 0 ^ (-γ) < ms ^ (-γ) := Real.rpow_lt_rpow_of_neg hms h0 (by linarith)
  have hr1 : 1 < r := by
    have h1 : 1 - θ * ms ^ (-γ) < 1 - θ * m 0 ^ (-γ) := by nlinarith
    have h2 : (1 + μ) / β * (1 - θ * ms ^ (-γ)) = 1 := by rw [hss]; field_simp; ring
    rw [hr]; nlinarith
  refine ⟨hr1, ?_⟩
  intro t
  induction t with
  | zero => simp
  | succ n ih =>
    have hm0 : 0 < m 0 := lt_trans hms h0
    have hmn : 0 < m n := (hpath n).1
    have hle : m n ^ (-γ) ≤ m 0 ^ (-γ) := Real.rpow_le_rpow_of_nonpos hm0 ih.1 (by linarith)
    have hstep : r * m n ≤ m (n + 1) := by
      rw [(hpath n).2]; unfold ratioMap
      have : (1 + μ) / β * (1 - θ * m 0 ^ (-γ)) ≤ (1 + μ) / β * (1 - θ * m n ^ (-γ)) := by
        apply mul_le_mul_of_nonneg_left _ hA.le; nlinarith
      rw [hr]; nlinarith
    constructor
    · nlinarith
    · rw [pow_succ]; nlinarith [pow_pos (lt_trans zero_lt_one hr1) n]

/-- Cochrane (2023), §19.3.2, p. 444, and Online Appendix p. 612: along a deflationary path
real balances grow without bound (`P_t y/M_t ↘ 0`). -/
theorem deflation_tendsto_atTop {β μ θ γ ms : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ))
    (hpath : IsMPath β μ θ γ m) (h0 : ms < m 0) : Tendsto m atTop atTop := by
  obtain ⟨hr1, hg⟩ := deflation_growth hβ hμ hθ hγ hms hss hpath h0
  have hm0 : 0 < m 0 := lt_trans hms h0
  exact tendsto_atTop_mono (fun t => (hg t).2)
    ((tendsto_pow_atTop_atTop_of_one_lt hr1).atTop_mul_const hm0)

/-- Cochrane (2023), §19.3.2, Figure 19.1, p. 444: every initial `m₀ > m̄` starts a unique
perfect-foresight path, and it is deflationary (`m_t → ∞`). -/
theorem deflation_path_exists {β μ θ γ ms m0 : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) (h0 : ms < m0) :
    ∃! m : ℕ → ℝ, IsMPath β μ θ γ m ∧ m 0 = m0 ∧ Tendsto m atTop atTop := by
  set m : ℕ → ℝ := fun t => (ratioMap β μ θ γ)^[t] m0 with hmdef
  have hsucc : ∀ t, m (t + 1) = ratioMap β μ θ γ (m t) := fun t =>
    Function.iterate_succ_apply' _ _ _
  have hA : 0 < (1 + μ) / β := div_pos hμ hβ
  have habove : ∀ t, ms < m t := by
    intro t
    induction t with
    | zero => simpa [hmdef] using h0
    | succ n ih =>
      rw [hsucc]
      have hlt : m n ^ (-γ) < ms ^ (-γ) := Real.rpow_lt_rpow_of_neg hms ih (by linarith)
      have h2 : (1 + μ) / β * (1 - θ * ms ^ (-γ)) = 1 := by rw [hss]; field_simp; ring
      unfold ratioMap
      have h4 := mul_lt_mul_of_pos_left hlt hθ
      have h3 : 1 < (1 + μ) / β * (1 - θ * m n ^ (-γ)) := by nlinarith
      nlinarith
  have hpath : IsMPath β μ θ γ m := fun t => ⟨lt_trans hms (habove t), hsucc t⟩
  refine ⟨m, ⟨hpath, rfl, deflation_tendsto_atTop hβ hμ hθ hγ hms hss hpath h0⟩, ?_⟩
  rintro m' ⟨hp', h0', -⟩
  funext t
  induction t with
  | zero => rw [h0']; rfl
  | succ n ih => rw [(hp' n).2, hsucc, ih]

/-! ## The transversality condition along deflations (E17) -/

/-- Cochrane (2023), Online Appendix p. 613: the transversality term
`β^{T+1} M_T/(P_{T+1} y) = β^{T+1} m_{T+1}/(1+µ)` (with `M_{T+1} = (1+µ)M_T`). -/
noncomputable def tvcTerm (β μ : ℝ) (m : ℕ → ℝ) (T : ℕ) : ℝ := β ^ (T + 1) * m (T + 1) / (1 + μ)

/-- Cochrane (2023), Online Appendix p. 613: the transversality term in levels,
`β^{T+1}M_T/(P_{T+1}y) = tvcTerm`, when `M_{T+1} = (1+µ)M_T`. -/
theorem tvcTerm_eq {β μ y : ℝ} {M P : ℕ → ℝ} (hμ : 0 < 1 + μ) (hy : 0 < y)
    (hP : ∀ t, 0 < P t) (hgrow : ∀ t, M (t + 1) = (1 + μ) * M t) (T : ℕ) :
    β ^ (T + 1) * M T / (P (T + 1) * y) =
      tvcTerm β μ (fun t => M t / (P t * y)) T := by
  unfold tvcTerm
  dsimp only
  rw [hgrow]
  have := hP (T + 1)
  field_simp

/-- A general lemma (not in the book): `exp(−a/(1−a₀)) ≤ 1 − a` for `0 ≤ a ≤ a₀ < 1`. -/
theorem exp_le_one_sub {a a0 : ℝ} (ha : 0 ≤ a) (haa : a ≤ a0) (ha0 : a0 < 1) :
    Real.exp (-(a / (1 - a0))) ≤ 1 - a := by
  have h1 : 0 < 1 - a := by linarith
  have h2 : Real.exp (-(a / (1 - a0))) ≤ Real.exp (-(a / (1 - a))) := by
    apply Real.exp_le_exp.mpr
    have : a / (1 - a) ≤ a / (1 - a0) :=
      div_le_div_of_nonneg_left ha (by linarith) (by linarith)
    linarith
  have h3 : 1 / (1 - a) ≤ Real.exp (a / (1 - a)) := by
    have := Real.add_one_le_exp (a / (1 - a))
    have h4 : a / (1 - a) + 1 = 1 / (1 - a) := by field_simp; ring
    linarith
  have h5 : Real.exp (-(a / (1 - a))) ≤ 1 - a := by
    rw [Real.exp_neg]
    rw [inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    have := mul_le_mul_of_nonneg_left h3 h1.le
    rw [mul_one_div_cancel h1.ne'] at this
    linarith
  linarith

/-- Cochrane (2023), Online Appendix p. 613: the scaled real balances `W_T = β^T m_T` obey
`W_{T+1} = (1+µ)(1 − θ m_T^{−γ}) W_T` along any path. -/
theorem scaled_succ {β μ θ γ : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hpath : IsMPath β μ θ γ m)
    (T : ℕ) : β ^ (T + 1) * m (T + 1) = (1 + μ) * (1 - θ * m T ^ (-γ)) * (β ^ T * m T) := by
  rw [(hpath T).2]; unfold ratioMap; rw [pow_succ]; field_simp

/-- Cochrane (2023), Online Appendix p. 613, "If money growth is negative … this subtlety
vanishes": for `−1 < µ < 0` the transversality term tends to zero along every path. -/
theorem tvc_tendsto_zero_of_neg {β μ θ γ : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hμ0 : μ < 0) (hθ : 0 < θ) (hpath : IsMPath β μ θ γ m) :
    Tendsto (tvcTerm β μ m) atTop (𝓝 0) := by
  have hW : ∀ T, 0 < β ^ T * m T ∧ β ^ T * m T ≤ (1 + μ) ^ T * m 0 := by
    intro T
    induction T with
    | zero => simp [(hpath 0).1]
    | succ n ih =>
      have hpos : 0 < β ^ (n + 1) * m (n + 1) := by have := (hpath (n + 1)).1; positivity
      refine ⟨hpos, ?_⟩
      rw [scaled_succ hβ hpath n]
      rw [scaled_succ hβ hpath n] at hpos
      have hfac : 0 < 1 - θ * m n ^ (-γ) := by
        by_contra hcon
        push Not at hcon
        have : (1 + μ) * (1 - θ * m n ^ (-γ)) * (β ^ n * m n) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hμ.le hcon) ih.1.le
        linarith
      have hle : 1 - θ * m n ^ (-γ) ≤ 1 := by
        have := Real.rpow_pos_of_pos (hpath n).1 (-γ); nlinarith
      rw [pow_succ]
      have h1 : (1 + μ) * (1 - θ * m n ^ (-γ)) * (β ^ n * m n) ≤ (1 + μ) * (β ^ n * m n) := by
        have := mul_le_mul_of_nonneg_right hle ih.1.le
        nlinarith
      nlinarith [ih.2]
  have hlim : Tendsto (fun T => (1 + μ) ^ (T + 1) * m 0 / (1 + μ)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hμ.le (by linarith)).comp
      (tendsto_add_atTop_nat 1)).mul_const (m 0)
    simpa using this.div_const (1 + μ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun T => ?_)
    (fun T => ?_)
  · unfold tvcTerm; exact div_nonneg (hW (T + 1)).1.le hμ.le
  · unfold tvcTerm; exact div_le_div_of_nonneg_right (hW (T + 1)).2 hμ.le

/-- Cochrane (2023), Online Appendix p. 613: along a deflationary path (`m₀ > m̄`) the scaled
balances satisfy `β^T m_T ≥ C (1+µ)^T` for a constant `C > 0` (the product
`∏(1 − θ m_s^{−γ})` stays bounded away from zero because `θ m_s^{−γ}` decays geometrically). -/
theorem scaled_lower_bound {β μ θ γ ms : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ))
    (hpath : IsMPath β μ θ γ m) (h0 : ms < m 0) :
    ∃ C, 0 < C ∧ ∀ T, C * (1 + μ) ^ T ≤ β ^ T * m T := by
  obtain ⟨hr1, hg⟩ := deflation_growth hβ hμ hθ hγ hms hss hpath h0
  set r := (1 + μ) / β * (1 - θ * m 0 ^ (-γ)) with hr
  have hm0 : 0 < m 0 := lt_trans hms h0
  set a0 := θ * m 0 ^ (-γ) with ha0
  set ρ := r ^ (-γ) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (by linarith) _
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hr1 (by linarith)
  have ha0pos : 0 < a0 := by positivity
  have hA : 0 < (1 + μ) / β := div_pos hμ hβ
  have ha01 : a0 < 1 := by
    have : 1 < (1 + μ) / β * (1 - a0) := hr1
    have : 0 < 1 - a0 := by
      by_contra h; push Not at h; nlinarith
    linarith
  -- geometric decay of `a_t = θ m_t^{−γ}`
  have hdecay : ∀ t, θ * m t ^ (-γ) ≤ a0 * ρ ^ t := by
    intro t
    have h1 : m t ^ (-γ) ≤ (r ^ t * m 0) ^ (-γ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (hg t).2 (by linarith)
    have h2 : (r ^ t * m 0) ^ (-γ) = ρ ^ t * m 0 ^ (-γ) := by
      rw [Real.mul_rpow (by positivity) hm0.le, ← Real.rpow_natCast_mul (by linarith),
        mul_comm (t : ℝ), Real.rpow_mul_natCast (by linarith)]
    rw [h2] at h1
    rw [ha0]
    nlinarith
  have hat : ∀ t, 0 ≤ θ * m t ^ (-γ) ∧ θ * m t ^ (-γ) ≤ a0 := by
    intro t
    refine ⟨by have := Real.rpow_pos_of_pos (hpath t).1 (-γ); positivity, ?_⟩
    have := hdecay t
    have : ρ ^ t ≤ 1 := pow_le_one₀ hρ0.le hρ1.le
    nlinarith
  set η := 1 - a0 with hη
  have hηpos : 0 < η := by linarith
  -- induction on the product bound
  have hind : ∀ T, m 0 * (1 + μ) ^ T *
      Real.exp (-((∑ s ∈ Finset.range T, θ * m s ^ (-γ)) / η)) ≤ β ^ T * m T := by
    intro T
    induction T with
    | zero => simp
    | succ n ih =>
      rw [scaled_succ hβ hpath n, Finset.sum_range_succ, add_div, neg_add, Real.exp_add,
        pow_succ]
      have he := exp_le_one_sub (hat n).1 (hat n).2 ha01
      have hpos : 0 ≤ m 0 * (1 + μ) ^ n *
          Real.exp (-((∑ s ∈ Finset.range n, θ * m s ^ (-γ)) / η)) := by positivity
      calc m 0 * ((1 + μ) ^ n * (1 + μ)) *
            (Real.exp (-((∑ s ∈ Finset.range n, θ * m s ^ (-γ)) / η)) *
              Real.exp (-(θ * m n ^ (-γ) / η)))
          = (1 + μ) * Real.exp (-(θ * m n ^ (-γ) / η)) * (m 0 * (1 + μ) ^ n *
              Real.exp (-((∑ s ∈ Finset.range n, θ * m s ^ (-γ)) / η))) := by ring
        _ ≤ (1 + μ) * (1 - θ * m n ^ (-γ)) * (β ^ n * m n) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left he hμ.le) ih hpos
          have : 0 ≤ 1 - θ * m n ^ (-γ) := by linarith [(hat n).2]
          positivity
  -- the sum is bounded
  have hsum : ∀ T, ∑ s ∈ Finset.range T, θ * m s ^ (-γ) ≤ a0 / (1 - ρ) := by
    intro T
    calc ∑ s ∈ Finset.range T, θ * m s ^ (-γ) ≤ ∑ s ∈ Finset.range T, a0 * ρ ^ s :=
          Finset.sum_le_sum fun s _ => hdecay s
      _ = a0 * ((1 - ρ ^ T) / (1 - ρ)) := by
          rw [← Finset.mul_sum, geom_sum_eq hρ1.ne, ← neg_div_neg_eq, neg_sub, neg_sub]
      _ ≤ a0 / (1 - ρ) := by
          rw [mul_div_assoc']
          apply div_le_div_of_nonneg_right _ (by linarith)
          have : 0 ≤ ρ ^ T := by positivity
          nlinarith
  refine ⟨m 0 * Real.exp (-(a0 / (1 - ρ) / η)), by positivity, fun T => ?_⟩
  have hexp : Real.exp (-(a0 / (1 - ρ) / η)) ≤
      Real.exp (-((∑ s ∈ Finset.range T, θ * m s ^ (-γ)) / η)) := by
    apply Real.exp_le_exp.mpr
    have := div_le_div_of_nonneg_right (hsum T) hηpos.le
    linarith
  calc m 0 * Real.exp (-(a0 / (1 - ρ) / η)) * (1 + μ) ^ T
      = m 0 * (1 + μ) ^ T * Real.exp (-(a0 / (1 - ρ) / η)) := by ring
    _ ≤ m 0 * (1 + μ) ^ T * Real.exp (-((∑ s ∈ Finset.range T, θ * m s ^ (-γ)) / η)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ β ^ T * m T := hind T

/-- Cochrane (2023), Online Appendix p. 613, "if µ ≥ 0, real money holdings violate the
condition `lim β^{T+1}M_{t+T}/(P_{t+T+1}y) ≠ 0`" (survey E17: `µ = 0` included). -/
theorem tvc_not_tendsto_zero {β μ θ γ ms : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ0 : 0 ≤ μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ))
    (hpath : IsMPath β μ θ γ m) (h0 : ms < m 0) :
    ¬ Tendsto (tvcTerm β μ m) atTop (𝓝 0) := by
  have hμ : 0 < 1 + μ := by linarith
  obtain ⟨C, hC, hlow⟩ := scaled_lower_bound hβ hμ hθ hγ hms hss hpath h0
  intro h
  have hev : ∀ T, C / (1 + μ) ≤ tvcTerm β μ m T := by
    intro T
    unfold tvcTerm
    apply div_le_div_of_nonneg_right _ hμ.le
    have := hlow (T + 1)
    have : 1 ≤ (1 + μ) ^ (T + 1) := one_le_pow₀ (by linarith)
    nlinarith
  have := ge_of_tendsto' h hev
  have : 0 < C / (1 + μ) := div_pos hC hμ
  linarith

/-- Cochrane (2023), Online Appendix pp. 612–613, survey error **E17** (corrected): along
a deflationary path (`m₀ > m̄`) with `β < 1 + µ`, the transversality term tends to zero if
and only if `µ < 0`. -/
theorem tvc_tendsto_zero_iff {β μ θ γ ms : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμβ : β < 1 + μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ))
    (hpath : IsMPath β μ θ γ m) (h0 : ms < m 0) :
    Tendsto (tvcTerm β μ m) atTop (𝓝 0) ↔ μ < 0 := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    exact tvc_not_tendsto_zero hβ hcon hθ hγ hms hss hpath h0 h
  · intro h
    exact tvc_tendsto_zero_of_neg hβ (by linarith) h hθ hpath

/-- Cochrane (2023), Online Appendix p. 613 (survey E17): at `µ = 0` the transversality term
converges to a strictly positive constant along every deflationary path, so the condition is
violated although money does not grow. -/
theorem tvc_mu_zero {β θ γ ms : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hθ : 0 < θ)
    (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + 0))
    (hpath : IsMPath β 0 θ γ m) (h0 : ms < m 0) :
    ∃ L, 0 < L ∧ Tendsto (tvcTerm β 0 m) atTop (𝓝 L) := by
  obtain ⟨C, hC, hlow⟩ := scaled_lower_bound hβ (by norm_num) hθ hγ hms hss hpath h0
  have hanti : Antitone (fun T => β ^ T * m T) := by
    refine antitone_nat_of_succ_le fun n => ?_
    rw [scaled_succ hβ hpath n]
    have hp := Real.rpow_pos_of_pos (hpath n).1 (-γ)
    have : 0 < β ^ n * m n := by have := (hpath n).1; positivity
    have h := mul_pos (mul_pos hθ hp) this
    nlinarith
  have hbdd : BddBelow (Set.range fun T => β ^ T * m T) :=
    ⟨C, by rintro _ ⟨T, rfl⟩; simpa using hlow T⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  refine ⟨⨅ T, β ^ T * m T, ?_, ?_⟩
  · exact lt_of_lt_of_le hC (le_ciInf fun T => by simpa using hlow T)
  · have := hlim.comp (tendsto_add_atTop_nat 1)
    unfold tvcTerm
    simpa [Function.comp_def] using this

/-- Cochrane (2023), Online Appendix p. 613: for `µ > 0` the transversality term diverges to
`+∞` along every deflationary path ("real money holdings rise faster than the real rate"). -/
theorem tvc_mu_pos {β μ θ γ ms : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ0 : 0 < μ) (hθ : 0 < θ)
    (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ))
    (hpath : IsMPath β μ θ γ m) (h0 : ms < m 0) :
    Tendsto (tvcTerm β μ m) atTop atTop := by
  have hμ : 0 < 1 + μ := by linarith
  obtain ⟨C, hC, hlow⟩ := scaled_lower_bound hβ hμ hθ hγ hms hss hpath h0
  have h1 : Tendsto (fun T => C * (1 + μ) ^ (T + 1) / (1 + μ)) atTop atTop :=
    (((tendsto_pow_atTop_atTop_of_one_lt (by linarith : (1 : ℝ) < 1 + μ)).comp
      (tendsto_add_atTop_nat 1)).const_mul_atTop hC).atTop_div_const hμ
  exact tendsto_atTop_mono (fun T => div_le_div_of_nonneg_right (hlow (T + 1)) hμ.le) h1

/-- Cochrane (2023), Online Appendix p. 613, "If money growth is negative … we unequivocally
have multiple deflationary equilibria" (corrected range `β < 1 + µ < 1`): every `m₀ > m̄`
starts a deflationary path satisfying the transversality condition, and distinct `m₀` give
distinct paths — a continuum of equilibria. -/
theorem deflation_continuum {β μ θ γ ms : ℝ} (hβ : 0 < β) (hμβ : β < 1 + μ) (hμ1 : μ < 0)
    (hθ : 0 < θ) (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) :
    ∃ path : ℝ → ℕ → ℝ, (∀ m0, ms < m0 → IsMPath β μ θ γ (path m0) ∧ path m0 0 = m0 ∧
      Tendsto (path m0) atTop atTop ∧ Tendsto (tvcTerm β μ (path m0)) atTop (𝓝 0)) ∧
      Set.InjOn path (Set.Ioi ms) := by
  have hμ : 0 < 1 + μ := by linarith
  have hex : ∀ m0 : ℝ, ∃ m : ℕ → ℝ, ms < m0 →
      IsMPath β μ θ γ m ∧ m 0 = m0 ∧ Tendsto m atTop atTop := by
    intro m0
    by_cases h : ms < m0
    · obtain ⟨m, hm, -⟩ := deflation_path_exists hβ hμ hθ hγ hms hss h
      exact ⟨m, fun _ => hm⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' h⟩
  choose path hpath using hex
  refine ⟨path, fun m0 h => ⟨(hpath m0 h).1, (hpath m0 h).2.1, (hpath m0 h).2.2,
    tvc_tendsto_zero_of_neg hβ hμ hμ1 hθ (hpath m0 h).1⟩, ?_⟩
  intro a ha b hb hab
  have h1 := (hpath a ha).2.1
  have h2 := (hpath b hb).2.1
  rw [← h1, ← h2, hab]

/-- Cochrane (2023), Online Appendix p. 613 and p. 617, "−δ < µ < 0" / "−δ ≤ µ < 0"
(corrected): when `1 + µ ≤ β` every path of real balances is strictly decreasing, so there is
no deflationary path at all. -/
theorem no_deflation_of_le_beta {β μ θ γ : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hμβ : 1 + μ ≤ β) (hθ : 0 < θ) (hpath : IsMPath β μ θ γ m) : StrictAnti m := by
  refine strictAnti_nat_of_succ_lt fun n => ?_
  rw [(hpath n).2]
  unfold ratioMap
  have hp := Real.rpow_pos_of_pos (hpath n).1 (-γ)
  have hA : (1 + μ) / β ≤ 1 := (div_le_one hβ).mpr hμβ
  have hA0 : 0 < (1 + μ) / β := div_pos hμ hβ
  have hmn := (hpath n).1
  have hθp := mul_pos hθ hp
  have : (1 + μ) / β * (1 - θ * m n ^ (-γ)) < 1 := by nlinarith [mul_pos hA0 hθp]
  nlinarith

/-- Cochrane (2023), Online Appendix p. 613 (survey E17/E13): with `β = 1/(1+δ)`, the condition
for deflationary paths `β < 1 + µ` is `µ > −δ/(1+δ)`, not `µ > −δ`; e.g. `δ = 1`, `µ = −0.6`
satisfies `µ > −δ` but `1 + µ = 0.4 < β = 0.5`. -/
theorem survival_threshold {δ μ : ℝ} (hδ : 0 < 1 + δ) :
    1 / (1 + δ) < 1 + μ ↔ -δ / (1 + δ) < μ := by
  constructor
  · intro h
    rw [div_lt_iff₀ hδ]
    rw [div_lt_iff₀ hδ] at h
    nlinarith
  · intro h
    rw [div_lt_iff₀ hδ]
    rw [div_lt_iff₀ hδ] at h
    nlinarith

/-- Cochrane (2023), Online Appendix p. 613 (survey E17), numerical counterexample to
"−δ < µ < 0" sufficing: `δ = 1`, `µ = −0.6` has `−δ < µ < 0` but `1 + µ < 1/(1+δ)`. -/
theorem survival_counterexample :
    -(1 : ℝ) < -0.6 ∧ (-0.6 : ℝ) < 0 ∧ 1 + (-0.6 : ℝ) < 1 / (1 + 1) := by
  norm_num

/-! ## §3.1.1 No debt and satiation: "this is fiscal theory"

Index convention: `M 0 = M_{−1}` is initial money and `M (t + 1) = M_t` is money chosen at
date `t`; `P t = P_t`, `s t = s_t`. -/

/-- Cochrane (2023), Online Appendix p. 613 and §19.3.2, p. 443: with satiation (`u_m = 0`) the
money-demand condition (19.18) `u_m/u_c = 1 − βP_t/P_{t+1}` forces `P_{t+1} = βP_t`, and the
bond price `βP_t/P_{t+1} = 1/(1+i_t)` equals one (`i = 0`). -/
theorem deflation_at_satiation {β um uc P P' : ℝ} (hP' : 0 < P') (hum : um = 0)
    (hfoc : um / uc = 1 - β * P / P') : P' = β * P ∧ β * P / P' = 1 := by
  rw [hum, zero_div] at hfoc
  have h1 : β * P / P' = 1 := by linarith
  refine ⟨?_, h1⟩
  field_simp at h1
  linarith

/-- Cochrane (2023), eq. (3.1), p. 614: the household flow budget (19.10) with no debt and
`c_t = y`, `M_{t−1} + P_t(y − y) = M_t + P_ts_t`, is `(M_t − M_{t−1})/P_t = −s_t`. -/
theorem flow_nodebt_iff {Mprev Mt Pt y st : ℝ} (hP : 0 < Pt) :
    Mprev + Pt * (y - y) = Mt + Pt * st ↔ (Mt - Mprev) / Pt = -st := by
  rw [div_eq_iff hP.ne']
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 614: with `P_{t+1} = βP_t` the price level is `P_t = βᵗP_0`. -/
theorem price_geometric {β : ℝ} {P : ℕ → ℝ} (hP : ∀ t, P (t + 1) = β * P t) (t : ℕ) :
    P t = β ^ t * P 0 := by
  induction t with
  | zero => simp
  | succ n ih => rw [hP, ih, pow_succ]; ring

/-- Cochrane (2023), p. 614: under (3.1) and `P_{t+1} = βP_t`, each discounted surplus is minus
the money added, deflated by the initial price level: `β^j s_j = −(M_j − M_{j−1})/P_0`. -/
theorem discounted_surplus {β : ℝ} {M P s : ℕ → ℝ} (hβ : 0 < β) (hP0 : 0 < P 0)
    (hP : ∀ t, P (t + 1) = β * P t) (hflow : ∀ t, (M (t + 1) - M t) / P t = -s t) (j : ℕ) :
    β ^ j * s j = -((M (j + 1) - M j) / P 0) := by
  have h := hflow j
  rw [price_geometric hP j] at h
  have : s j = -((M (j + 1) - M j) / (β ^ j * P 0)) := by linarith
  rw [this]
  field_simp

/-- Cochrane (2023), eq. (19.12) at `i = 0`, p. 614, first display: under (3.1) and
`P_{t+1} = βP_t`, `M_{−1}/P_0 = ∑_{j≤T} βʲ s_j + β^{T+1} M_T/P_{T+1}` for every `T`. -/
theorem pv_finite {β : ℝ} {M P s : ℕ → ℝ} (hβ : 0 < β) (hP0 : 0 < P 0)
    (hP : ∀ t, P (t + 1) = β * P t) (hflow : ∀ t, (M (t + 1) - M t) / P t = -s t) (T : ℕ) :
    M 0 / P 0 = ∑ j ∈ Finset.range (T + 1), β ^ j * s j + β ^ (T + 1) * M (T + 1) / P (T + 1) := by
  rw [Finset.sum_congr rfl fun j _ => discounted_surplus hβ hP0 hP hflow j, Finset.sum_neg_distrib,
    ← Finset.sum_div, Finset.sum_range_sub (fun j => M j), price_geometric hP (T + 1)]
  field_simp
  ring

/-- Cochrane (2023), p. 614, second and third displays: the same identity telescoped,
`M_{−1}/P_0 = ∑_{j≤T} −(M_j − M_{j−1})/P_0 + M_T/P_0` ("final money equals initial money plus
added money"), with `β^{T+1}M_T/P_{T+1} = M_T/P_0`. -/
theorem pv_finite_telescoped {β : ℝ} {M P : ℕ → ℝ} (hβ : 0 < β) (hP0 : 0 < P 0)
    (hP : ∀ t, P (t + 1) = β * P t) (T : ℕ) :
    M 0 / P 0 = ∑ j ∈ Finset.range (T + 1), -((M (j + 1) - M j) / P 0) + M (T + 1) / P 0 ∧
      β ^ (T + 1) * M (T + 1) / P (T + 1) = M (T + 1) / P 0 := by
  constructor
  · rw [Finset.sum_neg_distrib, ← Finset.sum_div, Finset.sum_range_sub (fun j => M j)]
    ring
  · rw [price_geometric hP (T + 1)]
    field_simp

/-- Cochrane (2023), p. 614: "final money equals initial money plus added money",
`M_T = M_{−1} + ∑_{j≤T}(M_j − M_{j−1})`. -/
theorem final_money_eq (M : ℕ → ℝ) (T : ℕ) :
    M (T + 1) = M 0 + ∑ j ∈ Finset.range (T + 1), (M (j + 1) - M j) := by
  rw [Finset.sum_range_sub (fun j => M j)]
  ring

/-- Cochrane (2023), p. 614, "The final term grows at rate `(1+µ)^T`": with constant money
growth `M_t = (1+µ)M_{t−1}` and `P_{t+1} = βP_t`, `β^{T+1}M_T/P_{T+1} = (1+µ)^{T+1}M_{−1}/P_0`,
which diverges for `µ > 0`, `M_{−1} > 0`. -/
theorem tvc_term_growth {β μ : ℝ} {M P : ℕ → ℝ} (hβ : 0 < β) (hP0 : 0 < P 0)
    (hP : ∀ t, P (t + 1) = β * P t) (hM : ∀ t, M (t + 1) = (1 + μ) * M t) :
    (∀ T, β ^ (T + 1) * M (T + 1) / P (T + 1) = (1 + μ) ^ (T + 1) * M 0 / P 0) ∧
      (0 < μ → 0 < M 0 →
        Tendsto (fun T => β ^ (T + 1) * M (T + 1) / P (T + 1)) atTop atTop) := by
  have hMt : ∀ t, M t = (1 + μ) ^ t * M 0 := by
    intro t
    induction t with
    | zero => simp
    | succ n ih => rw [hM, ih, pow_succ]; ring
  have heq : ∀ T, β ^ (T + 1) * M (T + 1) / P (T + 1) = (1 + μ) ^ (T + 1) * M 0 / P 0 := by
    intro T
    rw [(pv_finite_telescoped (M := M) hβ hP0 hP T).2, hMt]
  refine ⟨heq, fun hμ hM0 => ?_⟩
  simp only [heq]
  exact (((tendsto_pow_atTop_atTop_of_one_lt (by linarith : (1 : ℝ) < 1 + μ)).comp
    (tendsto_add_atTop_nat 1)).atTop_mul_const hM0).atTop_div_const hP0

/-- Cochrane (2023), p. 614, "The present value of surpluses explodes to negative infinity":
with helicopter money growth `µ > 0`, `M_{−1} > 0`, the partial sums `∑_{j≤T}βʲs_j → −∞`. -/
theorem pv_surplus_tendsto_bot {β μ : ℝ} {M P s : ℕ → ℝ} (hβ : 0 < β) (hP0 : 0 < P 0)
    (hP : ∀ t, P (t + 1) = β * P t) (hflow : ∀ t, (M (t + 1) - M t) / P t = -s t)
    (hM : ∀ t, M (t + 1) = (1 + μ) * M t) (hμ : 0 < μ) (hM0 : 0 < M 0) :
    Tendsto (fun T => ∑ j ∈ Finset.range (T + 1), β ^ j * s j) atTop atBot := by
  have h := (tvc_term_growth hβ hP0 hP hM).2 hμ hM0
  have heq : (fun T => ∑ j ∈ Finset.range (T + 1), β ^ j * s j) =
      fun T => M 0 / P 0 - β ^ (T + 1) * M (T + 1) / P (T + 1) := by
    funext T
    have := pv_finite hβ hP0 hP hflow T
    linarith
  rw [heq]
  exact tendsto_atBot_add_const_left _ _ (tendsto_neg_atTop_atBot.comp h)

/-- Cochrane (2023), p. 614, "there is no equilibrium initial price level, with perpetually
positive money growth, perpetually negative surpluses, and no liquidity value `u_m = 0`, whether
fiscal policy is active or passive": with `P_{t+1} = βP_t`, nondecreasing money and
`M_{−1} > 0`, the transversality condition `β^{T+1}M_T/P_{T+1} → 0` fails for every `P_0 > 0`. -/
theorem no_eqm_positive_growth {β : ℝ} {M P : ℕ → ℝ} (hβ : 0 < β) (hP0 : 0 < P 0)
    (hP : ∀ t, P (t + 1) = β * P t) (hmono : Monotone M) (hM0 : 0 < M 0) :
    ¬ Tendsto (fun T => β ^ (T + 1) * M (T + 1) / P (T + 1)) atTop (𝓝 0) := by
  intro h
  have hge : ∀ T, M 0 / P 0 ≤ β ^ (T + 1) * M (T + 1) / P (T + 1) := by
    intro T
    rw [(pv_finite_telescoped (M := M) hβ hP0 hP T).2]
    exact div_le_div_of_nonneg_right (hmono (Nat.zero_le _)) hP0.le
  have := ge_of_tendsto' h hge
  have : 0 < M 0 / P 0 := div_pos hM0 hP0
  linarith

/-- Cochrane (2023), p. 614, "a passive policy must have at some point positive surpluses …
we must in this model have a negative money growth rate `M_{t+1} − M_t < 0`": if the
transversality condition holds and `M_{−1} > 0`, some date has falling money and a positive
surplus. -/
theorem passive_requires_negative_growth {β : ℝ} {M P s : ℕ → ℝ} (hβ : 0 < β) (hP0 : 0 < P 0)
    (hP : ∀ t, P (t + 1) = β * P t) (hflow : ∀ t, (M (t + 1) - M t) / P t = -s t)
    (hM0 : 0 < M 0) (htvc : Tendsto (fun T => β ^ (T + 1) * M (T + 1) / P (T + 1)) atTop (𝓝 0)) :
    ∃ t, M (t + 1) < M t ∧ 0 < s t := by
  by_contra hcon
  push Not at hcon
  have hmono : Monotone M := by
    refine monotone_nat_of_le_succ fun n => ?_
    by_contra h
    push Not at h
    have hPn : 0 < P n := by rw [price_geometric hP n]; positivity
    have hs : 0 < s n := by
      have := hflow n
      have : (M (n + 1) - M n) / P n < 0 := div_neg_of_neg_of_pos (by linarith) hPn
      linarith
    exact absurd hs (not_lt.mpr (hcon n h))
  exact no_eqm_positive_growth hβ hP0 hP hmono hM0 htvc

/-- Cochrane (2023), p. 615, "the nominal money supply is eventually constant or declining"
(made precise): with `P_{t+1} = βP_t` the transversality condition holds iff nominal money
converges to zero. (A money stock eventually constant at a positive level violates it.) -/
theorem tvc_iff_money_vanishes {β : ℝ} {M P : ℕ → ℝ} (hβ : 0 < β) (hP0 : 0 < P 0)
    (hP : ∀ t, P (t + 1) = β * P t) :
    Tendsto (fun T => β ^ (T + 1) * M (T + 1) / P (T + 1)) atTop (𝓝 0) ↔
      Tendsto M atTop (𝓝 0) := by
  have heq : (fun T => β ^ (T + 1) * M (T + 1) / P (T + 1)) = fun T => M (T + 1) / P 0 := by
    funext T; exact (pv_finite_telescoped (M := M) hβ hP0 hP T).2
  rw [heq, ← tendsto_add_atTop_iff_nat 1 (f := M)]
  constructor
  · intro h
    have := h.mul_const (P 0)
    simp only [zero_mul] at this
    refine this.congr fun T => ?_
    field_simp
  · intro h
    simpa using h.div_const (P 0)

/-- Cochrane (2023), eq. (19.12), p. 614: under (3.1) and `P_{t+1} = βP_t`, if the discounted
surpluses are summable, the transversality term converges to `M_{−1}/P_0 − ∑ βʲs_j`. -/
theorem tvc_limit {β : ℝ} {M P s : ℕ → ℝ} (hβ : 0 < β) (hP0 : 0 < P 0)
    (hP : ∀ t, P (t + 1) = β * P t) (hflow : ∀ t, (M (t + 1) - M t) / P t = -s t)
    (hsum : Summable fun j => β ^ j * s j) :
    Tendsto (fun T => β ^ (T + 1) * M (T + 1) / P (T + 1)) atTop
      (𝓝 (M 0 / P 0 - ∑' j, β ^ j * s j)) := by
  have hpart : Tendsto (fun T => ∑ j ∈ Finset.range (T + 1), β ^ j * s j) atTop
      (𝓝 (∑' j, β ^ j * s j)) :=
    hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have heq : (fun T => β ^ (T + 1) * M (T + 1) / P (T + 1)) =
      fun T => M 0 / P 0 - ∑ j ∈ Finset.range (T + 1), β ^ j * s j := by
    funext T
    have := pv_finite hβ hP0 hP hflow T
    linarith
  rw [heq]
  exact tendsto_const_nhds.sub hpart

/-- Cochrane (2023), eq. (19.12), p. 614, infinite-horizon form: with summable discounted
surpluses, the transversality condition holds iff `M_{−1}/P_0 = ∑_{j≥0} βʲ s_j`. -/
theorem tvc_iff_pv {β : ℝ} {M P s : ℕ → ℝ} (hβ : 0 < β) (hP0 : 0 < P 0)
    (hP : ∀ t, P (t + 1) = β * P t) (hflow : ∀ t, (M (t + 1) - M t) / P t = -s t)
    (hsum : Summable fun j => β ^ j * s j) :
    Tendsto (fun T => β ^ (T + 1) * M (T + 1) / P (T + 1)) atTop (𝓝 0) ↔
      M 0 / P 0 = ∑' j, β ^ j * s j := by
  have h := tvc_limit hβ hP0 hP hflow hsum
  constructor
  · intro h0
    have := tendsto_nhds_unique h h0
    linarith
  · intro heq
    rw [heq, sub_self] at h
    exact h

/-- Cochrane (2023), pp. 614–615, "Such a government can have a determinate price level, even
with no money demand at all … the present value of surpluses must be positive": given
exogenous surpluses with summable present value `S > 0` and `M_{−1} > 0`, for each `P_0 > 0`
let the price level fall at rate `β` and money follow (3.1); the transversality condition then
holds iff `P_0 = M_{−1}/S`. -/
theorem price_level_determined {β : ℝ} {s : ℕ → ℝ} (hβ : 0 < β)
    (hsum : Summable fun j => β ^ j * s j) (hS : 0 < ∑' j, β ^ j * s j) {M P : ℕ → ℝ}
    (hP0 : 0 < P 0) (hP : ∀ t, P (t + 1) = β * P t)
    (hflow : ∀ t, (M (t + 1) - M t) / P t = -s t) (hM0 : 0 < M 0) :
    Tendsto (fun T => β ^ (T + 1) * M (T + 1) / P (T + 1)) atTop (𝓝 0) ↔
      P 0 = M 0 / ∑' j, β ^ j * s j := by
  rw [tvc_iff_pv hβ hP0 hP hflow hsum]
  constructor
  · intro h; field_simp at h ⊢; linarith
  · intro h; rw [h]; field_simp

/-- Cochrane (2023), p. 615: if the present value of surpluses is not positive, no positive
initial price level satisfies the transversality condition (`M_{−1} > 0`). -/
theorem no_price_level_of_nonpos_pv {β : ℝ} {s : ℕ → ℝ} (hβ : 0 < β)
    (hsum : Summable fun j => β ^ j * s j) (hS : ∑' j, β ^ j * s j ≤ 0) {M P : ℕ → ℝ}
    (hP0 : 0 < P 0) (hP : ∀ t, P (t + 1) = β * P t)
    (hflow : ∀ t, (M (t + 1) - M t) / P t = -s t) (hM0 : 0 < M 0) :
    ¬ Tendsto (fun T => β ^ (T + 1) * M (T + 1) / P (T + 1)) atTop (𝓝 0) := by
  rw [tvc_iff_pv hβ hP0 hP hflow hsum]
  intro h
  have : 0 < M 0 / P 0 := div_pos hM0 hP0
  linarith

/-! ## §3.1.2 No violation with open-market operations

Here `D t = B_t + M_t` (book dating, from `t = 0`), `P t = P_t`, `s t = s_t`; the flow budget
with `Q = 1` at date `t + 1` is `D_t/P_{t+1} = D_{t+1}/P_{t+1} + s_{t+1}`. -/

/-- Cochrane (2023), §3.1.2, p. 615: with the surplus rule `s_{t+1} = (1−β)D_t/P_{t+1}`, total
nominal debt declines, `B_t + M_t = β(B_{t−1} + M_{t−1})`, hence `B_t + M_t = βᵗ(B_0 + M_0)`
(p. 616). -/
theorem omo_total_debt {β : ℝ} {D P s : ℕ → ℝ} (hP : ∀ t, 0 < P t)
    (hflow : ∀ t, D t / P (t + 1) = D (t + 1) / P (t + 1) + s (t + 1))
    (hs : ∀ t, s (t + 1) = (1 - β) * D t / P (t + 1)) :
    (∀ t, D (t + 1) = β * D t) ∧ ∀ t, D t = β ^ t * D 0 := by
  have h1 : ∀ t, D (t + 1) = β * D t := by
    intro t
    have h := hflow t
    rw [hs t] at h
    have := hP (t + 1)
    field_simp at h
    linarith
  refine ⟨h1, fun t => ?_⟩
  induction t with
  | zero => simp
  | succ n ih => rw [h1, ih, pow_succ]; ring

/-- Cochrane (2023), §3.1.2, p. 615: with `P_{t+1} = βP_t`, real total debt is constant,
`(B_t + M_t)/P_{t+1} = (B_{t−1} + M_{t−1})/P_t`. -/
theorem omo_real_debt_const {β : ℝ} {D P : ℕ → ℝ} (hβ : 0 < β) (hP : ∀ t, 0 < P t)
    (hD : ∀ t, D (t + 1) = β * D t) (hPβ : ∀ t, P (t + 1) = β * P t) (t : ℕ) :
    D (t + 1) / P (t + 2) = D t / P (t + 1) := by
  rw [hD, hPβ (t + 1)]
  have := hP (t + 1)
  field_simp

/-- Cochrane (2023), §3.1.2, p. 616: with money growing by open-market purchases,
`M_t = (1+µ)ᵗM_0`, bonds are `B_t = βᵗ(B_0 + M_0) − (1+µ)ᵗM_0`. -/
theorem omo_bonds {β μ : ℝ} {B M : ℕ → ℝ} (hD : ∀ t, B t + M t = β ^ t * (B 0 + M 0))
    (hM : ∀ t, M t = (1 + μ) ^ t * M 0) (t : ℕ) :
    B t = β ^ t * (B 0 + M 0) - (1 + μ) ^ t * M 0 := by
  have := hD t
  rw [hM t] at this
  linarith

/-- Cochrane (2023), §3.1.2, p. 616, "government debt becomes negative": if `β < 1 + µ` and
`M_0 > 0`, bonds are eventually negative. -/
theorem omo_bonds_eventually_neg {β μ : ℝ} {B M : ℕ → ℝ} (hβ : 0 < β) (hμβ : β < 1 + μ)
    (hM0 : 0 < M 0) (hD : ∀ t, B t + M t = β ^ t * (B 0 + M 0))
    (hM : ∀ t, M t = (1 + μ) ^ t * M 0) : ∀ᶠ t in atTop, B t < 0 := by
  have hμ : 0 < 1 + μ := by linarith
  have hq : Tendsto (fun t : ℕ => (β / (1 + μ)) ^ t * (B 0 + M 0) - M 0) atTop
      (𝓝 (0 * (B 0 + M 0) - M 0)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (div_pos hβ hμ).le
      ((div_lt_one hμ).mpr hμβ)).mul_const _).sub_const _
  have hev := hq.eventually (gt_mem_nhds (by linarith : 0 * (B 0 + M 0) - M 0 < 0))
  filter_upwards [hev] with t ht
  rw [omo_bonds hD hM t]
  have hpos : 0 < (1 + μ) ^ t := pow_pos hμ t
  have : β ^ t * (B 0 + M 0) - (1 + μ) ^ t * M 0 =
      (1 + μ) ^ t * ((β / (1 + μ)) ^ t * (B 0 + M 0) - M 0) := by
    rw [div_pow]; field_simp
  rw [this]
  exact mul_neg_of_pos_of_neg hpos ht

/-- Cochrane (2023), §3.1.2, pp. 615–616, "the individual quantities of money and debt explode
in opposite directions": with `0 < β < 1`, `µ > 0`, `M_0 > 0`, `M_t → +∞` and `B_t → −∞`. -/
theorem omo_explode {β μ : ℝ} {B M : ℕ → ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hμ : 0 < μ)
    (hM0 : 0 < M 0) (hD : ∀ t, B t + M t = β ^ t * (B 0 + M 0))
    (hM : ∀ t, M t = (1 + μ) ^ t * M 0) :
    Tendsto M atTop atTop ∧ Tendsto B atTop atBot := by
  have hMt : Tendsto M atTop atTop := by
    have := (tendsto_pow_atTop_atTop_of_one_lt (by linarith : (1 : ℝ) < 1 + μ)).atTop_mul_const
      hM0
    exact this.congr fun t => (hM t).symm
  refine ⟨hMt, ?_⟩
  have hb : Tendsto (fun t : ℕ => β ^ t * (B 0 + M 0)) atTop (𝓝 (0 * (B 0 + M 0))) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).mul_const _
  have : B = fun t => β ^ t * (B 0 + M 0) + -M t := by
    funext t; have := hD t; linarith
  rw [this]
  exact Tendsto.add_atBot hb (tendsto_neg_atTop_atBot.comp hMt)

/-- Cochrane (2023), §3.1.2, p. 615, "the transversality condition holds": with `0 < β < 1`,
`P_t = βᵗP_0` and `B_t + M_t = βᵗ(B_0 + M_0)`, the term `β^{T+1}(B_T + M_T)/P_{T+1}` tends to zero
(it equals `βᵀ(B_0 + M_0)/P_0`). -/
theorem omo_tvc {β : ℝ} {D P : ℕ → ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hP0 : 0 < P 0)
    (hPβ : ∀ t, P (t + 1) = β * P t) (hD : ∀ t, D t = β ^ t * D 0) :
    (∀ T, β ^ (T + 1) * D T / P (T + 1) = β ^ T * D 0 / P 0) ∧
      Tendsto (fun T => β ^ (T + 1) * D T / P (T + 1)) atTop (𝓝 0) := by
  have heq : ∀ T, β ^ (T + 1) * D T / P (T + 1) = β ^ T * D 0 / P 0 := by
    intro T
    rw [hD, price_geometric hPβ (T + 1)]
    field_simp
  refine ⟨heq, ?_⟩
  simp only [heq]
  simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).mul_const (D 0)).div_const
    (P 0)

/-- Cochrane (2023), §3.1.2, p. 615: under the surplus rule and `P_{t+1} = βP_t`, the present
value budget holds: `(B_0 + M_0)/P_1 = ∑_{j≥0} βʲ s_{j+1}` (a genuine sum; the surplus is the
constant `(1−β)(B_0 + M_0)/P_1`). -/
theorem omo_pv {β : ℝ} {D P s : ℕ → ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hP : ∀ t, 0 < P t)
    (hflow : ∀ t, D t / P (t + 1) = D (t + 1) / P (t + 1) + s (t + 1))
    (hs : ∀ t, s (t + 1) = (1 - β) * D t / P (t + 1)) (hPβ : ∀ t, P (t + 1) = β * P t) :
    HasSum (fun j => β ^ j * s (j + 1)) (D 0 / P 1) := by
  obtain ⟨hD1, -⟩ := omo_total_debt hP hflow hs
  have hconst : ∀ j, D j / P (j + 1) = D 0 / P 1 := by
    intro j
    induction j with
    | zero => rfl
    | succ n ih => rw [omo_real_debt_const hβ hP hD1 hPβ n, ih]
  have hsj : ∀ j, β ^ j * s (j + 1) = β ^ j * ((1 - β) * (D 0 / P 1)) := by
    intro j; rw [hs j, mul_div_assoc, hconst j]
  have hgeo := (hasSum_geometric_of_lt_one hβ.le hβ1).mul_right ((1 - β) * (D 0 / P 1))
  have h1 : (1 - β)⁻¹ * ((1 - β) * (D 0 / P 1)) = D 0 / P 1 := by
    field_simp [(by linarith : (1 - β) ≠ 0)]
  rw [h1] at hgeo
  exact hgeo.congr_fun fun j => (hsj j)

/-! ## §3.1.3 Optimality with valued money -/

/-- Cochrane (2023), eq. (3.2) and p. 616: the last-period first-order condition. If the
consumer's real resources are `w` and `(c*, m*) = (w − m*, m*)` maximizes `u(c, m)` on the
budget line `c + m = w`, and `u` is differentiable there, then `u_c = u_m`. -/
theorem last_period_foc {u : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {w ms : ℝ}
    (hu : HasFDerivAt u L (w - ms, ms)) (hmax : ∀ m, u (w - m, m) ≤ u (w - ms, ms)) :
    L (1, 0) = L (0, 1) := by
  have hpath : HasDerivAt (fun m : ℝ => (w - m, m)) ((-1 : ℝ), (1 : ℝ)) ms := by
    have h1 : HasDerivAt (fun m : ℝ => w - m) (-1) ms := by
      simpa using (hasDerivAt_id ms).const_sub w
    exact h1.prodMk (hasDerivAt_id ms)
  have hcomp : HasDerivAt (fun m => u (w - m, m)) (L ((-1 : ℝ), (1 : ℝ))) ms :=
    HasFDerivAt.comp_hasDerivAt (l := u) (l' := L) (f := fun m : ℝ => (w - m, m)) ms hu hpath
  have hmaxl : IsLocalMax (fun m => u (w - m, m)) ms := Filter.Eventually.of_forall hmax
  have h0 := hmaxl.hasDerivAt_eq_zero hcomp
  have hsplit : ((-1 : ℝ), (1 : ℝ)) = (-1 : ℝ) • ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, smul_eq_mul] at h0
  linarith

/-- Cochrane (2023), p. 616 (sufficiency, under concavity in supergradient form): if
`u(c, m) ≤ u(c*, m*) + u_c(c − c*) + u_m(m − m*)` for all `(c, m)`, `u_c = u_m` and
`c* + m* = w`, then `(c*, m*)` maximizes `u` on the budget line `c + m = w`. -/
theorem last_period_foc_sufficient {u : ℝ × ℝ → ℝ} {cs ms uc um w : ℝ}
    (hsup : ∀ c m, u (c, m) ≤ u (cs, ms) + uc * (c - cs) + um * (m - ms)) (hfoc : uc = um)
    (hw : cs + ms = w) (m : ℝ) : u (w - m, m) ≤ u (cs, ms) := by
  have := hsup (w - m) m
  rw [hfoc] at this
  have h : um * (w - m - cs) + um * (m - ms) = 0 := by rw [← hw]; ring
  linarith

/-- Cochrane (2023), p. 616, "positive and finite marginal utility of consumption means
positive and finite … money demand", power case (19.20): for `c, m > 0`,
`u_c = c^{−γ} = θ m^{−γ} = u_m` iff `m = θ^{1/γ} c`. -/
theorem last_period_power_demand {θ γ c m : ℝ} (hθ : 0 < θ) (hγ : 0 < γ) (hc : 0 < c)
    (hm : 0 < m) : ucPow γ c = umPow θ γ m ↔ m = θ ^ (1 / γ) * c := by
  unfold ucPow umPow
  have hkey : (θ ^ (1 / γ) * c) ^ (-γ) = θ⁻¹ * c ^ (-γ) := by
    rw [Real.mul_rpow (by positivity) hc.le, ← Real.rpow_mul hθ.le,
      show 1 / γ * -γ = -1 by field_simp, Real.rpow_neg_one]
  constructor
  · intro h
    have h1 : m ^ (-γ) = (θ ^ (1 / γ) * c) ^ (-γ) := by
      rw [hkey, h]; field_simp
    have h2 := congrArg (fun z => z ^ (-γ)⁻¹) h1
    rwa [Real.rpow_rpow_inv hm.le (by linarith),
      Real.rpow_rpow_inv (by positivity) (by linarith)] at h2
  · intro h
    rw [h, hkey]
    field_simp

/-- Cochrane (2023), p. 617, "higher consumption means the marginal utility of consumption
declines. Hence, the marginal utility of money must also decline, and desired real money
holdings must rise": with separable utility, `u_c` and `u_m` strictly decreasing, and
`u_m(m_i) = k·u_c(c_i)` (`k = i/(1+i) > 0`), `c₁ < c₂` implies `m₁ < m₂`. -/
theorem separable_money_demand_rises {uc um : ℝ → ℝ} {k c1 c2 m1 m2 : ℝ}
    (huc : StrictAntiOn uc (Set.Ioi 0)) (hum : StrictAntiOn um (Set.Ioi 0)) (hk : 0 < k)
    (hc1 : 0 < c1) (hc12 : c1 < c2) (hm1 : 0 < m1) (hm2 : 0 < m2) (h1 : um m1 = k * uc c1)
    (h2 : um m2 = k * uc c2) : m1 < m2 := by
  have hu : uc c2 < uc c1 := huc hc1 (lt_trans hc1 hc12) hc12
  have : um m2 < um m1 := by rw [h1, h2]; exact mul_lt_mul_of_pos_left hu hk
  by_contra hcon
  push Not at hcon
  rcases hcon.lt_or_eq with hlt | heq
  · have := hum hm2 hm1 hlt; linarith
  · rw [heq] at this; linarith

/-- Cochrane (2023), p. 616, the consumer's iterated budget constraint with money and interest:
if `M_{t−1} + P_t(y − c_t) = M_t + P_ts_t` and `1/(1+i_t) = βP_t/P_{t+1}`, then
`M_{−1}/P_0 = ∑_{j≤T} βʲ[i_j/(1+i_j)·M_j/P_j + s_j + c_j − y] + β^{T+1}M_T/P_{T+1}`. -/
theorem iterated_budget {β y : ℝ} {M P s c i : ℕ → ℝ} (hP : ∀ t, 0 < P t)
    (hi : ∀ t, 1 + i t ≠ 0)
    (hflow : ∀ t, M t + P t * (y - c t) = M (t + 1) + P t * s t)
    (hQ : ∀ t, 1 / (1 + i t) = β * P t / P (t + 1)) (T : ℕ) :
    M 0 / P 0 = ∑ j ∈ Finset.range (T + 1),
        β ^ j * (i j / (1 + i j) * (M (j + 1) / P j) + s j + c j - y) +
      β ^ (T + 1) * M (T + 1) / P (T + 1) := by
  have hstep : ∀ j, M j / P j = (i j / (1 + i j) * (M (j + 1) / P j) + s j + c j - y) +
      β * (M (j + 1) / P (j + 1)) := by
    intro j
    have h1 : i j / (1 + i j) = 1 - β * P j / P (j + 1) := by
      rw [← hQ j]; field_simp [hi j]; ring
    have := hP j; have := hP (j + 1)
    have hf := hflow j
    have h2 : M j / P j = M (j + 1) / P j + s j + c j - y := by
      field_simp
      linarith
    rw [h2, h1]
    field_simp
    ring
  induction T with
  | zero =>
    rw [Finset.sum_range_one, hstep 0]
    ring
  | succ n ih =>
    have e := hstep (n + 1)
    rw [Finset.sum_range_succ, ih, mul_div_assoc, e]
    ring

end Cochrane.Monetarism.PruningDeflation
