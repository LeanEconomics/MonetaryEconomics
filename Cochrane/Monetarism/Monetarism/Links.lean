/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.Seigniorage
import Monetarism.CaganRE
import Monetarism.Nonseparable
import Monetarism.CashInAdvance
import Monetarism.ContinuousTime

/-!
# Links between the Monetarism chains

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19 (pp. 433–462) and Online
Appendices A3 (pp. 612–634) and A4 (pp. 635–641). Cross-chain connection theorems: the same book
objects formalised in different modules, in different coordinates or in different models.

## Main results

* **Money in utility, two coordinate systems.** Cochrane's (19.23) map `MoneyInUtility.nextX`
  in `x = Py/M` and the Online Appendix real-balance map `PruningDeflation.ratioMap` in
  `m = M/(Py) = 1/x` are conjugate (`ratioMap_eq_one_div_nextX`); paths of (19.21) in either
  form coincide (`isMPath_iff_isPowerPath`), and both are Woodford's separable map
  (`isMIUPath_iff_isMPath`, through `MoneyTargetingDynamics.miuPath_iff_sepPath`).
* **E13 = E17.** The existence of the inflationary steady state (E13, p. 445), the existence of
  deflationary paths (E17, A3 p. 613) and the existence of a unique `m̄` are the one condition
  `1 + µ > β` (`e13_iff_e17`). Along the deflations the PruningDeflation path is the
  MoneyTargetingDynamics orbit to `x = 0`, with rate `β/(1 + µ)` (`deflation_rate`); the finite
  time explosion of A3 (3.3) is `MoneyTargetingDynamics.power_inflation_exits` read in `m`
  (`explosion_same_path`).
* **The money TVC across MIU and CIA.** The MIU transversality term along a deflation and the
  CIA discounted real money along the deflationary equilibria of p. 454 vanish under the same
  condition `µ < 0` (`deflation_tvc_miu_iff_cia`); the CIA deflations also exist at the boundary
  `1 + µ = β`, where the MIU has none (`cia_boundary_deflation`).
* **Present values.** The `Regimes` valuation equation in `tsum` form is the
  `CashInAdvance.Stochastic.pv_iff_tvc` engine applied to the flow constraint
  (`flow_pv_tsum_iff_tvc`).
* **Optimality.** CIA sufficiency for any concave `u` via `MoneyInUtility.concave_le_tangent`
  (`cia_euler_sufficient_of_concave`, `tree_euler_sufficient_of_concave`); the two finite-tree
  notions of a node-contingent plan coincide (`meas_iff_tAdapted`).
* **Discrete versus continuous first-order conditions.** (19.13)–(19.14) give (19.16) through the
  algebra of (4.2) (`miu_foc_money_demand`); (19.13) is the discrete form of (4.1)
  (`miu_foc_log_growth`); the per-period interest cost `i/(1 + i)` per unit time tends to `i`
  (`interest_cost_continuous_limit`).
* **CES.** The A3 (p. 632) and A4 (p. 636) CES utilities differ by a constant
  (`ces_nonsep_eq_ct`), so their marginal utilities agree (`ces_uc_nonsep_eq_ct`,
  `ces_um_nonsep_eq_ct`); the A4 money demand is the inverse power demand
  (`demand_4_8_eq_power_demand`).
* **Cagan, seigniorage and fiscal selection.** Cagan velocity and revenue are the Seigniorage
  Cagan example (`cagan_steady_revenue`); the fiscally selected Cagan path is the bounded one iff
  money and fiscal policy are coordinated as in NI-7 (`cagan_ni7`); discrete unpleasant-arithmetic
  seigniorage is steady-state revenue (`seig_eq_revenue`); the Regimes and CIA passive surplus
  rules agree (`passiveSurplus_regimes_eq_cia`).
-/

namespace Cochrane.Monetarism.Links

open Filter Topology

/-! ## Money in utility: `x = Py/M` versus `m = M/(Py)` -/

/-- A general lemma: `(1/z)^γ = z^{−γ}` for `z > 0` (the change of coordinates `x = 1/m` of
Cochrane (2023), (19.23), p. 444, and Online Appendix p. 612). -/
theorem one_div_rpow_eq {z γ : ℝ} (hz : 0 < z) : (1 / z) ^ γ = z ^ (-γ) := by
  rw [Real.rpow_neg hz.le, one_div, Real.inv_rpow hz.le]

/-- Cochrane (2023), eq. (19.23), p. 444, and Online Appendix p. 612: the real-balance map
`m ↦ (1+µ)/β (1 − θm^{−γ}) m` is the canonical (19.23) map `nextX` conjugated by `m ↦ 1/m`,
`ratioMap(m) = 1/nextX(1/m)`, with `x̄` the steady state (19.22). -/
theorem ratioMap_eq_one_div_nextX {β μ θ γ m xb : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hm : 0 < m)
    (hden : θ * (1 / m) ^ γ ≠ 1) (hss : θ * xb ^ γ = 1 - β / (1 + μ)) :
    PruningDeflation.ratioMap β μ θ γ m = 1 / MoneyInUtility.nextX θ γ xb (1 / m) := by
  have h := (PruningDeflation.eq1923_iff (m' := PruningDeflation.ratioMap β μ θ γ m) hβ hμ hm
    hden hss).mp rfl
  rw [← h, one_div_one_div]

/-- Cochrane (2023), eq. (19.21), p. 444, and Online Appendix p. 612: a path of real balances
`m = M/(Py)` of the Online Appendix (`IsMPath`) is exactly a path `x = 1/m` of (19.21) in
Chapter 19's form (`IsPowerPath`, money growth `1 + µ`). -/
theorem isMPath_iff_isPowerPath {β μ θ γ : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) :
    PruningDeflation.IsMPath β μ θ γ m ↔
      MoneyInUtility.IsPowerPath β θ γ (1 + μ) (fun t => 1 / m t) := by
  constructor
  · intro h t
    obtain ⟨h0, h1⟩ := h t
    have h0' := (h (t + 1)).1
    refine ⟨one_div_pos.mpr h0, ?_⟩
    have e1 : (1 / m t) / (1 / m (t + 1)) = m (t + 1) / m t := by field_simp
    have e2 : m (t + 1) / m t = (1 + μ) / β * (1 - θ * m t ^ (-γ)) := by
      rw [h1]
      unfold PruningDeflation.ratioMap
      field_simp
    simp only
    rw [one_div_rpow_eq h0, e1, e2]
    field_simp
    ring
  · intro h t
    obtain ⟨h0, h1⟩ := h t
    have hm0 : 0 < m t := one_div_pos.mp h0
    have hm1 : 0 < m (t + 1) := one_div_pos.mp (h (t + 1)).1
    refine ⟨hm0, ?_⟩
    have e1 : (1 / m t) / (1 / m (t + 1)) = m (t + 1) / m t := by field_simp
    simp only at h1
    rw [one_div_rpow_eq hm0, e1] at h1
    unfold PruningDeflation.ratioMap
    rw [h1]
    field_simp
    ring

/-- Cochrane (2023), eq. (19.18), p. 442, with power utility (19.20), p. 443, and Online
Appendix p. 612: with constant output `y`, `u_c(y) = y^{−γ}`, `u_m(z) = θz^{−γ}` and money
growth `1 + µ`, a path of real balances `M/P = y·m` of (19.18) (`MoneyInUtility.IsMIUPath`) is
exactly a path of the Online Appendix map in `m = M/(Py)` (`IsMPath`). The bridge is
Woodford's separable map, `MoneyTargetingDynamics.miuPath_iff_sepPath`. -/
theorem isMIUPath_iff_isMPath {β μ θ γ y : ℝ} {M m : ℕ → ℝ} (hβ : 0 < β)
    (hy : 0 < y) (hM : ∀ t, 0 < M t) (hg : ∀ t, M (t + 1) = (1 + μ) * M t) :
    MoneyInUtility.IsMIUPath β (y ^ (-γ)) (fun z => θ * z ^ (-γ)) M (fun t => y * m t) ↔
      PruningDeflation.IsMPath β μ θ γ m := by
  have hc : 0 < y ^ (-γ) := Real.rpow_pos_of_pos hy _
  rw [MoneyTargetingDynamics.miuPath_iff_sepPath hβ hc hM hg]
  have hcy : y ^ (-γ) * y ≠ 0 := (mul_pos hc hy).ne'
  constructor
  · rintro ⟨hpos, hrec⟩ t
    have hm : 0 < m t := (mul_pos_iff_of_pos_left hy).mp (hpos t)
    refine ⟨hm, ?_⟩
    have h := hrec t
    unfold MoneyTargetingDynamics.sepF at h
    simp only at h
    rw [Real.mul_rpow hy.le hm.le] at h
    unfold PruningDeflation.ratioMap
    exact mul_left_cancel₀ hcy (by linear_combination h)
  · intro h
    refine ⟨fun t => mul_pos hy (h t).1, fun t => ?_⟩
    obtain ⟨hm, h1⟩ := h t
    unfold MoneyTargetingDynamics.sepF
    simp only
    rw [Real.mul_rpow hy.le hm.le, h1]
    unfold PruningDeflation.ratioMap
    ring

/-! ## E13 (p. 445) and E17 (A3 p. 613): one condition `1 + µ > β` -/

/-- Cochrane (2023), pp. 444–445 (survey E13) and Online Appendix p. 613 (survey E17): for
`θ, γ, β > 0` and `1 + µ > 0` the following are each equivalent to `β < 1 + µ`: the inflationary
steady state `x̄ > 0` of (19.22) exists (`MoneyInUtility.e13_corrected`); a deflationary path of
real balances (`m_t → ∞`) exists (`PruningDeflation.deflation_path_exists`,
`no_deflation_of_le_beta`); the steady state `m̄ = 1/x̄` exists and is unique
(`PruningDeflation.steady_exists_unique`). The printed conditions `1 + µ > 1/β` (E13) and
`µ > −δ` (E17) are both this single condition misprinted. -/
theorem e13_iff_e17 {β μ θ γ : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ) (hγ : 0 < γ) :
    ((∃ xb, 0 < xb ∧ θ * xb ^ γ = 1 - β / (1 + μ)) ↔ β < 1 + μ) ∧
      ((∃ m : ℕ → ℝ, PruningDeflation.IsMPath β μ θ γ m ∧ Tendsto m atTop atTop) ↔
        β < 1 + μ) ∧
      ((∃! ms : ℝ, 0 < ms ∧ θ * ms ^ (-γ) = 1 - β / (1 + μ)) ↔ β < 1 + μ) := by
  have h1 := (MoneyInUtility.e13_corrected (β := β) hθ hγ hμ).1
  refine ⟨h1, ⟨fun ⟨m, hp, hT⟩ => ?_, fun h => ?_⟩, ⟨fun ⟨ms, ⟨hms, hss⟩, _⟩ => ?_,
    fun h => PruningDeflation.steady_exists_unique hβ h hθ hγ⟩⟩
  · by_contra hle
    push Not at hle
    have hanti := PruningDeflation.no_deflation_of_le_beta hβ hμ hle hθ hp
    obtain ⟨t, ht⟩ := (hT.eventually (eventually_gt_atTop (m 0))).exists
    linarith [hanti.antitone (Nat.zero_le t)]
  · obtain ⟨ms, ⟨hms, hss⟩, -⟩ := PruningDeflation.steady_exists_unique hβ h hθ hγ
    obtain ⟨m, ⟨hp, -, hT⟩, -⟩ := PruningDeflation.deflation_path_exists hβ hμ hθ hγ hms hss
      (lt_add_one ms)
    exact ⟨m, hp, hT⟩
  · exact h1.mp ⟨1 / ms, one_div_pos.mpr hms, by rw [one_div_rpow_eq hms, hss]⟩

/-- Cochrane (2023), p. 444 ("This steady state is stable … `lim P_{t+1}/P_t = 1/(1 + δ)`") and
Online Appendix p. 612: along a deflationary path of real balances (`m₀ > m̄`) the inverse
`x_t = 1/m_t = P_ty/M_t` follows the canonical (19.23) map with `x̄ = 1/m̄`, converges to the
deflationary steady state `x = 0`, and `x_{t+1}/x_t → β/(1 + µ)`; the rate comes from
`MoneyTargetingDynamics.power_deflation_orbit`. -/
theorem deflation_rate {β μ θ γ ms : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμβ : β < 1 + μ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ))
    (hpath : PruningDeflation.IsMPath β μ θ γ m) (h0 : ms < m 0) :
    (∀ t, 1 / m (t + 1) = MoneyInUtility.nextX θ γ (1 / ms) (1 / m t)) ∧
      Tendsto (fun t => 1 / m t) atTop (𝓝 0) ∧
      Tendsto (fun t => (1 / m (t + 1)) / (1 / m t)) atTop (𝓝 (β / (1 + μ))) := by
  have hμ : 0 < 1 + μ := lt_trans hβ hμβ
  have hxb : θ * (1 / ms) ^ γ = 1 - β / (1 + μ) := by rw [one_div_rpow_eq hms, hss]
  have hgrow := PruningDeflation.deflation_growth hβ hμ hθ hγ hms hss hpath h0
  have hm0 : 0 < m 0 := lt_trans hms h0
  have hlt : ∀ t, θ * (1 / m t) ^ γ < 1 := by
    intro t
    have hmt : 0 < m t := (hpath t).1
    have h1 : m t ^ (-γ) ≤ m 0 ^ (-γ) :=
      Real.rpow_le_rpow_of_nonpos hm0 (hgrow.2 t).1 (by linarith)
    have h2 : m 0 ^ (-γ) < ms ^ (-γ) := Real.rpow_lt_rpow_of_neg hms h0 (by linarith)
    have h3 : 0 < β / (1 + μ) := div_pos hβ hμ
    rw [one_div_rpow_eq hmt]
    nlinarith [mul_le_mul_of_nonneg_left h1 hθ.le, mul_lt_mul_of_pos_left h2 hθ]
  have hrec : ∀ t, 1 / m (t + 1) = MoneyInUtility.nextX θ γ (1 / ms) (1 / m t) := fun t =>
    (PruningDeflation.eq1923_iff hβ hμ (hpath t).1 (hlt t).ne hxb).mp (hpath t).2
  have hK : 0 < 1 - θ * (1 / ms) ^ γ := by rw [hxb]; have := div_pos hβ hμ; linarith
  have horb := MoneyTargetingDynamics.power_deflation_orbit (x := fun t => 1 / m t) hθ hγ
    (one_div_pos.mpr hms) hK hrec (one_div_pos.mpr hm0) (one_div_lt_one_div_of_lt hms h0)
  refine ⟨hrec, horb.2.2.1, ?_⟩
  have e : 1 - θ * (1 / ms) ^ γ = β / (1 + μ) := by rw [hxb]; ring
  rw [← e]
  exact horb.2.2.2

/-- Cochrane (2023), Online Appendix eq. (3.3), p. 619 ("the price level eventually explodes to
infinity in finite time"), and Figure 19.1, p. 444: from `0 < m₀ < m̄` the real-balance orbit
reaches the demonetisation region at a finite date `T`, i.e. `x_T = 1/m_T` has `θx_T^γ ≥ 1`
(`u_m/u_c ≥ 1`, the exit of `MoneyTargetingDynamics.power_inflation_exits`), and before `T` the
orbit `x_t = 1/m_t` is the orbit of the canonical (19.23) map inside its domain `θx^γ < 1`. -/
theorem explosion_same_path {β μ θ γ ms m0 : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hθ : 0 < θ)
    (hγ : 0 < γ) (hms : 0 < ms) (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) (hm0 : 0 < m0)
    (hlt : m0 < ms) :
    ∃ T, 0 < (PruningDeflation.ratioMap β μ θ γ)^[T] m0 ∧
      1 ≤ θ * (1 / (PruningDeflation.ratioMap β μ θ γ)^[T] m0) ^ γ ∧
      ∀ t < T, θ * (1 / (PruningDeflation.ratioMap β μ θ γ)^[t] m0) ^ γ < 1 ∧
        1 / (PruningDeflation.ratioMap β μ θ γ)^[t + 1] m0 =
          MoneyInUtility.nextX θ γ (1 / ms) (1 / (PruningDeflation.ratioMap β μ θ γ)^[t] m0) := by
  set g := PruningDeflation.ratioMap β μ θ γ with hg
  obtain ⟨T, hT, hbefore⟩ := PruningInflation.finite_time_explosion hβ hμ hθ hγ hss hm0 hlt
  have hwp : 0 < θ ^ (1 / γ) := by positivity
  have hxb : θ * (1 / ms) ^ γ = 1 - β / (1 + μ) := by rw [one_div_rpow_eq hms, hss]
  -- above the demonetisation level the map is positive and `θx^γ < 1`
  have habove : ∀ z, θ ^ (1 / γ) < z → 0 < g z ∧ θ * (1 / z) ^ γ < 1 := by
    intro z hz
    have hz0 : 0 < z := lt_trans hwp hz
    have h1 : z ^ (-γ) < (θ ^ (1 / γ)) ^ (-γ) := Real.rpow_lt_rpow_of_neg hwp hz (by linarith)
    have h2 := PruningInflation.wp_spec hθ hγ
    have h3 : θ * z ^ (-γ) < 1 := by nlinarith [mul_lt_mul_of_pos_left h1 hθ]
    refine ⟨?_, by rw [one_div_rpow_eq hz0]; exact h3⟩
    rw [hg]
    unfold PruningDeflation.ratioMap
    have : 0 < 1 - θ * z ^ (-γ) := by linarith
    have := div_pos hμ hβ
    positivity
  have hposT : 0 < g^[T] m0 := by
    rcases Nat.eq_zero_or_pos T with rfl | hT0
    · simpa using hm0
    · obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
      rw [Function.iterate_succ_apply']
      exact (habove _ (hbefore k (by omega))).1
  refine ⟨T, hposT, ?_, fun t ht => ⟨(habove _ (hbefore t ht)).2, ?_⟩⟩
  · have h := (PruningInflation.explosion_x_form hθ hγ hposT).mp hT
    linarith
  · have hz := hbefore t ht
    rw [Function.iterate_succ_apply']
    exact (PruningDeflation.eq1923_iff hβ hμ (lt_trans hwp hz) (habove _ hz).2.ne hxb).mp rfl

/-! ## The money TVC along deflations: MIU (A3 p. 613) and CIA (p. 454) -/

/-- Cochrane (2023), Online Appendix pp. 612–613 (E17) and p. 454 (`CashInAdvance.PF`): the
transversality condition fails along the money-in-utility deflations exactly when it fails along
the cash-in-advance deflationary equilibria: both vanish iff `µ < 0`, so the MIU TVC term
`β^{T+1}M_T/(P_{T+1}y)` tends to zero iff the CIA discounted real money `β^tM_t/P_t` does. -/
theorem deflation_tvc_miu_iff_cia {β μ θ γ ms Mm1 P0 : ℝ} {m : ℕ → ℝ} (hβ : 0 < β)
    (hμβ : β < 1 + μ) (hθ : 0 < θ) (hγ : 0 < γ) (hms : 0 < ms)
    (hss : θ * ms ^ (-γ) = 1 - β / (1 + μ)) (hpath : PruningDeflation.IsMPath β μ θ γ m)
    (h0 : ms < m 0) (hP0 : 0 < P0) (hM : 0 < Mm1) :
    (Tendsto (PruningDeflation.tvcTerm β μ m) atTop (𝓝 0) ↔ μ < 0) ∧
      (Tendsto (fun t : ℕ => β ^ t * (Mm1 * (1 + μ) ^ (t + 1)) / (β ^ t * P0)) atTop (𝓝 0) ↔
        μ < 0) ∧
      (Tendsto (PruningDeflation.tvcTerm β μ m) atTop (𝓝 0) ↔
        Tendsto (fun t : ℕ => β ^ t * (Mm1 * (1 + μ) ^ (t + 1)) / (β ^ t * P0)) atTop
          (𝓝 0)) := by
  have h1 := PruningDeflation.tvc_tendsto_zero_iff hβ hμβ hθ hγ hms hss hpath h0
  have h2 := CashInAdvance.PF.deflation_money_tvc_iff (μ := μ) hβ hP0 hM (lt_trans hβ hμβ)
  exact ⟨h1, h2, h1.trans h2.symm⟩

/-- Cochrane (2023), p. 454 versus pp. 444–445 and A3 p. 613: at the boundary `1 + µ = β` the
cash-in-advance model still has its zero-rate deflationary equilibria (`P_t = β^tP_0`,
`CashInAdvance.PF.deflation_equilibrium`, for `P_0 ≤ M_0V/y`), while the money-in-utility model
has no deflationary path of real balances at all (`e13_iff_e17`): the CIA condition is
`1 + µ ≥ β`, the MIU condition the strict `1 + µ > β`. -/
theorem cia_boundary_deflation {β μ θ γ y V Mm1 P0 A0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : 0 < θ) (hγ : 0 < γ) (hb : 1 + μ = β) (hM : 0 ≤ Mm1) (hP0 : 0 < P0)
    (hcap : P0 * y / V ≤ Mm1 * (1 + μ)) :
    CashInAdvance.PF.MonetaryEq β y V (fun t => β ^ t * P0)
        (fun t => A0 * β ^ t - Mm1 * (1 + μ) ^ t) (fun t => Mm1 * (1 + μ) ^ t)
        (fun _ => A0 * (1 - β) / P0) ∧
      ¬ ∃ m : ℕ → ℝ, PruningDeflation.IsMPath β μ θ γ m ∧ Tendsto m atTop atTop := by
  refine ⟨CashInAdvance.PF.deflation_equilibrium hβ0 hβ1 hb.ge hM hP0 hcap, fun h => ?_⟩
  have := ((e13_iff_e17 hβ0 (by rw [hb]; exact hβ0) hθ hγ).2.1).mp h
  linarith

/-! ## Present values: the Regimes flow constraint and the CIA forward-iteration engine -/

/-- Cochrane (2023), (19.2), p. 434, and (19.28)–(19.30), p. 449: the valuation equation of
`Regimes` (stated there as a limit of partial sums, `Regimes.flow_pv_iff_tvc`) in `tsum` form:
given the flow constraint, bond pricing and adapted debt, and summable discounted flows, the
bond transversality condition holds iff `Λ_tB_{t−1}/P_t = ∑_j E_t[Λ_{t+j}(ΔM/P + s)_{t+j}]`.
This is the `CashInAdvance.Stochastic.pv_iff_tvc` engine applied to `Regimes`' recursion. -/
theorem flow_pv_tsum_iff_tvc {Ω : Type*} (𝔼 : ExpectationSystem Ω) (hPO : 𝔼.PullOut)
    {Λ P N i Bm Q s : ℕ → Ω → ℝ} (hBP : Regimes.BondPricing 𝔼 Λ P i)
    (hφ : ∀ t, 𝔼.E t (Λ t / P t) = Λ t / P t) (hBa : 𝔼.Adapted Bm)
    (hB : ∀ t, 𝔼.E t (Bm (t + 1)) = Bm (t + 1)) (hQ : ∀ t ω, Q t ω = 1 / (1 + i t ω))
    (hi : ∀ t ω, 1 + i t ω ≠ 0) (hP : ∀ t ω, P t ω ≠ 0) (hflow : Regimes.Flow Bm N P s Q)
    (t : ℕ) (ω : Ω)
    (hs : Summable fun j =>
      𝔼.E t (Λ (t + j) * ((N (t + j + 1) - N (t + j)) / P (t + j) + s (t + j))) ω) :
    Tendsto (fun T => 𝔼.E t (Λ (t + T) * Bm (t + T) / P (t + T)) ω) atTop (𝓝 0) ↔
      Λ t ω * Bm t ω / P t ω =
        ∑' j, 𝔼.E t (Λ (t + j) * ((N (t + j + 1) - N (t + j)) / P (t + j) + s (t + j))) ω := by
  set x : ℕ → Ω → ℝ := fun k => Λ k * Bm k / P k with hx
  set d : ℕ → Ω → ℝ := fun k => Λ k * ((N (k + 1) - N k) / P k + s k) with hd
  have hrec : ∀ k, x k = d k + 𝔼.E k (x (k + 1)) := fun k =>
    Regimes.flow_value_recursion 𝔼 hPO hBP hB hQ hi hP hflow k
  have hxa : 𝔼.Adapted x := fun k => by
    have h1 : x k = Bm k * (Λ k / P k) := by
      funext ω'
      simp only [hx, Pi.mul_apply, Pi.div_apply]
      ring
    rw [h1, hPO k _ _ (hBa k), hφ k]
  have hda : ∀ k, 𝔼.E k (d k) = d k := fun k => by
    have h1 : d k = x k - 𝔼.E k (x (k + 1)) := by rw [hrec k]; abel
    rw [h1, map_sub, hxa k, 𝔼.E_E_self]
  exact CashInAdvance.Stochastic.pv_iff_tvc 𝔼 (x := x) (g := d) (fun k => by rw [hrec k]; abel)
    hda t ω hs

/-! ## Optimality: shared concavity and finite-tree machinery -/

/-- Cochrane (2023), p. 453 ("first order conditions and transversality conditions are necessary
and sufficient") with footnote 1, p. 440: the cash-in-advance sufficiency theorem
`CashInAdvance.Euler.euler_sufficient` holds for any concave differentiable `u`, its
supporting-line hypothesis supplied by `MoneyInUtility.concave_le_tangent`. -/
theorem cia_euler_sufficient_of_concave {β W lam : ℝ} {u : ℝ → ℝ} {p c du : ℕ → ℝ}
    (hβ : 0 ≤ β) (hlam : 0 ≤ lam) (hconc : ConcaveOn ℝ Set.univ u)
    (hdu : ∀ τ, HasDerivAt u (du τ) (c τ)) (hfoc : ∀ τ, β ^ τ * du τ = lam * p τ)
    (hadm : CashInAdvance.Euler.Admissible β u p W c) (hbind : ∑' τ, p τ * c τ = W) :
    CashInAdvance.Euler.IsOptimalPlan β u p W c :=
  CashInAdvance.Euler.euler_sufficient hβ hlam
    (fun τ x => MoneyInUtility.concave_le_tangent hconc (hdu τ) x) hfoc hadm hbind

/-- Cochrane (2023), p. 453, under uncertainty (`CashInAdvance.TreeEuler.euler_sufficient`), with
footnote 1, p. 440: for concave differentiable `u` the supporting-line hypothesis holds at every
node (`MoneyInUtility.concave_le_tangent`). -/
theorem tree_euler_sufficient_of_concave {Ω : Type*} [Fintype Ω]
    (T : ExpectationsFiniteTree.FiniteTree Ω) {β W lam : ℝ} {u : ℝ → ℝ} {Λ c du : ℕ → Ω → ℝ}
    (hβ : 0 ≤ β) (hlam : 0 ≤ lam) (hconc : ConcaveOn ℝ Set.univ u)
    (hdu : ∀ τ ω, HasDerivAt u (du τ ω) (c τ ω)) (hfoc : ∀ τ ω, β ^ τ * du τ ω = lam * Λ τ ω)
    (hadm : CashInAdvance.TreeEuler.Admissible T β u Λ W c)
    (hbind : ∑' τ, CashInAdvance.TreeEuler.pvCost T Λ c τ = W) :
    CashInAdvance.TreeEuler.IsOptimal T β u Λ W c :=
  CashInAdvance.TreeEuler.euler_sufficient T hβ hlam
    (fun τ ω x => MoneyInUtility.concave_le_tangent hconc (hdu τ ω) x) hfoc hadm hbind

/-- Cochrane (2023), footnote 1, p. 440 (`c_t(x^t)`) and §19.5.1, p. 448: the two finite-tree
notions of a node-contingent plan, `CashInAdvance.TreeEuler.Meas` and
`MoneyInUtility.FootnoteTree.TAdapted`, coincide. -/
theorem meas_iff_tAdapted {Ω : Type*} [Fintype Ω] (T : ExpectationsFiniteTree.FiniteTree Ω)
    (x : ℕ → Ω → ℝ) :
    CashInAdvance.TreeEuler.Meas T x ↔ MoneyInUtility.FootnoteTree.TAdapted T x :=
  ⟨fun h t ω ω' hw => h t ω' ω hw, fun h t ω ω' hw => h t ω' ω hw⟩

/-! ## Discrete (19.13)–(19.16) and continuous-time (4.1)–(4.4) first-order conditions -/

/-- Cochrane (2023), eqs. (19.13)–(19.14), p. 440, give (19.16), p. 441, through the
continuous-time algebra of (4.2)/(4.4), p. 636: at an optimum of the footnote-1 problem
(`MoneyInUtility.foc_1913_1914`), `u_m/u_c = ι_t = i_t/(1 + i_t)`, which is
`ContinuousTime.foc_4_2` with discounting `β^t`, state price `q_t`, `P = 1` and `i^m = 0`. -/
theorem miu_foc_money_demand {β W : ℝ} {u uc um : ℝ → ℝ → ℝ} {q ι c m : ℕ → ℝ}
    (hβ : 0 < β) (hopt : MoneyInUtility.Optimal β u q ι W c m) (hq0 : q 0 = 1)
    (hq1 : 0 < q 1) (huc : ∀ k, HasDerivAt (fun x => u x (m k)) (uc (c k) (m k)) (c k))
    (hum : ∀ k, HasDerivAt (fun x => u (c k) x) (um (c k) (m k)) (m k)) (t : ℕ)
    (hu0 : uc (c t) (m t) ≠ 0) :
    um (c t) (m t) / uc (c t) (m t) = ι t := by
  obtain ⟨h1, h2⟩ := MoneyInUtility.foc_1913_1914 hopt hq0 hq1 huc hum t
  have h := ContinuousTime.foc_4_2 (pow_pos hβ t).ne' hu0 one_ne_zero h1
    (by rw [h2]; ring : β ^ t * um (c t) (m t) * (1 / 1) =
      uc (c 0) (m 0) * q t * (ι t - 0) * (1 / 1))
  rw [h, sub_zero]

/-- Cochrane (2023), eq. (19.13), p. 440, versus (4.1), p. 635: with `β = e^{−δ}` and state
prices `q_t = Λ_t/Λ_0 = e^{−R_t}` (`R_t` the cumulated real rate), the discrete first-order
condition `βᵗu_c(t) = λq_t` (`MoneyInUtility.foc_1913_1914`, `λ > 0`) says
`log u_c(t+1) − log u_c(t) = δ − (R_{t+1} − R_t)`, the discrete form of (4.1),
`d log u_c/dt = δ − r` (`ContinuousTime.foc_4_1`). -/
theorem miu_foc_log_growth {δ lam : ℝ} {R uct : ℕ → ℝ} (hlam : 0 < lam)
    (h : ∀ t, Real.exp (-δ) ^ t * uct t = lam * Real.exp (-R t)) (t : ℕ) :
    Real.log (uct (t + 1)) - Real.log (uct t) = δ - (R (t + 1) - R t) := by
  have e : ∀ k, uct k = lam * Real.exp (δ * k - R k) := by
    intro k
    have hk := h k
    rw [← Real.exp_nat_mul] at hk
    have hpos := Real.exp_pos (↑k * -δ)
    have e1 : Real.exp (δ * k - R k) = Real.exp (-R k) / Real.exp (↑k * -δ) := by
      rw [← Real.exp_sub]
      ring_nf
    rw [e1, mul_div_assoc', eq_div_iff hpos.ne', ← hk]
    ring
  rw [e (t + 1), e t, Real.log_mul hlam.ne' (Real.exp_pos _).ne',
    Real.log_mul hlam.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
  push_cast
  ring

/-- Cochrane (2023), (19.16), p. 441, and (4.2), p. 636 (`i^m = 0`), the continuous-time limit:
with period length `h` and `1 + i_h = e^{ih}`, the per-period interest cost of money
`ι_h = i_h/(1 + i_h) = 1 − e^{−ih}` per unit of time tends to the continuous-time rate `i`, so
the discrete `u_m/u_c = i/(1 + i)` (per period) becomes `u_m/u_c = i` (per unit time). -/
theorem interest_cost_continuous_limit (i : ℝ) :
    Tendsto (fun h => (1 - Real.exp (-(i * h))) / h) (𝓝[>] 0) (𝓝 i) := by
  have h1 : HasDerivAt (fun h : ℝ => -(i * h)) (-(i * 1)) 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_mul i).neg
  have hd : HasDerivAt (fun h : ℝ => 1 - Real.exp (-(i * h))) i 0 := by
    convert (h1.exp).const_sub 1 using 1
    simp
  refine (hd.tendsto_slope_zero_right).congr fun h => ?_
  simp only [zero_add, mul_zero, neg_zero, Real.exp_zero, sub_self, sub_zero, smul_eq_mul]
  ring

/-! ## CES money in utility: Online Appendix A3 (p. 632) and A4 (p. 636) -/

/-- Cochrane (2023), Online Appendix p. 632 versus p. 636: the A3 CES utility
`([c^ρ + θm^ρ]^{(1−γ)/ρ} − 1)/(1 − γ)` is the A4 CES utility
`[c^{1−θ'} + αm^{1−θ'}]^{(1−γ)/(1−θ')}/(1 − γ)` with `α = θ`, `θ' = 1 − ρ`, minus the constant
`1/(1 − γ)`. -/
theorem ces_nonsep_eq_ct (ρ θ γ c m : ℝ) :
    Nonseparable.cesU ρ θ γ c m = ContinuousTime.cesU θ (1 - ρ) γ c m - 1 / (1 - γ) := by
  unfold Nonseparable.cesU ContinuousTime.cesU ContinuousTime.cesX
  rw [sub_sub_cancel]
  ring

/-- Cochrane (2023), pp. 632 and 637: the A3 and A4 formulas for `u_c` agree
(`Nonseparable.ces_uc`, `ContinuousTime.hasDerivAt_cesU_c`, by uniqueness of the derivative). -/
theorem ces_uc_nonsep_eq_ct {ρ θ γ c m : ℝ} (hρ : ρ ≠ 0) (hγ : γ ≠ 1) (hθ : 0 < θ) (hc : 0 < c)
    (hm : 0 < m) :
    (c ^ ρ + θ * m ^ ρ) ^ ((1 - γ - ρ) / ρ) * c ^ (ρ - 1) =
      ContinuousTime.cesX θ (1 - ρ) c m ^ ((1 - ρ - γ) / (1 - (1 - ρ))) * c ^ (-(1 - ρ)) := by
  have h1 := Nonseparable.ces_uc hρ hγ hθ hc hm
  have h2 := (ContinuousTime.hasDerivAt_cesU_c (α := θ) (θ := 1 - ρ) (γ := γ) hθ.le hc hm
    (by intro h; exact hρ (by linarith)) hγ).sub_const (1 / (1 - γ))
  refine h1.unique ?_
  convert h2 using 1
  funext x
  exact ces_nonsep_eq_ct ρ θ γ x m

/-- Cochrane (2023), pp. 632 and 637: the A3 and A4 formulas for `u_m` agree
(`Nonseparable.ces_um`, `ContinuousTime.hasDerivAt_cesU_m`). -/
theorem ces_um_nonsep_eq_ct {ρ θ γ c m : ℝ} (hρ : ρ ≠ 0) (hγ : γ ≠ 1) (hθ : 0 < θ) (hc : 0 < c)
    (hm : 0 < m) :
    (c ^ ρ + θ * m ^ ρ) ^ ((1 - γ - ρ) / ρ) * (θ * m ^ (ρ - 1)) =
      ContinuousTime.cesX θ (1 - ρ) c m ^ ((1 - ρ - γ) / (1 - (1 - ρ))) *
        (θ * m ^ (-(1 - ρ))) := by
  have h1 := Nonseparable.ces_um hρ hγ hθ hc hm
  have h2 := (ContinuousTime.hasDerivAt_cesU_m (α := θ) (θ := 1 - ρ) (γ := γ) hθ.le hc hm
    (by intro h; exact hρ (by linarith)) hγ).sub_const (1 / (1 - γ))
  refine h1.unique ?_
  convert h2 using 1
  funext x
  exact ces_nonsep_eq_ct ρ θ γ c x

/-- Cochrane (2023), (4.8), p. 638, and (19.16)/(19.20), p. 443: the A4 money demand
`m/c = (1/α)^{−1/θ}(i − i^m)^{−1/θ}` (`ContinuousTime.demand_4_8`) is the inverse power demand
`(ι/α)^{−1/θ}` of `MoneyInUtility.power_demand_iff`. -/
theorem demand_4_8_eq_power_demand {α ι θ : ℝ} (hα : 0 < α) (hι : 0 < ι) :
    (1 / α) ^ (-(1 / θ)) * ι ^ (-(1 / θ)) = (ι / α) ^ (-(1 / θ)) := by
  rw [← Real.mul_rpow (by positivity) hι.le]
  congr 1
  ring

/-! ## Cagan money demand, seigniorage and fiscal selection -/

/-- Cochrane (2023), (19.4)–(19.5), p. 436, and p. 458: along a perfect-foresight Cagan path
with steady inflation `p_{t+1} = p_t + π`, velocity `Py/M = e^{p+y−m}` is `e^{a(r+π)}` (the
Cagan example `V(r + π) = e^{a(r+π)}` of `Seigniorage`), and seigniorage per unit of output
`π·M/(Py)` is `Seigniorage.cagRev a r π`. -/
theorem cagan_steady_revenue {a y r π : ℝ} {m p : ℕ → Unit → ℝ}
    (hC : CaganRE.Cagan perfectForesight a y r m p) (hπ : ∀ t, p (t + 1) () = p t () + π)
    (t : ℕ) :
    Real.exp (p t () + y - m t ()) = Real.exp (a * (r + π)) ∧
      π * Real.exp (m t () - p t () - y) = Seigniorage.cagRev a r π := by
  have h : m t () - p t () - y = -a * (r + p (t + 1) () - p t ()) := hC t ()
  rw [hπ t] at h
  have e1 : p t () + y - m t () = a * (r + π) := by linarith
  have e2 : m t () - p t () - y = -(a * (r + π)) := by linarith
  refine ⟨by rw [e1], ?_⟩
  rw [e2, Real.exp_neg, Seigniorage.cagRev, div_eq_mul_inv]

/-- Cochrane (2023), §19.1, p. 435 (survey NI-7) and pp. 437–438: in the Cagan model with
constant money `m̄`, the fiscally selected price path (`B_{−1}/P_0 = ∑βʲs_j = S`) is the bounded,
monetarist one exactly when monetary and fiscal policy are coordinated in the sense of
`Regimes.double_active_iff`: an active money supply `e^{m̄}` with velocity `e^{ar}` and an
active fiscal policy `(B, S)` have a common price level. -/
theorem cagan_ni7 {a y r mbar B S : ℝ} (ha : 0 < a) (hB : 0 < B) (hS : 0 < S)
    {p : ℕ → Unit → ℝ} (hp : CaganRE.Cagan perfectForesight a y r (fun _ _ => mbar) p)
    (hv : B / Real.exp (p 0 ()) = S) :
    BoundedProc p ↔ ∃ P : ℕ → Unit → ℝ,
      Regimes.MonetaryEqm (fun _ _ => Real.exp mbar) (fun _ _ => Real.exp (a * r))
        (fun _ _ => Real.exp y) P ∧ Regimes.Valuation (fun _ _ => B) (fun _ _ => S) P := by
  rw [CaganRE.fiscal_path_bounded_iff ha hB hS hp hv,
    Regimes.double_active_iff (fun _ _ => hB) (fun _ _ => hS)]
  unfold CaganRE.pbar
  rw [Real.exp_add, Real.exp_sub]
  have hy := Real.exp_pos y
  constructor
  · intro h _ _
    rw [h]
    field_simp
  · intro h
    have := h 0 ()
    field_simp
    linarith

/-- Cochrane (2023), (19.39)–(19.40), p. 456, and p. 458: the discrete seigniorage of
`UnpleasantArithmetic` with gross money growth `1 + n` and constant velocity, scaled by `1 + n`,
is output times the steady-state revenue `(π + g)/V` of `Seigniorage` at `π = n`, `g = 0`. -/
theorem seig_eq_revenue {y V n r : ℝ} (hn : 1 + n ≠ 0) :
    UnpleasantArithmetic.seig y V (1 + n) * (1 + n) =
      y * Seigniorage.revenue (fun _ => V) r 0 n := by
  unfold UnpleasantArithmetic.seig Seigniorage.revenue
  field_simp
  ring

/-- Cochrane (2023), §19.1, p. 435, and p. 453: under perfect foresight with a constant price
level `P_0` and target real debt `B/P_0`, the passive surplus rule of `Regimes`
(`s_t = W_t − βE_tW_{t+1}`) is the cash-in-advance passive surplus `(1 − β)B/P_0`. -/
theorem passiveSurplus_regimes_eq_cia (β B P0 : ℝ) (t : ℕ) :
    Regimes.passiveSurplus perfectForesight β (fun _ _ => B / P0) t =
      fun _ => CashInAdvance.PF.passiveSurplus β B (fun _ => P0) t := by
  funext u
  change B / P0 - β * (B / P0) = (1 - β) * B / P0
  ring

end Cochrane.Monetarism.Links
