/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.TidyR6ManagedSurplus
import FiscalConstraints.TidyR5GaussianAR1

/-!
# Does a managed surplus restore global determinacy? (the i.i.d. and AR(1) processes)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.1, p. 197: "As debt
starts to grow, the government increases surpluses so as to avoid the boundary. A higher value of
debt, induced by deflation, will push the government over the boundary absent a rise in future
surpluses. A plan that exceeds the bound by a finite amount will lead to an initial price-level
rise ... We are back to global determinacy of the price level and fiscal theory."

The book specifies no rule. We take the linear rule `s_t = s̄ + u_t + φ (x_t − b̄)` (the band
results hold for every `φ`; the one-sided results take `φ ≥ 0`) (`TidyR6ManagedSurplus.linRule`) and
its boundary-avoiding modification, on a genuine probability space: `(ℕ → ℝ, ν^ℕ)` of
`ExpectationsMeasureIID` with innovations `ε_t(ω) = ω_t`, `u = ExpectationsMeasureIID.ar1 ρ` an
AR(1) with `|ρ| < 1` (i.i.d. surpluses are `ρ = 0`, `ar1_zero`; Gaussian AR(1) as in
`TidyR5GaussianAR1`), permanent `r < g` (`0 < γ < 1`), and initial real debt `x₀ = B/(P₀ y₀)`.
Equilibrium (the book's criterion): debt stays within the limit forever, almost surely
(`Sustainable`, `IsEqmPrice`).

## Verdict

* **Sustainability: TRUE.** The modified rule keeps debt at or below `x̄` on every path, and is
  an adapted policy (`plan_adapted`); the unmodified rule does not (`linear_rule_not_sustainable`
  for `0 ≤ φ ≤ γ`, extended to every `φ > γ − 1` by
  `TidyR6LinearRuleBounds.linear_rule_zero_prob`).
* **Deflation is ruled out: TRUE.** If surpluses follow the plan (they do not respond to a
  revaluation of debt by the price level), every initial debt above the plan's `m₀` breaches the
  limit almost surely (`plan_hits`, `plan_sustainable_iff`): `P₀ < P* = B/(y₀ m₀)` is not an
  equilibrium, and `P*` is (existence).
* **Global determinacy (uniqueness): FALSE.** Every `P₀ ≥ P*` is an equilibrium: the equilibrium
  set is exactly `[P*, ∞)` (`plan_eqm_price_iff`, `plan_price_not_unique`). With an upper limit
  only, an initial debt below the plan just melts away (`r < g`). `P*` is the least equilibrium
  price (`plan_price_isLeast`): the book's "the price level rises until the government is again
  able to keep debt below the boundary" is a selection, not a consequence.
* **Feedback rules are worse.** If the rule responds to actual (revalued) debt, every
  `P₀ ≥ B/(y₀ x̄)` is an equilibrium (`feedback_price_iff`), and with a band every `P₀` in an
  interval (`band_feedback_price_iff`, `band_feedback_price_not_unique`).
* **Corrected statement (global determinacy, TRUE):** a two-sided plan, which also cuts surpluses
  to keep debt above a floor `x_{low}` (a band `[x_{low}, x̄]` around the target), with shocks that
  reach both edges (deficits and surpluses of every size, e.g. Gaussian), determines the price
  level uniquely: the only sustainable initial debt is `m₀` (`band_sustainable_iff`) and the
  equilibrium price level exists and is unique, `P₀ = B/(y₀ m₀)` (`band_eqm_price_unique`), for
  every response `φ`. Gaussian AR(1) summaries: `gaussian_plan_verdict`, `gaussian_band_verdict`.

The continuous-time Ornstein–Uhlenbeck surplus of p. 197 needs Itô calculus, which Mathlib lacks;
it is replaced by its discrete analogue, the Gaussian AR(1) (`ρ = e^{−η}` per period in
`TidyR5GaussianAR1.gaussian_ar1_exp_unbounded`).
-/

namespace Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure

open MeasureTheory ProbabilityTheory Filter
open ExpectationsMeasure ExpectationsMeasureIID DebtLimitStochastic DebtLimitStochasticMeasure
  LognormalGrowthMeasure TidyR5GaussianAR1 TidyR6ManagedSurplus

/-! ### Equilibrium notions -/

/-- Cochrane (2023), p. 197: initial debt `x₀` is sustainable under the surplus process `σ` if
debt stays at or below the limit `x̄` at every date, almost surely. -/
def Sustainable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (γ xbar : ℝ) (σ : ℕ → Ω → ℝ)
    (x₀ : ℝ) : Prop :=
  ∀ᵐ ω ∂μ, ∀ t, debtPath γ x₀ σ t ω ≤ xbar

/-- Cochrane (2023), p. 197: initial debt `x₀` is sustainable in the band `[x_{low}, x̄]` under
`σ` if debt stays in the band at every date, almost surely. -/
def BandSustainable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (γ xlow xbar : ℝ)
    (σ : ℕ → Ω → ℝ) (x₀ : ℝ) : Prop :=
  ∀ᵐ ω ∂μ, ∀ t, xlow ≤ debtPath γ x₀ σ t ω ∧ debtPath γ x₀ σ t ω ≤ xbar

/-- Cochrane (2023), p. 197: `P₀` is an equilibrium price level for the surplus plan `σ`, given
nominal debt `B` and GDP `y₀`, if `P₀ > 0` and the initial debt `B/(P₀ y₀)` is sustainable. -/
def IsEqmPrice {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (γ xbar : ℝ) (σ : ℕ → Ω → ℝ)
    (B y₀ P₀ : ℝ) : Prop :=
  0 < P₀ ∧ Sustainable μ γ xbar σ (B / (P₀ * y₀))

/-- Cochrane (2023), p. 197: `P₀` is an equilibrium price level for the plan `σ` with the band
`[x_{low}, x̄]`. -/
def IsBandEqmPrice {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (γ xlow xbar : ℝ)
    (σ : ℕ → Ω → ℝ) (B y₀ P₀ : ℝ) : Prop :=
  0 < P₀ ∧ BandSustainable μ γ xlow xbar σ (B / (P₀ * y₀))

/-- Cochrane (2023), p. 197: `P₀` is an equilibrium price level under the boundary-avoiding
modification of the feedback rule `F`, which responds to the actual debt `B/(P₀ y₀)`. -/
def IsFeedbackEqmPrice {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (γ xbar : ℝ)
    (F : ℕ → ℝ → Ω → ℝ) (B y₀ P₀ : ℝ) : Prop :=
  0 < P₀ ∧ ∀ᵐ ω ∂μ, ∀ t, avoidPath γ xbar F (B / (P₀ * y₀)) t ω ≤ xbar

/-- Cochrane (2023), p. 197: `P₀` is an equilibrium price level under the two-sided
modification of the feedback rule `F`. -/
def IsBandFeedbackEqmPrice {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (γ xlow xbar : ℝ)
    (F : ℕ → ℝ → Ω → ℝ) (B y₀ P₀ : ℝ) : Prop :=
  0 < P₀ ∧ ∀ᵐ ω ∂μ, ∀ t, xlow ≤ bandPath γ xlow xbar F (B / (P₀ * y₀)) t ω ∧
    bandPath γ xlow xbar F (B / (P₀ * y₀)) t ω ≤ xbar

/-! ### The surplus process -/

/-- Cochrane (2023), p. 197: i.i.d. surplus shocks are the AR(1) with `ρ = 0`: `u_t = ε_t`. -/
theorem ar1_zero (t : ℕ) (ω : ℕ → ℝ) : ar1 0 t ω = ω t := by
  cases t with
  | zero => rfl
  | succ t =>
    change 0 * ar1 0 t ω + ω (t + 1) = ω (t + 1)
    ring

/-- Cochrane (2023), p. 197: the linear rule with i.i.d. shocks is the linear rule with the
`ρ = 0` AR(1). -/
theorem linRule_shock (sbar φ bbar : ℝ) :
    linRule sbar φ bbar shock = linRule sbar φ bbar (ar1 0) := by
  funext t x ω
  simp only [linRule, ar1_zero]
  rfl

/-- Cochrane (2023), p. 197: under the unmodified linear rule with AR(1) shocks, debt is the
debt of `DebtLimitStochastic.debtPath` with root `γ − φ` and AR(1) surplus around `s̄ − φ b̄`. -/
theorem rulePath_linRule (γ sbar φ bbar ρ x₀ : ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    rulePath γ (linRule sbar φ bbar (ar1 ρ)) x₀ t ω =
      debtPath (γ - φ) x₀ (arSurplus ρ (sbar - φ * bbar)) t ω := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change γ * rulePath γ (linRule sbar φ bbar (ar1 ρ)) x₀ t ω -
      linRule sbar φ bbar (ar1 ρ) t (rulePath γ (linRule sbar φ bbar (ar1 ρ)) x₀ t ω) ω = _
    rw [linRule_response, ih, debtPath_succ, arSurplus]

variable {ν : ProbabilityMeasure ℝ}

variable (ν) in
/-- Cochrane (2023), p. 197 ("we must already imagine a managed surplus process"): the
boundary-avoiding linear plan is an adapted policy: next period's debt `m_{t+1}` and the
surplus `σ_t` are known at date `t`. -/
theorem plan_adapted (γ xbar sbar φ bbar ρ m₀ : ℝ) (t : ℕ) :
    Measurable[(iidSystem ν).𝓕 t] (avoidPath γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀ (t + 1)) ∧
      Measurable[(iidSystem ν).𝓕 t] (avoidSurplus γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀ t) := by
  set F := linRule sbar φ bbar (ar1 ρ) with hF
  have hx : ∀ t, Measurable[(iidSystem ν).𝓕 t] (avoidPath γ xbar F m₀ t) := by
    intro t
    induction t with
    | zero => exact measurable_const
    | succ t ih =>
      have ih' := ih.mono ((iidSystem ν).𝓕.mono (Nat.le_succ t)) le_rfl
      have hu := (measurable_ar1_F ν ρ t).mono ((iidSystem ν).𝓕.mono (Nat.le_succ t)) le_rfl
      have hf : avoidPath γ xbar F m₀ (t + 1) = fun ω => min xbar
          (γ * avoidPath γ xbar F m₀ t ω -
            (sbar + ar1 ρ t ω + φ * (avoidPath γ xbar F m₀ t ω - bbar))) := rfl
      rw [hf]
      exact measurable_const.min ((ih'.const_mul γ).sub
        ((hu.const_add sbar).add ((ih'.sub_const bbar).const_mul φ)))
  have hu := measurable_ar1_F ν ρ t
  have hFt : Measurable[(iidSystem ν).𝓕 t] (fun ω => F t (avoidPath γ xbar F m₀ t ω) ω) :=
    (hu.const_add sbar).add (((hx t).sub_const bbar).const_mul φ)
  refine ⟨?_, ?_⟩
  · have hf : avoidPath γ xbar F m₀ (t + 1) = fun ω => min xbar
        (γ * avoidPath γ xbar F m₀ t ω - F t (avoidPath γ xbar F m₀ t ω) ω) := rfl
    rw [hf]
    exact measurable_const.min (((hx t).const_mul γ).sub hFt)
  · exact hFt.add (measurable_const.max ((((hx t).const_mul γ).sub hFt).sub measurable_const))

variable (ν) in
/-- Cochrane (2023), p. 197: the two-sided linear plan is an adapted policy as well. -/
theorem band_plan_adapted (γ xlow xbar sbar φ bbar ρ m₀ : ℝ) (t : ℕ) :
    Measurable[(iidSystem ν).𝓕 t]
        (bandPath γ xlow xbar (linRule sbar φ bbar (ar1 ρ)) m₀ (t + 1)) ∧
      Measurable[(iidSystem ν).𝓕 t]
        (bandSurplus γ xlow xbar (linRule sbar φ bbar (ar1 ρ)) m₀ t) := by
  set F := linRule sbar φ bbar (ar1 ρ) with hF
  have hx : ∀ t, Measurable[(iidSystem ν).𝓕 t] (bandPath γ xlow xbar F m₀ t) := by
    intro t
    induction t with
    | zero => exact measurable_const
    | succ t ih =>
      have ih' := ih.mono ((iidSystem ν).𝓕.mono (Nat.le_succ t)) le_rfl
      have hu := (measurable_ar1_F ν ρ t).mono ((iidSystem ν).𝓕.mono (Nat.le_succ t)) le_rfl
      have hf : bandPath γ xlow xbar F m₀ (t + 1) = fun ω => max xlow (min xbar
          (γ * bandPath γ xlow xbar F m₀ t ω -
            (sbar + ar1 ρ t ω + φ * (bandPath γ xlow xbar F m₀ t ω - bbar)))) := rfl
      rw [hf]
      exact measurable_const.max (measurable_const.min ((ih'.const_mul γ).sub
        ((hu.const_add sbar).add ((ih'.sub_const bbar).const_mul φ))))
  have hu := measurable_ar1_F ν ρ t
  have hFt : Measurable[(iidSystem ν).𝓕 t] (fun ω => F t (bandPath γ xlow xbar F m₀ t ω) ω) :=
    (hu.const_add sbar).add (((hx t).sub_const bbar).const_mul φ)
  have hy : Measurable[(iidSystem ν).𝓕 t]
      (fun ω => γ * bandPath γ xlow xbar F m₀ t ω - F t (bandPath γ xlow xbar F m₀ t ω) ω) :=
    ((hx t).const_mul γ).sub hFt
  refine ⟨?_, ?_⟩
  · have hf : bandPath γ xlow xbar F m₀ (t + 1) = fun ω => max xlow (min xbar
        (γ * bandPath γ xlow xbar F m₀ t ω - F t (bandPath γ xlow xbar F m₀ t ω) ω)) := rfl
    rw [hf]
    exact measurable_const.max (measurable_const.min hy)
  · exact (hFt.add (measurable_const.max (hy.sub measurable_const))).sub
      (measurable_const.max (measurable_const.sub (measurable_const.min hy)))

/-! ### Shocks of every size recur -/

/-- Cochrane (2023), p. 197: with integrable i.i.d. innovations putting mass on deficits of every
size and `|ρ| < 1`, almost surely the AR(1) falls below every level infinitely often (the
debt theorem `TidyR5GaussianAR1.ar1_unbounded_of_integrable` at `γ = 0`). -/
theorem ar1_frequently_le (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) {ρ : ℝ} (hρ : |ρ| < 1) :
    ∀ᵐ ω ∂(iidSystem ν).μ, ∀ K : ℝ, ∃ᶠ t in atTop, ar1 ρ t ω ≤ K := by
  have h := ar1_unbounded_of_integrable hint hdef (γ := 0) le_rfl zero_lt_one hρ 0 0
  filter_upwards [h] with ω hω K
  have h1 := (frequently_shift_iff 1).1 (hω (-K))
  refine h1.mono fun k hk => ?_
  rw [show 1 + k = k + 1 from Nat.add_comm 1 k, debtPath_succ, arSurplus] at hk
  linarith

/-- Cochrane (2023), p. 197: the law of `−ε` (the mirror image of the innovation law). -/
noncomputable def negLaw (ν : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  ν.map fun x => -x

/-- Cochrane (2023), p. 197: flipping the sign of every innovation maps `ν^ℕ` to
`(negLaw ν)^ℕ`. -/
theorem map_neg_iid (ν : ProbabilityMeasure ℝ) :
    (iidSystem ν).μ.map (fun ω i => -ω i) = (iidSystem (negLaw ν)).μ := by
  change (Measure.infinitePi fun _ => (ν : Measure ℝ)).map (fun ω i => -ω i) =
    Measure.infinitePi fun _ => ((negLaw ν : ProbabilityMeasure ℝ) : Measure ℝ)
  rw [Measure.infinitePi_map_pi _ (f := fun _ x => -x) (fun _ => measurable_neg)]
  rfl

/-- Cochrane (2023), p. 197: the AR(1) driven by `−ε` is `−u`. -/
theorem ar1_neg (ρ : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ar1 ρ t (fun i => -ω i) = -ar1 ρ t ω := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change ρ * ar1 ρ t (fun i => -ω i) + -ω (t + 1) = -(ρ * ar1 ρ t ω + ω (t + 1))
    rw [ih]
    ring

/-- Cochrane (2023), p. 197: with integrable i.i.d. innovations putting mass on surpluses of
every size and `|ρ| < 1`, almost surely the AR(1) rises above every level infinitely often. -/
theorem ar1_frequently_ge (hint : Integrable id (ν : Measure ℝ))
    (hup : ∀ c : ℝ, (ν : Measure ℝ) (Set.Ici c) ≠ 0) {ρ : ℝ} (hρ : |ρ| < 1) :
    ∀ᵐ ω ∂(iidSystem ν).μ, ∀ K : ℝ, ∃ᶠ t in atTop, K ≤ ar1 ρ t ω := by
  have hint' : Integrable id ((negLaw ν : ProbabilityMeasure ℝ) : Measure ℝ) := by
    change Integrable id ((ν : Measure ℝ).map fun x => -x)
    rw [integrable_map_measure measurable_id.aestronglyMeasurable measurable_neg.aemeasurable]
    exact hint.neg
  have hdef' : ∀ c : ℝ, ((negLaw ν : ProbabilityMeasure ℝ) : Measure ℝ) (Set.Iic (-c)) ≠ 0 := by
    intro c
    change ((ν : Measure ℝ).map fun x => -x) (Set.Iic (-c)) ≠ 0
    rw [Measure.map_apply measurable_neg measurableSet_Iic]
    have e : (fun x : ℝ => -x) ⁻¹' Set.Iic (-c) = Set.Ici c := by
      ext x
      simp
    rw [e]
    exact hup c
  have h := ar1_frequently_le hint' hdef' hρ
  rw [← map_neg_iid] at h
  have hm : Measurable fun (ω : ℕ → ℝ) (i : ℕ) => -ω i :=
    measurable_pi_iff.mpr fun i => (measurable_pi_apply i).neg
  filter_upwards [ae_of_ae_map hm.aemeasurable h] with ω hω K
  refine (hω (-K)).mono fun t ht => ?_
  rw [ar1_neg] at ht
  linarith

/-! ### The plan touches the limit -/

/-- Cochrane (2023), p. 197: with integrable i.i.d. innovations with deficits of every size,
`|ρ| < 1`, `γ < 1` and any response `φ ≥ 0`, the boundary-avoiding linear plan almost surely
touches the limit `x̄` at some date. For `γ − φ ≥ 0` the unmodified rule would be a.s. unbounded
(`TidyR5GaussianAR1.ar1_unbounded_of_integrable`), and the plan meets `x̄` where the rule first
crosses it; for `γ − φ < 0` a large enough deficit shock carries the plan to `x̄` directly. -/
theorem plan_hits (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) {ρ γ φ : ℝ} (hρ : |ρ| < 1)
    (hγ1 : γ < 1) (hφ : 0 ≤ φ) (sbar bbar xbar m₀ : ℝ) :
    ∀ᵐ ω ∂(iidSystem ν).μ, ∃ t,
      avoidPath γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀ t ω = xbar := by
  rcases le_or_gt 0 (γ - φ) with ha | ha
  · have h := ar1_unbounded_of_integrable hint hdef (γ := γ - φ) ha (by linarith) hρ m₀
      (sbar - φ * bbar)
    filter_upwards [h] with ω hω
    obtain ⟨t, ht, ht1⟩ := ((hω xbar).and_eventually (eventually_ge_atTop 1)).exists
    have hr : ∃ t, 1 ≤ t ∧ xbar ≤ rulePath γ (linRule sbar φ bbar (ar1 ρ)) m₀ t ω :=
      ⟨t, ht1, by rw [rulePath_linRule]; exact ht.le⟩
    obtain ⟨s, -, hs⟩ := avoid_hits_of_rule_exceeds hr
    exact ⟨s, hs⟩
  · filter_upwards [ar1_frequently_le hint hdef hρ] with ω hω
    obtain ⟨t, ht, ht1⟩ := ((hω ((γ - φ - 1) * xbar - (sbar - φ * bbar))).and_eventually
      (eventually_ge_atTop 1)).exists
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    refine ⟨s + 1 + 1, avoidPath_succ_eq_xbar ?_⟩
    rw [linRule_response]
    have hm := avoidPath_le γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀ s ω
    have h1 := mul_le_mul_of_nonpos_left hm ha.le
    linarith

/-- Cochrane (2023), p. 197: with integrable i.i.d. innovations with deficits AND surpluses of
every size and `|ρ| < 1`, the two-sided linear plan from `m₀ ∈ [x_{low}, x̄]` almost surely touches
both edges of the band, for every response `φ` and every `γ`. -/
theorem band_hits (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0)
    (hup : ∀ c : ℝ, (ν : Measure ℝ) (Set.Ici c) ≠ 0) {ρ γ φ xlow xbar m₀ : ℝ} (hρ : |ρ| < 1)
    (hl : xlow ≤ xbar) (hm₀ : xlow ≤ m₀ ∧ m₀ ≤ xbar) (sbar bbar : ℝ) :
    ∀ᵐ ω ∂(iidSystem ν).μ,
      (∃ t, bandPath γ xlow xbar (linRule sbar φ bbar (ar1 ρ)) m₀ t ω = xbar) ∧
      ∃ t, bandPath γ xlow xbar (linRule sbar φ bbar (ar1 ρ)) m₀ t ω = xlow := by
  filter_upwards [ar1_frequently_le hint hdef hρ, ar1_frequently_ge hint hup hρ] with ω hle hge
  set a := γ - φ
  set c := sbar - φ * bbar
  constructor
  · obtain ⟨t, ht⟩ := (hle (min (a * xlow) (a * xbar) - c - xbar)).exists
    refine ⟨t + 1, bandPath_succ_eq_xbar hl ?_⟩
    rw [linRule_response]
    have hb := bandPath_mem_all (γ := γ) hl hm₀ (linRule sbar φ bbar (ar1 ρ)) ω t
    have hmm := (mul_mem_minmax (a := a) hb.1 hb.2).1
    linarith
  · obtain ⟨t, ht⟩ := (hge (max (a * xlow) (a * xbar) - c - xlow)).exists
    refine ⟨t + 1, bandPath_succ_eq_xlow ?_⟩
    rw [linRule_response]
    have hb := bandPath_mem_all (γ := γ) hl hm₀ (linRule sbar φ bbar (ar1 ρ)) ω t
    have hmm := (mul_mem_minmax (a := a) hb.1 hb.2).2
    linarith

/-! ### One-sided plans: deflation is ruled out, inflation is not -/

/-- **Managed surplus, one-sided limit** (Cochrane (2023), p. 197). With i.i.d. integrable
innovations with deficits of every size, `|ρ| < 1`, `0 < γ < 1` (`r < g`), any response `φ ≥ 0`
and a plan from `m₀ ≤ x̄`: initial debt `x₀` is sustainable under the boundary-avoiding plan iff
`x₀ ≤ m₀`. A deflation (`x₀ > m₀`) breaches the limit almost surely; any inflation (`x₀ < m₀`)
is sustained on every path. -/
theorem plan_sustainable_iff (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) {ρ γ φ : ℝ} (hρ : |ρ| < 1)
    (hγ : 0 < γ) (hγ1 : γ < 1) (hφ : 0 ≤ φ) {sbar bbar xbar m₀ : ℝ} (hm₀ : m₀ ≤ xbar) (x₀ : ℝ) :
    Sustainable (iidSystem ν).μ γ xbar (avoidSurplus γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀) x₀ ↔
      x₀ ≤ m₀ := by
  set F := linRule sbar φ bbar (ar1 ρ) with hF
  constructor
  · intro h
    by_contra hx
    rw [not_le] at hx
    obtain ⟨ω, hω, t, ht⟩ := (h.and (plan_hits hint hdef hρ hγ1 hφ sbar bbar xbar m₀)).exists
    exact absurd (hω t) (not_le.2 (plan_breach_high hγ
      (fun s => avoidPath_succ_eq γ xbar F m₀ s ω) hx ht))
  · intro hx
    exact Eventually.of_forall fun ω t => plan_within_of_le hγ.le
      (fun s => avoidPath_succ_eq γ xbar F m₀ s ω)
      (fun s => (avoidPath_within_iff γ xbar F m₀ ω).2 hm₀ s) hx t

/-- **The equilibrium price levels under a one-sided managed plan** (Cochrane (2023), p. 197):
with nominal debt `B > 0`, GDP `y₀ > 0` and a plan from `0 < m₀ ≤ x̄`, `P₀` is an equilibrium
price level iff `P₀ ≥ P* = B/(y₀ m₀)`. -/
theorem plan_eqm_price_iff (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) {ρ γ φ : ℝ} (hρ : |ρ| < 1)
    (hγ : 0 < γ) (hγ1 : γ < 1) (hφ : 0 ≤ φ) {sbar bbar xbar m₀ B y₀ : ℝ} (hB : 0 < B)
    (hy : 0 < y₀) (hm₀p : 0 < m₀) (hm₀ : m₀ ≤ xbar) (P₀ : ℝ) :
    IsEqmPrice (iidSystem ν).μ γ xbar (avoidSurplus γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀)
        B y₀ P₀ ↔ B / (y₀ * m₀) ≤ P₀ := by
  constructor
  · rintro ⟨hP, hS⟩
    exact (debt_le_iff_price_ge hy hP hm₀p).1
      ((plan_sustainable_iff hint hdef hρ hγ hγ1 hφ hm₀ _).1 hS)
  · intro hP
    have hP0 : 0 < P₀ := (div_pos hB (mul_pos hy hm₀p)).trans_le hP
    exact ⟨hP0, (plan_sustainable_iff hint hdef hρ hγ hγ1 hφ hm₀ _).2
      ((debt_le_iff_price_ge hy hP0 hm₀p).2 hP)⟩

/-- Cochrane (2023), p. 197 ("a plan that exceeds the bound by a finite amount will lead to an
initial price-level rise ... until the government is again able to keep debt below the
boundary"): `P* = B/(y₀ m₀)` is the LEAST equilibrium price level. -/
theorem plan_price_isLeast (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) {ρ γ φ : ℝ} (hρ : |ρ| < 1)
    (hγ : 0 < γ) (hγ1 : γ < 1) (hφ : 0 ≤ φ) {sbar bbar xbar m₀ B y₀ : ℝ} (hB : 0 < B)
    (hy : 0 < y₀) (hm₀p : 0 < m₀) (hm₀ : m₀ ≤ xbar) :
    IsLeast {P₀ | IsEqmPrice (iidSystem ν).μ γ xbar
      (avoidSurplus γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀) B y₀ P₀} (B / (y₀ * m₀)) :=
  ⟨(plan_eqm_price_iff hint hdef hρ hγ hγ1 hφ hB hy hm₀p hm₀ _).2 le_rfl,
    fun _ hP => (plan_eqm_price_iff hint hdef hρ hγ hγ1 hφ hB hy hm₀p hm₀ _).1 hP⟩

/-- **Correction** (Cochrane (2023), p. 197, "we are back to global determinacy of the price
level"): under a one-sided managed plan the equilibrium price level is NOT unique: `P*` and
`2 P*` are both equilibria. Only deflation is ruled out. -/
theorem plan_price_not_unique (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) {ρ γ φ : ℝ} (hρ : |ρ| < 1)
    (hγ : 0 < γ) (hγ1 : γ < 1) (hφ : 0 ≤ φ) {sbar bbar xbar m₀ B y₀ : ℝ} (hB : 0 < B)
    (hy : 0 < y₀) (hm₀p : 0 < m₀) (hm₀ : m₀ ≤ xbar) :
    ¬ ∃! P₀, IsEqmPrice (iidSystem ν).μ γ xbar
      (avoidSurplus γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀) B y₀ P₀ := by
  rintro ⟨P, -, hu⟩
  have hpos : 0 < B / (y₀ * m₀) := div_pos hB (mul_pos hy hm₀p)
  have h1 := hu _ ((plan_eqm_price_iff hint hdef hρ hγ hγ1 hφ hB hy hm₀p hm₀ _).2 le_rfl)
  have h2 := hu (2 * (B / (y₀ * m₀)))
    ((plan_eqm_price_iff hint hdef hρ hγ hγ1 hφ hB hy hm₀p hm₀ _).2 (by linarith))
  linarith

/-! ### Two-sided plans: global determinacy -/

/-- **Managed surplus, two-sided band: global determinacy** (Cochrane (2023), p. 197,
corrected). With i.i.d. integrable innovations with deficits and surpluses of every size,
`|ρ| < 1`, `0 < γ`, any response `φ`, a band `x_{low} ≤ x̄` and a plan from `m₀` in the band: the
only initial debt sustainable in the band under the plan is `x₀ = m₀`. -/
theorem band_sustainable_iff (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0)
    (hup : ∀ c : ℝ, (ν : Measure ℝ) (Set.Ici c) ≠ 0) {ρ γ φ xlow xbar m₀ : ℝ} (hρ : |ρ| < 1)
    (hγ : 0 < γ) (hl : xlow ≤ xbar) (hm₀ : xlow ≤ m₀ ∧ m₀ ≤ xbar) (sbar bbar x₀ : ℝ) :
    BandSustainable (iidSystem ν).μ γ xlow xbar
      (bandSurplus γ xlow xbar (linRule sbar φ bbar (ar1 ρ)) m₀) x₀ ↔ x₀ = m₀ := by
  set F := linRule sbar φ bbar (ar1 ρ) with hF
  constructor
  · intro h
    obtain ⟨ω, hω, ⟨t₁, h₁⟩, ⟨t₂, h₂⟩⟩ :=
      (h.and (band_hits (φ := φ) (γ := γ) hint hdef hup hρ hl hm₀ sbar bbar)).exists
    have hm := fun s => bandPath_succ_eq γ xlow xbar F m₀ s ω
    rcases lt_trichotomy x₀ m₀ with hx | hx | hx
    · exact absurd (hω t₂).1 (not_le.2 (plan_breach_low hγ hm hx h₂))
    · exact hx
    · exact absurd (hω t₁).2 (not_le.2 (plan_breach_high hγ hm hx h₁))
  · rintro rfl
    refine Eventually.of_forall fun ω t => ?_
    rw [band_plan_debtPath, sub_self, mul_zero, add_zero]
    exact bandPath_mem_all hl hm₀ F ω t

/-- **Existence and uniqueness of the equilibrium price level under a two-sided managed plan**
(Cochrane (2023), p. 197, corrected): with `B > 0`, `y₀ > 0` and a plan from `m₀ > 0` in the
band, there is exactly one equilibrium price level, `P₀ = B/(y₀ m₀)`. -/
theorem band_eqm_price_unique (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0)
    (hup : ∀ c : ℝ, (ν : Measure ℝ) (Set.Ici c) ≠ 0) {ρ γ φ xlow xbar m₀ B y₀ : ℝ}
    (hρ : |ρ| < 1) (hγ : 0 < γ) (hl : xlow ≤ xbar) (hm₀ : xlow ≤ m₀ ∧ m₀ ≤ xbar) (hB : 0 < B)
    (hy : 0 < y₀) (hm₀p : 0 < m₀) (sbar bbar : ℝ) :
    ∃! P₀, IsBandEqmPrice (iidSystem ν).μ γ xlow xbar
      (bandSurplus γ xlow xbar (linRule sbar φ bbar (ar1 ρ)) m₀) B y₀ P₀ := by
  obtain ⟨hpos, hspec⟩ := price_spec hB hy hm₀p
  refine ⟨B / (y₀ * m₀), ⟨hpos, ?_⟩, ?_⟩
  · rw [hspec]
    exact (band_sustainable_iff hint hdef hup hρ hγ hl hm₀ sbar bbar _).2 rfl
  · rintro P ⟨hP, hS⟩
    exact (debt_eq_iff_price_eq hy hP hm₀p).1
      ((band_sustainable_iff hint hdef hup hρ hγ hl hm₀ sbar bbar _).1 hS)

/-! ### Feedback rules: no determinacy -/

/-- Cochrane (2023), p. 197: on any probability space, under the boundary-avoiding modification
of ANY feedback rule, initial debt is sustainable iff `x₀ ≤ x̄`. -/
theorem feedback_sustainable_iff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (γ xbar : ℝ) (F : ℕ → ℝ → Ω → ℝ) (x₀ : ℝ) :
    (∀ᵐ ω ∂μ, ∀ t, avoidPath γ xbar F x₀ t ω ≤ xbar) ↔ x₀ ≤ xbar := by
  constructor
  · intro h
    obtain ⟨ω, hω⟩ := h.exists
    exact (avoidPath_within_iff γ xbar F x₀ ω).1 hω
  · intro hx
    exact Eventually.of_forall fun ω => (avoidPath_within_iff γ xbar F x₀ ω).2 hx

/-- **Correction** (Cochrane (2023), p. 197): if the managed surplus responds to the actual,
revalued debt, the equilibrium price levels are exactly `P₀ ≥ B/(y₀ x̄)`, for any rule `F` on
any probability space (`B > 0`, `y₀ > 0`, `x̄ > 0`). -/
theorem feedback_price_iff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (γ : ℝ) (F : ℕ → ℝ → Ω → ℝ) {xbar B y₀ : ℝ} (hB : 0 < B)
    (hy : 0 < y₀) (hx : 0 < xbar) (P₀ : ℝ) :
    IsFeedbackEqmPrice μ γ xbar F B y₀ P₀ ↔ B / (y₀ * xbar) ≤ P₀ := by
  constructor
  · rintro ⟨hP, hS⟩
    exact (debt_le_iff_price_ge hy hP hx).1 ((feedback_sustainable_iff μ γ xbar F _).1 hS)
  · intro hP
    have hP0 : 0 < P₀ := (div_pos hB (mul_pos hy hx)).trans_le hP
    exact ⟨hP0, (feedback_sustainable_iff μ γ xbar F _).2
      ((debt_le_iff_price_ge hy hP0 hx).2 hP)⟩

/-- **Correction** (Cochrane (2023), p. 197): under a boundary-avoiding feedback rule the
equilibrium price level is not unique. -/
theorem feedback_price_not_unique {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (γ : ℝ) (F : ℕ → ℝ → Ω → ℝ) {xbar B y₀ : ℝ} (hB : 0 < B)
    (hy : 0 < y₀) (hx : 0 < xbar) :
    ¬ ∃! P₀, IsFeedbackEqmPrice μ γ xbar F B y₀ P₀ := by
  rintro ⟨P, -, hu⟩
  have hpos : 0 < B / (y₀ * xbar) := div_pos hB (mul_pos hy hx)
  have h1 := hu _ ((feedback_price_iff μ γ F hB hy hx _).2 le_rfl)
  have h2 := hu (2 * (B / (y₀ * xbar))) ((feedback_price_iff μ γ F hB hy hx _).2 (by linarith))
  linarith

/-- Cochrane (2023), p. 197: under the two-sided modification of ANY feedback rule, on any
probability space, the equilibrium price levels are exactly
`B/(y₀ x̄) ≤ P₀ ≤ B/(y₀ x_{low})` (`0 < x_{low} ≤ x̄`, `B > 0`, `y₀ > 0`). -/
theorem band_feedback_price_iff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (γ : ℝ) (F : ℕ → ℝ → Ω → ℝ) {xlow xbar B y₀ : ℝ} (hB : 0 < B)
    (hy : 0 < y₀) (hlow : 0 < xlow) (hl : xlow ≤ xbar) (P₀ : ℝ) :
    IsBandFeedbackEqmPrice μ γ xlow xbar F B y₀ P₀ ↔
      B / (y₀ * xbar) ≤ P₀ ∧ P₀ ≤ B / (y₀ * xlow) := by
  have hxbar : 0 < xbar := hlow.trans_le hl
  constructor
  · rintro ⟨hP, hS⟩
    obtain ⟨ω, hω⟩ := hS.exists
    have h0 := (bandPath_within_iff hl F _ ω).1 hω
    exact ⟨(debt_le_iff_price_ge hy hP hxbar).1 h0.2, (le_debt_iff_price_le hy hP hlow).1 h0.1⟩
  · rintro ⟨h1, h2⟩
    have hP0 : 0 < P₀ := (div_pos hB (mul_pos hy hxbar)).trans_le h1
    refine ⟨hP0, Eventually.of_forall fun ω => (bandPath_within_iff hl F _ ω).2 ⟨?_, ?_⟩⟩
    · exact (le_debt_iff_price_le hy hP0 hlow).2 h2
    · exact (debt_le_iff_price_ge hy hP0 hxbar).2 h1

/-- **Correction** (Cochrane (2023), p. 197): even with a band, a feedback rule leaves the price
level indeterminate when `0 < x_{low} < x̄`: `B/(y₀ x̄)` and `B/(y₀ x_{low})` are distinct
equilibrium price levels. -/
theorem band_feedback_price_not_unique {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (γ : ℝ) (F : ℕ → ℝ → Ω → ℝ) {xlow xbar B y₀ : ℝ} (hB : 0 < B)
    (hy : 0 < y₀) (hlow : 0 < xlow) (hl : xlow < xbar) :
    ¬ ∃! P₀, IsBandFeedbackEqmPrice μ γ xlow xbar F B y₀ P₀ := by
  rintro ⟨P, -, hu⟩
  have hxbar : 0 < xbar := hlow.trans hl
  have hlt : B / (y₀ * xbar) < B / (y₀ * xlow) :=
    div_lt_div_of_pos_left hB (mul_pos hy hlow) (mul_lt_mul_of_pos_left hl hy)
  have h1 := hu (B / (y₀ * xbar))
    ((band_feedback_price_iff μ γ F hB hy hlow hl.le _).2 ⟨le_rfl, hlt.le⟩)
  have h2 := hu (B / (y₀ * xlow))
    ((band_feedback_price_iff μ γ F hB hy hlow hl.le _).2 ⟨hlt.le, le_rfl⟩)
  linarith

/-! ### Without the modification: Theorem S persists -/

/-- Cochrane (2023), p. 197: the UNMODIFIED linear rule with a response `0 ≤ φ ≤ γ < 1` does
not make any debt sustainable: with i.i.d. integrable innovations with deficits of every size
and `|ρ| < 1`, for every initial debt `x₀` and every limit `x̄`, debt stays at or below `x̄`
forever with probability zero. -/
theorem linear_rule_not_sustainable (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) {ρ γ φ : ℝ} (hρ : |ρ| < 1)
    (hφ : 0 ≤ φ) (hφγ : φ ≤ γ) (hγ1 : γ < 1) (sbar bbar x₀ xbar : ℝ) :
    (iidSystem ν).μ {ω | ∀ t, rulePath γ (linRule sbar φ bbar (ar1 ρ)) x₀ t ω ≤ xbar} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [ar1_unbounded_of_integrable hint hdef (γ := γ - φ) (by linarith)
    (by linarith) hρ x₀ (sbar - φ * bbar)] with ω hω hall
  obtain ⟨t, ht⟩ := (hω xbar).exists
  have := hall t
  rw [rulePath_linRule] at this
  exact absurd this (not_le.2 ht)

/-! ### Gaussian surpluses -/

/-- Cochrane (2023), p. 197: a non-degenerate Gaussian law puts positive mass on surpluses of
every size. -/
theorem gaussian_Ici_ne_zero (m : ℝ) {v : NNReal} (hv : v ≠ 0) (c : ℝ) :
    gaussianReal m v (Set.Ici c) ≠ 0 := by
  intro h
  have h2 := gaussianReal_absolutelyContinuous' m hv h
  rw [Real.volume_Ici] at h2
  exact ENNReal.top_ne_zero h2

/-- Cochrane (2023), p. 197: Gaussian innovations `N(0, v)` are integrable. -/
theorem gaussian_integrable (v : NNReal) :
    Integrable id ((gaussianProb 0 v : ProbabilityMeasure ℝ) : Measure ℝ) := by
  have h := memLp_id_gaussianReal (μ := 0) (v := v) 1
  rw [ENNReal.coe_one, memLp_one_iff_integrable] at h
  exact h

/-- **Verdict, one-sided limit, Gaussian AR(1) surpluses** (Cochrane (2023), §6.4.1, p. 197).
Surpluses `s_t = s̄ + u_t + φ (x_t − b̄)`, `u` a Gaussian AR(1) (`ε_t ~ N(0, v)`, `v ≠ 0`,
`|ρ| < 1`; `ρ = 0` is i.i.d.), `φ ≥ 0`, `0 < γ < 1`, boundary-avoiding modification, plan from
`0 < m₀ ≤ x̄`, `B > 0`, `y₀ > 0`:
(i) the plan keeps debt at or below `x̄` on every path (sustainability);
(ii) the equilibrium price levels are exactly `[B/(y₀ m₀), ∞)` (existence; deflation ruled out);
(iii) the equilibrium price level is NOT unique (no global determinacy);
(iv) if instead the rule responds to actual debt, the equilibrium price levels are exactly
`[B/(y₀ x̄), ∞)`. -/
theorem gaussian_plan_verdict {v : NNReal} (hv : v ≠ 0) {ρ γ φ : ℝ} (hρ : |ρ| < 1) (hγ : 0 < γ)
    (hγ1 : γ < 1) (hφ : 0 ≤ φ) {sbar bbar xbar m₀ B y₀ : ℝ} (hB : 0 < B) (hy : 0 < y₀)
    (hm₀p : 0 < m₀) (hm₀ : m₀ ≤ xbar) :
    (∀ ω t, avoidPath γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀ t ω ≤ xbar) ∧
    {P₀ | IsEqmPrice (iidSystem (gaussianProb 0 v)).μ γ xbar
      (avoidSurplus γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀) B y₀ P₀} =
        Set.Ici (B / (y₀ * m₀)) ∧
    (¬ ∃! P₀, IsEqmPrice (iidSystem (gaussianProb 0 v)).μ γ xbar
      (avoidSurplus γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀) B y₀ P₀) ∧
    {P₀ | IsFeedbackEqmPrice (iidSystem (gaussianProb 0 v)).μ γ xbar
      (linRule sbar φ bbar (ar1 ρ)) B y₀ P₀} = Set.Ici (B / (y₀ * xbar)) := by
  have hint := gaussian_integrable v
  have hdef := gaussian_Iic_ne_zero 0 hv
  refine ⟨fun ω => (avoidPath_within_iff γ xbar _ m₀ ω).2 hm₀, ?_,
    plan_price_not_unique hint hdef hρ hγ hγ1 hφ hB hy hm₀p hm₀, ?_⟩
  · ext P₀
    exact plan_eqm_price_iff hint hdef hρ hγ hγ1 hφ hB hy hm₀p hm₀ P₀
  · ext P₀
    exact feedback_price_iff _ γ _ hB hy (hm₀p.trans_le hm₀) P₀

/-- **Verdict, two-sided band, Gaussian AR(1) surpluses: global determinacy** (Cochrane (2023),
§6.4.1, p. 197, corrected statement). With the same surpluses and any response `φ`, a band
`x_{low} ≤ x̄` and a two-sided plan from `m₀ ∈ [x_{low}, x̄]`, `m₀ > 0`, `0 < γ`:
(i) debt stays in the band on every path; (ii) the only sustainable initial debt is `m₀`;
(iii) the equilibrium price level exists and is unique, `P₀ = B/(y₀ m₀)`. -/
theorem gaussian_band_verdict {v : NNReal} (hv : v ≠ 0) {ρ γ φ : ℝ} (hρ : |ρ| < 1)
    (hγ : 0 < γ) {xlow xbar m₀ B y₀ : ℝ} (hl : xlow ≤ xbar) (hm₀ : xlow ≤ m₀ ∧ m₀ ≤ xbar)
    (hB : 0 < B) (hy : 0 < y₀) (hm₀p : 0 < m₀) (sbar bbar : ℝ) :
    (∀ ω t, xlow ≤ bandPath γ xlow xbar (linRule sbar φ bbar (ar1 ρ)) m₀ t ω ∧
      bandPath γ xlow xbar (linRule sbar φ bbar (ar1 ρ)) m₀ t ω ≤ xbar) ∧
    (∀ x₀, BandSustainable (iidSystem (gaussianProb 0 v)).μ γ xlow xbar
      (bandSurplus γ xlow xbar (linRule sbar φ bbar (ar1 ρ)) m₀) x₀ ↔ x₀ = m₀) ∧
    ∃! P₀, IsBandEqmPrice (iidSystem (gaussianProb 0 v)).μ γ xlow xbar
      (bandSurplus γ xlow xbar (linRule sbar φ bbar (ar1 ρ)) m₀) B y₀ P₀ := by
  have hint := gaussian_integrable v
  have hdef := gaussian_Iic_ne_zero 0 hv
  have hup := gaussian_Ici_ne_zero 0 hv
  exact ⟨fun ω t => bandPath_mem_all hl hm₀ _ ω t,
    fun x₀ => band_sustainable_iff hint hdef hup hρ hγ hl hm₀ sbar bbar x₀,
    band_eqm_price_unique hint hdef hup hρ hγ hl hm₀ hB hy hm₀p sbar bbar⟩

/-- Cochrane (2023), p. 197, **on the i.i.d. process**: with i.i.d. surplus shocks `ε_t ~ ν`
(integrable, deficits and surpluses of every size) and the two-sided linear plan
`s_t = s̄ + ε_t + φ (m_t − b̄)` modified to the band, the equilibrium price level exists and is
unique; with the one-sided plan the equilibrium price levels are exactly `[B/(y₀ m₀), ∞)`. -/
theorem iid_verdict (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0)
    (hup : ∀ c : ℝ, (ν : Measure ℝ) (Set.Ici c) ≠ 0) {γ φ xlow xbar m₀ B y₀ : ℝ} (hγ : 0 < γ)
    (hγ1 : γ < 1) (hφ : 0 ≤ φ) (hl : xlow ≤ xbar) (hm₀ : xlow ≤ m₀ ∧ m₀ ≤ xbar) (hB : 0 < B)
    (hy : 0 < y₀) (hm₀p : 0 < m₀) (sbar bbar : ℝ) :
    (∃! P₀, IsBandEqmPrice (iidSystem ν).μ γ xlow xbar
      (bandSurplus γ xlow xbar (linRule sbar φ bbar shock) m₀) B y₀ P₀) ∧
    {P₀ | IsEqmPrice (iidSystem ν).μ γ xbar
      (avoidSurplus γ xbar (linRule sbar φ bbar shock) m₀) B y₀ P₀} =
        Set.Ici (B / (y₀ * m₀)) := by
  have hρ : |(0 : ℝ)| < 1 := by norm_num
  rw [linRule_shock]
  refine ⟨band_eqm_price_unique hint hdef hup hρ hγ hl hm₀ hB hy hm₀p sbar bbar, ?_⟩
  ext P₀
  exact plan_eqm_price_iff hint hdef hρ hγ hγ1 hφ hB hy hm₀p hm₀.2 P₀

end Cochrane.FiscalConstraints.TidyR6ManagedSurplusMeasure
