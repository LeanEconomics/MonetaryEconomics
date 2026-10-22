/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.FiscalRulesTargetFinal

/-!
# Theorem FR (d): strict comparative statics and the link to the core hypotheses

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.3.2,
eqs. (9.8)–(9.12), pp. 266–267 (Theorem FR, error E9.9).

## Strict comparative statics

* `price_strict_monotone`: for equilibria with prices bounded above (and integrable `1/P`), more
  initial debt in units of `θ` means a **strictly** higher date-0 price level: `d₀ < d₀'` gives
  `P_0 < P'_0` a.e. Proof: on the date-0 event `{P_0 = P'_0}` the comparison identity
  (`FiscalRulesTargetFinal.compare_identity_above`) forces `P_t = P'_t` at every date, so the debt
  difference grows like `β⁻ᵗ (d₀ − d₀')`, contradicting the bound on debt (`debt_bdd_rule`).

## The valuation equation is implied by the core hypotheses

* `hasSum_of_onesided`, `valuation_of_flow`: the valuation (9.9) as a genuine `HasSum` follows from
  the flow (9.8), predetermined debt and the transversality condition alone: the surplus
  `s_{0,t} + θ (P_t − P*_t)` is bounded on one side because `P > 0`, so the convergent partial sums
  are those of a series that is absolutely convergent after adding a geometric term. Prices may be
  unbounded above. (This corrects the earlier claim that the valuation `HasSum` fails for prices
  unbounded above.) `ruleEqm_of_flow` packages this.
* `fr_d_news_below_noval`: `FiscalRulesTargetClose.fr_d_news_below` with the valuation hypothesis
  dropped (general measure systems; news-bearing target; prices bounded away from zero; bounded
  deflator).
* `fr_d_finite_core` (**the link to the core `ExpectationSystem`**): on a finite fully supported
  system, stated entirely for the bridged core system `S.toExpectationSystem hfull`, the core
  hypotheses — positive adapted prices, the interest-rate target (9.12) for a stochastic target,
  the flow (9.8), predetermined debt, `b₀ = b̄` and the transversality condition — give `P = P*`.
  **No extra hypothesis is needed**: neither the valuation nor a price bound nor the deflator bound
  (prices are automatically bounded away from zero, `finite_price_lower`).
* `deflator_bound_needed`, `price_bound_needed`: on infinite systems the two extra hypotheses of
  `fr_d_news_below_noval` cannot be dropped: without the deflator bound
  (`FiscalRulesBelowCounter.fr_below_counterexample`) or without any price bound
  (`FiscalRulesMeasure.SunspotMeasure.fr_b_measure`) there are equilibria with `b₀ = b̄` and
  `P ≠ P*`.
-/

namespace Cochrane.AssetsRulesBalanceSheets.TidyR5FiscalLink

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure FiscalRulesMeasure FiscalRulesTargetMeasure FiscalRulesTargetOpen
open FiscalRulesTargetClose FiscalRulesTargetFinal

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-! ### Strict comparative statics -/

/-- Cochrane (2023), eqs. (9.8), (9.9), p. 266: in an equilibrium of the rule (`RuleEqm`) with
target `0 < m ≤ P* ≤ M*` and prices `P ≤ M`, real debt is bounded,
`|b_t| ≤ (|(1 − β) b̄| + |θ|(M + M*))/(1 − β)` a.e. -/
theorem debt_bdd_rule {β θ bbar m Ms M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Pstar P b : ℕ → Ω → ℝ}
    (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms) (hE : RuleEqm S β θ bbar Pstar P b)
    (hPM : ∀ t ω, P t ω ≤ M) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, |b t ω| ≤ (|(1 - β) * bbar| + |θ| * (M + Ms)) / (1 - β) := by
  obtain ⟨hP, hPa, -, hbi, -, hflow, hpre, -, htvc⟩ := hE
  have hPs0 : ∀ t ω, 0 < Pstar t ω := fun t ω => hm.trans_le (hPs t ω).1
  refine debt_bdd S hβ0 hβ1 (s := fun t ω => (1 - β) * bbar + θ * (P t ω - Pstar t ω))
    (fun t => stronglyMeasurable_const.add (((hPa t).sub (hPsa t)).const_mul θ))
    (fun t ω => ?_) hflow hpre hbi htvc t
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg θ)
  rw [abs_le]
  have := hP t ω
  have := hPM t ω
  have := (hPs t ω).2
  have := hPs0 t ω
  constructor <;> linarith

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**strict comparative statics**): if equilibria of the
rule with prices bounded above (and integrable `1/P`) exist for initial debts `b̄ + θ d₀` and
`b̄ + θ d₀'` with `d₀ < d₀'` (same target `0 < m ≤ P* ≤ M*`, news allowed), then `P_0 < P'_0` a.e.
This sharpens `FiscalRulesTargetFinal.price_monotone`. -/
theorem price_strict_monotone {β θ bbar d0 d0' m Ms M M' : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 0) {Pstar P P' b b' : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hE : RuleEqm S β θ bbar Pstar P b) (hE' : RuleEqm S β θ bbar Pstar P' b')
    (hPM : ∀ t ω, P t ω ≤ M) (hP'M : ∀ t ω, P' t ω ≤ M')
    (hq : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ)
    (hq' : ∀ t, Integrable (fun ω => 1 / P' t ω) S.μ)
    (hb0 : ∀ ω, b 0 ω = bbar + θ * d0) (hb0' : ∀ ω, b' 0 ω = bbar + θ * d0') (hd : d0 < d0') :
    ∀ᵐ ω ∂S.μ, P 0 ω < P' 0 ω := by
  have h1β : 0 < 1 - β := by linarith
  have hweak := price_monotone S hβ0 hβ1 hθ hPsa hm hPs hE hE' hPM hP'M hq hq' hb0 hb0' hd.le
  have hid := compare_identity_above S hβ0 hβ1 hθ hPsa hm hPs ((ruleEqm_iff_gen S).1 hE)
    ((ruleEqm_iff_gen S).1 hE') hPM hP'M hq hq'
  have hbK := debt_bdd_rule S hβ0 hβ1 hPsa hm hPs hE hPM
  have hbK' := debt_bdd_rule S hβ0 hβ1 hPsa hm hPs hE' hP'M
  obtain ⟨hP, hPa, -, -, -, hflow, -, -, -⟩ := hE
  obtain ⟨hP', hP'a, -, -, -, hflow', -, -, -⟩ := hE'
  set f : ℕ → Ω → ℝ := fun t ω => β ^ t * defl S Pstar t ω *
    ((P' t ω - P t ω) * (1 / P t ω - 1 / P' t ω)) with hf
  set G : Set Ω := {ω | P 0 ω = P' 0 ω} with hG
  have hGm : MeasurableSet[S.𝓕 0] G := measurableSet_eq_fun (hPa 0).measurable (hP'a 0).measurable
  have hGm' : MeasurableSet G := S.𝓕.le 0 _ hGm
  have hsq : ∀ t ω, (P' t ω - P t ω) * (1 / P t ω - 1 / P' t ω) =
      (P' t ω - P t ω) ^ 2 / (P t ω * P' t ω) := fun t ω => by
    field_simp [(hP t ω).ne', (hP' t ω).ne']
  have hfnn : ∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ f t ω := fun t => by
    filter_upwards [defl_bounds S hPsa hm hPs t] with ω hN
    simp only [hf]
    rw [hsq]
    exact mul_nonneg (mul_nonneg (pow_pos hβ0 t).le hN.1.le)
      (div_nonneg (sq_nonneg _) (mul_pos (hP t ω) (hP' t ω)).le)
  -- integrability of the drift
  have hfi : ∀ t, Integrable (f t) S.μ := fun t => by
    have hDm : StronglyMeasurable (defl S Pstar t) :=
      (defl_meas S hPsa (Nat.le_succ t)).mono (S.𝓕.le t)
    have hPm : StronglyMeasurable (P t) := (hPa t).mono (S.𝓕.le t)
    have hP'm : StronglyMeasurable (P' t) := (hP'a t).mono (S.𝓕.le t)
    have hqm : StronglyMeasurable (fun ω => 1 / P t ω) :=
      (hPm.measurable.const_div 1).stronglyMeasurable
    have hq'm : StronglyMeasurable (fun ω => 1 / P' t ω) :=
      (hP'm.measurable.const_div 1).stronglyMeasurable
    have hfm : StronglyMeasurable (f t) :=
      (stronglyMeasurable_const.mul hDm).mul ((hP'm.sub hPm).mul (hqm.sub hq'm))
    refine Integrable.mono' ((((hq t).const_mul M').add ((hq' t).const_mul M)).const_mul
      (β ^ t * (Ms / m) ^ t)) hfm.aestronglyMeasurable ?_
    filter_upwards [defl_bounds S hPsa hm hPs t, hfnn t] with ω hN hnn
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hX : (P' t ω - P t ω) * (1 / P t ω - 1 / P' t ω) ≤
        M' * (1 / P t ω) + M * (1 / P' t ω) := by
      have hp := hP t ω
      have hp' := hP' t ω
      have e : (P' t ω - P t ω) * (1 / P t ω - 1 / P' t ω) =
          P' t ω * (1 / P t ω) + P t ω * (1 / P' t ω) - 2 := by
        field_simp
        ring
      rw [e]
      have h1 : P' t ω * (1 / P t ω) ≤ M' * (1 / P t ω) :=
        mul_le_mul_of_nonneg_right (hP'M t ω) (one_div_pos.2 hp).le
      have h2 : P t ω * (1 / P' t ω) ≤ M * (1 / P' t ω) :=
        mul_le_mul_of_nonneg_right (hPM t ω) (one_div_pos.2 hp').le
      linarith
    have hX0 : 0 ≤ (P' t ω - P t ω) * (1 / P t ω - 1 / P' t ω) := by
      rw [hsq]
      exact div_nonneg (sq_nonneg _) (mul_pos (hP t ω) (hP' t ω)).le
    simp only [hf, Pi.add_apply]
    calc β ^ t * defl S Pstar t ω * ((P' t ω - P t ω) * (1 / P t ω - 1 / P' t ω))
        ≤ β ^ t * (Ms / m) ^ t * (M' * (1 / P t ω) + M * (1 / P' t ω)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hN.2 (pow_pos hβ0 t).le) hX hX0
            (mul_nonneg (pow_pos hβ0 t).le (hN.1.le.trans hN.2))
      _ = _ := rfl
  -- on `G` every forecast drift vanishes
  have hE0z : ∀ t, ∀ᵐ ω ∂S.μ, ω ∈ G → S.E 0 (f t) ω = 0 := fun t => by
    have hnnE : ∀ s, ∀ᵐ ω ∂S.μ, 0 ≤ S.E 0 (f s) ω := fun s => by
      have := S.E_mono (integrable_const 0) (hfi s) (hfnn s) 0
      rw [S.E_const] at this
      exact this
    filter_upwards [hid, ae_all_iff.2 hnnE] with ω e1 e2 hω
    have hω' : P 0 ω = P' 0 ω := hω
    rw [hω', sub_self, mul_zero] at e1
    exact congrFun ((hasSum_zero_iff_of_nonneg e2).1 e1) t
  have hfz : ∀ t, ∀ᵐ ω ∂S.μ, ω ∈ G → f t ω = 0 := fun t => by
    have hint : ∫ ω in G, f t ω ∂S.μ = 0 := by
      rw [← setIntegral_condExp (S.𝓕.le 0) (hfi t) hGm]
      exact setIntegral_eq_zero_of_ae_eq_zero (hE0z t)
    have h := (setIntegral_eq_zero_iff_of_nonneg_ae (ae_restrict_of_ae (hfnn t))
      (hfi t).integrableOn).1 hint
    exact (ae_restrict_iff' hGm').1 (h.mono fun ω e => e)
  have hPP : ∀ t, ∀ᵐ ω ∂S.μ, ω ∈ G → P t ω = P' t ω := fun t => by
    filter_upwards [hfz t, defl_bounds S hPsa hm hPs t] with ω e hN hω
    have e' := e hω
    simp only [hf] at e'
    rw [hsq] at e'
    have hpos : 0 < β ^ t * defl S Pstar t ω := mul_pos (pow_pos hβ0 t) hN.1
    rcases mul_eq_zero.1 e' with h | h
    · exact absurd h hpos.ne'
    · rcases div_eq_zero_iff.1 h with h2 | h2
      · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
        linarith
      · exact absurd h2 (mul_pos (hP t ω) (hP' t ω)).ne'
  -- on `G` the debt difference grows geometrically
  have hΔ : ∀ t, ∀ᵐ ω ∂S.μ, ω ∈ G → θ⁻¹ * (b t ω - b' t ω) = (d0 - d0') / β ^ t := by
    intro t
    induction t with
    | zero =>
      refine Eventually.of_forall fun ω _ => ?_
      rw [hb0 ω, hb0' ω]
      field_simp
      ring
    | succ t ih =>
      filter_upwards [ih, hPP t] with ω e1 e2 hω
      have f1 := hflow t ω
      have f2 := hflow' t ω
      have e3 := e1 hω
      have e4 := e2 hω
      have hb : b (t + 1) ω - b' (t + 1) ω = (b t ω - b' t ω) / β := by
        rw [eq_div_iff hβ0.ne']
        rw [f1, f2, e4]
        ring
      rw [hb, pow_succ, div_mul_eq_div_div, ← e3]
      ring
  -- the bound on debt rules this out
  set K : ℝ := |θ⁻¹| * ((|(1 - β) * bbar| + |θ| * (M + Ms)) / (1 - β) +
    (|(1 - β) * bbar| + |θ| * (M' + Ms)) / (1 - β)) with hK
  have hΔK : ∀ t, ∀ᵐ ω ∂S.μ, |θ⁻¹ * (b t ω - b' t ω)| ≤ K := fun t => by
    filter_upwards [hbK t, hbK' t] with ω e1 e2
    rw [abs_mul, hK]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add e1 e2)) (abs_nonneg _)
  obtain ⟨T, hT⟩ := exists_pow_lt_of_lt_one (show 0 < (d0' - d0) / (|K| + 1) by
    apply div_pos <;> linarith [abs_nonneg K]) hβ1
  have hGnull : ∀ᵐ ω ∂S.μ, ω ∉ G := by
    filter_upwards [hΔ T, hΔK T] with ω e1 e2 hω
    rw [e1 hω] at e2
    have hβT : 0 < β ^ T := pow_pos hβ0 T
    rw [abs_div, abs_of_pos hβT, div_le_iff₀ hβT, abs_of_neg (by linarith)] at e2
    rw [lt_div_iff₀ (by linarith [abs_nonneg K])] at hT
    nlinarith [le_abs_self K]
  filter_upwards [hweak, hGnull] with ω e1 e2
  exact lt_of_le_of_ne e1 e2

/-! ### The valuation equation follows from the flow and the transversality condition -/

/-- Cochrane (2023), eq. (9.9), p. 266 (supporting lemma): a real series whose partial sums converge
to `L` and whose terms are bounded on one side by a geometric sequence, `ε a_j ≥ −C βʲ` with
`ε = ±1` and `0 ≤ β < 1`, has sum `L` (it is absolutely summable). -/
theorem hasSum_of_onesided {a : ℕ → ℝ} {L β C ε : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hε : ε = 1 ∨ ε = -1) (hb : ∀ j, -(C * β ^ j) ≤ ε * a j)
    (hL : Tendsto (fun k => ∑ j ∈ Finset.range k, a j) atTop (𝓝 L)) : HasSum a L := by
  have hε2 : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hg := hasSum_geometric_of_lt_one hβ0 hβ1
  have hc : HasSum (fun j => ε * a j + C * β ^ j) (ε * L + C * (1 - β)⁻¹) := by
    refine (hasSum_iff_tendsto_nat_of_nonneg (fun j => by linarith [hb j]) _).2 ?_
    have := (hL.const_mul ε).add (hg.mul_left C).tendsto_sum_nat
    refine this.congr fun k => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  have h2 := (hc.sub (hg.mul_left C)).mul_left ε
  convert h2 using 1
  · funext j
    linear_combination (-(a j)) * hε2
  · linear_combination (-L) * hε2

/-- Cochrane (2023), eqs. (9.8), (9.9), p. 266 (**the valuation is implied by the flow and the
transversality condition**): let real debt obey the flow `b_t = s_{0,t} + θ (P_t − P*_t) +
β b_{t+1}` with a bounded adapted `s₀`, positive adapted integrable prices (not necessarily
bounded), an adapted target `0 ≤ P* ≤ M*`, predetermined integrable debt and the transversality
condition. Then the valuation (9.9) holds as a genuine `HasSum` a.e. -/
theorem valuation_of_flow {β θ C0 Ms : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {s0 Pstar P b : ℕ → Ω → ℝ} (hs0m : ∀ t, StronglyMeasurable[S.𝓕 t] (s0 t))
    (hs0C : ∀ t ω, |s0 t ω| ≤ C0) (hPsa : StronglyAdapted S.𝓕 Pstar)
    (hPs : ∀ t ω, 0 ≤ Pstar t ω ∧ Pstar t ω ≤ Ms) (hP : ∀ t ω, 0 < P t ω)
    (hPa : StronglyAdapted S.𝓕 P) (hPi : ∀ t, Integrable (P t) S.μ)
    (hbi : ∀ t, Integrable (b t) S.μ)
    (hflow : ∀ t ω, b t ω = s0 t ω + θ * (P t ω - Pstar t ω) + β * b (t + 1) ω)
    (hpre : ∀ t, StronglyMeasurable[S.𝓕 t] (b (t + 1)))
    (htvc : ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun T => β ^ T * S.E t (b (t + T)) ω) atTop (𝓝 0))
    (t : ℕ) : ∀ᵐ ω ∂S.μ, HasSum (fun j => β ^ j * S.E t
      (fun ω' => s0 (t + j) ω' + θ * (P (t + j) ω' - Pstar (t + j) ω')) ω) (b t ω) := by
  set s : ℕ → Ω → ℝ := fun t ω => s0 t ω + θ * (P t ω - Pstar t ω) with hs
  have hsm : ∀ t, StronglyMeasurable[S.𝓕 t] (s t) := fun t =>
    (hs0m t).add (((hPa t).sub (hPsa t)).const_mul θ)
  have hs0i : ∀ t, Integrable (s0 t) S.μ := fun t =>
    Integrable.of_bound ((hs0m t).mono (S.𝓕.le t)).aestronglyMeasurable C0
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hs0C t ω)
  have hPsi : ∀ t, Integrable (Pstar t) S.μ := fun t =>
    Integrable.of_bound ((hPsa t).mono (S.𝓕.le t)).aestronglyMeasurable Ms
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hPs t ω).1]; exact (hPs t ω).2)
  have hsi : ∀ t, Integrable (s t) S.μ := fun t =>
    (hs0i t).add (((hPi t).sub (hPsi t)).const_mul θ)
  have hflow' : ∀ t ω, b t ω = s t ω + β * b (t + 1) ω := hflow
  have hbm : ∀ t, StronglyMeasurable[S.𝓕 t] (b t) := fun t => by
    have e : b t = fun ω => s t ω + β * b (t + 1) ω := funext (hflow' t)
    rw [e]
    exact (hsm t).add ((hpre t).const_mul β)
  set ε : ℝ := if 0 ≤ θ then 1 else -1 with hε
  have hε1 : ε = 1 ∨ ε = -1 := by
    by_cases h : 0 ≤ θ
    · left; simp [hε, h]
    · right; simp [hε, h]
  set C : ℝ := C0 + |θ| * Ms with hC
  have hsl : ∀ t ω, -C ≤ ε * s t ω := fun t ω => by
    have h0 := (abs_le.1 (hs0C t ω))
    have hp := hP t ω
    have hps := hPs t ω
    simp only [hε, hs, hC]
    by_cases h : 0 ≤ θ
    · simp only [h, ↓reduceIte, one_mul]
      rw [abs_of_nonneg h]
      nlinarith
    · simp only [h, ↓reduceIte]
      push Not at h
      rw [abs_of_neg h]
      nlinarith
  have hEl : ∀ j, ∀ᵐ ω ∂S.μ, -C ≤ ε * S.E t (s (t + j)) ω := fun j => by
    have h1 := S.E_mono (integrable_const (-C)) ((hsi (t + j)).const_mul ε)
      (Eventually.of_forall fun ω => hsl (t + j) ω) t
    have h2 := S.E_smul ε (s (t + j)) t
    rw [S.E_const] at h1
    filter_upwards [h1, h2] with ω e1 e2
    have e3 : S.E t (fun ω => ε * s (t + j) ω) ω = ε * S.E t (s (t + j)) ω := by
      have : (fun ω => ε * s (t + j) ω) = ε • s (t + j) := rfl
      rw [this, e2]
      rfl
    rw [← e3]
    exact e1
  filter_upwards [ae_all_iff.2 (value_partial S hflow' hbm hbi hsi t), htvc t,
    ae_all_iff.2 hEl] with ω h1 h2 h3
  refine hasSum_of_onesided (C := C) (ε := ε) hβ0.le hβ1 hε1 (fun j => ?_) ?_
  · have := h3 j
    have hpj := pow_pos hβ0 j
    calc -(C * β ^ j) = β ^ j * (-C) := by ring
      _ ≤ β ^ j * (ε * S.E t (s (t + j)) ω) := mul_le_mul_of_nonneg_left this hpj.le
      _ = ε * (β ^ j * S.E t (s (t + j)) ω) := by ring
  · have := (tendsto_const_nhds (x := b t ω)).sub h2
    rw [sub_zero] at this
    exact this.congr fun k => by linarith [h1 k]

/-- Cochrane (2023), §9.3.2, pp. 266–267: the core-style hypotheses of the rule — positive adapted
integrable prices, an adapted target `0 ≤ P* ≤ M*`, (9.12), the flow (9.8), predetermined
integrable debt and the transversality condition — already make an equilibrium in the sense of
`RuleEqm`: the valuation clause is redundant (`valuation_of_flow`). -/
theorem ruleEqm_of_flow {β θ bbar Ms : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Pstar P b : ℕ → Ω → ℝ}
    (hPsa : StronglyAdapted S.𝓕 Pstar) (hPs : ∀ t ω, 0 ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hP : ∀ t ω, 0 < P t ω) (hPa : StronglyAdapted S.𝓕 P) (hPi : ∀ t, Integrable (P t) S.μ)
    (hbi : ∀ t, Integrable (b t) S.μ)
    (hrate : ∀ t, S.E t (P t / P (t + 1)) =ᵐ[S.μ] S.E t (Pstar t / Pstar (t + 1)))
    (hflow : ∀ t ω, b t ω = (1 - β) * bbar + θ * (P t ω - Pstar t ω) + β * b (t + 1) ω)
    (hpre : ∀ t, StronglyMeasurable[S.𝓕 t] (b (t + 1)))
    (htvc : ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun T => β ^ T * S.E t (b (t + T)) ω) atTop (𝓝 0)) :
    RuleEqm S β θ bbar Pstar P b :=
  ⟨hP, hPa, hPi, hbi, hrate, hflow, hpre, fun t => valuation_of_flow S hβ0 hβ1
    (s0 := fun _ _ => (1 - β) * bbar) (C0 := |(1 - β) * bbar|)
    (fun _ => stronglyMeasurable_const) (fun _ _ => le_rfl) hPsa hPs hP hPa hPi hbi hflow hpre
    htvc t, htvc⟩

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d), bounded away from zero, news-bearing
target, without the valuation hypothesis**): with the flow, predetermined debt, the
transversality condition, the interest-rate target (9.12), an adapted target `0 < m ≤ P* ≤ M*`
whose cumulative real-rate factor is bounded (`∏ γ⁻¹ ≤ L`), prices `P ≥ m_P > 0` and `b₀ = b̄`, the
price level is `P = P*`. -/
theorem fr_d_news_below_noval {β θ bbar mP m Ms L : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {Pstar P b : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hL : ∀ t k, ∀ᵐ ω ∂S.μ, ∏ i ∈ Finset.range k,
      (Pstar (t + i) ω * S.E (t + i) (fun ω => 1 / Pstar (t + i + 1) ω) ω)⁻¹ ≤ L)
    (hP : ∀ t ω, 0 < P t ω) (hPa : StronglyAdapted S.𝓕 P) (hPi : ∀ t, Integrable (P t) S.μ)
    (hbi : ∀ t, Integrable (b t) S.μ)
    (hrate : ∀ t, S.E t (P t / P (t + 1)) =ᵐ[S.μ] S.E t (Pstar t / Pstar (t + 1)))
    (hflow : ∀ t ω, b t ω = (1 - β) * bbar + θ * (P t ω - Pstar t ω) + β * b (t + 1) ω)
    (hpre : ∀ t, StronglyMeasurable[S.𝓕 t] (b (t + 1)))
    (htvc : ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun T => β ^ T * S.E t (b (t + T)) ω) atTop (𝓝 0))
    (hmP : 0 < mP) (hPmP : ∀ t ω, mP ≤ P t ω) (hb0 : ∀ ω, b 0 ω = bbar) (t : ℕ) :
    P t =ᵐ[S.μ] Pstar t :=
  fr_d_news_below S hβ0 hβ1 hθ hPsa hm hPs hL
    (ruleEqm_of_flow S hβ0 hβ1 hPsa (fun t ω => ⟨hm.le.trans (hPs t ω).1, (hPs t ω).2⟩) hP hPa
      hPi hbi hrate hflow hpre htvc) hmP hPmP hb0 t

/-! ### The link to the core `ExpectationSystem` on finite systems -/

/-- Cochrane (2023), eq. (9.12), p. 267 (supporting the link): on a finite fully supported system,
stated for the bridged core system, prices meeting the interest-rate target for a positive target
are bounded away from zero: after the date `T` at which the system is resolved, (9.12) gives
`P_t = P_T P*_t / P*_T`. -/
theorem finite_price_lower [Finite Ω] [DiscreteMeasurableSpace Ω] [Nonempty Ω]
    (hfull : ∀ ω, S.μ {ω} ≠ 0) {m Ms : ℝ} (hm : 0 < m) {Pstar P : ℕ → Ω → ℝ}
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hPsa : (S.toExpectationSystem hfull).Adapted Pstar)
    (hP : ∀ t ω, 0 < P t ω) (hPa : (S.toExpectationSystem hfull).Adapted P)
    (hrate : ∀ t, (S.toExpectationSystem hfull).E t (P t / P (t + 1)) =
      (S.toExpectationSystem hfull).E t (Pstar t / Pstar (t + 1))) :
    ∃ mP, 0 < mP ∧ ∀ t ω, mP ≤ P t ω := by
  have hsm : ∀ t (x : Ω → ℝ), S.E t x = x → StronglyMeasurable[S.𝓕 t] x := fun t x h => by
    have := S.stronglyMeasurable_E t x
    rwa [h] at this
  have hPs0 : ∀ t ω, 0 < Pstar t ω := fun t ω => hm.trans_le (hPs t ω).1
  have hMs : 0 < Ms := (hPs0 0 (Classical.arbitrary Ω)).trans_le (hPs 0 _).2
  obtain ⟨T, hres⟩ := finite_resolved S
  -- after `T` the ratio is realised
  have hstep : ∀ t, T ≤ t → ∀ ω, P (t + 1) ω = P t ω * (Pstar (t + 1) ω / Pstar t ω) := by
    intro t ht ω
    have hm1 : ∀ Q : ℕ → Ω → ℝ, (S.toExpectationSystem hfull).Adapted Q →
        StronglyMeasurable[S.𝓕 t] (Q t / Q (t + 1)) := fun Q hQ => by
      have h1 : StronglyMeasurable[S.𝓕 t] (Q t) := hsm t _ (hQ t)
      have h2 : StronglyMeasurable[S.𝓕 t] (Q (t + 1)) :=
        ((hsm (t + 1) _ (hQ (t + 1))).mono ((hres (t + 1) (by omega)).trans (S.𝓕.mono ht)))
      exact (h1.measurable.div h2.measurable).stronglyMeasurable
    have h := congrFun (hrate t) ω
    rw [S.toExpectationSystem_E, S.toExpectationSystem_E,
      S.E_of_stronglyMeasurable (hm1 P hPa) Integrable.of_finite,
      S.E_of_stronglyMeasurable (hm1 Pstar hPsa) Integrable.of_finite] at h
    simp only [Pi.div_apply] at h
    have := (hP t ω).ne'
    have := (hP (t + 1) ω).ne'
    have := (hPs0 t ω).ne'
    have := (hPs0 (t + 1) ω).ne'
    field_simp at h ⊢
    linarith
  have hlate : ∀ k ω, P (T + k) ω = P T ω * (Pstar (T + k) ω / Pstar T ω) := by
    intro k
    induction k with
    | zero => intro ω; simp [div_self (hPs0 T ω).ne']
    | succ k ih =>
      intro ω
      rw [← add_assoc, hstep (T + k) (by omega) ω, ih ω]
      have := (hPs0 (T + k) ω).ne'
      have := (hPs0 T ω).ne'
      field_simp
  obtain ⟨p, hp⟩ := Finite.exists_min (fun q : Fin (T + 1) × Ω => P q.1 q.2)
  set c := P p.1 p.2 with hc
  have hc0 : 0 < c := hP _ _
  have hr : 0 < m / Ms := div_pos hm hMs
  have hr1 : m / Ms ≤ 1 := (div_le_one hMs).2 ((hPs 0 (Classical.arbitrary Ω)).1.trans
    (hPs 0 _).2)
  refine ⟨c * (m / Ms), mul_pos hc0 hr, fun t ω => ?_⟩
  rcases Nat.lt_or_ge t (T + 1) with ht | ht
  · have := hp (⟨t, ht⟩, ω)
    calc c * (m / Ms) ≤ c * 1 := mul_le_mul_of_nonneg_left hr1 hc0.le
      _ = c := mul_one c
      _ ≤ P t ω := this
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show T ≤ t by omega)
    rw [hlate k ω]
    have hT := hp (⟨T, by omega⟩, ω)
    have hq : m / Ms ≤ Pstar (T + k) ω / Pstar T ω :=
      div_le_div₀ (hm.le.trans (hPs _ ω).1) (hPs _ ω).1 (hPs0 T ω) (hPs T ω).2
    exact mul_le_mul hT hq hr.le (hP T ω).le

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d), link to the core `ExpectationSystem`,
stochastic target**): on a finite, fully supported measure system, with every hypothesis stated
for the bridged core system `S.toExpectationSystem hfull` — positive adapted prices, an adapted
target `0 < m ≤ P* ≤ M*` (its present value may carry news), the interest-rate target (9.12)
`E_t(P_t/P_{t+1}) = E_t(P*_t/P*_{t+1})`, the flow (9.8) with the rule `s_t = (1 − β) b̄ + θ (P_t −
P*_t)`, predetermined real debt, `b₀ = b̄` and the transversality condition — the price level is
the target, `P = P*`, at every date and state. No extra hypothesis is needed: the valuation (9.9),
a price bound and the deflator bound all follow. -/
theorem fr_d_finite_core [Finite Ω] [DiscreteMeasurableSpace Ω] (hfull : ∀ ω, S.μ {ω} ≠ 0)
    {β θ bbar m Ms : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0) (hm : 0 < m)
    {Pstar P b : ℕ → Ω → ℝ} (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hPsa : (S.toExpectationSystem hfull).Adapted Pstar)
    (hP : ∀ t ω, 0 < P t ω) (hPa : (S.toExpectationSystem hfull).Adapted P)
    (hrate : ∀ t, (S.toExpectationSystem hfull).E t (P t / P (t + 1)) =
      (S.toExpectationSystem hfull).E t (Pstar t / Pstar (t + 1)))
    (hflow : ∀ t ω, b t ω = (1 - β) * bbar + θ * (P t ω - Pstar t ω) + β * b (t + 1) ω)
    (hpre : ∀ t, (S.toExpectationSystem hfull).E t (b (t + 1)) = b (t + 1))
    (hb0 : ∀ ω, b 0 ω = bbar)
    (htvc : ∀ t ω, Tendsto (fun T => β ^ T * (S.toExpectationSystem hfull).E t (b (t + T)) ω)
      atTop (𝓝 0)) :
    P = Pstar := by
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · funext t ω
    exact (IsEmpty.false ω).elim
  have hsm : ∀ t (x : Ω → ℝ), S.E t x = x → StronglyMeasurable[S.𝓕 t] x := fun t x h => by
    have := S.stronglyMeasurable_E t x
    rwa [h] at this
  obtain ⟨mP, hmP, hPmP⟩ := finite_price_lower S hfull hm hPs hPsa hP hPa hrate
  obtain ⟨L, hL⟩ := finite_hL S (fun t => hsm t _ (hPsa t)) hm hPs
  funext t
  refine S.eq_of_ae_eq hfull (fr_d_news_below_noval S hβ0 hβ1 hθ (fun t => hsm t _ (hPsa t)) hm
    hPs hL hP (fun t => hsm t _ (hPa t)) (fun _ => Integrable.of_finite)
    (fun _ => Integrable.of_finite) (fun t => EventuallyEq.of_eq (hrate t)) hflow
    (fun t => hsm t _ (hpre t)) (fun t => Eventually.of_forall (htvc t)) hmP hPmP hb0 t)

/-! ### Which extra hypotheses are necessary on infinite systems -/

/-- Cochrane (2023), §9.3.2, p. 267 (**the deflator bound is necessary**): for every `0 < β < 1`,
`θ ≠ 0`, `b̄`, there is a genuine probability space, an adapted target `0 < m ≤ P* ≤ 2` and an
equilibrium of the rule with prices bounded away from zero and `b₀ = b̄` (so every hypothesis of
`fr_d_news_below_noval` except the deflator bound holds) in which `P ≠ P*` and the deflator is
unbounded. -/
theorem deflator_bound_needed {β θ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0) (bbar : ℝ) :
    ∃ (S : MeasExpectationSystem (ℕ → ℝ)) (Pstar P b : ℕ → (ℕ → ℝ) → ℝ) (m mP : ℝ),
      RuleEqm S β θ bbar Pstar P b ∧ (∀ ω, b 0 ω = bbar) ∧ 0 < m ∧ 0 < mP ∧
      StronglyAdapted S.𝓕 Pstar ∧ (∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ 2) ∧
      (∀ t ω, mP ≤ P t ω) ∧ (¬ ∀ t, P t =ᵐ[S.μ] Pstar t) ∧
      ¬ ∃ L, ∀ t k, ∀ᵐ ω ∂S.μ, ∏ i ∈ Finset.range k,
        (Pstar (t + i) ω * S.E (t + i) (fun ω => 1 / Pstar (t + i + 1) ω) ω)⁻¹ ≤ L := by
  obtain ⟨hE, -, hb0, hmP, hlow, hPsa, hPs, -, -, -, -, hnot, -, hnoL⟩ :=
    FiscalRulesBelowCounter.fr_below_counterexample hβ0 hβ1 hθ bbar
  have hm : 0 < (2 - β) * (1 - β) / 2 := by
    have : 0 < (2 - β) * (1 - β) := mul_pos (by linarith) (by linarith)
    linarith
  exact ⟨_, _, _, _, _, _, hE, hb0, hm, hmP, hPsa, hPs, hlow, hnot, hnoL⟩

/-- Cochrane (2023), §9.3.2, p. 267 (**some price bound is necessary**, Theorem FR (b)): for every
`0 < β < 1`, `0 < c₀ < 1`, `θ`, `b̄`, the genuine settle-or-continue probability space carries an
equilibrium of the rule with the constant target `P* ≡ 1` (deflator bound `L = 1`) and `b₀ = b̄`
whose date-0 price is not `1`; its prices are neither bounded above nor away from zero. -/
theorem price_bound_needed {β c0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (θ bbar : ℝ) :
    RuleEqm (SunspotMeasure.sunSystem hβ0 hβ1 hc0 hc1) β θ bbar (fun _ _ => 1)
        (SunspotMeasure.sunPrice β c0) (SunspotMeasure.sunDebt β c0 θ bbar) ∧
      (∀ ω, SunspotMeasure.sunDebt β c0 θ bbar 0 ω = bbar) ∧
      (∀ ω, SunspotMeasure.sunPrice β c0 0 ω ≠ 1) ∧
      (¬ ∃ M, ∀ t, ∀ᵐ ω ∂(SunspotMeasure.sunSystem hβ0 hβ1 hc0 hc1).μ,
        SunspotMeasure.sunPrice β c0 t ω ≤ M) ∧
      ¬ ∃ m, 0 < m ∧ ∀ t, ∀ᵐ ω ∂(SunspotMeasure.sunSystem hβ0 hβ1 hc0 hc1).μ,
        m ≤ SunspotMeasure.sunPrice β c0 t ω := by
  obtain ⟨hE, -, hb0, -, hlt⟩ := SunspotMeasure.fr_b_measure hβ0 hβ1 hc0 hc1 θ bbar
  exact ⟨hE, hb0, fun ω => (hlt ω).ne, SunspotMeasure.sun_price_unbounded hβ0 hβ1 hc0 hc1⟩

end Cochrane.AssetsRulesBalanceSheets.TidyR5FiscalLink
