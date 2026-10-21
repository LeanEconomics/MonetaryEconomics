/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.FiscalRulesTargetMeasure

/-!
# Theorem FR (d): uniqueness with a news-bearing target and a general surplus `s₀`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.3.2,
eqs. (9.8)–(9.12), pp. 266–267 (Theorem FR, error E9.9; the stochastic `P*_t` target, p. 267; the
surplus `s_{0,t} = a(L) ε_{s,t}` with `a(β) = 0`, p. 266).

`FiscalRulesTargetMeasure` proves Theorem FR (d) for targets whose present value is predetermined
(no news), with `s₀ = (1 − β) b̄`. This module closes the remaining cases on genuine
measure-theoretic expectation systems.

## Main results

* **Comparison theorem** (`fr_compare`): two equilibria with the same underlying surplus `s₀`
  (`RuleEqmGen`), the same target and the same initial debt coincide once their prices are bounded
  above. No condition on `s₀` or on the target is needed.
  * Proof: the scaled debt difference `Δ = (b − b′)/θ` is predetermined and bounded, and
    `Δ_t = P_t − P′_t + β Δ_{t+1}`.
  * If `Δ_{t+1} > 0` somewhere, then `P_t < P′_t` there. The interest-rate target then forces
    `P_{t+1} < P′_{t+1}` on a positive-probability part (`child_lt`).
  * Along these events `Δ_{t+k+1} > δ/βᵏ` (`compare_step`), contradicting boundedness.
* **(1) `b₀ = b̄`, target with news** (`fr_d_news`, `fr_unique_news`): for every adapted bounded
  target, `P = P*` is an equilibrium and the unique one with prices bounded above.
  * `BoolNews.bool_news_unique`: on the coin tree of `BoolExample` (a target whose present value
    has news), the bounded-above equilibrium is unique for every initial debt. It is `P*` for
    `b₀ = b̄` and `P* + 1` for `b₀ = b̄ + θ/(1 − β)`.
  * `fr_d_news_link` (**link**): the result specialises to the core `FiscalRules.fr_unique_bounded`.
* **(3) A general surplus `s₀` with `a(β) = 0`**, where a bounded `B` has
  `B_t = s_{0,t} + β B_{t+1}` and `B_{t+1}` known at `t`; then `b̄` is replaced by the present
  value `B₀`:
  * `fr_unique_s0` (bounded above) and `fr_unique_s0_below` (bounded away from zero):
    `P_t = (1 + (b₀ − B₀)/(θ a₀)) P*_t`.
  * `fr_unique_s0_random`, `fr_unique_s0_random_below`: the same with random date-0 data.
  * `MA.value_rec`, `MA.fr_unique_ma` (finite order) and `MAinf.value_rec`, `MAinf.fr_unique_ma`
    (absolutely summable `a(L)`): a moving average `s_{0,t} = a(L) ε_t` with `a(β) = 0` has
    exactly such a predetermined present value, `B_t = ∑_{m ≥ 1} c_m ε_{t−m}`.
* The bounded-away-from-zero counterpart of (1)–(2) is in `FiscalRulesBelowCounter`.
-/

namespace Cochrane.AssetsRulesBalanceSheets.FiscalRulesTargetOpen

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure FiscalRulesMeasure FiscalRulesTargetMeasure

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), eqs. (9.8), (9.9), p. 266 (supporting Theorem FR (d)): if real debt obeys the
flow `b_t = s_t + β b_{t+1}` with `|s| ≤ C`, is predetermined, integrable and satisfies the
transversality condition, then `|b_t| ≤ C/(1 − β)` a.e. -/
theorem debt_bdd {β C : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {s b : ℕ → Ω → ℝ}
    (hsm : ∀ t, StronglyMeasurable[S.𝓕 t] (s t)) (hsC : ∀ t ω, |s t ω| ≤ C)
    (hflow : ∀ t ω, b t ω = s t ω + β * b (t + 1) ω)
    (hpre : ∀ t, StronglyMeasurable[S.𝓕 t] (b (t + 1))) (hbi : ∀ t, Integrable (b t) S.μ)
    (htvc : ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun T => β ^ T * S.E t (b (t + T)) ω) atTop (𝓝 0))
    (t : ℕ) : ∀ᵐ ω ∂S.μ, |b t ω| ≤ C / (1 - β) := by
  have hbm : ∀ t, StronglyMeasurable[S.𝓕 t] (b t) := fun t => by
    have e : b t = fun ω => s t ω + β * b (t + 1) ω := funext (hflow t)
    rw [e]
    exact (hsm t).add ((hpre t).const_mul β)
  have hsi : ∀ t, Integrable (s t) S.μ := fun t =>
    Integrable.of_bound ((hsm t).mono (S.𝓕.le t)).aestronglyMeasurable C
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hsC t ω)
  have hE : ∀ j, ∀ᵐ ω ∂S.μ, |S.E t (s (t + j)) ω| ≤ C := fun j =>
    S.abs_E_le (Eventually.of_forall fun ω => hsC (t + j) ω) t
  filter_upwards [ae_all_iff.2 (value_partial S hflow hbm hbi hsi t), htvc t, ae_all_iff.2 hE]
    with ω h1 h2 h3
  have hC : 0 ≤ C := (abs_nonneg _).trans (hsC 0 ω)
  have hpart : Tendsto (fun k => ∑ j ∈ Finset.range k, β ^ j * S.E t (s (t + j)) ω) atTop
      (𝓝 (b t ω)) := by
    have := (tendsto_const_nhds (x := b t ω)).sub h2
    rw [sub_zero] at this
    exact this.congr fun k => by linarith [h1 k]
  have hgeo := summable_geometric_of_lt_one hβ0.le hβ1
  refine le_of_tendsto' hpart.abs fun k => ?_
  calc |∑ j ∈ Finset.range k, β ^ j * S.E t (s (t + j)) ω|
      ≤ ∑ j ∈ Finset.range k, |β ^ j * S.E t (s (t + j)) ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range k, β ^ j * C := Finset.sum_le_sum fun j _ => by
        rw [abs_mul, abs_of_pos (pow_pos hβ0 j)]
        exact mul_le_mul_of_nonneg_left (h3 j) (pow_pos hβ0 j).le
    _ = C * ∑ j ∈ Finset.range k, β ^ j := by rw [Finset.mul_sum]; ring_nf
    _ ≤ C * ∑' j, β ^ j := mul_le_mul_of_nonneg_left
        (hgeo.sum_le_tsum _ fun j _ => pow_nonneg hβ0.le j) hC
    _ = C / (1 - β) := by rw [tsum_geometric_of_lt_one hβ0.le hβ1, div_eq_mul_inv]

/-- Cochrane (2023), eq. (9.12), p. 267 (the key step of Theorem FR (d) with any target): let `P`,
`P'` be positive with the same interest-rate relation `P_s E_s(1/P_{s+1}) = P'_s E_s(1/P'_{s+1})`.
If `P_s < P'_s` on a date-`s` event `A` of positive probability, then `P_{s+1} < P'_{s+1}` on a
positive-probability part of `A`: a price below the comparison path today forces a price below it
tomorrow in some state. -/
theorem child_lt {s : ℕ} {P P' : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω) (hP' : ∀ t ω, 0 < P' t ω)
    (hq : Integrable (fun ω => 1 / P (s + 1) ω) S.μ)
    (hq' : Integrable (fun ω => 1 / P' (s + 1) ω) S.μ)
    (hr : ∀ᵐ ω ∂S.μ, P s ω * S.E s (fun ω => 1 / P (s + 1) ω) ω =
      P' s ω * S.E s (fun ω => 1 / P' (s + 1) ω) ω)
    {A : Set Ω} (hA : MeasurableSet[S.𝓕 s] A) (hA0 : 0 < S.μ A)
    (hlt : ∀ ω ∈ A, P s ω < P' s ω) :
    0 < S.μ (A ∩ {ω | P (s + 1) ω < P' (s + 1) ω}) := by
  by_contra hcon
  have h0 : S.μ (A ∩ {ω | P (s + 1) ω < P' (s + 1) ω}) = 0 := le_antisymm (not_lt.1 hcon) bot_le
  rw [measure_eq_zero_iff_ae_notMem] at h0
  set q : Ω → ℝ := fun ω => 1 / P (s + 1) ω with hq_def
  set q' : Ω → ℝ := fun ω => 1 / P' (s + 1) ω with hq'_def
  have hAm : MeasurableSet A := S.𝓕.le s A hA
  have hind : A.indicator q ≤ᵐ[S.μ] A.indicator q' := by
    filter_upwards [h0] with ω h
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      have hle : P' (s + 1) ω ≤ P (s + 1) ω := by
        by_contra h'
        exact h ⟨hω, not_le.1 h'⟩
      exact one_div_le_one_div_of_le (hP' (s + 1) ω) hle
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
  have hmono := S.E_mono (hq.indicator hAm) (hq'.indicator hAm) hind s
  have hi1 : S.E s (A.indicator q) =ᵐ[S.μ] A.indicator (S.E s q) := condExp_indicator hq hA
  have hi2 : S.E s (A.indicator q') =ᵐ[S.μ] A.indicator (S.E s q') := condExp_indicator hq' hA
  have hnn : ∀ᵐ ω ∂S.μ, 0 ≤ S.E s q' ω := by
    have h := S.E_mono (integrable_const 0) hq'
      (Eventually.of_forall fun ω => (one_div_pos.2 (hP' (s + 1) ω)).le) s
    rw [S.E_const] at h
    exact h
  have hzero : ∀ᵐ ω ∂S.μ, ω ∈ A → S.E s q' ω = 0 := by
    filter_upwards [hmono, hi1, hi2, hnn, hr] with ω e1 e2 e3 e4 e5 hω
    rw [e2, e3, Set.indicator_of_mem hω, Set.indicator_of_mem hω] at e1
    have hlt' := hlt ω hω
    have hPs := hP s ω
    have : (P' s ω - P s ω) * S.E s q' ω ≤ 0 := by
      have := mul_le_mul_of_nonneg_left e1 hPs.le
      change P s ω * S.E s q ω = P' s ω * S.E s q' ω at e5
      nlinarith
    have hpos : 0 < P' s ω - P s ω := by linarith
    have := nonpos_of_mul_nonpos_right this hpos
    linarith
  have hint0 : ∫ ω in A, S.E s q' ω ∂S.μ = 0 :=
    integral_eq_zero_of_ae ((ae_restrict_iff' hAm).2 hzero)
  rw [setIntegral_condExp (S.𝓕.le s) hq' hA] at hint0
  have hpos : 0 < ∫ ω in A, q' ω ∂S.μ := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall fun ω => (one_div_pos.2 (hP' (s + 1) ω)).le) hq'.integrableOn]
    have hsup : Function.support q' = Set.univ :=
      Set.eq_univ_of_forall fun ω => (one_div_pos.2 (hP' (s + 1) ω)).ne'
    rwa [hsup, Set.univ_inter]
  linarith

/-- Cochrane (2023), eqs. (9.8), (9.12), pp. 266–267 (Theorem FR (d), **the growth argument**): let
`P`, `P'` be positive adapted price paths with the same interest-rate relation, and let the scaled
debt difference `Δ_t = (b_t − b'_t)/θ` obey `Δ_t = P_t − P'_t + β Δ_{t+1}`, be predetermined and
bounded. If `Δ_t = 0` a.e. then `Δ_{t+1} ≤ 0` a.e. Otherwise `P_t < P'_t` on an event of positive
probability, `child_lt` propagates `P < P'` to a positive-probability event at every later date, and
along it `Δ_{t+k+1} > δ/βᵏ`, contradicting boundedness. -/
theorem compare_step {β B : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {P P' Δ : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (hP' : ∀ t ω, 0 < P' t ω)
    (hPa : StronglyAdapted S.𝓕 P) (hP'a : StronglyAdapted S.𝓕 P')
    (hq : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ)
    (hq' : ∀ t, Integrable (fun ω => 1 / P' t ω) S.μ)
    (hr : ∀ t, ∀ᵐ ω ∂S.μ, P t ω * S.E t (fun ω => 1 / P (t + 1) ω) ω =
      P' t ω * S.E t (fun ω => 1 / P' (t + 1) ω) ω)
    (hΔ : ∀ t ω, Δ t ω = P t ω - P' t ω + β * Δ (t + 1) ω)
    (hΔm : ∀ t, StronglyMeasurable[S.𝓕 t] (Δ (t + 1)))
    (hΔB : ∀ t, ∀ᵐ ω ∂S.μ, |Δ t ω| ≤ B) {t : ℕ} (h0 : ∀ᵐ ω ∂S.μ, Δ t ω = 0) :
    ∀ᵐ ω ∂S.μ, Δ (t + 1) ω ≤ 0 := by
  by_contra hcon
  have hΔm' : ∀ t, StronglyMeasurable[S.𝓕 t] (Δ t) := fun t => by
    have e : Δ t = fun ω => P t ω - P' t ω + β * Δ (t + 1) ω := funext (hΔ t)
    rw [e]
    exact ((hPa t).sub (hP'a t)).add ((hΔm t).const_mul β)
  -- a positive threshold `δ`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, S.μ {ω | 1 / ((n : ℝ) + 1) < Δ (t + 1) ω} ≠ 0 := by
    by_contra h
    push Not at h
    apply hcon
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) (measure_iUnion_null h)
    simp only [Set.mem_ofPred_eq, not_le] at hω
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hω
    exact Set.mem_iUnion.2 ⟨k, hk⟩
  set δ : ℝ := 1 / ((n : ℝ) + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  -- the propagation
  have key : ∀ k : ℕ, ∃ A : Set Ω, MeasurableSet[S.𝓕 (t + k)] A ∧ 0 < S.μ A ∧
      ∀ ω ∈ A, P (t + k) ω < P' (t + k) ω ∧ δ / β ^ k < Δ (t + k + 1) ω := by
    intro k
    induction k with
    | zero =>
      refine ⟨{ω | δ < Δ (t + 1) ω} ∩ {ω | Δ t ω = 0}, ?_, ?_, fun ω hω => ?_⟩
      · exact (measurableSet_lt stronglyMeasurable_const.measurable (hΔm t).measurable).inter
          (measurableSet_eq_fun (hΔm' t).measurable measurable_const)
      · have he : ({ω | δ < Δ (t + 1) ω} ∩ {ω | Δ t ω = 0} : Set Ω) =ᵐ[S.μ]
            {ω | δ < Δ (t + 1) ω} := by
          filter_upwards [h0] with ω hω
          exact propext ⟨fun h => h.1, fun h => ⟨h, hω⟩⟩
        rw [measure_congr he]
        exact pos_iff_ne_zero.2 hn
      · obtain ⟨h1, h2⟩ := hω
        simp only [Set.mem_ofPred_eq] at h1 h2
        have e := hΔ t ω
        rw [h2] at e
        simp only [add_zero, pow_zero, div_one]
        exact ⟨by nlinarith, h1⟩
    | succ k ih =>
      obtain ⟨A, hAm, hA0, hA⟩ := ih
      refine ⟨A ∩ {ω | P (t + k + 1) ω < P' (t + k + 1) ω}, ?_, ?_, fun ω hω => ?_⟩
      · exact (S.𝓕.mono (Nat.le_succ (t + k)) A hAm).inter
          (measurableSet_lt (hPa (t + k + 1)).measurable (hP'a (t + k + 1)).measurable)
      · exact child_lt S hP hP' (hq (t + k + 1)) (hq' (t + k + 1)) (hr (t + k)) hAm hA0
          fun ω hω => (hA ω hω).1
      · obtain ⟨h1, h2⟩ := hω
        simp only [Set.mem_ofPred_eq] at h2
        obtain ⟨-, h3⟩ := hA ω h1
        have e := hΔ (t + k + 1) ω
        rw [show t + (k + 1) = t + k + 1 by ring]
        refine ⟨h2, ?_⟩
        have hβk : 0 < β ^ k := pow_pos hβ0 k
        have h4 : δ / β ^ k / β < Δ (t + k + 1) ω / β := div_lt_div_of_pos_right h3 hβ0
        rw [div_div, ← pow_succ] at h4
        refine h4.trans ?_
        rw [div_lt_iff₀ hβ0]
        linarith
  -- contradiction with boundedness
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hδ0 (by positivity : (0 : ℝ) < |B| + 1)) hβ1
  obtain ⟨A, -, hA0, hA⟩ := key k
  have hnull : S.μ A = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 (hΔB (t + k + 1)))
    simp only [Set.mem_ofPred_eq, not_le]
    have hβk : 0 < β ^ k := pow_pos hβ0 k
    have h1 := (hA ω hω).2
    have h2 : |B| + 1 < δ / β ^ k := by
      rw [lt_div_iff₀ hβk]
      rw [lt_div_iff₀ (by positivity)] at hk
      linarith
    exact lt_of_le_of_lt (le_abs_self B) (by linarith [le_abs_self (Δ (t + k + 1) ω)])
  exact absurd hnull hA0.ne'

/-- Cochrane (2023), §9.3.2, eqs. (9.8), (9.9), (9.12), pp. 266–267: an equilibrium of the surplus
rule `s_t = s_{0,t} + θ (P_t − P*_t)` with a **general** underlying surplus process `s₀` (the book's
`s_{0,t} = a(L) ε_{s,t}`), indexed debt and the interest-rate target — as `RuleEqm`, whose `s₀` is
the constant `(1 − β) b̄`: positive adapted integrable prices, (9.12), the flow (9.8) on every path,
predetermined integrable debt, the valuation (9.9) as a genuine `HasSum` and the transversality
condition (a.e.). -/
def RuleEqmGen (S : MeasExpectationSystem Ω) (β θ : ℝ) (s0 Pstar P b : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, 0 < P t ω) ∧ StronglyAdapted S.𝓕 P ∧ (∀ t, Integrable (P t) S.μ) ∧
    (∀ t, Integrable (b t) S.μ) ∧
    (∀ t, S.E t (P t / P (t + 1)) =ᵐ[S.μ] S.E t (Pstar t / Pstar (t + 1))) ∧
    (∀ t ω, b t ω = s0 t ω + θ * (P t ω - Pstar t ω) + β * b (t + 1) ω) ∧
    (∀ t, StronglyMeasurable[S.𝓕 t] (b (t + 1))) ∧
    (∀ t, ∀ᵐ ω ∂S.μ, HasSum (fun j => β ^ j * S.E t
      (fun ω' => s0 (t + j) ω' + θ * (P (t + j) ω' - Pstar (t + j) ω')) ω) (b t ω)) ∧
    ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun T => β ^ T * S.E t (b (t + T)) ω) atTop (𝓝 0)

/-- Cochrane (2023), §9.3.2, p. 266 (**link**): `RuleEqm` is `RuleEqmGen` with the constant
underlying surplus `s_{0,t} = (1 − β) b̄`. -/
theorem ruleEqm_iff_gen {β θ bbar : ℝ} {Pstar P b : ℕ → Ω → ℝ} :
    RuleEqm S β θ bbar Pstar P b ↔
      RuleEqmGen S β θ (fun _ _ => (1 - β) * bbar) Pstar P b := Iff.rfl

/-- Cochrane (2023), eq. (9.9), p. 266: if `B_t = s_t + β B_{t+1}` on every path with `B`
bounded and predetermined and `s` adapted and bounded, then `∑ⱼ βʲ E_t s_{t+j} = B_t` a.e. (a
genuine `HasSum`): `B` is the expected present value of `s`. -/
theorem hasSum_E_value {β C K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {s B : ℕ → Ω → ℝ}
    (hsm : ∀ t, StronglyMeasurable[S.𝓕 t] (s t)) (hsC : ∀ t ω, |s t ω| ≤ C)
    (hB : ∀ t ω, B t ω = s t ω + β * B (t + 1) ω)
    (hBpre : ∀ t, StronglyMeasurable[S.𝓕 t] (B (t + 1))) (hBK : ∀ t ω, |B t ω| ≤ K) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun j => β ^ j * S.E t (s (t + j)) ω) (B t ω) := by
  have hBm : ∀ t, StronglyMeasurable[S.𝓕 t] (B t) := fun t => by
    have e : B t = fun ω => s t ω + β * B (t + 1) ω := funext (hB t)
    rw [e]
    exact (hsm t).add ((hBpre t).const_mul β)
  have hBi : ∀ t, Integrable (B t) S.μ := fun t =>
    Integrable.of_bound ((hBm t).mono (S.𝓕.le t)).aestronglyMeasurable K
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hBK t ω)
  have hsi : ∀ t, Integrable (s t) S.μ := fun t =>
    Integrable.of_bound ((hsm t).mono (S.𝓕.le t)).aestronglyMeasurable C
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hsC t ω)
  have hE : ∀ j, ∀ᵐ ω ∂S.μ, |S.E t (s (t + j)) ω| ≤ C := fun j =>
    S.abs_E_le (Eventually.of_forall fun ω => hsC (t + j) ω) t
  have hEK : ∀ k, ∀ᵐ ω ∂S.μ, |S.E t (B (t + k)) ω| ≤ K := fun k =>
    S.abs_E_le (Eventually.of_forall fun ω => hBK (t + k) ω) t
  filter_upwards [ae_all_iff.2 (value_partial S hB hBm hBi hsi t), ae_all_iff.2 hE,
    ae_all_iff.2 hEK] with ω h1 h2 h3
  have hg := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1
  have hrem : Tendsto (fun k => β ^ k * S.E t (B (t + k)) ω) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun k => ?_) (by simpa using hg.mul_const K)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 k)]
    exact mul_le_mul_of_nonneg_left (h3 k) (pow_pos hβ0 k).le
  have hpart : Tendsto (fun k => ∑ j ∈ Finset.range k, β ^ j * S.E t (s (t + j)) ω) atTop
      (𝓝 (B t ω)) := by
    have := (tendsto_const_nhds (x := B t ω)).sub hrem
    rw [sub_zero] at this
    exact this.congr fun k => by linarith [h1 k]
  have hsum : Summable (fun j => β ^ j * S.E t (s (t + j)) ω) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right C) fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 j)]
      exact mul_le_mul_of_nonneg_left (h2 j) (pow_pos hβ0 j).le
  have he := tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hpart
  rw [← he]
  exact hsum.hasSum

/-- Cochrane (2023), §9.3.2, p. 266 (existence, `P = P*`): if the underlying surplus `s₀` is adapted
and bounded and its present value is predetermined — a bounded `B` with `B_t = s_{0,t} + β B_{t+1}`
and `B_{t+1}` known at `t` (the book's `a(β) = 0`) — then for **any** positive adapted integrable
target, `P = P*` with real debt `b = B` is an equilibrium of the rule (`RuleEqmGen`). -/
theorem target_ruleEqmGen {β θ C K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {s0 B Pstar : ℕ → Ω → ℝ}
    (hs0m : ∀ t, StronglyMeasurable[S.𝓕 t] (s0 t)) (hs0C : ∀ t ω, |s0 t ω| ≤ C)
    (hB : ∀ t ω, B t ω = s0 t ω + β * B (t + 1) ω)
    (hBpre : ∀ t, StronglyMeasurable[S.𝓕 t] (B (t + 1))) (hBK : ∀ t ω, |B t ω| ≤ K)
    (hPs : ∀ t ω, 0 < Pstar t ω) (hPsa : StronglyAdapted S.𝓕 Pstar)
    (hPsi : ∀ t, Integrable (Pstar t) S.μ) : RuleEqmGen S β θ s0 Pstar Pstar B := by
  have hBm : ∀ t, StronglyMeasurable[S.𝓕 t] (B t) := fun t => by
    have e : B t = fun ω => s0 t ω + β * B (t + 1) ω := funext (hB t)
    rw [e]
    exact (hs0m t).add ((hBpre t).const_mul β)
  refine ⟨hPs, hPsa, hPsi, fun t => Integrable.of_bound
    ((hBm t).mono (S.𝓕.le t)).aestronglyMeasurable K
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hBK t ω),
    fun t => EventuallyEq.rfl, fun t ω => by rw [hB t ω]; ring, hBpre, fun t => ?_, fun t => ?_⟩
  · simp only [sub_self, mul_zero, add_zero]
    exact hasSum_E_value S hβ0 hβ1 hs0m hs0C hB hBpre hBK t
  · filter_upwards [ae_all_iff.2 fun k =>
      S.abs_E_le (Eventually.of_forall fun ω => hBK (t + k) ω) t] with ω h
    refine squeeze_zero_norm (fun k => ?_)
      (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const K)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 k)]
    exact mul_le_mul_of_nonneg_left (h k) (pow_pos hβ0 k).le

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d), comparison form**): on any
measure-theoretic system, two equilibria of the rule with the **same** underlying surplus `s₀`, the
same target `P*` and the same initial debt (a.e.), whose prices are bounded above, coincide: `P =
P'` and `b = b'` a.e. at every date. No condition on `s₀` or on the target (its present value may
carry news) is needed. -/
theorem fr_compare {β θ M M' : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {s0 Pstar P P' b b' : ℕ → Ω → ℝ}
    (hE : RuleEqmGen S β θ s0 Pstar P b) (hE' : RuleEqmGen S β θ s0 Pstar P' b')
    (hPM : ∀ t ω, P t ω ≤ M) (hP'M : ∀ t ω, P' t ω ≤ M')
    (hq : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ)
    (hq' : ∀ t, Integrable (fun ω => 1 / P' t ω) S.μ)
    (hb0 : b 0 =ᵐ[S.μ] b' 0) (t : ℕ) : P t =ᵐ[S.μ] P' t ∧ b t =ᵐ[S.μ] b' t := by
  obtain ⟨hP, hPa, -, hbi, hrate, hflow, hpre, -, htvc⟩ := hE
  obtain ⟨hP', hP'a, -, hbi', hrate', hflow', hpre', -, htvc'⟩ := hE'
  -- the pulled-out interest-rate relation
  have hpull : ∀ {Q : ℕ → Ω → ℝ} {MQ : ℝ}, (∀ t ω, 0 < Q t ω) → StronglyAdapted S.𝓕 Q →
      (∀ t ω, Q t ω ≤ MQ) → (∀ t, Integrable (fun ω => 1 / Q t ω) S.μ) → ∀ t,
      S.E t (Q t / Q (t + 1)) =ᵐ[S.μ] Q t * S.E t (fun ω => 1 / Q (t + 1) ω) := by
    intro Q MQ hQ hQa hQM hQq t
    have e : Q t / Q (t + 1) = Q t * fun ω => 1 / Q (t + 1) ω := by
      funext ω
      simp [div_eq_mul_inv]
    rw [e]
    exact S.E_pullOut (hQa t) (C := MQ) (Eventually.of_forall fun ω => by
      rw [abs_of_pos (hQ t ω)]; exact hQM t ω) (hQq (t + 1))
  have hr : ∀ t, ∀ᵐ ω ∂S.μ, P t ω * S.E t (fun ω => 1 / P (t + 1) ω) ω =
      P' t ω * S.E t (fun ω => 1 / P' (t + 1) ω) ω := fun t => by
    filter_upwards [hpull hP hPa hPM hq t, hpull hP' hP'a hP'M hq' t, hrate t, hrate' t]
      with ω e1 e2 e3 e4
    rw [Pi.mul_apply] at e1 e2
    rw [← e1, ← e2, e3, e4]
  -- the scaled debt difference
  set Δ : ℕ → Ω → ℝ := fun t ω => θ⁻¹ * (b t ω - b' t ω) with hΔ_def
  have hΔ : ∀ t ω, Δ t ω = P t ω - P' t ω + β * Δ (t + 1) ω := fun t ω => by
    simp only [hΔ_def]
    rw [hflow t ω, hflow' t ω]
    field_simp
    ring
  have hΔm : ∀ t, StronglyMeasurable[S.𝓕 t] (Δ (t + 1)) := fun t =>
    ((hpre t).sub (hpre' t)).const_mul θ⁻¹
  -- the debt difference is bounded
  set d : ℕ → Ω → ℝ := fun t ω => b t ω - b' t ω with hd_def
  have hdflow : ∀ t ω, d t ω = θ * (P t ω - P' t ω) + β * d (t + 1) ω := fun t ω => by
    simp only [hd_def]
    rw [hflow t ω, hflow' t ω]
    ring
  have hsm : ∀ t, StronglyMeasurable[S.𝓕 t] (fun ω => θ * (P t ω - P' t ω)) := fun t =>
    ((hPa t).sub (hP'a t)).const_mul θ
  have hsC : ∀ t ω, |θ * (P t ω - P' t ω)| ≤ |θ| * (|M| + |M'|) := fun t ω => by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg θ)
    rw [abs_le]
    have := hP t ω
    have := hP' t ω
    have := hPM t ω
    have := hP'M t ω
    have := le_abs_self M
    have := le_abs_self M'
    constructor <;> linarith
  have hdpre : ∀ t, StronglyMeasurable[S.𝓕 t] (d (t + 1)) := fun t => (hpre t).sub (hpre' t)
  have hdi : ∀ t, Integrable (d t) S.μ := fun t => (hbi t).sub (hbi' t)
  have hdtvc : ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun T => β ^ T * S.E t (d (t + T)) ω) atTop (𝓝 0) := by
    intro t
    filter_upwards [htvc t, htvc' t,
      ae_all_iff.2 fun T => S.E_sub (hbi (t + T)) (hbi' (t + T)) t] with ω e1 e2 e3
    have := e1.sub e2
    rw [sub_zero] at this
    refine this.congr fun T => ?_
    change _ = β ^ T * S.E t (b (t + T) - b' (t + T)) ω
    rw [e3 T, Pi.sub_apply]
    ring
  have hdB := debt_bdd S hβ0 hβ1 (s := fun t ω => θ * (P t ω - P' t ω)) hsm hsC hdflow hdpre
    hdi hdtvc
  have hΔB : ∀ t, ∀ᵐ ω ∂S.μ, |Δ t ω| ≤ |θ|⁻¹ * (|θ| * (|M| + |M'|) / (1 - β)) := fun t => by
    filter_upwards [hdB t] with ω h
    simp only [hΔ_def]
    rw [abs_mul, abs_inv]
    exact mul_le_mul_of_nonneg_left h (inv_nonneg.2 (abs_nonneg θ))
  -- induction: `Δ ≡ 0`
  have hz : ∀ t, ∀ᵐ ω ∂S.μ, Δ t ω = 0 := by
    intro t
    induction t with
    | zero =>
      filter_upwards [hb0] with ω h
      simp only [hΔ_def, h, sub_self, mul_zero]
    | succ t ih =>
      have h1 := compare_step S hβ0 hβ1 hP hP' hPa hP'a hq hq' hr hΔ hΔm hΔB ih
      have h2 := compare_step S hβ0 hβ1 (Δ := fun t ω => -Δ t ω) hP' hP hP'a hPa hq' hq
        (fun t => (hr t).mono fun ω h => h.symm) (fun t ω => by rw [hΔ t ω]; ring)
        (fun t => (hΔm t).neg) (fun t => (hΔB t).mono fun ω h => by rwa [abs_neg])
        (ih.mono fun ω h => by rw [h, neg_zero])
      filter_upwards [h1, h2] with ω e1 e2
      linarith
  refine ⟨?_, ?_⟩
  · filter_upwards [hz t, hz (t + 1)] with ω e1 e2
    have := hΔ t ω
    rw [e1, e2] at this
    linarith
  · filter_upwards [hz t] with ω e
    simp only [hΔ_def] at e
    have := (mul_eq_zero.1 e).resolve_left (inv_ne_zero hθ)
    linarith

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d) with a news-bearing target, general
`s₀`**): let the underlying surplus `s₀` be adapted and bounded with predetermined present value `B`
(`a(β) = 0`), and let the target be **any** adapted process with `0 < m ≤ P* ≤ M*` — its present
value may carry news. If initial debt equals the present value of `s₀` (`b₀ = B₀` a.e.), every
equilibrium with prices bounded above has `P = P*` and `b = B` a.e. at every date. -/
theorem fr_unique_news {β θ C K m Ms M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {s0 B Pstar P b : ℕ → Ω → ℝ}
    (hs0m : ∀ t, StronglyMeasurable[S.𝓕 t] (s0 t)) (hs0C : ∀ t ω, |s0 t ω| ≤ C)
    (hB : ∀ t ω, B t ω = s0 t ω + β * B (t + 1) ω)
    (hBpre : ∀ t, StronglyMeasurable[S.𝓕 t] (B (t + 1))) (hBK : ∀ t ω, |B t ω| ≤ K)
    (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hE : RuleEqmGen S β θ s0 Pstar P b) (hPM : ∀ t ω, P t ω ≤ M)
    (hq : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ) (hb0 : b 0 =ᵐ[S.μ] B 0) (t : ℕ) :
    P t =ᵐ[S.μ] Pstar t ∧ b t =ᵐ[S.μ] B t := by
  have hPs0 : ∀ t ω, 0 < Pstar t ω := fun t ω => hm.trans_le (hPs t ω).1
  have hPsi : ∀ t, Integrable (Pstar t) S.μ := fun t =>
    Integrable.of_bound ((hPsa t).mono (S.𝓕.le t)).aestronglyMeasurable Ms
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (hPs0 t ω)]; exact (hPs t ω).2)
  have hqs : ∀ t, Integrable (fun ω => 1 / Pstar t ω) S.μ := fun t =>
    Integrable.of_bound (((hPsa t).measurable.const_div 1).stronglyMeasurable.mono
      (S.𝓕.le t)).aestronglyMeasurable (1 / m)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (hPs0 t ω))]
        exact one_div_le_one_div_of_le hm (hPs t ω).1)
  exact fr_compare S hβ0 hβ1 hθ hE
    (target_ruleEqmGen S hβ0 hβ1 (θ := θ) hs0m hs0C hB hBpre hBK hPs0 hPsa hPsi) hPM
    (fun t ω => (hPs t ω).2) hq hqs hb0 t

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d), `b₀ = b̄`, target with news —
settled**): on any measure-theoretic system and for any adapted target `0 < m ≤ P* ≤ M*` (no
condition on its present value), `P = P*` with `b ≡ b̄` is an equilibrium (`RuleEqm`), and it is the
**unique** equilibrium with prices bounded above and initial debt `b₀ = b̄`. -/
theorem fr_d_news {β θ bbar m Ms : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {Pstar : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms) :
    RuleEqm S β θ bbar Pstar Pstar (fun _ _ => bbar) ∧
      ∀ P b : ℕ → Ω → ℝ, RuleEqm S β θ bbar Pstar P b → (∃ M, ∀ t ω, P t ω ≤ M) →
        (∀ t, Integrable (fun ω => 1 / P t ω) S.μ) → (∀ ω, b 0 ω = bbar) →
        ∀ t, P t =ᵐ[S.μ] Pstar t ∧ b t =ᵐ[S.μ] fun _ => bbar := by
  have hPs0 : ∀ t ω, 0 < Pstar t ω := fun t ω => hm.trans_le (hPs t ω).1
  have hPsi : ∀ t, Integrable (Pstar t) S.μ := fun t =>
    Integrable.of_bound ((hPsa t).mono (S.𝓕.le t)).aestronglyMeasurable Ms
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (hPs0 t ω)]; exact (hPs t ω).2)
  have hB : ∀ t (ω : Ω), (fun _ _ => bbar : ℕ → Ω → ℝ) t ω =
      (fun _ _ => (1 - β) * bbar : ℕ → Ω → ℝ) t ω +
        β * (fun _ _ => bbar : ℕ → Ω → ℝ) (t + 1) ω := fun _ _ => by ring
  refine ⟨(ruleEqm_iff_gen S).2 (target_ruleEqmGen S hβ0 hβ1 (C := |(1 - β) * bbar|)
    (K := |bbar|) (fun _ => stronglyMeasurable_const) (fun _ _ => le_rfl) hB
    (fun _ => stronglyMeasurable_const) (fun _ _ => le_rfl) hPs0 hPsa hPsi),
    fun P b hE ⟨M, hPM⟩ hq hb0 t => ?_⟩
  exact fr_unique_news S hβ0 hβ1 hθ (C := |(1 - β) * bbar|) (K := |bbar|)
    (fun _ => stronglyMeasurable_const) (fun _ _ => le_rfl) hB
    (fun _ => stronglyMeasurable_const) (fun _ _ => le_rfl) hPsa hm hPs
    ((ruleEqm_iff_gen S).1 hE) hPM hq (Eventually.of_forall hb0) t

/-- Cochrane (2023), §9.3.2, pp. 266–267 (Theorem FR (d), **link**): on a finite fully supported
system, the hypotheses of the core `FiscalRules.fr_unique_bounded` (bounded-above case, `P* ≡ 1`,
stated for the bridged core system) give `P ≡ 1` through the news-robust theorem `fr_d_news`, which
needs no predetermined target value — so it specialises to (and agrees with) the core result. -/
theorem fr_d_news_link [Finite Ω] [DiscreteMeasurableSpace Ω]
    (hfull : ∀ ω, S.μ {ω} ≠ 0) {β θ bbar M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {P b : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω) (hPa : (S.toExpectationSystem hfull).Adapted P)
    (h912 : ∀ t, β • (S.toExpectationSystem hfull).E t (P t / P (t + 1)) = fun _ => β)
    (hflow : ∀ t ω, b t ω = (1 - β) * bbar + θ * (P t ω - 1) + β * b (t + 1) ω)
    (hpre : ∀ t, (S.toExpectationSystem hfull).E t (b (t + 1)) = b (t + 1))
    (hb0 : ∀ ω, b 0 ω = bbar)
    (htvc : ∀ t ω, Tendsto (fun T => β ^ T * (S.toExpectationSystem hfull).E t (b (t + T)) ω)
      atTop (𝓝 0)) (hM : ∀ t ω, P t ω ≤ M) :
    P = fun _ _ => 1 := by
  have hsm : ∀ t (x : Ω → ℝ), S.E t x = x → StronglyMeasurable[S.𝓕 t] x := fun t x h => by
    have := S.stronglyMeasurable_E t x
    rwa [h] at this
  have hrate : ∀ t, S.E t (P t / P (t + 1)) =ᵐ[S.μ]
      S.E t ((fun _ _ => (1 : ℝ)) t / (fun _ _ => (1 : ℝ)) (t + 1)) := fun t => by
    refine EventuallyEq.of_eq ?_
    have h := h912 t
    rw [S.toExpectationSystem_E] at h
    have e : ((fun _ _ => (1 : ℝ)) t / (fun _ _ => (1 : ℝ)) (t + 1) : Ω → ℝ) = fun _ => 1 := by
      funext ω
      simp
    rw [e, S.E_const]
    funext ω
    have := congrFun h ω
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hβ0.ne' (this.trans (mul_one β).symm)
  have hPm : StronglyAdapted S.𝓕 P := fun t => hsm t _ (hPa t)
  have hE : RuleEqm S β θ bbar (fun _ _ => 1) P b := by
    refine ⟨hP, hPm, fun _ => Integrable.of_finite, fun _ => Integrable.of_finite, hrate,
      hflow, fun t => hsm t _ (hpre t), fun t => ?_, fun t => Eventually.of_forall (htvc t)⟩
    have hsm' : ∀ t, StronglyMeasurable[S.𝓕 t] (fun ω => (1 - β) * bbar + θ * (P t ω - 1)) :=
      fun t => stronglyMeasurable_const.add (((hPm t).sub stronglyMeasurable_const).const_mul θ)
    have hsC : ∀ t ω, |(1 - β) * bbar + θ * (P t ω - 1)| ≤ |(1 - β) * bbar| + |θ| * (|M| + 1) :=
      fun t ω => by
        refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg θ)
        rw [abs_le]
        have := hP t ω
        have := hM t ω
        have := le_abs_self M
        constructor <;> linarith
    have hbK : ∀ t ω, |b t ω| ≤ (|(1 - β) * bbar| + |θ| * (|M| + 1)) / (1 - β) := fun t ω =>
      S.le_of_ae_le hfull (f := fun ω => |b t ω|)
        (g := fun _ => (|(1 - β) * bbar| + |θ| * (|M| + 1)) / (1 - β))
        (debt_bdd S hβ0 hβ1 hsm' hsC hflow (fun t => hsm t _ (hpre t))
          (fun _ => Integrable.of_finite) (fun t => Eventually.of_forall (htvc t)) t) ω
    exact hasSum_E_value S hβ0 hβ1 hsm' hsC hflow (fun t => hsm t _ (hpre t)) hbK t
  funext t
  exact S.eq_of_ae_eq hfull ((fr_d_news S hβ0 hβ1 hθ (fun _ => stronglyMeasurable_const)
    one_pos (fun _ _ => ⟨le_rfl, le_rfl⟩)).2 P b hE ⟨M, hM⟩ (fun _ => Integrable.of_finite)
    hb0 t).1

namespace BoolNews

open BoolExample

/-- Cochrane (2023), §9.3.2, p. 267 (**the news case decided on the coin tree**): for the target
`Ps` of `BoolExample`, whose present value carries news (`no_targetValue`), every equilibrium of
the rule with prices bounded above is pinned down: with `b₀ = b̄` it is the target `P = P*`, and
with `b₀ = b̄ + θ/(1 − β)` it is `P = P* + 1` — unique, though not proportional to `P*`. -/
theorem bool_news_unique {β θ bbar M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {P b : ℕ → Bool → ℝ} (hE : RuleEqm boolSystem β θ bbar Ps P b)
    (hPM : ∀ t ω, P t ω ≤ M) :
    ((∀ ω, b 0 ω = bbar) → P = Ps) ∧ ((∀ ω, b 0 ω = bbar + θ / (1 - β)) → P = Pc) := by
  have hPsa : StronglyAdapted boolSystem.𝓕 Ps := bool_adapted Ps ⟨9 / 7, fun ω => by simp [Ps]⟩
  refine ⟨fun hb0 => ?_, fun hb0 => ?_⟩
  · funext t
    exact boolSystem.eq_of_ae_eq boolSystem_fullSupport ((fr_d_news boolSystem hβ0 hβ1 hθ
      hPsa one_pos Ps_bounds).2 P b hE ⟨M, hPM⟩ (fun _ => Integrable.of_finite) hb0 t).1
  · funext t
    refine boolSystem.eq_of_ae_eq boolSystem_fullSupport (fr_compare boolSystem hβ0 hβ1 hθ
      ((ruleEqm_iff_gen boolSystem).1 hE) ((ruleEqm_iff_gen boolSystem).1
        (bool_ruleEqm hβ0 hβ1 θ bbar)) hPM (M' := 4) (fun t ω => ?_)
      (fun _ => Integrable.of_finite) (fun _ => Integrable.of_finite)
      (Eventually.of_forall fun ω => by rw [hb0 ω]; rfl) t).1
    have := Ps_bounds t ω
    simp only [Pc]
    linarith

end BoolNews

/-! ### General underlying surplus `s₀` with `a(β) = 0` -/

/-- Cochrane (2023), eq. (9.9), p. 266 (supporting): if `b` satisfies the transversality condition
and `g` is integrable and bounded, then `b − g` satisfies it too. -/
theorem tvc_sub_bdd {β K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {b g : ℕ → Ω → ℝ}
    (hbi : ∀ t, Integrable (b t) S.μ) (hgi : ∀ t, Integrable (g t) S.μ)
    (hgK : ∀ t ω, |g t ω| ≤ K)
    (htvc : ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun T => β ^ T * S.E t (b (t + T)) ω) atTop (𝓝 0))
    (t : ℕ) : ∀ᵐ ω ∂S.μ, Tendsto (fun T => β ^ T * S.E t
      (fun ω => b (t + T) ω - g (t + T) ω) ω) atTop (𝓝 0) := by
  filter_upwards [htvc t, ae_all_iff.2 fun T => S.E_sub (hbi (t + T)) (hgi (t + T)) t,
    ae_all_iff.2 fun T => S.abs_E_le (Eventually.of_forall fun ω => hgK (t + T) ω) t]
    with ω e1 e2 e3
  have hg : Tendsto (fun T => β ^ T * S.E t (g (t + T)) ω) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun k => ?_)
      (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const K)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 k)]
    exact mul_le_mul_of_nonneg_left (e3 k) (pow_pos hβ0 k).le
  have := e1.sub hg
  rw [sub_zero] at this
  refine this.congr fun T => ?_
  change _ = β ^ T * S.E t (b (t + T) - g (t + T)) ω
  rw [e2 T, Pi.sub_apply]
  ring

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d) for a general `s₀` with `a(β) = 0`**,
prices bounded above): let `s₀` have the bounded predetermined present value `B` with `B₀` a known
number, and let the target have a predetermined present value `a`. Then every equilibrium with
initial debt `b₀` and bounded-above prices has `P_t = (1 + (b₀ − B₀)/(θ a₀)) P*_t` a.e.: the book's
`b̄` is replaced by the present value of `s₀`. -/
theorem fr_unique_s0 {β θ b0 B0 K m Ms M Ka : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {s0 B Pstar P b a : ℕ → Ω → ℝ}
    (hs0m : ∀ t, StronglyMeasurable[S.𝓕 t] (s0 t))
    (hB : ∀ t ω, B t ω = s0 t ω + β * B (t + 1) ω)
    (hBpre : ∀ t, StronglyMeasurable[S.𝓕 t] (B (t + 1))) (hBK : ∀ t ω, |B t ω| ≤ K)
    (hB0 : ∀ ω, B 0 ω = B0)
    (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (ha : ∀ t ω, a t ω = Pstar t ω + β * a (t + 1) ω)
    (hapre : ∀ t, StronglyMeasurable[S.𝓕 t] (a (t + 1))) (haK : ∀ t ω, |a t ω| ≤ Ka)
    (hE : RuleEqmGen S β θ s0 Pstar P b) (hPM : ∀ t ω, P t ω ≤ M)
    (hq : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ) (hb0 : ∀ ω, b 0 ω = b0) (t : ℕ) :
    P t =ᵐ[S.μ] fun ω => (1 + (b0 - B0) / (θ * a 0 ω)) * Pstar t ω := by
  obtain ⟨hP, hPa, -, hbi, hrate, hflow, hpre, -, htvc⟩ := hE
  have hBm : ∀ t, StronglyMeasurable[S.𝓕 t] (B t) := fun t => by
    have e : B t = fun ω => s0 t ω + β * B (t + 1) ω := funext (hB t)
    rw [e]
    exact (hs0m t).add ((hBpre t).const_mul β)
  have hBi : ∀ t, Integrable (B t) S.μ := fun t =>
    Integrable.of_bound ((hBm t).mono (S.𝓕.le t)).aestronglyMeasurable K
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hBK t ω)
  have h := fr_unique_stochastic S hβ0 hβ1 hθ (bbar := 0) (b0 := b0 - B0) (M := M) (K := Ka)
    (b := fun t ω => b t ω - B t ω) hP hPa hPM hq hPsa hm hPs ha hapre haK hrate
    (fun t ω => by rw [hflow t ω, hB t ω]; ring) (fun t => (hpre t).sub (hBpre t))
    (fun ω => by rw [hb0 ω, hB0 ω]) (fun t => (hbi t).sub (hBi t))
    (tvc_sub_bdd S hβ0 hβ1 hbi hBi hBK htvc) t
  filter_upwards [h] with ω e
  rw [e, sub_zero]

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d) for a general `s₀` with `a(β) = 0`**,
prices bounded away from zero): as `fr_unique_s0`, with prices `≥ m_P > 0` and integrable instead of
bounded above, under the bounded cumulative target real-rate hypothesis of
`fr_unique_stochastic_below` (which cannot be dropped: `FiscalRulesBelowCounter`). -/
theorem fr_unique_s0_below {β θ b0 B0 K m Ms mP Ka L : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 0) {s0 B Pstar P b a : ℕ → Ω → ℝ}
    (hs0m : ∀ t, StronglyMeasurable[S.𝓕 t] (s0 t))
    (hB : ∀ t ω, B t ω = s0 t ω + β * B (t + 1) ω)
    (hBpre : ∀ t, StronglyMeasurable[S.𝓕 t] (B (t + 1))) (hBK : ∀ t ω, |B t ω| ≤ K)
    (hB0 : ∀ ω, B 0 ω = B0)
    (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (ha : ∀ t ω, a t ω = Pstar t ω + β * a (t + 1) ω)
    (hapre : ∀ t, StronglyMeasurable[S.𝓕 t] (a (t + 1))) (haK : ∀ t ω, |a t ω| ≤ Ka)
    (hE : RuleEqmGen S β θ s0 Pstar P b) (hmP : 0 < mP) (hPmP : ∀ t ω, mP ≤ P t ω)
    (hL : ∀ t k, ∀ᵐ ω ∂S.μ, ∏ i ∈ Finset.range k,
      (Pstar (t + i) ω * S.E (t + i) (fun ω => 1 / Pstar (t + i + 1) ω) ω)⁻¹ ≤ L)
    (hb0 : ∀ ω, b 0 ω = b0) (t : ℕ) :
    P t =ᵐ[S.μ] fun ω => (1 + (b0 - B0) / (θ * a 0 ω)) * Pstar t ω := by
  obtain ⟨-, hPa, hPi, hbi, hrate, hflow, hpre, -, htvc⟩ := hE
  have hBm : ∀ t, StronglyMeasurable[S.𝓕 t] (B t) := fun t => by
    have e : B t = fun ω => s0 t ω + β * B (t + 1) ω := funext (hB t)
    rw [e]
    exact (hs0m t).add ((hBpre t).const_mul β)
  have hBi : ∀ t, Integrable (B t) S.μ := fun t =>
    Integrable.of_bound ((hBm t).mono (S.𝓕.le t)).aestronglyMeasurable K
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hBK t ω)
  have h := fr_unique_stochastic_below S hβ0 hβ1 hθ (bbar := 0) (b0 := b0 - B0) (K := Ka)
    (b := fun t ω => b t ω - B t ω) hPa hmP hPmP hPi hPsa hm hPs ha hapre haK hrate
    (fun t ω => by rw [hflow t ω, hB t ω]; ring) (fun t => (hpre t).sub (hBpre t))
    (fun ω => by rw [hb0 ω, hB0 ω]) (fun t => (hbi t).sub (hBi t))
    (tvc_sub_bdd S hβ0 hβ1 hbi hBi hBK htvc) hL t
  filter_upwards [h] with ω e
  rw [e, sub_zero]

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d) for a general `s₀`, random date-0
data**, prices bounded above): as `fr_unique_s0`, but initial debt `b₀` and the present value `B₀`
of `s₀` may be random (date-0 information need not be trivial), provided the implied factor
`c = 1 + (b₀ − B₀)/(θ a₀)` lies in `[c_min, c_max]` with `c_min > 0`. Then `P_t = c P*_t` a.e.
Proof: `c P*` is a target with predetermined present value `c a`, the same interest-rate target,
and initial debt exactly equal to the present value of `s₀` plus `θ (c − 1) a`. -/
theorem fr_unique_s0_random {β θ K m Ms M Ka cmin cmax : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 0) {s0 B Pstar P b a : ℕ → Ω → ℝ}
    (hs0m : ∀ t, StronglyMeasurable[S.𝓕 t] (s0 t))
    (hB : ∀ t ω, B t ω = s0 t ω + β * B (t + 1) ω)
    (hBpre : ∀ t, StronglyMeasurable[S.𝓕 t] (B (t + 1))) (hBK : ∀ t ω, |B t ω| ≤ K)
    (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (ha : ∀ t ω, a t ω = Pstar t ω + β * a (t + 1) ω)
    (hapre : ∀ t, StronglyMeasurable[S.𝓕 t] (a (t + 1))) (haK : ∀ t ω, |a t ω| ≤ Ka)
    (hE : RuleEqmGen S β θ s0 Pstar P b) (hPM : ∀ t ω, P t ω ≤ M)
    (hq : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ) (hcmin : 0 < cmin)
    (hc : ∀ ω, cmin ≤ 1 + (b 0 ω - B 0 ω) / (θ * a 0 ω) ∧
      1 + (b 0 ω - B 0 ω) / (θ * a 0 ω) ≤ cmax) (t : ℕ) :
    P t =ᵐ[S.μ] fun ω => (1 + (b 0 ω - B 0 ω) / (θ * a 0 ω)) * Pstar t ω := by
  obtain ⟨hP, hPa, -, hbi, hrate, hflow, hpre, -, htvc⟩ := hE
  have hBm : ∀ t, StronglyMeasurable[S.𝓕 t] (B t) := fun t => by
    have e : B t = fun ω => s0 t ω + β * B (t + 1) ω := funext (hB t)
    rw [e]
    exact (hs0m t).add ((hBpre t).const_mul β)
  have hBi : ∀ t, Integrable (B t) S.μ := fun t =>
    Integrable.of_bound ((hBm t).mono (S.𝓕.le t)).aestronglyMeasurable K
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hBK t ω)
  have ham : ∀ t, StronglyMeasurable[S.𝓕 t] (a t) := targetValue_adapted S hPsa ha hapre
  have hapos : ∀ t ω, 0 < a t ω := fun t ω =>
    (div_pos hm (by linarith)).trans_le (targetValue_ge hβ0 hβ1 (fun t ω => (hPs t ω).1) ha haK t ω)
  have hb0m : StronglyMeasurable[S.𝓕 0] (b 0) := by
    have e : b 0 = fun ω => s0 0 ω + θ * (P 0 ω - Pstar 0 ω) + β * b (0 + 1) ω := funext (hflow 0)
    rw [e]
    exact ((hs0m 0).add (((hPa 0).sub (hPsa 0)).const_mul θ)).add ((hpre 0).const_mul β)
  set c : Ω → ℝ := fun ω => 1 + (b 0 ω - B 0 ω) / (θ * a 0 ω) with hc_def
  have hcm : ∀ t, StronglyMeasurable[S.𝓕 t] c := fun t =>
    ((measurable_const.add ((hb0m.measurable.sub (hBm 0).measurable).div
      ((ham 0).measurable.const_mul θ))).stronglyMeasurable).mono (S.𝓕.mono (Nat.zero_le t))
  have hc0 : ∀ ω, 0 < c ω := fun ω => hcmin.trans_le (hc ω).1
  have hcmax : ∀ ω, 0 ≤ cmax := fun ω => (hc0 ω).le.trans (hc ω).2
  have hgK : ∀ t ω, |B t ω + θ * (c ω - 1) * a t ω| ≤ K + |θ| * (|cmax| + 1) * Ka := fun t ω => by
    refine (abs_add_le _ _).trans (add_le_add (hBK t ω) ?_)
    rw [abs_mul, abs_mul]
    have h1 : |c ω - 1| ≤ |cmax| + 1 := by
      rw [abs_le]
      have := (hc ω).2
      have := le_abs_self cmax
      have := hc0 ω
      constructor <;> linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (abs_nonneg θ)) (haK t ω) (abs_nonneg _)
      (by positivity)
  have hgi : ∀ t, Integrable (fun ω => B t ω + θ * (c ω - 1) * a t ω) S.μ := fun t =>
    Integrable.of_bound ((((hBm t).add ((stronglyMeasurable_const.mul ((hcm t).sub
      stronglyMeasurable_const)).mul (ham t))).mono (S.𝓕.le t)).aestronglyMeasurable)
      (K + |θ| * (|cmax| + 1) * Ka)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgK t ω)
  -- the scaled target `c P*`, its value `c a`, and the adjusted debt
  set P2 : ℕ → Ω → ℝ := fun t ω => c ω * Pstar t ω with hP2
  set a2 : ℕ → Ω → ℝ := fun t ω => c ω * a t ω with ha2
  set b2 : ℕ → Ω → ℝ := fun t ω => b t ω - (B t ω + θ * (c ω - 1) * a t ω) with hb2
  have hP2a : StronglyAdapted S.𝓕 P2 := fun t => (hcm t).mul (hPsa t)
  have hP2s : ∀ t ω, cmin * m ≤ P2 t ω ∧ P2 t ω ≤ cmax * Ms := fun t ω =>
    ⟨mul_le_mul (hc ω).1 (hPs t ω).1 hm.le (hc0 ω).le,
      mul_le_mul (hc ω).2 (hPs t ω).2 (hm.trans_le (hPs t ω).1).le (hcmax ω)⟩
  have ha2r : ∀ t ω, a2 t ω = P2 t ω + β * a2 (t + 1) ω := fun t ω => by
    simp only [ha2, hP2]
    rw [ha t ω]
    ring
  have ha2pre : ∀ t, StronglyMeasurable[S.𝓕 t] (a2 (t + 1)) := fun t => (hcm t).mul (hapre t)
  have ha2K : ∀ t ω, |a2 t ω| ≤ cmax * Ka := fun t ω => by
    simp only [ha2]
    rw [abs_mul, abs_of_pos (hc0 ω)]
    exact mul_le_mul (hc ω).2 (haK t ω) (abs_nonneg _) (hcmax ω)
  have hrate2 : ∀ t, S.E t (P t / P (t + 1)) =ᵐ[S.μ] S.E t (P2 t / P2 (t + 1)) := fun t => by
    have e : P2 t / P2 (t + 1) = Pstar t / Pstar (t + 1) := funext fun ω => by
      simp only [Pi.div_apply, hP2]
      rw [mul_div_mul_left _ _ (hc0 ω).ne']
    rw [e]
    exact hrate t
  have hflow2 : ∀ t ω, b2 t ω = (1 - β) * 0 + θ * (P t ω - P2 t ω) + β * b2 (t + 1) ω :=
    fun t ω => by
      simp only [hb2, hP2]
      rw [hflow t ω, hB t ω, ha t ω]
      ring
  have hpre2 : ∀ t, StronglyMeasurable[S.𝓕 t] (b2 (t + 1)) := fun t =>
    (hpre t).sub ((hBpre t).add ((stronglyMeasurable_const.mul ((hcm t).sub
      stronglyMeasurable_const)).mul (hapre t)))
  have hb02 : ∀ ω, b2 0 ω = 0 := fun ω => by
    simp only [hb2, hc_def]
    have := (hapos 0 ω).ne'
    field_simp
    ring
  have hbi2 : ∀ t, Integrable (b2 t) S.μ := fun t => (hbi t).sub (hgi t)
  have htvc2 : ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun T => β ^ T * S.E t (b2 (t + T)) ω) atTop (𝓝 0) :=
    tvc_sub_bdd S hβ0 hβ1 (g := fun t ω => B t ω + θ * (c ω - 1) * a t ω) hbi hgi hgK htvc
  have h := fr_unique_stochastic S hβ0 hβ1 hθ (bbar := 0) (b0 := 0) hP hPa hPM hq hP2a
    (mul_pos hcmin hm) hP2s ha2r ha2pre ha2K hrate2 hflow2 hpre2 hb02 hbi2 htvc2 t
  filter_upwards [h] with ω e
  rw [e]
  simp only [hP2, sub_self, zero_div, add_zero, one_mul, hc_def]

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d) for a general `s₀`, random date-0
data**, prices bounded away from zero): as `fr_unique_s0_random`, with prices `≥ m_P > 0` and
integrable instead of bounded above, under the bounded cumulative target real-rate hypothesis of
`fr_unique_stochastic_below` (the scaled target `c P*` has the same real-rate factors). -/
theorem fr_unique_s0_random_below {β θ K m Ms mP Ka cmin cmax L : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 0) {s0 B Pstar P b a : ℕ → Ω → ℝ}
    (hs0m : ∀ t, StronglyMeasurable[S.𝓕 t] (s0 t))
    (hB : ∀ t ω, B t ω = s0 t ω + β * B (t + 1) ω)
    (hBpre : ∀ t, StronglyMeasurable[S.𝓕 t] (B (t + 1))) (hBK : ∀ t ω, |B t ω| ≤ K)
    (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (ha : ∀ t ω, a t ω = Pstar t ω + β * a (t + 1) ω)
    (hapre : ∀ t, StronglyMeasurable[S.𝓕 t] (a (t + 1))) (haK : ∀ t ω, |a t ω| ≤ Ka)
    (hE : RuleEqmGen S β θ s0 Pstar P b) (hmP : 0 < mP) (hPmP : ∀ t ω, mP ≤ P t ω)
    (hL : ∀ t k, ∀ᵐ ω ∂S.μ, ∏ i ∈ Finset.range k,
      (Pstar (t + i) ω * S.E (t + i) (fun ω => 1 / Pstar (t + i + 1) ω) ω)⁻¹ ≤ L)
    (hcmin : 0 < cmin)
    (hc : ∀ ω, cmin ≤ 1 + (b 0 ω - B 0 ω) / (θ * a 0 ω) ∧
      1 + (b 0 ω - B 0 ω) / (θ * a 0 ω) ≤ cmax) (t : ℕ) :
    P t =ᵐ[S.μ] fun ω => (1 + (b 0 ω - B 0 ω) / (θ * a 0 ω)) * Pstar t ω := by
  obtain ⟨hP, hPa, hPi, hbi, hrate, hflow, hpre, -, htvc⟩ := hE
  have hBm : ∀ t, StronglyMeasurable[S.𝓕 t] (B t) := fun t => by
    have e : B t = fun ω => s0 t ω + β * B (t + 1) ω := funext (hB t)
    rw [e]
    exact (hs0m t).add ((hBpre t).const_mul β)
  have hBi : ∀ t, Integrable (B t) S.μ := fun t =>
    Integrable.of_bound ((hBm t).mono (S.𝓕.le t)).aestronglyMeasurable K
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hBK t ω)
  have ham : ∀ t, StronglyMeasurable[S.𝓕 t] (a t) := targetValue_adapted S hPsa ha hapre
  have hapos : ∀ t ω, 0 < a t ω := fun t ω =>
    (div_pos hm (by linarith)).trans_le (targetValue_ge hβ0 hβ1 (fun t ω => (hPs t ω).1) ha haK t ω)
  have hb0m : StronglyMeasurable[S.𝓕 0] (b 0) := by
    have e : b 0 = fun ω => s0 0 ω + θ * (P 0 ω - Pstar 0 ω) + β * b (0 + 1) ω := funext (hflow 0)
    rw [e]
    exact ((hs0m 0).add (((hPa 0).sub (hPsa 0)).const_mul θ)).add ((hpre 0).const_mul β)
  set c : Ω → ℝ := fun ω => 1 + (b 0 ω - B 0 ω) / (θ * a 0 ω) with hc_def
  have hcm : ∀ t, StronglyMeasurable[S.𝓕 t] c := fun t =>
    ((measurable_const.add ((hb0m.measurable.sub (hBm 0).measurable).div
      ((ham 0).measurable.const_mul θ))).stronglyMeasurable).mono (S.𝓕.mono (Nat.zero_le t))
  have hc0 : ∀ ω, 0 < c ω := fun ω => hcmin.trans_le (hc ω).1
  have hcmax : ∀ ω, 0 ≤ cmax := fun ω => (hc0 ω).le.trans (hc ω).2
  have hgK : ∀ t ω, |B t ω + θ * (c ω - 1) * a t ω| ≤ K + |θ| * (|cmax| + 1) * Ka := fun t ω => by
    refine (abs_add_le _ _).trans (add_le_add (hBK t ω) ?_)
    rw [abs_mul, abs_mul]
    have h1 : |c ω - 1| ≤ |cmax| + 1 := by
      rw [abs_le]
      have := (hc ω).2
      have := le_abs_self cmax
      have := hc0 ω
      constructor <;> linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (abs_nonneg θ)) (haK t ω) (abs_nonneg _)
      (by positivity)
  have hgi : ∀ t, Integrable (fun ω => B t ω + θ * (c ω - 1) * a t ω) S.μ := fun t =>
    Integrable.of_bound ((((hBm t).add ((stronglyMeasurable_const.mul ((hcm t).sub
      stronglyMeasurable_const)).mul (ham t))).mono (S.𝓕.le t)).aestronglyMeasurable)
      (K + |θ| * (|cmax| + 1) * Ka)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgK t ω)
  -- the scaled target `c P*`, its value `c a`, and the adjusted debt
  set P2 : ℕ → Ω → ℝ := fun t ω => c ω * Pstar t ω with hP2
  set a2 : ℕ → Ω → ℝ := fun t ω => c ω * a t ω with ha2
  set b2 : ℕ → Ω → ℝ := fun t ω => b t ω - (B t ω + θ * (c ω - 1) * a t ω) with hb2
  have hP2a : StronglyAdapted S.𝓕 P2 := fun t => (hcm t).mul (hPsa t)
  have hP2s : ∀ t ω, cmin * m ≤ P2 t ω ∧ P2 t ω ≤ cmax * Ms := fun t ω =>
    ⟨mul_le_mul (hc ω).1 (hPs t ω).1 hm.le (hc0 ω).le,
      mul_le_mul (hc ω).2 (hPs t ω).2 (hm.trans_le (hPs t ω).1).le (hcmax ω)⟩
  have ha2r : ∀ t ω, a2 t ω = P2 t ω + β * a2 (t + 1) ω := fun t ω => by
    simp only [ha2, hP2]
    rw [ha t ω]
    ring
  have ha2pre : ∀ t, StronglyMeasurable[S.𝓕 t] (a2 (t + 1)) := fun t => (hcm t).mul (hapre t)
  have ha2K : ∀ t ω, |a2 t ω| ≤ cmax * Ka := fun t ω => by
    simp only [ha2]
    rw [abs_mul, abs_of_pos (hc0 ω)]
    exact mul_le_mul (hc ω).2 (haK t ω) (abs_nonneg _) (hcmax ω)
  have hrate2 : ∀ t, S.E t (P t / P (t + 1)) =ᵐ[S.μ] S.E t (P2 t / P2 (t + 1)) := fun t => by
    have e : P2 t / P2 (t + 1) = Pstar t / Pstar (t + 1) := funext fun ω => by
      simp only [Pi.div_apply, hP2]
      rw [mul_div_mul_left _ _ (hc0 ω).ne']
    rw [e]
    exact hrate t
  have hflow2 : ∀ t ω, b2 t ω = (1 - β) * 0 + θ * (P t ω - P2 t ω) + β * b2 (t + 1) ω :=
    fun t ω => by
      simp only [hb2, hP2]
      rw [hflow t ω, hB t ω, ha t ω]
      ring
  have hpre2 : ∀ t, StronglyMeasurable[S.𝓕 t] (b2 (t + 1)) := fun t =>
    (hpre t).sub ((hBpre t).add ((stronglyMeasurable_const.mul ((hcm t).sub
      stronglyMeasurable_const)).mul (hapre t)))
  have hb02 : ∀ ω, b2 0 ω = 0 := fun ω => by
    simp only [hb2, hc_def]
    have := (hapos 0 ω).ne'
    field_simp
    ring
  have hbi2 : ∀ t, Integrable (b2 t) S.μ := fun t => (hbi t).sub (hgi t)
  have htvc2 : ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun T => β ^ T * S.E t (b2 (t + T)) ω) atTop (𝓝 0) :=
    tvc_sub_bdd S hβ0 hβ1 (g := fun t ω => B t ω + θ * (c ω - 1) * a t ω) hbi hgi hgK htvc
  have hqs : ∀ t, Integrable (fun ω => 1 / Pstar t ω) S.μ := fun t =>
    Integrable.of_bound (((hPsa t).measurable.const_div 1).stronglyMeasurable.mono
      (S.𝓕.le t)).aestronglyMeasurable (1 / m)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (hm.trans_le (hPs t ω).1))]
        exact one_div_le_one_div_of_le hm (hPs t ω).1)
  have hL2 : ∀ t k, ∀ᵐ ω ∂S.μ, ∏ i ∈ Finset.range k,
      (P2 (t + i) ω * S.E (t + i) (fun ω => 1 / P2 (t + i + 1) ω) ω)⁻¹ ≤ L := by
    intro t k
    have hpo : ∀ i, S.E (t + i) (fun ω => 1 / P2 (t + i + 1) ω) =ᵐ[S.μ]
        (fun ω => 1 / c ω) * S.E (t + i) (fun ω => 1 / Pstar (t + i + 1) ω) := fun i => by
      have e : (fun ω => 1 / P2 (t + i + 1) ω) =
          (fun ω => 1 / c ω) * fun ω => 1 / Pstar (t + i + 1) ω := funext fun ω => by
        simp only [hP2, Pi.mul_apply]
        rw [one_div_mul_one_div]
      rw [e]
      exact S.E_pullOut (((hcm (t + i)).measurable.const_div 1).stronglyMeasurable)
        (C := 1 / cmin) (Eventually.of_forall fun ω => by
          rw [abs_of_pos (one_div_pos.2 (hc0 ω))]
          exact one_div_le_one_div_of_le hcmin (hc ω).1) (hqs (t + i + 1))
    filter_upwards [hL t k, ae_all_iff.2 hpo] with ω h1 h2
    refine (Finset.prod_congr rfl fun i _ => ?_).trans_le h1
    rw [h2 i, Pi.mul_apply]
    have := (hc0 ω).ne'
    simp only [hP2]
    field_simp
  have h := fr_unique_stochastic_below S hβ0 hβ1 hθ (bbar := 0) (b0 := 0) hPa hmP hPmP hPi hP2a
    (mul_pos hcmin hm) hP2s ha2r ha2pre ha2K hrate2 hflow2 hpre2 hb02 hbi2 htvc2 hL2 t
  filter_upwards [h] with ω e
  rw [e]
  simp only [hP2, sub_self, zero_div, add_zero, one_mul, hc_def]

namespace MA

/-- Cochrane (2023), §9.3.2, p. 266: the lagged shock `ε_{t−k}` (pre-sample shocks are zero). -/
noncomputable def lagε (ε : ℕ → Ω → ℝ) (k t : ℕ) (ω : Ω) : ℝ := if k ≤ t then ε (t - k) ω else 0

/-- Cochrane (2023), §9.3.2, p. 266: the moving-average surplus `s_{0,t} = a(L) ε_t =
∑_{k ≤ n} α_k ε_{t−k}`. -/
noncomputable def surplus (α : ℕ → ℝ) (n : ℕ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), α k * lagε ε k t ω

/-- Cochrane (2023), §9.3.2, p. 266: the coefficients `c_m = ∑_{k ≥ m} α_k β^{k−m}` of the
present value of `a(L) ε_t` on past shocks. -/
noncomputable def coef (β : ℝ) (α : ℕ → ℝ) (n m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1 - m), α (m + i) * β ^ i

/-- Cochrane (2023), §9.3.2, p. 266: the present value of the moving-average surplus, `B_t =
∑_{m=1}^{n} c_m ε_{t−m}` — a function of past shocks only. -/
noncomputable def value (β : ℝ) (α : ℕ → ℝ) (n : ℕ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ m ∈ Finset.range n, coef β α n (m + 1) * lagε ε (m + 1) t ω

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), §9.3.2, p. 266: `ε_{(t+1)−(m+1)} = ε_{t−m}`. -/
theorem lagε_succ (ε : ℕ → Ω → ℝ) (m t : ℕ) (ω : Ω) :
    lagε ε (m + 1) (t + 1) ω = lagε ε m t ω := by
  simp only [lagε, Nat.add_le_add_iff_right, Nat.add_sub_add_right]

/-- Cochrane (2023), §9.3.2, p. 266: `c_m = α_m + β c_{m+1}` for `m ≤ n`. -/
theorem coef_succ (β : ℝ) (α : ℕ → ℝ) {n m : ℕ} (hm : m ≤ n) :
    coef β α n m = α m + β * coef β α n (m + 1) := by
  unfold coef
  rw [show n + 1 - m = (n - m) + 1 by omega, Finset.sum_range_succ',
    show n + 1 - (m + 1) = n - m by omega, Finset.mul_sum]
  simp only [add_zero, pow_zero, mul_one]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show m + (i + 1) = m + 1 + i by ring, pow_succ]
  ring

/-- Cochrane (2023), §9.3.2, p. 266: `c_0 = a(β)`. -/
theorem coef_zero (β : ℝ) (α : ℕ → ℝ) (n : ℕ) :
    coef β α n 0 = ∑ k ∈ Finset.range (n + 1), α k * β ^ k := by
  simp [coef]

/-- Cochrane (2023), §9.3.2, p. 266: `c_{n+1} = 0`. -/
theorem coef_top (β : ℝ) (α : ℕ → ℝ) (n : ℕ) : coef β α n (n + 1) = 0 := by
  simp [coef]

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), §9.3.2, p. 266 (**`a(β) = 0` gives a predetermined present value**): if
`a(β) = ∑_k α_k βᵏ = 0`, the present value `B_t` of the moving-average surplus obeys `B_t = s_{0,t}
+ β B_{t+1}` on every path, and `B_{t+1}` depends only on shocks dated `t` and earlier. -/
theorem value_rec {β : ℝ} {α : ℕ → ℝ} {n : ℕ} (hα : ∑ k ∈ Finset.range (n + 1), α k * β ^ k = 0)
    (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    value β α n ε t ω = surplus α n ε t ω + β * value β α n ε (t + 1) ω := by
  have h1 : ∑ k ∈ Finset.range (n + 1), coef β α n k * lagε ε k t ω = value β α n ε t ω := by
    rw [Finset.sum_range_succ', coef_zero, hα, zero_mul, add_zero]
    rfl
  have h2 : ∑ k ∈ Finset.range (n + 1), coef β α n k * lagε ε k t ω =
      surplus α n ε t ω + β * value β α n ε (t + 1) ω := by
    rw [Finset.sum_congr rfl fun k hk => by
      rw [coef_succ β α (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]]
    simp only [add_mul, Finset.sum_add_distrib]
    unfold surplus value
    simp only [lagε_succ]
    rw [Finset.sum_range_succ (fun k => β * coef β α n (k + 1) * lagε ε k t ω), coef_top,
      Finset.mul_sum]
    simp only [mul_zero, zero_mul, add_zero]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [← h1, h2]

/-- Cochrane (2023), §9.3.2, p. 266: lagged shocks are known when they occur. -/
theorem lagε_measurable {ε : ℕ → Ω → ℝ} (hε : StronglyAdapted S.𝓕 ε) (k t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (lagε ε k t) := by
  by_cases h : k ≤ t
  · have e : lagε ε k t = ε (t - k) := funext fun ω => by simp [lagε, h]
    rw [e]
    exact (hε (t - k)).mono (S.𝓕.mono (Nat.sub_le t k))
  · have e : lagε ε k t = fun _ => 0 := funext fun ω => by simp [lagε, h]
    rw [e]
    exact stronglyMeasurable_const

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), §9.3.2, p. 266: lagged shocks inherit the bound `|ε| ≤ E`. -/
theorem abs_lagε_le {ε : ℕ → Ω → ℝ} {E : ℝ} (hE : 0 ≤ E) (hεE : ∀ t ω, |ε t ω| ≤ E)
    (k t : ℕ) (ω : Ω) : |lagε ε k t ω| ≤ E := by
  unfold lagε
  split_ifs
  · exact hεE _ ω
  · simpa using hE

/-- Cochrane (2023), §9.3.2, p. 266: the moving-average surplus and its present value are adapted
and bounded, and the present value is predetermined. -/
theorem ma_props {β : ℝ} {α : ℕ → ℝ} {n : ℕ} {ε : ℕ → Ω → ℝ} {E : ℝ}
    (hε : StronglyAdapted S.𝓕 ε) (hE : 0 ≤ E) (hεE : ∀ t ω, |ε t ω| ≤ E) :
    (∀ t, StronglyMeasurable[S.𝓕 t] (surplus α n ε t)) ∧
      (∀ t ω, |surplus α n ε t ω| ≤ (∑ k ∈ Finset.range (n + 1), |α k|) * E) ∧
      (∀ t, StronglyMeasurable[S.𝓕 t] (value β α n ε (t + 1))) ∧
      ∀ t ω, |value β α n ε t ω| ≤ (∑ m ∈ Finset.range n, |coef β α n (m + 1)|) * E := by
  refine ⟨fun t => ?_, fun t ω => ?_, fun t => ?_, fun t ω => ?_⟩
  · have e : surplus α n ε t = ∑ k ∈ Finset.range (n + 1), fun ω => α k * lagε ε k t ω := by
      funext ω
      simp [surplus]
    rw [e]
    exact Finset.stronglyMeasurable_sum _ fun k _ =>
      (lagε_measurable S hε k t).const_mul (α k)
  · unfold surplus
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_lagε_le hE hεE k t ω) (abs_nonneg _)
  · have e : value β α n ε (t + 1) =
        ∑ m ∈ Finset.range n, fun ω => coef β α n (m + 1) * lagε ε m t ω := by
      funext ω
      simp [value, lagε_succ]
    rw [e]
    exact Finset.stronglyMeasurable_sum _ fun m _ =>
      (lagε_measurable S hε m t).const_mul _
  · unfold value
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_lagε_le hE hεE _ t ω) (abs_nonneg _)

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), §9.3.2, p. 266: with zero pre-sample shocks, the date-0 present value of the
moving-average surplus is `0`. -/
theorem value_zero (β : ℝ) (α : ℕ → ℝ) (n : ℕ) (ε : ℕ → Ω → ℝ) (ω : Ω) :
    value β α n ε 0 ω = 0 := by
  unfold value
  exact Finset.sum_eq_zero fun m _ => by simp [lagε]

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d) with `s_{0,t} = a(L) ε_{s,t}`, `a(β) =
0`**): for a bounded adapted shock `ε` and a moving-average surplus with `a(β) = 0`, and any adapted
target `0 < m ≤ P* ≤ M*` (its present value may carry news), the only equilibrium with zero initial
debt (the present value of `s₀`) and prices bounded above is `P = P*`. -/
theorem fr_unique_ma {β θ E m Ms M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {α : ℕ → ℝ} {n : ℕ} (hα : ∑ k ∈ Finset.range (n + 1), α k * β ^ k = 0)
    {ε Pstar P b : ℕ → Ω → ℝ} (hε : StronglyAdapted S.𝓕 ε) (hE : 0 ≤ E)
    (hεE : ∀ t ω, |ε t ω| ≤ E) (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hEq : RuleEqmGen S β θ (surplus α n ε) Pstar P b) (hPM : ∀ t ω, P t ω ≤ M)
    (hq : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ) (hb0 : ∀ ω, b 0 ω = 0) (t : ℕ) :
    P t =ᵐ[S.μ] Pstar t := by
  obtain ⟨h1, h2, h3, h4⟩ := ma_props S (β := β) (α := α) (n := n) hε hE hεE
  exact (fr_unique_news S hβ0 hβ1 hθ h1 h2 (value_rec hα ε) h3 h4 hPsa hm hPs hEq hPM hq
    (Eventually.of_forall fun ω => by rw [hb0 ω, value_zero]) t).1

end MA

namespace MAinf

/-- Cochrane (2023), §9.3.2, p. 266: an infinite-order moving-average surplus `s_{0,t} = a(L) ε_t =
∑_{k ≤ t} α_k ε_{t−k}` (absolutely summable `α`, pre-sample shocks zero). -/
noncomputable def surplus (α : ℕ → ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (t + 1), α k * ε (t - k) ω

/-- Cochrane (2023), §9.3.2, p. 266: `c_m = ∑_{i ≥ 0} α_{m+i} βⁱ`; `c_0 = a(β)`. -/
noncomputable def coef (β : ℝ) (α : ℕ → ℝ) (m : ℕ) : ℝ := ∑' i, α (m + i) * β ^ i

/-- Cochrane (2023), §9.3.2, p. 266: the present value `B_t = ∑_{m ≥ 1} c_m ε_{t−m}` of the
moving-average surplus — a function of past shocks only. -/
noncomputable def value (β : ℝ) (α : ℕ → ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ m ∈ Finset.range t, coef β α (m + 1) * ε (t - 1 - m) ω

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), §9.3.2, p. 266: the series defining `c_m` converge (absolutely). -/
theorem summable_abs_shift {α : ℕ → ℝ} (hα : Summable fun k => |α k|) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (m : ℕ) : Summable fun i => |α (m + i)| * β ^ i := by
  have h : Summable fun i => |α (i + m)| := (summable_nat_add_iff m).2 hα
  refine Summable.of_nonneg_of_le (fun i => mul_nonneg (abs_nonneg _) (pow_nonneg hβ0 i))
    (fun i => ?_) h
  rw [add_comm m i]
  exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hβ0 hβ1)

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), §9.3.2, p. 266: `c_m = α_m + β c_{m+1}`. -/
theorem coef_succ {α : ℕ → ℝ} (hα : Summable fun k => |α k|) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (m : ℕ) : coef β α m = α m + β * coef β α (m + 1) := by
  have hs : Summable fun i => α (m + i) * β ^ i :=
    Summable.of_norm_bounded (summable_abs_shift hα hβ0 hβ1 m) fun i => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 i)]
  unfold coef
  rw [hs.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [add_zero, pow_zero, mul_one]
  congr 1
  refine tsum_congr fun i => ?_
  rw [show m + (i + 1) = m + 1 + i by ring, pow_succ]
  ring

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), §9.3.2, p. 266 (**`a(β) = 0` gives a predetermined present value**, infinite
order): if `a(β) = ∑_k α_k βᵏ = 0`, then `B_t = s_{0,t} + β B_{t+1}` on every path. -/
theorem value_rec {α : ℕ → ℝ} (hα : Summable fun k => |α k|) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (h0 : ∑' k, α k * β ^ k = 0) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    value β α ε t ω = surplus α ε t ω + β * value β α ε (t + 1) ω := by
  have hc0 : coef β α 0 = 0 := by simpa [coef] using h0
  have h1 : ∑ k ∈ Finset.range (t + 1), coef β α k * ε (t - k) ω = value β α ε t ω := by
    rw [Finset.sum_range_succ', hc0, zero_mul, add_zero]
    unfold value
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show t - (m + 1) = t - 1 - m by omega]
  have h2 : ∑ k ∈ Finset.range (t + 1), coef β α k * ε (t - k) ω =
      surplus α ε t ω + β * value β α ε (t + 1) ω := by
    rw [Finset.sum_congr rfl fun k _ => by rw [coef_succ hα hβ0 hβ1 k]]
    simp only [add_mul, Finset.sum_add_distrib]
    unfold surplus value
    rw [Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show t + 1 - 1 - k = t - k by omega]
    ring
  rw [← h1, h2]

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), §9.3.2, p. 266: `∑_{m < t} |c_{m+1}| ≤ ∑_k |α_k| / (1 − β)`, uniformly in `t`.
-/
theorem sum_coef_le {α : ℕ → ℝ} (hα : Summable fun k => |α k|) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (t : ℕ) :
    ∑ m ∈ Finset.range t, |coef β α (m + 1)| ≤ (∑' k, |α k|) / (1 - β) := by
  set A := ∑' k, |α k| with hA
  have hA0 : 0 ≤ A := tsum_nonneg fun k => abs_nonneg _
  have hsh := summable_abs_shift hα hβ0 hβ1.le
  have hc : ∀ m, |coef β α m| ≤ ∑' i, |α (m + i)| * β ^ i := fun m => by
    unfold coef
    have hs : Summable fun i => ‖α (m + i) * β ^ i‖ := (hsh m).congr fun i => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 i)]
    refine (norm_tsum_le_tsum_norm hs).trans (le_of_eq (tsum_congr fun i => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 i)]
  have hinner : ∀ i, ∑ m ∈ Finset.range t, |α (m + 1 + i)| * β ^ i ≤ A * β ^ i := fun i => by
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hβ0 i)
    have h1 : Summable fun m => |α (m + (1 + i))| := (summable_nat_add_iff (1 + i)).2 hα
    have h2 := hα.sum_add_tsum_nat_add (1 + i)
    have h3 : 0 ≤ ∑ k ∈ Finset.range (1 + i), |α k| := Finset.sum_nonneg fun k _ => abs_nonneg _
    calc ∑ m ∈ Finset.range t, |α (m + 1 + i)| = ∑ m ∈ Finset.range t, |α (m + (1 + i))| :=
          Finset.sum_congr rfl fun m _ => by rw [Nat.add_assoc]
      _ ≤ ∑' m, |α (m + (1 + i))| := h1.sum_le_tsum _ fun m _ => abs_nonneg _
      _ ≤ A := by rw [hA, ← h2]; linarith
  calc ∑ m ∈ Finset.range t, |coef β α (m + 1)|
      ≤ ∑ m ∈ Finset.range t, ∑' i, |α (m + 1 + i)| * β ^ i :=
        Finset.sum_le_sum fun m _ => hc (m + 1)
    _ = ∑' i, ∑ m ∈ Finset.range t, |α (m + 1 + i)| * β ^ i :=
        (Summable.tsum_finsetSum fun m _ => hsh (m + 1)).symm
    _ ≤ ∑' i, A * β ^ i := Summable.tsum_le_tsum hinner (summable_sum fun m _ => hsh (m + 1))
        ((summable_geometric_of_lt_one hβ0 hβ1).mul_left A)
    _ = A / (1 - β) := by rw [tsum_mul_left, tsum_geometric_of_lt_one hβ0 hβ1, div_eq_mul_inv]

/-- Cochrane (2023), §9.3.2, p. 266: the infinite-order moving-average surplus and its present value
are adapted and bounded, and the present value is predetermined. -/
theorem ma_props {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {α : ℕ → ℝ} (hα : Summable fun k => |α k|)
    {ε : ℕ → Ω → ℝ} {E : ℝ} (hε : StronglyAdapted S.𝓕 ε) (hE : 0 ≤ E)
    (hεE : ∀ t ω, |ε t ω| ≤ E) :
    (∀ t, StronglyMeasurable[S.𝓕 t] (surplus α ε t)) ∧
      (∀ t ω, |surplus α ε t ω| ≤ (∑' k, |α k|) * E) ∧
      (∀ t, StronglyMeasurable[S.𝓕 t] (value β α ε (t + 1))) ∧
      ∀ t ω, |value β α ε t ω| ≤ (∑' k, |α k|) / (1 - β) * E := by
  refine ⟨fun t => ?_, fun t ω => ?_, fun t => ?_, fun t ω => ?_⟩
  · have e : surplus α ε t = ∑ k ∈ Finset.range (t + 1), fun ω => α k * ε (t - k) ω := by
      funext ω
      simp [surplus]
    rw [e]
    exact Finset.stronglyMeasurable_sum _ fun k _ =>
      ((hε (t - k)).mono (S.𝓕.mono (Nat.sub_le t k))).const_mul (α k)
  · unfold surplus
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Finset.range (t + 1), |α k * ε (t - k) ω|
        ≤ ∑ k ∈ Finset.range (t + 1), |α k| * E := Finset.sum_le_sum fun k _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hεE _ ω) (abs_nonneg _)
      _ = (∑ k ∈ Finset.range (t + 1), |α k|) * E := by rw [Finset.sum_mul]
      _ ≤ (∑' k, |α k|) * E := mul_le_mul_of_nonneg_right
          (hα.sum_le_tsum _ fun k _ => abs_nonneg _) hE
  · have e : value β α ε (t + 1) =
        ∑ m ∈ Finset.range (t + 1), fun ω => coef β α (m + 1) * ε (t - m) ω := by
      funext ω
      simp only [value, Finset.sum_apply]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [show t + 1 - 1 - m = t - m by omega]
    rw [e]
    exact Finset.stronglyMeasurable_sum _ fun m _ =>
      ((hε (t - m)).mono (S.𝓕.mono (Nat.sub_le t m))).const_mul _
  · unfold value
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ m ∈ Finset.range t, |coef β α (m + 1) * ε (t - 1 - m) ω|
        ≤ ∑ m ∈ Finset.range t, |coef β α (m + 1)| * E := Finset.sum_le_sum fun m _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hεE _ ω) (abs_nonneg _)
      _ = (∑ m ∈ Finset.range t, |coef β α (m + 1)|) * E := by rw [Finset.sum_mul]
      _ ≤ (∑' k, |α k|) / (1 - β) * E :=
          mul_le_mul_of_nonneg_right (sum_coef_le hα hβ0 hβ1 t) hE

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d) with `s_{0,t} = a(L) ε_{s,t}`,
`a(β) = 0`, infinite order**): for a bounded adapted shock and an absolutely summable lag
polynomial with `a(β) = 0`, and any adapted target `0 < m ≤ P* ≤ M*` (its present value may carry
news), the only equilibrium with zero initial debt (the present value of `s₀` with zero pre-sample
shocks) and prices bounded above is `P = P*`. -/
theorem fr_unique_ma {β θ E m Ms M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {α : ℕ → ℝ} (hα : Summable fun k => |α k|) (hα0 : ∑' k, α k * β ^ k = 0)
    {ε Pstar P b : ℕ → Ω → ℝ} (hε : StronglyAdapted S.𝓕 ε) (hE : 0 ≤ E)
    (hεE : ∀ t ω, |ε t ω| ≤ E) (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hEq : RuleEqmGen S β θ (surplus α ε) Pstar P b) (hPM : ∀ t ω, P t ω ≤ M)
    (hq : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ) (hb0 : ∀ ω, b 0 ω = 0) (t : ℕ) :
    P t =ᵐ[S.μ] Pstar t := by
  obtain ⟨h1, h2, h3, h4⟩ := ma_props S hβ0.le hβ1 hα hε hE hεE
  exact (fr_unique_news S hβ0 hβ1 hθ h1 h2 (value_rec hα hβ0.le hβ1.le hα0 ε) h3 h4 hPsa hm hPs
    hEq hPM hq (Eventually.of_forall fun ω => by rw [hb0 ω]; simp [value]) t).1

end MAinf

end Cochrane.AssetsRulesBalanceSheets.FiscalRulesTargetOpen
