/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.FiscalRules
import AssetsRulesBalanceSheets.ExpectationsMeasure

/-!
# Theorem FR (b) on a genuine probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.3.2,
eqs. (9.8)–(9.12), pp. 266–267 (Theorem FR, error E9.9).

`FiscalRules.Sunspot` refutes the uniqueness claim of p. 267 with an infinite settle-or-continue
event tree carrying explicit node-based conditional expectations (`Sunspot.condE`), because a
positive linear `E_t` on all functions of its countable state space would have to be finitely
supported. Here the same tree is realised as a genuine `MeasExpectationSystem`
(`ExpectationsMeasure`): the state space is `ℕ` (the settlement date), the probability measure
`∑_k π_k δ_k` has infinitely many atoms (`sun_not_finitely_supported`), the filtration is the
tree's information, and `E_t` is Mathlib's `condExp`.

## Main results

* `RuleEqm`: equilibrium of the fiscal rule with indexed debt in the measure setting.
* `SunspotMeasure.sun_E`, `SunspotMeasure.sun_E_node` (**link**): Mathlib's conditional
  expectation agrees at every state with the node-based `Sunspot.condE`.
* `SunspotMeasure.sunspot_ruleEqm`, `SunspotMeasure.fr_b_measure`,
  `SunspotMeasure.fr_b_not_pinned` (**Theorem FR (b)**): on the genuine probability space the
  sunspot path is an equilibrium with the same initial debt as `P = P*`, but `P_0 = c₀ < 1`.
* `SunspotMeasure.sun_price_unbounded`: its prices are neither bounded above nor bounded away
  from zero, consistent with Theorem FR (d).
-/

namespace Cochrane.AssetsRulesBalanceSheets.FiscalRulesMeasure

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure FiscalRules

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Cochrane (2023), §9.3.2, p. 267 and eqs. (9.8), (9.9), (9.12), pp. 266–267: an equilibrium of
the fiscal rule with indexed debt on a measure-theoretic expectation system — positive adapted
integrable prices, the interest-rate target `E_t(P_t/P_{t+1}) = E_t(P*_t/P*_{t+1})` (eq. (9.12) with
the target rate `1/(1 + i_t) = β E_t(P*_t/P*_{t+1})`; the common factor `β` is cancelled), the flow
(9.8) with the rule `s_t = (1 − β) b̄ + θ (P_t − P*_t)` on every path, real debt predetermined
(`b_t`, the book's `b_{t−1}` one date later, is known at `t − 1`), the valuation (9.9) as a genuine
`HasSum` of conditional expectations (a.e.) and the transversality condition (a.e.). -/
def RuleEqm (S : MeasExpectationSystem Ω) (β θ bbar : ℝ) (Pstar P b : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, 0 < P t ω) ∧ StronglyAdapted S.𝓕 P ∧ (∀ t, Integrable (P t) S.μ) ∧
    (∀ t, Integrable (b t) S.μ) ∧
    (∀ t, S.E t (P t / P (t + 1)) =ᵐ[S.μ] S.E t (Pstar t / Pstar (t + 1))) ∧
    (∀ t ω, b t ω = (1 - β) * bbar + θ * (P t ω - Pstar t ω) + β * b (t + 1) ω) ∧
    (∀ t, StronglyMeasurable[S.𝓕 t] (b (t + 1))) ∧
    (∀ t, ∀ᵐ ω ∂S.μ, HasSum (fun j => β ^ j * S.E t
      (fun ω' => (1 - β) * bbar + θ * (P (t + j) ω' - Pstar (t + j) ω')) ω) (b t ω)) ∧
    ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun T => β ^ T * S.E t (b (t + T)) ω) atTop (𝓝 0)

/-- Cochrane (2023), §9.3.2, p. 267: on every measure-theoretic expectation system the target path
`P = P* ≡ 1` with constant real debt `b ≡ b̄` is an equilibrium of the rule. -/
theorem target_ruleEqm (S : MeasExpectationSystem Ω) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (θ bbar : ℝ) :
    RuleEqm S β θ bbar (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => bbar) := by
  refine ⟨fun _ _ => one_pos, fun _ => stronglyMeasurable_const,
    fun _ => integrable_const _, fun _ => integrable_const _, fun _ => EventuallyEq.rfl,
    fun _ _ => by ring, fun _ => stronglyMeasurable_const, fun t => ?_, fun t => ?_⟩
  · refine Eventually.of_forall fun ω => ?_
    simp only [S.E_const]
    have h1 : (1 : ℝ) - β ≠ 0 := by linarith
    have := (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_left ((1 - β) * bbar)
    convert this using 1
    · funext j
      ring
    · field_simp
  · refine Eventually.of_forall fun ω => ?_
    simp only [S.E_const]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const bbar

namespace SunspotMeasure

variable {β c0 : ℝ}

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): `contProb t (j + 1) = contProb t j · (1 − p_{t+j})`. -/
theorem contProb_succ (β c0 : ℝ) (t j : ℕ) : Sunspot.contProb β c0 t (j + 1) =
    Sunspot.contProb β c0 t j * (1 - Sunspot.settleProb β c0 (t + j)) := by
  unfold Sunspot.contProb
  rw [Finset.prod_range_succ]

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the probability of being unsettled at `t + i`, seen from
date `0`, is the product `contProb 0 t · contProb t i`. -/
theorem contProb_add (β c0 : ℝ) (t i : ℕ) : Sunspot.contProb β c0 0 (t + i) =
    Sunspot.contProb β c0 0 t * Sunspot.contProb β c0 t i := by
  unfold Sunspot.contProb
  rw [Finset.prod_range_add]
  simp only [zero_add]

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): every unsettled node is reached with positive
probability. -/
theorem contProb_pos (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (t j : ℕ) :
    0 < Sunspot.contProb β c0 t j :=
  Finset.prod_pos fun i _ => by
    have := Sunspot.settleProb_bounds hβ0 hβ1 hc0 hc1 (t + i)
    linarith

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the probability that the sunspot path settles at date `k
+ 1`, `π_k = contProb 0 k · p_k`; the state `ω = k ∈ ℕ` of the probability space is "settles at date
`k + 1`". -/
noncomputable def weight (β c0 : ℝ) (k : ℕ) : ℝ :=
  Sunspot.contProb β c0 0 k * Sunspot.settleProb β c0 k

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): `π_k = contProb 0 k − contProb 0 (k + 1)`. -/
theorem weight_eq (β c0 : ℝ) (k : ℕ) :
    weight β c0 k = Sunspot.contProb β c0 0 k - Sunspot.contProb β c0 0 (k + 1) := by
  rw [contProb_succ, zero_add, weight]
  ring

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): every settlement date has positive probability. -/
theorem weight_pos (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (k : ℕ) :
    0 < weight β c0 k := by
  have := Sunspot.settleProb_bounds hβ0 hβ1 hc0 hc1 k
  exact mul_pos (contProb_pos hβ0 hβ1 hc0 hc1 0 k) (by linarith)

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): `∑_{k<n} π_k = 1 − contProb 0 n` (telescoping). -/
theorem sum_weight (β c0 : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, weight β c0 k = 1 - Sunspot.contProb β c0 0 n := by
  simp_rw [weight_eq]
  rw [Finset.sum_range_sub']
  simp [Sunspot.contProb]

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the settlement probabilities sum to one — the path
settles with probability one, `∑_k π_k = 1`. -/
theorem hasSum_weight (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) :
    HasSum (weight β c0) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => (weight_pos hβ0 hβ1 hc0 hc1 k).le)]
  simp_rw [sum_weight]
  simpa using (Sunspot.contProb_tendsto_zero hβ0 hβ1 hc0 hc1 0).const_sub (1 : ℝ)

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the law of the settlement date, `∑_k π_k δ_k` on `ℕ`. -/
noncomputable def sunMeasure (β c0 : ℝ) : Measure ℕ :=
  Measure.sum fun k => ENNReal.ofReal (weight β c0 k) • Measure.dirac k

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the measure of a set of settlement dates. -/
theorem sunMeasure_apply (β c0 : ℝ) (s : Set ℕ) :
    sunMeasure β c0 s = ∑' k, s.indicator (fun k => ENNReal.ofReal (weight β c0 k)) k := by
  rw [sunMeasure, Measure.sum_apply _ (MeasurableSet.of_discrete)]
  refine tsum_congr fun k => ?_
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  by_cases h : k ∈ s <;> simp [h]

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): `P(settle at k + 1) = π_k`. -/
theorem sunMeasure_singleton (β c0 : ℝ) (j : ℕ) :
    sunMeasure β c0 {j} = ENNReal.ofReal (weight β c0 j) := by
  rw [sunMeasure_apply, tsum_eq_single j (fun k hk => by simp [hk])]
  simp

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the settlement-date law is a probability measure. -/
theorem sunMeasure_univ (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) :
    sunMeasure β c0 Set.univ = 1 := by
  rw [sunMeasure_apply]
  simp only [Set.indicator_univ]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (weight_pos hβ0 hβ1 hc0 hc1 k).le)
    (hasSum_weight hβ0 hβ1 hc0 hc1).summable, (hasSum_weight hβ0 hβ1 hc0 hc1).tsum_eq,
    ENNReal.ofReal_one]

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the node visited at date `t` by the state `ω` (settles
at `ω + 1`): `none` (not yet settled) for `t ≤ ω`, `some (ω + 1)` afterwards (`Sunspot.pathNode`).
-/
def node (t ω : ℕ) : Option ℕ := Sunspot.pathNode (ω + 1) t

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): before settling the state is at the continue node. -/
theorem node_of_le {t ω : ℕ} (h : t ≤ ω) : node t ω = none := by
  simp only [node, Sunspot.pathNode, show t < ω + 1 by omega, ↓reduceIte]

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): after settling the state is at its settled node. -/
theorem node_of_lt {t ω : ℕ} (h : ω < t) : node t ω = some (ω + 1) := by
  simp only [node, Sunspot.pathNode, show ¬ t < ω + 1 by omega, ↓reduceIte]

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the date-`s` node as a function of a later node. -/
def nodeBack (s : ℕ) (x : Option ℕ) : Option ℕ :=
  x.elim none fun m => if s < m then none else some m

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the date-`s` node is determined by the date-`t` node, `s
≤ t` (information is never forgotten). -/
theorem nodeBack_node {s t : ℕ} (hst : s ≤ t) (ω : ℕ) : nodeBack s (node t ω) = node s ω := by
  rcases Nat.lt_or_ge ω t with h | h
  · rw [node_of_lt h]
    rcases Nat.lt_or_ge ω s with h' | h'
    · rw [node_of_lt h']
      simp only [nodeBack, Option.elim_some, show ¬ s < ω + 1 by omega, ↓reduceIte]
    · rw [node_of_le h']
      simp only [nodeBack, Option.elim_some, show s < ω + 1 by omega, ↓reduceIte]
  · rw [node_of_le h, node_of_le (hst.trans h)]
    rfl

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the information of the tree, `𝓕_t = σ(node_t)` (whether
the path has settled by `t`, and when). -/
def sunFiltration : Filtration ℕ Nat.instMeasurableSpace where
  seq t := MeasurableSpace.comap (node t) ⊤
  mono' s t hst := by
    intro A hA
    obtain ⟨B, -, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA
    refine MeasurableSpace.measurableSet_comap.2
      ⟨nodeBack s ⁻¹' B, MeasurableSpace.measurableSet_top, ?_⟩
    ext ω
    simp only [Set.mem_preimage, nodeBack_node hst]
  le' _ _ _ := MeasurableSet.of_discrete

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the settlement-date law as a probability measure. -/
noncomputable def sunProb (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) :
    ProbabilityMeasure ℕ :=
  ⟨sunMeasure β c0, ⟨sunMeasure_univ hβ0 hβ1 hc0 hc1⟩⟩

/-- Cochrane (2023), §9.3.2, p. 267 (**Theorem FR (b)**, E9.9): the settle-or-continue sunspot tree
as a genuine measure-theoretic expectation system — `Ω = ℕ` (settlement dates) with infinitely many
atoms, the natural filtration of the tree and Mathlib's conditional expectation. -/
noncomputable def sunSystem (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) :
    MeasExpectationSystem ℕ :=
  ⟨sunProb hβ0 hβ1 hc0 hc1, sunFiltration⟩

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the measure of `sunSystem`. -/
theorem sunSystem_μ (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) :
    (sunSystem hβ0 hβ1 hc0 hc1).μ = sunMeasure β c0 := rfl

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): every state has positive probability, so a.e. statements
on `sunSystem` hold at every state. -/
theorem sunSystem_fullSupport (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (ω : ℕ) : (sunSystem hβ0 hβ1 hc0 hc1).μ {ω} ≠ 0 := by
  rw [sunSystem_μ, sunMeasure_singleton, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact weight_pos hβ0 hβ1 hc0 hc1 ω

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): `P(settle at k + 1) = π_k` (real form). -/
theorem measureReal_singleton (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (k : ℕ) : (sunMeasure β c0).real {k} = weight β c0 k := by
  rw [measureReal_def, sunMeasure_singleton,
    ENNReal.toReal_ofReal (weight_pos hβ0 hβ1 hc0 hc1 k).le]

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the probability of being unsettled at date `n`, `P(ω ≥
n) = contProb 0 n`. -/
theorem measureReal_Ici (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (n : ℕ) :
    (sunMeasure β c0).real (Set.Ici n) = Sunspot.contProb β c0 0 n := by
  have : IsProbabilityMeasure (sunMeasure β c0) := ⟨sunMeasure_univ hβ0 hβ1 hc0 hc1⟩
  have h1 : Set.Ici n = (↑(Finset.range n) : Set ℕ)ᶜ := by
    ext k
    simp
  rw [h1, probReal_compl_eq_one_sub MeasurableSet.of_discrete, ← sum_measureReal_singleton]
  simp_rw [measureReal_singleton hβ0 hβ1 hc0 hc1]
  rw [sum_weight]
  ring

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): a variable that is constant on the unsettled states from
some date on is integrable (it takes finitely many values). -/
theorem integrable_of_eventually_const (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0)
    (hc1 : c0 < 1) {X : ℕ → ℝ} {N : ℕ} (hX : ∀ k, N ≤ k → X k = X N) :
    Integrable X (sunMeasure β c0) := by
  have : IsProbabilityMeasure (sunMeasure β c0) := ⟨sunMeasure_univ hβ0 hβ1 hc0 hc1⟩
  refine Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable
    (∑ i ∈ Finset.range (N + 1), |X i|) (Eventually.of_forall fun k => ?_)
  rw [Real.norm_eq_abs]
  rcases Nat.lt_or_ge k (N + 1) with h | h
  · exact Finset.single_le_sum (f := fun i => |X i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 h)
  · rw [hX k (by omega)]
    exact Finset.single_le_sum (f := fun i => |X i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega))

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the average of `X` over the unsettled cell `{ω ≥ t}`. -/
noncomputable def cellAvg (β c0 : ℝ) (t : ℕ) (X : ℕ → ℝ) : ℝ :=
  (∫ ω in Set.Ici t, X ω ∂sunMeasure β c0) / Sunspot.contProb β c0 0 t

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): Mathlib's conditional expectation on `sunSystem`, at
every state — the value itself on a settled state, the cell average on the unsettled cell. -/
theorem sun_E (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (t : ℕ)
    {X : ℕ → ℝ} (hX : Integrable X (sunMeasure β c0)) :
    (sunSystem hβ0 hβ1 hc0 hc1).E t X = fun ω => if t ≤ ω then cellAvg β c0 t X else X ω := by
  set S := sunSystem hβ0 hβ1 hc0 hc1
  have hX' : Integrable X S.μ := hX
  set a := cellAvg β c0 t X with ha
  set g : ℕ → ℝ := fun ω => if t ≤ ω then a else X ω with hg
  set G : Option ℕ → ℝ := fun x => x.elim a fun m => X (m - 1) with hG
  have hgG : g = G ∘ node t := by
    funext ω
    rcases Nat.lt_or_ge ω t with h | h
    · simp [hg, hG, node_of_lt h, Nat.not_le.mpr h]
    · simp [hg, hG, node_of_le h, h]
  have hgm : StronglyMeasurable[S.𝓕 t] g := by
    have : Measurable[S.𝓕 t] g := by
      rw [hgG]
      exact fun U _ => MeasurableSpace.measurableSet_comap.2
        ⟨G ⁻¹' U, MeasurableSpace.measurableSet_top, rfl⟩
    exact this.stronglyMeasurable
  have hgi : Integrable g S.μ := by
    refine Integrable.mono' (hX'.abs.add (integrable_const |a|))
      Measurable.of_discrete.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    simp only [hg, Pi.add_apply]
    split_ifs
    · linarith [abs_nonneg (X ω)]
    · linarith [abs_nonneg a]
  have hct := contProb_pos hβ0 hβ1 hc0 hc1 0 t
  refine (S.eq_of_ae_eq (sunSystem_fullSupport hβ0 hβ1 hc0 hc1)
    (ae_eq_condExp_of_forall_setIntegral_eq (S.𝓕.le t) hX' (fun _ _ _ => hgi.integrableOn)
      (fun A hA _ => ?_) hgm.aestronglyMeasurable)).symm
  obtain ⟨B, -, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA
  rw [← integral_inter_add_sdiff (measurableSet_Ici (a := t)) hgi.integrableOn,
    ← integral_inter_add_sdiff (measurableSet_Ici (a := t)) hX'.integrableOn]
  congr 1
  · by_cases hB : none ∈ B
    · have hset : node t ⁻¹' B ∩ Set.Ici t = Set.Ici t := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici, and_iff_right_iff_imp]
        intro h
        rw [node_of_le h]
        exact hB
      rw [hset, setIntegral_congr_fun measurableSet_Ici (g := fun _ => a)
        (fun ω hω => by simp [hg, Set.mem_Ici.1 hω]), setIntegral_const, smul_eq_mul]
      rw [sunSystem_μ, measureReal_Ici hβ0 hβ1 hc0 hc1, ha, cellAvg]
      field_simp
    · have hset : node t ⁻¹' B ∩ Set.Ici t = ∅ := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro hω h
        rw [node_of_le h] at hω
        exact hB hω
      rw [hset]
      simp
  · refine setIntegral_congr_fun (MeasurableSet.of_discrete) fun ω hω => ?_
    have : ¬ t ≤ ω := fun h => hω.2 (Set.mem_Ici.2 h)
    simp [hg, this]

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): every date-`n` node variable `Y ∘ node_n` is integrable.
-/
theorem integrable_node (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (n : ℕ)
    (Y : Option ℕ → ℝ) : Integrable (fun ω => Y (node n ω)) (sunMeasure β c0) :=
  integrable_of_eventually_const hβ0 hβ1 hc0 hc1 (N := n) fun k hk => by
    simp only [node_of_le hk, node_of_le (le_refl n)]

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the integral of a date-`(n + i)` node variable over the
unsettled cell at `n`, as a finite sum over settlement dates plus the unsettled mass. -/
theorem setIntegral_Ici_node (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (Y : Option ℕ → ℝ) (i n : ℕ) :
    ∫ ω in Set.Ici n, Y (node (n + i) ω) ∂sunMeasure β c0 =
      ∑ l ∈ Finset.range i, weight β c0 (n + l) * Y (some (n + l + 1)) +
        Sunspot.contProb β c0 0 (n + i) * Y none := by
  induction i generalizing n with
  | zero =>
    simp only [add_zero, Finset.range_zero, Finset.sum_empty, zero_add]
    rw [setIntegral_congr_fun measurableSet_Ici (g := fun _ => Y none)
      (fun ω hω => by simp [node_of_le (Set.mem_Ici.1 hω)]), setIntegral_const, smul_eq_mul,
      measureReal_Ici hβ0 hβ1 hc0 hc1]
  | succ i ih =>
    have hset : Set.Ici n = {n} ∪ Set.Ici (n + 1) := by
      ext k
      simp only [Set.mem_Ici, Set.mem_union, Set.mem_singleton_iff]
      omega
    have hdisj : Disjoint ({n} : Set ℕ) (Set.Ici (n + 1)) := by
      rw [Set.disjoint_singleton_left, Set.mem_Ici]
      omega
    have hint := integrable_node hβ0 hβ1 hc0 hc1 (n + (i + 1)) Y
    rw [hset, setIntegral_union hdisj measurableSet_Ici hint.integrableOn hint.integrableOn,
      integral_singleton,
      measureReal_singleton hβ0 hβ1 hc0 hc1, smul_eq_mul, node_of_lt (by omega),
      show n + (i + 1) = n + 1 + i by ring, ih (n + 1), Finset.sum_range_succ']
    simp only [add_zero]
    have e : ∀ l ∈ Finset.range i, weight β c0 (n + 1 + l) * Y (some (n + 1 + l + 1)) =
        weight β c0 (n + (l + 1)) * Y (some (n + (l + 1) + 1)) := fun l _ => by
      rw [show n + 1 + l = n + (l + 1) by ring]
    rw [Finset.sum_congr rfl e]
    ring

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the cell average of a date-`(t + j)` node variable is
the node-based conditional expectation `Sunspot.condE t j`. -/
theorem cellAvg_node (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (t j : ℕ) (Y : Option ℕ → ℝ) :
    cellAvg β c0 t (fun ω => Y (node (t + j) ω)) = Sunspot.condE β c0 t j Y := by
  have hct := contProb_pos hβ0 hβ1 hc0 hc1 0 t
  rw [cellAvg, setIntegral_Ici_node hβ0 hβ1 hc0 hc1, div_eq_iff hct.ne', Sunspot.condE]
  simp only [weight, contProb_add, add_mul, Finset.sum_mul]
  rw [add_comm]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun l _ => by ring

/-- Cochrane (2023), §9.3.2, p. 267 (**link**, E9.9): Mathlib's conditional expectation on the
genuine probability space agrees, at **every** state, with the node-based conditional expectations
of `FiscalRules.Sunspot`: at the continue node `E_t (Y ∘ node_{t+j}) = Sunspot.condE t j Y`, at a
settled node it is the settled value. -/
theorem sun_E_node (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (t j : ℕ) (Y : Option ℕ → ℝ) (ω : ℕ) :
    (sunSystem hβ0 hβ1 hc0 hc1).E t (fun ω => Y (node (t + j) ω)) ω =
      (node t ω).elim (Sunspot.condE β c0 t j Y) fun m => Y (some m) := by
  rw [sun_E hβ0 hβ1 hc0 hc1 t (integrable_node hβ0 hβ1 hc0 hc1 (t + j) Y)]
  rcases Nat.lt_or_ge ω t with h | h
  · simp only [Nat.not_le.mpr h, ↓reduceIte, node_of_lt h, node_of_lt (by omega : ω < t + j),
      Option.elim_some]
  · simp only [h, ↓reduceIte, node_of_le h, Option.elim_none, cellAvg_node hβ0 hβ1 hc0 hc1]

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): `Sunspot.condE t j Y` only depends on the values of `Y`
at the nodes reachable from the date-`t` continue node within `j` dates. -/
theorem condE_congr {t j : ℕ} {Y Y' : Option ℕ → ℝ} (h0 : Y none = Y' none)
    (h : ∀ i < j, Y (some (t + i + 1)) = Y' (some (t + i + 1))) :
    Sunspot.condE β c0 t j Y = Sunspot.condE β c0 t j Y' := by
  unfold Sunspot.condE
  rw [h0]
  congr 1
  exact Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): node variables `Y ∘ node_t` are known at `t`. -/
theorem stronglyMeasurable_node (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (t : ℕ) (G : Option ℕ → ℝ) :
    StronglyMeasurable[(sunSystem hβ0 hβ1 hc0 hc1).𝓕 t] (fun ω => G (node t ω)) := by
  have : Measurable[(sunSystem hβ0 hβ1 hc0 hc1).𝓕 t] (fun ω => G (node t ω)) :=
    fun U _ => MeasurableSpace.measurableSet_comap.2
      ⟨G ⁻¹' U, MeasurableSpace.measurableSet_top, rfl⟩
  exact this.stronglyMeasurable

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the sunspot price process `P_t(ω) = Sunspot.price t
(node_t ω)`. -/
noncomputable def sunPrice (β c0 : ℝ) (t ω : ℕ) : ℝ := Sunspot.price β c0 t (node t ω)

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the real debt process `b_t(ω) = Sunspot.debt t (node_t
ω)`. -/
noncomputable def sunDebt (β c0 θ bbar : ℝ) (t ω : ℕ) : ℝ :=
  Sunspot.debt β c0 θ bbar t (node t ω)

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the sunspot price levels are positive. -/
theorem price_pos (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (t : ℕ)
    (x : Option ℕ) : 0 < Sunspot.price β c0 t x := by
  cases x with
  | none => simp only [Sunspot.price, Option.elim_none, Sunspot.contPrice]; positivity
  | some k =>
    simp only [Sunspot.price, Option.elim_some, Sunspot.settlePrice]
    exact mul_pos (by linarith) (Sunspot.value_pos hβ0 hβ1 hc0 hc1 k)

/-- Cochrane (2023), §9.3.2, p. 267, eq. (9.8) (E9.9): real debt is predetermined — `b_{t+1}` is a
function of the date-`t` node. -/
theorem sunDebt_succ (hβ0 : 0 < β) (hβ1 : β < 1) (θ bbar : ℝ) (t : ℕ) :
    sunDebt β c0 θ bbar (t + 1) = fun ω => Sunspot.debt β c0 θ bbar (t + 1) (node t ω) := by
  funext ω
  simp only [sunDebt]
  rcases Nat.lt_or_ge ω t with h | h
  · rw [node_of_lt h, node_of_lt (by omega)]
  · rcases Nat.eq_or_lt_of_le h with h' | h'
    · rw [← h', node_of_lt (by omega : t < t + 1), node_of_le le_rfl]
      exact ((Sunspot.flow_cont hβ0 hβ1 θ bbar t).1).symm
    · rw [node_of_le h, node_of_le (by omega)]

/-- Cochrane (2023), eq. (9.8), p. 266 (E9.9): the flow condition holds on every path of the genuine
probability space. -/
theorem sun_flow (hβ0 : 0 < β) (hβ1 : β < 1) (θ bbar : ℝ) (t ω : ℕ) :
    sunDebt β c0 θ bbar t ω = (1 - β) * bbar + θ * (sunPrice β c0 t ω - 1) +
      β * sunDebt β c0 θ bbar (t + 1) ω := by
  have e := congrFun (sunDebt_succ (c0 := c0) hβ0 hβ1 θ bbar t) ω
  rw [e]
  simp only [sunDebt, sunPrice]
  have h := Sunspot.flow_cont (c0 := c0) hβ0 hβ1 θ bbar t
  generalize node t ω = x
  cases x with
  | none => exact h.2
  | some k => exact Sunspot.flow_settled hβ1 θ bbar t k

/-- Cochrane (2023), eq. (9.12), p. 267 (E9.9): on the genuine probability space, `E_t(P_t/P_{t+1})
= 1 = P*_t/P*_{t+1}` at every state (Mathlib's conditional expectation). -/
theorem sun_rate (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (t : ℕ) :
    (sunSystem hβ0 hβ1 hc0 hc1).E t (sunPrice β c0 t / sunPrice β c0 (t + 1)) = fun _ => 1 := by
  set Y : Option ℕ → ℝ := fun x => Sunspot.price β c0 t (nodeBack t x) /
    Sunspot.price β c0 (t + 1) x with hY
  have hfun : sunPrice β c0 t / sunPrice β c0 (t + 1) = fun ω => Y (node (t + 1) ω) := by
    funext ω
    simp only [Pi.div_apply, sunPrice, hY, nodeBack_node (Nat.le_succ t)]
  rw [hfun]
  funext ω
  rw [sun_E_node hβ0 hβ1 hc0 hc1 t 1 Y ω]
  rcases Nat.lt_or_ge ω t with h | h
  · rw [node_of_lt h]
    simp only [Option.elim_some, hY, nodeBack, show ¬ t < ω + 1 by omega, ↓reduceIte]
    exact Sunspot.rate_target_settled hβ0 hβ1 hc0 hc1 t (ω + 1)
  · rw [node_of_le h, Option.elim_none, ← Sunspot.rate_target_cont hβ0 hβ1 hc0 hc1 t]
    refine condE_congr (by simp [hY, nodeBack]) fun i hi => ?_
    have hi0 : i = 0 := by omega
    subst hi0
    simp [hY, nodeBack]

/-- Cochrane (2023), eq. (9.9), p. 266 (E9.9): on the genuine probability space, at every state,
real debt equals the expected present value of surpluses, `b_{t−1} = ∑_j β^j E_t s_{t+j}` (a genuine
`HasSum`). -/
theorem sun_valuation (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (θ bbar : ℝ) (t ω : ℕ) :
    HasSum (fun j => β ^ j * (sunSystem hβ0 hβ1 hc0 hc1).E t
      (fun ω' => Sunspot.surplus β c0 θ bbar (t + j) (node (t + j) ω')) ω)
      (sunDebt β c0 θ bbar t ω) := by
  simp only [sun_E_node hβ0 hβ1 hc0 hc1, sunDebt]
  generalize node t ω = x
  cases x with
  | none => exact Sunspot.valuation_cont hβ0 hβ1 hc0 hc1 θ bbar t
  | some k => exact Sunspot.valuation_settled hβ0 hβ1 θ bbar t k

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the transversality condition `β^T E_t b_{t+T} → 0` on
the genuine probability space, at every state. -/
theorem sun_tvc (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (θ bbar : ℝ) (t ω : ℕ) :
    Tendsto (fun T => β ^ T * (sunSystem hβ0 hβ1 hc0 hc1).E t
      (sunDebt β c0 θ bbar (t + T)) ω) atTop (𝓝 0) := by
  have e : ∀ T, sunDebt β c0 θ bbar (t + T) =
      fun ω' => Sunspot.debt β c0 θ bbar (t + T) (node (t + T) ω') := fun T => rfl
  simp only [e, sun_E_node hβ0 hβ1 hc0 hc1]
  generalize node t ω = x
  cases x with
  | none => exact Sunspot.tvc_cont hβ0 hβ1 hc0 hc1 θ bbar t
  | some k => exact Sunspot.tvc_settled hβ0 hβ1 θ bbar t k

/-- Cochrane (2023), §9.3.2, p. 267 (**Theorem FR (b)**, E9.9): the sunspot path is an equilibrium
of the fiscal rule (`RuleEqm`, all conditions with Mathlib's conditional expectation) with target
`P* ≡ 1`. -/
theorem sunspot_ruleEqm (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (θ bbar : ℝ) : RuleEqm (sunSystem hβ0 hβ1 hc0 hc1) β θ bbar (fun _ _ => 1) (sunPrice β c0)
      (sunDebt β c0 θ bbar) := by
  set S := sunSystem hβ0 hβ1 hc0 hc1
  refine ⟨fun t ω => price_pos hβ0 hβ1 hc0 hc1 t _,
    fun t => stronglyMeasurable_node hβ0 hβ1 hc0 hc1 t (Sunspot.price β c0 t),
    fun t => integrable_node hβ0 hβ1 hc0 hc1 t (Sunspot.price β c0 t),
    fun t => integrable_node hβ0 hβ1 hc0 hc1 t (Sunspot.debt β c0 θ bbar t),
    fun t => ?_, fun t ω => sun_flow hβ0 hβ1 θ bbar t ω, fun t => ?_,
    fun t => Eventually.of_forall fun ω => sun_valuation hβ0 hβ1 hc0 hc1 θ bbar t ω,
    fun t => Eventually.of_forall fun ω => sun_tvc hβ0 hβ1 hc0 hc1 θ bbar t ω⟩
  · have h1 : ((fun _ => (1 : ℝ)) / fun _ => 1 : ℕ → ℝ) = fun _ => 1 := by
      funext ω
      simp
    change S.E t (sunPrice β c0 t / sunPrice β c0 (t + 1)) =ᵐ[S.μ]
      S.E t ((fun _ => (1 : ℝ)) / fun _ => 1)
    rw [sun_rate hβ0 hβ1 hc0 hc1, h1, S.E_const]
  · rw [sunDebt_succ hβ0 hβ1]
    exact stronglyMeasurable_node hβ0 hβ1 hc0 hc1 t _

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the sunspot path starts at `P_0 = c₀`. -/
theorem sunPrice_zero (ω : ℕ) : sunPrice β c0 0 ω = c0 := by
  simp [sunPrice, node_of_le (Nat.zero_le ω), Sunspot.price, Sunspot.contPrice]

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): initial real debt is `b̄`, the present value of `s₀ = (1
− β) b̄`. -/
theorem sunDebt_zero (hβ1 : β < 1) (θ bbar : ℝ) (ω : ℕ) :
    sunDebt β c0 θ bbar 0 ω = bbar := by
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith
  simp [sunDebt, node_of_le (Nat.zero_le ω), Sunspot.debt, Sunspot.nodeValue,
    Sunspot.value_zero]

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the probability space is not finitely supported — no
finite set of states has probability one (so no positive core `ExpectationSystem` on all functions
can represent it). -/
theorem sun_not_finitely_supported (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (s : Finset ℕ) : (sunSystem hβ0 hβ1 hc0 hc1).μ (↑s)ᶜ ≠ 0 := by
  obtain ⟨k, hk⟩ := Infinite.exists_notMem_finset s
  exact fun h => sunSystem_fullSupport hβ0 hβ1 hc0 hc1 k
    (measure_mono_null (Set.singleton_subset_iff.2 (by simpa using hk)) h)

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9, consistent with Theorem FR (d)): the sunspot prices are
neither (essentially) bounded above nor bounded away from zero. -/
theorem sun_price_unbounded (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) :
    (¬ ∃ M, ∀ t, ∀ᵐ ω ∂(sunSystem hβ0 hβ1 hc0 hc1).μ, sunPrice β c0 t ω ≤ M) ∧
      ¬ ∃ m, 0 < m ∧ ∀ t, ∀ᵐ ω ∂(sunSystem hβ0 hβ1 hc0 hc1).μ, m ≤ sunPrice β c0 t ω := by
  set S := sunSystem hβ0 hβ1 hc0 hc1
  have hfull := sunSystem_fullSupport hβ0 hβ1 hc0 hc1
  constructor
  · rintro ⟨M, hM⟩
    refine Sunspot.settlePrice_unbounded hβ0 hβ1 hc0 hc1
      ⟨max M (Sunspot.settlePrice β c0 0), fun k => ?_⟩
    cases k with
    | zero => exact le_max_right _ _
    | succ k =>
      have h := S.le_of_ae_le hfull (g := fun _ => M) (hM (k + 1)) k
      simp only [sunPrice, node_of_lt (Nat.lt_succ_self k), Sunspot.price,
        Option.elim_some] at h
      exact h.trans (le_max_left _ _)
  · rintro ⟨m, hm, h⟩
    obtain ⟨t, ht⟩ := ((Sunspot.contPrice_tendsto_zero (c0 := c0) hβ0 hβ1).eventually
      (gt_mem_nhds hm)).exists
    have h' := S.le_of_ae_le hfull (f := fun _ => m) (h t) t
    simp only [sunPrice, node_of_le (le_refl t), Sunspot.price, Option.elim_none] at h'
    linarith

/-- Cochrane (2023), §9.3.2, p. 267 (**Theorem FR (b)** in the measure setting, error E9.9): on the
genuine infinite-horizon probability space `sunSystem`, for every `0 < β < 1`, `0 < c₀ < 1`, `θ`,
`b̄`, both the sunspot path and the target path `P = P* ≡ 1` are equilibria of the rule with the
same initial debt `b̄`, and the sunspot path starts at `P_0 = c₀ < 1 = P*_0` at every state. -/
theorem fr_b_measure (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (θ bbar : ℝ) :
    RuleEqm (sunSystem hβ0 hβ1 hc0 hc1) β θ bbar (fun _ _ => 1) (sunPrice β c0)
        (sunDebt β c0 θ bbar) ∧
      RuleEqm (sunSystem hβ0 hβ1 hc0 hc1) β θ bbar (fun _ _ => 1) (fun _ _ => 1)
        (fun _ _ => bbar) ∧
      (∀ ω, sunDebt β c0 θ bbar 0 ω = bbar) ∧ (∀ ω, sunPrice β c0 0 ω = c0) ∧
      ∀ ω, sunPrice β c0 0 ω < 1 := by
  refine ⟨sunspot_ruleEqm hβ0 hβ1 hc0 hc1 θ bbar, target_ruleEqm _ hβ0 hβ1 θ bbar,
    sunDebt_zero hβ1 θ bbar, sunPrice_zero, fun ω => ?_⟩
  rw [sunPrice_zero]
  exact hc1

/-- Cochrane (2023), §9.3.2, p. 267 (**Theorem FR (b)**, the book's claim refuted in the measure
setting): the rule and the interest-rate target do not pin `P = P*` under uncertainty — there is an
equilibrium with initial debt `b̄` whose date-0 price differs from `P*_0 = 1` with probability one
(indeed at every state). -/
theorem fr_b_not_pinned (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (θ bbar : ℝ) :
    ∃ P b : ℕ → ℕ → ℝ, RuleEqm (sunSystem hβ0 hβ1 hc0 hc1) β θ bbar (fun _ _ => 1) P b ∧
      (∀ ω, b 0 ω = bbar) ∧ ¬ (P 0 =ᵐ[(sunSystem hβ0 hβ1 hc0 hc1).μ] fun _ => 1) := by
  refine ⟨_, _, sunspot_ruleEqm hβ0 hβ1 hc0 hc1 θ bbar, sunDebt_zero hβ1 θ bbar, fun h => ?_⟩
  have := congrFun ((sunSystem hβ0 hβ1 hc0 hc1).eq_of_ae_eq
    (sunSystem_fullSupport hβ0 hβ1 hc0 hc1) h) 0
  rw [sunPrice_zero] at this
  linarith

end SunspotMeasure

end Cochrane.AssetsRulesBalanceSheets.FiscalRulesMeasure
