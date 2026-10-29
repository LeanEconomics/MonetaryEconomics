/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.TidyR6ManagedSurplusMeasure

/-!
# The unmodified linear surplus rule for every response, and the managed plan below

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.1, p. 197.

Surpluses `s_t = s̄ + u_t + φ (x_t − b̄)` with `u` an AR(1) (`|ρ| < 1`, i.i.d. integrable
innovations `ν` with deficits of every size; Gaussian included) and `0 < γ < 1`. Without the
boundary-avoiding modification debt follows `x_{t+1} = (γ − φ) x_t − (s̄ − φ b̄ + u_t)`
(`TidyR6ManagedSurplusMeasure.rulePath_linRule`).

## Main results

* `linear_rule_ae_unbounded_above`, `linear_rule_zero_prob`: for every response `φ > γ − 1`
  (root `γ − φ < 1`; in particular every `φ ≥ 0`, including `φ > γ`, where the root is negative
  and debt oscillates), debt is almost surely unbounded above, so it stays below any limit with
  probability zero. For `γ − φ ≤ 0` the argument is pathwise (`unbounded_above_of_nonpos`): if
  debt stayed below `M`, then `(γ − φ) x_t ≥ (γ − φ) M`, and a large deficit shock lifts debt
  above `M`.
* `linear_rule_half_prob` (the other side): for `φ < γ − 1` (root `γ − φ > 1`, surpluses CUT
  sharply as debt rises) debt from a low enough initial value stays at or below zero forever
  with probability at least `1/2` (Markov's inequality on the discounted shock sum).
* `linear_rule_not_ae_sustainable`: for every `φ` and every initial debt, debt exceeds any limit
  at date 1 with positive probability, so no unmodified linear rule is sustainable almost surely.
* `plan_unbounded_below_of_frequently`, `plan_ae_unbounded_below`, `plan_debt_ae_unbounded_below`:
  the one-sided boundary-avoiding plan (any `φ`, any `γ`), and actual debt under it, are almost
  surely unbounded below when the innovations have surpluses of every size: the government
  accumulates assets without bound.
-/

namespace Cochrane.FiscalConstraints.TidyR6LinearRuleBounds

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure ExpectationsMeasureIID DebtLimitStochastic DebtLimitStochasticMeasure
  TidyR5GaussianAR1 TidyR6ManagedSurplus TidyR6ManagedSurplusMeasure

variable {ν : ProbabilityMeasure ℝ}

/-! ### Unmodified rule, root `γ − φ < 1`: unbounded above -/

/-- Cochrane (2023), p. 197: with root `a ≤ 0` (a response `φ ≥ γ`), on any path on which the
AR(1) falls below every level infinitely often, debt `x_{t+1} = a x_t − (c + u_t)` exceeds every
level at some date. -/
theorem unbounded_above_of_nonpos {a c ρ x₀ : ℝ} (ha : a ≤ 0) {ω : ℕ → ℝ}
    (hfreq : ∀ K : ℝ, ∃ᶠ t in atTop, ar1 ρ t ω ≤ K) (M : ℝ) :
    ∃ t, M < debtPath a x₀ (arSurplus ρ c) t ω := by
  by_contra hcon
  have hall : ∀ t, debtPath a x₀ (arSurplus ρ c) t ω ≤ M := fun t =>
    not_lt.1 fun h => hcon ⟨t, h⟩
  obtain ⟨t, ht⟩ := (hfreq ((a - 1) * M - c - 1)).exists
  have h1 := hall (t + 1)
  rw [debtPath_succ, arSurplus] at h1
  have h2 := mul_le_mul_of_nonpos_left (hall t) ha
  linarith

/-- Cochrane (2023), p. 197 (**unmodified linear rule, every response `φ > γ − 1`**): with
i.i.d. integrable innovations with deficits of every size and `|ρ| < 1`, debt under the
unmodified rule is almost surely unbounded above, from every initial debt. -/
theorem linear_rule_ae_unbounded_above (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) {ρ γ φ : ℝ} (hρ : |ρ| < 1)
    (hφ : γ - 1 < φ) (sbar bbar x₀ : ℝ) :
    ∀ᵐ ω ∂(iidSystem ν).μ, ∀ M : ℝ, ∃ t,
      M < rulePath γ (linRule sbar φ bbar (ar1 ρ)) x₀ t ω := by
  rcases le_or_gt 0 (γ - φ) with ha | ha
  · filter_upwards [ar1_unbounded_of_integrable hint hdef (γ := γ - φ) ha (by linarith) hρ x₀
      (sbar - φ * bbar)] with ω hω M
    obtain ⟨t, ht⟩ := (hω M).exists
    exact ⟨t, by rw [rulePath_linRule]; exact ht⟩
  · filter_upwards [ar1_frequently_le hint hdef hρ] with ω hω M
    obtain ⟨t, ht⟩ := unbounded_above_of_nonpos (x₀ := x₀) (c := sbar - φ * bbar) ha.le hω M
    exact ⟨t, by rw [rulePath_linRule]; exact ht⟩

/-- Cochrane (2023), p. 197 (Theorem S for the unmodified linear rule, **every `φ > γ − 1`**,
extending `TidyR6ManagedSurplusMeasure.linear_rule_not_sustainable` beyond `φ ≤ γ`): debt stays
at or below any limit `x̄` forever with probability zero. -/
theorem linear_rule_zero_prob (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) {ρ γ φ : ℝ} (hρ : |ρ| < 1)
    (hφ : γ - 1 < φ) (sbar bbar x₀ xbar : ℝ) :
    (iidSystem ν).μ {ω | ∀ t, rulePath γ (linRule sbar φ bbar (ar1 ρ)) x₀ t ω ≤ xbar} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [linear_rule_ae_unbounded_above hint hdef hρ hφ sbar bbar x₀] with ω hω hall
  obtain ⟨t, ht⟩ := hω xbar
  exact absurd (hall t) (not_le.2 ht)

/-! ### Unmodified rule, root `γ − φ > 1`: positive probability -/

/-- Cochrane (2023), (6.4) p. 196: for a root `a ≠ 0`,
`x_t = aᵗ (x₀ − ∑_{s<t} a^{−(s+1)} w_s)` solves `x_{t+1} = a x_t − w_t`. -/
theorem debtPath_eq_discounted {a x₀ : ℝ} (ha : a ≠ 0) (w : ℕ → (ℕ → ℝ) → ℝ) (ω : ℕ → ℝ) :
    ∀ t, debtPath a x₀ w t ω =
      a ^ t * (x₀ - ∑ s ∈ Finset.range t, a⁻¹ ^ (s + 1) * w s ω) := by
  intro t
  induction t with
  | zero =>
    change x₀ = _
    simp
  | succ t ih =>
    rw [debtPath_succ, ih, Finset.sum_range_succ, pow_succ]
    have e : a ^ t * a * (a⁻¹ ^ (t + 1) * w t ω) = w t ω := by
      rw [inv_pow, pow_succ]
      field_simp
    linear_combination e

/-- Cochrane (2023), p. 197 (**unmodified linear rule with a root above one**, `φ < γ − 1`): with
`a = γ − φ > 1`, i.i.d. integrable innovations, `|ρ| < 1`, and initial debt
`x₀ ≤ −(2 (|s̄ − φ b̄| + E|ε|/(1 − |ρ|))/(a − 1) + 1)`, debt stays at or below zero forever with
probability at least `1/2`. So the linear rule's sustainability depends on `φ`: zero
probability for `φ > γ − 1` (`linear_rule_zero_prob`), positive probability for `φ < γ − 1`. -/
theorem linear_rule_half_prob (hint : Integrable id (ν : Measure ℝ)) {ρ γ φ : ℝ}
    (hρ : |ρ| < 1) (hφ : φ < γ - 1) (sbar bbar x₀ : ℝ)
    (hx₀ : x₀ ≤ -(2 * ((|sbar - φ * bbar| + (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - |ρ|)) /
      (γ - φ - 1)) + 1)) :
    ENNReal.ofReal (1 / 2) ≤
      (iidSystem ν).μ {ω | ∀ t, rulePath γ (linRule sbar φ bbar (ar1 ρ)) x₀ t ω ≤ 0} := by
  set a := γ - φ with haDef
  set c := sbar - φ * bbar with hcDef
  set B := (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - |ρ|) with hBdef
  set C := (|c| + B) / (a - 1) with hCdef
  set D := 2 * C + 1 with hDdef
  set μ := (iidSystem ν).μ with hμ
  have ha1 : 0 < a - 1 := by rw [haDef]; linarith
  have ha0 : 0 < a := by linarith
  have hr0 : 0 ≤ a⁻¹ := inv_nonneg.2 ha0.le
  have hr1 : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hB0 : 0 ≤ B := div_nonneg (integral_nonneg fun x => abs_nonneg x) (by linarith)
  have hC0 : 0 ≤ C := div_nonneg (by positivity) ha1.le
  have hD0 : 0 < D := by linarith
  have hu := integral_abs_ar1_le hint hρ
  -- the discounted absolute shock sum up to `T`
  set S : ℕ → (ℕ → ℝ) → ℝ := fun T ω =>
    ∑ s ∈ Finset.range T, a⁻¹ ^ (s + 1) * |c + ar1 ρ s ω| with hS
  have hterm : ∀ s, Integrable (fun ω => a⁻¹ ^ (s + 1) * |c + ar1 ρ s ω|) μ := fun s =>
    (((integrable_const c).add (hu s).1).abs).const_mul _
  have hSint : ∀ T, Integrable (S T) μ := fun T =>
    integrable_finsetSum _ fun s _ => hterm s
  have hgeo : ∀ T, ∑ s ∈ Finset.range T, a⁻¹ ^ (s + 1) ≤ 1 / (a - 1) := by
    intro T
    have hsum : Summable fun s : ℕ => a⁻¹ ^ (s + 1) :=
      (summable_geometric_of_lt_one hr0 hr1).mul_left a⁻¹ |>.congr fun s => by ring
    calc ∑ s ∈ Finset.range T, a⁻¹ ^ (s + 1) ≤ ∑' s, a⁻¹ ^ (s + 1) :=
          hsum.sum_le_tsum _ fun s _ => pow_nonneg hr0 _
      _ = a⁻¹ * (1 - a⁻¹)⁻¹ := by
          rw [← tsum_geometric_of_lt_one hr0 hr1, ← tsum_mul_left]
          exact tsum_congr fun s => by ring
      _ = 1 / (a - 1) := by field_simp
  have hSle : ∀ T, ∫ ω, S T ω ∂μ ≤ C := by
    intro T
    rw [show ∫ ω, S T ω ∂μ = ∑ s ∈ Finset.range T, ∫ ω, a⁻¹ ^ (s + 1) * |c + ar1 ρ s ω| ∂μ from
      integral_finsetSum _ fun s _ => hterm s]
    calc ∑ s ∈ Finset.range T, ∫ ω, a⁻¹ ^ (s + 1) * |c + ar1 ρ s ω| ∂μ
        ≤ ∑ s ∈ Finset.range T, a⁻¹ ^ (s + 1) * (|c| + B) := by
          refine Finset.sum_le_sum fun s _ => ?_
          rw [integral_const_mul]
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hr0 _)
          calc ∫ ω, |c + ar1 ρ s ω| ∂μ ≤ ∫ ω, (|c| + |ar1 ρ s ω|) ∂μ :=
                integral_mono ((integrable_const c).add (hu s).1).abs
                  ((integrable_const _).add (hu s).1.abs) fun ω => abs_add_le _ _
            _ = |c| + ∫ ω, |ar1 ρ s ω| ∂μ := by
                rw [integral_add (integrable_const _) (hu s).1.abs]
                simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
                rfl
            _ ≤ |c| + B := by linarith [(hu s).2]
      _ = (∑ s ∈ Finset.range T, a⁻¹ ^ (s + 1)) * (|c| + B) := by rw [Finset.sum_mul]
      _ ≤ 1 / (a - 1) * (|c| + B) := mul_le_mul_of_nonneg_right (hgeo T) (by positivity)
      _ = C := by rw [hCdef]; ring
  -- the events "debt at or below zero up to `T`"
  set E : ℕ → Set (ℕ → ℝ) := fun T =>
    {ω | ∀ t ≤ T, debtPath a x₀ (arSurplus ρ c) t ω ≤ 0} with hE
  have hsub : ∀ T, {ω | S T ω < D} ⊆ E T := by
    intro T ω hω t ht
    simp only [Set.mem_ofPred_eq] at hω
    rw [debtPath_eq_discounted ha0.ne']
    refine mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ha0.le t) ?_
    have hmono : ∑ s ∈ Finset.range t, a⁻¹ ^ (s + 1) * |c + ar1 ρ s ω| ≤ S T ω :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ht) fun s _ _ =>
        mul_nonneg (pow_nonneg hr0 _) (abs_nonneg _)
    have habs : -(∑ s ∈ Finset.range t, a⁻¹ ^ (s + 1) * arSurplus ρ c s ω) ≤
        ∑ s ∈ Finset.range t, a⁻¹ ^ (s + 1) * |c + ar1 ρ s ω| := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun s _ => ?_
      rw [arSurplus]
      have := neg_abs_le (c + ar1 ρ s ω)
      nlinarith [pow_nonneg hr0 (s + 1)]
    linarith
  have hET : ∀ T, ENNReal.ofReal (1 / 2) ≤ μ (E T) := by
    intro T
    have hmk := mul_meas_ge_le_integral_of_nonneg (μ := μ)
      (Eventually.of_forall fun ω => Finset.sum_nonneg fun s _ =>
        mul_nonneg (pow_nonneg hr0 (s + 1)) (abs_nonneg (c + ar1 ρ s ω))) (hSint T) D
    have hreal : μ.real {ω | D ≤ S T ω} ≤ 1 / 2 := by
      have h1 : D * μ.real {ω | D ≤ S T ω} ≤ C := hmk.trans (hSle T)
      have hpr := measureReal_nonneg (μ := μ) (s := {ω | D ≤ S T ω})
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    have hcompl : {ω | D ≤ S T ω}ᶜ = {ω | S T ω < D} := by
      ext ω
      simp
    have hm : MeasurableSet {ω | D ≤ S T ω} :=
      measurableSet_le measurable_const (Finset.measurable_sum _ fun s _ =>
        (continuous_abs.measurable.comp ((measurable_ar1 ρ s).const_add c)).const_mul _)
    have hlow : 1 / 2 ≤ μ.real {ω | S T ω < D} := by
      rw [← hcompl, measureReal_compl hm, probReal_univ]
      linarith
    calc ENNReal.ofReal (1 / 2) ≤ ENNReal.ofReal (μ.real {ω | S T ω < D}) :=
          ENNReal.ofReal_le_ofReal hlow
      _ = μ {ω | S T ω < D} := ofReal_measureReal
      _ ≤ μ (E T) := measure_mono (hsub T)
  -- continuity from above
  have hEm : ∀ T, NullMeasurableSet (E T) μ := fun T => by
    have : E T = ⋂ t ∈ Finset.range (T + 1),
        {ω | debtPath a x₀ (arSurplus ρ c) t ω ≤ 0} := by
      ext ω
      simp only [hE, Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range]
      exact ⟨fun h t ht => h t (by omega), fun h t ht => h t (by omega)⟩
    rw [this]
    exact (Finset.measurableSet_biInter _ fun t _ =>
      measurableSet_le (measurable_arDebt a x₀ ρ c t) measurable_const).nullMeasurableSet
  have hanti : Antitone E := fun T T' h ω hω t ht => hω t (ht.trans h)
  have hlim := tendsto_measure_iInter_atTop hEm hanti ⟨0, measure_ne_top μ _⟩
  have hinter : (⋂ T, E T) =
      {ω | ∀ t, rulePath γ (linRule sbar φ bbar (ar1 ρ)) x₀ t ω ≤ 0} := by
    ext ω
    simp only [hE, Set.mem_iInter, Set.mem_ofPred_eq, rulePath_linRule]
    exact ⟨fun h t => h t t le_rfl, fun h T t _ => h t⟩
  rw [← hinter]
  exact ge_of_tendsto' hlim hET

/-- Cochrane (2023), p. 197: for EVERY response `φ` and every initial debt, the unmodified
linear rule carries debt above any limit `x̄` at date 1 with positive probability (deficit shocks
of every size), so no unmodified linear rule is sustainable almost surely. -/
theorem linear_rule_not_ae_sustainable (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0)
    (ρ γ φ sbar bbar x₀ xbar : ℝ) :
    ¬ ∀ᵐ ω ∂(iidSystem ν).μ, ∀ t, rulePath γ (linRule sbar φ bbar (ar1 ρ)) x₀ t ω ≤ xbar := by
  intro h
  set K := γ * x₀ - (sbar + φ * (x₀ - bbar)) - xbar - 1 with hK
  have h1 : ∀ᵐ ω ∂(iidSystem ν).μ, ω ∉ shock 0 ⁻¹' Set.Iic K := by
    filter_upwards [h] with ω hω hmem
    have h1 := hω 1
    change γ * x₀ - (sbar + ω 0 + φ * (x₀ - bbar)) ≤ xbar at h1
    simp only [Set.mem_preimage, Set.mem_Iic, shock] at hmem
    linarith
  have h0 := (measure_eq_zero_iff_ae_notMem.2 h1)
  rw [measure_shock_preimage 0 measurableSet_Iic] at h0
  exact hdef (-K) (by rw [neg_neg]; exact h0)

/-! ### The one-sided plan is unbounded below -/

/-- Cochrane (2023), p. 197: on any path on which the AR(1) rises above every level infinitely
often, the one-sided boundary-avoiding plan is unbounded below, for every `γ` and every `φ`. -/
theorem plan_unbounded_below_of_frequently {γ φ ρ sbar bbar xbar m₀ : ℝ} {ω : ℕ → ℝ}
    (hfreq : ∀ K : ℝ, ∃ᶠ t in atTop, K ≤ ar1 ρ t ω) (L : ℝ) :
    ∃ t, avoidPath γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀ t ω < L := by
  set F := linRule sbar φ bbar (ar1 ρ)
  set a := γ - φ
  set U := max xbar m₀
  by_contra hcon
  have hall : ∀ t, L ≤ avoidPath γ xbar F m₀ t ω := fun t => not_lt.1 fun h => hcon ⟨t, h⟩
  have hup : ∀ t, avoidPath γ xbar F m₀ t ω ≤ U := by
    intro t
    cases t with
    | zero => exact le_max_right _ _
    | succ t => exact (avoidPath_le γ xbar F m₀ t ω).trans (le_max_left _ _)
  obtain ⟨t, ht⟩ := (hfreq (max (a * L) (a * U) - (sbar - φ * bbar) - L + 1)).exists
  have hmm := (mul_mem_minmax (a := a) (hall t) (hup t)).2
  have hstep : avoidPath γ xbar F m₀ (t + 1) ω ≤
      γ * avoidPath γ xbar F m₀ t ω - F t (avoidPath γ xbar F m₀ t ω) ω := min_le_right _ _
  rw [linRule_response] at hstep
  have := hall (t + 1)
  linarith

/-- Cochrane (2023), p. 197 (**the one-sided managed plan is a.s. unbounded below**): with i.i.d.
integrable innovations with surpluses of every size and `|ρ| < 1`, for every `γ`, `φ` and `m₀`,
the plan almost surely falls below every level: the government accumulates assets without
bound. -/
theorem plan_ae_unbounded_below (hint : Integrable id (ν : Measure ℝ))
    (hup : ∀ c : ℝ, (ν : Measure ℝ) (Set.Ici c) ≠ 0) {ρ : ℝ} (hρ : |ρ| < 1)
    (γ φ sbar bbar xbar m₀ : ℝ) :
    ∀ᵐ ω ∂(iidSystem ν).μ, ∀ L : ℝ, ∃ t,
      avoidPath γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀ t ω < L := by
  filter_upwards [ar1_frequently_ge hint hup hρ] with ω hω L
  exact plan_unbounded_below_of_frequently hω L

/-- Cochrane (2023), p. 197: actual debt `x_t = m_t + γᵗ (x₀ − m₀)` under the one-sided plan,
from any initial debt `x₀`, is almost surely unbounded below too (`0 ≤ γ ≤ 1`). -/
theorem plan_debt_ae_unbounded_below (hint : Integrable id (ν : Measure ℝ))
    (hup : ∀ c : ℝ, (ν : Measure ℝ) (Set.Ici c) ≠ 0) {ρ γ : ℝ} (hρ : |ρ| < 1) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (φ sbar bbar xbar m₀ x₀ : ℝ) :
    ∀ᵐ ω ∂(iidSystem ν).μ, ∀ L : ℝ, ∃ t,
      debtPath γ x₀ (avoidSurplus γ xbar (linRule sbar φ bbar (ar1 ρ)) m₀) t ω < L := by
  filter_upwards [plan_ae_unbounded_below hint hup hρ γ φ sbar bbar xbar m₀] with ω hω L
  obtain ⟨t, ht⟩ := hω (L - |x₀ - m₀|)
  refine ⟨t, ?_⟩
  rw [avoid_plan_debtPath]
  have hp : γ ^ t ≤ 1 := pow_le_one₀ hγ0 hγ1
  have h1 : γ ^ t * (x₀ - m₀) ≤ |x₀ - m₀| := by
    calc γ ^ t * (x₀ - m₀) ≤ γ ^ t * |x₀ - m₀| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (pow_nonneg hγ0 t)
      _ ≤ 1 * |x₀ - m₀| := mul_le_mul_of_nonneg_right hp (abs_nonneg _)
      _ = |x₀ - m₀| := one_mul _
  linarith

end Cochrane.FiscalConstraints.TidyR6LinearRuleBounds
