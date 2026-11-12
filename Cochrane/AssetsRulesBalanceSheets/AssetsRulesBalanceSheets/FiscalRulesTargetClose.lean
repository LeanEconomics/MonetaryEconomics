/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.FiscalRulesBelowCounter

/-!
# Theorem FR (d): existence, the bounded-below case with news, random date-0 data

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.3.2,
eqs. (9.8)–(9.12), pp. 266–267 (Theorem FR, error E9.9).

This module closes three cases left open by `FiscalRulesTargetOpen` and `FiscalRulesBelowCounter`.

## Main results

* **Prices bounded away from zero, target with news** (`fr_compare_below`, `fr_unique_below_news`,
  `fr_d_news_below`). Assume the bounded cumulative real-rate factor `∏ E(P*/P*′)⁻¹ ≤ L`. Then an
  equilibrium with `P ≥ m_P > 0` coincides with any bounded-above equilibrium with the same
  initial debt; with `b₀ = b̄` it is `P = P*`. No predetermined target value is needed.
  * Key bound (`ratio_bdd`): `|D_t| ≤ L (M*/m_P + 1)/(1 − β) · P_t`. The debt deviation is at most
    a fixed multiple of the price level. This feeds the one-sided growth arguments
    `compare_step_le` and `compare_step_ratio`.
* **Random date-0 data without an assumed band** (`fr_unique_s0_random_full`,
  `fr_unique_s0_random_below_full`): `P = (1 + (b₀ − B₀)/(θ a₀)) P*`.
  * The band `c ∈ [c_min, c_max]` is derived: `c > 0` a.e. because the value of the price path is
    positive.
  * The proof localises on `{1/(n+1) ≤ c ≤ n+1}`.
* **Existence with news and `b₀ ≠ b̄`, news at a single date** (`oneShot`, `osTarget`):
  * `oneShot_eqm_form` and `oneShot_eqm_exists`: an equilibrium exists iff a scalar `d` solves the
    date-0 interest-rate target equation with positive prices.
  * `oneShot_exists_iff_atom`: when the target attains its infimum with positive probability (e.g.
    a finite tree), existence holds iff the realised present value of the target plus `d₀` is
    positive on every path.
  * `NoExist.oneShot_no_eqm`: existence can fail. On `(ℕ, ∑ π_k δ_k)` the infimum is not attained
    and no bounded-above equilibrium exists, although the realised present value plus `d₀` is at
    least `1/10` on every path.
-/

namespace Cochrane.AssetsRulesBalanceSheets.FiscalRulesTargetClose

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure FiscalRulesMeasure FiscalRulesTargetMeasure FiscalRulesTargetOpen

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-! ### The growth argument, one-sided -/

/-- Cochrane (2023), eqs. (9.8), (9.12), pp. 266–267 (Theorem FR (d), the growth argument): if on a
date-`t` event `A` of positive probability `P_t < P'_t` and `Δ_{t+1} > δ`, then for every `k` there
is a date-`(t+k)` event of positive probability on which `P_{t+k} < P'_{t+k}` and
`Δ_{t+k+1} > δ/βᵏ`. -/
theorem propagate {β δ : ℝ} (hβ0 : 0 < β) {P P' Δ : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (hP' : ∀ t ω, 0 < P' t ω)
    (hPa : StronglyAdapted S.𝓕 P) (hP'a : StronglyAdapted S.𝓕 P')
    (hq : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ)
    (hq' : ∀ t, Integrable (fun ω => 1 / P' t ω) S.μ)
    (hr : ∀ t, ∀ᵐ ω ∂S.μ, P t ω * S.E t (fun ω => 1 / P (t + 1) ω) ω =
      P' t ω * S.E t (fun ω => 1 / P' (t + 1) ω) ω)
    (hΔ : ∀ t ω, Δ t ω = P t ω - P' t ω + β * Δ (t + 1) ω) {t : ℕ} {A : Set Ω}
    (hAm : MeasurableSet[S.𝓕 t] A) (hA0 : 0 < S.μ A)
    (hA : ∀ ω ∈ A, P t ω < P' t ω ∧ δ < Δ (t + 1) ω) (k : ℕ) :
    ∃ A : Set Ω, MeasurableSet[S.𝓕 (t + k)] A ∧ 0 < S.μ A ∧
      ∀ ω ∈ A, P (t + k) ω < P' (t + k) ω ∧ δ / β ^ k < Δ (t + k + 1) ω := by
  induction k with
  | zero => exact ⟨A, hAm, hA0, fun ω hω => by simpa using hA ω hω⟩
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
      have h4 : δ / β ^ k / β < Δ (t + k + 1) ω / β := div_lt_div_of_pos_right h3 hβ0
      rw [div_div, ← pow_succ] at h4
      refine h4.trans ?_
      rw [div_lt_iff₀ hβ0]
      linarith

/-- Cochrane (2023), pp. 266–267 (supporting the growth argument): if `Δ_{t+1} > 0` on a set of
positive probability, it exceeds some `δ = 1/(n + 1)` there. -/
theorem exists_delta {t : ℕ} {Δ : ℕ → Ω → ℝ} (hcon : ¬ ∀ᵐ ω ∂S.μ, Δ (t + 1) ω ≤ 0) :
    ∃ n : ℕ, S.μ {ω | 1 / ((n : ℝ) + 1) < Δ (t + 1) ω} ≠ 0 := by
  by_contra h
  push Not at h
  apply hcon
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) (measure_iUnion_null h)
  simp only [Set.mem_ofPred_eq, not_le] at hω
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hω
  exact Set.mem_iUnion.2 ⟨k, hk⟩

/-- Cochrane (2023), pp. 266–267 (supporting the growth argument): the base event — if `Δ_t = 0`
a.e. and `Δ_{t+1} > δ` on a set of positive probability, then on its intersection with `{Δ_t = 0}`
(still of positive probability, known at `t`) also `P_t < P'_t`. -/
theorem base_event {β δ : ℝ} (hβ0 : 0 < β) {P P' Δ : ℕ → Ω → ℝ}
    (hPa : StronglyAdapted S.𝓕 P) (hP'a : StronglyAdapted S.𝓕 P')
    (hΔ : ∀ t ω, Δ t ω = P t ω - P' t ω + β * Δ (t + 1) ω)
    (hΔm : ∀ t, StronglyMeasurable[S.𝓕 t] (Δ (t + 1))) {t : ℕ}
    (h0 : ∀ᵐ ω ∂S.μ, Δ t ω = 0) (hδ0 : 0 < δ) (hn : S.μ {ω | δ < Δ (t + 1) ω} ≠ 0) :
    MeasurableSet[S.𝓕 t] ({ω | δ < Δ (t + 1) ω} ∩ {ω | Δ t ω = 0}) ∧
      0 < S.μ ({ω | δ < Δ (t + 1) ω} ∩ {ω | Δ t ω = 0}) ∧
      ∀ ω ∈ {ω | δ < Δ (t + 1) ω} ∩ {ω | Δ t ω = 0}, P t ω < P' t ω ∧ δ < Δ (t + 1) ω := by
  have hΔm' : StronglyMeasurable[S.𝓕 t] (Δ t) := by
    have e : Δ t = fun ω => P t ω - P' t ω + β * Δ (t + 1) ω := funext (hΔ t)
    rw [e]
    exact ((hPa t).sub (hP'a t)).add ((hΔm t).const_mul β)
  refine ⟨(measurableSet_lt stronglyMeasurable_const.measurable (hΔm t).measurable).inter
    (measurableSet_eq_fun hΔm'.measurable measurable_const), ?_, fun ω hω => ?_⟩
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
    exact ⟨by nlinarith, h1⟩

/-- Cochrane (2023), pp. 266–267 (Theorem FR (d), growth argument, `Δ` bounded above): if `Δ_t = 0`
a.e. and `Δ ≤ B` a.e. at every date, then `Δ_{t+1} ≤ 0` a.e. -/
theorem compare_step_le {β B : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {P P' Δ : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (hP' : ∀ t ω, 0 < P' t ω)
    (hPa : StronglyAdapted S.𝓕 P) (hP'a : StronglyAdapted S.𝓕 P')
    (hq : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ)
    (hq' : ∀ t, Integrable (fun ω => 1 / P' t ω) S.μ)
    (hr : ∀ t, ∀ᵐ ω ∂S.μ, P t ω * S.E t (fun ω => 1 / P (t + 1) ω) ω =
      P' t ω * S.E t (fun ω => 1 / P' (t + 1) ω) ω)
    (hΔ : ∀ t ω, Δ t ω = P t ω - P' t ω + β * Δ (t + 1) ω)
    (hΔm : ∀ t, StronglyMeasurable[S.𝓕 t] (Δ (t + 1)))
    (hΔB : ∀ t, ∀ᵐ ω ∂S.μ, Δ t ω ≤ B) {t : ℕ} (h0 : ∀ᵐ ω ∂S.μ, Δ t ω = 0) :
    ∀ᵐ ω ∂S.μ, Δ (t + 1) ω ≤ 0 := by
  by_contra hcon
  obtain ⟨n, hn⟩ := exists_delta S hcon
  have hδ0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  obtain ⟨hAm, hA0, hA⟩ := base_event S hβ0 hPa hP'a hΔ hΔm h0 hδ0 hn
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
    (div_pos hδ0 (by positivity : (0 : ℝ) < |B| + 1)) hβ1
  obtain ⟨A, -, hA0', hA'⟩ := propagate S hβ0 hP hP' hPa hP'a hq hq' hr hΔ hAm hA0 hA k
  have hnull : S.μ A = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 (hΔB (t + k + 1)))
    simp only [Set.mem_ofPred_eq, not_le]
    have hβk := pow_pos hβ0 k
    have h1 := (hA' ω hω).2
    have h2 : |B| + 1 < 1 / ((n : ℝ) + 1) / β ^ k := by
      rw [lt_div_iff₀ hβk]
      rw [lt_div_iff₀ (by positivity)] at hk
      linarith
    linarith [le_abs_self B]
  exact absurd hnull hA0'.ne'

/-- Cochrane (2023), pp. 266–267 (Theorem FR (d), growth argument, comparison path bounded): if
`P' ≤ M'`, `Δ_t = 0` a.e. and `Δ ≤ B` a.e. wherever `P < P'`, then `Δ_{t+1} ≤ 0` a.e. -/
theorem compare_step_ratio {β B M' : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {P P' Δ : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (hP' : ∀ t ω, 0 < P' t ω) (hP'M : ∀ t ω, P' t ω ≤ M')
    (hPa : StronglyAdapted S.𝓕 P) (hP'a : StronglyAdapted S.𝓕 P')
    (hq : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ)
    (hq' : ∀ t, Integrable (fun ω => 1 / P' t ω) S.μ)
    (hr : ∀ t, ∀ᵐ ω ∂S.μ, P t ω * S.E t (fun ω => 1 / P (t + 1) ω) ω =
      P' t ω * S.E t (fun ω => 1 / P' (t + 1) ω) ω)
    (hΔ : ∀ t ω, Δ t ω = P t ω - P' t ω + β * Δ (t + 1) ω)
    (hΔm : ∀ t, StronglyMeasurable[S.𝓕 t] (Δ (t + 1)))
    (hΔB : ∀ t, ∀ᵐ ω ∂S.μ, P t ω < P' t ω → Δ t ω ≤ B) {t : ℕ}
    (h0 : ∀ᵐ ω ∂S.μ, Δ t ω = 0) : ∀ᵐ ω ∂S.μ, Δ (t + 1) ω ≤ 0 := by
  by_contra hcon
  obtain ⟨n, hn⟩ := exists_delta S hcon
  have hδ0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  obtain ⟨hAm, hA0, hA⟩ := base_event S hβ0 hPa hP'a hΔ hΔm h0 hδ0 hn
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
    (div_pos (mul_pos hβ0 hδ0) (by positivity : (0 : ℝ) < |B| + |M'| + 1)) hβ1
  obtain ⟨A, -, hA0', hA'⟩ := propagate S hβ0 hP hP' hPa hP'a hq hq' hr hΔ hAm hA0 hA k
  have hnull : S.μ A = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 (hΔB (t + k)))
    simp only [Set.mem_ofPred_eq, not_imp, not_le]
    have hβk := pow_pos hβ0 k
    obtain ⟨h1, h2⟩ := hA' ω hω
    refine ⟨h1, ?_⟩
    have h3 : |B| + |M'| + 1 < β * (1 / ((n : ℝ) + 1)) / β ^ k := by
      rw [lt_div_iff₀ hβk]
      rw [lt_div_iff₀ (by positivity)] at hk
      linarith
    have h4 : β * (1 / ((n : ℝ) + 1)) / β ^ k < β * Δ (t + k + 1) ω := by
      rw [mul_div_assoc]
      exact mul_lt_mul_of_pos_left h2 hβ0
    have e := hΔ (t + k) ω
    linarith [le_abs_self B, le_abs_self M', hP (t + k) ω, hP'M (t + k) ω]
  exact absurd hnull hA0'.ne'

/-- Cochrane (2023), eq. (9.9), p. 266 (supporting): if `D_t = P_t − P*_t + β D_{t+1}` with
`P > 0`, `P* ≤ M*`, `D` predetermined, integrable and transversal, then `D_t ≥ −M*/(1 − β)` a.e.:
the present value of price deviations is bounded below whenever prices are positive. -/
theorem value_lower {β Ms : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Pstar P D : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (hPa : StronglyAdapted S.𝓕 P) (hPi : ∀ t, Integrable (P t) S.μ)
    (hPsa : StronglyAdapted S.𝓕 Pstar) (hPs0 : ∀ t ω, 0 < Pstar t ω)
    (hPsM : ∀ t ω, Pstar t ω ≤ Ms)
    (hD : ∀ t ω, D t ω = P t ω - Pstar t ω + β * D (t + 1) ω)
    (hDpre : ∀ t, StronglyMeasurable[S.𝓕 t] (D (t + 1))) (hDi : ∀ t, Integrable (D t) S.μ)
    (htvc : ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun k => β ^ k * S.E t (D (t + k)) ω) atTop (𝓝 0))
    (t : ℕ) : ∀ᵐ ω ∂S.μ, -(Ms / (1 - β)) ≤ D t ω := by
  have hDm : ∀ t, StronglyMeasurable[S.𝓕 t] (D t) := fun t => by
    have e : D t = fun ω => P t ω - Pstar t ω + β * D (t + 1) ω := funext (hD t)
    rw [e]
    exact ((hPa t).sub (hPsa t)).add ((hDpre t).const_mul β)
  have hPsi : ∀ t, Integrable (Pstar t) S.μ := fun t =>
    Integrable.of_bound ((hPsa t).mono (S.𝓕.le t)).aestronglyMeasurable Ms
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (hPs0 t ω)]; exact hPsM t ω)
  have hsi : ∀ t, Integrable (fun ω => P t ω - Pstar t ω) S.μ := fun t => (hPi t).sub (hPsi t)
  have hE : ∀ j, ∀ᵐ ω ∂S.μ, -Ms ≤ S.E t (fun ω => P (t + j) ω - Pstar (t + j) ω) ω := fun j => by
    have h := S.E_mono (integrable_const (-Ms)) (hsi (t + j))
      (Eventually.of_forall fun ω => by
        change -Ms ≤ P (t + j) ω - Pstar (t + j) ω
        linarith [hP (t + j) ω, hPsM (t + j) ω]) t
    rw [S.E_const] at h
    exact h
  filter_upwards [ae_all_iff.2 (value_partial S (P := fun t ω => P t ω - Pstar t ω) hD hDm hDi
    hsi t), htvc t, ae_all_iff.2 hE] with ω h1 h2 h3
  have hMs : 0 ≤ Ms := (hPs0 0 ω).le.trans (hPsM 0 ω)
  have hpart : Tendsto (fun k => ∑ j ∈ Finset.range k,
      β ^ j * S.E t (fun ω => P (t + j) ω - Pstar (t + j) ω) ω) atTop (𝓝 (D t ω)) := by
    have := (tendsto_const_nhds (x := D t ω)).sub h2
    rw [sub_zero] at this
    exact this.congr fun k => by linarith [h1 k]
  have hgeo := summable_geometric_of_lt_one hβ0.le hβ1
  refine ge_of_tendsto' hpart fun k => ?_
  calc -(Ms / (1 - β)) = -(Ms * ∑' j, β ^ j) := by
        rw [tsum_geometric_of_lt_one hβ0.le hβ1, div_eq_mul_inv]
    _ ≤ -(Ms * ∑ j ∈ Finset.range k, β ^ j) := neg_le_neg (mul_le_mul_of_nonneg_left
        (hgeo.sum_le_tsum _ fun j _ => pow_nonneg hβ0.le j) hMs)
    _ = ∑ j ∈ Finset.range k, β ^ j * (-Ms) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ _ := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h3 j) (pow_pos hβ0 j).le

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d), the key bound for prices bounded away
from zero**): let `P ≥ m_P > 0` satisfy the interest-rate target (9.12) for a bounded target
`0 < m ≤ P* ≤ M*` — whose present value may carry news — with the bounded cumulative real-rate
factor `∏ E(P*/P*′)⁻¹ ≤ L`, and let `D_t = P_t − P*_t + β D_{t+1}` be predetermined, integrable and
transversal. Then `|D_t| ≤ L (M*/m_P + 1)/(1 − β) · P_t` a.e.: the debt deviation is at most a
fixed multiple of the price level. Proof: `ξ = D/P` satisfies
`E_t ξ_{t+1} = (γ_t/β)(ξ_t − 1 + P*_t/P_t)`, so `Ξ_t = βᵗ N_t⁻¹ ξ_t` has drift
`βᵗ N_t⁻¹ (P*_t/P_t − 1)`, and the transversality condition with `N⁻¹ ≤ L N_t⁻¹` sums the drift. -/
theorem ratio_bdd {β m Ms mP L : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Pstar P D : ℕ → Ω → ℝ}
    (hPa : StronglyAdapted S.𝓕 P) (hmP : 0 < mP) (hPmP : ∀ t ω, mP ≤ P t ω)
    (hPi : ∀ t, Integrable (P t) S.μ) (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hrate : ∀ t, S.E t (P t / P (t + 1)) =ᵐ[S.μ] S.E t (Pstar t / Pstar (t + 1)))
    (hD : ∀ t ω, D t ω = P t ω - Pstar t ω + β * D (t + 1) ω)
    (hDpre : ∀ t, StronglyMeasurable[S.𝓕 t] (D (t + 1))) (hDi : ∀ t, Integrable (D t) S.μ)
    (htvc : ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun k => β ^ k * S.E t (D (t + k)) ω) atTop (𝓝 0))
    (hL : ∀ t k, ∀ᵐ ω ∂S.μ, ∏ i ∈ Finset.range k,
      (Pstar (t + i) ω * S.E (t + i) (fun ω => 1 / Pstar (t + i + 1) ω) ω)⁻¹ ≤ L)
    (t : ℕ) : ∀ᵐ ω ∂S.μ, |D t ω| ≤ L * (Ms / mP + 1) / (1 - β) * P t ω := by
  rcases isEmpty_or_nonempty Ω with hΩ | ⟨⟨ω0⟩⟩
  · exact Eventually.of_forall fun ω => (IsEmpty.false ω).elim
  -- basic facts
  have h1β : 0 < 1 - β := by linarith
  have hPm : ∀ t, StronglyMeasurable[S.𝓕 t] (P t) := fun t => hPa t
  have hPsm : ∀ t, StronglyMeasurable[S.𝓕 t] (Pstar t) := fun t => hPsa t
  have hPs0 : ∀ t ω, 0 < Pstar t ω := fun t ω => hm.trans_le (hPs t ω).1
  have hP : ∀ t ω, 0 < P t ω := fun t ω => hmP.trans_le (hPmP t ω)
  have hMs : 0 < Ms := (hPs0 0 ω0).trans_le (hPs 0 ω0).2
  have hDm : ∀ t, StronglyMeasurable[S.𝓕 t] (D t) := fun t => by
    have e : D t = fun ω => P t ω - Pstar t ω + β * D (t + 1) ω := funext (hD t)
    rw [e]
    exact ((hPm t).sub (hPsm t)).add ((hDpre t).const_mul β)
  set qs : ℕ → Ω → ℝ := fun t ω => 1 / Pstar t ω with hqs_def
  set q : ℕ → Ω → ℝ := fun t ω => 1 / P t ω with hq_def
  have hqsm : ∀ t, StronglyMeasurable[S.𝓕 t] (qs t) := fun t =>
    ((hPsm t).measurable.const_div 1).stronglyMeasurable
  have hqm : ∀ t, StronglyMeasurable[S.𝓕 t] (q t) := fun t =>
    ((hPm t).measurable.const_div 1).stronglyMeasurable
  have hqb : ∀ t ω, 0 < q t ω ∧ q t ω ≤ 1 / mP := fun t ω =>
    ⟨one_div_pos.2 (hP t ω), one_div_le_one_div_of_le hmP (hPmP t ω)⟩
  have hqP : ∀ t ω, q t ω * P t ω = 1 := fun t ω => by
    simp only [hq_def]
    field_simp [(hP t ω).ne']
  have hqsb : ∀ t ω, 1 / Ms ≤ qs t ω ∧ qs t ω ≤ 1 / m := fun t ω =>
    ⟨one_div_le_one_div_of_le (hPs0 t ω) (hPs t ω).2, one_div_le_one_div_of_le hm (hPs t ω).1⟩
  have hqi : ∀ t, Integrable (q t) S.μ := fun t =>
    Integrable.of_bound ((hqm t).mono (S.𝓕.le t)).aestronglyMeasurable (1 / mP)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (hqb t ω).1]; exact (hqb t ω).2)
  have hqsi : ∀ t, Integrable (qs t) S.μ := fun t =>
    Integrable.of_bound ((hqsm t).mono (S.𝓕.le t)).aestronglyMeasurable (1 / m)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (hPs0 t ω))]; exact (hqsb t ω).2)
  have hqbd : ∀ t, ∀ᵐ ω ∂S.μ, ‖q t ω‖ ≤ 1 / mP := fun t => Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_pos (hqb t ω).1]; exact (hqb t ω).2
  -- `γ_t = E_t(P*_t/P*_{t+1})`
  set γ : ℕ → Ω → ℝ := fun t ω => Pstar t ω * S.E t (qs (t + 1)) ω with hγ_def
  have hEqs : ∀ t, ∀ᵐ ω ∂S.μ, 1 / Ms ≤ S.E t (qs (t + 1)) ω ∧
      S.E t (qs (t + 1)) ω ≤ 1 / m := fun t => by
    have h1 := S.E_mono (integrable_const (1 / Ms)) (hqsi (t + 1))
      (Eventually.of_forall fun ω => (hqsb (t + 1) ω).1) t
    have h2 := S.E_mono (hqsi (t + 1)) (integrable_const (1 / m))
      (Eventually.of_forall fun ω => (hqsb (t + 1) ω).2) t
    rw [S.E_const] at h1 h2
    filter_upwards [h1, h2] with ω e1 e2
    exact ⟨e1, e2⟩
  have hγm : ∀ t, StronglyMeasurable[S.𝓕 t] (γ t) := fun t =>
    (hPsm t).mul (S.stronglyMeasurable_E t _)
  have hγb : ∀ t, ∀ᵐ ω ∂S.μ, m / Ms ≤ γ t ω ∧ γ t ω ≤ Ms / m := fun t => by
    filter_upwards [hEqs t] with ω h
    constructor
    · calc m / Ms = m * (1 / Ms) := by ring
        _ ≤ Pstar t ω * S.E t (qs (t + 1)) ω :=
          mul_le_mul (hPs t ω).1 h.1 (by positivity) (hPs0 t ω).le
    · calc Pstar t ω * S.E t (qs (t + 1)) ω ≤ Ms * (1 / m) :=
          mul_le_mul (hPs t ω).2 h.2 ((one_div_pos.2 hMs).le.trans h.1) hMs.le
        _ = Ms / m := by ring
  have hγpos : ∀ t, ∀ᵐ ω ∂S.μ, 0 < γ t ω := fun t => by
    filter_upwards [hγb t] with ω h
    exact (div_pos hm hMs).trans_le h.1
  -- the rate target: `E_t q_{t+1} = γ_t q_t`
  have hqrate : ∀ t, S.E t (q (t + 1)) =ᵐ[S.μ] γ t * q t := fun t => by
    have e1 : P t / P (t + 1) = P t * q (t + 1) := by
      funext ω
      simp [hq_def, div_eq_mul_inv]
    have e2 : Pstar t / Pstar (t + 1) = Pstar t * qs (t + 1) := by
      funext ω
      simp [hqs_def, div_eq_mul_inv]
    have hint : Integrable (P t * q (t + 1)) S.μ := by
      have := (hPi t).bdd_mul ((hqm (t + 1)).mono (S.𝓕.le _)).aestronglyMeasurable (hqbd (t + 1))
      exact this.congr (Eventually.of_forall fun ω => mul_comm _ _)
    have h1 : S.E t (P t * q (t + 1)) =ᵐ[S.μ] P t * S.E t (q (t + 1)) :=
      condExp_mul_of_stronglyMeasurable_left (hPm t) hint (hqi (t + 1))
    have h2 := S.E_pullOut (hPsm t) (C := Ms) (Eventually.of_forall fun ω => by
      rw [abs_of_pos (hPs0 t ω)]; exact (hPs t ω).2) (hqsi (t + 1))
    have h3 := hrate t
    rw [e1, e2] at h3
    filter_upwards [h1, h2, h3] with ω f1 f2 f3
    rw [f1, f2] at f3
    simp only [Pi.mul_apply] at f3 ⊢
    have hp := (hP t ω).ne'
    rw [show γ t ω * q t ω = Pstar t ω * S.E t (qs (t + 1)) ω / P t ω by
      simp only [hγ_def, hq_def]; ring, eq_div_iff hp]
    linarith
  -- `ξ = q D` and its forecast
  set xi : ℕ → Ω → ℝ := fun t ω => q t ω * D t ω with hxi_def
  have hxii : ∀ t, Integrable (xi t) S.μ := fun t =>
    (hDi t).bdd_mul ((hqm t).mono (S.𝓕.le t)).aestronglyMeasurable (hqbd t)
  have hExi : ∀ t, ∀ᵐ ω ∂S.μ, S.E t (xi (t + 1)) ω * β =
      γ t ω * (xi t ω - 1 + Pstar t ω * q t ω) := fun t => by
    have e : xi (t + 1) = D (t + 1) * q (t + 1) := by
      funext ω
      simp only [hxi_def, Pi.mul_apply]
      ring
    have hint : Integrable (D (t + 1) * q (t + 1)) S.μ := by
      rw [← e]
      exact hxii (t + 1)
    have h1 := condExp_mul_of_stronglyMeasurable_left (m := S.𝓕 t) (μ := S.μ) (hDpre t) hint
      (hqi (t + 1))
    filter_upwards [h1, hqrate t] with ω e1 e2
    have e1' : S.E t (xi (t + 1)) ω = D (t + 1) ω * S.E t (q (t + 1)) ω := by
      rw [e]
      exact e1
    rw [e1', e2, Pi.mul_apply]
    have h3 := hD t ω
    have h4 := hqP t ω
    simp only [hxi_def, hγ_def]
    linear_combination (-(Pstar t ω * S.E t (qs (t + 1)) ω * q t ω)) * h3 -
      (Pstar t ω * S.E t (qs (t + 1)) ω) * h4
  -- the deflator `N_t⁻¹ = ∏_{i<t} γ_i⁻¹`
  set Ninv : ℕ → Ω → ℝ := fun t ω => ∏ i ∈ Finset.range t, (γ i ω)⁻¹ with hN_def
  have hNmeas : ∀ s t, s ≤ t + 1 → StronglyMeasurable[S.𝓕 t] (Ninv s) := fun s t hst => by
    have : Measurable[S.𝓕 t] (Ninv s) := Finset.measurable_prod _ fun i hi =>
      ((hγm i).mono (S.𝓕.mono (by have := Finset.mem_range.1 hi; omega))).measurable.inv
    exact this.stronglyMeasurable
  have hNb : ∀ t, ∀ᵐ ω ∂S.μ, 0 < Ninv t ω ∧ Ninv t ω ≤ (Ms / m) ^ t := fun t => by
    filter_upwards [ae_all_iff.2 hγb] with ω h
    have hpos : ∀ i, 0 < γ i ω := fun i => (div_pos hm hMs).trans_le (h i).1
    refine ⟨Finset.prod_pos fun i _ => inv_pos.2 (hpos i), ?_⟩
    calc Ninv t ω ≤ ∏ _i ∈ Finset.range t, Ms / m :=
          Finset.prod_le_prod₀ (fun i _ => (inv_pos.2 (hpos i)).le) fun i _ => by
            rw [← inv_div]
            exact inv_anti₀ (div_pos hm hMs) (h i).1
      _ = (Ms / m) ^ t := by rw [Finset.prod_const, Finset.card_range]
  have hNγ : ∀ t, ∀ᵐ ω ∂S.μ, Ninv (t + 1) ω * γ t ω = Ninv t ω := fun t => by
    filter_upwards [hγpos t] with ω h
    simp only [hN_def, Finset.prod_range_succ]
    field_simp
  have hNL : ∀ j, ∀ᵐ ω ∂S.μ, Ninv (t + j) ω ≤ L * Ninv t ω := fun j => by
    filter_upwards [hL t j, hNb t] with ω h1 h2
    calc Ninv (t + j) ω = Ninv t ω * ∏ i ∈ Finset.range j, (γ (t + i) ω)⁻¹ := by
          simp only [hN_def, Finset.prod_range_add]
      _ ≤ Ninv t ω * L := mul_le_mul_of_nonneg_left h1 h2.1.le
      _ = L * Ninv t ω := by ring
  -- the drift `g_s = βˢ N_s⁻¹ (P*_s q_s − 1)` and `Ξ_s = βˢ N_s⁻¹ ξ_s`
  set C0 : ℝ := Ms / mP + 1 with hC0
  have hC00 : 0 < C0 := by positivity
  have hC01 : 1 ≤ C0 := by
    have := div_nonneg hMs.le hmP.le
    rw [hC0]
    linarith
  have hgb : ∀ s ω, |Pstar s ω * q s ω - 1| ≤ C0 := fun s ω => by
    have h1 : 0 ≤ Pstar s ω * q s ω := mul_nonneg (hPs0 s ω).le (hqb s ω).1.le
    have h2 : Pstar s ω * q s ω ≤ Ms * (1 / mP) :=
      mul_le_mul (hPs s ω).2 (hqb s ω).2 (hqb s ω).1.le hMs.le
    rw [abs_le]
    constructor
    · linarith
    · have : Ms * (1 / mP) = Ms / mP := by ring
      rw [hC0]
      linarith
  set g : ℕ → Ω → ℝ := fun s ω => β ^ s * Ninv s ω * (Pstar s ω * q s ω - 1) with hg_def
  set Xi : ℕ → Ω → ℝ := fun s ω => β ^ s * Ninv s ω * xi s ω with hXi_def
  have hNm' : ∀ s, StronglyMeasurable[S.𝓕 s] (fun ω => β ^ s * Ninv s ω) := fun s =>
    (hNmeas s s (Nat.le_succ s)).const_mul _
  have hNbd' : ∀ s, ∀ᵐ ω ∂S.μ, ‖β ^ s * Ninv s ω‖ ≤ β ^ s * (Ms / m) ^ s := fun s => by
    filter_upwards [hNb s] with ω h
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (pow_pos hβ0 s) h.1)]
    exact mul_le_mul_of_nonneg_left h.2 (pow_pos hβ0 s).le
  have hXii : ∀ s, Integrable (Xi s) S.μ := fun s =>
    (hxii s).bdd_mul ((hNm' s).mono (S.𝓕.le s)).aestronglyMeasurable (hNbd' s)
  have hgm : ∀ s, StronglyMeasurable[S.𝓕 s] (g s) := fun s =>
    (hNm' s).mul (((hPsm s).mul (hqm s)).sub stronglyMeasurable_const)
  have hgi : ∀ s, Integrable (g s) S.μ := fun s =>
    Integrable.of_bound ((hgm s).mono (S.𝓕.le s)).aestronglyMeasurable
      (β ^ s * (Ms / m) ^ s * C0) (by
        filter_upwards [hNbd' s] with ω h
        rw [Real.norm_eq_abs] at h ⊢
        simp only [hg_def]
        rw [abs_mul]
        exact mul_le_mul h (hgb s ω) (abs_nonneg _) ((abs_nonneg _).trans h))
  have hXim : ∀ s, StronglyMeasurable[S.𝓕 s] (Xi s) := fun s =>
    (hNm' s).mul ((hqm s).mul (hDm s))
  -- one step: `E_s Ξ_{s+1} = Ξ_s + g_s`
  have hstep : ∀ s, S.E s (Xi (s + 1)) =ᵐ[S.μ] Xi s + g s := fun s => by
    have h := S.E_pullOut (hNmeas (s + 1) s le_rfl |>.const_mul (β ^ (s + 1)))
      (C := β ^ (s + 1) * (Ms / m) ^ (s + 1))
      ((hNbd' (s + 1)).mono fun ω h => by rwa [Real.norm_eq_abs] at h) (hxii (s + 1))
    filter_upwards [h, hExi s, hNγ s] with ω e1 e2 e3
    have e1' : S.E s (Xi (s + 1)) ω = β ^ (s + 1) * Ninv (s + 1) ω * S.E s (xi (s + 1)) ω :=
      e1
    rw [e1', Pi.add_apply]
    simp only [hXi_def, hg_def]
    rw [pow_succ]
    linear_combination (β ^ s * Ninv (s + 1) ω) * e2 +
      (β ^ s * (xi s ω - 1 + Pstar s ω * q s ω)) * e3
  -- iterating: `E_t Ξ_{t+k} = Ξ_t + ∑_{j<k} E_t g_{t+j}`
  have hiter : ∀ k, ∀ᵐ ω ∂S.μ, S.E t (Xi (t + k)) ω =
      Xi t ω + ∑ j ∈ Finset.range k, S.E t (g (t + j)) ω := by
    intro k
    induction k with
    | zero =>
      refine Eventually.of_forall fun ω => ?_
      simp [S.E_of_stronglyMeasurable (hXim t) (hXii t)]
    | succ k ih =>
      have h1 := S.E_tower (Nat.le_add_right t k) (Xi (t + k + 1))
      have h2 := S.E_congr (hstep (t + k)) t
      have h3 := S.E_add (hXii (t + k)) (hgi (t + k)) t
      filter_upwards [ih, h1, h2, h3] with ω e0 e1 e2 e3
      change S.E t (Xi (t + k + 1)) ω = _
      rw [← e1, e2, e3, Pi.add_apply, e0, Finset.sum_range_succ]
      ring
  -- the drift is bounded: `|E_t g_{t+j}| ≤ β^{t+j} C₀ L N_t⁻¹`
  have hNti : Integrable (Ninv t) S.μ :=
    Integrable.of_bound ((hNmeas t t (Nat.le_succ t)).mono (S.𝓕.le t)).aestronglyMeasurable
      ((Ms / m) ^ t) ((hNb t).mono fun ω h => by
        rw [Real.norm_eq_abs, abs_of_pos h.1]; exact h.2)
  have hEg : ∀ j, ∀ᵐ ω ∂S.μ, |S.E t (g (t + j)) ω| ≤ β ^ (t + j) * C0 * L * Ninv t ω := by
    intro j
    set h : Ω → ℝ := fun ω => β ^ (t + j) * C0 * L * Ninv t ω with hh
    have hhm : StronglyMeasurable[S.𝓕 t] h := (hNmeas t t (Nat.le_succ t)).const_mul _
    have hhi : Integrable h S.μ := hNti.const_mul _
    have hgh : ∀ᵐ ω ∂S.μ, |g (t + j) ω| ≤ h ω := by
      filter_upwards [hNL j, hNb (t + j)] with ω e1 e2
      simp only [hg_def, hh]
      rw [abs_mul, abs_mul, abs_of_pos (pow_pos hβ0 _), abs_of_pos e2.1]
      have := hgb (t + j) ω
      have hb := pow_pos hβ0 (t + j)
      calc β ^ (t + j) * Ninv (t + j) ω * |Pstar (t + j) ω * q (t + j) ω - 1|
          ≤ β ^ (t + j) * (L * Ninv t ω) * C0 :=
            mul_le_mul (mul_le_mul_of_nonneg_left e1 hb.le) this (abs_nonneg _)
              (mul_nonneg hb.le (e2.1.le.trans e1))
        _ = β ^ (t + j) * C0 * L * Ninv t ω := by ring
    have hup := S.E_mono (hgi (t + j)) hhi (hgh.mono fun ω h => (le_abs_self _).trans h) t
    have hlo := S.E_mono (hgi (t + j)).neg hhi (hgh.mono fun ω h => (neg_le_abs _).trans h) t
    have hneg : S.E t (-g (t + j)) =ᵐ[S.μ] -S.E t (g (t + j)) := condExp_neg _ _
    rw [S.E_of_stronglyMeasurable hhm hhi] at hup hlo
    filter_upwards [hup, hlo, hneg] with ω e1 e2 e3
    rw [e3, Pi.neg_apply] at e2
    rw [abs_le]
    constructor <;> linarith
  -- transversality: `E_t Ξ_{t+k} → 0`
  have hlow := value_lower S hβ0 hβ1 (Ms := Ms) (fun t ω => hP t ω) hPa hPi hPsa hPs0
    (fun t ω => (hPs t ω).2) hD hDpre hDi htvc
  set Cl : ℝ := Ms / (1 - β) with hCl
  have hlim : ∀ᵐ ω ∂S.μ, Tendsto (fun k => S.E t (Xi (t + k)) ω) atTop (𝓝 0) := by
    have hk : ∀ k, ∀ᵐ ω ∂S.μ, |S.E t (Xi (t + k)) ω| ≤
        β ^ t * L / mP * Ninv t ω * (β ^ k * S.E t (D (t + k)) ω + 2 * Cl * β ^ k) := by
      intro k
      set f : Ω → ℝ := fun ω => β ^ t * L / mP * Ninv t ω * β ^ k with hf
      set H : Ω → ℝ := f * fun ω => D (t + k) ω + 2 * Cl with hH
      have hfm : StronglyMeasurable[S.𝓕 t] f :=
        ((hNmeas t t (Nat.le_succ t)).const_mul _).mul_const _
      have hfb : ∀ᵐ ω ∂S.μ, |f ω| ≤ |β ^ t * L / mP| * (Ms / m) ^ t * β ^ k := by
        filter_upwards [hNb t] with ω h
        simp only [hf]
        rw [abs_mul, abs_mul, abs_of_pos h.1, abs_of_pos (pow_pos hβ0 k)]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h.2 (abs_nonneg _))
          (pow_pos hβ0 k).le
      have hyi : Integrable (fun ω => D (t + k) ω + 2 * Cl) S.μ :=
        (hDi (t + k)).add (integrable_const _)
      have hHi : Integrable H S.μ :=
        hyi.bdd_mul (hfm.mono (S.𝓕.le t)).aestronglyMeasurable
          (hfb.mono fun ω h => by rwa [Real.norm_eq_abs])
      have hXH : ∀ᵐ ω ∂S.μ, |Xi (t + k) ω| ≤ H ω := by
        filter_upwards [hNL k, hNb (t + k), hlow (t + k), hNb t] with ω e1 e2 e3 e4
        simp only [hXi_def, hxi_def, hH, hf, Pi.mul_apply]
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (pow_pos hβ0 _), abs_of_pos e2.1,
          abs_of_pos (hqb _ ω).1, pow_add]
        have hD2 : |D (t + k) ω| ≤ D (t + k) ω + 2 * Cl := by
          rw [abs_le]
          have : 0 ≤ Cl := div_nonneg hMs.le h1β.le
          constructor <;> linarith
        have hq1 := (hqb (t + k) ω).2
        have hL0 : 0 ≤ L * Ninv t ω := e2.1.le.trans e1
        have hb := mul_pos (pow_pos hβ0 t) (pow_pos hβ0 k)
        calc β ^ t * β ^ k * Ninv (t + k) ω * (q (t + k) ω * |D (t + k) ω|)
            ≤ β ^ t * β ^ k * (L * Ninv t ω) * (1 / mP * (D (t + k) ω + 2 * Cl)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left e1 hb.le)
                (mul_le_mul hq1 hD2 (abs_nonneg _) (by positivity))
                (mul_nonneg (hqb _ ω).1.le (abs_nonneg _)) (mul_nonneg hb.le hL0)
          _ = β ^ t * L / mP * Ninv t ω * β ^ k * (D (t + k) ω + 2 * Cl) := by
              field_simp
      have hup := S.E_mono (hXii (t + k)) hHi (hXH.mono fun ω h => (le_abs_self _).trans h) t
      have hlo := S.E_mono (hXii (t + k)).neg hHi (hXH.mono fun ω h => (neg_le_abs _).trans h) t
      have hneg : S.E t (-Xi (t + k)) =ᵐ[S.μ] -S.E t (Xi (t + k)) := condExp_neg _ _
      have hpo := S.E_pullOut hfm hfb hyi
      have hadd := S.E_add (hDi (t + k)) (integrable_const (2 * Cl)) t
      filter_upwards [hup, hlo, hneg, hpo, hadd] with ω e1 e2 e3 e4 e5
      have eH : S.E t H ω =
          β ^ t * L / mP * Ninv t ω * (β ^ k * S.E t (D (t + k)) ω + 2 * Cl * β ^ k) := by
        change S.E t (f * fun ω => D (t + k) ω + 2 * Cl) ω = _
        rw [e4, Pi.mul_apply]
        have e5' : S.E t (fun ω => D (t + k) ω + 2 * Cl) ω = S.E t (D (t + k)) ω + 2 * Cl := by
          change S.E t (D (t + k) + fun _ => 2 * Cl) ω = _
          rw [e5, Pi.add_apply, S.E_const]
        rw [e5']
        simp only [hf]
        ring
      rw [e3, Pi.neg_apply] at e2
      rw [eH] at e1 e2
      rw [abs_le]
      constructor <;> linarith
    filter_upwards [ae_all_iff.2 hk, htvc t] with ω e1 e2
    have hg := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1
    have h3 : Tendsto (fun k => β ^ t * L / mP * Ninv t ω *
        (β ^ k * S.E t (D (t + k)) ω + 2 * Cl * β ^ k)) atTop (𝓝 0) := by
      have := (e2.add (hg.const_mul (2 * Cl))).const_mul (β ^ t * L / mP * Ninv t ω)
      simpa using this
    exact squeeze_zero_norm (fun k => by rw [Real.norm_eq_abs]; exact e1 k) h3
  -- conclusion
  filter_upwards [ae_all_iff.2 hiter, ae_all_iff.2 hEg, hlim, hNb t] with ω e1 e2 e3 e4
  have hc0 : 0 ≤ β ^ t * C0 * L * Ninv t ω := by
    have := (abs_nonneg _).trans (e2 0)
    simpa using this
  have hsumb : ∀ k, |∑ j ∈ Finset.range k, S.E t (g (t + j)) ω| ≤
      β ^ t * C0 * L * Ninv t ω / (1 - β) := fun k => by
    calc |∑ j ∈ Finset.range k, S.E t (g (t + j)) ω|
        ≤ ∑ j ∈ Finset.range k, |S.E t (g (t + j)) ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range k, β ^ (t + j) * C0 * L * Ninv t ω :=
          Finset.sum_le_sum fun j _ => e2 j
      _ = β ^ t * C0 * L * Ninv t ω * ∑ j ∈ Finset.range k, β ^ j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [pow_add]; ring
      _ ≤ β ^ t * C0 * L * Ninv t ω * ∑' j, β ^ j := mul_le_mul_of_nonneg_left
          ((summable_geometric_of_lt_one hβ0.le hβ1).sum_le_tsum _
            fun j _ => pow_nonneg hβ0.le j) hc0
      _ = β ^ t * C0 * L * Ninv t ω / (1 - β) := by
          rw [tsum_geometric_of_lt_one hβ0.le hβ1, div_eq_mul_inv]
  have hXb : |Xi t ω| ≤ β ^ t * C0 * L * Ninv t ω / (1 - β) := by
    have hb : ∀ k, |Xi t ω| ≤ |S.E t (Xi (t + k)) ω| + β ^ t * C0 * L * Ninv t ω / (1 - β) :=
      fun k => by
        have := e1 k
        have h2 := hsumb k
        calc |Xi t ω| = |S.E t (Xi (t + k)) ω - ∑ j ∈ Finset.range k, S.E t (g (t + j)) ω| := by
              rw [this]; ring_nf
          _ ≤ _ := (abs_sub _ _).trans (add_le_add le_rfl h2)
    have hl := (e3.abs.add_const (β ^ t * C0 * L * Ninv t ω / (1 - β)))
    rw [abs_zero, zero_add] at hl
    exact ge_of_tendsto' hl hb
  have hpos : 0 < β ^ t * Ninv t ω := mul_pos (pow_pos hβ0 t) e4.1
  have hqD : |q t ω * D t ω| ≤ C0 * L / (1 - β) := by
    have e : Xi t ω = β ^ t * Ninv t ω * (q t ω * D t ω) := rfl
    rw [e, abs_mul, abs_of_pos hpos] at hXb
    rw [← mul_le_mul_iff_of_pos_left hpos]
    calc β ^ t * Ninv t ω * |q t ω * D t ω| ≤ β ^ t * C0 * L * Ninv t ω / (1 - β) := hXb
      _ = β ^ t * Ninv t ω * (C0 * L / (1 - β)) := by ring
  have hDe : |D t ω| = |q t ω * D t ω| * P t ω := by
    rw [abs_mul, abs_of_pos (hqb t ω).1,
      show q t ω * |D t ω| * P t ω = |D t ω| * (q t ω * P t ω) by ring, hqP t ω, mul_one]
  rw [hDe]
  have : C0 * L / (1 - β) = L * (Ms / mP + 1) / (1 - β) := by rw [hC0]; ring
  rw [← this]
  exact mul_le_mul_of_nonneg_right hqD (hP t ω).le

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d), prices bounded away from zero, target
with news**): on any measure-theoretic system, let the underlying surplus `s₀` have a bounded
predetermined present value `B` (`a(β) = 0`) and let the target `0 < m ≤ P* ≤ M*` be adapted with
the bounded cumulative real-rate factor `∏ E(P*/P*′)⁻¹ ≤ L` — its present value may carry news. Then
an equilibrium with prices bounded away from zero (`P ≥ m_P > 0`, possibly unbounded above)
coincides a.e. with any equilibrium with prices bounded above and the same initial debt. -/
theorem fr_compare_below {β θ K mP M' m Ms L : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {s0 B Pstar P P' b b' : ℕ → Ω → ℝ}
    (hs0m : ∀ t, StronglyMeasurable[S.𝓕 t] (s0 t))
    (hB : ∀ t ω, B t ω = s0 t ω + β * B (t + 1) ω)
    (hBpre : ∀ t, StronglyMeasurable[S.𝓕 t] (B (t + 1))) (hBK : ∀ t ω, |B t ω| ≤ K)
    (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hL : ∀ t k, ∀ᵐ ω ∂S.μ, ∏ i ∈ Finset.range k,
      (Pstar (t + i) ω * S.E (t + i) (fun ω => 1 / Pstar (t + i + 1) ω) ω)⁻¹ ≤ L)
    (hE : RuleEqmGen S β θ s0 Pstar P b) (hmP : 0 < mP) (hPmP : ∀ t ω, mP ≤ P t ω)
    (hE' : RuleEqmGen S β θ s0 Pstar P' b') (hP'M : ∀ t ω, P' t ω ≤ M')
    (hq' : ∀ t, Integrable (fun ω => 1 / P' t ω) S.μ)
    (hb0 : b 0 =ᵐ[S.μ] b' 0) (t : ℕ) : P t =ᵐ[S.μ] P' t ∧ b t =ᵐ[S.μ] b' t := by
  obtain ⟨hP, hPa, hPi, hbi, hrate, hflow, hpre, -, htvc⟩ := hE
  obtain ⟨hP', hP'a, -, hbi', hrate', hflow', hpre', -, htvc'⟩ := hE'
  have h1β : 0 < 1 - β := by linarith
  have hPs0 : ∀ t ω, 0 < Pstar t ω := fun t ω => hm.trans_le (hPs t ω).1
  have hBm : ∀ t, StronglyMeasurable[S.𝓕 t] (B t) := fun t => by
    have e : B t = fun ω => s0 t ω + β * B (t + 1) ω := funext (hB t)
    rw [e]
    exact (hs0m t).add ((hBpre t).const_mul β)
  have hBi : ∀ t, Integrable (B t) S.μ := fun t =>
    Integrable.of_bound ((hBm t).mono (S.𝓕.le t)).aestronglyMeasurable K
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hBK t ω)
  -- `D = (b − B)/θ` for `P` and `D' = (b' − B)/θ` for `P'`
  set D : ℕ → Ω → ℝ := fun t ω => θ⁻¹ * (b t ω - B t ω) with hD_def
  set D' : ℕ → Ω → ℝ := fun t ω => θ⁻¹ * (b' t ω - B t ω) with hD'_def
  have hD : ∀ t ω, D t ω = P t ω - Pstar t ω + β * D (t + 1) ω := fun t ω => by
    simp only [hD_def]
    rw [hflow t ω, hB t ω]
    field_simp
    ring
  have hD' : ∀ t ω, D' t ω = P' t ω - Pstar t ω + β * D' (t + 1) ω := fun t ω => by
    simp only [hD'_def]
    rw [hflow' t ω, hB t ω]
    field_simp
    ring
  have hDpre : ∀ t, StronglyMeasurable[S.𝓕 t] (D (t + 1)) := fun t =>
    ((hpre t).sub (hBpre t)).const_mul θ⁻¹
  have hDi : ∀ t, Integrable (D t) S.μ := fun t => ((hbi t).sub (hBi t)).const_mul θ⁻¹
  have hDtvc : ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun k => β ^ k * S.E t (D (t + k)) ω) atTop (𝓝 0) := by
    intro t
    filter_upwards [tvc_sub_bdd S hβ0 hβ1 hbi hBi hBK htvc t,
      ae_all_iff.2 fun k => S.E_smul θ⁻¹ (fun ω => b (t + k) ω - B (t + k) ω) t] with ω h1 h2
    have := h1.const_mul θ⁻¹
    rw [mul_zero] at this
    refine this.congr fun k => ?_
    have e : D (t + k) = θ⁻¹ • fun ω => b (t + k) ω - B (t + k) ω := by
      funext ω
      simp [hD_def]
    rw [e, h2 k, Pi.smul_apply, smul_eq_mul]
    ring
  -- the key bounds
  have hratio := ratio_bdd S hβ0 hβ1 hPa hmP hPmP hPi hPsa hm hPs hrate hD hDpre hDi hDtvc hL
  have hlow := value_lower S hβ0 hβ1 (Ms := Ms) hP hPa hPi hPsa hPs0 (fun t ω => (hPs t ω).2) hD
    hDpre hDi hDtvc
  have hsm : ∀ t, StronglyMeasurable[S.𝓕 t] (fun ω => θ * (P' t ω - Pstar t ω)) := fun t =>
    ((hP'a t).sub (hPsa t)).const_mul θ
  have hsC : ∀ t ω, |θ * (P' t ω - Pstar t ω)| ≤ |θ| * (|M'| + Ms) := fun t ω => by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg θ)
    rw [abs_le]
    have := hP' t ω
    have := hP'M t ω
    have := le_abs_self M'
    have := hPs0 t ω
    have := (hPs t ω).2
    constructor <;> linarith
  have hdB := debt_bdd S hβ0 hβ1 (s := fun t ω => θ * (P' t ω - Pstar t ω))
    (b := fun t ω => b' t ω - B t ω) hsm hsC
    (fun t ω => by rw [hflow' t ω, hB t ω]; ring) (fun t => (hpre' t).sub (hBpre t))
    (fun t => (hbi' t).sub (hBi t)) (tvc_sub_bdd S hβ0 hβ1 hbi' hBi hBK htvc')
  set C2 : ℝ := |θ|⁻¹ * (|θ| * (|M'| + Ms) / (1 - β)) with hC2
  have hD'B : ∀ t, ∀ᵐ ω ∂S.μ, |D' t ω| ≤ C2 := fun t => by
    filter_upwards [hdB t] with ω h
    simp only [hD'_def, hC2]
    rw [abs_mul, abs_inv]
    exact mul_le_mul_of_nonneg_left h (inv_nonneg.2 (abs_nonneg θ))
  -- the pulled-out interest-rate relation
  have hq : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ := fun t =>
    Integrable.of_bound (((hPa t).measurable.const_div 1).stronglyMeasurable.mono
      (S.𝓕.le t)).aestronglyMeasurable (1 / mP)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (hP t ω))]
        exact one_div_le_one_div_of_le hmP (hPmP t ω))
  have hr : ∀ t, ∀ᵐ ω ∂S.μ, P t ω * S.E t (fun ω => 1 / P (t + 1) ω) ω =
      P' t ω * S.E t (fun ω => 1 / P' (t + 1) ω) ω := fun t => by
    have e : P t / P (t + 1) = P t * fun ω => 1 / P (t + 1) ω := by
      funext ω
      simp [div_eq_mul_inv]
    have e' : P' t / P' (t + 1) = P' t * fun ω => 1 / P' (t + 1) ω := by
      funext ω
      simp [div_eq_mul_inv]
    have hint : Integrable (P t * fun ω => 1 / P (t + 1) ω) S.μ := by
      have hm1 : AEStronglyMeasurable (fun ω => 1 / P (t + 1) ω) S.μ := (hq (t + 1)).1
      have hb1 : ∀ᵐ ω ∂S.μ, ‖1 / P (t + 1) ω‖ ≤ 1 / mP := Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (hP (t + 1) ω))]
        exact one_div_le_one_div_of_le hmP (hPmP (t + 1) ω)
      have := (hPi t).bdd_mul hm1 hb1
      exact this.congr (Eventually.of_forall fun ω => mul_comm _ _)
    have h1 : S.E t (P t * fun ω => 1 / P (t + 1) ω) =ᵐ[S.μ]
        P t * S.E t (fun ω => 1 / P (t + 1) ω) :=
      condExp_mul_of_stronglyMeasurable_left (hPa t) hint (hq (t + 1))
    have h2 := S.E_pullOut (hP'a t) (C := M') (Eventually.of_forall fun ω => by
      rw [abs_of_pos (hP' t ω)]; exact hP'M t ω) (hq' (t + 1))
    have h3 := hrate t
    have h4 := hrate' t
    rw [e] at h3
    rw [e'] at h4
    filter_upwards [h1, h2, h3, h4] with ω f1 f2 f3 f4
    rw [Pi.mul_apply] at f1 f2
    rw [← f1, ← f2, f3, f4]
  -- the scaled debt difference
  set Δ : ℕ → Ω → ℝ := fun t ω => θ⁻¹ * (b t ω - b' t ω) with hΔ_def
  have hΔe : ∀ t ω, Δ t ω = D t ω - D' t ω := fun t ω => by
    simp only [hΔ_def, hD_def, hD'_def]
    ring
  have hΔ : ∀ t ω, Δ t ω = P t ω - P' t ω + β * Δ (t + 1) ω := fun t ω => by
    rw [hΔe, hΔe, hD t ω, hD' t ω]
    ring
  have hΔm : ∀ t, StronglyMeasurable[S.𝓕 t] (Δ (t + 1)) := fun t =>
    ((hpre t).sub (hpre' t)).const_mul θ⁻¹
  set Bc : ℝ := L * (Ms / mP + 1) / (1 - β) with hBc
  have hz : ∀ t, ∀ᵐ ω ∂S.μ, Δ t ω = 0 := by
    intro t
    induction t with
    | zero =>
      filter_upwards [hb0] with ω h
      simp only [hΔ_def, h, sub_self, mul_zero]
    | succ t ih =>
      have h1 := compare_step_ratio S hβ0 hβ1 (B := |Bc| * |M'| + C2) hP hP' hP'M hPa hP'a hq
        hq' hr hΔ hΔm (fun s => by
          filter_upwards [hratio s, hD'B s] with ω e1 e2 hlt
          rw [hΔe]
          have h3 : Bc * P s ω ≤ |Bc| * |M'| := by
            calc Bc * P s ω ≤ |Bc| * P s ω :=
                  mul_le_mul_of_nonneg_right (le_abs_self _) (hP s ω).le
              _ ≤ |Bc| * |M'| := mul_le_mul_of_nonneg_left
                  ((hlt.le.trans (hP'M s ω)).trans (le_abs_self _)) (abs_nonneg _)
          have := le_abs_self (D s ω)
          have := neg_abs_le (D' s ω)
          linarith) ih
      have h2 := compare_step_le S hβ0 hβ1 (Δ := fun t ω => -Δ t ω) (B := C2 + Ms / (1 - β))
        hP' hP hP'a hPa hq' hq (fun t => (hr t).mono fun ω h => h.symm)
        (fun t ω => by rw [hΔ t ω]; ring) (fun t => (hΔm t).neg)
        (fun s => by
          filter_upwards [hlow s, hD'B s] with ω e1 e2
          rw [hΔe]
          have := le_abs_self (D' s ω)
          linarith)
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

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d), `b₀` = present value of `s₀`, prices
bounded away from zero, target with news**): under the bounded real-rate factor hypothesis, every
equilibrium with prices bounded away from zero has `P = P*` and `b = B` a.e. — no predetermined
present value of the target is needed. -/
theorem fr_unique_below_news {β θ C K mP m Ms L : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {s0 B Pstar P b : ℕ → Ω → ℝ}
    (hs0m : ∀ t, StronglyMeasurable[S.𝓕 t] (s0 t)) (hs0C : ∀ t ω, |s0 t ω| ≤ C)
    (hB : ∀ t ω, B t ω = s0 t ω + β * B (t + 1) ω)
    (hBpre : ∀ t, StronglyMeasurable[S.𝓕 t] (B (t + 1))) (hBK : ∀ t ω, |B t ω| ≤ K)
    (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hL : ∀ t k, ∀ᵐ ω ∂S.μ, ∏ i ∈ Finset.range k,
      (Pstar (t + i) ω * S.E (t + i) (fun ω => 1 / Pstar (t + i + 1) ω) ω)⁻¹ ≤ L)
    (hE : RuleEqmGen S β θ s0 Pstar P b) (hmP : 0 < mP) (hPmP : ∀ t ω, mP ≤ P t ω)
    (hb0 : b 0 =ᵐ[S.μ] B 0) (t : ℕ) : P t =ᵐ[S.μ] Pstar t ∧ b t =ᵐ[S.μ] B t := by
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
  exact fr_compare_below S hβ0 hβ1 hθ hs0m hB hBpre hBK hPsa hm hPs hL hE hmP hPmP
    (target_ruleEqmGen S hβ0 hβ1 (θ := θ) hs0m hs0C hB hBpre hBK hPs0 hPsa hPsi)
    (fun t ω => (hPs t ω).2) hqs hb0 t

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d) with `b₀ = b̄`, prices bounded away
from zero, news-bearing target**): under the bounded real-rate factor hypothesis, every equilibrium
of the rule (`RuleEqm`) with prices bounded away from zero and `b₀ = b̄` is `P = P*`. This extends
`fr_unique_stochastic_below` beyond a predetermined target value; `fr_below_counterexample` shows
the real-rate hypothesis itself cannot be dropped. -/
theorem fr_d_news_below {β θ bbar mP m Ms L : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {Pstar P b : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (hL : ∀ t k, ∀ᵐ ω ∂S.μ, ∏ i ∈ Finset.range k,
      (Pstar (t + i) ω * S.E (t + i) (fun ω => 1 / Pstar (t + i + 1) ω) ω)⁻¹ ≤ L)
    (hE : RuleEqm S β θ bbar Pstar P b) (hmP : 0 < mP) (hPmP : ∀ t ω, mP ≤ P t ω)
    (hb0 : ∀ ω, b 0 ω = bbar) (t : ℕ) : P t =ᵐ[S.μ] Pstar t :=
  (fr_unique_below_news S hβ0 hβ1 hθ (C := |(1 - β) * bbar|) (K := |bbar|)
    (B := fun _ _ => bbar) (fun _ => stronglyMeasurable_const) (fun _ _ => le_rfl)
    (fun _ _ => by ring) (fun _ => stronglyMeasurable_const) (fun _ _ => le_rfl) hPsa hm hPs hL
    ((ruleEqm_iff_gen S).1 hE) hmP hPmP (Eventually.of_forall hb0) t).1

/-! ### Random date-0 data without an assumed band -/

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d) for a general `s₀`, random date-0 data,
no band assumed**, prices bounded above): with a predetermined target value `a` and a bounded
predetermined present value `B` of `s₀`, every equilibrium with bounded-above prices has
`P_t = c P*_t` a.e., `c = 1 + (b₀ − B₀)/(θ a₀)` — the band `c ∈ [c_min, c_max]` of
`fr_unique_s0_random` is not needed. Proof: `c = V₀/a₀ > 0` a.e. (the value of the price path is
positive); on each date-0 event `G_n = {1/(n+1) ≤ c ≤ n+1}` glue the equilibrium with the
proportional path `c_n P*` outside `G_n` and apply `fr_unique_stochastic` to the scaled target
`c_n P*`, `c_n = c` clamped to `[1/(n+1), n+1]`. -/
theorem fr_unique_s0_random_full {β θ K m Ms M Ka : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 0) {s0 B Pstar P b a : ℕ → Ω → ℝ}
    (hs0m : ∀ t, StronglyMeasurable[S.𝓕 t] (s0 t))
    (hB : ∀ t ω, B t ω = s0 t ω + β * B (t + 1) ω)
    (hBpre : ∀ t, StronglyMeasurable[S.𝓕 t] (B (t + 1))) (hBK : ∀ t ω, |B t ω| ≤ K)
    (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (ha : ∀ t ω, a t ω = Pstar t ω + β * a (t + 1) ω)
    (hapre : ∀ t, StronglyMeasurable[S.𝓕 t] (a (t + 1))) (haK : ∀ t ω, |a t ω| ≤ Ka)
    (hE : RuleEqmGen S β θ s0 Pstar P b) (hPM : ∀ t ω, P t ω ≤ M)
    (hq : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ) (t : ℕ) :
    P t =ᵐ[S.μ] fun ω => (1 + (b 0 ω - B 0 ω) / (θ * a 0 ω)) * Pstar t ω := by
  obtain ⟨hP, hPa, hPi, hbi, hrate, hflow, hpre, -, htvc⟩ := hE
  have h1β : 0 < 1 - β := by linarith
  have hPs0 : ∀ t ω, 0 < Pstar t ω := fun t ω => hm.trans_le (hPs t ω).1
  have hBm : ∀ t, StronglyMeasurable[S.𝓕 t] (B t) := fun t => by
    have e : B t = fun ω => s0 t ω + β * B (t + 1) ω := funext (hB t)
    rw [e]
    exact (hs0m t).add ((hBpre t).const_mul β)
  have hBi : ∀ t, Integrable (B t) S.μ := fun t =>
    Integrable.of_bound ((hBm t).mono (S.𝓕.le t)).aestronglyMeasurable K
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hBK t ω)
  have ham : ∀ t, StronglyMeasurable[S.𝓕 t] (a t) := targetValue_adapted S hPsa ha hapre
  have hai : ∀ t, Integrable (a t) S.μ := fun t =>
    Integrable.of_bound ((ham t).mono (S.𝓕.le t)).aestronglyMeasurable Ka
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact haK t ω)
  have hapos : ∀ t ω, 0 < a t ω := fun t ω =>
    (div_pos hm (by linarith)).trans_le (targetValue_ge hβ0 hβ1 (fun t ω => (hPs t ω).1) ha haK t ω)
  have hbm : ∀ t, StronglyMeasurable[S.𝓕 t] (b t) := fun t => by
    have e : b t = fun ω => s0 t ω + θ * (P t ω - Pstar t ω) + β * b (t + 1) ω := funext (hflow t)
    rw [e]
    exact ((hs0m t).add (((hPa t).sub (hPsa t)).const_mul θ)).add ((hpre t).const_mul β)
  set c : Ω → ℝ := fun ω => 1 + (b 0 ω - B 0 ω) / (θ * a 0 ω) with hc_def
  have hcm : ∀ t, StronglyMeasurable[S.𝓕 t] c := fun t =>
    ((measurable_const.add (((hbm 0).measurable.sub (hBm 0).measurable).div
      ((ham 0).measurable.const_mul θ))).stronglyMeasurable).mono (S.𝓕.mono (Nat.zero_le t))
  -- `c > 0` a.e.: `c = V₀/a₀` with `V` the (positive) value of the price path
  have hcpos : ∀ᵐ ω ∂S.μ, 0 < c ω := by
    set V : ℕ → Ω → ℝ := fun t ω => θ⁻¹ * (b t ω - B t ω) + a t ω with hV_def
    have hVrec : ∀ t ω, V t ω = P t ω + β * V (t + 1) ω := fun t ω => by
      simp only [hV_def]
      rw [hflow t ω, hB t ω, ha t ω]
      field_simp
      ring
    have hVm : ∀ t, StronglyMeasurable[S.𝓕 t] (V t) := fun t =>
      (((hbm t).sub (hBm t)).const_mul θ⁻¹).add (ham t)
    have hVi : ∀ t, Integrable (V t) S.μ := fun t =>
      (((hbi t).sub (hBi t)).const_mul θ⁻¹).add (hai t)
    have hVtvc : ∀ t, ∀ᵐ ω ∂S.μ,
        Tendsto (fun k => β ^ k * S.E t (V (t + k)) ω) atTop (𝓝 0) := by
      intro t
      have hg := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1
      have hlin : ∀ k, ∀ᵐ ω ∂S.μ, S.E t (V (t + k)) ω =
          θ⁻¹ * S.E t (fun ω => b (t + k) ω - B (t + k) ω) ω + S.E t (a (t + k)) ω := fun k => by
        have e : V (t + k) = θ⁻¹ • (b (t + k) - B (t + k)) + a (t + k) := by
          funext ω
          simp [hV_def]
        filter_upwards [S.E_add (((hbi (t + k)).sub (hBi (t + k))).smul θ⁻¹) (hai (t + k)) t,
          S.E_smul θ⁻¹ (b (t + k) - B (t + k)) t] with ω e1 e2
        rw [e, e1, Pi.add_apply, e2, Pi.smul_apply, smul_eq_mul]
        rfl
      filter_upwards [tvc_sub_bdd S hβ0 hβ1 hbi hBi hBK htvc t, ae_all_iff.2 hlin,
        ae_all_iff.2 fun k => S.abs_E_le (Eventually.of_forall fun ω => haK (t + k) ω) t]
        with ω h1 h2 h4
      have hA : Tendsto (fun k => β ^ k * S.E t (a (t + k)) ω) atTop (𝓝 0) := by
        refine squeeze_zero_norm (fun k => ?_) (by simpa using hg.mul_const Ka)
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 k)]
        exact mul_le_mul_of_nonneg_left (h4 k) (pow_pos hβ0 k).le
      have := (h1.const_mul θ⁻¹).add hA
      rw [mul_zero, zero_add] at this
      refine this.congr fun k => ?_
      rw [h2 k]
      ring
    have hVnn := value_nonneg S hβ0 hP hVrec hVm hVi hPi hVtvc
    filter_upwards [hVnn 1] with ω h
    have e : c ω = V 0 ω / a 0 ω := by
      simp only [hc_def, hV_def]
      have := (hapos 0 ω).ne'
      field_simp
      ring
    rw [e]
    have := hVrec 0 ω
    have := hP 0 ω
    exact div_pos (by nlinarith) (hapos 0 ω)
  -- localisation on `G_n = {1/(n+1) ≤ c ≤ n+1}`
  have hloc : ∀ n : ℕ, ∀ᵐ ω ∂S.μ, (1 / ((n : ℝ) + 1) ≤ c ω ∧ c ω ≤ (n : ℝ) + 1) →
      P t ω = c ω * Pstar t ω := by
    intro n
    have hn0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hn1 : 1 / ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    set G : Set Ω := {ω | 1 / ((n : ℝ) + 1) ≤ c ω ∧ c ω ≤ (n : ℝ) + 1} with hG
    have hGm : ∀ t, MeasurableSet[S.𝓕 t] G := fun t =>
      (measurableSet_le measurable_const (hcm t).measurable).inter
        (measurableSet_le (hcm t).measurable measurable_const)
    set cn : Ω → ℝ := fun ω => min (max (c ω) (1 / ((n : ℝ) + 1))) ((n : ℝ) + 1) with hcn
    have hcnm : ∀ t, StronglyMeasurable[S.𝓕 t] cn := fun t =>
      (((hcm t).measurable.max measurable_const).min measurable_const).stronglyMeasurable
    have hcnb : ∀ ω, 1 / ((n : ℝ) + 1) ≤ cn ω ∧ cn ω ≤ (n : ℝ) + 1 := fun ω =>
      ⟨le_min (le_max_right _ _) hn1, min_le_right _ _⟩
    have hcnG : ∀ ω ∈ G, cn ω = c ω := fun ω hω => by
      simp only [hcn]
      rw [max_eq_left hω.1, min_eq_left hω.2]
    have hcn0 : ∀ ω, 0 < cn ω := fun ω => hn0.trans_le (hcnb ω).1
    -- the glued price path, the scaled target and the adjusted debt
    set Pt : ℕ → Ω → ℝ := fun t ω => G.indicator (P t) ω +
      Gᶜ.indicator (fun ω => cn ω * Pstar t ω) ω with hPt
    set P2 : ℕ → Ω → ℝ := fun t ω => cn ω * Pstar t ω with hP2
    set a2 : ℕ → Ω → ℝ := fun t ω => cn ω * a t ω with ha2
    set b2 : ℕ → Ω → ℝ := fun t ω => G.indicator (b t) ω -
      G.indicator (fun ω => B t ω + θ * (cn ω - 1) * a t ω) ω with hb2
    have hPtG : ∀ t ω, ω ∈ G → Pt t ω = P t ω := fun t ω hω => by
      simp [hPt, hω]
    have hPtGc : ∀ t ω, ω ∉ G → Pt t ω = cn ω * Pstar t ω := fun t ω hω => by
      simp [hPt, hω]
    have hPtpos : ∀ t ω, 0 < Pt t ω := fun t ω => by
      by_cases hω : ω ∈ G
      · rw [hPtG t ω hω]; exact hP t ω
      · rw [hPtGc t ω hω]; exact mul_pos (hcn0 ω) (hPs0 t ω)
    have hPta : StronglyAdapted S.𝓕 Pt := fun t =>
      ((hPa t).indicator (hGm t)).add (((hcnm t).mul (hPsa t)).indicator (hGm t).compl)
    have hPtM : ∀ t ω, Pt t ω ≤ max M (((n : ℝ) + 1) * Ms) := fun t ω => by
      by_cases hω : ω ∈ G
      · rw [hPtG t ω hω]; exact (hPM t ω).trans (le_max_left _ _)
      · rw [hPtGc t ω hω]
        exact (mul_le_mul (hcnb ω).2 (hPs t ω).2 (hPs0 t ω).le (by positivity)).trans
          (le_max_right _ _)
    have hqt : ∀ t, Integrable (fun ω => 1 / Pt t ω) S.μ := fun t => by
      refine Integrable.mono' ((hq t).abs.add (integrable_const (((n : ℝ) + 1) / m)))
        ((((hPta t).measurable.const_div 1).stronglyMeasurable.mono
          (S.𝓕.le t)).aestronglyMeasurable) (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (hPtpos t ω))]
      by_cases hω : ω ∈ G
      · rw [hPtG t ω hω]
        have := abs_nonneg (1 / P t ω)
        have : 0 ≤ ((n : ℝ) + 1) / m := by positivity
        have := le_abs_self (1 / P t ω)
        simp only [Pi.add_apply]
        linarith
      · rw [hPtGc t ω hω]
        have h1 : 1 / (cn ω * Pstar t ω) ≤ ((n : ℝ) + 1) / m := by
          rw [div_le_div_iff₀ (mul_pos (hcn0 ω) (hPs0 t ω)) hm]
          have h2 := mul_le_mul (hcnb ω).1 (hPs t ω).1 hm.le (hcn0 ω).le
          have h3 : 1 / ((n : ℝ) + 1) * m * ((n : ℝ) + 1) = m := by field_simp
          nlinarith
        simp only [Pi.add_apply]
        linarith [abs_nonneg (1 / P t ω)]
    have hP2a : StronglyAdapted S.𝓕 P2 := fun t => (hcnm t).mul (hPsa t)
    have hm2 : 0 < m / ((n : ℝ) + 1) := by positivity
    have hP2s : ∀ t ω, m / ((n : ℝ) + 1) ≤ P2 t ω ∧ P2 t ω ≤ ((n : ℝ) + 1) * Ms := fun t ω => by
      refine ⟨?_, mul_le_mul (hcnb ω).2 (hPs t ω).2 (hPs0 t ω).le (by positivity)⟩
      calc m / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) * m := by ring
        _ ≤ cn ω * Pstar t ω := mul_le_mul (hcnb ω).1 (hPs t ω).1 hm.le (hcn0 ω).le
    have ha2r : ∀ t ω, a2 t ω = P2 t ω + β * a2 (t + 1) ω := fun t ω => by
      simp only [ha2, hP2]
      rw [ha t ω]
      ring
    have ha2pre : ∀ t, StronglyMeasurable[S.𝓕 t] (a2 (t + 1)) := fun t => (hcnm t).mul (hapre t)
    have ha2K : ∀ t ω, |a2 t ω| ≤ ((n : ℝ) + 1) * Ka := fun t ω => by
      simp only [ha2]
      rw [abs_mul, abs_of_pos (hcn0 ω)]
      exact mul_le_mul (hcnb ω).2 (haK t ω) (abs_nonneg _) (by positivity)
    have hrate2 : ∀ t, S.E t (Pt t / Pt (t + 1)) =ᵐ[S.μ] S.E t (P2 t / P2 (t + 1)) := fun t => by
      have e2 : P2 t / P2 (t + 1) = Pstar t / Pstar (t + 1) := funext fun ω => by
        simp only [Pi.div_apply, hP2]
        rw [mul_div_mul_left _ _ (hcn0 ω).ne']
      have e1 : Pt t / Pt (t + 1) =
          G.indicator (P t / P (t + 1)) + Gᶜ.indicator (Pstar t / Pstar (t + 1)) := by
        funext ω
        by_cases hω : ω ∈ G
        · simp [Pi.div_apply, hPtG _ ω hω, hω]
        · simp only [Pi.div_apply, Pi.add_apply, hPtGc _ ω hω]
          rw [Set.indicator_of_notMem hω, Set.indicator_of_mem (Set.mem_compl hω), zero_add,
            mul_div_mul_left _ _ (hcn0 ω).ne']
          rfl
      have hi1 : Integrable (P t / P (t + 1)) S.μ := by
        have h := (hq (t + 1)).bdd_mul (c := M) ((hPa t).mono (S.𝓕.le t)).aestronglyMeasurable
          (Eventually.of_forall fun ω => by
            rw [Real.norm_eq_abs, abs_of_pos (hP t ω)]; exact hPM t ω)
        exact h.congr (Eventually.of_forall fun ω => by
          simp [Pi.div_apply, div_eq_mul_inv])
      have hi2 : Integrable (Pstar t / Pstar (t + 1)) S.μ := by
        refine Integrable.of_bound ((((hPsa t).measurable.mono (S.𝓕.le t) le_rfl).div
          ((hPsa (t + 1)).measurable.mono (S.𝓕.le (t + 1)) le_rfl)).aestronglyMeasurable)
          (Ms / m) (Eventually.of_forall fun ω => ?_)
        rw [Real.norm_eq_abs, Pi.div_apply, abs_of_pos (div_pos (hPs0 t ω) (hPs0 (t + 1) ω))]
        exact div_le_div₀ ((hPs0 t ω).le.trans (hPs t ω).2) (hPs t ω).2 hm (hPs (t + 1) ω).1
      rw [e1, e2]
      filter_upwards [S.E_add (hi1.indicator (S.𝓕.le t _ (hGm t)))
        (hi2.indicator (S.𝓕.le t _ (hGm t).compl)) t,
        condExp_indicator (m := S.𝓕 t) (μ := S.μ) hi1 (hGm t),
        condExp_indicator (m := S.𝓕 t) (μ := S.μ) hi2 (hGm t).compl, hrate t] with ω e3 e4 e5 e6
      rw [e3, Pi.add_apply]
      change S.E t (G.indicator (P t / P (t + 1))) ω +
        S.E t (Gᶜ.indicator (Pstar t / Pstar (t + 1))) ω = _
      have e4' : S.E t (G.indicator (P t / P (t + 1))) ω =
          G.indicator (S.E t (P t / P (t + 1))) ω := e4
      have e5' : S.E t (Gᶜ.indicator (Pstar t / Pstar (t + 1))) ω =
          Gᶜ.indicator (S.E t (Pstar t / Pstar (t + 1))) ω := e5
      rw [e4', e5']
      by_cases hω : ω ∈ G
      · rw [Set.indicator_of_mem hω, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hω),
          add_zero]
        exact e6
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_mem (Set.mem_compl hω), zero_add]
    have hflow2 : ∀ t ω, b2 t ω = (1 - β) * 0 + θ * (Pt t ω - P2 t ω) + β * b2 (t + 1) ω :=
      fun t ω => by
        by_cases hω : ω ∈ G
        · simp only [hb2, hP2, Set.indicator_of_mem hω]
          rw [hPtG t ω hω, hflow t ω, hB t ω, ha t ω]
          ring
        · simp only [hb2, hP2, Set.indicator_of_notMem hω]
          rw [hPtGc t ω hω]
          ring
    set gf : ℕ → Ω → ℝ := fun t ω => B t ω + θ * (cn ω - 1) * a t ω with hgf
    have hgfm : ∀ t, StronglyMeasurable[S.𝓕 t] (gf t) := fun t =>
      (hBm t).add ((stronglyMeasurable_const.mul ((hcnm t).sub stronglyMeasurable_const)).mul
        (ham t))
    have hgfpre : ∀ t, StronglyMeasurable[S.𝓕 t] (gf (t + 1)) := fun t =>
      (hBpre t).add ((stronglyMeasurable_const.mul ((hcnm t).sub stronglyMeasurable_const)).mul
        (hapre t))
    have hgfK : ∀ t ω, |G.indicator (gf t) ω| ≤ K + |θ| * ((n : ℝ) + 2) * Ka := fun t ω => by
      have hK : 0 ≤ K := (abs_nonneg _).trans (hBK t ω)
      have hKa : 0 ≤ Ka := (abs_nonneg _).trans (haK t ω)
      by_cases hω : ω ∈ G
      · rw [Set.indicator_of_mem hω]
        simp only [hgf]
        refine (abs_add_le _ _).trans (add_le_add (hBK t ω) ?_)
        rw [abs_mul, abs_mul]
        have h1 : |cn ω - 1| ≤ (n : ℝ) + 2 := by
          rw [abs_le]
          have := hcnb ω
          constructor <;> nlinarith
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (abs_nonneg θ)) (haK t ω) (abs_nonneg _)
          (by positivity)
      · rw [Set.indicator_of_notMem hω, abs_zero]
        positivity
    have hgfi : ∀ t, Integrable (G.indicator (gf t)) S.μ := fun t =>
      Integrable.of_bound ((((hgfm t).indicator (hGm t)).mono (S.𝓕.le t)).aestronglyMeasurable)
        _ (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgfK t ω)
    have hbGi : ∀ t, Integrable (G.indicator (b t)) S.μ := fun t =>
      (hbi t).indicator (S.𝓕.le 0 _ (hGm 0))
    have hpre2 : ∀ t, StronglyMeasurable[S.𝓕 t] (b2 (t + 1)) := fun t =>
      ((hpre t).indicator (hGm t)).sub ((hgfpre t).indicator (hGm t))
    have hb02 : ∀ ω, b2 0 ω = 0 := fun ω => by
      by_cases hω : ω ∈ G
      · simp only [hb2, Set.indicator_of_mem hω]
        rw [hcnG ω hω]
        simp only [hc_def]
        have := (hapos 0 ω).ne'
        field_simp
        ring
      · simp [hb2, hω]
    have hbi2 : ∀ t, Integrable (b2 t) S.μ := fun t => (hbGi t).sub (hgfi t)
    have hGtvc : ∀ t, ∀ᵐ ω ∂S.μ,
        Tendsto (fun T => β ^ T * S.E t (G.indicator (b (t + T))) ω) atTop (𝓝 0) := by
      intro t
      filter_upwards [htvc t, ae_all_iff.2 fun T =>
        condExp_indicator (m := S.𝓕 t) (μ := S.μ) (hbi (t + T)) (hGm t)] with ω e1 e2
      by_cases hω : ω ∈ G
      · refine e1.congr fun T => ?_
        have e2' : S.E t (G.indicator (b (t + T))) ω = G.indicator (S.E t (b (t + T))) ω :=
          e2 T
        rw [e2', Set.indicator_of_mem hω]
      · refine tendsto_const_nhds.congr fun T => ?_
        have e2' : S.E t (G.indicator (b (t + T))) ω = G.indicator (S.E t (b (t + T))) ω :=
          e2 T
        rw [e2', Set.indicator_of_notMem hω, mul_zero]
    have htvc2 : ∀ t, ∀ᵐ ω ∂S.μ,
        Tendsto (fun T => β ^ T * S.E t (b2 (t + T)) ω) atTop (𝓝 0) :=
      tvc_sub_bdd S hβ0 hβ1 (b := fun t => G.indicator (b t)) (g := fun t => G.indicator (gf t))
        hbGi hgfi hgfK hGtvc
    have h := fr_unique_stochastic S hβ0 hβ1 hθ (bbar := 0) (b0 := 0) hPtpos hPta hPtM hqt
      hP2a hm2 hP2s ha2r ha2pre ha2K hrate2 hflow2 hpre2 hb02 hbi2 htvc2 t
    filter_upwards [h] with ω e hω
    rw [← hPtG t ω hω, e]
    simp only [hP2, sub_self, zero_div, add_zero, one_mul]
    rw [hcnG ω hω]
  -- every state with `c > 0` lies in some `G_n`
  filter_upwards [hcpos, ae_all_iff.2 hloc] with ω h1 h2
  obtain ⟨n1, hn1⟩ := exists_nat_one_div_lt h1
  obtain ⟨n2, hn2⟩ := exists_nat_ge (c ω)
  refine h2 (n1 + n2) ⟨?_, ?_⟩
  · refine le_trans ?_ hn1.le
    rw [Nat.cast_add]
    exact one_div_le_one_div_of_le (by positivity) (by linarith [(n2.cast_nonneg : (0 : ℝ) ≤ n2)])
  · rw [Nat.cast_add]
    linarith [(n1.cast_nonneg : (0 : ℝ) ≤ n1)]

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d) for a general `s₀`, random date-0 data,
no band assumed**, prices bounded away from zero): as `fr_unique_s0_random_full`, with prices
`≥ m_P > 0` and the bounded real-rate hypothesis instead of bounded-above prices, so the band of
`fr_unique_s0_random_below` is not needed either (localisation on `G_n` with
`fr_unique_stochastic_below`). -/
theorem fr_unique_s0_random_below_full {β θ K m Ms mP Ka L : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
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
      (Pstar (t + i) ω * S.E (t + i) (fun ω => 1 / Pstar (t + i + 1) ω) ω)⁻¹ ≤ L) (t : ℕ) :
    P t =ᵐ[S.μ] fun ω => (1 + (b 0 ω - B 0 ω) / (θ * a 0 ω)) * Pstar t ω := by
  obtain ⟨hP, hPa, hPi, hbi, hrate, hflow, hpre, -, htvc⟩ := hE
  have h1β : 0 < 1 - β := by linarith
  have hPs0 : ∀ t ω, 0 < Pstar t ω := fun t ω => hm.trans_le (hPs t ω).1
  have hBm : ∀ t, StronglyMeasurable[S.𝓕 t] (B t) := fun t => by
    have e : B t = fun ω => s0 t ω + β * B (t + 1) ω := funext (hB t)
    rw [e]
    exact (hs0m t).add ((hBpre t).const_mul β)
  have hBi : ∀ t, Integrable (B t) S.μ := fun t =>
    Integrable.of_bound ((hBm t).mono (S.𝓕.le t)).aestronglyMeasurable K
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hBK t ω)
  have ham : ∀ t, StronglyMeasurable[S.𝓕 t] (a t) := targetValue_adapted S hPsa ha hapre
  have hai : ∀ t, Integrable (a t) S.μ := fun t =>
    Integrable.of_bound ((ham t).mono (S.𝓕.le t)).aestronglyMeasurable Ka
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact haK t ω)
  have hapos : ∀ t ω, 0 < a t ω := fun t ω =>
    (div_pos hm (by linarith)).trans_le (targetValue_ge hβ0 hβ1 (fun t ω => (hPs t ω).1) ha haK t ω)
  have hbm : ∀ t, StronglyMeasurable[S.𝓕 t] (b t) := fun t => by
    have e : b t = fun ω => s0 t ω + θ * (P t ω - Pstar t ω) + β * b (t + 1) ω := funext (hflow t)
    rw [e]
    exact ((hs0m t).add (((hPa t).sub (hPsa t)).const_mul θ)).add ((hpre t).const_mul β)
  set c : Ω → ℝ := fun ω => 1 + (b 0 ω - B 0 ω) / (θ * a 0 ω) with hc_def
  have hcm : ∀ t, StronglyMeasurable[S.𝓕 t] c := fun t =>
    ((measurable_const.add (((hbm 0).measurable.sub (hBm 0).measurable).div
      ((ham 0).measurable.const_mul θ))).stronglyMeasurable).mono (S.𝓕.mono (Nat.zero_le t))
  -- `c > 0` a.e.: `c = V₀/a₀` with `V` the (positive) value of the price path
  have hcpos : ∀ᵐ ω ∂S.μ, 0 < c ω := by
    set V : ℕ → Ω → ℝ := fun t ω => θ⁻¹ * (b t ω - B t ω) + a t ω with hV_def
    have hVrec : ∀ t ω, V t ω = P t ω + β * V (t + 1) ω := fun t ω => by
      simp only [hV_def]
      rw [hflow t ω, hB t ω, ha t ω]
      field_simp
      ring
    have hVm : ∀ t, StronglyMeasurable[S.𝓕 t] (V t) := fun t =>
      (((hbm t).sub (hBm t)).const_mul θ⁻¹).add (ham t)
    have hVi : ∀ t, Integrable (V t) S.μ := fun t =>
      (((hbi t).sub (hBi t)).const_mul θ⁻¹).add (hai t)
    have hVtvc : ∀ t, ∀ᵐ ω ∂S.μ,
        Tendsto (fun k => β ^ k * S.E t (V (t + k)) ω) atTop (𝓝 0) := by
      intro t
      have hg := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1
      have hlin : ∀ k, ∀ᵐ ω ∂S.μ, S.E t (V (t + k)) ω =
          θ⁻¹ * S.E t (fun ω => b (t + k) ω - B (t + k) ω) ω + S.E t (a (t + k)) ω := fun k => by
        have e : V (t + k) = θ⁻¹ • (b (t + k) - B (t + k)) + a (t + k) := by
          funext ω
          simp [hV_def]
        filter_upwards [S.E_add (((hbi (t + k)).sub (hBi (t + k))).smul θ⁻¹) (hai (t + k)) t,
          S.E_smul θ⁻¹ (b (t + k) - B (t + k)) t] with ω e1 e2
        rw [e, e1, Pi.add_apply, e2, Pi.smul_apply, smul_eq_mul]
        rfl
      filter_upwards [tvc_sub_bdd S hβ0 hβ1 hbi hBi hBK htvc t, ae_all_iff.2 hlin,
        ae_all_iff.2 fun k => S.abs_E_le (Eventually.of_forall fun ω => haK (t + k) ω) t]
        with ω h1 h2 h4
      have hA : Tendsto (fun k => β ^ k * S.E t (a (t + k)) ω) atTop (𝓝 0) := by
        refine squeeze_zero_norm (fun k => ?_) (by simpa using hg.mul_const Ka)
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 k)]
        exact mul_le_mul_of_nonneg_left (h4 k) (pow_pos hβ0 k).le
      have := (h1.const_mul θ⁻¹).add hA
      rw [mul_zero, zero_add] at this
      refine this.congr fun k => ?_
      rw [h2 k]
      ring
    have hVnn := value_nonneg S hβ0 hP hVrec hVm hVi hPi hVtvc
    filter_upwards [hVnn 1] with ω h
    have e : c ω = V 0 ω / a 0 ω := by
      simp only [hc_def, hV_def]
      have := (hapos 0 ω).ne'
      field_simp
      ring
    rw [e]
    have := hVrec 0 ω
    have := hP 0 ω
    exact div_pos (by nlinarith) (hapos 0 ω)
  -- localisation on `G_n = {1/(n+1) ≤ c ≤ n+1}`
  have hloc : ∀ n : ℕ, ∀ᵐ ω ∂S.μ, (1 / ((n : ℝ) + 1) ≤ c ω ∧ c ω ≤ (n : ℝ) + 1) →
      P t ω = c ω * Pstar t ω := by
    intro n
    have hn0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hn1 : 1 / ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    set G : Set Ω := {ω | 1 / ((n : ℝ) + 1) ≤ c ω ∧ c ω ≤ (n : ℝ) + 1} with hG
    have hGm : ∀ t, MeasurableSet[S.𝓕 t] G := fun t =>
      (measurableSet_le measurable_const (hcm t).measurable).inter
        (measurableSet_le (hcm t).measurable measurable_const)
    set cn : Ω → ℝ := fun ω => min (max (c ω) (1 / ((n : ℝ) + 1))) ((n : ℝ) + 1) with hcn
    have hcnm : ∀ t, StronglyMeasurable[S.𝓕 t] cn := fun t =>
      (((hcm t).measurable.max measurable_const).min measurable_const).stronglyMeasurable
    have hcnb : ∀ ω, 1 / ((n : ℝ) + 1) ≤ cn ω ∧ cn ω ≤ (n : ℝ) + 1 := fun ω =>
      ⟨le_min (le_max_right _ _) hn1, min_le_right _ _⟩
    have hcnG : ∀ ω ∈ G, cn ω = c ω := fun ω hω => by
      simp only [hcn]
      rw [max_eq_left hω.1, min_eq_left hω.2]
    have hcn0 : ∀ ω, 0 < cn ω := fun ω => hn0.trans_le (hcnb ω).1
    -- the glued price path, the scaled target and the adjusted debt
    set Pt : ℕ → Ω → ℝ := fun t ω => G.indicator (P t) ω +
      Gᶜ.indicator (fun ω => cn ω * Pstar t ω) ω with hPt
    set P2 : ℕ → Ω → ℝ := fun t ω => cn ω * Pstar t ω with hP2
    set a2 : ℕ → Ω → ℝ := fun t ω => cn ω * a t ω with ha2
    set b2 : ℕ → Ω → ℝ := fun t ω => G.indicator (b t) ω -
      G.indicator (fun ω => B t ω + θ * (cn ω - 1) * a t ω) ω with hb2
    have hPtG : ∀ t ω, ω ∈ G → Pt t ω = P t ω := fun t ω hω => by
      simp [hPt, hω]
    have hPtGc : ∀ t ω, ω ∉ G → Pt t ω = cn ω * Pstar t ω := fun t ω hω => by
      simp [hPt, hω]
    have hPtpos : ∀ t ω, 0 < Pt t ω := fun t ω => by
      by_cases hω : ω ∈ G
      · rw [hPtG t ω hω]; exact hP t ω
      · rw [hPtGc t ω hω]; exact mul_pos (hcn0 ω) (hPs0 t ω)
    have hPta : StronglyAdapted S.𝓕 Pt := fun t =>
      ((hPa t).indicator (hGm t)).add (((hcnm t).mul (hPsa t)).indicator (hGm t).compl)
    have hPtmP : ∀ t ω, min mP (m / ((n : ℝ) + 1)) ≤ Pt t ω := fun t ω => by
      by_cases hω : ω ∈ G
      · rw [hPtG t ω hω]; exact (min_le_left _ _).trans (hPmP t ω)
      · rw [hPtGc t ω hω]
        refine (min_le_right _ _).trans ?_
        calc m / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) * m := by ring
          _ ≤ cn ω * Pstar t ω := mul_le_mul (hcnb ω).1 (hPs t ω).1 hm.le (hcn0 ω).le
    have hPsi : ∀ t, Integrable (Pstar t) S.μ := fun t =>
      Integrable.of_bound ((hPsa t).mono (S.𝓕.le t)).aestronglyMeasurable Ms
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_pos (hPs0 t ω)]; exact (hPs t ω).2)
    have hPti : ∀ t, Integrable (Pt t) S.μ := fun t =>
      ((hPi t).indicator (S.𝓕.le 0 _ (hGm 0))).add
        ((Integrable.of_bound (((hcnm t).mul (hPsa t)).mono (S.𝓕.le t)).aestronglyMeasurable
          (((n : ℝ) + 1) * Ms) (Eventually.of_forall fun ω => by
            rw [Real.norm_eq_abs, Pi.mul_apply, abs_of_pos (mul_pos (hcn0 ω) (hPs0 t ω))]
            exact mul_le_mul (hcnb ω).2 (hPs t ω).2 (hPs0 t ω).le (by positivity))).indicator
          (S.𝓕.le 0 _ (hGm 0).compl))
    have hP2a : StronglyAdapted S.𝓕 P2 := fun t => (hcnm t).mul (hPsa t)
    have hm2 : 0 < m / ((n : ℝ) + 1) := by positivity
    have hP2s : ∀ t ω, m / ((n : ℝ) + 1) ≤ P2 t ω ∧ P2 t ω ≤ ((n : ℝ) + 1) * Ms := fun t ω => by
      refine ⟨?_, mul_le_mul (hcnb ω).2 (hPs t ω).2 (hPs0 t ω).le (by positivity)⟩
      calc m / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) * m := by ring
        _ ≤ cn ω * Pstar t ω := mul_le_mul (hcnb ω).1 (hPs t ω).1 hm.le (hcn0 ω).le
    have ha2r : ∀ t ω, a2 t ω = P2 t ω + β * a2 (t + 1) ω := fun t ω => by
      simp only [ha2, hP2]
      rw [ha t ω]
      ring
    have ha2pre : ∀ t, StronglyMeasurable[S.𝓕 t] (a2 (t + 1)) := fun t => (hcnm t).mul (hapre t)
    have ha2K : ∀ t ω, |a2 t ω| ≤ ((n : ℝ) + 1) * Ka := fun t ω => by
      simp only [ha2]
      rw [abs_mul, abs_of_pos (hcn0 ω)]
      exact mul_le_mul (hcnb ω).2 (haK t ω) (abs_nonneg _) (by positivity)
    have hrate2 : ∀ t, S.E t (Pt t / Pt (t + 1)) =ᵐ[S.μ] S.E t (P2 t / P2 (t + 1)) := fun t => by
      have e2 : P2 t / P2 (t + 1) = Pstar t / Pstar (t + 1) := funext fun ω => by
        simp only [Pi.div_apply, hP2]
        rw [mul_div_mul_left _ _ (hcn0 ω).ne']
      have e1 : Pt t / Pt (t + 1) =
          G.indicator (P t / P (t + 1)) + Gᶜ.indicator (Pstar t / Pstar (t + 1)) := by
        funext ω
        by_cases hω : ω ∈ G
        · simp [Pi.div_apply, hPtG _ ω hω, hω]
        · simp only [Pi.div_apply, Pi.add_apply, hPtGc _ ω hω]
          rw [Set.indicator_of_notMem hω, Set.indicator_of_mem (Set.mem_compl hω), zero_add,
            mul_div_mul_left _ _ (hcn0 ω).ne']
          rfl
      have hi1 : Integrable (P t / P (t + 1)) S.μ := by
        have hm1 : AEStronglyMeasurable (fun ω => 1 / P (t + 1) ω) S.μ :=
          (((hPa (t + 1)).mono (S.𝓕.le (t + 1))).measurable.const_div 1).aestronglyMeasurable
        have h := (hPi t).bdd_mul hm1 (c := 1 / mP) (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (hP (t + 1) ω))]
          exact one_div_le_one_div_of_le hmP (hPmP (t + 1) ω))
        exact h.congr (Eventually.of_forall fun ω => by
          simp [Pi.div_apply, div_eq_mul_inv, mul_comm])
      have hi2 : Integrable (Pstar t / Pstar (t + 1)) S.μ := by
        refine Integrable.of_bound ((((hPsa t).measurable.mono (S.𝓕.le t) le_rfl).div
          ((hPsa (t + 1)).measurable.mono (S.𝓕.le (t + 1)) le_rfl)).aestronglyMeasurable)
          (Ms / m) (Eventually.of_forall fun ω => ?_)
        rw [Real.norm_eq_abs, Pi.div_apply, abs_of_pos (div_pos (hPs0 t ω) (hPs0 (t + 1) ω))]
        exact div_le_div₀ ((hPs0 t ω).le.trans (hPs t ω).2) (hPs t ω).2 hm (hPs (t + 1) ω).1
      rw [e1, e2]
      filter_upwards [S.E_add (hi1.indicator (S.𝓕.le t _ (hGm t)))
        (hi2.indicator (S.𝓕.le t _ (hGm t).compl)) t,
        condExp_indicator (m := S.𝓕 t) (μ := S.μ) hi1 (hGm t),
        condExp_indicator (m := S.𝓕 t) (μ := S.μ) hi2 (hGm t).compl, hrate t] with ω e3 e4 e5 e6
      rw [e3, Pi.add_apply]
      change S.E t (G.indicator (P t / P (t + 1))) ω +
        S.E t (Gᶜ.indicator (Pstar t / Pstar (t + 1))) ω = _
      have e4' : S.E t (G.indicator (P t / P (t + 1))) ω =
          G.indicator (S.E t (P t / P (t + 1))) ω := e4
      have e5' : S.E t (Gᶜ.indicator (Pstar t / Pstar (t + 1))) ω =
          Gᶜ.indicator (S.E t (Pstar t / Pstar (t + 1))) ω := e5
      rw [e4', e5']
      by_cases hω : ω ∈ G
      · rw [Set.indicator_of_mem hω, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hω),
          add_zero]
        exact e6
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_mem (Set.mem_compl hω), zero_add]
    have hflow2 : ∀ t ω, b2 t ω = (1 - β) * 0 + θ * (Pt t ω - P2 t ω) + β * b2 (t + 1) ω :=
      fun t ω => by
        by_cases hω : ω ∈ G
        · simp only [hb2, hP2, Set.indicator_of_mem hω]
          rw [hPtG t ω hω, hflow t ω, hB t ω, ha t ω]
          ring
        · simp only [hb2, hP2, Set.indicator_of_notMem hω]
          rw [hPtGc t ω hω]
          ring
    set gf : ℕ → Ω → ℝ := fun t ω => B t ω + θ * (cn ω - 1) * a t ω with hgf
    have hgfm : ∀ t, StronglyMeasurable[S.𝓕 t] (gf t) := fun t =>
      (hBm t).add ((stronglyMeasurable_const.mul ((hcnm t).sub stronglyMeasurable_const)).mul
        (ham t))
    have hgfpre : ∀ t, StronglyMeasurable[S.𝓕 t] (gf (t + 1)) := fun t =>
      (hBpre t).add ((stronglyMeasurable_const.mul ((hcnm t).sub stronglyMeasurable_const)).mul
        (hapre t))
    have hgfK : ∀ t ω, |G.indicator (gf t) ω| ≤ K + |θ| * ((n : ℝ) + 2) * Ka := fun t ω => by
      have hK : 0 ≤ K := (abs_nonneg _).trans (hBK t ω)
      have hKa : 0 ≤ Ka := (abs_nonneg _).trans (haK t ω)
      by_cases hω : ω ∈ G
      · rw [Set.indicator_of_mem hω]
        simp only [hgf]
        refine (abs_add_le _ _).trans (add_le_add (hBK t ω) ?_)
        rw [abs_mul, abs_mul]
        have h1 : |cn ω - 1| ≤ (n : ℝ) + 2 := by
          rw [abs_le]
          have := hcnb ω
          constructor <;> nlinarith
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (abs_nonneg θ)) (haK t ω) (abs_nonneg _)
          (by positivity)
      · rw [Set.indicator_of_notMem hω, abs_zero]
        positivity
    have hgfi : ∀ t, Integrable (G.indicator (gf t)) S.μ := fun t =>
      Integrable.of_bound ((((hgfm t).indicator (hGm t)).mono (S.𝓕.le t)).aestronglyMeasurable)
        _ (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgfK t ω)
    have hbGi : ∀ t, Integrable (G.indicator (b t)) S.μ := fun t =>
      (hbi t).indicator (S.𝓕.le 0 _ (hGm 0))
    have hpre2 : ∀ t, StronglyMeasurable[S.𝓕 t] (b2 (t + 1)) := fun t =>
      ((hpre t).indicator (hGm t)).sub ((hgfpre t).indicator (hGm t))
    have hb02 : ∀ ω, b2 0 ω = 0 := fun ω => by
      by_cases hω : ω ∈ G
      · simp only [hb2, Set.indicator_of_mem hω]
        rw [hcnG ω hω]
        simp only [hc_def]
        have := (hapos 0 ω).ne'
        field_simp
        ring
      · simp [hb2, hω]
    have hbi2 : ∀ t, Integrable (b2 t) S.μ := fun t => (hbGi t).sub (hgfi t)
    have hGtvc : ∀ t, ∀ᵐ ω ∂S.μ,
        Tendsto (fun T => β ^ T * S.E t (G.indicator (b (t + T))) ω) atTop (𝓝 0) := by
      intro t
      filter_upwards [htvc t, ae_all_iff.2 fun T =>
        condExp_indicator (m := S.𝓕 t) (μ := S.μ) (hbi (t + T)) (hGm t)] with ω e1 e2
      by_cases hω : ω ∈ G
      · refine e1.congr fun T => ?_
        have e2' : S.E t (G.indicator (b (t + T))) ω = G.indicator (S.E t (b (t + T))) ω :=
          e2 T
        rw [e2', Set.indicator_of_mem hω]
      · refine tendsto_const_nhds.congr fun T => ?_
        have e2' : S.E t (G.indicator (b (t + T))) ω = G.indicator (S.E t (b (t + T))) ω :=
          e2 T
        rw [e2', Set.indicator_of_notMem hω, mul_zero]
    have htvc2 : ∀ t, ∀ᵐ ω ∂S.μ,
        Tendsto (fun T => β ^ T * S.E t (b2 (t + T)) ω) atTop (𝓝 0) :=
      tvc_sub_bdd S hβ0 hβ1 (b := fun t => G.indicator (b t)) (g := fun t => G.indicator (gf t))
        hbGi hgfi hgfK hGtvc
    have hqs : ∀ t, Integrable (fun ω => 1 / Pstar t ω) S.μ := fun t =>
      Integrable.of_bound (((hPsa t).measurable.const_div 1).stronglyMeasurable.mono
        (S.𝓕.le t)).aestronglyMeasurable (1 / m)
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (hPs0 t ω))]
          exact one_div_le_one_div_of_le hm (hPs t ω).1)
    have hL2 : ∀ t k, ∀ᵐ ω ∂S.μ, ∏ i ∈ Finset.range k,
        (P2 (t + i) ω * S.E (t + i) (fun ω => 1 / P2 (t + i + 1) ω) ω)⁻¹ ≤ L := by
      intro t k
      have hpo : ∀ i, S.E (t + i) (fun ω => 1 / P2 (t + i + 1) ω) =ᵐ[S.μ]
          (fun ω => 1 / cn ω) * S.E (t + i) (fun ω => 1 / Pstar (t + i + 1) ω) := fun i => by
        have e : (fun ω => 1 / P2 (t + i + 1) ω) =
            (fun ω => 1 / cn ω) * fun ω => 1 / Pstar (t + i + 1) ω := funext fun ω => by
          simp only [hP2, Pi.mul_apply]
          rw [one_div_mul_one_div]
        rw [e]
        exact S.E_pullOut (((hcnm (t + i)).measurable.const_div 1).stronglyMeasurable)
          (C := (n : ℝ) + 1) (Eventually.of_forall fun ω => by
            rw [abs_of_pos (one_div_pos.2 (hcn0 ω))]
            rw [div_le_iff₀ (hcn0 ω)]
            have := (hcnb ω).1
            rw [div_le_iff₀ (by positivity)] at this
            linarith) (hqs (t + i + 1))
      filter_upwards [hL t k, ae_all_iff.2 hpo] with ω h1 h2
      refine (Finset.prod_congr rfl fun i _ => ?_).trans_le h1
      rw [h2 i, Pi.mul_apply]
      have := (hcn0 ω).ne'
      simp only [hP2]
      field_simp
    have h := fr_unique_stochastic_below S hβ0 hβ1 hθ (bbar := 0) (b0 := 0) hPta
      (lt_min hmP hm2) hPtmP hPti hP2a hm2 hP2s ha2r ha2pre ha2K hrate2 hflow2 hpre2 hb02 hbi2
      htvc2 hL2 t
    filter_upwards [h] with ω e hω
    rw [← hPtG t ω hω, e]
    simp only [hP2, sub_self, zero_div, add_zero, one_mul]
    rw [hcnG ω hω]
  -- every state with `c > 0` lies in some `G_n`
  filter_upwards [hcpos, ae_all_iff.2 hloc] with ω h1 h2
  obtain ⟨n1, hn1⟩ := exists_nat_one_div_lt h1
  obtain ⟨n2, hn2⟩ := exists_nat_ge (c ω)
  refine h2 (n1 + n2) ⟨?_, ?_⟩
  · refine le_trans ?_ hn1.le
    rw [Nat.cast_add]
    exact one_div_le_one_div_of_le (by positivity) (by linarith [(n2.cast_nonneg : (0 : ℝ) ≤ n2)])
  · rw [Nat.cast_add]
    linarith [(n1.cast_nonneg : (0 : ℝ) ≤ n1)]

/-! ### Existence with news and `b₀ ≠ b̄`: the one-shot class -/

/-- Cochrane (2023), §9.3.2, p. 267 (news at a single date): the filtration with no information at
date `0` and full information from date `1` on. -/
def oneShotFiltration : Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq t := if t = 0 then ⊥ else inferInstance
  mono' s t hst := by
    simp only
    split_ifs <;> first | exact bot_le | exact le_rfl | omega
  le' t := by
    split_ifs
    · exact bot_le
    · exact le_rfl

/-- Cochrane (2023), §9.3.2, p. 267: the one-shot expectation system — all news arrives at date `1`.
-/
noncomputable def oneShot (Pm : ProbabilityMeasure Ω) : MeasExpectationSystem Ω :=
  ⟨Pm, oneShotFiltration⟩

/-- Cochrane (2023), §9.3.2, p. 267: on the one-shot system `E_0 f = E f` (a constant). -/
theorem oneShot_E_zero (Pm : ProbabilityMeasure Ω) (f : Ω → ℝ) :
    (oneShot Pm).E 0 f = fun _ => ∫ ω, f ω ∂(oneShot Pm).μ := by
  have h : (oneShot Pm).𝓕 0 = ⊥ := by simp [oneShot, oneShotFiltration]
  change (oneShot Pm).μ[f | (oneShot Pm).𝓕 0] = _
  rw [h]
  exact condExp_bot f

/-- Cochrane (2023), §9.3.2, p. 267: on the one-shot system every variable is known from date `1`,
`E_{t+1} f = f` for measurable integrable `f`. -/
theorem oneShot_E_succ (Pm : ProbabilityMeasure Ω) (t : ℕ) {f : Ω → ℝ} (hf : Measurable f)
    (hfi : Integrable f (oneShot Pm).μ) : (oneShot Pm).E (t + 1) f = f := by
  have h : (oneShot Pm).𝓕 (t + 1) = ‹MeasurableSpace Ω› := by simp [oneShot, oneShotFiltration]
  refine (oneShot Pm).E_of_stronglyMeasurable ?_ hfi
  rw [h]
  exact hf.stronglyMeasurable

/-- Cochrane (2023), §9.3.2, p. 267: a variable known at date `0` of the one-shot system is a
constant. -/
theorem oneShot_const (Pm : ProbabilityMeasure Ω) {f : Ω → ℝ}
    (hf : StronglyMeasurable[(oneShot Pm).𝓕 0] f) (hfi : Integrable f (oneShot Pm).μ) :
    f = fun _ => ∫ ω, f ω ∂(oneShot Pm).μ := by
  rw [← oneShot_E_zero Pm f]
  exact ((oneShot Pm).E_of_stronglyMeasurable hf hfi).symm

/-- Cochrane (2023), §9.3.2, p. 267: the one-shot target — `P*_0 = p₀`, and `P*_t = x` (a random
variable revealed at date `1`) for `t ≥ 1`. -/
def osTarget (p0 : ℝ) (x : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => p0
  | _ + 1 => x

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**existence with news: the reduction**): on the one-shot
system with target `osTarget p₀ x` (`0 < m ≤ x ≤ M*`, `p₀ > 0`) and initial debt `b₀ = b̄ + θ d₀`,
every equilibrium with prices bounded above is described by one number `d` (scaled date-1 debt):
`P_0 = p₀ + d₀ − β d`, `P_t = x + (1 − β) d` a.e. for `t ≥ 1`, `x + (1 − β) d > 0` a.e., and
`(p₀ + d₀ − β d) E[1/(x + (1 − β) d)] = p₀ E[1/x]` (the interest-rate target at date `0`). -/
theorem oneShot_eqm_form (Pm : ProbabilityMeasure Ω) {β θ bbar d0 p0 m Ms M : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ : θ ≠ 0) {x : Ω → ℝ} (hx : Measurable x) (hm : 0 < m)
    (hxb : ∀ ω, m ≤ x ω ∧ x ω ≤ Ms) (hp0 : 0 < p0) {P b : ℕ → Ω → ℝ}
    (hE : RuleEqm (oneShot Pm) β θ bbar (osTarget p0 x) P b) (hPM : ∀ t ω, P t ω ≤ M)
    (hq : ∀ t, Integrable (fun ω => 1 / P t ω) (oneShot Pm).μ)
    (hb0 : ∀ ω, b 0 ω = bbar + θ * d0) :
    ∃ d : ℝ, (∀ᵐ ω ∂(oneShot Pm).μ, 0 < x ω + (1 - β) * d) ∧
      (∀ ω, P 0 ω = p0 + d0 - β * d) ∧
      (∀ t, P (t + 1) =ᵐ[(oneShot Pm).μ] fun ω => x ω + (1 - β) * d) ∧
      (p0 + d0 - β * d) * ∫ ω, 1 / (x ω + (1 - β) * d) ∂(oneShot Pm).μ =
        p0 * ∫ ω, 1 / x ω ∂(oneShot Pm).μ := by
  set S := oneShot Pm with hS
  obtain ⟨hP, hPa, hPi, hbi, hrate, hflow, hpre, -, htvc⟩ := hE
  have h1β : 0 < 1 - β := by linarith
  have hx0 : ∀ ω, 0 < x ω := fun ω => hm.trans_le (hxb ω).1
  have hPsa : StronglyAdapted S.𝓕 (osTarget p0 x) := fun t => by
    cases t with
    | zero => exact stronglyMeasurable_const
    | succ t =>
      have h : S.𝓕 (t + 1) = ‹MeasurableSpace Ω› := by simp [hS, oneShot, oneShotFiltration]
      change StronglyMeasurable[S.𝓕 (t + 1)] x
      rw [h]
      exact hx.stronglyMeasurable
  have hPsb : ∀ t ω, |osTarget p0 x t ω| ≤ max p0 Ms := fun t ω => by
    cases t with
    | zero => simp [osTarget, abs_of_pos hp0]
    | succ t =>
      simp only [osTarget]
      rw [abs_of_pos (hx0 ω)]
      exact (hxb ω).2.trans (le_max_right _ _)
  -- bounded debt
  have hsC : ∀ t ω, |(1 - β) * bbar + θ * (P t ω - osTarget p0 x t ω)| ≤
      |(1 - β) * bbar| + |θ| * (|M| + max p0 Ms) := fun t ω => by
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add ?_ (hPsb t ω)))
      (abs_nonneg θ)
    rw [abs_of_pos (hP t ω)]
    exact (hPM t ω).trans (le_abs_self M)
  have hbB := debt_bdd S hβ0 hβ1
    (fun t => stronglyMeasurable_const.add (((hPa t).sub (hPsa t)).const_mul θ)) hsC hflow hpre
    hbi htvc
  set Cb := (|(1 - β) * bbar| + |θ| * (|M| + max p0 Ms)) / (1 - β) with hCb
  -- date-0 variables are constants
  have hP0 := oneShot_const Pm (hPa 0) (hPi 0)
  have hb1 := oneShot_const Pm (hpre 0) (hbi 1)
  set P0 := ∫ ω, P 0 ω ∂S.μ with hP0def
  set b1 := ∫ ω, b 1 ω ∂S.μ with hb1def
  set d := θ⁻¹ * (b1 - bbar) with hd
  have hP0e : ∀ ω, P 0 ω = p0 + d0 - β * d := fun ω => by
    have h := hflow 0 ω
    rw [hb0 ω, congrFun hb1 ω, congrFun hP0 ω] at h
    rw [congrFun hP0 ω, hd]
    simp only [osTarget] at h
    have hθθ : θ * θ⁻¹ = 1 := mul_inv_cancel₀ hθ
    have key : θ * (P0 - (p0 + d0 - β * (θ⁻¹ * (b1 - bbar)))) = 0 := by
      linear_combination (-1 : ℝ) * h + β * (b1 - bbar) * hθθ
    have := (mul_eq_zero.1 key).resolve_left hθ
    linarith
  -- for `t ≥ 1` the price level is constant over time
  have hrat : ∀ t, P (t + 2) =ᵐ[S.μ] P (t + 1) := fun t => by
    have hint : Integrable (P (t + 1) / P (t + 1 + 1)) S.μ := by
      have h := (hq (t + 1 + 1)).bdd_mul (c := M)
        ((hPa (t + 1)).mono (S.𝓕.le _)).aestronglyMeasurable
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_pos (hP _ ω)]; exact hPM _ ω)
      exact h.congr (Eventually.of_forall fun ω => by simp [Pi.div_apply, div_eq_mul_inv])
    have hmeas : Measurable (P (t + 1) / P (t + 1 + 1)) :=
      ((hPa (t + 1)).mono (S.𝓕.le _)).measurable.div ((hPa (t + 1 + 1)).mono (S.𝓕.le _)).measurable
    have e1 := oneShot_E_succ Pm t hmeas hint
    have e2 : osTarget p0 x (t + 1) / osTarget p0 x (t + 1 + 1) = fun _ => 1 := by
      funext ω
      simp [osTarget, (hx0 ω).ne']
    have h := hrate (t + 1)
    rw [e2, S.E_const] at h
    change S.E (t + 1) (P (t + 1) / P (t + 1 + 1)) =ᵐ[S.μ] _ at h
    rw [e1] at h
    filter_upwards [h] with ω e
    rw [Pi.div_apply, div_eq_one_iff_eq (hP _ ω).ne'] at e
    exact e.symm
  have hPc : ∀ t, P (t + 1) =ᵐ[S.μ] P 1 := fun t => by
    induction t with
    | zero => exact EventuallyEq.rfl
    | succ t ih => exact (hrat t).trans ih
  -- the transversality condition pins `b_1`
  have hb1e : ∀ᵐ ω ∂S.μ, b 1 ω = bbar + θ * (P 1 ω - x ω) / (1 - β) := by
    have hk : ∀ k, ∀ᵐ ω ∂S.μ, b 1 ω - (bbar + θ * (P 1 ω - x ω) / (1 - β)) =
        β ^ k * (b (k + 1) ω - (bbar + θ * (P 1 ω - x ω) / (1 - β))) := fun k => by
      induction k with
      | zero => exact Eventually.of_forall fun ω => by simp
      | succ k ih =>
        filter_upwards [ih, hPc k] with ω e1 e2
        rw [e1]
        have h := hflow (k + 1) ω
        simp only [osTarget] at h
        rw [e2] at h
        have h1β' : (1 - β) ≠ 0 := h1β.ne'
        have key : b (k + 1) ω - (bbar + θ * (P 1 ω - x ω) / (1 - β)) =
            β * (b (k + 1 + 1) ω - (bbar + θ * (P 1 ω - x ω) / (1 - β))) := by
          rw [h]
          field_simp
          ring
        rw [key, pow_succ]
        ring
    have hbd : ∀ ω, |bbar + θ * (P 1 ω - x ω) / (1 - β)| ≤
        |bbar| + |θ| * (|M| + Ms) / (1 - β) := fun ω => by
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_div, abs_of_pos h1β, abs_mul]
      refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (abs_nonneg θ)) h1β.le
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rw [abs_of_pos (hP 1 ω)]; exact (hPM 1 ω).trans (le_abs_self M)
      · rw [abs_of_pos (hx0 ω)]; exact (hxb ω).2
    filter_upwards [ae_all_iff.2 hk, ae_all_iff.2 hbB] with ω e1 e2
    have hb : ∀ k, |b 1 ω - (bbar + θ * (P 1 ω - x ω) / (1 - β))| ≤
        β ^ k * (Cb + (|bbar| + |θ| * (|M| + Ms) / (1 - β))) := fun k => by
      rw [e1 k, abs_mul, abs_of_pos (pow_pos hβ0 k)]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (e2 (k + 1)) (hbd ω)))
        (pow_pos hβ0 k).le
    have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const
      (Cb + (|bbar| + |θ| * (|M| + Ms) / (1 - β)))
    rw [zero_mul] at hlim
    have := abs_nonpos_iff.mp (ge_of_tendsto' hlim hb)
    linarith
  have hP1 : P 1 =ᵐ[S.μ] fun ω => x ω + (1 - β) * d := by
    filter_upwards [hb1e] with ω e
    rw [congrFun hb1 ω] at e
    have key : θ * (P 1 ω - x ω) = (1 - β) * (b1 - bbar) := by
      rw [e]
      field_simp
      ring
    rw [hd]
    calc P 1 ω = x ω + θ⁻¹ * (θ * (P 1 ω - x ω)) := by field_simp; ring
      _ = x ω + (1 - β) * (θ⁻¹ * (b1 - bbar)) := by rw [key]; ring
  refine ⟨d, ?_, hP0e, fun t => (hPc t).trans hP1, ?_⟩
  · filter_upwards [hP1] with ω e
    rw [← e]
    exact hP 1 ω
  · -- the interest-rate target at date `0`
    have h := hrate 0
    rw [oneShot_E_zero, oneShot_E_zero] at h
    obtain ⟨ω, hω⟩ := h.exists
    have e1 : ∫ ω, (P 0 / P (0 + 1)) ω ∂S.μ =
        (p0 + d0 - β * d) * ∫ ω, 1 / (x ω + (1 - β) * d) ∂S.μ := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hP1] with ω e
      simp only [Pi.div_apply]
      rw [hP0e ω, e]
      ring
    have e2 : ∫ ω, (osTarget p0 x 0 / osTarget p0 x (0 + 1)) ω ∂S.μ =
        p0 * ∫ ω, 1 / x ω ∂S.μ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp [osTarget, div_eq_mul_inv]
    rw [← e1, ← e2]
    exact hω

/-- Cochrane (2023), §9.3.2, p. 267 (one-shot class): the candidate price path
`P_0 = p₀ + d₀ − β d`, `P_t = x + (1 − β) d` for `t ≥ 1`. -/
noncomputable def osPrice (β p0 d0 d : ℝ) (x : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => p0 + d0 - β * d
  | _ + 1 => fun ω => x ω + (1 - β) * d

/-- Cochrane (2023), §9.3.2, p. 267 (one-shot class): the candidate real debt `b_0 = b̄ + θ d₀`,
`b_t = b̄ + θ d` for `t ≥ 1`. -/
def osDebt (bbar θ d0 d : ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => bbar + θ * d0
  | _ + 1 => fun _ => bbar + θ * d

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**existence with news: the converse**): on the one-shot
system, every number `d` with `x + (1 − β) d > 0`, `p₀ + d₀ − β d > 0` and
`(p₀ + d₀ − β d) E[1/(x + (1 − β) d)] = p₀ E[1/x]` gives an equilibrium (`RuleEqm`) with initial
debt `b̄ + θ d₀` and prices bounded above. Together with `oneShot_eqm_form` this is the exact
existence condition for a target whose news arrives at one date. -/
theorem oneShot_eqm_exists (Pm : ProbabilityMeasure Ω) {β θ bbar d0 p0 m Ms d : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) {x : Ω → ℝ} (hx : Measurable x) (hm : 0 < m)
    (hxb : ∀ ω, m ≤ x ω ∧ x ω ≤ Ms) (hp0 : 0 < p0) (hd : ∀ ω, 0 < x ω + (1 - β) * d)
    (hP0 : 0 < p0 + d0 - β * d)
    (heq : (p0 + d0 - β * d) * ∫ ω, 1 / (x ω + (1 - β) * d) ∂(oneShot Pm).μ =
      p0 * ∫ ω, 1 / x ω ∂(oneShot Pm).μ) :
    RuleEqm (oneShot Pm) β θ bbar (osTarget p0 x) (osPrice β p0 d0 d x) (osDebt bbar θ d0 d) ∧
      (∀ ω : Ω, osDebt bbar θ d0 d 0 ω = bbar + θ * d0) ∧
      (∀ t ω, osPrice β p0 d0 d x t ω ≤ max (p0 + d0 - β * d) (Ms + |(1 - β) * d|)) ∧
      ∀ t, Integrable (fun ω => 1 / osPrice β p0 d0 d x t ω) (oneShot Pm).μ := by
  set S := oneShot Pm with hS
  have h1β : 0 < 1 - β := by linarith
  have hx0 : ∀ ω, 0 < x ω := fun ω => hm.trans_le (hxb ω).1
  have hF : ∀ t, S.𝓕 (t + 1) = ‹MeasurableSpace Ω› := fun t => by
    simp [hS, oneShot, oneShotFiltration]
  have hxi : Integrable (fun ω => 1 / x ω) S.μ :=
    Integrable.of_bound (hx.const_div 1).aestronglyMeasurable (1 / m)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (hx0 ω))]
        exact one_div_le_one_div_of_le hm (hxb ω).1)
  have hne : Nonempty Ω := by
    by_contra hΩ
    rw [not_nonempty_iff] at hΩ
    have h1 : S.μ Set.univ = 1 := measure_univ
    rw [Set.univ_eq_empty_iff.2 hΩ, measure_empty] at h1
    exact zero_ne_one h1
  have hxpos : 0 < ∫ ω, 1 / x ω ∂S.μ := by
    have hMs : 0 < Ms := (hx0 (Classical.arbitrary Ω)).trans_le (hxb _).2
    have h := integral_mono (integrable_const (1 / Ms)) hxi (fun ω =>
      one_div_le_one_div_of_le (hx0 ω) (hxb ω).2)
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
    exact (one_div_pos.2 hMs).trans_le h
  have hyi : Integrable (fun ω => 1 / (x ω + (1 - β) * d)) S.μ := by
    by_contra hni
    rw [integral_undef hni, mul_zero] at heq
    have := mul_pos hp0 hxpos
    linarith
  have hPm : ∀ t, Measurable (osPrice β p0 d0 d x t) := fun t => by
    cases t with
    | zero => exact measurable_const
    | succ t => exact hx.add_const _
  have hPa : StronglyAdapted S.𝓕 (osPrice β p0 d0 d x) := fun t => by
    cases t with
    | zero => exact stronglyMeasurable_const
    | succ t => rw [hF t]; exact (hPm (t + 1)).stronglyMeasurable
  have hPsa : StronglyAdapted S.𝓕 (osTarget p0 x) := fun t => by
    cases t with
    | zero => exact stronglyMeasurable_const
    | succ t => rw [hF t]; exact hx.stronglyMeasurable
  have hPpos : ∀ t ω, 0 < osPrice β p0 d0 d x t ω := fun t ω => by
    cases t with
    | zero => exact hP0
    | succ t => exact hd ω
  have hPM : ∀ t ω, osPrice β p0 d0 d x t ω ≤ max (p0 + d0 - β * d) (Ms + |(1 - β) * d|) :=
    fun t ω => by
      cases t with
      | zero => exact le_max_left _ _
      | succ t =>
        refine le_trans ?_ (le_max_right _ _)
        change x ω + (1 - β) * d ≤ _
        linarith [(hxb ω).2, le_abs_self ((1 - β) * d)]
  have hPi : ∀ t, Integrable (osPrice β p0 d0 d x t) S.μ := fun t =>
    Integrable.of_bound (hPm t).aestronglyMeasurable
      (max (p0 + d0 - β * d) (Ms + |(1 - β) * d|))
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (hPpos t ω)]; exact hPM t ω)
  have hbK : ∀ t (ω : Ω), |osDebt bbar θ d0 d t ω| ≤ |bbar + θ * d0| + |bbar + θ * d| :=
    fun t ω => by
      cases t with
      | zero => exact le_add_of_nonneg_right (abs_nonneg _)
      | succ t => exact le_add_of_nonneg_left (abs_nonneg _)
  have hbpre : ∀ t, StronglyMeasurable[S.𝓕 t] (osDebt bbar θ d0 d (t + 1)) := fun t =>
    stronglyMeasurable_const
  have hflow : ∀ t ω, osDebt bbar θ d0 d t ω = (1 - β) * bbar +
      θ * (osPrice β p0 d0 d x t ω - osTarget p0 x t ω) + β * osDebt bbar θ d0 d (t + 1) ω :=
    fun t ω => by
      cases t with
      | zero => simp only [osDebt, osPrice, osTarget]; ring
      | succ t => simp only [osDebt, osPrice, osTarget]; ring
  have hsm : ∀ t, StronglyMeasurable[S.𝓕 t]
      (fun ω => (1 - β) * bbar + θ * (osPrice β p0 d0 d x t ω - osTarget p0 x t ω)) := fun t =>
    stronglyMeasurable_const.add (((hPa t).sub (hPsa t)).const_mul θ)
  have hsC : ∀ t ω, |(1 - β) * bbar + θ * (osPrice β p0 d0 d x t ω - osTarget p0 x t ω)| ≤
      |bbar + θ * d0| + |bbar + θ * d| + β * (|bbar + θ * d0| + |bbar + θ * d|) := fun t ω => by
    have h := hflow t ω
    have e : (1 - β) * bbar + θ * (osPrice β p0 d0 d x t ω - osTarget p0 x t ω) =
        osDebt bbar θ d0 d t ω - β * osDebt bbar θ d0 d (t + 1) ω := by linarith
    rw [e]
    refine (abs_sub _ _).trans (add_le_add (hbK t ω) ?_)
    rw [abs_mul, abs_of_pos hβ0]
    exact mul_le_mul_of_nonneg_left (hbK (t + 1) ω) hβ0.le
  refine ⟨⟨hPpos, hPa, hPi, fun t => ?_, fun t => ?_, hflow, hbpre,
    fun t => hasSum_E_value S hβ0 hβ1 hsm hsC hflow hbpre hbK t, fun t => ?_⟩,
    fun ω => rfl, hPM, fun t => ?_⟩
  · exact Integrable.of_bound (by cases t <;> exact aestronglyMeasurable_const) _
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hbK t ω)
  · cases t with
    | zero =>
      refine EventuallyEq.of_eq ?_
      rw [oneShot_E_zero, oneShot_E_zero]
      funext ω
      have e1 : ∫ ω, (osPrice β p0 d0 d x 0 / osPrice β p0 d0 d x (0 + 1)) ω ∂S.μ =
          (p0 + d0 - β * d) * ∫ ω, 1 / (x ω + (1 - β) * d) ∂S.μ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp [osPrice, div_eq_mul_inv]
      have e2 : ∫ ω, (osTarget p0 x 0 / osTarget p0 x (0 + 1)) ω ∂S.μ =
          p0 * ∫ ω, 1 / x ω ∂S.μ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp [osTarget, div_eq_mul_inv]
      rw [e1, e2, heq]
    | succ t =>
      refine EventuallyEq.of_eq ?_
      congr 1
      funext ω
      simp only [Pi.div_apply, osPrice, osTarget]
      rw [div_self (hd ω).ne', div_self (hx0 ω).ne']
  · refine Eventually.of_forall fun ω => ?_
    have hK := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const
      (|bbar + θ * d0| + |bbar + θ * d|)
    rw [zero_mul] at hK
    refine squeeze_zero_norm (fun T => ?_) hK
    have hc : S.E t (osDebt bbar θ d0 d (t + T)) = osDebt bbar θ d0 d (t + T) := by
      cases h : t + T with
      | zero => exact S.E_const t _
      | succ n => exact S.E_const t _
    rw [hc, Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 T)]
    exact mul_le_mul_of_nonneg_left (hbK _ ω) (pow_pos hβ0 T).le
  · cases t with
    | zero =>
      change Integrable (fun _ => 1 / (p0 + d0 - β * d)) S.μ
      exact integrable_const _
    | succ t => exact hyi

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**existence with news when the infimum is an atom**): on
the one-shot system, let the date-1 target value `x` attain its infimum `x_min > 0` with positive
probability (as on every finite tree). Then an equilibrium with prices bounded above and initial
debt `b̄ + θ d₀` exists **iff** `d₀ + p₀ + β x_min/(1 − β) > 0` — iff the realised present value
of the target plus `d₀` is positive on every path. (`NoExist.oneShot_no_eqm`: without the atom
this positivity, even bounded away from zero, is not sufficient.) -/
theorem oneShot_exists_iff_atom (Pm : ProbabilityMeasure Ω) {β θ bbar d0 p0 xmin Ms : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0) {x : Ω → ℝ} (hx : Measurable x) (hxmin : 0 < xmin)
    (hxb : ∀ ω, xmin ≤ x ω ∧ x ω ≤ Ms) (hatom : (oneShot Pm).μ {ω | x ω = xmin} ≠ 0)
    (hp0 : 0 < p0) :
    (∃ (P b : ℕ → Ω → ℝ) (M : ℝ), RuleEqm (oneShot Pm) β θ bbar (osTarget p0 x) P b ∧
      (∀ t ω, P t ω ≤ M) ∧ (∀ t, Integrable (fun ω => 1 / P t ω) (oneShot Pm).μ) ∧
      ∀ ω, b 0 ω = bbar + θ * d0) ↔ 0 < d0 + p0 + β * xmin / (1 - β) := by
  set S := oneShot Pm with hS
  have h1β : 0 < 1 - β := by linarith
  have hx0 : ∀ ω, 0 < x ω := fun ω => hxmin.trans_le (hxb ω).1
  have hAm : MeasurableSet {ω | x ω = xmin} := measurableSet_eq_fun hx measurable_const
  constructor
  · -- necessity
    rintro ⟨P, b, M, hE, hPM, hq, hb0⟩
    obtain ⟨d, hpos, hP0, -, -⟩ := oneShot_eqm_form Pm hβ0 hβ1 hθ hx hxmin hxb hp0 hE hPM hq hb0
    obtain ⟨ω, hωA, hω⟩ : ∃ ω, x ω = xmin ∧ 0 < x ω + (1 - β) * d := by
      by_contra hc
      push Not at hc
      exact hatom (measure_mono_null (fun ω hω => not_lt.2 (hc ω hω)) (ae_iff.1 hpos))
    rw [hωA] at hω
    have h1 := hE.1 0 ω
    rw [hP0 ω] at h1
    have h2 : -(β * d) < β * xmin / (1 - β) := by
      rw [lt_div_iff₀ h1β]
      nlinarith
    linarith
  · -- sufficiency: an intermediate-value argument in the scalar `d`
    intro hcond
    set dlo : ℝ := -(xmin / (1 - β)) with hdlo
    set dhi : ℝ := (p0 + d0) / β with hdhi
    have hlohi : dlo < dhi := by
      have e : (d0 + p0 + β * xmin / (1 - β)) / β = (p0 + d0) / β + xmin / (1 - β) := by
        field_simp
        ring
      have := div_pos hcond hβ0
      rw [e] at this
      rw [hdlo, hdhi]
      linarith
    set gap : ℝ := (dhi - dlo) / 2 with hgap
    have hgap0 : 0 < gap := by rw [hgap]; linarith
    have hxi : Integrable (fun ω => 1 / x ω) S.μ :=
      Integrable.of_bound (hx.const_div 1).aestronglyMeasurable (1 / xmin)
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (hx0 ω))]
          exact one_div_le_one_div_of_le hxmin (hxb ω).1)
    set γ : ℝ := p0 * ∫ ω, 1 / x ω ∂S.μ with hγ
    have hne : Nonempty Ω := by
      by_contra hΩ
      rw [not_nonempty_iff] at hΩ
      have h1 : S.μ Set.univ = 1 := measure_univ
      rw [Set.univ_eq_empty_iff.2 hΩ, measure_empty] at h1
      exact zero_ne_one h1
    have hMs : 0 < Ms := (hx0 (Classical.arbitrary Ω)).trans_le (hxb _).2
    have hγ0 : 0 < γ := by
      have h := integral_mono (integrable_const (1 / Ms)) hxi (fun ω =>
        one_div_le_one_div_of_le (hx0 ω) (hxb ω).2)
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
      exact mul_pos hp0 ((one_div_pos.2 hMs).trans_le h)
    set w : ℝ := S.μ.real {ω | x ω = xmin} with hw
    have hw0 : 0 < w := by
      rw [hw, measureReal_def]
      exact ENNReal.toReal_pos hatom (measure_ne_top _ _)
    -- `h(d) = (p₀ + d₀ − β d) E[1/(x + (1 − β) d)]`
    set I : ℝ → ℝ := fun d => ∫ ω, 1 / (x ω + (1 - β) * d) ∂S.μ with hI
    set h : ℝ → ℝ := fun d => (p0 + d0 - β * d) * I d with hh
    have hden : ∀ d ω, dlo < d → (1 - β) * (d - dlo) ≤ x ω + (1 - β) * d := fun d ω _ => by
      rw [hdlo]
      have := (hxb ω).1
      have e : (1 - β) * (xmin / (1 - β)) = xmin := by field_simp
      nlinarith
    have hIint : ∀ d, dlo < d → Integrable (fun ω => 1 / (x ω + (1 - β) * d)) S.μ := fun d hd =>
      Integrable.of_bound ((hx.add_const _).const_div 1).aestronglyMeasurable
        (1 / ((1 - β) * (d - dlo))) (Eventually.of_forall fun ω => by
          have h1 := hden d ω hd
          have h2 : 0 < (1 - β) * (d - dlo) := mul_pos h1β (by linarith)
          rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (h2.trans_le h1))]
          exact one_div_le_one_div_of_le h2 h1)
    -- near `dlo`, `h` is large (the atom at the infimum)
    set η1 : ℝ := min ((β * gap * w) / ((1 - β) * γ)) gap with hη1
    have hη10 : 0 < η1 := lt_min (by positivity) hgap0
    set d1 : ℝ := dlo + η1 with hd1
    have hd1lo : dlo < d1 := by rw [hd1]; linarith
    have hh1 : γ ≤ h d1 := by
      have hlow : w * (1 / ((1 - β) * η1)) ≤ I d1 := by
        have hA : ∫ ω in {ω | x ω = xmin}, 1 / (x ω + (1 - β) * d1) ∂S.μ =
            w * (1 / ((1 - β) * η1)) := by
          rw [setIntegral_congr_fun hAm (g := fun _ => 1 / ((1 - β) * η1)) (fun ω hω => by
            simp only [Set.mem_ofPred_eq] at hω
            simp only [hω, hd1, hdlo]
            congr 1
            field_simp
            ring), setIntegral_const, smul_eq_mul]
        rw [← hA]
        exact setIntegral_le_integral (hIint d1 hd1lo)
          (Eventually.of_forall fun ω => (one_div_pos.2 (by
            have := hden d1 ω hd1lo
            have : 0 < (1 - β) * (d1 - dlo) := mul_pos h1β (by linarith)
            linarith)).le)
      have hP : β * gap ≤ p0 + d0 - β * d1 := by
        have hmin := min_le_right ((β * gap * w) / ((1 - β) * γ)) gap
        have : d1 ≤ dlo + gap := by rw [hd1]; linarith
        have e : p0 + d0 = β * dhi := by rw [hdhi]; field_simp
        rw [hgap] at this ⊢
        nlinarith
      have hη1le : η1 ≤ (β * gap * w) / ((1 - β) * γ) := min_le_left _ _
      have hkey : γ ≤ β * gap * (w * (1 / ((1 - β) * η1))) := by
        rw [le_div_iff₀ (by positivity)] at hη1le
        rw [mul_one_div, ← mul_div_assoc, le_div_iff₀ (by positivity)]
        nlinarith
      calc γ ≤ β * gap * (w * (1 / ((1 - β) * η1))) := hkey
        _ ≤ (p0 + d0 - β * d1) * I d1 :=
            mul_le_mul hP hlow (by positivity) (by nlinarith)
    -- near `dhi`, `h` is small
    set η2 : ℝ := min (γ * ((1 - β) * gap) / (2 * β)) gap with hη2
    have hη20 : 0 < η2 := lt_min (by positivity) hgap0
    set d2 : ℝ := dhi - η2 with hd2
    have hd2lo : dlo < d2 := by
      rw [hd2]
      have := min_le_right (γ * ((1 - β) * gap) / (2 * β)) gap
      rw [hgap] at this
      linarith
    have hd12 : d1 ≤ d2 := by
      rw [hd1, hd2]
      have := min_le_right ((β * gap * w) / ((1 - β) * γ)) gap
      have := min_le_right (γ * ((1 - β) * gap) / (2 * β)) gap
      rw [hgap] at *
      linarith
    have hh2 : h d2 ≤ γ := by
      have hI2 : I d2 ≤ 1 / ((1 - β) * gap) := by
        have hb : (1 - β) * gap ≤ (1 - β) * (d2 - dlo) := by
          refine mul_le_mul_of_nonneg_left ?_ h1β.le
          rw [hd2]
          have := min_le_right (γ * ((1 - β) * gap) / (2 * β)) gap
          rw [hgap] at this ⊢
          linarith
        have h := integral_mono (hIint d2 hd2lo) (integrable_const (1 / ((1 - β) * gap)))
          (fun ω => one_div_le_one_div_of_le (by positivity) (hb.trans (hden d2 ω hd2lo)))
        rw [integral_const, probReal_univ, one_smul] at h
        exact h
      have hI20 : 0 ≤ I d2 := integral_nonneg fun ω => (one_div_pos.2 (by
        have := hden d2 ω hd2lo
        have : 0 < (1 - β) * (d2 - dlo) := mul_pos h1β (by linarith)
        linarith)).le
      have hP2 : p0 + d0 - β * d2 = β * η2 := by
        rw [hd2, hdhi]
        field_simp
        ring
      have hη2le : η2 ≤ γ * ((1 - β) * gap) / (2 * β) := min_le_left _ _
      change (p0 + d0 - β * d2) * I d2 ≤ γ
      rw [hP2]
      calc β * η2 * I d2 ≤ β * η2 * (1 / ((1 - β) * gap)) :=
            mul_le_mul_of_nonneg_left hI2 (by positivity)
        _ ≤ γ := by
            rw [le_div_iff₀ (by positivity)] at hη2le
            rw [mul_one_div, div_le_iff₀ (by positivity)]
            nlinarith
    -- continuity on `[d1, d2]` and the intermediate value theorem
    have hcont : ContinuousOn h (Set.Icc d1 d2) := by
      have hIc : ContinuousOn I (Set.Icc d1 d2) := by
        refine continuousOn_of_dominated (bound := fun _ => 1 / ((1 - β) * η1))
          (fun d _ => ((hx.add_const _).const_div 1).aestronglyMeasurable)
          (fun d hd => Eventually.of_forall fun ω => ?_) (integrable_const _)
          (Eventually.of_forall fun ω => ?_)
        · have h1 := hden d ω (hd1lo.trans_le hd.1)
          have h2 : (1 - β) * η1 ≤ (1 - β) * (d - dlo) :=
            mul_le_mul_of_nonneg_left (by rw [hd1] at hd; linarith [hd.1]) h1β.le
          have h3 : 0 < (1 - β) * η1 := by positivity
          rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (h3.trans_le (h2.trans h1)))]
          exact one_div_le_one_div_of_le h3 (h2.trans h1)
        · refine ContinuousOn.div continuousOn_const (by fun_prop) fun d hd => ?_
          have h1 := hden d ω (hd1lo.trans_le hd.1)
          have : 0 < (1 - β) * (d - dlo) := mul_pos h1β (by linarith [hd.1])
          linarith
      exact (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).mul hIc
    obtain ⟨d, hdI, hdeq⟩ := intermediate_value_Icc' hd12 hcont ⟨hh2, hh1⟩
    have hdlo' : dlo < d := hd1lo.trans_le hdI.1
    have hdhi' : d < dhi := by
      have := hdI.2
      rw [hd2] at this
      linarith
    have hpos : ∀ ω, 0 < x ω + (1 - β) * d := fun ω => by
      have h1 := hden d ω hdlo'
      have : 0 < (1 - β) * (d - dlo) := mul_pos h1β (by linarith)
      linarith
    have hP0 : 0 < p0 + d0 - β * d := by
      have e : p0 + d0 = β * dhi := by rw [hdhi]; field_simp
      nlinarith
    obtain ⟨hE, hb0, hM, hq⟩ := oneShot_eqm_exists Pm (θ := θ) (bbar := bbar) hβ0 hβ1 hx hxmin
      hxb hp0 hpos hP0 hdeq
    exact ⟨_, _, _, hE, hM, hq, hb0⟩

namespace NoExist

/-- Cochrane (2023), §9.3.2, p. 267 (nonexistence example): the weights `π_k = 3 · 4^{−(k+1)}`. -/
noncomputable def wts (k : ℕ) : ℝ := 3 * (1 / 4) ^ (k + 1)

/-- Cochrane (2023), §9.3.2, p. 267 (nonexistence example): the weights are positive. -/
theorem wts_pos (k : ℕ) : 0 < wts k := by unfold wts; positivity

/-- Cochrane (2023), §9.3.2, p. 267 (nonexistence example): the weights sum to one. -/
theorem hasSum_wts : HasSum wts 1 := by
  have h := (hasSum_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)).mul_left
    (3 / 4)
  convert h using 1
  · funext k
    simp only [wts, pow_succ]
    ring
  · norm_num

/-- Cochrane (2023), §9.3.2, p. 267 (nonexistence example): the law `∑ π_k δ_k` on `ℕ`. -/
noncomputable def wMeasure : Measure ℕ :=
  Measure.sum fun k => ENNReal.ofReal (wts k) • Measure.dirac k

/-- Cochrane (2023), §9.3.2, p. 267 (nonexistence example): `P({k}) = π_k`. -/
theorem wMeasure_singleton (j : ℕ) : wMeasure {j} = ENNReal.ofReal (wts j) := by
  rw [wMeasure, Measure.sum_apply _ (MeasurableSet.of_discrete)]
  rw [tsum_eq_single j (fun k hk => by simp [hk])]
  simp

/-- Cochrane (2023), §9.3.2, p. 267 (nonexistence example): the law is a probability measure. -/
theorem wMeasure_univ : wMeasure Set.univ = 1 := by
  rw [wMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (wts_pos k).le) hasSum_wts.summable,
    hasSum_wts.tsum_eq, ENNReal.ofReal_one]

/-- Cochrane (2023), §9.3.2, p. 267 (nonexistence example): the law as a probability measure. -/
noncomputable def wProb : ProbabilityMeasure ℕ := ⟨wMeasure, ⟨wMeasure_univ⟩⟩

/-- Cochrane (2023), §9.3.2, p. 267 (nonexistence example): the date-1 target value
`x_k = 1 + 2^{−(k+1)}` — its infimum `1` is not attained. -/
noncomputable def xC (k : ℕ) : ℝ := 1 + (1 / 2) ^ (k + 1)

/-- Cochrane (2023), §9.3.2, p. 267 (nonexistence example): `E[2^{k+1}] = 3` — the inverse distance
of `x` to its infimum is integrable. -/
theorem integral_pow2 : Integrable (fun k : ℕ => (2 : ℝ) ^ (k + 1)) wMeasure ∧
    ∫ k, (2 : ℝ) ^ (k + 1) ∂wMeasure = 3 := by
  have hw : ∀ k : ℕ, wts k * (2 : ℝ) ^ (k + 1) = 3 * (1 / 2) ^ (k + 1) := fun k => by
    simp only [wts]
    rw [mul_assoc, ← mul_pow]
    norm_num
  have hs : HasSum (fun k : ℕ => wts k * (2 : ℝ) ^ (k + 1)) 3 := by
    have h := (hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (3 / 2)
    convert h using 1
    · funext k
      rw [hw k, pow_succ]
      ring
    · norm_num
  have hfi : Integrable (fun k : ℕ => (2 : ℝ) ^ (k + 1)) wMeasure := by
    refine ⟨Measurable.of_discrete.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, wMeasure, lintegral_sum_measure]
    simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    have e : ∀ k : ℕ, ENNReal.ofReal (wts k) * ‖(2 : ℝ) ^ (k + 1)‖ₑ =
        ENNReal.ofReal (wts k * (2 : ℝ) ^ (k + 1)) := fun k => by
      rw [ENNReal.ofReal_mul (wts_pos k).le, ← ofReal_norm, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
    simp_rw [e]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (mul_pos (wts_pos k) (by positivity)).le)
      hs.summable]
    exact ENNReal.ofReal_lt_top
  refine ⟨hfi, ?_⟩
  rw [integral_countable hfi]
  have e : ∀ k : ℕ, wMeasure.real {k} • (2 : ℝ) ^ (k + 1) = wts k * (2 : ℝ) ^ (k + 1) := fun k => by
    rw [measureReal_def, wMeasure_singleton, ENNReal.toReal_ofReal (wts_pos k).le, smul_eq_mul]
  simp_rw [e]
  exact hs.tsum_eq

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**existence can fail with news and `b₀ ≠ b̄`**): on the
genuine probability space `(ℕ, ∑ π_k δ_k)` with one-shot information, take the target
`P*_0 = 1`, `P*_t = x_k = 1 + 2^{−(k+1)}` (`t ≥ 1`) and initial debt `b₀ = b̄ + θ d₀`,
`d₀ = 1/10 − 1 − β/(1 − β)`. The realised present value of the target plus `d₀` is at least `1/10`
on every path (`∑ⱼ βʲ P*_j = 1 + β x_k/(1 − β)`), so a positive price path with that present value
is not excluded by the valuation equation; yet **no equilibrium with prices bounded above
exists**. The infimum of `x` is not attained and `E[1/(x − inf x)] < ∞`, so the interest-rate
target at date `0` cannot be met. (With an atom at the infimum, as on any finite tree, this
obstruction disappears.) -/
theorem oneShot_no_eqm {β θ bbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0) :
    (∀ k, HasSum (fun j => β ^ j * osTarget 1 xC j k) (1 + β * xC k / (1 - β))) ∧
      (∀ k, 1 / 10 ≤ (1 / 10 - 1 - β / (1 - β)) + (1 + β * xC k / (1 - β))) ∧
      ¬ ∃ (P b : ℕ → ℕ → ℝ) (M : ℝ), RuleEqm (oneShot wProb) β θ bbar (osTarget 1 xC) P b ∧
        (∀ t k, P t k ≤ M) ∧ (∀ t, Integrable (fun k => 1 / P t k) (oneShot wProb).μ) ∧
        ∀ k, b 0 k = bbar + θ * (1 / 10 - 1 - β / (1 - β)) := by
  have h1β : 0 < 1 - β := by linarith
  have hxb : ∀ k, (1 : ℝ) ≤ xC k ∧ xC k ≤ 3 / 2 := fun k => by
    have h1 : (0 : ℝ) < (1 / 2) ^ (k + 1) := by positivity
    have h2 : ((1 : ℝ) / 2) ^ (k + 1) ≤ (1 / 2) ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    simp only [xC]
    constructor <;> linarith [show ((1 : ℝ) / 2) ^ 1 = 1 / 2 by norm_num]
  refine ⟨fun k => ?_, fun k => ?_, ?_⟩
  · rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, osTarget, one_mul]
    have h := (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_left (β * xC k)
    convert h using 1
    · funext j
      rw [pow_succ]
      ring
    · field_simp
      ring
  · have : β / (1 - β) ≤ β * xC k / (1 - β) :=
      div_le_div_of_nonneg_right (by nlinarith [(hxb k).1]) h1β.le
    linarith
  rintro ⟨P, b, M, hE, hPM, hq, hb0⟩
  obtain ⟨d, hpos, hP0, -, heq⟩ := oneShot_eqm_form wProb hβ0 hβ1 hθ (x := xC)
    Measurable.of_discrete one_pos hxb one_pos hE hPM hq hb0
  have hμ : (oneShot wProb).μ = wMeasure := rfl
  -- full support: the a.e. positivity holds at every state
  have hall : ∀ k, 0 < xC k + (1 - β) * d := fun k => by
    by_contra h
    have h0 := ae_iff.1 hpos
    have hk : wMeasure {k} = 0 := by
      rw [hμ] at h0
      exact measure_mono_null (fun j hj => by rw [Set.mem_singleton_iff.1 hj]; exact h) h0
    rw [wMeasure_singleton, ENNReal.ofReal_eq_zero] at hk
    exact absurd hk (not_le.2 (wts_pos k))
  -- hence `1 + (1 − β) d ≥ 0`
  have hd1 : 0 ≤ 1 + (1 - β) * d := by
    by_contra h
    push Not at h
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < -(1 + (1 - β) * d) by linarith)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    have h2 : ((1 : ℝ) / 2) ^ (k + 1) ≤ (1 / 2) ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have := hall k
    simp only [xC] at this
    linarith
  -- bounds on the two expectations
  have hI : ∫ k, 1 / (xC k + (1 - β) * d) ∂(oneShot wProb).μ ≤ 3 := by
    rw [hμ, ← integral_pow2.2]
    refine integral_mono_of_nonneg (Eventually.of_forall fun k => (one_div_pos.2 (hall k)).le)
      integral_pow2.1 (Eventually.of_forall fun k => ?_)
    have hu : (1 / 2 : ℝ) ^ (k + 1) ≤ xC k + (1 - β) * d := by simp only [xC]; linarith
    calc 1 / (xC k + (1 - β) * d) ≤ 1 / (1 / 2 : ℝ) ^ (k + 1) :=
          one_div_le_one_div_of_le (by positivity) hu
      _ = (2 : ℝ) ^ (k + 1) := by rw [one_div_pow, one_div_one_div]
  have hI0 : 0 ≤ ∫ k, 1 / (xC k + (1 - β) * d) ∂(oneShot wProb).μ :=
    integral_nonneg fun k => (one_div_pos.2 (hall k)).le
  have hJ : 2 / 3 ≤ ∫ k, 1 / xC k ∂(oneShot wProb).μ := by
    have hint : Integrable (fun k => 1 / xC k) (oneShot wProb).μ :=
      Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable 1
        (Eventually.of_forall fun k => by
          rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (by linarith [(hxb k).1]))]
          exact (div_le_one (by linarith [(hxb k).1])).2 (hxb k).1)
    have h := integral_mono (integrable_const (2 / 3 : ℝ)) hint (fun k => by
      rw [le_div_iff₀ (by linarith [(hxb k).1])]
      linarith [(hxb k).2])
    simpa using h
  -- the price at date `0`
  have hP0pos : 0 < 1 + (1 / 10 - 1 - β / (1 - β)) - β * d := by
    rw [← hP0 0]
    exact hE.1 0 0
  have hP0le : 1 + (1 / 10 - 1 - β / (1 - β)) - β * d ≤ 1 / 10 := by
    have : -(β * d) ≤ β / (1 - β) := by
      rw [le_div_iff₀ h1β]
      nlinarith
    linarith
  nlinarith [mul_le_mul hP0le hI hI0 (by norm_num : (0 : ℝ) ≤ 1 / 10)]

end NoExist

end Cochrane.AssetsRulesBalanceSheets.FiscalRulesTargetClose

