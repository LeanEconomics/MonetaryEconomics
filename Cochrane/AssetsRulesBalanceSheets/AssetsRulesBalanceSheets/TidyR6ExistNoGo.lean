/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.TidyR5ExistSet

/-!
# Theorem FR (d): existence is not a function of the target's realised present value

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.3.2,
eqs. (9.8)–(9.12), pp. 266–267 (Theorem FR; stochastic target `P*`, `b₀ = b̄ + θ d₀ ≠ b̄`).

The exact existence condition for an equilibrium with prices bounded above is the implicit one of
`FiscalRulesTargetFinal.exists_iff_pathwise`. The natural explicit candidate is a condition on the
realised present value of the target, `PV*(ω) = ∑ₛ βˢ P*_s(ω)`: the necessary condition
`d₀ + PV*(ω) > 0` a.e. (`FiscalRulesTargetFinal.exists_imp_pos`) is of this kind, and it is exact
when `PV*` is predetermined (`FiscalRulesTargetFinal.predetermined_exists_iff`) and, in the
one-shot class, when the target's infimum is an atom
(`FiscalRulesTargetClose.oneShot_exists_iff_atom`).

This module settles the question in general.

## Main results

* `pv_tgtS`, `pv_osTarget`: on the same probability space `(ℕ, ∑ p(1 − p)ᵏ δ_k)`, the
  settle-or-continue target `tgtS σ` (news at every date) and the one-shot target
  `osTarget 1 (xOS σ β)` with `xOS σ β k = 1 + (σ − 1) βᵏ` (all news at date `1`) have the **same
  realised present value in every state**, `PV*(k) = (1 + (σ − 1) β^{k+1})/(1 − β)`, the same date-0
  value `1` and the same bounds `1 ≤ P* ≤ σ`.
* `oneShot_exists_pos`: on the one-shot system an equilibrium with prices bounded above exists for
  the explicit `d₀ = E[1/x]/E[1/(x + 1 − β)] − (1 − β) ≥ β > 0`, while on the settle-or-continue
  system none exists for any `d₀ > 0` (`TidyR5NoExist.no_eqm_pos`).
* `no_condition_on_pv` (**the no-go theorem**): there is no condition `C(μ, PV*, d₀)` on the
  probability measure, the realised present value of the target and `d₀` that characterises
  existence on every system: any such condition — on the law of `PV*`, its essential infimum or
  supremum, its moments — gives the same answer for the two targets above but the existence sets
  differ. Existence depends on the information structure (when the news in `PV*` arrives), which is
  exactly what `FiscalRulesTargetFinal.exists_iff_pathwise` encodes.
* `lower_bound_sharp` (**the sharpest positive statement in terms of `inf PV*`**): the necessary
  condition `d₀ > −PV*(ω)` a.e. cannot be improved as a lower bound depending on the infimum of the
  realised present value alone: on the settle-or-continue system `inf_k PV*(k) = 1/(1 − β)` and the
  existence set is `(−1/(1 − β), 0]`, whose infimum is exactly `−inf PV*`.
-/

namespace Cochrane.AssetsRulesBalanceSheets.TidyR6ExistNoGo

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure FiscalRulesMeasure FiscalRulesTargetClose FiscalRulesTargetFinal
open TidyR5NoExist TidyR5ExistSet

/-- Cochrane (2023), §9.3.2, p. 267: the realised present value of the settle-or-continue target
in the state "settles at `k + 1`", `(1 + (σ − 1) β^{k+1})/(1 − β)`. -/
noncomputable def pvS (σ β : ℝ) (k : ℕ) : ℝ := (1 + (σ - 1) * β ^ (k + 1)) / (1 - β)

/-- Cochrane (2023), §9.3.2, p. 267: the one-shot target level revealed at date `1`,
`x_k = 1 + (σ − 1) βᵏ`, chosen so that the one-shot target has the same realised present value
as the settle-or-continue target. -/
noncomputable def xOS (σ β : ℝ) (k : ℕ) : ℝ := 1 + (σ - 1) * β ^ k

/-- Cochrane (2023), §9.3.2, p. 267: `1 ≤ x_k ≤ σ` for `σ ≥ 1`, `0 < β < 1`. -/
theorem xOS_bounds {σ β : ℝ} (hσ : 1 ≤ σ) (hβ0 : 0 < β) (hβ1 : β < 1) (k : ℕ) :
    1 ≤ xOS σ β k ∧ xOS σ β k ≤ σ := by
  have h1 : 0 ≤ β ^ k := pow_nonneg hβ0.le k
  have h2 : β ^ k ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
  unfold xOS
  constructor <;> nlinarith

/-- Cochrane (2023), eq. (9.9), p. 266: the realised present value of the settle-or-continue
target in state `k` is `pvS σ β k`. -/
theorem pv_tgtS {σ β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (k : ℕ) :
    HasSum (fun s => β ^ s * tgtS σ s k) (pvS σ β k) := by
  have h1β : (1 : ℝ) - β ≠ 0 := by linarith
  have hg := hasSum_geometric_of_lt_one hβ0.le hβ1
  have htail : HasSum (fun s => (σ - 1) * (if k < s then β ^ s else 0))
      ((σ - 1) * (β ^ (k + 1) * (1 - β)⁻¹)) := by
    refine HasSum.mul_left _ ?_
    rw [← hasSum_nat_add_iff' (k + 1)]
    have e : ∑ i ∈ Finset.range (k + 1), (if k < i then β ^ i else 0) = 0 :=
      Finset.sum_eq_zero fun i hi => by
        have : ¬ k < i := by have := Finset.mem_range.1 hi; omega
        simp [this]
    rw [e, sub_zero]
    have : (fun n => if k < n + (k + 1) then β ^ (n + (k + 1)) else 0) =
        fun n => β ^ (k + 1) * β ^ n := by
      funext n
      have : k < n + (k + 1) := by omega
      simp only [this, ↓reduceIte]
      ring
    rw [this]
    exact hg.mul_left _
  have hsum := hg.add htail
  convert hsum using 1
  · funext s
    unfold tgtS
    by_cases hs : s ≤ k
    · have : ¬ k < s := by omega
      simp [hs, this]
    · have : k < s := by omega
      simp only [hs, ↓reduceIte, this]
      ring
  · unfold pvS
    field_simp

/-- Cochrane (2023), eq. (9.9), p. 266: the realised present value of the one-shot target
`osTarget 1 (xOS σ β)` in state `k` is the same `pvS σ β k`. -/
theorem pv_osTarget {σ β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (k : ℕ) :
    HasSum (fun s => β ^ s * osTarget 1 (xOS σ β) s k) (pvS σ β k) := by
  have h1β : (1 : ℝ) - β ≠ 0 := by linarith
  have hg := hasSum_geometric_of_lt_one hβ0.le hβ1
  rw [← hasSum_nat_add_iff' 1]
  have e : (fun n => β ^ (n + 1) * osTarget 1 (xOS σ β) (n + 1) k) =
      fun n => (β * xOS σ β k) * β ^ n := by
    funext n
    simp only [osTarget]
    ring
  rw [e]
  convert hg.mul_left (β * xOS σ β k) using 1
  simp only [Finset.sum_range_one, pow_zero, osTarget, one_mul]
  unfold pvS xOS
  field_simp
  ring

/-- Cochrane (2023), §9.3.2, p. 267: both targets start at `P*_0 = 1`. -/
theorem targets_at_zero (σ β : ℝ) (k : ℕ) :
    tgtS σ 0 k = 1 ∧ osTarget 1 (xOS σ β) 0 k = 1 := by
  simp [tgtS, osTarget]

/-- Cochrane (2023), §9.3.2, p. 267: the settlement-date law as a probability measure on `ℕ`. -/
noncomputable def gProb {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : ProbabilityMeasure ℕ :=
  ⟨gMeasure p, ⟨gMeasure_univ hp0 hp1⟩⟩

/-- Cochrane (2023), §9.3.2, p. 267: the one-shot system and the settle-or-continue system live on
the same probability space `(ℕ, gMeasure p)`. -/
theorem same_measure {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (oneShot (gProb hp0 hp1)).μ = gMeasure p ∧ (gSys hp0 hp1).μ = gMeasure p :=
  ⟨rfl, rfl⟩

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**existence for a positive `d₀` with one-shot news**):
on the one-shot system over `(ℕ, gMeasure p)` with target `osTarget 1 (xOS σ β)`, an equilibrium
with prices bounded above and `b₀ = b̄ + θ d₀` exists for
`d₀ = E[1/x]/E[1/(x + 1 − β)] − (1 − β)`, and this `d₀` is at least `β > 0`. -/
theorem oneShot_exists_pos {p β θ bbar σ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ : θ ≠ 0) (hσ : 1 < σ) :
    ∃ d0 : ℝ, β ≤ d0 ∧
      ExistsAbove (oneShot (gProb hp0 hp1)) β θ bbar (osTarget 1 (xOS σ β)) d0 := by
  set Pm := gProb hp0 hp1 with hPm
  set μ := (oneShot Pm).μ with hμ
  have hprob : IsProbabilityMeasure μ := ⟨gMeasure_univ hp0 hp1⟩
  have h1β : 0 < 1 - β := by linarith
  set x := xOS σ β with hxdef
  have hxb := xOS_bounds hσ.le hβ0 hβ1
  have hx0 : ∀ k, 0 < x k := fun k => one_pos.trans_le (hxb k).1
  have hxm : Measurable x := measurable_of_countable x
  have hint : ∀ c : ℝ, 0 ≤ c → Integrable (fun k => 1 / (x k + c)) μ := fun c hc =>
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
      (Eventually.of_forall fun k => by
        rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (by linarith [hx0 k]))]
        rw [div_le_one (by linarith [hx0 k])]
        linarith [(hxb k).1])
  set E1 := ∫ k, 1 / x k ∂μ with hE1
  set E2 := ∫ k, 1 / (x k + (1 - β) * 1) ∂μ with hE2
  have hE2pos : 1 / (σ + 1) ≤ E2 := by
    have h := integral_mono (integrable_const (1 / (σ + 1))) (hint ((1 - β) * 1) (by linarith))
      (fun k => by
        simp only
        rw [div_le_div_iff₀ (by linarith) (by linarith [hx0 k])]
        linarith [(hxb k).2])
    rw [integral_const, probReal_univ, one_smul] at h
    exact h
  have hE2p : 0 < E2 := (by positivity : (0 : ℝ) < 1 / (σ + 1)).trans_le hE2pos
  have hE12 : E2 ≤ E1 := by
    have hint0 : Integrable (fun k => 1 / x k) μ :=
      (hint 0 le_rfl).congr (ae_of_all _ fun k => by simp only [add_zero])
    have hle : ∀ k, 1 / (x k + (1 - β) * 1) ≤ 1 / x k := fun k =>
      div_le_div_of_nonneg_left zero_le_one (hx0 k) (by linarith)
    exact integral_mono (hint ((1 - β) * 1) (by linarith)) hint0 hle
  refine ⟨E1 / E2 - (1 - β), ?_, ?_⟩
  · have : 1 ≤ E1 / E2 := (one_le_div hE2p).2 hE12
    linarith
  · have hiff := oneShot_exists_iff Pm hβ0 hβ1 hθ (bbar := bbar) (d0 := E1 / E2 - (1 - β))
      (p0 := 1) hxm one_pos (fun k => ⟨(hxb k).1, (hxb k).2⟩) one_pos
    refine hiff.2 ⟨1, Eventually.of_forall fun k => by linarith [hx0 k], ?_, hint _ (by linarith),
      ?_⟩
    · have : 0 < E1 / E2 := div_pos (hE2p.trans_le hE12) hE2p
      linarith
    · have e : (1 : ℝ) + (E1 / E2 - (1 - β)) - β * 1 = E1 / E2 := by ring
      rw [e, one_mul, ← hE2, div_mul_cancel₀ _ hE2p.ne']

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**the two systems disagree**): for every `0 < p < 1`,
`0 < β < 1`, `σ > 1`, `θ ≠ 0`, `b̄` there is `d₀ > 0` for which an equilibrium with prices bounded
above exists with the one-shot target and none exists with the settle-or-continue target, although
both targets have the same realised present value in every state of the same probability space. -/
theorem existence_differs {p β θ bbar σ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ : θ ≠ 0) (hσ : 1 < σ) :
    ∃ d0 : ℝ, 0 < d0 ∧
      ExistsAbove (oneShot (gProb hp0 hp1)) β θ bbar (osTarget 1 (xOS σ β)) d0 ∧
      ¬ ExistsAbove (gSys hp0 hp1) β θ bbar (tgtS σ) d0 := by
  obtain ⟨d0, hd0, hex⟩ := oneShot_exists_pos hp0 hp1 hβ0 hβ1 hθ (bbar := bbar) hσ
  refine ⟨d0, hβ0.trans_le hd0, hex, fun h => ?_⟩
  have := ((existsAbove_iff hp0 hp1 hβ0 hβ1 hθ hσ).1 h).2
  linarith

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**no condition on the realised present value of the
target characterises existence**): there is no condition `C(μ, PV*, d₀)` — on the probability
measure, the realised present value of the target `PV*(ω) = ∑ₛ βˢ P*_s(ω)` and `d₀` — such that,
on both the settle-or-continue system and the one-shot system over `(ℕ, gMeasure p)`, an
equilibrium with prices bounded above and `b₀ = b̄ + θ d₀` exists iff `C(μ, PV*, d₀)`. Both
targets have the same `μ` and the same `PV*` (`pv_tgtS`, `pv_osTarget`), but the existence sets
differ (`existence_differs`). In particular no condition on the law, the essential infimum or
supremum, or the moments of the realised present value can work. -/
theorem no_condition_on_pv {p β θ bbar σ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ : θ ≠ 0) (hσ : 1 < σ) :
    ¬ ∃ C : Measure ℕ → (ℕ → ℝ) → ℝ → Prop,
      (∀ d0, ExistsAbove (gSys hp0 hp1) β θ bbar (tgtS σ) d0 ↔
        C (gSys hp0 hp1).μ (fun k => ∑' s, β ^ s * tgtS σ s k) d0) ∧
      ∀ d0, ExistsAbove (oneShot (gProb hp0 hp1)) β θ bbar (osTarget 1 (xOS σ β)) d0 ↔
        C (oneShot (gProb hp0 hp1)).μ (fun k => ∑' s, β ^ s * osTarget 1 (xOS σ β) s k) d0 := by
  rintro ⟨C, h1, h2⟩
  obtain ⟨d0, -, hex, hno⟩ := existence_differs hp0 hp1 hβ0 hβ1 hθ (bbar := bbar) hσ
  have epv : (fun k => ∑' s, β ^ s * osTarget 1 (xOS σ β) s k) =
      fun k => ∑' s, β ^ s * tgtS σ s k := by
    funext k
    rw [(pv_osTarget hβ0 hβ1 k).tsum_eq, (pv_tgtS hβ0 hβ1 k).tsum_eq]
  have hC := (h2 d0).1 hex
  rw [epv] at hC
  exact hno ((h1 d0).2 hC)

/-- Cochrane (2023), §9.3.2, p. 267: the infimum over states of the realised present value of the
settle-or-continue target is `1/(1 − β)` (approached as settlement recedes, never attained). -/
theorem pvS_inf {σ β : ℝ} (hσ : 1 < σ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∀ k, 1 / (1 - β) < pvS σ β k) ∧ Tendsto (pvS σ β) atTop (𝓝 (1 / (1 - β))) := by
  have h1β : 0 < 1 - β := by linarith
  constructor
  · intro k
    unfold pvS
    have : 0 < (σ - 1) * β ^ (k + 1) := mul_pos (by linarith) (pow_pos hβ0 _)
    rw [div_lt_div_iff_of_pos_right h1β]
    linarith
  · have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).comp
      (tendsto_add_atTop_nat 1)).const_mul (σ - 1) |>.const_add 1 |>.div_const (1 - β)
    rw [show 1 / (1 - β) = (1 + (σ - 1) * 0) / (1 - β) by ring]
    exact h

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**the necessary lower bound is sharp**): on the
settle-or-continue system the necessary condition `d₀ > −PV*(k)` for every `k` is equivalent to
`d₀ ≥ −1/(1 − β) = −inf PV*`, and the existence set `(−1/(1 − β), 0]` comes arbitrarily close to
this bound: for every `ε > 0` some `d₀ < −inf PV* + ε` admits an equilibrium. So no lower bound
expressed through the infimum of the realised present value improves on `d₀ ≥ −inf PV*`. -/
theorem lower_bound_sharp {p β θ bbar σ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hθ : θ ≠ 0) (hσ : 1 < σ) :
    (∀ d0, (∀ k, 0 < d0 + pvS σ β k) ↔ -(1 / (1 - β)) ≤ d0) ∧
      ∀ ε, 0 < ε → ∃ d0, d0 < -(1 / (1 - β)) + ε ∧
        ExistsAbove (gSys hp0 hp1) β θ bbar (tgtS σ) d0 := by
  obtain ⟨hgt, hlim⟩ := pvS_inf hσ hβ0 hβ1
  have h1β : 0 < 1 - β := by linarith
  refine ⟨fun d0 => ⟨fun h => ?_, fun h k => by linarith [hgt k]⟩, fun ε hε => ?_⟩
  · have hl : Tendsto (fun k => d0 + pvS σ β k) atTop (𝓝 (d0 + 1 / (1 - β))) :=
      hlim.const_add d0
    have := ge_of_tendsto' hl fun k => (h k).le
    linarith
  · have hc : 0 < 1 / (1 - β) := by positivity
    set m := min ε (1 / (1 - β)) with hm
    have hm0 : 0 < m := lt_min hε hc
    have hm1 : m ≤ ε := min_le_left _ _
    have hm2 : m ≤ 1 / (1 - β) := min_le_right _ _
    refine ⟨-(1 / (1 - β)) + m / 2, by linarith,
      (existsAbove_iff hp0 hp1 hβ0 hβ1 hθ hσ).2 ⟨by linarith, by linarith⟩⟩

end Cochrane.AssetsRulesBalanceSheets.TidyR6ExistNoGo
