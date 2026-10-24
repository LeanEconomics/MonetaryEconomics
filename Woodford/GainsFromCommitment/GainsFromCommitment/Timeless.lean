/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.DateZeroCommitment
import GainsFromCommitment.InflationBias
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Optimality from a timeless perspective

Woodford (2003), *Interest and Prices*, Chapter 7, §1.1, pp. 474–476: the definition of a policy
that is optimal from a timeless perspective, Proposition 7.2, and Figure 7.1.

## Definitions

* `IsOptimalGiven` (p. 475): `(π, x)` solves the problem of minimising (1.2) over bounded paths
  satisfying (1.1) for `t ≥ 0`, subject to the additional constraint `π_0 = p₀`.
* `TimelesslyOptimal` (p. 475): a constant inflation target `π̄` is optimal from a timeless
  perspective if that problem with `p₀ = π̄` has a solution with `π_t = π̄` for all `t`.
* `TimelessFromEveryDate` (p. 474, the general definition, deterministic): the evolution from
  *every* date `t₀` onward is optimal subject to the constraint that the initial evolution at `t₀`
  be the one associated with the policy. `timelessFromEveryDate_iff` shows that for a constant
  target this is the same as `TimelesslyOptimal`.

## Main results

* `optimalGiven`, `optimalGiven_unique`: for every `p₀` the constrained problem has the solution
  `π_t = p₀μ₁ᵗ`, `x_t = (κ/λ)μ₁^{t+1}p₀/(1 − μ₁)`, and it is unique (in conditional mean square;
  exactly, under perfect foresight).
* **Proposition 7.2** (`prop_7_2`, `prop_7_2_det`, `prop_7_2_everyDate`): zero inflation is
  optimal from a timeless perspective, and it is the only constant inflation target with this
  property, for every `x*` (under any expectation system with the pull-out property).
* Survey E2 (`bias_pos_iff`, `bias_zero_of_xs_zero`, `printed_E2_false`): the constant inflation
  bias of discretion relative to the timeless policy is positive iff `x* > 0`; it is zero when
  `x* = 0`, so the printed "clearly positive when `x* = 0`" is false.
* Figure 7.1 (`fig_7_1_ordering`, `tendsto_dateZero_inflation`): for `x* > 0`, at every date,
  `0` (timeless) `< π_t` (date-zero optimal) `< πᵉ` (discretion), and `π_t → 0`.
* The zero lower bound remark of p. 469 (`IS`, `is_iff_impliedRate`, `nonneg_iff_hat`): with the
  IS relation (Ch. 4, (1.12), no disturbances) the implied rate is
  `ı̂_t = π_{t+1} + (x_{t+1} − x_t)/σ`, and `i_t ≥ 0` iff `ı̂_t ≥ log β`. Discretion
  (`discretion_rate_nonneg`) and the timeless policy (`timeless_rate_nonneg`) always satisfy it
  for `x* ≥ 0`. The date-zero commitment has `ı̂_t = (1 − μ₁)μ₁^{t+1}x*(λ/κ − 1/σ)`
  (`dateZero_impliedRate`), so `i_t ≥ 0` for all `t` iff
  `log β ≤ (1 − μ₁)μ₁x*(λ/κ − 1/σ)` (`dateZero_rate_nonneg_iff`): it always holds if `λσ ≥ κ`
  (`dateZero_rate_nonneg_of_le`) or `x*` is small enough (`dateZero_rate_nonneg_small`), but the
  book's unqualified claim fails for `λσ < κ` and large `x*` (`dateZero_rate_counterexample`).
-/

namespace Woodford.GainsFromCommitment.Timeless

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), p. 475: `(π, x)` minimises the expected loss (1.2), state by state, among
the bounded adapted paths satisfying (1.1) for all `t ≥ 0` and the additional constraint
`π_0 = p₀`. -/
def IsOptimalGiven (β κ lam xs p₀ : ℝ) (π x : ℕ → Ω → ℝ) : Prop :=
  DateZeroCommitment.Admissible 𝔼 β κ π x ∧ (∀ ω, π 0 ω = p₀) ∧
    ∀ π' x', DateZeroCommitment.Admissible 𝔼 β κ π' x' → (∀ ω, π' 0 ω = p₀) → ∀ ω,
      DateZeroCommitment.loss 𝔼 β lam xs π x ω ≤ DateZeroCommitment.loss 𝔼 β lam xs π' x' ω

/-- Woodford (2003), p. 475 (**optimal from a timeless perspective**): the constant inflation
target `π̄` is optimal from a timeless perspective if the problem of minimising (1.2) subject to
(1.1) for `t ≥ 0` and `π_0 = π̄` has a solution in which `π_t = π̄` for all `t`. -/
def TimelesslyOptimal (β κ lam xs pbar : ℝ) : Prop :=
  ∃ x, IsOptimalGiven 𝔼 β κ lam xs pbar (fun _ _ => pbar) x

/-- Woodford (2003), p. 475: the initial multiplier `φ_{−1} = −(λ/κ)x* + p₀/(1 − μ₁)` of the
problem with the constraint `π_0 = p₀` (it replaces the condition (1.9)). -/
noncomputable def timelessMult (β κ lam xs p₀ : ℝ) : ℝ :=
  -(lam / κ * xs) + p₀ / (1 - SecondOrderRE.mu1 β (κ ^ 2 / lam))

/-- Woodford (2003), p. 475: with this initial multiplier inflation is `π_t = p₀μ₁ᵗ`. -/
theorem inflPath_timeless {β κ lam xs : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam)
    (p₀ : ℝ) (t : ℕ) :
    DateZeroCommitment.inflPath β κ lam xs (timelessMult β κ lam xs p₀) t =
      p₀ * SecondOrderRE.mu1 β (κ ^ 2 / lam) ^ t := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  have h1 := SecondOrderRE.mu1_lt_one hβ hc
  rw [DateZeroCommitment.inflPath_eq, timelessMult]
  have : 1 - SecondOrderRE.mu1 β (κ ^ 2 / lam) ≠ 0 := by linarith
  field_simp
  ring

/-- Woodford (2003), p. 475: with this initial multiplier the output gap is
`x_t = (κ/λ)μ₁^{t+1}p₀/(1 − μ₁)`. -/
theorem gapPath_timeless {β κ lam xs : ℝ} (hκ : 0 < κ) (hlam : 0 < lam)
    (p₀ : ℝ) (t : ℕ) :
    DateZeroCommitment.gapPath β κ lam xs (timelessMult β κ lam xs p₀) t =
      κ / lam * SecondOrderRE.mu1 β (κ ^ 2 / lam) ^ (t + 1) * p₀ /
        (1 - SecondOrderRE.mu1 β (κ ^ 2 / lam)) := by
  rw [DateZeroCommitment.gapPath_eq hκ.ne' hlam.ne', timelessMult]
  ring

/-- **Woodford (2003), p. 475 (the problem with `π_0 = p₀`)**: for every `p₀` the path
`π_t = p₀μ₁ᵗ`, `x_t = (κ/λ)μ₁^{t+1}p₀/(1 − μ₁)` solves the constrained problem. -/
theorem optimalGiven (hpo : 𝔼.PullOut) {β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hlam : 0 < lam) (p₀ : ℝ) :
    IsOptimalGiven 𝔼 β κ lam xs p₀
      (DateZeroCommitment.lift
        (DateZeroCommitment.inflPath β κ lam xs (timelessMult β κ lam xs p₀)))
      (DateZeroCommitment.lift
        (DateZeroCommitment.gapPath β κ lam xs (timelessMult β κ lam xs p₀))) := by
  have h0 : ∀ ω : Ω, DateZeroCommitment.lift
      (DateZeroCommitment.inflPath β κ lam xs (timelessMult β κ lam xs p₀)) 0 ω = p₀ := by
    intro ω
    simp only [DateZeroCommitment.lift, inflPath_timeless hβ0 hκ hlam, pow_zero, mul_one]
  refine ⟨DateZeroCommitment.plan_admissible 𝔼 hβ0 hκ hlam _, h0, fun π x hadm hπ0 ω => ?_⟩
  refine (DateZeroCommitment.plan_optimal 𝔼 hpo hβ0 hβ1 hκ hlam hadm (Or.inr fun ω' => ?_) ω).1
  rw [hπ0 ω']
  exact (h0 ω').symm

/-- Woodford (2003), p. 475 (**uniqueness** for the problem with `π_0 = p₀`): any solution
coincides with `π_t = p₀μ₁ᵗ`, `x_t = (κ/λ)μ₁^{t+1}p₀/(1 − μ₁)` in conditional mean square. -/
theorem optimalGiven_unique (hpo : 𝔼.PullOut) {β κ lam xs p₀ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hlam : 0 < lam) {π x : ℕ → Ω → ℝ} (h : IsOptimalGiven 𝔼 β κ lam xs p₀ π x)
    (ω : Ω) (t : ℕ) :
    𝔼.E 0 (fun ω => (π t ω - p₀ * SecondOrderRE.mu1 β (κ ^ 2 / lam) ^ t) ^ 2) ω = 0 ∧
      𝔼.E 0 (fun ω => (x t ω - κ / lam * SecondOrderRE.mu1 β (κ ^ 2 / lam) ^ (t + 1) * p₀ /
        (1 - SecondOrderRE.mu1 β (κ ^ 2 / lam))) ^ 2) ω = 0 := by
  obtain ⟨hadm, hπ0, hmin⟩ := h
  have hstar := optimalGiven 𝔼 hpo hβ0 hβ1 hκ hlam (xs := xs) p₀
  have hopt := DateZeroCommitment.plan_optimal 𝔼 hpo hβ0 hβ1 hκ hlam hadm
    (Or.inr fun ω' => by rw [hπ0 ω']; exact (hstar.2.1 ω').symm) ω
  have heq := le_antisymm (hmin _ _ hstar.1 hstar.2.1 ω) hopt.1
  have := hopt.2 heq t
  rw [inflPath_timeless hβ0 hκ hlam, gapPath_timeless hκ hlam] at this
  exact this

/-- **Woodford (2003), Proposition 7.2, p. 475**: zero inflation is optimal from a timeless
perspective, and it is the unique constant inflation target with this property; this holds for
every `x*` (it is not necessary for `x*` to be small, p. 475), under any expectation system with
the pull-out property. -/
theorem prop_7_2 [Nonempty Ω] (hpo : 𝔼.PullOut) {β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hlam : 0 < lam) (pbar : ℝ) :
    TimelesslyOptimal 𝔼 β κ lam xs pbar ↔ pbar = 0 := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  have h0 := SecondOrderRE.mu1_pos hβ0 hc
  have h1 := SecondOrderRE.mu1_lt_one hβ0 hc
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have h := (optimalGiven_unique 𝔼 hpo hβ0 hβ1 hκ hlam hx ω 1).1
    rw [𝔼.const] at h
    have h2 : (pbar - pbar * SecondOrderRE.mu1 β (κ ^ 2 / lam) ^ 1) ^ 2 = 0 := h
    have h3 : pbar * (1 - SecondOrderRE.mu1 β (κ ^ 2 / lam)) = 0 := by
      have := (pow_eq_zero_iff two_ne_zero).1 h2
      linear_combination this
    rcases mul_eq_zero.1 h3 with h | h
    · exact h
    · exact absurd h (by linarith)
  · rintro rfl
    have hopt := optimalGiven 𝔼 hpo hβ0 hβ1 hκ hlam (xs := xs) 0
    have e : DateZeroCommitment.lift (Ω := Ω)
        (DateZeroCommitment.inflPath β κ lam xs (timelessMult β κ lam xs 0)) = fun _ _ => 0 := by
      funext t ω
      simp only [DateZeroCommitment.lift, inflPath_timeless hβ0 hκ hlam, zero_mul]
    rw [e] at hopt
    exact ⟨_, hopt⟩

/-! ### The deterministic statements -/

/-- Woodford (2003), p. 475 (perfect foresight): `(π, x)` solves the problem of minimising (1.2)
over bounded sequences satisfying (1.1) with `π_0 = p₀`. -/
def IsOptimalGivenDet (β κ lam xs p₀ : ℝ) (π x : ℕ → ℝ) : Prop :=
  DateZeroCommitment.DetAS β κ π x ∧ DateZeroCommitment.DetBounded π ∧
    DateZeroCommitment.DetBounded x ∧ π 0 = p₀ ∧
    ∀ π' x', DateZeroCommitment.DetAS β κ π' x' → DateZeroCommitment.DetBounded π' →
      DateZeroCommitment.DetBounded x' → π' 0 = p₀ →
        DateZeroCommitment.detLoss β lam xs π x ≤ DateZeroCommitment.detLoss β lam xs π' x'

/-- Woodford (2003), p. 475: the deterministic constrained problem is `IsOptimalGiven` under
perfect foresight. -/
theorem isOptimalGivenDet_iff (β κ lam xs p₀ : ℝ) (π x : ℕ → ℝ) :
    IsOptimalGivenDet β κ lam xs p₀ π x ↔
      IsOptimalGiven perfectForesight β κ lam xs p₀ (DateZeroCommitment.lift π)
        (DateZeroCommitment.lift x) := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨(DateZeroCommitment.detAdmissible_iff β κ π x).mp ⟨h1, h2, h3⟩, fun _ => h4,
      fun π' x' hadm hπ0 ω => ?_⟩
    have hl : π' = DateZeroCommitment.lift (fun t => π' t ()) := by
      funext t ω'; cases ω'; rfl
    have hm : x' = DateZeroCommitment.lift (fun t => x' t ()) := by
      funext t ω'; cases ω'; rfl
    rw [hl, hm] at hadm ⊢
    obtain ⟨a1, a2, a3⟩ := (DateZeroCommitment.detAdmissible_iff β κ _ _).mpr hadm
    cases ω
    exact h5 _ _ a1 a2 a3 (hπ0 ())
  · rintro ⟨hadm, h0, hmin⟩
    obtain ⟨a1, a2, a3⟩ := (DateZeroCommitment.detAdmissible_iff β κ π x).mpr hadm
    refine ⟨a1, a2, a3, h0 (), fun π' x' b1 b2 b3 b4 => ?_⟩
    exact hmin _ _ ((DateZeroCommitment.detAdmissible_iff β κ π' x').mp ⟨b1, b2, b3⟩)
      (fun _ => b4) ()

/-- **Woodford (2003), Proposition 7.2, p. 475 (deterministic)**: the constant target `π̄` is
optimal from a timeless perspective (the problem with `π_0 = π̄` has a solution with constant
inflation `π̄`) iff `π̄ = 0`. -/
theorem prop_7_2_det {β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam)
    (pbar : ℝ) :
    (∃ x, IsOptimalGivenDet β κ lam xs pbar (fun _ => pbar) x) ↔ pbar = 0 := by
  rw [← prop_7_2 perfectForesight perfectForesight_pullOut hβ0 hβ1 hκ hlam pbar]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨_, (isOptimalGivenDet_iff β κ lam xs pbar _ x).mp hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨fun t => x t (), (isOptimalGivenDet_iff β κ lam xs pbar _ _).mpr ?_⟩
    have hm : DateZeroCommitment.lift (fun t => x t ()) = x := by
      funext t ω'; cases ω'; rfl
    rw [hm]
    exact hx

/-- Woodford (2003), p. 474 (**the general definition, deterministic**): a time-invariant policy
with evolution `(π, x)` is optimal from a timeless perspective if, for every date `t₀`, the
evolution from `t₀` onward is optimal subject to the constraint that the initial evolution
(`π_{t₀}`) be the one associated with the policy. -/
def TimelessFromEveryDate (β κ lam xs : ℝ) (π x : ℕ → ℝ) : Prop :=
  ∀ t₀, IsOptimalGivenDet β κ lam xs (π t₀) (fun t => π (t₀ + t)) (fun t => x (t₀ + t))

/-- Woodford (2003), pp. 474–475: for a constant inflation target the general definition
reduces to the one of p. 475 (the problem is time-invariant, so the condition at every date `t₀`
is the condition at date 0). -/
theorem timelessFromEveryDate_iff (β κ lam xs pbar xbar : ℝ) :
    TimelessFromEveryDate β κ lam xs (fun _ => pbar) (fun _ => xbar) ↔
      IsOptimalGivenDet β κ lam xs pbar (fun _ => pbar) (fun _ => xbar) :=
  ⟨fun h => h 0, fun h _ => h⟩

/-- **Woodford (2003), Proposition 7.2 with the general definition of p. 474**: a constant
inflation rate `π̄` (with the output gap `(1 − β)π̄/κ` that (1.1) then requires) is optimal from a
timeless perspective in the sense that its evolution from every date is optimal given its initial
inflation, iff `π̄ = 0`. -/
theorem prop_7_2_everyDate {β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (pbar : ℝ) :
    TimelessFromEveryDate β κ lam xs (fun _ => pbar) (fun _ => (1 - β) * pbar / κ) ↔
      pbar = 0 := by
  rw [timelessFromEveryDate_iff, ← prop_7_2_det hβ0 hβ1 hκ hlam pbar]
  constructor
  · intro h; exact ⟨_, h⟩
  · rintro ⟨x, hx⟩
    -- a constant inflation path satisfying (1.1) has the constant gap `(1 − β)π̄/κ`
    have hx' : x = fun _ => (1 - β) * pbar / κ := by
      funext t
      have := hx.1 t
      field_simp
      linarith
    rw [hx'] at hx
    exact hx

/-! ### The inflation bias (survey E2) and Figure 7.1 -/

/-- Woodford (2003), p. 475 (survey E2, corrected): the constant inflation bias of discretion
relative to the timelessly optimal policy (zero inflation), `πᵉ − 0`, is positive iff `x* > 0`. -/
theorem bias_pos_iff {β κ lam xs : ℝ} (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) :
    0 < InflationBias.discretionInflation β κ lam xs - 0 ↔ 0 < xs := by
  rw [sub_zero]
  exact InflationBias.discretionInflation_pos_iff hβ1 hκ hlam

/-- Woodford (2003), p. 475 (survey E2): when `x* = 0` the inflation bias is zero. -/
theorem bias_zero_of_xs_zero (β κ lam : ℝ) : InflationBias.discretionInflation β κ lam 0 = 0 := by
  simp [InflationBias.discretionInflation]

/-- Woodford (2003), p. 475 (survey E2, the printed claim is false): the bias is not "clearly
positive when `x* = 0`"; at `x* = 0` it vanishes. -/
theorem printed_E2_false (β κ lam : ℝ) : ¬ 0 < InflationBias.discretionInflation β κ lam 0 := by
  rw [bias_zero_of_xs_zero]
  exact lt_irrefl 0

/-- **Woodford (2003), Figure 7.1, p. 476** ("inflation is lowest under the last of these
policies"): for `x* > 0`, at every date, timeless inflation `0` is below the date-zero optimal
inflation (1.13), which is below discretionary inflation (1.6). -/
theorem fig_7_1_ordering {β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hxs : 0 < xs) (t : ℕ) :
    0 < DateZeroCommitment.inflPath β κ lam xs 0 t ∧
      DateZeroCommitment.inflPath β κ lam xs 0 t <
        InflationBias.discretionInflation β κ lam xs := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  set μ := SecondOrderRE.mu1 β (κ ^ 2 / lam) with hμ
  have h0 : 0 < μ := SecondOrderRE.mu1_pos hβ0 hc
  have h1 : μ < 1 := SecondOrderRE.mu1_lt_one hβ0 hc
  have hr := SecondOrderRE.charPoly_mu1 hβ0 hc
  rw [← hμ] at hr
  unfold SecondOrderRE.charPoly at hr
  rw [DateZeroCommitment.inflPath_zero, ← hμ]
  have hpt : 0 < μ ^ t := pow_pos h0 t
  have hpt1 : μ ^ t ≤ 1 := pow_le_one₀ h0.le h1.le
  have hlk : 0 < lam / κ := by positivity
  refine ⟨by have : 0 < 1 - μ := by linarith
             positivity, ?_⟩
  -- `(1 − μ₁)(1 − β) < (κ²/λ)μ₁ = (1 − μ₁)(1 − βμ₁)`
  have hkey : (1 - μ) * ((1 - β) * lam + κ ^ 2) < κ ^ 2 := by
    have e : κ ^ 2 / lam * μ = (1 - μ) * (1 - β * μ) := by linear_combination (-1 : ℝ) * hr
    have e2 : κ ^ 2 * μ = lam * ((1 - μ) * (1 - β * μ)) := by
      rw [← e]; field_simp
    nlinarith [mul_pos (mul_pos hβ0 (sub_pos.mpr h1)) (mul_pos hlam (sub_pos.mpr h1))]
  have hd : 0 < (1 - β) * lam + κ ^ 2 := by nlinarith [sq_nonneg κ]
  calc (1 - μ) * (lam / κ) * xs * μ ^ t ≤ (1 - μ) * (lam / κ) * xs * 1 := by gcongr
    _ < InflationBias.discretionInflation β κ lam xs := by
        unfold InflationBias.discretionInflation
        rw [mul_one, lt_div_iff₀ hd]
        have : (1 - μ) * (lam / κ) * xs * ((1 - β) * lam + κ ^ 2) =
            (lam * xs / κ) * ((1 - μ) * ((1 - β) * lam + κ ^ 2)) := by ring
        rw [this]
        have : κ * lam * xs = (lam * xs / κ) * κ ^ 2 := by field_simp
        rw [this]
        exact mul_lt_mul_of_pos_left hkey (by positivity)

/-- Woodford (2003), p. 473 and Figure 7.1 ("under the optimal commitment, inflation should
asymptotically approach zero, despite … `x* > 0`"): the date-zero optimal inflation tends to
zero. -/
theorem tendsto_dateZero_inflation {β κ lam xs : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam) :
    Tendsto (DateZeroCommitment.inflPath β κ lam xs 0) atTop (𝓝 0) := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  have h0 := SecondOrderRE.mu1_pos hβ0 hc
  have h1 := SecondOrderRE.mu1_lt_one hβ0 hc
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).const_mul
    ((1 - SecondOrderRE.mu1 β (κ ^ 2 / lam)) * (lam / κ) * xs)
  simp only [mul_zero] at this
  refine this.congr fun t => ?_
  rw [DateZeroCommitment.inflPath_zero]

/-! ### The nominal interest rate stays nonnegative (p. 469) -/

/-- Woodford (2003), Ch. 4, eq. (1.12), p. 246 (perfect foresight, restated): the intertemporal IS
relation `x_t = x_{t+1} − σ(ı̂_t − π_{t+1} − r̂ⁿ_t)`, with `ı̂_t = log((1 + i_t)/(1 + ī))` the
deviation of the nominal rate from its zero-inflation steady state. -/
def IS (σ : ℝ) (rn i π x : ℕ → ℝ) : Prop := ∀ t, x t = x (t + 1) - σ * (i t - π (t + 1) - rn t)

/-- Woodford (2003), p. 469 ("the IS relation … simply determines the path of interest rates"):
the interest rate implied by paths of inflation and output with no real disturbances,
`ı̂_t = π_{t+1} + (x_{t+1} − x_t)/σ`. -/
noncomputable def impliedRate (σ : ℝ) (π x : ℕ → ℝ) (t : ℕ) : ℝ :=
  π (t + 1) + (x (t + 1) - x t) / σ

/-- Woodford (2003), p. 469: with no real disturbances (`r̂ⁿ = 0`) and `σ ≠ 0`, the IS relation
determines the interest-rate path uniquely: it holds iff `ı̂ = impliedRate`. -/
theorem is_iff_impliedRate {σ : ℝ} (hσ : σ ≠ 0) (i π x : ℕ → ℝ) :
    IS σ (fun _ => 0) i π x ↔ i = impliedRate σ π x := by
  rw [funext_iff]
  refine forall_congr' fun t => ?_
  unfold impliedRate
  constructor
  · intro h; field_simp; linarith
  · intro h; rw [h]; field_simp; ring

/-- Woodford (2003), Ch. 4, p. 248 (`r̂ⁿ`, `1 + r̄ⁿ = β⁻¹`), and p. 469 (the zero bound in
log-linear notation): with
`1 + ī = β⁻¹` (the zero-inflation steady state, `1 + r̄ⁿ = β⁻¹`) and
`ı̂ = log((1 + i)/(1 + ī))`, the nominal rate `i > −1` is nonnegative iff `ı̂ ≥ log β`. -/
theorem nonneg_iff_hat {β i : ℝ} (hβ : 0 < β) (hi : -1 < i) :
    0 ≤ i ↔ Real.log β ≤ Real.log ((1 + i) / β⁻¹) := by
  have h1 : 0 < 1 + i := by linarith
  rw [Real.log_div h1.ne' (inv_pos.mpr hβ).ne', Real.log_inv]
  rw [show Real.log β ≤ Real.log (1 + i) - -Real.log β ↔ 0 ≤ Real.log (1 + i) by
    constructor <;> intro h <;> linarith, Real.log_nonneg_iff h1]
  constructor <;> intro h <;> linarith

/-- Woodford (2003), p. 469: along the discretionary equilibrium (constant inflation (1.6) and
constant output gap) the implied rate is `ı̂_t = πᵉ`. -/
theorem discretion_impliedRate (σ β κ lam xs : ℝ) (t : ℕ) :
    impliedRate σ (fun _ => InflationBias.discretionInflation β κ lam xs)
      (fun _ => (1 - β) * InflationBias.discretionInflation β κ lam xs / κ) t =
      InflationBias.discretionInflation β κ lam xs := by
  simp [impliedRate]

/-- **Woodford (2003), p. 469 (discretion)**: for `x* ≥ 0` the nominal rate implied by the
discretionary equilibrium is nonnegative at every date, `ı̂_t = πᵉ ≥ 0 > log β`. -/
theorem discretion_rate_nonneg {σ β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hxs : 0 ≤ xs) (t : ℕ) :
    Real.log β ≤ impliedRate σ (fun _ => InflationBias.discretionInflation β κ lam xs)
      (fun _ => (1 - β) * InflationBias.discretionInflation β κ lam xs / κ) t := by
  rw [discretion_impliedRate]
  have hd2 : 0 < (1 - β) * lam + κ ^ 2 := by nlinarith [sq_nonneg κ]
  have : 0 ≤ InflationBias.discretionInflation β κ lam xs := by
    unfold InflationBias.discretionInflation; positivity
  linarith [Real.log_neg hβ0 hβ1]

/-- **Woodford (2003), p. 469 (timeless policy)**: zero inflation with a zero output gap implies
`ı̂_t = 0 > log β`, a positive nominal rate. -/
theorem timeless_rate_nonneg {σ β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (t : ℕ) :
    Real.log β ≤ impliedRate σ (fun _ => 0) (fun _ => 0) t := by
  simp only [impliedRate, sub_self, zero_div, add_zero]
  exact (Real.log_neg hβ0 hβ1).le

/-- Woodford (2003), p. 469 and (1.13): along the date-zero optimal commitment the implied rate
is `ı̂_t = (1 − μ₁)μ₁^{t+1}x*(λ/κ − 1/σ)`. -/
theorem dateZero_impliedRate {σ β κ lam xs : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hlam : lam ≠ 0)
    (t : ℕ) :
    impliedRate σ (DateZeroCommitment.inflPath β κ lam xs 0)
      (DateZeroCommitment.gapPath β κ lam xs 0) t =
      (1 - SecondOrderRE.mu1 β (κ ^ 2 / lam)) * SecondOrderRE.mu1 β (κ ^ 2 / lam) ^ (t + 1) *
        xs * (lam / κ - 1 / σ) := by
  unfold impliedRate
  rw [DateZeroCommitment.inflPath_zero, DateZeroCommitment.gapPath_zero hκ hlam,
    DateZeroCommitment.gapPath_zero hκ hlam]
  field_simp
  ring

/-- **Woodford (2003), p. 469 (date-zero commitment, exact condition)**: the nominal rate implied
by the date-zero optimal commitment is nonnegative at every date `t ≥ 0` iff it is at date 0,
i.e. iff `log β ≤ (1 − μ₁)μ₁x*(λ/κ − 1/σ)`. -/
theorem dateZero_rate_nonneg_iff {σ β κ lam xs : ℝ} (hβ0 : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ)
    (hlam : 0 < lam) (hβ1 : β < 1) :
    (∀ t, Real.log β ≤ impliedRate σ (DateZeroCommitment.inflPath β κ lam xs 0)
      (DateZeroCommitment.gapPath β κ lam xs 0) t) ↔
      Real.log β ≤ (1 - SecondOrderRE.mu1 β (κ ^ 2 / lam)) * SecondOrderRE.mu1 β (κ ^ 2 / lam) *
        xs * (lam / κ - 1 / σ) := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  set μ := SecondOrderRE.mu1 β (κ ^ 2 / lam) with hμ
  have h0 : 0 < μ := SecondOrderRE.mu1_pos hβ0 hc
  have h1 : μ < 1 := SecondOrderRE.mu1_lt_one hβ0 hc
  simp only [dateZero_impliedRate hσ.ne' hκ.ne' hlam.ne', ← hμ]
  constructor
  · intro h; simpa using h 0
  · intro h t
    set c := (1 - μ) * xs * (lam / κ - 1 / σ) with hcdef
    have e : ∀ n : ℕ, (1 - μ) * μ ^ n * xs * (lam / κ - 1 / σ) = c * μ ^ n := fun n => by
      rw [hcdef]; ring
    rw [e]
    rw [show (1 - μ) * μ * xs * (lam / κ - 1 / σ) = c * μ by rw [hcdef]; ring] at h
    have hp : μ ^ (t + 1) ≤ μ := by
      rw [pow_succ']
      exact mul_le_of_le_one_right h0.le (pow_le_one₀ h0.le h1.le)
    have hp0 : 0 < μ ^ (t + 1) := pow_pos h0 _
    rcases le_or_gt 0 c with hc0 | hc0
    · have := mul_nonneg hc0 hp0.le
      linarith [Real.log_neg hβ0 hβ1]
    · nlinarith

/-- Woodford (2003), p. 469 (sufficient condition): if `λσ ≥ κ` and `x* ≥ 0`, the date-zero
commitment implies a nonnegative nominal rate at every date (then `ı̂_t ≥ 0`). -/
theorem dateZero_rate_nonneg_of_le {σ β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) (hlam : 0 < lam) (hxs : 0 ≤ xs) (hle : κ ≤ lam * σ) (t : ℕ) :
    Real.log β ≤ impliedRate σ (DateZeroCommitment.inflPath β κ lam xs 0)
      (DateZeroCommitment.gapPath β κ lam xs 0) t := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  have h0 := SecondOrderRE.mu1_pos hβ0 hc
  have h1 := SecondOrderRE.mu1_lt_one hβ0 hc
  rw [dateZero_impliedRate hσ.ne' hκ.ne' hlam.ne']
  have hd : 0 ≤ lam / κ - 1 / σ := by
    rw [sub_nonneg, div_le_div_iff₀ hσ hκ]; linarith
  have : 0 ≤ (1 - SecondOrderRE.mu1 β (κ ^ 2 / lam)) *
      SecondOrderRE.mu1 β (κ ^ 2 / lam) ^ (t + 1) * xs * (lam / κ - 1 / σ) := by
    have : 0 ≤ 1 - SecondOrderRE.mu1 β (κ ^ 2 / lam) := by linarith
    positivity
  linarith [Real.log_neg hβ0 hβ1]

/-- Woodford (2003), p. 469 (the book's reading: `x*` small): for every parameter configuration
there is `B > 0` such that for all `0 ≤ x* ≤ B` the date-zero commitment implies a nonnegative
nominal rate at every date. -/
theorem dateZero_rate_nonneg_small {σ β κ lam : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) (hlam : 0 < lam) :
    ∃ B > 0, ∀ xs, 0 ≤ xs → xs ≤ B → ∀ t, Real.log β ≤
      impliedRate σ (DateZeroCommitment.inflPath β κ lam xs 0)
        (DateZeroCommitment.gapPath β κ lam xs 0) t := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  set μ := SecondOrderRE.mu1 β (κ ^ 2 / lam) with hμ
  have h0 : 0 < μ := SecondOrderRE.mu1_pos hβ0 hc
  have h1 : μ < 1 := SecondOrderRE.mu1_lt_one hβ0 hc
  have hL : 0 < -Real.log β := by linarith [Real.log_neg hβ0 hβ1]
  set D := (1 - μ) * μ * (|lam / κ| + |1 / σ|) + 1 with hD
  have hD0 : 0 < D := by
    have : 0 ≤ (1 - μ) * μ * (|lam / κ| + |1 / σ|) := by
      have : 0 ≤ 1 - μ := by linarith
      positivity
    linarith
  refine ⟨-Real.log β / D, div_pos hL hD0, fun xs hxs hB => ?_⟩
  refine (dateZero_rate_nonneg_iff hβ0 hσ hκ hlam hβ1).mpr ?_
  rw [← hμ]
  have hk : |lam / κ - 1 / σ| ≤ |lam / κ| + |1 / σ| := abs_sub _ _
  have hm : 0 ≤ (1 - μ) * μ := mul_nonneg (by linarith) h0.le
  have hbound : -((1 - μ) * μ * xs * (|lam / κ| + |1 / σ|)) ≤
      (1 - μ) * μ * xs * (lam / κ - 1 / σ) := by
    have := neg_abs_le (lam / κ - 1 / σ)
    have hx : 0 ≤ (1 - μ) * μ * xs := mul_nonneg hm hxs
    nlinarith
  have hxD : xs * D ≤ -Real.log β := by rwa [le_div_iff₀ hD0] at hB
  have : (1 - μ) * μ * xs * (|lam / κ| + |1 / σ|) ≤ xs * D := by
    rw [hD]; nlinarith
  linarith

/-- **Woodford (2003), p. 469 (survey-style counterexample: the claim needs a hypothesis)**: if
`λσ < κ`, then for `x*` large enough the date-zero commitment implies a negative nominal rate at
date 0, so "this is true for … the optimal commitment" fails without a smallness condition on
`x*` (or `λσ ≥ κ`). -/
theorem dateZero_rate_counterexample {σ β κ lam : ℝ} (hβ0 : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ)
    (hlam : 0 < lam) (hlt : lam * σ < κ) :
    ∃ xs > 0, impliedRate σ (DateZeroCommitment.inflPath β κ lam xs 0)
      (DateZeroCommitment.gapPath β κ lam xs 0) 0 < Real.log β := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  set μ := SecondOrderRE.mu1 β (κ ^ 2 / lam) with hμ
  have h0 : 0 < μ := SecondOrderRE.mu1_pos hβ0 hc
  have h1 : μ < 1 := SecondOrderRE.mu1_lt_one hβ0 hc
  have hd : lam / κ - 1 / σ < 0 := by
    rw [sub_neg, div_lt_div_iff₀ hκ hσ]; linarith
  set k := (1 - μ) * μ ^ 1 * (1 / σ - lam / κ) with hk
  have hk0 : 0 < k := by
    have : 0 < 1 - μ := by linarith
    have : 0 < 1 / σ - lam / κ := by linarith
    positivity
  refine ⟨(|Real.log β| + 1) / k, by positivity, ?_⟩
  rw [dateZero_impliedRate hσ.ne' hκ.ne' hlam.ne', ← hμ]
  have e : (1 - μ) * μ ^ (0 + 1) * ((|Real.log β| + 1) / k) * (lam / κ - 1 / σ) =
      -(|Real.log β| + 1) := by
    have hk' : (1 - μ) * μ ^ (0 + 1) * (lam / κ - 1 / σ) = -k := by rw [hk]; ring
    calc (1 - μ) * μ ^ (0 + 1) * ((|Real.log β| + 1) / k) * (lam / κ - 1 / σ)
        = ((1 - μ) * μ ^ (0 + 1) * (lam / κ - 1 / σ)) * ((|Real.log β| + 1) / k) := by ring
      _ = -(|Real.log β| + 1) := by rw [hk']; field_simp
  rw [e]
  linarith [neg_abs_le (Real.log β)]

end Woodford.GainsFromCommitment.Timeless
