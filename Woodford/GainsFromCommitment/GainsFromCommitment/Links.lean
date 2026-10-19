/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.Timeless
import GainsFromCommitment.Indexation
import GainsFromCommitment.Discretion
import GainsFromCommitment.CostPushCommitment
import GainsFromCommitment.NaturalRateCommitment
import GainsFromCommitment.InstrumentPath
import GainsFromCommitment.Implementation

/-!
# Cross-links between the formalisations of Chapter 7

Woodford (2003), *Interest and Prices*, Chapter 7 (pp. 464–533) and Appendix F (pp. 709–715).

Several book objects were formalised from different angles in different parts of the project.
This module proves that the different formalisations agree.

## Model equations
* `as_zero_iff`, `noninertial_AS_iff`, `costPush_AS_iff`: the aggregate-supply relation (2.1)
  with `u ≡ 0` is (1.1) of §1.1; the §3 form with the arguments in another order and the
  integer-dated §2.1 form are the same relation.
* `noninertial_IS_iff_natRate`, `noninertial_IS_iff_implementation`, `timeless_IS_iff`: the
  IS relation (2.23) in its three argument orders, and the deterministic (Ch. 4 (1.12)) form.
* `ar1Innov_noninertial`, `ar1Innov_varianceFrontier`: AR(1) disturbances with constant
  innovation variance (§2.1, p. 496, and §3, p. 511).
* `targetingRule_loss_eq`, `targetingRule_loss_eq_lq`: the ways of writing the expected
  discounted loss (1.2) — `E₀ ∑ βᵗ ℓ_t` (§1.1), `∑ βᵗ E₀ ℓ_t` (§5) and the general
  linear-quadratic loss of `LQSufficiency` — agree on bounded plans.

## Optimal commitment
* `feasible_zero_iff`, `isOptimalGiven_iff_isConstrainedOpt` (p. 475 vs pp. 489, 523): the
  §1.1 problem with `π₀ = p₀` is the constrained problem (2.8) of §2.1/§5.1 with `u ≡ 0`.
* `feasibleFree_zero_iff`, `dateZero_isT0Opt` (pp. 473, 489, 523): the date-zero plan of §1.1,
  optimal by `LQSufficiency`, is the `t₀`-optimal commitment of §5 with `u ≡ 0`.
* `timeless_plan_eq_star` (p. 475 vs Prop. 7.15, p. 524): the timeless plan `π_t = p₀μ₁ᵗ` is the
  unique bounded solution of (2.1) and the target criterion (5.1) (pre-sample gap
  `timelessXm1`); `timeless_plan_crit` checks (5.1) directly,
  `timeless_plan_timelesslyOptimal` (Prop. 7.15, timeless perspective) and
  `timeless_plan_implemented` (Prop. 7.17, p. 530) carry the results of §5 over to it.
* `instrumentXm1`, `instrumentXm1_spec`, `instrumentPath_eq_star`,
  `instrumentPath_isConstrainedOpt` (Prop. 7.14, p. 518, vs Props.
  7.7 and 7.15): the equilibrium (4.1) under the instrument path (4.2) is the optimal commitment
  equilibrium, optimal under the constraint (2.11) and from a timeless perspective.
* `impulsePlan_eq_star` ((2.7), p. 489, vs Prop. 7.15): the multiplier plan used for the impulse
  responses of §2.1, from any initial multiplier, is the §5 equilibrium with pre-sample gap
  `x* + (κ/λ)φ_{t₀−1}`.
* `faithful_of_ofNat`, `finiteTree_faithful`: the §2.1 faithfulness hypothesis gives the §5
  one, so the uniqueness results of §5 hold on every finite event tree
  (`finiteTree_eq_star_of_isConstrainedOpt`).
* `instrumentMu1_eq_m1`, `instrumentMu2_eq_m2`, `lamL_eq`: the roots used in §4 are the shared
  roots of (1.11).

## Discretion
* `piDisc_eq_discretionInflation`, `infl23_zero_eq_bias`, `discretionEq_zero_shock`
  (Prop. 7.1, p. 471, vs Prop. 7.5, p. 487): with no cost-push shocks the discretionary
  equilibrium of §2.1 is the constant inflation bias (1.6).
* `discretion_iff_solves22`, `infl23_eq_plan1`, `gap23_eq_plan1` (p. 487 vs pp. 511–512): the
  two formalisations of the discretionary condition (2.2), and the Markov solution (2.3) under
  AR(1) shocks is the noninertial plan `π̄^disc + f_π^disc u_t`, `x̄^disc + f_x^disc u_t`.
* `oni_lstab_le_discretion` (Prop. 7.11, p. 510, vs Prop. 7.5): the optimal noninertial plan has a
  stabilization loss no larger than the discretionary equilibrium, strictly smaller when
  `0 < ρ < 1`.

## Long-run targets
* `timelessOpt12_iff_timelesslyOptimal` (Prop. 7.2, p. 475, restated in §3): the two
  formalisations of timeless optimality of a constant target agree.
* `piBar119_eq_piBar_basic`, `timelessOpt114_iff_basic` (Prop. 7.3, p. 478, and (3.11), p. 513):
  the two formalisations of the optimal long-run inflation rate with transactions frictions
  agree.

## Natural-rate disturbances
* `instrumentPath_no_costPush` (Prop. 7.14 vs p. 501): without cost-push shocks the optimal
  instrument path is `i_t = rⁿ_t` with `π = x = 0`, the zero-gap policy of §2.2.
* `zero_gap_unique_faithful` (p. 501): uniqueness of the zero-gap optimum, proved in §2.2 under
  perfect foresight, holds for every faithful expectation system.
-/

namespace Woodford.GainsFromCommitment.Links

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Model equations -/

/-- Woodford (2003), eq. (2.1), p. 486, and eq. (1.1), p. 469: with `u ≡ 0` the aggregate-supply
relation with cost-push shocks (`VarianceFrontier.AS`, also used in §5) is the relation (1.1) of
§1.1 (`DateZeroCommitment.AS`). -/
theorem as_zero_iff (β κ : ℝ) (π x : ℕ → Ω → ℝ) :
    VarianceFrontier.AS 𝔼 β κ 0 π x ↔ DateZeroCommitment.AS 𝔼 β κ π x := by
  simp only [VarianceFrontier.AS, DateZeroCommitment.AS, Pi.zero_apply, add_zero]

/-- Woodford (2003), eq. (2.1), p. 486: the §3 formalisation of the aggregate-supply relation
(`Noninertial.AS`, arguments `π x u`) is the shared one (`VarianceFrontier.AS`, arguments
`u π x`). -/
theorem noninertial_AS_iff (β κ : ℝ) (π x u : ℕ → Ω → ℝ) :
    Noninertial.AS 𝔼 β κ π x u ↔ VarianceFrontier.AS 𝔼 β κ u π x := Iff.rfl

/-- Woodford (2003), eq. (2.1), p. 486: the integer-dated aggregate-supply relation of §2.1
(`CostPushCommitment.AS`, for the extension `ExpSysZ.ofNat 𝔼` of `𝔼` to integer dates) holds at
every date `t ≥ 0` iff the shared ℕ-dated relation (`VarianceFrontier.AS`) holds for the
restrictions of the processes to `t ≥ 0`. -/
theorem costPush_AS_iff (β κ : ℝ) (u π x : ℤ → Ω → ℝ) :
    (∀ n : ℕ, CostPushCommitment.AS (CostPushCommitment.ExpSysZ.ofNat 𝔼) β κ u π x n) ↔
      VarianceFrontier.AS 𝔼 β κ (fun n => u n) (fun n => π n) (fun n => x n) := by
  refine forall_congr' fun n => ?_
  have e : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
  simp only [CostPushCommitment.AS, CostPushCommitment.ExpSysZ.ofNat, Int.toNat_natCast, e]

/-- Woodford (2003), eq. (2.23), p. 502: the IS relation of §3 (`Noninertial.IS`) is the IS
relation of §2.2 (`NaturalRateCommitment.IS`). -/
theorem noninertial_IS_iff_natRate (σ : ℝ) (π x i rn : ℕ → Ω → ℝ) :
    Noninertial.IS 𝔼 σ π x i rn ↔ NaturalRateCommitment.IS 𝔼 σ rn π x i := Iff.rfl

/-- Woodford (2003), eq. (2.23), p. 502: the IS relation of §3 (`Noninertial.IS`) is the IS
relation of §5 (`Implementation.IS`). -/
theorem noninertial_IS_iff_implementation (σ : ℝ) (π x i rn : ℕ → Ω → ℝ) :
    Noninertial.IS 𝔼 σ π x i rn ↔ Implementation.IS 𝔼 σ rn i π x := Iff.rfl

/-- Woodford (2003), Ch. 4 eq. (1.12), p. 246, and Ch. 7 eq. (2.23), p. 502: the deterministic
IS relation used for the zero-bound remark of p. 469 (`Timeless.IS`) is the stochastic IS
relation of §5 under perfect foresight. -/
theorem timeless_IS_iff (σ : ℝ) (rn i π x : ℕ → ℝ) :
    Timeless.IS σ rn i π x ↔
      Implementation.IS perfectForesight σ (DateZeroCommitment.lift rn)
        (DateZeroCommitment.lift i) (DateZeroCommitment.lift π) (DateZeroCommitment.lift x) := by
  simp only [Timeless.IS, Implementation.IS, funext_iff, DateZeroCommitment.lift,
    perfectForesight, LinearMap.id_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact forall_congr' fun t => ⟨fun h _ => h, fun h => h ()⟩

/-- Woodford (2003), eq. (2.18), p. 496, and p. 511: an AR(1) disturbance with adapted mean-zero
innovations of constant conditional variance `s` (the §2.1 form `VarianceFrontier.AR1Innov`)
satisfies the §3 form `Noninertial.AR1Innov`. -/
theorem ar1Innov_noninertial {ρ s : ℝ} {u ε : ℕ → Ω → ℝ}
    (h : VarianceFrontier.AR1Innov 𝔼 ρ (fun _ => s) u ε) : Noninertial.AR1Innov 𝔼 ρ s u ε :=
  ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- Woodford (2003), eq. (2.18), p. 496, and p. 511: conversely, the §3 form with adapted
innovations is the §2.1 form with constant variance. -/
theorem ar1Innov_varianceFrontier {ρ s : ℝ} {u ε : ℕ → Ω → ℝ}
    (h : Noninertial.AR1Innov 𝔼 ρ s u ε) (hε : 𝔼.Adapted ε) :
    VarianceFrontier.AR1Innov 𝔼 ρ (fun _ => s) u ε :=
  ⟨h.1, hε, h.2.1, h.2.2.1, h.2.2.2⟩

/-- Woodford (2003), eq. (1.2), p. 469, and the expected loss of §2.1, p. 488: for bounded
plans and `0 ≤ β < 1`, the loss `∑ βᵗ E₀[π_t² + λ(x_t − x*)²]` of §5 (`TargetingRule.loss`) equals
the loss `E₀ ∑ βᵗ [π_t² + λ(x_t − x*)²]` of §1.1 (`DateZeroCommitment.loss`): `E₀` commutes with
the discounted sum. -/
theorem targetingRule_loss_eq {β lam xs : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {π x : ℕ → Ω → ℝ}
    (hπ : BoundedProc π) (hx : BoundedProc x) :
    TargetingRule.loss 𝔼 β lam xs π x = DateZeroCommitment.loss 𝔼 β lam xs π x := by
  obtain ⟨A, hA⟩ := hπ
  obtain ⟨B, hB⟩ := hx
  funext ω
  have hb : ∀ k ω', |(β ^ k • TargetingRule.periodLoss lam xs π x k) ω'| ≤
      β ^ k * (A ^ 2 + |lam| * (B + |xs|) ^ 2) := by
    intro k ω'
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
    exact mul_le_mul_of_nonneg_left (TargetingRule.abs_periodLoss_le hA hB k ω')
      (pow_nonneg hβ0 k)
  have h := 𝔼.E_tsum hβ0 hβ1 hb 0 ω
  simp only [Pi.smul_apply, smul_eq_mul, map_smul] at h
  unfold TargetingRule.loss DateZeroCommitment.loss
  exact h.symm

/-! ### Optimal commitment: §1.1 versus §§2.1 and 5.1 -/

/-- Woodford (2003), p. 475 and eq. (2.8), p. 489: with `u ≡ 0` a plan is feasible for the
constrained problem of §2.1/§5.1 with `π_{t₀} = p₀` (`TargetingRule.Feasible`) iff it is
admissible for the §1.1 problem (`DateZeroCommitment.Admissible`) and starts at `p₀`. -/
theorem feasible_zero_iff (β κ p₀ : ℝ) (π x : ℕ → Ω → ℝ) :
    TargetingRule.Feasible 𝔼 β κ 0 (fun _ => p₀) π x ↔
      DateZeroCommitment.Admissible 𝔼 β κ π x ∧ ∀ ω, π 0 ω = p₀ := by
  unfold TargetingRule.Feasible TargetingRule.FeasibleFree DateZeroCommitment.Admissible
  rw [as_zero_iff, funext_iff]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩
    exact ⟨⟨h5, h3, h4, h1, h2⟩, h6⟩
  · rintro ⟨⟨h5, h3, h4, h1, h2⟩, h6⟩
    exact ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩

/-- Woodford (2003), p. 475 versus eq. (2.8), p. 489, and §5.1, p. 523: the §1.1 problem of
minimising (1.2) subject to (1.1) and `π₀ = p₀` (`Timeless.IsOptimalGiven`) is the constrained
problem of §2.1/§5.1 (`TargetingRule.IsConstrainedOpt`) with no cost-push shocks and constraint
value `π̄_{t₀} = p₀` (`0 ≤ β < 1`). -/
theorem isOptimalGiven_iff_isConstrainedOpt {β lam xs : ℝ} (κ p₀ : ℝ) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (π x : ℕ → Ω → ℝ) :
    Timeless.IsOptimalGiven 𝔼 β κ lam xs p₀ π x ↔
      TargetingRule.IsConstrainedOpt 𝔼 β κ lam xs 0 (fun _ => p₀) π x := by
  unfold Timeless.IsOptimalGiven TargetingRule.IsConstrainedOpt
  constructor
  · rintro ⟨hadm, h0, hmin⟩
    refine ⟨(feasible_zero_iff 𝔼 β κ p₀ π x).mpr ⟨hadm, h0⟩, fun π' x' hF' ω => ?_⟩
    obtain ⟨hadm', h0'⟩ := (feasible_zero_iff 𝔼 β κ p₀ π' x').mp hF'
    rw [targetingRule_loss_eq 𝔼 hβ0 hβ1 hadm.2.2.2.1 hadm.2.2.2.2,
      targetingRule_loss_eq 𝔼 hβ0 hβ1 hadm'.2.2.2.1 hadm'.2.2.2.2]
    exact hmin π' x' hadm' h0' ω
  · rintro ⟨hF, hmin⟩
    obtain ⟨hadm, h0⟩ := (feasible_zero_iff 𝔼 β κ p₀ π x).mp hF
    refine ⟨hadm, h0, fun π' x' hadm' h0' ω => ?_⟩
    have h := hmin π' x' ((feasible_zero_iff 𝔼 β κ p₀ π' x').mpr ⟨hadm', h0'⟩) ω
    rwa [targetingRule_loss_eq 𝔼 hβ0 hβ1 hadm.2.2.2.1 hadm.2.2.2.2,
      targetingRule_loss_eq 𝔼 hβ0 hβ1 hadm'.2.2.2.1 hadm'.2.2.2.2] at h

/-- Woodford (2003), (1.2), p. 469, and survey §4.4: on bounded plans the loss of §5
(`TargetingRule.loss`) is the expected loss of the general linear-quadratic problem
(`LQSufficiency.expLoss`) instantiated at the §1.1 problem (`DateZeroCommitment.lqProblem`). -/
theorem targetingRule_loss_eq_lq {β lam xs : ℝ} (κ : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {π x : ℕ → Ω → ℝ} (hπ : BoundedProc π) (hx : BoundedProc x) :
    TargetingRule.loss 𝔼 β lam xs π x =
      LQSufficiency.expLoss 𝔼 (DateZeroCommitment.lqProblem β κ lam xs)
        (DateZeroCommitment.toVec π x) := by
  rw [DateZeroCommitment.expLoss_eq, targetingRule_loss_eq 𝔼 hβ0 hβ1 hπ hx]

/-- Woodford (2003), eq. (2.8), p. 489: with `u ≡ 0` a plan is feasible for the `t₀`-optimal
problem of §5 (`TargetingRule.FeasibleFree`) iff it is admissible for the §1.1 problem. -/
theorem feasibleFree_zero_iff (β κ : ℝ) (π x : ℕ → Ω → ℝ) :
    TargetingRule.FeasibleFree 𝔼 β κ 0 π x ↔ DateZeroCommitment.Admissible 𝔼 β κ π x := by
  unfold TargetingRule.FeasibleFree DateZeroCommitment.Admissible
  rw [as_zero_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h5, h3, h4, h1, h2⟩
  · rintro ⟨h5, h3, h4, h1, h2⟩
    exact ⟨h1, h2, h3, h4, h5⟩

/-- Woodford (2003), (1.12)–(1.13), p. 473, versus §2.1, p. 489, and §5.1, p. 523 (the
`t₀`-optimal commitment): the date-zero optimal plan of §1.1 — optimal by the linear-quadratic
Lagrangian sufficiency theorem (`LQSufficiency.isOptimalAmong_of_foc` through
`DateZeroCommitment.dateZero_optimal`) — solves the `t₀`-optimal problem of §5
(`TargetingRule.IsT0Opt`) with no cost-push shocks (pull-out property). -/
theorem dateZero_isT0Opt (hpo : 𝔼.PullOut) {β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hlam : 0 < lam) :
    TargetingRule.IsT0Opt 𝔼 β κ lam xs 0
      (DateZeroCommitment.lift (DateZeroCommitment.inflPath β κ lam xs 0))
      (DateZeroCommitment.lift (DateZeroCommitment.gapPath β κ lam xs 0)) := by
  obtain ⟨hadm, hmin⟩ := DateZeroCommitment.dateZero_optimal 𝔼 hpo hβ0 hβ1 hκ hlam (xs := xs)
  refine ⟨(feasibleFree_zero_iff 𝔼 β κ _ _).mpr hadm, fun π' x' hF' ω => ?_⟩
  have hadm' := (feasibleFree_zero_iff 𝔼 β κ π' x').mp hF'
  rw [targetingRule_loss_eq 𝔼 hβ0.le hβ1 hadm.2.2.2.1 hadm.2.2.2.2,
    targetingRule_loss_eq 𝔼 hβ0.le hβ1 hadm'.2.2.2.1 hadm'.2.2.2.2]
  exact (hmin π' x' hadm' ω).1

/-- Woodford (2003), p. 475: the pre-sample output gap `x_{−1} = (κ/λ)p₀/(1 − μ₁)` implied by the
timeless plan `x_t = (κ/λ)μ₁^{t+1}p₀/(1 − μ₁)` (its value at `t = −1`). -/
noncomputable def timelessXm1 (β κ lam p₀ : ℝ) : ℝ :=
  κ / lam * p₀ / (1 - SecondOrderRE.mu1 β (κ ^ 2 / lam))

/-- Woodford (2003), p. 475 and eq. (5.1), p. 523: the timeless plan of §1.1,
`π_t = p₀μ₁ᵗ`, `x_t = (κ/λ)μ₁^{t+1}p₀/(1 − μ₁)` (`Timeless.optimalGiven`), satisfies the target
criterion (5.1) `π_t + (λ/κ)(x_t − x_{t−1}) = 0` at every date, including `t₀`, with the
pre-sample gap `timelessXm1`. -/
theorem timeless_plan_crit {β κ lam : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam)
    (xs p₀ : ℝ) :
    TargetingRule.Crit lam κ (fun _ => timelessXm1 β κ lam p₀)
      (DateZeroCommitment.lift (Ω := Ω)
        (DateZeroCommitment.inflPath β κ lam xs (Timeless.timelessMult β κ lam xs p₀)))
      (DateZeroCommitment.lift
        (DateZeroCommitment.gapPath β κ lam xs (Timeless.timelessMult β κ lam xs p₀))) := by
  have hc : 0 < κ ^ 2 / lam := by positivity
  have h1 := SecondOrderRE.mu1_lt_one hβ hc
  have h1' : 1 - SecondOrderRE.mu1 β (κ ^ 2 / lam) ≠ 0 := by linarith
  intro t
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.zero_apply]
  cases t with
  | zero =>
    simp only [Sequences.lagged_zero, DateZeroCommitment.lift,
      Timeless.inflPath_timeless hβ hκ hlam, Timeless.gapPath_timeless hκ hlam, timelessXm1]
    field_simp
    ring
  | succ t =>
    simp only [Sequences.lagged_succ, DateZeroCommitment.lift,
      Timeless.inflPath_timeless hβ hκ hlam, Timeless.gapPath_timeless hκ hlam]
    field_simp
    ring

/-- Woodford (2003), p. 475 and **Proposition 7.15**, p. 524: the timeless plan of §1.1 is the
unique bounded solution of (2.1) (with `u ≡ 0`) and the target criterion (5.1): it is the §5
equilibrium `TargetingRule.piStar`, `TargetingRule.xStar` with no cost-push shocks and the
pre-sample gap `timelessXm1`. -/
theorem timeless_plan_eq_star {β κ lam : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam)
    (xs p₀ : ℝ) :
    DateZeroCommitment.lift (Ω := Ω)
        (DateZeroCommitment.inflPath β κ lam xs (Timeless.timelessMult β κ lam xs p₀)) =
      TargetingRule.piStar 𝔼 β κ lam (fun _ => timelessXm1 β κ lam p₀) 0 ∧
    DateZeroCommitment.lift (Ω := Ω)
        (DateZeroCommitment.gapPath β κ lam xs (Timeless.timelessMult β κ lam xs p₀)) =
      TargetingRule.xStar 𝔼 β κ lam (fun _ => timelessXm1 β κ lam p₀) 0 := by
  have hadm := DateZeroCommitment.plan_admissible 𝔼 hβ hκ hlam
    (xs := xs) (Timeless.timelessMult β κ lam xs p₀)
  have hu : BoundedProc (0 : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
  have hua : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => by simp
  have hm0 : 𝔼.E 0 (fun _ => timelessXm1 β κ lam p₀) = fun _ => timelessXm1 β κ lam p₀ :=
    𝔼.const 0 _
  exact (TargetingRule.prop_7_15 𝔼 hβ hκ hlam hu hua (K := |timelessXm1 β κ lam p₀|)
    (fun _ => le_rfl) hm0).2 _ _ ((as_zero_iff 𝔼 β κ _ _).mpr hadm.1)
    (timeless_plan_crit hβ hκ hlam xs p₀) hadm.2.2.2.2 hadm.2.2.1

/-- Woodford (2003), p. 475 and **Proposition 7.15**, p. 524 ("optimal from a timeless
perspective"): the timeless plan of §1.1 is timelessly optimal in the sense of §5
(`TargetingRule.TimelesslyOptimal`): at every date its continuation solves the constrained
problem with the time-invariant constraint (2.11) (pull-out property). -/
theorem timeless_plan_timelesslyOptimal (hpo : 𝔼.PullOut) {β κ lam : ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) (xs p₀ : ℝ) :
    TargetingRule.TimelesslyOptimal 𝔼 β κ lam xs 0
      (TargetingRule.rule211 𝔼 β κ lam 0 (fun _ => timelessXm1 β κ lam p₀)
        (DateZeroCommitment.lift
          (DateZeroCommitment.gapPath β κ lam xs (Timeless.timelessMult β κ lam xs p₀))))
      (DateZeroCommitment.lift
        (DateZeroCommitment.inflPath β κ lam xs (Timeless.timelessMult β κ lam xs p₀)))
      (DateZeroCommitment.lift
        (DateZeroCommitment.gapPath β κ lam xs (Timeless.timelessMult β κ lam xs p₀))) := by
  obtain ⟨h1, h2⟩ := timeless_plan_eq_star 𝔼 hβ hκ hlam xs p₀
  rw [h1, h2]
  exact TargetingRule.prop_7_15_timeless 𝔼 hβ hβ1 hκ hlam hpo xs ⟨0, fun _ _ => by simp⟩
    (fun t => by simp) (K := |timelessXm1 β κ lam p₀|) (fun _ => le_rfl) (𝔼.const 0 _)

/-- Woodford (2003), **Proposition 7.17**, p. 530, applied to the timeless plan of §1.1, p. 475:
with no cost-push shocks and any bounded adapted natural rate `rⁿ`, the interest-rate rule (5.5)
(with the pre-sample gap `timelessXm1`) implements the timeless plan: the plan together with the
rate `Implementation.iStar` satisfies (2.1), (2.23) and (5.5), and every bounded adapted
equilibrium of (2.1), (2.23) and (5.5) is this plan. -/
theorem timeless_plan_implemented {β κ lam σ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam)
    (hσ : 0 < σ) (xs p₀ : ℝ) {rn : ℕ → Ω → ℝ} (hrn : BoundedProc rn) (hrna : 𝔼.Adapted rn) :
    Implementation.IS 𝔼 σ rn
        (Implementation.iStar 𝔼 β κ lam σ rn 0 (fun _ => timelessXm1 β κ lam p₀))
        (DateZeroCommitment.lift
          (DateZeroCommitment.inflPath β κ lam xs (Timeless.timelessMult β κ lam xs p₀)))
        (DateZeroCommitment.lift
          (DateZeroCommitment.gapPath β κ lam xs (Timeless.timelessMult β κ lam xs p₀))) ∧
      Implementation.RF55 𝔼 β κ lam σ rn 0 (fun _ => timelessXm1 β κ lam p₀)
        (Implementation.iStar 𝔼 β κ lam σ rn 0 (fun _ => timelessXm1 β κ lam p₀))
        (DateZeroCommitment.lift
          (DateZeroCommitment.inflPath β κ lam xs (Timeless.timelessMult β κ lam xs p₀)))
        (DateZeroCommitment.lift
          (DateZeroCommitment.gapPath β κ lam xs (Timeless.timelessMult β κ lam xs p₀))) ∧
      ∀ π x i : ℕ → Ω → ℝ, DateZeroCommitment.AS 𝔼 β κ π x → Implementation.IS 𝔼 σ rn i π x →
        Implementation.RF55 𝔼 β κ lam σ rn 0 (fun _ => timelessXm1 β κ lam p₀) i π x →
        BoundedProc x → 𝔼.Adapted x →
        π = DateZeroCommitment.lift
          (DateZeroCommitment.inflPath β κ lam xs (Timeless.timelessMult β κ lam xs p₀)) ∧
        x = DateZeroCommitment.lift
          (DateZeroCommitment.gapPath β κ lam xs (Timeless.timelessMult β κ lam xs p₀)) := by
  obtain ⟨h1, h2⟩ := timeless_plan_eq_star 𝔼 hβ hκ hlam xs p₀
  have h := Implementation.prop_7_17 𝔼 hβ hκ hlam hσ (u := 0) ⟨0, fun _ _ => by simp⟩
    (fun t => by simp) hrn hrna (K := |timelessXm1 β κ lam p₀|) (fun _ => le_rfl)
    (𝔼.const 0 _)
  rw [h1, h2]
  refine ⟨h.1.2.1, h.1.2.2.1, fun π x i hAS hIS hRF hxb hxa => ?_⟩
  obtain ⟨e1, e2, -⟩ := h.2 π x i ((as_zero_iff 𝔼 β κ π x).mpr hAS) hIS hRF hxb hxa
  exact ⟨e1, e2⟩

/-! ### Optimal commitment: Proposition 7.14 versus Propositions 7.7 and 7.15 -/

/-- Woodford (2003), p. 518: the pre-sample output gap `x_{t₀−1} = −(κ/λ)S₀/(β(μ₂ − ρ))` implied
by the shock history in the equilibrium (4.1) of Proposition 7.14. -/
noncomputable def instrumentXm1 (β κ lam ρ : ℝ) (u hist : ℕ → Ω → ℝ) : Ω → ℝ :=
  fun ω => -(κ / lam) * InstrumentPath.histSum (InstrumentPath.mu1 β κ lam) u hist 0 ω /
    (β * (InstrumentPath.mu2 β κ lam - ρ))

/-- Woodford (2003), p. 518: the implied pre-sample gap is bounded and known at `t₀`. -/
theorem instrumentXm1_spec {β κ lam ρ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam)
    {u hist : ℕ → Ω → ℝ} {M : ℝ} (hua : 𝔼.Adapted u) (hub : ∀ t ω, |u t ω| ≤ M)
    (hh : ∀ j ω, |hist j ω| ≤ M) (hha : ∀ j, 𝔼.E 0 (hist j) = hist j) :
    (∃ K, ∀ ω, |instrumentXm1 β κ lam ρ u hist ω| ≤ K) ∧
      𝔼.E 0 (instrumentXm1 β κ lam ρ u hist) = instrumentXm1 β κ lam ρ u hist := by
  obtain ⟨-, -, h1pos, h1lt, h2⟩ := InstrumentPath.mu_facts hβ0 hκ hlam
  set c : ℝ := -(κ / lam) / (β * (InstrumentPath.mu2 β κ lam - ρ)) with hc
  have he : instrumentXm1 β κ lam ρ u hist =
      c • InstrumentPath.histSum (InstrumentPath.mu1 β κ lam) u hist 0 := by
    funext ω
    simp only [instrumentXm1, hc, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he]
  refine ⟨⟨|c| * (M / (1 - InstrumentPath.mu1 β κ lam)), fun ω => ?_⟩, ?_⟩
  · rw [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (InstrumentPath.histSum_bdd h1pos.le h1lt hub hh 0 ω) (abs_nonneg c)
  · rw [map_smul, InstrumentPath.histSum_adapted 𝔼 h1pos.le h1lt hub hh hua hha 0]

/-- Woodford (2003), **Proposition 7.14**, p. 518, versus **Proposition 7.15**, p. 524, and
**Proposition 7.7**, p. 491: under AR(1) cost-push shocks (`ρ < 1`) and a bounded pre-`t₀`
history known at `t₀`, the equilibrium paths (4.1) of the instrument-path analysis
(`InstrumentPath.piPath`, `xPath`) are the unique bounded solution of (2.1) and the target
criterion (5.1), i.e. the optimal commitment equilibrium `TargetingRule.piStar`, `xStar` with the
implied pre-sample gap `instrumentXm1`. -/
theorem instrumentPath_eq_star {β κ lam ρ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam)
    (hρ : ρ < 1) {u hist : ℕ → Ω → ℝ} {M : ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : ∀ t ω, |u t ω| ≤ M)
    (hh : ∀ j ω, |hist j ω| ≤ M) (hha : ∀ j, 𝔼.E 0 (hist j) = hist j) :
    InstrumentPath.piPath β κ lam ρ u hist =
        TargetingRule.piStar 𝔼 β κ lam (instrumentXm1 β κ lam ρ u hist) u ∧
      InstrumentPath.xPath β κ lam ρ u hist =
        TargetingRule.xStar 𝔼 β κ lam (instrumentXm1 β κ lam ρ u hist) u := by
  obtain ⟨⟨K, hK⟩, hm0⟩ := instrumentXm1_spec 𝔼 hβ0 hκ hlam hu.1 hub hh hha
  obtain ⟨-, -, -, hxa⟩ := InstrumentPath.paths_bdd_adapted 𝔼 hβ0 hκ hlam hρ hu.1 hub hh hha
  obtain ⟨-, -, hxb, -⟩ := InstrumentPath.paths_bdd_adapted 𝔼 hβ0 hκ hlam hρ hu.1 hub hh hha
  have hcrit : TargetingRule.Crit lam κ (instrumentXm1 β κ lam ρ u hist)
      (InstrumentPath.piPath β κ lam ρ u hist) (InstrumentPath.xPath β κ lam ρ u hist) := by
    intro t
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.zero_apply]
    cases t with
    | zero =>
      exact (InstrumentPath.piPath_target hβ0 hκ hlam hρ hub hh 0).2 ω
    | succ t =>
      exact (InstrumentPath.piPath_target hβ0 hκ hlam hρ hub hh t).1 ω
  exact (TargetingRule.prop_7_15 𝔼 hβ0 hκ hlam ⟨M, hub⟩ hu.1 hK hm0).2 _ _
    (InstrumentPath.piPath_AS 𝔼 hβ0 hκ hlam hρ hu hub hh hha) hcrit hxb hxa

/-- Woodford (2003), **Proposition 7.14**, p. 518, with **Proposition 7.7**, p. 491, and
Proposition 7.15, p. 524: the equilibrium (4.1) of the instrument-path analysis is optimal. It
minimises the expected discounted loss (1.2) among all bounded adapted plans satisfying (2.1) and
the initial constraint (2.11) (`TargetingRule.IsConstrainedOpt` with `TargetingRule.eq211`), and
it is optimal from a timeless perspective (pull-out property, `0 < β < 1`). -/
theorem instrumentPath_isConstrainedOpt (hpo : 𝔼.PullOut) {β κ lam ρ : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) (hρ : ρ < 1) (xs : ℝ) {u hist : ℕ → Ω → ℝ}
    {M : ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : ∀ t ω, |u t ω| ≤ M) (hh : ∀ j ω, |hist j ω| ≤ M)
    (hha : ∀ j, 𝔼.E 0 (hist j) = hist j) :
    TargetingRule.IsConstrainedOpt 𝔼 β κ lam xs u
        (TargetingRule.eq211 𝔼 β κ lam u (instrumentXm1 β κ lam ρ u hist))
        (InstrumentPath.piPath β κ lam ρ u hist) (InstrumentPath.xPath β κ lam ρ u hist) ∧
      TargetingRule.TimelesslyOptimal 𝔼 β κ lam xs u
        (TargetingRule.rule211 𝔼 β κ lam u (instrumentXm1 β κ lam ρ u hist)
          (InstrumentPath.xPath β κ lam ρ u hist))
        (InstrumentPath.piPath β κ lam ρ u hist) (InstrumentPath.xPath β κ lam ρ u hist) := by
  obtain ⟨⟨K, hK⟩, hm0⟩ := instrumentXm1_spec 𝔼 hβ0 hκ hlam hu.1 hub hh hha
  obtain ⟨h1, h2⟩ := instrumentPath_eq_star 𝔼 hβ0 hκ hlam hρ hu hub hh hha
  rw [h1, h2]
  obtain ⟨⟨hAS, hC, hπb, hxb, hπa, hxa⟩, -⟩ :=
    TargetingRule.prop_7_15 𝔼 hβ0 hκ hlam ⟨M, hub⟩ hu.1 hK hm0
  exact ⟨TargetingRule.crit_isConstrainedOpt 𝔼 hβ0 hβ1 hκ hlam hpo xs ⟨M, hub⟩ hu.1 hK hm0 hAS
    hC hπb hxb hπa hxa,
    TargetingRule.prop_7_15_timeless 𝔼 hβ0 hβ1 hκ hlam hpo xs ⟨M, hub⟩ hu.1 hK hm0⟩

/-! ### Optimal commitment: the impulse-response plan of §2.1 versus Proposition 7.15 -/

/-- Woodford (2003), (1.7)–(1.8) and (2.7), pp. 472, 489 (the plan used for the impulse
responses of §2.1, `ImpulseResponses.Plan`, where Lean date `0` is the economic date `t₀ − 1`)
versus **Proposition 7.15**, p. 524: for every initial multiplier `φ_{t₀−1}` known at `t₀` and
bounded, the plan from `t₀` on is the unique bounded solution of (2.1) and the target criterion
(5.1) with pre-sample gap `x_{t₀−1} = x* + (κ/λ)φ_{t₀−1}` (eq. (1.8) at `t₀ − 1`), i.e. the §5
equilibrium `TargetingRule.piStar`, `xStar` for the system seen from `t₀`
(`SecondOrderRE.shiftSys 𝔼 1`). -/
theorem impulsePlan_eq_star {β κ lam xs μ1 μ2 M B : ℝ} (hβ : 0 < β) (hκ : 0 < κ)
    (hlam : 0 < lam) (hr : ImpulseResponses.RootPair β (κ ^ 2 / lam) μ1 μ2)
    {u π x φ : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u)
    (hP : ImpulseResponses.Plan 𝔼 β κ lam xs μ1 μ2 u π x φ) (hφ0 : 𝔼.E 0 (φ 0) = φ 0)
    (hφb : ∀ ω, |φ 0 ω| ≤ B) :
    (fun t => π (t + 1)) = TargetingRule.piStar (SecondOrderRE.shiftSys 𝔼 1) β κ lam
        (fun ω => xs + κ / lam * φ 0 ω) (fun t => u (t + 1)) ∧
      (fun t => x (t + 1)) = TargetingRule.xStar (SecondOrderRE.shiftSys 𝔼 1) β κ lam
        (fun ω => xs + κ / lam * φ 0 ω) (fun t => u (t + 1)) := by
  set 𝔼' := SecondOrderRE.shiftSys 𝔼 1 with h𝔼'
  have hE : ∀ t (y : Ω → ℝ), 𝔼'.E t y = 𝔼.E (t + 1) y := fun t y => by
    rw [h𝔼', SecondOrderRE.shiftSys_E, add_comm]
  have hμ1 : |μ1| < 1 := by rw [abs_of_pos hr.1]; exact hr.2.1
  have hφa := ImpulseResponses.plan_phi_adapted 𝔼 hr.2.2.1 hu hP hφ0
  obtain ⟨F, hF⟩ := ImpulseResponses.plan_phi_bounded 𝔼 hμ1 hr.2.2.1 hu hP hφb
  have hx1 : ∀ t, x (t + 1) = fun ω => xs + κ / lam * φ (t + 1) ω := fun t => by
    rw [hP.2.1 t]; funext ω; simp [smul_eq_mul]
  have hub : BoundedProc (fun t => u (t + 1)) := ⟨M, fun t ω => hu (t + 1) ω⟩
  have hua' : 𝔼'.Adapted (fun t => u (t + 1)) := fun t => by rw [hE]; exact hua (t + 1)
  have hm0 : 𝔼'.E 0 (fun ω => xs + κ / lam * φ 0 ω) = fun ω => xs + κ / lam * φ 0 ω := by
    have e : (fun ω => xs + κ / lam * φ 0 ω) = (fun _ => xs) + (κ / lam) • φ 0 := by
      funext ω; simp [smul_eq_mul]
    rw [hE, e, map_add, map_smul, 𝔼.const, ← hφ0, 𝔼.known (Nat.zero_le _)]
  have hK : ∀ ω, |xs + κ / lam * φ 0 ω| ≤ |xs| + |κ / lam| * B := fun ω => by
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hφb ω) (abs_nonneg _)
  have hAS : VarianceFrontier.AS 𝔼' β κ (fun t => u (t + 1)) (fun t => π (t + 1))
      (fun t => x (t + 1)) := fun t => by
    rw [hE]
    exact ImpulseResponses.plan_AS 𝔼 hβ hκ.ne' hlam.ne' hr hu hua hP hφ0 t
  have hcrit : TargetingRule.Crit lam κ (fun ω => xs + κ / lam * φ 0 ω) (fun t => π (t + 1))
      (fun t => x (t + 1)) := by
    intro t
    funext ω
    have hκ0 : κ ≠ 0 := hκ.ne'
    have hl0 : lam ≠ 0 := hlam.ne'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.zero_apply]
    cases t with
    | zero =>
      simp only [Sequences.lagged_zero, hx1 0, hP.1 0, Pi.sub_apply]
      field_simp
      ring
    | succ t =>
      simp only [Sequences.lagged_succ, hx1 (t + 1), hx1 t, hP.1 (t + 1), Pi.sub_apply]
      field_simp
      ring
  have hxb : BoundedProc (fun t => x (t + 1)) := by
    refine ⟨|xs| + |κ / lam| * F, fun t ω => ?_⟩
    simp only
    rw [hx1 t]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hF (t + 1) ω) (abs_nonneg _)
  have hxa : 𝔼'.Adapted (fun t => x (t + 1)) := by
    intro t
    have e : x (t + 1) = (fun _ => xs) + (κ / lam) • φ (t + 1) := by
      rw [hx1 t]; funext ω; simp [smul_eq_mul]
    simp only
    rw [hE, e, map_add, map_smul, 𝔼.const, hφa (t + 1)]
  exact (TargetingRule.prop_7_15 𝔼' hβ hκ hlam hub hua' hK hm0).2 _ _ hAS hcrit hxb hxa

/-! ### Faithful conditional expectations -/

/-- Woodford (2003), p. 490 (uniqueness of the constrained optimum): the faithfulness hypothesis
of §2.1 (`CostPushCommitment.ExpSysZ.Faithful`, for the integer-dated extension of `𝔼`) implies
the one of §5 (`TargetingRule.Faithful`, at date `t₀ = 0`). -/
theorem faithful_of_ofNat (h : (CostPushCommitment.ExpSysZ.ofNat 𝔼).Faithful) :
    TargetingRule.Faithful 𝔼 :=
  fun y hy h0 => h 0 y hy h0

/-- Woodford (2003), p. 490: every finite event tree (strictly positive state probabilities) is
faithful in the sense of §5, so the uniqueness results of §5 hold under genuine uncertainty, not
only under perfect foresight. -/
theorem finiteTree_faithful {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') : TargetingRule.Faithful T.toExpectationSystem :=
  faithful_of_ofNat _ (CostPushCommitment.ExpSysZ.ofNat_finiteTree_faithful T)

/-- Woodford (2003), **Proposition 7.15**, p. 524 (uniqueness of the optimum), on a finite event
tree: every solution of the constrained problem with the constraint (2.11) is the equilibrium
determined by (2.1) and (5.1). -/
theorem finiteTree_eq_star_of_isConstrainedOpt {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') {β κ lam xs : ℝ} (hβ : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hlam : 0 < lam) {u : ℕ → Ω' → ℝ} (hu : BoundedProc u)
    (hua : T.toExpectationSystem.Adapted u) {xm1 : Ω' → ℝ} {K : ℝ} (hK : ∀ ω, |xm1 ω| ≤ K)
    (hm0 : T.toExpectationSystem.E 0 xm1 = xm1) {π x : ℕ → Ω' → ℝ}
    (hopt : TargetingRule.IsConstrainedOpt T.toExpectationSystem β κ lam xs u
      (TargetingRule.eq211 T.toExpectationSystem β κ lam u xm1) π x) :
    π = TargetingRule.piStar T.toExpectationSystem β κ lam xm1 u ∧
      x = TargetingRule.xStar T.toExpectationSystem β κ lam xm1 u :=
  TargetingRule.eq_star_of_isConstrainedOpt _ hβ hβ1 hκ hlam
    (ExpectationsFiniteTree.finiteTree_pullOut T) (finiteTree_faithful T) hu hua hK hm0 hopt

/-! ### The roots used in §4 -/

/-- Woodford (2003), eq. (1.11), p. 472: the root `μ₁` of §4 (`InstrumentPath.mu1`) is the root
of §2.1 (`CostPushCommitment.m1`); both are the shared `SecondOrderRE.mu1 β (κ²/λ)`. -/
theorem instrumentMu1_eq_m1 (β κ lam : ℝ) :
    InstrumentPath.mu1 β κ lam = CostPushCommitment.m1 β κ lam := rfl

/-- Woodford (2003), eq. (1.11), p. 472: the root `μ₂` of §4 (`InstrumentPath.mu2`) is the root
of §2.1 (`CostPushCommitment.m2`). -/
theorem instrumentMu2_eq_m2 (β κ lam : ℝ) :
    InstrumentPath.mu2 β κ lam = CostPushCommitment.m2 β κ lam := rfl

/-- Woodford (2003), p. 519 and Ch. 4 (2.6): the unstable root `L` of
`μ² − (1 + β + κσ)μ + β = 0` used for the sunspot equilibria of §4 is `βμ₂ = μ₁⁻¹`, where
`μ₁ < 1 < μ₂` are the shared roots of `βμ² − (1 + β + κσ)μ + 1 = 0` (`β, κ, σ > 0`). -/
theorem lamL_eq {β κ σ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hσ : 0 < σ) :
    InstrumentPath.lamL β κ σ = β * SecondOrderRE.mu2 β (κ * σ) ∧
      InstrumentPath.lamL β κ σ = (SecondOrderRE.mu1 β (κ * σ))⁻¹ := by
  have hc : 0 < κ * σ := mul_pos hκ hσ
  have h1 : InstrumentPath.lamL β κ σ = β * SecondOrderRE.mu2 β (κ * σ) := by
    unfold InstrumentPath.lamL SecondOrderRE.mu2 SecondOrderRE.disc
    field_simp
  refine ⟨h1, ?_⟩
  rw [h1]
  exact eq_inv_of_mul_eq_one_left (by
    linear_combination SecondOrderRE.beta_mul_mu1_mul_mu2 hβ hc)

/-! ### Discretion: Propositions 7.1, 7.5 and the noninertial analysis of §3 -/

/-- Woodford (2003), eq. (1.6), p. 471, and p. 511: the average discretionary inflation rate of
§3 (`Noninertial.piDisc`) is the inflation bias (1.6) of §1.1
(`InflationBias.discretionInflation`). -/
theorem piDisc_eq_discretionInflation (β κ lam xs : ℝ) :
    Noninertial.piDisc β κ lam xs = InflationBias.discretionInflation β κ lam xs := by
  unfold Noninertial.piDisc InflationBias.discretionInflation
  ring

/-- Woodford (2003), eq. (2.3), p. 487, and eq. (1.6), p. 471: with no cost-push shocks the
Markov inflation process (2.3) of §2.1 is the constant inflation bias (1.6) of §1.1. -/
theorem infl23_zero_eq_bias (β κ lam xs : ℝ) (t : ℕ) (ω : Ω) :
    Discretion.infl23 𝔼 β κ lam xs (fun _ _ => 0) t ω =
      InflationBias.discretionInflation β κ lam xs := by
  rw [Discretion.infl23_zero_shock, ← piDisc_eq_discretionInflation]
  rfl

/-- Woodford (2003), **Proposition 7.5**, p. 487, versus **Proposition 7.1**, pp. 471–472: with
no cost-push shocks the unique discretionary equilibrium of §2.1 (`Discretion.DiscretionEq`) has
inflation constant at the bias (1.6) and output gap `(1 − β)π̄/κ`, the Markov equilibrium of
Proposition 7.1 (`InflationBias.prop_7_1`). -/
theorem discretionEq_zero_shock {β κ lam xs : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (π x : ℕ → Ω → ℝ) :
    Discretion.DiscretionEq 𝔼 β κ lam xs 0 π x ↔
      (∀ t ω, π t ω = InflationBias.discretionInflation β κ lam xs) ∧
        ∀ t ω, x t ω = (1 - β) * InflationBias.discretionInflation β κ lam xs / κ := by
  have hu : ∀ t ω, |(0 : ℕ → Ω → ℝ) t ω| ≤ 0 := fun _ _ => by simp
  have hua : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => by simp
  rw [Discretion.prop_7_5 𝔼 hβ0 hβ1 hκ hlam hu hua]
  have hD : 0 < (1 - β) * lam + κ ^ 2 := by nlinarith [sq_nonneg κ]
  have hI : ∀ t ω, Discretion.infl23 𝔼 β κ lam xs 0 t ω =
      InflationBias.discretionInflation β κ lam xs :=
    fun t ω => infl23_zero_eq_bias 𝔼 β κ lam xs t ω
  have hG : ∀ t ω, Discretion.gap23 𝔼 β κ lam xs 0 t ω =
      (1 - β) * InflationBias.discretionInflation β κ lam xs / κ := by
    intro t ω
    have hD0 : (1 - β) * lam + κ ^ 2 ≠ 0 := hD.ne'
    have hκ0 : κ ≠ 0 := hκ.ne'
    have hl0 : lam ≠ 0 := hlam.ne'
    simp only [Discretion.gap23, hI, InflationBias.discretionInflation]
    rw [eq_div_iff hκ0, div_eq_mul_inv, div_eq_mul_inv]
    have hw : ((1 - β) * lam + κ ^ 2) * ((1 - β) * lam + κ ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hD0
    have hl : lam * lam⁻¹ = 1 := mul_inv_cancel₀ hl0
    linear_combination (-(xs * κ)) * hw + (-(κ ^ 3 * xs * ((1 - β) * lam + κ ^ 2)⁻¹)) * hl
  simp only [funext_iff, hI, hG]

/-- Woodford (2003), eq. (2.2), p. 487: the §3 formalisation of the discretionary condition
(`Noninertial.Discretion`) is the §2.1 one (`Discretion.Solves22`). -/
theorem discretion_iff_solves22 (β κ lam xs : ℝ) (π u : ℕ → Ω → ℝ) :
    Noninertial.Discretion 𝔼 β κ lam xs π u ↔ Discretion.Solves22 𝔼 β κ lam xs u π := by
  simp only [Noninertial.Discretion, Discretion.Solves22, funext_iff, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul]

/-- Woodford (2003), eq. (2.3), p. 487, and pp. 511–512: under AR(1) cost-push shocks
(`|ρ| ≤ 1`) the Markov inflation process (2.3) of §2.1 is the noninertial plan
`π_t = π̄^disc + f_π^disc u_t` of §3. -/
theorem infl23_eq_plan1 {β κ lam xs ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hρ : |ρ| ≤ 1) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u) :
    Discretion.infl23 𝔼 β κ lam xs u =
      Noninertial.plan1 (Noninertial.piDisc β κ lam xs) (Noninertial.fpiDisc β κ lam ρ) u := by
  obtain ⟨M, hM⟩ := hub
  exact (Noninertial.discretion_iff 𝔼 hβ0 hβ1 hκ hlam hρ hu ⟨M, hM⟩
    (Discretion.infl23_bounded 𝔼 hβ0 hβ1 hlam hM)).mp
    ((discretion_iff_solves22 𝔼 β κ lam xs _ u).mpr
      (Discretion.infl23_solves22 𝔼 hβ0 hβ1 hlam hM hu.1))

/-- Woodford (2003), eq. (1.4), p. 471, and pp. 511–512: under AR(1) cost-push shocks the
discretionary output gap of §2.1 is the noninertial plan `x_t = x̄^disc + f_x^disc u_t` of §3. -/
theorem gap23_eq_plan1 {β κ lam xs ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hρ : |ρ| ≤ 1) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u) :
    Discretion.gap23 𝔼 β κ lam xs u =
      Noninertial.plan1 (Noninertial.xDisc β κ lam xs) (Noninertial.fxDisc β κ lam ρ) u := by
  have h := infl23_eq_plan1 𝔼 hβ0 hβ1 hκ hlam hρ hu hub (xs := xs)
  funext t ω
  have h1 := congrFun (congrFun h t) ω
  simp only [Discretion.gap23, h1, Noninertial.plan1, Noninertial.xDisc, Noninertial.fxDisc]
  ring

/-- Woodford (2003), **Proposition 7.11**, p. 510, versus **Proposition 7.5**, p. 487 (the
ranking discussed on pp. 511–512): under AR(1) cost-push shocks with `0 ≤ ρ < 1` and innovations
of constant variance `s > 0`, the optimal noninertial plan has a stabilization loss (3.4) no
larger than that of the discretionary equilibrium (2.3) of §2.1, and strictly smaller when
`ρ > 0` (pull-out property, non-degenerate shocks). -/
theorem oni_lstab_le_discretion (hpo : 𝔼.PullOut) {β κ lam xs ρ s : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hs : 0 < s)
    {u ε : ℕ → Ω → ℝ} (hu : Noninertial.AR1Innov 𝔼 ρ s u ε) (hub : BoundedProc u)
    (hnd : Noninertial.Nondeg1 u) (t₀ : ℕ) (ω : Ω) :
    Noninertial.Lstab12 𝔼 β lam t₀ (Noninertial.plan1 0 (Noninertial.fpiOni β κ lam ρ) u)
        (Noninertial.plan1 0 (Noninertial.fxOni β κ lam ρ) u) ω ≤
      Noninertial.Lstab12 𝔼 β lam t₀ (Discretion.infl23 𝔼 β κ lam xs u)
        (Discretion.gap23 𝔼 β κ lam xs u) ω ∧
    (0 < ρ →
      Noninertial.Lstab12 𝔼 β lam t₀ (Noninertial.plan1 0 (Noninertial.fpiOni β κ lam ρ) u)
        (Noninertial.plan1 0 (Noninertial.fxOni β κ lam ρ) u) ω <
      Noninertial.Lstab12 𝔼 β lam t₀ (Discretion.infl23 𝔼 β κ lam xs u)
        (Discretion.gap23 𝔼 β κ lam xs u) ω) := by
  have hAR := Noninertial.AR1Innov.isAR1 𝔼 hu
  have hρa : |ρ| < 1 := by rw [abs_of_nonneg hρ0]; exact hρ1
  rw [infl23_eq_plan1 𝔼 hβ0 hβ1 hκ hlam hρa.le hAR hub,
    gap23_eq_plan1 𝔼 hβ0 hβ1 hκ hlam hρa.le hAR hub]
  have hβρ : 0 < 1 - β * ρ := by nlinarith
  obtain ⟨c1, c2⟩ := Noninertial.discretion_coeffs (xstar := xs) hβ1 hκ hlam hβρ
  have hAS := Noninertial.plan_AS_of 𝔼 hAR c1 c2
  obtain ⟨-, hall⟩ := Noninertial.prop_7_11_lstab 𝔼 hpo hβ0 hβ1 hκ hlam hρa hs hu hnd t₀ ω
  obtain ⟨hle, heq⟩ := hall _ _ _ _ hAS
  refine ⟨hle, fun hρ => lt_of_le_of_ne hle fun h => ?_⟩
  have h1 := (heq.mp h.symm).1
  have h2 := (Noninertial.fpiDisc_ge_fpiOni hβ0 hβ1 hκ hlam hρ0 hρ1).2.mp h1.symm
  linarith

/-! ### Long-run inflation targets: Propositions 7.2 and 7.3 restated in §3 -/

/-- Woodford (2003), **Proposition 7.2**, p. 475 (restated in §3, p. 513): the deterministic
timeless optimality of a constant target used in §3 (`Noninertial.TimelessOpt12`) holds exactly
when the §1.1 notion (`Timeless.TimelesslyOptimal`, under any expectation system with the
pull-out property) holds: both characterise `π̄ = 0`. -/
theorem timelessOpt12_iff_timelesslyOptimal [Nonempty Ω] (hpo : 𝔼.PullOut) {β κ lam xs : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) (pbar : ℝ) :
    Noninertial.TimelessOpt12 β κ lam xs pbar ↔ Timeless.TimelesslyOptimal 𝔼 β κ lam xs pbar := by
  rw [Noninertial.timelessOpt12_iff hβ0 hβ1 hκ hlam, Timeless.prop_7_2 𝔼 hpo hβ0 hβ1 hκ hlam]

/-- Woodford (2003), eq. (1.19), p. 478, and eq. (3.11), p. 513: the long-run inflation rate of
§3 (`Noninertial.piBar119`, with the interest target `i*`) is the one of §1.2
(`MonetaryFrictions.piBar` of the basic model, with `iᵐ = i*`). -/
theorem piBar119_eq_piBar_basic (β κ σ rbar lx li xs im : ℝ) :
    Noninertial.piBar119 β li rbar im =
      MonetaryFrictions.piBar (MonetaryFrictions.basic β κ σ rbar lx li xs im) := by
  rw [MonetaryFrictions.piBar_basic, Noninertial.piBar119]
  ring

/-- Woodford (2003), **Proposition 7.3**, p. 478 (restated in §3, (3.11), p. 513): the §3
formalisation of timeless optimality with transactions frictions (`Noninertial.TimelessOpt114`)
agrees with the §1.2 one (`MonetaryFrictions.TimelesslyOptimal` for the basic model): a constant
inflation rate `π̄` is timelessly optimal in the first sense iff the constant plan
`(π̄, (1 − β)π̄/κ, r̄ + π̄)` is timelessly optimal in the second. -/
theorem timelessOpt114_iff_basic {β κ σ rbar lx li xs im : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 ≤ li) (πb : ℝ) :
    Noninertial.TimelessOpt114 β κ σ rbar lx li xs im πb ↔
      MonetaryFrictions.TimelesslyOptimal (MonetaryFrictions.basic β κ σ rbar lx li xs im) πb
        ((1 - β) * πb / κ) (rbar + πb) := by
  rw [Noninertial.timelessOpt114_iff hβ0 hβ1 hκ hσ hlx hli,
    MonetaryFrictions.prop_7_3 hβ0 hβ1 hκ hσ hlx.le hli, piBar119_eq_piBar_basic β κ σ rbar lx li
      xs im, MonetaryFrictions.piBar_basic]
  simp

/-! ### Natural-rate disturbances: §2.2 versus §4 -/

/-- Woodford (2003), **Proposition 7.14**, p. 518, versus p. 501: with no cost-push shocks (and
no pre-`t₀` history of them) the optimal instrument path (4.2) is `i_t = rⁿ_t`, with zero
inflation and output gap: the zero-gap policy of §2.2, which satisfies the IS relation (2.23). -/
theorem instrumentPath_no_costPush (β κ lam σ ρ : ℝ) (rn : ℕ → Ω → ℝ) :
    InstrumentPath.piPath β κ lam ρ (0 : ℕ → Ω → ℝ) 0 = 0 ∧
      InstrumentPath.xPath β κ lam ρ (0 : ℕ → Ω → ℝ) 0 = 0 ∧
      InstrumentPath.iPath β κ lam σ ρ 0 0 rn = rn ∧
      NaturalRateCommitment.IS 𝔼 σ rn (InstrumentPath.piPath β κ lam ρ 0 0)
        (InstrumentPath.xPath β κ lam ρ 0 0) (InstrumentPath.iPath β κ lam σ ρ 0 0 rn) := by
  have hS : ∀ m t ω, InstrumentPath.histSum m (0 : ℕ → Ω → ℝ) 0 t ω = 0 := by
    intro m t ω
    simp [InstrumentPath.histSum, InstrumentPath.histU]
  have h1 : InstrumentPath.piPath β κ lam ρ (0 : ℕ → Ω → ℝ) 0 = 0 := by
    funext t ω
    simp [InstrumentPath.piPath, hS]
  have h2 : InstrumentPath.xPath β κ lam ρ (0 : ℕ → Ω → ℝ) 0 = 0 := by
    funext t ω
    simp [InstrumentPath.xPath, hS]
  have h3 : InstrumentPath.iPath β κ lam σ ρ (0 : ℕ → Ω → ℝ) 0 rn = rn := by
    funext t ω
    simp [InstrumentPath.iPath, hS]
  refine ⟨h1, h2, h3, ?_⟩
  rw [h1, h2, h3]
  exact (NaturalRateCommitment.zero_gap_feasible 𝔼 β κ σ rn).2

/-- Woodford (2003), p. 501 (zero inflation and output gap is the *unique* optimum when the loss
is (1.2) with `x* = 0`), extended from perfect foresight
(`NaturalRateCommitment.zero_gap_unique_pf`) to every faithful expectation system (in particular
every finite event tree, `finiteTree_faithful`): a bounded plan with zero expected discounted
loss is zero. -/
theorem zero_gap_unique_faithful (hf : TargetingRule.Faithful 𝔼) {β lam : ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hlam : 0 < lam) {π x : ℕ → Ω → ℝ} (hπ : BoundedProc π) (hx : BoundedProc x)
    (h0 : ∀ ω,
      𝔼.E 0 (fun ω' => ∑' k, β ^ k * (π (0 + k) ω' ^ 2 + lam * x (0 + k) ω' ^ 2)) ω = 0) :
    π = 0 ∧ x = 0 := by
  refine TargetingRule.eq_zero_of_loss_eq_zero 𝔼 hβ hβ1 hlam hf hπ hx fun ω => ?_
  rw [targetingRule_loss_eq 𝔼 hβ.le hβ1 hπ hx]
  simpa [DateZeroCommitment.loss] using h0 ω

end Woodford.GainsFromCommitment.Links
