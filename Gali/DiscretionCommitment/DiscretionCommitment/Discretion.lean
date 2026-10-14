/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DiscretionCommitment.LossAndCostPush

/-!
# Optimal discretionary policy

Galí (2015), Chapter 5, §5.2.1 (pp. 129–133). The central bank minimises
`E_0 ∑ βᵗ (π_t² + ϑ x_t²)` subject to (2) `π_t = β E_t π_{t+1} + κ x_t + u_t`, with the
cost-push shock `u` an AR(1) (3) with `ρ_u ∈ [0, 1)`, but cannot commit.

## The period problem and the targeting rule (4)

* `period_problem_iff`: `(π, x)` minimises `π² + ϑ x²` on the line `π = κ x + υ` iff
  `x = −(κ/ϑ) π` (necessary and sufficient, `ϑ > 0`); `period_solution` gives the unique
  minimiser.
* `discretionEq_iff`: a discretionary equilibrium (the NKPC and, date by date and state by
  state, the period problem solved taking `υ_t = β E_t π_{t+1} + u_t` as given) is exactly the
  NKPC together with the targeting rule (4).

## The equilibrium (5)–(6)

* `inflation_forward`: under (4), `π_t = a E_t π_{t+1} + (ϑ/(ϑ+κ²)) u_t`,
  `a = ϑβ/(ϑ+κ²) ∈ [0, 1)`.
* `discretion_iff_forwardSeries`: for any bounded adapted `u`, the bounded adapted
  discretionary equilibrium exists and is unique: `π_t = ∑ aᵏ E_t[(ϑ/(ϑ+κ²)) u_{t+k}]`.
* `discretionEq_iff_msv`, `discretion_msv_isEq`: with AR(1) `u`, the unique bounded adapted
  equilibrium is (5) `π = ϑ/(κ² + ϑ(1 − βρ_u)) u`, (6) `x = −κ/(κ² + ϑ(1 − βρ_u)) u`.

## Dampening (p. 131)

* `zeroGap_iff`: holding `x ≡ 0`, the unique bounded inflation is `u/(1 − βρ_u)`.
* `psiPi_lt`, `dampening`: the discretionary inflation response is positive and strictly
  smaller in absolute value at every horizon `E_t π_{t+k}` where the shock matters.
* `expected_priceLevel_hasSum`, `priceLevel_response_strictMonoOn`: the cumulated (expected)
  inflation, i.e. the permanent change in the price level, is `Ψ_π u_t/(1 − ρ_u)` and is
  strictly increasing in the persistence `ρ_u`.

## Implementation (7)–(10)

* `dis_welfareGap_iff`: the DIS in the natural gap with `r^n` is equivalent to (7), the DIS in
  the welfare-relevant gap with the efficient rate `r^e`; `efficientRate_eq`:
  `σ E_t Δy^e_{t+1} = −σ(1 − ρ_a) ψ_ya a_t`.
* `interestRate_iff`, `psiI_pos`: (8) `i_t = r^e_t + Ψ_i u_t`, `Ψ_i > 0`.
* `rule8_iff_solves`, `AO_eigenvalues`, `AO_not_schurStable`, `rule8_indeterminate`: the
  "rule" (8) gives (9) with exactly one eigenvalue of `A_O` outside the unit circle, hence a
  bounded equilibrium other than the discretionary one.
* `rule10_eq`, `rule10_iff_solves`, `AT_schurStable_iff`, `rule10_implements`,
  `rule10_indeterminate`: (10) `i_t = r^e_t + Ψ'_i u_t + φ_π π_t` implements the
  discretionary equilibrium as the unique bounded equilibrium iff `φ_π > 1` (for `φ_π ≥ 0`).
-/

namespace Gali.DiscretionCommitment.Discretion

open Filter Topology Gali.DiscretionCommitment.LossAndCostPush

/-! ### The period problem (p. 129) -/

/-- Galí (2015), p. 129: the period objective as a function of the output gap `x`, after
substituting the constraint `π = κ x + υ`: `(κ x + υ)² + ϑ x²`. -/
def periodObj (κ ϑ υ x : ℝ) : ℝ := (κ * x + υ) ^ 2 + ϑ * x ^ 2

/-- Galí (2015), p. 130 (completing the square): the change of the period objective is
`(κ² + ϑ)(x' − x)² + 2 (x' − x)((κ² + ϑ) x + κ υ)`. -/
theorem periodObj_sub (κ ϑ υ x x' : ℝ) :
    periodObj κ ϑ υ x' - periodObj κ ϑ υ x
      = (κ ^ 2 + ϑ) * (x' - x) ^ 2 + 2 * (x' - x) * ((κ ^ 2 + ϑ) * x + κ * υ) := by
  unfold periodObj
  ring

/-- Galí (2015), eq. (4), p. 130 (**necessary and sufficient**): for `ϑ > 0`, `x` minimises
the period objective iff the targeting rule `x = −(κ/ϑ)(κ x + υ)` holds. -/
theorem periodObj_isMinOn_iff {κ ϑ υ x : ℝ} (hϑ : 0 < ϑ) :
    IsMinOn (periodObj κ ϑ υ) Set.univ x ↔ x = -(κ / ϑ) * (κ * x + υ) := by
  have hA : 0 < κ ^ 2 + ϑ := by positivity
  have hfoc : x = -(κ / ϑ) * (κ * x + υ) ↔ (κ ^ 2 + ϑ) * x + κ * υ = 0 := by
    constructor
    · intro h
      field_simp at h
      linarith
    · intro h
      field_simp
      linarith
  rw [hfoc]
  constructor
  · intro h
    set g := (κ ^ 2 + ϑ) * x + κ * υ
    have hle := h (Set.mem_univ (x - g / (κ ^ 2 + ϑ)))
    simp only [Set.mem_ofPred_eq] at hle
    have hd := periodObj_sub κ ϑ υ x (x - g / (κ ^ 2 + ϑ))
    have hval : (κ ^ 2 + ϑ) * (x - g / (κ ^ 2 + ϑ) - x) ^ 2 +
        2 * (x - g / (κ ^ 2 + ϑ) - x) * g = -(g ^ 2 / (κ ^ 2 + ϑ)) := by
      field_simp
      ring
    have hg2 : g ^ 2 / (κ ^ 2 + ϑ) ≤ 0 := by linarith
    have : g ^ 2 ≤ 0 := by
      rwa [div_le_iff₀ hA, zero_mul] at hg2
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg g))
  · intro h x' _
    have hd := periodObj_sub κ ϑ υ x x'
    rw [h, mul_zero, add_zero] at hd
    have : 0 ≤ (κ ^ 2 + ϑ) * (x' - x) ^ 2 := by positivity
    simp only [Set.mem_ofPred_eq]
    linarith

/-- Galí (2015), p. 129 and eq. (4), p. 130 (**the period problem, necessary and
sufficient**): for `ϑ > 0`, `(π, x)` minimises `π² + ϑ x²` subject to `π = κ x + υ` iff it is
feasible and satisfies the targeting rule `x = −(κ/ϑ) π`. -/
theorem period_problem_iff {κ ϑ υ π x : ℝ} (hϑ : 0 < ϑ) :
    (π = κ * x + υ ∧ ∀ π' x', π' = κ * x' + υ → π ^ 2 + ϑ * x ^ 2 ≤ π' ^ 2 + ϑ * x' ^ 2) ↔
      (π = κ * x + υ ∧ x = -(κ / ϑ) * π) := by
  constructor
  · rintro ⟨hc, hmin⟩
    refine ⟨hc, ?_⟩
    have : IsMinOn (periodObj κ ϑ υ) Set.univ x := fun x' _ => by
      have := hmin _ x' rfl
      rw [hc] at this
      simpa [periodObj] using this
    rw [hc]
    exact (periodObj_isMinOn_iff hϑ).mp this
  · rintro ⟨hc, hx⟩
    refine ⟨hc, fun π' x' hc' => ?_⟩
    rw [hc] at hx
    have := (periodObj_isMinOn_iff hϑ).mpr hx (Set.mem_univ x')
    simp only [Set.mem_ofPred_eq, periodObj] at this
    rw [hc, hc']
    exact this

/-- Galí (2015), pp. 129–130: the unique solution of the period problem,
`x = −κ υ/(κ² + ϑ)`, `π = ϑ υ/(κ² + ϑ)`. -/
theorem period_solution {κ ϑ υ π x : ℝ} (hϑ : 0 < ϑ) :
    (π = κ * x + υ ∧ x = -(κ / ϑ) * π) ↔
      (x = -κ * υ / (κ ^ 2 + ϑ) ∧ π = ϑ * υ / (κ ^ 2 + ϑ)) := by
  have hA : κ ^ 2 + ϑ ≠ 0 := by positivity
  constructor
  · rintro ⟨hc, hx⟩
    have hx' : (κ ^ 2 + ϑ) * x = -κ * υ := by
      field_simp at hx
      rw [hc] at hx
      linarith
    have hxv : x = -κ * υ / (κ ^ 2 + ϑ) := by
      field_simp
      linarith
    refine ⟨hxv, ?_⟩
    rw [hc, hxv]
    field_simp
    ring
  · rintro ⟨hx, hp⟩
    constructor
    · rw [hx, hp]
      field_simp
      ring
    · rw [hx, hp]
      field_simp

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The discretionary equilibrium -/

/-- Galí (2015), eq. (4), p. 130: the targeting rule `x_t = −(κ/ϑ) π_t` at every date. -/
def TargetingRule (κ ϑ : ℝ) (x infl : ℕ → Ω → ℝ) : Prop := ∀ t, x t = (-(κ / ϑ)) • infl t

/-- Galí (2015), §5.2.1, pp. 129–130: a **discretionary equilibrium**. The NKPC (2) holds and,
at each date and in each state, `(π_t, x_t)` solves the period problem: it minimises
`π² + ϑ x²` over the line `π = κ x + υ_t`, taking `υ_t = β E_t π_{t+1} + u_t` as given. -/
def DiscretionEq (β κ ϑ : ℝ) (u x infl : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β κ x u infl ∧ ∀ t ω, ∀ π' x' : ℝ,
    π' = κ * x' + (β * 𝔼.E t (infl (t + 1)) ω + u t ω) →
      infl t ω ^ 2 + ϑ * x t ω ^ 2 ≤ π' ^ 2 + ϑ * x' ^ 2

/-- Galí (2015), p. 130: for `ϑ > 0` a discretionary equilibrium is exactly a pair satisfying
the NKPC (2) and the targeting rule (4). -/
theorem discretionEq_iff {β κ ϑ : ℝ} (hϑ : 0 < ϑ) {u x infl : ℕ → Ω → ℝ} :
    DiscretionEq 𝔼 β κ ϑ u x infl ↔ NKPC 𝔼 β κ x u infl ∧ TargetingRule κ ϑ x infl := by
  have hpt : ∀ (h : NKPC 𝔼 β κ x u infl) t ω,
      infl t ω = κ * x t ω + (β * 𝔼.E t (infl (t + 1)) ω + u t ω) := fun h t ω => by
    have := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  constructor
  · rintro ⟨h, hmin⟩
    refine ⟨h, fun t => funext fun ω => ?_⟩
    have := ((period_problem_iff hϑ).mp ⟨hpt h t ω, hmin t ω⟩).2
    simpa using this
  · rintro ⟨h, hr⟩
    refine ⟨h, fun t ω => ((period_problem_iff hϑ).mpr ⟨hpt h t ω, ?_⟩).2⟩
    have := congrFun (hr t) ω
    simpa using this

/-- Galí (2015), p. 130: the discount factor of the discretionary inflation equation,
`a = ϑβ/(ϑ + κ²)`. -/
noncomputable def aDisc (β κ ϑ : ℝ) : ℝ := ϑ * β / (ϑ + κ ^ 2)

/-- Galí (2015), p. 130: `0 ≤ a < 1` for `ϑ > 0`, `0 ≤ β < 1`. -/
theorem aDisc_mem {β κ ϑ : ℝ} (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    0 ≤ aDisc β κ ϑ ∧ aDisc β κ ϑ < 1 := by
  unfold aDisc
  have hA : 0 < ϑ + κ ^ 2 := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hA]
  nlinarith [sq_nonneg κ]

/-- Galí (2015), p. 130, unnumbered display: under the targeting rule (4) the NKPC becomes
`π_t = (ϑβ/(ϑ + κ²)) E_t π_{t+1} + (ϑ/(ϑ + κ²)) u_t`. Conversely, this equation together
with (4) gives back the NKPC. -/
theorem inflation_forward_iff {β κ ϑ : ℝ} (hϑ : 0 < ϑ) {u x infl : ℕ → Ω → ℝ}
    (hr : TargetingRule κ ϑ x infl) :
    NKPC 𝔼 β κ x u infl ↔
      ∀ t, infl t = aDisc β κ ϑ • 𝔼.E t (infl (t + 1)) + (ϑ / (ϑ + κ ^ 2)) • u t := by
  have hA : ϑ + κ ^ 2 ≠ 0 := by positivity
  have hϑ' : ϑ ≠ 0 := hϑ.ne'
  constructor
  · intro h t
    funext ω
    have p := congrFun (h t) ω
    have r := congrFun (hr t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at p r ⊢
    rw [r] at p
    unfold aDisc
    field_simp
    field_simp at p
    linarith
  · intro h t
    funext ω
    have p := congrFun (h t) ω
    have r := congrFun (hr t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at p r ⊢
    rw [r]
    unfold aDisc at p
    field_simp at p
    field_simp
    linarith

/-- Galí (2015), p. 130: the forward series of a bounded process is adapted (`E_t` leaves
`∑ aᵏ E_t u_{t+k}` unchanged). A general lemma not in the core. -/
theorem forwardSeries_adapted {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) : 𝔼.Adapted (𝔼.forwardSeries a u) := by
  intro t
  funext ω
  have hb : ∀ k ω', |a ^ k * 𝔼.E t (u (t + k)) ω'| ≤ a ^ k * M := by
    intro k ω'
    rw [abs_mul, abs_pow, abs_of_nonneg ha0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (t + k)) t ω') (pow_nonneg ha0 k)
  change 𝔼.E t (fun ω' => ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω') ω =
    ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω
  rw [𝔼.E_tsum ha0 ha1 hb t ω]
  refine tsum_congr fun k => ?_
  change 𝔼.E t (a ^ k • 𝔼.E t (u (t + k))) ω = _
  rw [map_smul, 𝔼.E_E_self]
  rfl

/-- Galí (2015), eqs. (4)–(5), p. 130 (**existence and uniqueness, general shocks**): for
`ϑ > 0`, `0 ≤ β < 1` and bounded adapted `u`, bounded adapted `(x, π)` form a discretionary
equilibrium iff `π_t = ∑_{k ≥ 0} aᵏ E_t[(ϑ/(ϑ + κ²)) u_{t+k}]` (`a = ϑβ/(ϑ + κ²)`) and
`x = −(κ/ϑ) π` (only boundedness of `π` is needed for uniqueness). -/
theorem discretion_iff_forwardSeries {β κ ϑ M : ℝ} (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {u x infl : ℕ → Ω → ℝ} (hub : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u)
    (hpb : BoundedProc infl) :
    DiscretionEq 𝔼 β κ ϑ u x infl ↔
      infl = 𝔼.forwardSeries (aDisc β κ ϑ) (fun t => (ϑ / (ϑ + κ ^ 2)) • u t) ∧
        x = fun t => (-(κ / ϑ)) • infl t := by
  obtain ⟨ha0, ha1⟩ := aDisc_mem (κ := κ) hϑ hβ0 hβ1
  set c := ϑ / (ϑ + κ ^ 2)
  have hcb : ∀ t ω, |(c • u t) ω| ≤ |c| * M := fun t ω => by
    rw [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hub t ω) (abs_nonneg c)
  have hca : 𝔼.Adapted fun t => c • u t := fun t => by rw [map_smul, hua t]
  rw [discretionEq_iff 𝔼 hϑ]
  constructor
  · rintro ⟨h, hr⟩
    have hf := (inflation_forward_iff 𝔼 hϑ hr).mp h
    exact ⟨𝔼.eq_forwardSeries ha0 ha1 hcb hca hf hpb, funext hr⟩
  · rintro ⟨hp, hx⟩
    have hr : TargetingRule κ ϑ x infl := fun t => by rw [hx]
    refine ⟨(inflation_forward_iff 𝔼 hϑ hr).mpr fun t => ?_, hr⟩
    rw [hp]
    exact 𝔼.forwardSeries_solves ha0 ha1 hcb hca t

/-- Galí (2015), eq. (5), p. 130 (**existence, general shocks**): for bounded adapted `u` the
forward-series pair is a bounded adapted discretionary equilibrium. -/
theorem discretion_forwardSeries_isEq {β κ ϑ M : ℝ} (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {u : ℕ → Ω → ℝ} (hub : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) :
    let infl := 𝔼.forwardSeries (aDisc β κ ϑ) (fun t => (ϑ / (ϑ + κ ^ 2)) • u t)
    DiscretionEq 𝔼 β κ ϑ u (fun t => (-(κ / ϑ)) • infl t) infl ∧
      BoundedProc infl ∧ 𝔼.Adapted infl ∧
      BoundedProc (fun t => (-(κ / ϑ)) • infl t) ∧ 𝔼.Adapted (fun t => (-(κ / ϑ)) • infl t) := by
  intro infl
  obtain ⟨ha0, ha1⟩ := aDisc_mem (κ := κ) hϑ hβ0 hβ1
  set c := ϑ / (ϑ + κ ^ 2)
  have hcb : ∀ t ω, |(c • u t) ω| ≤ |c| * M := fun t ω => by
    rw [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hub t ω) (abs_nonneg c)
  have hpb : BoundedProc infl := 𝔼.forwardSeries_bounded ha0 ha1 hcb
  have hpa : 𝔼.Adapted infl := forwardSeries_adapted 𝔼 ha0 ha1 hcb
  obtain ⟨B, hB⟩ := hpb
  have hxb : BoundedProc (fun t => (-(κ / ϑ)) • infl t) := ⟨|κ / ϑ| * B, fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hB t ω) (abs_nonneg _)⟩
  refine ⟨(discretion_iff_forwardSeries 𝔼 hϑ hβ0 hβ1 hub hua ⟨B, hB⟩).mpr ⟨rfl, rfl⟩,
    ⟨B, hB⟩, hpa, hxb, fun t => by rw [map_smul, hpa t]⟩

/-! ### The MSV solution with AR(1) cost-push shocks: (5) and (6) -/

/-- Galí (2015), eq. (5), p. 130: `Ψ_π = ϑ/(κ² + ϑ(1 − βρ_u))`. -/
noncomputable def psiPi (β κ ϑ ρ : ℝ) : ℝ := ϑ / (κ ^ 2 + ϑ * (1 - β * ρ))

/-- Galí (2015), eq. (6), p. 130: `Ψ_x = −κ/(κ² + ϑ(1 − βρ_u))`. -/
noncomputable def psiX (β κ ϑ ρ : ℝ) : ℝ := -κ / (κ ^ 2 + ϑ * (1 - β * ρ))

/-- Galí (2015), p. 130: the common denominator `κ² + ϑ(1 − βρ_u)` is positive. -/
theorem den_pos {β κ ϑ ρ : ℝ} (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ1 : ρ < 1) :
    0 < κ ^ 2 + ϑ * (1 - β * ρ) := by
  have : β * ρ < 1 := by nlinarith
  have : 0 < ϑ * (1 - β * ρ) := mul_pos hϑ (by linarith)
  positivity

/-- Galí (2015), eqs. (4)–(6), p. 130: `Ψ_x = −(κ/ϑ) Ψ_π`. -/
theorem psiX_eq {β κ ϑ ρ : ℝ} (hϑ : ϑ ≠ 0) : psiX β κ ϑ ρ = -(κ / ϑ) * psiPi β κ ϑ ρ := by
  unfold psiX psiPi
  field_simp

/-- Galí (2015), eq. (5), p. 130: `Ψ_π = (ϑ/(ϑ+κ²))/(1 − aρ_u)` with `a = ϑβ/(ϑ+κ²)`: the
forward solution of the inflation equation for an AR(1) shock. -/
theorem psiPi_eq_forward {β κ ϑ ρ : ℝ} (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hρ1 : ρ < 1) :
    psiPi β κ ϑ ρ = (1 - aDisc β κ ϑ * ρ)⁻¹ * (ϑ / (ϑ + κ ^ 2)) := by
  have hA : ϑ + κ ^ 2 ≠ 0 := by positivity
  have hD := den_pos (κ := κ) hϑ hβ0 hβ1 hρ1
  have h1 : 1 - aDisc β κ ϑ * ρ ≠ 0 := by
    unfold aDisc
    rw [div_mul_eq_mul_div, one_sub_div hA]
    exact div_ne_zero (by nlinarith) hA
  unfold psiPi
  rw [eq_inv_mul_iff_mul_eq₀ h1]
  unfold aDisc
  field_simp
  ring

/-- Galí (2015), eqs. (5)–(6), p. 130 (**existence**): with AR(1) cost-push shocks, the MSV
pair `π = Ψ_π u`, `x = Ψ_x u` is a discretionary equilibrium. -/
theorem discretion_msv_isEq {β κ ϑ ρ : ℝ} (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hρ1 : ρ < 1) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) :
    DiscretionEq 𝔼 β κ ϑ u (fun t => psiX β κ ϑ ρ • u t) (fun t => psiPi β κ ϑ ρ • u t) := by
  have hr : TargetingRule κ ϑ (fun t => psiX β κ ϑ ρ • u t) (fun t => psiPi β κ ϑ ρ • u t) :=
    fun t => by rw [psiX_eq hϑ.ne', smul_smul]
  rw [discretionEq_iff 𝔼 hϑ, inflation_forward_iff 𝔼 hϑ hr]
  refine ⟨fun t => ?_, hr⟩
  rw [map_smul, hu.2 t, smul_smul]
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [psiPi_eq_forward hϑ hβ0 hβ1 hρ1]
  have hA : ϑ + κ ^ 2 ≠ 0 := by positivity
  have h1 : 1 - aDisc β κ ϑ * ρ ≠ 0 := by
    have := psiPi_eq_forward (κ := κ) hϑ hβ0 hβ1 hρ1
    intro h0
    rw [h0, inv_zero, zero_mul] at this
    have hD := den_pos (κ := κ) hϑ hβ0 hβ1 hρ1
    unfold psiPi at this
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · exact hϑ.ne' h
    · exact hD.ne' h
  field_simp
  ring

/-- Galí (2015), eqs. (5)–(6), p. 130 (**existence and uniqueness among bounded processes**):
with a bounded AR(1) cost-push shock (`0 ≤ ρ_u < 1`), bounded adapted `(x, π)` form a
discretionary equilibrium iff `π = ϑ/(κ² + ϑ(1 − βρ_u)) u` and
`x = −κ/(κ² + ϑ(1 − βρ_u)) u`. -/
theorem discretionEq_iff_msv {β κ ϑ ρ : ℝ} (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hρ1 : ρ < 1) {u x infl : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u)
    (hub : BoundedProc u) (hxb : BoundedProc x) (hpb : BoundedProc infl) :
    DiscretionEq 𝔼 β κ ϑ u x infl ↔
      infl = (fun t => psiPi β κ ϑ ρ • u t) ∧ x = (fun t => psiX β κ ϑ ρ • u t) := by
  obtain ⟨ha0, ha1⟩ := aDisc_mem (κ := κ) hϑ hβ0 hβ1
  have ha : |aDisc β κ ϑ| < 1 := by rw [abs_of_nonneg ha0]; exact ha1
  obtain ⟨M, hM⟩ := hub
  have hmsvb : BoundedProc (fun t => psiPi β κ ϑ ρ • u t) := ⟨|psiPi β κ ϑ ρ| * M,
    fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)⟩
  have hmsv := discretion_msv_isEq 𝔼 (κ := κ) hϑ hβ0 hβ1 hρ1 hu
  constructor
  · intro h
    obtain ⟨hn, hr⟩ := (discretionEq_iff 𝔼 hϑ).mp h
    obtain ⟨hn', hr'⟩ := (discretionEq_iff 𝔼 hϑ).mp hmsv
    have hf := (inflation_forward_iff 𝔼 hϑ hr).mp hn
    have hf' := (inflation_forward_iff 𝔼 hϑ hr').mp hn'
    have hp : infl = fun t => psiPi β κ ϑ ρ • u t := 𝔼.forward_unique ha hf hf' hpb hmsvb
    refine ⟨hp, funext fun t => ?_⟩
    simp only [hr t, hp, psiX_eq hϑ.ne', smul_smul]
  · rintro ⟨rfl, rfl⟩
    exact hmsv

/-! ### Dampening relative to `x ≡ 0` (p. 131) -/

/-- Galí (2015), p. 131: if the output gap were held at zero, the NKPC
`π_t = β E_t π_{t+1} + u_t` would have the unique bounded adapted solution
`π_t = u_t/(1 − βρ_u)`. -/
theorem zeroGap_iff {β κ ρ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ1 : ρ < 1)
    {u infl : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u) (hpb : BoundedProc infl) :
    NKPC 𝔼 β κ 0 u infl ↔ infl = fun t => (1 - β * ρ)⁻¹ • u t := by
  have hβρ : β * ρ < 1 := by nlinarith
  have hne : 1 - β * ρ ≠ 0 := by linarith
  have ha : |β| < 1 := by rw [abs_of_nonneg hβ0]; exact hβ1
  have hiff : NKPC 𝔼 β κ 0 u infl ↔ ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + u t := by
    unfold NKPC
    simp only [Pi.zero_apply, smul_zero, add_zero]
  obtain ⟨M, hM⟩ := hub
  have hcb : BoundedProc (fun t => (1 - β * ρ)⁻¹ • u t) := ⟨|(1 - β * ρ)⁻¹| * M,
    fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)⟩
  have hsol : ∀ t, (1 - β * ρ)⁻¹ • u t =
      β • 𝔼.E t ((1 - β * ρ)⁻¹ • u (t + 1)) + u t := 𝔼.forward_ar1_solves hne hu
  rw [hiff]
  constructor
  · intro h
    exact 𝔼.forward_unique ha h hsol hpb hcb
  · rintro rfl
    exact hsol

/-- Galí (2015), p. 131 (**dampening**): for `κ ≠ 0`, `ϑ > 0`,
`0 < ϑ/(κ² + ϑ(1 − βρ_u)) < 1/(1 − βρ_u)`. -/
theorem psiPi_lt {β κ ϑ ρ : ℝ} (hκ : κ ≠ 0) (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hρ1 : ρ < 1) :
    0 < psiPi β κ ϑ ρ ∧ psiPi β κ ϑ ρ < (1 - β * ρ)⁻¹ := by
  have hD := den_pos (κ := κ) hϑ hβ0 hβ1 hρ1
  have hβρ : 0 < 1 - β * ρ := by nlinarith
  have hk : 0 < κ ^ 2 := by positivity
  refine ⟨div_pos hϑ hD, ?_⟩
  unfold psiPi
  rw [div_lt_iff₀ hD, inv_mul_eq_div, lt_div_iff₀ hβρ]
  nlinarith

/-- Galí (2015), p. 131 (**dampening at all horizons**): let `π^d = Ψ_π u` be discretionary
inflation and `π⁰ = u/(1 − βρ_u)` inflation with the gap held at zero. Then for every date
`t`, horizon `k` and state, `E_t π^d_{t+k} = Ψ_π ρ_uᵏ u_t` and `E_t π⁰_{t+k} = ρ_uᵏ u_t/(1 − βρ_u)`
have the same sign, `|E_t π^d_{t+k}| ≤ |E_t π⁰_{t+k}|`, and the inequality is strict whenever
`ρ_uᵏ u_t ≠ 0`. -/
theorem dampening {β κ ϑ ρ : ℝ} (hκ : κ ≠ 0) (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hρ1 : ρ < 1) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (t k : ℕ) (ω : Ω) :
    𝔼.E t (psiPi β κ ϑ ρ • u (t + k)) ω = psiPi β κ ϑ ρ * (ρ ^ k * u t ω) ∧
      𝔼.E t ((1 - β * ρ)⁻¹ • u (t + k)) ω = (1 - β * ρ)⁻¹ * (ρ ^ k * u t ω) ∧
      0 ≤ 𝔼.E t (psiPi β κ ϑ ρ • u (t + k)) ω * 𝔼.E t ((1 - β * ρ)⁻¹ • u (t + k)) ω ∧
      |𝔼.E t (psiPi β κ ϑ ρ • u (t + k)) ω| ≤ |𝔼.E t ((1 - β * ρ)⁻¹ • u (t + k)) ω| ∧
      (ρ ^ k * u t ω ≠ 0 →
        |𝔼.E t (psiPi β κ ϑ ρ • u (t + k)) ω| < |𝔼.E t ((1 - β * ρ)⁻¹ • u (t + k)) ω|) := by
  obtain ⟨h0, h1⟩ := psiPi_lt hκ hϑ hβ0 hβ1 hρ1
  have e1 : 𝔼.E t (psiPi β κ ϑ ρ • u (t + k)) ω = psiPi β κ ϑ ρ * (ρ ^ k * u t ω) := by
    rw [map_smul, 𝔼.ar1_iterate hu t k]
    simp
  have e2 : 𝔼.E t ((1 - β * ρ)⁻¹ • u (t + k)) ω = (1 - β * ρ)⁻¹ * (ρ ^ k * u t ω) := by
    rw [map_smul, 𝔼.ar1_iterate hu t k]
    simp
  have hpos : 0 < (1 - β * ρ)⁻¹ := h0.trans h1
  refine ⟨e1, e2, ?_, ?_, fun hne => ?_⟩
  · rw [e1, e2]
    have : 0 ≤ psiPi β κ ϑ ρ * (1 - β * ρ)⁻¹ * (ρ ^ k * u t ω) ^ 2 := by positivity
    nlinarith
  · rw [e1, e2, abs_mul (psiPi β κ ϑ ρ), abs_mul (1 - β * ρ)⁻¹, abs_of_pos h0,
      abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_right h1.le (abs_nonneg _)
  · rw [e1, e2, abs_mul (psiPi β κ ϑ ρ), abs_mul (1 - β * ρ)⁻¹, abs_of_pos h0,
      abs_of_pos hpos]
    exact mul_lt_mul_of_pos_right h1 (abs_pos.mpr hne)

/-- Galí (2015), pp. 131–132 (**a permanent change in the price level**): under discretion the
expected cumulated inflation from date `t` on, `∑_{k ≥ 0} E_t π_{t+k}`, converges to
`Ψ_π u_t/(1 − ρ_u)`: the (expected) price level shifts permanently. -/
theorem expected_priceLevel_hasSum {β κ ϑ ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (t : ℕ) (ω : Ω) :
    HasSum (fun k => 𝔼.E t (psiPi β κ ϑ ρ • u (t + k)) ω)
      (psiPi β κ ϑ ρ / (1 - ρ) * u t ω) := by
  have h := ((hasSum_geometric_of_lt_one hρ0 hρ1).mul_left (psiPi β κ ϑ ρ * u t ω))
  convert h using 1
  · funext k
    rw [map_smul, 𝔼.ar1_iterate hu t k]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · field_simp

/-- Galí (2015), p. 132 (**the size of the price-level shift increases with persistence**):
for `κ ≠ 0`, `ϑ > 0`, `0 ≤ β < 1`, the long-run price-level response to a unit cost-push shock,
`Ψ_π(ρ_u)/(1 − ρ_u) = ϑ/((κ² + ϑ(1 − βρ_u))(1 − ρ_u))`, is strictly increasing in
`ρ_u ∈ [0, 1)`. -/
theorem priceLevel_response_strictMonoOn {β κ ϑ : ℝ} (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) :
    StrictMonoOn (fun ρ => psiPi β κ ϑ ρ / (1 - ρ)) (Set.Ico 0 1) := by
  intro ρ₁ h₁ ρ₂ h₂ hlt
  obtain ⟨h₁0, h₁1⟩ := h₁
  obtain ⟨h₂0, h₂1⟩ := h₂
  have hD₁ := den_pos (κ := κ) hϑ hβ0 hβ1 h₁1
  have hD₂ := den_pos (κ := κ) hϑ hβ0 hβ1 h₂1
  have hg₂ : 0 < (κ ^ 2 + ϑ * (1 - β * ρ₂)) * (1 - ρ₂) := mul_pos hD₂ (by linarith)
  simp only [psiPi, div_div]
  apply div_lt_div_of_pos_left hϑ hg₂
  have hk : 0 ≤ κ ^ 2 := sq_nonneg κ
  have hb : 0 ≤ ϑ * β := mul_nonneg hϑ.le hβ0
  nlinarith [mul_pos (sub_pos.mpr hlt) hϑ, mul_nonneg hb (sub_pos.mpr hlt).le]

/-! ### The DIS in the welfare-relevant gap (7) -/

/-- Galí (2015), eq. (7), p. 132: the dynamic IS equation in a gap `x` with real rate `r`,
`x_t = E_t x_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − r_t)`. -/
def DIS (σ : ℝ) (x i infl r : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t = 𝔼.E t (x (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - r t)

/-- Galí (2015), p. 132: the real rate consistent with an output path `y^v` (natural or
efficient), `r_t = ζ_t + σ E_t{Δy^v_{t+1}}`, where `ζ_t = ρ + (1 − ρ_z) z_t` collects the
discount-rate and preference terms common to `r^n` and `r^e`. -/
def rateOf (σ : ℝ) (ζ yv : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => ζ t + σ • (𝔼.E t (yv (t + 1)) - yv t)

/-- Galí (2015), eq. (7), p. 132 (**exact**): for `σ ≠ 0`, the DIS in the natural-output gap
`y − y^n` with the natural rate `r^n` holds iff the DIS (7) in the welfare-relevant gap
`x = y − y^e` with the efficient rate `r^e` holds. -/
theorem dis_welfareGap_iff {σ : ℝ} (hσ : σ ≠ 0) {y yn ye i infl ζ : ℕ → Ω → ℝ} :
    DIS 𝔼 σ (fun t => y t - yn t) i infl (rateOf 𝔼 σ ζ yn) ↔
      DIS 𝔼 σ (fun t => y t - ye t) i infl (rateOf 𝔼 σ ζ ye) := by
  have hinv : σ⁻¹ * σ = 1 := inv_mul_cancel₀ hσ
  constructor
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    simp only [rateOf, map_sub, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at e ⊢
    linear_combination e - (𝔼.E t (ye (t + 1)) ω - ye t ω - 𝔼.E t (yn (t + 1)) ω + yn t ω) *
      hinv
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    simp only [rateOf, map_sub, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at e ⊢
    linear_combination e - (𝔼.E t (yn (t + 1)) ω - yn t ω - 𝔼.E t (ye (t + 1)) ω + ye t ω) *
      hinv

/-- Galí (2015), p. 132: with efficient output `y^e_t = ψ_ya a_t` (in deviations) and AR(1)
technology `a`, `σ E_t{Δy^e_{t+1}} = −σ(1 − ρ_a) ψ_ya a_t`, so
`r^e_t = ζ_t − σ(1 − ρ_a) ψ_ya a_t`. -/
theorem efficientRate_eq {σ ψ ρa : ℝ} {ζ a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) (t : ℕ) :
    rateOf 𝔼 σ ζ (fun s => ψ • a s) t = ζ t - (σ * (1 - ρa) * ψ) • a t := by
  unfold rateOf
  rw [map_smul, ha.2 t]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### The equilibrium interest rate (8) -/

/-- Galí (2015), eq. (8), p. 133: `Ψ_i = (ϑρ_u + σκ(1 − ρ_u))/(κ² + ϑ(1 − βρ_u))`. -/
noncomputable def psiI (β σ κ ϑ ρ : ℝ) : ℝ :=
  (ϑ * ρ + σ * κ * (1 - ρ)) / (κ ^ 2 + ϑ * (1 - β * ρ))

/-- Galí (2015), eq. (8), p. 133: `Ψ_i = ρ_u Ψ_π + σ(ρ_u − 1) Ψ_x`. -/
theorem psiI_eq (β σ κ ϑ ρ : ℝ) :
    psiI β σ κ ϑ ρ = psiPi β κ ϑ ρ * ρ + σ * psiX β κ ϑ ρ * (ρ - 1) := by
  unfold psiI psiPi psiX
  ring

/-- Galí (2015), eq. (8), p. 133 (**the interest-rate path under discretion, exact**): along
the discretionary equilibrium (5)–(6) with AR(1) `u`, the DIS (7) holds iff
`i_t = r^e_t + Ψ_i u_t`. -/
theorem interestRate_iff {β σ κ ϑ ρ : ℝ} (hσ : σ ≠ 0) {u i re : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρ u) :
    DIS 𝔼 σ (fun t => psiX β κ ϑ ρ • u t) i (fun t => psiPi β κ ϑ ρ • u t) re ↔
      ∀ t, i t = re t + psiI β σ κ ϑ ρ • u t := by
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  have hinv' : σ⁻¹ * σ = 1 := inv_mul_cancel₀ hσ
  constructor
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    simp only [map_smul, hu.2 t, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [psiI_eq]
    linear_combination σ * e - (i t ω - psiPi β κ ϑ ρ * (ρ * u t ω) - re t ω) * hinv
  · intro h t
    funext ω
    have hi := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
    rw [psiI_eq] at hi
    simp only [map_smul, hu.2 t, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination σ⁻¹ * hi - psiX β κ ϑ ρ * (1 - ρ) * u t ω * hinv'

/-- Galí (2015), eq. (8), p. 133: `Ψ_i > 0` for `σ, κ, ϑ > 0`, `0 ≤ β < 1`, `0 ≤ ρ_u < 1`. -/
theorem psiI_pos {β σ κ ϑ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) : 0 < psiI β σ κ ϑ ρ := by
  unfold psiI
  have hD := den_pos (κ := κ) hϑ hβ0 hβ1 hρ1
  have h1 : 0 < σ * κ * (1 - ρ) := mul_pos (mul_pos hσ hκ) (by linarith)
  have h2 : 0 ≤ ϑ * ρ := mul_nonneg hϑ.le hρ0
  exact div_pos (by linarith) hD

/-! ### The "rule" (8) and indeterminacy (9) -/

/-- Galí (2015), eq. (9), p. 133: the stacked vector `(x_t, π_t)` (restated from the
Chapter 4 project). -/
def stack (x infl : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![x t, infl t]

/-- Two bounded processes stack to a bounded vector process (restated from the Chapter 4
project; Galí 2015, p. 133). -/
theorem boundedVec_stack {a b : ℕ → Ω → ℝ} (ha : BoundedProc a) (hb : BoundedProc b) :
    BoundedVec (stack a b) := by
  obtain ⟨M₁, h₁⟩ := ha
  obtain ⟨M₂, h₂⟩ := hb
  refine ⟨max M₁ M₂, fun t j ω => ?_⟩
  fin_cases j
  · exact (h₁ t ω).trans (le_max_left _ _)
  · exact (h₂ t ω).trans (le_max_right _ _)

/-- Two adapted processes stack to an adapted vector process (restated from the Chapter 4
project; Galí 2015, p. 133). -/
theorem adaptedVec_stack {a b : ℕ → Ω → ℝ} (ha : 𝔼.Adapted a) (hb : 𝔼.Adapted b) :
    𝔼.AdaptedVec (stack a b) := by
  intro t j
  fin_cases j
  · exact ha t
  · exact hb t

/-- Galí (2015), eq. (9), p. 133: `A_O = [[1, σ⁻¹], [κ, β + κσ⁻¹]]`. -/
noncomputable def AO (β σ κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, σ⁻¹; κ, β + κ * σ⁻¹]

/-- Galí (2015), eq. (9), p. 133: the forcing `B_O u_t` for a rule `i_t = r^e_t + ψ u_t`,
`B_O = (−σ⁻¹ψ, 1 − κσ⁻¹ψ)`. -/
noncomputable def wO (σ κ ψ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun t => ![(-(ψ * σ⁻¹)) • u t, (1 - κ * ψ * σ⁻¹) • u t]

/-- Galí (2015), eq. (9), p. 133 (**exact**): under a rule `i_t = r^e_t + ψ u_t` (in
particular (8), `ψ = Ψ_i`), the NKPC (2) and the DIS (7) hold iff `(x, π)` solves
`(x_t, π_t) = A_O E_t (x_{t+1}, π_{t+1}) + B_O u_t`. -/
theorem rule8_iff_solves {β σ κ ψ : ℝ} {u x infl i re : ℕ → Ω → ℝ}
    (hrule : ∀ t, i t = re t + ψ • u t) :
    (NKPC 𝔼 β κ x u infl ∧ DIS 𝔼 σ x i infl re) ↔
      𝔼.Solves (AO β σ κ) (wO σ κ ψ u) (stack x infl) := by
  constructor
  · rintro ⟨hp, hd⟩ t j
    funext ω
    have e := congrFun (hd t) ω
    have p := congrFun (hp t) ω
    simp only [hrule t, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e p
    fin_cases j
    · simp [stack, AO, wO]
      linear_combination e
    · simp [stack, AO, wO]
      linear_combination p + κ * e
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have e0 := congrFun (h t 0) ω
      have e1 := congrFun (h t 1) ω
      simp [stack, AO, wO] at e0 e1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e1 - κ * e0
    · have e0 := congrFun (h t 0) ω
      simp [stack, AO, wO] at e0
      simp only [hrule t, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e0

/-- Galí (2015), eq. (9), p. 133: `tr A_O = 1 + β + κσ⁻¹`. -/
theorem tr2_AO (β σ κ : ℝ) : tr2 (AO β σ κ) = 1 + β + κ * σ⁻¹ := by
  simp only [tr2, AO, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- Galí (2015), eq. (9), p. 133: `det A_O = β`. -/
theorem det2_AO (β σ κ : ℝ) : det2 (AO β σ κ) = β := by
  simp only [det2, AO, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- Galí (2015), p. 133: for `σ, κ > 0` and `β ≥ 0`, `A_O` fails the Schur–Cohn condition. -/
theorem AO_not_schurStable {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    ¬ SchurStable (tr2 (AO β σ κ)) (det2 (AO β σ κ)) := by
  rw [tr2_AO, det2_AO]
  rintro ⟨-, h⟩
  have hk : 0 < κ * σ⁻¹ := mul_pos hκ (inv_pos.mpr hσ)
  have := le_abs_self (1 + β + κ * σ⁻¹)
  linarith

/-- Galí (2015), p. 133 (**"A_O has always one eigenvalue outside the unit circle"**): for
`σ, κ > 0` and `0 < β < 1`, the characteristic polynomial of `A_O` factors as
`(z − r₁)(z − r₂)` with real roots `0 < r₁ < 1 < r₂`: exactly one eigenvalue lies outside the
unit circle. -/
theorem AO_eigenvalues {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) :
    ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ < 1 ∧ 1 < r₂ ∧
      ∀ z, z ^ 2 - tr2 (AO β σ κ) * z + det2 (AO β σ κ) = (z - r₁) * (z - r₂) := by
  rw [tr2_AO, det2_AO]
  set T := 1 + β + κ * σ⁻¹ with hT
  have hk : 0 < κ * σ⁻¹ := mul_pos hκ (inv_pos.mpr hσ)
  have hT1 : 1 + β < T := by linarith
  have hsq : (1 + β) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (by linarith) hT1.le 2
  have hdisc : 0 ≤ T ^ 2 - 4 * β := by nlinarith [sq_nonneg (1 - β)]
  set s := Real.sqrt (T ^ 2 - 4 * β) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = T ^ 2 - 4 * β := Real.sq_sqrt hdisc
  refine ⟨(T - s) / 2, (T + s) / 2, ?_, ?_, ?_, fun z => ?_⟩
  · have : s < T := by nlinarith
    linarith
  · have : T - 2 < s := by
      by_contra hc
      push Not at hc
      nlinarith
    linarith
  · have : 2 - T < s := by
      by_contra hc
      push Not at hc
      nlinarith
    linarith
  · linear_combination (1 / 4 : ℝ) * hs2

/-- Galí (2015), eq. (9), p. 133 (**the "rule" (8) does not determine the equilibrium**): with
bounded AR(1) cost-push shocks, `σ, κ, ϑ > 0` and `0 < β < 1`, if the nominal rate follows
`i_t = r^e_t + Ψ_i u_t` there is a bounded adapted equilibrium of (2) and (7) other than the
discretionary one (5)–(6). -/
theorem rule8_indeterminate [Nonempty Ω] {β σ κ ϑ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ1 : ρ < 1) {u re : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u) :
    ∃ x infl : ℕ → Ω → ℝ, NKPC 𝔼 β κ x u infl ∧
      DIS 𝔼 σ x (fun t => re t + psiI β σ κ ϑ ρ • u t) infl re ∧
      𝔼.Adapted x ∧ 𝔼.Adapted infl ∧ BoundedProc x ∧ BoundedProc infl ∧
      (x ≠ (fun t => psiX β κ ϑ ρ • u t) ∨ infl ≠ (fun t => psiPi β κ ϑ ρ • u t)) := by
  obtain ⟨M, hM⟩ := hub
  have hbd : ∀ c : ℝ, BoundedProc (fun t => c • u t) := fun c => ⟨|c| * M, fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg c)⟩
  have had : ∀ c : ℝ, 𝔼.Adapted (fun t => c • u t) := fun c t => by rw [map_smul, hu.1 t]
  have hrule : ∀ t, (fun t => re t + psiI β σ κ ϑ ρ • u t) t =
      re t + psiI β σ κ ϑ ρ • u t := fun _ => rfl
  have hn := ((discretionEq_iff 𝔼 hϑ).mp (discretion_msv_isEq 𝔼 (κ := κ) hϑ hβ0 hβ1 hρ1 hu)).1
  have hd : DIS 𝔼 σ (fun t => psiX β κ ϑ ρ • u t) (fun t => re t + psiI β σ κ ϑ ρ • u t)
      (fun t => psiPi β κ ϑ ρ • u t) re := (interestRate_iff 𝔼 hσ.ne' hu).mpr hrule
  have hs := (rule8_iff_solves 𝔼 hrule).mp ⟨hn, hd⟩
  obtain ⟨y, hy, hay, ⟨B, hB⟩, hne⟩ := 𝔼.system_not_unique (AO_not_schurStable hσ hκ) hs
    (adaptedVec_stack 𝔼 (had _) (had _)) (boundedVec_stack (hbd _) (hbd _))
  have hst : stack (fun t => y t 0) (fun t => y t 1) = y := by
    funext t j
    fin_cases j <;> rfl
  obtain ⟨hn', hd'⟩ := (rule8_iff_solves 𝔼 (β := β) (x := fun t => y t 0)
    (infl := fun t => y t 1) hrule).mpr (hst ▸ hy)
  refine ⟨fun t => y t 0, fun t => y t 1, hn', hd', fun t => hay t 0, fun t => hay t 1,
    ⟨B, fun t ω => hB t 0 ω⟩, ⟨B, fun t ω => hB t 1 ω⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hst, hcon.1, hcon.2]

/-! ### An implementing rule (10) -/

/-- Galí (2015), eq. (10), p. 133: `Ψ'_i = (σκ(1 − ρ_u) − ϑ(φ_π − ρ_u))/(κ² + ϑ(1 − βρ_u))`. -/
noncomputable def psiIprime (β σ κ ϑ ρ φπ : ℝ) : ℝ :=
  (σ * κ * (1 - ρ) - ϑ * (φπ - ρ)) / (κ ^ 2 + ϑ * (1 - β * ρ))

/-- Galí (2015), eq. (10), p. 133 (the two forms of the rule agree, exact):
`r^e_t + Ψ_i u_t + φ_π(π_t − Ψ_π u_t) = r^e_t + Ψ'_i u_t + φ_π π_t`. -/
theorem rule10_eq (β σ κ ϑ ρ φπ : ℝ) (re u infl : ℕ → Ω → ℝ) (t : ℕ) :
    re t + psiI β σ κ ϑ ρ • u t + φπ • (infl t - psiPi β κ ϑ ρ • u t) =
      re t + psiIprime β σ κ ϑ ρ φπ • u t + φπ • infl t := by
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  unfold psiI psiIprime psiPi
  ring

/-- Galí (2015), p. 133 (the system under rule (10); ch. 4, eq. (13) with `φ_y = 0`):
`A_T = (σ + κφ_π)⁻¹ [[σ, 1 − βφ_π], [σκ, κ + βσ]]`. -/
noncomputable def AT (β σ κ φπ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![σ / (σ + κ * φπ), (1 - β * φπ) / (σ + κ * φπ);
    σ * κ / (σ + κ * φπ), (κ + β * σ) / (σ + κ * φπ)]

/-- Galí (2015), p. 133: the forcing of the system under a rule
`i_t = r^e_t + ψ u_t + φ_π π_t`: `(σ + κφ_π)⁻¹ (−(ψ + φ_π), σ − κψ) u_t`. -/
noncomputable def wT (σ κ φπ ψ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun t => ![(-(ψ + φπ) / (σ + κ * φπ)) • u t, ((σ - κ * ψ) / (σ + κ * φπ)) • u t]

/-- Galí (2015), p. 133 (**exact**): under a rule `i_t = r^e_t + ψ u_t + φ_π π_t` (in
particular (10), `ψ = Ψ'_i`), the NKPC (2) and the DIS (7) hold iff `(x, π)` solves
`(x_t, π_t) = A_T E_t (x_{t+1}, π_{t+1}) + w_t`. Adapted from the Chapter 4 project. -/
theorem rule10_iff_solves {β σ κ φπ ψ : ℝ} (hσ : σ ≠ 0) (hS : σ + κ * φπ ≠ 0)
    {u x infl i re : ℕ → Ω → ℝ} (hrule : ∀ t, i t = re t + ψ • u t + φπ • infl t) :
    (NKPC 𝔼 β κ x u infl ∧ DIS 𝔼 σ x i infl re) ↔
      𝔼.Solves (AT β σ κ φπ) (wT σ κ φπ ψ u) (stack x infl) := by
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  constructor
  · rintro ⟨hp, hd⟩ t j
    funext ω
    have e := congrFun (hd t) ω
    have p := congrFun (hp t) ω
    simp only [hrule t, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e p
    have s : σ * x t ω + φπ * infl t ω
        = σ * 𝔼.E t (x (t + 1)) ω + 𝔼.E t (infl (t + 1)) ω - ψ * u t ω := by
      linear_combination σ * e -
        (ψ * u t ω + φπ * infl t ω - 𝔼.E t (infl (t + 1)) ω) * hinv
    fin_cases j
    · simp [stack, AT, wT]
      field_simp
      linear_combination s - φπ * p
    · simp [stack, AT, wT]
      field_simp
      linear_combination κ * s + σ * p
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have e0 := congrFun (h t 0) ω
      have e1 := congrFun (h t 1) ω
      simp [stack, AT, wT] at e0 e1
      field_simp at e0 e1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      apply mul_left_cancel₀ hS
      linear_combination e1 - κ * e0
    · have e0 := congrFun (h t 0) ω
      have e1 := congrFun (h t 1) ω
      simp [stack, AT, wT] at e0 e1
      field_simp at e0 e1
      simp only [hrule t, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have s : σ * x t ω + φπ * infl t ω
          = σ * 𝔼.E t (x (t + 1)) ω + 𝔼.E t (infl (t + 1)) ω - ψ * u t ω := by
        apply mul_left_cancel₀ hS
        linear_combination σ * e0 + φπ * e1
      linear_combination σ⁻¹ * s - (x t ω - 𝔼.E t (x (t + 1)) ω) * hinv

/-- Galí (2015), p. 133: `tr A_T = (σ(1 + β) + κ)/(σ + κφ_π)`. -/
theorem tr2_AT {β σ κ φπ : ℝ} (hS : σ + κ * φπ ≠ 0) :
    tr2 (AT β σ κ φπ) = (σ * (1 + β) + κ) / (σ + κ * φπ) := by
  simp only [tr2, AT, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), p. 133: `det A_T = σβ/(σ + κφ_π)`. -/
theorem det2_AT {β σ κ φπ : ℝ} (hS : σ + κ * φπ ≠ 0) :
    det2 (AT β σ κ φπ) = σ * β / (σ + κ * φπ) := by
  simp only [det2, AT, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), p. 133 (**the Taylor principle for rule (10)**; ch. 4, eq. (14) with
`φ_y = 0`): for `σ, κ > 0`, `0 < β < 1`, `φ_π ≥ 0`, both eigenvalues of `A_T` lie inside the
unit circle iff `φ_π > 1`. -/
theorem AT_schurStable_iff {β σ κ φπ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) :
    SchurStable (tr2 (AT β σ κ φπ)) (det2 (AT β σ κ φπ)) ↔ 1 < φπ := by
  have hS : 0 < σ + κ * φπ := by positivity
  rw [tr2_AT hS.ne', det2_AT hS.ne']
  have hD0 : 0 < σ * β / (σ + κ * φπ) := by positivity
  have hD1 : σ * β / (σ + κ * φπ) < 1 := by
    rw [div_lt_one hS]; nlinarith
  have hT0 : 0 < (σ * (1 + β) + κ) / (σ + κ * φπ) := by positivity
  unfold SchurStable
  rw [abs_of_pos hD0, abs_of_pos hT0]
  have key : (σ * (1 + β) + κ) / (σ + κ * φπ) < 1 + σ * β / (σ + κ * φπ)
      ↔ σ * (1 + β) + κ < σ + κ * φπ + σ * β := by
    rw [one_add_div hS.ne', div_lt_div_iff_of_pos_right hS]
  rw [key]
  constructor
  · rintro ⟨-, h⟩
    nlinarith
  · intro h
    exact ⟨hD1, by nlinarith⟩

/-- Galí (2015), eq. (10), p. 133 (**rule (10) implements the discretionary equilibrium
uniquely**): for `σ, κ, ϑ > 0`, `0 < β < 1`, `ρ_u < 1`, bounded AR(1) `u` and any `φ_π > 1`,
bounded adapted `(x, π)` and a nominal rate `i` satisfy the NKPC (2), the DIS (7) and the rule
`i_t = r^e_t + Ψ'_i u_t + φ_π π_t` iff `(x, π)` is the discretionary equilibrium (5)–(6) and
`i_t = r^e_t + Ψ_i u_t` (8). -/
theorem rule10_implements {β σ κ ϑ ρ φπ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hρ1 : ρ < 1) (hφ : 1 < φπ) {u re x infl i : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u) (hxa : 𝔼.Adapted x) (hpa : 𝔼.Adapted infl)
    (hxb : BoundedProc x) (hpb : BoundedProc infl) :
    (NKPC 𝔼 β κ x u infl ∧ DIS 𝔼 σ x i infl re ∧
        ∀ t, i t = re t + psiIprime β σ κ ϑ ρ φπ • u t + φπ • infl t) ↔
      (x = (fun t => psiX β κ ϑ ρ • u t) ∧ infl = (fun t => psiPi β κ ϑ ρ • u t) ∧
        ∀ t, i t = re t + psiI β σ κ ϑ ρ • u t) := by
  have hS : σ + κ * φπ ≠ 0 := by positivity
  obtain ⟨M, hM⟩ := hub
  have hbd : ∀ c : ℝ, BoundedProc (fun t => c • u t) := fun c => ⟨|c| * M, fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg c)⟩
  have had : ∀ c : ℝ, 𝔼.Adapted (fun t => c • u t) := fun c t => by rw [map_smul, hu.1 t]
  -- the discretionary triple satisfies (2), (7) and (10)
  have hn := ((discretionEq_iff 𝔼 hϑ).mp
    (discretion_msv_isEq 𝔼 (κ := κ) hϑ hβ0.le hβ1 hρ1 hu)).1
  have hrule8 : ∀ t, (fun t => re t + psiI β σ κ ϑ ρ • u t) t =
      re t + psiI β σ κ ϑ ρ • u t := fun _ => rfl
  have hd := (interestRate_iff 𝔼 (β := β) (κ := κ) (ϑ := ϑ) hσ.ne' hu).mpr hrule8
  have hrule10 : ∀ t, (fun t => re t + psiI β σ κ ϑ ρ • u t) t =
      re t + psiIprime β σ κ ϑ ρ φπ • u t + φπ • (fun t => psiPi β κ ϑ ρ • u t) t := by
    intro t
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    unfold psiI psiIprime psiPi
    ring
  constructor
  · rintro ⟨hp, hdis, hr⟩
    have hs := (rule10_iff_solves 𝔼 hσ.ne' hS hr).mp ⟨hp, hdis⟩
    have hs' := (rule10_iff_solves 𝔼 hσ.ne' hS hrule10).mp ⟨hn, hd⟩
    have heq := 𝔼.system_unique ((AT_schurStable_iff hσ hκ hβ0 hβ1 (by linarith)).mpr hφ)
      hs hs' (adaptedVec_stack 𝔼 hxa hpa) (adaptedVec_stack 𝔼 (had _) (had _))
      (boundedVec_stack hxb hpb) (boundedVec_stack (hbd _) (hbd _))
    have h1 : x = fun t => psiX β κ ϑ ρ • u t := funext fun t => by
      simpa [stack] using congrFun (congrFun heq t) 0
    have h2 : infl = fun t => psiPi β κ ϑ ρ • u t := funext fun t => by
      simpa [stack] using congrFun (congrFun heq t) 1
    refine ⟨h1, h2, fun t => ?_⟩
    rw [hr t, h2]
    exact (hrule10 t).symm
  · rintro ⟨rfl, rfl, hi⟩
    have hieq : i = fun t => re t + psiI β σ κ ϑ ρ • u t := funext hi
    subst hieq
    exact ⟨hn, hd, hrule10⟩

/-- Galí (2015), p. 133 (**the Taylor principle is needed**): for `0 ≤ φ_π ≤ 1` the rule (10)
does not determine the equilibrium: there is a bounded adapted equilibrium of (2), (7) and (10)
other than the discretionary one. -/
theorem rule10_indeterminate [Nonempty Ω] {β σ κ ϑ ρ φπ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hϑ : 0 < ϑ) (hβ0 : 0 < β) (hβ1 : β < 1) (hρ1 : ρ < 1) (hφ0 : 0 ≤ φπ) (hφ1 : φπ ≤ 1)
    {u re : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u) :
    ∃ x infl : ℕ → Ω → ℝ, NKPC 𝔼 β κ x u infl ∧
      DIS 𝔼 σ x (fun t => re t + psiIprime β σ κ ϑ ρ φπ • u t + φπ • infl t) infl re ∧
      𝔼.Adapted x ∧ 𝔼.Adapted infl ∧ BoundedProc x ∧ BoundedProc infl ∧
      (x ≠ (fun t => psiX β κ ϑ ρ • u t) ∨ infl ≠ (fun t => psiPi β κ ϑ ρ • u t)) := by
  have hS : σ + κ * φπ ≠ 0 := by positivity
  obtain ⟨M, hM⟩ := hub
  have hbd : ∀ c : ℝ, BoundedProc (fun t => c • u t) := fun c => ⟨|c| * M, fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg c)⟩
  have had : ∀ c : ℝ, 𝔼.Adapted (fun t => c • u t) := fun c t => by rw [map_smul, hu.1 t]
  have hn := ((discretionEq_iff 𝔼 hϑ).mp
    (discretion_msv_isEq 𝔼 (κ := κ) hϑ hβ0.le hβ1 hρ1 hu)).1
  have hrule8 : ∀ t, (fun t => re t + psiI β σ κ ϑ ρ • u t) t =
      re t + psiI β σ κ ϑ ρ • u t := fun _ => rfl
  have hd := (interestRate_iff 𝔼 (β := β) (κ := κ) (ϑ := ϑ) hσ.ne' hu).mpr hrule8
  have hrule10 : ∀ t, (fun t => re t + psiI β σ κ ϑ ρ • u t) t =
      re t + psiIprime β σ κ ϑ ρ φπ • u t + φπ • (fun t => psiPi β κ ϑ ρ • u t) t := by
    intro t
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    unfold psiI psiIprime psiPi
    ring
  have hs := (rule10_iff_solves 𝔼 hσ.ne' hS hrule10).mp ⟨hn, hd⟩
  have hns : ¬ SchurStable (tr2 (AT β σ κ φπ)) (det2 (AT β σ κ φπ)) := by
    rw [AT_schurStable_iff hσ hκ hβ0 hβ1 hφ0]
    linarith
  obtain ⟨y, hy, hay, ⟨B, hB⟩, hne⟩ := 𝔼.system_not_unique hns hs
    (adaptedVec_stack 𝔼 (had _) (had _)) (boundedVec_stack (hbd _) (hbd _))
  have hst : stack (fun t => y t 0) (fun t => y t 1) = y := by
    funext t j
    fin_cases j <;> rfl
  have hr' : ∀ t, (fun t => re t + psiIprime β σ κ ϑ ρ φπ • u t + φπ • y t 1) t =
      re t + psiIprime β σ κ ϑ ρ φπ • u t + φπ • (fun t => y t 1) t := fun _ => rfl
  obtain ⟨hn', hd'⟩ := (rule10_iff_solves 𝔼 (β := β) (x := fun t => y t 0) hσ.ne' hS hr').mpr
    (hst ▸ hy)
  refine ⟨fun t => y t 0, fun t => y t 1, hn', hd', fun t => hay t 0, fun t => hay t 1,
    ⟨B, fun t ω => hB t 0 ω⟩, ⟨B, fun t ω => hB t 1 ω⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hst, hcon.1, hcon.2]

end Gali.DiscretionCommitment.Discretion
