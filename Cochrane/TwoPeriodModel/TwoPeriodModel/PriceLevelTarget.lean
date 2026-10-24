/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TwoPeriodModel.DebtSales

/-!
# Debt reactions and a price-level target; fiscal policy changes monetary policy

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 1, §§1.6–1.7, pp. 13–15.

The date-1 surplus follows the rule (1.13) `s₁ = B₀/P₁*`, where the price-level target `P₁* > 0`
is a date-1 random variable. Write `e = E₀(1/P₁*)`; we assume `e > 0` in every state.
An equilibrium under the rule is an `Equilibrium` of `TwoPeriod` with `s₁ = B₀/P₁*`.

## Main results

* (1.13), p. 13: `rule_price1_iff`, `rule_price1` (`P₁ = P₁*` uniquely).
* p. 14: `rule_valuation` (`B₋₁/P₀ = s₀ + βE₀(B₀/P₁*) = s₀ + βB₀E₀(1/P₁*)`),
  `rule_existsUnique`, `rule_price0`.
* p. 14, financing a deficit: `rule_borrow` (issue `ΔB₀ = −Δs₀/(βe)` more debt: `P₀`, `P₁`
  unchanged), `rule_inflate` (do not sell more debt: `P₀` rises), `rule_superinflate` (sell
  less debt: `s₁` falls and `P₀` rises even more).
* Box p. 14 / p. 15, §1.7: `rule_price0_strictAnti_B0` (more debt lowers `P₀`, `P₁ = P₁*`
  unchanged), `RuleTargetEquilibrium`, `rule_target_existsUnique` (under the rule and an
  interest-rate target, `P₀ = 1/((1 + i₀)βe)`), `rule_higher_rate_lowers_price0` ("higher
  interest rates lower inflation, immediately"), `rule_higher_rate_fiscal_tightening` (the
  accompanying expected future fiscal tightening: `B₀` and `s₁` rise, `s₀` unchanged).
* p. 15, demand curves: `rule_flat_demand` (`Q₀/P₀ = βe` for every `B₀`), `rule_revenue`
  (revenue `βB₀e` strictly increasing in `B₀`); with fixed surpluses
  `unit_elastic` (`Q₀B₀` the same for every `B₀`).
-/

namespace Cochrane.TwoPeriodModel.PriceLevelTarget

open Cochrane.TwoPeriodModel.TwoPeriod Cochrane.TwoPeriodModel.MonetaryFiscal
  Cochrane.TwoPeriodModel.DebtSales

variable {Ω : Type*}

/-- Cochrane (2023), eq. (1.13), p. 13: under the rule `s₁ = B₀/P₁*` (`B₀ > 0`, `P₁* > 0`), a
positive `P₁` satisfies `B₀/P₁ = s₁` iff `P₁ = P₁*`. -/
theorem rule_price1_iff {B0 Pstar P1 : Ω → ℝ} (hB0 : ∀ ω, 0 < B0 ω)
    (hPs : ∀ ω, 0 < Pstar ω) (hP1 : ∀ ω, 0 < P1 ω) :
    Valuation1 B0 P1 (B0 / Pstar) ↔ P1 = Pstar := by
  constructor
  · intro h
    rw [price1_eq (fun ω => (hP1 ω).ne') (fun ω => (div_pos (hB0 ω) (hPs ω)).ne') h]
    funext ω
    simp only [Pi.div_apply]
    have := (hB0 ω).ne'; have := (hPs ω).ne'
    field_simp
  · rintro rfl
    rfl

/-- Cochrane (2023), p. 13: "with this rule, equilibrium inflation is given uniquely from
`B₀/P₁ = s₁` by `P₁ = P₁*`": every equilibrium under the rule has `P₁ = P₁*`. -/
theorem rule_price1 (𝔼 : ExpectationSystem Ω) {β : ℝ} {Bm1 B0 s0 Pstar P0 P1 Q0 : Ω → ℝ}
    (hB0 : ∀ ω, 0 < B0 ω) (hPs : ∀ ω, 0 < Pstar ω)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 (B0 / Pstar) P0 P1 Q0) : P1 = Pstar :=
  (rule_price1_iff hB0 hPs he.2.1).mp he.2.2.2.2.2

/-- Cochrane (2023), p. 14: `E₀(B₀/P₁*) = B₀E₀(1/P₁*)` (`PullOut`, `B₀` known at 0), so the
present value under the rule is `s₀ + βB₀E₀(1/P₁*)`. -/
theorem rule_pv (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) (β : ℝ) {B0 s0 Pstar : Ω → ℝ}
    (hkB0 : Known 𝔼 0 B0) : pv 𝔼 β s0 (B0 / Pstar) = s0 + β • (B0 * 𝔼.E 0 (1 / Pstar)) := by
  have e : B0 / Pstar = B0 * (1 / Pstar) := by
    funext ω; simp only [Pi.div_apply, Pi.mul_apply, Pi.one_apply]; ring
  rw [pv, e, hP 0 B0 _ hkB0]

/-- Cochrane (2023), p. 14: in an equilibrium under the rule,
`B₋₁/P₀ = s₀ + βE₀(B₀/P₁*) = s₀ + βB₀E₀(1/P₁*)` (`PullOut`, `B₀` known at 0). -/
theorem rule_valuation (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 Pstar P0 P1 Q0 : Ω → ℝ} (hkB0 : Known 𝔼 0 B0)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 (B0 / Pstar) P0 P1 Q0) :
    Bm1 / P0 = s0 + β • 𝔼.E 0 (B0 / Pstar) ∧
      s0 + β • 𝔼.E 0 (B0 / Pstar) = s0 + β • (B0 * 𝔼.E 0 (1 / Pstar)) := by
  obtain ⟨hP0, -, hk, hflow, hQ, h1⟩ := he
  exact ⟨valuation0_of_flow 𝔼 hP hP0 hk hkB0 hflow hQ h1, rule_pv 𝔼 hP β hkB0⟩

/-- Cochrane (2023), pp. 13–14: under the rule there is exactly one equilibrium (`PullOut`;
`B₋₁, B₀ > 0`, `B₋₁, B₀, s₀` known at 0; `P₁* > 0`; positive present value
`s₀ + βB₀E₀(1/P₁*)`). -/
theorem rule_existsUnique (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 Pstar : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω) (hkBm1 : Known 𝔼 0 Bm1)
    (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0) (hks0 : Known 𝔼 0 s0)
    (hPs : ∀ ω, 0 < Pstar ω) (hpv : ∀ ω, 0 < s0 ω + β * (B0 ω * 𝔼.E 0 (1 / Pstar) ω)) :
    ∃! p : (Ω → ℝ) × (Ω → ℝ) × (Ω → ℝ),
      Equilibrium 𝔼 β Bm1 B0 s0 (B0 / Pstar) p.1 p.2.1 p.2.2 := by
  refine equilibrium_existsUnique 𝔼 hP hBm1 hkBm1 hB0 hkB0 hks0
    (fun ω => div_pos (hB0 ω) (hPs ω)) (fun ω => ?_)
  rw [rule_pv 𝔼 hP β hkB0]
  exact hpv ω

/-- Cochrane (2023), p. 14: the equilibrium price level under the rule,
`P₀ = B₋₁/(s₀ + βB₀E₀(1/P₁*))`. -/
theorem rule_price0 (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 Pstar P0 P1 Q0 : Ω → ℝ} (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0)
    (hPs : ∀ ω, 0 < Pstar ω) (hpv : ∀ ω, 0 < s0 ω + β * (B0 ω * 𝔼.E 0 (1 / Pstar) ω))
    (he : Equilibrium 𝔼 β Bm1 B0 s0 (B0 / Pstar) P0 P1 Q0) (ω : Ω) :
    P0 ω = Bm1 ω / (s0 ω + β * (B0 ω * 𝔼.E 0 (1 / Pstar) ω)) := by
  have hpv' : ∀ ω, 0 < pv 𝔼 β s0 (B0 / Pstar) ω := fun ω => by
    rw [rule_pv 𝔼 hP β hkB0]; exact hpv ω
  rw [price0_formula 𝔼 hP (s1 := B0 / Pstar) hB0 hkB0 (fun ω => div_pos (hB0 ω) (hPs ω)) hpv'
    he ω]
  have := congrFun (rule_pv 𝔼 hP β (s0 := s0) (Pstar := Pstar) hkB0) ω
  simp only [pv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply] at this
  rw [this]

/-! ### Financing a deficit under the rule (p. 14) -/

/-- Cochrane (2023), p. 14: "to finance a deficit `s₀` by borrowing, without affecting the price
level at either date, the government issues more nominal debt `B₀`, without changing the
price-level target": lowering `s₀` by `Δ` and raising `B₀` by `ΔB₀` with `βΔB₀E₀(1/P₁*) = −Δ`
leaves `P₀` unchanged, and `P₁ = P₁*` in both equilibria. -/
theorem rule_borrow (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β Δ : ℝ}
    {Bm1 B0 ΔB s0 Pstar P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hB0 : ∀ ω, 0 < B0 ω)
    (hkB0 : Known 𝔼 0 B0) (hB0' : ∀ ω, 0 < (B0 + ΔB) ω) (hkΔB : Known 𝔼 0 ΔB)
    (hPs : ∀ ω, 0 < Pstar ω) (hpv : ∀ ω, 0 < s0 ω + β * (B0 ω * 𝔼.E 0 (1 / Pstar) ω))
    (hΔB : ∀ ω, β * ΔB ω * 𝔼.E 0 (1 / Pstar) ω = -Δ)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 (B0 / Pstar) P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 (B0 + ΔB) (s0 + fun _ => Δ) ((B0 + ΔB) / Pstar) P0' P1' Q0') :
    P0' = P0 ∧ P1' = Pstar ∧ P1 = Pstar := by
  have hkB0' := known_add 𝔼 hkB0 hkΔB
  have hsame : ∀ ω, s0 ω + Δ + β * ((B0 + ΔB) ω * 𝔼.E 0 (1 / Pstar) ω) =
      s0 ω + β * (B0 ω * 𝔼.E 0 (1 / Pstar) ω) := fun ω => by
    simp only [Pi.add_apply]
    linear_combination hΔB ω
  have hpv' : ∀ ω, 0 < s0 ω + Δ + β * ((B0 + ΔB) ω * 𝔼.E 0 (1 / Pstar) ω) :=
    fun ω => by rw [hsame]; exact hpv ω
  refine ⟨funext fun ω => ?_, rule_price1 𝔼 hB0' hPs he', rule_price1 𝔼 hB0 hPs he⟩
  rw [rule_price0 𝔼 hP hB0' hkB0' hPs hpv' he' ω, rule_price0 𝔼 hP hB0 hkB0 hPs hpv he ω,
    hsame]

/-- Cochrane (2023), p. 14: "to finance the deficit by inflating away outstanding debt, the
government simply does not sell more debt `B₀`": with `B₀` unchanged and `s₀` lower by `Δ < 0`,
`P₀` rises in every state (`B₋₁ > 0`) while `P₁ = P₁*`. -/
theorem rule_inflate (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β Δ : ℝ} (hΔ : Δ < 0)
    {Bm1 B0 s0 Pstar P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω)
    (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0) (hPs : ∀ ω, 0 < Pstar ω)
    (hpv : ∀ ω, 0 < s0 ω + β * (B0 ω * 𝔼.E 0 (1 / Pstar) ω))
    (hpv' : ∀ ω, 0 < s0 ω + Δ + β * (B0 ω * 𝔼.E 0 (1 / Pstar) ω))
    (he : Equilibrium 𝔼 β Bm1 B0 s0 (B0 / Pstar) P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 B0 (s0 + fun _ => Δ) (B0 / Pstar) P0' P1' Q0') :
    (∀ ω, P0 ω < P0' ω) ∧ P1' = Pstar := by
  refine ⟨fun ω => ?_, rule_price1 𝔼 hB0 hPs he'⟩
  rw [rule_price0 𝔼 hP hB0 hkB0 hPs hpv he ω, rule_price0 𝔼 hP hB0 hkB0 hPs hpv' he' ω]
  have h' := hpv' ω
  exact div_lt_div_of_pos_left (hBm1 ω) h' (by linarith)

/-- Cochrane (2023), p. 14: "to super-inflate … the government sells even less debt `B₀`, which
lowers surpluses `s₁`": with `B₀' < B₀`, `s₀` lower by `Δ < 0`, `β > 0`, `E₀(1/P₁*) > 0`, the
date-1 surplus falls in every state and `P₀` rises above its "inflate" level. -/
theorem rule_superinflate (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β Δ : ℝ} (hβ : 0 < β)
    {Bm1 B0 B0' s0 Pstar Pi0 Pi1 Qi Ps0 Ps1 Qs : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω)
    (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0) (hB0' : ∀ ω, 0 < B0' ω)
    (hkB0' : Known 𝔼 0 B0') (hless : ∀ ω, B0' ω < B0 ω) (hPs : ∀ ω, 0 < Pstar ω)
    (he : ∀ ω, 0 < 𝔼.E 0 (1 / Pstar) ω)
    (hpvs : ∀ ω, 0 < s0 ω + Δ + β * (B0' ω * 𝔼.E 0 (1 / Pstar) ω))
    (hei : Equilibrium 𝔼 β Bm1 B0 (s0 + fun _ => Δ) (B0 / Pstar) Pi0 Pi1 Qi)
    (hes : Equilibrium 𝔼 β Bm1 B0' (s0 + fun _ => Δ) (B0' / Pstar) Ps0 Ps1 Qs) (ω : Ω) :
    (B0' / Pstar) ω < (B0 / Pstar) ω ∧ Pi0 ω < Ps0 ω := by
  have hlt : ∀ ω, β * (B0' ω * 𝔼.E 0 (1 / Pstar) ω) < β * (B0 ω * 𝔼.E 0 (1 / Pstar) ω) :=
    fun ω => mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right (hless ω) (he ω)) hβ
  have hpvi : ∀ ω, 0 < s0 ω + Δ + β * (B0 ω * 𝔼.E 0 (1 / Pstar) ω) :=
    fun ω => by linarith [hpvs ω, hlt ω]
  refine ⟨div_lt_div_of_pos_right (hless ω) (hPs ω), ?_⟩
  rw [rule_price0 𝔼 hP hB0 hkB0 hPs hpvi hei ω, rule_price0 𝔼 hP hB0' hkB0' hPs hpvs hes ω]
  exact div_lt_div_of_pos_left (hBm1 ω) (hpvs ω) (by linarith [hlt ω])

/-! ### §1.7: fiscal policy changes monetary policy -/

/-- Cochrane (2023), box p. 14 and p. 15: "larger debt `B₀` has no effect on `P₁ = P₁*`, and it
lowers the price level `P₀` immediately": with `B₀ < B₀'`, `s₀` unchanged, `β > 0`,
`E₀(1/P₁*) > 0`, `B₋₁ > 0`, `P₀' < P₀` in every state and `P₁ = P₁' = P₁*`. -/
theorem rule_price0_strictAnti_B0 (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    (hβ : 0 < β) {Bm1 B0 B0' s0 Pstar P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω)
    (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0) (hB0' : ∀ ω, 0 < B0' ω)
    (hkB0' : Known 𝔼 0 B0') (hmore : ∀ ω, B0 ω < B0' ω) (hPs : ∀ ω, 0 < Pstar ω)
    (he : ∀ ω, 0 < 𝔼.E 0 (1 / Pstar) ω)
    (hpv : ∀ ω, 0 < s0 ω + β * (B0 ω * 𝔼.E 0 (1 / Pstar) ω))
    (heq : Equilibrium 𝔼 β Bm1 B0 s0 (B0 / Pstar) P0 P1 Q0)
    (heq' : Equilibrium 𝔼 β Bm1 B0' s0 (B0' / Pstar) P0' P1' Q0') :
    (∀ ω, P0' ω < P0 ω) ∧ P1 = Pstar ∧ P1' = Pstar := by
  have hlt : ∀ ω, β * (B0 ω * 𝔼.E 0 (1 / Pstar) ω) < β * (B0' ω * 𝔼.E 0 (1 / Pstar) ω) :=
    fun ω => mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right (hmore ω) (he ω)) hβ
  have hpv' : ∀ ω, 0 < s0 ω + β * (B0' ω * 𝔼.E 0 (1 / Pstar) ω) :=
    fun ω => by linarith [hpv ω, hlt ω]
  refine ⟨fun ω => ?_, rule_price1 𝔼 hB0 hPs heq, rule_price1 𝔼 hB0' hPs heq'⟩
  rw [rule_price0 𝔼 hP hB0 hkB0 hPs hpv heq ω, rule_price0 𝔼 hP hB0' hkB0' hPs hpv' heq' ω]
  exact div_lt_div_of_pos_left (hBm1 ω) (hpv ω) (by linarith [hlt ω])

/-- Cochrane (2023), §1.7, p. 15: an equilibrium under the rule `s₁ = B₀/P₁*` and the
interest-rate target `i₀`: `B₀` endogenous, known at 0 and positive, and `Q₀ = 1/(1 + i₀)`. -/
def RuleTargetEquilibrium (𝔼 : ExpectationSystem Ω) (β i0 : ℝ) (Bm1 s0 Pstar P0 B0 P1 : Ω → ℝ) :
    Prop :=
  Known 𝔼 0 B0 ∧ (∀ ω, 0 < B0 ω) ∧
    Equilibrium 𝔼 β Bm1 B0 s0 (B0 / Pstar) P0 P1 (fun _ => 1 / (1 + i0))

/-- Cochrane (2023), p. 15: under the rule, the bond price is `Q₀ = βE₀(P₀/P₁*) = βP₀E₀(1/P₁*)`,
so with the target `Q₀ = 1/(1 + i₀)` the price level is `P₀ = 1/((1 + i₀)βE₀(1/P₁*))`
(`PullOut`, `B₀ > 0`, `P₁* > 0`, `i₀ ≠ −1`, `β ≠ 0`). -/
theorem rule_target_price0 (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β i0 : ℝ}
    (hβ : β ≠ 0) (hi : 1 + i0 ≠ 0) {Bm1 s0 Pstar P0 B0 P1 : Ω → ℝ} (hPs : ∀ ω, 0 < Pstar ω)
    (he : RuleTargetEquilibrium 𝔼 β i0 Bm1 s0 Pstar P0 B0 P1) (ω : Ω) :
    P0 ω = 1 / ((1 + i0) * β * 𝔼.E 0 (1 / Pstar) ω) := by
  obtain ⟨-, hB0, hq⟩ := he
  have hP1 := rule_price1 𝔼 hB0 hPs hq
  have hinv := E0_invP1 𝔼 hP hβ hi hq ω
  rw [hP1] at hinv
  have hP0 := (hq.1 ω).ne'
  rw [hinv]
  field_simp

/-- Cochrane (2023), §1.7, p. 15: **under the rule and an interest-rate target the equilibrium is
unique**: for `i₀ > −1`, `β > 0`, `e = E₀(1/P₁*) > 0`, with `B₋₁ > 0` and `s₀` known at 0 and
`s₀ < B₋₁(1 + i₀)βe` (so that a positive debt is sold), there is exactly one `(P₀, B₀, P₁)`:
`P₀ = 1/((1 + i₀)βe)`, `B₀ = (B₋₁/P₀ − s₀)/(βe)`, `P₁ = P₁*`. -/
theorem rule_target_existsUnique (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β i0 : ℝ}
    (hβ : 0 < β) (hi : -1 < i0) {Bm1 s0 Pstar : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω)
    (hkBm1 : Known 𝔼 0 Bm1) (hks0 : Known 𝔼 0 s0) (hPs : ∀ ω, 0 < Pstar ω)
    (he : ∀ ω, 0 < 𝔼.E 0 (1 / Pstar) ω)
    (hs0 : ∀ ω, s0 ω < Bm1 ω * ((1 + i0) * β * 𝔼.E 0 (1 / Pstar) ω)) :
    ∃! p : (Ω → ℝ) × (Ω → ℝ) × (Ω → ℝ),
      RuleTargetEquilibrium 𝔼 β i0 Bm1 s0 Pstar p.1 p.2.1 p.2.2 := by
  have hi' : 0 < 1 + i0 := by linarith
  set e := 𝔼.E 0 (1 / Pstar) with he_def
  have hke : Known 𝔼 0 e := known_E 𝔼 0 _
  set P0 : Ω → ℝ := fun ω => 1 / ((1 + i0) * β * e ω) with hP0def
  have hP0 : ∀ ω, 0 < P0 ω := fun ω => by
    have := he ω; simp only [hP0def]; positivity
  have hkP0 : Known 𝔼 0 P0 := by
    have : P0 = (fun _ => (1 : ℝ)) / ((1 + i0) * β) • e := by
      funext ω; simp [hP0def, mul_assoc]
    rw [this]
    exact known_div 𝔼 hP (known_const 𝔼 0 1) (known_smul 𝔼 _ hke) (fun ω => by
      simp only [Pi.smul_apply, smul_eq_mul]; have := he ω; positivity)
  set B0 : Ω → ℝ := (Bm1 / P0 - s0) / (β • e) with hB0def
  have hB0 : ∀ ω, 0 < B0 ω := fun ω => by
    simp only [hB0def, Pi.div_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hP0def]
    have := he ω; have := hs0 ω
    refine div_pos ?_ (by positivity)
    rw [div_div_eq_mul_div, div_one]
    linarith
  have hkB0 : Known 𝔼 0 B0 :=
    known_div 𝔼 hP (known_sub 𝔼 (known_div 𝔼 hP hkBm1 hkP0 (fun ω => (hP0 ω).ne')) hks0)
      (known_smul 𝔼 β hke) (fun ω => by
        simp only [Pi.smul_apply, smul_eq_mul]; have := he ω; positivity)
  have hpvB : ∀ ω, s0 ω + β * (B0 ω * e ω) = Bm1 ω / P0 ω := fun ω => by
    simp only [hB0def, Pi.div_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have := (he ω).ne'; have := hβ.ne'
    field_simp
    ring
  have hpv : ∀ ω, 0 < pv 𝔼 β s0 (B0 / Pstar) ω := fun ω => by
    rw [rule_pv 𝔼 hP β hkB0]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
    rw [hpvB]
    exact div_pos (hBm1 ω) (hP0 ω)
  have hs1 : ∀ ω, 0 < (B0 / Pstar) ω := fun ω => div_pos (hB0 ω) (hPs ω)
  refine ⟨(P0, B0, Pstar), ⟨hkB0, hB0, ?_⟩, ?_⟩
  · refine (equilibrium_iff 𝔼 hP hB0 hkB0 hs1 hpv).mpr ⟨hP0, hkP0, ?_, ?_, ?_⟩
    · funext ω
      simp only [Pi.div_apply]
      have := (hB0 ω).ne'; have := (hPs ω).ne'
      field_simp
    · funext ω
      rw [rule_pv 𝔼 hP β hkB0]
      simp only [Pi.div_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
      rw [hpvB]
      have := (hBm1 ω).ne'; have := (hP0 ω).ne'
      field_simp
    · unfold BondPrice0
      have e1 : P0 / Pstar = P0 * (1 / Pstar) := by
        funext ω; simp only [Pi.div_apply, Pi.mul_apply, Pi.one_apply]; ring
      rw [e1, hP 0 P0 _ hkP0]
      funext ω
      simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, hP0def]
      rw [← he_def]
      have := (he ω).ne'; have := hβ.ne'; have := hi'.ne'
      field_simp
  · rintro ⟨P0', B0', P1'⟩ hrt
    have h0 := rule_target_price0 𝔼 hP hβ.ne' hi'.ne' hPs hrt
    obtain ⟨hkB0', hB0', hq⟩ := hrt
    simp only at hkB0' hB0' hq h0
    have hP0eq : P0' = P0 := funext fun ω => by rw [h0 ω]
    have hP1 := rule_price1 𝔼 hB0' hPs hq
    have hv := (rule_valuation 𝔼 hP hkB0' hq)
    have hB : B0' = B0 := by
      funext ω
      have e1 := congrFun hv.1 ω
      have e2 := congrFun hv.2 ω
      simp only [Pi.div_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
        at e1 e2
      rw [e2, hP0eq] at e1
      have h3 := hpvB ω
      have : β * e ω ≠ 0 := (mul_pos hβ (he ω)).ne'
      have h4 : β * e ω * B0' ω = β * e ω * B0 ω := by
        rw [he_def] at h3 ⊢
        linarith
      exact mul_left_cancel₀ this h4
    rw [hP0eq, hB, hP1]

/-- Cochrane (2023), box p. 14 and p. 15: "higher interest rates lower inflation, immediately":
under the rule, `i₀ < i₀'` gives `P₀' < P₀` in every state (lower current inflation
`P₀/P₋₁`), with `P₁ = P₁' = P₁*` unchanged (`PullOut`, `β > 0`, `i₀ > −1`, `E₀(1/P₁*) > 0`). -/
theorem rule_higher_rate_lowers_price0 (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut)
    {β i0 i0' : ℝ} (hβ : 0 < β) (hi : -1 < i0) (hii' : i0 < i0')
    {Bm1 s0 Pstar P0 B0 P1 P0' B0' P1' : Ω → ℝ} (hPs : ∀ ω, 0 < Pstar ω)
    (he : ∀ ω, 0 < 𝔼.E 0 (1 / Pstar) ω)
    (heq : RuleTargetEquilibrium 𝔼 β i0 Bm1 s0 Pstar P0 B0 P1)
    (heq' : RuleTargetEquilibrium 𝔼 β i0' Bm1 s0 Pstar P0' B0' P1') :
    (∀ ω, P0' ω < P0 ω) ∧ P1 = Pstar ∧ P1' = Pstar := by
  refine ⟨fun ω => ?_, rule_price1 𝔼 heq.2.1 hPs heq.2.2, rule_price1 𝔼 heq'.2.1 hPs heq'.2.2⟩
  rw [rule_target_price0 𝔼 hP hβ.ne' (by linarith) hPs heq ω,
    rule_target_price0 𝔼 hP hβ.ne' (by linarith) hPs heq' ω]
  have := he ω
  have h1 : 0 < (1 + i0) * β * 𝔼.E 0 (1 / Pstar) ω := by
    have : 0 < 1 + i0 := by linarith
    positivity
  refine one_div_lt_one_div_of_lt h1 ?_
  have : 0 < β * 𝔼.E 0 (1 / Pstar) ω := by positivity
  nlinarith

/-- Cochrane (2023), p. 15: "we see a simultaneous fiscal tightening along with the
interest-rate rise … only an expected future fiscal tightening": under the rule, a higher
target `i₀ < i₀'` with unchanged `s₀` raises the debt sold and the date-1 surplus
`s₁ = B₀/P₁*` in every state. -/
theorem rule_higher_rate_fiscal_tightening (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut)
    {β i0 i0' : ℝ} (hβ : 0 < β) (hi : -1 < i0) (hii' : i0 < i0')
    {Bm1 s0 Pstar P0 B0 P1 P0' B0' P1' : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω)
    (hPs : ∀ ω, 0 < Pstar ω) (he : ∀ ω, 0 < 𝔼.E 0 (1 / Pstar) ω)
    (heq : RuleTargetEquilibrium 𝔼 β i0 Bm1 s0 Pstar P0 B0 P1)
    (heq' : RuleTargetEquilibrium 𝔼 β i0' Bm1 s0 Pstar P0' B0' P1') (ω : Ω) :
    B0 ω < B0' ω ∧ (B0 / Pstar) ω < (B0' / Pstar) ω := by
  have hlow := (rule_higher_rate_lowers_price0 𝔼 hP hβ hi hii' hPs he heq heq').1 ω
  have hv := congrFun (rule_valuation 𝔼 hP heq.1 heq.2.2).1 ω
  have hv2 := congrFun (rule_valuation 𝔼 hP heq.1 heq.2.2).2 ω
  have hv' := congrFun (rule_valuation 𝔼 hP heq'.1 heq'.2.2).1 ω
  have hv2' := congrFun (rule_valuation 𝔼 hP heq'.1 heq'.2.2).2 ω
  simp only [Pi.div_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
    at hv hv2 hv' hv2'
  rw [hv2] at hv
  rw [hv2'] at hv'
  have hP0 := heq.2.2.1 ω
  have hP0' := heq'.2.2.1 ω
  have hdiv : Bm1 ω / P0 ω < Bm1 ω / P0' ω := div_lt_div_of_pos_left (hBm1 ω) hP0' hlow
  have hlt : β * (B0 ω * 𝔼.E 0 (1 / Pstar) ω) < β * (B0' ω * 𝔼.E 0 (1 / Pstar) ω) := by
    linarith
  have hB : B0 ω < B0' ω :=
    lt_of_mul_lt_mul_right (lt_of_mul_lt_mul_left hlt hβ.le) (he ω).le
  exact ⟨hB, div_lt_div_of_pos_right hB (hPs ω)⟩

/-! ### Demand curves for debt (p. 15) -/

/-- Cochrane (2023), p. 15: "now, the debt demand curve is flat, giving the same real price
`Q₀/P₀` for any amount sold `B₀`": under the rule, `Q₀/P₀ = βE₀(1/P₁*)` in every equilibrium
(`PullOut`, `B₀ > 0`, `P₁* > 0`). -/
theorem rule_flat_demand (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 Pstar P0 P1 Q0 : Ω → ℝ} (hB0 : ∀ ω, 0 < B0 ω) (hPs : ∀ ω, 0 < Pstar ω)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 (B0 / Pstar) P0 P1 Q0) :
    Q0 / P0 = β • 𝔼.E 0 (1 / Pstar) := by
  have hP1 := rule_price1 𝔼 hB0 hPs he
  obtain ⟨hP0, -, hk, -, hQ, -⟩ := he
  rw [hQ, hP1]
  have e1 : P0 / Pstar = P0 * (1 / Pstar) := by
    funext ω; simp only [Pi.div_apply, Pi.mul_apply, Pi.one_apply]; ring
  rw [e1, hP 0 P0 _ hk]
  funext ω
  simp only [Pi.div_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  have := (hP0 ω).ne'
  field_simp

/-- Cochrane (2023), p. 15: "the more bonds `B₀` sold, then, the more total real revenue such
sales produce": under the rule, revenue `Q₀B₀/P₀ = βB₀E₀(1/P₁*)`, strictly increasing in `B₀`
when `β > 0` and `E₀(1/P₁*) > 0`. -/
theorem rule_revenue (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ} (hβ : 0 < β)
    {Bm1 B0 B0' s0 s0' Pstar P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hB0 : ∀ ω, 0 < B0 ω)
    (hB0' : ∀ ω, 0 < B0' ω) (hmore : ∀ ω, B0 ω < B0' ω) (hPs : ∀ ω, 0 < Pstar ω)
    (he : ∀ ω, 0 < 𝔼.E 0 (1 / Pstar) ω)
    (heq : Equilibrium 𝔼 β Bm1 B0 s0 (B0 / Pstar) P0 P1 Q0)
    (heq' : Equilibrium 𝔼 β Bm1 B0' s0' (B0' / Pstar) P0' P1' Q0') (ω : Ω) :
    (Q0 * B0 / P0) ω = β * 𝔼.E 0 (1 / Pstar) ω * B0 ω ∧
      (Q0 * B0 / P0) ω < (Q0' * B0' / P0') ω := by
  have h := congrFun (rule_flat_demand 𝔼 hP hB0 hPs heq) ω
  have h' := congrFun (rule_flat_demand 𝔼 hP hB0' hPs heq') ω
  simp only [Pi.div_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply] at h h' ⊢
  have e1 : Q0 ω * B0 ω / P0 ω = Q0 ω / P0 ω * B0 ω := by ring
  have e2 : Q0' ω * B0' ω / P0' ω = Q0' ω / P0' ω * B0' ω := by ring
  rw [e1, e2, h, h']
  exact ⟨rfl, mul_lt_mul_of_pos_left (hmore ω) (mul_pos hβ (he ω))⟩

/-- Cochrane (2023), p. 15: "fixing surpluses `{s₀, s₁}`, the demand curve for nominal debt was
unit-elastic, giving the same total real revenue `βE₀(s₁)` for any amount of bonds `B₀`": two
equilibria with the same surpluses and debt `B₀`, `B₀'` have the same `P₀` and the same nominal
revenue `Q₀B₀ = Q₀'B₀'` (so `Q₀' = Q₀B₀/B₀'`). -/
theorem unit_elastic (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 B0' s0 s1 P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hB0 : ∀ ω, 0 < B0 ω)
    (hkB0 : Known 𝔼 0 B0) (hB0' : ∀ ω, 0 < B0' ω) (hkB0' : Known 𝔼 0 B0')
    (hs1 : ∀ ω, 0 < s1 ω) (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 B0' s0 s1 P0' P1' Q0') :
    P0' = P0 ∧ Q0' * B0' = Q0 * B0 := by
  have hP0 : P0' = P0 := funext fun ω => by
    rw [price0_formula 𝔼 hP hB0' hkB0' hs1 hpv he' ω, price0_formula 𝔼 hP hB0 hkB0 hs1 hpv he ω]
  refine ⟨hP0, ?_⟩
  obtain ⟨-, -, hk, -, hQ, h1⟩ := he
  obtain ⟨-, -, hk', -, hQ', h1'⟩ := he'
  rw [revenue_eq 𝔼 hP hk' hkB0' hQ' h1', revenue_eq 𝔼 hP hk hkB0 hQ h1, hP0]

end Cochrane.TwoPeriodModel.PriceLevelTarget
