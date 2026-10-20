/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TwoPeriodModel.TwoPeriod

/-!
# Monetary policy, fiscal policy and inflation

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 1, §1.4, pp. 9–10.

The two-period model of `TwoPeriod` (equilibrium `Equilibrium`, valuation equations (1.6)–(1.7)
= (1.1) and (1.5)). Everything holds for an arbitrary `ExpectationSystem` with `PullOut`.

## Main results

* (1.8), p. 9: `eq_1_8` (the chain `B₋₁/P₀ = s₀ + Q₀B₀/P₀ = s₀ + βE₀(P₀/P₁)B₀/P₀ = s₀ + βE₀s₁`);
  `revenue_invariant` ("bond sales raise no extra revenue").
* p. 9, share split: `shareSplit_equilibrium`, `shareSplit_unique` (selling `κB₀` with unchanged
  surpluses leaves `P₀`, multiplies `P₁` by `κ`, divides `Q₀` by `κ`), `doubling` (`κ = 2`),
  `rate_strictAnti` and `shareSplit_rate_rises` (the nominal rate rises).
* p. 10, interest-rate target: `TargetEquilibrium`, `target_existsUnique` (for every `i₀ > −1`
  exactly one `(P₀, B₀, P₁)`; this is also `determinate_under_peg`), `target_bond_demand`
  (the flat supply curve: `B₀ = (1 + i₀)P₀βE₀s₁`).
* (1.9), p. 10: `expected_inflation`, `E0_invP1`.
* p. 10, "Fisherian": `fisherian_two_period` (a higher `i₀` leaves `P₀` and raises `P₁` in
  every state and lowers `E₀(1/P₁)`).
* (1.10), p. 10: `innov`, `unexpected_inflation`; "(1.9)–(1.10) completely determine expected
  and unexpected inflation": `inflation_decomposition`, `no_fiscal_news`.
-/

namespace Cochrane.TwoPeriodModel.MonetaryFiscal

open Cochrane.TwoPeriodModel.TwoPeriod

variable {Ω : Type*}

/-! ### (1.8): bond sales raise no extra revenue -/

/-- Cochrane (2023), eq. (1.8), p. 9: in an equilibrium (with `PullOut`, `B₀` known at 0),
`B₋₁/P₀ = s₀ + (1/(1 + i₀))B₀/P₀`, `(1/(1 + i₀))B₀/P₀ = βE₀(P₀/P₁)B₀/P₀`, and
`βE₀(P₀/P₁)B₀/P₀ = βE₀s₁`. -/
theorem eq_1_8 (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ} (hkB0 : Known 𝔼 0 B0)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0) :
    Bm1 / P0 = s0 + (fun ω => 1 / (1 + rate Q0 ω)) * B0 / P0 ∧
      (fun ω => 1 / (1 + rate Q0 ω)) * B0 / P0 = β • 𝔼.E 0 (P0 / P1) * B0 / P0 ∧
      β • 𝔼.E 0 (P0 / P1) * B0 / P0 = β • 𝔼.E 0 s1 := by
  obtain ⟨hP0, -, hk, hflow, hQ, h1⟩ := he
  have hr := revenue_eq 𝔼 hP hk hkB0 hQ h1
  have hQ' : (fun ω => 1 / (1 + rate Q0 ω)) = Q0 := by
    funext ω; exact (bondPrice_eq_inv_one_add_rate Q0 ω).symm
  rw [hQ']
  refine ⟨?_, by rw [hQ], ?_⟩
  · funext ω
    have e := congrFun hflow ω
    simp only [Pi.add_apply, Pi.mul_apply, Pi.div_apply] at e ⊢
    have := (hP0 ω).ne'
    rw [e]
    field_simp
  · rw [← hQ, hr]
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply, Pi.smul_apply, smul_eq_mul]
    have := (hP0 ω).ne'
    field_simp

/-- Cochrane (2023), p. 9: "bond sales `B₀` raise real revenue equal to `βE₀(s₁)`": in every
equilibrium `Q₀B₀/P₀ = βE₀s₁`, whatever the quantity `B₀` sold (`PullOut`, `B₀` known at 0). -/
theorem revenue_invariant (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ} (hkB0 : Known 𝔼 0 B0)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0) : Q0 * B0 / P0 = β • 𝔼.E 0 s1 := by
  obtain ⟨hP0, -, hk, -, hQ, h1⟩ := he
  rw [revenue_eq 𝔼 hP hk hkB0 hQ h1]
  funext ω
  simp only [Pi.mul_apply, Pi.div_apply, Pi.smul_apply, smul_eq_mul]
  have := (hP0 ω).ne'
  field_simp

/-! ### The share split -/

/-- Cochrane (2023), p. 9: **share split.** If `(P₀, P₁, Q₀)` is an equilibrium and the
government sells `κB₀` (`κ > 0`) with unchanged surpluses, then `(P₀, κP₁, Q₀/κ)` is an
equilibrium: `P₀` does not change, `P₁` rises in proportion, the bond price falls. -/
theorem shareSplit_equilibrium (𝔼 : ExpectationSystem Ω) {β k : ℝ} (hk : 0 < k)
    {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ} (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0) :
    Equilibrium 𝔼 β Bm1 (k • B0) s0 s1 P0 (k • P1) (k⁻¹ • Q0) := by
  obtain ⟨hP0, hP1, hkP0, hflow, hQ, h1⟩ := he
  refine ⟨hP0, fun ω => ?_, hkP0, ?_, ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_pos hk (hP1 ω)
  · funext ω
    have e := congrFun hflow ω
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    rw [e]
    field_simp
  · have e : P0 / k • P1 = k⁻¹ • (P0 / P1) := by
      funext ω
      simp only [Pi.div_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
    unfold BondPrice0 at hQ ⊢
    rw [e, map_smul, hQ, smul_comm]
  · funext ω
    have e := congrFun h1 ω
    simp only [Pi.div_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    rw [← e]
    have := (hP1 ω).ne'
    field_simp

/-- Cochrane (2023), p. 9: the share split's equilibrium is the only one: under the hypotheses
of `equilibrium_existsUnique`, every equilibrium of the economy with debt `κB₀` is
`(P₀, κP₁, Q₀/κ)`. -/
theorem shareSplit_unique (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β k : ℝ} (hk : 0 < k)
    {Bm1 B0 s0 s1 P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω)
    (hkBm1 : Known 𝔼 0 Bm1) (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0)
    (hks0 : Known 𝔼 0 s0) (hs1 : ∀ ω, 0 < s1 ω) (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 (k • B0) s0 s1 P0' P1' Q0') :
    P0' = P0 ∧ P1' = k • P1 ∧ Q0' = k⁻¹ • Q0 := by
  have hB0' : ∀ ω, 0 < (k • B0) ω := fun ω => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact mul_pos hk (hB0 ω)
  have hu := equilibrium_existsUnique 𝔼 hP hBm1 hkBm1 hB0' (known_smul 𝔼 k hkB0) hks0 hs1 hpv
  have := hu.unique (y₁ := (P0', P1', Q0')) (y₂ := (P0, k • P1, k⁻¹ • Q0)) he'
    (shareSplit_equilibrium 𝔼 hk he)
  simp only [Prod.mk.injEq] at this
  exact this

/-- Cochrane (2023), p. 9: "a doubling of `B₀` with no change in surpluses halves the bond
price … doubling debt `B₀` doubles the price level `P₁`" (and leaves `P₀`). -/
theorem doubling (𝔼 : ExpectationSystem Ω) {β : ℝ} {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ}
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0) :
    Equilibrium 𝔼 β Bm1 ((2 : ℝ) • B0) s0 s1 P0 ((2 : ℝ) • P1) ((2 : ℝ)⁻¹ • Q0) :=
  shareSplit_equilibrium 𝔼 two_pos he

/-- Cochrane (2023), eq. (1.3), p. 8: the nominal rate `i₀ = 1/Q₀ − 1` is strictly decreasing
in the bond price on `Q₀ > 0`. -/
theorem rate_strictAnti {Q Q' : ℝ} (hQ : 0 < Q) (hQQ' : Q < Q') : 1 / Q' - 1 < 1 / Q - 1 := by
  have := one_div_lt_one_div_of_lt hQ hQQ'
  linarith

/-- Cochrane (2023), p. 9: selling more debt `κB₀` (`κ > 1`) with unchanged surpluses "raises
the nominal interest rate": with `Q₀ > 0`, `rate (Q₀/κ) > rate Q₀` in every state. -/
theorem shareSplit_rate_rises {k : ℝ} (hk : 1 < k) {Q0 : Ω → ℝ} (hQ : ∀ ω, 0 < Q0 ω) (ω : Ω) :
    rate Q0 ω < rate (k⁻¹ • Q0) ω := by
  simp only [rate, Pi.smul_apply, smul_eq_mul]
  have hk0 : 0 < k⁻¹ * Q0 ω := mul_pos (inv_pos.mpr (by linarith)) (hQ ω)
  refine rate_strictAnti hk0 ?_
  have : k⁻¹ < 1 := inv_lt_one_of_one_lt₀ hk
  nlinarith [hQ ω]

/-! ### The interest-rate target -/

/-- Cochrane (2023), p. 10: an equilibrium under the interest-rate target `i₀` (the government
offers any quantity of bonds at `Q₀ = 1/(1 + i₀)`): the quantity `B₀` is now endogenous,
known at date 0 and positive, and `(P₀, P₁, Q₀ = 1/(1 + i₀))` is an equilibrium given it. -/
def TargetEquilibrium (𝔼 : ExpectationSystem Ω) (β i0 : ℝ) (Bm1 s0 s1 P0 B0 P1 : Ω → ℝ) :
    Prop :=
  Known 𝔼 0 B0 ∧ (∀ ω, 0 < B0 ω) ∧
    Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 (fun _ => 1 / (1 + i0))

/-- Cochrane (2023), eq. (1.9), p. 10: in an equilibrium with `Q₀ = 1/(1 + i₀)`, the target
sets expected inflation: `E₀(P₀/P₁) = 1/(β(1 + i₀))` (`β ≠ 0`, `i₀ ≠ −1`). -/
theorem expected_inflation (𝔼 : ExpectationSystem Ω) {β i0 : ℝ} (hβ : β ≠ 0)
    (hi : 1 + i0 ≠ 0) {Bm1 B0 s0 s1 P0 P1 : Ω → ℝ}
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 (fun _ => 1 / (1 + i0))) (ω : Ω) :
    𝔼.E 0 (P0 / P1) ω = 1 / (β * (1 + i0)) := by
  obtain ⟨-, -, -, -, hQ, -⟩ := he
  have e := congrFun hQ ω
  simp only [Pi.smul_apply, smul_eq_mul] at e
  rw [div_eq_iff hi] at e
  rw [eq_div_iff (mul_ne_zero hβ hi)]
  linear_combination -e

/-- Cochrane (2023), eq. (1.9), p. 10: "really, by lowering `E(1/P₁)`":
`E₀(1/P₁) = 1/(β(1 + i₀)P₀)` (`PullOut`, `β ≠ 0`, `i₀ ≠ −1`). -/
theorem E0_invP1 (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β i0 : ℝ} (hβ : β ≠ 0)
    (hi : 1 + i0 ≠ 0) {Bm1 B0 s0 s1 P0 P1 : Ω → ℝ}
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 (fun _ => 1 / (1 + i0))) (ω : Ω) :
    𝔼.E 0 (1 / P1) ω = 1 / (β * (1 + i0) * P0 ω) := by
  have hP0 := he.1 ω
  have hk := he.2.2.1
  have h := expected_inflation 𝔼 hβ hi he ω
  have hpo : 𝔼.E 0 (P0 / P1) = P0 * 𝔼.E 0 (1 / P1) := by
    rw [← hP 0 P0 _ hk]
    congr 1
    funext ω
    simp only [Pi.div_apply, Pi.mul_apply, Pi.one_apply]
    ring
  rw [hpo] at h
  simp only [Pi.mul_apply] at h
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero hβ hi) hP0.ne')]
  rw [eq_div_iff (mul_ne_zero hβ hi)] at h
  linear_combination h

/-- Cochrane (2023), p. 10: under the target, the quantity of bonds people buy at the fixed
price ("a flat supply curve") is `B₀ = (1 + i₀)P₀βE₀s₁` (`PullOut`, `i₀ ≠ −1`). -/
theorem target_bond_demand (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β i0 : ℝ}
    (hi : 1 + i0 ≠ 0) {Bm1 s0 s1 P0 B0 P1 : Ω → ℝ}
    (he : TargetEquilibrium 𝔼 β i0 Bm1 s0 s1 P0 B0 P1) :
    B0 = (fun _ => 1 + i0) * P0 * (β • 𝔼.E 0 s1) := by
  obtain ⟨hkB0, -, -, -, hk, -, hQ, h1⟩ := he
  have hr := revenue_eq 𝔼 hP hk hkB0 hQ h1
  funext ω
  have e := congrFun hr ω
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
  rw [div_mul_eq_mul_div, div_eq_iff hi] at e
  linear_combination e

/-- Cochrane (2023), p. 10: **inflation is stable and determinate under an interest-rate
target, even a peg.** For every `i₀ > −1`, with `PullOut`, `B₋₁ > 0` and `s₀` known at 0,
`s₁ > 0`, `E₀s₁ > 0` and a positive present value, there is exactly one equilibrium
`(P₀, B₀, P₁)`: `P₀ = B₋₁/(s₀ + βE₀s₁)`, `B₀ = (1 + i₀)P₀βE₀s₁`, `P₁ = B₀/s₁`. -/
theorem target_existsUnique (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β i0 : ℝ}
    (hβ : 0 < β) (hi : -1 < i0) {Bm1 s0 s1 : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω)
    (hkBm1 : Known 𝔼 0 Bm1) (hks0 : Known 𝔼 0 s0) (hs1 : ∀ ω, 0 < s1 ω)
    (hEs1 : ∀ ω, 0 < 𝔼.E 0 s1 ω) (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω) :
    ∃! p : (Ω → ℝ) × (Ω → ℝ) × (Ω → ℝ),
      TargetEquilibrium 𝔼 β i0 Bm1 s0 s1 p.1 p.2.1 p.2.2 := by
  have hi' : 0 < 1 + i0 := by linarith
  set P0 := Bm1 / pv 𝔼 β s0 s1 with hP0def
  have hP0 : ∀ ω, 0 < P0 ω := fun ω => div_pos (hBm1 ω) (hpv ω)
  have hkP0 : Known 𝔼 0 P0 :=
    known_div 𝔼 hP hkBm1 (known_pv 𝔼 β hks0 s1) (fun ω => (hpv ω).ne')
  set B0 := (fun _ => 1 + i0) * P0 * (β • 𝔼.E 0 s1) with hB0def
  have hB0 : ∀ ω, 0 < B0 ω := fun ω => by
    simp only [hB0def, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    have := hP0 ω; have := hEs1 ω; positivity
  have hkB0 : Known 𝔼 0 B0 :=
    known_mul 𝔼 hP (known_mul 𝔼 hP (known_const 𝔼 0 _) hkP0)
      (known_smul 𝔼 β (known_E 𝔼 0 s1))
  refine ⟨(P0, B0, B0 / s1), ⟨hkB0, hB0, ?_⟩, ?_⟩
  · refine (equilibrium_iff 𝔼 hP hB0 hkB0 hs1 hpv).mpr ⟨hP0, hkP0, rfl, rfl, ?_⟩
    -- the bond price at the target
    have hkr : Known 𝔼 0 (P0 / B0) := known_div 𝔼 hP hkP0 hkB0 (fun ω => (hB0 ω).ne')
    have e1 : P0 / (B0 / s1) = (P0 / B0) * s1 := by
      funext ω
      simp only [Pi.div_apply, Pi.mul_apply]
      have := (hB0 ω).ne'; have := (hs1 ω).ne'
      field_simp
    unfold BondPrice0
    rw [e1, hP 0 _ _ hkr]
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply, Pi.smul_apply, smul_eq_mul, hB0def]
    have := (hP0 ω).ne'; have := (hEs1 ω).ne'
    field_simp
  · rintro ⟨P0', B0', P1'⟩ ⟨hkB0', hB0', he⟩
    simp only at hkB0' hB0' he
    have hdem := target_bond_demand 𝔼 hP hi'.ne' ⟨hkB0', hB0', he⟩
    obtain ⟨-, -, h1, h0, -⟩ := (equilibrium_iff 𝔼 hP hB0' hkB0' hs1 hpv).mp he
    have hP0eq : P0' = P0 := h0
    rw [hP0eq] at hdem
    rw [hP0eq, h1, hdem]

/-- Cochrane (2023), p. 10: "inflation is stable and determinate even with an interest-rate
peg" — the peg `i₀` determines `(P₀, B₀, P₁)` uniquely (`target_existsUnique`). -/
theorem determinate_under_peg (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β i0 : ℝ}
    (hβ : 0 < β) (hi : -1 < i0) {Bm1 s0 s1 : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω)
    (hkBm1 : Known 𝔼 0 Bm1) (hks0 : Known 𝔼 0 s0) (hs1 : ∀ ω, 0 < s1 ω)
    (hEs1 : ∀ ω, 0 < 𝔼.E 0 s1 ω) (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω)
    {P0 B0 P1 P0' B0' P1' : Ω → ℝ} (he : TargetEquilibrium 𝔼 β i0 Bm1 s0 s1 P0 B0 P1)
    (he' : TargetEquilibrium 𝔼 β i0 Bm1 s0 s1 P0' B0' P1') :
    P0 = P0' ∧ B0 = B0' ∧ P1 = P1' := by
  have := (target_existsUnique 𝔼 hP hβ hi hBm1 hkBm1 hks0 hs1 hEs1 hpv).unique
    (y₁ := (P0, B0, P1)) (y₂ := (P0', B0', P1')) he he'
  simp only [Prod.mk.injEq] at this
  exact this

/-- Cochrane (2023), p. 10, the **Fisherian** response: a higher target `i₀ < i₀'` has no effect
on `P₀` (hence on contemporaneous inflation `P₀/P₋₁`) and raises `P₁` in every state, lowering
`E₀(1/P₁)` (`PullOut`, `E₀s₁ > 0`). -/
theorem fisherian_two_period (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β i0 i0' : ℝ}
    (hβ : 0 < β) (hi : -1 < i0) (hii' : i0 < i0') {Bm1 s0 s1 : Ω → ℝ}
    (hs1 : ∀ ω, 0 < s1 ω) (hEs1 : ∀ ω, 0 < 𝔼.E 0 s1 ω) (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω)
    {P0 B0 P1 P0' B0' P1' : Ω → ℝ} (he : TargetEquilibrium 𝔼 β i0 Bm1 s0 s1 P0 B0 P1)
    (he' : TargetEquilibrium 𝔼 β i0' Bm1 s0 s1 P0' B0' P1') :
    P0' = P0 ∧ (∀ ω, P1 ω < P1' ω) ∧ ∀ ω, 𝔼.E 0 (1 / P1') ω < 𝔼.E 0 (1 / P1) ω := by
  have hd := target_bond_demand 𝔼 hP (by linarith) he
  have hd' := target_bond_demand 𝔼 hP (by linarith) he'
  obtain ⟨hkB0, hB0, hq⟩ := he
  obtain ⟨hkB0', hB0', hq'⟩ := he'
  obtain ⟨hP0, -, h1, h0, -⟩ := (equilibrium_iff 𝔼 hP hB0 hkB0 hs1 hpv).mp hq
  obtain ⟨-, -, h1', h0', -⟩ := (equilibrium_iff 𝔼 hP hB0' hkB0' hs1 hpv).mp hq'
  have hPP : P0' = P0 := by rw [h0, h0']
  refine ⟨hPP, fun ω => ?_, fun ω => ?_⟩
  · rw [h1, h1', hd, hd', hPP]
    simp only [Pi.div_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    refine div_lt_div_of_pos_right ?_ (hs1 ω)
    have := hP0 ω; have := hEs1 ω
    have : 0 < P0 ω * (β * 𝔼.E 0 s1 ω) := by positivity
    nlinarith
  · rw [E0_invP1 𝔼 hP hβ.ne' (by linarith) hq' ω, E0_invP1 𝔼 hP hβ.ne' (by linarith) hq ω, hPP]
    have := hP0 ω
    have h1i : 0 < 1 + i0 := by linarith
    refine one_div_lt_one_div_of_lt (by positivity) ?_
    have : 0 < β * P0 ω := by positivity
    nlinarith

/-! ### (1.10): fiscal policy sets unexpected inflation -/

/-- Cochrane (2023), p. 10: the innovation `(E₁ − E₀)x`. -/
noncomputable def innov (𝔼 : ExpectationSystem Ω) (x : Ω → ℝ) : Ω → ℝ :=
  𝔼.E 1 x - 𝔼.E 0 x

/-- Cochrane (2023), eq. (1.10), p. 10: multiplying (1.6) by `P₀` and taking innovations,
`(B₀/P₀)(E₁ − E₀)(P₀/P₁) = (E₁ − E₀)s₁` (`PullOut`; `B₀, P₀` known at 0; `P₀ > 0`). -/
theorem unexpected_inflation (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut)
    {B0 s1 P0 P1 : Ω → ℝ} (hP0 : ∀ ω, 0 < P0 ω) (hkP0 : Known 𝔼 0 P0) (hkB0 : Known 𝔼 0 B0)
    (h1 : Valuation1 B0 P1 s1) : (B0 / P0) * innov 𝔼 (P0 / P1) = innov 𝔼 s1 := by
  have hk0 : Known 𝔼 0 (B0 / P0) := known_div 𝔼 hP hkB0 hkP0 (fun ω => (hP0 ω).ne')
  have hk1 : Known 𝔼 1 (B0 / P0) := known_mono 𝔼 zero_le_one hk0
  have e : B0 / P0 * (P0 / P1) = s1 := by
    rw [← h1]
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply]
    have := (hP0 ω).ne'
    field_simp
  unfold innov
  rw [mul_sub, ← hP 1 _ _ hk1, ← hP 0 _ _ hk0, e]

/-- Cochrane (2023), pp. 10, "(1.9)–(1.10) completely determine expected and unexpected
inflation": under the target `i₀`, with `s₁` known at date 1 (`PullOut`, `β ≠ 0`),
`P₀/P₁ = 1/(β(1 + i₀)) + (P₀/B₀)(E₁ − E₀)s₁` in every state. -/
theorem inflation_decomposition (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β i0 : ℝ}
    (hβ : β ≠ 0) (hi : 1 + i0 ≠ 0) {Bm1 s0 s1 P0 B0 P1 : Ω → ℝ} (hks1 : Known 𝔼 1 s1)
    (he : TargetEquilibrium 𝔼 β i0 Bm1 s0 s1 P0 B0 P1) (ω : Ω) :
    P0 ω / P1 ω = 1 / (β * (1 + i0)) + P0 ω / B0 ω * innov 𝔼 s1 ω := by
  obtain ⟨hkB0, hB0, hq⟩ := he
  obtain ⟨hP0, hP1, hkP0, -, -, h1⟩ := id hq
  have hk0 : Known 𝔼 0 (P0 / B0) := known_div 𝔼 hP hkP0 hkB0 (fun ω => (hB0 ω).ne')
  have e : P0 / P1 = (P0 / B0) * s1 := by
    rw [← h1]
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply]
    have := (hB0 ω).ne'; have := (hP1 ω).ne'
    field_simp
  have hkr : Known 𝔼 1 (P0 / P1) := by
    rw [e]; exact known_mul 𝔼 hP (known_mono 𝔼 zero_le_one hk0) hks1
  have hu := congrFun (unexpected_inflation 𝔼 hP hP0 hkP0 hkB0 h1) ω
  have hexp := expected_inflation 𝔼 hβ hi hq ω
  have hin : innov 𝔼 (P0 / P1) ω = (P0 / P1) ω - 𝔼.E 0 (P0 / P1) ω := by
    simp only [innov, Pi.sub_apply]
    rw [hkr]
  simp only [Pi.mul_apply] at hu
  simp only [Pi.div_apply] at hu hin
  have := (hB0 ω).ne'; have := (hP0 ω).ne'
  have hsub : innov 𝔼 (P0 / P1) ω = P0 ω / B0 ω * innov 𝔼 s1 ω := by
    rw [← hu]; field_simp
  rw [← hexp]
  linarith

/-- Cochrane (2023), p. 10: without fiscal news (`s₁` known at date 0, so `(E₁ − E₀)s₁ = 0`),
inflation under the target equals expected inflation: `P₀/P₁ = 1/(β(1 + i₀))` in every state. -/
theorem no_fiscal_news (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β i0 : ℝ}
    (hβ : β ≠ 0) (hi : 1 + i0 ≠ 0) {Bm1 s0 s1 P0 B0 P1 : Ω → ℝ} (hks1 : Known 𝔼 0 s1)
    (he : TargetEquilibrium 𝔼 β i0 Bm1 s0 s1 P0 B0 P1) (ω : Ω) :
    P0 ω / P1 ω = 1 / (β * (1 + i0)) := by
  rw [inflation_decomposition 𝔼 hP hβ hi (known_mono 𝔼 zero_le_one hks1) he ω]
  have : innov 𝔼 s1 ω = 0 := by
    simp only [innov, Pi.sub_apply]
    rw [known_mono 𝔼 zero_le_one hks1, hks1, sub_self]
  rw [this, mul_zero, add_zero]

end Cochrane.TwoPeriodModel.MonetaryFiscal
