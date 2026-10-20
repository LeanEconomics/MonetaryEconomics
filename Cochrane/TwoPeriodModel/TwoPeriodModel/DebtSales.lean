/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TwoPeriodModel.MonetaryFiscal

/-!
# Fiscal policy debt sales

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 1, §1.5, pp. 10–13 and
Table 1.1, p. 11.

Comparative statics of the two-period equilibrium of `TwoPeriod` when debt sales come with
changes in surpluses. Every comparison is between two equilibria (old and new policy) of the
same `ExpectationSystem` with `PullOut`; the price levels are read off `equilibrium_iff`
(`P₁ = B₀/s₁`, `P₀ = B₋₁/(s₀ + βE₀s₁)`) and the end-of-period real value of debt off
`revenue_invariant` (`Q₀B₀/P₀ = βE₀s₁`).

## Main results

* Box p. 10 / p. 11, the **equity issue**: `equityIssue_price1` (raising `B₀` and `s₁` in
  proportion leaves `P₁`), `equityIssue_revenue` (revenue is multiplied by `κ`),
  `equityIssue_lowers_price0` (the revenue can lower `P₀`), `equityIssue_funds_deficit`
  (or fund a deficit `s₀ − (κ − 1)βE₀s₁` with `P₀` unchanged).
* Table 1.1, row "Borrow", pp. 11–12: `borrow_price0`, `borrow_value_rises`,
  `borrow_keeps_price1_iff`, and `borrow_implementable` (under genuine uncertainty the borrowing
  strategy is implemented by scaling `B₀` and `s₁` by the date-0 factor
  `c = 1 − Δs₀/(βE₀s₁)`; then `P₀`, `P₁` and `Q₀` are all unchanged).
  **Error E1** (p. 12): the printed condition `(B₀ + ΔB₀)/P₁ = s₁ + RΔs₀` should read
  `s₁ − RΔs₀`: `borrow_debt_corrected` and the counterexample `borrow_printed_fails`.
* Table 1.1, row "Inflate": `inflate_price0_rises`, `inflate_value_unchanged`,
  `inflate_real_debt_falls_by_deficit` (`B₋₁/P₀` falls by exactly the fall in `s₀`).
* Table 1.1, row "AR(1)": `ar1_price0_rises_more`, `ar1_value_falls`.
* p. 12, the "s-shaped" surplus: `sShape_two_period` (a deficit with a rising value of debt
  requires expected future surpluses to rise), `steady_price0_iff` (a completely steady `P₀`
  despite a deficit iff `Δs₀ + βΔE₀s₁ = 0`).
-/

namespace Cochrane.TwoPeriodModel.DebtSales

open Cochrane.TwoPeriodModel.TwoPeriod Cochrane.TwoPeriodModel.MonetaryFiscal

variable {Ω : Type*}

/-- Cochrane (2023), eq. (1.5), p. 8: in an equilibrium, `P₀ = B₋₁/(s₀ + βE₀s₁)` state by state
(`PullOut`, `B₀ > 0` known at 0, `s₁ > 0`, positive present value). -/
theorem price0_formula (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β : ℝ}
    {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ} (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0)
    (hs1 : ∀ ω, 0 < s1 ω) (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0) (ω : Ω) :
    P0 ω = Bm1 ω / (s0 ω + β * 𝔼.E 0 s1 ω) := by
  obtain ⟨-, -, -, h0, -⟩ := (equilibrium_iff 𝔼 hP hB0 hkB0 hs1 hpv).mp he
  rw [h0]
  rfl

/-! ### The equity issue -/

/-- Cochrane (2023), eq. (1.11), p. 11: "if the government raises `B₀` and `s₁` proportionally,
there is no effect on the price level at time 1": with `κ > 0`, `s₁ > 0`, `P₁, P₁' > 0`,
`B₀/P₁ = s₁` and `κB₀/P₁' = κs₁` give `P₁' = P₁`. -/
theorem equityIssue_price1 {k : ℝ} (hk : 0 < k) {B0 s1 P1 P1' : Ω → ℝ}
    (hs1 : ∀ ω, 0 < s1 ω) (hP1 : ∀ ω, 0 < P1 ω) (hP1' : ∀ ω, 0 < P1' ω)
    (h1 : Valuation1 B0 P1 s1) (h1' : Valuation1 (k • B0) P1' (k • s1)) : P1' = P1 := by
  have hks : ∀ ω, (k • s1) ω ≠ 0 := fun ω => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact (mul_pos hk (hs1 ω)).ne'
  rw [price1_eq (fun ω => (hP1' ω).ne') hks h1',
    price1_eq (fun ω => (hP1 ω).ne') (fun ω => (hs1 ω).ne') h1]
  funext ω
  simp only [Pi.div_apply, Pi.smul_apply, smul_eq_mul]
  have := hk.ne'
  field_simp

/-- Cochrane (2023), eq. (1.12), p. 11: the equity issue raises the end-of-period real value of
debt and the real revenue from selling it: with debt `κB₀`
and surplus `κs₁` (any `s₀'`), `Q₀'B₀'/P₀' = κ · Q₀B₀/P₀` (`PullOut`, `B₀` known at 0). -/
theorem equityIssue_revenue (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β k : ℝ}
    {Bm1 B0 s0 s0' s1 P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hkB0 : Known 𝔼 0 B0)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 (k • B0) s0' (k • s1) P0' P1' Q0') :
    Q0' * (k • B0) / P0' = k • (Q0 * B0 / P0) := by
  rw [revenue_invariant 𝔼 hP (known_smul 𝔼 k hkB0) he', revenue_invariant 𝔼 hP hkB0 he,
    map_smul, smul_comm]

/-- Cochrane (2023), p. 11: "or additional revenue can be used to lower the price level `P₀`":
with `s₀` unchanged, `κ > 1`, `β > 0`, `B₋₁ > 0` and `E₀s₁ > 0`, the equity issue lowers `P₀` in
every state (`PullOut`, `B₀ > 0` known at 0, `s₁ > 0`, positive present value). -/
theorem equityIssue_lowers_price0 (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β k : ℝ}
    (hβ : 0 < β) (hk : 1 < k) {Bm1 B0 s0 s1 P0 P1 Q0 P0' P1' Q0' : Ω → ℝ}
    (hBm1 : ∀ ω, 0 < Bm1 ω) (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0)
    (hs1 : ∀ ω, 0 < s1 ω) (hEs1 : ∀ ω, 0 < 𝔼.E 0 s1 ω) (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 (k • B0) s0 (k • s1) P0' P1' Q0') (ω : Ω) :
    P0' ω < P0 ω := by
  have hk0 : 0 < k := by linarith
  have hpvω : 0 < s0 ω + β * 𝔼.E 0 s1 ω := hpv ω
  have hlt : s0 ω + β * 𝔼.E 0 s1 ω < s0 ω + β * 𝔼.E 0 (k • s1) ω := by
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    have := hEs1 ω
    nlinarith [mul_pos (mul_pos hβ this) (sub_pos.mpr hk)]
  have hpv' : ∀ ω, 0 < pv 𝔼 β s0 (k • s1) ω := fun ω => by
    simp only [pv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_smul]
    have hp := hpv ω; have hE := hEs1 ω
    simp only [pv, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hp
    nlinarith [mul_pos (mul_pos hβ hE) (sub_pos.mpr hk)]
  have hB0' : ∀ ω, 0 < (k • B0) ω := fun ω => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact mul_pos hk0 (hB0 ω)
  have hs1' : ∀ ω, 0 < (k • s1) ω := fun ω => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact mul_pos hk0 (hs1 ω)
  rw [price0_formula 𝔼 hP hB0 hkB0 hs1 hpv he ω,
    price0_formula 𝔼 hP hB0' (known_smul 𝔼 k hkB0) hs1' hpv' he' ω]
  exact div_lt_div_of_pos_left (hBm1 ω) hpvω hlt

/-- Cochrane (2023), p. 11: "the additional revenue can fund a deficit, a decline in `s₀`, with
no change in `P₀` or `P₁`": with `s₀' = s₀ − (κ − 1)βE₀s₁` and `(κB₀, κs₁)`, `P₀' = P₀` (and
`P₁' = P₁` by `equityIssue_price1`). -/
theorem equityIssue_funds_deficit (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β k : ℝ}
    (hk : 0 < k) {Bm1 B0 s0 s1 P0 P1 Q0 P0' P1' Q0' : Ω → ℝ}
    (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0)
    (hs1 : ∀ ω, 0 < s1 ω) (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 (k • B0) (s0 - ((k - 1) * β) • 𝔼.E 0 s1) (k • s1) P0' P1' Q0') :
    P0' = P0 := by
  have hsame : pv 𝔼 β (s0 - ((k - 1) * β) • 𝔼.E 0 s1) (k • s1) = pv 𝔼 β s0 s1 := by
    funext ω
    simp only [pv, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_smul]
    ring
  have hpv' : ∀ ω, 0 < pv 𝔼 β (s0 - ((k - 1) * β) • 𝔼.E 0 s1) (k • s1) ω :=
    fun ω => hsame ▸ hpv ω
  have hB0' : ∀ ω, 0 < (k • B0) ω := fun ω => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact mul_pos hk (hB0 ω)
  have hs1' : ∀ ω, 0 < (k • s1) ω := fun ω => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact mul_pos hk (hs1 ω)
  obtain ⟨-, -, -, h0, -⟩ := (equilibrium_iff 𝔼 hP hB0 hkB0 hs1 hpv).mp he
  obtain ⟨-, -, -, h0', -⟩ :=
    (equilibrium_iff 𝔼 hP hB0' (known_smul 𝔼 k hkB0) hs1' hpv').mp he'
  rw [h0', h0, hsame]

/-! ### Table 1.1: financing a deficit `Δs₀ < 0` -/

/-- Cochrane (2023), Table 1.1, row "Borrow", p. 12: lowering `s₀` by `Δ` and raising expected
`s₁` by `−RΔ` (`R = 1/β`) leaves the present value, hence `P₀`, unchanged: if
`E₀s₁' = E₀s₁ − Δ/β`, the equilibrium `P₀'` of `(B₀', s₀ + Δ, s₁')` equals `P₀`. -/
theorem borrow_price0 (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β Δ : ℝ} (hβ : β ≠ 0)
    {Bm1 B0 B0' s0 s1 s1' P0 P1 Q0 P0' P1' Q0' : Ω → ℝ}
    (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0) (hB0' : ∀ ω, 0 < B0' ω)
    (hkB0' : Known 𝔼 0 B0') (hs1 : ∀ ω, 0 < s1 ω) (hs1' : ∀ ω, 0 < s1' ω)
    (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω) (hE : 𝔼.E 0 s1' = 𝔼.E 0 s1 - fun _ => Δ / β)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 B0' (s0 + fun _ => Δ) s1' P0' P1' Q0') : P0' = P0 := by
  have hsame : pv 𝔼 β (s0 + fun _ => Δ) s1' = pv 𝔼 β s0 s1 := by
    funext ω
    simp only [pv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hE, Pi.sub_apply]
    field_simp
    ring
  have hpv' : ∀ ω, 0 < pv 𝔼 β (s0 + fun _ => Δ) s1' ω := fun ω => hsame ▸ hpv ω
  obtain ⟨-, -, -, h0, -⟩ := (equilibrium_iff 𝔼 hP hB0 hkB0 hs1 hpv).mp he
  obtain ⟨-, -, -, h0', -⟩ := (equilibrium_iff 𝔼 hP hB0' hkB0' hs1' hpv').mp he'
  rw [h0', h0, hsame]

/-- Cochrane (2023), Table 1.1, row "Borrow", p. 12: the end-of-period real value of debt
`Q₀B₀/P₀` rises by exactly `−Δ` (by `−Δ > 0` for a deficit `Δ < 0`). -/
theorem borrow_value_rises (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β Δ : ℝ} (hβ : β ≠ 0)
    {Bm1 B0 B0' s0 s1 s1' P0 P1 Q0 P0' P1' Q0' : Ω → ℝ}
    (hkB0 : Known 𝔼 0 B0) (hkB0' : Known 𝔼 0 B0')
    (hE : 𝔼.E 0 s1' = 𝔼.E 0 s1 - fun _ => Δ / β)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 B0' (s0 + fun _ => Δ) s1' P0' P1' Q0') :
    Q0' * B0' / P0' = Q0 * B0 / P0 - fun _ => Δ := by
  rw [revenue_invariant 𝔼 hP hkB0' he', revenue_invariant 𝔼 hP hkB0 he, hE]
  funext ω
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp

/-- Cochrane (2023), Table 1.1, row "Borrow", p. 12: the new equilibrium leaves `P₁` unchanged
in every state iff the new debt is scaled like the new surplus, `B₀' s₁ = B₀ s₁'`
(`s₁, s₁', P₁, P₁' > 0`). -/
theorem borrow_keeps_price1_iff {B0 B0' s1 s1' P1 P1' : Ω → ℝ} (hs1 : ∀ ω, 0 < s1 ω)
    (hs1' : ∀ ω, 0 < s1' ω) (hP1 : ∀ ω, 0 < P1 ω) (hP1' : ∀ ω, 0 < P1' ω)
    (h1 : Valuation1 B0 P1 s1) (h1' : Valuation1 B0' P1' s1') :
    P1' = P1 ↔ B0' * s1 = B0 * s1' := by
  rw [price1_eq (fun ω => (hP1' ω).ne') (fun ω => (hs1' ω).ne') h1',
    price1_eq (fun ω => (hP1 ω).ne') (fun ω => (hs1 ω).ne') h1]
  constructor
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.div_apply, Pi.mul_apply] at e ⊢
    have := (hs1 ω).ne'; have := (hs1' ω).ne'
    field_simp at e
    linarith
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.div_apply, Pi.mul_apply] at e ⊢
    have := (hs1 ω).ne'; have := (hs1' ω).ne'
    field_simp
    linarith

/-- Cochrane (2023), Table 1.1, row "Borrow", p. 12, under genuine uncertainty: scaling debt and
the date-1 surplus by the date-0 factor `c = 1 − Δ/(βE₀s₁)` implements the borrowing strategy
with `P₀`, `P₁` and `Q₀` all unchanged: `(P₀, P₁, Q₀)` is an equilibrium of
`(B₋₁, cB₀, s₀ + Δ, cs₁)`, with `E₀(cs₁) = E₀s₁ − Δ/β` (`PullOut`, `B₀` known at 0, `β > 0`,
`Δ ≤ 0`, `E₀s₁ > 0`). -/
theorem borrow_implementable (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β Δ : ℝ}
    (hβ : 0 < β) (hΔ : Δ ≤ 0) {Bm1 B0 s0 s1 P0 P1 Q0 : Ω → ℝ} (hkB0 : Known 𝔼 0 B0)
    (hEs1 : ∀ ω, 0 < 𝔼.E 0 s1 ω) (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0) :
    let c : Ω → ℝ := fun ω => 1 - Δ / (β * 𝔼.E 0 s1 ω)
    (∀ ω, 1 ≤ c ω) ∧ 𝔼.E 0 (c * s1) = 𝔼.E 0 s1 - (fun _ => Δ / β) ∧
      Equilibrium 𝔼 β Bm1 (c * B0) (s0 + fun _ => Δ) (c * s1) P0 P1 Q0 := by
  intro c
  obtain ⟨hP0, hP1, hk, hflow, hQ, h1⟩ := he
  have hc1 : ∀ ω, 1 ≤ c ω := fun ω => by
    have : Δ / (β * 𝔼.E 0 s1 ω) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hΔ (mul_pos hβ (hEs1 ω)).le
    simp only [c]; linarith
  have hkc : Known 𝔼 0 c := by
    have e : c = (fun _ => (1 : ℝ)) - (fun _ => Δ) / (β • 𝔼.E 0 s1) := by
      funext ω; simp [c]
    rw [e]
    exact known_sub 𝔼 (known_const 𝔼 0 1) (known_div 𝔼 hP (known_const 𝔼 0 Δ)
      (known_smul 𝔼 β (known_E 𝔼 0 s1)) (fun ω => by
        simp only [Pi.smul_apply, smul_eq_mul]; exact (mul_pos hβ (hEs1 ω)).ne'))
  have hEc : 𝔼.E 0 (c * s1) = 𝔼.E 0 s1 - (fun _ => Δ / β) := by
    rw [hP 0 c s1 hkc]
    funext ω
    simp only [Pi.mul_apply, Pi.sub_apply, c]
    have := (hEs1 ω).ne'; have := hβ.ne'
    field_simp
  refine ⟨hc1, hEc, hP0, hP1, hk, ?_, hQ, ?_⟩
  · have hv := valuation0_of_flow 𝔼 hP hP0 hk hkB0 hflow hQ h1
    have h1' : Valuation1 (c * B0) P1 (c * s1) := by
      rw [Valuation1, ← h1]
      funext ω
      simp only [Pi.mul_apply, Pi.div_apply]
      ring
    refine (flow_iff_valuation0 𝔼 hP hP0 hk (known_mul 𝔼 hP hkc hkB0) hQ h1').mpr ?_
    rw [Valuation0, hv, hEc]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  · rw [Valuation1, ← h1]
    funext ω
    simp only [Pi.mul_apply, Pi.div_apply]
    ring

/-- Cochrane (2023), p. 12 (**error E1**, corrected): with `B₀/P₁ = s₁` (`P₁ ≠ 0`, `β ≠ 0`,
`R = 1/β`), the extra debt `ΔB₀` that keeps `P₁` when `s₁` is raised by `−RΔs₀` satisfies
`(B₀ + ΔB₀)/P₁ = s₁ − RΔs₀`; precisely, `P₁` is the equilibrium price for `(B₀ + ΔB₀, s₁ − RΔs₀)`
iff `ΔB₀ = −RΔs₀P₁`. -/
theorem borrow_debt_corrected {B0 P1 s1 β Δ ΔB : ℝ} (hP1 : P1 ≠ 0) (h1 : B0 / P1 = s1) :
    (B0 + ΔB) / P1 = s1 - Δ / β ↔ ΔB = -(Δ / β) * P1 := by
  rw [← h1, div_eq_iff hP1]
  constructor
  · intro h
    field_simp at h
    have : ΔB = -(P1 * Δ / β) := by linarith
    rw [this]
    ring
  · intro h
    rw [h]
    field_simp
    ring

/-- Cochrane (2023), p. 12 (**error E1**): the printed condition `(B₀ + ΔB₀)/P₁ = s₁ + RΔs₀` is
wrong: with the new surplus `s₁ − RΔs₀` and that debt, the date-1 price level is not `P₁`
whenever `Δs₀ ≠ 0` (here `R = 1/β`, `P₁ ≠ 0`, `β ≠ 0`, `s₁ − RΔs₀ ≠ 0`). -/
theorem borrow_printed_fails {B0 P1 s1 β Δ ΔB : ℝ} (hP1 : P1 ≠ 0) (hβ : β ≠ 0) (hΔ : Δ ≠ 0)
    (hs : s1 - Δ / β ≠ 0) (hprinted : (B0 + ΔB) / P1 = s1 + Δ / β) :
    (B0 + ΔB) / (s1 - Δ / β) ≠ P1 := by
  intro h
  rw [div_eq_iff hs] at h
  rw [div_eq_iff hP1, h] at hprinted
  have : P1 * (2 * (Δ / β)) = 0 := by linarith
  rcases mul_eq_zero.mp this with h0 | h0
  · exact hP1 h0
  · have : Δ / β = 0 := by linarith
    exact hΔ ((div_eq_zero_iff.mp this).resolve_right hβ)

/-- Cochrane (2023), Table 1.1, row "Inflate", p. 12: if `s₀` falls by `Δ < 0` and `s₁` is
unchanged, `P₀` rises in every state (`B₋₁ > 0`, positive present values). -/
theorem inflate_price0_rises (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β Δ : ℝ}
    (hΔ : Δ < 0) {Bm1 B0 B0' s0 s1 P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω)
    (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0) (hB0' : ∀ ω, 0 < B0' ω)
    (hkB0' : Known 𝔼 0 B0') (hs1 : ∀ ω, 0 < s1 ω)
    (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω) (hpv' : ∀ ω, 0 < pv 𝔼 β (s0 + fun _ => Δ) s1 ω)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 B0' (s0 + fun _ => Δ) s1 P0' P1' Q0') (ω : Ω) :
    P0 ω < P0' ω := by
  rw [price0_formula 𝔼 hP hB0 hkB0 hs1 hpv he ω,
    price0_formula 𝔼 hP hB0' hkB0' hs1 hpv' he' ω]
  have h' := hpv' ω
  simp only [pv, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h'
  simp only [Pi.add_apply]
  exact div_lt_div_of_pos_left (hBm1 ω) h' (by linarith)

/-- Cochrane (2023), Table 1.1, row "Inflate", p. 12: the end-of-period value of debt
`Q₀B₀/P₀ = βE₀s₁`, "a claim to unchanged surpluses", does not change. -/
theorem inflate_value_unchanged (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β Δ : ℝ}
    {Bm1 B0 B0' s0 s1 P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hkB0 : Known 𝔼 0 B0)
    (hkB0' : Known 𝔼 0 B0') (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 B0' (s0 + fun _ => Δ) s1 P0' P1' Q0') :
    Q0' * B0' / P0' = Q0 * B0 / P0 := by
  rw [revenue_invariant 𝔼 hP hkB0' he', revenue_invariant 𝔼 hP hkB0 he]

/-- Cochrane (2023), Table 1.1, row "Inflate", p. 12: "the value of the dollars that redeem
bonds `B₋₁` falls by exactly the fall in the surplus `s₀`": `B₋₁/P₀' = B₋₁/P₀ + Δ`. -/
theorem inflate_real_debt_falls_by_deficit (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut)
    {β Δ : ℝ} {Bm1 B0 B0' s0 s1 P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hkB0 : Known 𝔼 0 B0)
    (hkB0' : Known 𝔼 0 B0') (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 B0' (s0 + fun _ => Δ) s1 P0' P1' Q0') :
    Bm1 / P0' = Bm1 / P0 + fun _ => Δ := by
  obtain ⟨hP0, -, hk, hflow, hQ, h1⟩ := he
  obtain ⟨hP0', -, hk', hflow', hQ', h1'⟩ := he'
  rw [valuation0_of_flow 𝔼 hP hP0' hk' hkB0' hflow' hQ' h1',
    valuation0_of_flow 𝔼 hP hP0 hk hkB0 hflow hQ h1]
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), Table 1.1, row "AR(1)", p. 12: if `s₁` falls along with `s₀`
(`E₀s₁' = E₀s₁ + ηΔ`, `η > 0`, `Δ < 0`, `β > 0`), `P₀` rises even more than under "Inflate":
`P₀ < P₀^{inflate} < P₀^{AR(1)}` in every state. -/
theorem ar1_price0_rises_more (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β Δ η : ℝ}
    (hβ : 0 < β) (hΔ : Δ < 0) (hη : 0 < η)
    {Bm1 B0 Bi Ba s0 s1 sa P0 P1 Q0 Pi0 Pi1 Qi Pa0 Pa1 Qa : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω)
    (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0) (hBi : ∀ ω, 0 < Bi ω)
    (hkBi : Known 𝔼 0 Bi) (hBa : ∀ ω, 0 < Ba ω) (hkBa : Known 𝔼 0 Ba)
    (hs1 : ∀ ω, 0 < s1 ω) (hsa : ∀ ω, 0 < sa ω)
    (hEa : 𝔼.E 0 sa = 𝔼.E 0 s1 + fun _ => η * Δ)
    (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω) (hpva : ∀ ω, 0 < pv 𝔼 β (s0 + fun _ => Δ) sa ω)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (hei : Equilibrium 𝔼 β Bm1 Bi (s0 + fun _ => Δ) s1 Pi0 Pi1 Qi)
    (hea : Equilibrium 𝔼 β Bm1 Ba (s0 + fun _ => Δ) sa Pa0 Pa1 Qa) (ω : Ω) :
    P0 ω < Pi0 ω ∧ Pi0 ω < Pa0 ω := by
  have hpvi : ∀ ω, 0 < pv 𝔼 β (s0 + fun _ => Δ) s1 ω := fun ω => by
    have := hpva ω
    simp only [pv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hEa] at this ⊢
    have : β * (η * Δ) < 0 := mul_neg_of_pos_of_neg hβ (mul_neg_of_pos_of_neg hη hΔ)
    linarith
  refine ⟨inflate_price0_rises 𝔼 hP hΔ hBm1 hB0 hkB0 hBi hkBi hs1 hpv hpvi he hei ω, ?_⟩
  rw [price0_formula 𝔼 hP hBi hkBi hs1 hpvi hei ω,
    price0_formula 𝔼 hP hBa hkBa hsa hpva hea ω]
  have h' := hpva ω
  simp only [pv, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h'
  simp only [Pi.add_apply, hEa] at h' ⊢
  have : β * (η * Δ) < 0 := mul_neg_of_pos_of_neg hβ (mul_neg_of_pos_of_neg hη hΔ)
  exact div_lt_div_of_pos_left (hBm1 ω) h' (by nlinarith)

/-- Cochrane (2023), Table 1.1, row "AR(1)", p. 12: "the deficit in time 0 is accompanied by a
decline in the end-of-period value of debt": `Q₀'B₀'/P₀' = Q₀B₀/P₀ + βηΔ < Q₀B₀/P₀`. -/
theorem ar1_value_falls (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β Δ η : ℝ}
    (hβ : 0 < β) (hΔ : Δ < 0) (hη : 0 < η)
    {Bm1 B0 B0' s0 s1 s1' P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hkB0 : Known 𝔼 0 B0)
    (hkB0' : Known 𝔼 0 B0') (hE : 𝔼.E 0 s1' = 𝔼.E 0 s1 + fun _ => η * Δ)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 B0' (s0 + fun _ => Δ) s1' P0' P1' Q0') (ω : Ω) :
    (Q0' * B0' / P0') ω = (Q0 * B0 / P0) ω + β * η * Δ ∧
      (Q0' * B0' / P0') ω < (Q0 * B0 / P0) ω := by
  rw [revenue_invariant 𝔼 hP hkB0' he', revenue_invariant 𝔼 hP hkB0 he, hE]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  have : β * (η * Δ) < 0 := mul_neg_of_pos_of_neg hβ (mul_neg_of_pos_of_neg hη hΔ)
  constructor
  · ring
  · linarith

/-- Cochrane (2023), Table 1.1, column `B₀/P₁`, p. 11: in each strategy the real value of the
maturing debt is `B₀/P₁ = s₁`, so it rises, is unchanged or falls with expected `s₁`:
`E₀(B₀'/P₁') − E₀(B₀/P₁) = E₀s₁' − E₀s₁`. -/
theorem maturing_value_change (𝔼 : ExpectationSystem Ω) {B0 B0' s1 s1' P1 P1' : Ω → ℝ}
    (h1 : Valuation1 B0 P1 s1) (h1' : Valuation1 B0' P1' s1') :
    𝔼.E 0 (B0' / P1') - 𝔼.E 0 (B0 / P1) = 𝔼.E 0 s1' - 𝔼.E 0 s1 := by
  rw [h1, h1']

/-- Cochrane (2023), p. 12, the **"s-shaped" surplus** in two periods: if a deficit
(`Δ < 0`) is accompanied by a rise in the end-of-period value of debt `Q₀B₀/P₀`, then expected
future surpluses must rise, `E₀s₁' > E₀s₁` (`β > 0`). -/
theorem sShape_two_period (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β Δ : ℝ}
    (hβ : 0 < β) {Bm1 B0 B0' s0 s1 s1' P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hkB0 : Known 𝔼 0 B0)
    (hkB0' : Known 𝔼 0 B0') (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 B0' (s0 + fun _ => Δ) s1' P0' P1' Q0') {ω : Ω}
    (hrise : (Q0 * B0 / P0) ω < (Q0' * B0' / P0') ω) : 𝔼.E 0 s1 ω < 𝔼.E 0 s1' ω := by
  rw [revenue_invariant 𝔼 hP hkB0' he', revenue_invariant 𝔼 hP hkB0 he] at hrise
  simp only [Pi.smul_apply, smul_eq_mul] at hrise
  exact lt_of_mul_lt_mul_left hrise hβ.le

/-- Cochrane (2023), p. 11 and p. 12: "fiscal theory can produce a completely steady price level
despite wide variation in deficits and debt": the deficit `Δ` leaves `P₀` unchanged iff it is
matched by expected future surpluses, `Δ + β(E₀s₁' − E₀s₁) = 0` (in a state `ω`; `B₋₁ > 0`,
positive present values). -/
theorem steady_price0_iff (𝔼 : ExpectationSystem Ω) (hP : 𝔼.PullOut) {β Δ : ℝ}
    {Bm1 B0 B0' s0 s1 s1' P0 P1 Q0 P0' P1' Q0' : Ω → ℝ} (hBm1 : ∀ ω, 0 < Bm1 ω)
    (hB0 : ∀ ω, 0 < B0 ω) (hkB0 : Known 𝔼 0 B0) (hB0' : ∀ ω, 0 < B0' ω)
    (hkB0' : Known 𝔼 0 B0') (hs1 : ∀ ω, 0 < s1 ω) (hs1' : ∀ ω, 0 < s1' ω)
    (hpv : ∀ ω, 0 < pv 𝔼 β s0 s1 ω) (hpv' : ∀ ω, 0 < pv 𝔼 β (s0 + fun _ => Δ) s1' ω)
    (he : Equilibrium 𝔼 β Bm1 B0 s0 s1 P0 P1 Q0)
    (he' : Equilibrium 𝔼 β Bm1 B0' (s0 + fun _ => Δ) s1' P0' P1' Q0') (ω : Ω) :
    P0' ω = P0 ω ↔ Δ + β * (𝔼.E 0 s1' ω - 𝔼.E 0 s1 ω) = 0 := by
  rw [price0_formula 𝔼 hP hB0 hkB0 hs1 hpv he ω,
    price0_formula 𝔼 hP hB0' hkB0' hs1' hpv' he' ω]
  have h1 := hpv ω
  have h2 := hpv' ω
  simp only [pv, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
  have hB := (hBm1 ω).ne'
  rw [div_eq_div_iff h2.ne' h1.ne']
  constructor
  · intro h
    have : Bm1 ω * ((s0 ω + β * 𝔼.E 0 s1 ω) - (s0 ω + Δ + β * 𝔼.E 0 s1' ω)) = 0 := by
      linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hB
    · linarith
  · intro h
    have : s0 ω + Δ + β * 𝔼.E 0 s1' ω = s0 ω + β * 𝔼.E 0 s1 ω := by linarith
    rw [this]

end Cochrane.TwoPeriodModel.DebtSales
