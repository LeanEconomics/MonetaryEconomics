/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.GeneralLinks

/-!
# The bond price is positive: `i > −1` from the expectation axioms

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.1, eq. (2.3), p. 22
(`1/(1 + i_t) = β E_t(P_t/P_{t+1})`), and the equilibrium notions of §§2.1–2.4, pp. 21–33.

The link between the equilibrium notions (`GeneralLinks.equilibrium_iff_isEqm`) takes an
adapted rate `i > −1` as a hypothesis, and `FiscalMonetary.Equilibrium` lists `i > −1` among its
conditions. This module decides the question: for `β > 0` both are consequences of the bond-pricing
condition (2.3) and the core `ExpectationSystem` axioms, with no extra property of expectations
(only the pull-out property, already assumed by the link, for adaptedness).

## Main results

* `E_pos_of_pos`: **strict positivity from the axioms alone.** If `X > 0` in every state then
  `E_t X > 0` in every state, for every `ExpectationSystem` on every state space. The proof uses
  only linearity, constants and monotonicity: with `k(ω)` the least `n` such that
  `(n + 1) X(ω) ≥ 1`, one has `1 ≤ (n + 1) X + k/(n + 1)` pointwise for every `n`, so
  `E_t X = 0` would force `E_t k ≥ n + 1` for every `n`.
* `bondPrice_pos`, `isEqm_bondPrice_pos`, `isEqm_rate_gt`: in every equilibrium derived in
  `Valuation` with `β > 0`, `Q_t > 0` and `i_t = 1/Q_t − 1 > −1` in every state.
* `bondPricing_rate_gt`, `bondPricing_rate_adapted`: the bond-pricing condition alone forces
  `i > −1`, and (with pull-out) an adapted rate.
* `equilibrium_iff_reduced`: `FiscalMonetary.Equilibrium` without its rate conditions is the same
  notion (`β > 0`, pull-out).
* `equilibrium_iff_isEqm_pos`: `GeneralLinks.equilibrium_iff_isEqm` without the hypotheses
  `i > −1` and `i` adapted (`β > 0`).
* `isEqm_fisher_log_pos`: `GeneralLinks.isEqm_fisher_log` without the hypothesis `Q > 0`.
* `no_eqm_of_rate_le`: a rate target with `i_t ≤ −1` in some state has no equilibrium in either
  sense.
* `beta_zero_counterexample`: the hypothesis is needed at `β = 0`: under perfect foresight with
  `β = 0` the data `i ≡ −1`, `P ≡ 1`, no debt and no surpluses satisfy every other hypothesis of
  `GeneralLinks.equilibrium_iff_isEqm` and are an equilibrium derived from flow plus
  transversality, but not a `FiscalMonetary.Equilibrium`.
-/

namespace Cochrane.IntertemporalModel.TidyR5BondPrice

open Filter Topology ExpectationTools

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Strict positivity of `E_t` -/

/-- Cochrane (2023), eq. (2.3), p. 22 (`E_t` of a positive payoff is positive), from the core
axioms alone: if `X > 0` in every state, then `E_t X > 0` in every state. No faithfulness,
finiteness or countability of `Ω` is needed. -/
theorem E_pos_of_pos {X : Ω → ℝ} (hX : ∀ ω, 0 < X ω) (t : ℕ) (ω : Ω) : 0 < 𝔼.E t X ω := by
  classical
  have hex : ∀ ω', ∃ n : ℕ, 1 ≤ ((n : ℝ) + 1) * X ω' := fun ω' => by
    obtain ⟨n, hn⟩ := exists_nat_gt (X ω')⁻¹
    refine ⟨n, ?_⟩
    have hx := hX ω'
    have h1 : (X ω')⁻¹ * X ω' = 1 := inv_mul_cancel₀ hx.ne'
    nlinarith
  set K : Ω → ℝ := fun ω' => (Nat.find (hex ω') : ℝ) with hK
  have hbound : ∀ n : ℕ, (fun _ => (1 : ℝ)) ≤ ((n : ℝ) + 1) • X + ((n : ℝ) + 1)⁻¹ • K := by
    intro n ω'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    have hK0 : 0 ≤ K ω' := Nat.cast_nonneg _
    by_cases h : 1 ≤ ((n : ℝ) + 1) * X ω'
    · have : 0 ≤ ((n : ℝ) + 1)⁻¹ * K ω' := mul_nonneg (inv_nonneg.mpr hpos.le) hK0
      linarith
    · have hlt : n < Nat.find (hex ω') := by
        by_contra hle
        push Not at hle
        have hs := Nat.find_spec (hex ω')
        have hmono : ((Nat.find (hex ω') : ℝ) + 1) * X ω' ≤ ((n : ℝ) + 1) * X ω' := by
          refine mul_le_mul_of_nonneg_right ?_ (hX ω').le
          have : (Nat.find (hex ω') : ℝ) ≤ n := by exact_mod_cast hle
          linarith
        exact h (hs.trans hmono)
      have hKn : (n : ℝ) + 1 ≤ K ω' := by
        simp only [hK]
        exact_mod_cast hlt
      have e : ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) = 1 := inv_mul_cancel₀ hpos.ne'
      have h2 : 1 ≤ ((n : ℝ) + 1)⁻¹ * K ω' := by
        calc (1 : ℝ) = ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) := e.symm
          _ ≤ ((n : ℝ) + 1)⁻¹ * K ω' :=
            mul_le_mul_of_nonneg_left hKn (inv_nonneg.mpr hpos.le)
      have : 0 ≤ ((n : ℝ) + 1) * X ω' := mul_nonneg hpos.le (hX ω').le
      linarith
  have hE : ∀ n : ℕ, 1 ≤ ((n : ℝ) + 1) * 𝔼.E t X ω + ((n : ℝ) + 1)⁻¹ * 𝔼.E t K ω := by
    intro n
    have h := 𝔼.mono t (hbound n) ω
    rw [𝔼.const, map_add, map_smul, map_smul] at h
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
  have h0 : 0 ≤ 𝔼.E t X ω := E_nonneg 𝔼 (fun ω' => (hX ω').le) ω
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨n, hn⟩ := exists_nat_gt (𝔼.E t K ω)
    have h1 := hE n
    rw [← h, mul_zero, zero_add] at h1
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    have h2 := mul_le_mul_of_nonneg_left h1 hpos.le
    rw [mul_one, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at h2
    linarith

/-! ### The bond price and the nominal rate -/

/-- Cochrane (2023), eq. (2.3), p. 22: with `β > 0` and a positive price level, the bond price
`β E_t(P_t/P_{t+1})` is positive in every state. -/
theorem bondPrice_pos {β : ℝ} (hβ : 0 < β) {P : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω) (t : ℕ)
    (ω : Ω) : 0 < (β • 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω')) ω :=
  mul_pos hβ (E_pos_of_pos 𝔼 (fun ω' => div_pos (hP t ω') (hP (t + 1) ω')) t ω)

/-- Cochrane (2023), eq. (2.3), p. 22: in every equilibrium derived in `Valuation`
(`Valuation.IsEqm`) with `β > 0`, the bond price is positive in every state. -/
theorem isEqm_bondPrice_pos {β : ℝ} (hβ : 0 < β) {Bm s P Q : ℕ → Ω → ℝ}
    (h : Valuation.IsEqm 𝔼 β Bm s P Q) (t : ℕ) (ω : Ω) : 0 < Q t ω := by
  rw [h.2.2.1 t]
  exact bondPrice_pos 𝔼 hβ h.1 t ω

/-- Cochrane (2023), eq. (2.3), p. 22: in every equilibrium derived in `Valuation` with `β > 0`,
the nominal rate `i_t = 1/Q_t − 1` (`Environment.rate`) exceeds `−1` in every state. -/
theorem isEqm_rate_gt {β : ℝ} (hβ : 0 < β) {Bm s P Q : ℕ → Ω → ℝ}
    (h : Valuation.IsEqm 𝔼 β Bm s P Q) (t : ℕ) (ω : Ω) : -1 < Environment.rate Q t ω := by
  simp only [Environment.rate]
  linarith [inv_pos.mpr (isEqm_bondPrice_pos 𝔼 hβ h t ω)]

/-- Cochrane (2023), eqs. (2.3) and (2.14), pp. 22, 31: the bond-pricing condition
`(1 + i_t)⁻¹ = β E_t(P_t/P_{t+1})` at a date, with `β > 0` and positive prices, forces
`i_t > −1` in every state. -/
theorem rate_gt_of_pricing {β : ℝ} (hβ : 0 < β) {P i : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω)
    {t : ℕ} (hbp : (1 + i t)⁻¹ = β • 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω')) (ω : Ω) :
    -1 < i t ω := by
  have h := bondPrice_pos 𝔼 hβ hP t ω
  rw [← hbp] at h
  have h' : 0 < 1 + i t ω := inv_pos.mp h
  linarith

/-- Cochrane (2023), eqs. (2.3) and (2.14), pp. 22, 31: with the pull-out property, the
bond-pricing condition at a date, `β > 0` and positive prices make the rate `i_t` known at `t`
(the bond price is a forecast, hence known, and nonzero). -/
theorem rate_adapted_of_pricing (hPO : 𝔼.PullOut) {β : ℝ} (hβ : 0 < β) {P i : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) {t : ℕ}
    (hbp : (1 + i t)⁻¹ = β • 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω')) :
    𝔼.E t (i t) = i t := by
  have hQ : 𝔼.E t (1 + i t)⁻¹ = (1 + i t)⁻¹ := by
    rw [hbp, map_smul, 𝔼.E_E_self]
  have hne : ∀ ω, (1 + i t)⁻¹ ω ≠ 0 := fun ω => by
    rw [hbp]
    exact (bondPrice_pos 𝔼 hβ hP t ω).ne'
  have hinv := E_inv_known 𝔼 hPO hQ hne
  rw [inv_inv, map_add] at hinv
  have h1 : 𝔼.E t (1 : Ω → ℝ) = 1 := 𝔼.const t 1
  rw [h1] at hinv
  exact add_left_cancel hinv

/-- Cochrane (2023), eqs. (2.3) and (2.14), pp. 22, 31: `FiscalMonetary.BondPricing` with
`β > 0` and a positive price level forces `i > −1` at every date and in every state. -/
theorem bondPricing_rate_gt {β : ℝ} (hβ : 0 < β) {P i : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω)
    (hbp : FiscalMonetary.BondPricing 𝔼 β P i) (t : ℕ) (ω : Ω) : -1 < i t ω :=
  rate_gt_of_pricing 𝔼 hβ hP (hbp t) ω

/-- Cochrane (2023), eqs. (2.3) and (2.14), pp. 22, 31: with pull-out, `FiscalMonetary.BondPricing`
with `β > 0` and a positive price level makes the rate adapted. -/
theorem bondPricing_rate_adapted (hPO : 𝔼.PullOut) {β : ℝ} (hβ : 0 < β) {P i : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (hbp : FiscalMonetary.BondPricing 𝔼 β P i) : 𝔼.Adapted i :=
  fun t => rate_adapted_of_pricing 𝔼 hPO hβ hP (hbp t)

/-- Cochrane (2023), §§2.1–2.4, pp. 21–33: for `β > 0` and with pull-out, the conditions
"`i` adapted" and "`i > −1`" in `FiscalMonetary.Equilibrium` are redundant: an equilibrium is an
adapted positive price level, adapted debt, the valuation equation and the bond-pricing
condition. -/
theorem equilibrium_iff_reduced (hPO : 𝔼.PullOut) {β : ℝ} (hβ : 0 < β) {Bm1 : Ω → ℝ}
    {s B P i : ℕ → Ω → ℝ} :
    FiscalMonetary.Equilibrium 𝔼 β Bm1 s B P i ↔
      𝔼.Adapted P ∧ (∀ t ω, 0 < P t ω) ∧ 𝔼.Adapted B ∧ FiscalMonetary.Valuation 𝔼 β Bm1 s B P ∧
        FiscalMonetary.BondPricing 𝔼 β P i := by
  constructor
  · rintro ⟨hPa, hP, hBa, -, -, hv, hbp⟩
    exact ⟨hPa, hP, hBa, hv, hbp⟩
  · rintro ⟨hPa, hP, hBa, hv, hbp⟩
    exact ⟨hPa, hP, hBa, bondPricing_rate_adapted 𝔼 hPO hβ hP hbp,
      bondPricing_rate_gt 𝔼 hβ hP hbp, hv, hbp⟩

/-- Cochrane (2023), eq. (2.3), p. 22: in an equilibrium derived in `Valuation` with bond price
`Q = 1/(1 + i)` and `β > 0`, the rate exceeds `−1` in every state. -/
theorem isEqm_inv_rate_gt {β : ℝ} (hβ : 0 < β) {Bm s P i : ℕ → Ω → ℝ}
    (h : Valuation.IsEqm 𝔼 β Bm s P (fun t => (1 + i t)⁻¹)) (t : ℕ) (ω : Ω) : -1 < i t ω :=
  rate_gt_of_pricing 𝔼 hβ h.1 (h.2.2.1 t) ω

/-- Cochrane (2023), eq. (2.3), p. 22: in an equilibrium derived in `Valuation` with bond price
`Q = 1/(1 + i)`, `β > 0` and pull-out, the rate is adapted. -/
theorem isEqm_inv_rate_adapted (hPO : 𝔼.PullOut) {β : ℝ} (hβ : 0 < β) {Bm s P i : ℕ → Ω → ℝ}
    (h : Valuation.IsEqm 𝔼 β Bm s P (fun t => (1 + i t)⁻¹)) : 𝔼.Adapted i :=
  fun t => rate_adapted_of_pricing 𝔼 hPO hβ h.1 (h.2.2.1 t)

/-- Cochrane (2023), §§2.1–2.4, pp. 21–33: `GeneralLinks.equilibrium_iff_isEqm` **without** the
hypotheses that the rate is adapted and exceeds `−1`, for `β > 0`: the valuation-equation
equilibrium of `FiscalMonetary` is exactly the equilibrium of `Valuation` with maturing debt
`GeneralLinks.debtPath B_{−1} B` and bond price `1/(1 + i)`. -/
theorem equilibrium_iff_isEqm_pos (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼) {β : ℝ}
    (hβ : 0 < β) {Bm1 : Ω → ℝ} {s B P i : ℕ → Ω → ℝ} (hs : Valuation.AbsSummable 𝔼 β s)
    (hsad : 𝔼.Adapted s) (hex : ∀ t ω, Summable fun j => β ^ j * |s (t + j) ω|)
    (hBa : 𝔼.Adapted B) :
    FiscalMonetary.Equilibrium 𝔼 β Bm1 s B P i ↔
      Valuation.IsEqm 𝔼 β (GeneralLinks.debtPath Bm1 B) s P (fun t => (1 + i t)⁻¹) := by
  constructor
  · intro h
    exact (GeneralLinks.equilibrium_iff_isEqm 𝔼 hPO hMC hβ.le hs hsad hex hBa h.2.2.2.1
      h.2.2.2.2.1).mp h
  · intro h
    exact (GeneralLinks.equilibrium_iff_isEqm 𝔼 hPO hMC hβ.le hs hsad hex hBa
      (isEqm_inv_rate_adapted 𝔼 hPO hβ h) (isEqm_inv_rate_gt 𝔼 hβ h)).mpr h

/-- Cochrane (2023), eq. (2.16), p. 35: `GeneralLinks.isEqm_fisher_log` without the hypothesis
that the bond price is positive: in every equilibrium derived in `Valuation` with `β > 0`, the
exact Fisher equation holds in logs. -/
theorem isEqm_fisher_log_pos {β : ℝ} (hβ : 0 < β) {Bm s P Q : ℕ → Ω → ℝ}
    (h : Valuation.IsEqm 𝔼 β Bm s P Q) (t : ℕ) (ω : Ω) :
    Real.log (1 + Environment.rate Q t ω) = -Real.log β -
      Real.log (𝔼.E t (fun ω' => Real.exp (-Real.log (P (t + 1) ω' / P t ω'))) ω) :=
  GeneralLinks.isEqm_fisher_log 𝔼 hβ h (isEqm_bondPrice_pos 𝔼 hβ h) t ω

/-- Cochrane (2023), pp. 31–33 (interest-rate targets): a target with `i_t ≤ −1` in some state
has no equilibrium in either sense, for `β > 0`: no `FiscalMonetary.Equilibrium` and no
`Valuation.IsEqm` with bond price `1/(1 + i)` (whatever the debt). -/
theorem no_eqm_of_rate_le {β : ℝ} (hβ : 0 < β) {s i : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (hle : i t ω ≤ -1) :
    (∀ (Bm1 : Ω → ℝ) (B P : ℕ → Ω → ℝ), ¬ FiscalMonetary.Equilibrium 𝔼 β Bm1 s B P i) ∧
      ∀ Bm P : ℕ → Ω → ℝ, ¬ Valuation.IsEqm 𝔼 β Bm s P (fun t => (1 + i t)⁻¹) := by
  refine ⟨fun Bm1 B P h => ?_, fun Bm P h => ?_⟩
  · linarith [h.2.2.2.2.1 t ω]
  · linarith [isEqm_inv_rate_gt 𝔼 hβ h t ω]

/-! ### The hypothesis is needed at `β = 0` -/

/-- Cochrane (2023), §2.1, p. 21: the data of the `β = 0` counterexample — the rate `i ≡ −1`. -/
def rateNegOne : ℕ → Unit → ℝ := fun _ _ => -1

/-- Cochrane (2023), §§2.1–2.4, pp. 21–33: **the hypothesis `i > −1` cannot be dropped at
`β = 0`.** Under perfect foresight with `β = 0`, no initial debt, no debt sold, no surpluses,
`P ≡ 1` and `i ≡ −1`, every other hypothesis of `GeneralLinks.equilibrium_iff_isEqm` holds
(pull-out, monotone convergence, `β ≥ 0`, absolute summability in expectation and ex post,
adapted surpluses, debt and rate), the economy is an equilibrium derived from flow plus
transversality (`Valuation.IsEqm`, bond price `1/(1 + i) = 0`), but it is not a
`FiscalMonetary.Equilibrium`. -/
theorem beta_zero_counterexample :
    perfectForesight.PullOut ∧ MonotoneConvergence perfectForesight ∧
      Valuation.AbsSummable perfectForesight 0 (fun _ _ => 0) ∧
      perfectForesight.Adapted (fun _ _ => 0) ∧
      (∀ t ω, Summable fun j => (0 : ℝ) ^ j * |(fun (_ : ℕ) (_ : Unit) => (0 : ℝ)) (t + j) ω|) ∧
      perfectForesight.Adapted rateNegOne ∧
      Valuation.IsEqm perfectForesight 0 (GeneralLinks.debtPath (fun _ => 0) (fun _ _ => 0))
        (fun _ _ => 0) (fun _ _ => 1) (fun t => (1 + rateNegOne t)⁻¹) ∧
      ¬ FiscalMonetary.Equilibrium perfectForesight 0 (fun _ => 0) (fun _ _ => 0)
        (fun _ _ => 0) (fun _ _ => 1) rateNegOne := by
  refine ⟨perfectForesight_pullOut, perfectForesight_monotoneConvergence,
    fun t ω => by
      change Summable fun j : ℕ => (0 : ℝ) ^ j * |(0 : ℝ)|
      simp, fun _ => rfl, fun t ω => by simp, fun _ => rfl,
    ⟨fun _ _ => one_pos, fun _ => rfl, fun t => ?_, fun t ω => ?_, fun t ω => ?_⟩, ?_⟩
  · funext ω
    simp [rateNegOne]
  · cases t <;> simp [GeneralLinks.debtPath]
  · have e : (fun N : ℕ => (0 : ℝ) ^ N * perfectForesight.E t
        ((fun t ω => GeneralLinks.debtPath (fun _ => (0 : ℝ)) (fun _ _ => 0) t ω /
          (fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) t ω) (t + N)) ω) = fun _ => 0 := by
      funext N
      cases N with
      | zero =>
        change (0 : ℝ) ^ 0 * (GeneralLinks.debtPath (fun _ => (0 : ℝ)) (fun _ _ => 0) (t + 0) ω
          / 1) = 0
        cases t <;> simp [GeneralLinks.debtPath]
      | succ N => simp
    rw [e]
    exact tendsto_const_nhds
  · intro h
    have := h.2.2.2.2.1 0 ()
    simp [rateNegOne] at this

end Cochrane.IntertemporalModel.TidyR5BondPrice
