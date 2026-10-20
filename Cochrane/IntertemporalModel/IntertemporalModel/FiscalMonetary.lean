/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.ExpectationTools
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Fiscal and monetary policy in the intertemporal model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.4 (pp. 29–34),
§2.7 (pp. 42–44), §2.8 (pp. 44–47) and §2.10 (pp. 49–51).

Conventions. `B t` is the nominal one-period debt sold at the end of date `t` (the book's `B_t`,
maturing at `t + 1`); `Bm1` is the initial debt `B_{−1}`. Present values are genuine `tsum`s:
`epv β s t = ∑_{j≥0} βʲ s_{t+j}` state by state, `pv = E_t epv` (the book's
`E_t ∑ βʲ s_{t+j}`) and `pvEx = E_t ∑_{j≥1} βʲ s_{t+j}`; `pv` equals the chapter's
`Valuation.pv` (`∑ βʲ E_t s_{t+j}`) under the hypotheses of `GeneralLinks.fm_pv_eq_pv`.
Innovations are `ExpectationTools.innov t x = E_{t+1} x − E_t x` (the book's `ΔE_{t+1}`). An
`Equilibrium` is an adapted positive price level, adapted debt and nominal rate `i > −1`
satisfying the valuation equation (2.7)/(2.12) at every date and the bond-pricing condition
(2.3)/(2.14); the valuation equation is stated here directly.
`GeneralLinks.equilibrium_iff_isEqm` proves that these are exactly the equilibria
`Valuation.IsEqm` derived from the flow condition (2.4) and the transversality condition (2.6).
Everything holds for an arbitrary `ExpectationSystem` with the pull-out property, so
under perfect foresight and under genuine uncertainty (the coin-flip economy at the end).

## Main results

* (2.13) `unexpected_inflation`, `unexpected_inflation_eq`, `no_surprise_iff`,
  `disinflation_iff`; expected inflation `expected_inflation`; (2.14)–(2.15)
  `expected_valuation`, `debt_eq`; (2.26) `eq_2_26`, `eq_2_26_zero`, `flow_nominal`; (2.27)
  `eq_2_27`; `inflation_decomposition` (target sets expected, fiscal news unexpected inflation).
* Debt with surpluses fixed: `revenue_invariant` (unit-elastic demand), `shareSplit`,
  `future_sales_irrelevant`.
* Interest-rate targets: `peg_equilibrium`, `peg_unique`, `peg_existsUnique` (any adapted
  target, no Taylor principle), `peg_expected_inflation`, `expected_inflation_indep_surplus`,
  `debt_ratio_of_rate`, `debt_growth_of_rate` and `rate_change_eq_debt_growth_iff`,
  `printed_one_percent_fails` (survey E7); real-rate pegs: `real_rate_forced`,
  `no_eqm_real_rate_peg`, `real_rate_peg_unbounded`; the contrast with the classic doctrine:
  `scaled_all_but_initial`, `scaled_not_initial`; perfect foresight: `pf_pricing_iff`,
  `pf_price_formula`, `pf_family`.
* §2.7: `equityIssue`, `equityIssue_finances_deficit`, `sShape_seq`, `sShape`,
  `reform_with_deficits`; AR(1) surpluses: `ar1_news`, `ar1_pv_news`,
  `ar1_unexpected_inflation` and `ar1_printed_fails` (survey E5), `ar1_value_news`,
  `ar1_value_falls`, `ar1_news_exceeds_deficit`.
* §2.8: `consolidation_irrelevant`. §2.10: `stimulus_no_jump`, `pf_stimulus_neutral`,
  `stimulus_price_iff`, `stimulus_unexpected_inflation`, `news_pv_add_known`, and the
  coin-flip counterexample `CoinExample.stimulus_not_neutral` ("no effect at all" holds under
  perfect foresight but not under uncertainty).
-/

namespace Cochrane.IntertemporalModel.FiscalMonetary

open Filter Topology ExpectationTools

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Present values of surpluses -/

/-- Cochrane (2023), eq. (2.7), p. 22: the ex-post discounted sum of surpluses
`∑_{j ≥ 0} βʲ s_{t+j}` (a genuine `tsum`, state by state). -/
noncomputable def epv (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, β ^ j * s (t + j) ω

/-- Cochrane (2023), eq. (2.7), p. 22: the present value of surpluses
`PV_t = E_t ∑_{j ≥ 0} βʲ s_{t+j}`. -/
noncomputable def pv (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := 𝔼.E t (epv β s t)

/-- Cochrane (2023), eq. (2.15), p. 31: the ex-dividend present value
`E_t ∑_{j ≥ 1} βʲ s_{t+j}`, the real value of the debt sold at the end of date `t`. -/
noncomputable def pvEx (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  𝔼.E t (fun ω => ∑' j, β ^ (j + 1) * s (t + (j + 1)) ω)

/-- Cochrane (2023), eq. (2.7), p. 22: the ex-post discounted sum converges in every state at
every date. -/
def SurplusSummable (β : ℝ) (s : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Summable (fun j => β ^ j * s (t + j) ω)

omit 𝔼 in
/-- Cochrane (2023), eq. (2.7), p. 22: summability of `∑ βʲ s_j` at date `0` gives it at every
date (`β ≠ 0`). -/
theorem surplusSummable_of_zero {β : ℝ} (hβ : β ≠ 0) {s : ℕ → Ω → ℝ}
    (h : ∀ ω, Summable (fun j => β ^ j * s j ω)) : SurplusSummable β s := by
  intro t ω
  have h1 : Summable (fun j => β ^ (j + t) * s (j + t) ω) := (summable_nat_add_iff t).mpr (h ω)
  refine (h1.mul_left ((β ^ t)⁻¹)).congr fun j => ?_
  rw [pow_add, add_comm j t]
  field_simp

omit 𝔼 in
/-- Cochrane (2023), eq. (2.7), p. 22: bounded surpluses and `0 ≤ β < 1` give summability. -/
theorem surplusSummable_of_bounded {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) : SurplusSummable β s := by
  intro t ω
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right M)
    (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
  exact mul_le_mul_of_nonneg_left (hs (t + j) ω) (pow_nonneg hβ0 j)

omit 𝔼 in
/-- Cochrane (2023), eq. (2.15), p. 31: the ex-dividend sum is `β` times next date's sum,
`∑_{j ≥ 1} βʲ s_{t+j} = β ∑_{j ≥ 0} βʲ s_{t+1+j}` (no summability needed). -/
theorem exsum_eq (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) :
    (fun ω => ∑' j, β ^ (j + 1) * s (t + (j + 1)) ω) = β • epv β s (t + 1) := by
  funext ω
  simp only [epv, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [show t + (j + 1) = t + 1 + j by omega, pow_succ]
  ring

omit 𝔼 in
/-- Cochrane (2023), eq. (2.26), p. 42 (ex post): `∑_{j≥0} βʲ s_{t+j} = s_t + β ∑_{j≥0} βʲ
s_{t+1+j}`. -/
theorem epv_succ {β : ℝ} {s : ℕ → Ω → ℝ} (hs : SurplusSummable β s) (t : ℕ) :
    epv β s t = s t + β • epv β s (t + 1) := by
  rw [← exsum_eq]
  funext ω
  simp only [epv, Pi.add_apply]
  rw [(hs t ω).tsum_eq_zero_add]
  simp

/-- Cochrane (2023), eq. (2.15), p. 31: `E_t ∑_{j≥1} βʲ s_{t+j} = β E_t PV_{t+1}`. -/
theorem pvEx_eq (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) :
    pvEx 𝔼 β s t = β • 𝔼.E t (pv 𝔼 β s (t + 1)) := by
  rw [pvEx, exsum_eq, map_smul, pv, 𝔼.tower (Nat.le_succ t)]

/-- Cochrane (2023), eq. (2.7), p. 22: the present value is known at date `t`. -/
theorem pv_adapted (β : ℝ) (s : ℕ → Ω → ℝ) : 𝔼.Adapted (pv 𝔼 β s) := fun t =>
  𝔼.E_E_self t _

/-- Cochrane (2023), eq. (2.15), p. 31: the ex-dividend present value is known at date `t`. -/
theorem pvEx_adapted (β : ℝ) (s : ℕ → Ω → ℝ) : 𝔼.Adapted (pvEx 𝔼 β s) := fun t =>
  𝔼.E_E_self t _

/-- Cochrane (2023), eq. (2.26), p. 42: `E_t ∑_{j≥0} βʲ s_{t+j} = s_t + E_t ∑_{j≥1} βʲ s_{t+j}`
for adapted surpluses. -/
theorem pv_eq_add_pvEx {β : ℝ} {s : ℕ → Ω → ℝ} (hs : SurplusSummable β s)
    (hsa : 𝔼.Adapted s) (t : ℕ) : pv 𝔼 β s t = s t + pvEx 𝔼 β s t := by
  rw [pv, epv_succ hs, map_add, hsa t, pvEx, exsum_eq]

/-- Cochrane (2023), eq. (2.15), p. 31: a uniform positive lower bound `PV ≥ c > 0` gives a
positive ex-dividend present value `≥ β c`. -/
theorem pvEx_ge {β c : ℝ} (hβ : 0 ≤ β) {s : ℕ → Ω → ℝ}
    (hc : ∀ t ω, c ≤ pv 𝔼 β s t ω) (t : ℕ) (ω : Ω) : β * c ≤ pvEx 𝔼 β s t ω := by
  rw [pvEx_eq]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (const_le_E 𝔼 (hc (t + 1)) t ω) hβ

/-! ### Present values and innovations `ΔE_{t+1} = E_{t+1} − E_t` -/

/-- Cochrane (2023), eq. (2.12), p. 30: `E_t PV_{t+1} = E_t ∑_{j≥0} βʲ s_{t+1+j}`. -/
theorem E_pv_succ (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) :
    𝔼.E t (pv 𝔼 β s (t + 1)) = 𝔼.E t (epv β s (t + 1)) := by
  rw [pv, 𝔼.tower (Nat.le_succ t)]

/-- Cochrane (2023), eq. (2.13), p. 30: the innovation in the present value
`ΔE_{t+1} PV_{t+1}` is the innovation in the ex-post sum `ΔE_{t+1} ∑ βʲ s_{t+1+j}`. -/
theorem news_pv_succ (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) :
    innov 𝔼 t (pv 𝔼 β s (t + 1)) = innov 𝔼 t (epv β s (t + 1)) := by
  rw [pv, innov_E_succ]

/-! ### Equilibrium -/

/-- Cochrane (2023), eqs. (2.7) and (2.12), pp. 22, 30: the government debt valuation equation
at every date, `B_{−1}/P_0 = E_0 ∑ βʲ s_j` and `B_t/P_{t+1} = E_{t+1} ∑ βʲ s_{t+1+j}`. Here
`B t` is the nominal debt sold at the end of date `t` (it matures at `t + 1`) and `Bm1` is the
initial debt `B_{−1}`. -/
def Valuation (β : ℝ) (Bm1 : Ω → ℝ) (s B P : ℕ → Ω → ℝ) : Prop :=
  Bm1 / P 0 = pv 𝔼 β s 0 ∧ ∀ t, B t / P (t + 1) = pv 𝔼 β s (t + 1)

/-- Cochrane (2023), eqs. (2.3) and (2.14), pp. 22, 31: the bond price
`Q_t = 1/(1 + i_t) = β E_t(P_t/P_{t+1})` at every date. -/
def BondPricing (β : ℝ) (P i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (1 + i t)⁻¹ = β • 𝔼.E t (P t / P (t + 1))

/-- Cochrane (2023), §2.1–§2.4, pp. 21–33: an equilibrium of the frictionless intertemporal
model given surpluses `s` and initial debt `B_{−1}`: an adapted positive price level `P`, adapted
debt `B`, an adapted nominal rate `i > −1`, the valuation equation at every date (which is the
flow condition (2.5) plus the transversality condition (2.6)) and the bond-pricing condition
(2.3). Whether `B` (a debt-quantity policy) or `i` (an interest-rate target) is the policy
instrument is a matter of which of them is given. -/
def Equilibrium (β : ℝ) (Bm1 : Ω → ℝ) (s B P i : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted P ∧ (∀ t ω, 0 < P t ω) ∧ 𝔼.Adapted B ∧ 𝔼.Adapted i ∧ (∀ t ω, -1 < i t ω) ∧
    Valuation 𝔼 β Bm1 s B P ∧ BondPricing 𝔼 β P i

variable {𝔼}
variable {β : ℝ} {Bm1 : Ω → ℝ} {s B P i : ℕ → Ω → ℝ}

/-- Cochrane (2023), eq. (2.7), p. 22, "the price level must adjust so that (2.7) holds": in
equilibrium `P_0 = B_{−1}/PV_0` (when `PV_0 ≠ 0`). -/
theorem price_zero (h : Equilibrium 𝔼 β Bm1 s B P i) (ω : Ω) (hpv : pv 𝔼 β s 0 ω ≠ 0) :
    P 0 ω = Bm1 ω / pv 𝔼 β s 0 ω := by
  have h1 := congrFun h.2.2.2.2.2.1.1 ω
  simp only [Pi.div_apply] at h1
  rw [← h1] at hpv ⊢
  rw [div_div_cancel₀ (by intro h0; exact hpv (by rw [h0, zero_div]))]

/-- Cochrane (2023), eq. (2.12), p. 30: in equilibrium `P_{t+1} = B_t/PV_{t+1}` (when
`PV_{t+1} ≠ 0`): the price level is determined by the debt outstanding and the present value
of surpluses. -/
theorem price_succ (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) (ω : Ω)
    (hpv : pv 𝔼 β s (t + 1) ω ≠ 0) : P (t + 1) ω = B t ω / pv 𝔼 β s (t + 1) ω := by
  have h1 := congrFun (h.2.2.2.2.2.1.2 t) ω
  simp only [Pi.div_apply] at h1
  rw [← h1] at hpv ⊢
  rw [div_div_cancel₀ (by intro h0; exact hpv (by rw [h0, zero_div]))]

/-- Cochrane (2023), §2.4.1, p. 30: the real value of the debt `B_t/P_t` is known at `t`
(pull-out property). -/
theorem realDebt_known (hPO : 𝔼.PullOut) (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) :
    𝔼.E t (B t / P t) = B t / P t :=
  E_div_known 𝔼 hPO (h.2.2.1 t) (h.1 t) (fun ω => (h.2.1 t ω).ne')

/-- Cochrane (2023), eq. (2.13), p. 30, **unexpected inflation**:
`(B_t/P_t) ΔE_{t+1}(P_t/P_{t+1}) = ΔE_{t+1} ∑_{j≥0} βʲ s_{t+1+j}`. -/
theorem unexpected_inflation (hPO : 𝔼.PullOut) (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) :
    (B t / P t) * innov 𝔼 t (P t / P (t + 1)) = innov 𝔼 t (epv β s (t + 1)) := by
  have hsplit : B t / P (t + 1) = (B t / P t) * (P t / P (t + 1)) := by
    funext ω
    have := (h.2.1 t ω).ne'
    simp only [Pi.div_apply, Pi.mul_apply]
    field_simp
  rw [← innov_mul_known 𝔼 hPO (realDebt_known hPO h t), ← hsplit, h.2.2.2.2.2.1.2 t,
    news_pv_succ]

/-- Cochrane (2023), eq. (2.13), p. 30: unexpected inflation is the present-value news divided
by the real value of the debt. -/
theorem unexpected_inflation_eq (hPO : 𝔼.PullOut) (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ)
    (ω : Ω) (hB : B t ω ≠ 0) :
    innov 𝔼 t (P t / P (t + 1)) ω = innov 𝔼 t (epv β s (t + 1)) ω / (B t ω / P t ω) := by
  have h1 := congrFun (unexpected_inflation hPO h t) ω
  simp only [Pi.mul_apply, Pi.div_apply] at h1
  have hP := (h.2.1 t ω).ne'
  rw [← h1]
  field_simp

/-- Cochrane (2023), p. 30, bullet: "unexpected inflation is determined entirely by changing
expectations of the present value of fiscal surpluses": with debt outstanding, unexpected
inflation is zero exactly when the present-value news is zero. -/
theorem no_surprise_iff (hPO : 𝔼.PullOut) (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) (ω : Ω)
    (hB : B t ω ≠ 0) :
    innov 𝔼 t (P t / P (t + 1)) ω = 0 ↔ innov 𝔼 t (epv β s (t + 1)) ω = 0 := by
  have h1 := congrFun (unexpected_inflation hPO h t) ω
  simp only [Pi.mul_apply, Pi.div_apply] at h1
  have hV : B t ω / P t ω ≠ 0 := div_ne_zero hB (h.2.1 t ω).ne'
  rw [← h1]
  constructor
  · intro h0; rw [h0, mul_zero]
  · intro h0; exact (mul_eq_zero.mp h0).resolve_left hV

/-- Cochrane (2023), p. 42 and §2.8, p. 44: with positive debt, a positive present-value news
produces a disinflation `ΔE_{t+1}(P_t/P_{t+1}) > 0`, and conversely. -/
theorem disinflation_iff (hPO : 𝔼.PullOut) (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) (ω : Ω)
    (hB : 0 < B t ω) :
    0 < innov 𝔼 t (P t / P (t + 1)) ω ↔ 0 < innov 𝔼 t (epv β s (t + 1)) ω := by
  have h1 := congrFun (unexpected_inflation hPO h t) ω
  simp only [Pi.mul_apply, Pi.div_apply] at h1
  have hV : 0 < B t ω / P t ω := div_pos hB (h.2.1 t ω)
  rw [← h1]
  exact (mul_pos_iff_of_pos_left hV).symm

/-- Cochrane (2023), p. 30, "you can't expect future unexpected shocks": in equilibrium the
date-`t` forecast of every later unexpected inflation is zero. -/
theorem E_unexpected_inflation_zero (t k : ℕ) :
    𝔼.E t (innov 𝔼 (t + k) (P (t + k) / P (t + k + 1))) = 0 :=
  E_innov_zero_of_le 𝔼 (Nat.le_add_right t k) _

/-- Cochrane (2023), §2.4.2, p. 30 (display after (2.13)): **expected inflation**,
`(B_t/P_t) E_t(P_t/P_{t+1}) = E_t ∑_{j≥0} βʲ s_{t+1+j}`. -/
theorem expected_inflation (hPO : 𝔼.PullOut) (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) :
    (B t / P t) * 𝔼.E t (P t / P (t + 1)) = 𝔼.E t (epv β s (t + 1)) := by
  have hsplit : B t / P (t + 1) = (B t / P t) * (P t / P (t + 1)) := by
    funext ω
    have := (h.2.1 t ω).ne'
    simp only [Pi.div_apply, Pi.mul_apply]
    field_simp
  rw [← hPO t _ _ (realDebt_known hPO h t), ← hsplit, h.2.2.2.2.2.1.2 t, E_pv_succ]

/-- Cochrane (2023), eqs. (2.14)–(2.15), p. 31: the real revenue from bond sales,
`(B_t/P_t)/(1 + i_t) = (B_t/P_t) β E_t(P_t/P_{t+1}) = E_t ∑_{j≥1} βʲ s_{t+j}`. -/
theorem expected_valuation (hPO : 𝔼.PullOut) (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) :
    (B t / P t) * (1 + i t)⁻¹ = β • ((B t / P t) * 𝔼.E t (P t / P (t + 1))) ∧
      (B t / P t) * (1 + i t)⁻¹ = pvEx 𝔼 β s t := by
  have h1 : (B t / P t) * (1 + i t)⁻¹ = β • ((B t / P t) * 𝔼.E t (P t / P (t + 1))) := by
    rw [h.2.2.2.2.2.2 t, mul_smul_comm]
  refine ⟨h1, ?_⟩
  rw [h1, expected_inflation hPO h t, pvEx_eq, E_pv_succ]

/-- Cochrane (2023), eq. (2.15), p. 31, and p. 43: in equilibrium the debt sold is
`B_t = (1 + i_t) P_t E_t ∑_{j≥1} βʲ s_{t+j}`. -/
theorem debt_eq (hPO : 𝔼.PullOut) (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) (ω : Ω) :
    B t ω = (1 + i t ω) * P t ω * pvEx 𝔼 β s t ω := by
  have h1 := congrFun (expected_valuation hPO h t).2 ω
  simp only [Pi.mul_apply, Pi.div_apply, Pi.inv_apply, Pi.add_apply, Pi.one_apply] at h1
  have hP := (h.2.1 t ω).ne'
  have hi : 1 + i t ω ≠ 0 := by linarith [h.2.2.2.2.1 t ω]
  rw [← h1]
  field_simp

/-- Cochrane (2023), eqs. (2.4) and (2.26), pp. 22, 42: the flow condition in real terms,
`B_t/P_{t+1} = s_{t+1} + (B_{t+1}/P_{t+1})/(1 + i_{t+1}) = s_{t+1} + E_{t+1} ∑_{j≥1} βʲ
s_{t+1+j}`. -/
theorem eq_2_26 (hPO : 𝔼.PullOut) (hs : SurplusSummable β s) (hsa : 𝔼.Adapted s)
    (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) :
    B t / P (t + 1) = s (t + 1) + (B (t + 1) / P (t + 1)) * (1 + i (t + 1))⁻¹ ∧
      B t / P (t + 1) = s (t + 1) + pvEx 𝔼 β s (t + 1) := by
  rw [(expected_valuation hPO h (t + 1)).2, h.2.2.2.2.2.1.2 t, pv_eq_add_pvEx 𝔼 hs hsa]
  exact ⟨rfl, rfl⟩

/-- Cochrane (2023), eqs. (2.4) and (2.26), pp. 22, 42, at the initial date:
`B_{−1}/P_0 = s_0 + (B_0/P_0)/(1 + i_0) = s_0 + E_0 ∑_{j≥1} βʲ s_j`. -/
theorem eq_2_26_zero (hPO : 𝔼.PullOut) (hs : SurplusSummable β s) (hsa : 𝔼.Adapted s)
    (h : Equilibrium 𝔼 β Bm1 s B P i) :
    Bm1 / P 0 = s 0 + (B 0 / P 0) * (1 + i 0)⁻¹ ∧ Bm1 / P 0 = s 0 + pvEx 𝔼 β s 0 := by
  rw [(expected_valuation hPO h 0).2, h.2.2.2.2.2.1.1, pv_eq_add_pvEx 𝔼 hs hsa]
  exact ⟨rfl, rfl⟩

/-- Cochrane (2023), eq. (2.4), p. 22: the nominal flow condition
`B_t = P_{t+1} s_{t+1} + Q_{t+1} B_{t+1}` with `Q = 1/(1 + i)`. -/
theorem flow_nominal (hPO : 𝔼.PullOut) (hs : SurplusSummable β s) (hsa : 𝔼.Adapted s)
    (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) (ω : Ω) :
    B t ω = P (t + 1) ω * s (t + 1) ω + (1 + i (t + 1) ω)⁻¹ * B (t + 1) ω := by
  have h1 := congrFun (eq_2_26 hPO hs hsa h t).1 ω
  simp only [Pi.mul_apply, Pi.div_apply, Pi.inv_apply, Pi.add_apply, Pi.one_apply] at h1
  have hP := (h.2.1 (t + 1) ω).ne'
  field_simp at h1
  linear_combination h1

/-- Cochrane (2023), eq. (2.27), p. 42: innovations in the flow condition,
`(B_t/P_t) ΔE_{t+1}(P_t/P_{t+1}) = ΔE_{t+1}[s_{t+1} + (B_{t+1}/P_{t+1})/(1 + i_{t+1})]
= ΔE_{t+1}[s_{t+1} + E_{t+1} ∑_{j≥1} βʲ s_{t+1+j}]`. -/
theorem eq_2_27 (hPO : 𝔼.PullOut) (hs : SurplusSummable β s) (hsa : 𝔼.Adapted s)
    (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) :
    (B t / P t) * innov 𝔼 t (P t / P (t + 1)) =
        innov 𝔼 t (s (t + 1) + (B (t + 1) / P (t + 1)) * (1 + i (t + 1))⁻¹) ∧
      (B t / P t) * innov 𝔼 t (P t / P (t + 1)) =
        innov 𝔼 t (s (t + 1) + pvEx 𝔼 β s (t + 1)) := by
  rw [← (eq_2_26 hPO hs hsa h t).1, ← (eq_2_26 hPO hs hsa h t).2, h.2.2.2.2.2.1.2 t,
    news_pv_succ, unexpected_inflation hPO h t]
  exact ⟨rfl, rfl⟩

/-! ### Debt sales with surpluses fixed: share split, revenue, future sales (§2.4.2) -/

/-- Cochrane (2023), p. 31, unit-elastic demand: two equilibria with the same surpluses raise
the same real revenue `(B_t/P_t)/(1 + i_t)` from bond sales, whatever debt they sell. -/
theorem revenue_invariant (hPO : 𝔼.PullOut) {Bm1' : Ω → ℝ} {B' P' i' : ℕ → Ω → ℝ}
    (h : Equilibrium 𝔼 β Bm1 s B P i) (h' : Equilibrium 𝔼 β Bm1' s B' P' i') (t : ℕ) :
    (B' t / P' t) * (1 + i' t)⁻¹ = (B t / P t) * (1 + i t)⁻¹ := by
  rw [(expected_valuation hPO h' t).2, (expected_valuation hPO h t).2]

/-- Cochrane (2023), p. 31, "changing expectations of future bond sales `ΔE_{t+1}B_{t+j}`,
`j ≥ 1`, make no difference": two equilibria with the same surpluses and the same debt up to
date `t` have the same price level up to date `t + 1`, whatever debt they sell later. -/
theorem future_sales_irrelevant {B' P' i' : ℕ → Ω → ℝ} (h : Equilibrium 𝔼 β Bm1 s B P i)
    (h' : Equilibrium 𝔼 β Bm1 s B' P' i') (hpv : ∀ t ω, pv 𝔼 β s t ω ≠ 0) {t : ℕ}
    (hB : ∀ k ≤ t, B' k = B k) : ∀ k ≤ t + 1, P' k = P k := by
  intro k hk
  funext ω
  cases k with
  | zero => rw [price_zero h' ω (hpv 0 ω), price_zero h ω (hpv 0 ω)]
  | succ k =>
    rw [price_succ h' k ω (hpv _ ω), price_succ h k ω (hpv _ ω), hB k (by omega)]

/-- Cochrane (2023), p. 31, bullet and "selling bonds without changing surpluses is again like a
share split": scaling the debt sold at `t` by `λ > 0` with surpluses unchanged leaves the price
level up to `t` unchanged, scales `P_{t+1}` and the gross nominal rate `1 + i_t` by `λ`, divides
expected gross deflation `E_t(P_t/P_{t+1})` by `λ` and leaves the real revenue unchanged. -/
theorem shareSplit (hPO : 𝔼.PullOut) {B' P' i' : ℕ → Ω → ℝ}
    (h : Equilibrium 𝔼 β Bm1 s B P i) (h' : Equilibrium 𝔼 β Bm1 s B' P' i')
    (hpv : ∀ t ω, pv 𝔼 β s t ω ≠ 0) {t : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (hBk : ∀ k < t, B' k = B k) (hBt : B' t = lam • B t) (hB0 : ∀ ω, B t ω ≠ 0) :
    (∀ k ≤ t, P' k = P k) ∧ P' (t + 1) = lam • P (t + 1) ∧ 1 + i' t = lam • (1 + i t) ∧
      𝔼.E t (P' t / P' (t + 1)) = lam⁻¹ • 𝔼.E t (P t / P (t + 1)) ∧
      (B' t / P' t) * (1 + i' t)⁻¹ = (B t / P t) * (1 + i t)⁻¹ := by
  have hPk : ∀ k ≤ t, P' k = P k := by
    intro k hk
    funext ω
    cases k with
    | zero => rw [price_zero h' ω (hpv 0 ω), price_zero h ω (hpv 0 ω)]
    | succ k =>
      rw [price_succ h' k ω (hpv _ ω), price_succ h k ω (hpv _ ω), hBk k (by omega)]
  have hPt := hPk t le_rfl
  have hP1 : P' (t + 1) = lam • P (t + 1) := by
    funext ω
    rw [price_succ h' t ω (hpv _ ω), Pi.smul_apply, price_succ h t ω (hpv _ ω), hBt,
      Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_div_assoc]
  refine ⟨hPk, hP1, ?_, ?_, revenue_invariant hPO h h' t⟩
  · funext ω
    have e1 := debt_eq hPO h' t ω
    have e2 := debt_eq hPO h t ω
    rw [hBt, hPt, Pi.smul_apply, smul_eq_mul] at e1
    have hne : P t ω * pvEx 𝔼 β s t ω ≠ 0 := by
      intro h0
      apply hB0 ω
      rw [e2, mul_assoc, h0, mul_zero]
    simp only [Pi.add_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul]
    rw [e2] at e1
    apply mul_right_cancel₀ hne
    linear_combination -e1
  · have hfun : P' t / P' (t + 1) = lam⁻¹ • (P t / P (t + 1)) := by
      funext ω
      rw [hP1, hPt]
      simp only [Pi.div_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
    rw [hfun, map_smul]

/-! ### Interest-rate targets (§2.4.3–§2.4.4) -/

/-- Cochrane (2023), §2.4.3, p. 31: the price level of the interest-rate-target equilibrium,
`P_0 = B_{−1}/PV_0`, `P_{t+1} = (1 + i_t) P_t E_t ∑_{j≥1} βʲ s_{t+j} / PV_{t+1}`. -/
noncomputable def pegP (𝔼 : ExpectationSystem Ω) (β : ℝ) (Bm1 : Ω → ℝ) (s i : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ
  | 0 => Bm1 / pv 𝔼 β s 0
  | t + 1 => (1 + i t) * pegP 𝔼 β Bm1 s i t * pvEx 𝔼 β s t / pv 𝔼 β s (t + 1)

/-- Cochrane (2023), eq. (2.15), p. 31: the debt the government sells at the interest-rate
target (the flat supply curve), `B_t = (1 + i_t) P_t E_t ∑_{j≥1} βʲ s_{t+j}`. -/
noncomputable def pegB (𝔼 : ExpectationSystem Ω) (β : ℝ) (Bm1 : Ω → ℝ) (s i : ℕ → Ω → ℝ)
    (t : ℕ) : Ω → ℝ :=
  (1 + i t) * pegP 𝔼 β Bm1 s i t * pvEx 𝔼 β s t

/-- Cochrane (2023), §2.4.3, p. 31: `P_{t+1} = B_t / PV_{t+1}` along the target equilibrium. -/
theorem pegP_succ (𝔼 : ExpectationSystem Ω) (β : ℝ) (Bm1 : Ω → ℝ) (s i : ℕ → Ω → ℝ) (t : ℕ) :
    pegP 𝔼 β Bm1 s i (t + 1) = pegB 𝔼 β Bm1 s i t / pv 𝔼 β s (t + 1) := rfl

/-- Cochrane (2023), §2.4.3, p. 31: the target-equilibrium price level is positive. -/
theorem pegP_pos {Bm1 : Ω → ℝ} (hB : ∀ ω, 0 < Bm1 ω) (hi : ∀ t ω, -1 < i t ω)
    (hpv : ∀ t ω, 0 < pv 𝔼 β s t ω) (hpvEx : ∀ t ω, 0 < pvEx 𝔼 β s t ω) (t : ℕ) (ω : Ω) :
    0 < pegP 𝔼 β Bm1 s i t ω := by
  induction t with
  | zero => exact div_pos (hB ω) (hpv 0 ω)
  | succ t ih =>
    have h1 : 0 < 1 + i t ω := by linarith [hi t ω]
    change 0 < (1 + i t ω) * pegP 𝔼 β Bm1 s i t ω * pvEx 𝔼 β s t ω / pv 𝔼 β s (t + 1) ω
    have := hpvEx t ω
    have := hpv (t + 1) ω
    positivity

/-- Cochrane (2023), bullets pp. 31–33, "the government can target nominal interest rates by
offering debt for sale with no change in surpluses": for every adapted target `i > −1`,
positive initial debt and positive present values, the target path `(pegP, pegB)` is an
equilibrium. -/
theorem peg_equilibrium (hPO : 𝔼.PullOut) (hBm1 : 𝔼.E 0 Bm1 = Bm1) (hB : ∀ ω, 0 < Bm1 ω)
    (hia : 𝔼.Adapted i) (hi : ∀ t ω, -1 < i t ω) (hpv : ∀ t ω, 0 < pv 𝔼 β s t ω)
    (hpvEx : ∀ t ω, 0 < pvEx 𝔼 β s t ω) :
    Equilibrium 𝔼 β Bm1 s (pegB 𝔼 β Bm1 s i) (pegP 𝔼 β Bm1 s i) i := by
  have hpos := pegP_pos (𝔼 := 𝔼) hB hi hpv hpvEx
  have hpvne : ∀ t ω, pv 𝔼 β s t ω ≠ 0 := fun t ω => (hpv t ω).ne'
  have hPa : 𝔼.Adapted (pegP 𝔼 β Bm1 s i) := by
    intro t
    induction t with
    | zero => exact E_div_known 𝔼 hPO hBm1 (pv_adapted 𝔼 β s 0) (hpvne 0)
    | succ t ih =>
      have hnum : 𝔼.E t ((1 + i t) * pegP 𝔼 β Bm1 s i t * pvEx 𝔼 β s t) =
          (1 + i t) * pegP 𝔼 β Bm1 s i t * pvEx 𝔼 β s t :=
        E_mul_known 𝔼 hPO (E_mul_known 𝔼 hPO (E_one_add_known 𝔼 (hia t)) ih)
          (pvEx_adapted 𝔼 β s t)
      exact E_div_known 𝔼 hPO (ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) hnum)
        (pv_adapted 𝔼 β s (t + 1)) (hpvne (t + 1))
  have hBa : 𝔼.Adapted (pegB 𝔼 β Bm1 s i) := fun t =>
    E_mul_known 𝔼 hPO (E_mul_known 𝔼 hPO (E_one_add_known 𝔼 (hia t)) (hPa t))
      (pvEx_adapted 𝔼 β s t)
  have hBpos : ∀ t ω, 0 < pegB 𝔼 β Bm1 s i t ω := by
    intro t ω
    have h1 : 0 < 1 + i t ω := by linarith [hi t ω]
    change 0 < (1 + i t ω) * pegP 𝔼 β Bm1 s i t ω * pvEx 𝔼 β s t ω
    have := hpos t ω
    have := hpvEx t ω
    positivity
  refine ⟨hPa, hpos, hBa, hia, hi, ⟨?_, fun t => ?_⟩, fun t => ?_⟩
  · funext ω
    change Bm1 ω / (Bm1 ω / pv 𝔼 β s 0 ω) = pv 𝔼 β s 0 ω
    rw [div_div_cancel₀ (hB ω).ne']
  · funext ω
    rw [pegP_succ]
    change pegB 𝔼 β Bm1 s i t ω / (pegB 𝔼 β Bm1 s i t ω / pv 𝔼 β s (t + 1) ω) = _
    rw [div_div_cancel₀ (hBpos t ω).ne']
  · set c : Ω → ℝ := ((1 + i t) * pvEx 𝔼 β s t)⁻¹ with hc
    have hca : 𝔼.E t c = c :=
      E_inv_known 𝔼 hPO (E_mul_known 𝔼 hPO (E_one_add_known 𝔼 (hia t)) (pvEx_adapted 𝔼 β s t))
        (fun ω => mul_ne_zero (by simp only [Pi.add_apply, Pi.one_apply]; linarith [hi t ω])
          (hpvEx t ω).ne')
    have hfun : pegP 𝔼 β Bm1 s i t / pegP 𝔼 β Bm1 s i (t + 1) = c * pv 𝔼 β s (t + 1) := by
      funext ω
      rw [pegP_succ]
      have h1 : 1 + i t ω ≠ 0 := by linarith [hi t ω]
      have := (hpos t ω).ne'
      have := (hpvEx t ω).ne'
      have := hpvne (t + 1) ω
      simp only [hc, pegB, Pi.div_apply, Pi.mul_apply, Pi.inv_apply, Pi.add_apply,
        Pi.one_apply]
      field_simp
    rw [hfun, hPO t c _ hca]
    funext ω
    have e := congrFun (pvEx_eq 𝔼 β s t) ω
    simp only [Pi.smul_apply, smul_eq_mul] at e
    have h1 : 1 + i t ω ≠ 0 := by linarith [hi t ω]
    have := (hpvEx t ω).ne'
    simp only [hc, Pi.inv_apply, Pi.add_apply, Pi.one_apply, Pi.smul_apply, Pi.mul_apply,
      smul_eq_mul]
    rw [mul_left_comm, ← e]
    field_simp

/-- Cochrane (2023), bullet p. 33, "inflation can be stable and determinate under an interest
rate target, or even an interest-rate peg": any equilibrium with the target `i` is the target
path `(pegP, pegB)`. -/
theorem peg_unique (hPO : 𝔼.PullOut) (hpv : ∀ t ω, pv 𝔼 β s t ω ≠ 0)
    (h : Equilibrium 𝔼 β Bm1 s B P i) :
    P = pegP 𝔼 β Bm1 s i ∧ B = pegB 𝔼 β Bm1 s i := by
  have hP : ∀ t, P t = pegP 𝔼 β Bm1 s i t := by
    intro t
    induction t with
    | zero =>
      funext ω
      rw [price_zero h ω (hpv 0 ω)]
      rfl
    | succ t ih =>
      funext ω
      rw [price_succ h t ω (hpv _ ω), debt_eq hPO h t ω, ih]
      rfl
  refine ⟨funext hP, funext fun t => ?_⟩
  funext ω
  rw [debt_eq hPO h t ω, hP t]
  rfl

/-- Cochrane (2023), §2.4.3–§2.4.4, pp. 31–33: existence and uniqueness of the equilibrium
under an interest-rate target (time-varying, state-contingent `i` allowed). -/
theorem peg_existsUnique (hPO : 𝔼.PullOut) (hBm1 : 𝔼.E 0 Bm1 = Bm1) (hB : ∀ ω, 0 < Bm1 ω)
    (hia : 𝔼.Adapted i) (hi : ∀ t ω, -1 < i t ω) (hpv : ∀ t ω, 0 < pv 𝔼 β s t ω)
    (hpvEx : ∀ t ω, 0 < pvEx 𝔼 β s t ω) :
    ∃! x : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), Equilibrium 𝔼 β Bm1 s x.2 x.1 i := by
  refine ⟨(pegP 𝔼 β Bm1 s i, pegB 𝔼 β Bm1 s i),
    peg_equilibrium hPO hBm1 hB hia hi hpv hpvEx, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := peg_unique hPO (fun t ω => (hpv t ω).ne') hx
  exact Prod.ext h1 h2

/-- Cochrane (2023), p. 32, bullet "the nominal interest-rate target determines expected
inflation": in every equilibrium `E_t(P_t/P_{t+1}) = 1/(β(1 + i_t))`. -/
theorem peg_expected_inflation (hβ : β ≠ 0) (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) :
    𝔼.E t (P t / P (t + 1)) = β⁻¹ • (1 + i t)⁻¹ := by
  rw [h.2.2.2.2.2.2 t, smul_smul, inv_mul_cancel₀ hβ, one_smul]

/-- Cochrane (2023), p. 33, bullet "monetary policy can target the nominal interest rate, and
determine expected inflation ... fiscal policy determines unexpected inflation": in equilibrium
`P_t/P_{t+1} = 1/(β(1 + i_t)) + ΔE_{t+1} ∑ βʲ s_{t+1+j} / (B_t/P_t)`. -/
theorem inflation_decomposition (hPO : 𝔼.PullOut) (hβ : β ≠ 0)
    (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) (ω : Ω) (hB : B t ω ≠ 0) :
    (P t / P (t + 1)) ω =
      β⁻¹ * (1 + i t ω)⁻¹ + innov 𝔼 t (epv β s (t + 1)) ω / (B t ω / P t ω) := by
  have hk : 𝔼.E (t + 1) (P t / P (t + 1)) = P t / P (t + 1) :=
    E_div_known 𝔼 hPO (ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (h.1 t)) (h.1 (t + 1))
      (fun ω => (h.2.1 (t + 1) ω).ne')
  have e := congrFun (eq_E_add_innov 𝔼 hk) ω
  rw [e, Pi.add_apply, peg_expected_inflation hβ h t, unexpected_inflation_eq hPO h t ω hB]
  rfl

/-- Cochrane (2023), p. 30 ("bad fiscal news affects inflation for one period only") and
p. 33: two equilibria with the same interest-rate target have the same expected inflation at
every date, whatever their surpluses and initial debt. -/
theorem expected_inflation_indep_surplus (hβ : β ≠ 0) {Bm1' : Ω → ℝ} {s' B' P' : ℕ → Ω → ℝ}
    (h : Equilibrium 𝔼 β Bm1 s B P i) (h' : Equilibrium 𝔼 β Bm1' s' B' P' i) (t : ℕ) :
    𝔼.E t (P' t / P' (t + 1)) = 𝔼.E t (P t / P (t + 1)) := by
  rw [peg_expected_inflation hβ h' t, peg_expected_inflation hβ h t]

/-- Cochrane (2023), p. 32, "if the government raises the interest-rate target ... it will sell
... more nominal debt": with the same surpluses and the same current price level, debt sold is
proportional to the gross rate, `B'_t/B_t = (1 + i'_t)/(1 + i_t)`. -/
theorem debt_ratio_of_rate (hPO : 𝔼.PullOut) {Bm1' : Ω → ℝ} {B' P' i' : ℕ → Ω → ℝ}
    (h : Equilibrium 𝔼 β Bm1 s B P i) (h' : Equilibrium 𝔼 β Bm1' s B' P' i') {t : ℕ}
    (hPt : P' t = P t) (ω : Ω) (hB : B t ω ≠ 0) :
    B' t ω / B t ω = (1 + i' t ω) / (1 + i t ω) := by
  have e1 := debt_eq hPO h' t ω
  have e2 := debt_eq hPO h t ω
  rw [hPt] at e1
  have hne : P t ω * pvEx 𝔼 β s t ω ≠ 0 := by
    intro h0; apply hB; rw [e2, mul_assoc, h0, mul_zero]
  rw [e1, e2, mul_assoc, mul_assoc, mul_div_mul_right _ _ hne]

/-- Cochrane (2023), p. 32 (survey E7): the exact proportional rise in nominal debt is
`ΔB/B = Δi/(1 + i)`. -/
theorem debt_growth_of_rate (hPO : 𝔼.PullOut) {Bm1' : Ω → ℝ} {B' P' i' : ℕ → Ω → ℝ}
    (h : Equilibrium 𝔼 β Bm1 s B P i) (h' : Equilibrium 𝔼 β Bm1' s B' P' i') {t : ℕ}
    (hPt : P' t = P t) (ω : Ω) (hB : B t ω ≠ 0) :
    B' t ω / B t ω - 1 = (i' t ω - i t ω) / (1 + i t ω) := by
  rw [debt_ratio_of_rate hPO h h' hPt ω hB]
  have hi : 1 + i t ω ≠ 0 := by linarith [h.2.2.2.2.1 t ω]
  field_simp
  ring

/-- Cochrane (2023), p. 32 (survey E7): "one percentage point higher rate, one percent more
debt" is exact only at `i = 0`: `Δi/(1 + i) = Δi` iff `Δi = 0` or `i = 0`. -/
theorem rate_change_eq_debt_growth_iff {i0 i1 : ℝ} (hi : -1 < i0) :
    (i1 - i0) / (1 + i0) = i1 - i0 ↔ i1 = i0 ∨ i0 = 0 := by
  have h1 : 1 + i0 ≠ 0 := by linarith
  rw [div_eq_iff h1]
  constructor
  · intro h
    have : (i1 - i0) * i0 = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h2 | h2
    · left; linarith
    · right; exact h2
  · rintro (h2 | h2)
    · rw [h2]; ring
    · rw [h2]; ring

/-- Cochrane (2023), p. 32 (survey E7): numerical counterexample to the printed "one percent":
raising the rate from 5% to 6% raises nominal debt by `1/105`, not `1/100`. -/
theorem printed_one_percent_fails : ((1 + 0.06) / (1 + 0.05) - 1 : ℝ) ≠ 0.01 := by
  norm_num

/-- Cochrane (2023), p. 32, "an attempt to fix the real rate in this model would lead to
infinite demands": with `c_t = y` the household Euler equation for a real bond priced at `q`
reads `q u'(y) = β u'(y)`, so the real bond price is forced to `β` (`R = 1/β`). -/
theorem real_rate_forced {u' q : ℝ} (hu : u' ≠ 0) (h : q * u' = β * u') : q = β :=
  mul_right_cancel₀ hu h

/-- Cochrane (2023), p. 32: a real-rate peg `q ≠ β` has no equilibrium: buying `x` real
bonds at price `q` changes utility by `u(y − q x) + β u(y + x)`, whose derivative at `x = 0` is
`(β − q) u'(y) ≠ 0`, so consuming the endowment is not optimal. -/
theorem no_eqm_real_rate_peg {u : ℝ → ℝ} {u' y q : ℝ} (hu : HasDerivAt u u' y) (hu' : u' ≠ 0)
    (hq : q ≠ β) : ¬ IsLocalMax (fun x => u (y - q * x) + β * u (y + x)) 0 := by
  intro hmax
  have h1 : HasDerivAt (fun x : ℝ => y - q * x) (-q) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul q).const_sub y
  have h2 : HasDerivAt (fun x : ℝ => y + x) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add y
  have hu1 : HasDerivAt u u' (y - q * 0) := by simpa using hu
  have hu2 : HasDerivAt u u' (y + 0) := by simpa using hu
  have hd : HasDerivAt (fun x => u (y - q * x) + β * u (y + x)) (u' * -q + β * (u' * 1)) 0 :=
    HasDerivAt.add (hu1.comp 0 h1) ((hu2.comp 0 h2).const_mul β)
  have h0 := hmax.hasDerivAt_eq_zero hd
  apply hq
  apply mul_right_cancel₀ hu'
  linear_combination -h0

/-- Cochrane (2023), p. 32, "infinite demands": with linear utility a real-rate peg `q ≠ β`
makes the gain from trading real bonds unbounded. -/
theorem real_rate_peg_unbounded {y q : ℝ} (hq : q ≠ β) (M : ℝ) :
    ∃ x, M < (y - q * x) + β * (y + x) - (y + β * y) := by
  have hne : β - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  refine ⟨(|M| + 1) / (β - q), ?_⟩
  have : (y - q * ((|M| + 1) / (β - q))) + β * (y + (|M| + 1) / (β - q)) - (y + β * y) =
      |M| + 1 := by
    field_simp
    ring
  rw [this]
  linarith [le_abs_self M]

/-- Cochrane (2023), p. 33 (the classic doctrine: without the valuation equation the price
level is not determined): scaling a solution by `c > 0` preserves every equilibrium condition
except the initial valuation equation `B_{−1}/P_0 = PV_0`, which fails for `c ≠ 1`. -/
theorem scaled_all_but_initial (hPO : 𝔼.PullOut) (h : Equilibrium 𝔼 β Bm1 s B P i) {c : ℝ}
    (hc : 0 < c) :
    𝔼.Adapted (fun t => c • P t) ∧ (∀ t ω, 0 < c * P t ω) ∧ 𝔼.Adapted (fun t => c • B t) ∧
      (∀ t, c • B t / c • P (t + 1) = pv 𝔼 β s (t + 1)) ∧
      BondPricing 𝔼 β (fun t => c • P t) i := by
  have _ := hPO
  refine ⟨fun t => by simp only [map_smul, h.1 t], fun t ω => mul_pos hc (h.2.1 t ω),
    fun t => by simp only [map_smul, h.2.2.1 t], fun t => ?_, fun t => ?_⟩
  · rw [← h.2.2.2.2.2.1.2 t]
    funext ω
    simp only [Pi.div_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_div_mul_left _ _ hc.ne']
  · rw [h.2.2.2.2.2.2 t]
    congr 2
    funext ω
    simp only [Pi.div_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_div_mul_left _ _ hc.ne']

/-- Cochrane (2023), p. 33: the initial valuation equation pins the scale: for `c ≠ 1` and
nonzero initial debt the scaled price level violates `B_{−1}/P_0 = PV_0`. -/
theorem scaled_not_initial (h : Equilibrium 𝔼 β Bm1 s B P i) {c : ℝ} (hc : c ≠ 1) {ω : Ω}
    (hB : Bm1 ω ≠ 0) : Bm1 / (c • P 0) ≠ pv 𝔼 β s 0 := by
  intro h1
  have e1 := congrFun h1 ω
  have e2 := congrFun h.2.2.2.2.2.1.1 ω
  simp only [Pi.div_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
  have hP := (h.2.1 0 ω).ne'
  rw [← e2] at e1
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, zero_mul, div_zero] at e1; exact hB (by field_simp at e1; linarith)
  field_simp at e1
  exact hc e1.symm

/-- Cochrane (2023), p. 33, perfect foresight: the bond-pricing condition is
`P_{t+1} = β (1 + i_t) P_t`, so monetary policy alone gives a family of price paths. -/
theorem pf_pricing_iff (hβ : β ≠ 0) {P i : ℕ → Unit → ℝ} (hP : ∀ t u, 0 < P t u)
    (hi : ∀ t u, -1 < i t u) :
    BondPricing perfectForesight β P i ↔ ∀ t, P (t + 1) () = β * (1 + i t ()) * P t () := by
  constructor
  · intro h t
    have e := congrFun (h t) ()
    change (1 + i t ())⁻¹ = β * (P t () / P (t + 1) ()) at e
    have h1 : 1 + i t () ≠ 0 := by linarith [hi t ()]
    have := (hP t ()).ne'
    have := (hP (t + 1) ()).ne'
    field_simp at e
    linear_combination e
  · intro h t
    funext u
    cases u
    change (1 + i t ())⁻¹ = β * (P t () / P (t + 1) ())
    have h1 : 1 + i t () ≠ 0 := by linarith [hi t ()]
    have := (hP t ()).ne'
    rw [h t]
    field_simp

/-- Cochrane (2023), p. 33, "fiscal policy only determines ... the time-zero price level ...
thereby choosing which of the many price level paths is unique": under perfect foresight every
equilibrium has `P_t = (B_{−1}/PV_0) ∏_{k<t} β(1 + i_k)`. -/
theorem pf_price_formula {Bm1 : Unit → ℝ} {s B P i : ℕ → Unit → ℝ}
    (hβ : β ≠ 0) (h : Equilibrium perfectForesight β Bm1 s B P i)
    (hpv : pv perfectForesight β s 0 () ≠ 0)
    (t : ℕ) :
    P t () = Bm1 () / pv perfectForesight β s 0 () *
      ∏ k ∈ Finset.range t, (β * (1 + i k ())) := by
  have hrec := (pf_pricing_iff hβ h.2.1 h.2.2.2.2.1).mp h.2.2.2.2.2.2
  induction t with
  | zero => simp [price_zero h () hpv]
  | succ t ih =>
    rw [hrec t, ih, Finset.prod_range_succ]
    ring

/-- Cochrane (2023), p. 33: under perfect foresight every scale `c > 0` gives a path
`c ∏_{k<t} β(1 + i_k)` satisfying the bond-pricing condition (the family generated by monetary
policy, of which the valuation equation selects `c = B_{−1}/PV_0`). -/
theorem pf_family {i : ℕ → Unit → ℝ} (hβ : 0 < β) (hi : ∀ t u, -1 < i t u) {c : ℝ}
    (hc : 0 < c) :
    BondPricing perfectForesight β
      (fun t _ => c * ∏ k ∈ Finset.range t, (β * (1 + i k ()))) i := by
  have hpos : ∀ t (u : Unit), 0 < c * ∏ k ∈ Finset.range t, (β * (1 + i k ())) := by
    intro t _
    refine mul_pos hc (Finset.prod_pos fun k _ => mul_pos hβ (by linarith [hi k ()]))
  refine (pf_pricing_iff hβ.ne' hpos hi).mpr fun t => ?_
  rw [Finset.prod_range_succ]
  ring


/-! ### Fiscal policy and debt (§2.7) -/

/-- Cochrane (2023), eq. (2.7), p. 22: for bounded surpluses the date-`r` forecast of the
ex-post sum is the sum of forecasts, `E_r ∑ βʲ s_{t+j} = ∑ βʲ E_r s_{t+j}`. -/
theorem E_epv_tsum {M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hs : ∀ t ω, |s t ω| ≤ M)
    (r t : ℕ) (ω : Ω) : 𝔼.E r (epv β s t) ω = ∑' j, β ^ j * 𝔼.E r (s (t + j)) ω := by
  have hb : ∀ j ω', |β ^ j * s (t + j) ω'| ≤ β ^ j * M := fun j ω' => by
    rw [abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (hs (t + j) ω') (pow_nonneg hβ0 j)
  change 𝔼.E r (fun ω' => ∑' j, β ^ j * s (t + j) ω') ω = _
  rw [𝔼.E_tsum hβ0 hβ1 hb r ω]
  refine tsum_congr fun j => ?_
  change 𝔼.E r (β ^ j • s (t + j)) ω = _
  rw [map_smul]
  rfl

/-- Cochrane (2023), p. 43: for bounded surpluses the present-value news is the discounted sum
of surplus news, `ΔE_{t+1} ∑ βʲ s_{t+1+j} = ∑ βʲ ΔE_{t+1} s_{t+1+j}`. -/
theorem news_epv_tsum {M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hs : ∀ t ω, |s t ω| ≤ M)
    (t : ℕ) (ω : Ω) :
    innov 𝔼 t (epv β s (t + 1)) ω = ∑' j, β ^ j * innov 𝔼 t (s (t + 1 + j)) ω := by
  have hsum : ∀ r, Summable (fun j => β ^ j * 𝔼.E r (s (t + 1 + j)) ω) := fun r =>
    summable_E_shift 𝔼 hβ0 hβ1 hs r (t + 1) ω
  simp only [innov, Pi.sub_apply]
  rw [E_epv_tsum hβ0 hβ1 hs, E_epv_tsum hβ0 hβ1 hs, ← (hsum (t + 1)).tsum_sub (hsum t)]
  exact tsum_congr fun j => by ring

/-- Cochrane (2023), p. 43, "the surplus process must have an s-shaped moving average": if the
discounted sum of news `∑ βʲ d_j` is zero and the current news `d_0` is a deficit, some later
news `d_j`, `j ≥ 1`, is a surplus. -/
theorem sShape_seq (hβ : 0 < β) {d : ℕ → ℝ} (hd : Summable (fun j => β ^ j * d j))
    (h0 : ∑' j, β ^ j * d j = 0) (hd0 : d 0 < 0) : ∃ j, 1 ≤ j ∧ 0 < d j := by
  by_contra hc
  push Not at hc
  have htail : ∑' j, β ^ (j + 1) * d (j + 1) ≤ 0 :=
    tsum_nonpos fun j => mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ.le _)
      (hc (j + 1) (by omega))
  rw [hd.tsum_eq_zero_add] at h0
  simp only [pow_zero, one_mul] at h0
  linarith

/-- Cochrane (2023), p. 43: with bounded surpluses, zero unexpected present value and a current
deficit shock `ΔE_{t+1} s_{t+1} < 0` force a later positive surplus shock (the s-shape). -/
theorem sShape {M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs : ∀ t ω, |s t ω| ≤ M) (t : ℕ) (ω : Ω)
    (h0 : innov 𝔼 t (epv β s (t + 1)) ω = 0) (hd : innov 𝔼 t (s (t + 1)) ω < 0) :
    ∃ j, 1 ≤ j ∧ 0 < innov 𝔼 t (s (t + 1 + j)) ω := by
  have hsum : Summable (fun j => β ^ j * innov 𝔼 t (s (t + 1 + j)) ω) := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right (M + M)) (fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0.le]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0.le j)
    simp only [innov, Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (𝔼.abs_E_le (hs _) _ ω) (𝔼.abs_E_le (hs _) _ ω))
  rw [news_epv_tsum hβ0.le hβ1 hs] at h0
  exact sShape_seq hβ0 hsum h0 (by simpa using hd)

/-- Cochrane (2023), p. 42, "a credible fiscal reform can coexist with ongoing or even larger
short-term deficits, yet produce a disinflation": a pattern of surplus news with deficits at the
first two dates and a positive present value. -/
theorem reform_with_deficits (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ d : ℕ → ℝ, d 0 < 0 ∧ d 1 < 0 ∧ Summable (fun j => β ^ j * d j) ∧
      0 < ∑' j, β ^ j * d j := by
  set d : ℕ → ℝ := fun j => if j = 2 then 3 / β ^ 2 else if j < 2 then -1 else 0 with hd
  have hz : ∀ j ∉ Finset.range 3, β ^ j * d j = 0 := by
    intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    simp only [hd, show j ≠ 2 by omega, show ¬ j < 2 by omega, ↓reduceIte, mul_zero]
  refine ⟨d, by simp [hd], by simp [hd], summable_of_ne_finset_zero hz, ?_⟩
  rw [tsum_eq_sum hz]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hd]
  norm_num
  field_simp
  linarith

/-- Cochrane (2023), p. 42, the equity issue: if two equilibria share the current price level
and the debt sold rises in proportion to the expected subsequent surpluses
(`B'_t PV^{ex}_t = B_t PV'^{ex}_t`), the nominal rate is unchanged and real revenue rises in
proportion to the debt. -/
theorem equityIssue (hPO : 𝔼.PullOut) {Bm1' : Ω → ℝ} {s' B' P' i' : ℕ → Ω → ℝ}
    (h : Equilibrium 𝔼 β Bm1 s B P i) (h' : Equilibrium 𝔼 β Bm1' s' B' P' i') {t : ℕ}
    (hPt : P' t = P t) (ω : Ω)
    (hprop : B' t ω * pvEx 𝔼 β s t ω = B t ω * pvEx 𝔼 β s' t ω)
    (hex : pvEx 𝔼 β s t ω ≠ 0) (hex' : pvEx 𝔼 β s' t ω ≠ 0) :
    i' t ω = i t ω ∧
      ((B' t / P' t) * (1 + i' t)⁻¹) ω * B t ω = ((B t / P t) * (1 + i t)⁻¹) ω * B' t ω := by
  have e1 := debt_eq hPO h' t ω
  have e2 := debt_eq hPO h t ω
  rw [hPt] at e1
  have hP := (h.2.1 t ω).ne'
  refine ⟨?_, ?_⟩
  · rw [e1, e2] at hprop
    have : (i' t ω - i t ω) * (P t ω * pvEx 𝔼 β s' t ω * pvEx 𝔼 β s t ω) = 0 := by
      linear_combination hprop
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · exfalso
      exact mul_ne_zero (mul_ne_zero hP hex') hex h0
  · rw [(expected_valuation hPO h' t).2, (expected_valuation hPO h t).2]
    linear_combination -hprop

/-- Cochrane (2023), p. 42, "this extra money can finance a deficit, a lower `s_t`, with no
unexpected inflation": with the same debt outstanding, a deficit `s'_{t+1} = s_{t+1} − δ`
matched by higher subsequent surpluses `PV'^{ex}_{t+1} = PV^{ex}_{t+1} + δ` leaves the price
level unchanged and raises real bond revenue by `δ`. -/
theorem equityIssue_finances_deficit (hPO : 𝔼.PullOut) {Bm1' : Ω → ℝ}
    {s' B' P' i' : ℕ → Ω → ℝ} (hs : SurplusSummable β s) (hs' : SurplusSummable β s')
    (hsa : 𝔼.Adapted s) (hsa' : 𝔼.Adapted s') (h : Equilibrium 𝔼 β Bm1 s B P i)
    (h' : Equilibrium 𝔼 β Bm1' s' B' P' i') {t : ℕ} {δ : Ω → ℝ} (hBt : B' t = B t)
    (hst : s' (t + 1) = s (t + 1) - δ) (hex : pvEx 𝔼 β s' (t + 1) = pvEx 𝔼 β s (t + 1) + δ)
    (hpv : ∀ ω, pv 𝔼 β s (t + 1) ω ≠ 0) :
    P' (t + 1) = P (t + 1) ∧
      (B' (t + 1) / P' (t + 1)) * (1 + i' (t + 1))⁻¹ =
        (B (t + 1) / P (t + 1)) * (1 + i (t + 1))⁻¹ + δ := by
  have hpveq : pv 𝔼 β s' (t + 1) = pv 𝔼 β s (t + 1) := by
    rw [pv_eq_add_pvEx 𝔼 hs' hsa', pv_eq_add_pvEx 𝔼 hs hsa, hst, hex]
    abel
  refine ⟨funext fun ω => ?_, ?_⟩
  · rw [price_succ h' t ω (by rw [hpveq]; exact hpv ω), price_succ h t ω (hpv ω), hBt, hpveq]
  · rw [(expected_valuation hPO h' (t + 1)).2, (expected_valuation hPO h (t + 1)).2, hex]

/-! ### AR(1) surpluses (§2.7, p. 43) -/

/-- Cochrane (2023), p. 43: for an AR(1) surplus `E_t s_{t+1} = η s_t`, the news about
`s_{t+1+j}` is `ηʲ ε_{s,t+1}` with `ε_{s,t+1} = s_{t+1} − η s_t`. -/
theorem ar1_news {η : ℝ} (hAR : 𝔼.IsAR1 η s) (t j : ℕ) :
    innov 𝔼 t (s (t + 1 + j)) = η ^ j • (s (t + 1) - η • s t) := by
  rw [innov, 𝔼.ar1_iterate hAR (t + 1) j, show t + 1 + j = t + (j + 1) by omega,
    𝔼.ar1_iterate hAR t (j + 1), smul_sub, smul_smul, pow_succ]

/-- Cochrane (2023), p. 43: for a bounded AR(1) surplus the present-value news is
`ΔE_{t+1} ∑ βʲ s_{t+1+j} = ε_{s,t+1}/(1 − βη)`. -/
theorem ar1_pv_news {η M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hβη : |β * η| < 1)
    (hs : ∀ t ω, |s t ω| ≤ M) (hAR : 𝔼.IsAR1 η s) (t : ℕ) :
    innov 𝔼 t (epv β s (t + 1)) = (1 - β * η)⁻¹ • (s (t + 1) - η • s t) := by
  funext ω
  rw [news_epv_tsum hβ0 hβ1 hs]
  simp only [ar1_news hAR, Pi.smul_apply, smul_eq_mul]
  have : ∀ j : ℕ, β ^ j * (η ^ j * (s (t + 1) - η • s t) ω) =
      (β * η) ^ j * (s (t + 1) - η • s t) ω := fun j => by rw [mul_pow]; ring
  simp only [this]
  rw [tsum_mul_right, tsum_geometric_of_abs_lt_one hβη]

/-- Cochrane (2023), p. 43, corrected (survey E5): with an AR(1) surplus the unexpected
inflation satisfies `(B_t/P_t) ΔE_{t+1}(P_t/P_{t+1}) = ε_{s,t+1}/(1 − βη)`; the printed
`ΔE_{t+1}(P_t/P_{t+1}) = ε_{s,t+1}/(1 − βη)` omits the factor `B_t/P_t`. -/
theorem ar1_unexpected_inflation (hPO : 𝔼.PullOut) {η M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hβη : |β * η| < 1) (hs : ∀ t ω, |s t ω| ≤ M) (hAR : 𝔼.IsAR1 η s)
    (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) :
    (B t / P t) * innov 𝔼 t (P t / P (t + 1)) = (1 - β * η)⁻¹ • (s (t + 1) - η • s t) := by
  rw [unexpected_inflation hPO h t, ar1_pv_news hβ0 hβ1 hβη hs hAR]

/-- Cochrane (2023), p. 43 (survey E5): the printed formula
`ΔE_{t+1}(P_t/P_{t+1}) = ε_{s,t+1}/(1 − βη)` fails whenever the shock is nonzero and the real
value of the debt `B_t/P_t` differs from one. -/
theorem ar1_printed_fails (hPO : 𝔼.PullOut) {η M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hβη : |β * η| < 1) (hs : ∀ t ω, |s t ω| ≤ M) (hAR : 𝔼.IsAR1 η s)
    (h : Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) (ω : Ω)
    (hε : (s (t + 1) - η • s t) ω ≠ 0) (hV : B t ω / P t ω ≠ 1) :
    innov 𝔼 t (P t / P (t + 1)) ω ≠ ((1 - β * η)⁻¹ • (s (t + 1) - η • s t)) ω := by
  intro he
  have e := congrFun (ar1_unexpected_inflation hPO hβ0 hβ1 hβη hs hAR h t) ω
  simp only [Pi.mul_apply, Pi.div_apply] at e
  rw [he] at e
  have h1 : 1 - β * η ≠ 0 := by
    intro h0; rw [show β * η = 1 by linarith, abs_one] at hβη; exact lt_irrefl _ hβη
  have hx : ((1 - β * η)⁻¹ • (s (t + 1) - η • s t)) ω ≠ 0 := by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero (inv_ne_zero h1) hε
  apply hV
  apply mul_right_cancel₀ hx
  rw [one_mul, e]

/-- Cochrane (2023), p. 43: for an AR(1) surplus the news about the value of the debt sold,
`ΔE_{t+1} ∑_{j≥1} βʲ s_{t+1+j}`, is `βη/(1 − βη) ε_{s,t+1}`. -/
theorem ar1_value_news {η M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hβη : |β * η| < 1)
    (hs : ∀ t ω, |s t ω| ≤ M) (hAR : 𝔼.IsAR1 η s) (t : ℕ) :
    innov 𝔼 t (pvEx 𝔼 β s (t + 1)) = (β * η * (1 - β * η)⁻¹) • (s (t + 1) - η • s t) := by
  have hsum := surplusSummable_of_bounded hβ0 hβ1 hs
  have hpe : pvEx 𝔼 β s (t + 1) = pv 𝔼 β s (t + 1) - s (t + 1) := by
    rw [pv_eq_add_pvEx 𝔼 hsum hAR.1]; abel
  have hn0 := ar1_news hAR t 0
  simp only [add_zero, pow_zero, one_smul] at hn0
  rw [hpe, innov_sub, news_pv_succ, ar1_pv_news hβ0 hβ1 hβη hs hAR, hn0]
  have h1 : 1 - β * η ≠ 0 := by
    intro h0; rw [show β * η = 1 by linarith, abs_one] at hβη; exact lt_irrefl _ hβη
  funext ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Cochrane (2023), p. 43, "the AR(1) generates a value of debt ... that goes down when there
is a deficit": with `0 < βη < 1` a deficit shock lowers the value of the debt. -/
theorem ar1_value_falls {η M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hpos : 0 < β * η)
    (hlt : β * η < 1) (hs : ∀ t ω, |s t ω| ≤ M) (hAR : 𝔼.IsAR1 η s) (t : ℕ) (ω : Ω)
    (hε : (s (t + 1) - η • s t) ω < 0) : innov 𝔼 t (pvEx 𝔼 β s (t + 1)) ω < 0 := by
  have hβη : |β * η| < 1 := by rw [abs_of_pos hpos]; exact hlt
  rw [ar1_value_news hβ0 hβ1 hβη hs hAR, Pi.smul_apply, smul_eq_mul]
  have : 0 < β * η * (1 - β * η)⁻¹ := mul_pos hpos (inv_pos.mpr (by linarith))
  exact mul_neg_of_pos_of_neg this hε

/-- Cochrane (2023), p. 43, "unexpected inflation is larger than the deficit shock": for
`0 < βη < 1` and a deficit `ε < 0`, the present-value news `ε/(1 − βη)` is below `ε`. -/
theorem ar1_news_exceeds_deficit {η ε : ℝ} (hpos : 0 < β * η) (hlt : β * η < 1) (hε : ε < 0) :
    (1 - β * η)⁻¹ * ε < ε := by
  have h1 : 0 < 1 - β * η := by linarith
  rw [inv_mul_lt_iff₀ h1]
  nlinarith

/-! ### The central bank and the Treasury (§2.8) and fiscal stimulus (§2.10) -/

/-- Cochrane (2023), p. 33 and §2.8, p. 44: the split between Treasury and central bank is
irrelevant: if the central bank finances its holdings `B^C` of Treasury debt by overnight
reserves `R = B^C` (perfect substitutes for bonds), the equilibrium conditions depend only on
the debt held by the public, `B^T − B^C + R = B^T`. -/
theorem consolidation_irrelevant {BT BC R : ℕ → Ω → ℝ} (hcb : ∀ t, R t = BC t) :
    Equilibrium 𝔼 β Bm1 s (fun t => BT t - BC t + R t) P i ↔ Equilibrium 𝔼 β Bm1 s BT P i := by
  have : (fun t => BT t - BC t + R t) = BT := funext fun t => by rw [hcb t]; abel
  rw [this]

/-- Cochrane (2023), p. 50, "borrow money, ... spend the money, repay the debt has no effect at
all on current ... inflation": a rearrangement of surpluses that leaves the present value at
`t + 1` unchanged, with the same debt outstanding, leaves `P_{t+1}` unchanged. -/
theorem stimulus_no_jump {s' B' P' i' : ℕ → Ω → ℝ} {Bm1' : Ω → ℝ}
    (h : Equilibrium 𝔼 β Bm1 s B P i) (h' : Equilibrium 𝔼 β Bm1' s' B' P' i') {t : ℕ}
    (hBt : B' t = B t) (hpv : pv 𝔼 β s' (t + 1) = pv 𝔼 β s (t + 1))
    (hpv0 : ∀ ω, pv 𝔼 β s (t + 1) ω ≠ 0) : P' (t + 1) = P (t + 1) := by
  funext ω
  rw [price_succ h' t ω (by rw [hpv]; exact hpv0 ω), price_succ h t ω (hpv0 ω), hBt, hpv]

/-- Cochrane (2023), p. 50, perfect foresight: a rearrangement of surpluses with the same
initial present value and the same interest-rate target leaves the whole price path unchanged
(no effect on current or expected future inflation). -/
theorem pf_stimulus_neutral (hβ : β ≠ 0) {s' B' P' : ℕ → Unit → ℝ} {Bm1 : Unit → ℝ}
    {s B P i : ℕ → Unit → ℝ} (h : Equilibrium perfectForesight β Bm1 s B P i)
    (h' : Equilibrium perfectForesight β Bm1 s' B' P' i)
    (hpv : pv perfectForesight β s' 0 = pv perfectForesight β s 0)
    (hpv0 : pv perfectForesight β s 0 () ≠ 0) : P' = P := by
  funext t u
  cases u
  rw [pf_price_formula hβ h' (by rw [hpv]; exact hpv0), pf_price_formula hβ h hpv0, hpv]

/-- Cochrane (2023), p. 50, corrected for uncertainty: a stimulus that adds a date-`t`-known
amount `D` to the present value at `t + 1` (same target `i`, same `P_t`) leaves `P_{t+1}`
unchanged in state `ω` iff `D = 0` there or there is no other fiscal news
`ΔE_{t+1} ∑ βʲ s_{t+1+j} = 0`. Under genuine uncertainty "no effect at all" fails. -/
theorem stimulus_price_iff (hPO : 𝔼.PullOut) (hβ : β ≠ 0) {s' B' P' : ℕ → Ω → ℝ}
    {Bm1' : Ω → ℝ} (h : Equilibrium 𝔼 β Bm1 s B P i) (h' : Equilibrium 𝔼 β Bm1' s' B' P' i)
    {t : ℕ} (hPt : P' t = P t) {D : Ω → ℝ} (hD : 𝔼.E t D = D)
    (hpv : pv 𝔼 β s' (t + 1) = pv 𝔼 β s (t + 1) + D) (ω : Ω)
    (hpv0 : pv 𝔼 β s (t + 1) ω ≠ 0) (hpv0' : pv 𝔼 β s' (t + 1) ω ≠ 0) :
    P' (t + 1) ω = P (t + 1) ω ↔ D ω = 0 ∨ innov 𝔼 t (epv β s (t + 1)) ω = 0 := by
  have hex' : pvEx 𝔼 β s' t = pvEx 𝔼 β s t + β • D := by
    rw [pvEx_eq, pvEx_eq, hpv, map_add, hD, smul_add]
  have e1 : P' (t + 1) ω = (1 + i t ω) * P t ω * (pvEx 𝔼 β s t ω + β * D ω) /
      (pv 𝔼 β s (t + 1) ω + D ω) := by
    rw [price_succ h' t ω hpv0', debt_eq hPO h' t ω, hPt, hex', hpv]
    rfl
  have e2 : P (t + 1) ω = (1 + i t ω) * P t ω * pvEx 𝔼 β s t ω / pv 𝔼 β s (t + 1) ω := by
    rw [price_succ h t ω hpv0, debt_eq hPO h t ω]
  have hnews : innov 𝔼 t (epv β s (t + 1)) ω = pv 𝔼 β s (t + 1) ω - β⁻¹ * pvEx 𝔼 β s t ω := by
    rw [← news_pv_succ, innov, pv_adapted 𝔼 β s (t + 1), pvEx_eq]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
  have hden : pv 𝔼 β s (t + 1) ω + D ω ≠ 0 := by
    have := congrFun hpv ω; simp only [Pi.add_apply] at this; rwa [← this]
  have hc : (1 + i t ω) * P t ω ≠ 0 :=
    mul_ne_zero (by linarith [h.2.2.2.2.1 t ω]) (h.2.1 t ω).ne'
  rw [e1, e2, hnews, div_eq_div_iff hden hpv0]
  constructor
  · intro heq
    have : D ω * (β * pv 𝔼 β s (t + 1) ω - pvEx 𝔼 β s t ω) * ((1 + i t ω) * P t ω) = 0 := by
      linear_combination heq
    rcases mul_eq_zero.mp this with h0 | h0
    · rcases mul_eq_zero.mp h0 with h1 | h1
      · exact Or.inl h1
      · right
        field_simp
        linear_combination h1
    · exact absurd h0 hc
  · rintro (h0 | h0)
    · rw [h0]; ring
    · field_simp at h0
      linear_combination ((1 + i t ω) * P t ω * D ω) * h0

/-- Cochrane (2023), p. 50, corrected for uncertainty: if a stimulus leaves the present-value
news unchanged, unexpected inflation is rescaled by the real value of the debt,
`(B'_t/P'_t) ΔE_{t+1}(P'_t/P'_{t+1}) = (B_t/P_t) ΔE_{t+1}(P_t/P_{t+1})`. -/
theorem stimulus_unexpected_inflation (hPO : 𝔼.PullOut) {s' B' P' i' : ℕ → Ω → ℝ}
    {Bm1' : Ω → ℝ} (h : Equilibrium 𝔼 β Bm1 s B P i) (h' : Equilibrium 𝔼 β Bm1' s' B' P' i')
    {t : ℕ} (hn : innov 𝔼 t (epv β s' (t + 1)) = innov 𝔼 t (epv β s (t + 1))) :
    (B' t / P' t) * innov 𝔼 t (P' t / P' (t + 1)) = (B t / P t) * innov 𝔼 t (P t / P (t + 1)) := by
  rw [unexpected_inflation hPO h' t, unexpected_inflation hPO h t, hn]

/-- Cochrane (2023), p. 50: adding a date-`t`-known amount to the present value at `t + 1`
does not change the present-value news. -/
theorem news_pv_add_known {s' : ℕ → Ω → ℝ} {t : ℕ} {D : Ω → ℝ} (hD : 𝔼.E t D = D)
    (hpv : pv 𝔼 β s' (t + 1) = pv 𝔼 β s (t + 1) + D) :
    innov 𝔼 t (epv β s' (t + 1)) = innov 𝔼 t (epv β s (t + 1)) := by
  rw [← news_pv_succ, ← news_pv_succ, hpv, innov_add, innov_of_known 𝔼 hD, add_zero]


/-! ### A coin-flip economy: fiscal stimulus is not neutral under uncertainty -/

namespace CoinExample

open ExpectationsFiniteTree

/-- Cochrane (2023), p. 50 (example economy): the indicator of heads on the first coin. -/
def fh (b : Bool) : ℝ := if b then 1 else 0

/-- Cochrane (2023), p. 50 (example economy): the first-coin indicator is `0` or `1`. -/
theorem fh_nonneg (b : Bool) : 0 ≤ fh b := by cases b <;> simp [fh]

/-- Cochrane (2023), p. 50 (example economy): a variable that depends only on the first coin is
known from date `1` on. -/
theorem coin_E_first {t : ℕ} (ht : 1 ≤ t) (f : Bool → ℝ) :
    coinSystem.E t (fun ω => f ω.1) = fun ω => f ω.1 := by
  funext ω
  rw [coinSystem, FiniteTree.toExpectationSystem_E]
  refine coinTree.condE_of_const_on_cell fun ω' h => ?_
  have h' := coinTree.refines ht ω' ω h
  change Setoid.ker (coinObs 1) ω' ω at h'
  rw [Setoid.ker_def] at h'
  simp only [coinObs, Prod.mk.injEq] at h'
  obtain ⟨h1, -⟩ := h'
  simp only [le_refl, ↓reduceIte] at h1
  rw [h1]

/-- Cochrane (2023), p. 50 (example economy): at date `0` the first coin is forecast at
`1/2`, so `E_0(a + b·fh) = a + b/2`. -/
theorem coin_E_zero (a b : ℝ) :
    coinSystem.E 0 (fun ω => a + b * fh ω.1) = fun _ => a + b / 2 := by
  have hsplit : (fun ω : Bool × Bool => a + b * fh ω.1) = (fun _ => a) + b • firstHeads := by
    funext ω
    simp [fh, firstHeads]
  funext ω
  rw [hsplit, map_add, map_smul, coinSystem.const, Pi.add_apply, Pi.smul_apply,
    coinSystem_E0_firstHeads, smul_eq_mul]
  ring

/-- Cochrane (2023), p. 50 (example economy): baseline surpluses `s_0 = 1`,
`s_t = 1 + fh` for `t ≥ 1` (news about all future surpluses arrives at date `1`). -/
noncomputable def sB (t : ℕ) : Bool × Bool → ℝ := fun ω => if t = 0 then 1 else 1 + fh ω.1

/-- Cochrane (2023), p. 50 (example economy): the stimulus "borrow, spend, repay": half a unit
less surplus at date `0`, one unit more at date `1` (`(1/2)/β` with `β = 1/2`), the rest
unchanged. -/
noncomputable def sS (t : ℕ) : Bool × Bool → ℝ :=
  fun ω => if t = 0 then 1 / 2 else if t = 1 then 2 + fh ω.1 else 1 + fh ω.1

/-- Cochrane (2023), p. 50 (example economy): with `β = 1/2`, a surplus `1 + fh` forever has
ex-post value `2(1 + fh)`. -/
theorem epv_tail {x : ℕ → Bool × Bool → ℝ} {t : ℕ}
    (hx : ∀ j, x (t + j) = fun ω => 1 + fh ω.1) :
    epv (1 / 2) x t = fun ω => 2 * (1 + fh ω.1) := by
  funext ω
  simp only [epv, hx]
  rw [tsum_mul_right, tsum_geometric_two]

/-- Cochrane (2023), p. 50 (example economy): the surpluses are bounded. -/
theorem sB_bounded : ∀ t ω, |sB t ω| ≤ 3 := by
  intro t ω
  have := fh_nonneg ω.1
  have : fh ω.1 ≤ 1 := by cases ω.1 <;> simp [fh]
  simp only [sB]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

/-- Cochrane (2023), p. 50 (example economy): the stimulus surpluses are bounded. -/
theorem sS_bounded : ∀ t ω, |sS t ω| ≤ 3 := by
  intro t ω
  have := fh_nonneg ω.1
  have : fh ω.1 ≤ 1 := by cases ω.1 <;> simp [fh]
  simp only [sS]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

/-- Cochrane (2023), p. 50 (example economy): baseline ex-post values from date `1` on. -/
theorem epv_sB_succ (t : ℕ) : epv (1 / 2) sB (t + 1) = fun ω => 2 * (1 + fh ω.1) :=
  epv_tail fun j => funext fun ω => by simp [sB]

/-- Cochrane (2023), p. 50 (example economy): stimulus ex-post values from date `2` on. -/
theorem epv_sS_add_two (t : ℕ) : epv (1 / 2) sS (t + 2) = fun ω => 2 * (1 + fh ω.1) :=
  epv_tail fun j => funext fun ω => by
    simp only [sS, show t + 2 + j ≠ 0 by omega, show t + 2 + j ≠ 1 by omega, ↓reduceIte]

/-- Cochrane (2023), p. 50 (example economy): the stimulus ex-post value at date `1` is
`3 + 2 fh`. -/
theorem epv_sS_one : epv (1 / 2) sS 1 = fun ω => 3 + 2 * fh ω.1 := by
  rw [epv_succ (surplusSummable_of_bounded (by norm_num) (by norm_num) sS_bounded),
    epv_sS_add_two 0]
  funext ω
  simp only [sS, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  norm_num
  ring

/-- Cochrane (2023), p. 50 (example economy): baseline and stimulus have the same date-`0`
present value `5/2`. -/
theorem pv_zero_eq : pv coinSystem (1 / 2) sS 0 = pv coinSystem (1 / 2) sB 0 ∧
    pv coinSystem (1 / 2) sB 0 = fun _ => 5 / 2 := by
  have h1 : epv (1 / 2) sB 0 = fun ω => 2 + 1 * fh ω.1 := by
    rw [epv_succ (surplusSummable_of_bounded (by norm_num) (by norm_num) sB_bounded),
      epv_sB_succ 0]
    funext ω
    simp only [sB, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    norm_num
    ring
  have h2 : epv (1 / 2) sS 0 = fun ω => 2 + 1 * fh ω.1 := by
    rw [epv_succ (surplusSummable_of_bounded (by norm_num) (by norm_num) sS_bounded),
      epv_sS_one]
    funext ω
    simp only [sS, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    norm_num
    ring
  refine ⟨by rw [pv, pv, h1, h2], ?_⟩
  rw [pv, h1, coin_E_zero]
  norm_num

/-- Cochrane (2023), p. 50 (example economy): baseline present values from date `1` on. -/
theorem pv_sB_succ (t : ℕ) : pv coinSystem (1 / 2) sB (t + 1) = fun ω => 2 * (1 + fh ω.1) := by
  rw [pv, epv_sB_succ]
  exact coin_E_first (by omega) (fun b => 2 * (1 + fh b))

/-- Cochrane (2023), p. 50 (example economy): the baseline present value at date `1`. -/
theorem pv_sB_one : pv coinSystem (1 / 2) sB 1 = fun ω => 2 * (1 + fh ω.1) := pv_sB_succ 0

/-- Cochrane (2023), p. 50 (example economy): stimulus present values from date `2` on. -/
theorem pv_sS_add_two (t : ℕ) :
    pv coinSystem (1 / 2) sS (t + 2) = fun ω => 2 * (1 + fh ω.1) := by
  rw [pv, epv_sS_add_two]
  exact coin_E_first (by omega) (fun b => 2 * (1 + fh b))

/-- Cochrane (2023), p. 50 (example economy): the stimulus raises the date-`1` present value by
the known amount `1`. -/
theorem pv_sS_one : pv coinSystem (1 / 2) sS 1 = pv coinSystem (1 / 2) sB 1 + fun _ => 1 := by
  rw [pv, epv_sS_one, coin_E_first le_rfl (fun b => 3 + 2 * fh b), pv_sB_one]
  funext ω
  simp only [Pi.add_apply]
  ring

/-- Cochrane (2023), p. 50 (example economy): all baseline present values are positive. -/
theorem pv_sB_pos (t : ℕ) (ω : Bool × Bool) : 0 < pv coinSystem (1 / 2) sB t ω := by
  have := fh_nonneg ω.1
  match t with
  | 0 => rw [pv_zero_eq.2]; norm_num
  | t + 1 => rw [pv_sB_succ]; positivity

/-- Cochrane (2023), p. 50 (example economy): all stimulus present values are positive. -/
theorem pv_sS_pos (t : ℕ) (ω : Bool × Bool) : 0 < pv coinSystem (1 / 2) sS t ω := by
  have := fh_nonneg ω.1
  match t with
  | 0 => rw [pv_zero_eq.1, pv_zero_eq.2]; norm_num
  | 1 => rw [pv_sS_one, Pi.add_apply, pv_sB_one]; positivity
  | t + 2 => rw [pv_sS_add_two]; positivity

/-- Cochrane (2023), p. 50 (example economy): all baseline ex-dividend values are positive. -/
theorem pvEx_sB_pos (t : ℕ) (ω : Bool × Bool) : 0 < pvEx coinSystem (1 / 2) sB t ω := by
  have := fh_nonneg ω.1
  have e : (fun ω : Bool × Bool => 2 * (1 + fh ω.1)) = fun ω => 2 + 2 * fh ω.1 := by
    funext ω; ring
  rw [pvEx_eq]
  match t with
  | 0 =>
    rw [pv_sB_one, e, coin_E_zero]
    norm_num
  | t + 1 =>
    rw [pv_sB_succ, coin_E_first (by omega) (fun b => 2 * (1 + fh b))]
    simp only [Pi.smul_apply, smul_eq_mul]
    positivity

/-- Cochrane (2023), p. 50 (example economy): all stimulus ex-dividend values are positive. -/
theorem pvEx_sS_pos (t : ℕ) (ω : Bool × Bool) : 0 < pvEx coinSystem (1 / 2) sS t ω := by
  have := fh_nonneg ω.1
  rw [pvEx_eq]
  match t with
  | 0 =>
    have e : (pv coinSystem (1 / 2) sS 1) = fun ω => 3 + 2 * fh ω.1 := by
      rw [pv_sS_one, pv_sB_one]
      funext ω; simp only [Pi.add_apply]; ring
    rw [e, coin_E_zero]
    norm_num
  | t + 1 =>
    rw [pv_sS_add_two, coin_E_first (by omega) (fun b => 2 * (1 + fh b))]
    simp only [Pi.smul_apply, smul_eq_mul]
    positivity

/-- Cochrane (2023), p. 50 (example economy): the date-`1` fiscal news is
`ΔE_1 ∑ βʲ s_{1+j} = 2 fh − 1 = ±1`. -/
theorem news_sB : innov coinSystem 0 (epv (1 / 2) sB (0 + 1)) = fun ω => 2 * fh ω.1 - 1 := by
  have hr : epv (1 / 2) sB (0 + 1) = fun ω => 2 + 2 * fh ω.1 := by
    rw [epv_sB_succ 0]; funext ω; ring
  rw [innov, hr, coin_E_first (by norm_num : 1 ≤ 0 + 1) (fun b => 2 + 2 * fh b), coin_E_zero]
  funext ω; simp only [Pi.sub_apply]; ring

/-- Cochrane (2023), p. 50 (example economy): the fiscal news is nonzero in every state. -/
theorem news_sB_ne (ω : Bool × Bool) : innov coinSystem 0 (epv (1 / 2) sB (0 + 1)) ω ≠ 0 := by
  rw [news_sB]
  cases hb : ω.1 <;> norm_num [hb, fh]

/-- Cochrane (2023), p. 50 (example economy): the coin-flip expectations have the pull-out
property. -/
theorem coin_pullOut : coinSystem.PullOut := finiteTree_pullOut coinTree

/-- Cochrane (2023), p. 50 (example economy): the baseline economy with a zero interest-rate
target and unit initial debt has an equilibrium. -/
theorem eqm_sB : Equilibrium coinSystem (1 / 2) (fun _ => 1) sB
    (pegB coinSystem (1 / 2) (fun _ => 1) sB fun _ _ => 0)
    (pegP coinSystem (1 / 2) (fun _ => 1) sB fun _ _ => 0) (fun _ _ => 0) :=
  peg_equilibrium coin_pullOut (coinSystem.const 0 1) (fun _ => one_pos)
    (fun t => coinSystem.const t 0) (fun _ _ => by norm_num) pv_sB_pos pvEx_sB_pos

/-- Cochrane (2023), p. 50 (example economy): the stimulus economy with the same target and
initial debt has an equilibrium. -/
theorem eqm_sS : Equilibrium coinSystem (1 / 2) (fun _ => 1) sS
    (pegB coinSystem (1 / 2) (fun _ => 1) sS fun _ _ => 0)
    (pegP coinSystem (1 / 2) (fun _ => 1) sS fun _ _ => 0) (fun _ _ => 0) :=
  peg_equilibrium coin_pullOut (coinSystem.const 0 1) (fun _ => one_pos)
    (fun t => coinSystem.const t 0) (fun _ _ => by norm_num) pv_sS_pos pvEx_sS_pos

/-- Cochrane (2023), p. 50, counterexample to "borrow money, don't drive up interest rates,
spend the money, repay the debt — has no effect at all on current, unexpected, or expected
future inflation" under genuine uncertainty: in the coin-flip economy the stimulus
(`s'_0 = s_0 − 1/2`, `s'_1 = s_1 + 1`, `s'_t = s_t` otherwise, `β = 1/2`) leaves the date-`0`
present value, the date-`0` price level and expected inflation unchanged, but changes the
date-`1` price level in every state. -/
theorem stimulus_not_neutral :
    (sS 0 = fun ω => sB 0 ω - 1 / 2) ∧ (sS 1 = fun ω => sB 1 ω + 1) ∧
      (∀ t, 2 ≤ t → sS t = sB t) ∧
      pv coinSystem (1 / 2) sS 0 = pv coinSystem (1 / 2) sB 0 ∧
      pegP coinSystem (1 / 2) (fun _ => 1) sS (fun _ _ => 0) 0 =
        pegP coinSystem (1 / 2) (fun _ => 1) sB (fun _ _ => 0) 0 ∧
      ∀ ω, pegP coinSystem (1 / 2) (fun _ => 1) sS (fun _ _ => 0) 1 ω ≠
        pegP coinSystem (1 / 2) (fun _ => 1) sB (fun _ _ => 0) 1 ω := by
  have hP0 : pegP coinSystem (1 / 2) (fun _ => 1) sS (fun _ _ => 0) 0 =
      pegP coinSystem (1 / 2) (fun _ => 1) sB (fun _ _ => 0) 0 := by
    change (fun _ => (1 : ℝ)) / pv coinSystem (1 / 2) sS 0 =
      (fun _ => (1 : ℝ)) / pv coinSystem (1 / 2) sB 0
    rw [pv_zero_eq.1]
  refine ⟨funext fun ω => by norm_num [sS, sB], funext fun ω => by (simp [sS, sB]; ring),
    fun t ht => funext fun ω => by
      simp only [sS, sB, show t ≠ 0 by omega, show t ≠ 1 by omega, ↓reduceIte],
    pv_zero_eq.1, hP0, fun ω => ?_⟩
  intro heq
  have hiff := stimulus_price_iff coin_pullOut (by norm_num) eqm_sB eqm_sS hP0
    (coinSystem.const 0 1) pv_sS_one ω (pv_sB_pos 1 ω).ne' (pv_sS_pos 1 ω).ne'
  rcases hiff.mp heq with h0 | h0
  · norm_num at h0
  · exact news_sB_ne ω h0

/-- Cochrane (2023), eq. (2.13), p. 30, under genuine uncertainty: in the coin-flip economy the
date-`1` fiscal news produces nonzero unexpected inflation in every state. -/
theorem coin_unexpected_inflation_ne (ω : Bool × Bool) :
    innov coinSystem 0 ((pegP coinSystem (1 / 2) (fun _ => 1) sB fun _ _ => 0) 0 /
      (pegP coinSystem (1 / 2) (fun _ => 1) sB fun _ _ => 0) (0 + 1)) ω ≠ 0 := by
  have hB : (pegB coinSystem (1 / 2) (fun _ => 1) sB fun _ _ => 0) 0 ω ≠ 0 := by
    rw [debt_eq coin_pullOut eqm_sB 0 ω]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (eqm_sB.2.1 0 ω).ne') (pvEx_sB_pos 0 ω).ne'
  rw [Ne, no_surprise_iff coin_pullOut eqm_sB 0 ω hB]
  exact news_sB_ne ω

end CoinExample

end Cochrane.IntertemporalModel.FiscalMonetary
