/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR6ActiveFiscalTree
import Monetarism.ExpectationsMeasure

/-!
# Active fiscal policy under uncertainty on a probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Ch. 19, §19.5, pp. 448–454 (the
valuation equation (19.35), p. 450; "active fiscal policy can rule out these multiple
equilibria", p. 454). `TidyR6ActiveFiscalTree` proves uniqueness for every `ExpectationSystem`
with full support (finite trees). Here the same statement is proved on a genuine probability
space (`ExpectationsMeasure.MeasExpectationSystem`, Mathlib's `condExp`), with every equilibrium
condition and every conclusion holding almost surely, money an arbitrary positive adapted process
and surpluses an arbitrary integrable process.

## Setting

`Q_t = E_t[βP_t/P_{t+1}]` (`bondPriceM`), the standard bond price `q_t = E_t[βM_t/M_{t+1}]`
(`stdBondPriceM`), the standard price level `TidyR6ActiveFiscalTree.stdPrice`. An equilibrium
(`MeasMonetaryEq`) has positive prices adapted to the filtration, bonds and money chosen at `t`,
the integrability that makes `Q_t` a conditional expectation and real liabilities integrable,
the cash constraint, optimal money and the flow budget almost surely, and the transversality
condition `E[β^Tx_T] → 0`.

## Main results

* `integral_recursion`: `E[x_t] = βE[x_{t+1}] + E[s_t + (1 − Q_t)y/V]`.
* `integral_valuation`: `Σ_{j<T} β^jE[s_j + (1 − Q_j)y/V] → E[x_0]`.
* `std_le_bondPriceM`: `Q_t ≥ q_t` almost surely.
* `meas_price_unique`: if `B_{−1} + M_{−1} ≥ 0` a.s., the standard valuation holds in expectation
  and a.s. either liabilities are positive or `q_0 < 1`, then every equilibrium has
  `P_t = M_tV/y` and `Q_t = q_t` almost surely at every date.
* `meas_coord_of_standard`, `meas_unique_of_standard`: the standard equilibrium, when it exists,
  is the only one (almost surely), with no extra integrability hypotheses.

The counterexamples of `TidyR6ActiveFiscalTree` (`pf_two_equilibria`: the proviso
`B_{−1} + M_{−1} ≥ 0` is needed; `coin_no_standard_equilibrium`: the standard equilibrium can
fail to exist) are finite-tree economies, which are probability spaces
(`ExpectationsMeasure.TreeBridge.treeSystem`).
-/

namespace Cochrane.Monetarism.TidyR6ActiveFiscalMeasure

open MeasureTheory Filter Topology
open Cochrane.Monetarism.ExpectationsMeasure
open Cochrane.Monetarism.TidyR6ActiveFiscalTree (stdPrice wealth)

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), (19.32), p. 450, on a probability space: `Q_t = E_t[βP_t/P_{t+1}]`.
Probability-space version of `TidyR6ActiveFiscalTree.bondPriceS`. -/
noncomputable def bondPriceM (β : ℝ) (P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  S.E t (fun ω => β * P t ω / P (t + 1) ω)

/-- Cochrane (2023), p. 454, on a probability space: the standard bond price
`q_t = E_t[βM_t/M_{t+1}]`.
Probability-space version of `TidyR6ActiveFiscalTree.stdBondPrice`. -/
noncomputable def stdBondPriceM (β : ℝ) (Min : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  S.E t (fun ω => β * Min (t + 1) ω / Min (t + 2) ω)

/-- Cochrane (2023), (19.35), p. 450: the date-`t` flow `s_t + (1 − Q_t)y/V`. -/
noncomputable def flowM (β y V : ℝ) (P s : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  s t ω + (1 - bondPriceM S β P t ω) * y / V

/-- Cochrane (2023), (19.35), p. 450: the standard date-`t` flow `s_t + (1 − q_t)y/V`.
Probability-space version of `TidyR6ActiveFiscalTree.stdFlow`. -/
noncomputable def stdFlowM (β y V : ℝ) (Min s : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  s t ω + (1 - stdBondPriceM S β Min t ω) * y / V

/-- Cochrane (2023), (19.27), p. 449: the flow budget almost surely at every date.
Probability-space version of `TidyR6ActiveFiscalTree.FlowHolds`. -/
def FlowAE (β : ℝ) (P Bin Min s : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ∀ᵐ ω ∂S.μ, Bin t ω + Min t ω =
    bondPriceM S β P t ω * Bin (t + 1) ω + Min (t + 1) ω + P t ω * s t ω

/-- Cochrane (2023), (19.33), p. 450: optimal money almost surely, `Q_t ≤ 1` and
`Q_t < 1 ⇒ M_t = P_ty/V`. -/
def MoneyAE (β y V : ℝ) (P Min : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ∀ᵐ ω ∂S.μ, bondPriceM S β P t ω ≤ 1 ∧
    (bondPriceM S β P t ω < 1 → Min (t + 1) ω = P t ω * y / V)

variable (β y V : ℝ) (P Bin Min s : ℕ → Ω → ℝ)

/-- Cochrane (2023), §19.5, pp. 448–450, on a probability space: an equilibrium of the
cash-in-advance model with constant endowment. Positive prices adapted to the filtration, bonds
and money chosen at `t`; `β/P_{t+1}` and `βP_t/P_{t+1}` integrable (so `Q_t` is a conditional
expectation) and real liabilities integrable; the cash constraint, optimal money and the flow
budget almost surely; and the transversality condition `E[β^Tx_T] → 0`. -/
structure MeasMonetaryEq where
  pos : ∀ t ω, 0 < P t ω
  measP : ∀ t, StronglyMeasurable[S.𝓕 t] (P t)
  measB : ∀ t, StronglyMeasurable[S.𝓕 t] (Bin (t + 1))
  measM : ∀ t, StronglyMeasurable[S.𝓕 t] (Min (t + 1))
  intR : ∀ t, Integrable (fun ω => β / P (t + 1) ω) S.μ
  intQ : ∀ t, Integrable (fun ω => β * P t ω / P (t + 1) ω) S.μ
  intW : ∀ t, Integrable (wealth P Bin Min t) S.μ
  cia : ∀ t, ∀ᵐ ω ∂S.μ, P t ω * y / V ≤ Min (t + 1) ω
  money : MoneyAE S β y V P Min
  flow : FlowAE S β P Bin Min s
  tvc : Tendsto (fun T => ∫ ω, β ^ T * wealth P Bin Min T ω ∂S.μ) atTop (𝓝 0)

variable {S β y V P Bin Min s}

/-- Cochrane (2023), (19.32), p. 450: `Q_t = P_tE_t[β/P_{t+1}]` almost surely (pull-out).
Probability-space version of `TidyR6ActiveFiscalTree.bondPriceS_eq`. -/
theorem bondPriceM_ae (h : MeasMonetaryEq S β y V P Bin Min s) (t : ℕ) :
    bondPriceM S β P t =ᵐ[S.μ] P t * S.E t (fun ω => β / P (t + 1) ω) := by
  have e : (fun ω => β * P t ω / P (t + 1) ω) = P t * (fun ω => β / P (t + 1) ω) := by
    funext ω; simp only [Pi.mul_apply]; ring
  unfold bondPriceM
  rw [e]
  exact condExp_mul_of_stronglyMeasurable_left (h.measP t) (by rw [← e]; exact h.intQ t)
    (h.intR t)

/-- Cochrane (2023), p. 454: `q_t = M_tE_t[β/M_{t+1}]` almost surely (pull-out).
Probability-space version of `TidyR6ActiveFiscalTree.stdBondPrice_eq`. -/
theorem stdBondPriceM_ae {t : ℕ} (hM : ∀ t, StronglyMeasurable[S.𝓕 t] (Min (t + 1)))
    (hS : Integrable (fun ω => β / Min (t + 2) ω) S.μ)
    (hq : Integrable (fun ω => β * Min (t + 1) ω / Min (t + 2) ω) S.μ) :
    stdBondPriceM S β Min t =ᵐ[S.μ] Min (t + 1) * S.E t (fun ω => β / Min (t + 2) ω) := by
  have e : (fun ω => β * Min (t + 1) ω / Min (t + 2) ω) =
      Min (t + 1) * (fun ω => β / Min (t + 2) ω) := by
    funext ω; simp only [Pi.mul_apply]; ring
  unfold stdBondPriceM
  rw [e]
  exact condExp_mul_of_stronglyMeasurable_left (hM t) (by rw [← e]; exact hq) hS

/-- Cochrane (2023), (19.35), p. 450: the flow `s_t + (1 − Q_t)y/V` is integrable when the
surplus is. -/
theorem flowM_integrable {t : ℕ} (hs : Integrable (s t) S.μ) :
    Integrable (flowM S β y V P s t) S.μ :=
  hs.add ((((integrable_const (1 : ℝ)).sub
    (S.integrable_E t (fun ω => β * P t ω / P (t + 1) ω))).mul_const y).div_const V)

/-- Cochrane (2023), (19.35), p. 450: the standard flow `s_t + (1 − q_t)y/V` is integrable when
the surplus is. -/
theorem stdFlowM_integrable {t : ℕ} (hs : Integrable (s t) S.μ) :
    Integrable (stdFlowM S β y V Min s t) S.μ :=
  hs.add ((((integrable_const (1 : ℝ)).sub
    (S.integrable_E t (fun ω => β * Min (t + 1) ω / Min (t + 2) ω))).mul_const y).div_const V)

/-- **Cochrane (2023), (19.27)–(19.35), pp. 449–450, in expectation: the wealth recursion.** In
an equilibrium with integrable surpluses, `E[x_t] = βE[x_{t+1}] + E[s_t + (1 − Q_t)y/V]`.
Probability-space version of `TidyR6ActiveFiscalTree.wealth_recursion`. -/
theorem integral_recursion (hV : 0 < V) (h : MeasMonetaryEq S β y V P Bin Min s)
    (hs : ∀ t, Integrable (s t) S.μ) (t : ℕ) :
    ∫ ω, wealth P Bin Min t ω ∂S.μ =
      β * ∫ ω, wealth P Bin Min (t + 1) ω ∂S.μ + ∫ ω, flowM S β y V P s t ω ∂S.μ := by
  set K : Ω → ℝ := fun ω => Bin (t + 1) ω + Min (t + 1) ω with hK
  set R : Ω → ℝ := fun ω => β / P (t + 1) ω with hR
  have hKm : StronglyMeasurable[S.𝓕 t] K := (h.measB t).add (h.measM t)
  have hKR : K * R = fun ω => β * wealth P Bin Min (t + 1) ω := by
    funext ω
    have := (h.pos (t + 1) ω).ne'
    simp only [Pi.mul_apply, hK, hR, wealth]
    field_simp
  have hKRi : Integrable (K * R) S.μ := by rw [hKR]; exact (h.intW (t + 1)).const_mul β
  have h1 : S.E t (K * R) =ᵐ[S.μ] K * S.E t R :=
    condExp_mul_of_stronglyMeasurable_left hKm hKRi (h.intR t)
  have h2 := bondPriceM_ae h t
  have hae : wealth P Bin Min t =ᵐ[S.μ] fun ω => S.E t (K * R) ω + flowM S β y V P s t ω := by
    filter_upwards [h1, h2, h.flow t, h.money t] with ω e1 e2 hf hm
    simp only [Pi.mul_apply] at e1 e2
    have hP := (h.pos t ω).ne'
    have hsg : (1 - bondPriceM S β P t ω) * Min (t + 1) ω =
        (1 - bondPriceM S β P t ω) * (P t ω * y / V) := by
      rcases lt_or_eq_of_le hm.1 with hQ | hQ
      · rw [hm.2 hQ]
      · rw [hQ, sub_self, zero_mul, zero_mul]
    have hER : S.E t R ω = bondPriceM S β P t ω / P t ω := by rw [e2, hR]; field_simp
    simp only [wealth, flowM]
    rw [e1, hER, hf]
    have e3 : bondPriceM S β P t ω * Bin (t + 1) ω + Min (t + 1) ω + P t ω * s t ω =
        (Bin (t + 1) ω + Min (t + 1) ω) * bondPriceM S β P t ω +
          (1 - bondPriceM S β P t ω) * Min (t + 1) ω + P t ω * s t ω := by ring
    rw [e3, hsg]
    have := hV.ne'
    simp only [hK]
    field_simp
    ring
  rw [integral_congr_ae hae]
  rw [integral_add (S.integrable_E t _) (flowM_integrable (hs t))]
  rw [S.integral_E, hKR, integral_const_mul]

/-- **Cochrane (2023), (19.35), p. 450, in expectation: the valuation equation as a limit.** In
an equilibrium with integrable surpluses, `Σ_{j<T} β^jE[s_j + (1 − Q_j)y/V] → E[x_0]`.
Probability-space version of `TidyR6ActiveFiscalTree.valuation_limit`. -/
theorem integral_valuation (hV : 0 < V) (h : MeasMonetaryEq S β y V P Bin Min s)
    (hs : ∀ t, Integrable (s t) S.μ) :
    Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * ∫ ω, flowM S β y V P s j ω ∂S.μ) atTop
      (𝓝 (∫ ω, wealth P Bin Min 0 ω ∂S.μ)) := by
  have hpart : ∀ T, ∑ j ∈ Finset.range T, β ^ j * ∫ ω, flowM S β y V P s j ω ∂S.μ =
      ∫ ω, wealth P Bin Min 0 ω ∂S.μ - ∫ ω, β ^ T * wealth P Bin Min T ω ∂S.μ := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [Finset.sum_range_succ, ih, integral_const_mul, integral_const_mul,
        integral_recursion hV h hs T, pow_succ]
      ring
  simp_rw [hpart]
  simpa using h.tvc.const_sub (∫ ω, wealth P Bin Min 0 ω ∂S.μ)

/-- Cochrane (2023), (19.24), p. 449, one period ahead, almost surely: `M_{t+1} > 0` and
`(y/V)·β/M_{t+1} ≤ β/P_{t+1}` (`β ≥ 0`).
Probability-space version of `TidyR6ActiveFiscalTree.cash_bound`. -/
theorem cash_bound_ae (hy : 0 < y) (hV : 0 < V) (h : MeasMonetaryEq S β y V P Bin Min s)
    (hβ : 0 ≤ β) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, 0 < Min (t + 2) ω ∧ (y / V) * (β / Min (t + 2) ω) ≤ β / P (t + 1) ω := by
  filter_upwards [h.cia (t + 1)] with ω hc
  have hP1 := h.pos (t + 1) ω
  have hpos : 0 < P (t + 1) ω * y / V := by positivity
  have hM2 : 0 < Min (t + 1 + 1) ω := lt_of_lt_of_le hpos hc
  refine ⟨hM2, ?_⟩
  rw [show (y / V) * (β / Min (t + 2) ω) = β / (Min (t + 1 + 1) ω * V / y) by
    field_simp]
  refine div_le_div_of_nonneg_left hβ hP1 ?_
  rw [le_div_iff₀ hy]
  calc P (t + 1) ω * y = P (t + 1) ω * y / V * V := by field_simp
    _ ≤ Min (t + 1 + 1) ω * V := mul_le_mul_of_nonneg_right hc hV.le

/-- Cochrane (2023), p. 454, almost surely: **every equilibrium bond price is at least the
standard one**, `Q_t ≥ q_t`, given `q_t ≤ 1` a.s. and the integrability of `β/M_{t+1}` and
`βM_t/M_{t+1}`.
Probability-space version of `TidyR6ActiveFiscalTree.std_le_bondPrice`. -/
theorem std_le_bondPriceM (hy : 0 < y) (hV : 0 < V) (h : MeasMonetaryEq S β y V P Bin Min s)
    (hβ : 0 ≤ β) (t : ℕ) (hS : Integrable (fun ω => β / Min (t + 2) ω) S.μ)
    (hq : Integrable (fun ω => β * Min (t + 1) ω / Min (t + 2) ω) S.μ)
    (hq1 : ∀ᵐ ω ∂S.μ, stdBondPriceM S β Min t ω ≤ 1) :
    ∀ᵐ ω ∂S.μ, stdBondPriceM S β Min t ω ≤ bondPriceM S β P t ω := by
  have h2 := bondPriceM_ae h t
  have h3 := stdBondPriceM_ae h.measM hS hq
  have hle : (fun ω => (y / V) * (β / Min (t + 2) ω)) ≤ᵐ[S.μ] fun ω => β / P (t + 1) ω := by
    filter_upwards [cash_bound_ae hy hV h hβ t] with ω hω using hω.2
  have hmono := S.E_mono (hS.const_mul (y / V)) (h.intR t) hle t
  have hsm := S.E_smul (y / V) (fun ω => β / Min (t + 2) ω) t
  have e : (y / V) • (fun ω => β / Min (t + 2) ω) = fun ω => (y / V) * (β / Min (t + 2) ω) := by
    funext ω; simp
  rw [e] at hsm
  filter_upwards [h2, h3, hmono, hsm, h.money t, hq1, h.cia t] with ω e2 e3 hmo hsmω hm hq1ω hc
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at e2 e3 hsmω
  rcases lt_or_eq_of_le hm.1 with hlt | heq
  · have hb := hm.2 hlt
    have hPt : P t ω = Min (t + 1) ω * V / y := by rw [hb]; field_simp
    rw [e2, e3, hPt]
    rw [hsmω] at hmo
    have hP := h.pos t ω
    have hM1 : 0 < Min (t + 1) ω := by
      have : 0 < P t ω * y / V := by positivity
      linarith
    have hMV : 0 ≤ Min (t + 1) ω * V / y := by positivity
    calc Min (t + 1) ω * S.E t (fun ω => β / Min (t + 2) ω) ω
        = Min (t + 1) ω * V / y * (y / V * S.E t (fun ω => β / Min (t + 2) ω) ω) := by
          field_simp
      _ ≤ Min (t + 1) ω * V / y * S.E t (fun ω => β / P (t + 1) ω) ω :=
          mul_le_mul_of_nonneg_left hmo hMV
  · rw [heq]; exact hq1ω

/-- **Cochrane (2023), pp. 453–454 on a probability space: active fiscal policy determines the
price level almost surely.** Let `β > 0`, `y, V > 0`, surpluses integrable, `β/M_{t+1}` and
`βM_t/M_{t+1}` integrable, `q_t ≤ 1` a.s., `B_{−1} + M_{−1} ≥ 0` a.s., the standard valuation in
expectation `Σ_jβ^jE[s_j + (1 − q_j)y/V] = E[(B_{−1} + M_{−1})y/(VM_0)]` (as a limit of partial
sums), and a.s. `B_{−1} + M_{−1} > 0` or `q_0 < 1`. Then every equilibrium has `P_t = M_tV/y`
and `Q_t = q_t` almost surely at every date.
Probability-space version of `TidyR6ActiveFiscalTree.stoch_price_unique`. -/
theorem meas_price_unique (hβ : 0 < β) (hy : 0 < y) (hV : 0 < V)
    (h : MeasMonetaryEq S β y V P Bin Min s) (hs : ∀ t, Integrable (s t) S.μ)
    (hS : ∀ t, Integrable (fun ω => β / Min (t + 2) ω) S.μ)
    (hq : ∀ t, Integrable (fun ω => β * Min (t + 1) ω / Min (t + 2) ω) S.μ)
    (hq1 : ∀ t, ∀ᵐ ω ∂S.μ, stdBondPriceM S β Min t ω ≤ 1)
    (hW : ∀ᵐ ω ∂S.μ, 0 ≤ Bin 0 ω + Min 0 ω)
    (hcoord : Tendsto (fun T => ∑ j ∈ Finset.range T,
      β ^ j * ∫ ω, stdFlowM S β y V Min s j ω ∂S.μ) atTop
      (𝓝 (∫ ω, (Bin 0 ω + Min 0 ω) * y / (V * Min 1 ω) ∂S.μ)))
    (hpin : ∀ᵐ ω ∂S.μ, 0 < Bin 0 ω + Min 0 ω ∨ stdBondPriceM S β Min 0 ω < 1) :
    (∀ t, P t =ᵐ[S.μ] stdPrice y V Min t) ∧
      ∀ t, bondPriceM S β P t =ᵐ[S.μ] stdBondPriceM S β Min t := by
  have hGH : ∀ j, ∀ᵐ ω ∂S.μ, flowM S β y V P s j ω ≤ stdFlowM S β y V Min s j ω := by
    intro j
    filter_upwards [std_le_bondPriceM hy hV h hβ.le j (hS j) (hq j) (hq1 j)] with ω hω
    simp only [flowM, stdFlowM]
    have hyV : 0 ≤ y / V := by positivity
    rw [mul_div_assoc, mul_div_assoc]
    nlinarith
  set c0 : Ω → ℝ := fun ω => (Bin 0 ω + Min 0 ω) * y / (V * Min 1 ω) with hc0
  -- `c0 ≤ x_0` almost surely, and `c0` is integrable
  have hM1 : ∀ᵐ ω ∂S.μ, 0 < Min 1 ω := by
    filter_upwards [h.cia 0] with ω hc
    have := h.pos 0 ω
    have : 0 < P 0 ω * y / V := by positivity
    simpa using lt_of_lt_of_le this hc
  have hcx : ∀ᵐ ω ∂S.μ, c0 ω ≤ wealth P Bin Min 0 ω := by
    filter_upwards [h.cia 0, hW, hM1] with ω hc hw hm
    have hP0 := h.pos 0 ω
    simp only [hc0, wealth]
    rw [div_le_div_iff₀ (by positivity) hP0]
    have : P 0 ω * y ≤ V * Min 1 ω := by
      have e : P 0 ω * y = P 0 ω * y / V * V := by field_simp
      rw [e, mul_comm V]
      simpa using mul_le_mul_of_nonneg_right hc hV.le
    nlinarith
  have hc0i : Integrable c0 S.μ := by
    have hr : AEStronglyMeasurable (fun ω => P 0 ω * y / (V * Min 1 ω)) S.μ := by
      have h1 : StronglyMeasurable (P 0) := (h.measP 0).mono (S.𝓕.le 0)
      have h2 : StronglyMeasurable (Min 1) := (h.measM 0).mono (S.𝓕.le 0)
      exact (((h1.mul_const y).div (h2.const_mul V))).aestronglyMeasurable
    have hb : ∀ᵐ ω ∂S.μ, ‖P 0 ω * y / (V * Min 1 ω)‖ ≤ 1 := by
      filter_upwards [h.cia 0, hM1] with ω hc hm
      have hP0 := h.pos 0 ω
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_one (by positivity)]
      have e : P 0 ω * y = P 0 ω * y / V * V := by field_simp
      rw [e, mul_comm V]
      simpa using mul_le_mul_of_nonneg_right hc hV.le
    refine ((h.intW 0).bdd_mul hr hb).congr ?_
    filter_upwards [hM1] with ω hm
    have hP0 := (h.pos 0 ω).ne'
    simp only [hc0, wealth]
    field_simp
  -- the gaps
  set d : ℕ → ℝ := fun j =>
    β ^ j * ∫ ω, (stdFlowM S β y V Min s j ω - flowM S β y V P s j ω) ∂S.μ with hd
  have hdnn : ∀ j, 0 ≤ d j := fun j => mul_nonneg (pow_nonneg hβ.le j)
    (integral_nonneg_of_ae (by
      filter_upwards [hGH j] with ω hω; simp only [Pi.zero_apply]; linarith))
  have hdsum : ∀ T, ∑ j ∈ Finset.range T, d j =
      ∑ j ∈ Finset.range T, β ^ j * ∫ ω, stdFlowM S β y V Min s j ω ∂S.μ -
        ∑ j ∈ Finset.range T, β ^ j * ∫ ω, flowM S β y V P s j ω ∂S.μ := by
    intro T
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hd]
    rw [integral_sub (stdFlowM_integrable (hs j)) (flowM_integrable (hs j))]
    ring
  have hHS : HasSum d (∫ ω, c0 ω ∂S.μ - ∫ ω, wealth P Bin Min 0 ω ∂S.μ) := by
    refine (hasSum_iff_tendsto_nat_of_nonneg hdnn _).2 ?_
    simp_rw [hdsum]
    exact hcoord.sub (integral_valuation hV h hs)
  have hint_le : ∫ ω, c0 ω ∂S.μ ≤ ∫ ω, wealth P Bin Min 0 ω ∂S.μ :=
    integral_mono_ae hc0i (h.intW 0) hcx
  have hd0 : ∀ j, d j = 0 := fun j => le_antisymm
    (by have := le_hasSum hHS j (fun i _ => hdnn i); linarith) (hdnn j)
  have hsum0 := hHS.nonneg hdnn
  -- bond prices almost surely standard
  have hQq : ∀ t, bondPriceM S β P t =ᵐ[S.μ] stdBondPriceM S β Min t := by
    intro t
    have hz : ∫ ω, (stdFlowM S β y V Min s t ω - flowM S β y V P s t ω) ∂S.μ = 0 := by
      have := hd0 t
      simp only [hd] at this
      exact (mul_eq_zero.mp this).resolve_left (pow_pos hβ t).ne'
    have hae := (integral_eq_zero_iff_of_nonneg_ae
      (by filter_upwards [hGH t] with ω hω; simp only [Pi.zero_apply, Pi.sub_apply]; linarith)
      ((stdFlowM_integrable (hs t)).sub (flowM_integrable (hs t)))).1 hz
    filter_upwards [hae] with ω hω
    simp only [Pi.zero_apply, Pi.sub_apply, flowM, stdFlowM] at hω
    have hk : (y / V) * (bondPriceM S β P t ω - stdBondPriceM S β Min t ω) = 0 := by
      rw [← hω]; ring
    have := (mul_eq_zero.mp hk).resolve_left (by positivity)
    linarith
  -- `x_0 = c0` almost surely
  have hx0 : wealth P Bin Min 0 =ᵐ[S.μ] c0 := by
    have hz : ∫ ω, (wealth P Bin Min 0 ω - c0 ω) ∂S.μ = 0 := by
      rw [integral_sub (h.intW 0) hc0i]; linarith
    have hae := (integral_eq_zero_iff_of_nonneg_ae
      (by filter_upwards [hcx] with ω hω; simp only [Pi.zero_apply, Pi.sub_apply]; linarith)
      ((h.intW 0).sub hc0i)).1 hz
    filter_upwards [hae] with ω hω
    simp only [Pi.sub_apply, Pi.zero_apply] at hω
    linarith
  -- the initial price level
  have hP0 : P 0 =ᵐ[S.μ] stdPrice y V Min 0 := by
    filter_upwards [hx0, hpin, hQq 0, h.money 0, hM1] with ω hx hp hQ hm hm1
    have hP := h.pos 0 ω
    simp only [stdPrice, zero_add]
    rcases hp with hpos | hq0
    · simp only [wealth, hc0] at hx
      rw [div_eq_div_iff hP.ne' (by positivity)] at hx
      have h2 : (Bin 0 ω + Min 0 ω) * (V * Min 1 ω) =
          (Bin 0 ω + Min 0 ω) * (y * P 0 ω) := by linarith
      have h3 := mul_left_cancel₀ hpos.ne' h2
      field_simp
      linarith
    · have hb := hm.2 (by rw [hQ]; exact hq0)
      simp only [zero_add] at hb
      rw [hb]
      field_simp
  -- forward induction
  have hPt : ∀ t, P t =ᵐ[S.μ] stdPrice y V Min t := by
    intro t
    induction t with
    | zero => exact hP0
    | succ t ih =>
      set R : Ω → ℝ := fun ω => β / P (t + 1) ω with hR
      set Sf : Ω → ℝ := fun ω => (y / V) * (β / Min (t + 2) ω) with hSf
      have hSfi : Integrable Sf S.μ := (hS t).const_mul (y / V)
      have hsm := S.E_smul (y / V) (fun ω => β / Min (t + 2) ω) t
      have e : (y / V) • (fun ω => β / Min (t + 2) ω) = Sf := by funext ω; simp [hSf]
      rw [e] at hsm
      have hE : S.E t (R - Sf) =ᵐ[S.μ] 0 := by
        have hsub := S.E_sub (h.intR t) hSfi t
        filter_upwards [hsub, hsm, bondPriceM_ae h t, stdBondPriceM_ae h.measM (hS t) (hq t),
          hQq t, ih, h.cia t] with ω e1 e2 e3 e4 e5 e6 hc
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.zero_apply,
          stdPrice] at e1 e2 e3 e4 e6 ⊢
        rw [e1, e2]
        rw [e5, e4, e6] at e3
        have hP := h.pos t ω
        have hM1 : 0 < Min (t + 1) ω := by
          have : 0 < P t ω * y / V := by positivity
          linarith
        have h4 : Min (t + 1) ω * (V / y * S.E t R ω - S.E t (fun ω => β / Min (t + 2) ω) ω)
            = 0 := by
          rw [hR]; linear_combination (-1 : ℝ) * e3
        have h5 := (mul_eq_zero.mp h4).resolve_left hM1.ne'
        field_simp at h5
        field_simp
        linarith
      have hZ : 0 ≤ᵐ[S.μ] R - Sf := by
        filter_upwards [cash_bound_ae hy hV h hβ.le t] with ω hω
        simp only [Pi.zero_apply, Pi.sub_apply, hR, hSf]
        linarith [hω.2]
      have hint : ∫ ω, (R - Sf) ω ∂S.μ = 0 := by
        rw [← S.integral_E t, integral_congr_ae hE]
        simp
      have hae := (integral_eq_zero_iff_of_nonneg_ae hZ ((h.intR t).sub hSfi)).1 hint
      filter_upwards [hae, cash_bound_ae hy hV h hβ.le t] with ω hω hb
      simp only [Pi.sub_apply, Pi.zero_apply, hR, hSf] at hω
      have hP1 := h.pos (t + 1) ω
      have hM2 := hb.1
      change P (t + 1) ω = Min (t + 1 + 1) ω * V / y
      have hz' : β / P (t + 1) ω = y / V * (β / Min (t + 1 + 1) ω) := by linarith
      field_simp at hz'
      rw [eq_div_iff hy.ne']
      linarith
  exact ⟨hPt, hQq⟩

/-- Cochrane (2023), p. 454: along the standard path the bond price is `q_t`.
Probability-space version of `TidyR6ActiveFiscalTree.bondPriceS_std`. -/
theorem bondPriceM_std (hy : 0 < y) (hV : 0 < V) (hM : ∀ t ω, 0 < Min (t + 1) ω) (t : ℕ) :
    bondPriceM S β (stdPrice y V Min) t = stdBondPriceM S β Min t := by
  unfold bondPriceM stdBondPriceM
  congr 1
  funext ω
  have := (hM (t + 1) ω).ne'
  have := hy.ne'
  have := hV.ne'
  change β * (Min (t + 1) ω * V / y) / (Min (t + 2) ω * V / y) =
    β * Min (t + 1) ω / Min (t + 2) ω
  field_simp

/-- Cochrane (2023), p. 454: positive standard prices mean positive money. -/
theorem money_pos_of_std (hy : 0 < y) (hV : 0 < V) {Bs : ℕ → Ω → ℝ}
    (h : MeasMonetaryEq S β y V (stdPrice y V Min) Bs Min s) (t : ℕ) (ω : Ω) :
    0 < Min (t + 1) ω := by
  have := h.pos t ω
  simp only [stdPrice] at this
  have h2 : Min (t + 1) ω * V / y * (y / V) = Min (t + 1) ω := by field_simp
  rw [← h2]
  positivity

/-- Cochrane (2023), (19.35), p. 450: **the standard valuation holds in expectation whenever the
standard equilibrium exists.**
Probability-space version of `TidyR6ActiveFiscalTree.coord_of_standard`. -/
theorem meas_coord_of_standard (hy : 0 < y) (hV : 0 < V) {Bs : ℕ → Ω → ℝ}
    (h : MeasMonetaryEq S β y V (stdPrice y V Min) Bs Min s) (hs : ∀ t, Integrable (s t) S.μ) :
    Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * ∫ ω, stdFlowM S β y V Min s j ω ∂S.μ)
      atTop (𝓝 (∫ ω, (Bs 0 ω + Min 0 ω) * y / (V * Min 1 ω) ∂S.μ)) := by
  have hQ := bondPriceM_std (S := S) (β := β) hy hV (money_pos_of_std hy hV h)
  have hf : ∀ j, flowM S β y V (stdPrice y V Min) s j = stdFlowM S β y V Min s j := by
    intro j; funext ω; simp only [flowM, stdFlowM, hQ j]
  have hval := integral_valuation hV h hs
  simp_rw [hf] at hval
  have e : wealth (stdPrice y V Min) Bs Min 0 =
      fun ω => (Bs 0 ω + Min 0 ω) * y / (V * Min 1 ω) := by
    funext ω
    have := money_pos_of_std hy hV h 0 ω
    simp only [zero_add] at this
    simp only [wealth, stdPrice, zero_add]
    have := hy.ne'
    have := hV.ne'
    field_simp
  rw [e] at hval
  exact hval

/-- **Cochrane (2023), pp. 453–454 on a probability space, existence form: if the standard
equilibrium exists, every equilibrium has its price level almost surely.** With `β > 0`,
`y, V > 0`, integrable surpluses, the same money, surpluses and initial bonds as a standard
equilibrium, `B_{−1} + M_{−1} ≥ 0` a.s. and a.s. `B_{−1} + M_{−1} > 0` or `q_0 < 1`:
`P_t = M_tV/y` and `Q_t = q_t` almost surely at every date.
Probability-space version of `TidyR6ActiveFiscalTree.unique_of_standard`. -/
theorem meas_unique_of_standard (hβ : 0 < β) (hy : 0 < y) (hV : 0 < V) {Bs : ℕ → Ω → ℝ}
    (h : MeasMonetaryEq S β y V P Bin Min s)
    (hstd : MeasMonetaryEq S β y V (stdPrice y V Min) Bs Min s)
    (hs : ∀ t, Integrable (s t) S.μ) (hB0 : Bin 0 = Bs 0) (hW : ∀ᵐ ω ∂S.μ, 0 ≤ Bin 0 ω + Min 0 ω)
    (hpin : ∀ᵐ ω ∂S.μ, 0 < Bin 0 ω + Min 0 ω ∨ stdBondPriceM S β Min 0 ω < 1) :
    (∀ t, P t =ᵐ[S.μ] stdPrice y V Min t) ∧
      ∀ t, bondPriceM S β P t =ᵐ[S.μ] stdBondPriceM S β Min t := by
  have hQs := bondPriceM_std (S := S) (β := β) hy hV (money_pos_of_std hy hV hstd)
  have hq1 : ∀ t, ∀ᵐ ω ∂S.μ, stdBondPriceM S β Min t ω ≤ 1 := fun t => by
    filter_upwards [hstd.money t] with ω hω
    rw [← hQs t]; exact hω.1
  have hS : ∀ t, Integrable (fun ω => β / Min (t + 2) ω) S.μ := by
    intro t
    refine ((hstd.intR t).const_mul (V / y)).congr (ae_of_all _ fun ω => ?_)
    have := (money_pos_of_std hy hV hstd (t + 1) ω).ne'
    have := hy.ne'
    have := hV.ne'
    change V / y * (β / (Min (t + 1 + 1) ω * V / y)) = β / Min (t + 2) ω
    field_simp
  have hq : ∀ t, Integrable (fun ω => β * Min (t + 1) ω / Min (t + 2) ω) S.μ := by
    intro t
    refine (hstd.intQ t).congr (ae_of_all _ fun ω => ?_)
    have := (money_pos_of_std hy hV hstd (t + 1) ω).ne'
    have := hy.ne'
    have := hV.ne'
    change β * (Min (t + 1) ω * V / y) / (Min (t + 1 + 1) ω * V / y) =
      β * Min (t + 1) ω / Min (t + 2) ω
    field_simp
  have hcoord := meas_coord_of_standard hy hV hstd hs
  rw [← hB0] at hcoord
  exact meas_price_unique hβ hy hV h hs hS hq hq1 hW hcoord hpin

end Cochrane.Monetarism.TidyR6ActiveFiscalMeasure
