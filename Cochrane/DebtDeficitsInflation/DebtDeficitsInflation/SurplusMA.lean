/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DebtDeficitsInflation.LinearizedIdentities

/-!
# The surplus process and unexpected inflation

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.2–§4.2.4, eqs.
(4.1)–(4.10), pp. 86–93.

The "simple model" of §4.2 is the linearised flow identity with one-period debt
(`rⁿ_{t+1} = i_t` known at `t`), a constant expected real return and no growth
(`SimpleModel`), together with the innovation terminal condition (`InnovTVC`, automatic for a
bounded value of debt and `|ρ| < 1`). The surplus has a moving-average representation
`s_t = a(L)ε_t` (4.1).

## Main results

* (4.2) Hansen–Roberds–Sargent: `innov_infl_eq_tsum`, `innov_infl_eq`
  (`Δ_{t+1}π_{t+1} = −∑ρʲΔ_{t+1}s̃_{t+1+j} = −a(ρ)ε_{t+1}`), for every `|ρ| ≤ 1`; (4.4)
  `innov_infl_eq_surplus`; volatility and correlation, exactly: `condVar_innov_infl`,
  `condCov_innov_infl`, `no_correlation_of_gen_zero`; the 11% example
  `ar1_volatility_example`.
* (4.3) the AR(1): `gen_ar1`, `one_lt_gen_ar1_iff` (`a(ρ) > 1` iff `η > 0`; survey E2:
  the book's "a number greater than one" needs `η > 0`, `gen_ar1_lt_one_example`);
  `exists_neg_coeff_of_gen_lt_one` (`a(ρ) < 1` forces a negative coefficient).
* The MA(1): `isMA_ma1`, `gen_ma1`, `gen_ma1_inv`, `gen_ma1_zero`, `one_lt_gen_ma1`,
  `gen_ma1_mem_Ioo`, `innov_ma1_now`, `innov_ma1_next`; survey E3: the signs of the p. 88 example
  (`ma1_printed_signs_false`).
* §4.2.2: (4.5) `value_ar1`, (4.6) `value_recursion`, (4.7) `rho_innov_value`,
  `rho_innov_value_eq`, `innov_value_pos_iff`, `innov_value_full_repayment`,
  `innov_value_eq_series`.
* §4.2.3 exact model (Section 2.7 valuation with a constant real rate): (4.8)
  `exact_innov_flow`, (4.9) `exact_innov_flow_pv`, (4.10) `exact_innov_flow_ma`; revenue from
  bond sales `revenue_innov`; financing cases `financing_by_debt`, `financing_by_inflation`,
  `financing_superinflation`; `exact_flow_of_valuation`.
* p. 87 exact line (survey E1): `exact_innov_line` (`(B_t/P_t)Δ(P_t/P_{t+1}) =
  Δ∑βʲs_{t+1+j} = a(β)ε_{t+1}`), the printed sum over `s_{t+j}` gives `β a(β) ε_{t+1}`
  (`printed_exact_line`, `printed_exact_line_iff`, counterexample
  `printed_exact_line_counterexample`).
* §4.2.4: `innov_return`, `innov_return_split`, `innov_return_riskfree`,
  `abs_innov_return_ge`; the one-step stochastic-discount-factor valuation of p. 93,
  `sdf_one_step`.
-/

namespace Cochrane.DebtDeficitsInflation.SurplusMA

open Filter Topology
open Cochrane.DebtDeficitsInflation.Innovations
open Cochrane.DebtDeficitsInflation.LinearizedIdentities

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The simple model -/

/-- Cochrane (2023), §4.2, p. 87 ("one-period debt, a constant real rate, and flexible
prices"): the linearised flow identity (3.17) with no growth, `r = rⁿ − π`, `v` known at each
date, one-period debt (`rⁿ_{t+1} = i_t` known at `t`) and a constant expected real return
`E_t r_{t+1} = c`. -/
def SimpleModel (ρ c : ℝ) (v r rn infl s : ℕ → Ω → ℝ) : Prop :=
  Flow ρ v r (fun _ => 0) s ∧ (∀ t, r t = rn t - infl t) ∧ 𝔼.Adapted v ∧
    (∀ t, 𝔼.E t (rn (t + 1)) = rn (t + 1)) ∧ ConstExpReturn 𝔼 r c

/-- Cochrane (2023), eq. (3.19), p. 64 (the terminal condition, in innovations):
`ρᵀ Δ_{t+1} v_{t+T} → 0` at every date and state. -/
def InnovTVC (ρ : ℝ) (v : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + T)) ω) atTop (𝓝 0)

/-- Cochrane (2023), p. 64 ("the assumption or observation that debt/GDP is a stationary
process is enough"): a bounded value of debt satisfies the innovation terminal condition for
`|ρ| < 1`. -/
theorem innovTVC_of_bounded {ρ : ℝ} (hρ : |ρ| < 1) {v : ℕ → Ω → ℝ} (hv : BoundedProc v) :
    InnovTVC 𝔼 ρ v := by
  obtain ⟨M, hM⟩ := hv
  exact fun t ω => tvc_innov_of_bounded 𝔼 hρ hM t t ω

/-! ### (4.2): unexpected inflation is `−a(ρ)ε` -/

/-- Cochrane (2023), eq. (4.2), p. 87, first equality: in the simple model,
`Δ_{t+1}π_{t+1} = −∑_{j ≥ 0} ρʲ Δ_{t+1} s̃_{t+1+j}`, valid for every `|ρ| ≤ 1`. -/
theorem innov_infl_eq_tsum {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (hρ : |ρ| ≤ 1) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (infl (t + 1)) ω = -∑' j, ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω := by
  obtain ⟨hf, hr, hv, hrn, hc⟩ := hm
  have hS := innov_PV_termwise 𝔼 hs hε hM hρ t ω
  rw [inflation_identity_one_period_const 𝔼 hf hr hc hv (hrn t) (hT t ω)
    (seriesTo_of_hasSum hS), hS.tsum_eq]

/-- Cochrane (2023), eq. (4.2), p. 87 (Hansen, Roberds and Sargent 1992): in the simple model
`Δ_{t+1}π_{t+1} = −∑_j a_j ρʲ ε_{t+1} = −a(ρ) ε_{t+1}`, for every `|ρ| ≤ 1`. -/
theorem innov_infl_eq {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (hρ : |ρ| ≤ 1) (t : ℕ) : innov 𝔼 t (infl (t + 1)) = -gen a ρ • ε ((t : ℤ) + 1) := by
  funext ω
  rw [innov_infl_eq_tsum 𝔼 hm hT hs hε hM hρ t ω,
    (innov_PV_termwise 𝔼 hs hε hM hρ t ω).tsum_eq]
  simp

/-- Cochrane (2023), eq. (4.4), p. 88: with the normalisation `a_0 = 1`,
`Δ_{t+1}π_{t+1} = −a(ρ) Δ_{t+1}s̃_{t+1}`. -/
theorem innov_infl_eq_surplus {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (ha0 : a 0 = 1) (hρ : |ρ| ≤ 1) (t : ℕ) :
    innov 𝔼 t (infl (t + 1)) = -gen a ρ • innov 𝔼 t (s (t + 1)) := by
  rw [innov_infl_eq 𝔼 hm hT hs hε hM hρ, innov_MA_zero 𝔼 hs hε hM ha0]

/-- Cochrane (2023), §4.2.1, p. 88 (inflation volatility): the conditional variance of
unexpected inflation is `a(ρ)²` times that of the surplus shock,
`E_t[(Δπ_{t+1})²] = a(ρ)² E_t[ε²_{t+1}]`. -/
theorem condVar_innov_infl {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (hρ : |ρ| ≤ 1) (t : ℕ) :
    𝔼.E t (fun ω => innov 𝔼 t (infl (t + 1)) ω ^ 2) =
      gen a ρ ^ 2 • 𝔼.E t (fun ω => ε ((t : ℤ) + 1) ω ^ 2) := by
  rw [innov_infl_eq 𝔼 hm hT hs hε hM hρ, ← map_smul]
  congr 1
  funext ω
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), §4.2.1, pp. 88–89 (correlation of inflation and deficit shocks): the
conditional covariance of unexpected inflation with the surplus shock is
`E_t[Δπ_{t+1} ε_{t+1}] = −a(ρ) E_t[ε²_{t+1}]`. -/
theorem condCov_innov_infl {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (hρ : |ρ| ≤ 1) (t : ℕ) :
    𝔼.E t (fun ω => innov 𝔼 t (infl (t + 1)) ω * ε ((t : ℤ) + 1) ω) =
      -gen a ρ • 𝔼.E t (fun ω => ε ((t : ℤ) + 1) ω ^ 2) := by
  rw [innov_infl_eq 𝔼 hm hT hs hε hM hρ, ← map_smul]
  congr 1
  funext ω
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), §4.2.1, p. 89 ("consider the case `a(ρ) = 0` ... the model predicts no
correlation between deficits and inflation"): with `a(ρ) = 0` there is no unexpected inflation
at all, so in particular no covariance with the surplus shock. -/
theorem no_correlation_of_gen_zero {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (hρ : |ρ| ≤ 1) (h0 : gen a ρ = 0) (t : ℕ) :
    innov 𝔼 t (infl (t + 1)) = 0 ∧
      𝔼.E t (fun ω => innov 𝔼 t (infl (t + 1)) ω * ε ((t : ℤ) + 1) ω) = 0 := by
  refine ⟨by rw [innov_infl_eq 𝔼 hm hT hs hε hM hρ, h0]; simp, ?_⟩
  rw [condCov_innov_infl 𝔼 hm hT hs hε hM hρ, h0, neg_zero, zero_smul]

/-- Cochrane (2023), §4.2.1, p. 88: the numerical example "5/(1 − 0.55) = 11%" (it is
`100/9 ≈ 11.1`). -/
theorem ar1_volatility_example : (5 : ℝ) / (1 - 0.55) = 100 / 9 ∧
    (11 : ℝ) < 5 / (1 - 0.55) ∧ (5 : ℝ) / (1 - 0.55) < 11.2 := by
  norm_num

/-! ### Examples: the AR(1) and the MA(1) -/

/-- Cochrane (2023), eq. (4.3), p. 88: for the AR(1), `a(ρ) = ∑ ηʲρʲ = 1/(1 − ρη)`
(`|ρη| < 1`). -/
theorem gen_ar1 {η ρ : ℝ} (h : |ρ * η| < 1) : gen (fun j => η ^ j) ρ = 1 / (1 - ρ * η) := by
  unfold gen
  simp_rw [← mul_pow]
  rw [mul_comm η ρ, tsum_geometric_of_abs_lt_one h, one_div]

/-- Cochrane (2023), p. 88, corrected (survey E2): "`a(ρ) = 1/(1 − ρη)` is a number greater than
one" holds exactly when `η > 0` (for `0 < ρ`, `|ρη| < 1`). -/
theorem one_lt_gen_ar1_iff {η ρ : ℝ} (hρ : 0 < ρ) (h : |ρ * η| < 1) :
    1 < gen (fun j => η ^ j) ρ ↔ 0 < η := by
  rw [gen_ar1 h]
  have h1 : 0 < 1 - ρ * η := by linarith [le_abs_self (ρ * η)]
  rw [lt_div_iff₀ h1, one_mul]
  constructor
  · intro h2
    by_contra h3
    push Not at h3
    nlinarith
  · intro h2
    nlinarith

/-- Cochrane (2023), p. 88 (survey E2, counterexample): with `η = −0.3` (and `ρ = 0.9`)
`a(ρ) = 1/1.27 < 1`, so the AR(1) does not always give `a(ρ) > 1`. -/
theorem gen_ar1_lt_one_example : gen (fun j => (-0.3 : ℝ) ^ j) 0.9 < 1 := by
  rw [gen_ar1 (by norm_num [abs_of_neg])]
  norm_num

/-- Cochrane (2023), p. 88 ("since by normalization `a_0 = 1 > 0`, `a(ρ) < 1` means that some of
the higher moving average terms `a_j` must be negative"), for `ρ > 0`. -/
theorem exists_neg_coeff_of_gen_lt_one {a : ℕ → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsum : Summable fun j => a j * ρ ^ j) (ha0 : a 0 = 1) (hlt : gen a ρ < 1) :
    ∃ j, 1 ≤ j ∧ a j < 0 := by
  by_contra hcon
  push Not at hcon
  have hnn : ∀ j, 0 ≤ a (j + 1) * ρ ^ (j + 1) := fun j =>
    mul_nonneg (hcon (j + 1) (by omega)) (pow_nonneg hρ.le _)
  have : 1 ≤ gen a ρ := by
    unfold gen
    rw [hsum.tsum_eq_zero_add, ha0]
    simp only [pow_zero, mul_one, le_add_iff_nonneg_right]
    exact tsum_nonneg hnn
  linarith

/-- Cochrane (2023), p. 88: the MA(1) coefficients `a_0 = 1`, `a_1 = −θ`, `a_j = 0` for
`j ≥ 2`. -/
def ma1Coeff (θ : ℝ) (j : ℕ) : ℝ := if j = 0 then 1 else if j = 1 then -θ else 0

/-- Cochrane (2023), p. 88: `s_t = ε_t − θ ε_{t−1} = (1 − θL)ε_t` is a moving average with the
MA(1) coefficients. -/
theorem isMA_ma1 (θ : ℝ) (ε : ℤ → Ω → ℝ) :
    IsMA (ma1Coeff θ) ε (fun t => ε t - θ • ε ((t : ℤ) - 1)) := by
  refine ⟨summable_of_ne_finset_zero (s := {0, 1}) fun j hj => ?_, fun t ω => ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    simp [ma1Coeff, hj.1, hj.2]
  · rw [tsum_eq_sum (s := {0, 1}) fun j hj => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      simp [ma1Coeff, hj.1, hj.2]]
    simp [ma1Coeff]
    ring

/-- Cochrane (2023), p. 88: the MA(1) has `a(z) = 1 − θz`. -/
theorem gen_ma1 (θ z : ℝ) : gen (ma1Coeff θ) z = 1 - θ * z := by
  unfold gen
  rw [tsum_eq_sum (s := {0, 1}) fun j hj => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    simp [ma1Coeff, hj.1, hj.2]]
  simp [ma1Coeff]
  ring

/-- Cochrane (2023), p. 88: "For `θ = ρ⁻¹`, we have `a(ρ) = 0`" (full repayment with
interest). -/
theorem gen_ma1_inv {ρ : ℝ} (hρ : ρ ≠ 0) : gen (ma1Coeff ρ⁻¹) ρ = 0 := by
  rw [gen_ma1, inv_mul_cancel₀ hρ, sub_self]

/-- Cochrane (2023), p. 88: "The value `θ = 0` gives an i.i.d. surplus process with
`a(ρ) = 1`". -/
theorem gen_ma1_zero (ρ : ℝ) : gen (ma1Coeff 0) ρ = 1 := by
  rw [gen_ma1, zero_mul, sub_zero]

/-- Cochrane (2023), p. 88: "a negative `θ` generates ... `a(ρ) > 1`" (for `ρ > 0`). -/
theorem one_lt_gen_ma1 {θ ρ : ℝ} (hθ : θ < 0) (hρ : 0 < ρ) : 1 < gen (ma1Coeff θ) ρ := by
  rw [gen_ma1]
  nlinarith

/-- Cochrane (2023), p. 88: "Smaller values of `θ` accommodate `0 < a(ρ) < 1`": for
`0 < θ < ρ⁻¹` (and `ρ > 0`), `0 < a(ρ) < 1`. -/
theorem gen_ma1_mem_Ioo {θ ρ : ℝ} (hρ : 0 < ρ) (hθ0 : 0 < θ) (hθ1 : θ < ρ⁻¹) :
    0 < gen (ma1Coeff θ) ρ ∧ gen (ma1Coeff θ) ρ < 1 := by
  rw [gen_ma1]
  have h : θ * ρ < 1 := by
    have := mul_lt_mul_of_pos_right hθ1 hρ
    rwa [inv_mul_cancel₀ hρ.ne'] at this
  constructor <;> nlinarith

/-- Cochrane (2023), p. 88: for the MA(1), the deficit shock is the surplus innovation,
`Δ_{t+1}s_{t+1} = ε_{t+1}`. -/
theorem innov_ma1_now {θ : ℝ} {ε : ℤ → Ω → ℝ} (hε : IsMDS 𝔼 ε) {M : ℝ}
    (hM : ∀ k ω, |ε k ω| ≤ M) (t : ℕ) :
    innov 𝔼 t ((fun t : ℕ => ε t - θ • ε ((t : ℤ) - 1)) (t + 1)) = ε ((t : ℤ) + 1) :=
  innov_MA_zero 𝔼 (isMA_ma1 θ ε) hε hM (by simp [ma1Coeff]) t

/-- Cochrane (2023), p. 88: "that shock changes the expected value of the next surplus":
`Δ_{t+1}s_{t+2} = −θ ε_{t+1}` (so a deficit shock `ε_{t+1} = −1` raises it by `θ`). -/
theorem innov_ma1_next {θ : ℝ} {ε : ℤ → Ω → ℝ} (hε : IsMDS 𝔼 ε) {M : ℝ}
    (hM : ∀ k ω, |ε k ω| ≤ M) (t : ℕ) :
    innov 𝔼 t ((fun t : ℕ => ε t - θ • ε ((t : ℤ) - 1)) (t + 1 + 1)) =
      -θ • ε ((t : ℤ) + 1) := by
  rw [innov_MA 𝔼 (isMA_ma1 θ ε) hε hM t 1]
  simp [ma1Coeff]

/-- Cochrane (2023), p. 88, corrected (survey E3): with `θ = ρ⁻¹` the shock sets
`Δ_{t+1}s_{t+1} = ε_{t+1}` and `Δ_{t+1}s_{t+2} = −ρ⁻¹ε_{t+1}`; the printed
"`s₁ = −ε₁` ... `s₂ = ρ⁻¹ε₁`" (both signs flipped) holds in a state only if there is no
shock in that state. -/
theorem ma1_printed_signs_false {ρ : ℝ} (hρ : ρ ≠ 0) {ε : ℤ → Ω → ℝ} (hε : IsMDS 𝔼 ε)
    {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) (t : ℕ) (ω : Ω)
    (hprinted : innov 𝔼 t ((fun t : ℕ => ε t - ρ⁻¹ • ε ((t : ℤ) - 1)) (t + 1)) ω =
        -ε ((t : ℤ) + 1) ω ∨
      innov 𝔼 t ((fun t : ℕ => ε t - ρ⁻¹ • ε ((t : ℤ) - 1)) (t + 1 + 1)) ω =
        ρ⁻¹ * ε ((t : ℤ) + 1) ω) :
    ε ((t : ℤ) + 1) ω = 0 := by
  rw [innov_ma1_now 𝔼 hε hM, innov_ma1_next 𝔼 hε hM] at hprinted
  simp only [Pi.smul_apply, smul_eq_mul] at hprinted
  have hi : ρ⁻¹ ≠ 0 := inv_ne_zero hρ
  rcases hprinted with h | h
  · linarith
  · have : 2 * ρ⁻¹ * ε ((t : ℤ) + 1) ω = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 (mul_ne_zero two_ne_zero hi)
    · exact h1

/-! ### §4.2.2: surpluses and debt -/

/-- Cochrane (2023), eq. (4.6), p. 89: in the simple model,
`v_t = E_t(s̃_{t+1} + ρ v_{t+1}) − c` (with the book's normalisation `c = E_t r_{t+1} = 0`,
`v_t = E_t(s̃_{t+1} + ρ v_{t+1})`). -/
theorem value_recursion {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (t : ℕ) :
    v t = 𝔼.E t (s (t + 1) + ρ • v (t + 1)) - fun _ => c := by
  obtain ⟨hf, -, hv, -, hc⟩ := hm
  have h := hf t
  have hv' : v t = ρ • v (t + 1) + s (t + 1) - r (t + 1) := by
    rw [h]; funext ω; simp
  conv_lhs => rw [← hv t, hv']
  rw [map_sub, hc t, add_comm]

/-- Cochrane (2023), eq. (4.5), p. 89: with an AR(1) surplus (`E_t s_{t+1} = η s_t`) and
constant expected return normalised to zero, `v_t = E_t ∑_{j ≥ 0} ρʲ s̃_{t+1+j} = η s_t/(1 − ρη)`
(under the terminal condition `ρᵀ E_t v_{t+T} → 0`, `|ρη| < 1`). -/
theorem value_ar1 {ρ η : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ 0 v r rn infl s) (hs : 𝔼.IsAR1 η s) (hρη : |ρ * η| < 1) {t : ℕ}
    {ω : Ω} (hT : Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 0)) :
    SeriesTo (fun j => ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω) (v t ω) ∧
      v t ω = η * s t ω / (1 - ρ * η) := by
  obtain ⟨hf, -, hv, -, hc⟩ := hm
  have hE : ∀ j, 𝔼.E t (s (t + 1 + j)) ω = η ^ (j + 1) * s t ω := fun j => by
    rw [show t + 1 + j = t + (j + 1) by omega, 𝔼.ar1_iterate hs]
    rfl
  have hS : HasSum (fun j => ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω) (η * s t ω / (1 - ρ * η)) := by
    have := (hasSum_geometric_of_abs_lt_one hρη).mul_left (η * s t ω)
    convert this using 1
    · funext j
      rw [hE, mul_pow]
      ring
    · field_simp
  have hG : SeriesTo (fun j => ρ ^ j * 𝔼.E t ((fun _ => (0 : Ω → ℝ)) (t + 1 + j)) ω) 0 :=
    seriesTo_zero.congr (fun j => by simp) rfl
  have hR := pv_expected 𝔼 hf hv hT (seriesTo_of_hasSum hS) hG
  have hR0 : SeriesTo (fun j => ρ ^ j * 𝔼.E t (r (t + 1 + j)) ω) 0 := by
    refine seriesTo_zero.congr (fun j => ?_) rfl
    rw [← 𝔼.tower (show t ≤ t + j by omega), show t + 1 + j = t + j + 1 by omega, hc,
      𝔼.const, mul_zero]
  have heq := hR0.unique hR
  refine ⟨(seriesTo_of_hasSum hS).congr (fun _ => rfl) (by linarith), by linarith⟩

/-- Cochrane (2023), eq. (4.7), p. 89, first equality: innovations of the flow identity,
`ρ Δ_{t+1} v_{t+1} = −Δ_{t+1}π_{t+1} − Δ_{t+1}s̃_{t+1}` (no terminal condition needed). -/
theorem rho_innov_value {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (t : ℕ) :
    ρ • innov 𝔼 t (v (t + 1)) = -innov 𝔼 t (infl (t + 1)) - innov 𝔼 t (s (t + 1)) := by
  obtain ⟨hf, hr, hv, hrn, -⟩ := hm
  rw [← map_smul, hf t, map_sub, map_sub, map_add, innov_of_known 𝔼 (hv t), hr (t + 1),
    map_sub, innov_of_known 𝔼 (hrn t)]
  simp

/-- Cochrane (2023), eq. (4.7), p. 89: `ρ Δ_{t+1} v_{t+1} = [a(ρ) − 1] ε_{t+1}`. -/
theorem rho_innov_value_eq {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (ha0 : a 0 = 1) (hρ : |ρ| ≤ 1) (t : ℕ) :
    ρ • innov 𝔼 t (v (t + 1)) = (gen a ρ - 1) • ε ((t : ℤ) + 1) := by
  rw [rho_innov_value 𝔼 hm, innov_infl_eq 𝔼 hm hT hs hε hM hρ, innov_MA_zero 𝔼 hs hε hM ha0,
    sub_smul, one_smul, neg_smul, neg_neg]

/-- Cochrane (2023), pp. 89–90: "If `a(ρ) > 1` ... a surprise surplus ... raises the value of
debt ... If `a(ρ) < 1` ... lowers the value of debt": for a positive surplus shock and `ρ > 0`,
`Δ_{t+1} v_{t+1} > 0` iff `a(ρ) > 1`. -/
theorem innov_value_pos_iff {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (ha0 : a 0 = 1) (hρ0 : 0 < ρ) (hρ : |ρ| ≤ 1) (t : ℕ) (ω : Ω)
    (hpos : 0 < ε ((t : ℤ) + 1) ω) : 0 < innov 𝔼 t (v (t + 1)) ω ↔ 1 < gen a ρ := by
  have h := congrFun (rho_innov_value_eq 𝔼 hm hT hs hε hM ha0 hρ t) ω
  simp only [Pi.smul_apply, smul_eq_mul] at h
  constructor
  · intro hv
    have : 0 < (gen a ρ - 1) * ε ((t : ℤ) + 1) ω := by rw [← h]; positivity
    have := (pos_iff_pos_of_mul_pos this).2 hpos
    linarith
  · intro hg
    have : 0 < ρ * innov 𝔼 t (v (t + 1)) ω := by
      rw [h]; exact mul_pos (by linarith) hpos
    exact (pos_iff_pos_of_mul_pos this).1 hρ0

/-- Cochrane (2023), p. 90: "In the case of full repayment `a(ρ) = 0`, then a higher surplus
lowers the value of debt one for one" (`ρΔv_{t+1} = −ε_{t+1}`, and inflation is unaffected);
with `a(ρ) = 1` the deficit is financed by inflation and the value of debt is unchanged. -/
theorem innov_value_full_repayment {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (ha0 : a 0 = 1) (hρ : |ρ| ≤ 1) (t : ℕ) :
    (gen a ρ = 0 → ρ • innov 𝔼 t (v (t + 1)) = -ε ((t : ℤ) + 1) ∧
        innov 𝔼 t (infl (t + 1)) = 0) ∧
      (gen a ρ = 1 → ρ • innov 𝔼 t (v (t + 1)) = 0 ∧
        innov 𝔼 t (infl (t + 1)) = -innov 𝔼 t (s (t + 1))) := by
  have h1 := rho_innov_value_eq 𝔼 hm hT hs hε hM ha0 hρ t
  have h2 := innov_infl_eq 𝔼 hm hT hs hε hM hρ t
  refine ⟨fun h0 => ⟨?_, ?_⟩, fun h0 => ⟨?_, ?_⟩⟩
  · rw [h1, h0]; simp
  · rw [h2, h0]; simp
  · rw [h1, h0]; simp
  · rw [h2, h0, innov_MA_zero 𝔼 hs hε hM ha0]; simp

/-- Cochrane (2023), p. 91 (the linearised rearrangement of (4.8)–(4.10)):
`ρ Δ_{t+1} v_{t+1} = ρ Δ_{t+1} ∑_{j ≥ 0} ρʲ s̃_{t+2+j} = [a(ρ) − 1] ε_{t+1}`: the series
`∑_j ρ^{j+1} Δ_{t+1} s̃_{t+2+j}` converges to `ρ Δ_{t+1} v_{t+1}`. -/
theorem innov_value_eq_series {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) (t : ℕ) (ω : Ω) :
    SeriesTo (fun j => ρ ^ (j + 1) * innov 𝔼 t (s (t + 2 + j)) ω)
      (ρ * innov 𝔼 t (v (t + 1)) ω) := by
  obtain ⟨hf, -, -, -, hc⟩ := hm
  have hT' : Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + 1 + T)) ω) atTop (𝓝 0) := by
    have h := (hT t ω).const_mul ρ⁻¹
    rw [mul_zero] at h
    by_cases hρ : ρ = 0
    · subst hρ
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with T hT1
      rw [zero_pow (by omega), zero_mul]
    · rw [← tendsto_add_atTop_iff_nat 1] at h
      refine h.congr fun T => ?_
      rw [pow_succ, show t + (T + 1) = t + 1 + T by omega]
      field_simp
  have h0 := (rec_seriesTo_map (innov 𝔼 t)
    ((flow_iff_recursion ρ v r (fun _ => 0) s).1 hf) hT').const_mul ρ
  refine h0.congr (fun j => ?_) (by rw [mul_comm])
  rw [show t + 1 + 1 + j = t + 2 + j by omega, map_sub, map_add, Pi.sub_apply, Pi.add_apply,
    innov_future_return_zero 𝔼 hc, pow_succ]
  simp
  ring

/-! ### §4.2.4: the return on government debt -/

/-- Cochrane (2023), §4.2.4, p. 92: in the simple model the ex-post real return innovation is
`Δ_{t+1} r_{t+1} = −Δ_{t+1}π_{t+1} = a(ρ) ε_{t+1}`. -/
theorem innov_return {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (hρ : |ρ| ≤ 1) (t : ℕ) :
    innov 𝔼 t (r (t + 1)) = -innov 𝔼 t (infl (t + 1)) ∧
      innov 𝔼 t (r (t + 1)) = gen a ρ • ε ((t : ℤ) + 1) := by
  have h1 : innov 𝔼 t (r (t + 1)) = -innov 𝔼 t (infl (t + 1)) := by
    obtain ⟨-, hr, -, hrn, -⟩ := hm
    rw [hr, map_sub, innov_of_known 𝔼 (hrn t), zero_sub]
  refine ⟨h1, ?_⟩
  rw [h1, innov_infl_eq 𝔼 hm hT hs hε hM hρ, neg_smul, neg_neg]

/-- Cochrane (2023), §4.2.4, p. 92: the return split into "price change" and "dividend",
`r_{t+1} = ρv_{t+1} − v_t + s̃_{t+1}` and `Δ_{t+1}r_{t+1} = ρΔv_{t+1} + Δs̃_{t+1} =
[a(ρ) − 1]ε_{t+1} + ε_{t+1}`. -/
theorem innov_return_split {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (ha0 : a 0 = 1) (hρ : |ρ| ≤ 1) (t : ℕ) :
    r (t + 1) = ρ • v (t + 1) - v t + s (t + 1) ∧
      innov 𝔼 t (r (t + 1)) = ρ • innov 𝔼 t (v (t + 1)) + innov 𝔼 t (s (t + 1)) ∧
      innov 𝔼 t (r (t + 1)) = (gen a ρ - 1) • ε ((t : ℤ) + 1) + ε ((t : ℤ) + 1) := by
  have hsplit : r (t + 1) = ρ • v (t + 1) - v t + s (t + 1) := by
    rw [hm.1 t]; funext ω; simp; ring
  have h2 : innov 𝔼 t (r (t + 1)) = ρ • innov 𝔼 t (v (t + 1)) + innov 𝔼 t (s (t + 1)) := by
    rw [hsplit, map_add, map_sub, map_smul, innov_of_known 𝔼 (hm.2.2.1 t), sub_zero]
  refine ⟨hsplit, h2, ?_⟩
  rw [h2, rho_innov_value_eq 𝔼 hm hT hs hε hM ha0 hρ, innov_MA_zero 𝔼 hs hε hM ha0]

/-- Cochrane (2023), §4.2.4, p. 92: "With `a(ρ) = 0`, unexpected inflation ... is zero, and
nominal government bonds are risk free in real terms, for any volatility of surpluses". -/
theorem innov_return_riskfree {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (hρ : |ρ| ≤ 1) (h0 : gen a ρ = 0) (t : ℕ) : innov 𝔼 t (r (t + 1)) = 0 := by
  rw [(innov_return 𝔼 hm hT hs hε hM hρ t).2, h0, zero_smul]

/-- Cochrane (2023), §4.2.4, p. 92: "With `a(ρ) ≥ 1` ... the rate of return is more volatile
than surpluses": `|Δ_{t+1} r_{t+1}| ≥ |Δ_{t+1} s̃_{t+1}|` in every state. -/
theorem abs_innov_return_ge {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (ha0 : a 0 = 1) (hρ : |ρ| ≤ 1) (h1 : 1 ≤ gen a ρ) (t : ℕ) (ω : Ω) :
    |innov 𝔼 t (s (t + 1)) ω| ≤ |innov 𝔼 t (r (t + 1)) ω| := by
  rw [(innov_return 𝔼 hm hT hs hε hM hρ t).2, innov_MA_zero 𝔼 hs hε hM ha0, Pi.smul_apply,
    smul_eq_mul, abs_mul, abs_of_pos (show 0 < gen a ρ by linarith)]
  exact le_mul_of_one_le_left (abs_nonneg _) h1

/-- Cochrane (2023), §4.2.4, p. 93: the one-step valuation with a stochastic discount factor
`Λ`: if `V_t = E_t ∑_{j ≥ 1} (Λ_{t+j}/Λ_t) s_{t+j}` at every date, then
`V_t = E_t[(Λ_{t+1}/Λ_t) s_{t+1}] + E_t[(Λ_{t+1}/Λ_t) V_{t+1}]` (with `V_t = Q_tB_t/P_t` and
`Λ_{t+1}/Λ_t = βu'(c_{t+1})/u'(c_t)` this is the book's display). -/
theorem sdf_one_step (hpull : 𝔼.PullOut) {Λ s V : ℕ → Ω → ℝ} (hΛ0 : ∀ t ω, Λ t ω ≠ 0)
    (hm : ∀ t, 𝔼.E (t + 1) (fun ω => Λ (t + 1) ω / Λ t ω) = fun ω => Λ (t + 1) ω / Λ t ω)
    (hsum : ∀ t ω, Summable fun j => Λ (t + 1 + j) ω / Λ t ω * s (t + 1 + j) ω)
    (hV : ∀ t, V t = 𝔼.E t (fun ω => ∑' j, Λ (t + 1 + j) ω / Λ t ω * s (t + 1 + j) ω))
    (t : ℕ) :
    V t = 𝔼.E t (fun ω => Λ (t + 1) ω / Λ t ω * s (t + 1) ω) +
      𝔼.E t (fun ω => Λ (t + 1) ω / Λ t ω * V (t + 1) ω) := by
  set m : Ω → ℝ := fun ω => Λ (t + 1) ω / Λ t ω with hm_def
  set R : Ω → ℝ := fun ω => ∑' j, Λ (t + 1 + 1 + j) ω / Λ (t + 1) ω * s (t + 1 + 1 + j) ω
    with hR_def
  have hsplit : (fun ω => ∑' j, Λ (t + 1 + j) ω / Λ t ω * s (t + 1 + j) ω) =
      (fun ω => m ω * s (t + 1) ω) + m * R := by
    funext ω
    rw [(hsum t ω).tsum_eq_zero_add]
    simp only [Pi.add_apply, Pi.mul_apply, hm_def, hR_def, add_zero]
    rw [← tsum_mul_left]
    congr 1
    refine tsum_congr fun j => ?_
    rw [show t + 1 + (j + 1) = t + 1 + 1 + j by omega]
    field_simp [hΛ0 t ω, hΛ0 (t + 1) ω]
  have hVR : 𝔼.E (t + 1) R = V (t + 1) := (hV (t + 1)).symm
  have hmR : 𝔼.E t (m * R) = 𝔼.E t (fun ω => m ω * V (t + 1) ω) := by
    rw [← 𝔼.tower (Nat.le_succ t), hpull (t + 1) m R (hm t), hVR]
    rfl
  rw [hV t, hsplit, map_add, hmR]

/-! ### §4.2.3: the exact model -/

/-- Cochrane (2023), §4.2.3, p. 91: the real value of maturing debt `B_t/P_{t+1}`. -/
noncomputable def realDebt (B P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := fun ω => B t ω / P (t + 1) ω

/-- Cochrane (2023), §4.2.3, p. 91: the end-of-period debt deflated by today's price,
`B_t/P_t`. -/
noncomputable def realDebtEnd (B P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := fun ω => B t ω / P t ω

/-- Cochrane (2023), §4.2.3, p. 91: the inverse gross inflation rate `P_t/P_{t+1}`. -/
noncomputable def deflation (P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := fun ω => P t ω / P (t + 1) ω

/-- Cochrane (2023), §2.7 and §4.2.3, p. 91 (constant real rate, flexible prices): the
one-period bond price `Q_t = β E_t(P_t/P_{t+1})`. -/
noncomputable def bondPrice (β : ℝ) (P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := β • 𝔼.E t (deflation P t)

/-- Cochrane (2023), p. 87: the discounted sum `∑_{j ≥ 0} βʲ s_{t+j}`. -/
noncomputable def pv (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, β ^ j * s (t + j) ω

/-- Cochrane (2023), §2.7 and §4.2, p. 87: the exact valuation equation
`B_t/P_{t+1} = E_{t+1} ∑_{j ≥ 0} βʲ s_{t+1+j}` at every date. -/
def ExactValuation (β : ℝ) (B P s : ℕ → Ω → ℝ) : Prop :=
  ∀ t, realDebt B P t = 𝔼.E (t + 1) (pv β s (t + 1))

/-- Cochrane (2023), p. 91: `B_t/P_{t+1} = (B_t/P_t)(P_t/P_{t+1})`. -/
theorem realDebt_eq_mul {B P : ℕ → Ω → ℝ} (hP : ∀ t ω, P t ω ≠ 0) (t : ℕ) :
    realDebt B P t = realDebtEnd B P t * deflation P t := by
  funext ω
  simp only [realDebt, realDebtEnd, deflation, Pi.mul_apply]
  field_simp [hP t ω, hP (t + 1) ω]

/-- Cochrane (2023), p. 87: `∑_{j ≥ 0} βʲ s_{t+j} = s_t + β ∑_{j ≥ 0} βʲ s_{t+1+j}` for a
bounded surplus and `|β| < 1`. -/
theorem pv_succ {β : ℝ} (hβ : |β| < 1) {s : ℕ → Ω → ℝ} {K : ℝ} (hs : ∀ t ω, |s t ω| ≤ K)
    (t : ℕ) : pv β s t = s t + β • pv β s (t + 1) := by
  funext ω
  have hsum : Summable fun j => β ^ j * s (t + j) ω :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one (abs_nonneg β) hβ).mul_right K)
      fun j => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow]
        exact mul_le_mul_of_nonneg_left (hs _ ω) (pow_nonneg (abs_nonneg _) _)
  simp only [pv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsum.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, add_zero]
  congr 1
  refine tsum_congr fun j => ?_
  rw [pow_succ, show t + (j + 1) = t + 1 + j by omega]
  ring

/-- Cochrane (2023), p. 91: real revenue from bond sales, `Q_t B_t/P_t = β E_t(B_t/P_{t+1})`
(uses the pull-out property, since `B_t/P_t` is known at `t`). -/
theorem revenue_eq (hpull : 𝔼.PullOut) {β : ℝ} {B P : ℕ → Ω → ℝ} (hP : ∀ t ω, P t ω ≠ 0)
    (hBP : ∀ t, 𝔼.E t (realDebtEnd B P t) = realDebtEnd B P t) (t : ℕ) :
    bondPrice 𝔼 β P t * realDebtEnd B P t = β • 𝔼.E t (realDebt B P t) := by
  rw [realDebt_eq_mul hP, hpull t _ _ (hBP t), bondPrice, smul_mul_assoc, mul_comm]

/-- Cochrane (2023), §2.7 and p. 91: the exact valuation equation implies the exact flow
identity `B_t/P_{t+1} = s_{t+1} + Q_{t+1} B_{t+1}/P_{t+1}`. -/
theorem exact_flow_of_valuation (hpull : 𝔼.PullOut) {β : ℝ} (hβ : |β| < 1)
    {B P s : ℕ → Ω → ℝ} (hP : ∀ t ω, P t ω ≠ 0)
    (hBP : ∀ t, 𝔼.E t (realDebtEnd B P t) = realDebtEnd B P t) (hsa : 𝔼.Adapted s) {K : ℝ}
    (hsb : ∀ t ω, |s t ω| ≤ K) (hval : ExactValuation 𝔼 β B P s) (t : ℕ) :
    realDebt B P t = s (t + 1) + bondPrice 𝔼 β P (t + 1) * realDebtEnd B P (t + 1) := by
  rw [revenue_eq 𝔼 hpull hP hBP, hval (t + 1), 𝔼.tower (Nat.le_succ (t + 1)), hval t,
    pv_succ hβ hsb, map_add, map_smul, hsa]

/-- Cochrane (2023), p. 87, corrected (survey E1): in the exact model,
`(B_t/P_t) Δ_{t+1}(P_t/P_{t+1}) = Δ_{t+1} ∑_{j ≥ 0} βʲ s_{t+1+j} = a(β) ε_{t+1}`. -/
theorem exact_innov_line (hpull : 𝔼.PullOut) {β : ℝ} (hβ : |β| < 1) {B P s : ℕ → Ω → ℝ}
    (hP : ∀ t ω, P t ω ≠ 0) (hBP : ∀ t, 𝔼.E t (realDebtEnd B P t) = realDebtEnd B P t)
    (hval : ExactValuation 𝔼 β B P s) {a : ℕ → ℝ} {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s)
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) (t : ℕ) :
    realDebtEnd B P t * innov 𝔼 t (deflation P t) = innov 𝔼 t (pv β s (t + 1)) ∧
      innov 𝔼 t (pv β s (t + 1)) = gen a β • ε ((t : ℤ) + 1) := by
  have hknown : 𝔼.E (t + 1) (realDebtEnd B P t) = realDebtEnd B P t :=
    ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hBP t)
  refine ⟨?_, innov_PV 𝔼 hs hε hM hβ t⟩
  have hr : innov 𝔼 t (pv β s (t + 1)) = innov 𝔼 t (realDebt B P t) := by
    rw [hval t, innov_E_of_le 𝔼 le_rfl]
  rw [hr, realDebt_eq_mul hP, innov_apply, innov_apply, hpull (t + 1) _ _ hknown,
    hpull t _ _ (hBP t), mul_sub]

/-- Cochrane (2023), p. 87, as printed (survey E1): the innovation in `∑_{j ≥ 0} βʲ s_{t+j}`
(current surplus included) is `β a(β) ε_{t+1}`, not `a(β) ε_{t+1}`. -/
theorem printed_exact_line {β : ℝ} (hβ : |β| < 1) {s : ℕ → Ω → ℝ} {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (t : ℕ) : innov 𝔼 t (pv β s t) = (β * gen a β) • ε ((t : ℤ) + 1) := by
  have hv := (isMA_iff_vec a ε s).1 hs
  have hsa := adapted_MAVec 𝔼 hv (isMDSVec_of_isMDS 𝔼 hε) (fun k _ ω => hM k ω)
  rw [pv_succ hβ (fun t ω => abs_MAVec_le hv (fun k _ ω => hM k ω) t ω), map_add, map_smul,
    innov_of_known 𝔼 (hsa t), zero_add]
  change β • innov 𝔼 t (fun ω => ∑' j, β ^ j * s (t + 1 + j) ω) = _
  rw [innov_PV 𝔼 hs hε hM hβ, smul_smul]

/-- Cochrane (2023), p. 87 (survey E1): the printed line `Δ_{t+1}∑βʲ s_{t+j} = a(β)ε_{t+1}`
holds in a state iff `(1 − β) a(β) ε_{t+1} = 0`; for `β < 1` iff `a(β) = 0` or there is no
shock. -/
theorem printed_exact_line_iff {β : ℝ} (hβ : |β| < 1) {s : ℕ → Ω → ℝ} {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (t : ℕ) (ω : Ω) :
    innov 𝔼 t (pv β s t) ω = gen a β * ε ((t : ℤ) + 1) ω ↔
      gen a β = 0 ∨ ε ((t : ℤ) + 1) ω = 0 := by
  rw [printed_exact_line 𝔼 hβ hs hε hM, Pi.smul_apply, smul_eq_mul]
  have h1 : 1 - β ≠ 0 := by
    have := le_abs_self β
    intro h; linarith
  constructor
  · intro h
    have : (1 - β) * (gen a β * ε ((t : ℤ) + 1) ω) = 0 := by linarith
    rcases mul_eq_zero.1 this with h2 | h2
    · exact absurd h2 h1
    · exact mul_eq_zero.1 h2
  · rintro (h | h) <;> simp [h]

/-- Cochrane (2023), p. 87 (survey E1, counterexample): for the i.i.d. coin-flip surplus
`s_t = ε_t` (`a(β) = 1`) and `β = 1/2`, `Δ_1 ∑ βʲ s_j = 1/2` in the state where the first coin is
heads, whereas the printed formula gives `a(β) ε_1 = 1`. -/
theorem printed_exact_line_counterexample :
    innov ExpectationsFiniteTree.coinSystem 0 (pv (1 / 2) (fun t => coinShockZ t) 0)
        (true, true) = 1 / 2 ∧
      gen iidCoeff (1 / 2) * coinShockZ ((0 : ℕ) + 1) (true, true) = 1 := by
  have hβ : |(1 / 2 : ℝ)| < 1 := by norm_num [abs_of_pos]
  have h := printed_exact_line ExpectationsFiniteTree.coinSystem hβ (isMA_iid coinShockZ)
    coinShockZ_isMDS coinShockZ_bounded 0
  have h1 : coinShockZ ((0 : ℕ) + 1) (true, true) = 1 := by
    simpa using coinShockZ_one
  refine ⟨?_, by rw [gen_iid, h1, one_mul]⟩
  rw [h, Pi.smul_apply, smul_eq_mul, gen_iid, h1]
  norm_num

/-- Cochrane (2023), eq. (4.8), p. 91: `(B_t/P_t) Δ_{t+1}(P_t/P_{t+1}) =
Δ_{t+1} s_{t+1} + β Δ_{t+1}(B_{t+1}/P_{t+2})`. -/
theorem exact_innov_flow (hpull : 𝔼.PullOut) {β : ℝ} (hβ : |β| < 1) {B P s : ℕ → Ω → ℝ}
    (hP : ∀ t ω, P t ω ≠ 0) (hBP : ∀ t, 𝔼.E t (realDebtEnd B P t) = realDebtEnd B P t)
    (hsa : 𝔼.Adapted s) {K : ℝ} (hsb : ∀ t ω, |s t ω| ≤ K) (hval : ExactValuation 𝔼 β B P s)
    (t : ℕ) :
    realDebtEnd B P t * innov 𝔼 t (deflation P t) =
      innov 𝔼 t (s (t + 1)) + β • innov 𝔼 t (realDebt B P (t + 1)) := by
  have hknown : 𝔼.E (t + 1) (realDebtEnd B P t) = realDebtEnd B P t :=
    ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hBP t)
  have hlhs : realDebtEnd B P t * innov 𝔼 t (deflation P t) = innov 𝔼 t (realDebt B P t) := by
    rw [realDebt_eq_mul hP, innov_apply, innov_apply, hpull (t + 1) _ _ hknown,
      hpull t _ _ (hBP t), mul_sub]
  rw [hlhs, exact_flow_of_valuation 𝔼 hpull hβ hP hBP hsa hsb hval t,
    revenue_eq 𝔼 hpull hP hBP, map_add, map_smul, innov_E_of_le 𝔼 le_rfl]

/-- Cochrane (2023), eq. (4.9), p. 91: `(B_t/P_t) Δ_{t+1}(P_t/P_{t+1}) =
Δ_{t+1} s_{t+1} + β Δ_{t+1} ∑_{j ≥ 0} βʲ s_{t+2+j}`. -/
theorem exact_innov_flow_pv (hpull : 𝔼.PullOut) {β : ℝ} (hβ : |β| < 1) {B P s : ℕ → Ω → ℝ}
    (hP : ∀ t ω, P t ω ≠ 0) (hBP : ∀ t, 𝔼.E t (realDebtEnd B P t) = realDebtEnd B P t)
    (hsa : 𝔼.Adapted s) {K : ℝ} (hsb : ∀ t ω, |s t ω| ≤ K) (hval : ExactValuation 𝔼 β B P s)
    (t : ℕ) :
    realDebtEnd B P t * innov 𝔼 t (deflation P t) =
      innov 𝔼 t (s (t + 1)) + β • innov 𝔼 t (pv β s (t + 1 + 1)) := by
  rw [exact_innov_flow 𝔼 hpull hβ hP hBP hsa hsb hval t, hval (t + 1),
    innov_E_of_le 𝔼 (Nat.le_succ (t + 1))]

/-- Cochrane (2023), eq. (4.10), p. 91: `(B_t/P_t) Δ_{t+1}(P_t/P_{t+1}) =
ε_{t+1} + [a(β) − 1] ε_{t+1}`; the second term is the revenue from bond sales. -/
theorem exact_innov_flow_ma (hpull : 𝔼.PullOut) {β : ℝ} (hβ : |β| < 1) {B P s : ℕ → Ω → ℝ}
    (hP : ∀ t ω, P t ω ≠ 0) (hBP : ∀ t, 𝔼.E t (realDebtEnd B P t) = realDebtEnd B P t)
    (hval : ExactValuation 𝔼 β B P s) {a : ℕ → ℝ} {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s)
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) (ha0 : a 0 = 1) (t : ℕ) :
    innov 𝔼 t (s (t + 1)) = ε ((t : ℤ) + 1) ∧
      β • innov 𝔼 t (pv β s (t + 1 + 1)) = (gen a β - 1) • ε ((t : ℤ) + 1) := by
  have hv := (isMA_iff_vec a ε s).1 hs
  have hsa := adapted_MAVec 𝔼 hv (isMDSVec_of_isMDS 𝔼 hε) (fun k _ ω => hM k ω)
  have hsb := fun t ω => abs_MAVec_le hv (fun k _ ω => hM k ω) t ω
  have h1 := exact_innov_flow_pv 𝔼 hpull hβ hP hBP hsa hsb hval t
  have h2 := exact_innov_line 𝔼 hpull hβ hP hBP hval hs hε hM t
  have h3 := innov_MA_zero 𝔼 hs hε hM ha0 t
  refine ⟨h3, ?_⟩
  rw [h2.1, h2.2, h3] at h1
  rw [sub_smul, one_smul, h1]
  abel

/-- Cochrane (2023), p. 91: the innovation in real revenue from bond sales at the end of
`t + 1` is `Δ_{t+1}(Q_{t+1}B_{t+1}/P_{t+1}) = [a(β) − 1] ε_{t+1}`. -/
theorem revenue_innov (hpull : 𝔼.PullOut) {β : ℝ} (hβ : |β| < 1) {B P s : ℕ → Ω → ℝ}
    (hP : ∀ t ω, P t ω ≠ 0) (hBP : ∀ t, 𝔼.E t (realDebtEnd B P t) = realDebtEnd B P t)
    (hval : ExactValuation 𝔼 β B P s) {a : ℕ → ℝ} {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s)
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) (ha0 : a 0 = 1) (t : ℕ) :
    innov 𝔼 t (bondPrice 𝔼 β P (t + 1) * realDebtEnd B P (t + 1)) =
      (gen a β - 1) • ε ((t : ℤ) + 1) := by
  rw [revenue_eq 𝔼 hpull hP hBP, map_smul, innov_E_of_le 𝔼 le_rfl, hval (t + 1),
    innov_E_of_le 𝔼 (Nat.le_succ (t + 1))]
  exact (exact_innov_flow_ma 𝔼 hpull hβ hP hBP hval hs hε hM ha0 t).2

/-- Cochrane (2023), p. 91: "If `a(β) = 0`, that extra revenue completely finances the
deficit": the revenue innovation is `−ε_{t+1} = −Δs_{t+1}` and there is no inflation surprise. -/
theorem financing_by_debt (hpull : 𝔼.PullOut) {β : ℝ} (hβ : |β| < 1) {B P s : ℕ → Ω → ℝ}
    (hP : ∀ t ω, P t ω ≠ 0) (hBP : ∀ t, 𝔼.E t (realDebtEnd B P t) = realDebtEnd B P t)
    (hval : ExactValuation 𝔼 β B P s) {a : ℕ → ℝ} {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s)
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) (ha0 : a 0 = 1) (h0 : gen a β = 0)
    (t : ℕ) :
    innov 𝔼 t (bondPrice 𝔼 β P (t + 1) * realDebtEnd B P (t + 1)) = -innov 𝔼 t (s (t + 1)) ∧
      realDebtEnd B P t * innov 𝔼 t (deflation P t) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [revenue_innov 𝔼 hpull hβ hP hBP hval hs hε hM ha0, h0, innov_MA_zero 𝔼 hs hε hM ha0]
    simp
  · have h := exact_innov_line 𝔼 hpull hβ hP hBP hval hs hε hM t
    rw [h.1, h.2, h0, zero_smul]

/-- Cochrane (2023), p. 91: "if `a(β) = a_0 = 1`, then the government gets no additional
revenue from bond sales. The extra deficit is entirely financed by inflating away outstanding
debt": revenue innovation zero, `(B_t/P_t)Δ(P_t/P_{t+1}) = ε_{t+1}`. -/
theorem financing_by_inflation (hpull : 𝔼.PullOut) {β : ℝ} (hβ : |β| < 1)
    {B P s : ℕ → Ω → ℝ} (hP : ∀ t ω, P t ω ≠ 0)
    (hBP : ∀ t, 𝔼.E t (realDebtEnd B P t) = realDebtEnd B P t)
    (hval : ExactValuation 𝔼 β B P s) {a : ℕ → ℝ} {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s)
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) (ha0 : a 0 = 1) (h1 : gen a β = 1)
    (t : ℕ) :
    innov 𝔼 t (bondPrice 𝔼 β P (t + 1) * realDebtEnd B P (t + 1)) = 0 ∧
      realDebtEnd B P t * innov 𝔼 t (deflation P t) = ε ((t : ℤ) + 1) := by
  refine ⟨?_, ?_⟩
  · rw [revenue_innov 𝔼 hpull hβ hP hBP hval hs hε hM ha0, h1, sub_self, zero_smul]
  · have h := exact_innov_line 𝔼 hpull hβ hP hBP hval hs hε hM t
    rw [h.1, h.2, h1, one_smul]

/-- Cochrane (2023), p. 91: "if `a(β) > 1`, then the government raises less revenue from
selling bonds": after a deficit shock `ε_{t+1} < 0` the revenue innovation is negative and the
devaluation `(B_t/P_t)Δ(P_t/P_{t+1})` exceeds the deficit. -/
theorem financing_superinflation (hpull : 𝔼.PullOut) {β : ℝ} (hβ : |β| < 1)
    {B P s : ℕ → Ω → ℝ} (hP : ∀ t ω, P t ω ≠ 0)
    (hBP : ∀ t, 𝔼.E t (realDebtEnd B P t) = realDebtEnd B P t)
    (hval : ExactValuation 𝔼 β B P s) {a : ℕ → ℝ} {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s)
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) (ha0 : a 0 = 1) (h1 : 1 < gen a β)
    (t : ℕ) (ω : Ω) (hneg : ε ((t : ℤ) + 1) ω < 0) :
    innov 𝔼 t (bondPrice 𝔼 β P (t + 1) * realDebtEnd B P (t + 1)) ω < 0 ∧
      (realDebtEnd B P t * innov 𝔼 t (deflation P t)) ω < ε ((t : ℤ) + 1) ω := by
  refine ⟨?_, ?_⟩
  · rw [revenue_innov 𝔼 hpull hβ hP hBP hval hs hε hM ha0, Pi.smul_apply, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (by linarith) hneg
  · have h := exact_innov_line 𝔼 hpull hβ hP hBP hval hs hε hM t
    rw [h.1, h.2, Pi.smul_apply, smul_eq_mul]
    nlinarith

end Cochrane.DebtDeficitsInflation.SurplusMA
