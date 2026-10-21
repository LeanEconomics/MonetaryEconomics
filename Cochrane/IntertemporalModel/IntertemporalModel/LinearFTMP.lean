/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.ExpectationTools
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# The fiscal theory of monetary policy: the linear model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.5 "The fiscal theory of
monetary policy" and §2.6 "Interest-rate rules", pp. 34–42.

## Main results

* Innovations `ΔE_{t+1} = E_{t+1} − E_t` are `ExpectationTools.innov` (shared with
  `FiscalMonetary`): linear, zero on known variables, unforecastable, pull-out of known factors.
* (2.16) as an exact derivative: `fisher_log_form` (the exact Fisher equation
  `1/(1 + i_t) = β E_t(P_t/P_{t+1})` in logs), `fisher_deriv` (along any bounded direction of
  inflation the exact map has derivative `E_t π_{t+1}` at the steady state `log(1 + i) = r`),
  `fisher_pf_exact` (exact under perfect foresight).
* (2.17) exactly: `unexpected_inflation_exact` (`V_t ΔE_{t+1}(P_t/P_{t+1}) = ΔE_{t+1} PV_{t+1}`
  with `V_t = B_t/P_t`), `innov_forwardSeries` (the PV news is `∑ βʲ ΔE_{t+1} s_{t+1+j}`, a
  genuine series), `pvNews_isShock`; the linear (2.17) as the first derivative of the exact one,
  `linear_217`; (2.18) exactly, `debt_218`.
* (2.19): `pegModel_iff`, `peg_existsUnique` — for every interest-rate path and every fiscal
  shock the model has exactly one solution given `π_0`, `π_{t+1} = i_t − ε_{Σs,t+1}`; it is
  bounded when the inputs are (`pegSol_bounded`).
* Figure 2.1 and p. 36: `irf_peg_impact`, `irf_peg_later`, `fig21_rate`, `fig21_fiscal`;
  announcements: `expected_inflation_ahead`, `announcement_invariant`,
  `no_announcement_effect`; fiscal news timing: `innov_of_news`, `pvNews_of_news`,
  `fig21_expected_fiscal` (inflation jumps when the fiscal news arrives, not when surpluses
  change); p. 37 `long_run_fisher`.
* §2.5.1: `pTarget_price` (`p_t = E_t p*_{t+1} − i_t`), `pTarget_rate_lowers_price`,
  `pTarget_fiscal_contraction`, `loggerhead`; survey error E6: `innov_pi_eq_innov_p` and
  `printed_E6_false`.
* p. 39 (passive fiscal policy): `passive_any_innovation` — any martingale difference is an
  equilibrium inflation innovation once fiscal policy accommodates.
* §2.6, (2.20)–(2.25): `ruleModel_iff`, `eq224_iff`, `rule_existsUnique` (**for every `θ`**: the
  FTPL needs no Taylor principle), `rule_eq_peg` (feeding the equilibrium rate into (2.19)),
  `ruleSol_bounded` (`|θ| < 1`), `ruleSol_unbounded` (`|θ| > 1`, survey item E30).
* Figure 2.2: the impulse responses as innovations, `irf_rule` (`ΔE_{t+1}π_{t+1+j} =
  −θʲ ε_{Σs,t+1} + c_j ε_{i,t+1}` with `c_j = (θʲ − ηʲ)/(θ − η)`), `irf_rule_rate`,
  `conv_eq`, `fig22_monetary`, `fig22_fiscal`; the hump `hump_step`, `hump_up`, `hump_down`,
  `hump_exists` (unimodal for every `0 < η < θ < 1`), `fig22_peak` (for `θ = .8`, `η = .7` the
  peak is `π_5 = 1.695`); p. 41 `fiscal_sets_impact`,
  `one_time_price_jump`, `price_level_returns`.

Expectations: an arbitrary `ExpectationSystem`; `PullOut` is a hypothesis where used. Inflation
`π_t`, rates `i_t` and shocks are random variables (`Ω → ℝ`) at each date.
-/

namespace Cochrane.IntertemporalModel.LinearFTMP

open Filter Topology Asymptotics ExpectationTools

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (2.16): the Fisher equation as an exact derivative -/

/-- Cochrane (2023), eq. (2.16), p. 35 (exact form, from (2.3)): `1/(1 + i_t) = β E_t(P_t/P_{t+1})`
with `β = 1/R`. -/
def FisherExact (β : ℝ) (i P : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, 1 / (1 + i t ω) = β * 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω

/-- Cochrane (2023), eq. (2.16), p. 35: with positive prices, `1 + i_t > 0` and a positive
expectation, the exact Fisher equation is `log(1 + i_t) = r − log E_t[exp(−π_{t+1})]` with
`r = log R = −log β` and `π_{t+1} = log(P_{t+1}/P_t)`. -/
theorem fisher_log_form {β : ℝ} (hβ : 0 < β) {i P : ℕ → Ω → ℝ} {t : ℕ}
    (hP : ∀ s ω, 0 < P s ω) (hi : ∀ ω, 0 < 1 + i t ω)
    (hE : ∀ ω, 0 < 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω) :
    FisherExact 𝔼 β i P t ↔ ∀ ω, Real.log (1 + i t ω) = -Real.log β -
      Real.log (𝔼.E t (fun ω' => Real.exp (-Real.log (P (t + 1) ω' / P t ω'))) ω) := by
  have hX : (fun ω' => Real.exp (-Real.log (P (t + 1) ω' / P t ω'))) =
      fun ω' => P t ω' / P (t + 1) ω' := by
    funext ω'
    have h1 := hP t ω'
    have h2 := hP (t + 1) ω'
    rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  rw [hX]
  refine forall_congr' fun ω => ?_
  have hE' := hE ω
  have hi' := hi ω
  have hlog : -Real.log β - Real.log (𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω) =
      Real.log ((β * 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω)⁻¹) := by
    rw [Real.log_inv, Real.log_mul hβ.ne' hE'.ne']
    ring
  rw [hlog]
  constructor
  · intro h
    rw [← h, one_div, inv_inv]
  · intro h
    have h' := Real.log_injOn_pos (Set.mem_Ioi.mpr hi')
      (Set.mem_Ioi.mpr (inv_pos.mpr (mul_pos hβ hE'))) h
    rw [h', one_div, inv_inv]

/-- Cochrane (2023), eq. (2.16), p. 35 (exact under perfect foresight): with perfect foresight
the exact Fisher equation is `log(1 + i_t) = −log β + log(P_{t+1}/P_t)`, i.e. `i_t = r + π_{t+1}`
exactly in logs. -/
theorem fisher_pf_exact {β : ℝ} (hβ : 0 < β) {i P : ℕ → Unit → ℝ} {t : ℕ}
    (hP : ∀ s ω, 0 < P s ω) (hi : ∀ ω, 0 < 1 + i t ω) :
    FisherExact perfectForesight β i P t ↔
      ∀ ω, Real.log (1 + i t ω) = -Real.log β + Real.log (P (t + 1) ω / P t ω) := by
  rw [fisher_log_form perfectForesight hβ hP hi (fun ω => div_pos (hP t ω) (hP (t + 1) ω))]
  refine forall_congr' fun ω => ?_
  change _ = _ - Real.log (Real.exp _) ↔ _
  rw [Real.log_exp]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), eq. (2.16), p. 35 (derivative of an expectation; restated from the Woodford
Chapter 2 project, `LogLinear.hasDerivAt_E_exp`): for a bounded random variable `X`,
`ε ↦ E_t[exp(ε X)]` has derivative `E_t X` at `0`. -/
theorem hasDerivAt_E_exp {K : ℝ} {X : Ω → ℝ} (hX : ∀ ω, |X ω| ≤ K) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => 𝔼.E t (fun ω' => Real.exp (ε * X ω')) ω) (𝔼.E t X ω) 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hK : 0 ≤ |K| := abs_nonneg K
  have hbig : (fun h : ℝ => 𝔼.E t (fun ω' => Real.exp ((0 + h) * X ω')) ω -
      𝔼.E t (fun ω' => Real.exp (0 * X ω')) ω - h • 𝔼.E t X ω) =O[𝓝 0] fun h => h ^ 2 := by
    refine IsBigO.of_bound (|K| ^ 2) ?_
    have hball : Metric.ball (0 : ℝ) (1 / (|K| + 1)) ∈ 𝓝 (0 : ℝ) :=
      Metric.ball_mem_nhds 0 (by positivity)
    filter_upwards [hball] with h hh
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
    have hrem : ∀ ω', |Real.exp (h * X ω') - 1 - h * X ω'| ≤ |K| ^ 2 * h ^ 2 := by
      intro ω'
      have hx : |h * X ω'| ≤ 1 := by
        rw [abs_mul]
        have h1 : |X ω'| ≤ |K| := (hX ω').trans (le_abs_self K)
        have h2 : |h| * (|K| + 1) ≤ 1 := by
          rw [lt_div_iff₀ (by positivity)] at hh
          exact hh.le
        nlinarith [abs_nonneg h, abs_nonneg (X ω')]
      refine (Real.abs_exp_sub_one_sub_id_le hx).trans ?_
      rw [mul_pow, mul_comm (|K| ^ 2)]
      have : X ω' ^ 2 ≤ |K| ^ 2 := by
        rw [← sq_abs (X ω')]
        exact pow_le_pow_left₀ (abs_nonneg _) ((hX ω').trans (le_abs_self K)) 2
      exact mul_le_mul_of_nonneg_left this (sq_nonneg h)
    have heq : 𝔼.E t (fun ω' => Real.exp ((0 + h) * X ω')) ω -
        𝔼.E t (fun ω' => Real.exp (0 * X ω')) ω - h • 𝔼.E t X ω =
        𝔼.E t (fun ω' => Real.exp (h * X ω') - 1 - h * X ω') ω := by
      have hfun : (fun ω' => Real.exp (h * X ω') - 1 - h * X ω') =
          (fun ω' => Real.exp (h * X ω')) - (fun _ => (1 : ℝ)) - h • X := by
        funext ω'
        simp
      rw [hfun, map_sub, map_sub, map_smul, 𝔼.const]
      simp [𝔼.const]
    rw [heq, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h)]
    exact 𝔼.abs_E_le hrem t ω
  exact hbig.trans_isLittleO (isLittleO_pow_id (by norm_num))

/-- Cochrane (2023), eq. (2.16), p. 35, `i_t ≈ r + E_t π_{t+1}` as an exact derivative: along a
bounded direction `π̂` of inflation (`π_{t+1} = ε π̂`, so `P_t/P_{t+1} = exp(−ε π̂)`), the right
side of `fisher_log_form`, `ε ↦ −log β − log E_t[exp(−ε π̂)]`, has derivative `E_t π̂` at the
steady state `ε = 0`. -/
theorem fisher_deriv {K : ℝ} {πh : Ω → ℝ} (hb : ∀ ω, |πh ω| ≤ K) (β : ℝ) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => -Real.log β - Real.log (𝔼.E t (fun ω' => Real.exp (ε * -πh ω')) ω))
      (𝔼.E t πh ω) 0 := by
  have hX : ∀ ω', |(fun ω'' => -πh ω'') ω'| ≤ K := fun ω' => by
    simpa only [abs_neg] using hb ω'
  have h1 : 𝔼.E t (fun ω' => Real.exp (0 * -πh ω')) ω = 1 := by
    simp only [zero_mul, Real.exp_zero]
    rw [𝔼.const]
  have h := (hasDerivAt_E_exp 𝔼 hX t ω).log (by rw [h1]; exact one_ne_zero)
  rw [h1, div_one] at h
  have hneg : 𝔼.E t (fun ω'' => -πh ω'') ω = -𝔼.E t πh ω := by
    change 𝔼.E t (-πh) ω = _
    rw [map_neg, Pi.neg_apply]
  rw [hneg] at h
  have := h.const_sub (-Real.log β)
  simpa using this

/-- Cochrane (2023), eq. (2.16), p. 35: at the steady state `ε = 0` the exact Fisher map equals
`r = log R = −log β` ("when we think of variables as deviations from steady state, we drop
`r`"). -/
theorem fisher_deriv_value (πh : Ω → ℝ) (β : ℝ) (t : ℕ) (ω : Ω) :
    -Real.log β - Real.log (𝔼.E t (fun ω' => Real.exp (0 * -πh ω')) ω) = -Real.log β := by
  simp only [zero_mul, Real.exp_zero]
  rw [𝔼.const, Real.log_one, sub_zero]

/-! ### (2.17)–(2.18): fiscal news and unexpected inflation, exactly -/

/-- Cochrane (2023), eq. (2.17), p. 35, exact form (eq. (2.13) at `t + 1`): if the valuation
equation `B_t/P_{t+1} = PV_{t+1}` holds and `V_t = B_t/P_t` is known at `t`, then
`V_t ΔE_{t+1}(P_t/P_{t+1}) = ΔE_{t+1} PV_{t+1}`. -/
theorem unexpected_inflation_exact (hPO : 𝔼.PullOut) {B P PV : ℕ → Ω → ℝ} {t : ℕ}
    (hP : ∀ ω, P t ω ≠ 0)
    (hV : 𝔼.E t (fun ω => B t ω / P t ω) = fun ω => B t ω / P t ω)
    (hval : (fun ω => B t ω / P (t + 1) ω) = PV (t + 1)) :
    (fun ω => B t ω / P t ω) * innov 𝔼 t (fun ω => P t ω / P (t + 1) ω) =
      innov 𝔼 t (PV (t + 1)) := by
  rw [← innov_mul_known 𝔼 hPO hV, ← hval]
  congr 1
  funext ω
  simp only [Pi.mul_apply]
  rw [div_mul_div_comm, mul_comm (P t ω), mul_div_mul_right _ _ (hP ω)]

/-- Cochrane (2023), eq. (2.17), p. 35: the shock to the present value of (scaled) surpluses,
`ε_{Σs,t+1} = ΔE_{t+1} ∑_{j ≥ 0} βʲ s̃_{t+1+j} = ∑_{j ≥ 0} βʲ ΔE_{t+1} s̃_{t+1+j}`. -/
noncomputable def pvNews (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' k, β ^ k * innov 𝔼 t (s (t + 1 + k)) ω

/-- Cochrane (2023), eqs. (2.17)–(2.18), p. 35: `E_t PV_{t+1} = ∑_{k ≥ 0} βᵏ E_t s_{t+1+k}`, with
`PV_{t+1} = E_{t+1} ∑ βᵏ s_{t+1+k}` the forward series (bounded surpluses, `0 ≤ β < 1`). -/
theorem E_forwardSeries_succ {β M : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (t : ℕ) (ω : Ω) :
    𝔼.E t (𝔼.forwardSeries β s (t + 1)) ω = ∑' k, β ^ k * 𝔼.E t (s (t + 1 + k)) ω := by
  have hb : ∀ k ω', |β ^ k * 𝔼.E (t + 1) (s (t + 1 + k)) ω'| ≤ β ^ k * M := by
    intro k ω'
    rw [abs_mul, abs_pow, abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hs (t + 1 + k)) (t + 1) ω') (pow_nonneg h0 k)
  change 𝔼.E t (fun ω' => ∑' k, β ^ k * 𝔼.E (t + 1) (s (t + 1 + k)) ω') ω = _
  rw [𝔼.E_tsum h0 h1 hb t ω]
  refine tsum_congr fun k => ?_
  change 𝔼.E t (β ^ k • 𝔼.E (t + 1) (s (t + 1 + k))) ω = _
  rw [map_smul, 𝔼.tower (Nat.le_succ t), Pi.smul_apply, smul_eq_mul]

/-- Cochrane (2023), eq. (2.17), p. 35: the innovation in the present value of surpluses is the
discounted sum of the innovations in each future surplus,
`ΔE_{t+1} PV_{t+1} = ∑_{k ≥ 0} βᵏ ΔE_{t+1} s_{t+1+k}` (bounded surpluses, `0 ≤ β < 1`). -/
theorem innov_forwardSeries {β M : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (t : ℕ) :
    innov 𝔼 t (𝔼.forwardSeries β s (t + 1)) = pvNews 𝔼 β s t := by
  funext ω
  unfold innov pvNews
  rw [𝔼.forwardSeries_adapted h0 h1 hs (t + 1), Pi.sub_apply,
    E_forwardSeries_succ 𝔼 h0 h1 hs t ω]
  change ∑' k, β ^ k * 𝔼.E (t + 1) (s (t + 1 + k)) ω - _ = _
  rw [← (summable_E_shift 𝔼 h0 h1 hs (t + 1) (t + 1) ω).tsum_sub
    (summable_E_shift 𝔼 h0 h1 hs t (t + 1) ω)]
  refine tsum_congr fun k => ?_
  rw [← mul_sub]
  rfl

/-- Cochrane (2023), p. 40 (terminology: a "shock" only moves unexpectedly): `ε_{t+1}` is known
at `t + 1` and `E_t ε_{t+1} = 0`. -/
def IsShock (ε : ℕ → Ω → ℝ) : Prop :=
  (∀ t, 𝔼.E (t + 1) (ε (t + 1)) = ε (t + 1)) ∧ ∀ t, 𝔼.E t (ε (t + 1)) = 0

/-- Cochrane (2023), eq. (2.17), p. 35: the fiscal news `ε_{Σs,t+1}` is a shock in the sense of
p. 40 (bounded surpluses, `0 ≤ β < 1`). -/
theorem pvNews_isShock {β M : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) : IsShock 𝔼 (fun t => match t with
      | 0 => 0
      | t + 1 => pvNews 𝔼 β s t) := by
  have hb : ∀ t k ω', |β ^ k * innov 𝔼 t (s (t + 1 + k)) ω'| ≤ β ^ k * (2 * M) := by
    intro t k ω'
    rw [abs_mul, abs_pow, abs_of_nonneg h0]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h0 k)
    unfold innov
    rw [Pi.sub_apply, two_mul]
    exact (abs_sub _ _).trans (add_le_add (𝔼.abs_E_le (hs _) _ ω') (𝔼.abs_E_le (hs _) _ ω'))
  constructor
  · intro t
    funext ω
    change 𝔼.E (t + 1) (fun ω' => ∑' k, β ^ k * innov 𝔼 t (s (t + 1 + k)) ω') ω = _
    rw [𝔼.E_tsum h0 h1 (hb t) (t + 1) ω]
    refine tsum_congr fun k => ?_
    change 𝔼.E (t + 1) (β ^ k • innov 𝔼 t (s (t + 1 + k))) ω = _
    rw [map_smul, innov_known_next, Pi.smul_apply, smul_eq_mul]
  · intro t
    funext ω
    change 𝔼.E t (fun ω' => ∑' k, β ^ k * innov 𝔼 t (s (t + 1 + k)) ω') ω = 0
    rw [𝔼.E_tsum h0 h1 (hb t) t ω]
    have : ∀ k, 𝔼.E t (fun ω' => β ^ k * innov 𝔼 t (s (t + 1 + k)) ω') ω = 0 := by
      intro k
      change 𝔼.E t (β ^ k • innov 𝔼 t (s (t + 1 + k))) ω = 0
      rw [map_smul, E_innov_zero, smul_zero, Pi.zero_apply]
    simp only [this, tsum_zero]

/-- Cochrane (2023), eq. (2.18), p. 35 (exact): from the Fisher equation and the valuation
equation at `t + 1`, `(B_t/P_t)/(1 + i_t) = (B_t/P_t) β E_t(P_t/P_{t+1}) = E_t ∑_{j ≥ 1} βʲ s_{t+j}`
(bounded surpluses, `0 ≤ β < 1`; `B_t/P_t` known at `t`). -/
theorem debt_218 (hPO : 𝔼.PullOut) {β M : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) {i B P s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) {t : ℕ} (hP : ∀ ω, P t ω ≠ 0) (hfis : FisherExact 𝔼 β i P t)
    (hV : 𝔼.E t (fun ω => B t ω / P t ω) = fun ω => B t ω / P t ω)
    (hval : (fun ω => B t ω / P (t + 1) ω) = 𝔼.forwardSeries β s (t + 1)) (ω : Ω) :
    B t ω / P t ω * (1 / (1 + i t ω)) = ∑' k, β ^ (k + 1) * 𝔼.E t (s (t + 1 + k)) ω := by
  rw [hfis ω]
  have hpull := congrFun (hPO t _ (fun ω' => P t ω' / P (t + 1) ω') hV) ω
  have hprod : ((fun ω => B t ω / P t ω) * fun ω' => P t ω' / P (t + 1) ω') =
      fun ω => B t ω / P (t + 1) ω := by
    funext ω'
    simp only [Pi.mul_apply]
    rw [div_mul_div_comm, mul_comm (P t ω'), mul_div_mul_right _ _ (hP ω')]
  rw [hprod, hval, Pi.mul_apply] at hpull
  calc B t ω / P t ω * (β * 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω)
      = β * (B t ω / P t ω * 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω) := by ring
    _ = β * ∑' k, β ^ k * 𝔼.E t (s (t + 1 + k)) ω := by
        rw [← hpull, E_forwardSeries_succ 𝔼 h0 h1 hs t ω]
    _ = _ := by
        rw [← tsum_mul_left]
        refine tsum_congr fun k => ?_
        ring

/-- Cochrane (2023), eq. (2.17), p. 35, the LINEAR (2.17) as the first derivative of the exact
(2.17): consider a family of economies indexed by `ε` with `π_{t+1} = ε π̂` (so
`P_t/P_{t+1} = exp(−ε π̂)`), PV news `ε V ΔE_{t+1} S̃` (surpluses scaled by steady-state debt
`V ≠ 0`, `s̃ = s/V`), and value of debt `V_t(ε)` differentiable with `V_t(0) = V`. If the exact
(2.17) holds along the family, then `ΔE_{t+1} π̂ = −ΔE_{t+1} S̃`. -/
theorem linear_217 {K V v' : ℝ} {πh S : Ω → ℝ} (hb : ∀ ω, |πh ω| ≤ K) (hV : V ≠ 0)
    {Vt : ℝ → ℝ} (hVt : HasDerivAt Vt v' 0) (hV0 : Vt 0 = V) (t : ℕ) (ω : Ω)
    (hfam : ∀ ε, Vt ε * innov 𝔼 t (fun ω' => Real.exp (ε * -πh ω')) ω =
      ε * V * innov 𝔼 t S ω) :
    innov 𝔼 t πh ω = -innov 𝔼 t S ω := by
  have hX : ∀ ω', |(fun ω'' => -πh ω'') ω'| ≤ K := fun ω' => by
    simpa only [abs_neg] using hb ω'
  have hneg : ∀ n, 𝔼.E n (fun ω'' => -πh ω'') ω = -𝔼.E n πh ω := fun n => by
    change 𝔼.E n (-πh) ω = _
    rw [map_neg, Pi.neg_apply]
  have hg : HasDerivAt (fun ε => innov 𝔼 t (fun ω' => Real.exp (ε * -πh ω')) ω)
      (-innov 𝔼 t πh ω) 0 := by
    have h := HasDerivAt.sub (hasDerivAt_E_exp 𝔼 hX (t + 1) ω) (hasDerivAt_E_exp 𝔼 hX t ω)
    rw [hneg, hneg] at h
    have e : (fun ε => innov 𝔼 t (fun ω' => Real.exp (ε * -πh ω')) ω) =
        (fun ε => 𝔼.E (t + 1) (fun ω' => Real.exp (ε * -πh ω')) ω) -
          fun ε => 𝔼.E t (fun ω' => Real.exp (ε * -πh ω')) ω := by
      funext ε
      rfl
    rw [e]
    convert h using 1
    unfold innov
    rw [Pi.sub_apply]
    ring
  have hg0 : innov 𝔼 t (fun ω' => Real.exp (0 * -πh ω')) ω = 0 := by
    simp only [zero_mul, Real.exp_zero]
    rw [innov_const, Pi.zero_apply]
  have hL := hVt.mul hg
  rw [hg0, hV0, mul_zero, zero_add] at hL
  have hR : HasDerivAt (fun ε : ℝ => ε * V * innov 𝔼 t S ω) (V * innov 𝔼 t S ω) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const V).mul_const (innov 𝔼 t S ω)
    simpa using this
  have hfun : (Vt * fun ε => innov 𝔼 t (fun ω' => Real.exp (ε * -πh ω')) ω) =
      fun ε => ε * V * innov 𝔼 t S ω := funext hfam
  rw [hfun] at hL
  have h := hL.unique hR
  have h2 : V * (innov 𝔼 t πh ω + innov 𝔼 t S ω) = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hV
  · linarith

/-! ### (2.19): the interest-rate peg -/

/-- Cochrane (2023), eqs. (2.16)–(2.17), p. 35 (the linear model, variables as deviations from
steady state): `i_t = E_t π_{t+1}` and `ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` at every date. -/
def PegModel (i ε π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = 𝔼.E t (π (t + 1)) ∧ innov 𝔼 t (π (t + 1)) = -ε (t + 1)

/-- Cochrane (2023), eq. (2.19), p. 36: for adapted inflation, an adapted rate path and a fiscal
shock, the model (2.16)–(2.17) holds iff `π_{t+1} = i_t − ε_{Σs,t+1}` at every date. -/
theorem pegModel_iff {i ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hi : 𝔼.Adapted i)
    (hε : IsShock 𝔼 ε) : PegModel 𝔼 i ε π ↔ ∀ t, π (t + 1) = i t - ε (t + 1) := by
  constructor
  · intro h t
    rw [eq_E_add_innov 𝔼 (hπ (t + 1)), ← (h t).1, (h t).2, sub_eq_add_neg]
  · intro h t
    have hE : 𝔼.E t (π (t + 1)) = i t := by
      rw [h t, map_sub, hi t, hε.2 t, sub_zero]
    refine ⟨hE.symm, ?_⟩
    unfold innov
    rw [hE, h t, map_sub, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hi t), hε.1 t]
    abel

/-- Cochrane (2023), eq. (2.19), p. 36: the solution `π_0` given, `π_{t+1} = i_t − ε_{Σs,t+1}`. -/
def pegSol (i ε : ℕ → Ω → ℝ) (π0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => π0
  | t + 1 => i t - ε (t + 1)

/-- Cochrane (2023), eq. (2.19), p. 36: the solution is adapted. -/
theorem pegSol_adapted {i ε : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hi : 𝔼.Adapted i) (hε : IsShock 𝔼 ε) : 𝔼.Adapted (pegSol i ε π0) := by
  intro t
  cases t with
  | zero => exact h0
  | succ t =>
    change 𝔼.E (t + 1) (i t - ε (t + 1)) = i t - ε (t + 1)
    rw [map_sub, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hi t), hε.1 t]

/-- Cochrane (2023), eq. (2.19), p. 36 ("the full solution of the model"): for EVERY adapted rate
path `i` and every fiscal shock `ε_{Σs}`, given `π_0` (set by date-0 fiscal news), the model
(2.16)–(2.17) has exactly one adapted solution. No boundedness is imposed. -/
theorem peg_existsUnique {i ε : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hi : 𝔼.Adapted i) (hε : IsShock 𝔼 ε) :
    ∃! π, 𝔼.Adapted π ∧ π 0 = π0 ∧ PegModel 𝔼 i ε π := by
  have ha := pegSol_adapted 𝔼 h0 hi hε
  refine ⟨pegSol i ε π0, ⟨ha, rfl, (pegModel_iff 𝔼 ha hi hε).mpr fun t => rfl⟩, ?_⟩
  rintro π ⟨hπ, hπ0, hm⟩
  have h := (pegModel_iff 𝔼 hπ hi hε).mp hm
  funext t
  cases t with
  | zero => exact hπ0
  | succ t => exact h t

/-- Cochrane (2023), pp. 33, 37 ("inflation is stable under an interest-rate target"): with
bounded `π_0`, rates and shocks the solution (2.19) is bounded. -/
theorem pegSol_bounded {i ε : ℕ → Ω → ℝ} {π0 : Ω → ℝ} {A Bi Be : ℝ} (h0 : ∀ ω, |π0 ω| ≤ A)
    (hi : ∀ t ω, |i t ω| ≤ Bi) (hε : ∀ t ω, |ε t ω| ≤ Be) :
    BoundedProc (pegSol i ε π0) := by
  refine ⟨|A| + |Bi| + |Be|, fun t ω => ?_⟩
  cases t with
  | zero =>
    have := (h0 ω).trans (le_abs_self A)
    change |π0 ω| ≤ _
    linarith [abs_nonneg Bi, abs_nonneg Be]
  | succ t =>
    change |i t ω - ε (t + 1) ω| ≤ _
    have h1 := (hi t ω).trans (le_abs_self Bi)
    have h2 := (hε (t + 1) ω).trans (le_abs_self Be)
    linarith [abs_sub (i t ω) (ε (t + 1) ω), abs_nonneg A]

/-! ### Figure 2.1: impulse responses as innovations -/

/-- Cochrane (2023), p. 40 (a shock "only moves unexpectedly"): a later shock has no innovation
at an earlier date, `ΔE_{t+1} ε_{t+2+j} = 0`. -/
theorem innov_shock_later {ε : ℕ → Ω → ℝ} (hε : IsShock 𝔼 ε) (t j : ℕ) :
    innov 𝔼 t (ε (t + 2 + j)) = 0 := by
  have e : t + 2 + j = t + 1 + j + 1 := by omega
  rw [e]
  unfold innov
  rw [← 𝔼.tower (show t + 1 ≤ t + 1 + j by omega), hε.2, map_zero,
    ← 𝔼.tower (show t ≤ t + 1 + j by omega), hε.2, map_zero, sub_zero]

/-- Cochrane (2023), Figure 2.1 and p. 36 ("there is no unexpected time-`t` inflation without a
fiscal shock"): on impact, `ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` whatever the rate news. -/
theorem irf_peg_impact {i ε π : ℕ → Ω → ℝ} (hi : 𝔼.Adapted i) (hε : IsShock 𝔼 ε)
    (h : ∀ t, π (t + 1) = i t - ε (t + 1)) (t : ℕ) :
    innov 𝔼 t (π (t + 1)) = -ε (t + 1) := by
  rw [h t, innov_sub, innov_of_known 𝔼 (hi t)]
  unfold innov
  rw [hε.1 t, hε.2 t]
  abel

/-- Cochrane (2023), Figure 2.1 and p. 36 ("inflation moves up one period later"): after impact
the inflation response is the rate response one period earlier,
`ΔE_{t+1} π_{t+2+j} = ΔE_{t+1} i_{t+1+j}`. -/
theorem irf_peg_later {i ε π : ℕ → Ω → ℝ} (hε : IsShock 𝔼 ε)
    (h : ∀ t, π (t + 1) = i t - ε (t + 1)) (t j : ℕ) :
    innov 𝔼 t (π (t + 2 + j)) = innov 𝔼 t (i (t + 1 + j)) := by
  have e : t + 2 + j = t + 1 + j + 1 := by omega
  rw [e, h, innov_sub, ← e, innov_shock_later 𝔼 hε, sub_zero]

/-- Cochrane (2023), Figure 2.1, top panel: a permanent interest-rate shock at `t + 1` (news
`ΔE_{t+1} i_{t+1+j} = 1` for all `j`) with no fiscal shock gives no inflation on impact and
inflation `1` from `t + 2` on. -/
theorem fig21_rate {i ε π : ℕ → Ω → ℝ} (hi : 𝔼.Adapted i) (hε : IsShock 𝔼 ε)
    (h : ∀ t, π (t + 1) = i t - ε (t + 1)) {t : ℕ} {ω : Ω} (hε0 : ε (t + 1) ω = 0)
    (hnews : ∀ j, innov 𝔼 t (i (t + 1 + j)) ω = 1) :
    innov 𝔼 t (π (t + 1)) ω = 0 ∧ ∀ j, innov 𝔼 t (π (t + 2 + j)) ω = 1 := by
  refine ⟨?_, fun j => ?_⟩
  · rw [irf_peg_impact 𝔼 hi hε h t, Pi.neg_apply, hε0, neg_zero]
  · rw [irf_peg_later 𝔼 hε h t j, hnews j]

/-- Cochrane (2023), Figure 2.1, bottom panel: a fiscal shock `ε_{Σs,t+1} = −1` with no interest
rate news gives a one-period inflation `1` on impact and nothing afterwards. -/
theorem fig21_fiscal {i ε π : ℕ → Ω → ℝ} (hi : 𝔼.Adapted i) (hε : IsShock 𝔼 ε)
    (h : ∀ t, π (t + 1) = i t - ε (t + 1)) {t : ℕ} {ω : Ω} (hε1 : ε (t + 1) ω = -1)
    (hnews : ∀ j, innov 𝔼 t (i (t + 1 + j)) ω = 0) :
    innov 𝔼 t (π (t + 1)) ω = 1 ∧ ∀ j, innov 𝔼 t (π (t + 2 + j)) ω = 0 := by
  refine ⟨?_, fun j => ?_⟩
  · rw [irf_peg_impact 𝔼 hi hε h t, Pi.neg_apply, hε1, neg_neg]
  · rw [irf_peg_later 𝔼 hε h t j, hnews j]

/-! ### Announcements (p. 36) -/

/-- Cochrane (2023), p. 36 ("If `E_{t−k} i_t` rises, then `E_{t−k} π_{t+1}` rises"): for every
`s ≤ t`, `E_s π_{t+1} = E_s i_t`. -/
theorem expected_inflation_ahead {i ε π : ℕ → Ω → ℝ} (hε : IsShock 𝔼 ε)
    (h : ∀ t, π (t + 1) = i t - ε (t + 1)) {s t : ℕ} (hst : s ≤ t) :
    𝔼.E s (π (t + 1)) = 𝔼.E s (i t) := by
  rw [h t, map_sub, ← 𝔼.tower hst (ε (t + 1)), hε.2 t, map_zero, sub_zero]

/-- Cochrane (2023), p. 36 ("The response is the same if the interest-rate movement is announced
ahead of time"): two information structures `𝔼₁`, `𝔼₂` (e.g. the rate path announced early, or
revealed date by date) with the same realised adapted rate path, no fiscal shocks and the same
`π_0` give the same inflation path. -/
theorem announcement_invariant (𝔼₁ 𝔼₂ : ExpectationSystem Ω) {i π₁ π₂ : ℕ → Ω → ℝ}
    (hi₁ : 𝔼₁.Adapted i) (hi₂ : 𝔼₂.Adapted i) (hπ₁ : 𝔼₁.Adapted π₁) (hπ₂ : 𝔼₂.Adapted π₂)
    (h₁ : PegModel 𝔼₁ i 0 π₁) (h₂ : PegModel 𝔼₂ i 0 π₂) (h0 : π₁ 0 = π₂ 0) : π₁ = π₂ := by
  have hs₁ : IsShock 𝔼₁ 0 := ⟨fun t => map_zero _, fun t => map_zero _⟩
  have hs₂ : IsShock 𝔼₂ 0 := ⟨fun t => map_zero _, fun t => map_zero _⟩
  have e₁ := (pegModel_iff 𝔼₁ hπ₁ hi₁ hs₁).mp h₁
  have e₂ := (pegModel_iff 𝔼₂ hπ₂ hi₂ hs₂).mp h₂
  funext t
  cases t with
  | zero => exact h0
  | succ t => rw [e₁ t, e₂ t]

/-- Cochrane (2023), p. 36 ("in many models announcements of future policy can affect the
economy on the date of the announcement. Not in this case"): two rate paths that agree before
date `T` give the same inflation up to and including date `T`. -/
theorem no_announcement_effect {i i' ε π π' : ℕ → Ω → ℝ}
    (h : ∀ t, π (t + 1) = i t - ε (t + 1)) (h' : ∀ t, π' (t + 1) = i' t - ε (t + 1))
    (h0 : π 0 = π' 0) {T : ℕ} (hii : ∀ s < T, i s = i' s) : ∀ s ≤ T, π s = π' s := by
  intro s hs
  cases s with
  | zero => exact h0
  | succ s => rw [h s, h' s, hii s (by omega)]

/-- Cochrane (2023), p. 37 ("in the long run higher nominal interest rates must come with
higher inflation"): a constant rate `c` and no fiscal shocks give `π_{t+1} = c`. -/
theorem long_run_fisher {i ε π : ℕ → Ω → ℝ} {c : ℝ} (h : ∀ t, π (t + 1) = i t - ε (t + 1))
    (hc : ∀ t, i t = fun _ => c) (hε : ε = 0) (t : ℕ) : π (t + 1) = fun _ => c := by
  rw [h t, hc t, hε, Pi.zero_apply, sub_zero]

/-! ### Fiscal news: inflation when the news arrives (Figure 2.1, "expected fiscal shock") -/

/-- Cochrane (2023), Figure 2.1 and pp. 36–37: a random variable revealed at date `a + 1`
(`E_{a+1} x = x`, `E_a x = 0`) has innovation `x` at `a + 1` and none at any other date. -/
theorem innov_of_news {a : ℕ} {x : Ω → ℝ} (hxa : 𝔼.E (a + 1) x = x) (hx0 : 𝔼.E a x = 0)
    (t : ℕ) : innov 𝔼 t x = if t = a then x else 0 := by
  unfold innov
  rcases lt_trichotomy t a with hlt | heq | hgt
  · simp only [hlt.ne, ↓reduceIte]
    rw [← 𝔼.tower (show t + 1 ≤ a by omega), hx0, map_zero,
      ← 𝔼.tower hlt.le, hx0, map_zero, sub_zero]
  · subst heq
    simp only [↓reduceIte]
    rw [hxa, hx0, sub_zero]
  · simp only [hgt.ne', ↓reduceIte]
    rw [ForwardSolution.E_of_known 𝔼 (show a + 1 ≤ t + 1 by omega) hxa,
      ForwardSolution.E_of_known 𝔼 (show a + 1 ≤ t by omega) hxa, sub_self]

/-- Cochrane (2023), Figure 2.1 and pp. 36–37 ("The fiscal shock is a shock to the present value
of surpluses, so when surpluses actually change does not matter"): with surpluses
`s_k = c_k + D_k x`, `x` revealed at `a + 1`, the PV news is
`(∑ₖ βᵏ D_{a+1+k}) x` at date `a + 1` and zero at every other date, whatever the profile `D` of
the surplus change. -/
theorem pvNews_of_news {β : ℝ} {c D : ℕ → ℝ} {a : ℕ} {x : Ω → ℝ} (hxa : 𝔼.E (a + 1) x = x)
    (hx0 : 𝔼.E a x = 0) (t : ℕ) :
    pvNews 𝔼 β (fun k ω => c k + D k * x ω) t =
      fun ω => if t = a then (∑' k, β ^ k * D (a + 1 + k)) * x ω else 0 := by
  funext ω
  have hk : ∀ k, innov 𝔼 t (fun ω' => c (t + 1 + k) + D (t + 1 + k) * x ω') ω =
      D (t + 1 + k) * (if t = a then x ω else 0) := by
    intro k
    have e : (fun ω' => c (t + 1 + k) + D (t + 1 + k) * x ω') =
        (fun _ => c (t + 1 + k)) + D (t + 1 + k) • x := by
      funext ω'
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [e, innov_add, innov_const, innov_smul, innov_of_news 𝔼 hxa hx0 t, zero_add]
    split_ifs <;> simp
  change ∑' k, β ^ k * innov 𝔼 t (fun ω' => c (t + 1 + k) + D (t + 1 + k) * x ω') ω = _
  simp_rw [hk]
  split_ifs with ht
  · subst ht
    rw [← tsum_mul_right]
    refine tsum_congr fun k => ?_
    ring
  · simp

/-- Cochrane (2023), Figure 2.1, "expected fiscal shock" (pp. 36–37: "Inflation happens when the
shock is announced, not when surpluses appear"): with no rate response (`i = 0`) and fiscal
shocks equal to the PV news of surpluses `s_k = c_k + D_k x` announced at `a + 1`, inflation is
`−(∑ₖ βᵏ D_{a+1+k}) x` at the announcement date `a + 1` and zero at every other date, however
late the surpluses actually change. -/
theorem fig21_expected_fiscal {β : ℝ} {c D : ℕ → ℝ} {a : ℕ} {x : Ω → ℝ}
    (hxa : 𝔼.E (a + 1) x = x) (hx0 : 𝔼.E a x = 0) {π : ℕ → Ω → ℝ}
    (h : ∀ t, π (t + 1) = 0 - pvNews 𝔼 β (fun k ω => c k + D k * x ω) t) (t : ℕ) :
    π (t + 1) = fun ω => if t = a then -((∑' k, β ^ k * D (a + 1 + k)) * x ω) else 0 := by
  rw [h t, pvNews_of_news 𝔼 hxa hx0 t]
  funext ω
  split_ifs <;> simp

/-! ### §2.5.1: a fiscal price-level target -/

/-- Cochrane (2023), §2.5.1, p. 38: if fiscal policy attains the target `p_{t+1} = p*_{t+1}`
and the Fisher equation `i_t = E_t(p_{t+1} − p_t)` holds (log price level `p`, known at `t`),
then `p_t = E_t p*_{t+1} − i_t`. -/
theorem pTarget_price {i p pstar : ℕ → Ω → ℝ} {t : ℕ} (hp : 𝔼.E t (p t) = p t)
    (hfis : i t = 𝔼.E t (p (t + 1) - p t)) (htarget : p (t + 1) = pstar (t + 1)) :
    p t = 𝔼.E t (pstar (t + 1)) - i t := by
  rw [hfis, map_sub, hp, htarget]
  abel

/-- Cochrane (2023), §2.5.1, p. 38 ("A higher interest rate now immediately lowers inflation"):
with the same targets, a higher rate `i'_t > i_t` gives a lower price level `p'_t < p_t`, hence
lower inflation `p'_t − p_{t−1} < p_t − p_{t−1}`. -/
theorem pTarget_rate_lowers_price {i i' p p' pstar : ℕ → Ω → ℝ} {t : ℕ}
    (hp : 𝔼.E t (p t) = p t) (hp' : 𝔼.E t (p' t) = p' t)
    (hfis : i t = 𝔼.E t (p (t + 1) - p t)) (hfis' : i' t = 𝔼.E t (p' (t + 1) - p' t))
    (htarget : p (t + 1) = pstar (t + 1)) (htarget' : p' (t + 1) = pstar (t + 1)) {ω : Ω}
    (hlt : i t ω < i' t ω) (q : ℝ) : p' t ω < p t ω ∧ p' t ω - q < p t ω - q := by
  have h1 := congrFun (pTarget_price 𝔼 hp hfis htarget) ω
  have h2 := congrFun (pTarget_price 𝔼 hp' hfis' htarget') ω
  simp only [Pi.sub_apply] at h1 h2
  constructor <;> linarith

/-- Cochrane (2023), §2.5.1, p. 38 ("To defend the price level targets ... the fiscal authority
will be induced to raise future surpluses"): with targets `p*_{t+2}` known at `t`, the linear
valuation equation `ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` forces the fiscal shock to equal the rate
news, `ε_{Σs,t+1} = ΔE_{t+1} i_{t+1}`. -/
theorem pTarget_fiscal_contraction {i p pstar ε : ℕ → Ω → ℝ} (hp : 𝔼.Adapted p)
    (hfis : ∀ t, i t = 𝔼.E t (p (t + 1) - p t)) (htarget : ∀ t, p (t + 1) = pstar (t + 1))
    {t : ℕ} (hstar : 𝔼.E t (pstar (t + 2)) = pstar (t + 2))
    (h221 : innov 𝔼 t (p (t + 1) - p t) = -ε (t + 1)) : ε (t + 1) = innov 𝔼 t (i (t + 1)) := by
  have hp1 := pTarget_price 𝔼 (hp (t + 1)) (hfis (t + 1)) (htarget (t + 1))
  have hk : 𝔼.E (t + 1) (pstar (t + 1 + 1)) = pstar (t + 2) :=
    ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) hstar
  rw [hk] at hp1
  rw [innov_sub, innov_of_known 𝔼 (hp t), sub_zero, hp1, innov_sub,
    innov_of_known 𝔼 hstar, zero_sub] at h221
  exact (neg_inj.mp h221).symm

/-- Cochrane (2023), §2.5.1, p. 38 ("then we are at a loggerhead"): if fiscal policy also sets
`p_t = p*_t` (targets known at `t`), the Fisher equation leaves monetary policy no freedom:
`i_t = p*_{t+1} − p*_t`. -/
theorem loggerhead {i p pstar : ℕ → Ω → ℝ} {t : ℕ} (hstar : 𝔼.E t (pstar (t + 1)) = pstar (t + 1))
    (hp : 𝔼.E t (p t) = p t) (hfis : i t = 𝔼.E t (p (t + 1) - p t)) (h1 : p t = pstar t)
    (h2 : p (t + 1) = pstar (t + 1)) : i t = pstar (t + 1) - pstar t := by
  rw [pTarget_price 𝔼 hp hfis h2, hstar] at h1
  rw [← h1]
  abel

/-- Cochrane (2023), p. 38 (survey error E6, corrected): `ΔE_{t+1} π_{t+1} = ΔE_{t+1} p_{t+1}`
(`p_t` is known at `t`, so it has no innovation). -/
theorem innov_pi_eq_innov_p {p : ℕ → Ω → ℝ} {t : ℕ} (hp : 𝔼.E t (p t) = p t) :
    innov 𝔼 t (p (t + 1) - p t) = innov 𝔼 t (p (t + 1)) := by
  rw [innov_sub, innov_of_known 𝔼 hp, sub_zero]

/-- Cochrane (2023), p. 38, survey error E6: the printed `ΔE_t π_t = ΔE_t p_t − p_{t−1}` is false
(perfect foresight with `p ≡ 1`: the left side is `0`, the right side `−1`). -/
theorem printed_E6_false : ∃ p : ℕ → Unit → ℝ, perfectForesight.Adapted p ∧
    innov perfectForesight 0 (p 1 - p 0) ≠ innov perfectForesight 0 (p 1) - p 0 := by
  refine ⟨fun _ _ => 1, fun _ => rfl, fun h => ?_⟩
  have := congrFun h ()
  simp [innov, perfectForesight] at this

/-! ### p. 39: passive fiscal policy -/

/-- Cochrane (2023), p. 39: the passive fiscal policy of the new-Keynesian reading,
`ε_{Σs,t+1} = −ΔE_{t+1} π_{t+1}` "in response to whatever inflation happens". -/
def passiveShock (π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => -innov 𝔼 t (π (t + 1))

/-- Cochrane (2023), p. 39: under passive fiscal policy the valuation equation holds for every
inflation path satisfying the Fisher equation. -/
theorem passive_valuation_holds {i π : ℕ → Ω → ℝ} (hfis : ∀ t, i t = 𝔼.E t (π (t + 1))) :
    PegModel 𝔼 i (passiveShock 𝔼 π) π := fun t => ⟨hfis t, by
      change _ = -(-innov 𝔼 t (π (t + 1)))
      rw [neg_neg]⟩

/-- Cochrane (2023), p. 39 ("The bank threatens hyperinflation for any but one value of
unexpected inflation"): with passive fiscal policy, EVERY shock `ν` is an equilibrium inflation
innovation: `π_{t+1} = i_t + ν_{t+1}` is adapted, satisfies the model with the passive fiscal
response, and has `ΔE_{t+1} π_{t+1} = ν_{t+1}`. -/
theorem passive_any_innovation {i ν : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hi : 𝔼.Adapted i) (hν : IsShock 𝔼 ν) :
    𝔼.Adapted (pegSol i (fun t => -ν t) π0) ∧
      PegModel 𝔼 i (passiveShock 𝔼 (pegSol i (fun t => -ν t) π0)) (pegSol i (fun t => -ν t) π0) ∧
      ∀ t, innov 𝔼 t (pegSol i (fun t => -ν t) π0 (t + 1)) = ν (t + 1) := by
  have hs : IsShock 𝔼 (fun t => -ν t) :=
    ⟨fun t => by rw [map_neg, hν.1 t], fun t => by rw [map_neg, hν.2 t, neg_zero]⟩
  have ha := pegSol_adapted 𝔼 h0 hi hs
  have hm := (pegModel_iff 𝔼 ha hi hs).mpr fun t => rfl
  refine ⟨ha, passive_valuation_holds 𝔼 fun t => (hm t).1, fun t => ?_⟩
  rw [(hm t).2, neg_neg]

/-! ### §2.6: interest-rate rules, (2.20)–(2.25) -/

/-- Cochrane (2023), p. 40: a shock's innovation on arrival is the shock itself,
`ΔE_{t+1} ε_{t+1} = ε_{t+1}`. -/
theorem innov_shock {ε : ℕ → Ω → ℝ} (hε : IsShock 𝔼 ε) (t : ℕ) :
    innov 𝔼 t (ε (t + 1)) = ε (t + 1) := by
  unfold innov
  rw [hε.1 t, hε.2 t, sub_zero]

/-- Cochrane (2023), eqs. (2.20)–(2.22), p. 40: `i_t = E_t π_{t+1}`,
`ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` and the Taylor-type rule `i_t = θ π_t + u_t`. -/
def RuleModel (θ : ℝ) (i u ε π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = 𝔼.E t (π (t + 1)) ∧ innov 𝔼 t (π (t + 1)) = -ε (t + 1) ∧ i t = θ • π t + u t

/-- Cochrane (2023), eq. (2.23), p. 40: the serially correlated disturbance
`u_t = η u_{t−1} + ε_{i,t}`. -/
def Disturbance (η : ℝ) (u εi : ℕ → Ω → ℝ) : Prop := ∀ t, u (t + 1) = η • u t + εi (t + 1)

/-- Cochrane (2023), eq. (2.24) with (2.21), p. 40: `E_t π_{t+1} = θ π_t + u_t` and
`ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}`. -/
def Eq224 (θ : ℝ) (u ε π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, 𝔼.E t (π (t + 1)) = θ • π t + u t ∧ innov 𝔼 t (π (t + 1)) = -ε (t + 1)

/-- Cochrane (2023), eqs. (2.20)–(2.24), p. 40 ("Eliminating the interest rate"): the model
(2.20)–(2.22) holds iff the rate is given by the rule and inflation satisfies (2.24), (2.21). -/
theorem ruleModel_iff {θ : ℝ} {i u ε π : ℕ → Ω → ℝ} :
    RuleModel 𝔼 θ i u ε π ↔ (∀ t, i t = θ • π t + u t) ∧ Eq224 𝔼 θ u ε π := by
  constructor
  · intro h
    exact ⟨fun t => (h t).2.2, fun t => ⟨(h t).1.symm.trans (h t).2.2, (h t).2.1⟩⟩
  · rintro ⟨hi, h⟩ t
    exact ⟨(hi t).trans (h t).1.symm, (h t).2, hi t⟩

/-- Cochrane (2023), eq. (2.25), p. 40: for adapted inflation and disturbance and a fiscal shock,
(2.24) with (2.21) holds iff `π_{t+1} = θ π_t + u_t − ε_{Σs,t+1}`. -/
theorem eq224_iff {θ : ℝ} {u ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hu : 𝔼.Adapted u)
    (hε : IsShock 𝔼 ε) :
    Eq224 𝔼 θ u ε π ↔ ∀ t, π (t + 1) = θ • π t + u t - ε (t + 1) := by
  have hk : ∀ t, 𝔼.E t (θ • π t + u t) = θ • π t + u t := fun t => by
    rw [map_add, map_smul, hπ t, hu t]
  constructor
  · intro h t
    rw [eq_E_add_innov 𝔼 (hπ (t + 1)), (h t).1, (h t).2, sub_eq_add_neg]
  · intro h t
    refine ⟨?_, ?_⟩
    · rw [h t, map_sub, hk t, hε.2 t, sub_zero]
    · rw [h t, innov_sub, innov_of_known 𝔼 (hk t), innov_shock 𝔼 hε, zero_sub]

/-- Cochrane (2023), eq. (2.25), p. 40: the solution `π_0` given,
`π_{t+1} = θ π_t + u_t − ε_{Σs,t+1}`. -/
def ruleSol (θ : ℝ) (u ε : ℕ → Ω → ℝ) (π0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => π0
  | t + 1 => θ • ruleSol θ u ε π0 t + u t - ε (t + 1)

/-- Cochrane (2023), eq. (2.25), p. 40: the solution is adapted. -/
theorem ruleSol_adapted {θ : ℝ} {u ε : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hu : 𝔼.Adapted u) (hε : IsShock 𝔼 ε) : 𝔼.Adapted (ruleSol θ u ε π0) := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
    change 𝔼.E (t + 1) (θ • ruleSol θ u ε π0 t + u t - ε (t + 1)) = _
    rw [map_sub, map_add, map_smul, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih,
      ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hu t), hε.1 t]
    rfl

/-- Cochrane (2023), eqs. (2.20)–(2.25), p. 40, the fiscal-theory point of §2.6: for EVERY rule
coefficient `θ ∈ ℝ` (no Taylor principle), every adapted disturbance `u` and every fiscal shock,
given `π_0`, there is exactly one equilibrium `(π, i)` of (2.20)–(2.22) with `π` adapted. -/
theorem rule_existsUnique (θ : ℝ) {u ε : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hu : 𝔼.Adapted u) (hε : IsShock 𝔼 ε) :
    ∃! q : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), 𝔼.Adapted q.1 ∧ q.1 0 = π0 ∧
      RuleModel 𝔼 θ q.2 u ε q.1 := by
  have ha := ruleSol_adapted 𝔼 (θ := θ) h0 hu hε
  refine ⟨(ruleSol θ u ε π0, fun t => θ • ruleSol θ u ε π0 t + u t), ⟨ha, rfl, ?_⟩, ?_⟩
  · exact (ruleModel_iff 𝔼).mpr ⟨fun t => rfl, (eq224_iff 𝔼 ha hu hε).mpr fun t => rfl⟩
  · rintro ⟨π, i⟩ ⟨hπ, hπ0, hm⟩
    obtain ⟨hi, h224⟩ := (ruleModel_iff 𝔼).mp hm
    have h := (eq224_iff 𝔼 hπ hu hε).mp h224
    dsimp only at hπ0 hi h
    have hπeq : π = ruleSol θ u ε π0 := by
      funext t
      induction t with
      | zero => exact hπ0
      | succ t ih =>
        rw [h t, ih]
        rfl
    refine Prod.ext hπeq ?_
    funext t
    change i t = θ • ruleSol θ u ε π0 t + u t
    rw [hi t, hπeq]

/-- Cochrane (2023), p. 40 ("if we had fed the equilibrium `{i_t}` response ... into the
calculation (2.19) ... as if that path were an exogenous time-varying peg, we would have obtained
the same result"): a solution of the rule model solves the peg model (2.16)–(2.17) with the
equilibrium rate, and equals the peg solution (2.19) for that rate. -/
theorem rule_eq_peg {θ : ℝ} {i u ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hu : 𝔼.Adapted u)
    (hε : IsShock 𝔼 ε) (hm : RuleModel 𝔼 θ i u ε π) :
    PegModel 𝔼 i ε π ∧ π = pegSol i ε (π 0) := by
  have hpeg : PegModel 𝔼 i ε π := fun t => ⟨(hm t).1, (hm t).2.1⟩
  have hi : 𝔼.Adapted i := fun t => by rw [(hm t).2.2, map_add, map_smul, hπ t, hu t]
  refine ⟨hpeg, ?_⟩
  have h := (pegModel_iff 𝔼 hπ hi hε).mp hpeg
  funext t
  cases t with
  | zero => rfl
  | succ t => exact h t

/-- Cochrane (2023), §2.6 (survey item E30): for `|θ| < 1` and bounded `π_0`, disturbance and
shocks, the equilibrium (2.25) is bounded. -/
theorem ruleSol_bounded {θ A Bu Be : ℝ} (hθ : |θ| < 1) {u ε : ℕ → Ω → ℝ} {π0 : Ω → ℝ}
    (h0 : ∀ ω, |π0 ω| ≤ A) (hu : ∀ t ω, |u t ω| ≤ Bu) (hε : ∀ t ω, |ε t ω| ≤ Be) :
    BoundedProc (ruleSol θ u ε π0) := by
  set K := |A| + (|Bu| + |Be|) / (1 - |θ|) with hK
  have h1 : 0 < 1 - |θ| := by linarith
  have hfrac : 0 ≤ (|Bu| + |Be|) / (1 - |θ|) := div_nonneg (by positivity) h1.le
  refine ⟨K, fun t => ?_⟩
  induction t with
  | zero => exact fun ω => (h0 ω).trans ((le_abs_self A).trans (by linarith))
  | succ t ih =>
    intro ω
    change |θ * ruleSol θ u ε π0 t ω + u t ω - ε (t + 1) ω| ≤ K
    have ha : |θ * ruleSol θ u ε π0 t ω| ≤ |θ| * K := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (ih ω) (abs_nonneg _)
    have hb := (hu t ω).trans (le_abs_self Bu)
    have hc := (hε (t + 1) ω).trans (le_abs_self Be)
    have hKe : K * (1 - |θ|) = |A| * (1 - |θ|) + (|Bu| + |Be|) := by
      rw [hK, add_mul, div_mul_cancel₀ _ h1.ne']
    have hB : 0 ≤ |A| * (1 - |θ|) := mul_nonneg (abs_nonneg A) h1.le
    calc |θ * ruleSol θ u ε π0 t ω + u t ω - ε (t + 1) ω|
        ≤ |θ * ruleSol θ u ε π0 t ω + u t ω| + |ε (t + 1) ω| := abs_sub _ _
      _ ≤ |θ * ruleSol θ u ε π0 t ω| + |u t ω| + |ε (t + 1) ω| := by
          gcongr; exact abs_add_le _ _
      _ ≤ K := by nlinarith

/-- Cochrane (2023), §2.6 (survey item E30): for `|θ| > 1` the equilibrium is unbounded as soon
as inflation starts away from zero (no disturbances or shocks: `π_t = θᵗ π_0`), so the
linearisation of §2.5 is not justified along it; the equilibrium still exists and is unique. -/
theorem ruleSol_unbounded {θ : ℝ} (hθ : 1 < |θ|) {π0 : Ω → ℝ} {ω : Ω} (hω : π0 ω ≠ 0) :
    ¬ BoundedProc (ruleSol θ 0 0 π0) := by
  have hpow : ∀ t, ruleSol θ 0 0 π0 t ω = θ ^ t * π0 ω := by
    intro t
    induction t with
    | zero => simp [ruleSol]
    | succ t ih =>
      change θ * ruleSol θ 0 0 π0 t ω + 0 - 0 = _
      rw [ih, pow_succ]
      ring
  rintro ⟨M, hM⟩
  have hpos : 0 < |π0 ω| := abs_pos.mpr hω
  obtain ⟨t, ht⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hθ).eventually_gt_atTop
    (M / |π0 ω|)).exists
  have h1 := hM t ω
  rw [hpow t, abs_mul, abs_pow] at h1
  rw [div_lt_iff₀ hpos] at ht
  linarith

/-! ### Figure 2.2: impulse responses as innovations -/

/-- Cochrane (2023), Figure 2.2, p. 41: the coefficients `c_0 = 0`, `c_{j+1} = θ c_j + ηʲ` of
the monetary-shock response, `c_j = ∑_{k<j} θ^{j−1−k} ηᵏ`. -/
def conv (θ η : ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => θ * conv θ η j + η ^ j

/-- Cochrane (2023), Figure 2.2, p. 41: for `θ ≠ η`, `c_j = (θʲ − ηʲ)/(θ − η)`. -/
theorem conv_eq {θ η : ℝ} (h : θ ≠ η) (j : ℕ) : conv θ η j = (θ ^ j - η ^ j) / (θ - η) := by
  have hne : θ - η ≠ 0 := sub_ne_zero.mpr h
  induction j with
  | zero => simp [conv]
  | succ j ih =>
    rw [conv, ih]
    field_simp
    ring

/-- Cochrane (2023), eq. (2.23), p. 40: the response of the disturbance to a monetary shock,
`ΔE_{t+1} u_{t+1+j} = ηʲ ε_{i,t+1}`. -/
theorem irf_disturbance {η : ℝ} {u εi : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u) (hεi : IsShock 𝔼 εi)
    (hd : Disturbance η u εi) (t j : ℕ) :
    innov 𝔼 t (u (t + 1 + j)) = η ^ j • εi (t + 1) := by
  induction j with
  | zero =>
    rw [add_zero, hd t, innov_add, innov_smul, innov_of_known 𝔼 (hu t), innov_shock 𝔼 hεi,
      smul_zero, zero_add, pow_zero, one_smul]
  | succ j ih =>
    rw [show t + 1 + (j + 1) = t + 1 + j + 1 by omega, hd, innov_add, innov_smul, ih,
      show t + 1 + j + 1 = t + 2 + j by omega, innov_shock_later 𝔼 hεi, add_zero, smul_smul,
      pow_succ, mul_comm η]

/-- Cochrane (2023), Figure 2.2 and eq. (2.25), pp. 40–41: impulse responses of inflation in the
rule model, `ΔE_{t+1} π_{t+1+j} = −θʲ ε_{Σs,t+1} + c_j ε_{i,t+1}`. -/
theorem irf_rule {θ η : ℝ} {u εi ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hu : 𝔼.Adapted u)
    (hεi : IsShock 𝔼 εi) (hε : IsShock 𝔼 ε) (hd : Disturbance η u εi)
    (h : ∀ t, π (t + 1) = θ • π t + u t - ε (t + 1)) (t j : ℕ) :
    innov 𝔼 t (π (t + 1 + j)) = (-θ ^ j) • ε (t + 1) + conv θ η j • εi (t + 1) := by
  induction j with
  | zero =>
    have hk : 𝔼.E t (θ • π t + u t) = θ • π t + u t := by rw [map_add, map_smul, hπ t, hu t]
    rw [add_zero, h t, innov_sub, innov_of_known 𝔼 hk, innov_shock 𝔼 hε, pow_zero, conv,
      zero_smul, add_zero, zero_sub, neg_one_smul]
  | succ j ih =>
    rw [show t + 1 + (j + 1) = t + 1 + j + 1 by omega, h, innov_sub, innov_add, innov_smul, ih,
      irf_disturbance 𝔼 hu hεi hd, show t + 1 + j + 1 = t + 2 + j by omega,
      innov_shock_later 𝔼 hε, sub_zero, conv, smul_add, smul_smul, smul_smul, add_smul,
      pow_succ]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Cochrane (2023), Figure 2.2, p. 41: the interest-rate responses,
`ΔE_{t+1} i_{t+1+j} = −θ^{j+1} ε_{Σs,t+1} + c_{j+1} ε_{i,t+1}` (inflation follows the rate with
a one-period lag). -/
theorem irf_rule_rate {θ η : ℝ} {i u εi ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hu : 𝔼.Adapted u)
    (hεi : IsShock 𝔼 εi) (hε : IsShock 𝔼 ε) (hd : Disturbance η u εi)
    (hm : RuleModel 𝔼 θ i u ε π) (t j : ℕ) :
    innov 𝔼 t (i (t + 1 + j)) = (-θ ^ (j + 1)) • ε (t + 1) + conv θ η (j + 1) • εi (t + 1) := by
  have h224 := ((ruleModel_iff 𝔼).mp hm).2
  have h := (eq224_iff 𝔼 hπ hu hε).mp h224
  have hpeg := (rule_eq_peg 𝔼 hπ hu hε hm).1
  have hi : 𝔼.Adapted i := fun t => by rw [(hm t).2.2, map_add, map_smul, hπ t, hu t]
  have hp := (pegModel_iff 𝔼 hπ hi hε).mp hpeg
  rw [← irf_peg_later 𝔼 hε hp t j, show t + 2 + j = t + 1 + (j + 1) by omega,
    irf_rule 𝔼 hπ hu hεi hε hd h t (j + 1)]

/-- Cochrane (2023), Figure 2.2, top panel: a unit monetary shock `ε_{i,t+1} = 1` with no fiscal
shock: inflation responds `c_j = (θʲ − ηʲ)/(θ − η)` (`0` on impact: "`π_1` cannot jump"), the
rate `c_{j+1}`. -/
theorem fig22_monetary {θ η : ℝ} (hθη : θ ≠ η) {i u εi ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hu : 𝔼.Adapted u) (hεi : IsShock 𝔼 εi) (hε : IsShock 𝔼 ε) (hd : Disturbance η u εi)
    (hm : RuleModel 𝔼 θ i u ε π) {t : ℕ} {ω : Ω} (h1 : εi (t + 1) ω = 1)
    (h0 : ε (t + 1) ω = 0) (j : ℕ) :
    innov 𝔼 t (π (t + 1 + j)) ω = (θ ^ j - η ^ j) / (θ - η) ∧
      innov 𝔼 t (i (t + 1 + j)) ω = (θ ^ (j + 1) - η ^ (j + 1)) / (θ - η) := by
  have h224 := ((ruleModel_iff 𝔼).mp hm).2
  have h := (eq224_iff 𝔼 hπ hu hε).mp h224
  rw [irf_rule 𝔼 hπ hu hεi hε hd h t j, irf_rule_rate 𝔼 hπ hu hεi hε hd hm t j]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, h0, conv_eq hθη]
  constructor <;> ring

/-- Cochrane (2023), Figure 2.2, bottom panel: a unit fiscal shock `ε_{Σs,t+1} = −1` with no
monetary shock: inflation responds `θʲ` and the rate `θ^{j+1}` (`π_t = θ^{t−1}`, `i_t = θᵗ` with
the shock at date 1). -/
theorem fig22_fiscal {θ η : ℝ} {i u εi ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hu : 𝔼.Adapted u) (hεi : IsShock 𝔼 εi) (hε : IsShock 𝔼 ε) (hd : Disturbance η u εi)
    (hm : RuleModel 𝔼 θ i u ε π) {t : ℕ} {ω : Ω} (h0 : εi (t + 1) ω = 0)
    (h1 : ε (t + 1) ω = -1) (j : ℕ) :
    innov 𝔼 t (π (t + 1 + j)) ω = θ ^ j ∧ innov 𝔼 t (i (t + 1 + j)) ω = θ ^ (j + 1) := by
  have h224 := ((ruleModel_iff 𝔼).mp hm).2
  have h := (eq224_iff 𝔼 hπ hu hε).mp h224
  rw [irf_rule 𝔼 hπ hu hεi hε hd h t j, irf_rule_rate 𝔼 hπ hu hεi hε hd hm t j]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, h0]
  constructor <;> ring

/-- Cochrane (2023), p. 41 ("fiscal policy alone sets the initial unexpected inflation of this
response function"): `ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` whatever `θ`, `η` and the monetary
shock. -/
theorem fiscal_sets_impact {θ η : ℝ} {u εi ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hu : 𝔼.Adapted u) (hεi : IsShock 𝔼 εi) (hε : IsShock 𝔼 ε) (hd : Disturbance η u εi)
    (h : ∀ t, π (t + 1) = θ • π t + u t - ε (t + 1)) (t : ℕ) :
    innov 𝔼 t (π (t + 1)) = -ε (t + 1) := by
  have := irf_rule 𝔼 hπ hu hεi hε hd h t 0
  rw [add_zero, pow_zero, conv, zero_smul, add_zero, neg_one_smul] at this
  exact this

/-- Cochrane (2023), p. 41 ("Monetary policy could turn the event into a one-time price level
shock, with no further inflation"): with `θ = 0` and no monetary shock, a fiscal shock
`ε_{Σs,t+1} = −1` raises inflation by `1` on impact and leaves later inflation unchanged. -/
theorem one_time_price_jump {η : ℝ} {u εi ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hu : 𝔼.Adapted u) (hεi : IsShock 𝔼 εi) (hε : IsShock 𝔼 ε) (hd : Disturbance η u εi)
    (h : ∀ t, π (t + 1) = (0 : ℝ) • π t + u t - ε (t + 1)) {t : ℕ} {ω : Ω}
    (h0 : εi (t + 1) ω = 0) (h1 : ε (t + 1) ω = -1) (j : ℕ) :
    innov 𝔼 t (π (t + 1 + j)) ω = if j = 0 then 1 else 0 := by
  rw [irf_rule 𝔼 hπ hu hεi hε hd h t j]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, h0]
  cases j with
  | zero => simp
  | succ j => simp

/-- Cochrane (2023), p. 41 ("Monetary policy could return the price level to its previous
value"): with `θ = 0`, `|η| < 1`, a fiscal shock `ε_{Σs,t+1} = −1` met by the monetary shock
`ε_{i,t+1} = −(1 − η)`, the inflation responses sum to zero: the price level returns. -/
theorem price_level_returns {η : ℝ} (hη : |η| < 1) {u εi ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hu : 𝔼.Adapted u) (hεi : IsShock 𝔼 εi) (hε : IsShock 𝔼 ε) (hd : Disturbance η u εi)
    (h : ∀ t, π (t + 1) = (0 : ℝ) • π t + u t - ε (t + 1)) {t : ℕ} {ω : Ω}
    (h0 : εi (t + 1) ω = -(1 - η)) (h1 : ε (t + 1) ω = -1) :
    HasSum (fun j => innov 𝔼 t (π (t + 1 + j)) ω) 0 := by
  have hx : ∀ j, innov 𝔼 t (π (t + 1 + j)) ω = -(0 : ℝ) ^ j * -1 + conv 0 η j * -(1 - η) := by
    intro j
    rw [irf_rule 𝔼 hπ hu hεi hε hd h t j]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, h0]
  have hc : ∀ j, conv 0 η (j + 1) = η ^ j := fun j => by simp [conv]
  have htail : HasSum (fun j => innov 𝔼 t (π (t + 1 + (j + 1))) ω) (-1) := by
    have hg := (hasSum_geometric_of_abs_lt_one hη).mul_left (-(1 - η))
    have h1η : 1 - η ≠ 0 := by
      have := (abs_lt.mp hη).2
      linarith
    have hv : -(1 - η) * (1 - η)⁻¹ = -1 := by
      rw [neg_mul, mul_inv_cancel₀ h1η]
    rw [hv] at hg
    convert hg using 1
    funext j
    rw [hx (j + 1), hc j]
    simp only [ne_eq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true, zero_pow]
    ring
  have hf0 : innov 𝔼 t (π (t + 1 + 0)) ω = 1 := by
    rw [hx 0]
    simp [conv]
  refine (hasSum_nat_add_iff' 1).mp ?_
  rw [Finset.sum_range_one, hf0, zero_sub]
  exact htail

/-! ### The hump (Figure 2.2, p. 40) -/

/-- Cochrane (2023), Figure 2.2, p. 40 ("a pretty hump-shaped inflation response"): for
`0 < η < θ < 1`, once the monetary response `c_j` stops rising it falls strictly ever after:
`c_{j+1} ≤ c_j → c_{j+2} < c_{j+1}`. -/
theorem hump_step {θ η : ℝ} (hη : 0 < η) (hηθ : η < θ) (hθ : θ < 1) (j : ℕ)
    (h : conv θ η (j + 1) ≤ conv θ η j) : conv θ η (j + 2) < conv θ η (j + 1) := by
  have hne : θ ≠ η := hηθ.ne'
  have hd : 0 < θ - η := sub_pos.mpr hηθ
  rw [conv_eq hne, conv_eq hne, div_le_div_iff_of_pos_right hd] at h
  rw [conv_eq hne, conv_eq hne, div_lt_div_iff_of_pos_right hd]
  have hθ0 : 0 < θ := hη.trans hηθ
  have hpθ : 0 < θ ^ j := pow_pos hθ0 j
  have hpη : 0 < η ^ j := pow_pos hη j
  have h1 : (1 - η) * η ^ j ≤ (1 - θ) * θ ^ j := by
    rw [pow_succ, pow_succ] at h
    nlinarith
  have h2 : (1 - η) * η ^ j * η ≤ (1 - θ) * θ ^ j * η := mul_le_mul_of_nonneg_right h1 hη.le
  have h3 : (1 - θ) * θ ^ j * η < (1 - θ) * θ ^ j * θ :=
    mul_lt_mul_of_pos_left hηθ (mul_pos (by linarith) hpθ)
  have key : (1 - η) * η ^ j * η < (1 - θ) * θ ^ j * θ := h2.trans_lt h3
  have e : θ ^ (j + 1) - η ^ (j + 1) - (θ ^ (j + 2) - η ^ (j + 2)) =
      (1 - θ) * θ ^ j * θ - (1 - η) * η ^ j * η := by ring
  linarith

/-- Cochrane (2023), Figure 2.2, p. 40: before the peak the response rises,
`c_J < c_{J+1} → ∀ j ≤ J, c_j < c_{j+1}` (`0 < η < θ < 1`). -/
theorem hump_up {θ η : ℝ} (hη : 0 < η) (hηθ : η < θ) (hθ : θ < 1) {J : ℕ}
    (h : conv θ η J < conv θ η (J + 1)) : ∀ j ≤ J, conv θ η j < conv θ η (j + 1) := by
  intro j hj
  induction J with
  | zero =>
    obtain rfl : j = 0 := by omega
    exact h
  | succ J ih =>
    rcases Nat.lt_or_ge j (J + 1) with hlt | hge
    · refine ih ?_ (by omega)
      by_contra hc
      have := hump_step hη hηθ hθ J (not_lt.mp hc)
      linarith
    · obtain rfl : j = J + 1 := by omega
      exact h

/-- Cochrane (2023), Figure 2.2, p. 40: after the peak the response falls,
`c_{J+1} ≤ c_J → ∀ k, c_{J+2+k} < c_{J+1+k}` (`0 < η < θ < 1`). -/
theorem hump_down {θ η : ℝ} (hη : 0 < η) (hηθ : η < θ) (hθ : θ < 1) {J : ℕ}
    (h : conv θ η (J + 1) ≤ conv θ η J) : ∀ k, conv θ η (J + 2 + k) < conv θ η (J + 1 + k) := by
  intro k
  induction k with
  | zero => exact hump_step hη hηθ hθ J h
  | succ k ih =>
    have := hump_step hη hηθ hθ (J + 1 + k) (by
      rw [show J + 1 + k + 1 = J + 2 + k by omega]
      exact ih.le)
    rw [show J + 2 + (k + 1) = J + 1 + k + 2 by omega,
      show J + 1 + (k + 1) = J + 1 + k + 1 by omega]
    exact this

/-- Cochrane (2023), Figure 2.2, p. 40 (the hump, in general): for `0 < η < θ < 1` the response
`c_j` is unimodal: strictly increasing up to some `J`, `c_{J+1} ≤ c_J`, and strictly decreasing
after `J`. -/
theorem hump_exists {θ η : ℝ} (hη : 0 < η) (hηθ : η < θ) (hθ : θ < 1) :
    ∃ J, (∀ j < J, conv θ η j < conv θ η (j + 1)) ∧ conv θ η (J + 1) ≤ conv θ η J ∧
      ∀ j, J < j → conv θ η (j + 1) < conv θ η j := by
  have hne : θ ≠ η := hηθ.ne'
  have hθ0 : 0 < θ := hη.trans hηθ
  have hex : ∃ J, conv θ η (J + 1) ≤ conv θ η J := by
    by_contra hc
    push Not at hc
    have hmono : ∀ j, conv θ η 1 ≤ conv θ η (j + 1) := by
      intro j
      induction j with
      | zero => exact le_rfl
      | succ j ih => exact ih.trans (hc (j + 1)).le
    have h1 : conv θ η 1 = 1 := by simp [conv]
    have hlim : Tendsto (fun j => conv θ η (j + 1)) atTop (𝓝 0) := by
      have ht := ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0.le hθ).sub
        (tendsto_pow_atTop_nhds_zero_of_lt_one hη.le (hηθ.trans hθ))).div_const (θ - η)
      rw [sub_zero, zero_div] at ht
      have ht' := ht.comp (tendsto_add_atTop_nat 1)
      refine ht'.congr fun j => ?_
      simp only [Function.comp_apply]
      rw [conv_eq hne]
    have := ge_of_tendsto' hlim (fun j => (h1 ▸ hmono j : (1 : ℝ) ≤ conv θ η (j + 1)))
    linarith
  classical
  refine ⟨Nat.find hex, fun j hj => ?_, Nat.find_spec hex, fun j hj => ?_⟩
  · exact not_le.mp (Nat.find_min hex hj)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hj
    have := hump_down hη hηθ hθ (Nat.find_spec hex) k
    rw [show Nat.find hex + k + 1 + 1 = Nat.find hex + 2 + k by omega,
      show Nat.find hex + k + 1 = Nat.find hex + 1 + k by omega]
    exact this

/-- Cochrane (2023), Figure 2.2, p. 41 (`θ = 0.8`, `η = 0.7`): the inflation response rises up
to `c_4` (inflation at date 5 for a shock at date 1) and falls strictly afterwards; the peak is
`c_4 = 1.695`. -/
theorem fig22_peak :
    (∀ j < 4, conv (4 / 5) (7 / 10) j < conv (4 / 5) (7 / 10) (j + 1)) ∧
      (∀ j, 4 ≤ j → conv (4 / 5) (7 / 10) (j + 1) < conv (4 / 5) (7 / 10) j) ∧
      conv (4 / 5) (7 / 10) 4 = 339 / 200 := by
  have hη : (0 : ℝ) < 7 / 10 := by norm_num
  have hηθ : (7 / 10 : ℝ) < 4 / 5 := by norm_num
  have hθ : (4 / 5 : ℝ) < 1 := by norm_num
  have h34 : conv (4 / 5) (7 / 10) 3 < conv (4 / 5) (7 / 10) (3 + 1) := by
    norm_num [conv]
  have h54 : conv (4 / 5) (7 / 10) (4 + 1) ≤ conv (4 / 5) (7 / 10) 4 := by
    norm_num [conv]
  refine ⟨fun j hj => hump_up hη hηθ hθ h34 j (by omega), fun j hj => ?_, by norm_num [conv]⟩
  rcases Nat.eq_or_lt_of_le hj with rfl | hlt
  · have := h54
    rcases this.lt_or_eq with h | h
    · exact h
    · norm_num [conv] at h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have := hump_down hη hηθ hθ h54 k
    rw [show 4 + k + 1 + 1 = 4 + 2 + k by omega, show 4 + k + 1 = 4 + 1 + k by omega]
    exact this

end Cochrane.IntertemporalModel.LinearFTMP
