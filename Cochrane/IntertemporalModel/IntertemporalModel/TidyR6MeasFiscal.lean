/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.TidyR6MeasHyp
import IntertemporalModel.TidyR5MeasFamily
import IntertemporalModel.ExpectationsMeasureIID

/-!
# Fiscal and monetary corollaries on a genuine probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.4.2, p. 31 (share splits,
revenue, future bond sales), §2.7, pp. 42–43 (equity issues, AR(1) surpluses, the s-shape),
§2.9, p. 48 ((2.28), the Treasury rule, the flat supply curve and the two-step process) and
§2.10, p. 50 (fiscal stimulus), restated and proved on a probability space with a filtration
(`MeasExpectationSystem`), with Mathlib's conditional expectation and equations holding almost
surely. These are the `FiscalMonetary` and `FlatSupply` corollaries that were stated only for an
`ExpectationSystem`; the equilibrium notion is `TidyR5Meas.MEquilibrium`.

## Main results

* Debt sales with surpluses fixed: `mRevenue` (real revenue is `PVex_t`), `mRevenue_invariant`,
  `mFuture_sales_irrelevant`, `mShareSplit`.
* Equity issues: `mEquityIssue`, `mEquityIssue_finances_deficit`.
* AR(1) surpluses: `mAr1_pv` (`PV_t = s_t/(1 − βη)`), `mAr1_pv_news`,
  `mAr1_unexpected_inflation` (the corrected formula with the factor `B_t/P_t`),
  `mAr1_printed_fails`, `mAr1_value_news`, `mAr1_value_falls`; in the `±1` coin economy
  `Coin.coin_ar1_news` (news nonzero almost surely).
* The s-shape: `mNews_pv_tsum`, `mSShape`.
* Fiscal stimulus: `mNews_pv_add_known`, `mStimulus_no_jump`, `mStimulus_price_iff`,
  `mStimulus_unexpected_inflation`, and the counterexample to "no effect at all" on the i.i.d.
  `±1` coin economy, where every history is null: `Coin.coin_stimulus_not_neutral`.
* §2.9: `mTreasury_rule` ((2.28)), `mDebt_ratio_of_rate` (the flat supply curve),
  `mTwoStep`, `mTwoStep_eq_pegP`, `mTwoStep_debt`, `mTwoStep_equilibrium`.
* Links back to the core on finite trees: `Link.tree_mRevenue`, `Link.tree_mTreasury_rule`.
-/

namespace Cochrane.IntertemporalModel.TidyR6MeasFiscal

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure TidyR5Meas

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)
variable {β : ℝ} {Bm1 Bm1' : Ω → ℝ} {s s' B P i B' P' i' : ℕ → Ω → ℝ}

/-- Cochrane (2023), eq. (2.15), p. 31, on a probability space: `PV_{t+1} > 0` almost surely
gives `PVex_t > 0` almost surely (`β > 0`). -/
theorem pvExM_pos_at (hβ0 : 0 < β) {t : ℕ} (hpv : ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s (t + 1) ω) :
    ∀ᵐ ω ∂S.μ, 0 < pvExM S β s t ω := by
  filter_upwards [HouseholdMeasure.E_pos (S.integrable_E (t + 1) _) hpv t] with ω h
  simp only [pvExM, Pi.smul_apply, smul_eq_mul]
  exact mul_pos hβ0 h

/-! ### Debt sales with surpluses fixed (§2.4.2) -/

/-- Cochrane (2023), p. 31 (unit-elastic demand), on a probability space: in every equilibrium
the real revenue from bond sales is `(B_t/P_t)/(1 + i_t) = PVex_t` almost surely (`β > 0`,
`PV_{t+1} > 0` a.s.).
Restates `GeneralLinks.equilibrium_realRevenue` on a genuine probability space. -/
theorem mRevenue (hβ0 : 0 < β) (h : MEquilibrium S β Bm1 s B P i) (t : ℕ)
    (hpv : ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s (t + 1) ω) :
    (fun ω => B t ω / P t ω * (1 + i t ω)⁻¹) =ᵐ[S.μ] pvExM S β s t := by
  filter_upwards [mDebt_eq S hβ0 h t hpv, h.2.1 t, mEqm_rate_gt S hβ0 h t] with ω h1 h2 h3
  have e : B t ω = (1 + i t ω) * P t ω * pvExM S β s t ω := h1
  rw [e]
  have : 1 + i t ω ≠ 0 := by linarith
  have := h2.ne'
  field_simp

/-- Cochrane (2023), p. 31, on a probability space: two equilibria with the same surpluses raise
the same real revenue almost surely, whatever debt they sell.
Restates `FiscalMonetary.revenue_invariant` on a genuine probability space. -/
theorem mRevenue_invariant (hβ0 : 0 < β) (h : MEquilibrium S β Bm1 s B P i)
    (h' : MEquilibrium S β Bm1' s B' P' i') (t : ℕ)
    (hpv : ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s (t + 1) ω) :
    (fun ω => B' t ω / P' t ω * (1 + i' t ω)⁻¹) =ᵐ[S.μ]
      fun ω => B t ω / P t ω * (1 + i t ω)⁻¹ :=
  (mRevenue S hβ0 h' t hpv).trans (mRevenue S hβ0 h t hpv).symm

/-- Cochrane (2023), p. 31, "changing expectations of future bond sales make no difference", on a
probability space: two equilibria with the same surpluses and initial debt and the same debt up
to date `t` almost surely have the same price level up to date `t + 1` almost surely.
Restates `FiscalMonetary.future_sales_irrelevant` on a genuine probability space. -/
theorem mFuture_sales_irrelevant (h : MEquilibrium S β Bm1 s B P i)
    (h' : MEquilibrium S β Bm1 s B' P' i') (hpv : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s t ω)
    {t : ℕ} (hB : ∀ k ≤ t, B' k =ᵐ[S.μ] B k) : ∀ k ≤ t + 1, P' k =ᵐ[S.μ] P k := by
  intro k hk
  cases k with
  | zero => exact (mPrice_zero S h' (hpv 0)).trans (mPrice_zero S h (hpv 0)).symm
  | succ k =>
    filter_upwards [mPrice_succ S h' k (hpv (k + 1)), mPrice_succ S h k (hpv (k + 1)),
      hB k (by omega)] with ω h1 h2 h3
    rw [h1, h2, h3]

/-- Cochrane (2023), p. 31, "selling bonds without changing surpluses is again like a share
split", on a probability space: scaling the debt sold at `t` by `λ > 0` almost surely (same debt
before, same surpluses and initial debt) leaves the price level up to `t` unchanged, scales
`P_{t+1}` and the gross rate `1 + i_t` by `λ`, divides `E_t(P_t/P_{t+1})` by `λ` and leaves real
revenue unchanged, all almost surely.
Restates `FiscalMonetary.shareSplit` on a genuine probability space. -/
theorem mShareSplit (hβ0 : 0 < β) (h : MEquilibrium S β Bm1 s B P i)
    (h' : MEquilibrium S β Bm1 s B' P' i') (hpv : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s t ω)
    {t : ℕ} {lam : ℝ} (hlam : 0 < lam) (hBk : ∀ k < t, B' k =ᵐ[S.μ] B k)
    (hBt : B' t =ᵐ[S.μ] lam • B t) :
    (∀ k ≤ t, P' k =ᵐ[S.μ] P k) ∧ P' (t + 1) =ᵐ[S.μ] lam • P (t + 1) ∧
      (fun ω => 1 + i' t ω) =ᵐ[S.μ] (fun ω => lam * (1 + i t ω)) ∧
      S.E t (fun ω => P' t ω / P' (t + 1) ω) =ᵐ[S.μ]
        lam⁻¹ • S.E t (fun ω => P t ω / P (t + 1) ω) ∧
      (fun ω => B' t ω / P' t ω * (1 + i' t ω)⁻¹) =ᵐ[S.μ]
        fun ω => B t ω / P t ω * (1 + i t ω)⁻¹ := by
  have hPk : ∀ k ≤ t, P' k =ᵐ[S.μ] P k := by
    intro k hk
    cases k with
    | zero => exact (mPrice_zero S h' (hpv 0)).trans (mPrice_zero S h (hpv 0)).symm
    | succ k =>
      filter_upwards [mPrice_succ S h' k (hpv (k + 1)), mPrice_succ S h k (hpv (k + 1)),
        hBk k (by omega)] with ω h1 h2 h3
      rw [h1, h2, h3]
  have hP1 : P' (t + 1) =ᵐ[S.μ] lam • P (t + 1) := by
    filter_upwards [mPrice_succ S h' t (hpv (t + 1)), mPrice_succ S h t (hpv (t + 1)), hBt]
      with ω h1 h2 h3
    rw [h1, Pi.smul_apply, h2, h3, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_div_assoc]
  refine ⟨hPk, hP1, ?_, ?_, mRevenue_invariant S hβ0 h h' t (hpv (t + 1))⟩
  · filter_upwards [mDebt_eq S hβ0 h' t (hpv (t + 1)), mDebt_eq S hβ0 h t (hpv (t + 1)), hBt,
      hPk t le_rfl, h.2.1 t, pvExM_pos_at S hβ0 (hpv (t + 1))] with ω e1 e2 e3 e4 e5 e6
    have e1' : B' t ω = (1 + i' t ω) * P' t ω * pvExM S β s t ω := e1
    have e2' : B t ω = (1 + i t ω) * P t ω * pvExM S β s t ω := e2
    rw [e3, Pi.smul_apply, smul_eq_mul, e2', e4] at e1'
    have hne : P t ω * pvExM S β s t ω ≠ 0 := (mul_pos e5 e6).ne'
    apply mul_right_cancel₀ hne
    linear_combination -e1'
  · have hfun : (fun ω => P' t ω / P' (t + 1) ω) =ᵐ[S.μ]
        lam⁻¹ • fun ω => P t ω / P (t + 1) ω := by
      filter_upwards [hP1, hPk t le_rfl] with ω h1 h2
      rw [h1, h2, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
      have := hlam.ne'
      field_simp
    filter_upwards [S.E_congr hfun t, S.E_smul lam⁻¹ (fun ω => P t ω / P (t + 1) ω) t]
      with ω h1 h2
    rw [h1, h2]

/-! ### Equity issues (§2.7, p. 42) -/

/-- Cochrane (2023), p. 42, the equity issue, on a probability space: if two equilibria share the
current price level and the debt sold rises in proportion to the expected subsequent surpluses
(`B'_t PVex_t = B_t PV'ex_t` a.s.), the nominal rate is unchanged and real revenue rises in
proportion to the debt, almost surely.
Restates `FiscalMonetary.equityIssue` on a genuine probability space. -/
theorem mEquityIssue (hβ0 : 0 < β) (h : MEquilibrium S β Bm1 s B P i)
    (h' : MEquilibrium S β Bm1' s' B' P' i') {t : ℕ} (hPt : P' t =ᵐ[S.μ] P t)
    (hpv : ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s (t + 1) ω)
    (hpv' : ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s' (t + 1) ω)
    (hprop : (fun ω => B' t ω * pvExM S β s t ω) =ᵐ[S.μ] fun ω => B t ω * pvExM S β s' t ω) :
    i' t =ᵐ[S.μ] i t ∧
      (fun ω => B' t ω / P' t ω * (1 + i' t ω)⁻¹ * B t ω) =ᵐ[S.μ]
        fun ω => B t ω / P t ω * (1 + i t ω)⁻¹ * B' t ω := by
  refine ⟨?_, ?_⟩
  · filter_upwards [mDebt_eq S hβ0 h' t hpv', mDebt_eq S hβ0 h t hpv, hPt, hprop, h.2.1 t,
      pvExM_pos_at S hβ0 hpv, pvExM_pos_at S hβ0 hpv'] with ω e1 e2 e3 e4 e5 e6 e7
    have e1' : B' t ω = (1 + i' t ω) * P' t ω * pvExM S β s' t ω := e1
    have e2' : B t ω = (1 + i t ω) * P t ω * pvExM S β s t ω := e2
    have e4' : B' t ω * pvExM S β s t ω = B t ω * pvExM S β s' t ω := e4
    rw [e1', e2', e3] at e4'
    have hne : P t ω * pvExM S β s' t ω * pvExM S β s t ω ≠ 0 :=
      (mul_pos (mul_pos e5 e7) e6).ne'
    have : (i' t ω - i t ω) * (P t ω * pvExM S β s' t ω * pvExM S β s t ω) = 0 := by
      linear_combination e4'
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · exact absurd h0 hne
  · filter_upwards [mRevenue S hβ0 h' t hpv', mRevenue S hβ0 h t hpv, hprop] with ω e1 e2 e3
    have e1' : B' t ω / P' t ω * (1 + i' t ω)⁻¹ = pvExM S β s' t ω := e1
    have e2' : B t ω / P t ω * (1 + i t ω)⁻¹ = pvExM S β s t ω := e2
    have e3' : B' t ω * pvExM S β s t ω = B t ω * pvExM S β s' t ω := e3
    rw [e1', e2']
    linear_combination -e3'

/-- Cochrane (2023), p. 42, "this extra money can finance a deficit ... with no unexpected
inflation", on a probability space: with the same debt outstanding almost surely, a deficit
`s'_{t+1} = s_{t+1} − δ` matched by higher subsequent surpluses `PV'ex_{t+1} = PVex_{t+1} + δ`
(both a.s.) leaves `P_{t+1}` unchanged and raises real revenue by `δ`, almost surely
(`0 < β < 1`, bounded adapted surpluses, positive present values).
Restates `FiscalMonetary.equityIssue_finances_deficit` on a genuine probability space. -/
theorem mEquityIssue_finances_deficit (hβ0 : 0 < β) (hβ1 : β < 1) {M M' : ℝ}
    (hsad : StronglyAdapted S.𝓕 s) (hsM : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ M)
    (hsad' : StronglyAdapted S.𝓕 s') (hsM' : ∀ t, ∀ᵐ ω ∂S.μ, |s' t ω| ≤ M')
    (h : MEquilibrium S β Bm1 s B P i) (h' : MEquilibrium S β Bm1' s' B' P' i') {t : ℕ}
    {δ : Ω → ℝ} (hBt : B' t =ᵐ[S.μ] B t) (hst : s' (t + 1) =ᵐ[S.μ] s (t + 1) - δ)
    (hex : pvExM S β s' (t + 1) =ᵐ[S.μ] pvExM S β s (t + 1) + δ)
    (hpv : ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s (t + 1) ω)
    (hpv2 : ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s (t + 2) ω)
    (hpv2' : ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s' (t + 2) ω) :
    P' (t + 1) =ᵐ[S.μ] P (t + 1) ∧
      (fun ω => B' (t + 1) ω / P' (t + 1) ω * (1 + i' (t + 1) ω)⁻¹) =ᵐ[S.μ]
        fun ω => B (t + 1) ω / P (t + 1) ω * (1 + i (t + 1) ω)⁻¹ + δ ω := by
  have ha : |β| < 1 := by rwa [abs_of_pos hβ0]
  have hpveq : S.forwardSol β s' (t + 1) =ᵐ[S.μ] S.forwardSol β s (t + 1) := by
    filter_upwards [pv_eq_add_pvEx S ha hsad' hsM' (t + 1), pv_eq_add_pvEx S ha hsad hsM (t + 1),
      hst, hex] with ω e1 e2 e3 e4
    rw [e1, e2, Pi.add_apply, Pi.add_apply, e3, e4, Pi.sub_apply, Pi.add_apply]
    ring
  have hpv' : ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s' (t + 1) ω := by
    filter_upwards [hpveq, hpv] with ω e h
    rw [e]
    exact h
  refine ⟨?_, ?_⟩
  · filter_upwards [mPrice_succ S h' t hpv', mPrice_succ S h t hpv, hBt, hpveq] with ω e1 e2 e3 e4
    rw [e1, e2, e3, e4]
  · filter_upwards [mRevenue S hβ0 h' (t + 1) hpv2', mRevenue S hβ0 h (t + 1) hpv2, hex]
      with ω e1 e2 e3
    rw [e1, e2, e3, Pi.add_apply]

/-! ### AR(1) surpluses (§2.7, p. 43) -/

/-- Cochrane (2023), eq. (2.13), p. 30, on a probability space: the news of random variables
equal almost surely are equal almost surely. -/
theorem innov_congr {f g : Ω → ℝ} (h : f =ᵐ[S.μ] g) (t : ℕ) :
    S.innov t f =ᵐ[S.μ] S.innov t g := by
  filter_upwards [S.E_congr h (t + 1), S.E_congr h t] with ω h1 h2
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, h1, h2]

variable {η : ℝ} {e : ℕ → Ω → ℝ}

/-- Cochrane (2023), p. 43, on a probability space: for a bounded adapted AR(1) surplus
`s_{t+1} = η s_t + e_{t+1}` with martingale-difference shocks (`E_t e_{t+1} = 0` a.s.),
`0 ≤ β < 1` and `|βη| < 1`, the present value is `PV_t = s_t/(1 − βη)` almost surely. -/
theorem mAr1_pv (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hβη : |β * η| < 1) (hsad : StronglyAdapted S.𝓕 s)
    (hsb : S.BddProc s) (hrec : ∀ t, s (t + 1) = η • s t + e (t + 1))
    (hmd : ∀ t, S.E t (e (t + 1)) =ᵐ[S.μ] 0) (t : ℕ) :
    S.forwardSol β s t =ᵐ[S.μ] (1 - β * η)⁻¹ • s t := by
  obtain ⟨M, hM⟩ := hsb
  have ha : |β| < 1 := by rwa [abs_of_nonneg hβ0]
  have hm : ∀ t, AEStronglyMeasurable (s t) S.μ := fun t =>
    ((hsad t).mono (S.𝓕.le t)).aestronglyMeasurable
  filter_upwards [S.forwardSol_hasSum ha hm hM t,
    ae_all_iff.2 fun j => S.ar1_E hrec hsad ⟨M, hM⟩ hmd t j] with ω h1 h2
  have h3 : HasSum (fun k => β ^ k * S.E t (s (t + k)) ω) ((1 - β * η)⁻¹ * s t ω) := by
    have hg := (hasSum_geometric_of_abs_lt_one hβη).mul_right (s t ω)
    convert hg using 1
    funext k
    rw [h2 k, Pi.smul_apply, smul_eq_mul, mul_pow]
    ring
  rw [Pi.smul_apply, smul_eq_mul]
  exact h1.unique h3

/-- Cochrane (2023), p. 43, on a probability space: for the AR(1) surplus of `mAr1_pv` the
present-value news is `ΔE_{t+1} PV_{t+1} = e_{t+1}/(1 − βη)` almost surely.
Restates `FiscalMonetary.ar1_pv_news` on a genuine probability space. -/
theorem mAr1_pv_news (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hβη : |β * η| < 1)
    (hsad : StronglyAdapted S.𝓕 s) (hsb : S.BddProc s)
    (hrec : ∀ t, s (t + 1) = η • s t + e (t + 1)) (hmd : ∀ t, S.E t (e (t + 1)) =ᵐ[S.μ] 0)
    (t : ℕ) : S.innov t (S.forwardSol β s (t + 1)) =ᵐ[S.μ] (1 - β * η)⁻¹ • e (t + 1) := by
  have hpv := mAr1_pv S hβ0 hβ1 hβη hsad hsb hrec hmd (t + 1)
  have h1 : S.E t (s (t + 1)) =ᵐ[S.μ] η • s t := by
    simpa using S.ar1_E hrec hsad hsb hmd t 1
  have hk : S.E (t + 1) (S.forwardSol β s (t + 1)) = S.forwardSol β s (t + 1) :=
    S.E_E_self (t + 1) _
  filter_upwards [hpv, S.E_congr hpv t, S.E_smul (1 - β * η)⁻¹ (s (t + 1)) t, h1]
    with ω e1 e2 e3 e4
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, hk]
  rw [e1, e2, e3]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [e4, Pi.smul_apply, smul_eq_mul, hrec t, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), p. 43, corrected (survey E5), on a probability space: in every equilibrium
with an AR(1) surplus, `(B_t/P_t) ΔE_{t+1}(P_t/P_{t+1}) = e_{t+1}/(1 − βη)` almost surely.
Restates `FiscalMonetary.ar1_unexpected_inflation` on a genuine probability space. -/
theorem mAr1_unexpected_inflation (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hβη : |β * η| < 1)
    (hsad : StronglyAdapted S.𝓕 s) (hsb : S.BddProc s)
    (hrec : ∀ t, s (t + 1) = η • s t + e (t + 1)) (hmd : ∀ t, S.E t (e (t + 1)) =ᵐ[S.μ] 0)
    (h : MEquilibrium S β Bm1 s B P i) (t : ℕ) :
    (fun ω => B t ω / P t ω * S.innov t (fun ω => P t ω / P (t + 1) ω) ω) =ᵐ[S.μ]
      (1 - β * η)⁻¹ • e (t + 1) :=
  (mUnexpected_inflation S h t).trans (mAr1_pv_news S hβ0 hβ1 hβη hsad hsb hrec hmd t)

/-- Cochrane (2023), p. 43 (survey E5), on a probability space: almost surely, wherever the
shock is nonzero and the real debt `B_t/P_t` differs from one, the printed formula
`ΔE_{t+1}(P_t/P_{t+1}) = e_{t+1}/(1 − βη)` fails.
Restates `FiscalMonetary.ar1_printed_fails` on a genuine probability space. -/
theorem mAr1_printed_fails (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hβη : |β * η| < 1)
    (hsad : StronglyAdapted S.𝓕 s) (hsb : S.BddProc s)
    (hrec : ∀ t, s (t + 1) = η • s t + e (t + 1)) (hmd : ∀ t, S.E t (e (t + 1)) =ᵐ[S.μ] 0)
    (h : MEquilibrium S β Bm1 s B P i) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, e (t + 1) ω ≠ 0 → B t ω / P t ω ≠ 1 →
      S.innov t (fun ω => P t ω / P (t + 1) ω) ω ≠ (1 - β * η)⁻¹ * e (t + 1) ω := by
  have h1 : 1 - β * η ≠ 0 := by
    have := (abs_lt.mp hβη).2
    linarith
  filter_upwards [mAr1_unexpected_inflation S hβ0 hβ1 hβη hsad hsb hrec hmd h t]
    with ω hω he hV heq
  simp only [Pi.smul_apply, smul_eq_mul] at hω
  rw [heq] at hω
  apply hV
  have hx : (1 - β * η)⁻¹ * e (t + 1) ω ≠ 0 := mul_ne_zero (inv_ne_zero h1) he
  apply mul_right_cancel₀ hx
  rw [one_mul, hω]

/-- Cochrane (2023), p. 43, on a probability space: for the AR(1) surplus the news about the
value of the debt sold, `ΔE_{t+1} PVex_{t+1}`, is `βη/(1 − βη) e_{t+1}` almost surely
(`0 < β < 1`).
Restates `FiscalMonetary.ar1_value_news` on a genuine probability space. -/
theorem mAr1_value_news (hβ0 : 0 < β) (hβ1 : β < 1) (hβη : |β * η| < 1)
    (hsad : StronglyAdapted S.𝓕 s) (hsb : S.BddProc s)
    (hrec : ∀ t, s (t + 1) = η • s t + e (t + 1)) (hmd : ∀ t, S.E t (e (t + 1)) =ᵐ[S.μ] 0)
    (t : ℕ) :
    S.innov t (pvExM S β s (t + 1)) =ᵐ[S.μ] (β * η * (1 - β * η)⁻¹) • e (t + 1) := by
  obtain ⟨M, hM⟩ := hsb
  have ha : |β| < 1 := by rwa [abs_of_pos hβ0]
  have h1η : 1 - β * η ≠ 0 := by
    have := (abs_lt.mp hβη).2
    linarith
  have hsi : Integrable (s (t + 1)) S.μ := MeasExpectationSystem.BddRV.integrable
    (MeasExpectationSystem.BddRV.of_stronglyMeasurable (hsad (t + 1)) (hM (t + 1)))
  have hpe : pvExM S β s (t + 1) =ᵐ[S.μ] S.forwardSol β s (t + 1) - s (t + 1) := by
    filter_upwards [pv_eq_add_pvEx S ha hsad hM (t + 1)] with ω h1
    rw [Pi.sub_apply, h1, Pi.add_apply]
    ring
  have hns : S.innov t (s (t + 1)) =ᵐ[S.μ] e (t + 1) := by
    have hk : S.E (t + 1) (s (t + 1)) = s (t + 1) := S.E_of_stronglyMeasurable (hsad (t + 1)) hsi
    have h1 : S.E t (s (t + 1)) =ᵐ[S.μ] η • s t := by
      simpa using S.ar1_E hrec hsad ⟨M, hM⟩ hmd t 1
    filter_upwards [h1] with ω h1
    rw [MeasExpectationSystem.innov, Pi.sub_apply, hk, h1, hrec t]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hIP : Integrable (S.forwardSol β s (t + 1)) S.μ := S.integrable_E _ _
  filter_upwards [innov_congr S hpe t, S.E_sub hIP hsi (t + 1), S.E_sub hIP hsi t,
    mAr1_pv_news S hβ0.le hβ1 hβη hsad ⟨M, hM⟩ hrec hmd t, hns] with ω e1 e2 e3 e4 e5
  rw [e1]
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e4 e5 ⊢
  rw [e2, e3]
  simp only [Pi.sub_apply]
  have hc : (1 - β * η) * (1 - β * η)⁻¹ = 1 := mul_inv_cancel₀ h1η
  linear_combination e4 - e5 + e (t + 1) ω * hc

/-- Cochrane (2023), p. 43, "the AR(1) generates a value of debt ... that goes down when there
is a deficit", on a probability space: for `0 < βη < 1`, almost surely a deficit shock
`e_{t+1} < 0` lowers the value of the debt.
Restates `FiscalMonetary.ar1_value_falls` on a genuine probability space. -/
theorem mAr1_value_falls (hβ0 : 0 < β) (hβ1 : β < 1) (hpos : 0 < β * η) (hlt : β * η < 1)
    (hsad : StronglyAdapted S.𝓕 s) (hsb : S.BddProc s)
    (hrec : ∀ t, s (t + 1) = η • s t + e (t + 1)) (hmd : ∀ t, S.E t (e (t + 1)) =ᵐ[S.μ] 0)
    (t : ℕ) : ∀ᵐ ω ∂S.μ, e (t + 1) ω < 0 → S.innov t (pvExM S β s (t + 1)) ω < 0 := by
  have hβη : |β * η| < 1 := by rwa [abs_of_pos hpos]
  filter_upwards [mAr1_value_news S hβ0 hβ1 hβη hsad hsb hrec hmd t] with ω h hε
  rw [h, Pi.smul_apply, smul_eq_mul]
  exact mul_neg_of_pos_of_neg (mul_pos hpos (inv_pos.mpr (by linarith))) hε

/-! ### The s-shape (§2.7, p. 43) -/

/-- Cochrane (2023), p. 43, on a probability space: for bounded adapted surpluses and
`0 < β < 1`, almost surely the present-value news is the discounted sum of surplus news,
`ΔE_{t+1} PV_{t+1} = ∑ βʲ ΔE_{t+1} s_{t+1+j}` (a genuine `HasSum`).
Restates `FiscalMonetary.news_epv_tsum` on a genuine probability space. -/
theorem mNews_pv_tsum (hβ0 : 0 < β) (hβ1 : β < 1) (hsad : StronglyAdapted S.𝓕 s) {M : ℝ}
    (hsM : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ M) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun j => β ^ j * S.innov t (s (t + 1 + j)) ω)
      (S.innov t (S.forwardSol β s (t + 1)) ω) := by
  have ha : |β| < 1 := by rwa [abs_of_pos hβ0]
  have hm : ∀ t, AEStronglyMeasurable (s t) S.μ := fun t =>
    ((hsad t).mono (S.𝓕.le t)).aestronglyMeasurable
  have hsm' : ∀ k, S.E t (fun ω => β ^ k * s (t + 1 + k) ω) =ᵐ[S.μ]
      β ^ k • S.E t (s (t + 1 + k)) := fun k => S.E_smul (β ^ k) (s (t + 1 + k)) t
  have h2 := S.E_hasSum (f := fun k ω => β ^ k * s (t + 1 + k) ω)
    ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right M)
    (fun k => (hm (t + 1 + k)).const_mul _) (fun k => by
      filter_upwards [hsM (t + 1 + k)] with ω h
      rw [abs_mul, abs_pow, abs_of_pos hβ0]
      exact mul_le_mul_of_nonneg_left h (pow_nonneg hβ0.le k)) t
  have h3 : S.E t (S.forwardSol β s (t + 1)) =ᵐ[S.μ]
      S.E t (MeasExpectationSystem.discSum β s (t + 1)) :=
    S.E_tower (Nat.le_succ t) (MeasExpectationSystem.discSum β s (t + 1))
  have hk : S.E (t + 1) (S.forwardSol β s (t + 1)) = S.forwardSol β s (t + 1) :=
    S.E_E_self (t + 1) _
  filter_upwards [S.forwardSol_hasSum ha hm hsM (t + 1), h2, ae_all_iff.2 hsm', h3]
    with ω e1 e2 e3 e4
  have e2' : HasSum (fun k => β ^ k * S.E t (s (t + 1 + k)) ω)
      (S.E t (S.forwardSol β s (t + 1)) ω) := by
    rw [e4]
    have hf : (fun k => β ^ k * S.E t (s (t + 1 + k)) ω) =
        fun k => S.E t (fun ω => β ^ k * s (t + 1 + k) ω) ω := by
      funext k
      rw [e3 k, Pi.smul_apply, smul_eq_mul]
    rw [hf]
    exact e2
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, hk]
  convert e1.sub e2' using 1
  funext j
  ring

/-- Cochrane (2023), p. 43, "the surplus process must have an s-shaped moving average", on a
probability space: almost surely, zero present-value news and a current deficit shock
`ΔE_{t+1} s_{t+1} < 0` force a later positive surplus shock.
Restates `FiscalMonetary.sShape` on a genuine probability space. -/
theorem mSShape (hβ0 : 0 < β) (hβ1 : β < 1) (hsad : StronglyAdapted S.𝓕 s) {M : ℝ}
    (hsM : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ M) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, S.innov t (S.forwardSol β s (t + 1)) ω = 0 → S.innov t (s (t + 1)) ω < 0 →
      ∃ j, 1 ≤ j ∧ 0 < S.innov t (s (t + 1 + j)) ω := by
  filter_upwards [mNews_pv_tsum S hβ0 hβ1 hsad hsM t] with ω h h0 hd
  exact FiscalMonetary.sShape_seq hβ0 h.summable (by rw [h.tsum_eq]; exact h0)
    (by simpa using hd)

/-! ### Fiscal stimulus (§2.10, p. 50) -/

/-- Cochrane (2023), p. 50, on a probability space: adding an integrable amount `D` known at `t`
to the present value at `t + 1` does not change the present-value news, almost surely.
Restates `FiscalMonetary.news_pv_add_known` on a genuine probability space. -/
theorem mNews_pv_add_known {t : ℕ} {D : Ω → ℝ} (hD : StronglyMeasurable[S.𝓕 t] D)
    (hDi : Integrable D S.μ)
    (hpv : S.forwardSol β s' (t + 1) =ᵐ[S.μ] S.forwardSol β s (t + 1) + D) :
    S.innov t (S.forwardSol β s' (t + 1)) =ᵐ[S.μ] S.innov t (S.forwardSol β s (t + 1)) := by
  have hk : ∀ x : ℕ → Ω → ℝ, S.E (t + 1) (S.forwardSol β x (t + 1)) = S.forwardSol β x (t + 1) :=
    fun x => S.E_E_self (t + 1) _
  have hEt : S.E t (S.forwardSol β s (t + 1) + D) =ᵐ[S.μ]
      S.E t (S.forwardSol β s (t + 1)) + D := by
    have hIP : Integrable (S.forwardSol β s (t + 1)) S.μ := S.integrable_E _ _
    filter_upwards [S.E_add hIP hDi t] with ω h
    rw [h, Pi.add_apply, Pi.add_apply, S.E_of_stronglyMeasurable hD hDi]
  filter_upwards [hpv, S.E_congr hpv t, hEt] with ω e1 e2 e3
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, hk]
  rw [e1, e2, e3, Pi.add_apply, Pi.add_apply]
  ring

/-- Cochrane (2023), p. 50, "borrow money, ... spend the money, repay the debt has no effect at
all on current ... inflation", on a probability space: with the same debt outstanding and the
same present value at `t + 1`, almost surely, `P_{t+1}` is unchanged almost surely.
Restates `FiscalMonetary.stimulus_no_jump` on a genuine probability space. -/
theorem mStimulus_no_jump (h : MEquilibrium S β Bm1 s B P i)
    (h' : MEquilibrium S β Bm1' s' B' P' i') {t : ℕ} (hBt : B' t =ᵐ[S.μ] B t)
    (hpv : S.forwardSol β s' (t + 1) =ᵐ[S.μ] S.forwardSol β s (t + 1))
    (hpv0 : ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s (t + 1) ω) : P' (t + 1) =ᵐ[S.μ] P (t + 1) := by
  have hpv0' : ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s' (t + 1) ω := by
    filter_upwards [hpv, hpv0] with ω e h
    rw [e]
    exact h
  filter_upwards [mPrice_succ S h' t hpv0', mPrice_succ S h t hpv0, hBt, hpv] with ω e1 e2 e3 e4
  rw [e1, e2, e3, e4]

/-- Cochrane (2023), p. 50, corrected for uncertainty, on a probability space: a stimulus that
adds an integrable amount `D` known at `t` to the present value at `t + 1` (same target, same
`P_t`) leaves `P_{t+1}` unchanged in almost every state exactly where `D = 0` or there is no
other fiscal news `ΔE_{t+1} PV_{t+1} = 0`.
Restates `FiscalMonetary.stimulus_price_iff` on a genuine probability space. -/
theorem mStimulus_price_iff (hβ0 : 0 < β) (h : MEquilibrium S β Bm1 s B P i)
    (h' : MEquilibrium S β Bm1' s' B' P' i) {t : ℕ} (hPt : P' t =ᵐ[S.μ] P t) {D : Ω → ℝ}
    (hD : StronglyMeasurable[S.𝓕 t] D) (hDi : Integrable D S.μ)
    (hpvD : S.forwardSol β s' (t + 1) =ᵐ[S.μ] S.forwardSol β s (t + 1) + D)
    (hpv0 : ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s (t + 1) ω)
    (hpv0' : ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s' (t + 1) ω) :
    ∀ᵐ ω ∂S.μ, (P' (t + 1) ω = P (t + 1) ω ↔
      D ω = 0 ∨ S.innov t (S.forwardSol β s (t + 1)) ω = 0) := by
  have hEt : S.E t (S.forwardSol β s (t + 1) + D) =ᵐ[S.μ]
      S.E t (S.forwardSol β s (t + 1)) + D := by
    have hIP : Integrable (S.forwardSol β s (t + 1)) S.μ := S.integrable_E _ _
    filter_upwards [S.E_add hIP hDi t] with ω h
    rw [h, Pi.add_apply, Pi.add_apply, S.E_of_stronglyMeasurable hD hDi]
  have hk : S.E (t + 1) (S.forwardSol β s (t + 1)) = S.forwardSol β s (t + 1) :=
    S.E_E_self (t + 1) _
  filter_upwards [mPrice_succ S h' t hpv0', mPrice_succ S h t hpv0, mDebt_eq S hβ0 h' t hpv0',
    mDebt_eq S hβ0 h t hpv0, hPt, hpvD, S.E_congr hpvD t, hEt, h.2.1 t, mEqm_rate_gt S hβ0 h t,
    hpv0, hpv0'] with ω p1 p2 d1 d2 e1 e2 e3 e4 hP hi hY hY'
  have d1' : B' t ω = (1 + i t ω) * P' t ω * pvExM S β s' t ω := d1
  have d2' : B t ω = (1 + i t ω) * P t ω * pvExM S β s t ω := d2
  have hX' : pvExM S β s' t ω = pvExM S β s t ω + β * D ω := by
    simp only [pvExM, Pi.smul_apply, smul_eq_mul]
    rw [e3, e4, Pi.add_apply]
    ring
  have hden : S.forwardSol β s (t + 1) ω + D ω ≠ 0 := by
    have := hY'
    rw [e2, Pi.add_apply] at this
    exact this.ne'
  have hc : (1 + i t ω) * P t ω ≠ 0 := mul_ne_zero (by linarith) hP.ne'
  have hE : pvExM S β s t ω = β * S.E t (S.forwardSol β s (t + 1)) ω := rfl
  rw [p1, p2, d1', d2', e1, hX', e2, Pi.add_apply]
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, hk]
  rw [div_eq_div_iff hden hY.ne', hE]
  constructor
  · intro heq
    have h0 : ((1 + i t ω) * P t ω) * (D ω * (β * (S.forwardSol β s (t + 1) ω -
        S.E t (S.forwardSol β s (t + 1)) ω))) = 0 := by
      linear_combination heq
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 hc
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr ((mul_eq_zero.mp h2).resolve_left hβ0.ne')
  · rintro (h0 | h0)
    · rw [h0]
      ring
    · have e5 : S.E t (S.forwardSol β s (t + 1)) ω = S.forwardSol β s (t + 1) ω := by linarith
      rw [e5]
      ring

/-- Cochrane (2023), p. 50, corrected for uncertainty, on a probability space: a stimulus that
leaves the present-value news unchanged leaves `(B_t/P_t) ΔE_{t+1}(P_t/P_{t+1})` unchanged,
almost surely.
Restates `FiscalMonetary.stimulus_unexpected_inflation` on a genuine probability space. -/
theorem mStimulus_unexpected_inflation (h : MEquilibrium S β Bm1 s B P i)
    (h' : MEquilibrium S β Bm1' s' B' P' i') {t : ℕ}
    (hn : S.innov t (S.forwardSol β s' (t + 1)) =ᵐ[S.μ] S.innov t (S.forwardSol β s (t + 1))) :
    (fun ω => B' t ω / P' t ω * S.innov t (fun ω => P' t ω / P' (t + 1) ω) ω) =ᵐ[S.μ]
      fun ω => B t ω / P t ω * S.innov t (fun ω => P t ω / P (t + 1) ω) ω :=
  (mUnexpected_inflation S h' t).trans (hn.trans (mUnexpected_inflation S h t).symm)

/-! ### The Treasury, the central bank and the flat supply curve (§2.9) -/

/-- Cochrane (2023), eq. (2.28), p. 48, on a probability space: in every equilibrium the debt
sold follows the Treasury rule `B_{t+1} = (B_t − P_{t+1} s_{t+1})(1 + i_{t+1})` almost surely
(bounded adapted surpluses, `0 < β < 1`, positive present values).
Restates `FlatSupply.treasury_rule_of_equilibrium` on a genuine probability space. -/
theorem mTreasury_rule (hβ0 : 0 < β) (hβ1 : β < 1) (hsad : StronglyAdapted S.𝓕 s) {M : ℝ}
    (hsM : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ M) (h : MEquilibrium S β Bm1 s B P i)
    (hpv : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s t ω) (t : ℕ) :
    B (t + 1) =ᵐ[S.μ] fun ω => (B t ω - P (t + 1) ω * s (t + 1) ω) * (1 + i (t + 1) ω) := by
  filter_upwards [mFlow S hβ0 hβ1 hsad hsM h hpv t, h.2.1 (t + 1),
    mEqm_rate_gt S hβ0 h (t + 1)] with ω h1 h2 h3
  have hi : 1 + i (t + 1) ω ≠ 0 := by linarith
  have hP := h2.ne'
  have h4 : B (t + 1) ω / P (t + 1) ω * (1 + i (t + 1) ω)⁻¹ =
      B t ω / P (t + 1) ω - s (t + 1) ω := by linarith
  have key : B (t + 1) ω = (B t ω / P (t + 1) ω - s (t + 1) ω) * (1 + i (t + 1) ω) *
      P (t + 1) ω := by
    rw [← h4, mul_assoc (B (t + 1) ω / P (t + 1) ω), inv_mul_cancel₀ hi, mul_one,
      div_mul_cancel₀ _ hP]
  rw [key, show (B t ω / P (t + 1) ω - s (t + 1) ω) * (1 + i (t + 1) ω) * P (t + 1) ω =
    (B t ω / P (t + 1) ω * P (t + 1) ω - P (t + 1) ω * s (t + 1) ω) * (1 + i (t + 1) ω) by
    ring, div_mul_cancel₀ _ hP]

/-- Cochrane (2023), p. 48, "if the central bank raises interest rates ... the Treasury then
raises the face value of debt it sells" (the flat supply curve), on a probability space: two
equilibria with the same surpluses and the same price level at `t` almost surely sell debt in
the ratio of the gross rates, `B'_t/B_t = (1 + i'_t)/(1 + i_t)` almost surely.
Restates `FiscalMonetary.debt_ratio_of_rate` on a genuine probability space. -/
theorem mDebt_ratio_of_rate (hβ0 : 0 < β) (h : MEquilibrium S β Bm1 s B P i)
    (h' : MEquilibrium S β Bm1' s B' P' i') {t : ℕ} (hPt : P' t =ᵐ[S.μ] P t)
    (hpv : ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s (t + 1) ω) :
    (fun ω => B' t ω / B t ω) =ᵐ[S.μ] fun ω => (1 + i' t ω) / (1 + i t ω) := by
  filter_upwards [mDebt_eq S hβ0 h' t hpv, mDebt_eq S hβ0 h t hpv, hPt, h.2.1 t,
    pvExM_pos_at S hβ0 hpv] with ω e1 e2 e3 e4 e5
  have e1' : B' t ω = (1 + i' t ω) * P' t ω * pvExM S β s t ω := e1
  have e2' : B t ω = (1 + i t ω) * P t ω * pvExM S β s t ω := e2
  rw [e1', e2', e3, mul_assoc, mul_assoc, mul_div_mul_right _ _ (mul_pos e4 e5).ne']

/-- Cochrane (2023), §2.9, p. 48, on a probability space: the debt maturing at `t` in the
two-step process, `D_0 = B_{−1}`, `D_{t+1} = (D_t − (D_t/PV_t) s_t)(1 + i_t)` (the price level
is `D_t/PV_t` and the Treasury sells at the rate the central bank sets).
Restates `FlatSupply.twoStep` on a genuine probability space. -/
noncomputable def mTwoStep (β : ℝ) (Bm1 : Ω → ℝ) (s i : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => Bm1
  | t + 1 => fun ω => (mTwoStep β Bm1 s i t ω -
      mTwoStep β Bm1 s i t ω / S.forwardSol β s t ω * s t ω) * (1 + i t ω)

/-- Cochrane (2023), §2.9, p. 48, on a probability space: the two-step process produces the
interest-rate-target price level, `D_t/PV_t = mPegP_t` almost surely.
Restates `FlatSupply.twoStep_eq_pegP` on a genuine probability space. -/
theorem mTwoStep_eq_pegP (hβ0 : 0 < β) (hβ1 : β < 1) (hsad : StronglyAdapted S.𝓕 s) {M : ℝ}
    (hsM : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ M) (hpv : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s t ω)
    (t : ℕ) :
    (fun ω => mTwoStep S β Bm1 s i t ω / S.forwardSol β s t ω) =ᵐ[S.μ] mPegP S β Bm1 s i t := by
  have ha : |β| < 1 := by rwa [abs_of_pos hβ0]
  induction t with
  | zero => exact Eventually.of_forall fun ω => rfl
  | succ t ih =>
    filter_upwards [ih, pv_eq_add_pvEx S ha hsad hsM t, hpv t] with ω h1 h2 h3
    change (mTwoStep S β Bm1 s i t ω - mTwoStep S β Bm1 s i t ω / S.forwardSol β s t ω *
      s t ω) * (1 + i t ω) / S.forwardSol β s (t + 1) ω = (1 + i t ω) *
        mPegP S β Bm1 s i t ω * pvExM S β s t ω / S.forwardSol β s (t + 1) ω
    have h1' : mTwoStep S β Bm1 s i t ω / S.forwardSol β s t ω = mPegP S β Bm1 s i t ω := h1
    have h2' : S.forwardSol β s t ω = s t ω + pvExM S β s t ω := by
      rw [h2, Pi.add_apply]
    rw [← h1']
    congr 1
    have := h3.ne'
    rw [show pvExM S β s t ω = S.forwardSol β s t ω - s t ω by linarith]
    field_simp

/-- Cochrane (2023), §2.9, p. 48, on a probability space: the debt the Treasury sells in the
two-step process is the target debt, `D_{t+1} = mPegB_t` almost surely.
Restates `FlatSupply.twoStep_debt_eq_pegB` on a genuine probability space. -/
theorem mTwoStep_debt (hβ0 : 0 < β) (hβ1 : β < 1) (hsad : StronglyAdapted S.𝓕 s) {M : ℝ}
    (hsM : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ M) (hpv : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s t ω)
    (t : ℕ) : mTwoStep S β Bm1 s i (t + 1) =ᵐ[S.μ] mPegB S β Bm1 s i t := by
  filter_upwards [mTwoStep_eq_pegP S (Bm1 := Bm1) (i := i) hβ0 hβ1 hsad hsM hpv (t + 1),
    hpv (t + 1)] with ω h1 h2
  have h1' : mTwoStep S β Bm1 s i (t + 1) ω / S.forwardSol β s (t + 1) ω =
      (1 + i t ω) * mPegP S β Bm1 s i t ω * pvExM S β s t ω / S.forwardSol β s (t + 1) ω := h1
  exact (div_left_inj' h2.ne').mp h1'

/-- Cochrane (2023), §2.9, p. 48: the two-step debt is adapted. -/
theorem mTwoStep_sm (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1) (hsad : StronglyAdapted S.𝓕 s)
    (hia : StronglyAdapted S.𝓕 i) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (mTwoStep S β Bm1 s i t) ∧
      StronglyMeasurable[S.𝓕 t] (mTwoStep S β Bm1 s i (t + 1)) := by
  have hstep : ∀ t, StronglyMeasurable[S.𝓕 t] (mTwoStep S β Bm1 s i t) →
      StronglyMeasurable[S.𝓕 t] (mTwoStep S β Bm1 s i (t + 1)) := fun t ht =>
    ((ht.measurable.sub ((ht.measurable.div (S.forwardSol_adapted β s t).measurable).mul
      (hsad t).measurable)).mul ((hia t).measurable.const_add 1)).stronglyMeasurable
  have hall : ∀ t, StronglyMeasurable[S.𝓕 t] (mTwoStep S β Bm1 s i t) := by
    intro t
    induction t with
    | zero => exact hBm1
    | succ t ih => exact (hstep t ih).mono (S.𝓕.mono (Nat.le_succ t))
  exact ⟨hall t, hstep t (hall t)⟩

/-- Cochrane (2023), §2.9, p. 48, "the central bank plus Treasury thus really do sell any
quantity of debt at the fixed interest rate", on a probability space: under the hypotheses of
`TidyR6MeasHyp.mPeg_equilibrium_pos` (with bounded adapted surpluses and `β < 1`) the two-step
process is an equilibrium with the target `i`.
Restates `FlatSupply.twoStep_equilibrium` on a genuine probability space. -/
theorem mTwoStep_equilibrium (hβ0 : 0 < β) (hβ1 : β < 1) (hsad : StronglyAdapted S.𝓕 s)
    {M : ℝ} (hsM : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ M) (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1)
    (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω) (hia : StronglyAdapted S.𝓕 i)
    (hi : ∀ t, ∀ᵐ ω ∂S.μ, -1 < i t ω) (hQi : ∀ t, Integrable (fun ω => (1 + i t ω)⁻¹) S.μ)
    (hpv : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s t ω) :
    MEquilibrium S β Bm1 s (fun t => mTwoStep S β Bm1 s i (t + 1))
      (fun t ω => mTwoStep S β Bm1 s i t ω / S.forwardSol β s t ω) i :=
  TidyR5MeasFamily.mEquilibrium_congr S
    (TidyR6MeasHyp.mPeg_equilibrium_pos S hβ0 hBm1 hB hia hi hQi hpv)
    (fun t => ((mTwoStep_sm S hBm1 hsad hia t).1.measurable.div
      (S.forwardSol_adapted β s t).measurable).stronglyMeasurable)
    (fun t => (mTwoStep_sm S hBm1 hsad hia t).2)
    (fun t => mTwoStep_eq_pegP S hβ0 hβ1 hsad hsM hpv t)
    (fun t => mTwoStep_debt S hβ0 hβ1 hsad hsM hpv t)

/-! ### Links to the core versions on finite trees -/

namespace Link

open ExpectationsFiniteTree TreeBridge HouseholdMeasureTVC.Link TidyR5MeasLinear.Link

variable {Ω' : Type*} [Fintype Ω'] [MeasurableSpace Ω'] [DiscreteMeasurableSpace Ω']
  (T : FiniteTree Ω')

/-- Cochrane (2023), p. 31: on a finite tree the measure-theoretic revenue result gives the core
statement in every state: in every `FiscalMonetary.Equilibrium` with `β > 0` and positive present
values, `(B_t/P_t)/(1 + i_t) = FiscalMonetary.pvEx`. -/
theorem tree_mRevenue {β : ℝ} (hβ0 : 0 < β) {Bm1 : Ω' → ℝ} {s B P i : ℕ → Ω' → ℝ}
    (h : FiscalMonetary.Equilibrium T.toExpectationSystem β Bm1 s B P i)
    (hpv : ∀ t ω, 0 < FiscalMonetary.pv T.toExpectationSystem β s t ω) (t : ℕ) (ω : Ω') :
    B t ω / P t ω * (1 + i t ω)⁻¹ = FiscalMonetary.pvEx T.toExpectationSystem β s t ω := by
  have hm := (tree_mEquilibrium_iff T hβ0).mpr h
  have hpv' : ∀ᵐ ω ∂(treeSystem T).μ, 0 < (treeSystem T).forwardSol β s (t + 1) ω :=
    Eventually.of_forall fun ω => by rw [tree_forwardSol]; exact hpv (t + 1) ω
  have e := congrFun (eq_of_ae T (mRevenue (treeSystem T) hβ0 hm t hpv')) ω
  rw [tree_pvExM] at e
  exact e

/-- Cochrane (2023), eq. (2.28), p. 48: on a finite tree the measure-theoretic Treasury rule
gives the core one (`FlatSupply.treasury_rule_of_equilibrium`) in every state, for bounded
adapted surpluses and positive present values. -/
theorem tree_mTreasury_rule {β M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Bm1 : Ω' → ℝ}
    {s B P i : ℕ → Ω' → ℝ} (hsa : T.toExpectationSystem.Adapted s) (hs : ∀ t ω, |s t ω| ≤ M)
    (h : FiscalMonetary.Equilibrium T.toExpectationSystem β Bm1 s B P i)
    (hpv : ∀ t ω, 0 < FiscalMonetary.pv T.toExpectationSystem β s t ω) (t : ℕ) (ω : Ω') :
    B (t + 1) ω = (B t ω - P (t + 1) ω * s (t + 1) ω) * (1 + i (t + 1) ω) := by
  have hm := (tree_mEquilibrium_iff T hβ0).mpr h
  have hpv' : ∀ t, ∀ᵐ ω ∂(treeSystem T).μ, 0 < (treeSystem T).forwardSol β s t ω := fun t =>
    Eventually.of_forall fun ω => by rw [tree_forwardSol]; exact hpv t ω
  have e := eq_of_ae T (mTreasury_rule (treeSystem T) hβ0 hβ1 ((tree_adapted_iff T s).mpr hsa)
    (fun t => Eventually.of_forall (hs t)) hm hpv' t)
  exact congrFun e ω

end Link

/-! ### The i.i.d. `±1` coin economy: AR(1) news and fiscal stimulus -/

namespace Coin

open ExpectationsMeasureIID

/-- Cochrane (2023), Ch. 2, p. 29: the fair coin never lands on `0`. -/
theorem coin_ne_zero : ∀ᵐ x ∂(coin : Measure ℝ), x ≠ 0 := by
  change ∀ᵐ x ∂coinMeasure, x ≠ 0
  rw [ae_iff]
  have e : {x : ℝ | ¬ x ≠ 0} = {0} := by
    ext x
    simp
  rw [e]
  simp [coinMeasure]

/-- Cochrane (2023), Ch. 2, p. 29: in the coin economy every shock is nonzero almost surely. -/
theorem shock_ne_zero (t : ℕ) : ∀ᵐ ω ∂(iidSystem coin).μ, shock t ω ≠ 0 :=
  (measurePreserving_eval_infinitePi (fun _ => (coin : Measure ℝ)) t).quasiMeasurePreserving.ae
    coin_ne_zero

/-- Cochrane (2023), p. 43, in the i.i.d. `±1` coin economy: for the AR(1) surplus
`s_{t+1} = η s_t + ε_{t+1}` (`ExpectationsMeasureIID.ar1`, `|η| < 1`), `0 ≤ β < 1`, the
present-value news is `ε_{t+1}/(1 − βη)` almost surely, and it is nonzero almost surely: fiscal
news, hence unexpected inflation, is genuinely random. -/
theorem coin_ar1_news {β η : ℝ} (hη : |η| < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hβη : |β * η| < 1) (t : ℕ) :
    (iidSystem coin).innov t ((iidSystem coin).forwardSol β (ar1 η) (t + 1)) =ᵐ[(iidSystem coin).μ]
        (1 - β * η)⁻¹ • shock (t + 1) ∧
      ∀ᵐ ω ∂(iidSystem coin).μ,
        (iidSystem coin).innov t ((iidSystem coin).forwardSol β (ar1 η) (t + 1)) ω ≠ 0 := by
  have h := mAr1_pv_news (iidSystem coin) hβ0 hβ1 hβη (ar1_adapted coin η)
    ⟨_, fun t => ar1_bdd hη coin_bdd t⟩ (ar1_succ η) (E_shock_zero coin_mean) t
  have h1 : 1 - β * η ≠ 0 := by
    have := (abs_lt.mp hβη).2
    linarith
  refine ⟨h, ?_⟩
  filter_upwards [h, shock_ne_zero (t + 1)] with ω e1 e2
  rw [e1, Pi.smul_apply, smul_eq_mul]
  exact mul_ne_zero (inv_ne_zero h1) e2

/-- Cochrane (2023), p. 50: the indicator `1` of heads (`x ≥ 1`). -/
noncomputable def hd (x : ℝ) : ℝ := if 1 ≤ x then 1 else 0

/-- Cochrane (2023), p. 50: the indicator of heads is measurable. -/
theorem measurable_hd : Measurable hd :=
  Measurable.ite measurableSet_Ici measurable_const measurable_const

/-- Cochrane (2023), p. 50: the indicator of heads is `0` or `1`. -/
theorem hd_cases (x : ℝ) : hd x = 0 ∨ hd x = 1 := by
  unfold hd
  split_ifs <;> simp

/-- Cochrane (2023), p. 50: the indicator of heads is nonnegative. -/
theorem hd_nonneg (x : ℝ) : 0 ≤ hd x := by
  rcases hd_cases x with h | h <;> rw [h]; norm_num

/-- Cochrane (2023), p. 50: `|a + b hd| ≤ |a| + |b|`. -/
theorem abs_aff_hd_le (a b x : ℝ) : |a + b * hd x| ≤ |a| + |b| := by
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  rcases hd_cases x with h | h <;> rw [h] <;> simp

/-- Cochrane (2023), p. 50: from date `1` on, a function `a + b hd(ε_1)` of the date-`1` coin is
its own forecast. -/
theorem E_late {t : ℕ} (ht : 1 ≤ t) (a b : ℝ) :
    (iidSystem coin).E t (fun ω => a + b * hd (ω 1)) = fun ω => a + b * hd (ω 1) := by
  have hm : Measurable[(iidSystem coin).𝓕 t] (fun ω : ℕ → ℝ => a + b * hd (shock 1 ω)) :=
    measurable_const.add (measurable_const.mul (measurable_hd.comp (measurable_shock coin ht)))
  have hi : Integrable (fun ω : ℕ → ℝ => a + b * hd (ω 1)) (iidSystem coin).μ :=
    Integrable.of_bound (C := |a| + |b|) ((hm.mono ((iidSystem coin).𝓕.le t) le_rfl
      ).aestronglyMeasurable) (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        exact abs_aff_hd_le a b (ω 1))
  exact (iidSystem coin).E_of_stronglyMeasurable hm.stronglyMeasurable hi

/-- Cochrane (2023), p. 50: at date `0`, `E_0(a + b hd(ε_1)) = a + b/2` almost surely. -/
theorem E_zero_fun (a b : ℝ) :
    (iidSystem coin).E 0 (fun ω => a + b * hd (ω 1)) =ᵐ[(iidSystem coin).μ]
      fun _ => a + b / 2 := by
  have h := E_shock_fun coin 0 (f := fun x => a + b * hd x)
    (measurable_const.add (measurable_const.mul measurable_hd))
  have hI : ∫ x, (fun x => a + b * hd x) x ∂(coin : Measure ℝ) = a + b / 2 := by
    rw [integral_coin]
    norm_num [hd]
    ring
  rw [hI] at h
  exact h

/-- Cochrane (2023), p. 50: baseline surpluses, `s_0 = 1`, `s_t = 1 + hd(ε_1)` for `t ≥ 1`.
Restates `FiscalMonetary.CoinExample.sB` on a genuine probability space. -/
noncomputable def sB : ℕ → (ℕ → ℝ) → ℝ := fun t ω => if t = 0 then 1 else 1 + hd (ω 1)

/-- Cochrane (2023), p. 50: the stimulus `s'_0 = s_0 − 1/2`, `s'_1 = s_1 + 1`, `s'_t = s_t`
otherwise.
Restates `FiscalMonetary.CoinExample.sS` on a genuine probability space. -/
noncomputable def sS : ℕ → (ℕ → ℝ) → ℝ := fun t ω =>
  if t = 0 then 1 / 2 else if t = 1 then 2 + hd (ω 1) else 1 + hd (ω 1)

/-- Cochrane (2023), eq. (2.7), p. 22: with `β = 1/2`, a constant tail `c` from date `t` on
gives the discounted sum `2c`. -/
theorem discSum_tail {f : ℕ → (ℕ → ℝ) → ℝ} {t : ℕ} {c : (ℕ → ℝ) → ℝ}
    (h : ∀ k, f (t + k) = c) :
    MeasExpectationSystem.discSum (1 / 2 : ℝ) f t = fun ω => 2 * c ω := by
  funext ω
  simp only [MeasExpectationSystem.discSum, h]
  rw [tsum_mul_right, tsum_geometric_two]

/-- Cochrane (2023), p. 50: the surpluses are bounded by `3`. -/
theorem sB_sS_bdd (t : ℕ) (ω : ℕ → ℝ) : |sB t ω| ≤ 3 ∧ |sS t ω| ≤ 3 := by
  have h0 := hd_nonneg (ω 1)
  have h1 : hd (ω 1) ≤ 1 := by rcases hd_cases (ω 1) with h | h <;> rw [h]; norm_num
  unfold sB sS
  constructor
  · split_ifs
    · norm_num
    · rw [abs_le]
      constructor <;> linarith
  · split_ifs
    · norm_num
    · rw [abs_le]
      constructor <;> linarith
    · rw [abs_le]
      constructor <;> linarith

/-- Cochrane (2023), p. 50: from date `1` on, the baseline discounted sum is `2(1 + hd(ε_1))`. -/
theorem discSum_sB {t : ℕ} (ht : 1 ≤ t) :
    MeasExpectationSystem.discSum (1 / 2 : ℝ) sB t = fun ω => 2 + 2 * hd (ω 1) := by
  rw [discSum_tail (c := fun ω => 1 + hd (ω 1)) (fun k => funext fun ω => by
    simp only [sB, show t + k ≠ 0 by omega, ↓reduceIte])]
  funext ω
  ring

/-- Cochrane (2023), p. 50: from date `2` on, the stimulus discounted sum is `2(1 + hd(ε_1))`. -/
theorem discSum_sS {t : ℕ} (ht : 2 ≤ t) :
    MeasExpectationSystem.discSum (1 / 2 : ℝ) sS t = fun ω => 2 + 2 * hd (ω 1) := by
  rw [discSum_tail (c := fun ω => 1 + hd (ω 1)) (fun k => funext fun ω => by
    simp only [sS, show t + k ≠ 0 by omega, show t + k ≠ 1 by omega, ↓reduceIte])]
  funext ω
  ring

/-- Cochrane (2023), p. 50: the recursion of the discounted sums. -/
theorem discSum_rec' (f : ℕ → (ℕ → ℝ) → ℝ) (hf : ∀ t ω, |f t ω| ≤ 3) (t : ℕ) (ω : ℕ → ℝ) :
    MeasExpectationSystem.discSum (1 / 2 : ℝ) f t ω =
      f t ω + 1 / 2 * MeasExpectationSystem.discSum (1 / 2 : ℝ) f (t + 1) ω :=
  MeasExpectationSystem.discSum_succ (MeasExpectationSystem.summable_geom_mul
    (by norm_num : |(1 / 2 : ℝ)| < 1) fun k => hf (t + k) ω)

/-- Cochrane (2023), p. 50: at date `1` the stimulus discounted sum is `3 + 2 hd(ε_1)`. -/
theorem discSum_sS_one :
    MeasExpectationSystem.discSum (1 / 2 : ℝ) sS 1 = fun ω => 3 + 2 * hd (ω 1) := by
  funext ω
  rw [discSum_rec' sS (fun t ω => (sB_sS_bdd t ω).2) 1 ω, discSum_sS (le_refl 2)]
  simp only [sS, one_ne_zero, ↓reduceIte]
  ring

/-- Cochrane (2023), p. 50: at date `0` both discounted sums are `2 + hd(ε_1)`, state by state:
the stimulus leaves the realised present value unchanged. -/
theorem discSum_zero :
    MeasExpectationSystem.discSum (1 / 2 : ℝ) sS 0 = (fun ω => 2 + hd (ω 1)) ∧
      MeasExpectationSystem.discSum (1 / 2 : ℝ) sB 0 = fun ω => 2 + hd (ω 1) := by
  constructor
  · funext ω
    rw [discSum_rec' sS (fun t ω => (sB_sS_bdd t ω).2) 0 ω, zero_add, discSum_sS_one]
    simp only [sS, ↓reduceIte]
    ring
  · funext ω
    rw [discSum_rec' sB (fun t ω => (sB_sS_bdd t ω).1) 0 ω, zero_add, discSum_sB le_rfl]
    simp only [sB, ↓reduceIte]
    ring

/-- Cochrane (2023), p. 50: the present values of the two surplus paths in the coin economy:
`PV_0 = 5/2` almost surely for both, `PV_t = 2 + 2hd(ε_1)` for the baseline at `t ≥ 1`, and for
the stimulus `PV_1 = 3 + 2hd(ε_1)`, `PV_t = 2 + 2hd(ε_1)` at `t ≥ 2`. -/
theorem pv_values :
    (iidSystem coin).forwardSol (1 / 2) sS 0 = (iidSystem coin).forwardSol (1 / 2) sB 0 ∧
      (iidSystem coin).forwardSol (1 / 2) sB 0 =ᵐ[(iidSystem coin).μ] (fun _ => 5 / 2) ∧
      (∀ t, 1 ≤ t → (iidSystem coin).forwardSol (1 / 2) sB t = fun ω => 2 + 2 * hd (ω 1)) ∧
      (iidSystem coin).forwardSol (1 / 2) sS 1 = (fun ω => 3 + 2 * hd (ω 1)) ∧
      ∀ t, 2 ≤ t → (iidSystem coin).forwardSol (1 / 2) sS t = fun ω => 2 + 2 * hd (ω 1) := by
  refine ⟨?_, ?_, fun t ht => ?_, ?_, fun t ht => ?_⟩
  · change (iidSystem coin).E 0 _ = (iidSystem coin).E 0 _
    rw [discSum_zero.1, discSum_zero.2]
  · change (iidSystem coin).E 0 _ =ᵐ[_] _
    rw [discSum_zero.2]
    have h := E_zero_fun 2 1
    simp only [one_mul] at h
    refine h.trans (Eventually.of_forall fun _ => ?_)
    norm_num
  · change (iidSystem coin).E t _ = _
    rw [discSum_sB ht, E_late ht]
  · change (iidSystem coin).E 1 _ = _
    rw [discSum_sS_one, E_late le_rfl]
  · change (iidSystem coin).E t _ = _
    rw [discSum_sS ht, E_late (by omega)]

/-- Cochrane (2023), p. 50: all present values are positive almost surely, for both surplus
paths. -/
theorem pv_pos : (∀ t, ∀ᵐ ω ∂(iidSystem coin).μ, 0 < (iidSystem coin).forwardSol (1 / 2) sB t ω) ∧
    ∀ t, ∀ᵐ ω ∂(iidSystem coin).μ, 0 < (iidSystem coin).forwardSol (1 / 2) sS t ω := by
  obtain ⟨h0, h05, hB, hS1, hS⟩ := pv_values
  have hpos : ∀ a b : ℝ, 0 < a → 0 ≤ b → ∀ ω : ℕ → ℝ, 0 < a + b * hd (ω 1) := fun a b ha hb ω =>
    add_pos_of_pos_of_nonneg ha (mul_nonneg hb (hd_nonneg _))
  refine ⟨fun t => ?_, fun t => ?_⟩
  · rcases Nat.eq_zero_or_pos t with rfl | ht
    · filter_upwards [h05] with ω h
      rw [h]
      norm_num
    · rw [hB t ht]
      exact Eventually.of_forall (hpos 2 2 (by norm_num) (by norm_num))
  · rcases Nat.lt_or_ge t 2 with ht | ht
    · interval_cases t
      · filter_upwards [h05] with ω h
        rw [h0, h]
        norm_num
      · rw [hS1]
        exact Eventually.of_forall (hpos 3 2 (by norm_num) (by norm_num))
    · rw [hS t ht]
      exact Eventually.of_forall (hpos 2 2 (by norm_num) (by norm_num))

/-- Cochrane (2023), p. 50: the zero rate target is adapted, exceeds `−1` and has integrable
bond price. -/
theorem zeroRate_ok :
    StronglyAdapted (iidSystem coin).𝓕 (fun (_ : ℕ) (_ : ℕ → ℝ) => (0 : ℝ)) ∧
      (∀ t, ∀ᵐ ω ∂(iidSystem coin).μ, -1 < (fun (_ : ℕ) (_ : ℕ → ℝ) => (0 : ℝ)) t ω) ∧
      ∀ t, Integrable (fun ω => (1 + (fun (_ : ℕ) (_ : ℕ → ℝ) => (0 : ℝ)) t ω)⁻¹)
        (iidSystem coin).μ :=
  ⟨fun _ => stronglyMeasurable_const, fun _ => Eventually.of_forall fun _ => by norm_num,
    fun _ => (integrable_const (1 : ℝ)).congr (Eventually.of_forall fun _ => by simp)⟩

/-- Cochrane (2023), p. 50, counterexample to "borrow money, don't drive up interest rates, spend
the money, repay the debt — has no effect at all on current, unexpected, or expected future
inflation", **on a genuine probability space** (the i.i.d. `±1` coin, in which every history is
null, `ExpectationsMeasureIID.coin_economy`): with `β = 1/2`, `B_{−1} = 1`, the target `i ≡ 0`,
the baseline `sB` and the stimulus `sS` (`s'_0 = s_0 − 1/2`, `s'_1 = s_1 + 1`, `s'_t = s_t`
otherwise), the date-`0` present values are equal state by state, both surplus paths have an
equilibrium, and for **every** pair of equilibria the date-`0` price level and expected inflation
agree almost surely while the date-`1` price levels differ almost surely.
Restates `FiscalMonetary.CoinExample.stimulus_not_neutral` on a genuine probability space. -/
theorem coin_stimulus_not_neutral :
    (sS 0 = fun ω => sB 0 ω - 1 / 2) ∧ (sS 1 = fun ω => sB 1 ω + 1) ∧
      (∀ t, 2 ≤ t → sS t = sB t) ∧
      (iidSystem coin).forwardSol (1 / 2) sS 0 = (iidSystem coin).forwardSol (1 / 2) sB 0 ∧
      MEquilibrium (iidSystem coin) (1 / 2) (fun _ => 1) sB
        (mPegB (iidSystem coin) (1 / 2) (fun _ => 1) sB fun _ _ => 0)
        (mPegP (iidSystem coin) (1 / 2) (fun _ => 1) sB fun _ _ => 0) (fun _ _ => 0) ∧
      MEquilibrium (iidSystem coin) (1 / 2) (fun _ => 1) sS
        (mPegB (iidSystem coin) (1 / 2) (fun _ => 1) sS fun _ _ => 0)
        (mPegP (iidSystem coin) (1 / 2) (fun _ => 1) sS fun _ _ => 0) (fun _ _ => 0) ∧
      ∀ B P B' P' : ℕ → (ℕ → ℝ) → ℝ,
        MEquilibrium (iidSystem coin) (1 / 2) (fun _ => 1) sB B P (fun _ _ => 0) →
        MEquilibrium (iidSystem coin) (1 / 2) (fun _ => 1) sS B' P' (fun _ _ => 0) →
        P' 0 =ᵐ[(iidSystem coin).μ] P 0 ∧
        (iidSystem coin).E 0 (fun ω => P' 0 ω / P' 1 ω) =ᵐ[(iidSystem coin).μ]
          (iidSystem coin).E 0 (fun ω => P 0 ω / P 1 ω) ∧
        ∀ᵐ ω ∂(iidSystem coin).μ, P' 1 ω ≠ P 1 ω := by
  set CS := iidSystem coin
  obtain ⟨hpv0, hpv05, hpvB, hpvS1, -⟩ := pv_values
  obtain ⟨hposB, hposS⟩ := pv_pos
  obtain ⟨hia, hi, hQi⟩ := zeroRate_ok
  have hBm1 : StronglyMeasurable[CS.𝓕 0] (fun _ : ℕ → ℝ => (1 : ℝ)) := stronglyMeasurable_const
  have hB : ∀ᵐ ω ∂CS.μ, 0 < (fun _ : ℕ → ℝ => (1 : ℝ)) ω := Eventually.of_forall fun _ => one_pos
  have hβ : (0 : ℝ) < 1 / 2 := by norm_num
  have hEB := TidyR6MeasHyp.mPeg_equilibrium_pos CS hβ hBm1 hB hia hi hQi hposB
  have hES := TidyR6MeasHyp.mPeg_equilibrium_pos CS hβ hBm1 hB hia hi hQi hposS
  refine ⟨funext fun ω => by norm_num [sS, sB], funext fun ω => by (simp [sS, sB]; ring),
    fun t ht => funext fun ω => by
      simp only [sS, sB, show t ≠ 0 by omega, show t ≠ 1 by omega, ↓reduceIte],
    hpv0, hEB, hES, fun B P B' P' h h' => ?_⟩
  have hP0 : mPegP CS (1 / 2) (fun _ => 1) sS (fun _ _ => 0) 0 =
      mPegP CS (1 / 2) (fun _ => 1) sB (fun _ _ => 0) 0 := by
    change (fun ω => (1 : ℝ) / CS.forwardSol (1 / 2) sS 0 ω) =
      fun ω => (1 : ℝ) / CS.forwardSol (1 / 2) sB 0 ω
    rw [hpv0]
  obtain ⟨u0, -⟩ := TidyR6MeasHyp.mPeg_unique_pos CS hβ hposB h 0
  obtain ⟨u0', -⟩ := TidyR6MeasHyp.mPeg_unique_pos CS hβ hposS h' 0
  obtain ⟨u1, -⟩ := TidyR6MeasHyp.mPeg_unique_pos CS hβ hposB h 1
  obtain ⟨u1', -⟩ := TidyR6MeasHyp.mPeg_unique_pos CS hβ hposS h' 1
  refine ⟨u0'.trans (hP0 ▸ u0.symm), ?_, ?_⟩
  · filter_upwards [mExpected_inflation CS (by norm_num) h' 0,
      mExpected_inflation CS (by norm_num) h 0] with ω e1 e2
    rw [e1, e2]
  · have hEB1 : CS.E 0 (CS.forwardSol (1 / 2) sB 1) =ᵐ[CS.μ] fun _ => 3 := by
      rw [hpvB 1 le_rfl]
      refine (E_zero_fun 2 2).trans (Eventually.of_forall fun _ => ?_)
      norm_num
    have hES1 : CS.E 0 (CS.forwardSol (1 / 2) sS 1) =ᵐ[CS.μ] fun _ => 4 := by
      rw [hpvS1]
      refine (E_zero_fun 3 2).trans (Eventually.of_forall fun _ => ?_)
      norm_num
    filter_upwards [u1, u1', hEB1, hES1, TidyR6MeasHyp.mPegP_pos_ae CS hβ hB hi hposB 0]
      with ω e1 e2 e3 e4 e5
    rw [e1, e2]
    change (1 + (0 : ℝ)) * mPegP CS (1 / 2) (fun _ => 1) sS (fun _ _ => 0) 0 ω *
        ((1 / 2 : ℝ) * CS.E 0 (CS.forwardSol (1 / 2) sS 1) ω) / CS.forwardSol (1 / 2) sS 1 ω ≠
      (1 + (0 : ℝ)) * mPegP CS (1 / 2) (fun _ => 1) sB (fun _ _ => 0) 0 ω *
        ((1 / 2 : ℝ) * CS.E 0 (CS.forwardSol (1 / 2) sB 1) ω) / CS.forwardSol (1 / 2) sB 1 ω
    rw [hP0, e3, e4, hpvB 1 le_rfl, hpvS1]
    have hp := e5.ne'
    have h0 := hd_nonneg (ω 1)
    have hA : (3 : ℝ) + 2 * hd (ω 1) ≠ 0 := by positivity
    have hC : (2 : ℝ) + 2 * hd (ω 1) ≠ 0 := by positivity
    intro heq
    rw [div_eq_div_iff hA hC] at heq
    have : mPegP CS (1 / 2) (fun _ => 1) sB (fun _ _ => 0) 0 ω * (1 - 2 * hd (ω 1)) = 0 := by
      linear_combination (-2 : ℝ) * heq
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hp h1
    · rcases hd_cases (ω 1) with h2 | h2 <;> rw [h2] at h1 <;> norm_num at h1

end Coin


end Cochrane.IntertemporalModel.TidyR6MeasFiscal
