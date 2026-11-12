/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.TidyR6MeasSigned

/-!
# Interest-rate targets when present values vanish on part of the space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.1, pp. 21–23, §2.4,
pp. 29–33 (interest-rate targets), (2.26), p. 42, and (2.28), p. 48, on a probability space.

`TidyR6MeasSigned` characterised target equilibria when present values are nonzero almost surely.
Here present values may vanish on any part of the space.

* `mDebt_eq_general`: in every equilibrium `B_t = (1 + i_t) P_t PVex_t` almost surely, with no
  condition on the sign or on zeros of debt (`β > 0`).
* `mEqm_zero_conditions`: every equilibrium satisfies `B_{−1} = 0 ⇔ PV_0 = 0`, `B_{−1} PV_0 ≥ 0`,
  and at every date `PV_{t+1} = 0 ⇔ E_t PV_{t+1} = 0`, `PV_{t+1} E_t PV_{t+1} ≥ 0` (almost surely):
  the event where the present value vanishes is known a period ahead.
* `mPeg_exists_iff_general` (headline): for `β > 0`, `B_{−1}` known at `0` and an adapted target,
  an equilibrium exists **iff** the bond price is integrable, `i > −1` almost surely, and these
  conditions hold. The witness is `zP`, `zB`: off the zero event it is the target path, on it the
  price level grows at `β(1 + i_t)`.
* Non-uniqueness: `nonunique_date0` (if `{PV_0 = 0}` has positive probability, the price level is
  free there: scaling it by `2` gives another equilibrium), `nonunique_news` (if
  `{PV_{t+1} = 0} = {B_t = 0}` receives news at `t + 1`, the price level `P_{t+1}` there can be
  moved by that news). The precise statement is that positive probability alone does not suffice
  at later dates: `pinned_of_known` (with no news at `t + 1` the bond price pins
  `P_{t+1} = β(1 + i_t)P_t`) and `TwoState.unique_with_zero_pv` (two equally likely states, full
  information, `{PV_1 = 0}` of probability `1/2`, yet the equilibrium is unique almost surely).
* Signed versions with no positivity at all: `mFlow_signed` ((2.4)/(2.26)), `mTreasury_rule_signed`
  ((2.28)); the two-step process with debt of either sign: `mTwoStep_eq_pegP_signed`,
  `mTwoStep_debt_signed`, `mTwoStep_equilibrium_signed`.
-/

namespace Cochrane.IntertemporalModel.TidyR6MeasZero

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure TidyR5Meas
  TidyR6MeasL1

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)
variable {β : ℝ} {Bm1 : Ω → ℝ} {s B P i : ℕ → Ω → ℝ}

/-! ### The debt formula and the necessary conditions -/

/-- Cochrane (2023), eq. (2.15), p. 31, on a probability space, **with no condition on debt**: in
every equilibrium with `β > 0`, `B_t = (1 + i_t) P_t PVex_t` almost surely (where `B_t = 0` both
sides vanish because `E_t PV_{t+1} = 0` there).
Generalises `TidyR6MeasSigned.mDebt_eq_signed`. and `TidyR5Meas.mDebt_eq`. -/
theorem mDebt_eq_general (hβ0 : 0 < β) (h : MEquilibrium S β Bm1 s B P i) (t : ℕ) :
    B t =ᵐ[S.μ] fun ω => (1 + i t ω) * P t ω * pvExM S β s t ω := by
  have hrate := mEqm_rate_gt S hβ0 h t
  obtain ⟨hPa, hP, hBa, -, hint, ⟨-, hv⟩, hbp⟩ := h
  have hZ : MeasurableSet[S.𝓕 t] {ω | B t ω = 0} :=
    measurableSet_eq_fun (hBa t).measurable measurable_const
  set g : Ω → ℝ := S.forwardSol β s (t + 1) with hg
  have hgi : Integrable g S.μ := S.integrable_E _ _
  set f : Ω → ℝ := fun ω => if B t ω = 0 then 0 else P t ω / B t ω with hf
  set ind : Ω → ℝ := fun ω => if B t ω = 0 then 0 else 1 with hind
  set ind0 : Ω → ℝ := fun ω => if B t ω = 0 then 1 else 0 with hind0
  have hfm : StronglyMeasurable[S.𝓕 t] f :=
    (Measurable.ite hZ measurable_const ((hPa t).measurable.div (hBa t).measurable)
      ).stronglyMeasurable
  have hindm : StronglyMeasurable[S.𝓕 t] ind :=
    (Measurable.ite hZ measurable_const measurable_const).stronglyMeasurable
  have hind0m : StronglyMeasurable[S.𝓕 t] ind0 :=
    (Measurable.ite hZ measurable_const measurable_const).stronglyMeasurable
  have hb1 : ∀ᵐ ω ∂S.μ, |ind ω| ≤ 1 := Eventually.of_forall fun ω => by
    simp only [hind]
    split_ifs <;> norm_num
  have hb0 : ∀ᵐ ω ∂S.μ, |ind0 ω| ≤ 1 := Eventually.of_forall fun ω => by
    simp only [hind0]
    split_ifs <;> norm_num
  have hfg : f * g =ᵐ[S.μ] ind * fun ω => P t ω / P (t + 1) ω := by
    filter_upwards [hv t, hP (t + 1)] with ω h1 h2
    have e1 : B t ω / P (t + 1) ω = S.forwardSol β s (t + 1) ω := h1
    simp only [Pi.mul_apply, hf, hind, hg]
    split_ifs with hB
    · simp
    · rw [← e1]
      have := h2.ne'
      field_simp
  have h0g : ind0 * g =ᵐ[S.μ] 0 := by
    filter_upwards [hv t] with ω h1
    have e1 : B t ω / P (t + 1) ω = S.forwardSol β s (t + 1) ω := h1
    simp only [Pi.mul_apply, hind0, hg, Pi.zero_apply]
    split_ifs with hB
    · rw [← e1, hB, zero_div, mul_zero]
    · rw [zero_mul]
  have hpo := condExp_mul_of_stronglyMeasurable_left hfm
    ((hb1.mono fun ω h => by rwa [Real.norm_eq_abs]) |> fun hb =>
      ((hint t).bdd_mul (hindm.mono (S.𝓕.le t)).aestronglyMeasurable hb).congr hfg.symm) hgi
  filter_upwards [hbp t, S.E_congr hfg t, hpo, S.E_pullOut hindm hb1 (hint t),
    S.E_pullOut hind0m hb0 hgi, S.E_congr h0g t, hrate, hP t] with ω h1 h2 h3 h4 h5 h6 h7 h8
  have h3' : S.E t (f * g) ω = f ω * S.E t g ω := h3
  have h4' : S.E t (ind * fun ω => P t ω / P (t + 1) ω) ω =
      ind ω * S.E t (fun ω => P t ω / P (t + 1) ω) ω := h4
  have h5' : S.E t (ind0 * g) ω = ind0 ω * S.E t g ω := h5
  have h6' : S.E t (ind0 * g) ω = 0 := by rw [h6, S.E_zero]; rfl
  have h1' : (1 + i t ω)⁻¹ = β * S.E t (fun ω => P t ω / P (t + 1) ω) ω := h1
  change B t ω = (1 + i t ω) * P t ω * (β * S.E t g ω)
  by_cases hB : B t ω = 0
  · have : S.E t g ω = 0 := by
      rw [h5'] at h6'
      simpa [hind0, hB] using h6'
    rw [hB, this]
    ring
  · rw [h2, h4'] at h3'
    simp only [hf, hind, hB, ↓reduceIte, one_mul] at h3'
    have hne : 1 + i t ω ≠ 0 := by linarith
    rw [h3'] at h1'
    have := h8.ne'
    field_simp at h1'
    linear_combination h1'

/-- Cochrane (2023), pp. 22, 30–33, on a probability space, **the conditions every equilibrium
satisfies** (`β > 0`): almost surely `B_{−1} = 0 ⇔ PV_0 = 0` and `B_{−1} PV_0 ≥ 0`, and at every
date `PV_{t+1} = 0 ⇔ E_t PV_{t+1} = 0` and `PV_{t+1} E_t PV_{t+1} ≥ 0`.
Generalises `TidyR6MeasSigned.mEqm_sign`, `TidyR6MeasSigned.mEqm_sign_condition` and
`TidyR6MeasHyp.mEqm_pv_zero_pos`. -/
theorem mEqm_zero_conditions (hβ0 : 0 < β) (h : MEquilibrium S β Bm1 s B P i) :
    (∀ᵐ ω ∂S.μ, (Bm1 ω = 0 ↔ S.forwardSol β s 0 ω = 0) ∧
      0 ≤ Bm1 ω * S.forwardSol β s 0 ω) ∧
    ∀ t, ∀ᵐ ω ∂S.μ, (S.forwardSol β s (t + 1) ω = 0 ↔
      S.E t (S.forwardSol β s (t + 1)) ω = 0) ∧
      0 ≤ S.forwardSol β s (t + 1) ω * S.E t (S.forwardSol β s (t + 1)) ω := by
  refine ⟨?_, fun t => ?_⟩
  · filter_upwards [h.2.2.2.2.2.1.1, h.2.1 0] with ω h1 h2
    have e : Bm1 ω = P 0 ω * S.forwardSol β s 0 ω := by
      have e0 : Bm1 ω / P 0 ω = S.forwardSol β s 0 ω := h1
      rw [← e0]
      field_simp
    rw [e]
    refine ⟨⟨fun h0 => (mul_eq_zero.mp h0).resolve_left h2.ne', fun h0 => by rw [h0, mul_zero]⟩,
      ?_⟩
    nlinarith [mul_self_nonneg (S.forwardSol β s 0 ω)]
  · filter_upwards [mDebt_eq_general S hβ0 h t, h.2.2.2.2.2.1.2 t, h.2.1 t, h.2.1 (t + 1),
      mEqm_rate_gt S hβ0 h t] with ω h1 h2 h3 h4 h5
    have e1 : B t ω = (1 + i t ω) * P t ω * (β * S.E t (S.forwardSol β s (t + 1)) ω) := h1
    have e2 : S.forwardSol β s (t + 1) ω = B t ω / P (t + 1) ω := (h2 : _ = _).symm
    have hc : 0 < (1 + i t ω) * P t ω * β / P (t + 1) ω := by
      have : 0 < 1 + i t ω := by linarith
      positivity
    have e3 : S.forwardSol β s (t + 1) ω =
        (1 + i t ω) * P t ω * β / P (t + 1) ω * S.E t (S.forwardSol β s (t + 1)) ω := by
      rw [e2, e1]
      ring
    rw [e3]
    refine ⟨⟨fun h0 => (mul_eq_zero.mp h0).resolve_left hc.ne', fun h0 => by rw [h0, mul_zero]⟩,
      ?_⟩
    nlinarith [mul_self_nonneg (S.E t (S.forwardSol β s (t + 1)) ω)]

/-! ### Signed flow condition, Treasury rule and two-step process -/

/-- Cochrane (2023), eqs. (2.4) and (2.26), pp. 22, 42, on a probability space, **with no
positivity of debt or present values** (integrable surpluses, `β > 0`): in every equilibrium
`B_t/P_{t+1} = s_{t+1} + (B_{t+1}/P_{t+1})/(1 + i_{t+1})` almost surely.
Generalises `TidyR6MeasL1.mFlow_L1`. -/
theorem mFlow_signed (hβ0 : 0 < β) (hsad : StronglyAdapted S.𝓕 s) (hs : SurplusL1 S β s)
    (h : MEquilibrium S β Bm1 s B P i) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, B t ω / P (t + 1) ω =
      s (t + 1) ω + B (t + 1) ω / P (t + 1) ω * (1 + i (t + 1) ω)⁻¹ := by
  filter_upwards [h.2.2.2.2.2.1.2 t, pv_eq_add_pvEx_L1 hsad hs (t + 1),
    mDebt_eq_general S hβ0 h (t + 1), h.2.1 (t + 1), mEqm_rate_gt S hβ0 h (t + 1)]
    with ω h1 h2 h3 h4 h5
  have e1 : B t ω / P (t + 1) ω = S.forwardSol β s (t + 1) ω := h1
  rw [e1, h2, Pi.add_apply, h3]
  have := h4.ne'
  have : 1 + i (t + 1) ω ≠ 0 := by linarith
  field_simp

/-- Cochrane (2023), eq. (2.28), p. 48, **with no positivity**: in every equilibrium
`B_{t+1} = (B_t − P_{t+1} s_{t+1})(1 + i_{t+1})` almost surely (integrable surpluses, `β > 0`).
Generalises `TidyR6MeasL1.mTreasury_rule_L1`. -/
theorem mTreasury_rule_signed (hβ0 : 0 < β) (hsad : StronglyAdapted S.𝓕 s)
    (hs : SurplusL1 S β s) (h : MEquilibrium S β Bm1 s B P i) (t : ℕ) :
    B (t + 1) =ᵐ[S.μ] fun ω => (B t ω - P (t + 1) ω * s (t + 1) ω) * (1 + i (t + 1) ω) := by
  filter_upwards [mFlow_signed S hβ0 hsad hs h t, h.2.1 (t + 1),
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

/-- Cochrane (2023), §2.9, p. 48, with debt of either sign: the two-step process produces the
target price level, `D_t/PV_t = mPegP_t` almost surely, when present values are nonzero almost
surely (integrable surpluses).
Generalises `TidyR6MeasL1.mTwoStep_eq_pegP_L1`. -/
theorem mTwoStep_eq_pegP_signed (hsad : StronglyAdapted S.𝓕 s) (hs : SurplusL1 S β s)
    (hpv : ∀ t, ∀ᵐ ω ∂S.μ, S.forwardSol β s t ω ≠ 0) (t : ℕ) :
    (fun ω => TidyR6MeasFiscal.mTwoStep S β Bm1 s i t ω / S.forwardSol β s t ω) =ᵐ[S.μ]
      mPegP S β Bm1 s i t := by
  induction t with
  | zero => exact Eventually.of_forall fun ω => rfl
  | succ t ih =>
    filter_upwards [ih, pv_eq_add_pvEx_L1 hsad hs t, hpv t] with ω h1 h2 h3
    change (TidyR6MeasFiscal.mTwoStep S β Bm1 s i t ω -
      TidyR6MeasFiscal.mTwoStep S β Bm1 s i t ω / S.forwardSol β s t ω * s t ω) * (1 + i t ω) /
        S.forwardSol β s (t + 1) ω = (1 + i t ω) * mPegP S β Bm1 s i t ω * pvExM S β s t ω /
          S.forwardSol β s (t + 1) ω
    have h1' : TidyR6MeasFiscal.mTwoStep S β Bm1 s i t ω / S.forwardSol β s t ω =
      mPegP S β Bm1 s i t ω := h1
    have h2' : S.forwardSol β s t ω = s t ω + pvExM S β s t ω := by
      rw [h2, Pi.add_apply]
    rw [← h1']
    congr 1
    rw [show pvExM S β s t ω = S.forwardSol β s t ω - s t ω by linarith]
    field_simp

/-- Cochrane (2023), §2.9, p. 48, with debt of either sign: the Treasury's debt in the two-step
process is the target debt almost surely (present values nonzero almost surely).
Generalises `TidyR6MeasL1.mTwoStep_debt_L1`. -/
theorem mTwoStep_debt_signed (hsad : StronglyAdapted S.𝓕 s) (hs : SurplusL1 S β s)
    (hpv : ∀ t, ∀ᵐ ω ∂S.μ, S.forwardSol β s t ω ≠ 0) (t : ℕ) :
    TidyR6MeasFiscal.mTwoStep S β Bm1 s i (t + 1) =ᵐ[S.μ] mPegB S β Bm1 s i t := by
  filter_upwards [mTwoStep_eq_pegP_signed S (Bm1 := Bm1) (i := i) hsad hs hpv (t + 1),
    hpv (t + 1)] with ω h1 h2
  have h1' : TidyR6MeasFiscal.mTwoStep S β Bm1 s i (t + 1) ω / S.forwardSol β s (t + 1) ω =
      (1 + i t ω) * mPegP S β Bm1 s i t ω * pvExM S β s t ω / S.forwardSol β s (t + 1) ω := h1
  exact (div_left_inj' h2).mp h1'

/-- Cochrane (2023), §2.9, p. 48, **debt of either sign**: under the hypotheses of
`TidyR6MeasSigned.mPeg_equilibrium_signed` (with integrable adapted surpluses) the two-step
process is an equilibrium with the target.
Generalises `TidyR6MeasL1.mTwoStep_equilibrium_L1`. -/
theorem mTwoStep_equilibrium_signed (hβ0 : 0 < β) (hsad : StronglyAdapted S.𝓕 s)
    (hs : SurplusL1 S β s) (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1)
    (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω * S.forwardSol β s 0 ω) (hia : StronglyAdapted S.𝓕 i)
    (hi : ∀ t, ∀ᵐ ω ∂S.μ, -1 < i t ω) (hQi : ∀ t, Integrable (fun ω => (1 + i t ω)⁻¹) S.μ)
    (hsign : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s (t + 1) ω *
      S.E t (S.forwardSol β s (t + 1)) ω) :
    MEquilibrium S β Bm1 s (fun t => TidyR6MeasFiscal.mTwoStep S β Bm1 s i (t + 1))
      (fun t ω => TidyR6MeasFiscal.mTwoStep S β Bm1 s i t ω / S.forwardSol β s t ω) i := by
  have hpv : ∀ t, ∀ᵐ ω ∂S.μ, S.forwardSol β s t ω ≠ 0 := fun t => by
    cases t with
    | zero =>
      filter_upwards [hB] with ω h h0
      rw [h0, mul_zero] at h
      exact lt_irrefl _ h
    | succ t =>
      filter_upwards [hsign t] with ω h h0
      rw [h0, zero_mul] at h
      exact lt_irrefl _ h
  exact TidyR5MeasFamily.mEquilibrium_congr S
    (TidyR6MeasSigned.mPeg_equilibrium_signed S hβ0 hBm1 hB hia hi hQi hsign)
    (fun t => ((TidyR6MeasFiscal.mTwoStep_sm S hBm1 hsad hia t).1.measurable.div
      (S.forwardSol_adapted β s t).measurable).stronglyMeasurable)
    (fun t => (TidyR6MeasFiscal.mTwoStep_sm S hBm1 hsad hia t).2)
    (fun t => mTwoStep_eq_pegP_signed S hsad hs hpv t)
    (fun t => mTwoStep_debt_signed S hsad hs hpv t)

/-! ### Existence when present values vanish on part of the space -/

/-- Cochrane (2023), §2.4.3, p. 31: the growth factor of the price level along the target path,
`β E_t PV_{t+1}/PV_{t+1}`, replaced by `β` where `E_t PV_{t+1} = 0`. -/
noncomputable def gFac (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := fun ω =>
  if S.E t (S.forwardSol β s (t + 1)) ω = 0 then β
  else β * S.E t (S.forwardSol β s (t + 1)) ω / S.forwardSol β s (t + 1) ω

/-- Cochrane (2023), §2.4.3, p. 31: the target price level when present values may vanish:
`P_0 = B_{−1}/PV_0` (`1` where `PV_0 = 0`), `P_{t+1} = (1 + i_t) P_t gFac_t`. -/
noncomputable def zP (β : ℝ) (Bm1 : Ω → ℝ) (s i : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun ω => if S.forwardSol β s 0 ω = 0 then 1 else Bm1 ω / S.forwardSol β s 0 ω
  | t + 1 => fun ω => (1 + i t ω) * zP β Bm1 s i t ω * gFac S β s t ω

/-- Cochrane (2023), eq. (2.15), p. 31: the target debt `B_t = (1 + i_t) P_t PVex_t` along `zP`. -/
noncomputable def zB (β : ℝ) (Bm1 : Ω → ℝ) (s i : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (1 + i t ω) * zP S β Bm1 s i t ω * pvExM S β s t ω

/-- Cochrane (2023), §2.4.3, p. 31: the growth factor is known at `t + 1`. -/
theorem gFac_sm (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) :
    StronglyMeasurable[S.𝓕 (t + 1)] (gFac S β s t) := by
  have hE : Measurable[S.𝓕 (t + 1)] (S.E t (S.forwardSol β s (t + 1))) :=
    ((S.stronglyMeasurable_E t _).mono (S.𝓕.mono (Nat.le_succ t))).measurable
  exact (Measurable.ite (measurableSet_eq_fun hE measurable_const) measurable_const
    ((measurable_const.mul hE).div (S.forwardSol_adapted β s (t + 1)).measurable)
    ).stronglyMeasurable

/-- Cochrane (2023), §2.4.3, p. 31: the target price level and debt are adapted. -/
theorem zP_sm (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1) (hia : StronglyAdapted S.𝓕 i) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (zP S β Bm1 s i t) ∧
      StronglyMeasurable[S.𝓕 t] (zB S β Bm1 s i t) := by
  have hP : ∀ t, StronglyMeasurable[S.𝓕 t] (zP S β Bm1 s i t) := by
    intro t
    induction t with
    | zero =>
      exact (Measurable.ite (measurableSet_eq_fun (S.forwardSol_adapted β s 0).measurable
        measurable_const) measurable_const
        (hBm1.measurable.div (S.forwardSol_adapted β s 0).measurable)).stronglyMeasurable
    | succ t ih =>
      have hmono : S.𝓕 t ≤ S.𝓕 (t + 1) := S.𝓕.mono (Nat.le_succ t)
      exact (((((hia t).mono hmono).measurable.const_add 1).mul (ih.mono hmono).measurable).mul
        (gFac_sm S β s t).measurable).stronglyMeasurable
  exact ⟨hP t, ((((hia t).measurable.const_add 1).mul (hP t).measurable).mul
    (pvExM_sm S β s t).measurable).stronglyMeasurable⟩

/-- Cochrane (2023), §§2.4.3–2.4.4, pp. 31–33, on a probability space, **existence when present
values may vanish**: for `β > 0`, `B_{−1}` known at `0`, an adapted target with `i > −1` a.s. and
integrable bond price, and the conditions of `mEqm_zero_conditions`, the path `(zP, zB)` is an
equilibrium.
Generalises `TidyR6MeasSigned.mPeg_equilibrium_signed`. -/
theorem mPeg_equilibrium_zero (hβ0 : 0 < β) (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1)
    (hia : StronglyAdapted S.𝓕 i) (hi : ∀ t, ∀ᵐ ω ∂S.μ, -1 < i t ω)
    (hQi : ∀ t, Integrable (fun ω => (1 + i t ω)⁻¹) S.μ)
    (hC0 : ∀ᵐ ω ∂S.μ, (Bm1 ω = 0 ↔ S.forwardSol β s 0 ω = 0) ∧
      0 ≤ Bm1 ω * S.forwardSol β s 0 ω)
    (hCt : ∀ t, ∀ᵐ ω ∂S.μ, (S.forwardSol β s (t + 1) ω = 0 ↔
      S.E t (S.forwardSol β s (t + 1)) ω = 0) ∧
      0 ≤ S.forwardSol β s (t + 1) ω * S.E t (S.forwardSol β s (t + 1)) ω) :
    MEquilibrium S β Bm1 s (zB S β Bm1 s i) (zP S β Bm1 s i) i := by
  have hg : ∀ t, ∀ᵐ ω ∂S.μ, 0 < gFac S β s t ω := fun t => by
    filter_upwards [hCt t] with ω hcpat
    obtain ⟨h1, h2⟩ := hcpat
    simp only [gFac]
    split_ifs with hE
    · exact hβ0
    · have hP : S.forwardSol β s (t + 1) ω ≠ 0 := fun h0 => hE (h1.mp h0)
      have h3 : 0 < S.E t (S.forwardSol β s (t + 1)) ω * S.forwardSol β s (t + 1) ω :=
        lt_of_le_of_ne (by rw [mul_comm]; exact h2) (mul_ne_zero hE hP).symm
      rw [mul_div_assoc]
      exact mul_pos hβ0 (TidyR6MeasSigned.div_pos_of_mul_pos h3)
  have hPpos : ∀ t, ∀ᵐ ω ∂S.μ, 0 < zP S β Bm1 s i t ω := by
    intro t
    induction t with
    | zero =>
      filter_upwards [hC0] with ω hcpat
      obtain ⟨h1, h2⟩ := hcpat
      change 0 < if S.forwardSol β s 0 ω = 0 then 1 else Bm1 ω / S.forwardSol β s 0 ω
      split_ifs with h0
      · exact one_pos
      · have hB : Bm1 ω ≠ 0 := fun hb => h0 (h1.mp hb)
        exact TidyR6MeasSigned.div_pos_of_mul_pos
          (lt_of_le_of_ne h2 (mul_ne_zero hB h0).symm)
    | succ t ih =>
      filter_upwards [ih, hg t, hi t] with ω h1 h2 h3
      change 0 < (1 + i t ω) * zP S β Bm1 s i t ω * gFac S β s t ω
      have : 0 < 1 + i t ω := by linarith
      positivity
  set E : ℕ → Ω → ℝ := fun t => S.E t (S.forwardSol β s (t + 1)) with hEdef
  set c1 : ℕ → Ω → ℝ := fun t ω => if E t ω = 0 then β⁻¹ else 0 with hc1
  set c2 : ℕ → Ω → ℝ := fun t ω => if E t ω = 0 then 0 else (β * E t ω)⁻¹ with hc2
  set σ : ℕ → Ω → ℝ := fun t ω => if 0 < E t ω then 1 else -1 with hσ
  have hEm : ∀ t, StronglyMeasurable[S.𝓕 t] (E t) := fun t => S.stronglyMeasurable_E t _
  have hc1m : ∀ t, StronglyMeasurable[S.𝓕 t] (c1 t) := fun t =>
    (Measurable.ite (measurableSet_eq_fun (hEm t).measurable measurable_const) measurable_const
      measurable_const).stronglyMeasurable
  have hc2m : ∀ t, StronglyMeasurable[S.𝓕 t] (c2 t) := fun t =>
    (Measurable.ite (measurableSet_eq_fun (hEm t).measurable measurable_const) measurable_const
      (measurable_const.mul (hEm t).measurable).inv).stronglyMeasurable
  have hσm : ∀ t, StronglyMeasurable[S.𝓕 t] (σ t) := fun t =>
    (Measurable.ite (measurableSet_lt measurable_const (hEm t).measurable) measurable_const
      measurable_const).stronglyMeasurable
  have hqm : ∀ t, StronglyMeasurable[S.𝓕 t] (fun ω => (1 + i t ω)⁻¹) := fun t =>
    ((hia t).measurable.const_add 1).inv.stronglyMeasurable
  set w : ℕ → Ω → ℝ := fun t ω => (1 + i t ω)⁻¹ * c2 t ω with hw
  set a : ℕ → Ω → ℝ := fun t ω => (1 + i t ω)⁻¹ * c1 t ω with ha
  have hratio : ∀ t, (fun ω => zP S β Bm1 s i t ω / zP S β Bm1 s i (t + 1) ω) =ᵐ[S.μ]
      a t + w t * S.forwardSol β s (t + 1) := fun t => by
    filter_upwards [hPpos t, hi t, hCt t] with ω h1 h2 hcpat
    obtain ⟨h3, -⟩ := hcpat
    change zP S β Bm1 s i t ω / ((1 + i t ω) * zP S β Bm1 s i t ω * gFac S β s t ω) = _
    have h4 : 1 + i t ω ≠ 0 := by linarith
    have := h1.ne'
    have := hβ0.ne'
    simp only [gFac, Pi.add_apply, Pi.mul_apply, ha, hw, hc1, hc2, hEdef]
    split_ifs with hE
    · field_simp
      ring
    · have hP : S.forwardSol β s (t + 1) ω ≠ 0 := fun h0 => hE (h3.mp h0)
      field_simp
      ring
  have hai : ∀ t, Integrable (a t) S.μ := fun t => by
    have hb : ∀ᵐ ω ∂S.μ, ‖c1 t ω‖ ≤ β⁻¹ := Eventually.of_forall fun ω => by
      simp only [hc1, Real.norm_eq_abs]
      split_ifs
      · rw [abs_of_pos (inv_pos.mpr hβ0)]
      · simp [hβ0.le]
    refine ((hQi t).bdd_mul ((hc1m t).mono (S.𝓕.le t)).aestronglyMeasurable hb).congr
      (Eventually.of_forall fun ω => ?_)
    simp only [ha]
    ring
  have hbi : ∀ t, Integrable (w t * S.forwardSol β s (t + 1)) S.μ := fun t => by
    set X : Ω → ℝ := σ t * S.forwardSol β s (t + 1) with hX
    set Z : Ω → ℝ := fun ω => (1 + i t ω)⁻¹ * (c2 t ω * σ t ω) with hZ
    have hσb : ∀ᵐ ω ∂S.μ, |σ t ω| ≤ 1 := Eventually.of_forall fun ω => by
      simp only [hσ]
      split_ifs <;> norm_num
    have hPVi : Integrable (S.forwardSol β s (t + 1)) S.μ := S.integrable_E _ _
    have hXi : Integrable X S.μ := hPVi.bdd_mul ((hσm t).mono (S.𝓕.le t)).aestronglyMeasurable
      (hσb.mono fun ω h => by rwa [Real.norm_eq_abs])
    have hZm : StronglyMeasurable[S.𝓕 t] Z :=
      ((hqm t).measurable.mul ((hc2m t).measurable.mul (hσm t).measurable)).stronglyMeasurable
    have hZ0 : ∀ᵐ ω ∂S.μ, 0 ≤ Z ω := by
      filter_upwards [hi t] with ω h
      have hq : 0 ≤ (1 + i t ω)⁻¹ := (inv_pos.mpr (by linarith)).le
      refine mul_nonneg hq ?_
      by_cases h1 : E t ω = 0
      · simp [hc2, h1]
      · by_cases h2 : 0 < E t ω
        · simp only [hc2, hσ, h1, h2, ↓reduceIte, mul_one]
          exact (inv_pos.mpr (mul_pos hβ0 h2)).le
        · have hlt : E t ω < 0 := lt_of_le_of_ne (not_lt.mp h2) h1
          simp only [hc2, hσ, h1, h2, ↓reduceIte]
          have : (β * E t ω)⁻¹ < 0 := inv_lt_zero.mpr (mul_neg_of_pos_of_neg hβ0 hlt)
          linarith
    have hX0 : ∀ᵐ ω ∂S.μ, 0 ≤ X ω := by
      filter_upwards [hCt t] with ω hcpat
      obtain ⟨h1, h2⟩ := hcpat
      simp only [hX, Pi.mul_apply, hσ]
      split_ifs with hE
      · rw [one_mul]
        by_contra hn
        push Not at hn
        nlinarith
      · push Not at hE
        rcases hE.lt_or_eq with hlt | heq
        · nlinarith
        · rw [h1.mpr heq, mul_zero]
    have hZE : Integrable (fun ω => Z ω * S.E t X ω) S.μ := by
      have hb : ∀ᵐ ω ∂S.μ, ‖(if E t ω = 0 then (0 : ℝ) else β⁻¹)‖ ≤ β⁻¹ :=
        Eventually.of_forall fun ω => by
          split_ifs
          · simp [hβ0.le]
          · rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hβ0)]
      have hm : AEStronglyMeasurable (fun ω => if E t ω = 0 then (0 : ℝ) else β⁻¹) S.μ :=
        ((Measurable.ite (measurableSet_eq_fun (hEm t).measurable measurable_const)
          measurable_const measurable_const).mono (S.𝓕.le t) le_rfl).aestronglyMeasurable
      refine ((hQi t).bdd_mul hm hb).congr ?_
      filter_upwards [S.E_pullOut (hσm t) hσb hPVi] with ω h
      have h' : S.E t X ω = σ t ω * E t ω := h
      simp only [hZ, h', hc2, hσ]
      by_cases h1 : E t ω = 0
      · simp [h1]
      · simp only [h1, ↓reduceIte]
        have := hβ0.ne'
        split_ifs <;> (field_simp; try ring)
    have hmain := (HouseholdMeasureTVC.integrable_mul_of_E hZm hZ0 hXi hX0 hZE).1
    refine hmain.congr (Eventually.of_forall fun ω => ?_)
    simp only [hZ, hX, Pi.mul_apply, hw, hσ]
    split_ifs <;> ring
  refine ⟨fun t => (zP_sm S hBm1 hia t).1, hPpos, fun t => (zP_sm S hBm1 hia t).2, hia,
    fun t => ((hai t).add (hbi t)).congr (hratio t).symm, ⟨?_, fun t => ?_⟩, fun t => ?_⟩
  · filter_upwards [hC0] with ω hcpat
    obtain ⟨h1, -⟩ := hcpat
    change Bm1 ω / (if S.forwardSol β s 0 ω = 0 then 1 else Bm1 ω / S.forwardSol β s 0 ω) =
      S.forwardSol β s 0 ω
    split_ifs with h0
    · rw [h1.mpr h0, zero_div, h0]
    · rw [div_div_cancel₀ (fun hb => h0 (h1.mp hb))]
  · filter_upwards [hCt t, hPpos t, hi t] with ω hcpat h2 h3
    obtain ⟨h1, -⟩ := hcpat
    change (1 + i t ω) * zP S β Bm1 s i t ω * (β * S.E t (S.forwardSol β s (t + 1)) ω) /
      ((1 + i t ω) * zP S β Bm1 s i t ω * gFac S β s t ω) = S.forwardSol β s (t + 1) ω
    have h4 : 1 + i t ω ≠ 0 := by linarith
    have := h2.ne'
    have := hβ0.ne'
    simp only [gFac]
    split_ifs with hE
    · rw [hE, mul_zero, mul_zero, zero_div, h1.mpr hE]
    · have hP : S.forwardSol β s (t + 1) ω ≠ 0 := fun h0 => hE (h1.mp h0)
      field_simp
  · have hpo := condExp_mul_of_stronglyMeasurable_left
      ((hqm t).measurable.mul (hc2m t).measurable).stronglyMeasurable (hbi t)
      (S.integrable_E (t + 1) (MeasExpectationSystem.discSum β s (t + 1)))
    have hEa : S.E t (a t) = a t :=
      S.E_of_stronglyMeasurable ((hqm t).measurable.mul (hc1m t).measurable).stronglyMeasurable
        (hai t)
    filter_upwards [S.E_congr (hratio t) t, S.E_add (hai t) (hbi t) t, hpo, hi t]
      with ω h1 h2 h3 h4
    rw [Pi.smul_apply, smul_eq_mul, h1, h2, Pi.add_apply, hEa]
    have h3' : S.E t (w t * S.forwardSol β s (t + 1)) ω = w t ω * E t ω := h3
    rw [h3']
    have h5 : 1 + i t ω ≠ 0 := by linarith
    have := hβ0.ne'
    simp only [ha, hw, hc1, hc2]
    split_ifs with hE
    · field_simp
      ring
    · field_simp
      ring

/-- Cochrane (2023), §§2.4.3–2.4.4, pp. 31–33, on a probability space, **the exact condition for
an interest-rate target, present values of any sign and possibly zero**: for `β > 0`, `B_{−1}`
known at `0` and an adapted target, an equilibrium exists iff the bond price is integrable,
`i > −1` a.s., `B_{−1} = 0 ⇔ PV_0 = 0` and `B_{−1} PV_0 ≥ 0` a.s., and at every date
`PV_{t+1} = 0 ⇔ E_t PV_{t+1} = 0` and `PV_{t+1} E_t PV_{t+1} ≥ 0` a.s.
Generalises `TidyR6MeasSigned.mPeg_existsUnique_iff_signed`. -/
theorem mPeg_exists_iff_general (hβ0 : 0 < β) (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1)
    (hia : StronglyAdapted S.𝓕 i) :
    (∃ B P : ℕ → Ω → ℝ, MEquilibrium S β Bm1 s B P i) ↔
      (∀ t, Integrable (fun ω => (1 + i t ω)⁻¹) S.μ) ∧ (∀ t, ∀ᵐ ω ∂S.μ, -1 < i t ω) ∧
        (∀ᵐ ω ∂S.μ, (Bm1 ω = 0 ↔ S.forwardSol β s 0 ω = 0) ∧
          0 ≤ Bm1 ω * S.forwardSol β s 0 ω) ∧
        ∀ t, ∀ᵐ ω ∂S.μ, (S.forwardSol β s (t + 1) ω = 0 ↔
          S.E t (S.forwardSol β s (t + 1)) ω = 0) ∧
          0 ≤ S.forwardSol β s (t + 1) ω * S.E t (S.forwardSol β s (t + 1)) ω := by
  constructor
  · rintro ⟨B, P, h⟩
    obtain ⟨h0, ht⟩ := mEqm_zero_conditions S hβ0 h
    exact ⟨TidyR6MeasHyp.mEqm_bondPrice_integrable S h, mEqm_rate_gt S hβ0 h, h0, ht⟩
  · rintro ⟨hQi, hi, hC0, hCt⟩
    exact ⟨_, _, mPeg_equilibrium_zero S hβ0 hBm1 hia hi hQi hC0 hCt⟩

/-! ### Non-uniqueness, and when it fails -/

/-- Cochrane (2023), p. 33: the scale factor `2` on the event `{PV_0 = 0}`, `1` elsewhere. -/
noncomputable def lam0 (β : ℝ) (s : ℕ → Ω → ℝ) : Ω → ℝ :=
  fun ω => if S.forwardSol β s 0 ω = 0 then 2 else 1

/-- Cochrane (2023), pp. 22, 33, on a probability space, **the price level is free where `PV_0`
vanishes**: if `{PV_0 = 0}` has positive probability, scaling an equilibrium's price level and
debt by `2` on that event (at every date) gives another equilibrium, whose initial price level
differs with positive probability (`β > 0`).
Generalises `TidyR6MeasSigned.zero_pv_not_unique`. -/
theorem nonunique_date0 (hβ0 : 0 < β) (h : MEquilibrium S β Bm1 s B P i)
    (hZ : ¬ ∀ᵐ ω ∂S.μ, S.forwardSol β s 0 ω ≠ 0) :
    MEquilibrium S β Bm1 s (fun t ω => lam0 S β s ω * B t ω) (fun t ω => lam0 S β s ω * P t ω)
        i ∧ ¬ (fun ω => lam0 S β s ω * P 0 ω) =ᵐ[S.μ] P 0 := by
  have hlm : StronglyMeasurable[S.𝓕 0] (lam0 S β s) :=
    (Measurable.ite (measurableSet_eq_fun (S.forwardSol_adapted β s 0).measurable
      measurable_const) measurable_const measurable_const).stronglyMeasurable
  have hlpos : ∀ ω, 0 < lam0 S β s ω := fun ω => by
    simp only [lam0]
    split_ifs <;> norm_num
  have hr : ∀ t, (fun ω => lam0 S β s ω * P t ω / (lam0 S β s ω * P (t + 1) ω)) =
      fun ω => P t ω / P (t + 1) ω := fun t => funext fun ω =>
    mul_div_mul_left _ _ (hlpos ω).ne'
  obtain ⟨hPa, hP, hBa, hia, hint, ⟨hv0, hv⟩, hbp⟩ := h
  have hC0 := (mEqm_zero_conditions S hβ0 ⟨hPa, hP, hBa, hia, hint, ⟨hv0, hv⟩, hbp⟩).1
  have hint' : ∀ t, Integrable
      (fun ω => lam0 S β s ω * P t ω / (lam0 S β s ω * P (t + 1) ω)) S.μ := fun t => by
    rw [hr]
    exact hint t
  refine ⟨⟨fun t => (hlm.mono (S.𝓕.mono (Nat.zero_le t))).mul (hPa t),
    fun t => (hP t).mono fun ω h => mul_pos (hlpos ω) h,
    fun t => (hlm.mono (S.𝓕.mono (Nat.zero_le t))).mul (hBa t), hia,
    hint', ⟨?_, fun t => ?_⟩, fun t => ?_⟩, ?_⟩
  · filter_upwards [hv0, hC0] with ω h1 hcpat
    obtain ⟨h2, -⟩ := hcpat
    by_cases h0 : S.forwardSol β s 0 ω = 0
    · rw [h2.mpr h0, zero_div, h0]
    · have h1' : Bm1 ω / P 0 ω = S.forwardSol β s 0 ω := h1
      simp only [lam0, h0, ↓reduceIte, one_mul]
      exact h1'
  · filter_upwards [hv t] with ω h1
    rw [mul_div_mul_left _ _ (hlpos ω).ne']
    exact h1
  · change (fun ω => (1 + i t ω)⁻¹) =ᵐ[S.μ]
      β • S.E t (fun ω => lam0 S β s ω * P t ω / (lam0 S β s ω * P (t + 1) ω))
    rw [hr]
    exact hbp t
  · intro he
    apply hZ
    filter_upwards [he, hP 0] with ω h1 h2 h0
    simp only [lam0, h0, ↓reduceIte] at h1
    linarith

/-- Cochrane (2023), eq. (2.3), p. 22, on a probability space, **when the price level is pinned**:
in every equilibrium with `β > 0`, if `P_t/P_{t+1}` is known at `t` (no news at `t + 1`), the bond
price pins `P_{t+1} = β(1 + i_t) P_t` almost surely, wherever debt or present values vanish.
Generalises `TidyR6MeasRestate.mPrice_succ_no_news`. -/
theorem pinned_of_known (hβ0 : 0 < β) (h : MEquilibrium S β Bm1 s B P i) (t : ℕ)
    (hk : StronglyMeasurable[S.𝓕 t] (fun ω => P t ω / P (t + 1) ω)) :
    P (t + 1) =ᵐ[S.μ] fun ω => β * (1 + i t ω) * P t ω := by
  have hE := S.E_of_stronglyMeasurable hk (h.2.2.2.2.1 t)
  filter_upwards [h.2.2.2.2.2.2 t, h.2.1 t, h.2.1 (t + 1), mEqm_rate_gt S hβ0 h t]
    with ω h1 h2 h3 h4
  have h1' : (1 + i t ω)⁻¹ = β * (P t ω / P (t + 1) ω) := by
    rw [h1, Pi.smul_apply, smul_eq_mul, hE]
  have h5 : 1 + i t ω ≠ 0 := by linarith
  have := h2.ne'
  have := h3.ne'
  have := hβ0.ne'
  field_simp at h1'
  linarith

/-- Cochrane (2023), p. 33: the perturbed ratio `P_t/P'_{t+1}`: unchanged where `B_t ≠ 0`, and
`E_t(P_t/P_{t+1})(1 + δξ)` where `B_t = 0`. -/
noncomputable def pertR (P B : ℕ → Ω → ℝ) (t : ℕ) (ξ : Ω → ℝ) (δ : ℝ) : Ω → ℝ :=
  fun ω => P t ω / P (t + 1) ω + (if B t ω = 0 then 1 else 0) *
    (S.E t (fun ω => P t ω / P (t + 1) ω) ω * (1 + δ * ξ ω) - P t ω / P (t + 1) ω)

/-- Cochrane (2023), p. 33: the factor `Y = (P_t/P_{t+1})/pertR` by which the price level and
debt are moved from date `t + 1` on. -/
noncomputable def pertY (P B : ℕ → Ω → ℝ) (t : ℕ) (ξ : Ω → ℝ) (δ : ℝ) : Ω → ℝ :=
  fun ω => P t ω / P (t + 1) ω / pertR S P B t ξ δ ω

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 33: a process left unchanged up to `t` and multiplied by `Y` from
`t + 1` on. -/
def pertP (X : ℕ → Ω → ℝ) (Y : Ω → ℝ) (t : ℕ) : ℕ → Ω → ℝ :=
  fun s ω => if s ≤ t then X s ω else Y ω * X s ω

/-- Cochrane (2023), pp. 22, 33, on a probability space: in every equilibrium, for a
date-`t + 1` news variable `ξ` (`|ξ| ≤ 1`, `E_t ξ = 0` a.s.) and `|δ| ≤ 1/2`, moving the price
level and debt from `t + 1` on by `pertY` gives another equilibrium (any `β`): where `B_t = 0`
the price level `P_{t+1}` is free up to the bond-pricing condition. -/
theorem pert_equilibrium (h : MEquilibrium S β Bm1 s B P i) {t : ℕ} {ξ : Ω → ℝ}
    (hξm : StronglyMeasurable[S.𝓕 (t + 1)] ξ) (hξb : ∀ ω, |ξ ω| ≤ 1)
    (hξ0 : S.E t ξ =ᵐ[S.μ] 0) {δ : ℝ} (hδ : |δ| ≤ 1 / 2) :
    MEquilibrium S β Bm1 s (pertP B (pertY S P B t ξ δ) t) (pertP P (pertY S P B t ξ δ) t) i := by
  have hsign := TidyR6MeasSigned.mEqm_sign S h t
  obtain ⟨hPa, hP, hBa, hia, hint, ⟨hv0, hv⟩, hbp⟩ := h
  set R : Ω → ℝ := fun ω => P t ω / P (t + 1) ω with hR
  set ER : Ω → ℝ := S.E t R with hER
  set ind : Ω → ℝ := fun ω => if B t ω = 0 then 1 else 0 with hind
  set Y := pertY S P B t ξ δ with hY
  have hmono : S.𝓕 t ≤ S.𝓕 (t + 1) := S.𝓕.mono (Nat.le_succ t)
  have hRm : StronglyMeasurable[S.𝓕 (t + 1)] R :=
    (((hPa t).mono hmono).measurable.div (hPa (t + 1)).measurable).stronglyMeasurable
  have hERm : StronglyMeasurable[S.𝓕 t] ER := S.stronglyMeasurable_E t R
  have hindm : StronglyMeasurable[S.𝓕 t] ind :=
    (Measurable.ite (measurableSet_eq_fun (hBa t).measurable measurable_const)
      measurable_const measurable_const).stronglyMeasurable
  have hindb : ∀ᵐ ω ∂S.μ, |ind ω| ≤ 1 := Eventually.of_forall fun ω => by
    simp only [hind]
    split_ifs <;> norm_num
  have hRpos : ∀ᵐ ω ∂S.μ, 0 < R ω := by
    filter_upwards [hP t, hP (t + 1)] with ω h1 h2
    exact div_pos h1 h2
  have hERpos := HouseholdMeasure.E_pos (hint t) hRpos t
  have hδξ : ∀ ω, 1 / 2 ≤ 1 + δ * ξ ω := fun ω => by
    have : |δ * ξ ω| ≤ 1 / 2 := by
      rw [abs_mul]
      nlinarith [hξb ω, abs_nonneg δ, abs_nonneg (ξ ω)]
    linarith [neg_abs_le (δ * ξ ω)]
  have hR'pos : ∀ᵐ ω ∂S.μ, 0 < pertR S P B t ξ δ ω := by
    filter_upwards [hRpos, hERpos] with ω h1 h2
    simp only [pertR]
    split_ifs
    · have := hδξ ω
      nlinarith
    · simpa using h1
  have hYpos : ∀ᵐ ω ∂S.μ, 0 < Y ω := by
    filter_upwards [hRpos, hR'pos] with ω h1 h2
    exact div_pos h1 h2
  have hYm : StronglyMeasurable[S.𝓕 (t + 1)] Y :=
    (hRm.measurable.div ((hRm.measurable).add ((hindm.mono hmono).measurable.mul
      (((hERm.mono hmono).measurable.mul (measurable_const.add
        (measurable_const.mul hξm.measurable))).sub hRm.measurable)))).stronglyMeasurable
  have hξi : Integrable ξ S.μ := Integrable.of_bound ((hξm.mono (S.𝓕.le _)).aestronglyMeasurable)
    1 (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hξb ω)
  have h1δi : Integrable (fun ω => 1 + δ * ξ ω) S.μ := (integrable_const 1).add (hξi.const_mul δ)
  have hERi : Integrable ER S.μ := S.integrable_E t R
  have hEξi : Integrable (fun ω => ER ω * (1 + δ * ξ ω)) S.μ := by
    have hb : ∀ᵐ ω ∂S.μ, ‖1 + δ * ξ ω‖ ≤ 1 + |δ| := Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans ?_
      rw [abs_one, abs_mul]
      nlinarith [hξb ω, abs_nonneg δ]
    exact (hERi.bdd_mul h1δi.aestronglyMeasurable hb).congr
      (Eventually.of_forall fun ω => mul_comm _ _)
  set D : Ω → ℝ := fun ω => ind ω * (ER ω * (1 + δ * ξ ω) - R ω) with hD
  have hDi : Integrable D S.μ := (hEξi.sub (hint t)).bdd_mul
    ((hindm.mono (S.𝓕.le t)).aestronglyMeasurable) (hindb.mono fun ω h => by
      rwa [Real.norm_eq_abs])
  have hR'eq : pertR S P B t ξ δ = R + D := rfl
  have hR'i : Integrable (pertR S P B t ξ δ) S.μ := by rw [hR'eq]; exact (hint t).add hDi
  have hED : S.E t D =ᵐ[S.μ] 0 := by
    have h1 := S.E_pullOut hindm hindb (hEξi.sub (hint t))
    have h2 := S.E_sub hEξi (hint t) t
    have h3 := condExp_mul_of_stronglyMeasurable_left hERm hEξi h1δi
    have h4 := S.E_add (integrable_const 1) (hξi.const_mul δ) t
    have h5 := S.E_smul δ ξ t
    filter_upwards [h1, h2, h3, h4, h5, hξ0] with ω e1 e2 e3 e4 e5 e6
    have e1' : S.E t D ω = ind ω * S.E t (fun ω => ER ω * (1 + δ * ξ ω) - R ω) ω := e1
    have e2' : S.E t (fun ω => ER ω * (1 + δ * ξ ω) - R ω) ω =
        S.E t (fun ω => ER ω * (1 + δ * ξ ω)) ω - ER ω := e2
    have e3' : S.E t (fun ω => ER ω * (1 + δ * ξ ω)) ω =
        ER ω * S.E t (fun ω => 1 + δ * ξ ω) ω := e3
    have e4' : S.E t (fun ω => 1 + δ * ξ ω) ω = 1 + S.E t (fun ω => δ * ξ ω) ω := by
      have := e4
      simp only [Pi.add_apply, S.E_const] at this
      exact this
    have e5' : S.E t (fun ω => δ * ξ ω) ω = δ * S.E t ξ ω := e5
    rw [e1', e2', e3', e4', e5', e6]
    simp
  have hEeq : S.E t (pertR S P B t ξ δ) =ᵐ[S.μ] S.E t R := by
    rw [hR'eq]
    filter_upwards [S.E_add (hint t) hDi t, hED] with ω e1 e2
    rw [e1, Pi.add_apply, e2, Pi.zero_apply, add_zero]
  have hrat : ∀ u, (fun ω => pertP P Y t u ω / pertP P Y t (u + 1) ω) =ᵐ[S.μ]
      if u = t then pertR S P B t ξ δ else fun ω => P u ω / P (u + 1) ω := fun u => by
    rcases lt_trichotomy u t with hlt | heq | hgt
    · refine Eventually.of_forall fun ω => ?_
      simp only [pertP, hlt.le, show u + 1 ≤ t by omega, hlt.ne, ↓reduceIte]
    · subst heq
      filter_upwards [hRpos, hR'pos, hP u, hP (u + 1)] with ω h1 h2 h3 h4
      simp only [pertP, le_refl, show ¬ u + 1 ≤ u by omega, ↓reduceIte, hY, pertY]
      have := h1.ne'
      have := h2.ne'
      have := h3.ne'
      have := h4.ne'
      simp only [hR] at h1 ⊢
      field_simp
    · filter_upwards [hYpos] with ω h1
      simp only [pertP, show ¬ u ≤ t by omega, show ¬ u + 1 ≤ t by omega, hgt.ne', ↓reduceIte]
      exact mul_div_mul_left _ _ h1.ne'
  refine ⟨fun u => ?_, fun u => ?_, fun u => ?_, hia, fun u => ?_, ⟨?_, fun u => ?_⟩,
    fun u => ?_⟩
  · by_cases hu : u ≤ t
    · have e : pertP P Y t u = P u := funext fun ω => by simp only [pertP, hu, ↓reduceIte]
      rw [e]
      exact hPa u
    · have e : pertP P Y t u = Y * P u := funext fun ω => by simp only [pertP, hu, ↓reduceIte]; rfl
      rw [e]
      exact (hYm.mono (S.𝓕.mono (by omega))).mul (hPa u)
  · filter_upwards [hP u, hYpos] with ω h1 h2
    simp only [pertP]
    split_ifs
    · exact h1
    · exact mul_pos h2 h1
  · by_cases hu : u ≤ t
    · have e : pertP B Y t u = B u := funext fun ω => by simp only [pertP, hu, ↓reduceIte]
      rw [e]
      exact hBa u
    · have e : pertP B Y t u = Y * B u := funext fun ω => by simp only [pertP, hu, ↓reduceIte]; rfl
      rw [e]
      exact (hYm.mono (S.𝓕.mono (by omega))).mul (hBa u)
  · refine Integrable.congr ?_ (hrat u).symm
    split_ifs
    · exact hR'i
    · exact hint u
  · have e : pertP P Y t 0 = P 0 := funext fun ω => by simp only [pertP, Nat.zero_le, ↓reduceIte]
    change (fun ω => Bm1 ω / pertP P Y t 0 ω) =ᵐ[S.μ] _
    rw [e]
    exact hv0
  · rcases lt_trichotomy u t with hlt | heq | hgt
    · filter_upwards [hv u] with ω h1
      simp only [pertP, hlt.le, show u + 1 ≤ t by omega, ↓reduceIte]
      exact h1
    · subst heq
      filter_upwards [hv u, hsign, hRpos, hP (u + 1)] with ω h1 h2 h3 h4
      simp only [pertP, le_refl, show ¬ u + 1 ≤ u by omega, ↓reduceIte]
      by_cases hB : B u ω = 0
      · rw [hB, zero_div]
        exact (h2.1.mp hB).symm
      · have hY1 : Y ω = 1 := by
          simp only [hY, pertY, pertR, hB, ↓reduceIte, zero_mul, add_zero]
          exact div_self h3.ne'
        rw [hY1, one_mul]
        exact h1
    · filter_upwards [hv u, hYpos] with ω h1 h2
      simp only [pertP, show ¬ u ≤ t by omega, show ¬ u + 1 ≤ t by omega, ↓reduceIte]
      rw [mul_div_mul_left _ _ h2.ne']
      exact h1
  · have hc := S.E_congr (hrat u) u
    split_ifs at hc with hu
    · subst hu
      filter_upwards [hbp u, hc, hEeq] with ω e1 e2 e3
      rw [Pi.smul_apply, smul_eq_mul, e2, e3]
      exact e1
    · filter_upwards [hbp u, hc] with ω e1 e2
      rw [Pi.smul_apply, smul_eq_mul, e2]
      exact e1

/-- Cochrane (2023), pp. 22, 33, on a probability space, **non-uniqueness where the zero event
receives news**: in every equilibrium, if there is a date-`t + 1` variable `ξ` with
`|ξ| ≤ 1` and `E_t ξ = 0` a.s. that is nonzero with positive probability on `{B_t = 0}` (which is
`{PV_{t+1} = 0}`, `TidyR6MeasSigned.mEqm_sign`), there is another equilibrium whose price level
at `t + 1` differs with positive probability. -/
theorem nonunique_news (h : MEquilibrium S β Bm1 s B P i) {t : ℕ} {ξ : Ω → ℝ}
    (hξm : StronglyMeasurable[S.𝓕 (t + 1)] ξ) (hξb : ∀ ω, |ξ ω| ≤ 1)
    (hξ0 : S.E t ξ =ᵐ[S.μ] 0) (hnews : ¬ ∀ᵐ ω ∂S.μ, B t ω = 0 → ξ ω = 0) :
    ∃ B' P' : ℕ → Ω → ℝ, MEquilibrium S β Bm1 s B' P' i ∧ ¬ P' (t + 1) =ᵐ[S.μ] P (t + 1) := by
  by_contra hc
  push Not at hc
  have hδ1 : |(1 / 2 : ℝ)| ≤ 1 / 2 := by norm_num
  have hδ2 : |(-1 / 2 : ℝ)| ≤ 1 / 2 := by norm_num
  have e1 := hc _ _ (pert_equilibrium S h hξm hξb hξ0 hδ1)
  have e2 := hc _ _ (pert_equilibrium S h hξm hξb hξ0 hδ2)
  apply hnews
  have hERpos := HouseholdMeasure.E_pos (h.2.2.2.2.1 t)
    (by filter_upwards [h.2.1 t, h.2.1 (t + 1)] with ω h1 h2; exact div_pos h1 h2) t
  filter_upwards [e1, e2, h.2.1 t, h.2.1 (t + 1), hERpos] with ω a1 a2 hp1 hp2 hE hB
  simp only [pertP, show ¬ t + 1 ≤ t by omega, ↓reduceIte] at a1 a2
  have hY : ∀ δ : ℝ, pertY S P B t ξ δ ω * P (t + 1) ω = P (t + 1) ω →
      P t ω / P (t + 1) ω = S.E t (fun ω => P t ω / P (t + 1) ω) ω * (1 + δ * ξ ω) := by
    intro δ hd
    have hy : pertY S P B t ξ δ ω = 1 := by
      have := hp2.ne'
      field_simp at hd ⊢
      linarith [hd]
    simp only [pertY, pertR, hB, ↓reduceIte, one_mul, add_sub_cancel] at hy
    have hq := div_pos hp1 hp2
    by_contra hne
    have hden : S.E t (fun ω => P t ω / P (t + 1) ω) ω * (1 + δ * ξ ω) ≠ 0 := by
      intro h0
      rw [h0, div_zero] at hy
      exact zero_ne_one hy
    exact hne ((div_eq_one_iff_eq hden).mp hy)
  have f1 := hY (1 / 2) a1
  have f2 := hY (-1 / 2) a2
  have : S.E t (fun ω => P t ω / P (t + 1) ω) ω * ξ ω = 0 := by linarith
  exact (mul_eq_zero.mp this).resolve_left hE.ne'

/-! ### Positive probability alone does not give non-uniqueness at later dates -/

namespace TwoState

/-- Cochrane (2023), §2.1, p. 21: two equally likely states. -/
noncomputable def twoMeasure : Measure Bool :=
  (2⁻¹ : ENNReal) • (Measure.dirac true + Measure.dirac false)

/-- Cochrane (2023), §2.1, p. 21: the two-state measure has total mass one. -/
theorem twoMeasure_univ : twoMeasure Set.univ = 1 := by
  simp only [twoMeasure, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- Cochrane (2023), §2.1, p. 21: the two-state economy with full information at every date. -/
noncomputable def twoSystem : MeasExpectationSystem Bool :=
  ⟨⟨twoMeasure, ⟨twoMeasure_univ⟩⟩, ⟨fun _ => inferInstance, fun _ _ _ => le_rfl, fun _ => le_rfl⟩⟩

/-- Cochrane (2023), §2.1, p. 21: almost surely means in both states. -/
theorem ae_two {p : Bool → Prop} : (∀ᵐ ω ∂twoSystem.μ, p ω) ↔ p true ∧ p false := by
  change (∀ᵐ ω ∂twoMeasure, p ω) ↔ _
  rw [ae_iff]
  simp only [twoMeasure, Measure.smul_apply, Measure.add_apply,
    Measure.dirac_apply' _ (MeasurableSet.of_discrete), smul_eq_mul]
  by_cases h1 : p true <;> by_cases h2 : p false <;> simp [Set.indicator, h1, h2]

/-- Cochrane (2023), §2.1, p. 21: every function on the two states is measurable. -/
theorem measurable_bool (f : Bool → ℝ) : Measurable f := fun _ _ => MeasurableSet.of_discrete

/-- Cochrane (2023), §2.1, p. 21: every function on the two states is integrable. -/
theorem integrable_bool (x : Bool → ℝ) : Integrable x twoSystem.μ :=
  Integrable.of_bound (measurable_bool x).aestronglyMeasurable (|x true| + |x false|)
    (Eventually.of_forall fun ω => by cases ω <;> simp)

/-- Cochrane (2023), §2.1, p. 21: with full information `E_t x = x`. -/
theorem twoE (t : ℕ) (x : Bool → ℝ) : twoSystem.E t x = x :=
  twoSystem.E_of_stronglyMeasurable (measurable_bool x).stronglyMeasurable (integrable_bool x)

/-- Cochrane (2023), eq. (2.7), p. 22: surpluses `1/2` forever in state `true`; `1` at date `0`
and nothing afterwards in state `false`. -/
noncomputable def sZ : ℕ → Bool → ℝ := fun t ω => if ω then 1 / 2 else if t = 0 then 1 else 0

/-- Cochrane (2023), eq. (2.7), p. 22: at `β = 1/2` the present values are `1` in state `true`,
`1` at date `0` and `0` afterwards in state `false`. -/
theorem pvZ (t : ℕ) : twoSystem.forwardSol (1 / 2) sZ t =
    fun ω => if ω then 1 else if t = 0 then 1 else 0 := by
  change twoSystem.E t _ = _
  rw [twoE]
  funext ω
  simp only [MeasExpectationSystem.discSum]
  cases ω
  · have e : (fun k : ℕ => (1 / 2 : ℝ) ^ k * sZ (t + k) false) =
        fun k => if k = 0 then (if t = 0 then (1 : ℝ) else 0) else 0 := by
      funext k
      cases k with
      | zero => simp [sZ]
      | succ k => simp [sZ]
    rw [e, tsum_ite_eq]
    simp
  · simp only [sZ, ↓reduceIte]
    rw [tsum_mul_right, tsum_geometric_two]
    norm_num

/-- Cochrane (2023), pp. 22, 33, **the precise statement at later dates**: in the two-state
economy with full information, `β = 1/2`, `B_{−1} = 1` and the target `i ≡ 1`, the event
`{PV_1 = 0}` (state `false`) has probability `1/2` (positive, not full), an equilibrium exists,
and every equilibrium has `P_t = 1` almost surely at every date: where the zero event receives no
news the price level is pinned by the bond price (`pinned_of_known`). -/
theorem unique_with_zero_pv :
    (¬ ∀ᵐ ω ∂twoSystem.μ, twoSystem.forwardSol (1 / 2) sZ 1 ω ≠ 0) ∧
      (¬ ∀ᵐ ω ∂twoSystem.μ, twoSystem.forwardSol (1 / 2) sZ 1 ω = 0) ∧
      MEquilibrium twoSystem (1 / 2) (fun _ => 1) sZ (fun _ ω => if ω then 1 else 0)
        (fun _ _ => 1) (fun _ _ => 1) ∧
      ∀ B P : ℕ → Bool → ℝ, MEquilibrium twoSystem (1 / 2) (fun _ => 1) sZ B P (fun _ _ => 1) →
        ∀ t, P t =ᵐ[twoSystem.μ] fun _ => 1 := by
  refine ⟨fun h => ?_, fun h => ?_, ?_, fun B P h t => ?_⟩
  · have := (ae_two.mp h).2
    rw [pvZ] at this
    simp at this
  · have := (ae_two.mp h).1
    rw [pvZ] at this
    simp at this
  · refine ⟨fun _ => stronglyMeasurable_const, fun _ => Eventually.of_forall fun _ => one_pos,
      fun _ => (measurable_bool _).stronglyMeasurable, fun _ => stronglyMeasurable_const,
      fun _ => integrable_bool _, ⟨?_, fun t => ?_⟩, fun t => ?_⟩
    · rw [pvZ]
      refine Eventually.of_forall fun ω => ?_
      cases ω <;> simp
    · rw [pvZ]
      refine Eventually.of_forall fun ω => ?_
      cases ω <;> simp
    · rw [twoE]
      refine Eventually.of_forall fun ω => ?_
      norm_num
  · induction t with
    | zero =>
      filter_upwards [h.2.2.2.2.2.1.1, h.2.1 0] with ω h1 h2
      rw [pvZ] at h1
      have h1' : 1 / P 0 ω = if ω then 1 else 1 := by simpa using h1
      have e : (if ω then (1 : ℝ) else 1) = 1 := by cases ω <;> rfl
      rw [e, div_eq_one_iff_eq h2.ne'] at h1'
      exact h1'.symm
    | succ t ih =>
      filter_upwards [pinned_of_known twoSystem (by norm_num) h t
        (measurable_bool _).stronglyMeasurable, ih] with ω h1 h2
      rw [h1, h2]
      norm_num

end TwoState

end Cochrane.IntertemporalModel.TidyR6MeasZero
