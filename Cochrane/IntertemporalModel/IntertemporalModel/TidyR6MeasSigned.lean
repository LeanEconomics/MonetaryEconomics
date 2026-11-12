/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.TidyR6MeasL1

/-!
# Interest-rate targets with debt of either sign, and adapted debt on a complete filtration

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.1, pp. 21–23 ((2.3), (2.7))
and §2.4, pp. 29–33 (interest-rate targets), on a probability space (`MeasExpectationSystem`).

`TidyR6MeasHyp.mPeg_existsUnique_iff` characterised target equilibria with positive debt. Here
debt and present values may have either sign (the government may be a net creditor).

* Necessary facts in every equilibrium: `mEqm_sign` (`B_t` and `PV_{t+1}` have the same sign, and
  `B_t = 0` exactly where `PV_{t+1} = 0`), `mDebt_eq_signed` (`B_t = (1 + i_t) P_t PVex_t` where
  debt is nonzero), `mEqm_sign_condition` (`PV_{t+1}` and its forecast `E_t PV_{t+1}` have the
  same sign: the sign of the present value must be known one period ahead).
* `mPeg_existsUnique_iff_signed` (headline): with present values nonzero almost surely, an
  equilibrium exists iff the bond price is integrable, `i > −1` a.s., `B_{−1} PV_0 > 0` a.s. and
  `PV_{t+1} E_t PV_{t+1} > 0` a.s. at every date; it is then unique almost surely
  (`mPeg_equilibrium_signed`, `mPeg_unique_signed`). Negative debt with negative present values
  is an equilibrium exactly like positive debt.
* Where present values vanish identically the price level is not determined:
  `zero_pv_not_unique` (no surpluses, no debt: every constant price level is an equilibrium).
  On a zero event of smaller measure this holds at date 0 but at later dates only where that
  event receives news (`TidyR6MeasZero.nonunique_date0`, `TidyR6MeasZero.nonunique_news`,
  `TidyR6MeasZero.TwoState.unique_with_zero_pv`).
* Adapted debt: `debt_adapted_of_complete` derives adaptedness of `B` non-circularly from
  `B_{−1}` known at `0` (a primitive), the flow condition and a complete filtration;
  `mEquilibrium_iff_mIsEqm_complete_L1` is then the equivalence with no adaptedness hypothesis at
  all; `PointMass.debt_adapted_needed` shows the completeness cannot be dropped.
-/

namespace Cochrane.IntertemporalModel.TidyR6MeasSigned

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure TidyR5Meas
  TidyR6MeasL1

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)
variable {β : ℝ} {Bm1 : Ω → ℝ} {s B P i : ℕ → Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), eq. (2.7), p. 22 (tool): `a b > 0` gives `a/b > 0`. -/
theorem div_pos_of_mul_pos {a b : ℝ} (h : 0 < a * b) : 0 < a / b := by
  have hb : b ≠ 0 := by
    rintro rfl
    simp at h
  rw [show a / b = a * b / (b * b) by field_simp]
  exact div_pos h (mul_self_pos.mpr hb)

/-! ### Necessary facts in every equilibrium -/

/-- Cochrane (2023), eq. (2.12), p. 30, on a probability space: in every equilibrium, almost
surely, `B_t = 0` iff `PV_{t+1} = 0`, and `B_t PV_{t+1} ≥ 0`.
Generalises `TidyR6MeasHyp.mEqm_pv_succ_pos_iff`. -/
theorem mEqm_sign (h : MEquilibrium S β Bm1 s B P i) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, (B t ω = 0 ↔ S.forwardSol β s (t + 1) ω = 0) ∧
      0 ≤ B t ω * S.forwardSol β s (t + 1) ω := by
  filter_upwards [h.2.2.2.2.2.1.2 t, h.2.1 (t + 1)] with ω h1 h2
  have e : S.forwardSol β s (t + 1) ω = B t ω / P (t + 1) ω := h1.symm
  rw [e]
  refine ⟨⟨fun h0 => by rw [h0, zero_div], fun h0 => ?_⟩, ?_⟩
  · exact (div_eq_zero_iff.mp h0).resolve_right h2.ne'
  · rw [mul_div_assoc', div_nonneg_iff]
    exact Or.inl ⟨mul_self_nonneg _, h2.le⟩

/-- Cochrane (2023), eq. (2.15), p. 31, on a probability space, **debt of either sign**: in every
equilibrium with `β > 0` and nonzero debt at `t` almost surely, `B_t = (1 + i_t) P_t PVex_t`
almost surely.
Generalises `TidyR5Meas.mDebt_eq`. -/
theorem mDebt_eq_signed (hβ0 : 0 < β) (h : MEquilibrium S β Bm1 s B P i) (t : ℕ)
    (hB0 : ∀ᵐ ω ∂S.μ, B t ω ≠ 0) :
    B t =ᵐ[S.μ] fun ω => (1 + i t ω) * P t ω * pvExM S β s t ω := by
  have hrate := mEqm_rate_gt S hβ0 h t
  obtain ⟨hPa, hP, hBa, -, hint, ⟨-, hv⟩, hbp⟩ := h
  set f : Ω → ℝ := fun ω => P t ω / B t ω with hf
  set g : Ω → ℝ := S.forwardSol β s (t + 1) with hg
  have hfm : StronglyMeasurable[S.𝓕 t] f :=
    ((hPa t).measurable.div (hBa t).measurable).stronglyMeasurable
  have hfg : (fun ω => P t ω / P (t + 1) ω) =ᵐ[S.μ] f * g := by
    filter_upwards [hv t, hP (t + 1), hB0] with ω h1 h2 h3
    have e1 : B t ω / P (t + 1) ω = S.forwardSol β s (t + 1) ω := h1
    simp only [hf, hg, Pi.mul_apply]
    rw [← e1]
    have := h2.ne'
    field_simp
  have hgi : Integrable g S.μ := S.integrable_E _ _
  have hpo := condExp_mul_of_stronglyMeasurable_left hfm ((hint t).congr hfg) hgi
  filter_upwards [hbp t, S.E_congr hfg t, hpo, hB0, hrate] with ω h1 h2 h3 h4 h5
  have e : (1 + i t ω)⁻¹ = f ω * pvExM S β s t ω := by
    rw [h1, Pi.smul_apply, smul_eq_mul, h2]
    have h3' : S.E t (f * g) ω = f ω * S.E t g ω := h3
    rw [h3']
    simp only [pvExM, Pi.smul_apply, smul_eq_mul, hg]
    ring
  have hne : 1 + i t ω ≠ 0 := by linarith
  simp only [hf] at e
  field_simp at e
  linear_combination e

/-- Cochrane (2023), eq. (2.3), p. 22, on a probability space, **the sign must be known a period
ahead**: in every equilibrium with `β > 0` and nonzero debt at `t` almost surely, the present
value `PV_{t+1}` and its forecast `E_t PV_{t+1}` have the same sign almost surely,
`PV_{t+1} E_t PV_{t+1} > 0`. -/
theorem mEqm_sign_condition (hβ0 : 0 < β) (h : MEquilibrium S β Bm1 s B P i) (t : ℕ)
    (hB0 : ∀ᵐ ω ∂S.μ, B t ω ≠ 0) :
    ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s (t + 1) ω * S.E t (S.forwardSol β s (t + 1)) ω := by
  filter_upwards [mDebt_eq_signed S hβ0 h t hB0, h.2.2.2.2.2.1.2 t, h.2.1 t, h.2.1 (t + 1),
    mEqm_rate_gt S hβ0 h t, hB0] with ω h1 h2 h3 h4 h5 h6
  have e1 : B t ω = (1 + i t ω) * P t ω * (β * S.E t (S.forwardSol β s (t + 1)) ω) := h1
  have e2 : S.forwardSol β s (t + 1) ω = B t ω / P (t + 1) ω := (h2 : _ = _).symm
  have hi : 0 < 1 + i t ω := by linarith
  have hE : S.E t (S.forwardSol β s (t + 1)) ω ≠ 0 := by
    intro h0
    rw [h0, mul_zero, mul_zero] at e1
    exact h6 e1
  have hBE : 0 < B t ω * S.E t (S.forwardSol β s (t + 1)) ω := by
    rw [e1]
    have : 0 < (1 + i t ω) * P t ω * β := by positivity
    nlinarith [mul_self_pos.mpr hE]
  rw [e2, div_mul_eq_mul_div]
  exact div_pos hBE h4

/-! ### Existence and uniqueness with debt of either sign -/

/-- Cochrane (2023), §2.4.3, p. 31, on a probability space, debt of either sign: the target price
level is positive almost surely when `B_{−1} PV_0 > 0`, `1 + i > 0` and `PV_{t+1} E_t PV_{t+1} > 0`
almost surely.
Generalises `TidyR6MeasHyp.mPegP_pos_ae`. -/
theorem mPegP_pos_signed (hβ0 : 0 < β) (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω * S.forwardSol β s 0 ω)
    (hi : ∀ t, ∀ᵐ ω ∂S.μ, -1 < i t ω)
    (hsign : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s (t + 1) ω *
      S.E t (S.forwardSol β s (t + 1)) ω) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, 0 < mPegP S β Bm1 s i t ω := by
  induction t with
  | zero =>
    filter_upwards [hB] with ω h1
    exact div_pos_of_mul_pos h1
  | succ t ih =>
    filter_upwards [ih, hsign t, hi t] with ω h1 h2 h3
    change 0 < (1 + i t ω) * mPegP S β Bm1 s i t ω * (β * S.E t (S.forwardSol β s (t + 1)) ω) /
      S.forwardSol β s (t + 1) ω
    have h4 : 0 < 1 + i t ω := by linarith
    have h6 : 0 < S.E t (S.forwardSol β s (t + 1)) ω * S.forwardSol β s (t + 1) ω := by
      rw [mul_comm]
      exact h2
    have h5 : 0 < β * S.E t (S.forwardSol β s (t + 1)) ω / S.forwardSol β s (t + 1) ω := by
      rw [mul_div_assoc]
      exact mul_pos hβ0 (div_pos_of_mul_pos h6)
    rw [mul_div_assoc]
    exact mul_pos (mul_pos h4 h1) h5

/-- Cochrane (2023), bullets pp. 31–33, on a probability space, **debt of either sign**: for
`β > 0`, initial debt known at `0` with `B_{−1} PV_0 > 0` a.s., an adapted target with `i > −1`
a.s. and integrable bond price, and present values whose sign is known a period ahead
(`PV_{t+1} E_t PV_{t+1} > 0` a.s.), the target path is an equilibrium.
Generalises `TidyR6MeasHyp.mPeg_equilibrium_pos`. -/
theorem mPeg_equilibrium_signed (hβ0 : 0 < β) (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1)
    (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω * S.forwardSol β s 0 ω) (hia : StronglyAdapted S.𝓕 i)
    (hi : ∀ t, ∀ᵐ ω ∂S.μ, -1 < i t ω) (hQi : ∀ t, Integrable (fun ω => (1 + i t ω)⁻¹) S.μ)
    (hsign : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s (t + 1) ω *
      S.E t (S.forwardSol β s (t + 1)) ω) :
    MEquilibrium S β Bm1 s (mPegB S β Bm1 s i) (mPegP S β Bm1 s i) i := by
  have hPpos := mPegP_pos_signed S hβ0 hB hi hsign
  have hE0 : ∀ t, ∀ᵐ ω ∂S.μ, S.E t (S.forwardSol β s (t + 1)) ω ≠ 0 ∧
      S.forwardSol β s (t + 1) ω ≠ 0 := fun t => by
    filter_upwards [hsign t] with ω h
    exact ⟨fun h0 => by rw [h0, mul_zero] at h; exact lt_irrefl _ h,
      fun h0 => by rw [h0, zero_mul] at h; exact lt_irrefl _ h⟩
  have hBne : ∀ t, ∀ᵐ ω ∂S.μ, mPegB S β Bm1 s i t ω ≠ 0 := fun t => by
    filter_upwards [hPpos t, hE0 t, hi t] with ω h1 h2 h3
    change (1 + i t ω) * mPegP S β Bm1 s i t ω * (β * S.E t (S.forwardSol β s (t + 1)) ω) ≠ 0
    have h4 : 1 + i t ω ≠ 0 := by linarith
    exact mul_ne_zero (mul_ne_zero h4 h1.ne') (mul_ne_zero hβ0.ne' h2.1)
  have hratio : ∀ t, (fun ω => mPegP S β Bm1 s i t ω / mPegP S β Bm1 s i (t + 1) ω) =ᵐ[S.μ]
      fun ω => (1 + i t ω)⁻¹ * (S.forwardSol β s (t + 1) ω /
        (β * S.E t (S.forwardSol β s (t + 1)) ω)) := fun t => by
    filter_upwards [hPpos t, hE0 t, hi t] with ω h1 h2 h4
    change mPegP S β Bm1 s i t ω / ((1 + i t ω) * mPegP S β Bm1 s i t ω *
      (β * S.E t (S.forwardSol β s (t + 1)) ω) / S.forwardSol β s (t + 1) ω) = _
    have h5 : 1 + i t ω ≠ 0 := by linarith
    have := h1.ne'
    have := h2.1
    have := h2.2
    have := hβ0.ne'
    field_simp
  have hint : ∀ t, Integrable
      (fun ω => mPegP S β Bm1 s i t ω / mPegP S β Bm1 s i (t + 1) ω) S.μ := fun t => by
    set X := S.forwardSol β s (t + 1) with hX
    set σ : Ω → ℝ := fun ω => if 0 < S.E t X ω then 1 else -1 with hσ
    have hσm : StronglyMeasurable[S.𝓕 t] σ :=
      (Measurable.ite (measurableSet_lt measurable_const (S.stronglyMeasurable_E t X).measurable)
        measurable_const measurable_const).stronglyMeasurable
    have hσb : ∀ᵐ ω ∂S.μ, |σ ω| ≤ 1 := Eventually.of_forall fun ω => by
      simp only [hσ]
      split_ifs <;> norm_num
    have hXi : Integrable X S.μ := S.integrable_E _ _
    have hY := S.E_pullOut hσm hσb hXi
    have hYi : Integrable (σ * X) S.μ :=
      hXi.bdd_mul (hσm.mono (S.𝓕.le t)).aestronglyMeasurable
        (hσb.mono fun ω h => by rwa [Real.norm_eq_abs])
    have hYpos : ∀ᵐ ω ∂S.μ, 0 < (σ * X) ω := by
      filter_upwards [hsign t] with ω h
      simp only [Pi.mul_apply, hσ]
      split_ifs with hc
      · rw [one_mul]
        by_contra hn
        push Not at hn
        nlinarith
      · push Not at hc
        have : S.E t X ω ≠ 0 := fun h0 => by rw [h0, mul_zero] at h; exact lt_irrefl _ h
        have hlt : S.E t X ω < 0 := lt_of_le_of_ne hc this
        nlinarith
    have hmain := TidyR6MeasHyp.integrable_ratio S hβ0
      (((hia t).measurable.const_add 1).inv.stronglyMeasurable)
      ((hi t).mono fun ω h => (inv_pos.mpr (by linarith)).le) (hQi t) hYi hYpos
    refine hmain.congr ?_
    filter_upwards [hY, hratio t, hE0 t] with ω e1 e2 e3
    have hEX : S.E t X ω ≠ 0 := e3.1
    rw [e2, show S.forwardSol β s (t + 1) = X from rfl]
    simp only [Pi.mul_apply, Pi.inv_apply] at e1 ⊢
    rw [e1]
    simp only [hσ]
    split_ifs <;> (field_simp; try ring)
  refine ⟨mPegP_sm S hBm1 hia, hPpos, mPegB_sm S hBm1 hia, hia, hint, ⟨?_, fun t => ?_⟩,
    fun t => ?_⟩
  · filter_upwards [hB] with ω h1
    change Bm1 ω / (Bm1 ω / S.forwardSol β s 0 ω) = S.forwardSol β s 0 ω
    have : Bm1 ω ≠ 0 := fun h0 => by rw [h0, zero_mul] at h1; exact lt_irrefl _ h1
    rw [div_div_cancel₀ this]
  · filter_upwards [hBne t] with ω h1
    change mPegB S β Bm1 s i t ω / (mPegB S β Bm1 s i t ω / S.forwardSol β s (t + 1) ω) =
      S.forwardSol β s (t + 1) ω
    rw [div_div_cancel₀ h1]
  · set cc : Ω → ℝ := fun ω => ((1 + i t ω) * pvExM S β s t ω)⁻¹ with hcc
    have hccm : StronglyMeasurable[S.𝓕 t] cc :=
      ((((hia t).measurable.const_add 1).mul (pvExM_sm S β s t).measurable).inv
        ).stronglyMeasurable
    have hr2 : (fun ω => mPegP S β Bm1 s i t ω / mPegP S β Bm1 s i (t + 1) ω) =ᵐ[S.μ]
        cc * S.forwardSol β s (t + 1) := by
      filter_upwards [hratio t] with ω h
      rw [h]
      simp only [hcc, Pi.mul_apply, mul_inv]
      change (1 + i t ω)⁻¹ * (S.forwardSol β s (t + 1) ω /
        (β * S.E t (S.forwardSol β s (t + 1)) ω)) =
        (1 + i t ω)⁻¹ * (β * S.E t (S.forwardSol β s (t + 1)) ω)⁻¹ *
          S.forwardSol β s (t + 1) ω
      ring
    have hpo := condExp_mul_of_stronglyMeasurable_left hccm ((hint t).congr hr2)
      (S.integrable_E (t + 1) _)
    filter_upwards [S.E_congr hr2 t, hpo, hE0 t, hi t] with ω h1 h2 h3 h4
    rw [Pi.smul_apply, smul_eq_mul, h1]
    have h2' : S.E t (cc * S.forwardSol β s (t + 1)) ω =
        cc ω * S.E t (S.forwardSol β s (t + 1)) ω := h2
    rw [h2']
    have e : pvExM S β s t ω = β * S.E t (S.forwardSol β s (t + 1)) ω := rfl
    have h5 : 1 + i t ω ≠ 0 := by linarith
    simp only [hcc, e]
    have := h3.1
    have := hβ0.ne'
    field_simp

/-- Cochrane (2023), bullet p. 33, on a probability space, **debt of either sign**: with `β > 0`
and present values nonzero almost surely, every equilibrium with the target `i` is the target
path almost surely at every date.
Generalises `TidyR6MeasHyp.mPeg_unique_pos`. -/
theorem mPeg_unique_signed (hβ0 : 0 < β) (hpv0 : ∀ t, ∀ᵐ ω ∂S.μ, S.forwardSol β s t ω ≠ 0)
    (h : MEquilibrium S β Bm1 s B P i) (t : ℕ) :
    P t =ᵐ[S.μ] mPegP S β Bm1 s i t ∧ B t =ᵐ[S.μ] mPegB S β Bm1 s i t := by
  have hBne : ∀ t, ∀ᵐ ω ∂S.μ, B t ω ≠ 0 := fun t => by
    filter_upwards [mEqm_sign S h t, hpv0 (t + 1)] with ω h1 h2
    exact fun h0 => h2 (h1.1.mp h0)
  have hP : ∀ t, P t =ᵐ[S.μ] mPegP S β Bm1 s i t := by
    intro t
    induction t with
    | zero =>
      filter_upwards [h.2.2.2.2.2.1.1, h.2.1 0, hpv0 0] with ω h1 h2 h3
      change P 0 ω = Bm1 ω / S.forwardSol β s 0 ω
      have e : Bm1 ω / P 0 ω = S.forwardSol β s 0 ω := h1
      rw [← e]
      have : Bm1 ω ≠ 0 := fun h0 => h3 (by rw [← e, h0, zero_div])
      have := h2.ne'
      field_simp
    | succ t ih =>
      filter_upwards [h.2.2.2.2.2.1.2 t, h.2.1 (t + 1), hpv0 (t + 1),
        mDebt_eq_signed S hβ0 h t (hBne t), ih, hBne t] with ω h1 h2 h3 h4 h5 h6
      have e : B t ω / P (t + 1) ω = S.forwardSol β s (t + 1) ω := h1
      have h4' : B t ω = (1 + i t ω) * P t ω * pvExM S β s t ω := h4
      change P (t + 1) ω = (1 + i t ω) * mPegP S β Bm1 s i t ω * pvExM S β s t ω /
        S.forwardSol β s (t + 1) ω
      rw [← h5, ← h4', ← e]
      have := h2.ne'
      field_simp
  refine ⟨hP t, ?_⟩
  filter_upwards [mDebt_eq_signed S hβ0 h t (hBne t), hP t] with ω h1 h2
  have h1' : B t ω = (1 + i t ω) * P t ω * pvExM S β s t ω := h1
  rw [h1', h2]
  rfl

/-- Cochrane (2023), §§2.4.3–2.4.4, pp. 31–33, on a probability space, **the exact condition for
an interest-rate target with debt of either sign**: for `β > 0`, `B_{−1}` known at `0`, an
adapted target and present values nonzero almost surely, an equilibrium exists iff the bond
price is integrable, `i > −1` a.s., `B_{−1} PV_0 > 0` a.s. and `PV_{t+1} E_t PV_{t+1} > 0` a.s. at
every date; every equilibrium then equals the target path almost surely.
Generalises `TidyR6MeasHyp.mPeg_existsUnique_iff`. -/
theorem mPeg_existsUnique_iff_signed (hβ0 : 0 < β) (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1)
    (hia : StronglyAdapted S.𝓕 i) (hpv0 : ∀ t, ∀ᵐ ω ∂S.μ, S.forwardSol β s t ω ≠ 0) :
    ((∃ B P : ℕ → Ω → ℝ, MEquilibrium S β Bm1 s B P i) ↔
      (∀ t, Integrable (fun ω => (1 + i t ω)⁻¹) S.μ) ∧ (∀ t, ∀ᵐ ω ∂S.μ, -1 < i t ω) ∧
        (∀ᵐ ω ∂S.μ, 0 < Bm1 ω * S.forwardSol β s 0 ω) ∧
        ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s (t + 1) ω *
          S.E t (S.forwardSol β s (t + 1)) ω) ∧
    ∀ B P : ℕ → Ω → ℝ, MEquilibrium S β Bm1 s B P i → ∀ t,
      P t =ᵐ[S.μ] mPegP S β Bm1 s i t ∧ B t =ᵐ[S.μ] mPegB S β Bm1 s i t := by
  refine ⟨⟨?_, ?_⟩, fun B P h t => mPeg_unique_signed S hβ0 hpv0 h t⟩
  · rintro ⟨B, P, h⟩
    have hBne : ∀ t, ∀ᵐ ω ∂S.μ, B t ω ≠ 0 := fun t => by
      filter_upwards [mEqm_sign S h t, hpv0 (t + 1)] with ω h1 h2
      exact fun h0 => h2 (h1.1.mp h0)
    refine ⟨TidyR6MeasHyp.mEqm_bondPrice_integrable S h, mEqm_rate_gt S hβ0 h, ?_,
      fun t => mEqm_sign_condition S hβ0 h t (hBne t)⟩
    filter_upwards [h.2.2.2.2.2.1.1, h.2.1 0, hpv0 0] with ω h1 h2 h3
    have e : Bm1 ω = P 0 ω * S.forwardSol β s 0 ω := by
      have e0 : Bm1 ω / P 0 ω = S.forwardSol β s 0 ω := h1
      rw [← e0]
      field_simp
    rw [e]
    nlinarith [mul_self_pos.mpr h3]
  · rintro ⟨hQi, hi, hB, hsign⟩
    exact ⟨_, _, mPeg_equilibrium_signed S hβ0 hBm1 hB hia hi hQi hsign⟩

/-- Cochrane (2023), pp. 22, 33, no-go where present values vanish: with no surpluses and no debt
(`PV ≡ 0`), for every `c > 0` the constant price level `c` with zero debt and the rate
`β⁻¹ − 1` is an equilibrium (any `β`), and different `c` give price levels that differ almost
surely: the valuation equation does not determine the price level.
Restates `EquilibriumFormation.no_initial_debt_not_unique` on a genuine probability space. -/
theorem zero_pv_not_unique (β : ℝ) :
    (∀ c : ℝ, 0 < c → MEquilibrium S β 0 0 0 (fun _ _ => c) (fun _ _ => β⁻¹ - 1)) ∧
      ∀ c c' : ℝ, c ≠ c' → ¬ (fun _ : Ω => c) =ᵐ[S.μ] fun _ => c' := by
  have hpv : ∀ t, S.forwardSol β (0 : ℕ → Ω → ℝ) t = 0 := fun t => by
    have hd : MeasExpectationSystem.discSum β (0 : ℕ → Ω → ℝ) t = 0 := by
      funext ω
      simp [MeasExpectationSystem.discSum]
    change S.E t _ = 0
    rw [hd, S.E_zero]
  refine ⟨fun c hc => ?_, fun c c' hne h => ?_⟩
  · have e : ∀ t, (fun ω => (fun (_ : ℕ) (_ : Ω) => c) t ω / (fun (_ : ℕ) (_ : Ω) => c) (t + 1) ω)
        = fun _ => 1 := fun t => funext fun _ => div_self hc.ne'
    refine ⟨fun _ => stronglyMeasurable_const, fun _ => Eventually.of_forall fun _ => hc,
      fun _ => stronglyMeasurable_zero, fun _ => stronglyMeasurable_const,
      fun t => by rw [e t]; exact integrable_const 1, ⟨?_, fun t => ?_⟩, fun t => ?_⟩
    · rw [hpv 0]
      exact Eventually.of_forall fun _ => by simp
    · rw [hpv (t + 1)]
      exact Eventually.of_forall fun _ => by simp
    · rw [e t, S.E_const]
      refine Eventually.of_forall fun _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul, mul_one, add_sub_cancel, inv_inv]
  · obtain ⟨ω, hω⟩ := h.exists
    exact hne hω

/-! ### Adapted debt on a complete filtration -/

/-- Cochrane (2023), eq. (2.4), p. 22, on a probability space with a complete filtration,
**non-circularly**: in a derived equilibrium (`MIsEqm`, bond price `1/(1 + i)`) with
`β > 0`, adapted surpluses, integrable `P_t/P_{t+1}` and initial debt `B_{−1}` known at `0` (a
primitive), the debt sold `B` is adapted. -/
theorem debt_adapted_of_complete (hc : TidyR6MeasHyp.CompleteFiltration S) (hβ0 : 0 < β)
    (hsad : StronglyAdapted S.𝓕 s) (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1)
    (hPP : ∀ t, Integrable (fun ω => P t ω / P (t + 1) ω) S.μ)
    (h : MIsEqm S β (GeneralLinks.debtPath Bm1 B) s P (fun t ω => (1 + i t ω)⁻¹)) :
    StronglyAdapted S.𝓕 B := by
  obtain ⟨hP, hPa, hQ, hflow, -⟩ := h
  have hstep : ∀ t, StronglyMeasurable[S.𝓕 t] (GeneralLinks.debtPath Bm1 B t) →
      StronglyMeasurable[S.𝓕 t] (B t) := fun t hm => by
    set q : Ω → ℝ := β • S.E t (fun ω => P t ω / P (t + 1) ω) with hq
    have hqm : StronglyMeasurable[S.𝓕 t] q := (S.stronglyMeasurable_E t _).const_smul β
    have hqpos : ∀ᵐ ω ∂S.μ, 0 < q ω := by
      have hr : ∀ᵐ ω ∂S.μ, 0 < P t ω / P (t + 1) ω := by
        filter_upwards [hP t, hP (t + 1)] with ω h1 h2
        exact div_pos h1 h2
      filter_upwards [HouseholdMeasure.E_pos (hPP t) hr t] with ω h1
      simp only [hq, Pi.smul_apply, smul_eq_mul]
      exact mul_pos hβ0 h1
    have hg : StronglyMeasurable[S.𝓕 t]
        (fun ω => (GeneralLinks.debtPath Bm1 B t ω - P t ω * s t ω) / q ω) :=
      ((hm.measurable.sub ((hPa t).measurable.mul (hsad t).measurable)).div
        hqm.measurable).stronglyMeasurable
    refine TidyR6MeasHyp.stronglyMeasurable_of_ae_eq S hc hg ?_
    filter_upwards [hflow t, hQ t, hqpos] with ω h1 h2 h3
    have h2' : (1 + i t ω)⁻¹ = q ω := h2
    have h1' : GeneralLinks.debtPath Bm1 B t ω =
        P t ω * s t ω + (1 + i t ω)⁻¹ * B t ω := h1
    rw [h1', h2']
    field_simp
    ring
  have hall : ∀ t, StronglyMeasurable[S.𝓕 t] (GeneralLinks.debtPath Bm1 B t) := by
    intro t
    induction t with
    | zero => exact hBm1
    | succ t ih => exact (hstep t ih).mono (S.𝓕.mono (Nat.le_succ t))
  exact fun t => hstep t (hall t)

/-- Cochrane (2023), §§2.1–2.4, pp. 21–33, on a probability space with a complete filtration and
integrable surpluses: with `B_{−1}` known at `0`, integrable `P_t/P_{t+1}` and integrable real
debt, `MEquilibrium` iff `MIsEqm`, with **no adaptedness hypothesis on the debt or the rate**
(`β > 0`).
Generalises `TidyR6MeasHyp.mEquilibrium_iff_mIsEqm_complete` and
`TidyR6MeasL1.mEquilibrium_iff_mIsEqm_L1`. -/
theorem mEquilibrium_iff_mIsEqm_complete_L1 (hc : TidyR6MeasHyp.CompleteFiltration S)
    (hβ0 : 0 < β) (hsad : StronglyAdapted S.𝓕 s) (hs : SurplusL1 S β s)
    (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1)
    (hPP : ∀ t, Integrable (fun ω => P t ω / P (t + 1) ω) S.μ)
    (hx : ∀ t, Integrable (fun ω => GeneralLinks.debtPath Bm1 B t ω / P t ω) S.μ) :
    MEquilibrium S β Bm1 s B P i ↔
      MIsEqm S β (GeneralLinks.debtPath Bm1 B) s P (fun t ω => (1 + i t ω)⁻¹) := by
  constructor
  · intro h
    exact ((mEquilibrium_iff_mIsEqm_L1 hsad hs).mp h).1
  · intro h
    exact (mEquilibrium_iff_mIsEqm_L1 hsad hs).mpr ⟨h,
      debt_adapted_of_complete S hc hβ0 hsad hBm1 hPP h,
      TidyR6MeasHyp.rate_adapted_of_complete S hc h.2.2.1, hPP, hx⟩

namespace PointMass

open TidyR6MeasHyp.PointMass

/-- Cochrane (2023), eq. (2.4), p. 22: debt `0` on the support and `1` on the null state. -/
def ptDebt : ℕ → Bool → ℝ := fun _ ω => if ω then 0 else 1

/-- Cochrane (2023), eq. (2.4), p. 22, counterexample: in the point-mass economy with the trivial
filtration (which is not complete: the null state is not known), `β = 1/2`, `P ≡ 1`, no
surpluses, `B_{−1} = 0` known at `0` and the adapted rate `i ≡ 1`, the derived equilibrium
`MIsEqm` holds with the debt `ptDebt`, `P_t/P_{t+1}` and real debt are integrable and surpluses
are `TidyR6MeasL1.SurplusL1`, but the debt is not adapted and `MEquilibrium` fails: completeness
is needed in `debt_adapted_of_complete`. -/
theorem debt_adapted_needed :
    MIsEqm ptSystem (1 / 2) (GeneralLinks.debtPath 0 ptDebt) 0 (fun _ _ => 1)
        (fun _ _ => (1 + 1)⁻¹) ∧
      SurplusL1 ptSystem (1 / 2) (0 : ℕ → Bool → ℝ) ∧
      (∀ t, Integrable (fun ω => GeneralLinks.debtPath (0 : Bool → ℝ) ptDebt t ω /
        (fun (_ : ℕ) (_ : Bool) => (1 : ℝ)) t ω) ptSystem.μ) ∧
      ¬ StronglyAdapted ptSystem.𝓕 ptDebt ∧
      ¬ MEquilibrium ptSystem (1 / 2) 0 0 ptDebt (fun _ _ => 1) (fun _ _ => 1) := by
  have hna : ¬ StronglyAdapted ptSystem.𝓕 ptDebt := by
    intro h
    obtain ⟨c, hc⟩ := stronglyMeasurable_bot_iff.mp (h 0)
    have h1 := congrFun hc true
    have h2 := congrFun hc false
    simp only [ptDebt] at h1 h2
    norm_num at h1 h2
    linarith
  have hdp : ∀ n, GeneralLinks.debtPath (0 : Bool → ℝ) ptDebt n true = 0 := fun n => by
    cases n <;> rfl
  refine ⟨⟨fun t => Eventually.of_forall fun _ => one_pos, fun t => stronglyMeasurable_const,
    fun t => ?_, fun t => ae_pt.mpr ?_, fun t => ae_pt.mpr ?_⟩, ⟨fun _ => integrable_zero _ _ _,
    fun k => by simp⟩, fun t => Integrable.of_finite, hna, fun h => hna h.2.2.1⟩
  · rw [ptE]
    exact ae_pt.mpr (by norm_num)
  · rw [hdp t, hdp (t + 1)]
    simp
  · simp only [ptE, hdp, div_one, mul_zero]
    exact tendsto_const_nhds

end PointMass

end Cochrane.IntertemporalModel.TidyR6MeasSigned
