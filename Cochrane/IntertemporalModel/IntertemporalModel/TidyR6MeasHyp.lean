/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.TidyR5Meas
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-!
# The measure-theoretic equilibrium results without their explicit hypotheses

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.1, pp. 21–23 (the
valuation equation (2.7), the bond price (2.3), flow (2.4) and transversality (2.6)) and §2.4,
pp. 29–33 (interest-rate targets), on a probability space (`MeasExpectationSystem`). The
results of `TidyR5Meas` carry explicit hypotheses; this module removes each of them or proves
that it is needed.

## Interest-rate targets

`TidyR5Meas.mPeg_equilibrium` assumes surpluses bounded almost surely, present values bounded
below by `c > 0` almost surely, a target `i > −1` in every state and an integrable bond price.

* `mEqm_bondPrice_integrable`: the integrability of `1/(1 + i_t)` is **necessary** in every
  equilibrium (it is almost surely `β E_t(P_t/P_{t+1})`); `mEqm_rate_gt` of `TidyR5Meas` gives
  `i > −1` almost surely; `mEqm_pv_zero_pos`, `mEqm_pv_succ_pos_iff`: positive present values
  almost surely are necessary at date `0` and equivalent to positive debt at later dates.
* `integrable_ratio`: the integrability of `P_t/P_{t+1}` follows from that of the bond price
  alone (conditional monotone convergence), so no bound on surpluses is needed.
* `mPeg_existsUnique_iff` (headline): for `β > 0`, positive initial debt and an adapted target,
  **an equilibrium with positive debt exists iff the bond price is integrable, `i > −1` almost
  surely and present values are positive almost surely**; then it is unique almost surely at
  every date (`mPeg_unique_pos`, `mPeg_existsUnique_pos`). No hypothesis on the surpluses
  remains, and no bound `c`.
* `forwardSol_hasSum_dom`: the present value is the genuine forward sum `∑ βᵏ E_t s_{t+k}` for
  surpluses dominated by any summable bound (growing surpluses included).
* `Uniform.nonintRate_no_equilibrium`: on the uniform probability space a target satisfying
  every other hypothesis of `TidyR5Meas.mPeg_equilibrium` but with non-integrable bond price has
  no equilibrium.

## The two equilibrium notions

* `mEquilibrium_iff_mIsEqm_reg`: `MEquilibrium` iff `MIsEqm` plus adapted debt, adapted rate,
  integrable `P_t/P_{t+1}` and integrable real debt, with no hypothesis on `B`, `P`, `i`
  (integrable real debt is automatic in an `MEquilibrium`, `mEqm_realDebt_integrable`).
* The adapted rate: `rateVersion` is an adapted version of the rate, equal to it almost surely
  under almost-sure bond pricing (`rate_ae_eq_version`), so every derived equilibrium becomes an
  `MEquilibrium` after this choice (`mIsEqm_version`); on a complete filtration
  (`CompleteFiltration`) the rate is adapted automatically (`rate_adapted_of_complete`,
  `mEquilibrium_iff_mIsEqm_complete`).
* Each remaining condition is needed: `PointMass.rate_adapted_needed` (a point mass with the
  trivial filtration), `Uniform.realDebt_integrable_needed` and `Uniform.ratio_integrable_needed`
  (the uniform distribution on `(0, 1]` with full information), where `MIsEqm` holds because
  `condExp` is `0` on non-integrable functions, every other hypothesis holds, and `MEquilibrium`
  fails.
-/

namespace Cochrane.IntertemporalModel.TidyR6MeasHyp

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure TidyR5Meas

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)
variable {β : ℝ} {Bm1 : Ω → ℝ} {s B P i : ℕ → Ω → ℝ}

/-! ### Necessary conditions -/

/-- Cochrane (2023), eq. (2.3), p. 22, on a probability space: in every equilibrium the bond
price `1/(1 + i_t)` is integrable (it is almost surely `β E_t(P_t/P_{t+1})`). -/
theorem mEqm_bondPrice_integrable (h : MEquilibrium S β Bm1 s B P i) (t : ℕ) :
    Integrable (fun ω => (1 + i t ω)⁻¹) S.μ :=
  ((S.integrable_E t _).smul β).congr (h.2.2.2.2.2.2 t).symm

/-- Cochrane (2023), eq. (2.7), p. 22, on a probability space: with positive initial debt,
every equilibrium has `PV_0 > 0` almost surely.
Restates `Valuation.eqm_pv_pos` on a genuine probability space. -/
theorem mEqm_pv_zero_pos (h : MEquilibrium S β Bm1 s B P i) (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω) :
    ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s 0 ω := by
  filter_upwards [h.2.2.2.2.2.1.1, h.2.1 0, hB] with ω h1 h2 h3
  have e : Bm1 ω / P 0 ω = S.forwardSol β s 0 ω := h1
  rw [← e]
  exact div_pos h3 h2

/-- Cochrane (2023), eq. (2.12), p. 30, on a probability space: in every equilibrium
`PV_{t+1} > 0` almost surely iff the debt sold at `t` is positive almost surely. -/
theorem mEqm_pv_succ_pos_iff (h : MEquilibrium S β Bm1 s B P i) (t : ℕ) :
    (∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s (t + 1) ω) ↔ ∀ᵐ ω ∂S.μ, 0 < B t ω := by
  constructor
  · intro hpv
    filter_upwards [h.2.2.2.2.2.1.2 t, h.2.1 (t + 1), hpv] with ω h1 h2 h3
    have e : B t ω / P (t + 1) ω = S.forwardSol β s (t + 1) ω := h1
    rw [← e] at h3
    exact (div_pos_iff_of_pos_right h2).mp h3
  · intro hB
    filter_upwards [h.2.2.2.2.2.1.2 t, h.2.1 (t + 1), hB] with ω h1 h2 h3
    have e : B t ω / P (t + 1) ω = S.forwardSol β s (t + 1) ω := h1
    rw [← e]
    exact div_pos h3 h2

/-- Cochrane (2023), eq. (2.7), p. 22, on a probability space: in every equilibrium the real
debt `B_{t−1}/P_t` is integrable at every date (it is almost surely a conditional
expectation). -/
theorem mEqm_realDebt_integrable (h : MEquilibrium S β Bm1 s B P i) (t : ℕ) :
    Integrable (fun ω => GeneralLinks.debtPath Bm1 B t ω / P t ω) S.μ := by
  have hI : ∀ n, Integrable (S.forwardSol β s n) S.μ := fun n => S.integrable_E n _
  cases t with
  | zero => exact (hI 0).congr h.2.2.2.2.2.1.1.symm
  | succ t => exact (hI (t + 1)).congr (h.2.2.2.2.2.1.2 t).symm

/-! ### Integrability of `P_t/P_{t+1}` from the bond price alone -/

/-- Cochrane (2023), eqs. (2.3) and (2.15), pp. 22, 31, on a probability space: for `β > 0`, a
nonnegative integrable `q` known at `t` and a positive integrable `X`,
`q X/(β E_t X)` is integrable (conditional monotone convergence,
`HouseholdMeasureTVC.integrable_mul_of_E`). With `q = 1/(1 + i_t)` and `X = PV_{t+1}` this is
`P_t/P_{t+1}` along the target path. -/
theorem integrable_ratio (hβ0 : 0 < β) {t : ℕ} {q X : Ω → ℝ} (hq : StronglyMeasurable[S.𝓕 t] q)
    (hq0 : ∀ᵐ ω ∂S.μ, 0 ≤ q ω) (hqi : Integrable q S.μ) (hX : Integrable X S.μ)
    (hX0 : ∀ᵐ ω ∂S.μ, 0 < X ω) :
    Integrable (fun ω => q ω * (X ω / (β * S.E t X ω))) S.μ := by
  set Z : Ω → ℝ := fun ω => q ω / (β * S.E t X ω) with hZ
  have hZm : StronglyMeasurable[S.𝓕 t] Z :=
    (hq.measurable.div (measurable_const.mul (S.stronglyMeasurable_E t X).measurable)
      ).stronglyMeasurable
  have hEpos := HouseholdMeasure.E_pos hX hX0 t
  have hZ0 : ∀ᵐ ω ∂S.μ, 0 ≤ Z ω := by
    filter_upwards [hq0, hEpos] with ω h1 h2
    exact div_nonneg h1 (mul_pos hβ0 h2).le
  have hZE : Integrable (fun ω => Z ω * S.E t X ω) S.μ := by
    refine (hqi.div_const β).congr ?_
    filter_upwards [hEpos] with ω h
    simp only [hZ]
    have := h.ne'
    have := hβ0.ne'
    field_simp
  have hmain := (HouseholdMeasureTVC.integrable_mul_of_E hZm hZ0 hX
    (hX0.mono fun ω h => h.le) hZE).1
  refine hmain.congr (Eventually.of_forall fun ω => ?_)
  simp only [hZ]
  ring

/-! ### Interest-rate targets with positive present values only -/

/-- Cochrane (2023), eq. (2.15), p. 31, on a probability space: positive present values almost
surely give a positive ex-dividend present value almost surely (`β > 0`). -/
theorem pvExM_pos (hβ0 : 0 < β) (hpv : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s t ω) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, 0 < pvExM S β s t ω := by
  filter_upwards [HouseholdMeasure.E_pos (S.integrable_E (t + 1) _) (hpv (t + 1)) t] with ω h
  simp only [pvExM, Pi.smul_apply, smul_eq_mul]
  exact mul_pos hβ0 h

/-- Cochrane (2023), §2.4.3, p. 31, on a probability space: the target price level is positive
almost surely when initial debt, `1 + i` and present values are positive almost surely.
Generalises `TidyR5Meas.mPegP_pos`. -/
theorem mPegP_pos_ae (hβ0 : 0 < β) (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω)
    (hi : ∀ t, ∀ᵐ ω ∂S.μ, -1 < i t ω) (hpv : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s t ω)
    (t : ℕ) : ∀ᵐ ω ∂S.μ, 0 < mPegP S β Bm1 s i t ω := by
  induction t with
  | zero =>
    filter_upwards [hB, hpv 0] with ω h1 h2
    exact div_pos h1 h2
  | succ t ih =>
    filter_upwards [ih, pvExM_pos S hβ0 hpv t, hpv (t + 1), hi t] with ω h1 h2 h3 h4
    change 0 < (1 + i t ω) * mPegP S β Bm1 s i t ω * pvExM S β s t ω /
      S.forwardSol β s (t + 1) ω
    have h5 : 0 < 1 + i t ω := by linarith
    positivity

/-- Cochrane (2023), eq. (2.15), p. 31, on a probability space: the target debt is positive
almost surely under the hypotheses of `mPegP_pos_ae`. -/
theorem mPegB_pos_ae (hβ0 : 0 < β) (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω)
    (hi : ∀ t, ∀ᵐ ω ∂S.μ, -1 < i t ω) (hpv : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s t ω)
    (t : ℕ) : ∀ᵐ ω ∂S.μ, 0 < mPegB S β Bm1 s i t ω := by
  filter_upwards [mPegP_pos_ae S hβ0 hB hi hpv t, pvExM_pos S hβ0 hpv t, hi t] with ω h1 h2 h3
  change 0 < (1 + i t ω) * mPegP S β Bm1 s i t ω * pvExM S β s t ω
  have h4 : 0 < 1 + i t ω := by linarith
  positivity

/-- Cochrane (2023), bullets pp. 31–33, "the government can target nominal interest rates", on a
probability space, **without bounds**: for `β > 0`, positive initial debt known at `0`, an
adapted target with `i > −1` almost surely and integrable bond price, and present values
positive almost surely, the target path `(mPegP, mPegB)` is an equilibrium. No hypothesis on
the surpluses and no `β < 1` is needed.
Generalises `TidyR5Meas.mPeg_equilibrium`. -/
theorem mPeg_equilibrium_pos (hβ0 : 0 < β) (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1)
    (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω) (hia : StronglyAdapted S.𝓕 i)
    (hi : ∀ t, ∀ᵐ ω ∂S.μ, -1 < i t ω) (hQi : ∀ t, Integrable (fun ω => (1 + i t ω)⁻¹) S.μ)
    (hpv : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s t ω) :
    MEquilibrium S β Bm1 s (mPegB S β Bm1 s i) (mPegP S β Bm1 s i) i := by
  have hPpos := mPegP_pos_ae S hβ0 hB hi hpv
  have hpe := pvExM_pos S hβ0 hpv
  have hBpos := mPegB_pos_ae S hβ0 hB hi hpv
  have hratio : ∀ t, (fun ω => mPegP S β Bm1 s i t ω / mPegP S β Bm1 s i (t + 1) ω) =ᵐ[S.μ]
      fun ω => (1 + i t ω)⁻¹ * (S.forwardSol β s (t + 1) ω /
        (β * S.E t (S.forwardSol β s (t + 1)) ω)) := fun t => by
    filter_upwards [hPpos t, hpe t, hpv (t + 1), hi t] with ω h1 h2 h3 h4
    change mPegP S β Bm1 s i t ω / ((1 + i t ω) * mPegP S β Bm1 s i t ω * pvExM S β s t ω /
      S.forwardSol β s (t + 1) ω) = _
    have e : pvExM S β s t ω = β * S.E t (S.forwardSol β s (t + 1)) ω := rfl
    rw [← e]
    have h5 : 1 + i t ω ≠ 0 := by linarith
    have := h1.ne'
    have := h2.ne'
    have := h3.ne'
    field_simp
  have hint : ∀ t, Integrable
      (fun ω => mPegP S β Bm1 s i t ω / mPegP S β Bm1 s i (t + 1) ω) S.μ := fun t =>
    (integrable_ratio S hβ0 (((hia t).measurable.const_add 1).inv.stronglyMeasurable)
      ((hi t).mono fun ω h => (inv_pos.mpr (by linarith)).le) (hQi t) (S.integrable_E _ _)
      (hpv (t + 1))).congr (hratio t).symm
  refine ⟨mPegP_sm S hBm1 hia, hPpos, mPegB_sm S hBm1 hia, hia, hint, ⟨?_, fun t => ?_⟩,
    fun t => ?_⟩
  · filter_upwards [hB] with ω h1
    change Bm1 ω / (Bm1 ω / S.forwardSol β s 0 ω) = S.forwardSol β s 0 ω
    rw [div_div_cancel₀ h1.ne']
  · filter_upwards [hBpos t] with ω h1
    change mPegB S β Bm1 s i t ω / (mPegB S β Bm1 s i t ω / S.forwardSol β s (t + 1) ω) =
      S.forwardSol β s (t + 1) ω
    rw [div_div_cancel₀ h1.ne']
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
    filter_upwards [S.E_congr hr2 t, hpo, hpe t, hi t] with ω h1 h2 h3 h4
    rw [Pi.smul_apply, smul_eq_mul, h1]
    have h2' : S.E t (cc * S.forwardSol β s (t + 1)) ω =
        cc ω * S.E t (S.forwardSol β s (t + 1)) ω := h2
    rw [h2']
    have e : pvExM S β s t ω = β * S.E t (S.forwardSol β s (t + 1)) ω := rfl
    have h5 : 1 + i t ω ≠ 0 := by linarith
    rw [e] at h3
    simp only [hcc, e]
    have hE : S.E t (S.forwardSol β s (t + 1)) ω ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h3
      exact lt_irrefl _ h3
    have := h3.ne'
    field_simp

/-- Cochrane (2023), bullet p. 33, "inflation can be stable and determinate under an interest
rate target", on a probability space: with `β > 0` and present values positive almost surely,
every equilibrium with the target `i` is the target path almost surely at every date.
Generalises `TidyR5Meas.mPeg_unique`. -/
theorem mPeg_unique_pos (hβ0 : 0 < β) (hpv : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s t ω)
    (h : MEquilibrium S β Bm1 s B P i) (t : ℕ) :
    P t =ᵐ[S.μ] mPegP S β Bm1 s i t ∧ B t =ᵐ[S.μ] mPegB S β Bm1 s i t := by
  have hP : ∀ t, P t =ᵐ[S.μ] mPegP S β Bm1 s i t := by
    intro t
    induction t with
    | zero => exact mPrice_zero S h (hpv 0)
    | succ t ih =>
      filter_upwards [mPrice_succ S h t (hpv (t + 1)), mDebt_eq S hβ0 h t (hpv (t + 1)), ih]
        with ω h1 h2 h3
      have h2' : B t ω = (1 + i t ω) * P t ω * pvExM S β s t ω := h2
      rw [h1]
      change B t ω / S.forwardSol β s (t + 1) ω = (1 + i t ω) * mPegP S β Bm1 s i t ω *
        pvExM S β s t ω / S.forwardSol β s (t + 1) ω
      rw [h2', h3]
  refine ⟨hP t, ?_⟩
  filter_upwards [mDebt_eq S hβ0 h t (hpv (t + 1)), hP t] with ω h1 h2
  have h1' : B t ω = (1 + i t ω) * P t ω * pvExM S β s t ω := h1
  rw [h1', h2]
  rfl

/-- Cochrane (2023), §§2.4.3–2.4.4, pp. 31–33, on a probability space: **existence and almost
sure uniqueness under an interest-rate target** under the hypotheses of `mPeg_equilibrium_pos`
(no bound on surpluses, no `c`).
Generalises `TidyR5Meas.mPeg_existsUnique`. -/
theorem mPeg_existsUnique_pos (hβ0 : 0 < β) (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1)
    (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω) (hia : StronglyAdapted S.𝓕 i)
    (hi : ∀ t, ∀ᵐ ω ∂S.μ, -1 < i t ω) (hQi : ∀ t, Integrable (fun ω => (1 + i t ω)⁻¹) S.μ)
    (hpv : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s t ω) :
    ∃ x : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), MEquilibrium S β Bm1 s x.2 x.1 i ∧
      ∀ y : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), MEquilibrium S β Bm1 s y.2 y.1 i →
        ∀ t, y.1 t =ᵐ[S.μ] x.1 t ∧ y.2 t =ᵐ[S.μ] x.2 t :=
  ⟨(mPegP S β Bm1 s i, mPegB S β Bm1 s i),
    mPeg_equilibrium_pos S hβ0 hBm1 hB hia hi hQi hpv,
    fun _ hy t => mPeg_unique_pos S hβ0 hpv hy t⟩

/-- Cochrane (2023), §§2.4.3–2.4.4, pp. 31–33, on a probability space, **the exact condition
for an interest-rate target**: for `β > 0`, positive initial debt known at `0` and an adapted
target `i`, an equilibrium with positive debt exists iff the bond price `1/(1 + i_t)` is
integrable, `i_t > −1` almost surely and `PV_t > 0` almost surely, at every date.
Generalises `TidyR5Meas.mPeg_existsUnique`. -/
theorem mPeg_existsUnique_iff (hβ0 : 0 < β) (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1)
    (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω) (hia : StronglyAdapted S.𝓕 i) :
    (∃ B P : ℕ → Ω → ℝ, MEquilibrium S β Bm1 s B P i ∧ ∀ t, ∀ᵐ ω ∂S.μ, 0 < B t ω) ↔
      (∀ t, Integrable (fun ω => (1 + i t ω)⁻¹) S.μ) ∧ (∀ t, ∀ᵐ ω ∂S.μ, -1 < i t ω) ∧
        ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s t ω := by
  constructor
  · rintro ⟨B, P, h, hBp⟩
    refine ⟨mEqm_bondPrice_integrable S h, mEqm_rate_gt S hβ0 h, fun t => ?_⟩
    cases t with
    | zero => exact mEqm_pv_zero_pos S h hB
    | succ t => exact (mEqm_pv_succ_pos_iff S h t).mpr (hBp t)
  · rintro ⟨hQi, hi, hpv⟩
    exact ⟨_, _, mPeg_equilibrium_pos S hβ0 hBm1 hB hia hi hQi hpv,
      mPegB_pos_ae S hβ0 hB hi hpv⟩

/-- Cochrane (2023), eq. (2.7), p. 22, on a probability space: the present value is the genuine
forward sum `PV_t = ∑ βᵏ E_t s_{t+k}` almost surely for surpluses dominated almost surely by
any bounds `M_k` with `∑ βᵏ M_k < ∞` (`β > 0`), which allows growing surpluses.
Generalises `ExpectationsMeasure.MeasExpectationSystem.forwardSol_hasSum`. -/
theorem forwardSol_hasSum_dom {Mb : ℕ → ℝ} (hβ0 : 0 < β)
    (hsm : ∀ t, AEStronglyMeasurable (s t) S.μ) (hb : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ Mb t)
    (hsum : Summable (fun k => β ^ k * Mb k)) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun k => β ^ k * S.E t (s (t + k)) ω) (S.forwardSol β s t ω) := by
  have hsumt : Summable (fun k => β ^ k * Mb (t + k)) := by
    have h1 : Summable (fun k => β ^ (k + t) * Mb (k + t)) := (summable_nat_add_iff t).mpr hsum
    refine (h1.mul_left ((β ^ t)⁻¹)).congr fun k => ?_
    rw [pow_add, add_comm k t]
    have : β ^ t ≠ 0 := pow_ne_zero t hβ0.ne'
    field_simp
  have hsm' : ∀ k, S.E t (fun ω => β ^ k * s (t + k) ω) =ᵐ[S.μ] β ^ k • S.E t (s (t + k)) :=
    fun k => S.E_smul (β ^ k) (s (t + k)) t
  filter_upwards [S.E_hasSum (f := fun k ω => β ^ k * s (t + k) ω) hsumt
    (fun k => (hsm (t + k)).const_mul _) (fun k => by
      filter_upwards [hb (t + k)] with ω h
      rw [abs_mul, abs_pow, abs_of_pos hβ0]
      exact mul_le_mul_of_nonneg_left h (pow_nonneg hβ0.le k)) t,
    ae_all_iff.2 hsm'] with ω h1 h2
  have e : (fun k => β ^ k * S.E t (s (t + k)) ω) =
      fun k => S.E t (fun ω => β ^ k * s (t + k) ω) ω := by
    funext k
    rw [h2 k, Pi.smul_apply, smul_eq_mul]
  rw [e]
  exact h1

/-! ### The two equilibrium notions without regularity hypotheses -/

/-- Cochrane (2023), §§2.1–2.4, pp. 21–33, on a probability space: `MEquilibrium` is exactly
`MIsEqm` (maturing debt `GeneralLinks.debtPath B_{−1} B`, bond price `1/(1 + i)`) together with
adapted debt, an adapted rate, integrable `P_t/P_{t+1}` and integrable real debt; the only
hypotheses are on `β` and the surpluses (those of `TidyR5Meas.mFlowTvc_iff_valuation`).
Generalises `TidyR5Meas.mEquilibrium_iff_mIsEqm`. -/
theorem mEquilibrium_iff_mIsEqm_reg (hβ0 : 0 < β) (hβ1 : β < 1)
    (hsad : StronglyAdapted S.𝓕 s) {M : ℝ} (hsM : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ M) :
    MEquilibrium S β Bm1 s B P i ↔
      MIsEqm S β (GeneralLinks.debtPath Bm1 B) s P (fun t ω => (1 + i t ω)⁻¹) ∧
        StronglyAdapted S.𝓕 B ∧ StronglyAdapted S.𝓕 i ∧
        (∀ t, Integrable (fun ω => P t ω / P (t + 1) ω) S.μ) ∧
        ∀ t, Integrable (fun ω => GeneralLinks.debtPath Bm1 B t ω / P t ω) S.μ := by
  constructor
  · intro h
    have hx := mEqm_realDebt_integrable S h
    exact ⟨(mEquilibrium_iff_mIsEqm S hβ0 hβ1 hsad hsM h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 hx).mp h,
      h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, hx⟩
  · rintro ⟨h, hBa, hia, hPP, hx⟩
    exact (mEquilibrium_iff_mIsEqm S hβ0 hβ1 hsad hsM hBa hia hPP hx).mpr h

/-- Cochrane (2023), eq. (2.3), p. 22, on a probability space: the adapted version of the rate
implied by the bond price, `i^v_t = (β E_t(P_t/P_{t+1}))⁻¹ − 1`. -/
noncomputable def rateVersion (β : ℝ) (P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (β * S.E t (fun ω => P t ω / P (t + 1) ω) ω)⁻¹ - 1

/-- Cochrane (2023), eq. (2.3), p. 22: the version of the rate is adapted. -/
theorem rateVersion_adapted (β : ℝ) (P : ℕ → Ω → ℝ) :
    StronglyAdapted S.𝓕 (rateVersion S β P) := fun t =>
  (((S.stronglyMeasurable_E t _).measurable.const_mul β).inv.sub_const 1).stronglyMeasurable

/-- Cochrane (2023), eq. (2.3), p. 22: the version of the rate satisfies the bond-pricing
condition in every state. -/
theorem rateVersion_pricing (β : ℝ) (P : ℕ → Ω → ℝ) :
    MBondPricing S β P (rateVersion S β P) := fun t =>
  Eventually.of_forall fun ω => by
    simp only [rateVersion, add_sub_cancel, inv_inv, Pi.smul_apply, smul_eq_mul]

/-- Cochrane (2023), eq. (2.3), p. 22, on a probability space: under almost-sure bond pricing
the rate equals its adapted version almost surely at every date. -/
theorem rate_ae_eq_version (h : MBondPricing S β P i) (t : ℕ) :
    i t =ᵐ[S.μ] rateVersion S β P t := by
  filter_upwards [h t] with ω h1
  have e : (1 + i t ω)⁻¹ = β * S.E t (fun ω => P t ω / P (t + 1) ω) ω := h1
  simp only [rateVersion]
  rw [← e, inv_inv]
  ring

/-- Cochrane (2023), §§2.1–2.4, pp. 21–33, on a probability space: a derived equilibrium
(`MIsEqm` with bond price `1/(1 + i)`) with adapted debt, integrable `P_t/P_{t+1}` and
integrable real debt is an `MEquilibrium` once the rate is replaced by its adapted version,
which equals it almost surely (hypotheses on `β` and `s` as in `mEquilibrium_iff_mIsEqm_reg`). -/
theorem mIsEqm_version (hβ0 : 0 < β) (hβ1 : β < 1) (hsad : StronglyAdapted S.𝓕 s) {M : ℝ}
    (hsM : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ M)
    (h : MIsEqm S β (GeneralLinks.debtPath Bm1 B) s P (fun t ω => (1 + i t ω)⁻¹))
    (hBa : StronglyAdapted S.𝓕 B) (hPP : ∀ t, Integrable (fun ω => P t ω / P (t + 1) ω) S.μ)
    (hx : ∀ t, Integrable (fun ω => GeneralLinks.debtPath Bm1 B t ω / P t ω) S.μ) :
    MEquilibrium S β Bm1 s B P (rateVersion S β P) ∧ ∀ t, i t =ᵐ[S.μ] rateVersion S β P t := by
  have hbp : MBondPricing S β P i := h.2.2.1
  have h' : MIsEqm S β (GeneralLinks.debtPath Bm1 B) s P
      (fun t ω => (1 + rateVersion S β P t ω)⁻¹) :=
    ⟨h.1, h.2.1, rateVersion_pricing S β P, fun t => by
      filter_upwards [h.2.2.2.1 t, rate_ae_eq_version S hbp t] with ω h1 h2
      rw [h1, h2], h.2.2.2.2⟩
  exact ⟨(mEquilibrium_iff_mIsEqm S hβ0 hβ1 hsad hsM hBa (rateVersion_adapted S β P) hPP
    hx).mpr h', rate_ae_eq_version S hbp⟩

/-- Cochrane (2023), §2.1, p. 21 (information): a filtration is complete when every null set is
known at every date. -/
def CompleteFiltration : Prop := ∀ t (N : Set Ω), S.μ N = 0 → MeasurableSet[S.𝓕 t] N

/-- Cochrane (2023), §2.1, p. 21: on a complete filtration, a function equal almost surely to one
known at `t` is known at `t`. -/
theorem stronglyMeasurable_of_ae_eq (hc : CompleteFiltration S) {t : ℕ} {f g : Ω → ℝ}
    (hg : StronglyMeasurable[S.𝓕 t] g) (hfg : f =ᵐ[S.μ] g) : StronglyMeasurable[S.𝓕 t] f := by
  have hN : S.μ {ω | ¬ f ω = g ω} = 0 := ae_iff.mp hfg
  have hm : Measurable[S.𝓕 t] f := by
    intro U hU
    have e : f ⁻¹' U = (g ⁻¹' U ∩ {ω | ¬ f ω = g ω}ᶜ) ∪ (f ⁻¹' U ∩ {ω | ¬ f ω = g ω}) := by
      ext ω
      by_cases h : f ω = g ω <;> simp [h]
    rw [e]
    exact ((hg.measurable hU).inter (hc t _ hN).compl).union
      (hc t _ (measure_mono_null Set.inter_subset_right hN))
  exact hm.stronglyMeasurable

/-- Cochrane (2023), eq. (2.3), p. 22, on a probability space with a complete filtration:
almost-sure bond pricing makes the rate adapted. -/
theorem rate_adapted_of_complete (hc : CompleteFiltration S) (h : MBondPricing S β P i) :
    StronglyAdapted S.𝓕 i := fun t =>
  stronglyMeasurable_of_ae_eq S hc (rateVersion_adapted S β P t) (rate_ae_eq_version S h t)

/-- Cochrane (2023), §§2.1–2.4, pp. 21–33, on a probability space with a complete filtration:
the two notions agree with no hypothesis on the rate (`TidyR5Meas.mEquilibrium_iff_mIsEqm`
without its hypothesis that the rate is adapted). -/
theorem mEquilibrium_iff_mIsEqm_complete (hc : CompleteFiltration S) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hsad : StronglyAdapted S.𝓕 s) {M : ℝ} (hsM : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ M)
    (hBa : StronglyAdapted S.𝓕 B) (hPP : ∀ t, Integrable (fun ω => P t ω / P (t + 1) ω) S.μ)
    (hx : ∀ t, Integrable (fun ω => GeneralLinks.debtPath Bm1 B t ω / P t ω) S.μ) :
    MEquilibrium S β Bm1 s B P i ↔
      MIsEqm S β (GeneralLinks.debtPath Bm1 B) s P (fun t ω => (1 + i t ω)⁻¹) := by
  constructor
  · intro h
    exact (mEquilibrium_iff_mIsEqm S hβ0 hβ1 hsad hsM hBa h.2.2.2.1 hPP hx).mp h
  · intro h
    have hia : StronglyAdapted S.𝓕 i := rate_adapted_of_complete S hc h.2.2.1
    exact (mEquilibrium_iff_mIsEqm S hβ0 hβ1 hsad hsM hBa hia hPP hx).mpr h

/-! ### Counterexample: the adapted rate is needed without a complete filtration -/

namespace PointMass

/-- Cochrane (2023), §2.1, p. 21: the point mass at `true` on `Bool`. -/
noncomputable def ptProb : ProbabilityMeasure Bool := ⟨Measure.dirac true, inferInstance⟩

/-- Cochrane (2023), §2.1, p. 21: the trivial filtration (nothing is ever learned). -/
def botFiltration : Filtration ℕ (inferInstance : MeasurableSpace Bool) :=
  ⟨fun _ => ⊥, fun _ _ _ => le_rfl, fun _ => bot_le⟩

/-- Cochrane (2023), §2.1, p. 21: the point-mass economy with the trivial filtration. -/
noncomputable def ptSystem : MeasExpectationSystem Bool := ⟨ptProb, botFiltration⟩

/-- Cochrane (2023), eq. (2.3), p. 22: a rate equal to `1` on the support and `0` on the null
state `false`, so that `1/(1 + i) = 1/2` almost surely. -/
def ptRate : ℕ → Bool → ℝ := fun _ ω => if ω then 1 else 0

/-- Cochrane (2023), §2.1, p. 21: almost surely means at `true` in the point-mass economy. -/
theorem ae_pt {p : Bool → Prop} : (∀ᵐ ω ∂ptSystem.μ, p ω) ↔ p true :=
  ae_dirac_iff (MeasurableSet.of_discrete)

/-- Cochrane (2023), §2.1, p. 21: with the trivial filtration `E_t` is the expectation. -/
theorem ptE (t : ℕ) (x : Bool → ℝ) : ptSystem.E t x = fun _ => x true := by
  change (Measure.dirac true)[x | ⊥] = _
  rw [condExp_bot, integral_dirac]

/-- Cochrane (2023), eq. (2.3), p. 22, counterexample: in the point-mass economy with the trivial
filtration, `β = 1/2`, `P ≡ 1`, no surpluses and no debt, the derived equilibrium `MIsEqm` holds
with the rate `ptRate`, and so do the other hypotheses of `TidyR5Meas.mEquilibrium_iff_mIsEqm`
(adapted surpluses bounded by `0`, adapted debt, integrable `P_t/P_{t+1}` and real debt), but the
rate is not adapted and `MEquilibrium` fails. The adapted version `rateVersion` repairs it. -/
theorem rate_adapted_needed :
    MIsEqm ptSystem (1 / 2) (GeneralLinks.debtPath 0 0) 0 (fun _ _ => 1)
        (fun t ω => (1 + ptRate t ω)⁻¹) ∧
      StronglyAdapted ptSystem.𝓕 (0 : ℕ → Bool → ℝ) ∧
      (∀ t, ∀ᵐ ω ∂ptSystem.μ, |(0 : ℕ → Bool → ℝ) t ω| ≤ 0) ∧
      (∀ t, Integrable (fun ω => (fun _ _ => (1 : ℝ)) t ω / (fun _ _ => (1 : ℝ)) (t + 1) ω)
        ptSystem.μ) ∧
      (∀ t, Integrable (fun ω => GeneralLinks.debtPath 0 0 t ω / (fun _ _ => (1 : ℝ)) t ω)
        ptSystem.μ) ∧
      ¬ StronglyAdapted ptSystem.𝓕 ptRate ∧
      ¬ MEquilibrium ptSystem (1 / 2) 0 0 0 (fun _ _ => 1) ptRate ∧
      MEquilibrium ptSystem (1 / 2) 0 0 0 (fun _ _ => 1)
        (rateVersion ptSystem (1 / 2) (fun _ _ => 1)) := by
  have hdp : ∀ n, GeneralLinks.debtPath (0 : Bool → ℝ) (0 : ℕ → Bool → ℝ) n = 0 := fun n => by
    cases n <;> rfl
  have hna : ¬ StronglyAdapted ptSystem.𝓕 ptRate := by
    intro h
    obtain ⟨c, hc⟩ := stronglyMeasurable_bot_iff.mp (h 0)
    have h1 := congrFun hc true
    have h2 := congrFun hc false
    simp only [ptRate] at h1 h2
    norm_num at h1 h2
    linarith
  have hI1 : ∀ t, Integrable (fun ω => (fun (_ : ℕ) (_ : Bool) => (1 : ℝ)) t ω /
      (fun (_ : ℕ) (_ : Bool) => (1 : ℝ)) (t + 1) ω) ptSystem.μ := fun t =>
    (integrable_const (1 : ℝ)).congr (Eventually.of_forall fun ω => by simp)
  have hE1 : ∀ t, ptSystem.E t (fun ω => (fun _ _ => (1 : ℝ)) t ω / (fun _ _ => (1 : ℝ))
      (t + 1) ω) = fun _ => 1 := fun t => by
    rw [ptE]
    norm_num
  refine ⟨⟨fun t => Eventually.of_forall fun _ => one_pos, fun t => stronglyMeasurable_const,
    fun t => ?_, fun t => Eventually.of_forall fun ω => ?_, fun t => Eventually.of_forall
    fun ω => ?_⟩, fun t => stronglyMeasurable_const,
    fun t => Eventually.of_forall fun ω => by simp, fun t => hI1 t,
    fun t => ?_, hna, fun h => hna h.2.2.2.1, ?_⟩
  · rw [hE1]
    refine ae_pt.mpr ?_
    simp [ptRate]
    norm_num
  · rw [hdp t, hdp (t + 1)]
    simp
  · simp only [hdp, Pi.zero_apply, zero_div, ptE, mul_zero]
    exact tendsto_const_nhds
  · simp only [hdp, Pi.zero_apply, zero_div]
    exact integrable_zero _ _ _
  · refine ⟨fun t => stronglyMeasurable_const, fun t => Eventually.of_forall fun _ => one_pos,
      fun t => stronglyMeasurable_const, rateVersion_adapted _ _ _, fun t => hI1 t,
      ⟨?_, fun t => ?_⟩, rateVersion_pricing _ _ _⟩
    · refine Eventually.of_forall fun ω => ?_
      change (0 : ℝ) / 1 = ptSystem.E 0 (MeasExpectationSystem.discSum (1 / 2) 0 0) ω
      rw [ptE]
      simp [MeasExpectationSystem.discSum]
    · refine Eventually.of_forall fun ω => ?_
      change (0 : ℝ) / 1 = ptSystem.E (t + 1) (MeasExpectationSystem.discSum (1 / 2) 0 (t + 1)) ω
      rw [ptE]
      simp [MeasExpectationSystem.discSum]

end PointMass

/-! ### Counterexamples on the uniform distribution with full information -/

namespace Uniform

/-- Cochrane (2023), §2.1, p. 21: the uniform distribution on `(0, 1]` as a probability measure
on `ℝ`. -/
noncomputable def unifProb : ProbabilityMeasure ℝ :=
  ⟨volume.restrict (Set.Ioc 0 1), ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; simp⟩⟩

/-- Cochrane (2023), §2.1, p. 21: full information at every date. -/
def fullFiltration : Filtration ℕ (inferInstance : MeasurableSpace ℝ) :=
  ⟨fun _ => inferInstance, fun _ _ _ => le_rfl, fun _ => le_rfl⟩

/-- Cochrane (2023), §2.1, p. 21: the uniform economy with full information. -/
noncomputable def unifSystem : MeasExpectationSystem ℝ := ⟨unifProb, fullFiltration⟩

/-- Cochrane (2023), §2.1, p. 21: `1/ω` is not integrable on the uniform economy. -/
theorem inv_not_integrable : ¬ Integrable (fun x : ℝ => x⁻¹) unifSystem.μ := by
  intro h
  have h' : IntervalIntegrable (fun x : ℝ => x⁻¹) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr h
  rw [intervalIntegrable_inv_iff] at h'
  simp at h'

/-- Cochrane (2023), §2.1, p. 21: a nonzero multiple of `1/ω` is not integrable. -/
theorem mul_inv_not_integrable {c : ℝ} (hc : c ≠ 0) :
    ¬ Integrable (fun x : ℝ => c * x⁻¹) unifSystem.μ := by
  intro h
  apply inv_not_integrable
  exact (h.const_mul c⁻¹).congr (Eventually.of_forall fun _ => inv_mul_cancel_left₀ hc _)

/-- Cochrane (2023), §2.1, p. 21: almost surely `0 < ω` in the uniform economy. -/
theorem ae_pos : ∀ᵐ x ∂unifSystem.μ, 0 < x :=
  (ae_restrict_mem measurableSet_Ioc).mono fun _ hx => hx.1

/-- Cochrane (2023), §2.1, p. 21: with full information `E_t x = x` for integrable measurable
`x`. -/
theorem unifE {t : ℕ} {x : ℝ → ℝ} (hx : StronglyMeasurable x) (hi : Integrable x unifSystem.μ) :
    unifSystem.E t x = x :=
  unifSystem.E_of_stronglyMeasurable hx hi

/-- Cochrane (2023), §2.1, p. 21: the positive version `g(ω) = ω` for `ω > 0`, `1` otherwise. -/
noncomputable def posVer (x : ℝ) : ℝ := if 0 < x then x else 1

/-- Cochrane (2023), §2.1, p. 21: the positive version is positive and measurable. -/
theorem posVer_pos (x : ℝ) : 0 < posVer x := by
  unfold posVer
  split_ifs with h
  · exact h
  · exact one_pos

/-- Cochrane (2023), §2.1, p. 21: the positive version is measurable. -/
theorem measurable_posVer : Measurable posVer :=
  Measurable.ite measurableSet_Ioi measurable_id measurable_const

/-- Cochrane (2023), §2.1, p. 21: `1/g` is not integrable. -/
theorem posVer_inv_not_integrable : ¬ Integrable (fun x => (posVer x)⁻¹) unifSystem.μ := by
  intro h
  apply inv_not_integrable
  refine h.congr ?_
  filter_upwards [ae_pos] with x hx
  simp [posVer, hx]

/-- Cochrane (2023), eq. (2.7), p. 22: with constant surpluses `1/2` and `β = 1/2` the present
value is `1` at every date (any expectation system). -/
theorem pv_half {Ω' : Type*} [MeasurableSpace Ω'] (S' : MeasExpectationSystem Ω') (t : ℕ) :
    S'.forwardSol (1 / 2) (fun _ _ => 1 / 2) t = fun _ => 1 := by
  have e : MeasExpectationSystem.discSum (Ω := Ω') (1 / 2 : ℝ) (fun _ _ => (1 / 2 : ℝ)) t =
      fun _ => 1 := by
    funext ω
    simp only [MeasExpectationSystem.discSum]
    rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  change S'.E t _ = _
  rw [e, S'.E_const]

/-- Cochrane (2023), eq. (2.3), p. 22: the target with `1 + i_0(ω) = g(ω)` (so
`1/(1 + i_0) = 1/ω` almost surely) and `i_t = 0` afterwards. -/
noncomputable def nonintRate : ℕ → ℝ → ℝ
  | 0 => fun x => posVer x - 1
  | _ + 1 => fun _ => 0

/-- Cochrane (2023), §§2.4.3–2.4.4, pp. 31–33, counterexample: on the uniform economy with
`β = 1/2`, surpluses `s ≡ 1/2` (bounded, with present value `1`), `B_{−1} = 1` and the adapted
target `nonintRate > −1` in every state, every hypothesis of `TidyR5Meas.mPeg_equilibrium`
except the integrability of the bond price holds, the bond price is not integrable, and there is
no equilibrium at all (`mEqm_bondPrice_integrable`). -/
theorem nonintRate_no_equilibrium :
    (∀ t, ∀ᵐ ω ∂unifSystem.μ, |(fun (_ : ℕ) (_ : ℝ) => (1 / 2 : ℝ)) t ω| ≤ 1 / 2) ∧
      (∀ t, ∀ᵐ ω ∂unifSystem.μ, (1 : ℝ) ≤
        unifSystem.forwardSol (1 / 2) (fun _ _ => 1 / 2) t ω) ∧
      StronglyAdapted unifSystem.𝓕 nonintRate ∧ (∀ t ω, -1 < nonintRate t ω) ∧
      ¬ Integrable (fun ω => (1 + nonintRate 0 ω)⁻¹) unifSystem.μ ∧
      ∀ B P : ℕ → ℝ → ℝ, ¬ MEquilibrium unifSystem (1 / 2) (fun _ => 1)
        (fun _ _ => 1 / 2) B P nonintRate := by
  have hni : ¬ Integrable (fun ω => (1 + nonintRate 0 ω)⁻¹) unifSystem.μ := by
    simp only [nonintRate, add_sub_cancel]
    exact posVer_inv_not_integrable
  refine ⟨fun t => Eventually.of_forall fun ω => by norm_num, fun t => by
    rw [pv_half]
    exact Eventually.of_forall fun _ => le_rfl, fun t => ?_, fun t ω => ?_, hni,
    fun B P h => hni (mEqm_bondPrice_integrable unifSystem h 0)⟩
  · cases t with
    | zero => exact (measurable_posVer.sub_const 1).stronglyMeasurable
    | succ t => exact stronglyMeasurable_const
  · cases t with
    | zero =>
      simp only [nonintRate]
      linarith [posVer_pos ω]
    | succ t =>
      simp only [nonintRate]
      norm_num

/-- Cochrane (2023), §2.1, p. 21: the debt `2ⁿ/ω` maturing at `n`. -/
noncomputable def cB (n : ℕ) (x : ℝ) : ℝ := 2 ^ n * x⁻¹

/-- Cochrane (2023), eqs. (2.3)–(2.6), p. 22, counterexample: on the uniform economy with
`β = 1/2`, `P ≡ 1`, `s ≡ 0`, `i ≡ 1` and maturing debt `2ᵗ/ω`, the derived equilibrium `MIsEqm`
holds (the transversality condition holds only because `condExp` is `0` on the non-integrable
real debt), debt and rate are adapted and `P_t/P_{t+1}` is integrable, but real debt is not
integrable and `MEquilibrium` fails: integrable real debt is needed in
`TidyR5Meas.mEquilibrium_iff_mIsEqm`. -/
theorem realDebt_integrable_needed :
    MIsEqm unifSystem (1 / 2) (GeneralLinks.debtPath (cB 0) fun t => cB (t + 1)) 0
        (fun _ _ => 1) (fun _ _ => (1 + 1)⁻¹) ∧
      StronglyAdapted unifSystem.𝓕 (fun t => cB (t + 1)) ∧
      (∀ t, Integrable (fun ω => (fun _ _ => (1 : ℝ)) t ω / (fun _ _ => (1 : ℝ)) (t + 1) ω)
        unifSystem.μ) ∧
      ¬ Integrable (fun ω => GeneralLinks.debtPath (cB 0) (fun t => cB (t + 1)) 0 ω /
        (fun _ _ => (1 : ℝ)) 0 ω) unifSystem.μ ∧
      ¬ MEquilibrium unifSystem (1 / 2) (cB 0) 0 (fun t => cB (t + 1)) (fun _ _ => 1)
        (fun _ _ => 1) := by
  have hdp : ∀ n, GeneralLinks.debtPath (cB 0) (fun t => cB (t + 1)) n = cB n := fun n => by
    cases n <;> rfl
  have hni : ∀ n, ¬ Integrable (fun ω => cB n ω / 1) unifSystem.μ := fun n h =>
    mul_inv_not_integrable (pow_ne_zero n (two_ne_zero : (2 : ℝ) ≠ 0))
      (h.congr (Eventually.of_forall fun ω => by simp [cB]))
  have hI1 : ∀ t, Integrable (fun ω => (fun (_ : ℕ) (_ : ℝ) => (1 : ℝ)) t ω /
      (fun (_ : ℕ) (_ : ℝ) => (1 : ℝ)) (t + 1) ω) unifSystem.μ := fun t =>
    (integrable_const (1 : ℝ)).congr (Eventually.of_forall fun ω => by simp)
  have hE1 : ∀ t, unifSystem.E t (fun ω => (fun _ _ => (1 : ℝ)) t ω / (fun _ _ => (1 : ℝ))
      (t + 1) ω) = fun _ => 1 := fun t => by
    have e : (fun ω => (fun (_ : ℕ) (_ : ℝ) => (1 : ℝ)) t ω / (fun (_ : ℕ) (_ : ℝ) => (1 : ℝ))
        (t + 1) ω) = fun _ => 1 := by
      funext ω
      norm_num
    rw [e, unifSystem.E_const]
  refine ⟨⟨fun t => Eventually.of_forall fun _ => one_pos, fun t => stronglyMeasurable_const,
    fun t => Eventually.of_forall fun ω => ?_, fun t => Eventually.of_forall fun ω => ?_,
    fun t => Eventually.of_forall fun ω => ?_⟩, fun t => ?_, fun t => hI1 t,
    ?_, fun h => ?_⟩
  · rw [hE1]
    simp only [Pi.smul_apply, smul_eq_mul]
    norm_num
  · rw [hdp t, hdp (t + 1)]
    simp only [cB, Pi.zero_apply, mul_zero, zero_add, pow_succ]
    ring
  · simp only [hdp]
    have hz : ∀ N, unifSystem.E t (fun ω => cB (t + N) ω / 1) = 0 := fun N =>
      condExp_of_not_integrable (hni (t + N))
    simp only [hz, Pi.zero_apply, mul_zero]
    exact tendsto_const_nhds
  · exact (show Measurable (cB (t + 1)) from
      measurable_const.mul measurable_inv).stronglyMeasurable
  · rw [hdp 0]
    exact hni 0
  · have hv := h.2.2.2.2.2.1.1
    have h0 : unifSystem.forwardSol (1 / 2) 0 0 = 0 := by
      change unifSystem.E 0 (MeasExpectationSystem.discSum (1 / 2) 0 0) = 0
      have : MeasExpectationSystem.discSum (1 / 2 : ℝ) (0 : ℕ → ℝ → ℝ) 0 = 0 := by
        funext ω
        simp [MeasExpectationSystem.discSum]
      rw [this, unifSystem.E_zero]
    rw [h0] at hv
    exact hni 0 (integrable_zero _ _ _ |>.congr hv.symm)

/-- Cochrane (2023), §2.1, p. 21: the price path `P_0 = 1`, `P_{t+1} = g(ω)`. -/
noncomputable def ppP : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | _ + 1 => posVer

/-- Cochrane (2023), eq. (2.3), p. 22: the rate `i_0 = −1`, `i_{t+1} = 1`. -/
def ppRate : ℕ → ℝ → ℝ
  | 0 => fun _ => -1
  | _ + 1 => fun _ => 1

/-- Cochrane (2023), eqs. (2.3)–(2.6), p. 22, counterexample: on the uniform economy with
`β = 1/2`, no surpluses and no debt, the price path `P_0 = 1`, `P_{t+1} = g(ω)` and the rate
`i_0 = −1`, `i_{t+1} = 1`, the derived equilibrium `MIsEqm` holds (the bond price `0 = 1/(1 + i_0)`
equals `β E_0(P_0/P_1) = 0` only because `P_0/P_1 = 1/ω` is not integrable), debt and rate are
adapted and real debt is integrable, but `P_0/P_1` is not integrable and `MEquilibrium` fails:
integrable `P_t/P_{t+1}` is needed in `TidyR5Meas.mEquilibrium_iff_mIsEqm`. -/
theorem ratio_integrable_needed :
    MIsEqm unifSystem (1 / 2) (GeneralLinks.debtPath 0 0) 0 ppP
        (fun t ω => (1 + ppRate t ω)⁻¹) ∧
      StronglyAdapted unifSystem.𝓕 ppRate ∧
      (∀ t, Integrable (fun ω => GeneralLinks.debtPath (0 : ℝ → ℝ) 0 t ω / ppP t ω)
        unifSystem.μ) ∧
      ¬ Integrable (fun ω => ppP 0 ω / ppP 1 ω) unifSystem.μ ∧
      ¬ MEquilibrium unifSystem (1 / 2) 0 0 0 ppP ppRate := by
  have hdp : ∀ n, GeneralLinks.debtPath (0 : ℝ → ℝ) (0 : ℕ → ℝ → ℝ) n = 0 := fun n => by
    cases n <;> rfl
  have hni : ¬ Integrable (fun ω => ppP 0 ω / ppP 1 ω) unifSystem.μ := fun h =>
    posVer_inv_not_integrable (h.congr (Eventually.of_forall fun ω => by
      simp [ppP]))
  refine ⟨⟨fun t => Eventually.of_forall fun ω => ?_, fun t => ?_, fun t => ?_,
    fun t => Eventually.of_forall fun ω => ?_, fun t => Eventually.of_forall fun ω => ?_⟩,
    fun t => ?_, fun t => ?_, hni, fun h => hni (h.2.2.2.2.1 0)⟩
  · cases t with
    | zero => exact one_pos
    | succ t => exact posVer_pos ω
  · cases t with
    | zero => exact stronglyMeasurable_const
    | succ t => exact measurable_posVer.stronglyMeasurable
  · cases t with
    | zero =>
      have hz : unifSystem.E 0 (fun ω => ppP 0 ω / ppP (0 + 1) ω) = 0 :=
        condExp_of_not_integrable hni
      rw [hz]
      refine Eventually.of_forall fun ω => ?_
      simp [ppRate]
    | succ t =>
      have e : (fun ω => ppP (t + 1) ω / ppP (t + 1 + 1) ω) = fun _ => 1 := by
        funext ω
        exact div_self (posVer_pos ω).ne'
      rw [e, unifSystem.E_const]
      refine Eventually.of_forall fun ω => ?_
      simp only [ppRate, Pi.smul_apply, smul_eq_mul]
      norm_num
  · rw [hdp t, hdp (t + 1)]
    simp
  · simp only [hdp, Pi.zero_apply, zero_div, unifSystem.E_const, mul_zero]
    exact tendsto_const_nhds
  · cases t with
    | zero => exact stronglyMeasurable_const
    | succ t => exact stronglyMeasurable_const
  · simp only [hdp, Pi.zero_apply, zero_div]
    exact integrable_zero _ _ _

end Uniform

end Cochrane.IntertemporalModel.TidyR6MeasHyp
