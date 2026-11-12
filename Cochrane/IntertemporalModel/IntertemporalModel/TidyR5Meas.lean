/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.HouseholdMeasureTVC
import IntertemporalModel.GeneralLinks

/-!
# The equilibrium of Chapter 2 on a genuine probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.1, pp. 21–23 (the
valuation equation (2.7), the bond price (2.3), the flow condition (2.4) and the transversality
condition (2.6)) and §2.4, pp. 29–33 (unexpected inflation (2.13), interest-rate targets,
(2.14)–(2.15)), on a probability space with a filtration (`MeasExpectationSystem`), where `E_t`
is Mathlib's conditional expectation, information may grow forever and equations hold almost
surely.

## Equilibrium notions

* `MEquilibrium` (the valuation-equation notion, `FiscalMonetary.Equilibrium` on a probability
  space): adapted price level, positive almost surely, adapted debt and rate, integrable
  `P_t/P_{t+1}` (so that `E_t(P_t/P_{t+1})` is a genuine conditional expectation), the valuation
  equation (2.7)/(2.12) almost surely at every date (`MValuation`, present value
  `E_t ∑ βʲ s_{t+j}` = `MeasExpectationSystem.forwardSol`) and the bond price (2.3) almost
  surely (`MBondPricing`). The condition `i > −1` is not part of the definition: it is a theorem
  (`mEqm_rate_gt`).
* `MIsEqm` (the derived notion, `Valuation.IsEqm` on a probability space): positive adapted price
  level, bond price (2.3), nominal flow condition (2.4) and transversality condition (2.6),
  almost surely.

## Main results

* Interest-rate targets: `mPegP`, `mPegB`; `mPeg_equilibrium` (existence for every adapted
  target `i > −1` with integrable bond price, surpluses bounded and with present value bounded
  away from zero), `mPeg_unique` (every equilibrium with that target equals it almost surely at
  every date).
* Price-level results: `mPrice_zero`, `mPrice_succ` (`P_t = B_{t−1}/PV_t` a.s.), `mDebt_eq`
  ((2.15)), `mExpected_inflation` (the target sets expected inflation), `mUnexpected_inflation`
  ((2.13): fiscal news sets unexpected inflation), `mInflation_decomposition`,
  `mNo_surprise_iff`, `mFlow` ((2.4)/(2.26)), `mEqm_rate_gt` (`i > −1` a.s., from `β > 0`).
* `mFlowTvc_iff_valuation` and `mEquilibrium_iff_mIsEqm`: the two notions agree (the measure
  version of `GeneralLinks.equilibrium_iff_isEqm`), with no `i > −1` hypothesis.

The linear model and the links to the abstract `ExpectationSystem` versions on finite trees are
in `TidyR5MeasLinear`.
-/

namespace Cochrane.IntertemporalModel.TidyR5Meas

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-! ### Present values -/

/-- Cochrane (2023), eq. (2.15), p. 31, on a probability space: the ex-dividend present value
`PVex_t = β E_t PV_{t+1}` (`= E_t ∑_{j ≥ 1} βʲ s_{t+j}`), with `PV = forwardSol`. -/
noncomputable def pvExM (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  β • S.E t (S.forwardSol β s (t + 1))

/-- Cochrane (2023), eq. (2.15), p. 31: the ex-dividend present value is known at `t`. -/
theorem pvExM_sm (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : StronglyMeasurable[S.𝓕 t] (pvExM S β s t) :=
  (S.stronglyMeasurable_E t _).const_smul β

/-- Cochrane (2023), eq. (2.7), p. 22: for `|β| < 1` and `|s| ≤ M` a.s., `|PV_t| ≤ M/(1 − |β|)`
almost surely. -/
theorem pv_bdd {β M : ℝ} (hβ : |β| < 1) {s : ℕ → Ω → ℝ} (hsM : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ M)
    (t : ℕ) : ∀ᵐ ω ∂S.μ, |S.forwardSol β s t ω| ≤ M / (1 - |β|) :=
  S.abs_E_le (S.discSum_bdd hβ hsM t) t

/-- Cochrane (2023), eq. (2.15), p. 31: a lower bound `PV ≥ c` a.s. at every date gives
`PVex_t ≥ β c` a.s. (`β ≥ 0`). -/
theorem pvExM_ge {β c : ℝ} (hβ : 0 ≤ β) {s : ℕ → Ω → ℝ}
    (hc : ∀ t, ∀ᵐ ω ∂S.μ, c ≤ S.forwardSol β s t ω) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, β * c ≤ pvExM S β s t ω := by
  have h := S.E_mono (integrable_const c) (S.integrable_E (t + 1) _) (hc (t + 1)) t
  rw [S.E_const] at h
  filter_upwards [h] with ω h
  simp only [pvExM, Pi.smul_apply, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left h hβ

/-- Cochrane (2023), eq. (2.26), p. 42, on a probability space: `PV_t = s_t + PVex_t` almost
surely (`|β| < 1`, bounded adapted surpluses). -/
theorem pv_eq_add_pvEx {β M : ℝ} (hβ : |β| < 1) {s : ℕ → Ω → ℝ} (hsad : StronglyAdapted S.𝓕 s)
    (hsM : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ M) (t : ℕ) :
    S.forwardSol β s t =ᵐ[S.μ] s t + pvExM S β s t := by
  filter_upwards [S.forwardSol_solves hβ hsad hsM t] with ω h
  rw [h, Pi.add_apply, Pi.add_apply]
  simp only [pvExM]
  ring

/-! ### The two equilibrium notions -/

/-- Cochrane (2023), eqs. (2.7) and (2.12), pp. 22, 30, on a probability space: the valuation
equation almost surely at every date, `B_{−1}/P_0 = PV_0` and `B_t/P_{t+1} = PV_{t+1}`. -/
def MValuation (β : ℝ) (Bm1 : Ω → ℝ) (s B P : ℕ → Ω → ℝ) : Prop :=
  (fun ω => Bm1 ω / P 0 ω) =ᵐ[S.μ] S.forwardSol β s 0 ∧
    ∀ t, (fun ω => B t ω / P (t + 1) ω) =ᵐ[S.μ] S.forwardSol β s (t + 1)

/-- Cochrane (2023), eqs. (2.3) and (2.14), pp. 22, 31, on a probability space: the bond price
`1/(1 + i_t) = β E_t(P_t/P_{t+1})` almost surely at every date. -/
def MBondPricing (β : ℝ) (P i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (fun ω => (1 + i t ω)⁻¹) =ᵐ[S.μ] β • S.E t (fun ω => P t ω / P (t + 1) ω)

/-- Cochrane (2023), §§2.1–2.4, pp. 21–33, on a probability space: an equilibrium given
surpluses `s` and initial debt `B_{−1}` — adapted price level positive a.s., adapted debt sold
`B`, adapted rate `i`, integrable `P_t/P_{t+1}`, the valuation equation and the bond price
(2.3) almost surely at every date. -/
def MEquilibrium (β : ℝ) (Bm1 : Ω → ℝ) (s B P i : ℕ → Ω → ℝ) : Prop :=
  StronglyAdapted S.𝓕 P ∧ (∀ t, ∀ᵐ ω ∂S.μ, 0 < P t ω) ∧ StronglyAdapted S.𝓕 B ∧
    StronglyAdapted S.𝓕 i ∧ (∀ t, Integrable (fun ω => P t ω / P (t + 1) ω) S.μ) ∧
    MValuation S β Bm1 s B P ∧ MBondPricing S β P i

/-- Cochrane (2023), §2.1, pp. 21–22, eqs. (2.3), (2.4), (2.6), on a probability space: the
derived equilibrium given maturing debt `Bm t = B_{t−1}`, surpluses and a bond price `Q` —
price level positive a.s. and adapted, `Q_t = β E_t(P_t/P_{t+1})` a.s., the nominal flow
condition `B_{t−1} = P_t s_t + Q_t B_t` a.s. and the transversality condition
`β^N E_t(B_{t+N−1}/P_{t+N}) → 0` a.s., at every date. -/
def MIsEqm (β : ℝ) (Bm s P Q : ℕ → Ω → ℝ) : Prop :=
  (∀ t, ∀ᵐ ω ∂S.μ, 0 < P t ω) ∧ StronglyAdapted S.𝓕 P ∧
    (∀ t, Q t =ᵐ[S.μ] β • S.E t (fun ω => P t ω / P (t + 1) ω)) ∧
    (∀ t, ∀ᵐ ω ∂S.μ, Bm t ω = P t ω * s t ω + Q t ω * Bm (t + 1) ω) ∧
    ∀ t, ∀ᵐ ω ∂S.μ,
      Tendsto (fun N => β ^ N * S.E t (fun ω => Bm (t + N) ω / P (t + N) ω) ω) atTop (𝓝 0)

/-! ### The bond price is positive -/

/-- Cochrane (2023), eq. (2.3), p. 22, on a probability space: in every equilibrium with
`β > 0`, the bond price is positive and `i_t > −1` almost surely at every date (no hypothesis on
`i`). -/
theorem mEqm_rate_gt {β : ℝ} (hβ : 0 < β) {Bm1 : Ω → ℝ} {s B P i : ℕ → Ω → ℝ}
    (h : MEquilibrium S β Bm1 s B P i) (t : ℕ) : ∀ᵐ ω ∂S.μ, -1 < i t ω := by
  have hpos : ∀ᵐ ω ∂S.μ, 0 < P t ω / P (t + 1) ω := by
    filter_upwards [h.2.1 t, h.2.1 (t + 1)] with ω h1 h2
    exact div_pos h1 h2
  filter_upwards [h.2.2.2.2.2.2 t, HouseholdMeasure.E_pos (h.2.2.2.2.1 t) hpos t] with ω h1 h2
  have h3 : 0 < (1 + i t ω)⁻¹ := by
    rw [h1, Pi.smul_apply, smul_eq_mul]
    exact mul_pos hβ h2
  have h4 : 0 < 1 + i t ω := inv_pos.mp h3
  linarith

/-! ### Price-level results -/

variable {β M c : ℝ} {Bm1 : Ω → ℝ} {s B P i : ℕ → Ω → ℝ}

/-- Cochrane (2023), eq. (2.7), p. 22, on a probability space: in equilibrium
`P_0 = B_{−1}/PV_0` almost surely, when `PV_0 > 0` a.s. -/
theorem mPrice_zero (h : MEquilibrium S β Bm1 s B P i)
    (hpv : ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s 0 ω) :
    P 0 =ᵐ[S.μ] fun ω => Bm1 ω / S.forwardSol β s 0 ω := by
  filter_upwards [h.2.2.2.2.2.1.1, h.2.1 0, hpv] with ω h1 h2 h3
  rw [← h1]
  have : Bm1 ω ≠ 0 := by
    intro h0
    rw [← h1, h0, zero_div] at h3
    exact lt_irrefl _ h3
  field_simp

/-- Cochrane (2023), eq. (2.12), p. 30, on a probability space: in equilibrium
`P_{t+1} = B_t/PV_{t+1}` almost surely, when `PV_{t+1} > 0` a.s. -/
theorem mPrice_succ (h : MEquilibrium S β Bm1 s B P i) (t : ℕ)
    (hpv : ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s (t + 1) ω) :
    P (t + 1) =ᵐ[S.μ] fun ω => B t ω / S.forwardSol β s (t + 1) ω := by
  filter_upwards [h.2.2.2.2.2.1.2 t, h.2.1 (t + 1), hpv] with ω h1 h2 h3
  rw [← h1]
  have : B t ω ≠ 0 := by
    intro h0
    rw [← h1, h0, zero_div] at h3
    exact lt_irrefl _ h3
  field_simp

/-- Cochrane (2023), eq. (2.15), p. 31, and p. 43, on a probability space: in equilibrium the
debt sold is `B_t = (1 + i_t) P_t PVex_t` almost surely, when `β > 0` and `PV_{t+1} > 0` a.s. -/
theorem mDebt_eq (hβ0 : 0 < β) (h : MEquilibrium S β Bm1 s B P i) (t : ℕ)
    (hpv : ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s (t + 1) ω) :
    B t =ᵐ[S.μ] fun ω => (1 + i t ω) * P t ω * pvExM S β s t ω := by
  obtain ⟨hPa, hP, hBa, -, hint, ⟨-, hv⟩, hbp⟩ := h
  set f : Ω → ℝ := fun ω => P t ω / B t ω with hf
  set g : Ω → ℝ := S.forwardSol β s (t + 1) with hg
  have hfm : StronglyMeasurable[S.𝓕 t] f :=
    ((hPa t).measurable.div (hBa t).measurable).stronglyMeasurable
  have hBpos : ∀ᵐ ω ∂S.μ, 0 < B t ω := by
    filter_upwards [hv t, hP (t + 1), hpv] with ω h1 h2 h3
    have e : B t ω = P (t + 1) ω * S.forwardSol β s (t + 1) ω := by
      have := h2.ne'
      have e1 : B t ω / P (t + 1) ω = S.forwardSol β s (t + 1) ω := h1
      field_simp at e1
      linarith
    rw [e]
    exact mul_pos h2 h3
  have hfg : (fun ω => P t ω / P (t + 1) ω) =ᵐ[S.μ] f * g := by
    filter_upwards [hv t, hP (t + 1), hBpos] with ω h1 h2 h3
    have e1 : B t ω / P (t + 1) ω = S.forwardSol β s (t + 1) ω := h1
    simp only [hf, hg, Pi.mul_apply]
    rw [← e1]
    have := h2.ne'
    have := h3.ne'
    field_simp
  have hgi : Integrable g S.μ := S.integrable_E _ _
  have hpo := condExp_mul_of_stronglyMeasurable_left hfm ((hint t).congr hfg) hgi
  have hEpos := HouseholdMeasure.E_pos hgi hpv t
  filter_upwards [hbp t, S.E_congr hfg t, hpo, hBpos, hP t, hEpos] with ω h1 h2 h3 h4 h5 h6
  have e : (1 + i t ω)⁻¹ = f ω * pvExM S β s t ω := by
    rw [h1, Pi.smul_apply, smul_eq_mul, h2]
    have h3' : S.E t (f * g) ω = f ω * S.E t g ω := h3
    rw [h3']
    simp only [pvExM, Pi.smul_apply, smul_eq_mul, hg]
    ring
  have hpe : 0 < pvExM S β s t ω := by
    simp only [pvExM, Pi.smul_apply, smul_eq_mul]
    exact mul_pos hβ0 h6
  have hpos : 0 < (1 + i t ω)⁻¹ := by
    rw [e]
    exact mul_pos (div_pos h5 h4) hpe
  have hne : 1 + i t ω ≠ 0 := (inv_pos.mp hpos).ne'
  simp only [hf] at e
  have := h4.ne'
  field_simp at e
  linear_combination e

/-- Cochrane (2023), p. 32, bullet "the nominal interest-rate target determines expected
inflation", on a probability space: in every equilibrium `E_t(P_t/P_{t+1}) = 1/(β(1 + i_t))`
almost surely (`β ≠ 0`). -/
theorem mExpected_inflation (hβ : β ≠ 0) (h : MEquilibrium S β Bm1 s B P i) (t : ℕ) :
    S.E t (fun ω => P t ω / P (t + 1) ω) =ᵐ[S.μ] fun ω => β⁻¹ * (1 + i t ω)⁻¹ := by
  filter_upwards [h.2.2.2.2.2.2 t] with ω h1
  rw [h1, Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hβ, one_mul]

/-- Cochrane (2023), eq. (2.13), p. 30, **unexpected inflation** on a probability space: in
every equilibrium, `(B_t/P_t) ΔE_{t+1}(P_t/P_{t+1}) = ΔE_{t+1} PV_{t+1}` almost surely. -/
theorem mUnexpected_inflation (h : MEquilibrium S β Bm1 s B P i) (t : ℕ) :
    (fun ω => B t ω / P t ω * S.innov t (fun ω => P t ω / P (t + 1) ω) ω) =ᵐ[S.μ]
      S.innov t (S.forwardSol β s (t + 1)) := by
  obtain ⟨hPa, hP, hBa, -, hint, ⟨-, hv⟩, -⟩ := h
  set f : Ω → ℝ := fun ω => B t ω / P t ω with hf
  set g : Ω → ℝ := fun ω => P t ω / P (t + 1) ω with hg
  have hfm : StronglyMeasurable[S.𝓕 t] f :=
    ((hBa t).measurable.div (hPa t).measurable).stronglyMeasurable
  have hfm1 : StronglyMeasurable[S.𝓕 (t + 1)] f := hfm.mono (S.𝓕.mono (Nat.le_succ t))
  have hfg : f * g =ᵐ[S.μ] S.forwardSol β s (t + 1) := by
    filter_upwards [hv t, hP t] with ω h1 h2
    rw [← h1]
    simp only [hf, hg, Pi.mul_apply]
    have := h2.ne'
    field_simp
  have hfgi : Integrable (f * g) S.μ := (S.integrable_E _ _).congr hfg.symm
  have hpo0 := condExp_mul_of_stronglyMeasurable_left hfm hfgi (hint t)
  have hpo1 := condExp_mul_of_stronglyMeasurable_left hfm1 hfgi (hint t)
  filter_upwards [hpo0, hpo1, S.E_congr hfg t, S.E_congr hfg (t + 1)] with ω h0 h1 h2 h3
  have h0' : S.E t (f * g) ω = f ω * S.E t g ω := h0
  have h1' : S.E (t + 1) (f * g) ω = f ω * S.E (t + 1) g ω := h1
  simp only [MeasExpectationSystem.innov, Pi.sub_apply]
  rw [← h2, ← h3, h0', h1']
  ring

/-- Cochrane (2023), p. 33, bullet "monetary policy ... determines expected inflation ...
fiscal policy determines unexpected inflation", on a probability space: in every equilibrium
`P_t/P_{t+1} = 1/(β(1 + i_t)) + ΔE_{t+1} PV_{t+1}/(B_t/P_t)` almost surely, where `B_t ≠ 0`
(`β ≠ 0`). -/
theorem mInflation_decomposition (hβ0 : β ≠ 0) (h : MEquilibrium S β Bm1 s B P i) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, B t ω ≠ 0 → P t ω / P (t + 1) ω =
      β⁻¹ * (1 + i t ω)⁻¹ + S.innov t (S.forwardSol β s (t + 1)) ω / (B t ω / P t ω) := by
  have hm : StronglyMeasurable[S.𝓕 (t + 1)] (fun ω => P t ω / P (t + 1) ω) :=
    (((h.1 t).mono (S.𝓕.mono (Nat.le_succ t))).measurable.div
      (h.1 (t + 1)).measurable).stronglyMeasurable
  have e := S.eq_E_add_innov hm (h.2.2.2.2.1 t)
  filter_upwards [mExpected_inflation S hβ0 h t, mUnexpected_inflation S h t, h.2.1 t]
    with ω h1 h2 h3 hB
  have e' := congrFun e ω
  rw [Pi.add_apply, h1] at e'
  rw [e', ← h2]
  have := h3.ne'
  field_simp

/-- Cochrane (2023), p. 30, bullet "unexpected inflation is determined entirely by changing
expectations of the present value of fiscal surpluses", on a probability space: almost surely,
where debt is outstanding (`B_t ≠ 0`), unexpected inflation is zero exactly when the
present-value news is zero. -/
theorem mNo_surprise_iff (h : MEquilibrium S β Bm1 s B P i) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, B t ω ≠ 0 → (S.innov t (fun ω => P t ω / P (t + 1) ω) ω = 0 ↔
      S.innov t (S.forwardSol β s (t + 1)) ω = 0) := by
  filter_upwards [mUnexpected_inflation S h t, h.2.1 t] with ω h1 h2 hB
  rw [← h1]
  have hV : B t ω / P t ω ≠ 0 := div_ne_zero hB h2.ne'
  constructor
  · intro h0
    rw [h0, mul_zero]
  · intro h0
    exact (mul_eq_zero.mp h0).resolve_left hV

/-- Cochrane (2023), eqs. (2.4) and (2.26), pp. 22, 42, on a probability space: in every
equilibrium the flow condition `B_t/P_{t+1} = s_{t+1} + (B_{t+1}/P_{t+1})/(1 + i_{t+1})` holds
almost surely (bounded adapted surpluses, `0 < β < 1`, `PV > 0` a.s.). -/
theorem mFlow (hβ0 : 0 < β) (hβ1 : β < 1) (hsad : StronglyAdapted S.𝓕 s)
    (hsM : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ M) (h : MEquilibrium S β Bm1 s B P i)
    (hpv : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s t ω) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, B t ω / P (t + 1) ω =
      s (t + 1) ω + B (t + 1) ω / P (t + 1) ω * (1 + i (t + 1) ω)⁻¹ := by
  have hβ : |β| < 1 := by rwa [abs_of_pos hβ0]
  filter_upwards [h.2.2.2.2.2.1.2 t, pv_eq_add_pvEx S hβ hsad hsM (t + 1),
    mDebt_eq S hβ0 h (t + 1) (hpv (t + 2)), h.2.1 (t + 1),
    mEqm_rate_gt S hβ0 h (t + 1)] with ω h1 h2 h3 h4 h5
  have e1 : B t ω / P (t + 1) ω = S.forwardSol β s (t + 1) ω := h1
  rw [e1, h2, Pi.add_apply, h3]
  have := h4.ne'
  have : 1 + i (t + 1) ω ≠ 0 := by linarith
  field_simp

/-! ### Interest-rate targets: existence and uniqueness -/

/-- Cochrane (2023), §2.4.3, p. 31, on a probability space: the price level of the
interest-rate-target equilibrium, `P_0 = B_{−1}/PV_0`,
`P_{t+1} = (1 + i_t) P_t PVex_t/PV_{t+1}`. -/
noncomputable def mPegP (β : ℝ) (Bm1 : Ω → ℝ) (s i : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun ω => Bm1 ω / S.forwardSol β s 0 ω
  | t + 1 => fun ω => (1 + i t ω) * mPegP β Bm1 s i t ω * pvExM S β s t ω /
      S.forwardSol β s (t + 1) ω

/-- Cochrane (2023), eq. (2.15), p. 31, on a probability space: the debt sold at the target,
`B_t = (1 + i_t) P_t PVex_t`. -/
noncomputable def mPegB (β : ℝ) (Bm1 : Ω → ℝ) (s i : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (1 + i t ω) * mPegP S β Bm1 s i t ω * pvExM S β s t ω

/-- Cochrane (2023), §2.4.3, p. 31: the target price level is adapted. -/
theorem mPegP_sm (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1) (hia : StronglyAdapted S.𝓕 i)
    (t : ℕ) : StronglyMeasurable[S.𝓕 t] (mPegP S β Bm1 s i t) := by
  induction t with
  | zero =>
    exact (hBm1.measurable.div (S.forwardSol_adapted β s 0).measurable).stronglyMeasurable
  | succ t ih =>
    have hmono : S.𝓕 t ≤ S.𝓕 (t + 1) := S.𝓕.mono (Nat.le_succ t)
    exact (((((hia t).mono hmono).measurable.const_add 1).mul (ih.mono hmono).measurable).mul
      ((pvExM_sm S β s t).mono hmono).measurable).div
      (S.forwardSol_adapted β s (t + 1)).measurable |>.stronglyMeasurable

/-- Cochrane (2023), eq. (2.15), p. 31: the target debt is adapted. -/
theorem mPegB_sm (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1) (hia : StronglyAdapted S.𝓕 i)
    (t : ℕ) : StronglyMeasurable[S.𝓕 t] (mPegB S β Bm1 s i t) :=
  ((((hia t).measurable.const_add 1).mul (mPegP_sm S hBm1 hia t).measurable).mul
    (pvExM_sm S β s t).measurable).stronglyMeasurable

/-- Cochrane (2023), §2.4.3, p. 31: with `β > 0`, positive initial debt, a target `i > −1` and
present values bounded below by `c > 0`, the target price level is positive almost surely. -/
theorem mPegP_pos (hβ0 : 0 < β) (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω) (hi : ∀ t ω, -1 < i t ω)
    (hc0 : 0 < c) (hc : ∀ t, ∀ᵐ ω ∂S.μ, c ≤ S.forwardSol β s t ω) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, 0 < mPegP S β Bm1 s i t ω := by
  induction t with
  | zero =>
    filter_upwards [hB, hc 0] with ω h1 h2
    exact div_pos h1 (lt_of_lt_of_le hc0 h2)
  | succ t ih =>
    filter_upwards [ih, pvExM_ge S hβ0.le hc t, hc (t + 1)] with ω h1 h2 h3
    change 0 < (1 + i t ω) * mPegP S β Bm1 s i t ω * pvExM S β s t ω /
      S.forwardSol β s (t + 1) ω
    have h4 : 0 < 1 + i t ω := by linarith [hi t ω]
    have h5 : 0 < pvExM S β s t ω := lt_of_lt_of_le (mul_pos hβ0 hc0) h2
    have h6 : 0 < S.forwardSol β s (t + 1) ω := lt_of_lt_of_le hc0 h3
    positivity

/-- Cochrane (2023), bullets pp. 31–33, "the government can target nominal interest rates", on a
probability space: for `0 < β < 1`, surpluses bounded a.s. with present value bounded below by
`c > 0` a.s., positive initial debt known at `0`, and every adapted target `i > −1` whose bond
price `1/(1 + i_t)` is integrable, the target path `(mPegP, mPegB)` is an equilibrium. -/
theorem mPeg_equilibrium (hβ0 : 0 < β) (hβ1 : β < 1) (hsM : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ M)
    (hc0 : 0 < c) (hc : ∀ t, ∀ᵐ ω ∂S.μ, c ≤ S.forwardSol β s t ω)
    (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1) (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω)
    (hia : StronglyAdapted S.𝓕 i) (hi : ∀ t ω, -1 < i t ω)
    (hQi : ∀ t, Integrable (fun ω => (1 + i t ω)⁻¹) S.μ) :
    MEquilibrium S β Bm1 s (mPegB S β Bm1 s i) (mPegP S β Bm1 s i) i := by
  have ha : |β| < 1 := by rwa [abs_of_pos hβ0]
  have hPpos := mPegP_pos S hβ0 hB hi hc0 hc
  have hpe := pvExM_ge S hβ0.le hc
  have hBpos : ∀ t, ∀ᵐ ω ∂S.μ, 0 < mPegB S β Bm1 s i t ω := fun t => by
    filter_upwards [hPpos t, hpe t] with ω h1 h2
    change 0 < (1 + i t ω) * mPegP S β Bm1 s i t ω * pvExM S β s t ω
    have h4 : 0 < 1 + i t ω := by linarith [hi t ω]
    have h5 : 0 < pvExM S β s t ω := lt_of_lt_of_le (mul_pos hβ0 hc0) h2
    positivity
  have hratio : ∀ t, (fun ω => mPegP S β Bm1 s i t ω / mPegP S β Bm1 s i (t + 1) ω) =ᵐ[S.μ]
      fun ω => (1 + i t ω)⁻¹ * (S.forwardSol β s (t + 1) ω / pvExM S β s t ω) := fun t => by
    filter_upwards [hPpos t, hpe t, hc (t + 1)] with ω h1 h2 h3
    change mPegP S β Bm1 s i t ω / ((1 + i t ω) * mPegP S β Bm1 s i t ω * pvExM S β s t ω /
      S.forwardSol β s (t + 1) ω) = _
    have h4 : 1 + i t ω ≠ 0 := by linarith [hi t ω]
    have h5 : pvExM S β s t ω ≠ 0 := (lt_of_lt_of_le (mul_pos hβ0 hc0) h2).ne'
    have h6 : S.forwardSol β s (t + 1) ω ≠ 0 := (lt_of_lt_of_le hc0 h3).ne'
    have h7 := h1.ne'
    field_simp
  have hint : ∀ t, Integrable
      (fun ω => mPegP S β Bm1 s i t ω / mPegP S β Bm1 s i (t + 1) ω) S.μ := fun t => by
    refine Integrable.congr ?_ (hratio t).symm
    refine (hQi t).mul_bdd (c := M / (1 - |β|) / (β * c)) ?_ ?_
    · exact ((((S.forwardSol_adapted β s (t + 1)).mono (S.𝓕.le (t + 1))).measurable.div
        ((pvExM_sm S β s t).mono (S.𝓕.le t)).measurable)).aestronglyMeasurable
    · filter_upwards [pv_bdd S ha hsM (t + 1), hpe t] with ω h1 h2
      have h5 : 0 < pvExM S β s t ω := lt_of_lt_of_le (mul_pos hβ0 hc0) h2
      rw [Real.norm_eq_abs, abs_div, abs_of_pos h5]
      exact div_le_div₀ ((abs_nonneg _).trans h1) h1 (mul_pos hβ0 hc0) h2
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
      ((((hia t).measurable.const_add 1).mul (pvExM_sm S β s t).measurable).inv).stronglyMeasurable
    have hr2 : (fun ω => mPegP S β Bm1 s i t ω / mPegP S β Bm1 s i (t + 1) ω) =ᵐ[S.μ]
        cc * S.forwardSol β s (t + 1) := by
      filter_upwards [hratio t] with ω h
      rw [h]
      simp only [hcc, Pi.mul_apply, mul_inv]
      ring
    have hpo := condExp_mul_of_stronglyMeasurable_left hccm ((hint t).congr hr2)
      (S.integrable_E (t + 1) _)
    filter_upwards [S.E_congr hr2 t, hpo, hpe t] with ω h1 h2 h3
    rw [Pi.smul_apply, smul_eq_mul, h1]
    have h2' : S.E t (cc * S.forwardSol β s (t + 1)) ω =
        cc ω * S.E t (S.forwardSol β s (t + 1)) ω := h2
    rw [h2']
    have h5 : 0 < pvExM S β s t ω := lt_of_lt_of_le (mul_pos hβ0 hc0) h3
    have e : pvExM S β s t ω = β * S.E t (S.forwardSol β s (t + 1)) ω := rfl
    have h4 : 1 + i t ω ≠ 0 := by linarith [hi t ω]
    rw [e] at h5
    simp only [hcc, e]
    have hE : S.E t (S.forwardSol β s (t + 1)) ω ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h5
      exact lt_irrefl _ h5
    have := h5.ne'
    field_simp

/-- Cochrane (2023), bullet p. 33, "inflation can be stable and determinate under an interest
rate target", on a probability space: with `β > 0` and present values bounded below by `c > 0`,
every equilibrium with the target `i` is the target path, almost surely at every date. -/
theorem mPeg_unique (hβ0 : 0 < β) (hc0 : 0 < c) (hc : ∀ t, ∀ᵐ ω ∂S.μ, c ≤ S.forwardSol β s t ω)
    (h : MEquilibrium S β Bm1 s B P i) (t : ℕ) :
    P t =ᵐ[S.μ] mPegP S β Bm1 s i t ∧ B t =ᵐ[S.μ] mPegB S β Bm1 s i t := by
  have hpv : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β s t ω := fun t =>
    (hc t).mono fun ω h => lt_of_lt_of_le hc0 h
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

/-- Cochrane (2023), §§2.4.3–2.4.4, pp. 31–33, on a probability space: **existence and
uniqueness under an interest-rate target** (time-varying, state-contingent `i`): under the
hypotheses of `mPeg_equilibrium` there is an equilibrium, and every equilibrium with the target
equals it almost surely at every date. -/
theorem mPeg_existsUnique (hβ0 : 0 < β) (hβ1 : β < 1) (hsM : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ M)
    (hc0 : 0 < c) (hc : ∀ t, ∀ᵐ ω ∂S.μ, c ≤ S.forwardSol β s t ω)
    (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1) (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω)
    (hia : StronglyAdapted S.𝓕 i) (hi : ∀ t ω, -1 < i t ω)
    (hQi : ∀ t, Integrable (fun ω => (1 + i t ω)⁻¹) S.μ) :
    ∃ x : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), MEquilibrium S β Bm1 s x.2 x.1 i ∧
      ∀ y : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), MEquilibrium S β Bm1 s y.2 y.1 i →
        ∀ t, y.1 t =ᵐ[S.μ] x.1 t ∧ y.2 t =ᵐ[S.μ] x.2 t :=
  ⟨(mPegP S β Bm1 s i, mPegB S β Bm1 s i),
    mPeg_equilibrium S hβ0 hβ1 hsM hc0 hc hBm1 hB hia hi hQi,
    fun _ hy t => mPeg_unique S hβ0 hc0 hc hy t⟩

/-! ### The derived equilibrium: flow plus transversality is the valuation equation -/

/-- Cochrane (2023), eqs. (2.3)–(2.4), p. 22, on a probability space: with the bond price (2.3)
`Q_t = β E_t(P_t/P_{t+1})` a.s., debt sold at `t` known at `t`, positive prices and integrable
`P_t/P_{t+1}` and real debt, the real value of the debt carried out of date `t` is
`Q_t B_t/P_t = β E_t(B_t/P_{t+1})` almost surely. -/
theorem endDebt {Bm Q : ℕ → Ω → ℝ} (hPa : StronglyAdapted S.𝓕 P)
    (hBm : ∀ t, StronglyMeasurable[S.𝓕 t] (Bm (t + 1))) (hP : ∀ t, ∀ᵐ ω ∂S.μ, 0 < P t ω)
    (hQ : ∀ t, Q t =ᵐ[S.μ] β • S.E t (fun ω => P t ω / P (t + 1) ω))
    (hPP : ∀ t, Integrable (fun ω => P t ω / P (t + 1) ω) S.μ)
    (hx : ∀ t, Integrable (fun ω => Bm t ω / P t ω) S.μ) (t : ℕ) :
    (fun ω => Q t ω * Bm (t + 1) ω / P t ω) =ᵐ[S.μ]
      β • S.E t (fun ω => Bm (t + 1) ω / P (t + 1) ω) := by
  set f : Ω → ℝ := fun ω => Bm (t + 1) ω / P t ω with hfdef
  set g : Ω → ℝ := fun ω => P t ω / P (t + 1) ω with hgdef
  have hfm : StronglyMeasurable[S.𝓕 t] f :=
    ((hBm t).measurable.div (hPa t).measurable).stronglyMeasurable
  have hfg : f * g =ᵐ[S.μ] fun ω => Bm (t + 1) ω / P (t + 1) ω := by
    filter_upwards [hP t] with ω hp
    have := hp.ne'
    simp only [hfdef, hgdef, Pi.mul_apply]
    field_simp
  have hpo := condExp_mul_of_stronglyMeasurable_left hfm ((hx (t + 1)).congr hfg.symm) (hPP t)
  filter_upwards [hQ t, hpo, S.E_congr hfg t] with ω hq h2 h3
  have h2' : S.E t (f * g) ω = f ω * S.E t g ω := h2
  rw [Pi.smul_apply, smul_eq_mul, ← h3, h2', hq, Pi.smul_apply, smul_eq_mul]
  simp only [hfdef]
  ring

/-- Cochrane (2023), eqs. (2.4)–(2.5), p. 22, on a probability space: under the hypotheses of
`endDebt`, the nominal flow condition `B_{t−1} = P_t s_t + Q_t B_t` a.s. at every date is the
real flow condition `x_t = s_t + β E_t x_{t+1}` a.s. at every date, `x_t = B_{t−1}/P_t`. -/
theorem nominal_iff_real {Bm Q : ℕ → Ω → ℝ} (hPa : StronglyAdapted S.𝓕 P)
    (hBm : ∀ t, StronglyMeasurable[S.𝓕 t] (Bm (t + 1))) (hP : ∀ t, ∀ᵐ ω ∂S.μ, 0 < P t ω)
    (hQ : ∀ t, Q t =ᵐ[S.μ] β • S.E t (fun ω => P t ω / P (t + 1) ω))
    (hPP : ∀ t, Integrable (fun ω => P t ω / P (t + 1) ω) S.μ)
    (hx : ∀ t, Integrable (fun ω => Bm t ω / P t ω) S.μ) :
    (∀ t, ∀ᵐ ω ∂S.μ, Bm t ω = P t ω * s t ω + Q t ω * Bm (t + 1) ω) ↔
      ∀ t, (fun ω => Bm t ω / P t ω) =ᵐ[S.μ]
        s t + β • S.E t (fun ω => Bm (t + 1) ω / P (t + 1) ω) := by
  constructor
  · intro h t
    filter_upwards [h t, hP t, endDebt S hPa hBm hP hQ hPP hx t] with ω h1 hp h2
    rw [Pi.add_apply, ← h2, h1]
    have := hp.ne'
    field_simp
  · intro h t
    filter_upwards [h t, hP t, endDebt S hPa hBm hP hQ hPP hx t] with ω h1 hp h2
    have h1' : Bm t ω / P t ω = s t ω + (β • S.E t (fun ω => Bm (t + 1) ω / P (t + 1) ω)) ω :=
      h1
    have h2' : Q t ω * Bm (t + 1) ω / P t ω =
        (β • S.E t (fun ω => Bm (t + 1) ω / P (t + 1) ω)) ω := h2
    rw [← h2'] at h1'
    have := hp.ne'
    field_simp at h1'
    linarith

/-- Cochrane (2023), eqs. (2.4)–(2.7), p. 22, on a probability space with information growing
forever, **both directions**: for `0 < β < 1`, adapted surpluses bounded a.s., positive adapted
prices, the bond price (2.3) a.s., debt sold at `t` known at `t`, and integrable `P_t/P_{t+1}`
and real debt `x_t = B_{t−1}/P_t`, the nominal flow condition (2.4) and the transversality
condition (2.6) hold a.s. at every date iff the valuation equation (2.7) `x_t = PV_t` holds a.s.
at every date. -/
theorem mFlowTvc_iff_valuation (hβ0 : 0 < β) (hβ1 : β < 1) (hsad : StronglyAdapted S.𝓕 s)
    (hsM : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ M) {Bm Q : ℕ → Ω → ℝ} (hPa : StronglyAdapted S.𝓕 P)
    (hBm : ∀ t, StronglyMeasurable[S.𝓕 t] (Bm (t + 1))) (hP : ∀ t, ∀ᵐ ω ∂S.μ, 0 < P t ω)
    (hQ : ∀ t, Q t =ᵐ[S.μ] β • S.E t (fun ω => P t ω / P (t + 1) ω))
    (hPP : ∀ t, Integrable (fun ω => P t ω / P (t + 1) ω) S.μ)
    (hx : ∀ t, Integrable (fun ω => Bm t ω / P t ω) S.μ) :
    ((∀ t, ∀ᵐ ω ∂S.μ, Bm t ω = P t ω * s t ω + Q t ω * Bm (t + 1) ω) ∧
      ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun N => β ^ N * S.E t (fun ω => Bm (t + N) ω / P (t + N) ω) ω)
        atTop (𝓝 0)) ↔
      ∀ t, (fun ω => Bm t ω / P t ω) =ᵐ[S.μ] S.forwardSol β s t := by
  have ha : |β| < 1 := by rwa [abs_of_pos hβ0]
  have hsm : ∀ n, AEStronglyMeasurable (s n) S.μ := fun n =>
    ((hsad n).mono (S.𝓕.le n)).aestronglyMeasurable
  have hsi : ∀ n, Integrable (s n) S.μ := fun n =>
    MeasExpectationSystem.BddRV.integrable ⟨hsm n, M, hsM n⟩
  rw [nominal_iff_real S hPa hBm hP hQ hPP hx]
  constructor
  · rintro ⟨hflow, htvc⟩ t
    have htel := ae_all_iff.2 (HouseholdMeasureTVC.telescope_ae hflow hsad hsi t)
    filter_upwards [htel, htvc t, S.forwardSol_hasSum ha hsm hsM t] with ω h1 h2 h3
    have hlim1 : Tendsto (fun N => ∑ j ∈ Finset.range (N + 1), β ^ j * S.E t (s (t + j)) ω)
        atTop (𝓝 (S.forwardSol β s t ω)) :=
      h3.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    have h2' : Tendsto (fun N => β ^ (N + 1) *
        S.E t (fun ω => Bm (t + N + 1) ω / P (t + N + 1) ω) ω) atTop (𝓝 0) :=
      h2.comp (tendsto_add_atTop_nat 1)
    have hlim2 : Tendsto (fun N => ∑ j ∈ Finset.range (N + 1), β ^ j * S.E t (s (t + j)) ω)
        atTop (𝓝 (Bm t ω / P t ω)) := by
      have e : ∀ N, ∑ j ∈ Finset.range (N + 1), β ^ j * S.E t (s (t + j)) ω =
          Bm t ω / P t ω - β ^ (N + 1) *
            S.E t (fun ω => Bm (t + N + 1) ω / P (t + N + 1) ω) ω := fun N => by
        rw [h1 N]
        ring
      simp_rw [e]
      simpa using (tendsto_const_nhds (x := Bm t ω / P t ω)).sub h2'
    exact tendsto_nhds_unique hlim2 hlim1
  · intro hv
    have hflow : ∀ t, (fun ω => Bm t ω / P t ω) =ᵐ[S.μ]
        s t + β • S.E t (fun ω => Bm (t + 1) ω / P (t + 1) ω) := fun t => by
      filter_upwards [hv t, S.forwardSol_solves ha hsad hsM t, S.E_congr (hv (t + 1)) t]
        with ω h1 h2 h3
      rw [h1, h2, Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
        smul_eq_mul, h3]
      ring
    refine ⟨hflow, fun t => ?_⟩
    have hE : ∀ᵐ ω ∂S.μ, ∀ N,
        S.E t (fun ω => Bm (t + N) ω / P (t + N) ω) ω = S.E t (S.forwardSol β s (t + N)) ω ∧
          |S.E t (S.forwardSol β s (t + N)) ω| ≤ M / (1 - |β|) :=
      ae_all_iff.2 fun N => by
        filter_upwards [S.E_congr (hv (t + N)) t,
          S.abs_E_le (pv_bdd S ha hsM (t + N)) t] with ω h1 h2
        exact ⟨h1, h2⟩
    filter_upwards [hE] with ω h
    have hb : Tendsto (fun N : ℕ => β ^ N * (M / (1 - |β|))) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (M / (1 - |β|))
    refine squeeze_zero_norm (fun N => ?_) hb
    have hbN : |β| ^ N = β ^ N := by rw [abs_of_pos hβ0]
    rw [Real.norm_eq_abs, abs_mul, abs_pow, hbN, (h N).1]
    exact mul_le_mul_of_nonneg_left (h N).2 (pow_nonneg hβ0.le N)

/-- Cochrane (2023), §§2.1–2.4, pp. 21–33, on a probability space: **the two equilibrium notions
agree** (the measure version of `GeneralLinks.equilibrium_iff_isEqm`, with no hypothesis
`i > −1`). For `0 < β < 1`, adapted surpluses bounded a.s., adapted debt and rate, integrable
`P_t/P_{t+1}` and integrable real debt, `MEquilibrium` holds iff `MIsEqm` holds with maturing
debt `GeneralLinks.debtPath B_{−1} B` and bond price `1/(1 + i)`, together with the adaptedness
of `P`. -/
theorem mEquilibrium_iff_mIsEqm (hβ0 : 0 < β) (hβ1 : β < 1) (hsad : StronglyAdapted S.𝓕 s)
    (hsM : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ M) (hBa : StronglyAdapted S.𝓕 B)
    (hia : StronglyAdapted S.𝓕 i) (hPP : ∀ t, Integrable (fun ω => P t ω / P (t + 1) ω) S.μ)
    (hx : ∀ t, Integrable (fun ω => GeneralLinks.debtPath Bm1 B t ω / P t ω) S.μ) :
    MEquilibrium S β Bm1 s B P i ↔
      MIsEqm S β (GeneralLinks.debtPath Bm1 B) s P (fun t ω => (1 + i t ω)⁻¹) := by
  have hBm : ∀ t, StronglyMeasurable[S.𝓕 t] (GeneralLinks.debtPath Bm1 B (t + 1)) := hBa
  constructor
  · rintro ⟨hPa, hP, -, -, -, ⟨hv0, hv⟩, hbp⟩
    have hval : ∀ t, (fun ω => GeneralLinks.debtPath Bm1 B t ω / P t ω) =ᵐ[S.μ]
        S.forwardSol β s t := fun t => by
      cases t with
      | zero => exact hv0
      | succ t => exact hv t
    obtain ⟨hflow, htvc⟩ := (mFlowTvc_iff_valuation S hβ0 hβ1 hsad hsM hPa hBm hP hbp hPP hx).mpr
      hval
    exact ⟨hP, hPa, hbp, hflow, htvc⟩
  · rintro ⟨hP, hPa, hbp, hflow, htvc⟩
    have hval := (mFlowTvc_iff_valuation S hβ0 hβ1 hsad hsM hPa hBm hP hbp hPP hx).mp
      ⟨hflow, htvc⟩
    exact ⟨hPa, hP, hBa, hia, hPP, ⟨hval 0, fun t => hval (t + 1)⟩, hbp⟩

/-- Cochrane (2023), eq. (2.7), p. 22, on a probability space: in every derived equilibrium
(`MIsEqm`) with positive debt and present values a.s., the price level is `P_t = B_{t−1}/PV_t`
almost surely at every date (hypotheses of `mFlowTvc_iff_valuation`). -/
theorem mIsEqm_price_eq (hβ0 : 0 < β) (hβ1 : β < 1) (hsad : StronglyAdapted S.𝓕 s)
    (hsM : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ M) {Bm Q : ℕ → Ω → ℝ}
    (hBm : ∀ t, StronglyMeasurable[S.𝓕 t] (Bm (t + 1)))
    (hPP : ∀ t, Integrable (fun ω => P t ω / P (t + 1) ω) S.μ)
    (hx : ∀ t, Integrable (fun ω => Bm t ω / P t ω) S.μ) (h : MIsEqm S β Bm s P Q)
    (hBpos : ∀ t, ∀ᵐ ω ∂S.μ, 0 < Bm t ω) (t : ℕ) :
    P t =ᵐ[S.μ] fun ω => Bm t ω / S.forwardSol β s t ω := by
  obtain ⟨hP, hPa, hQ, hflow, htvc⟩ := h
  have hval := (mFlowTvc_iff_valuation S hβ0 hβ1 hsad hsM hPa hBm hP hQ hPP hx).mp
    ⟨hflow, htvc⟩
  filter_upwards [hval t, hP t, hBpos t] with ω h1 h2 h3
  rw [← h1]
  have := h2.ne'
  have := h3.ne'
  field_simp

/-- Cochrane (2023), pp. 31–33, in the language of the derived equilibrium on a probability
space: under the hypotheses of `mPeg_equilibrium` (with adapted surpluses), the target path is
a derived equilibrium (`MIsEqm`, maturing debt `GeneralLinks.debtPath B_{−1} (mPegB)`, bond price
`1/(1 + i)`), and every derived equilibrium with that bond price, adapted debt sold, integrable
`P_t/P_{t+1}` and integrable real debt equals it almost surely at every date. -/
theorem mPeg_existsUnique_mIsEqm (hβ0 : 0 < β) (hβ1 : β < 1) (hsad : StronglyAdapted S.𝓕 s)
    (hsM : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ M) (hc0 : 0 < c)
    (hc : ∀ t, ∀ᵐ ω ∂S.μ, c ≤ S.forwardSol β s t ω) (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1)
    (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω) (hia : StronglyAdapted S.𝓕 i) (hi : ∀ t ω, -1 < i t ω)
    (hQi : ∀ t, Integrable (fun ω => (1 + i t ω)⁻¹) S.μ) :
    MIsEqm S β (GeneralLinks.debtPath Bm1 (mPegB S β Bm1 s i)) s (mPegP S β Bm1 s i)
      (fun t ω => (1 + i t ω)⁻¹) ∧
    ∀ B' P' : ℕ → Ω → ℝ, StronglyAdapted S.𝓕 B' →
      (∀ t, Integrable (fun ω => P' t ω / P' (t + 1) ω) S.μ) →
      (∀ t, Integrable (fun ω => GeneralLinks.debtPath Bm1 B' t ω / P' t ω) S.μ) →
      MIsEqm S β (GeneralLinks.debtPath Bm1 B') s P' (fun t ω => (1 + i t ω)⁻¹) →
        ∀ t, P' t =ᵐ[S.μ] mPegP S β Bm1 s i t ∧ B' t =ᵐ[S.μ] mPegB S β Bm1 s i t := by
  have hE := mPeg_equilibrium S hβ0 hβ1 hsM hc0 hc hBm1 hB hia hi hQi
  have hx : ∀ t, Integrable
      (fun ω => GeneralLinks.debtPath Bm1 (mPegB S β Bm1 s i) t ω / mPegP S β Bm1 s i t ω)
      S.μ := fun t => by
    refine (S.integrable_E t (MeasExpectationSystem.discSum β s t)).congr ?_
    cases t with
    | zero => exact hE.2.2.2.2.2.1.1.symm
    | succ t => exact (hE.2.2.2.2.2.1.2 t).symm
  refine ⟨(mEquilibrium_iff_mIsEqm S hβ0 hβ1 hsad hsM hE.2.2.1 hia hE.2.2.2.2.1 hx).mp hE,
    fun B' P' hB'a hPP' hx' h' t => ?_⟩
  exact mPeg_unique S hβ0 hc0 hc
    ((mEquilibrium_iff_mIsEqm S hβ0 hβ1 hsad hsM hB'a hia hPP' hx').mpr h') t

end Cochrane.IntertemporalModel.TidyR5Meas
