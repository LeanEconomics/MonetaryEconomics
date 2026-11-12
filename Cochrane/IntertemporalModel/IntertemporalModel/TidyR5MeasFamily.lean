/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.TidyR5MeasLinear
import IntertemporalModel.TidyR5Family
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# The family of exact equilibria on a genuine probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.4, pp. 29–33, and §2.5,
pp. 34–37: the family of exact nonlinear equilibria of `TidyR5Family` (surpluses
`s_t(ε) = s̄ + ε ŝ_t`, a rate family `i(ε)`, canonically `1 + i_t(ε) = β⁻¹ exp(ε î_t)`,
`TidyR5Family.rateExp`) on a probability space with
Mathlib's conditional expectation, where information may grow forever and no history need have
positive probability.

The family is written with one fixed version of the present values of `ŝ`
(`MeasExpectationSystem.forwardSol` and `TidyR5Meas.pvExM`): `pvAff`, `pvExAff`, `mFamP`,
`mFamB`. For each `ε` it is an equilibrium in the sense of `TidyR5Meas.MEquilibrium`, and as a
function of `ε` it is smooth in almost every state, so it can be differentiated state by
state.

## Main results

* `forwardSol_surpFam`, `pvExM_surpFam`: present values of `s(ε)` are affine in `ε` almost
  surely.
* `mEquilibrium_congr`: `MEquilibrium` only depends on prices and debt up to null sets.
* `mFam_equilibrium`, `mFam_unique`: for every `ε` in `TidyR5Family.famDom` the family member is
  an equilibrium, and every equilibrium with the same surpluses and target equals it almost
  surely at every date; `mFam_steady`: the steady state at `ε = 0`.
* `mFam_contDiffOn`: almost surely, price level, debt and inflation are `C^n` in `ε` on
  `famDom` for every `n`.
* `mFamInfl_hasDerivAt_gen` (any rate family) and `mFamInfl_hasDerivAt` (canonical target):
  almost surely, the derivative at `ε = 0` of inflation is the solution (2.19) of the linear
  model, with the fiscal shock `mShock` (news about the present value of
  `ŝ` scaled by steady-state debt) and `π̂_0 = mInfl0`; `meas_family_linearization`: everything
  together, with existence and almost-sure uniqueness of the linear solution
  (`TidyR5MeasLinear.mPeg_linear_existsUnique`).
* `tree_mFamP`, `tree_mFamInfl`: on a finite event tree the family is `TidyR5Family.priceFam`
  and its inflation `TidyR5Family.inflFam`, for every rate family.

The rule family on a probability space is in `TidyR5MeasFamilyRule`.
-/

namespace Cochrane.IntertemporalModel.TidyR5MeasFamily

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure TidyR5Meas
  TidyR5MeasLinear TidyR5Family

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), §§2.1–2.4, pp. 21–33, on a probability space: an equilibrium remains an
equilibrium when its price level and debt are replaced by adapted processes equal to them almost
surely at every date. -/
theorem mEquilibrium_congr {β : ℝ} {Bm1 : Ω → ℝ} {s B P i B' P' : ℕ → Ω → ℝ}
    (h : MEquilibrium S β Bm1 s B P i) (hP'a : StronglyAdapted S.𝓕 P')
    (hB'a : StronglyAdapted S.𝓕 B') (hP : ∀ t, P' t =ᵐ[S.μ] P t) (hB : ∀ t, B' t =ᵐ[S.μ] B t) :
    MEquilibrium S β Bm1 s B' P' i := by
  obtain ⟨-, hpos, -, hia, hint, ⟨hv0, hv⟩, hbp⟩ := h
  have hr : ∀ t, (fun ω => P' t ω / P' (t + 1) ω) =ᵐ[S.μ] fun ω => P t ω / P (t + 1) ω :=
    fun t => by
      filter_upwards [hP t, hP (t + 1)] with ω h1 h2
      rw [h1, h2]
  refine ⟨hP'a, fun t => ?_, hB'a, hia, fun t => (hint t).congr (hr t).symm,
    ⟨?_, fun t => ?_⟩, fun t => ?_⟩
  · filter_upwards [hpos t, hP t] with ω h1 h2
    rw [h2]
    exact h1
  · filter_upwards [hv0, hP 0] with ω h1 h2
    rw [h2]
    exact h1
  · filter_upwards [hv t, hP (t + 1), hB t] with ω h1 h2 h3
    rw [h2, h3]
    exact h1
  · filter_upwards [hbp t, S.E_congr (hr t) t] with ω h1 h2
    rw [h1, Pi.smul_apply, Pi.smul_apply, h2]

/-! ### The family -/

/-- Cochrane (2023), eq. (2.7), p. 22: the affine present value of the family,
`V + ε PV_t(ŝ)`, for the fixed version `PV(ŝ) = forwardSol`. -/
noncomputable def pvAff (β sbar : ℝ) (shat : ℕ → Ω → ℝ) (ε : ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ssV β sbar + ε * S.forwardSol β shat t ω

/-- Cochrane (2023), eq. (2.15), p. 31: the affine ex-dividend present value of the family,
`βV + ε PVex_t(ŝ)`. -/
noncomputable def pvExAff (β sbar : ℝ) (shat : ℕ → Ω → ℝ) (ε : ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => β * ssV β sbar + ε * pvExM S β shat t ω

/-- Cochrane (2023), §2.4.3, p. 31, on a probability space: the price level of the family,
`P_0 = B_{−1}/PV_0(ε)`, `P_{t+1} = (1 + i_t(ε)) P_t PVex_t(ε)/PV_{t+1}(ε)`, for an arbitrary rate
family `iF` (e.g. the canonical target `TidyR5Family.rateExp`). -/
noncomputable def mFamP (β sbar : ℝ) (shat : ℕ → Ω → ℝ) (Bm1 : Ω → ℝ) (iF : ℝ → ℕ → Ω → ℝ)
    (ε : ℝ) : ℕ → Ω → ℝ
  | 0 => fun ω => Bm1 ω / pvAff S β sbar shat ε 0 ω
  | t + 1 => fun ω => (1 + iF ε t ω) * mFamP β sbar shat Bm1 iF ε t ω *
      pvExAff S β sbar shat ε t ω / pvAff S β sbar shat ε (t + 1) ω

/-- Cochrane (2023), eq. (2.15), p. 31, on a probability space: the debt sold along the family,
`B_t = (1 + i_t(ε)) P_t PVex_t(ε)`. -/
noncomputable def mFamB (β sbar : ℝ) (shat : ℕ → Ω → ℝ) (Bm1 : Ω → ℝ) (iF : ℝ → ℕ → Ω → ℝ)
    (ε : ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (1 + iF ε t ω) * mFamP S β sbar shat Bm1 iF ε t ω *
    pvExAff S β sbar shat ε t ω

/-- Cochrane (2023), §2.5, p. 35, on a probability space: inflation along the family,
`π_t(ε) = log(P_t(ε)/P_{t−1}(ε))`, with `P_{−1} = B_{−1}/V`. -/
noncomputable def mFamInfl (β sbar : ℝ) (shat : ℕ → Ω → ℝ) (Bm1 : Ω → ℝ)
    (iF : ℝ → ℕ → Ω → ℝ) (ε : ℝ) : ℕ → Ω → ℝ
  | 0 => fun ω => Real.log (mFamP S β sbar shat Bm1 iF ε 0 ω / (Bm1 ω / ssV β sbar))
  | t + 1 => fun ω => Real.log (mFamP S β sbar shat Bm1 iF ε (t + 1) ω /
      mFamP S β sbar shat Bm1 iF ε t ω)

/-- Cochrane (2023), eq. (2.17), p. 35, on a probability space: the fiscal shock of the linear
model for the family, the news about `PV(ŝ)` scaled by steady-state debt,
`ε_{Σs,t+1} = V⁻¹ ΔE_{t+1} PV_{t+1}(ŝ)`. -/
noncomputable def mShock (β sbar : ℝ) (shat : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (ssV β sbar)⁻¹ • mFiscShock S β shat t

/-- Cochrane (2023), eq. (2.17), p. 35, on a probability space: the initial inflation of the
linear model, `π̂_0 = −PV_0(ŝ)/V`. -/
noncomputable def mInfl0 (β sbar : ℝ) (shat : ℕ → Ω → ℝ) : Ω → ℝ :=
  fun ω => -((ssV β sbar)⁻¹ * S.forwardSol β shat 0 ω)

variable {β sbar M Mi : ℝ} {shat ihat : ℕ → Ω → ℝ} {Bm1 : Ω → ℝ} {iF : ℝ → ℕ → Ω → ℝ}

/-! ### Present values of the family -/

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), eq. (2.7), p. 22: the realised discounted sum of `s(ε)` is
`V + ε ∑ βʲ ŝ_{t+j}` in every state. -/
theorem discSum_surpFam (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hs : ∀ t ω, |shat t ω| ≤ M) (ε : ℝ)
    (t : ℕ) : MeasExpectationSystem.discSum β (surpFam sbar shat ε) t =
      (fun _ => ssV β sbar) + ε • MeasExpectationSystem.discSum β shat t := by
  funext ω
  exact congrFun (epv_surpFam (sbar := sbar) hβ0 hβ1 hs ε t) ω

/-- Cochrane (2023), eq. (2.7), p. 22: the realised discounted sum of a bounded adapted `ŝ` is
integrable. -/
theorem discSum_integrable (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hsad : StronglyAdapted S.𝓕 shat)
    (hs : ∀ t ω, |shat t ω| ≤ M) (t : ℕ) :
    Integrable (MeasExpectationSystem.discSum β shat t) S.μ := by
  have ha : |β| < 1 := by rwa [abs_of_nonneg hβ0]
  exact MeasExpectationSystem.BddRV.integrable
    ⟨S.aestronglyMeasurable_discSum ha
      (fun t => ((hsad t).mono (S.𝓕.le t)).aestronglyMeasurable)
      (fun t => Eventually.of_forall (hs t)) t, M / (1 - |β|),
      S.discSum_bdd ha (fun t => Eventually.of_forall (hs t)) t⟩

/-- Cochrane (2023), eq. (2.7), p. 22, on a probability space: `PV_t(s(ε)) = V + ε PV_t(ŝ)`
almost surely. -/
theorem forwardSol_surpFam (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hsad : StronglyAdapted S.𝓕 shat)
    (hs : ∀ t ω, |shat t ω| ≤ M) (ε : ℝ) (t : ℕ) :
    S.forwardSol β (surpFam sbar shat ε) t =ᵐ[S.μ] pvAff S β sbar shat ε t := by
  change S.E t (MeasExpectationSystem.discSum β (surpFam sbar shat ε) t) =ᵐ[S.μ] _
  rw [discSum_surpFam hβ0 hβ1 hs]
  filter_upwards [S.E_add (integrable_const (ssV β sbar))
    ((discSum_integrable S hβ0 hβ1 hsad hs t).smul ε) t,
    S.E_smul ε (MeasExpectationSystem.discSum β shat t) t] with ω h1 h2
  rw [h1, Pi.add_apply, S.E_const, h2]
  rfl

/-- Cochrane (2023), eq. (2.15), p. 31, on a probability space: `PVex_t(s(ε)) = βV + ε PVex_t(ŝ)`
almost surely. -/
theorem pvExM_surpFam (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hsad : StronglyAdapted S.𝓕 shat)
    (hs : ∀ t ω, |shat t ω| ≤ M) (ε : ℝ) (t : ℕ) :
    pvExM S β (surpFam sbar shat ε) t =ᵐ[S.μ] pvExAff S β sbar shat ε t := by
  have h1 := S.E_congr (forwardSol_surpFam S (sbar := sbar) hβ0 hβ1 hsad hs ε (t + 1)) t
  have e : pvAff S β sbar shat ε (t + 1) =
      (fun _ => ssV β sbar) + ε • S.forwardSol β shat (t + 1) := rfl
  rw [e] at h1
  have h2 : S.E t ((fun _ => ssV β sbar) + ε • S.forwardSol β shat (t + 1)) =ᵐ[S.μ]
      S.E t (fun _ => ssV β sbar) + S.E t (ε • S.forwardSol β shat (t + 1)) :=
    S.E_add (integrable_const (ssV β sbar)) ((S.integrable_E (t + 1) _).smul ε) t
  filter_upwards [h1, h2, S.E_smul ε (S.forwardSol β shat (t + 1)) t] with ω e1 e2 e3
  simp only [pvExM, pvExAff, Pi.smul_apply, smul_eq_mul]
  rw [e1, e2, Pi.add_apply, S.E_const, e3, Pi.smul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), eqs. (2.7) and (2.15), pp. 22, 31: almost surely, at every date,
`B_{−1} > 0`, `|PV_t(ŝ)| ≤ M/(1 − β)` and `|PVex_t(ŝ)| ≤ β M/(1 − β)`. -/
theorem good_ae (hβ0 : 0 < β) (hβ1 : β < 1) (hs : ∀ t ω, |shat t ω| ≤ M)
    (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω) :
    ∀ᵐ ω ∂S.μ, 0 < Bm1 ω ∧ ∀ t, |S.forwardSol β shat t ω| ≤ (1 - β)⁻¹ * M ∧
      |pvExM S β shat t ω| ≤ β * ((1 - β)⁻¹ * M) := by
  have ha : |β| < 1 := by rwa [abs_of_pos hβ0]
  have hK : M / (1 - |β|) = (1 - β)⁻¹ * M := by
    rw [abs_of_pos hβ0, div_eq_inv_mul]
  have hb : ∀ t, ∀ᵐ ω ∂S.μ, |S.forwardSol β shat t ω| ≤ (1 - β)⁻¹ * M := fun t => by
    rw [← hK]
    exact pv_bdd S ha (fun t => Eventually.of_forall (hs t)) t
  have hbE : ∀ t, ∀ᵐ ω ∂S.μ, |pvExM S β shat t ω| ≤ β * ((1 - β)⁻¹ * M) := fun t => by
    filter_upwards [S.abs_E_le (hb (t + 1)) t] with ω h
    simp only [pvExM, Pi.smul_apply, smul_eq_mul]
    rw [abs_mul, abs_of_pos hβ0]
    exact mul_le_mul_of_nonneg_left h hβ0.le
  filter_upwards [hB, ae_all_iff.2 hb, ae_all_iff.2 hbE] with ω h1 h2 h3
  exact ⟨h1, fun t => ⟨h2 t, h3 t⟩⟩

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), eq. (2.7), p. 22: on `famDom`, `V + ε Y > 0` whenever
`|Y| ≤ M/(1 − β)`. -/
theorem aff_pos (hβ1 : β < 1) {Y ε : ℝ} (hY : |Y| ≤ (1 - β)⁻¹ * M)
    (hε : ε ∈ famDom sbar M) : 0 < ssV β sbar + ε * Y := by
  have hε' : |ε| * M < sbar := hε
  have hc : 0 < (1 - β)⁻¹ := inv_pos.mpr (by linarith)
  have h1 : |ε * Y| ≤ |ε| * ((1 - β)⁻¹ * M) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hY (abs_nonneg ε)
  have h2 := neg_abs_le (ε * Y)
  have h3 : 0 < (1 - β)⁻¹ * (sbar - |ε| * M) := mul_pos hc (by linarith)
  simp only [ssV]
  nlinarith

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), eq. (2.15), p. 31: on `famDom`, `βV + ε X > 0` whenever
`|X| ≤ β M/(1 − β)` (`β > 0`). -/
theorem affEx_pos (hβ0 : 0 < β) (hβ1 : β < 1) {X ε : ℝ} (hX : |X| ≤ β * ((1 - β)⁻¹ * M))
    (hε : ε ∈ famDom sbar M) : 0 < β * ssV β sbar + ε * X := by
  have hY : |X / β| ≤ (1 - β)⁻¹ * M := by
    rw [abs_div, abs_of_pos hβ0, div_le_iff₀ hβ0]
    linarith
  have h := mul_pos hβ0 (aff_pos (sbar := sbar) hβ1 hY hε)
  have e : β * (ssV β sbar + ε * (X / β)) = β * ssV β sbar + ε * X := by
    field_simp
  rwa [e] at h

/-- Cochrane (2023), §2.4.3, p. 31: in every state where the bounds of `good_ae` hold, the
family's price level is positive on `famDom` (for a rate family exceeding `−1` there). -/
theorem mFamP_pos (hβ0 : 0 < β) (hβ1 : β < 1) {ω : Ω} (hω : 0 < Bm1 ω ∧
      ∀ t, |S.forwardSol β shat t ω| ≤ (1 - β)⁻¹ * M ∧
        |pvExM S β shat t ω| ≤ β * ((1 - β)⁻¹ * M))
    (hiG : ∀ ε ∈ famDom sbar M, ∀ t ω, -1 < iF ε t ω)
    {ε : ℝ} (hε : ε ∈ famDom sbar M) (t : ℕ) : 0 < mFamP S β sbar shat Bm1 iF ε t ω := by
  induction t with
  | zero => exact div_pos hω.1 (aff_pos hβ1 (hω.2 0).1 hε)
  | succ t ih =>
    change 0 < (1 + iF ε t ω) * mFamP S β sbar shat Bm1 iF ε t ω *
      pvExAff S β sbar shat ε t ω / pvAff S β sbar shat ε (t + 1) ω
    have h1 : 0 < 1 + iF ε t ω := by linarith [hiG ε hε t ω]
    have h2 : 0 < pvExAff S β sbar shat ε t ω := affEx_pos hβ0 hβ1 (hω.2 t).2 hε
    have h3 : 0 < pvAff S β sbar shat ε (t + 1) ω := aff_pos hβ1 (hω.2 (t + 1)).1 hε
    positivity

/-! ### Each member is an equilibrium, and the only one -/

/-- Cochrane (2023), eq. (2.16), p. 35: the canonical rate is adapted when `î` is (on a
probability space no `FunctionsKnown` hypothesis is needed). -/
theorem rateExp_sm (hihat : StronglyAdapted S.𝓕 ihat) (ε : ℝ) :
    StronglyAdapted S.𝓕 (rateExp β ihat ε) := fun t =>
  ((((hihat t).measurable.const_mul ε).exp.const_mul β⁻¹).sub_const 1).stronglyMeasurable

/-- Cochrane (2023), eq. (2.3), p. 22: with `|î| ≤ Mi`, the bond price of the canonical target,
`1/(1 + i_t(ε)) = β exp(−ε î_t)`, is integrable. -/
theorem rateExp_bondPrice_integrable (hβ0 : 0 < β) (hihat : StronglyAdapted S.𝓕 ihat)
    (hib : ∀ t ω, |ihat t ω| ≤ Mi) (ε : ℝ) (t : ℕ) :
    Integrable (fun ω => (1 + rateExp β ihat ε t ω)⁻¹) S.μ := by
  refine Integrable.of_bound (C := β * Real.exp (|ε| * Mi)) ?_ (Eventually.of_forall fun ω => ?_)
  · exact ((((rateExp_sm S hihat ε t).mono (S.𝓕.le t)).measurable.const_add 1).inv
      ).aestronglyMeasurable
  · have e : (1 + rateExp β ihat ε t ω)⁻¹ = β * Real.exp (-(ε * ihat t ω)) := by
      simp only [rateExp, add_sub_cancel]
      rw [mul_inv, inv_inv, Real.exp_neg]
    rw [e, Real.norm_eq_abs, abs_mul, abs_of_pos hβ0, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hβ0.le
    have h1 : |ε * ihat t ω| ≤ |ε| * Mi := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hib t ω) (abs_nonneg ε)
    linarith [neg_abs_le (ε * ihat t ω)]

/-- Cochrane (2023), §2.4.3, p. 31: the family's price level is adapted when the rate is. -/
theorem mFamP_sm (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1) {ε : ℝ}
    (hiA : StronglyAdapted S.𝓕 (iF ε)) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (mFamP S β sbar shat Bm1 iF ε t) := by
  have hpv : ∀ t, Measurable[S.𝓕 t] (pvAff S β sbar shat ε t) := fun t =>
    ((S.forwardSol_adapted β shat t).measurable.const_mul ε).const_add _
  have hpvE : ∀ t, Measurable[S.𝓕 t] (pvExAff S β sbar shat ε t) := fun t =>
    ((pvExM_sm S β shat t).measurable.const_mul ε).const_add _
  induction t with
  | zero => exact (hBm1.measurable.div (hpv 0)).stronglyMeasurable
  | succ t ih =>
    have hmono : S.𝓕 t ≤ S.𝓕 (t + 1) := S.𝓕.mono (Nat.le_succ t)
    exact (((((hiA t).mono hmono).measurable.const_add 1).mul
      (ih.mono hmono).measurable).mul ((hpvE t).mono hmono le_rfl)).div (hpv (t + 1))
      |>.stronglyMeasurable

/-- Cochrane (2023), eq. (2.15), p. 31: the family's debt is adapted when the rate is. -/
theorem mFamB_sm (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1) {ε : ℝ}
    (hiA : StronglyAdapted S.𝓕 (iF ε)) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (mFamB S β sbar shat Bm1 iF ε t) :=
  (((((hiA t)).measurable.const_add 1).mul (mFamP_sm S hBm1 hiA t).measurable).mul
    (((pvExM_sm S β shat t).measurable.const_mul ε).const_add _)).stronglyMeasurable

/-- Cochrane (2023), §2.4.3, p. 31: the family is almost surely the target equilibrium
`TidyR5Meas.mPegP`, `mPegB` of the economy with surpluses `s(ε)` and target `i(ε)`. -/
theorem mFam_ae_mPeg (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hsad : StronglyAdapted S.𝓕 shat)
    (hs : ∀ t ω, |shat t ω| ≤ M) (ε : ℝ) (t : ℕ) :
    mFamP S β sbar shat Bm1 iF ε t =ᵐ[S.μ] mPegP S β Bm1 (surpFam sbar shat ε) (iF ε) t ∧
      mFamB S β sbar shat Bm1 iF ε t =ᵐ[S.μ] mPegB S β Bm1 (surpFam sbar shat ε) (iF ε) t := by
  have hP : ∀ t, mFamP S β sbar shat Bm1 iF ε t =ᵐ[S.μ]
      mPegP S β Bm1 (surpFam sbar shat ε) (iF ε) t := by
    intro t
    induction t with
    | zero =>
      filter_upwards [forwardSol_surpFam S (sbar := sbar) hβ0 hβ1 hsad hs ε 0] with ω h
      change Bm1 ω / pvAff S β sbar shat ε 0 ω =
        Bm1 ω / S.forwardSol β (surpFam sbar shat ε) 0 ω
      rw [h]
    | succ t ih =>
      filter_upwards [ih, forwardSol_surpFam S (sbar := sbar) hβ0 hβ1 hsad hs ε (t + 1),
        pvExM_surpFam S (sbar := sbar) hβ0 hβ1 hsad hs ε t] with ω h1 h2 h3
      change (1 + iF ε t ω) * mFamP S β sbar shat Bm1 iF ε t ω *
        pvExAff S β sbar shat ε t ω / pvAff S β sbar shat ε (t + 1) ω =
        (1 + iF ε t ω) * mPegP S β Bm1 (surpFam sbar shat ε) (iF ε) t ω *
          pvExM S β (surpFam sbar shat ε) t ω /
            S.forwardSol β (surpFam sbar shat ε) (t + 1) ω
      rw [h1, h2, h3]
  refine ⟨hP t, ?_⟩
  filter_upwards [hP t, pvExM_surpFam S (sbar := sbar) hβ0 hβ1 hsad hs ε t] with ω h1 h3
  change (1 + iF ε t ω) * mFamP S β sbar shat Bm1 iF ε t ω *
      pvExAff S β sbar shat ε t ω = (1 + iF ε t ω) *
        mPegP S β Bm1 (surpFam sbar shat ε) (iF ε) t ω * pvExM S β (surpFam sbar shat ε) t ω
  rw [h1, h3]

/-- Cochrane (2023), eq. (2.7), p. 22, on a probability space: the present value of `s(ε)` is
bounded below by `(s̄ − |ε| M)/(1 − β)` almost surely at every date. -/
theorem forwardSol_surpFam_ge (hβ0 : 0 < β) (hβ1 : β < 1) (hsad : StronglyAdapted S.𝓕 shat)
    (hs : ∀ t ω, |shat t ω| ≤ M) (ε : ℝ) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, (1 - β)⁻¹ * (sbar - |ε| * M) ≤ S.forwardSol β (surpFam sbar shat ε) t ω := by
  have ha : |β| < 1 := by rwa [abs_of_pos hβ0]
  have hb := pv_bdd S ha (fun t => Eventually.of_forall (hs t)) t
  filter_upwards [forwardSol_surpFam S (sbar := sbar) hβ0.le hβ1 hsad hs ε t, hb] with ω h1 h2
  rw [h1]
  simp only [pvAff, ssV]
  rw [abs_of_pos hβ0, div_eq_inv_mul] at h2
  have hc : 0 ≤ (1 - β)⁻¹ := inv_nonneg.mpr (by linarith)
  have h3 : |ε * S.forwardSol β shat t ω| ≤ |ε| * ((1 - β)⁻¹ * M) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h2 (abs_nonneg ε)
  have h4 := neg_abs_le (ε * S.forwardSol β shat t ω)
  nlinarith

/-- Cochrane (2023), §2.4.3, p. 31, on a probability space: for every `ε ∈ famDom` the family
member is an equilibrium (`TidyR5Meas.MEquilibrium`): `0 < β < 1`, bounded adapted `ŝ`,
positive initial debt known at `0`, and a rate family that is adapted, exceeds `−1` and has an
integrable bond price on the domain. -/
theorem mFam_equilibrium (hβ0 : 0 < β) (hβ1 : β < 1) (hsad : StronglyAdapted S.𝓕 shat)
    (hs : ∀ t ω, |shat t ω| ≤ M) (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1)
    (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω) (hiA : ∀ ε ∈ famDom sbar M, StronglyAdapted S.𝓕 (iF ε))
    (hiG : ∀ ε ∈ famDom sbar M, ∀ t ω, -1 < iF ε t ω)
    (hiQ : ∀ ε ∈ famDom sbar M, ∀ t, Integrable (fun ω => (1 + iF ε t ω)⁻¹) S.μ)
    {ε : ℝ} (hε : ε ∈ famDom sbar M) :
    MEquilibrium S β Bm1 (surpFam sbar shat ε) (mFamB S β sbar shat Bm1 iF ε)
      (mFamP S β sbar shat Bm1 iF ε) (iF ε) := by
  have hε' : |ε| * M < sbar := hε
  have hc0 : 0 < (1 - β)⁻¹ * (sbar - |ε| * M) := mul_pos (inv_pos.mpr (by linarith))
    (by linarith)
  have hsM : ∀ t, ∀ᵐ ω ∂S.μ, |surpFam sbar shat ε t ω| ≤ |sbar| + |ε| * M := fun t =>
    Eventually.of_forall fun ω => by
      simp only [surpFam]
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hs t ω) (abs_nonneg ε)
  have hE := mPeg_equilibrium S hβ0 hβ1 hsM hc0
    (fun t => forwardSol_surpFam_ge S hβ0 hβ1 hsad hs ε t) hBm1 hB (hiA ε hε) (hiG ε hε)
    (hiQ ε hε)
  exact mEquilibrium_congr S hE (fun t => mFamP_sm S hBm1 (hiA ε hε) t)
    (fun t => mFamB_sm S hBm1 (hiA ε hε) t)
    (fun t => (mFam_ae_mPeg S hβ0.le hβ1 hsad hs ε t).1)
    (fun t => (mFam_ae_mPeg S hβ0.le hβ1 hsad hs ε t).2)

/-- Cochrane (2023), p. 33 (determinacy under a target), on a probability space: for every
`ε ∈ famDom`, every equilibrium with surpluses `s(ε)` and the target `i(ε)` equals the family
member almost surely at every date. -/
theorem mFam_unique (hβ0 : 0 < β) (hβ1 : β < 1) (hsad : StronglyAdapted S.𝓕 shat)
    (hs : ∀ t ω, |shat t ω| ≤ M) {ε : ℝ} (hε : ε ∈ famDom sbar M) {B P : ℕ → Ω → ℝ}
    (h : MEquilibrium S β Bm1 (surpFam sbar shat ε) B P (iF ε)) (t : ℕ) :
    P t =ᵐ[S.μ] mFamP S β sbar shat Bm1 iF ε t ∧
      B t =ᵐ[S.μ] mFamB S β sbar shat Bm1 iF ε t := by
  have hε' : |ε| * M < sbar := hε
  have hc0 : 0 < (1 - β)⁻¹ * (sbar - |ε| * M) := mul_pos (inv_pos.mpr (by linarith))
    (by linarith)
  obtain ⟨h1, h2⟩ := mPeg_unique S hβ0 hc0
    (fun t => forwardSol_surpFam_ge S hβ0 hβ1 hsad hs ε t) h t
  obtain ⟨h3, h4⟩ := mFam_ae_mPeg S (Bm1 := Bm1) (iF := iF) hβ0.le hβ1 hsad hs ε t
  exact ⟨h1.trans h3.symm, h2.trans h4.symm⟩

/-- Cochrane (2023), §2.5, p. 35: at `ε = 0`, with `i(0) = 1/β − 1`, the family is the steady
state, `P_t = B_{−1}/V` and `B_t = B_{−1}`, in every state (`0 < β < 1`, `s̄ > 0`). -/
theorem mFam_steady (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar)
    (hi0 : ∀ t ω, iF 0 t ω = β⁻¹ - 1) (t : ℕ) :
    mFamP S β sbar shat Bm1 iF 0 t = (fun ω => Bm1 ω / ssV β sbar) ∧
      mFamB S β sbar shat Bm1 iF 0 t = Bm1 := by
  have hV : ssV β sbar ≠ 0 := mul_ne_zero (inv_ne_zero (by linarith)) hsbar.ne'
  have hP : ∀ t, mFamP S β sbar shat Bm1 iF 0 t = fun ω => Bm1 ω / ssV β sbar := by
    intro t
    induction t with
    | zero =>
      funext ω
      change Bm1 ω / (ssV β sbar + 0 * S.forwardSol β shat 0 ω) = _
      rw [zero_mul, add_zero]
    | succ t ih =>
      funext ω
      change (1 + iF 0 t ω) * mFamP S β sbar shat Bm1 iF 0 t ω *
        (β * ssV β sbar + 0 * pvExM S β shat t ω) /
          (ssV β sbar + 0 * S.forwardSol β shat (t + 1) ω) = _
      rw [ih, hi0]
      simp only [zero_mul, add_zero]
      have := hβ0.ne'
      field_simp
      ring
  refine ⟨hP t, ?_⟩
  funext ω
  change (1 + iF 0 t ω) * mFamP S β sbar shat Bm1 iF 0 t ω *
    (β * ssV β sbar + 0 * pvExM S β shat t ω) = Bm1 ω
  rw [hP t, hi0]
  field_simp
  ring

/-! ### Smoothness and the derivative, almost surely -/

/-- Cochrane (2023), §§2.4–2.5, pp. 31–35, on a probability space: if almost surely the rate
family is `C^n` in `ε` on `famDom` (any `n`, including `∞` and analytic), then almost surely the
family's price level, debt and inflation are `C^n` in `ε` on `famDom` at every date. -/
theorem mFam_contDiffOn (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar)
    (hs : ∀ t ω, |shat t ω| ≤ M) (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω)
    (hiG : ∀ ε ∈ famDom sbar M, ∀ t ω, -1 < iF ε t ω) {n : WithTop ℕ∞}
    (hiC : ∀ᵐ ω ∂S.μ, ∀ t, ContDiffOn ℝ n (fun ε => iF ε t ω) (famDom sbar M)) :
    ∀ᵐ ω ∂S.μ, ∀ t : ℕ,
      ContDiffOn ℝ n (fun ε => mFamP S β sbar shat Bm1 iF ε t ω) (famDom sbar M) ∧
      ContDiffOn ℝ n (fun ε => mFamB S β sbar shat Bm1 iF ε t ω) (famDom sbar M) ∧
      ContDiffOn ℝ n (fun ε => mFamInfl S β sbar shat Bm1 iF ε t ω) (famDom sbar M) := by
  filter_upwards [good_ae S hβ0 hβ1 hs hB, hiC] with ω hω hC t
  have hV : 0 < ssV β sbar := mul_pos (inv_pos.mpr (by linarith)) hsbar
  have hpv : ∀ t, ContDiff ℝ n (fun ε => pvAff S β sbar shat ε t ω) := fun t =>
    contDiff_const.add (contDiff_id.mul contDiff_const)
  have hpvE : ∀ t, ContDiff ℝ n (fun ε => pvExAff S β sbar shat ε t ω) := fun t =>
    contDiff_const.add (contDiff_id.mul contDiff_const)
  have hP : ∀ t, ContDiffOn ℝ n (fun ε => mFamP S β sbar shat Bm1 iF ε t ω)
      (famDom sbar M) := by
    intro t
    induction t with
    | zero =>
      exact contDiffOn_const.div (hpv 0).contDiffOn
        (fun ε hε => (aff_pos hβ1 (hω.2 0).1 hε).ne')
    | succ t ih =>
      exact (((contDiffOn_const.add (hC t)).mul ih).mul
        (hpvE t).contDiffOn).div (hpv (t + 1)).contDiffOn
        (fun ε hε => (aff_pos hβ1 (hω.2 (t + 1)).1 hε).ne')
  refine ⟨hP t, ((contDiffOn_const.add (hC t)).mul (hP t)).mul (hpvE t).contDiffOn, ?_⟩
  cases t with
  | zero =>
    refine ((hP 0).div_const _).log fun ε hε => ?_
    exact (div_pos (mFamP_pos S hβ0 hβ1 hω hiG hε 0) (div_pos hω.1 hV)).ne'
  | succ t =>
    refine ((hP (t + 1)).div (hP t) (fun ε hε => (mFamP_pos S hβ0 hβ1 hω hiG hε t).ne')).log
      fun ε hε => ?_
    exact (div_pos (mFamP_pos S hβ0 hβ1 hω hiG hε (t + 1))
      (mFamP_pos S hβ0 hβ1 hω hiG hε t)).ne'

/-- Cochrane (2023), eqs. (2.16)–(2.17), p. 35, on a probability space, the derivative of
inflation along the family, state by state: almost surely, at every date,
`π̂_0 = −PV_0(ŝ)/V` and `π̂_{t+1} = d/dε log(1 + i_t(ε))|₀ − ε_{Σs,t+1}` with
`ε_{Σs,t+1} = V⁻¹ ΔE_{t+1} PV_{t+1}(ŝ)` (`mShock`), for any rate family exceeding `−1` on
`famDom` whose log gross rate has an almost-sure derivative `î` at `0`. -/
theorem mFamInfl_hasDerivAt_gen (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar)
    (hs : ∀ t ω, |shat t ω| ≤ M) (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω)
    (hiG : ∀ ε ∈ famDom sbar M, ∀ t ω, -1 < iF ε t ω) {ihat' : ℕ → Ω → ℝ}
    (hiD : ∀ᵐ ω ∂S.μ, ∀ t, HasDerivAt (fun ε => Real.log (1 + iF ε t ω)) (ihat' t ω) 0) :
    ∀ᵐ ω ∂S.μ, HasDerivAt (fun ε => mFamInfl S β sbar shat Bm1 iF ε 0 ω)
        (mInfl0 S β sbar shat ω) 0 ∧
      ∀ t, HasDerivAt (fun ε => mFamInfl S β sbar shat Bm1 iF ε (t + 1) ω)
        (ihat' t ω - mShock S β sbar shat (t + 1) ω) 0 := by
  filter_upwards [good_ae S hβ0 hβ1 hs hB, hiD] with ω hω hD
  have hV : 0 < ssV β sbar := mul_pos (inv_pos.mpr (by linarith)) hsbar
  have hnhds := famDom_mem_nhds hsbar M
  refine ⟨?_, fun t => ?_⟩
  · set Y := S.forwardSol β shat 0 ω with hY
    have hev : (fun ε => mFamInfl S β sbar shat Bm1 iF ε 0 ω) =ᶠ[𝓝 0]
        fun ε => Real.log (ssV β sbar) - Real.log (ssV β sbar + ε * Y) := by
      filter_upwards [hnhds] with ε hε
      have h3 := aff_pos hβ1 (hω.2 0).1 hε
      change Real.log (Bm1 ω / (ssV β sbar + ε * Y) / (Bm1 ω / ssV β sbar)) = _
      have hB' := hω.1.ne'
      rw [show Bm1 ω / (ssV β sbar + ε * Y) / (Bm1 ω / ssV β sbar) =
          ssV β sbar / (ssV β sbar + ε * Y) by field_simp,
        Real.log_div hV.ne' h3.ne']
    have hA : HasDerivAt (fun ε : ℝ => ssV β sbar + ε * Y) Y 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const Y).const_add (ssV β sbar)
    have hL := (hA.log (by simpa using hV.ne')).const_sub (Real.log (ssV β sbar))
    refine (hL.congr_of_eventuallyEq hev).congr_deriv ?_
    change -(Y / (ssV β sbar + 0 * Y)) = -((ssV β sbar)⁻¹ * Y)
    rw [zero_mul, add_zero, div_eq_inv_mul]
  · set X := pvExM S β shat t ω with hX
    set Y := S.forwardSol β shat (t + 1) ω with hY
    have hev : (fun ε => mFamInfl S β sbar shat Bm1 iF ε (t + 1) ω) =ᶠ[𝓝 0]
        fun ε => Real.log (1 + iF ε t ω) + Real.log (β * ssV β sbar + ε * X) -
          Real.log (ssV β sbar + ε * Y) := by
      filter_upwards [hnhds] with ε hε
      have hP := mFamP_pos S hβ0 hβ1 hω hiG hε t
      have h1 : 0 < 1 + iF ε t ω := by linarith [hiG ε hε t ω]
      have h2 : 0 < β * ssV β sbar + ε * X := affEx_pos hβ0 hβ1 (hω.2 t).2 hε
      have h3 : 0 < ssV β sbar + ε * Y := aff_pos hβ1 (hω.2 (t + 1)).1 hε
      change Real.log ((1 + iF ε t ω) * mFamP S β sbar shat Bm1 iF ε t ω *
        (β * ssV β sbar + ε * X) / (ssV β sbar + ε * Y) /
          mFamP S β sbar shat Bm1 iF ε t ω) = _
      have hP' := hP.ne'
      rw [show (1 + iF ε t ω) * mFamP S β sbar shat Bm1 iF ε t ω *
          (β * ssV β sbar + ε * X) / (ssV β sbar + ε * Y) /
            mFamP S β sbar shat Bm1 iF ε t ω =
          (1 + iF ε t ω) * (β * ssV β sbar + ε * X) / (ssV β sbar + ε * Y) by
          field_simp,
        Real.log_div (mul_pos h1 h2).ne' h3.ne', Real.log_mul h1.ne' h2.ne']
    have hA : HasDerivAt (fun ε : ℝ => β * ssV β sbar + ε * X) X 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const X).const_add (β * ssV β sbar)
    have hC : HasDerivAt (fun ε : ℝ => ssV β sbar + ε * Y) Y 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const Y).const_add (ssV β sbar)
    have hbV : β * ssV β sbar ≠ 0 := (mul_pos hβ0 hV).ne'
    have hL := HasDerivAt.sub (HasDerivAt.add (hD t) (hA.log (by simpa using hbV)))
      (hC.log (by simpa using hV.ne'))
    refine (hL.congr_of_eventuallyEq hev).congr_deriv ?_
    have hXe : X = β * S.E t (S.forwardSol β shat (t + 1)) ω := rfl
    have hsh : mShock S β sbar shat (t + 1) ω = (ssV β sbar)⁻¹ *
        (Y - S.E t (S.forwardSol β shat (t + 1)) ω) := by
      change (ssV β sbar)⁻¹ * (S.E (t + 1) (S.forwardSol β shat (t + 1)) ω -
        S.E t (S.forwardSol β shat (t + 1)) ω) = _
      rw [show S.E (t + 1) (S.forwardSol β shat (t + 1)) = S.forwardSol β shat (t + 1) from
        S.E_E_self (t + 1) _]
    change ihat' t ω + X / (β * ssV β sbar + 0 * X) - Y / (ssV β sbar + 0 * Y) =
      ihat' t ω - mShock S β sbar shat (t + 1) ω
    rw [hsh, hXe, zero_mul, add_zero, zero_mul, add_zero]
    field_simp
    ring

/-- Cochrane (2023), eqs. (2.16)–(2.19), pp. 35–36, on a probability space, for the canonical
target: **almost surely the derivative at `ε = 0` of inflation along the family of exact
equilibria is the solution (2.19) of the linear model**, `π̂_0 = −PV_0(ŝ)/V`,
`π̂_{t+1} = î_t − ε_{Σs,t+1}`. -/
theorem mFamInfl_hasDerivAt (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar)
    (hs : ∀ t ω, |shat t ω| ≤ M) (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω) :
    ∀ᵐ ω ∂S.μ, ∀ t, HasDerivAt (fun ε => mFamInfl S β sbar shat Bm1 (rateExp β ihat) ε t ω)
      (LinearFTMP.pegSol ihat (mShock S β sbar shat) (mInfl0 S β sbar shat) t ω) 0 := by
  filter_upwards [mFamInfl_hasDerivAt_gen S hβ0 hβ1 hsbar hs hB
    (fun ε _ t ω => rateExp_gt hβ0 ihat ε t ω)
    (Eventually.of_forall fun ω t => rateExp_log_hasDerivAt hβ0 ihat t ω)] with ω h t
  cases t with
  | zero => exact h.1
  | succ t => exact h.2 t

/-- Cochrane (2023), eq. (2.17), p. 35, on a probability space: the scaled fiscal shock is a
shock (`TidyR5MeasLinear.MIsShock`). -/
theorem mShock_isShock : MIsShock S (mShock S β sbar shat) := by
  obtain ⟨h1, h2, h3⟩ := mFiscShock_isShock S β shat
  refine ⟨fun t => (h1 t).const_smul _, fun t => (h2 t).smul _, fun t => ?_⟩
  filter_upwards [S.E_smul (ssV β sbar)⁻¹ (mFiscShock S β shat (t + 1)) t, h3 t] with ω e1 e2
  change S.E t ((ssV β sbar)⁻¹ • mFiscShock S β shat (t + 1)) ω = 0
  rw [e1, Pi.smul_apply, e2, Pi.zero_apply, smul_zero]

/-- Cochrane (2023), eq. (2.17), p. 35, on a probability space: the initial inflation of the
linear model is known at `0` and integrable. -/
theorem mInfl0_sm_integrable : StronglyMeasurable[S.𝓕 0] (mInfl0 S β sbar shat) ∧
    Integrable (mInfl0 S β sbar shat) S.μ :=
  ⟨((S.forwardSol_adapted β shat 0).measurable.const_mul _).neg.stronglyMeasurable,
    ((S.integrable_E 0 _).const_mul _).neg⟩

/-- Cochrane (2023), §§2.4–2.5, pp. 31–36, **the family of exact equilibria on a genuine
probability space**, for the canonical target, all in one statement. For `0 < β < 1`, `s̄ > 0`,
bounded adapted `ŝ` and `î`, and a positive initial debt known at `0`, on the open
neighbourhood `famDom` of `ε = 0`:
* for each `ε` the family member is an equilibrium, and every equilibrium with the same
  surpluses and target equals it almost surely at every date;
* at `ε = 0` it is the steady state;
* almost surely, price level, debt and inflation are `C^n` in `ε` for every `n`;
* the linear model (2.16)–(2.19) with the fiscal shock `mShock` and `π̂_0 = mInfl0` has an
  adapted integrable solution, unique up to null sets at every date, and every adapted
  integrable solution is, at every date and almost surely, the derivative at `ε = 0` of
  inflation along the family. -/
theorem meas_family_linearization (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar)
    (hsad : StronglyAdapted S.𝓕 shat) (hs : ∀ t ω, |shat t ω| ≤ M)
    (hihat : StronglyAdapted S.𝓕 ihat) (hib : ∀ t ω, |ihat t ω| ≤ Mi)
    (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1) (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω) :
    (∀ ε ∈ famDom sbar M, MEquilibrium S β Bm1 (surpFam sbar shat ε)
      (mFamB S β sbar shat Bm1 (rateExp β ihat) ε)
      (mFamP S β sbar shat Bm1 (rateExp β ihat) ε) (rateExp β ihat ε)) ∧
    (∀ ε ∈ famDom sbar M, ∀ B P : ℕ → Ω → ℝ,
      MEquilibrium S β Bm1 (surpFam sbar shat ε) B P (rateExp β ihat ε) →
        ∀ t, P t =ᵐ[S.μ] mFamP S β sbar shat Bm1 (rateExp β ihat) ε t ∧
          B t =ᵐ[S.μ] mFamB S β sbar shat Bm1 (rateExp β ihat) ε t) ∧
    (∀ t, mFamP S β sbar shat Bm1 (rateExp β ihat) 0 t = (fun ω => Bm1 ω / ssV β sbar) ∧
      mFamB S β sbar shat Bm1 (rateExp β ihat) 0 t = Bm1) ∧
    (∀ n : WithTop ℕ∞, ∀ᵐ ω ∂S.μ, ∀ t : ℕ,
      ContDiffOn ℝ n (fun ε => mFamP S β sbar shat Bm1 (rateExp β ihat) ε t ω)
        (famDom sbar M) ∧
      ContDiffOn ℝ n (fun ε => mFamB S β sbar shat Bm1 (rateExp β ihat) ε t ω)
        (famDom sbar M) ∧
      ContDiffOn ℝ n (fun ε => mFamInfl S β sbar shat Bm1 (rateExp β ihat) ε t ω)
        (famDom sbar M)) ∧
    (StronglyAdapted S.𝓕 (LinearFTMP.pegSol ihat (mShock S β sbar shat) (mInfl0 S β sbar shat)) ∧
      (∀ t, Integrable
        (LinearFTMP.pegSol ihat (mShock S β sbar shat) (mInfl0 S β sbar shat) t) S.μ) ∧
      MPegModel S ihat (mShock S β sbar shat)
        (LinearFTMP.pegSol ihat (mShock S β sbar shat) (mInfl0 S β sbar shat))) ∧
    ∀ π : ℕ → Ω → ℝ, StronglyAdapted S.𝓕 π → (∀ t, Integrable (π t) S.μ) →
      π 0 =ᵐ[S.μ] mInfl0 S β sbar shat → MPegModel S ihat (mShock S β sbar shat) π →
        ∀ t, ∀ᵐ ω ∂S.μ, HasDerivAt
          (fun ε => mFamInfl S β sbar shat Bm1 (rateExp β ihat) ε t ω) (π t ω) 0 := by
  have hii : ∀ t, Integrable (ihat t) S.μ := fun t =>
    MeasExpectationSystem.BddRV.integrable
      ⟨((hihat t).mono (S.𝓕.le t)).aestronglyMeasurable, Mi, Eventually.of_forall (hib t)⟩
  have hiG : ∀ ε ∈ famDom sbar M, ∀ t ω, -1 < rateExp β ihat ε t ω :=
    fun ε _ t ω => rateExp_gt hβ0 ihat ε t ω
  obtain ⟨h0, h0i⟩ := mInfl0_sm_integrable S (β := β) (sbar := sbar) (shat := shat)
  obtain ⟨hex, huniq⟩ := mPeg_linear_existsUnique S hihat hii (mShock_isShock S) h0 h0i
  refine ⟨fun ε hε => mFam_equilibrium S hβ0 hβ1 hsad hs hBm1 hB
      (fun ε _ => rateExp_sm S hihat ε) hiG
      (fun ε _ t => rateExp_bondPrice_integrable S hβ0 hihat hib ε t) hε,
    fun ε hε B P h t => mFam_unique S hβ0 hβ1 hsad hs hε h t,
    fun t => mFam_steady S hβ0 hβ1 hsbar (rateExp_zero ihat) t,
    fun n => mFam_contDiffOn S hβ0 hβ1 hsbar hs hB hiG
      (Eventually.of_forall fun ω t => (rateExp_contDiff ihat t ω).contDiffOn), hex,
    fun π hπ hπi hπ0 hm t => ?_⟩
  filter_upwards [huniq π hπ hπi hπ0 hm t, mFamInfl_hasDerivAt S (ihat := ihat) hβ0 hβ1 hsbar
    hs hB] with ω h1 h2
  rw [h1]
  exact h2 t

/-! ### The link to the family on a finite tree -/

namespace Link

open ExpectationsFiniteTree TreeBridge TidyR5MeasLinear.Link

variable {Ω' : Type*} [Fintype Ω'] [MeasurableSpace Ω'] [DiscreteMeasurableSpace Ω']
  (T : FiniteTree Ω')

/-- Cochrane (2023), §2.4.3, p. 31: on a finite tree the measure-theoretic family is the family
`TidyR5Family.priceFam` (and `debtFam`) of the core model, in every
state, for every `ε` and every rate family (bounded `ŝ`, `0 ≤ β < 1`). -/
theorem tree_mFamP (hβ0 : 0 ≤ β) (hβ1 : β < 1) {shat' : ℕ → Ω' → ℝ}
    (hs : ∀ t ω, |shat' t ω| ≤ M) (Bm1' : Ω' → ℝ) (iF' : ℝ → ℕ → Ω' → ℝ) (ε : ℝ) (t : ℕ) :
    mFamP (treeSystem T) β sbar shat' Bm1' iF' ε t =
        priceFam T.toExpectationSystem β sbar shat' Bm1' iF' ε t ∧
      mFamB (treeSystem T) β sbar shat' Bm1' iF' ε t =
        debtFam T.toExpectationSystem β sbar shat' Bm1' iF' ε t := by
  have hpv : ∀ t, pvAff (treeSystem T) β sbar shat' ε t =
      FiscalMonetary.pv T.toExpectationSystem β (surpFam sbar shat' ε) t := fun t => by
    rw [pv_surpFam T.toExpectationSystem hβ0 hβ1 hs]
    funext ω
    simp only [pvAff, tree_forwardSol]
  have hpvE : ∀ t, pvExAff (treeSystem T) β sbar shat' ε t =
      FiscalMonetary.pvEx T.toExpectationSystem β (surpFam sbar shat' ε) t := fun t => by
    rw [pvEx_surpFam T.toExpectationSystem hβ0 hβ1 hs]
    funext ω
    simp only [pvExAff, tree_pvExM]
  have hP : ∀ t, mFamP (treeSystem T) β sbar shat' Bm1' iF' ε t =
      priceFam T.toExpectationSystem β sbar shat' Bm1' iF' ε t := by
    intro t
    induction t with
    | zero =>
      funext ω
      change Bm1' ω / pvAff (treeSystem T) β sbar shat' ε 0 ω = _
      rw [hpv]
      rfl
    | succ t ih =>
      funext ω
      change (1 + iF' ε t ω) * mFamP (treeSystem T) β sbar shat' Bm1' iF' ε t ω *
        pvExAff (treeSystem T) β sbar shat' ε t ω / pvAff (treeSystem T) β sbar shat' ε (t + 1) ω
        = _
      rw [ih, hpv, hpvE]
      rfl
  refine ⟨hP t, ?_⟩
  funext ω
  change (1 + iF' ε t ω) * mFamP (treeSystem T) β sbar shat' Bm1' iF' ε t ω *
    pvExAff (treeSystem T) β sbar shat' ε t ω = _
  rw [hP t, hpvE]
  rfl

/-- Cochrane (2023), §2.5, p. 35: on a finite tree the measure-theoretic family's inflation is
`TidyR5Family.inflFam`. -/
theorem tree_mFamInfl (hβ0 : 0 ≤ β) (hβ1 : β < 1) {shat' : ℕ → Ω' → ℝ}
    (hs : ∀ t ω, |shat' t ω| ≤ M) (Bm1' : Ω' → ℝ) (iF' : ℝ → ℕ → Ω' → ℝ) (ε : ℝ) (t : ℕ) :
    mFamInfl (treeSystem T) β sbar shat' Bm1' iF' ε t =
      inflFam T.toExpectationSystem β sbar shat' Bm1' iF' ε t := by
  have hP := fun t => (tree_mFamP (sbar := sbar) T hβ0 hβ1 hs Bm1' iF' ε t).1
  cases t with
  | zero =>
    funext ω
    change Real.log (mFamP (treeSystem T) β sbar shat' Bm1' iF' ε 0 ω / (Bm1' ω / ssV β sbar))
      = _
    rw [hP 0]
    rfl
  | succ t =>
    funext ω
    change Real.log (mFamP (treeSystem T) β sbar shat' Bm1' iF' ε (t + 1) ω /
      mFamP (treeSystem T) β sbar shat' Bm1' iF' ε t ω) = _
    rw [hP (t + 1), hP t]
    rfl

end Link

end Cochrane.IntertemporalModel.TidyR5MeasFamily
