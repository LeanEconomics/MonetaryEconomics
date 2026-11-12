/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.TidyR5MeasFamily
import IntertemporalModel.TidyR5FamilyRule

/-!
# The family of exact equilibria under an interest-rate rule on a probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.6 "Interest-rate rules",
pp. 39–42, eqs. (2.20)–(2.25), on a probability space with Mathlib's conditional expectation:
the family of exact equilibria under the exact rule `log(1 + i_t) = −log β + θ π_t + ε u_t`
(`TidyR5FamilyRule`), built with the fixed versions of present values of
`TidyR5MeasFamily` (`TidyR5MeasFamily.pvAff`, `TidyR5MeasFamily.pvExAff`), for every `θ ∈ ℝ`.

## Main results

* `mRuleInfl`, `mRuleRate`: inflation and the rate of the family in closed form;
  `mRuleInfl_bound`: they are bounded on `famDom` almost surely, so the bond price is integrable
  (`mRuleRate_bondPrice_integrable`).
* `mRule_equilibrium`, `mRule_exact`: for every `ε ∈ famDom` the family member is an equilibrium
  (`TidyR5Meas.MEquilibrium`) satisfying the exact rule almost surely (`MRuleExact`);
  `mRule_unique`: every equilibrium satisfying the exact rule equals it almost surely at every
  date.
* `mRuleInfl_hasDerivAt`, `mRule_rate_hasDerivAt`: the derivatives at `ε = 0` of inflation and
  of the log gross rate are the solution (2.25) `LinearFTMP.ruleSol θ u ε_{Σs} π̂_0` of the linear
  model and its rate, in every state for the closed form (almost surely for the family, whose
  inflation is the closed form, `mFamInfl_eq`); `mRule_family_linearization`: everything
  together with the existence and almost-sure uniqueness of the linear solution
  (`TidyR5MeasLinear.mRule_linear_existsUnique`), for every `θ`.
* `tree_mRuleRate`: on a finite tree the rate is `TidyR5FamilyRule.ruleRate`.
-/

namespace Cochrane.IntertemporalModel.TidyR5MeasFamilyRule

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure TidyR5Meas
  TidyR5MeasLinear TidyR5Family TidyR5FamilyRule TidyR5MeasFamily

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), eqs. (2.20)–(2.22), p. 40, on a probability space: inflation along the rule
family in closed form, `π_0 = log V − log PV_0(ε)`,
`π_{t+1} = −log β + θ π_t + ε u_t + log PVex_t(ε) − log PV_{t+1}(ε)`. -/
noncomputable def mRuleInfl (β sbar : ℝ) (shat : ℕ → Ω → ℝ) (θ : ℝ) (u : ℕ → Ω → ℝ) (ε : ℝ) :
    ℕ → Ω → ℝ
  | 0 => fun ω => Real.log (ssV β sbar) - Real.log (pvAff S β sbar shat ε 0 ω)
  | t + 1 => fun ω => -Real.log β + θ * mRuleInfl β sbar shat θ u ε t ω + ε * u t ω +
      Real.log (pvExAff S β sbar shat ε t ω) - Real.log (pvAff S β sbar shat ε (t + 1) ω)

/-- Cochrane (2023), eq. (2.22), p. 40, on a probability space: the rate of the rule family,
`1 + i_t(ε) = β⁻¹ exp(θ π_t(ε) + ε u_t)`. -/
noncomputable def mRuleRate (β sbar : ℝ) (shat : ℕ → Ω → ℝ) (θ : ℝ) (u : ℕ → Ω → ℝ) (ε : ℝ) :
    ℕ → Ω → ℝ :=
  fun t ω => β⁻¹ * Real.exp (θ * mRuleInfl S β sbar shat θ u ε t ω + ε * u t ω) - 1

/-- Cochrane (2023), eq. (2.22), p. 40, exact form, on a probability space: the rule
`log(1 + i_t) = −log β + θ π_t + ε u_t` almost surely at every date (`π` from
`TidyR5FamilyRule.logInfl`, `P_{−1} = B_{−1}/V`). -/
def MRuleExact (β θ : ℝ) (Bm1 : Ω → ℝ) (V : ℝ) (u : ℕ → Ω → ℝ) (ε : ℝ) (P i : ℕ → Ω → ℝ) :
    Prop :=
  ∀ t, ∀ᵐ ω ∂S.μ, Real.log (1 + i t ω) = -Real.log β + θ * logInfl Bm1 V P t ω + ε * u t ω

variable {β sbar M θ Mu : ℝ} {shat u : ℕ → Ω → ℝ} {Bm1 : Ω → ℝ}

/-- Cochrane (2023), eq. (2.22), p. 40: the rule family's rate exceeds `−1` (`β > 0`). -/
theorem mRuleRate_gt (hβ0 : 0 < β) (ε : ℝ) (t : ℕ) (ω : Ω) :
    -1 < mRuleRate S β sbar shat θ u ε t ω := by
  simp only [mRuleRate]
  have := mul_pos (inv_pos.mpr hβ0)
    (Real.exp_pos (θ * mRuleInfl S β sbar shat θ u ε t ω + ε * u t ω))
  linarith

/-- Cochrane (2023), eq. (2.22), p. 40: `log(1 + i_t(ε)) = −log β + θ π_t(ε) + ε u_t` exactly
(`β > 0`). -/
theorem log_one_add_mRuleRate (hβ0 : 0 < β) (ε : ℝ) (t : ℕ) (ω : Ω) :
    Real.log (1 + mRuleRate S β sbar shat θ u ε t ω) =
      -Real.log β + θ * mRuleInfl S β sbar shat θ u ε t ω + ε * u t ω := by
  simp only [mRuleRate, add_sub_cancel]
  rw [Real.log_mul (inv_pos.mpr hβ0).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_inv]
  ring

/-- Cochrane (2023), p. 40: inflation of the rule family is adapted (adapted `u`). -/
theorem mRuleInfl_sm (hu : StronglyAdapted S.𝓕 u) (ε : ℝ) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (mRuleInfl S β sbar shat θ u ε t) := by
  have hpv : ∀ t, Measurable[S.𝓕 t] (pvAff S β sbar shat ε t) := fun t =>
    ((S.forwardSol_adapted β shat t).measurable.const_mul ε).const_add _
  have hpvE : ∀ t, Measurable[S.𝓕 t] (pvExAff S β sbar shat ε t) := fun t =>
    ((pvExM_sm S β shat t).measurable.const_mul ε).const_add _
  induction t with
  | zero => exact (measurable_const.sub (hpv 0).log).stronglyMeasurable
  | succ t ih =>
    have hmono : S.𝓕 t ≤ S.𝓕 (t + 1) := S.𝓕.mono (Nat.le_succ t)
    exact ((((measurable_const.add ((ih.mono hmono).measurable.const_mul θ)).add
      (((hu t).mono hmono).measurable.const_mul ε)).add ((hpvE t).log.mono hmono le_rfl)).sub
      (hpv (t + 1)).log).stronglyMeasurable

/-- Cochrane (2023), eq. (2.22), p. 40: the rule family's rate is adapted. -/
theorem mRuleRate_sm (hu : StronglyAdapted S.𝓕 u) (ε : ℝ) :
    StronglyAdapted S.𝓕 (mRuleRate S β sbar shat θ u ε) := fun t =>
  (((((mRuleInfl_sm S hu ε t).measurable.const_mul θ).add
    ((hu t).measurable.const_mul ε)).exp.const_mul β⁻¹).sub_const 1).stronglyMeasurable

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 40: `|log x| ≤ |log a| + |log b|` for `0 < a ≤ x ≤ b`. -/
theorem abs_log_le {a b x : ℝ} (ha : 0 < a) (h1 : a ≤ x) (h2 : x ≤ b) :
    |Real.log x| ≤ |Real.log a| + |Real.log b| := by
  have l1 := Real.log_le_log ha h1
  have l2 := Real.log_le_log (ha.trans_le h1) h2
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log a), abs_nonneg (Real.log b)]
  · linarith [le_abs_self (Real.log b), abs_nonneg (Real.log a)]

/-- Cochrane (2023), p. 40: the bound on inflation of the rule family, with
`L = (s̄ − |ε| M)/(1 − β)` and `U = (s̄ + |ε| M)/(1 − β)` bounding present values. -/
noncomputable def ruleBound (β sbar M θ Mu ε : ℝ) : ℕ → ℝ
  | 0 => |Real.log (ssV β sbar)| + (|Real.log ((1 - β)⁻¹ * (sbar - |ε| * M))| +
      |Real.log ((1 - β)⁻¹ * (sbar + |ε| * M))|)
  | t + 1 => |Real.log β| + |θ| * ruleBound β sbar M θ Mu ε t + |ε| * Mu +
      (|Real.log (β * ((1 - β)⁻¹ * (sbar - |ε| * M)))| +
        |Real.log (β * ((1 - β)⁻¹ * (sbar + |ε| * M)))|) +
      (|Real.log ((1 - β)⁻¹ * (sbar - |ε| * M))| + |Real.log ((1 - β)⁻¹ * (sbar + |ε| * M))|)

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), eq. (2.7), p. 22: `V + ε Y ≤ (s̄ + |ε| M)/(1 − β)` when
`|Y| ≤ M/(1 − β)`. -/
theorem aff_le {Y ε : ℝ} (hY : |Y| ≤ (1 - β)⁻¹ * M) :
    ssV β sbar + ε * Y ≤ (1 - β)⁻¹ * (sbar + |ε| * M) := by
  have h1 : ε * Y ≤ |ε| * ((1 - β)⁻¹ * M) := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hY (abs_nonneg ε)
  simp only [ssV]
  nlinarith

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), eq. (2.7), p. 22: `V + ε Y ≥ (s̄ − |ε| M)/(1 − β)` when
`|Y| ≤ M/(1 − β)`. -/
theorem le_aff {Y ε : ℝ} (hY : |Y| ≤ (1 - β)⁻¹ * M) :
    (1 - β)⁻¹ * (sbar - |ε| * M) ≤ ssV β sbar + ε * Y := by
  have h1 : -(|ε| * ((1 - β)⁻¹ * M)) ≤ ε * Y := by
    refine le_trans ?_ (neg_abs_le _)
    rw [abs_mul, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_left hY (abs_nonneg ε)
  simp only [ssV]
  nlinarith

/-- Cochrane (2023), p. 40: in every state where the bounds of `TidyR5MeasFamily.good_ae` hold,
for `ε ∈ famDom` and `|u| ≤ Mu`, `|π_t(ε)| ≤ ruleBound t`. -/
theorem mRuleInfl_bound (hβ0 : 0 < β) (hβ1 : β < 1) (hu : ∀ t ω, |u t ω| ≤ Mu) {ω : Ω}
    (hω : 0 < Bm1 ω ∧ ∀ t, |S.forwardSol β shat t ω| ≤ (1 - β)⁻¹ * M ∧
      |pvExM S β shat t ω| ≤ β * ((1 - β)⁻¹ * M))
    {ε : ℝ} (hε : ε ∈ famDom sbar M) (t : ℕ) :
    |mRuleInfl S β sbar shat θ u ε t ω| ≤ ruleBound β sbar M θ Mu ε t := by
  have hε' : |ε| * M < sbar := hε
  have hL : 0 < (1 - β)⁻¹ * (sbar - |ε| * M) := mul_pos (inv_pos.mpr (by linarith))
    (by linarith)
  have hpv : ∀ t, |Real.log (pvAff S β sbar shat ε t ω)| ≤
      |Real.log ((1 - β)⁻¹ * (sbar - |ε| * M))| +
        |Real.log ((1 - β)⁻¹ * (sbar + |ε| * M))| := fun t =>
    abs_log_le hL (le_aff (hω.2 t).1) (aff_le (hω.2 t).1)
  have hpvE : ∀ t, |Real.log (pvExAff S β sbar shat ε t ω)| ≤
      |Real.log (β * ((1 - β)⁻¹ * (sbar - |ε| * M)))| +
        |Real.log (β * ((1 - β)⁻¹ * (sbar + |ε| * M)))| := by
    intro t
    have hX : |pvExM S β shat t ω / β| ≤ (1 - β)⁻¹ * M := by
      rw [abs_div, abs_of_pos hβ0, div_le_iff₀ hβ0]
      linarith [(hω.2 t).2]
    have e : pvExAff S β sbar shat ε t ω =
        β * (ssV β sbar + ε * (pvExM S β shat t ω / β)) := by
      simp only [pvExAff]
      field_simp
    rw [e]
    exact abs_log_le (mul_pos hβ0 hL) (mul_le_mul_of_nonneg_left (le_aff hX) hβ0.le)
      (mul_le_mul_of_nonneg_left (aff_le hX) hβ0.le)
  induction t with
  | zero =>
    change |Real.log (ssV β sbar) - Real.log (pvAff S β sbar shat ε 0 ω)| ≤ _
    exact (abs_sub _ _).trans (add_le_add le_rfl (hpv 0))
  | succ t ih =>
    change |-Real.log β + θ * mRuleInfl S β sbar shat θ u ε t ω + ε * u t ω +
      Real.log (pvExAff S β sbar shat ε t ω) - Real.log (pvAff S β sbar shat ε (t + 1) ω)| ≤ _
    have h1 : |θ * mRuleInfl S β sbar shat θ u ε t ω| ≤ |θ| * ruleBound β sbar M θ Mu ε t := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ih (abs_nonneg θ)
    have h2 : |ε * u t ω| ≤ |ε| * Mu := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hu t ω) (abs_nonneg ε)
    have h3 := hpvE t
    have h4 := hpv (t + 1)
    simp only [ruleBound]
    calc _ ≤ |-Real.log β + θ * mRuleInfl S β sbar shat θ u ε t ω + ε * u t ω +
          Real.log (pvExAff S β sbar shat ε t ω)| +
          |Real.log (pvAff S β sbar shat ε (t + 1) ω)| := abs_sub _ _
      _ ≤ |-Real.log β + θ * mRuleInfl S β sbar shat θ u ε t ω + ε * u t ω| +
          |Real.log (pvExAff S β sbar shat ε t ω)| +
          |Real.log (pvAff S β sbar shat ε (t + 1) ω)| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ |-Real.log β + θ * mRuleInfl S β sbar shat θ u ε t ω| + |ε * u t ω| +
          |Real.log (pvExAff S β sbar shat ε t ω)| +
          |Real.log (pvAff S β sbar shat ε (t + 1) ω)| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ |-Real.log β| + |θ * mRuleInfl S β sbar shat θ u ε t ω| + |ε * u t ω| +
          |Real.log (pvExAff S β sbar shat ε t ω)| +
          |Real.log (pvAff S β sbar shat ε (t + 1) ω)| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ _ := by
        rw [abs_neg]
        linarith

/-- Cochrane (2023), eq. (2.3), p. 22, on a probability space: on `famDom`, with `|u| ≤ Mu`,
the bond price `1/(1 + i_t(ε)) = β exp(−θ π_t − ε u_t)` of the rule family is integrable. -/
theorem mRuleRate_bondPrice_integrable (hβ0 : 0 < β) (hβ1 : β < 1)
    (hs : ∀ t ω, |shat t ω| ≤ M) (hua : StronglyAdapted S.𝓕 u) (hu : ∀ t ω, |u t ω| ≤ Mu)
    (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω) {ε : ℝ} (hε : ε ∈ famDom sbar M) (t : ℕ) :
    Integrable (fun ω => (1 + mRuleRate S β sbar shat θ u ε t ω)⁻¹) S.μ := by
  refine Integrable.of_bound
    (C := β * Real.exp (|θ| * ruleBound β sbar M θ Mu ε t + |ε| * Mu)) ?_ ?_
  · exact ((((mRuleRate_sm S hua ε t).mono (S.𝓕.le t)).measurable.const_add 1).inv
      ).aestronglyMeasurable
  · filter_upwards [good_ae S (Bm1 := Bm1) hβ0 hβ1 hs hB] with ω hω
    have e : (1 + mRuleRate S β sbar shat θ u ε t ω)⁻¹ =
        β * Real.exp (-(θ * mRuleInfl S β sbar shat θ u ε t ω + ε * u t ω)) := by
      simp only [mRuleRate, add_sub_cancel]
      rw [mul_inv, inv_inv, Real.exp_neg]
    rw [e, Real.norm_eq_abs, abs_mul, abs_of_pos hβ0, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hβ0.le
    have h1 : |θ * mRuleInfl S β sbar shat θ u ε t ω| ≤ |θ| * ruleBound β sbar M θ Mu ε t := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (mRuleInfl_bound S hβ0 hβ1 hu hω hε t) (abs_nonneg θ)
    have h2 : |ε * u t ω| ≤ |ε| * Mu := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hu t ω) (abs_nonneg ε)
    linarith [neg_abs_le (θ * mRuleInfl S β sbar shat θ u ε t ω), neg_abs_le (ε * u t ω)]

/-! ### Each member is an equilibrium satisfying the exact rule, and the only one -/

/-- Cochrane (2023), §2.6, p. 40, on a probability space: for every `ε ∈ famDom` the rule family
member is an equilibrium (`0 < β < 1`, bounded adapted `ŝ` and `u`, positive initial debt known
at `0`), for every `θ`. -/
theorem mRule_equilibrium (hβ0 : 0 < β) (hβ1 : β < 1) (hsad : StronglyAdapted S.𝓕 shat)
    (hs : ∀ t ω, |shat t ω| ≤ M) (hua : StronglyAdapted S.𝓕 u) (hu : ∀ t ω, |u t ω| ≤ Mu)
    (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1) (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω) {ε : ℝ}
    (hε : ε ∈ famDom sbar M) :
    MEquilibrium S β Bm1 (surpFam sbar shat ε)
      (mFamB S β sbar shat Bm1 (mRuleRate S β sbar shat θ u) ε)
      (mFamP S β sbar shat Bm1 (mRuleRate S β sbar shat θ u) ε)
      (mRuleRate S β sbar shat θ u ε) :=
  mFam_equilibrium S hβ0 hβ1 hsad hs hBm1 hB (fun ε _ => mRuleRate_sm S hua ε)
    (fun ε _ t ω => mRuleRate_gt S hβ0 ε t ω)
    (fun _ hε t => mRuleRate_bondPrice_integrable S hβ0 hβ1 hs hua hu hB hε t) hε

/-- Cochrane (2023), p. 40: in every state where the bounds of `good_ae` hold, on `famDom` the
family's inflation is the closed form `mRuleInfl`. -/
theorem mFamInfl_eq (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar) {ω : Ω}
    (hω : 0 < Bm1 ω ∧ ∀ t, |S.forwardSol β shat t ω| ≤ (1 - β)⁻¹ * M ∧
      |pvExM S β shat t ω| ≤ β * ((1 - β)⁻¹ * M))
    {ε : ℝ} (hε : ε ∈ famDom sbar M) (t : ℕ) :
    mFamInfl S β sbar shat Bm1 (mRuleRate S β sbar shat θ u) ε t ω =
      mRuleInfl S β sbar shat θ u ε t ω := by
  have hV : 0 < ssV β sbar := mul_pos (inv_pos.mpr (by linarith)) hsbar
  have hiG : ∀ ε ∈ famDom sbar M, ∀ t ω, -1 < mRuleRate S β sbar shat θ u ε t ω :=
    fun ε _ t ω => mRuleRate_gt S hβ0 ε t ω
  cases t with
  | zero =>
    change Real.log (Bm1 ω / pvAff S β sbar shat ε 0 ω / (Bm1 ω / ssV β sbar)) =
      Real.log (ssV β sbar) - Real.log (pvAff S β sbar shat ε 0 ω)
    have h3 : 0 < pvAff S β sbar shat ε 0 ω := aff_pos (sbar := sbar) hβ1 (hω.2 0).1 hε
    have hB' := hω.1.ne'
    rw [show Bm1 ω / pvAff S β sbar shat ε 0 ω / (Bm1 ω / ssV β sbar) =
        ssV β sbar / pvAff S β sbar shat ε 0 ω by field_simp,
      Real.log_div hV.ne' h3.ne']
  | succ t =>
    have hP := mFamP_pos S hβ0 hβ1 hω hiG hε t
    have h1 : 0 < 1 + mRuleRate S β sbar shat θ u ε t ω := by linarith [hiG ε hε t ω]
    have h2 : 0 < pvExAff S β sbar shat ε t ω := affEx_pos hβ0 hβ1 (hω.2 t).2 hε
    have h3 : 0 < pvAff S β sbar shat ε (t + 1) ω := aff_pos hβ1 (hω.2 (t + 1)).1 hε
    change Real.log ((1 + mRuleRate S β sbar shat θ u ε t ω) *
      mFamP S β sbar shat Bm1 (mRuleRate S β sbar shat θ u) ε t ω *
      pvExAff S β sbar shat ε t ω / pvAff S β sbar shat ε (t + 1) ω /
      mFamP S β sbar shat Bm1 (mRuleRate S β sbar shat θ u) ε t ω) = _
    have hP' := hP.ne'
    rw [show (1 + mRuleRate S β sbar shat θ u ε t ω) *
        mFamP S β sbar shat Bm1 (mRuleRate S β sbar shat θ u) ε t ω *
        pvExAff S β sbar shat ε t ω / pvAff S β sbar shat ε (t + 1) ω /
        mFamP S β sbar shat Bm1 (mRuleRate S β sbar shat θ u) ε t ω =
        (1 + mRuleRate S β sbar shat θ u ε t ω) * pvExAff S β sbar shat ε t ω /
          pvAff S β sbar shat ε (t + 1) ω by field_simp,
      Real.log_div (mul_pos h1 h2).ne' h3.ne', Real.log_mul h1.ne' h2.ne',
      log_one_add_mRuleRate S hβ0]
    rfl

/-- Cochrane (2023), eq. (2.22), p. 40, on a probability space: on `famDom` the family satisfies
the exact rule almost surely. -/
theorem mRule_exact (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar)
    (hs : ∀ t ω, |shat t ω| ≤ M) (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω) {ε : ℝ}
    (hε : ε ∈ famDom sbar M) :
    MRuleExact S β θ Bm1 (ssV β sbar) u ε
      (mFamP S β sbar shat Bm1 (mRuleRate S β sbar shat θ u) ε)
      (mRuleRate S β sbar shat θ u ε) := by
  intro t
  filter_upwards [good_ae S hβ0 hβ1 hs hB] with ω hω
  rw [log_one_add_mRuleRate S hβ0]
  have e : logInfl Bm1 (ssV β sbar) (mFamP S β sbar shat Bm1 (mRuleRate S β sbar shat θ u) ε)
      t ω = mFamInfl S β sbar shat Bm1 (mRuleRate S β sbar shat θ u) ε t ω := by
    cases t <;> rfl
  rw [e, mFamInfl_eq S hβ0 hβ1 hsbar hω hε t]

/-- Cochrane (2023), §§2.1–2.4, pp. 21–33, on a probability space: an equilibrium remains an
equilibrium when its rate is replaced by an adapted rate equal to it almost surely at every
date. -/
theorem mEquilibrium_congr_rate {s B P i i' : ℕ → Ω → ℝ} (h : MEquilibrium S β Bm1 s B P i)
    (hi'a : StronglyAdapted S.𝓕 i') (hi : ∀ t, i' t =ᵐ[S.μ] i t) :
    MEquilibrium S β Bm1 s B P i' := by
  obtain ⟨hPa, hP, hBa, -, hint, hv, hbp⟩ := h
  refine ⟨hPa, hP, hBa, hi'a, hint, hv, fun t => ?_⟩
  filter_upwards [hbp t, hi t] with ω h1 h2
  rw [h2]
  exact h1

/-- Cochrane (2023), §2.6, p. 40 (the rule's equilibrium is unique, for every `θ`), on a
probability space: for every `ε ∈ famDom`, any equilibrium `(B, P, i)` with surpluses `s(ε)`
whose rate satisfies the exact rule almost surely equals the family member almost surely at
every date. -/
theorem mRule_unique (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar)
    (hsad : StronglyAdapted S.𝓕 shat) (hs : ∀ t ω, |shat t ω| ≤ M)
    (hua : StronglyAdapted S.𝓕 u) (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω) {ε : ℝ}
    (hε : ε ∈ famDom sbar M) {B P i : ℕ → Ω → ℝ}
    (h : MEquilibrium S β Bm1 (surpFam sbar shat ε) B P i)
    (hr : MRuleExact S β θ Bm1 (ssV β sbar) u ε P i) (t : ℕ) :
    i t =ᵐ[S.μ] mRuleRate S β sbar shat θ u ε t ∧
      P t =ᵐ[S.μ] mFamP S β sbar shat Bm1 (mRuleRate S β sbar shat θ u) ε t ∧
      B t =ᵐ[S.μ] mFamB S β sbar shat Bm1 (mRuleRate S β sbar shat θ u) ε t := by
  have hV : 0 < ssV β sbar := mul_pos (inv_pos.mpr (by linarith)) hsbar
  have hε' : |ε| * M < sbar := hε
  have hc0 : 0 < (1 - β)⁻¹ * (sbar - |ε| * M) := mul_pos (inv_pos.mpr (by linarith))
    (by linarith)
  have hpv : ∀ t, ∀ᵐ ω ∂S.μ, 0 < S.forwardSol β (surpFam sbar shat ε) t ω := fun t =>
    (forwardSol_surpFam_ge S hβ0 hβ1 hsad hs ε t).mono fun ω h => lt_of_lt_of_le hc0 h
  have hgood := good_ae S hβ0 hβ1 hs hB
  have hinfl : ∀ t, ∀ᵐ ω ∂S.μ,
      logInfl Bm1 (ssV β sbar) P t ω = mRuleInfl S β sbar shat θ u ε t ω := by
    intro t
    induction t with
    | zero =>
      filter_upwards [mPrice_zero S h (hpv 0),
        forwardSol_surpFam S (sbar := sbar) hβ0.le hβ1 hsad hs ε 0, hgood] with ω h1 h2 hω
      change Real.log (P 0 ω / (Bm1 ω / ssV β sbar)) = Real.log (ssV β sbar) -
        Real.log (pvAff S β sbar shat ε 0 ω)
      have h3 : 0 < pvAff S β sbar shat ε 0 ω := aff_pos (sbar := sbar) hβ1 (hω.2 0).1 hε
      have hB' := hω.1.ne'
      rw [h1, h2, show Bm1 ω / pvAff S β sbar shat ε 0 ω / (Bm1 ω / ssV β sbar) =
          ssV β sbar / pvAff S β sbar shat ε 0 ω by field_simp, Real.log_div hV.ne' h3.ne']
    | succ t ih =>
      filter_upwards [ih, mPrice_succ S h t (hpv (t + 1)), mDebt_eq S hβ0 h t (hpv (t + 1)),
        forwardSol_surpFam S (sbar := sbar) hβ0.le hβ1 hsad hs ε (t + 1),
        pvExM_surpFam S (sbar := sbar) hβ0.le hβ1 hsad hs ε t, hgood, h.2.1 t,
        mEqm_rate_gt S hβ0 h t, hr t] with ω h0 h1 h2 h3 h4 hω hPt hit hrt
      have h2' : B t ω = (1 + i t ω) * P t ω * pvExM S β (surpFam sbar shat ε) t ω := h2
      change Real.log (P (t + 1) ω / P t ω) = -Real.log β +
        θ * mRuleInfl S β sbar shat θ u ε t ω + ε * u t ω +
        Real.log (pvExAff S β sbar shat ε t ω) - Real.log (pvAff S β sbar shat ε (t + 1) ω)
      have hA : 0 < pvExAff S β sbar shat ε t ω := affEx_pos hβ0 hβ1 (hω.2 t).2 hε
      have hC : 0 < pvAff S β sbar shat ε (t + 1) ω := aff_pos hβ1 (hω.2 (t + 1)).1 hε
      have hi1 : 0 < 1 + i t ω := by linarith
      have hPt' := hPt.ne'
      rw [h1, h2', h3, h4, show (1 + i t ω) * P t ω * pvExAff S β sbar shat ε t ω /
          pvAff S β sbar shat ε (t + 1) ω / P t ω =
          (1 + i t ω) * pvExAff S β sbar shat ε t ω / pvAff S β sbar shat ε (t + 1) ω by
          field_simp, Real.log_div (mul_pos hi1 hA).ne' hC.ne', Real.log_mul hi1.ne' hA.ne',
        hrt, h0]
  have hi : ∀ t, i t =ᵐ[S.μ] mRuleRate S β sbar shat θ u ε t := fun t => by
    filter_upwards [hinfl t, hr t, mEqm_rate_gt S hβ0 h t] with ω h1 h2 h3
    have hi1 : 0 < 1 + i t ω := by linarith
    rw [h1] at h2
    have e2 := congrArg Real.exp h2
    rw [Real.exp_log hi1, Real.exp_add, Real.exp_add, Real.exp_neg, Real.exp_log hβ0] at e2
    change i t ω = β⁻¹ * Real.exp (θ * mRuleInfl S β sbar shat θ u ε t ω + ε * u t ω) - 1
    rw [Real.exp_add]
    linarith
  have h' := mEquilibrium_congr_rate S h (mRuleRate_sm S hua ε) fun t => (hi t).symm
  obtain ⟨h1, h2⟩ := mFam_unique S hβ0 hβ1 hsad hs hε h' t
  exact ⟨hi t, h1, h2⟩

/-! ### Smoothness and the derivative -/

/-- Cochrane (2023), p. 40: in every state where the bounds of `good_ae` hold, inflation and the
rate of the rule family are `C^n` in `ε` on `famDom` (every `n`). -/
theorem mRule_contDiffOn (hβ0 : 0 < β) (hβ1 : β < 1) {n : WithTop ℕ∞} {ω : Ω}
    (hω : 0 < Bm1 ω ∧ ∀ t, |S.forwardSol β shat t ω| ≤ (1 - β)⁻¹ * M ∧
      |pvExM S β shat t ω| ≤ β * ((1 - β)⁻¹ * M)) (t : ℕ) :
    ContDiffOn ℝ n (fun ε => mRuleInfl S β sbar shat θ u ε t ω) (famDom sbar M) ∧
      ContDiffOn ℝ n (fun ε => mRuleRate S β sbar shat θ u ε t ω) (famDom sbar M) := by
  have hpv : ∀ t, ContDiff ℝ n (fun ε => pvAff S β sbar shat ε t ω) := fun t =>
    contDiff_const.add (contDiff_id.mul contDiff_const)
  have hpvE : ∀ t, ContDiff ℝ n (fun ε => pvExAff S β sbar shat ε t ω) := fun t =>
    contDiff_const.add (contDiff_id.mul contDiff_const)
  have hI : ∀ t, ContDiffOn ℝ n (fun ε => mRuleInfl S β sbar shat θ u ε t ω)
      (famDom sbar M) := by
    intro t
    induction t with
    | zero =>
      exact contDiffOn_const.sub ((hpv 0).contDiffOn.log
        fun ε hε => (aff_pos hβ1 (hω.2 0).1 hε).ne')
    | succ t ih =>
      exact ((((contDiffOn_const.add (contDiffOn_const.mul ih)).add
        (contDiffOn_id.mul contDiffOn_const)).add
        ((hpvE t).contDiffOn.log fun ε hε => (affEx_pos hβ0 hβ1 (hω.2 t).2 hε).ne')).sub
        ((hpv (t + 1)).contDiffOn.log fun ε hε => (aff_pos hβ1 (hω.2 (t + 1)).1 hε).ne'))
  exact ⟨hI t, (contDiffOn_const.mul ((contDiffOn_const.mul (hI t)).add
    (contDiffOn_id.mul contDiffOn_const)).exp).sub contDiffOn_const⟩

/-- Cochrane (2023), eq. (2.25), p. 40, on a probability space: in every state, the derivative at
`ε = 0` of the closed-form inflation of the rule family is the solution
`LinearFTMP.ruleSol θ u ε_{Σs} π̂_0` of the linear model (`ε_{Σs}` = `TidyR5MeasFamily.mShock`,
`π̂_0` = `TidyR5MeasFamily.mInfl0`), for every `θ`. -/
theorem mRuleInfl_hasDerivAt (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => mRuleInfl S β sbar shat θ u ε t ω)
      (LinearFTMP.ruleSol θ u (mShock S β sbar shat) (mInfl0 S β sbar shat) t ω) 0 := by
  have hV : 0 < ssV β sbar := mul_pos (inv_pos.mpr (by linarith)) hsbar
  have hlogpv : ∀ t, HasDerivAt (fun ε => Real.log (pvAff S β sbar shat ε t ω))
      (S.forwardSol β shat t ω / ssV β sbar) 0 := by
    intro t
    have hA0 : HasDerivAt (fun ε => ssV β sbar + ε * S.forwardSol β shat t ω)
        (S.forwardSol β shat t ω) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (S.forwardSol β shat t ω)).const_add
        (ssV β sbar)
    have hA : HasDerivAt (fun ε => pvAff S β sbar shat ε t ω) (S.forwardSol β shat t ω) 0 :=
      hA0
    have h0 : pvAff S β sbar shat 0 t ω = ssV β sbar := by
      simp [pvAff]
    have := hA.log (by rw [h0]; exact hV.ne')
    rwa [h0] at this
  have hlogpvE : ∀ t, HasDerivAt (fun ε => Real.log (pvExAff S β sbar shat ε t ω))
      (pvExM S β shat t ω / (β * ssV β sbar)) 0 := by
    intro t
    have hA0 : HasDerivAt (fun ε => β * ssV β sbar + ε * pvExM S β shat t ω)
        (pvExM S β shat t ω) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (pvExM S β shat t ω)).const_add
        (β * ssV β sbar)
    have hA : HasDerivAt (fun ε => pvExAff S β sbar shat ε t ω) (pvExM S β shat t ω) 0 := hA0
    have h0 : pvExAff S β sbar shat 0 t ω = β * ssV β sbar := by
      simp [pvExAff]
    have := hA.log (by rw [h0]; exact (mul_pos hβ0 hV).ne')
    rwa [h0] at this
  induction t with
  | zero =>
    refine ((hlogpv 0).const_sub (Real.log (ssV β sbar))).congr_deriv ?_
    change -(S.forwardSol β shat 0 ω / ssV β sbar) =
      -((ssV β sbar)⁻¹ * S.forwardSol β shat 0 ω)
    rw [div_eq_inv_mul]
  | succ t ih =>
    have hL := HasDerivAt.sub (HasDerivAt.add (HasDerivAt.add (HasDerivAt.const_add
      (-Real.log β) (ih.const_mul θ)) ((hasDerivAt_id (0 : ℝ)).mul_const (u t ω)))
      (hlogpvE t)) (hlogpv (t + 1))
    refine hL.congr_deriv ?_
    have hXe : pvExM S β shat t ω = β * S.E t (S.forwardSol β shat (t + 1)) ω := rfl
    have hsh : mShock S β sbar shat (t + 1) ω = (ssV β sbar)⁻¹ *
        (S.forwardSol β shat (t + 1) ω - S.E t (S.forwardSol β shat (t + 1)) ω) := by
      change (ssV β sbar)⁻¹ * (S.E (t + 1) (S.forwardSol β shat (t + 1)) ω -
        S.E t (S.forwardSol β shat (t + 1)) ω) = _
      rw [show S.E (t + 1) (S.forwardSol β shat (t + 1)) = S.forwardSol β shat (t + 1) from
        S.E_E_self (t + 1) _]
    change θ * LinearFTMP.ruleSol θ u (mShock S β sbar shat) (mInfl0 S β sbar shat) t ω +
        id 1 * u t ω + pvExM S β shat t ω / (β * ssV β sbar) -
        S.forwardSol β shat (t + 1) ω / ssV β sbar =
      θ * LinearFTMP.ruleSol θ u (mShock S β sbar shat) (mInfl0 S β sbar shat) t ω +
        u t ω - mShock S β sbar shat (t + 1) ω
    rw [hsh, hXe, id]
    have := hV.ne'
    have := hβ0.ne'
    field_simp
    ring

/-- Cochrane (2023), eqs. (2.22) and (2.25), p. 40, on a probability space: in every state, the
derivative at `ε = 0` of the log gross rate of the rule family is the linear model's rate
`θ π̂_t + u_t`. -/
theorem mRule_rate_hasDerivAt (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar) (t : ℕ)
    (ω : Ω) : HasDerivAt (fun ε => Real.log (1 + mRuleRate S β sbar shat θ u ε t ω))
      (θ * LinearFTMP.ruleSol θ u (mShock S β sbar shat) (mInfl0 S β sbar shat) t ω +
        u t ω) 0 := by
  have e : (fun ε => Real.log (1 + mRuleRate S β sbar shat θ u ε t ω)) =
      fun ε => -Real.log β + θ * mRuleInfl S β sbar shat θ u ε t ω + ε * u t ω :=
    funext fun ε => log_one_add_mRuleRate S hβ0 ε t ω
  rw [e]
  have h := HasDerivAt.add (((mRuleInfl_hasDerivAt S (shat := shat) (θ := θ) (u := u) hβ0 hβ1
    hsbar t ω).const_mul θ).const_add (-Real.log β)) ((hasDerivAt_id (0 : ℝ)).mul_const (u t ω))
  exact h.congr_deriv (by simp)

/-- Cochrane (2023), §2.6, pp. 39–42, **the linear rule model is the derivative of the family of
exact equilibria on a genuine probability space**, for every `θ ∈ ℝ`. With `0 < β < 1`,
`s̄ > 0`, bounded adapted `ŝ` and `u`, and positive initial debt known at `0`, on `famDom`:
* each family member is an equilibrium satisfying the exact rule almost surely, and every such
  equilibrium equals it almost surely at every date;
* almost surely, price level, debt and inflation are `C^n` in `ε` for every `n`;
* the linear rule model with `ε_{Σs} = mShock` and `π̂_0 = mInfl0` has an adapted integrable
  solution, unique up to null sets, and every adapted integrable solution `(π̂, î)` is, at every
  date and almost surely, the derivative at `ε = 0` of inflation and of the log gross rate
  along the family. -/
theorem mRule_family_linearization (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar)
    (hsad : StronglyAdapted S.𝓕 shat) (hs : ∀ t ω, |shat t ω| ≤ M)
    (hua : StronglyAdapted S.𝓕 u) (hu : ∀ t ω, |u t ω| ≤ Mu)
    (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1) (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω) :
    (∀ ε ∈ famDom sbar M, MEquilibrium S β Bm1 (surpFam sbar shat ε)
      (mFamB S β sbar shat Bm1 (mRuleRate S β sbar shat θ u) ε)
      (mFamP S β sbar shat Bm1 (mRuleRate S β sbar shat θ u) ε)
      (mRuleRate S β sbar shat θ u ε) ∧
      MRuleExact S β θ Bm1 (ssV β sbar) u ε
        (mFamP S β sbar shat Bm1 (mRuleRate S β sbar shat θ u) ε)
        (mRuleRate S β sbar shat θ u ε)) ∧
    (∀ ε ∈ famDom sbar M, ∀ B P i : ℕ → Ω → ℝ,
      MEquilibrium S β Bm1 (surpFam sbar shat ε) B P i →
      MRuleExact S β θ Bm1 (ssV β sbar) u ε P i → ∀ t,
        i t =ᵐ[S.μ] mRuleRate S β sbar shat θ u ε t ∧
        P t =ᵐ[S.μ] mFamP S β sbar shat Bm1 (mRuleRate S β sbar shat θ u) ε t ∧
        B t =ᵐ[S.μ] mFamB S β sbar shat Bm1 (mRuleRate S β sbar shat θ u) ε t) ∧
    (∀ n : WithTop ℕ∞, ∀ᵐ ω ∂S.μ, ∀ t : ℕ,
      ContDiffOn ℝ n (fun ε => mFamP S β sbar shat Bm1 (mRuleRate S β sbar shat θ u) ε t ω)
        (famDom sbar M) ∧
      ContDiffOn ℝ n (fun ε => mFamB S β sbar shat Bm1 (mRuleRate S β sbar shat θ u) ε t ω)
        (famDom sbar M) ∧
      ContDiffOn ℝ n (fun ε => mFamInfl S β sbar shat Bm1 (mRuleRate S β sbar shat θ u) ε t ω)
        (famDom sbar M)) ∧
    ((StronglyAdapted S.𝓕
        (LinearFTMP.ruleSol θ u (mShock S β sbar shat) (mInfl0 S β sbar shat)) ∧
      (∀ t, Integrable
        (LinearFTMP.ruleSol θ u (mShock S β sbar shat) (mInfl0 S β sbar shat) t) S.μ) ∧
      MRuleModel S θ (fun t => θ • LinearFTMP.ruleSol θ u (mShock S β sbar shat)
        (mInfl0 S β sbar shat) t + u t) u (mShock S β sbar shat)
        (LinearFTMP.ruleSol θ u (mShock S β sbar shat) (mInfl0 S β sbar shat))) ∧
    ∀ q : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), StronglyAdapted S.𝓕 q.1 →
      (∀ t, Integrable (q.1 t) S.μ) → q.1 0 =ᵐ[S.μ] mInfl0 S β sbar shat →
      MRuleModel S θ q.2 u (mShock S β sbar shat) q.1 → ∀ t, ∀ᵐ ω ∂S.μ,
        HasDerivAt (fun ε => mFamInfl S β sbar shat Bm1 (mRuleRate S β sbar shat θ u) ε t ω)
          (q.1 t ω) 0 ∧
        HasDerivAt (fun ε => Real.log (1 + mRuleRate S β sbar shat θ u ε t ω)) (q.2 t ω) 0) := by
  have hui : ∀ t, Integrable (u t) S.μ := fun t =>
    MeasExpectationSystem.BddRV.integrable
      ⟨((hua t).mono (S.𝓕.le t)).aestronglyMeasurable, Mu, Eventually.of_forall (hu t)⟩
  obtain ⟨h0, h0i⟩ := mInfl0_sm_integrable S (β := β) (sbar := sbar) (shat := shat)
  obtain ⟨hex, huniq⟩ := mRule_linear_existsUnique S θ hua hui (mShock_isShock S) h0 h0i
  have hgood := good_ae S hβ0 hβ1 hs hB
  refine ⟨fun ε hε => ⟨mRule_equilibrium S hβ0 hβ1 hsad hs hua hu hBm1 hB hε,
      mRule_exact S hβ0 hβ1 hsbar hs hB hε⟩,
    fun ε hε B P i h hr t => mRule_unique S hβ0 hβ1 hsbar hsad hs hua hB hε h hr t,
    fun n => mFam_contDiffOn S hβ0 hβ1 hsbar hs hB (fun ε _ t ω => mRuleRate_gt S hβ0 ε t ω)
      (hgood.mono fun ω hω t => (mRule_contDiffOn S hβ0 hβ1 hω t).2), ⟨hex, ?_⟩⟩
  intro q hπ hπi hπ0 hm t
  obtain ⟨h1, h2⟩ := huniq q hπ hπi hπ0 hm t
  filter_upwards [h1, h2, hgood] with ω e1 e2 hω
  refine ⟨?_, ?_⟩
  · rw [e1]
    refine (mRuleInfl_hasDerivAt S hβ0 hβ1 hsbar t ω).congr_of_eventuallyEq ?_
    filter_upwards [famDom_mem_nhds hsbar M] with ε hε
    exact mFamInfl_eq S hβ0 hβ1 hsbar hω hε t
  · rw [e2]
    change HasDerivAt _ (θ * LinearFTMP.ruleSol θ u (mShock S β sbar shat)
      (mInfl0 S β sbar shat) t ω + u t ω) 0
    exact mRule_rate_hasDerivAt S hβ0 hβ1 hsbar t ω

/-! ### The link to the rule family on a finite tree -/

namespace Link

open ExpectationsFiniteTree TreeBridge TidyR5MeasLinear.Link

variable {Ω' : Type*} [Fintype Ω'] [MeasurableSpace Ω'] [DiscreteMeasurableSpace Ω']
  (T : FiniteTree Ω')

/-- Cochrane (2023), §2.6, p. 40: on a finite tree the measure-theoretic rule family's inflation
and rate are `TidyR5FamilyRule.ruleInfl` and `TidyR5FamilyRule.ruleRate`, so its price level is
`TidyR5Family.priceFam` for the rate `ruleRate` (bounded `ŝ`, `0 ≤ β < 1`). -/
theorem tree_mRuleRate (hβ0 : 0 ≤ β) (hβ1 : β < 1) {shat' u' : ℕ → Ω' → ℝ}
    (hs : ∀ t ω, |shat' t ω| ≤ M) (Bm1' : Ω' → ℝ) (ε : ℝ) :
    mRuleInfl (treeSystem T) β sbar shat' θ u' ε =
        ruleInfl T.toExpectationSystem β sbar shat' θ u' ε ∧
      mRuleRate (treeSystem T) β sbar shat' θ u' =
        ruleRate T.toExpectationSystem β sbar shat' θ u' ∧
      ∀ t, mFamP (treeSystem T) β sbar shat' Bm1' (mRuleRate (treeSystem T) β sbar shat' θ u') ε
        t = priceFam T.toExpectationSystem β sbar shat' Bm1'
          (ruleRate T.toExpectationSystem β sbar shat' θ u') ε t := by
  have hpv : ∀ ε t, pvAff (treeSystem T) β sbar shat' ε t =
      FiscalMonetary.pv T.toExpectationSystem β (surpFam sbar shat' ε) t := fun ε t => by
    rw [pv_surpFam T.toExpectationSystem hβ0 hβ1 hs]
    funext ω
    simp only [pvAff, tree_forwardSol]
  have hpvE : ∀ ε t, pvExAff (treeSystem T) β sbar shat' ε t =
      FiscalMonetary.pvEx T.toExpectationSystem β (surpFam sbar shat' ε) t := fun ε t => by
    rw [pvEx_surpFam T.toExpectationSystem hβ0 hβ1 hs]
    funext ω
    simp only [pvExAff, tree_pvExM]
  have hI : ∀ ε, mRuleInfl (treeSystem T) β sbar shat' θ u' ε =
      ruleInfl T.toExpectationSystem β sbar shat' θ u' ε := by
    intro ε
    funext t
    induction t with
    | zero =>
      funext ω
      change Real.log (ssV β sbar) - Real.log (pvAff (treeSystem T) β sbar shat' ε 0 ω) = _
      rw [hpv]
      rfl
    | succ t ih =>
      funext ω
      change -Real.log β + θ * mRuleInfl (treeSystem T) β sbar shat' θ u' ε t ω + ε * u' t ω +
        Real.log (pvExAff (treeSystem T) β sbar shat' ε t ω) -
        Real.log (pvAff (treeSystem T) β sbar shat' ε (t + 1) ω) = _
      rw [ih, hpv, hpvE]
      rfl
  have hR : mRuleRate (treeSystem T) β sbar shat' θ u' =
      ruleRate T.toExpectationSystem β sbar shat' θ u' := by
    funext ε t ω
    change β⁻¹ * Real.exp (θ * mRuleInfl (treeSystem T) β sbar shat' θ u' ε t ω + ε * u' t ω) - 1
      = _
    rw [hI]
    rfl
  refine ⟨hI ε, hR, fun t => ?_⟩
  rw [hR]
  exact (TidyR5MeasFamily.Link.tree_mFamP (sbar := sbar) T hβ0 hβ1 hs Bm1' _ ε t).1

end Link

end Cochrane.IntertemporalModel.TidyR5MeasFamilyRule
