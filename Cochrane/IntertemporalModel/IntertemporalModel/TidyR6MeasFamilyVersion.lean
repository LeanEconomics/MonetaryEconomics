/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.TidyR5MeasFamilyRule
import IntertemporalModel.TidyR6MeasHyp

/-!
# The families of exact equilibria with chosen versions: smooth in every state

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.4, pp. 29–33, §2.5,
pp. 34–37 (the peg family whose derivative is (2.19)) and §2.6, pp. 39–42 (the rule family whose
derivative is (2.25)), on a probability space.

`TidyR5MeasFamily` and `TidyR5MeasFamilyRule` assume `ŝ`, `î` and `u` bounded in every state,
and their smoothness and derivatives hold only almost surely, because the fixed versions
`MeasExpectationSystem.forwardSol` of the present values are bounded only almost surely. This
module removes both restrictions.

* The family is written for arbitrary versions `Y`, `X` of the present value and ex-dividend
  present value of `ŝ`: `vFamP`, `vFamB`, `vFamInfl`, `vShock`, `vInfl0`, and under the rule
  `vRuleInfl`, `vRuleRate`.
* Chosen versions: `pvVer`, `pvExVer` (present values clamped to their almost-sure bounds,
  `clamp`), and `procVer` for `ŝ` and `u`. They are adapted, bounded in every state and equal to the
  originals almost surely.
* `ŝ` and `u` need only be bounded almost surely; for `î` the hypothesis is the integrability of
  `exp(−ε î_t)` on the domain, which is necessary (`rateExp_bondPrice_iff` with
  `TidyR6MeasHyp.mEqm_bondPrice_integrable`), plus the integrability of `î` for the linear model.
* `version_family_linearization` (peg) and `version_rule_linearization` (rule, every `θ`): each
  family member is an equilibrium, unique almost surely; price level, debt and inflation are
  `C^n` in `ε` **in every state**; the derivative at `ε = 0` is **in every state with
  `B_{−1} ≠ 0`** the solution of the linear model with the version shock `vShock`, which is a
  shock and equals `TidyR5MeasFamily.mShock` almost surely; and the families agree with those of
  `TidyR5MeasFamily` almost surely, for all `ε` at once.
* What is necessary: `pv_bound_necessary` (if present values `V + ε Y` stay positive almost surely
  for all `|ε| < δ` then `|Y| ≤ V/δ` almost surely) and `shat_bound_of_pv_bound` (bounded present
  values give bounded surpluses), so almost-sure boundedness of `ŝ` is the exact condition for a
  family on a neighbourhood of `ε = 0`; `vFamInfl_zero_of` shows the derivative statement needs
  `B_{−1} ≠ 0` (where `B_{−1} = 0` inflation is identically `0`).
-/

namespace Cochrane.IntertemporalModel.TidyR6MeasFamilyVersion

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure TidyR5Meas
  TidyR5MeasLinear TidyR5Family TidyR5FamilyRule TidyR5MeasFamily TidyR5MeasFamilyRule

variable {Ω : Type*}

/-! ### The family for given versions of the present values -/

/-- Cochrane (2023), §2.4.3, p. 31: the price level of the family for versions `Y` (present
value of `ŝ`) and `X` (ex-dividend present value of `ŝ`), `P_0 = B_{−1}/(V + εY_0)`,
`P_{t+1} = (1 + i_t(ε)) P_t (βV + εX_t)/(V + εY_{t+1})`. -/
noncomputable def vFamP (β sbar : ℝ) (Y X : ℕ → Ω → ℝ) (Bm1 : Ω → ℝ) (iF : ℝ → ℕ → Ω → ℝ)
    (ε : ℝ) : ℕ → Ω → ℝ
  | 0 => fun ω => Bm1 ω / (ssV β sbar + ε * Y 0 ω)
  | t + 1 => fun ω => (1 + iF ε t ω) * vFamP β sbar Y X Bm1 iF ε t ω *
      (β * ssV β sbar + ε * X t ω) / (ssV β sbar + ε * Y (t + 1) ω)

/-- Cochrane (2023), eq. (2.15), p. 31: the debt sold along the family for versions `Y`, `X`. -/
noncomputable def vFamB (β sbar : ℝ) (Y X : ℕ → Ω → ℝ) (Bm1 : Ω → ℝ) (iF : ℝ → ℕ → Ω → ℝ)
    (ε : ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (1 + iF ε t ω) * vFamP β sbar Y X Bm1 iF ε t ω * (β * ssV β sbar + ε * X t ω)

/-- Cochrane (2023), §2.5, p. 35: inflation along the family for versions `Y`, `X`. -/
noncomputable def vFamInfl (β sbar : ℝ) (Y X : ℕ → Ω → ℝ) (Bm1 : Ω → ℝ)
    (iF : ℝ → ℕ → Ω → ℝ) (ε : ℝ) : ℕ → Ω → ℝ
  | 0 => fun ω => Real.log (vFamP β sbar Y X Bm1 iF ε 0 ω / (Bm1 ω / ssV β sbar))
  | t + 1 => fun ω => Real.log (vFamP β sbar Y X Bm1 iF ε (t + 1) ω /
      vFamP β sbar Y X Bm1 iF ε t ω)

/-- Cochrane (2023), eq. (2.17), p. 35: the fiscal shock for versions `Y`, `X`,
`ε_{Σs,t+1} = V⁻¹(Y_{t+1} − X_t/β)`, zero at date `0`. -/
noncomputable def vShock (β sbar : ℝ) (Y X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => fun ω => (ssV β sbar)⁻¹ * (Y (t + 1) ω - β⁻¹ * X t ω)

/-- Cochrane (2023), eq. (2.17), p. 35: initial inflation of the linear model for the version
`Y`, `π̂_0 = −Y_0/V`. -/
noncomputable def vInfl0 (β sbar : ℝ) (Y : ℕ → Ω → ℝ) : Ω → ℝ :=
  fun ω => -((ssV β sbar)⁻¹ * Y 0 ω)

/-- Cochrane (2023), eqs. (2.20)–(2.22), p. 40: inflation of the rule family for versions `Y`,
`X`, `π_0 = log V − log(V + εY_0)`,
`π_{t+1} = −log β + θπ_t + εu_t + log(βV + εX_t) − log(V + εY_{t+1})`. -/
noncomputable def vRuleInfl (β sbar : ℝ) (Y X : ℕ → Ω → ℝ) (θ : ℝ) (u : ℕ → Ω → ℝ) (ε : ℝ) :
    ℕ → Ω → ℝ
  | 0 => fun ω => Real.log (ssV β sbar) - Real.log (ssV β sbar + ε * Y 0 ω)
  | t + 1 => fun ω => -Real.log β + θ * vRuleInfl β sbar Y X θ u ε t ω + ε * u t ω +
      Real.log (β * ssV β sbar + ε * X t ω) - Real.log (ssV β sbar + ε * Y (t + 1) ω)

/-- Cochrane (2023), eq. (2.22), p. 40: the rate of the rule family for versions `Y`, `X`,
`1 + i_t = β⁻¹ exp(θπ_t + εu_t)`. -/
noncomputable def vRuleRate (β sbar : ℝ) (Y X : ℕ → Ω → ℝ) (θ : ℝ) (u : ℕ → Ω → ℝ) (ε : ℝ) :
    ℕ → Ω → ℝ :=
  fun t ω => β⁻¹ * Real.exp (θ * vRuleInfl β sbar Y X θ u ε t ω + ε * u t ω) - 1

/-- Cochrane (2023), eq. (2.7), p. 22: the versions `Y`, `X` obey the bounds
`|Y_t| ≤ M/(1 − β)`, `|X_t| ≤ βM/(1 − β)` in state `ω` at every date. -/
def Bounds (β M : ℝ) (Y X : ℕ → Ω → ℝ) (ω : Ω) : Prop :=
  ∀ t, |Y t ω| ≤ (1 - β)⁻¹ * M ∧ |X t ω| ≤ β * ((1 - β)⁻¹ * M)

variable {β sbar M θ : ℝ} {Y X : ℕ → Ω → ℝ} {Bm1 : Ω → ℝ} {iF : ℝ → ℕ → Ω → ℝ}
  {u : ℕ → Ω → ℝ}

/-! ### State by state: positivity, smoothness and derivatives -/

/-- Cochrane (2023), §2.4.3, p. 31: where `B_{−1} = 0` the family's price level is `0`. -/
theorem vFamP_zero_of {ω : Ω} (hB0 : Bm1 ω = 0) (ε : ℝ) (t : ℕ) :
    vFamP β sbar Y X Bm1 iF ε t ω = 0 := by
  induction t with
  | zero => simp [vFamP, hB0]
  | succ t ih =>
    change (1 + iF ε t ω) * vFamP β sbar Y X Bm1 iF ε t ω * (β * ssV β sbar + ε * X t ω) /
      (ssV β sbar + ε * Y (t + 1) ω) = 0
    rw [ih]
    simp

/-- Cochrane (2023), §2.5, p. 35: where `B_{−1} = 0` the family's inflation is identically `0`
(so its derivative is `0`, not the linear solution). -/
theorem vFamInfl_zero_of {ω : Ω} (hB0 : Bm1 ω = 0) (ε : ℝ) (t : ℕ) :
    vFamInfl β sbar Y X Bm1 iF ε t ω = 0 := by
  cases t with
  | zero => simp [vFamInfl, vFamP_zero_of hB0, hB0]
  | succ t => simp [vFamInfl, vFamP_zero_of hB0]

/-- Cochrane (2023), §2.4.3, p. 31: where the bounds hold and `B_{−1} ≠ 0`, the family's price
level is nonzero on `famDom` (rate family exceeding `−1`). -/
theorem vFamP_ne (hβ0 : 0 < β) (hβ1 : β < 1) {ω : Ω} (hω : Bounds β M Y X ω)
    (hB0 : Bm1 ω ≠ 0) (hiG : ∀ ε ∈ famDom sbar M, ∀ t, -1 < iF ε t ω) {ε : ℝ}
    (hε : ε ∈ famDom sbar M) (t : ℕ) : vFamP β sbar Y X Bm1 iF ε t ω ≠ 0 := by
  induction t with
  | zero => exact div_ne_zero hB0 (aff_pos hβ1 (hω 0).1 hε).ne'
  | succ t ih =>
    have h1 : 1 + iF ε t ω ≠ 0 := by linarith [hiG ε hε t]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero h1 ih) (affEx_pos hβ0 hβ1 (hω t).2 hε).ne')
      (aff_pos hβ1 (hω (t + 1)).1 hε).ne'

/-- Cochrane (2023), §§2.4–2.5, pp. 31–35, **in every state** where the bounds hold (any
`B_{−1}`): if the rate family is `C^n` in `ε` on `famDom`, so are the family's price level, debt
and inflation, at every date.
Generalises `TidyR5MeasFamily.mFam_contDiffOn`. -/
theorem vFam_contDiffOn (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar) {ω : Ω}
    (hω : Bounds β M Y X ω) (hiG : ∀ ε ∈ famDom sbar M, ∀ t, -1 < iF ε t ω) {n : WithTop ℕ∞}
    (hC : ∀ t, ContDiffOn ℝ n (fun ε => iF ε t ω) (famDom sbar M)) (t : ℕ) :
    ContDiffOn ℝ n (fun ε => vFamP β sbar Y X Bm1 iF ε t ω) (famDom sbar M) ∧
      ContDiffOn ℝ n (fun ε => vFamB β sbar Y X Bm1 iF ε t ω) (famDom sbar M) ∧
      ContDiffOn ℝ n (fun ε => vFamInfl β sbar Y X Bm1 iF ε t ω) (famDom sbar M) := by
  have hV : 0 < ssV β sbar := mul_pos (inv_pos.mpr (by linarith)) hsbar
  have hpv : ∀ t, ContDiff ℝ n (fun ε => ssV β sbar + ε * Y t ω) := fun t =>
    contDiff_const.add (contDiff_id.mul contDiff_const)
  have hpvE : ∀ t, ContDiff ℝ n (fun ε => β * ssV β sbar + ε * X t ω) := fun t =>
    contDiff_const.add (contDiff_id.mul contDiff_const)
  have hP : ∀ t, ContDiffOn ℝ n (fun ε => vFamP β sbar Y X Bm1 iF ε t ω) (famDom sbar M) := by
    intro t
    induction t with
    | zero =>
      exact contDiffOn_const.div (hpv 0).contDiffOn
        (fun ε hε => (aff_pos hβ1 (hω 0).1 hε).ne')
    | succ t ih =>
      exact (((contDiffOn_const.add (hC t)).mul ih).mul
        (hpvE t).contDiffOn).div (hpv (t + 1)).contDiffOn
        (fun ε hε => (aff_pos hβ1 (hω (t + 1)).1 hε).ne')
  refine ⟨hP t, ((contDiffOn_const.add (hC t)).mul (hP t)).mul (hpvE t).contDiffOn, ?_⟩
  by_cases hB0 : Bm1 ω = 0
  · have e : (fun ε => vFamInfl β sbar Y X Bm1 iF ε t ω) = fun _ => 0 :=
      funext fun ε => vFamInfl_zero_of hB0 ε t
    rw [e]
    exact contDiffOn_const
  · cases t with
    | zero =>
      exact ((hP 0).div_const _).log fun ε hε =>
        div_ne_zero (vFamP_ne hβ0 hβ1 hω hB0 hiG hε 0) (div_ne_zero hB0 hV.ne')
    | succ t =>
      exact ((hP (t + 1)).div (hP t) (fun ε hε => vFamP_ne hβ0 hβ1 hω hB0 hiG hε t)).log
        fun ε hε => div_ne_zero (vFamP_ne hβ0 hβ1 hω hB0 hiG hε (t + 1))
          (vFamP_ne hβ0 hβ1 hω hB0 hiG hε t)

/-- Cochrane (2023), eqs. (2.16)–(2.17), p. 35, **in every state** where the bounds hold and
`B_{−1} ≠ 0`: the derivative at `ε = 0` of the family's inflation is `π̂_0 = vInfl0` and
`π̂_{t+1} = î'_t − ε_{Σs,t+1}` with the version shock `vShock`, for any rate family exceeding
`−1` on `famDom` whose log gross rate has derivative `î'` at `0` in that state.
Generalises `TidyR5MeasFamily.mFamInfl_hasDerivAt`. -/
theorem vFamInfl_hasDerivAt (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar) {ω : Ω}
    (hω : Bounds β M Y X ω) (hB0 : Bm1 ω ≠ 0) (hiG : ∀ ε ∈ famDom sbar M, ∀ t, -1 < iF ε t ω)
    {ihat' : ℕ → Ω → ℝ}
    (hD : ∀ t, HasDerivAt (fun ε => Real.log (1 + iF ε t ω)) (ihat' t ω) 0) :
    HasDerivAt (fun ε => vFamInfl β sbar Y X Bm1 iF ε 0 ω) (vInfl0 β sbar Y ω) 0 ∧
      ∀ t, HasDerivAt (fun ε => vFamInfl β sbar Y X Bm1 iF ε (t + 1) ω)
        (ihat' t ω - vShock β sbar Y X (t + 1) ω) 0 := by
  have hV : 0 < ssV β sbar := mul_pos (inv_pos.mpr (by linarith)) hsbar
  have hnhds := famDom_mem_nhds hsbar M
  refine ⟨?_, fun t => ?_⟩
  · set y := Y 0 ω with hy
    have hev : (fun ε => vFamInfl β sbar Y X Bm1 iF ε 0 ω) =ᶠ[𝓝 0]
        fun ε => Real.log (ssV β sbar) - Real.log (ssV β sbar + ε * y) := by
      filter_upwards [hnhds] with ε hε
      have h3 := aff_pos hβ1 (hω 0).1 hε
      change Real.log (Bm1 ω / (ssV β sbar + ε * y) / (Bm1 ω / ssV β sbar)) = _
      rw [show Bm1 ω / (ssV β sbar + ε * y) / (Bm1 ω / ssV β sbar) =
          ssV β sbar / (ssV β sbar + ε * y) by field_simp,
        Real.log_div hV.ne' h3.ne']
    have hA : HasDerivAt (fun ε : ℝ => ssV β sbar + ε * y) y 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const y).const_add (ssV β sbar)
    have hL := (hA.log (by simpa using hV.ne')).const_sub (Real.log (ssV β sbar))
    refine (hL.congr_of_eventuallyEq hev).congr_deriv ?_
    change -(y / (ssV β sbar + 0 * y)) = -((ssV β sbar)⁻¹ * y)
    rw [zero_mul, add_zero, div_eq_inv_mul]
  · set x := X t ω with hx
    set y := Y (t + 1) ω with hy
    have hev : (fun ε => vFamInfl β sbar Y X Bm1 iF ε (t + 1) ω) =ᶠ[𝓝 0]
        fun ε => Real.log (1 + iF ε t ω) + Real.log (β * ssV β sbar + ε * x) -
          Real.log (ssV β sbar + ε * y) := by
      filter_upwards [hnhds] with ε hε
      have hP := vFamP_ne hβ0 hβ1 hω hB0 hiG hε t
      have h1 : 0 < 1 + iF ε t ω := by linarith [hiG ε hε t]
      have h2 : 0 < β * ssV β sbar + ε * x := affEx_pos hβ0 hβ1 (hω t).2 hε
      have h3 : 0 < ssV β sbar + ε * y := aff_pos hβ1 (hω (t + 1)).1 hε
      change Real.log ((1 + iF ε t ω) * vFamP β sbar Y X Bm1 iF ε t ω *
        (β * ssV β sbar + ε * x) / (ssV β sbar + ε * y) /
          vFamP β sbar Y X Bm1 iF ε t ω) = _
      rw [show (1 + iF ε t ω) * vFamP β sbar Y X Bm1 iF ε t ω *
          (β * ssV β sbar + ε * x) / (ssV β sbar + ε * y) /
            vFamP β sbar Y X Bm1 iF ε t ω =
          (1 + iF ε t ω) * (β * ssV β sbar + ε * x) / (ssV β sbar + ε * y) by
          field_simp,
        Real.log_div (mul_pos h1 h2).ne' h3.ne', Real.log_mul h1.ne' h2.ne']
    have hA : HasDerivAt (fun ε : ℝ => β * ssV β sbar + ε * x) x 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const x).const_add (β * ssV β sbar)
    have hC : HasDerivAt (fun ε : ℝ => ssV β sbar + ε * y) y 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const y).const_add (ssV β sbar)
    have hbV : β * ssV β sbar ≠ 0 := (mul_pos hβ0 hV).ne'
    have hL := HasDerivAt.sub (HasDerivAt.add (hD t) (hA.log (by simpa using hbV)))
      (hC.log (by simpa using hV.ne'))
    refine (hL.congr_of_eventuallyEq hev).congr_deriv ?_
    change ihat' t ω + x / (β * ssV β sbar + 0 * x) - y / (ssV β sbar + 0 * y) =
      ihat' t ω - (ssV β sbar)⁻¹ * (y - β⁻¹ * x)
    rw [zero_mul, add_zero, zero_mul, add_zero]
    have := hV.ne'
    have := hβ0.ne'
    field_simp
    ring

/-- Cochrane (2023), eq. (2.22), p. 40: the rule family's rate exceeds `−1` (`β > 0`).
Generalises `TidyR5MeasFamilyRule.mRuleRate_gt`. -/
theorem vRuleRate_gt (hβ0 : 0 < β) (ε : ℝ) (t : ℕ) (ω : Ω) :
    -1 < vRuleRate β sbar Y X θ u ε t ω := by
  simp only [vRuleRate]
  have := mul_pos (inv_pos.mpr hβ0)
    (Real.exp_pos (θ * vRuleInfl β sbar Y X θ u ε t ω + ε * u t ω))
  linarith

/-- Cochrane (2023), eq. (2.22), p. 40: `log(1 + i_t(ε)) = −log β + θπ_t(ε) + εu_t` exactly
(`β > 0`).
Generalises `TidyR5MeasFamilyRule.log_one_add_mRuleRate`. -/
theorem log_one_add_vRuleRate (hβ0 : 0 < β) (ε : ℝ) (t : ℕ) (ω : Ω) :
    Real.log (1 + vRuleRate β sbar Y X θ u ε t ω) =
      -Real.log β + θ * vRuleInfl β sbar Y X θ u ε t ω + ε * u t ω := by
  simp only [vRuleRate, add_sub_cancel]
  rw [Real.log_mul (inv_pos.mpr hβ0).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_inv]
  ring

/-- Cochrane (2023), p. 40, **in every state** where the bounds hold: inflation and the rate of
the rule family are `C^n` in `ε` on `famDom` (every `n`).
Generalises `TidyR5MeasFamilyRule.mRule_contDiffOn`. -/
theorem vRule_contDiffOn (hβ0 : 0 < β) (hβ1 : β < 1) {n : WithTop ℕ∞} {ω : Ω}
    (hω : Bounds β M Y X ω) (t : ℕ) :
    ContDiffOn ℝ n (fun ε => vRuleInfl β sbar Y X θ u ε t ω) (famDom sbar M) ∧
      ContDiffOn ℝ n (fun ε => vRuleRate β sbar Y X θ u ε t ω) (famDom sbar M) := by
  have hpv : ∀ t, ContDiff ℝ n (fun ε => ssV β sbar + ε * Y t ω) := fun t =>
    contDiff_const.add (contDiff_id.mul contDiff_const)
  have hpvE : ∀ t, ContDiff ℝ n (fun ε => β * ssV β sbar + ε * X t ω) := fun t =>
    contDiff_const.add (contDiff_id.mul contDiff_const)
  have hI : ∀ t, ContDiffOn ℝ n (fun ε => vRuleInfl β sbar Y X θ u ε t ω)
      (famDom sbar M) := by
    intro t
    induction t with
    | zero =>
      exact contDiffOn_const.sub ((hpv 0).contDiffOn.log
        fun ε hε => (aff_pos hβ1 (hω 0).1 hε).ne')
    | succ t ih =>
      exact ((((contDiffOn_const.add (contDiffOn_const.mul ih)).add
        (contDiffOn_id.mul contDiffOn_const)).add
        ((hpvE t).contDiffOn.log fun ε hε => (affEx_pos hβ0 hβ1 (hω t).2 hε).ne')).sub
        ((hpv (t + 1)).contDiffOn.log fun ε hε => (aff_pos hβ1 (hω (t + 1)).1 hε).ne'))
  exact ⟨hI t, (contDiffOn_const.mul ((contDiffOn_const.mul (hI t)).add
    (contDiffOn_id.mul contDiffOn_const)).exp).sub contDiffOn_const⟩

/-- Cochrane (2023), eq. (2.25), p. 40, **in every state**: the derivative at `ε = 0` of the
rule family's inflation is the linear solution `LinearFTMP.ruleSol θ u (vShock) (vInfl0)`, for
every `θ` (`0 < β < 1`, `s̄ > 0`).
Generalises `TidyR5MeasFamilyRule.mRuleInfl_hasDerivAt`. -/
theorem vRuleInfl_hasDerivAt (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => vRuleInfl β sbar Y X θ u ε t ω)
      (LinearFTMP.ruleSol θ u (vShock β sbar Y X) (vInfl0 β sbar Y) t ω) 0 := by
  have hV : 0 < ssV β sbar := mul_pos (inv_pos.mpr (by linarith)) hsbar
  have hlogpv : ∀ t, HasDerivAt (fun ε => Real.log (ssV β sbar + ε * Y t ω))
      (Y t ω / ssV β sbar) 0 := by
    intro t
    have hA : HasDerivAt (fun ε => ssV β sbar + ε * Y t ω) (Y t ω) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (Y t ω)).const_add (ssV β sbar)
    have := hA.log (by simpa using hV.ne')
    simpa using this
  have hlogpvE : ∀ t, HasDerivAt (fun ε => Real.log (β * ssV β sbar + ε * X t ω))
      (X t ω / (β * ssV β sbar)) 0 := by
    intro t
    have hA : HasDerivAt (fun ε => β * ssV β sbar + ε * X t ω) (X t ω) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (X t ω)).const_add (β * ssV β sbar)
    have := hA.log (by simpa using (mul_pos hβ0 hV).ne')
    simpa using this
  induction t with
  | zero =>
    refine ((hlogpv 0).const_sub (Real.log (ssV β sbar))).congr_deriv ?_
    change -(Y 0 ω / ssV β sbar) = -((ssV β sbar)⁻¹ * Y 0 ω)
    rw [div_eq_inv_mul]
  | succ t ih =>
    have hL := HasDerivAt.sub (HasDerivAt.add (HasDerivAt.add (HasDerivAt.const_add
      (-Real.log β) (ih.const_mul θ)) ((hasDerivAt_id (0 : ℝ)).mul_const (u t ω)))
      (hlogpvE t)) (hlogpv (t + 1))
    refine hL.congr_deriv ?_
    change θ * LinearFTMP.ruleSol θ u (vShock β sbar Y X) (vInfl0 β sbar Y) t ω +
        id 1 * u t ω + X t ω / (β * ssV β sbar) - Y (t + 1) ω / ssV β sbar =
      θ * LinearFTMP.ruleSol θ u (vShock β sbar Y X) (vInfl0 β sbar Y) t ω +
        u t ω - (ssV β sbar)⁻¹ * (Y (t + 1) ω - β⁻¹ * X t ω)
    rw [id]
    have := hV.ne'
    have := hβ0.ne'
    field_simp
    ring

/-- Cochrane (2023), p. 40, in every state where the bounds hold and `B_{−1} ≠ 0`: on `famDom`
the family's inflation under the rule is the closed form `vRuleInfl`.
Generalises `TidyR5MeasFamilyRule.mFamInfl_eq`. -/
theorem vFamInfl_eq_vRuleInfl (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar) {ω : Ω}
    (hω : Bounds β M Y X ω) (hB0 : Bm1 ω ≠ 0) {ε : ℝ} (hε : ε ∈ famDom sbar M) (t : ℕ) :
    vFamInfl β sbar Y X Bm1 (vRuleRate β sbar Y X θ u) ε t ω =
      vRuleInfl β sbar Y X θ u ε t ω := by
  have hV : 0 < ssV β sbar := mul_pos (inv_pos.mpr (by linarith)) hsbar
  have hiG : ∀ ε ∈ famDom sbar M, ∀ t, -1 < vRuleRate β sbar Y X θ u ε t ω :=
    fun ε _ t => vRuleRate_gt hβ0 ε t ω
  cases t with
  | zero =>
    change Real.log (Bm1 ω / (ssV β sbar + ε * Y 0 ω) / (Bm1 ω / ssV β sbar)) =
      Real.log (ssV β sbar) - Real.log (ssV β sbar + ε * Y 0 ω)
    have h3 : 0 < ssV β sbar + ε * Y 0 ω := aff_pos (sbar := sbar) hβ1 (hω 0).1 hε
    rw [show Bm1 ω / (ssV β sbar + ε * Y 0 ω) / (Bm1 ω / ssV β sbar) =
        ssV β sbar / (ssV β sbar + ε * Y 0 ω) by field_simp,
      Real.log_div hV.ne' h3.ne']
  | succ t =>
    have hP := vFamP_ne hβ0 hβ1 hω hB0 hiG hε t
    have h1 : 0 < 1 + vRuleRate β sbar Y X θ u ε t ω := by linarith [hiG ε hε t]
    have h2 : 0 < β * ssV β sbar + ε * X t ω := affEx_pos hβ0 hβ1 (hω t).2 hε
    have h3 : 0 < ssV β sbar + ε * Y (t + 1) ω := aff_pos hβ1 (hω (t + 1)).1 hε
    change Real.log ((1 + vRuleRate β sbar Y X θ u ε t ω) *
      vFamP β sbar Y X Bm1 (vRuleRate β sbar Y X θ u) ε t ω *
      (β * ssV β sbar + ε * X t ω) / (ssV β sbar + ε * Y (t + 1) ω) /
      vFamP β sbar Y X Bm1 (vRuleRate β sbar Y X θ u) ε t ω) = _
    rw [show (1 + vRuleRate β sbar Y X θ u ε t ω) *
        vFamP β sbar Y X Bm1 (vRuleRate β sbar Y X θ u) ε t ω *
        (β * ssV β sbar + ε * X t ω) / (ssV β sbar + ε * Y (t + 1) ω) /
        vFamP β sbar Y X Bm1 (vRuleRate β sbar Y X θ u) ε t ω =
        (1 + vRuleRate β sbar Y X θ u ε t ω) * (β * ssV β sbar + ε * X t ω) /
          (ssV β sbar + ε * Y (t + 1) ω) by field_simp,
      Real.log_div (mul_pos h1 h2).ne' h3.ne', Real.log_mul h1.ne' h2.ne',
      log_one_add_vRuleRate hβ0]
    rfl

/-! ### Congruence in the versions -/

/-- Cochrane (2023), §2.4.3, p. 31: the family depends on the state only through the values of
the versions and of the rate there. -/
theorem vFamP_congr {Y' X' : ℕ → Ω → ℝ} {iF' : ℝ → ℕ → Ω → ℝ} {ω : Ω}
    (hY : ∀ t, Y t ω = Y' t ω) (hX : ∀ t, X t ω = X' t ω) (hi : ∀ ε t, iF ε t ω = iF' ε t ω)
    (ε : ℝ) (t : ℕ) : vFamP β sbar Y X Bm1 iF ε t ω = vFamP β sbar Y' X' Bm1 iF' ε t ω := by
  induction t with
  | zero => simp only [vFamP, hY]
  | succ t ih =>
    change (1 + iF ε t ω) * vFamP β sbar Y X Bm1 iF ε t ω * (β * ssV β sbar + ε * X t ω) /
      (ssV β sbar + ε * Y (t + 1) ω) = (1 + iF' ε t ω) * vFamP β sbar Y' X' Bm1 iF' ε t ω *
        (β * ssV β sbar + ε * X' t ω) / (ssV β sbar + ε * Y' (t + 1) ω)
    rw [ih, hY, hX, hi]

/-- Cochrane (2023), eq. (2.15), p. 31: the same congruence for the debt. -/
theorem vFamB_congr {Y' X' : ℕ → Ω → ℝ} {iF' : ℝ → ℕ → Ω → ℝ} {ω : Ω}
    (hY : ∀ t, Y t ω = Y' t ω) (hX : ∀ t, X t ω = X' t ω) (hi : ∀ ε t, iF ε t ω = iF' ε t ω)
    (ε : ℝ) (t : ℕ) : vFamB β sbar Y X Bm1 iF ε t ω = vFamB β sbar Y' X' Bm1 iF' ε t ω := by
  change (1 + iF ε t ω) * vFamP β sbar Y X Bm1 iF ε t ω * (β * ssV β sbar + ε * X t ω) =
    (1 + iF' ε t ω) * vFamP β sbar Y' X' Bm1 iF' ε t ω * (β * ssV β sbar + ε * X' t ω)
  rw [vFamP_congr hY hX hi, hX, hi]

/-- Cochrane (2023), §2.5, p. 35: the same congruence for inflation. -/
theorem vFamInfl_congr {Y' X' : ℕ → Ω → ℝ} {iF' : ℝ → ℕ → Ω → ℝ} {ω : Ω}
    (hY : ∀ t, Y t ω = Y' t ω) (hX : ∀ t, X t ω = X' t ω) (hi : ∀ ε t, iF ε t ω = iF' ε t ω)
    (ε : ℝ) (t : ℕ) :
    vFamInfl β sbar Y X Bm1 iF ε t ω = vFamInfl β sbar Y' X' Bm1 iF' ε t ω := by
  cases t with
  | zero =>
    change Real.log (vFamP β sbar Y X Bm1 iF ε 0 ω / (Bm1 ω / ssV β sbar)) =
      Real.log (vFamP β sbar Y' X' Bm1 iF' ε 0 ω / (Bm1 ω / ssV β sbar))
    rw [vFamP_congr hY hX hi]
  | succ t =>
    change Real.log (vFamP β sbar Y X Bm1 iF ε (t + 1) ω / vFamP β sbar Y X Bm1 iF ε t ω) =
      Real.log (vFamP β sbar Y' X' Bm1 iF' ε (t + 1) ω / vFamP β sbar Y' X' Bm1 iF' ε t ω)
    rw [vFamP_congr hY hX hi, vFamP_congr hY hX hi]

/-- Cochrane (2023), p. 40: the rule family depends on the state only through the values of the
versions and of `u` there. -/
theorem vRuleInfl_congr {Y' X' u' : ℕ → Ω → ℝ} {ω : Ω} (hY : ∀ t, Y t ω = Y' t ω)
    (hX : ∀ t, X t ω = X' t ω) (hu : ∀ t, u t ω = u' t ω) (ε : ℝ) (t : ℕ) :
    vRuleInfl β sbar Y X θ u ε t ω = vRuleInfl β sbar Y' X' θ u' ε t ω := by
  induction t with
  | zero => simp only [vRuleInfl, hY]
  | succ t ih =>
    change -Real.log β + θ * vRuleInfl β sbar Y X θ u ε t ω + ε * u t ω +
      Real.log (β * ssV β sbar + ε * X t ω) - Real.log (ssV β sbar + ε * Y (t + 1) ω) =
      -Real.log β + θ * vRuleInfl β sbar Y' X' θ u' ε t ω + ε * u' t ω +
      Real.log (β * ssV β sbar + ε * X' t ω) - Real.log (ssV β sbar + ε * Y' (t + 1) ω)
    rw [ih, hu, hX, hY]

/-- Cochrane (2023), eq. (2.22), p. 40: the same congruence for the rule's rate. -/
theorem vRuleRate_congr {Y' X' u' : ℕ → Ω → ℝ} {ω : Ω} (hY : ∀ t, Y t ω = Y' t ω)
    (hX : ∀ t, X t ω = X' t ω) (hu : ∀ t, u t ω = u' t ω) (ε : ℝ) (t : ℕ) :
    vRuleRate β sbar Y X θ u ε t ω = vRuleRate β sbar Y' X' θ u' ε t ω := by
  simp only [vRuleRate, vRuleInfl_congr hY hX hu, hu]

/-! ### What is necessary -/

/-- Cochrane (2023), eq. (2.7), p. 22: if `V + εY > 0` almost surely for every `|ε| < δ`, then
`|Y| ≤ V/δ` almost surely. Positive present values `V + ε PV_t(ŝ)` on a neighbourhood of
`ε = 0` (necessary for equilibria with positive debt, `TidyR6MeasHyp.mEqm_pv_zero_pos`) force
essentially bounded `PV_t(ŝ)`. -/
theorem pv_bound_necessary [MeasurableSpace Ω] {μ : Measure Ω} {V δ : ℝ} (hδ : 0 < δ)
    {Yt : Ω → ℝ} (h : ∀ ε ∈ Set.Ioo (-δ) δ, ∀ᵐ ω ∂μ, 0 < V + ε * Yt ω) :
    ∀ᵐ ω ∂μ, |Yt ω| ≤ V / δ := by
  have hn : ∀ n : ℕ, (n : ℝ) / (n + 1) * δ ∈ Set.Ioo (-δ) δ ∧
      -((n : ℝ) / (n + 1) * δ) ∈ Set.Ioo (-δ) δ := fun n => by
    have h1 : (0 : ℝ) ≤ (n : ℝ) / (n + 1) := by positivity
    have h2 : (n : ℝ) / (n + 1) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    constructor <;> constructor <;> nlinarith
  filter_upwards [ae_all_iff.2 fun n => h _ (hn n).1, ae_all_iff.2 fun n => h _ (hn n).2]
    with ω h1 h2
  have hb : ∀ n : ℕ, (n : ℝ) / (n + 1) * (δ * |Yt ω|) ≤ V := fun n => by
    have a1 := h1 n
    have a2 := h2 n
    rcases abs_cases (Yt ω) with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] <;> nlinarith
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1) * (δ * |Yt ω|)) atTop
      (𝓝 (1 * (δ * |Yt ω|))) :=
    (tendsto_natCast_div_add_atTop (1 : ℝ)).mul_const _
  have hle : 1 * (δ * |Yt ω|) ≤ V := le_of_tendsto' hlim hb
  rw [le_div_iff₀ hδ]
  linarith

variable [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), eq. (2.26), p. 42, on a probability space: if the present value of `ŝ`
satisfies its recursion `PV_t = ŝ_t + β E_t PV_{t+1}` almost surely and `|PV_t| ≤ K` almost
surely at every date, then `|ŝ_t| ≤ (1 + |β|) K` almost surely: bounded present values need
bounded surpluses. -/
theorem shat_bound_of_pv_bound {shat : ℕ → Ω → ℝ} {K : ℝ}
    (hrec : ∀ t, S.forwardSol β shat t =ᵐ[S.μ] shat t + β • S.E t (S.forwardSol β shat (t + 1)))
    (hK : ∀ t, ∀ᵐ ω ∂S.μ, |S.forwardSol β shat t ω| ≤ K) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, |shat t ω| ≤ (1 + |β|) * K := by
  filter_upwards [hrec t, hK t, S.abs_E_le (hK (t + 1)) t] with ω h1 h2 h3
  have e : shat t ω = S.forwardSol β shat t ω - β * S.E t (S.forwardSol β shat (t + 1)) ω := by
    rw [h1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e]
  calc |S.forwardSol β shat t ω - β * S.E t (S.forwardSol β shat (t + 1)) ω|
      ≤ |S.forwardSol β shat t ω| + |β * S.E t (S.forwardSol β shat (t + 1)) ω| :=
        abs_sub _ _
    _ ≤ K + |β| * K := by
        rw [abs_mul]
        exact add_le_add h2 (mul_le_mul_of_nonneg_left h3 (abs_nonneg β))
    _ = (1 + |β|) * K := by ring

/-- Cochrane (2023), eq. (2.3), p. 22: the bond price of the canonical target
`1 + i_t = β⁻¹ exp(ε î_t)` is integrable iff `exp(−ε î_t)` is (`β > 0`).
Generalises `TidyR5MeasFamily.rateExp_bondPrice_integrable`. -/
theorem rateExp_bondPrice_iff (hβ0 : 0 < β) (ihat : ℕ → Ω → ℝ) (ε : ℝ) (t : ℕ) :
    Integrable (fun ω => (1 + rateExp β ihat ε t ω)⁻¹) S.μ ↔
      Integrable (fun ω => Real.exp (-(ε * ihat t ω))) S.μ := by
  have e : ∀ ω, (1 + rateExp β ihat ε t ω)⁻¹ = β * Real.exp (-(ε * ihat t ω)) := fun ω => by
    simp only [rateExp, add_sub_cancel]
    rw [mul_inv, inv_inv, Real.exp_neg]
  constructor
  · intro h
    refine (h.const_mul β⁻¹).congr (Eventually.of_forall fun ω => ?_)
    simp only
    rw [e, ← mul_assoc, inv_mul_cancel₀ hβ0.ne', one_mul]
  · intro h
    exact (h.const_mul β).congr (Eventually.of_forall fun ω => (e ω).symm)

/-! ### Chosen versions -/

/-- Cochrane (2023), eq. (2.7), p. 22: clamping to `[−K, K]`. -/
noncomputable def clamp (K x : ℝ) : ℝ := max (-K) (min K x)

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), eq. (2.7), p. 22: the clamp is bounded by `K ≥ 0`. -/
theorem abs_clamp_le {K : ℝ} (hK : 0 ≤ K) (x : ℝ) : |clamp K x| ≤ K :=
  abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), eq. (2.7), p. 22: the clamp does nothing inside `[−K, K]`. -/
theorem clamp_eq {K x : ℝ} (h : |x| ≤ K) : clamp K x = x := by
  unfold clamp
  rw [min_eq_right (abs_le.mp h).2, max_eq_right (abs_le.mp h).1]

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), eq. (2.7), p. 22: the clamp is measurable. -/
theorem measurable_clamp (K : ℝ) : Measurable (clamp K) :=
  (continuous_const.max (continuous_const.min continuous_id)).measurable

/-- Cochrane (2023), eq. (2.7), p. 22: the chosen version of the present value of `ŝ`, clamped
to `[−M/(1 − β), M/(1 − β)]`. -/
noncomputable def pvVer (β M : ℝ) (shat : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => clamp ((1 - β)⁻¹ * M) (S.forwardSol β shat t ω)

/-- Cochrane (2023), eq. (2.15), p. 31: the chosen version of the ex-dividend present value of
`ŝ`, clamped to `[−βM/(1 − β), βM/(1 − β)]`. -/
noncomputable def pvExVer (β M : ℝ) (shat : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => clamp (β * ((1 - β)⁻¹ * M)) (pvExM S β shat t ω)

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), §2.5, p. 35: the chosen version of a process bounded by `M` almost surely,
clamped to `[−M, M]`. -/
noncomputable def procVer (M : ℝ) (x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t ω => clamp M (x t ω)

/-- Cochrane (2023), eq. (2.7), p. 22: the chosen versions are adapted. -/
theorem ver_adapted (β M : ℝ) (shat : ℕ → Ω → ℝ) :
    StronglyAdapted S.𝓕 (pvVer S β M shat) ∧ StronglyAdapted S.𝓕 (pvExVer S β M shat) :=
  ⟨fun t => ((measurable_clamp _).comp (S.forwardSol_adapted β shat t).measurable
    ).stronglyMeasurable,
   fun t => ((measurable_clamp _).comp (pvExM_sm S β shat t).measurable).stronglyMeasurable⟩

/-- Cochrane (2023), §2.5, p. 35: the clamped version of an adapted process is adapted. -/
theorem procVer_adapted (M : ℝ) {x : ℕ → Ω → ℝ} (hx : StronglyAdapted S.𝓕 x) :
    StronglyAdapted S.𝓕 (procVer M x) := fun t =>
  ((measurable_clamp M).comp (hx t).measurable).stronglyMeasurable

/-- Cochrane (2023), eq. (2.7), p. 22: the chosen versions obey the bounds in **every** state
(`0 < β < 1`, `M ≥ 0`). -/
theorem ver_bounds (hβ0 : 0 < β)
    (hβ1 : β < 1) (hM : 0 ≤ M) (shat : ℕ → Ω → ℝ) (ω : Ω) :
    Bounds β M (pvVer S β M shat) (pvExVer S β M shat) ω := fun t => by
  have hK : 0 ≤ (1 - β)⁻¹ * M := mul_nonneg (inv_nonneg.mpr (by linarith)) hM
  exact ⟨abs_clamp_le hK _, abs_clamp_le (mul_nonneg hβ0.le hK) _⟩

/-- Cochrane (2023), eq. (2.7), p. 22: with `|ŝ| ≤ M` almost surely, the chosen versions equal
the present values almost surely at every date (all dates at once). -/
theorem ver_ae (hβ0 : 0 < β) (hβ1 : β < 1) {shat : ℕ → Ω → ℝ}
    (hs : ∀ t, ∀ᵐ ω ∂S.μ, |shat t ω| ≤ M) :
    ∀ᵐ ω ∂S.μ, ∀ t, pvVer S β M shat t ω = S.forwardSol β shat t ω ∧
      pvExVer S β M shat t ω = pvExM S β shat t ω := by
  have ha : |β| < 1 := by rwa [abs_of_pos hβ0]
  have hK : M / (1 - |β|) = (1 - β)⁻¹ * M := by rw [abs_of_pos hβ0, div_eq_inv_mul]
  have hb : ∀ t, ∀ᵐ ω ∂S.μ, |S.forwardSol β shat t ω| ≤ (1 - β)⁻¹ * M := fun t => by
    rw [← hK]
    exact pv_bdd S ha hs t
  have hbE : ∀ t, ∀ᵐ ω ∂S.μ, |pvExM S β shat t ω| ≤ β * ((1 - β)⁻¹ * M) := fun t => by
    filter_upwards [S.abs_E_le (hb (t + 1)) t] with ω h
    simp only [pvExM, Pi.smul_apply, smul_eq_mul]
    rw [abs_mul, abs_of_pos hβ0]
    exact mul_le_mul_of_nonneg_left h hβ0.le
  filter_upwards [ae_all_iff.2 hb, ae_all_iff.2 hbE] with ω h1 h2 t
  exact ⟨clamp_eq (h1 t), clamp_eq (h2 t)⟩

/-- Cochrane (2023), §2.5, p. 35: the clamped version of a process bounded by `M` almost surely
equals it almost surely at every date. -/
theorem procVer_ae {x : ℕ → Ω → ℝ} (hx : ∀ t, ∀ᵐ ω ∂S.μ, |x t ω| ≤ M) (t : ℕ) :
    procVer M x t =ᵐ[S.μ] x t := by
  filter_upwards [hx t] with ω h
  exact clamp_eq h

/-- Cochrane (2023), eq. (2.7), p. 22: a process bounded by `M` almost surely has `M ≥ 0`. -/
theorem nonneg_of_bound {x : ℕ → Ω → ℝ} (hx : ∀ t, ∀ᵐ ω ∂S.μ, |x t ω| ≤ M) : 0 ≤ M := by
  obtain ⟨ω, hω⟩ := (hx 0).exists
  exact (abs_nonneg _).trans hω

/-! ### Present values of processes equal almost surely -/

/-- Cochrane (2023), eq. (2.7), p. 22, on a probability space: surpluses equal almost surely at
every date have present values equal almost surely at every date. -/
theorem forwardSol_congr {s s' : ℕ → Ω → ℝ} (h : ∀ k, s k =ᵐ[S.μ] s' k) (t : ℕ) :
    S.forwardSol β s t =ᵐ[S.μ] S.forwardSol β s' t := by
  have hd : MeasExpectationSystem.discSum β s t =ᵐ[S.μ] MeasExpectationSystem.discSum β s' t := by
    filter_upwards [ae_all_iff.2 h] with ω hω
    simp only [MeasExpectationSystem.discSum, hω]
  exact S.E_congr hd t

/-- Cochrane (2023), eq. (2.15), p. 31, on a probability space: the same for the ex-dividend
present values. -/
theorem pvExM_congr {s s' : ℕ → Ω → ℝ} (h : ∀ k, s k =ᵐ[S.μ] s' k) (t : ℕ) :
    pvExM S β s t =ᵐ[S.μ] pvExM S β s' t := by
  filter_upwards [S.E_congr (forwardSol_congr S (β := β) h (t + 1)) t] with ω h1
  simp only [pvExM, Pi.smul_apply, smul_eq_mul, h1]

/-- Cochrane (2023), §§2.1–2.4, pp. 21–33, on a probability space: an equilibrium for `s` is an
equilibrium for any `s'` with the same present values almost surely. -/
theorem mEquilibrium_congr_surplus {s s' B P i : ℕ → Ω → ℝ}
    (h : MEquilibrium S β Bm1 s B P i) (hs : ∀ t, S.forwardSol β s t =ᵐ[S.μ] S.forwardSol β s' t) :
    MEquilibrium S β Bm1 s' B P i := by
  obtain ⟨hPa, hP, hBa, hia, hint, ⟨hv0, hv⟩, hbp⟩ := h
  exact ⟨hPa, hP, hBa, hia, hint, ⟨hv0.trans (hs 0), fun t => (hv t).trans (hs (t + 1))⟩, hbp⟩

/-- Cochrane (2023), §2.5, p. 35: the surplus families of processes equal almost surely are
equal almost surely. -/
theorem surpFam_ae {μ : Measure Ω} {shat shat' : ℕ → Ω → ℝ}
    (h : ∀ k, shat k =ᵐ[μ] shat' k) (ε : ℝ) (k : ℕ) :
    surpFam sbar shat ε k =ᵐ[μ] surpFam sbar shat' ε k := by
  filter_upwards [h k] with ω hω
  simp only [surpFam, hω]

/-- Cochrane (2023), §2.4.3, p. 31: the family of `TidyR5MeasFamily` is the version family with
the fixed versions `MeasExpectationSystem.forwardSol` and `TidyR5Meas.pvExM`. -/
theorem mFamP_eq_vFamP (shat : ℕ → Ω → ℝ) (ε : ℝ) (t : ℕ) :
    mFamP S β sbar shat Bm1 iF ε t =
      vFamP β sbar (S.forwardSol β shat) (pvExM S β shat) Bm1 iF ε t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext ω
    change (1 + iF ε t ω) * mFamP S β sbar shat Bm1 iF ε t ω * pvExAff S β sbar shat ε t ω /
      pvAff S β sbar shat ε (t + 1) ω = _
    rw [ih]
    rfl

/-- Cochrane (2023), eq. (2.15), p. 31: the same for the debt. -/
theorem mFamB_eq_vFamB (shat : ℕ → Ω → ℝ) (ε : ℝ) (t : ℕ) :
    mFamB S β sbar shat Bm1 iF ε t =
      vFamB β sbar (S.forwardSol β shat) (pvExM S β shat) Bm1 iF ε t := by
  funext ω
  change (1 + iF ε t ω) * mFamP S β sbar shat Bm1 iF ε t ω * pvExAff S β sbar shat ε t ω = _
  rw [mFamP_eq_vFamP]
  rfl

/-- Cochrane (2023), p. 40: the closed-form rule inflation of `TidyR5MeasFamilyRule` is the
version one with the fixed versions. -/
theorem mRuleInfl_eq_vRuleInfl (shat : ℕ → Ω → ℝ) (ε : ℝ) (t : ℕ) :
    mRuleInfl S β sbar shat θ u ε t =
      vRuleInfl β sbar (S.forwardSol β shat) (pvExM S β shat) θ u ε t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext ω
    change -Real.log β + θ * mRuleInfl S β sbar shat θ u ε t ω + ε * u t ω +
      Real.log (pvExAff S β sbar shat ε t ω) - Real.log (pvAff S β sbar shat ε (t + 1) ω) = _
    rw [ih]
    rfl

/-- Cochrane (2023), eq. (2.22), p. 40: the same for the rule's rate. -/
theorem mRuleRate_eq_vRuleRate (shat : ℕ → Ω → ℝ) (ε : ℝ) :
    mRuleRate S β sbar shat θ u ε =
      vRuleRate β sbar (S.forwardSol β shat) (pvExM S β shat) θ u ε := by
  funext t ω
  change β⁻¹ * Real.exp (θ * mRuleInfl S β sbar shat θ u ε t ω + ε * u t ω) - 1 = _
  rw [mRuleInfl_eq_vRuleInfl]
  rfl

/-- Cochrane (2023), §2.4.3, p. 31: the version family is adapted when the versions, the rate
and the initial debt are.
Generalises `TidyR5MeasFamily.mFamP_sm`. -/
theorem vFamP_sm (hY : StronglyAdapted S.𝓕 Y) (hX : StronglyAdapted S.𝓕 X)
    (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1) {ε : ℝ} (hiA : StronglyAdapted S.𝓕 (iF ε))
    (t : ℕ) : StronglyMeasurable[S.𝓕 t] (vFamP β sbar Y X Bm1 iF ε t) := by
  induction t with
  | zero =>
    exact (hBm1.measurable.div (((hY 0).measurable.const_mul ε).const_add _)).stronglyMeasurable
  | succ t ih =>
    have hmono : S.𝓕 t ≤ S.𝓕 (t + 1) := S.𝓕.mono (Nat.le_succ t)
    exact ((((((hiA t).mono hmono).measurable.const_add 1).mul (ih.mono hmono).measurable).mul
      ((((hX t).mono hmono).measurable.const_mul ε).const_add _)).div
      (((hY (t + 1)).measurable.const_mul ε).const_add _)).stronglyMeasurable

/-- Cochrane (2023), eq. (2.15), p. 31: the version family's debt is adapted.
Generalises `TidyR5MeasFamily.mFamB_sm`. -/
theorem vFamB_sm (hY : StronglyAdapted S.𝓕 Y) (hX : StronglyAdapted S.𝓕 X)
    (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1) {ε : ℝ} (hiA : StronglyAdapted S.𝓕 (iF ε))
    (t : ℕ) : StronglyMeasurable[S.𝓕 t] (vFamB β sbar Y X Bm1 iF ε t) :=
  ((((hiA t).measurable.const_add 1).mul (vFamP_sm S hY hX hBm1 hiA t).measurable).mul
    (((hX t).measurable.const_mul ε).const_add _)).stronglyMeasurable

/-- Cochrane (2023), p. 40: the version rule inflation is adapted (adapted versions and `u`).
Generalises `TidyR5MeasFamilyRule.mRuleInfl_sm`. -/
theorem vRuleInfl_sm (hY : StronglyAdapted S.𝓕 Y) (hX : StronglyAdapted S.𝓕 X)
    (hu : StronglyAdapted S.𝓕 u) (ε : ℝ) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (vRuleInfl β sbar Y X θ u ε t) := by
  have hpv : ∀ t, Measurable[S.𝓕 t] (fun ω => ssV β sbar + ε * Y t ω) := fun t =>
    ((hY t).measurable.const_mul ε).const_add _
  have hpvE : ∀ t, Measurable[S.𝓕 t] (fun ω => β * ssV β sbar + ε * X t ω) := fun t =>
    ((hX t).measurable.const_mul ε).const_add _
  induction t with
  | zero => exact (measurable_const.sub (hpv 0).log).stronglyMeasurable
  | succ t ih =>
    have hmono : S.𝓕 t ≤ S.𝓕 (t + 1) := S.𝓕.mono (Nat.le_succ t)
    exact ((((measurable_const.add ((ih.mono hmono).measurable.const_mul θ)).add
      (((hu t).mono hmono).measurable.const_mul ε)).add ((hpvE t).log.mono hmono le_rfl)).sub
      (hpv (t + 1)).log).stronglyMeasurable

/-- Cochrane (2023), eq. (2.22), p. 40: the version rule rate is adapted.
Generalises `TidyR5MeasFamilyRule.mRuleRate_sm`. -/
theorem vRuleRate_sm (hY : StronglyAdapted S.𝓕 Y) (hX : StronglyAdapted S.𝓕 X)
    (hu : StronglyAdapted S.𝓕 u) (ε : ℝ) : StronglyAdapted S.𝓕 (vRuleRate β sbar Y X θ u ε) :=
  fun t => (((((vRuleInfl_sm S hY hX hu ε t).measurable.const_mul θ).add
    ((hu t).measurable.const_mul ε)).exp.const_mul β⁻¹).sub_const 1).stronglyMeasurable

/-! ### The version family: equilibrium and uniqueness -/

variable {shat ihat : ℕ → Ω → ℝ}

/-- Cochrane (2023), §2.4.3, p. 31, on a probability space: almost surely, in every such state,
for all `ε` and `t`, the version family with `pvVer`, `pvExVer` equals the family of
`TidyR5MeasFamily` built from any `ŝ'` equal to `ŝ` almost surely, for rates `iF`, `iF'` that
agree in that state. -/
theorem vFam_ae_mFam (hβ0 : 0 < β) (hβ1 : β < 1) (hs : ∀ t, ∀ᵐ ω ∂S.μ, |shat t ω| ≤ M)
    {shat' : ℕ → Ω → ℝ} (hss : ∀ k, shat' k =ᵐ[S.μ] shat k) :
    ∀ᵐ ω ∂S.μ, ∀ t, pvVer S β M shat t ω = S.forwardSol β shat' t ω ∧
      pvExVer S β M shat t ω = pvExM S β shat' t ω := by
  filter_upwards [ver_ae S hβ0 hβ1 hs, ae_all_iff.2 fun t => forwardSol_congr S (β := β) hss t,
    ae_all_iff.2 fun t => pvExM_congr S (β := β) hss t] with ω h1 h2 h3 t
  exact ⟨(h1 t).1.trans (h2 t).symm, (h1 t).2.trans (h3 t).symm⟩

/-- Cochrane (2023), §2.4.3, p. 31, on a probability space, **with `ŝ` bounded only almost
surely**: for every `ε ∈ famDom`, the version family is an equilibrium (`0 < β < 1`, adapted
`ŝ` with `|ŝ| ≤ M` almost surely, positive initial debt known at `0`, a rate family that is
adapted, exceeds `−1` and has integrable bond price on the domain).
Generalises `TidyR5MeasFamily.mFam_equilibrium`. -/
theorem vFam_equilibrium (hβ0 : 0 < β) (hβ1 : β < 1) (hsad : StronglyAdapted S.𝓕 shat)
    (hs : ∀ t, ∀ᵐ ω ∂S.μ, |shat t ω| ≤ M) (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1)
    (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω) (hiA : ∀ ε ∈ famDom sbar M, StronglyAdapted S.𝓕 (iF ε))
    (hiG : ∀ ε ∈ famDom sbar M, ∀ t ω, -1 < iF ε t ω)
    (hiQ : ∀ ε ∈ famDom sbar M, ∀ t, Integrable (fun ω => (1 + iF ε t ω)⁻¹) S.μ)
    {ε : ℝ} (hε : ε ∈ famDom sbar M) :
    MEquilibrium S β Bm1 (surpFam sbar shat ε)
      (vFamB β sbar (pvVer S β M shat) (pvExVer S β M shat) Bm1 iF ε)
      (vFamP β sbar (pvVer S β M shat) (pvExVer S β M shat) Bm1 iF ε) (iF ε) := by
  have hM := nonneg_of_bound S hs
  have hs'ad := procVer_adapted S M hsad
  have hs'b : ∀ t ω, |procVer M shat t ω| ≤ M := fun t ω => abs_clamp_le hM _
  have hss := procVer_ae S hs
  have hE := mFam_equilibrium S hβ0 hβ1 hs'ad hs'b hBm1 hB hiA hiG hiQ hε
  have hE' := mEquilibrium_congr_surplus S hE
    (fun t => forwardSol_congr S (surpFam_ae hss ε) t)
  have hgood := vFam_ae_mFam S hβ0 hβ1 hs hss
  obtain ⟨hYa, hXa⟩ := ver_adapted S β M shat
  refine mEquilibrium_congr S hE' (fun t => vFamP_sm S hYa hXa hBm1 (hiA ε hε) t)
    (fun t => vFamB_sm S hYa hXa hBm1 (hiA ε hε) t) (fun t => ?_) (fun t => ?_)
  · filter_upwards [hgood] with ω hω
    rw [mFamP_eq_vFamP]
    exact vFamP_congr (fun t => (hω t).1) (fun t => (hω t).2) (fun _ _ => rfl) ε t
  · filter_upwards [hgood] with ω hω
    rw [mFamB_eq_vFamB]
    exact vFamB_congr (fun t => (hω t).1) (fun t => (hω t).2) (fun _ _ => rfl) ε t

/-- Cochrane (2023), p. 33 (determinacy under a target), on a probability space, with `ŝ`
bounded only almost surely: every equilibrium with surpluses `s(ε)` and the target `i(ε)`
equals the version family almost surely at every date.
Generalises `TidyR5MeasFamily.mFam_unique`. -/
theorem vFam_unique (hβ0 : 0 < β) (hβ1 : β < 1) (hsad : StronglyAdapted S.𝓕 shat)
    (hs : ∀ t, ∀ᵐ ω ∂S.μ, |shat t ω| ≤ M) {ε : ℝ} (hε : ε ∈ famDom sbar M) {B P : ℕ → Ω → ℝ}
    (h : MEquilibrium S β Bm1 (surpFam sbar shat ε) B P (iF ε)) (t : ℕ) :
    P t =ᵐ[S.μ] vFamP β sbar (pvVer S β M shat) (pvExVer S β M shat) Bm1 iF ε t ∧
      B t =ᵐ[S.μ] vFamB β sbar (pvVer S β M shat) (pvExVer S β M shat) Bm1 iF ε t := by
  have hM := nonneg_of_bound S hs
  have hs'ad := procVer_adapted S M hsad
  have hs'b : ∀ t ω, |procVer M shat t ω| ≤ M := fun t ω => abs_clamp_le hM _
  have hss := procVer_ae S hs
  have h' := mEquilibrium_congr_surplus S h
    (fun t => (forwardSol_congr S (surpFam_ae hss ε) t).symm)
  obtain ⟨h1, h2⟩ := mFam_unique S hβ0 hβ1 hs'ad hs'b hε h' t
  have hgood := vFam_ae_mFam S hβ0 hβ1 hs hss
  refine ⟨?_, ?_⟩
  · filter_upwards [h1, hgood] with ω e hω
    rw [e, mFamP_eq_vFamP]
    exact (vFamP_congr (fun t => (hω t).1) (fun t => (hω t).2) (fun _ _ => rfl) ε t).symm
  · filter_upwards [h2, hgood] with ω e hω
    rw [e, mFamB_eq_vFamB]
    exact (vFamB_congr (fun t => (hω t).1) (fun t => (hω t).2) (fun _ _ => rfl) ε t).symm

/-! ### The version shock -/

/-- Cochrane (2023), eq. (2.17), p. 35, on a probability space: with `|ŝ| ≤ M` almost surely,
the version shock equals `TidyR5MeasFamily.mShock` and `vInfl0` equals
`TidyR5MeasFamily.mInfl0` almost surely (`0 < β < 1`). -/
theorem vShock_ae (hβ0 : 0 < β) (hβ1 : β < 1) (hs : ∀ t, ∀ᵐ ω ∂S.μ, |shat t ω| ≤ M) :
    (∀ t, vShock β sbar (pvVer S β M shat) (pvExVer S β M shat) t =ᵐ[S.μ]
      mShock S β sbar shat t) ∧
    vInfl0 β sbar (pvVer S β M shat) =ᵐ[S.μ] mInfl0 S β sbar shat := by
  have hv := ver_ae S hβ0 hβ1 hs
  refine ⟨fun t => ?_, ?_⟩
  · cases t with
    | zero =>
      refine Eventually.of_forall fun ω => ?_
      change (0 : ℝ) = ((ssV β sbar)⁻¹ • (0 : Ω → ℝ)) ω
      simp
    | succ t =>
      filter_upwards [hv] with ω h
      change (ssV β sbar)⁻¹ * (pvVer S β M shat (t + 1) ω - β⁻¹ * pvExVer S β M shat t ω) =
        (ssV β sbar)⁻¹ * (S.E (t + 1) (S.forwardSol β shat (t + 1)) ω -
          S.E t (S.forwardSol β shat (t + 1)) ω)
      rw [(h (t + 1)).1, (h t).2, show S.E (t + 1) (S.forwardSol β shat (t + 1)) =
        S.forwardSol β shat (t + 1) from S.E_E_self (t + 1) _]
      simp only [pvExM, Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hβ0.ne', one_mul]
  · filter_upwards [hv] with ω h
    change -((ssV β sbar)⁻¹ * pvVer S β M shat 0 ω) = -((ssV β sbar)⁻¹ * S.forwardSol β shat 0 ω)
    rw [(h 0).1]

/-- Cochrane (2023), eq. (2.17), p. 35, on a probability space: the version shock is a shock
(`TidyR5MeasLinear.MIsShock`), and `vInfl0` is known at `0` and integrable.
Generalises `TidyR5MeasFamily.mShock_isShock`. -/
theorem vShock_isShock (hβ0 : 0 < β) (hβ1 : β < 1) (hs : ∀ t, ∀ᵐ ω ∂S.μ, |shat t ω| ≤ M) :
    MIsShock S (vShock β sbar (pvVer S β M shat) (pvExVer S β M shat)) ∧
      StronglyMeasurable[S.𝓕 0] (vInfl0 β sbar (pvVer S β M shat)) ∧
      Integrable (vInfl0 β sbar (pvVer S β M shat)) S.μ := by
  obtain ⟨hsh, h0⟩ := vShock_ae S (sbar := sbar) hβ0 hβ1 hs
  obtain ⟨m1, m2, m3⟩ := mShock_isShock S (β := β) (sbar := sbar) (shat := shat)
  obtain ⟨hYa, hXa⟩ := ver_adapted S β M shat
  obtain ⟨-, h0i⟩ := mInfl0_sm_integrable S (β := β) (sbar := sbar) (shat := shat)
  refine ⟨⟨fun t => ?_, fun t => (m2 t).congr (hsh (t + 1)).symm, fun t => ?_⟩, ?_,
    h0i.congr h0.symm⟩
  · exact (((hYa (t + 1)).measurable.sub (((hXa t).mono (S.𝓕.mono (Nat.le_succ t))
      ).measurable.const_mul β⁻¹)).const_mul _).stronglyMeasurable
  · filter_upwards [S.E_congr (hsh (t + 1)) t, m3 t] with ω e1 e2
    rw [e1, e2]
  · exact (((hYa 0).measurable.const_mul _).neg).stronglyMeasurable

/-- Cochrane (2023), eq. (2.19), p. 36: solutions of the linear peg model built from shocks and
initial values equal almost surely are equal almost surely. -/
theorem pegSol_congr {μ : Measure Ω} {i ε ε' : ℕ → Ω → ℝ}
    {π0 π0' : Ω → ℝ} (hε : ∀ t, ε t =ᵐ[μ] ε' t) (h0 : π0 =ᵐ[μ] π0') (t : ℕ) :
    LinearFTMP.pegSol i ε π0 t =ᵐ[μ] LinearFTMP.pegSol i ε' π0' t := by
  cases t with
  | zero => exact h0
  | succ t =>
    filter_upwards [hε (t + 1)] with ω h
    change i t ω - ε (t + 1) ω = i t ω - ε' (t + 1) ω
    rw [h]

/-- Cochrane (2023), eq. (2.25), p. 40: solutions of the linear rule model built from
disturbances, shocks and initial values equal almost surely are equal almost surely. -/
theorem ruleSol_congr {μ : Measure Ω} {u' ε ε' : ℕ → Ω → ℝ}
    {π0 π0' : Ω → ℝ} (hu : ∀ t, u t =ᵐ[μ] u' t) (hε : ∀ t, ε t =ᵐ[μ] ε' t)
    (h0 : π0 =ᵐ[μ] π0') (t : ℕ) :
    LinearFTMP.ruleSol θ u ε π0 t =ᵐ[μ] LinearFTMP.ruleSol θ u' ε' π0' t := by
  induction t with
  | zero => exact h0
  | succ t ih =>
    filter_upwards [ih, hu t, hε (t + 1)] with ω h1 h2 h3
    change θ * LinearFTMP.ruleSol θ u ε π0 t ω + u t ω - ε (t + 1) ω =
      θ * LinearFTMP.ruleSol θ u' ε' π0' t ω + u' t ω - ε' (t + 1) ω
    rw [h1, h2, h3]

/-! ### The headline results -/

/-- Cochrane (2023), §§2.4–2.5, pp. 31–36, **the peg family with chosen versions**: for
`0 < β < 1`, `s̄ > 0`, adapted `ŝ` with `|ŝ| ≤ M` almost surely, an adapted integrable `î` with
`exp(−ε î_t)` integrable for `ε ∈ famDom` (necessary: `rateExp_bondPrice_iff`), positive initial
debt known at `0`, and the canonical target `1 + i_t(ε) = β⁻¹ exp(ε î_t)`:
* for each `ε ∈ famDom` the version family is an equilibrium, and every equilibrium equals it
  almost surely at every date;
* **in every state**, its price level, debt and inflation are `C^n` in `ε` on `famDom`, every `n`;
* **in every state with `B_{−1} ≠ 0`**, the derivative at `0` of inflation is the solution (2.19)
  of the linear model with the version shock;
* that solution is adapted, integrable and solves the linear model with a genuine shock;
* the version family equals the family of `TidyR5MeasFamily` almost surely for all `ε` at once,
  and the version shock equals `mShock` almost surely.
Generalises `TidyR5MeasFamily.meas_family_linearization`. -/
theorem version_family_linearization (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar)
    (hsad : StronglyAdapted S.𝓕 shat) (hs : ∀ t, ∀ᵐ ω ∂S.μ, |shat t ω| ≤ M)
    (hihat : StronglyAdapted S.𝓕 ihat) (hii : ∀ t, Integrable (ihat t) S.μ)
    (hexp : ∀ ε ∈ famDom sbar M, ∀ t, Integrable (fun ω => Real.exp (-(ε * ihat t ω))) S.μ)
    (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1) (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω) :
    (∀ ε ∈ famDom sbar M, MEquilibrium S β Bm1 (surpFam sbar shat ε)
      (vFamB β sbar (pvVer S β M shat) (pvExVer S β M shat) Bm1 (rateExp β ihat) ε)
      (vFamP β sbar (pvVer S β M shat) (pvExVer S β M shat) Bm1 (rateExp β ihat) ε)
      (rateExp β ihat ε)) ∧
    (∀ ε ∈ famDom sbar M, ∀ B P : ℕ → Ω → ℝ,
      MEquilibrium S β Bm1 (surpFam sbar shat ε) B P (rateExp β ihat ε) → ∀ t,
        P t =ᵐ[S.μ] vFamP β sbar (pvVer S β M shat) (pvExVer S β M shat) Bm1
          (rateExp β ihat) ε t ∧
        B t =ᵐ[S.μ] vFamB β sbar (pvVer S β M shat) (pvExVer S β M shat) Bm1
          (rateExp β ihat) ε t) ∧
    (∀ (n : WithTop ℕ∞) (ω : Ω) (t : ℕ),
      ContDiffOn ℝ n (fun ε => vFamP β sbar (pvVer S β M shat) (pvExVer S β M shat) Bm1
        (rateExp β ihat) ε t ω) (famDom sbar M) ∧
      ContDiffOn ℝ n (fun ε => vFamB β sbar (pvVer S β M shat) (pvExVer S β M shat) Bm1
        (rateExp β ihat) ε t ω) (famDom sbar M) ∧
      ContDiffOn ℝ n (fun ε => vFamInfl β sbar (pvVer S β M shat) (pvExVer S β M shat) Bm1
        (rateExp β ihat) ε t ω) (famDom sbar M)) ∧
    (∀ ω, Bm1 ω ≠ 0 → ∀ t, HasDerivAt (fun ε => vFamInfl β sbar (pvVer S β M shat)
      (pvExVer S β M shat) Bm1 (rateExp β ihat) ε t ω)
      (LinearFTMP.pegSol ihat (vShock β sbar (pvVer S β M shat) (pvExVer S β M shat))
        (vInfl0 β sbar (pvVer S β M shat)) t ω) 0) ∧
    (StronglyAdapted S.𝓕 (LinearFTMP.pegSol ihat
        (vShock β sbar (pvVer S β M shat) (pvExVer S β M shat))
        (vInfl0 β sbar (pvVer S β M shat))) ∧
      (∀ t, Integrable (LinearFTMP.pegSol ihat
        (vShock β sbar (pvVer S β M shat) (pvExVer S β M shat))
        (vInfl0 β sbar (pvVer S β M shat)) t) S.μ) ∧
      MPegModel S ihat (vShock β sbar (pvVer S β M shat) (pvExVer S β M shat))
        (LinearFTMP.pegSol ihat (vShock β sbar (pvVer S β M shat) (pvExVer S β M shat))
          (vInfl0 β sbar (pvVer S β M shat)))) ∧
    (∀ᵐ ω ∂S.μ, ∀ ε t, vFamP β sbar (pvVer S β M shat) (pvExVer S β M shat) Bm1
      (rateExp β ihat) ε t ω = mFamP S β sbar shat Bm1 (rateExp β ihat) ε t ω) ∧
    (∀ t, vShock β sbar (pvVer S β M shat) (pvExVer S β M shat) t =ᵐ[S.μ]
      mShock S β sbar shat t) := by
  have hM := nonneg_of_bound S hs
  have hiQ : ∀ ε ∈ famDom sbar M, ∀ t, Integrable (fun ω => (1 + rateExp β ihat ε t ω)⁻¹) S.μ :=
    fun ε hε t => (rateExp_bondPrice_iff S hβ0 ihat ε t).mpr (hexp ε hε t)
  have hiG : ∀ ε ∈ famDom sbar M, ∀ t ω, -1 < rateExp β ihat ε t ω :=
    fun ε _ t ω => rateExp_gt hβ0 ihat ε t ω
  obtain ⟨hsh, h0, h0i⟩ := vShock_isShock S (sbar := sbar) hβ0 hβ1 hs
  obtain ⟨hex, -⟩ := mPeg_linear_existsUnique S hihat hii hsh h0 h0i
  refine ⟨fun ε hε => vFam_equilibrium S hβ0 hβ1 hsad hs hBm1 hB
      (fun ε _ => rateExp_sm S hihat ε) hiG hiQ hε,
    fun ε hε B P h t => vFam_unique S hβ0 hβ1 hsad hs hε h t,
    fun n ω t => vFam_contDiffOn hβ0 hβ1 hsbar (ver_bounds S hβ0 hβ1 hM shat ω)
      (fun ε hε t => hiG ε hε t ω) (fun t => (rateExp_contDiff ihat t ω).contDiffOn) t,
    fun ω hB0 t => ?_, hex, ?_, (vShock_ae S hβ0 hβ1 hs).1⟩
  · have hd := vFamInfl_hasDerivAt (iF := rateExp β ihat) hβ0 hβ1 hsbar
      (ver_bounds S hβ0 hβ1 hM shat ω) hB0 (fun ε hε t => hiG ε hε t ω)
      (fun t => rateExp_log_hasDerivAt hβ0 ihat t ω)
    cases t with
    | zero => exact hd.1
    | succ t => exact hd.2 t
  · filter_upwards [vFam_ae_mFam S hβ0 hβ1 hs (fun k => Eventually.of_forall fun _ => rfl)]
      with ω hω ε t
    rw [mFamP_eq_vFamP]
    exact vFamP_congr (fun t => (hω t).1) (fun t => (hω t).2) (fun _ _ => rfl) ε t

/-- Cochrane (2023), §2.6, pp. 39–42, **the rule family with chosen versions**, for every
`θ ∈ ℝ`: for `0 < β < 1`, `s̄ > 0`, adapted `ŝ` and `u` with `|ŝ| ≤ M` and `|u| ≤ Mu` almost
surely, and positive initial debt known at `0`, with the rate `vRuleRate` built from the chosen
versions `pvVer`, `pvExVer` and `procVer Mu u`:
* for each `ε ∈ famDom` the version family is an equilibrium satisfying the exact rule
  `log(1 + i_t) = −log β + θπ_t + εu_t` almost surely (with the original `u`);
* **in every state**, the rule's inflation and rate are `C^n` in `ε` on `famDom`, every `n`, and
  their derivatives at `0` are the solution (2.25) `ruleSol θ (procVer Mu u) (vShock) (vInfl0)`
  and its rate; **in every state with `B_{−1} ≠ 0`** the family's inflation is that closed form on
  `famDom`;
* the derivative equals the linear solution of `TidyR5MeasFamilyRule` built from the original
  `u`, `mShock` and `mInfl0` almost surely.
Generalises `TidyR5MeasFamilyRule.mRule_family_linearization`. -/
theorem version_rule_linearization {Mu : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar)
    (hsad : StronglyAdapted S.𝓕 shat) (hs : ∀ t, ∀ᵐ ω ∂S.μ, |shat t ω| ≤ M)
    (hua : StronglyAdapted S.𝓕 u) (hu : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ Mu)
    (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1) (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω) :
    (∀ ε ∈ famDom sbar M, MEquilibrium S β Bm1 (surpFam sbar shat ε)
      (vFamB β sbar (pvVer S β M shat) (pvExVer S β M shat) Bm1
        (vRuleRate β sbar (pvVer S β M shat) (pvExVer S β M shat) θ (procVer Mu u)) ε)
      (vFamP β sbar (pvVer S β M shat) (pvExVer S β M shat) Bm1
        (vRuleRate β sbar (pvVer S β M shat) (pvExVer S β M shat) θ (procVer Mu u)) ε)
      (vRuleRate β sbar (pvVer S β M shat) (pvExVer S β M shat) θ (procVer Mu u) ε) ∧
      MRuleExact S β θ Bm1 (ssV β sbar) u ε
        (vFamP β sbar (pvVer S β M shat) (pvExVer S β M shat) Bm1
          (vRuleRate β sbar (pvVer S β M shat) (pvExVer S β M shat) θ (procVer Mu u)) ε)
        (vRuleRate β sbar (pvVer S β M shat) (pvExVer S β M shat) θ (procVer Mu u) ε)) ∧
    (∀ (n : WithTop ℕ∞) (ω : Ω) (t : ℕ),
      ContDiffOn ℝ n (fun ε => vRuleInfl β sbar (pvVer S β M shat) (pvExVer S β M shat) θ
        (procVer Mu u) ε t ω) (famDom sbar M) ∧
      ContDiffOn ℝ n (fun ε => vRuleRate β sbar (pvVer S β M shat) (pvExVer S β M shat) θ
        (procVer Mu u) ε t ω) (famDom sbar M)) ∧
    (∀ ω t, HasDerivAt (fun ε => vRuleInfl β sbar (pvVer S β M shat) (pvExVer S β M shat) θ
        (procVer Mu u) ε t ω)
      (LinearFTMP.ruleSol θ (procVer Mu u) (vShock β sbar (pvVer S β M shat)
        (pvExVer S β M shat)) (vInfl0 β sbar (pvVer S β M shat)) t ω) 0) ∧
    (∀ ω, Bm1 ω ≠ 0 → ∀ ε ∈ famDom sbar M, ∀ t,
      vFamInfl β sbar (pvVer S β M shat) (pvExVer S β M shat) Bm1
        (vRuleRate β sbar (pvVer S β M shat) (pvExVer S β M shat) θ (procVer Mu u)) ε t ω =
      vRuleInfl β sbar (pvVer S β M shat) (pvExVer S β M shat) θ (procVer Mu u) ε t ω) ∧
    (∀ t, LinearFTMP.ruleSol θ (procVer Mu u) (vShock β sbar (pvVer S β M shat)
        (pvExVer S β M shat)) (vInfl0 β sbar (pvVer S β M shat)) t =ᵐ[S.μ]
      LinearFTMP.ruleSol θ u (mShock S β sbar shat) (mInfl0 S β sbar shat) t) := by
  have hM := nonneg_of_bound S hs
  have hMu := nonneg_of_bound S hu
  have hs'ad := procVer_adapted S M hsad
  have hs'b : ∀ t ω, |procVer M shat t ω| ≤ M := fun t ω => abs_clamp_le hM _
  have hss := procVer_ae S hs
  have hu'ad := procVer_adapted S Mu hua
  have hu'b : ∀ t ω, |procVer Mu u t ω| ≤ Mu := fun t ω => abs_clamp_le hMu _
  have huu := procVer_ae S hu
  obtain ⟨hYa, hXa⟩ := ver_adapted S β M shat
  have hgood := vFam_ae_mFam S hβ0 hβ1 hs hss
  have hrate : ∀ᵐ ω ∂S.μ, ∀ ε t,
      vRuleRate β sbar (pvVer S β M shat) (pvExVer S β M shat) θ (procVer Mu u) ε t ω =
        mRuleRate S β sbar (procVer M shat) θ (procVer Mu u) ε t ω := by
    filter_upwards [hgood] with ω hω ε t
    rw [mRuleRate_eq_vRuleRate]
    exact vRuleRate_congr (fun t => (hω t).1) (fun t => (hω t).2) (fun _ => rfl) ε t
  refine ⟨fun ε hε => ⟨?_, ?_⟩, fun n ω t => vRule_contDiffOn hβ0 hβ1
      (ver_bounds S hβ0 hβ1 hM shat ω) t,
    fun ω t => vRuleInfl_hasDerivAt hβ0 hβ1 hsbar t ω,
    fun ω hB0 ε hε t => vFamInfl_eq_vRuleInfl hβ0 hβ1 hsbar
      (ver_bounds S hβ0 hβ1 hM shat ω) hB0 hε t, fun t => ?_⟩
  · refine vFam_equilibrium S hβ0 hβ1 hsad hs hBm1 hB
      (fun ε _ => vRuleRate_sm S hYa hXa hu'ad ε) (fun ε _ t ω => vRuleRate_gt hβ0 ε t ω)
      (fun ε hε t => ?_) hε
    refine (mRuleRate_bondPrice_integrable S (θ := θ) hβ0 hβ1 hs'b hu'ad hu'b hB hε t).congr ?_
    filter_upwards [hrate] with ω h
    rw [h ε t]
  · intro t
    filter_upwards [hB, huu t] with ω hB' hu'
    rw [log_one_add_vRuleRate hβ0]
    have e : logInfl Bm1 (ssV β sbar) (vFamP β sbar (pvVer S β M shat) (pvExVer S β M shat)
        Bm1 (vRuleRate β sbar (pvVer S β M shat) (pvExVer S β M shat) θ (procVer Mu u)) ε) t ω =
        vFamInfl β sbar (pvVer S β M shat) (pvExVer S β M shat) Bm1
          (vRuleRate β sbar (pvVer S β M shat) (pvExVer S β M shat) θ (procVer Mu u)) ε t ω := by
      cases t <;> rfl
    rw [e, vFamInfl_eq_vRuleInfl hβ0 hβ1 hsbar (ver_bounds S hβ0 hβ1 hM shat ω) hB'.ne' hε t,
      hu']
  · obtain ⟨hsh, h0⟩ := vShock_ae S (sbar := sbar) hβ0 hβ1 hs
    exact ruleSol_congr huu hsh h0 t

end Cochrane.IntertemporalModel.TidyR6MeasFamilyVersion
