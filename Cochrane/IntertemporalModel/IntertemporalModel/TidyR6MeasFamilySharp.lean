/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.TidyR6MeasFamilyVersion
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# The sharp conditions on `î` and `u` for the families of exact equilibria

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §§2.4–2.5, pp. 31–36 (the peg
family, canonical target `1 + i_t(ε) = β⁻¹ exp(ε î_t)`) and §2.6, pp. 39–42 (the rule family
`log(1 + i_t) = −log β + θπ_t + εu_t`), on a probability space.

* The peg family: `ihat_integrable_of_exp` derives the integrability of `î` from the (necessary)
  integrability of `exp(−εî_t)` on the domain, so `version_family_linearization_exp` is
  `TidyR6MeasFamilyVersion.version_family_linearization` without its hypothesis that `î` is
  integrable.
* The rule family: inflation splits as `π_t(ε) = π⁰_t(ε) + ε w_t` with `π⁰` the family without
  the disturbance (bounded in every state, `vRuleInfl_bound` with `u = 0`) and the cumulated
  disturbance `w_{t+1} = θ w_t + u_t` (`wSum`, `vRuleInfl_split`). Hence the bond price is
  integrable iff `exp(−ε(θ w_t + u_t))` is (`vRule_bondPrice_iff`), and **the family is an
  equilibrium for every `ε ∈ famDom` iff `exp(−ε(θ w_t + u_t))` is integrable for every
  `ε ∈ famDom` and every `t`** (`vRule_equilibrium_iff`, any adapted `u`, no bound on `u`).
* `Unif.unbounded_u_rule`: the condition does not require bounded `u`: on the uniform
  distribution, `u_t = −log ω` is not essentially bounded, yet with `θ = 0` the rule family is an
  equilibrium for every `ε` in the domain.
-/

namespace Cochrane.IntertemporalModel.TidyR6MeasFamilySharp

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure TidyR5Meas
  TidyR5MeasLinear TidyR5Family TidyR5FamilyRule TidyR5MeasFamily TidyR5MeasFamilyRule
  TidyR6MeasFamilyVersion

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)
variable {β sbar M θ : ℝ} {shat ihat u : ℕ → Ω → ℝ} {Bm1 : Ω → ℝ} {Y X : ℕ → Ω → ℝ}

/-! ### The peg family: integrability of `î` is implied -/

/-- Cochrane (2023), eq. (2.16), p. 35, on a probability space: if `exp(−ε î_t)` is integrable for
every `ε ∈ famDom` (`s̄ > 0`), then `î_t` is integrable (`|x| ≤ (e^{δx} + e^{−δx})/δ` with
`±δ ∈ famDom`). -/
theorem ihat_integrable_of_exp (hsbar : 0 < sbar) (hihat : StronglyAdapted S.𝓕 ihat)
    (hexp : ∀ ε ∈ famDom sbar M, ∀ t, Integrable (fun ω => Real.exp (-(ε * ihat t ω))) S.μ)
    (t : ℕ) : Integrable (ihat t) S.μ := by
  set δ : ℝ := sbar / (|M| + 1) with hδ
  have hM1 : 0 < |M| + 1 := by positivity
  have hδ0 : 0 < δ := div_pos hsbar hM1
  have hmem : ∀ ε, |ε| = δ → ε ∈ famDom sbar M := fun ε he => by
    change |ε| * M < sbar
    rw [he]
    have : δ * (|M| + 1) = sbar := div_mul_cancel₀ _ hM1.ne'
    nlinarith [le_abs_self M]
  have h1 := hexp δ (hmem δ (abs_of_pos hδ0)) t
  have h2 := hexp (-δ) (hmem (-δ) (by rw [abs_neg, abs_of_pos hδ0])) t
  refine Integrable.mono' ((h1.add h2).div_const δ)
    (((hihat t).mono (S.𝓕.le t)).aestronglyMeasurable) (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, le_div_iff₀ hδ0, Pi.add_apply]
  have e1 := Real.add_one_le_exp (-(δ * ihat t ω))
  have e2 := Real.add_one_le_exp (-(-δ * ihat t ω))
  rcases abs_cases (ihat t ω) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
    nlinarith [Real.exp_pos (-(δ * ihat t ω)), Real.exp_pos (-(-δ * ihat t ω))]

/-- Cochrane (2023), §§2.4–2.5, pp. 31–36: `TidyR6MeasFamilyVersion.version_family_linearization`
**without the hypothesis that `î` is integrable**, which follows from the integrability of
`exp(−εî_t)` on the domain (`ihat_integrable_of_exp`); that integrability is itself necessary
(`TidyR6MeasFamilyVersion.rateExp_bondPrice_iff`, `TidyR6MeasHyp.mEqm_bondPrice_integrable`). -/
theorem version_family_linearization_exp (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar)
    (hsad : StronglyAdapted S.𝓕 shat) (hs : ∀ t, ∀ᵐ ω ∂S.μ, |shat t ω| ≤ M)
    (hihat : StronglyAdapted S.𝓕 ihat)
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
      mShock S β sbar shat t) :=
  version_family_linearization S hβ0 hβ1 hsbar hsad hs hihat
    (ihat_integrable_of_exp S hsbar hihat hexp) hexp hBm1 hB

/-! ### The rule family: the sharp condition on `u` -/

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), eq. (2.23), p. 40: the cumulated disturbance `w_0 = 0`,
`w_{t+1} = θ w_t + u_t`. -/
def wSum (θ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun ω => θ * wSum θ u t ω + u t ω

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), eq. (2.25), p. 40: inflation of the rule family splits as
`π_t(ε) = π⁰_t(ε) + ε w_t`, with `π⁰` the family without the disturbance. -/
theorem vRuleInfl_split (ε : ℝ) (t : ℕ) (ω : Ω) :
    vRuleInfl β sbar Y X θ u ε t ω = vRuleInfl β sbar Y X θ 0 ε t ω + ε * wSum θ u t ω := by
  induction t with
  | zero => simp [vRuleInfl, wSum]
  | succ t ih =>
    change -Real.log β + θ * vRuleInfl β sbar Y X θ u ε t ω + ε * u t ω +
      Real.log (β * ssV β sbar + ε * X t ω) - Real.log (ssV β sbar + ε * Y (t + 1) ω) =
      (-Real.log β + θ * vRuleInfl β sbar Y X θ 0 ε t ω + ε * (0 : ℕ → Ω → ℝ) t ω +
      Real.log (β * ssV β sbar + ε * X t ω) - Real.log (ssV β sbar + ε * Y (t + 1) ω)) +
      ε * (θ * wSum θ u t ω + u t ω)
    rw [ih]
    simp only [Pi.zero_apply]
    ring

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 40: in every state where the bounds hold, for `ε ∈ famDom` and
`|u_t| ≤ Mu` there, `|π_t(ε)| ≤ TidyR5MeasFamilyRule.ruleBound` (version form of
`TidyR5MeasFamilyRule.mRuleInfl_bound`). -/
theorem vRuleInfl_bound {Mu : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {ω : Ω} (hω : Bounds β M Y X ω)
    (hu : ∀ t, |u t ω| ≤ Mu) {ε : ℝ} (hε : ε ∈ famDom sbar M) (t : ℕ) :
    |vRuleInfl β sbar Y X θ u ε t ω| ≤ ruleBound β sbar M θ Mu ε t := by
  have hε' : |ε| * M < sbar := hε
  have hL : 0 < (1 - β)⁻¹ * (sbar - |ε| * M) := mul_pos (inv_pos.mpr (by linarith))
    (by linarith)
  have hpv : ∀ t, |Real.log (ssV β sbar + ε * Y t ω)| ≤
      |Real.log ((1 - β)⁻¹ * (sbar - |ε| * M))| +
        |Real.log ((1 - β)⁻¹ * (sbar + |ε| * M))| := fun t =>
    abs_log_le hL (le_aff (hω t).1) (aff_le (hω t).1)
  have hpvE : ∀ t, |Real.log (β * ssV β sbar + ε * X t ω)| ≤
      |Real.log (β * ((1 - β)⁻¹ * (sbar - |ε| * M)))| +
        |Real.log (β * ((1 - β)⁻¹ * (sbar + |ε| * M)))| := by
    intro t
    have hX : |X t ω / β| ≤ (1 - β)⁻¹ * M := by
      rw [abs_div, abs_of_pos hβ0, div_le_iff₀ hβ0]
      linarith [(hω t).2]
    have e : β * ssV β sbar + ε * X t ω = β * (ssV β sbar + ε * (X t ω / β)) := by
      field_simp
    rw [e]
    exact abs_log_le (mul_pos hβ0 hL) (mul_le_mul_of_nonneg_left (le_aff hX) hβ0.le)
      (mul_le_mul_of_nonneg_left (aff_le hX) hβ0.le)
  induction t with
  | zero =>
    change |Real.log (ssV β sbar) - Real.log (ssV β sbar + ε * Y 0 ω)| ≤ _
    exact (abs_sub _ _).trans (add_le_add le_rfl (hpv 0))
  | succ t ih =>
    change |-Real.log β + θ * vRuleInfl β sbar Y X θ u ε t ω + ε * u t ω +
      Real.log (β * ssV β sbar + ε * X t ω) - Real.log (ssV β sbar + ε * Y (t + 1) ω)| ≤ _
    have h1 : |θ * vRuleInfl β sbar Y X θ u ε t ω| ≤ |θ| * ruleBound β sbar M θ Mu ε t := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ih (abs_nonneg θ)
    have h2 : |ε * u t ω| ≤ |ε| * Mu := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hu t) (abs_nonneg ε)
    have h3 := hpvE t
    have h4 := hpv (t + 1)
    simp only [ruleBound]
    calc _ ≤ |-Real.log β + θ * vRuleInfl β sbar Y X θ u ε t ω + ε * u t ω +
          Real.log (β * ssV β sbar + ε * X t ω)| +
          |Real.log (ssV β sbar + ε * Y (t + 1) ω)| := abs_sub _ _
      _ ≤ |-Real.log β + θ * vRuleInfl β sbar Y X θ u ε t ω + ε * u t ω| +
          |Real.log (β * ssV β sbar + ε * X t ω)| +
          |Real.log (ssV β sbar + ε * Y (t + 1) ω)| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ |-Real.log β + θ * vRuleInfl β sbar Y X θ u ε t ω| + |ε * u t ω| +
          |Real.log (β * ssV β sbar + ε * X t ω)| +
          |Real.log (ssV β sbar + ε * Y (t + 1) ω)| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ |-Real.log β| + |θ * vRuleInfl β sbar Y X θ u ε t ω| + |ε * u t ω| +
          |Real.log (β * ssV β sbar + ε * X t ω)| +
          |Real.log (ssV β sbar + ε * Y (t + 1) ω)| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ _ := by
        rw [abs_neg]
        linarith

/-- Cochrane (2023), eq. (2.3), p. 22, on a probability space, **the sharp condition on `u`**: for
adapted versions bounded in every state, an adapted `u` (no bound) and `ε ∈ famDom`, the bond
price of the rule family is integrable iff `exp(−ε(θ w_t + u_t))` is integrable. -/
theorem vRule_bondPrice_iff (hβ0 : 0 < β) (hβ1 : β < 1) (hY : StronglyAdapted S.𝓕 Y)
    (hX : StronglyAdapted S.𝓕 X) (hb : ∀ ω, Bounds β M Y X ω) {ε : ℝ}
    (hε : ε ∈ famDom sbar M) (t : ℕ) :
    Integrable (fun ω => (1 + vRuleRate β sbar Y X θ u ε t ω)⁻¹) S.μ ↔
      Integrable (fun ω => Real.exp (-(ε * (θ * wSum θ u t ω + u t ω)))) S.μ := by
  set K := ruleBound β sbar M θ 0 ε t with hKdef
  set π0 : Ω → ℝ := fun ω => vRuleInfl β sbar Y X θ 0 ε t ω with hπ0
  have hK : ∀ ω, |π0 ω| ≤ K := fun ω =>
    vRuleInfl_bound (u := 0) hβ0 hβ1 (hb ω) (fun _ => by simp) hε t
  have hπm : Measurable π0 := ((vRuleInfl_sm S hY hX (u := 0) (θ := θ)
    (fun _ => stronglyMeasurable_zero) ε t).mono (S.𝓕.le t)).measurable
  have hθK : ∀ ω, |θ * π0 ω| ≤ |θ| * K := fun ω => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hK ω) (abs_nonneg θ)
  have key : ∀ ω, (1 + vRuleRate β sbar Y X θ u ε t ω)⁻¹ =
      (β * Real.exp (-(θ * π0 ω))) * Real.exp (-(ε * (θ * wSum θ u t ω + u t ω))) := fun ω => by
    simp only [vRuleRate, add_sub_cancel, hπ0]
    rw [vRuleInfl_split, mul_inv, inv_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  constructor
  · intro h
    have hb' : ∀ᵐ ω ∂S.μ, ‖(β * Real.exp (-(θ * π0 ω)))⁻¹‖ ≤ β⁻¹ * Real.exp (|θ| * K) :=
      Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_inv, abs_of_pos (mul_pos hβ0 (Real.exp_pos _)), mul_inv,
          ← Real.exp_neg, neg_neg]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          ((le_abs_self _).trans (hθK ω))) (inv_nonneg.mpr hβ0.le)
    refine (h.bdd_mul (((measurable_const.mul (hπm.const_mul θ).neg.exp).inv
      ).aestronglyMeasurable) hb').congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.neg_apply]
    rw [key ω, ← mul_assoc, inv_mul_cancel₀ (mul_pos hβ0 (Real.exp_pos _)).ne', one_mul]
  · intro h
    have hb' : ∀ᵐ ω ∂S.μ, ‖β * Real.exp (-(θ * π0 ω))‖ ≤ β * Real.exp (|θ| * K) :=
      Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (mul_pos hβ0 (Real.exp_pos _))]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          ((neg_le_abs _).trans (hθK ω))) hβ0.le
    exact (h.bdd_mul ((measurable_const.mul (hπm.const_mul θ).neg.exp).aestronglyMeasurable)
      hb').congr (Eventually.of_forall fun ω => (key ω).symm)

/-- Cochrane (2023), §2.6, pp. 39–42, on a probability space, **the exact condition on the
disturbance**: for `0 < β < 1`, adapted `ŝ` bounded almost surely, **any adapted `u`** and
positive initial debt known at `0`, the version rule family (built with the original `u`) is an
equilibrium for every `ε ∈ famDom` iff `exp(−ε(θ w_t + u_t))` is integrable for every
`ε ∈ famDom` and every date (`w` the cumulated disturbance).
Sharpens the equilibrium part of `TidyR6MeasFamilyVersion.version_rule_linearization`. -/
theorem vRule_equilibrium_iff (hβ0 : 0 < β) (hβ1 : β < 1) (hsad : StronglyAdapted S.𝓕 shat)
    (hs : ∀ t, ∀ᵐ ω ∂S.μ, |shat t ω| ≤ M) (hua : StronglyAdapted S.𝓕 u)
    (hBm1 : StronglyMeasurable[S.𝓕 0] Bm1) (hB : ∀ᵐ ω ∂S.μ, 0 < Bm1 ω) :
    (∀ ε ∈ famDom sbar M, MEquilibrium S β Bm1 (surpFam sbar shat ε)
      (vFamB β sbar (pvVer S β M shat) (pvExVer S β M shat) Bm1
        (vRuleRate β sbar (pvVer S β M shat) (pvExVer S β M shat) θ u) ε)
      (vFamP β sbar (pvVer S β M shat) (pvExVer S β M shat) Bm1
        (vRuleRate β sbar (pvVer S β M shat) (pvExVer S β M shat) θ u) ε)
      (vRuleRate β sbar (pvVer S β M shat) (pvExVer S β M shat) θ u ε)) ↔
    ∀ ε ∈ famDom sbar M, ∀ t,
      Integrable (fun ω => Real.exp (-(ε * (θ * wSum θ u t ω + u t ω)))) S.μ := by
  have hM := nonneg_of_bound S hs
  obtain ⟨hYa, hXa⟩ := ver_adapted S β M shat
  have hb := ver_bounds S hβ0 hβ1 hM shat
  constructor
  · intro h ε hε t
    exact (vRule_bondPrice_iff S hβ0 hβ1 hYa hXa hb hε t).mp
      (TidyR6MeasHyp.mEqm_bondPrice_integrable S (h ε hε) t)
  · intro h ε hε
    exact vFam_equilibrium S hβ0 hβ1 hsad hs hBm1 hB (fun ε _ => vRuleRate_sm S hYa hXa hua ε)
      (fun ε _ t ω => vRuleRate_gt hβ0 ε t ω)
      (fun ε hε t => (vRule_bondPrice_iff S hβ0 hβ1 hYa hXa hb hε t).mpr (h ε hε t)) hε

/-! ### Bounded `u` is not necessary -/

namespace Unif

open TidyR6MeasHyp.Uniform

/-- Cochrane (2023), eq. (2.23), p. 40: the unbounded disturbance `u_t = −log ω` on the uniform
distribution (with the positive version of `ω`). -/
noncomputable def uLog : ℕ → ℝ → ℝ := fun _ x => -Real.log (posVer x)

/-- Cochrane (2023), §2.6, pp. 39–42, the sharp condition in action: on the uniform distribution
with full information, `β = 1/2`, `s̄ = 1/2`, `ŝ = 0` (`M = 1`), `θ = 0` and `B_{−1} = 1`, the
disturbance `u_t = −log ω` is not essentially bounded, yet the rule family is an equilibrium for
every `ε ∈ famDom` (`exp(−εu_t) = ω^ε` is integrable for `ε > −1`): boundedness of `u` is
sufficient but not necessary. -/
theorem unbounded_u_rule :
    (¬ ∃ K, ∀ t, ∀ᵐ ω ∂unifSystem.μ, |uLog t ω| ≤ K) ∧
    ∀ ε ∈ famDom (1 / 2) 1, MEquilibrium unifSystem (1 / 2) (fun _ => 1)
      (surpFam (1 / 2) 0 ε)
      (vFamB (1 / 2) (1 / 2) (pvVer unifSystem (1 / 2) 1 0) (pvExVer unifSystem (1 / 2) 1 0)
        (fun _ => 1) (vRuleRate (1 / 2) (1 / 2) (pvVer unifSystem (1 / 2) 1 0)
          (pvExVer unifSystem (1 / 2) 1 0) 0 uLog) ε)
      (vFamP (1 / 2) (1 / 2) (pvVer unifSystem (1 / 2) 1 0) (pvExVer unifSystem (1 / 2) 1 0)
        (fun _ => 1) (vRuleRate (1 / 2) (1 / 2) (pvVer unifSystem (1 / 2) 1 0)
          (pvExVer unifSystem (1 / 2) 1 0) 0 uLog) ε)
      (vRuleRate (1 / 2) (1 / 2) (pvVer unifSystem (1 / 2) 1 0)
        (pvExVer unifSystem (1 / 2) 1 0) 0 uLog ε) := by
  have hum : Measurable (uLog 0) := measurable_posVer.log.neg
  refine ⟨?_, (vRule_equilibrium_iff unifSystem (by norm_num) (by norm_num)
    (fun _ => stronglyMeasurable_zero) (fun _ => Eventually.of_forall fun _ => by simp)
    (fun _ => hum.stronglyMeasurable) stronglyMeasurable_const
    (Eventually.of_forall fun _ => one_pos)).mpr fun ε hε t => ?_⟩
  · rintro ⟨K, hK⟩
    apply posVer_inv_not_integrable
    refine Integrable.of_bound (measurable_posVer.inv.aestronglyMeasurable) (Real.exp K) ?_
    filter_upwards [hK 0] with x hx
    have hp := posVer_pos x
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), ← Real.exp_log (inv_pos.mpr hp),
      Real.log_inv]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans hx)
  · have hε' : |ε| * 1 < 1 / 2 := hε
    have hr : -1 < ε := by
      have := neg_abs_le ε
      linarith
    have hI : IntegrableOn (fun x : ℝ => x ^ ε) (Set.Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' hr)
    refine (show Integrable (fun x : ℝ => x ^ ε) unifSystem.μ from hI).congr ?_
    filter_upwards [ae_pos] with x hx
    simp only [uLog, zero_mul, zero_add, mul_neg, neg_neg, posVer, hx, ↓reduceIte]
    rw [Real.rpow_def_of_pos hx, mul_comm]

end Unif

end Cochrane.IntertemporalModel.TidyR6MeasFamilySharp
