/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR7StochWerningExist

/-!
# Equilibrium selection under uncertainty: the active rule (20.7), `π_T`, and `π_0`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.2, pp. 474–477
(equation (20.7) and the two selections of Figure 20.4), §20.2.4, pp. 478–479.

The book selects among the bounded equilibria of the trap experiment in two ways: the
new-Keynesian choice of `π_T` (enforced by an active rule `i = i* + φ(π − π*)` after the trap,
(20.7)), and the fiscal choice of the time-0 jump (`π_0 = 0`). Under uncertainty:

* **`active_rule_selects`** (stochastic (20.7)): after `T`, an active rule `φ > 1` selects the
  chosen deterministic path as the unique `L¹`-bounded equilibrium *state by state*:
  `π_t = π*_t` and `x_t = x*_t` almost surely for every `t ≥ T`. The rule rules out every
  sunspot or fiscal innovation after `T`.
* **`nk_selection`**: in the trap experiment, pinning `π_T` (a.s. equal to a constant `c`)
  removes all uncertainty before `T`: `π_s = wPi(c)_s` and `x_s = wX(c)_s` almost surely for
  `0 ≤ s ≤ T`. So the new-Keynesian selection carries over to uncertainty unchanged.
* **`fiscal_pi0_mean`**: pinning only `π_0 = c` determines the mean path,
  `E π_t = wPi(0)_t + e^{−λ^b t}(c − wPi(0)_0)` (with `c = 0` the no-jump equilibrium of
  p. 476), but **not** the equilibrium: `pi0_not_selects` exhibits, on bmPath at the book's
  calibration, two different mean-square-bounded equilibria with `π_0 = 0` (innovation
  loadings `0` and `1`). Under uncertainty the fiscal selection must specify the inflation
  innovation at every date (the continuous-time analogue of `ΔE_{t+1}π_{t+1}` in discrete time,
  p. 476), not only at time `0`; this is the one place where the deterministic statement needs
  strengthening under uncertainty.
-/

namespace Cochrane.ZeroBound.TidyR7StochWerningSelect

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.ContinuousTimeNK Cochrane.ZeroBound.WerningModel
open Cochrane.ZeroBound.TidyR7StochWerning Cochrane.ZeroBound.TidyR7StochWerningTrap
open Cochrane.ZeroBound.TidyR7StochWerningExist
open Cochrane.ZeroBound.TidyR7BrownianTools
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Cochrane (2023), §20.2.2, p. 474 (tool): an integrable `𝓕_s`-measurable `Z` whose integral
over every `A ∈ 𝓕_s` is `P(A)c` is almost surely `c`.
From Mathlib `ae_eq_condExp_of_forall_setIntegral_eq` and `condExp_of_stronglyMeasurable`. -/
theorem ae_eq_const_of_setIntegral [IsProbabilityMeasure P] {𝓕 : Filtration ℝ mΩ} {s : ℝ}
    {Z : Ω → ℝ} (hZm : StronglyMeasurable[𝓕 s] Z) (hZi : Integrable Z P) (c : ℝ)
    (h : ∀ A, MeasurableSet[𝓕 s] A → ∫ ω in A, Z ω ∂P = P.real A * c) :
    Z =ᵐ[P] fun _ => c := by
  have h1 : (fun _ => c) =ᵐ[P] P[Z | 𝓕 s] :=
    ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) hZi (fun _ _ _ => integrableOn_const)
      (fun A hA _ => by rw [h A hA, setIntegral_const, smul_eq_mul])
      stronglyMeasurable_const.aestronglyMeasurable
  rw [condExp_of_stronglyMeasurable (𝓕.le s) hZm hZi] at h1
  exact h1.symm

/-- **Cochrane (2023), (20.7), p. 474, under uncertainty: an active rule after the trap selects
the chosen path state by state.** Let `(x*, π*)` be a deterministic continuous path, bounded on
`[T, ∞)`, solving (20.5)–(20.6) in integral form on `[T, ∞)` with interest rate `i*`. Let `x, π`
be regular `L¹`-bounded processes with, from `T` on, `E_t dx = σ(i* + φ(π − π*) − π − u)dt`
and `E_t dπ = (ρπ − κ(x + g))dt`. If `σ, κ, ρ > 0` and `φ > 1`, then `π_t = π*_t` and
`x_t = x*_t` almost surely for every `t ≥ T`. -/
theorem active_rule_selects [IsProbabilityMeasure P] {σ κ ρ φ T : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hρ : 0 < ρ) (hφ : 1 < φ) (hT : 0 ≤ T) {𝓕 : Filtration ℝ mΩ} {istar u g xs πs : ℝ → ℝ}
    (hi : ∀ a b, IntegrableOn istar (Set.Ioc a b)) (hu : ∀ a b, IntegrableOn u (Set.Ioc a b))
    (hg : ∀ a b, IntegrableOn g (Set.Ioc a b)) (hxsc : Continuous xs) (hπsc : Continuous πs)
    (hxsb : BddOnIci xs) (hπsb : BddOnIci πs)
    (hdet : ∀ s t, T ≤ s → s ≤ t → xs t - xs s = ∫ r in s..t, σ * (istar r - πs r - u r) ∧
      πs t - πs s = ∫ r in s..t, (ρ * πs r - κ * (xs r + g r)))
    {x π : ℝ → Ω → ℝ} (hx : Regular 𝓕 x) (hxb : BddL1 P x) (hπ : Regular 𝓕 π)
    (hπb : BddL1 P π)
    (hdx : ExpDriftFrom P 𝓕 T x
      (fun r ω => σ * ((istar r + φ * (π r ω - πs r)) - π r ω - u r)))
    (hdπ : ExpDriftFrom P 𝓕 T π (fun r ω => ρ * π r ω - κ * (x r ω + g r))) {t : ℝ}
    (ht : T ≤ t) :
    π t =ᵐ[P] (fun _ => πs t) ∧ x t =ᵐ[P] (fun _ => xs t) := by
  obtain ⟨Kx, hKx⟩ := hxb
  obtain ⟨Kπ, hKπ⟩ := hπb
  obtain ⟨Kxs, hKxs⟩ := hxsb
  obtain ⟨Kπs, hKπs⟩ := hπsb
  have hmx : ∀ t, Measurable (x t) := fun t => ((hx.2 t).mono (𝓕.le t)).measurable
  have hmπ : ∀ t, Measurable (π t) := fun t => ((hπ.2 t).mono (𝓕.le t)).measurable
  have ht0 : 0 ≤ t := hT.trans ht
  -- conditional means on `A ∈ 𝓕_t`, from date `t` on
  have key : ∀ A, MeasurableSet[𝓕 t] A →
      ∫ ω in A, π t ω ∂P = P.real A * πs t ∧ ∫ ω in A, x t ω ∂P = P.real A * xs t := by
    intro A hA
    set p := P.real A
    set mx : ℝ → ℝ := fun r => ∫ ω in A, x r ω ∂P
    set mπ : ℝ → ℝ := fun r => ∫ ω in A, π r ω ∂P
    have hbx : ∀ r, 0 ≤ r → |mx r| ≤ Kx := fun r hr => abs_setIntegral_le hKx A hr
    have hbπ : ∀ r, 0 ≤ r → |mπ r| ≤ Kπ := fun r hr => abs_setIntegral_le hKπ A hr
    have hix : ∀ b, IntegrableOn mx (Set.Icc t b) := fun b =>
      Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
        (stronglyMeasurable_setIntegral hx.1 hmx A).aestronglyMeasurable (M := Kx)
        (ae_restrict_of_forall_mem measurableSet_Icc fun r hr => by
          rw [Real.norm_eq_abs]; exact hbx r (ht0.trans hr.1))
    have hiπ : ∀ b, IntegrableOn mπ (Set.Icc t b) := fun b =>
      Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
        (stronglyMeasurable_setIntegral hπ.1 hmπ A).aestronglyMeasurable (M := Kπ)
        (ae_restrict_of_forall_mem measurableSet_Icc fun r hr => by
          rw [Real.norm_eq_abs]; exact hbπ r (ht0.trans hr.1))
    -- the integral forms of the conditional means (as in `condMean_integral_eq`)
    have hfx : ∀ v, t ≤ v → mx v - mx t = ∫ r in t..v,
        σ * (p * istar r + φ * (mπ r - p * πs r) - mπ r - p * u r) := fun v hv => by
      have px := integrable_prod_proc (P := P) hx.1 hmx hKx ht0 (b := v)
      have pπ := integrable_prod_proc (P := P) hπ.1 hmπ hKπ ht0 (b := v)
      have pi := integrable_prod_det (P := P) (hi t v)
      have pu := integrable_prod_det (P := P) (hu t v)
      have pπs := integrable_prod_det (P := P)
        ((hπsc.integrableOn_Icc (a := t) (b := v)).mono_set Set.Ioc_subset_Icc_self)
      rw [setIntegral_expDrift hdx ht hv hA (hKx t ht0).1 (hKx v (ht0.trans hv)).1
        ((((pi.add ((pπ.sub pπs).const_mul φ)).sub pπ).sub pu).const_mul σ)]
      refine intervalIntegral.integral_congr fun r hr => ?_
      have hr0 : 0 ≤ r := ht0.trans (by rw [Set.uIcc_of_le hv] at hr; exact hr.1)
      have h1 := (hKπ r hr0).1.integrableOn (s := A)
      have e1 : Integrable (fun ω => istar r + φ * (π r ω - πs r)) (P.restrict A) :=
        (integrable_const _).add ((h1.sub (integrable_const _)).const_mul φ)
      have e2 : Integrable (fun ω => istar r + φ * (π r ω - πs r) - π r ω) (P.restrict A) :=
        e1.sub h1
      have e3 : Integrable (fun ω => π r ω - πs r) (P.restrict A) := h1.sub (integrable_const _)
      rw [integral_const_mul, integral_sub e2 (integrable_const _), integral_sub e1 h1,
        integral_add (integrable_const _) (e3.const_mul φ), integral_const_mul,
        integral_sub h1 (integrable_const _), setIntegral_const, setIntegral_const,
        setIntegral_const, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    have hfπ : ∀ v, t ≤ v → mπ v - mπ t = ∫ r in t..v, (ρ * mπ r - κ * (mx r + p * g r)) :=
      fun v hv => by
      have px := integrable_prod_proc (P := P) hx.1 hmx hKx ht0 (b := v)
      have pπ := integrable_prod_proc (P := P) hπ.1 hmπ hKπ ht0 (b := v)
      have pg := integrable_prod_det (P := P) (hg t v)
      rw [setIntegral_expDrift hdπ ht hv hA (hKπ t ht0).1 (hKπ v (ht0.trans hv)).1
        ((pπ.const_mul ρ).sub ((px.add pg).const_mul κ))]
      refine intervalIntegral.integral_congr fun r hr => ?_
      have hr0 : 0 ≤ r := ht0.trans (by rw [Set.uIcc_of_le hv] at hr; exact hr.1)
      have h1 := (hKπ r hr0).1.integrableOn (s := A)
      have h2 := (hKx r hr0).1.integrableOn (s := A)
      have e1 : Integrable (fun ω => ρ * π r ω) (P.restrict A) := h1.const_mul ρ
      have e2 : Integrable (fun ω => κ * (x r ω + g r)) (P.restrict A) :=
        (h2.add (integrable_const (g r))).const_mul κ
      rw [integral_sub e1 e2, integral_const_mul, integral_const_mul,
        integral_add h2 (integrable_const (g r)), setIntegral_const, smul_eq_mul]
    -- continuity of the conditional means
    have icc : ∀ {f : ℝ → ℝ}, (∀ a b, IntegrableOn f (Set.Ioc a b)) → ∀ b,
        IntegrableOn f (Set.Icc t b) := fun hf b =>
      (integrableOn_Icc_iff_integrableOn_Ioc (by simp)).2 (hf t b)
    have hcx : ContinuousOn mx (Set.Ici t) := continuousOn_of_intForm (fun b =>
      (((((icc hi b).const_mul p).add (((hiπ b).sub
        ((hπsc.integrableOn_Icc (a := t) (b := b)).const_mul p)).const_mul φ)).sub
          (hiπ b)).sub ((icc hu b).const_mul p)).const_mul σ) hfx
    have hcπ : ContinuousOn mπ (Set.Ici t) := continuousOn_of_intForm (fun b =>
      ((hiπ b).const_mul ρ).sub (((hix b).add ((icc hg b).const_mul p)).const_mul κ)) hfπ
    -- the deviations from `P(A)·(x*, π*)` solve the active deviation system
    have ii : ∀ v, t ≤ v → ∀ {f : ℝ → ℝ}, (∀ a b, IntegrableOn f (Set.Ioc a b)) →
        IntervalIntegrable f volume t v := fun v hv f hf =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hv).2 (hf t v)
    have hii : ∀ v, t ≤ v → ∀ G : ℝ → ℝ, (∀ b, IntegrableOn G (Set.Icc t b)) →
        IntervalIntegrable G volume t v := fun v hv G hG =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hv).2 ((hG v).mono_set Set.Ioc_subset_Icc_self)
    have hd1 : ∀ v, t ≤ v → (mx v - p * xs v) - (mx t - p * xs t) =
        ∫ r in t..v, σ * (φ - 1) * (mπ r - p * πs r) := fun v hv => by
      have e : (mx v - p * xs v) - (mx t - p * xs t) = (mx v - mx t) - p * (xs v - xs t) := by
        ring
      have j1 : IntervalIntegrable
          (fun r => σ * (p * istar r + φ * (mπ r - p * πs r) - mπ r - p * u r)) volume t v :=
        hii v hv _ fun b => (((((icc hi b).const_mul p).add (((hiπ b).sub
          ((hπsc.integrableOn_Icc (a := t) (b := b)).const_mul p)).const_mul φ)).sub
            (hiπ b)).sub ((icc hu b).const_mul p)).const_mul σ
      have j2 : IntervalIntegrable (fun r => p * (σ * (istar r - πs r - u r))) volume t v :=
        ((((ii v hv hi).sub (hπsc.intervalIntegrable t v)).sub (ii v hv hu)).const_mul
          σ).const_mul p
      rw [e, hfx v hv, (hdet t v ht hv).1, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub j1 j2]
      refine intervalIntegral.integral_congr fun r _ => ?_
      ring
    have hd2 : ∀ v, t ≤ v → (mπ v - p * πs v) - (mπ t - p * πs t) =
        ∫ r in t..v, (ρ * (mπ r - p * πs r) - κ * (mx r - p * xs r)) := fun v hv => by
      have e : (mπ v - p * πs v) - (mπ t - p * πs t) = (mπ v - mπ t) - p * (πs v - πs t) := by
        ring
      have j1 : IntervalIntegrable (fun r => ρ * mπ r - κ * (mx r + p * g r)) volume t v :=
        hii v hv _ fun b =>
          ((hiπ b).const_mul ρ).sub (((hix b).add ((icc hg b).const_mul p)).const_mul κ)
      have j2 : IntervalIntegrable (fun r => p * (ρ * πs r - κ * (xs r + g r))) volume t v :=
        (((hπsc.intervalIntegrable t v).const_mul ρ).sub (((hxsc.intervalIntegrable t v).add
          (ii v hv hg)).const_mul κ)).const_mul p
      rw [e, hfπ v hv, (hdet t v ht hv).2, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub j1 j2]
      refine intervalIntegral.integral_congr fun r _ => ?_
      ring
    have hdc : ContinuousOn (fun r => mx r - p * xs r) (Set.Ici t) :=
      hcx.sub (continuousOn_const.mul hxsc.continuousOn)
    have hpc : ContinuousOn (fun r => mπ r - p * πs r) (Set.Ici t) :=
      hcπ.sub (continuousOn_const.mul hπsc.continuousOn)
    have hp0 : 0 ≤ p := measureReal_nonneg
    have hz := active_rule_dev_zero (T := t) (S := ∅) Set.countable_empty hσ hκ hρ hφ hpc hdc
      (fun r hr _ => ⟨hasDerivAt_of_intForm (G := fun r => σ * (φ - 1) * (mπ r - p * πs r))
          (continuousOn_const.mul hpc) hd1 hr,
        hasDerivAt_of_intForm (G := fun r => ρ * (mπ r - p * πs r) - κ * (mx r - p * xs r))
          ((continuousOn_const.mul hpc).sub (continuousOn_const.mul hdc)) hd2 hr⟩)
      (Kπ + p * Kπs) (Kx + p * Kxs)
      (fun r hr => (abs_sub _ _).trans (add_le_add (hbπ r (ht0.trans hr)) (by
        rw [abs_mul, abs_of_nonneg hp0]
        exact mul_le_mul_of_nonneg_left (hKπs r (ht0.trans hr)) hp0)))
      (fun r hr => (abs_sub _ _).trans (add_le_add (hbx r (ht0.trans hr)) (by
        rw [abs_mul, abs_of_nonneg hp0]
        exact mul_le_mul_of_nonneg_left (hKxs r (ht0.trans hr)) hp0)))
    obtain ⟨z1, z2⟩ := hz t le_rfl
    exact ⟨by linarith, by linarith⟩
  exact ⟨ae_eq_const_of_setIntegral (hπ.2 t) (hKπ t ht0).1 (πs t) fun A hA => (key A hA).1,
    ae_eq_const_of_setIntegral (hx.2 t) (hKx t ht0).1 (xs t) fun A hA => (key A hA).2⟩

/-- Cochrane (2023), (20.7), p. 474 (non-vacuity of the hypotheses): the chosen path itself,
as a deterministic process, satisfies every hypothesis of `active_rule_selects` (here the steady
state `x* = π* = 0` with `i* = u = g = 0`, on any filtered probability space). -/
theorem active_rule_hyps_zero [IsProbabilityMeasure P] (𝓕 : Filtration ℝ mΩ) (σ κ ρ φ T : ℝ) :
    ExpDriftFrom P 𝓕 T (fun _ _ => (0 : ℝ))
        (fun r ω => σ * ((0 + φ * ((fun _ _ => (0 : ℝ)) r ω - 0)) - (fun _ _ => (0 : ℝ)) r ω - 0)) ∧
      ExpDriftFrom P 𝓕 T (fun _ _ => (0 : ℝ))
        (fun r ω => ρ * (fun _ _ => (0 : ℝ)) r ω - κ * ((fun _ _ => (0 : ℝ)) r ω + 0)) ∧
      Regular 𝓕 (fun _ _ => (0 : ℝ)) ∧ BddL1 P (fun _ _ => (0 : ℝ)) := by
  refine ⟨fun s t _ _ => ⟨by simp, by simp [Pi.zero_def]⟩,
    fun s t _ _ => ⟨by simp, by simp [Pi.zero_def]⟩,
    regular_zero 𝓕, bddL1_zero⟩

/-! ## The two selections of Figure 20.4 under uncertainty -/

/-- Cochrane (2023), §20.2.2, pp. 475–476 ("the new-Keynesian approach … picks … `π_T = 0`"),
under uncertainty: **pinning `π_T` removes all uncertainty before `T`.** If `π_T = c` almost
surely in a bounded stochastic equilibrium of the experiment, then `π_s = wPi(c)_s` and
`x_s = wX(c)_s` almost surely for every `0 ≤ s ≤ T`. -/
theorem nk_selection [IsProbabilityMeasure P] {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} {x π : ℝ → Ω → ℝ} (hx : Regular 𝓕 x) (hxb : BddL1 P x)
    (hπ : Regular 𝓕 π) (hπb : BddL1 P π)
    (h : IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T) (fun _ _ => 0) x π)
    (c : ℝ) (hc : π T =ᵐ[P] fun _ => c) {s : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) :
    π s =ᵐ[P] (fun _ => wPi σ κ ρ T u g c s) ∧ x s =ᵐ[P] (fun _ => wX σ κ ρ T u g c s) := by
  have hcT : P[π T | 𝓕 s] =ᵐ[P] fun _ => c := by
    have := condExp_congr_ae (m := 𝓕 s) hc
    rw [condExp_const (𝓕.le s)] at this
    exact this
  obtain ⟨Kπ, hKπ⟩ := hπb
  obtain ⟨Kx, hKx⟩ := hxb
  have e1 := condExp_pi_eq_wPi hσ hκ hx ⟨Kx, hKx⟩ hπ ⟨Kπ, hKπ⟩ h hs hsT le_rfl
  have e2 := condExp_x_eq_wX hσ hκ hx ⟨Kx, hKx⟩ hπ ⟨Kπ, hKπ⟩ h hs hsT le_rfl
  rw [condExp_of_stronglyMeasurable (𝓕.le s) (hπ.2 s) (hKπ s hs).1] at e1
  rw [condExp_of_stronglyMeasurable (𝓕.le s) (hx.2 s) (hKx s hs).1] at e2
  refine ⟨?_, ?_⟩
  · filter_upwards [e1, hcT] with ω h1 h2
    rw [h1, h2]
  · filter_upwards [e2, hcT] with ω h1 h2
    rw [h1, h2]

/-- Cochrane (2023), §20.2.2, p. 476 ("I focus on the equilibrium with … no inflation jump,
`π_0 = 0`"), under uncertainty: **pinning `π_0 = c` determines the mean path**:
`E π_t = wPi(0)_t + e^{−λ^b t}(c − wPi(0)_0)` for `t ≥ 0`. -/
theorem fiscal_pi0_mean [IsProbabilityMeasure P] {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} {x π : ℝ → Ω → ℝ} (hx : Regular 𝓕 x) (hxb : BddL1 P x)
    (hπ : Regular 𝓕 π) (hπb : BddL1 P π)
    (h : IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T) (fun _ _ => 0) x π)
    (c : ℝ) (hc : π 0 =ᵐ[P] fun _ => c) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, π t ω ∂P = wPi σ κ ρ T u g 0 t +
      Real.exp (-(lamb ρ κ σ * t)) * (c - wPi σ κ ρ T u g 0 0) := by
  have hA : MeasurableSet[𝓕 0] (Set.univ : Set Ω) := MeasurableSet.univ
  obtain ⟨a1, -⟩ := setIntegral_trap hσ hκ hx hxb hπ hπb h le_rfl hA t ht
  simp only [Measure.restrict_univ, probReal_univ, one_mul, sub_zero] at a1
  rw [a1, integral_congr_ae hc, integral_const, probReal_univ, one_smul]

/-- Cochrane (2023), §20.2.2, p. 476, under uncertainty: **`π_0 = 0` does not select the
equilibrium.** On bmPath at the book's calibration (`ρ = 0.05`, `σ = κ = 1`, `T = 5`,
`u_r = −2%`, `g = 0`) there is a `π_T` such that the processes with innovation loadings `0` and
`1` are both stochastic equilibria with `π_0 = 0` on every path, both bounded in mean square,
and they are different. The fiscal selection must specify the innovations at every date. -/
theorem pi0_not_selects :
    ∃ πT : ℝ,
      (∀ b ω, eqPi 1 1 (1 / 20) 5 (-2 / 100) 0 πT b TidyR7BrownianExist.bmPath 0 ω = 0) ∧
      (∀ b, IsStochEqm 1 (1 / 20) 1 TidyR7BrownianSchauder.gaussSeq
        (bmFiltrationReal TidyR7BrownianExist.bmPath TidyR7BrownianExist.measurable_bmPath)
        (fun _ => 0) (trapStep (-2 / 100) 5) (trapStep 0 5) (fun _ _ => 0)
        (eqX 1 1 (1 / 20) 5 (-2 / 100) 0 πT b TidyR7BrownianExist.bmPath)
        (eqPi 1 1 (1 / 20) 5 (-2 / 100) 0 πT b TidyR7BrownianExist.bmPath) ∧
        BddL2 TidyR7BrownianSchauder.gaussSeq
          (eqPi 1 1 (1 / 20) 5 (-2 / 100) 0 πT b TidyR7BrownianExist.bmPath)) ∧
      ¬ ∀ t, 0 ≤ t →
        eqPi 1 1 (1 / 20) 5 (-2 / 100) 0 πT 0 TidyR7BrownianExist.bmPath t
          =ᵐ[TidyR7BrownianSchauder.gaussSeq]
        eqPi 1 1 (1 / 20) 5 (-2 / 100) 0 πT 1 TidyR7BrownianExist.bmPath t := by
  have := TidyR7BrownianSchauder.isProbabilityMeasure_gaussSeq
  set c := wPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 0
  refine ⟨-(c * Real.exp (-(lamb (1 / 20) 1 1 * 5))), fun b ω => ?_, fun b => ⟨?_, ?_⟩, ?_⟩
  · simp only [eqPi, TidyR7OrnsteinUhlenbeck.ouProc_zero TidyR7BrownianExist.bmPath_zero]
    rw [wPi_shift]
    have e : Real.exp (-(lamb (1 / 20) 1 1 * 5)) * Real.exp (lamb (1 / 20) 1 1 * (5 - 0)) = 1 := by
      rw [← Real.exp_add]
      simp
    linear_combination (-c) * e
  · exact isStochEqm_eq TidyR7BrownianExist.isPreBrownianReal_bmPath
      TidyR7BrownianExist.measurable_bmPath TidyR7BrownianExist.continuous_bmPath one_pos
      one_pos _ _ _ _ _
  · exact bddL2_eqPi TidyR7BrownianExist.isPreBrownianReal_bmPath
      TidyR7BrownianExist.measurable_bmPath TidyR7BrownianExist.continuous_bmPath
      TidyR7BrownianExist.bmPath_zero one_pos one_pos _ _ _ _ _
  · intro h
    have := (eqPi_inj TidyR7BrownianExist.isPreBrownianReal_bmPath
      TidyR7BrownianExist.measurable_bmPath TidyR7BrownianExist.continuous_bmPath
      TidyR7BrownianExist.bmPath_zero one_pos one_pos h).2
    norm_num at this

end Cochrane.ZeroBound.TidyR7StochWerningSelect
