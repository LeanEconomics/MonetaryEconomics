/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR7StochWerningNatural

/-!
# Natural-rate shocks: explicit equilibria on a Brownian motion

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.2, pp. 474–475,
equations (20.5)–(20.10), with the natural rate `trapStep u T + ν` and the Ornstein–Uhlenbeck
natural-rate shock `dν = −ην dt + s_ν dW` (`ν = ouProc η 0 0 s_ν W`).

With `d = −κσ/(λ^f + η)` (TidyR7StochWerningNatural.natD), the stable-direction smoothing
`χ_t = e^{−λ^b t}∫_0^t e^{λ^b u}ν_u du` (`chiProc`, an ordinary pathwise integral) and a stable
innovation `ζ^b = ouProc (λ^b) 0 0 b W`, the processes

`π = wPi(π_T) + dχ + ζ^b`, `x = wX(π_T) + (λ^f d/κ)χ + (λ^f/κ)ζ^b − (d/κ)ν` (`natPi`, `natX`)

are regular `L¹`-bounded stochastic equilibria (`isStochEqm_nat`, `regular_natPi`, `bddL1_natPi`,
…). Their innovations are `dπ = b dW` and `dx = ((λ^f b − d s_ν)/κ) dW`: with `b = 0` (no
inflation innovation), a natural-rate shock moves output on impact by
`−d s_ν/κ = σ s_ν/(λ^f + η)`, the deterministic response of (20.10) to news of a natural-rate
path `s_ν e^{−ητ}`. This makes TidyR7StochWerningNatural.unstable_natural non-vacuous
(`natural_nonvacuous`, on bmPath at the book's calibration).

## Main results

* `stronglyMeasurable_integral_adapted`: `∫_0^t k(u)Z_u du` is `𝓕_t`-measurable for an adapted
  continuous `Z` on the Brownian filtration.
* `chiProc_sub`, `regular_chiProc`, `bddL1_chiProc` (`E|χ_t| ≤ K/λ`).
* `expDrift_ou`: `E_t dν = −ην dt` for the OU shock.
* **`isStochEqm_nat`**, `regular_natPi`, `regular_natX`, `bddL1_natPi`, `bddL1_natX`.
* **`natural_nonvacuous`**: on bmPath, with `ρ = 0.05`, `σ = κ = 1`, `T = 5`, `u = −2%`,
  `η = 1/2`, `s_ν = 1/100`, all hypotheses of `unstable_natural` hold, and its conclusion.
-/

namespace Cochrane.ZeroBound.TidyR7StochWerningNaturalExist

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.ContinuousTimeNK Cochrane.ZeroBound.WerningModel
open Cochrane.ZeroBound.TidyR7StochWerning Cochrane.ZeroBound.TidyR7StochWerningTrap
open Cochrane.ZeroBound.TidyR7StochWerningExist Cochrane.ZeroBound.TidyR7StochWerningNatural
open Cochrane.ZeroBound.TidyR7OUPath Cochrane.ZeroBound.TidyR7OrnsteinUhlenbeck
open Cochrane.ZeroBound.TidyR7BrownianTools
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

/-! ## Algebra of regular and `L¹`-bounded processes -/

/-- Cochrane (2023), §20.2.2, p. 474 (tool): sums of regular processes are regular. -/
theorem Regular.add {𝓕 : Filtration ℝ mΩ} {Z₁ Z₂ : ℝ → Ω → ℝ} (h₁ : Regular 𝓕 Z₁)
    (h₂ : Regular 𝓕 Z₂) : Regular 𝓕 (fun t ω => Z₁ t ω + Z₂ t ω) :=
  ⟨fun ω => (h₁.1 ω).add (h₂.1 ω), fun t => (h₁.2 t).add (h₂.2 t)⟩

/-- Cochrane (2023), §20.2.2, p. 474 (tool): multiples of regular processes are regular. -/
theorem Regular.const_mul {𝓕 : Filtration ℝ mΩ} {Z : ℝ → Ω → ℝ} (h : Regular 𝓕 Z) (c : ℝ) :
    Regular 𝓕 (fun t ω => c * Z t ω) :=
  ⟨fun ω => continuous_const.mul (h.1 ω), fun t => stronglyMeasurable_const.mul (h.2 t)⟩

/-- Cochrane (2023), §20.2.2, p. 474 (tool): a continuous deterministic path is regular. -/
theorem regular_det (𝓕 : Filtration ℝ mΩ) {f : ℝ → ℝ} (hf : Continuous f) :
    Regular 𝓕 (fun t _ => f t) :=
  ⟨fun _ => hf, fun _ => stronglyMeasurable_const⟩

/-- Cochrane (2023), §20.2.2, p. 474 (tool): sums of `L¹`-bounded processes are `L¹`-bounded. -/
theorem BddL1.add {Z₁ Z₂ : ℝ → Ω → ℝ} (h₁ : BddL1 P Z₁) (h₂ : BddL1 P Z₂) :
    BddL1 P (fun t ω => Z₁ t ω + Z₂ t ω) := by
  obtain ⟨K₁, hK₁⟩ := h₁
  obtain ⟨K₂, hK₂⟩ := h₂
  refine ⟨K₁ + K₂, fun t ht => ⟨(hK₁ t ht).1.add (hK₂ t ht).1, ?_⟩⟩
  calc ∫ ω, |Z₁ t ω + Z₂ t ω| ∂P ≤ ∫ ω, (|Z₁ t ω| + |Z₂ t ω|) ∂P :=
        integral_mono ((hK₁ t ht).1.add (hK₂ t ht).1).abs ((hK₁ t ht).1.abs.add (hK₂ t ht).1.abs)
          fun ω => abs_add_le _ _
    _ = ∫ ω, |Z₁ t ω| ∂P + ∫ ω, |Z₂ t ω| ∂P := integral_add (hK₁ t ht).1.abs (hK₂ t ht).1.abs
    _ ≤ K₁ + K₂ := add_le_add (hK₁ t ht).2 (hK₂ t ht).2

/-- Cochrane (2023), §20.2.2, p. 474 (tool): multiples of `L¹`-bounded processes are
`L¹`-bounded. -/
theorem BddL1.const_mul {Z : ℝ → Ω → ℝ} (h : BddL1 P Z) (c : ℝ) :
    BddL1 P (fun t ω => c * Z t ω) := by
  obtain ⟨K, hK⟩ := h
  refine ⟨|c| * K, fun t ht => ⟨(hK t ht).1.const_mul c, ?_⟩⟩
  simp only [abs_mul]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hK t ht).2 (abs_nonneg c)

/-- Cochrane (2023), §20.2.2, p. 474 (tool): a bounded deterministic path is `L¹`-bounded. -/
theorem bddL1_det [IsProbabilityMeasure P] {f : ℝ → ℝ} (hf : BddOnIci f) :
    BddL1 P (fun t _ => f t) := by
  obtain ⟨K, hK⟩ := hf
  exact ⟨K, fun t ht => ⟨integrable_const _, by simpa using hK t ht⟩⟩

/-! ## Pathwise integrals of adapted processes -/

/-- Cochrane (2023), §20.2.2, p. 474 (tool): for an adapted process `Z` with continuous paths on
the Brownian filtration and continuous `k`, `∫_0^t k(u) Z_u du` is `𝓕_t`-measurable. -/
theorem stronglyMeasurable_integral_adapted (hW : ∀ t, Measurable (W t)) {Z : ℝ → Ω → ℝ}
    (hZ : Regular (bmFiltrationReal W hW) Z) {k : ℝ → ℝ} (hk : Continuous k) (t : ℝ) :
    StronglyMeasurable[bmFiltrationReal W hW t] fun ω => ∫ u in (0 : ℝ)..t, k u * Z u ω := by
  set m := (bmFiltrationReal W hW) t
  let F : ℝ → Ω → ℝ := fun u ω => k u * Z (min u (max t 0)) ω
  have hle : ∀ u, (min u (max t 0)).toNNReal ≤ t.toNNReal := fun u => by
    rcases le_total 0 t with h | h
    · exact Real.toNNReal_le_toNNReal ((min_le_right _ _).trans (max_eq_left h).le)
    · have h1 : min u (max t 0) ≤ 0 := (min_le_right _ _).trans (max_eq_right h).le
      rw [Real.toNNReal_of_nonpos h1]
      exact bot_le
  have hFm : ∀ u, Measurable[m] (F u) := fun u =>
    (stronglyMeasurable_const.mul ((hZ.2 (min u (max t 0))).mono
      ((bmFiltration W hW).mono (hle u)))).measurable
  have hFc : ∀ ω, Continuous fun u => F u ω := fun ω =>
    hk.mul ((hZ.1 ω).comp (continuous_id.min continuous_const))
  have hF := (measurable_uncurry_of_continuous_of_measurable (m := m) hFc hFm).stronglyMeasurable
  have h1 := @StronglyMeasurable.integral_prod_left ℝ Ω ℝ _ m (volume.restrict (Set.Ioc 0 t))
    _ _ _ F hF
  have h2 := @StronglyMeasurable.integral_prod_left ℝ Ω ℝ _ m (volume.restrict (Set.Ioc t 0))
    _ _ _ F hF
  have hG : StronglyMeasurable[m] fun ω => ∫ u in (0 : ℝ)..t, F u ω := by
    simp only [intervalIntegral]
    exact h1.sub h2
  have heq : (fun ω => ∫ u in (0 : ℝ)..t, k u * Z u ω) = fun ω => ∫ u in (0 : ℝ)..t, F u ω := by
    funext ω
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hu2 : u ≤ max t 0 := by
      have := hu.2
      rw [max_comm]
      exact this
    simp only [F, min_eq_left hu2]
  rw [heq]
  exact hG

/-- Cochrane (2023), §20.2.2, p. 475: the stable-direction smoothing of a process `Z`,
`χ_t = e^{−λt}∫_0^t e^{λu}Z_u du`, the solution of `dχ = (−λχ + Z)dt`, `χ_0 = 0`. -/
noncomputable def chiProc (lam : ℝ) (Z : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-lam * t) * ouPrim lam (fun u => Z u ω) t

/-- Cochrane (2023), §20.2.2, p. 475: `χ' = −λχ + Z` path by path. -/
theorem hasDerivAt_chiProc {Z : ℝ → Ω → ℝ} (hZ : ∀ ω, Continuous fun t => Z t ω) (lam : ℝ)
    (ω : Ω) (t : ℝ) :
    HasDerivAt (fun t => chiProc lam Z t ω) (-lam * chiProc lam Z t ω + Z t ω) t := by
  have h1 : HasDerivAt (fun t => Real.exp (-lam * t)) (Real.exp (-lam * t) * -lam) t := by
    simpa using ((hasDerivAt_id' t).const_mul (-lam)).exp
  refine (h1.mul (hasDerivAt_ouPrim lam (hZ ω) t)).congr_deriv ?_
  have he : Real.exp (-lam * t) * Real.exp (lam * t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  simp only [chiProc]
  linear_combination (Z t ω) * he

/-- Cochrane (2023), §20.2.2, p. 475: **increments of `χ`**, path by path:
`χ_t − χ_s = ∫_s^t (−λχ_r + Z_r) dr`. -/
theorem chiProc_sub {Z : ℝ → Ω → ℝ} (hZ : ∀ ω, Continuous fun t => Z t ω) (lam : ℝ) (ω : Ω)
    (s t : ℝ) :
    chiProc lam Z t ω - chiProc lam Z s ω = ∫ r in s..t, (-lam * chiProc lam Z r ω + Z r ω) := by
  have hc : Continuous fun r => chiProc lam Z r ω :=
    continuous_iff_continuousAt.2 fun r => (hasDerivAt_chiProc hZ lam ω r).continuousAt
  have hi : IntervalIntegrable (fun r => -lam * chiProc lam Z r ω + Z r ω) volume s t :=
    ((continuous_const.mul hc).add (hZ ω)).intervalIntegrable s t
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => hasDerivAt_chiProc hZ lam ω r) hi).symm

/-- Cochrane (2023), §20.2.2, p. 475: `χ` of a regular process on the Brownian filtration is
regular. -/
theorem regular_chiProc (hW : ∀ t, Measurable (W t)) {Z : ℝ → Ω → ℝ}
    (hZ : Regular (bmFiltrationReal W hW) Z) (lam : ℝ) :
    Regular (bmFiltrationReal W hW) (chiProc lam Z) :=
  ⟨fun ω => continuous_iff_continuousAt.2 fun r => (hasDerivAt_chiProc hZ.1 lam ω r).continuousAt,
    fun t => stronglyMeasurable_const.mul
      (stronglyMeasurable_integral_adapted hW hZ (k := fun u => Real.exp (lam * u))
        (by fun_prop) t)⟩

/-- Cochrane (2023), §20.2.2, p. 475: `∫_0^t e^{−λ(t−u)} du = (1 − e^{−λt})/λ ≤ 1/λ` for
`λ > 0`.
Restates `ExpIntegrals.intervalIntegral_exp_neg_mul` after substitution. -/
theorem integral_exp_decay_le {lam : ℝ} (hlam : 0 < lam) (t : ℝ) :
    ∫ u in (0 : ℝ)..t, Real.exp (-(lam * (t - u))) ≤ 1 / lam := by
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) t, HasDerivAt (fun u => Real.exp (lam * u - lam * t) / lam)
      (Real.exp (-(lam * (t - x)))) x := fun x _ => by
    have := (((hasDerivAt_id' x).const_mul lam).sub_const (lam * t)).exp.div_const lam
    refine this.congr_deriv ?_
    field_simp
    congr 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun u => Real.exp (-(lam * (t - u)))).intervalIntegrable 0 t)]
  simp only [sub_self, Real.exp_zero, mul_zero, zero_sub]
  have : 0 < Real.exp (-(lam * t)) / lam := div_pos (Real.exp_pos _) hlam
  linarith

/-- Cochrane (2023), §20.2.2, p. 475: **`χ` of an `L¹`-bounded process is `L¹`-bounded**:
`E|χ_t| ≤ K/λ` for `λ > 0`. -/
theorem bddL1_chiProc [IsProbabilityMeasure P] (hW : ∀ t, Measurable (W t)) {Z : ℝ → Ω → ℝ}
    (hZ : Regular (bmFiltrationReal W hW) Z) (hZb : BddL1 P Z) {lam : ℝ} (hlam : 0 < lam) :
    BddL1 P (chiProc lam Z) := by
  obtain ⟨K, hK⟩ := hZb
  have hK0 : 0 ≤ K := (integral_nonneg fun _ => abs_nonneg _).trans (hK 0 le_rfl).2
  have hm : ∀ t, Measurable (Z t) := fun t =>
    ((hZ.2 t).mono ((bmFiltrationReal W hW).le t)).measurable
  refine ⟨K / lam, fun t ht => ?_⟩
  -- the dominating function `G ω = ∫_0^t e^{−λ(t−u)}|Z_u ω| du`
  set μ := volume.restrict (Set.Ioc (0 : ℝ) t)
  set H : ℝ → Ω → ℝ := fun u ω => Real.exp (-(lam * (t - u))) * |Z u ω|
  have hHi : Integrable (Function.uncurry H) (μ.prod P) := by
    have hZp := (integrable_prod_proc (P := P) hZ.1 hm hK le_rfl (b := t)).norm
    have hb : ∀ᵐ p ∂(μ.prod P), ‖Real.exp (-(lam * (t - p.1)))‖ ≤ 1 :=
      Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst
        (p := fun u => ‖Real.exp (-(lam * (t - u)))‖ ≤ 1)
        (ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
          nlinarith [hu.2])
    refine (hZp.bdd_mul (((by fun_prop : Continuous fun u : ℝ =>
      Real.exp (-(lam * (t - u)))).measurable.comp measurable_fst).aestronglyMeasurable) hb).congr
        (Eventually.of_forall fun p => ?_)
    simp [H, Function.uncurry, Real.norm_eq_abs]
  have hGi : Integrable (fun ω => ∫ u, H u ω ∂μ) P := hHi.integral_prod_right
  have hbd : ∀ ω, |chiProc lam Z t ω| ≤ ∫ u, H u ω ∂μ := fun ω => by
    have h1 := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
      (f := fun u => Real.exp (lam * u) * Z u ω) ht
    simp only [chiProc, ouPrim, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-lam * t) * |∫ u in (0 : ℝ)..t, Real.exp (lam * u) * Z u ω|
        ≤ Real.exp (-lam * t) * ∫ u in (0 : ℝ)..t, |Real.exp (lam * u) * Z u ω| :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = ∫ u in (0 : ℝ)..t, H u ω := by
          rw [← intervalIntegral.integral_const_mul]
          refine intervalIntegral.integral_congr fun u _ => ?_
          simp only [H, abs_mul, abs_of_pos (Real.exp_pos _)]
          rw [← mul_assoc, ← Real.exp_add]
          ring_nf
      _ = ∫ u, H u ω ∂μ := intervalIntegral.integral_of_le ht
  have hχm : AEStronglyMeasurable (chiProc lam Z t) P :=
    ((regular_chiProc hW hZ lam).2 t).mono ((bmFiltrationReal W hW).le t) |>.aestronglyMeasurable
  have hχi : Integrable (chiProc lam Z t) P :=
    hGi.mono' hχm (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hbd ω)
  refine ⟨hχi, ?_⟩
  have hswap := integral_integral_swap hHi
  have hin : ∀ u, ∫ ω, H u ω ∂P = Real.exp (-(lam * (t - u))) * ∫ ω, |Z u ω| ∂P := fun u =>
    integral_const_mul _ _
  calc ∫ ω, |chiProc lam Z t ω| ∂P ≤ ∫ ω, ∫ u, H u ω ∂μ ∂P :=
        integral_mono hχi.abs hGi hbd
    _ = ∫ u, ∫ ω, H u ω ∂P ∂μ := hswap.symm
    _ = ∫ u in Set.Ioc 0 t, Real.exp (-(lam * (t - u))) * ∫ ω, |Z u ω| ∂P :=
        integral_congr_ae (Eventually.of_forall fun u => hin u)
    _ ≤ ∫ u in Set.Ioc 0 t, Real.exp (-(lam * (t - u))) * K := by
        refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun u hu => ?_
        · exact hHi.integral_prod_left.congr (Eventually.of_forall fun u => hin u)
        · exact (by fun_prop : Continuous fun u => Real.exp (-(lam * (t - u))) * K).integrableOn_Ioc
        · exact mul_le_mul_of_nonneg_left (hK u hu.1.le).2 (Real.exp_pos _).le
    _ = K * ∫ u in (0 : ℝ)..t, Real.exp (-(lam * (t - u))) := by
        rw [intervalIntegral.integral_of_le ht, integral_mul_const, mul_comm]
    _ ≤ K * (1 / lam) := mul_le_mul_of_nonneg_left (integral_exp_decay_le hlam t) hK0
    _ = K / lam := by ring

/-! ## The OU natural-rate shock -/

/-- Cochrane (2023), §20.2.2, p. 474: the OU natural-rate shock `dν = −ην dt + s dW` satisfies
`E_t dν = −ην dt`. -/
theorem expDrift_ou [IsProbabilityMeasure P] (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω) (η sν : ℝ) :
    ExpDrift P (bmFiltrationReal W hW) (ouProc η 0 0 sν W)
      (fun r ω => -(η * ouProc η 0 0 sν W r ω)) :=
  expDrift_of_bm hB hW sν fun s t _ _ ω => by
    have := ouProc_sub hcont η 0 0 sν ω s t
    simp only [sub_zero] at this
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
    linarith

/-- Cochrane (2023), §20.2.2, p. 474: the OU natural-rate shock is `L¹`-bounded (`η > 0`). -/
theorem bddL1_ou [IsProbabilityMeasure P] (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {η : ℝ} (hη : 0 < η) (sν : ℝ) : BddL1 P (ouProc η 0 0 sν W) :=
  BddL2.bddL1 ⟨sν ^ 2 / (2 * η), fun _ ht => ouProc_sq_le hB hW hcont hW0 hη sν ht⟩

/-! ## The explicit equilibria -/

/-- Cochrane (2023), §20.2.2, p. 475, with natural-rate shocks: inflation
`π = wPi(π_T) + dχ + ζ^b`, `χ = chiProc λ^b ν`. -/
noncomputable def natPi (σ κ ρ η sν T u g πT b : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  wPi σ κ ρ T u g πT t + natD σ κ ρ η * chiProc (lamb ρ κ σ) (ouProc η 0 0 sν W) t ω +
    ouProc (lamb ρ κ σ) 0 0 b W t ω

/-- Cochrane (2023), (20.10), p. 475, with natural-rate shocks: output
`x = wX(π_T) + (λ^f d/κ)χ + (λ^f/κ)ζ^b − (d/κ)ν`. -/
noncomputable def natX (σ κ ρ η sν T u g πT b : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  wX σ κ ρ T u g πT t +
    lamf ρ κ σ * natD σ κ ρ η / κ * chiProc (lamb ρ κ σ) (ouProc η 0 0 sν W) t ω +
    lamf ρ κ σ / κ * ouProc (lamb ρ κ σ) 0 0 b W t ω +
    -(natD σ κ ρ η / κ) * ouProc η 0 0 sν W t ω

/-- **Cochrane (2023), (20.5)–(20.6), p. 474, with natural-rate shocks: every `(π_T, b)` gives a
stochastic equilibrium** with zero interest rate and natural rate `trapStep u T + ν`, with
innovations `dπ = b dW` and `dx = ((λ^f b − d s_ν)/κ) dW`. -/
theorem isStochEqm_nat [IsProbabilityMeasure P] (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω) {σ ρ κ η : ℝ}
    (hσ : 0 < σ) (hκ : 0 < κ) (hη : 0 ≤ η) (sν T u g πT b : ℝ) :
    IsStochEqm σ ρ κ P (bmFiltrationReal W hW) (fun _ => 0) (trapStep u T) (trapStep g T)
      (ouProc η 0 0 sν W) (natX σ κ ρ η sν T u g πT b W) (natPi σ κ ρ η sν T u g πT b W) := by
  have hsub := lamf_sub_lamb ρ κ σ
  have hκ0 := hκ.ne'
  have hc : lamf ρ κ σ / κ * lamb ρ κ σ = σ := by
    have := lamf_mul_lamb (ρ := ρ) hκ hσ
    field_simp
    linarith
  have hdd : natD σ κ ρ η * lamf ρ κ σ / κ + natD σ κ ρ η * η / κ = -σ := by
    have := natD_eq (ρ := ρ) hσ hκ hη
    field_simp
    linarith
  have hνc : ∀ ω, Continuous fun r => ouProc η 0 0 sν W r ω := fun ω =>
    continuous_ouPath η 0 0 sν (continuous_bmReal (hcont ω))
  have hzc : ∀ ω, Continuous fun r => ouProc (lamb ρ κ σ) 0 0 b W r ω := fun ω =>
    continuous_ouPath (lamb ρ κ σ) 0 0 b (continuous_bmReal (hcont ω))
  have hχc : ∀ ω, Continuous fun r => chiProc (lamb ρ κ σ) (ouProc η 0 0 sν W) r ω :=
    fun ω => continuous_iff_continuousAt.2 fun r =>
      (hasDerivAt_chiProc hνc (lamb ρ κ σ) ω r).continuousAt
  have hWc := wPi_continuous σ κ ρ T u g πT hκ hσ
  have hXc := wX_continuous σ κ ρ T u g πT hκ hσ
  refine ⟨expDrift_of_bm hB hW ((lamf ρ κ σ * b - natD σ κ ρ η * sν) / κ)
      fun s t hs hst ω => ?_, expDrift_of_bm hB hW b fun s t hs hst ω => ?_⟩
  · -- the IS curve
    obtain ⟨d1, -⟩ := wPath_intForm (ρ := ρ) hκ hσ T u g πT hs hst
    have hz := ouProc_sub hcont (lamb ρ κ σ) 0 0 b ω s t
    have hν := ouProc_sub hcont η 0 0 sν ω s t
    have hχ := chiProc_sub hνc (lamb ρ κ σ) ω s t
    simp only [sub_zero] at hz hν
    have iχ : IntervalIntegrable (fun r => chiProc (lamb ρ κ σ) (ouProc η 0 0 sν W) r ω)
        volume s t := (hχc ω).intervalIntegrable s t
    have iν : IntervalIntegrable (fun r => ouProc η 0 0 sν W r ω) volume s t :=
      (hνc ω).intervalIntegrable s t
    have iz : IntervalIntegrable (fun r => ouProc (lamb ρ κ σ) 0 0 b W r ω) volume s t :=
      (hzc ω).intervalIntegrable s t
    have hχ' : chiProc (lamb ρ κ σ) (ouProc η 0 0 sν W) t ω -
        chiProc (lamb ρ κ σ) (ouProc η 0 0 sν W) s ω =
        -lamb ρ κ σ * (∫ r in s..t, chiProc (lamb ρ κ σ) (ouProc η 0 0 sν W) r ω) +
          ∫ r in s..t, ouProc η 0 0 sν W r ω := by
      rw [hχ, intervalIntegral.integral_add (iχ.const_mul _) iν,
        intervalIntegral.integral_const_mul]
    have i0 : IntervalIntegrable (fun r => σ * (0 - wPi σ κ ρ T u g πT r - trapStep u T r))
        volume s t := ((intervalIntegrable_const.sub (hWc.intervalIntegrable s t)).sub
          (trapStep_intervalIntegrable u T s t)).const_mul σ
    have i1 : IntervalIntegrable (fun r => σ * (0 - wPi σ κ ρ T u g πT r - trapStep u T r) +
        -σ * natD σ κ ρ η * chiProc (lamb ρ κ σ) (ouProc η 0 0 sν W) r ω) volume s t :=
      i0.add (iχ.const_mul _)
    have i2 : IntervalIntegrable (fun r => σ * (0 - wPi σ κ ρ T u g πT r - trapStep u T r) +
        -σ * natD σ κ ρ η * chiProc (lamb ρ κ σ) (ouProc η 0 0 sν W) r ω +
        -σ * ouProc (lamb ρ κ σ) 0 0 b W r ω) volume s t := i1.add (iz.const_mul _)
    have e : (∫ r in s..t, σ * (0 - natPi σ κ ρ η sν T u g πT b W r ω -
        (trapStep u T r + ouProc η 0 0 sν W r ω))) =
        (∫ r in s..t, σ * (0 - wPi σ κ ρ T u g πT r - trapStep u T r)) +
          -σ * natD σ κ ρ η * (∫ r in s..t, chiProc (lamb ρ κ σ) (ouProc η 0 0 sν W) r ω) +
          -σ * (∫ r in s..t, ouProc (lamb ρ κ σ) 0 0 b W r ω) +
          -σ * ∫ r in s..t, ouProc η 0 0 sν W r ω := by
      rw [← intervalIntegral.integral_const_mul (-σ * natD σ κ ρ η),
        ← intervalIntegral.integral_const_mul (-σ) (fun r => ouProc (lamb ρ κ σ) 0 0 b W r ω),
        ← intervalIntegral.integral_const_mul (-σ) (fun r => ouProc η 0 0 sν W r ω),
        ← intervalIntegral.integral_add i0 (iχ.const_mul _),
        ← intervalIntegral.integral_add i1 (iz.const_mul _),
        ← intervalIntegral.integral_add i2 (iν.const_mul _)]
      refine intervalIntegral.integral_congr fun r _ => ?_
      simp only [natPi]
      ring
    simp only [natX]
    rw [e, ← d1]
    linear_combination (lamf ρ κ σ * natD σ κ ρ η / κ) * hχ' + (lamf ρ κ σ / κ) * hz -
      (natD σ κ ρ η / κ) * hν -
      (natD σ κ ρ η * ∫ r in s..t, chiProc (lamb ρ κ σ) (ouProc η 0 0 sν W) r ω) * hc -
      (∫ r in s..t, ouProc (lamb ρ κ σ) 0 0 b W r ω) * hc +
      (∫ r in s..t, ouProc η 0 0 sν W r ω) * hdd
  · -- the Phillips curve
    obtain ⟨-, d2⟩ := wPath_intForm (ρ := ρ) hκ hσ T u g πT hs hst
    have hz := ouProc_sub hcont (lamb ρ κ σ) 0 0 b ω s t
    have hχ := chiProc_sub hνc (lamb ρ κ σ) ω s t
    simp only [sub_zero] at hz
    have iχ : IntervalIntegrable (fun r => chiProc (lamb ρ κ σ) (ouProc η 0 0 sν W) r ω)
        volume s t := (hχc ω).intervalIntegrable s t
    have iν : IntervalIntegrable (fun r => ouProc η 0 0 sν W r ω) volume s t :=
      (hνc ω).intervalIntegrable s t
    have iz : IntervalIntegrable (fun r => ouProc (lamb ρ κ σ) 0 0 b W r ω) volume s t :=
      (hzc ω).intervalIntegrable s t
    have hχ' : chiProc (lamb ρ κ σ) (ouProc η 0 0 sν W) t ω -
        chiProc (lamb ρ κ σ) (ouProc η 0 0 sν W) s ω =
        -lamb ρ κ σ * (∫ r in s..t, chiProc (lamb ρ κ σ) (ouProc η 0 0 sν W) r ω) +
          ∫ r in s..t, ouProc η 0 0 sν W r ω := by
      rw [hχ, intervalIntegral.integral_add (iχ.const_mul _) iν,
        intervalIntegral.integral_const_mul]
    have i0 : IntervalIntegrable (fun r => ρ * wPi σ κ ρ T u g πT r -
        κ * (wX σ κ ρ T u g πT r + trapStep g T r)) volume s t :=
      ((hWc.intervalIntegrable s t).const_mul ρ).sub (((hXc.intervalIntegrable s t).add
        (trapStep_intervalIntegrable g T s t)).const_mul κ)
    have i1 : IntervalIntegrable (fun r => ρ * wPi σ κ ρ T u g πT r -
        κ * (wX σ κ ρ T u g πT r + trapStep g T r) +
        (ρ - lamf ρ κ σ) * natD σ κ ρ η * chiProc (lamb ρ κ σ) (ouProc η 0 0 sν W) r ω)
        volume s t := i0.add (iχ.const_mul _)
    have i2 : IntervalIntegrable (fun r => ρ * wPi σ κ ρ T u g πT r -
        κ * (wX σ κ ρ T u g πT r + trapStep g T r) +
        (ρ - lamf ρ κ σ) * natD σ κ ρ η * chiProc (lamb ρ κ σ) (ouProc η 0 0 sν W) r ω +
        (ρ - lamf ρ κ σ) * ouProc (lamb ρ κ σ) 0 0 b W r ω) volume s t :=
      i1.add (iz.const_mul _)
    have e : (∫ r in s..t, (ρ * natPi σ κ ρ η sν T u g πT b W r ω -
        κ * (natX σ κ ρ η sν T u g πT b W r ω + trapStep g T r))) =
        (∫ r in s..t, (ρ * wPi σ κ ρ T u g πT r - κ * (wX σ κ ρ T u g πT r + trapStep g T r))) +
          (ρ - lamf ρ κ σ) * natD σ κ ρ η *
            (∫ r in s..t, chiProc (lamb ρ κ σ) (ouProc η 0 0 sν W) r ω) +
          (ρ - lamf ρ κ σ) * (∫ r in s..t, ouProc (lamb ρ κ σ) 0 0 b W r ω) +
          natD σ κ ρ η * ∫ r in s..t, ouProc η 0 0 sν W r ω := by
      rw [← intervalIntegral.integral_const_mul ((ρ - lamf ρ κ σ) * natD σ κ ρ η),
        ← intervalIntegral.integral_const_mul (ρ - lamf ρ κ σ)
          (fun r => ouProc (lamb ρ κ σ) 0 0 b W r ω),
        ← intervalIntegral.integral_const_mul (natD σ κ ρ η)
          (fun r => ouProc η 0 0 sν W r ω),
        ← intervalIntegral.integral_add i0 (iχ.const_mul _),
        ← intervalIntegral.integral_add i1 (iz.const_mul _),
        ← intervalIntegral.integral_add i2 (iν.const_mul _)]
      refine intervalIntegral.integral_congr fun r _ => ?_
      simp only [natPi, natX]
      field_simp
      ring
    rw [e]
    simp only [natPi]
    rw [← d2]
    linear_combination natD σ κ ρ η * hχ' + hz +
      (natD σ κ ρ η * (∫ r in s..t, chiProc (lamb ρ κ σ) (ouProc η 0 0 sν W) r ω) +
        ∫ r in s..t, ouProc (lamb ρ κ σ) 0 0 b W r ω) * hsub

/-- Cochrane (2023), §20.2.2, p. 474: the inflation process with natural-rate shocks is
regular. -/
theorem regular_natPi (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω)
    {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (η sν T u g πT b : ℝ) :
    Regular (bmFiltrationReal W hW) (natPi σ κ ρ η sν T u g πT b W) :=
  Regular.add (Regular.add (regular_det _ (wPi_continuous σ κ ρ T u g πT hκ hσ))
    (Regular.const_mul (regular_chiProc hW (regular_ouProc hW hcont η 0 0 sν) (lamb ρ κ σ)) _))
    (regular_ouProc hW hcont (lamb ρ κ σ) 0 0 b)

/-- Cochrane (2023), (20.10), p. 475: the output process with natural-rate shocks is
regular. -/
theorem regular_natX (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω)
    {σ ρ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (η sν T u g πT b : ℝ) :
    Regular (bmFiltrationReal W hW) (natX σ κ ρ η sν T u g πT b W) :=
  Regular.add (Regular.add (Regular.add (regular_det _ (wX_continuous σ κ ρ T u g πT hκ hσ))
    (Regular.const_mul (regular_chiProc hW (regular_ouProc hW hcont η 0 0 sν) (lamb ρ κ σ)) _))
    (Regular.const_mul (regular_ouProc hW hcont (lamb ρ κ σ) 0 0 b) _))
    (Regular.const_mul (regular_ouProc hW hcont η 0 0 sν) _)

/-- Cochrane (2023), §20.2.2, p. 474: the inflation process with natural-rate shocks is
`L¹`-bounded (`η > 0`). -/
theorem bddL1_natPi [IsProbabilityMeasure P] (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {σ ρ κ η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hη : 0 < η)
    (sν T u g πT b : ℝ) : BddL1 P (natPi σ κ ρ η sν T u g πT b W) := by
  have hlb := lamb_pos (ρ := ρ) hκ hσ
  exact BddL1.add (BddL1.add (bddL1_det (wPath_bdd (ρ := ρ) hκ hσ T u g πT).2)
    (BddL1.const_mul (bddL1_chiProc hW (regular_ouProc hW hcont η 0 0 sν)
      (bddL1_ou hB hW hcont hW0 hη sν) hlb) _)) (bddL1_ou hB hW hcont hW0 hlb b)

/-- Cochrane (2023), (20.10), p. 475: the output process with natural-rate shocks is
`L¹`-bounded (`η > 0`). -/
theorem bddL1_natX [IsProbabilityMeasure P] (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {σ ρ κ η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hη : 0 < η)
    (sν T u g πT b : ℝ) : BddL1 P (natX σ κ ρ η sν T u g πT b W) := by
  have hlb := lamb_pos (ρ := ρ) hκ hσ
  exact BddL1.add (BddL1.add (BddL1.add (bddL1_det (wPath_bdd (ρ := ρ) hκ hσ T u g πT).1)
    (BddL1.const_mul (bddL1_chiProc hW (regular_ouProc hW hcont η 0 0 sν)
      (bddL1_ou hB hW hcont hW0 hη sν) hlb) _))
    (BddL1.const_mul (bddL1_ou hB hW hcont hW0 hlb b) _))
    (BddL1.const_mul (bddL1_ou hB hW hcont hW0 hη sν) _)

/-! ## Non-vacuity on the constructed Brownian motion -/

open Cochrane.ZeroBound.TidyR7BrownianExist Cochrane.ZeroBound.TidyR7BrownianSchauder

/-- Cochrane (2023), §20.2.2, pp. 474–475 (non-vacuity of `unstable_natural`): on bmPath at the
book's calibration (`ρ = 0.05`, `σ = κ = 1`, `T = 5`, `u = −2%`, `g = 0`) with an OU
natural-rate shock (`η = 1/2`, `s_ν = 1/100`), the shock is genuinely random (it exceeds `0`
with positive probability at date `1`), the process `(natX, natPi)` with `π_T = 0`, `b = 0`
satisfies every hypothesis of `unstable_natural`, and hence its conclusion. -/
theorem natural_nonvacuous :
    0 < gaussSeq {ω | 0 < ouProc (1 / 2) 0 0 (1 / 100) bmPath 1 ω} ∧
    IsStochEqm 1 (1 / 20) 1 gaussSeq (bmFiltrationReal bmPath measurable_bmPath) (fun _ => 0)
        (trapStep (-2 / 100) 5) (trapStep 0 5) (ouProc (1 / 2) 0 0 (1 / 100) bmPath)
        (natX 1 1 (1 / 20) (1 / 2) (1 / 100) 5 (-2 / 100) 0 0 0 bmPath)
        (natPi 1 1 (1 / 20) (1 / 2) (1 / 100) 5 (-2 / 100) 0 0 0 bmPath) ∧
      Regular (bmFiltrationReal bmPath measurable_bmPath)
        (natPi 1 1 (1 / 20) (1 / 2) (1 / 100) 5 (-2 / 100) 0 0 0 bmPath) ∧
      BddL1 gaussSeq (natPi 1 1 (1 / 20) (1 / 2) (1 / 100) 5 (-2 / 100) 0 0 0 bmPath) ∧
      BddL1 gaussSeq (natX 1 1 (1 / 20) (1 / 2) (1 / 100) 5 (-2 / 100) 0 0 0 bmPath) ∧
      ∀ s, 0 ≤ s → (fun ω => lamf (1 / 20) 1 1 *
          natPi 1 1 (1 / 20) (1 / 2) (1 / 100) 5 (-2 / 100) 0 0 0 bmPath s ω -
          1 * natX 1 1 (1 / 20) (1 / 2) (1 / 100) 5 (-2 / 100) 0 0 0 bmPath s ω) =ᵐ[gaussSeq]
        fun ω => (lamf (1 / 20) 1 1 * wPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 s -
          1 * wX 1 1 (1 / 20) 5 (-2 / 100) 0 0 s) +
          natD 1 1 (1 / 20) (1 / 2) * ouProc (1 / 2) 0 0 (1 / 100) bmPath s ω := by
  have := isProbabilityMeasure_gaussSeq
  have hB := isPreBrownianReal_bmPath
  have hη : (0 : ℝ) < 1 / 2 := by norm_num
  have heq := isStochEqm_nat (P := gaussSeq) hB measurable_bmPath continuous_bmPath one_pos
    one_pos hη.le (1 / 100) 5 (-2 / 100) 0 0 0 (ρ := 1 / 20)
  have rπ := regular_natPi measurable_bmPath continuous_bmPath one_pos one_pos (ρ := 1 / 20)
    (1 / 2) (1 / 100) 5 (-2 / 100) 0 0 0
  have bπ := bddL1_natPi (P := gaussSeq) hB measurable_bmPath continuous_bmPath bmPath_zero
    one_pos one_pos hη (ρ := 1 / 20) (1 / 100) 5 (-2 / 100) 0 0 0
  have bx := bddL1_natX (P := gaussSeq) hB measurable_bmPath continuous_bmPath bmPath_zero
    one_pos one_pos hη (ρ := 1 / 20) (1 / 100) 5 (-2 / 100) 0 0 0
  refine ⟨ouProc_gt_pos hB measurable_bmPath continuous_bmPath bmPath_zero hη (by norm_num) 0 0
      one_pos 0, heq, rπ, bπ, bx, fun s hs => ?_⟩
  exact unstable_natural one_pos one_pos hη.le (regular_ouProc measurable_bmPath continuous_bmPath
      (1 / 2) 0 0 (1 / 100)) (bddL1_ou hB measurable_bmPath continuous_bmPath bmPath_zero hη _)
    (expDrift_ou hB measurable_bmPath continuous_bmPath _ _)
    (regular_natX measurable_bmPath continuous_bmPath one_pos one_pos _ _ _ _ _ _ _)
    bx rπ bπ heq hs

end Cochrane.ZeroBound.TidyR7StochWerningNaturalExist
