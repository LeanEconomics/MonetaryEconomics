/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR7StochWerningNaturalExist

/-!
# Natural-rate shocks: conditional expectations and mean-square bounds

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.2, pp. 474–475,
equations (20.5)–(20.10), §20.2.4, p. 479 (news), with the natural rate `trapStep u T + ν` and a
mean-reverting shock `E_t dν = −ην dt`; the interest rate is zero throughout (the model of
TidyR7StochWerningNatural; the variant in which the rate tracks the natural rate after the trap
is TidyR8StochWerningNaturalTrack).

TidyR7StochWerningNatural pins the unstable combination `λ^f π − κx` state by state. Here we
characterise the conditional expectations themselves, in every regular `L¹`-bounded
equilibrium, on any filtration:

* `condExp_nu`: `E_s ν_t = e^{−η(t−s)} ν_s`;
* **`condExp_pi_nat`**: `E_s π_t = wPi(0)_t + e^{−λ^b(t−s)}(π_s − wPi(0)_s) + d k(t − s) ν_s`,
  with `d = −κσ/(λ^f + η)` and `k(τ) = ∫_0^τ e^{−λ^b(τ−v)} e^{−ηv} dv` (`natK`): the news `ν_s`
  moves expected inflation along the deterministic response to a natural-rate path
  `ν_s e^{−ητ}`; the free part `π_s − wPi(0)_s` decays at `λ^b` as without shocks;
* **`condExp_x_nat`**: `E_s x_t = wX(0)_t + (λ^f/κ)(E_sπ_t − wPi(0)_t) − (d/κ)e^{−η(t−s)}ν_s`.

On a Brownian motion the explicit equilibria of TidyR7StochWerningNaturalExist are **bounded in
mean square** (`bddL2_natPi`, `bddL2_natX`), not only in `L¹`: the pathwise smoothing
`χ = chiProc λ ν` satisfies `χ_t² ≤ chiProc λ (ν²)_t / λ` (Cauchy–Schwarz, `sq_chiProc_le`).
Non-vacuity on bmPath at the book's calibration: `bmPath_condExp_pi_nat`.
-/

namespace Cochrane.ZeroBound.TidyR8StochWerningNaturalMean

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.ContinuousTimeNK Cochrane.ZeroBound.WerningModel
open Cochrane.ZeroBound.TidyR7StochWerning Cochrane.ZeroBound.TidyR7StochWerningTrap
open Cochrane.ZeroBound.TidyR7StochWerningExist Cochrane.ZeroBound.TidyR7StochWerningNatural
open Cochrane.ZeroBound.TidyR7StochWerningNaturalExist
open Cochrane.ZeroBound.TidyR7OUPath Cochrane.ZeroBound.TidyR7OrnsteinUhlenbeck
open Cochrane.ZeroBound.TidyR7BrownianTools
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ## Conditional means as deterministic functions of time -/

/-- Cochrane (2023), §20.2.2, p. 474 (tool): the conditional mean `r ↦ ∫_A Z_r` of a process with
continuous paths, measurable sections and bounded first moments is integrable on every
`[s, b]`, `s ≥ 0`. -/
theorem integrableOn_setIntegral [IsFiniteMeasure P] {Z : ℝ → Ω → ℝ}
    (hc : ∀ ω, Continuous fun t => Z t ω) (hm : ∀ t, Measurable (Z t)) {K : ℝ}
    (hK : ∀ t, 0 ≤ t → Integrable (Z t) P ∧ ∫ ω, |Z t ω| ∂P ≤ K) (A : Set Ω) {s : ℝ}
    (hs : 0 ≤ s) (b : ℝ) : IntegrableOn (fun r => ∫ ω in A, Z r ω ∂P) (Set.Icc s b) :=
  Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
    (stronglyMeasurable_setIntegral hc hm A).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Icc fun r hr => by
      rw [Real.norm_eq_abs]; exact abs_setIntegral_le hK A (hs.trans hr.1))

/-- Cochrane (2023), §20.2.2, p. 474: **the conditional mean of the shock decays**: for
`A ∈ 𝓕_s`, `∫_A ν_t = e^{−η(t−s)} ∫_A ν_s` for `t ≥ s ≥ 0`. -/
theorem setIntegral_nu [IsProbabilityMeasure P] {η : ℝ} {𝓕 : Filtration ℝ mΩ}
    {ν : ℝ → Ω → ℝ} (hν : Regular 𝓕 ν) (hνb : BddL1 P ν)
    (hνd : ExpDrift P 𝓕 ν (fun r ω => -(η * ν r ω))) {s : ℝ} (hs : 0 ≤ s) {A : Set Ω}
    (hA : MeasurableSet[𝓕 s] A) {t : ℝ} (hst : s ≤ t) :
    ∫ ω in A, ν t ω ∂P = Real.exp (-η * (t - s)) * ∫ ω in A, ν s ω ∂P := by
  obtain ⟨Kν, hKν⟩ := hνb
  have hmν : ∀ t, Measurable (ν t) := fun t => ((hν.2 t).mono (𝓕.le t)).measurable
  set mν : ℝ → ℝ := fun r => ∫ ω in A, ν r ω ∂P
  have hiν := integrableOn_setIntegral hν.1 hmν hKν A hs
  have hfν : ∀ t, s ≤ t → mν t - mν s = ∫ r in s..t, -(η * mν r) := fun t ht => by
    have pν := integrable_prod_proc (P := P) hν.1 hmν hKν hs (b := t)
    rw [setIntegral_expDrift hνd hs ht hA (hKν s hs).1 (hKν t (hs.trans ht)).1
      (pν.const_mul η).neg]
    refine intervalIntegral.integral_congr fun r _ => ?_
    rw [integral_neg, integral_const_mul]
  have hcν : ContinuousOn mν (Set.Ici s) :=
    continuousOn_of_intForm (fun b => ((hiν b).const_mul η).neg) hfν
  exact linear_ode_Ici (a := -η) (S := ∅) Set.countable_empty hcν
    (fun r hr _ => (hasDerivAt_of_intForm (G := fun r => -(η * mν r))
      (continuousOn_const.mul hcν).neg hfν hr).congr_deriv (by ring)) t hst

/-- Cochrane (2023), §20.2.2, p. 474: **`E_s ν_t = e^{−η(t−s)} ν_s`** for a regular
`L¹`-bounded shock with `E_t dν = −ην dt`. -/
theorem condExp_nu [IsProbabilityMeasure P] {η : ℝ} {𝓕 : Filtration ℝ mΩ} {ν : ℝ → Ω → ℝ}
    (hν : Regular 𝓕 ν) (hνb : BddL1 P ν) (hνd : ExpDrift P 𝓕 ν (fun r ω => -(η * ν r ω)))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    P[ν t | 𝓕 s] =ᵐ[P] fun ω => Real.exp (-η * (t - s)) * ν s ω := by
  obtain ⟨Kν, hKν⟩ := hνb
  have h1 : (fun ω => Real.exp (-η * (t - s)) * ν s ω) =ᵐ[P] P[ν t | 𝓕 s] :=
    ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hKν t (hs.trans hst)).1
      (fun _ _ _ => ((hKν s hs).1.const_mul _).integrableOn)
      (fun A hA _ => by
        rw [integral_const_mul, setIntegral_nu hν ⟨Kν, hKν⟩ hνd hs hA hst])
      (stronglyMeasurable_const.mul (hν.2 s)).aestronglyMeasurable
  exact h1.symm

/-! ## The response kernel -/

/-- Cochrane (2023), (20.8), p. 474, with a mean-reverting natural-rate shock: the response of
expected inflation at horizon `τ` to the shock, per unit of `d`,
`k(τ) = e^{−λ^b τ}∫_0^τ e^{(λ^b − η)v} dv = ∫_0^τ e^{−λ^b(τ−v)}e^{−ηv} dv`. -/
noncomputable def natK (lb η τ : ℝ) : ℝ :=
  Real.exp (-(lb * τ)) * ∫ v in (0 : ℝ)..τ, Real.exp ((lb - η) * v)

/-- Cochrane (2023), (20.8), p. 474: `k(0) = 0`. -/
theorem natK_zero (lb η : ℝ) : natK lb η 0 = 0 := by simp [natK]

/-- Cochrane (2023), (20.8), p. 474: `k' = −λ^b k + e^{−ητ}`. -/
theorem hasDerivAt_natK (lb η τ : ℝ) :
    HasDerivAt (natK lb η) (-lb * natK lb η τ + Real.exp (-(η * τ))) τ := by
  have h1 : HasDerivAt (fun τ => Real.exp (-(lb * τ))) (Real.exp (-(lb * τ)) * -lb) τ := by
    simpa using ((hasDerivAt_id' τ).const_mul lb).neg.exp
  have h2 := ((by fun_prop : Continuous fun v => Real.exp ((lb - η) * v)).integral_hasStrictDerivAt
    0 τ).hasDerivAt
  refine (h1.mul h2).congr_deriv ?_
  have he : Real.exp (-(lb * τ)) * Real.exp ((lb - η) * τ) = Real.exp (-(η * τ)) := by
    rw [← Real.exp_add]
    ring_nf
  simp only [natK]
  linear_combination he

/-- Cochrane (2023), (20.8), p. 474: `k` is continuous. -/
theorem continuous_natK (lb η : ℝ) : Continuous (natK lb η) :=
  continuous_iff_continuousAt.2 fun τ => (hasDerivAt_natK lb η τ).continuousAt

/-! ## Expected inflation and output under natural-rate shocks -/

/-- Cochrane (2023), §20.2.2, p. 474 (tool): the conditional mean of an affine combination,
`∫_A (a + b f + c g) = P(A)a + b∫_A f + c∫_A g`. -/
theorem setIntegral_affine [IsFiniteMeasure P] {f g : Ω → ℝ} (hf : Integrable f P)
    (hg : Integrable g P) (a b c : ℝ) (A : Set Ω) :
    ∫ ω in A, (a + b * f ω + c * g ω) ∂P = P.real A * a + b * ∫ ω in A, f ω ∂P +
      c * ∫ ω in A, g ω ∂P := by
  have h1 : Integrable (fun ω => a + b * f ω) (P.restrict A) :=
    ((integrable_const a).add (hf.const_mul b)).integrableOn
  have h2 : Integrable (fun ω => c * g ω) (P.restrict A) := (hg.const_mul c).integrableOn
  have h3 : Integrable (fun ω => b * f ω) (P.restrict A) := (hf.const_mul b).integrableOn
  calc ∫ ω in A, (a + b * f ω + c * g ω) ∂P
      = ∫ ω in A, (a + b * f ω) ∂P + ∫ ω in A, c * g ω ∂P := integral_add h1 h2
    _ = (∫ ω in A, a ∂P + ∫ ω in A, b * f ω ∂P) + ∫ ω in A, c * g ω ∂P := by
        rw [integral_add (integrable_const a) h3]
    _ = _ := by rw [integral_const_mul, integral_const_mul, setIntegral_const, smul_eq_mul]

/-- Cochrane (2023), (20.8)–(20.10), pp. 474–475, under natural-rate shocks: **conditional
means of inflation.** In a regular `L¹`-bounded equilibrium with `i = 0`, natural rate
`trapStep u T + ν` (`E_t dν = −ην dt`, `η ≥ 0`) and disturbance `trapStep g T`, for `A ∈ 𝓕_s`
and `t ≥ s ≥ 0`: `∫_A π_t = P(A)wPi(0)_t + e^{−λ^b(t−s)}(∫_A π_s − P(A)wPi(0)_s) +
d k(t − s)∫_A ν_s`.
Generalises `TidyR7StochWerningTrap.setIntegral_trap` (the case `ν = 0`). -/
theorem setIntegral_pi_nat [IsProbabilityMeasure P] {σ ρ κ η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hη : 0 ≤ η) {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} {ν x π : ℝ → Ω → ℝ} (hν : Regular 𝓕 ν)
    (hνb : BddL1 P ν) (hνd : ExpDrift P 𝓕 ν (fun r ω => -(η * ν r ω))) (hx : Regular 𝓕 x)
    (hxb : BddL1 P x) (hπ : Regular 𝓕 π) (hπb : BddL1 P π)
    (h : IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T) ν x π) {s : ℝ}
    (hs : 0 ≤ s) {A : Set Ω} (hA : MeasurableSet[𝓕 s] A) {t : ℝ} (hst : s ≤ t) :
    ∫ ω in A, π t ω ∂P = P.real A * wPi σ κ ρ T u g 0 t +
      Real.exp (-(lamb ρ κ σ * (t - s))) * (∫ ω in A, π s ω ∂P - P.real A * wPi σ κ ρ T u g 0 s) +
      natD σ κ ρ η * natK (lamb ρ κ σ) η (t - s) * ∫ ω in A, ν s ω ∂P := by
  obtain ⟨Kν, hKν⟩ := hνb
  obtain ⟨Kx, hKx⟩ := hxb
  obtain ⟨Kπ, hKπ⟩ := hπb
  have hmν : ∀ t, Measurable (ν t) := fun t => ((hν.2 t).mono (𝓕.le t)).measurable
  have hmx : ∀ t, Measurable (x t) := fun t => ((hx.2 t).mono (𝓕.le t)).measurable
  have hmπ : ∀ t, Measurable (π t) := fun t => ((hπ.2 t).mono (𝓕.le t)).measurable
  have hsub := lamf_sub_lamb ρ κ σ
  set lf := lamf ρ κ σ
  set lb := lamb ρ κ σ
  set d := natD σ κ ρ η
  set p := P.real A
  set mx : ℝ → ℝ := fun r => ∫ ω in A, x r ω ∂P
  set mπ : ℝ → ℝ := fun r => ∫ ω in A, π r ω ∂P
  set mν : ℝ → ℝ := fun r => ∫ ω in A, ν r ω ∂P
  set W0 := wPi σ κ ρ T u g 0
  set X0 := wX σ κ ρ T u g 0
  have hix := integrableOn_setIntegral hx.1 hmx hKx A hs
  have hiπ := integrableOn_setIntegral hπ.1 hmπ hKπ A hs
  have hiν := integrableOn_setIntegral hν.1 hmν hKν A hs
  have itr : ∀ c b, IntegrableOn (trapStep c T) (Set.Icc s b) := fun c b =>
    trapStep_integrableOn c T measure_Icc_lt_top.ne
  have hcm := fun t (ht : s ≤ t) => condMean_integral_eq (P := P)
    (fun a b => integrableOn_zero) (fun a b => trapStep_integrableOn u T measure_Ioc_lt_top.ne)
    (fun a b => trapStep_integrableOn g T measure_Ioc_lt_top.ne) hν ⟨Kν, hKν⟩
    hx ⟨Kx, hKx⟩ hπ ⟨Kπ, hKπ⟩ h hs hA t ht
  have hGx : ∀ b, IntegrableOn (fun r => σ * (p * 0 - mπ r - (p * trapStep u T r + mν r)))
      (Set.Icc s b) := fun b =>
    ((((integrableOn_const (by simp)).sub (hiπ b)).sub (((itr u b).const_mul p).add
      (hiν b))).const_mul σ)
  have hGπ : ∀ b, IntegrableOn (fun r => ρ * mπ r - κ * (mx r + p * trapStep g T r))
      (Set.Icc s b) := fun b =>
    ((hiπ b).const_mul ρ).sub (((hix b).add ((itr g b).const_mul p)).const_mul κ)
  have hcx : ContinuousOn mx (Set.Ici s) := continuousOn_of_intForm hGx fun t ht => (hcm t ht).1
  have hcπ : ContinuousOn mπ (Set.Ici s) :=
    continuousOn_of_intForm hGπ fun t ht => (hcm t ht).2
  -- the unstable combination, integrated over `A`
  have hun : ∀ r, s ≤ r → lf * mπ r - κ * mx r = p * (lf * W0 r - κ * X0 r) + d * mν r := by
    intro r hr
    have hr0 := hs.trans hr
    have e := integral_congr_ae (μ := P.restrict A) (ae_restrict_of_ae
      (unstable_natural hσ hκ hη hν ⟨Kν, hKν⟩ hνd hx ⟨Kx, hKx⟩ hπ ⟨Kπ, hKπ⟩ h hr0))
    rw [integral_sub ((hKπ r hr0).1.integrableOn.const_mul lf)
        ((hKx r hr0).1.integrableOn.const_mul κ),
      integral_add (integrable_const _) ((hKν r hr0).1.integrableOn.const_mul d),
      integral_const_mul, integral_const_mul, integral_const_mul, setIntegral_const,
      smul_eq_mul] at e
    simp only [mx, mπ, mν, W0, X0, p, lf, d]
    linarith
  have hnu : ∀ r, s ≤ r → mν r = Real.exp (-η * (r - s)) * mν s := fun r hr =>
    setIntegral_nu hν ⟨Kν, hKν⟩ hνd hs hA hr
  -- the deviation `G = mπ − p W0 − d mν(s) k(· − s)` decays at `λ^b`
  have hp := wPath_isPath (ρ := ρ) hκ hσ T u g 0
  set G : ℝ → ℝ := fun r => mπ r - p * W0 r - d * mν s * natK lb η (r - s) with hGdef
  have hGc : ContinuousOn G (Set.Ici s) :=
    (hcπ.sub (continuousOn_const.mul (wPi_continuous σ κ ρ T u g 0 hκ hσ).continuousOn)).sub
      (continuousOn_const.mul ((continuous_natK lb η).comp
        (continuous_id.sub continuous_const)).continuousOn)
  have hGd : ∀ r, s < r → r ∉ ({T} : Set ℝ) → HasDerivAt G (-lb * G r) r := by
    intro r hr hrT
    have hrT' : r ≠ T := hrT
    have ca : ∀ {m : ℝ → ℝ}, ContinuousOn m (Set.Ici s) → ContinuousAt m r := fun hm =>
      hm.continuousAt (Ici_mem_nhds hr)
    have dπ := TidyR7StochWerningNatural.hasDerivAt_of_intForm_at hGπ (fun t ht => (hcm t ht).2)
      hr (((ca hcπ).const_mul ρ).sub (((ca hcx).add ((trapStep_continuousAt g hrT').const_mul
        p)).const_mul κ))
    have dW := (hp.2.2 r (hs.trans_lt hr) hrT).2
    have dk : HasDerivAt (fun r => natK lb η (r - s))
        (-lb * natK lb η (r - s) + Real.exp (-(η * (r - s)))) r := by
      exact (hasDerivAt_natK lb η (r - s)).comp_sub_const r s
    refine ((dπ.sub (dW.const_mul p)).sub (dk.const_mul (d * mν s))).congr_deriv ?_
    have h1 := hun r hr.le
    have h2 := hnu r hr.le
    have he : Real.exp (-η * (r - s)) = Real.exp (-(η * (r - s))) := by ring_nf
    rw [he] at h2
    simp only [G]
    linear_combination h1 - (mπ r - p * W0 r) * hsub + d * h2
  have hsol := linear_ode_Ici (Set.countable_singleton T) hGc hGd t hst
  simp only [G, sub_self, natK_zero, mul_zero, sub_zero] at hsol
  have he : Real.exp (-lb * (t - s)) = Real.exp (-(lb * (t - s))) := by ring_nf
  rw [he] at hsol
  change mπ t = _
  linarith

/-- **Cochrane (2023), (20.8)–(20.10), pp. 474–475, §20.2.4, p. 479, under natural-rate shocks:
expected inflation.** In every regular `L¹`-bounded equilibrium with `i = 0`, natural rate
`trapStep u T + ν` (`E_t dν = −ην dt`, `η ≥ 0`) and disturbance `trapStep g T`,
`E_s π_t = wPi(0)_t + e^{−λ^b(t−s)}(π_s − wPi(0)_s) + d k(t − s) ν_s` almost surely, for
`t ≥ s ≥ 0`, with `d = −κσ/(λ^f + η)` (`TidyR7StochWerningNatural.natD`) and `k = natK`.
With `ν = 0` this is `TidyR7StochWerningTrap.condExp_pi_eq`. -/
theorem condExp_pi_nat [IsProbabilityMeasure P] {σ ρ κ η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hη : 0 ≤ η) {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} {ν x π : ℝ → Ω → ℝ} (hν : Regular 𝓕 ν)
    (hνb : BddL1 P ν) (hνd : ExpDrift P 𝓕 ν (fun r ω => -(η * ν r ω))) (hx : Regular 𝓕 x)
    (hxb : BddL1 P x) (hπ : Regular 𝓕 π) (hπb : BddL1 P π)
    (h : IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T) ν x π) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    P[π t | 𝓕 s] =ᵐ[P] fun ω => wPi σ κ ρ T u g 0 t +
      Real.exp (-(lamb ρ κ σ * (t - s))) * (π s ω - wPi σ κ ρ T u g 0 s) +
      natD σ κ ρ η * natK (lamb ρ κ σ) η (t - s) * ν s ω := by
  obtain ⟨Kν, hKν⟩ := hνb
  obtain ⟨Kπ, hKπ⟩ := hπb
  have hπs := (hKπ s hs).1
  have hνs := (hKν s hs).1
  have hint : Integrable (fun ω => wPi σ κ ρ T u g 0 t +
      Real.exp (-(lamb ρ κ σ * (t - s))) * (π s ω - wPi σ κ ρ T u g 0 s) +
      natD σ κ ρ η * natK (lamb ρ κ σ) η (t - s) * ν s ω) P :=
    ((integrable_const _).add ((hπs.sub (integrable_const _)).const_mul _)).add
      (hνs.const_mul _)
  have h1 : (fun ω => wPi σ κ ρ T u g 0 t +
      Real.exp (-(lamb ρ κ σ * (t - s))) * (π s ω - wPi σ κ ρ T u g 0 s) +
      natD σ κ ρ η * natK (lamb ρ κ σ) η (t - s) * ν s ω) =ᵐ[P] P[π t | 𝓕 s] :=
    ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hKπ t (hs.trans hst)).1
      (fun _ _ _ => hint.integrableOn)
      (fun A hA _ => by
        calc ∫ ω in A, (wPi σ κ ρ T u g 0 t +
              Real.exp (-(lamb ρ κ σ * (t - s))) * (π s ω - wPi σ κ ρ T u g 0 s) +
              natD σ κ ρ η * natK (lamb ρ κ σ) η (t - s) * ν s ω) ∂P
            = ∫ ω in A, ((wPi σ κ ρ T u g 0 t - Real.exp (-(lamb ρ κ σ * (t - s))) *
                wPi σ κ ρ T u g 0 s) + Real.exp (-(lamb ρ κ σ * (t - s))) * π s ω +
              natD σ κ ρ η * natK (lamb ρ κ σ) η (t - s) * ν s ω) ∂P := by
                congr 1; funext ω; ring
          _ = _ := setIntegral_affine hπs hνs _ _ _ A
          _ = ∫ ω in A, π t ω ∂P := by
                rw [setIntegral_pi_nat hσ hκ hη hν ⟨Kν, hKν⟩ hνd hx hxb hπ ⟨Kπ, hKπ⟩ h hs hA
                  hst]
                ring)
      ((stronglyMeasurable_const.add (stronglyMeasurable_const.mul ((hπ.2 s).sub
        stronglyMeasurable_const))).add
          (stronglyMeasurable_const.mul (hν.2 s))).aestronglyMeasurable
  exact h1.symm

/-- **Cochrane (2023), (20.10), p. 475, under natural-rate shocks: expected output.** In the
setting of `condExp_pi_nat`,
`E_s x_t = wX(0)_t + (λ^f/κ)(e^{−λ^b(t−s)}(π_s − wPi(0)_s) + d k(t − s) ν_s) −
(d/κ)e^{−η(t−s)} ν_s` almost surely.
Generalises `TidyR7StochWerningTrap.condExp_x_eq`. -/
theorem condExp_x_nat [IsProbabilityMeasure P] {σ ρ κ η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hη : 0 ≤ η) {𝓕 : Filtration ℝ mΩ} {T u g : ℝ} {ν x π : ℝ → Ω → ℝ} (hν : Regular 𝓕 ν)
    (hνb : BddL1 P ν) (hνd : ExpDrift P 𝓕 ν (fun r ω => -(η * ν r ω))) (hx : Regular 𝓕 x)
    (hxb : BddL1 P x) (hπ : Regular 𝓕 π) (hπb : BddL1 P π)
    (h : IsStochEqm σ ρ κ P 𝓕 (fun _ => 0) (trapStep u T) (trapStep g T) ν x π) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    P[x t | 𝓕 s] =ᵐ[P] fun ω => wX σ κ ρ T u g 0 t + lamf ρ κ σ / κ *
      (Real.exp (-(lamb ρ κ σ * (t - s))) * (π s ω - wPi σ κ ρ T u g 0 s) +
        natD σ κ ρ η * natK (lamb ρ κ σ) η (t - s) * ν s ω) -
      natD σ κ ρ η / κ * (Real.exp (-η * (t - s)) * ν s ω) := by
  obtain ⟨Kν, hKν⟩ := hνb
  obtain ⟨Kπ, hKπ⟩ := hπb
  obtain ⟨Kx, hKx⟩ := hxb
  have ht0 := hs.trans hst
  have hπs := (hKπ s hs).1
  have hνs := (hKν s hs).1
  have hκ0 := hκ.ne'
  set lf := lamf ρ κ σ
  set lb := lamb ρ κ σ
  set d := natD σ κ ρ η
  have hint : Integrable (fun ω => wX σ κ ρ T u g 0 t + lf / κ *
      (Real.exp (-(lb * (t - s))) * (π s ω - wPi σ κ ρ T u g 0 s) +
        d * natK lb η (t - s) * ν s ω) - d / κ * (Real.exp (-η * (t - s)) * ν s ω)) P :=
    ((integrable_const _).add ((((hπs.sub (integrable_const _)).const_mul _).add
      (hνs.const_mul _)).const_mul _)).sub ((hνs.const_mul _).const_mul _)
  have h1 : (fun ω => wX σ κ ρ T u g 0 t + lf / κ *
      (Real.exp (-(lb * (t - s))) * (π s ω - wPi σ κ ρ T u g 0 s) +
        d * natK lb η (t - s) * ν s ω) - d / κ * (Real.exp (-η * (t - s)) * ν s ω))
      =ᵐ[P] P[x t | 𝓕 s] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hKx t ht0).1
      (fun _ _ _ => hint.integrableOn) (fun A hA _ => ?_)
      (((stronglyMeasurable_const.add (stronglyMeasurable_const.mul
        ((stronglyMeasurable_const.mul ((hπ.2 s).sub stronglyMeasurable_const)).add
          (stronglyMeasurable_const.mul (hν.2 s))))).sub (stronglyMeasurable_const.mul
            (stronglyMeasurable_const.mul (hν.2 s)))).aestronglyMeasurable)
    have hπt := setIntegral_pi_nat hσ hκ hη hν ⟨Kν, hKν⟩ hνd hx ⟨Kx, hKx⟩ hπ ⟨Kπ, hKπ⟩ h hs
      hA hst
    have hνt := setIntegral_nu (P := P) hν ⟨Kν, hKν⟩ hνd hs hA hst
    have e := integral_congr_ae (μ := P.restrict A) (ae_restrict_of_ae
      (unstable_natural hσ hκ hη hν ⟨Kν, hKν⟩ hνd hx ⟨Kx, hKx⟩ hπ ⟨Kπ, hKπ⟩ h ht0))
    rw [integral_sub ((hKπ t ht0).1.integrableOn.const_mul lf)
        ((hKx t ht0).1.integrableOn.const_mul κ),
      integral_add (integrable_const _) ((hKν t ht0).1.integrableOn.const_mul d),
      integral_const_mul, integral_const_mul, integral_const_mul, setIntegral_const,
      smul_eq_mul] at e
    have ea : (fun ω => wX σ κ ρ T u g 0 t + lf / κ *
        (Real.exp (-(lb * (t - s))) * (π s ω - wPi σ κ ρ T u g 0 s) +
          d * natK lb η (t - s) * ν s ω) - d / κ * (Real.exp (-η * (t - s)) * ν s ω)) =
        fun ω => (wX σ κ ρ T u g 0 t - lf / κ * (Real.exp (-(lb * (t - s))) *
          wPi σ κ ρ T u g 0 s)) + lf / κ * Real.exp (-(lb * (t - s))) * π s ω +
          (lf / κ * (d * natK lb η (t - s)) - d / κ * Real.exp (-η * (t - s))) * ν s ω := by
      funext ω; ring
    rw [ea, setIntegral_affine hπs hνs]
    have key : κ * ∫ ω in A, x t ω ∂P = lf * ∫ ω in A, π t ω ∂P -
        P.real A * (lf * wPi σ κ ρ T u g 0 t - κ * wX σ κ ρ T u g 0 t) -
        d * ∫ ω in A, ν t ω ∂P := by linarith
    have hq1 : κ * (lf / κ) = lf := mul_div_cancel₀ _ hκ0
    have hq2 : κ * (d / κ) = d := mul_div_cancel₀ _ hκ0
    apply mul_left_cancel₀ hκ0
    rw [key, hπt, hνt]
    linear_combination (Real.exp (-(lb * (t - s))) * ∫ ω in A, π s ω ∂P -
      P.real A * Real.exp (-(lb * (t - s))) * wPi σ κ ρ T u g 0 s +
      d * natK lb η (t - s) * ∫ ω in A, ν s ω ∂P) * hq1 -
      (Real.exp (-η * (t - s)) * ∫ ω in A, ν s ω ∂P) * hq2
  exact h1.symm

/-! ## Mean-square bounds for the explicit equilibria -/

/-- Cochrane (2023), §20.2.2, p. 474 (tool): sums of `L²`-bounded processes are
`L²`-bounded.
The `L²` analogue of `TidyR7StochWerningNaturalExist.BddL1.add`. -/
theorem BddL2.add {Z₁ Z₂ : ℝ → Ω → ℝ} (h₁ : BddL2 P Z₁) (h₂ : BddL2 P Z₂) :
    BddL2 P (fun t ω => Z₁ t ω + Z₂ t ω) := by
  obtain ⟨K₁, hK₁⟩ := h₁
  obtain ⟨K₂, hK₂⟩ := h₂
  refine ⟨2 * K₁ + 2 * K₂, fun t ht => ⟨(hK₁ t ht).1.add (hK₂ t ht).1, ?_⟩⟩
  have i1 := (hK₁ t ht).1.integrable_sq
  have i2 := (hK₂ t ht).1.integrable_sq
  calc ∫ ω, (Z₁ t ω + Z₂ t ω) ^ 2 ∂P ≤ ∫ ω, (2 * Z₁ t ω ^ 2 + 2 * Z₂ t ω ^ 2) ∂P := by
        refine integral_mono ((hK₁ t ht).1.add (hK₂ t ht).1).integrable_sq
          ((i1.const_mul 2).add (i2.const_mul 2)) fun ω => ?_
        nlinarith [sq_nonneg (Z₁ t ω - Z₂ t ω)]
    _ = 2 * ∫ ω, Z₁ t ω ^ 2 ∂P + 2 * ∫ ω, Z₂ t ω ^ 2 ∂P := by
        rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul,
          integral_const_mul]
    _ ≤ 2 * K₁ + 2 * K₂ := by linarith [(hK₁ t ht).2, (hK₂ t ht).2]

/-- Cochrane (2023), §20.2.2, p. 474 (tool): multiples of `L²`-bounded processes are
`L²`-bounded.
The `L²` analogue of `TidyR7StochWerningNaturalExist.BddL1.const_mul`. -/
theorem BddL2.const_mul {Z : ℝ → Ω → ℝ} (h : BddL2 P Z) (c : ℝ) :
    BddL2 P (fun t ω => c * Z t ω) := by
  obtain ⟨K, hK⟩ := h
  refine ⟨c ^ 2 * K, fun t ht => ⟨(hK t ht).1.const_mul c, ?_⟩⟩
  calc ∫ ω, (c * Z t ω) ^ 2 ∂P = c ^ 2 * ∫ ω, Z t ω ^ 2 ∂P := by
        rw [← integral_const_mul]; congr 1; funext ω; ring
    _ ≤ c ^ 2 * K := mul_le_mul_of_nonneg_left (hK t ht).2 (sq_nonneg c)

/-- Cochrane (2023), §20.2.2, p. 474 (tool): a bounded deterministic path is `L²`-bounded.
The `L²` analogue of `TidyR7StochWerningNaturalExist.bddL1_det`. -/
theorem bddL2_det [IsProbabilityMeasure P] {f : ℝ → ℝ} (hf : BddOnIci f) :
    BddL2 P (fun t _ => f t) := by
  obtain ⟨K, hK⟩ := hf
  refine ⟨K ^ 2, fun t ht => ⟨memLp_const _, ?_⟩⟩
  simp only [integral_const, probReal_univ, one_smul]
  have := hK t ht
  nlinarith [abs_nonneg (f t), sq_abs (f t)]

/-- Cochrane (2023), §20.2.2, p. 475 (tool): **Cauchy–Schwarz for the smoothing**,
`(∫_0^t w f)² ≤ (∫_0^t w)(∫_0^t w f²)` for a positive continuous weight `w` and continuous `f`,
`t > 0`.
A case of Mathlib `integral_mul_le_Lp_mul_Lq_of_nonneg`. -/
theorem sq_integral_weight_le {w f : ℝ → ℝ} (hw : Continuous w) (hwp : ∀ u, 0 < w u)
    (hf : Continuous f) {t : ℝ} (ht : 0 < t) :
    (∫ u in (0 : ℝ)..t, w u * f u) ^ 2 ≤
      (∫ u in (0 : ℝ)..t, w u) * ∫ u in (0 : ℝ)..t, w u * f u ^ 2 := by
  set Wt := ∫ u in (0 : ℝ)..t, w u
  set I := ∫ u in (0 : ℝ)..t, w u * f u
  set J := ∫ u in (0 : ℝ)..t, w u * f u ^ 2
  have hW : 0 < Wt := intervalIntegral.intervalIntegral_pos_of_pos_on
    (hw.intervalIntegrable 0 t) (fun u _ => hwp u) ht
  have i1 : IntervalIntegrable (fun u => w u * f u ^ 2) volume 0 t :=
    (hw.mul (hf.pow 2)).intervalIntegrable 0 t
  have i2 : IntervalIntegrable (fun u => w u * f u) volume 0 t :=
    (hw.mul hf).intervalIntegrable 0 t
  have i3 : IntervalIntegrable w volume 0 t := hw.intervalIntegrable 0 t
  have h0 : 0 ≤ ∫ u in (0 : ℝ)..t, w u * (Wt * f u - I) ^ 2 :=
    intervalIntegral.integral_nonneg ht.le fun u _ => mul_nonneg (hwp u).le (sq_nonneg _)
  have e : (∫ u in (0 : ℝ)..t, w u * (Wt * f u - I) ^ 2) = Wt ^ 2 * J - 2 * Wt * I * I +
      I ^ 2 * Wt := by
    have e1 : (fun u => w u * (Wt * f u - I) ^ 2) =
        fun u => Wt ^ 2 * (w u * f u ^ 2) - 2 * Wt * I * (w u * f u) + I ^ 2 * w u := by
      funext u
      ring
    rw [e1, intervalIntegral.integral_add ((i1.const_mul _).sub (i2.const_mul _))
        (i3.const_mul _), intervalIntegral.integral_sub (i1.const_mul _) (i2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [e] at h0
  have : 0 ≤ Wt * (Wt * J - I ^ 2) := by nlinarith
  nlinarith [(mul_nonneg_iff_of_pos_left hW).1 this]

/-- Cochrane (2023), §20.2.2, p. 475: the smoothing as a weighted integral,
`chiProc λ Z_t = ∫_0^t e^{−λ(t−u)} Z_u du`. -/
theorem chiProc_eq_integral (lam : ℝ) (Z : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    chiProc lam Z t ω = ∫ u in (0 : ℝ)..t, Real.exp (-(lam * (t - u))) * Z u ω := by
  simp only [chiProc, ouPrim]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u _ => ?_
  change Real.exp (-lam * t) * (Real.exp (lam * u) * Z u ω) = _
  rw [← mul_assoc, ← Real.exp_add]
  ring_nf

/-- Cochrane (2023), §20.2.2, p. 475: **`χ_t² ≤ chiProc λ (Z²)_t / λ`** for `λ > 0`, `t ≥ 0` and
continuous paths. -/
theorem sq_chiProc_le {lam : ℝ} (hlam : 0 < lam) {Z : ℝ → Ω → ℝ}
    (hZ : ∀ ω, Continuous fun t => Z t ω) {t : ℝ} (ht : 0 ≤ t) (ω : Ω) :
    chiProc lam Z t ω ^ 2 ≤ (1 / lam) * chiProc lam (fun r ω => Z r ω ^ 2) t ω := by
  rw [chiProc_eq_integral, chiProc_eq_integral]
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    simp
  have hwc : Continuous fun u => Real.exp (-(lam * (t - u))) := by fun_prop
  have hcs := sq_integral_weight_le hwc (fun u => Real.exp_pos _) (hZ ω) hpos
  have hJ : 0 ≤ ∫ u in (0 : ℝ)..t, Real.exp (-(lam * (t - u))) * Z u ω ^ 2 :=
    intervalIntegral.integral_nonneg hpos.le fun u _ => mul_nonneg (Real.exp_pos _).le
      (sq_nonneg _)
  exact hcs.trans (mul_le_mul_of_nonneg_right (integral_exp_decay_le hlam t) hJ)

variable {W : ℝ≥0 → Ω → ℝ}

/-- Cochrane (2023), §20.2.2, p. 475: **the smoothing of an `L²`-bounded regular process is
`L²`-bounded** (`λ > 0`), on the Brownian filtration. -/
theorem bddL2_chiProc [IsProbabilityMeasure P] (hW : ∀ t, Measurable (W t)) {Z : ℝ → Ω → ℝ}
    (hZ : Regular (bmFiltrationReal W hW) Z) (hZb : BddL2 P Z) {lam : ℝ} (hlam : 0 < lam) :
    BddL2 P (chiProc lam Z) := by
  obtain ⟨K, hK⟩ := hZb
  have hZ2 : Regular (bmFiltrationReal W hW) (fun r ω => Z r ω ^ 2) :=
    ⟨fun ω => (hZ.1 ω).pow 2, fun t => (hZ.2 t).pow 2⟩
  have hZ2b : BddL1 P (fun r ω => Z r ω ^ 2) := ⟨K, fun t ht => ⟨(hK t ht).1.integrable_sq, by
    simp only [abs_pow, sq_abs]; exact (hK t ht).2⟩⟩
  obtain ⟨K', hK'⟩ := bddL1_chiProc hW hZ2 hZ2b hlam
  refine ⟨(1 / lam) * K', fun t ht => ?_⟩
  have hχm : AEStronglyMeasurable (chiProc lam Z t) P :=
    ((regular_chiProc hW hZ lam).2 t).mono ((bmFiltrationReal W hW).le t) |>.aestronglyMeasurable
  have hb := sq_chiProc_le hlam hZ.1 ht
  have hi := ((hK' t ht).1.const_mul (1 / lam))
  have hsq : Integrable (fun ω => chiProc lam Z t ω ^ 2) P :=
    hi.mono' (hχm.pow 2) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hb ω)
  refine ⟨(memLp_two_iff_integrable_sq hχm).2 hsq, ?_⟩
  calc ∫ ω, chiProc lam Z t ω ^ 2 ∂P ≤ ∫ ω, (1 / lam) * chiProc lam (fun r ω => Z r ω ^ 2) t ω ∂P :=
        integral_mono hsq hi hb
    _ ≤ ∫ ω, (1 / lam) * |chiProc lam (fun r ω => Z r ω ^ 2) t ω| ∂P :=
        integral_mono hi ((hK' t ht).1.abs.const_mul _) fun ω =>
          mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    _ = (1 / lam) * ∫ ω, |chiProc lam (fun r ω => Z r ω ^ 2) t ω| ∂P := integral_const_mul _ _
    _ ≤ (1 / lam) * K' := mul_le_mul_of_nonneg_left (hK' t ht).2 (by positivity)

/-- Cochrane (2023), §20.2.2, p. 474: the OU process is `L²`-bounded (`η > 0`).
Restates `TidyR7StochWerningExist.ouProc_sq_le`; a special case of
`TidyR7StochWerningExist.bddL2_add_ou`. -/
theorem bddL2_ou [IsProbabilityMeasure P] (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {η : ℝ} (hη : 0 < η) (sν : ℝ) : BddL2 P (ouProc η 0 0 sν W) :=
  ⟨sν ^ 2 / (2 * η), fun _ ht => ouProc_sq_le hB hW hcont hW0 hη sν ht⟩

/-- **Cochrane (2023), §20.2.2, p. 474, with natural-rate shocks: the inflation process is
bounded in mean square** (`η > 0`).
Strengthens `TidyR7StochWerningNaturalExist.bddL1_natPi`. -/
theorem bddL2_natPi [IsProbabilityMeasure P] (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {σ ρ κ η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hη : 0 < η)
    (sν T u g πT b : ℝ) : BddL2 P (natPi σ κ ρ η sν T u g πT b W) := by
  have hlb := lamb_pos (ρ := ρ) hκ hσ
  exact BddL2.add (BddL2.add (bddL2_det (wPath_bdd (ρ := ρ) hκ hσ T u g πT).2)
    (BddL2.const_mul (bddL2_chiProc hW (regular_ouProc hW hcont η 0 0 sν)
      (bddL2_ou hB hW hcont hW0 hη sν) hlb) _)) (bddL2_ou hB hW hcont hW0 hlb b)

/-- **Cochrane (2023), (20.10), p. 475, with natural-rate shocks: the output process is bounded
in mean square** (`η > 0`).
Strengthens `TidyR7StochWerningNaturalExist.bddL1_natX`. -/
theorem bddL2_natX [IsProbabilityMeasure P] (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {σ ρ κ η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hη : 0 < η)
    (sν T u g πT b : ℝ) : BddL2 P (natX σ κ ρ η sν T u g πT b W) := by
  have hlb := lamb_pos (ρ := ρ) hκ hσ
  exact BddL2.add (BddL2.add (BddL2.add (bddL2_det (wPath_bdd (ρ := ρ) hκ hσ T u g πT).1)
    (BddL2.const_mul (bddL2_chiProc hW (regular_ouProc hW hcont η 0 0 sν)
      (bddL2_ou hB hW hcont hW0 hη sν) hlb) _))
    (BddL2.const_mul (bddL2_ou hB hW hcont hW0 hlb b) _))
    (BddL2.const_mul (bddL2_ou hB hW hcont hW0 hη sν) _)

/-! ## Non-vacuity on the constructed Brownian motion -/

open Cochrane.ZeroBound.TidyR7BrownianExist Cochrane.ZeroBound.TidyR7BrownianSchauder

/-- Cochrane (2023), §20.2.2, pp. 474–475 (non-vacuity): on bmPath at the book's calibration
(`ρ = 0.05`, `σ = κ = 1`, `T = 5`, `u = −2%`, `g = 0`) with the OU natural-rate shock
`η = 1/2`, `s_ν = 1/100`, the explicit equilibrium with `π_T = 0`, `b = 0` is bounded in mean
square and its expected inflation obeys `condExp_pi_nat` at every `0 ≤ s ≤ t`. -/
theorem bmPath_condExp_pi_nat :
    BddL2 gaussSeq (natPi 1 1 (1 / 20) (1 / 2) (1 / 100) 5 (-2 / 100) 0 0 0 bmPath) ∧
      BddL2 gaussSeq (natX 1 1 (1 / 20) (1 / 2) (1 / 100) 5 (-2 / 100) 0 0 0 bmPath) ∧
      ∀ s t, 0 ≤ s → s ≤ t →
        gaussSeq[natPi 1 1 (1 / 20) (1 / 2) (1 / 100) 5 (-2 / 100) 0 0 0 bmPath t |
          bmFiltrationReal bmPath measurable_bmPath s] =ᵐ[gaussSeq] fun ω =>
          wPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 t + Real.exp (-(lamb (1 / 20) 1 1 * (t - s))) *
            (natPi 1 1 (1 / 20) (1 / 2) (1 / 100) 5 (-2 / 100) 0 0 0 bmPath s ω -
              wPi 1 1 (1 / 20) 5 (-2 / 100) 0 0 s) +
          natD 1 1 (1 / 20) (1 / 2) * natK (lamb (1 / 20) 1 1) (1 / 2) (t - s) *
            ouProc (1 / 2) 0 0 (1 / 100) bmPath s ω := by
  have := isProbabilityMeasure_gaussSeq
  have hB := isPreBrownianReal_bmPath
  have hη : (0 : ℝ) < 1 / 2 := by norm_num
  refine ⟨bddL2_natPi hB measurable_bmPath continuous_bmPath bmPath_zero one_pos one_pos hη
      _ _ _ _ _ _, bddL2_natX hB measurable_bmPath continuous_bmPath bmPath_zero one_pos one_pos
      hη _ _ _ _ _ _, fun s t hs hst => ?_⟩
  exact condExp_pi_nat one_pos one_pos hη.le
    (regular_ouProc measurable_bmPath continuous_bmPath (1 / 2) 0 0 (1 / 100))
    (bddL1_ou hB measurable_bmPath continuous_bmPath bmPath_zero hη _)
    (expDrift_ou hB measurable_bmPath continuous_bmPath _ _)
    (regular_natX measurable_bmPath continuous_bmPath one_pos one_pos _ _ _ _ _ _ _)
    (bddL1_natX hB measurable_bmPath continuous_bmPath bmPath_zero one_pos one_pos hη
      (ρ := 1 / 20) _ _ _ _ _ _)
    (regular_natPi measurable_bmPath continuous_bmPath one_pos one_pos _ _ _ _ _ _ _)
    (bddL1_natPi hB measurable_bmPath continuous_bmPath bmPath_zero one_pos one_pos hη
      (ρ := 1 / 20) _ _ _ _ _ _)
    (isStochEqm_nat hB measurable_bmPath continuous_bmPath one_pos one_pos hη.le _ _ _ _ _ _)
    hs hst

end Cochrane.ZeroBound.TidyR8StochWerningNaturalMean
