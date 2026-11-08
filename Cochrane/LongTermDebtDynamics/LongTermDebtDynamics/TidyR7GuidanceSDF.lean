/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR7ItoProductRule
import Mathlib.Analysis.ODE.ExistUnique

/-!
# The nominal discount factor with a known short rate: `E_s Λ_u = e^{−c(u−s)} Λ_s`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.2.1, pp. 559–561
(the continuous-time valuation equation `∫_0^∞ Q_t^{(t+j)} B_t^{(t+j)} dj / P_t =
E_t ∫_0^∞ e^{−rj} s_{t+j} dj` and the forward-guidance formula of p. 561), under uncertainty.

In continuous time a zero-coupon bond paying one dollar at `u` is worth
`Q_s^{(u)} = E_s[Λ_u]/Λ_s`, where `Λ` is the nominal stochastic discount factor
(`Λ_t = e^{−rt}/P_t` with the book's constant real rate `r`). The short rate `i` is the expected
rate of decline of `Λ`: `dΛ = −i Λ dt + H dW` for one Brownian motion `W`. With the book's rate
path known in advance, `i` is constant on each piece of the path. This module proves, with the
Itô integral of the Cochrane Monetarism project (copied into this project, see
`TidyR7ItoIntegral.itoInt`), that then `E_s Λ_u = e^{−c(u−s)} Λ_s`, whatever the diffusion `H`,
and also when the rate `c` on the piece is random but known at `s` (finitely many values: the
jump-at-news-date structure of the discrete version, TidyR5GuidanceUncertainty).

## Setting

`SDFPiece P 𝓕 W Λ H c s t C`: on `[s, t]`, for each `u`, almost surely
`Λ_u = Λ_s − c ∫_s^u Λ_v dv + ∫_s^u H dW`, with `c` an `𝓕_s`-measurable rate taking finitely
many values, `H` a bounded admissible integrand (`TidyR7ItoIntegral.ItoIntegrand`), `Λ_s`
`𝓕_s`-measurable, every `Λ_u` integrable and `(u, ω) ↦ Λ_u(ω)` integrable on `(s, t] × Ω`.
The drift `−cΛ` need NOT be bounded (`Λ = e^{−ru}(1 + κW_u)` is allowed): the time integral is
pathwise and the proof does not use the product rule.

## Main results

* `setIntegral_itoInt_eq_zero`: `∫_A ∫_s^u H dW = 0` for `A ∈ 𝓕_s`.
* `setIntegral_eq_sub_integral` (**`E_s ∫ = ∫ E_s` on test sets**, by Fubini):
  `∫_A Λ_u = ∫_A Λ_s − c ∫_s^u (∫_A Λ_v) dv` when `c` is constant on `A ∈ 𝓕_s`.
* `setIntegral_sdf` (the linear integral equation solved, by ODE uniqueness):
  `∫_A Λ_u = e^{−c(u−s)} ∫_A Λ_s`.
* `condExp_sdf`: **`E[Λ_u | 𝓕_s] = e^{−c(u−s)} Λ_s` a.s.** for a random rate known at `s`;
  `condExp_sdf_const`: the deterministic-rate case.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR7GuidanceSDF

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.LongTermDebtDynamics.TidyR7BrownianTools
  Cochrane.LongTermDebtDynamics.TidyR7BrownianQV Cochrane.LongTermDebtDynamics.TidyR7ItoL2
  Cochrane.LongTermDebtDynamics.TidyR7ItoIntegral
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → ℝ}

variable (P 𝓕 W) (Λ H : ℝ → Ω → ℝ) (c : Ω → ℝ) (s t C : ℝ)

/-- **Cochrane (2023), Online Appendix §A1.2.1, pp. 559–561 (under uncertainty): the nominal
discount factor on a piece `[s, t]` of the rate path.** The rate `c` is known at `s` and takes
finitely many values; almost surely `Λ_u = Λ_s − c ∫_s^u Λ_v dv + ∫_s^u H dW` for each
`u ∈ [s, t]` (that is, `dΛ = −cΛ dt + H dW`), `H` is a bounded admissible integrand, and `Λ` is
integrable at each date and jointly on `(s, t] × Ω`. -/
structure SDFPiece where
  adapted : StronglyMeasurable[𝓕 s] (Λ s)
  rate : StronglyMeasurable[𝓕 s] c
  rate_finite : ∃ S : Finset ℝ, ∀ ω, c ω ∈ S
  integ : Integrable (fun p : ℝ × Ω => Λ p.1 p.2) ((volume.restrict (Set.Ioc s t)).prod P)
  integ_at : ∀ u ∈ Set.Icc s t, Integrable (Λ u) P
  diff : ItoIntegrand P 𝓕 H s t C
  eq : ∀ u ∈ Set.Icc s t, Λ u =ᵐ[P] fun ω => Λ s ω - c ω * (∫ v in s..u, Λ v ω)
    + itoInt P 𝓕 W H s u ω

variable {P 𝓕 W Λ H c s t C}

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561 (under uncertainty): the Itô integral has
mean zero on every event known at its start, `∫_A ∫_s^u H dW dP = 0` for `A ∈ 𝓕_s`.
The case `G = 1_A` of `TidyR7ItoIntegral.integral_mul_itoInt`. -/
theorem setIntegral_itoInt_eq_zero (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {u : ℝ} (hH : ItoIntegrand P 𝓕 H s u C)
    {A : Set Ω} (hA : MeasurableSet[𝓕 s] A) :
    ∫ ω in A, itoInt P 𝓕 W H s u ω ∂P = 0 := by
  have h := integral_mul_itoInt hB hW h𝓕 hs hH (G := A.indicator fun _ => (1 : ℝ))
    (stronglyMeasurable_const.indicator hA) (CG := 1)
    (fun ω => by by_cases h : ω ∈ A <;> simp [h])
  rwa [integral_indicator_one_mul (𝓕.le s A hA)] at h

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the joint integrability of `Λ` on
`(s, t] × Ω` restricts to `(s, u] × A` for `u ≤ t`.
From Mathlib `Integrable.mono_measure` with `Measure.prod_restrict`. -/
theorem SDFPiece.integrable_window [SFinite P] (hΛ : SDFPiece P 𝓕 W Λ H c s t C) {u : ℝ}
    (hut : u ≤ t) (A : Set Ω) :
    Integrable (Function.uncurry Λ) ((volume.restrict (Set.Ioc s u)).prod (P.restrict A)) := by
  have h := hΛ.integ
  rw [← Measure.restrict_univ (μ := P), Measure.prod_restrict] at h
  rw [Measure.prod_restrict]
  exact h.mono_measure (Measure.restrict_mono
    (Set.prod_mono (Set.Ioc_subset_Ioc_right hut) (Set.subset_univ A)) le_rfl)

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561 (under uncertainty): `E_s ∫ = ∫ E_s` on
test sets.** If the rate is `c₀` on `A ∈ 𝓕_s`, then for `u ∈ [s, t]`
`∫_A Λ_u = ∫_A Λ_s − c₀ ∫_s^u (∫_A Λ_v dP) dv` (Fubini for the drift, mean zero for the Itô
integral). -/
theorem setIntegral_eq_sub_integral (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hΛ : SDFPiece P 𝓕 W Λ H c s t C) {A : Set Ω}
    (hA : MeasurableSet[𝓕 s] A) {c₀ : ℝ} (hc : ∀ ω ∈ A, c ω = c₀) {u : ℝ}
    (hu : u ∈ Set.Icc s t) :
    ∫ ω in A, Λ u ω ∂P = ∫ ω in A, Λ s ω ∂P - c₀ * ∫ v in s..u, ∫ ω in A, Λ v ω ∂P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hA' : MeasurableSet A := 𝓕.le s A hA
  have hwin := hΛ.integrable_window hu.2 A
  have hI : Integrable (fun ω => ∫ v in s..u, Λ v ω) (P.restrict A) := by
    have h := hwin.integral_prod_right
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [intervalIntegral.integral_of_le hu.1]
  have hJ : Integrable (itoInt P 𝓕 W H s u) P :=
    (memLp_itoInt hB hW h𝓕 hs (hΛ.diff.mono le_rfl hu.2)).integrable one_le_two
  have hswap := intervalIntegral_integral_swap (μ := P.restrict A) (a := s) (b := u) (f := Λ)
    (by rw [Set.uIoc_of_le hu.1]; exact hwin)
  rw [integral_congr_ae (ae_restrict_of_ae (hΛ.eq u hu))]
  rw [setIntegral_congr_fun hA' (g := fun ω => Λ s ω - c₀ * (∫ v in s..u, Λ v ω)
    + itoInt P 𝓕 W H s u ω) (fun ω hω => by simp only [hc ω hω])]
  have h0 : Integrable (Λ s) (P.restrict A) :=
    (hΛ.integ_at s ⟨le_rfl, hu.1.trans hu.2⟩).integrableOn
  have hf : Integrable (fun ω => Λ s ω - c₀ * ∫ v in s..u, Λ v ω) (P.restrict A) :=
    h0.sub (hI.const_mul c₀)
  rw [integral_add hf hJ.integrableOn, integral_sub h0 (hI.const_mul c₀), integral_const_mul,
    setIntegral_itoInt_eq_zero hB hW h𝓕 hs (hΛ.diff.mono le_rfl hu.2) hA, hswap, add_zero]

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561 (under uncertainty): the expected
discount factor decays at the known rate.** If the rate is `c₀` on `A ∈ 𝓕_s`, then for every
`u ∈ [s, t]`, `∫_A Λ_u dP = e^{−c₀(u−s)} ∫_A Λ_s dP`. The function `g(u) = ∫_A Λ_u` solves
`g(u) = g(s) − c₀ ∫_s^u g`, hence is continuous, differentiable from the right with `g' = −c₀g`,
and ODE uniqueness (Mathlib `ODE_solution_unique_of_mem_Icc_right`) identifies it. -/
theorem setIntegral_sdf (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hΛ : SDFPiece P 𝓕 W Λ H c s t C) {A : Set Ω}
    (hA : MeasurableSet[𝓕 s] A) {c₀ : ℝ} (hc : ∀ ω ∈ A, c ω = c₀) {u : ℝ}
    (hu : u ∈ Set.Icc s t) :
    ∫ ω in A, Λ u ω ∂P = Real.exp (-c₀ * (u - s)) * ∫ ω in A, Λ s ω ∂P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set g : ℝ → ℝ := fun v => ∫ ω in A, Λ v ω ∂P with hg
  have hst : s ≤ t := hu.1.trans hu.2
  have heq : ∀ v ∈ Set.Icc s t, g v = g s - c₀ * ∫ x in s..v, g x := fun v hv =>
    setIntegral_eq_sub_integral hB hW h𝓕 hs hΛ hA hc hv
  have hgi : IntervalIntegrable g volume s t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
    exact (hΛ.integrable_window le_rfl A).integral_prod_left
  have hF : ContinuousOn (fun v => ∫ x in s..v, g x) (Set.Icc s t) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hgi Set.left_mem_uIcc
    rwa [Set.uIcc_of_le hst] at h
  have hgc : ContinuousOn g (Set.Icc s t) :=
    (continuousOn_const.sub (continuousOn_const.mul hF)).congr fun v hv => heq v hv
  have hgd : ∀ v ∈ Set.Ico s t, HasDerivWithinAt g (-c₀ * g v) (Set.Ici v) v := by
    intro v hv
    have hmem : Set.Icc s t ∈ 𝓝[Set.Ioi v] v :=
      mem_of_superset (Ioc_mem_nhdsGT hv.2) fun x hx => ⟨hv.1.trans hx.1.le, hx.2⟩
    have hd : HasDerivWithinAt (fun w => ∫ x in s..w, g x) (g v) (Set.Ici v) v :=
      intervalIntegral.integral_hasDerivWithinAt_right
        (hgi.mono_set (by rw [Set.uIcc_of_le hv.1, Set.uIcc_of_le hst]
                          exact Set.Icc_subset_Icc_right hv.2.le))
        ((hgc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc v).filter_mono
          (nhdsWithin_le_of_mem hmem))
        ((hgc v ⟨hv.1, hv.2.le⟩).mono_of_mem_nhdsWithin hmem)
    have hd2 := (hd.const_mul c₀).const_sub (g s)
    refine (hd2.congr_of_eventuallyEq ?_ (heq v ⟨hv.1, hv.2.le⟩)).congr_deriv ?_
    · filter_upwards [Ico_mem_nhdsGE hv.2] with w hw
      exact heq w ⟨hv.1.trans hw.1, hw.2.le⟩
    · rw [heq v ⟨hv.1, hv.2.le⟩]
      ring
  set φ : ℝ → ℝ := fun v => Real.exp (-c₀ * (v - s)) * g s with hφ
  have hφd : ∀ v, HasDerivAt φ (-c₀ * φ v) v := by
    intro v
    have h1 : HasDerivAt (fun v => -c₀ * (v - s)) (-c₀) v := by
      simpa using ((hasDerivAt_id v).sub_const s).const_mul (-c₀)
    have h2 := (h1.exp).mul_const (g s)
    refine h2.congr_deriv ?_
    simp only [hφ]
    ring
  have hlip : ∀ v ∈ Set.Ico s t,
      LipschitzOnWith ‖c₀‖₊ (fun x : ℝ => -c₀ * x) Set.univ := by
    intro _ _
    refine (LipschitzWith.of_dist_le_mul fun x y => ?_).lipschitzOnWith
    rw [Real.dist_eq, Real.dist_eq, coe_nnnorm, Real.norm_eq_abs, ← abs_mul]
    exact le_of_eq (by rw [← abs_neg]; congr 1; ring)
  have hE := ODE_solution_unique_of_mem_Icc_right (v := fun _ x => -c₀ * x)
    (s := fun _ => Set.univ) hlip hgc hgd (fun _ _ => Set.mem_univ _)
    (fun v _ => (hφd v).continuousAt.continuousWithinAt)
    (fun v _ => (hφd v).hasDerivWithinAt) (fun _ _ => Set.mem_univ _)
    (by simp [hφ]) hu
  simpa [hφ] using hE

/-- **Cochrane (2023), Online Appendix §A1.2.1, pp. 559–561 (under uncertainty): bond prices
with a rate known at `s`.** On a piece `[s, t]` with rate `c` known at `s` (finitely many
values), `E[Λ_u | 𝓕_s] = e^{−c(u−s)} Λ_s` a.s. for `u ∈ [s, t]`, whatever the diffusion `H`:
the zero-coupon price `Q_s^{(u)} = E_sΛ_u/Λ_s = e^{−c(u−s)}` is the perfect-foresight price. -/
theorem condExp_sdf (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hΛ : SDFPiece P 𝓕 W Λ H c s t C) {u : ℝ}
    (hu : u ∈ Set.Icc s t) :
    P[Λ u | 𝓕 s] =ᵐ[P] fun ω => Real.exp (-c ω * (u - s)) * Λ s ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨S, hS⟩ := hΛ.rate_finite
  have hs0 : Integrable (Λ s) P := hΛ.integ_at s ⟨le_rfl, hu.1.trans hu.2⟩
  have hcm : StronglyMeasurable[𝓕 s] (fun ω => Real.exp (-c ω * (u - s))) :=
    Real.continuous_exp.comp_stronglyMeasurable (hΛ.rate.neg.mul_const (u - s))
  set M : ℝ := ∑ x ∈ S, Real.exp (-x * (u - s)) with hM
  have hbd : ∀ ω, ‖Real.exp (-c ω * (u - s))‖ ≤ M := by
    intro ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hM]
    exact Finset.single_le_sum (f := fun x => Real.exp (-x * (u - s)))
      (fun x _ => (Real.exp_pos _).le) (hS ω)
  have hgi : Integrable (fun ω => Real.exp (-c ω * (u - s)) * Λ s ω) P :=
    hs0.bdd_mul (hcm.mono (𝓕.le s)).aestronglyMeasurable (ae_of_all _ hbd)
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hΛ.integ_at u hu)
    (fun _ _ _ => hgi.integrableOn) (fun A hA _ => ?_)
    (hcm.mul hΛ.adapted).aestronglyMeasurable).symm
  set B : ℝ → Set Ω := fun x => A ∩ c ⁻¹' {x} with hBdef
  have hBm : ∀ x, MeasurableSet[𝓕 s] (B x) := fun x =>
    hA.inter (hΛ.rate.measurable (measurableSet_singleton x))
  have hAU : A = ⋃ x ∈ S, B x := by
    ext ω
    simp only [hBdef, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, exists_prop]
    exact ⟨fun h => ⟨c ω, hS ω, h, rfl⟩, fun ⟨_, _, h, _⟩ => h⟩
  have hdisj : (S : Set ℝ).Pairwise (Function.onFun Disjoint B) := by
    intro x _ y _ hxy
    refine Set.disjoint_left.2 fun ω h1 h2 => hxy ?_
    exact (Set.mem_singleton_iff.1 h1.2).symm.trans (Set.mem_singleton_iff.1 h2.2)
  have hBm' : ∀ x ∈ S, MeasurableSet (B x) := fun x _ => 𝓕.le s _ (hBm x)
  rw [hAU, integral_biUnion_finset S hBm' hdisj (fun _ _ => hgi.integrableOn),
    integral_biUnion_finset S hBm' hdisj (fun _ _ => (hΛ.integ_at u hu).integrableOn)]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hcB : ∀ ω ∈ B x, c ω = x := fun ω hω => Set.mem_singleton_iff.1 hω.2
  rw [setIntegral_sdf hB hW h𝓕 hs hΛ (hBm x) hcB hu,
    setIntegral_congr_fun (hBm' x (by assumption))
      (g := fun ω => Real.exp (-x * (u - s)) * Λ s ω) (fun ω hω => by simp only [hcB ω hω]),
    integral_const_mul]

/-- **Cochrane (2023), Online Appendix §A1.2.1, pp. 559–561 (under uncertainty): a known
constant rate.** If `dΛ = −c₀Λ dt + H dW` on `[s, t]` with a deterministic rate `c₀`, then
`E[Λ_u | 𝓕_s] = e^{−c₀(u−s)} Λ_s` a.s.: bond prices are the deterministic `e^{−c₀(u−s)}`.
The constant-rate case of `condExp_sdf`. -/
theorem condExp_sdf_const (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {c₀ : ℝ}
    (hΛ : SDFPiece P 𝓕 W Λ H (fun _ => c₀) s t C) {u : ℝ} (hu : u ∈ Set.Icc s t) :
    P[Λ u | 𝓕 s] =ᵐ[P] fun ω => Real.exp (-c₀ * (u - s)) * Λ s ω :=
  condExp_sdf hB hW h𝓕 hs hΛ hu

end Cochrane.LongTermDebtDynamics.TidyR7GuidanceSDF
