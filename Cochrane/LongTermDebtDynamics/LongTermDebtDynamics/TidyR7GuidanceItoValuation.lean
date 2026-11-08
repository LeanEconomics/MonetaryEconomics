/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR7GuidanceSDF
import LongTermDebtDynamics.ForwardGuidance

/-!
# The continuous-time forward-guidance formula under uncertainty

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.2.1, p. 561:
with the geometric maturity structure `B_0^{(j)} = ϖ e^{−ϖj} B_0` and the announcement at date
`0` that the rate, `r` until `T`, is `i` from `T` on, the valuation equation
`ϖ [∫_0^T e^{−rj}e^{−ϖj} dj + ∫_T^∞ e^{−rT−i(j−T)}e^{−ϖj} dj] B_0/P_0 = s/r`
gives `P_0/P − 1 = e^{−(r+ϖ)T}((r+ϖ)/(i+ϖ) − 1)` (`ForwardGuidance.cfg_jump`).

Here the economy is stochastic. The nominal discount factor `Λ` follows
`dΛ = −i_t Λ dt + H dW` (one Brownian motion, `TidyR7GuidanceSDF.SDFPiece` on `[0, T]` and on
every `[T, t]`), so the price level, inflation and the surpluses `s` are random. The debt is
valued by `E_0 ∫_0^∞ Λ_j B_0^{(j)} dj / Λ_0` and the surpluses by
`E_0 ∫_0^∞ e^{−rj} s_j dj` (the book's `E_t ∫`).

## Main results

* `condExp_guidance`, `bondPrice_guidance`: with the announced path known (`r` before `T`,
  `i` after), `E_0 Λ_j = e^{−(r min(j,T) + i max(j−T,0))} Λ_0`: the bond prices are the
  deterministic ones of the book, `ϖe^{−ϖj}Q_0^{(j)} = ForwardGuidance.cfgIntegrand`.
* `condExp_debtValue`: **the interchange `E_0 ∫_0^∞ = ∫_0^∞ E_0`**:
  `E_0 ∫_0^∞ ϖe^{−ϖj} Λ_j dj = Λ_0 · ForwardGuidance.cfgValue r i ϖ T` a.s.;
  `debtValue_guidance`: the value of the debt per unit is `cfgValue`, state by state.
* `guidance_jump_ito`: **the book's formula holds verbatim, state by state**: with the same
  random surpluses and debt, the price level with guidance against the price level without,
  `P_0/P_0' − 1 = cfgJump r i ϖ T` a.s., whatever the diffusion of `Λ` (inflation risk) and
  of the surpluses. No covariation correction arises because the bond prices are deterministic.
* Random future rates (news at `T`: the rate from `T` on, `ι`, is known only at `T`, finitely
  many values): `condExp_debtValue_random`:
  `E_0 ∫ ϖe^{−ϖj}Λ_j dj = E_0[e^{rT} Λ_T cfgValue r ι ϖ T]`, and `random_jump_ito`:
  **`P_0/P_0' − 1 = E_0[e^{rT} Λ_T cfgJump r ι ϖ T]/Λ_0`**: the deterministic jump averaged
  under the `T`-forward measure `e^{rT}Λ_T/Λ_0`, not the jump at the expected rate. The
  counterexamples on the constructed Brownian motion are in TidyR7GuidanceItoBM.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR7GuidanceItoValuation

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.LongTermDebtDynamics.TidyR7BrownianTools
  Cochrane.LongTermDebtDynamics.TidyR7BrownianQV Cochrane.LongTermDebtDynamics.TidyR7ItoIntegral
  Cochrane.LongTermDebtDynamics.TidyR7GuidanceSDF Cochrane.LongTermDebtDynamics.ForwardGuidance
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → ℝ}

variable (P 𝓕 W) (Λ H K : ℝ → Ω → ℝ) (r : ℝ) (ι : Ω → ℝ) (T : ℝ)

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561 (under uncertainty): the nominal
discount factor under the announcement.** The short rate is `r` on `[0, T]` and `ι` on
`[T, ∞)`: `dΛ = −rΛ dt + H dW` on `[0, T]` and `dΛ = −ιΛ dt + K dW` on every `[T, t]`. The
post-`T` rate `ι` is known at `T` (it is a deterministic `i` for the book's announcement, see
`condExp_guidance`; random rates are news revealed at `T`). -/
structure GuidanceSDF where
  pre : ∃ C, SDFPiece P 𝓕 W Λ H (fun _ => r) 0 T C
  post : ∀ t, T ≤ t → ∃ C, SDFPiece P 𝓕 W Λ K ι T t C

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561 (under uncertainty): the market value of
the geometric debt portfolio per unit of `B_0`, in nominal terms over `P_0`:
`E_0[∫_0^∞ ϖe^{−ϖj} Λ_j dj]/Λ_0` (the book's `ϖ ∫_0^∞ Q_0^{(j)} e^{−ϖj} dj`). -/
noncomputable def debtValue (ϖ : ℝ) : Ω → ℝ := fun ω =>
  P[fun ω' => ∫ j in Set.Ioi (0 : ℝ), ϖ * Real.exp (-ϖ * j) * Λ j ω' | 𝓕 0] ω / Λ 0 ω

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 559 (under uncertainty): the present value of
surpluses, `E_0 ∫_0^∞ e^{−rj} s_j dj`. -/
noncomputable def pvSurplus (s : ℝ → Ω → ℝ) : Ω → ℝ :=
  P[fun ω => ∫ j in Set.Ioi (0 : ℝ), Real.exp (-r * j) * s j ω | 𝓕 0]

variable {P 𝓕 W Λ H K r ι T}

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561 (under uncertainty): bond prices under
a known announced path.** With rate `r` before `T` and a deterministic `i` from `T` on,
`E[Λ_j | 𝓕_0] = e^{−(r min(j,T) + i max(j−T,0))} Λ_0` a.s. for every `j ≥ 0`. -/
theorem condExp_guidance (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hT : 0 ≤ T) {i : ℝ}
    (hΛ : GuidanceSDF P 𝓕 W Λ H K r (fun _ => i) T) {j : ℝ} (hj : 0 ≤ j) :
    P[Λ j | 𝓕 0] =ᵐ[P] fun ω => Real.exp (-(r * min j T + i * max (j - T) 0)) * Λ 0 ω := by
  obtain ⟨C, hpre⟩ := hΛ.pre
  rcases le_or_gt j T with hjT | hjT
  · have h := condExp_sdf_const hB hW h𝓕 le_rfl hpre ⟨hj, hjT⟩
    refine h.trans (ae_of_all _ fun ω => ?_)
    simp only [min_eq_left hjT, max_eq_right (sub_nonpos.2 hjT), mul_zero, add_zero, sub_zero]
    ring_nf
  · obtain ⟨C', hpost⟩ := hΛ.post j hjT.le
    have h1 := condExp_sdf_const hB hW h𝓕 hT hpost ⟨hjT.le, le_rfl⟩
    have h2 := condExp_sdf_const hB hW h𝓕 le_rfl hpre ⟨hT, le_rfl⟩
    have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
    have h3 := (condExp_condExp_of_le (μ := P) (f := Λ j) (𝓕.mono hT) (𝓕.le T)).symm
    have h4 : P[P[Λ j | 𝓕 T] | 𝓕 0] =ᵐ[P] P[(Real.exp (-i * (j - T))) • Λ T | 𝓕 0] :=
      condExp_congr_ae (h1.trans (ae_of_all _ fun ω => by simp [smul_eq_mul]))
    have h5 := condExp_smul (μ := P) (Real.exp (-i * (j - T))) (Λ T) (𝓕 0)
    filter_upwards [h3, h4, h5, h2] with ω e3 e4 e5 e2
    rw [e3, e4, e5, Pi.smul_apply, e2, smul_eq_mul, min_eq_right hjT.le,
      max_eq_left (sub_nonneg.2 hjT.le), ← mul_assoc, ← Real.exp_add]
    congr 2
    ring

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561 (under uncertainty): the book's bond
prices.** Under a known announced path, a.s. on `Λ_0 ≠ 0`, the date-0 price of the maturity-`j`
zero-coupon bond times the maturity density, `ϖe^{−ϖj} E_0[Λ_j]/Λ_0`, is the deterministic
integrand `ForwardGuidance.cfgIntegrand r i ϖ T j` of p. 561. -/
theorem bondPrice_guidance (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hT : 0 ≤ T) {i : ℝ}
    (hΛ : GuidanceSDF P 𝓕 W Λ H K r (fun _ => i) T) {j : ℝ} (hj : 0 ≤ j) (ϖ : ℝ) :
    ∀ᵐ ω ∂P, Λ 0 ω ≠ 0 →
      ϖ * Real.exp (-ϖ * j) * (P[Λ j | 𝓕 0] ω / Λ 0 ω) = cfgIntegrand r i ϖ T j := by
  filter_upwards [condExp_guidance hB hW h𝓕 hT hΛ hj] with ω hω h0
  rw [hω, mul_div_assoc, div_self h0, mul_one, cfgIntegrand]

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: joint integrability on `(0, ∞) × Ω`
restricts to `(0, ∞) × A`.
From Mathlib `Integrable.mono_measure` with `Measure.prod_restrict`. Compare
`TidyR7GuidanceSDF.SDFPiece.integrable_window`. -/
theorem integrable_restrict_prod [SFinite P] {F : ℝ → Ω → ℝ} {I : Set ℝ}
    (hF : Integrable (fun p : ℝ × Ω => F p.1 p.2) ((volume.restrict I).prod P)) (A : Set Ω) :
    Integrable (Function.uncurry F) ((volume.restrict I).prod (P.restrict A)) := by
  have h := hF
  rw [← Measure.restrict_univ (μ := P), Measure.prod_restrict] at h
  rw [Measure.prod_restrict]
  exact h.mono_measure (Measure.restrict_mono
    (Set.prod_mono subset_rfl (Set.subset_univ A)) le_rfl)

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561 (under uncertainty): the interchange
`E_0 ∫_0^∞ = ∫_0^∞ E_0` for the debt.** Under a known announced path, with `r + ϖ > 0`,
`i + ϖ > 0`, `T ≥ 0` and `(j, ω) ↦ ϖe^{−ϖj}Λ_j(ω)` integrable on `(0, ∞) × Ω`,
`E_0 ∫_0^∞ ϖe^{−ϖj} Λ_j dj = cfgValue r i ϖ T · Λ_0` a.s. (Fubini on test sets, then
`condExp_guidance` maturity by maturity and `ForwardGuidance.integral_cfg`). -/
theorem condExp_debtValue (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hT : 0 ≤ T) {i ϖ : ℝ}
    (hΛ : GuidanceSDF P 𝓕 W Λ H K r (fun _ => i) T) (hrv : 0 < r + ϖ) (hiv : 0 < i + ϖ)
    (hint : Integrable (fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * Λ p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod P)) :
    P[fun ω => ∫ j in Set.Ioi (0 : ℝ), ϖ * Real.exp (-ϖ * j) * Λ j ω | 𝓕 0] =ᵐ[P]
      fun ω => cfgValue r i ϖ T * Λ 0 ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨C, hpre⟩ := hΛ.pre
  have h0 : Integrable (Λ 0) P := hpre.integ_at 0 ⟨le_rfl, hT⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le 0) hint.integral_prod_right
    (fun _ _ _ => (h0.const_mul _).integrableOn) (fun A hA _ => ?_)
    (hpre.adapted.const_mul _).aestronglyMeasurable).symm
  have hA' : MeasurableSet A := 𝓕.le 0 A hA
  have hswap := integral_integral_swap (integrable_restrict_prod
    (F := fun j ω => ϖ * Real.exp (-ϖ * j) * Λ j ω) hint A)
  rw [← hswap, integral_const_mul]
  have hpt : ∀ j ∈ Set.Ioi (0 : ℝ), ∫ ω in A, ϖ * Real.exp (-ϖ * j) * Λ j ω ∂P =
      cfgIntegrand r i ϖ T j * ∫ ω in A, Λ 0 ω ∂P := by
    intro j hj
    have hj0 : (0 : ℝ) ≤ j := le_of_lt hj
    have hc := condExp_guidance hB hW h𝓕 hT hΛ hj0
    have hj1 : Integrable (Λ j) P := by
      rcases le_or_gt j T with hjT | hjT
      · exact hpre.integ_at j ⟨hj0, hjT⟩
      · obtain ⟨C', hpost⟩ := hΛ.post j hjT.le
        exact hpost.integ_at j ⟨hjT.le, le_rfl⟩
    rw [integral_const_mul, ← setIntegral_condExp (𝓕.le 0) hj1 hA,
      setIntegral_congr_ae hA' (ae_imp_of_ae_restrict (ae_restrict_of_ae hc)),
      integral_const_mul, cfgIntegrand]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_mul_const,
    integral_cfg hrv hiv hT]

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561 (under uncertainty): the value of the
debt is the book's.** Under the hypotheses of `condExp_debtValue`, a.s. on `Λ_0 ≠ 0` the value
per unit of debt is `debtValue = cfgValue r i ϖ T`, state by state. -/
theorem debtValue_guidance (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hT : 0 ≤ T) {i ϖ : ℝ}
    (hΛ : GuidanceSDF P 𝓕 W Λ H K r (fun _ => i) T) (hrv : 0 < r + ϖ) (hiv : 0 < i + ϖ)
    (hint : Integrable (fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * Λ p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod P)) :
    ∀ᵐ ω ∂P, Λ 0 ω ≠ 0 → debtValue P 𝓕 Λ ϖ ω = cfgValue r i ϖ T := by
  filter_upwards [condExp_debtValue hB hW h𝓕 hT hΛ hrv hiv hint] with ω hω h0
  rw [debtValue, hω, mul_div_assoc, div_self h0, mul_one]

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561, under uncertainty: the continuous
forward-guidance formula holds verbatim, state by state.** Two economies on the same
probability space with the same debt `B_0` and the same random surpluses `s`: `Λ` with the
announcement (rate `r` until `T`, `i` after) and `Λ'` without (`r` throughout), each with any
bounded diffusion. If the valuation equations `B_0/P_0 · debtValue = E_0 ∫ e^{−rj}s_j dj` hold,
then a.s. where `Λ_0, Λ'_0 ≠ 0` and the present value of surpluses is nonzero,
`P_0/P_0' − 1 = e^{−(r+ϖ)T}((r+ϖ)/(i+ϖ) − 1)` (`ForwardGuidance.cfgJump`). -/
theorem guidance_jump_ito (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hT : 0 ≤ T) {i ϖ : ℝ} (hϖ : 0 < ϖ)
    (hrv : 0 < r + ϖ) (hiv : 0 < i + ϖ) {Λ' H' K' s : ℝ → Ω → ℝ} {B0 P0 P0' : Ω → ℝ}
    (hΛ : GuidanceSDF P 𝓕 W Λ H K r (fun _ => i) T)
    (hint : Integrable (fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * Λ p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod P))
    (hΛ' : GuidanceSDF P 𝓕 W Λ' H' K' r (fun _ => r) T)
    (hint' : Integrable (fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * Λ' p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod P))
    (hP0 : ∀ ω, 0 < P0 ω) (hP0' : ∀ ω, 0 < P0' ω)
    (hval : ∀ᵐ ω ∂P, B0 ω / P0 ω * debtValue P 𝓕 Λ ϖ ω = pvSurplus P 𝓕 r s ω)
    (hval' : ∀ᵐ ω ∂P, B0 ω / P0' ω * debtValue P 𝓕 Λ' ϖ ω = pvSurplus P 𝓕 r s ω) :
    ∀ᵐ ω ∂P, Λ 0 ω ≠ 0 → Λ' 0 ω ≠ 0 → pvSurplus P 𝓕 r s ω ≠ 0 →
      P0 ω / P0' ω - 1 = cfgJump r i ϖ T := by
  filter_upwards [debtValue_guidance hB hW h𝓕 hT hΛ hrv hiv hint,
    debtValue_guidance hB hW h𝓕 hT hΛ' hrv hrv hint', hval, hval'] with ω e1 e2 v1 v2 h0 h0' hS
  rw [e1 h0] at v1
  rw [e2 h0'] at v2
  exact cfg_jump hrv hiv hϖ (hP0' ω) (hP0 ω) v2 v1 hS

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: a finite-valued measurable `ι`
decomposes a set integral, `∫_A f = Σ_{x ∈ S} ∫_{A ∩ {ι = x}} f`.
A specialisation of Mathlib `MeasureTheory.integral_biUnion_finset`. -/
theorem setIntegral_eq_sum_levels {S : Finset ℝ} (hS : ∀ ω, ι ω ∈ S) (hι : Measurable ι)
    {A : Set Ω} (hAm : MeasurableSet A) {f : Ω → ℝ} (hf : IntegrableOn f A P) :
    ∫ ω in A, f ω ∂P = ∑ x ∈ S, ∫ ω in A ∩ ι ⁻¹' {x}, f ω ∂P := by
  have hAU : A = ⋃ x ∈ S, A ∩ ι ⁻¹' {x} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      exists_prop]
    exact ⟨fun h => ⟨ι ω, hS ω, h, rfl⟩, fun ⟨_, _, h, _⟩ => h⟩
  have hdisj : (S : Set ℝ).Pairwise (Function.onFun Disjoint fun x => A ∩ ι ⁻¹' {x}) := by
    intro x _ y _ hxy
    refine Set.disjoint_left.2 fun ω h1 h2 => hxy ?_
    exact (Set.mem_singleton_iff.1 h1.2).symm.trans (Set.mem_singleton_iff.1 h2.2)
  conv_lhs => rw [hAU]
  rw [integral_biUnion_finset S (fun x _ => hAm.inter (hι (measurableSet_singleton x))) hdisj
    (fun x _ => hf.mono_set Set.inter_subset_left)]

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the valuation integrand of p. 561 is
integrable on `(0, ∞)` for `r + ϖ > 0`, `i + ϖ > 0`. -/
theorem integrableOn_cfgIntegrand {r i ϖ : ℝ} (T : ℝ) (hrv : 0 < r + ϖ) (hiv : 0 < i + ϖ) :
    IntegrableOn (cfgIntegrand r i ϖ T) (Set.Ioi 0) := by
  have h1 : IntegrableOn (fun j => |ϖ| * (Real.exp (-(r + ϖ) * j)
      + Real.exp ((i - r) * T) * Real.exp (-(i + ϖ) * j))) (Set.Ioi 0) :=
    ((integrableOn_exp_mul_Ioi (by linarith) 0).add
      ((integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _)).const_mul _
  refine h1.mono' (by unfold cfgIntegrand; fun_prop) (ae_of_all _ fun j => ?_)
  have e1 : 0 < Real.exp (-(r + ϖ) * j) := Real.exp_pos _
  have e2 : 0 < Real.exp ((i - r) * T) * Real.exp (-(i + ϖ) * j) := by positivity
  rw [cfgIntegrand, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos (-ϖ * j)),
    abs_of_pos (Real.exp_pos _), mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg ϖ)
  rcases le_or_gt j T with hjT | hjT
  · rw [min_eq_left hjT, max_eq_right (sub_nonpos.2 hjT)]
    have : -ϖ * j + -(r * j + i * 0) = -(r + ϖ) * j := by ring
    rw [this]
    linarith
  · rw [min_eq_right hjT.le, max_eq_left (sub_nonneg.2 hjT.le), ← Real.exp_add]
    have : -ϖ * j + -(r * T + i * (j - T)) = (i - r) * T + -(i + ϖ) * j := by ring
    rw [this]
    linarith

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 561: the jump and the value are related by
`cfgJump r x ϖ T + 1 = cfgValue r x ϖ T · (r+ϖ)/ϖ`. -/
theorem cfgJump_add_one {r x ϖ : ℝ} (T : ℝ) (hϖ : ϖ ≠ 0) (hrv : r + ϖ ≠ 0) (hxv : x + ϖ ≠ 0) :
    cfgJump r x ϖ T + 1 = cfgValue r x ϖ T * ((r + ϖ) / ϖ) := by
  rw [cfgJump, cfgValue]
  field_simp
  ring

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561, under uncertainty about the future
rate: the value of the debt.** The rate is `r` until `T` and `ι` from `T` on, `ι` revealed at
`T` (finitely many values, `ι + ϖ > 0`). Then
`E_0 ∫_0^∞ ϖe^{−ϖj} Λ_j dj = E_0[e^{rT} Λ_T · cfgValue r ι ϖ T]` a.s.: the book's value at the
realised rate, weighted by the discount factor at the news date. -/
theorem condExp_debtValue_random (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hT : 0 ≤ T) {ϖ : ℝ} (hΛ : GuidanceSDF P 𝓕 W Λ H K r ι T)
    (hrv : 0 < r + ϖ) (hiv : ∀ ω, 0 < ι ω + ϖ)
    (hint : Integrable (fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * Λ p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod P)) :
    P[fun ω => ∫ j in Set.Ioi (0 : ℝ), ϖ * Real.exp (-ϖ * j) * Λ j ω | 𝓕 0] =ᵐ[P]
      P[fun ω => Real.exp (r * T) * Λ T ω * cfgValue r (ι ω) ϖ T | 𝓕 0] := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨C, hpre⟩ := hΛ.pre
  obtain ⟨C0, hT0⟩ := hΛ.post T le_rfl
  obtain ⟨S, hS⟩ := hT0.rate_finite
  set S' : Finset ℝ := S.filter fun x => 0 < x + ϖ with hS'def
  have hS' : ∀ ω, ι ω ∈ S' := fun ω => Finset.mem_filter.2 ⟨hS ω, hiv ω⟩
  have hιm : Measurable ι := (hT0.rate.mono (𝓕.le T)).measurable
  have hΛT : Integrable (Λ T) P := hT0.integ_at T ⟨le_rfl, le_rfl⟩
  have hvm : Measurable fun x : ℝ => cfgValue r x ϖ T := by unfold cfgValue; fun_prop
  set M : ℝ := ∑ x ∈ S, |cfgValue r x ϖ T| with hM
  have hYint : Integrable (fun ω => Real.exp (r * T) * Λ T ω * cfgValue r (ι ω) ϖ T) P := by
    have h := (hΛT.const_mul (Real.exp (r * T))).bdd_mul (c := M)
      (hvm.comp hιm).aestronglyMeasurable (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, hM]
        exact Finset.single_le_sum (f := fun x => |cfgValue r x ϖ T|)
          (fun x _ => abs_nonneg _) (hS ω))
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only [Function.comp_apply]
    ring
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le 0) hint.integral_prod_right
    (fun _ _ _ => integrable_condExp.integrableOn) (fun A hA _ => ?_)
    stronglyMeasurable_condExp.aestronglyMeasurable).symm
  have hA' : MeasurableSet A := 𝓕.le 0 A hA
  have hAT : MeasurableSet[𝓕 T] A := 𝓕.mono hT A hA
  have hBm : ∀ x, MeasurableSet[𝓕 T] (A ∩ ι ⁻¹' {x}) := fun x =>
    hAT.inter (hT0.rate.measurable (measurableSet_singleton x))
  have hBι : ∀ x, ∀ ω ∈ A ∩ ι ⁻¹' {x}, ι ω = x := fun x ω hω => Set.mem_singleton_iff.1 hω.2
  have hL : ∫ ω in A, Λ 0 ω ∂P =
      Real.exp (r * T) * ∑ x ∈ S', ∫ ω in A ∩ ι ⁻¹' {x}, Λ T ω ∂P := by
    have h1 := setIntegral_sdf hB hW h𝓕 le_rfl hpre hA (fun _ _ => rfl) ⟨hT, le_rfl⟩
    have h2 := setIntegral_eq_sum_levels hS' hιm hA' hΛT.integrableOn
    rw [h2, sub_zero] at h1
    rw [h1, ← mul_assoc, ← Real.exp_add]
    simp
  have hpt : ∀ j ∈ Set.Ioi (0 : ℝ), ∫ ω in A, ϖ * Real.exp (-ϖ * j) * Λ j ω ∂P =
      ∑ x ∈ S', Real.exp (r * T) * (∫ ω in A ∩ ι ⁻¹' {x}, Λ T ω ∂P)
        * cfgIntegrand r x ϖ T j := by
    intro j hj
    have hj0 : (0 : ℝ) ≤ j := le_of_lt hj
    rw [integral_const_mul]
    rcases le_or_gt j T with hjT | hjT
    · have h1 := setIntegral_sdf hB hW h𝓕 le_rfl hpre hA (fun _ _ => rfl) ⟨hj0, hjT⟩
      rw [h1, hL, sub_zero, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [cfgIntegrand, min_eq_left hjT, max_eq_right (sub_nonpos.2 hjT)]
      simp only [mul_zero, add_zero]
      ring_nf
    · obtain ⟨Cj, hpj⟩ := hΛ.post j hjT.le
      have hΛj : Integrable (Λ j) P := hpj.integ_at j ⟨hjT.le, le_rfl⟩
      rw [setIntegral_eq_sum_levels hS' hιm hA' hΛj.integrableOn, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [setIntegral_sdf hB hW h𝓕 hT hpj (hBm x) (hBι x) ⟨hjT.le, le_rfl⟩, cfgIntegrand,
        min_eq_right hjT.le, max_eq_left (sub_nonneg.2 hjT.le)]
      have e : Real.exp (-(r * T + x * (j - T))) =
          Real.exp (-(r * T)) * Real.exp (-x * (j - T)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [e]
      have e2 : Real.exp (r * T) * Real.exp (-(r * T)) = 1 := by
        rw [← Real.exp_add]; simp
      linear_combination (ϖ * Real.exp (-ϖ * j) * Real.exp (-x * (j - T))
        * ∫ ω in A ∩ ι ⁻¹' {x}, Λ T ω ∂P) * e2.symm
  rw [setIntegral_condExp (𝓕.le 0) hYint hA,
    ← integral_integral_swap (integrable_restrict_prod
      (F := fun j ω => ϖ * Real.exp (-ϖ * j) * Λ j ω) hint A),
    setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_finsetSum S' (fun x hx => ((integrableOn_cfgIntegrand T hrv
      (Finset.mem_filter.1 hx).2).const_mul _)),
    setIntegral_eq_sum_levels hS' hιm hA' hYint.integrableOn]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [integral_const_mul, integral_cfg hrv (Finset.mem_filter.1 hx).2 hT,
    setIntegral_congr_fun (𝓕.le T _ (hBm x))
      (g := fun ω => (Real.exp (r * T) * cfgValue r x ϖ T) * Λ T ω)
      (fun ω hω => by simp only [hBι x ω hω]; ring), integral_const_mul]
  ring

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 561, under uncertainty about the future
rate: the corrected forward-guidance formula.** As in `guidance_jump_ito`, but the rate from `T`
on is the news `ι`, revealed at `T` (finitely many values, `ι + ϖ > 0`). Then a.s. where
`Λ_0, Λ'_0 ≠ 0` and the present value of surpluses is nonzero,
`P_0/P_0' − 1 = E_0[e^{rT} Λ_T · cfgJump r ι ϖ T] / Λ_0`:
the deterministic jump at each realised rate, averaged with the weights `e^{rT}Λ_T/Λ_0` of the
`T`-forward measure (they have `E_0`-mean one). -/
theorem random_jump_ito (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hT : 0 ≤ T) {ϖ : ℝ} (hϖ : 0 < ϖ) (hrv : 0 < r + ϖ)
    (hiv : ∀ ω, 0 < ι ω + ϖ) {Λ' H' K' s : ℝ → Ω → ℝ} {B0 P0 P0' : Ω → ℝ}
    (hΛ : GuidanceSDF P 𝓕 W Λ H K r ι T)
    (hint : Integrable (fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * Λ p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod P))
    (hΛ' : GuidanceSDF P 𝓕 W Λ' H' K' r (fun _ => r) T)
    (hint' : Integrable (fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * Λ' p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod P))
    (hP0 : ∀ ω, 0 < P0 ω) (hP0' : ∀ ω, 0 < P0' ω)
    (hval : ∀ᵐ ω ∂P, B0 ω / P0 ω * debtValue P 𝓕 Λ ϖ ω = pvSurplus P 𝓕 r s ω)
    (hval' : ∀ᵐ ω ∂P, B0 ω / P0' ω * debtValue P 𝓕 Λ' ϖ ω = pvSurplus P 𝓕 r s ω) :
    ∀ᵐ ω ∂P, Λ 0 ω ≠ 0 → Λ' 0 ω ≠ 0 → pvSurplus P 𝓕 r s ω ≠ 0 →
      P0 ω / P0' ω - 1 =
        P[fun ω => Real.exp (r * T) * Λ T ω * cfgJump r (ι ω) ϖ T | 𝓕 0] ω / Λ 0 ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨C, hpre⟩ := hΛ.pre
  obtain ⟨C0, hT0⟩ := hΛ.post T le_rfl
  obtain ⟨S, hS⟩ := hT0.rate_finite
  have hιm : Measurable ι := (hT0.rate.mono (𝓕.le T)).measurable
  have hΛT : Integrable (Λ T) P := hT0.integ_at T ⟨le_rfl, le_rfl⟩
  have hjm : Measurable fun x : ℝ => cfgJump r x ϖ T := by unfold cfgJump; fun_prop
  set M : ℝ := ∑ x ∈ S, |cfgJump r x ϖ T| with hM
  have hZint : Integrable (fun ω => Real.exp (r * T) * Λ T ω * cfgJump r (ι ω) ϖ T) P := by
    have h := (hΛT.const_mul (Real.exp (r * T))).bdd_mul (c := M)
      (hjm.comp hιm).aestronglyMeasurable (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, hM]
        exact Finset.single_le_sum (f := fun x => |cfgJump r x ϖ T|)
          (fun x _ => abs_nonneg _) (hS ω))
    refine h.congr (ae_of_all _ fun ω => ?_)
    simp only [Function.comp_apply]
    ring
  have hΛTe : Integrable (fun ω => Real.exp (r * T) * Λ T ω) P := hΛT.const_mul _
  set k : ℝ := (r + ϖ) / ϖ with hk
  have hpt : (k • fun ω => Real.exp (r * T) * Λ T ω * cfgValue r (ι ω) ϖ T) =
      (fun ω => Real.exp (r * T) * Λ T ω * cfgJump r (ι ω) ϖ T)
        + fun ω => Real.exp (r * T) * Λ T ω := by
    funext ω
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    have e := cfgJump_add_one (r := r) (x := ι ω) T hϖ.ne' hrv.ne' (hiv ω).ne'
    rw [hk]
    linear_combination (-(Real.exp (r * T) * Λ T ω)) * e
  have hlin1 := condExp_smul (μ := P) k
    (fun ω => Real.exp (r * T) * Λ T ω * cfgValue r (ι ω) ϖ T) (𝓕 0)
  have hlin2 := condExp_add (m := 𝓕 0) hZint hΛTe
  have hlin3 := condExp_smul (μ := P) (Real.exp (r * T)) (Λ T) (𝓕 0)
  have hpreT := condExp_sdf_const hB hW h𝓕 le_rfl hpre ⟨hT, le_rfl⟩
  have hV := condExp_debtValue_random hB hW h𝓕 hT hΛ hrv hiv hint
  filter_upwards [hV, debtValue_guidance hB hW h𝓕 hT hΛ' hrv hrv hint', hval, hval', hlin1,
    hlin2, hlin3, hpreT] with ω e1 e2 v1 v2 l1 l2 l3 l4 h0 h0' hS0
  rw [e2 h0', cfgValue_same r ϖ T hrv] at v2
  rw [debtValue, e1] at v1
  rw [hpt] at l1
  have l3' : P[fun ω => Real.exp (r * T) * Λ T ω | 𝓕 0] ω = Real.exp (r * T) *
      (Real.exp (-r * (T - 0)) * Λ 0 ω) := by
    have e : (fun ω => Real.exp (r * T) * Λ T ω) = Real.exp (r * T) • Λ T := by
      funext ω; simp [smul_eq_mul]
    rw [e, l3, Pi.smul_apply, l4, smul_eq_mul]
  have l3'' : P[fun ω => Real.exp (r * T) * Λ T ω | 𝓕 0] ω = Λ 0 ω := by
    rw [l3', ← mul_assoc, ← Real.exp_add]
    simp
  rw [l2, Pi.add_apply, l3''] at l1
  rw [Pi.smul_apply, smul_eq_mul] at l1
  set Y := P[fun ω => Real.exp (r * T) * Λ T ω * cfgValue r (ι ω) ϖ T | 𝓕 0] ω with hY
  set Z := P[fun ω => Real.exp (r * T) * Λ T ω * cfgJump r (ι ω) ϖ T | 𝓕 0] ω with hZ
  have hB0 : B0 ω ≠ 0 := by
    intro hb
    rw [hb, zero_div, zero_mul] at v2
    exact hS0 v2.symm
  have hP := (hP0 ω).ne'
  have hP' := (hP0' ω).ne'
  have hrv' := hrv.ne'
  have hϖ' := hϖ.ne'
  rw [hk] at l1
  have heq : B0 ω * Y * (P0' ω * (r + ϖ)) = B0 ω * ϖ * (P0 ω * Λ 0 ω) := by
    have h := v1.trans v2.symm
    rw [div_mul_div_comm, div_mul_div_comm,
      div_eq_div_iff (mul_ne_zero hP h0) (mul_ne_zero hP' hrv')] at h
    linear_combination h
  have heq2 : Y * (P0' ω * (r + ϖ)) = ϖ * (P0 ω * Λ 0 ω) :=
    mul_left_cancel₀ hB0 (by linear_combination heq)
  have l1' : (r + ϖ) * Y = (Z + Λ 0 ω) * ϖ := by
    rw [div_mul_eq_mul_div, eq_div_iff hϖ'] at l1
    exact l1.symm
  rw [div_sub_one hP', div_eq_div_iff hP' h0]
  apply mul_left_cancel₀ hϖ'
  linear_combination (-1) * heq2 + P0' ω * l1'

end Cochrane.LongTermDebtDynamics.TidyR7GuidanceItoValuation
