/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR8GuidanceDateT

/-!
# The surplus side of the valuation equation: `E_t ∫ = ∫ E_t`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.2.1,
pp. 559–561: the right-hand side of the valuation equation at date `a`,
`E_a ∫_0^∞ e^{−rj} s_{a+j} dj` (`TidyR8GuidanceDateT.pvSurplusAt`), for random surpluses `s`
on a probability space with an arbitrary filtration `𝓕` (no Brownian structure is needed).

`E_a ∫ = ∫ E_a` needs care: `ω ↦ E[s_{a+j} | 𝓕_a](ω)` is defined only up to a null set for
each `j`, so `∫_0^∞ e^{−rj} E_a[s_{a+j}] dj` is meaningful only for a version jointly measurable
in `(j, ω)`. Two statements are proved.

## Main results

* `setIntegral_pvSurplusAt` (on test sets, no version needed): for `A ∈ 𝓕_a`,
  `∫_A E_a ∫_0^∞ e^{−rj}s_{a+j} dj dP = ∫_0^∞ e^{−rj} ∫_A E_a[s_{a+j}] dP dj`.
* `pvSurplusAt_interchange` (**a.s.**): if `m(j, ω)` is jointly measurable for
  `Borel ⊗ 𝓕_a` and `m_j = E_a[s_{a+j}]` a.s. for each `j > 0`, then
  `E_a ∫_0^∞ e^{−rj} s_{a+j} dj = ∫_0^∞ e^{−rj} m_j dj` a.s. The only other hypothesis is
  that the discounted surplus `(j, ω) ↦ e^{−rj}s_{a+j}(ω)` is integrable on `(0, ∞) × Ω`
  (`integrable_surplus_of_majorant`: implied by an integrable majorant); adaptedness of `s` is
  not needed.
* `valuation_interchanged_at` (**both sides interchanged**): under a known announced path,
  a.s. on `Λ_a ≠ 0`, `B_a/P_a · cfgValue r i ϖ τ = ∫_0^∞ e^{−rj} E_a[s_{a+j}] dj`, and
  `priceLevel_interchanged_at`: `P_a = B_a cfgValue r i ϖ τ / ∫_0^∞ e^{−rj} E_a[s_{a+j}] dj`.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR8SurplusInterchange

open MeasureTheory ProbabilityTheory Filter
open Cochrane.LongTermDebtDynamics.TidyR7BrownianTools
  Cochrane.LongTermDebtDynamics.TidyR7BrownianQV
  Cochrane.LongTermDebtDynamics.TidyR7GuidanceItoValuation
  Cochrane.LongTermDebtDynamics.TidyR8GuidanceDateT Cochrane.LongTermDebtDynamics.ForwardGuidance
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ mΩ}
  {r a : ℝ} {s : ℝ → Ω → ℝ}

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 559: **an integrable majorant.** If the
discounted surplus `e^{−rj}s_{a+j}(ω)` is a.e.-strongly measurable and dominated on
`(0, ∞) × Ω` by an integrable `G`, it is integrable there (Mathlib `Integrable.mono'`). -/
theorem integrable_surplus_of_majorant [IsFiniteMeasure P]
    (hsm : AEStronglyMeasurable (fun p : ℝ × Ω => Real.exp (-r * p.1) * s (a + p.1) p.2)
      ((volume.restrict (Set.Ioi 0)).prod P))
    {G : ℝ × Ω → ℝ} (hG : Integrable G ((volume.restrict (Set.Ioi 0)).prod P))
    (hle : ∀ j ∈ Set.Ioi (0 : ℝ), ∀ ω, |Real.exp (-r * j) * s (a + j) ω| ≤ G (j, ω)) :
    Integrable (fun p : ℝ × Ω => Real.exp (-r * p.1) * s (a + p.1) p.2)
      ((volume.restrict (Set.Ioi 0)).prod P) := by
  refine hG.mono' hsm ?_
  have hfst := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (ν := P)).ae (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [hfst] with p hp
  rw [Real.norm_eq_abs]
  exact hle p.1 hp p.2

/-- Cochrane (2023), Online Appendix §A1.2.1, p. 559: if the discounted surplus is integrable
on `(0, ∞) × Ω`, then `s_{a+j}` is integrable for almost every maturity `j > 0`.
The first component of Mathlib `integrable_prod_iff`. -/
theorem ae_integrable_surplus [IsFiniteMeasure P]
    (hint : Integrable (fun p : ℝ × Ω => Real.exp (-r * p.1) * s (a + p.1) p.2)
      ((volume.restrict (Set.Ioi 0)).prod P)) :
    ∀ᵐ j ∂(volume.restrict (Set.Ioi (0 : ℝ))), Integrable (s (a + j)) P := by
  filter_upwards [((integrable_prod_iff hint.aestronglyMeasurable).1 hint).1] with j hj
  refine (hj.const_mul (Real.exp (r * j))).congr (ae_of_all _ fun ω => ?_)
  change Real.exp (r * j) * (Real.exp (-r * j) * s (a + j) ω) = s (a + j) ω
  rw [← mul_assoc, ← Real.exp_add]
  have e : r * j + -r * j = 0 := by ring
  rw [e, Real.exp_zero, one_mul]

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 559 (under uncertainty): `E_a ∫ = ∫ E_a`
for the surpluses, on test sets.** If `(j, ω) ↦ e^{−rj}s_{a+j}(ω)` is integrable on
`(0, ∞) × Ω`, then for every `A ∈ 𝓕_a`,
`∫_A E_a[∫_0^∞ e^{−rj}s_{a+j} dj] dP = ∫_0^∞ e^{−rj} (∫_A E_a[s_{a+j}] dP) dj`
(Fubini, then the defining property of `E_a` maturity by maturity). -/
theorem setIntegral_pvSurplusAt [IsFiniteMeasure P]
    (hint : Integrable (fun p : ℝ × Ω => Real.exp (-r * p.1) * s (a + p.1) p.2)
      ((volume.restrict (Set.Ioi 0)).prod P)) {A : Set Ω} (hA : MeasurableSet[𝓕 a] A) :
    ∫ ω in A, pvSurplusAt P 𝓕 r a s ω ∂P =
      ∫ j in Set.Ioi (0 : ℝ), Real.exp (-r * j) * ∫ ω in A, P[s (a + j) | 𝓕 a] ω ∂P := by
  rw [pvSurplusAt, setIntegral_condExp (𝓕.le a) hint.integral_prod_right hA,
    ← integral_integral_swap (integrable_restrict_prod
      (F := fun j ω => Real.exp (-r * j) * s (a + j) ω) hint A)]
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  filter_upwards [ae_imp_of_ae_restrict (ae_integrable_surplus hint)] with j hj hj0
  rw [integral_const_mul, setIntegral_condExp (𝓕.le a) (hj hj0) hA]

/-- **Cochrane (2023), Online Appendix §A1.2.1, p. 559 (under uncertainty): the interchange
`E_a ∫_0^∞ e^{−rj} s_{a+j} dj = ∫_0^∞ e^{−rj} E_a[s_{a+j}] dj` almost surely.** Let the
discounted surplus be integrable on `(0, ∞) × Ω` and let `m` be a version of the conditional
expectations, `m_j = E[s_{a+j} | 𝓕_a]` a.s. for each `j > 0`, that is jointly measurable for
`Borel ⊗ 𝓕_a`. Then `pvSurplusAt = ∫_0^∞ e^{−rj} m_j dj` a.s. -/
theorem pvSurplusAt_interchange [IsFiniteMeasure P]
    (hint : Integrable (fun p : ℝ × Ω => Real.exp (-r * p.1) * s (a + p.1) p.2)
      ((volume.restrict (Set.Ioi 0)).prod P)) {m : ℝ → Ω → ℝ}
    (hm : StronglyMeasurable[@Prod.instMeasurableSpace ℝ Ω _ (𝓕 a)] (Function.uncurry m))
    (hver : ∀ j ∈ Set.Ioi (0 : ℝ), m j =ᵐ[P] P[s (a + j) | 𝓕 a]) :
    pvSurplusAt P 𝓕 r a s =ᵐ[P]
      fun ω => ∫ j in Set.Ioi (0 : ℝ), Real.exp (-r * j) * m j ω := by
  have hm1 : StronglyMeasurable[@Prod.instMeasurableSpace ℝ Ω _ (𝓕 a)]
      (Function.uncurry fun j ω => Real.exp (-r * j) * m j ω) := by
    have he : StronglyMeasurable[@Prod.instMeasurableSpace ℝ Ω _ (𝓕 a)]
        (fun p : ℝ × Ω => Real.exp (-r * p.1)) :=
      (Real.continuous_exp.measurable.comp
        (measurable_const.mul (@measurable_fst ℝ Ω _ (𝓕 a)))).stronglyMeasurable
    exact he.mul hm
  have hle : @Prod.instMeasurableSpace ℝ Ω _ (𝓕 a) ≤ Prod.instMeasurableSpace :=
    sup_le_sup_left (MeasurableSpace.comap_mono (𝓕.le a)) _
  have hm2 : StronglyMeasurable (Function.uncurry fun j ω => Real.exp (-r * j) * m j ω) :=
    hm1.mono hle
  have hmint : Integrable (fun p : ℝ × Ω => Real.exp (-r * p.1) * m p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod P) := by
    refine (integrable_prod_iff hm2.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with j hj
      change Integrable (fun ω => Real.exp (-r * j) * m j ω) P
      exact (integrable_condExp.congr (hver j hj).symm).const_mul (Real.exp (-r * j))
    · have h2 := ((integrable_prod_iff hint.aestronglyMeasurable).1 hint).2
      refine h2.mono' hm2.norm.integral_prod_right'.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with j hj
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      change ∫ ω, ‖Real.exp (-r * j) * m j ω‖ ∂P ≤ ∫ ω, ‖Real.exp (-r * j) * s (a + j) ω‖ ∂P
      have e1 : ∀ x : ℝ, ‖Real.exp (-r * j) * x‖ = Real.exp (-r * j) * |x| := fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      simp_rw [e1]
      rw [integral_const_mul, integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      rw [integral_congr_ae ((hver j hj).mono fun ω hω => by rw [hω])]
      exact integral_abs_condExp_le _
  have hg : StronglyMeasurable[𝓕 a]
      (fun ω => ∫ j in Set.Ioi (0 : ℝ), Real.exp (-r * j) * m j ω) :=
    @StronglyMeasurable.integral_prod_left ℝ Ω ℝ _ (𝓕 a) (volume.restrict (Set.Ioi 0)) _ _ _
      (fun j ω => Real.exp (-r * j) * m j ω) hm1
  rw [pvSurplusAt]
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le a) hint.integral_prod_right
    (fun _ _ _ => hmint.integral_prod_right.integrableOn) (fun A hA _ => ?_)
    hg.aestronglyMeasurable).symm
  have hA' : MeasurableSet A := 𝓕.le a A hA
  rw [← integral_integral_swap (integrable_restrict_prod
      (F := fun j ω => Real.exp (-r * j) * m j ω) hmint A),
    ← integral_integral_swap (integrable_restrict_prod
      (F := fun j ω => Real.exp (-r * j) * s (a + j) ω) hint A)]
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  filter_upwards [ae_imp_of_ae_restrict (ae_integrable_surplus hint)] with j hj hj0
  rw [integral_const_mul, integral_const_mul,
    setIntegral_congr_ae hA' ((hver j hj0).mono fun ω hω _ => hω),
    setIntegral_condExp (𝓕.le a) (hj hj0) hA]

variable {W : ℝ≥0 → Ω → ℝ}

/-- **Cochrane (2023), Online Appendix §A1.2.1, pp. 559–561 (under uncertainty): the
valuation equation at date `a` with both sides interchanged.** Under a known announced path
from `a` (`r` on `[a, a + τ]`, `i` after; `r + ϖ > 0`, `i + ϖ > 0`, `a, τ ≥ 0`), with the
debt payoffs and the discounted surpluses integrable on `(0, ∞) × Ω` and `m` a
`Borel ⊗ 𝓕_a`-measurable version of `E_a[s_{a+j}]`: if
`B_a/P_a · debtValueAt = E_a ∫ e^{−rj}s_{a+j} dj` a.s. on `Λ_a ≠ 0`, then a.s. on `Λ_a ≠ 0`,
`B_a/P_a · cfgValue r i ϖ τ = ∫_0^∞ e^{−rj} m_j dj`: the book's
`∫_0^∞ Q_a^{(a+j)}B_a^{(a+j)} dj/P_a = ∫_0^∞ e^{−rj}E_a s_{a+j} dj` with the deterministic bond
prices of the announcement. -/
theorem valuation_interchanged_at (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (ha : 0 ≤ a) {τ i ϖ : ℝ} (hτ : 0 ≤ τ) {Λ H K : ℝ → Ω → ℝ}
    (hΛ : GuidanceSDFAt P 𝓕 W Λ H K r (fun _ => i) a τ) (hrv : 0 < r + ϖ) (hiv : 0 < i + ϖ)
    (hintD : Integrable (fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * Λ (a + p.1) p.2)
      ((volume.restrict (Set.Ioi 0)).prod P))
    (hint : Integrable (fun p : ℝ × Ω => Real.exp (-r * p.1) * s (a + p.1) p.2)
      ((volume.restrict (Set.Ioi 0)).prod P)) {m : ℝ → Ω → ℝ}
    (hm : StronglyMeasurable[@Prod.instMeasurableSpace ℝ Ω _ (𝓕 a)] (Function.uncurry m))
    (hver : ∀ j ∈ Set.Ioi (0 : ℝ), m j =ᵐ[P] P[s (a + j) | 𝓕 a]) {B Pa : Ω → ℝ}
    (hval : ∀ᵐ ω ∂P, Λ a ω ≠ 0 →
      B ω / Pa ω * debtValueAt P 𝓕 Λ a ϖ ω = pvSurplusAt P 𝓕 r a s ω) :
    ∀ᵐ ω ∂P, Λ a ω ≠ 0 →
      B ω / Pa ω * cfgValue r i ϖ τ = ∫ j in Set.Ioi (0 : ℝ), Real.exp (-r * j) * m j ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  filter_upwards [debtValueAt_guidance hB hW h𝓕 ha hτ hΛ hrv hiv hintD,
    pvSurplusAt_interchange hint hm hver, hval] with ω e1 e2 v h0
  rw [← e1 h0, ← e2]
  exact v h0

/-- **Cochrane (2023), Online Appendix §A1.2.1, pp. 559–561 (under uncertainty): the price
level at the announcement date.** Under the hypotheses of `valuation_interchanged_at`, a.s.
where `Λ_a ≠ 0`, `P_a ≠ 0` and the present value of surpluses is nonzero,
`P_a = B_a · cfgValue r i ϖ τ / ∫_0^∞ e^{−rj} E_a[s_{a+j}] dj`. -/
theorem priceLevel_interchanged_at (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (ha : 0 ≤ a) {τ i ϖ : ℝ} (hτ : 0 ≤ τ) {Λ H K : ℝ → Ω → ℝ}
    (hΛ : GuidanceSDFAt P 𝓕 W Λ H K r (fun _ => i) a τ) (hrv : 0 < r + ϖ) (hiv : 0 < i + ϖ)
    (hintD : Integrable (fun p : ℝ × Ω => ϖ * Real.exp (-ϖ * p.1) * Λ (a + p.1) p.2)
      ((volume.restrict (Set.Ioi 0)).prod P))
    (hint : Integrable (fun p : ℝ × Ω => Real.exp (-r * p.1) * s (a + p.1) p.2)
      ((volume.restrict (Set.Ioi 0)).prod P)) {m : ℝ → Ω → ℝ}
    (hm : StronglyMeasurable[@Prod.instMeasurableSpace ℝ Ω _ (𝓕 a)] (Function.uncurry m))
    (hver : ∀ j ∈ Set.Ioi (0 : ℝ), m j =ᵐ[P] P[s (a + j) | 𝓕 a]) {B Pa : Ω → ℝ}
    (hval : ∀ᵐ ω ∂P, Λ a ω ≠ 0 →
      B ω / Pa ω * debtValueAt P 𝓕 Λ a ϖ ω = pvSurplusAt P 𝓕 r a s ω) :
    ∀ᵐ ω ∂P, Λ a ω ≠ 0 → Pa ω ≠ 0 →
      (∫ j in Set.Ioi (0 : ℝ), Real.exp (-r * j) * m j ω) ≠ 0 →
      Pa ω = B ω * cfgValue r i ϖ τ / ∫ j in Set.Ioi (0 : ℝ), Real.exp (-r * j) * m j ω := by
  filter_upwards [valuation_interchanged_at hB hW h𝓕 ha hτ hΛ hrv hiv hintD hint hm hver
    hval] with ω h h0 hP hI
  rw [eq_div_iff hI, ← h h0]
  field_simp

end Cochrane.LongTermDebtDynamics.TidyR8SurplusInterchange
