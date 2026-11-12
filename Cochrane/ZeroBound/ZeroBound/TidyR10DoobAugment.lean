/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR10DoobVersion

/-!
# The completed filtration and an Itô integral with every path continuous

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for (1.32) with diffusive
bonds (Track 3, chunk B3, item 2). `TidyR10DoobVersion.exists_adapted_continuous_itoInt` is
adapted to `𝓕` with paths continuous outside a null set `N`. Setting the process to `0` on `N`
makes every path continuous, but `N` is only `𝓕_∞`-measurable, so the result is adapted to the
**`P`-completed filtration** `augment P 𝓕` (`𝓕_t` together with all sets a.e. equal to an
`𝓕_t`-set; Mathlib v4.34 has no completion of a filtration, only `Filtration.rightCont`).

## Main results

* `augment`, `le_augment`, `measurableSet_augment_of_null`,
  `stronglyMeasurable_augment_of_ae_eq` (a measurable `f` a.e. equal to an
  `augment P 𝓕 t`-measurable `g` is `augment P 𝓕 t`-measurable).
* `bmFiltration_augment`: the completed filtration of an admissible filtration is admissible.
* `condExp_augment`: `E[f | augment P 𝓕 t] = E[f | 𝓕_t]` a.e., so conditional statements for the
  completed filtration are statements for `𝓕`.
* `itoInt_augment`: `∫ H dW` for the completed filtration equals `∫ H dW` for `𝓕` a.e.
* `exists_continuous_itoInt_augment` (**item 2, every path**): `X` adapted to `augment P 𝓕`,
  `X_t = ∫_s^t H dW` a.s. for every `t`, EVERY path continuous on `ℝ`, `X = 0` on `(−∞, s]`,
  `X` a martingale for `augment P 𝓕`, and `E[sup_{[s,T]} X²] ≤ 4E[∫_s^T H²]` for every `T > s`.
-/

namespace Cochrane.ZeroBound.TidyR10DoobAugment

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.TidyR7StieltjesSums Cochrane.ZeroBound.TidyR7BrownianTools
  Cochrane.ZeroBound.TidyR7BrownianQV Cochrane.ZeroBound.TidyR7ItoL2
  Cochrane.ZeroBound.TidyR7ItoIntegral Cochrane.ZeroBound.TidyR7CondDominated
  Cochrane.ZeroBound.TidyR10DoobIto Cochrane.ZeroBound.TidyR10DoobVersion
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ mΩ}

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (tool): the `P`-completion of a sub-σ-algebra `m`
inside `mΩ`: the measurable sets a.e. equal to an `m`-measurable set.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobAugment.augSigma). -/
abbrev augSigma (P : Measure Ω) (m : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' A := MeasurableSet[mΩ] A ∧ ∃ B, MeasurableSet[m] B ∧ A =ᵐ[P] B
  measurableSet_empty := ⟨@MeasurableSet.empty _ mΩ, ∅, @MeasurableSet.empty _ m, EventuallyEq.rfl⟩
  measurableSet_compl A hA := by
    obtain ⟨hA1, B, hB, hAB⟩ := hA
    exact ⟨@MeasurableSet.compl _ _ mΩ hA1, Bᶜ, hB.compl, Filter.EventuallyEqSet.compl hAB⟩
  measurableSet_iUnion f hf := by
    choose hf1 B hB hfB using hf
    exact ⟨@MeasurableSet.iUnion _ _ mΩ _ _ hf1, ⋃ i, B i, MeasurableSet.iUnion hB,
      Filter.EventuallyEqSet.countable_iUnion hfB⟩

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (tool): **the `P`-completed filtration**
`t ↦ augSigma P (𝓕 t)`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobAugment.augment). -/
def augment (P : Measure Ω) (𝓕 : Filtration ℝ mΩ) : Filtration ℝ mΩ where
  seq t := augSigma P (𝓕 t)
  mono' i j hij A hA := by
    obtain ⟨hA1, B, hB, hAB⟩ := hA
    exact ⟨hA1, B, 𝓕.mono hij B hB, hAB⟩
  le' _ _ hA := hA.1

/-- Cochrane (2023), A1 §1.6, pp. 567–568: membership in the completed filtration.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobAugment.measurableSet_augment_iff). -/
theorem measurableSet_augment_iff {t : ℝ} {A : Set Ω} :
    MeasurableSet[augment P 𝓕 t] A ↔
      MeasurableSet[mΩ] A ∧ ∃ B, MeasurableSet[𝓕 t] B ∧ A =ᵐ[P] B :=
  Iff.rfl

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `𝓕_t ≤ (augment P 𝓕)_t`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobAugment.le_augment). -/
theorem le_augment (t : ℝ) : 𝓕 t ≤ augment P 𝓕 t := fun A hA =>
  ⟨𝓕.le t A hA, A, hA, EventuallyEq.rfl⟩

/-- Cochrane (2023), A1 §1.6, pp. 567–568: measurable null sets belong to every
`(augment P 𝓕)_t`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobAugment.measurableSet_augment_of_null). -/
theorem measurableSet_augment_of_null {t : ℝ} {A : Set Ω} (hA : MeasurableSet A)
    (hA0 : P A = 0) : MeasurableSet[augment P 𝓕 t] A :=
  ⟨hA, ∅, @MeasurableSet.empty _ (𝓕 t), ae_eq_empty.2 hA0⟩

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the completed filtration absorbs null
modifications.** If `f` is measurable and `f = g` a.e. with `g`
`(augment P 𝓕)_t`-strongly measurable, then `f` is `(augment P 𝓕)_t`-strongly measurable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobAugment.stronglyMeasurable_augment_of_ae_eq). -/
theorem stronglyMeasurable_augment_of_ae_eq {t : ℝ} {f g : Ω → ℝ} (hf : Measurable f)
    (hg : StronglyMeasurable[augment P 𝓕 t] g) (hfg : f =ᵐ[P] g) :
    StronglyMeasurable[augment P 𝓕 t] f := by
  classical
  have hm : Measurable[augment P 𝓕 t] f := by
    intro B hB
    obtain ⟨-, C, hC, hgC⟩ := hg.measurable hB
    refine ⟨hf hB, C, hC, ?_⟩
    refine EventuallyEq.trans ?_ hgC
    filter_upwards [hfg] with ω hω
    change (f ω ∈ B) = (g ω ∈ B)
    rw [hω]
  let := augment P 𝓕 t
  exact hm.stronglyMeasurable

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the completed filtration of an admissible
filtration is admissible** (`TidyR7BrownianQV.BMFiltration`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobAugment.bmFiltration_augment). -/
theorem bmFiltration_augment {W : ℝ≥0 → Ω → ℝ} (h𝓕 : BMFiltration P W 𝓕) :
    BMFiltration P W (augment P 𝓕) where
  adapted u := (h𝓕.adapted u).mono (le_augment u)
  indep u v huv := by
    rw [Indep_iff]
    intro A B hA hB
    obtain ⟨-, C, hC, hBC⟩ := hB
    have h := (Indep_iff _ _ P).1 (h𝓕.indep u v huv) A C hA hC
    rw [measure_congr (Filter.EventuallyEqSet.inter EventuallyEq.rfl hBC), h, measure_congr hBC]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: conditioning on the completed filtration is
conditioning on `𝓕`**: `E[f | (augment P 𝓕)_t] = E[f | 𝓕_t]` a.e. (for non-integrable `f` both
are `0` by Mathlib's convention).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobAugment.condExp_augment). -/
theorem condExp_augment [IsFiniteMeasure P] (f : Ω → ℝ) (t : ℝ) :
    P[f | augment P 𝓕 t] =ᵐ[P] P[f | 𝓕 t] := by
  by_cases hf : Integrable f P
  · refine (ae_eq_condExp_of_forall_setIntegral_eq ((augment P 𝓕).le t) hf
      (fun _ _ _ => integrable_condExp.integrableOn) ?_
      (stronglyMeasurable_condExp.mono (le_augment t)).aestronglyMeasurable).symm
    intro A hA _
    obtain ⟨-, B, hB, hAB⟩ := hA
    rw [setIntegral_congr_set hAB, setIntegral_congr_set hAB,
      setIntegral_condExp (𝓕.le t) hf hB]
  · rw [condExp_of_not_integrable hf, condExp_of_not_integrable hf]

variable {W : ℝ≥0 → Ω → ℝ} {H : ℝ → Ω → ℝ} {s t C : ℝ}

/-- Cochrane (2023), A1 §1.6, pp. 567–568: an integrand admissible for `𝓕` is admissible for
the completed filtration.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobAugment.itoIntegrand_augment). -/
theorem itoIntegrand_augment (hH : ItoIntegrand P 𝓕 H s t C) :
    ItoIntegrand P (augment P 𝓕) H s t C where
  adapted u hu := (hH.adapted u hu).mono (le_augment u)
  bound := hH.bound
  cont := hH.cont

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the Itô integral does not depend on completing
the filtration**: `∫_s^t H dW` for `augment P 𝓕` equals `∫_s^t H dW` for `𝓕` a.e.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobAugment.itoInt_augment). -/
theorem itoInt_augment (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hH : ItoIntegrand P 𝓕 H s t C) :
    itoInt P (augment P 𝓕) W H s t =ᵐ[P] itoInt P 𝓕 W H s t := by
  rcases lt_or_ge s t with hst | hts
  · exact ae_eq_of_L2Tendsto
      (L2Tendsto_dyadic hB hW (bmFiltration_augment h𝓕) hs hst (itoIntegrand_augment hH))
      (L2Tendsto_dyadic hB hW h𝓕 hs hst hH)
  · rw [itoInt_of_le hts, itoInt_of_le hts]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Track 3, item 2): an Itô integral with EVERY path
continuous, adapted to the completed filtration.** Let `W` be pre-Brownian with measurable
values and a.s. continuous paths, `𝓕` admissible, `0 ≤ s`, and `H` admissible for `𝓕` on every
`[s, T]` with one bound `C`. There is `X` with: `X_t` `(augment P 𝓕)_t`-strongly measurable;
`X_t = ∫_s^t H dW` (for `𝓕`) a.s. for every `t`; `X_t = 0` for `t ≤ s`; EVERY path continuous on
`ℝ`; `X` a martingale for `augment P 𝓕`; and `E[(sup_{[s,T]}|X|)²] ≤ 4E[∫_s^T H_u² du]` for every
`T > s`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobAugment.exists_continuous_itoInt_augment). -/
theorem exists_continuous_itoInt_augment (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕)
    (hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω) (hs : 0 ≤ s)
    (hH : ∀ T, ItoIntegrand P 𝓕 H s T C) :
    ∃ X : ℝ → Ω → ℝ, (∀ t, StronglyMeasurable[augment P 𝓕 t] (X t)) ∧
      (∀ t, X t =ᵐ[P] itoInt P 𝓕 W H s t) ∧ (∀ t ≤ s, ∀ ω, X t ω = 0) ∧
      (∀ ω, Continuous fun t => X t ω) ∧ Martingale X (augment P 𝓕) P ∧
      ∀ T, s < T → Integrable (fun ω => pathSup s T X ω ^ 2) P ∧
        ∫ ω, pathSup s T X ω ^ 2 ∂P ≤ 4 * ∫ ω, (∫ u in s..T, H u ω ^ 2) ∂P := by
  classical
  have h𝓖 := bmFiltration_augment h𝓕
  have hH' : ∀ T, ItoIntegrand P (augment P 𝓕) H s T C := fun T => itoIntegrand_augment (hH T)
  obtain ⟨X0, hX0m, hX0I, hX00, hX0c, hX0mart, -⟩ :=
    exists_adapted_continuous_itoInt hB hW h𝓖 hcont hs hH'
  have hbad : P {ω | ¬ Continuous fun t => X0 t ω} = 0 := ae_iff.1 hX0c
  obtain ⟨N, hSN, hNm, hN0⟩ := exists_measurable_superset_of_null hbad
  set X : ℝ → Ω → ℝ := fun t ω => if ω ∈ N then 0 else X0 t ω with hX
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  have hXX0 : ∀ t, X t =ᵐ[P] X0 t := fun t => by
    filter_upwards [hNae] with ω hω
    simp only [hX, hω, ↓reduceIte]
  have hXm : ∀ t, StronglyMeasurable[augment P 𝓕 t] (X t) := by
    intro t
    have hmeas : Measurable (X t) :=
      Measurable.ite hNm measurable_const (((hX0m t).mono ((augment P 𝓕).le t)).measurable)
    exact stronglyMeasurable_augment_of_ae_eq hmeas (hX0m t) (hXX0 t)
  have hXI' : ∀ t, X t =ᵐ[P] itoInt P (augment P 𝓕) W H s t := fun t =>
    (hXX0 t).trans (hX0I t)
  have hXI : ∀ t, X t =ᵐ[P] itoInt P 𝓕 W H s t := by
    intro t
    rcases le_total s t with hst | hts
    · exact (hXI' t).trans (itoInt_augment hB hW h𝓕 hs (hH t))
    · refine ae_of_all _ fun ω => ?_
      simp only [hX, hX00 t hts ω, itoInt_of_le hts]
      split_ifs <;> rfl
  have hXc : ∀ ω, Continuous fun t => X t ω := by
    intro ω
    by_cases hω : ω ∈ N
    · simp only [hX, hω, ↓reduceIte]
      exact continuous_const
    · have hc : Continuous fun t => X0 t ω := by
        by_contra h
        exact hω (hSN h)
      simpa only [hX, hω, ↓reduceIte] using hc
  refine ⟨X, hXm, hXI, fun t ht ω => ?_, hXc, ⟨hXm, fun i j hij => ?_⟩, fun T hsT => ?_⟩
  · simp only [hX, hX00 t ht ω]
    split_ifs <;> rfl
  · exact (condExp_congr_ae (hXX0 j)).trans ((hX0mart.2 i j hij).trans (hXX0 i).symm)
  · have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
    exact doob_sq_itoInt hB hW h𝓖 hs hsT (hH' T) (fun t _ => hXI' t)
      (ae_of_all _ fun ω x _ => (hXc ω).continuousWithinAt)

end Cochrane.ZeroBound.TidyR10DoobAugment
