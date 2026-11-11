/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR7BrownianQV

/-!
# Two independent Brownian motions and a common admissible filtration

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for (1.32) when bonds and the
deflated price `Λ/P` load on different shocks (Track 3, chunk B2): two independent Brownian
motions `W¹`, `W²` on one probability space, with one filtration that is admissible for both.

## Main definitions

* `TwoBMFiltration P W₁ W₂ 𝓕`: `𝓕` is admissible for each motion
  (`TidyR7BrownianQV.BMFiltration`), the PAIR of increments `(W¹_v − W¹_u, W²_v − W²_u)`
  (`incrPair`) is independent of `𝓕_u`, and the two increments over a common interval are
  independent.
* `twoBMFiltration W₁ W₂`: the joint natural filtration
  `𝓕_u = σ(W¹_r, r ≤ u) ⊔ σ(W²_r, r ≤ u)` on the time index `ℝ` (through `max u 0`).
* `twoGauss`: the product `gaussSeq ⊗ gaussSeq` of two copies of the Gaussian sequence space;
  `bmPath₁ t ω = bmPath t ω.1`, `bmPath₂ t ω = bmPath t ω.2`.

## Main results

* `indep_sup_sup`: if `𝒜₁ ⊥ ℬ₁`, `𝒜₂ ⊥ ℬ₂` and `𝒢₁ ⊥ 𝒢₂` with `𝒜ᵢ, ℬᵢ ≤ 𝒢ᵢ`, then
  `ℬ₁ ⊔ ℬ₂ ⊥ 𝒜₁ ⊔ 𝒜₂` (by π-systems of intersections, `generateFrom_interSets`).
* `twoBMFiltration_isTwoBM` (**the common filtration is admissible for both motions**): for any
  two pre-Brownian motions with measurable values whose paths are independent as path-valued
  random variables, the joint natural filtration is a `TwoBMFiltration`.
* Existence on `twoGauss`: `isBrownianReal_bmPath₁`, `isBrownianReal_bmPath₂` (each is a
  Brownian motion, every path continuous), `indepFun_bmPath₁₂` (independent as processes),
  `twoBMFiltration_bmPath_isTwoBM`, and the packaged `exists_two_independent_bm`.
-/

namespace Cochrane.Monetarism.TidyR10TwoBMExist

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7BrownianTools Cochrane.Monetarism.TidyR7BrownianQV
  Cochrane.Monetarism.TidyR7BrownianSchauder Cochrane.Monetarism.TidyR7BrownianExist
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ## The definition -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the pair of increments
`(W¹_v − W¹_u, W²_v − W²_u)`. -/
def incrPair (W₁ W₂ : ℝ≥0 → Ω → ℝ) (u v : ℝ) (ω : Ω) : ℝ × ℝ := (incr W₁ u v ω, incr W₂ u v ω)

variable (P) (W₁ W₂ : ℝ≥0 → Ω → ℝ) (𝓕 : Filtration ℝ mΩ)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (the information `E_t` of (1.32) when bonds and `Λ/P`
load on two shocks): a common admissible filtration for two Brownian motions.** `𝓕` is
admissible for `W¹` and for `W²`, the pair of increments over `[u, v]` is independent of `𝓕_u`,
and the two increments over a common interval are independent of each other. -/
structure TwoBMFiltration where
  bm1 : BMFiltration P W₁ 𝓕
  bm2 : BMFiltration P W₂ 𝓕
  indep : ∀ u v, u ≤ v → Indep (MeasurableSpace.comap (incrPair W₁ W₂ u v) inferInstance) (𝓕 u) P
  incr_indep : ∀ u v, IndepFun (incr W₁ u v) (incr W₂ u v) P

variable {P W₁ W₂ 𝓕}

/-! ## Independence of joins -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the intersections `a ∩ b` with `a` measurable for
`m₁` and `b` for `m₂`, a π-system generating `m₁ ⊔ m₂`. -/
def interSets (m₁ m₂ : MeasurableSpace Ω) : Set (Set Ω) :=
  {s | ∃ a b, MeasurableSet[m₁] a ∧ MeasurableSet[m₂] b ∧ s = a ∩ b}

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `interSets m₁ m₂` is a π-system. -/
theorem isPiSystem_interSets (m₁ m₂ : MeasurableSpace Ω) : IsPiSystem (interSets m₁ m₂) := by
  rintro _ ⟨a, b, ha, hb, rfl⟩ _ ⟨a', b', ha', hb', rfl⟩ _
  refine ⟨a ∩ a', b ∩ b', ha.inter ha', hb.inter hb', ?_⟩
  ext ω
  simp only [Set.mem_inter_iff]
  tauto

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `interSets m₁ m₂` generates `m₁ ⊔ m₂`.
The two-family case of Mathlib `generateFrom_piiUnionInter_measurableSet`. -/
theorem generateFrom_interSets (m₁ m₂ : MeasurableSpace Ω) :
    MeasurableSpace.generateFrom (interSets m₁ m₂) = m₁ ⊔ m₂ := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) (sup_le ?_ ?_)
  · rintro _ ⟨a, b, ha, hb, rfl⟩
    exact ((le_sup_left : m₁ ≤ m₁ ⊔ m₂) a ha).inter ((le_sup_right : m₂ ≤ m₁ ⊔ m₂) b hb)
  · intro a ha
    refine MeasurableSpace.measurableSet_generateFrom ⟨a, Set.univ, ha,
      MeasurableSet.univ, ?_⟩
    rw [Set.inter_univ]
  · intro b hb
    refine MeasurableSpace.measurableSet_generateFrom ⟨Set.univ, b, MeasurableSet.univ,
      hb, ?_⟩
    rw [Set.univ_inter]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: independence of joins.** If `ℬ₁ ⊥ 𝒜₁`,
`ℬ₂ ⊥ 𝒜₂`, and `𝒢₁ ⊥ 𝒢₂` with `𝒜₁, ℬ₁ ≤ 𝒢₁` and `𝒜₂, ℬ₂ ≤ 𝒢₂`, then
`ℬ₁ ⊔ ℬ₂ ⊥ 𝒜₁ ⊔ 𝒜₂` (future increments of two independent motions are independent of their
joint past). -/
theorem indep_sup_sup [IsProbabilityMeasure P] {a₁ b₁ a₂ b₂ g₁ g₂ : MeasurableSpace Ω}
    (h₁ : Indep b₁ a₁ P) (h₂ : Indep b₂ a₂ P) (hg : Indep g₁ g₂ P) (ha₁ : a₁ ≤ g₁)
    (hb₁ : b₁ ≤ g₁) (ha₂ : a₂ ≤ g₂) (hb₂ : b₂ ≤ g₂) (hg₁ : g₁ ≤ mΩ) (hg₂ : g₂ ≤ mΩ) :
    Indep (b₁ ⊔ b₂) (a₁ ⊔ a₂) P := by
  rw [← generateFrom_interSets b₁ b₂, ← generateFrom_interSets a₁ a₂]
  refine IndepSets.indep' ?_ ?_ (isPiSystem_interSets _ _) (isPiSystem_interSets _ _) ?_
  · rintro _ ⟨a, b, ha, hb, rfl⟩
    exact (hg₁ a (hb₁ a ha)).inter (hg₂ b (hb₂ b hb))
  · rintro _ ⟨a, b, ha, hb, rfl⟩
    exact (hg₁ a (ha₁ a ha)).inter (hg₂ b (ha₂ b hb))
  rw [IndepSets_iff]
  rintro _ _ ⟨B₁, B₂, hB₁, hB₂, rfl⟩ ⟨A₁, A₂, hA₁, hA₂, rfl⟩
  have e1 := (Indep_iff _ _ _).1 h₁ B₁ A₁ hB₁ hA₁
  have e2 := (Indep_iff _ _ _).1 h₂ B₂ A₂ hB₂ hA₂
  have e3 := (Indep_iff _ _ _).1 hg (B₁ ∩ A₁) (B₂ ∩ A₂) ((hb₁ _ hB₁).inter (ha₁ _ hA₁))
    ((hb₂ _ hB₂).inter (ha₂ _ hA₂))
  have e4 := (Indep_iff _ _ _).1 hg B₁ B₂ (hb₁ _ hB₁) (hb₂ _ hB₂)
  have e5 := (Indep_iff _ _ _).1 hg A₁ A₂ (ha₁ _ hA₁) (ha₂ _ hA₂)
  have hset : B₁ ∩ B₂ ∩ (A₁ ∩ A₂) = B₁ ∩ A₁ ∩ (B₂ ∩ A₂) := by
    ext ω
    simp only [Set.mem_inter_iff]
    tauto
  rw [hset, e3, e1, e2, e4, e5]
  ring

/-! ## The joint natural filtration -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the σ-algebra of the whole path `(W_t)_{t ≥ 0}`. -/
abbrev pathSigma (W : ℝ≥0 → Ω → ℝ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω t => W t ω) MeasurableSpace.pi

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the path σ-algebra of a process with measurable values
is a sub-σ-algebra. -/
theorem pathSigma_le {W : ℝ≥0 → Ω → ℝ} (hW : ∀ t, Measurable (W t)) : pathSigma W ≤ mΩ :=
  (Measurable.of_eval hW).comap_le

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the past `𝓕^W_a` is part of the path σ-algebra. -/
theorem bmFiltration_le_pathSigma {W : ℝ≥0 → Ω → ℝ} (hW : ∀ t, Measurable (W t)) (a : ℝ≥0) :
    bmFiltration W hW a ≤ pathSigma W := by
  rw [bmFiltration_eq_comap]
  have h1 : Measurable fun (f : ℝ≥0 → ℝ) (r : Set.Iic a) => f r := by fun_prop
  have hm : Measurable[pathSigma W] (fun ω (r : Set.Iic a) => W r ω) :=
    h1.comp (comap_measurable (fun ω t => W t ω))
  exact hm.comap_le

/-- Cochrane (2023), A1 §1.6, pp. 567–568: an increment is measurable for the path σ-algebra. -/
theorem measurable_incr_pathSigma (W : ℝ≥0 → Ω → ℝ) (u v : ℝ) :
    Measurable[pathSigma W] (incr W u v) := by
  have h1 : Measurable fun f : ℝ≥0 → ℝ => f v.toNNReal - f u.toNNReal := by fun_prop
  have h : Measurable[pathSigma W] (fun ω => (fun f : ℝ≥0 → ℝ => f v.toNNReal - f u.toNNReal)
      ((fun ω t => W t ω) ω)) :=
    h1.comp (comap_measurable (fun ω t => W t ω))
  exact h

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the joint natural filtration**
`𝓕_u = σ(W¹_r, r ≤ max u 0) ⊔ σ(W²_r, r ≤ max u 0)` on the time index `ℝ`. -/
noncomputable def twoBMFiltration (W₁ W₂ : ℝ≥0 → Ω → ℝ) (hW₁ : ∀ t, Measurable (W₁ t))
    (hW₂ : ∀ t, Measurable (W₂ t)) : Filtration ℝ mΩ where
  seq u := bmFiltration W₁ hW₁ u.toNNReal ⊔ bmFiltration W₂ hW₂ u.toNNReal
  mono' _ _ h := sup_le_sup ((bmFiltration W₁ hW₁).mono (Real.toNNReal_le_toNNReal h))
    ((bmFiltration W₂ hW₂).mono (Real.toNNReal_le_toNNReal h))
  le' u := sup_le ((bmFiltration W₁ hW₁).le u.toNNReal) ((bmFiltration W₂ hW₂).le u.toNNReal)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the joint natural filtration of two independent
pre-Brownian motions is a common admissible filtration.** If `W¹`, `W²` are pre-Brownian with
measurable values and their paths are independent (as random elements of `ℝ≥0 → ℝ`), then
`twoBMFiltration W¹ W²` is a `TwoBMFiltration`. -/
theorem twoBMFiltration_isTwoBM (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (hI : IndepFun (fun ω t => W₁ t ω) (fun ω t => W₂ t ω) P) :
    TwoBMFiltration P W₁ W₂ (twoBMFiltration W₁ W₂ hW₁ hW₂) := by
  have : IsProbabilityMeasure P := hB₁.isGaussianProcess.isProbabilityMeasure
  have hg : Indep (pathSigma W₁) (pathSigma W₂) P := (IndepFun_iff_Indep _ _ _).1 hI
  have hind : ∀ u v, u ≤ v → Indep (MeasurableSpace.comap (incr W₁ u v) inferInstance
      ⊔ MeasurableSpace.comap (incr W₂ u v) inferInstance)
      (twoBMFiltration W₁ W₂ hW₁ hW₂ u) P := fun u v huv =>
    indep_sup_sup (indep_increment_bmFiltration hB₁ hW₁ (Real.toNNReal_le_toNNReal huv))
      (indep_increment_bmFiltration hB₂ hW₂ (Real.toNNReal_le_toNNReal huv)) hg
      (bmFiltration_le_pathSigma hW₁ _) (measurable_incr_pathSigma W₁ u v).comap_le
      (bmFiltration_le_pathSigma hW₂ _) (measurable_incr_pathSigma W₂ u v).comap_le
      (pathSigma_le hW₁) (pathSigma_le hW₂)
  refine ⟨⟨fun u => ?_, fun u v huv => ?_⟩, ⟨fun u => ?_, fun u v huv => ?_⟩,
    fun u v huv => ?_, fun u v => ?_⟩
  · exact (stronglyAdapted_bmFiltration hW₁ u.toNNReal).mono le_sup_left
  · exact indep_of_indep_of_le_left (hind u v huv) le_sup_left
  · exact (stronglyAdapted_bmFiltration hW₂ u.toNNReal).mono le_sup_right
  · exact indep_of_indep_of_le_left (hind u v huv) le_sup_right
  · change Indep (MeasurableSpace.comap (fun ω => (incr W₁ u v ω, incr W₂ u v ω))
      inferInstance) _ P
    have e := MeasurableSpace.comap_prodMk (mβ := (inferInstance : MeasurableSpace ℝ))
      (mγ := (inferInstance : MeasurableSpace ℝ)) (incr W₁ u v) (incr W₂ u v)
    rw [show (inferInstance : MeasurableSpace (ℝ × ℝ))
      = (inferInstance : MeasurableSpace ℝ).prod inferInstance from rfl, e]
    exact hind u v huv
  · have h1 : Measurable fun f : ℝ≥0 → ℝ => f v.toNNReal - f u.toNNReal := by fun_prop
    exact hI.comp h1 h1

/-! ## Existence on the product of two Gaussian sequence spaces -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (infrastructure for two shocks): **the product of two
copies of the Gaussian sequence space**, `gaussSeq ⊗ gaussSeq` on `(ℕ → ℝ) × (ℕ → ℝ)`. -/
noncomputable def twoGauss : Measure ((ℕ → ℝ) × (ℕ → ℝ)) := gaussSeq.prod gaussSeq

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `twoGauss` is a probability measure.
Restates the Mathlib instance `MeasureTheory.Measure.prod.instIsProbabilityMeasure`. -/
theorem isProbabilityMeasure_twoGauss : IsProbabilityMeasure twoGauss := by
  have := isProbabilityMeasure_gaussSeq
  unfold twoGauss
  infer_instance

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the first Brownian motion** `W¹_t(ω) = bmPath t ω.1`,
built from the first coordinate sequence. -/
noncomputable def bmPath₁ (t : ℝ≥0) (ω : (ℕ → ℝ) × (ℕ → ℝ)) : ℝ := bmPath t ω.1

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the second Brownian motion**
`W²_t(ω) = bmPath t ω.2`, built from the second coordinate sequence. -/
noncomputable def bmPath₂ (t : ℝ≥0) (ω : (ℕ → ℝ) × (ℕ → ℝ)) : ℝ := bmPath t ω.2

/-- Cochrane (2023), A1 §1.6, pp. 567–568: each `W¹_t` is measurable. -/
theorem measurable_bmPath₁ (t : ℝ≥0) : Measurable (bmPath₁ t) :=
  (measurable_bmPath t).comp measurable_fst

/-- Cochrane (2023), A1 §1.6, pp. 567–568: each `W²_t` is measurable. -/
theorem measurable_bmPath₂ (t : ℝ≥0) : Measurable (bmPath₂ t) :=
  (measurable_bmPath t).comp measurable_snd

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **`W¹` is a Brownian motion** on `twoGauss`, with every
path continuous: the first projection carries `twoGauss` to `gaussSeq`. -/
theorem isBrownianReal_bmPath₁ : IsBrownianReal bmPath₁ twoGauss := by
  have := isProbabilityMeasure_gaussSeq
  have hfst : HasLaw Prod.fst gaussSeq twoGauss := measurePreserving_fst.hasLaw
  exact ⟨⟨fun I => (isBrownianReal_bmPath.hasLaw I).comp hfst⟩,
    Eventually.of_forall fun ω => continuous_bmPath ω.1⟩

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **`W²` is a Brownian motion** on `twoGauss`, with
every path continuous. -/
theorem isBrownianReal_bmPath₂ : IsBrownianReal bmPath₂ twoGauss := by
  have := isProbabilityMeasure_gaussSeq
  have hsnd : HasLaw Prod.snd gaussSeq twoGauss := measurePreserving_snd.hasLaw
  exact ⟨⟨fun I => (isBrownianReal_bmPath.hasLaw I).comp hsnd⟩,
    Eventually.of_forall fun ω => continuous_bmPath ω.2⟩

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **`W¹` and `W²` are independent as processes**: their
paths, as random elements of `ℝ≥0 → ℝ`, are independent (Mathlib `indepFun_prod`). -/
theorem indepFun_bmPath₁₂ :
    IndepFun (fun ω t => bmPath₁ t ω) (fun ω t => bmPath₂ t ω) twoGauss := by
  have := isProbabilityMeasure_gaussSeq
  exact indepFun_prod (X := fun ω t => bmPath t ω) (Y := fun ω t => bmPath t ω)
    (Measurable.of_eval measurable_bmPath) (Measurable.of_eval measurable_bmPath)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the joint natural filtration of `W¹`, `W²` on
`twoGauss`. -/
noncomputable def twoBMF : Filtration ℝ (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))) :=
  twoBMFiltration bmPath₁ bmPath₂ measurable_bmPath₁ measurable_bmPath₂

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (non-vacuity): the constructed pair has a common
admissible filtration**, `twoBMF`. -/
theorem twoBMFiltration_bmPath_isTwoBM : TwoBMFiltration twoGauss bmPath₁ bmPath₂ twoBMF :=
  twoBMFiltration_isTwoBM isBrownianReal_bmPath₁.toIsPreBrownianReal
    isBrownianReal_bmPath₂.toIsPreBrownianReal measurable_bmPath₁ measurable_bmPath₂
    indepFun_bmPath₁₂

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: two independent Brownian motions with a common
admissible filtration exist**: on a probability space, two Brownian motions (Mathlib
`IsBrownianReal`) with measurable values and every path continuous and starting at `0`,
independent as processes, and a filtration that is a `TwoBMFiltration` for the pair. -/
theorem exists_two_independent_bm :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (W₁ W₂ : ℝ≥0 → Ω → ℝ) (𝓕 : Filtration ℝ (inferInstance : MeasurableSpace Ω)),
      IsBrownianReal W₁ P ∧ IsBrownianReal W₂ P ∧ (∀ t, Measurable (W₁ t)) ∧
      (∀ t, Measurable (W₂ t)) ∧ (∀ ω, Continuous (fun t => W₁ t ω) ∧ W₁ 0 ω = 0) ∧
      (∀ ω, Continuous (fun t => W₂ t ω) ∧ W₂ 0 ω = 0) ∧
      IndepFun (fun ω t => W₁ t ω) (fun ω t => W₂ t ω) P ∧ TwoBMFiltration P W₁ W₂ 𝓕 :=
  ⟨_, inferInstance, twoGauss, isProbabilityMeasure_twoGauss, bmPath₁, bmPath₂, twoBMF,
    isBrownianReal_bmPath₁, isBrownianReal_bmPath₂, measurable_bmPath₁, measurable_bmPath₂,
    fun ω => ⟨continuous_bmPath ω.1, bmPath_zero ω.1⟩,
    fun ω => ⟨continuous_bmPath ω.2, bmPath_zero ω.2⟩, indepFun_bmPath₁₂,
    twoBMFiltration_bmPath_isTwoBM⟩

end Cochrane.Monetarism.TidyR10TwoBMExist
