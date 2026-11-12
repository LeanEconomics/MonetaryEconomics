/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.Expectations
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Process.Filtration

/-!
# Measure-theoretic conditional expectations

Woodford (2003), *Interest and Prices*, Chapter 3, §2.1 and Appendix B.3 (pp. 659–661): the
expectations `E_t` in (2.8) and (2.9) on a genuine probability space. Restated (the part needed
here) from the Cochrane ObservationalEquivalence project's ExpectationsMeasure, with the namespace
renamed.

The core `ExpectationSystem` defines `E_t` on **all** functions `Ω → ℝ` with exact equalities.
This module is the measure-theoretic counterpart: a probability space with a filtration and
Mathlib's `condExp`, every property in its almost-everywhere form; `E_t` of a non-integrable
function is Mathlib's junk value `0`, so integrability hypotheses appear where the core needs
none.

* `MeasExpectationSystem Ω` (fields `P : ProbabilityMeasure Ω`, `𝓕 : Filtration ℕ _`);
  `S.μ` the measure, `S.E t x = S.μ[x | S.𝓕 t]`.
* `E_add`, `E_sub`, `E_smul`, `E_const`, `E_mono`, `E_tower`, `E_known`, `E_E_self`,
  `E_of_stronglyMeasurable`, `E_of_aestronglyMeasurable`, `E_congr`, `stronglyMeasurable_E`,
  `integrable_E`, `integral_E`.
* Bridge: `toExpectationSystem` (a finite discrete state space with full support gives a core
  `ExpectationSystem` with the same `E_t`, `toExpectationSystem_E`).
-/

namespace Woodford.NominalRigidities.TidyR5ExpectationsMeasure

open MeasureTheory ProbabilityTheory Filter Topology

variable (Ω : Type*) [mΩ : MeasurableSpace Ω]

/-- Woodford (2003), App. B.3 (the conditional expectations `E_t` of (2.8); restated from the
Cochrane ObservationalEquivalence project): a probability space `(Ω, P)` with a filtration
`𝓕 : ℕ → MeasurableSpace Ω`; `E_t x := P[x | 𝓕 t]`. -/
structure MeasExpectationSystem where
  /-- The probability measure. -/
  P : ProbabilityMeasure Ω
  /-- The information available at each date. -/
  𝓕 : Filtration ℕ mΩ

namespace MeasExpectationSystem

variable {Ω} (S : MeasExpectationSystem Ω)

/-- Woodford (2003), App. B.3: the probability measure as a measure. -/
abbrev μ : Measure Ω := S.P

/-- Woodford (2003), App. B.3: `E_t x = μ[x | 𝓕 t]`, Mathlib's conditional expectation. -/
noncomputable abbrev E (t : ℕ) (x : Ω → ℝ) : Ω → ℝ := S.μ[x | S.𝓕 t]

/-- Woodford (2003), App. B.3: `E_t` is additive (a.e.). -/
theorem E_add {x y : Ω → ℝ} (hx : Integrable x S.μ) (hy : Integrable y S.μ) (t : ℕ) :
    S.E t (x + y) =ᵐ[S.μ] S.E t x + S.E t y := condExp_add hx hy _

/-- Woodford (2003), App. B.3: `E_t` commutes with differences (a.e.). -/
theorem E_sub {x y : Ω → ℝ} (hx : Integrable x S.μ) (hy : Integrable y S.μ) (t : ℕ) :
    S.E t (x - y) =ᵐ[S.μ] S.E t x - S.E t y := condExp_sub hx hy _

/-- Woodford (2003), App. B.3: `E_t` is homogeneous (a.e.). -/
theorem E_smul (c : ℝ) (x : Ω → ℝ) (t : ℕ) : S.E t (c • x) =ᵐ[S.μ] c • S.E t x :=
  condExp_smul c x _

/-- Woodford (2003), App. B.3: constants are known (exactly). -/
theorem E_const (t : ℕ) (c : ℝ) : S.E t (fun _ => c) = fun _ => c :=
  condExp_const (S.𝓕.le t) c

/-- Woodford (2003), App. B.3: `E_t` is monotone (a.e.). -/
theorem E_mono {x y : Ω → ℝ} (hx : Integrable x S.μ) (hy : Integrable y S.μ)
    (hxy : x ≤ᵐ[S.μ] y) (t : ℕ) : S.E t x ≤ᵐ[S.μ] S.E t y := condExp_mono hx hy hxy

/-- Woodford (2003), App. B.3: the law of iterated expectations `E_s E_t = E_s`, `s ≤ t` (a.e.). -/
theorem E_tower {s t : ℕ} (hst : s ≤ t) (x : Ω → ℝ) : S.E s (S.E t x) =ᵐ[S.μ] S.E s x :=
  condExp_condExp_of_le (S.𝓕.mono hst) (S.𝓕.le t)

/-- Woodford (2003), App. B.3: `E_t x` is `𝓕 t`-strongly measurable. -/
theorem stronglyMeasurable_E (t : ℕ) (x : Ω → ℝ) : StronglyMeasurable[S.𝓕 t] (S.E t x) :=
  stronglyMeasurable_condExp

/-- Woodford (2003), App. B.3: `E_t x` is integrable. -/
theorem integrable_E (t : ℕ) (x : Ω → ℝ) : Integrable (S.E t x) S.μ := integrable_condExp

/-- Woodford (2003), App. B.3: what is known at `t` is its own forecast (exactly). -/
theorem E_of_stronglyMeasurable {t : ℕ} {x : Ω → ℝ} (hx : StronglyMeasurable[S.𝓕 t] x)
    (hi : Integrable x S.μ) : S.E t x = x :=
  condExp_of_stronglyMeasurable (S.𝓕.le t) hx hi

/-- Woodford (2003), App. B.3: what is a.e. known at `t` is a.e. its own forecast. -/
theorem E_of_aestronglyMeasurable {t : ℕ} {x : Ω → ℝ} (hx : AEStronglyMeasurable[S.𝓕 t] x S.μ)
    (hi : Integrable x S.μ) : S.E t x =ᵐ[S.μ] x :=
  condExp_of_aestronglyMeasurable' (S.𝓕.le t) hx hi

/-- Woodford (2003), App. B.3: earlier forecasts are known later, `E_t E_s = E_s` for `s ≤ t`
(exactly). -/
theorem E_known {s t : ℕ} (hst : s ≤ t) (x : Ω → ℝ) : S.E t (S.E s x) = S.E s x :=
  S.E_of_stronglyMeasurable ((S.stronglyMeasurable_E s x).mono (S.𝓕.mono hst))
    (S.integrable_E s x)

/-- Woodford (2003), App. B.3: `E_t` is idempotent (exactly). -/
theorem E_E_self (t : ℕ) (x : Ω → ℝ) : S.E t (S.E t x) = S.E t x := S.E_known le_rfl x

/-- Woodford (2003), App. B.3: `E_t` respects a.e. equality. -/
theorem E_congr {x y : Ω → ℝ} (h : x =ᵐ[S.μ] y) (t : ℕ) : S.E t x =ᵐ[S.μ] S.E t y :=
  condExp_congr_ae h

/-- Woodford (2003), App. B.3: the unconditional mean of a forecast is the mean. -/
theorem integral_E (t : ℕ) (x : Ω → ℝ) : ∫ ω, S.E t x ω ∂S.μ = ∫ ω, x ω ∂S.μ :=
  integral_condExp (S.𝓕.le t)

/-! ### Bridge to the core `ExpectationSystem` on a finite, fully supported state space -/

/-- Woodford (2003), App. B.3 (restated from the Cochrane ObservationalEquivalence project): when
every state has positive probability, a.e. equality is equality. -/
theorem eq_of_ae_eq (hfull : ∀ ω, S.μ {ω} ≠ 0) {f g : Ω → ℝ} (h : f =ᵐ[S.μ] g) : f = g := by
  funext ω
  by_contra hne
  have h0 : S.μ {ω' | f ω' ≠ g ω'} = 0 := ae_iff.mp h
  refine hfull ω (measure_mono_null (fun ω' hω' => ?_) h0)
  rw [Set.mem_singleton_iff.mp hω']
  exact hne

/-- Woodford (2003), App. B.3 (restated from the Cochrane ObservationalEquivalence project): when
every state has positive probability, a.e. inequality is inequality. -/
theorem le_of_ae_le (hfull : ∀ ω, S.μ {ω} ≠ 0) {f g : Ω → ℝ} (h : f ≤ᵐ[S.μ] g) : f ≤ g := by
  intro ω
  by_contra hne
  have h0 : S.μ {ω' | ¬ f ω' ≤ g ω'} = 0 := ae_iff.mp h
  refine hfull ω (measure_mono_null (fun ω' hω' => ?_) h0)
  rw [Set.mem_singleton_iff.mp hω']
  exact hne

/-- Woodford (2003), App. B.3 (restated from the Cochrane ObservationalEquivalence project): `E_t`
as a linear map on all of `Ω → ℝ`, for a finite discrete state space with full support. -/
noncomputable def ELin [Finite Ω] [DiscreteMeasurableSpace Ω] (hfull : ∀ ω, S.μ {ω} ≠ 0)
    (t : ℕ) : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) where
  toFun := S.E t
  map_add' _ _ := S.eq_of_ae_eq hfull (S.E_add Integrable.of_finite Integrable.of_finite t)
  map_smul' c x := S.eq_of_ae_eq hfull (S.E_smul c x t)

/-- Woodford (2003), App. B.3 (**bridge**; restated from the Cochrane ObservationalEquivalence
project): on a finite discrete state space with full support, a measure-theoretic expectation
system is a core `ExpectationSystem` with the same `E_t` at every state, so every core theorem
applies to it. -/
noncomputable def toExpectationSystem [Finite Ω] [DiscreteMeasurableSpace Ω]
    (hfull : ∀ ω, S.μ {ω} ≠ 0) : ExpectationSystem Ω where
  E := S.ELin hfull
  const := S.E_const
  mono t _ _ h := S.le_of_ae_le hfull
    (S.E_mono Integrable.of_finite Integrable.of_finite (Eventually.of_forall h) t)
  tower hst x := S.eq_of_ae_eq hfull (S.E_tower hst x)
  known hst x := S.E_known hst x

/-- Woodford (2003), App. B.3 (restated from the Cochrane ObservationalEquivalence project): the
core system's `E_t` is Mathlib's conditional expectation, exactly. -/
theorem toExpectationSystem_E [Finite Ω] [DiscreteMeasurableSpace Ω]
    (hfull : ∀ ω, S.μ {ω} ≠ 0) (t : ℕ) (x : Ω → ℝ) :
    (S.toExpectationSystem hfull).E t x = S.E t x := rfl

end MeasExpectationSystem

end Woodford.NominalRigidities.TidyR5ExpectationsMeasure
