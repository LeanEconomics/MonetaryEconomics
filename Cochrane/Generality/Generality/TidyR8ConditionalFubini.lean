/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# A conditional Fubini theorem: `E_t ∫ X_τ dτ = ∫ E_t X_τ dτ`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.6, pp. 70–79: the
continuous-time present values `E_t ∫_0^∞ e^{−rτ} s_{t+τ} dτ` of (3.31)–(3.36) and (3.43), the
AR(1) example after (3.44)–(3.45) on p. 77, and the innovation identities (3.46)–(3.51). The book
moves `E_t` inside the time integral throughout (e.g. p. 77,
`E_t ∫_0^∞ e^{−rτ}s_{t+τ}dτ = ∫_0^∞ e^{−(r+η)τ}s_t dτ`). This module proves that interchange.

## The difficulty and how it is handled

For each `τ` the conditional expectation `E[X_τ | m]` is only an almost-everywhere class, so
`τ ↦ E[X_τ | m](ω)` need not be a measurable path. The theorem therefore asks for a *version*
`Y` of the conditional expectations that is jointly measurable in `(τ, ω)` for the product of the
time σ-algebra with the conditioning σ-algebra `m`, with `Y_τ = E[X_τ | m]` a.s. for almost every
`τ`. In the applications (`TidyR8OUPresentValue`, `TidyR8StochasticNews`) such a version is
explicit, e.g. `Y(τ, ω) = e^{−ητ}s_t(ω)` for the AR(1) surplus.

## Main results

* `condExp_integral_interchange` (**conditional Fubini**): if `X` is integrable on `ν ⊗ μ`
  (`ν` any s-finite measure on the time axis, for instance `e^{−rτ}dτ` on `(0, ∞)` folded into
  `X`) and `Y` is such a version, then a.s. `E[∫ X_τ dν | m] = ∫ Y_τ dν`.
* `integrable_uncurry_of_integral_abs`: the hypothesis in the book's form — `X` jointly
  measurable, every `X_τ` integrable and `τ ↦ E|X_τ|` integrable for `ν` (`∫E|X_τ|e^{−rτ}dτ < ∞`)
  — gives integrability on `ν ⊗ μ`.
* `integrable_uncurry_version`: the version `Y` is then itself integrable on `ν ⊗ μ`.
* `integral_integral_interchange`: the unconditional case `E ∫ X_τ dν = ∫ E X_τ dν`.
* `condExp_integral_interchange_of_integral_abs`: the interchange from the book-form hypotheses.
* `condExp_integral_revision`: the revision between two conditioning σ-algebras `m₁ ≤ m₂` is the
  integral of the revisions of the versions, `E[∫X | m₂] − E[∫X | m₁] = ∫ (Y² − Y¹)` a.s.
-/

namespace Cochrane.Generality.TidyR8ConditionalFubini

open MeasureTheory Function

variable {T Ω : Type*} {mT : MeasurableSpace T} {m m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {ν : Measure T}

/-- Cochrane (2023), §3.6, pp. 70–79: the product σ-algebra on `T × Ω` is monotone in the
σ-algebra on `Ω` (a function measurable for `mT ⊗ m` is measurable for `mT ⊗ mΩ` when
`m ≤ mΩ`). -/
theorem measurableSpace_prod_le_prod (hm : m ≤ mΩ) :
    (@Prod.instMeasurableSpace T Ω mT m) ≤ (@Prod.instMeasurableSpace T Ω mT mΩ) :=
  sup_le_sup le_rfl (MeasurableSpace.comap_mono hm)

/-- **Cochrane (2023), §3.6, pp. 70–79 (`∫ E|X_τ| e^{−rτ}dτ < ∞`):** a jointly measurable
process with integrable values whose mean absolute value is `ν`-integrable is integrable on
`ν ⊗ μ`.
One direction of Mathlib `integrable_prod_iff`. -/
theorem integrable_uncurry_of_integral_abs [SFinite ν] [SFinite μ] {X : T → Ω → ℝ}
    (hX : AEStronglyMeasurable (uncurry X) (ν.prod μ)) (hXi : ∀ᵐ τ ∂ν, Integrable (X τ) μ)
    (hXa : Integrable (fun τ => ∫ ω, |X τ ω| ∂μ) ν) : Integrable (uncurry X) (ν.prod μ) :=
  (integrable_prod_iff hX).2 ⟨hXi, by simpa [Real.norm_eq_abs] using hXa⟩

/-- Cochrane (2023), §3.6, pp. 70–79: a jointly `mT ⊗ m`-measurable version `Y` of the
conditional expectations `E[X_τ | m]` of an integrable `X` is integrable on `ν ⊗ μ`, since
`E|E[X_τ | m]| ≤ E|X_τ|` (Mathlib `integral_abs_condExp_le`). -/
theorem integrable_uncurry_version [SFinite ν] [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {X Y : T → Ω → ℝ} (hX : Integrable (uncurry X) (ν.prod μ))
    (hY : @StronglyMeasurable (T × Ω) ℝ _ (@Prod.instMeasurableSpace T Ω mT m) (uncurry Y))
    (hXY : ∀ᵐ τ ∂ν, Y τ =ᵐ[μ] μ[X τ | m]) : Integrable (uncurry Y) (ν.prod μ) := by
  have hYm : StronglyMeasurable (uncurry Y) := hY.mono (measurableSpace_prod_le_prod hm)
  have hXp := (integrable_prod_iff hX.aestronglyMeasurable).1 hX
  refine (integrable_prod_iff hYm.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · filter_upwards [hXY] with τ hτ
    exact integrable_condExp.congr hτ.symm
  · refine Integrable.mono' hXp.2 hYm.aestronglyMeasurable.norm.integral_prod_right' ?_
    filter_upwards [hXY] with τ hτ
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have e1 : ∫ ω, ‖uncurry Y (τ, ω)‖ ∂μ = ∫ ω, |μ[X τ | m] ω| ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hτ] with ω hω
      simp only [uncurry_apply_pair, Real.norm_eq_abs, hω]
    have e2 : ∫ ω, ‖uncurry X (τ, ω)‖ ∂μ = ∫ ω, |X τ ω| ∂μ := by
      simp only [uncurry_apply_pair, Real.norm_eq_abs]
    rw [e1, e2]
    exact integral_abs_condExp_le (X τ)

/-- **Cochrane (2023), §3.6, pp. 70–79, p. 77 (`E_t ∫ e^{−rτ}s_{t+τ}dτ = ∫ e^{−rτ}E_t s_{t+τ}dτ`):
the conditional Fubini theorem.** Let `μ` be finite, `m ≤ mΩ` a sub-σ-algebra, `ν` an s-finite
measure on the time axis, `X` integrable on `ν ⊗ μ`, and `Y` a version of the conditional
expectations, jointly measurable for `mT ⊗ m`, with `Y_τ = E[X_τ | m]` a.s. for `ν`-a.e. `τ`. Then
a.s. `E[∫ X_τ dν(τ) | m] = ∫ Y_τ dν(τ)`. -/
theorem condExp_integral_interchange [SFinite ν] [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {X Y : T → Ω → ℝ} (hX : Integrable (uncurry X) (ν.prod μ))
    (hY : @StronglyMeasurable (T × Ω) ℝ _ (@Prod.instMeasurableSpace T Ω mT m) (uncurry Y))
    (hXY : ∀ᵐ τ ∂ν, Y τ =ᵐ[μ] μ[X τ | m]) :
    μ[fun ω => ∫ τ, X τ ω ∂ν | m] =ᵐ[μ] fun ω => ∫ τ, Y τ ω ∂ν := by
  have hYi := integrable_uncurry_version hm hX hY hXY
  have hgm : StronglyMeasurable[m] (fun ω => ∫ τ, Y τ ω ∂ν) :=
    @StronglyMeasurable.integral_prod_left T Ω ℝ mT m ν _ _ _ Y hY
  have hf : Integrable (fun ω => ∫ τ, X τ ω ∂ν) μ := hX.integral_prod_right (f := uncurry X)
  have hg : Integrable (fun ω => ∫ τ, Y τ ω ∂ν) μ := hYi.integral_prod_right (f := uncurry Y)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hf (fun _ _ _ => hg.integrableOn)
    (fun A hA _ => ?_) hgm.aestronglyMeasurable).symm
  have rest : ∀ {Z : T → Ω → ℝ}, Integrable (uncurry Z) (ν.prod μ) →
      Integrable (uncurry Z) (ν.prod (μ.restrict A)) := fun {Z} hZ => by
    have e : ν.prod (μ.restrict A) = (ν.prod μ).restrict (Set.univ ×ˢ A) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [e]
    exact hZ.restrict
  rw [← integral_integral_swap (rest hYi), ← integral_integral_swap (rest hX)]
  refine integral_congr_ae ?_
  filter_upwards [hXY, (integrable_prod_iff hX.aestronglyMeasurable).1 hX |>.1] with τ hτ hXτ
  rw [setIntegral_congr_ae (hm A hA) (hτ.mono fun _ h _ => h)]
  exact setIntegral_condExp hm hXτ hA

/-- **Cochrane (2023), §3.6, pp. 70–79: the unconditional interchange** `E ∫ X_τ dν = ∫ E X_τ dν`
for `X` integrable on `ν ⊗ μ` (Mathlib `integral_integral_swap`). -/
theorem integral_integral_interchange [SFinite ν] [SFinite μ] {X : T → Ω → ℝ}
    (hX : Integrable (uncurry X) (ν.prod μ)) :
    ∫ ω, ∫ τ, X τ ω ∂ν ∂μ = ∫ τ, ∫ ω, X τ ω ∂μ ∂ν :=
  (integral_integral_swap hX).symm

/-- **Cochrane (2023), §3.6, pp. 70–79, p. 77: the conditional Fubini theorem from the
book-form hypotheses**: `X` jointly measurable, each `X_τ` integrable, `∫ E|X_τ| dν < ∞`
(e.g. `∫_0^∞ E|s_{t+τ}| e^{−rτ}dτ < ∞`), and a jointly `mT ⊗ m`-measurable version `Y`. -/
theorem condExp_integral_interchange_of_integral_abs [SFinite ν] [IsFiniteMeasure μ]
    (hm : m ≤ mΩ) {X Y : T → Ω → ℝ}
    (hXm : AEStronglyMeasurable (uncurry X) (ν.prod μ)) (hXi : ∀ᵐ τ ∂ν, Integrable (X τ) μ)
    (hXa : Integrable (fun τ => ∫ ω, |X τ ω| ∂μ) ν)
    (hY : @StronglyMeasurable (T × Ω) ℝ _ (@Prod.instMeasurableSpace T Ω mT m) (uncurry Y))
    (hXY : ∀ᵐ τ ∂ν, Y τ =ᵐ[μ] μ[X τ | m]) :
    μ[fun ω => ∫ τ, X τ ω ∂ν | m] =ᵐ[μ] fun ω => ∫ τ, Y τ ω ∂ν :=
  condExp_integral_interchange hm (integrable_uncurry_of_integral_abs hXm hXi hXa) hY hXY

/-- **Cochrane (2023), §3.6.3, pp. 76–79 (`Δ_t ∫ e^{−rτ}x_{t+τ}dτ = ∫ e^{−rτ}Δ_t x_{t+τ}dτ`):
the revision of an expected integral is the integral of the revisions.** For sub-σ-algebras
`m₁, m₂ ≤ mΩ` with versions `Y¹, Y²` as in `condExp_integral_interchange`, a.s.
`E[∫X | m₂] − E[∫X | m₁] = ∫ (Y²_τ − Y¹_τ) dν`. -/
theorem condExp_integral_revision [SFinite ν] [IsFiniteMeasure μ]
    (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ) {X Y₁ Y₂ : T → Ω → ℝ}
    (hX : Integrable (uncurry X) (ν.prod μ))
    (hY₁ : @StronglyMeasurable (T × Ω) ℝ _ (@Prod.instMeasurableSpace T Ω mT m₁) (uncurry Y₁))
    (hY₂ : @StronglyMeasurable (T × Ω) ℝ _ (@Prod.instMeasurableSpace T Ω mT m₂) (uncurry Y₂))
    (hXY₁ : ∀ᵐ τ ∂ν, Y₁ τ =ᵐ[μ] μ[X τ | m₁]) (hXY₂ : ∀ᵐ τ ∂ν, Y₂ τ =ᵐ[μ] μ[X τ | m₂]) :
    (fun ω => μ[fun ω => ∫ τ, X τ ω ∂ν | m₂] ω - μ[fun ω => ∫ τ, X τ ω ∂ν | m₁] ω) =ᵐ[μ]
      fun ω => ∫ τ, (Y₂ τ ω - Y₁ τ ω) ∂ν := by
  have i₁ := integrable_uncurry_version hm₁ hX hY₁ hXY₁
  have i₂ := integrable_uncurry_version hm₂ hX hY₂ hXY₂
  filter_upwards [condExp_integral_interchange hm₁ hX hY₁ hXY₁,
    condExp_integral_interchange hm₂ hX hY₂ hXY₂,
    (integrable_prod_iff' i₁.aestronglyMeasurable).1 i₁ |>.1,
    (integrable_prod_iff' i₂.aestronglyMeasurable).1 i₂ |>.1] with ω h1 h2 h3 h4
  rw [h1, h2, integral_sub (f := fun τ => Y₂ τ ω) (g := fun τ => Y₁ τ ω) h4 h3]

end Cochrane.Generality.TidyR8ConditionalFubini
