/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR10TwoBMIto
import Monetarism.TidyR9MonetarismItoPositive
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# The (1.32) product step when bonds and `Λ/P` load on independent shocks

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eq. (1.32). The step from the middle line of (1.32) to its last
line is `E_t d(BΛ/P) = (Λ/P) dB + B E_t d(Λ/P)`, with no covariation term. I5e
(TidyR7ItoBondStep) proved that with ONE Brownian motion the correct step carries the bracket
`E_t d[B, Λ/P] = σ_Bσ_X dt`, and left open the case of bonds and `Λ/P` driven by independent
shocks. Here bonds `B` (drift `β`, diffusions `σ_B¹`, `σ_B²`) and `X = Λ/P` (drift `ν`,
diffusions `σ_X¹`, `σ_X²`) are two-driver Itô processes
(`TidyR10TwoBMIto.ItoProcess2`) on a common admissible filtration of two independent Brownian
motions.

## Main results

* `twoBM_bond_step` (conditional form): a.s.
  `E_s[B_tX_t − B_sX_s] = E_s[∫_s^t B ν du + ∫_s^t X β du + ∫_s^t σ_B¹σ_X¹ du + ∫_s^t σ_B²σ_X² du]`:
  `E_t d(BΛ/P) = B E_t d(Λ/P) + (Λ/P) E_t dB + (σ_B¹σ_X¹ + σ_B²σ_X²) dt`.
* `twoBM_bond_step_book_iff`: the book's bracket-free step holds iff
  `E_s[∫σ_B¹σ_X¹ + ∫σ_B²σ_X²] = 0`; `twoBM_bond_step_of_bracket_zero`: it holds when
  `σ_B¹σ_X¹ + σ_B²σ_X² = 0` on `[s, t]` a.s.; `twoBM_bond_step_separate_drivers`: **it holds
  when bonds load only on `W²` and `Λ/P` only on `W¹`** (`σ_B¹ = 0`, `σ_X² = 0`), however
  diffusive both are.
* Independent-drivers economy (`indepX = 2 + sin W¹ ∈ [1, 3]`, `indepB = b + c sin W²`):
  `indepDrv_itoProcess2_X`, `indepDrv_itoProcess2_B`, `indepDrv_rate_eq` (the drift of `Λ/P`
  is `−i Λ/P` with `i = sin W¹/(2(2 + sin W¹))`, `|i| ≤ 1/2`), `indepDrv_book_holds` (**the book's
  step holds on every `[s, t]`**, although both `B` and `Λ/P` diffuse at all times), and
  `indepDrv_book_holds_bmPath` on the constructed pair. With `B = b + c sin W¹` instead (the same
  shock) the step fails (TidyR9MonetarismItoPositive, pos_book_fails).
* Correlated economy (`W³ = ρW¹ + √(1 − ρ²)W²`, `corrDrv_X = 2 + arctan W¹ > 0`,
  `corrDrv_B = b + cW³`): `corrDrv_itoProcess2_X`, `corrDrv_itoProcess2_B`, `corrDrv_bond_step`
  (**the bracket is `ρσ_Bσ_X = ρc/(1 + (W¹)²)`**), `corrDrv_book_iff` (**the book's step holds on
  `[s, t]` iff `ρc = 0`**, for every `0 ≤ s < t`), `corrDrv_book_iff_bmPath`.
-/

namespace Cochrane.Monetarism.TidyR10TwoBMBondStep

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoSums Cochrane.Monetarism.TidyR7ItoIntegral
  Cochrane.Monetarism.TidyR7ItoUnbounded Cochrane.Monetarism.TidyR7ItoProducts
  Cochrane.Monetarism.TidyR7ItoProcess Cochrane.Monetarism.TidyR7ItoProductRule
  Cochrane.Monetarism.TidyR7ItoBondStep Cochrane.Monetarism.TidyR9ItoFormula
  Cochrane.Monetarism.TidyR10TwoBMExist Cochrane.Monetarism.TidyR10TwoBMIto
  Cochrane.Monetarism.TidyR7BrownianSchauder Cochrane.Monetarism.TidyR7BrownianExist
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ}
  {W₁ W₂ : ℝ≥0 → Ω → ℝ} {s t : ℝ}
  {B X β ν σB₁ σB₂ σX₁ σX₂ : ℝ → Ω → ℝ} {Cβ CB₁ CB₂ Cν CX₁ CX₂ : ℝ}

/-! ## The product step with two shocks -/

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the product step with bonds and `Λ/P` loading on
two independent shocks, conditional form.** For two-driver Itô bonds `B` and `X = Λ/P` on
`[s, t]`, `0 ≤ s < t`, almost surely
`E_s[B_tX_t − B_sX_s] = E_s[∫_s^t B ν du + ∫_s^t X β du + ∫_s^t σ_B¹σ_X¹ du + ∫_s^t σ_B²σ_X² du]`.
The case `X := B`, `Y := X` of `TidyR10TwoBMIto.condExp_product_rule_two`. -/
theorem twoBM_bond_step (hB₁ : IsPreBrownianReal W₁ μ) (hB₂ : IsPreBrownianReal W₂ μ)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration μ W₁ W₂ 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hBo : ItoProcess2 μ 𝓕 W₁ W₂ B β σB₁ σB₂ s t Cβ CB₁ CB₂)
    (hX : ItoProcess2 μ 𝓕 W₁ W₂ X ν σX₁ σX₂ s t Cν CX₁ CX₂) :
    μ[fun ω => B t ω * X t ω - B s ω * X s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => dtInt μ 𝓕 (fun u ω => B u ω * ν u ω) s t ω
        + dtInt μ 𝓕 (fun u ω => X u ω * β u ω) s t ω
        + ((∫ u in s..t, σB₁ u ω * σX₁ u ω) + ∫ u in s..t, σB₂ u ω * σX₂ u ω) | 𝓕 s] :=
  condExp_product_rule_two hB₁ hB₂ hW₁ hW₂ h hs hst hBo hX

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: when the book's step is right, two shocks.** The
bracket-free step `E_s[B_tX_t − B_sX_s] = E_s[∫B ν du + ∫X β du]` holds a.s. **iff**
`E_s[∫_s^t σ_B¹σ_X¹ du + ∫_s^t σ_B²σ_X² du] = 0` a.s. -/
theorem twoBM_bond_step_book_iff (hB₁ : IsPreBrownianReal W₁ μ) (hB₂ : IsPreBrownianReal W₂ μ)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration μ W₁ W₂ 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hBo : ItoProcess2 μ 𝓕 W₁ W₂ B β σB₁ σB₂ s t Cβ CB₁ CB₂)
    (hX : ItoProcess2 μ 𝓕 W₁ W₂ X ν σX₁ σX₂ s t Cν CX₁ CX₂) :
    (μ[fun ω => B t ω * X t ω - B s ω * X s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => dtInt μ 𝓕 (fun u ω => B u ω * ν u ω) s t ω
        + dtInt μ 𝓕 (fun u ω => X u ω * β u ω) s t ω | 𝓕 s]) ↔
      μ[fun ω => (∫ u in s..t, σB₁ u ω * σX₁ u ω) + ∫ u in s..t, σB₂ u ω * σX₂ u ω | 𝓕 s]
        =ᵐ[μ] 0 :=
  condExp_product_rule_two_bookForm_iff hB₁ hB₂ hW₁ hW₂ h hs hst hBo hX

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the book's step when the total bracket density
vanishes.** If `σ_B¹σ_X¹ + σ_B²σ_X² = 0` on `[s, t]` a.s., the bracket-free step holds. -/
theorem twoBM_bond_step_of_bracket_zero (hB₁ : IsPreBrownianReal W₁ μ)
    (hB₂ : IsPreBrownianReal W₂ μ) (hW₁ : ∀ t, Measurable (W₁ t))
    (hW₂ : ∀ t, Measurable (W₂ t)) (h : TwoBMFiltration μ W₁ W₂ 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hBo : ItoProcess2 μ 𝓕 W₁ W₂ B β σB₁ σB₂ s t Cβ CB₁ CB₂)
    (hX : ItoProcess2 μ 𝓕 W₁ W₂ X ν σX₁ σX₂ s t Cν CX₁ CX₂)
    (hσ : ∀ᵐ ω ∂μ, ∀ u ∈ Set.Icc s t, σB₁ u ω * σX₁ u ω + σB₂ u ω * σX₂ u ω = 0) :
    μ[fun ω => B t ω * X t ω - B s ω * X s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => dtInt μ 𝓕 (fun u ω => B u ω * ν u ω) s t ω
        + dtInt μ 𝓕 (fun u ω => X u ω * β u ω) s t ω | 𝓕 s] := by
  refine (twoBM_bond_step_book_iff hB₁ hB₂ hW₁ hW₂ h hs hst hBo hX).2 ?_
  have e : (fun ω => (∫ u in s..t, σB₁ u ω * σX₁ u ω) + ∫ u in s..t, σB₂ u ω * σX₂ u ω)
      =ᵐ[μ] 0 := by
    filter_upwards [bracket_two_ae_eq hst.le hBo hX, hσ] with ω h1 h2
    rw [h1, Pi.zero_apply]
    have : ∀ u ∈ Set.uIcc s t, σB₁ u ω * σX₁ u ω + σB₂ u ω * σX₂ u ω = 0 := fun u hu => by
      rw [Set.uIcc_of_le hst.le] at hu
      exact h2 u hu
    rw [intervalIntegral.integral_congr this]
    simp
  filter_upwards [condExp_congr_ae (m := 𝓕 s) e] with ω hω
  rw [hω, condExp_zero]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the book's step when bonds and `Λ/P` load on
different independent shocks.** If bonds load only on `W²` (`σ_B¹ = 0`) and `Λ/P` only on `W¹`
(`σ_X² = 0`) on `[s, t]` a.s., the bracket-free step
`E_s[B_tX_t − B_sX_s] = E_s[∫B ν du + ∫X β du]` holds, however diffusive both are. -/
theorem twoBM_bond_step_separate_drivers (hB₁ : IsPreBrownianReal W₁ μ)
    (hB₂ : IsPreBrownianReal W₂ μ) (hW₁ : ∀ t, Measurable (W₁ t))
    (hW₂ : ∀ t, Measurable (W₂ t)) (h : TwoBMFiltration μ W₁ W₂ 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hBo : ItoProcess2 μ 𝓕 W₁ W₂ B β σB₁ σB₂ s t Cβ CB₁ CB₂)
    (hX : ItoProcess2 μ 𝓕 W₁ W₂ X ν σX₁ σX₂ s t Cν CX₁ CX₂)
    (hB0 : ∀ᵐ ω ∂μ, ∀ u ∈ Set.Icc s t, σB₁ u ω = 0)
    (hX0 : ∀ᵐ ω ∂μ, ∀ u ∈ Set.Icc s t, σX₂ u ω = 0) :
    μ[fun ω => B t ω * X t ω - B s ω * X s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => dtInt μ 𝓕 (fun u ω => B u ω * ν u ω) s t ω
        + dtInt μ 𝓕 (fun u ω => X u ω * β u ω) s t ω | 𝓕 s] := by
  refine twoBM_bond_step_of_bracket_zero hB₁ hB₂ hW₁ hW₂ h hs hst hBo hX ?_
  filter_upwards [hB0, hX0] with ω h1 h2 u hu
  rw [h1 u hu, h2 u hu]
  ring

/-! ## The independent-drivers economy: `Λ/P = 2 + sin W¹`, `B = b + c sin W²` -/

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (independent shocks): **the deflated price**
`Λ/P = 2 + sin W¹ ∈ [1, 3]`, loading only on `W¹`. -/
noncomputable def indepX (W₁ : ℝ≥0 → Ω → ℝ) (u : ℝ) (ω : Ω) : ℝ :=
  2 + 1 * Real.sin (bmReal W₁ u ω)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (independent shocks): **bonds** `B = b + c sin W²`,
loading only on `W²`. -/
noncomputable def indepB (W₂ : ℝ≥0 → Ω → ℝ) (b c : ℝ) (u : ℝ) (ω : Ω) : ℝ :=
  b + c * Real.sin (bmReal W₂ u ω)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (independent shocks): the nominal rate
`i = sin W¹/(2(2 + sin W¹))` forced by the bond-pricing drift of `Λ/P`. -/
noncomputable def indepI (W₁ : ℝ≥0 → Ω → ℝ) (u : ℝ) (ω : Ω) : ℝ :=
  Real.sin (bmReal W₁ u ω) / (2 * (2 + Real.sin (bmReal W₁ u ω)))

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (independent shocks): `1 ≤ Λ/P ≤ 3`. -/
theorem indepDrv_X_bounds (u : ℝ) (ω : Ω) : 1 ≤ indepX W₁ u ω ∧ indepX W₁ u ω ≤ 3 := by
  have h1 := Real.neg_one_le_sin (bmReal W₁ u ω)
  have h2 := Real.sin_le_one (bmReal W₁ u ω)
  simp only [indepX]
  constructor <;> linarith

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (independent shocks): **the drift of `Λ/P` is the
bond-pricing drift** `−(sin W¹)/2 = −i·Λ/P`, with `|i| ≤ 1/2`. -/
theorem indepDrv_rate_eq (u : ℝ) (ω : Ω) :
    -(1 * Real.sin (bmReal W₁ u ω) / 2) = -(indepI W₁ u ω * indepX W₁ u ω) ∧
      |indepI W₁ u ω| ≤ 1 / 2 := by
  have h1 := Real.neg_one_le_sin (bmReal W₁ u ω)
  have h2 := Real.abs_sin_le_one (bmReal W₁ u ω)
  have hpos : 0 < 2 + Real.sin (bmReal W₁ u ω) := by linarith
  refine ⟨?_, ?_⟩
  · simp only [indepI, indepX]
    field_simp
  · simp only [indepI]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (2 + Real.sin (bmReal W₁ u ω))),
      div_le_iff₀ (by positivity)]
    linarith

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (independent shocks): `Λ/P = 2 + sin W¹` is a
two-driver Itô process with drift `−sin W¹/2`, diffusions `cos W¹` and `0`
(TidyR9MonetarismItoPositive, itoProcess_affine_sin, for `W¹`). -/
theorem indepDrv_itoProcess2_X (hB₁ : IsPreBrownianReal W₁ μ) (hB₂ : IsPreBrownianReal W₂ μ)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (hc₁ : ∀ ω, Continuous fun t => W₁ t ω) (h : TwoBMFiltration μ W₁ W₂ 𝓕) (hs : 0 ≤ s) :
    ItoProcess2 μ 𝓕 W₁ W₂ (indepX W₁) (fun u ω => -(1 * Real.sin (bmReal W₁ u ω) / 2))
      (fun u ω => 1 * Real.cos (bmReal W₁ u ω)) (fun _ _ => 0) s t (|1| / 2) |1| 0 :=
  itoProcess2_of_itoProcess₁ (TidyR9MonetarismItoPositive.itoProcess_affine_sin (t := t) hB₁ hW₁
    h.bm1 hc₁ hs 2 1) hB₂ hW₂ h.bm2 hs

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (independent shocks): bonds `B = b + c sin W²` form
a two-driver Itô process with drift `−c sin W²/2`, diffusions `0` and `c cos W²`.
From `TidyR9MonetarismItoPositive.itoProcess_affine_sin` applied to `W²`. -/
theorem indepDrv_itoProcess2_B (hB₁ : IsPreBrownianReal W₁ μ) (hB₂ : IsPreBrownianReal W₂ μ)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (hc₂ : ∀ ω, Continuous fun t => W₂ t ω) (h : TwoBMFiltration μ W₁ W₂ 𝓕) (hs : 0 ≤ s)
    (b c : ℝ) :
    ItoProcess2 μ 𝓕 W₁ W₂ (indepB W₂ b c) (fun u ω => -(c * Real.sin (bmReal W₂ u ω) / 2))
      (fun _ _ => 0) (fun u ω => c * Real.cos (bmReal W₂ u ω)) s t (|c| / 2) 0 |c| :=
  itoProcess2_of_itoProcess₂ (TidyR9MonetarismItoPositive.itoProcess_affine_sin (t := t) hB₂ hW₂
    h.bm2 hc₂ hs b c) hB₁ hW₁ h.bm1 hs

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the book's step holds when bonds and `Λ/P` load
on independent shocks.** With `Λ/P = 2 + sin W¹ ∈ [1, 3]` and bonds `B = b + c sin W²`, both
diffusive at all times, on every `[s, t]`, `0 ≤ s < t`, a.s.
`E_s[B_tX_t − B_sX_s] = E_s[∫_s^t B ν du + ∫_s^t X β du]` with `ν = −sin W¹/2 = −i Λ/P` and
`β = −c sin W²/2`: the bracket `σ_B¹σ_X¹ + σ_B²σ_X² = 0·cos W¹ + c cos W²·0` vanishes. -/
theorem indepDrv_book_holds (hB₁ : IsPreBrownianReal W₁ μ) (hB₂ : IsPreBrownianReal W₂ μ)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (hc₁ : ∀ ω, Continuous fun t => W₁ t ω) (hc₂ : ∀ ω, Continuous fun t => W₂ t ω)
    (h : TwoBMFiltration μ W₁ W₂ 𝓕) (hs : 0 ≤ s) (hst : s < t) (b c : ℝ) :
    μ[fun ω => indepB W₂ b c t ω * indepX W₁ t ω - indepB W₂ b c s ω * indepX W₁ s ω | 𝓕 s]
      =ᵐ[μ] μ[fun ω => dtInt μ 𝓕 (fun u ω => indepB W₂ b c u ω
          * -(1 * Real.sin (bmReal W₁ u ω) / 2)) s t ω
        + dtInt μ 𝓕 (fun u ω => indepX W₁ u ω * -(c * Real.sin (bmReal W₂ u ω) / 2)) s t ω
          | 𝓕 s] :=
  twoBM_bond_step_separate_drivers hB₁ hB₂ hW₁ hW₂ h hs hst
    (indepDrv_itoProcess2_B hB₁ hB₂ hW₁ hW₂ hc₂ h hs b c)
    (indepDrv_itoProcess2_X hB₁ hB₂ hW₁ hW₂ hc₁ h hs)
    (ae_of_all _ fun _ _ _ => rfl) (ae_of_all _ fun _ _ _ => rfl)

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567 (non-vacuity): the independent-shocks economy on
the constructed pair** `TidyR10TwoBMExist.bmPath₁`, `bmPath₂`: `1 ≤ Λ/P ≤ 3`, `|i| ≤ 1/2`, and
the book's step holds on every `[s, t]`, `0 ≤ s < t`. -/
theorem indepDrv_book_holds_bmPath (hs : 0 ≤ s) (hst : s < t) (b c : ℝ) :
    (∀ u ω, 1 ≤ indepX bmPath₁ u ω ∧ indepX bmPath₁ u ω ≤ 3 ∧ |indepI bmPath₁ u ω| ≤ 1 / 2) ∧
    twoGauss[fun ω => indepB bmPath₂ b c t ω * indepX bmPath₁ t ω
        - indepB bmPath₂ b c s ω * indepX bmPath₁ s ω | twoBMF s]
      =ᵐ[twoGauss] twoGauss[fun ω => dtInt twoGauss twoBMF (fun u ω => indepB bmPath₂ b c u ω
          * -(1 * Real.sin (bmReal bmPath₁ u ω) / 2)) s t ω
        + dtInt twoGauss twoBMF (fun u ω => indepX bmPath₁ u ω
          * -(c * Real.sin (bmReal bmPath₂ u ω) / 2)) s t ω | twoBMF s] :=
  ⟨fun u ω => ⟨(indepDrv_X_bounds u ω).1, (indepDrv_X_bounds u ω).2,
      (indepDrv_rate_eq u ω).2⟩,
    indepDrv_book_holds isBrownianReal_bmPath₁.toIsPreBrownianReal
      isBrownianReal_bmPath₂.toIsPreBrownianReal measurable_bmPath₁ measurable_bmPath₂
      (fun ω => continuous_bmPath ω.1) (fun ω => continuous_bmPath ω.2)
      twoBMFiltration_bmPath_isTwoBM hs hst b c⟩

/-! ## The correlated economy: `Λ/P = 2 + arctan W¹`, `B = b + cW³` -/

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (correlated shocks): **the deflated price**
`Λ/P = 2 + arctan W¹ ∈ (2 − π/2, 2 + π/2)`, positive. -/
noncomputable def corrDrv_X (W₁ : ℝ≥0 → Ω → ℝ) (u : ℝ) (ω : Ω) : ℝ :=
  2 + Real.arctan (bmReal W₁ u ω)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (correlated shocks): **bonds** `B = b + cW³`,
`W³ = ρW¹ + √(1 − ρ²)W²` (`TidyR10TwoBMIto.corrBM`). -/
noncomputable def corrDrv_B (W₁ W₂ : ℝ≥0 → Ω → ℝ) (ρ b c : ℝ) (u : ℝ) (ω : Ω) : ℝ :=
  b + c * bmReal (corrBM ρ W₁ W₂) u ω

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (correlated shocks): the nominal rate
`i = W¹/((1 + (W¹)²)²(2 + arctan W¹))` forced by the bond-pricing drift of `Λ/P`. -/
noncomputable def corrDrv_I (W₁ : ℝ≥0 → Ω → ℝ) (u : ℝ) (ω : Ω) : ℝ :=
  bmReal W₁ u ω / ((1 + bmReal W₁ u ω ^ 2) ^ 2 * corrDrv_X W₁ u ω)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (correlated shocks): `Λ/P = 2 + arctan W¹ > 0`. -/
theorem corrDrv_X_pos (u : ℝ) (ω : Ω) : 0 < corrDrv_X W₁ u ω := by
  have h1 := Real.neg_pi_div_two_lt_arctan (bmReal W₁ u ω)
  have h2 := Real.pi_le_four
  simp only [corrDrv_X]
  linarith

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (correlated shocks): **the drift of `Λ/P` is the
bond-pricing drift** `−W¹/(1 + (W¹)²)² = −i·Λ/P`. -/
theorem corrDrv_rate_eq (u : ℝ) (ω : Ω) :
    -(bmReal W₁ u ω / (1 + bmReal W₁ u ω ^ 2) ^ 2) = -(corrDrv_I W₁ u ω * corrDrv_X W₁ u ω) := by
  have hX := (corrDrv_X_pos (W₁ := W₁) u ω).ne'
  have hD : (1 + bmReal W₁ u ω ^ 2) ^ 2 ≠ 0 := by positivity
  simp only [corrDrv_I]
  field_simp

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (correlated shocks): the second derivative of
`arctan`, `(1/(1 + x²))' = −2x/(1 + x²)²`. -/
theorem corrDrv_hasDerivAt_inv (x : ℝ) :
    HasDerivAt (fun y : ℝ => (1 + y ^ 2)⁻¹) (-(2 * x) / (1 + x ^ 2) ^ 2) x := by
  have h1 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add 1
  exact h1.inv (by positivity)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (correlated shocks): `|−2x/(1 + x²)²| ≤ 1`. -/
theorem corrDrv_abs_second_le (x : ℝ) : |-(2 * x) / (1 + x ^ 2) ^ 2| ≤ 1 := by
  have hD : 0 < (1 + x ^ 2) ^ 2 := by positivity
  rw [abs_div, abs_of_pos hD, div_le_one hD, abs_neg, abs_mul, abs_two]
  have h1 : 2 * |x| ≤ 1 + x ^ 2 := by
    nlinarith [sq_abs x, sq_nonneg (|x| - 1)]
  nlinarith [sq_nonneg x]

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (correlated shocks): `Λ/P = 2 + arctan W¹` is a
two-driver Itô process with drift `−W¹/(1 + (W¹)²)²` and diffusions `1/(1 + (W¹)²)` and `0`
(TidyR9ItoFormula, itoProcess_comp, for `W¹`). -/
theorem corrDrv_itoProcess2_X (hB₁ : IsPreBrownianReal W₁ μ) (hB₂ : IsPreBrownianReal W₂ μ)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (hc₁ : ∀ ω, Continuous fun t => W₁ t ω) (h : TwoBMFiltration μ W₁ W₂ 𝓕) (hs : 0 ≤ s) :
    ItoProcess2 μ 𝓕 W₁ W₂ (corrDrv_X W₁)
      (fun u ω => -(bmReal W₁ u ω / (1 + bmReal W₁ u ω ^ 2) ^ 2))
      (fun u ω => (1 + bmReal W₁ u ω ^ 2)⁻¹) (fun _ _ => 0) s t (1 * 0 + 1 / 2 * (1 * 1))
      (1 * 1) 0 := by
  have hcomp := itoProcess_comp (t := t) hB₁ hW₁ h.bm1 hs (itoProcess_bm hB₁ hW₁ h.bm1 hs)
    (ae_of_all _ fun ω => (continuous_bmReal (hc₁ ω)).continuousOn)
    (f := fun x => 2 + Real.arctan x) (f' := fun x => (1 + x ^ 2)⁻¹)
    (f'' := fun x => -(2 * x) / (1 + x ^ 2) ^ 2)
    (fun x => (Real.hasDerivAt_arctan' x).const_add 2) corrDrv_hasDerivAt_inv
    ((continuous_const.mul continuous_id).neg.div
      ((continuous_const.add (continuous_pow 2)).pow 2) fun x => by positivity)
    (L1 := 1) (L2 := 1)
    (fun x => by
      rw [abs_inv, abs_of_pos (by positivity : (0 : ℝ) < 1 + x ^ 2)]
      exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x]))
    corrDrv_abs_second_le
  refine itoProcess2_of_itoProcess₁ (itoProcess_of_coeff_eq hcomp (fun u ω => ?_)
    (fun u ω => ?_)) hB₂ hW₂ h.bm2 hs
  · have hD : (1 + bmReal W₁ u ω ^ 2) ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  · ring

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (correlated shocks): bonds `B = b + cW³` form a
two-driver Itô process with drift `0` and loadings `cρ` on `W¹`, `c√(1 − ρ²)` on `W²`
(`σ_B = c` along `W³`). -/
theorem corrDrv_itoProcess2_B (hB₁ : IsPreBrownianReal W₁ μ) (hB₂ : IsPreBrownianReal W₂ μ)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration μ W₁ W₂ 𝓕) (hs : 0 ≤ s) (ρ b c : ℝ) :
    ItoProcess2 μ 𝓕 W₁ W₂ (corrDrv_B W₁ W₂ ρ b c) (fun _ _ => 0) (fun _ _ => c * ρ)
      (fun _ _ => c * Real.sqrt (1 - ρ ^ 2)) s t 0 |c * ρ| |c * Real.sqrt (1 - ρ ^ 2)| where
  adapted u _ := stronglyMeasurable_const.add
    ((((h.bm1.adapted u).const_mul ρ).add
      ((h.bm2.adapted u).const_mul (Real.sqrt (1 - ρ ^ 2)))).const_mul c)
  init := by
    have : IsProbabilityMeasure μ := hB₁.isGaussianProcess.isProbabilityMeasure
    exact (memLp_const b).add ((((hB₁.isGaussianProcess.hasGaussianLaw_eval _).memLp_two.const_mul
      ρ).add ((hB₂.isGaussianProcess.hasGaussianLaw_eval _).memLp_two.const_mul _)).const_mul c)
  drift := itoIntegrand_const stronglyMeasurable_const (fun _ => by simp)
  diff1 := itoIntegrand_const stronglyMeasurable_const (fun _ => le_rfl)
  diff2 := itoIntegrand_const stronglyMeasurable_const (fun _ => le_rfl)
  eq u hu := by
    filter_upwards [itoInt_const hB₁ hW₁ h.bm1 hs hu.1 (c := fun _ => c * ρ)
      stronglyMeasurable_const (C := |c * ρ|) (fun _ => le_rfl),
      itoInt_const hB₂ hW₂ h.bm2 hs hu.1 (c := fun _ => c * Real.sqrt (1 - ρ ^ 2))
      stronglyMeasurable_const (C := |c * Real.sqrt (1 - ρ ^ 2)|) (fun _ => le_rfl)]
      with ω h1 h2
    rw [itoRHS2, h1, h2]
    simp only [corrDrv_B, bmReal, corrBM, incr, intervalIntegral.integral_zero, add_zero]
    ring

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the product step with correlated shocks; the
bracket is `ρσ_Bσ_X`.** With `Λ/P = 2 + arctan W¹` (`σ_X = 1/(1 + (W¹)²)` along `W¹`) and bonds
`B = b + cW³` (`σ_B = c` along `W³ = ρW¹ + √(1 − ρ²)W²`), on `[s, t]`, `0 ≤ s < t`, a.s.
`E_s[B_tX_t − B_sX_s] = E_s[∫B ν du + ∫X·0 du + ∫_s^t ρ c/(1 + (W¹_u)²) du]`: the `W²`-bracket
is `c√(1 − ρ²)·0` and the `W¹`-bracket `cρ·σ_X`. -/
theorem corrDrv_bond_step (hB₁ : IsPreBrownianReal W₁ μ) (hB₂ : IsPreBrownianReal W₂ μ)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (hc₁ : ∀ ω, Continuous fun t => W₁ t ω) (h : TwoBMFiltration μ W₁ W₂ 𝓕) (hs : 0 ≤ s)
    (hst : s < t) (ρ b c : ℝ) :
    μ[fun ω => corrDrv_B W₁ W₂ ρ b c t ω * corrDrv_X W₁ t ω
        - corrDrv_B W₁ W₂ ρ b c s ω * corrDrv_X W₁ s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => dtInt μ 𝓕 (fun u ω => corrDrv_B W₁ W₂ ρ b c u ω
          * -(bmReal W₁ u ω / (1 + bmReal W₁ u ω ^ 2) ^ 2)) s t ω
        + dtInt μ 𝓕 (fun u ω => corrDrv_X W₁ u ω * (fun _ _ => (0 : ℝ)) u ω) s t ω
        + ρ * c * ∫ u in s..t, (1 + bmReal W₁ u ω ^ 2)⁻¹ | 𝓕 s] := by
  have hh := twoBM_bond_step hB₁ hB₂ hW₁ hW₂ h hs hst
    (corrDrv_itoProcess2_B (t := t) hB₁ hB₂ hW₁ hW₂ h hs ρ b c)
    (corrDrv_itoProcess2_X hB₁ hB₂ hW₁ hW₂ hc₁ h hs)
  refine hh.trans (condExp_congr_ae (ae_of_all _ fun ω => ?_))
  simp only [mul_zero, intervalIntegral.integral_zero, add_zero,
    intervalIntegral.integral_const_mul]
  ring

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: with correlated shocks the book's step holds iff
the correlation (or the bond loading) is zero.** In the economy of `corrDrv_bond_step`, on any
`[s, t]` with `0 ≤ s < t`, the bracket-free step
`E_s[B_tX_t − B_sX_s] = E_s[∫B ν du + ∫X β du]` holds a.s. **iff** `ρc = 0`: the bracket
`ρc∫_s^t du/(1 + (W¹_u)²)` has `E_s` zero only if `ρc = 0`, its integral being positive for every
path. -/
theorem corrDrv_book_iff (hB₁ : IsPreBrownianReal W₁ μ) (hB₂ : IsPreBrownianReal W₂ μ)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (hc₁ : ∀ ω, Continuous fun t => W₁ t ω) (h : TwoBMFiltration μ W₁ W₂ 𝓕) (hs : 0 ≤ s)
    (hst : s < t) (ρ b c : ℝ) :
    (μ[fun ω => corrDrv_B W₁ W₂ ρ b c t ω * corrDrv_X W₁ t ω
        - corrDrv_B W₁ W₂ ρ b c s ω * corrDrv_X W₁ s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => dtInt μ 𝓕 (fun u ω => corrDrv_B W₁ W₂ ρ b c u ω
          * -(bmReal W₁ u ω / (1 + bmReal W₁ u ω ^ 2) ^ 2)) s t ω
        + dtInt μ 𝓕 (fun u ω => corrDrv_X W₁ u ω * (fun _ _ => (0 : ℝ)) u ω) s t ω | 𝓕 s])
      ↔ ρ * c = 0 := by
  have : IsProbabilityMeasure μ := hB₁.isGaussianProcess.isProbabilityMeasure
  have hX := corrDrv_itoProcess2_X hB₁ hB₂ hW₁ hW₂ hc₁ h hs (t := t)
  rw [twoBM_bond_step_book_iff hB₁ hB₂ hW₁ hW₂ h hs hst
    (corrDrv_itoProcess2_B (t := t) hB₁ hB₂ hW₁ hW₂ h hs ρ b c) hX]
  set J : Ω → ℝ := fun ω => ∫ u in s..t, (1 + bmReal W₁ u ω ^ 2)⁻¹ with hJ
  have eQ : (fun ω => (∫ u in s..t, c * ρ * (1 + bmReal W₁ u ω ^ 2)⁻¹)
      + ∫ u in s..t, c * Real.sqrt (1 - ρ ^ 2) * (fun _ _ => (0 : ℝ)) u ω)
      = fun ω => ρ * c * J ω := by
    funext ω
    simp only [hJ, mul_zero, intervalIntegral.integral_zero, add_zero,
      intervalIntegral.integral_const_mul]
    ring
  rw [eQ]
  have iJ : Integrable J μ :=
    (memLp_integral_drift hX.diff1 le_rfl hst.le le_rfl).integrable one_le_two
  have Jpos : ∀ ω, 0 < J ω := fun ω => by
    have hcont : Continuous fun u => (1 + bmReal W₁ u ω ^ 2)⁻¹ :=
      ((continuous_const.add ((continuous_bmReal (hc₁ ω)).pow 2)).inv₀ fun u =>
        (by positivity : (0 : ℝ) < 1 + bmReal W₁ u ω ^ 2).ne')
    exact intervalIntegral.intervalIntegral_pos_of_pos_on
      (hcont.intervalIntegrable _ _)
      (fun u _ => inv_pos.2 (by positivity : (0 : ℝ) < 1 + bmReal W₁ u ω ^ 2)) hst
  have hEJ : 0 < ∫ ω, J ω ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (fun ω => (Jpos ω).le) iJ]
    have hsupp : Function.support J = Set.univ := by
      ext ω
      simp only [Function.mem_support, ne_eq, Set.mem_univ, iff_true]
      exact (Jpos ω).ne'
    rw [hsupp, measure_univ]
    exact one_pos
  constructor
  · intro hh
    have hE := integral_condExp (μ := μ) (f := fun ω => ρ * c * J ω) (𝓕.le s)
    rw [integral_congr_ae hh, integral_const_mul] at hE
    simp only [Pi.zero_apply, integral_zero] at hE
    rcases mul_eq_zero.1 hE.symm with h0 | h0
    · exact h0
    · exact absurd h0 hEJ.ne'
  · intro hρ
    have e : (fun ω => ρ * c * J ω) = 0 := by
      funext ω
      rw [hρ, zero_mul, Pi.zero_apply]
    rw [e, condExp_zero]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567 (non-vacuity): the correlated economy on the
constructed pair**: `Λ/P = 2 + arctan W¹ > 0`, and on every `[s, t]`, `0 ≤ s < t`, the book's
step holds iff `ρc = 0`; in particular it FAILS for `ρ = 1/2`, `c = 1`. -/
theorem corrDrv_book_iff_bmPath (hs : 0 ≤ s) (hst : s < t) (ρ b c : ℝ) :
    (∀ u ω, 0 < corrDrv_X bmPath₁ u ω) ∧
    ((twoGauss[fun ω => corrDrv_B bmPath₁ bmPath₂ ρ b c t ω * corrDrv_X bmPath₁ t ω
        - corrDrv_B bmPath₁ bmPath₂ ρ b c s ω * corrDrv_X bmPath₁ s ω | twoBMF s]
      =ᵐ[twoGauss] twoGauss[fun ω => dtInt twoGauss twoBMF (fun u ω =>
          corrDrv_B bmPath₁ bmPath₂ ρ b c u ω
          * -(bmReal bmPath₁ u ω / (1 + bmReal bmPath₁ u ω ^ 2) ^ 2)) s t ω
        + dtInt twoGauss twoBMF (fun u ω => corrDrv_X bmPath₁ u ω * (fun _ _ => (0 : ℝ)) u ω)
          s t ω | twoBMF s]) ↔ ρ * c = 0) :=
  ⟨fun u ω => corrDrv_X_pos u ω,
    corrDrv_book_iff isBrownianReal_bmPath₁.toIsPreBrownianReal
      isBrownianReal_bmPath₂.toIsPreBrownianReal measurable_bmPath₁ measurable_bmPath₂
      (fun ω => continuous_bmPath ω.1) twoBMFiltration_bmPath_isTwoBM hs hst ρ b c⟩

end Cochrane.Monetarism.TidyR10TwoBMBondStep
