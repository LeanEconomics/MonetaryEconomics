/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR10TwoBMCross
import Monetarism.TidyR7ItoBondStep

/-!
# Itô calculus with two independent drivers: `d(XY) = X dY + Y dX + (H¹K¹ + H²K²) dt`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for (1.32) when bonds and `Λ/P`
load on two independent shocks (Track 3, chunk B2).

## Itô integrals per driver

The Itô integral of TidyR7ItoIntegral, `itoInt P 𝓕 W H s t`, needs of the integrator only
`IsPreBrownianReal W P`, measurable values and an admissible filtration
`TidyR7BrownianQV.BMFiltration P W 𝓕`. A common filtration
`TidyR10TwoBMExist.TwoBMFiltration P W¹ W² 𝓕` is admissible for each driver (its fields
`TidyR10TwoBMExist.TwoBMFiltration.bm1`, `TidyR10TwoBMExist.TwoBMFiltration.bm2`), so
`∫ H dW¹` and `∫ K dW²` exist on the same filtration, with all the I5c properties
(`itoInt_isometry_two`, `martingale_itoInt_two`).

## Two-driver Itô processes

`ItoProcess2 P 𝓕 W¹ W² X a H¹ H² s t`: `X` adapted, `X_s ∈ L²`, `a, H¹, H²` bounded admissible,
and `X_u = X_s + ∫_s^u a dr + ∫_s^u H¹ dW¹ + ∫_s^u H² dW²` a.s. Every such `X` splits EXACTLY as
`X = X¹ + X²` with `X² = ∫_s^· H² dW²` an Itô process for `W²` (drift `0`) and
`X¹ = X − X²` an Itô process for `W¹` (drift `a`, diffusion `H¹`)
(`ItoProcess2.part₁_ito`, `ItoProcess2.part₂_ito`). Every one-driver Itô process is a two-driver
one (`itoProcess2_of_itoProcess₁`, `itoProcess2_of_itoProcess₂`).

## Main results

* `tendsto_integral_abs_sumCross_indep` (**no bracket between independent drivers**): for `X` an
  Itô process for `W¹` and `Y` one for `W²`, `Σ ΔX_iΔY_i → 0` in `L¹`: the main term
  `Σ H_iK_iΔW¹_iΔW²_i` vanishes by `TidyR10TwoBMCross.L2Tendsto_wcvSum`.
* `tendsto_integral_abs_sumCross_two` (**the bracket of two-driver processes**):
  `Σ ΔX_iΔY_i → ∫H¹K¹ du + ∫H²K² du` in `L¹` (the per-driver brackets of I5d,
  `TidyR7ItoCovariation.tendsto_integral_abs_sumCross`, plus the two vanishing cross brackets).
* `L2Tendsto_sumRS_two`: `Σ Z_iΔY_i → ∫Z b du + ∫Z K¹ dW¹ + ∫Z K² dW²` in `L²`.
* `product_rule_two` (**Itô's product rule with two drivers**): a.s.
  `X_tY_t − X_sY_s = ∫X dY + ∫Y dX + ∫_s^t H¹K¹ du + ∫_s^t H²K² du`;
  `bracket_two_ae_eq` (the two brackets are `∫(H¹K¹ + H²K²) du` a.s.).
* `condExp_product_rule_two`: `E_s[X_tY_t − X_sY_s] = E_s[∫Xb + ∫Ya + ∫H¹K¹ + ∫H²K²]`;
  `condExp_product_rule_two_bookForm_iff`: the bracket-free form holds iff
  `E_s[∫H¹K¹ + ∫H²K²] = 0`.
* `integral_itoInt_mul_itoInt_indep`: `E[(∫_s^t H dW¹)(∫_s^t K dW²)] = 0`.
* The correlated motion `W³ = ρW¹ + √(1 − ρ²)W²` (`corrBM`): `itoProcess2_corrBM` (an Itô
  process with loadings `ρ`, `√(1 − ρ²)`), `L2Tendsto_crossSum_corrBM` and
  `tendsto_integral_abs_sumCross_corrBM` (**`d[W¹, W³] = ρ dt`**: `Σ ΔW¹_iΔW³_i → ρ(t − s)`).
* Non-vacuity on `TidyR10TwoBMExist.bmPath₁`, `bmPath₂`: `product_rule_two_bmPath`
  (`W¹_tW²_t = ∫W¹ dW² + ∫W² dW¹`, no bracket), `tendsto_crossSum_corrBM_bmPath`.
-/

namespace Cochrane.Monetarism.TidyR10TwoBMIto

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoSums Cochrane.Monetarism.TidyR7ItoIntegral
  Cochrane.Monetarism.TidyR7ItoUnbounded Cochrane.Monetarism.TidyR7ItoProducts
  Cochrane.Monetarism.TidyR7ItoProcess Cochrane.Monetarism.TidyR7ItoCovariation
  Cochrane.Monetarism.TidyR7ItoProductRule Cochrane.Monetarism.TidyR7ItoBondStep
  Cochrane.Monetarism.TidyR7StieltjesCalculus Cochrane.Monetarism.TidyR10TwoBMExist
  Cochrane.Monetarism.TidyR10TwoBMCross
open Cochrane.Monetarism.TidyR7ProductStep (sumRS sumCross)
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ mΩ}
  {W₁ W₂ : ℝ≥0 → Ω → ℝ} {s t : ℝ}

/-! ## Itô integrals against each driver -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the Itô isometry against each driver on the common
filtration**: for a common admissible filtration, `E[(∫_s^t H dWʲ)²] = E[∫_s^t H² du]` for
`j = 1, 2`, `0 ≤ s ≤ t` (I5c's `TidyR7ItoIntegral.integral_itoInt_sq`, applied with the fields
`TidyR10TwoBMExist.TwoBMFiltration.bm1` and `TidyR10TwoBMExist.TwoBMFiltration.bm2`). -/
theorem itoInt_isometry_two (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration P W₁ W₂ 𝓕) (hs : 0 ≤ s) (hst : s ≤ t) {H : ℝ → Ω → ℝ} {C : ℝ}
    (hH : ItoIntegrand P 𝓕 H s t C) :
    ∫ ω, itoInt P 𝓕 W₁ H s t ω ^ 2 ∂P = ∫ ω, (∫ u in s..t, H u ω ^ 2) ∂P ∧
      ∫ ω, itoInt P 𝓕 W₂ H s t ω ^ 2 ∂P = ∫ ω, (∫ u in s..t, H u ω ^ 2) ∂P :=
  ⟨integral_itoInt_sq hB₁ hW₁ h.bm1 hs hst hH, integral_itoInt_sq hB₂ hW₂ h.bm2 hs hst hH⟩

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: both running Itô integrals are martingales for the
common filtration** (I5c's `TidyR7ItoIntegral.martingale_itoInt` per driver). -/
theorem martingale_itoInt_two (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration P W₁ W₂ 𝓕) (hs : 0 ≤ s) {H : ℝ → Ω → ℝ} {C : ℝ}
    (hH : ∀ T, ItoIntegrand P 𝓕 H s T C) :
    Martingale (fun u => itoInt P 𝓕 W₁ H s u) 𝓕 P ∧
      Martingale (fun u => itoInt P 𝓕 W₂ H s u) 𝓕 P :=
  ⟨martingale_itoInt hB₁ hW₁ h.bm1 hs hH, martingale_itoInt hB₂ hW₂ h.bm2 hs hH⟩

/-! ## Two-driver Itô processes -/

variable (P 𝓕 W₁ W₂) (X a H₁ H₂ : ℝ → Ω → ℝ) (s t Ca C₁ C₂ : ℝ)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the right side
`X_s + ∫_s^u a dr + ∫_s^u H¹ dW¹ + ∫_s^u H² dW²` of a two-driver Itô process. -/
noncomputable def itoRHS2 (u : ℝ) (ω : Ω) : ℝ :=
  X s ω + (∫ r in s..u, a r ω) + itoInt P 𝓕 W₁ H₁ s u ω + itoInt P 𝓕 W₂ H₂ s u ω

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: an Itô process driven by two Brownian motions on
`[s, t]`** (bonds and `Λ/P` loading on two shocks): `X` adapted, `X_s` square integrable, `a`,
`H¹`, `H²` bounded admissible integrands, and
`X_u = X_s + ∫_s^u a dr + ∫_s^u H¹ dW¹ + ∫_s^u H² dW²` a.s. for each `u ∈ [s, t]`. -/
structure ItoProcess2 where
  adapted : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (X u)
  init : MemLp (X s) 2 P
  drift : ItoIntegrand P 𝓕 a s t Ca
  diff1 : ItoIntegrand P 𝓕 H₁ s t C₁
  diff2 : ItoIntegrand P 𝓕 H₂ s t C₂
  eq : ∀ u ∈ Set.Icc s t, X u =ᵐ[P] itoRHS2 P 𝓕 W₁ W₂ X a H₁ H₂ s u

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the `W¹`-part** `X¹ = X − ∫_s^· H² dW²` of a
two-driver process. -/
noncomputable def part₁ (u : ℝ) (ω : Ω) : ℝ := X u ω - itoInt P 𝓕 W₂ H₂ s u ω

variable {P 𝓕 W₁ W₂ X a H₁ H₂ s t Ca C₁ C₂}

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `X = X¹ + ∫_s^· H² dW²` exactly. -/
theorem part₁_add (u : ℝ) (ω : Ω) :
    part₁ P 𝓕 W₂ X H₂ s u ω + itoInt P 𝓕 W₂ H₂ s u ω = X u ω := sub_add_cancel _ _

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the `W¹`-part is a one-driver Itô process** for
`W¹`, with the drift `a` and diffusion `H¹` of `X`. -/
theorem ItoProcess2.part₁_ito (hX : ItoProcess2 P 𝓕 W₁ W₂ X a H₁ H₂ s t Ca C₁ C₂) :
    ItoProcess P 𝓕 W₁ (part₁ P 𝓕 W₂ X H₂ s) a H₁ s t Ca C₁ where
  adapted u hu := (hX.adapted u hu).sub stronglyMeasurable_itoInt
  init := by
    have e : part₁ P 𝓕 W₂ X H₂ s s = X s := by
      funext ω
      simp [part₁, itoInt_of_le (le_refl s)]
    rw [e]
    exact hX.init
  drift := hX.drift
  diff := hX.diff1
  eq u hu := by
    filter_upwards [hX.eq u hu] with ω hω
    simp only [part₁, itoInt_of_le (le_refl s), Pi.zero_apply, sub_zero]
    rw [hω, itoRHS2]
    ring

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the `W²`-part** `∫_s^· H² dW²` is a one-driver Itô
process for `W²` with drift `0`. -/
theorem ItoProcess2.part₂_ito [IsFiniteMeasure P]
    (hX : ItoProcess2 P 𝓕 W₁ W₂ X a H₁ H₂ s t Ca C₁ C₂) :
    ItoProcess P 𝓕 W₂ (fun u ω => itoInt P 𝓕 W₂ H₂ s u ω) (fun _ _ => 0) H₂ s t 0 C₂ :=
  itoProcess_itoInt hX.diff2

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: a two-driver Itô process is a mean-square
continuous integrand**, as the sum of its two parts (`TidyR7ItoProcess.ItoProcess.toMS`). -/
theorem ItoProcess2.toMS (hX : ItoProcess2 P 𝓕 W₁ W₂ X a H₁ H₂ s t Ca C₁ C₂)
    (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration P W₁ W₂ 𝓕) (hs : 0 ≤ s) : MSIntegrand P 𝓕 X s t := by
  have : IsProbabilityMeasure P := hB₁.isGaussianProcess.isProbabilityMeasure
  have hm := MSIntegrand.add (hX.part₁_ito.toMS hB₁ hW₁ h.bm1 hs)
    (hX.part₂_ito.toMS hB₂ hW₂ h.bm2 hs)
  have e : (fun u ω => part₁ P 𝓕 W₂ X H₂ s u ω + itoInt P 𝓕 W₂ H₂ s u ω) = X :=
    funext fun u => funext fun ω => part₁_add u ω
  rw [e] at hm
  exact hm

/-- Cochrane (2023), A1 §1.6, pp. 567–568: a two-driver Itô process is square integrable. -/
theorem ItoProcess2.memLp (hX : ItoProcess2 P 𝓕 W₁ W₂ X a H₁ H₂ s t Ca C₁ C₂)
    (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration P W₁ W₂ 𝓕) (hs : 0 ≤ s) {u : ℝ} (hu : u ∈ Set.Icc s t) :
    MemLp (X u) 2 P :=
  (hX.toMS hB₁ hB₂ hW₁ hW₂ h hs).memLp u hu

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: a one-driver Itô process for `W¹` is a two-driver
one**, with second diffusion `0` (`∫ 0 dW² = 0`). -/
theorem itoProcess2_of_itoProcess₁ {Y b K : ℝ → Ω → ℝ} {Cb CK : ℝ}
    (hY : ItoProcess P 𝓕 W₁ Y b K s t Cb CK) (hB₂ : IsPreBrownianReal W₂ P)
    (hW₂ : ∀ t, Measurable (W₂ t)) (h𝓕 : BMFiltration P W₂ 𝓕) (hs : 0 ≤ s) :
    ItoProcess2 P 𝓕 W₁ W₂ Y b K (fun _ _ => 0) s t Cb CK 0 where
  adapted := hY.adapted
  init := hY.init
  drift := hY.drift
  diff1 := hY.diff
  diff2 := itoIntegrand_const stronglyMeasurable_const (fun _ => by simp)
  eq u hu := by
    filter_upwards [hY.eq u hu, itoInt_const hB₂ hW₂ h𝓕 hs hu.1 (c := fun _ => (0 : ℝ))
      stronglyMeasurable_const (C := 0) (fun _ => by simp)] with ω h1 h2
    rw [itoRHS2, h1, h2, zero_mul, add_zero]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: a one-driver Itô process for `W²` is a two-driver
one**, with first diffusion `0`. -/
theorem itoProcess2_of_itoProcess₂ {Y b K : ℝ → Ω → ℝ} {Cb CK : ℝ}
    (hY : ItoProcess P 𝓕 W₂ Y b K s t Cb CK) (hB₁ : IsPreBrownianReal W₁ P)
    (hW₁ : ∀ t, Measurable (W₁ t)) (h𝓕 : BMFiltration P W₁ 𝓕) (hs : 0 ≤ s) :
    ItoProcess2 P 𝓕 W₁ W₂ Y b (fun _ _ => 0) K s t Cb 0 CK where
  adapted := hY.adapted
  init := hY.init
  drift := hY.drift
  diff1 := itoIntegrand_const stronglyMeasurable_const (fun _ => by simp)
  diff2 := hY.diff
  eq u hu := by
    filter_upwards [hY.eq u hu, itoInt_const hB₁ hW₁ h𝓕 hs hu.1 (c := fun _ => (0 : ℝ))
      stronglyMeasurable_const (C := 0) (fun _ => by simp)] with ω h1 h2
    rw [itoRHS2, h1, h2, zero_mul, add_zero]

/-! ## Sums -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the cross sum of square-integrable processes is
integrable.
Generalises `TidyR7ItoProductRule.integrable_sumCross` to square-integrable processes. -/
theorem integrable_sumCross_of_memLp {X Y : ℝ → Ω → ℝ} (hX : ∀ u ∈ Set.Icc s t, MemLp (X u) 2 P)
    (hY : ∀ u ∈ Set.Icc s t, MemLp (Y u) 2 P) (p : Partition s t) :
    Integrable (sumCross p X Y) P :=
  (integrable_finsetSum (Finset.range p.n) fun _ hi =>
    ((hX _ (t_mem p (Finset.mem_range.1 hi))).sub
      (hX _ (t_mem p (Finset.mem_range.1 hi).le))).integrable_mul
    ((hY _ (t_mem p (Finset.mem_range.1 hi))).sub
      (hY _ (t_mem p (Finset.mem_range.1 hi).le)))).congr
    (ae_of_all _ fun _ => rfl)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the cross sum is bilinear: for `X = X¹ + X²`,
`Y = Y¹ + Y²`, `Σ ΔXΔY = Σ ΔX¹ΔY¹ + Σ ΔX¹ΔY² + Σ ΔX²ΔY¹ + Σ ΔX²ΔY²`. -/
theorem sumCross_split {X Y X₁ X₂ Y₁ Y₂ : ℝ → Ω → ℝ} (hX : ∀ u ω, X u ω = X₁ u ω + X₂ u ω)
    (hY : ∀ u ω, Y u ω = Y₁ u ω + Y₂ u ω) (p : Partition s t) (ω : Ω) :
    sumCross p X Y ω = sumCross p X₁ Y₁ ω + sumCross p X₁ Y₂ ω + sumCross p X₂ Y₁ ω
      + sumCross p X₂ Y₂ ω := by
  simp only [sumCross, crossSum, hX, hY, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the left-point sum is linear in the integrator: for
`Y = Y¹ + Y²`, `Σ Z_iΔY_i = Σ Z_iΔY¹_i + Σ Z_iΔY²_i`. -/
theorem sumRS_split {Z Y Y₁ Y₂ : ℝ → Ω → ℝ} (hY : ∀ u ω, Y u ω = Y₁ u ω + Y₂ u ω)
    (p : Partition s t) (ω : Ω) :
    sumRS p Z Y ω = sumRS p Z Y₁ ω + sumRS p Z Y₂ ω := by
  simp only [sumRS, rsSum, hY, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-! ## No bracket between independent drivers -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (`dW¹dW² = 0` for Itô processes): no bracket
between independent drivers.** For a common admissible filtration, `X` an Itô process for `W¹`
(drift `a`, diffusion `H`) and `Y` an Itô process for `W²` (drift `b`, diffusion `K`) on
`[s, t]`, `0 ≤ s < t`: `Σ ΔX_iΔY_i → 0` in `L¹` along any partitions with mesh `→ 0`.
The proof of `TidyR7ItoCovariation.tendsto_integral_abs_sumCross` with the main term
`Σ H_iK_i(ΔW_i)²` replaced by `Σ H_iK_iΔW¹_iΔW²_i → 0`
(`TidyR10TwoBMCross.L2Tendsto_wcvSum`). -/
theorem tendsto_integral_abs_sumCross_indep (hB₁ : IsPreBrownianReal W₁ P)
    (hB₂ : IsPreBrownianReal W₂ P) (hW₁ : ∀ t, Measurable (W₁ t))
    (hW₂ : ∀ t, Measurable (W₂ t)) (h : TwoBMFiltration P W₁ W₂ 𝓕) (hs : 0 ≤ s)
    {X Y a b H K : ℝ → Ω → ℝ} {Ca CH Cb CK : ℝ} (hX : ItoProcess P 𝓕 W₁ X a H s t Ca CH)
    (hY : ItoProcess P 𝓕 W₂ Y b K s t Cb CK) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, |sumCross (ps k) X Y ω| ∂P) atTop (𝓝 0) := by
  have : IsProbabilityMeasure P := hB₁.isGaussianProcess.isProbabilityMeasure
  set HK : ℝ → Ω → ℝ := fun u ω => H u ω * K u ω with hHK
  have hHKa : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (HK u) := fun u hu =>
    (hX.diff.adapted u hu).mul (hY.diff.adapted u hu)
  have hHKb : ∀ u ∈ Set.Icc s t, ∀ ω, |HK u ω| ≤ CH * CK := fun u hu ω => by
    simp only [hHK, abs_mul]
    exact mul_le_mul (hX.diff.bound u hu ω) (hY.diff.bound u hu ω) (abs_nonneg _)
      ((abs_nonneg _).trans (hX.diff.bound u hu ω))
  set A : ℕ → ℕ → Ω → ℝ := fun k i ω => ∫ r in (ps k).t i..(ps k).t (i + 1), a r ω with hA
  set Bt : ℕ → ℕ → Ω → ℝ := fun k i ω => ∫ r in (ps k).t i..(ps k).t (i + 1), b r ω with hBt
  set R : ℕ → ℕ → Ω → ℝ := fun k i => itoInt P 𝓕 W₁ (fun r ω => H r ω - H ((ps k).t i) ω)
    ((ps k).t i) ((ps k).t (i + 1)) with hR
  set S : ℕ → ℕ → Ω → ℝ := fun k i => itoInt P 𝓕 W₂ (fun r ω => K r ω - K ((ps k).t i) ω)
    ((ps k).t i) ((ps k).t (i + 1)) with hS
  set β : ℕ → ℕ → Ω → ℝ := fun k i ω =>
    H ((ps k).t i) ω * incr W₁ ((ps k).t i) ((ps k).t (i + 1)) ω with hβ
  set dY : ℕ → ℕ → Ω → ℝ := fun k i ω => Y ((ps k).t (i + 1)) ω - Y ((ps k).t i) ω with hdY
  have mA : ∀ k, ∀ i < (ps k).n, MemLp (A k i) 2 P := fun k i hi =>
    memLp_integral_drift hX.drift (t_mem _ hi.le).1 (t_le_succ _ i) (t_mem _ hi).2
  have mB : ∀ k, ∀ i < (ps k).n, MemLp (Bt k i) 2 P := fun k i hi =>
    memLp_integral_drift hY.drift (t_mem _ hi.le).1 (t_le_succ _ i) (t_mem _ hi).2
  have mR : ∀ k, ∀ i < (ps k).n, MemLp (R k i) 2 P := fun k i hi =>
    memLp_itoInt hB₁ hW₁ h.bm1 (hs.trans (t_mem _ hi.le).1)
      (itoIntegrand_sub_left (t_le_succ _ i) (hX.diff.mono (t_mem _ hi.le).1 (t_mem _ hi).2))
  have mS : ∀ k, ∀ i < (ps k).n, MemLp (S k i) 2 P := fun k i hi =>
    memLp_itoInt hB₂ hW₂ h.bm2 (hs.trans (t_mem _ hi.le).1)
      (itoIntegrand_sub_left (t_le_succ _ i) (hY.diff.mono (t_mem _ hi.le).1 (t_mem _ hi).2))
  have mβ : ∀ k, ∀ i < (ps k).n, MemLp (β k i) 2 P := fun k i hi =>
    memLp_mul_incr_of_memLp hB₁ hW₁ h.bm1 (t_le_succ _ i) (hX.diff.adapted _ (t_mem _ hi.le))
      (memLp_of_bound (hX.diff.measurable (t_mem _ hi.le)) (hX.diff.bound _ (t_mem _ hi.le)))
  have mdY : ∀ k, ∀ i < (ps k).n, MemLp (dY k i) 2 P := fun k i hi =>
    (hY.memLp hB₂ hW₂ h.bm2 hs (t_mem _ hi)).sub (hY.memLp hB₂ hW₂ h.bm2 hs (t_mem _ hi.le))
  have mBS : ∀ k, ∀ i < (ps k).n, MemLp (fun ω => Bt k i ω + S k i ω) 2 P := fun k i hi =>
    (mB k i hi).add (mS k i hi)
  -- the pathwise split
  have hsplit : ∀ k, (fun ω => sumCross (ps k) X Y ω) =ᵐ[P] fun ω =>
      wcvSum W₁ W₂ HK (ps k) ω
        + ∑ i ∈ Finset.range (ps k).n, A k i ω * dY k i ω
        + ∑ i ∈ Finset.range (ps k).n, (Bt k i ω + S k i ω) * β k i ω
        + ∑ i ∈ Finset.range (ps k).n, R k i ω * dY k i ω := by
    intro k
    have hall : ∀ᵐ ω ∂P, ∀ i, i < (ps k).n →
        (X ((ps k).t (i + 1)) ω - X ((ps k).t i) ω) * dY k i ω
          = HK ((ps k).t i) ω * cvTerm W₁ W₂ ((ps k).t i) ((ps k).t (i + 1)) ω
            + A k i ω * dY k i ω + (Bt k i ω + S k i ω) * β k i ω + R k i ω * dY k i ω := by
      refine ae_all_iff.2 fun i => ?_
      by_cases hi : i < (ps k).n
      · have hm := t_mem (ps k) hi.le
        have hm' := t_mem (ps k) hi
        filter_upwards [hX.incr_decomp hB₁ hW₁ h.bm1 hs hm.1 (t_le_succ _ i) hm'.2,
          hY.incr_decomp hB₂ hW₂ h.bm2 hs hm.1 (t_le_succ _ i) hm'.2] with ω h1 h2 _
        simp only [hdY, hA, hBt, hR, hS, hβ, hHK, cvTerm]
        rw [h1, h2]
        ring
      · exact ae_of_all _ fun ω hh => absurd hh hi
    filter_upwards [hall] with ω hω
    simp only [sumCross, crossSum, wcvSum]
    have e : ∑ i ∈ Finset.range (ps k).n, (X ((ps k).t (i + 1)) ω - X ((ps k).t i) ω) *
        (Y ((ps k).t (i + 1)) ω - Y ((ps k).t i) ω)
        = ∑ i ∈ Finset.range (ps k).n, (HK ((ps k).t i) ω *
          cvTerm W₁ W₂ ((ps k).t i) ((ps k).t (i + 1)) ω
          + A k i ω * dY k i ω + (Bt k i ω + S k i ω) * β k i ω + R k i ω * dY k i ω) :=
      Finset.sum_congr rfl fun i hi => hω i (Finset.mem_range.1 hi)
    rw [e, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- the four limits
  have hHKm : ∀ u ∈ Set.Icc s t, Measurable (HK u) := fun u hu =>
    ((hHKa u hu).mono (𝓕.le u)).measurable
  have hw : Tendsto (fun k => ∫ ω, |wcvSum W₁ W₂ HK (ps k) ω| ∂P) atTop (𝓝 0) := by
    have hL := tendsto_integral_abs_of_L2Tendsto
      (L2Tendsto_wcvSum hB₁ hB₂ hW₁ hW₂ h hs hHKa hHKb ps hps)
    simpa using hL
  have hp1 := tendsto_integral_abs_sum_mul (P := P) (n := fun k => (ps k).n) mA mdY
    (tendsto_sum_integral_drift_sq hX.drift.bound ps hps)
    (fun k => sum_integral_incr_sq_le hB₂ hW₂ h.bm2 hs hY (ps k))
  have hBS0 : Tendsto (fun k => ∑ i ∈ Finset.range (ps k).n,
      ∫ ω, (Bt k i ω + S k i ω) ^ 2 ∂P) atTop (𝓝 0) := by
    have hl := ((tendsto_sum_integral_drift_sq (P := P) hY.drift.bound ps hps).const_mul 2).add
      ((tendsto_sum_integral_itoInt_sub_sq hB₂ hW₂ h.bm2 hs hY.diff ps hps).const_mul 2)
    rw [mul_zero, add_zero] at hl
    refine squeeze_zero (fun k => Finset.sum_nonneg fun i _ => integral_nonneg fun _ =>
      sq_nonneg _) (fun k => ?_) hl
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add
      ((mB k i hi').integrable_sq.const_mul _) ((mS k i hi').integrable_sq.const_mul _)]
    exact integral_mono ((mBS k i hi').integrable_sq) (((mB k i hi').integrable_sq.const_mul
      _).add ((mS k i hi').integrable_sq.const_mul _)) fun ω => add_sq_le_two _ _
  have hp2 := tendsto_integral_abs_sum_mul (P := P) (n := fun k => (ps k).n)
    (f := fun k i ω => Bt k i ω + S k i ω) mBS mβ hBS0
    (fun k => sum_integral_mul_incr_sq_le hB₁ hW₁ h.bm1 hs hX.diff (ps k))
  have hp3 := tendsto_integral_abs_sum_mul (P := P) (n := fun k => (ps k).n) mR mdY
    (tendsto_sum_integral_itoInt_sub_sq hB₁ hW₁ h.bm1 hs hX.diff ps hps)
    (fun k => sum_integral_incr_sq_le hB₂ hW₂ h.bm2 hs hY (ps k))
  -- integrability and the triangle inequality
  have iw : ∀ k, Integrable (fun ω => |wcvSum W₁ W₂ HK (ps k) ω|) P := fun k =>
    ((memLp_wcvSum hB₁ hB₂ hW₁ hW₂ h (ps k) hHKm hHKb).integrable one_le_two).abs
  have isum : ∀ (k : ℕ) (f g : ℕ → Ω → ℝ), (∀ i < (ps k).n, MemLp (f i) 2 P) →
      (∀ i < (ps k).n, MemLp (g i) 2 P) →
      Integrable (fun ω => |∑ i ∈ Finset.range (ps k).n, f i ω * g i ω|) P :=
    fun k f g hf hg => (integrable_finsetSum _ fun i hi =>
      (hf i (Finset.mem_range.1 hi)).integrable_mul (hg i (Finset.mem_range.1 hi))).abs
  have hbound : ∀ k, ∫ ω, |sumCross (ps k) X Y ω| ∂P
      ≤ ∫ ω, |wcvSum W₁ W₂ HK (ps k) ω| ∂P
        + ∫ ω, |∑ i ∈ Finset.range (ps k).n, A k i ω * dY k i ω| ∂P
        + ∫ ω, |∑ i ∈ Finset.range (ps k).n, (Bt k i ω + S k i ω) * β k i ω| ∂P
        + ∫ ω, |∑ i ∈ Finset.range (ps k).n, R k i ω * dY k i ω| ∂P := by
    intro k
    have i1 := isum k (A k) (dY k) (mA k) (mdY k)
    have i2 := isum k (fun i ω => Bt k i ω + S k i ω) (β k) (mBS k) (mβ k)
    have i3 := isum k (R k) (dY k) (mR k) (mdY k)
    have j2 : Integrable (fun ω => |wcvSum W₁ W₂ HK (ps k) ω|
        + |∑ i ∈ Finset.range (ps k).n, A k i ω * dY k i ω|) P := (iw k).add i1
    have j3 : Integrable (fun ω => |wcvSum W₁ W₂ HK (ps k) ω|
        + |∑ i ∈ Finset.range (ps k).n, A k i ω * dY k i ω|
        + |∑ i ∈ Finset.range (ps k).n, (Bt k i ω + S k i ω) * β k i ω|) P := j2.add i2
    have j4 : Integrable (fun ω => |wcvSum W₁ W₂ HK (ps k) ω|
        + |∑ i ∈ Finset.range (ps k).n, A k i ω * dY k i ω|
        + |∑ i ∈ Finset.range (ps k).n, (Bt k i ω + S k i ω) * β k i ω|
        + |∑ i ∈ Finset.range (ps k).n, R k i ω * dY k i ω|) P := j3.add i3
    rw [← integral_add (iw k) i1, ← integral_add j2 i2, ← integral_add j3 i3]
    rw [integral_congr_ae (g := fun ω => |wcvSum W₁ W₂ HK (ps k) ω
        + ∑ i ∈ Finset.range (ps k).n, A k i ω * dY k i ω
        + ∑ i ∈ Finset.range (ps k).n, (Bt k i ω + S k i ω) * β k i ω
        + ∑ i ∈ Finset.range (ps k).n, R k i ω * dY k i ω|)
      (by filter_upwards [hsplit k] with ω hω; rw [hω])]
    refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) j4
      (ae_of_all _ fun ω => ?_)
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
      (abs_add_le _ _) le_rfl)) le_rfl)
  have hlim := ((hw.add hp1).add hp2).add hp3
  simp only [add_zero] at hlim
  exact squeeze_zero (fun k => integral_nonneg fun _ => abs_nonneg _) hbound hlim

/-! ## The bracket and the product rule with two drivers -/

variable {Y b K₁ K₂ : ℝ → Ω → ℝ} {Cb D₁ D₂ : ℝ}

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the bracket of two-driver Itô processes,
`d[X, Y] = (H¹K¹ + H²K²) dt`.** For two-driver Itô processes `X` (diffusions `H¹`, `H²`) and
`Y` (diffusions `K¹`, `K²`) on `[s, t]`, `0 ≤ s < t`, along any partitions with mesh `→ 0`,
`Σ ΔX_iΔY_i → ∫_s^t H¹K¹ du + ∫_s^t H²K² du` in `L¹`: the same-driver brackets by I5d
(`TidyR7ItoCovariation.tendsto_integral_abs_sumCross`), the cross-driver ones vanish
(`tendsto_integral_abs_sumCross_indep`). -/
theorem tendsto_integral_abs_sumCross_two (hB₁ : IsPreBrownianReal W₁ P)
    (hB₂ : IsPreBrownianReal W₂ P) (hW₁ : ∀ t, Measurable (W₁ t))
    (hW₂ : ∀ t, Measurable (W₂ t)) (h : TwoBMFiltration P W₁ W₂ 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hX : ItoProcess2 P 𝓕 W₁ W₂ X a H₁ H₂ s t Ca C₁ C₂)
    (hY : ItoProcess2 P 𝓕 W₁ W₂ Y b K₁ K₂ s t Cb D₁ D₂) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, |sumCross (ps k) X Y ω
      - ((∫ u in s..t, H₁ u ω * K₁ u ω) + ∫ u in s..t, H₂ u ω * K₂ u ω)| ∂P) atTop (𝓝 0) := by
  have : IsProbabilityMeasure P := hB₁.isGaussianProcess.isProbabilityMeasure
  set X₁ := part₁ P 𝓕 W₂ X H₂ s with hX₁
  set Y₁ := part₁ P 𝓕 W₂ Y K₂ s with hY₁
  set X₂ : ℝ → Ω → ℝ := fun u ω => itoInt P 𝓕 W₂ H₂ s u ω with hX₂
  set Y₂ : ℝ → Ω → ℝ := fun u ω => itoInt P 𝓕 W₂ K₂ s u ω with hY₂
  have pX₁ := hX.part₁_ito
  have pY₁ := hY.part₁_ito
  have pX₂ := hX.part₂_ito
  have pY₂ := hY.part₂_ito
  set L₁ : Ω → ℝ := fun ω => ∫ u in s..t, H₁ u ω * K₁ u ω with hL₁
  set L₂ : Ω → ℝ := fun ω => ∫ u in s..t, H₂ u ω * K₂ u ω with hL₂
  have t11 := tendsto_integral_abs_sumCross hB₁ hW₁ h.bm1 hs hst pX₁ pY₁ ps hps
  have t22 := tendsto_integral_abs_sumCross hB₂ hW₂ h.bm2 hs hst pX₂ pY₂ ps hps
  have t12 := tendsto_integral_abs_sumCross_indep hB₁ hB₂ hW₁ hW₂ h hs pX₁ pY₂ ps hps
  have t21 := tendsto_integral_abs_sumCross_indep hB₁ hB₂ hW₁ hW₂ h hs pY₁ pX₂ ps hps
  have mX₁ := fun u (hu : u ∈ Set.Icc s t) => pX₁.memLp hB₁ hW₁ h.bm1 hs hu
  have mY₁ := fun u (hu : u ∈ Set.Icc s t) => pY₁.memLp hB₁ hW₁ h.bm1 hs hu
  have mX₂ := fun u (hu : u ∈ Set.Icc s t) => pX₂.memLp hB₂ hW₂ h.bm2 hs hu
  have mY₂ := fun u (hu : u ∈ Set.Icc s t) => pY₂.memLp hB₂ hW₂ h.bm2 hs hu
  have mL₁ : MemLp L₁ 2 P :=
    memLp_integral_drift (itoIntegrand_mul hX.diff1 hY.diff1) le_rfl hst.le le_rfl
  have mL₂ : MemLp L₂ 2 P :=
    memLp_integral_drift (itoIntegrand_mul hX.diff2 hY.diff2) le_rfl hst.le le_rfl
  have i11 : ∀ k, Integrable (fun ω => |sumCross (ps k) X₁ Y₁ ω - L₁ ω|) P := fun k =>
    ((integrable_sumCross_of_memLp mX₁ mY₁ (ps k)).sub (mL₁.integrable one_le_two)).abs
  have i22 : ∀ k, Integrable (fun ω => |sumCross (ps k) X₂ Y₂ ω - L₂ ω|) P := fun k =>
    ((integrable_sumCross_of_memLp mX₂ mY₂ (ps k)).sub (mL₂.integrable one_le_two)).abs
  have i12 : ∀ k, Integrable (fun ω => |sumCross (ps k) X₁ Y₂ ω|) P := fun k =>
    (integrable_sumCross_of_memLp mX₁ mY₂ (ps k)).abs
  have i21 : ∀ k, Integrable (fun ω => |sumCross (ps k) Y₁ X₂ ω|) P := fun k =>
    (integrable_sumCross_of_memLp mY₁ mX₂ (ps k)).abs
  have hbound : ∀ k, ∫ ω, |sumCross (ps k) X Y ω - (L₁ ω + L₂ ω)| ∂P
      ≤ ∫ ω, |sumCross (ps k) X₁ Y₁ ω - L₁ ω| ∂P + ∫ ω, |sumCross (ps k) X₁ Y₂ ω| ∂P
        + ∫ ω, |sumCross (ps k) Y₁ X₂ ω| ∂P + ∫ ω, |sumCross (ps k) X₂ Y₂ ω - L₂ ω| ∂P := by
    intro k
    have j2 : Integrable (fun ω => |sumCross (ps k) X₁ Y₁ ω - L₁ ω|
        + |sumCross (ps k) X₁ Y₂ ω|) P := (i11 k).add (i12 k)
    have j3 : Integrable (fun ω => |sumCross (ps k) X₁ Y₁ ω - L₁ ω|
        + |sumCross (ps k) X₁ Y₂ ω| + |sumCross (ps k) Y₁ X₂ ω|) P := j2.add (i21 k)
    have j4 : Integrable (fun ω => |sumCross (ps k) X₁ Y₁ ω - L₁ ω|
        + |sumCross (ps k) X₁ Y₂ ω| + |sumCross (ps k) Y₁ X₂ ω|
        + |sumCross (ps k) X₂ Y₂ ω - L₂ ω|) P := j3.add (i22 k)
    rw [← integral_add (i11 k) (i12 k), ← integral_add j2 (i21 k), ← integral_add j3 (i22 k)]
    refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) j4
      (ae_of_all _ fun ω => ?_)
    have hsp := sumCross_split (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂)
      (fun u ω => (part₁_add u ω).symm) (fun u ω => (part₁_add u ω).symm) (ps k) ω
    have hc : sumCross (ps k) X₂ Y₁ ω = sumCross (ps k) Y₁ X₂ ω :=
      Cochrane.Monetarism.TidyR7ItoBridge.crossSum_comm _ _ _
    have e : sumCross (ps k) X Y ω - (L₁ ω + L₂ ω) = (sumCross (ps k) X₁ Y₁ ω - L₁ ω)
        + sumCross (ps k) X₁ Y₂ ω + sumCross (ps k) Y₁ X₂ ω
        + (sumCross (ps k) X₂ Y₂ ω - L₂ ω) := by
      rw [hsp, hc]
      ring
    beta_reduce
    rw [e]
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
      (abs_add_le _ _) le_rfl)) le_rfl)
  have hlim := ((t11.add t12).add t21).add t22
  simp only [add_zero] at hlim
  exact squeeze_zero (fun k => integral_nonneg fun _ => abs_nonneg _) hbound hlim

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `Σ Z_iΔY_i → ∫_s^t Z dY` against a two-driver
process** in `L²`, where `∫ Z dY := ∫ Z b du + ∫ Z K¹ dW¹ + ∫ Z K² dW²`, for a mean-square
continuous `Z` (from `TidyR7ItoCovariation.L2Tendsto_sumRS` for each part of `Y`). -/
theorem L2Tendsto_sumRS_two (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration P W₁ W₂ 𝓕) (hs : 0 ≤ s) (hst : s < t) {Z : ℝ → Ω → ℝ}
    (hZ : MSIntegrand P 𝓕 Z s t) (hY : ItoProcess2 P 𝓕 W₁ W₂ Y b K₁ K₂ s t Cb D₁ D₂)
    (ps : ℕ → Partition s t) (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    L2Tendsto P (fun k => sumRS (ps k) Z Y) (fun ω =>
      dtInt P 𝓕 (fun u ω => Z u ω * b u ω) s t ω
        + itoInt P 𝓕 W₁ (fun u ω => Z u ω * K₁ u ω) s t ω
        + itoInt P 𝓕 W₂ (fun u ω => Z u ω * K₂ u ω) s t ω) := by
  have : IsProbabilityMeasure P := hB₁.isGaussianProcess.isProbabilityMeasure
  have h1 := L2Tendsto_sumRS hB₁ hW₁ h.bm1 hs hst hZ hY.part₁_ito ps hps
  have h2 := L2Tendsto_sumRS hB₂ hW₂ h.bm2 hs hst hZ hY.part₂_ito ps hps
  have h0 := dtInt_of_eq_zero (P := P) (𝓕 := 𝓕) (s := s) (t := t)
    (G := fun u ω => Z u ω * (fun _ _ => (0 : ℝ)) u ω) fun _ _ _ => mul_zero _
  refine ((h1.add h2).congr_seq fun k => ae_of_all _ fun ω => ?_).congr_ae ?_
  · simp only [Pi.add_apply]
    exact (sumRS_split (fun u ω => (part₁_add u ω).symm) (ps k) ω).symm
  · filter_upwards [h0] with ω hω
    simp only [Pi.add_apply] at hω ⊢
    rw [hω, Pi.zero_apply]
    ring

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: Itô's product rule with two independent drivers.**
For two-driver Itô processes `X` (drift `a`, diffusions `H¹`, `H²`) and `Y` (drift `b`,
diffusions `K¹`, `K²`) on `[s, t]`, `0 ≤ s < t`, almost surely
`X_tY_t − X_sY_s = (∫X b du + ∫X K¹ dW¹ + ∫X K² dW²) + (∫Y a du + ∫Y H¹ dW¹ + ∫Y H² dW²)
  + ∫_s^t H¹K¹ du + ∫_s^t H²K² du`:
`d(XY) = X dY + Y dX + (H¹K¹ + H²K²) dt`, the cross terms `H¹K²`, `H²K¹` vanishing. -/
theorem product_rule_two (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration P W₁ W₂ 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hX : ItoProcess2 P 𝓕 W₁ W₂ X a H₁ H₂ s t Ca C₁ C₂)
    (hY : ItoProcess2 P 𝓕 W₁ W₂ Y b K₁ K₂ s t Cb D₁ D₂) :
    (fun ω => X t ω * Y t ω - X s ω * Y s ω) =ᵐ[P] fun ω =>
      (dtInt P 𝓕 (fun u ω => X u ω * b u ω) s t ω
        + itoInt P 𝓕 W₁ (fun u ω => X u ω * K₁ u ω) s t ω
        + itoInt P 𝓕 W₂ (fun u ω => X u ω * K₂ u ω) s t ω)
      + (dtInt P 𝓕 (fun u ω => Y u ω * a u ω) s t ω
        + itoInt P 𝓕 W₁ (fun u ω => Y u ω * H₁ u ω) s t ω
        + itoInt P 𝓕 W₂ (fun u ω => Y u ω * H₂ u ω) s t ω)
      + ((∫ u in s..t, H₁ u ω * K₁ u ω) + ∫ u in s..t, H₂ u ω * K₂ u ω) := by
  have : IsProbabilityMeasure P := hB₁.isGaussianProcess.isProbabilityMeasure
  set ps : ℕ → Partition s t := fun k => dyadic hst k with hps_def
  have hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0) := tendsto_mesh_dyadic hst
  set L1 : Ω → ℝ := fun ω => dtInt P 𝓕 (fun u ω => X u ω * b u ω) s t ω
    + itoInt P 𝓕 W₁ (fun u ω => X u ω * K₁ u ω) s t ω
    + itoInt P 𝓕 W₂ (fun u ω => X u ω * K₂ u ω) s t ω with hL1
  set L2 : Ω → ℝ := fun ω => dtInt P 𝓕 (fun u ω => Y u ω * a u ω) s t ω
    + itoInt P 𝓕 W₁ (fun u ω => Y u ω * H₁ u ω) s t ω
    + itoInt P 𝓕 W₂ (fun u ω => Y u ω * H₂ u ω) s t ω with hL2
  set L3 : Ω → ℝ := fun ω => (∫ u in s..t, H₁ u ω * K₁ u ω) + ∫ u in s..t, H₂ u ω * K₂ u ω
    with hL3
  have h1 : L2Tendsto P (fun k => sumRS (ps k) X Y) L1 :=
    L2Tendsto_sumRS_two hB₁ hB₂ hW₁ hW₂ h hs hst (hX.toMS hB₁ hB₂ hW₁ hW₂ h hs) hY ps hps
  have h2 : L2Tendsto P (fun k => sumRS (ps k) Y X) L2 :=
    L2Tendsto_sumRS_two hB₁ hB₂ hW₁ hW₂ h hs hst (hY.toMS hB₁ hB₂ hW₁ hW₂ h hs) hX ps hps
  have h3 := tendsto_integral_abs_sumCross_two hB₁ hB₂ hW₁ hW₂ h hs hst hX hY ps hps
  have mX := fun u (hu : u ∈ Set.Icc s t) => hX.memLp hB₁ hB₂ hW₁ hW₂ h hs hu
  have mY := fun u (hu : u ∈ Set.Icc s t) => hY.memLp hB₁ hB₂ hW₁ hW₂ h hs hu
  have mL3 : MemLp L3 2 P :=
    (memLp_integral_drift (itoIntegrand_mul hX.diff1 hY.diff1) le_rfl hst.le le_rfl).add
      (memLp_integral_drift (itoIntegrand_mul hX.diff2 hY.diff2) le_rfl hst.le le_rfl)
  have t1 := tendsto_integral_abs_of_L2Tendsto h1
  have t2 := tendsto_integral_abs_of_L2Tendsto h2
  have i1 : ∀ k, Integrable (fun ω => |sumRS (ps k) X Y ω - L1 ω|) P := fun k =>
    (((h1.1 k).sub h1.2.1).integrable one_le_two).abs
  have i2 : ∀ k, Integrable (fun ω => |sumRS (ps k) Y X ω - L2 ω|) P := fun k =>
    (((h2.1 k).sub h2.2.1).integrable one_le_two).abs
  have i3 : ∀ k, Integrable (fun ω => |sumCross (ps k) X Y ω - L3 ω|) P := fun k =>
    ((integrable_sumCross_of_memLp mX mY (ps k)).sub (mL3.integrable one_le_two)).abs
  set D : Ω → ℝ := fun ω => X t ω * Y t ω - X s ω * Y s ω with hD
  have hbound : ∀ k, ∫ ω, |D ω - (L1 ω + L2 ω + L3 ω)| ∂P
      ≤ ∫ ω, |sumRS (ps k) X Y ω - L1 ω| ∂P + ∫ ω, |sumRS (ps k) Y X ω - L2 ω| ∂P
        + ∫ ω, |sumCross (ps k) X Y ω - L3 ω| ∂P := by
    intro k
    have j2 : Integrable (fun ω => |sumRS (ps k) X Y ω - L1 ω|
        + |sumRS (ps k) Y X ω - L2 ω|) P := (i1 k).add (i2 k)
    have j3 : Integrable (fun ω => |sumRS (ps k) X Y ω - L1 ω|
        + |sumRS (ps k) Y X ω - L2 ω| + |sumCross (ps k) X Y ω - L3 ω|) P := j2.add (i3 k)
    rw [← integral_add (i1 k) (i2 k), ← integral_add j2 (i3 k)]
    refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) j3
      (ae_of_all _ fun ω => ?_)
    have hid := prod_partition_identity (ps k) (fun u => X u ω) (fun u => Y u ω)
    have e : D ω - (L1 ω + L2 ω + L3 ω) = (sumRS (ps k) X Y ω - L1 ω)
        + (sumRS (ps k) Y X ω - L2 ω) + (sumCross (ps k) X Y ω - L3 ω) := by
      simp only [hD, sumRS, sumCross]
      rw [hid]
      ring
    change |D ω - (L1 ω + L2 ω + L3 ω)| ≤ _
    rw [e]
    exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  have hlim := (t1.add t2).add h3
  rw [add_zero, add_zero] at hlim
  have h0 : ∫ ω, |D ω - (L1 ω + L2 ω + L3 ω)| ∂P ≤ 0 := ge_of_tendsto' hlim hbound
  have mD : MemLp (fun ω => D ω - (L1 ω + L2 ω + L3 ω)) 1 P := by
    have hDi : Integrable D P :=
      ((mX t ⟨hst.le, le_rfl⟩).integrable_mul (mY t ⟨hst.le, le_rfl⟩)).sub
        ((mX s ⟨le_rfl, hst.le⟩).integrable_mul (mY s ⟨le_rfl, hst.le⟩))
    have hL1i : Integrable L1 P := (h1.2.1).integrable one_le_two
    have hL2i : Integrable L2 P := (h2.2.1).integrable one_le_two
    exact memLp_one_iff_integrable.2 (hDi.sub ((hL1i.add hL2i).add (mL3.integrable one_le_two)))
  have hz := (integral_eq_zero_iff_of_nonneg (fun ω => abs_nonneg _)
    (memLp_one_iff_integrable.1 mD).abs).1 (le_antisymm h0 (integral_nonneg fun _ => abs_nonneg _))
  filter_upwards [hz] with ω hω
  simp only [Pi.zero_apply, abs_eq_zero, sub_eq_zero] at hω
  exact hω

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the two brackets add up to one time integral,
`∫H¹K¹ du + ∫H²K² du = ∫(H¹K¹ + H²K²) du` a.s. (paths are a.s. continuous). -/
theorem bracket_two_ae_eq (hst : s ≤ t) (hX : ItoProcess2 P 𝓕 W₁ W₂ X a H₁ H₂ s t Ca C₁ C₂)
    (hY : ItoProcess2 P 𝓕 W₁ W₂ Y b K₁ K₂ s t Cb D₁ D₂) :
    (fun ω => (∫ u in s..t, H₁ u ω * K₁ u ω) + ∫ u in s..t, H₂ u ω * K₂ u ω) =ᵐ[P]
      fun ω => ∫ u in s..t, (H₁ u ω * K₁ u ω + H₂ u ω * K₂ u ω) := by
  filter_upwards [hX.diff1.cont, hX.diff2.cont, hY.diff1.cont, hY.diff2.cont]
    with ω c1 c2 c3 c4
  have hI : Set.uIcc s t = Set.Icc s t := Set.uIcc_of_le hst
  refine (intervalIntegral.integral_add ?_ ?_).symm
  · exact ((c1.mul c3).mono (by rw [hI])).intervalIntegrable
  · exact ((c2.mul c4).mono (by rw [hI])).intervalIntegrable

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (the form of (1.32) with two shocks):
`E_s[X_tY_t − X_sY_s] = E_s[∫_s^t X b du + ∫_s^t Y a du + ∫_s^t H¹K¹ du + ∫_s^t H²K² du]`**
a.s.: the four `dW`-integrals have conditional mean `0`
(`TidyR7ItoUnbounded.condExp_itoInt_ms` per driver). -/
theorem condExp_product_rule_two (hB₁ : IsPreBrownianReal W₁ P)
    (hB₂ : IsPreBrownianReal W₂ P) (hW₁ : ∀ t, Measurable (W₁ t))
    (hW₂ : ∀ t, Measurable (W₂ t)) (h : TwoBMFiltration P W₁ W₂ 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hX : ItoProcess2 P 𝓕 W₁ W₂ X a H₁ H₂ s t Ca C₁ C₂)
    (hY : ItoProcess2 P 𝓕 W₁ W₂ Y b K₁ K₂ s t Cb D₁ D₂) :
    P[fun ω => X t ω * Y t ω - X s ω * Y s ω | 𝓕 s] =ᵐ[P]
      P[fun ω => dtInt P 𝓕 (fun u ω => X u ω * b u ω) s t ω
        + dtInt P 𝓕 (fun u ω => Y u ω * a u ω) s t ω
        + ((∫ u in s..t, H₁ u ω * K₁ u ω) + ∫ u in s..t, H₂ u ω * K₂ u ω) | 𝓕 s] := by
  have : IsProbabilityMeasure P := hB₁.isGaussianProcess.isProbabilityMeasure
  have hXm := hX.toMS hB₁ hB₂ hW₁ hW₂ h hs
  have hYm := hY.toMS hB₁ hB₂ hW₁ hW₂ h hs
  set F : Ω → ℝ := fun ω => dtInt P 𝓕 (fun u ω => X u ω * b u ω) s t ω
    + dtInt P 𝓕 (fun u ω => Y u ω * a u ω) s t ω
    + ((∫ u in s..t, H₁ u ω * K₁ u ω) + ∫ u in s..t, H₂ u ω * K₂ u ω) with hF
  have g1 := MSIntegrand.mul_itoIntegrand hXm hY.diff1
  have g2 := MSIntegrand.mul_itoIntegrand hXm hY.diff2
  have g3 := MSIntegrand.mul_itoIntegrand hYm hX.diff1
  have g4 := MSIntegrand.mul_itoIntegrand hYm hX.diff2
  set I1 := itoInt P 𝓕 W₁ (fun u ω => X u ω * K₁ u ω) s t with hI1
  set I2 := itoInt P 𝓕 W₂ (fun u ω => X u ω * K₂ u ω) s t with hI2
  set I3 := itoInt P 𝓕 W₁ (fun u ω => Y u ω * H₁ u ω) s t with hI3
  set I4 := itoInt P 𝓕 W₂ (fun u ω => Y u ω * H₂ u ω) s t with hI4
  have iI1 : Integrable I1 P := (memLp_itoInt_ms hB₁ hW₁ h.bm1 hs g1).integrable one_le_two
  have iI2 : Integrable I2 P := (memLp_itoInt_ms hB₂ hW₂ h.bm2 hs g2).integrable one_le_two
  have iI3 : Integrable I3 P := (memLp_itoInt_ms hB₁ hW₁ h.bm1 hs g3).integrable one_le_two
  have iI4 : Integrable I4 P := (memLp_itoInt_ms hB₂ hW₂ h.bm2 hs g4).integrable one_le_two
  have iF : Integrable F P :=
    (((memLp_dtInt (MSIntegrand.mul_itoIntegrand hXm hY.drift)).integrable one_le_two).add
      ((memLp_dtInt (MSIntegrand.mul_itoIntegrand hYm hX.drift)).integrable one_le_two)).add
      (((memLp_integral_drift (itoIntegrand_mul hX.diff1 hY.diff1) le_rfl hst.le
        le_rfl).integrable one_le_two).add ((memLp_integral_drift
          (itoIntegrand_mul hX.diff2 hY.diff2) le_rfl hst.le le_rfl).integrable one_le_two))
  have e1 : (fun ω => X t ω * Y t ω - X s ω * Y s ω) =ᵐ[P] F + (I1 + I2 + I3 + I4) := by
    filter_upwards [product_rule_two hB₁ hB₂ hW₁ hW₂ h hs hst hX hY] with ω hω
    rw [hω]
    simp only [hF, hI1, hI2, hI3, hI4, Pi.add_apply]
    ring
  have hzero : P[I1 + I2 + I3 + I4 | 𝓕 s] =ᵐ[P] 0 := by
    filter_upwards [condExp_add ((iI1.add iI2).add iI3) iI4 (𝓕 s),
      condExp_add (iI1.add iI2) iI3 (𝓕 s), condExp_add iI1 iI2 (𝓕 s),
      condExp_itoInt_ms hB₁ hW₁ h.bm1 hs g1, condExp_itoInt_ms hB₂ hW₂ h.bm2 hs g2,
      condExp_itoInt_ms hB₁ hW₁ h.bm1 hs g3, condExp_itoInt_ms hB₂ hW₂ h.bm2 hs g4]
      with ω h1 h2 h3 h4 h5 h6 h7
    rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, Pi.add_apply]
    simp only [hI1, hI2, hI3, hI4] at h4 h5 h6 h7 ⊢
    rw [h4, h5, h6, h7]
    simp
  exact condExp_eq_of_ae_eq_add e1 iF (((iI1.add iI2).add iI3).add iI4) hzero

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (when the bracket-free form of (1.32) is right, two
shocks):** `E_s[X_tY_t − X_sY_s] = E_s[∫X b du + ∫Y a du]` a.s. **iff**
`E_s[∫_s^t H¹K¹ du + ∫_s^t H²K² du] = 0` a.s. -/
theorem condExp_product_rule_two_bookForm_iff (hB₁ : IsPreBrownianReal W₁ P)
    (hB₂ : IsPreBrownianReal W₂ P) (hW₁ : ∀ t, Measurable (W₁ t))
    (hW₂ : ∀ t, Measurable (W₂ t)) (h : TwoBMFiltration P W₁ W₂ 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hX : ItoProcess2 P 𝓕 W₁ W₂ X a H₁ H₂ s t Ca C₁ C₂)
    (hY : ItoProcess2 P 𝓕 W₁ W₂ Y b K₁ K₂ s t Cb D₁ D₂) :
    (P[fun ω => X t ω * Y t ω - X s ω * Y s ω | 𝓕 s] =ᵐ[P]
      P[fun ω => dtInt P 𝓕 (fun u ω => X u ω * b u ω) s t ω
        + dtInt P 𝓕 (fun u ω => Y u ω * a u ω) s t ω | 𝓕 s]) ↔
      P[fun ω => (∫ u in s..t, H₁ u ω * K₁ u ω) + ∫ u in s..t, H₂ u ω * K₂ u ω | 𝓕 s]
        =ᵐ[P] 0 := by
  have : IsProbabilityMeasure P := hB₁.isGaussianProcess.isProbabilityMeasure
  have hXm := hX.toMS hB₁ hB₂ hW₁ hW₂ h hs
  have hYm := hY.toMS hB₁ hB₂ hW₁ hW₂ h hs
  set F : Ω → ℝ := fun ω => dtInt P 𝓕 (fun u ω => X u ω * b u ω) s t ω
    + dtInt P 𝓕 (fun u ω => Y u ω * a u ω) s t ω with hF
  set Q : Ω → ℝ := fun ω => (∫ u in s..t, H₁ u ω * K₁ u ω) + ∫ u in s..t, H₂ u ω * K₂ u ω
    with hQ
  have iF : Integrable F P :=
    ((memLp_dtInt (MSIntegrand.mul_itoIntegrand hXm hY.drift)).integrable one_le_two).add
      ((memLp_dtInt (MSIntegrand.mul_itoIntegrand hYm hX.drift)).integrable one_le_two)
  have iQ : Integrable Q P :=
    ((memLp_integral_drift (itoIntegrand_mul hX.diff1 hY.diff1) le_rfl hst.le
      le_rfl).integrable one_le_two).add ((memLp_integral_drift
        (itoIntegrand_mul hX.diff2 hY.diff2) le_rfl hst.le le_rfl).integrable one_le_two)
  have hmain : P[fun ω => X t ω * Y t ω - X s ω * Y s ω | 𝓕 s] =ᵐ[P] P[F | 𝓕 s] + P[Q | 𝓕 s] :=
    (condExp_product_rule_two hB₁ hB₂ hW₁ hW₂ h hs hst hX hY).trans (condExp_add iF iQ (𝓕 s))
  constructor
  · intro hh
    filter_upwards [hmain, hh] with ω h1 h2
    rw [h1, Pi.add_apply] at h2
    simp only [Pi.zero_apply]
    linarith
  · intro hh
    filter_upwards [hmain, hh] with ω h1 h2
    rw [h1, Pi.add_apply, h2]
    simp

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: Itô integrals against independent drivers are
uncorrelated**, `E[(∫_s^t H dW¹)(∫_s^t K dW²)] = 0` for bounded admissible `H`, `K`,
`0 ≤ s < t`: `product_rule_two` for `X = ∫H dW¹`, `Y = ∫K dW²` has bracket
`∫H·0 + ∫0·K = 0`. -/
theorem integral_itoInt_mul_itoInt_indep (hB₁ : IsPreBrownianReal W₁ P)
    (hB₂ : IsPreBrownianReal W₂ P) (hW₁ : ∀ t, Measurable (W₁ t))
    (hW₂ : ∀ t, Measurable (W₂ t)) (h : TwoBMFiltration P W₁ W₂ 𝓕) (hs : 0 ≤ s) (hst : s < t)
    {H K : ℝ → Ω → ℝ} {CH CK : ℝ} (hH : ItoIntegrand P 𝓕 H s t CH)
    (hK : ItoIntegrand P 𝓕 K s t CK) :
    ∫ ω, itoInt P 𝓕 W₁ H s t ω * itoInt P 𝓕 W₂ K s t ω ∂P = 0 := by
  have : IsProbabilityMeasure P := hB₁.isGaussianProcess.isProbabilityMeasure
  have hX := itoProcess2_of_itoProcess₁ (itoProcess_itoInt (W := W₁) hH) hB₂ hW₂ h.bm2 hs
  have hY := itoProcess2_of_itoProcess₂ (itoProcess_itoInt (W := W₂) hK) hB₁ hW₁ h.bm1 hs
  have hc := condExp_product_rule_two hB₁ hB₂ hW₁ hW₂ h hs hst hX hY
  have h0 : ∀ G : ℝ → Ω → ℝ, dtInt P 𝓕 (fun u ω => G u ω * (fun _ _ => (0 : ℝ)) u ω) s t
      =ᵐ[P] 0 := fun G => dtInt_of_eq_zero fun _ _ _ => mul_zero _
  have hr : (fun ω => dtInt P 𝓕 (fun u ω => itoInt P 𝓕 W₁ H s u ω * (fun _ _ => (0 : ℝ)) u ω)
        s t ω + dtInt P 𝓕 (fun u ω => itoInt P 𝓕 W₂ K s u ω * (fun _ _ => (0 : ℝ)) u ω) s t ω
        + ((∫ u in s..t, H u ω * (fun _ _ => (0 : ℝ)) u ω)
          + ∫ u in s..t, (fun _ _ => (0 : ℝ)) u ω * K u ω)) =ᵐ[P] 0 := by
    filter_upwards [h0 (fun u ω => itoInt P 𝓕 W₁ H s u ω),
      h0 (fun u ω => itoInt P 𝓕 W₂ K s u ω)] with ω h1 h2
    rw [h1, h2]
    simp
  have hE := integral_condExp (μ := P) (f := fun ω => itoInt P 𝓕 W₁ H s t ω
    * itoInt P 𝓕 W₂ K s t ω - itoInt P 𝓕 W₁ H s s ω * itoInt P 𝓕 W₂ K s s ω) (𝓕.le s)
  rw [integral_congr_ae (hc.trans (condExp_congr_ae hr)), condExp_zero] at hE
  simp only [itoInt_of_le (le_refl s), Pi.zero_apply, mul_zero, sub_zero, integral_zero] at hE
  exact hE.symm

/-! ## Correlated Brownian motion -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the correlated motion**
`W³ = ρW¹ + √(1 − ρ²)W²`. -/
noncomputable def corrBM (ρ : ℝ) (W₁ W₂ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ρ * W₁ t ω + Real.sqrt (1 - ρ ^ 2) * W₂ t ω

/-- Cochrane (2023), A1 §1.6, pp. 567–568: increments of `W³` are
`ρΔW¹ + √(1 − ρ²)ΔW²`. -/
theorem incr_corrBM (ρ : ℝ) (u v : ℝ) (ω : Ω) :
    incr (corrBM ρ W₁ W₂) u v ω = ρ * incr W₁ u v ω + Real.sqrt (1 - ρ ^ 2) * incr W₂ u v ω := by
  simp only [incr, bmReal, corrBM]
  ring

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `W³` is a two-driver Itô process** on the common
filtration, with drift `0` and loadings `ρ` on `W¹` and `√(1 − ρ²)` on `W²`, for `|ρ| ≤ 1`. -/
theorem itoProcess2_corrBM (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration P W₁ W₂ 𝓕) (hs : 0 ≤ s) (ρ : ℝ) :
    ItoProcess2 P 𝓕 W₁ W₂ (bmReal (corrBM ρ W₁ W₂)) (fun _ _ => 0) (fun _ _ => ρ)
      (fun _ _ => Real.sqrt (1 - ρ ^ 2)) s t 0 |ρ| |Real.sqrt (1 - ρ ^ 2)| where
  adapted u _ := ((h.bm1.adapted u).const_mul ρ).add
    ((h.bm2.adapted u).const_mul (Real.sqrt (1 - ρ ^ 2)))
  init := ((hB₁.isGaussianProcess.hasGaussianLaw_eval _).memLp_two.const_mul ρ).add
    ((hB₂.isGaussianProcess.hasGaussianLaw_eval _).memLp_two.const_mul _)
  drift := itoIntegrand_const stronglyMeasurable_const (fun _ => by simp)
  diff1 := itoIntegrand_const stronglyMeasurable_const (fun _ => le_rfl)
  diff2 := itoIntegrand_const stronglyMeasurable_const (fun _ => le_rfl)
  eq u hu := by
    filter_upwards [itoInt_const hB₁ hW₁ h.bm1 hs hu.1 (c := fun _ => ρ)
      stronglyMeasurable_const (C := |ρ|) (fun _ => le_rfl),
      itoInt_const hB₂ hW₂ h.bm2 hs hu.1 (c := fun _ => Real.sqrt (1 - ρ ^ 2))
      stronglyMeasurable_const (C := |Real.sqrt (1 - ρ ^ 2)|) (fun _ => le_rfl)] with ω h1 h2
    rw [itoRHS2, h1, h2]
    have e := incr_corrBM (W₁ := W₁) (W₂ := W₂) ρ s u ω
    simp only [incr] at e
    simp only [intervalIntegral.integral_zero, add_zero, incr]
    linarith

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `d[W¹, W³] = ρ dt` in `L¹`.** For a common
admissible filtration and `0 ≤ s < t`, along any partitions with mesh `→ 0`,
`Σ ΔW¹_iΔW³_i → ρ(t − s)` in `L¹`: `tendsto_integral_abs_sumCross_two` with `W¹` (loadings
`1`, `0`) and `W³` (loadings `ρ`, `√(1 − ρ²)`). -/
theorem tendsto_integral_abs_sumCross_corrBM (hB₁ : IsPreBrownianReal W₁ P)
    (hB₂ : IsPreBrownianReal W₂ P) (hW₁ : ∀ t, Measurable (W₁ t))
    (hW₂ : ∀ t, Measurable (W₂ t)) (h : TwoBMFiltration P W₁ W₂ 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (ρ : ℝ) (ps : ℕ → Partition s t) (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, |sumCross (ps k) (bmReal W₁) (bmReal (corrBM ρ W₁ W₂)) ω
      - ρ * (t - s)| ∂P) atTop (𝓝 0) := by
  have hX := itoProcess2_of_itoProcess₁ (itoProcess_bm (t := t) hB₁ hW₁ h.bm1 hs) hB₂ hW₂
    h.bm2 hs
  have hY := itoProcess2_corrBM (t := t) hB₁ hB₂ hW₁ hW₂ h hs ρ
  have hh := tendsto_integral_abs_sumCross_two hB₁ hB₂ hW₁ hW₂ h hs hst hX hY ps hps
  simp only [one_mul, zero_mul, intervalIntegral.integral_const, smul_eq_mul,
    intervalIntegral.integral_zero, add_zero] at hh
  simpa only [mul_comm] using hh

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `d[W¹, W³] = ρ dt` in `L²`**, with the exact
decomposition `Σ ΔW¹_iΔW³_i − ρ(t − s) = ρ(Σ(ΔW¹_i)² − (t − s)) + √(1 − ρ²)Σ ΔW¹_iΔW²_i`
(`(dW¹)² = dt` from TidyR7BrownianQV and `dW¹dW² = 0` from TidyR10TwoBMCross). -/
theorem L2Tendsto_crossSum_corrBM (hB₁ : IsPreBrownianReal W₁ P)
    (hB₂ : IsPreBrownianReal W₂ P) (hW₁ : ∀ t, Measurable (W₁ t))
    (hW₂ : ∀ t, Measurable (W₂ t)) (h : TwoBMFiltration P W₁ W₂ 𝓕) (hs : 0 ≤ s) (ρ : ℝ)
    (ps : ℕ → Partition s t) (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    L2Tendsto P (fun k => sumCross (ps k) (bmReal W₁) (bmReal (corrBM ρ W₁ W₂)))
      (fun _ => ρ * (t - s)) := by
  have : IsProbabilityMeasure P := hB₁.isGaussianProcess.isProbabilityMeasure
  have hq : L2Tendsto P (fun k => qvSum W₁ (ps k)) (fun _ => t - s) := by
    refine ⟨fun k => (memLp_qvSum_sub hB₁ hW₁ (ps k)).add (memLp_const (t - s)) |>.ae_eq
      (ae_of_all _ fun ω => by simp), memLp_const _, ?_⟩
    exact tendsto_integral_qvSum_sub_sq hB₁ hW₁ hs ps hps
  have hc := L2Tendsto_cvSum hB₁ hB₂ hW₁ hW₂ h hs ps hps
  have hsum := (hq.const_mul ρ).add (hc.const_mul (Real.sqrt (1 - ρ ^ 2)))
  refine (hsum.congr_seq fun k => ae_of_all _ fun ω => ?_).congr_ae (ae_of_all _ fun ω => ?_)
  · simp only [Pi.add_apply, sumCross, crossSum, qvSum, cvSum, cvTerm, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e := incr_corrBM (W₁ := W₁) (W₂ := W₂) ρ ((ps k).t i) ((ps k).t (i + 1)) ω
    simp only [incr] at e ⊢
    rw [e]
    ring
  · simp

/-! ## Non-vacuity on the constructed pair -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (non-vacuity): the product of the two constructed
independent motions has no bracket**: on `twoGauss`, for `0 ≤ s < t`, a.s.
`W¹_tW²_t − W¹_sW²_s = ∫_s^t W¹ dW² + ∫_s^t W² dW¹` (`product_rule_two`, all drift and
cross-driver terms vanishing). -/
theorem product_rule_two_bmPath (hs : 0 ≤ s) (hst : s < t) :
    (fun ω => bmReal bmPath₁ t ω * bmReal bmPath₂ t ω - bmReal bmPath₁ s ω * bmReal bmPath₂ s ω)
      =ᵐ[twoGauss] fun ω =>
        itoInt twoGauss twoBMF bmPath₂ (fun u ω => bmReal bmPath₁ u ω * 1) s t ω
          + itoInt twoGauss twoBMF bmPath₁ (fun u ω => bmReal bmPath₂ u ω * 1) s t ω := by
  have := isProbabilityMeasure_twoGauss
  have hB₁ := isBrownianReal_bmPath₁.toIsPreBrownianReal
  have hB₂ := isBrownianReal_bmPath₂.toIsPreBrownianReal
  have h := twoBMFiltration_bmPath_isTwoBM
  have hX := itoProcess2_of_itoProcess₁ (itoProcess_bm (t := t) hB₁ measurable_bmPath₁ h.bm1 hs)
    hB₂ measurable_bmPath₂ h.bm2 hs
  have hY := itoProcess2_of_itoProcess₂ (itoProcess_bm (t := t) hB₂ measurable_bmPath₂ h.bm2 hs)
    hB₁ measurable_bmPath₁ h.bm1 hs
  have hpr := product_rule_two hB₁ hB₂ measurable_bmPath₁ measurable_bmPath₂ h hs hst hX hY
  have h0 : ∀ G : ℝ → (ℕ → ℝ) × (ℕ → ℝ) → ℝ,
      dtInt twoGauss twoBMF (fun u ω => G u ω * (fun _ _ => (0 : ℝ)) u ω) s t =ᵐ[twoGauss] 0 :=
    fun G => dtInt_of_eq_zero fun _ _ _ => mul_zero _
  have hz : ∀ G : ℝ → (ℕ → ℝ) × (ℕ → ℝ) → ℝ, ∀ W : ℝ≥0 → (ℕ → ℝ) × (ℕ → ℝ) → ℝ,
      (∀ t, Measurable (W t)) → IsPreBrownianReal W twoGauss → BMFiltration twoGauss W twoBMF →
      MSIntegrand twoGauss twoBMF G s t →
      itoInt twoGauss twoBMF W (fun u ω => G u ω * (fun _ _ => (0 : ℝ)) u ω) s t
        =ᵐ[twoGauss] 0 := by
    intro G W hW hB hF _
    have e : (fun u ω => G u ω * (fun _ _ => (0 : ℝ)) u ω) = fun _ _ => (0 : ℝ) := by
      funext u ω
      simp
    rw [e]
    filter_upwards [itoInt_const hB hW hF hs hst.le (c := fun _ => (0 : ℝ))
      stronglyMeasurable_const (C := 0) (fun _ => by simp)] with ω hω
    rw [hω, Pi.zero_apply, zero_mul]
  have mX := hX.toMS hB₁ hB₂ measurable_bmPath₁ measurable_bmPath₂ h hs
  have mY := hY.toMS hB₁ hB₂ measurable_bmPath₁ measurable_bmPath₂ h hs
  filter_upwards [hpr, h0 (bmReal bmPath₁), h0 (bmReal bmPath₂),
    hz _ _ measurable_bmPath₁ hB₁ h.bm1 mX, hz _ _ measurable_bmPath₂ hB₂ h.bm2 mY]
    with ω h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4, h5]
  simp only [Pi.zero_apply, mul_zero, zero_mul, intervalIntegral.integral_zero]
  ring

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (non-vacuity): on the constructed pair, for every
`ρ`, `Σ ΔW¹_iΔW³_i → ρ(t − s)` in `L²` along any partitions of `[s, t]`, `0 ≤ s`, with mesh
`→ 0`, `W³ = ρW¹ + √(1 − ρ²)W²`. -/
theorem tendsto_crossSum_corrBM_bmPath (hs : 0 ≤ s) (ρ : ℝ) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    L2Tendsto twoGauss (fun k => sumCross (ps k) (bmReal bmPath₁)
      (bmReal (corrBM ρ bmPath₁ bmPath₂))) (fun _ => ρ * (t - s)) :=
  L2Tendsto_crossSum_corrBM isBrownianReal_bmPath₁.toIsPreBrownianReal
    isBrownianReal_bmPath₂.toIsPreBrownianReal measurable_bmPath₁ measurable_bmPath₂
    twoBMFiltration_bmPath_isTwoBM hs ρ ps hps

end Cochrane.Monetarism.TidyR10TwoBMIto
