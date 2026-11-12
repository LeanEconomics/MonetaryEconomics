/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR12SDEProductRule
import Monetarism.TidyR7MonetarismIto

/-!
# The money–bond model of §1.6 with an unbounded diffusive `Λ/P`: the corrected (1.32)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.32) (Track 3, chunk B4). The model of
`TidyR7MonetarismIto.ItoMonetaryModel` asks `n = Λ/P` to be an Itô process with BOUNDED
coefficients, which excludes the lognormal `Λ/P` (B1's positive `2 + sin W` came with a random
rate forced by that choice of `n`). Here `n` is an Itô process with mean-square continuous
coefficients (`TidyR12SDEProcess.ItoProcessMS`), so `dn = −i n dt + σ n dW` with a KNOWN
constant rate `i` is admitted (`TidyR12SDEMonetaryGBM`).

## The model (`ItoMonetaryModelMS`)

As `TidyR7MonetarismIto.ItoMonetaryModel`, except: `n = Λ/P` is an `ItoProcessMS` with drift
`−i n` and diffusion `σ_X`; bonds `B` (drift `β`, diffusion `σ_B`, bounded coefficients) have
bounded values with a.s. continuous paths (`ItoMonetaryModelMS.bonds_bdd`, the hypothesis of
`TidyR12SDEProductRule.condExp_product_rule_ms`); money `M` (drift `m`, diffusion `σ_M`) as
before; (1.31) on the coefficients, `β + m = iB + i^mM − Ps`, `σ_B + σ_M = 0`.

## Main results

* `ItoMonetaryModelMS.incr_1_32_ms_general` (**corrected (1.32)**): a.s.
  `E_s[n_tB_t − n_sB_s] = E_s[−(∫_s^t (Λs − i^m nM) du + ∫_s^t n dM) + ∫_s^t σ_Xσ_B du]`.
* `ItoMonetaryModelMS.incr_1_32_ms_book_iff`: the last line of (1.32) as printed holds iff
  `E_s[∫_s^t σ_Xσ_B du] = 0`; `ItoMonetaryModelMS.incr_1_32_ms_uncorrelated`: it holds when
  `σ_Xσ_B = 0` on `[s, t]` (in particular for bonds of bounded variation);
  `ItoMonetaryModelMS.incr_1_32_ms_book_fails`: it fails whenever `E[∫_s^t σ_Xσ_B du] ≠ 0`.
-/

namespace Cochrane.Monetarism.TidyR12SDEMonetary

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoSums Cochrane.Monetarism.TidyR7ItoIntegral
  Cochrane.Monetarism.TidyR7ItoUnbounded Cochrane.Monetarism.TidyR7ItoProducts
  Cochrane.Monetarism.TidyR7ItoProcess Cochrane.Monetarism.TidyR7ItoBondStep
  Cochrane.Monetarism.TidyR7MonetarismModel Cochrane.Monetarism.TidyR7MonetarismIto
  Cochrane.Monetarism.TidyR12SDETools Cochrane.Monetarism.TidyR12SDEProcess
  Cochrane.Monetarism.TidyR12SDEProductRule
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

variable (μ : Measure Ω) (𝓕 : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ℝ)
  (Λ P B M i im sp β σB m σM σX : ℝ → Ω → ℝ) (s t CBv Cβ CB Cm CM : ℝ)

/-- **Cochrane (2023), A1 §1.6, (1.31)–(1.32), pp. 567–568: the money–bond model with an
unbounded diffusive `Λ/P` on `[s, t]`.** `P > 0`; `n = Λ/P` an Itô process with mean-square
continuous coefficients, drift `−i n` (bond pricing) and diffusion `σ_X`; bonds `B` (drift `β`,
diffusion `σ_B`) an Itô process with bounded coefficients and bounded, a.s. continuous values;
money `M` (drift `m`, diffusion `σ_M`) an Itô process; (1.31) on the coefficients,
`β + m = iB + i^mM − Ps` and `σ_B + σ_M = 0`. -/
structure ItoMonetaryModelMS where
  P_pos : ∀ u ω, 0 < P u ω
  disc_ito : ItoProcessMS μ 𝓕 W (disc Λ P) (fun u ω => -(i u ω * disc Λ P u ω)) σX s t
  bonds_ito : ItoProcess μ 𝓕 W B β σB s t Cβ CB
  bonds_bdd : ItoIntegrand μ 𝓕 B s t CBv
  money_ito : ItoProcess μ 𝓕 W M m σM s t Cm CM
  flow_drift : ∀ u ω, β u ω + m u ω = flowRate B M P i im sp u ω
  flow_diff : ∀ u ω, σB u ω + σM u ω = 0

variable {μ 𝓕 W Λ P B M i im sp β σB m σM σX s t CBv Cβ CB Cm CM}

namespace ItoMonetaryModelMS

variable (hm : ItoMonetaryModelMS μ 𝓕 W Λ P B M i im sp β σB m σM σX s t CBv Cβ CB Cm CM)
include hm

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: **the rate identity behind (1.32)**,
`Λs − i^m nM = −(B·(−in) + nβ + nm)` (the analogue of
`TidyR7MonetarismIto.ItoMonetaryModel.rate_1_32`). -/
theorem rate_1_32_ms (u : ℝ) (ω : Ω) :
    Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω =
      -1 * (B u ω * -(i u ω * disc Λ P u ω) + disc Λ P u ω * β u ω
        + disc Λ P u ω * m u ω) := by
  have hn : disc Λ P u ω * P u ω = Λ u ω := div_mul_cancel₀ (Λ u ω) (hm.P_pos u ω).ne'
  have h1 := hm.flow_drift u ω
  simp only [flowRate] at h1
  linear_combination (disc Λ P u ω) * h1 - sp u ω * hn

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the corrected (1.32) with an unbounded
diffusive `Λ/P`.** For `0 ≤ s < t`, almost surely
`E_s[n_tB_t − n_sB_s] = E_s[−(∫_s^t (Λs − i^m nM) du + ∫_s^t n dM) + ∫_s^t σ_Xσ_B du]`,
`n = Λ/P` (the bracket is the mean-square time integral).
The analogue of `TidyR7MonetarismIto.ItoMonetaryModel.incr_1_32_ito_general`. -/
theorem incr_1_32_ms_general (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t) :
    μ[fun ω => disc Λ P t ω * B t ω - disc Λ P s ω * B s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => -(dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω) s t ω
        + moneyInt μ 𝓕 W Λ P m σM s t ω)
        + dtInt μ 𝓕 (fun u ω => σX u ω * σB u ω) s t ω | 𝓕 s] := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have hn := hm.disc_ito
  have hb := hm.bonds_ito
  have hM := hm.money_ito
  have nMS := hn.toMS hBM hWm h𝓕 hs
  have G1 := MSIntegrand.mul_itoIntegrand nMS hb.drift
  have G2 := msIntegrand_itoIntegrand_mul hm.bonds_bdd hn.drift
  have G3 := MSIntegrand.mul_itoIntegrand nMS hM.drift
  have G4 := MSIntegrand.mul_itoIntegrand nMS hM.diff
  have G5 := MSIntegrand.mul_itoIntegrand hn.diff hb.diff
  have hprod := condExp_product_rule_ms hBM hWm h𝓕 hs hst hn hb hm.bonds_bdd
  set d1 := dtInt μ 𝓕 (fun u ω => disc Λ P u ω * β u ω) s t with hd1
  set d2 := dtInt μ 𝓕 (fun u ω => B u ω * -(i u ω * disc Λ P u ω)) s t with hd2
  set d3 := dtInt μ 𝓕 (fun u ω => disc Λ P u ω * m u ω) s t with hd3
  set I := itoInt μ 𝓕 W (fun u ω => disc Λ P u ω * σM u ω) s t with hI
  set Q := dtInt μ 𝓕 (fun u ω => σX u ω * σB u ω) s t with hQ
  have eD : dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω) s t =ᵐ[μ]
      fun ω => -(d2 ω + d1 ω + d3 ω) := by
    have e : (fun u ω => Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω) =
        fun u ω => -1 * (B u ω * -(i u ω * disc Λ P u ω) + disc Λ P u ω * β u ω
          + disc Λ P u ω * m u ω) := funext fun u => funext fun ω => hm.rate_1_32_ms u ω
    rw [e]
    filter_upwards [dtInt_const_mul (MSIntegrand.add (MSIntegrand.add G2 G1) G3) (-1),
      dtInt_add (MSIntegrand.add G2 G1) G3, dtInt_add G2 G1] with ω h1 h2 h3
    rw [h1, h2, Pi.add_apply, h3, Pi.add_apply]
    ring
  have iR0 : Integrable (fun ω => d1 ω + d2 ω + Q ω) μ :=
    (((memLp_dtInt G1).integrable one_le_two).add ((memLp_dtInt G2).integrable one_le_two)).add
      ((memLp_dtInt G5).integrable one_le_two)
  have iI : Integrable I μ := (memLp_itoInt_ms hBM hWm h𝓕 hs G4).integrable one_le_two
  have hR : μ[fun ω => -(dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω)
        s t ω + moneyInt μ 𝓕 W Λ P m σM s t ω) + Q ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => d1 ω + d2 ω + Q ω | 𝓕 s] := by
    refine condExp_eq_of_ae_eq_add (h := fun ω => -I ω) ?_ iR0 iI.neg ?_
    · filter_upwards [eD] with ω h
      simp only [moneyInt, intIto, Pi.add_apply]
      rw [h]
      simp only [hd3, hI]
      ring
    · filter_upwards [condExp_neg (μ := μ) I (𝓕 s), condExp_itoInt_ms hBM hWm h𝓕 hs G4] with
        ω h1 h2
      change μ[-I | 𝓕 s] ω = 0
      rw [h1, Pi.neg_apply, h2]
      simp
  refine hprod.trans ?_
  exact hR.symm

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the book's right-hand side
`−(∫_s^t (Λs − i^m nM) du + ∫_s^t n dM)` is integrable, `0 ≤ s`.
The analogue of `TidyR7MonetarismIto.ItoMonetaryModel.integrable_rhs_1_32`. -/
theorem integrable_rhs_1_32_ms (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) :
    Integrable (fun ω => -(dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω
      - im u ω * disc Λ P u ω * M u ω) s t ω + moneyInt μ 𝓕 W Λ P m σM s t ω)) μ := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have hn := hm.disc_ito
  have hb := hm.bonds_ito
  have hM := hm.money_ito
  have nMS := hn.toMS hBM hWm h𝓕 hs
  have G := MSIntegrand.add (MSIntegrand.add (msIntegrand_itoIntegrand_mul hm.bonds_bdd hn.drift)
    (MSIntegrand.mul_itoIntegrand nMS hb.drift)) (MSIntegrand.mul_itoIntegrand nMS hM.drift)
  have e : (fun u ω => Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω) =
      fun u ω => -1 * (B u ω * -(i u ω * disc Λ P u ω) + disc Λ P u ω * β u ω
        + disc Λ P u ω * m u ω) := funext fun u => funext fun ω => hm.rate_1_32_ms u ω
  rw [e]
  exact (((memLp_dtInt (MSIntegrand.const_mul G (-1))).integrable one_le_two).add
    (integrable_intIto hBM hWm h𝓕 hs nMS hM.drift hM.diff)).neg

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: when the last line of (1.32) as printed is
right, with an unbounded diffusive `Λ/P`.** For `0 ≤ s < t`, the book's
`E_s[n_tB_t − n_sB_s] = −E_s[∫_s^t (Λs − i^m nM) du + ∫_s^t n dM]` holds a.s. **iff**
`E_s[∫_s^t σ_Xσ_B du] = 0` a.s.
Generalises `TidyR7MonetarismIto.ItoMonetaryModel.incr_1_32_ito_book_iff` (bounded `Λ/P`). -/
theorem incr_1_32_ms_book_iff (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t) :
    (μ[fun ω => disc Λ P t ω * B t ω - disc Λ P s ω * B s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => -(dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω) s t ω
        + moneyInt μ 𝓕 W Λ P m σM s t ω) | 𝓕 s]) ↔
      μ[dtInt μ 𝓕 (fun u ω => σX u ω * σB u ω) s t | 𝓕 s] =ᵐ[μ] 0 := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have iF := hm.integrable_rhs_1_32_ms hBM hWm h𝓕 hs
  have iQ : Integrable (dtInt μ 𝓕 (fun u ω => σX u ω * σB u ω) s t) μ :=
    (memLp_dtInt (MSIntegrand.mul_itoIntegrand hm.disc_ito.diff hm.bonds_ito.diff)).integrable
      one_le_two
  have hmain := (hm.incr_1_32_ms_general hBM hWm h𝓕 hs hst).trans (condExp_add iF iQ (𝓕 s))
  constructor
  · intro h
    filter_upwards [hmain, h] with ω h1 h2
    rw [h1, Pi.add_apply] at h2
    simp only [Pi.zero_apply]
    linarith
  · intro h
    filter_upwards [hmain, h] with ω h1 h2
    rw [h1, Pi.add_apply, h2]
    simp

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the last line as printed holds when bonds'
diffusion is uncorrelated with `Λ/P`**, `σ_Xσ_B = 0` on `[s, t]` (e.g. bonds of bounded
variation, `σ_B = 0`), with `Λ/P` diffusive and unbounded.
Generalises `TidyR7MonetarismIto.ItoMonetaryModel.incr_1_32_ito_uncorrelated` (bounded `Λ/P`). -/
theorem incr_1_32_ms_uncorrelated (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hσ : ∀ u ∈ Set.Icc s t, ∀ ω, σX u ω * σB u ω = 0) :
    μ[fun ω => disc Λ P t ω * B t ω - disc Λ P s ω * B s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => -(dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω) s t ω
        + moneyInt μ 𝓕 W Λ P m σM s t ω) | 𝓕 s] := by
  refine (hm.incr_1_32_ms_book_iff hBM hWm h𝓕 hs hst).2 ?_
  filter_upwards [condExp_congr_ae (m := 𝓕 s) (dtInt_of_eq_zero (P := μ) (𝓕 := 𝓕) hσ)] with
    ω h
  rw [h, condExp_zero]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the last line as printed FAILS whenever the
expected bracket is nonzero**: if `E[∫_s^t σ_Xσ_B du] ≠ 0` (`0 ≤ s < t`), the book's
`E_s[n_tB_t − n_sB_s] = −E_s[∫_s^t (Λs − i^m nM) du + ∫_s^t n dM]` is false (taking `E` of
`E_s[∫σ_Xσ_B] = 0` would give `E[∫σ_Xσ_B] = 0`). -/
theorem incr_1_32_ms_book_fails (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hQ : ∫ ω, dtInt μ 𝓕 (fun u ω => σX u ω * σB u ω) s t ω ∂μ ≠ 0) :
    ¬ (μ[fun ω => disc Λ P t ω * B t ω - disc Λ P s ω * B s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => -(dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω) s t ω
        + moneyInt μ 𝓕 W Λ P m σM s t ω) | 𝓕 s]) := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  intro h
  have h0 := (hm.incr_1_32_ms_book_iff hBM hWm h𝓕 hs hst).1 h
  apply hQ
  rw [← integral_condExp (𝓕.le s), integral_congr_ae h0]
  simp

end ItoMonetaryModelMS

end Cochrane.Monetarism.TidyR12SDEMonetary
