/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR7ItoBondStep
import Monetarism.TidyR7MonetarismModel

/-!
# The money–bond model of §1.6 with diffusive bonds: the corrected (1.32) and (1.34)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). The Itô analogue of
`TidyR7MonetarismModel.MonetaryModel` on an interval `[s, t]`, `0 ≤ s < t`.

## The model (`ItoMonetaryModel`)

A Brownian motion `W` with an admissible filtration `𝓕`; the price level `P > 0`; the nominal
discount factor `n = Λ/P` (`TidyR7MonetarismModel.disc`) is an Itô process with drift `−i n`
(the bond-pricing condition `E_t d(Λ/P) = −i(Λ/P) dt`) and diffusion `σ_X`; bonds `B` (drift
`β`, diffusion `σ_B`) and money `M` (drift `m`, diffusion `σ_M`) are Itô processes; the flow
(1.31) `dM = iB dt + i^mM dt − Ps dt − dB` is imposed on the coefficients:
`β + m = iB + i^mM − Ps` (`TidyR7MonetarismModel.flowRate`) and `σ_B + σ_M = 0`. It gives back
I3's path condition `(B + M)_u − (B + M)_s = ∫_s^u (iB + i^mM − Ps) dr` a.s.
(`ItoMonetaryModel.flow_1_31`). **Under (1.31) diffusive bonds force diffusive money**,
`σ_M = −σ_B`, because `B + M` is locally riskless; so `−E_t d[n, M] = E_t d[n, B]`.

`∫ X dY := ∫ X b du + ∫ X K dW` for `Y` with drift `b` and diffusion `K` (`intIto`; the `du`
integral is the mean-square one, `TidyR7ItoProducts.dtInt`, equal to the pathwise one for a.s.
continuous paths, `TidyR7ItoProducts.dtInt_ae_eq_integral`). The money term of (1.32) is
`∫ n dM` (`moneyInt`).

## Main results

* `ItoMonetaryModel.incr_1_32_ito_general` (**corrected (1.32)**): a.s.
  `E_s[n_tB_t − n_sB_s] = E_s[−(∫_s^t (Λs − i^m nM) du + ∫_s^t n dM) + ∫_s^t σ_Xσ_B du]`;
  `ItoMonetaryModel.incr_1_32_ito` (`i^m = 0`, the book's case):
  `E_t d(ΛB/P) = −Λ(s dt + dM/P) + E_t[σ_Bσ_X] dt`.
* `ItoMonetaryModel.incr_1_32_ito_book_iff`: the last line of (1.32) as printed holds iff
  `E_s[∫_s^t σ_Xσ_B du] = 0`; `ItoMonetaryModel.incr_1_32_ito_uncorrelated`: it holds when
  `σ_Bσ_X = 0` on `[s, t]` a.s., in particular for bonds of bounded variation.
* `ItoMonetaryModel.middle_1_32_ito`, `ItoMonetaryModel.middle_1_32_ito_expIncr`: **the middle
  line of (1.32) holds verbatim**, `E_s[∫ n dB] + B·E_s d(Λ/P) = −E_s[∫(Λs − i^m nM) + ∫ n dM]`,
  with `B·E_s d(Λ/P) = lim E_s[Σ B_iΔn_i] = E_s∫B(−in) du`; `ItoMonetaryModel.line1_1_32_rate`:
  the first line is (1.31) divided by `P` (drift and diffusion parts).
* `ItoMonetaryModel.incr_1_34_ito` (**(1.34)'s line holds verbatim**):
  `E_s[n_t(B + M)_t − n_s(B + M)_s] = −E_s∫_s^t (Λs + (i − i^m)nM) du`, because `B + M` has no
  diffusion (`ItoMonetaryModel.wealth_ito`).
-/

namespace Cochrane.Monetarism.TidyR7MonetarismIto

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoSums Cochrane.Monetarism.TidyR7ItoIntegral
  Cochrane.Monetarism.TidyR7ItoUnbounded Cochrane.Monetarism.TidyR7ItoProducts
  Cochrane.Monetarism.TidyR7ItoProcess Cochrane.Monetarism.TidyR7ItoProductRule
  Cochrane.Monetarism.TidyR7ItoBondStep Cochrane.Monetarism.TidyR7MonetarismModel
open Cochrane.Monetarism.TidyR7ProductStep (sumRS sumCross addProc)
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: **the integral `∫_s^t X dY`** against an Itô
process `Y` with drift `b` and diffusion `K`: `∫_s^t X b du + ∫_s^t X K dW` (mean-square time
integral plus Itô integral). -/
noncomputable def intIto (μ : Measure Ω) (𝓕 : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ℝ)
    (X b K : ℝ → Ω → ℝ) (s t : ℝ) (ω : Ω) : ℝ :=
  dtInt μ 𝓕 (fun u ω => X u ω * b u ω) s t ω + itoInt μ 𝓕 W (fun u ω => X u ω * K u ω) s t ω

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: **the money term `∫_s^t n dM = ∫_s^t (Λ/P) dM`**
of (1.32) (`Λ dM/P` integrated), money having drift `m` and diffusion `σ_M`. -/
noncomputable def moneyInt (μ : Measure Ω) (𝓕 : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ℝ)
    (Λ P m σM : ℝ → Ω → ℝ) (s t : ℝ) (ω : Ω) : ℝ :=
  intIto μ 𝓕 W (disc Λ P) m σM s t ω

variable {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ} {s t : ℝ}

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: `E_s[∫_s^t X dY] = E_s[∫_s^t X b du]` a.s. (the
`dW` part has conditional mean `0`), for mean-square continuous `X`, `0 ≤ s`.
A corollary of `TidyR7ItoUnbounded.condExp_itoInt_ms`. -/
theorem condExp_intIto (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) {X b K : ℝ → Ω → ℝ} {Cb CK : ℝ}
    (hX : MSIntegrand μ 𝓕 X s t) (hb : ItoIntegrand μ 𝓕 b s t Cb)
    (hK : ItoIntegrand μ 𝓕 K s t CK) :
    μ[intIto μ 𝓕 W X b K s t | 𝓕 s] =ᵐ[μ]
      μ[dtInt μ 𝓕 (fun u ω => X u ω * b u ω) s t | 𝓕 s] := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have hG := MSIntegrand.mul_itoIntegrand hX hK
  exact condExp_eq_of_ae_eq_add (ae_of_all _ fun _ => rfl)
    ((memLp_dtInt (MSIntegrand.mul_itoIntegrand hX hb)).integrable one_le_two)
    ((memLp_itoInt_ms hBM hWm h𝓕 hs hG).integrable one_le_two)
    (condExp_itoInt_ms hBM hWm h𝓕 hs hG)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: `∫_s^t X dY` is square integrable, hence
integrable. -/
theorem integrable_intIto (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) {X b K : ℝ → Ω → ℝ} {Cb CK : ℝ}
    (hX : MSIntegrand μ 𝓕 X s t) (hb : ItoIntegrand μ 𝓕 b s t Cb)
    (hK : ItoIntegrand μ 𝓕 K s t CK) : Integrable (intIto μ 𝓕 W X b K s t) μ := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  exact ((memLp_dtInt (MSIntegrand.mul_itoIntegrand hX hb)).integrable one_le_two).add
    ((memLp_itoInt_ms hBM hWm h𝓕 hs (MSIntegrand.mul_itoIntegrand hX hK)).integrable
      one_le_two)

/-! ## The model -/

variable (μ 𝓕 W) (Λ P B M i im sp β σB m σM σX : ℝ → Ω → ℝ) (s t Cn CX Cβ CB Cm CM : ℝ)

/-- **Cochrane (2023), A1 §1.6, (1.31)–(1.34), pp. 567–568: the money–bond model with diffusive
bonds on `[s, t]`.** `P > 0`; `n = Λ/P` an Itô process with drift `−i n` (bond pricing,
`E_t d(Λ/P) = −i(Λ/P) dt`) and diffusion `σ_X`; bonds `B` (drift `β`, diffusion `σ_B`) and
money `M` (drift `m`, diffusion `σ_M`) Itô processes; the flow (1.31) on the coefficients,
`β + m = iB + i^mM − Ps` and `σ_B + σ_M = 0`. -/
structure ItoMonetaryModel where
  P_pos : ∀ u ω, 0 < P u ω
  disc_ito : ItoProcess μ 𝓕 W (disc Λ P) (fun u ω => -(i u ω * disc Λ P u ω)) σX s t Cn CX
  bonds_ito : ItoProcess μ 𝓕 W B β σB s t Cβ CB
  money_ito : ItoProcess μ 𝓕 W M m σM s t Cm CM
  flow_drift : ∀ u ω, β u ω + m u ω = flowRate B M P i im sp u ω
  flow_diff : ∀ u ω, σB u ω + σM u ω = 0

variable {μ 𝓕 W Λ P B M i im sp β σB m σM σX s t Cn CX Cβ CB Cm CM}

namespace ItoMonetaryModel

variable (hm : ItoMonetaryModel μ 𝓕 W Λ P B M i im sp β σB m σM σX s t Cn CX Cβ CB Cm CM)
include hm

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567: **diffusive bonds force diffusive money**,
`σ_M = −σ_B`. -/
theorem money_diff (u : ℝ) (ω : Ω) : σM u ω = -σB u ω := by
  have := hm.flow_diff u ω
  linarith

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567, the first line as rates: (1.31) divided by `P`,
`β/P − iB/P = −s − m/P + i^mM/P` (drift part) and `σ_B/P + σ_M/P = 0` (diffusion part), i.e.
`dB/P + E_t[d(Λ/P)/(Λ/P)]B/P = −s dt − dM/P` when `i^m = 0`. -/
theorem line1_1_32_rate (u : ℝ) (ω : Ω) :
    β u ω / P u ω - i u ω * B u ω / P u ω =
        -sp u ω - m u ω / P u ω + im u ω * M u ω / P u ω ∧
      σB u ω / P u ω + σM u ω / P u ω = 0 := by
  have hP := (hm.P_pos u ω).ne'
  have h1 := hm.flow_drift u ω
  have h2 := hm.flow_diff u ω
  simp only [flowRate] at h1
  constructor
  · field_simp
    linarith
  · rw [← add_div, h2, zero_div]

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: **the rate identity behind (1.32)**: with
`n = Λ/P` and `nP = Λ`, (1.31) times `n` reads
`Λs − i^m nM = −(B·(−in) + nβ + nm)`. -/
theorem rate_1_32 (u : ℝ) (ω : Ω) :
    Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω =
      -1 * (B u ω * -(i u ω * disc Λ P u ω) + disc Λ P u ω * β u ω
        + disc Λ P u ω * m u ω) := by
  have hn : disc Λ P u ω * P u ω = Λ u ω := div_mul_cancel₀ (Λ u ω) (hm.P_pos u ω).ne'
  have h1 := hm.flow_drift u ω
  simp only [flowRate] at h1
  linear_combination (disc Λ P u ω) * h1 - sp u ω * hn

/-- Cochrane (2023), A1 §1.6, (1.34), p. 567: **the rate identity behind (1.34)**:
`Λs + (i − i^m)nM = −(n(β + m) + (B + M)(−in))`. -/
theorem rate_1_34 (u : ℝ) (ω : Ω) :
    Λ u ω * sp u ω + (i u ω - im u ω) * disc Λ P u ω * M u ω =
      -1 * (disc Λ P u ω * (β u ω + m u ω)
        + addProc B M u ω * -(i u ω * disc Λ P u ω)) := by
  have hn : disc Λ P u ω * P u ω = Λ u ω := div_mul_cancel₀ (Λ u ω) (hm.P_pos u ω).ne'
  have h1 := hm.flow_drift u ω
  simp only [flowRate] at h1
  simp only [addProc]
  linear_combination (disc Λ P u ω) * h1 - sp u ω * hn

/-- **Cochrane (2023), A1 §1.6, (1.31), p. 567: bonds plus money is an Itô process with drift
`β + m` and no diffusion** (`B + M` is locally riskless), `0 ≤ s`. -/
theorem wealth_ito (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) :
    ItoProcess μ 𝓕 W (addProc B M) (fun u ω => β u ω + m u ω) (fun _ _ => 0) s t
      (Cβ + Cm) 0 := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have hb := hm.bonds_ito
  have hM := hm.money_ito
  refine ⟨fun u hu => (hb.adapted u hu).add (hM.adapted u hu), hb.init.add hM.init,
    hb.drift.add hM.drift, itoIntegrand_const (c := fun _ => (0 : ℝ)) stronglyMeasurable_const
      (fun _ => by simp), fun u hu => ?_⟩
  have hσ : ItoIntegrand μ 𝓕 (fun u ω => σB u ω + σM u ω) s u (CB + CM) :=
    (hb.diff.add hM.diff).mono le_rfl hu.2
  have e0 : (fun u ω => σB u ω + σM u ω) = fun _ _ => (0 : ℝ) :=
    funext fun u => funext fun ω => hm.flow_diff u ω
  have hadd := itoInt_add hBM hWm h𝓕 hs (hb.diff.mono le_rfl hu.2) (hM.diff.mono le_rfl hu.2)
  have hz : itoInt μ 𝓕 W (fun u ω => σB u ω + σM u ω) s u =ᵐ[μ] 0 := by
    rw [e0]
    filter_upwards [itoInt_const hBM hWm h𝓕 hs hu.1 (c := fun _ => (0 : ℝ))
      stronglyMeasurable_const (C := 0) (fun _ => by simp)] with ω hω
    rw [hω]
    simp
  have hz' : itoInt μ 𝓕 W (fun _ _ => (0 : ℝ)) s u =ᵐ[μ] 0 := by
    rw [← e0]
    exact hz
  filter_upwards [hb.eq u hu, hM.eq u hu, hadd, hz, hz', hb.drift.cont, hM.drift.cont] with
    ω h1 h2 h3 h4 h5 c1 c2
  have hsub : Set.uIcc s u ⊆ Set.Icc s t := by
    rw [Set.uIcc_of_le hu.1]
    exact Set.Icc_subset_Icc le_rfl hu.2
  have i1 : IntervalIntegrable (fun r => β r ω) MeasureSpace.volume s u :=
    (c1.mono hsub).intervalIntegrable
  have i2 : IntervalIntegrable (fun r => m r ω) MeasureSpace.volume s u :=
    (c2.mono hsub).intervalIntegrable
  simp only [addProc, h1, h2]
  rw [intervalIntegral.integral_add i1 i2, h5]
  simp only [Pi.zero_apply] at h4
  rw [h3] at h4
  simp only [Pi.zero_apply]
  linarith

/-- **Cochrane (2023), A1 §1.6, (1.31), p. 567: the nominal flow path by path.** For
`u ∈ [s, t]`, a.s. `(B + M)_u − (B + M)_s = ∫_s^u (i_rB_r + i^m_rM_r − P_rs_r) dr`: the flow
condition of `TidyR7MonetarismModel.MonetaryModel` on `[s, t]`. -/
theorem flow_1_31 (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) {u : ℝ} (hu : u ∈ Set.Icc s t) :
    (fun ω => addProc B M u ω - addProc B M s ω) =ᵐ[μ]
      fun ω => ∫ r in s..u, flowRate B M P i im sp r ω := by
  have hw := hm.wealth_ito hBM hWm h𝓕 hs
  have e0 : (fun r ω => β r ω + m r ω) = flowRate B M P i im sp :=
    funext fun r => funext fun ω => hm.flow_drift r ω
  filter_upwards [hw.eq u hu, itoInt_const hBM hWm h𝓕 hs hu.1 (c := fun _ => (0 : ℝ))
      stronglyMeasurable_const (C := 0) (fun _ => by simp)] with ω h1 h2
  have h2' : itoInt μ 𝓕 W (fun _ _ => (0 : ℝ)) s u ω = 0 := by
    rw [h2]
    simp
  rw [h1, h2', ← e0]
  ring

/-! ## The corrected (1.32) -/

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the corrected (1.32), general `i^m`.** For
`0 ≤ s < t`, almost surely
`E_s[n_tB_t − n_sB_s] = E_s[−(∫_s^t (Λs − i^m nM) du + ∫_s^t n dM) + ∫_s^t σ_Xσ_B du]`,
`n = Λ/P`: the book's right-hand side plus the bracket `E_s d[n, B] = E_s[σ_Bσ_X] dt`.
The Itô version of `TidyR7MonetarismModel.MonetaryModel.incr_1_32_general`. -/
theorem incr_1_32_ito_general (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t) :
    μ[fun ω => disc Λ P t ω * B t ω - disc Λ P s ω * B s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => -(dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω) s t ω
        + moneyInt μ 𝓕 W Λ P m σM s t ω) + ∫ u in s..t, σX u ω * σB u ω | 𝓕 s] := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have hn := hm.disc_ito
  have hb := hm.bonds_ito
  have hM := hm.money_ito
  have nMS := hn.toMS hBM hWm h𝓕 hs
  have bMS := hb.toMS hBM hWm h𝓕 hs
  have G1 := MSIntegrand.mul_itoIntegrand nMS hb.drift
  have G2 := MSIntegrand.mul_itoIntegrand bMS hn.drift
  have G3 := MSIntegrand.mul_itoIntegrand nMS hM.drift
  have G4 := MSIntegrand.mul_itoIntegrand nMS hM.diff
  have hprod := condExp_product_rule hBM hWm h𝓕 hs hst hn hb
  set d1 := dtInt μ 𝓕 (fun u ω => disc Λ P u ω * β u ω) s t with hd1
  set d2 := dtInt μ 𝓕 (fun u ω => B u ω * -(i u ω * disc Λ P u ω)) s t with hd2
  set d3 := dtInt μ 𝓕 (fun u ω => disc Λ P u ω * m u ω) s t with hd3
  set I := itoInt μ 𝓕 W (fun u ω => disc Λ P u ω * σM u ω) s t with hI
  set Q : Ω → ℝ := fun ω => ∫ u in s..t, σX u ω * σB u ω with hQ
  have eD : dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω) s t =ᵐ[μ]
      fun ω => -(d2 ω + d1 ω + d3 ω) := by
    have e : (fun u ω => Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω) =
        fun u ω => -1 * (B u ω * -(i u ω * disc Λ P u ω) + disc Λ P u ω * β u ω
          + disc Λ P u ω * m u ω) := funext fun u => funext fun ω => hm.rate_1_32 u ω
    rw [e]
    filter_upwards [dtInt_const_mul (MSIntegrand.add (MSIntegrand.add G2 G1) G3) (-1),
      dtInt_add (MSIntegrand.add G2 G1) G3,
      dtInt_add G2 G1] with ω h1 h2 h3
    rw [h1, h2, Pi.add_apply, h3, Pi.add_apply]
    ring
  have iR0 : Integrable (fun ω => d1 ω + d2 ω + Q ω) μ :=
    (((memLp_dtInt G1).integrable one_le_two).add ((memLp_dtInt G2).integrable one_le_two)).add
      ((memLp_integral_drift (itoIntegrand_mul hn.diff hb.diff) le_rfl hst.le
        le_rfl).integrable one_le_two)
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

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the corrected (1.32), `i^m = 0` (the book's
case): `E_t d(ΛB/P) = −Λ(s dt + dM/P) + E_t[σ_Bσ_X] dt`, integrated.** For `0 ≤ s < t`, a.s.
`E_s[n_tB_t − n_sB_s] = E_s[−(∫_s^t Λs du + ∫_s^t n dM) + ∫_s^t σ_Xσ_B du]`.
The Itô version of `TidyR7MonetarismModel.MonetaryModel.incr_1_32`. -/
theorem incr_1_32_ito (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t) (him : ∀ u ω, im u ω = 0) :
    μ[fun ω => disc Λ P t ω * B t ω - disc Λ P s ω * B s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => -(dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω) s t ω
        + moneyInt μ 𝓕 W Λ P m σM s t ω) + ∫ u in s..t, σX u ω * σB u ω | 𝓕 s] := by
  have h := hm.incr_1_32_ito_general hBM hWm h𝓕 hs hst
  have e : (fun u ω => Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω) =
      fun u ω => Λ u ω * sp u ω := funext fun u => funext fun ω => by simp [him]
  rwa [e] at h

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the book's right-hand side
`−(∫_s^t (Λs − i^m nM) du + ∫_s^t n dM)` is integrable. -/
theorem integrable_rhs_1_32 (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) :
    Integrable (fun ω => -(dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω
      - im u ω * disc Λ P u ω * M u ω) s t ω + moneyInt μ 𝓕 W Λ P m σM s t ω)) μ := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have hn := hm.disc_ito
  have hb := hm.bonds_ito
  have hM := hm.money_ito
  have nMS := hn.toMS hBM hWm h𝓕 hs
  have bMS := hb.toMS hBM hWm h𝓕 hs
  have G := MSIntegrand.add (MSIntegrand.add (MSIntegrand.mul_itoIntegrand bMS hn.drift)
    (MSIntegrand.mul_itoIntegrand nMS hb.drift)) (MSIntegrand.mul_itoIntegrand nMS hM.drift)
  have e : (fun u ω => Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω) =
      fun u ω => -1 * (B u ω * -(i u ω * disc Λ P u ω) + disc Λ P u ω * β u ω
        + disc Λ P u ω * m u ω) := funext fun u => funext fun ω => hm.rate_1_32 u ω
  rw [e]
  exact (((memLp_dtInt (MSIntegrand.const_mul G (-1))).integrable one_le_two).add
    (integrable_intIto hBM hWm h𝓕 hs nMS hM.drift hM.diff)).neg

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: when the last line of (1.32) as printed is
right.** For `0 ≤ s < t`, the book's
`E_s[n_tB_t − n_sB_s] = −E_s[∫_s^t (Λs − i^m nM) du + ∫_s^t n dM]` holds a.s. **iff**
`E_s[∫_s^t σ_Xσ_B du] = 0` a.s. -/
theorem incr_1_32_ito_book_iff (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t) :
    (μ[fun ω => disc Λ P t ω * B t ω - disc Λ P s ω * B s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => -(dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω) s t ω
        + moneyInt μ 𝓕 W Λ P m σM s t ω) | 𝓕 s]) ↔
      μ[fun ω => ∫ u in s..t, σX u ω * σB u ω | 𝓕 s] =ᵐ[μ] 0 := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have iF := hm.integrable_rhs_1_32 hBM hWm h𝓕 hs
  have iQ : Integrable (fun ω => ∫ u in s..t, σX u ω * σB u ω) μ :=
    (memLp_integral_drift (itoIntegrand_mul hm.disc_ito.diff hm.bonds_ito.diff) le_rfl hst.le
      le_rfl).integrable one_le_two
  have hmain := (hm.incr_1_32_ito_general hBM hWm h𝓕 hs hst).trans (condExp_add iF iQ (𝓕 s))
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
diffusion is uncorrelated with `Λ/P`**, `σ_Xσ_B = 0` on `[s, t]` a.s. (in particular for bonds
of bounded variation, `σ_B = 0`, with `Λ/P` still diffusive).
Compare `TidyR7MonetarismModel.MonetaryModel.incr_1_32`. -/
theorem incr_1_32_ito_uncorrelated (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hσ : ∀ᵐ ω ∂μ, ∀ u ∈ Set.Icc s t, σX u ω * σB u ω = 0) :
    μ[fun ω => disc Λ P t ω * B t ω - disc Λ P s ω * B s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => -(dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω) s t ω
        + moneyInt μ 𝓕 W Λ P m σM s t ω) | 𝓕 s] := by
  refine (hm.incr_1_32_ito_book_iff hBM hWm h𝓕 hs hst).2 ?_
  have h := condExp_bracket_zero (𝓕 := 𝓕) (σB := fun u ω => σX u ω * σB u ω)
    (σX := fun _ _ => (1 : ℝ)) hst.le hσ
  simpa using h

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the middle line of (1.32) holds verbatim**,
`(Λ/P) dB + E_t[d(Λ/P)]B = −Λ(s dt + dM/P)` integrated: for `0 ≤ s < t`, a.s.
`E_s[∫_s^t n dB] + E_s[∫_s^t B(−in) du] = E_s[−(∫_s^t (Λs − i^m nM) du + ∫_s^t n dM)]`
(`B·E_s d(Λ/P) = E_s∫B(−in) du`, `middle_1_32_ito_expIncr`). It is (1.31) times `n`; no product
step is involved, so no bracket.
The Itô version of `TidyR7MonetarismModel.MonetaryModel.middle_1_32`. -/
theorem middle_1_32_ito (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) :
    μ[intIto μ 𝓕 W (disc Λ P) β σB s t | 𝓕 s]
        + μ[dtInt μ 𝓕 (fun u ω => B u ω * -(i u ω * disc Λ P u ω)) s t | 𝓕 s] =ᵐ[μ]
      μ[fun ω => -(dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω) s t ω
        + moneyInt μ 𝓕 W Λ P m σM s t ω) | 𝓕 s] := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have hn := hm.disc_ito
  have hb := hm.bonds_ito
  have hM := hm.money_ito
  have nMS := hn.toMS hBM hWm h𝓕 hs
  have bMS := hb.toMS hBM hWm h𝓕 hs
  have G1 := MSIntegrand.mul_itoIntegrand nMS hb.drift
  have G2 := MSIntegrand.mul_itoIntegrand bMS hn.drift
  have G3 := MSIntegrand.mul_itoIntegrand nMS hM.drift
  have G4 := MSIntegrand.mul_itoIntegrand nMS hM.diff
  set d1 := dtInt μ 𝓕 (fun u ω => disc Λ P u ω * β u ω) s t with hd1
  set d2 := dtInt μ 𝓕 (fun u ω => B u ω * -(i u ω * disc Λ P u ω)) s t with hd2
  set I := itoInt μ 𝓕 W (fun u ω => disc Λ P u ω * σM u ω) s t with hI
  have i1 : Integrable d1 μ := (memLp_dtInt G1).integrable one_le_two
  have i2 : Integrable d2 μ := (memLp_dtInt G2).integrable one_le_two
  have iI : Integrable I μ := (memLp_itoInt_ms hBM hWm h𝓕 hs G4).integrable one_le_two
  have e : (fun u ω => Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω) =
      fun u ω => -1 * (B u ω * -(i u ω * disc Λ P u ω) + disc Λ P u ω * β u ω
        + disc Λ P u ω * m u ω) := funext fun u => funext fun ω => hm.rate_1_32 u ω
  have hR : μ[fun ω => -(dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω
        - im u ω * disc Λ P u ω * M u ω) s t ω + moneyInt μ 𝓕 W Λ P m σM s t ω) | 𝓕 s] =ᵐ[μ]
      μ[d1 + d2 | 𝓕 s] := by
    refine condExp_eq_of_ae_eq_add (h := fun ω => -I ω) ?_ (i1.add i2) iI.neg ?_
    · rw [e]
      filter_upwards [dtInt_const_mul (MSIntegrand.add (MSIntegrand.add G2 G1) G3) (-1),
      dtInt_add (MSIntegrand.add G2 G1) G3,
        dtInt_add G2 G1] with ω h1 h2 h3
      simp only [moneyInt, intIto, Pi.add_apply]
      rw [h1, h2, Pi.add_apply, h3, Pi.add_apply]
      simp only [hd1, hd2, hI]
      ring
    · filter_upwards [condExp_neg (μ := μ) I (𝓕 s), condExp_itoInt_ms hBM hWm h𝓕 hs G4] with
        ω h1 h2
      change μ[-I | 𝓕 s] ω = 0
      rw [h1, Pi.neg_apply, h2]
      simp
  filter_upwards [hR, condExp_add i1 i2 (𝓕 s), condExp_intIto hBM hWm h𝓕 hs nMS hb.drift
    hb.diff] with ω h1 h2 h3
  rw [Pi.add_apply, h3, h1, h2, Pi.add_apply]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the middle line in the expected-increment
reading.** For `0 ≤ s < t` and partitions with mesh `→ 0`, in `L¹`:
`E_s[Σ n_iΔB_i] → E_s∫_s^t nβ du = E_s[∫_s^t n dB]` (the book's `(Λ/P) dB`) and
`E_s[Σ B_iΔn_i] → E_s∫_s^t B(−in) du` (the book's `E_t[d(Λ/P)]B`, `E_t d(Λ/P) = −i(Λ/P) dt`),
and the middle line `middle_1_32_ito` holds. -/
theorem middle_1_32_ito_expIncr (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, |μ[sumRS (ps k) (disc Λ P) B | 𝓕 s] ω
      - μ[intIto μ 𝓕 W (disc Λ P) β σB s t | 𝓕 s] ω| ∂μ) atTop (𝓝 0) ∧
    Tendsto (fun k => ∫ ω, |μ[sumRS (ps k) B (disc Λ P) | 𝓕 s] ω
      - μ[dtInt μ 𝓕 (fun u ω => B u ω * -(i u ω * disc Λ P u ω)) s t | 𝓕 s] ω| ∂μ)
      atTop (𝓝 0) ∧
    (μ[intIto μ 𝓕 W (disc Λ P) β σB s t | 𝓕 s]
        + μ[dtInt μ 𝓕 (fun u ω => B u ω * -(i u ω * disc Λ P u ω)) s t | 𝓕 s] =ᵐ[μ]
      μ[fun ω => -(dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω) s t ω
        + moneyInt μ 𝓕 W Λ P m σM s t ω) | 𝓕 s]) := by
  have hn := hm.disc_ito
  have hb := hm.bonds_ito
  have h := bond_step_expIncr hBM hWm h𝓕 hs hst hb hn ps hps
  have hc := condExp_intIto hBM hWm h𝓕 hs (hn.toMS hBM hWm h𝓕 hs) hb.drift hb.diff
  refine ⟨?_, h.2.1, hm.middle_1_32_ito hBM hWm h𝓕 hs⟩
  have e : ∀ k, ∫ ω, |μ[sumRS (ps k) (disc Λ P) B | 𝓕 s] ω
      - μ[intIto μ 𝓕 W (disc Λ P) β σB s t | 𝓕 s] ω| ∂μ =
      ∫ ω, |μ[sumRS (ps k) (disc Λ P) B | 𝓕 s] ω
      - μ[dtInt μ 𝓕 (fun u ω => disc Λ P u ω * β u ω) s t | 𝓕 s] ω| ∂μ := fun k =>
    integral_congr_ae (by filter_upwards [hc] with ω hω; rw [hω])
  simp_rw [e]
  exact h.2.2.1

/-! ## (1.34) -/

/-- **Cochrane (2023), A1 §1.6, p. 567, the line before (1.34), verbatim with diffusive bonds:
`E_t d(Λ(M + B)/P) = −Λ(s + (i − i^m)M/P) dt`, integrated.** For `0 ≤ s < t`, a.s.
`E_s[n_t(B + M)_t − n_s(B + M)_s] = −E_s∫_s^t (Λs + (i − i^m)nM) du`. No bracket: `B + M` has no
diffusion (`wealth_ito`).
The Itô version of `TidyR7MonetarismModel.MonetaryModel.incr_1_34`. -/
theorem incr_1_34_ito (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t) :
    μ[fun ω => disc Λ P t ω * addProc B M t ω - disc Λ P s ω * addProc B M s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => -dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω
        + (i u ω - im u ω) * disc Λ P u ω * M u ω) s t ω | 𝓕 s] := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have hn := hm.disc_ito
  have hw := hm.wealth_ito hBM hWm h𝓕 hs
  have nMS := hn.toMS hBM hWm h𝓕 hs
  have wMS := hw.toMS hBM hWm h𝓕 hs
  have G1 := MSIntegrand.mul_itoIntegrand nMS hw.drift
  have G2 := MSIntegrand.mul_itoIntegrand wMS hn.drift
  have hprod := condExp_product_rule hBM hWm h𝓕 hs hst hn hw
  refine hprod.trans (condExp_congr_ae ?_)
  have e : (fun u ω => Λ u ω * sp u ω + (i u ω - im u ω) * disc Λ P u ω * M u ω) =
      fun u ω => -1 * (disc Λ P u ω * (β u ω + m u ω)
        + addProc B M u ω * -(i u ω * disc Λ P u ω)) :=
    funext fun u => funext fun ω => hm.rate_1_34 u ω
  rw [e]
  filter_upwards [dtInt_const_mul (MSIntegrand.add G1 G2) (-1), dtInt_add G1 G2] with ω h1 h2
  rw [h1, h2, Pi.add_apply]
  simp

end ItoMonetaryModel

end Cochrane.Monetarism.TidyR7MonetarismIto
