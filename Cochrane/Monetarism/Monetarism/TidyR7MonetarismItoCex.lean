/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR7MonetarismItoValuation

/-!
# Brownian economies for (1.32) with diffusive bonds: the book's step fails, and holds

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Two instances of
`TidyR7MonetarismIto.ItoMonetaryModel` on the constructed Brownian motion
`TidyR7BrownianExist.bmPath` under `gaussSeq` with its natural filtration (`bmF`).

## Economy 1: bonds' diffusion correlated with `Λ/P` (`cexModel`)

`P = 1`, `Λ = Λ/P = 1 + W`, `i = i^m = 0`, surplus `s = 0`, bonds `B = b + cW`, money
`M = M₀ − cW` (forced by (1.31): `B + M = b + M₀` is riskless), `σ_X = 1`, `σ_B = c`. On
`[0, 1]`: `E[n_1B_1 − n_0B_0] = c` (`cex_lhs`), the book's right-hand side
`−E[∫Λs + ∫n dM] = 0` (`cex_book_rhs`), the bracket `E∫_0^1 σ_Xσ_B = c` (`cex_bracket`): the
corrected (1.32) holds, `c = 0 + c`, and for `c ≠ 0` the book's last line of (1.32) fails
conditionally on every `[s, t]` (`cex_book_fails`). With `c = 1`: `1 ≠ 0`.

`Λ/P = 1 + W` is not positive. Positivity cannot be had here: the toolkit's Itô processes have
bounded a.s. continuous coefficients, and a positive diffusive `Λ/P` such as `exp(W − t/2)` has
diffusion coefficient `Λ/P` itself (unbounded) and needs the Itô formula for `exp`, which is
not formalised. The algebra of (1.32) uses only `P ≠ 0` (`P = 1` here); positivity of `Λ` enters
only the book's division by `Λ_s` (`TidyR7MonetarismItoValuation.real_form_ito`).

## Economy 2: both diffusive, driven on disjoint time intervals (`disjModel`)

`P = 1`, `Λ/P = 1 + ∫_0^· φ dW`, `B = b + ∫_0^· ψ dW`, `M = M₀ − ∫_0^· ψ dW`, with the ramps
`φ = min 1 (max 0 (1 − u))` (`rampDown`), `ψ = min 1 (max 0 (u − 1))` (`rampUp`): `φψ = 0`
everywhere although `φ(0) = ψ(2) = 1`. The book's last line of (1.32) holds on every `[s, t]`
(`disj_1_32`) and the book's (1.33) holds iff transversality (`disj_1_33`): the condition is
`E_s∫σ_Bσ_X du = 0`, not `σ_B = 0`.
-/

namespace Cochrane.Monetarism.TidyR7MonetarismItoCex

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoSums Cochrane.Monetarism.TidyR7ItoIntegral
  Cochrane.Monetarism.TidyR7ItoUnbounded Cochrane.Monetarism.TidyR7ItoProducts
  Cochrane.Monetarism.TidyR7ItoProcess Cochrane.Monetarism.TidyR7ItoProductRule
  Cochrane.Monetarism.TidyR7ItoBondStep Cochrane.Monetarism.TidyR7MonetarismModel
  Cochrane.Monetarism.TidyR7MonetarismIto Cochrane.Monetarism.TidyR7MonetarismItoValuation
  Cochrane.Monetarism.TidyR7BrownianExist Cochrane.Monetarism.TidyR7ItoBridge
  Cochrane.Monetarism.TidyR7BrownianSchauder
open scoped ENNReal NNReal

/-! ## Two generic Itô processes -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (test processes for (1.32)): `a + cW` is an Itô
process on `[s, t]`, `0 ≤ s`, with drift `0` and diffusion `c`.
Generalises `TidyR7ItoProductRule.itoProcess_bm`. -/
theorem itoProcess_affine {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ} {s t : ℝ} (hBM : IsPreBrownianReal W μ)
    (hWm : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) {X a : ℝ → Ω → ℝ}
    (a0 c : ℝ) {C : ℝ} (hC : |c| ≤ C) (hX : X = fun u ω => a0 + c * bmReal W u ω)
    (ha : a = fun _ _ => 0) : ItoProcess μ 𝓕 W X a (fun _ _ => c) s t 0 C := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  subst hX ha
  exact
    { adapted := fun u _ => stronglyMeasurable_const.add
        (stronglyMeasurable_const.mul (h𝓕.adapted u))
      init := (memLp_const a0).add
        ((hBM.isGaussianProcess.hasGaussianLaw_eval _).memLp_two.const_mul c)
      drift := itoIntegrand_const (c := fun _ => (0 : ℝ)) stronglyMeasurable_const
        (fun _ => by simp)
      diff := itoIntegrand_const (c := fun _ => c) stronglyMeasurable_const (fun _ => hC)
      eq := fun u hu => by
        filter_upwards [itoInt_const hBM hWm h𝓕 hs hu.1 (c := fun _ => c)
          stronglyMeasurable_const (C := C) (fun _ => hC)] with ω hω
        rw [hω]
        simp only [incr, intervalIntegral.integral_zero]
        ring }

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (test processes for (1.32)): `a + ∫_r^· H dW` is an
Itô process on `[s, t]`, `0 ≤ r ≤ s ≤ t`, with drift `0` and diffusion `H`.
Generalises `TidyR7ItoBondStep.itoProcess_itoInt`. -/
theorem itoProcess_shift {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ} {s t r : ℝ} (hBM : IsPreBrownianReal W μ)
    (hWm : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration μ W 𝓕) (hr : 0 ≤ r) (hrs : r ≤ s)
    (hst : s ≤ t) {X a H : ℝ → Ω → ℝ} {C : ℝ} (hH : ItoIntegrand μ 𝓕 H r t C) (a0 : ℝ)
    (hX : X = fun u ω => a0 + itoInt μ 𝓕 W H r u ω) (ha : a = fun _ _ => 0) :
    ItoProcess μ 𝓕 W X a H s t 0 C := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  subst hX ha
  exact
    { adapted := fun _ _ => stronglyMeasurable_const.add stronglyMeasurable_itoInt
      init := (memLp_const a0).add (memLp_itoInt hBM hWm h𝓕 hr (hH.mono le_rfl hst))
      drift := itoIntegrand_const (c := fun _ => (0 : ℝ)) stronglyMeasurable_const
        (fun _ => by simp)
      diff := hH.mono hrs le_rfl
      eq := fun u hu => by
        filter_upwards [itoInt_add_itoInt hBM hWm h𝓕 hr hrs hu.1 (hH.mono le_rfl hu.2)] with
          ω hω
        rw [hω]
        simp only [intervalIntegral.integral_zero]
        ring }

/-! ## The probability space -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the natural filtration of the constructed Brownian
motion `bmPath`, indexed by `ℝ`. -/
noncomputable abbrev bmF : Filtration ℝ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
  bmFiltrationReal bmPath measurable_bmPath

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the constant process `c`. -/
abbrev constP (c : ℝ) : ℝ → (ℕ → ℝ) → ℝ := fun _ _ => c

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `gaussSeq` is a probability measure.
Restates `TidyR7BrownianSchauder.isProbabilityMeasure_gaussSeq`. -/
theorem isProb : IsProbabilityMeasure gaussSeq :=
  isPreBrownianReal_bmPath.isGaussianProcess.isProbabilityMeasure

/-! ## Economy 1 -/

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (counterexample): the SDF `Λ = 1 + W` (with
`P = 1`, `Λ/P = 1 + W`). -/
noncomputable abbrev cexΛ : ℝ → (ℕ → ℝ) → ℝ := fun u ω => 1 + 1 * bmReal bmPath u ω

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (counterexample): bonds `B = b + cW`. -/
noncomputable abbrev cexB (b c : ℝ) : ℝ → (ℕ → ℝ) → ℝ := fun u ω => b + c * bmReal bmPath u ω

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567 (counterexample): money `M = M₀ − cW`. -/
noncomputable abbrev cexM (M0 c : ℝ) : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => M0 + -c * bmReal bmPath u ω

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: `Λ/P = 1 + W` when `P = 1`. -/
theorem disc_cex : disc cexΛ (constP 1) = fun u ω => 1 + 1 * bmReal bmPath u ω :=
  funext fun u => funext fun ω => by simp [disc]

/-- **Cochrane (2023), A1 §1.6, (1.31)–(1.34), pp. 567–568: economy 1 is a model with diffusive
bonds.** On every `[s, t]`, `0 ≤ s`: `P = 1`, `Λ/P = 1 + W`, `i = i^m = s = 0`, `B = b + cW`,
`M = M₀ − cW`, `σ_X = 1`, `σ_B = c`, `σ_M = −c`. -/
theorem cexModel (b c M0 : ℝ) {s t : ℝ} (hs : 0 ≤ s) :
    ItoMonetaryModel gaussSeq bmF bmPath cexΛ (constP 1) (cexB b c) (cexM M0 c) (constP 0)
      (constP 0) (constP 0) (constP 0) (constP c) (constP 0) (constP (-c)) (constP 1) s t
      0 1 0 |c| 0 |-c| where
  P_pos _ _ := one_pos
  disc_ito := by
    have hBM := isPreBrownianReal_bmPath
    have h𝓕 := bmFiltrationReal_isBM hBM measurable_bmPath
    refine itoProcess_affine hBM measurable_bmPath h𝓕 hs 1 1 (C := 1) (by simp) ?_ ?_
    · exact disc_cex
    · funext u ω
      simp
  bonds_ito := itoProcess_affine isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) hs b c le_rfl rfl rfl
  money_ito := itoProcess_affine isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) hs M0 (-c) le_rfl rfl
    rfl
  flow_drift _ _ := by simp [flowRate]
  flow_diff _ _ := by simp

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567 (counterexample, left side):**
`E[n_1B_1 − n_0B_0] = E[(1 + W_1)(b + cW_1)] − b = c`. -/
theorem cex_lhs (b c : ℝ) :
    ∫ ω, (disc cexΛ (constP 1) 1 ω * cexB b c 1 ω - disc cexΛ (constP 1) 0 ω * cexB b c 0 ω)
      ∂gaussSeq = c := by
  have := isProb
  have e : (fun ω => disc cexΛ (constP 1) 1 ω * cexB b c 1 ω
      - disc cexΛ (constP 1) 0 ω * cexB b c 0 ω) =
      fun ω => c * bmPath 1 ω ^ 2 + (b + c) * bmPath 1 ω := funext fun ω => by
    have w1 : bmReal bmPath 1 ω = bmPath 1 ω := by simp only [bmReal, Real.toNNReal_one]
    have w0 : bmReal bmPath 0 ω = 0 := by
      simp only [bmReal, Real.toNNReal_zero, bmPath_zero]
    simp only [disc, cexΛ, cexB, constP, w1, w0, div_one]
    ring
  have i2 : Integrable (fun ω => bmPath 1 ω ^ 2) gaussSeq :=
    (integrable_incr_sq (W := bmPath) isPreBrownianReal_bmPath 0 1).congr
      (ae_of_all _ fun ω => by simp [incr, bmReal, bmPath_zero])
  have i1 : Integrable (fun ω => bmPath 1 ω) gaussSeq :=
    (isPreBrownianReal_bmPath.isGaussianProcess.hasGaussianLaw_eval 1).memLp_two.integrable
      one_le_two
  have h2 : ∫ ω, bmPath 1 ω ^ 2 ∂gaussSeq = 1 := by
    have h := integral_incr_sq (W := bmPath) isPreBrownianReal_bmPath le_rfl zero_le_one
    simpa [incr, bmReal, bmPath_zero] using h
  rw [e, integral_add (i2.const_mul c) (i1.const_mul (b + c)), integral_const_mul,
    integral_const_mul, h2, integral_bmPath]
  ring

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567 (counterexample, the book's right side):**
`−E[∫_0^1 Λs du + ∫_0^1 n dM] = 0` (`s = 0`; `E∫n dM = E∫n(−c) dW = 0`). -/
theorem cex_book_rhs (b c M0 : ℝ) :
    ∫ ω, -(dtInt gaussSeq bmF (fun u ω => cexΛ u ω * constP 0 u ω
        - constP 0 u ω * disc cexΛ (constP 1) u ω * cexM M0 c u ω) 0 1 ω
      + moneyInt gaussSeq bmF bmPath cexΛ (constP 1) (constP 0) (constP (-c)) 0 1 ω)
      ∂gaussSeq = 0 := by
  have := isProb
  have hBM := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hBM measurable_bmPath
  have hm := cexModel b c M0 (s := 0) (t := 1) le_rfl
  have G := MSIntegrand.mul_itoIntegrand (hm.disc_ito.toMS hBM measurable_bmPath h𝓕 le_rfl)
    hm.money_ito.diff
  have z1 : dtInt gaussSeq bmF (fun u ω => cexΛ u ω * constP 0 u ω
      - constP 0 u ω * disc cexΛ (constP 1) u ω * cexM M0 c u ω) 0 1 =ᵐ[gaussSeq] 0 :=
    dtInt_of_eq_zero fun u _ ω => by simp
  have z2 : dtInt gaussSeq bmF (fun u ω => disc cexΛ (constP 1) u ω * constP 0 u ω) 0 1
      =ᵐ[gaussSeq] 0 := dtInt_of_eq_zero fun u _ ω => by simp
  have hI := integral_mul_itoInt_ms hBM measurable_bmPath h𝓕 le_rfl G
    (Z := fun _ => 1) stronglyMeasurable_const (memLp_const 1)
  have e : (fun ω => -(dtInt gaussSeq bmF (fun u ω => cexΛ u ω * constP 0 u ω
        - constP 0 u ω * disc cexΛ (constP 1) u ω * cexM M0 c u ω) 0 1 ω
      + moneyInt gaussSeq bmF bmPath cexΛ (constP 1) (constP 0) (constP (-c)) 0 1 ω))
      =ᵐ[gaussSeq] fun ω => -(1 * itoInt gaussSeq bmF bmPath
        (fun u ω => disc cexΛ (constP 1) u ω * constP (-c) u ω) 0 1 ω) := by
    filter_upwards [z1, z2] with ω h1 h2
    simp only [moneyInt, intIto]
    rw [h1, h2]
    simp
  rw [integral_congr_ae e, integral_neg, hI, neg_zero]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567 (counterexample, the bracket):**
`E[∫_0^1 σ_Xσ_B du] = E[∫_0^1 1·c du] = c`. -/
theorem cex_bracket (c : ℝ) :
    ∫ ω, (∫ u in (0 : ℝ)..1, constP 1 u ω * constP c u ω) ∂gaussSeq = c := by
  have := isProb
  simp

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567 (counterexample): the last line of (1.32) as
printed fails** in economy 1 for `c ≠ 0`, on every `[s, t]`, `0 ≤ s < t`: `E_s[n_tB_t − n_sB_s]`
is not a.s. `−E_s[∫_s^t Λs du + ∫_s^t n dM]`; the bracket `E_s∫_s^t σ_Xσ_B du = c(t − s) ≠ 0`
(`ItoMonetaryModel.incr_1_32_ito_book_iff`). -/
theorem cex_book_fails (b M0 : ℝ) {c : ℝ} (hc : c ≠ 0) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    ¬ (gaussSeq[fun ω => disc cexΛ (constP 1) t ω * cexB b c t ω
        - disc cexΛ (constP 1) s ω * cexB b c s ω | bmF s] =ᵐ[gaussSeq]
      gaussSeq[fun ω => -(dtInt gaussSeq bmF (fun u ω => cexΛ u ω * constP 0 u ω
        - constP 0 u ω * disc cexΛ (constP 1) u ω * cexM M0 c u ω) s t ω
        + moneyInt gaussSeq bmF bmPath cexΛ (constP 1) (constP 0) (constP (-c)) s t ω)
        | bmF s]) := by
  have := isProb
  have hBM := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hBM measurable_bmPath
  intro h
  have hiff := ((cexModel b c M0 (t := t) hs).incr_1_32_ito_book_iff hBM measurable_bmPath h𝓕
    hs hst).1 h
  have e : (fun ω : ℕ → ℝ => ∫ u in s..t, constP 1 u ω * constP c u ω) =
      fun _ => (t - s) * c := funext fun ω => by simp
  rw [e, condExp_const (bmF.le s)] at hiff
  obtain ⟨ω, hω⟩ := hiff.exists
  have : (t - s) * c = 0 := hω
  rcases mul_eq_zero.1 this with h1 | h1
  · linarith
  · exact hc h1

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567 (counterexample): the corrected (1.32) holds** in
economy 1 on every `[s, t]`, `0 ≤ s < t`: `E_s[n_tB_t − n_sB_s]` equals
`E_s[−(∫Λs + ∫n dM) + ∫σ_Xσ_B du]` a.s.
The instance of `ItoMonetaryModel.incr_1_32_ito_general`. -/
theorem cex_corrected (b c M0 : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    gaussSeq[fun ω => disc cexΛ (constP 1) t ω * cexB b c t ω
        - disc cexΛ (constP 1) s ω * cexB b c s ω | bmF s] =ᵐ[gaussSeq]
      gaussSeq[fun ω => -(dtInt gaussSeq bmF (fun u ω => cexΛ u ω * constP 0 u ω
        - constP 0 u ω * disc cexΛ (constP 1) u ω * cexM M0 c u ω) s t ω
        + moneyInt gaussSeq bmF bmPath cexΛ (constP 1) (constP 0) (constP (-c)) s t ω)
        + ∫ u in s..t, constP 1 u ω * constP c u ω | bmF s] :=
  (cexModel b c M0 hs).incr_1_32_ito_general isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) hs hst

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: headline counterexample** (economy 1, `[0, 1]`,
`c ≠ 0`): both sides computed, `E[n_1B_1 − n_0B_0] = c`, the book's right side has mean `0`, the
bracket has mean `c`; the book's last line of (1.32) fails conditionally; the corrected one
holds. With `c = 1`: `1 ≠ 0`. -/
theorem cex_headline (b M0 : ℝ) {c : ℝ} (hc : c ≠ 0) :
    (∫ ω, (disc cexΛ (constP 1) 1 ω * cexB b c 1 ω - disc cexΛ (constP 1) 0 ω * cexB b c 0 ω)
      ∂gaussSeq = c) ∧
    (∫ ω, -(dtInt gaussSeq bmF (fun u ω => cexΛ u ω * constP 0 u ω
        - constP 0 u ω * disc cexΛ (constP 1) u ω * cexM M0 c u ω) 0 1 ω
      + moneyInt gaussSeq bmF bmPath cexΛ (constP 1) (constP 0) (constP (-c)) 0 1 ω)
      ∂gaussSeq = 0) ∧
    (∫ ω, (∫ u in (0 : ℝ)..1, constP 1 u ω * constP c u ω) ∂gaussSeq = c) ∧
    (¬ (gaussSeq[fun ω => disc cexΛ (constP 1) 1 ω * cexB b c 1 ω
        - disc cexΛ (constP 1) 0 ω * cexB b c 0 ω | bmF 0] =ᵐ[gaussSeq]
      gaussSeq[fun ω => -(dtInt gaussSeq bmF (fun u ω => cexΛ u ω * constP 0 u ω
        - constP 0 u ω * disc cexΛ (constP 1) u ω * cexM M0 c u ω) 0 1 ω
        + moneyInt gaussSeq bmF bmPath cexΛ (constP 1) (constP 0) (constP (-c)) 0 1 ω)
        | bmF 0])) ∧
    (gaussSeq[fun ω => disc cexΛ (constP 1) 1 ω * cexB b c 1 ω
        - disc cexΛ (constP 1) 0 ω * cexB b c 0 ω | bmF 0] =ᵐ[gaussSeq]
      gaussSeq[fun ω => -(dtInt gaussSeq bmF (fun u ω => cexΛ u ω * constP 0 u ω
        - constP 0 u ω * disc cexΛ (constP 1) u ω * cexM M0 c u ω) 0 1 ω
        + moneyInt gaussSeq bmF bmPath cexΛ (constP 1) (constP 0) (constP (-c)) 0 1 ω)
        + ∫ u in (0 : ℝ)..1, constP 1 u ω * constP c u ω | bmF 0]) :=
  ⟨cex_lhs b c, cex_book_rhs b c M0, cex_bracket c, cex_book_fails b M0 hc le_rfl zero_lt_one,
    cex_corrected b c M0 le_rfl zero_lt_one⟩

/-- **Cochrane (2023), A1 §1.6, p. 567, (1.34) in economy 1:** the line before (1.34) holds
verbatim, `E_s[n_t(B + M)_t − n_s(B + M)_s] = −E_s∫_s^t (Λs + (i − i^m)nM) du` a.s.
The instance of `ItoMonetaryModel.incr_1_34_ito`. -/
theorem cex_1_34 (b c M0 : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    gaussSeq[fun ω => disc cexΛ (constP 1) t ω
        * TidyR7ProductStep.addProc (cexB b c) (cexM M0 c) t ω
      - disc cexΛ (constP 1) s ω * TidyR7ProductStep.addProc (cexB b c) (cexM M0 c) s ω
        | bmF s] =ᵐ[gaussSeq]
      gaussSeq[fun ω => -dtInt gaussSeq bmF (fun u ω => cexΛ u ω * constP 0 u ω
        + (constP 0 u ω - constP 0 u ω) * disc cexΛ (constP 1) u ω * cexM M0 c u ω) s t ω
        | bmF s] :=
  (cexModel b c M0 hs).incr_1_34_ito isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) hs hst

/-! ## Economy 2 -/

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the ramp `φ(u) = min 1 (max 0 (1 − u))`, the
diffusion of `Λ/P` in economy 2 (active on `[0, 1]`). -/
noncomputable def rampDown (u : ℝ) : ℝ := min 1 (max 0 (1 - u))

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the ramp `ψ(u) = min 1 (max 0 (u − 1))`, the
diffusion of bonds in economy 2 (active on `[1, ∞)`). -/
noncomputable def rampUp (u : ℝ) : ℝ := min 1 (max 0 (u - 1))

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: `φψ = 0` everywhere. -/
theorem rampDown_mul_rampUp (u : ℝ) : rampDown u * rampUp u = 0 := by
  rcases le_or_gt u 1 with hu | hu
  · have : rampUp u = 0 := by
      simp only [rampUp, max_eq_left (by linarith : u - 1 ≤ 0), min_eq_right zero_le_one]
    rw [this, mul_zero]
  · have : rampDown u = 0 := by
      simp only [rampDown, max_eq_left (by linarith : 1 - u ≤ 0), min_eq_right zero_le_one]
    rw [this, zero_mul]

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: both ramps are nonzero somewhere,
`φ(0) = ψ(2) = 1`. -/
theorem ramps_ne_zero : rampDown 0 = 1 ∧ rampUp 2 = 1 := by
  constructor <;> norm_num [rampDown, rampUp]

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: `|min 1 (max 0 x)| ≤ 1`. -/
theorem abs_clamp_le (x : ℝ) : |min 1 (max 0 x)| ≤ 1 := by
  rw [abs_le]
  constructor
  · exact le_min (by norm_num) (le_max_left _ _) |>.trans' (by norm_num)
  · exact min_le_left _ _

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the ramps are continuous. -/
theorem continuous_ramps : Continuous rampDown ∧ Continuous rampUp :=
  ⟨continuous_const.min (continuous_const.max (continuous_const.sub continuous_id)),
    continuous_const.min (continuous_const.max (continuous_id.sub continuous_const))⟩

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (economy 2): the SDF `Λ = Λ/P = 1 + ∫_0^· φ dW`. -/
noncomputable abbrev disjΛ : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => 1 + itoInt gaussSeq bmF bmPath (fun r _ => rampDown r) 0 u ω

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (economy 2): bonds `B = b + ∫_0^· ψ dW`. -/
noncomputable abbrev disjB (b : ℝ) : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => b + itoInt gaussSeq bmF bmPath (fun r _ => rampUp r) 0 u ω

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567 (economy 2): money `M = M₀ + ∫_0^· (−ψ) dW`. -/
noncomputable abbrev disjM (M0 : ℝ) : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => M0 + itoInt gaussSeq bmF bmPath (fun r _ => -rampUp r) 0 u ω

/-- **Cochrane (2023), A1 §1.6, (1.31)–(1.34), pp. 567–568: economy 2 is a model with diffusive
bonds and diffusive `Λ/P` driven on disjoint time intervals**, on every `[s, t]`, `0 ≤ s ≤ t`:
`P = 1`, `i = i^m = s = 0`, `σ_X = φ`, `σ_B = ψ`, `σ_M = −ψ`. -/
theorem disjModel (b M0 : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ItoMonetaryModel gaussSeq bmF bmPath disjΛ (constP 1) (disjB b) (disjM M0) (constP 0)
      (constP 0) (constP 0) (constP 0) (fun r _ => rampUp r) (constP 0) (fun r _ => -rampUp r)
      (fun r _ => rampDown r) s t 0 1 0 1 0 1 := by
  have hBM := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hBM measurable_bmPath
  have hD : ItoIntegrand gaussSeq bmF (fun r _ => rampDown r) 0 t 1 :=
    itoIntegrand_deterministic continuous_ramps.1.continuousOn fun u _ => abs_clamp_le _
  have hU : ItoIntegrand gaussSeq bmF (fun r _ => rampUp r) 0 t 1 :=
    itoIntegrand_deterministic continuous_ramps.2.continuousOn fun u _ => abs_clamp_le _
  have hU' : ItoIntegrand gaussSeq bmF (fun r _ => -rampUp r) 0 t 1 :=
    itoIntegrand_deterministic continuous_ramps.2.neg.continuousOn fun u _ => by
      rw [abs_neg]; exact abs_clamp_le _
  exact
    { P_pos := fun _ _ => one_pos
      disc_ito := itoProcess_shift hBM measurable_bmPath h𝓕 le_rfl hs hst hD 1
        (funext fun u => funext fun ω => by simp [disc]) (funext fun u => funext fun ω => by simp)
      bonds_ito := itoProcess_shift hBM measurable_bmPath h𝓕 le_rfl hs hst hU b rfl rfl
      money_ito := itoProcess_shift hBM measurable_bmPath h𝓕 le_rfl hs hst hU' M0 rfl rfl
      flow_drift := fun _ _ => by simp [flowRate]
      flow_diff := fun _ _ => by simp }

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the book's last line of (1.32) holds in economy 2
although bonds and `Λ/P` both diffuse**, on every `[s, t]`, `0 ≤ s < t`:
`E_s[n_tB_t − n_sB_s] = −E_s[∫_s^t Λs du + ∫_s^t n dM]` a.s., since `σ_Xσ_B = φψ = 0`.
An instance of `TidyR7MonetarismIto.ItoMonetaryModel.incr_1_32_ito_uncorrelated`. -/
theorem disj_1_32 (b M0 : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    gaussSeq[fun ω => disc disjΛ (constP 1) t ω * disjB b t ω
        - disc disjΛ (constP 1) s ω * disjB b s ω | bmF s] =ᵐ[gaussSeq]
      gaussSeq[fun ω => -(dtInt gaussSeq bmF (fun u ω => disjΛ u ω * constP 0 u ω
        - constP 0 u ω * disc disjΛ (constP 1) u ω * disjM M0 u ω) s t ω
        + moneyInt gaussSeq bmF bmPath disjΛ (constP 1) (constP 0) (fun r _ => -rampUp r) s t ω)
        | bmF s] :=
  (disjModel b M0 hs hst.le).incr_1_32_ito_uncorrelated isPreBrownianReal_bmPath
    measurable_bmPath (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) hs hst
    (ae_of_all _ fun _ u _ => rampDown_mul_rampUp u)

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the book's (1.33) in economy 2.** For `0 ≤ s`
and times `T_k ≥ s`: the book's limit form `E_s[F_{T_k}] → n_sB_s` a.s. holds iff the
transversality condition `E_s[n_{T_k}B_{T_k}] → 0` a.s. (no bracket correction, `φψ = 0`).
An instance of `TidyR7MonetarismItoValuation.valuation_1_33_ito_uncorrelated`. -/
theorem disj_1_33 (b M0 : ℝ) {s : ℝ} (hs : 0 ≤ s) {T : ℕ → ℝ} (hT : ∀ k, s ≤ T k) :
    (∀ᵐ ω ∂gaussSeq, Tendsto (fun k => gaussSeq[flowItoBook gaussSeq bmF bmPath disjΛ
      (constP 1) (disjM M0) (constP 0) (constP 0) (constP 0) (fun r _ => -rampUp r) s (T k)
        | bmF s] ω) atTop (𝓝 (disc disjΛ (constP 1) s ω * disjB b s ω))) ↔
      ∀ᵐ ω ∂gaussSeq, Tendsto (fun k => gaussSeq[fun ω => disc disjΛ (constP 1) (T k) ω
        * disjB b (T k) ω | bmF s] ω) atTop (𝓝 0) :=
  valuation_1_33_ito_uncorrelated (σX := fun r _ => rampDown r) (σB := fun r _ => rampUp r)
    (fun _ hT' => disjModel b M0 hs hT'.le) isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) hs hT
    (ae_of_all _ fun _ u _ => rampDown_mul_rampUp u)

end Cochrane.Monetarism.TidyR7MonetarismItoCex
