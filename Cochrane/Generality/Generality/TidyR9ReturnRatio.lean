/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.TidyR9ItoFormulaVariants

/-!
# The ex-post return as discount factor with diffusions: `d(V/W) = −(s/W) dt` and (1.28)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1.5, pp. 565–566,
eqs. (1.27)–(1.28), and Chapter 3, §3.6, (3.36)–(3.39), pp. 74–75. The deterministic version is
`ContinuousLong.A15_integrated` / `ContinuousLong.A15_valuation_iff`.

The book writes (1.27), `dV/V = −(s/V) dt + dW/W`, notes `dV²/V² = dW dV/(WV) = dW²/W²`, and
computes `d(V/W) = (V/W)(dV/V − dW/W − dW dV/(WV) + dW²/W²) = (V/W)(dV/V − dW/W) = −(s/W) dt`.
Here `V` (drift `a_V`, diffusion `σ_V`) and the cumulative return `W` of the book (called `R`
below, drift `a_R`, diffusion `σ_R`, since `W` is the Brownian motion) are Itô processes on
`[s, t]` with a.s. continuous paths, and `R ≥ c > 0` on `[s, t]` for every state (so `1/R` is
an Itô process, `TidyR9ItoFormulaVariants.itoProcess_inv`; a return hitting `0` would need
stopping times, which are not available).

## Main results

* `itoInt_add_ms`: linearity of the Itô integral for mean-square integrands.
* `quotient_rule` (**the book's first line, verbatim with its bracket terms**): a.s.
  `V_t/R_t − V_s/R_s = ∫_s^t (a_V/R − V a_R/R² + V σ_R²/R³ − σ_Vσ_R/R²) du
  + ∫_s^t (σ_V/R − V σ_R/R²) dW`, i.e. `d(V/R) = (V/R)(dV/V − dR/R − dR dV/(RV) + dR²/R²)`:
  Itô's product rule for `V·(1/R)`, which contains the covariation `dV·d(1/R) = −dV dR/R²`.
* `brackets_cancel_127`: under the diffusion part of (1.27), `R σ_V = V σ_R`, the two bracket
  terms cancel, `V σ_R²/R³ − σ_Vσ_R/R² = 0` (the book's second line).
* `ratio_127` (**`d(V/W) = −(s/W) dt` pathwise**): under (1.27) on the coefficients
  (`R a_V = V a_R − R s`, `R σ_V = V σ_R`), a.s. `V_t/R_t − V_s/R_s = −∫_s^t s_u/R_u du`: the
  diffusion of `V/R` vanishes and no bracket term is left over.
* `ratio_crossFree_iff`: the reading `d(V/R) = dV/R + V d(1/R)` that drops the covariation
  `dV·d(1/R)` holds a.s. iff `∫_s^t σ_Vσ_R/R² du = 0` a.s. So (1.28) needs no bracket term in
  its final form, but the derivation does: the book keeps both bracket terms and is right.
* `valuation_128_seq`, `valuation_128_iff` (**(1.28) with diffusions**): along `T_k → ∞`,
  a.s. `∫_t^{T_k} s/R → V_t/R_t` iff `V_{T_k}/R_{T_k} → 0`, and, when `s/R` is integrable on
  `(t, ∞)` pathwise, `V_t/R_t = ∫_t^∞ s_τ/R_τ dτ` iff the transversality condition
  `V_{T_k}/R_{T_k} → 0`; pathwise, for almost every state. The book's "so the limit is zero" is
  E23 (`ContinuousLong.A15_counterexample`); a diffusive counterexample is in
  `TidyR9PositiveDiscount`.
-/

namespace Cochrane.Generality.TidyR9ReturnRatio

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Generality.TidyR7StieltjesSums Cochrane.Generality.TidyR7BrownianTools
  Cochrane.Generality.TidyR7BrownianQV Cochrane.Generality.TidyR7ItoL2
  Cochrane.Generality.TidyR7ItoSums Cochrane.Generality.TidyR7ItoIntegral
  Cochrane.Generality.TidyR7ItoUnbounded Cochrane.Generality.TidyR7ItoProducts
  Cochrane.Generality.TidyR7ItoProcess Cochrane.Generality.TidyR7ItoProductRule
  Cochrane.Generality.TidyR7ItoBondStep Cochrane.Generality.TidyR9ItoFormula
  Cochrane.Generality.TidyR9ItoFormulaVariants
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → ℝ} {s t : ℝ}

/-- Cochrane (2023), A1.5, p. 566 (the `dW`-terms of `d(V/W)`): **linearity of the Itô integral
for mean-square integrands**, `∫(G + K) dW = ∫G dW + ∫K dW` a.s.
Generalises `TidyR7ItoIntegral.itoInt_add` (bounded integrands). -/
theorem itoInt_add_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {G K : ℝ → Ω → ℝ} (hG : MSIntegrand P 𝓕 G s t)
    (hK : MSIntegrand P 𝓕 K s t) :
    itoInt P 𝓕 W (fun u ω => G u ω + K u ω) s t
      =ᵐ[P] fun ω => itoInt P 𝓕 W G s t ω + itoInt P 𝓕 W K s t ω := by
  rcases lt_or_ge s t with hst | hts
  · have h1 := L2Tendsto_dyadic_ms hB hW h𝓕 hs hst (MSIntegrand.add hG hK)
    have h2 := ((L2Tendsto_dyadic_ms hB hW h𝓕 hs hst hG).add
      (L2Tendsto_dyadic_ms hB hW h𝓕 hs hst hK)).congr_seq
        (fun k => ae_of_all _ fun ω => (congrFun (itoSum_add G K (dyadic hst k)) ω).symm)
    exact ae_eq_of_L2Tendsto h1 h2
  · rw [itoInt_of_le hts, itoInt_of_le hts, itoInt_of_le hts]
    exact ae_of_all _ fun ω => by simp

variable {V aV σV R aR σR : ℝ → Ω → ℝ} {CV CVσ CR CRσ : ℝ}

/-- **Cochrane (2023), A1.5, p. 565: the book's quotient rule
`d(V/W) = (V/W)(dV/V − dW/W − dW dV/(WV) + dW²/W²)`, verbatim with its bracket terms.** For
Itô processes `V` and `R` (the book's `W`) with a.s. continuous paths on `[s, t]`,
`0 ≤ s < t`, and `R ≥ c > 0` on `[s, t]`: a.s.
`V_t/R_t − V_s/R_s = ∫_s^t (a_V/R − V a_R/R² + V σ_R²/R³ − σ_Vσ_R/R²) du
+ ∫_s^t (σ_V/R − V σ_R/R²) dW`.
Itô's product rule (`TidyR7ItoProductRule.product_rule_pathwise`) for `V·(1/R)`, with `1/R` from
`TidyR9ItoFormulaVariants.itoProcess_inv`. -/
theorem quotient_rule (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hV : ItoProcess P 𝓕 W V aV σV s t CV CVσ) (hR : ItoProcess P 𝓕 W R aR σR s t CR CRσ)
    (hVc : ∀ᵐ ω ∂P, ContinuousOn (fun u => V u ω) (Set.Icc s t))
    (hRc : ∀ᵐ ω ∂P, ContinuousOn (fun u => R u ω) (Set.Icc s t)) {c : ℝ} (hc : 0 < c)
    (hRlow : ∀ u ∈ Set.Icc s t, ∀ ω, c ≤ R u ω) :
    (fun ω => V t ω / R t ω - V s ω / R s ω) =ᵐ[P] fun ω =>
      (∫ u in s..t, (aV u ω / R u ω - V u ω * aR u ω / R u ω ^ 2
        + V u ω * σR u ω ^ 2 / R u ω ^ 3 - σV u ω * σR u ω / R u ω ^ 2))
      + itoInt P 𝓕 W (fun u ω => σV u ω / R u ω - V u ω * σR u ω / R u ω ^ 2) s t ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hpos : ∀ u ∈ Set.Icc s t, ∀ ω, 0 < R u ω := fun u hu ω => hc.trans_le (hRlow u hu ω)
  have hY := itoProcess_inv hB hW h𝓕 hs hst.le hR hRc hc hRlow
  have hYc : ∀ᵐ ω ∂P, ContinuousOn (fun u => (R u ω)⁻¹) (Set.Icc s t) := by
    filter_upwards [hRc] with ω hω
    exact hω.inv₀ fun u hu => (hpos u hu ω).ne'
  have hpr := product_rule_pathwise hB hW h𝓕 hs hst hV hY hVc hYc
  have G1 := MSIntegrand.mul_itoIntegrand (hV.toMS hB hW h𝓕 hs) hY.diff
  have G2 := MSIntegrand.mul_itoIntegrand (hY.toMS hB hW h𝓕 hs) hV.diff
  have hadd := itoInt_add_ms hB hW h𝓕 hs G1 G2
  have hcongr : itoInt P 𝓕 W (fun u ω => V u ω * -(σR u ω / R u ω ^ 2)
      + (R u ω)⁻¹ * σV u ω) s t
      = itoInt P 𝓕 W (fun u ω => σV u ω / R u ω - V u ω * σR u ω / R u ω ^ 2) s t :=
    itoInt_congr_Icc fun u _ ω => by ring
  filter_upwards [hpr, hadd, hVc, hRc, hYc, hV.drift.cont, hV.diff.cont, hR.drift.cont,
    hR.diff.cont] with ω h1 h2 c1 c2 c3 c4 c5 c6 c7
  rw [hcongr] at h2
  have hne : ∀ u ∈ Set.Icc s t, R u ω ≠ 0 := fun u hu => (hpos u hu ω).ne'
  have cb : ContinuousOn (fun u => -(aR u ω / R u ω ^ 2) + σR u ω ^ 2 / R u ω ^ 3)
      (Set.Icc s t) :=
    (c6.div (c2.pow 2) fun u hu => pow_ne_zero _ (hne u hu)).neg.add
      ((c7.pow 2).div (c2.pow 3) fun u hu => pow_ne_zero _ (hne u hu))
  have ck : ContinuousOn (fun u => -(σR u ω / R u ω ^ 2)) (Set.Icc s t) :=
    (c7.div (c2.pow 2) fun u hu => pow_ne_zero _ (hne u hu)).neg
  have i1 : IntervalIntegrable (fun u => V u ω * (-(aR u ω / R u ω ^ 2)
      + σR u ω ^ 2 / R u ω ^ 3)) volume s t := (c1.mul cb).intervalIntegrable_of_Icc hst.le
  have i2 : IntervalIntegrable (fun u => (R u ω)⁻¹ * aV u ω) volume s t :=
    (c3.mul c4).intervalIntegrable_of_Icc hst.le
  have i3 : IntervalIntegrable (fun u => σV u ω * -(σR u ω / R u ω ^ 2)) volume s t :=
    (c5.mul ck).intervalIntegrable_of_Icc hst.le
  have hsum : (∫ u in s..t, V u ω * (-(aR u ω / R u ω ^ 2) + σR u ω ^ 2 / R u ω ^ 3))
      + (∫ u in s..t, (R u ω)⁻¹ * aV u ω) + (∫ u in s..t, σV u ω * -(σR u ω / R u ω ^ 2))
      = ∫ u in s..t, (aV u ω / R u ω - V u ω * aR u ω / R u ω ^ 2
        + V u ω * σR u ω ^ 2 / R u ω ^ 3 - σV u ω * σR u ω / R u ω ^ 2) := by
    rw [← intervalIntegral.integral_add i1 i2, ← intervalIntegral.integral_add (i1.add i2) i3]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hst.le] at hu
    have := hne u hu
    field_simp
    ring
  have e1 : V t ω / R t ω - V s ω / R s ω = V t ω * (R t ω)⁻¹ - V s ω * (R s ω)⁻¹ := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
  rw [e1, h1, h2, ← hsum]
  ring

/-- **Cochrane (2023), A1.5, p. 565 (`dV²/V² = dW dV/(WV) = dW²/W²`): the bracket terms
cancel.** If `R σ_V = V σ_R` (the diffusion part of (1.27)) and `R ≠ 0`, then
`V σ_R²/R³ − σ_Vσ_R/R² = 0`, i.e. `(V/R)(dR²/R² − dR dV/(RV)) = 0`. -/
theorem brackets_cancel_127 {V' R' σV' σR' : ℝ} (hR : R' ≠ 0) (hσ : R' * σV' = V' * σR') :
    V' * σR' ^ 2 / R' ^ 3 - σV' * σR' / R' ^ 2 = 0 := by
  have e : V' * σR' ^ 2 / R' ^ 3 - σV' * σR' / R' ^ 2 = σR' * (V' * σR' - R' * σV') / R' ^ 3 := by
    field_simp
  rw [e, hσ, sub_self, mul_zero, zero_div]

variable {sp : ℝ → Ω → ℝ}

/-- **Cochrane (2023), A1.5, pp. 565–566, (1.27): `d(V/W) = −(s/W) dt` with diffusions,
pathwise.** Under the hypotheses of `quotient_rule` and the flow (1.27) on the coefficients on
`[s, t]` (`R a_V = V a_R − R s`, `R σ_V = V σ_R`, `ContinuousLong`'s `dV/V = −(s/V)dt + dR/R`
multiplied by `RV`), a.s. `V_t/R_t − V_s/R_s = −∫_s^t s_u/R_u du`. The `dW`-part of `V/R`
vanishes identically and the bracket terms cancel (`brackets_cancel_127`): no correction term
is needed.
Generalises `ContinuousLong.A15_integrated`. -/
theorem ratio_127 (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hV : ItoProcess P 𝓕 W V aV σV s t CV CVσ) (hR : ItoProcess P 𝓕 W R aR σR s t CR CRσ)
    (hVc : ∀ᵐ ω ∂P, ContinuousOn (fun u => V u ω) (Set.Icc s t))
    (hRc : ∀ᵐ ω ∂P, ContinuousOn (fun u => R u ω) (Set.Icc s t)) {c : ℝ} (hc : 0 < c)
    (hRlow : ∀ u ∈ Set.Icc s t, ∀ ω, c ≤ R u ω)
    (hfa : ∀ u ∈ Set.Icc s t, ∀ ω, R u ω * aV u ω = V u ω * aR u ω - R u ω * sp u ω)
    (hfσ : ∀ u ∈ Set.Icc s t, ∀ ω, R u ω * σV u ω = V u ω * σR u ω) :
    (fun ω => V t ω / R t ω - V s ω / R s ω) =ᵐ[P] fun ω => -∫ u in s..t, sp u ω / R u ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hne : ∀ u ∈ Set.Icc s t, ∀ ω, R u ω ≠ 0 := fun u hu ω =>
    (hc.trans_le (hRlow u hu ω)).ne'
  have hq := quotient_rule hB hW h𝓕 hs hst hV hR hVc hRc hc hRlow
  have hz : itoInt P 𝓕 W (fun u ω => σV u ω / R u ω - V u ω * σR u ω / R u ω ^ 2) s t
      = itoInt P 𝓕 W (fun u ω => 0 * σV u ω) s t := by
    refine itoInt_congr_Icc fun u hu ω => ?_
    have h0 := hne u hu ω
    have e : σV u ω / R u ω - V u ω * σR u ω / R u ω ^ 2
        = (R u ω * σV u ω - V u ω * σR u ω) / R u ω ^ 2 := by
      field_simp
    rw [e, hfσ u hu ω, sub_self, zero_div, zero_mul]
  have h0 := itoInt_const_mul hB hW h𝓕 hs hV.diff 0
  filter_upwards [hq, h0] with ω e1 e2
  rw [e1, hz, e2, zero_mul, add_zero, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [Set.uIcc_of_le hst.le] at hu
  have h0 := hne u hu ω
  have e : aV u ω / R u ω - V u ω * aR u ω / R u ω ^ 2 + V u ω * σR u ω ^ 2 / R u ω ^ 3
      - σV u ω * σR u ω / R u ω ^ 2 = -(sp u ω / R u ω)
        + (R u ω * (R u ω * aV u ω - (V u ω * aR u ω - R u ω * sp u ω))
          - σR u ω * (R u ω * σV u ω - V u ω * σR u ω)) / R u ω ^ 3 := by
    field_simp
    ring
  rw [e, hfa u hu ω, hfσ u hu ω]
  ring

/-- **Cochrane (2023), A1.5, p. 565: dropping the covariation `dV·d(1/W)` is wrong exactly
when the bracket is not zero.** Under the hypotheses of `quotient_rule`, the reading
`d(V/R) = dV/R + V d(1/R)` (Itô's formula for `1/R` but no cross term), a.s.
`V_t/R_t − V_s/R_s = ∫(a_V/R − V a_R/R² + V σ_R²/R³) du + ∫(σ_V/R − V σ_R/R²) dW`, holds iff
a.s. `∫_s^t σ_Vσ_R/R² du = 0`. -/
theorem ratio_crossFree_iff (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hV : ItoProcess P 𝓕 W V aV σV s t CV CVσ) (hR : ItoProcess P 𝓕 W R aR σR s t CR CRσ)
    (hVc : ∀ᵐ ω ∂P, ContinuousOn (fun u => V u ω) (Set.Icc s t))
    (hRc : ∀ᵐ ω ∂P, ContinuousOn (fun u => R u ω) (Set.Icc s t)) {c : ℝ} (hc : 0 < c)
    (hRlow : ∀ u ∈ Set.Icc s t, ∀ ω, c ≤ R u ω) :
    ((fun ω => V t ω / R t ω - V s ω / R s ω) =ᵐ[P] fun ω =>
      (∫ u in s..t, (aV u ω / R u ω - V u ω * aR u ω / R u ω ^ 2
        + V u ω * σR u ω ^ 2 / R u ω ^ 3))
      + itoInt P 𝓕 W (fun u ω => σV u ω / R u ω - V u ω * σR u ω / R u ω ^ 2) s t ω) ↔
      ∀ᵐ ω ∂P, ∫ u in s..t, σV u ω * σR u ω / R u ω ^ 2 = 0 := by
  have hq := quotient_rule hB hW h𝓕 hs hst hV hR hVc hRc hc hRlow
  have hne : ∀ u ∈ Set.Icc s t, ∀ ω, R u ω ≠ 0 := fun u hu ω =>
    (hc.trans_le (hRlow u hu ω)).ne'
  have hsplit : ∀ᵐ ω ∂P, (∫ u in s..t, (aV u ω / R u ω - V u ω * aR u ω / R u ω ^ 2
      + V u ω * σR u ω ^ 2 / R u ω ^ 3 - σV u ω * σR u ω / R u ω ^ 2))
      = (∫ u in s..t, (aV u ω / R u ω - V u ω * aR u ω / R u ω ^ 2
        + V u ω * σR u ω ^ 2 / R u ω ^ 3)) - ∫ u in s..t, σV u ω * σR u ω / R u ω ^ 2 := by
    filter_upwards [hVc, hRc, hV.drift.cont, hV.diff.cont, hR.drift.cont, hR.diff.cont]
      with ω c1 c2 c4 c5 c6 c7
    have hd : ∀ n : ℕ, ∀ u ∈ Set.Icc s t, R u ω ^ n ≠ 0 := fun n u hu =>
      pow_ne_zero _ (hne u hu ω)
    have cA : ContinuousOn (fun u => aV u ω / R u ω - V u ω * aR u ω / R u ω ^ 2
        + V u ω * σR u ω ^ 2 / R u ω ^ 3) (Set.Icc s t) :=
      ((c4.div c2 fun u hu => hne u hu ω).sub ((c1.mul c6).div (c2.pow 2) (hd 2))).add
        ((c1.mul (c7.pow 2)).div (c2.pow 3) (hd 3))
    have cC : ContinuousOn (fun u => σV u ω * σR u ω / R u ω ^ 2) (Set.Icc s t) :=
      (c5.mul c7).div (c2.pow 2) (hd 2)
    rw [← intervalIntegral.integral_sub (cA.intervalIntegrable_of_Icc (μ := volume) hst.le)
      (cC.intervalIntegrable_of_Icc (μ := volume) hst.le)]
  constructor
  · intro h
    filter_upwards [h, hq, hsplit] with ω e1 e2 e3
    rw [e1, e3] at e2
    linarith
  · intro h
    filter_upwards [h, hq, hsplit] with ω e1 e2 e3
    rw [e2, e3, e1, sub_zero]

variable {CVf CVσf CRf CRσf cf : ℝ → ℝ}

/-- **Cochrane (2023), A1.5, (1.28), p. 566, limit form with diffusions:** if the hypotheses of
`ratio_127` hold on every `[t, T]`, `T > t ≥ 0` (bounds and the lower bound `c(T) > 0` of `R`
may depend on `T`), then along any `T_k > t`, for almost every state,
`∫_t^{T_k} s_u/R_u du → V_t/R_t` iff `V_{T_k}/R_{T_k} → 0` (the transversality condition).
Generalises `ContinuousLong.A15_valuation_iff`. -/
theorem valuation_128_seq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (ht : 0 ≤ t)
    (hV : ∀ T, t < T → ItoProcess P 𝓕 W V aV σV t T (CVf T) (CVσf T))
    (hR : ∀ T, t < T → ItoProcess P 𝓕 W R aR σR t T (CRf T) (CRσf T))
    (hVc : ∀ T, ∀ᵐ ω ∂P, ContinuousOn (fun u => V u ω) (Set.Icc t T))
    (hRc : ∀ T, ∀ᵐ ω ∂P, ContinuousOn (fun u => R u ω) (Set.Icc t T))
    (hc : ∀ T, 0 < cf T) (hRlow : ∀ T, ∀ u ∈ Set.Icc t T, ∀ ω, cf T ≤ R u ω)
    (hfa : ∀ u, t ≤ u → ∀ ω, R u ω * aV u ω = V u ω * aR u ω - R u ω * sp u ω)
    (hfσ : ∀ u, t ≤ u → ∀ ω, R u ω * σV u ω = V u ω * σR u ω) {T : ℕ → ℝ}
    (hT : ∀ k, t < T k) :
    ∀ᵐ ω ∂P, (Tendsto (fun k => ∫ u in t..T k, sp u ω / R u ω) atTop (𝓝 (V t ω / R t ω)) ↔
      Tendsto (fun k => V (T k) ω / R (T k) ω) atTop (𝓝 0)) := by
  have hall : ∀ᵐ ω ∂P, ∀ k, V (T k) ω / R (T k) ω - V t ω / R t ω
      = -∫ u in t..T k, sp u ω / R u ω := ae_all_iff.2 fun k =>
    ratio_127 hB hW h𝓕 ht (hT k) (hV _ (hT k)) (hR _ (hT k)) (hVc _) (hRc _) (hc (T k))
      (hRlow (T k)) (fun u hu ω => hfa u hu.1 ω) (fun u hu ω => hfσ u hu.1 ω)
  filter_upwards [hall] with ω h
  have e : ∀ k, ∫ u in t..T k, sp u ω / R u ω = V t ω / R t ω - V (T k) ω / R (T k) ω :=
    fun k => by linarith [h k]
  simp_rw [e]
  constructor
  · intro h1
    have := (tendsto_const_nhds (x := V t ω / R t ω)).sub h1
    simpa using this
  · intro h1
    have := (tendsto_const_nhds (x := V t ω / R t ω)).sub h1
    simpa using this

/-- **Cochrane (2023), A1.5, eq. (1.28), p. 566, with diffusions:
`V_t/W_t = ∫_t^∞ s_τ/W_τ dτ` iff the transversality condition.** Under the hypotheses of
`valuation_128_seq`, with `T_k → ∞` and `s/R` pathwise integrable on `(t, ∞)` for almost every
state: for almost every state, `V_t/R_t = ∫_t^∞ s_u/R_u du` iff `V_{T_k}/R_{T_k} → 0`. The
limit is a hypothesis, not a consequence of (1.27) (E23).
Generalises `ContinuousLong.A15_valuation_iff`. -/
theorem valuation_128_iff (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (ht : 0 ≤ t)
    (hV : ∀ T, t < T → ItoProcess P 𝓕 W V aV σV t T (CVf T) (CVσf T))
    (hR : ∀ T, t < T → ItoProcess P 𝓕 W R aR σR t T (CRf T) (CRσf T))
    (hVc : ∀ T, ∀ᵐ ω ∂P, ContinuousOn (fun u => V u ω) (Set.Icc t T))
    (hRc : ∀ T, ∀ᵐ ω ∂P, ContinuousOn (fun u => R u ω) (Set.Icc t T))
    (hc : ∀ T, 0 < cf T) (hRlow : ∀ T, ∀ u ∈ Set.Icc t T, ∀ ω, cf T ≤ R u ω)
    (hfa : ∀ u, t ≤ u → ∀ ω, R u ω * aV u ω = V u ω * aR u ω - R u ω * sp u ω)
    (hfσ : ∀ u, t ≤ u → ∀ ω, R u ω * σV u ω = V u ω * σR u ω) {T : ℕ → ℝ}
    (hT : ∀ k, t < T k) (hTlim : Tendsto T atTop atTop)
    (hI : ∀ᵐ ω ∂P, IntegrableOn (fun u => sp u ω / R u ω) (Set.Ioi t)) :
    ∀ᵐ ω ∂P, (V t ω / R t ω = ∫ u in Set.Ioi t, sp u ω / R u ω ↔
      Tendsto (fun k => V (T k) ω / R (T k) ω) atTop (𝓝 0)) := by
  filter_upwards [valuation_128_seq hB hW h𝓕 ht hV hR hVc hRc hc hRlow hfa hfσ hT, hI]
    with ω h hi
  have hlim := intervalIntegral_tendsto_integral_Ioi t hi hTlim
  rw [← h]
  constructor
  · intro he
    rw [he]
    exact hlim
  · intro h1
    exact tendsto_nhds_unique h1 hlim

end Cochrane.Generality.TidyR9ReturnRatio
