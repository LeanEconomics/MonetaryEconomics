/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR12SDETools

/-!
# The Itô integral on the `L²(dt × dP)`-closure of jointly measurable MS integrands

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34) (Track 3, chunk B6, item 1). The toolkit's
`TidyR7ItoIntegral.itoInt` is only shown to exist for mean-square continuous integrands
(`TidyR7ItoUnbounded.MSIntegrand`). A martingale-representation integrand need not be mean-square
continuous, so the integral is extended here to the closure of those integrands.

Write `μ_{s,t} = (Lebesgue on (s, t]) ⊗ P` (`mrepMeasure`) on `ℝ × Ω`. The class
`MRepIntegrand P 𝓕 H s t` (**exactly the `L²(μ_{s,t})`-closure of the jointly measurable
mean-square continuous integrands**) holds when there are mean-square continuous `G n` on
`[s, t]`, each jointly measurable in `(u, ω)`, with `G n → H` in `L²(μ_{s,t})`
(`MRepApprox`). The integral `mrepInt` is the `𝓕_t`-measurable `L²(P)` limit of
`∫_s^t G n dW`.

## Main results

* `mrep_memLp_uncurry`, `mrep_isometry_ms`: a jointly measurable mean-square continuous `G` lies
  in `L²(μ_{s,t})` and `E[(∫_s^t G dW)²] = ∫ G² dμ_{s,t}` (Fubini form of the isometry).
* `mrep_spec`: along ANY approximating sequence, `∫ G n dW → mrepInt H` in `L²(P)`; the limit is
  `𝓕_t`-strongly measurable.
* `mrep_agree`: on jointly measurable mean-square continuous integrands `mrepInt = itoInt` a.s.
* `mrep_isometry`: `E[(mrepInt H)²] = ∫ H² dμ_{s,t}`.
* Linearity: `mrep_add`, `mrep_const_mul`, `mrep_sub` (class) and `mrepInt_add`,
  `mrepInt_const_mul`, `mrepInt_sub` (a.s.); `mrepInt_isometry_sub`.
* `mrepInt_integral_mul_eq_zero` (`E[Z ∫_s^t H dW] = 0` for square-integrable `𝓕_s`-measurable
  `Z`), `mrepInt_integral_eq_zero`.
* `mrep_mono`, `mrepInt_add_mrepInt` (`∫_s^t = ∫_s^r + ∫_r^t`), `mrepInt_condExp`
  (`E[∫_s^t H dW | 𝓕_r] = ∫_s^r H dW`).
* `mrep_of_L2Tendsto` (the class is closed in `L²(μ_{s,t})`), `mrepInt_L2Tendsto` (the integral is
  continuous).

What is NOT shown: that every progressively measurable `H` with `E∫H² < ∞` lies in the class (the
density of mean-square continuous integrands among progressive ones). The representation theorem
(`TidyR13MRepTheorem`) only needs the class as defined.
-/

namespace Cochrane.ZeroBound.TidyR13MRepIntegral

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.TidyR7StieltjesSums Cochrane.ZeroBound.TidyR7BrownianTools
  Cochrane.ZeroBound.TidyR7BrownianQV Cochrane.ZeroBound.TidyR7ItoL2
  Cochrane.ZeroBound.TidyR7ItoIntegral Cochrane.ZeroBound.TidyR7ItoUnbounded
  Cochrane.ZeroBound.TidyR7ItoBondStep Cochrane.ZeroBound.TidyR9ItoFormula
  Cochrane.ZeroBound.TidyR10DoobFubini Cochrane.ZeroBound.TidyR12SDETools
  Cochrane.ZeroBound.TidyR8MonetarismItoDom
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ} {s t : ℝ}

/-! ## The measure `dt × dP` and the class -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (integrands of (1.32) with diffusive bonds): the
measure `μ_{s,t} = (Lebesgue on (s, t]) ⊗ P` on `ℝ × Ω`, the `dt × dP` of the Itô isometry.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrepMeasure). -/
noncomputable def mrepMeasure (P : Measure Ω) (s t : ℝ) : Measure (ℝ × Ω) :=
  (volume.restrict (Set.Ioc s t)).prod P

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `G` is an **approximating sequence** for `H` on
`[s, t]`: every `G n` is a mean-square continuous integrand, jointly measurable in `(u, ω)`, and
`G n → H` in `L²(μ_{s,t})`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.MRepApprox). -/
def MRepApprox (P : Measure Ω) (𝓕 : Filtration ℝ mΩ) (H : ℝ → Ω → ℝ) (s t : ℝ)
    (G : ℕ → ℝ → Ω → ℝ) : Prop :=
  (∀ n, MSIntegrand P 𝓕 (G n) s t) ∧ (∀ n, Measurable (Function.uncurry (G n))) ∧
    L2Tendsto (mrepMeasure P s t) (fun n => Function.uncurry (G n)) (Function.uncurry H)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the extended integrand class** on `[s, t]`: the
`L²(dt × dP)`-closure of the jointly measurable mean-square continuous integrands (some
approximating sequence exists).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.MRepIntegrand). -/
def MRepIntegrand (P : Measure Ω) (𝓕 : Filtration ℝ mΩ) (H : ℝ → Ω → ℝ) (s t : ℝ) : Prop :=
  ∃ G, MRepApprox P 𝓕 H s t G

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the extended Itô integral `∫_s^t H dW`.** A chosen
`𝓕_t`-strongly measurable `L²(P)` limit of `∫_s^t G n dW` along an approximating sequence, if one
exists, else `0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrepInt). -/
noncomputable def mrepInt (P : Measure Ω) (𝓕 : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ℝ)
    (H : ℝ → Ω → ℝ) (s t : ℝ) : Ω → ℝ := by
  classical
  exact if h : ∃ Y, StronglyMeasurable[𝓕 t] Y ∧ ∃ G, MRepApprox P 𝓕 H s t G ∧
      L2Tendsto P (fun n => itoInt P 𝓕 W (G n) s t) Y then h.choose else 0

/-! ## Jointly measurable mean-square continuous integrands -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: a jointly measurable mean-square continuous integrand
is in `L²(μ_{s,t})` (`u ↦ E[G_u²]` is continuous on `[s, t]`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrep_memLp_uncurry). -/
theorem mrep_memLp_uncurry [IsFiniteMeasure P] {G : ℝ → Ω → ℝ} (hG : MSIntegrand P 𝓕 G s t)
    (hGm : Measurable (Function.uncurry G)) :
    MemLp (Function.uncurry G) 2 (mrepMeasure P s t) := by
  have ham : AEStronglyMeasurable (Function.uncurry G) (mrepMeasure P s t) :=
    hGm.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq ham]
  have hsq : AEStronglyMeasurable (fun x : ℝ × Ω => Function.uncurry G x ^ 2)
      (mrepMeasure P s t) := (hGm.pow_const 2).aestronglyMeasurable
  unfold mrepMeasure at hsq ⊢
  rw [integrable_prod_iff hsq]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (hG.memLp u (Set.Ioc_subset_Icc_self hu)).integrable_sq
  · have hc : ContinuousOn (fun u => ∫ ω, G u ω ^ 2 ∂P) (Set.Icc s t) :=
      continuousOn_integral_sq_ms hG
    have hi : IntegrableOn (fun u => ∫ ω, G u ω ^ 2 ∂P) (Set.Ioc s t) :=
      (hc.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    refine hi.congr_fun (fun u _ => ?_) measurableSet_Ioc
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp [Function.uncurry]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: for `s ≤ t`, `∫ G² dμ_{s,t} = ∫_s^t E[G_u²] du`
(Fubini).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrep_integral_sq). -/
theorem mrep_integral_sq [IsFiniteMeasure P] {G : ℝ → Ω → ℝ} (hG : MSIntegrand P 𝓕 G s t)
    (hGm : Measurable (Function.uncurry G)) (hst : s ≤ t) :
    ∫ x, Function.uncurry G x ^ 2 ∂mrepMeasure P s t = ∫ u in s..t, ∫ ω, G u ω ^ 2 ∂P := by
  have hi := (mrep_memLp_uncurry hG hGm).integrable_sq
  unfold mrepMeasure at hi ⊢
  rw [integral_prod _ hi, intervalIntegral.integral_of_le hst]
  rfl

/-- Cochrane (2023), A1 §1.6, pp. 567–568: for `t ≤ s` the measure `μ_{s,t}` is zero.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrepMeasure_of_le). -/
theorem mrepMeasure_of_le (hts : t ≤ s) : mrepMeasure P s t = 0 := by
  rw [mrepMeasure, Set.Ioc_eq_empty (not_lt.2 hts), Measure.restrict_empty, Measure.zero_prod]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the Itô isometry in `dt × dP` form** for a jointly
measurable mean-square continuous integrand, `0 ≤ s`:
`E[(∫_s^t G dW)²] = ∫ G² dμ_{s,t}`.
The `dt × dP` form of `TidyR10DoobFubini.integral_itoInt_sq_ms`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrep_isometry_ms). -/
theorem mrep_isometry_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {G : ℝ → Ω → ℝ} (hG : MSIntegrand P 𝓕 G s t)
    (hGm : Measurable (Function.uncurry G)) :
    ∫ ω, itoInt P 𝓕 W G s t ω ^ 2 ∂P = ∫ x, Function.uncurry G x ^ 2 ∂mrepMeasure P s t := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rcases le_total s t with hst | hts
  · rw [integral_itoInt_sq_ms hB hW h𝓕 hs hst hG, mrep_integral_sq hG hGm hst]
  · rw [itoInt_of_le hts, mrepMeasure_of_le hts]
    simp

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the difference of two mean-square continuous
integrands is one.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrep_ms_sub). -/
theorem mrep_ms_sub {G K : ℝ → Ω → ℝ} (hG : MSIntegrand P 𝓕 G s t)
    (hK : MSIntegrand P 𝓕 K s t) : MSIntegrand P 𝓕 (fun u ω => G u ω - K u ω) s t := by
  have e : (fun u ω => G u ω - K u ω) = fun u ω => G u ω + -1 * K u ω :=
    funext fun u => funext fun ω => by ring
  rw [e]
  exact Cochrane.ZeroBound.TidyR7ItoBondStep.MSIntegrand.add hG
    (Cochrane.ZeroBound.TidyR7ItoBondStep.MSIntegrand.const_mul hK (-1))

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the isometry for differences**,
`E[(∫G dW − ∫K dW)²] = ∫(G − K)² dμ_{s,t}`, jointly measurable mean-square continuous `G, K`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrep_isometry_sub). -/
theorem mrep_isometry_sub (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {G K : ℝ → Ω → ℝ} (hG : MSIntegrand P 𝓕 G s t)
    (hGm : Measurable (Function.uncurry G)) (hK : MSIntegrand P 𝓕 K s t)
    (hKm : Measurable (Function.uncurry K)) :
    ∫ ω, (itoInt P 𝓕 W G s t ω - itoInt P 𝓕 W K s t ω) ^ 2 ∂P
      = ∫ x, (Function.uncurry G x - Function.uncurry K x) ^ 2 ∂mrepMeasure P s t := by
  have hm : Measurable (Function.uncurry fun u ω => G u ω - K u ω) := hGm.sub hKm
  have h := mrep_isometry_ms hB hW h𝓕 hs (mrep_ms_sub hG hK) hm
  rw [show (∫ x, (Function.uncurry G x - Function.uncurry K x) ^ 2 ∂mrepMeasure P s t)
    = ∫ x, Function.uncurry (fun u ω => G u ω - K u ω) x ^ 2 ∂mrepMeasure P s t from rfl, ← h]
  refine integral_congr_ae ?_
  filter_upwards [itoInt_sub_ms hB hW h𝓕 hs hG hK] with ω hω
  rw [hω]

/-! ## General `L²` facts -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: an `L²`-convergent sequence is `L²`-Cauchy.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrep_cauchy_of_L2Tendsto). -/
theorem mrep_cauchy_of_L2Tendsto {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    {X : ℕ → α → ℝ} {Y : α → ℝ} (h : L2Tendsto μ X Y) :
    ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ l ≥ N, ∫ x, (X k x - X l x) ^ 2 ∂μ ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 h.2.2) (ε / 4) (by positivity)
  refine ⟨N, fun k hk l hl => ?_⟩
  have hle := integral_sq_sub_le (P := μ) h.2.1 (h.1 k) (h.1 l)
  have e : ∀ j, ∫ x, (Y x - X j x) ^ 2 ∂μ = ∫ x, (X j x - Y x) ^ 2 ∂μ := fun j =>
    integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [e k, e l] at hle
  have a1 := hN k hk
  have a2 := hN l hl
  rw [Real.dist_eq, sub_zero] at a1 a2
  have b1 := (abs_lt.1 a1).2
  have b2 := (abs_lt.1 a2).2
  linarith

/-- Cochrane (2023), A1 §1.6, pp. 567–568: if `X k → Y` in `L²` then `E[X_k²] → E[Y²]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrep_tendsto_integral_sq). -/
theorem mrep_tendsto_integral_sq {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    {X : ℕ → α → ℝ} {Y : α → ℝ} (h : L2Tendsto μ X Y) :
    Tendsto (fun k => ∫ x, X k x ^ 2 ∂μ) atTop (𝓝 (∫ x, Y x ^ 2 ∂μ)) := by
  have e : ∀ k, ∫ x, X k x ^ 2 ∂μ - ∫ x, Y x ^ 2 ∂μ
      = ∫ x, (X k x - Y x) ^ 2 ∂μ + 2 * ∫ x, Y x * (X k x - Y x) ∂μ := by
    intro k
    have i1 := (h.1 k).integrable_sq
    have i2 := h.2.1.integrable_sq
    have i3 : Integrable (fun x => (X k x - Y x) ^ 2) μ := ((h.1 k).sub h.2.1).integrable_sq
    have i4 : Integrable (fun x => Y x * (X k x - Y x)) μ :=
      h.2.1.integrable_mul ((h.1 k).sub h.2.1)
    rw [← integral_sub i1 i2, ← integral_const_mul, ← integral_add i3 (i4.const_mul 2)]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  refine tendsto_sub_nhds_zero_iff.1 ?_
  simp_rw [e]
  have h2 : Tendsto (fun k => ∫ x, Y x * (X k x - Y x) ∂μ) atTop (𝓝 0) :=
    tendsto_zero_of_sq_le (c := ∫ x, Y x ^ 2 ∂μ)
      (fun k => sq_integral_mul_le h.2.1 ((h.1 k).sub h.2.1)) h.2.2
  simpa using h.2.2.add (h2.const_mul 2)

/-! ## The integral exists and does not depend on the approximating sequence -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: along an approximating sequence the integrals
`∫_s^t G n dW` are `L²(P)`-Cauchy (isometry).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrep_itoInt_cauchy). -/
theorem mrep_itoInt_cauchy (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {H : ℝ → Ω → ℝ} {G : ℕ → ℝ → Ω → ℝ}
    (hG : MRepApprox P 𝓕 H s t G) :
    ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ l ≥ N,
      ∫ ω, (itoInt P 𝓕 W (G k) s t ω - itoInt P 𝓕 W (G l) s t ω) ^ 2 ∂P ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := mrep_cauchy_of_L2Tendsto hG.2.2 ε hε
  refine ⟨N, fun k hk l hl => ?_⟩
  rw [mrep_isometry_sub hB hW h𝓕 hs (hG.1 k) (hG.2.1 k) (hG.1 l) (hG.2.1 l)]
  exact hN k hk l hl

/-- Cochrane (2023), A1 §1.6, pp. 567–568: two approximating sequences give integrals with the
same `L²(P)` limits.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrep_L2Tendsto_of_approx). -/
theorem mrep_L2Tendsto_of_approx (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {H : ℝ → Ω → ℝ} {G G' : ℕ → ℝ → Ω → ℝ}
    (hG : MRepApprox P 𝓕 H s t G) (hG' : MRepApprox P 𝓕 H s t G') {Y : Ω → ℝ}
    (hY : L2Tendsto P (fun n => itoInt P 𝓕 W (G' n) s t) Y) :
    L2Tendsto P (fun n => itoInt P 𝓕 W (G n) s t) Y := by
  have hm : ∀ n, MemLp (itoInt P 𝓕 W (G n) s t) 2 P := fun n =>
    memLp_itoInt_ms hB hW h𝓕 hs (hG.1 n)
  refine ⟨hm, hY.2.1, ?_⟩
  have hle : ∀ n, ∫ ω, (itoInt P 𝓕 W (G n) s t ω - Y ω) ^ 2 ∂P ≤
      2 * (2 * ∫ x, (Function.uncurry (G' n) x - Function.uncurry H x) ^ 2 ∂mrepMeasure P s t
        + 2 * ∫ x, (Function.uncurry (G n) x - Function.uncurry H x) ^ 2 ∂mrepMeasure P s t)
      + 2 * ∫ ω, (itoInt P 𝓕 W (G' n) s t ω - Y ω) ^ 2 ∂P := by
    intro n
    have h1 := integral_sq_sub_le (hY.1 n) (hm n) hY.2.1
    have h2 := integral_sq_sub_le (P := mrepMeasure P s t) hG.2.2.2.1 (hG'.2.2.1 n)
      (hG.2.2.1 n)
    have e : ∀ (F : ℕ → ℝ → Ω → ℝ) n, ∫ x, (Function.uncurry H x - Function.uncurry (F n) x) ^ 2
        ∂mrepMeasure P s t = ∫ x, (Function.uncurry (F n) x - Function.uncurry H x) ^ 2
        ∂mrepMeasure P s t := fun F n => integral_congr_ae (ae_of_all _ fun x => by ring)
    rw [e G' n, e G n] at h2
    rw [mrep_isometry_sub hB hW h𝓕 hs (hG'.1 n) (hG'.2.1 n) (hG.1 n) (hG.2.1 n)] at h1
    linarith
  have hlim : Tendsto (fun n =>
      2 * (2 * ∫ x, (Function.uncurry (G' n) x - Function.uncurry H x) ^ 2 ∂mrepMeasure P s t
        + 2 * ∫ x, (Function.uncurry (G n) x - Function.uncurry H x) ^ 2 ∂mrepMeasure P s t)
      + 2 * ∫ ω, (itoInt P 𝓕 W (G' n) s t ω - Y ω) ^ 2 ∂P) atTop (𝓝 0) := by
    have := ((hG'.2.2.2.2.const_mul 2).add (hG.2.2.2.2.const_mul 2)).const_mul 2 |>.add
      (hY.2.2.const_mul 2)
    simpa using this
  exact squeeze_zero (fun n => integral_nonneg fun _ => sq_nonneg _) hle hlim

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the extended integral is well defined.** For any
approximating sequence `G` of `H` on `[s, t]`, `0 ≤ s`: `mrepInt H` is `𝓕_t`-strongly measurable
and `∫_s^t G n dW → mrepInt H` in `L²(P)`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrep_spec). -/
theorem mrep_spec (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {H : ℝ → Ω → ℝ} {G : ℕ → ℝ → Ω → ℝ}
    (hG : MRepApprox P 𝓕 H s t G) :
    StronglyMeasurable[𝓕 t] (mrepInt P 𝓕 W H s t) ∧
      L2Tendsto P (fun n => itoInt P 𝓕 W (G n) s t) (mrepInt P 𝓕 W H s t) := by
  classical
  obtain ⟨Y, hYm, hY⟩ := exists_L2Tendsto (𝓕.le t) (fun k => stronglyMeasurable_itoInt)
    (fun k => memLp_itoInt_ms hB hW h𝓕 hs (hG.1 k)) (mrep_itoInt_cauchy hB hW h𝓕 hs hG)
  have hex : ∃ Y, StronglyMeasurable[𝓕 t] Y ∧ ∃ G, MRepApprox P 𝓕 H s t G ∧
      L2Tendsto P (fun n => itoInt P 𝓕 W (G n) s t) Y := ⟨Y, hYm, G, hG, hY⟩
  have e : mrepInt P 𝓕 W H s t = hex.choose := by simp only [mrepInt, hex, ↓reduceDIte]
  rw [e]
  obtain ⟨hm, G', hG', hL⟩ := hex.choose_spec
  exact ⟨hm, mrep_L2Tendsto_of_approx hB hW h𝓕 hs hG hG' hL⟩

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `mrepInt H` is `𝓕_t`-strongly measurable for every
`H` in the class.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.stronglyMeasurable_mrepInt). -/
theorem stronglyMeasurable_mrepInt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {H : ℝ → Ω → ℝ} (hH : MRepIntegrand P 𝓕 H s t) :
    StronglyMeasurable[𝓕 t] (mrepInt P 𝓕 W H s t) :=
  (mrep_spec hB hW h𝓕 hs hH.choose_spec).1

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `mrepInt H` is square integrable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.memLp_mrepInt). -/
theorem memLp_mrepInt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {H : ℝ → Ω → ℝ} (hH : MRepIntegrand P 𝓕 H s t) :
    MemLp (mrepInt P 𝓕 W H s t) 2 P :=
  (mrep_spec hB hW h𝓕 hs hH.choose_spec).2.2.1

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the class sits in `L²(μ_{s,t})`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.MRepIntegrand.memLp). -/
theorem MRepIntegrand.memLp {H : ℝ → Ω → ℝ} (hH : MRepIntegrand P 𝓕 H s t) :
    MemLp (Function.uncurry H) 2 (mrepMeasure P s t) :=
  hH.choose_spec.2.2.2.1

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: agreement with the toolkit integral.** A jointly
measurable mean-square continuous integrand is in the class and `mrepInt G = itoInt G` a.s.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrep_agree). -/
theorem mrep_agree (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {G : ℝ → Ω → ℝ} (hG : MSIntegrand P 𝓕 G s t)
    (hGm : Measurable (Function.uncurry G)) :
    MRepIntegrand P 𝓕 G s t ∧ mrepInt P 𝓕 W G s t =ᵐ[P] itoInt P 𝓕 W G s t := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hmem := mrep_memLp_uncurry hG hGm
  have hA : MRepApprox P 𝓕 G s t (fun _ => G) :=
    ⟨fun _ => hG, fun _ => hGm, fun _ => hmem, hmem, by simp⟩
  refine ⟨⟨_, hA⟩, ?_⟩
  have h1 := (mrep_spec hB hW h𝓕 hs hA).2
  have h2 : L2Tendsto P (fun _ : ℕ => itoInt P 𝓕 W G s t) (itoInt P 𝓕 W G s t) :=
    ⟨fun _ => memLp_itoInt_ms hB hW h𝓕 hs hG, memLp_itoInt_ms hB hW h𝓕 hs hG, by simp⟩
  exact ae_eq_of_L2Tendsto h1 h2

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the Itô isometry on the extended class**,
`E[(∫_s^t H dW)²] = ∫ H² dμ_{s,t}`, `0 ≤ s`.
Extends `TidyR10DoobFubini.integral_itoInt_sq_ms` to the extended class.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrep_isometry). -/
theorem mrep_isometry (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {H : ℝ → Ω → ℝ} (hH : MRepIntegrand P 𝓕 H s t) :
    ∫ ω, mrepInt P 𝓕 W H s t ω ^ 2 ∂P = ∫ x, Function.uncurry H x ^ 2 ∂mrepMeasure P s t := by
  obtain ⟨G, hG⟩ := hH
  have h1 := mrep_tendsto_integral_sq (mrep_spec hB hW h𝓕 hs hG).2
  have h2 := mrep_tendsto_integral_sq hG.2.2
  have e : ∀ n, ∫ ω, itoInt P 𝓕 W (G n) s t ω ^ 2 ∂P
      = ∫ x, Function.uncurry (G n) x ^ 2 ∂mrepMeasure P s t := fun n =>
    mrep_isometry_ms hB hW h𝓕 hs (hG.1 n) (hG.2.1 n)
  simp_rw [e] at h1
  exact tendsto_nhds_unique h1 h2

/-! ## Linearity -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: approximating sequences add.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.MRepApprox.add). -/
theorem MRepApprox.add {H K : ℝ → Ω → ℝ} {G G' : ℕ → ℝ → Ω → ℝ}
    (hG : MRepApprox P 𝓕 H s t G) (hG' : MRepApprox P 𝓕 K s t G') :
    MRepApprox P 𝓕 (fun u ω => H u ω + K u ω) s t (fun n u ω => G n u ω + G' n u ω) :=
  ⟨fun n => Cochrane.ZeroBound.TidyR7ItoBondStep.MSIntegrand.add (hG.1 n) (hG'.1 n),
    fun n => (hG.2.1 n).add (hG'.2.1 n), hG.2.2.add hG'.2.2⟩

/-- Cochrane (2023), A1 §1.6, pp. 567–568: approximating sequences scale.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.MRepApprox.const_mul). -/
theorem MRepApprox.const_mul {H : ℝ → Ω → ℝ} {G : ℕ → ℝ → Ω → ℝ}
    (hG : MRepApprox P 𝓕 H s t G) (c : ℝ) :
    MRepApprox P 𝓕 (fun u ω => c * H u ω) s t (fun n u ω => c * G n u ω) :=
  ⟨fun n => Cochrane.ZeroBound.TidyR7ItoBondStep.MSIntegrand.const_mul (hG.1 n) c,
    fun n => (hG.2.1 n).const_mul c, hG.2.2.const_mul c⟩

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the class is closed under sums.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrep_add). -/
theorem mrep_add {H K : ℝ → Ω → ℝ} (hH : MRepIntegrand P 𝓕 H s t)
    (hK : MRepIntegrand P 𝓕 K s t) : MRepIntegrand P 𝓕 (fun u ω => H u ω + K u ω) s t :=
  ⟨_, hH.choose_spec.add hK.choose_spec⟩

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the class is closed under constant multiples.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrep_const_mul). -/
theorem mrep_const_mul {H : ℝ → Ω → ℝ} (hH : MRepIntegrand P 𝓕 H s t) (c : ℝ) :
    MRepIntegrand P 𝓕 (fun u ω => c * H u ω) s t :=
  ⟨_, hH.choose_spec.const_mul c⟩

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the class is closed under differences.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrep_sub). -/
theorem mrep_sub {H K : ℝ → Ω → ℝ} (hH : MRepIntegrand P 𝓕 H s t)
    (hK : MRepIntegrand P 𝓕 K s t) : MRepIntegrand P 𝓕 (fun u ω => H u ω - K u ω) s t := by
  have e : (fun u ω => H u ω - K u ω) = fun u ω => H u ω + -1 * K u ω :=
    funext fun u => funext fun ω => by ring
  rw [e]
  exact mrep_add hH (mrep_const_mul hK (-1))

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `∫(H + K) dW = ∫H dW + ∫K dW`** a.s. on the
extended class, `0 ≤ s`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrepInt_add). -/
theorem mrepInt_add (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {H K : ℝ → Ω → ℝ} (hH : MRepIntegrand P 𝓕 H s t)
    (hK : MRepIntegrand P 𝓕 K s t) :
    mrepInt P 𝓕 W (fun u ω => H u ω + K u ω) s t =ᵐ[P]
      fun ω => mrepInt P 𝓕 W H s t ω + mrepInt P 𝓕 W K s t ω := by
  obtain ⟨G, hG⟩ := hH
  obtain ⟨G', hG'⟩ := hK
  have h1 := (mrep_spec hB hW h𝓕 hs (hG.add hG')).2
  have h2 : L2Tendsto P (fun n => itoInt P 𝓕 W (fun u ω => G n u ω + G' n u ω) s t)
      (fun ω => mrepInt P 𝓕 W H s t ω + mrepInt P 𝓕 W K s t ω) :=
    ((mrep_spec hB hW h𝓕 hs hG).2.add (mrep_spec hB hW h𝓕 hs hG').2).congr_seq
      (fun n => (itoInt_add_ms hB hW h𝓕 hs (hG.1 n) (hG'.1 n)).symm)
  exact ae_eq_of_L2Tendsto h1 h2

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `∫cH dW = c∫H dW`** a.s. on the extended class.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrepInt_const_mul). -/
theorem mrepInt_const_mul (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {H : ℝ → Ω → ℝ} (hH : MRepIntegrand P 𝓕 H s t)
    (c : ℝ) :
    mrepInt P 𝓕 W (fun u ω => c * H u ω) s t =ᵐ[P] fun ω => c * mrepInt P 𝓕 W H s t ω := by
  obtain ⟨G, hG⟩ := hH
  have h1 := (mrep_spec hB hW h𝓕 hs (hG.const_mul c)).2
  have h2 : L2Tendsto P (fun n => itoInt P 𝓕 W (fun u ω => c * G n u ω) s t)
      (fun ω => c * mrepInt P 𝓕 W H s t ω) :=
    ((mrep_spec hB hW h𝓕 hs hG).2.const_mul c).congr_seq
      (fun n => (itoInt_const_mul_ms hB hW h𝓕 hs (hG.1 n) c).symm)
  exact ae_eq_of_L2Tendsto h1 h2

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `∫(H − K) dW = ∫H dW − ∫K dW` a.s. on the
extended integrand class.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrepInt_sub). -/
theorem mrepInt_sub (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {H K : ℝ → Ω → ℝ} (hH : MRepIntegrand P 𝓕 H s t)
    (hK : MRepIntegrand P 𝓕 K s t) :
    mrepInt P 𝓕 W (fun u ω => H u ω - K u ω) s t =ᵐ[P]
      fun ω => mrepInt P 𝓕 W H s t ω - mrepInt P 𝓕 W K s t ω := by
  have e : (fun u ω => H u ω - K u ω) = fun u ω => H u ω + -1 * K u ω :=
    funext fun u => funext fun ω => by ring
  rw [e]
  filter_upwards [mrepInt_add hB hW h𝓕 hs hH (mrep_const_mul hK (-1)),
    mrepInt_const_mul hB hW h𝓕 hs hK (-1)] with ω h1 h2
  rw [h1, h2]
  ring

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the isometry for differences on the
extended integrand class**, `E[(∫H dW − ∫K dW)²] = ∫(H − K)² dμ_{s,t}`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrepInt_isometry_sub). -/
theorem mrepInt_isometry_sub (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {H K : ℝ → Ω → ℝ} (hH : MRepIntegrand P 𝓕 H s t)
    (hK : MRepIntegrand P 𝓕 K s t) :
    ∫ ω, (mrepInt P 𝓕 W H s t ω - mrepInt P 𝓕 W K s t ω) ^ 2 ∂P
      = ∫ x, (Function.uncurry H x - Function.uncurry K x) ^ 2 ∂mrepMeasure P s t := by
  have h := mrep_isometry hB hW h𝓕 hs (mrep_sub hH hK)
  rw [show (∫ x, (Function.uncurry H x - Function.uncurry K x) ^ 2 ∂mrepMeasure P s t)
    = ∫ x, Function.uncurry (fun u ω => H u ω - K u ω) x ^ 2 ∂mrepMeasure P s t from rfl, ← h]
  refine integral_congr_ae ?_
  filter_upwards [mrepInt_sub hB hW h𝓕 hs hH hK] with ω hω
  rw [hω]

/-! ## Zero mean and the martingale property -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (`E_s ∫_s^t H dW = 0`): orthogonality to the
square-integrable past** on the extended class: `E[Z ∫_s^t H dW] = 0` for `Z` square integrable
and `𝓕_s`-measurable, `0 ≤ s`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrepInt_integral_mul_eq_zero). -/
theorem mrepInt_integral_mul_eq_zero (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {H : ℝ → Ω → ℝ} (hH : MRepIntegrand P 𝓕 H s t)
    {Z : Ω → ℝ} (hZ : StronglyMeasurable[𝓕 s] Z) (hZ2 : MemLp Z 2 P) :
    ∫ ω, Z ω * mrepInt P 𝓕 W H s t ω ∂P = 0 := by
  obtain ⟨G, hG⟩ := hH
  have h := tendsto_integral_mul_of_L2Tendsto_memLp (mrep_spec hB hW h𝓕 hs hG).2 hZ2
  have e : ∀ n, ∫ ω, Z ω * itoInt P 𝓕 W (G n) s t ω ∂P = 0 := fun n =>
    integral_mul_itoInt_ms hB hW h𝓕 hs (hG.1 n) hZ hZ2
  simp_rw [e] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `E[∫_s^t H dW] = 0` on the extended class.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrepInt_integral_eq_zero). -/
theorem mrepInt_integral_eq_zero (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {H : ℝ → Ω → ℝ} (hH : MRepIntegrand P 𝓕 H s t) :
    ∫ ω, mrepInt P 𝓕 W H s t ω ∂P = 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h := mrepInt_integral_mul_eq_zero hB hW h𝓕 hs hH (Z := fun _ => 1)
    stronglyMeasurable_const (memLp_const 1)
  simpa using h

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `μ_{a,b} ≤ μ_{s,t}` for `[a, b] ⊆ [s, t]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrepMeasure_mono). -/
theorem mrepMeasure_mono [SFinite P] {a b : ℝ} (ha : s ≤ a) (hb : b ≤ t) :
    mrepMeasure P a b ≤ mrepMeasure P s t :=
  Measure.prod_mono (Measure.restrict_mono (Set.Ioc_subset_Ioc ha hb) le_rfl) le_rfl

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `L²` convergence on `μ_{s,t}` passes to
`μ_{a,b}`, `[a, b] ⊆ [s, t]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrep_L2Tendsto_mono). -/
theorem mrep_L2Tendsto_mono [SFinite P] {X : ℕ → ℝ × Ω → ℝ} {Y : ℝ × Ω → ℝ}
    (h : L2Tendsto (mrepMeasure P s t) X Y) {a b : ℝ} (ha : s ≤ a) (hb : b ≤ t) :
    L2Tendsto (mrepMeasure P a b) X Y := by
  have hle := mrepMeasure_mono (P := P) ha hb
  refine ⟨fun k => (h.1 k).mono_measure hle, h.2.1.mono_measure hle, ?_⟩
  refine squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) (fun k => ?_) h.2.2
  exact integral_mono_measure hle (ae_of_all _ fun _ => sq_nonneg _)
    ((h.1 k).sub h.2.1).integrable_sq

/-- Cochrane (2023), A1 §1.6, pp. 567–568: an approximating sequence on `[s, t]` is one on
`[a, b] ⊆ [s, t]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.MRepApprox.mono). -/
theorem MRepApprox.mono [SFinite P] {H : ℝ → Ω → ℝ} {G : ℕ → ℝ → Ω → ℝ}
    (hG : MRepApprox P 𝓕 H s t G) {a b : ℝ} (ha : s ≤ a) (hb : b ≤ t) :
    MRepApprox P 𝓕 H a b G :=
  ⟨fun n => (hG.1 n).mono ha hb, hG.2.1, mrep_L2Tendsto_mono hG.2.2 ha hb⟩

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the class on `[s, t]` restricts to `[a, b] ⊆ [s, t]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrep_mono). -/
theorem mrep_mono [SFinite P] {H : ℝ → Ω → ℝ} (hH : MRepIntegrand P 𝓕 H s t) {a b : ℝ}
    (ha : s ≤ a) (hb : b ≤ t) : MRepIntegrand P 𝓕 H a b :=
  ⟨_, hH.choose_spec.mono ha hb⟩

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: additivity over intervals** on the extended class:
`∫_s^t H dW = ∫_s^r H dW + ∫_r^t H dW` a.s., `0 ≤ s ≤ r ≤ t`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrepInt_add_mrepInt). -/
theorem mrepInt_add_mrepInt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {r : ℝ} (hsr : s ≤ r) (hrt : r ≤ t)
    {H : ℝ → Ω → ℝ} (hH : MRepIntegrand P 𝓕 H s t) :
    mrepInt P 𝓕 W H s t =ᵐ[P] fun ω => mrepInt P 𝓕 W H s r ω + mrepInt P 𝓕 W H r t ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨G, hG⟩ := hH
  have h1 := (mrep_spec hB hW h𝓕 hs hG).2
  have h2 : L2Tendsto P (fun n => itoInt P 𝓕 W (G n) s t)
      (fun ω => mrepInt P 𝓕 W H s r ω + mrepInt P 𝓕 W H r t ω) :=
    ((mrep_spec hB hW h𝓕 hs (hG.mono le_rfl hrt)).2.add
      (mrep_spec hB hW h𝓕 (hs.trans hsr) (hG.mono hsr le_rfl)).2).congr_seq
      (fun n => (itoInt_add_itoInt_ms hB hW h𝓕 hs hsr hrt (hG.1 n)).symm)
  exact ae_eq_of_L2Tendsto h1 h2

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the martingale property on the extended class**,
`E[∫_s^t H dW | 𝓕_r] = ∫_s^r H dW` a.s., `0 ≤ s ≤ r ≤ t`.
Extends `TidyR7ItoUnbounded.condExp_itoInt_ms` to the extended class.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrepInt_condExp). -/
theorem mrepInt_condExp (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {r : ℝ} (hsr : s ≤ r) (hrt : r ≤ t)
    {H : ℝ → Ω → ℝ} (hH : MRepIntegrand P 𝓕 H s t) :
    P[mrepInt P 𝓕 W H s t | 𝓕 r] =ᵐ[P] mrepInt P 𝓕 W H s r := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hsr' := mrep_mono hH le_rfl hrt
  have hrt' := mrep_mono hH hsr le_rfl
  have hi : ∀ {a b}, 0 ≤ a → MRepIntegrand P 𝓕 H a b → Integrable (mrepInt P 𝓕 W H a b) P :=
    fun ha h => (memLp_mrepInt hB hW h𝓕 ha h).integrable one_le_two
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le r) (hi hs hH)
    (fun _ _ _ => (hi hs hsr').integrableOn) (fun A hA _ => ?_)
    (stronglyMeasurable_mrepInt hB hW h𝓕 hs hsr').aestronglyMeasurable).symm
  have hz := mrepInt_integral_mul_eq_zero hB hW h𝓕 (hs.trans hsr) hrt'
    (Z := A.indicator fun _ => (1 : ℝ)) (stronglyMeasurable_const.indicator hA)
    ((memLp_const 1).indicator (𝓕.le r A hA))
  have e : ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω * mrepInt P 𝓕 W H r t ω ∂P
      = ∫ ω in A, mrepInt P 𝓕 W H r t ω ∂P := by
    rw [← integral_indicator (𝓕.le r A hA)]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    by_cases h : ω ∈ A <;> simp [h]
  rw [e] at hz
  symm
  rw [setIntegral_congr_ae (𝓕.le r A hA) (by
      filter_upwards [mrepInt_add_mrepInt hB hW h𝓕 hs hsr hrt hH] with ω hω _ using hω),
    integral_add (hi hs hsr').integrableOn (hi (hs.trans hsr) hrt').integrableOn, hz, add_zero]

/-! ## Closedness and continuity -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the class is closed in `L²(μ_{s,t})`.** If every
`H k` is in the class and `H k → H` in `L²(μ_{s,t})`, then `H` is in the class (diagonal
sequence).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrep_of_L2Tendsto). -/
theorem mrep_of_L2Tendsto {Hs : ℕ → ℝ → Ω → ℝ} {H : ℝ → Ω → ℝ}
    (hHs : ∀ k, MRepIntegrand P 𝓕 (Hs k) s t)
    (hL : L2Tendsto (mrepMeasure P s t) (fun k => Function.uncurry (Hs k))
      (Function.uncurry H)) : MRepIntegrand P 𝓕 H s t := by
  choose G hG using hHs
  have hex : ∀ k, ∃ n, ∫ x, (Function.uncurry (G k n) x - Function.uncurry (Hs k) x) ^ 2
      ∂mrepMeasure P s t ≤ 1 / ((k : ℝ) + 1) := fun k =>
    ((hG k).2.2.2.2.eventually (ge_mem_nhds (by positivity))).exists
  choose N hN using hex
  refine ⟨fun k => G k (N k), fun k => (hG k).1 (N k), fun k => (hG k).2.1 (N k),
    fun k => (hG k).2.2.1 (N k), hL.2.1, ?_⟩
  have hle : ∀ k, ∫ x, (Function.uncurry (G k (N k)) x - Function.uncurry H x) ^ 2
      ∂mrepMeasure P s t ≤ 2 * (1 / ((k : ℝ) + 1))
        + 2 * ∫ x, (Function.uncurry (Hs k) x - Function.uncurry H x) ^ 2 ∂mrepMeasure P s t := by
    intro k
    have h := integral_sq_sub_le (P := mrepMeasure P s t) (hL.1 k) ((hG k).2.2.1 (N k)) hL.2.1
    have e : ∫ x, (Function.uncurry (Hs k) x - Function.uncurry (G k (N k)) x) ^ 2
        ∂mrepMeasure P s t = ∫ x, (Function.uncurry (G k (N k)) x - Function.uncurry (Hs k) x)
          ^ 2 ∂mrepMeasure P s t := integral_congr_ae (ae_of_all _ fun x => by ring)
    rw [e] at h
    linarith [hN k]
  have hlim : Tendsto (fun k : ℕ => 2 * (1 / ((k : ℝ) + 1))
      + 2 * ∫ x, (Function.uncurry (Hs k) x - Function.uncurry H x) ^ 2 ∂mrepMeasure P s t)
      atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 2).add (hL.2.2.const_mul 2)
    simpa using this
  exact squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) hle hlim

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: continuity of the extended integral.** If `H k`,
`H` are in the class and `H k → H` in `L²(μ_{s,t})`, then `∫_s^t H k dW → ∫_s^t H dW` in
`L²(P)`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR13MRepIntegral.mrepInt_L2Tendsto). -/
theorem mrepInt_L2Tendsto (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {Hs : ℕ → ℝ → Ω → ℝ} {H : ℝ → Ω → ℝ}
    (hHs : ∀ k, MRepIntegrand P 𝓕 (Hs k) s t) (hH : MRepIntegrand P 𝓕 H s t)
    (hL : L2Tendsto (mrepMeasure P s t) (fun k => Function.uncurry (Hs k))
      (Function.uncurry H)) :
    L2Tendsto P (fun k => mrepInt P 𝓕 W (Hs k) s t) (mrepInt P 𝓕 W H s t) := by
  refine ⟨fun k => memLp_mrepInt hB hW h𝓕 hs (hHs k), memLp_mrepInt hB hW h𝓕 hs hH, ?_⟩
  have e : ∀ k, ∫ ω, (mrepInt P 𝓕 W (Hs k) s t ω - mrepInt P 𝓕 W H s t ω) ^ 2 ∂P
      = ∫ x, (Function.uncurry (Hs k) x - Function.uncurry H x) ^ 2 ∂mrepMeasure P s t :=
    fun k => mrepInt_isometry_sub hB hW h𝓕 hs (hHs k) hH
  simp_rw [e]
  exact hL.2.2

end Cochrane.ZeroBound.TidyR13MRepIntegral
