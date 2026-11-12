/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR7MonetarismIto
import Monetarism.TidyR7MonetarismValuation

/-!
# The valuation equations (1.33) and (1.34) with diffusive bonds

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.33)–(1.34), in the model
`TidyR7MonetarismIto.ItoMonetaryModel`, assumed on every `[s, T]`, `T > s`, with fixed bounds.
I3's route (`TidyR7MonetarismValuation`): the integrated (1.32) gives the finite-horizon budget,
and the valuation equation is equivalent to the transversality condition.

## (1.33): a bracket term enters the valuation equation

With the corrected (1.32) (`TidyR7MonetarismIto.ItoMonetaryModel.incr_1_32_ito_general`) the
discounted flow is `F^c_T = ∫_s^T (Λs − i^m nM) du + ∫_s^T n dM − ∫_s^T σ_Xσ_B du` (`flowItoC`):
* `rec_1_33_ito`: `n_sB_s = E_s[n_TB_T] + E_s[F^c_T]` for every `T ≥ s`;
* `valuation_1_33_ito_seq` (limit form, no convergence hypothesis): `E_s[F^c_{T_k}] → n_sB_s`
  a.s. iff `E_s[n_{T_k}B_{T_k}] → 0` a.s.; `valuation_1_33_ito` (`L¹` form);
* `valuation_1_33_ito_book_iff`: under the transversality condition, the book's (1.33) (flow
  `F_T` without the bracket, `flowItoBook`) holds in the limit form **iff**
  `E_s[∫_s^{T_k} σ_Xσ_B du] → 0` a.s.;
* `valuation_1_33_ito_uncorrelated`: if `σ_Xσ_B = 0` a.s. (bonds' diffusion uncorrelated with
  `Λ/P`, e.g. bonds of bounded variation), the book's (1.33) holds iff transversality, as in I3;
* `real_form_ito`: the book's normalisation `B_s/P_s = E_s[G/Λ_s]` (restates
  `TidyR7MonetarismValuation.real_form` for this model).

## (1.34): verbatim

`B + M` has no diffusion, so `rec_1_34_ito`, `valuation_1_34_ito_seq`, `valuation_1_34_ito`
hold with the book's flow `∫_s^T (Λs + (i − i^m)nM) du`: (1.34) needs no correction.
-/

namespace Cochrane.Monetarism.TidyR7MonetarismItoValuation

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoSums Cochrane.Monetarism.TidyR7ItoIntegral
  Cochrane.Monetarism.TidyR7ItoUnbounded Cochrane.Monetarism.TidyR7ItoProducts
  Cochrane.Monetarism.TidyR7ItoProcess Cochrane.Monetarism.TidyR7ItoProductRule
  Cochrane.Monetarism.TidyR7ItoBondStep Cochrane.Monetarism.TidyR7MonetarismModel
  Cochrane.Monetarism.TidyR7MonetarismIto Cochrane.Monetarism.TidyR7MonetarismValuation
open Cochrane.Monetarism.TidyR7ProductStep (addProc)
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: **the book's discounted flow** of (1.33) on
`[s, T]`, `F_T = ∫_s^T (Λs − i^m nM) du + ∫_s^T n dM`, `n = Λ/P`. -/
noncomputable def flowItoBook (μ : Measure Ω) (𝓕 : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ℝ)
    (Λ P M im sp m σM : ℝ → Ω → ℝ) (s T : ℝ) (ω : Ω) : ℝ :=
  dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω) s T ω
    + moneyInt μ 𝓕 W Λ P m σM s T ω

/-- Cochrane (2023), A1 §1.6, (1.32)–(1.33), p. 567: **the bracket** `∫_s^T σ_Xσ_B du`, the
integrated `d[Λ/P, B]`. -/
noncomputable def bracket (σX σB : ℝ → Ω → ℝ) (s T : ℝ) (ω : Ω) : ℝ :=
  ∫ u in s..T, σX u ω * σB u ω

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: **the corrected discounted flow**
`F^c_T = F_T − ∫_s^T σ_Xσ_B du`. -/
noncomputable def flowItoC (μ : Measure Ω) (𝓕 : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ℝ)
    (Λ P M im sp m σM σX σB : ℝ → Ω → ℝ) (s T : ℝ) (ω : Ω) : ℝ :=
  flowItoBook μ 𝓕 W Λ P M im sp m σM s T ω - bracket σX σB s T ω

/-- Cochrane (2023), A1 §1.6, (1.34), p. 567: **the discounted flow of (1.34)**,
`∫_s^T (Λs + (i − i^m)nM) du`. -/
noncomputable def flowIto134 (μ : Measure Ω) (𝓕 : Filtration ℝ mΩ)
    (Λ P M i im sp : ℝ → Ω → ℝ) (s T : ℝ) (ω : Ω) : ℝ :=
  dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω + (i u ω - im u ω) * disc Λ P u ω * M u ω) s T ω

variable {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ} {s : ℝ}
  {Λ P B M i im sp β σB m σM σX : ℝ → Ω → ℝ} {Cn CX Cβ CB Cm CM : ℝ}

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: all the flows vanish on `[s, s]`. -/
theorem flows_self (ω : Ω) :
    flowItoBook μ 𝓕 W Λ P M im sp m σM s s ω = 0 ∧ bracket σX σB s s ω = 0 ∧
      flowItoC μ 𝓕 W Λ P M im sp m σM σX σB s s ω = 0 ∧
      flowIto134 μ 𝓕 Λ P M i im sp s s ω = 0 := by
  simp [flowItoC, flowItoBook, bracket, flowIto134, moneyInt, intIto, dtInt_of_le le_rfl,
    itoInt_of_le le_rfl]

/-- **Cochrane (2023), A1 §1.6, (1.33)–(1.34), p. 567: dividing by `Λ_s`.** If `Λ_s > 0` is
`𝓕_s`-measurable and `P_s > 0`, then for `G`, `G/Λ_s` integrable:
`(Λ_s/P_s)X = E_s[G]` a.s. iff `X/P_s = E_s[G/Λ_s]` a.s.
Restates `TidyR7MonetarismValuation.real_form` with these hypotheses in place of a
`TidyR7MonetarismModel.MonetaryModel`. -/
theorem real_form_ito (hΛm : StronglyMeasurable[𝓕 s] (Λ s)) (hΛ : ∀ ω, 0 < Λ s ω)
    (hP : ∀ ω, 0 < P s ω) {X G : Ω → ℝ} (hG : Integrable G μ)
    (hGΛ : Integrable (fun ω => G ω / Λ s ω) μ) :
    (fun ω => disc Λ P s ω * X ω) =ᵐ[μ] μ[G | 𝓕 s] ↔
      (fun ω => X ω / P s ω) =ᵐ[μ] μ[fun ω => G ω / Λ s ω | 𝓕 s] := by
  have hinv : StronglyMeasurable[𝓕 s] fun ω => (Λ s ω)⁻¹ :=
    hΛm.measurable.inv.stronglyMeasurable
  have e : (fun ω => G ω / Λ s ω) = (fun ω => (Λ s ω)⁻¹) * G :=
    funext fun ω => by simp only [Pi.mul_apply]; ring
  have hpull := condExp_mul_of_stronglyMeasurable_left hinv (by rw [← e]; exact hGΛ) hG
  rw [← e] at hpull
  have hΛ0 : ∀ ω, Λ s ω ≠ 0 := fun ω => (hΛ ω).ne'
  have hP0 : ∀ ω, P s ω ≠ 0 := fun ω => (hP ω).ne'
  constructor
  · intro h
    filter_upwards [h, hpull] with ω h1 h2
    rw [h2, Pi.mul_apply, ← h1]
    simp only [disc]
    field_simp [hΛ0 ω, hP0 ω]
  · intro h
    filter_upwards [h, hpull] with ω h1 h2
    rw [h2, Pi.mul_apply] at h1
    have h1' : X ω = P s ω * ((Λ s ω)⁻¹ * μ[G | 𝓕 s] ω) := by
      rw [← h1]; field_simp [hP0 ω]
    rw [h1']
    simp only [disc]
    field_simp [hΛ0 ω, hP0 ω]

variable (hm : ∀ T, s < T →
  ItoMonetaryModel μ 𝓕 W Λ P B M i im sp β σB m σM σX s T Cn CX Cβ CB Cm CM)
include hm

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: `n_TB_T` is integrable for every `T ≥ s`. -/
theorem integrable_nB (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) {T : ℝ} (hT : s ≤ T) :
    Integrable (fun ω => disc Λ P T ω * B T ω) μ := by
  have h := hm (T + 1) (by linarith)
  have hu : T ∈ Set.Icc s (T + 1) := ⟨hT, by linarith⟩
  exact (h.disc_ito.memLp hBM hWm h𝓕 hs hu).integrable_mul (h.bonds_ito.memLp hBM hWm h𝓕 hs hu)

/-- Cochrane (2023), A1 §1.6, (1.34), p. 567: `n_T(B + M)_T` is integrable for every `T ≥ s`. -/
theorem integrable_nW (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) {T : ℝ} (hT : s ≤ T) :
    Integrable (fun ω => disc Λ P T ω * addProc B M T ω) μ := by
  have h := hm (T + 1) (by linarith)
  have hu : T ∈ Set.Icc s (T + 1) := ⟨hT, by linarith⟩
  exact (h.disc_ito.memLp hBM hWm h𝓕 hs hu).integrable_mul
    ((h.wealth_ito hBM hWm h𝓕 hs).memLp hBM hWm h𝓕 hs hu)

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: `n_sB_s` and `n_s(B + M)_s` are
`𝓕_s`-measurable. -/
theorem stronglyMeasurable_nB_nW :
    StronglyMeasurable[𝓕 s] (fun ω => disc Λ P s ω * B s ω) ∧
      StronglyMeasurable[𝓕 s] (fun ω => disc Λ P s ω * addProc B M s ω) := by
  have h := hm (s + 1) (by linarith)
  have hu : s ∈ Set.Icc s (s + 1) := ⟨le_rfl, by linarith⟩
  refine ⟨(h.disc_ito.adapted s hu).mul (h.bonds_ito.adapted s hu),
    (h.disc_ito.adapted s hu).mul ((h.bonds_ito.adapted s hu).add (h.money_ito.adapted s hu))⟩

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: the flows are integrable on every `[s, T]`. -/
theorem integrable_flows (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) {T : ℝ} (hT : s ≤ T) :
    Integrable (flowItoBook μ 𝓕 W Λ P M im sp m σM s T) μ ∧
      Integrable (bracket σX σB s T) μ ∧
      Integrable (flowItoC μ 𝓕 W Λ P M im sp m σM σX σB s T) μ := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  rcases hT.lt_or_eq with hT | hT
  · have h := hm T hT
    have i1 : Integrable (flowItoBook μ 𝓕 W Λ P M im sp m σM s T) μ :=
      (h.integrable_rhs_1_32 hBM hWm h𝓕 hs).neg.congr (ae_of_all _ fun ω => by
        simp [flowItoBook])
    have i2 : Integrable (bracket σX σB s T) μ :=
      (memLp_integral_drift (itoIntegrand_mul h.disc_ito.diff h.bonds_ito.diff) le_rfl
        hT.le le_rfl).integrable one_le_two
    exact ⟨i1, i2, i1.sub i2⟩
  · subst hT
    have e1 : flowItoBook μ 𝓕 W Λ P M im sp m σM s s = 0 :=
      funext fun ω => (flows_self (σX := σX) (σB := σB) (i := i) ω).1
    have e2 : bracket σX σB s s = 0 :=
      funext fun ω => (flows_self (μ := μ) (𝓕 := 𝓕) (W := W) (Λ := Λ) (P := P) (M := M)
        (im := im) (sp := sp) (m := m) (σM := σM) (i := i) ω).2.1
    have e3 : flowItoC μ 𝓕 W Λ P M im sp m σM σX σB s s = 0 :=
      funext fun ω => (flows_self (i := i) ω).2.2.1
    rw [e1, e2, e3]
    exact ⟨integrable_zero _ _ _, integrable_zero _ _ _, integrable_zero _ _ _⟩

/-- Cochrane (2023), A1 §1.6, (1.34), p. 567: the flow `∫_s^T (Λs + (i − i^m)nM) du` of (1.34)
is integrable on every `[s, T]` (its integrand is `−(n(β + m) + (B + M)(−in))`, mean-square
continuous). -/
theorem integrable_flow134 (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) {T : ℝ} (hT : s ≤ T) :
    Integrable (flowIto134 μ 𝓕 Λ P M i im sp s T) μ := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  rcases hT.lt_or_eq with hT | hT
  · have h := hm T hT
    have hn := h.disc_ito
    have hw := h.wealth_ito hBM hWm h𝓕 hs
    have G := MSIntegrand.add (MSIntegrand.mul_itoIntegrand (hn.toMS hBM hWm h𝓕 hs) hw.drift)
      (MSIntegrand.mul_itoIntegrand (hw.toMS hBM hWm h𝓕 hs) hn.drift)
    have e : (fun u ω => Λ u ω * sp u ω + (i u ω - im u ω) * disc Λ P u ω * M u ω) =
        fun u ω => -1 * (disc Λ P u ω * (β u ω + m u ω)
          + addProc B M u ω * -(i u ω * disc Λ P u ω)) :=
      funext fun u => funext fun ω => h.rate_1_34 u ω
    change Integrable (dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω
      + (i u ω - im u ω) * disc Λ P u ω * M u ω) s T) μ
    rw [e]
    exact (memLp_dtInt (MSIntegrand.const_mul G (-1))).integrable one_le_two
  · subst hT
    have e : flowIto134 μ 𝓕 Λ P M i im sp s s = 0 :=
      funext fun ω => (flows_self (μ := μ) (𝓕 := 𝓕) (W := W) (Λ := Λ) (P := P) (M := M)
        (im := im) (sp := sp) (m := m) (σM := σM) (i := i) (σX := σX) (σB := σB) ω).2.2.2
    rw [e]
    exact integrable_zero _ _ _

/-! ## (1.33) -/

/-- **Cochrane (2023), A1 §1.6, (1.32) ⇒ (1.33), p. 567: the finite-horizon budget with the
bracket.** For every `T ≥ s`, a.s. `n_sB_s = E_s[n_TB_T] + E_s[F^c_T]`,
`F^c_T = ∫_s^T (Λs − i^m nM) du + ∫_s^T n dM − ∫_s^T σ_Xσ_B du`.
An instance of `TidyR7MonetarismValuation.rec_of_incr`; the analogue of
`TidyR7MonetarismValuation.MonetaryModel.rec_1_33`. -/
theorem rec_1_33_ito (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) {T : ℝ} (hT : s ≤ T) :
    (fun ω => disc Λ P s ω * B s ω) =ᵐ[μ]
      μ[fun ω => disc Λ P T ω * B T ω | 𝓕 s]
        + μ[flowItoC μ 𝓕 W Λ P M im sp m σM σX σB s T | 𝓕 s] := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have hYs := (stronglyMeasurable_nB_nW hm).1
  have hYi := integrable_nB hm hBM hWm h𝓕 hs le_rfl
  rcases hT.lt_or_eq with hT | hT
  · refine rec_of_incr (Y := fun T ω => disc Λ P T ω * B T ω) ?_ hYs hYi
      (integrable_nB hm hBM hWm h𝓕 hs hT.le)
    refine ((hm T hT).incr_1_32_ito_general hBM hWm h𝓕 hs hT).trans
      (condExp_congr_ae (ae_of_all _ fun ω => ?_))
    simp only [flowItoC, flowItoBook, bracket]
    ring
  · subst hT
    have e : flowItoC μ 𝓕 W Λ P M im sp m σM σX σB s s = 0 :=
      funext fun ω => (flows_self (i := i) ω).2.2.1
    rw [e, condExp_zero, condExp_of_stronglyMeasurable (𝓕.le s) hYs hYi]
    simp

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: valuation iff transversality, limit form, with
the bracket.** Along any times `T_k ≥ s`: a.s. `E_s[F^c_{T_k}] → n_sB_s` iff a.s.
`E_s[n_{T_k}B_{T_k}] → 0`.
An instance of `TidyR7MonetarismValuation.valuation_iff_tvc_seq`; the analogue of
`TidyR7MonetarismValuation.MonetaryModel.valuation_1_33_seq`. -/
theorem valuation_1_33_ito_seq (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) {T : ℕ → ℝ} (hT : ∀ k, s ≤ T k) :
    (∀ᵐ ω ∂μ, Tendsto (fun k => μ[flowItoC μ 𝓕 W Λ P M im sp m σM σX σB s (T k) | 𝓕 s] ω)
      atTop (𝓝 (disc Λ P s ω * B s ω))) ↔
      ∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => disc Λ P (T k) ω * B (T k) ω | 𝓕 s] ω) atTop
        (𝓝 0) :=
  valuation_iff_tvc_seq (Y := fun T ω => disc Λ P T ω * B T ω)
    (F := fun T => flowItoC μ 𝓕 W Λ P M im sp m σM σX σB s T)
    (fun _ hT => rec_1_33_ito hm hBM hWm h𝓕 hs hT) hT

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: valuation iff transversality, `L¹` form, with the
bracket.** If `F^c_T → G` in `L¹` (`G` integrable), then `n_sB_s = E_s[G]` a.s. iff
`E_s[n_TB_T] → 0` in `L¹`.
An instance of `TidyR7MonetarismValuation.valuation_iff_tvc_flow`; the analogue of
`TidyR7MonetarismValuation.MonetaryModel.valuation_1_33`. -/
theorem valuation_1_33_ito (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) {G : Ω → ℝ} (hG : Integrable G μ)
    (hconv : Tendsto (fun T => ∫ ω, |flowItoC μ 𝓕 W Λ P M im sp m σM σX σB s T ω - G ω| ∂μ)
      atTop (𝓝 0)) :
    (fun ω => disc Λ P s ω * B s ω) =ᵐ[μ] μ[G | 𝓕 s] ↔
      Tendsto (fun T => ∫ ω, |μ[fun ω => disc Λ P T ω * B T ω | 𝓕 s] ω| ∂μ) atTop (𝓝 0) := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  exact valuation_iff_tvc_flow (Y := fun T ω => disc Λ P T ω * B T ω)
    (F := fun T => flowItoC μ 𝓕 W Λ P M im sp m σM σX σB s T)
    (fun _ hT => rec_1_33_ito hm hBM hWm h𝓕 hs hT)
    (fun _ hT => integrable_nB hm hBM hWm h𝓕 hs hT)
    (fun _ hT => (integrable_flows hm hBM hWm h𝓕 hs hT).2.2) hG hconv

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: when the book's (1.33) survives diffusive
bonds.** Under the transversality condition `E_s[n_{T_k}B_{T_k}] → 0` a.s. (times `T_k ≥ s`),
the book's limit-form (1.33), `E_s[F_{T_k}] → n_sB_s` a.s. with the bracket-free flow `F`, holds
**iff** `E_s[∫_s^{T_k} σ_Xσ_B du] → 0` a.s. -/
theorem valuation_1_33_ito_book_iff (hBM : IsPreBrownianReal W μ)
    (hWm : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) {T : ℕ → ℝ}
    (hT : ∀ k, s ≤ T k)
    (htvc : ∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => disc Λ P (T k) ω * B (T k) ω | 𝓕 s] ω)
      atTop (𝓝 0)) :
    (∀ᵐ ω ∂μ, Tendsto (fun k => μ[flowItoBook μ 𝓕 W Λ P M im sp m σM s (T k) | 𝓕 s] ω)
      atTop (𝓝 (disc Λ P s ω * B s ω))) ↔
      ∀ᵐ ω ∂μ, Tendsto (fun k => μ[bracket σX σB s (T k) | 𝓕 s] ω) atTop (𝓝 0) := by
  have hc := (valuation_1_33_ito_seq hm hBM hWm h𝓕 hs hT).2 htvc
  have hadd : ∀ᵐ ω ∂μ, ∀ k, μ[flowItoBook μ 𝓕 W Λ P M im sp m σM s (T k) | 𝓕 s] ω =
      μ[flowItoC μ 𝓕 W Λ P M im sp m σM σX σB s (T k) | 𝓕 s] ω
        + μ[bracket σX σB s (T k) | 𝓕 s] ω := by
    refine ae_all_iff.2 fun k => ?_
    obtain ⟨-, i2, i3⟩ := integrable_flows hm hBM hWm h𝓕 hs (T := T k) (hT k)
    have e : flowItoBook μ 𝓕 W Λ P M im sp m σM s (T k) =
        flowItoC μ 𝓕 W Λ P M im sp m σM σX σB s (T k) + bracket σX σB s (T k) :=
      funext fun ω => by simp only [flowItoC, Pi.add_apply]; ring
    filter_upwards [condExp_add i3 i2 (𝓕 s)] with ω h
    rw [e, h, Pi.add_apply]
  constructor
  · intro h
    filter_upwards [h, hc, hadd] with ω h1 h2 h3
    have e : ∀ k, μ[bracket σX σB s (T k) | 𝓕 s] ω =
        μ[flowItoBook μ 𝓕 W Λ P M im sp m σM s (T k) | 𝓕 s] ω
          - μ[flowItoC μ 𝓕 W Λ P M im sp m σM σX σB s (T k) | 𝓕 s] ω := fun k => by
      rw [h3 k]; ring
    simp_rw [e]
    simpa using h1.sub h2
  · intro h
    filter_upwards [h, hc, hadd] with ω h1 h2 h3
    simp_rw [h3]
    simpa using h2.add h1

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the book's (1.33) when bonds' diffusion is
uncorrelated with `Λ/P`.** If `σ_Xσ_B = 0` on `[s, ∞)` a.s. (e.g. bonds of bounded variation),
then along any times `T_k ≥ s`: the book's limit form `E_s[F_{T_k}] → n_sB_s` a.s. holds iff
the transversality condition `E_s[n_{T_k}B_{T_k}] → 0` a.s.
Compare `TidyR7MonetarismValuation.MonetaryModel.valuation_1_33_seq`. -/
theorem valuation_1_33_ito_uncorrelated (hBM : IsPreBrownianReal W μ)
    (hWm : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) {T : ℕ → ℝ}
    (hT : ∀ k, s ≤ T k) (hσ : ∀ᵐ ω ∂μ, ∀ u, s ≤ u → σX u ω * σB u ω = 0) :
    (∀ᵐ ω ∂μ, Tendsto (fun k => μ[flowItoBook μ 𝓕 W Λ P M im sp m σM s (T k) | 𝓕 s] ω)
      atTop (𝓝 (disc Λ P s ω * B s ω))) ↔
      ∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => disc Λ P (T k) ω * B (T k) ω | 𝓕 s] ω) atTop
        (𝓝 0) := by
  have hz : ∀ᵐ ω ∂μ, ∀ k, μ[bracket σX σB s (T k) | 𝓕 s] ω = 0 := by
    refine ae_all_iff.2 fun k => ?_
    have h := condExp_bracket_zero (μ := μ) (𝓕 := 𝓕) (σB := fun u ω => σX u ω * σB u ω)
      (σX := fun _ _ => (1 : ℝ)) (hT k) (by
        filter_upwards [hσ] with ω hω u hu
        exact hω u hu.1)
    simp only [mul_one] at h
    exact h
  have hbr : ∀ᵐ ω ∂μ, Tendsto (fun k => μ[bracket σX σB s (T k) | 𝓕 s] ω) atTop (𝓝 0) := by
    filter_upwards [hz] with ω hω
    simp_rw [hω]
    exact tendsto_const_nhds
  constructor
  · intro h
    have hadd : ∀ᵐ ω ∂μ, ∀ k, μ[flowItoBook μ 𝓕 W Λ P M im sp m σM s (T k) | 𝓕 s] ω =
        μ[flowItoC μ 𝓕 W Λ P M im sp m σM σX σB s (T k) | 𝓕 s] ω := by
      refine ae_all_iff.2 fun k => ?_
      obtain ⟨-, i2, i3⟩ := integrable_flows hm hBM hWm h𝓕 hs (T := T k) (hT k)
      have e : flowItoBook μ 𝓕 W Λ P M im sp m σM s (T k) =
          flowItoC μ 𝓕 W Λ P M im sp m σM σX σB s (T k) + bracket σX σB s (T k) :=
        funext fun ω => by simp only [flowItoC, Pi.add_apply]; ring
      filter_upwards [condExp_add i3 i2 (𝓕 s), (ae_all_iff.1 hz) k] with ω h1 h2
      rw [e, h1, Pi.add_apply, h2, add_zero]
    refine (valuation_1_33_ito_seq hm hBM hWm h𝓕 hs hT).1 ?_
    filter_upwards [h, hadd] with ω h1 h2
    simp_rw [← h2]
    exact h1
  · intro h
    exact (valuation_1_33_ito_book_iff hm hBM hWm h𝓕 hs hT h).2 hbr

/-! ## (1.34) -/

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567: the finite-horizon budget for bonds plus money,
verbatim.** For every `T ≥ s`, a.s.
`n_s(B + M)_s = E_s[n_T(B + M)_T] + E_s∫_s^T (Λs + (i − i^m)nM) du`.
An instance of `TidyR7MonetarismValuation.rec_of_incr`. -/
theorem rec_1_34_ito (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) {T : ℝ} (hT : s ≤ T) :
    (fun ω => disc Λ P s ω * addProc B M s ω) =ᵐ[μ]
      μ[fun ω => disc Λ P T ω * addProc B M T ω | 𝓕 s]
        + μ[flowIto134 μ 𝓕 Λ P M i im sp s T | 𝓕 s] := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have hYs := (stronglyMeasurable_nB_nW hm).2
  have hYi := integrable_nW hm hBM hWm h𝓕 hs le_rfl
  rcases hT.lt_or_eq with hT | hT
  · exact rec_of_incr (Y := fun T ω => disc Λ P T ω * addProc B M T ω)
      ((hm T hT).incr_1_34_ito hBM hWm h𝓕 hs hT) hYs hYi
      (integrable_nW hm hBM hWm h𝓕 hs hT.le)
  · subst hT
    have e : flowIto134 μ 𝓕 Λ P M i im sp s s = 0 :=
      funext fun ω => (flows_self (μ := μ) (𝓕 := 𝓕) (W := W) (Λ := Λ) (P := P) (M := M)
        (im := im) (sp := sp) (m := m) (σM := σM) (i := i) (σX := σX) (σB := σB) ω).2.2.2
    rw [e, condExp_zero, condExp_of_stronglyMeasurable (𝓕.le s) hYs hYi]
    simp

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567: valuation iff transversality, limit form,
verbatim with diffusive bonds.** Along any times `T_k ≥ s`: a.s.
`E_s∫_s^{T_k} (Λs + (i − i^m)nM) du → n_s(B + M)_s` iff a.s. `E_s[n_{T_k}(B + M)_{T_k}] → 0`.
An instance of `TidyR7MonetarismValuation.valuation_iff_tvc_seq`. -/
theorem valuation_1_34_ito_seq (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) {T : ℕ → ℝ} (hT : ∀ k, s ≤ T k) :
    (∀ᵐ ω ∂μ, Tendsto (fun k => μ[flowIto134 μ 𝓕 Λ P M i im sp s (T k) | 𝓕 s] ω)
      atTop (𝓝 (disc Λ P s ω * addProc B M s ω))) ↔
      ∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => disc Λ P (T k) ω * addProc B M (T k) ω | 𝓕 s] ω)
        atTop (𝓝 0) :=
  valuation_iff_tvc_seq (Y := fun T ω => disc Λ P T ω * addProc B M T ω)
    (F := fun T => flowIto134 μ 𝓕 Λ P M i im sp s T)
    (fun _ hT => rec_1_34_ito hm hBM hWm h𝓕 hs hT) hT

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567: valuation iff transversality, `L¹` form,
verbatim with diffusive bonds.** If the flows `∫_s^T (Λs + (i − i^m)nM) du` converge in `L¹`
to an integrable `G`, then `n_s(B + M)_s = E_s[G]` a.s. iff
`E_s[n_T(B + M)_T] → 0` in `L¹`.
An instance of `TidyR7MonetarismValuation.valuation_iff_tvc_flow`; the analogue of
`TidyR7MonetarismValuation.MonetaryModel.valuation_1_34`. -/
theorem valuation_1_34_ito (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) {G : Ω → ℝ} (hG : Integrable G μ)
    (hconv : Tendsto (fun T => ∫ ω, |flowIto134 μ 𝓕 Λ P M i im sp s T ω - G ω| ∂μ)
      atTop (𝓝 0)) :
    (fun ω => disc Λ P s ω * addProc B M s ω) =ᵐ[μ] μ[G | 𝓕 s] ↔
      Tendsto (fun T => ∫ ω, |μ[fun ω => disc Λ P T ω * addProc B M T ω | 𝓕 s] ω| ∂μ) atTop
        (𝓝 0) := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  exact valuation_iff_tvc_flow (Y := fun T ω => disc Λ P T ω * addProc B M T ω)
    (F := fun T => flowIto134 μ 𝓕 Λ P M i im sp s T)
    (fun _ hT => rec_1_34_ito hm hBM hWm h𝓕 hs hT)
    (fun _ hT => integrable_nW hm hBM hWm h𝓕 hs hT)
    (fun _ hT => integrable_flow134 hm hBM hWm h𝓕 hs hT) hG hconv

end Cochrane.Monetarism.TidyR7MonetarismItoValuation
