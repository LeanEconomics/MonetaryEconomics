/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR7MonetarismItoValuation
import Monetarism.TidyR8MonetarismUISharp

/-!
# The dominated `E_t∫_t^∞` form of (1.33) with the bracket, for diffusive bonds

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.32)–(1.33), in the model
`TidyR7MonetarismIto.ItoMonetaryModel` (on every `[s, T]`, `T > s`, with fixed bounds, as in
`TidyR7MonetarismItoValuation`). That module proves the limit and `L¹` forms of (1.33) with the
bracket; here the dominated (printed) form `n_sB_s = E_s[∫_s^∞ …]` is proved.

## The abstract dominated form

`valuation_iff_tvc_dom_ae`: the dominated form of `TidyR7MonetarismValuation.valuation_iff_tvc_dom`
with almost-sure hypotheses (measurability, domination and convergence only a.s., as the
mean-square flows are defined up to null sets), via
`TidyR8MonetarismUISharp.ae_tendsto_condExp_of_dominated_ae`.
`valuation_1_33_ito_dom`: with the corrected flows
`F^c_T = ∫_s^T (Λs − i^m nM) du + ∫_s^T n dM − ∫_s^T σ_Xσ_B du`
(`TidyR7MonetarismItoValuation.flowItoC`) converging a.s. to `G` and dominated a.s. by an
integrable `H`: `n_sB_s = E_s[G]` a.s. iff the transversality condition.

## Verifiable hypotheses (`valuation_1_33_ito_dom_pathwise`)

The mean-square time integrals are pathwise integrals a.s. when the integrands have a.s.
continuous paths (`TidyR7ItoProducts.dtInt_ae_eq_integral`); so, with
* the drift flow `d = Λs − i^m nM + n m` (`flowDrift`) and the bracket density `σ_Xσ_B` a.s.
  continuous on `[s, ∞)` and integrable on `(s, ∞)` path by path, with
  `∫_s^∞ |d| + ∫_s^∞ |σ_Xσ_B| ≤ H₁` integrable, and
* the Itô part `J_k = ∫_s^{T_k} nσ_M dW` converging a.s. to `J` with `|J_k| ≤ H₂` integrable
  (for instance when money's diffusion vanishes after a date, `itoInt_eventually_const`),
the flows converge a.s. to `G = ∫_s^∞ d du + J − ∫_s^∞ σ_Xσ_B du` (`domLimit`), are dominated by
`H₁ + H₂`, and:
* `n_sB_s = E_s[G]` a.s. iff the transversality condition (the dominated (1.33) WITH the
  bracket);
* under the transversality condition, the book's dominated (1.33),
  `n_sB_s = E_s[∫_s^∞ d du + J]` (no bracket, `domLimitBook`), holds iff
  `E_s[∫_s^∞ σ_Xσ_B du] = 0` a.s.

Tools: `itoInt_add_itoInt_ms` (additivity of the Itô integral over intervals for mean-square
continuous integrands; generalises `TidyR7ItoIntegral.itoInt_add_itoInt`),
`itoInt_ae_zero_of_vanish`, `itoInt_eventually_const`, `abs_intervalIntegral_le_Ioi`.
-/

namespace Cochrane.Monetarism.TidyR8MonetarismItoDom

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoSums Cochrane.Monetarism.TidyR7ItoIntegral
  Cochrane.Monetarism.TidyR7ItoUnbounded Cochrane.Monetarism.TidyR7ItoProducts
  Cochrane.Monetarism.TidyR7ItoProcess Cochrane.Monetarism.TidyR7ItoBondStep
  Cochrane.Monetarism.TidyR7MonetarismModel Cochrane.Monetarism.TidyR7MonetarismIto
  Cochrane.Monetarism.TidyR7MonetarismValuation Cochrane.Monetarism.TidyR7MonetarismItoValuation
  Cochrane.Monetarism.TidyR8MonetarismUISharp
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ## The abstract dominated form with almost-sure hypotheses -/

/-- **Cochrane (2023), A1 §1.6, (1.33)–(1.34), p. 567: valuation iff transversality, dominated
form, almost-sure hypotheses.** If `Y_s = E_s[Y_T] + E_s[F_T]` for every `T ≥ s` and along
`T_k ≥ s` the flows are a.e. strongly measurable, `|F_{T_k}| ≤ H` a.s. with `H` integrable and
`F_{T_k} → G` a.s., then `Y_s = E_s[G]` a.s. iff `E_s[Y_{T_k}] → 0` a.s.
Generalises `TidyR7MonetarismValuation.valuation_iff_tvc_dom`. -/
theorem valuation_iff_tvc_dom_ae {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ℝ mΩ}
    {Y F : ℝ → Ω → ℝ} {s : ℝ}
    (hrec : ∀ T, s ≤ T → Y s =ᵐ[μ] μ[Y T | 𝓕 s] + μ[F T | 𝓕 s]) {T : ℕ → ℝ}
    (hT : ∀ k, s ≤ T k) {G H : Ω → ℝ} (hFm : ∀ k, AEStronglyMeasurable (F (T k)) μ)
    (hH : Integrable H μ) (hbd : ∀ k, ∀ᵐ ω ∂μ, |F (T k) ω| ≤ H ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun k => F (T k) ω) atTop (𝓝 (G ω))) :
    Y s =ᵐ[μ] μ[G | 𝓕 s] ↔ ∀ᵐ ω ∂μ, Tendsto (fun k => μ[Y (T k) | 𝓕 s] ω) atTop (𝓝 0) := by
  have hc := ae_tendsto_condExp_of_dominated_ae (𝓕.le s) hFm hH hbd hlim
  rw [← valuation_iff_tvc_seq hrec hT]
  constructor
  · intro h
    filter_upwards [h, hc] with ω h1 h2
    rwa [h1]
  · intro h
    filter_upwards [h, hc] with ω h1 h2
    exact tendsto_nhds_unique h1 h2

/-! ## Itô-integral tools -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: additivity over intervals for mean-square continuous
integrands**: `∫_s^t G dW = ∫_s^r G dW + ∫_r^t G dW` a.s. for `0 ≤ s ≤ r ≤ t`.
Generalises `TidyR7ItoIntegral.itoInt_add_itoInt` (bounded integrands); the proof is the same
with `TidyR7ItoUnbounded.L2Tendsto_itoSum_ms`. -/
theorem itoInt_add_itoInt_ms {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ}
    {G : ℝ → Ω → ℝ} (hB : IsPreBrownianReal W μ) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) {s r t : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hrt : r ≤ t)
    (hG : MSIntegrand μ 𝓕 G s t) :
    itoInt μ 𝓕 W G s t =ᵐ[μ] fun ω => itoInt μ 𝓕 W G s r ω + itoInt μ 𝓕 W G r t ω := by
  rcases hsr.lt_or_eq with hsr | hsr
  · rcases hrt.lt_or_eq with hrt | hrt
    · set ps : ℕ → Partition s t := fun k => concat (dyadic hsr k) (dyadic hrt k) with hps_def
      have hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0) := by
        refine squeeze_zero (fun k => mesh_nonneg _) (fun k => mesh_concat_le _ _) ?_
        simpa using (tendsto_mesh_dyadic hsr).max (tendsto_mesh_dyadic hrt)
      have h1 := L2Tendsto_itoSum_ms hB hW h𝓕 hs (hsr.trans hrt) hG ps hps
      have h2 := ((L2Tendsto_dyadic_ms hB hW h𝓕 hs hsr (hG.mono le_rfl hrt.le)).add
        (L2Tendsto_dyadic_ms hB hW h𝓕 (hs.trans hsr.le) hrt (hG.mono hsr.le le_rfl))).congr_seq
          (fun k => ae_of_all _ fun ω => (itoSum_concat G _ _ ω).symm)
      exact ae_eq_of_L2Tendsto h1 h2
    · have e : itoInt μ 𝓕 W G r t = 0 := itoInt_of_le hrt.ge
      refine ae_of_all _ fun ω => ?_
      rw [e, ← hrt]
      simp
  · have e : itoInt μ 𝓕 W G s r = 0 := itoInt_of_le hsr.ge
    refine ae_of_all _ fun ω => ?_
    rw [e, ← hsr]
    simp

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the Itô integral of an integrand vanishing on
`[r, t]` is `0` a.s.** (every left-point sum is `0`). -/
theorem itoInt_ae_zero_of_vanish {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ}
    {G : ℝ → Ω → ℝ} {r t : ℝ} (hG0 : ∀ u ∈ Set.Icc r t, ∀ ω, G u ω = 0) :
    itoInt μ 𝓕 W G r t =ᵐ[μ] 0 := by
  rcases lt_or_ge r t with hrt | htr
  · have e : ∀ k, itoSum W G (dyadic hrt k) = 0 := fun k => funext fun ω => by
      unfold itoSum
      exact Finset.sum_eq_zero fun i hi => by
        simp only [hG0 _ (t_mem _ (Finset.mem_range.1 hi).le) ω, zero_mul]
    have hL : L2Tendsto μ (fun k => itoSum W G (dyadic hrt k)) 0 :=
      ⟨fun k => by change MemLp (itoSum W G (dyadic hrt k)) 2 μ; rw [e k]; exact MemLp.zero,
        MemLp.zero, by simp [e]⟩
    exact ae_eq_of_L2Tendsto (itoInt_spec hrt ⟨0, stronglyMeasurable_zero, hL⟩).2 hL
  · rw [itoInt_of_le htr]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: an Itô integral whose integrand vanishes after
`T*` is constant after `T*`**: `∫_s^T G dW = ∫_s^{T*} G dW` a.s. for `0 ≤ s ≤ T* ≤ T`. -/
theorem itoInt_eventually_const {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ}
    {G : ℝ → Ω → ℝ} (hB : IsPreBrownianReal W μ) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) {s Ts T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ Ts) (hTT : Ts ≤ T)
    (hG : MSIntegrand μ 𝓕 G s T) (hG0 : ∀ u, Ts ≤ u → ∀ ω, G u ω = 0) :
    itoInt μ 𝓕 W G s T =ᵐ[μ] itoInt μ 𝓕 W G s Ts := by
  filter_upwards [itoInt_add_itoInt_ms hB hW h𝓕 hs hsT hTT hG,
    itoInt_ae_zero_of_vanish (μ := μ) (𝓕 := 𝓕) (W := W) (r := Ts) (t := T)
      (fun u hu ω => hG0 u hu.1 ω)] with ω h1 h2
  rw [h1, h2, Pi.zero_apply, add_zero]

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567 (tool): `|∫_s^T f| ≤ ∫_s^∞ |f|` for `s ≤ T` and `f`
integrable on `(s, ∞)`. -/
theorem abs_intervalIntegral_le_Ioi {f : ℝ → ℝ} {s T : ℝ} (hsT : s ≤ T)
    (hf : IntegrableOn f (Set.Ioi s)) : |∫ u in s..T, f u| ≤ ∫ u in Set.Ioi s, |f u| := by
  rw [intervalIntegral.integral_of_le hsT]
  calc |∫ u in Set.Ioc s T, f u| ≤ ∫ u in Set.Ioc s T, |f u| := abs_integral_le_integral_abs
    _ ≤ ∫ u in Set.Ioi s, |f u| :=
      setIntegral_mono_set hf.abs (ae_of_all _ fun _ => abs_nonneg _)
        Set.Ioc_subset_Ioi_self.eventuallyLE

/-! ## The flows of (1.33) path by path -/

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: **the drift flow** `d = Λs − i^m nM + n m`, the
density of the time integrals in `F^c` (`n = Λ/P`, `m` money's drift). -/
noncomputable def flowDrift (Λ P M im sp m : ℝ → Ω → ℝ) (u : ℝ) (ω : Ω) : ℝ :=
  (Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω) + disc Λ P u ω * m u ω

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: **the bracket to infinity**
`∫_s^∞ σ_Xσ_B du`, path by path. -/
noncomputable def bracketInf (σX σB : ℝ → Ω → ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  ∫ u in Set.Ioi s, σX u ω * σB u ω

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: **the corrected flow to infinity**
`G = ∫_s^∞ d du + J − ∫_s^∞ σ_Xσ_B du`, `J = lim ∫_s^{T_k} nσ_M dW`. -/
noncomputable def domLimit (Λ P M im sp m σX σB : ℝ → Ω → ℝ) (s : ℝ) (J : Ω → ℝ) (ω : Ω) : ℝ :=
  (∫ u in Set.Ioi s, flowDrift Λ P M im sp m u ω) + J ω - bracketInf σX σB s ω

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: **the book's flow to infinity** (no bracket)
`∫_s^∞ d du + J`. -/
noncomputable def domLimitBook (Λ P M im sp m : ℝ → Ω → ℝ) (s : ℝ) (J : Ω → ℝ) (ω : Ω) : ℝ :=
  (∫ u in Set.Ioi s, flowDrift Λ P M im sp m u ω) + J ω

variable {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ} {s : ℝ}
  {Λ P B M i im sp β σB m σM σX : ℝ → Ω → ℝ} {Cn CX Cβ CB Cm CM : ℝ}

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: the book's flow to infinity is the corrected one
plus the bracket to infinity. -/
theorem domLimitBook_eq (J : Ω → ℝ) (ω : Ω) :
    domLimitBook Λ P M im sp m s J ω =
      domLimit Λ P M im sp m σX σB s J ω + bracketInf σX σB s ω := by
  simp only [domLimitBook, domLimit]
  ring

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the corrected flow path by path.** On `[s, T]`,
`s < T`, in the model on `[s, T]` with `0 ≤ s`, and with `Λs − i^m nM` and `n m` having a.s.
continuous paths: a.s.
`F^c_T = ∫_s^T d du + ∫_s^T nσ_M dW − ∫_s^T σ_Xσ_B du`, the time integrals pathwise
(`TidyR7ItoProducts.dtInt_ae_eq_integral`). -/
theorem flowItoC_pathwise {T : ℝ} (hsT : s < T)
    (h : ItoMonetaryModel μ 𝓕 W Λ P B M i im sp β σB m σM σX s T Cn CX Cβ CB Cm CM)
    (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration μ W 𝓕)
    (hs : 0 ≤ s)
    (hc1 : ∀ᵐ ω ∂μ, ContinuousOn (fun u => Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω)
      (Set.Icc s T))
    (hc2 : ∀ᵐ ω ∂μ, ContinuousOn (fun u => disc Λ P u ω * m u ω) (Set.Icc s T)) :
    flowItoC μ 𝓕 W Λ P M im sp m σM σX σB s T =ᵐ[μ] fun ω =>
      (∫ u in s..T, flowDrift Λ P M im sp m u ω) +
        itoInt μ 𝓕 W (fun u ω => disc Λ P u ω * σM u ω) s T ω -
          ∫ u in s..T, σX u ω * σB u ω := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have hn := h.disc_ito
  have hb := h.bonds_ito
  have hM := h.money_ito
  have nMS := hn.toMS hBM hWm h𝓕 hs
  have bMS := hb.toMS hBM hWm h𝓕 hs
  have G := MSIntegrand.add (MSIntegrand.add (MSIntegrand.mul_itoIntegrand bMS hn.drift)
    (MSIntegrand.mul_itoIntegrand nMS hb.drift)) (MSIntegrand.mul_itoIntegrand nMS hM.drift)
  have e : (fun u ω => Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω) =
      fun u ω => -1 * (B u ω * -(i u ω * disc Λ P u ω) + disc Λ P u ω * β u ω
        + disc Λ P u ω * m u ω) := funext fun u => funext fun ω => h.rate_1_32 u ω
  have hg1 : MSIntegrand μ 𝓕 (fun u ω => Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω) s T := by
    rw [e]
    exact MSIntegrand.const_mul G (-1)
  have hg2 : MSIntegrand μ 𝓕 (fun u ω => disc Λ P u ω * m u ω) s T :=
    MSIntegrand.mul_itoIntegrand nMS hM.drift
  have d1 := dtInt_ae_eq_integral hsT.le hg1 hc1
  have d2 := dtInt_ae_eq_integral hsT.le hg2 hc2
  filter_upwards [d1, d2, hc1, hc2] with ω e1 e2 c1 c2
  have i1 : IntervalIntegrable (fun u => Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω)
      MeasureSpace.volume s T := c1.intervalIntegrable_of_Icc hsT.le
  have i2 : IntervalIntegrable (fun u => disc Λ P u ω * m u ω) MeasureSpace.volume s T :=
    c2.intervalIntegrable_of_Icc hsT.le
  simp only [flowItoC, flowItoBook, moneyInt, intIto, bracket, flowDrift]
  rw [e1, e2, intervalIntegral.integral_add i1 i2]
  ring

variable (hm : ∀ T, s < T →
  ItoMonetaryModel μ 𝓕 W Λ P B M i im sp β σB m σM σX s T Cn CX Cβ CB Cm CM)
include hm

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the dominated form of (1.33) with the
bracket.** Along times `T_k ≥ s`, if the corrected flows
`F^c_{T_k} = ∫_s^{T_k} (Λs − i^m nM) du + ∫_s^{T_k} n dM − ∫_s^{T_k} σ_Xσ_B du` converge a.s. to
`G` and `|F^c_{T_k}| ≤ H` a.s. with `H` integrable, then `n_sB_s = E_s[G]` a.s. iff
`E_s[n_{T_k}B_{T_k}] → 0` a.s.
The dominated companion of `TidyR7MonetarismItoValuation.valuation_1_33_ito` (`L¹` form);
an instance of `valuation_iff_tvc_dom_ae`. -/
theorem valuation_1_33_ito_dom (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) {T : ℕ → ℝ} (hT : ∀ k, s ≤ T k) {G H : Ω → ℝ}
    (hH : Integrable H μ)
    (hbd : ∀ k, ∀ᵐ ω ∂μ, |flowItoC μ 𝓕 W Λ P M im sp m σM σX σB s (T k) ω| ≤ H ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun k => flowItoC μ 𝓕 W Λ P M im sp m σM σX σB s (T k) ω) atTop
      (𝓝 (G ω))) :
    (fun ω => disc Λ P s ω * B s ω) =ᵐ[μ] μ[G | 𝓕 s] ↔
      ∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => disc Λ P (T k) ω * B (T k) ω | 𝓕 s] ω) atTop
        (𝓝 0) := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  exact valuation_iff_tvc_dom_ae (Y := fun T ω => disc Λ P T ω * B T ω)
    (F := fun T => flowItoC μ 𝓕 W Λ P M im sp m σM σX σB s T)
    (fun _ hT => rec_1_33_ito hm hBM hWm h𝓕 hs hT) hT
    (fun k => (integrable_flows hm hBM hWm h𝓕 hs (hT k)).2.2.aestronglyMeasurable) hH hbd hlim

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the dominated (1.33) with the bracket under
verifiable hypotheses.** Let `0 ≤ s < T_k → ∞`; let `Λs − i^m nM` and `n m` have a.s. continuous
paths on `[s, ∞)`; let path by path the drift flow `d` (`flowDrift`) and `σ_Xσ_B` be integrable
on `(s, ∞)` with `∫_s^∞ |d| + ∫_s^∞ |σ_Xσ_B| ≤ H₁` a.s., `H₁` integrable; let the Itô part
`J_k = ∫_s^{T_k} nσ_M dW` converge a.s. to `J` with `|J_k| ≤ H₂` a.s., `H₂` integrable. Then:
(i) the corrected flows converge a.s. to `G = ∫_s^∞ d + J − ∫_s^∞ σ_Xσ_B` (`domLimit`);
(ii) `|F^c_{T_k}| ≤ H₁ + H₂` a.s.;
(iii) `n_sB_s = E_s[G]` a.s. iff the transversality condition `E_s[n_{T_k}B_{T_k}] → 0` a.s.;
(iv) under the transversality condition the book's dominated (1.33),
`n_sB_s = E_s[∫_s^∞ d + J]` (`domLimitBook`), holds iff `E_s[∫_s^∞ σ_Xσ_B du] = 0` a.s.
Part (iv) is the dominated analogue of `TidyR7MonetarismItoValuation.valuation_1_33_ito_book_iff`.
-/
theorem valuation_1_33_ito_dom_pathwise (hBM : IsPreBrownianReal W μ)
    (hWm : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) {T : ℕ → ℝ}
    (hT : ∀ k, s < T k) (hTt : Tendsto T atTop atTop)
    (hc1 : ∀ᵐ ω ∂μ, ContinuousOn (fun u => Λ u ω * sp u ω - im u ω * disc Λ P u ω * M u ω)
      (Set.Ici s))
    (hc2 : ∀ᵐ ω ∂μ, ContinuousOn (fun u => disc Λ P u ω * m u ω) (Set.Ici s))
    (hi : ∀ᵐ ω ∂μ, IntegrableOn (fun u => flowDrift Λ P M im sp m u ω) (Set.Ioi s) ∧
      IntegrableOn (fun u => σX u ω * σB u ω) (Set.Ioi s))
    {H₁ : Ω → ℝ} (hH₁ : Integrable H₁ μ)
    (hH₁b : ∀ᵐ ω ∂μ, (∫ u in Set.Ioi s, |flowDrift Λ P M im sp m u ω|) +
      (∫ u in Set.Ioi s, |σX u ω * σB u ω|) ≤ H₁ ω)
    {J H₂ : Ω → ℝ} (hH₂ : Integrable H₂ μ)
    (hJ : ∀ᵐ ω ∂μ, Tendsto (fun k => itoInt μ 𝓕 W (fun u ω => disc Λ P u ω * σM u ω) s (T k) ω)
      atTop (𝓝 (J ω)))
    (hJb : ∀ k, ∀ᵐ ω ∂μ, |itoInt μ 𝓕 W (fun u ω => disc Λ P u ω * σM u ω) s (T k) ω| ≤ H₂ ω) :
    (∀ᵐ ω ∂μ, Tendsto (fun k => flowItoC μ 𝓕 W Λ P M im sp m σM σX σB s (T k) ω) atTop
      (𝓝 (domLimit Λ P M im sp m σX σB s J ω))) ∧
    (∀ k, ∀ᵐ ω ∂μ, |flowItoC μ 𝓕 W Λ P M im sp m σM σX σB s (T k) ω| ≤ H₁ ω + H₂ ω) ∧
    ((fun ω => disc Λ P s ω * B s ω) =ᵐ[μ] μ[domLimit Λ P M im sp m σX σB s J | 𝓕 s] ↔
      ∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => disc Λ P (T k) ω * B (T k) ω | 𝓕 s] ω) atTop
        (𝓝 0)) ∧
    ((∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => disc Λ P (T k) ω * B (T k) ω | 𝓕 s] ω) atTop
        (𝓝 0)) →
      ((fun ω => disc Λ P s ω * B s ω) =ᵐ[μ] μ[domLimitBook Λ P M im sp m s J | 𝓕 s] ↔
        μ[bracketInf σX σB s | 𝓕 s] =ᵐ[μ] 0)) := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have hpw : ∀ᵐ ω ∂μ, ∀ k, flowItoC μ 𝓕 W Λ P M im sp m σM σX σB s (T k) ω =
      (∫ u in s..T k, flowDrift Λ P M im sp m u ω) +
        itoInt μ 𝓕 W (fun u ω => disc Λ P u ω * σM u ω) s (T k) ω -
          ∫ u in s..T k, σX u ω * σB u ω :=
    ae_all_iff.2 fun k => by
      filter_upwards [flowItoC_pathwise (hT k) (hm (T k) (hT k)) hBM hWm h𝓕 hs
        (by filter_upwards [hc1] with ω h; exact h.mono Set.Icc_subset_Ici_self)
        (by filter_upwards [hc2] with ω h; exact h.mono Set.Icc_subset_Ici_self)] with ω h
      exact h
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun k => flowItoC μ 𝓕 W Λ P M im sp m σM σX σB s (T k) ω) atTop
      (𝓝 (domLimit Λ P M im sp m σX σB s J ω)) := by
    filter_upwards [hpw, hi, hJ] with ω h1 h2 h3
    have := ((intervalIntegral_tendsto_integral_Ioi s h2.1 hTt).add h3).sub
      (intervalIntegral_tendsto_integral_Ioi s h2.2 hTt)
    exact this.congr fun k => (h1 k).symm
  have hbd : ∀ k, ∀ᵐ ω ∂μ,
      |flowItoC μ 𝓕 W Λ P M im sp m σM σX σB s (T k) ω| ≤ H₁ ω + H₂ ω := fun k => by
    filter_upwards [hpw, hi, hH₁b, hJb k] with ω h1 h2 h3 h4
    rw [h1 k]
    have a1 := abs_intervalIntegral_le_Ioi (hT k).le h2.1
    have a2 := abs_intervalIntegral_le_Ioi (hT k).le h2.2
    calc |(∫ u in s..T k, flowDrift Λ P M im sp m u ω) +
          itoInt μ 𝓕 W (fun u ω => disc Λ P u ω * σM u ω) s (T k) ω -
            ∫ u in s..T k, σX u ω * σB u ω|
        ≤ |∫ u in s..T k, flowDrift Λ P M im sp m u ω| +
            |itoInt μ 𝓕 W (fun u ω => disc Λ P u ω * σM u ω) s (T k) ω| +
            |∫ u in s..T k, σX u ω * σB u ω| := by
          refine (abs_sub _ _).trans ?_
          exact add_le_add_left (abs_add_le _ _) _
      _ ≤ H₁ ω + H₂ ω := by linarith
  have hval := valuation_1_33_ito_dom hm hBM hWm h𝓕 hs (fun k => (hT k).le)
    (hH₁.add hH₂) hbd hlim
  refine ⟨hlim, hbd, hval, fun htvc => ?_⟩
  have hv := hval.2 htvc
  -- integrability of the limits
  have hFm : ∀ k, AEStronglyMeasurable (flowItoC μ 𝓕 W Λ P M im sp m σM σX σB s (T k)) μ :=
    fun k => (integrable_flows hm hBM hWm h𝓕 hs (hT k).le).2.2.aestronglyMeasurable
  have hGi : Integrable (domLimit Λ P M im sp m σX σB s J) μ := by
    refine (hH₁.add hH₂).mono' (aestronglyMeasurable_of_tendsto_ae atTop hFm hlim) ?_
    filter_upwards [hlim, ae_all_iff.2 hbd] with ω h1 h2
    rw [Real.norm_eq_abs]
    exact le_of_tendsto' h1.abs fun k => h2 k
  have hbrlim : ∀ᵐ ω ∂μ, Tendsto (fun k => bracket σX σB s (T k) ω) atTop
      (𝓝 (bracketInf σX σB s ω)) := by
    filter_upwards [hi] with ω h
    exact intervalIntegral_tendsto_integral_Ioi s h.2 hTt
  have hBi : Integrable (bracketInf σX σB s) μ := by
    refine hH₁.mono' (aestronglyMeasurable_of_tendsto_ae atTop (fun k =>
      (integrable_flows hm hBM hWm h𝓕 hs (hT k).le).2.1.aestronglyMeasurable) hbrlim) ?_
    filter_upwards [hi, hH₁b] with ω h1 h2
    rw [Real.norm_eq_abs]
    have a1 : |bracketInf σX σB s ω| ≤ ∫ u in Set.Ioi s, |σX u ω * σB u ω| :=
      abs_integral_le_integral_abs
    have a2 : 0 ≤ ∫ u in Set.Ioi s, |flowDrift Λ P M im sp m u ω| :=
      integral_nonneg fun _ => abs_nonneg _
    linarith
  have heq : domLimitBook Λ P M im sp m s J =
      domLimit Λ P M im sp m σX σB s J + bracketInf σX σB s :=
    funext fun ω => domLimitBook_eq J ω
  have hadd := condExp_add hGi hBi (𝓕 s)
  rw [heq]
  constructor
  · intro h
    filter_upwards [h, hv, hadd] with ω h1 h2 h3
    rw [h3, Pi.add_apply, ← h2] at h1
    simp only [Pi.zero_apply]
    linarith
  · intro h
    filter_upwards [h, hv, hadd] with ω h1 h2 h3
    rw [h3, Pi.add_apply, ← h2, h1, Pi.zero_apply, add_zero]

end Cochrane.Monetarism.TidyR8MonetarismItoDom
