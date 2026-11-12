/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.TidyR7ItoDiscountFactorCex

/-!
# A1.4 in real terms: `B_t/P_t = E_t∫_t^∞ (Λ_τ/Λ_t) s_τ dτ` with an Itô discount factor

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1.4, pp. 564–565
("work either up or down"): with short-term debt, the chain
`B_t/P_t = E_t∫_t^∞ (Λ_τ/Λ_t)s_τ dτ` ⇔ `Λ_tB_t/P_t = E_t∫_t^∞ Λ_τs_τ dτ` ⇔
`d(Λ_tB_t/P_t) = −s_tΛ_t dt` ⇔ … ⇔ the flow `B_ti_t dt = P_ts_t dt + dB_t`, and (3.31)–(3.32),
p. 74. `TidyR7ItoDiscountFactor.shortDebt_model` and `TidyR7ItoDiscountFactor.ItoDiscountModel`
gave the nominal form `Λ_tB_t/P_t = E_t∫Λs` (with `n = Λ/P` the nominal discount factor)
iff the transversality condition. This module adds the first, **real** line: dividing by
`Λ_t`.

## Positivity is a hypothesis

The results assume only `Λ_t = n_tP_t ≠ 0` almost surely, which is all the division needs. A
positive, fully diffusive discount factor satisfying every hypothesis is built later with Itô's
formula (`TidyR9PositiveRealForm.realForm_positive`).

## Integrability is a hypothesis too, and it is genuine

`E_t[G/Λ_t]` is a conditional expectation only if `G/Λ_t` is integrable; when it is not, the
book's `E_t∫(Λ_τ/Λ_t)s_τdτ` must be read as `Λ_t^{-1}E_t∫Λ_τs_τdτ` (a generalised conditional
expectation of a `𝓕_t`-multiple). The results state that integrability (`hGΛ`).

## Main results

* `realForm_iff` (general): for `L` `m`-measurable, `L ≠ 0` a.s., `G` and `G/L` integrable,
  `L·Y = E[G | m]` a.s. iff `Y = E[G/L | m]` a.s. (pull-out property);
* `shortDebt_realForm` (**A1.4, first line, `L¹` form**): on the short-debt model of
  `TidyR7ItoDiscountFactor.shortDebt_model` on every `[s, T]`, with `∫_s^T n(Ps) du → G` in `L¹`,
  `B_s/P_s = E_s[G/Λ_s]` a.s. iff the transversality condition `E_s[n_TB_T] → 0` in `L¹`;
* `shortDebt_realForm_integral`: the same with `G = ∫_s^∞ Λ_u s_u du` pathwise, so
  `B_s/P_s = E_s[∫_s^∞ (Λ_u/Λ_s)s_u du]` verbatim;
* non-vacuity, `cosEconomy_realForm` (any Brownian motion) and `bmPath_cosEconomy_realForm`
  (the constructed one): an economy on the constructed Brownian motion with a
  **random** `𝓕_s`-measurable discount factor `Λ_s = 2 + cos W_s` (so `1 ≤ Λ_s ≤ 3`),
  `Λ_u = Λ_se^{−r(u−s)}`, `P = 1`, `i = r`, `s = 1`, `B = 1/r`, satisfying every hypothesis,
  the transversality condition, and the real form `B_s/P_s = 1/r`.
-/

namespace Cochrane.Generality.TidyR8ShortDebtRealForm

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Generality.TidyR7StieltjesSums Cochrane.Generality.TidyR7BrownianTools
  Cochrane.Generality.TidyR7BrownianQV Cochrane.Generality.TidyR7ItoL2
  Cochrane.Generality.TidyR7ItoSums Cochrane.Generality.TidyR7ItoIntegral
  Cochrane.Generality.TidyR7ItoUnbounded Cochrane.Generality.TidyR7ItoProducts
  Cochrane.Generality.TidyR7ItoProcess Cochrane.Generality.TidyR7ItoProductRule
  Cochrane.Generality.TidyR7ItoBondStep Cochrane.Generality.TidyR7ItoBridge
  Cochrane.Generality.TidyR7BrownianExist Cochrane.Generality.TidyR7BrownianSchauder
  Cochrane.Generality.TidyR7ItoDiscountFactor Cochrane.Generality.TidyR7ItoDiscountFactorCex
open scoped ENNReal NNReal

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ## Dividing a conditional expectation by an `𝓕_t`-measurable factor -/

/-- **Cochrane (2023), A1.4, p. 564 (`B_t/P_t = E_t∫(Λ_τ/Λ_t)s` ⇔ `Λ_tB_t/P_t = E_t∫Λs`):
dividing by the discount factor.** For `L` `m`-measurable with
`L ≠ 0` a.s., and `G`, `G/L` integrable: `L·Y = E[G | m]` a.s. iff `Y = E[G/L | m]` a.s.
Mathlib `condExp_mul_of_stronglyMeasurable_left` (pull-out). -/
theorem realForm_iff {L Y G : Ω → ℝ}
    (hL : StronglyMeasurable[m] L) (hL0 : ∀ᵐ ω ∂μ, L ω ≠ 0) (hG : Integrable G μ)
    (hGL : Integrable (fun ω => G ω / L ω) μ) :
    (fun ω => L ω * Y ω) =ᵐ[μ] μ[G | m] ↔ Y =ᵐ[μ] μ[fun ω => G ω / L ω | m] := by
  have hLi : StronglyMeasurable[m] (fun ω => (L ω)⁻¹) :=
    (hL.measurable.inv).stronglyMeasurable
  have e : (fun ω => G ω / L ω) = (fun ω => (L ω)⁻¹) * G := by
    funext ω
    simp only [Pi.mul_apply]
    ring
  have hpull : μ[fun ω => G ω / L ω | m] =ᵐ[μ] fun ω => (L ω)⁻¹ * μ[G | m] ω := by
    rw [e]
    filter_upwards [condExp_mul_of_stronglyMeasurable_left hLi (e ▸ hGL) hG] with ω h
    rw [h, Pi.mul_apply]
  constructor
  · intro h
    filter_upwards [h, hpull, hL0] with ω h1 h2 h3
    rw [h2, ← h1]
    field_simp
  · intro h
    filter_upwards [h, hpull, hL0] with ω h1 h2 h3
    rw [h1, h2]
    field_simp

variable {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ} {s : ℝ}

/-- **Cochrane (2023), A1.4, pp. 564–565: short-term debt in real terms, `L¹` form.** Let the
nominal discount factor `n = Λ/P` (drift `−i n`, diffusion `σ_n`) and nominal debt `B`
(`dB = (iB − Ps)dt`) be Itô processes on every `[s, T]`, `P_s` `𝓕_s`-measurable, and
`Λ_s = n_sP_s ≠ 0` a.s. If `∫_s^T n(Ps) du → G` in `L¹` with `G` and `G/Λ_s` integrable, then
`B_s/P_s = E_s[G/Λ_s]` a.s. iff the transversality condition `E_s[n_TB_T] → 0` in `L¹`.
`TidyR7ItoDiscountFactor.ItoDiscountModel.valuation_L1` and `realForm_iff`. -/
theorem shortDebt_realForm {n B P i sp σn : ℝ → Ω → ℝ} {Cν Cn Cβ : ℝ → ℝ}
    (hn : ∀ T, s < T → ItoProcess μ 𝓕 W n (fun u ω => -(i u ω * n u ω)) σn s T (Cν T) (Cn T))
    (hB : ∀ T, s < T → ItoProcess μ 𝓕 W B (fun u ω => i u ω * B u ω - P u ω * sp u ω)
      (fun _ _ => 0) s T (Cβ T) 0)
    (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration μ W 𝓕)
    (hs : 0 ≤ s) (hP : StronglyMeasurable[𝓕 s] (P s)) (hΛ : ∀ᵐ ω ∂μ, n s ω * P s ω ≠ 0)
    {G : Ω → ℝ} (hG : Integrable G μ) (hGΛ : Integrable (fun ω => G ω / (n s ω * P s ω)) μ)
    (hconv : Tendsto (fun T => ∫ ω, |dtInt μ 𝓕 (fun u ω => n u ω * (P u ω * sp u ω)) s T ω
      - G ω| ∂μ) atTop (𝓝 0)) :
    (fun ω => B s ω / P s ω) =ᵐ[μ] μ[fun ω => G ω / (n s ω * P s ω) | 𝓕 s] ↔
      Tendsto (fun T => ∫ ω, |μ[fun ω => n T ω * B T ω | 𝓕 s] ω| ∂μ) atTop (𝓝 0) := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have hm : ∀ T, s < T → ItoDiscountModel μ 𝓕 W n B (fun u ω => -(i u ω * n u ω)) σn
      (fun u ω => i u ω * B u ω - P u ω * sp u ω) (fun _ _ => 0) (fun u ω => P u ω * sp u ω)
      s T (Cν T) (Cn T) (Cβ T) ((fun _ => (0 : ℝ)) T) :=
    fun T hT => shortDebt_model (hn T hT) (hB T hT)
  rw [← ItoDiscountModel.valuation_L1 hm hBM hWm h𝓕 hs hG hconv]
  have hns : StronglyMeasurable[𝓕 s] (n s) :=
    (hn (s + 1) (by linarith)).adapted s ⟨le_rfl, by linarith⟩
  rw [← realForm_iff (L := fun ω => n s ω * P s ω) (Y := fun ω => B s ω / P s ω)
    (by exact hns.mul hP) hΛ hG hGΛ]
  have hcongr : (fun ω => n s ω * P s ω * (B s ω / P s ω)) =ᵐ[μ] fun ω => n s ω * B s ω := by
    filter_upwards [hΛ] with ω h
    have hP0 : P s ω ≠ 0 := right_ne_zero_of_mul h
    field_simp
  exact ⟨fun h => hcongr.symm.trans h, fun h => hcongr.trans h⟩

/-- **Cochrane (2023), A1.4, p. 564, verbatim: `B_t/P_t = E_t∫_t^∞ (Λ_τ/Λ_t)s_τ dτ`.** Under the
hypotheses of `shortDebt_realForm` with `G = ∫_s^∞ Λ_u s_u du` (`Λ = nP`) pathwise: a.s.
`B_s/P_s = E_s[∫_s^∞ (Λ_u/Λ_s) s_u du]` iff the transversality condition. -/
theorem shortDebt_realForm_integral {n B P i sp σn : ℝ → Ω → ℝ} {Cν Cn Cβ : ℝ → ℝ}
    (hn : ∀ T, s < T → ItoProcess μ 𝓕 W n (fun u ω => -(i u ω * n u ω)) σn s T (Cν T) (Cn T))
    (hB : ∀ T, s < T → ItoProcess μ 𝓕 W B (fun u ω => i u ω * B u ω - P u ω * sp u ω)
      (fun _ _ => 0) s T (Cβ T) 0)
    (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration μ W 𝓕)
    (hs : 0 ≤ s) (hP : StronglyMeasurable[𝓕 s] (P s)) (hΛ : ∀ᵐ ω ∂μ, n s ω * P s ω ≠ 0)
    (hG : Integrable (fun ω => ∫ u in Set.Ioi s, n u ω * P u ω * sp u ω) μ)
    (hGΛ : Integrable (fun ω => ∫ u in Set.Ioi s, n u ω * P u ω / (n s ω * P s ω) * sp u ω) μ)
    (hconv : Tendsto (fun T => ∫ ω, |dtInt μ 𝓕 (fun u ω => n u ω * (P u ω * sp u ω)) s T ω
      - ∫ u in Set.Ioi s, n u ω * P u ω * sp u ω| ∂μ) atTop (𝓝 0)) :
    (fun ω => B s ω / P s ω) =ᵐ[μ]
      μ[fun ω => ∫ u in Set.Ioi s, n u ω * P u ω / (n s ω * P s ω) * sp u ω | 𝓕 s] ↔
      Tendsto (fun T => ∫ ω, |μ[fun ω => n T ω * B T ω | 𝓕 s] ω| ∂μ) atTop (𝓝 0) := by
  have e : (fun ω => ∫ u in Set.Ioi s, n u ω * P u ω / (n s ω * P s ω) * sp u ω) =
      fun ω => (∫ u in Set.Ioi s, n u ω * P u ω * sp u ω) / (n s ω * P s ω) := by
    funext ω
    rw [← integral_div]
    congr 1
    funext u
    ring
  rw [e] at hGΛ ⊢
  exact shortDebt_realForm hn hB hBM hWm h𝓕 hs hP hΛ hG hGΛ hconv

/-! ## Non-vacuity: a random `𝓕_s`-measurable discount factor -/

/-- Cochrane (2023), A1.4, p. 564 (non-vacuity): the nominal discount factor of the example,
`n_u = (2 + cos W_s)e^{−r(u−s)}`, a random `𝓕_s`-measurable level `Λ_s = 2 + cos W_s ∈ [1, 3]`
discounted at the constant rate `i = r` (with `P = 1`, `Λ = n`). -/
noncomputable def cosLam (W : ℝ≥0 → Ω → ℝ) (r s u : ℝ) (ω : Ω) : ℝ :=
  (2 + Real.cos (bmReal W s ω)) * Real.exp (-(r * (u - s)))

/-- Cochrane (2023), A1.4, p. 564 (non-vacuity): `1 ≤ 2 + cos x ≤ 3`. -/
theorem cos_level_bounds (x : ℝ) : 1 ≤ 2 + Real.cos x ∧ 2 + Real.cos x ≤ 3 := by
  constructor <;> linarith [Real.neg_one_le_cos x, Real.cos_le_one x]

/-- Cochrane (2023), A1.4, p. 564 (non-vacuity): the level `2 + cos W_s` is `𝓕_s`-measurable. -/
theorem stronglyMeasurable_cos_level (h𝓕 : BMFiltration μ W 𝓕) (s : ℝ) :
    StronglyMeasurable[𝓕 s] fun ω => 2 + Real.cos (bmReal W s ω) :=
  (measurable_const.add (Real.continuous_cos.measurable.comp
    (h𝓕.adapted s).measurable)).stronglyMeasurable

/-- Cochrane (2023), A1.4, p. 564 (non-vacuity): on `[s, ∞)`, `|−r n_u| ≤ 3r` (`r ≥ 0`). -/
theorem abs_cosLam_drift_le {r : ℝ} (hr : 0 ≤ r) {u : ℝ} (hu : s ≤ u) (ω : Ω) :
    |-(r * cosLam W r s u ω)| ≤ 3 * r := by
  have hb := cos_level_bounds (bmReal W s ω)
  have he : Real.exp (-(r * (u - s))) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith)
  rw [abs_neg, abs_mul, abs_of_nonneg hr, cosLam, abs_mul, abs_of_pos (by linarith),
    abs_of_pos (Real.exp_pos _)]
  have : (2 + Real.cos (bmReal W s ω)) * Real.exp (-(r * (u - s))) ≤ 3 :=
    calc _ ≤ 3 * 1 := mul_le_mul hb.2 he (Real.exp_pos _).le (by norm_num)
      _ = 3 := by ring
  nlinarith

/-- Cochrane (2023), A1.4, (1.26), p. 564 (non-vacuity): `n = cosLam` is an Itô process on
`[s, T]` with drift `−i n` (`i = r`) and no diffusion.
Generalises `TidyR7ItoDiscountFactorCex.itoProcess_det` to a random `𝓕_s`-measurable level. -/
theorem itoProcess_cosLam (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) {r : ℝ} (hr : 0 ≤ r) {T : ℝ} (hsT : s ≤ T) :
    ItoProcess μ 𝓕 W (cosLam W r s) (fun u ω => -((fun _ _ => r) u ω * cosLam W r s u ω))
      (fun _ _ => 0) s T (3 * r) 0 := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have hc := stronglyMeasurable_cos_level h𝓕 s
  have had : ∀ u ∈ Set.Icc s T, StronglyMeasurable[𝓕 u] (cosLam W r s u) := fun u hu =>
    (hc.mono (𝓕.mono hu.1)).mul stronglyMeasurable_const
  have hcont : ∀ ω, Continuous fun u => cosLam W r s u ω := fun ω => by
    unfold cosLam
    fun_prop
  exact
    { adapted := had
      init := MemLp.of_bound ((had s ⟨le_rfl, hsT⟩).mono (𝓕.le s)).aestronglyMeasurable 3
        (ae_of_all _ fun ω => by
          have hb := cos_level_bounds (bmReal W s ω)
          simp only [cosLam, sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one,
            Real.norm_eq_abs]
          rw [abs_of_pos (by linarith)]
          exact hb.2)
      drift :=
        { adapted := fun u hu => by exact ((had u hu).const_mul r).neg
          bound := fun u hu ω => abs_cosLam_drift_le hr hu.1 ω
          cont := ae_of_all _ fun ω => ((hcont ω).const_mul r).neg.continuousOn }
      diff := itoIntegrand_const (c := fun _ => (0 : ℝ)) stronglyMeasurable_const
        (fun _ => by simp)
      eq := fun u hu => by
        filter_upwards [itoInt_const hBM hWm h𝓕 hs hu.1 (c := fun _ => (0 : ℝ))
          stronglyMeasurable_const (C := 0) (fun _ => by simp)] with ω hω
        rw [hω, zero_mul, add_zero]
        have hd : ∀ v, HasDerivAt (fun v => cosLam W r s v ω)
            (-(r * cosLam W r s v ω)) v := fun v => by
          unfold cosLam
          have h1 : HasDerivAt (fun v => -(r * (v - s))) (-(r * 1)) v :=
            (((hasDerivAt_id v).sub_const s).const_mul r).neg
          convert (h1.exp).const_mul (2 + Real.cos (bmReal W s ω)) using 1
          ring
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v)
          ((((hcont ω).const_mul r).neg).intervalIntegrable _ _)]
        ring }


/-- Cochrane (2023), A1.4, p. 564 (non-vacuity): the level `2 + cos W_s` is integrable. -/
theorem integrable_cos_level [IsFiniteMeasure μ] (h𝓕 : BMFiltration μ W 𝓕) (s : ℝ) :
    Integrable (fun ω => 2 + Real.cos (bmReal W s ω)) μ :=
  (MemLp.of_bound (p := 1) ((stronglyMeasurable_cos_level h𝓕 s).mono (𝓕.le s)
    ).aestronglyMeasurable 3 (ae_of_all _ fun ω => by
      have hb := cos_level_bounds (bmReal W s ω)
      rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
      exact hb.2)).integrable le_rfl

/-- Cochrane (2023), A1.4, p. 564 (non-vacuity): `K e^{−r(T−s)} → 0` as `T → ∞` (`r > 0`). -/
theorem tendsto_const_mul_exp_decay (K : ℝ) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    Tendsto (fun T => K * Real.exp (-(r * (T - s)))) atTop (𝓝 0) := by
  have h0 : Tendsto (fun T : ℝ => T - s) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-s) tendsto_id
  have h1 : Tendsto (fun T : ℝ => r * (T - s)) atTop atTop := h0.const_mul_atTop hr
  have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul K
  rw [mul_zero] at h2
  exact h2

/-- Cochrane (2023), A1.4, p. 564 (non-vacuity): `∫_s^T n_u du = Λ_s(1 − e^{−r(T−s)})/r` in
the example (`r ≠ 0`). -/
theorem integral_cosLam {r : ℝ} (hr : r ≠ 0) (T : ℝ) (ω : Ω) :
    ∫ u in s..T, cosLam W r s u ω * (1 * 1) =
      (2 + Real.cos (bmReal W s ω)) * (1 - Real.exp (-(r * (T - s)))) / r := by
  have hd : ∀ v, HasDerivAt (fun v => -(cosLam W r s v ω) / r) (cosLam W r s v ω * (1 * 1)) v :=
    fun v => by
      unfold cosLam
      have h1 : HasDerivAt (fun v => -(r * (v - s))) (-(r * 1)) v :=
        (((hasDerivAt_id v).sub_const s).const_mul r).neg
      convert (((h1.exp).const_mul (2 + Real.cos (bmReal W s ω))).neg).div_const r using 1
      field_simp
  have hc : Continuous fun u => cosLam W r s u ω * (1 * 1) := by
    unfold cosLam
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v) (hc.intervalIntegrable _ _)]
  simp only [cosLam, sub_self, mul_zero, neg_zero, Real.exp_zero]
  field_simp
  ring

/-- Cochrane (2023), A1.4, p. 564 (non-vacuity): `∫_s^∞ n_u du = Λ_s/r` for the example
(`r > 0`). -/
theorem integral_Ioi_cosLam {r : ℝ} (hr : 0 < r) (ω : Ω) :
    ∫ u in Set.Ioi s, cosLam W r s u ω * 1 * 1 = (2 + Real.cos (bmReal W s ω)) / r := by
  have e : ∀ u, cosLam W r s u ω * 1 * 1 =
      ((2 + Real.cos (bmReal W s ω)) * Real.exp (r * s)) * Real.exp (-r * u) := fun u => by
    rw [cosLam, mul_assoc _ (Real.exp (r * s)), ← Real.exp_add]
    ring_nf
  have hh : Real.exp (r * s) * Real.exp (-r * s) = 1 := by
    rw [← Real.exp_add]
    simp
  simp_rw [e]
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) s, mul_assoc, neg_div_neg_eq,
    ← mul_div_assoc, hh]
  ring

/-- **Cochrane (2023), A1.4, pp. 564–565 (non-vacuity of `shortDebt_realForm_integral`): an
economy with a random discount factor.** For a Brownian motion `W` with admissible filtration,
`0 ≤ s`, `r > 0`: the nominal discount factor `n_u = (2 + cos W_s)e^{−r(u−s)}` (`i = r`, no
diffusion), price level `P = 1`, surplus `s = 1` and debt `B = 1/r` (`dB = (iB − Ps)dt = 0`)
satisfy every hypothesis of `shortDebt_realForm_integral`, the transversality condition
`E_s[n_TB_T] → 0` in `L¹` holds, and so the real form
`B_s/P_s = 1/r = E_s[∫_s^∞ (Λ_u/Λ_s)s_u du]` holds, with `Λ_s = 2 + cos W_s` random. -/
theorem cosEconomy_realForm (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun T => ∫ ω, |μ[fun ω => cosLam W r s T ω * (fun _ _ => 1 / r) T ω | 𝓕 s] ω| ∂μ)
      atTop (𝓝 0) ∧
    (fun ω => (fun (_ : ℝ) (_ : Ω) => 1 / r) s ω / (fun (_ : ℝ) (_ : Ω) => (1 : ℝ)) s ω) =ᵐ[μ]
      μ[fun ω => ∫ u in Set.Ioi s, cosLam W r s u ω * (fun _ _ => (1 : ℝ)) u ω /
        (cosLam W r s s ω * (fun _ _ => (1 : ℝ)) s ω) * (fun _ _ => (1 : ℝ)) u ω | 𝓕 s] := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  set c : Ω → ℝ := fun ω => 2 + Real.cos (bmReal W s ω) with hcdef
  have hcm := stronglyMeasurable_cos_level h𝓕 s
  have hci := integrable_cos_level h𝓕 s
  have hcpos : ∀ ω, 0 < c ω := fun ω => by
    have := cos_level_bounds (bmReal W s ω); simp only [hcdef]; linarith
  have hn : ∀ T, s < T → ItoProcess μ 𝓕 W (cosLam W r s)
      (fun u ω => -((fun _ _ => r) u ω * cosLam W r s u ω)) (fun _ _ => 0) s T (3 * r) 0 :=
    fun T hT => itoProcess_cosLam hBM hWm h𝓕 hs hr.le hT.le
  have hB : ∀ T, s < T → ItoProcess μ 𝓕 W (fun _ _ => 1 / r)
      (fun u ω => (fun _ _ => r) u ω * (fun _ _ => 1 / r) u ω
        - (fun _ _ => (1 : ℝ)) u ω * (fun _ _ => (1 : ℝ)) u ω) (fun _ _ => 0) s T
      ((fun _ => |r * (1 / r) - 1 * 1|) T) 0 := fun T _ =>
    itoProcess_det hBM hWm h𝓕 hs (f := fun _ => 1 / r) (g := fun _ => r * (1 / r) - 1 * 1)
      continuousOn_const (fun _ _ => le_rfl) (fun u _ => by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        field_simp
        ring)
  have hns : ∀ T, StronglyMeasurable[𝓕 s] (cosLam W r s T) := fun T =>
    hcm.mul stronglyMeasurable_const
  have hnsi : ∀ T, Integrable (cosLam W r s T) μ := fun T => hci.mul_const _
  -- the transversality condition
  have htvc : Tendsto (fun T => ∫ ω, |μ[fun ω => cosLam W r s T ω * (fun _ _ => 1 / r) T ω
      | 𝓕 s] ω| ∂μ) atTop (𝓝 0) := by
    refine (tendsto_const_mul_exp_decay ((∫ ω, c ω ∂μ) / r) hr s).congr fun T => ?_
    have hce : μ[fun ω => cosLam W r s T ω * (fun _ _ => 1 / r) T ω | 𝓕 s] =
        fun ω => cosLam W r s T ω * (1 / r) :=
      condExp_of_stronglyMeasurable (𝓕.le s) (by exact (hns T).mul stronglyMeasurable_const)
        (by exact (hnsi T).mul_const _)
    symm
    rw [hce]
    have e : ∀ ω, |cosLam W r s T ω * (fun _ _ => 1 / r) T ω| =
        Real.exp (-(r * (T - s))) / r * c ω := fun ω => by
      simp only [cosLam, hcdef]
      rw [abs_of_pos (by have := hcpos ω; simp only [hcdef] at this; positivity)]
      ring
    simp_rw [e]
    rw [integral_const_mul]
    ring
  refine ⟨htvc, ?_⟩
  -- the hypotheses of `shortDebt_realForm_integral`
  have hΛ : ∀ᵐ ω ∂μ, cosLam W r s s ω * (fun _ _ => (1 : ℝ)) s ω ≠ 0 :=
    ae_of_all _ fun ω => by
      simp only [cosLam, sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
      exact (hcpos ω).ne'
  have eG : (fun ω => ∫ u in Set.Ioi s, cosLam W r s u ω * (fun _ _ => (1 : ℝ)) u ω *
      (fun _ _ => (1 : ℝ)) u ω) = fun ω => c ω / r := funext fun ω => integral_Ioi_cosLam hr ω
  have hG : Integrable (fun ω => ∫ u in Set.Ioi s, cosLam W r s u ω * (fun _ _ => (1 : ℝ)) u ω *
      (fun _ _ => (1 : ℝ)) u ω) μ := by
    rw [eG]; exact hci.div_const r
  have hGΛ : Integrable (fun ω => ∫ u in Set.Ioi s, cosLam W r s u ω * (fun _ _ => (1 : ℝ)) u ω
      / (cosLam W r s s ω * (fun _ _ => (1 : ℝ)) s ω) * (fun _ _ => (1 : ℝ)) u ω) μ := by
    refine (integrable_const (1 / r)).congr (ae_of_all _ fun ω => ?_)
    have e : ∀ u, cosLam W r s u ω * (fun _ _ => (1 : ℝ)) u ω /
        (cosLam W r s s ω * (fun _ _ => (1 : ℝ)) s ω) * (fun _ _ => (1 : ℝ)) u ω =
        cosLam W r s u ω * 1 * 1 / c ω := fun u => by
      simp only [cosLam, hcdef, sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
    have hcp := hcpos ω
    simp only [hcdef] at hcp
    simp only [e, integral_div, integral_Ioi_cosLam hr ω, hcdef]
    field_simp
  have hm : ∀ T, s < T → ItoDiscountModel μ 𝓕 W (cosLam W r s) (fun _ _ => 1 / r)
      (fun u ω => -((fun _ _ => r) u ω * cosLam W r s u ω)) (fun _ _ => 0)
      (fun u ω => (fun _ _ => r) u ω * (fun _ _ => 1 / r) u ω
        - (fun _ _ => (1 : ℝ)) u ω * (fun _ _ => (1 : ℝ)) u ω) (fun _ _ => 0)
      (fun u ω => (fun _ _ => (1 : ℝ)) u ω * (fun _ _ => (1 : ℝ)) u ω) s T (3 * r) 0
      ((fun _ => |r * (1 / r) - 1 * 1|) T) 0 := fun T hT => shortDebt_model (hn T hT) (hB T hT)
  have hconv : Tendsto (fun T => ∫ ω, |dtInt μ 𝓕 (fun u ω => cosLam W r s u ω *
      ((fun _ _ => (1 : ℝ)) u ω * (fun _ _ => (1 : ℝ)) u ω)) s T ω
      - ∫ u in Set.Ioi s, cosLam W r s u ω * (fun _ _ => (1 : ℝ)) u ω *
        (fun _ _ => (1 : ℝ)) u ω| ∂μ) atTop (𝓝 0) := by
    refine (tendsto_const_mul_exp_decay ((∫ ω, c ω ∂μ) / r) hr s).congr' ?_
    filter_upwards [eventually_gt_atTop s] with T hT
    have hd := dtInt_ae_eq_integral hT.le ((hm T hT).msIntegrand_lamSp hBM hWm h𝓕 hs)
      (ae_of_all _ fun ω => by unfold cosLam; fun_prop)
    have e : (fun ω => |dtInt μ 𝓕 (fun u ω => cosLam W r s u ω *
        ((fun _ _ => (1 : ℝ)) u ω * (fun _ _ => (1 : ℝ)) u ω)) s T ω
        - ∫ u in Set.Ioi s, cosLam W r s u ω * (fun _ _ => (1 : ℝ)) u ω *
          (fun _ _ => (1 : ℝ)) u ω|) =ᵐ[μ]
        fun ω => Real.exp (-(r * (T - s))) / r * c ω := by
      filter_upwards [hd] with ω hω
      rw [hω, integral_cosLam hr.ne' T ω, integral_Ioi_cosLam hr ω]
      have hcp := hcpos ω
      simp only [hcdef] at hcp ⊢
      rw [show (2 + Real.cos (bmReal W s ω)) * (1 - Real.exp (-(r * (T - s)))) / r
          - (2 + Real.cos (bmReal W s ω)) / r =
          -(Real.exp (-(r * (T - s))) / r * (2 + Real.cos (bmReal W s ω))) by ring, abs_neg,
        abs_of_pos (by positivity)]
    rw [integral_congr_ae e, integral_const_mul]
    ring
  exact (shortDebt_realForm_integral hn hB hBM hWm h𝓕 hs stronglyMeasurable_const hΛ hG hGΛ
    hconv).2 htvc


/-- **Cochrane (2023), A1.4, p. 564 (non-vacuity on the constructed motion):** on `bmPath` with
its natural filtration `bmF`, for `0 ≤ s`, `r > 0`, the economy of `cosEconomy_realForm`
(`Λ_s = 2 + cos W_s`) satisfies the transversality condition and the real form
`B_s/P_s = E_s[∫_s^∞ (Λ_u/Λ_s)s_u du]`. -/
theorem bmPath_cosEconomy_realForm {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r) :
    Tendsto (fun T => ∫ ω, |gaussSeq[fun ω => cosLam bmPath r s T ω * (fun _ _ => 1 / r) T ω
      | bmF s] ω| ∂gaussSeq) atTop (𝓝 0) ∧
    (fun ω => (fun (_ : ℝ) (_ : ℕ → ℝ) => 1 / r) s ω /
        (fun (_ : ℝ) (_ : ℕ → ℝ) => (1 : ℝ)) s ω) =ᵐ[gaussSeq]
      gaussSeq[fun ω => ∫ u in Set.Ioi s, cosLam bmPath r s u ω * (fun _ _ => (1 : ℝ)) u ω /
        (cosLam bmPath r s s ω * (fun _ _ => (1 : ℝ)) s ω) * (fun _ _ => (1 : ℝ)) u ω | bmF s] :=
  cosEconomy_realForm isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) hs hr

end Cochrane.Generality.TidyR8ShortDebtRealForm
