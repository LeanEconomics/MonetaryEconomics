/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR7MonetarismModel
import Monetarism.TidyR7StieltjesCalculus

/-!
# The valuation equations (1.33) and (1.34) under uncertainty: integrating to infinity

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.33)–(1.34), in the model
`TidyR7MonetarismModel.MonetaryModel`. "Now we can integrate, and impose the transversality
condition": from the integrated (1.32) `E_s[n_TB_T − n_sB_s] = −E_s[F_T]`
(`TidyR7MonetarismModel.MonetaryModel.incr_1_32`, `n = Λ/P`,
`F_T = ∫_s^T Λs dr + ∫_s^T n dM`, `flow133`), the finite-horizon budget
`n_sB_s = E_s[n_TB_T] + E_s[F_T]` holds for every `T ≥ s` (`MonetaryModel.rec_1_33`).

## Three readings of "integrate to infinity"

* **Limit form, no convergence hypothesis** (`valuation_iff_tvc_seq`,
  `MonetaryModel.valuation_1_33_seq`): along any times `T_k ≥ s`, almost surely,
  `E_s[F_{T_k}] → n_sB_s` iff `E_s[n_{T_k}B_{T_k}] → 0`. This is the exact content of (1.33) when
  `∫_s^∞` is read as `lim_T E_s∫_s^T`; it needs nothing beyond the finite-horizon budgets.
* **`L¹` form** (`valuation_iff_tvc_flow`, `MonetaryModel.valuation_1_33`): if `F_T → G` in `L¹`
  (`G = ∫_s^∞`), then `n_sB_s = E_s[G]` a.s. iff `E_s[n_TB_T] → 0` in `L¹`.
* **Dominated form** (`valuation_iff_tvc_dom`, `MonetaryModel.valuation_1_33_dom`): if
  `F_{T_k} → G` path by path with `|F_{T_k}| ≤ H` integrable, then `n_sB_s = E_s[G]` a.s. iff
  `E_s[n_{T_k}B_{T_k}] → 0` a.s. (conditional dominated convergence
  `TidyR7CondDominated.ae_tendsto_condExp_of_dominated` identifies `lim E_s[F_{T_k}]` with
  `E_s[G]`). The convergence hypothesis is exactly what makes `E_s ∫_s^∞` equal
  `lim E_s ∫_s^T`; it is not needed for the limit form, and without it the printed `E_t∫_t^∞`
  may not exist while the limit form holds (`TidyR7MonetarismCoin`).

## The book's normalisation

`real_form`: `n_sX = E_s[G]` iff `X/P_s = E_s[G/Λ_s]` (`Λ_s > 0` is `𝓕_s`-measurable and pulls out);
`flow133_div`: `F_T/Λ_s = ∫_s^T (Λ_τ/Λ_s)s_τ dτ + ∫_s^T (Λ_τ/Λ_s) dM_τ/P_τ`, the book's integrand.
`MonetaryModel.valuation_1_33_book`: (1.33) as printed,
`B_s/P_s = E_s ∫_s^∞ (Λ_τ/Λ_s)(s_τ dτ + dM_τ/P_τ)`, iff the transversality condition.

## (1.34)

`MonetaryModel.valuation_1_34`: via `TidyR7MonetarismModel.MonetaryModel.hasDrift_1_34` and
`TidyR6StochasticDrift.valuation_iff_tvc` (`L¹` form);
`MonetaryModel.valuation_1_34_book`: dominated form and
`(M_s + B_s)/P_s = E_s∫_s^∞ (Λ_τ/Λ_s)(s_τ + (i_τ − i^m_τ)M_τ/P_τ) dτ`.
-/

namespace Cochrane.Monetarism.TidyR7MonetarismValuation

open MeasureTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesIntegral Cochrane.Monetarism.TidyR7StieltjesSums
  Cochrane.Monetarism.TidyR7CondDominated Cochrane.Monetarism.TidyR7ProductStep
  Cochrane.Monetarism.TidyR7MonetarismAC Cochrane.Monetarism.TidyR7MonetarismModel

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ}

/-! ## Generic: from the finite-horizon budgets to the valuation equation -/

/-- Cochrane (2023), A1 §1.6, (1.32) ⇒ (1.33), p. 567: **the finite-horizon budget.** If
`E_s[Y_T − Y_s] = −E_s[F]`, with `Y_s` `𝓕_s`-measurable and `Y_T`, `Y_s` integrable, then
`Y_s = E_s[Y_T] + E_s[F]` almost surely.
Generalises `TidyR6StochasticDrift.valuation_of_drift` to a general flow; continuous-time form of
`TidyR6StochasticDrift.rec_of_incr_1_32`. -/
theorem rec_of_incr [IsFiniteMeasure μ] {Y : ℝ → Ω → ℝ} {F : Ω → ℝ} {s T : ℝ}
    (hinc : μ[fun ω => Y T ω - Y s ω | 𝓕 s] =ᵐ[μ] μ[fun ω => -F ω | 𝓕 s])
    (hYs : StronglyMeasurable[𝓕 s] (Y s)) (hYsi : Integrable (Y s) μ)
    (hYTi : Integrable (Y T) μ) :
    Y s =ᵐ[μ] μ[Y T | 𝓕 s] + μ[F | 𝓕 s] := by
  have h1 := condExp_sub (m := 𝓕 s) hYTi hYsi
  have h2 := condExp_neg (μ := μ) F (𝓕 s)
  have h3 : μ[Y s | 𝓕 s] = Y s := condExp_of_stronglyMeasurable (𝓕.le s) hYs hYsi
  filter_upwards [hinc, h1, h2] with ω e1 e2 e3
  have a1 : μ[fun ω => Y T ω - Y s ω | 𝓕 s] ω = μ[Y T | 𝓕 s] ω - Y s ω := by
    rw [show (fun ω => Y T ω - Y s ω) = Y T - Y s from rfl, e2, Pi.sub_apply, h3]
  have a2 : μ[fun ω => -F ω | 𝓕 s] ω = -μ[F | 𝓕 s] ω := by
    rw [show (fun ω => -F ω) = -F from rfl, e3, Pi.neg_apply]
  rw [a1, a2] at e1
  simp only [Pi.add_apply]
  linarith

/-- **Cochrane (2023), A1 §1.6, (1.33)–(1.34), p. 567: valuation iff transversality, `L¹` form,
for a general discounted flow.** If `Y_s = E_s[Y_T] + E_s[F_T]` for every `T ≥ s`, `Y_T`, `F_T`
and `G` are integrable and `F_T → G` in `L¹`, then `Y_s = E_s[G]` a.s. iff `E_s[Y_T] → 0` in `L¹`.
Generalises `TidyR6StochasticDrift.valuation_iff_tvc` (there `F_T = ∫_s^T g dr`) to flows with a
Stieltjes part `∫ n dM`. -/
theorem valuation_iff_tvc_flow [IsFiniteMeasure μ] {Y F : ℝ → Ω → ℝ} {s : ℝ} {G : Ω → ℝ}
    (hrec : ∀ T, s ≤ T → Y s =ᵐ[μ] μ[Y T | 𝓕 s] + μ[F T | 𝓕 s])
    (hYi : ∀ T, s ≤ T → Integrable (Y T) μ) (hFi : ∀ T, s ≤ T → Integrable (F T) μ)
    (hG : Integrable G μ) (hconv : Tendsto (fun T => ∫ ω, |F T ω - G ω| ∂μ) atTop (𝓝 0)) :
    Y s =ᵐ[μ] μ[G | 𝓕 s] ↔ Tendsto (fun T => ∫ ω, |μ[Y T | 𝓕 s] ω| ∂μ) atTop (𝓝 0) := by
  set b : Ω → ℝ := fun ω => Y s ω - μ[G | 𝓕 s] ω with hb
  have hbi : Integrable b μ := (hYi s le_rfl).sub integrable_condExp
  have hclose : ∀ T, s ≤ T → |∫ ω, |μ[Y T | 𝓕 s] ω| ∂μ - ∫ ω, |b ω| ∂μ| ≤
      ∫ ω, |F T ω - G ω| ∂μ := by
    intro T hsT
    have hv := hrec T hsT
    have hsub := condExp_sub (m := 𝓕 s) (hFi T hsT) hG
    have hae : ∀ᵐ ω ∂μ, |μ[Y T | 𝓕 s] ω| - |b ω| ≤ |μ[F T - G | 𝓕 s] ω| ∧
        |b ω| - |μ[Y T | 𝓕 s] ω| ≤ |μ[F T - G | 𝓕 s] ω| := by
      filter_upwards [hv, hsub] with ω e1 e2
      simp only [Pi.add_apply] at e1
      have e2' : μ[F T - G | 𝓕 s] ω = μ[F T | 𝓕 s] ω - μ[G | 𝓕 s] ω := by
        rw [e2]; rfl
      have ea : μ[Y T | 𝓕 s] ω = b ω - μ[F T - G | 𝓕 s] ω := by
        rw [e2']; simp only [hb]; linarith
      rw [ea]
      constructor
      · have := abs_sub (b ω) (μ[F T - G | 𝓕 s] ω)
        linarith
      · have := abs_sub_abs_le_abs_sub (b ω) (b ω - μ[F T - G | 𝓕 s] ω)
        simp only [sub_sub_cancel] at this
        linarith
    have hYTc : Integrable (fun ω => |μ[Y T | 𝓕 s] ω|) μ := integrable_condExp.abs
    have hbc : Integrable (fun ω => |b ω|) μ := hbi.abs
    have hdc : Integrable (fun ω => |μ[F T - G | 𝓕 s] ω|) μ := integrable_condExp.abs
    have hle := integral_abs_condExp_le (μ := μ) (m := 𝓕 s) (F T - G)
    have hle' : ∫ ω, |(F T - G) ω| ∂μ = ∫ ω, |F T ω - G ω| ∂μ := rfl
    rw [hle'] at hle
    rw [abs_le]
    constructor
    · have := integral_mono_ae (hbc.sub hYTc) hdc (by
        filter_upwards [hae] with ω h; simp only [Pi.sub_apply]; linarith [h.2])
      simp only [Pi.sub_apply] at this
      rw [integral_sub hbc hYTc] at this
      linarith
    · have := integral_mono_ae (hYTc.sub hbc) hdc (by
        filter_upwards [hae] with ω h; simp only [Pi.sub_apply]; linarith [h.1])
      simp only [Pi.sub_apply] at this
      rw [integral_sub hYTc hbc] at this
      linarith
  have hlim : Tendsto (fun T => ∫ ω, |μ[Y T | 𝓕 s] ω| ∂μ) atTop (𝓝 (∫ ω, |b ω| ∂μ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hconv
    filter_upwards [eventually_ge_atTop s] with T hT
    rw [Real.norm_eq_abs]
    exact hclose T hT
  constructor
  · intro h
    have hb0 : ∫ ω, |b ω| ∂μ = 0 := by
      have : (fun ω => |b ω|) =ᵐ[μ] 0 := by
        filter_upwards [h] with ω hω; simp [hb, hω]
      rw [integral_congr_ae this]; simp
    rwa [hb0] at hlim
  · intro h
    have hb0 : ∫ ω, |b ω| ∂μ = 0 := tendsto_nhds_unique hlim h
    have hae := (integral_eq_zero_iff_of_nonneg (fun ω => abs_nonneg (b ω)) hbi.abs).1 hb0
    filter_upwards [hae] with ω hω
    simp only [Pi.zero_apply, abs_eq_zero, hb] at hω
    linarith

/-- **Cochrane (2023), A1 §1.6, (1.33)–(1.34), p. 567: valuation iff transversality, limit form,
with no convergence hypothesis.** If `Y_s = E_s[Y_T] + E_s[F_T]` for every `T ≥ s`, then along
any times `T_k ≥ s`: almost surely `E_s[F_{T_k}] → Y_s` iff almost surely `E_s[Y_{T_k}] → 0`. -/
theorem valuation_iff_tvc_seq {Y F : ℝ → Ω → ℝ} {s : ℝ}
    (hrec : ∀ T, s ≤ T → Y s =ᵐ[μ] μ[Y T | 𝓕 s] + μ[F T | 𝓕 s]) {T : ℕ → ℝ}
    (hT : ∀ k, s ≤ T k) :
    (∀ᵐ ω ∂μ, Tendsto (fun k => μ[F (T k) | 𝓕 s] ω) atTop (𝓝 (Y s ω))) ↔
      ∀ᵐ ω ∂μ, Tendsto (fun k => μ[Y (T k) | 𝓕 s] ω) atTop (𝓝 0) := by
  have hall := ae_all_iff.2 fun k => hrec (T k) (hT k)
  have key : ∀ᵐ ω ∂μ, ∀ k, μ[Y (T k) | 𝓕 s] ω = Y s ω - μ[F (T k) | 𝓕 s] ω := by
    filter_upwards [hall] with ω h k
    have := h k
    simp only [Pi.add_apply] at this
    linarith
  constructor
  · intro h
    filter_upwards [h, key] with ω h1 h2
    simp_rw [h2]
    have := (tendsto_const_nhds (x := Y s ω)).sub h1
    rwa [sub_self] at this
  · intro h
    filter_upwards [h, key] with ω h1 h2
    have e : ∀ k, μ[F (T k) | 𝓕 s] ω = Y s ω - μ[Y (T k) | 𝓕 s] ω := fun k => by
      rw [h2 k]; ring
    simp_rw [e]
    have := (tendsto_const_nhds (x := Y s ω)).sub h1
    rwa [sub_zero] at this

/-- **Cochrane (2023), A1 §1.6, (1.33)–(1.34), p. 567: valuation iff transversality, dominated
infinite-horizon form.** If `Y_s = E_s[Y_T] + E_s[F_T]` for every `T ≥ s` and along times
`T_k ≥ s` the flows `F_{T_k}` are measurable, converge path by path to `G = ∫_s^∞` and are
dominated by an integrable `H`, then `Y_s = E_s[G]` a.s. iff `E_s[Y_{T_k}] → 0` a.s. -/
theorem valuation_iff_tvc_dom [IsFiniteMeasure μ] {Y F : ℝ → Ω → ℝ} {s : ℝ}
    (hrec : ∀ T, s ≤ T → Y s =ᵐ[μ] μ[Y T | 𝓕 s] + μ[F T | 𝓕 s]) {T : ℕ → ℝ}
    (hT : ∀ k, s ≤ T k) {G H : Ω → ℝ} (hFm : ∀ k, Measurable (F (T k))) (hH : Integrable H μ)
    (hbd : ∀ k ω, |F (T k) ω| ≤ H ω) (hlim : ∀ ω, Tendsto (fun k => F (T k) ω) atTop (𝓝 (G ω))) :
    Y s =ᵐ[μ] μ[G | 𝓕 s] ↔ ∀ᵐ ω ∂μ, Tendsto (fun k => μ[Y (T k) | 𝓕 s] ω) atTop (𝓝 0) := by
  have hc := ae_tendsto_condExp_of_dominated (𝓕.le s) hFm hH hbd hlim
  rw [← valuation_iff_tvc_seq hrec hT]
  constructor
  · intro h
    filter_upwards [h, hc] with ω h1 h2
    rwa [h1]
  · intro h
    filter_upwards [h, hc] with ω h1 h2
    exact tendsto_nhds_unique h1 h2

/-! ## The flows of (1.33) and (1.34) -/

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: the discounted flow
`F_T = ∫_s^T Λ_rs_r dr + ∫_s^T (Λ/P) dM` (money creation counted as seigniorage). -/
noncomputable def flow133 (Λ P M sp : ℝ → Ω → ℝ) (s T : ℝ) (ω : Ω) : ℝ :=
  (∫ r in s..T, Λ r ω * sp r ω) + rsInt s T (fun u => disc Λ P u ω) (fun u => M u ω)

/-- Cochrane (2023), A1 §1.6, (1.34), p. 567: the discounted flow
`F_T = ∫_s^T (Λ_rs_r + (i_r − i^m_r)(Λ_r/P_r)M_r) dr` (seigniorage as interest saving). -/
noncomputable def flow134 (Λ P M i im sp : ℝ → Ω → ℝ) (s T : ℝ) (ω : Ω) : ℝ :=
  ∫ r in s..T, (Λ r ω * sp r ω + (i r ω - im r ω) * disc Λ P r ω * M r ω)

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the book's integrand.** For `Λ_s ≠ 0`,
`F_T/Λ_s = ∫_s^T (Λ_τ/Λ_s)s_τ dτ + ∫_s^T (Λ_τ/Λ_s) dM_τ/P_τ`. -/
theorem flow133_div (Λ P M sp : ℝ → Ω → ℝ) (s T : ℝ) (ω : Ω) :
    flow133 Λ P M sp s T ω / Λ s ω = (∫ r in s..T, Λ r ω / Λ s ω * sp r ω) +
      rsInt s T (fun u => Λ u ω / Λ s ω / P u ω) (fun u => M u ω) := by
  have e : (fun u => Λ u ω / Λ s ω / P u ω) = fun u => (Λ s ω)⁻¹ * disc Λ P u ω :=
    funext fun u => by simp only [disc]; ring
  rw [flow133, add_div, e, rsInt_smul_left, ← intervalIntegral.integral_div]
  congr 1
  · exact intervalIntegral.integral_congr fun r _ => by ring
  · ring

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567: the book's integrand.**
`F_T/Λ_s = ∫_s^T (Λ_τ/Λ_s)(s_τ + (i_τ − i^m_τ)M_τ/P_τ) dτ`. -/
theorem flow134_div (Λ P M i im sp : ℝ → Ω → ℝ) (s T : ℝ) (ω : Ω) :
    flow134 Λ P M i im sp s T ω / Λ s ω =
      ∫ r in s..T, Λ r ω / Λ s ω * (sp r ω + (i r ω - im r ω) * M r ω / P r ω) := by
  rw [flow134, ← intervalIntegral.integral_div]
  exact intervalIntegral.integral_congr fun r _ => by simp only [disc]; ring

/-! ## The book's normalisation -/

variable {Λ P B M A N i im sp : ℝ → Ω → ℝ}

/-- **Cochrane (2023), A1 §1.6, (1.33)–(1.34), p. 567: dividing by `Λ_s`.** For `X` and `G`
with `G`, `G/Λ_s` integrable: `(Λ_s/P_s)X = E_s[G]` a.s. iff `X/P_s = E_s[G/Λ_s]` a.s.
(`Λ_s > 0` is `𝓕_s`-measurable and pulls out of `E_s`, Mathlib
`condExp_mul_of_stronglyMeasurable_left`). -/
theorem real_form (hm : MonetaryModel μ 𝓕 Λ P B M A N i im sp) {s : ℝ} {X G : Ω → ℝ}
    (hG : Integrable G μ) (hGΛ : Integrable (fun ω => G ω / Λ s ω) μ) :
    (fun ω => disc Λ P s ω * X ω) =ᵐ[μ] μ[G | 𝓕 s] ↔
      (fun ω => X ω / P s ω) =ᵐ[μ] μ[fun ω => G ω / Λ s ω | 𝓕 s] := by
  have hinv : StronglyMeasurable[𝓕 s] fun ω => (Λ s ω)⁻¹ :=
    (hm.Λ_adapted s).measurable.inv.stronglyMeasurable
  have e : (fun ω => G ω / Λ s ω) = (fun ω => (Λ s ω)⁻¹) * G :=
    funext fun ω => by simp only [Pi.mul_apply]; ring
  have hpull := condExp_mul_of_stronglyMeasurable_left hinv (by rw [← e]; exact hGΛ) hG
  rw [← e] at hpull
  have hΛ : ∀ ω, Λ s ω ≠ 0 := fun ω => (hm.Λ_pos s ω).ne'
  have hP : ∀ ω, P s ω ≠ 0 := fun ω => (hm.P_pos s ω).ne'
  constructor
  · intro h
    filter_upwards [h, hpull] with ω h1 h2
    rw [h2, Pi.mul_apply, ← h1]
    simp only [disc]
    field_simp [hΛ ω, hP ω]
  · intro h
    filter_upwards [h, hpull] with ω h1 h2
    rw [h2, Pi.mul_apply] at h1
    have h1' : X ω = P s ω * ((Λ s ω)⁻¹ * μ[G | 𝓕 s] ω) := by
      rw [← h1]; field_simp [hP ω]
    rw [h1']
    simp only [disc]
    field_simp [hΛ ω, hP ω]

namespace MonetaryModel

variable (hm : MonetaryModel μ 𝓕 Λ P B M A N i im sp)
include hm

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: with `i^m = 0`, path by path
`F_T = −(∫_s^T n dB + ∫_s^T B dA)` (`TidyR7MonetarismModel.MonetaryModel.pathwise_1_32`). -/
theorem flow133_eq (him : ∀ r ω, im r ω = 0) {s T : ℝ} (hsT : s ≤ T) :
    flow133 Λ P M sp s T = -(intRS s T (disc Λ P) B + intRS s T B A) := by
  funext ω
  have h := hm.pathwise_1_32 ω hsT
  simp only [him, zero_mul, sub_zero] at h
  simp only [flow133, Pi.neg_apply, Pi.add_apply, intRS]
  rw [h, neg_neg]

/-- Cochrane (2023), A1 §1.6, (1.34), p. 567: path by path
`F_T = −(∫_s^T n d(B + M) + ∫_s^T (B + M) dA)`. -/
theorem flow134_eq {s T : ℝ} (hsT : s ≤ T) :
    flow134 Λ P M i im sp s T =
      -(intRS s T (disc Λ P) (addProc B M) + intRS s T (addProc B M) A) := by
  funext ω
  simp only [flow134, Pi.neg_apply, Pi.add_apply, intRS]
  rw [hm.pathwise_1_34 ω hsT, neg_neg]

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567: the flow `F_T` is measurable (a combination of
pathwise Stieltjes integrals, `TidyR7StieltjesCalculus.measurable_rsInt`). -/
theorem measurable_flow133 (him : ∀ r ω, im r ω = 0) {s T : ℝ} (hsT : s ≤ T) :
    Measurable (flow133 Λ P M sp s T) := by
  rw [flow133_eq hm him hsT]
  rcases hsT.lt_or_eq with hlt | rfl
  · have hBm : ∀ u, Measurable (B u) := fun u => ((hm.B_adapted u).mono (𝓕.le u)).measurable
    have m1 : Measurable (intRS s T (disc Λ P) B) :=
      TidyR7StieltjesCalculus.measurable_rsInt (f := fun ω u => disc Λ P u ω)
        (g := fun ω u => B u ω) hlt hm.measurable_disc hBm fun ω =>
          Or.inr ⟨hm.disc_cadlag ω, hm.B_bv ω s T, (hm.B_cont ω).continuousOn⟩
    have m2 : Measurable (intRS s T B A) :=
      TidyR7StieltjesCalculus.measurable_rsInt (f := fun ω u => B u ω)
        (g := fun ω u => A u ω) hlt hBm hm.measurable_A fun ω =>
          Or.inl ⟨(hm.B_cont ω).continuousOn, hm.A_bv ω s T⟩
    exact (m1.add m2).neg
  · have e : intRS s s (disc Λ P) B + intRS s s B A = 0 := funext fun ω => by
      simp only [Pi.add_apply, intRS, TidyR7StieltjesVariation.rsInt_self, add_zero,
        Pi.zero_apply]
    rw [e, neg_zero]
    exact measurable_const

/-- Cochrane (2023), A1 §1.6, (1.34), p. 567: the flow `F_T` of (1.34) is measurable. -/
theorem measurable_flow134 {s T : ℝ} (hsT : s ≤ T) :
    Measurable (flow134 Λ P M i im sp s T) := by
  rw [flow134_eq hm hsT]
  rcases hsT.lt_or_eq with hlt | rfl
  · have hWm : ∀ u, Measurable (addProc B M u) := fun u =>
      ((hm.W_adapted u).mono (𝓕.le u)).measurable
    have m1 : Measurable (intRS s T (disc Λ P) (addProc B M)) :=
      TidyR7StieltjesCalculus.measurable_rsInt (f := fun ω u => disc Λ P u ω)
        (g := fun ω u => addProc B M u ω) hlt hm.measurable_disc hWm fun ω =>
          Or.inr ⟨hm.disc_cadlag ω, hm.W_bv ω s T, (hm.W_cont ω).continuousOn⟩
    have m2 : Measurable (intRS s T (addProc B M) A) :=
      TidyR7StieltjesCalculus.measurable_rsInt (f := fun ω u => addProc B M u ω)
        (g := fun ω u => A u ω) hlt hWm hm.measurable_A fun ω =>
          Or.inl ⟨(hm.W_cont ω).continuousOn, hm.A_bv ω s T⟩
    exact (m1.add m2).neg
  · have e : intRS s s (disc Λ P) (addProc B M) + intRS s s (addProc B M) A = 0 :=
      funext fun ω => by
        simp only [Pi.add_apply, intRS, TidyR7StieltjesVariation.rsInt_self, add_zero,
          Pi.zero_apply]
    rw [e, neg_zero]
    exact measurable_const

variable [IsFiniteMeasure μ]

/-- **Cochrane (2023), A1 §1.6, (1.32) ⇒ (1.33), p. 567: the finite-horizon budget.** With
`i^m = 0`, the domination conditions on `[s, T]` and `n_sB_s`, `n_TB_T` integrable:
`n_sB_s = E_s[n_TB_T] + E_s[∫_s^T Λs dr + ∫_s^T n dM]` almost surely; `F_T` is integrable. -/
theorem rec_1_33 (him : ∀ r ω, im r ω = 0) {s T : ℝ} (hsT : s ≤ T)
    (hd : Dominated μ A N s T B (disc Λ P))
    (hYs : Integrable (fun ω => disc Λ P s ω * B s ω) μ)
    (hYT : Integrable (fun ω => disc Λ P T ω * B T ω) μ) :
    Integrable (flow133 Λ P M sp s T) μ ∧
      (fun ω => disc Λ P s ω * B s ω) =ᵐ[μ]
        μ[fun ω => disc Λ P T ω * B T ω | 𝓕 s] + μ[flow133 Λ P M sp s T | 𝓕 s] := by
  have hpd := hm.productStepData_B hsT hd
  have i1 := hpd.integrable_intXB
  rw [← hm.disc_eq] at i1
  have hF : Integrable (flow133 Λ P M sp s T) μ := by
    rw [flow133_eq hm him hsT]
    exact (i1.add hpd.integrable_intBA).neg
  refine ⟨hF, ?_⟩
  have hinc := hm.incr_1_32 hsT hd him
  exact rec_of_incr (Y := fun t ω => disc Λ P t ω * B t ω) (F := flow133 Λ P M sp s T) hinc
    ((hm.disc_adapted s).mul (hm.B_adapted s)) hYs hYT

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567, limit form.** With `i^m = 0`, the domination
conditions on every `[s, T]` and `n_TB_T` integrable for `T ≥ s`: along any times `T_k ≥ s`,
almost surely `E_s[∫_s^{T_k} Λs dr + ∫_s^{T_k} n dM] → n_sB_s` iff almost surely
`E_s[n_{T_k}B_{T_k}] → 0`. No convergence of the flows is assumed. -/
theorem valuation_1_33_seq (him : ∀ r ω, im r ω = 0) {s : ℝ}
    (hd : ∀ T, s ≤ T → Dominated μ A N s T B (disc Λ P))
    (hYi : ∀ T, s ≤ T → Integrable (fun ω => disc Λ P T ω * B T ω) μ) {T : ℕ → ℝ}
    (hT : ∀ k, s ≤ T k) :
    (∀ᵐ ω ∂μ, Tendsto (fun k => μ[flow133 Λ P M sp s (T k) | 𝓕 s] ω) atTop
        (𝓝 (disc Λ P s ω * B s ω))) ↔
      ∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => disc Λ P (T k) ω * B (T k) ω | 𝓕 s] ω) atTop
        (𝓝 0) :=
  valuation_iff_tvc_seq (Y := fun t ω => disc Λ P t ω * B t ω)
    (fun T' hT' => (rec_1_33 hm him hT' (hd T' hT') (hYi s le_rfl) (hYi T' hT')).2) hT

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567, `L¹` form: valuation iff transversality.** With
`i^m = 0`, the domination conditions on every `[s, T]`, `n_TB_T` integrable, and
`F_T = ∫_s^T Λs dr + ∫_s^T n dM → G` in `L¹` (`G = ∫_s^∞ Λs dr + ∫_s^∞ n dM`):
`n_sB_s = E_s[G]` a.s. iff `E_s[n_TB_T] → 0` in `L¹`.
Generalises `TidyR6StochasticDrift.valuation_1_33_fv` and `ContinuousTime.money_printing_iff`. -/
theorem valuation_1_33 (him : ∀ r ω, im r ω = 0) {s : ℝ}
    (hd : ∀ T, s ≤ T → Dominated μ A N s T B (disc Λ P))
    (hYi : ∀ T, s ≤ T → Integrable (fun ω => disc Λ P T ω * B T ω) μ) {G : Ω → ℝ}
    (hG : Integrable G μ)
    (hconv : Tendsto (fun T => ∫ ω, |flow133 Λ P M sp s T ω - G ω| ∂μ) atTop (𝓝 0)) :
    (fun ω => disc Λ P s ω * B s ω) =ᵐ[μ] μ[G | 𝓕 s] ↔
      Tendsto (fun T => ∫ ω, |μ[fun ω => disc Λ P T ω * B T ω | 𝓕 s] ω| ∂μ) atTop (𝓝 0) :=
  valuation_iff_tvc_flow (Y := fun t ω => disc Λ P t ω * B t ω) (F := flow133 Λ P M sp s)
    (fun T hT => (rec_1_33 hm him hT (hd T hT) (hYi s le_rfl) (hYi T hT)).2) hYi
    (fun T hT => (rec_1_33 hm him hT (hd T hT) (hYi s le_rfl) (hYi T hT)).1) hG hconv

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567, dominated form.** With `i^m = 0`, the domination
conditions on every `[s, T]`, `n_TB_T` integrable, and along `T_k ≥ s` the flows `F_{T_k}`
converging path by path to `G` with `|F_{T_k}| ≤ H` integrable: `n_sB_s = E_s[G]` a.s. iff
`E_s[n_{T_k}B_{T_k}] → 0` a.s. -/
theorem valuation_1_33_dom (him : ∀ r ω, im r ω = 0) {s : ℝ}
    (hd : ∀ T, s ≤ T → Dominated μ A N s T B (disc Λ P))
    (hYi : ∀ T, s ≤ T → Integrable (fun ω => disc Λ P T ω * B T ω) μ) {T : ℕ → ℝ}
    (hT : ∀ k, s ≤ T k) {G H : Ω → ℝ} (hH : Integrable H μ)
    (hbd : ∀ k ω, |flow133 Λ P M sp s (T k) ω| ≤ H ω)
    (hlim : ∀ ω, Tendsto (fun k => flow133 Λ P M sp s (T k) ω) atTop (𝓝 (G ω))) :
    (fun ω => disc Λ P s ω * B s ω) =ᵐ[μ] μ[G | 𝓕 s] ↔
      ∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => disc Λ P (T k) ω * B (T k) ω | 𝓕 s] ω) atTop
        (𝓝 0) :=
  valuation_iff_tvc_dom (Y := fun t ω => disc Λ P t ω * B t ω) (F := flow133 Λ P M sp s)
    (fun T' hT' => (rec_1_33 hm him hT' (hd T' hT') (hYi s le_rfl) (hYi T' hT')).2) hT
    (fun k => measurable_flow133 hm him (hT k)) hH hbd hlim

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567, as printed:
`B_s/P_s = E_s ∫_s^∞ (Λ_τ/Λ_s)(s_τ dτ + dM_τ/P_τ)` iff the transversality condition.** Under the
hypotheses of `MonetaryModel.valuation_1_33_dom` and `G/Λ_s` integrable: (i) path by path,
`∫_s^{T_k} (Λ_τ/Λ_s)s_τ dτ + ∫_s^{T_k} (Λ_τ/Λ_s) dM_τ/P_τ → G/Λ_s` (the book's integral to
infinity); (ii) `B_s/P_s = E_s[G/Λ_s]` a.s. iff `E_s[Λ_{T_k}B_{T_k}/P_{T_k}] → 0` a.s. -/
theorem valuation_1_33_book (him : ∀ r ω, im r ω = 0) {s : ℝ}
    (hd : ∀ T, s ≤ T → Dominated μ A N s T B (disc Λ P))
    (hYi : ∀ T, s ≤ T → Integrable (fun ω => disc Λ P T ω * B T ω) μ) {T : ℕ → ℝ}
    (hT : ∀ k, s ≤ T k) {G H : Ω → ℝ} (hH : Integrable H μ)
    (hbd : ∀ k ω, |flow133 Λ P M sp s (T k) ω| ≤ H ω)
    (hlim : ∀ ω, Tendsto (fun k => flow133 Λ P M sp s (T k) ω) atTop (𝓝 (G ω)))
    (hGΛ : Integrable (fun ω => G ω / Λ s ω) μ) :
    (∀ ω, Tendsto (fun k => (∫ r in s..T k, Λ r ω / Λ s ω * sp r ω) +
        rsInt s (T k) (fun u => Λ u ω / Λ s ω / P u ω) (fun u => M u ω)) atTop
        (𝓝 (G ω / Λ s ω))) ∧
      ((fun ω => B s ω / P s ω) =ᵐ[μ] μ[fun ω => G ω / Λ s ω | 𝓕 s] ↔
        ∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => disc Λ P (T k) ω * B (T k) ω | 𝓕 s] ω) atTop
          (𝓝 0)) := by
  have hGm : Measurable G := measurable_of_tendsto_metrizable
    (fun k => measurable_flow133 hm him (hT k)) (tendsto_pi_nhds.2 hlim)
  have hG : Integrable G μ := hH.mono' hGm.aestronglyMeasurable (Eventually.of_forall fun ω =>
    by rw [Real.norm_eq_abs]; exact le_of_tendsto' (hlim ω).abs fun k => hbd k ω)
  refine ⟨fun ω => ?_, ?_⟩
  · simp_rw [← flow133_div]
    exact (hlim ω).div_const _
  · rw [← real_form hm hG hGΛ]
    exact valuation_1_33_dom hm him hd hYi hT hH hbd hlim

omit [IsFiniteMeasure μ] in
/-- Cochrane (2023), A1 §1.6, (1.34), p. 567: the flow of (1.34) over `[u, v]` is integrable
under the domination conditions on every interval (for `u ≤ v` and, by reversal, `v ≤ u`). -/
theorem integrable_flow134
    (hd : ∀ s t, s ≤ t → Dominated μ A N s t (addProc B M) (disc Λ P)) (u v : ℝ) :
    Integrable (flow134 Λ P M i im sp u v) μ := by
  have key : ∀ u v, u ≤ v → Integrable (flow134 Λ P M i im sp u v) μ := by
    intro u v huv
    have hpd := hm.productStepData_W huv (hd u v huv)
    have i1 := hpd.integrable_intXB
    rw [← hm.disc_eq] at i1
    rw [flow134_eq hm huv]
    exact (i1.add hpd.integrable_intBA).neg
  rcases le_total u v with h | h
  · exact key u v h
  · have e : flow134 Λ P M i im sp u v = -flow134 Λ P M i im sp v u := funext fun ω => by
      simp only [flow134, Pi.neg_apply]
      rw [intervalIntegral.integral_symm]
    rw [e]
    exact (key v u h).neg

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567, `L¹` form: valuation iff transversality.** With
the domination conditions for `B + M` on every interval, `n_T(B + M)_T` integrable, and
`F_T = ∫_s^T (Λs + (i − i^m)nM) dr → G` in `L¹`:
`n_s(B_s + M_s) = E_s[G]` a.s. iff `E_s[n_T(B_T + M_T)] → 0` in `L¹`. Via
`TidyR7MonetarismModel.MonetaryModel.hasDrift_1_34` and
`TidyR6StochasticDrift.valuation_iff_tvc`.
Stochastic generalisation of `ContinuousTime.money_interest_iff`. -/
theorem valuation_1_34 {s : ℝ}
    (hd : ∀ s t, s ≤ t → Dominated μ A N s t (addProc B M) (disc Λ P))
    (hYi : ∀ T, Integrable (fun ω => disc Λ P T ω * addProc B M T ω) μ) {G : Ω → ℝ}
    (hG : Integrable G μ)
    (hconv : Tendsto (fun T => ∫ ω, |flow134 Λ P M i im sp s T ω - G ω| ∂μ) atTop (𝓝 0)) :
    (fun ω => disc Λ P s ω * addProc B M s ω) =ᵐ[μ] μ[G | 𝓕 s] ↔
      Tendsto (fun T => ∫ ω, |μ[fun ω => disc Λ P T ω * addProc B M T ω | 𝓕 s] ω| ∂μ)
        atTop (𝓝 0) :=
  TidyR6StochasticDrift.valuation_iff_tvc (Y := fun t ω => disc Λ P t ω * addProc B M t ω)
    (g := fun r ω => Λ r ω * sp r ω + (i r ω - im r ω) * disc Λ P r ω * M r ω)
    (hm.hasDrift_1_34 hd) ((hm.disc_adapted s).mul (hm.W_adapted s)) hYi
    (fun T => integrable_flow134 hm hd s T) hG hconv

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567, as printed:
`(M_s + B_s)/P_s = E_s∫_s^∞ (Λ_τ/Λ_s)(s_τ + (i_τ − i^m_τ)M_τ/P_τ) dτ` iff the transversality
condition**, dominated form. With the domination conditions for `B + M` on every interval,
`n_T(B_T + M_T)` integrable, `F_{T_k} = ∫_s^{T_k}(Λs + (i − i^m)nM) → G` path by path along
`T_k ≥ s` with `|F_{T_k}| ≤ H` integrable and `G/Λ_s` integrable: (i) path by path
`∫_s^{T_k} (Λ_τ/Λ_s)(s_τ + (i_τ − i^m_τ)M_τ/P_τ) dτ → G/Λ_s`; (ii)
`(M_s + B_s)/P_s = E_s[G/Λ_s]` a.s. iff `E_s[Λ_{T_k}(M + B)_{T_k}/P_{T_k}] → 0` a.s.
Stochastic generalisation of `ContinuousTime.money_interest_iff`. -/
theorem valuation_1_34_book {s : ℝ}
    (hd : ∀ s t, s ≤ t → Dominated μ A N s t (addProc B M) (disc Λ P))
    (hYi : ∀ T, Integrable (fun ω => disc Λ P T ω * addProc B M T ω) μ) {T : ℕ → ℝ}
    (hT : ∀ k, s ≤ T k) {G H : Ω → ℝ} (hH : Integrable H μ)
    (hbd : ∀ k ω, |flow134 Λ P M i im sp s (T k) ω| ≤ H ω)
    (hlim : ∀ ω, Tendsto (fun k => flow134 Λ P M i im sp s (T k) ω) atTop (𝓝 (G ω)))
    (hGΛ : Integrable (fun ω => G ω / Λ s ω) μ) :
    (∀ ω, Tendsto (fun k => ∫ r in s..T k,
        Λ r ω / Λ s ω * (sp r ω + (i r ω - im r ω) * M r ω / P r ω)) atTop
        (𝓝 (G ω / Λ s ω))) ∧
      ((fun ω => addProc B M s ω / P s ω) =ᵐ[μ] μ[fun ω => G ω / Λ s ω | 𝓕 s] ↔
        ∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => disc Λ P (T k) ω * addProc B M (T k) ω | 𝓕 s] ω)
          atTop (𝓝 0)) := by
  have hGm : Measurable G := measurable_of_tendsto_metrizable
    (fun k => measurable_flow134 hm (hT k)) (tendsto_pi_nhds.2 hlim)
  have hG : Integrable G μ := hH.mono' hGm.aestronglyMeasurable (Eventually.of_forall fun ω =>
    by rw [Real.norm_eq_abs]; exact le_of_tendsto' (hlim ω).abs fun k => hbd k ω)
  refine ⟨fun ω => ?_, ?_⟩
  · simp_rw [← flow134_div]
    exact (hlim ω).div_const _
  · rw [← real_form hm hG hGΛ]
    have hrec : ∀ T', s ≤ T' → (fun ω => disc Λ P s ω * addProc B M s ω) =ᵐ[μ]
        μ[fun ω => disc Λ P T' ω * addProc B M T' ω | 𝓕 s] +
          μ[flow134 Λ P M i im sp s T' | 𝓕 s] := fun T' hT' =>
      rec_of_incr (Y := fun t ω => disc Λ P t ω * addProc B M t ω)
        (F := flow134 Λ P M i im sp s T') (hm.incr_1_34 hT' (hd s T' hT'))
        ((hm.disc_adapted s).mul (hm.W_adapted s)) (hYi s) (hYi T')
    exact valuation_iff_tvc_dom (Y := fun t ω => disc Λ P t ω * addProc B M t ω)
      (F := flow134 Λ P M i im sp s) hrec hT (fun k => measurable_flow134 hm (hT k)) hH hbd hlim

end MonetaryModel

end Cochrane.Monetarism.TidyR7MonetarismValuation
