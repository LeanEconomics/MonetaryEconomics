/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.TidyR7ItoBondStep

/-!
# The discount factor and the value of debt as Itô processes: `E_t[d(ΛW)] = 0`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.6, pp. 70–79 (the
continuous-time valuation equations (3.31)–(3.36) and the stochastic processes of (3.44)–(3.45),
`dx = μ dt + σ dz`), and Online Appendix A1.4–A1.5, pp. 564–566. The deterministic versions are
`ContinuousLong.Lambda_W_const` (`(ΛW)' = 0`) and `ContinuousLong.Lambda_valuation`
(`(ΛV)' = −Λs`, `ΛV = ∫Λs`).

## Setting

One Brownian motion `W` (`TidyR7BrownianQV.BMFiltration`); on `[s, t]`, `0 ≤ s < t`, the
discount factor `Λ` (drift `a_Λ`, diffusion `σ_Λ`) and the value of debt `V` (drift `a_V`,
diffusion `σ_V`) are Itô processes with bounded, adapted, a.s. continuous coefficients
(`TidyR7ItoProcess.ItoProcess`); the surplus `s` is any process. `ItoDiscountModel` imposes the
pricing condition **on the coefficients**,
`Λ a_V + V a_Λ + σ_Λσ_V = −Λ s` at every date of `[s, t]` and every state,
which is the book's `E_t[dΛ/Λ + dV/V + dΛdV/(ΛV)] = −(s/V) dt` multiplied by `ΛV`
(`pricing_rate_iff`). With `s = 0` and `V` the cumulative return `W` this is the basic pricing
relation `E_t[d(ΛW)] = 0` of A1.5 (the book's expanded form
`E_t[dΛ/Λ + dW/W + dΛdW/(ΛW)] = 0`); `drift_of_flow_127` derives the `V` condition from the
`W` condition and the flow (1.27), `dV/V = −(s/V) dt + dW/W`, exactly as on p. 566.

## Main results

* `ItoDiscountModel.step` (**`E_t[d(ΛV)] = −Λ s dt`**, A1.5): a.s.
  `E_s[Λ_tV_t − Λ_sV_s] = −E_s[∫_s^t Λ s du]`; `ItoDiscountModel.step_W` (**`E_t[d(ΛW)] = 0`**):
  `E_s[Λ_tW_t − Λ_sW_s] = 0` when `s = 0`; `ItoDiscountModel.martingale_W`: on every
  `[r, u] ⊆ [s, t]`, `E_r[Λ_uW_u] = Λ_rW_r` (`ΛW` is a martingale on `[s, t]`).
* `ItoDiscountModel.bookForm_iff`: the bracket-free step
  `E_s[Δ(ΛV)] = E_s[∫Λ a_V du] + E_s[∫V a_Λ du]` (i.e. `Λ E_t dV + V E_t dΛ`, dropping
  `dΛ dV`) holds iff `E_s[∫_s^t σ_Λσ_V du] = 0`. **The book keeps `dΛ_t dW_t/(Λ_tW_t)` on p. 566,
  so A1.5 holds verbatim with diffusions**; only a reading without the covariation would fail.
* Valuation iff transversality (`ItoDiscountModel` on every `[s, T]`):
  `rec_value` (`Λ_sV_s = E_s[Λ_TV_T] + E_s[∫_s^T Λs]`), `valuation_seq` (limit form, no
  convergence hypothesis: `E_s[∫_s^{T_k} Λs] → Λ_sV_s` a.s. iff `E_s[Λ_{T_k}V_{T_k}] → 0` a.s.),
  `valuation_L1` (`Λ_sV_s = E_s[G]` iff the TVC holds in `L¹`, when `∫_s^T Λs → G` in `L¹`),
  `valuation_seq_pathwise` (the same with the pathwise `∫_s^T Λ_u s_u du`).
* A1.4 (short-term debt): `shortDebt_model` — nominal debt `B` with `dB = (iB − Ps) dt` (no
  diffusion, the flow (3.29)/(1.31) with `M = 0`) and the nominal discount factor `n = Λ/P` with
  `E_t dn = −i n dt` (1.26) satisfy the pricing condition with nominal surplus `Ps`; with it
  `rec_value` and `valuation_seq` are the stochastic A1.4 chain
  `d(ΛB/P) = −Λs dt` ⇔ `B/P = E_t∫(Λ_τ/Λ_t)s_τ dτ` (given the TVC). `shortDebt_step`: the book's
  middle line `Λ/P dB + B E_t d(Λ/P)` is the whole expected increment (bonds of bounded variation).
* Tools: `itoProcess_restrict` (an Itô process on `[s, t]` is one on every `[r, t'] ⊆ [s, t]`),
  and restatements of the Monetarism project's generic valuation lemmas (`rec_of_incr`,
  `valuation_iff_tvc_seq`, `valuation_iff_tvc_flow`).

Non-vacuity on the constructed Brownian motion is in `TidyR7ItoDiscountFactorCex`.
-/

namespace Cochrane.Generality.TidyR7ItoDiscountFactor

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Generality.TidyR7StieltjesSums Cochrane.Generality.TidyR7BrownianTools
  Cochrane.Generality.TidyR7BrownianQV Cochrane.Generality.TidyR7ItoL2
  Cochrane.Generality.TidyR7ItoSums Cochrane.Generality.TidyR7ItoIntegral
  Cochrane.Generality.TidyR7ItoUnbounded Cochrane.Generality.TidyR7ItoProducts
  Cochrane.Generality.TidyR7ItoProcess Cochrane.Generality.TidyR7ItoProductRule
  Cochrane.Generality.TidyR7ItoBondStep
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ## The pricing condition on the coefficients -/

/-- Cochrane (2023), A1.5, p. 566: **the book's expanded form of `E_t[d(ΛW)] = 0`.** For
`Λ, W ≠ 0`, `E_t[dΛ/Λ + dW/W + dΛdW/(ΛW)] = 0`, i.e. on the coefficients
`a_Λ/Λ + a_W/W + (σ_Λ/Λ)(σ_W/W) = 0`, is equivalent to the drift of `ΛW` vanishing,
`Λ a_W + W a_Λ + σ_Λσ_W = 0` (the product rule's `d(ΛW) = Λ dW + W dΛ + dΛ dW`). -/
theorem pricing_rate_iff {Λ W aΛ aW σΛ σW : ℝ} (hΛ : Λ ≠ 0) (hW : W ≠ 0) :
    aΛ / Λ + aW / W + σΛ / Λ * (σW / W) = 0 ↔ Λ * aW + W * aΛ + σΛ * σW = 0 := by
  have e : aΛ / Λ + aW / W + σΛ / Λ * (σW / W) = (Λ * aW + W * aΛ + σΛ * σW) / (Λ * W) := by
    field_simp
    ring
  rw [e, div_eq_zero_iff]
  exact ⟨fun h => h.resolve_right (mul_ne_zero hΛ hW), fun h => Or.inl h⟩

/-- Cochrane (2023), A1.5, p. 566: **`E_t[dΛ/Λ + dV/V + dΛdV/(ΛV)] = −(s/V) dt` on the
coefficients.** For `Λ, V ≠ 0`, `a_Λ/Λ + a_V/V + (σ_Λ/Λ)(σ_V/V) = −s/V` iff
`Λ a_V + V a_Λ + σ_Λσ_V = −Λ s` (the pricing condition of `ItoDiscountModel`). -/
theorem pricingV_rate_iff {Λ V aΛ aV σΛ σV sp : ℝ} (hΛ : Λ ≠ 0) (hV : V ≠ 0) :
    aΛ / Λ + aV / V + σΛ / Λ * (σV / V) = -(sp / V) ↔
      Λ * aV + V * aΛ + σΛ * σV = -(Λ * sp) := by
  have e : aΛ / Λ + aV / V + σΛ / Λ * (σV / V) + sp / V =
      (Λ * aV + V * aΛ + σΛ * σV + Λ * sp) / (Λ * V) := by
    field_simp
    ring
  constructor
  · intro h
    have h0 : aΛ / Λ + aV / V + σΛ / Λ * (σV / V) + sp / V = 0 := by rw [h]; ring
    rw [e, div_eq_zero_iff] at h0
    have := h0.resolve_right (mul_ne_zero hΛ hV)
    linarith
  · intro h
    have h0 : (Λ * aV + V * aΛ + σΛ * σV + Λ * sp) / (Λ * V) = 0 := by
      rw [show Λ * aV + V * aΛ + σΛ * σV + Λ * sp = 0 by linarith, zero_div]
    rw [← e] at h0
    linarith

/-- Cochrane (2023), A1.5, (1.27), p. 565: **the flow (1.27) on the coefficients.** For
`V, W ≠ 0`, `dV/V = −(s/V) dt + dW/W` (drift `a_V/V = −s/V + a_W/W`, diffusion
`σ_V/V = σ_W/W`) iff `W a_V = V a_W − W s` and `W σ_V = V σ_W`. The diffusion part is the book's
"`dV²/V² = dW dV/(WV) = dW²/W²`" (p. 565). -/
theorem flow_127_iff {V W aV aW σV σW sp : ℝ} (hV : V ≠ 0) (hW : W ≠ 0) :
    (aV / V = -(sp / V) + aW / W ∧ σV / V = σW / W) ↔
      (W * aV = V * aW - W * sp ∧ W * σV = V * σW) := by
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · field_simp at h1
      linarith
    · field_simp at h2
      linarith
  · rintro ⟨h1, h2⟩
    constructor
    · field_simp
      linarith
    · field_simp
      linarith

/-- **Cochrane (2023), A1.5, p. 566: from `E_t[d(ΛW)] = 0` and the flow (1.27) to
`E_t[d(ΛV)] = −Λ s dt`, on the coefficients.** If `W ≠ 0`, `Λ a_W + W a_Λ + σ_Λσ_W = 0` and
(1.27) holds (`W a_V = V a_W − W s`, `W σ_V = V σ_W`), then `Λ a_V + V a_Λ + σ_Λσ_V = −Λ s`:
the book's step "`E_t[dΛ/Λ + dV/V + dΛdV/(ΛV)] = −(s/V) dt`" with the covariation term. -/
theorem drift_of_flow_127 {Λ V W aΛ aV aW σΛ σV σW sp : ℝ} (hW : W ≠ 0)
    (hpr : Λ * aW + W * aΛ + σΛ * σW = 0) (ha : W * aV = V * aW - W * sp)
    (hσ : W * σV = V * σW) : Λ * aV + V * aΛ + σΛ * σV = -(Λ * sp) := by
  have h : W * (Λ * aV + V * aΛ + σΛ * σV + Λ * sp) = 0 := by
    linear_combination Λ * ha + σΛ * hσ + V * hpr
  have := (mul_eq_zero.1 h).resolve_left hW
  linarith

/-! ## Tools -/

variable {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ} {s t : ℝ}

/-- Cochrane (2023), §3.6, (3.44), p. 77: **an Itô process on `[s, t]` is an Itô process on
every `[r, t'] ⊆ [s, t]`** (same coefficients and bounds), `0 ≤ s`: `X_u = X_r + ∫_r^u a +
∫_r^u H dW` from additivity of both integrals (`TidyR7ItoIntegral.itoInt_add_itoInt`). -/
theorem itoProcess_restrict (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) {X a H : ℝ → Ω → ℝ} {Ca CH : ℝ}
    (hX : ItoProcess μ 𝓕 W X a H s t Ca CH) {r t' : ℝ} (hsr : s ≤ r) (hrt : r ≤ t')
    (ht' : t' ≤ t) : ItoProcess μ 𝓕 W X a H r t' Ca CH where
  adapted u hu := hX.adapted u ⟨hsr.trans hu.1, hu.2.trans ht'⟩
  init := hX.memLp hBM hWm h𝓕 hs ⟨hsr, hrt.trans ht'⟩
  drift := hX.drift.mono hsr ht'
  diff := hX.diff.mono hsr ht'
  eq u hu := by
    have hu' : u ∈ Set.Icc s t := ⟨hsr.trans hu.1, hu.2.trans ht'⟩
    have hr' : r ∈ Set.Icc s t := ⟨hsr, hrt.trans ht'⟩
    filter_upwards [hX.eq u hu', hX.eq r hr',
      itoInt_add_itoInt hBM hWm h𝓕 hs hsr hu.1 (hX.diff.mono le_rfl hu'.2), hX.drift.cont]
      with ω h1 h2 h3 h4
    rw [h1, h2, h3]
    have i1 : IntervalIntegrable (fun v => a v ω) volume s r :=
      ContinuousOn.intervalIntegrable_of_Icc hsr
        (h4.mono (Set.Icc_subset_Icc le_rfl (hrt.trans ht')))
    have i2 : IntervalIntegrable (fun v => a v ω) volume r u :=
      ContinuousOn.intervalIntegrable_of_Icc hu.1
        (h4.mono (Set.Icc_subset_Icc hsr (hu.2.trans ht')))
    rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
    ring

/-- Cochrane (2023), §3.6, (3.44), p. 77 (the `dt`-terms): **the mean-square time integral
depends only on the integrand on `[s, t]`**: if `G = K` on `[s, t]` then
`∫_s^t G du = ∫_s^t K du` (the Riemann sums only sample `[s, t]`). -/
theorem dtInt_congr {G K : ℝ → Ω → ℝ} (h : ∀ u ∈ Set.Icc s t, ∀ ω, G u ω = K u ω) :
    dtInt μ 𝓕 G s t = dtInt μ 𝓕 K s t := by
  have hs : ∀ p : Partition s t, dtSum G p = dtSum K p := fun p => funext fun ω => by
    simp only [dtSum, riemannSum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [h _ (t_mem p (Finset.mem_range.1 hi).le) ω]
  have hfun : (dtSum (s := s) (t := t) G) = dtSum K := funext hs
  unfold dtInt
  rw [hfun]

/-- Cochrane (2023), §3.6, (3.44), p. 77: **mean-square continuous integrands are determined by
their values on `[s, t]`**: if `G = K` on `[s, t]` and `G` is one, so is `K`. -/
theorem msIntegrand_congr {G K : ℝ → Ω → ℝ} (hG : MSIntegrand μ 𝓕 G s t)
    (h : ∀ u ∈ Set.Icc s t, ∀ ω, G u ω = K u ω) : MSIntegrand μ 𝓕 K s t where
  adapted u hu := by
    have e : K u = G u := funext fun ω => (h u hu ω).symm
    rw [e]
    exact hG.adapted u hu
  memLp u hu := by
    have e : K u = G u := funext fun ω => (h u hu ω).symm
    rw [e]
    exact hG.memLp u hu
  cont ε hε := by
    obtain ⟨δ, hδ, hc⟩ := hG.cont ε hε
    refine ⟨δ, hδ, fun u hu v hv huv => ?_⟩
    have e : (fun ω => (K u ω - K v ω) ^ 2) = fun ω => (G u ω - G v ω) ^ 2 :=
      funext fun ω => by rw [h u hu ω, h v hv ω]
    rw [e]
    exact hc u hu v hv huv

/-- Cochrane (2023), (3.31)–(3.36), pp. 70–75, and A1.5, p. 566 (from the expected-increment
identity to the finite-horizon budget): if `E_s[Y_T − Y_s] = −E_s[F]`, with `Y_s`
`𝓕_s`-measurable and `Y_T`, `Y_s` integrable, then `Y_s = E_s[Y_T] + E_s[F]` a.s.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7MonetarismValuation.rec_of_incr). -/
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

/-- **Cochrane (2023), (3.31)–(3.36), pp. 70–75, and A1.5, p. 566: valuation iff transversality,
limit form, with no convergence hypothesis.** If `Y_s = E_s[Y_T] + E_s[F_T]` for every `T ≥ s`,
then along any times `T_k ≥ s`: a.s. `E_s[F_{T_k}] → Y_s` iff a.s. `E_s[Y_{T_k}] → 0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7MonetarismValuation.valuation_iff_tvc_seq). -/
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

/-- **Cochrane (2023), (3.31)–(3.36), pp. 70–75, and A1.5, p. 566: valuation iff
transversality, `L¹` form.** If `Y_s = E_s[Y_T] + E_s[F_T]` for every `T ≥ s`, `Y_T`, `F_T` and
`G` are integrable and `F_T → G` in `L¹`, then `Y_s = E_s[G]` a.s. iff `E_s[Y_T] → 0` in `L¹`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7MonetarismValuation.valuation_iff_tvc_flow). -/
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

/-! ## The model -/

variable (μ 𝓕 W) (Λ V aΛ σΛ aV σV sp : ℝ → Ω → ℝ) (s t CΛ CΛσ CV CVσ : ℝ)

/-- **Cochrane (2023), §3.6, (3.31)–(3.36), (3.44), pp. 70–77, and A1.5, p. 566: the discount
factor and the value of debt as Itô processes on `[s, t]`.** `Λ` (drift `a_Λ`, diffusion `σ_Λ`)
and `V` (drift `a_V`, diffusion `σ_V`) are Itô processes driven by the same Brownian motion, and
the pricing condition `E_t[d(ΛV)] = −Λ s dt` holds on the coefficients:
`Λ a_V + V a_Λ + σ_Λσ_V = −Λ s`. With `s = 0` and `V = W` (the cumulative return) this is
`E_t[d(ΛW)] = 0`. -/
structure ItoDiscountModel where
  lam_ito : ItoProcess μ 𝓕 W Λ aΛ σΛ s t CΛ CΛσ
  val_ito : ItoProcess μ 𝓕 W V aV σV s t CV CVσ
  pricing : ∀ u ∈ Set.Icc s t, ∀ ω,
    Λ u ω * aV u ω + V u ω * aΛ u ω + σΛ u ω * σV u ω = -(Λ u ω * sp u ω)

variable {μ 𝓕 W Λ V aΛ σΛ aV σV sp s t CΛ CΛσ CV CVσ}

namespace ItoDiscountModel

/-- Cochrane (2023), A1.5, p. 566: **the model restricts to every `[r, t'] ⊆ [s, t]`**,
`0 ≤ s`. -/
theorem restrict (hm : ItoDiscountModel μ 𝓕 W Λ V aΛ σΛ aV σV sp s t CΛ CΛσ CV CVσ)
    (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration μ W 𝓕)
    (hs : 0 ≤ s) {r t' : ℝ} (hsr : s ≤ r) (hrt : r ≤ t') (ht' : t' ≤ t) :
    ItoDiscountModel μ 𝓕 W Λ V aΛ σΛ aV σV sp r t' CΛ CΛσ CV CVσ where
  lam_ito := itoProcess_restrict hBM hWm h𝓕 hs hm.lam_ito hsr hrt ht'
  val_ito := itoProcess_restrict hBM hWm h𝓕 hs hm.val_ito hsr hrt ht'
  pricing u hu := hm.pricing u ⟨hsr.trans hu.1, hu.2.trans ht'⟩

variable (hm : ItoDiscountModel μ 𝓕 W Λ V aΛ σΛ aV σV sp s t CΛ CΛσ CV CVσ)
include hm

/-- Cochrane (2023), A1.5, p. 566: the discounted surplus `Λ s` is a mean-square continuous
integrand on `[s, t]` (it equals `−(Λ a_V + V a_Λ + σ_Λσ_V)` by the pricing condition), so its
time integral `∫_s^t Λ s du` (`TidyR7ItoProducts.dtInt`) exists. -/
theorem msIntegrand_lamSp (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) :
    MSIntegrand μ 𝓕 (fun u ω => Λ u ω * sp u ω) s t := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have G1 := MSIntegrand.mul_itoIntegrand (hm.lam_ito.toMS hBM hWm h𝓕 hs) hm.val_ito.drift
  have G2 := MSIntegrand.mul_itoIntegrand (hm.val_ito.toMS hBM hWm h𝓕 hs) hm.lam_ito.drift
  have G3 := ItoIntegrand.toMS (itoIntegrand_mul hm.lam_ito.diff hm.val_ito.diff)
  have h := MSIntegrand.const_mul (MSIntegrand.add (MSIntegrand.add G1 G2) G3) (-1)
  refine msIntegrand_congr h fun u hu ω => ?_
  rw [hm.pricing u hu ω]
  ring

/-- **Cochrane (2023), A1.5, p. 566: `E_t[d(Λ_tV_t)] = −Λ_t s_t dt` with diffusions.** For
`0 ≤ s < t`, almost surely `E_s[Λ_tV_t − Λ_sV_s] = −E_s[∫_s^t Λ_u s_u du]`. From Itô's product
rule `d(ΛV) = Λ dV + V dΛ + dΛ dV` (`TidyR7ItoProductRule.condExp_product_rule`, bracket
`d[Λ, V] = σ_Λσ_V dt`) and the pricing condition.
Generalises the first part of `ContinuousLong.Lambda_valuation`. -/
theorem step (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t) :
    μ[fun ω => Λ t ω * V t ω - Λ s ω * V s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => -dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω) s t ω | 𝓕 s] := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have G1 := MSIntegrand.mul_itoIntegrand (hm.lam_ito.toMS hBM hWm h𝓕 hs) hm.val_ito.drift
  have G2 := MSIntegrand.mul_itoIntegrand (hm.val_ito.toMS hBM hWm h𝓕 hs) hm.lam_ito.drift
  have I3 := itoIntegrand_mul hm.lam_ito.diff hm.val_ito.diff
  have e3 := dtInt_ae_eq_integral hst.le (ItoIntegrand.toMS I3) I3.cont
  have a1 := dtInt_add G1 G2
  have a2 := dtInt_add (MSIntegrand.add G1 G2) (ItoIntegrand.toMS I3)
  have hfun : dtInt μ 𝓕 (fun u ω => (Λ u ω * aV u ω + V u ω * aΛ u ω) + σΛ u ω * σV u ω) s t
      = dtInt μ 𝓕 (fun u ω => -1 * (Λ u ω * sp u ω)) s t :=
    dtInt_congr fun u hu ω => by rw [hm.pricing u hu ω]; ring
  beta_reduce at a2
  rw [hfun] at a2
  have a3 := dtInt_const_mul (hm.msIntegrand_lamSp hBM hWm h𝓕 hs) (-1)
  refine (condExp_product_rule hBM hWm h𝓕 hs hst hm.lam_ito hm.val_ito).trans
    (condExp_congr_ae ?_)
  filter_upwards [e3, a1, a2, a3] with ω h3 h1 h2 h4
  simp only [Pi.add_apply] at h1 h2
  linarith

/-- **Cochrane (2023), A1.5, p. 566: the book's step without the covariation fails exactly when
the bracket is not zero.** For `0 ≤ s < t`, the bracket-free identity
`E_s[Λ_tV_t − Λ_sV_s] = E_s[∫Λ a_V du + ∫V a_Λ du]` (`Λ E_t dV + V E_t dΛ`) holds a.s. iff
`E_s[∫_s^t σ_Λσ_V du] = 0` a.s. The book writes the term `dΛ dV/(ΛV)`, so its A1.5 is right.
An instance of `TidyR7ItoProductRule.condExp_product_rule_bookForm_iff`. -/
theorem bookForm_iff (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t) :
    (μ[fun ω => Λ t ω * V t ω - Λ s ω * V s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => dtInt μ 𝓕 (fun u ω => Λ u ω * aV u ω) s t ω
        + dtInt μ 𝓕 (fun u ω => V u ω * aΛ u ω) s t ω | 𝓕 s]) ↔
      μ[fun ω => ∫ u in s..t, σΛ u ω * σV u ω | 𝓕 s] =ᵐ[μ] 0 :=
  condExp_product_rule_bookForm_iff hBM hWm h𝓕 hs hst hm.lam_ito hm.val_ito

omit hm in
/-- **Cochrane (2023), A1.5, p. 566: the basic pricing relation `E_t[d(Λ_tW_t)] = 0` with
diffusions.** If `Λ` and the cumulative return `W` (here the process `V`) satisfy the pricing
condition with zero surplus, `Λ a_W + W a_Λ + σ_Λσ_W = 0`, then for `0 ≤ s < t`,
`E_s[Λ_tW_t − Λ_sW_s] = 0` a.s.
Generalises `ContinuousLong.Lambda_W_const`. -/
theorem step_W (hm : ItoDiscountModel μ 𝓕 W Λ V aΛ σΛ aV σV (fun _ _ => 0) s t CΛ CΛσ CV CVσ)
    (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration μ W 𝓕)
    (hs : 0 ≤ s) (hst : s < t) :
    μ[fun ω => Λ t ω * V t ω - Λ s ω * V s ω | 𝓕 s] =ᵐ[μ] 0 := by
  refine (hm.step hBM hWm h𝓕 hs hst).trans ?_
  have z : dtInt μ 𝓕 (fun u ω => Λ u ω * (fun _ _ => (0 : ℝ)) u ω) s t =ᵐ[μ] 0 :=
    dtInt_of_eq_zero fun u _ ω => by simp
  have z' : (fun ω => -dtInt μ 𝓕 (fun u ω => Λ u ω * (fun _ _ => (0 : ℝ)) u ω) s t ω)
      =ᵐ[μ] (0 : Ω → ℝ) := by
    filter_upwards [z] with ω hω
    change -dtInt μ 𝓕 (fun u ω => Λ u ω * 0) s t ω = 0
    rw [hω, Pi.zero_apply, neg_zero]
  exact (condExp_congr_ae z').trans (by rw [condExp_zero])

omit hm in
/-- **Cochrane (2023), A1.5, p. 566: `Λ W` is a martingale on `[s, t]`.** Under the zero-surplus
pricing condition on `[s, t]`, `0 ≤ s`, for all `s ≤ r ≤ u ≤ t`, `E_r[Λ_uW_u] = Λ_rW_r` a.s.
Generalises `ContinuousLong.Lambda_W_const`. -/
theorem martingale_W
    (hm : ItoDiscountModel μ 𝓕 W Λ V aΛ σΛ aV σV (fun _ _ => 0) s t CΛ CΛσ CV CVσ)
    (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration μ W 𝓕)
    (hs : 0 ≤ s) {r u : ℝ} (hsr : s ≤ r) (hru : r ≤ u) (hut : u ≤ t) :
    μ[fun ω => Λ u ω * V u ω | 𝓕 r] =ᵐ[μ] fun ω => Λ r ω * V r ω := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have hr0 : 0 ≤ r := hs.trans hsr
  have hmr := hm.restrict hBM hWm h𝓕 hs hsr hru hut
  have hYr : StronglyMeasurable[𝓕 r] (fun ω => Λ r ω * V r ω) :=
    (hmr.lam_ito.adapted r ⟨le_rfl, hru⟩).mul (hmr.val_ito.adapted r ⟨le_rfl, hru⟩)
  have iu : Integrable (fun ω => Λ u ω * V u ω) μ :=
    (hmr.lam_ito.memLp hBM hWm h𝓕 hr0 ⟨hru, le_rfl⟩).integrable_mul
      (hmr.val_ito.memLp hBM hWm h𝓕 hr0 ⟨hru, le_rfl⟩)
  have ir : Integrable (fun ω => Λ r ω * V r ω) μ :=
    (hmr.lam_ito.memLp hBM hWm h𝓕 hr0 ⟨le_rfl, hru⟩).integrable_mul
      (hmr.val_ito.memLp hBM hWm h𝓕 hr0 ⟨le_rfl, hru⟩)
  rcases hru.lt_or_eq with hru' | hru'
  · have h0 := hmr.step_W hBM hWm h𝓕 hr0 hru'
    have h1 := condExp_sub (m := 𝓕 r) iu ir
    have h2 : μ[fun ω => Λ r ω * V r ω | 𝓕 r] = fun ω => Λ r ω * V r ω :=
      condExp_of_stronglyMeasurable (𝓕.le r) hYr ir
    filter_upwards [h0, h1] with ω e0 e1
    have e1' : μ[fun ω => Λ u ω * V u ω - Λ r ω * V r ω | 𝓕 r] ω =
        μ[fun ω => Λ u ω * V u ω | 𝓕 r] ω - Λ r ω * V r ω := by
      rw [show (fun ω => Λ u ω * V u ω - Λ r ω * V r ω) =
        (fun ω => Λ u ω * V u ω) - fun ω => Λ r ω * V r ω from rfl, e1, Pi.sub_apply, h2]
    rw [e1'] at e0
    simp only [Pi.zero_apply] at e0
    linarith
  · subst hru'
    rw [condExp_of_stronglyMeasurable (𝓕.le r) hYr ir]

omit hm in
/-- **Cochrane (2023), A1.4, p. 564: short-term debt, the book's middle line verbatim.** For the
nominal discount factor `n = Λ/P` (an Itô process with drift `ν`, diffusion `σ_n`) and nominal
debt `B` with no diffusion (`dB = β dt`), `0 ≤ s < t`: a.s.
`E_s[n_tB_t − n_sB_s] = E_s[∫ n β du + ∫ B ν du]`, i.e. `E_t d(ΛB/P) = (Λ/P) dB + B E_t d(Λ/P)`
with no covariation term (bonds of bounded variation).
An instance of `TidyR7ItoBondStep.bond_step_bv`. -/
theorem shortDebt_step {n B ν σn β : ℝ → Ω → ℝ} {Cν Cn Cβ : ℝ} (hBM : IsPreBrownianReal W μ)
    (hWm : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration μ W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    (hn : ItoProcess μ 𝓕 W n ν σn s t Cν Cn)
    (hB : ItoProcess μ 𝓕 W B β (fun _ _ => 0) s t Cβ 0) :
    μ[fun ω => n t ω * B t ω - n s ω * B s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => dtInt μ 𝓕 (fun u ω => n u ω * β u ω) s t ω
        + dtInt μ 𝓕 (fun u ω => B u ω * ν u ω) s t ω | 𝓕 s] := by
  have h := bond_step_bv hBM hWm h𝓕 hs hst hB hn (ae_of_all _ fun _ _ _ => rfl)
  have e : (fun ω => n t ω * B t ω - n s ω * B s ω) = fun ω => B t ω * n t ω - B s ω * n s ω :=
    funext fun ω => by ring
  rw [e]
  refine h.trans (condExp_congr_ae (ae_of_all _ fun ω => ?_))
  simp only
  ring

end ItoDiscountModel

/-! ## A1.4: short-term debt is an instance -/

/-- **Cochrane (2023), A1.4, (1.26), pp. 564–565, and (3.29)–(3.31), pp. 70–71: short-term debt
gives a pricing model.** If the nominal discount factor `n = Λ/P` is an Itô process with drift
`−i n` (`i dt = −E_t[d(Λ/P)]/(Λ/P)`, (1.26)) and diffusion `σ_n`, and nominal debt `B` follows
`dB = (iB − Ps) dt` (the flow `B i dt = P s dt + dB`, no diffusion), then `(n, B)` satisfy the
pricing condition with nominal surplus `P s`: `n·(iB − Ps) + B·(−in) + σ_n·0 = −n·(Ps)`.
With `n P = Λ`, `ItoDiscountModel.step` is `E_t d(ΛB/P) = −Λ s dt`. -/
theorem shortDebt_model {n B P i sp σn : ℝ → Ω → ℝ} {Cν Cn Cβ : ℝ}
    (hn : ItoProcess μ 𝓕 W n (fun u ω => -(i u ω * n u ω)) σn s t Cν Cn)
    (hB : ItoProcess μ 𝓕 W B (fun u ω => i u ω * B u ω - P u ω * sp u ω) (fun _ _ => 0) s t
      Cβ 0) :
    ItoDiscountModel μ 𝓕 W n B (fun u ω => -(i u ω * n u ω)) σn
      (fun u ω => i u ω * B u ω - P u ω * sp u ω) (fun _ _ => 0)
      (fun u ω => P u ω * sp u ω) s t Cν Cn Cβ 0 where
  lam_ito := hn
  val_ito := hB
  pricing _ _ _ := by ring

namespace ItoDiscountModel

/-! ## Valuation iff transversality -/

variable {CΛf CΛσf CVf CVσf : ℝ → ℝ}

/-- **Cochrane (2023), (3.31)–(3.36), pp. 70–75, and A1.5, p. 566: the finite-horizon value with
diffusions.** If the model holds on every `[s, T]`, `T > s` (bounds may depend on `T`), then for
every `T ≥ s`, a.s. `Λ_sV_s = E_s[Λ_TV_T] + E_s[∫_s^T Λ_u s_u du]`.
An instance of `rec_of_incr`. -/
theorem rec_value
    (hm : ∀ T, s < T → ItoDiscountModel μ 𝓕 W Λ V aΛ σΛ aV σV sp s T (CΛf T) (CΛσf T) (CVf T)
      (CVσf T))
    (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration μ W 𝓕)
    (hs : 0 ≤ s) {T : ℝ} (hT : s ≤ T) :
    (fun ω => Λ s ω * V s ω) =ᵐ[μ] μ[fun ω => Λ T ω * V T ω | 𝓕 s]
      + μ[dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω) s T | 𝓕 s] := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  have h1 := hm (s + 1) (by linarith)
  have hYs : StronglyMeasurable[𝓕 s] (fun ω => Λ s ω * V s ω) :=
    (h1.lam_ito.adapted s ⟨le_rfl, by linarith⟩).mul (h1.val_ito.adapted s ⟨le_rfl, by linarith⟩)
  have hYi : Integrable (fun ω => Λ s ω * V s ω) μ :=
    h1.lam_ito.init.integrable_mul h1.val_ito.init
  rcases hT.lt_or_eq with hT | hT
  · have hmT := hm T hT
    refine rec_of_incr (Y := fun T ω => Λ T ω * V T ω) (hmT.step hBM hWm h𝓕 hs hT) hYs hYi
      ((hmT.lam_ito.memLp hBM hWm h𝓕 hs ⟨hT.le, le_rfl⟩).integrable_mul
        (hmT.val_ito.memLp hBM hWm h𝓕 hs ⟨hT.le, le_rfl⟩))
  · subst hT
    rw [dtInt_of_le le_rfl, condExp_zero, condExp_of_stronglyMeasurable (𝓕.le s) hYs hYi]
    simp

/-- **Cochrane (2023), (3.31)–(3.36), pp. 70–75, and A1.5, p. 566 (`V_tΛ_t = ∫_t^∞ Λ_τ s_τ dτ`):
valuation iff transversality with diffusions, limit form.** Along any times `T_k ≥ s`: a.s.
`E_s[∫_s^{T_k} Λ s du] → Λ_sV_s` iff a.s. `E_s[Λ_{T_k}V_{T_k}] → 0`. No convergence
hypothesis on the flow is needed.
An instance of `valuation_iff_tvc_seq`; generalises the valuation part of
`ContinuousLong.Lambda_valuation`. -/
theorem valuation_seq
    (hm : ∀ T, s < T → ItoDiscountModel μ 𝓕 W Λ V aΛ σΛ aV σV sp s T (CΛf T) (CΛσf T) (CVf T)
      (CVσf T))
    (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration μ W 𝓕)
    (hs : 0 ≤ s) {T : ℕ → ℝ} (hT : ∀ k, s ≤ T k) :
    (∀ᵐ ω ∂μ, Tendsto (fun k => μ[dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω) s (T k) | 𝓕 s] ω)
      atTop (𝓝 (Λ s ω * V s ω))) ↔
      ∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => Λ (T k) ω * V (T k) ω | 𝓕 s] ω) atTop (𝓝 0) :=
  valuation_iff_tvc_seq (Y := fun T ω => Λ T ω * V T ω)
    (F := fun T => dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω) s T)
    (fun _ hT => rec_value hm hBM hWm h𝓕 hs hT) hT

/-- **Cochrane (2023), (3.31)–(3.36), pp. 70–75, and A1.5, p. 566: valuation iff
transversality with diffusions, `L¹` form.** If `∫_s^T Λ s du → G` in `L¹` (`G` integrable),
then `Λ_sV_s = E_s[G]` a.s. iff `E_s[Λ_TV_T] → 0` in `L¹`.
An instance of `valuation_iff_tvc_flow`. -/
theorem valuation_L1
    (hm : ∀ T, s < T → ItoDiscountModel μ 𝓕 W Λ V aΛ σΛ aV σV sp s T (CΛf T) (CΛσf T) (CVf T)
      (CVσf T))
    (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration μ W 𝓕)
    (hs : 0 ≤ s) {G : Ω → ℝ} (hG : Integrable G μ)
    (hconv : Tendsto (fun T => ∫ ω, |dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω) s T ω - G ω| ∂μ)
      atTop (𝓝 0)) :
    (fun ω => Λ s ω * V s ω) =ᵐ[μ] μ[G | 𝓕 s] ↔
      Tendsto (fun T => ∫ ω, |μ[fun ω => Λ T ω * V T ω | 𝓕 s] ω| ∂μ) atTop (𝓝 0) := by
  have : IsProbabilityMeasure μ := hBM.isGaussianProcess.isProbabilityMeasure
  refine valuation_iff_tvc_flow (Y := fun T ω => Λ T ω * V T ω)
    (F := fun T => dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω) s T)
    (fun _ hT => rec_value hm hBM hWm h𝓕 hs hT) (fun T hT => ?_) (fun T hT => ?_) hG hconv
  · rcases hT.lt_or_eq with hT | hT
    · exact ((hm T hT).lam_ito.memLp hBM hWm h𝓕 hs ⟨hT.le, le_rfl⟩).integrable_mul
        ((hm T hT).val_ito.memLp hBM hWm h𝓕 hs ⟨hT.le, le_rfl⟩)
    · subst hT
      have h1 := hm (s + 1) (by linarith)
      exact h1.lam_ito.init.integrable_mul h1.val_ito.init
  · rcases hT.lt_or_eq with hT | hT
    · exact (memLp_dtInt ((hm T hT).msIntegrand_lamSp hBM hWm h𝓕 hs)).integrable one_le_two
    · subst hT
      rw [dtInt_of_le le_rfl]
      exact integrable_zero _ _ _

/-- **Cochrane (2023), A1.5, p. 566, with the pathwise integral `∫_s^T Λ_u s_u du`.** If `Λ s`
has a.s. continuous paths on every `[s, T]`, the limit form of the valuation equation holds with
the pathwise discounted surplus: a.s. `E_s[∫_s^{T_k} Λ_u s_u du] → Λ_sV_s` iff a.s.
`E_s[Λ_{T_k}V_{T_k}] → 0`.
An instance of `valuation_iff_tvc_seq`. -/
theorem valuation_seq_pathwise
    (hm : ∀ T, s < T → ItoDiscountModel μ 𝓕 W Λ V aΛ σΛ aV σV sp s T (CΛf T) (CΛσf T) (CVf T)
      (CVσf T))
    (hBM : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration μ W 𝓕)
    (hs : 0 ≤ s)
    (hc : ∀ T, ∀ᵐ ω ∂μ, ContinuousOn (fun u => Λ u ω * sp u ω) (Set.Icc s T))
    {T : ℕ → ℝ} (hT : ∀ k, s ≤ T k) :
    (∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => ∫ u in s..T k, Λ u ω * sp u ω | 𝓕 s] ω)
      atTop (𝓝 (Λ s ω * V s ω))) ↔
      ∀ᵐ ω ∂μ, Tendsto (fun k => μ[fun ω => Λ (T k) ω * V (T k) ω | 𝓕 s] ω) atTop (𝓝 0) := by
  have key : ∀ k, μ[fun ω => ∫ u in s..T k, Λ u ω * sp u ω | 𝓕 s] =ᵐ[μ]
      μ[dtInt μ 𝓕 (fun u ω => Λ u ω * sp u ω) s (T k) | 𝓕 s] := by
    intro k
    rcases (hT k).lt_or_eq with hk | hk
    · exact condExp_congr_ae
        (dtInt_ae_eq_integral hk.le ((hm (T k) hk).msIntegrand_lamSp hBM hWm h𝓕 hs) (hc _)).symm
    · rw [← hk, dtInt_of_le le_rfl]
      simp only [intervalIntegral.integral_same]
      exact Filter.EventuallyEq.rfl
  have hall := ae_all_iff.2 key
  rw [← valuation_seq hm hBM hWm h𝓕 hs hT]
  constructor
  · intro h
    filter_upwards [h, hall] with ω h1 h2
    simp_rw [← h2]
    exact h1
  · intro h
    filter_upwards [h, hall] with ω h1 h2
    simp_rw [h2]
    exact h1

end ItoDiscountModel

end Cochrane.Generality.TidyR7ItoDiscountFactor
