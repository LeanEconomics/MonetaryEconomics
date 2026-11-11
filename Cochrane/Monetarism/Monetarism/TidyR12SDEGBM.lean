/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR12SDEGauss
import Mathlib.Algebra.Order.Chebyshev

/-!
# Geometric Brownian motion solves `dG = mG dt + σG dW`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.32)–(1.34) (Track 3, chunk B4). The positive diffusive
stochastic discount factor of §1.6 with a known interest rate and constant volatility is a
geometric Brownian motion, whose diffusion `σG` is unbounded, so it is outside
`TidyR7ItoProcess.ItoProcess`. Here

`G_u = ξ·exp(κ(u − s) + σ(W_u − W_s))`, `u ≥ s`

(`gbm`, `ξ` square integrable and `𝓕_s`-measurable) is shown to be an Itô process with
mean-square continuous coefficients (`TidyR12SDEProcess.ItoProcessMS`) with drift `mG` and
diffusion `σG`, `m = κ + σ²/2`, and identified with the solution of the SDE
`dX = mX dt + σX dW`, `X_s = ξ`, of `TidyR12SDEExist`.

## The route

Directly from the left-point sums, without an Itô formula for `exp`: along the dyadic partitions
of `[s, t]` (step `h`), `G_t − G_s = Σ G_{t_i}(e^{κh + σΔW_i} − 1) = m·ΣG_{t_i}h + σ·ΣG_{t_i}ΔW_i +
ΣG_{t_i}R_i` (`gbm_sub_eq_sum`), `R_i = e^{κh + σΔW_i} − 1 − mh − σΔW_i`. The first two sums
converge in `L²` to `∫ mG du` and `∫ σG dW`; the remainder `ΣG_{t_i}R_i` splits into orthogonal
martingale differences `G_{t_i}(R_i − E R_i)` and `E[R]·ΣG_{t_i}`, and `E[R], E[R²] = o(h)`
(`TidyR12SDEGauss.gbmMean_littleO`, `TidyR12SDEGauss.gbmSq_littleO`) send both to `0`.

## Main results

* `gbm_ms`: `G` is a mean-square continuous process on `[s, T]`; `integral_gbm_sq`
  (`E[G_u²] = E[ξ²]e^{(2κ + 2σ²)(u − s)}`).
* **`gbm_eq`**: `G_t − G_s = ∫_s^t mG du + ∫_s^t σG dW` a.s.; **`gbm_itoProcessMS`**.
* **`gbm_eq_sdeSol`**: `G` is the solution of `dX = mX dt + σX dW`, `X_s = ξ` (uniqueness,
  `TidyR12SDEPicard.sde_unique`).
* `gbm_pos` (positive when `ξ > 0`), **`condExp_gbm`** (`E_s[G_t] = e^{m(t − s)}G_s`).
* The exponential martingale `ξ·exp(σ(W_u − W_s) − σ²(u − s)/2)` (`κ = −σ²/2`, `m = 0`):
  `expMart_eq` (`dG = σG dW`), `condExp_expMart` (`E_s G_t = G_s`).
* `itoProcessMS_mul_bm`: `Y_u = u·W_u` is an `ItoProcessMS` with drift `W` and diffusion `u`
  (an unbounded drift).
* Non-vacuity on the constructed motion: `gbm_itoProcessMS_bmPath`, `expMart_eq_bmPath`,
  `gbm_eq_sdeSol_bmPath`.
-/

namespace Cochrane.Monetarism.TidyR12SDEGBM

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoSums Cochrane.Monetarism.TidyR7ItoIntegral
  Cochrane.Monetarism.TidyR7ItoUnbounded Cochrane.Monetarism.TidyR7ItoProducts
  Cochrane.Monetarism.TidyR7ItoProcess Cochrane.Monetarism.TidyR7ItoCovariation
  Cochrane.Monetarism.TidyR12SDETools Cochrane.Monetarism.TidyR12SDEProcess
  Cochrane.Monetarism.TidyR12SDEPicard Cochrane.Monetarism.TidyR12SDEExist
  Cochrane.Monetarism.TidyR12SDEGauss Cochrane.Monetarism.TidyR7ItoBondStep
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ}

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: geometric Brownian motion from `s`**,
`G_u = ξ·exp(κ(u − s) + σ(W_u − W_s))`. -/
noncomputable def gbm (W : ℝ≥0 → Ω → ℝ) (ξ : Ω → ℝ) (s κ σ : ℝ) (u : ℝ) (ω : Ω) : ℝ :=
  ξ ω * Real.exp (κ * (u - s) + σ * incr W s u ω)

variable {ξ : Ω → ℝ} {s κ σ : ℝ}

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `G_s = ξ`. -/
theorem gbm_self : gbm W ξ s κ σ s = ξ := by
  funext ω
  simp [gbm, incr_self]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the multiplicative step**,
`G_v = G_u·exp(κ(v − u) + σ(W_v − W_u))`. -/
theorem gbm_step (u v : ℝ) (ω : Ω) :
    gbm W ξ s κ σ v ω = gbm W ξ s κ σ u ω * Real.exp (κ * (v - u) + σ * incr W u v ω) := by
  simp only [gbm, incr, mul_assoc, ← Real.exp_add]
  ring_nf

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `G_u` is `𝓕_u`-strongly measurable for `u ≥ s`. -/
theorem stronglyMeasurable_gbm (h𝓕 : BMFiltration P W 𝓕) (hξ : StronglyMeasurable[𝓕 s] ξ)
    {u : ℝ} (hsu : s ≤ u) : StronglyMeasurable[𝓕 u] (gbm W ξ s κ σ u) :=
  (hξ.mono (𝓕.mono hsu)).mul (Real.continuous_exp.comp_stronglyMeasurable
    (stronglyMeasurable_const.add (stronglyMeasurable_const.mul (stronglyMeasurable_incr h𝓕 hsu))))

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `G_u` is square integrable for `0 ≤ s ≤ u`. -/
theorem memLp_gbm (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hξ2 : MemLp ξ 2 P) (hξ : StronglyMeasurable[𝓕 s] ξ)
    {u : ℝ} (hsu : s ≤ u) : MemLp (gbm W ξ s κ σ u) 2 P :=
  memLp_mul_fun_incr hW h𝓕 hsu hξ hξ2 (φ := fun z => Real.exp (κ * (u - s) + σ * z))
    (by fun_prop) (memLp_exp_incr hB hW hs hsu κ σ)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **`E[G_u²] = E[ξ²]·e^{(2κ + 2σ²)(u − s)}`**. -/
theorem integral_gbm_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hξ : StronglyMeasurable[𝓕 s] ξ) {u : ℝ}
    (hsu : s ≤ u) :
    ∫ ω, gbm W ξ s κ σ u ω ^ 2 ∂P
      = (∫ ω, ξ ω ^ 2 ∂P) * Real.exp ((2 * κ + 2 * σ ^ 2) * (u - s)) := by
  have hQ : StronglyMeasurable[𝓕 s] (fun ω => ξ ω ^ 2) := hξ.pow 2
  have h := integral_mul_fun_incr hW h𝓕 hsu hQ
    (φ := fun z => Real.exp (κ * (u - s) + σ * z) ^ 2) (by fun_prop)
  rw [integral_exp_incr_sq hB hs hsu] at h
  rw [← h]
  exact integral_congr_ae (ae_of_all _ fun ω => by simp only [gbm]; ring)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the mean-square increment**: for `s ≤ v ≤ u`,
`E[(G_u − G_v)²] = E[G_v²]·(e^{(2κ + 2σ²)(u − v)} − 2e^{m(u − v)} + 1)`, `m = κ + σ²/2`. -/
theorem integral_gbm_sub_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hξ : StronglyMeasurable[𝓕 s] ξ) {u v : ℝ}
    (hsv : s ≤ v) (hvu : v ≤ u) :
    ∫ ω, (gbm W ξ s κ σ u ω - gbm W ξ s κ σ v ω) ^ 2 ∂P
      = (∫ ω, gbm W ξ s κ σ v ω ^ 2 ∂P) * (Real.exp ((2 * κ + 2 * σ ^ 2) * (u - v))
        - 2 * Real.exp ((κ + σ ^ 2 / 2) * (u - v)) + 1) := by
  have hQ : StronglyMeasurable[𝓕 v] (fun ω => gbm W ξ s κ σ v ω ^ 2) :=
    (stronglyMeasurable_gbm (κ := κ) (σ := σ) h𝓕 hξ hsv).pow 2
  have h := integral_mul_fun_incr hW h𝓕 hvu hQ
    (φ := fun z => (Real.exp (κ * (u - v) + σ * z) - 1) ^ 2) (by fun_prop)
  rw [integral_exp_incr_sub_one_sq hB hW (hs.trans hsv) hvu] at h
  rw [← h]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp only
  rw [gbm_step v u ω]
  ring

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: geometric Brownian motion is a mean-square
continuous process** on `[s, T]`, `0 ≤ s` (adapted, square integrable, and
`E[(G_u − G_v)²] ≤ sup E[G²]·(e^{(2κ+2σ²)h} − 2e^{mh} + 1) → 0`). -/
theorem gbm_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hξ2 : MemLp ξ 2 P)
    (hξ : StronglyMeasurable[𝓕 s] ξ) (T : ℝ) : MSIntegrand P 𝓕 (gbm W ξ s κ σ) s T where
  adapted _ hu := stronglyMeasurable_gbm h𝓕 hξ hu.1
  memLp _ hu := memLp_gbm hB hW h𝓕 hs hξ2 hξ hu.1
  cont ε hε := by
    set M := (∫ ω, ξ ω ^ 2 ∂P) * Real.exp (|2 * κ + 2 * σ ^ 2| * (T - s)) with hM
    have hM0 : 0 ≤ M := mul_nonneg (integral_nonneg fun _ => sq_nonneg _) (Real.exp_pos _).le
    have hMb : ∀ v ∈ Set.Icc s T, ∫ ω, gbm W ξ s κ σ v ω ^ 2 ∂P ≤ M := by
      intro v hv
      rw [integral_gbm_sq hB hW h𝓕 hs hξ hv.1]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
        (integral_nonneg fun _ => sq_nonneg _)
      calc (2 * κ + 2 * σ ^ 2) * (v - s) ≤ |2 * κ + 2 * σ ^ 2| * (v - s) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (sub_nonneg.2 hv.1)
        _ ≤ |2 * κ + 2 * σ ^ 2| * (T - s) :=
            mul_le_mul_of_nonneg_left (by linarith only [hv.2]) (abs_nonneg _)
    set g : ℝ → ℝ := fun h => Real.exp ((2 * κ + 2 * σ ^ 2) * h)
      - 2 * Real.exp ((κ + σ ^ 2 / 2) * h) + 1 with hg
    have hgc : ContinuousAt g 0 := by
      simp only [hg]
      fun_prop
    have hg0 : g 0 = 0 := by simp only [hg]; norm_num
    obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.1 hgc (ε / (M + 1)) (by positivity)
    refine ⟨δ / 2, by positivity, fun u hu v hv huv => ?_⟩
    have key : ∀ a b, a ∈ Set.Icc s T → b ∈ Set.Icc s T → a ≤ b → b - a ≤ δ / 2 →
        ∫ ω, (gbm W ξ s κ σ b ω - gbm W ξ s κ σ a ω) ^ 2 ∂P ≤ ε := by
      intro a b ha hb hab hd
      rw [integral_gbm_sub_sq hB hW h𝓕 hs hξ ha.1 hab]
      have h1 : |g (b - a) - g 0| < ε / (M + 1) := by
        have := hδg (x := b - a) (by
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (sub_nonneg.2 hab)]
          linarith only [hd, hδ])
        rwa [Real.dist_eq] at this
      rw [hg0, sub_zero] at h1
      have h2 : g (b - a) ≤ ε / (M + 1) := (le_abs_self _).trans h1.le
      have h3 : 0 ≤ g (b - a) := by
        have := integral_exp_incr_sub_one_sq (P := P) hB hW (hs.trans ha.1) hab κ σ
        simp only [hg]
        rw [← this]
        exact integral_nonneg fun _ => sq_nonneg _
      calc (∫ ω, gbm W ξ s κ σ a ω ^ 2 ∂P) * g (b - a) ≤ M * (ε / (M + 1)) :=
            mul_le_mul (hMb a ha) h2 h3 hM0
        _ ≤ ε := by
            rw [mul_div_assoc']
            rw [div_le_iff₀ (by positivity)]
            nlinarith only [hε, hM0]
    rcases le_total u v with h | h
    · have e : ∫ ω, (gbm W ξ s κ σ u ω - gbm W ξ s κ σ v ω) ^ 2 ∂P
          = ∫ ω, (gbm W ξ s κ σ v ω - gbm W ξ s κ σ u ω) ^ 2 ∂P :=
        integral_congr_ae (ae_of_all _ fun ω => by ring)
      rw [e]
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)] at huv
      exact key u v hu hv h huv
    · rw [abs_of_nonneg (sub_nonneg.2 h)] at huv
      exact key v u hv hu h huv

/-! ## The left-point sums -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the remainder sum `Σ G_{t_i}R_i` of geometric Brownian
motion along a partition. -/
noncomputable def gbmRemSum (W : ℝ≥0 → Ω → ℝ) (ξ : Ω → ℝ) (s κ σ : ℝ) {a b : ℝ}
    (p : Partition a b) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range p.n, gbm W ξ s κ σ (p.t i) ω *
    gbmRem κ σ (p.t (i + 1) - p.t i) (incr W (p.t i) (p.t (i + 1)) ω)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the exact partition identity**: along every
partition of `[s, t]`, `G_t − G_s = m·ΣG_{t_i}Δt_i + σ·ΣG_{t_i}ΔW_i + ΣG_{t_i}R_i`. -/
theorem gbm_sub_eq_sum {t : ℝ} (p : Partition s t) (ω : Ω) :
    gbm W ξ s κ σ t ω - gbm W ξ s κ σ s ω
      = dtSum (fun u ω => (κ + σ ^ 2 / 2) * gbm W ξ s κ σ u ω) p ω
        + itoSum W (fun u ω => σ * gbm W ξ s κ σ u ω) p ω + gbmRemSum W ξ s κ σ p ω := by
  have tel := Finset.sum_range_sub (fun i => gbm W ξ s κ σ (p.t i) ω) p.n
  simp only [p.last, p.first] at tel
  rw [← tel]
  simp only [dtSum, riemannSum, itoSum, gbmRemSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gbm_step (p.t i) (p.t (i + 1)) ω]
  simp only [gbmRem]
  ring

/-- Cochrane (2023), A1 §1.6, p. 567: every dyadic step has length `(t − s)/2^k`. -/
lemma dyadic_step {t : ℝ} (hst : s < t) (k i : ℕ) :
    (dyadic hst k).t (i + 1) - (dyadic hst k).t i = (t - s) / 2 ^ k := by
  simp only [dyadic]
  push_cast
  ring

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the remainder bound** along the dyadic partitions
(step `h = (t − s)/2^k`, `n = 2^k`, `ρ = E[R]`): if `E[G_u²] ≤ M` on `[s, t]`,
`E[(ΣG_{t_i}R_i)²] ≤ 2nM(2|E[R²]| + 2ρ²) + 2ρ²n²M`. -/
theorem integral_gbmRemSum_sq_le (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hξ2 : MemLp ξ 2 P)
    (hξ : StronglyMeasurable[𝓕 s] ξ) {t : ℝ} (hst : s < t) (k : ℕ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ u ∈ Set.Icc s t, ∫ ω, gbm W ξ s κ σ u ω ^ 2 ∂P ≤ M) :
    ∫ ω, gbmRemSum W ξ s κ σ (dyadic hst k) ω ^ 2 ∂P
      ≤ 2 * ((2 ^ k : ℝ) * (M * (2 * |gbmSq κ σ ((t - s) / 2 ^ k)|
          + 2 * gbmMean κ σ ((t - s) / 2 ^ k) ^ 2)))
        + 2 * (gbmMean κ σ ((t - s) / 2 ^ k) ^ 2 * ((2 ^ k : ℝ) * ((2 ^ k : ℝ) * M))) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set p := dyadic hst k with hp
  set h := (t - s) / 2 ^ k with hh
  set ρ := gbmMean κ σ h with hρ
  have hstep : ∀ i, p.t (i + 1) - p.t i = h := fun i => dyadic_step hst k i
  have hn : p.n = 2 ^ k := rfl
  set G : ℕ → Ω → ℝ := fun i => gbm W ξ s κ σ (p.t i) with hG
  set Z : ℕ → Ω → ℝ := fun i => incr W (p.t i) (p.t (i + 1)) with hZ
  have hsi : ∀ i, i ≤ p.n → s ≤ p.t i := fun i hi => (t_mem p hi).1
  have hpos : ∀ i, 0 ≤ p.t i := fun i => by
    have := p.strictMono.monotone (Nat.zero_le i)
    rw [p.first] at this
    linarith only [this, hs]
  have mG : ∀ i, i ≤ p.n → MemLp (G i) 2 P := fun i hi =>
    memLp_gbm hB hW h𝓕 hs hξ2 hξ (hsi i hi)
  have sG : ∀ i, i ≤ p.n → StronglyMeasurable[𝓕 (p.t i)] (G i) := fun i hi =>
    stronglyMeasurable_gbm h𝓕 hξ (hsi i hi)
  have bG : ∀ i, i ≤ p.n → ∫ ω, G i ω ^ 2 ∂P ≤ M := fun i hi => hM _ (t_mem p hi)
  have mR : ∀ i, MemLp (fun ω => gbmRem κ σ h (Z i ω)) 2 P := fun i => by
    have := memLp_gbmRem hB hW (hpos i) (t_le_succ p i) κ σ (P := P)
    rwa [hstep] at this
  have iR : ∀ i, ∫ ω, gbmRem κ σ h (Z i ω) ∂P = ρ := fun i => by
    have := integral_gbmRem hB hW (hpos i) (t_le_succ p i) κ σ (P := P)
    rwa [hstep] at this
  have iR2 : ∀ i, ∫ ω, gbmRem κ σ h (Z i ω) ^ 2 ∂P = gbmSq κ σ h := fun i => by
    have := integral_gbmRem_sq hB hW (hpos i) (t_le_succ p i) κ σ (P := P)
    rwa [hstep] at this
  set V : ℕ → Ω → ℝ := fun i ω => G i ω * (gbmRem κ σ h (Z i ω) - ρ) with hV
  have hdec : ∀ ω, gbmRemSum W ξ s κ σ p ω
      = ∑ i ∈ Finset.range p.n, V i ω + ρ * ∑ i ∈ Finset.range p.n, G i ω := fun ω => by
    simp only [gbmRemSum, hstep, hV, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have mφ : ∀ i, MemLp (fun ω => gbmRem κ σ h (Z i ω) - ρ) 2 P := fun i =>
    (mR i).sub (memLp_const ρ)
  have mV : ∀ i < p.n, MemLp (V i) 2 P := fun i hi =>
    memLp_mul_fun_incr hW h𝓕 (t_le_succ p i) (sG i hi.le) (mG i hi.le)
      (φ := fun z => gbmRem κ σ h z - ρ) ((continuous_gbmRem κ σ h).measurable.sub_const ρ)
      (mφ i)
  have sV : ∀ i < p.n, StronglyMeasurable[𝓕 (p.t (i + 1))] (V i) := fun i hi =>
    ((sG i hi.le).mono (𝓕.mono (t_le_succ p i))).mul
      (((continuous_gbmRem κ σ h).comp_stronglyMeasurable
        (stronglyMeasurable_incr h𝓕 (t_le_succ p i))).sub stronglyMeasurable_const)
  have oV : ∀ i < p.n, ∀ Y : Ω → ℝ, StronglyMeasurable[𝓕 (p.t i)] Y → MemLp Y 2 P →
      ∫ ω, Y ω * V i ω ∂P = 0 := by
    intro i hi Y hY hY2
    have hQ : StronglyMeasurable[𝓕 (p.t i)] (fun ω => Y ω * G i ω) := hY.mul (sG i hi.le)
    have h1 : ∫ ω, (Y ω * G i ω) * (gbmRem κ σ h (Z i ω) - ρ) ∂P
        = (∫ ω, Y ω * G i ω ∂P) * ∫ ω, (gbmRem κ σ h (Z i ω) - ρ) ∂P :=
      integral_mul_fun_incr hW h𝓕 (t_le_succ p i) hQ
        ((continuous_gbmRem κ σ h).measurable.sub_const ρ)
    have h2 : ∫ ω, (gbmRem κ σ h (Z i ω) - ρ) ∂P = 0 := by
      rw [integral_sub ((mR i).integrable one_le_two) (integrable_const ρ), iR i]
      simp
    rw [h2, mul_zero] at h1
    rw [← h1]
    exact integral_congr_ae (ae_of_all _ fun ω => by simp only [hV]; ring)
  have hsumV := integral_sum_sq_of_orth (P := P) (𝓕 := 𝓕) p.strictMono.monotone p.n mV sV oV
  have bV : ∀ i < p.n, ∫ ω, V i ω ^ 2 ∂P ≤ M * (2 * |gbmSq κ σ h| + 2 * ρ ^ 2) := by
    intro i hi
    have hQ : StronglyMeasurable[𝓕 (p.t i)] (fun ω => G i ω ^ 2) := (sG i hi.le).pow 2
    have h1 : ∫ ω, G i ω ^ 2 * (gbmRem κ σ h (Z i ω) - ρ) ^ 2 ∂P
        = (∫ ω, G i ω ^ 2 ∂P) * ∫ ω, (gbmRem κ σ h (Z i ω) - ρ) ^ 2 ∂P :=
      integral_mul_fun_incr hW h𝓕 (t_le_succ p i) hQ
        (((continuous_gbmRem κ σ h).measurable.sub_const ρ).pow_const 2)
    have h2 : ∫ ω, (gbmRem κ σ h (Z i ω) - ρ) ^ 2 ∂P ≤ 2 * |gbmSq κ σ h| + 2 * ρ ^ 2 := by
      have i1 := (mR i).integrable_sq
      have i2 : Integrable (fun ω => 2 * gbmRem κ σ h (Z i ω) ^ 2 + 2 * ρ ^ 2) P :=
        (i1.const_mul 2).add (integrable_const _)
      have hle : ∫ ω, (gbmRem κ σ h (Z i ω) - ρ) ^ 2 ∂P
          ≤ ∫ ω, (2 * gbmRem κ σ h (Z i ω) ^ 2 + 2 * ρ ^ 2) ∂P :=
        integral_mono (mφ i).integrable_sq i2 fun ω => by
          nlinarith only [sq_nonneg (gbmRem κ σ h (Z i ω) + ρ)]
      have e : ∫ ω, (2 * gbmRem κ σ h (Z i ω) ^ 2 + 2 * ρ ^ 2) ∂P
          = 2 * gbmSq κ σ h + 2 * ρ ^ 2 := by
        rw [integral_add (i1.const_mul 2) (integrable_const _), integral_const_mul, iR2 i]
        simp
      rw [e] at hle
      linarith only [hle, le_abs_self (gbmSq κ σ h)]
    have h0 : 0 ≤ ∫ ω, (gbmRem κ σ h (Z i ω) - ρ) ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
    calc ∫ ω, V i ω ^ 2 ∂P = (∫ ω, G i ω ^ 2 ∂P) * ∫ ω, (gbmRem κ σ h (Z i ω) - ρ) ^ 2 ∂P := by
          rw [← h1]
          exact integral_congr_ae (ae_of_all _ fun ω => by simp only [hV]; ring)
      _ ≤ M * (2 * |gbmSq κ σ h| + 2 * ρ ^ 2) := mul_le_mul (bG i hi.le) h2 h0 hM0
  have mSV : MemLp (fun ω => ∑ i ∈ Finset.range p.n, V i ω) 2 P :=
    memLp_finsetSum _ fun i hi => mV i (Finset.mem_range.1 hi)
  have mSG : MemLp (fun ω => ρ * ∑ i ∈ Finset.range p.n, G i ω) 2 P :=
    (memLp_finsetSum _ fun i hi => mG i (Finset.mem_range.1 hi).le).const_mul ρ
  have b1 : ∫ ω, (∑ i ∈ Finset.range p.n, V i ω) ^ 2 ∂P
      ≤ (2 ^ k : ℝ) * (M * (2 * |gbmSq κ σ h| + 2 * ρ ^ 2)) := by
    rw [hsumV]
    refine (Finset.sum_le_sum fun i hi => bV i (Finset.mem_range.1 hi)).trans_eq ?_
    rw [Finset.sum_const, Finset.card_range, hn, nsmul_eq_mul]
    push_cast
    ring
  have b2 : ∫ ω, (ρ * ∑ i ∈ Finset.range p.n, G i ω) ^ 2 ∂P
      ≤ ρ ^ 2 * ((2 ^ k : ℝ) * ((2 ^ k : ℝ) * M)) := by
    have iG : Integrable (fun ω => ∑ i ∈ Finset.range p.n, G i ω ^ 2) P :=
      integrable_finsetSum _ fun i hi => (mG i (Finset.mem_range.1 hi).le).integrable_sq
    have hpt : ∀ ω, (ρ * ∑ i ∈ Finset.range p.n, G i ω) ^ 2
        ≤ ρ ^ 2 * ((2 ^ k : ℝ) * ∑ i ∈ Finset.range p.n, G i ω ^ 2) := fun ω => by
      rw [mul_pow]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      have := sq_sum_le_card_mul_sum_sq (s := Finset.range p.n) (f := fun i => G i ω)
      rw [Finset.card_range, hn] at this
      exact_mod_cast this
    refine (integral_mono mSG.integrable_sq ((iG.const_mul _).const_mul _) hpt).trans ?_
    rw [integral_const_mul, integral_const_mul, integral_finsetSum _ fun i hi =>
      (mG i (Finset.mem_range.1 hi).le).integrable_sq]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
      (sq_nonneg _)
    refine (Finset.sum_le_sum fun i hi => bG i (Finset.mem_range.1 hi).le).trans_eq ?_
    rw [Finset.sum_const, Finset.card_range, hn, nsmul_eq_mul]
    push_cast
    ring
  have e : ∫ ω, gbmRemSum W ξ s κ σ p ω ^ 2 ∂P = ∫ ω, (∑ i ∈ Finset.range p.n, V i ω
      + ρ * ∑ i ∈ Finset.range p.n, G i ω) ^ 2 ∂P :=
    integral_congr_ae (ae_of_all _ fun ω => by simp only [hdec ω])
  rw [e]
  have i1 : Integrable (fun ω => 2 * (∑ i ∈ Finset.range p.n, V i ω) ^ 2) P :=
    mSV.integrable_sq.const_mul 2
  have i2 : Integrable (fun ω => 2 * (ρ * ∑ i ∈ Finset.range p.n, G i ω) ^ 2) P :=
    mSG.integrable_sq.const_mul 2
  have hsq : ∫ ω, (∑ i ∈ Finset.range p.n, V i ω + ρ * ∑ i ∈ Finset.range p.n, G i ω) ^ 2 ∂P
      ≤ ∫ ω, (2 * (∑ i ∈ Finset.range p.n, V i ω) ^ 2
        + 2 * (ρ * ∑ i ∈ Finset.range p.n, G i ω) ^ 2) ∂P :=
    integral_mono (mSV.add mSG).integrable_sq (i1.add i2) fun ω => add_sq_le_two _ _
  rw [integral_add i1 i2, integral_const_mul, integral_const_mul] at hsq
  linarith only [hsq, b1, b2]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the remainder vanishes in mean square** along the
dyadic partitions of `[s, t]`, `0 ≤ s < t` (`E[R], E[R²] = o(h)` and `n h = t − s`). -/
theorem L2Tendsto_gbmRemSum (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hξ2 : MemLp ξ 2 P)
    (hξ : StronglyMeasurable[𝓕 s] ξ) {t : ℝ} (hst : s < t) :
    L2Tendsto P (fun k => gbmRemSum W ξ s κ σ (dyadic hst k)) 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨M, hM0, hM⟩ := exists_bound_integral_sq_ms (gbm_ms (κ := κ) (σ := σ) hB hW h𝓕 hs hξ2 hξ t)
  have hpos : ∀ (p : Partition s t) i, 0 ≤ p.t i := fun p i => by
    have := p.strictMono.monotone (Nat.zero_le i)
    rw [p.first] at this
    linarith only [this, hs]
  refine ⟨fun k => memLp_finsetSum _ fun i hi => memLp_mul_fun_incr hW h𝓕 (t_le_succ _ i)
    (stronglyMeasurable_gbm h𝓕 hξ (t_mem _ (Finset.mem_range.1 hi).le).1)
    (memLp_gbm hB hW h𝓕 hs hξ2 hξ (t_mem _ (Finset.mem_range.1 hi).le).1)
    (continuous_gbmRem κ σ _).measurable (memLp_gbmRem hB hW (hpos _ i) (t_le_succ _ i) κ σ),
    MemLp.zero, ?_⟩
  simp only [Pi.zero_apply, sub_zero]
  set B : ℕ → ℝ := fun k => 2 * ((2 ^ k : ℝ) * (M * (2 * |gbmSq κ σ ((t - s) / 2 ^ k)|
      + 2 * gbmMean κ σ ((t - s) / 2 ^ k) ^ 2)))
    + 2 * (gbmMean κ σ ((t - s) / 2 ^ k) ^ 2 * ((2 ^ k : ℝ) * ((2 ^ k : ℝ) * M))) with hBdef
  refine squeeze_zero (fun k => integral_nonneg fun _ => sq_nonneg _)
    (fun k => integral_gbmRemSum_sq_le hB hW h𝓕 hs hξ2 hξ hst k hM0 hM) ?_
  rw [Metric.tendsto_atTop]
  intro η hη
  set C := 8 * M * (t - s) + 2 * M * (t - s) ^ 2 + 1 with hC
  have hC0 : 0 < C := by
    have : 0 ≤ t - s := (sub_pos.2 hst).le
    positivity
  set ε := min 1 (η / (2 * C)) with hε
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεC : ε * C < η := by
    have h := min_le_right 1 (η / (2 * C))
    rw [← hε, le_div_iff₀ (by positivity)] at h
    linarith only [h, mul_pos hε0 hC0]
  obtain ⟨δ1, hδ1, h1⟩ := gbmSq_littleO κ σ hε0
  obtain ⟨δ2, hδ2, h2⟩ := gbmMean_littleO κ σ hε0
  have hh : Tendsto (fun k : ℕ => (t - s) / 2 ^ k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  obtain ⟨N, hN⟩ := (hh.eventually (gt_mem_nhds (lt_min (lt_min hδ1 hδ2) one_pos)))
    |>.exists_forall_of_atTop
  refine ⟨N, fun k hk => ?_⟩
  set h := (t - s) / 2 ^ k with hhdef
  have hh0 : 0 ≤ h := by
    have : 0 ≤ t - s := (sub_pos.2 hst).le
    positivity
  have hhN := hN k hk
  have hhδ1 : h ≤ δ1 := (hhN.le.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hhδ2 : h ≤ δ2 := (hhN.le.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hh1 : h ≤ 1 := hhN.le.trans (min_le_right _ _)
  have b1 := h1 h hh0 hhδ1
  have b2 := h2 h hh0 hhδ2
  have hnh : (2 ^ k : ℝ) * h = t - s := by
    rw [hhdef]
    field_simp
  have hρ2 : gbmMean κ σ h ^ 2 ≤ ε * h * (ε * h) := by
    have := pow_le_pow_left₀ (abs_nonneg _) b2 2
    rw [sq_abs] at this
    exact this.trans_eq (sq _)
  have hεh : ε * h ≤ 1 := by
    calc ε * h ≤ 1 * 1 := mul_le_mul hε1 hh1 hh0 zero_le_one
      _ = 1 := one_mul 1
  have hn0 : (0 : ℝ) ≤ 2 ^ k := by positivity
  have hB0 : 0 ≤ B k := by
    simp only [hBdef]
    positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hB0]
  have e1 : (2 ^ k : ℝ) * (M * (2 * |gbmSq κ σ h| + 2 * gbmMean κ σ h ^ 2))
      ≤ (2 ^ k : ℝ) * (M * (2 * (ε * h) + 2 * (ε * h))) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hM0) hn0
    have : ε * h * (ε * h) ≤ ε * h := mul_le_of_le_one_right (mul_nonneg hε0.le hh0) hεh
    linarith only [b1, hρ2, this]
  have e2 : gbmMean κ σ h ^ 2 * ((2 ^ k : ℝ) * ((2 ^ k : ℝ) * M))
      ≤ ε * h * (ε * h) * ((2 ^ k : ℝ) * ((2 ^ k : ℝ) * M)) :=
    mul_le_mul_of_nonneg_right hρ2 (by positivity)
  have e3 : (2 ^ k : ℝ) * (M * (2 * (ε * h) + 2 * (ε * h))) = 4 * ε * M * (t - s) := by
    rw [← hnh]
    ring
  have e4 : ε * h * (ε * h) * ((2 ^ k : ℝ) * ((2 ^ k : ℝ) * M)) = ε * ε * M * (t - s) ^ 2 := by
    rw [← hnh]
    ring
  have e5 : ε * ε * M * (t - s) ^ 2 ≤ ε * M * (t - s) ^ 2 := by
    have h0 : 0 ≤ M * (t - s) ^ 2 := by positivity
    have h1 : ε * ε ≤ ε := mul_le_of_le_one_left hε0.le hε1
    calc ε * ε * M * (t - s) ^ 2 = (ε * ε) * (M * (t - s) ^ 2) := by ring
      _ ≤ ε * (M * (t - s) ^ 2) := mul_le_mul_of_nonneg_right h1 h0
      _ = ε * M * (t - s) ^ 2 := by ring
  have hεCe : ε * C = 8 * (ε * M * (t - s)) + 2 * (ε * M * (t - s) ^ 2) + ε := by
    rw [hC]
    ring
  have hBk : B k ≤ ε * C := by
    simp only [hBdef, ← hhdef]
    have e3' : (2 ^ k : ℝ) * (M * (2 * (ε * h) + 2 * (ε * h))) = 4 * (ε * M * (t - s)) := by
      rw [e3]
      ring
    have e4' : ε * h * (ε * h) * ((2 ^ k : ℝ) * ((2 ^ k : ℝ) * M)) = ε * ε * M * (t - s) ^ 2 :=
      e4
    linarith only [e1, e2, e3', e4', e5, hεCe, hε0]
  linarith only [hBk, hεC]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: geometric Brownian motion solves
`dG = mG dt + σG dW`**, `m = κ + σ²/2`: for `0 ≤ s ≤ t`, a.s.
`G_t − G_s = ∫_s^t mG_u du + ∫_s^t σG_u dW`. -/
theorem gbm_eq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hξ2 : MemLp ξ 2 P)
    (hξ : StronglyMeasurable[𝓕 s] ξ) {t : ℝ} (hst : s ≤ t) :
    (fun ω => gbm W ξ s κ σ t ω - gbm W ξ s κ σ s ω) =ᵐ[P] fun ω =>
      dtInt P 𝓕 (fun u ω => (κ + σ ^ 2 / 2) * gbm W ξ s κ σ u ω) s t ω
        + itoInt P 𝓕 W (fun u ω => σ * gbm W ξ s κ σ u ω) s t ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rcases hst.lt_or_eq with hst | hst
  · have hG := gbm_ms (κ := κ) (σ := σ) hB hW h𝓕 hs hξ2 hξ t
    have h1 := L2Tendsto_dyadic_dt hst (MSIntegrand.const_mul hG (κ + σ ^ 2 / 2))
    have h2 := L2Tendsto_dyadic_ms hB hW h𝓕 hs hst (MSIntegrand.const_mul hG σ)
    have h3 := L2Tendsto_gbmRemSum (κ := κ) (σ := σ) hB hW h𝓕 hs hξ2 hξ hst
    have h4 := ((h1.add h2).add h3).congr_seq (fun k => ae_of_all _ fun ω =>
      (gbm_sub_eq_sum (dyadic hst k) ω).symm)
    have hm : MemLp (fun ω => gbm W ξ s κ σ t ω - gbm W ξ s κ σ s ω) 2 P :=
      (memLp_gbm hB hW h𝓕 hs hξ2 hξ hst.le).sub (memLp_gbm hB hW h𝓕 hs hξ2 hξ le_rfl)
    have h5 : L2Tendsto P (fun _ => fun ω => gbm W ξ s κ σ t ω - gbm W ξ s κ σ s ω)
        (fun ω => gbm W ξ s κ σ t ω - gbm W ξ s κ σ s ω) := ⟨fun _ => hm, hm, by simp⟩
    filter_upwards [ae_eq_of_L2Tendsto h5 h4] with ω h
    rw [h]
    simp
  · subst hst
    refine ae_of_all _ fun ω => ?_
    simp [dtInt_of_le, itoInt_of_le]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: geometric Brownian motion is an Itô process with
mean-square continuous coefficients** on `[s, T]`, `0 ≤ s`: drift `(κ + σ²/2)G`, diffusion
`σG` (both unbounded). -/
theorem gbm_itoProcessMS (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hξ2 : MemLp ξ 2 P)
    (hξ : StronglyMeasurable[𝓕 s] ξ) (T : ℝ) :
    ItoProcessMS P 𝓕 W (gbm W ξ s κ σ) (fun u ω => (κ + σ ^ 2 / 2) * gbm W ξ s κ σ u ω)
      (fun u ω => σ * gbm W ξ s κ σ u ω) s T := by
  have hG := gbm_ms (κ := κ) (σ := σ) hB hW h𝓕 hs hξ2 hξ T
  refine ⟨hG.adapted, memLp_gbm hB hW h𝓕 hs hξ2 hξ le_rfl, MSIntegrand.const_mul hG _,
    MSIntegrand.const_mul hG _, fun u hu => ?_⟩
  filter_upwards [gbm_eq hB hW h𝓕 hs hξ2 hξ hu.1] with ω h
  rw [add_assoc, ← h]
  ring

/-- Cochrane (2023), A1 §1.6, pp. 567–568: admissible coefficients stay admissible with a larger
Lipschitz constant. -/
theorem SDECoeff.mono_lip {b : ℝ → ℝ → ℝ} {T L L' K : ℝ} (hb : SDECoeff b s T L K)
    (hL : L ≤ L') : SDECoeff b s T L' K where
  lip u hu x y := (hb.lip u hu x y).trans (mul_le_mul_of_nonneg_right hL (abs_nonneg _))
  bound0 := hb.bound0
  time := hb.time

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: geometric Brownian motion is THE solution of
`dX = mX dt + σX dW`, `X_s = ξ`** (`m = κ + σ²/2`): it agrees a.s. at every `t ∈ [s, T]` with the
Picard solution `TidyR12SDEExist.sdeSol` (uniqueness, `TidyR12SDEPicard.sde_unique`). -/
theorem gbm_eq_sdeSol (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hξ2 : MemLp ξ 2 P)
    (hξ : StronglyMeasurable[𝓕 s] ξ) {T : ℝ} (hsT : s ≤ T) :
    ∀ t ∈ Set.Icc s T, gbm W ξ s κ σ t =ᵐ[P]
      sdeSol P 𝓕 W (fun _ x => (κ + σ ^ 2 / 2) * x) (fun _ x => σ * x) ξ s t := by
  have hb := SDECoeff.mono_lip (sdeCoeff_const_mul (s := s) (T := T) (κ + σ ^ 2 / 2))
    (le_add_of_nonneg_right (abs_nonneg σ))
  have hσ := SDECoeff.mono_lip (sdeCoeff_const_mul (s := s) (T := T) σ)
    (le_add_of_nonneg_left (abs_nonneg (κ + σ ^ 2 / 2)))
  refine sde_unique hB hW h𝓕 hs hsT hb hσ (gbm_ms hB hW h𝓕 hs hξ2 hξ T)
    (sdeSol_ms hB hW h𝓕 hs hsT hb hσ hξ2 hξ) (fun t ht => ?_)
    (sdeSol_fixed hB hW h𝓕 hs hsT hb hσ hξ2 hξ)
  filter_upwards [gbm_eq (κ := κ) (σ := σ) hB hW h𝓕 hs hξ2 hξ ht.1] with ω h
  have h0 : gbm W ξ s κ σ s ω = ξ ω := congrFun gbm_self ω
  simp only [picard]
  rw [← h0, add_assoc, ← h]
  ring

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **geometric Brownian motion is positive** when
`ξ > 0`. -/
theorem gbm_pos (hξ0 : ∀ ω, 0 < ξ ω) (u : ℝ) (ω : Ω) : 0 < gbm W ξ s κ σ u ω :=
  mul_pos (hξ0 ω) (Real.exp_pos _)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `E_s[G_t] = e^{m(t − s)}G_s`** for `0 ≤ s ≤ t`,
`m = κ + σ²/2` (pull out `ξ`; the increment is independent of `𝓕_s`). -/
theorem condExp_gbm (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hξ2 : MemLp ξ 2 P)
    (hξ : StronglyMeasurable[𝓕 s] ξ) {t : ℝ} (hst : s ≤ t) :
    P[gbm W ξ s κ σ t | 𝓕 s] =ᵐ[P]
      fun ω => Real.exp ((κ + σ ^ 2 / 2) * (t - s)) * gbm W ξ s κ σ s ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set g : Ω → ℝ := fun ω => Real.exp (κ * (t - s) + σ * incr W s t ω) with hg
  have hφ : Measurable fun z : ℝ => Real.exp (κ * (t - s) + σ * z) := by fun_prop
  have ig : Integrable g P := (memLp_exp_incr hB hW hs hst κ σ).integrable one_le_two
  have e : gbm W ξ s κ σ t = ξ * g := rfl
  have hgm : StronglyMeasurable[MeasurableSpace.comap (incr W s t) inferInstance] g :=
    (hφ.comp (comap_measurable (incr W s t))).stronglyMeasurable
  have h1 := condExp_mul_of_stronglyMeasurable_left (m := 𝓕 s) hξ
    (by rw [← e]; exact (memLp_gbm hB hW h𝓕 hs hξ2 hξ hst).integrable one_le_two) ig
  have h2 := condExp_indep_eq (μ := P) (measurable_incr hW s t).comap_le (𝓕.le s) hgm
    (h𝓕.indep s t hst)
  rw [e]
  filter_upwards [h1, h2] with ω h1 h2
  rw [h1, Pi.mul_apply, h2, hg, integral_exp_incr hB hs hst, congrFun gbm_self ω]
  ring

/-! ## The exponential martingale -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the exponential martingale solves `dG = σG dW`**:
for `G_u = ξ·exp(σ(W_u − W_s) − σ²(u − s)/2)` (`κ = −σ²/2`) and `0 ≤ s ≤ t`, a.s.
`G_t − G_s = ∫_s^t σG dW`. -/
theorem expMart_eq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hξ2 : MemLp ξ 2 P)
    (hξ : StronglyMeasurable[𝓕 s] ξ) {t : ℝ} (hst : s ≤ t) :
    (fun ω => gbm W ξ s (-(σ ^ 2 / 2)) σ t ω - gbm W ξ s (-(σ ^ 2 / 2)) σ s ω) =ᵐ[P]
      fun ω => itoInt P 𝓕 W (fun u ω => σ * gbm W ξ s (-(σ ^ 2 / 2)) σ u ω) s t ω := by
  have h0 : dtInt P 𝓕 (fun u ω => (-(σ ^ 2 / 2) + σ ^ 2 / 2) * gbm W ξ s (-(σ ^ 2 / 2)) σ u ω)
      s t =ᵐ[P] 0 := dtInt_of_eq_zero fun u _ ω => by ring
  filter_upwards [gbm_eq (κ := -(σ ^ 2 / 2)) (σ := σ) hB hW h𝓕 hs hξ2 hξ hst, h0] with ω h1 h2
  rw [h1, h2]
  simp

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the exponential martingale property for an
admissible filtration**: `E_s[G_t] = G_s` for `G_u = ξ·exp(σ(W_u − W_s) − σ²(u − s)/2)`,
`0 ≤ s ≤ t`. Generalises `TidyR9ExpMartingale.condExp_exp_increment` (natural filtration,
`ξ = 1`). -/
theorem condExp_expMart (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hξ2 : MemLp ξ 2 P)
    (hξ : StronglyMeasurable[𝓕 s] ξ) {t : ℝ} (hst : s ≤ t) :
    P[gbm W ξ s (-(σ ^ 2 / 2)) σ t | 𝓕 s] =ᵐ[P] gbm W ξ s (-(σ ^ 2 / 2)) σ s := by
  filter_upwards [condExp_gbm (κ := -(σ ^ 2 / 2)) (σ := σ) hB hW h𝓕 hs hξ2 hξ hst] with ω h
  rw [h]
  simp

/-! ## An unbounded drift: `u·W_u` -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the deterministic integrand `u ↦ u` is admissible on
`[s, t]` (bounded by `|s| + |t|`). -/
theorem itoIntegrand_id {s t : ℝ} :
    ItoIntegrand P 𝓕 (fun u _ => u) s t (|s| + |t|) where
  adapted _ _ := stronglyMeasurable_const
  bound u hu _ := by
    rcases le_total 0 u with h | h
    · rw [abs_of_nonneg h]
      linarith [le_abs_self t, abs_nonneg s, hu.2]
    · rw [abs_of_nonpos h]
      linarith [neg_abs_le s, abs_nonneg t, hu.1]
  cont := ae_of_all _ fun _ => continuousOn_id

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `Y_u = u·W_u` is an Itô process with mean-square
continuous coefficients** on `[s, t]`, `0 ≤ s`: drift `W` (unbounded) and diffusion `u`
(`d(uW) = W du + u dW`, from `TidyR7ItoProductRule.product_rule_bm_id`). -/
theorem itoProcessMS_mul_bm (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (t : ℝ) :
    ItoProcessMS P 𝓕 W (fun u ω => bmReal W u ω * u) (bmReal W) (fun u _ => u) s t := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨fun u _ => (h𝓕.adapted u).mul stronglyMeasurable_const,
    ((hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two).mul_const _,
    (TidyR7ItoProductRule.itoProcess_bm hB hW h𝓕 hs).toMS hB hW h𝓕 hs,
    ItoIntegrand.toMS itoIntegrand_id, fun u hu => ?_⟩
  rcases hu.1.lt_or_eq with hsu | hsu
  · filter_upwards [TidyR7ItoProductRule.product_rule_bm_id (t := u) hB hW h𝓕 hs hsu] with ω h
    linarith
  · subst hsu
    refine ae_of_all _ fun ω => ?_
    simp [dtInt_of_le, itoInt_of_le]

/-! ## Non-vacuity on the constructed motion -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (non-vacuity): on the constructed Brownian motion
`TidyR7BrownianExist.bmPath` with its natural filtration, `G_u = exp(κu + σW_u)` (`ξ = 1`,
`s = 0`) is an `ItoProcessMS` on `[0, T]` with drift `(κ + σ²/2)G` and diffusion `σG`. -/
theorem gbm_itoProcessMS_bmPath (κ σ T : ℝ) :
    ItoProcessMS TidyR7BrownianSchauder.gaussSeq
      (bmFiltrationReal TidyR7BrownianExist.bmPath TidyR7BrownianExist.measurable_bmPath)
      TidyR7BrownianExist.bmPath (gbm TidyR7BrownianExist.bmPath (fun _ => 1) 0 κ σ)
      (fun u ω => (κ + σ ^ 2 / 2) * gbm TidyR7BrownianExist.bmPath (fun _ => 1) 0 κ σ u ω)
      (fun u ω => σ * gbm TidyR7BrownianExist.bmPath (fun _ => 1) 0 κ σ u ω) 0 T := by
  have : IsProbabilityMeasure TidyR7BrownianSchauder.gaussSeq :=
    TidyR7BrownianExist.isPreBrownianReal_bmPath.isGaussianProcess.isProbabilityMeasure
  exact gbm_itoProcessMS TidyR7BrownianExist.isPreBrownianReal_bmPath
    TidyR7BrownianExist.measurable_bmPath
    (bmFiltrationReal_isBM TidyR7BrownianExist.isPreBrownianReal_bmPath
      TidyR7BrownianExist.measurable_bmPath) le_rfl (memLp_const 1) stronglyMeasurable_const T

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (non-vacuity): on the constructed motion, the
exponential martingale `G_u = exp(σW_u − σ²u/2)` satisfies `G_1 − G_0 = ∫_0^1 σG dW` a.s. -/
theorem expMart_eq_bmPath (σ : ℝ) :
    (fun ω => gbm TidyR7BrownianExist.bmPath (fun _ => 1) 0 (-(σ ^ 2 / 2)) σ 1 ω
      - gbm TidyR7BrownianExist.bmPath (fun _ => 1) 0 (-(σ ^ 2 / 2)) σ 0 ω)
      =ᵐ[TidyR7BrownianSchauder.gaussSeq] fun ω => itoInt TidyR7BrownianSchauder.gaussSeq
        (bmFiltrationReal TidyR7BrownianExist.bmPath TidyR7BrownianExist.measurable_bmPath)
        TidyR7BrownianExist.bmPath
        (fun u ω => σ * gbm TidyR7BrownianExist.bmPath (fun _ => 1) 0 (-(σ ^ 2 / 2)) σ u ω)
        0 1 ω := by
  have : IsProbabilityMeasure TidyR7BrownianSchauder.gaussSeq :=
    TidyR7BrownianExist.isPreBrownianReal_bmPath.isGaussianProcess.isProbabilityMeasure
  exact expMart_eq TidyR7BrownianExist.isPreBrownianReal_bmPath
    TidyR7BrownianExist.measurable_bmPath
    (bmFiltrationReal_isBM TidyR7BrownianExist.isPreBrownianReal_bmPath
      TidyR7BrownianExist.measurable_bmPath) le_rfl (memLp_const 1) stronglyMeasurable_const
    zero_le_one

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (non-vacuity of `TidyR12SDEExist.sde_existsUnique`): on
the constructed motion, the Picard solution of `dX = mX dt + σX dW`, `X_0 = 1`, is
`exp(κu + σW_u)`, `m = κ + σ²/2`, a.s. at every `t ∈ [0, T]`, `T ≥ 0`. -/
theorem gbm_eq_sdeSol_bmPath (κ σ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∀ t ∈ Set.Icc 0 T, gbm TidyR7BrownianExist.bmPath (fun _ => 1) 0 κ σ t
      =ᵐ[TidyR7BrownianSchauder.gaussSeq] sdeSol TidyR7BrownianSchauder.gaussSeq
        (bmFiltrationReal TidyR7BrownianExist.bmPath TidyR7BrownianExist.measurable_bmPath)
        TidyR7BrownianExist.bmPath (fun _ x => (κ + σ ^ 2 / 2) * x) (fun _ x => σ * x)
        (fun _ => 1) 0 t := by
  have : IsProbabilityMeasure TidyR7BrownianSchauder.gaussSeq :=
    TidyR7BrownianExist.isPreBrownianReal_bmPath.isGaussianProcess.isProbabilityMeasure
  exact gbm_eq_sdeSol TidyR7BrownianExist.isPreBrownianReal_bmPath
    TidyR7BrownianExist.measurable_bmPath
    (bmFiltrationReal_isBM TidyR7BrownianExist.isPreBrownianReal_bmPath
      TidyR7BrownianExist.measurable_bmPath) le_rfl (memLp_const 1) stronglyMeasurable_const hT

end Cochrane.Monetarism.TidyR12SDEGBM
