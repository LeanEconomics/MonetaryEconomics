/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR12SDEProcess
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Existence and uniqueness for stochastic differential equations with Lipschitz coefficients

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34) (Track 3, chunk B4). The §1.6 economy
specifies `Λ/P`, bonds and money by their stochastic differentials; this module shows that
such equations have solutions. For

`dX = b(t, X) dt + σ(t, X) dW` on `[s, T]`, `X_s = ξ`,

with `0 ≤ s ≤ T`, `ξ` square integrable and `𝓕_s`-measurable, and coefficients satisfying
`SDECoeff` (Lipschitz in `x` uniformly in `t ∈ [s, T]`, `|b(t, 0)| ≤ K`, and continuous in `t`
uniformly against the linear-growth weight `1 + |x|`), there is a solution and it is unique
among mean-square continuous solutions.

## The setting

Processes are mean-square continuous (`TidyR7ItoUnbounded.MSIntegrand`), so the integrals are
the mean-square time integral `TidyR7ItoProducts.dtInt` and the Itô integral
`TidyR7ItoIntegral.itoInt`. A **solution** is an `MSIntegrand` `X` on `[s, T]` with, for every
`t ∈ [s, T]`, almost surely `X_t = ξ + ∫_s^t b(u, X_u) du + ∫_s^t σ(u, X_u) dW`
(`X_t = picard … X t` a.s.). Uniqueness is among such solutions. The time-continuity condition
on the coefficients is what makes `u ↦ b(u, X_u)` mean-square continuous; it holds for every
coefficient that does not depend on `t`, and for `α(t) + β(t)x` with `α, β` continuous
(`sdeCoeff_linear`).

## Main results

* `SDECoeff.msIntegrand_comp`: `u ↦ b(u, X_u)` is mean-square continuous for mean-square
  continuous `X`.
* `picard`, `picard_itoProcessMS`: the Picard map, whose values are Itô processes with
  mean-square continuous coefficients (`TidyR12SDEProcess.ItoProcessMS`).
* `picard_sub_sq_le` (**the contraction estimate**):
  `E[(Φ(X)_t − Φ(Y)_t)²] ≤ 2L²(T − s + 1)∫_s^t E[(X_u − Y_u)²] du`.
* `iterate_bound`: `f_{n+1}(t) ≤ K∫_s^t f_n` and `f_0 ≤ M` give
  `f_n(t) ≤ M(K(t − s))ⁿ/n!` (the Gronwall iteration).
* `sde_unique` (**uniqueness**); existence is in `TidyR12SDEExist` (`TidyR12SDEExist.picardSeq`,
  `TidyR12SDEExist.sdeSol`, **`TidyR12SDEExist.sde_existsUnique`**,
  `TidyR12SDEExist.sdeSol_itoProcessMS`: the solution is an `ItoProcessMS` with drift
  `b(u, X_u)` and diffusion `σ(u, X_u)`).
* `sdeCoeff_linear`, `sdeCoeff_const_mul`: the linear coefficients `α(t) + β(t)x`, in
  particular `m·x` and `σ·x` of geometric Brownian motion (`TidyR12SDEGBM`).
-/

namespace Cochrane.Monetarism.TidyR12SDEPicard

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoSums Cochrane.Monetarism.TidyR7ItoIntegral
  Cochrane.Monetarism.TidyR7ItoUnbounded Cochrane.Monetarism.TidyR7ItoProducts
  Cochrane.Monetarism.TidyR7ItoProcess Cochrane.Monetarism.TidyR8MonetarismItoDom
  Cochrane.Monetarism.TidyR10DoobFubini Cochrane.Monetarism.TidyR12SDETools
  Cochrane.Monetarism.TidyR12SDEProcess
open scoped ENNReal NNReal Nat

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ## Coefficients -/

variable (b : ℝ → ℝ → ℝ) (s T L K : ℝ)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: admissible SDE coefficients on `[s, T]`** (the drift
and diffusion of `dX = b(t, X)dt + σ(t, X)dW`): Lipschitz in `x` with constant `L` uniformly in
`t ∈ [s, T]`, `|b(t, 0)| ≤ K` (hence linear growth), and continuous in `t` uniformly against the
weight `1 + |x|`: for `ε > 0` there is `δ > 0` with `|b(u, x) − b(v, x)| ≤ ε(1 + |x|)` whenever
`u, v ∈ [s, T]`, `|u − v| ≤ δ`. -/
structure SDECoeff where
  lip : ∀ u ∈ Set.Icc s T, ∀ x y, |b u x - b u y| ≤ L * |x - y|
  bound0 : ∀ u ∈ Set.Icc s T, |b u 0| ≤ K
  time : ∀ ε > 0, ∃ δ > 0, ∀ u ∈ Set.Icc s T, ∀ v ∈ Set.Icc s T, |u - v| ≤ δ →
    ∀ x, |b u x - b v x| ≤ ε * (1 + |x|)

variable {b s T L K}

/-- Cochrane (2023), A1 §1.6, pp. 567–568: an admissible coefficient is continuous in `x`
(Lipschitz). -/
theorem SDECoeff.continuous (hb : SDECoeff b s T L K) {u : ℝ} (hu : u ∈ Set.Icc s T) :
    Continuous (b u) :=
  (LipschitzWith.of_dist_le_mul (K := L.toNNReal) fun x y => by
    rw [Real.dist_eq, Real.dist_eq]
    exact (hb.lip u hu x y).trans
      (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) (abs_nonneg _))).continuous

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **linear growth**, `|b(u, x)| ≤ K + L|x|`. -/
theorem SDECoeff.abs_le (hb : SDECoeff b s T L K) {u : ℝ} (hu : u ∈ Set.Icc s T) (x : ℝ) :
    |b u x| ≤ K + L * |x| := by
  have h1 := hb.lip u hu x 0
  have h2 := hb.bound0 u hu
  rw [sub_zero] at h1
  calc |b u x| = |(b u x - b u 0) + b u 0| := by ring_nf
    _ ≤ |b u x - b u 0| + |b u 0| := abs_add_le _ _
    _ ≤ K + L * |x| := by linarith

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `(b(u, x) − b(u, y))² ≤ L²(x − y)²`. -/
theorem SDECoeff.sq_sub_le (hb : SDECoeff b s T L K) {u : ℝ} (hu : u ∈ Set.Icc s T) (x y : ℝ) :
    (b u x - b u y) ^ 2 ≤ L ^ 2 * (x - y) ^ 2 := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (hb.lip u hu x y) 2
  rwa [sq_abs, mul_pow, sq_abs] at h

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `b(u, Z)` is square integrable for square-integrable
measurable `Z` (linear growth). -/
theorem SDECoeff.memLp_comp {P : Measure Ω} [IsFiniteMeasure P] (hb : SDECoeff b s T L K)
    {u : ℝ} (hu : u ∈ Set.Icc s T) {Z : Ω → ℝ} (hZm : Measurable Z) (hZ : MemLp Z 2 P) :
    MemLp (fun ω => b u (Z ω)) 2 P := by
  refine MemLp.of_le ((memLp_const |K|).add (hZ.abs.const_mul |L|))
    ((hb.continuous hu).measurable.comp hZm).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  have h := hb.abs_le hu (Z ω)
  have hK := le_abs_self K
  have hL : L * |Z ω| ≤ |L| * |Z ω| := mul_le_mul_of_nonneg_right (le_abs_self L) (abs_nonneg _)
  simp only [Real.norm_eq_abs, Pi.add_apply, Pi.abs_apply]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |K| + |L| * |Z ω|)]
  linarith

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `E[(b(u, Z) − b(u, Z'))²] ≤ L²E[(Z − Z')²]`. -/
theorem SDECoeff.integral_sq_sub_comp_le {P : Measure Ω} [IsFiniteMeasure P]
    (hb : SDECoeff b s T L K) {u : ℝ} (hu : u ∈ Set.Icc s T) {Z Z' : Ω → ℝ}
    (hZm : Measurable Z) (hZ : MemLp Z 2 P) (hZm' : Measurable Z') (hZ' : MemLp Z' 2 P) :
    ∫ ω, (b u (Z ω) - b u (Z' ω)) ^ 2 ∂P ≤ L ^ 2 * ∫ ω, (Z ω - Z' ω) ^ 2 ∂P := by
  rw [← integral_const_mul]
  exact integral_mono ((hb.memLp_comp hu hZm hZ).sub (hb.memLp_comp hu hZm' hZ')).integrable_sq
    ((hZ.sub hZ').integrable_sq.const_mul _) fun ω => hb.sq_sub_le hu _ _

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `u ↦ b(u, X_u)` is a mean-square continuous
integrand** on `[s, T]` when `X` is one (adapted by continuity of `b(u, ·)`; square integrable by
linear growth; `E[(b(u, X_u) − b(v, X_v))²] ≤ 2ε²E[(1 + |X_u|)²] + 2L²E[(X_u − X_v)²]` with
`sup E[X_u²] < ∞`, `TidyR12SDETools.exists_bound_integral_sq_ms`). -/
theorem SDECoeff.msIntegrand_comp {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ mΩ} (hb : SDECoeff b s T L K) {X : ℝ → Ω → ℝ}
    (hX : MSIntegrand P 𝓕 X s T) : MSIntegrand P 𝓕 (fun u ω => b u (X u ω)) s T where
  adapted u hu := (hb.continuous hu).comp_stronglyMeasurable (hX.adapted u hu)
  memLp u hu := hb.memLp_comp hu (hX.measurable hu) (hX.memLp u hu)
  cont ε hε := by
    obtain ⟨M, hM0, hM⟩ := exists_bound_integral_sq_ms hX
    set η := min 1 (ε / (8 * (1 + M))) with hη
    have hη0 : 0 < η := lt_min one_pos (by positivity)
    have hη1 : η ≤ 1 := min_le_left _ _
    have hη2 : η * (8 * (1 + M)) ≤ ε := by
      have h := min_le_right 1 (ε / (8 * (1 + M)))
      rw [← hη, le_div_iff₀ (by positivity)] at h
      exact h
    obtain ⟨δ1, hδ1, h1⟩ := hb.time η hη0
    obtain ⟨δ2, hδ2, h2⟩ := hX.cont (ε / (4 * (L ^ 2 + 1))) (by positivity)
    refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun u hu v hv huv => ?_⟩
    have hd1 := h1 u hu v hv (huv.trans (min_le_left _ _))
    have hd2 := h2 u hu v hv (huv.trans (min_le_right _ _))
    have hXu := hX.memLp u hu
    have hXv := hX.memLp v hv
    have i0 : Integrable (fun ω => (b u (X u ω) - b v (X v ω)) ^ 2) P :=
      ((hb.memLp_comp hu (hX.measurable hu) hXu).sub
        (hb.memLp_comp hv (hX.measurable hv) hXv)).integrable_sq
    have iA : Integrable (fun ω => X u ω ^ 2) P := hXu.integrable_sq
    have iB : Integrable (fun ω => (X u ω - X v ω) ^ 2) P := (hXu.sub hXv).integrable_sq
    have hpt : ∀ ω, (b u (X u ω) - b v (X v ω)) ^ 2 ≤
        (4 * η ^ 2 + 4 * η ^ 2 * X u ω ^ 2) + 2 * L ^ 2 * (X u ω - X v ω) ^ 2 := by
      intro ω
      have ha := hd1 (X u ω)
      have hc := hb.sq_sub_le hv (X u ω) (X v ω)
      have ha2 : (b u (X u ω) - b v (X u ω)) ^ 2 ≤ (η * (1 + |X u ω|)) ^ 2 := by
        have := pow_le_pow_left₀ (abs_nonneg _) ha 2
        rwa [sq_abs] at this
      have hx : (1 + |X u ω|) ^ 2 ≤ 2 + 2 * X u ω ^ 2 := by
        nlinarith [sq_abs (X u ω), sq_nonneg (1 - |X u ω|)]
      have e : b u (X u ω) - b v (X v ω)
          = (b u (X u ω) - b v (X u ω)) + (b v (X u ω) - b v (X v ω)) := by ring
      rw [e]
      have h3 := add_sq_le_two (b u (X u ω) - b v (X u ω)) (b v (X u ω) - b v (X v ω))
      have h4 : (η * (1 + |X u ω|)) ^ 2 ≤ η ^ 2 * (2 + 2 * X u ω ^ 2) := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left hx (sq_nonneg _)
      nlinarith
    have hle : ∫ ω, (b u (X u ω) - b v (X v ω)) ^ 2 ∂P ≤ ∫ ω, ((4 * η ^ 2 + 4 * η ^ 2 * X u ω ^ 2)
        + 2 * L ^ 2 * (X u ω - X v ω) ^ 2) ∂P :=
      integral_mono i0 (((integrable_const (4 * η ^ 2)).add
        (iA.const_mul (4 * η ^ 2))).add (iB.const_mul (2 * L ^ 2))) hpt
    rw [integral_add (f := fun ω => 4 * η ^ 2 + 4 * η ^ 2 * X u ω ^ 2)
      ((integrable_const _).add (iA.const_mul _)) (iB.const_mul _),
      integral_add (f := fun _ => 4 * η ^ 2) (integrable_const _) (iA.const_mul _),
      integral_const_mul, integral_const_mul, integral_const, smul_eq_mul, probReal_univ,
      one_mul] at hle
    rw [integral_const_mul] at hle
    have hA := hM u hu
    have hηsq : η ^ 2 ≤ η := by nlinarith
    have k1 : 4 * η ^ 2 + 4 * η ^ 2 * ∫ ω, X u ω ^ 2 ∂P ≤ ε / 2 := by
      have : 4 * η ^ 2 * (1 + ∫ ω, X u ω ^ 2 ∂P) ≤ 4 * η * (1 + M) :=
        mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      nlinarith
    have k2 : 2 * L ^ 2 * ∫ ω, (X u ω - X v ω) ^ 2 ∂P ≤ ε / 2 := by
      have hL : 0 < 4 * (L ^ 2 + 1) := by positivity
      have h5 : (∫ ω, (X u ω - X v ω) ^ 2 ∂P) * (4 * (L ^ 2 + 1)) ≤ ε := by
        rwa [le_div_iff₀ hL] at hd2
      have h6 : 0 ≤ ∫ ω, (X u ω - X v ω) ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
      nlinarith [sq_nonneg L]
    change ∫ ω, (b u (X u ω) - b v (X v ω)) ^ 2 ∂P ≤ ε
    linarith

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **linear coefficients are admissible**:
`b(t, x) = α(t) + β(t)x` with `α, β` continuous on `[s, T]` satisfies `SDECoeff` (with `L`,
`K` bounds of `|β|`, `|α|` on `[s, T]`; time continuity from uniform continuity on the compact
`[s, T]`). -/
theorem sdeCoeff_linear {α β : ℝ → ℝ} (hα : ContinuousOn α (Set.Icc s T))
    (hβ : ContinuousOn β (Set.Icc s T)) :
    ∃ L K, SDECoeff (fun u x => α u + β u * x) s T L K := by
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn hβ
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hα
  refine ⟨L, K, ⟨fun u hu x y => ?_, fun u hu => ?_, fun ε hε => ?_⟩⟩
  · have e : α u + β u * x - (α u + β u * y) = β u * (x - y) := by ring
    rw [e, abs_mul]
    have := hL u hu
    rw [Real.norm_eq_abs] at this
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  · have := hK u hu
    rw [Real.norm_eq_abs] at this
    simpa using this
  · obtain ⟨δ1, hδ1, h1⟩ := Metric.uniformContinuousOn_iff.1
      (isCompact_Icc.uniformContinuousOn_of_continuous hα) ε hε
    obtain ⟨δ2, hδ2, h2⟩ := Metric.uniformContinuousOn_iff.1
      (isCompact_Icc.uniformContinuousOn_of_continuous hβ) ε hε
    refine ⟨min δ1 δ2 / 2, by positivity, fun u hu v hv huv x => ?_⟩
    have hd : dist u v < min δ1 δ2 := by
      rw [Real.dist_eq]
      have : 0 < min δ1 δ2 := lt_min hδ1 hδ2
      linarith
    have e1 := h1 u hu v hv (hd.trans_le (min_le_left _ _))
    have e2 := h2 u hu v hv (hd.trans_le (min_le_right _ _))
    rw [Real.dist_eq] at e1 e2
    have e : α u + β u * x - (α v + β v * x) = (α u - α v) + (β u - β v) * x := by ring
    rw [e]
    calc |(α u - α v) + (β u - β v) * x| ≤ |α u - α v| + |β u - β v| * |x| := by
          rw [← abs_mul]
          exact abs_add_le _ _
      _ ≤ ε + ε * |x| := add_le_add e1.le (mul_le_mul_of_nonneg_right e2.le (abs_nonneg _))
      _ = ε * (1 + |x|) := by ring

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **`b(t, x) = c·x` is admissible** on every `[s, T]`
with `L = |c|`, `K = 0` (the drift `m·x` and diffusion `σ·x` of geometric Brownian motion). -/
theorem sdeCoeff_const_mul (c : ℝ) : SDECoeff (fun _ x => c * x) s T |c| 0 where
  lip _ _ x y := by rw [← mul_sub, abs_mul]
  bound0 _ _ := by simp
  time ε hε := ⟨1, one_pos, fun _ _ _ _ _ x => by simp only [sub_self, abs_zero]; positivity⟩

/-! ## The Picard map -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the Picard map** of `dX = b(t, X)dt + σ(t, X)dW`,
`X_s = ξ`: `Φ(X)_t = ξ + ∫_s^t b(u, X_u) du + ∫_s^t σ(u, X_u) dW` (mean-square time integral, Itô
integral). -/
noncomputable def picard (P : Measure Ω) (𝓕 : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ℝ)
    (b σ : ℝ → ℝ → ℝ) (ξ : Ω → ℝ) (s : ℝ) (X : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ξ ω + dtInt P 𝓕 (fun u ω => b u (X u ω)) s t ω + itoInt P 𝓕 W (fun u ω => σ u (X u ω)) s t ω

variable {P : Measure Ω} {𝓕 : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ℝ} {σ : ℝ → ℝ → ℝ}
  {ξ : Ω → ℝ} {Kσ : ℝ}

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `Φ(X)_s = ξ`. -/
theorem picard_self (X : ℝ → Ω → ℝ) : picard P 𝓕 W b σ ξ s X s = ξ := by
  funext ω
  simp [picard, dtInt_of_le, itoInt_of_le]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the Picard image of a mean-square continuous process
is an Itô process with mean-square continuous coefficients** `b(u, X_u)`, `σ(u, X_u)` on
`[s, T]`, `0 ≤ s`, for `ξ` square integrable and `𝓕_s`-measurable. -/
theorem picard_itoProcessMS (hB : IsPreBrownianReal W P) (hb : SDECoeff b s T L K)
    (hσ : SDECoeff σ s T L Kσ) (hξ2 : MemLp ξ 2 P) (hξ : StronglyMeasurable[𝓕 s] ξ)
    {X : ℝ → Ω → ℝ} (hX : MSIntegrand P 𝓕 X s T) :
    ItoProcessMS P 𝓕 W (picard P 𝓕 W b σ ξ s X) (fun u ω => b u (X u ω))
      (fun u ω => σ u (X u ω)) s T := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨fun u hu => ?_, ?_, hb.msIntegrand_comp hX, hσ.msIntegrand_comp hX, fun u _ => ?_⟩
  · exact ((hξ.mono (𝓕.mono hu.1)).add stronglyMeasurable_dtInt).add stronglyMeasurable_itoInt
  · rw [picard_self]
    exact hξ2
  · refine ae_of_all _ fun ω => ?_
    rw [picard_self]
    rfl

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the Picard image of a mean-square continuous process
is mean-square continuous on `[s, T]`, `0 ≤ s`. -/
theorem picard_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hb : SDECoeff b s T L K)
    (hσ : SDECoeff σ s T L Kσ) (hξ2 : MemLp ξ 2 P) (hξ : StronglyMeasurable[𝓕 s] ξ)
    {X : ℝ → Ω → ℝ} (hX : MSIntegrand P 𝓕 X s T) :
    MSIntegrand P 𝓕 (picard P 𝓕 W b σ ξ s X) s T :=
  (picard_itoProcessMS hB hb hσ hξ2 hξ hX).toMS hB hW h𝓕 hs

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the contraction estimate.** For mean-square
continuous `X, Y` on `[s, T]`, `0 ≤ s`, and `t ∈ [s, T]`,
`E[(Φ(X)_t − Φ(Y)_t)²] ≤ 2L²(T − s + 1)∫_s^t E[(X_u − Y_u)²] du`
(`E[(∫G du)²] ≤ (t − s)∫E[G²]`, the isometry `E[(∫H dW)²] = ∫E[H²]`, and the Lipschitz bound). -/
theorem picard_sub_sq_le (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hb : SDECoeff b s T L K)
    (hσ : SDECoeff σ s T L Kσ) {X Y : ℝ → Ω → ℝ} (hX : MSIntegrand P 𝓕 X s T)
    (hY : MSIntegrand P 𝓕 Y s T) {t : ℝ} (ht : t ∈ Set.Icc s T) :
    ∫ ω, (picard P 𝓕 W b σ ξ s X t ω - picard P 𝓕 W b σ ξ s Y t ω) ^ 2 ∂P
      ≤ 2 * L ^ 2 * (T - s + 1) * ∫ u in s..t, ∫ ω, (X u ω - Y u ω) ^ 2 ∂P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hXt := hX.mono le_rfl ht.2
  have hYt := hY.mono le_rfl ht.2
  have hbX := (hb.msIntegrand_comp hX).mono le_rfl ht.2
  have hbY := (hb.msIntegrand_comp hY).mono le_rfl ht.2
  have hσX := (hσ.msIntegrand_comp hX).mono le_rfl ht.2
  have hσY := (hσ.msIntegrand_comp hY).mono le_rfl ht.2
  have hG := MSIntegrand.sub hbX hbY
  have hH := MSIntegrand.sub hσX hσY
  have hD := MSIntegrand.sub hXt hYt
  set A := dtInt P 𝓕 (fun u ω => b u (X u ω) - b u (Y u ω)) s t with hA
  set I := itoInt P 𝓕 W (fun u ω => σ u (X u ω) - σ u (Y u ω)) s t with hI
  have iA : MemLp A 2 P := memLp_dtInt hG
  have iI : MemLp I 2 P := memLp_itoInt_ms hB hW h𝓕 hs hH
  have e : (fun ω => picard P 𝓕 W b σ ξ s X t ω - picard P 𝓕 W b σ ξ s Y t ω) =ᵐ[P]
      fun ω => A ω + I ω := by
    filter_upwards [dtInt_sub hbX hbY, itoInt_sub_ms hB hW h𝓕 hs hσX hσY] with ω h1 h2
    simp only [picard, hA, hI, h1, h2]
    ring
  have e2 : ∫ ω, (picard P 𝓕 W b σ ξ s X t ω - picard P 𝓕 W b σ ξ s Y t ω) ^ 2 ∂P
      = ∫ ω, (A ω + I ω) ^ 2 ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [e] with ω h
    rw [h]
  have hDc := continuousOn_integral_sq_ms hD
  set J := ∫ u in s..t, ∫ ω, (X u ω - Y u ω) ^ 2 ∂P with hJ
  have hJ0 : 0 ≤ J := intervalIntegral.integral_nonneg ht.1 fun _ _ =>
    integral_nonneg fun _ => sq_nonneg _
  have hcmp : ∀ (c : ℝ → ℝ → ℝ) {Kc : ℝ}, SDECoeff c s T L Kc →
      MSIntegrand P 𝓕 (fun u ω => c u (X u ω) - c u (Y u ω)) s t →
      ∫ u in s..t, ∫ ω, (c u (X u ω) - c u (Y u ω)) ^ 2 ∂P ≤ L ^ 2 * J := by
    intro c Kc hc hcm
    rw [hJ, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on ht.1
      ((continuousOn_integral_sq_ms hcm).intervalIntegrable_of_Icc ht.1)
      ((hDc.const_smul (L ^ 2)).intervalIntegrable_of_Icc ht.1) fun u hu => ?_
    have hu' : u ∈ Set.Icc s T := ⟨hu.1, hu.2.trans ht.2⟩
    exact hc.integral_sq_sub_comp_le hu' (hX.measurable hu') (hX.memLp u hu')
      (hY.measurable hu') (hY.memLp u hu')
  have b1 : ∫ ω, A ω ^ 2 ∂P ≤ (t - s) * (L ^ 2 * J) :=
    (integral_dtInt_sq_le ht.1 hG).trans
      (mul_le_mul_of_nonneg_left (hcmp b hb hG) (sub_nonneg.2 ht.1))
  have b2 : ∫ ω, I ω ^ 2 ∂P ≤ L ^ 2 * J := by
    rw [hI, integral_itoInt_sq_ms hB hW h𝓕 hs ht.1 hH]
    exact hcmp σ hσ hH
  rw [e2]
  have hsq : ∫ ω, (A ω + I ω) ^ 2 ∂P ≤ 2 * ∫ ω, A ω ^ 2 ∂P + 2 * ∫ ω, I ω ^ 2 ∂P := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (iA.integrable_sq.const_mul 2) (iI.integrable_sq.const_mul 2)]
    exact integral_mono (iA.add iI).integrable_sq
      ((iA.integrable_sq.const_mul 2).add (iI.integrable_sq.const_mul 2))
      fun ω => add_sq_le_two _ _
  have hts : t - s ≤ T - s := by linarith [ht.2]
  have hLJ : 0 ≤ L ^ 2 * J := mul_nonneg (sq_nonneg _) hJ0
  nlinarith

/-! ## The Gronwall iteration -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the Gronwall iteration.** If `f n` are continuous on
`[s, T]`, `f 0 ≤ M` there, `K ≥ 0` and `f (n + 1) t ≤ K∫_s^t f n` for `t ∈ [s, T]`, then
`f n t ≤ M(K(t − s))ⁿ/n!` on `[s, T]`. -/
theorem iterate_bound {f : ℕ → ℝ → ℝ} {M : ℝ} (hK : 0 ≤ K)
    (hcont : ∀ n, ContinuousOn (f n) (Set.Icc s T)) (h0 : ∀ t ∈ Set.Icc s T, f 0 t ≤ M)
    (hstep : ∀ n, ∀ t ∈ Set.Icc s T, f (n + 1) t ≤ K * ∫ u in s..t, f n u) :
    ∀ n, ∀ t ∈ Set.Icc s T, f n t ≤ M * (K * (t - s)) ^ n / n ! := by
  intro n
  induction n with
  | zero => intro t ht; simpa using h0 t ht
  | succ n ih =>
    intro t ht
    have hsub : Set.Icc s t ⊆ Set.Icc s T := Set.Icc_subset_Icc le_rfl ht.2
    have hint : ∫ u in s..t, f n u ≤ ∫ u in s..t, M * (K * (u - s)) ^ n / n ! := by
      refine intervalIntegral.integral_mono_on ht.1
        (((hcont n).mono hsub).intervalIntegrable_of_Icc ht.1) ?_ fun u hu => ih u (hsub hu)
      exact (by fun_prop : Continuous fun u => M * (K * (u - s)) ^ n / n !).intervalIntegrable _ _
    have hcalc : ∫ u in s..t, M * (K * (u - s)) ^ n / n !
        = M * K ^ n / n ! * ((t - s) ^ (n + 1) / (n + 1)) := by
      have e : (fun u => M * (K * (u - s)) ^ n / n !) = fun u => M * K ^ n / n ! * (u - s) ^ n :=
        funext fun u => by rw [mul_pow]; ring
      rw [e, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_right (fun x => x ^ n) s, integral_pow]
      simp
    calc f (n + 1) t ≤ K * ∫ u in s..t, f n u := hstep n t ht
      _ ≤ K * (M * K ^ n / n ! * ((t - s) ^ (n + 1) / (n + 1))) := by
          rw [← hcalc]
          exact mul_le_mul_of_nonneg_left hint hK
      _ = M * (K * (t - s)) ^ (n + 1) / (n + 1) ! := by
          rw [mul_pow, Nat.factorial_succ]
          push_cast
          field_simp
          ring

/-- Cochrane (2023), A1 §1.6, pp. 567–568: if `0 ≤ d ≤ M(K(t − s))ⁿ/n!` for every `n`, then
`d = 0`. -/
theorem eq_zero_of_le_pow_div_factorial {d M c : ℝ} (hd : 0 ≤ d)
    (h : ∀ n : ℕ, d ≤ M * c ^ n / n !) : d = 0 := by
  have ht : Tendsto (fun n : ℕ => M * (c ^ n / n !)) atTop (𝓝 (M * 0)) :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop c).const_mul M
  rw [mul_zero] at ht
  refine le_antisymm (ge_of_tendsto' ht fun n => ?_) hd
  rw [← mul_div_assoc]
  exact h n

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `E[(X − Y)²] = 0` gives `X = Y` a.s. -/
theorem ae_eq_of_integral_sq_sub_eq_zero {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (h : ∫ ω, (X ω - Y ω) ^ 2 ∂P = 0) : X =ᵐ[P] Y := by
  have h0 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (X ω - Y ω))
    (hX.sub hY).integrable_sq).1 h
  filter_upwards [h0] with ω hω
  have : (X ω - Y ω) ^ 2 = 0 := hω
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  linarith

/-! ## Uniqueness -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: uniqueness for the SDE**
`dX = b(t, X)dt + σ(t, X)dW`, `X_s = ξ`: two mean-square continuous solutions on `[s, T]`,
`0 ≤ s`, agree a.s. at every `t ∈ [s, T]` (Gronwall: `D(t) = E[(X_t − Y_t)²]` satisfies
`D(t) ≤ 2L²(T − s + 1)∫_s^t D`, hence `D ≤ M(Kt)ⁿ/n! → 0`). -/
theorem sde_unique (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hsT : s ≤ T) (hb : SDECoeff b s T L K)
    (hσ : SDECoeff σ s T L Kσ) {X Y : ℝ → Ω → ℝ} (hX : MSIntegrand P 𝓕 X s T)
    (hY : MSIntegrand P 𝓕 Y s T)
    (hXe : ∀ t ∈ Set.Icc s T, X t =ᵐ[P] picard P 𝓕 W b σ ξ s X t)
    (hYe : ∀ t ∈ Set.Icc s T, Y t =ᵐ[P] picard P 𝓕 W b σ ξ s Y t) :
    ∀ t ∈ Set.Icc s T, X t =ᵐ[P] Y t := by
  have hD := MSIntegrand.sub hX hY
  obtain ⟨M, -, hM⟩ := exists_bound_integral_sq_ms hD
  set D : ℝ → ℝ := fun t => ∫ ω, (X t ω - Y t ω) ^ 2 ∂P with hDdef
  have hK : 0 ≤ 2 * L ^ 2 * (T - s + 1) := by
    have : 0 ≤ T - s + 1 := by linarith
    positivity
  have hstep : ∀ n : ℕ, ∀ t ∈ Set.Icc s T, D t ≤ 2 * L ^ 2 * (T - s + 1) * ∫ u in s..t, D u := by
    intro _ t ht
    have e : D t = ∫ ω, (picard P 𝓕 W b σ ξ s X t ω - picard P 𝓕 W b σ ξ s Y t ω) ^ 2 ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hXe t ht, hYe t ht] with ω h1 h2
      rw [h1, h2]
    rw [e]
    exact picard_sub_sq_le hB hW h𝓕 hs hb hσ hX hY ht
  have hbd := iterate_bound (f := fun _ => D) hK (fun _ => continuousOn_integral_sq_ms hD)
    (fun t ht => hM t ht) hstep
  intro t ht
  have h0 : D t = 0 := eq_zero_of_le_pow_div_factorial (integral_nonneg fun _ => sq_nonneg _)
    fun n => hbd n t ht
  exact ae_eq_of_integral_sq_sub_eq_zero (hX.memLp t ht) (hY.memLp t ht) h0

end Cochrane.Monetarism.TidyR12SDEPicard
