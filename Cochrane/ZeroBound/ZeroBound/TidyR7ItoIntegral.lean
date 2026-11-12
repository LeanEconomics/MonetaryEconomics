/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR7ItoSums

/-!
# The Itô integral `∫_s^t H dW`: existence, isometry, linearity, martingale property

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for (1.32) with diffusive
bonds (chunk I5c of the Itô track): the stochastic integral of a bounded adapted integrand with
continuous paths against a Brownian motion, as the mean-square limit of left-point sums.

## Setting

`W` is any pre-Brownian motion with measurable values, `𝓕` any admissible filtration
(`TidyR7BrownianQV.BMFiltration`), `0 ≤ s`. An **admissible integrand on `[s, t]`**
(`ItoIntegrand P 𝓕 H s t C`) is adapted (`H u` is `𝓕_u`-strongly measurable), bounded by `C`,
and has almost surely continuous paths on `[s, t]`. Continuity is required only almost surely:
that is all the proof uses (dominated convergence), and it is what I5d needs, since an Itô
integral used as an integrand has continuous paths only a.s. and, without completing the
filtration, cannot be made continuous everywhere while staying adapted.

## The definition

`itoInt P 𝓕 W H s t` is, for `s < t`, a **chosen** (`Classical.choose`) `𝓕_t`-strongly measurable
mean-square limit of the left-point sums along the dyadic partitions
`TidyR7StieltjesSums.dyadic`, whenever one exists, and `0` otherwise (and `0` for `t ≤ s`).
For an admissible integrand the limit exists (`exists_dyadic_limit`, by the Cauchy estimate
`TidyR7ItoSums.integral_itoSum_sub_sq_le` and completeness `TidyR7ItoL2.exists_L2Tendsto`), so
the chosen representative is adapted (`stronglyMeasurable_itoInt`), and any two choices agree
a.e. The definition itself needs no hypothesis, so it also applies to unbounded integrands
whose dyadic sums converge (TidyR7ItoBridge: `∫ W dW`).

## Main results

* Item 2: `L2Tendsto_itoSum` (**along ANY partitions with mesh `→ 0` the left-point sums
  converge in mean square to `itoInt`**), `ae_eq_itoInt_of_L2Tendsto` (the limit does not depend
  on the partition sequence), `integral_mul_itoInt_sq` (`E[G(∫H dW)²] = E[G∫H²du]` for bounded
  `𝓕_s`-measurable `G`), `integral_itoInt_sq` (**the Itô isometry**
  `E[(∫_s^t H dW)²] = E[∫_s^t H_u² du]`), `itoInt_add`, `itoInt_const_mul` (linearity),
  `itoInt_one` (`∫ 1 dW = W_t − W_s`), `itoInt_const` (`∫ c dW = c(W_t − W_s)` for bounded
  `𝓕_s`-measurable `c`).
* Item 3: `itoInt_add_itoInt` (`∫_s^t = ∫_s^r + ∫_r^t`), `integral_mul_itoInt` (`E[G∫_r^t H dW] = 0`
  for bounded `𝓕_r`-measurable `G`), `condExp_itoInt` (`E[∫_s^t H dW | 𝓕_r] = ∫_s^r H dW`),
  `martingale_itoInt` (`t ↦ ∫_s^t H dW` is a martingale for `𝓕` on the whole time index `ℝ`,
  `0` before `s`), `condExp_itoInt_sq` (**the conditional isometry**
  `E[(∫_r^t H dW)² | 𝓕_r] = E[∫_r^t H_u² du | 𝓕_r]`).
-/

namespace Cochrane.ZeroBound.TidyR7ItoIntegral

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.TidyR7StieltjesSums Cochrane.ZeroBound.TidyR7BrownianTools
  Cochrane.ZeroBound.TidyR7BrownianQV Cochrane.ZeroBound.TidyR7ItoL2
  Cochrane.ZeroBound.TidyR7ItoSums
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ}

variable (P 𝓕) (H : ℝ → Ω → ℝ) (s t C : ℝ)

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (the bond and price integrands of (1.32) with
diffusive bonds): **an admissible Itô integrand on `[s, t]`**: adapted, bounded by `C`, with
almost surely continuous paths on `[s, t]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.ItoIntegrand). -/
structure ItoIntegrand where
  adapted : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (H u)
  bound : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C
  cont : ∀ᵐ ω ∂P, ContinuousOn (fun u => H u ω) (Set.Icc s t)

variable {P 𝓕 H s t C}

/-- Cochrane (2023), A1 §1.6, pp. 567–568: an admissible integrand has measurable values.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.ItoIntegrand.measurable). -/
theorem ItoIntegrand.measurable (hH : ItoIntegrand P 𝓕 H s t C) {u : ℝ}
    (hu : u ∈ Set.Icc s t) : Measurable (H u) :=
  ((hH.adapted u hu).mono (𝓕.le u)).measurable

/-- Cochrane (2023), A1 §1.6, pp. 567–568: an admissible integrand on `[s, t]` is admissible on
every `[a, b] ⊆ [s, t]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.ItoIntegrand.mono). -/
theorem ItoIntegrand.mono (hH : ItoIntegrand P 𝓕 H s t C) {a b : ℝ} (ha : s ≤ a) (hb : b ≤ t) :
    ItoIntegrand P 𝓕 H a b C where
  adapted u hu := hH.adapted u ⟨ha.trans hu.1, hu.2.trans hb⟩
  bound u hu := hH.bound u ⟨ha.trans hu.1, hu.2.trans hb⟩
  cont := by
    filter_upwards [hH.cont] with ω hω
    exact hω.mono (Set.Icc_subset_Icc ha hb)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: admissible integrands add.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.ItoIntegrand.add). -/
theorem ItoIntegrand.add {K : ℝ → Ω → ℝ} {C' : ℝ} (hH : ItoIntegrand P 𝓕 H s t C)
    (hK : ItoIntegrand P 𝓕 K s t C') :
    ItoIntegrand P 𝓕 (fun u ω => H u ω + K u ω) s t (C + C') where
  adapted u hu := (hH.adapted u hu).add (hK.adapted u hu)
  bound u hu ω := (abs_add_le _ _).trans (add_le_add (hH.bound u hu ω) (hK.bound u hu ω))
  cont := by
    filter_upwards [hH.cont, hK.cont] with ω h1 h2
    exact h1.add h2

/-- Cochrane (2023), A1 §1.6, pp. 567–568: admissible integrands scale.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.ItoIntegrand.const_mul). -/
theorem ItoIntegrand.const_mul (hH : ItoIntegrand P 𝓕 H s t C) (c : ℝ) :
    ItoIntegrand P 𝓕 (fun u ω => c * H u ω) s t (|c| * C) where
  adapted u hu := (hH.adapted u hu).const_mul c
  bound u hu ω := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hH.bound u hu ω) (abs_nonneg c)
  cont := by
    filter_upwards [hH.cont] with ω h1
    exact h1.const_smul c

/-- Cochrane (2023), A1 §1.6, pp. 567–568: an integrand constant in time, `c` bounded and
`𝓕_s`-measurable, is admissible on `[s, t]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.itoIntegrand_const). -/
theorem itoIntegrand_const {c : Ω → ℝ} (hc : StronglyMeasurable[𝓕 s] c)
    (hcb : ∀ ω, |c ω| ≤ C) : ItoIntegrand P 𝓕 (fun _ => c) s t C where
  adapted _ hu := hc.mono (𝓕.mono hu.1)
  bound _ _ ω := hcb ω
  cont := ae_of_all _ fun _ => continuousOn_const

/-! ## The definition -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the Itô integral `∫_s^t H dW`** (the stochastic
integral in (1.32) with diffusive bonds). For `s < t`: a chosen `𝓕_t`-strongly measurable
mean-square limit of the left-point sums `Σ H_{t_i}ΔW_i` along the dyadic partitions of
`[s, t]` if one exists, else `0`; for `t ≤ s`: `0`.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7ItoIntegral.itoInt). -/
noncomputable def itoInt (P : Measure Ω) (𝓕 : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ℝ)
    (H : ℝ → Ω → ℝ) (s t : ℝ) : Ω → ℝ := by
  classical
  exact if hst : s < t then
    if h : ∃ Y, StronglyMeasurable[𝓕 t] Y ∧
        L2Tendsto P (fun k => itoSum W H (dyadic hst k)) Y then h.choose else 0
  else 0

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `∫_s^t H dW = 0` for `t ≤ s`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.itoInt_of_le). -/
theorem itoInt_of_le (hts : t ≤ s) : itoInt P 𝓕 W H s t = 0 := by
  simp only [itoInt, not_lt.2 hts, ↓reduceDIte]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: if the dyadic left-point sums have an adapted
mean-square limit, `itoInt` is one.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.itoInt_spec). -/
theorem itoInt_spec (hst : s < t)
    (h : ∃ Y, StronglyMeasurable[𝓕 t] Y ∧ L2Tendsto P (fun k => itoSum W H (dyadic hst k)) Y) :
    StronglyMeasurable[𝓕 t] (itoInt P 𝓕 W H s t) ∧
      L2Tendsto P (fun k => itoSum W H (dyadic hst k)) (itoInt P 𝓕 W H s t) := by
  classical
  have e : itoInt P 𝓕 W H s t = h.choose := by
    simp only [itoInt, hst, h, ↓reduceDIte]
  rw [e]
  exact h.choose_spec

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **`∫_s^t H dW` is `𝓕_t`-strongly measurable**
(adapted), for every integrand.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.stronglyMeasurable_itoInt). -/
theorem stronglyMeasurable_itoInt : StronglyMeasurable[𝓕 t] (itoInt P 𝓕 W H s t) := by
  classical
  by_cases hst : s < t
  · by_cases h : ∃ Y, StronglyMeasurable[𝓕 t] Y ∧
        L2Tendsto P (fun k => itoSum W H (dyadic hst k)) Y
    · exact (itoInt_spec hst h).1
    · have e : itoInt P 𝓕 W H s t = 0 := by simp only [itoInt, hst, h, ↓reduceDIte]
      rw [e]
      exact stronglyMeasurable_zero
  · rw [itoInt_of_le (not_lt.1 hst)]
    exact stronglyMeasurable_zero

/-! ## Existence (item 2) -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the left-point sums are mean-square Cauchy** along
any sequence of partitions of `[s, t]`, `0 ≤ s < t`, with mesh `→ 0`, for an admissible
integrand.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.cauchy_itoSum). -/
theorem cauchy_itoSum (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) (hH : ItoIntegrand P 𝓕 H s t C)
    (ps : ℕ → Partition s t) (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) {ε : ℝ}
    (hε : 0 < ε) : ∃ N, ∀ k ≥ N, ∀ l ≥ N,
      ∫ ω, (itoSum W H (ps k) ω - itoSum W H (ps l) ω) ^ 2 ∂P ≤ ε := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hts : 0 < t - s := sub_pos.2 hst
  obtain ⟨δ, hδ, hδH⟩ := exists_delta_integral_sq_sub_le (P := P) (fun _ hu => hH.measurable hu)
    hH.bound hH.cont (ε := ε / (t - s)) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hps.eventually (ge_mem_nhds hδ))
  refine ⟨N, fun k hk l hl => ?_⟩
  have h := integral_itoSum_sub_sq_le hB hW h𝓕 hs hH.adapted hH.bound hδH (ps k) (ps l)
    (hN k hk) (hN l hl)
  rwa [div_mul_cancel₀ _ hts.ne'] at h

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (item 2): existence of the Itô integral.** For an
admissible integrand and `0 ≤ s < t`, the dyadic left-point sums have an `𝓕_t`-strongly
measurable mean-square limit.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.exists_dyadic_limit). -/
theorem exists_dyadic_limit (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) (hH : ItoIntegrand P 𝓕 H s t C) :
    ∃ Y, StronglyMeasurable[𝓕 t] Y ∧ L2Tendsto P (fun k => itoSum W H (dyadic hst k)) Y :=
  exists_L2Tendsto (𝓕.le t) (fun _ => stronglyMeasurable_itoSum h𝓕 hH.adapted _)
    (fun _ => memLp_itoSum hB hW (fun _ hu => hH.measurable hu) hH.bound _)
    (fun _ hε => cauchy_itoSum hB hW h𝓕 hs hst hH _ (tendsto_mesh_dyadic hst) hε)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the dyadic left-point sums converge in mean square to
`itoInt`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.L2Tendsto_dyadic). -/
theorem L2Tendsto_dyadic (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) (hH : ItoIntegrand P 𝓕 H s t C) :
    L2Tendsto P (fun k => itoSum W H (dyadic hst k)) (itoInt P 𝓕 W H s t) :=
  (itoInt_spec hst (exists_dyadic_limit hB hW h𝓕 hs hst hH)).2

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `∫_s^t H dW` is square integrable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.memLp_itoInt). -/
theorem memLp_itoInt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hH : ItoIntegrand P 𝓕 H s t C) :
    MemLp (itoInt P 𝓕 W H s t) 2 P := by
  rcases lt_or_ge s t with hst | hts
  · exact (L2Tendsto_dyadic hB hW h𝓕 hs hst hH).2.1
  · rw [itoInt_of_le hts]
    exact MemLp.zero

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (item 2): convergence along ANY partitions.** For an
admissible integrand, `0 ≤ s < t`, and any partitions of `[s, t]` with mesh `→ 0`, the
left-point sums converge in mean square to `∫_s^t H dW`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.L2Tendsto_itoSum). -/
theorem L2Tendsto_itoSum (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) (hH : ItoIntegrand P 𝓕 H s t C)
    (ps : ℕ → Partition s t) (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    L2Tendsto P (fun k => itoSum W H (ps k)) (itoInt P 𝓕 W H s t) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hY := L2Tendsto_dyadic hB hW h𝓕 hs hst hH
  have hmem : ∀ p : Partition s t, MemLp (itoSum W H p) 2 P := fun p =>
    memLp_itoSum hB hW (fun _ hu => hH.measurable hu) hH.bound p
  have hts : 0 < t - s := sub_pos.2 hst
  refine ⟨fun k => hmem _, hY.2.1, ?_⟩
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨δ, hδ, hδH⟩ := exists_delta_integral_sq_sub_le (P := P) (fun _ hu => hH.measurable hu)
    hH.bound hH.cont (ε := η / (4 * (t - s))) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hps.eventually (ge_mem_nhds hδ))
  have hdy : ∀ᶠ m in atTop, mesh (dyadic hst m) ≤ δ :=
    (tendsto_mesh_dyadic hst).eventually (ge_mem_nhds hδ)
  refine ⟨N, fun k hk => ?_⟩
  have hev : ∀ᶠ m in atTop, ∫ ω, (itoSum W H (ps k) ω - itoInt P 𝓕 W H s t ω) ^ 2 ∂P
      ≤ 2 * (η / (4 * (t - s)) * (t - s))
        + 2 * ∫ ω, (itoSum W H (dyadic hst m) ω - itoInt P 𝓕 W H s t ω) ^ 2 ∂P := by
    filter_upwards [hdy] with m hm
    refine (integral_sq_sub_le (hmem (dyadic hst m)) (hmem (ps k)) hY.2.1).trans ?_
    have h := integral_itoSum_sub_sq_le hB hW h𝓕 hs hH.adapted hH.bound hδH (dyadic hst m) (ps k)
      hm (hN k hk)
    linarith
  have hlim : Tendsto (fun m => 2 * (η / (4 * (t - s)) * (t - s))
      + 2 * ∫ ω, (itoSum W H (dyadic hst m) ω - itoInt P 𝓕 W H s t ω) ^ 2 ∂P) atTop
      (𝓝 (2 * (η / (4 * (t - s)) * (t - s)) + 2 * 0)) :=
    tendsto_const_nhds.add (hY.2.2.const_mul 2)
  have h2 := ge_of_tendsto hlim hev
  have e2 : 2 * (η / (4 * (t - s)) * (t - s)) + 2 * 0 = η / 2 := by field_simp; ring
  rw [e2] at h2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
  linarith

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (item 2): the limit does not depend on the
partitions.** Any mean-square limit of the left-point sums along any partitions of `[s, t]`
with mesh `→ 0` equals `∫_s^t H dW` a.e.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.ae_eq_itoInt_of_L2Tendsto). -/
theorem ae_eq_itoInt_of_L2Tendsto (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) (hH : ItoIntegrand P 𝓕 H s t C)
    (ps : ℕ → Partition s t) (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) {Z : Ω → ℝ}
    (hZ : L2Tendsto P (fun k => itoSum W H (ps k)) Z) : Z =ᵐ[P] itoInt P 𝓕 W H s t :=
  ae_eq_of_L2Tendsto hZ (L2Tendsto_itoSum hB hW h𝓕 hs hst hH ps hps)

/-! ## The Itô isometry -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the Riemann sum `Σ H_{t_i}²Δt_i` is measurable in
`ω`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.measurable_riemannSum_sq). -/
theorem measurable_riemannSum_sq (hHm : ∀ u ∈ Set.Icc s t, Measurable (H u))
    (p : Partition s t) : Measurable fun ω => riemannSum p (fun u => H u ω ^ 2) := by
  simp only [riemannSum]
  exact Finset.measurable_sum _ fun i hi =>
    ((hHm _ (t_mem p (Finset.mem_range.1 hi).le)).pow_const 2).mul_const _

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `|Σ H_{t_i}²Δt_i| ≤ C²(t − s)` for `|H| ≤ C`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.abs_riemannSum_sq_le). -/
theorem abs_riemannSum_sq_le (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) (p : Partition s t)
    (ω : Ω) : |riemannSum p (fun u => H u ω ^ 2)| ≤ C ^ 2 * (t - s) := by
  rw [riemannSum, ← sum_step_eq p, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_pos (step_pos p i)]
  refine mul_le_mul_of_nonneg_right ?_ (step_pos p i).le
  have hb := hHb _ (t_mem p (Finset.mem_range.1 hi).le) ω
  exact sq_le_sq' (abs_le.1 hb).1 (abs_le.1 hb).2

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `|∫_s^t H_u² du| ≤ C²(t − s)` for `|H| ≤ C`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.abs_integral_sq_le). -/
theorem abs_integral_sq_le (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) (hst : s ≤ t) (ω : Ω) :
    |∫ u in s..t, H u ω ^ 2| ≤ C ^ 2 * (t - s) := by
  rw [← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := C ^ 2)
    fun u hu => ?_).trans_eq ?_
  · rw [Set.uIoc_of_le hst] at hu
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := hHb u ⟨hu.1.le, hu.2⟩ ω
    exact sq_le_sq' (abs_le.1 hb).1 (abs_le.1 hb).2
  · rw [abs_of_nonneg (sub_nonneg.2 hst)]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: along any partitions with mesh `→ 0`, a.s.
`Σ H_{t_i}²Δt_i → ∫_s^t H_u² du` (`TidyR7ItoL2.tendsto_riemannSum` on each continuous path).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.ae_tendsto_riemannSum_sq). -/
theorem ae_tendsto_riemannSum_sq (hH : ItoIntegrand P 𝓕 H s t C) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto (fun k => riemannSum (ps k) (fun u => H u ω ^ 2)) atTop
      (𝓝 (∫ u in s..t, H u ω ^ 2)) := by
  filter_upwards [hH.cont] with ω hω
  exact tendsto_riemannSum (hω.pow 2) ps hps

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `ω ↦ ∫_s^t H_u(ω)² du` is integrable (an a.e. limit
of measurable Riemann sums, bounded by `C²(t − s)`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.integrable_integral_sq). -/
theorem integrable_integral_sq [IsFiniteMeasure P] (hH : ItoIntegrand P 𝓕 H s t C)
    (hst : s ≤ t) : Integrable (fun ω => ∫ u in s..t, H u ω ^ 2) P := by
  rcases hst.lt_or_eq with h | h
  · have hm : AEStronglyMeasurable (fun ω => ∫ u in s..t, H u ω ^ 2) P :=
      aestronglyMeasurable_of_tendsto_ae atTop (fun k =>
        (measurable_riemannSum_sq (fun _ hu => hH.measurable hu) (dyadic h k)).aestronglyMeasurable)
        (ae_tendsto_riemannSum_sq hH _ (tendsto_mesh_dyadic h))
    exact Integrable.of_bound hm (C ^ 2 * (t - s)) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact abs_integral_sq_le hH.bound hst ω)
  · simp [h]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: for bounded measurable `G`,
`E[G Σ H_{t_i}²Δt_i] → E[G ∫_s^t H_u² du]` along any partitions with mesh `→ 0` (dominated
convergence).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.tendsto_integral_mul_riemannSum_sq). -/
theorem tendsto_integral_mul_riemannSum_sq [IsFiniteMeasure P] (hH : ItoIntegrand P 𝓕 H s t C)
    (ps : ℕ → Partition s t) (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) {G : Ω → ℝ}
    (hGm : Measurable G) {CG : ℝ} (hGb : ∀ ω, |G ω| ≤ CG) :
    Tendsto (fun k => ∫ ω, G ω * riemannSum (ps k) (fun u => H u ω ^ 2) ∂P) atTop
      (𝓝 (∫ ω, G ω * (∫ u in s..t, H u ω ^ 2) ∂P)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => CG * (C ^ 2 * (t - s)))
    (fun k => (hGm.mul (measurable_riemannSum_sq (fun _ hu => hH.measurable hu)
      (ps k))).aestronglyMeasurable) (integrable_const _) (fun k => ae_of_all _ fun ω => ?_) ?_
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hGb ω) (abs_riemannSum_sq_le hH.bound _ ω) (abs_nonneg _)
      ((abs_nonneg _).trans (hGb ω))
  · filter_upwards [ae_tendsto_riemannSum_sq hH ps hps] with ω hω
    exact hω.const_mul (G ω)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the weighted Itô isometry.** For an admissible
integrand, `0 ≤ s ≤ t` and bounded `𝓕_s`-measurable `G`,
`E[G(∫_s^t H dW)²] = E[G ∫_s^t H_u² du]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.integral_mul_itoInt_sq). -/
theorem integral_mul_itoInt_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s ≤ t) (hH : ItoIntegrand P 𝓕 H s t C)
    {G : Ω → ℝ} (hG : StronglyMeasurable[𝓕 s] G) {CG : ℝ} (hGb : ∀ ω, |G ω| ≤ CG) :
    ∫ ω, G ω * itoInt P 𝓕 W H s t ω ^ 2 ∂P = ∫ ω, G ω * (∫ u in s..t, H u ω ^ 2) ∂P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hGm : Measurable G := (hG.mono (𝓕.le s)).measurable
  rcases hst.lt_or_eq with hst | hst
  · have t1 := tendsto_integral_mul_sq_of_L2Tendsto (L2Tendsto_dyadic hB hW h𝓕 hs hst hH) hGm hGb
    have e : ∀ k, ∫ ω, G ω * itoSum W H (dyadic hst k) ω ^ 2 ∂P
        = ∫ ω, G ω * riemannSum (dyadic hst k) (fun u => H u ω ^ 2) ∂P := fun k => by
      rw [integral_mul_itoSum_sq hB hW h𝓕 hs hH.adapted hH.bound _ hG hGb,
        sum_integral_eq_integral_riemannSum (fun _ hu => hH.measurable hu) hH.bound _ hGm hGb]
    exact tendsto_nhds_unique (t1.congr e)
      (tendsto_integral_mul_riemannSum_sq hH _ (tendsto_mesh_dyadic hst) hGm hGb)
  · rw [itoInt_of_le hst.ge, hst]
    simp

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (item 2): the Itô isometry**
`E[(∫_s^t H dW)²] = E[∫_s^t H_u² du]` for an admissible integrand, `0 ≤ s ≤ t`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.integral_itoInt_sq). -/
theorem integral_itoInt_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s ≤ t) (hH : ItoIntegrand P 𝓕 H s t C) :
    ∫ ω, itoInt P 𝓕 W H s t ω ^ 2 ∂P = ∫ ω, (∫ u in s..t, H u ω ^ 2) ∂P := by
  have h := integral_mul_itoInt_sq hB hW h𝓕 hs hst hH (G := fun _ => 1) stronglyMeasurable_const
    (CG := 1) (fun _ => by simp)
  simpa using h

/-! ## Linearity and simple integrands -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: linearity, additivity**:
`∫(H + K) dW = ∫H dW + ∫K dW` a.s.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7ItoIntegral.itoInt_add). -/
theorem itoInt_add (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hH : ItoIntegrand P 𝓕 H s t C)
    {K : ℝ → Ω → ℝ} {C' : ℝ} (hK : ItoIntegrand P 𝓕 K s t C') :
    itoInt P 𝓕 W (fun u ω => H u ω + K u ω) s t
      =ᵐ[P] fun ω => itoInt P 𝓕 W H s t ω + itoInt P 𝓕 W K s t ω := by
  rcases lt_or_ge s t with hst | hts
  · have h1 := L2Tendsto_dyadic hB hW h𝓕 hs hst (hH.add hK)
    have h2 := ((L2Tendsto_dyadic hB hW h𝓕 hs hst hH).add
      (L2Tendsto_dyadic hB hW h𝓕 hs hst hK)).congr_seq
        (fun k => ae_of_all _ fun ω => (congrFun (itoSum_add H K (dyadic hst k)) ω).symm)
    exact ae_eq_of_L2Tendsto h1 h2
  · rw [itoInt_of_le hts, itoInt_of_le hts, itoInt_of_le hts]
    exact ae_of_all _ fun ω => by simp

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: linearity, homogeneity**:
`∫ cH dW = c ∫ H dW` a.s. for a constant `c`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.itoInt_const_mul). -/
theorem itoInt_const_mul (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hH : ItoIntegrand P 𝓕 H s t C) (c : ℝ) :
    itoInt P 𝓕 W (fun u ω => c * H u ω) s t =ᵐ[P] fun ω => c * itoInt P 𝓕 W H s t ω := by
  rcases lt_or_ge s t with hst | hts
  · have h1 := L2Tendsto_dyadic hB hW h𝓕 hs hst (hH.const_mul c)
    have h2 := ((L2Tendsto_dyadic hB hW h𝓕 hs hst hH).const_mul c).congr_seq
        (fun k => ae_of_all _ fun ω => (congrFun (itoSum_const_mul c H (dyadic hst k)) ω).symm)
    exact ae_eq_of_L2Tendsto h1 h2
  · rw [itoInt_of_le hts, itoInt_of_le hts]
    exact ae_of_all _ fun ω => by simp

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `∫_s^t c dW = c(W_t − W_s)`** a.s. for a bounded
`𝓕_s`-measurable `c`, `0 ≤ s ≤ t`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.itoInt_const). -/
theorem itoInt_const (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s ≤ t) {c : Ω → ℝ}
    (hc : StronglyMeasurable[𝓕 s] c) (hcb : ∀ ω, |c ω| ≤ C) :
    itoInt P 𝓕 W (fun _ => c) s t =ᵐ[P] fun ω => c ω * incr W s t ω := by
  have hH : ItoIntegrand P 𝓕 (fun _ => c) s t C := itoIntegrand_const hc hcb
  rcases hst.lt_or_eq with hst | hst
  · have hX : ∀ k, itoSum W (fun _ => c) (dyadic hst k) = fun ω => c ω * incr W s t ω :=
      fun k => funext (itoSum_const c _)
    have hm : MemLp (fun ω => c ω * incr W s t ω) 2 P := by
      rw [← hX 0]
      exact memLp_itoSum hB hW (fun _ hu => hH.measurable hu) hH.bound _
    have h2 : L2Tendsto P (fun k => itoSum W (fun _ => c) (dyadic hst k))
        (fun ω => c ω * incr W s t ω) := by
      refine ⟨fun k => by beta_reduce; rw [hX k]; exact hm, hm, ?_⟩
      simp only [hX, sub_self]
      simp
    exact (ae_eq_of_L2Tendsto h2 (L2Tendsto_dyadic hB hW h𝓕 hs hst hH)).symm
  · rw [itoInt_of_le hst.ge, hst]
    exact ae_of_all _ fun ω => by simp [incr_self]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `∫_s^t 1 dW = W_t − W_s`** a.s., `0 ≤ s ≤ t`.
The `c = 1` case of `itoInt_const`.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7ItoIntegral.itoInt_one). -/
theorem itoInt_one (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s ≤ t) :
    itoInt P 𝓕 W (fun _ _ => 1) s t =ᵐ[P] incr W s t := by
  have h := itoInt_const hB hW h𝓕 hs hst (c := fun _ => 1) stronglyMeasurable_const (C := 1)
    (fun _ => by simp)
  filter_upwards [h] with ω hω
  rw [hω, one_mul]

/-! ## The martingale property (item 3) -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: additivity over intervals**:
`∫_s^t H dW = ∫_s^r H dW + ∫_r^t H dW` a.s. for `0 ≤ s ≤ r ≤ t` (left-point sums over the
concatenated dyadic partitions, `TidyR7ItoSums.itoSum_concat`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.itoInt_add_itoInt). -/
theorem itoInt_add_itoInt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {r : ℝ} (hsr : s ≤ r) (hrt : r ≤ t)
    (hH : ItoIntegrand P 𝓕 H s t C) :
    itoInt P 𝓕 W H s t =ᵐ[P] fun ω => itoInt P 𝓕 W H s r ω + itoInt P 𝓕 W H r t ω := by
  rcases hsr.lt_or_eq with hsr | hsr
  · rcases hrt.lt_or_eq with hrt | hrt
    · set ps : ℕ → Partition s t := fun k => concat (dyadic hsr k) (dyadic hrt k) with hps_def
      have hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0) := by
        refine squeeze_zero (fun k => mesh_nonneg _) (fun k => mesh_concat_le _ _) ?_
        simpa using (tendsto_mesh_dyadic hsr).max (tendsto_mesh_dyadic hrt)
      have h1 := L2Tendsto_itoSum hB hW h𝓕 hs (hsr.trans hrt) hH ps hps
      have h2 := ((L2Tendsto_dyadic hB hW h𝓕 hs hsr (hH.mono le_rfl hrt.le)).add
        (L2Tendsto_dyadic hB hW h𝓕 (hs.trans hsr.le) hrt (hH.mono hsr.le le_rfl))).congr_seq
          (fun k => ae_of_all _ fun ω => (itoSum_concat H _ _ ω).symm)
      exact ae_eq_of_L2Tendsto h1 h2
    · have e : itoInt P 𝓕 W H r t = 0 := itoInt_of_le hrt.ge
      refine ae_of_all _ fun ω => ?_
      rw [e, ← hrt]
      simp
  · have e : itoInt P 𝓕 W H s r = 0 := itoInt_of_le hsr.ge
    refine ae_of_all _ fun ω => ?_
    rw [e, ← hsr]
    simp

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (`E_r ∫_r^t H dW = 0`): orthogonality to the past.**
For an admissible integrand on `[r, t]`, `0 ≤ r`, and bounded `𝓕_r`-measurable `G`,
`E[G ∫_r^t H dW] = 0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.integral_mul_itoInt). -/
theorem integral_mul_itoInt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {r : ℝ} (hr : 0 ≤ r) (hH : ItoIntegrand P 𝓕 H r t C)
    {G : Ω → ℝ} (hG : StronglyMeasurable[𝓕 r] G) {CG : ℝ} (hGb : ∀ ω, |G ω| ≤ CG) :
    ∫ ω, G ω * itoInt P 𝓕 W H r t ω ∂P = 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rcases lt_or_ge r t with hrt | htr
  · have t1 := tendsto_integral_mul_of_L2Tendsto (L2Tendsto_dyadic hB hW h𝓕 hr hrt hH)
      (hG.mono (𝓕.le r)).measurable hGb
    have e : ∀ k, ∫ ω, G ω * itoSum W H (dyadic hrt k) ω ∂P = 0 := fun k =>
      integral_mul_itoSum hB hW h𝓕 hH.adapted hH.bound _ hG hGb
    exact tendsto_nhds_unique t1 (tendsto_const_nhds.congr fun k => (e k).symm)
  · rw [itoInt_of_le htr]
    simp

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the Itô integral has mean zero,
`E[∫_s^t H dW] = 0`.
The `G = 1` case of `integral_mul_itoInt`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.integral_itoInt). -/
theorem integral_itoInt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hH : ItoIntegrand P 𝓕 H s t C) :
    ∫ ω, itoInt P 𝓕 W H s t ω ∂P = 0 := by
  have h := integral_mul_itoInt hB hW h𝓕 hs hH (G := fun _ => 1) stronglyMeasurable_const
    (CG := 1) (fun _ => by simp)
  simpa using h

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (item 3): the martingale property**
`E[∫_s^t H dW | 𝓕_r] = ∫_s^r H dW` a.s. for `0 ≤ s ≤ r ≤ t`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.condExp_itoInt). -/
theorem condExp_itoInt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {r : ℝ} (hsr : s ≤ r) (hrt : r ≤ t)
    (hH : ItoIntegrand P 𝓕 H s t C) :
    P[itoInt P 𝓕 W H s t | 𝓕 r] =ᵐ[P] itoInt P 𝓕 W H s r := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hint : ∀ a b, s ≤ a → b ≤ t → Integrable (itoInt P 𝓕 W H a b) P := fun a b ha hb =>
    (memLp_itoInt hB hW h𝓕 (hs.trans ha) (hH.mono ha hb)).integrable one_le_two
  have hadd := itoInt_add_itoInt hB hW h𝓕 hs hsr hrt hH
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le r) (hint s t le_rfl le_rfl)
    (fun _ _ _ => (hint s r le_rfl hrt).integrableOn) ?_
    stronglyMeasurable_itoInt.aestronglyMeasurable).symm
  intro A hA _
  have hA' : MeasurableSet A := 𝓕.le r A hA
  have h0 : ∫ ω in A, itoInt P 𝓕 W H r t ω ∂P = 0 := by
    have h := integral_mul_itoInt hB hW h𝓕 (hs.trans hsr) (hH.mono hsr le_rfl)
      (G := A.indicator fun _ => (1 : ℝ)) (stronglyMeasurable_const.indicator hA) (CG := 1)
      (fun ω => by by_cases h : ω ∈ A <;> simp [h])
    rwa [integral_indicator_one_mul hA'] at h
  rw [integral_congr_ae (ae_restrict_of_ae hadd), integral_add (hint s r le_rfl hrt).integrableOn
    (hint r t hsr le_rfl).integrableOn, h0, add_zero]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (item 3): `t ↦ ∫_s^t H dW` is a martingale** for
`𝓕` on the whole time index `ℝ` (it is `0` for `t ≤ s`), for an integrand admissible on every
`[s, T]`, `0 ≤ s`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.martingale_itoInt). -/
theorem martingale_itoInt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hH : ∀ T, ItoIntegrand P 𝓕 H s T C) :
    Martingale (fun t => itoInt P 𝓕 W H s t) 𝓕 P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨fun t => stronglyMeasurable_itoInt, fun i j hij => ?_⟩
  rcases le_or_gt i s with his | hsi
  · change P[itoInt P 𝓕 W H s j | 𝓕 i] =ᵐ[P] itoInt P 𝓕 W H s i
    rw [itoInt_of_le his]
    refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le i)
      ((memLp_itoInt hB hW h𝓕 hs (hH j)).integrable one_le_two)
      (fun _ _ _ => integrableOn_zero) ?_ stronglyMeasurable_zero.aestronglyMeasurable).symm
    intro A hA _
    have hA' : MeasurableSet A := 𝓕.le i A hA
    have h := integral_mul_itoInt hB hW h𝓕 hs (hH j) (G := A.indicator fun _ => (1 : ℝ))
      (stronglyMeasurable_const.indicator (𝓕.mono his A hA)) (CG := 1)
      (fun ω => by by_cases h : ω ∈ A <;> simp [h])
    rw [integral_indicator_one_mul hA'] at h
    rw [h]
    simp
  · exact condExp_itoInt hB hW h𝓕 hs hsi.le hij (hH j)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (item 3): the conditional Itô isometry**
`E[(∫_r^t H dW)² | 𝓕_r] = E[∫_r^t H_u² du | 𝓕_r]` a.s. for `0 ≤ r ≤ t`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoIntegral.condExp_itoInt_sq). -/
theorem condExp_itoInt_sq (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {r : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t)
    (hH : ItoIntegrand P 𝓕 H r t C) :
    P[fun ω => itoInt P 𝓕 W H r t ω ^ 2 | 𝓕 r]
      =ᵐ[P] P[fun ω => ∫ u in r..t, H u ω ^ 2 | 𝓕 r] := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hf : Integrable (fun ω => itoInt P 𝓕 W H r t ω ^ 2) P :=
    (memLp_itoInt hB hW h𝓕 hr hH).integrable_sq
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le r) hf
    (fun _ _ _ => integrable_condExp.integrableOn) ?_
    stronglyMeasurable_condExp.aestronglyMeasurable).symm
  intro A hA _
  have hA' : MeasurableSet A := 𝓕.le r A hA
  have h := integral_mul_itoInt_sq hB hW h𝓕 hr hrt hH (G := A.indicator fun _ => (1 : ℝ))
    (stronglyMeasurable_const.indicator hA) (CG := 1)
    (fun ω => by by_cases h : ω ∈ A <;> simp [h])
  rw [integral_indicator_one_mul hA', integral_indicator_one_mul hA'] at h
  rw [setIntegral_condExp (𝓕.le r) (integrable_integral_sq hH hrt) hA, h]

end Cochrane.ZeroBound.TidyR7ItoIntegral
