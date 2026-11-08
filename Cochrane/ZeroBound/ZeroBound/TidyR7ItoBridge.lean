/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR7ItoIntegral
import ZeroBound.TidyR7StieltjesCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Itô integral against Track 1, and `∫ W dW = (W_t² − W_s² − (t − s))/2`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for (1.32) with diffusive
bonds (chunk I5c): how the Itô integral `TidyR7ItoIntegral.itoInt` relates to the pathwise
Riemann–Stieltjes calculus of Track 1, and the canonical Itô correction.

## Main results

* Item 5, **integration by parts against bounded-variation integrands**:
  `itoInt_eq_byParts`: for an admissible `H` whose paths are a.s. of bounded variation on
  `[s, t]`, a.s. `∫_s^t H dW = H_tW_t − H_sW_s − ∫_s^t W dH`, the last integral pathwise
  Riemann–Stieltjes (`TidyR7StieltjesIntegral.rsInt`): the Itô integral of such an `H` is the
  Track 1 integral. `ae_tendsto_crossSum_integrand_bm`: the bracket sums `Σ ΔH_iΔW_i → 0`.
  Deterministic integrands (Wiener integrals): `itoInt_deterministic`,
  `integral_itoInt_deterministic_sq` (`E[(∫ h dW)²] = ∫_s^t h²`); on the constructed motion
  `integral_itoInt_id_bmPath_sq` (`E[(∫_0^1 u dW_u)²] = 1/3`).
* Item 6, **the Itô correction**: `itoSum_bm` (`Σ W_{t_i}ΔW_i = (W_t² − W_s² − Σ(ΔW_i)²)/2`
  exactly), `L2Tendsto_itoSum_bm`, `itoInt_bm` (for ANY pre-Brownian `W` and admissible filtration,
  `∫_s^t W dW = (W_t² − W_s² − (t − s))/2` a.s.; `W` is unbounded, so this uses the
  hypothesis-free definition of `itoInt`), and on the constructed motion
  `TidyR7BrownianExist.bmPath`: `itoInt_bmPath` (`∫_0^1 W dW = (W_1² − 1)/2`),
  `not_itoInt_bmPath_eq_stratonovich` (it is NOT the Stratonovich/naive value `W_1²/2`),
  `integral_itoInt_bmPath_sq` (`E[(∫_0^1 W dW)²] = 1/2`) and
  `integral_itoInt_bmPath_sq_eq_isometry` (`= ∫_0^1 E[W_u²] du`, the isometry for this unbounded
  integrand).
-/

namespace Cochrane.ZeroBound.TidyR7ItoBridge

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.ZeroBound.TidyR7StieltjesSums
  Cochrane.ZeroBound.TidyR7StieltjesIntegral
  Cochrane.ZeroBound.TidyR7StieltjesCalculus Cochrane.ZeroBound.TidyR7BrownianTools
  Cochrane.ZeroBound.TidyR7BrownianQV Cochrane.ZeroBound.TidyR7ItoL2
  Cochrane.ZeroBound.TidyR7ItoSums Cochrane.ZeroBound.TidyR7ItoIntegral
  Cochrane.ZeroBound.TidyR7BrownianSchauder Cochrane.ZeroBound.TidyR7BrownianExist
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ} {H : ℝ → Ω → ℝ} {s t C : ℝ}

/-! ## Item 5: bounded-variation integrands -/

/-- Cochrane (2023), A1 §1.6, p. 567: the cross sum is symmetric,
`Σ ΔfΔg = Σ ΔgΔf`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBridge.crossSum_comm). -/
theorem crossSum_comm {a b : ℝ} (p : Partition a b) (f g : ℝ → ℝ) :
    crossSum p f g = crossSum p g f :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567 (`dH·dW = 0` for bounded-variation `H`): if the
paths of `W` are a.s. continuous and those of `H` a.s. continuous and of bounded variation on
`[s, t]`, then a.s., along every sequence of partitions with mesh `→ 0`,
`Σ (H_{t_{i+1}} − H_{t_i})(W_{t_{i+1}} − W_{t_i}) → 0`.
The integrand form of the Monetarism project's TidyR7BrownianVariation.tendsto_crossSum_bm_bv.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBridge.ae_tendsto_crossSum_integrand_bm). -/
theorem ae_tendsto_crossSum_integrand_bm (hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω)
    (hHc : ∀ᵐ ω ∂P, ContinuousOn (fun u => H u ω) (Set.Icc s t))
    (hbv : ∀ᵐ ω ∂P, BoundedVariationOn (fun u => H u ω) (Set.Icc s t)) :
    ∀ᵐ ω ∂P, ∀ ps : ℕ → Partition s t, Tendsto (fun k => mesh (ps k)) atTop (𝓝 0) →
      Tendsto (fun k => crossSum (ps k) (fun u => H u ω) (fun u => bmReal W u ω)) atTop
        (𝓝 0) := by
  filter_upwards [hcont, hHc, hbv] with ω hω h1 h2 ps hps
  simp_rw [crossSum_comm _ (fun u => H u ω)]
  exact tendsto_crossSum_zero_of_continuousOn (continuous_bmReal hω).continuousOn h2 ps hps

/-- Cochrane (2023), A1 §1.6, p. 567: the exact partition identity for the left-point sum,
`Σ H_iΔW_i = H_tW_t − H_sW_s − Σ W_iΔH_i − Σ ΔH_iΔW_i`
(`TidyR7StieltjesCalculus.prod_partition_identity`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBridge.itoSum_eq_byParts). -/
theorem itoSum_eq_byParts (H : ℝ → Ω → ℝ) (p : Partition s t) (ω : Ω) :
    itoSum W H p ω = H t ω * bmReal W t ω - H s ω * bmReal W s ω
      - rsSum p (fun u => bmReal W u ω) (fun u => H u ω)
      - crossSum p (fun u => bmReal W u ω) (fun u => H u ω) := by
  have h := prod_partition_identity p (fun u => H u ω) (fun u => bmReal W u ω)
  rw [itoSum_eq_rsSum, ← crossSum_comm]
  beta_reduce at h
  linarith

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (item 5): the Itô integral of a bounded-variation
integrand is Track 1's integral.** If `W` has a.s. continuous paths and the admissible
integrand `H` has a.s. bounded-variation paths on `[s, t]`, `0 ≤ s < t`, then a.s.
`∫_s^t H dW = H_tW_t − H_sW_s − ∫_s^t W dH` with `∫ W dH` pathwise Riemann–Stieltjes.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBridge.itoInt_eq_byParts). -/
theorem itoInt_eq_byParts (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω) (hs : 0 ≤ s)
    (hst : s < t) (hH : ItoIntegrand P 𝓕 H s t C)
    (hbv : ∀ᵐ ω ∂P, BoundedVariationOn (fun u => H u ω) (Set.Icc s t)) :
    itoInt P 𝓕 W H s t =ᵐ[P] fun ω => H t ω * bmReal W t ω - H s ω * bmReal W s ω
      - rsInt s t (fun u => bmReal W u ω) (fun u => H u ω) := by
  refine ae_eq_of_L2Tendsto_of_ae_tendsto (L2Tendsto_dyadic hB hW h𝓕 hs hst hH) ?_
  filter_upwards [hcont, hbv] with ω hω hbvω
  have hWc := (continuous_bmReal hω).continuousOn (s := Set.Icc s t)
  have h1 := tendsto_rsSum_of_continuousOn hWc hbvω _ (tendsto_mesh_dyadic hst)
  have h2 := tendsto_crossSum_zero_of_continuousOn hWc hbvω _ (tendsto_mesh_dyadic hst)
  have h3 := (tendsto_const_nhds (x := H t ω * bmReal W t ω - H s ω * bmReal W s ω)).sub h1
    |>.sub h2
  rw [sub_zero] at h3
  exact h3.congr fun k => (itoSum_eq_byParts H _ ω).symm

/-- Cochrane (2023), A1 §1.6, pp. 567–568: a deterministic integrand bounded by `C` and
continuous on `[s, t]` is admissible.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBridge.itoIntegrand_deterministic). -/
theorem itoIntegrand_deterministic {h : ℝ → ℝ} (hc : ContinuousOn h (Set.Icc s t))
    (hb : ∀ u ∈ Set.Icc s t, |h u| ≤ C) : ItoIntegrand P 𝓕 (fun u _ => h u) s t C where
  adapted _ _ := stronglyMeasurable_const
  bound u hu _ := hb u hu
  cont := ae_of_all _ fun _ => hc

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (item 5): Wiener integrals by parts.** For a
deterministic `h` continuous and of bounded variation on `[s, t]` (e.g. `C¹`), `0 ≤ s < t`,
a.s. `∫_s^t h dW = h(t)W_t − h(s)W_s − ∫_s^t W dh`.
The deterministic case of `itoInt_eq_byParts`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBridge.itoInt_deterministic). -/
theorem itoInt_deterministic (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hcont : ∀ᵐ ω ∂P, Continuous fun t => W t ω) (hs : 0 ≤ s)
    (hst : s < t) {h : ℝ → ℝ} (hc : ContinuousOn h (Set.Icc s t))
    (hb : ∀ u ∈ Set.Icc s t, |h u| ≤ C) (hbv : BoundedVariationOn h (Set.Icc s t)) :
    itoInt P 𝓕 W (fun u _ => h u) s t =ᵐ[P] fun ω => h t * bmReal W t ω - h s * bmReal W s ω
      - rsInt s t (fun u => bmReal W u ω) h :=
  itoInt_eq_byParts hB hW h𝓕 hcont hs hst (itoIntegrand_deterministic hc hb)
    (ae_of_all _ fun _ => hbv)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the Wiener isometry**: for a deterministic `h`
bounded and continuous on `[s, t]`, `0 ≤ s ≤ t`, `E[(∫_s^t h dW)²] = ∫_s^t h(u)² du`.
The deterministic case of `TidyR7ItoIntegral.integral_itoInt_sq`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBridge.integral_itoInt_deterministic_sq). -/
theorem integral_itoInt_deterministic_sq (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s ≤ t)
    {h : ℝ → ℝ} (hc : ContinuousOn h (Set.Icc s t)) (hb : ∀ u ∈ Set.Icc s t, |h u| ≤ C) :
    ∫ ω, itoInt P 𝓕 W (fun u _ => h u) s t ω ^ 2 ∂P = ∫ u in s..t, h u ^ 2 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [integral_itoInt_sq hB hW h𝓕 hs hst (itoIntegrand_deterministic hc hb)]
  simp

/-! ## Item 6: `∫ W dW` -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the discrete Itô correction.** Exactly, for every
partition, `Σ W_{t_i}ΔW_i = (W_t² − W_s² − Σ(ΔW_i)²)/2`.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7ItoBridge.itoSum_bm). -/
theorem itoSum_bm (p : Partition s t) (ω : Ω) :
    itoSum W (bmReal W) p ω = (bmReal W t ω ^ 2 - bmReal W s ω ^ 2 - qvSum W p ω) / 2 := by
  have h := prod_partition_identity p (fun u => bmReal W u ω) (fun u => bmReal W u ω)
  rw [← qvSum_eq_crossSum] at h
  have e : itoSum W (bmReal W) p ω = rsSum p (fun u => bmReal W u ω) (fun u => bmReal W u ω) :=
    itoSum_eq_rsSum (bmReal W) p ω
  rw [e]
  linarith

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `W_u(W_v − W_u)` is square integrable (`W_u` and the
later increment are independent with finite second moments).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBridge.memLp_mul_incr). -/
theorem memLp_mul_incr (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {u v : ℝ} (huv : u ≤ v) :
    MemLp (fun ω => bmReal W u ω * incr W u v ω) 2 P := by
  have hm : Measurable fun ω => bmReal W u ω * incr W u v ω :=
    (hW _).mul (measurable_incr hW u v)
  refine (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 ?_
  have hI : IndepFun (fun ω => incr W u v ω ^ 2) (fun ω => bmReal W u ω ^ 2) P :=
    (indepFun_incr h𝓕 huv (h𝓕.adapted u)).comp (φ := fun x => x ^ 2) (ψ := fun x => x ^ 2)
      (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have h1 : Integrable (fun ω => bmReal W u ω ^ 2) P :=
    (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two.integrable_sq
  have h := hI.integrable_mul (integrable_incr_sq hB u v) h1
  refine h.congr (ae_of_all _ fun ω => ?_)
  simp only [Pi.mul_apply]
  ring

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (item 6): `Σ W_{t_i}ΔW_i → (W_t² − W_s² − (t − s))/2`
in mean square** along any partitions of `[s, t]`, `0 ≤ s`, with mesh `→ 0` (from I5b's
`TidyR7BrownianQV.tendsto_integral_qvSum_sub_sq`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBridge.L2Tendsto_itoSum_bm). -/
theorem L2Tendsto_itoSum_bm (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    L2Tendsto P (fun k => itoSum W (bmReal W) (ps k))
      (fun ω => (bmReal W t ω ^ 2 - bmReal W s ω ^ 2 - (t - s)) / 2) := by
  have hmem : ∀ p : Partition s t, MemLp (itoSum W (bmReal W) p) 2 P := fun p =>
    memLp_finsetSum (f := fun i ω => bmReal W (p.t i) ω * incr W (p.t i) (p.t (i + 1)) ω) _
      fun i _ => memLp_mul_incr hB hW h𝓕 (p.strictMono.monotone (Nat.le_succ i))
  have hdiff : ∀ p : Partition s t,
      (fun ω => (bmReal W t ω ^ 2 - bmReal W s ω ^ 2 - (t - s)) / 2)
        = fun ω => itoSum W (bmReal W) p ω + 1 / 2 * (qvSum W p ω - (t - s)) := fun p => by
    funext ω
    rw [itoSum_bm]
    ring
  have hY : MemLp (fun ω => (bmReal W t ω ^ 2 - bmReal W s ω ^ 2 - (t - s)) / 2) 2 P := by
    rw [hdiff (ps 0)]
    exact (hmem _).add ((memLp_qvSum_sub hB hW (ps 0)).const_mul (1 / 2))
  refine ⟨fun k => hmem _, hY, ?_⟩
  have e : ∀ k, ∫ ω, (itoSum W (bmReal W) (ps k) ω
      - (bmReal W t ω ^ 2 - bmReal W s ω ^ 2 - (t - s)) / 2) ^ 2 ∂P
      = (1 / 4) * ∫ ω, (qvSum W (ps k) ω - (t - s)) ^ 2 ∂P := by
    intro k
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only
    rw [itoSum_bm]
    ring
  simp_rw [e]
  have h := (tendsto_integral_qvSum_sub_sq hB hW hs ps hps).const_mul (1 / 4)
  rw [mul_zero] at h
  exact h

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (item 6): `∫_s^t W dW = (W_t² − W_s² − (t − s))/2`**
a.s., for any pre-Brownian `W` with measurable values, any admissible filtration and
`0 ≤ s < t`. The `−(t − s)/2` is the Itô correction: the integral is not the pathwise
(Stratonovich-type) value `(W_t² − W_s²)/2`.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7ItoBridge.itoInt_bm). -/
theorem itoInt_bm (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) :
    itoInt P 𝓕 W (bmReal W) s t
      =ᵐ[P] fun ω => (bmReal W t ω ^ 2 - bmReal W s ω ^ 2 - (t - s)) / 2 := by
  have hL := L2Tendsto_itoSum_bm hB hW h𝓕 hs (dyadic hst) (tendsto_mesh_dyadic hst)
  have hm : StronglyMeasurable[𝓕 t]
      (fun ω => (bmReal W t ω ^ 2 - bmReal W s ω ^ 2 - (t - s)) / 2) :=
    (((((h𝓕.adapted t).measurable.pow_const 2).sub
      (((h𝓕.adapted s).mono (𝓕.mono hst.le)).measurable.pow_const 2)).sub_const
        (t - s)).div_const 2).stronglyMeasurable
  exact ae_eq_of_L2Tendsto (itoInt_spec hst ⟨_, hm, hL⟩).2 hL

/-! ## Item 6 on the constructed Brownian motion -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (item 6, non-vacuity): `∫_0^1 W dW = (W_1² − 1)/2`**
a.s. for the constructed motion `TidyR7BrownianExist.bmPath` and its natural filtration.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBridge.itoInt_bmPath). -/
theorem itoInt_bmPath :
    itoInt gaussSeq (bmFiltrationReal bmPath measurable_bmPath) bmPath (bmReal bmPath) 0 1
      =ᵐ[gaussSeq] fun ω => (bmPath 1 ω ^ 2 - 1) / 2 := by
  have h := itoInt_bm isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) le_rfl zero_lt_one
  filter_upwards [h] with ω hω
  rw [hω]
  simp [bmReal, bmPath_zero]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (item 6): the Itô integral is not the
Stratonovich/naive value.** `∫_0^1 W dW` is NOT a.s. equal to `W_1²/2`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBridge.not_itoInt_bmPath_eq_stratonovich). -/
theorem not_itoInt_bmPath_eq_stratonovich :
    ¬ (itoInt gaussSeq (bmFiltrationReal bmPath measurable_bmPath) bmPath (bmReal bmPath) 0 1
      =ᵐ[gaussSeq] fun ω => bmPath 1 ω ^ 2 / 2) := by
  intro h
  have : IsProbabilityMeasure gaussSeq :=
    isPreBrownianReal_bmPath.isGaussianProcess.isProbabilityMeasure
  have h2 := itoInt_bmPath.symm.trans h
  obtain ⟨ω, hω⟩ := h2.exists
  linarith

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (item 6): `E[(∫_0^1 W dW)²] = 1/2`** for the
constructed motion (`E[W_1⁴] = 3`, `E[W_1²] = 1`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBridge.integral_itoInt_bmPath_sq). -/
theorem integral_itoInt_bmPath_sq :
    ∫ ω, itoInt gaussSeq (bmFiltrationReal bmPath measurable_bmPath) bmPath (bmReal bmPath) 0 1
      ω ^ 2 ∂gaussSeq = 1 / 2 := by
  have : IsProbabilityMeasure gaussSeq :=
    isPreBrownianReal_bmPath.isGaussianProcess.isProbabilityMeasure
  have h4 := integral_increment_pow_four isPreBrownianReal_bmPath 0 1
  have h2 := integral_increment_sq isPreBrownianReal_bmPath 0 1
  have i4 := integrable_increment_pow_four isPreBrownianReal_bmPath 0 1
  have i2 : Integrable (fun ω => (bmPath 1 ω - bmPath 0 ω) ^ 2) gaussSeq :=
    integrable_incr_sq (W := bmPath) isPreBrownianReal_bmPath 0 1 |>.congr (ae_of_all _ fun ω => by
      simp [incr, bmReal])
  simp only [bmPath_zero, sub_zero, NNReal.coe_one, NNReal.coe_zero] at h4 h2 i4 i2
  rw [integral_congr_ae (g := fun ω => ((bmPath 1 ω ^ 2 - 1) / 2) ^ 2)
    (by filter_upwards [itoInt_bmPath] with ω hω; rw [hω])]
  have e : (fun ω => ((bmPath 1 ω ^ 2 - 1) / 2) ^ 2)
      = fun ω => (1 / 4) * bmPath 1 ω ^ 4 - (1 / 2) * bmPath 1 ω ^ 2 + 1 / 4 := by
    funext ω
    ring
  rw [e, integral_add (f := fun ω => 1 / 4 * bmPath 1 ω ^ 4 - 1 / 2 * bmPath 1 ω ^ 2)
    ((i4.const_mul _).sub (i2.const_mul _)) (integrable_const _),
    integral_sub (f := fun ω => 1 / 4 * bmPath 1 ω ^ 4) (i4.const_mul _) (i2.const_mul _),
    integral_const_mul, integral_const_mul, h4, h2]
  simp
  norm_num

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (item 6): the isometry for `∫_0^1 W dW`**,
`E[(∫_0^1 W dW)²] = ∫_0^1 E[W_u²] du` (`= ∫_0^1 u du = 1/2`), although `W` is unbounded.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBridge.integral_itoInt_bmPath_sq_eq_isometry). -/
theorem integral_itoInt_bmPath_sq_eq_isometry :
    ∫ ω, itoInt gaussSeq (bmFiltrationReal bmPath measurable_bmPath) bmPath (bmReal bmPath) 0 1
      ω ^ 2 ∂gaussSeq = ∫ u in (0 : ℝ)..1, ∫ ω, bmReal bmPath u ω ^ 2 ∂gaussSeq := by
  rw [integral_itoInt_bmPath_sq]
  have e : ∀ u ∈ Set.uIcc (0 : ℝ) 1, ∫ ω, bmReal bmPath u ω ^ 2 ∂gaussSeq = u := by
    intro u hu
    rw [Set.uIcc_of_le zero_le_one] at hu
    have h := integral_incr_sq (W := bmPath) isPreBrownianReal_bmPath le_rfl hu.1
    simpa [incr, bmReal, bmPath_zero] using h
  rw [intervalIntegral.integral_congr e, integral_id]
  norm_num

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (item 5, non-vacuity): for the constructed motion,
the Wiener integral `∫_0^1 u dW_u` has `E[(∫_0^1 u dW_u)²] = ∫_0^1 u² du = 1/3`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoBridge.integral_itoInt_id_bmPath_sq). -/
theorem integral_itoInt_id_bmPath_sq :
    ∫ ω, itoInt gaussSeq (bmFiltrationReal bmPath measurable_bmPath) bmPath (fun u _ => u) 0 1
      ω ^ 2 ∂gaussSeq = 1 / 3 := by
  rw [integral_itoInt_deterministic_sq isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) le_rfl zero_le_one
    (C := 1) (h := fun u => u) continuousOn_id (fun u hu => by rw [abs_of_nonneg hu.1]; exact hu.2),
    integral_pow]
  norm_num

end Cochrane.ZeroBound.TidyR7ItoBridge
