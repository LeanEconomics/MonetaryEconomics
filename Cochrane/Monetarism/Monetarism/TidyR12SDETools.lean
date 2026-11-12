/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR10DoobMSVersion
import Monetarism.TidyR9ItoFormulaVariants

/-!
# Tools for stochastic differential equations: mean-square time integrals and `L²` bounds

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34) (Track 3, chunk B4). Stochastic differential
equations `dX = b(t, X) dt + σ(t, X) dW` are solved below (`TidyR12SDEPicard`) in the class of
mean-square continuous processes (`TidyR7ItoUnbounded.MSIntegrand`), with the mean-square time
integral `TidyR7ItoProducts.dtInt` and the Itô integral `TidyR7ItoIntegral.itoInt`. This module
collects what the Picard iteration needs about them.

## Main results

* `dtSum_concat`, `dtInt_add_dtInt` (additivity over intervals of the mean-square time integral).
* `MSIntegrand.sub`, `dtInt_sub`, `itoInt_add_ms`, `itoInt_sub_ms` (linearity).
* `sq_dtSum_le` (Cauchy–Schwarz for Riemann sums) and **`integral_dtInt_sq_le`**:
  `E[(∫_s^t G du)²] ≤ (t − s)∫_s^t E[G_u²] du`, the time-integral companion of the Itô isometry
  `TidyR10DoobFubini.integral_itoInt_sq_ms`.
* `exists_bound_integral_sq_ms`: `sup_{u ∈ [s, t]} E[G_u²] < ∞` for a mean-square continuous `G`.
* `integral_dtInt_sq_le_const`, `integral_itoInt_sq_le_const`: the bounds `(t − s)²M` and
  `(t − s)M` when `E[G_u²] ≤ M`.
-/

namespace Cochrane.Monetarism.TidyR12SDETools

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoSums Cochrane.Monetarism.TidyR7ItoIntegral
  Cochrane.Monetarism.TidyR7ItoUnbounded Cochrane.Monetarism.TidyR7ItoProducts
  Cochrane.Monetarism.TidyR7ItoBondStep Cochrane.Monetarism.TidyR10DoobFubini
  Cochrane.Monetarism.TidyR8MonetarismItoDom
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ} {s t : ℝ}

/-! ## Additivity of the time integral -/

/-- Cochrane (2023), A1 §1.6, p. 567: the Riemann sum over a concatenated partition is the sum
of the Riemann sums.
The time-integral analogue of `TidyR7ItoSums.itoSum_concat`. -/
theorem dtSum_concat {r : ℝ} (G : ℝ → Ω → ℝ) (p : Partition s r) (q : Partition r t) (ω : Ω) :
    dtSum G (concat p q) ω = dtSum G p ω + dtSum G q ω := by
  simp only [dtSum, riemannSum, concat]
  rw [Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [concatT_of_le p q hi'.le, concatT_of_le p q hi']
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [concatT_add, add_assoc, concatT_add]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the mean-square time integral is additive over
intervals**, `∫_s^t G du = ∫_s^r G du + ∫_r^t G du` a.s. for `s ≤ r ≤ t` and `G` mean-square
continuous on `[s, t]`.
The time-integral analogue of `TidyR8MonetarismItoDom.itoInt_add_itoInt_ms`. -/
theorem dtInt_add_dtInt {G : ℝ → Ω → ℝ} {r : ℝ} (hsr : s ≤ r) (hrt : r ≤ t)
    (hG : MSIntegrand P 𝓕 G s t) :
    dtInt P 𝓕 G s t =ᵐ[P] fun ω => dtInt P 𝓕 G s r ω + dtInt P 𝓕 G r t ω := by
  rcases hsr.lt_or_eq with hsr | hsr
  · rcases hrt.lt_or_eq with hrt | hrt
    · set ps : ℕ → Partition s t := fun k => concat (dyadic hsr k) (dyadic hrt k) with hps_def
      have hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0) := by
        refine squeeze_zero (fun k => mesh_nonneg _) (fun k => mesh_concat_le _ _) ?_
        simpa using (tendsto_mesh_dyadic hsr).max (tendsto_mesh_dyadic hrt)
      have h1 := L2Tendsto_dtSum (hsr.trans hrt) hG ps hps
      have h2 := ((L2Tendsto_dyadic_dt hsr (hG.mono le_rfl hrt.le)).add
        (L2Tendsto_dyadic_dt hrt (hG.mono hsr.le le_rfl))).congr_seq
          (fun k => ae_of_all _ fun ω => (dtSum_concat G _ _ ω).symm)
      exact ae_eq_of_L2Tendsto h1 h2
    · have e : dtInt P 𝓕 G r t = 0 := dtInt_of_le hrt.ge
      refine ae_of_all _ fun ω => ?_
      rw [e, ← hrt]
      simp
  · have e : dtInt P 𝓕 G s r = 0 := dtInt_of_le hsr.ge
    refine ae_of_all _ fun ω => ?_
    rw [e, ← hsr]
    simp

/-! ## Linearity -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: mean-square continuous integrands are closed under
differences.
Composes `TidyR7ItoBondStep.MSIntegrand.add` and `TidyR7ItoBondStep.MSIntegrand.const_mul`. -/
theorem MSIntegrand.sub {G K : ℝ → Ω → ℝ} (hG : MSIntegrand P 𝓕 G s t)
    (hK : MSIntegrand P 𝓕 K s t) : MSIntegrand P 𝓕 (fun u ω => G u ω - K u ω) s t := by
  have h := MSIntegrand.add hG (MSIntegrand.const_mul hK (-1))
  have e : (fun u ω => G u ω + -1 * K u ω) = fun u ω => G u ω - K u ω :=
    funext fun u => funext fun ω => by ring
  rwa [e] at h

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `∫(G − K) du = ∫G du − ∫K du` a.s. for mean-square
continuous `G, K`. -/
theorem dtInt_sub {G K : ℝ → Ω → ℝ} (hG : MSIntegrand P 𝓕 G s t)
    (hK : MSIntegrand P 𝓕 K s t) :
    dtInt P 𝓕 (fun u ω => G u ω - K u ω) s t =ᵐ[P]
      fun ω => dtInt P 𝓕 G s t ω - dtInt P 𝓕 K s t ω := by
  have e : (fun u ω => G u ω - K u ω) = fun u ω => G u ω + -1 * K u ω :=
    funext fun u => funext fun ω => by ring
  rw [e]
  filter_upwards [dtInt_add hG (MSIntegrand.const_mul hK (-1)), dtInt_const_mul hK (-1)] with
    ω h1 h2
  rw [h1, Pi.add_apply, h2]
  ring

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `∫(G + K) dW = ∫G dW + ∫K dW` a.s. for mean-square
continuous `G, K`, `0 ≤ s`.
Generalises `TidyR7ItoIntegral.itoInt_add` (bounded integrands). -/
theorem itoInt_add_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {G K : ℝ → Ω → ℝ} (hG : MSIntegrand P 𝓕 G s t)
    (hK : MSIntegrand P 𝓕 K s t) :
    itoInt P 𝓕 W (fun u ω => G u ω + K u ω) s t =ᵐ[P]
      fun ω => itoInt P 𝓕 W G s t ω + itoInt P 𝓕 W K s t ω := by
  rcases lt_or_ge s t with hst | hts
  · have h2 : L2Tendsto P (fun k => itoSum W (fun u ω => G u ω + K u ω) (dyadic hst k))
        (fun ω => itoInt P 𝓕 W G s t ω + itoInt P 𝓕 W K s t ω) :=
      ((L2Tendsto_dyadic_ms hB hW h𝓕 hs hst hG).add
        (L2Tendsto_dyadic_ms hB hW h𝓕 hs hst hK)).congr_seq
        (fun k => ae_of_all _ fun ω => by rw [itoSum_add]; rfl)
    have h1 := (itoInt_spec hst ⟨_, stronglyMeasurable_itoInt.add stronglyMeasurable_itoInt,
      h2⟩).2
    exact ae_eq_of_L2Tendsto h1 h2
  · rw [itoInt_of_le hts, itoInt_of_le hts, itoInt_of_le hts]
    exact ae_of_all _ fun ω => by simp

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `∫(G − K) dW = ∫G dW − ∫K dW` a.s. for mean-square
continuous `G, K`, `0 ≤ s`. -/
theorem itoInt_sub_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {G K : ℝ → Ω → ℝ} (hG : MSIntegrand P 𝓕 G s t)
    (hK : MSIntegrand P 𝓕 K s t) :
    itoInt P 𝓕 W (fun u ω => G u ω - K u ω) s t =ᵐ[P]
      fun ω => itoInt P 𝓕 W G s t ω - itoInt P 𝓕 W K s t ω := by
  have e : (fun u ω => G u ω - K u ω) = fun u ω => G u ω + -1 * K u ω :=
    funext fun u => funext fun ω => by ring
  rw [e]
  filter_upwards [itoInt_add_ms hB hW h𝓕 hs hG (MSIntegrand.const_mul hK (-1)),
    TidyR9ItoFormula.itoInt_const_mul_ms hB hW h𝓕 hs hK (-1)] with ω h1 h2
  rw [h1, h2]
  ring

/-! ## The time-integral `L²` bound -/

/-- Cochrane (2023), A1 §1.6, p. 567: **Cauchy–Schwarz for Riemann sums**,
`(Σ G_{t_i}Δt_i)² ≤ (t − s) Σ G_{t_i}²Δt_i`. -/
theorem sq_dtSum_le (G : ℝ → Ω → ℝ) (p : Partition s t) (ω : Ω) :
    dtSum G p ω ^ 2 ≤ (t - s) * dtSum (fun u ω => G u ω ^ 2) p ω := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range p.n)
    (fun i => √(p.t (i + 1) - p.t i)) (fun i => G (p.t i) ω * √(p.t (i + 1) - p.t i))
  have hpos : ∀ i, 0 ≤ p.t (i + 1) - p.t i := fun i => (step_pos p i).le
  have e1 : ∑ i ∈ Finset.range p.n, √(p.t (i + 1) - p.t i) *
      (G (p.t i) ω * √(p.t (i + 1) - p.t i)) = dtSum G p ω := by
    simp only [dtSum, riemannSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := Real.mul_self_sqrt (hpos i)
    linear_combination G (p.t i) ω * this
  have e2 : ∑ i ∈ Finset.range p.n, √(p.t (i + 1) - p.t i) ^ 2 = t - s := by
    simp only [Real.sq_sqrt (hpos _)]
    exact sum_step_eq p
  have e3 : ∑ i ∈ Finset.range p.n, (G (p.t i) ω * √(p.t (i + 1) - p.t i)) ^ 2
      = dtSum (fun u ω => G u ω ^ 2) p ω := by
    simp only [dtSum, riemannSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, Real.sq_sqrt (hpos i)]
  rwa [e1, e2, e3] at h

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the expected Riemann sum of `G²` is the Riemann sum
of `u ↦ E[G_u²]`. -/
theorem integral_dtSum_sq {G : ℝ → Ω → ℝ} (hG : ∀ u ∈ Set.Icc s t, MemLp (G u) 2 P)
    (p : Partition s t) :
    ∫ ω, dtSum (fun u ω => G u ω ^ 2) p ω ∂P = riemannSum p (fun u => ∫ ω, G u ω ^ 2 ∂P) := by
  simp only [dtSum, riemannSum]
  rw [integral_finsetSum _ fun i hi =>
    ((hG _ (t_mem p (Finset.mem_range.1 hi).le)).integrable_sq.mul_const _)]
  exact Finset.sum_congr rfl fun i _ => integral_mul_const _ _

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the `L²` bound for the mean-square time
integral**, `E[(∫_s^t G du)²] ≤ (t − s)∫_s^t E[G_u²] du` for `G` mean-square continuous on
`[s, t]` and `P` a probability measure. The time-integral companion of the Itô isometry
`TidyR10DoobFubini.integral_itoInt_sq_ms`. -/
theorem integral_dtInt_sq_le [IsProbabilityMeasure P] {G : ℝ → Ω → ℝ} (hst : s ≤ t)
    (hG : MSIntegrand P 𝓕 G s t) :
    ∫ ω, dtInt P 𝓕 G s t ω ^ 2 ∂P ≤ (t - s) * ∫ u in s..t, ∫ ω, G u ω ^ 2 ∂P := by
  rcases hst.lt_or_eq with hst | hst
  · have hL := L2Tendsto_dyadic_dt hst hG
    have h1 := tendsto_integral_mul_sq_of_L2Tendsto hL (G := fun _ => (1 : ℝ))
      measurable_const (C := 1) (fun _ => by simp)
    simp only [one_mul] at h1
    have h2 := (tendsto_riemannSum (continuousOn_integral_sq_ms hG) _
      (tendsto_mesh_dyadic hst)).const_mul (t - s)
    refine le_of_tendsto_of_tendsto h1 h2 (Eventually.of_forall fun k => ?_)
    have hm : ∀ p : Partition s t, Integrable (fun ω => dtSum (fun u ω => G u ω ^ 2) p ω) P :=
      fun p => integrable_finsetSum _ fun i hi =>
        ((hG.memLp _ (t_mem p (Finset.mem_range.1 hi).le)).integrable_sq.mul_const _)
    calc ∫ ω, dtSum G (dyadic hst k) ω ^ 2 ∂P
        ≤ ∫ ω, (t - s) * dtSum (fun u ω => G u ω ^ 2) (dyadic hst k) ω ∂P :=
          integral_mono (memLp_dtSum hG.memLp _).integrable_sq ((hm _).const_mul _)
            fun ω => sq_dtSum_le G _ ω
      _ = (t - s) * riemannSum (dyadic hst k) (fun u => ∫ ω, G u ω ^ 2 ∂P) := by
          rw [integral_const_mul, integral_dtSum_sq hG.memLp]
  · rw [hst, dtInt_of_le le_rfl]
    simp

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **a mean-square continuous process has bounded second
moments on `[s, t]`**, `E[G_u²] ≤ M` (`u ↦ E[G_u²]` is continuous on the compact `[s, t]`). -/
theorem exists_bound_integral_sq_ms {G : ℝ → Ω → ℝ} (hG : MSIntegrand P 𝓕 G s t) :
    ∃ M, 0 ≤ M ∧ ∀ u ∈ Set.Icc s t, ∫ ω, G u ω ^ 2 ∂P ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuousOn_integral_sq_ms hG)
  refine ⟨max M 0, le_max_right _ _, fun u hu => ?_⟩
  have h := hM u hu
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans (h.trans (le_max_left _ _))

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `E[G_u²] ≤ M` on `[s, t]` gives
`∫_s^t E[G_u²] du ≤ (t − s)M`. -/
theorem intervalIntegral_integral_sq_le {G : ℝ → Ω → ℝ} (hst : s ≤ t)
    (hG : MSIntegrand P 𝓕 G s t) {M : ℝ} (hM : ∀ u ∈ Set.Icc s t, ∫ ω, G u ω ^ 2 ∂P ≤ M) :
    ∫ u in s..t, ∫ ω, G u ω ^ 2 ∂P ≤ (t - s) * M := by
  have h := intervalIntegral.integral_mono_on hst
    ((continuousOn_integral_sq_ms hG).intervalIntegrable_of_Icc hst)
    (intervalIntegrable_const : IntervalIntegrable (fun _ => M) MeasureSpace.volume s t) hM
  simpa [mul_comm] using h

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `E[(∫_s^t G du)²] ≤ (t − s)²M`** when
`E[G_u²] ≤ M` on `[s, t]`. -/
theorem integral_dtInt_sq_le_const [IsProbabilityMeasure P] {G : ℝ → Ω → ℝ} (hst : s ≤ t)
    (hG : MSIntegrand P 𝓕 G s t) {M : ℝ} (hM : ∀ u ∈ Set.Icc s t, ∫ ω, G u ω ^ 2 ∂P ≤ M) :
    ∫ ω, dtInt P 𝓕 G s t ω ^ 2 ∂P ≤ (t - s) ^ 2 * M := by
  have h1 := integral_dtInt_sq_le hst hG
  have h2 := intervalIntegral_integral_sq_le hst hG hM
  have h0 : 0 ≤ t - s := sub_nonneg.2 hst
  calc ∫ ω, dtInt P 𝓕 G s t ω ^ 2 ∂P ≤ (t - s) * ((t - s) * M) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 h0)
    _ = (t - s) ^ 2 * M := by ring

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `E[(∫_s^t G dW)²] ≤ (t − s)M`** when `E[G_u²] ≤ M`
on `[s, t]`, `0 ≤ s ≤ t`. Restates `TidyR7ItoUnbounded.integral_itoInt_sq_le_ms` with the
factors in the order used below. -/
theorem integral_itoInt_sq_le_const (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s ≤ t) {G : ℝ → Ω → ℝ}
    (hG : MSIntegrand P 𝓕 G s t) {M : ℝ} (hM : ∀ u ∈ Set.Icc s t, ∫ ω, G u ω ^ 2 ∂P ≤ M) :
    ∫ ω, itoInt P 𝓕 W G s t ω ^ 2 ∂P ≤ (t - s) * M := by
  rw [mul_comm]
  exact integral_itoInt_sq_le_ms hB hW h𝓕 hs hst hG hM

end Cochrane.Monetarism.TidyR12SDETools
