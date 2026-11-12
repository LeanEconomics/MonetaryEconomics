/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.TidyR7ItoProductRule

/-!
# The weighted bracket `Σ G_iΔX_iΔY_i → ∫ G H K du`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for Itô's formula `f(X)`
(Track 3, chunk B1): the second-order term `½Σ f''(X_{t_i})(ΔX_i)²` of the Taylor expansion is a
bracket sum with the adapted weight `G = f''(X)`. This module extends
`TidyR7ItoCovariation.tendsto_integral_abs_sumCross` (weight `1`) to bounded adapted weights
with a.s. continuous paths.

## Main results

* `wSumCross` (the weighted cross sum `Σ G_{t_i}ΔX_iΔY_i`), `integrable_wSumCross`.
* `tendsto_integral_abs_wSumCross` (**the weighted bracket**): for Itô processes `X` (diffusion
  `H`), `Y` (diffusion `K`) and an admissible weight `G` (`TidyR7ItoIntegral.ItoIntegrand`),
  along any partitions of `[s, t]` with mesh `→ 0`,
  `Σ G_{t_i}ΔX_iΔY_i → ∫_s^t G_uH_uK_u du` in `L¹`: `G d[X, Y] = GHK dt`.
* `tendsto_integral_abs_wSumCross_one`: the weight `1` gives back the bracket of
  `TidyR7ItoCovariation.tendsto_integral_abs_sumCross`.
-/

namespace Cochrane.Generality.TidyR9ItoWeightedBracket

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Generality.TidyR7StieltjesSums Cochrane.Generality.TidyR7BrownianTools
  Cochrane.Generality.TidyR7BrownianQV Cochrane.Generality.TidyR7ItoL2
  Cochrane.Generality.TidyR7ItoSums Cochrane.Generality.TidyR7ItoIntegral
  Cochrane.Generality.TidyR7ItoUnbounded Cochrane.Generality.TidyR7ItoProducts
  Cochrane.Generality.TidyR7ItoProcess Cochrane.Generality.TidyR7ItoCovariation
  Cochrane.Generality.TidyR7ItoProductRule
open Cochrane.Generality.TidyR7ProductStep (sumCross)
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → ℝ} {s t : ℝ}

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (Itô's formula, second-order term): **the weighted
cross sum** `Σ_i G_{t_i}(X_{t_{i+1}} − X_{t_i})(Y_{t_{i+1}} − Y_{t_i})`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoWeightedBracket.wSumCross). -/
noncomputable def wSumCross (p : Partition s t) (G X Y : ℝ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range p.n,
    G (p.t i) ω * ((X (p.t (i + 1)) ω - X (p.t i) ω) * (Y (p.t (i + 1)) ω - Y (p.t i) ω))

/-- Cochrane (2023), A1 §1.6, pp. 567–568: with weight `1` the weighted cross sum is the cross
sum `TidyR7ProductStep.sumCross`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoWeightedBracket.wSumCross_one). -/
theorem wSumCross_one (p : Partition s t) (X Y : ℝ → Ω → ℝ) :
    wSumCross p (fun _ _ => 1) X Y = sumCross p X Y := by
  funext ω
  simp [wSumCross, sumCross, TidyR7StieltjesSums.crossSum]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: a bounded measurable multiple of a square-integrable
variable, `G·Z`, is square integrable with `E[(GZ)²] ≤ C²E[Z²]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoWeightedBracket.memLp_mul_of_bound). -/
theorem memLp_mul_of_bound {G Z : Ω → ℝ} (hG : Measurable G) {C : ℝ} (hGb : ∀ ω, |G ω| ≤ C)
    (hZ : MemLp Z 2 P) : MemLp (fun ω => G ω * Z ω) 2 P ∧
      ∫ ω, (G ω * Z ω) ^ 2 ∂P ≤ C ^ 2 * ∫ ω, Z ω ^ 2 ∂P := by
  have hm : MemLp (fun ω => G ω * Z ω) 2 P :=
    hZ.of_le_mul (c := C) (hG.aestronglyMeasurable.mul hZ.aestronglyMeasurable)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hGb ω) (abs_nonneg _))
  refine ⟨hm, ?_⟩
  rw [← integral_const_mul]
  refine integral_mono hm.integrable_sq (hZ.integrable_sq.const_mul _) fun ω => ?_
  have h := hGb ω
  have h2 : G ω ^ 2 ≤ C ^ 2 := sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the weighted cross sum of two Itô processes with a
bounded adapted weight is integrable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoWeightedBracket.integrable_wSumCross). -/
theorem integrable_wSumCross (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {X Y a b H K G : ℝ → Ω → ℝ} {Ca CH Cb CK Cg : ℝ}
    (hX : ItoProcess P 𝓕 W X a H s t Ca CH) (hY : ItoProcess P 𝓕 W Y b K s t Cb CK)
    (hG : ItoIntegrand P 𝓕 G s t Cg) (p : Partition s t) :
    Integrable (wSumCross p G X Y) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine integrable_finsetSum (Finset.range p.n) fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  have mX := (hX.memLp hB hW h𝓕 hs (t_mem p hi')).sub (hX.memLp hB hW h𝓕 hs (t_mem p hi'.le))
  have mY := (hY.memLp hB hW h𝓕 hs (t_mem p hi')).sub (hY.memLp hB hW h𝓕 hs (t_mem p hi'.le))
  have h := (memLp_mul_of_bound (hG.measurable (t_mem p hi'.le)) (hG.bound _ (t_mem p hi'.le))
    mX).1
  have hi2 := h.integrable_mul mY
  refine hi2.congr (ae_of_all _ fun ω => ?_)
  simp only [Pi.mul_apply, Pi.sub_apply]
  ring

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Itô's formula, the second-order term: the weighted
bracket `G d[X, Y] = GHK dt`):
`Σ G_{t_i}(X_{t_{i+1}} − X_{t_i})(Y_{t_{i+1}} − Y_{t_i}) → ∫_s^t G_uH_uK_u du` in `L¹`** along
any partitions with mesh `→ 0`, for Itô processes `X` (drift `a`, diffusion `H`), `Y` (drift
`b`, diffusion `K`) and a bounded adapted weight `G` with a.s. continuous paths, `0 ≤ s < t`.
Generalises `TidyR7ItoCovariation.tendsto_integral_abs_sumCross` (the weight `1`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoWeightedBracket.tendsto_integral_abs_wSumCross). -/
theorem tendsto_integral_abs_wSumCross (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) {X Y a b H K G : ℝ → Ω → ℝ}
    {Ca CH Cb CK Cg : ℝ} (hX : ItoProcess P 𝓕 W X a H s t Ca CH)
    (hY : ItoProcess P 𝓕 W Y b K s t Cb CK) (hG : ItoIntegrand P 𝓕 G s t Cg)
    (ps : ℕ → Partition s t) (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, |wSumCross (ps k) G X Y ω - ∫ u in s..t, G u ω * (H u ω * K u ω)|
      ∂P) atTop (𝓝 0) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hGHKi : ItoIntegrand P 𝓕 (fun u ω => G u ω * (H u ω * K u ω)) s t (Cg * (CH * CK)) :=
    itoIntegrand_mul hG (itoIntegrand_mul hX.diff hY.diff)
  have hGHi : ItoIntegrand P 𝓕 (fun u ω => G u ω * H u ω) s t (Cg * CH) :=
    itoIntegrand_mul hG hX.diff
  set GHK : ℝ → Ω → ℝ := fun u ω => G u ω * (H u ω * K u ω) with hGHK
  have hHKa : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (GHK u) := hGHKi.adapted
  have hHKb : ∀ u ∈ Set.Icc s t, ∀ ω, |GHK u ω| ≤ Cg * (CH * CK) := hGHKi.bound
  have hHKc : ∀ᵐ ω ∂P, ContinuousOn (fun u => GHK u ω) (Set.Icc s t) := hGHKi.cont
  -- the pieces
  set A : ℕ → ℕ → Ω → ℝ := fun k i ω => ∫ r in (ps k).t i..(ps k).t (i + 1), a r ω with hA
  set Bt : ℕ → ℕ → Ω → ℝ := fun k i ω => ∫ r in (ps k).t i..(ps k).t (i + 1), b r ω with hBt
  set R : ℕ → ℕ → Ω → ℝ := fun k i => itoInt P 𝓕 W (fun r ω => H r ω - H ((ps k).t i) ω)
    ((ps k).t i) ((ps k).t (i + 1)) with hR
  set S : ℕ → ℕ → Ω → ℝ := fun k i => itoInt P 𝓕 W (fun r ω => K r ω - K ((ps k).t i) ω)
    ((ps k).t i) ((ps k).t (i + 1)) with hS
  set β : ℕ → ℕ → Ω → ℝ := fun k i ω => (G ((ps k).t i) ω * H ((ps k).t i) ω) *
    incr W ((ps k).t i) ((ps k).t (i + 1)) ω with hβ
  set dY : ℕ → ℕ → Ω → ℝ := fun k i ω => Y ((ps k).t (i + 1)) ω - Y ((ps k).t i) ω with hdY
  set gY : ℕ → ℕ → Ω → ℝ := fun k i ω => G ((ps k).t i) ω * dY k i ω with hgY
  -- square integrability of the pieces
  have mA : ∀ k, ∀ i < (ps k).n, MemLp (A k i) 2 P := fun k i hi =>
    memLp_integral_drift hX.drift (t_mem _ hi.le).1 (t_le_succ _ i) (t_mem _ hi).2
  have mB : ∀ k, ∀ i < (ps k).n, MemLp (Bt k i) 2 P := fun k i hi =>
    memLp_integral_drift hY.drift (t_mem _ hi.le).1 (t_le_succ _ i) (t_mem _ hi).2
  have mR : ∀ k, ∀ i < (ps k).n, MemLp (R k i) 2 P := fun k i hi =>
    memLp_itoInt hB hW h𝓕 (hs.trans (t_mem _ hi.le).1) (itoIntegrand_sub_left (t_le_succ _ i)
      (hX.diff.mono (t_mem _ hi.le).1 (t_mem _ hi).2))
  have mS : ∀ k, ∀ i < (ps k).n, MemLp (S k i) 2 P := fun k i hi =>
    memLp_itoInt hB hW h𝓕 (hs.trans (t_mem _ hi.le).1) (itoIntegrand_sub_left (t_le_succ _ i)
      (hY.diff.mono (t_mem _ hi.le).1 (t_mem _ hi).2))
  have mβ : ∀ k, ∀ i < (ps k).n, MemLp (β k i) 2 P := fun k i hi =>
    memLp_mul_incr_of_memLp hB hW h𝓕 (t_le_succ _ i) (hGHi.adapted _ (t_mem _ hi.le))
      (memLp_of_bound (hGHi.measurable (t_mem _ hi.le)) (hGHi.bound _ (t_mem _ hi.le)))
  have mdY : ∀ k, ∀ i < (ps k).n, MemLp (dY k i) 2 P := fun k i hi =>
    (hY.memLp hB hW h𝓕 hs (t_mem _ hi)).sub (hY.memLp hB hW h𝓕 hs (t_mem _ hi.le))
  have mgY : ∀ k, ∀ i < (ps k).n, MemLp (gY k i) 2 P := fun k i hi =>
    (memLp_mul_of_bound (hG.measurable (t_mem _ hi.le)) (hG.bound _ (t_mem _ hi.le))
      (mdY k i hi)).1
  have mBS : ∀ k, ∀ i < (ps k).n, MemLp (fun ω => Bt k i ω + S k i ω) 2 P := fun k i hi =>
    (mB k i hi).add (mS k i hi)
  have hgYB : ∀ k, ∑ i ∈ Finset.range (ps k).n, ∫ ω, gY k i ω ^ 2 ∂P
      ≤ Cg ^ 2 * ((2 * Cb ^ 2 * (t - s) + 2 * CK ^ 2) * (t - s)) := by
    intro k
    refine (Finset.sum_le_sum fun i hi => (memLp_mul_of_bound
      (hG.measurable (t_mem _ (Finset.mem_range.1 hi).le))
      (hG.bound _ (t_mem _ (Finset.mem_range.1 hi).le)) (mdY k i (Finset.mem_range.1 hi))).2).trans
      ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_integral_incr_sq_le hB hW h𝓕 hs hY (ps k))
      (sq_nonneg _)
  -- the pathwise split
  have hsplit : ∀ k, (fun ω => wSumCross (ps k) G X Y ω - ∫ u in s..t, GHK u ω) =ᵐ[P] fun ω =>
      wqvSum W GHK (ps k) ω + (riemannSum (ps k) (fun u => GHK u ω) - ∫ u in s..t, GHK u ω)
        + ∑ i ∈ Finset.range (ps k).n, A k i ω * gY k i ω
        + ∑ i ∈ Finset.range (ps k).n, (Bt k i ω + S k i ω) * β k i ω
        + ∑ i ∈ Finset.range (ps k).n, R k i ω * gY k i ω := by
    intro k
    have hall : ∀ᵐ ω ∂P, ∀ i, i < (ps k).n →
        G ((ps k).t i) ω * ((X ((ps k).t (i + 1)) ω - X ((ps k).t i) ω) * dY k i ω)
          = GHK ((ps k).t i) ω * incr W ((ps k).t i) ((ps k).t (i + 1)) ω ^ 2
            + A k i ω * gY k i ω + (Bt k i ω + S k i ω) * β k i ω + R k i ω * gY k i ω := by
      refine ae_all_iff.2 fun i => ?_
      by_cases hi : i < (ps k).n
      · have hm := t_mem (ps k) hi.le
        have hm' := t_mem (ps k) hi
        filter_upwards [hX.incr_decomp hB hW h𝓕 hs hm.1 (t_le_succ _ i) hm'.2,
          hY.incr_decomp hB hW h𝓕 hs hm.1 (t_le_succ _ i) hm'.2] with ω h1 h2 _
        simp only [hdY, hA, hBt, hR, hS, hβ, hGHK, hgY]
        rw [h1, h2]
        ring
      · exact ae_of_all _ fun ω h => absurd h hi
    filter_upwards [hall] with ω hω
    rw [wqvSum_eq]
    simp only [wSumCross, riemannSum]
    have e : ∑ i ∈ Finset.range (ps k).n, G ((ps k).t i) ω *
        ((X ((ps k).t (i + 1)) ω - X ((ps k).t i) ω) * (Y ((ps k).t (i + 1)) ω - Y ((ps k).t i) ω))
        = ∑ i ∈ Finset.range (ps k).n, (GHK ((ps k).t i) ω *
          incr W ((ps k).t i) ((ps k).t (i + 1)) ω ^ 2
          + A k i ω * gY k i ω + (Bt k i ω + S k i ω) * β k i ω + R k i ω * gY k i ω) :=
      Finset.sum_congr rfl fun i hi => hω i (Finset.mem_range.1 hi)
    rw [e, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    ring
  -- the five limits
  have hw : Tendsto (fun k => ∫ ω, |wqvSum W GHK (ps k) ω| ∂P) atTop (𝓝 0) := by
    have hm : ∀ k, MemLp (wqvSum W GHK (ps k)) 2 P := fun k =>
      memLp_finsetSum _ fun i hi => (memLp_qvTerm hB hW _ _).of_le_mul (c := Cg * (CH * CK))
        ((((hHKa _ (t_mem _ (Finset.mem_range.1 hi).le)).mono (𝓕.le _)).measurable).mul
          (measurable_qvTerm hW _ _)).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (hHKb _ (t_mem _ (Finset.mem_range.1 hi).le) ω)
            (abs_nonneg _))
    refine tendsto_zero_of_sq_le (c := 1) (fun k => ?_)
      (tendsto_integral_wqvSum_sq hB hW h𝓕 hs hHKa hHKb ps hps)
    rw [one_mul]
    exact sq_integral_abs_le (hm k)
  have hRm : ∀ (p : Partition s t), Measurable fun ω => riemannSum p (fun u => GHK u ω) := by
    intro p
    simp only [riemannSum]
    exact Finset.measurable_sum _ fun i hi => ((((hHKa _
      (t_mem _ (Finset.mem_range.1 hi).le)).mono (𝓕.le _)).measurable)).mul_const _
  have hIm : AEStronglyMeasurable (fun ω => ∫ u in s..t, GHK u ω) P :=
    aestronglyMeasurable_integral_drift hGHKi le_rfl hst.le le_rfl
  have hr : Tendsto (fun k => ∫ ω, |riemannSum (ps k) (fun u => GHK u ω)
      - ∫ u in s..t, GHK u ω| ∂P) atTop (𝓝 0) := by
    have hlim : ∀ᵐ ω ∂P, Tendsto (fun k => riemannSum (ps k) (fun u => GHK u ω)) atTop
        (𝓝 (∫ u in s..t, GHK u ω)) := by
      filter_upwards [hHKc] with ω hω
      exact tendsto_riemannSum hω ps hps
    have h := tendsto_integral_of_dominated_convergence
      (F := fun k ω => |riemannSum (ps k) (fun u => GHK u ω) - ∫ u in s..t, GHK u ω|)
      (f := fun _ => (0 : ℝ)) (fun _ => 2 * (Cg * (CH * CK)) * (t - s))
      (fun k => (((hRm (ps k)).aestronglyMeasurable).sub hIm).norm) (integrable_const _)
      (fun k => ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_abs]
        have h1 := abs_riemannSum_le (fun u hu => hHKb u hu ω) (ps k)
        have h2 := abs_integral_drift_le hHKb le_rfl hst.le le_rfl ω
        calc |riemannSum (ps k) (fun u => GHK u ω) - ∫ u in s..t, GHK u ω|
            ≤ |riemannSum (ps k) (fun u => GHK u ω)| + |∫ u in s..t, GHK u ω| := abs_sub _ _
          _ ≤ 2 * (Cg * (CH * CK)) * (t - s) := by linarith)
      (by
        filter_upwards [hlim] with ω hω
        have := (hω.sub_const (∫ u in s..t, GHK u ω)).abs
        simpa using this)
    simpa using h
  have hp1 := tendsto_integral_abs_sum_mul (P := P) (n := fun k => (ps k).n) mA mgY
    (tendsto_sum_integral_drift_sq hX.drift.bound ps hps) hgYB
  have hBS0 : Tendsto (fun k => ∑ i ∈ Finset.range (ps k).n,
      ∫ ω, (Bt k i ω + S k i ω) ^ 2 ∂P) atTop (𝓝 0) := by
    have hl := ((tendsto_sum_integral_drift_sq (P := P) hY.drift.bound ps hps).const_mul 2).add
      ((tendsto_sum_integral_itoInt_sub_sq hB hW h𝓕 hs hY.diff ps hps).const_mul 2)
    rw [mul_zero, add_zero] at hl
    refine squeeze_zero (fun k => Finset.sum_nonneg fun i _ => integral_nonneg fun _ =>
      sq_nonneg _) (fun k => ?_) hl
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add
      ((mB k i hi').integrable_sq.const_mul _) ((mS k i hi').integrable_sq.const_mul _)]
    exact integral_mono ((mBS k i hi').integrable_sq) (((mB k i hi').integrable_sq.const_mul
      _).add ((mS k i hi').integrable_sq.const_mul _)) fun ω => add_sq_le_two _ _
  have hp2 := tendsto_integral_abs_sum_mul (P := P) (n := fun k => (ps k).n)
    (f := fun k i ω => Bt k i ω + S k i ω) mBS mβ hBS0
    (fun k => sum_integral_mul_incr_sq_le hB hW h𝓕 hs hGHi (ps k))
  have hp3 := tendsto_integral_abs_sum_mul (P := P) (n := fun k => (ps k).n) mR mgY
    (tendsto_sum_integral_itoInt_sub_sq hB hW h𝓕 hs hX.diff ps hps) hgYB
  -- integrability of the pieces, and the triangle inequality
  have iw : ∀ k, Integrable (fun ω => |wqvSum W GHK (ps k) ω|) P := fun k =>
    (integrable_finsetSum _ fun i hi => ((memLp_qvTerm hB hW _ _).integrable
      one_le_two).bdd_mul (c := Cg * (CH * CK)) (((hHKa _ (t_mem _
        (Finset.mem_range.1 hi).le)).mono (𝓕.le _)).measurable.aestronglyMeasurable)
          (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs]; exact hHKb _ (t_mem _ (Finset.mem_range.1 hi).le) ω)).abs
  have ir : ∀ k, Integrable (fun ω => |riemannSum (ps k) (fun u => GHK u ω)
      - ∫ u in s..t, GHK u ω|) P := by
    intro k
    refine Integrable.of_bound (((hRm (ps k)).aestronglyMeasurable.sub hIm).norm)
      (2 * (Cg * (CH * CK)) * (t - s)) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    have h1 := abs_riemannSum_le (fun u hu => hHKb u hu ω) (ps k)
    have h2 := abs_integral_drift_le hHKb le_rfl hst.le le_rfl ω
    calc |riemannSum (ps k) (fun u => GHK u ω) - ∫ u in s..t, GHK u ω|
        ≤ |riemannSum (ps k) (fun u => GHK u ω)| + |∫ u in s..t, GHK u ω| := abs_sub _ _
      _ ≤ 2 * (Cg * (CH * CK)) * (t - s) := by linarith
  have isum : ∀ (k : ℕ) (f g : ℕ → Ω → ℝ), (∀ i < (ps k).n, MemLp (f i) 2 P) →
      (∀ i < (ps k).n, MemLp (g i) 2 P) →
      Integrable (fun ω => |∑ i ∈ Finset.range (ps k).n, f i ω * g i ω|) P :=
    fun k f g hf hg => (integrable_finsetSum _ fun i hi =>
      (hf i (Finset.mem_range.1 hi)).integrable_mul (hg i (Finset.mem_range.1 hi))).abs
  have hbound : ∀ k, ∫ ω, |wSumCross (ps k) G X Y ω - ∫ u in s..t, G u ω * (H u ω * K u ω)| ∂P
      ≤ ∫ ω, |wqvSum W GHK (ps k) ω| ∂P
        + ∫ ω, |riemannSum (ps k) (fun u => GHK u ω) - ∫ u in s..t, GHK u ω| ∂P
        + ∫ ω, |∑ i ∈ Finset.range (ps k).n, A k i ω * gY k i ω| ∂P
        + ∫ ω, |∑ i ∈ Finset.range (ps k).n, (Bt k i ω + S k i ω) * β k i ω| ∂P
        + ∫ ω, |∑ i ∈ Finset.range (ps k).n, R k i ω * gY k i ω| ∂P := by
    intro k
    have i1 := isum k (A k) (gY k) (mA k) (mgY k)
    have i2 := isum k (fun i ω => Bt k i ω + S k i ω) (β k) (mBS k) (mβ k)
    have i3 := isum k (R k) (gY k) (mR k) (mgY k)
    have j2 : Integrable (fun ω => |wqvSum W GHK (ps k) ω|
        + |riemannSum (ps k) (fun u => GHK u ω) - ∫ u in s..t, GHK u ω|) P := (iw k).add (ir k)
    have j3 : Integrable (fun ω => |wqvSum W GHK (ps k) ω|
        + |riemannSum (ps k) (fun u => GHK u ω) - ∫ u in s..t, GHK u ω|
        + |∑ i ∈ Finset.range (ps k).n, A k i ω * gY k i ω|) P := j2.add i1
    have j4 : Integrable (fun ω => |wqvSum W GHK (ps k) ω|
        + |riemannSum (ps k) (fun u => GHK u ω) - ∫ u in s..t, GHK u ω|
        + |∑ i ∈ Finset.range (ps k).n, A k i ω * gY k i ω|
        + |∑ i ∈ Finset.range (ps k).n, (Bt k i ω + S k i ω) * β k i ω|) P := j3.add i2
    have j5 : Integrable (fun ω => |wqvSum W GHK (ps k) ω|
        + |riemannSum (ps k) (fun u => GHK u ω) - ∫ u in s..t, GHK u ω|
        + |∑ i ∈ Finset.range (ps k).n, A k i ω * gY k i ω|
        + |∑ i ∈ Finset.range (ps k).n, (Bt k i ω + S k i ω) * β k i ω|
        + |∑ i ∈ Finset.range (ps k).n, R k i ω * gY k i ω|) P := j4.add i3
    rw [← integral_add (iw k) (ir k), ← integral_add j2 i1, ← integral_add j3 i2,
      ← integral_add j4 i3]
    rw [integral_congr_ae (g := fun ω => |wqvSum W GHK (ps k) ω + (riemannSum (ps k)
        (fun u => GHK u ω) - ∫ u in s..t, GHK u ω)
        + ∑ i ∈ Finset.range (ps k).n, A k i ω * gY k i ω
        + ∑ i ∈ Finset.range (ps k).n, (Bt k i ω + S k i ω) * β k i ω
        + ∑ i ∈ Finset.range (ps k).n, R k i ω * gY k i ω|)
      (by filter_upwards [hsplit k] with ω hω; simp only [hGHK] at hω; rw [hω])]
    refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) j5
      (ae_of_all _ fun ω => ?_)
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
  have hlim := (((hw.add hr).add hp1).add hp2).add hp3
  simp only [add_zero] at hlim
  exact squeeze_zero (fun k => integral_nonneg fun _ => abs_nonneg _) hbound hlim

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the weight `1` gives back the bracket**
`Σ ΔX_iΔY_i → ∫_s^t H_uK_u du` in `L¹`.
Restates `TidyR7ItoCovariation.tendsto_integral_abs_sumCross` as the case `G = 1` of
`tendsto_integral_abs_wSumCross`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoWeightedBracket.tendsto_integral_abs_wSumCross_one). -/
theorem tendsto_integral_abs_wSumCross_one (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t)
    {X Y a b H K : ℝ → Ω → ℝ} {Ca CH Cb CK : ℝ} (hX : ItoProcess P 𝓕 W X a H s t Ca CH)
    (hY : ItoProcess P 𝓕 W Y b K s t Cb CK) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, |sumCross (ps k) X Y ω - ∫ u in s..t, H u ω * K u ω| ∂P) atTop
      (𝓝 0) := by
  have h := tendsto_integral_abs_wSumCross hB hW h𝓕 hs hst hX hY
    (itoIntegrand_const (C := 1) (c := fun _ => (1 : ℝ)) stronglyMeasurable_const
      (fun _ => by simp)) ps hps
  simpa [wSumCross_one] using h

end Cochrane.Generality.TidyR9ItoWeightedBracket
