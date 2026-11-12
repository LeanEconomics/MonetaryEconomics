/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR10TwoBMExist
import Monetarism.TidyR7ItoSums

/-!
# The cross variation of two independent Brownian motions: `dW¹ dW² = 0`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for (1.32) when bonds and `Λ/P`
load on independent shocks (Track 3, chunk B2): the rule `dW¹ dW² = 0` for two independent
Brownian motions with a common admissible filtration
(`TidyR10TwoBMExist.TwoBMFiltration`), the two-motion analogue of `(dW)² = dt`
(module TidyR7BrownianQV).

## Conventions

`cvTerm W¹ W² u v = (W¹_v − W¹_u)(W²_v − W²_u)`; along a partition of `[s, t]`,
`cvSum = Σ_i ΔW¹_iΔW²_i` and, for a weight `H`, `wcvSum = Σ_i H_{t_i}ΔW¹_iΔW²_i`.

## Main results

* Moments: `integral_cvTerm` (`E[ΔW¹ΔW²] = 0`), `integral_cvTerm_sq`
  (`E[(ΔW¹ΔW²)²] = Δt²`), `integral_mul_cvTerm` (`E[Y ΔW¹ΔW²] = 0` for `Y` `𝓕_u`-measurable),
  `integral_mul_cvTerm_sq` (`E[Y(ΔW¹ΔW²)²] = Δt²E[Y]`), `condExp_cvTerm`
  (**`E[ΔW¹ΔW² | 𝓕_u] = 0`**).
* **Exact `L²` identities**: `integral_mul_wcvSum_sq`
  (`E[G(Σ H_iΔW¹_iΔW²_i)²] = Σ E[G H_i²]Δt_i²` for bounded `𝓕_s`-measurable `G`),
  `integral_wcvSum_sq`, `integral_cvSum_sq` (**`E[(Σ ΔW¹_iΔW²_i)²] = Σ Δt_i²`**),
  `integral_cvSum_sq_le` (`≤ mesh·(t − s)`), `integral_wcvSum_sq_le` (`≤ C²·mesh·(t − s)`).
* Conditional: `condExp_wcvSum` (`E[Σ H_iΔW¹_iΔW²_i | 𝓕_s] = 0`).
* **Convergence**: `L2Tendsto_cvSum`, `L2Tendsto_wcvSum` (`→ 0` in `L²` along ANY partitions with
  mesh `→ 0`); almost surely: `ae_tendsto_wcvSum_of_summable_mesh`, `ae_tendsto_cvSum_dyadic`,
  `ae_tendsto_wcvSum_dyadic` (dyadic partitions).
* Non-vacuity on the constructed pair `TidyR10TwoBMExist.bmPath₁`, `bmPath₂`:
  `integral_cvSum_sq_bmPath`, `ae_tendsto_cvSum_dyadic_bmPath`.
-/

namespace Cochrane.Monetarism.TidyR10TwoBMCross

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoSums Cochrane.Monetarism.TidyR10TwoBMExist
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W₁ W₂ : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ}

/-! ## Cross increments and sums -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the cross increment `(W¹_v − W¹_u)(W²_v − W²_u)`,
the discrete `dW¹ dW²`. -/
def cvTerm (W₁ W₂ : ℝ≥0 → Ω → ℝ) (u v : ℝ) (ω : Ω) : ℝ := incr W₁ u v ω * incr W₂ u v ω

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the cross variation sum** `Σ_i ΔW¹_iΔW²_i` along a
partition of `[s, t]`. -/
def cvSum {s t : ℝ} (W₁ W₂ : ℝ≥0 → Ω → ℝ) (p : Partition s t) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range p.n, cvTerm W₁ W₂ (p.t i) (p.t (i + 1)) ω

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the weighted cross variation sum**
`Σ_i H_{t_i}ΔW¹_iΔW²_i`. -/
def wcvSum {s t : ℝ} (W₁ W₂ : ℝ≥0 → Ω → ℝ) (H : ℝ → Ω → ℝ) (p : Partition s t) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range p.n, H (p.t i) ω * cvTerm W₁ W₂ (p.t i) (p.t (i + 1)) ω

/-- Cochrane (2023), A1 §1.6, pp. 567–568: with weight `1` the weighted sum is `cvSum`. -/
theorem wcvSum_one {s t : ℝ} (p : Partition s t) (ω : Ω) :
    wcvSum W₁ W₂ (fun _ _ => 1) p ω = cvSum W₁ W₂ p ω := by
  simp [wcvSum, cvSum]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: cross increments are measurable. -/
theorem measurable_cvTerm (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (u v : ℝ) : Measurable (cvTerm W₁ W₂ u v) :=
  (measurable_incr hW₁ u v).mul (measurable_incr hW₂ u v)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: for a common admissible filtration, the cross
increment over `[u, v]` is `𝓕_v`-measurable. -/
theorem stronglyMeasurable_cvTerm (h : TwoBMFiltration P W₁ W₂ 𝓕) {u v : ℝ} (huv : u ≤ v) :
    StronglyMeasurable[𝓕 v] (cvTerm W₁ W₂ u v) :=
  (stronglyMeasurable_incr h.bm1 huv).mul (stronglyMeasurable_incr h.bm2 huv)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the pair of increments over `[u, v]` is independent
of every `𝓕_u`-measurable `Y`. -/
theorem indepFun_pair (h : TwoBMFiltration P W₁ W₂ 𝓕) {u v : ℝ} (huv : u ≤ v) {Y : Ω → ℝ}
    (hY : StronglyMeasurable[𝓕 u] Y) :
    IndepFun (fun ω => (incr W₁ u v ω, incr W₂ u v ω)) Y P := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_right (h.indep u v huv) hY.measurable.comap_le

/-! ## Moments -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (`E dW¹dW² = 0`): `E[ΔW¹ΔW²] = 0`**, the two
increments over a common interval being independent and centred. -/
theorem integral_cvTerm (hB₁ : IsPreBrownianReal W₁ P) (hW₁ : ∀ t, Measurable (W₁ t))
    (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration P W₁ W₂ 𝓕) (u v : ℝ) : ∫ ω, cvTerm W₁ W₂ u v ω ∂P = 0 := by
  simp only [cvTerm]
  rw [(h.incr_indep u v).integral_fun_mul_eq_mul_integral
    (measurable_incr hW₁ u v).aestronglyMeasurable (measurable_incr hW₂ u v).aestronglyMeasurable,
    integral_incr hB₁, zero_mul]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `(ΔW¹)²` and `(ΔW²)²` are independent. -/
theorem indepFun_incr_sq (h : TwoBMFiltration P W₁ W₂ 𝓕) (u v : ℝ) :
    IndepFun (fun ω => incr W₁ u v ω ^ 2) (fun ω => incr W₂ u v ω ^ 2) P :=
  (h.incr_indep u v).comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `(ΔW¹ΔW²)²` is integrable. -/
theorem integrable_cvTerm_sq (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (h : TwoBMFiltration P W₁ W₂ 𝓕) (u v : ℝ) :
    Integrable (fun ω => cvTerm W₁ W₂ u v ω ^ 2) P := by
  have hi := (indepFun_incr_sq h u v).integrable_mul (integrable_incr_sq hB₁ u v)
    (integrable_incr_sq hB₂ u v)
  refine hi.congr (ae_of_all _ fun ω => ?_)
  simp only [Pi.mul_apply, cvTerm]
  ring

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the cross increment is square integrable. -/
theorem memLp_cvTerm (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration P W₁ W₂ 𝓕) (u v : ℝ) : MemLp (cvTerm W₁ W₂ u v) 2 P :=
  (memLp_two_iff_integrable_sq (measurable_cvTerm hW₁ hW₂ u v).aestronglyMeasurable).2
    (integrable_cvTerm_sq hB₁ hB₂ h u v)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `E[(ΔW¹ΔW²)²] = Δt²`** for `0 ≤ u ≤ v`. -/
theorem integral_cvTerm_sq (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration P W₁ W₂ 𝓕) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    ∫ ω, cvTerm W₁ W₂ u v ω ^ 2 ∂P = (v - u) ^ 2 := by
  have e : (fun ω => cvTerm W₁ W₂ u v ω ^ 2)
      = fun ω => incr W₁ u v ω ^ 2 * incr W₂ u v ω ^ 2 := by
    funext ω
    simp only [cvTerm]
    ring
  rw [e, (indepFun_incr_sq h u v).integral_fun_mul_eq_mul_integral
    ((measurable_incr hW₁ u v).pow_const 2).aestronglyMeasurable
    ((measurable_incr hW₂ u v).pow_const 2).aestronglyMeasurable, integral_incr_sq hB₁ hu huv,
    integral_incr_sq hB₂ hu huv, sq]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (`E_t dW¹dW² = 0`): the cross increment is orthogonal
to the past.** For `u ≤ v` and `Y` `𝓕_u`-measurable, `E[Y ΔW¹ΔW²] = 0`. -/
theorem integral_mul_cvTerm (hB₁ : IsPreBrownianReal W₁ P) (hW₁ : ∀ t, Measurable (W₁ t))
    (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration P W₁ W₂ 𝓕) {u v : ℝ} (huv : u ≤ v) {Y : Ω → ℝ}
    (hY : StronglyMeasurable[𝓕 u] Y) : ∫ ω, Y ω * cvTerm W₁ W₂ u v ω ∂P = 0 := by
  have hI : IndepFun Y (cvTerm W₁ W₂ u v) P :=
    ((indepFun_pair h huv hY).comp (φ := fun z : ℝ × ℝ => z.1 * z.2) (ψ := id)
      (measurable_fst.mul measurable_snd) measurable_id).symm
  rw [hI.integral_fun_mul_eq_mul_integral (hY.mono (𝓕.le u)).aestronglyMeasurable
    (measurable_cvTerm hW₁ hW₂ u v).aestronglyMeasurable,
    integral_cvTerm hB₁ hW₁ hW₂ h, mul_zero]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: for `0 ≤ u ≤ v` and `Y` `𝓕_u`-measurable,
`E[Y(ΔW¹ΔW²)²] = Δt²E[Y]`. -/
theorem integral_mul_cvTerm_sq (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration P W₁ W₂ 𝓕) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) {Y : Ω → ℝ}
    (hY : StronglyMeasurable[𝓕 u] Y) :
    ∫ ω, Y ω * cvTerm W₁ W₂ u v ω ^ 2 ∂P = (v - u) ^ 2 * ∫ ω, Y ω ∂P := by
  have hI : IndepFun Y (fun ω => cvTerm W₁ W₂ u v ω ^ 2) P :=
    ((indepFun_pair h huv hY).comp (φ := fun z : ℝ × ℝ => (z.1 * z.2) ^ 2) (ψ := id)
      ((measurable_fst.mul measurable_snd).pow_const 2) measurable_id).symm
  rw [hI.integral_fun_mul_eq_mul_integral (hY.mono (𝓕.le u)).aestronglyMeasurable
    ((measurable_cvTerm hW₁ hW₂ u v).pow_const 2).aestronglyMeasurable,
    integral_cvTerm_sq hB₁ hB₂ hW₁ hW₂ h hu huv, mul_comm]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `E[ΔW¹ΔW² | 𝓕_u] = 0`** for `u ≤ v`: the pair of
increments is independent of `𝓕_u` (Mathlib `condExp_indep_eq`). -/
theorem condExp_cvTerm (hB₁ : IsPreBrownianReal W₁ P) (hW₁ : ∀ t, Measurable (W₁ t))
    (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration P W₁ W₂ 𝓕) {u v : ℝ} (huv : u ≤ v) :
    P[cvTerm W₁ W₂ u v | 𝓕 u] =ᵐ[P] 0 := by
  have : IsProbabilityMeasure P := hB₁.isGaussianProcess.isProbabilityMeasure
  have hpm : Measurable fun ω => (incr W₁ u v ω, incr W₂ u v ω) :=
    (measurable_incr hW₁ u v).prodMk (measurable_incr hW₂ u v)
  have hf : StronglyMeasurable[MeasurableSpace.comap
      (fun ω => (incr W₁ u v ω, incr W₂ u v ω)) inferInstance] (cvTerm W₁ W₂ u v) := by
    have hm : Measurable[MeasurableSpace.comap
        (fun ω => (incr W₁ u v ω, incr W₂ u v ω)) inferInstance]
        (fun ω => (fun z : ℝ × ℝ => z.1 * z.2) ((fun ω => (incr W₁ u v ω, incr W₂ u v ω)) ω)) :=
      (measurable_fst.mul measurable_snd).comp (comap_measurable _)
    exact hm.stronglyMeasurable
  have hc := condExp_indep_eq hpm.comap_le (𝓕.le u) hf (h.indep u v huv)
  rw [integral_cvTerm hB₁ hW₁ hW₂ h] at hc
  exact hc

/-! ## The weighted `L²` identity -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: for bounded `G` and `H`, each product
`G·(H_i cv_i)(H_j cv_j)` is integrable. -/
theorem integrable_mul_cvTerm_pair (hB₁ : IsPreBrownianReal W₁ P)
    (hB₂ : IsPreBrownianReal W₂ P) (hW₁ : ∀ t, Measurable (W₁ t))
    (hW₂ : ∀ t, Measurable (W₂ t)) (h : TwoBMFiltration P W₁ W₂ 𝓕) {s t : ℝ} (p : Partition s t)
    {G : Ω → ℝ}
    (hGm : Measurable G) {CG : ℝ} (hGb : ∀ ω, |G ω| ≤ CG) {H : ℝ → Ω → ℝ}
    (hHm : ∀ u ∈ Set.Icc s t, Measurable (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) {i j : ℕ} (hi : i < p.n) (hj : j < p.n) :
    Integrable (fun ω => G ω * ((H (p.t i) ω * cvTerm W₁ W₂ (p.t i) (p.t (i + 1)) ω) *
      (H (p.t j) ω * cvTerm W₁ W₂ (p.t j) (p.t (j + 1)) ω))) P := by
  have hD : Integrable (fun ω => cvTerm W₁ W₂ (p.t i) (p.t (i + 1)) ω *
      cvTerm W₁ W₂ (p.t j) (p.t (j + 1)) ω) P :=
    (memLp_cvTerm hB₁ hB₂ hW₁ hW₂ h _ _).integrable_mul (memLp_cvTerm hB₁ hB₂ hW₁ hW₂ h _ _)
  have hmi := hHm _ (t_mem p hi.le)
  have hmj := hHm _ (t_mem p hj.le)
  have hb : ∀ᵐ ω ∂P, ‖G ω * H (p.t i) ω * H (p.t j) ω‖ ≤ CG * C * C := by
    refine ae_of_all _ fun ω => ?_
    have h1 := hGb ω
    have h2 := hHb _ (t_mem p hi.le) ω
    have h3 := hHb _ (t_mem p hj.le) ω
    have hC : 0 ≤ C := (abs_nonneg _).trans h2
    have hCG : 0 ≤ CG := (abs_nonneg _).trans h1
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) hCG) h3 (abs_nonneg _)
      (mul_nonneg hCG hC)
  have hh := hD.bdd_mul ((hGm.mul hmi).mul hmj).aestronglyMeasurable hb
  refine hh.congr (ae_of_all _ fun ω => ?_)
  simp only [Pi.mul_apply]
  ring

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the weighted cross-variation `L²` identity with a
past weight.** For a common admissible filtration, `0 ≤ s`, a partition of `[s, t]`, a bounded
`𝓕_s`-measurable `G` and a bounded adapted `H`,
`E[G(Σ H_{t_i}ΔW¹_iΔW²_i)²] = Σ E[G H_{t_i}²](Δt_i)²`. The cross terms vanish by
`integral_mul_cvTerm`, the diagonal ones by `integral_mul_cvTerm_sq`. -/
theorem integral_mul_wcvSum_sq (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration P W₁ W₂ 𝓕) {s t : ℝ} (hs : 0 ≤ s) (p : Partition s t) {G : Ω → ℝ}
    (hG : StronglyMeasurable[𝓕 s] G) {CG : ℝ} (hGb : ∀ ω, |G ω| ≤ CG) {H : ℝ → Ω → ℝ}
    (hH : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) :
    ∫ ω, G ω * wcvSum W₁ W₂ H p ω ^ 2 ∂P
      = ∑ i ∈ Finset.range p.n, (∫ ω, G ω * H (p.t i) ω ^ 2 ∂P) * (p.t (i + 1) - p.t i) ^ 2 := by
  have hGm : Measurable G := (hG.mono (𝓕.le s)).measurable
  have hHm : ∀ u ∈ Set.Icc s t, Measurable (H u) := fun u hu =>
    ((hH u hu).mono (𝓕.le u)).measurable
  have hint := fun i j hi hj =>
    integrable_mul_cvTerm_pair hB₁ hB₂ hW₁ hW₂ h p hGm hGb hHm hHb (i := i) (j := j) hi hj
  have mem : ∀ i, i ≤ p.n → p.t i ∈ Set.Icc s t := fun i hi => t_mem p hi
  have nn : ∀ i, i ≤ p.n → 0 ≤ p.t i := fun i hi => hs.trans (mem i hi).1
  have mono : ∀ i j, i ≤ j → p.t i ≤ p.t j := fun i j hij => p.strictMono.monotone hij
  have hGt : ∀ i, i ≤ p.n → StronglyMeasurable[𝓕 (p.t i)] G := fun i hi =>
    hG.mono (𝓕.mono (mem i hi).1)
  have ha : ∀ i, i < p.n → ∀ j, i + 1 ≤ j → j ≤ p.n →
      StronglyMeasurable[𝓕 (p.t j)]
        (fun ω => H (p.t i) ω * cvTerm W₁ W₂ (p.t i) (p.t (i + 1)) ω) := by
    intro i hi j hij hj
    exact ((hH _ (mem i hi.le)).mono (𝓕.mono (mono i j (by omega)))).mul
      ((stronglyMeasurable_cvTerm h (mono i (i + 1) (Nat.le_succ i))).mono
        (𝓕.mono (mono (i + 1) j hij)))
  have e : (fun ω => G ω * wcvSum W₁ W₂ H p ω ^ 2) = fun ω => ∑ i ∈ Finset.range p.n,
      ∑ j ∈ Finset.range p.n, G ω * ((H (p.t i) ω * cvTerm W₁ W₂ (p.t i) (p.t (i + 1)) ω) *
        (H (p.t j) ω * cvTerm W₁ W₂ (p.t j) (p.t (j + 1)) ω)) := by
    funext ω
    rw [wcvSum, sq, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
  rw [e, integral_finsetSum _ fun i hi => integrable_finsetSum _ fun j hj =>
    hint i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  rw [integral_finsetSum _ fun j hj => hint i j hi' (Finset.mem_range.1 hj),
    Finset.sum_eq_single i]
  · have hY : StronglyMeasurable[𝓕 (p.t i)] (fun ω => G ω * H (p.t i) ω ^ 2) :=
      (hGt i hi'.le).mul ((hH _ (mem i hi'.le)).pow 2)
    have hh := integral_mul_cvTerm_sq hB₁ hB₂ hW₁ hW₂ h (nn i hi'.le)
      (mono i (i + 1) (Nat.le_succ i)) hY
    have e2 : (fun ω => G ω * ((H (p.t i) ω * cvTerm W₁ W₂ (p.t i) (p.t (i + 1)) ω) *
        (H (p.t i) ω * cvTerm W₁ W₂ (p.t i) (p.t (i + 1)) ω)))
        = fun ω => (G ω * H (p.t i) ω ^ 2) * cvTerm W₁ W₂ (p.t i) (p.t (i + 1)) ω ^ 2 := by
      funext ω
      ring
    rw [e2, hh]
    ring
  · intro j hj hji
    have hj' := Finset.mem_range.1 hj
    rcases lt_or_gt_of_ne hji with hlt | hlt
    · have hY : StronglyMeasurable[𝓕 (p.t i)] (fun ω => G ω *
          (H (p.t j) ω * cvTerm W₁ W₂ (p.t j) (p.t (j + 1)) ω) * H (p.t i) ω) :=
        ((hGt i hi'.le).mul (ha j hj' i hlt hi'.le)).mul (hH _ (mem i hi'.le))
      have hh := integral_mul_cvTerm hB₁ hW₁ hW₂ h (mono i (i + 1) (Nat.le_succ i)) hY
      have e2 : (fun ω => G ω * ((H (p.t i) ω * cvTerm W₁ W₂ (p.t i) (p.t (i + 1)) ω) *
          (H (p.t j) ω * cvTerm W₁ W₂ (p.t j) (p.t (j + 1)) ω)))
          = fun ω => (G ω * (H (p.t j) ω * cvTerm W₁ W₂ (p.t j) (p.t (j + 1)) ω) *
            H (p.t i) ω) * cvTerm W₁ W₂ (p.t i) (p.t (i + 1)) ω := by
        funext ω
        ring
      rw [e2, hh]
    · have hY : StronglyMeasurable[𝓕 (p.t j)] (fun ω => G ω *
          (H (p.t i) ω * cvTerm W₁ W₂ (p.t i) (p.t (i + 1)) ω) * H (p.t j) ω) :=
        ((hGt j hj'.le).mul (ha i hi' j hlt hj'.le)).mul (hH _ (mem j hj'.le))
      have hh := integral_mul_cvTerm hB₁ hW₁ hW₂ h (mono j (j + 1) (Nat.le_succ j)) hY
      have e2 : (fun ω => G ω * ((H (p.t i) ω * cvTerm W₁ W₂ (p.t i) (p.t (i + 1)) ω) *
          (H (p.t j) ω * cvTerm W₁ W₂ (p.t j) (p.t (j + 1)) ω)))
          = fun ω => (G ω * (H (p.t i) ω * cvTerm W₁ W₂ (p.t i) (p.t (i + 1)) ω) *
            H (p.t j) ω) * cvTerm W₁ W₂ (p.t j) (p.t (j + 1)) ω := by
        funext ω
        ring
      rw [e2, hh]
  · intro hn
    exact absurd hi hn

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the weighted cross-variation `L²` identity**:
`E[(Σ H_{t_i}ΔW¹_iΔW²_i)²] = Σ E[H_{t_i}²](Δt_i)²` for a bounded adapted `H`.
The `G = 1` case of `integral_mul_wcvSum_sq`. -/
theorem integral_wcvSum_sq (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration P W₁ W₂ 𝓕) {s t : ℝ} (hs : 0 ≤ s) (p : Partition s t)
    {H : ℝ → Ω → ℝ} (hH : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) :
    ∫ ω, wcvSum W₁ W₂ H p ω ^ 2 ∂P
      = ∑ i ∈ Finset.range p.n, (∫ ω, H (p.t i) ω ^ 2 ∂P) * (p.t (i + 1) - p.t i) ^ 2 := by
  have hh := integral_mul_wcvSum_sq hB₁ hB₂ hW₁ hW₂ h hs p (G := fun _ => 1)
    stronglyMeasurable_const (CG := 1) (fun _ => by simp) hH hHb
  simpa using hh

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the exact cross-variation `L²` identity.** For every
partition `s = t_0 < … < t_n = t`, `0 ≤ s`: `E[(Σ ΔW¹_iΔW²_i)²] = Σ(Δt_i)²`. -/
theorem integral_cvSum_sq (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration P W₁ W₂ 𝓕) {s t : ℝ} (hs : 0 ≤ s) (p : Partition s t) :
    ∫ ω, cvSum W₁ W₂ p ω ^ 2 ∂P = ∑ i ∈ Finset.range p.n, (p.t (i + 1) - p.t i) ^ 2 := by
  have : IsProbabilityMeasure P := hB₁.isGaussianProcess.isProbabilityMeasure
  have hh := integral_wcvSum_sq hB₁ hB₂ hW₁ hW₂ h hs p (H := fun _ _ => 1)
    (fun _ _ => stronglyMeasurable_const) (C := 1) (fun _ _ _ => by simp)
  simp only [wcvSum_one] at hh
  simpa using hh

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `E[(Σ ΔW¹_iΔW²_i)²] ≤ mesh·(t − s)`.** -/
theorem integral_cvSum_sq_le (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration P W₁ W₂ 𝓕) {s t : ℝ} (hs : 0 ≤ s) (p : Partition s t) :
    ∫ ω, cvSum W₁ W₂ p ω ^ 2 ∂P ≤ mesh p * (t - s) := by
  rw [integral_cvSum_sq hB₁ hB₂ hW₁ hW₂ h hs p]
  exact sum_step_sq_le p

/-- Cochrane (2023), A1 §1.6, pp. 567–568: for `|H| ≤ C`,
`E[(Σ H_{t_i}ΔW¹_iΔW²_i)²] ≤ C²·mesh·(t − s)`. -/
theorem integral_wcvSum_sq_le (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration P W₁ W₂ 𝓕) {s t : ℝ} (hs : 0 ≤ s) (p : Partition s t)
    {H : ℝ → Ω → ℝ} (hH : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) :
    ∫ ω, wcvSum W₁ W₂ H p ω ^ 2 ∂P ≤ C ^ 2 * (mesh p * (t - s)) := by
  have : IsProbabilityMeasure P := hB₁.isGaussianProcess.isProbabilityMeasure
  rw [integral_wcvSum_sq hB₁ hB₂ hW₁ hW₂ h hs p hH hHb]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (sum_step_sq_le p) (sq_nonneg C))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  have hb := hHb _ (t_mem p (Finset.mem_range.1 hi).le)
  have hle : ∫ ω, H (p.t i) ω ^ 2 ∂P ≤ ∫ _ω, C ^ 2 ∂P :=
    integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _) (integrable_const _)
      (ae_of_all _ fun ω => sq_le_sq' (abs_le.1 (hb ω)).1 (abs_le.1 (hb ω)).2)
  simpa using hle

/-! ## The conditional mean of the weighted sum -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the weighted cross sum of a bounded measurable `H` is
square integrable. -/
theorem memLp_wcvSum (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration P W₁ W₂ 𝓕) {s t : ℝ} (p : Partition s t) {H : ℝ → Ω → ℝ}
    (hHm : ∀ u ∈ Set.Icc s t, Measurable (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) : MemLp (wcvSum W₁ W₂ H p) 2 P :=
  memLp_finsetSum _ fun i hi => (memLp_cvTerm hB₁ hB₂ hW₁ hW₂ h _ _).of_le_mul (c := C)
    ((hHm _ (t_mem _ (Finset.mem_range.1 hi).le)).mul
      (measurable_cvTerm hW₁ hW₂ _ _)).aestronglyMeasurable
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hHb _ (t_mem _ (Finset.mem_range.1 hi).le) ω)
        (abs_nonneg _))

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `E[Σ H_{t_i}ΔW¹_iΔW²_i | 𝓕_s] = 0`** for a bounded
adapted `H` and a partition of `[s, t]`. -/
theorem condExp_wcvSum (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration P W₁ W₂ 𝓕) {s t : ℝ} (p : Partition s t) {H : ℝ → Ω → ℝ}
    (hH : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) :
    P[wcvSum W₁ W₂ H p | 𝓕 s] =ᵐ[P] 0 := by
  have : IsProbabilityMeasure P := hB₁.isGaussianProcess.isProbabilityMeasure
  have hHm : ∀ u ∈ Set.Icc s t, Measurable (H u) := fun u hu =>
    ((hH u hu).mono (𝓕.le u)).measurable
  have hf : Integrable (wcvSum W₁ W₂ H p) P :=
    (memLp_wcvSum hB₁ hB₂ hW₁ hW₂ h p hHm hHb).integrable one_le_two
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) hf
    (fun _ _ _ => (integrable_zero _ _ _).integrableOn) ?_
    stronglyMeasurable_const.aestronglyMeasurable).symm
  intro A hA _
  have hA' : MeasurableSet A := 𝓕.le s A hA
  have hterm : ∀ i ∈ Finset.range p.n, Integrable (fun ω => A.indicator (fun _ => (1 : ℝ)) ω *
      (H (p.t i) ω * cvTerm W₁ W₂ (p.t i) (p.t (i + 1)) ω)) P := by
    intro i hi
    have hm := t_mem p (Finset.mem_range.1 hi).le
    refine ((memLp_cvTerm hB₁ hB₂ hW₁ hW₂ h _ _).integrable one_le_two).bdd_mul (c := 1 * C)
      (((measurable_const.indicator hA').mul (hHm _ hm)).aestronglyMeasurable)
      (ae_of_all _ fun ω => ?_) |>.congr (ae_of_all _ fun ω => by simp only [Pi.mul_apply]; ring)
    rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
    refine mul_le_mul ?_ (hHb _ hm ω) (abs_nonneg _) zero_le_one
    by_cases hω : ω ∈ A <;> simp [hω]
  simp only [Pi.zero_apply, integral_zero]
  rw [← integral_indicator_one_mul hA']
  have e : (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * wcvSum W₁ W₂ H p ω)
      = fun ω => ∑ i ∈ Finset.range p.n, A.indicator (fun _ => (1 : ℝ)) ω *
        (H (p.t i) ω * cvTerm W₁ W₂ (p.t i) (p.t (i + 1)) ω) := by
    funext ω
    rw [wcvSum, Finset.mul_sum]
  rw [e, integral_finsetSum _ hterm]
  refine (Finset.sum_eq_zero fun i hi => ?_).symm
  have hm := t_mem p (Finset.mem_range.1 hi).le
  have hY : StronglyMeasurable[𝓕 (p.t i)]
      (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * H (p.t i) ω) :=
    ((stronglyMeasurable_const.indicator hA).mono (𝓕.mono hm.1)).mul (hH _ hm)
  have hh := integral_mul_cvTerm hB₁ hW₁ hW₂ h (p.strictMono.monotone (Nat.le_succ i)) hY
  rw [← hh]
  exact integral_congr_ae (ae_of_all _ fun ω => by ring)

/-! ## Convergence -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (the rule `H dW¹dW² = 0`):
`Σ H_{t_i}ΔW¹_iΔW²_i → 0` in `L²`** along ANY partitions of `[s, t]` with mesh `→ 0`, `0 ≤ s`,
for a bounded adapted `H`. -/
theorem L2Tendsto_wcvSum (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration P W₁ W₂ 𝓕) {s t : ℝ} (hs : 0 ≤ s) {H : ℝ → Ω → ℝ}
    (hH : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    L2Tendsto P (fun k => wcvSum W₁ W₂ H (ps k)) 0 := by
  have hHm : ∀ u ∈ Set.Icc s t, Measurable (H u) := fun u hu =>
    ((hH u hu).mono (𝓕.le u)).measurable
  refine ⟨fun k => memLp_wcvSum hB₁ hB₂ hW₁ hW₂ h (ps k) hHm hHb, MemLp.zero, ?_⟩
  change Tendsto (fun k => ∫ ω, (wcvSum W₁ W₂ H (ps k) ω - (0 : Ω → ℝ) ω) ^ 2 ∂P) atTop (𝓝 0)
  simp only [Pi.zero_apply, sub_zero]
  refine squeeze_zero (fun k => integral_nonneg fun _ => sq_nonneg _)
    (fun k => integral_wcvSum_sq_le hB₁ hB₂ hW₁ hW₂ h hs (ps k) hH hHb) ?_
  have := (hps.mul_const (t - s)).const_mul (C ^ 2)
  simpa using this

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (the rule `dW¹dW² = 0`): `Σ ΔW¹_iΔW²_i → 0` in
`L²`** along any partitions of `[s, t]` with mesh `→ 0`, `0 ≤ s`. -/
theorem L2Tendsto_cvSum (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration P W₁ W₂ 𝓕) {s t : ℝ} (hs : 0 ≤ s) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    L2Tendsto P (fun k => cvSum W₁ W₂ (ps k)) 0 := by
  have hh := L2Tendsto_wcvSum hB₁ hB₂ hW₁ hW₂ h hs (H := fun _ _ => 1)
    (fun _ _ => stronglyMeasurable_const) (C := 1) (fun _ _ _ => by simp) ps hps
  have e : ∀ k, wcvSum W₁ W₂ (fun _ _ => 1) (ps k) = cvSum W₁ W₂ (ps k) := fun k =>
    funext (wcvSum_one (ps k))
  simp only [e] at hh
  exact hh

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `Σ H_{t_i}ΔW¹_iΔW²_i → 0` almost surely** along any
partitions of `[s, t]`, `0 ≤ s`, with summable meshes. -/
theorem ae_tendsto_wcvSum_of_summable_mesh (hB₁ : IsPreBrownianReal W₁ P)
    (hB₂ : IsPreBrownianReal W₂ P) (hW₁ : ∀ t, Measurable (W₁ t))
    (hW₂ : ∀ t, Measurable (W₂ t)) (h : TwoBMFiltration P W₁ W₂ 𝓕) {s t : ℝ} (hs : 0 ≤ s)
    {H : ℝ → Ω → ℝ} (hH : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) (ps : ℕ → Partition s t)
    (hsum : Summable fun k => mesh (ps k)) :
    ∀ᵐ ω ∂P, Tendsto (fun k => wcvSum W₁ W₂ H (ps k) ω) atTop (𝓝 0) := by
  have hHm : ∀ u ∈ Set.Icc s t, Measurable (H u) := fun u hu =>
    ((hH u hu).mono (𝓕.le u)).measurable
  refine ae_tendsto_zero_of_summable_integral_sq (P := P)
    (F := fun k => wcvSum W₁ W₂ H (ps k)) (fun k => ?_)
    (fun k => (memLp_wcvSum hB₁ hB₂ hW₁ hW₂ h (ps k) hHm hHb).integrable_sq)
    (Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => sq_nonneg _)
      (fun k => integral_wcvSum_sq_le hB₁ hB₂ hW₁ hW₂ h hs (ps k) hH hHb)
      ((hsum.mul_right (t - s)).mul_left (C ^ 2)))
  exact Finset.measurable_sum _ fun i hi =>
    (hHm _ (t_mem _ (Finset.mem_range.1 hi).le)).mul (measurable_cvTerm hW₁ hW₂ _ _)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `Σ H_{t_i}ΔW¹_iΔW²_i → 0` almost surely along the
dyadic partitions** of `[s, t]`, `0 ≤ s < t`. -/
theorem ae_tendsto_wcvSum_dyadic (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration P W₁ W₂ 𝓕) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) {H : ℝ → Ω → ℝ}
    (hH : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (H u)) {C : ℝ}
    (hHb : ∀ u ∈ Set.Icc s t, ∀ ω, |H u ω| ≤ C) :
    ∀ᵐ ω ∂P, Tendsto (fun k => wcvSum W₁ W₂ H (dyadic hst k) ω) atTop (𝓝 0) :=
  ae_tendsto_wcvSum_of_summable_mesh hB₁ hB₂ hW₁ hW₂ h hs hH hHb _ (summable_mesh_dyadic hst)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `Σ ΔW¹_iΔW²_i → 0` almost surely along the dyadic
partitions** of `[s, t]`, `0 ≤ s < t`. -/
theorem ae_tendsto_cvSum_dyadic (hB₁ : IsPreBrownianReal W₁ P) (hB₂ : IsPreBrownianReal W₂ P)
    (hW₁ : ∀ t, Measurable (W₁ t)) (hW₂ : ∀ t, Measurable (W₂ t))
    (h : TwoBMFiltration P W₁ W₂ 𝓕) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    ∀ᵐ ω ∂P, Tendsto (fun k => cvSum W₁ W₂ (dyadic hst k) ω) atTop (𝓝 0) := by
  have hh := ae_tendsto_wcvSum_dyadic hB₁ hB₂ hW₁ hW₂ h hs hst (H := fun _ _ => 1)
    (fun _ _ => stronglyMeasurable_const) (C := 1) (fun _ _ _ => by simp)
  simpa only [wcvSum_one] using hh

/-! ## Non-vacuity on the constructed pair -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (non-vacuity): on the constructed pair `bmPath₁`,
`bmPath₂`, `E[(Σ ΔW¹_iΔW²_i)²] = Σ(Δt_i)²` for every partition of `[s, t]`, `0 ≤ s`. -/
theorem integral_cvSum_sq_bmPath {s t : ℝ} (hs : 0 ≤ s) (p : Partition s t) :
    ∫ ω, cvSum bmPath₁ bmPath₂ p ω ^ 2 ∂twoGauss
      = ∑ i ∈ Finset.range p.n, (p.t (i + 1) - p.t i) ^ 2 :=
  integral_cvSum_sq isBrownianReal_bmPath₁.toIsPreBrownianReal
    isBrownianReal_bmPath₂.toIsPreBrownianReal measurable_bmPath₁ measurable_bmPath₂
    twoBMFiltration_bmPath_isTwoBM hs p

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (non-vacuity): on the constructed pair,
`Σ ΔW¹_iΔW²_i → 0` almost surely along the dyadic partitions of `[s, t]`, `0 ≤ s < t`. -/
theorem ae_tendsto_cvSum_dyadic_bmPath {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    ∀ᵐ ω ∂twoGauss, Tendsto (fun k => cvSum bmPath₁ bmPath₂ (dyadic hst k) ω) atTop (𝓝 0) :=
  ae_tendsto_cvSum_dyadic isBrownianReal_bmPath₁.toIsPreBrownianReal
    isBrownianReal_bmPath₂.toIsPreBrownianReal measurable_bmPath₁ measurable_bmPath₂
    twoBMFiltration_bmPath_isTwoBM hs hst

end Cochrane.Monetarism.TidyR10TwoBMCross
