/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.TidyR7ItoIntegral

/-!
# The Itô integral of unbounded, mean-square continuous integrands

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for (1.32) with diffusive
bonds (chunk I5d of the Itô track): the product rule needs `∫ X K dW` with `X` itself an Itô
process (e.g. `X = W`), which is unbounded and, as constructed by `TidyR7ItoIntegral.itoInt`,
has no path regularity. The bounded class `TidyR7ItoIntegral.ItoIntegrand` does not contain it.

## The class

`MSIntegrand P 𝓕 G s t`: `G` is adapted on `[s, t]`, every `G u` is square integrable, and
`u ↦ G u` is **uniformly continuous in mean square** on `[s, t]` (`MSUnifCont`:
`∀ ε > 0, ∃ δ > 0, |u − v| ≤ δ ⇒ E[(G_u − G_v)²] ≤ ε`). No bound and no path regularity is
required. Every bounded admissible integrand is in the class (`ItoIntegrand.toMS`); so is every
Itô process with bounded coefficients (TidyR7ItoProcess), and the product of one with a bounded
admissible integrand (TidyR7ItoProducts). The integral is the SAME hypothesis-free
`TidyR7ItoIntegral.itoInt`; only the existence of the limit is new.

## Main results

* `L²` cells: `memLp_mul_incr_of_memLp`, `integral_cellSum_sq_of_memLp`
  (`E[(Σ ξ_kΔW_k)²] = Σ E[ξ_k²](b_k − a_k)` for square-integrable `𝓕_{a_k}`-measurable `ξ_k`),
  `integral_mul_cellSum_of_memLp` (`E[Z Σ ξ_kΔW_k] = 0` for square-integrable `𝓕_r`-measurable
  `Z`).
* Left-point sums: `integral_itoSum_sq_ms` (discrete isometry), `integral_itoSum_sub_sq_le_ms`
  (Cauchy estimate).
* Existence: `exists_dyadic_limit_ms`, `L2Tendsto_itoSum_ms` (**along any partitions with mesh
  `→ 0`**), `memLp_itoInt_ms`.
* Isometry: `tendsto_sum_integral_sq_ms` (`Σ E[G_{t_i}²]Δt_i → E[(∫ G dW)²]`, the isometry in
  the form `E[(∫G dW)²] = ∫ E[G_u²] du` as a limit of Riemann sums), `integral_itoInt_sq_le_ms`
  (`E[G_u²] ≤ ε` on `[s, t]` gives `E[(∫G dW)²] ≤ ε(t − s)`).
* Martingale property: `integral_mul_itoInt_ms` (`E[Z ∫_r^t G dW] = 0` for square-integrable
  `𝓕_r`-measurable `Z`), `condExp_itoInt_ms` (`E[∫_r^t G dW | 𝓕_r] = 0`).
-/

namespace Cochrane.Generality.TidyR7ItoUnbounded

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Generality.TidyR7StieltjesSums Cochrane.Generality.TidyR7BrownianTools
  Cochrane.Generality.TidyR7BrownianQV Cochrane.Generality.TidyR7ItoL2
  Cochrane.Generality.TidyR7ItoSums Cochrane.Generality.TidyR7ItoIntegral
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ mΩ}

/-! ## Increments against square-integrable coefficients -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: for `u ≤ v` and a square-integrable
`𝓕_u`-measurable `ξ`, `ξ²(W_v − W_u)²` is integrable (independent integrable factors).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.integrable_sq_mul_incr_sq). -/
theorem integrable_sq_mul_incr_sq (hB : IsPreBrownianReal W P) (h𝓕 : BMFiltration P W 𝓕)
    {u v : ℝ} (huv : u ≤ v) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[𝓕 u] ξ) (hξ2 : MemLp ξ 2 P) :
    Integrable (fun ω => ξ ω ^ 2 * incr W u v ω ^ 2) P := by
  have hI : IndepFun (fun ω => ξ ω ^ 2) (fun ω => incr W u v ω ^ 2) P :=
    ((indepFun_incr h𝓕 huv hξ).comp (φ := fun x => x ^ 2) (ψ := fun x => x ^ 2)
      (measurable_id.pow_const 2) (measurable_id.pow_const 2)).symm
  exact hI.integrable_mul hξ2.integrable_sq (integrable_incr_sq hB u v)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: for `u ≤ v` and a square-integrable
`𝓕_u`-measurable `ξ`, `ξ(W_v − W_u)` is square integrable.
Generalises `TidyR7ItoBridge.memLp_mul_incr`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.memLp_mul_incr_of_memLp). -/
theorem memLp_mul_incr_of_memLp (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {u v : ℝ} (huv : u ≤ v) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[𝓕 u] ξ) (hξ2 : MemLp ξ 2 P) :
    MemLp (fun ω => ξ ω * incr W u v ω) 2 P := by
  refine (memLp_two_iff_integrable_sq ((hξ.mono (𝓕.le u)).measurable.mul
    (measurable_incr hW u v)).aestronglyMeasurable).2 ?_
  refine (integrable_sq_mul_incr_sq hB h𝓕 huv hξ hξ2).congr (ae_of_all _ fun ω => ?_)
  simp only [Pi.mul_apply]
  ring

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the elementary integral of square-integrable adapted
coefficients is square integrable.
Generalises `TidyR7ItoSums.memLp_cellSum`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.memLp_cellSum_of_memLp). -/
theorem memLp_cellSum_of_memLp {κ : Type*} (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) {S : Finset κ} {a b : κ → ℝ}
    {ξ : κ → Ω → ℝ} (hab : ∀ k ∈ S, a k ≤ b k) (hξ : ∀ k ∈ S, StronglyMeasurable[𝓕 (a k)] (ξ k))
    (hξ2 : ∀ k ∈ S, MemLp (ξ k) 2 P) : MemLp (cellSum W S a b ξ) 2 P :=
  memLp_finsetSum S fun k hk => memLp_mul_incr_of_memLp hB hW h𝓕 (hab k hk) (hξ k hk) (hξ2 k hk)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the `L²` identity for non-overlapping cells with
unbounded coefficients.** For `0 ≤ a_k ≤ b_k`, pairwise non-overlapping cells, and
square-integrable `𝓕_{a_k}`-measurable `ξ_k`, `E[(Σ ξ_kΔW_k)²] = Σ E[ξ_k²](b_k − a_k)`.
Generalises `TidyR7ItoSums.integral_mul_cellSum_sq` (with `G = 1`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.integral_cellSum_sq_of_memLp). -/
theorem integral_cellSum_sq_of_memLp {κ : Type*} (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) {S : Finset κ} {a b : κ → ℝ}
    {ξ : κ → Ω → ℝ} (ha : ∀ k ∈ S, 0 ≤ a k) (hab : ∀ k ∈ S, a k ≤ b k)
    (hξ : ∀ k ∈ S, StronglyMeasurable[𝓕 (a k)] (ξ k)) (hξ2 : ∀ k ∈ S, MemLp (ξ k) 2 P)
    (hdisj : ∀ k ∈ S, ∀ l ∈ S, k ≠ l → b k ≤ a l ∨ b l ≤ a k ∨ a k = b k ∨ a l = b l) :
    ∫ ω, cellSum W S a b ξ ω ^ 2 ∂P = ∑ k ∈ S, (∫ ω, ξ k ω ^ 2 ∂P) * (b k - a k) := by
  classical
  have hx2 : ∀ k ∈ S, MemLp (fun ω => ξ k ω * incr W (a k) (b k) ω) 2 P := fun k hk =>
    memLp_mul_incr_of_memLp hB hW h𝓕 (hab k hk) (hξ k hk) (hξ2 k hk)
  have hint : ∀ k ∈ S, ∀ l ∈ S, Integrable (fun ω => (ξ k ω * incr W (a k) (b k) ω) *
      (ξ l ω * incr W (a l) (b l) ω)) P := fun k hk l hl => (hx2 k hk).integrable_mul (hx2 l hl)
  have e : (fun ω => cellSum W S a b ξ ω ^ 2) = fun ω => ∑ k ∈ S, ∑ l ∈ S,
      (ξ k ω * incr W (a k) (b k) ω) * (ξ l ω * incr W (a l) (b l) ω) := by
    funext ω
    rw [cellSum, sq, Finset.sum_mul_sum]
  have hpast : ∀ k ∈ S, ∀ v, b k ≤ v →
      StronglyMeasurable[𝓕 v] (fun ω => ξ k ω * incr W (a k) (b k) ω) := fun k hk v hv =>
    ((hξ k hk).mono (𝓕.mono ((hab k hk).trans hv))).mul
      ((stronglyMeasurable_incr h𝓕 (hab k hk)).mono (𝓕.mono hv))
  have hoff : ∀ k ∈ S, ∀ l ∈ S, b k ≤ a l → ∫ ω, (ξ k ω * incr W (a k) (b k) ω) *
      (ξ l ω * incr W (a l) (b l) ω) ∂P = 0 := by
    intro k hk l hl hkl
    have hY : StronglyMeasurable[𝓕 (a l)] (fun ω =>
        (ξ k ω * incr W (a k) (b k) ω) * ξ l ω) := (hpast k hk _ hkl).mul (hξ l hl)
    have h := integral_mul_incr hB hW h𝓕 (hab l hl) hY
    rw [← h]
    exact integral_congr_ae (ae_of_all _ fun ω => by ring)
  have hempty : ∀ k ∈ S, ∀ l ∈ S, a k = b k → ∫ ω, (ξ k ω * incr W (a k) (b k) ω) *
      (ξ l ω * incr W (a l) (b l) ω) ∂P = 0 := by
    intro k _ l _ hk
    rw [← hk]
    simp [incr_self]
  rw [e, integral_finsetSum _ fun k hk => integrable_finsetSum _ fun l hl => hint k hk l hl]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_finsetSum _ fun l hl => hint k hk l hl, Finset.sum_eq_single k]
  · have hY : StronglyMeasurable[𝓕 (a k)] (fun ω => ξ k ω ^ 2) := (hξ k hk).pow 2
    have h := integral_mul_incr_sq hB hW h𝓕 (ha k hk) (hab k hk) hY
    rw [mul_comm _ (b k - a k), ← h]
    exact integral_congr_ae (ae_of_all _ fun ω => by ring)
  · intro l hl hlk
    rcases hdisj k hk l hl (Ne.symm hlk) with h | h | h | h
    · exact hoff k hk l hl h
    · rw [← hoff l hl k hk h]
      exact integral_congr_ae (ae_of_all _ fun ω => by ring)
    · exact hempty k hk l hl h
    · rw [← hempty l hl k hk h]
      exact integral_congr_ae (ae_of_all _ fun ω => by ring)
  · intro h
    exact absurd hk h

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: elementary integrals are orthogonal to the
square-integrable past.** For `r ≤ a_k ≤ b_k`, square-integrable `𝓕_{a_k}`-measurable `ξ_k`
and square-integrable `𝓕_r`-measurable `Z`, `E[Z Σ ξ_kΔW_k] = 0`.
Generalises `TidyR7ItoSums.integral_mul_cellSum`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.integral_mul_cellSum_of_memLp). -/
theorem integral_mul_cellSum_of_memLp {κ : Type*} (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) {S : Finset κ} {a b : κ → ℝ}
    {ξ : κ → Ω → ℝ} {r : ℝ} (hra : ∀ k ∈ S, r ≤ a k) (hab : ∀ k ∈ S, a k ≤ b k)
    (hξ : ∀ k ∈ S, StronglyMeasurable[𝓕 (a k)] (ξ k)) (hξ2 : ∀ k ∈ S, MemLp (ξ k) 2 P)
    {Z : Ω → ℝ} (hZ : StronglyMeasurable[𝓕 r] Z) (hZ2 : MemLp Z 2 P) :
    ∫ ω, Z ω * cellSum W S a b ξ ω ∂P = 0 := by
  have hint : ∀ k ∈ S, Integrable (fun ω => Z ω * (ξ k ω * incr W (a k) (b k) ω)) P :=
    fun k hk => hZ2.integrable_mul (memLp_mul_incr_of_memLp hB hW h𝓕 (hab k hk) (hξ k hk)
      (hξ2 k hk))
  have e : (fun ω => Z ω * cellSum W S a b ξ ω)
      = fun ω => ∑ k ∈ S, Z ω * (ξ k ω * incr W (a k) (b k) ω) := by
    funext ω
    rw [cellSum, Finset.mul_sum]
  rw [e, integral_finsetSum _ hint]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hY : StronglyMeasurable[𝓕 (a k)] (fun ω => Z ω * ξ k ω) :=
    (hZ.mono (𝓕.mono (hra k hk))).mul (hξ k hk)
  rw [← integral_mul_incr hB hW h𝓕 (hab k hk) hY]
  exact integral_congr_ae (ae_of_all _ fun ω => by ring)

/-! ## The class of mean-square continuous integrands -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (the integrands `X·K` of (1.32) with diffusive
bonds): **uniform continuity in mean square on `[s, t]`**,
`∀ ε > 0, ∃ δ > 0, ∀ u, v ∈ [s, t], |u − v| ≤ δ → E[(G_u − G_v)²] ≤ ε`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.MSUnifCont). -/
def MSUnifCont (P : Measure Ω) (G : ℝ → Ω → ℝ) (s t : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ u ∈ Set.Icc s t, ∀ v ∈ Set.Icc s t, |u - v| ≤ δ →
    ∫ ω, (G u ω - G v ω) ^ 2 ∂P ≤ ε

variable (P 𝓕) (G : ℝ → Ω → ℝ) (s t : ℝ)

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (the integrands `X·K` of (1.32) with diffusive
bonds): **a mean-square continuous Itô integrand on `[s, t]`**: adapted, square integrable at
every time, uniformly continuous in mean square. No bound, no path regularity.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.MSIntegrand). -/
structure MSIntegrand where
  adapted : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (G u)
  memLp : ∀ u ∈ Set.Icc s t, MemLp (G u) 2 P
  cont : MSUnifCont P G s t

variable {P 𝓕 G s t}

/-- Cochrane (2023), A1 §1.6, pp. 567–568: a mean-square continuous integrand has measurable
values.
The analogue of `TidyR7ItoIntegral.ItoIntegrand.measurable`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.MSIntegrand.measurable). -/
theorem MSIntegrand.measurable (hG : MSIntegrand P 𝓕 G s t) {u : ℝ} (hu : u ∈ Set.Icc s t) :
    Measurable (G u) :=
  ((hG.adapted u hu).mono (𝓕.le u)).measurable

/-- Cochrane (2023), A1 §1.6, pp. 567–568: a mean-square continuous integrand on `[s, t]` is
one on every `[a, b] ⊆ [s, t]`.
The analogue of `TidyR7ItoIntegral.ItoIntegrand.mono`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.MSIntegrand.mono). -/
theorem MSIntegrand.mono (hG : MSIntegrand P 𝓕 G s t) {a b : ℝ} (ha : s ≤ a) (hb : b ≤ t) :
    MSIntegrand P 𝓕 G a b where
  adapted u hu := hG.adapted u ⟨ha.trans hu.1, hu.2.trans hb⟩
  memLp u hu := hG.memLp u ⟨ha.trans hu.1, hu.2.trans hb⟩
  cont ε hε := by
    obtain ⟨δ, hδ, h⟩ := hG.cont ε hε
    exact ⟨δ, hδ, fun u hu v hv huv => h u ⟨ha.trans hu.1, hu.2.trans hb⟩ v
      ⟨ha.trans hv.1, hv.2.trans hb⟩ huv⟩

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: bounded admissible integrands are mean-square
continuous** (`TidyR7ItoL2.exists_delta_integral_sq_sub_le`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.ItoIntegrand.toMS). -/
theorem ItoIntegrand.toMS [IsFiniteMeasure P] {C : ℝ} (hH : ItoIntegrand P 𝓕 G s t C) :
    MSIntegrand P 𝓕 G s t where
  adapted := hH.adapted
  memLp u hu := memLp_of_bound (hH.measurable hu) (hH.bound u hu)
  cont _ hε := exists_delta_integral_sq_sub_le (fun _ hu => hH.measurable hu) hH.bound hH.cont hε

/-- Cochrane (2023), A1 §1.6, pp. 567–568: an integrand constant in time, `Z` square
integrable and `𝓕_s`-measurable, is mean-square continuous on `[s, t]`.
Generalises `TidyR7ItoIntegral.itoIntegrand_const`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.msIntegrand_const). -/
theorem msIntegrand_const {Z : Ω → ℝ} (hZ : StronglyMeasurable[𝓕 s] Z) (hZ2 : MemLp Z 2 P) :
    MSIntegrand P 𝓕 (fun _ => Z) s t where
  adapted _ hu := hZ.mono (𝓕.mono hu.1)
  memLp _ _ := hZ2
  cont ε hε := ⟨1, one_pos, fun _ _ _ _ _ => by simp [hε.le]⟩

/-! ## Left-point sums of mean-square continuous integrands -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the left-point sum of a mean-square continuous
integrand is square integrable.
Generalises `TidyR7ItoSums.memLp_itoSum`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.memLp_itoSum_ms). -/
theorem memLp_itoSum_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hG : MSIntegrand P 𝓕 G s t) (p : Partition s t) :
    MemLp (itoSum W G p) 2 P :=
  memLp_cellSum_of_memLp hB hW h𝓕 (fun i _ => p.strictMono.monotone (Nat.le_succ i))
    (fun _ hi => hG.adapted _ (t_mem p (Finset.mem_range.1 hi).le))
    (fun _ hi => hG.memLp _ (t_mem p (Finset.mem_range.1 hi).le))

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the discrete isometry for unbounded integrands**,
`E[(Σ G_{t_i}ΔW_i)²] = Σ E[G_{t_i}²]Δt_i`, `0 ≤ s`.
Generalises `TidyR7ItoSums.integral_itoSum_sq`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.integral_itoSum_sq_ms). -/
theorem integral_itoSum_sq_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hG : MSIntegrand P 𝓕 G s t) (p : Partition s t) :
    ∫ ω, itoSum W G p ω ^ 2 ∂P
      = ∑ i ∈ Finset.range p.n, (∫ ω, G (p.t i) ω ^ 2 ∂P) * (p.t (i + 1) - p.t i) := by
  rw [itoSum_eq_cellSum]
  exact integral_cellSum_sq_of_memLp hB hW h𝓕
    (fun i hi => hs.trans (t_mem p (Finset.mem_range.1 hi).le).1)
    (fun i _ => p.strictMono.monotone (Nat.le_succ i))
    (fun _ hi => hG.adapted _ (t_mem p (Finset.mem_range.1 hi).le))
    (fun _ hi => hG.memLp _ (t_mem p (Finset.mem_range.1 hi).le)) (partition_cells_disjoint p)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `E[Z Σ G_{t_i}ΔW_i] = 0` for a square-integrable
`𝓕_s`-measurable `Z`.
Generalises `TidyR7ItoSums.integral_mul_itoSum`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.integral_mul_itoSum_ms). -/
theorem integral_mul_itoSum_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hG : MSIntegrand P 𝓕 G s t) (p : Partition s t) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[𝓕 s] Z) (hZ2 : MemLp Z 2 P) :
    ∫ ω, Z ω * itoSum W G p ω ∂P = 0 := by
  rw [itoSum_eq_cellSum]
  exact integral_mul_cellSum_of_memLp hB hW h𝓕
    (fun i hi => (t_mem p (Finset.mem_range.1 hi).le).1)
    (fun i _ => p.strictMono.monotone (Nat.le_succ i))
    (fun _ hi => hG.adapted _ (t_mem p (Finset.mem_range.1 hi).le))
    (fun _ hi => hG.memLp _ (t_mem p (Finset.mem_range.1 hi).le)) hZ hZ2

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the Cauchy estimate for unbounded integrands.** If
`E[(G_u − G_v)²] ≤ ε` whenever `|u − v| ≤ δ`, then `E[(I_p(G) − I_q(G))²] ≤ ε(t − s)` for all
partitions with meshes `≤ δ`.
Generalises `TidyR7ItoSums.integral_itoSum_sub_sq_le`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.integral_itoSum_sub_sq_le_ms). -/
theorem integral_itoSum_sub_sq_le_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hG : MSIntegrand P 𝓕 G s t) {ε δ : ℝ}
    (hδ : ∀ u ∈ Set.Icc s t, ∀ v ∈ Set.Icc s t, |u - v| ≤ δ →
      ∫ ω, (G u ω - G v ω) ^ 2 ∂P ≤ ε)
    (p q : Partition s t) (hp : mesh p ≤ δ) (hq : mesh q ≤ δ) :
    ∫ ω, (itoSum W G p ω - itoSum W G q ω) ^ 2 ∂P ≤ ε * (t - s) := by
  classical
  simp_rw [itoSum_sub_itoSum G p q]
  have hmem : ∀ k ∈ Finset.range p.n ×ˢ Finset.range q.n,
      p.t k.1 ∈ Set.Icc s t ∧ q.t k.2 ∈ Set.Icc s t := by
    intro k hk
    rw [Finset.mem_product] at hk
    exact ⟨t_mem p (Finset.mem_range.1 hk.1).le, t_mem q (Finset.mem_range.1 hk.2).le⟩
  rw [integral_cellSum_sq_of_memLp hB hW h𝓕 (S := Finset.range p.n ×ˢ Finset.range q.n)
    (a := fun k => cellA p q k.1 k.2) (b := fun k => cellB p q k.1 k.2)
    (ξ := fun k ω => G (p.t k.1) ω - G (q.t k.2) ω)
    (fun k hk => hs.trans ((hmem k hk).1.1.trans (le_max_left _ _)))
    (fun k _ => cellA_le_cellB p q k.1 k.2)
    (fun k hk => ((hG.adapted _ (hmem k hk).1).mono (𝓕.mono (le_max_left _ _))).sub
      ((hG.adapted _ (hmem k hk).2).mono (𝓕.mono (le_max_right _ _))))
    (fun k hk => (hG.memLp _ (hmem k hk).1).sub (hG.memLp _ (hmem k hk).2))
    (cells_disjoint p q), ← sum_cells_eq p q, Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.mem_product] at hk
  have hi := Finset.mem_range.1 hk.1
  have hj := Finset.mem_range.1 hk.2
  rcases (cellA_le_cellB p q k.1 k.2).lt_or_eq with hne | heq
  · refine mul_le_mul_of_nonneg_right ?_ (sub_nonneg.2 hne.le)
    exact hδ _ (t_mem p hi.le) _ (t_mem q hj.le)
      ((abs_sub_le_of_cell p q hi hj hne).trans (max_le hp hq))
  · rw [heq, sub_self, mul_zero, mul_zero]

/-! ## Existence -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the left-point sums of a mean-square continuous
integrand are mean-square Cauchy along any partitions with mesh `→ 0`, `0 ≤ s < t`.
Generalises `TidyR7ItoIntegral.cauchy_itoSum`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.cauchy_itoSum_ms). -/
theorem cauchy_itoSum_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) (hG : MSIntegrand P 𝓕 G s t)
    (ps : ℕ → Partition s t) (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) {ε : ℝ}
    (hε : 0 < ε) : ∃ N, ∀ k ≥ N, ∀ l ≥ N,
      ∫ ω, (itoSum W G (ps k) ω - itoSum W G (ps l) ω) ^ 2 ∂P ≤ ε := by
  have hts : 0 < t - s := sub_pos.2 hst
  obtain ⟨δ, hδ, hδG⟩ := hG.cont (ε / (t - s)) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hps.eventually (ge_mem_nhds hδ))
  refine ⟨N, fun k hk l hl => ?_⟩
  have h := integral_itoSum_sub_sq_le_ms hB hW h𝓕 hs hG hδG (ps k) (ps l) (hN k hk) (hN l hl)
  rwa [div_mul_cancel₀ _ hts.ne'] at h

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: existence of `∫ G dW` for unbounded integrands.**
For a mean-square continuous integrand and `0 ≤ s < t`, the dyadic left-point sums have an
`𝓕_t`-strongly measurable mean-square limit.
Generalises `TidyR7ItoIntegral.exists_dyadic_limit`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.exists_dyadic_limit_ms). -/
theorem exists_dyadic_limit_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) (hG : MSIntegrand P 𝓕 G s t) :
    ∃ Y, StronglyMeasurable[𝓕 t] Y ∧ L2Tendsto P (fun k => itoSum W G (dyadic hst k)) Y :=
  exists_L2Tendsto (𝓕.le t) (fun _ => stronglyMeasurable_itoSum h𝓕 hG.adapted _)
    (fun _ => memLp_itoSum_ms hB hW h𝓕 hG _)
    (fun _ hε => cauchy_itoSum_ms hB hW h𝓕 hs hst hG _ (tendsto_mesh_dyadic hst) hε)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the dyadic left-point sums of a mean-square
continuous integrand converge in mean square to `itoInt`.
Generalises `TidyR7ItoIntegral.L2Tendsto_dyadic`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.L2Tendsto_dyadic_ms). -/
theorem L2Tendsto_dyadic_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) (hG : MSIntegrand P 𝓕 G s t) :
    L2Tendsto P (fun k => itoSum W G (dyadic hst k)) (itoInt P 𝓕 W G s t) :=
  (itoInt_spec hst (exists_dyadic_limit_ms hB hW h𝓕 hs hst hG)).2

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `∫_s^t G dW` is square integrable for a mean-square
continuous integrand.
Generalises `TidyR7ItoIntegral.memLp_itoInt`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.memLp_itoInt_ms). -/
theorem memLp_itoInt_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hG : MSIntegrand P 𝓕 G s t) :
    MemLp (itoInt P 𝓕 W G s t) 2 P := by
  rcases lt_or_ge s t with hst | hts
  · exact (L2Tendsto_dyadic_ms hB hW h𝓕 hs hst hG).2.1
  · rw [itoInt_of_le hts]
    exact MemLp.zero

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: convergence along ANY partitions, unbounded
integrands.** For a mean-square continuous integrand, `0 ≤ s < t`, and any partitions of
`[s, t]` with mesh `→ 0`, `Σ G_{t_i}ΔW_i → ∫_s^t G dW` in mean square.
Generalises `TidyR7ItoIntegral.L2Tendsto_itoSum`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.L2Tendsto_itoSum_ms). -/
theorem L2Tendsto_itoSum_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) (hG : MSIntegrand P 𝓕 G s t)
    (ps : ℕ → Partition s t) (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    L2Tendsto P (fun k => itoSum W G (ps k)) (itoInt P 𝓕 W G s t) := by
  have hY := L2Tendsto_dyadic_ms hB hW h𝓕 hs hst hG
  have hmem : ∀ p : Partition s t, MemLp (itoSum W G p) 2 P := fun p =>
    memLp_itoSum_ms hB hW h𝓕 hG p
  have hts : 0 < t - s := sub_pos.2 hst
  refine ⟨fun k => hmem _, hY.2.1, ?_⟩
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨δ, hδ, hδG⟩ := hG.cont (η / (4 * (t - s))) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hps.eventually (ge_mem_nhds hδ))
  have hdy : ∀ᶠ m in atTop, mesh (dyadic hst m) ≤ δ :=
    (tendsto_mesh_dyadic hst).eventually (ge_mem_nhds hδ)
  refine ⟨N, fun k hk => ?_⟩
  have hev : ∀ᶠ m in atTop, ∫ ω, (itoSum W G (ps k) ω - itoInt P 𝓕 W G s t ω) ^ 2 ∂P
      ≤ 2 * (η / (4 * (t - s)) * (t - s))
        + 2 * ∫ ω, (itoSum W G (dyadic hst m) ω - itoInt P 𝓕 W G s t ω) ^ 2 ∂P := by
    filter_upwards [hdy] with m hm
    refine (integral_sq_sub_le (hmem (dyadic hst m)) (hmem (ps k)) hY.2.1).trans ?_
    have h := integral_itoSum_sub_sq_le_ms hB hW h𝓕 hs hG hδG (dyadic hst m) (ps k) hm (hN k hk)
    linarith
  have hlim : Tendsto (fun m => 2 * (η / (4 * (t - s)) * (t - s))
      + 2 * ∫ ω, (itoSum W G (dyadic hst m) ω - itoInt P 𝓕 W G s t ω) ^ 2 ∂P) atTop
      (𝓝 (2 * (η / (4 * (t - s)) * (t - s)) + 2 * 0)) :=
    tendsto_const_nhds.add (hY.2.2.const_mul 2)
  have h2 := ge_of_tendsto hlim hev
  have e2 : 2 * (η / (4 * (t - s)) * (t - s)) + 2 * 0 = η / 2 := by field_simp; ring
  rw [e2] at h2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
  linarith

/-! ## The isometry -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the Itô isometry for unbounded integrands.** Along
any partitions with mesh `→ 0`, `Σ E[G_{t_i}²]Δt_i → E[(∫_s^t G dW)²]`: the isometry
`E[(∫G dW)²] = ∫_s^t E[G_u²] du` with the time integral read as the limit of its Riemann sums.
The unbounded form of `TidyR7ItoIntegral.integral_itoInt_sq`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.tendsto_sum_integral_sq_ms). -/
theorem tendsto_sum_integral_sq_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s < t) (hG : MSIntegrand P 𝓕 G s t)
    (ps : ℕ → Partition s t) (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∑ i ∈ Finset.range (ps k).n,
        (∫ ω, G ((ps k).t i) ω ^ 2 ∂P) * ((ps k).t (i + 1) - (ps k).t i)) atTop
      (𝓝 (∫ ω, itoInt P 𝓕 W G s t ω ^ 2 ∂P)) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h := tendsto_integral_mul_sq_of_L2Tendsto (L2Tendsto_itoSum_ms hB hW h𝓕 hs hst hG ps hps)
    (G := fun _ => 1) measurable_const (C := 1) (fun _ => by simp)
  simp only [one_mul] at h
  exact h.congr fun k => integral_itoSum_sq_ms hB hW h𝓕 hs hG (ps k)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the isometry bound.** If `E[G_u²] ≤ ε` for all
`u ∈ [s, t]`, then `E[(∫_s^t G dW)²] ≤ ε(t − s)`, `0 ≤ s ≤ t`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.integral_itoInt_sq_le_ms). -/
theorem integral_itoInt_sq_le_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) (hst : s ≤ t) (hG : MSIntegrand P 𝓕 G s t)
    {ε : ℝ} (hε : ∀ u ∈ Set.Icc s t, ∫ ω, G u ω ^ 2 ∂P ≤ ε) :
    ∫ ω, itoInt P 𝓕 W G s t ω ^ 2 ∂P ≤ ε * (t - s) := by
  rcases lt_or_ge s t with hst' | hts
  · have h := tendsto_sum_integral_sq_ms hB hW h𝓕 hs hst' hG _ (tendsto_mesh_dyadic hst')
    refine le_of_tendsto h (Eventually.of_forall fun k => ?_)
    rw [← sum_step_eq (dyadic hst' k), Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ?_ (step_pos _ i).le
    exact hε _ (t_mem _ (Finset.mem_range.1 hi).le)
  · rw [itoInt_of_le hts, le_antisymm hts hst]
    simp

/-! ## The martingale property -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: for `X k → Y` in mean square and a square-integrable
`Z`, `E[Z X_k] → E[Z Y]` (Cauchy–Schwarz).
Generalises `TidyR7ItoL2.tendsto_integral_mul_of_L2Tendsto`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.tendsto_integral_mul_of_L2Tendsto_memLp). -/
theorem tendsto_integral_mul_of_L2Tendsto_memLp {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (h : L2Tendsto P X Y) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P) :
    Tendsto (fun k => ∫ ω, Z ω * X k ω ∂P) atTop (𝓝 (∫ ω, Z ω * Y ω ∂P)) := by
  have e : ∀ k, ∫ ω, Z ω * X k ω ∂P - ∫ ω, Z ω * Y ω ∂P
      = ∫ ω, Z ω * (X k ω - Y ω) ∂P := by
    intro k
    rw [← integral_sub (f := fun ω => Z ω * X k ω) (g := fun ω => Z ω * Y ω)
      (hZ2.integrable_mul (h.1 k)) (hZ2.integrable_mul h.2.1)]
    exact integral_congr_ae (ae_of_all _ fun ω => by ring)
  refine tendsto_sub_nhds_zero_iff.1 ?_
  simp_rw [e]
  exact tendsto_zero_of_sq_le (c := ∫ ω, Z ω ^ 2 ∂P)
    (fun k => sq_integral_mul_le hZ2 ((h.1 k).sub h.2.1)) h.2.2

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (`E_r ∫_r^t G dW = 0`): orthogonality to the
square-integrable past.** For a mean-square continuous integrand on `[r, t]`, `0 ≤ r`, and a
square-integrable `𝓕_r`-measurable `Z`, `E[Z ∫_r^t G dW] = 0`.
Generalises `TidyR7ItoIntegral.integral_mul_itoInt`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.integral_mul_itoInt_ms). -/
theorem integral_mul_itoInt_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {r : ℝ} (hr : 0 ≤ r) (hG : MSIntegrand P 𝓕 G r t)
    {Z : Ω → ℝ} (hZ : StronglyMeasurable[𝓕 r] Z) (hZ2 : MemLp Z 2 P) :
    ∫ ω, Z ω * itoInt P 𝓕 W G r t ω ∂P = 0 := by
  rcases lt_or_ge r t with hrt | htr
  · have t1 := tendsto_integral_mul_of_L2Tendsto_memLp (L2Tendsto_dyadic_ms hB hW h𝓕 hr hrt hG)
      hZ2
    have e : ∀ k, ∫ ω, Z ω * itoSum W G (dyadic hrt k) ω ∂P = 0 := fun k =>
      integral_mul_itoSum_ms hB hW h𝓕 hG _ hZ hZ2
    exact tendsto_nhds_unique t1 (tendsto_const_nhds.congr fun k => (e k).symm)
  · rw [itoInt_of_le htr]
    simp

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: `E[∫_r^t G dW | 𝓕_r] = 0`** a.s. for a mean-square
continuous integrand on `[r, t]`, `0 ≤ r`.
Generalises `TidyR7ItoIntegral.condExp_itoInt`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoUnbounded.condExp_itoInt_ms). -/
theorem condExp_itoInt_ms (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (h𝓕 : BMFiltration P W 𝓕) {r : ℝ} (hr : 0 ≤ r) (hG : MSIntegrand P 𝓕 G r t) :
    P[itoInt P 𝓕 W G r t | 𝓕 r] =ᵐ[P] 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hf : Integrable (itoInt P 𝓕 W G r t) P :=
    (memLp_itoInt_ms hB hW h𝓕 hr hG).integrable one_le_two
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le r) hf
    (fun _ _ _ => (integrable_zero _ _ _).integrableOn) ?_
    stronglyMeasurable_zero.aestronglyMeasurable).symm
  intro A hA _
  have hA' : MeasurableSet A := 𝓕.le r A hA
  have h := integral_mul_itoInt_ms hB hW h𝓕 hr hG (Z := A.indicator fun _ => (1 : ℝ))
    (stronglyMeasurable_const.indicator hA)
    (memLp_of_bound (measurable_const.indicator hA') (C := 1)
      (fun ω => by by_cases h : ω ∈ A <;> simp [h]))
  rw [integral_indicator_one_mul hA'] at h
  rw [h]
  simp

end Cochrane.Generality.TidyR7ItoUnbounded
