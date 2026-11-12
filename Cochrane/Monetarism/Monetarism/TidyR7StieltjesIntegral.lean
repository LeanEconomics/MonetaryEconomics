/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts
import Mathlib.Topology.Order.Cadlag

/-!
# The Riemann–Stieltjes integral `∫_a^b f dg` on a compact interval

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). The step in (1.32)
`Λ/P · dB + E_t d(Λ/P)·B = E_t d(ΛB/P)` is a product rule. It is proved later without a stochastic
integral, path by path, from the finite partition identity for products and limits of
Riemann–Stieltjes sums. This module and `TidyR7StieltjesSums`, `TidyR7StieltjesCalculus`,
`TidyR7StieltjesVariation` are the deterministic (pathwise) Riemann–Stieltjes tools for that (1.32)
product step.

## The integral

For `g` of bounded variation on `[a, b]` let `ĝ = clampFn a b g`, `ĝ(x) = g(max a (min b x))`
(`g` frozen outside `[a, b]`); `ĝ` has bounded variation on `ℝ` (`bv_clampFn`). Mathlib builds from
it the Lebesgue–Stieltjes vector measure `BoundedVariationOn.vectorMeasure`, which gives `[s, t]`
the mass `ĝ(t+) − ĝ(s−)`; it is `stMeasure a b g`. The integral is
`rsInt a b f g = ∫_{[a, b]} f d(stMeasure a b g)` (`∫ᵛ x in Icc a b, f x ∂• stMeasure a b g`).

**Atoms.** The total mass is `g(b) − g(a)` (`stMeasure_Icc`). An interior point `a < t < b`
carries the full jump `g(t+) − g(t−)` (`stMeasure_singleton_interior`), whatever the value
`g(t)`; the endpoints carry the one-sided jumps inside `[a, b]`: `a` the mass `g(a+) − g(a)`
(`stMeasure_singleton_left`), `b` the mass `g(b) − g(b−)` (`stMeasure_singleton_right`). So
`∫ 1 dg = g(b) − g(a)` (`rsInt_one`), and for continuous `f` this is the classical
Riemann–Stieltjes integral (proved in `TidyR7StieltjesSums`). A continuous `g` has no atoms
(`stMeasure_singleton_of_continuousOn`).

## Calculus

* `rsInt_add_left`, `rsInt_smul_left`: linearity in `f` (for `f` integrable against every
  finite-variation measure on `[a, b]`, `RSIntegrable`: continuous, càdlàg, or bounded measurable
  integrands, `rsIntegrable_of_continuousOn`, `rsIntegrable_of_isCadlag`,
  `rsIntegrable_of_measurable`).
* `rsInt_add_right`, `rsInt_smul_right`: linearity in `g`.
* `abs_rsInt_le`: `|∫ f dg| ≤ sup_{[a,b]}|f| · Var_{[a,b]}(g)`.
* `rsInt_add_interval`: `∫_a^b = ∫_a^c + ∫_c^b` (the atom of `g` at `c` splits correctly).
* Càdlàg functions: `countable_jumps` (a càdlàg function has countably many jumps), measurable,
  bounded on compacts.
-/

namespace Cochrane.Monetarism.TidyR7StieltjesIntegral

open MeasureTheory Filter Topology

/-! ## Freezing a function outside `[a, b]` -/

/-- Cochrane (2023), A1 §1.6, p. 567 (tool for (1.32)): `g` frozen outside `[a, b]`,
`x ↦ g(max a (min b x))`. -/
def clampFn (a b : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ := g (max a (min b x))

/-- Cochrane (2023), A1 §1.6, p. 567: `clampFn a b g = g` on `[a, b]`. -/
theorem clampFn_of_mem {a b x : ℝ} {g : ℝ → ℝ} (hx : x ∈ Set.Icc a b) :
    clampFn a b g x = g x := by
  simp only [clampFn, min_eq_right hx.2, max_eq_right hx.1]

/-- Cochrane (2023), A1 §1.6, p. 567: `clampFn a b g = g(a)` left of `a`. -/
theorem clampFn_of_le {a b x : ℝ} {g : ℝ → ℝ} (hx : x ≤ a) : clampFn a b g x = g a := by
  simp only [clampFn]
  rw [max_eq_left ((min_le_right b x).trans hx)]

/-- Cochrane (2023), A1 §1.6, p. 567: `clampFn a b g = g(b)` right of `b`. -/
theorem clampFn_of_ge {a b x : ℝ} {g : ℝ → ℝ} (hab : a ≤ b) (hx : b ≤ x) :
    clampFn a b g x = g b := by
  simp only [clampFn]
  rw [min_eq_left hx, max_eq_right hab]

/-- Cochrane (2023), A1 §1.6, p. 567: freezing does not increase the variation,
`Var_ℝ(clampFn a b g) ≤ Var_{[a,b]}(g)`.
A special case of Mathlib `eVariationOn.comp_le_of_monotoneOn`. -/
theorem eVariationOn_clampFn_le {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) :
    eVariationOn (clampFn a b g) Set.univ ≤ eVariationOn g (Set.Icc a b) :=
  eVariationOn.comp_le_of_monotoneOn g (fun x => max a (min b x))
    (fun _ _ _ _ hxy => max_le_max le_rfl (min_le_min le_rfl hxy))
    (fun _ _ => ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩)

/-- Cochrane (2023), A1 §1.6, p. 567: if `g` has bounded variation on `[a, b]`, the frozen
function has bounded variation on `ℝ`. -/
theorem bv_clampFn {a b : ℝ} {g : ℝ → ℝ} (hab : a ≤ b) (hg : BoundedVariationOn g (Set.Icc a b)) :
    BoundedVariationOn (clampFn a b g) Set.univ :=
  ne_top_of_le_ne_top hg (eVariationOn_clampFn_le hab g)

/-- Cochrane (2023), A1 §1.6, p. 567: if `g` is continuous on `[a, b]`, the frozen function is
continuous. -/
theorem continuous_clampFn {a b : ℝ} {g : ℝ → ℝ} (hab : a ≤ b) (hg : ContinuousOn g (Set.Icc a b)) :
    Continuous (clampFn a b g) :=
  hg.comp_continuous (continuous_const.max (continuous_const.min continuous_id))
    (fun _ => ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩)

/-- Cochrane (2023), A1 §1.6, p. 567: the frozen function has left limit `g(a)` at `a`. -/
theorem leftLim_clampFn_left (a b : ℝ) (g : ℝ → ℝ) :
    Function.leftLim (clampFn a b g) a = g a := by
  have h : Set.EqOn (clampFn a b g) (fun _ => g a) (Set.Iic a) := fun _ hx => clampFn_of_le hx
  have hc : ContinuousWithinAt (clampFn a b g) (Set.Iic a) a :=
    continuousWithinAt_const.congr h (h (le_refl a))
  rw [hc.leftLim_eq, clampFn_of_le le_rfl]

/-- Cochrane (2023), A1 §1.6, p. 567: the frozen function has right limit `g(b)` at `b`. -/
theorem rightLim_clampFn_right {a b : ℝ} (hab : a ≤ b) (g : ℝ → ℝ) :
    Function.rightLim (clampFn a b g) b = g b := by
  have h : Set.EqOn (clampFn a b g) (fun _ => g b) (Set.Ici b) :=
    fun _ hx => clampFn_of_ge hab hx
  have hc : ContinuousWithinAt (clampFn a b g) (Set.Ici b) b :=
    continuousWithinAt_const.congr h (h (le_refl b))
  rw [hc.rightLim_eq, clampFn_of_ge hab le_rfl]

/-- Cochrane (2023), A1 §1.6, p. 567: on `[a, b)` the right limit of the frozen function is the
right limit `g(x+)` of `g`. -/
theorem rightLim_clampFn {a b x : ℝ} {g : ℝ → ℝ} (hab : a ≤ b)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hx : x ∈ Set.Ico a b) :
    Function.rightLim (clampFn a b g) x = Function.rightLim g x := by
  have ht := (bv_clampFn hab hg).tendsto_rightLim x
  have hev : clampFn a b g =ᶠ[𝓝[>] x] g := by
    filter_upwards [Ioo_mem_nhdsGT hx.2] with y hy
    exact clampFn_of_mem ⟨hx.1.trans hy.1.le, hy.2.le⟩
  exact (rightLim_eq_of_tendsto (ht.congr' hev)).symm

/-- Cochrane (2023), A1 §1.6, p. 567: on `(a, b]` the left limit of the frozen function is the
left limit `g(x−)` of `g`. -/
theorem leftLim_clampFn {a b x : ℝ} {g : ℝ → ℝ} (hab : a ≤ b)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hx : x ∈ Set.Ioc a b) :
    Function.leftLim (clampFn a b g) x = Function.leftLim g x := by
  have ht := (bv_clampFn hab hg).tendsto_leftLim x
  have hev : clampFn a b g =ᶠ[𝓝[<] x] g := by
    filter_upwards [Ioo_mem_nhdsLT hx.1] with y hy
    exact clampFn_of_mem ⟨hy.1.le, hy.2.le.trans hx.2⟩
  exact (leftLim_eq_of_tendsto (ht.congr' hev)).symm

/-! ## The Stieltjes measure and the integral -/

/-- Cochrane (2023), A1 §1.6, p. 567 (tool for (1.32)): **the Lebesgue–Stieltjes measure of `g`
on `[a, b]`**, Mathlib's `BoundedVariationOn.vectorMeasure` of `clampFn a b g` when this has
bounded variation (and `0` otherwise). It gives `[s, t]` the mass `ĝ(t+) − ĝ(s−)`. -/
noncomputable def stMeasure (a b : ℝ) (g : ℝ → ℝ) : VectorMeasure ℝ ℝ :=
  @dite _ (BoundedVariationOn (clampFn a b g) Set.univ) (Classical.dec _)
    (fun h => h.vectorMeasure) (fun _ => 0)

/-- Cochrane (2023), A1 §1.6, p. 567: `stMeasure` is the vector measure of the frozen function. -/
theorem stMeasure_eq {a b : ℝ} {g : ℝ → ℝ} (h : BoundedVariationOn (clampFn a b g) Set.univ) :
    stMeasure a b g = h.vectorMeasure := by
  rw [stMeasure, dite_eq_left h]

/-- Cochrane (2023), A1 §1.6, p. 567: the Stieltjes measure has finite total variation.
From Mathlib `BoundedVariationOn.variation_vectorMeasure_univ_le`. -/
theorem isFiniteMeasure_stMeasure (a b : ℝ) (g : ℝ → ℝ) :
    IsFiniteMeasure (stMeasure a b g).variation := by
  by_cases h : BoundedVariationOn (clampFn a b g) Set.univ
  · rw [stMeasure_eq h]
    exact ⟨lt_of_le_of_lt h.variation_vectorMeasure_univ_le (lt_top_iff_ne_top.2 h)⟩
  · rw [stMeasure, dite_eq_right h, VectorMeasure.variation_zero]
    infer_instance

/-- Cochrane (2023), A1 §1.6, p. 567: the total variation of the Stieltjes measure of any set is
at most `Var_{[a,b]}(g)`.
From Mathlib `BoundedVariationOn.variation_vectorMeasure_univ_le`. -/
theorem variation_real_le {a b : ℝ} {g : ℝ → ℝ} (hab : a ≤ b)
    (hg : BoundedVariationOn g (Set.Icc a b)) (s : Set ℝ) :
    (stMeasure a b g).variation.real s ≤ (eVariationOn g (Set.Icc a b)).toReal := by
  have h := bv_clampFn hab hg
  rw [stMeasure_eq h, Measure.real]
  exact ENNReal.toReal_mono hg ((measure_mono (Set.subset_univ s)).trans
    (h.variation_vectorMeasure_univ_le.trans (eVariationOn_clampFn_le hab g)))

/-- Cochrane (2023), A1 §1.6, p. 567 (tool for (1.32)): **the Riemann–Stieltjes integral**
`∫_a^b f dg = ∫_{[a, b]} f d(stMeasure a b g)`. -/
noncomputable def rsInt (a b : ℝ) (f g : ℝ → ℝ) : ℝ :=
  ∫ᵛ x in Set.Icc a b, f x ∂• stMeasure a b g

/-! ## How the integral treats the atoms of `g` -/

/-- Cochrane (2023), A1 §1.6, p. 567: the total mass of `[a, b]` is `g(b) − g(a)`.
Mathlib `BoundedVariationOn.vectorMeasure_Icc` for the frozen function. -/
theorem stMeasure_Icc {a b : ℝ} {g : ℝ → ℝ} (hab : a ≤ b)
    (hg : BoundedVariationOn g (Set.Icc a b)) : stMeasure a b g (Set.Icc a b) = g b - g a := by
  rw [stMeasure_eq (bv_clampFn hab hg), (bv_clampFn hab hg).vectorMeasure_Icc hab,
    rightLim_clampFn_right hab, leftLim_clampFn_left]

/-- Cochrane (2023), A1 §1.6, p. 567: the left endpoint carries the mass `g(a+) − g(a)`.
Mathlib `BoundedVariationOn.vectorMeasure_singleton` for the frozen function. -/
theorem stMeasure_singleton_left {a b : ℝ} {g : ℝ → ℝ} (hab : a < b)
    (hg : BoundedVariationOn g (Set.Icc a b)) :
    stMeasure a b g {a} = Function.rightLim g a - g a := by
  rw [stMeasure_eq (bv_clampFn hab.le hg), (bv_clampFn hab.le hg).vectorMeasure_singleton,
    rightLim_clampFn hab.le hg ⟨le_rfl, hab⟩, leftLim_clampFn_left]

/-- Cochrane (2023), A1 §1.6, p. 567: an interior point carries the full jump
`g(t+) − g(t−)`, independently of the value `g(t)`.
Mathlib `BoundedVariationOn.vectorMeasure_singleton` for the frozen function. -/
theorem stMeasure_singleton_interior {a b t : ℝ} {g : ℝ → ℝ}
    (hg : BoundedVariationOn g (Set.Icc a b)) (hat : a < t) (htb : t < b) :
    stMeasure a b g {t} = Function.rightLim g t - Function.leftLim g t := by
  have hab : a ≤ b := hat.le.trans htb.le
  rw [stMeasure_eq (bv_clampFn hab hg), (bv_clampFn hab hg).vectorMeasure_singleton,
    rightLim_clampFn hab hg ⟨hat.le, htb⟩, leftLim_clampFn hab hg ⟨hat, htb.le⟩]

/-- Cochrane (2023), A1 §1.6, p. 567: the right endpoint carries the mass `g(b) − g(b−)`.
Mathlib `BoundedVariationOn.vectorMeasure_singleton` for the frozen function. -/
theorem stMeasure_singleton_right {a b : ℝ} {g : ℝ → ℝ} (hab : a < b)
    (hg : BoundedVariationOn g (Set.Icc a b)) :
    stMeasure a b g {b} = g b - Function.leftLim g b := by
  rw [stMeasure_eq (bv_clampFn hab.le hg), (bv_clampFn hab.le hg).vectorMeasure_singleton,
    rightLim_clampFn_right hab.le, leftLim_clampFn hab.le hg ⟨hab, le_rfl⟩]

/-- Cochrane (2023), A1 §1.6, p. 567: the measure of `(s, t]` is `ĝ(t+) − ĝ(s+)`.
Restates Mathlib `BoundedVariationOn.vectorMeasure_Ioc`. -/
theorem stMeasure_Ioc {a b s t : ℝ} {g : ℝ → ℝ} (hab : a ≤ b)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hst : s ≤ t) :
    stMeasure a b g (Set.Ioc s t) =
      Function.rightLim (clampFn a b g) t - Function.rightLim (clampFn a b g) s := by
  rw [stMeasure_eq (bv_clampFn hab hg), (bv_clampFn hab hg).vectorMeasure_Ioc hst]

/-- Cochrane (2023), A1 §1.6, p. 567: for `g` continuous on `[a, b]` the right and left limits
of the frozen function are its values. -/
theorem rightLim_clampFn_of_continuousOn {a b : ℝ} {g : ℝ → ℝ} (hab : a ≤ b)
    (hgc : ContinuousOn g (Set.Icc a b)) (x : ℝ) :
    Function.rightLim (clampFn a b g) x = clampFn a b g x ∧
      Function.leftLim (clampFn a b g) x = clampFn a b g x :=
  ⟨((continuous_clampFn hab hgc).continuousAt.continuousWithinAt).rightLim_eq,
    ((continuous_clampFn hab hgc).continuousAt.continuousWithinAt).leftLim_eq⟩

/-- Cochrane (2023), A1 §1.6, p. 567: **a continuous `g` has no atoms**. -/
theorem stMeasure_singleton_of_continuousOn {a b : ℝ} {g : ℝ → ℝ} (hab : a ≤ b)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hgc : ContinuousOn g (Set.Icc a b)) (x : ℝ) :
    (stMeasure a b g).variation {x} = 0 := by
  rw [stMeasure_eq (bv_clampFn hab hg), (bv_clampFn hab hg).variation_vectorMeasure_singleton,
    (rightLim_clampFn_of_continuousOn hab hgc x).1, (rightLim_clampFn_of_continuousOn hab hgc x).2]
  simp

/-- Cochrane (2023), A1 §1.6, p. 567: for continuous `g`, `(s, t] ⊆ [a, b]` has mass
`g(t) − g(s)`. -/
theorem stMeasure_Ioc_of_continuousOn {a b s t : ℝ} {g : ℝ → ℝ} (hab : a ≤ b)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hgc : ContinuousOn g (Set.Icc a b))
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t) :
    stMeasure a b g (Set.Ioc s t) = g t - g s := by
  rw [stMeasure_Ioc hab hg hst, (rightLim_clampFn_of_continuousOn hab hgc t).1,
    (rightLim_clampFn_of_continuousOn hab hgc s).1, clampFn_of_mem hs, clampFn_of_mem ht]

/-- Cochrane (2023), A1 §1.6, p. 567: `∫_a^b 1 dg = g(b) − g(a)`. -/
theorem rsInt_one {a b : ℝ} {g : ℝ → ℝ} (hab : a ≤ b) (hg : BoundedVariationOn g (Set.Icc a b)) :
    rsInt a b (fun _ => 1) g = g b - g a := by
  have := isFiniteMeasure_stMeasure a b g
  rw [rsInt, VectorMeasure.setIntegral_const, stMeasure_Icc hab hg]
  simp

/-! ## Integrable integrands -/

/-- Cochrane (2023), A1 §1.6, p. 567: `f` is integrable on `[a, b]` against every
finite-variation vector measure (continuous, càdlàg and bounded measurable integrands are). -/
def RSIntegrable (a b : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ν : VectorMeasure ℝ ℝ, IsFiniteMeasure ν.variation → ν.IntegrableOn f (Set.Icc a b)

/-- Cochrane (2023), A1 §1.6, p. 567: continuous integrands are integrable. -/
theorem rsIntegrable_of_continuousOn {a b : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b)) :
    RSIntegrable a b f := by
  intro ν _
  change Integrable f (ν.restrict (Set.Icc a b)).variation
  rw [VectorMeasure.variation_restrict measurableSet_Icc]
  exact hf.integrableOn_compact isCompact_Icc

/-- Cochrane (2023), A1 §1.6, p. 567: bounded measurable integrands are integrable. -/
theorem rsIntegrable_of_measurable {a b C : ℝ} {f : ℝ → ℝ} (hf : Measurable f)
    (hC : ∀ x ∈ Set.Icc a b, |f x| ≤ C) : RSIntegrable a b f := by
  intro ν _
  change Integrable f (ν.restrict (Set.Icc a b)).variation
  rw [VectorMeasure.variation_restrict measurableSet_Icc]
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (ae_restrict_of_forall_mem measurableSet_Icc fun x hx => by
      rw [Real.norm_eq_abs]; exact hC x hx)

/-- Cochrane (2023), A1 §1.6, p. 567: integrability passes to subintervals. -/
theorem RSIntegrable.mono {a b c d : ℝ} {f : ℝ → ℝ} (hf : RSIntegrable a b f) (hca : a ≤ c)
    (hdb : d ≤ b) : RSIntegrable c d f :=
  fun ν hν => (hf ν hν).mono measurableSet_Icc (Set.Icc_subset_Icc hca hdb)

/-! ## Càdlàg functions -/

/-- Cochrane (2023), A1 §1.6, p. 567: near the right of any point, a càdlàg function has jumps
smaller than `ε`. -/
theorem exists_small_jumps_right {f : ℝ → ℝ} (hf : IsCadlag f) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ Set.Ioo x (x + δ), |f y - Function.leftLim f y| < ε := by
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousWithinAt_iff.1 (hf.isRightContinuous x) (ε / 2)
    (half_pos hε)
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have hnear : ∀ z ∈ Set.Ioo x (x + δ), |f z - f x| < ε / 2 := by
    intro z hz
    have := hδf hz.1 (by rw [Real.dist_eq, abs_of_pos (sub_pos.2 hz.1)]; linarith [hz.2])
    rwa [Real.dist_eq] at this
  have hlim : Tendsto (fun z => |f z - f x|) (𝓝[<] y) (𝓝 |Function.leftLim f y - f x|) :=
    ((hf.tendsto_nhdsLT_leftLim y).sub tendsto_const_nhds).abs
  have hle : |Function.leftLim f y - f x| ≤ ε / 2 := by
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT hy.1] with z hz
    exact (hnear z ⟨hz.1, hz.2.trans hy.2⟩).le
  have h1 := hnear y hy
  calc |f y - Function.leftLim f y| = |(f y - f x) - (Function.leftLim f y - f x)| := by ring_nf
    _ ≤ |f y - f x| + |Function.leftLim f y - f x| := abs_sub _ _
    _ < ε := by linarith

/-- Cochrane (2023), A1 §1.6, p. 567: **a càdlàg function has countably many jumps**:
`{x | f x ≠ f(x−)}` is countable. (For each `ε`, the jumps larger than `ε` are isolated from the
right, `exists_small_jumps_right`.) -/
theorem countable_jumps {f : ℝ → ℝ} (hf : IsCadlag f) :
    {x | f x ≠ Function.leftLim f x}.Countable := by
  have hU : {x | f x ≠ Function.leftLim f x} ⊆
      ⋃ m : ℕ, {x | 1 / ((m : ℝ) + 1) < |f x - Function.leftLim f x|} := by
    intro x hx
    have hpos : 0 < |f x - Function.leftLim f x| := abs_pos.2 (sub_ne_zero.2 hx)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
    exact Set.mem_iUnion.2 ⟨m, hm⟩
  refine Set.Countable.mono hU (Set.countable_iUnion fun m => ?_)
  set J := {x | 1 / ((m : ℝ) + 1) < |f x - Function.leftLim f x|}
  refine Set.Countable.mono ?_ (countable_setOfPred_isolated_right_within (s := J))
  intro x hx
  refine ⟨hx, ?_⟩
  obtain ⟨δ, hδ, hsmall⟩ := exists_small_jumps_right hf x (ε := 1 / ((m : ℝ) + 1))
    (by positivity)
  rw [← empty_mem_iff_bot, mem_nhdsWithin]
  refine ⟨Set.Iio (x + δ), isOpen_Iio, show x < x + δ by linarith, fun y hy => ?_⟩
  exact absurd (hsmall y ⟨hy.2.2, hy.1⟩) (not_lt.2 hy.2.1.le)

/-- Cochrane (2023), A1 §1.6, p. 567: a càdlàg function is continuous where it does not jump. -/
theorem continuousAt_of_leftLim_eq {f : ℝ → ℝ} (hf : IsCadlag f) {x : ℝ}
    (h : Function.leftLim f x = f x) : ContinuousAt f x := by
  rw [continuousAt_iff_continuous_left'_right']
  refine ⟨?_, hf.isRightContinuous x⟩
  have := hf.tendsto_nhdsLT_leftLim x
  rw [h] at this
  exact this

/-- Cochrane (2023), A1 §1.6, p. 567: càdlàg functions are measurable. -/
theorem measurable_of_isCadlag {f : ℝ → ℝ} (hf : IsCadlag f) : Measurable f := by
  refine measurable_of_countable_not_continuousAt ((countable_jumps hf).mono fun x hx => ?_)
  exact fun h => hx (continuousAt_of_leftLim_eq hf h.symm)

/-- Cochrane (2023), A1 §1.6, p. 567: a càdlàg function is bounded on `[a, b]`.
Mathlib `isBounded_image_of_isCadlag_of_isCompact` in `|f| ≤ C` form. -/
theorem exists_bound_of_isCadlag {f : ℝ → ℝ} (hf : IsCadlag f) (a b : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ Set.Icc a b, |f x| ≤ C := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).1
    (isBounded_image_of_isCadlag_of_isCompact hf (isCompact_Icc (a := a) (b := b)))
  refine ⟨max r 0, le_max_right _ _, fun x hx => ?_⟩
  have := hr ⟨x, hx, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- Cochrane (2023), A1 §1.6, p. 567: càdlàg integrands are integrable. -/
theorem rsIntegrable_of_isCadlag {a b : ℝ} {f : ℝ → ℝ} (hf : IsCadlag f) : RSIntegrable a b f := by
  obtain ⟨C, -, hC⟩ := exists_bound_of_isCadlag hf a b
  exact rsIntegrable_of_measurable (measurable_of_isCadlag hf) hC

/-! ## Linearity in `f` and in `g` -/

/-- Cochrane (2023), A1 §1.6, p. 567: **linearity in the integrand**,
`∫(f₁ + f₂)dg = ∫f₁dg + ∫f₂dg`.
Restates Mathlib `VectorMeasure.integral_fun_add`. -/
theorem rsInt_add_left {a b : ℝ} {f₁ f₂ g : ℝ → ℝ} (hf₁ : RSIntegrable a b f₁)
    (hf₂ : RSIntegrable a b f₂) :
    rsInt a b (fun x => f₁ x + f₂ x) g = rsInt a b f₁ g + rsInt a b f₂ g :=
  VectorMeasure.integral_fun_add (hf₁ _ (isFiniteMeasure_stMeasure a b g))
    (hf₂ _ (isFiniteMeasure_stMeasure a b g))

/-- Cochrane (2023), A1 §1.6, p. 567: **homogeneity in the integrand**, `∫(cf)dg = c∫f dg`.
Restates Mathlib `VectorMeasure.integral_fun_smul`. -/
theorem rsInt_smul_left {a b : ℝ} (c : ℝ) (f g : ℝ → ℝ) :
    rsInt a b (fun x => c * f x) g = c * rsInt a b f g :=
  VectorMeasure.integral_fun_smul _ _ c f

/-- Cochrane (2023), A1 §1.6, p. 567: the variation of a sum is at most the sum of the
variations. -/
theorem eVariationOn_add_le (f g : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => f x + g x) s ≤ eVariationOn f s + eVariationOn g s := by
  refine iSup_le fun p => ?_
  calc ∑ i ∈ Finset.range p.1,
        edist (f (p.2.1 (i + 1)) + g (p.2.1 (i + 1))) (f (p.2.1 i) + g (p.2.1 i))
      ≤ ∑ i ∈ Finset.range p.1, (edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) +
          edist (g (p.2.1 (i + 1))) (g (p.2.1 i))) :=
        Finset.sum_le_sum fun _ _ => edist_add_add_le _ _ _ _
    _ = ∑ i ∈ Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) +
          ∑ i ∈ Finset.range p.1, edist (g (p.2.1 (i + 1))) (g (p.2.1 i)) :=
        Finset.sum_add_distrib
    _ ≤ eVariationOn f s + eVariationOn g s :=
        add_le_add (eVariationOn.sum_le p.2.2.1 p.2.2.2) (eVariationOn.sum_le p.2.2.1 p.2.2.2)

/-- Cochrane (2023), A1 §1.6, p. 567: right limits of bounded-variation functions add (up to a
constant). -/
theorem rightLim_add_sub {G₁ G₂ : ℝ → ℝ} (h₁ : BoundedVariationOn G₁ Set.univ)
    (h₂ : BoundedVariationOn G₂ Set.univ) (k x : ℝ) :
    Function.rightLim (fun y => G₁ y + G₂ y - k) x =
      Function.rightLim G₁ x + Function.rightLim G₂ x - k :=
  rightLim_eq_of_tendsto (((h₁.tendsto_rightLim x).add (h₂.tendsto_rightLim x)).sub
    tendsto_const_nhds)

/-- Cochrane (2023), A1 §1.6, p. 567: left limits of bounded-variation functions add (up to a
constant). -/
theorem leftLim_add_sub {G₁ G₂ : ℝ → ℝ} (h₁ : BoundedVariationOn G₁ Set.univ)
    (h₂ : BoundedVariationOn G₂ Set.univ) (k x : ℝ) :
    Function.leftLim (fun y => G₁ y + G₂ y - k) x =
      Function.leftLim G₁ x + Function.leftLim G₂ x - k :=
  leftLim_eq_of_tendsto (((h₁.tendsto_leftLim x).add (h₂.tendsto_leftLim x)).sub
    tendsto_const_nhds)

/-- Cochrane (2023), A1 §1.6, p. 567: the Stieltjes measure is additive in `g`. -/
theorem stMeasure_add {a b : ℝ} {g₁ g₂ : ℝ → ℝ} (hab : a ≤ b)
    (hg₁ : BoundedVariationOn g₁ (Set.Icc a b)) (hg₂ : BoundedVariationOn g₂ (Set.Icc a b)) :
    stMeasure a b (fun x => g₁ x + g₂ x) = stMeasure a b g₁ + stMeasure a b g₂ := by
  have h₁ := bv_clampFn hab hg₁
  have h₂ := bv_clampFn hab hg₂
  have e : clampFn a b (fun x => g₁ x + g₂ x) =
      fun y => clampFn a b g₁ y + clampFn a b g₂ y - 0 := by
    funext y; simp [clampFn]
  have h₁₂ : BoundedVariationOn (clampFn a b (fun x => g₁ x + g₂ x)) Set.univ := by
    have := eVariationOn_add_le (clampFn a b g₁) (clampFn a b g₂) Set.univ
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨h₁, h₂⟩) this
  rw [stMeasure_eq h₁, stMeasure_eq h₂, stMeasure_eq h₁₂]
  refine VectorMeasure.ext_of_Icc _ _ fun s t hst => ?_
  rw [add_apply, h₁₂.vectorMeasure_Icc hst, h₁.vectorMeasure_Icc hst,
    h₂.vectorMeasure_Icc hst, e, rightLim_add_sub h₁ h₂, leftLim_add_sub h₁ h₂]
  ring

/-- Cochrane (2023), A1 §1.6, p. 567: **linearity in the integrator**,
`∫f d(g₁ + g₂) = ∫f dg₁ + ∫f dg₂`.
Restates Mathlib `VectorMeasure.integral_add_vectorMeasure`. -/
theorem rsInt_add_right {a b : ℝ} {f g₁ g₂ : ℝ → ℝ} (hab : a ≤ b)
    (hg₁ : BoundedVariationOn g₁ (Set.Icc a b)) (hg₂ : BoundedVariationOn g₂ (Set.Icc a b))
    (hf : RSIntegrable a b f) :
    rsInt a b f (fun x => g₁ x + g₂ x) = rsInt a b f g₁ + rsInt a b f g₂ := by
  rw [rsInt, stMeasure_add hab hg₁ hg₂, VectorMeasure.restrict_add,
    VectorMeasure.integral_add_vectorMeasure (hf _ (isFiniteMeasure_stMeasure a b g₁))
      (hf _ (isFiniteMeasure_stMeasure a b g₂))]
  rfl

/-- Cochrane (2023), A1 §1.6, p. 567: the Stieltjes measure is homogeneous in `g`. -/
theorem stMeasure_smul {a b : ℝ} {g : ℝ → ℝ} (c : ℝ) (hab : a ≤ b)
    (hg : BoundedVariationOn g (Set.Icc a b)) :
    stMeasure a b (fun x => c * g x) = c • stMeasure a b g := by
  have h₁ := bv_clampFn hab hg
  have hk : BoundedVariationOn (fun _ : ℝ => c) Set.univ := by
    rw [BoundedVariationOn, eVariationOn.constant_on
      (Set.subsingleton_of_forall_eq c fun _ ⟨_, _, hy⟩ => hy.symm)]
    exact ENNReal.zero_ne_top
  have hc : BoundedVariationOn (clampFn a b (fun x => c * g x)) Set.univ := hk.mul h₁
  rw [stMeasure_eq h₁, stMeasure_eq hc]
  refine VectorMeasure.ext_of_Icc _ _ fun s t hst => ?_
  rw [smul_apply, hc.vectorMeasure_Icc hst, h₁.vectorMeasure_Icc hst]
  have e : clampFn a b (fun x => c * g x) = fun y => c * clampFn a b g y := rfl
  rw [e, rightLim_eq_of_tendsto (tendsto_const_nhds.mul (h₁.tendsto_rightLim t)),
    leftLim_eq_of_tendsto (tendsto_const_nhds.mul (h₁.tendsto_leftLim s)), smul_eq_mul]
  ring

/-- Cochrane (2023), A1 §1.6, p. 567: **homogeneity in the integrator**, `∫f d(cg) = c∫f dg`.
Restates Mathlib `VectorMeasure.integral_smul_vectorMeasure`. -/
theorem rsInt_smul_right {a b : ℝ} {f g : ℝ → ℝ} (c : ℝ) (hab : a ≤ b)
    (hg : BoundedVariationOn g (Set.Icc a b)) :
    rsInt a b f (fun x => c * g x) = c * rsInt a b f g := by
  rw [rsInt, stMeasure_smul c hab hg, VectorMeasure.restrict_smul,
    VectorMeasure.integral_smul_vectorMeasure]
  rfl

/-! ## The bound and additivity over intervals -/

/-- Cochrane (2023), A1 §1.6, p. 567: **`|∫_a^b f dg| ≤ sup_{[a,b]}|f| · Var_{[a,b]}(g)`**.
From Mathlib `VectorMeasure.norm_setIntegral_le_of_norm_le_const`. -/
theorem abs_rsInt_le {a b C : ℝ} {f g : ℝ → ℝ} (hab : a ≤ b)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hC : ∀ x ∈ Set.Icc a b, |f x| ≤ C) :
    |rsInt a b f g| ≤ C * (eVariationOn g (Set.Icc a b)).toReal := by
  have := isFiniteMeasure_stMeasure a b g
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC a ⟨le_rfl, hab⟩)
  have h := VectorMeasure.norm_setIntegral_le_of_norm_le_const (μ := stMeasure a b g)
    (s := Set.Icc a b) (B := ContinuousLinearMap.lsmul ℝ ℝ) (f := f) (C := C)
    (fun x hx => by rw [Real.norm_eq_abs]; exact hC x hx)
  rw [Real.norm_eq_abs] at h
  have hL : ‖ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)‖ ≤ 1 := ContinuousLinearMap.opNorm_lsmul_le
  have hv := variation_real_le hab hg (Set.Icc a b)
  have hv0 : 0 ≤ (stMeasure a b g).variation.real (Set.Icc a b) := measureReal_nonneg
  calc |rsInt a b f g|
      ≤ C * ‖ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)‖ *
          (stMeasure a b g).variation.real (Set.Icc a b) := h
    _ ≤ C * 1 * (eVariationOn g (Set.Icc a b)).toReal :=
        mul_le_mul (mul_le_mul_of_nonneg_left hL hC0) hv hv0 (by linarith)
    _ = C * (eVariationOn g (Set.Icc a b)).toReal := by ring

/-- Cochrane (2023), A1 §1.6, p. 567: `g` frozen on `[a, b]` is the sum of `g` frozen on
`[a, c]` and on `[c, b]`, minus `g(c)`. -/
theorem clampFn_split {a b c : ℝ} {g : ℝ → ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    clampFn a b g = fun x => clampFn a c g x + clampFn c b g x - g c := by
  funext x
  rcases le_total x c with hx | hx
  · rw [clampFn_of_le (a := c) (b := b) hx]
    simp only [clampFn, min_eq_right hx, min_eq_right (hx.trans hcb)]
    ring
  · rw [clampFn_of_ge hac hx]
    have h1 : c ≤ min b x := le_min hcb hx
    simp only [clampFn, max_eq_right h1, max_eq_right (hac.trans h1)]
    ring

/-- Cochrane (2023), A1 §1.6, p. 567: the Stieltjes measure on `[a, b]` is the sum of those on
`[a, c]` and `[c, b]`. -/
theorem stMeasure_split {a b c : ℝ} {g : ℝ → ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hg : BoundedVariationOn g (Set.Icc a b)) :
    stMeasure a b g = stMeasure a c g + stMeasure c b g := by
  have h := bv_clampFn (hac.trans hcb) hg
  have h₁ := bv_clampFn hac (hg.mono (Set.Icc_subset_Icc le_rfl hcb))
  have h₂ := bv_clampFn hcb (hg.mono (Set.Icc_subset_Icc hac le_rfl))
  rw [stMeasure_eq h, stMeasure_eq h₁, stMeasure_eq h₂]
  refine VectorMeasure.ext_of_Icc _ _ fun s t hst => ?_
  rw [add_apply, h.vectorMeasure_Icc hst, h₁.vectorMeasure_Icc hst,
    h₂.vectorMeasure_Icc hst, clampFn_split hac hcb, rightLim_add_sub h₁ h₂,
    leftLim_add_sub h₁ h₂]
  ring

/-- Cochrane (2023), A1 §1.6, p. 567: **additivity over intervals**,
`∫_a^b f dg = ∫_a^c f dg + ∫_c^b f dg` for `a ≤ c ≤ b` (the jump `g(c+) − g(c−)` of an interior
point `c` splits as `g(c) − g(c−)` in `[a, c]` plus `g(c+) − g(c)` in `[c, b]`). -/
theorem rsInt_add_interval {a b c : ℝ} {f g : ℝ → ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hf : RSIntegrable a b f) :
    rsInt a b f g = rsInt a c f g + rsInt c b f g := by
  have h₁ := bv_clampFn hac (hg.mono (Set.Icc_subset_Icc le_rfl hcb))
  have h₂ := bv_clampFn hcb (hg.mono (Set.Icc_subset_Icc hac le_rfl))
  rw [rsInt, stMeasure_split hac hcb hg, VectorMeasure.restrict_add,
    VectorMeasure.integral_add_vectorMeasure (hf _ (isFiniteMeasure_stMeasure a c g))
      (hf _ (isFiniteMeasure_stMeasure c b g))]
  congr 1
  · rw [rsInt]
    refine VectorMeasure.setIntegral_congr_set measurableSet_Icc measurableSet_Icc ?_
    have h0 : (stMeasure a c g).variation (Set.Ioi c) = 0 := by
      rw [stMeasure_eq h₁]
      refine le_antisymm ((h₁.variation_vectorMeasure_Ioi_le).trans
        (le_of_eq (eVariationOn.constant_on ?_))) bot_le
      exact Set.subsingleton_of_forall_eq (g c) fun _ ⟨_, hx, hxy⟩ =>
        hxy ▸ clampFn_of_ge hac (le_of_lt hx)
    rw [ae_eq_set]
    constructor
    · exact measure_mono_null (fun x hx => lt_of_not_ge fun h => hx.2 ⟨hx.1.1, h⟩) h0
    · exact measure_mono_null (fun x hx => absurd ⟨hx.1.1, hx.1.2.trans hcb⟩ hx.2) h0
  · rw [rsInt]
    refine VectorMeasure.setIntegral_congr_set measurableSet_Icc measurableSet_Icc ?_
    have h0 : (stMeasure c b g).variation (Set.Iio c) = 0 := by
      rw [stMeasure_eq h₂]
      refine le_antisymm ((h₂.variation_vectorMeasure_Iio_le).trans
        (le_of_eq (eVariationOn.constant_on ?_))) bot_le
      exact Set.subsingleton_of_forall_eq (g c) fun _ ⟨_, hx, hxy⟩ =>
        hxy ▸ clampFn_of_le (le_of_lt hx)
    rw [ae_eq_set]
    constructor
    · exact measure_mono_null (fun x hx => lt_of_not_ge fun h => hx.2 ⟨h, hx.1.2⟩) h0
    · exact measure_mono_null (fun x hx => absurd ⟨hac.trans hx.1.1, hx.1.2⟩ hx.2) h0

end Cochrane.Monetarism.TidyR7StieltjesIntegral
