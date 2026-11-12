/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR7StieltjesCalculus

/-!
# Riemann–Stieltjes sums against a JUMPING integrator, and the jump covariation

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). The product step of (1.32),
`Λ/P · dB + E_t d(Λ/P)·B = E_t d(ΛB/P)`, was proved in `TidyR7ProductStep` for bonds `B` with
CONTINUOUS paths. Continuity entered only through the pathwise limits of `TidyR7StieltjesSums`:
the left-point sums `Σ f(t_i)Δg_i → ∫ f dg` and the cross sum `Σ Δf_iΔg_i → 0`, both for `g`
continuous. This module removes that hypothesis: `g` is càdlàg (right-continuous with left
limits) of bounded variation on `[a, b]`, `f` is càdlàg.

## Main results (along ANY sequence of partitions with mesh → 0)

* `tendsto_rsSum_leftLim` (extension (a)): `Σ f(t_i)Δg_i → ∫_a^b f(·−) dg`
  (`rsInt a b (Function.leftLim f) g`): the left-point sum sees the value of `f` BEFORE a common
  jump. `tendsto_rsSumRight`: the right-point sums `Σ f(t_{i+1})Δg_i → ∫_a^b f dg`.
* `jumpSum a b f g = Σ_{a<u≤b} Δf_u Δg_u` (`Δf_u = f(u) − f(u−)`, `jump`): a sum over `ℝ` of a
  family supported on the countable set of jumps of `f` in `(a, b]` (`countable_support_jumpSum`),
  ABSOLUTELY convergent (`summable_abs_jumpSum`). `hasSum_jumpSum`, `jumpSum_eq`: it equals
  `∫_a^b f dg − ∫_a^b f(·−) dg`.
* `tendsto_crossSum_jumpSum` (extension (b)): `Σ Δf_iΔg_i → Σ_{a<u≤b} Δf_uΔg_u`.
* `jumpSum_eq_zero_of_continuousOn`: for `g` continuous on `[a, b]` the jump sum is `0`, so (b)
  recovers `TidyR7StieltjesSums.tendsto_crossSum_zero`; `rsInt_leftLim_of_continuousOn` and
  `rsInt_congr_Ioc` recover `TidyR7StieltjesSums.tendsto_rsSum_of_isCadlag`.
* Tools: `rsInt_eq_Ioc` (a càdlàg integrator does not charge the left endpoint),
  `measurable_leftLim`, `rsIntegrable_leftLim`, `rsInt_const_right`, `rsInt_single_jump`
  (the integral against a one-jump step function is `f(c)·(jump at c)`), `jumpSum_add_right`,
  `jumpSum_smul_right`, `jumpSum_heaviside` (consistency with
  `TidyR7StieltjesSums.crossSum_heaviside`).
-/

namespace Cochrane.Monetarism.TidyR7JumpSums

open MeasureTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesIntegral Cochrane.Monetarism.TidyR7StieltjesSums

variable {a b : ℝ}

/-! ## Càdlàg integrators -/

/-- Cochrane (2023), A1 §1.6, p. 567 (tool for (1.32)): a càdlàg function equals its right
limit.
A special case of Mathlib `ContinuousWithinAt.rightLim_eq`. -/
theorem rightLim_eq_of_isCadlag {g : ℝ → ℝ} (hg : IsCadlag g) (x : ℝ) :
    Function.rightLim g x = g x :=
  (continuousWithinAt_Ioi_iff_Ici.1 (hg.isRightContinuous x)).rightLim_eq

/-- Cochrane (2023), A1 §1.6, p. 567: for `g` càdlàg the frozen function has right limit `g(x)`
at every `x ∈ [a, b]`. -/
theorem rightLim_clampFn_eq {g : ℝ → ℝ} (hab : a ≤ b) (hg : BoundedVariationOn g (Set.Icc a b))
    (hgc : IsCadlag g) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    Function.rightLim (clampFn a b g) x = g x := by
  rcases hx.2.lt_or_eq with h | rfl
  · rw [rightLim_clampFn hab hg ⟨hx.1, h⟩, rightLim_eq_of_isCadlag hgc]
  · exact rightLim_clampFn_right hab g

/-- Cochrane (2023), A1 §1.6, p. 567: **a càdlàg integrator does not charge the left
endpoint**: the variation of `stMeasure a b g` at `{a}` is `|g(a+) − g(a)| = 0`.
The càdlàg case of `TidyR7StieltjesIntegral.stMeasure_singleton_left`. -/
theorem variation_stMeasure_left {g : ℝ → ℝ} (hab : a ≤ b)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hgc : IsCadlag g) :
    (stMeasure a b g).variation {a} = 0 := by
  rw [stMeasure_eq (bv_clampFn hab hg), (bv_clampFn hab hg).variation_vectorMeasure_singleton,
    leftLim_clampFn_left, rightLim_clampFn_eq hab hg hgc ⟨le_rfl, hab⟩]
  simp

/-- Cochrane (2023), A1 §1.6, p. 567: for a càdlàg integrator, `∫_a^b f dg = ∫_{(a,b]} f dg`.
From `TidyR7StieltjesSums.setIntegral_Icc_eq`. -/
theorem rsInt_eq_Ioc {f g : ℝ → ℝ} (hab : a ≤ b) (hg : BoundedVariationOn g (Set.Icc a b))
    (hgc : IsCadlag g) :
    rsInt a b f g = ∫ᵛ x in Set.Ioc a b, f x ∂• stMeasure a b g := by
  rw [rsInt, VectorMeasure.setIntegral_congr_set measurableSet_Icc measurableSet_Ioc ?_]
  rw [ae_eq_set]
  constructor
  · refine measure_mono_null (fun x hx => ?_) (variation_stMeasure_left hab hg hgc)
    exact le_antisymm (not_lt.1 fun h => hx.2 ⟨h, hx.1.2⟩) hx.1.1
  · exact measure_mono_null (fun x hx => absurd (Set.Ioc_subset_Icc_self hx.1) hx.2)
      (measure_empty (μ := (stMeasure a b g).variation))

/-- Cochrane (2023), A1 §1.6, p. 567: for a càdlàg integrator, the integral depends on `f`
only through its values on `(a, b]`. -/
theorem rsInt_congr_Ioc {f₁ f₂ g : ℝ → ℝ} (hab : a ≤ b) (hg : BoundedVariationOn g (Set.Icc a b))
    (hgc : IsCadlag g) (h : Set.EqOn f₁ f₂ (Set.Ioc a b)) : rsInt a b f₁ g = rsInt a b f₂ g := by
  rw [rsInt_eq_Ioc hab hg hgc, rsInt_eq_Ioc hab hg hgc]
  exact VectorMeasure.setIntegral_congr_fun h

/-- Cochrane (2023), A1 §1.6, p. 567: **left limits of a function continuous on `[a, b]`**:
`f(x−) = f(x)` for `x ∈ (a, b]`.
A special case of Mathlib `ContinuousWithinAt.leftLim_eq`. -/
theorem leftLim_eq_of_continuousOn {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b)) {x : ℝ}
    (hx : x ∈ Set.Ioc a b) : Function.leftLim f x = f x := by
  refine leftLim_eq_of_tendsto ((hf x (Set.Ioc_subset_Icc_self hx)).tendsto.mono_left ?_)
  exact nhdsWithin_le_of_mem (Filter.mem_of_superset (Ioo_mem_nhdsLT hx.1)
    fun y hy => ⟨hy.1.le, hy.2.le.trans hx.2⟩)

/-- Cochrane (2023), A1 §1.6, p. 567: for `f` continuous on `[a, b]` and a càdlàg integrator,
`∫_a^b f(·−) dg = ∫_a^b f dg`. -/
theorem rsInt_leftLim_of_continuousOn {f g : ℝ → ℝ} (hab : a ≤ b)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hgc : IsCadlag g)
    (hf : ContinuousOn f (Set.Icc a b)) : rsInt a b (Function.leftLim f) g = rsInt a b f g :=
  rsInt_congr_Ioc hab hg hgc fun _ hx => leftLim_eq_of_continuousOn hf hx

/-! ## Left limits of a càdlàg integrand -/

/-- Cochrane (2023), A1 §1.6, p. 567: the left limits of a càdlàg function form a measurable
function (`f(x−) = lim f(x − 1/(n+1))`). -/
theorem measurable_leftLim {f : ℝ → ℝ} (hf : IsCadlag f) : Measurable (Function.leftLim f) := by
  refine measurable_of_tendsto_metrizable (f := fun (n : ℕ) x => f (x - 1 / ((n : ℝ) + 1)))
    (fun n => (measurable_of_isCadlag hf).comp (measurable_id.sub_const _)) ?_
  refine tendsto_pi_nhds.2 fun x => (hf.tendsto_nhdsLT_leftLim x).comp ?_
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
  · simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    change x - 1 / ((n : ℝ) + 1) < x
    linarith

/-- Cochrane (2023), A1 §1.6, p. 567: if `|f| ≤ C` on `(c, x)`, `c < x`, then `|f(x−)| ≤ C`. -/
theorem abs_leftLim_le {f : ℝ → ℝ} (hf : IsCadlag f) {c x C : ℝ} (hcx : c < x)
    (hC : ∀ y ∈ Set.Ioo c x, |f y| ≤ C) : |Function.leftLim f x| ≤ C := by
  refine le_of_tendsto (hf.tendsto_nhdsLT_leftLim x).abs ?_
  filter_upwards [Ioo_mem_nhdsLT hcx] with y hy
  exact hC y hy

/-- Cochrane (2023), A1 §1.6, p. 567: the left limits of a càdlàg function are integrable
against every finite-variation measure on `[a, b]`. -/
theorem rsIntegrable_leftLim {f : ℝ → ℝ} (hf : IsCadlag f) :
    RSIntegrable a b (Function.leftLim f) := by
  obtain ⟨C, -, hC⟩ := exists_bound_of_isCadlag hf (a - 1) b
  refine rsIntegrable_of_measurable (measurable_leftLim hf) (C := C) fun x hx => ?_
  exact abs_leftLim_le hf (by linarith : x - 1 < x) fun y hy =>
    hC y ⟨by linarith [hy.1, hx.1], hy.2.le.trans hx.2⟩

/-! ## Extension (a): left-point sums against a càdlàg integrator -/

/-- Cochrane (2023), A1 §1.6, p. 567: for a càdlàg integrator `g` of bounded variation the
left-point sum with coefficients `c_i` is the integral of the step function over `(a, b]`.
Generalises `TidyR7StieltjesSums.rsSum_eq_integral_stepFn` (continuous `g`). -/
theorem rsSum_eq_integral_stepFn_of_isCadlag {g : ℝ → ℝ}
    (hg : BoundedVariationOn g (Set.Icc a b)) (hgc : IsCadlag g) (P : Partition a b)
    (c : ℕ → ℝ) :
    ∑ i ∈ Finset.range P.n, c i * (g (P.t (i + 1)) - g (P.t i)) =
      ∫ᵛ x in Set.Ioc a b, stepFn P c x ∂• stMeasure a b g := by
  have hab := a_le_b P
  have hG := bv_clampFn hab hg
  have hfin := isFiniteMeasure_stMeasure a b g
  rw [stMeasure_eq hG] at hfin ⊢
  rw [integral_stepFn hG hfin P c]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [rightLim_clampFn_eq hab hg hgc (t_mem P (Finset.mem_range.1 hi)),
    rightLim_clampFn_eq hab hg hgc (t_mem P (Finset.mem_range.1 hi).le)]

/-- **Cochrane (2023), A1 §1.6, p. 567, extension (a): left-point sums against a jumping
integrator.** For `f` càdlàg and `g` càdlàg of bounded variation on `[a, b]`, along ANY sequence
of partitions with mesh → 0, `Σ f(t_i)(g(t_{i+1}) − g(t_i)) → ∫_a^b f(·−) dg`.
Generalises `TidyR7StieltjesSums.tendsto_rsSum_of_isCadlag` (continuous `g`). -/
theorem tendsto_rsSum_leftLim {f g : ℝ → ℝ} (hf : IsCadlag f)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hgc : IsCadlag g)
    (P : ℕ → Partition a b) (hP : Tendsto (fun k => mesh (P k)) atTop (𝓝 0)) :
    Tendsto (fun k => rsSum (P k) f g) atTop (𝓝 (rsInt a b (Function.leftLim f) g)) := by
  have hab := a_le_b (P 0)
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_isCadlag hf a b
  have e : ∀ k, ∫ᵛ x in Set.Ioc a b, stepFn (P k) (fun i => f ((P k).t i)) x ∂• stMeasure a b g =
      rsSum (P k) f g := fun k =>
    (rsSum_eq_integral_stepFn_of_isCadlag hg hgc (P k) fun i => f ((P k).t i)).symm
  rw [rsInt_eq_Ioc hab hg hgc]
  refine (tendsto_congr e).1 (tendsto_integral_stepFn (isFiniteMeasure_stMeasure a b g) P
    (fun k i => f ((P k).t i)) hC0 (fun k i hi => hC _ (t_mem (P k) hi.le)) fun x hx => ?_)
  exact tendsto_stepFn_left P hP hx (hf.tendsto_nhdsLT_leftLim x)

/-- Cochrane (2023), A1 §1.6, p. 567: **the right-point sum**
`Σ_{i<n} f(t_{i+1})(g(t_{i+1}) − g(t_i))`. -/
def rsSumRight (P : Partition a b) (f g : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range P.n, f (P.t (i + 1)) * (g (P.t (i + 1)) - g (P.t i))

/-- Cochrane (2023), A1 §1.6, p. 567: the cross sum is the right-point sum minus the left-point
sum. -/
theorem crossSum_eq_sub (P : Partition a b) (f g : ℝ → ℝ) :
    crossSum P f g = rsSumRight P f g - rsSum P f g := by
  rw [crossSum, rsSumRight, rsSum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **Cochrane (2023), A1 §1.6, p. 567: right-point sums.** For `f` càdlàg and `g` càdlàg of
bounded variation on `[a, b]`, along ANY sequence of partitions with mesh → 0,
`Σ f(t_{i+1})(g(t_{i+1}) − g(t_i)) → ∫_a^b f dg` (the Lebesgue–Stieltjes integral of `f`
itself, charging `f(u)Δg_u` at a jump `u` of `g`). -/
theorem tendsto_rsSumRight {f g : ℝ → ℝ} (hf : IsCadlag f)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hgc : IsCadlag g)
    (P : ℕ → Partition a b) (hP : Tendsto (fun k => mesh (P k)) atTop (𝓝 0)) :
    Tendsto (fun k => rsSumRight (P k) f g) atTop (𝓝 (rsInt a b f g)) := by
  have hab := a_le_b (P 0)
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_isCadlag hf a b
  have e : ∀ k,
      ∫ᵛ x in Set.Ioc a b, stepFn (P k) (fun i => f ((P k).t (i + 1))) x ∂• stMeasure a b g =
        rsSumRight (P k) f g := fun k =>
    (rsSum_eq_integral_stepFn_of_isCadlag hg hgc (P k) fun i => f ((P k).t (i + 1))).symm
  rw [rsInt_eq_Ioc hab hg hgc]
  refine (tendsto_congr e).1 (tendsto_integral_stepFn (isFiniteMeasure_stMeasure a b g) P
    (fun k i => f ((P k).t (i + 1))) hC0 (fun k i hi => hC _ (t_mem (P k) hi)) fun x hx => ?_)
  exact tendsto_stepFn_right P hP hx
    (continuousWithinAt_Ioi_iff_Ici.1 (hf.isRightContinuous x)).tendsto

/-! ## The jump covariation `Σ_{a<u≤b} Δf_u Δg_u` -/

/-- Cochrane (2023), A1 §1.6, p. 567: the jump `Δf_u = f(u) − f(u−)` of `f` at `u`. -/
noncomputable def jump (f : ℝ → ℝ) (u : ℝ) : ℝ := f u - Function.leftLim f u

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: **the jump covariation**
`Σ_{a<u≤b} Δf_u Δg_u`, as a sum over `ℝ` of the family `1_{(a,b]}(u)·Δf_uΔg_u` (supported on the
countable set of jumps of `f` in `(a, b]` when `f` is càdlàg: `countable_support_jumpSum`). -/
noncomputable def jumpSum (a b : ℝ) (f g : ℝ → ℝ) : ℝ :=
  ∑' u : ℝ, (Set.Ioc a b).indicator (fun u => jump f u * jump g u) u

/-- Cochrane (2023), A1 §1.6, p. 567: the summands of `jumpSum` vanish outside the countable set
of jumps of `f` in `(a, b]`. -/
theorem countable_support_jumpSum {f : ℝ → ℝ} (hf : IsCadlag f) (g : ℝ → ℝ) :
    (Function.support fun u => (Set.Ioc a b).indicator (fun u => jump f u * jump g u) u).Countable
    := by
  refine (countable_jumps hf).mono fun u hu => ?_
  intro h
  apply hu
  have : jump f u = 0 := by rw [jump, ← h, sub_self]
  simp [this]

/-- Cochrane (2023), A1 §1.6, p. 567: an atom of `stMeasure a b g` at `u ∈ (a, b]` is the jump
`Δg_u` when `g` is càdlàg.
Extends `TidyR7StieltjesIntegral.stMeasure_singleton_interior` to `u ∈ (a, b]`. -/
theorem stMeasure_singleton_jump {g : ℝ → ℝ} (hg : BoundedVariationOn g (Set.Icc a b))
    (hgc : IsCadlag g) {u : ℝ} (hu : u ∈ Set.Ioc a b) : stMeasure a b g {u} = jump g u := by
  rcases hu.2.lt_or_eq with h | rfl
  · rw [stMeasure_singleton_interior hg hu.1 h, rightLim_eq_of_isCadlag hgc, jump]
  · rw [stMeasure_singleton_right hu.1 hg, jump]

/-- **Cochrane (2023), A1 §1.6, p. 567: the jump covariation as an integral.** For `f` càdlàg and
`g` càdlàg of bounded variation on `[a, b]`, the family `1_{(a,b]}Δf Δg` is summable with sum
`∫_a^b f dg − ∫_a^b f(·−) dg`. -/
theorem hasSum_jumpSum {f g : ℝ → ℝ} (hab : a ≤ b) (hf : IsCadlag f)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hgc : IsCadlag g) :
    HasSum (fun u => (Set.Ioc a b).indicator (fun u => jump f u * jump g u) u)
      (rsInt a b f g - rsInt a b (Function.leftLim f) g) := by
  set ν := stMeasure a b g with hν
  have hfin := isFiniteMeasure_stMeasure a b g
  set S : Set ℝ := {x | f x ≠ Function.leftLim f x} ∩ Set.Ioc a b with hS
  have hSc : S.Countable := (countable_jumps hf).mono Set.inter_subset_left
  have hSm : MeasurableSet S := hSc.measurableSet
  have hSI : S ⊆ Set.Ioc a b := Set.inter_subset_right
  have i1 : ν.IntegrableOn f (Set.Ioc a b) :=
    (rsIntegrable_of_isCadlag hf (a := a) (b := b) ν hfin).mono measurableSet_Icc
      Set.Ioc_subset_Icc_self
  have i2 : ν.IntegrableOn (Function.leftLim f) (Set.Ioc a b) :=
    (rsIntegrable_leftLim hf (a := a) (b := b) ν hfin).mono measurableSet_Icc
      Set.Ioc_subset_Icc_self
  have e1 : rsInt a b f g - rsInt a b (Function.leftLim f) g =
      ∫ᵛ x in Set.Ioc a b, jump f x ∂• ν := by
    rw [rsInt_eq_Ioc hab hg hgc, rsInt_eq_Ioc hab hg hgc]
    exact (VectorMeasure.integral_fun_sub i1 i2).symm
  have e2 : ∫ᵛ x in Set.Ioc a b, jump f x ∂• ν = ∫ᵛ x in S, jump f x ∂• ν :=
    VectorMeasure.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hSm measurableSet_Ioc hSI
      fun x hx => by
        have : ¬ (f x ≠ Function.leftLim f x) := fun h => hx.2 ⟨h, hx.1⟩
        rw [jump, not_not.1 this, sub_self]
  have hU : (⋃ i : S, ({(i : ℝ)} : Set ℝ)) = S := Set.iUnion_of_singleton_coe S
  have iS : ν.IntegrableOn (jump f) (⋃ i : S, ({(i : ℝ)} : Set ℝ)) := by
    rw [hU]
    exact VectorMeasure.IntegrableOn.mono measurableSet_Ioc hSI
      (show ν.IntegrableOn (jump f) (Set.Ioc a b) from i1.sub i2)
  have := hSc.to_subtype
  have h3 := VectorMeasure.hasSum_setIntegral_iUnion (B := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := ν) (f := jump f) (s := fun i : S => ({(i : ℝ)} : Set ℝ))
    (fun _ => measurableSet_singleton _)
    (fun i j hij => Set.disjoint_singleton.2 fun h => hij (Subtype.ext h)) iS
  rw [hU, ← e2, ← e1] at h3
  have hsupp : Function.support
      (fun u => (Set.Ioc a b).indicator (fun u => jump f u * jump g u) u) ⊆ S := by
    intro u hu
    by_cases hI : u ∈ Set.Ioc a b
    · refine ⟨fun h => hu ?_, hI⟩
      have : jump f u = 0 := by rw [jump, ← h, sub_self]
      simp [this]
    · exact absurd (Set.indicator_of_notMem hI _) hu
  refine (hasSum_subtype_iff_of_support_subset hsupp).1 ?_
  refine h3.congr_fun fun i => ?_
  have hi : (i : ℝ) ∈ Set.Ioc a b := hSI i.2
  simp only [Function.comp_apply, Set.indicator_of_mem hi]
  rw [VectorMeasure.integral_singleton, stMeasure_singleton_jump hg hgc hi]
  simp

/-- **Cochrane (2023), A1 §1.6, p. 567: `Σ_{a<u≤b} Δf_uΔg_u = ∫_a^b f dg − ∫_a^b f(·−) dg`** for
`f` càdlàg and `g` càdlàg of bounded variation on `[a, b]`. -/
theorem jumpSum_eq {f g : ℝ → ℝ} (hab : a ≤ b) (hf : IsCadlag f)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hgc : IsCadlag g) :
    jumpSum a b f g = rsInt a b f g - rsInt a b (Function.leftLim f) g :=
  (hasSum_jumpSum hab hf hg hgc).tsum_eq

/-- **Cochrane (2023), A1 §1.6, p. 567: the jump covariation converges absolutely**:
`Σ_{a<u≤b} |Δf_uΔg_u| < ∞` (Mathlib `summable_abs_iff`; `ℝ` is finite-dimensional). -/
theorem summable_abs_jumpSum {f g : ℝ → ℝ} (hab : a ≤ b) (hf : IsCadlag f)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hgc : IsCadlag g) :
    Summable fun u => |(Set.Ioc a b).indicator (fun u => jump f u * jump g u) u| :=
  summable_abs_iff.2 (hasSum_jumpSum hab hf hg hgc).summable

/-- **Cochrane (2023), A1 §1.6, p. 567, extension (b): the cross sum converges to the jump
covariation.** For `f` càdlàg (not necessarily of bounded variation) and `g` càdlàg of bounded
variation on `[a, b]`, along ANY sequence of partitions with mesh → 0,
`Σ (f(t_{i+1}) − f(t_i))(g(t_{i+1}) − g(t_i)) → Σ_{a<u≤b} Δf_uΔg_u`.
Generalises `TidyR7StieltjesSums.tendsto_crossSum_zero` (continuous `g`, limit `0`). -/
theorem tendsto_crossSum_jumpSum {f g : ℝ → ℝ} (hf : IsCadlag f)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hgc : IsCadlag g)
    (P : ℕ → Partition a b) (hP : Tendsto (fun k => mesh (P k)) atTop (𝓝 0)) :
    Tendsto (fun k => crossSum (P k) f g) atTop (𝓝 (jumpSum a b f g)) := by
  rw [jumpSum_eq (a_le_b (P 0)) hf hg hgc]
  refine ((tendsto_rsSumRight hf hg hgc P hP).sub (tendsto_rsSum_leftLim hf hg hgc P hP)).congr
    fun k => ?_
  rw [crossSum_eq_sub]

/-- Cochrane (2023), A1 §1.6, p. 567: **the jump covariation vanishes when `g` is continuous on
`[a, b]`** (no common jumps), consistent with `TidyR7StieltjesSums.tendsto_crossSum_zero`. -/
theorem jumpSum_eq_zero_of_continuousOn {f g : ℝ → ℝ} (hab : a ≤ b) (hf : IsCadlag f)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hgc : IsCadlag g)
    (hgo : ContinuousOn g (Set.Icc a b)) : jumpSum a b f g = 0 := by
  rw [jumpSum_eq hab hf hg hgc, ← rsInt_eq_rsInt_leftLim hab hf hg hgo, sub_self]

/-- Cochrane (2023), A1 §1.6, p. 567: **the jump covariation vanishes when `f` is continuous on
`[a, b]`**. -/
theorem jumpSum_eq_zero_of_continuousOn_left {f g : ℝ → ℝ} (hab : a ≤ b) (hf : IsCadlag f)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hgc : IsCadlag g)
    (hfo : ContinuousOn f (Set.Icc a b)) : jumpSum a b f g = 0 := by
  rw [jumpSum_eq hab hf hg hgc, rsInt_leftLim_of_continuousOn hab hg hgc hfo, sub_self]

/-- Cochrane (2023), A1 §1.6, p. 567: **`∫ f dg = ∫ f(·−) dg + Σ Δf Δg`** (the Lebesgue–Stieltjes
integral of `f` itself charges `f(u)Δg_u = f(u−)Δg_u + Δf_uΔg_u` at a jump `u` of `g`). -/
theorem rsInt_eq_leftLim_add_jumpSum {f g : ℝ → ℝ} (hab : a ≤ b) (hf : IsCadlag f)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hgc : IsCadlag g) :
    rsInt a b f g = rsInt a b (Function.leftLim f) g + jumpSum a b f g := by
  rw [jumpSum_eq hab hf hg hgc]
  ring

/-- Cochrane (2023), A1 §1.6, p. 567: the jump covariation is additive in the integrator. -/
theorem jumpSum_add_right {f g₁ g₂ : ℝ → ℝ} (hab : a ≤ b) (hf : IsCadlag f)
    (hg₁ : BoundedVariationOn g₁ (Set.Icc a b)) (hg₁c : IsCadlag g₁)
    (hg₂ : BoundedVariationOn g₂ (Set.Icc a b)) (hg₂c : IsCadlag g₂) :
    jumpSum a b f (fun x => g₁ x + g₂ x) = jumpSum a b f g₁ + jumpSum a b f g₂ := by
  have hb : BoundedVariationOn (fun x => g₁ x + g₂ x) (Set.Icc a b) :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hg₁, hg₂⟩) (eVariationOn_add_le _ _ _)
  rw [jumpSum_eq hab hf hb (hg₁c.fun_add hg₂c), jumpSum_eq hab hf hg₁ hg₁c,
    jumpSum_eq hab hf hg₂ hg₂c, rsInt_add_right hab hg₁ hg₂ (rsIntegrable_of_isCadlag hf),
    rsInt_add_right hab hg₁ hg₂ (rsIntegrable_leftLim hf)]
  ring

/-- Cochrane (2023), A1 §1.6, p. 567: the jump covariation is homogeneous in the integrator. -/
theorem jumpSum_smul_right {f g : ℝ → ℝ} (c : ℝ) (hab : a ≤ b) (hf : IsCadlag f)
    (hg : BoundedVariationOn g (Set.Icc a b)) (hgc : IsCadlag g) :
    jumpSum a b f (fun x => c * g x) = c * jumpSum a b f g := by
  have hk : BoundedVariationOn (fun _ : ℝ => c) (Set.Icc a b) := by
    rw [BoundedVariationOn, eVariationOn.constant_on
      (Set.subsingleton_of_forall_eq c fun _ ⟨_, _, hy⟩ => hy.symm)]
    exact ENNReal.zero_ne_top
  have hb : BoundedVariationOn (fun x => c * g x) (Set.Icc a b) := hk.fun_mul hg
  have hcc : IsCadlag fun x => c * g x := hgc.const_smul c
  rw [jumpSum_eq hab hf hb hcc, jumpSum_eq hab hf hg hgc, rsInt_smul_right c hab hg,
    rsInt_smul_right c hab hg]
  ring

/-! ## Computing integrals against step functions -/

/-- Cochrane (2023), A1 §1.6, p. 567: **the integral against a constant integrator is `0`**. -/
theorem rsInt_const_right (hab : a ≤ b) (f : ℝ → ℝ) (k : ℝ) : rsInt a b f (fun _ => k) = 0 := by
  have hv : eVariationOn (fun _ : ℝ => k) (Set.Icc a b) = 0 :=
    eVariationOn.constant_on (Set.subsingleton_of_forall_eq k fun _ ⟨_, _, hy⟩ => hy.symm)
  have hbv : BoundedVariationOn (fun _ : ℝ => k) (Set.Icc a b) := by
    rw [BoundedVariationOn, hv]
    exact ENNReal.zero_ne_top
  have h := bv_clampFn hab hbv
  have h0 : (stMeasure a b fun _ => k).variation (Set.Icc a b) = 0 := by
    rw [stMeasure_eq h]
    exact le_antisymm ((measure_mono (Set.subset_univ _)).trans
      (h.variation_vectorMeasure_univ_le.trans ((eVariationOn_clampFn_le hab _).trans hv.le)))
      bot_le
  exact VectorMeasure.setIntegral_of_variation_apply_eq_zero _ h0

/-- **Cochrane (2023), A1 §1.6, p. 567: the integral against a one-jump step function.** If
`g = k₀` on `(−∞, c)` and `g = k₁` on `[c, ∞)` with `a < c ≤ b`, then for EVERY `f`,
`∫_a^b f dg = f(c)(k₁ − k₀)`. -/
theorem rsInt_single_jump {f g : ℝ → ℝ} {c k₀ k₁ : ℝ} (hac : a < c) (hcb : c ≤ b)
    (hg : BoundedVariationOn g (Set.Icc a b))
    (h0 : ∀ x, x < c → g x = k₀) (h1 : ∀ x, c ≤ x → g x = k₁) :
    rsInt a b f g = f c * (k₁ - k₀) := by
  have hab : a ≤ b := hac.le.trans hcb
  have hG0 : ∀ y, y < c → clampFn a b g y = k₀ := fun y hy =>
    h0 _ (max_lt hac ((min_le_right b y).trans_lt hy))
  have hG1 : ∀ y, c ≤ y → clampFn a b g y = k₁ := fun y hy =>
    h1 _ ((le_min hcb hy).trans (le_max_right _ _))
  have hG := bv_clampFn hab hg
  have hL : ∀ y, y ≤ c → Function.leftLim (clampFn a b g) y = k₀ := by
    intro y hy
    refine leftLim_eq_of_tendsto (tendsto_const_nhds.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hG0 z (lt_of_lt_of_le hz hy)).symm
  have hR : ∀ y, c ≤ y → Function.rightLim (clampFn a b g) y = k₁ := by
    intro y hy
    refine rightLim_eq_of_tendsto (tendsto_const_nhds.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hG1 z (hy.trans (le_of_lt hz))).symm
  have vL : hG.vectorMeasure.variation (Set.Iio c) = 0 := by
    rw [hG.variation_vectorMeasure_Iio]
    exact eVariationOn.constant_on (Set.subsingleton_of_forall_eq k₀ fun _ ⟨y, hy, e⟩ =>
      e ▸ hL y (le_of_lt hy))
  have vR : hG.vectorMeasure.variation (Set.Ioi c) = 0 := by
    rw [hG.variation_vectorMeasure_Ioi]
    exact eVariationOn.constant_on (Set.subsingleton_of_forall_eq k₁ fun _ ⟨y, hy, e⟩ =>
      e ▸ hR y (le_of_lt hy))
  rw [rsInt, stMeasure_eq hG, VectorMeasure.setIntegral_congr_set measurableSet_Icc
    (measurableSet_singleton c) ?_, VectorMeasure.integral_singleton,
    hG.vectorMeasure_singleton, hL c le_rfl, hR c le_rfl]
  · simp
  rw [ae_eq_set]
  constructor
  · refine measure_mono_null (fun x hx => ?_) (measure_union_null vL vR)
    rcases lt_or_gt_of_ne (hx.2 : x ≠ c) with h | h
    · exact Or.inl h
    · exact Or.inr h
  · exact measure_mono_null (fun x hx => absurd ⟨hac.le.trans (le_of_eq (hx.1 : x = c).symm),
      (le_of_eq (hx.1 : x = c)).trans hcb⟩ hx.2) (measure_empty (μ := hG.vectorMeasure.variation))

/-- Cochrane (2023), A1 §1.6, p. 567: **consistency with
`TidyR7StieltjesSums.crossSum_heaviside`**: for `f = g = 1_{[1,∞)}` on `[0, 2]` the cross sum is `1`
at every partition, and the jump covariation `Σ_{0<u≤2} Δf_uΔg_u = 1·1` is its limit. -/
theorem jumpSum_heaviside : jumpSum 0 2 heaviside heaviside = 1 := by
  have h := tendsto_crossSum_jumpSum isCadlag_heaviside bv_heaviside isCadlag_heaviside _
    (tendsto_mesh_dyadic (by norm_num : (0 : ℝ) < 2))
  simp only [crossSum_heaviside] at h
  exact (tendsto_nhds_unique tendsto_const_nhds h).symm

end Cochrane.Monetarism.TidyR7JumpSums
