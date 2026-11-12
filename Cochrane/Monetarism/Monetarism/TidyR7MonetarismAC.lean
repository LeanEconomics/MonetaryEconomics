/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR7StieltjesVariation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Stieltjes integrals against absolutely continuous integrators

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). In (1.31)–(1.32) two integrators are absolutely
continuous rather than `C¹`: the finite-variation part `A` of `Λ/P`, with
`A_t − A_s = −∫_s^t i_u (Λ_u/P_u) du` (the bond-pricing condition `E_t d(Λ/P)/(Λ/P) = −i dt`), and
the nominal debt-plus-money `B + M`, with `d(B + M) = (iB + i^mM − Ps) dt` by the flow (1.31).
Their densities are only measurable (`i` and `s` measurable, `Λ/P` càdlàg), so
`TidyR7ProductStepCases.rsInt_eq_integral_mul_deriv` (continuous derivative) does not apply.

## Main results

* `eVariationOn_le_integral`, `bv_of_primitive`: a primitive `g = g(a) + ∫_a^· h` of an interval
  integrable `h` has variation at most `∫_a^b |h|` on `[a, b]`.
* `continuousOn_of_primitive`: it is continuous on `[a, b]`.
* `rsInt_eq_integral_of_primitive`: for `f` càdlàg, `∫_a^b f dg = ∫_a^b f(x)h(x) dx` (Lebesgue).
  Proof: each left-point sum is `∫_a^b φ_k h` for the step function `φ_k` of the partition; along
  the dyadic partitions `φ_k → f(x−) = f(x)` off the countable jump set of `f`, a Lebesgue-null set,
  with `|φ_k h| ≤ C|h|`; and the sums also converge to `∫ f dg`
  (`TidyR7StieltjesSums.tendsto_rsSum_of_isCadlag`).
* `continuous_of_incr`, `bv_of_incr`, `rsInt_eq_integral_of_incr`: the same for a path given by
  its increments, `g(v) − g(u) = ∫_u^v h` for all `u ≤ v`, with `h` locally integrable (the form
  used for `A` and for `B + M`).
-/

namespace Cochrane.Monetarism.TidyR7MonetarismAC

open MeasureTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesIntegral Cochrane.Monetarism.TidyR7StieltjesSums

/-- Cochrane (2023), A1 §1.6, p. 567 (tool for (1.32)): **the variation of a primitive.** If
`g(x) = g(a) + ∫_a^x h` on `[a, b]`, `h` interval integrable, then
`Var_{[a,b]} g ≤ ∫_a^b |h|`. -/
theorem eVariationOn_le_integral {a b : ℝ} {g h : ℝ → ℝ} (hab : a ≤ b)
    (hh : IntervalIntegrable h MeasureSpace.volume a b)
    (hg : ∀ x ∈ Set.Icc a b, g x = g a + ∫ y in a..x, h y) :
    eVariationOn g (Set.Icc a b) ≤ ENNReal.ofReal (∫ y in a..b, |h y|) := by
  have hsub : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      IntervalIntegrable h MeasureSpace.volume x y := fun x hx y hy =>
    hh.mono_set (Set.uIcc_subset_uIcc (Set.mem_uIcc_of_le hx.1 hx.2)
      (Set.mem_uIcc_of_le hy.1 hy.2))
  have hdiff : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, g y - g x = ∫ r in x..y, h r := by
    intro x hx y hy
    rw [hg x hx, hg y hy, add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left (hsub a ⟨le_rfl, hab⟩ y hy)
        (hsub a ⟨le_rfl, hab⟩ x hx)]
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, hmem⟩ := p
  have hab' : ∀ i, ∫ r in u i..u (i + 1), |h r| ≥ 0 := fun i =>
    intervalIntegral.integral_nonneg (hu (Nat.le_succ i)) fun _ _ => abs_nonneg _
  calc ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i))
      ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (∫ r in u i..u (i + 1), |h r|) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [edist_dist, Real.dist_eq, hdiff _ (hmem i) _ (hmem (i + 1))]
        exact ENNReal.ofReal_le_ofReal
          (intervalIntegral.abs_integral_le_integral_abs (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, ∫ r in u i..u (i + 1), |h r|) :=
        (ENNReal.ofReal_sum_of_nonneg fun i _ => hab' i).symm
    _ = ENNReal.ofReal (∫ r in u 0..u n, |h r|) := by
        rw [intervalIntegral.sum_integral_adjacent_intervals fun i _ =>
          (hsub _ (hmem i) _ (hmem (i + 1))).abs]
    _ ≤ ENNReal.ofReal (∫ y in a..b, |h y|) := by
        refine ENNReal.ofReal_le_ofReal (intervalIntegral.integral_mono_interval (hmem 0).1
          (hu (Nat.zero_le n)) (hmem n).2 (Eventually.of_forall fun _ => abs_nonneg _) hh.abs)

/-- Cochrane (2023), A1 §1.6, p. 567 (tool for (1.32)): a primitive of an interval integrable
function has bounded variation on `[a, b]`.
Generalises `TidyR7ProductStepCases.bv_of_hasDerivAt`. -/
theorem bv_of_primitive {a b : ℝ} {g h : ℝ → ℝ} (hab : a ≤ b)
    (hh : IntervalIntegrable h MeasureSpace.volume a b)
    (hg : ∀ x ∈ Set.Icc a b, g x = g a + ∫ y in a..x, h y) :
    BoundedVariationOn g (Set.Icc a b) :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (eVariationOn_le_integral hab hh hg)

/-- Cochrane (2023), A1 §1.6, p. 567 (tool for (1.32)): a primitive of an interval integrable
function is continuous on `[a, b]`.
From Mathlib `intervalIntegral.continuousOn_primitive_interval`. -/
theorem continuousOn_of_primitive {a b : ℝ} {g h : ℝ → ℝ} (hab : a ≤ b)
    (hh : IntervalIntegrable h MeasureSpace.volume a b)
    (hg : ∀ x ∈ Set.Icc a b, g x = g a + ∫ y in a..x, h y) :
    ContinuousOn g (Set.Icc a b) := by
  have hI : IntegrableOn h (Set.uIcc a b) MeasureSpace.volume := by
    rw [Set.uIcc_of_le hab]
    exact (integrableOn_Icc_iff_integrableOn_Ioc (by simp)).2
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hh)
  have hc := intervalIntegral.continuousOn_primitive_interval hI
  rw [Set.uIcc_of_le hab] at hc
  exact (continuousOn_const.add hc).congr hg

/-- **Cochrane (2023), A1 §1.6, p. 567 (tool for (1.32)): the Stieltjes integral against an
absolutely continuous integrator.** For `f` càdlàg, `h` interval integrable on `[a, b]` and
`g(x) = g(a) + ∫_a^x h` on `[a, b]`: `∫_a^b f dg = ∫_a^b f(x)h(x) dx`.
Generalises `TidyR7ProductStepCases.rsInt_eq_integral_mul_deriv`. -/
theorem rsInt_eq_integral_of_primitive {a b : ℝ} {f g h : ℝ → ℝ} (hab : a ≤ b) (hf : IsCadlag f)
    (hh : IntervalIntegrable h MeasureSpace.volume a b)
    (hg : ∀ x ∈ Set.Icc a b, g x = g a + ∫ y in a..x, h y) :
    rsInt a b f g = ∫ x in a..b, f x * h x := by
  rcases hab.lt_or_eq with hlt | rfl
  swap
  · rw [TidyR7StieltjesVariation.rsInt_self, intervalIntegral.integral_same]
  have hbv := bv_of_primitive hab hh hg
  have hgc := continuousOn_of_primitive hab hh hg
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_isCadlag hf a b
  have hsub : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      IntervalIntegrable h MeasureSpace.volume x y := fun x hx y hy =>
    hh.mono_set (Set.uIcc_subset_uIcc (Set.mem_uIcc_of_le hx.1 hx.2)
      (Set.mem_uIcc_of_le hy.1 hy.2))
  have hdiff : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, g y - g x = ∫ r in x..y, h r := by
    intro x hx y hy
    rw [hg x hx, hg y hy, add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left (hsub a ⟨le_rfl, hab⟩ y hy)
        (hsub a ⟨le_rfl, hab⟩ x hx)]
  -- integrability of `φ h` for a bounded step function `φ`
  have hint : ∀ (P : Partition a b) (c : ℕ → ℝ), (∀ i < P.n, |c i| ≤ C) →
      IntervalIntegrable (fun x => stepFn P c x * h x) MeasureSpace.volume a b := by
    intro P c hc
    rw [intervalIntegrable_iff] at hh ⊢
    refine hh.bdd_mul (c := C) (measurable_stepFn P c).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact abs_stepFn_le P c hC0 hc x
  -- each left-point sum is the integral of a step function against `h`
  have hstep : ∀ P : Partition a b, rsSum P f g =
      ∫ x in a..b, stepFn P (fun i => f (P.t i)) x * h x := by
    intro P
    have hc : ∀ i < P.n, |f (P.t i)| ≤ C := fun i hi => hC _ (t_mem P hi.le)
    have hI := hint P _ hc
    have hlt : ∀ i, P.t i < P.t (i + 1) := fun i => P.strictMono (Nat.lt_succ_self i)
    have hpiece : ∀ i < P.n, IntervalIntegrable (fun x => stepFn P (fun i => f (P.t i)) x * h x)
        MeasureSpace.volume (P.t i) (P.t (i + 1)) := fun i hi =>
      hI.mono_set (Set.uIcc_subset_uIcc (Set.mem_uIcc_of_le (t_mem P hi.le).1 (t_mem P hi.le).2)
        (Set.mem_uIcc_of_le (t_mem P hi).1 (t_mem P hi).2))
    have hs := intervalIntegral.sum_integral_adjacent_intervals hpiece
    rw [P.first, P.last] at hs
    rw [← hs]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [hdiff _ (t_mem P hi'.le) _ (t_mem P hi'), ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun x hx => ?_)
    rw [Set.uIoc_of_le (hlt i).le] at hx
    rw [stepFn_eq P _ hi' hx]
  have hP := tendsto_mesh_dyadic hlt
  have hlim1 := tendsto_rsSum_of_isCadlag hf hbv hgc (dyadic hlt) hP
  simp only [hstep] at hlim1
  have hlim2 : Tendsto (fun k => ∫ x in a..b, stepFn (dyadic hlt k)
      (fun i => f ((dyadic hlt k).t i)) x * h x) atTop (𝓝 (∫ x in a..b, f x * h x)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun x => C * |h x|) (Eventually.of_forall fun k => ?_)
      (Eventually.of_forall fun k => ae_of_all _ fun x _ => ?_) ?_ ?_
    · exact (hint _ _ fun i hi => hC _ (t_mem _ hi.le)).def'.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_stepFn_le _ _ hC0
        (fun i hi => hC _ (t_mem _ hi.le)) x) (abs_nonneg _)
    · exact hh.abs.const_mul C
    · have hnull : MeasureSpace.volume {x | f x ≠ Function.leftLim f x} = 0 :=
        (countable_jumps hf).measure_zero _
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx hxab
      rw [Set.uIoc_of_le hab] at hxab
      have hcont : ContinuousAt f x := continuousAt_of_leftLim_eq hf
        (by simp only [not_not] at hx; exact hx.symm)
      exact (tendsto_stepFn_left (dyadic hlt) hP hxab
        (hcont.tendsto.mono_left nhdsWithin_le_nhds)).mul_const _
  exact tendsto_nhds_unique hlim1 hlim2

/-- Cochrane (2023), A1 §1.6, p. 567 (tool for (1.31)): **a path given by its increments**,
`g(v) − g(u) = ∫_u^v h` for all `u ≤ v`, is the primitive `g(a) + ∫_a^x h` on every `[a, b]`. -/
theorem primitive_of_incr {g h : ℝ → ℝ}
    (hg : ∀ u v, u ≤ v → g v - g u = ∫ r in u..v, h r) (a b : ℝ) :
    ∀ x ∈ Set.Icc a b, g x = g a + ∫ y in a..x, h y := fun x hx => by
  linarith [hg a x hx.1]

/-- Cochrane (2023), A1 §1.6, p. 567 (tool for (1.31)): a path given by its increments against a
locally integrable density is continuous on `ℝ`.
From Mathlib `intervalIntegral.continuous_primitive`.
Generalises `TidyR7ProductStepCases.continuous_of_hasDerivAt`. -/
theorem continuous_of_incr {g h : ℝ → ℝ}
    (hh : ∀ u v, IntervalIntegrable h MeasureSpace.volume u v)
    (hg : ∀ u v, u ≤ v → g v - g u = ∫ r in u..v, h r) : Continuous g := by
  have e : g = fun x => g 0 + ∫ r in (0 : ℝ)..x, h r := by
    funext x
    rcases le_total 0 x with hx | hx
    · linarith [hg 0 x hx]
    · have := hg x 0 hx
      rw [intervalIntegral.integral_symm]
      linarith
  rw [e]
  exact continuous_const.add (intervalIntegral.continuous_primitive hh 0)

/-- Cochrane (2023), A1 §1.6, p. 567 (tool for (1.31)): a path given by its increments against a
locally integrable density has bounded variation on every `[a, b]`.
Generalises `TidyR7ProductStepCases.bv_of_hasDerivAt`. -/
theorem bv_of_incr {g h : ℝ → ℝ} (hh : ∀ u v, IntervalIntegrable h MeasureSpace.volume u v)
    (hg : ∀ u v, u ≤ v → g v - g u = ∫ r in u..v, h r) (a b : ℝ) :
    BoundedVariationOn g (Set.Icc a b) := by
  rcases le_total a b with hab | hab
  · exact bv_of_primitive hab (hh a b) (primitive_of_incr hg a b)
  · rcases hab.lt_or_eq with hlt | heq
    · rw [Set.Icc_eq_empty (not_le.2 hlt), BoundedVariationOn, eVariationOn.subsingleton _
        Set.subsingleton_empty]
      exact ENNReal.zero_ne_top
    · rw [heq]
      exact bv_of_primitive le_rfl (hh a a) (primitive_of_incr hg a a)

/-- **Cochrane (2023), A1 §1.6, p. 567 (tool for (1.32)): the Stieltjes integral against a path
given by its increments.** For `f` càdlàg, `h` locally integrable and
`g(v) − g(u) = ∫_u^v h` for `u ≤ v`: `∫_a^b f dg = ∫_a^b f h` for `a ≤ b`.
Generalises `TidyR7ProductStepCases.rsInt_eq_integral_mul_deriv`. -/
theorem rsInt_eq_integral_of_incr {f g h : ℝ → ℝ} (hf : IsCadlag f)
    (hh : ∀ u v, IntervalIntegrable h MeasureSpace.volume u v)
    (hg : ∀ u v, u ≤ v → g v - g u = ∫ r in u..v, h r) {a b : ℝ} (hab : a ≤ b) :
    rsInt a b f g = ∫ x in a..b, f x * h x :=
  rsInt_eq_integral_of_primitive hab hf (hh a b) (primitive_of_incr hg a b)

end Cochrane.Monetarism.TidyR7MonetarismAC
