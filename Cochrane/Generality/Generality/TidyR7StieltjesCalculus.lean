/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.TidyR7StieltjesSums

/-!
# Riemann–Stieltjes calculus: products, integration by parts, measurability in a parameter

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). The product step in (1.32),
`Λ/P · dB + E_t d(Λ/P)·B = E_t d(ΛB/P)`, is proved path by path from the exact partition identity
for products. These are the deterministic Riemann–Stieltjes tools for that (1.32) product step.

## Main results

* `prod_partition_identity`: for every partition,
  `f(b)g(b) − f(a)g(a) = Σ f_iΔg_i + Σ g_iΔf_i + Σ Δf_iΔg_i` exactly.
* `integration_by_parts`: `f(b)g(b) − f(a)g(a) = ∫_a^b f dg + ∫_a^b g df` for `f`, `g`
  continuous of bounded variation; `integration_by_parts_of_isCadlag`: the same for `f` càdlàg of
  bounded variation and `g` continuous of bounded variation (both from the partition identity,
  `TidyR7StieltjesSums.tendsto_crossSum_zero` and the convergence of the sums).
* `abs_rsSum_le`, `abs_crossSum_le`: the sums are dominated, `|Σ f_iΔg_i| ≤ sup|f|·Var(g)`,
  `|Σ Δf_iΔg_i| ≤ 2 sup|f|·Var(g)`, uniformly in the partition (for conditional dominated
  convergence).
* `measurable_rsSum`, `tendsto_rsSum_dyadic_pi`, `measurable_rsInt`: for paths `f(ω, ·)`,
  `g(ω, ·)` as in case (a) or (b) for each `ω`, with `f(·, t)`, `g(·, t)` measurable, the dyadic
  sums are measurable in `ω` and converge pointwise in `ω`, so `ω ↦ ∫_a^b f(ω) dg(ω)` is
  measurable.
-/

namespace Cochrane.Generality.TidyR7StieltjesCalculus

open MeasureTheory Filter Topology
open Cochrane.Generality.TidyR7StieltjesIntegral Cochrane.Generality.TidyR7StieltjesSums

variable {a b : ℝ}

/-! ## The exact partition identity for products -/

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the exact partition identity for products.**
For every partition of `[a, b]`,
`f(b)g(b) − f(a)g(a) = Σ f(t_i)Δg_i + Σ g(t_i)Δf_i + Σ Δf_iΔg_i`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesCalculus.prod_partition_identity). -/
theorem prod_partition_identity (P : Partition a b) (f g : ℝ → ℝ) :
    f b * g b - f a * g a = rsSum P f g + rsSum P g f + crossSum P f g := by
  have ht := Finset.sum_range_sub (fun i => f (P.t i) * g (P.t i)) P.n
  rw [P.last, P.first] at ht
  rw [← ht, rsSum, rsSum, crossSum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ## Domination of the sums -/

/-- Cochrane (2023), A1 §1.6, p. 567: `Σ |g(t_{i+1}) − g(t_i)| ≤ Var_{[a,b]}(g)` for every
partition.
Mathlib `eVariationOn.sum_le_of_monotoneOn_Icc` in real form.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesCalculus.sum_abs_sub_le). -/
theorem sum_abs_sub_le {g : ℝ → ℝ} (hg : BoundedVariationOn g (Set.Icc a b))
    (P : Partition a b) :
    ∑ i ∈ Finset.range P.n, |g (P.t (i + 1)) - g (P.t i)| ≤
      (eVariationOn g (Set.Icc a b)).toReal := by
  have h := eVariationOn.sum_le_of_monotoneOn_Icc (f := g) (s := Set.Icc a b) (m := 0)
    (n := P.n) (u := P.t) (P.strictMono.monotone.monotoneOn _) fun i hi => t_mem P hi.2
  rw [← Finset.range_eq_Ico] at h
  have e : ∑ i ∈ Finset.range P.n, |g (P.t (i + 1)) - g (P.t i)| =
      (∑ i ∈ Finset.range P.n, edist (g (P.t (i + 1))) (g (P.t i))).toReal := by
    rw [ENNReal.toReal_sum fun _ _ => edist_ne_top _ _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg, Real.dist_eq]
  rw [e]
  exact ENNReal.toReal_mono hg h

/-- Cochrane (2023), A1 §1.6, p. 567: **domination of the Riemann–Stieltjes sums**,
`|Σ f(t_i)Δg_i| ≤ sup_{[a,b]}|f| · Var_{[a,b]}(g)` for every partition.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesCalculus.abs_rsSum_le). -/
theorem abs_rsSum_le {f g : ℝ → ℝ} {C : ℝ} (hg : BoundedVariationOn g (Set.Icc a b))
    (hC : ∀ x ∈ Set.Icc a b, |f x| ≤ C) (P : Partition a b) :
    |rsSum P f g| ≤ C * (eVariationOn g (Set.Icc a b)).toReal := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC a ⟨le_rfl, a_le_b P⟩)
  calc |rsSum P f g| ≤ ∑ i ∈ Finset.range P.n, |f (P.t i) * (g (P.t (i + 1)) - g (P.t i))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range P.n, C * |g (P.t (i + 1)) - g (P.t i)| := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hC _ (t_mem P (Finset.mem_range.1 hi).le))
          (abs_nonneg _)
    _ = C * ∑ i ∈ Finset.range P.n, |g (P.t (i + 1)) - g (P.t i)| := (Finset.mul_sum _ _ _).symm
    _ ≤ C * (eVariationOn g (Set.Icc a b)).toReal :=
        mul_le_mul_of_nonneg_left (sum_abs_sub_le hg P) hC0

/-- Cochrane (2023), A1 §1.6, p. 567: **domination of the cross sums**,
`|Σ Δf_iΔg_i| ≤ 2 sup_{[a,b]}|f| · Var_{[a,b]}(g)` for every partition.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesCalculus.abs_crossSum_le). -/
theorem abs_crossSum_le {f g : ℝ → ℝ} {C : ℝ} (hg : BoundedVariationOn g (Set.Icc a b))
    (hC : ∀ x ∈ Set.Icc a b, |f x| ≤ C) (P : Partition a b) :
    |crossSum P f g| ≤ 2 * C * (eVariationOn g (Set.Icc a b)).toReal := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC a ⟨le_rfl, a_le_b P⟩)
  calc |crossSum P f g| ≤ ∑ i ∈ Finset.range P.n,
        |(f (P.t (i + 1)) - f (P.t i)) * (g (P.t (i + 1)) - g (P.t i))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range P.n, 2 * C * |g (P.t (i + 1)) - g (P.t i)| := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        have h1 := hC _ (t_mem P (Finset.mem_range.1 hi))
        have h2 := hC _ (t_mem P (Finset.mem_range.1 hi).le)
        calc |f (P.t (i + 1)) - f (P.t i)| ≤ |f (P.t (i + 1))| + |f (P.t i)| := abs_sub _ _
          _ ≤ 2 * C := by linarith
    _ = 2 * C * ∑ i ∈ Finset.range P.n, |g (P.t (i + 1)) - g (P.t i)| :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * C * (eVariationOn g (Set.Icc a b)).toReal :=
        mul_le_mul_of_nonneg_left (sum_abs_sub_le hg P) (by linarith)

/-! ## Integration by parts -/

/-- Cochrane (2023), A1 §1.6, p. 567: for `f` continuous and `g` of bounded variation on
`[a, b]`, the cross sum tends to `0` as the mesh → 0.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesCalculus.tendsto_crossSum_zero_of_continuousOn). -/
theorem tendsto_crossSum_zero_of_continuousOn {f g : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    (hg : BoundedVariationOn g (Set.Icc a b)) (P : ℕ → Partition a b)
    (hP : Tendsto (fun k => mesh (P k)) atTop (𝓝 0)) :
    Tendsto (fun k => crossSum (P k) f g) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  set V := (eVariationOn g (Set.Icc a b)).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set ε := η / (V + 1) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hP δ hδ
  refine ⟨N, fun k hk => ?_⟩
  have hmk : mesh (P k) < δ := by
    have := hN k hk
    rw [Real.dist_eq, sub_zero] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  rw [Real.dist_eq, sub_zero]
  have hb : |crossSum (P k) f g| ≤ ε * V := by
    calc |crossSum (P k) f g| ≤ ∑ i ∈ Finset.range (P k).n,
          |(f ((P k).t (i + 1)) - f ((P k).t i)) * (g ((P k).t (i + 1)) - g ((P k).t i))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (P k).n, ε * |g ((P k).t (i + 1)) - g ((P k).t i)| := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          have hi' := Finset.mem_range.1 hi
          have := hδf _ (t_mem (P k) hi') _ (t_mem (P k) hi'.le) (by
            rw [Real.dist_eq, abs_of_nonneg (by linarith [(P k).strictMono (Nat.lt_succ_self i)])]
            exact lt_of_le_of_lt (le_mesh (P k) hi') hmk)
          rw [Real.dist_eq] at this
          exact this.le
      _ = ε * ∑ i ∈ Finset.range (P k).n, |g ((P k).t (i + 1)) - g ((P k).t i)| :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ ε * V := mul_le_mul_of_nonneg_left (sum_abs_sub_le hg (P k)) hε.le
  refine lt_of_le_of_lt hb ?_
  rw [hεdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

/-- **Cochrane (2023), A1 §1.6, p. 567: integration by parts.** For `f`, `g` continuous of
bounded variation on `[a, b]`, `a < b`: `f(b)g(b) − f(a)g(a) = ∫_a^b f dg + ∫_a^b g df`.
As a statement, a special case of Mathlib
`BoundedVariationOn.setIntegral_Icc_leftLim_smul_vectorMeasure_eq_sub`; proved here from the
partition identity.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesCalculus.integration_by_parts). -/
theorem integration_by_parts {f g : ℝ → ℝ} (hab : a < b) (hfc : ContinuousOn f (Set.Icc a b))
    (hf : BoundedVariationOn f (Set.Icc a b)) (hgc : ContinuousOn g (Set.Icc a b))
    (hg : BoundedVariationOn g (Set.Icc a b)) :
    f b * g b - f a * g a = rsInt a b f g + rsInt a b g f := by
  have h := ((tendsto_rsSum_dyadic_of_continuousOn hab hfc hg).add
    (tendsto_rsSum_dyadic_of_continuousOn hab hgc hf)).add
    (tendsto_crossSum_zero_of_continuousOn hfc hg _ (tendsto_mesh_dyadic hab))
  rw [add_zero] at h
  have e : ∀ k, rsSum (dyadic hab k) f g + rsSum (dyadic hab k) g f +
      crossSum (dyadic hab k) f g = f b * g b - f a * g a :=
    fun k => (prod_partition_identity _ f g).symm
  exact tendsto_nhds_unique tendsto_const_nhds ((tendsto_congr e).1 h)

/-- **Cochrane (2023), A1 §1.6, p. 567: integration by parts with one càdlàg factor.** For `f`
càdlàg of bounded variation on `[a, b]` and `g` continuous of bounded variation on `[a, b]`,
`a < b`: `f(b)g(b) − f(a)g(a) = ∫_a^b f dg + ∫_a^b g df` (`∫ g df` charges the jumps of `f`
with the value of the continuous `g`; `∫ f dg = ∫ f(t−) dg` since `g` has no atoms).
As a statement, a special case of Mathlib
`BoundedVariationOn.setIntegral_Icc_leftLim_smul_vectorMeasure_eq_sub`; proved here from the
partition identity.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesCalculus.integration_by_parts_of_isCadlag). -/
theorem integration_by_parts_of_isCadlag {f g : ℝ → ℝ} (hab : a < b) (hfc : IsCadlag f)
    (hf : BoundedVariationOn f (Set.Icc a b)) (hgc : ContinuousOn g (Set.Icc a b))
    (hg : BoundedVariationOn g (Set.Icc a b)) :
    f b * g b - f a * g a = rsInt a b f g + rsInt a b g f := by
  have h := ((tendsto_rsSum_dyadic_of_isCadlag hab hfc hg hgc).add
    (tendsto_rsSum_dyadic_of_continuousOn hab hgc hf)).add
    (tendsto_crossSum_dyadic hab hfc hg hgc)
  rw [add_zero] at h
  have e : ∀ k, rsSum (dyadic hab k) f g + rsSum (dyadic hab k) g f +
      crossSum (dyadic hab k) f g = f b * g b - f a * g a :=
    fun k => (prod_partition_identity _ f g).symm
  exact tendsto_nhds_unique tendsto_const_nhds ((tendsto_congr e).1 h)

/-! ## Measurability in a parameter -/

/-- Cochrane (2023), A1 §1.6, p. 567: if every `f(·, t)`, `g(·, t)` is measurable, every
Riemann–Stieltjes sum `ω ↦ Σ f(ω, t_i)(g(ω, t_{i+1}) − g(ω, t_i))` is measurable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesCalculus.measurable_rsSum). -/
theorem measurable_rsSum {Ω : Type*} [MeasurableSpace Ω] {f g : Ω → ℝ → ℝ}
    (hf : ∀ t, Measurable fun ω => f ω t) (hg : ∀ t, Measurable fun ω => g ω t)
    (P : Partition a b) : Measurable fun ω => rsSum P (f ω) (g ω) := by
  simp only [rsSum]
  exact Finset.measurable_sum _ fun i _ => (hf _).mul ((hg _).sub (hg _))

/-- Cochrane (2023), A1 §1.6, p. 567: if every `f(·, t)`, `g(·, t)` is measurable, every cross sum
is measurable in `ω`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesCalculus.measurable_crossSum). -/
theorem measurable_crossSum {Ω : Type*} [MeasurableSpace Ω] {f g : Ω → ℝ → ℝ}
    (hf : ∀ t, Measurable fun ω => f ω t) (hg : ∀ t, Measurable fun ω => g ω t)
    (P : Partition a b) : Measurable fun ω => crossSum P (f ω) (g ω) := by
  simp only [crossSum]
  exact Finset.measurable_sum _ fun i _ => ((hf _).sub (hf _)).mul ((hg _).sub (hg _))

/-- Cochrane (2023), A1 §1.6, p. 567: if for each `ω` the paths `f(ω, ·)`, `g(ω, ·)` are as in
case (a) (`f` continuous, `g` of bounded variation) or case (b) (`f` càdlàg, `g` continuous of
bounded variation), the dyadic sums converge to `ω ↦ ∫_a^b f(ω) dg(ω)` pointwise in `ω`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesCalculus.tendsto_rsSum_dyadic_pi). -/
theorem tendsto_rsSum_dyadic_pi {Ω : Type*} {f g : Ω → ℝ → ℝ} (hab : a < b)
    (hcase : ∀ ω, (ContinuousOn (f ω) (Set.Icc a b) ∧
        BoundedVariationOn (g ω) (Set.Icc a b)) ∨
      (IsCadlag (f ω) ∧ BoundedVariationOn (g ω) (Set.Icc a b) ∧
        ContinuousOn (g ω) (Set.Icc a b))) :
    Tendsto (fun k ω => rsSum (dyadic hab k) (f ω) (g ω)) atTop
      (𝓝 fun ω => rsInt a b (f ω) (g ω)) := by
  rw [tendsto_pi_nhds]
  intro ω
  rcases hcase ω with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · exact tendsto_rsSum_dyadic_of_continuousOn hab h1 h2
  · exact tendsto_rsSum_dyadic_of_isCadlag hab h1 h2 h3

/-- **Cochrane (2023), A1 §1.6, p. 567: measurability in a parameter.** If for each `ω` the paths
`f(ω, ·)`, `g(ω, ·)` are as in case (a) or case (b), and every `f(·, t)`, `g(·, t)` is
measurable, then `ω ↦ ∫_a^b f(ω) dg(ω)` is measurable (the pointwise limit of the measurable
dyadic sums, `tendsto_rsSum_dyadic_pi`; the sums are dominated by `abs_rsSum_le`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7StieltjesCalculus.measurable_rsInt). -/
theorem measurable_rsInt {Ω : Type*} [MeasurableSpace Ω] {f g : Ω → ℝ → ℝ} (hab : a < b)
    (hf : ∀ t, Measurable fun ω => f ω t) (hg : ∀ t, Measurable fun ω => g ω t)
    (hcase : ∀ ω, (ContinuousOn (f ω) (Set.Icc a b) ∧
        BoundedVariationOn (g ω) (Set.Icc a b)) ∨
      (IsCadlag (f ω) ∧ BoundedVariationOn (g ω) (Set.Icc a b) ∧
        ContinuousOn (g ω) (Set.Icc a b))) :
    Measurable fun ω => rsInt a b (f ω) (g ω) :=
  measurable_of_tendsto_metrizable (fun k => measurable_rsSum hf hg (dyadic hab k))
    (tendsto_rsSum_dyadic_pi hab hcase)

end Cochrane.Generality.TidyR7StieltjesCalculus
