/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR7StieltjesVariation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Conditional dominated convergence and measurable path suprema

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). The product step in (1.32),
`Λ/P · dB + E_t d(Λ/P)·B = E_t d(ΛB/P)`, is proved in `TidyR7ProductStep` by passing the pathwise
Riemann–Stieltjes limits of `TidyR7StieltjesSums` under the conditional expectation `E_s`. These
are the probabilistic tools for that step.

## Main results

* `ae_tendsto_condExp_of_dominated`: **conditional dominated convergence, almost surely.** If
  `F_k → f` pointwise, `|F_k| ≤ D` with `D` integrable and the `F_k` measurable, then
  `E[F_k | 𝓖] → E[f | 𝓖]` almost surely (for any sub-σ-algebra `𝓖` and finite measure). Mathlib
  has the `L¹` form (`MeasureTheory.tendsto_condExpL1_of_dominated_convergence`); the a.s. form is
  proved here from the tail suprema `tailSup F f k = sup_{j ≥ k}|F_j − f|`: their conditional
  expectations decrease a.s. to a nonnegative limit whose integral is `0` by dominated
  convergence.
* `pathSup`: the **measurable supremum of a path**, `sup_{q ∈ D}|X_q(ω)|` over the countable set
  `D = TidyR7StieltjesVariation.denseSet s t` (rationals of `[s, t]` with `t`).
  `measurable_pathSup`: measurable when each `X_u` (`u ∈ [s, t]`) is. `abs_le_pathSup_of_right`:
  it bounds `|X_u(ω)|` on all of `[s, t]` when the path is right-continuous and bounded on
  `[s, t]` (each `u` is the limit of the points `pushRight t k u ∈ D` from the right); corollaries
  for càdlàg paths (`abs_le_pathSup_of_isCadlag`) and paths continuous on `[s, t]`
  (`abs_le_pathSup_of_continuousOn`). This is the measurable `C(ω)` with
  `|Σ X_iΔB_i| ≤ C(ω)·Var(B)(ω)` that conditional dominated convergence needs.
* `exists_partition_seq`: for `s ≤ t` there is a sequence of partitions of `[s, t]` with mesh
  `→ 0` (dyadic for `s < t`, `pointPartition` for `s = t`).
-/

namespace Cochrane.LongTermDebtDynamics.TidyR7CondDominated

open MeasureTheory Filter Topology
open Cochrane.LongTermDebtDynamics.TidyR7StieltjesIntegral
  Cochrane.LongTermDebtDynamics.TidyR7StieltjesSums
  Cochrane.LongTermDebtDynamics.TidyR7StieltjesVariation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ## Tail suprema -/

/-- Cochrane (2023), A1 §1.6, p. 567 (tool for (1.32)): the tail supremum
`sup_{j ≥ k}|F_j(ω) − f(ω)|`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7CondDominated.tailSup). -/
noncomputable def tailSup (F : ℕ → Ω → ℝ) (f : Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ⨆ j : ℕ, |F (k + j) ω - f ω|

/-- Cochrane (2023), A1 §1.6, p. 567: under `|F_k| ≤ D`, `|f| ≤ D` the tail is bounded by
`2D`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7CondDominated.tailSup_bddAbove). -/
theorem tailSup_bddAbove {F : ℕ → Ω → ℝ} {f D : Ω → ℝ} (hbd : ∀ k ω, |F k ω| ≤ D ω)
    (hf : ∀ ω, |f ω| ≤ D ω) (k : ℕ) (ω : Ω) :
    ∀ j, |F (k + j) ω - f ω| ≤ 2 * D ω := by
  intro j
  have h1 := hbd (k + j) ω
  have h2 := hf ω
  calc |F (k + j) ω - f ω| ≤ |F (k + j) ω| + |f ω| := abs_sub _ _
    _ ≤ 2 * D ω := by linarith

/-- Cochrane (2023), A1 §1.6, p. 567: `0 ≤ tailSup F f k ω ≤ 2D(ω)`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7CondDominated.tailSup_mem). -/
theorem tailSup_mem {F : ℕ → Ω → ℝ} {f D : Ω → ℝ} (hbd : ∀ k ω, |F k ω| ≤ D ω)
    (hf : ∀ ω, |f ω| ≤ D ω) (k : ℕ) (ω : Ω) :
    0 ≤ tailSup F f k ω ∧ tailSup F f k ω ≤ 2 * D ω :=
  ⟨Real.iSup_nonneg fun _ => abs_nonneg _, ciSup_le (tailSup_bddAbove hbd hf k ω)⟩

/-- Cochrane (2023), A1 §1.6, p. 567: `|F_{k+j} − f| ≤ tailSup F f k`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7CondDominated.le_tailSup). -/
theorem le_tailSup {F : ℕ → Ω → ℝ} {f D : Ω → ℝ} (hbd : ∀ k ω, |F k ω| ≤ D ω)
    (hf : ∀ ω, |f ω| ≤ D ω) (k j : ℕ) (ω : Ω) : |F (k + j) ω - f ω| ≤ tailSup F f k ω :=
  le_ciSup ⟨2 * D ω, by rintro _ ⟨i, rfl⟩; exact tailSup_bddAbove hbd hf k ω i⟩ j

/-- Cochrane (2023), A1 §1.6, p. 567: the tail suprema decrease in `k`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7CondDominated.tailSup_succ_le). -/
theorem tailSup_succ_le {F : ℕ → Ω → ℝ} {f D : Ω → ℝ} (hbd : ∀ k ω, |F k ω| ≤ D ω)
    (hf : ∀ ω, |f ω| ≤ D ω) (k : ℕ) (ω : Ω) : tailSup F f (k + 1) ω ≤ tailSup F f k ω :=
  ciSup_le fun j => by
    have := le_tailSup hbd hf k (j + 1) ω
    rwa [show k + (j + 1) = k + 1 + j by omega] at this

/-- Cochrane (2023), A1 §1.6, p. 567: if `F_k(ω) → f(ω)` the tail suprema tend to `0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7CondDominated.tendsto_tailSup). -/
theorem tendsto_tailSup {F : ℕ → Ω → ℝ} {f D : Ω → ℝ} (hbd : ∀ k ω, |F k ω| ≤ D ω)
    (hf : ∀ ω, |f ω| ≤ D ω) {ω : Ω} (hlim : Tendsto (fun k => F k ω) atTop (𝓝 (f ω))) :
    Tendsto (fun k => tailSup F f k ω) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim (ε / 2) (by linarith)
  refine ⟨N, fun k hk => ?_⟩
  have h0 := (tailSup_mem hbd hf k ω).1
  have hle : tailSup F f k ω ≤ ε / 2 := ciSup_le fun j => by
    have := hN (k + j) (by omega)
    rw [Real.dist_eq] at this
    exact this.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith

/-- Cochrane (2023), A1 §1.6, p. 567: the tail suprema of measurable functions are measurable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7CondDominated.measurable_tailSup). -/
theorem measurable_tailSup {F : ℕ → Ω → ℝ} {f : Ω → ℝ} (hF : ∀ k, Measurable (F k))
    (hf : Measurable f) (k : ℕ) : Measurable (tailSup F f k) :=
  Measurable.iSup fun j => continuous_abs.measurable.comp ((hF (k + j)).sub hf)

/-! ## Conditional dominated convergence -/

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567 (tool): conditional dominated convergence,
almost surely.** If the `F_k` are measurable, `F_k(ω) → f(ω)` for every `ω` and
`|F_k| ≤ D` with `D` integrable, then `E[F_k | 𝓖] → E[f | 𝓖]` almost surely.
The almost-sure form of Mathlib `tendsto_condExpL1_of_dominated_convergence`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7CondDominated.ae_tendsto_condExp_of_dominated). -/
theorem ae_tendsto_condExp_of_dominated {m m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hm : m ≤ m0) {F : ℕ → Ω → ℝ} {f D : Ω → ℝ}
    (hF : ∀ k, Measurable (F k)) (hD : Integrable D μ) (hbd : ∀ k ω, |F k ω| ≤ D ω)
    (hlim : ∀ ω, Tendsto (fun k => F k ω) atTop (𝓝 (f ω))) :
    ∀ᵐ ω ∂μ, Tendsto (fun k => μ[F k | m] ω) atTop (𝓝 (μ[f | m] ω)) := by
  have hfm : Measurable f := measurable_of_tendsto_metrizable hF (tendsto_pi_nhds.2 hlim)
  have hfD : ∀ ω, |f ω| ≤ D ω := fun ω => le_of_tendsto' (hlim ω).abs fun k => hbd k ω
  have hFi : ∀ k, Integrable (F k) μ := fun k =>
    hD.mono' (hF k).aestronglyMeasurable (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hbd k ω)
  have hfi : Integrable f μ := hD.mono' hfm.aestronglyMeasurable (Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hfD ω)
  have hgm := measurable_tailSup hF hfm
  have hgi : ∀ k, Integrable (tailSup F f k) μ := fun k =>
    (hD.const_mul 2).mono' (hgm k).aestronglyMeasurable (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (tailSup_mem hbd hfD k ω).1]
      exact (tailSup_mem hbd hfD k ω).2)
  have hint : Tendsto (fun k => ∫ ω, tailSup F f k ω ∂μ) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (fun ω => 2 * D ω)
      (fun k => (hgm k).aestronglyMeasurable) (hD.const_mul 2)
      (fun k => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (tailSup_mem hbd hfD k ω).1]
        exact (tailSup_mem hbd hfD k ω).2)
      (Eventually.of_forall fun ω => tendsto_tailSup hbd hfD (hlim ω))
    simpa using this
  set c : ℕ → Ω → ℝ := fun k => μ[tailSup F f k | m] with hc
  have hae : ∀ᵐ ω ∂μ, ∀ k, c (k + 1) ω ≤ c k ω ∧ 0 ≤ c k ω ∧
      |μ[F k | m] ω - μ[f | m] ω| ≤ c k ω := by
    rw [ae_all_iff]
    intro k
    have h1 := condExp_mono (m := m) (hgi (k + 1)) (hgi k)
      (Eventually.of_forall fun ω => tailSup_succ_le hbd hfD k ω)
    have h2 := condExp_nonneg (m := m) (μ := μ)
      (Eventually.of_forall fun ω => (tailSup_mem hbd hfD k ω).1)
    have h3 := condExp_sub (m := m) (hFi k) hfi
    have h4 := abs_condExp_ae_le_condExp_abs (m := m) (μ := μ) (F k - f)
    have h5 := condExp_mono (m := m) ((hFi k).sub hfi).abs (hgi k)
      (Eventually.of_forall fun ω => by
        have := le_tailSup hbd hfD k 0 ω
        rw [add_zero] at this
        exact this)
    filter_upwards [h1, h2, h3, h4, h5] with ω e1 e2 e3 e4 e5
    refine ⟨e1, e2, ?_⟩
    have e3' : μ[F k - f | m] ω = μ[F k | m] ω - μ[f | m] ω := by rw [e3]; rfl
    rw [← e3']
    exact e4.trans e5
  have hcm : ∀ k, Measurable (c k) := fun k => (stronglyMeasurable_condExp.mono hm).measurable
  have hhm : Measurable fun ω => ⨅ k, c k ω := Measurable.iInf hcm
  have hbdd : ∀ᵐ ω ∂μ, BddBelow (Set.range fun k => c k ω) := by
    filter_upwards [hae] with ω h
    exact ⟨0, by rintro _ ⟨j, rfl⟩; exact (h j).2.1⟩
  have hh0 : ∀ᵐ ω ∂μ, 0 ≤ ⨅ k, c k ω := by
    filter_upwards [hae] with ω h
    exact le_ciInf fun k => (h k).2.1
  have hhle : ∀ k, ∀ᵐ ω ∂μ, (⨅ j, c j ω) ≤ c k ω := fun k => by
    filter_upwards [hbdd] with ω h
    exact ciInf_le h k
  have hhi : Integrable (fun ω => ⨅ k, c k ω) μ :=
    integrable_condExp.mono' hhm.aestronglyMeasurable (by
      filter_upwards [hh0, hhle 0] with ω h1 h2
      rw [Real.norm_eq_abs, abs_of_nonneg h1]
      exact h2)
  have hint0 : ∫ ω, (⨅ k, c k ω) ∂μ ≤ 0 := by
    refine ge_of_tendsto hint (Eventually.of_forall fun k => ?_)
    calc ∫ ω, (⨅ j, c j ω) ∂μ ≤ ∫ ω, c k ω ∂μ := integral_mono_ae hhi integrable_condExp (hhle k)
      _ = ∫ ω, tailSup F f k ω ∂μ := integral_condExp hm
  have hz : (fun ω => ⨅ k, c k ω) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hh0 hhi).1
      (le_antisymm hint0 (integral_nonneg_of_ae hh0))
  filter_upwards [hae, hz, hbdd] with ω h hzω hb
  have hanti : Antitone fun k => c k ω := antitone_nat_of_succ_le fun k => (h k).1
  have hcl : Tendsto (fun k => c k ω) atTop (𝓝 0) := by
    have := tendsto_atTop_ciInf hanti hb
    rwa [show (⨅ k, c k ω) = 0 from hzω] at this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun k => norm_nonneg _) (fun k => by
    rw [Real.norm_eq_abs]; exact (h k).2.2) hcl

/-! ## Measurable suprema of paths -/

/-- Cochrane (2023), A1 §1.6, p. 567 (tool for (1.32)): **the measurable supremum of a path**,
`sup_{q ∈ D}|X_q(ω)|` over the countable set `D = denseSet s t`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7CondDominated.pathSup). -/
noncomputable def pathSup (s t : ℝ) (X : ℝ → Ω → ℝ) (ω : Ω) : ℝ :=
  ⨆ q : denseSet s t, |X q ω|

/-- Cochrane (2023), A1 §1.6, p. 567: `pathSup ≥ 0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7CondDominated.pathSup_nonneg). -/
theorem pathSup_nonneg (s t : ℝ) (X : ℝ → Ω → ℝ) (ω : Ω) : 0 ≤ pathSup s t X ω :=
  Real.iSup_nonneg fun _ => abs_nonneg _

/-- **Cochrane (2023), A1 §1.6, p. 567: the path supremum is measurable** if every `X_u`,
`u ∈ [s, t]`, is.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7CondDominated.measurable_pathSup). -/
theorem measurable_pathSup {s t : ℝ} {X : ℝ → Ω → ℝ}
    (hX : ∀ u ∈ Set.Icc s t, Measurable (X u)) : Measurable (pathSup s t X) := by
  have := (countable_denseSet s t).to_subtype
  exact Measurable.iSup fun q => continuous_abs.measurable.comp (hX q q.2.1)

/-- **Cochrane (2023), A1 §1.6, p. 567: the path supremum bounds the path on `[s, t]`** when the
path is right-continuous on `[s, t]` (within `[x, t]` at each `x`) and bounded there.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7CondDominated.abs_le_pathSup_of_right). -/
theorem abs_le_pathSup_of_right {s t : ℝ} {X : ℝ → Ω → ℝ} {ω : Ω}
    (hr : ∀ x ∈ Set.Icc s t, ContinuousWithinAt (fun u => X u ω) (Set.Icc x t) x)
    {C : ℝ} (hC : ∀ x ∈ Set.Icc s t, |X x ω| ≤ C) {u : ℝ} (hu : u ∈ Set.Icc s t) :
    |X u ω| ≤ pathSup s t X ω := by
  have hbdd : BddAbove (Set.range fun q : denseSet s t => |X q ω|) :=
    ⟨C, by rintro _ ⟨q, rfl⟩; exact hC q q.2.1⟩
  have ht : Tendsto (fun k => |X (pushRight t k u) ω|) atTop (𝓝 |X u ω|) :=
    ((hr u hu).tendsto.comp (tendsto_pushRight hu)).abs
  exact le_of_tendsto' ht fun k => le_ciSup hbdd ⟨pushRight t k u, (pushRight_mem hu k).2⟩

/-- Cochrane (2023), A1 §1.6, p. 567: the path supremum bounds a càdlàg path on `[s, t]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7CondDominated.abs_le_pathSup_of_isCadlag). -/
theorem abs_le_pathSup_of_isCadlag {s t : ℝ} {X : ℝ → Ω → ℝ} {ω : Ω}
    (hX : IsCadlag fun u => X u ω) {u : ℝ} (hu : u ∈ Set.Icc s t) :
    |X u ω| ≤ pathSup s t X ω := by
  obtain ⟨C, -, hC⟩ := exists_bound_of_isCadlag hX s t
  exact abs_le_pathSup_of_right (fun x _ =>
    (continuousWithinAt_Ioi_iff_Ici.1 (hX.isRightContinuous x)).mono Set.Icc_subset_Ici_self)
    hC hu

/-- Cochrane (2023), A1 §1.6, p. 567: the path supremum bounds a path continuous on `[s, t]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7CondDominated.abs_le_pathSup_of_continuousOn). -/
theorem abs_le_pathSup_of_continuousOn {s t : ℝ} {X : ℝ → Ω → ℝ} {ω : Ω}
    (hX : ContinuousOn (fun u => X u ω) (Set.Icc s t)) {u : ℝ} (hu : u ∈ Set.Icc s t) :
    |X u ω| ≤ pathSup s t X ω := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hX
  exact abs_le_pathSup_of_right (fun x hx => (hX x hx).mono (Set.Icc_subset_Icc_left hx.1))
    (fun x hx => by rw [← Real.norm_eq_abs]; exact hC x hx) hu

/-! ## Sequences of partitions -/

/-- Cochrane (2023), A1 §1.6, p. 567: the partition of the degenerate interval `[s, s]`
(`n = 0`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7CondDominated.pointPartition). -/
def pointPartition (s : ℝ) : Partition s s where
  n := 0
  t := fun i => s + i
  strictMono := fun i j h => by
    have : (i : ℝ) < j := Nat.cast_lt.2 h
    simp only
    linarith
  first := by simp
  last := by simp

/-- Cochrane (2023), A1 §1.6, p. 567: the mesh of `pointPartition s` is `0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7CondDominated.mesh_pointPartition). -/
theorem mesh_pointPartition (s : ℝ) : mesh (pointPartition s) = 0 := by
  have : IsEmpty (Fin (pointPartition s).n) := by simp only [pointPartition]; infer_instance
  exact Real.iSup_of_isEmpty _

/-- Cochrane (2023), A1 §1.6, p. 567: **for `s ≤ t` there is a sequence of partitions of
`[s, t]` with mesh `→ 0`**.
Generalises `TidyR7StieltjesSums.dyadic` and `TidyR7StieltjesSums.tendsto_mesh_dyadic`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7CondDominated.exists_partition_seq). -/
theorem exists_partition_seq {s t : ℝ} (hst : s ≤ t) :
    ∃ P : ℕ → Partition s t, Tendsto (fun k => mesh (P k)) atTop (𝓝 0) := by
  rcases hst.lt_or_eq with h | rfl
  · exact ⟨dyadic h, tendsto_mesh_dyadic h⟩
  · exact ⟨fun _ => pointPartition s, by simp only [mesh_pointPartition]; exact tendsto_const_nhds⟩

end Cochrane.LongTermDebtDynamics.TidyR7CondDominated
