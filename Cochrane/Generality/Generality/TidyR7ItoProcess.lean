/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.TidyR7ItoProducts

/-!
# Itô processes `X_u = X_s + ∫_s^u a dr + ∫_s^u H dW`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for (1.32) with diffusive
bonds (chunk I5d): bonds `B` and the deflated price `Λ/P` of (1.32) are, in the diffusive case,
"bounded-variation drift + `∫ · dW`". This module sets up such processes and the tools for the
product rule (TidyR7ItoCovariation, TidyR7ItoProductRule).

## Setting

`ItoProcess P 𝓕 W X a H s t Ca CH`: `X` is adapted on `[s, t]`, `X_s` is square integrable (it
need not be bounded: `X = W` has `X_s = W_s`), the drift `a` and the diffusion coefficient `H`
are bounded admissible integrands (`TidyR7ItoIntegral.ItoIntegrand`: adapted, bounded, a.s.
continuous), and for every `u ∈ [s, t]`, almost surely,
`X_u = X_s + ∫_s^u a_r dr + ∫_s^u H dW` (pathwise Lebesgue drift integral; Itô integral
`TidyR7ItoIntegral.itoInt`). `X` itself is a given process (for instance `W`); nothing about its
paths is assumed. The statements needed later are at fixed times, so no continuous version is
required: everything is done with `itoInt` at partition points.

## Main results

* `ItoProcess.memLp`, `ItoProcess.incr_eq` (`X_v − X_u = ∫_u^v a + ∫_u^v H dW` a.s.),
  `ItoProcess.incr_decomp` (`= ∫_u^v a + H_u(W_v − W_u) + ∫_u^v (H − H_u) dW`),
  `ItoProcess.integral_incr_sq_le` (`E[(X_v − X_u)²] ≤ 2C_a²(v − u)² + 2C_H²(v − u)`),
  `ItoProcess.toMS` (**an Itô process is a mean-square continuous integrand**, so
  `TidyR7ItoUnbounded` integrates it; this is the unbounded class needed for `∫ X dY`).
* `driftErr`, `eventually_integral_sq_mul_driftErr_le`: the error
  `D_i = ∫_{t_i}^{t_{i+1}} b − b_{t_i}Δt_i` of the left-point rule satisfies
  `E[X_{t_i}² D_i²] ≤ εΔt_i²` uniformly in `i` once the mesh is small.
* Generic `L²`/`L¹` tools: `integral_sum_sq_of_orth` (Pythagoras for martingale-difference sums
  with square-integrable past), `sq_integral_abs_sum_mul_le`
  (`(E|Σ f_ig_i|)² ≤ Σ E f_i² · Σ E g_i²`), `sq_integral_abs_le`.
-/

namespace Cochrane.Generality.TidyR7ItoProcess

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Generality.TidyR7StieltjesSums Cochrane.Generality.TidyR7BrownianTools
  Cochrane.Generality.TidyR7BrownianQV Cochrane.Generality.TidyR7ItoL2
  Cochrane.Generality.TidyR7ItoSums Cochrane.Generality.TidyR7ItoIntegral
  Cochrane.Generality.TidyR7ItoUnbounded Cochrane.Generality.TidyR7ItoProducts
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → ℝ}

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `(x + y)² ≤ 2x² + 2y²`.
Restates `TidyR7ItoL2.sq_sub_le_two_mul` up to substitution.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProcess.add_sq_le_two). -/
lemma add_sq_le_two (x y : ℝ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

/-! ## Generic `L²` tools -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: Pythagoras for martingale differences.** Let
`c` be monotone, `V_i` square integrable and `𝓕_{c_{i+1}}`-strongly measurable, and orthogonal
to every square-integrable `𝓕_{c_i}`-measurable `Z`. Then `E[(Σ_{i<n} V_i)²] = Σ_{i<n} E[V_i²]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProcess.integral_sum_sq_of_orth). -/
theorem integral_sum_sq_of_orth {c : ℕ → ℝ} (hc : Monotone c) {V : ℕ → Ω → ℝ} (n : ℕ)
    (hV2 : ∀ i < n, MemLp (V i) 2 P) (hVm : ∀ i < n, StronglyMeasurable[𝓕 (c (i + 1))] (V i))
    (horth : ∀ i < n, ∀ Z : Ω → ℝ, StronglyMeasurable[𝓕 (c i)] Z → MemLp Z 2 P →
      ∫ ω, Z ω * V i ω ∂P = 0) :
    ∫ ω, (∑ i ∈ Finset.range n, V i ω) ^ 2 ∂P = ∑ i ∈ Finset.range n, ∫ ω, V i ω ^ 2 ∂P := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hS2 : MemLp (fun ω => ∑ i ∈ Finset.range n, V i ω) 2 P :=
      memLp_finsetSum _ fun i hi => hV2 i (by have := Finset.mem_range.1 hi; omega)
    have hSm : StronglyMeasurable[𝓕 (c n)] (fun ω => ∑ i ∈ Finset.range n, V i ω) :=
      Finset.stronglyMeasurable_fun_sum _ fun i hi =>
        (hVm i (by have := Finset.mem_range.1 hi; omega)).mono
          (𝓕.mono (hc (by have := Finset.mem_range.1 hi; omega)))
    have hVn := hV2 n (Nat.lt_succ_self n)
    have h0 := horth n (Nat.lt_succ_self n) _ hSm hS2
    have e : (fun ω => (∑ i ∈ Finset.range (n + 1), V i ω) ^ 2) = fun ω =>
        (∑ i ∈ Finset.range n, V i ω) ^ 2 + 2 * ((∑ i ∈ Finset.range n, V i ω) * V n ω)
          + V n ω ^ 2 := by
      funext ω
      rw [Finset.sum_range_succ]
      ring
    have j2 : Integrable (fun ω => 2 * ((∑ i ∈ Finset.range n, V i ω) * V n ω)) P :=
      (hS2.integrable_mul hVn).const_mul 2
    rw [e, integral_add (f := fun ω => (∑ i ∈ Finset.range n, V i ω) ^ 2
        + 2 * ((∑ i ∈ Finset.range n, V i ω) * V n ω)) (g := fun ω => V n ω ^ 2)
        (hS2.integrable_sq.add j2) hVn.integrable_sq,
      integral_add (f := fun ω => (∑ i ∈ Finset.range n, V i ω) ^ 2)
        (g := fun ω => 2 * ((∑ i ∈ Finset.range n, V i ω) * V n ω)) hS2.integrable_sq j2,
      integral_const_mul, h0,
      ih (fun i hi => hV2 i (by omega)) (fun i hi => hVm i (by omega))
        (fun i hi => horth i (by omega)), Finset.sum_range_succ]
    ring

/-- Cochrane (2023), A1 §1.6, pp. 567–568: on a probability space, `(E|f|)² ≤ E[f²]`
(Cauchy–Schwarz against `1`).
The `b = 1` case of `TidyR7ItoL2.sq_integral_mul_le`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProcess.sq_integral_abs_le). -/
theorem sq_integral_abs_le [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : MemLp f 2 P) :
    (∫ ω, |f ω| ∂P) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂P := by
  have h := sq_integral_mul_le hf.abs (memLp_const (1 : ℝ) (μ := P) (p := 2))
  simpa [sq_abs] using h

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: Cauchy–Schwarz for sums of products**,
`(E|Σ_{i<n} f_ig_i|)² ≤ (Σ E f_i²)(Σ E g_i²)` for square-integrable `f_i, g_i`.
Generalises `TidyR7ItoL2.sq_integral_mul_le`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProcess.sq_integral_abs_sum_mul_le). -/
theorem sq_integral_abs_sum_mul_le {n : ℕ} {f g : ℕ → Ω → ℝ} (hf : ∀ i < n, MemLp (f i) 2 P)
    (hg : ∀ i < n, MemLp (g i) 2 P) :
    (∫ ω, |∑ i ∈ Finset.range n, f i ω * g i ω| ∂P) ^ 2
      ≤ (∑ i ∈ Finset.range n, ∫ ω, f i ω ^ 2 ∂P) * ∑ i ∈ Finset.range n, ∫ ω, g i ω ^ 2 ∂P := by
  have hi : ∀ i ∈ Finset.range n, Integrable (fun ω => |f i ω * g i ω|) P := fun i hi =>
    ((hf i (Finset.mem_range.1 hi)).integrable_mul (hg i (Finset.mem_range.1 hi))).abs
  have h1 : ∫ ω, |∑ i ∈ Finset.range n, f i ω * g i ω| ∂P
      ≤ ∑ i ∈ Finset.range n, ∫ ω, |f i ω * g i ω| ∂P := by
    rw [← integral_finsetSum _ hi]
    refine integral_mono (integrable_finsetSum _ fun i hi' =>
      (hf i (Finset.mem_range.1 hi')).integrable_mul (hg i (Finset.mem_range.1 hi'))).abs
      (integrable_finsetSum _ hi) fun ω => Finset.abs_sum_le_sum_abs _ _
  have h2 : (∑ i ∈ Finset.range n, ∫ ω, |f i ω * g i ω| ∂P) ^ 2
      ≤ (∑ i ∈ Finset.range n, ∫ ω, f i ω ^ 2 ∂P) * ∑ i ∈ Finset.range n, ∫ ω, g i ω ^ 2 ∂P := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
      (fun i _ => integral_nonneg fun _ => sq_nonneg _)
      (fun i _ => integral_nonneg fun _ => sq_nonneg _) fun i hi' => ?_
    have h := sq_integral_mul_le (hf i (Finset.mem_range.1 hi')).abs
      (hg i (Finset.mem_range.1 hi')).abs
    simpa [sq_abs, abs_mul] using h
  exact (pow_le_pow_left₀ (integral_nonneg fun _ => abs_nonneg _) h1 2).trans h2

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: products of a vanishing and a bounded family.** If
`Σ_i E[(f^k_i)²] → 0` and `Σ_i E[(g^k_i)²] ≤ B` for all `k`, then `E|Σ_i f^k_ig^k_i| → 0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProcess.tendsto_integral_abs_sum_mul). -/
theorem tendsto_integral_abs_sum_mul {n : ℕ → ℕ} {f g : ℕ → ℕ → Ω → ℝ}
    (hf : ∀ k, ∀ i < n k, MemLp (f k i) 2 P) (hg : ∀ k, ∀ i < n k, MemLp (g k i) 2 P)
    (hf0 : Tendsto (fun k => ∑ i ∈ Finset.range (n k), ∫ ω, f k i ω ^ 2 ∂P) atTop (𝓝 0))
    {B : ℝ} (hgB : ∀ k, ∑ i ∈ Finset.range (n k), ∫ ω, g k i ω ^ 2 ∂P ≤ B) :
    Tendsto (fun k => ∫ ω, |∑ i ∈ Finset.range (n k), f k i ω * g k i ω| ∂P) atTop (𝓝 0) := by
  refine tendsto_zero_of_sq_le (c := B) (fun k => ?_) hf0
  refine (sq_integral_abs_sum_mul_le (hf k) (hg k)).trans ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (hgB k)
    (Finset.sum_nonneg fun i _ => integral_nonneg fun _ => sq_nonneg _)

/-! ## Drift integrals -/

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `|∫_c^d a_r dr| ≤ C(d − c)` for `|a| ≤ C` on
`[s, t] ⊇ [c, d]`.
Pathwise Mathlib `intervalIntegral.norm_integral_le_of_norm_le_const`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProcess.abs_integral_drift_le). -/
theorem abs_integral_drift_le {a : ℝ → Ω → ℝ} {s t C : ℝ}
    (hab : ∀ u ∈ Set.Icc s t, ∀ ω, |a u ω| ≤ C) {c d : ℝ} (hsc : s ≤ c) (hcd : c ≤ d)
    (hdt : d ≤ t) (ω : Ω) : |∫ r in c..d, a r ω| ≤ C * (d - c) := by
  rw [← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := C) fun r hr => ?_).trans_eq ?_
  · rw [Set.uIoc_of_le hcd] at hr
    rw [Real.norm_eq_abs]
    exact hab r ⟨hsc.trans hr.1.le, hr.2.trans hdt⟩ ω
  · rw [abs_of_nonneg (sub_nonneg.2 hcd)]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: for a bounded admissible drift on `[s, t]` and
`s ≤ c ≤ d ≤ t`, `ω ↦ ∫_c^d a_r(ω) dr` is a.e. strongly measurable (an a.s. limit of measurable
Riemann sums).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProcess.aestronglyMeasurable_integral_drift). -/
theorem aestronglyMeasurable_integral_drift {a : ℝ → Ω → ℝ} {s t C : ℝ}
    (ha : ItoIntegrand P 𝓕 a s t C) {c d : ℝ} (hsc : s ≤ c) (hcd : c ≤ d) (hdt : d ≤ t) :
    AEStronglyMeasurable (fun ω => ∫ r in c..d, a r ω) P := by
  rcases hcd.lt_or_eq with hcd | hcd
  · refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun k ω =>
      riemannSum (dyadic hcd k) (fun u => a u ω)) (fun k => ?_) ?_
    · have hm : Measurable fun ω => riemannSum (dyadic hcd k) (fun u => a u ω) := by
        simp only [riemannSum]
        exact Finset.measurable_sum _ fun i hi => (ha.measurable
          ⟨hsc.trans (t_mem _ (Finset.mem_range.1 hi).le).1,
            (t_mem _ (Finset.mem_range.1 hi).le).2.trans hdt⟩).mul_const _
      exact hm.aestronglyMeasurable
    · filter_upwards [ha.cont] with ω hω
      exact tendsto_riemannSum (hω.mono (Set.Icc_subset_Icc hsc hdt)) _ (tendsto_mesh_dyadic hcd)
  · subst hcd
    simp only [intervalIntegral.integral_same]
    exact aestronglyMeasurable_const

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the drift integral over `[c, d] ⊆ [s, t]` is square
integrable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProcess.memLp_integral_drift). -/
theorem memLp_integral_drift [IsFiniteMeasure P] {a : ℝ → Ω → ℝ} {s t C : ℝ}
    (ha : ItoIntegrand P 𝓕 a s t C) {c d : ℝ} (hsc : s ≤ c) (hcd : c ≤ d) (hdt : d ≤ t) :
    MemLp (fun ω => ∫ r in c..d, a r ω) 2 P :=
  MemLp.of_bound (aestronglyMeasurable_integral_drift ha hsc hcd hdt) (C * (d - c))
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]
      exact abs_integral_drift_le ha.bound hsc hcd hdt ω)

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (the left-point error of the drift):
`D = ∫_u^v b_r dr − b_u(v − u)`.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7ItoProcess.driftErr). -/
noncomputable def driftErr (b : ℝ → Ω → ℝ) (u v : ℝ) (ω : Ω) : ℝ :=
  (∫ r in u..v, b r ω) - b u ω * (v - u)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: if a path oscillates by at most `η` on `(u, v]` from
its value at `u`, the left-point error is at most `η(v − u)`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProcess.abs_integral_sub_le). -/
theorem abs_integral_sub_le {f : ℝ → ℝ} {u v η : ℝ} (huv : u ≤ v)
    (hf : IntervalIntegrable f MeasureSpace.volume u v)
    (hη : ∀ r ∈ Set.Ioc u v, |f r - f u| ≤ η) :
    |(∫ r in u..v, f r) - f u * (v - u)| ≤ η * (v - u) := by
  have e : (∫ r in u..v, f r) - f u * (v - u) = ∫ r in u..v, (f r - f u) := by
    rw [intervalIntegral.integral_sub hf intervalIntegrable_const, intervalIntegral.integral_const,
      smul_eq_mul, mul_comm]
  rw [e, ← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := η) fun r hr => ?_).trans_eq ?_
  · rw [Set.uIoc_of_le huv] at hr
    rw [Real.norm_eq_abs]
    exact hη r hr
  · rw [abs_of_nonneg (sub_nonneg.2 huv)]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `|D| ≤ 2C(v − u)` for `|b| ≤ C` on `[s, t] ⊇ [u, v]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProcess.abs_driftErr_le). -/
theorem abs_driftErr_le {b : ℝ → Ω → ℝ} {s t C : ℝ}
    (hbb : ∀ u ∈ Set.Icc s t, ∀ ω, |b u ω| ≤ C) {u v : ℝ} (hsu : s ≤ u) (huv : u ≤ v)
    (hvt : v ≤ t) (ω : Ω) : |driftErr b u v ω| ≤ 2 * C * (v - u) := by
  have h1 := abs_integral_drift_le hbb hsu huv hvt ω
  have h2 : |b u ω * (v - u)| ≤ C * (v - u) := by
    rw [abs_mul, abs_of_nonneg (sub_nonneg.2 huv)]
    exact mul_le_mul_of_nonneg_right (hbb u ⟨hsu, huv.trans hvt⟩ ω) (sub_nonneg.2 huv)
  unfold driftErr
  calc |(∫ r in u..v, b r ω) - b u ω * (v - u)|
      ≤ |∫ r in u..v, b r ω| + |b u ω * (v - u)| := abs_sub _ _
    _ ≤ 2 * C * (v - u) := by linarith

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the left-point error of the drift is a.e. strongly
measurable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProcess.aestronglyMeasurable_driftErr). -/
theorem aestronglyMeasurable_driftErr {b : ℝ → Ω → ℝ} {s t C : ℝ}
    (hb : ItoIntegrand P 𝓕 b s t C) {u v : ℝ} (hsu : s ≤ u) (huv : u ≤ v) (hvt : v ≤ t) :
    AEStronglyMeasurable (driftErr b u v) P :=
  (aestronglyMeasurable_integral_drift hb hsu huv hvt).sub
    ((hb.measurable ⟨hsu, huv.trans hvt⟩).mul_const _).aestronglyMeasurable

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the drift error is uniformly small against an
unbounded weight.** For `X` square integrable and uniformly mean-square continuous on `[s, t]`,
a bounded admissible drift `b`, and partitions with mesh `→ 0`: for every `ε > 0`, eventually
`E[X_{t_i}² D_i²] ≤ ε(t_{i+1} − t_i)²` for all cells `i` (a bad sequence of cells has a
convergent subsequence of left ends; `TidyR7ItoProducts.tendsto_integral_sq_mul_sq` along it,
with `Z = D_i/Δt_i → 0` a.s. by uniform continuity of the paths of `b`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProcess.eventually_integral_sq_mul_driftErr_le). -/
theorem eventually_integral_sq_mul_driftErr_le [IsFiniteMeasure P] {s t : ℝ} {X b : ℝ → Ω → ℝ}
    (hX2 : ∀ u ∈ Set.Icc s t, MemLp (X u) 2 P) (hXc : MSUnifCont P X s t) {Cb : ℝ}
    (hb : ItoIntegrand P 𝓕 b s t Cb) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ i < (ps k).n, ∫ ω, X ((ps k).t i) ω ^ 2 *
      driftErr b ((ps k).t i) ((ps k).t (i + 1)) ω ^ 2 ∂P
        ≤ ε * ((ps k).t (i + 1) - (ps k).t i) ^ 2 := by
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hcon
  push Not at hbad
  choose i hi hlt using hbad
  set p : ℕ → Partition s t := fun j => ps (φ j) with hp
  have hmem : ∀ j, (p j).t (i j) ∈ Set.Icc s t := fun j => t_mem (p j) (hi j).le
  have hmem' : ∀ j, (p j).t (i j + 1) ∈ Set.Icc s t := fun j => t_mem (p j) (hi j)
  have hΔ : ∀ j, 0 < (p j).t (i j + 1) - (p j).t (i j) := fun j => step_pos (p j) (i j)
  obtain ⟨a, ha, ψ, hψ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
  set Z : ℕ → Ω → ℝ := fun j ω => driftErr b ((p (ψ j)).t (i (ψ j)))
    ((p (ψ j)).t (i (ψ j) + 1)) ω / ((p (ψ j)).t (i (ψ j) + 1) - (p (ψ j)).t (i (ψ j)))
    with hZ
  have hZm : ∀ j, AEStronglyMeasurable (Z j) P := fun j =>
    ((aestronglyMeasurable_driftErr hb (hmem (ψ j)).1
      ((p (ψ j)).strictMono.monotone (Nat.le_succ _)) (hmem' (ψ j)).2).mul_const
        ((p (ψ j)).t (i (ψ j) + 1) - (p (ψ j)).t (i (ψ j)))⁻¹).congr
      (ae_of_all _ fun ω => (div_eq_mul_inv _ _).symm)
  have hZb : ∀ j ω, |Z j ω| ≤ 2 * Cb := by
    intro j ω
    rw [hZ, abs_div, abs_of_pos (hΔ (ψ j)), div_le_iff₀ (hΔ (ψ j))]
    exact abs_driftErr_le hb.bound (hmem (ψ j)).1
      ((p (ψ j)).strictMono.monotone (Nat.le_succ _)) (hmem' (ψ j)).2 ω
  have hmesh : Tendsto (fun j => mesh (p (ψ j))) atTop (𝓝 0) :=
    (hps.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop
  have hZ0 : ∀ᵐ ω ∂P, Tendsto (fun j => Z j ω) atTop (𝓝 0) := by
    filter_upwards [hb.cont] with ω hω
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨δ, hδ, hδb⟩ := Metric.uniformContinuousOn_iff.1
      (isCompact_Icc.uniformContinuousOn_of_continuous hω) (η / 2) (by positivity)
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hmesh.eventually (gt_mem_nhds hδ))
    refine ⟨N, fun j hj => ?_⟩
    have hj' := hN j hj
    have hΔj := hΔ (ψ j)
    have hint : IntervalIntegrable (fun r => b r ω) MeasureSpace.volume
        ((p (ψ j)).t (i (ψ j))) ((p (ψ j)).t (i (ψ j) + 1)) :=
      (hω.mono (Set.uIcc_subset_Icc (hmem (ψ j)) (hmem' (ψ j)))).intervalIntegrable
    have hosc : ∀ r ∈ Set.Ioc ((p (ψ j)).t (i (ψ j))) ((p (ψ j)).t (i (ψ j) + 1)),
        |b r ω - b ((p (ψ j)).t (i (ψ j))) ω| ≤ η / 2 := by
      intro r hr
      have hrm : r ∈ Set.Icc s t := ⟨(hmem (ψ j)).1.trans hr.1.le, hr.2.trans (hmem' (ψ j)).2⟩
      have hd : dist r ((p (ψ j)).t (i (ψ j))) < δ := by
        rw [Real.dist_eq, abs_of_pos (sub_pos.2 hr.1)]
        exact ((sub_le_sub_right hr.2 _).trans (le_mesh _ (hi (ψ j)))).trans_lt hj'
      have := hδb r hrm _ (hmem (ψ j)) hd
      rw [Real.dist_eq] at this
      exact this.le
    have hD := abs_integral_sub_le ((p (ψ j)).strictMono.monotone (Nat.le_succ _)) hint hosc
    rw [Real.dist_eq, sub_zero, hZ]
    simp only
    rw [abs_div, abs_of_pos hΔj, div_lt_iff₀ hΔj]
    unfold driftErr
    nlinarith
  have hT := tendsto_integral_sq_mul_sq hX2 hXc (fun j => hmem (ψ j)) ha hlim hZm hZb hZ0
  have hgt : ∀ j, ε < ∫ ω, X ((p (ψ j)).t (i (ψ j))) ω ^ 2 * Z j ω ^ 2 ∂P := by
    intro j
    have h := hlt (ψ j)
    have hΔ2 : 0 < ((p (ψ j)).t (i (ψ j) + 1) - (p (ψ j)).t (i (ψ j))) ^ 2 :=
      pow_pos (hΔ (ψ j)) 2
    have e : ∫ ω, X ((p (ψ j)).t (i (ψ j))) ω ^ 2 * driftErr b ((p (ψ j)).t (i (ψ j)))
        ((p (ψ j)).t (i (ψ j) + 1)) ω ^ 2 ∂P
        = ((p (ψ j)).t (i (ψ j) + 1) - (p (ψ j)).t (i (ψ j))) ^ 2 *
          ∫ ω, X ((p (ψ j)).t (i (ψ j))) ω ^ 2 * Z j ω ^ 2 ∂P := by
      have hne : (p (ψ j)).t (i (ψ j) + 1) - (p (ψ j)).t (i (ψ j)) ≠ 0 := (hΔ (ψ j)).ne'
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      simp only [hZ, div_pow]
      field_simp
    rw [e] at h
    nlinarith
  have := ge_of_tendsto hT (Eventually.of_forall fun j => (hgt j).le)
  linarith

/-! ## Itô processes -/

variable (P 𝓕 W) (X a H : ℝ → Ω → ℝ) (s t Ca CH : ℝ)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: an Itô process on `[s, t]`** (bonds `B` and the
deflated price `Λ/P` in (1.32) with diffusive bonds): `X` adapted, `X_s` square integrable,
`a`, `H` bounded admissible integrands, and `X_u = X_s + ∫_s^u a dr + ∫_s^u H dW` a.s. for each
`u ∈ [s, t]`.
Restated from the Cochrane Monetarism project (Cochrane.Monetarism.TidyR7ItoProcess.ItoProcess). -/
structure ItoProcess where
  adapted : ∀ u ∈ Set.Icc s t, StronglyMeasurable[𝓕 u] (X u)
  init : MemLp (X s) 2 P
  drift : ItoIntegrand P 𝓕 a s t Ca
  diff : ItoIntegrand P 𝓕 H s t CH
  eq : ∀ u ∈ Set.Icc s t, X u =ᵐ[P] fun ω => X s ω + (∫ r in s..u, a r ω) + itoInt P 𝓕 W H s u ω

variable {P 𝓕 W X a H s t Ca CH}

/-- Cochrane (2023), A1 §1.6, pp. 567–568: an Itô process is square integrable at each time.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProcess.ItoProcess.memLp). -/
theorem ItoProcess.memLp (hX : ItoProcess P 𝓕 W X a H s t Ca CH) (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {u : ℝ}
    (hu : u ∈ Set.Icc s t) : MemLp (X u) 2 P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h0 : MemLp (fun ω => X s ω + (∫ r in s..u, a r ω) + itoInt P 𝓕 W H s u ω) 2 P :=
    (hX.init.add (memLp_integral_drift hX.drift le_rfl hu.1 hu.2)).add
      (memLp_itoInt hB hW h𝓕 hs (hX.diff.mono le_rfl hu.2))
  exact h0.ae_eq (hX.eq u hu).symm

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: increments of an Itô process**,
`X_v − X_u = ∫_u^v a dr + ∫_u^v H dW` a.s. for `s ≤ u ≤ v ≤ t`, `0 ≤ s`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProcess.ItoProcess.incr_eq). -/
theorem ItoProcess.incr_eq (hX : ItoProcess P 𝓕 W X a H s t Ca CH) (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) {u v : ℝ}
    (hsu : s ≤ u) (huv : u ≤ v) (hvt : v ≤ t) :
    (fun ω => X v ω - X u ω) =ᵐ[P] fun ω => (∫ r in u..v, a r ω) + itoInt P 𝓕 W H u v ω := by
  have hu : u ∈ Set.Icc s t := ⟨hsu, huv.trans hvt⟩
  have hv : v ∈ Set.Icc s t := ⟨hsu.trans huv, hvt⟩
  filter_upwards [hX.eq u hu, hX.eq v hv,
    itoInt_add_itoInt hB hW h𝓕 hs hsu huv (hX.diff.mono le_rfl hvt), hX.drift.cont]
    with ω h1 h2 h3 h4
  have hst : s ≤ t := hsu.trans (huv.trans hvt)
  have i1 : IntervalIntegrable (fun r => a r ω) MeasureSpace.volume s v :=
    (h4.mono (Set.uIcc_subset_Icc ⟨le_rfl, hst⟩ hv)).intervalIntegrable
  have i2 : IntervalIntegrable (fun r => a r ω) MeasureSpace.volume s u :=
    (h4.mono (Set.uIcc_subset_Icc ⟨le_rfl, hst⟩ hu)).intervalIntegrable
  have hsub := intervalIntegral.integral_interval_sub_left i1 i2
  rw [h1, h2, h3]
  linarith

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `H − H_u` is a bounded admissible integrand on
`[u, v]` when `H` is (bound `2C`).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProcess.itoIntegrand_sub_left). -/
theorem itoIntegrand_sub_left {K : ℝ → Ω → ℝ} {u v C : ℝ} (huv : u ≤ v)
    (hK : ItoIntegrand P 𝓕 K u v C) :
    ItoIntegrand P 𝓕 (fun r ω => K r ω - K u ω) u v (2 * C) where
  adapted r hr := (hK.adapted r hr).sub ((hK.adapted u ⟨le_rfl, huv⟩).mono (𝓕.mono hr.1))
  bound r hr ω := by
    rw [two_mul]
    exact (abs_sub _ _).trans (add_le_add (hK.bound r hr ω) (hK.bound u ⟨le_rfl, huv⟩ ω))
  cont := by
    filter_upwards [hK.cont] with ω hω
    exact hω.sub continuousOn_const

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the one-cell decomposition**: for
`s ≤ u ≤ v ≤ t`, a.s.
`X_v − X_u = ∫_u^v a dr + H_u(W_v − W_u) + ∫_u^v (H − H_u) dW`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProcess.ItoProcess.incr_decomp). -/
theorem ItoProcess.incr_decomp (hX : ItoProcess P 𝓕 W X a H s t Ca CH)
    (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕)
    (hs : 0 ≤ s) {u v : ℝ} (hsu : s ≤ u) (huv : u ≤ v) (hvt : v ≤ t) :
    (fun ω => X v ω - X u ω) =ᵐ[P] fun ω => (∫ r in u..v, a r ω)
      + (H u ω * incr W u v ω + itoInt P 𝓕 W (fun r ω => H r ω - H u ω) u v ω) := by
  have hHuv : ItoIntegrand P 𝓕 H u v CH := hX.diff.mono hsu hvt
  have hc : ItoIntegrand P 𝓕 (fun _ => H u) u v CH :=
    itoIntegrand_const (hHuv.adapted u ⟨le_rfl, huv⟩) (hHuv.bound u ⟨le_rfl, huv⟩)
  have e : H = fun r ω => (fun _ => H u) r ω + (fun r ω => H r ω - H u ω) r ω := by
    funext r ω
    simp
  have hadd := itoInt_add hB hW h𝓕 (hs.trans hsu) hc (itoIntegrand_sub_left huv hHuv)
  rw [← e] at hadd
  filter_upwards [hX.incr_eq hB hW h𝓕 hs hsu huv hvt, hadd,
    itoInt_const hB hW h𝓕 (hs.trans hsu) huv (hHuv.adapted u ⟨le_rfl, huv⟩)
      (hHuv.bound u ⟨le_rfl, huv⟩)] with ω h1 h2 h3
  rw [h1, h2, h3]

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: the mean-square modulus of an Itô process**,
`E[(X_v − X_u)²] ≤ 2C_a²(v − u)² + 2C_H²(v − u)` for `s ≤ u ≤ v ≤ t`, `0 ≤ s`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProcess.ItoProcess.integral_incr_sq_le). -/
theorem ItoProcess.integral_incr_sq_le (hX : ItoProcess P 𝓕 W X a H s t Ca CH)
    (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕)
    (hs : 0 ≤ s) {u v : ℝ} (hsu : s ≤ u) (huv : u ≤ v) (hvt : v ≤ t) :
    ∫ ω, (X v ω - X u ω) ^ 2 ∂P ≤ 2 * Ca ^ 2 * (v - u) ^ 2 + 2 * CH ^ 2 * (v - u) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hHuv : ItoIntegrand P 𝓕 H u v CH := hX.diff.mono hsu hvt
  have iD := memLp_integral_drift hX.drift hsu huv hvt
  have iI := memLp_itoInt hB hW h𝓕 (hs.trans hsu) hHuv
  rw [integral_congr_ae (g := fun ω => ((∫ r in u..v, a r ω) + itoInt P 𝓕 W H u v ω) ^ 2)
    (by filter_upwards [hX.incr_eq hB hW h𝓕 hs hsu huv hvt] with ω hω; rw [hω])]
  have hD : ∫ ω, (∫ r in u..v, a r ω) ^ 2 ∂P ≤ Ca ^ 2 * (v - u) ^ 2 := by
    refine (integral_mono iD.integrable_sq (integrable_const (Ca ^ 2 * (v - u) ^ 2))
      fun ω => ?_).trans (by simp)
    have h := abs_integral_drift_le hX.drift.bound hsu huv hvt ω
    rw [← mul_pow]
    exact sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
  have hI : ∫ ω, itoInt P 𝓕 W H u v ω ^ 2 ∂P ≤ CH ^ 2 * (v - u) := by
    refine integral_itoInt_sq_le_ms hB hW h𝓕 (hs.trans hsu) huv (ItoIntegrand.toMS hHuv)
      fun r hr => ?_
    refine (integral_mono (memLp_of_bound (hHuv.measurable hr) (hHuv.bound r hr)).integrable_sq
      (integrable_const (CH ^ 2)) fun ω => ?_).trans (by simp)
    have h := hHuv.bound r hr ω
    exact sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
  have hle : ∫ ω, ((∫ r in u..v, a r ω) + itoInt P 𝓕 W H u v ω) ^ 2 ∂P
      ≤ 2 * ∫ ω, (∫ r in u..v, a r ω) ^ 2 ∂P + 2 * ∫ ω, itoInt P 𝓕 W H u v ω ^ 2 ∂P := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (iD.integrable_sq.const_mul _) (iI.integrable_sq.const_mul _)]
    exact integral_mono ((iD.add iI).integrable_sq.congr (ae_of_all _ fun ω => rfl))
      ((iD.integrable_sq.const_mul _).add (iI.integrable_sq.const_mul _))
      fun ω => add_sq_le_two _ _
  linarith

/-- **Cochrane (2023), A1 §1.6, pp. 567–568: an Itô process is a mean-square continuous
integrand** on `[s, t]` (`0 ≤ s`), so `∫ X dW`-type integrals of it exist
(TidyR7ItoUnbounded).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR7ItoProcess.ItoProcess.toMS). -/
theorem ItoProcess.toMS (hX : ItoProcess P 𝓕 W X a H s t Ca CH) (hB : IsPreBrownianReal W P)
    (hW : ∀ t, Measurable (W t)) (h𝓕 : BMFiltration P W 𝓕) (hs : 0 ≤ s) :
    MSIntegrand P 𝓕 X s t where
  adapted := hX.adapted
  memLp _ hu := hX.memLp hB hW h𝓕 hs hu
  cont ε hε := by
    set K := 2 * Ca ^ 2 + 2 * CH ^ 2 + 1 with hK
    have hK0 : 0 < K := by positivity
    refine ⟨min 1 (ε / K), lt_min one_pos (by positivity), fun u hu v hv huv => ?_⟩
    have hb : ∀ x ∈ Set.Icc s t, ∀ y ∈ Set.Icc s t, x ≤ y → y - x ≤ min 1 (ε / K) →
        ∫ ω, (X y ω - X x ω) ^ 2 ∂P ≤ ε := by
      intro x hx y hy hxy hd
      have h := hX.integral_incr_sq_le hB hW h𝓕 hs hx.1 hxy hy.2
      have h1 : y - x ≤ 1 := hd.trans (min_le_left _ _)
      have h2 : y - x ≤ ε / K := hd.trans (min_le_right _ _)
      have h0 : 0 ≤ y - x := sub_nonneg.2 hxy
      have h3 : (y - x) ^ 2 ≤ y - x := by nlinarith
      have h4 : K * (y - x) ≤ ε := by
        rw [le_div_iff₀ hK0] at h2
        linarith
      nlinarith [sq_nonneg Ca, sq_nonneg CH]
    rcases le_total u v with h | h
    · have e : ∫ ω, (X u ω - X v ω) ^ 2 ∂P = ∫ ω, (X v ω - X u ω) ^ 2 ∂P :=
        integral_congr_ae (ae_of_all _ fun ω => by ring)
      rw [e]
      exact hb u hu v hv h (by rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)] at huv; exact huv)
    · exact hb v hv u hu h (by rw [abs_of_nonneg (sub_nonneg.2 h)] at huv; exact huv)

end Cochrane.Generality.TidyR7ItoProcess
