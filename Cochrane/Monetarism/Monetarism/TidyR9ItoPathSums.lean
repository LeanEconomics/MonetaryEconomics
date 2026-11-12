/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR9ItoTaylor
import Monetarism.TidyR7ItoL2

/-!
# The partition identity of Itô's formula and its deterministic limits

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for Itô's formula `f(t, X)`
(Track 3, chunk B1), the analogue for a general `f` of the exact partition identity
`TidyR7StieltjesCalculus.prod_partition_identity` used by the product rule.

## Main results

For `f(u, x)` with partial derivatives `f_t`, `f_x`, `f_xx` and a path `x`:

* `itoTaylor_partition_identity` (**the exact partition identity**): for every partition,
  `f(t, x_t) − f(s, x_s) = Σ [f(t_{i+1}, x_{i+1}) − f(t_i, x_{i+1})] + Σ f_x(t_i, x_i)Δx_i
    + ½Σ f_xx(t_i, x_i)(Δx_i)² + Σ R_i` (`timeSum`, `rsSum`, the weighted square sum, `remSum`).
* `tendsto_timeSum` (the time sum converges to `∫_s^t f_t(u, x_u) du` for a continuous path),
  `abs_timeSum_le` (`≤ 3L_t(t − s)` for `|f_t| ≤ L_t`).
* `eventually_abs_remSum_le` (**the remainder is `o(Σ(Δx)²)` uniformly**: for every `ε > 0`,
  eventually `|Σ R_i| ≤ ε Σ(Δx_i)²`), `abs_remSum_le` (`≤ 2L Σ(Δx_i)²` for `|f_xx| ≤ L`).
-/

namespace Cochrane.Monetarism.TidyR9ItoPathSums

open Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianQV
  Cochrane.Monetarism.TidyR7ItoL2 Cochrane.Monetarism.TidyR9ItoTaylor

variable {s t : ℝ}

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (Itô's formula, the time part): **the time sum**
`Σ_i [f(t_{i+1}, x_{t_{i+1}}) − f(t_i, x_{t_{i+1}})]`. -/
noncomputable def timeSum (p : Partition s t) (f : ℝ → ℝ → ℝ) (x : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range p.n, (f (p.t (i + 1)) (x (p.t (i + 1))) - f (p.t i) (x (p.t (i + 1))))

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (Itô's formula, the Taylor remainder): **the remainder
sum** `Σ_i R_i`, with
`R_i = f(t_i, x_{i+1}) − f(t_i, x_i) − f_x(t_i, x_i)Δx_i − ½f_xx(t_i, x_i)(Δx_i)²`. -/
noncomputable def remSum (p : Partition s t) (f fx fxx : ℝ → ℝ → ℝ) (x : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range p.n, (f (p.t i) (x (p.t (i + 1))) - f (p.t i) (x (p.t i))
    - fx (p.t i) (x (p.t i)) * (x (p.t (i + 1)) - x (p.t i))
    - fxx (p.t i) (x (p.t i)) / 2 * (x (p.t (i + 1)) - x (p.t i)) ^ 2)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Itô's formula): the exact partition identity**
`f(t, x_t) − f(s, x_s) = Σ[f(t_{i+1}, x_{i+1}) − f(t_i, x_{i+1})] + Σ f_x(t_i, x_i)Δx_i
  + ½Σ f_xx(t_i, x_i)(Δx_i)² + Σ R_i` for every partition of `[s, t]` and every path.
The second-order analogue of `TidyR7StieltjesCalculus.prod_partition_identity`. -/
theorem itoTaylor_partition_identity (p : Partition s t) (f fx fxx : ℝ → ℝ → ℝ)
    (x : ℝ → ℝ) :
    f t (x t) - f s (x s) = timeSum p f x + rsSum p (fun u => fx u (x u)) x
      + (∑ i ∈ Finset.range p.n, fxx (p.t i) (x (p.t i))
        * ((x (p.t (i + 1)) - x (p.t i)) * (x (p.t (i + 1)) - x (p.t i)))) / 2
      + remSum p f fx fxx x := by
  have ht := Finset.sum_range_sub (fun i => f (p.t i) (x (p.t i))) p.n
  rw [p.last, p.first] at ht
  rw [← ht, timeSum, rsSum, remSum, Finset.sum_div, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Cochrane (2023), A1 §1.6, pp. 567–568: a cell of a partition lies in `[s, t]`, left end at
most right end.
From `TidyR7StieltjesSums.t_mem` and monotonicity. -/
lemma cell_mem (p : Partition s t) {i : ℕ} (hi : i < p.n) :
    p.t i ∈ Set.Icc s t ∧ p.t (i + 1) ∈ Set.Icc s t ∧ p.t i ≤ p.t (i + 1) :=
  ⟨t_mem p hi.le, t_mem p hi, p.strictMono.monotone (Nat.le_succ i)⟩

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Itô's formula, the `f_t dt` term): the time sum
converges** to `∫_s^t f_t(u, x_u) du` along any partitions with mesh `→ 0`, for `f_t` jointly
continuous, `f_xx` jointly continuous (used only through `exists_delta_taylor_path`) and a path
continuous on `[s, t]`. -/
theorem tendsto_timeSum {f ft fx fxx : ℝ → ℝ → ℝ}
    (hft : ∀ u x, HasDerivAt (fun r => f r x) (ft u x) u)
    (hfx : ∀ u x, HasDerivAt (f u) (fx u x) x) (hfxx : ∀ u x, HasDerivAt (fx u) (fxx u x) x)
    (cft : Continuous (Function.uncurry ft)) (cfxx : Continuous (Function.uncurry fxx))
    {x : ℝ → ℝ} (hx : ContinuousOn x (Set.Icc s t)) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) :
    Tendsto (fun k => timeSum (ps k) f x) atTop (𝓝 (∫ u in s..t, ft u (x u))) := by
  have hst : 0 ≤ t - s := sub_nonneg.2 (a_le_b (ps 0))
  have hgc : ContinuousOn (fun u => ft u (x u)) (Set.Icc s t) :=
    cft.comp_continuousOn (continuousOn_id.prodMk hx)
  have hR := tendsto_riemannSum hgc ps hps
  rw [Metric.tendsto_atTop] at hR ⊢
  intro η hη
  set ε := η / (4 * (t - s + 1)) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨δ, hδ, hδf⟩ := exists_delta_taylor_path hft hfx hfxx cft cfxx hx hε0
  obtain ⟨N1, hN1⟩ := hR (η / 2) (by linarith)
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 (hps.eventually (gt_mem_nhds hδ))
  refine ⟨max N1 N2, fun k hk => ?_⟩
  have hk1 := hN1 k (le_of_max_le_left hk)
  have hk2 := hN2 k (le_of_max_le_right hk)
  set p := ps k with hp
  have hcell : |timeSum p f x - riemannSum p (fun u => ft u (x u))| ≤ 2 * ε * (t - s) := by
    rw [timeSum, riemannSum, ← Finset.sum_sub_distrib, ← sum_step_eq p, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    obtain ⟨hu, hv, huv⟩ := cell_mem p (Finset.mem_range.1 hi)
    obtain ⟨h1, h2, -⟩ := hδf _ hu _ hv huv ((le_mesh p (Finset.mem_range.1 hi)).trans_lt hk2)
    have hpos : 0 ≤ p.t (i + 1) - p.t i := sub_nonneg.2 huv
    have e : f (p.t (i + 1)) (x (p.t (i + 1))) - f (p.t i) (x (p.t (i + 1)))
        - ft (p.t i) (x (p.t i)) * (p.t (i + 1) - p.t i)
        = (f (p.t (i + 1)) (x (p.t (i + 1))) - f (p.t i) (x (p.t (i + 1)))
          - ft (p.t i) (x (p.t (i + 1))) * (p.t (i + 1) - p.t i))
        + (ft (p.t i) (x (p.t (i + 1))) - ft (p.t i) (x (p.t i))) * (p.t (i + 1) - p.t i) := by
      ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hpos]
    have h3 := mul_le_mul_of_nonneg_right h2 hpos
    linarith
  rw [Real.dist_eq] at hk1 ⊢
  have h4 : 2 * ε * (t - s) < η / 2 := by
    rw [hε]
    have : 2 * (η / (4 * (t - s + 1))) * (t - s) = η / 2 * ((t - s) / (t - s + 1)) := by
      field_simp
      ring
    rw [this]
    have hq : (t - s) / (t - s + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
    nlinarith
  calc |timeSum p f x - ∫ u in s..t, ft u (x u)|
      ≤ |timeSum p f x - riemannSum p (fun u => ft u (x u))|
        + |riemannSum p (fun u => ft u (x u)) - ∫ u in s..t, ft u (x u)| := abs_sub_le _ _ _
    _ < η := by linarith

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the time sum is bounded**, `|Σ T_i| ≤ 3L_t(t − s)`,
if `|f_t| ≤ L_t` on `[s, t] × ℝ`. -/
theorem abs_timeSum_le {f ft : ℝ → ℝ → ℝ} (hft : ∀ u x, HasDerivAt (fun r => f r x) (ft u x) u)
    {Lt : ℝ} (hftb : ∀ u ∈ Set.Icc s t, ∀ x, |ft u x| ≤ Lt) (p : Partition s t) (x : ℝ → ℝ) :
    |timeSum p f x| ≤ 3 * Lt * (t - s) := by
  rw [timeSum, ← sum_step_eq p, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  obtain ⟨hu, hv, huv⟩ := cell_mem p (Finset.mem_range.1 hi)
  have hsub : ∀ r ∈ Set.Icc (p.t i) (p.t (i + 1)), r ∈ Set.Icc s t := fun r hr =>
    ⟨hu.1.trans hr.1, hr.2.trans hv.2⟩
  have h := abs_taylor1_le (g := fun r => f r (x (p.t (i + 1))))
    (g' := fun r => ft r (x (p.t (i + 1)))) (c := 2 * Lt) huv (fun r _ => hft r _)
    (fun r hr => by
      have h1 := hftb r (hsub r hr) (x (p.t (i + 1)))
      have h2 := hftb (p.t i) hu (x (p.t (i + 1)))
      exact (abs_sub _ _).trans (by linarith))
  have hpos : 0 ≤ p.t (i + 1) - p.t i := sub_nonneg.2 huv
  have h3 : |ft (p.t i) (x (p.t (i + 1))) * (p.t (i + 1) - p.t i)|
      ≤ Lt * (p.t (i + 1) - p.t i) := by
    rw [abs_mul, abs_of_nonneg hpos]
    exact mul_le_mul_of_nonneg_right (hftb _ hu _) hpos
  have h4 := abs_add_le (f (p.t (i + 1)) (x (p.t (i + 1))) - f (p.t i) (x (p.t (i + 1)))
    - ft (p.t i) (x (p.t (i + 1))) * (p.t (i + 1) - p.t i))
    (ft (p.t i) (x (p.t (i + 1))) * (p.t (i + 1) - p.t i))
  rw [sub_add_cancel] at h4
  linarith

/-- Cochrane (2023), A1 §1.6, pp. 567–568: **the remainder is at most `2L Σ(Δx_i)²`** if
`|f_xx| ≤ L` on `[s, t] × ℝ`. -/
theorem abs_remSum_le {f fx fxx : ℝ → ℝ → ℝ} (hfx : ∀ u x, HasDerivAt (f u) (fx u x) x)
    (hfxx : ∀ u x, HasDerivAt (fx u) (fxx u x) x) {L : ℝ}
    (hfxxb : ∀ u ∈ Set.Icc s t, ∀ x, |fxx u x| ≤ L) (p : Partition s t) (x : ℝ → ℝ) :
    |remSum p f fx fxx x| ≤ 2 * L * crossSum p x x := by
  rw [remSum, crossSum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  obtain ⟨hu, -, -⟩ := cell_mem p (Finset.mem_range.1 hi)
  have h := abs_taylor2_le (hfx (p.t i)) (hfxx (p.t i)) (x := x (p.t i)) (y := x (p.t (i + 1)))
    (c := 2 * L) fun z _ => by
      have h1 := hfxxb _ hu z
      have h2 := hfxxb _ hu (x (p.t i))
      exact (abs_sub _ _).trans (by linarith)
  rw [← sq]
  exact h

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Itô's formula, the remainder vanishes against the
quadratic variation): for a continuous path and every `ε > 0`, eventually
`|Σ R_i| ≤ ε Σ(Δx_i)²`** along any partitions with mesh `→ 0` (uniform continuity of `f_xx` on
the compact range, `exists_delta_taylor_path`). -/
theorem eventually_abs_remSum_le {f ft fx fxx : ℝ → ℝ → ℝ}
    (hft : ∀ u x, HasDerivAt (fun r => f r x) (ft u x) u)
    (hfx : ∀ u x, HasDerivAt (f u) (fx u x) x) (hfxx : ∀ u x, HasDerivAt (fx u) (fxx u x) x)
    (cft : Continuous (Function.uncurry ft)) (cfxx : Continuous (Function.uncurry fxx))
    {x : ℝ → ℝ} (hx : ContinuousOn x (Set.Icc s t)) (ps : ℕ → Partition s t)
    (hps : Tendsto (fun k => mesh (ps k)) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, |remSum (ps k) f fx fxx x| ≤ ε * crossSum (ps k) x x := by
  obtain ⟨δ, hδ, hδf⟩ := exists_delta_taylor_path hft hfx hfxx cft cfxx hx hε
  filter_upwards [hps.eventually (gt_mem_nhds hδ)] with k hk
  rw [remSum, crossSum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  obtain ⟨hu, hv, huv⟩ := cell_mem (ps k) (Finset.mem_range.1 hi)
  obtain ⟨-, -, h3⟩ := hδf _ hu _ hv huv ((le_mesh (ps k) (Finset.mem_range.1 hi)).trans_lt hk)
  rw [← sq]
  exact h3

end Cochrane.Monetarism.TidyR9ItoPathSums
