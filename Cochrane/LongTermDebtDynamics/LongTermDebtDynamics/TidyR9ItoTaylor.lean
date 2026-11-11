/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Second-order Taylor bounds along a continuous path (deterministic part of Itô's formula)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for Itô's formula `f(X)`
(Track 3, chunk B1), which the positive diffusive `Λ/P` of (1.32)–(1.34) needs: the
deterministic estimates behind the expansion
`f(t_{i+1}, x_{i+1}) − f(t_i, x_i) = f_t Δt + f_x Δx + ½ f_xx (Δx)² + remainder`.

## Main results

* `abs_taylor2_le` (**Taylor with a second-order remainder**): if `|f''(z) − f''(x)| ≤ c` on the
  segment between `x` and `y`, then `|f y − f x − f'(x)(y − x) − ½f''(x)(y − x)²| ≤ c(y − x)²`
  (two applications of the mean value inequality; no Lagrange point needed).
* `abs_taylor1_le`: the first-order version in time,
  `|g v − g u − g'(u)(v − u)| ≤ c(v − u)` if `|g' − g'(u)| ≤ c` on `[u, v]`.
* `abs_sub_le_of_deriv_bound` (a derivative bounded by `L` gives an `L`-Lipschitz function).
* `exists_delta_taylor_path` (**the uniform pathwise estimate**): for `f(u, x)` with `f_t`, `f_xx`
  jointly continuous and a path `x` continuous on `[s, t]`, for every `ε > 0` there is `δ > 0`
  such that for `u ≤ v` in `[s, t]` with `v − u < δ` the time error is `≤ ε(v − u)`, the shift of
  `f_t` is `≤ ε`, and the space remainder is `≤ ε(x_v − x_u)²`. This is where uniform continuity of
  `f_t`, `f_xx` on the compact set `[s, t] × [−M, M]` (`M` a bound of the path) enters: no
  global uniform continuity of `f''` is needed.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR9ItoTaylor

open Filter Topology

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Itô's formula, the space step): Taylor's formula
with a second-order remainder.** If `f' = df`, `f'' = df'` everywhere and
`|f''(z) − f''(x)| ≤ c` for `z` between `x` and `y`, then
`|f y − f x − f'(x)(y − x) − f''(x)/2·(y − x)²| ≤ c(y − x)²`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoTaylor.abs_taylor2_le). -/
theorem abs_taylor2_le {f f' f'' : ℝ → ℝ} (hf : ∀ z, HasDerivAt f (f' z) z)
    (hf' : ∀ z, HasDerivAt f' (f'' z) z) {x y c : ℝ}
    (hc : ∀ z ∈ Set.uIcc x y, |f'' z - f'' x| ≤ c) :
    |f y - f x - f' x * (y - x) - f'' x / 2 * (y - x) ^ 2| ≤ c * (y - x) ^ 2 := by
  have hconv : Convex ℝ (Set.uIcc x y) := convex_uIcc x y
  have hx : x ∈ Set.uIcc x y := Set.left_mem_uIcc
  have hy : y ∈ Set.uIcc x y := Set.right_mem_uIcc
  set g1 : ℝ → ℝ := fun z => f' z - f' x - f'' x * (z - x) with hg1
  have hd1 : ∀ z, HasDerivAt g1 (f'' z - f'' x) z := by
    intro z
    have h := HasDerivAt.sub (HasDerivAt.sub_const (f' x) (hf' z))
      (HasDerivAt.const_mul (f'' x) (HasDerivAt.sub_const x (hasDerivAt_id' z)))
    convert h using 1
    ring
  have hb1 : ∀ z ∈ Set.uIcc x y, |g1 z| ≤ c * |y - x| := by
    intro z hz
    have h := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := g1) (f' := fun z => f'' z - f'' x) (C := c)
      (fun w _ => (hd1 w).hasDerivWithinAt) (fun w hw => by
        rw [Real.norm_eq_abs]; exact hc w hw) hx hz
    have e : g1 x = 0 := by simp [hg1]
    rw [e, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at h
    have hzx : |z - x| ≤ |y - x| := by
      rw [Set.mem_uIcc] at hz
      rcases hz with hz | hz
      · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
      · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
    have c0 : 0 ≤ c := (abs_nonneg _).trans (hc x hx)
    exact h.trans (mul_le_mul_of_nonneg_left hzx c0)
  set g : ℝ → ℝ := fun z => f z - f x - f' x * (z - x) - f'' x / 2 * (z - x) ^ 2 with hg
  have hd : ∀ z, HasDerivAt g (g1 z) z := by
    intro z
    have h1 := HasDerivAt.sub (HasDerivAt.sub_const (f x) (hf z))
      (HasDerivAt.const_mul (f' x) (HasDerivAt.sub_const x (hasDerivAt_id' z)))
    have h2 := HasDerivAt.const_mul (f'' x / 2)
      (HasDerivAt.pow (HasDerivAt.sub_const x (hasDerivAt_id' z)) 2)
    have h := HasDerivAt.sub h1 h2
    convert h using 1
    simp only [hg1]
    push_cast
    ring
  have h := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := g) (f' := g1) (C := c * |y - x|)
    (fun w _ => (hd w).hasDerivWithinAt) (fun w hw => by
      rw [Real.norm_eq_abs]; exact hb1 w hw) hx hy
  have e : g x = 0 := by simp [hg]
  rw [e, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at h
  have e2 : c * |y - x| * |y - x| = c * (y - x) ^ 2 := by
    rw [mul_assoc, ← sq, sq_abs]
  simpa [hg, e2] using h

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Itô's formula, the time step): first-order
Taylor bound.** If `g' = dg` on `[u, v]` and `|g'(r) − g'(u)| ≤ c` there, `u ≤ v`, then
`|g v − g u − g'(u)(v − u)| ≤ c(v − u)`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoTaylor.abs_taylor1_le). -/
theorem abs_taylor1_le {g g' : ℝ → ℝ} {u v c : ℝ} (huv : u ≤ v)
    (hg : ∀ r ∈ Set.Icc u v, HasDerivAt g (g' r) r)
    (hc : ∀ r ∈ Set.Icc u v, |g' r - g' u| ≤ c) :
    |g v - g u - g' u * (v - u)| ≤ c * (v - u) := by
  have hconv : Convex ℝ (Set.Icc u v) := convex_Icc u v
  have hu : u ∈ Set.Icc u v := Set.left_mem_Icc.2 huv
  have hv : v ∈ Set.Icc u v := Set.right_mem_Icc.2 huv
  set h1 : ℝ → ℝ := fun r => g r - g' u * r with hh1
  have hd : ∀ r ∈ Set.Icc u v, HasDerivWithinAt h1 (g' r - g' u) (Set.Icc u v) r := by
    intro r hr
    have h := (HasDerivAt.sub (hg r hr) (HasDerivAt.const_mul (g' u)
      (hasDerivAt_id' r))).hasDerivWithinAt (s := Set.Icc u v)
    convert h using 1
    ring
  have h := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := h1)
    (f' := fun r => g' r - g' u) (C := c) hd (fun r hr => by
      rw [Real.norm_eq_abs]; exact hc r hr) hu hv
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 huv)] at h
  have e : h1 v - h1 u = g v - g u - g' u * (v - u) := by
    simp only [hh1]
    ring
  rw [← e]
  exact h

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (Itô's formula): **a derivative bounded by `L` gives
an `L`-Lipschitz function**, `|g x − g y| ≤ L|x − y|`.
Restates Mathlib `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` on `univ`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoTaylor.abs_sub_le_of_deriv_bound). -/
theorem abs_sub_le_of_deriv_bound {g g' : ℝ → ℝ} (hg : ∀ z, HasDerivAt g (g' z) z) {L : ℝ}
    (hL : ∀ z, |g' z| ≤ L) (x y : ℝ) : |g x - g y| ≤ L * |x - y| := by
  have h := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g) (f' := g') (C := L)
    (fun w _ => (hg w).hasDerivWithinAt) (fun w _ => by
      rw [Real.norm_eq_abs]; exact hL w) (Set.mem_univ y) (Set.mem_univ x)
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Itô's formula along a path): the uniform pathwise
estimate.** Let `f(u, x)` have partial derivatives `f_t = ∂_u f`, `f_x = ∂_x f`,
`f_xx = ∂_x f_x` everywhere, with `f_t` and `f_xx` jointly continuous, and let the path `x` be
continuous on `[s, t]`. For every `ε > 0` there is `δ > 0` such that for all `u ≤ v` in
`[s, t]` with `v − u < δ`:
`|f(v, x_v) − f(u, x_v) − f_t(u, x_v)(v − u)| ≤ ε(v − u)`,
`|f_t(u, x_v) − f_t(u, x_u)| ≤ ε`, and
`|f(u, x_v) − f(u, x_u) − f_x(u, x_u)Δx − ½f_xx(u, x_u)(Δx)²| ≤ ε(Δx)²`, `Δx = x_v − x_u`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR9ItoTaylor.exists_delta_taylor_path). -/
theorem exists_delta_taylor_path {f ft fx fxx : ℝ → ℝ → ℝ}
    (hft : ∀ u x, HasDerivAt (fun r => f r x) (ft u x) u)
    (hfx : ∀ u x, HasDerivAt (f u) (fx u x) x) (hfxx : ∀ u x, HasDerivAt (fx u) (fxx u x) x)
    (cft : Continuous (Function.uncurry ft)) (cfxx : Continuous (Function.uncurry fxx))
    {x : ℝ → ℝ} {s t : ℝ} (hx : ContinuousOn x (Set.Icc s t)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ u ∈ Set.Icc s t, ∀ v ∈ Set.Icc s t, u ≤ v → v - u < δ →
      |f v (x v) - f u (x v) - ft u (x v) * (v - u)| ≤ ε * (v - u) ∧
      |ft u (x v) - ft u (x u)| ≤ ε ∧
      |f u (x v) - f u (x u) - fx u (x u) * (x v - x u) - fxx u (x u) / 2 * (x v - x u) ^ 2|
        ≤ ε * (x v - x u) ^ 2 := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hx
  set K : Set (ℝ × ℝ) := Set.Icc s t ×ˢ Set.Icc (-M) M with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hxK : ∀ u ∈ Set.Icc s t, x u ∈ Set.Icc (-M) M := fun u hu => by
    have h := hM u hu
    rw [Real.norm_eq_abs] at h
    exact abs_le.1 h
  have uft := Metric.uniformContinuousOn_iff.1
    (hKc.uniformContinuousOn_of_continuous cft.continuousOn) ε hε
  have ufxx := Metric.uniformContinuousOn_iff.1
    (hKc.uniformContinuousOn_of_continuous cfxx.continuousOn) ε hε
  obtain ⟨δ1, hδ1, h1⟩ := uft
  obtain ⟨δ2, hδ2, h2⟩ := ufxx
  have ux := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hx) (min δ1 δ2) (lt_min hδ1 hδ2)
  obtain ⟨δ3, hδ3, h3⟩ := ux
  refine ⟨min (min δ1 δ2) δ3, lt_min (lt_min hδ1 hδ2) hδ3, fun u hu v hv huv hvu => ?_⟩
  have hvu1 : v - u < δ1 := hvu.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hvu3 : v - u < δ3 := hvu.trans_le (min_le_right _ _)
  have hdx : dist (x v) (x u) < min δ1 δ2 := h3 v hv u hu (by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 huv)]; exact hvu3)
  have hdx1 : |x v - x u| < δ1 := by
    rw [← Real.dist_eq]; exact hdx.trans_le (min_le_left _ _)
  have hdx2 : |x v - x u| < δ2 := by
    rw [← Real.dist_eq]; exact hdx.trans_le (min_le_right _ _)
  refine ⟨?_, ?_, ?_⟩
  · -- the time error
    refine abs_taylor1_le (g := fun r => f r (x v)) (g' := fun r => ft r (x v)) huv
      (fun r _ => hft r (x v)) fun r hr => ?_
    have hrK : (r, x v) ∈ K := ⟨⟨hu.1.trans hr.1, hr.2.trans hv.2⟩, hxK v hv⟩
    have huK : (u, x v) ∈ K := ⟨hu, hxK v hv⟩
    have hd : dist (r, x v) (u, x v) < δ1 := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hr.1)]
      exact max_lt (by linarith [hr.2]) hδ1
    have h := h1 _ hrK _ huK hd
    rw [Real.dist_eq] at h
    exact h.le
  · -- the shift of `f_t`
    have hvK : (u, x v) ∈ K := ⟨hu, hxK v hv⟩
    have huK : (u, x u) ∈ K := ⟨hu, hxK u hu⟩
    have hd : dist (u, x v) (u, x u) < δ1 := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq]
      exact max_lt hδ1 hdx1
    have h := h1 _ hvK _ huK hd
    rw [Real.dist_eq] at h
    exact h.le
  · -- the space remainder
    refine abs_taylor2_le (hfx u) (hfxx u) fun z hz => ?_
    have hzM : z ∈ Set.Icc (-M) M :=
      Set.uIcc_subset_Icc (hxK u hu) (hxK v hv) hz
    have hzK : (u, z) ∈ K := ⟨hu, hzM⟩
    have huK : (u, x u) ∈ K := ⟨hu, hxK u hu⟩
    have hzx : |z - x u| ≤ |x v - x u| := by
      rw [Set.mem_uIcc] at hz
      rcases hz with hz | hz
      · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
      · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
    have hd : dist (u, z) (u, x u) < δ2 := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq]
      exact max_lt hδ2 (hzx.trans_lt hdx2)
    have h := h2 _ hzK _ huK hd
    rw [Real.dist_eq] at h
    exact h.le

end Cochrane.LongTermDebtDynamics.TidyR9ItoTaylor
