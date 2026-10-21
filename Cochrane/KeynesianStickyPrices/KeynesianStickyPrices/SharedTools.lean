/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.ForwardSolution
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Shared tools for Chapter 17

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, pp. 397–421, and Online
Appendix A1, §1.7–§1.8 and §1.13.1, pp. 569–572 and 586–588: general lemmas used by both the
simple-model chain (`StaticIS` … `AdaptiveTaylor`) and the full-model chain (`FullModel` …
`History`). They were proved separately in the two chains and are collected here once.

* Stable scalar recursions: if `x_{n+1} = a x_n + f_n` with `|a| < 1` and `f_n → 0` then
  `x_n → 0` (`tendsto_zero_of_stable`), and the averaging form `tendsto_of_stable_avg`
  (long-run responses, pp. 406 and 408).
* Forward sums `∑_j qʲ g_{n+j}` of a bounded path with `|q| < 1`: recursion and bound
  (`fwd_sum_props`) and limit (`fwd_sum_tendsto`, dominated convergence) — eq. (5.5), p. 119,
  as used on p. 408.
* Infinite-past (ℤ-indexed) backward recursions `x_{s+1} = a x_s + w_{s+1}`, `|a| < 1`: the
  backward moving average (17.8), p. 400 (`backward_iterate`, `eq_backward_series`,
  `backward_series_solves`), and its homogeneous corollary `int_homog_zero` (a bounded solution
  of `x_{s+1} = a x_s` on ℤ vanishes), used for the anticipated-from-the-infinite-past path of
  Fig. 17.5, p. 409.
* The structural matrices of the three-equation model, p. 420 and A1 (1.55), p. 586:
  `Pmat`, `Qmat` and the solved transition matrix `solvedA P Q = P⁻¹Q` with its trace and
  determinant (`tr2_solvedA`, `det2_solvedA`, `det2_Pmat`).
-/

namespace Cochrane.KeynesianStickyPrices.SharedTools

open Filter Topology

/-! ### Stable recursions -/

/-- Cochrane (2023), p. 406 (supporting lemma, proved here): if `x_{n+1} = a x_n + f_n` with
`|a| < 1` and `f_n → 0`, then `x_n → 0`. -/
theorem tendsto_zero_of_stable {a : ℝ} (ha : |a| < 1) {x f : ℕ → ℝ}
    (h : ∀ n, x (n + 1) = a * x n + f n) (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h1a : 0 < 1 - |a| := by linarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hf ((1 - |a|) * ε / 2) (by positivity)
  have hk : ∀ k, |x (N + k)| ≤ |a| ^ k * |x N| + ε / 2 := by
    intro k
    induction k with
    | zero => simp only [add_zero, pow_zero, one_mul]; linarith
    | succ k ih =>
      have hfk := hN (N + k) (Nat.le_add_right N k)
      rw [Real.dist_eq, sub_zero] at hfk
      rw [← add_assoc, h]
      calc |a * x (N + k) + f (N + k)| ≤ |a| * |x (N + k)| + |f (N + k)| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ |a| * (|a| ^ k * |x N| + ε / 2) + (1 - |a|) * ε / 2 :=
            add_le_add (mul_le_mul_of_nonneg_left ih (abs_nonneg a)) hfk.le
        _ = |a| ^ (k + 1) * |x N| + ε / 2 := by ring
  have hpow : Tendsto (fun k => |a| ^ k * |x N|) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg a) ha).mul_const (|x N|)
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hpow (ε / 2) (by positivity)
  refine ⟨N + K, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h1 := hk (K + k)
  have h2 := hK (K + k) (Nat.le_add_right K k)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h2
  rw [Real.dist_eq, sub_zero, add_assoc]
  linarith

/-- Cochrane (2023), p. 406 (supporting lemma): if `x_{n+1} = a x_n + b y_n` with `a + b = 1`,
`|a| < 1` and `y_n → ȳ`, then `x_n → ȳ`. -/
theorem tendsto_of_stable_avg {a b yb : ℝ} (ha : |a| < 1) (hab : a + b = 1) {x y : ℕ → ℝ}
    (h : ∀ n, x (n + 1) = a * x n + b * y n) (hy : Tendsto y atTop (𝓝 yb)) :
    Tendsto x atTop (𝓝 yb) := by
  have hf : Tendsto (fun n => b * (y n - yb)) atTop (𝓝 0) := by
    simpa using (hy.sub_const yb).const_mul b
  have := tendsto_zero_of_stable ha (x := fun n => x n - yb) (f := fun n => b * (y n - yb))
    (fun n => by rw [h n]; linear_combination yb * hab) hf
  simpa using this.add_const yb

/-! ### Forward sums -/

/-- Cochrane (2023), p. 408: the forward sum `Y_n = ∑_j qʲ g_{n+j}` of a bounded path, `|q| < 1`,
satisfies `Y_n = g_n + q Y_{n+1}` and `|Y_n| ≤ M/(1 − |q|)`. -/
theorem fwd_sum_props {q M : ℝ} (hq : |q| < 1) {g : ℕ → ℝ} (hg : ∀ n, |g n| ≤ M) :
    (∀ n, (∑' j : ℕ, q ^ j * g (n + j)) = g n + q * ∑' j : ℕ, q ^ j * g (n + 1 + j)) ∧
      ∀ n, |∑' j : ℕ, q ^ j * g (n + j)| ≤ M / (1 - |q|) := by
  have hgeo := summable_geometric_of_lt_one (abs_nonneg q) hq
  have hb : ∀ n j, ‖q ^ j * g (n + j)‖ ≤ |q| ^ j * M := fun n j => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hg _) (pow_nonneg (abs_nonneg q) j)
  have hs : ∀ n, Summable fun j => q ^ j * g (n + j) := fun n =>
    Summable.of_norm_bounded (hgeo.mul_right M) (hb n)
  refine ⟨fun n => ?_, fun n => ?_⟩
  · rw [(hs n).tsum_eq_zero_add, ← tsum_mul_left]
    simp only [pow_zero, one_mul, add_zero]
    congr 1
    refine tsum_congr fun j => ?_
    rw [pow_succ, show n + (j + 1) = n + 1 + j by ring]
    ring
  · have := tsum_of_norm_bounded ((hasSum_geometric_of_lt_one (abs_nonneg q) hq).mul_right M)
      (hb n)
    rw [Real.norm_eq_abs] at this
    simpa [div_eq_mul_inv, mul_comm] using this

/-- Cochrane (2023), p. 408: the forward sum converges to `ḡ/(1 − q)` when `g_n → ḡ`
(dominated convergence for series). -/
theorem fwd_sum_tendsto {q M gb : ℝ} (hq : |q| < 1) {g : ℕ → ℝ} (hg : ∀ n, |g n| ≤ M)
    (hlim : Tendsto g atTop (𝓝 gb)) :
    Tendsto (fun n => ∑' j : ℕ, q ^ j * g (n + j)) atTop (𝓝 (gb / (1 - q))) := by
  have hgeo := summable_geometric_of_lt_one (abs_nonneg q) hq
  have hq1 : 1 - q ≠ 0 := by
    intro h0; have : q = 1 := by linarith
    rw [this, abs_one] at hq; exact lt_irrefl _ hq
  have hsum : ∑' j : ℕ, q ^ j * gb = gb / (1 - q) := by
    rw [tsum_mul_right, tsum_geometric_of_abs_lt_one hq]; field_simp
  rw [← hsum]
  refine tendsto_tsum_of_dominated_convergence (bound := fun j => |q| ^ j * M)
    (hgeo.mul_right M) (fun j => ?_) (Eventually.of_forall fun n j => ?_)
  · exact (hlim.comp (tendsto_add_atTop_nat j)).const_mul (q ^ j)
  · rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hg _) (pow_nonneg (abs_nonneg q) j)

/-! ### Infinite-past backward recursions (ℤ-indexed) -/

/-- Cochrane (2023), eq. (17.8), p. 400: iterating the stable backward recursion
`x_{s+1} = a x_s + w_{s+1}` on the integers `k` times,
`x_t = aᵏ x_{t−k} + ∑_{j<k} aʲ w_{t−j}`. -/
theorem backward_iterate {a : ℝ} {x w : ℤ → ℝ} (h : ∀ s, x (s + 1) = a * x s + w (s + 1))
    (t : ℤ) (k : ℕ) :
    x t = a ^ k * x (t - k) + ∑ j ∈ Finset.range k, a ^ j * w (t - j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := h (t - (k + 1 : ℕ))
    have e : t - ((k + 1 : ℕ) : ℤ) + 1 = t - k := by push_cast; ring
    rw [e] at hs
    rw [ih, hs, Finset.sum_range_succ]
    ring

/-- Cochrane (2023), eq. (17.8), p. 400: with `|a| < 1`, every bounded solution on the integers
of `x_{s+1} = a x_s + w_{s+1}` (bounded `w`) is the backward moving average
`x_t = ∑_{j ≥ 0} aʲ w_{t−j}`. -/
theorem eq_backward_series {a Mx Mw : ℝ} (ha : |a| < 1) {x w : ℤ → ℝ}
    (hx : ∀ s, |x s| ≤ Mx) (hw : ∀ s, |w s| ≤ Mw) (h : ∀ s, x (s + 1) = a * x s + w (s + 1))
    (t : ℤ) : x t = ∑' j : ℕ, a ^ j * w (t - j) := by
  have hsum : Summable fun j : ℕ => a ^ j * w (t - j) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one (abs_nonneg a) ha).mul_right Mw)
      fun j => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow]
        exact mul_le_mul_of_nonneg_left (hw _) (pow_nonneg (abs_nonneg a) j)
  have hlim : Tendsto (fun k => ∑ j ∈ Finset.range k, a ^ j * w (t - j)) atTop (𝓝 (x t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm (a := fun k => |a| ^ k * Mx) (fun k => ?_) ?_
    · rw [Real.norm_eq_abs, Real.norm_eq_abs, backward_iterate h t k, abs_abs,
        show ∀ A S : ℝ, S - (A + S) = -A from fun A S => by ring, abs_neg, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hx _) (pow_nonneg (abs_nonneg a) k)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg a) ha).mul_const Mx
  exact tendsto_nhds_unique hlim hsum.hasSum.tendsto_sum_nat

/-- Cochrane (2023), eq. (17.8), p. 400 (converse): for `|a| < 1` and bounded `w`, the backward
moving average is a bounded solution of `x_{s+1} = a x_s + w_{s+1}`. -/
theorem backward_series_solves {a Mw : ℝ} (ha : |a| < 1) {w : ℤ → ℝ} (hw : ∀ s, |w s| ≤ Mw) :
    (∀ s, (∑' j : ℕ, a ^ j * w (s + 1 - j)) = a * (∑' j : ℕ, a ^ j * w (s - j)) + w (s + 1)) ∧
      ∀ s, |∑' j : ℕ, a ^ j * w (s - j)| ≤ Mw / (1 - |a|) := by
  have hg := summable_geometric_of_lt_one (abs_nonneg a) ha
  have hsum : ∀ s, Summable fun j : ℕ => a ^ j * w (s - j) := fun s =>
    Summable.of_norm_bounded (hg.mul_right Mw) fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hw _) (pow_nonneg (abs_nonneg a) j)
  refine ⟨fun s => ?_, fun s => ?_⟩
  · rw [(hsum (s + 1)).tsum_eq_zero_add, ← tsum_mul_left]
    simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero, Nat.cast_add, Nat.cast_one]
    rw [add_comm]
    congr 1
    refine tsum_congr fun j => ?_
    rw [pow_succ, show s + 1 - ((j : ℤ) + 1) = s - j by ring]
    ring
  · have hb : ∀ j : ℕ, ‖a ^ j * w (s - j)‖ ≤ |a| ^ j * Mw := fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hw _) (pow_nonneg (abs_nonneg a) j)
    have := tsum_of_norm_bounded ((hasSum_geometric_of_lt_one (abs_nonneg a) ha).mul_right Mw) hb
    rw [Real.norm_eq_abs] at this
    simpa [div_eq_mul_inv, mul_comm] using this

/-- Cochrane (2023), eq. (17.8), p. 400 and Fig. 17.5, p. 409 (homogeneous case): with
`|a| < 1`, the only bounded solution on the integers of `x_{s+1} = a x_s` is zero (an infinite
past leaves no free initial condition). -/
theorem int_homog_zero {a M : ℝ} (ha : |a| < 1) {x : ℤ → ℝ} (hx : ∀ s, |x s| ≤ M)
    (h : ∀ s, x (s + 1) = a * x s) : x = 0 := by
  funext t
  have e := eq_backward_series ha hx (w := fun _ => 0) (Mw := 0) (fun _ => by simp)
    (fun s => by rw [h s, add_zero]) t
  simpa using e

/-! ### The structural matrices of the three-equation model -/

/-- Cochrane (2023), p. 420: the matrix `A = P⁻¹ Q` of `x_t = A E_t x_{t+1}`, written with the
adjugate of `P`. -/
noncomputable def solvedA (P Q : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(P 1 1 * Q 0 0 - P 0 1 * Q 1 0) / det2 P, (P 1 1 * Q 0 1 - P 0 1 * Q 1 1) / det2 P;
    (P 0 0 * Q 1 0 - P 1 0 * Q 0 0) / det2 P, (P 0 0 * Q 1 1 - P 1 0 * Q 0 1) / det2 P]

/-- `tr A = (P₁₁Q₀₀ − P₀₁Q₁₀ − P₁₀Q₀₁ + P₀₀Q₁₁)/det P`. -/
theorem tr2_solvedA (P Q : Matrix (Fin 2) (Fin 2) ℝ) :
    tr2 (solvedA P Q) =
      (P 1 1 * Q 0 0 - P 0 1 * Q 1 0 - P 1 0 * Q 0 1 + P 0 0 * Q 1 1) / det2 P := by
  simp only [tr2, solvedA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- `det A = det Q / det P`. -/
theorem det2_solvedA {P : Matrix (Fin 2) (Fin 2) ℝ} (hP : det2 P ≠ 0)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) : det2 (solvedA P Q) = det2 Q / det2 P := by
  have h : det2 (solvedA P Q) = solvedA P Q 0 0 * solvedA P Q 1 1 -
      solvedA P Q 0 1 * solvedA P Q 1 0 := rfl
  rw [h]
  simp only [solvedA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [div_mul_div_comm, div_mul_div_comm, div_sub_div_same,
    div_eq_div_iff (mul_ne_zero hP hP) hP]
  unfold det2
  ring

/-- Cochrane (2023), p. 420: the structural matrix `P = [[1 + σφ_x, σφ], [−κ, 1]]`. -/
def Pmat (σ κ φ φx : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1 + σ * φx, σ * φ; -κ, 1]

/-- Cochrane (2023), p. 420: the structural matrix `Q = [[1, σ], [0, β]]`. -/
def Qmat (σ β : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, σ; 0, β]

/-- `D = det P = 1 + σφ_x + σκφ`. -/
theorem det2_Pmat (σ κ φ φx : ℝ) : det2 (Pmat σ κ φ φx) = 1 + σ * φx + σ * κ * φ := by
  simp [det2, Pmat]; ring

end Cochrane.KeynesianStickyPrices.SharedTools
