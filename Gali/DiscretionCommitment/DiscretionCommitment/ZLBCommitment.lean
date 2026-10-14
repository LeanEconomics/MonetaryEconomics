/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DiscretionCommitment.ZLBDiscretion
import DiscretionCommitment.Commitment
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.LinearCombination

/-!
# Optimal policy with commitment under a zero lower bound

Galí (2015), Subsection 5.4.2, pp. 148–152.

At date 0 the central bank chooses `{x_t, π_t}` to minimise `∑ β^t (π_t² + ϑ x_t²)` subject to
the Phillips curve and the IS-plus-ZLB inequality `x_t ≤ x_{t+1} + (π_{t+1} + rⁿ_t)/σ` at every
date (p. 149). The economy is deterministic, so paths are sequences `ℕ → ℝ`; the loss is a
genuine infinite sum (`tsum`), and optimality is over all feasible paths with finite loss (a
path with non-summable loss has partial sums tending to `+∞`, `loss_partial_tendsto_top`).

## Main results

* `lagrangian_identity`, `kkt_sufficient`, `kkt_optimal`, `kkt_unique`: SUFFICIENCY — any
  feasible path satisfying the FOCs (35)–(36) with `ξ₁,₋₁ = ξ₂,₋₁ = 0`, `ξ₂ ≥ 0` and `ξ₂ i = 0`
  (with bounded multipliers and finite loss) is optimal, and it is the unique optimum: the loss
  of any other feasible path exceeds it by at least `∑ β^t ((Δπ_t)² + ϑ (Δx_t)²)`.
* `optimal_unique`: strict convexity — two optimal paths coincide.
* `γ`, `δ` and their properties are imported from `DiscretionCommitment.Commitment` (`gam`, `del`,
  `del_pos`, `del_lt_one_iff`, `del_quad`, `kappa_sq_del`).
* `post_eq37`, `post_eq38`, `post_eq39`, `post_priceLevel`, `post_eq40`, `post_second_order`,
  `post_eq41`, `post_eq42_pos`, `post_eq43_pos`, `post_unique_bounded`: the post-liftoff
  dynamics (37)–(43); with `ξ₁,t_C+1 > 0`, `x > 0` and `π > 0` after liftoff, and the closed form
  is the unique bounded solution.
* `liftoff_iff`, `Nmat_det`, `eq47`, `eq47_iff`: the liftoff-period conditions (44)–(46) and the
  matrix `M` of (47).
* `eq48_iff`, `eq49_iff`, `eq49_matrix`, `eq50_iff`: the ZLB-phase dynamics with `A`, `B`, `H`, `J`.
* `post_rate`, `post_rate_nonneg`: after liftoff `i_t = ρ + (1 − δ)(1 − σκ/ϑ) δ^{k+1} ξ`, so the
  infinitely many conditions `i_t ≥ 0` reduce to two.
* `algorithm_verification`: the algorithm of p. 152 as a verification theorem — if the candidate
  built for a guessed `t_C` has `ξ₂,t ≥ 0` on `[0, t_C]` and `i ≥ 0` at `t_C + 1, t_C + 2`, it is
  the unique optimal path, with `i_t = 0` exactly on the announced ZLB spell `[0, t_C]`.
* `equation_count`: (C5-9) the book's "`4(t_C + 2)` equations" counts (46) and `ξ₂,t_C+1 = 0`
  alongside (47)–(50), with (50) used only for `t ≤ t_C`.
-/

namespace Gali.DiscretionCommitment.ZLBCommitment

open Gali.DiscretionCommitment.ZLBDiscretion

/-! ## The commitment problem -/

/-- Galí (2015), p. 149: the constraints of the commitment problem — the Phillips curve (29)
and `x_t ≤ x_{t+1} + (1/σ)(π_{t+1} + rⁿ_t)` ((28) and (30) combined) at every date. -/
def Feasible (β κ σ : ℝ) (rn x π : ℕ → ℝ) : Prop :=
  ∀ t, NKPC β κ x π t ∧ x t ≤ ups1 σ rn x π t

/-- Galí (2015), p. 149: feasibility is (29) together with a nonnegative implied rate. -/
theorem feasible_iff {β κ σ : ℝ} (hσ : 0 < σ) {rn x π : ℕ → ℝ} :
    Feasible β κ σ rn x π ↔ ∀ t, NKPC β κ x π t ∧ 0 ≤ impliedRate σ rn x π t := by
  refine forall_congr' fun t => and_congr_right fun _ => ?_
  rw [impliedRate_eq hσ.ne']
  constructor
  · intro h; exact mul_nonneg hσ.le (by linarith)
  · intro h
    have := (mul_nonneg_iff_of_pos_left hσ).mp h
    linarith

/-- Galí (2015), p. 148: the period-`t` term `β^t (π_t² + ϑ x_t²)` of the loss. -/
noncomputable def lossTerm (β ϑ : ℝ) (x π : ℕ → ℝ) (t : ℕ) : ℝ :=
  β ^ t * (π t ^ 2 + ϑ * x t ^ 2)

/-- Galí (2015), p. 148: the loss `∑_{t ≥ 0} β^t (π_t² + ϑ x_t²)`. -/
noncomputable def loss (β ϑ : ℝ) (x π : ℕ → ℝ) : ℝ := ∑' t, lossTerm β ϑ x π t

/-- Galí (2015), p. 148: the loss terms are nonnegative. -/
theorem lossTerm_nonneg {β ϑ : ℝ} (hβ : 0 ≤ β) (hϑ : 0 ≤ ϑ) (x π : ℕ → ℝ) (t : ℕ) :
    0 ≤ lossTerm β ϑ x π t := by
  unfold lossTerm; positivity

/-- Galí (2015), p. 148: a path whose loss terms are not summable has partial losses tending to
`+∞`, so it is worse than any path with finite loss. -/
theorem loss_partial_tendsto_top {β ϑ : ℝ} (hβ : 0 ≤ β) (hϑ : 0 ≤ ϑ) {x π : ℕ → ℝ}
    (h : ¬ Summable (lossTerm β ϑ x π)) :
    Filter.Tendsto (fun n => ∑ t ∈ Finset.range n, lossTerm β ϑ x π t) Filter.atTop
      Filter.atTop :=
  (not_summable_iff_tendsto_nat_atTop_of_nonneg (lossTerm_nonneg hβ hϑ x π)).mp h

/-- Galí (2015), p. 148: `(x, π)` solves the commitment problem — it is feasible, has finite
loss, and its loss is no larger than that of any feasible path with finite loss. -/
def Optimal (β κ σ ϑ : ℝ) (rn x π : ℕ → ℝ) : Prop :=
  Feasible β κ σ rn x π ∧ Summable (lossTerm β ϑ x π) ∧
    ∀ y q, Feasible β κ σ rn y q → Summable (lossTerm β ϑ y q) → loss β ϑ x π ≤ loss β ϑ y q

/-- Galí (2015), p. 149: the lag operator with the initial conditions `ξ₋₁ = 0`. -/
def lag (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => f t

/-- Galí (2015), p. 149: `lag f (t + 1) = f t`. -/
@[simp] theorem lag_succ (f : ℕ → ℝ) (t : ℕ) : lag f (t + 1) = f t := rfl

/-- Galí (2015), p. 149: `lag f 0 = 0` (the initial conditions `ξ₁,₋₁ = ξ₂,₋₁ = 0`). -/
@[simp] theorem lag_zero (f : ℕ → ℝ) : lag f 0 = 0 := rfl

/-- Galí (2015), eq. (35), p. 149: `π_t + ξ₁,t − ξ₁,t−1 − ξ₂,t−1/(βσ) = 0`. -/
def FOC35 (β σ : ℝ) (π ξ1 ξ2 : ℕ → ℝ) (t : ℕ) : Prop :=
  π t + ξ1 t - lag ξ1 t - lag ξ2 t / (β * σ) = 0

/-- Galí (2015), eq. (36), p. 149: `ϑ x_t − κ ξ₁,t + ξ₂,t − ξ₂,t−1/β = 0`. -/
def FOC36 (β κ ϑ : ℝ) (x ξ1 ξ2 : ℕ → ℝ) (t : ℕ) : Prop :=
  ϑ * x t - κ * ξ1 t + ξ2 t - lag ξ2 t / β = 0

/-- Galí (2015), pp. 149: the KKT system of the commitment problem — feasibility, the FOCs
(35)–(36) with `ξ₁,₋₁ = ξ₂,₋₁ = 0`, and the slackness conditions `ξ₂ ≥ 0`, `ξ₂ i = 0`. -/
def KKT (β κ σ ϑ : ℝ) (rn x π ξ1 ξ2 : ℕ → ℝ) : Prop :=
  Feasible β κ σ rn x π ∧ ∀ t, FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t ∧ 0 ≤ ξ2 t ∧
    ξ2 t * impliedRate σ rn x π t = 0

/-- Galí (2015), p. 149: the Lagrangian identity (summation by parts). For a direction
`(dx, dπ)` satisfying the linearised Phillips curve, the first variation of the truncated loss
equals the inequality-multiplier terms plus a boundary term. -/
theorem lagrangian_identity {β κ σ ϑ : ℝ} (hβ : β ≠ 0) (hσ : σ ≠ 0)
    {x π ξ1 ξ2 dx dπ : ℕ → ℝ}
    (h35 : ∀ t, FOC35 β σ π ξ1 ξ2 t) (h36 : ∀ t, FOC36 β κ ϑ x ξ1 ξ2 t)
    (hd : ∀ t, dπ t = β * dπ (t + 1) + κ * dx t) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), β ^ t * (π t * dπ t + ϑ * x t * dx t) =
      ∑ s ∈ Finset.range T, β ^ s * (ξ2 s * (dx (s + 1) + dπ (s + 1) / σ - dx s)) -
        β ^ T * ξ2 T * dx T - β ^ (T + 1) * ξ1 T * dπ (T + 1) := by
  induction T with
  | zero =>
    have a := h35 0
    have b := h36 0
    simp only [FOC35, FOC36, lag_zero, zero_div, sub_zero] at a b
    simp only [zero_add, Finset.sum_range_one, Finset.range_zero, Finset.sum_empty, pow_zero,
      pow_one, one_mul, zero_sub]
    linear_combination dπ 0 * a + dx 0 * b - ξ1 0 * hd 0
  | succ T ih =>
    have a := h35 (T + 1)
    have b := h36 (T + 1)
    simp only [FOC35, FOC36, lag_succ] at a b
    have e1 : β ^ (T + 1) * (ξ2 T / (β * σ)) = β ^ T * ξ2 T / σ := by
      rw [pow_succ]; field_simp
    have e2 : β ^ (T + 1) * (ξ2 T / β) = β ^ T * ξ2 T := by
      rw [pow_succ]; field_simp
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    linear_combination β ^ (T + 1) * dπ (T + 1) * a + β ^ (T + 1) * dx (T + 1) * b -
      β ^ (T + 1) * ξ1 (T + 1) * hd (T + 1) + dπ (T + 1) * e1 + dx (T + 1) * e2

/-- Galí (2015), p. 149: if `∑ β^t a_t²` is summable-small (`β^t a_t² → 0`) and `0 ≤ β < 1`,
then `β^t |a_t| → 0`. -/
theorem tendsto_pow_mul_abs {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) {a : ℕ → ℝ}
    (h : Filter.Tendsto (fun t => β ^ t * a t ^ 2) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun t => β ^ t * |a t|) Filter.atTop (nhds 0) := by
  have hg : Filter.Tendsto (fun t => (β ^ t + β ^ t * a t ^ 2) / 2) Filter.atTop
      (nhds ((0 + 0) / 2)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ hβ1).add h).div_const 2
  rw [add_zero, zero_div] at hg
  refine squeeze_zero (fun t => by positivity) (fun t => ?_) hg
  have hp : 0 ≤ β ^ t := pow_nonneg hβ t
  have : |a t| ≤ (1 + a t ^ 2) / 2 := by
    nlinarith [sq_nonneg (|a t| - 1), sq_abs (a t)]
  nlinarith

/-- Galí (2015), p. 149: SUFFICIENCY of the KKT system (Lagrangian + convexity). If `(x, π)`
satisfies the KKT system with bounded multipliers and has finite loss, then for every feasible
`(y, q)` with finite loss, `loss (x, π) + ∑ β^t ((q_t − π_t)² + ϑ (y_t − x_t)²) ≤ loss (y, q)`. -/
theorem kkt_sufficient {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hϑ : 0 < ϑ)
    {rn x π ξ1 ξ2 : ℕ → ℝ} (hK : KKT β κ σ ϑ rn x π ξ1 ξ2)
    (hb : ∃ C, ∀ t, |ξ1 t| ≤ C ∧ |ξ2 t| ≤ C) (hs : Summable (lossTerm β ϑ x π))
    {y q : ℕ → ℝ} (hy : Feasible β κ σ rn y q) (hsy : Summable (lossTerm β ϑ y q)) :
    Summable (fun t => β ^ t * ((q t - π t) ^ 2 + ϑ * (y t - x t) ^ 2)) ∧
      loss β ϑ x π + ∑' t, β ^ t * ((q t - π t) ^ 2 + ϑ * (y t - x t) ^ 2) ≤
        loss β ϑ y q := by
  obtain ⟨hF, hK⟩ := hK
  obtain ⟨C, hC⟩ := hb
  set D : ℕ → ℝ := fun t => β ^ t * ((q t - π t) ^ 2 + ϑ * (y t - x t) ^ 2) with hDdef
  have hD0 : ∀ t, 0 ≤ D t := fun t => by simp only [hDdef]; positivity
  have hDs : Summable D := by
    refine Summable.of_nonneg_of_le hD0 (fun t => ?_) ((hsy.add hs).mul_left 2)
    simp only [hDdef, lossTerm]
    have hp : 0 ≤ β ^ t := pow_nonneg hβ.le t
    have : (q t - π t) ^ 2 + ϑ * (y t - x t) ^ 2 ≤
        2 * ((q t ^ 2 + ϑ * y t ^ 2) + (π t ^ 2 + ϑ * x t ^ 2)) := by
      nlinarith [sq_nonneg (q t + π t), sq_nonneg (y t + x t)]
    nlinarith
  refine ⟨hDs, ?_⟩
  -- the boundary terms vanish
  have hD_lim := hDs.tendsto_atTop_zero
  have hdx : Filter.Tendsto (fun t => β ^ t * |y t - x t|) Filter.atTop (nhds 0) := by
    refine tendsto_pow_mul_abs hβ.le hβ1 (squeeze_zero (fun t => by positivity) (fun t => ?_)
      (by simpa using hD_lim.div_const ϑ))
    simp only [hDdef]
    rw [le_div_iff₀ hϑ]
    have hp : 0 ≤ β ^ t := pow_nonneg hβ.le t
    nlinarith [sq_nonneg (q t - π t)]
  have hdπ : Filter.Tendsto (fun t => β ^ t * |q t - π t|) Filter.atTop (nhds 0) := by
    refine tendsto_pow_mul_abs hβ.le hβ1 (squeeze_zero (fun t => by positivity) (fun t => ?_)
      hD_lim)
    simp only [hDdef]
    have hp : 0 ≤ β ^ t := pow_nonneg hβ.le t
    nlinarith [mul_nonneg hp (mul_nonneg hϑ.le (sq_nonneg (y t - x t)))]
  set b : ℕ → ℝ := fun T => C * (β ^ T * |y T - x T|) +
    C * (β ^ (T + 1) * |q (T + 1) - π (T + 1)|) with hbdef
  have hb_lim : Filter.Tendsto (fun T => -(2 * b T)) Filter.atTop (nhds 0) := by
    have := ((hdx.const_mul C).add ((hdπ.comp (Filter.tendsto_add_atTop_nat 1)).const_mul C))
    simpa [hbdef] using (this.const_mul 2).neg
  -- partial sums
  have hlimL : Filter.Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), lossTerm β ϑ y q t -
      ∑ t ∈ Finset.range (T + 1), lossTerm β ϑ x π t - ∑ t ∈ Finset.range (T + 1), D t)
      Filter.atTop (nhds (loss β ϑ y q - loss β ϑ x π - ∑' t, D t)) := by
    have h1 := hsy.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
    have h2 := hs.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
    have h3 := hDs.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
    exact (h1.sub h2).sub h3
  have hineq : ∀ T, -(2 * b T) ≤ ∑ t ∈ Finset.range (T + 1), lossTerm β ϑ y q t -
      ∑ t ∈ Finset.range (T + 1), lossTerm β ϑ x π t - ∑ t ∈ Finset.range (T + 1), D t := by
    intro T
    have hsplit : ∑ t ∈ Finset.range (T + 1), lossTerm β ϑ y q t -
        ∑ t ∈ Finset.range (T + 1), lossTerm β ϑ x π t - ∑ t ∈ Finset.range (T + 1), D t =
        2 * ∑ t ∈ Finset.range (T + 1),
          β ^ t * (π t * (q t - π t) + ϑ * x t * (y t - x t)) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [lossTerm, hDdef]
      ring
    have hd : ∀ t, q t - π t = β * (q (t + 1) - π (t + 1)) + κ * (y t - x t) := by
      intro t
      have h1 := (hy t).1
      have h2 := (hF t).1
      unfold NKPC at h1 h2
      linarith
    have hid := lagrangian_identity hβ.ne' hσ.ne' (fun t => (hK t).1) (fun t => (hK t).2.1)
      (dx := fun t => y t - x t) (dπ := fun t => q t - π t) hd T
    rw [hsplit, hid]
    have hsum : 0 ≤ ∑ s ∈ Finset.range T, β ^ s * (ξ2 s * ((y (s + 1) - x (s + 1)) +
        (q (s + 1) - π (s + 1)) / σ - (y s - x s))) := by
      refine Finset.sum_nonneg fun s _ => mul_nonneg (pow_nonneg hβ.le s) ?_
      have hslack : ξ2 s * (ups1 σ rn x π s - x s) = 0 := by
        have h := (hK s).2.2.2
        rw [impliedRate_eq hσ.ne'] at h
        rw [mul_left_comm] at h
        rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hσ.ne'
        · exact h'
      have hfy : 0 ≤ ξ2 s * (ups1 σ rn y q s - y s) :=
        mul_nonneg (hK s).2.2.1 (by linarith [(hy s).2])
      have e : ξ2 s * ((y (s + 1) - x (s + 1)) + (q (s + 1) - π (s + 1)) / σ - (y s - x s)) =
          ξ2 s * (ups1 σ rn y q s - y s) - ξ2 s * (ups1 σ rn x π s - x s) := by
        unfold ups1; ring
      rw [e, hslack]
      linarith
    have hC1 := (hC T).2
    have hC2 := (hC T).1
    have hp : 0 ≤ β ^ T := pow_nonneg hβ.le T
    have hp1 : 0 ≤ β ^ (T + 1) := pow_nonneg hβ.le (T + 1)
    have k1 : |β ^ T * ξ2 T * (y T - x T)| ≤ C * (β ^ T * |y T - x T|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hp]
      have := abs_nonneg (y T - x T)
      nlinarith [mul_nonneg (sub_nonneg.mpr hC1) (mul_nonneg hp this)]
    have k2 : |β ^ (T + 1) * ξ1 T * (q (T + 1) - π (T + 1))| ≤
        C * (β ^ (T + 1) * |q (T + 1) - π (T + 1)|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hp1]
      have := abs_nonneg (q (T + 1) - π (T + 1))
      nlinarith [mul_nonneg (sub_nonneg.mpr hC2) (mul_nonneg hp1 this)]
    have k3 := le_abs_self (β ^ T * ξ2 T * (y T - x T))
    have k4 := le_abs_self (β ^ (T + 1) * ξ1 T * (q (T + 1) - π (T + 1)))
    simp only [hbdef]
    linarith
  have := le_of_tendsto_of_tendsto' hb_lim hlimL hineq
  unfold loss at this ⊢
  linarith

/-- Galí (2015), p. 149: a KKT path with bounded multipliers and finite loss is optimal. -/
theorem kkt_optimal {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hϑ : 0 < ϑ)
    {rn x π ξ1 ξ2 : ℕ → ℝ} (hK : KKT β κ σ ϑ rn x π ξ1 ξ2)
    (hb : ∃ C, ∀ t, |ξ1 t| ≤ C ∧ |ξ2 t| ≤ C) (hs : Summable (lossTerm β ϑ x π)) :
    Optimal β κ σ ϑ rn x π := by
  refine ⟨hK.1, hs, fun y q hy hsy => ?_⟩
  obtain ⟨hDs, hle⟩ := kkt_sufficient hβ hβ1 hσ hϑ hK hb hs hy hsy
  have : 0 ≤ ∑' t, β ^ t * ((q t - π t) ^ 2 + ϑ * (y t - x t) ^ 2) :=
    tsum_nonneg fun t => by positivity
  linarith

/-- Galí (2015), p. 149: a nonnegative summable sequence with nonpositive sum vanishes. -/
theorem eq_zero_of_tsum_nonpos {D : ℕ → ℝ} (h0 : ∀ t, 0 ≤ D t) (hs : Summable D)
    (h : ∑' t, D t ≤ 0) (t : ℕ) : D t = 0 :=
  le_antisymm ((hs.le_tsum t fun j _ => h0 j).trans h) (h0 t)

/-- Galí (2015), p. 149: a weighted sum of squares `β^t (a² + ϑ b²)` vanishes only at
`a = b = 0`. -/
theorem sq_terms_zero {β ϑ a b : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) (t : ℕ)
    (h : β ^ t * (a ^ 2 + ϑ * b ^ 2) = 0) : a = 0 ∧ b = 0 := by
  have hp : 0 < β ^ t := pow_pos hβ t
  have h2 : a ^ 2 + ϑ * b ^ 2 = 0 := by
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hp.ne'
    · exact h'
  have ha : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg hϑ.le (sq_nonneg b)]
  have hb : ϑ * b ^ 2 = 0 := by linarith
  exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ha,
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      ((mul_eq_zero.mp hb).resolve_left hϑ.ne')⟩

/-- Galí (2015), p. 149: UNIQUENESS — a KKT path (bounded multipliers, finite loss) is the
only feasible path with finite loss whose loss is no larger. -/
theorem kkt_unique {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hϑ : 0 < ϑ)
    {rn x π ξ1 ξ2 : ℕ → ℝ} (hK : KKT β κ σ ϑ rn x π ξ1 ξ2)
    (hb : ∃ C, ∀ t, |ξ1 t| ≤ C ∧ |ξ2 t| ≤ C) (hs : Summable (lossTerm β ϑ x π))
    {y q : ℕ → ℝ} (hy : Feasible β κ σ rn y q) (hsy : Summable (lossTerm β ϑ y q))
    (hle : loss β ϑ y q ≤ loss β ϑ x π) : y = x ∧ q = π := by
  obtain ⟨hDs, hle2⟩ := kkt_sufficient hβ hβ1 hσ hϑ hK hb hs hy hsy
  have hz := eq_zero_of_tsum_nonpos (fun t => by positivity) hDs (by linarith)
  refine ⟨funext fun t => ?_, funext fun t => ?_⟩
  · have := (sq_terms_zero hβ hϑ t (hz t)).2; linarith
  · have := (sq_terms_zero hβ hϑ t (hz t)).1; linarith

/-- Galí (2015), p. 149: STRICT CONVEXITY — two optimal paths of the commitment problem
coincide (the midpoint would do strictly better otherwise). -/
theorem optimal_unique {β κ σ ϑ : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) {rn x1 π1 x2 π2 : ℕ → ℝ}
    (h1 : Optimal β κ σ ϑ rn x1 π1) (h2 : Optimal β κ σ ϑ rn x2 π2) : x1 = x2 ∧ π1 = π2 := by
  obtain ⟨hF1, hs1, ho1⟩ := h1
  obtain ⟨hF2, hs2, ho2⟩ := h2
  set xm : ℕ → ℝ := fun t => (x1 t + x2 t) / 2 with hxm
  set πm : ℕ → ℝ := fun t => (π1 t + π2 t) / 2 with hπm
  have hFm : Feasible β κ σ rn xm πm := by
    intro t
    obtain ⟨a1, b1⟩ := hF1 t
    obtain ⟨a2, b2⟩ := hF2 t
    unfold NKPC at a1 a2
    refine ⟨?_, ?_⟩
    · unfold NKPC; simp only [hxm, hπm]; linarith
    · have e : ups1 σ rn xm πm t = (ups1 σ rn x1 π1 t + ups1 σ rn x2 π2 t) / 2 := by
        simp only [ups1, hxm, hπm]; ring
      rw [e]; simp only [hxm]; linarith
  set D : ℕ → ℝ := fun t => β ^ t * ((π1 t - π2 t) ^ 2 + ϑ * (x1 t - x2 t) ^ 2) with hDdef
  have hD0 : ∀ t, 0 ≤ D t := fun t => by simp only [hDdef]; positivity
  have hDs : Summable D := by
    refine Summable.of_nonneg_of_le hD0 (fun t => ?_) ((hs1.add hs2).mul_left 2)
    simp only [hDdef, lossTerm]
    have hp : 0 ≤ β ^ t := pow_nonneg hβ.le t
    have : (π1 t - π2 t) ^ 2 + ϑ * (x1 t - x2 t) ^ 2 ≤
        2 * ((π1 t ^ 2 + ϑ * x1 t ^ 2) + (π2 t ^ 2 + ϑ * x2 t ^ 2)) := by
      nlinarith [sq_nonneg (π1 t + π2 t), sq_nonneg (x1 t + x2 t)]
    nlinarith
  have hterm : ∀ t, lossTerm β ϑ xm πm t =
      (lossTerm β ϑ x1 π1 t + lossTerm β ϑ x2 π2 t) / 2 - D t / 4 := by
    intro t; simp only [lossTerm, hDdef, hxm, hπm]; ring
  have hsm : Summable (lossTerm β ϑ xm πm) := by
    rw [show lossTerm β ϑ xm πm = fun t =>
      (lossTerm β ϑ x1 π1 t + lossTerm β ϑ x2 π2 t) / 2 - D t / 4 from funext hterm]
    exact ((hs1.add hs2).div_const 2).sub (hDs.div_const 4)
  have hlm : loss β ϑ xm πm = (loss β ϑ x1 π1 + loss β ϑ x2 π2) / 2 - (∑' t, D t) / 4 := by
    unfold loss
    rw [show lossTerm β ϑ xm πm = fun t =>
      (lossTerm β ϑ x1 π1 t + lossTerm β ϑ x2 π2 t) / 2 - D t / 4 from funext hterm]
    rw [((hs1.add hs2).div_const 2).tsum_sub (hDs.div_const 4), tsum_div_const,
      tsum_div_const, hs1.tsum_add hs2]
  have l12 := ho1 x2 π2 hF2 hs2
  have l21 := ho2 x1 π1 hF1 hs1
  have l1m := ho1 xm πm hFm hsm
  have hz := eq_zero_of_tsum_nonpos hD0 hDs (by linarith)
  refine ⟨funext fun t => ?_, funext fun t => ?_⟩
  · have := (sq_terms_zero hβ hϑ t (hz t)).2; linarith
  · have := (sq_terms_zero hβ hϑ t (hz t)).1; linarith

/-! ## Post-liftoff dynamics (37)–(43) -/

/-- Galí (2015), eq. (42), p. 150: `x_{t_C+2+k} = κ δ^{k+1} ξ / ϑ`, `ξ = ξ₁,t_C+1`. -/
noncomputable def postX (β κ ϑ ξ : ℝ) (k : ℕ) : ℝ := κ * Commitment.del β κ ϑ ^ (k + 1) * ξ / ϑ

/-- Galí (2015), eq. (43), p. 150: `π_{t_C+2+k} = (1 − δ) δ^k ξ`. -/
noncomputable def postPi (β κ ϑ ξ : ℝ) (k : ℕ) : ℝ :=
  (1 - Commitment.del β κ ϑ) * Commitment.del β κ ϑ ^ k * ξ

/-- Galí (2015), pp. 149–150: the multiplier `ξ₁,t_C+1+k = δ^k ξ` (from (38) and (42)). -/
noncomputable def postXi (β κ ϑ ξ : ℝ) (k : ℕ) : ℝ := Commitment.del β κ ϑ ^ k * ξ

/-- Galí (2015), eq. (41), p. 150: the price-level gap `p̂_{t_C+1+k} = p_{t_C+1+k} − p* =
−δ^k ξ`. -/
noncomputable def postP (β κ ϑ ξ : ℝ) (k : ℕ) : ℝ := -(Commitment.del β κ ϑ ^ k * ξ)

/-- Galí (2015), eq. (37), p. 149: `π_t + ξ₁,t − ξ₁,t−1 = 0` after liftoff. -/
theorem post_eq37 (β κ ϑ ξ : ℝ) (k : ℕ) :
    postPi β κ ϑ ξ k + postXi β κ ϑ ξ (k + 1) - postXi β κ ϑ ξ k = 0 := by
  unfold postPi postXi; ring

/-- Galí (2015), eq. (38), p. 149: `ϑ x_t − κ ξ₁,t = 0` after liftoff. -/
theorem post_eq38 {β κ ϑ : ℝ} (hϑ : ϑ ≠ 0) (ξ : ℝ) (k : ℕ) :
    ϑ * postX β κ ϑ ξ k - κ * postXi β κ ϑ ξ (k + 1) = 0 := by
  unfold postX postXi; field_simp; ring

/-- Galí (2015), eq. (39), p. 149: the Phillips curve `π_t = β π_{t+1} + κ x_t` after liftoff. -/
theorem post_eq39 {β κ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (ξ : ℝ) (k : ℕ) :
    postPi β κ ϑ ξ k = β * postPi β κ ϑ ξ (k + 1) + κ * postX β κ ϑ ξ k := by
  have key : κ ^ 2 * Commitment.del β κ ϑ =
      ϑ * (1 - Commitment.del β κ ϑ) * (1 - β * Commitment.del β κ ϑ) := by
    have h := Commitment.kappa_sq_del (κ := κ) hβ hβ1 hϑ
    rw [div_eq_iff hϑ.ne'] at h
    linear_combination h
  unfold postPi postX
  set δ := Commitment.del β κ ϑ
  field_simp
  linear_combination (-(δ ^ k * ξ)) * key

/-- Galí (2015), p. 150: (37) and `p_t = p_{t−1} + π_t` make `p_t + ξ₁,t` constant after
liftoff, equal to `p* ≡ p_{t_C+1} + ξ₁,t_C+1` (here `L = t_C + 1`). -/
theorem post_priceLevel {L : ℕ} {p π ξ1 : ℕ → ℝ}
    (hp : ∀ k, p (L + (k + 1)) = p (L + k) + π (L + (k + 1)))
    (h37 : ∀ k, π (L + (k + 1)) + ξ1 (L + (k + 1)) - ξ1 (L + k) = 0) (k : ℕ) :
    p (L + k) + ξ1 (L + k) = p L + ξ1 L := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have a := hp k
    have b := h37 k
    linarith

/-- Galí (2015), eq. (40), p. 150: (37), (38) give `x_t = −(κ/ϑ)(p_t − p*)` after liftoff. -/
theorem post_eq40 {κ ϑ : ℝ} (hϑ : ϑ ≠ 0) {L : ℕ} {p x π ξ1 : ℕ → ℝ}
    (hp : ∀ k, p (L + (k + 1)) = p (L + k) + π (L + (k + 1)))
    (h37 : ∀ k, π (L + (k + 1)) + ξ1 (L + (k + 1)) - ξ1 (L + k) = 0)
    (h38 : ∀ k, ϑ * x (L + (k + 1)) - κ * ξ1 (L + (k + 1)) = 0) (k : ℕ) :
    x (L + (k + 1)) = -(κ / ϑ) * (p (L + (k + 1)) - (p L + ξ1 L)) := by
  have h1 := post_priceLevel hp h37 (k + 1)
  have h2 := h38 k
  rw [← h1]
  field_simp
  linarith

/-- Galí (2015), p. 150: (39) and (40) give the second-order equation
`p̂_t = γ p̂_{t−1} + γ β p̂_{t+1}` (with `a, b, c` the gaps at `t − 1, t, t + 1`). -/
theorem post_second_order {β κ ϑ : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) {a b c x πt πt1 : ℝ}
    (hπ : πt = b - a) (hπ1 : πt1 = c - b) (hx : x = -(κ / ϑ) * b) (h39 : πt = β * πt1 + κ * x) :
    b = Commitment.gam β κ ϑ * a + Commitment.gam β κ ϑ * β * c := by
  subst hπ hπ1 hx
  unfold Commitment.gam
  have hD : 0 < ϑ * (1 + β) + κ ^ 2 := by positivity
  field_simp at h39
  have hm : b * (ϑ * (1 + β) + κ ^ 2) = ϑ * a + ϑ * β * c := by linear_combination h39
  field_simp
  linear_combination hm

/-- Galí (2015), eq. (41), p. 150: `p̂_{t+1} = δ p̂_t` after liftoff, with `p̂_{t_C+1} = −ξ`. -/
theorem post_eq41 (β κ ϑ ξ : ℝ) (k : ℕ) :
    postP β κ ϑ ξ (k + 1) = Commitment.del β κ ϑ * postP β κ ϑ ξ k ∧ postP β κ ϑ ξ 0 = -ξ := by
  unfold postP; constructor <;> ring

/-- Galí (2015), p. 150: the closed form `p̂ = −δ^k ξ` solves the second-order equation. -/
theorem postP_second_order {β κ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (ξ : ℝ) (k : ℕ) :
    postP β κ ϑ ξ (k + 1) =
      Commitment.gam β κ ϑ * postP β κ ϑ ξ k +
        Commitment.gam β κ ϑ * β * postP β κ ϑ ξ (k + 2) := by
  have h := Commitment.del_quad (κ := κ) hβ hβ1 hϑ
  unfold postP
  linear_combination (Commitment.del β κ ϑ ^ k * ξ) * h

/-- Galí (2015), eqs. (40)–(42), p. 150: `x_{t_C+2+k} = −(κ/ϑ) p̂_{t_C+2+k}` and
`p̂_{t_C+2+k} = −δ^{k+1} ξ`. -/
theorem post_eq40_closed {β κ ϑ : ℝ} (hϑ : ϑ ≠ 0) (ξ : ℝ) (k : ℕ) :
    postX β κ ϑ ξ k = -(κ / ϑ) * postP β κ ϑ ξ (k + 1) := by
  unfold postX postP; field_simp

/-- Galí (2015), eq. (42), p. 150: with `ξ₁,t_C+1 > 0`, the output gap is positive after
liftoff. -/
theorem post_eq42_pos {β κ ϑ ξ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hϑ : 0 < ϑ) (hξ : 0 < ξ)
    (k : ℕ) : 0 < postX β κ ϑ ξ k := by
  have := Commitment.del_pos (κ := κ) hβ hϑ
  unfold postX; positivity

/-- Galí (2015), eq. (43), p. 150: with `ξ₁,t_C+1 > 0`, inflation is positive after liftoff. -/
theorem post_eq43_pos {β κ ϑ ξ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    (hξ : 0 < ξ)
    (k : ℕ) : 0 < postPi β κ ϑ ξ k := by
  have h0 := Commitment.del_pos (κ := κ) hβ hϑ
  have h1 : 0 < 1 - Commitment.del β κ ϑ := by
    linarith [(Commitment.del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne']
  unfold postPi; positivity

/-- Galí (2015), p. 150: inflation and the output gap converge to zero after liftoff. -/
theorem post_tendsto_zero {β κ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) (ξ : ℝ) :
    Filter.Tendsto (postX β κ ϑ ξ) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (postPi β κ ϑ ξ) Filter.atTop (nhds 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (Commitment.del_pos (κ := κ) hβ hϑ).le
    ((Commitment.del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne')
  have h1 := h.comp (Filter.tendsto_add_atTop_nat 1)
  refine ⟨?_, ?_⟩
  · have := ((h1.const_mul κ).mul_const ξ).div_const ϑ
    rw [mul_zero, zero_mul, zero_div] at this
    exact this
  · have := (h.const_mul (1 - Commitment.del β κ ϑ)).mul_const ξ
    rw [mul_zero, zero_mul] at this
    exact this

/-- Galí (2015), p. 150: UNIQUENESS of the post-liftoff path — among solutions of (37)–(39)
for `t ≥ t_C + 2` with a bounded output gap, the closed form (41)–(43) is the only one
(`L = t_C + 1`, `ξ = ξ₁,L`). -/
theorem post_unique_bounded {β κ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    {L : ℕ} {x π ξ1 : ℕ → ℝ}
    (h37 : ∀ k, π (L + (k + 1)) + ξ1 (L + (k + 1)) - ξ1 (L + k) = 0)
    (h38 : ∀ k, ϑ * x (L + (k + 1)) - κ * ξ1 (L + (k + 1)) = 0)
    (h39 : ∀ k, π (L + (k + 1)) = β * π (L + (k + 2)) + κ * x (L + (k + 1)))
    (hb : ∃ C, ∀ t, |x t| ≤ C) (k : ℕ) :
    ξ1 (L + k) = postXi β κ ϑ (ξ1 L) k ∧ x (L + (k + 1)) = postX β κ ϑ (ξ1 L) k ∧
      π (L + (k + 1)) = postPi β κ ϑ (ξ1 L) k := by
  obtain ⟨C, hC⟩ := hb
  have hδ0 := Commitment.del_pos (κ := κ) hβ hϑ
  have hδ1 := (Commitment.del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne'
  have key : κ ^ 2 * Commitment.del β κ ϑ =
      ϑ * (1 - Commitment.del β κ ϑ) * (1 - β * Commitment.del β κ ϑ) := by
    have h := Commitment.kappa_sq_del (κ := κ) hβ hβ1 hϑ
    rw [div_eq_iff hϑ.ne'] at h
    linear_combination h
  set δ := Commitment.del β κ ϑ with hδ
  set q : ℕ → ℝ := fun k => ξ1 (L + k) with hq
  have hπq : ∀ k, π (L + (k + 1)) = q k - q (k + 1) := fun k => by
    simp only [hq]; linarith [h37 k]
  have hxq : ∀ k, ϑ * x (L + (k + 1)) = κ * q (k + 1) := fun k => by
    simp only [hq]; linarith [h38 k]
  have hrec : ∀ k, ϑ * (q k - q (k + 1)) = ϑ * β * (q (k + 1) - q (k + 2)) +
      κ ^ 2 * q (k + 1) := by
    intro k
    have a := h39 k
    rw [hπq k, show L + (k + 2) = L + (k + 1 + 1) by omega, hπq (k + 1)] at a
    have b := hxq k
    linear_combination ϑ * a + κ * b
  set w : ℕ → ℝ := fun k => q (k + 1) - δ * q k with hw
  have hstep : ∀ k, β * δ * w (k + 1) = w k := by
    intro k
    apply mul_left_cancel₀ hϑ.ne'
    simp only [hw]
    linear_combination δ * hrec k + q (k + 1) * key
  -- bounds
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  set B := ϑ * C / κ + |q 0| with hB
  have hqB : ∀ k, |q k| ≤ B := by
    intro k
    rcases k with _ | k
    · have : 0 ≤ ϑ * C / κ := by positivity
      simp only [hB]; linarith
    · have e : q (k + 1) = ϑ * x (L + (k + 1)) / κ := by
        rw [hxq k]; field_simp
      rw [e, abs_div, abs_mul, abs_of_pos hϑ, abs_of_pos hκ]
      have h1 : ϑ * |x (L + (k + 1))| / κ ≤ ϑ * C / κ := by
        gcongr; exact hC _
      have := abs_nonneg (q 0)
      simp only [hB]; linarith
  have hwB : ∀ k, |w k| ≤ (1 + δ) * B := by
    intro k
    simp only [hw]
    calc |q (k + 1) - δ * q k| ≤ |q (k + 1)| + |δ * q k| := abs_sub _ _
      _ = |q (k + 1)| + δ * |q k| := by rw [abs_mul, abs_of_pos hδ0]
      _ ≤ B + δ * B := by gcongr <;> exact hqB _
      _ = (1 + δ) * B := by ring
  have hiter : ∀ k, w 0 = (β * δ) ^ k * w k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [ih, ← hstep k, pow_succ]; ring
  have hβδ0 : 0 ≤ β * δ := by positivity
  have hβδ1 : β * δ < 1 := by nlinarith
  have hw0 : w 0 = 0 := by
    have hlim : Filter.Tendsto (fun k => (β * δ) ^ k * ((1 + δ) * B)) Filter.atTop
        (nhds (0 * ((1 + δ) * B))) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hβδ0 hβδ1).mul_const _
    rw [zero_mul] at hlim
    have hle : ∀ k, |w 0| ≤ (β * δ) ^ k * ((1 + δ) * B) := by
      intro k
      rw [hiter k, abs_mul, abs_of_nonneg (pow_nonneg hβδ0 k)]
      exact mul_le_mul_of_nonneg_left (hwB k) (pow_nonneg hβδ0 k)
    have := ge_of_tendsto' hlim hle
    exact abs_nonpos_iff.mp this
  have hwz : ∀ k, w k = 0 := by
    intro k
    induction k with
    | zero => exact hw0
    | succ k ih =>
      have := hstep k
      rw [ih] at this
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (by positivity)
      · exact h
  have hqk : ∀ k, q k = δ ^ k * q 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hwz k
      simp only [hw] at this
      rw [pow_succ]; linear_combination this + δ * ih
  have hq0 : q 0 = ξ1 L := by simp [hq]
  refine ⟨?_, ?_, ?_⟩
  · have := hqk k; simp only [hq, postXi] at this ⊢; rw [this, ← hq0]
  · have e := hxq k
    rw [hqk (k + 1), hq0] at e
    unfold postX
    field_simp
    linear_combination e
  · rw [hπq k, hqk k, hqk (k + 1), hq0]
    unfold postPi
    ring

/-! ## The liftoff period (44)–(47) -/

/-- Galí (2015), eq. (44), p. 150: `π_{t_C+1} + ξ₁,t_C+1 − ξ₁,t_C − ξ₂,t_C/(βσ) = 0` (eq. (35)
at `t_C + 1` with `ξ₂,t_C+1 = 0`). -/
def Eq44 (β σ xiL πL xi1c xi2c : ℝ) : Prop := πL + xiL - xi1c - xi2c / (β * σ) = 0

/-- Galí (2015), eq. (45), p. 150: `ϑ x_{t_C+1} − κ ξ₁,t_C+1 − ξ₂,t_C/β = 0` (eq. (36) at
`t_C + 1` with `ξ₂,t_C+1 = 0`). -/
def Eq45 (β κ ϑ xiL xL xi2c : ℝ) : Prop := ϑ * xL - κ * xiL - xi2c / β = 0

/-- Galí (2015), eq. (46), p. 150: `π_{t_C+1} = β (1 − δ) ξ₁,t_C+1 + κ x_{t_C+1}` (eq. (29) at
`t_C + 1` with `π_{t_C+2} = (1 − δ) ξ₁,t_C+1` from (43)). -/
def Eq46 (β κ ϑ xiL xL πL : ℝ) : Prop := πL = β * (1 - Commitment.del β κ ϑ) * xiL + κ * xL

/-- Galí (2015), p. 151: the left matrix of (47),
`N = [−κ, 1 + β(1 − δ); β(1 − δ) + κ²/ϑ, −κ/ϑ]`. -/
noncomputable def Nmat (β κ ϑ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-κ, 1 + β * (1 - Commitment.del β κ ϑ); β * (1 - Commitment.del β κ ϑ) + κ ^ 2 / ϑ, -κ / ϑ]

/-- Galí (2015), p. 151: the right matrix of (47), `K = [β(1 − δ), (1 − δ)/σ; 0, (1 − δ)/ϑ]`. -/
noncomputable def Kmat (β κ σ ϑ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![β * (1 - Commitment.del β κ ϑ), (1 - Commitment.del β κ ϑ) / σ;
    0, (1 - Commitment.del β κ ϑ) / ϑ]

/-- Galí (2015), p. 151: `M ≡ N⁻¹ K`. -/
noncomputable def Mmat (β κ σ ϑ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := (Nmat β κ ϑ)⁻¹ * Kmat β κ σ ϑ

/-- Galí (2015), p. 151: `det N = −β(1 − δ)(1 + β(1 − δ) + κ²/ϑ) ≠ 0`, so `M` is well defined. -/
theorem Nmat_det {β κ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) :
    (Nmat β κ ϑ).det = -(β * (1 - Commitment.del β κ ϑ) *
      (1 + β * (1 - Commitment.del β κ ϑ) + κ ^ 2 / ϑ)) ∧
      (Nmat β κ ϑ).det ≠ 0 := by
  have h1 : 0 < 1 - Commitment.del β κ ϑ := by
    linarith [(Commitment.del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne']
  have e : (Nmat β κ ϑ).det =
      -(β * (1 - Commitment.del β κ ϑ) * (1 + β * (1 - Commitment.del β κ ϑ) + κ ^ 2 / ϑ)) := by
    rw [Nmat, Matrix.det_fin_two_of]
    field_simp
    ring
  refine ⟨e, ?_⟩
  rw [e, neg_ne_zero]
  positivity

/-- Galí (2015), pp. 150–151: (44)–(46) are equivalent to the two rows of `N (x, π)' = K ξ`
together with `ξ₁,t_C+1 = (π − κ x) / (β (1 − δ))` (eliminating `ξ₁,t_C+1` with (46)). -/
theorem liftoff_iff {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hϑ : 0 < ϑ)
    (xiL xL πL xi1c xi2c : ℝ) :
    (Eq44 β σ xiL πL xi1c xi2c ∧ Eq45 β κ ϑ xiL xL xi2c ∧ Eq46 β κ ϑ xiL xL πL) ↔
      (-κ * xL + (1 + β * (1 - Commitment.del β κ ϑ)) * πL =
          β * (1 - Commitment.del β κ ϑ) * xi1c + (1 - Commitment.del β κ ϑ) / σ * xi2c ∧
        (β * (1 - Commitment.del β κ ϑ) + κ ^ 2 / ϑ) * xL + -κ / ϑ * πL =
          (1 - Commitment.del β κ ϑ) / ϑ * xi2c ∧
        xiL = (πL - κ * xL) / (β * (1 - Commitment.del β κ ϑ))) := by
  have h1 : 0 < 1 - Commitment.del β κ ϑ := by
    linarith [(Commitment.del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne']
  unfold Eq44 Eq45 Eq46
  set d := Commitment.del β κ ϑ
  have ha : β * (1 - d) ≠ 0 := by positivity
  constructor
  · rintro ⟨a, b, c⟩
    have hxi : xiL = (πL - κ * xL) / (β * (1 - d)) := by
      rw [eq_div_iff ha]; linarith
    refine ⟨?_, ?_, hxi⟩
    · have e : β * (1 - d) * (xi2c / (β * σ)) = (1 - d) / σ * xi2c := by
        field_simp
      linear_combination β * (1 - d) * a + c + e
    · rw [hxi] at b
      field_simp at b
      have hm : (β * (1 - d) * ϑ + κ ^ 2) * xL - κ * πL = (1 - d) * xi2c := by
        linear_combination b
      field_simp
      linear_combination hm
  · rintro ⟨a, b, c⟩
    have c' : β * (1 - d) * xiL = πL - κ * xL := by rw [c]; field_simp
    refine ⟨?_, ?_, by linarith⟩
    · have e : β * (1 - d) * (xi2c / (β * σ)) = (1 - d) / σ * xi2c := by
        field_simp
      apply mul_left_cancel₀ ha
      linear_combination a + c' - e
    · apply mul_left_cancel₀ ha
      have e : β * (1 - d) * (xi2c / β) = (1 - d) * xi2c := by field_simp
      field_simp at b
      linear_combination b - κ * c' - e

/-- Galí (2015), p. 151: `N (x, π)'` written out. -/
theorem Nmat_mulVec (β κ ϑ xL πL : ℝ) :
    Matrix.mulVec (Nmat β κ ϑ) ![xL, πL] =
      ![-κ * xL + (1 + β * (1 - Commitment.del β κ ϑ)) * πL,
        (β * (1 - Commitment.del β κ ϑ) + κ ^ 2 / ϑ) * xL + -κ / ϑ * πL] := by
  ext j
  fin_cases j <;> simp [Nmat] <;> ring

/-- Galí (2015), p. 151: `K (ξ₁,t_C, ξ₂,t_C)'` written out. -/
theorem Kmat_mulVec (β κ σ ϑ a b : ℝ) :
    Matrix.mulVec (Kmat β κ σ ϑ) ![a, b] =
      ![β * (1 - Commitment.del β κ ϑ) * a + (1 - Commitment.del β κ ϑ) / σ * b,
        (1 - Commitment.del β κ ϑ) / ϑ * b] := by
  ext j
  fin_cases j <;> simp [Kmat] <;> ring

/-- Galí (2015), eq. (47), p. 151: (44)–(46) hold iff `(x_{t_C+1}, π_{t_C+1})' =
M (ξ₁,t_C, ξ₂,t_C)'` and `ξ₁,t_C+1 = (π_{t_C+1} − κ x_{t_C+1}) / (β (1 − δ))`. -/
theorem eq47_iff {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hϑ : 0 < ϑ)
    (xiL xL πL xi1c xi2c : ℝ) :
    (Eq44 β σ xiL πL xi1c xi2c ∧ Eq45 β κ ϑ xiL xL xi2c ∧ Eq46 β κ ϑ xiL xL πL) ↔
      (![xL, πL] = Matrix.mulVec (Mmat β κ σ ϑ) ![xi1c, xi2c] ∧
        xiL = (πL - κ * xL) / (β * (1 - Commitment.del β κ ϑ))) := by
  rw [liftoff_iff hβ hβ1 hκ hσ hϑ]
  have hU : IsUnit (Nmat β κ ϑ).det := isUnit_iff_ne_zero.mpr (Nmat_det hβ hβ1 hκ hϑ).2
  have hNK : (-κ * xL + (1 + β * (1 - Commitment.del β κ ϑ)) * πL =
          β * (1 - Commitment.del β κ ϑ) * xi1c + (1 - Commitment.del β κ ϑ) / σ * xi2c ∧
        (β * (1 - Commitment.del β κ ϑ) + κ ^ 2 / ϑ) * xL + -κ / ϑ * πL =
          (1 - Commitment.del β κ ϑ) / ϑ * xi2c) ↔
      Matrix.mulVec (Nmat β κ ϑ) ![xL, πL] = Matrix.mulVec (Kmat β κ σ ϑ) ![xi1c, xi2c] := by
    rw [Nmat_mulVec, Kmat_mulVec]
    constructor
    · rintro ⟨a, b⟩
      ext j
      fin_cases j
      · exact a
      · exact b
    · intro h
      exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
  have hM : Matrix.mulVec (Nmat β κ ϑ) ![xL, πL] = Matrix.mulVec (Kmat β κ σ ϑ) ![xi1c, xi2c] ↔
      ![xL, πL] = Matrix.mulVec (Mmat β κ σ ϑ) ![xi1c, xi2c] := by
    constructor
    · intro h
      rw [Mmat, ← Matrix.mulVec_mulVec, ← h, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec]
    · intro h
      rw [h, Mmat, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU,
        Matrix.one_mul]
  rw [← hM, ← hNK, and_assoc]

/-- Galí (2015), eq. (47), p. 151: (44)–(46) imply `(x_{t_C+1}, π_{t_C+1})' = M (ξ₁,t_C, ξ₂,t_C)'`.
-/
theorem eq47 {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hϑ : 0 < ϑ)
    {xiL xL πL xi1c xi2c : ℝ}
    (h : Eq44 β σ xiL πL xi1c xi2c ∧ Eq45 β κ ϑ xiL xL xi2c ∧ Eq46 β κ ϑ xiL xL πL) :
    ![xL, πL] = Matrix.mulVec (Mmat β κ σ ϑ) ![xi1c, xi2c] :=
  ((eq47_iff hβ hβ1 hκ hσ hϑ xiL xL πL xi1c xi2c).mp h).1

/-! ## The ZLB phase (48)–(50) -/

/-- Galí (2015), eq. (48), p. 151: on `[0, t_Z]` with `i_t = 0`, the system is (34):
`(x_t, π_t)' = A (x_{t+1}, π_{t+1})' − B ε` (restated from `eq34_iff`). -/
theorem eq48_iff {β κ σ η ρ : ℝ} (hσ : σ ≠ 0) {tZ t : ℕ} (ht : t ≤ tZ) {x π i : ℕ → ℝ} :
    (NKPC β κ x π t ∧ DIS σ (natRate ρ η tZ) x π i t ∧ i t = 0) ↔
      (i t = 0 ∧ (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1))) :=
  eq34_iff hσ ht

/-- Galí (2015), eq. (49), p. 151: on `(t_Z, t_C]` with `i_t = 0` and `rⁿ_t = ρ`, the system is
`(x_t, π_t)' = A (x_{t+1}, π_{t+1})' + B ρ` (`backStep` with drop `−ρ`). -/
theorem eq49_iff {β κ σ η ρ : ℝ} (hσ : σ ≠ 0) {tZ t : ℕ} (ht : tZ < t) {x π i : ℕ → ℝ} :
    (NKPC β κ x π t ∧ DIS σ (natRate ρ η tZ) x π i t ∧ i t = 0) ↔
      (i t = 0 ∧ (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1))) := by
  rw [dis_iff hσ]
  unfold NKPC impliedRate backStep
  rw [natRate_of_lt ht, Prod.ext_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hx : x t = x (t + 1) + π (t + 1) / σ - -ρ / σ := by
      rw [h3] at h2
      field_simp
      linarith
    refine ⟨h3, hx, ?_⟩
    simp only
    rw [h1, hx]
    ring
  · rintro ⟨h3, hx, hπ⟩
    simp only at hx hπ
    refine ⟨?_, ?_, h3⟩
    · rw [hπ, hx]; ring
    · rw [h3, hx]; field_simp; ring

/-- Galí (2015), eq. (49), p. 151: the matrix form `A s + B ρ`. -/
theorem eq49_matrix (β κ σ ρ : ℝ) (s : ℝ × ℝ) :
    ![(backStep β κ σ (-ρ) s).1, (backStep β κ σ (-ρ) s).2] =
      Matrix.mulVec (Amat β κ σ) ![s.1, s.2] + ρ • Bvec κ σ := by
  rw [eq34_matrix, neg_smul, sub_neg_eq_add]

/-- Galí (2015), p. 151: `H ≡ [1, 1/(βσ); κ, (1/β)(1 + κ/σ)]`. -/
noncomputable def Hmat (β κ σ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 1 / (β * σ); κ, 1 / β * (1 + κ / σ)]

/-- Galí (2015), p. 151: `J ≡ [0, 1; ϑ, κ]`. -/
def Jmat (κ ϑ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; ϑ, κ]

/-- Galí (2015), eq. (50), p. 151: the FOCs (35)–(36) are
`(ξ₁,t, ξ₂,t)' = H (ξ₁,t−1, ξ₂,t−1)' − J (x_t, π_t)'`, with `ξ₁,₋₁ = ξ₂,₋₁ = 0`. -/
theorem eq50_iff {β κ σ ϑ : ℝ} {x π ξ1 ξ2 : ℕ → ℝ} (t : ℕ) :
    (FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t) ↔
      ![ξ1 t, ξ2 t] = Matrix.mulVec (Hmat β κ σ) ![lag ξ1 t, lag ξ2 t] -
        Matrix.mulVec (Jmat κ ϑ) ![x t, π t] := by
  have hv : Matrix.mulVec (Hmat β κ σ) ![lag ξ1 t, lag ξ2 t] -
      Matrix.mulVec (Jmat κ ϑ) ![x t, π t] =
      ![lag ξ1 t + lag ξ2 t / (β * σ) - π t,
        κ * lag ξ1 t + 1 / β * (1 + κ / σ) * lag ξ2 t - (ϑ * x t + κ * π t)] := by
    ext j
    fin_cases j <;> simp [Hmat, Jmat] <;> ring
  rw [hv]
  unfold FOC35 FOC36
  constructor
  · rintro ⟨a, b⟩
    ext j
    fin_cases j
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      linear_combination a
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      linear_combination b + κ * a
  · intro h
    have a := congrFun h 0
    have b := congrFun h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a b
    exact ⟨by linear_combination a, by linear_combination b - κ * a⟩

/-! ## The algorithm of p. 152 as a verification theorem -/

/-- Galí (2015), p. 152: after liftoff the implied rate is
`i_{t_C+2+k} = ρ + (1 − δ)(1 − σκ/ϑ) δ^{k+1} ξ`. -/
theorem post_rate {β κ σ ϑ ρ η : ℝ} (hϑ : ϑ ≠ 0) {tZ tC : ℕ} (htC : tZ ≤ tC) {x π : ℕ → ℝ}
    {ξ : ℝ} (hx : ∀ k, x (tC + k + 2) = postX β κ ϑ ξ k)
    (hπ : ∀ k, π (tC + k + 2) = postPi β κ ϑ ξ k) (k : ℕ) :
    impliedRate σ (natRate ρ η tZ) x π (tC + k + 2) =
      ρ + (1 - Commitment.del β κ ϑ) * (1 - σ * κ / ϑ) * Commitment.del β κ ϑ ^ (k + 1) * ξ := by
  unfold impliedRate
  rw [natRate_of_lt (by omega), show tC + k + 2 + 1 = tC + (k + 1) + 2 by omega, hx, hx, hπ]
  unfold postX postPi
  field_simp
  ring

/-- Galí (2015), p. 152: the infinitely many conditions `i_t ≥ 0`, `t ≥ t_C + 2`, reduce to the
single condition `i_{t_C+2} ≥ 0` (the rate moves monotonically towards `ρ > 0`). -/
theorem post_rate_nonneg {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    (hρ : 0 < ρ)
    {tZ tC : ℕ} (htC : tZ ≤ tC) {x π : ℕ → ℝ} {ξ : ℝ}
    (hx : ∀ k, x (tC + k + 2) = postX β κ ϑ ξ k) (hπ : ∀ k, π (tC + k + 2) = postPi β κ ϑ ξ k)
    (h0 : 0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + 2)) (k : ℕ) :
    0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + k + 2) := by
  have hδ0 := Commitment.del_pos (κ := κ) hβ hϑ
  have hδ1 := (Commitment.del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne'
  have e0 : impliedRate σ (natRate ρ η tZ) x π (tC + 2) =
      ρ + (1 - Commitment.del β κ ϑ) * (1 - σ * κ / ϑ) * Commitment.del β κ ϑ ^ (0 + 1) * ξ :=
    post_rate hϑ.ne' htC hx hπ 0
  rw [e0] at h0
  rw [post_rate hϑ.ne' htC hx hπ k]
  set A := (1 - Commitment.del β κ ϑ) * (1 - σ * κ / ϑ) * ξ with hA
  have hk : (1 - Commitment.del β κ ϑ) * (1 - σ * κ / ϑ) * Commitment.del β κ ϑ ^ (k + 1) * ξ =
      A * Commitment.del β κ ϑ ^ (k + 1) := by rw [hA]; ring
  have h0' : (1 - Commitment.del β κ ϑ) * (1 - σ * κ / ϑ) * Commitment.del β κ ϑ ^ (0 + 1) * ξ =
      A * Commitment.del β κ ϑ := by rw [hA]; ring
  rw [hk]
  rw [h0'] at h0
  have hp : Commitment.del β κ ϑ ^ (k + 1) ≤ Commitment.del β κ ϑ := by
    rw [pow_succ']
    exact mul_le_of_le_one_right hδ0.le (pow_le_one₀ hδ0.le hδ1.le)
  have hp0 : 0 ≤ Commitment.del β κ ϑ ^ (k + 1) := pow_nonneg hδ0.le _
  rcases le_or_gt 0 A with hA0 | hA0
  · have := mul_nonneg hA0 hp0; linarith
  · nlinarith

/-- Galí (2015), p. 152: one backward step of (48)/(49) gives the Phillips curve and `i_t = 0`. -/
theorem backStep_nkpc_rate {β κ σ e : ℝ} (hσ : σ ≠ 0) {rn x π : ℕ → ℝ} {t : ℕ}
    (h : (x t, π t) = backStep β κ σ e (x (t + 1), π (t + 1))) (hr : rn t = -e) :
    NKPC β κ x π t ∧ impliedRate σ rn x π t = 0 := by
  rw [Prod.ext_iff] at h
  obtain ⟨hx, hπ⟩ := h
  simp only [backStep] at hx hπ
  refine ⟨?_, ?_⟩
  · unfold NKPC; rw [hπ, hx]; ring
  · unfold impliedRate; rw [hr, hx]; field_simp; ring

/-- Galí (2015), p. 152: the candidate built for a guessed `t_C` satisfies (44)–(46), hence the
matrix relation (47). -/
theorem algorithm_eq47 {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ)
    {tC : ℕ} {x π ξ1 ξ2 : ℕ → ℝ}
    (h50 : FOC35 β σ π ξ1 ξ2 (tC + 1) ∧ FOC36 β κ ϑ x ξ1 ξ2 (tC + 1))
    (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hπ2 : π (tC + 2) = postPi β κ ϑ (ξ1 (tC + 1)) 0) :
    Eq44 β σ (ξ1 (tC + 1)) (π (tC + 1)) (ξ1 tC) (ξ2 tC) ∧
      Eq45 β κ ϑ (ξ1 (tC + 1)) (x (tC + 1)) (ξ2 tC) ∧
      Eq46 β κ ϑ (ξ1 (tC + 1)) (x (tC + 1)) (π (tC + 1)) ∧
      ![x (tC + 1), π (tC + 1)] = Matrix.mulVec (Mmat β κ σ ϑ) ![ξ1 tC, ξ2 tC] := by
  obtain ⟨a, b⟩ := h50
  unfold FOC35 at a
  unfold FOC36 at b
  rw [lag_succ, lag_succ] at a
  rw [lag_succ, hξ2] at b
  have h44 : Eq44 β σ (ξ1 (tC + 1)) (π (tC + 1)) (ξ1 tC) (ξ2 tC) := by
    unfold Eq44; linarith
  have h45 : Eq45 β κ ϑ (ξ1 (tC + 1)) (x (tC + 1)) (ξ2 tC) := by
    unfold Eq45; linarith
  have h46' : Eq46 β κ ϑ (ξ1 (tC + 1)) (x (tC + 1)) (π (tC + 1)) := by
    unfold Eq46
    unfold NKPC at h46
    rw [h46, show tC + 1 + 1 = tC + 2 by omega, hπ2]
    unfold postPi; ring
  exact ⟨h44, h45, h46', eq47 hβ hβ1 hκ hσ hϑ ⟨h44, h45, h46'⟩⟩

/-- Galí (2015), p. 152, VERIFICATION THEOREM for the algorithm. Guess `t_C ≥ t_Z`. Suppose the
candidate path satisfies (48) on `[0, t_Z]`, (49) on `(t_Z, t_C]`, (50) for `t ≤ t_C + 1`, the
Phillips curve at `t_C + 1` (i.e. (46)), `ξ₂,t_C+1 = 0`, and follows (42)–(43) (with
`ξ₁,t = δ^{t−t_C−1} ξ₁,t_C+1`, `ξ₂,t = 0`) after `t_C + 1`. If the sign conditions
`ξ₂,t ≥ 0` hold on `[0, t_C]` and `i ≥ 0` at `t_C + 1` and `t_C + 2`, then the candidate
satisfies the KKT system, is optimal, keeps `i_t = 0` on `[0, t_C]` (with `i ≥ 0` everywhere),
and is the unique optimal path. -/
theorem algorithm_verification {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) {tZ tC : ℕ} (htC : tZ ≤ tC)
    {x π ξ1 ξ2 : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (h50 : ∀ t, t ≤ tC + 1 → FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t)
    (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hpost : ∀ k, x (tC + k + 2) = postX β κ ϑ (ξ1 (tC + 1)) k ∧
      π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k ∧
      ξ1 (tC + k + 2) = postXi β κ ϑ (ξ1 (tC + 1)) (k + 1) ∧ ξ2 (tC + k + 2) = 0)
    (hsign : ∀ t, t ≤ tC → 0 ≤ ξ2 t)
    (hi1 : 0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + 1))
    (hi2 : 0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + 2)) :
    KKT β κ σ ϑ (natRate ρ η tZ) x π ξ1 ξ2 ∧ Optimal β κ σ ϑ (natRate ρ η tZ) x π ∧
      (∀ t, t ≤ tC → impliedRate σ (natRate ρ η tZ) x π t = 0) ∧
      (∀ t, 0 ≤ impliedRate σ (natRate ρ η tZ) x π t) ∧
      (∀ y q, Feasible β κ σ (natRate ρ η tZ) y q → Summable (lossTerm β ϑ y q) →
        loss β ϑ y q ≤ loss β ϑ x π → y = x ∧ q = π) := by
  have hδ0 := Commitment.del_pos (κ := κ) hβ hϑ
  have hδ1 := (Commitment.del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne'
  set ξ := ξ1 (tC + 1) with hξ
  set rn := natRate ρ η tZ with hrn
  have hξ1post : ∀ k, ξ1 (tC + 1 + k) = postXi β κ ϑ ξ k := by
    intro k
    rcases k with _ | k
    · simp [postXi, hξ]
    · rw [show tC + 1 + (k + 1) = tC + k + 2 by omega]; exact (hpost k).2.2.1
  have hξ2post : ∀ k, ξ2 (tC + 1 + k) = 0 := by
    intro k
    rcases k with _ | k
    · simpa using hξ2
    · rw [show tC + 1 + (k + 1) = tC + k + 2 by omega]; exact (hpost k).2.2.2
  have hbind : ∀ t, t ≤ tC → NKPC β κ x π t ∧ impliedRate σ rn x π t = 0 := by
    intro t ht
    rcases le_or_gt t tZ with h | h
    · exact backStep_nkpc_rate hσ.ne' (h48 t h) (by rw [hrn, natRate_of_le h])
    · exact backStep_nkpc_rate hσ.ne' (h49 t h ht) (by rw [hrn, natRate_of_lt h, neg_neg])
  have hx : ∀ k, x (tC + k + 2) = postX β κ ϑ ξ k := fun k => (hpost k).1
  have hπ : ∀ k, π (tC + k + 2) = postPi β κ ϑ ξ k := fun k => (hpost k).2.1
  have hrate : ∀ t, 0 ≤ impliedRate σ rn x π t := by
    intro t
    rcases le_or_gt t tC with ht | ht
    · rw [(hbind t ht).2]
    · rcases Nat.eq_or_lt_of_le ht with h | h
      · rw [← h]; exact hi1
      · obtain ⟨k, rfl⟩ : ∃ k, t = tC + k + 2 := ⟨t - tC - 2, by omega⟩
        exact post_rate_nonneg hβ hβ1 hκ hϑ hρ htC hx hπ hi2 k
  have hnkpc : ∀ t, NKPC β κ x π t := by
    intro t
    rcases le_or_gt t tC with ht | ht
    · exact (hbind t ht).1
    · rcases Nat.eq_or_lt_of_le ht with h | h
      · rw [← h]; exact h46
      · obtain ⟨k, rfl⟩ : ∃ k, t = tC + k + 2 := ⟨t - tC - 2, by omega⟩
        unfold NKPC
        rw [show tC + k + 2 + 1 = tC + (k + 1) + 2 by omega, hx, hπ, hπ]
        exact post_eq39 hβ hβ1 hϑ ξ k
  have hK : KKT β κ σ ϑ rn x π ξ1 ξ2 := by
    refine ⟨(feasible_iff hσ).mpr fun t => ⟨hnkpc t, hrate t⟩, fun t => ?_⟩
    rcases le_or_gt t (tC + 1) with ht | ht
    · refine ⟨(h50 t ht).1, (h50 t ht).2, ?_, ?_⟩
      · rcases le_or_gt t tC with h | h
        · exact hsign t h
        · rw [show t = tC + 1 by omega, hξ2]
      · rcases le_or_gt t tC with h | h
        · rw [(hbind t h).2, mul_zero]
        · rw [show t = tC + 1 by omega, hξ2, zero_mul]
    · obtain ⟨k, rfl⟩ : ∃ k, t = tC + k + 2 := ⟨t - tC - 2, by omega⟩
      have e : tC + k + 2 = (tC + 1 + k) + 1 := by omega
      have l1 : lag ξ1 (tC + k + 2) = postXi β κ ϑ ξ k := by rw [e, lag_succ, hξ1post]
      have l2 : lag ξ2 (tC + k + 2) = 0 := by rw [e, lag_succ, hξ2post]
      have x1 : ξ1 (tC + k + 2) = postXi β κ ϑ ξ (k + 1) := (hpost k).2.2.1
      have x2 : ξ2 (tC + k + 2) = 0 := (hpost k).2.2.2
      refine ⟨?_, ?_, by rw [x2], by rw [x2, zero_mul]⟩
      · unfold FOC35
        rw [l1, l2, x1, hπ, zero_div, sub_zero]
        exact post_eq37 β κ ϑ ξ k
      · unfold FOC36
        rw [l2, x1, x2, hx, zero_div, sub_zero, add_zero]
        exact post_eq38 hϑ.ne' ξ k
  -- bounded multipliers
  have hb : ∃ C, ∀ t, |ξ1 t| ≤ C ∧ |ξ2 t| ≤ C := by
    refine ⟨∑ s ∈ Finset.range (tC + 1), (|ξ1 s| + |ξ2 s|) + |ξ|, fun t => ?_⟩
    have hS : 0 ≤ ∑ s ∈ Finset.range (tC + 1), (|ξ1 s| + |ξ2 s|) :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hξ0 := abs_nonneg ξ
    rcases le_or_gt t tC with ht | ht
    · have hle := Finset.single_le_sum (f := fun s => |ξ1 s| + |ξ2 s|)
        (fun _ _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))
      have a1 := abs_nonneg (ξ1 t)
      have a2 := abs_nonneg (ξ2 t)
      constructor <;> linarith
    · obtain ⟨k, rfl⟩ : ∃ k, t = tC + 1 + k := ⟨t - tC - 1, by omega⟩
      rw [hξ1post, hξ2post, abs_zero]
      refine ⟨?_, by linarith⟩
      unfold postXi
      rw [abs_mul, abs_of_nonneg (pow_nonneg hδ0.le k)]
      have : Commitment.del β κ ϑ ^ k * |ξ| ≤ |ξ| :=
        mul_le_of_le_one_left hξ0 (pow_le_one₀ hδ0.le hδ1.le)
      linarith
  -- finite loss
  have hs : Summable (lossTerm β ϑ x π) := by
    refine (summable_nat_add_iff (tC + 2)).mp ?_
    have e : (fun n => lossTerm β ϑ x π (n + (tC + 2))) = fun n =>
        β ^ (tC + 2) * (((1 - Commitment.del β κ ϑ) * ξ) ^ 2 +
          ϑ * (κ * Commitment.del β κ ϑ * ξ / ϑ) ^ 2) *
          (β * Commitment.del β κ ϑ ^ 2) ^ n := by
      funext n
      rw [lossTerm, show n + (tC + 2) = tC + n + 2 by omega, hx, hπ]
      unfold postX postPi
      ring
    rw [e]
    exact (summable_geometric_of_lt_one (by positivity) (by nlinarith)).mul_left _
  refine ⟨hK, kkt_optimal hβ hβ1 hσ hϑ hK hb hs, fun t ht => (hbind t ht).2, hrate,
    fun y q hy hsy hle => kkt_unique hβ hβ1 hσ hϑ hK hb hs hy hsy hle⟩

/-- Galí (2015), p. 152 (C5-9): the count of the algorithm's equations. The unknowns are
`(x_t, π_t, ξ₁,t, ξ₂,t)` for `t = 0, …, t_C + 1`, i.e. `4 (t_C + 2)`. The equations matching
them are (48)–(49) for `t ≤ t_C` (`2 (t_C + 1)`), (50) for `t ≤ t_C` (`2 (t_C + 1)`), (47) (`2`),
and — silently in the book — (46) and `ξ₂,t_C+1 = 0` (`1 + 1`); compare `algorithm_eq47`, which
derives (47) from (50) at `t_C + 1`, (46) and `ξ₂,t_C+1 = 0`. -/
theorem equation_count (tC : ℕ) :
    2 * (tC + 1) + 2 * (tC + 1) + 2 + 1 + 1 = 4 * (tC + 2) := by
  ring

end Gali.DiscretionCommitment.ZLBCommitment
