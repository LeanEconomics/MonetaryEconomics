/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Shared sequence tools for Chapter 7

Woodford (2003), *Interest and Prices*, Chapter 7 (pp. 464–533) and Appendix F (pp. 709–715).

The losses of Chapter 7 are discounted sums `∑ βᵗ ℓ_t` over *bounded* plans (p. 477), and every
Lagrangian argument (survey §4.4) rests on the same telescoping identity. This module collects
the elementary tools that several parts of the chapter use, so that each is proved once:

* `lagged`: the lag of a sequence with a given pre-sample value (`y_{t−1}` with `y_{−1}` given;
  the multipliers `φ_{t−1}` of (1.7), (1.16)–(1.18), the gap `x_{t−1}` of (5.1)).
* `Bdd` and its closure properties (`bdd_const`, `Bdd.add`, `Bdd.sub`, `Bdd.mul`, `Bdd.sq`,
  `Bdd.neg`, `Bdd.shift`, `Bdd.drop`, `Bdd.lag`, `bdd_of_zero_from`, `bdd_sub_const`,
  `bdd_lin`).
* Discounted sums: `summable_disc`, `hasSum_disc_const`, and the telescoping identities
  `hasSum_telescope`, `tsum_telescope` (`∑ βᵗ (a_t − β a_{t+1}) = a_0`) and `tsum_telescope_inv`
  (`∑ βᵗ (β⁻¹ a_t − a_{t+1}) = β⁻¹ a_0`).
-/

namespace Woodford.GainsFromCommitment.Sequences

open Filter Topology

/-! ### Lags with a given pre-sample value -/

/-- Woodford (2003), eq. (1.9), p. 472, (1.16)–(1.18), p. 478, and (5.1), p. 523: the lagged
sequence with a given initial value, `lagged ym y 0 = ym` (the value `y_{−1}`) and
`lagged ym y (t + 1) = y t`. -/
def lagged {α : Type*} (ym : α) (y : ℕ → α) : ℕ → α
  | 0 => ym
  | t + 1 => y t

/-- Woodford (2003), eq. (1.10), p. 472: `lagged ym y 0 = ym`. -/
@[simp] theorem lagged_zero {α : Type*} (ym : α) (y : ℕ → α) : lagged ym y 0 = ym := rfl

/-- Woodford (2003), eq. (1.10), p. 472: `lagged ym y (t + 1) = y t`. -/
@[simp] theorem lagged_succ {α : Type*} (ym : α) (y : ℕ → α) (t : ℕ) :
    lagged ym y (t + 1) = y t := rfl

/-- Woodford (2003), p. 478: the lag of a constant sequence with the same pre-sample value is
that constant. -/
@[simp] theorem lagged_const {α : Type*} (c : α) (t : ℕ) : lagged c (fun _ => c) t = c := by
  cases t <;> rfl

/-! ### Bounded sequences -/

/-- Woodford (2003), p. 477: the plans compared are *bounded* sequences. A real sequence
`f : ℕ → ℝ` is bounded. -/
def Bdd (f : ℕ → ℝ) : Prop := ∃ C, ∀ t, |f t| ≤ C

/-- Woodford (2003), p. 477: a constant sequence is bounded. -/
theorem bdd_const (c : ℝ) : Bdd (fun _ => c) := ⟨|c|, fun _ => le_rfl⟩

/-- Woodford (2003), p. 477: sums of bounded sequences are bounded. -/
theorem Bdd.add {f g : ℕ → ℝ} (hf : Bdd f) (hg : Bdd g) : Bdd (fun t => f t + g t) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  exact ⟨C + D, fun t => (abs_add_le _ _).trans (add_le_add (hC t) (hD t))⟩

/-- Woodford (2003), p. 477: differences of bounded sequences are bounded. -/
theorem Bdd.sub {f g : ℕ → ℝ} (hf : Bdd f) (hg : Bdd g) : Bdd (fun t => f t - g t) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  exact ⟨C + D, fun t => (abs_sub _ _).trans (add_le_add (hC t) (hD t))⟩

/-- Woodford (2003), p. 477: products of bounded sequences are bounded. -/
theorem Bdd.mul {f g : ℕ → ℝ} (hf : Bdd f) (hg : Bdd g) : Bdd (fun t => f t * g t) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨C * D, fun t => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hC t) (hD t) (abs_nonneg _) ((abs_nonneg _).trans (hC 0))

/-- Woodford (2003), p. 477: squares of bounded sequences are bounded. -/
theorem Bdd.sq {f : ℕ → ℝ} (hf : Bdd f) : Bdd (fun t => f t ^ 2) := by
  simpa [pow_two] using hf.mul hf

/-- Woodford (2003), p. 477: negatives of bounded sequences are bounded. -/
theorem Bdd.neg {f : ℕ → ℝ} (hf : Bdd f) : Bdd (fun t => -f t) := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, fun t => by rw [abs_neg]; exact hC t⟩

/-- Woodford (2003), p. 477: the one-period lead of a bounded sequence is bounded. -/
theorem Bdd.shift {f : ℕ → ℝ} (hf : Bdd f) : Bdd (fun t => f (t + 1)) := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, fun t => hC (t + 1)⟩

/-- Woodford (2003), p. 477: shifting a bounded sequence in time keeps it bounded. -/
theorem Bdd.drop {f : ℕ → ℝ} (hf : Bdd f) (t0 : ℕ) : Bdd (fun t => f (t0 + t)) := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, fun t => hC (t0 + t)⟩

/-- Woodford (2003), p. 478: the lag of a bounded sequence is bounded. -/
theorem Bdd.lag {f : ℕ → ℝ} (hf : Bdd f) (m : ℝ) : Bdd (lagged m f) := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨max |m| C, fun t => ?_⟩
  cases t with
  | zero => exact le_max_left _ _
  | succ n => exact (hC n).trans (le_max_right _ _)

/-- Woodford (2003), (1.14), p. 476: a sequence vanishing from date `N` on is bounded. -/
theorem bdd_of_zero_from {f : ℕ → ℝ} (N : ℕ) (hf : ∀ t, N ≤ t → f t = 0) : Bdd f := by
  refine ⟨∑ s ∈ Finset.range N, |f s|, fun t => ?_⟩
  by_cases ht : t < N
  · exact Finset.single_le_sum (f := fun s => |f s|) (fun s _ => abs_nonneg _)
      (Finset.mem_range.mpr ht)
  · rw [hf t (not_lt.mp ht), abs_zero]
    exact Finset.sum_nonneg (fun s _ => abs_nonneg _)

/-- Woodford (2003), p. 474: deviations of a bounded sequence from a constant are bounded. -/
theorem bdd_sub_const {y : ℕ → ℝ} (hy : Bdd y) (c : ℝ) : Bdd (fun t => y t - c) :=
  hy.sub (bdd_const c)

/-- Woodford (2003), p. 474: linear combinations of bounded sequences are bounded. -/
theorem bdd_lin {y z : ℕ → ℝ} (hy : Bdd y) (hz : Bdd z) (a b : ℝ) :
    Bdd (fun t => a * y t + b * z t) :=
  ((bdd_const a).mul hy).add ((bdd_const b).mul hz)

/-! ### Discounted sums and telescoping -/

/-- Woodford (2003), (1.2), p. 469, and (2.4), p. 488: a bounded sequence discounted by
`0 ≤ β < 1` is summable. -/
theorem summable_disc {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {a : ℕ → ℝ} {M : ℝ}
    (ha : ∀ t, |a t| ≤ M) : Summable (fun t => β ^ t * a t) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right M)
    (fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
  exact mul_le_mul_of_nonneg_left (ha t) (pow_nonneg hβ0 t)

/-- Woodford (2003), (1.2), p. 469: the discounted sum of a constant, `(1 − β)⁻¹ c`. -/
theorem hasSum_disc_const {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (c : ℝ) :
    HasSum (fun t : ℕ => β ^ t * c) ((1 - β)⁻¹ * c) :=
  (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right c

/-- Woodford (2003), p. 478 and App. F.1 (the telescoping step of the Lagrangian argument,
survey §4.4): for a bounded sequence `a`, `∑_t βᵗ (a_t − β a_{t+1}) = a_0`. -/
theorem hasSum_telescope {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {a : ℕ → ℝ} {M : ℝ}
    (ha : ∀ t, |a t| ≤ M) : HasSum (fun t => β ^ t * (a t - β * a (t + 1))) (a 0) := by
  obtain ⟨A, hA⟩ := summable_disc hβ0 hβ1 ha
  have h1 : HasSum (fun t => β ^ (t + 1) * a (t + 1)) (A - a 0) := by
    have := (hasSum_nat_add_iff' (f := fun t => β ^ t * a t) 1).mpr hA
    simpa using this
  have h2 := hA.sub h1
  convert h2 using 1
  · funext t
    ring
  · ring

/-- Woodford (2003), App. F.1 (the telescoping step of the Lagrangian argument, survey §4.4):
for a bounded sequence `g` and `0 ≤ β < 1`, `∑_k βᵏ (g_k − β g_{k+1}) = g_0`. -/
theorem tsum_telescope {β B : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {g : ℕ → ℝ}
    (hg : ∀ k, |g k| ≤ B) : ∑' k, β ^ k * (g k - β * g (k + 1)) = g 0 :=
  (hasSum_telescope hβ0 hβ1 hg).tsum_eq

/-- Woodford (2003), p. 506 (the telescoping step of Lagrangian sufficiency): for a bounded
sequence and `0 < β < 1`, `∑_k βᵏ(β⁻¹a_k − a_{k+1}) = β⁻¹a_0` (and the series converges). -/
theorem tsum_telescope_inv {β M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {a : ℕ → ℝ}
    (ha : ∀ k, |a k| ≤ M) :
    Summable (fun k => β ^ k * (β⁻¹ * a k - a (k + 1))) ∧
      ∑' k, β ^ k * (β⁻¹ * a k - a (k + 1)) = β⁻¹ * a 0 := by
  have h := (hasSum_telescope hβ0.le hβ1 ha).mul_left β⁻¹
  have he : (fun k => β⁻¹ * (β ^ k * (a k - β * a (k + 1)))) =
      fun k => β ^ k * (β⁻¹ * a k - a (k + 1)) := by
    funext k
    field_simp
  rw [he] at h
  exact ⟨h.summable, h.tsum_eq⟩

end Woodford.GainsFromCommitment.Sequences
