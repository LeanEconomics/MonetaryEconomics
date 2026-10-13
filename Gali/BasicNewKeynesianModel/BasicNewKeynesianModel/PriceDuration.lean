/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Calvo price durations

Galí (2015), Chapter 3, §3.2 (p. 55). Each period a firm may reset its price
with probability `1 − θ`, independently of its history. A price set today is
still in force `k` periods later with probability `θᵏ`, and its duration (the
number of periods until the first reset opportunity, counting the current one)
is `k ≥ 1` with probability `(1 − θ) θ^{k−1}`. The book states that the
average duration of a price is `1/(1 − θ)`.

## Main results

* `survival_sum`: the duration probabilities sum to one.
* `mean_duration`: the expected duration is `1/(1 − θ)` (Galí, p. 55).
* `CalvoParam`: the Calvo parameter `θ ∈ [0, 1)` bundled with its range, the
  form later modules use.
-/

namespace Gali.BasicNewKeynesianModel

/-- The probability that a price lasts exactly `k + 1` periods,
`(1 − θ) θᵏ` (Galí, p. 55). Durations are indexed from `0` so that the
duration `k + 1 ≥ 1` has index `k`. -/
noncomputable def durationProb (θ : ℝ) (k : ℕ) : ℝ := (1 - θ) * θ ^ k

/-- Duration probabilities are nonnegative for `θ ∈ [0, 1]`. -/
theorem durationProb_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (k : ℕ) :
    0 ≤ durationProb θ k :=
  mul_nonneg (by linarith) (pow_nonneg h0 k)

/-- The duration probabilities form a distribution: `∑ₖ (1 − θ) θᵏ = 1`
for `θ ∈ [0, 1)`. -/
theorem survival_sum {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) :
    ∑' k, durationProb θ k = 1 := by
  unfold durationProb
  rw [tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
  field_simp [sub_ne_zero.mpr (ne_of_lt h1).symm]

/-- The probability that a price set today is still in force after `k`
periods is `θᵏ`: the tail mass of the duration distribution beyond `k`
periods, `∑_{j ≥ k} (1 − θ) θʲ = θᵏ`. -/
theorem tail_sum {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (k : ℕ) :
    ∑' j, durationProb θ (j + k) = θ ^ k := by
  unfold durationProb
  have hs : ∀ j, (1 - θ) * θ ^ (j + k) = θ ^ k * ((1 - θ) * θ ^ j) := by
    intro j; ring
  simp_rw [hs]
  rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
  field_simp [sub_ne_zero.mpr (ne_of_lt h1).symm]

/-- **Average price duration** (Galí, p. 55): with reset probability `1 − θ`,
the expected duration of a price is `∑ₖ (k + 1)(1 − θ) θᵏ = 1/(1 − θ)`. -/
theorem mean_duration {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) :
    ∑' k : ℕ, ((k : ℝ) + 1) * durationProb θ k = 1 / (1 - θ) := by
  have hn : ‖θ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have hA : Summable fun k : ℕ => (k : ℝ) * θ ^ k :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hn |>.congr fun k => by simp
  have hB : Summable fun k : ℕ => θ ^ k := summable_geometric_of_lt_one h0 h1
  have hs : ∀ k : ℕ, ((k : ℝ) + 1) * durationProb θ k
      = (1 - θ) * ((k : ℝ) * θ ^ k) + (1 - θ) * θ ^ k := by
    intro k; unfold durationProb; ring
  simp_rw [hs]
  rw [(hA.mul_left _).tsum_add (hB.mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_coe_mul_geometric_of_norm_lt_one hn, tsum_geometric_of_lt_one h0 h1]
  have h : (1 - θ) ≠ 0 := sub_ne_zero.mpr (ne_of_lt h1).symm
  field_simp
  ring

/-- A Calvo price-stickiness parameter: `θ` is the probability that a firm
cannot reset its price in a given period, with `0 ≤ θ < 1` (Galí, p. 55). -/
structure CalvoParam where
  /-- The probability of not resetting the price this period. -/
  θ : ℝ
  nonneg : 0 ≤ θ
  lt_one : θ < 1

/-- The average duration of a price under a Calvo parameter is `1/(1 − θ)`
(Galí, p. 55). -/
theorem CalvoParam.mean_duration (c : CalvoParam) :
    ∑' k : ℕ, ((k : ℝ) + 1) * durationProb c.θ k = 1 / (1 - c.θ) :=
  Gali.BasicNewKeynesianModel.mean_duration c.nonneg c.lt_one

end Gali.BasicNewKeynesianModel
