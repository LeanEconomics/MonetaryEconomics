/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.MaturityBuffer

/-!
# Long-term debt and total inflation: what (8.4) does and does not say

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 8, §8.4, eq. (8.4), p. 250:
"The longer the maturity of debt `ω`, the more the revision in present value of surpluses can be
spread to future inflation, though at the cost of more total inflation."

Write `x_j = ΔE_{t+1} π_{t+1+j}` for the inflation news and `C` for the right-hand side of (8.4)
(with no real-rate news `C = −∑ ρʲ ΔE s_{t+1+j}`, the same for every maturity). Then (8.4) is
`∑ ωʲ x_j = C`, and total inflation is `∑ x_j` (the revision of the long-run price level).

## Main results

* `total_ge` (**spreading costs total inflation**): for `0 ≤ ω ≤ 1` and nonnegative inflation news,
  total inflation is at least `C`, the total under short-term debt (`short_debt_total`); with
  `ω < 1` equality holds iff there is no inflation after the first period (`total_eq_iff`).
* `total_ge_spread` (**the precise cost**): for `0 < ω ≤ 1`, if current inflation is reduced by
  `Δ = C − x_0` (spreading `Δ` forward), total inflation is at least `C + Δ (1 − ω)/ω`; the bound is
  attained by putting all deferred inflation one period ahead (`total_spread_attained`). With
  short-term debt (`ω = 0`) nothing can be spread: `x_0 = C`.
* `spread_cost_antitone`: the minimal cost `(1 − ω)/ω` per unit spread falls as the maturity
  lengthens; perpetuities (`ω = 1`) spread at no cost in total inflation (`perpetuity_total`).
* `geometric_total`, `geometric_total_strictMono_phi`, `geometric_total_strictAnti_omega`
  (**the counterexample**): with a geometric inflation profile `x_j = a φʲ`, total inflation is
  `C (1 − ωφ)/(1 − φ)`: increasing in the spreading `φ` but strictly *decreasing* in the maturity
  `ω`. So "longer maturity means more total inflation" is false as a statement about `ω` alone: it
  is spreading, not maturity, that costs total inflation; (8.4) alone does not determine the path.
* `total_lt_without_sign` (**the sign condition is needed**): with deflation news allowed, a path
  satisfying (8.4) can have total inflation below `C`.
* `total_ge_of_identities`: the link to `MaturityBuffer.identity_84` with no real-rate news.
-/

namespace Cochrane.AssetsRulesBalanceSheets.TidyR6TotalInflation

open Filter Topology

/-- Cochrane (2023), §8.4, p. 250: with short-term debt (`ω = 0`) the identity
`∑ ωʲ x_j = C` reads `x_0 = C`: all of the revision is immediate inflation, and the total is
`C` plus any later inflation news, which (8.4) leaves unconstrained. -/
theorem short_debt_total {C : ℝ} {x : ℕ → ℝ} (hx : Summable x)
    (h : ∑' j, (0 : ℝ) ^ j * x j = C) : x 0 = C ∧ ∑' j, x j = C + ∑' j, x (j + 1) := by
  have e : ∑' j, (0 : ℝ) ^ j * x j = x 0 := by
    rw [tsum_eq_single 0 fun j hj => by simp [hj]]
    simp
  rw [e] at h
  exact ⟨h, by rw [hx.tsum_eq_zero_add, h]⟩

/-- Cochrane (2023), §8.4, p. 250 (supporting lemma): for `0 ≤ ω ≤ 1` and nonnegative summable
`x`, the weighted sum `∑ ωʲ x_j` is summable and at most `∑ x_j`. -/
theorem weighted_le {ω : ℝ} (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) {x : ℕ → ℝ} (hx0 : ∀ j, 0 ≤ x j)
    (hx : Summable x) : Summable (fun j => ω ^ j * x j) ∧ ∑' j, ω ^ j * x j ≤ ∑' j, x j := by
  have hle : ∀ j, ω ^ j * x j ≤ x j := fun j =>
    mul_le_of_le_one_left (hx0 j) (pow_le_one₀ hω0 hω1)
  have hs : Summable (fun j => ω ^ j * x j) :=
    hx.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg hω0 j) (hx0 j)) hle
  exact ⟨hs, hs.tsum_le_tsum hle hx⟩

/-- Cochrane (2023), §8.4, p. 250 (**spreading costs total inflation**): if `0 ≤ ω ≤ 1`, the
inflation news are nonnegative and summable and satisfy (8.4) `∑ ωʲ x_j = C`, then total inflation
`∑ x_j` is at least `C`, the total under short-term debt. -/
theorem total_ge {ω C : ℝ} (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) {x : ℕ → ℝ} (hx0 : ∀ j, 0 ≤ x j)
    (hx : Summable x) (h : ∑' j, ω ^ j * x j = C) : C ≤ ∑' j, x j :=
  h ▸ (weighted_le hω0 hω1 hx0 hx).2

/-- Cochrane (2023), §8.4, p. 250: with `0 ≤ ω < 1` and nonnegative summable news satisfying
(8.4), total inflation equals `C` iff all the inflation is immediate (`x_j = 0` for `j ≥ 1`). -/
theorem total_eq_iff {ω C : ℝ} (hω0 : 0 ≤ ω) (hω1 : ω < 1) {x : ℕ → ℝ} (hx0 : ∀ j, 0 ≤ x j)
    (hx : Summable x) (h : ∑' j, ω ^ j * x j = C) :
    ∑' j, x j = C ↔ ∀ j, x (j + 1) = 0 := by
  obtain ⟨hs, -⟩ := weighted_le hω0 hω1.le hx0 hx
  have hd : Summable (fun j => (1 - ω ^ j) * x j) :=
    (hx.sub hs).congr fun j => by ring
  have hdiff : ∑' j, x j - C = ∑' j, (1 - ω ^ j) * x j := by
    rw [← h, ← hx.tsum_sub hs]
    exact tsum_congr fun j => by ring
  have hnn : ∀ j, 0 ≤ (1 - ω ^ j) * x j := fun j =>
    mul_nonneg (by linarith [pow_le_one₀ hω0 hω1.le (n := j)]) (hx0 j)
  constructor
  · intro htot j
    have h0 : ∑' j, (1 - ω ^ j) * x j = 0 := by rw [← hdiff, htot, sub_self]
    have hz := (hasSum_zero_iff_of_nonneg hnn).1 (h0 ▸ hd.hasSum)
    have := congrFun hz (j + 1)
    simp only [Pi.zero_apply] at this
    have hpos : 0 < 1 - ω ^ (j + 1) := by
      have : ω ^ (j + 1) < 1 := pow_lt_one₀ hω0 hω1 (Nat.succ_ne_zero j)
      linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · exact h1
  · intro hz
    have : ∀ j, (1 - ω ^ j) * x j = 0 := fun j => by
      rcases j with _ | j
      · simp
      · rw [hz j, mul_zero]
    rw [tsum_congr this, tsum_zero] at hdiff
    linarith

/-- Cochrane (2023), §8.4, p. 250 (**the precise cost of spreading**): for `0 < ω ≤ 1` and
nonnegative summable inflation news satisfying (8.4) `∑ ωʲ x_j = C`, let `Δ = C − x_0` be the
reduction of current inflation below its short-debt value. Then total inflation is at least
`C + Δ (1 − ω)/ω`. -/
theorem total_ge_spread {ω C : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1) {x : ℕ → ℝ} (hx0 : ∀ j, 0 ≤ x j)
    (hx : Summable x) (h : ∑' j, ω ^ j * x j = C) :
    C + (C - x 0) * (1 - ω) / ω ≤ ∑' j, x j := by
  obtain ⟨hs, -⟩ := weighted_le hω0.le hω1 hx0 hx
  have hx1 : Summable (fun j => x (j + 1)) := (summable_nat_add_iff 1).2 hx
  have hs1 : Summable (fun j => ω ^ (j + 1) * x (j + 1)) := (summable_nat_add_iff 1).2 hs
  have hsplit : C = x 0 + ∑' j, ω ^ (j + 1) * x (j + 1) := by
    rw [← h, hs.tsum_eq_zero_add]
    simp
  have hle : ∀ j, ω ^ (j + 1) * x (j + 1) ≤ ω * x (j + 1) := fun j => by
    refine mul_le_mul_of_nonneg_right ?_ (hx0 _)
    calc ω ^ (j + 1) = ω * ω ^ j := pow_succ' ω j
      _ ≤ ω * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hω0.le hω1) hω0.le
      _ = ω := mul_one ω
  have hb : ∑' j, ω ^ (j + 1) * x (j + 1) ≤ ω * ∑' j, x (j + 1) := by
    rw [← tsum_mul_left]
    exact hs1.tsum_le_tsum hle (hx1.mul_left ω)
  have htot : ∑' j, x j = x 0 + ∑' j, x (j + 1) := hx.tsum_eq_zero_add
  rw [htot]
  have hΔ : C - x 0 ≤ ω * ∑' j, x (j + 1) := by linarith
  have : (C - x 0) / ω ≤ ∑' j, x (j + 1) := by
    rw [div_le_iff₀ hω0]
    linarith
  have e : C + (C - x 0) * (1 - ω) / ω = x 0 + (C - x 0) / ω := by
    field_simp
    ring
  rw [e]
  linarith

/-- Cochrane (2023), §8.4, p. 250: the bound of `total_ge_spread` is attained. For `0 < ω` and
`0 ≤ Δ ≤ C`, the path `x_0 = C − Δ`, `x_1 = Δ/ω`, `x_j = 0` otherwise, satisfies (8.4) and has
total inflation `C + Δ (1 − ω)/ω`. -/
theorem total_spread_attained {ω C Δ : ℝ} (hω0 : 0 < ω) :
    let x : ℕ → ℝ := fun j => if j = 0 then C - Δ else if j = 1 then Δ / ω else 0
    ∑' j, ω ^ j * x j = C ∧ ∑' j, x j = C + Δ * (1 - ω) / ω := by
  intro x
  have hsupp : ∀ j ∉ ({0, 1} : Finset ℕ), x j = 0 := fun j hj => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    simp [x, hj.1, hj.2]
  constructor
  · rw [tsum_eq_sum (s := {0, 1}) fun j hj => by rw [hsupp j hj, mul_zero]]
    simp only [Finset.mem_singleton, zero_ne_one, not_false_eq_true, Finset.sum_insert,
      Finset.sum_singleton, pow_zero, one_mul, pow_one, x]
    simp only [↓reduceIte, one_ne_zero]
    field_simp
    ring
  · rw [tsum_eq_sum (s := {0, 1}) fun j hj => hsupp j hj]
    simp only [Finset.mem_singleton, zero_ne_one, not_false_eq_true, Finset.sum_insert,
      Finset.sum_singleton, x, ↓reduceIte, one_ne_zero]
    field_simp
    ring

/-- Cochrane (2023), §8.4, p. 250: the minimal total-inflation cost per unit of current inflation
spread forward, `(1 − ω)/ω`, is strictly decreasing in the maturity `ω ∈ (0, 1]`. -/
theorem spread_cost_antitone {ω ω' : ℝ} (hω0 : 0 < ω) (hωω : ω < ω') :
    (1 - ω') / ω' < (1 - ω) / ω := by
  have hω'0 : 0 < ω' := hω0.trans hωω
  rw [div_lt_div_iff₀ hω'0 hω0]
  nlinarith

/-- Cochrane (2023), §8.4, p. 250: with perpetuities (`ω = 1`) total inflation always equals the
revision `C`, however it is spread. -/
theorem perpetuity_total {C : ℝ} {x : ℕ → ℝ} (h : ∑' j, (1 : ℝ) ^ j * x j = C) :
    ∑' j, x j = C := by
  simpa using h

/-- Cochrane (2023), §8.4, p. 250: with a geometric inflation profile `x_j = a φʲ`, `0 ≤ φ < 1`,
`0 ≤ ω ≤ 1`, the identity (8.4) `∑ ωʲ x_j = C` forces `a = C (1 − ωφ)`, and total inflation is
`C (1 − ωφ)/(1 − φ)`. -/
theorem geometric_total {ω φ a C : ℝ} (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1)
    (h : ∑' j, ω ^ j * (a * φ ^ j) = C) :
    a = C * (1 - ω * φ) ∧ ∑' j, a * φ ^ j = C * (1 - ω * φ) / (1 - φ) := by
  have hωφ : ω * φ < 1 := by nlinarith
  have hωφ0 : 0 ≤ ω * φ := mul_nonneg hω0 hφ0
  have e1 : ∑' j, ω ^ j * (a * φ ^ j) = a / (1 - ω * φ) := by
    have : (fun j => ω ^ j * (a * φ ^ j)) = fun j => a * (ω * φ) ^ j := by
      funext j; rw [mul_pow]; ring
    rw [this, tsum_mul_left, tsum_geometric_of_lt_one hωφ0 hωφ, div_eq_mul_inv]
  have ha : a = C * (1 - ω * φ) := by
    rw [e1] at h
    have : 1 - ω * φ ≠ 0 := by linarith
    field_simp at h
    linarith
  refine ⟨ha, ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one hφ0 hφ1, ha, div_eq_mul_inv]

/-- Cochrane (2023), §8.4, p. 250: with a geometric profile, for `C > 0` and `ω < 1`, total
inflation `C (1 − ωφ)/(1 − φ)` is strictly increasing in the spreading parameter `φ < 1`:
spreading inflation forward costs total inflation. -/
theorem geometric_total_strictMono_phi {ω C φ φ' : ℝ} (hC : 0 < C) (hω1 : ω < 1)
    (hφφ : φ < φ') (hφ'1 : φ' < 1) :
    C * (1 - ω * φ) / (1 - φ) < C * (1 - ω * φ') / (1 - φ') := by
  have h1 : 0 < 1 - φ := by linarith
  have h2 : 0 < 1 - φ' := by linarith
  rw [div_lt_div_iff₀ h1 h2]
  have : 0 < C * (1 - ω) * (φ' - φ) := by
    have : 0 < 1 - ω := by linarith
    have : 0 < φ' - φ := by linarith
    positivity
  nlinarith

/-- Cochrane (2023), §8.4, p. 250 (**the counterexample**): with a geometric profile
`0 < φ < 1` and `C > 0`, total inflation `C (1 − ωφ)/(1 − φ)` is strictly *decreasing* in the
maturity `ω`: for the same shape of the inflation response, longer debt means less total inflation
(and less current inflation `C (1 − ωφ)`). So "longer maturity, more total inflation" does not
follow from (8.4); the cost comes from spreading (`geometric_total_strictMono_phi`,
`total_ge_spread`). -/
theorem geometric_total_strictAnti_omega {ω ω' C φ : ℝ} (hC : 0 < C) (hφ0 : 0 < φ)
    (hφ1 : φ < 1) (hωω : ω < ω') :
    C * (1 - ω' * φ) / (1 - φ) < C * (1 - ω * φ) / (1 - φ) ∧
      C * (1 - ω' * φ) < C * (1 - ω * φ) := by
  have h1 : 0 < 1 - φ := by linarith
  have h2 : C * (1 - ω' * φ) < C * (1 - ω * φ) := by
    have : 0 < C * ((ω' - ω) * φ) := mul_pos hC (mul_pos (by linarith) hφ0)
    nlinarith
  exact ⟨div_lt_div_of_pos_right h2 h1, h2⟩

/-- Cochrane (2023), §8.4, p. 250 (**the sign condition is needed**): for `0 < ω < 1` and any `C`,
the path `x_0 = C + ω`, `x_1 = −1`, `x_j = 0` otherwise satisfies (8.4) `∑ ωʲ x_j = C` but has total
inflation `C − (1 − ω) < C`: with deflation news, spreading need not cost total inflation. -/
theorem total_lt_without_sign {ω C : ℝ} (hω1 : ω < 1) :
    let x : ℕ → ℝ := fun j => if j = 0 then C + ω else if j = 1 then -1 else 0
    ∑' j, ω ^ j * x j = C ∧ ∑' j, x j = C - (1 - ω) ∧ ∑' j, x j < C := by
  intro x
  have hsupp : ∀ j ∉ ({0, 1} : Finset ℕ), x j = 0 := fun j hj => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    simp [x, hj.1, hj.2]
  have e2 : ∑' j, x j = C - (1 - ω) := by
    rw [tsum_eq_sum (s := {0, 1}) fun j hj => hsupp j hj]
    simp only [Finset.mem_singleton, zero_ne_one, not_false_eq_true, Finset.sum_insert,
      Finset.sum_singleton, x, ↓reduceIte, one_ne_zero]
    ring
  refine ⟨?_, e2, by rw [e2]; linarith⟩
  rw [tsum_eq_sum (s := {0, 1}) fun j hj => by rw [hsupp j hj, mul_zero]]
  simp only [Finset.mem_singleton, zero_ne_one, not_false_eq_true, Finset.sum_insert,
    Finset.sum_singleton, pow_zero, one_mul, pow_one, x, ↓reduceIte, one_ne_zero]
  ring

/-- Cochrane (2023), eq. (8.4), p. 250 (**the link to the identities**): if the news satisfy
(3.20)–(3.21) (`MaturityBuffer.Identity320`, `MaturityBuffer.Identity321`) with maturity
`0 < ω ≤ 1` and no real-rate news, and the inflation news are nonnegative and summable, then total
inflation is at least the surplus revision `C = −∑ ρʲ ΔE s_{t+1+j}` plus `(C − x_0)(1 − ω)/ω`. -/
theorem total_ge_of_identities {ρ ω rn : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1) {πN sN : ℕ → ℝ}
    (hπ0 : ∀ j, 0 ≤ πN j) (hπ : Summable πN)
    (h320 : MaturityBuffer.Identity320 ρ πN sN (fun _ => 0) rn)
    (h321 : MaturityBuffer.Identity321 ω πN (fun _ => 0) rn) :
    -(∑' j, ρ ^ j * sN j) + (-(∑' j, ρ ^ j * sN j) - πN 0) * (1 - ω) / ω ≤ ∑' j, πN j := by
  have hs := (weighted_le hω0.le hω1 hπ0 hπ).1
  have h84 := MaturityBuffer.identity_84 (ρ := ρ) (w := ω) (rn := rn) (sN := sN)
    (rN := fun _ => 0) (by simp) ((summable_nat_add_iff 1).2 hs) (by simp) h320 h321
  simp only [mul_zero, tsum_zero, add_zero] at h84
  exact total_ge_spread hω0 hω1 hπ0 hπ h84

end Cochrane.AssetsRulesBalanceSheets.TidyR6TotalInflation
