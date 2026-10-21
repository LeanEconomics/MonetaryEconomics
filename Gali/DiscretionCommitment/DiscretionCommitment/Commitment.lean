/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DiscretionCommitment.Expectations
import DiscretionCommitment.ExpectationsFiniteTree
import Mathlib.Topology.Order.IntermediateValue

/-!
# Optimal policy under commitment

Galí (2015), Section 5.2.2, pp. 133–138. The central bank chooses `{π_t, x_t}` to minimise
`E_0 ∑ βᵗ (π_t² + ϑ x_t²)` subject to the Phillips curve `π_t = β E_t π_{t+1} + κ x_t + u_t`
for all `t ≥ 0`.

## Main results

* The coefficients: `four_beta_gam_sq_lt_one` (`4βγ² < 1`), `del_quad` (`γβδ² − δ + γ = 0`),
  `del_lt_one_iff`, `del_mem_Ioo_iff` (`δ ∈ (0, 1)` iff `κ > 0`, C5-9), `del_kappa_zero`
  (`δ = 1` at `κ = 0`), `one_sub_gam_beta_del` (`1 − γβδ = γ/δ`), `kappa_sq_del`
  (`κ²δ/ϑ = (1 − δ)(1 − βδ)`), `quad_roots` (the roots are `δ` and `1/(βδ) > 1`).
* (11)–(13): `foc_iff_targeting`, `targeting_iff_eleven_twelve`; (14): `nkpc_iff_priceEq`.
* (15): the factorisation `priceEq_iff_w`; `pHat_priceEq` and `priceEq_unique` (the unique bounded
  solution with `p̂_{−1} = 0`); AR(1) closed forms `pHat_ar1` (15), `gapC_ar1` (16), `gapC_zero`.
* **Deterministic optimal-policy theorem** (`Det`): for a bounded known shock path, the
  commitment path is feasible with finite loss (`candD_feasible`, `candD_finiteLoss`), is optimal
  among all feasible finite-loss paths (`candD_isOptimal`, via the Lagrangian identity
  `loss_sub_hasSum` with the transversality term), and is the unique optimum
  (`isOptimal_iff`, `existsUnique_optimal`); the first-order conditions / the targeting rule are
  necessary and sufficient (`isOptimal_iff_foc`).
* **Stochastic optimal-policy theorem**: `commitment_optimal` — among all bounded adapted plans,
  the commitment plan minimises the expected loss state by state; any plan with the same expected
  loss agrees with it in conditional mean square. The Lagrangian argument uses the tower property,
  `E_tsum` and the pull-out property `PullOut` (true for perfect foresight and finite trees,
  `perfectForesight_pullOut`, `finiteTree_pullOut`, but not one of the `ExpectationSystem` fields).
* `targeting_unique`: the targeting rule and the Phillips curve pin down the commitment plan.
* p. 137: `iterated_nkpc`. p. 138 (`ρ_u = 0`): `dis_iff_rate_rho0` (`i_t = r^e_t −
  (1 − δ)(1 − σκ/ϑ) p̂_t`, C5-1), `pHat_rho0_sum`, and `rule_implements` (the price-level rule
  with `φ_p > 0` implements the allocation uniquely; algebra restated from the Chapter 4 project).
-/

namespace Gali.DiscretionCommitment.Commitment

open Filter Topology

/-! ### The coefficients `γ` and `δ` -/

/-- Galí (2015), (14), p. 135: `γ ≡ ϑ / (ϑ(1 + β) + κ²)`. -/
noncomputable def gam (β κ ϑ : ℝ) : ℝ := ϑ / (ϑ * (1 + β) + κ ^ 2)

/-- Galí (2015), (15), p. 136: `δ ≡ (1 − √(1 − 4βγ²)) / (2γβ)`. -/
noncomputable def del (β κ ϑ : ℝ) : ℝ :=
  (1 - √(1 - 4 * β * gam β κ ϑ ^ 2)) / (2 * gam β κ ϑ * β)

/-- Galí (2015), (14), p. 135: `γ > 0`. -/
theorem gam_pos {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) : 0 < gam β κ ϑ := by
  unfold gam; positivity

/-- Galí (2015), (14), p. 135: `γ (ϑ(1 + β) + κ²) = ϑ`. -/
theorem gam_mul_denom {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) :
    gam β κ ϑ * (ϑ * (1 + β) + κ ^ 2) = ϑ := by
  unfold gam
  have : 0 < ϑ * (1 + β) + κ ^ 2 := by positivity
  field_simp

/-- Galí (2015), (14), p. 135: `γ (1 + β) ≤ 1`. -/
theorem gam_mul_le {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) : gam β κ ϑ * (1 + β) ≤ 1 := by
  have hD : 0 < ϑ * (1 + β) + κ ^ 2 := by positivity
  rw [gam, div_mul_eq_mul_div, div_le_one hD]
  nlinarith [sq_nonneg κ]

/-- Galí (2015), (14)–(15), pp. 135–136: `γ (1 + β) < 1` iff `κ ≠ 0`. -/
theorem gam_mul_lt_iff {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) :
    gam β κ ϑ * (1 + β) < 1 ↔ κ ≠ 0 := by
  have hD : 0 < ϑ * (1 + β) + κ ^ 2 := by positivity
  rw [gam, div_mul_eq_mul_div, div_lt_one hD]
  constructor
  · intro h hκ
    rw [hκ] at h
    linarith
  · intro hκ
    have := pow_pos (abs_pos.2 hκ) 2
    rw [sq_abs] at this
    linarith

/-- Galí (2015), (15), p. 136: `4βγ² < 1`, so `δ` is real (for every `κ`). -/
theorem four_beta_gam_sq_lt_one {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    4 * β * gam β κ ϑ ^ 2 < 1 := by
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hle := gam_mul_le (κ := κ) hβ0 hϑ
  have h1 : (gam β κ ϑ * (1 + β)) ^ 2 ≤ 1 := by
    have : 0 ≤ gam β κ ϑ * (1 + β) := by positivity
    nlinarith
  have h2 : 0 < gam β κ ϑ ^ 2 * (1 - β) ^ 2 := by
    have : 0 < 1 - β := by linarith
    positivity
  nlinarith

/-- Galí (2015), (15), p. 136: the square root `s = √(1 − 4βγ²)` satisfies `s² = 1 − 4βγ²`. -/
theorem sqrt_sq_eq {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    √(1 - 4 * β * gam β κ ϑ ^ 2) ^ 2 = 1 - 4 * β * gam β κ ϑ ^ 2 :=
  Real.sq_sqrt (by linarith [four_beta_gam_sq_lt_one (κ := κ) hβ0 hβ1 hϑ])

/-- Galí (2015), (15), p. 136: `√(1 − 4βγ²) < 1`. -/
theorem sqrt_lt_one {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) :
    √(1 - 4 * β * gam β κ ϑ ^ 2) < 1 := by
  rw [Real.sqrt_lt' one_pos]
  have := gam_pos (κ := κ) hβ0 hϑ
  have : 0 < 4 * β * gam β κ ϑ ^ 2 := by positivity
  linarith

/-- Galí (2015), (15), p. 136: `δ · 2γβ = 1 − √(1 − 4βγ²)`. -/
theorem del_mul {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) :
    del β κ ϑ * (2 * gam β κ ϑ * β) = 1 - √(1 - 4 * β * gam β κ ϑ ^ 2) := by
  have := gam_pos (κ := κ) hβ0 hϑ
  unfold del
  field_simp

/-- Galí (2015), (15), p. 136: `δ > 0`. -/
theorem del_pos {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) : 0 < del β κ ϑ := by
  have := gam_pos (κ := κ) hβ0 hϑ
  have := sqrt_lt_one (κ := κ) hβ0 hϑ
  unfold del
  apply div_pos <;> [linarith; positivity]

/-- Galí (2015), (15), p. 136 and footnote 4: `δ` is a root of `γβδ² − δ + γ = 0`, the
undetermined-coefficients condition for `p̂_t = δ p̂_{t−1} + b u_t` to solve (14). -/
theorem del_quad {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    gam β κ ϑ * β * del β κ ϑ ^ 2 - del β κ ϑ + gam β κ ϑ = 0 := by
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hδ := del_mul (κ := κ) hβ0 hϑ
  have hs2 := sqrt_sq_eq (κ := κ) hβ0 hβ1 hϑ
  set g := gam β κ ϑ
  set s := √(1 - 4 * β * g ^ 2)
  set d := del β κ ϑ
  have h4 : (4 * g * β) * (g * β * d ^ 2 - d + g) = 0 := by
    linear_combination (2 * g * β * d + (1 - s) - 2) * hδ + hs2
  rcases mul_eq_zero.1 h4 with h | h
  · exfalso; have : 0 < 4 * g * β := by positivity
    linarith
  · exact h

/-- Galí (2015), (15), p. 136 (C5-9): `δ < 1` if and only if `κ ≠ 0`. -/
theorem del_lt_one_iff {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    del β κ ϑ < 1 ↔ κ ≠ 0 := by
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hle := gam_mul_le (κ := κ) hβ0 hϑ
  have hiff := gam_mul_lt_iff (κ := κ) hβ0 hϑ
  set g := gam β κ ϑ
  have h0 : 0 ≤ 1 - 2 * g * β := by nlinarith
  have hgb : 0 < g * β := by positivity
  rw [del, div_lt_one (by positivity), ← hiff]
  constructor
  · intro h
    have h1 : 1 - 2 * g * β < √(1 - 4 * β * g ^ 2) := by linarith
    have h2 := (Real.lt_sqrt h0).1 h1
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg hgb.le (sub_nonneg.2 hc)]
  · intro h
    have h2 : (1 - 2 * g * β) ^ 2 < 1 - 4 * β * g ^ 2 := by nlinarith
    have := (Real.lt_sqrt h0).2 h2
    linarith

/-- Galí (2015), (15), p. 136 (C5-9): for `κ ≥ 0`, `δ ∈ (0, 1)` if and only if `κ > 0`. -/
theorem del_mem_Ioo_iff {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : 0 ≤ κ) :
    (0 < del β κ ϑ ∧ del β κ ϑ < 1) ↔ 0 < κ := by
  rw [del_lt_one_iff hβ0 hβ1 hϑ]
  exact ⟨fun h => lt_of_le_of_ne hκ (Ne.symm h.2), fun h => ⟨del_pos hβ0 hϑ, h.ne'⟩⟩

/-- Galí (2015), (15), p. 136 (C5-9, the boundary case): with `κ = 0`, `δ = 1`. -/
theorem del_kappa_zero {β ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    del β 0 ϑ = 1 := by
  have hg := gam_pos (κ := 0) hβ0 hϑ
  have hg1 : gam β 0 ϑ * (1 + β) = 1 := by
    unfold gam
    have : 0 < ϑ * (1 + β) := by positivity
    field_simp
    ring
  set g := gam β 0 ϑ
  have hs : √(1 - 4 * β * g ^ 2) = g * (1 - β) := by
    have hnn : 0 ≤ g * (1 - β) := mul_nonneg hg.le (by linarith)
    rw [← Real.sqrt_sq hnn]
    congr 1
    linear_combination (-(1 : ℝ)) * (g * (1 + β) + 1) * hg1
  rw [del, hs, div_eq_one_iff_eq (by positivity)]
  linear_combination -hg1

/-- Galí (2015), (15), p. 136: `1 − γβδ = γ/δ` (used to get `b = δ/(1 − δβρ_u)`). -/
theorem one_sub_gam_beta_del {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    1 - gam β κ ϑ * β * del β κ ϑ = gam β κ ϑ / del β κ ϑ := by
  have hd := del_pos (κ := κ) hβ0 hϑ
  have hq := del_quad (κ := κ) hβ0 hβ1 hϑ
  rw [eq_div_iff hd.ne']
  linear_combination -hq

/-- Galí (2015), (15), p. 136: `δ/γ = 1 + βδ²`. -/
theorem del_div_gam {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    del β κ ϑ / gam β κ ϑ = 1 + β * del β κ ϑ ^ 2 := by
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hq := del_quad (κ := κ) hβ0 hβ1 hϑ
  rw [div_eq_iff hg.ne']
  linear_combination -hq

/-- Galí (2015), p. 143 (key identity, used for (15) and (24)): `κ²δ/ϑ = (1 − δ)(1 − βδ)`. -/
theorem kappa_sq_del {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    κ ^ 2 * del β κ ϑ / ϑ = (1 - del β κ ϑ) * (1 - β * del β κ ϑ) := by
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hq := del_quad (κ := κ) hβ0 hβ1 hϑ
  have hm := gam_mul_denom (κ := κ) hβ0 hϑ
  rw [div_eq_iff hϑ.ne']
  apply mul_left_cancel₀ hg.ne'
  linear_combination del β κ ϑ * hm - ϑ * hq

/-- Galí (2015), (15), p. 136 (factorisation): `γβz² − z + γ = γβ (z − δ)(z − 1/(βδ))`, so the
roots of the characteristic equation of (14) are `δ` and `1/(βδ)`. -/
theorem quad_factor {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (z : ℝ) :
    gam β κ ϑ * β * z ^ 2 - z + gam β κ ϑ =
      gam β κ ϑ * β * (z - del β κ ϑ) * (z - 1 / (β * del β κ ϑ)) := by
  have hd := del_pos (κ := κ) hβ0 hϑ
  have h1 := one_sub_gam_beta_del (κ := κ) hβ0 hβ1 hϑ
  have h2 : gam β κ ϑ * β * (z - del β κ ϑ) * (z - 1 / (β * del β κ ϑ)) =
      gam β κ ϑ * β * z ^ 2 - z * (gam β κ ϑ * β * del β κ ϑ + gam β κ ϑ / del β κ ϑ) +
        gam β κ ϑ := by
    field_simp
    ring
  rw [h2, ← h1]
  ring

/-- Galí (2015), (15), p. 136: for `κ ≠ 0`, `δ` is the unique root of `γβz² − z + γ = 0`
inside the unit interval; the other root `1/(βδ)` exceeds one. -/
theorem quad_roots {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0) :
    (∀ z, gam β κ ϑ * β * z ^ 2 - z + gam β κ ϑ = 0 ↔ z = del β κ ϑ ∨ z = 1 / (β * del β κ ϑ))
      ∧ 1 < 1 / (β * del β κ ϑ) := by
  have hd := del_pos (κ := κ) hβ0 hϑ
  have hd1 := (del_lt_one_iff hβ0 hβ1 hϑ).2 hκ
  have hg := gam_pos (κ := κ) hβ0 hϑ
  refine ⟨fun z => ?_, ?_⟩
  · rw [quad_factor hβ0 hβ1 hϑ z]
    have : gam β κ ϑ * β ≠ 0 := by positivity
    simp only [mul_eq_zero, this, false_or, sub_eq_zero]
  · rw [lt_div_iff₀ (by positivity), one_mul]
    nlinarith

/-! ### Lags, the price-level gap and the targeting rule -/

/-- Galí (2015), p. 135: the lag operator with zero initial condition, `(lag p)_0 = 0` and
`(lag p)_{t+1} = p_t`; it encodes `ξ_{−1} = 0` and `p̂_{−1} = 0`. -/
def lag {α : Type*} [Zero α] (p : ℕ → α) : ℕ → α
  | 0 => 0
  | t + 1 => p t

/-- Galí (2015), p. 135: `(lag p)_0 = 0`. -/
@[simp] theorem lag_zero {α : Type*} [Zero α] (p : ℕ → α) : lag p 0 = 0 := rfl

/-- Galí (2015), p. 135: `(lag p)_{t+1} = p_t`. -/
@[simp] theorem lag_succ {α : Type*} [Zero α] (p : ℕ → α) (t : ℕ) : lag p (t + 1) = p t := rfl

/-- Galí (2015), p. 135: the lag commutes with scalar multiplication. -/
theorem lag_smul {α : Type*} [AddCommGroup α] [Module ℝ α] (c : ℝ) (p : ℕ → α) (t : ℕ) :
    lag (fun s => c • p s) t = c • lag p t := by
  cases t <;> simp

/-- Galí (2015), p. 135: the lag commutes with negation. -/
theorem lag_neg {α : Type*} [AddCommGroup α] (p : ℕ → α) (t : ℕ) :
    lag (fun s => -p s) t = -lag p t := by
  cases t <;> simp

/-- Galí (2015), p. 135: the price-level gap `p̂_t = p_t − p_{−1} = ∑_{s ≤ t} π_s`. -/
def priceGap {α : Type*} [AddCommMonoid α] (π : ℕ → α) (t : ℕ) : α :=
  ∑ s ∈ Finset.range (t + 1), π s

/-- Galí (2015), p. 135: `p̂_t − p̂_{t−1} = π_t` (with `p̂_{−1} = 0`). -/
theorem priceGap_sub_lag {α : Type*} [AddCommGroup α] (π : ℕ → α) (t : ℕ) :
    priceGap π t - lag (priceGap π) t = π t := by
  cases t with
  | zero => simp [priceGap]
  | succ t => simp [priceGap, Finset.sum_range_succ _ (t + 1)]

/-- Galí (2015), p. 135: conversely, any `p` is the price-level gap of `p_t − p_{t−1}`. -/
theorem priceGap_of_sub_lag {α : Type*} [AddCommGroup α] (p : ℕ → α) :
    priceGap (fun t => p t - lag p t) = p := by
  funext t
  induction t with
  | zero => simp [priceGap]
  | succ t ih =>
    rw [priceGap, Finset.sum_range_succ, ← priceGap, ih]
    simp

/-! ### The commitment first-order conditions and the targeting rule (11)–(13) -/

/-- Galí (2015), p. 134–135: the first-order conditions of the commitment problem,
`ϑ x_t − κ ξ_t = 0` and `π_t + ξ_t − ξ_{t−1} = 0` for all `t ≥ 0`, with `ξ_{−1} = 0`
(statewise; the book's "differentiating with respect to `y_t`" should read `x_t`, C5-4). -/
def FOC (κ ϑ : ℝ) (π x ξ : ℕ → ℝ) : Prop :=
  ∀ t, ϑ * x t = κ * ξ t ∧ π t + ξ t - lag ξ t = 0

/-- Galí (2015), (13), p. 135: the first-order conditions hold for some multipliers iff the
targeting rule in levels `x_t = −(κ/ϑ) p̂_t` holds; then `ξ_t = −p̂_t`. -/
theorem foc_iff_targeting {κ ϑ : ℝ} (hϑ : ϑ ≠ 0) (π x : ℕ → ℝ) :
    (∃ ξ, FOC κ ϑ π x ξ) ↔ ∀ t, x t = -(κ / ϑ) * priceGap π t := by
  constructor
  · rintro ⟨ξ, hξ⟩
    have hξp : ∀ t, ξ t = -priceGap π t := by
      intro t
      induction t with
      | zero =>
        have := (hξ 0).2
        simp only [lag_zero] at this
        simp only [priceGap, zero_add, Finset.range_one, Finset.sum_singleton]
        linarith
      | succ t ih =>
        have := (hξ (t + 1)).2
        simp only [lag_succ] at this
        rw [priceGap, Finset.sum_range_succ, ← priceGap]
        linarith
    intro t
    have := (hξ t).1
    rw [hξp t] at this
    field_simp
    linarith
  · intro h
    refine ⟨fun t => -priceGap π t, fun t => ⟨?_, ?_⟩⟩
    · rw [h t]; field_simp
    · have := priceGap_sub_lag π t
      rw [lag_neg]
      linarith

/-- Galí (2015), (11)–(13), p. 135: the targeting rule in levels (13) is equivalent to
`x_0 = −(κ/ϑ) π_0` (11) together with `x_t − x_{t−1} = −(κ/ϑ) π_t` for `t ≥ 1` (12). -/
theorem targeting_iff_eleven_twelve (κ ϑ : ℝ) (π x : ℕ → ℝ) :
    (∀ t, x t = -(κ / ϑ) * priceGap π t) ↔
      (x 0 = -(κ / ϑ) * π 0 ∧ ∀ t, x (t + 1) - x t = -(κ / ϑ) * π (t + 1)) := by
  constructor
  · intro h
    refine ⟨by rw [h 0]; simp [priceGap], fun t => ?_⟩
    rw [h (t + 1), h t, priceGap, Finset.sum_range_succ, ← priceGap]
    ring
  · rintro ⟨h0, h1⟩ t
    induction t with
    | zero => rw [h0]; simp [priceGap]
    | succ t ih =>
      rw [priceGap, Finset.sum_range_succ, ← priceGap]
      linear_combination h1 t + ih

/-! ### The model under uncertainty -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), (2), p. 128: the New Keynesian Phillips curve with a cost-push shock,
`π_t = β E_t π_{t+1} + κ x_t + u_t` (`x` is the welfare-relevant output gap). -/
def NKPC (β κ : ℝ) (u π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t = β • 𝔼.E t (π (t + 1)) + κ • x t + u t

/-- Galí (2015), (14), p. 135: `p̂_t = γ p̂_{t−1} + γβ E_t p̂_{t+1} + γ u_t`, `p̂_{−1} = 0`. -/
def PriceEq (β κ ϑ : ℝ) (u p : ℕ → Ω → ℝ) : Prop :=
  ∀ t, p t = gam β κ ϑ • lag p t + (gam β κ ϑ * β) • 𝔼.E t (p (t + 1)) + gam β κ ϑ • u t

/-- Galí (2015), p. 135: inflation implied by a price-level gap, `π_t = p̂_t − p̂_{t−1}`. -/
def inflOf (p : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := p t - lag p t

/-- Galí (2015), (13), p. 135: the output gap implied by the targeting rule,
`x_t = −(κ/ϑ) p̂_t`. -/
noncomputable def gapOf (κ ϑ : ℝ) (p : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := (-(κ / ϑ)) • p t

/-- Galí (2015), p. 135: the lag of an adapted process is adapted (`p̂_{t−1}` is known at `t`). -/
theorem lag_adapted {p : ℕ → Ω → ℝ} (hp : 𝔼.Adapted p) : 𝔼.Adapted (lag p) := by
  intro t
  cases t with
  | zero => exact map_zero _
  | succ t =>
    change 𝔼.E (t + 1) (p t) = p t
    have := 𝔼.known (Nat.le_succ t) (p t)
    rwa [hp t] at this

/-- Galí (2015), p. 135 (pointwise algebra): with `x_t = −(κ/ϑ) p̂_t`, the Phillips curve
`p̂_t − p̂_{t−1} = β (E_t p̂_{t+1} − p̂_t) + κ x_t + u_t` is equivalent to (14). -/
theorem pc_iff_fourteen {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) (P L Ep U : ℝ) :
    P - L = β * (Ep - P) + κ * (-(κ / ϑ) * P) + U ↔
      P = gam β κ ϑ * L + gam β κ ϑ * β * Ep + gam β κ ϑ * U := by
  have hD : 0 < ϑ * (1 + β) + κ ^ 2 := by positivity
  rw [gam]
  constructor <;> intro h
  · field_simp at h ⊢
    linarith
  · field_simp at h ⊢
    linarith

/-- Galí (2015), (14), p. 135: under the targeting rule (13), the Phillips curve (2) holds iff
the price-level gap satisfies (14). -/
theorem nkpc_iff_priceEq {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) {u p : ℕ → Ω → ℝ}
    (hp : 𝔼.Adapted p) :
    NKPC 𝔼 β κ u (inflOf p) (gapOf κ ϑ p) ↔ PriceEq 𝔼 β κ ϑ u p := by
  have hE : ∀ t, 𝔼.E t (inflOf p (t + 1)) = 𝔼.E t (p (t + 1)) - p t := fun t => by
    change 𝔼.E t (p (t + 1) - p t) = _
    rw [map_sub, hp t]
  constructor
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    rw [hE] at e
    simp only [inflOf, gapOf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    exact (pc_iff_fourteen hβ0 hϑ _ _ _ _).1 e
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    rw [hE]
    simp only [inflOf, gapOf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    exact (pc_iff_fourteen hβ0 hϑ _ _ _ _).2 e

/-! ### Factorisation of (14) -/

/-- Galí (2015), (15), p. 136: the quasi-difference `w_t = p̂_t − δ p̂_{t−1}`. -/
noncomputable def wOf (β κ ϑ : ℝ) (p : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  p t - del β κ ϑ • lag p t

/-- Galí (2015), (15), p. 136 (pointwise algebra): (14) holds iff the quasi-difference solves
the forward equation `w_t = βδ E_t w_{t+1} + δ u_t`; this is the factorisation
`(1 − γL − γβL⁻¹) = (γ/δ)(1 − δL)(1 − βδL⁻¹)`. -/
theorem fourteen_iff_w {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (P L Ep U : ℝ) :
    P = gam β κ ϑ * L + gam β κ ϑ * β * Ep + gam β κ ϑ * U ↔
      P - del β κ ϑ * L = β * del β κ ϑ * (Ep - del β κ ϑ * P) + del β κ ϑ * U := by
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hdg : del β κ ϑ = gam β κ ϑ * (1 + β * del β κ ϑ ^ 2) := by
    rw [← del_div_gam hβ0 hβ1 hϑ]; field_simp
  set g := gam β κ ϑ
  set d := del β κ ϑ
  have key : P - d * L - β * d * (Ep - d * P) - d * U =
      (1 + β * d ^ 2) * (P - (g * L + g * β * Ep + g * U)) := by
    linear_combination (-(L + β * Ep + U)) * hdg
  have hpos : 0 < 1 + β * d ^ 2 := by positivity
  constructor
  · intro h
    linear_combination key + (1 + β * d ^ 2) * h
  · intro h
    have : (1 + β * d ^ 2) * (P - (g * L + g * β * Ep + g * U)) = 0 := by
      rw [← key, h]; ring
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · linarith

/-- Galí (2015), (15), p. 136: for an adapted price-level gap, (14) holds iff the
quasi-difference `w` solves `w_t = βδ E_t w_{t+1} + δ u_t`. -/
theorem priceEq_iff_w {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ)
    {u p : ℕ → Ω → ℝ} (hp : 𝔼.Adapted p) :
    PriceEq 𝔼 β κ ϑ u p ↔ ∀ t, wOf β κ ϑ p t =
      (β * del β κ ϑ) • 𝔼.E t (wOf β κ ϑ p (t + 1)) + del β κ ϑ • u t := by
  have hE : ∀ t, 𝔼.E t (wOf β κ ϑ p (t + 1)) = 𝔼.E t (p (t + 1)) - del β κ ϑ • p t :=
    fun t => by
      change 𝔼.E t (p (t + 1) - del β κ ϑ • p t) = _
      rw [map_sub, map_smul, hp t]
  constructor
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    rw [hE]
    simp only [wOf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    exact (fourteen_iff_w hβ0 hβ1 hϑ _ _ _ _).1 e
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    rw [hE] at e
    simp only [wOf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    exact (fourteen_iff_w hβ0 hβ1 hϑ _ _ _ _).2 e

/-! ### The commitment path -/

/-- Galí (2015), (15), p. 136: `0 ≤ βδ < 1` for `κ ≠ 0`. -/
theorem beta_del_mem {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0) :
    0 ≤ β * del β κ ϑ ∧ β * del β κ ϑ < 1 := by
  have hd := del_pos (κ := κ) hβ0 hϑ
  have hd1 := (del_lt_one_iff hβ0 hβ1 hϑ).2 hκ
  exact ⟨by positivity, by nlinarith⟩

/-- Galí (2015), (15), p. 136: the forward part `w_t = δ ∑_{k ≥ 0} (βδ)ᵏ E_t u_{t+k}` of the
commitment solution (the unique bounded solution of `w_t = βδ E_t w_{t+1} + δ u_t`). -/
noncomputable def fwd (β κ ϑ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  del β κ ϑ • 𝔼.forwardSeries (β * del β κ ϑ) u t

/-- Galí (2015), (15), p. 136: the commitment price-level gap, `p̂_t = δ p̂_{t−1} + w_t`,
`p̂_{−1} = 0`. -/
noncomputable def pHat (β κ ϑ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fwd 𝔼 β κ ϑ u 0
  | t + 1 => del β κ ϑ • pHat β κ ϑ u t + fwd 𝔼 β κ ϑ u (t + 1)

/-- Galí (2015), (15), p. 136: `p̂_t = δ p̂_{t−1} + w_t` for all `t ≥ 0` (`p̂_{−1} = 0`). -/
theorem pHat_eq (β κ ϑ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) :
    pHat 𝔼 β κ ϑ u t = del β κ ϑ • lag (pHat 𝔼 β κ ϑ u) t + fwd 𝔼 β κ ϑ u t := by
  cases t with
  | zero => simp [pHat]
  | succ t => rfl

/-- Galí (2015), (15), p. 136: the commitment inflation path `π_t = p̂_t − p̂_{t−1}`. -/
noncomputable def inflC (β κ ϑ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := inflOf (pHat 𝔼 β κ ϑ u)

/-- Galí (2015), (13) and (16), p. 135–136: the commitment output gap `x_t = −(κ/ϑ) p̂_t`. -/
noncomputable def gapC (β κ ϑ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  gapOf κ ϑ (pHat 𝔼 β κ ϑ u)

/-- Galí (2015), (15), p. 136: `w_t = βδ E_t w_{t+1} + δ u_t`. -/
theorem fwd_solves {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) (t : ℕ) :
    fwd 𝔼 β κ ϑ u t = (β * del β κ ϑ) • 𝔼.E t (fwd 𝔼 β κ ϑ u (t + 1)) + del β κ ϑ • u t := by
  obtain ⟨ha0, ha1⟩ := beta_del_mem hβ0 hβ1 hϑ hκ
  rw [fwd, fwd, 𝔼.forwardSeries_solves ha0 ha1 hu hua t, map_smul, smul_add, smul_comm]

/-- Galí (2015), (15), p. 136: `w` is bounded. -/
theorem fwd_bounded {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) : BoundedProc (fwd 𝔼 β κ ϑ u) := by
  obtain ⟨ha0, ha1⟩ := beta_del_mem hβ0 hβ1 hϑ hκ
  obtain ⟨B, hB⟩ := 𝔼.forwardSeries_bounded ha0 ha1 hu
  refine ⟨del β κ ϑ * B, fun t ω => ?_⟩
  have hd := del_pos (κ := κ) hβ0 hϑ
  simp only [fwd, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hd]
  exact mul_le_mul_of_nonneg_left (hB t ω) hd.le

/-- Galí (2015), (15), p. 136: `w` is adapted. -/
theorem fwd_adapted {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) :
    𝔼.Adapted (fwd 𝔼 β κ ϑ u) := by
  intro t
  conv_lhs => rw [fwd_solves 𝔼 hβ0 hβ1 hϑ hκ hu hua t]
  rw [map_add, map_smul, map_smul, 𝔼.E_E_self, hua t, ← fwd_solves 𝔼 hβ0 hβ1 hϑ hκ hu hua t]

/-- Galí (2015), (15), p. 136: the commitment price-level gap is adapted. -/
theorem pHat_adapted {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) :
    𝔼.Adapted (pHat 𝔼 β κ ϑ u) := by
  have hf := fwd_adapted 𝔼 hβ0 hβ1 hϑ hκ hu hua
  intro t
  induction t with
  | zero => exact hf 0
  | succ t ih =>
    change 𝔼.E (t + 1) (del β κ ϑ • pHat 𝔼 β κ ϑ u t + fwd 𝔼 β κ ϑ u (t + 1)) = _
    have h1 : 𝔼.E (t + 1) (pHat 𝔼 β κ ϑ u t) = pHat 𝔼 β κ ϑ u t := by
      have := 𝔼.known (Nat.le_succ t) (pHat 𝔼 β κ ϑ u t)
      rwa [ih] at this
    rw [map_add, map_smul, h1, hf (t + 1)]
    rfl

/-- Galí (2015), (15), p. 136: the commitment price-level gap is bounded,
`|p̂_t| ≤ B/(1 − δ)` when `|w_t| ≤ B`. -/
theorem pHat_bounded {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) : BoundedProc (pHat 𝔼 β κ ϑ u) := by
  obtain ⟨B, hB⟩ := fwd_bounded 𝔼 hβ0 hβ1 hϑ hκ hu
  have hd := del_pos (κ := κ) hβ0 hϑ
  have hd1 := (del_lt_one_iff hβ0 hβ1 hϑ).2 hκ
  have h1d : 0 < 1 - del β κ ϑ := by linarith
  refine ⟨B / (1 - del β κ ϑ), fun t ω => ?_⟩
  induction t with
  | zero =>
    change |fwd 𝔼 β κ ϑ u 0 ω| ≤ _
    have hB0 := hB 0 ω
    have : 0 ≤ B := (abs_nonneg _).trans hB0
    rw [le_div_iff₀ h1d]
    nlinarith
  | succ t ih =>
    change |del β κ ϑ * pHat 𝔼 β κ ϑ u t ω + fwd 𝔼 β κ ϑ u (t + 1) ω| ≤ _
    have h2 := hB (t + 1) ω
    have h3 : |del β κ ϑ * pHat 𝔼 β κ ϑ u t ω| ≤ del β κ ϑ * (B / (1 - del β κ ϑ)) := by
      rw [abs_mul, abs_of_pos hd]
      exact mul_le_mul_of_nonneg_left ih hd.le
    have h4 : del β κ ϑ * (B / (1 - del β κ ϑ)) + B = B / (1 - del β κ ϑ) := by
      field_simp; ring
    calc _ ≤ |del β κ ϑ * pHat 𝔼 β κ ϑ u t ω| + |fwd 𝔼 β κ ϑ u (t + 1) ω| := abs_add_le _ _
      _ ≤ _ := by linarith

/-- Galí (2015), (15), p. 136: the quasi-difference of the commitment price-level gap is `w`. -/
theorem wOf_pHat (β κ ϑ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) :
    wOf β κ ϑ (pHat 𝔼 β κ ϑ u) t = fwd 𝔼 β κ ϑ u t := by
  rw [wOf, pHat_eq 𝔼 β κ ϑ u t]
  abel

/-- **Galí (2015), (14)–(15), pp. 135–136**: the commitment price-level gap solves (14) with
`p̂_{−1} = 0`. -/
theorem pHat_priceEq {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) :
    PriceEq 𝔼 β κ ϑ u (pHat 𝔼 β κ ϑ u) := by
  rw [priceEq_iff_w 𝔼 hβ0 hβ1 hϑ (pHat_adapted 𝔼 hβ0 hβ1 hϑ hκ hu hua)]
  intro t
  rw [wOf_pHat, wOf_pHat]
  exact fwd_solves 𝔼 hβ0 hβ1 hϑ hκ hu hua t

/-- **Galí (2015), (15), p. 136 (uniqueness)**: the commitment price-level gap is the unique
bounded adapted solution of (14) with `p̂_{−1} = 0`. -/
theorem priceEq_unique {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) {q : ℕ → Ω → ℝ}
    (hq : PriceEq 𝔼 β κ ϑ u q) (hqa : 𝔼.Adapted q) (hqb : BoundedProc q) :
    q = pHat 𝔼 β κ ϑ u := by
  obtain ⟨ha0, ha1⟩ := beta_del_mem hβ0 hβ1 hϑ hκ
  have hw := (priceEq_iff_w 𝔼 hβ0 hβ1 hϑ hqa).1 hq
  obtain ⟨Mq, hMq⟩ := hqb
  have hd := del_pos (κ := κ) hβ0 hϑ
  have hwb : BoundedProc (wOf β κ ϑ q) := by
    refine ⟨Mq + del β κ ϑ * Mq, fun t ω => ?_⟩
    have hl : |lag q t ω| ≤ Mq := by
      cases t with
      | zero => simpa using (abs_nonneg (q 0 ω)).trans (hMq 0 ω)
      | succ t => exact hMq t ω
    simp only [wOf, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    calc _ ≤ |q t ω| + |del β κ ϑ * lag q t ω| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_mul, abs_of_pos hd]
        exact add_le_add (hMq t ω) (mul_le_mul_of_nonneg_left hl hd.le)
  have hweq : wOf β κ ϑ q = fwd 𝔼 β κ ϑ u :=
    𝔼.forward_unique (by rw [abs_of_nonneg ha0]; exact ha1) hw
      (fwd_solves 𝔼 hβ0 hβ1 hϑ hκ hu hua) hwb (fwd_bounded 𝔼 hβ0 hβ1 hϑ hκ hu)
  funext t
  induction t with
  | zero =>
    have := congrFun hweq 0
    simpa [wOf, pHat] using this
  | succ t ih =>
    have := congrFun hweq (t + 1)
    simp only [wOf, lag_succ, ih] at this
    rw [sub_eq_iff_eq_add] at this
    rw [this, add_comm]
    rfl

/-- Galí (2015), (14), p. 135: the commitment path satisfies the Phillips curve (2). -/
theorem cand_nkpc {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) :
    NKPC 𝔼 β κ u (inflC 𝔼 β κ ϑ u) (gapC 𝔼 β κ ϑ u) :=
  (nkpc_iff_priceEq 𝔼 hβ0 hϑ (pHat_adapted 𝔼 hβ0 hβ1 hϑ hκ hu hua)).2
    (pHat_priceEq 𝔼 hβ0 hβ1 hϑ hκ hu hua)

/-- Galí (2015), (15)–(16), p. 136: the commitment inflation and output gap are adapted and
bounded. -/
theorem cand_adapted_bounded {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ)
    (hκ : κ ≠ 0) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) :
    𝔼.Adapted (inflC 𝔼 β κ ϑ u) ∧ 𝔼.Adapted (gapC 𝔼 β κ ϑ u) ∧
      BoundedProc (inflC 𝔼 β κ ϑ u) ∧ BoundedProc (gapC 𝔼 β κ ϑ u) := by
  have hpa := pHat_adapted 𝔼 hβ0 hβ1 hϑ hκ hu hua
  have hla := lag_adapted 𝔼 hpa
  obtain ⟨B, hB⟩ := pHat_bounded 𝔼 hβ0 hβ1 hϑ hκ hu
  have hl : ∀ t ω, |lag (pHat 𝔼 β κ ϑ u) t ω| ≤ B := fun t ω => by
    cases t with
    | zero => simpa using (abs_nonneg (pHat 𝔼 β κ ϑ u 0 ω)).trans (hB 0 ω)
    | succ t => exact hB t ω
  refine ⟨fun t => ?_, fun t => ?_, ⟨B + B, fun t ω => ?_⟩, ⟨|κ / ϑ| * B, fun t ω => ?_⟩⟩
  · change 𝔼.E t (pHat 𝔼 β κ ϑ u t - lag (pHat 𝔼 β κ ϑ u) t) = _
    rw [map_sub, hpa t, hla t]; rfl
  · change 𝔼.E t ((-(κ / ϑ)) • pHat 𝔼 β κ ϑ u t) = _
    rw [map_smul, hpa t]; rfl
  · change |pHat 𝔼 β κ ϑ u t ω - lag (pHat 𝔼 β κ ϑ u) t ω| ≤ _
    exact (abs_sub _ _).trans (add_le_add (hB t ω) (hl t ω))
  · change |(-(κ / ϑ)) * pHat 𝔼 β κ ϑ u t ω| ≤ _
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hB t ω) (abs_nonneg _)

/-! ### AR(1) cost-push shocks: (15) and (16) -/

/-- Galí (2015), (15), p. 136: `1 − δβρ_u > 0` for `|ρ_u| < 1`. -/
theorem one_sub_dbr_pos {β κ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    (hρ : |ρ| < 1) : 0 < 1 - del β κ ϑ * β * ρ := by
  obtain ⟨ha0, ha1⟩ := beta_del_mem hβ0 hβ1 hϑ hκ
  have h1 : del β κ ϑ * β * ρ ≤ β * del β κ ϑ * |ρ| := by
    rw [mul_comm (del β κ ϑ) β]
    exact mul_le_mul_of_nonneg_left (le_abs_self ρ) ha0
  have h2 : β * del β κ ϑ * |ρ| < 1 := by
    calc β * del β κ ϑ * |ρ| ≤ β * del β κ ϑ * 1 :=
          mul_le_mul_of_nonneg_left hρ.le ha0
      _ < 1 := by rw [mul_one]; exact ha1
  linarith

/-- Galí (2015), (15), p. 136 and footnote 4: with an AR(1) shock, the forward part is
`w_t = δ/(1 − δβρ_u) u_t`. -/
theorem fwd_ar1 {β κ ϑ ρ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    (hρ : |ρ| < 1) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 ρ u) (t : ℕ) :
    fwd 𝔼 β κ ϑ u t = (del β κ ϑ / (1 - del β κ ϑ * β * ρ)) • u t := by
  obtain ⟨ha0, ha1⟩ := beta_del_mem hβ0 hβ1 hϑ hκ
  have hpos := one_sub_dbr_pos hβ0 hβ1 hϑ hκ hρ
  set c := del β κ ϑ / (1 - del β κ ϑ * β * ρ)
  have hsol : ∀ t, (fun t => c • u t) t =
      (β * del β κ ϑ) • 𝔼.E t ((fun t => c • u t) (t + 1)) + del β κ ϑ • u t := by
    intro t
    simp only [map_smul, har.2 t, smul_smul, ← add_smul]
    congr 1
    simp only [c]
    field_simp
    ring
  have hb : BoundedProc (fun t => c • u t) := by
    refine ⟨|c| * M, fun t ω => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hu t ω) (abs_nonneg c)
  have := 𝔼.forward_unique (by rw [abs_of_nonneg ha0]; exact ha1)
    (fwd_solves 𝔼 hβ0 hβ1 hϑ hκ hu har.1) hsol (fwd_bounded 𝔼 hβ0 hβ1 hϑ hκ hu) hb
  exact congrFun this t

/-- **Galí (2015), (15), p. 136**: with an AR(1) cost-push shock the commitment price-level gap
follows `p̂_t = δ p̂_{t−1} + δ/(1 − δβρ_u) u_t` for `t ≥ 0`, `p̂_{−1} = 0`. -/
theorem pHat_ar1 {β κ ϑ ρ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    (hρ : |ρ| < 1) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 ρ u) (t : ℕ) :
    pHat 𝔼 β κ ϑ u t = del β κ ϑ • lag (pHat 𝔼 β κ ϑ u) t +
      (del β κ ϑ / (1 - del β κ ϑ * β * ρ)) • u t := by
  rw [pHat_eq, fwd_ar1 𝔼 hβ0 hβ1 hϑ hκ hρ hu har]

/-- **Galí (2015), (16), p. 136**: the commitment output gap follows
`x_t = δ x_{t−1} − κδ/(ϑ(1 − δβρ_u)) u_t` for `t ≥ 1`, and (with `x_{−1} = 0`) at `t = 0`. -/
theorem gapC_ar1 {β κ ϑ ρ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    (hρ : |ρ| < 1) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 ρ u) (t : ℕ) :
    gapC 𝔼 β κ ϑ u t = del β κ ϑ • lag (gapC 𝔼 β κ ϑ u) t -
      (κ * del β κ ϑ / (ϑ * (1 - del β κ ϑ * β * ρ))) • u t := by
  have hpos := one_sub_dbr_pos hβ0 hβ1 hϑ hκ hρ
  have hl : lag (gapC 𝔼 β κ ϑ u) t = (-(κ / ϑ)) • lag (pHat 𝔼 β κ ϑ u) t :=
    lag_smul _ _ t
  rw [hl, gapC, gapOf, pHat_ar1 𝔼 hβ0 hβ1 hϑ hκ hρ hu har t, smul_add, smul_smul, smul_smul,
    smul_smul, sub_eq_add_neg (G := Ω → ℝ), ← neg_smul]
  congr 2
  · ring
  · field_simp

/-- **Galí (2015), p. 136**: the impact response of the output gap under commitment,
`x_0 = −κδ/(ϑ(1 − δβρ_u)) u_0`. -/
theorem gapC_zero {β κ ϑ ρ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    (hρ : |ρ| < 1) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 ρ u) :
    gapC 𝔼 β κ ϑ u 0 = (-(κ * del β κ ϑ / (ϑ * (1 - del β κ ϑ * β * ρ)))) • u 0 := by
  rw [gapC_ar1 𝔼 hβ0 hβ1 hϑ hκ hρ hu har 0, neg_smul]
  simp

/-! ### The Lagrangian argument: telescoping with a transversality term -/

/-- Galí (2015), p. 134 (the Lagrangian argument, abstract form): if
`g_t = D_t + 2 (h_t − h_{t+1})` with `D_t ≥ 0`, `h_0 = 0` (the constraint of period `−1` does
not bind, `ξ_{−1} = 0`) and `h_t → 0` (transversality), and `∑ g_t = G`, then `∑ D_t = G`. -/
theorem hasSum_of_telescope {g D h : ℕ → ℝ} {G : ℝ} (hg : HasSum g G) (hD : ∀ t, 0 ≤ D t)
    (hgt : ∀ t, g t = D t + 2 * (h t - h (t + 1))) (h0 : h 0 = 0)
    (hh : Tendsto h atTop (𝓝 0)) : HasSum D G := by
  rw [hasSum_iff_tendsto_nat_of_nonneg hD]
  have hpart : (fun n => ∑ t ∈ Finset.range n, D t) =
      fun n => ∑ t ∈ Finset.range n, g t + 2 * h n := by
    funext n
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, hgt n]; ring
  rw [hpart]
  simpa using hg.tendsto_sum_nat.add (hh.const_mul 2)

/-! ### Optimality under uncertainty -/

/-- Galí (2015), p. 134 ("the law of iterated expectations has been used"): the pull-out
property `E_t (a y) = a E_t y` for `a` known at `t`. It holds for true conditional expectations
(`perfectForesight_pullOut`, `finiteTree_pullOut`) but is not among the `ExpectationSystem`
fields, so the stochastic optimality theorems take it as a hypothesis. -/
def PullOut : Prop := ∀ t (a y : Ω → ℝ), 𝔼.E t a = a → 𝔼.E t (a * y) = a * 𝔼.E t y

/-- Galí (2015), p. 134: perfect foresight has the pull-out property. -/
theorem perfectForesight_pullOut : PullOut perfectForesight := fun _ _ _ _ => rfl

/-- Galí (2015), p. 134: the cell-average expectations of a finite event tree have the pull-out
property, so the hypothesis is satisfiable under genuine uncertainty. -/
theorem finiteTree_pullOut {Ω' : Type*} [Fintype Ω'] (T : ExpectationsFiniteTree.FiniteTree Ω') :
    PullOut T.toExpectationSystem := by
  classical
  intro t a y ha
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E] at ha ⊢
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  funext ω
  have hcell : ∀ ω', T.info t ω' ω → a ω' = a ω := fun ω' h => by
    rw [← ha, T.condE_congr a h]
  simp only [ExpectationsFiniteTree.FiniteTree.condE, ExpectationsFiniteTree.FiniteTree.num,
    Pi.mul_apply]
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun ω' _ => ?_
  by_cases h : T.info t ω' ω
  · simp only [h, ↓reduceIte, hcell ω' h]
    ring
  · simp only [h, ↓reduceIte, mul_zero]

/-- Galí (2015), p. 134: the period loss `π_t² + ϑ x_t²`. -/
def periodLoss (ϑ : ℝ) (π x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := fun ω => π t ω ^ 2 + ϑ * x t ω ^ 2

/-- Galí (2015), p. 134: the expected loss `E_0 ∑_{t ≥ 0} βᵗ (π_t² + ϑ x_t²)` (a date-0 random
variable). -/
noncomputable def expLoss (β ϑ : ℝ) (π x : ℕ → Ω → ℝ) : Ω → ℝ :=
  𝔼.E 0 (fun ω => ∑' t, β ^ t * periodLoss ϑ π x t ω)

/-- Galí (2015), p. 134: an admissible plan: bounded adapted inflation and output gap
satisfying the Phillips curve (2) at every date and state. -/
def Plan (β κ : ℝ) (u π x : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β κ u π x ∧ 𝔼.Adapted π ∧ 𝔼.Adapted x ∧ BoundedProc π ∧ BoundedProc x

/-- Galí (2015), p. 134: for a bounded plan the expected loss is the genuine infinite sum
`∑ βᵗ E_0(π_t² + ϑ x_t²)` (`E_0` commutes with the geometrically dominated series). -/
theorem expLoss_hasSum {β ϑ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hϑ : 0 ≤ ϑ)
    {π x : ℕ → Ω → ℝ} (hπ : BoundedProc π) (hx : BoundedProc x) (ω : Ω) :
    HasSum (fun t => β ^ t * 𝔼.E 0 (periodLoss ϑ π x t) ω) (expLoss 𝔼 β ϑ π x ω) := by
  obtain ⟨A, hA⟩ := hπ
  obtain ⟨B, hB⟩ := hx
  have hpl : ∀ t ω, |periodLoss ϑ π x t ω| ≤ A ^ 2 + ϑ * B ^ 2 := by
    intro t ω
    have h1 : π t ω ^ 2 ≤ A ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hA t ω) 2
    have h2 : x t ω ^ 2 ≤ B ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB t ω) 2
    unfold periodLoss
    rw [abs_of_nonneg (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h2 hϑ]
  have hf : ∀ k ω, |β ^ k * periodLoss ϑ π x k ω| ≤ β ^ k * (A ^ 2 + ϑ * B ^ 2) := by
    intro k ω
    rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
    exact mul_le_mul_of_nonneg_left (hpl k ω) (pow_nonneg hβ0 k)
  have hE : 𝔼.E 0 (fun ω' => ∑' k, β ^ k * periodLoss ϑ π x k ω') ω =
      ∑' k, 𝔼.E 0 (fun ω' => β ^ k * periodLoss ϑ π x k ω') ω := 𝔼.E_tsum hβ0 hβ1 hf 0 ω
  have heq : ∀ k, 𝔼.E 0 (fun ω' => β ^ k * periodLoss ϑ π x k ω') ω =
      β ^ k * 𝔼.E 0 (periodLoss ϑ π x k) ω := fun k => by
    have : (fun ω' => β ^ k * periodLoss ϑ π x k ω') = β ^ k • periodLoss ϑ π x k := rfl
    rw [this, map_smul]; rfl
  have hs : Summable (fun t => β ^ t * 𝔼.E 0 (periodLoss ϑ π x t) ω) :=
    Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (A ^ 2 + ϑ * B ^ 2)) (fun k => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
        exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hpl k) 0 ω) (pow_nonneg hβ0 k))
  convert hs.hasSum using 1
  change 𝔼.E 0 (fun ω' => ∑' k, β ^ k * periodLoss ϑ π x k ω') ω = _
  rw [hE]
  exact tsum_congr heq

/-- Galí (2015), p. 134 (the Lagrangian identity, one period): if `(π*, x*)` satisfies the
first-order conditions with an adapted multiplier `ξ` and `(π, x)` is any other solution of the
Phillips curve, then, with `d = (π, x) − (π*, x*)`,
`E_0 ℓ_t − E_0 ℓ*_t = E_0(dπ_t² + ϑ dx_t²) + 2 E_0(ξ_{t−1} dπ_t) − 2β E_0(ξ_t dπ_{t+1})`
(the conditional expectation in the constraint is removed by the law of iterated expectations
and the pull-out property). -/
theorem E0_identity (hpo : PullOut 𝔼) {β κ ϑ : ℝ} {u π x πs xs ξ : ℕ → Ω → ℝ}
    (hn : NKPC 𝔼 β κ u π x) (hns : NKPC 𝔼 β κ u πs xs) (hξa : 𝔼.Adapted ξ)
    (hfoc : ∀ t, ϑ • xs t = κ • ξ t ∧ πs t = lag ξ t - ξ t) (t : ℕ) (ω : Ω) :
    𝔼.E 0 (periodLoss ϑ π x t) ω - 𝔼.E 0 (periodLoss ϑ πs xs t) ω =
      𝔼.E 0 (fun ω => (π t ω - πs t ω) ^ 2 + ϑ * (x t ω - xs t ω) ^ 2) ω +
        2 * 𝔼.E 0 (fun ω => lag ξ t ω * (π t ω - πs t ω)) ω -
          2 * β * 𝔼.E 0 (fun ω => lag ξ (t + 1) ω * (π (t + 1) ω - πs (t + 1) ω)) ω := by
  have hfun : periodLoss ϑ π x t - periodLoss ϑ πs xs t =
      (fun ω => (π t ω - πs t ω) ^ 2 + ϑ * (x t ω - xs t ω) ^ 2) +
        (2 : ℝ) • (fun ω => lag ξ t ω * (π t ω - πs t ω)) -
          (2 * β) • (ξ t * (𝔼.E t (π (t + 1)) - 𝔼.E t (πs (t + 1)))) := by
    funext ω'
    have n1 := congrFun (hn t) ω'
    have n2 := congrFun (hns t) ω'
    have f1 := congrFun (hfoc t).1 ω'
    have f2 := congrFun (hfoc t).2 ω'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at n1 n2 f1 f2
    simp only [periodLoss, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.mul_apply]
    linear_combination 2 * (π t ω' - πs t ω') * f2 + 2 * (x t ω' - xs t ω') * f1 -
      2 * ξ t ω' * (n1 - n2)
  have hpull : 𝔼.E 0 (ξ t * (𝔼.E t (π (t + 1)) - 𝔼.E t (πs (t + 1)))) =
      𝔼.E 0 (fun ω => lag ξ (t + 1) ω * (π (t + 1) ω - πs (t + 1) ω)) := by
    rw [← map_sub, ← hpo t _ _ (hξa t), 𝔼.tower (Nat.zero_le t)]
    rfl
  have := congrFun (congrArg (𝔼.E 0) hfun) ω
  rw [map_sub, map_sub, map_add, map_smul, map_smul, hpull] at this
  simpa [mul_assoc] using this

/-- Galí (2015), p. 134: `E_0` of a nonnegative random variable is nonnegative. -/
theorem E0_nonneg {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) (t : ℕ) (ω : Ω) : 0 ≤ 𝔼.E t f ω := by
  have := 𝔼.mono t (show (0 : Ω → ℝ) ≤ f from hf) ω
  rwa [map_zero] at this

/-- **Galí (2015), pp. 134–135 (sufficiency of the first-order conditions, stochastic)**: if a
plan `(π*, x*)` satisfies the commitment first-order conditions `ϑ x*_t = κ ξ_t`,
`π*_t = ξ_{t−1} − ξ_t` (`ξ_{−1} = 0`) with a bounded adapted multiplier, then for every other
plan `(π, x)` the excess expected loss is the genuine infinite sum
`E_0 L(π, x) − E_0 L(π*, x*) = ∑ βᵗ E_0((π_t − π*_t)² + ϑ (x_t − x*_t)²)`. -/
theorem expLoss_sub_hasSum (hpo : PullOut 𝔼) {β κ ϑ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hϑ : 0 ≤ ϑ) {u π x πs xs ξ : ℕ → Ω → ℝ} (hp : Plan 𝔼 β κ u π x)
    (hps : Plan 𝔼 β κ u πs xs) (hξa : 𝔼.Adapted ξ) (hξb : BoundedProc ξ)
    (hfoc : ∀ t, ϑ • xs t = κ • ξ t ∧ πs t = lag ξ t - ξ t) (ω : Ω) :
    HasSum (fun t => β ^ t * 𝔼.E 0 (fun ω => (π t ω - πs t ω) ^ 2 + ϑ * (x t ω - xs t ω) ^ 2) ω)
      (expLoss 𝔼 β ϑ π x ω - expLoss 𝔼 β ϑ πs xs ω) := by
  obtain ⟨hn, -, -, hπb, hxb⟩ := hp
  obtain ⟨hns, -, -, hπsb, hxsb⟩ := hps
  obtain ⟨A, hA⟩ := hπb
  obtain ⟨As, hAs⟩ := hπsb
  obtain ⟨Z, hZ⟩ := hξb
  have hZ0 : 0 ≤ Z := (abs_nonneg _).trans (hZ 0 ω)
  have hlag : ∀ t ω, |lag ξ t ω| ≤ Z := fun t ω => by
    cases t with
    | zero => simpa using hZ0
    | succ t => exact hZ t ω
  have hH : ∀ t ω, |lag ξ t ω * (π t ω - πs t ω)| ≤ Z * (A + As) := fun t ω => by
    rw [abs_mul]
    exact mul_le_mul (hlag t ω) ((abs_sub _ _).trans (add_le_add (hA t ω) (hAs t ω)))
      (abs_nonneg _) hZ0
  refine hasSum_of_telescope
    ((expLoss_hasSum 𝔼 hβ0 hβ1 hϑ ⟨A, hA⟩ hxb ω).sub (expLoss_hasSum 𝔼 hβ0 hβ1 hϑ ⟨As, hAs⟩ hxsb ω))
    (fun t => mul_nonneg (pow_nonneg hβ0 t) (E0_nonneg 𝔼 (fun ω => by positivity) 0 ω))
    (h := fun t => β ^ t * 𝔼.E 0 (fun ω => lag ξ t ω * (π t ω - πs t ω)) ω)
    (fun t => ?_) ?_ ?_
  · rw [← mul_sub, E0_identity 𝔼 hpo hn hns hξa hfoc t ω, pow_succ]
    ring
  · simp only [lag_zero, Pi.zero_apply, zero_mul, pow_zero, one_mul]
    rw [𝔼.const 0 0]
  · refine squeeze_zero_norm (a := fun t => β ^ t * (Z * (A + As))) (fun t => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hH t) 0 ω) (pow_nonneg hβ0 t)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const (Z * (A + As))

/-- **Galí (2015), pp. 134–135 (optimality)**: a plan satisfying the first-order conditions with
a bounded adapted multiplier has the smallest expected loss among all plans, state by state. -/
theorem expLoss_le_of_foc (hpo : PullOut 𝔼) {β κ ϑ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hϑ : 0 ≤ ϑ) {u π x πs xs ξ : ℕ → Ω → ℝ} (hp : Plan 𝔼 β κ u π x)
    (hps : Plan 𝔼 β κ u πs xs) (hξa : 𝔼.Adapted ξ) (hξb : BoundedProc ξ)
    (hfoc : ∀ t, ϑ • xs t = κ • ξ t ∧ πs t = lag ξ t - ξ t) (ω : Ω) :
    expLoss 𝔼 β ϑ πs xs ω ≤ expLoss 𝔼 β ϑ π x ω :=
  sub_nonneg.1 ((expLoss_sub_hasSum 𝔼 hpo hβ0 hβ1 hϑ hp hps hξa hξb hfoc ω).nonneg
    (fun t => mul_nonneg (pow_nonneg hβ0 t) (E0_nonneg 𝔼 (fun ω => by positivity) 0 ω)))

/-- **Galí (2015), pp. 134–135 (uniqueness of the optimum, stochastic)**: a plan attaining the
same expected loss in state `ω` as a plan satisfying the first-order conditions coincides with it
in conditional mean square: `E_0 (π_t − π*_t)² = E_0 (x_t − x*_t)² = 0` at `ω`, for every `t`
(under perfect foresight this is equality of the paths). -/
theorem eq_of_expLoss_eq (hpo : PullOut 𝔼) {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hϑ : 0 < ϑ) {u π x πs xs ξ : ℕ → Ω → ℝ} (hp : Plan 𝔼 β κ u π x)
    (hps : Plan 𝔼 β κ u πs xs) (hξa : 𝔼.Adapted ξ) (hξb : BoundedProc ξ)
    (hfoc : ∀ t, ϑ • xs t = κ • ξ t ∧ πs t = lag ξ t - ξ t) (ω : Ω)
    (heq : expLoss 𝔼 β ϑ π x ω = expLoss 𝔼 β ϑ πs xs ω) (t : ℕ) :
    𝔼.E 0 (fun ω => (π t ω - πs t ω) ^ 2) ω = 0 ∧ 𝔼.E 0 (fun ω => (x t ω - xs t ω) ^ 2) ω = 0 := by
  have hs := expLoss_sub_hasSum 𝔼 hpo hβ0.le hβ1 hϑ.le hp hps hξa hξb hfoc ω
  rw [heq, sub_self] at hs
  have hz := (hasSum_zero_iff_of_nonneg (fun t => mul_nonneg (pow_nonneg hβ0.le t)
    (E0_nonneg 𝔼 (fun ω => by positivity) 0 ω))).1 hs
  have ht := congrFun hz t
  simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', hβ0.ne', ne_eq, false_and,
    false_or] at ht
  have hsplit : (fun ω => (π t ω - πs t ω) ^ 2 + ϑ * (x t ω - xs t ω) ^ 2) =
      (fun ω => (π t ω - πs t ω) ^ 2) + ϑ • (fun ω => (x t ω - xs t ω) ^ 2) := rfl
  rw [hsplit, map_add, map_smul] at ht
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht
  have h1 := E0_nonneg 𝔼 (f := fun ω => (π t ω - πs t ω) ^ 2) (fun ω => by positivity) 0 ω
  have h2 := E0_nonneg 𝔼 (f := fun ω => (x t ω - xs t ω) ^ 2) (fun ω => by positivity) 0 ω
  have h3 := mul_nonneg hϑ.le h2
  constructor
  · linarith
  · have : ϑ * 𝔼.E 0 (fun ω => (x t ω - xs t ω) ^ 2) ω = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hϑ.ne'
    · exact h

/-- Galí (2015), p. 135: the commitment path satisfies the first-order conditions with the
multiplier `ξ_t = −p̂_t`. -/
theorem cand_foc {β κ ϑ : ℝ} (hϑ : 0 < ϑ) (u : ℕ → Ω → ℝ) (t : ℕ) :
    ϑ • gapC 𝔼 β κ ϑ u t = κ • (fun s => -pHat 𝔼 β κ ϑ u s) t ∧
      inflC 𝔼 β κ ϑ u t = lag (fun s => -pHat 𝔼 β κ ϑ u s) t - (fun s => -pHat 𝔼 β κ ϑ u s) t := by
  refine ⟨?_, ?_⟩
  · simp only [gapC, gapOf, smul_smul, smul_neg, ← neg_smul]
    congr 1
    field_simp
  · rw [lag_neg]
    simp only [inflC, inflOf, sub_neg_eq_add]
    abel

/-- **Galí (2015), §5.2.2, pp. 133–136 (THE OPTIMAL POLICY UNDER COMMITMENT, stochastic)**:
for a bounded adapted cost-push process, the path (15)–(16) (in general form `p̂_t = δ p̂_{t−1} +
δ ∑ (βδ)ᵏ E_t u_{t+k}`, `π_t = p̂_t − p̂_{t−1}`, `x_t = −(κ/ϑ) p̂_t`) is an admissible plan and,
state by state, minimises the expected loss `E_0 ∑ βᵗ (π_t² + ϑ x_t²)` among all bounded adapted
plans; any plan with the same expected loss at `ω` equals it in conditional mean square. -/
theorem commitment_optimal (hpo : PullOut 𝔼) {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hϑ : 0 < ϑ) (hκ : κ ≠ 0) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) :
    Plan 𝔼 β κ u (inflC 𝔼 β κ ϑ u) (gapC 𝔼 β κ ϑ u) ∧
      ∀ π x, Plan 𝔼 β κ u π x → ∀ ω,
        expLoss 𝔼 β ϑ (inflC 𝔼 β κ ϑ u) (gapC 𝔼 β κ ϑ u) ω ≤ expLoss 𝔼 β ϑ π x ω ∧
        (expLoss 𝔼 β ϑ π x ω = expLoss 𝔼 β ϑ (inflC 𝔼 β κ ϑ u) (gapC 𝔼 β κ ϑ u) ω →
          ∀ t, 𝔼.E 0 (fun ω => (π t ω - inflC 𝔼 β κ ϑ u t ω) ^ 2) ω = 0 ∧
            𝔼.E 0 (fun ω => (x t ω - gapC 𝔼 β κ ϑ u t ω) ^ 2) ω = 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := cand_adapted_bounded 𝔼 hβ0 hβ1 hϑ hκ hu hua
  have hplan : Plan 𝔼 β κ u (inflC 𝔼 β κ ϑ u) (gapC 𝔼 β κ ϑ u) :=
    ⟨cand_nkpc 𝔼 hβ0 hβ1 hϑ hκ hu hua, h1, h2, h3, h4⟩
  have hξa : 𝔼.Adapted (fun s => -pHat 𝔼 β κ ϑ u s) := fun t => by
    simp only [map_neg, pHat_adapted 𝔼 hβ0 hβ1 hϑ hκ hu hua t]
  have hξb : BoundedProc (fun s => -pHat 𝔼 β κ ϑ u s) := by
    obtain ⟨B, hB⟩ := pHat_bounded 𝔼 hβ0 hβ1 hϑ hκ hu
    exact ⟨B, fun t ω => by simpa using hB t ω⟩
  refine ⟨hplan, fun π x hp ω => ⟨?_, ?_⟩⟩
  · exact expLoss_le_of_foc 𝔼 hpo hβ0.le hβ1 hϑ.le hp hplan hξa hξb (cand_foc 𝔼 hϑ u) ω
  · intro heq
    exact eq_of_expLoss_eq 𝔼 hpo hβ0 hβ1 hϑ hp hplan hξa hξb (cand_foc 𝔼 hϑ u) ω heq

/-! ### The deterministic problem: a known cost-push path and finite loss -/

namespace Det

/-- Galí (2015), p. 134 (perfect foresight): the constraints `π_t = β π_{t+1} + κ x_t + u_t`,
`t ≥ 0`. -/
def Feasible (β κ : ℝ) (u π x : ℕ → ℝ) : Prop := ∀ t, π t = β * π (t + 1) + κ * x t + u t

/-- Galí (2015), p. 134: the discounted period loss `βᵗ (π_t² + ϑ x_t²)`. -/
def lossTerm (β ϑ : ℝ) (π x : ℕ → ℝ) (t : ℕ) : ℝ := β ^ t * (π t ^ 2 + ϑ * x t ^ 2)

/-- Galí (2015), p. 134: the loss `∑ βᵗ (π_t² + ϑ x_t²)` is finite. -/
def FiniteLoss (β ϑ : ℝ) (π x : ℕ → ℝ) : Prop := Summable (lossTerm β ϑ π x)

/-- Galí (2015), p. 134: the loss `∑_{t ≥ 0} βᵗ (π_t² + ϑ x_t²)` (used on finite-loss paths). -/
noncomputable def loss (β ϑ : ℝ) (π x : ℕ → ℝ) : ℝ := ∑' t, lossTerm β ϑ π x t

/-- Galí (2015), p. 134: `(π, x)` solves the commitment problem: it is feasible, has finite loss,
and its loss is no larger than that of any feasible path with finite loss. -/
def IsOptimal (β κ ϑ : ℝ) (u π x : ℕ → ℝ) : Prop :=
  Feasible β κ u π x ∧ FiniteLoss β ϑ π x ∧
    ∀ π' x', Feasible β κ u π' x' → FiniteLoss β ϑ π' x' → loss β ϑ π x ≤ loss β ϑ π' x'

/-- Galí (2015), p. 134 (transversality): on a finite-loss path `βᵗ π_t² → 0` and
`βᵗ x_t² → 0`. -/
theorem tendsto_disc_sq {β ϑ : ℝ} (hβ0 : 0 ≤ β) (hϑ : 0 < ϑ) {π x : ℕ → ℝ}
    (hl : FiniteLoss β ϑ π x) :
    Tendsto (fun t => β ^ t * π t ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun t => β ^ t * x t ^ 2) atTop (𝓝 0) := by
  have hL := hl.tendsto_atTop_zero
  constructor
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL
      (fun t => by positivity) (fun t => ?_)
    have : 0 ≤ β ^ t * (ϑ * x t ^ 2) := by positivity
    simp only [lossTerm]
    nlinarith
  · have hL' := hL.div_const ϑ
    rw [zero_div] at hL'
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL'
      (fun t => by positivity) (fun t => ?_)
    have : 0 ≤ β ^ t * π t ^ 2 := by positivity
    simp only [lossTerm]
    rw [le_div_iff₀ hϑ]
    nlinarith

/-- **Galí (2015), pp. 134–135 (sufficiency of the first-order conditions, deterministic)**:
if a feasible finite-loss path `(π*, x*)` satisfies the first-order conditions with multipliers
`ξ` (`ξ_{−1} = 0`), then for every feasible finite-loss path `(π, x)`
`L(π, x) − L(π*, x*) = ∑ βᵗ ((π_t − π*_t)² + ϑ (x_t − x*_t)²)`: the Lagrangian cross terms
telescope to `−2β^{T+1} ξ_T (π_{T+1} − π*_{T+1}) → 0` (transversality). -/
theorem loss_sub_hasSum {β κ ϑ : ℝ} (hβ0 : 0 ≤ β) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u π x πs xs ξ : ℕ → ℝ} (hf : Feasible β κ u π x) (hl : FiniteLoss β ϑ π x)
    (hfs : Feasible β κ u πs xs) (hls : FiniteLoss β ϑ πs xs) (hξ : FOC κ ϑ πs xs ξ) :
    HasSum (fun t => β ^ t * ((π t - πs t) ^ 2 + ϑ * (x t - xs t) ^ 2))
      (loss β ϑ π x - loss β ϑ πs xs) := by
  have hξx : ∀ t, ξ t = ϑ / κ * xs t := fun t => by
    field_simp; linarith [(hξ t).1]
  obtain ⟨hπ0, -⟩ := tendsto_disc_sq hβ0 hϑ hl
  obtain ⟨hπs0, hxs0⟩ := tendsto_disc_sq hβ0 hϑ hls
  have hξ0 : Tendsto (fun t => β ^ t * ξ t ^ 2) atTop (𝓝 0) := by
    have : (fun t => β ^ t * ξ t ^ 2) = fun t => (ϑ / κ) ^ 2 * (β ^ t * xs t ^ 2) := by
      funext t; rw [hξx t]; ring
    rw [this]
    simpa using hxs0.const_mul ((ϑ / κ) ^ 2)
  have hlag0 : Tendsto (fun t => β ^ t * lag ξ t ^ 2) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    have : (fun t => β ^ (t + 1) * lag ξ (t + 1) ^ 2) = fun t => β * (β ^ t * ξ t ^ 2) := by
      funext t; rw [lag_succ, pow_succ]; ring
    rw [this]
    simpa using hξ0.const_mul β
  have hd0 : Tendsto (fun t => β ^ t * (π t - πs t) ^ 2) atTop (𝓝 0) := by
    have hup := (hπ0.const_mul 2).add (hπs0.const_mul 2)
    rw [mul_zero, add_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun t => by positivity) (fun t => ?_)
    have hb : 0 ≤ β ^ t := pow_nonneg hβ0 t
    have : (π t - πs t) ^ 2 ≤ 2 * π t ^ 2 + 2 * πs t ^ 2 := by nlinarith [sq_nonneg (π t + πs t)]
    have := mul_le_mul_of_nonneg_left this hb
    simp only
    nlinarith
  refine hasSum_of_telescope (hl.hasSum.sub hls.hasSum)
    (fun t => by positivity) (h := fun t => β ^ t * lag ξ t * (π t - πs t))
    (fun t => ?_) (by simp) ?_
  · have n1 := hf t
    have n2 := hfs t
    have f1 := (hξ t).1
    have f2 := (hξ t).2
    simp only [lossTerm, lag_succ]
    linear_combination β ^ t * (2 * (π t - πs t) * f2 + 2 * (x t - xs t) * f1 -
      2 * ξ t * (n1 - n2))
  · have hup := hlag0.add hd0
    rw [add_zero] at hup
    refine squeeze_zero_norm (fun t => ?_) hup
    have hb : 0 ≤ β ^ t := pow_nonneg hβ0 t
    have hab : |lag ξ t * (π t - πs t)| ≤ lag ξ t ^ 2 + (π t - πs t) ^ 2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (lag ξ t + (π t - πs t)),
        sq_nonneg (lag ξ t - (π t - πs t))]
    rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg hb]
    nlinarith [mul_le_mul_of_nonneg_left hab hb]

/-- **Galí (2015), pp. 134–135 (optimality, deterministic)**: a feasible finite-loss path
satisfying the first-order conditions is optimal. -/
theorem isOptimal_of_foc {β κ ϑ : ℝ} (hβ0 : 0 ≤ β) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u πs xs ξ : ℕ → ℝ} (hfs : Feasible β κ u πs xs) (hls : FiniteLoss β ϑ πs xs)
    (hξ : FOC κ ϑ πs xs ξ) : IsOptimal β κ ϑ u πs xs :=
  ⟨hfs, hls, fun _ _ hf hl => sub_nonneg.1
    ((loss_sub_hasSum hβ0 hϑ hκ hf hl hfs hls hξ).nonneg (fun t => by positivity))⟩

/-- **Galí (2015), pp. 134–135 (uniqueness, deterministic)**: a feasible finite-loss path with the
same loss as a path satisfying the first-order conditions coincides with it (strict convexity:
the excess loss is `∑ βᵗ (dπ_t² + ϑ dx_t²)`). -/
theorem eq_of_loss_eq {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u π x πs xs ξ : ℕ → ℝ} (hf : Feasible β κ u π x) (hl : FiniteLoss β ϑ π x)
    (hfs : Feasible β κ u πs xs) (hls : FiniteLoss β ϑ πs xs) (hξ : FOC κ ϑ πs xs ξ)
    (heq : loss β ϑ π x = loss β ϑ πs xs) : π = πs ∧ x = xs := by
  have hs := loss_sub_hasSum hβ0.le hϑ hκ hf hl hfs hls hξ
  rw [heq, sub_self] at hs
  have hz := (hasSum_zero_iff_of_nonneg (fun t => by positivity)).1 hs
  have ht : ∀ t, (π t - πs t) ^ 2 + ϑ * (x t - xs t) ^ 2 = 0 := fun t => by
    have := congrFun hz t
    simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', hβ0.ne', ne_eq, false_and,
      false_or] at this
    exact this
  refine ⟨funext fun t => ?_, funext fun t => ?_⟩
  · have h1 := ht t
    have : (π t - πs t) ^ 2 = 0 := by nlinarith [sq_nonneg (π t - πs t), sq_nonneg (x t - xs t)]
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linarith
  · have h1 := ht t
    have h2 : ϑ * (x t - xs t) ^ 2 = 0 := by
      nlinarith [sq_nonneg (π t - πs t), sq_nonneg (x t - xs t)]
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hϑ.ne'
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      linarith

/-- Galí (2015), p. 136: a known cost-push path as a (trivially adapted) process on the
one-point state space of perfect foresight. -/
def lift (u : ℕ → ℝ) : ℕ → Unit → ℝ := fun t _ => u t

/-- **Galí (2015), (15), p. 136 (deterministic)**: the commitment price-level gap for a known
cost-push path, `p̂_t = δ p̂_{t−1} + δ ∑_{k ≥ 0} (βδ)ᵏ u_{t+k}`, `p̂_{−1} = 0`. -/
noncomputable def pHatD (β κ ϑ : ℝ) (u : ℕ → ℝ) (t : ℕ) : ℝ :=
  pHat perfectForesight β κ ϑ (lift u) t ()

/-- Galí (2015), (15), p. 136 (deterministic): commitment inflation `π_t = p̂_t − p̂_{t−1}`. -/
noncomputable def inflD (β κ ϑ : ℝ) (u : ℕ → ℝ) (t : ℕ) : ℝ :=
  pHatD β κ ϑ u t - lag (pHatD β κ ϑ u) t

/-- Galí (2015), (13), (16), pp. 135–136 (deterministic): commitment output gap
`x_t = −(κ/ϑ) p̂_t`. -/
noncomputable def gapD (β κ ϑ : ℝ) (u : ℕ → ℝ) (t : ℕ) : ℝ := -(κ / ϑ) * pHatD β κ ϑ u t

/-- Galí (2015), p. 136: the lag commutes with evaluation at the single state. -/
theorem lag_pHatD (β κ ϑ : ℝ) (u : ℕ → ℝ) (t : ℕ) :
    lag (pHatD β κ ϑ u) t = lag (pHat perfectForesight β κ ϑ (lift u)) t () := by
  cases t <;> rfl

/-- Galí (2015), (15), p. 136 (deterministic): the commitment price-level gap is bounded. -/
theorem pHatD_bounded {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → ℝ} (hu : ∀ t, |u t| ≤ M) : ∃ B, ∀ t, |pHatD β κ ϑ u t| ≤ B := by
  obtain ⟨B, hB⟩ := pHat_bounded perfectForesight hβ0 hβ1 hϑ hκ (u := lift u)
    (fun t _ => hu t)
  exact ⟨B, fun t => hB t ()⟩

/-- Galí (2015), (14)–(16), pp. 135–136 (deterministic): the commitment path is feasible. -/
theorem candD_feasible {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → ℝ} (hu : ∀ t, |u t| ≤ M) :
    Feasible β κ u (inflD β κ ϑ u) (gapD β κ ϑ u) := by
  intro t
  have h := congrFun (cand_nkpc perfectForesight hβ0 hβ1 hϑ hκ (u := lift u) (fun t _ => hu t)
    (fun _ => rfl) t) ()
  simp only [inflD, gapD, lag_pHatD]
  exact h

/-- Galí (2015), p. 135 (deterministic): the commitment path satisfies the first-order
conditions with `ξ_t = −p̂_t`. -/
theorem candD_foc {β κ ϑ : ℝ} (hϑ : 0 < ϑ) (u : ℕ → ℝ) :
    FOC κ ϑ (inflD β κ ϑ u) (gapD β κ ϑ u) (fun t => -pHatD β κ ϑ u t) := by
  intro t
  have h := cand_foc perfectForesight (β := β) (κ := κ) hϑ (lift u) t
  have h1 := congrFun h.1 ()
  have h2 := congrFun h.2 ()
  refine ⟨h1, ?_⟩
  have hl : lag (fun t => -pHatD β κ ϑ u t) t =
      lag (fun s => -pHat perfectForesight β κ ϑ (lift u) s) t () := by
    cases t <;> rfl
  rw [hl]
  simp only [inflD, lag_pHatD]
  change inflC perfectForesight β κ ϑ (lift u) t () + _ - _ = 0
  rw [h2]
  simp only [Pi.sub_apply, Pi.neg_apply, pHatD]
  ring

/-- Galí (2015), p. 134 (deterministic): a bounded path has finite loss. -/
theorem finiteLoss_of_bounded {β ϑ A B : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hϑ : 0 ≤ ϑ)
    {π x : ℕ → ℝ} (hπ : ∀ t, |π t| ≤ A) (hx : ∀ t, |x t| ≤ B) : FiniteLoss β ϑ π x := by
  refine Summable.of_nonneg_of_le (fun t => by unfold lossTerm; positivity) (fun t => ?_)
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (A ^ 2 + ϑ * B ^ 2))
  have h1 : π t ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hπ t) 2
  have h2 : x t ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hx t) 2
  unfold lossTerm
  exact mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_left h2 hϑ])
    (pow_nonneg hβ0 t)

/-- Galí (2015), (15)–(16), p. 136 (deterministic): the commitment path has finite loss. -/
theorem candD_finiteLoss {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → ℝ} (hu : ∀ t, |u t| ≤ M) : FiniteLoss β ϑ (inflD β κ ϑ u) (gapD β κ ϑ u) := by
  obtain ⟨B, hB⟩ := pHatD_bounded hβ0 hβ1 hϑ hκ hu
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  refine finiteLoss_of_bounded hβ0.le hβ1 hϑ.le (A := B + B) (B := |κ / ϑ| * B)
    (fun t => ?_) (fun t => ?_)
  · have hl : |lag (pHatD β κ ϑ u) t| ≤ B := by
      cases t with
      | zero => simpa using hB0
      | succ t => exact hB t
    exact (abs_sub _ _).trans (add_le_add (hB t) hl)
  · simp only [gapD, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hB t) (abs_nonneg _)

/-- **Galí (2015), §5.2.2, pp. 133–136 (THE OPTIMAL POLICY UNDER COMMITMENT, deterministic)**:
for a bounded known cost-push path, the commitment path is optimal among all feasible paths
with finite loss. -/
theorem candD_isOptimal {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → ℝ} (hu : ∀ t, |u t| ≤ M) : IsOptimal β κ ϑ u (inflD β κ ϑ u) (gapD β κ ϑ u) :=
  isOptimal_of_foc hβ0.le hϑ hκ (candD_feasible hβ0 hβ1 hϑ hκ hu)
    (candD_finiteLoss hβ0 hβ1 hϑ hκ hu) (candD_foc hϑ u)

/-- **Galí (2015), §5.2.2 (uniqueness, deterministic)**: the commitment path is the only
optimal path. -/
theorem isOptimal_iff {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → ℝ} (hu : ∀ t, |u t| ≤ M) (π x : ℕ → ℝ) :
    IsOptimal β κ ϑ u π x ↔ π = inflD β κ ϑ u ∧ x = gapD β κ ϑ u := by
  have hc := candD_isOptimal hβ0 hβ1 hϑ hκ hu
  constructor
  · rintro ⟨hf, hl, hmin⟩
    have h1 := hmin _ _ hc.1 hc.2.1
    have h2 := hc.2.2 _ _ hf hl
    exact eq_of_loss_eq hβ0 hϑ hκ hf hl hc.1 hc.2.1 (candD_foc hϑ u) (le_antisymm h1 h2)
  · rintro ⟨rfl, rfl⟩
    exact hc

/-- **Galí (2015), §5.2.2 (existence and uniqueness, deterministic)**: the commitment problem
has exactly one solution. -/
theorem existsUnique_optimal {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ)
    (hκ : κ ≠ 0) {u : ℕ → ℝ} (hu : ∀ t, |u t| ≤ M) :
    ∃! p : (ℕ → ℝ) × (ℕ → ℝ), IsOptimal β κ ϑ u p.1 p.2 := by
  refine ⟨(inflD β κ ϑ u, gapD β κ ϑ u), candD_isOptimal hβ0 hβ1 hϑ hκ hu, ?_⟩
  rintro ⟨π, x⟩ h
  obtain ⟨h1, h2⟩ := (isOptimal_iff hβ0 hβ1 hϑ hκ hu π x).1 h
  rw [h1, h2]

/-- **Galí (2015), pp. 134–135 (necessity and sufficiency of the first-order conditions)**: a
feasible finite-loss path is optimal iff it satisfies the first-order conditions for some
multipliers, iff it satisfies the targeting rule `x_t = −(κ/ϑ) p̂_t` (13). -/
theorem isOptimal_iff_foc {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → ℝ} (hu : ∀ t, |u t| ≤ M) {π x : ℕ → ℝ} (hf : Feasible β κ u π x)
    (hl : FiniteLoss β ϑ π x) :
    (IsOptimal β κ ϑ u π x ↔ ∃ ξ, FOC κ ϑ π x ξ) ∧
      (IsOptimal β κ ϑ u π x ↔ ∀ t, x t = -(κ / ϑ) * priceGap π t) := by
  have h1 : IsOptimal β κ ϑ u π x ↔ ∃ ξ, FOC κ ϑ π x ξ := by
    constructor
    · intro h
      obtain ⟨rfl, rfl⟩ := (isOptimal_iff hβ0 hβ1 hϑ hκ hu π x).1 h
      exact ⟨_, candD_foc hϑ u⟩
    · rintro ⟨ξ, hξ⟩
      exact isOptimal_of_foc hβ0.le hϑ hκ hf hl hξ
  exact ⟨h1, h1.trans (foc_iff_targeting hϑ.ne' π x)⟩

end Det

namespace Det

/-- **Galí (2015), (15), p. 136 (deterministic, general shock path)**: the commitment price-level
gap is `p̂_t = δ p̂_{t−1} + δ ∑_{k ≥ 0} (βδ)ᵏ u_{t+k}`, `p̂_{−1} = 0`. -/
theorem pHatD_eq (β κ ϑ : ℝ) (u : ℕ → ℝ) (t : ℕ) :
    pHatD β κ ϑ u t = del β κ ϑ * lag (pHatD β κ ϑ u) t +
      del β κ ϑ * ∑' k, (β * del β κ ϑ) ^ k * u (t + k) := by
  rw [lag_pHatD]
  exact congrFun (pHat_eq perfectForesight β κ ϑ (lift u) t) ()

end Det

/-! ### The targeting rule pins down the commitment path -/

/-- **Galí (2015), (13)–(15), pp. 135–136**: the commitment path is the only bounded adapted
plan satisfying the Phillips curve and the targeting rule `x_t = −(κ/ϑ) p̂_t`,
`p̂_t = ∑_{s ≤ t} π_s`. -/
theorem targeting_unique {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) {π x : ℕ → Ω → ℝ}
    (hn : NKPC 𝔼 β κ u π x) (hxa : 𝔼.Adapted x) (hxb : BoundedProc x)
    (ht : ∀ t, x t = (-(κ / ϑ)) • priceGap π t) :
    π = inflC 𝔼 β κ ϑ u ∧ x = gapC 𝔼 β κ ϑ u := by
  have hp : ∀ t, priceGap π t = (-(ϑ / κ)) • x t := fun t => by
    rw [ht t, smul_smul]
    have : -(ϑ / κ) * -(κ / ϑ) = 1 := by field_simp
    rw [this, one_smul]
  have hpa : 𝔼.Adapted (priceGap π) := fun t => by rw [hp t, map_smul, hxa t]
  have hpb : BoundedProc (priceGap π) := by
    obtain ⟨B, hB⟩ := hxb
    refine ⟨|ϑ / κ| * B, fun t ω => ?_⟩
    rw [hp t]
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hB t ω) (abs_nonneg _)
  have hπ : inflOf (priceGap π) = π := funext fun t => priceGap_sub_lag π t
  have hx : gapOf κ ϑ (priceGap π) = x := funext fun t => (ht t).symm
  have hn' : NKPC 𝔼 β κ u (inflOf (priceGap π)) (gapOf κ ϑ (priceGap π)) := by
    rw [hπ, hx]; exact hn
  have heq := priceEq_unique 𝔼 hβ0 hβ1 hϑ hκ hu hua
    ((nkpc_iff_priceEq 𝔼 hβ0 hϑ hpa).1 hn') hpa hpb
  refine ⟨?_, ?_⟩
  · rw [← hπ, heq]; rfl
  · rw [← hx, heq]; rfl

/-! ### The iterated Phillips curve (p. 137) -/

/-- **Galí (2015), p. 137**: iterating (2) forward, in any bounded adapted plan with an AR(1)
cost-push shock,
`π_t = κ x_t + κ ∑_{k ≥ 1} βᵏ E_t x_{t+k} + u_t/(1 − βρ_u)`. -/
theorem iterated_nkpc {β κ ρ M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ : |ρ| < 1)
    {u π x : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 ρ u)
    (hn : NKPC 𝔼 β κ u π x) (hπb : BoundedProc π) (hxa : 𝔼.Adapted x) (hxb : BoundedProc x)
    (t : ℕ) (ω : Ω) :
    π t ω = κ * x t ω + κ * ∑' k, β ^ (k + 1) * 𝔼.E t (x (t + (k + 1))) ω +
      (1 - β * ρ)⁻¹ * u t ω := by
  obtain ⟨B, hB⟩ := hxb
  set w : ℕ → Ω → ℝ := fun t => κ • x t + u t with hw
  have hwb : ∀ t ω, |w t ω| ≤ |κ| * B + M := fun t ω => by
    simp only [hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ (hu t ω))
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hB t ω) (abs_nonneg κ)
  have hwa : 𝔼.Adapted w := fun t => by
    simp only [hw, map_add, map_smul, hxa t, har.1 t]
  have hπ : ∀ t, π t = β • 𝔼.E t (π (t + 1)) + w t := fun t => by
    rw [hn t, hw, add_assoc]
  have hfs := 𝔼.eq_forwardSeries hβ0 hβ1 hwb hwa hπ hπb
  have hβρ : |β * ρ| < 1 := by
    rw [abs_mul, abs_of_nonneg hβ0]
    calc β * |ρ| ≤ 1 * |ρ| := mul_le_mul_of_nonneg_right hβ1.le (abs_nonneg ρ)
      _ < 1 := by rw [one_mul]; exact hρ
  have hterm : ∀ k, β ^ k * 𝔼.E t (w (t + k)) ω =
      κ * (β ^ k * 𝔼.E t (x (t + k)) ω) + (β * ρ) ^ k * u t ω := fun k => by
    simp only [hw, map_add, map_smul, 𝔼.ar1_iterate har t k, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  have hs1 : Summable (fun k => β ^ k * 𝔼.E t (x (t + k)) ω) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right B)
      (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hB (t + k)) t ω) (pow_nonneg hβ0 k)
  have hs2 : Summable (fun k => (β * ρ) ^ k * u t ω) :=
    (summable_geometric_of_abs_lt_one hβρ).mul_right _
  rw [hfs]
  change ∑' k, β ^ k * 𝔼.E t (w (t + k)) ω = _
  rw [tsum_congr hterm, (hs1.mul_left κ).tsum_add hs2, tsum_mul_left, tsum_mul_right,
    tsum_geometric_of_abs_lt_one hβρ, hs1.tsum_eq_zero_add, pow_zero, one_mul, add_zero,
    hxa t]
  ring

/-! ### The interest-rate path with serially uncorrelated shocks (p. 138) -/

/-- Galí (2015), (7), p. 132: the dynamic IS equation in the welfare-relevant gap,
`x_t = E_t x_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − r^e_t)`. -/
def DIS (σ : ℝ) (re i π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t = 𝔼.E t (x (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (π (t + 1)) - re t)

/-- Galí (2015), p. 138: with `ρ_u = 0`, `E_t p̂_{t+1} = δ p̂_t` under commitment. -/
theorem E_pHat_rho0 {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 0 u) (t : ℕ) :
    𝔼.E t (pHat 𝔼 β κ ϑ u (t + 1)) = del β κ ϑ • pHat 𝔼 β κ ϑ u t := by
  have h := pHat_ar1 𝔼 hβ0 hβ1 hϑ hκ (by simp) hu har (t + 1)
  rw [lag_succ] at h
  rw [h, map_add, map_smul, map_smul, pHat_adapted 𝔼 hβ0 hβ1 hϑ hκ hu har.1 t, har.2 t,
    zero_smul, smul_zero, add_zero]

/-- **Galí (2015), p. 138 (with C5-1)**: with `ρ_u = 0`, the commitment allocation satisfies the
dynamic IS equation iff the nominal rate is `i_t = r^e_t − (1 − δ)(1 − σκ/ϑ) p̂_t` (the book prints
`α_x` for `ϑ`, a first-edition remnant). -/
theorem dis_iff_rate_rho0 {β κ ϑ σ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ)
    (hκ : κ ≠ 0) (hσ : 0 < σ) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 0 u)
    (re i : ℕ → Ω → ℝ) :
    DIS 𝔼 σ re i (inflC 𝔼 β κ ϑ u) (gapC 𝔼 β κ ϑ u) ↔
      ∀ t, i t = re t - ((1 - del β κ ϑ) * (1 - σ * κ / ϑ)) • pHat 𝔼 β κ ϑ u t := by
  have hEp := E_pHat_rho0 𝔼 hβ0 hβ1 hϑ hκ hu har
  have hpa := pHat_adapted 𝔼 hβ0 hβ1 hϑ hκ hu har.1
  have hEx : ∀ t, 𝔼.E t (gapC 𝔼 β κ ϑ u (t + 1)) =
      (-(κ / ϑ) * del β κ ϑ) • pHat 𝔼 β κ ϑ u t := fun t => by
    change 𝔼.E t ((-(κ / ϑ)) • pHat 𝔼 β κ ϑ u (t + 1)) = _
    rw [map_smul, hEp, smul_smul]
  have hEπ : ∀ t, 𝔼.E t (inflC 𝔼 β κ ϑ u (t + 1)) =
      (del β κ ϑ - 1) • pHat 𝔼 β κ ϑ u t := fun t => by
    change 𝔼.E t (pHat 𝔼 β κ ϑ u (t + 1) - pHat 𝔼 β κ ϑ u t) = _
    rw [map_sub, hEp, hpa t, sub_smul, one_smul]
  constructor
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    rw [hEx, hEπ] at e
    simp only [gapC, gapOf, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    field_simp at e ⊢
    linear_combination e
  · intro h t
    funext ω
    rw [hEx, hEπ, h t]
    simp only [gapC, gapOf, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

/-- **Galí (2015), p. 138**: with `ρ_u = 0`, `p̂_t = ∑_{k=0}^{t} δ^{k+1} u_{t−k}`, so the
commitment nominal rate is `i_t = r^e_t − (1 − δ)(1 − σκ/ϑ) ∑_{k=0}^{t} δ^{k+1} u_{t−k}`. -/
theorem pHat_rho0_sum {β κ ϑ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hκ : κ ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (har : 𝔼.IsAR1 0 u) (t : ℕ) :
    pHat 𝔼 β κ ϑ u t = ∑ k ∈ Finset.range (t + 1), del β κ ϑ ^ (k + 1) • u (t - k) := by
  have h := pHat_ar1 𝔼 hβ0 hβ1 hϑ hκ (by simp) hu har
  simp only [mul_zero, sub_zero, div_one] at h
  induction t with
  | zero => rw [h 0]; simp
  | succ t ih =>
    rw [h (t + 1), lag_succ, ih, Finset.sum_range_succ' _ (t + 1), Finset.smul_sum]
    simp only [zero_add, pow_one, Nat.sub_zero, smul_smul, ← pow_succ']
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.add_sub_add_right]

/-! ### The implementing rule with a price-level response (p. 138, footnote 6)

The deviations of any equilibrium under the rule from the commitment allocation solve the
system of Galí (2015), Exercise 4.6 (price-level rule, natural rate zero, `p̂_{−1} = 0`). The
algebra of that exercise (characteristic polynomial, reduction to a two-dimensional forward
system, Schur stability for `φ_p > 0`) is restated from the Chapter 4 project
(`MonetaryPolicyDesign/Ex4_6.lean`); the book's footnote 6 cites "exercise 4.5", which is the
first-edition numbering (C5-2). -/

namespace Rule

/-- Galí (2015), Ex. 4.6, p. 125: the characteristic polynomial
`P(λ) = σ (λ − 1)² (1 − βλ) − κ λ (1 + φ_p − λ)` of the equilibrium dynamics. -/
def charPoly (σ κ β φ r : ℝ) : ℝ := σ * (r - 1) ^ 2 * (1 - β * r) - κ * r * (1 + φ - r)

/-- Galí (2015), Ex. 4.6: the loading `c(λ) = −(1 − λ)(1 − βλ)/κ` of the output gap on the
lagged price level in the `λ`-mode. -/
noncomputable def loadY (κ β r : ℝ) : ℝ := -((1 - r) * (1 - β * r)) / κ

/-- Galí (2015), Ex. 4.6: the coefficient `e(λ) = σ c(λ) − φ_p − 1 + λ` of the reduced IS
equation. -/
noncomputable def eCoef (σ κ β φ r : ℝ) : ℝ := σ * loadY κ β r - φ - 1 + r

/-- Galí (2015), Ex. 4.6: the coefficient `1 + β − βλ` of the reduced Phillips curve. -/
def mCoef (β r : ℝ) : ℝ := 1 + β - β * r

/-- Galí (2015), Ex. 4.6: the forward matrix `A(λ)` of the reduced system
`(w_t, v_t) = A(λ) E_t (w_{t+1}, v_{t+1})`. -/
noncomputable def fwdA (σ κ β φ r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![r / σ * (σ * β + κ), r / σ * (κ * σ);
    r / σ * (eCoef σ κ β φ r * β + mCoef β r), r / σ * (mCoef β r * σ)]

/-- Galí (2015), Ex. 4.6: `κ c(λ) = −(1 − λ)(1 − βλ)`. -/
theorem loadY_mul {κ : ℝ} (hκ : κ ≠ 0) (β r : ℝ) :
    κ * loadY κ β r = -((1 - r) * (1 - β * r)) := by
  unfold loadY; field_simp

/-- Galí (2015), Ex. 4.6: `P(0) = σ`. -/
theorem charPoly_zero (σ κ β φ : ℝ) : charPoly σ κ β φ 0 = σ := by
  unfold charPoly; ring

/-- Galí (2015), Ex. 4.6: `P(1) = −κ φ_p`. -/
theorem charPoly_one (σ κ β φ : ℝ) : charPoly σ κ β φ 1 = -(κ * φ) := by
  unfold charPoly; ring

/-- Galí (2015), Ex. 4.6: `P(−1) = 4σ(1 + β) + κ(2 + φ_p)`. -/
theorem charPoly_neg_one (σ κ β φ : ℝ) :
    charPoly σ κ β φ (-1) = 4 * σ * (1 + β) + κ * (2 + φ) := by
  unfold charPoly; ring

/-- Galí (2015), Ex. 4.6: `P` is continuous. -/
theorem continuous_charPoly (σ κ β φ : ℝ) : Continuous (charPoly σ κ β φ) := by
  unfold charPoly; fun_prop

/-- Galí (2015), Ex. 4.6: at a root `λ` of `P`, `σ c(λ)(1 − λ) + λ (1 + φ_p − λ) = 0`, the
coefficient of `p̂_{t−1}` in the reduced IS equation. -/
theorem is_coef_zero {σ κ β φ r : ℝ} (hκ : κ ≠ 0) (hP : charPoly σ κ β φ r = 0) :
    σ * loadY κ β r * (1 - r) + r * (1 + φ - r) = 0 := by
  have h := loadY_mul hκ β r
  apply mul_left_cancel₀ hκ
  unfold charPoly at hP
  linear_combination σ * (1 - r) * h - hP

/-- Galí (2015), Ex. 4.6: at a root `λ` of `P`, `λ (σ (1 + β − βλ) − κ e(λ)) = σ`; the
determinant of the reduced system's left-hand matrix is `σ/λ`. -/
theorem delta_eq {σ κ β φ r : ℝ} (hκ : κ ≠ 0) (hP : charPoly σ κ β φ r = 0) :
    r * (σ * mCoef β r - κ * eCoef σ κ β φ r) = σ := by
  have h := loadY_mul hκ β r
  unfold eCoef mCoef
  unfold charPoly at hP
  linear_combination (-(r * σ)) * h - hP

/-! ### The reduction, pointwise -/

/-- Galí (2015), Ex. 4.6 (pointwise algebra): the Phillips curve
`(1 + β) p̂_t − p̂_{t−1} = β E_t p̂_{t+1} + κ ỹ_t` holds iff
`(1 + β − βλ) w_t − κ v_t = β E_t w_{t+1}`, for any `λ`. -/
theorem pc_iff {κ β r : ℝ} (hκ : κ ≠ 0) (k p y Ep : ℝ) :
    (1 + β) * p - k = β * Ep + κ * y ↔
      mCoef β r * (p - r * k) - κ * (y - loadY κ β r * k) = β * (Ep - r * p) := by
  have h := loadY_mul hκ β r
  unfold mCoef
  constructor <;> intro e
  · linear_combination e + k * h
  · linear_combination e - k * h

/-- Galí (2015), Ex. 4.6 (pointwise algebra): at a root `λ` of `P`, the IS equation
`σ ỹ_t = σ E_t ỹ_{t+1} − ((φ_p + 1) p̂_t − E_t p̂_{t+1})` holds iff
`σ v_t = σ E_t v_{t+1} + e(λ) w_t + E_t w_{t+1}`. -/
theorem is_iff {σ κ β φ r : ℝ} (hκ : κ ≠ 0) (hP : charPoly σ κ β φ r = 0) (k p y Ep Ey : ℝ) :
    σ * y = σ * Ey - ((φ + 1) * p - Ep) ↔
      σ * (y - loadY κ β r * k) =
        σ * (Ey - loadY κ β r * p) + eCoef σ κ β φ r * (p - r * k) + (Ep - r * p) := by
  have h := is_coef_zero hκ hP
  unfold eCoef
  constructor <;> intro e
  · linear_combination e - k * h
  · linear_combination e + k * h

/-- Galí (2015), Ex. 4.6 (pointwise algebra): the reduced Phillips curve and IS equation give
the forward form `(w, v) = A(λ) (E w', E v')`. -/
theorem fwd_of {σ κ β φ r : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hP : charPoly σ κ β φ r = 0)
    {w v Ew Ev : ℝ} (h1 : mCoef β r * w - κ * v = β * Ew)
    (h2 : σ * v = σ * Ev + eCoef σ κ β φ r * w + Ew) :
    w = r / σ * (σ * β + κ) * Ew + r / σ * (κ * σ) * Ev ∧
      v = r / σ * (eCoef σ κ β φ r * β + mCoef β r) * Ew + r / σ * (mCoef β r * σ) * Ev := by
  have hΔ := delta_eq hκ hP
  constructor
  · field_simp
    linear_combination r * (σ * h1 + κ * h2) - w * hΔ
  · field_simp
    linear_combination r * (mCoef β r * h2 + eCoef σ κ β φ r * h1) - v * hΔ

/-! ### The forward matrix: determinant, trace and Schur stability -/

/-- Galí (2015), Ex. 4.6: at a root `λ` of `P`, `det A(λ) = βλ`. -/
theorem det2_fwdA {σ κ β φ r : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hP : charPoly σ κ β φ r = 0) :
    det2 (fwdA σ κ β φ r) = β * r := by
  have hΔ := delta_eq hκ hP
  have hr : r ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hΔ
    exact hσ hΔ.symm
  have hm : σ * mCoef β r - κ * eCoef σ κ β φ r = σ / r := by
    rw [eq_div_iff hr]; linarith
  calc det2 (fwdA σ κ β φ r)
      = (r / σ) ^ 2 * σ * β * (σ * mCoef β r - κ * eCoef σ κ β φ r) := by
        simp only [det2, fwdA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one]
        ring
    _ = β * r := by rw [hm]; field_simp

/-- Galí (2015), Ex. 4.6: `tr A(λ) = λ (σβ + κ + σ(1 + β − βλ))/σ`. -/
theorem tr2_fwdA (σ κ β φ r : ℝ) :
    tr2 (fwdA σ κ β φ r) = r / σ * (σ * β + κ) + r / σ * (mCoef β r * σ) := by
  simp only [tr2, fwdA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]

/-- Galí (2015), Ex. 4.6: at a root `λ` of `P`, `σ (1 − λ)(1 − tr A + det A) = κ φ_p λ`. -/
theorem key_one {σ κ β φ r : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hP : charPoly σ κ β φ r = 0) :
    σ * (1 - r) * (1 - tr2 (fwdA σ κ β φ r) + det2 (fwdA σ κ β φ r)) = κ * φ * r := by
  rw [det2_fwdA hσ hκ hP, tr2_fwdA]
  unfold mCoef
  unfold charPoly at hP
  field_simp
  linear_combination hP

/-- Galí (2015), Ex. 4.6: at a root `λ` of `P`, `σ (1 + λ)(1 + tr A + det A) = λ P(−1)`. -/
theorem key_neg_one {σ κ β φ r : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hP : charPoly σ κ β φ r = 0) :
    σ * (1 + r) * (1 + tr2 (fwdA σ κ β φ r) + det2 (fwdA σ κ β φ r)) =
      r * charPoly σ κ β φ (-1) := by
  rw [det2_fwdA hσ hκ hP, tr2_fwdA]
  unfold mCoef
  have hP' := hP
  unfold charPoly at hP' ⊢
  field_simp
  linear_combination hP'

/-- Galí (2015), Ex. 4.6: if `λ` is a root of `P` with `|λ| < 1`, `φ_p λ > 0` and
`λ P(−1) > 0`, the forward matrix `A(λ)` is Schur stable (both eigenvalues inside the unit
circle). -/
theorem schur_fwdA {σ κ β φ r : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hP : charPoly σ κ β φ r = 0) (hr : |r| < 1) (h1 : 0 < φ * r)
    (h2 : 0 < r * charPoly σ κ β φ (-1)) :
    SchurStable (tr2 (fwdA σ κ β φ r)) (det2 (fwdA σ κ β φ r)) := by
  have k1 := key_one hσ.ne' hκ.ne' hP
  have k2 := key_neg_one hσ.ne' hκ.ne' hP
  rw [det2_fwdA hσ.ne' hκ.ne' hP] at k1 k2 ⊢
  obtain ⟨hr0, hr1⟩ := abs_lt.1 hr
  have hpos1 : 0 < σ * (1 - r) := mul_pos hσ (by linarith)
  have hpos2 : 0 < σ * (1 + r) := mul_pos hσ (by linarith)
  have e1 : 0 < 1 - tr2 (fwdA σ κ β φ r) + β * r := by
    have : 0 < σ * (1 - r) * (1 - tr2 (fwdA σ κ β φ r) + β * r) := by
      rw [k1]; nlinarith
    exact pos_of_mul_pos_right this hpos1.le
  have e2 : 0 < 1 + tr2 (fwdA σ κ β φ r) + β * r := by
    have : 0 < σ * (1 + r) * (1 + tr2 (fwdA σ κ β φ r) + β * r) := by rw [k2]; exact h2
    exact pos_of_mul_pos_right this hpos2.le
  refine ⟨?_, abs_lt.2 ⟨by linarith, by linarith⟩⟩
  rw [abs_mul, abs_of_pos hβ0]
  nlinarith [abs_nonneg r]


/-- Galí (2015), Ex. 4.6: for `φ_p > 0` the polynomial has a root in `(0, 1)` (`P(0) = σ > 0`,
`P(1) = −κφ_p < 0`). -/
theorem exists_root_pos {σ κ β φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hφ : 0 < φ) :
    ∃ r, 0 < r ∧ r < 1 ∧ charPoly σ κ β φ r = 0 := by
  have h := intermediate_value_Ioo' (zero_le_one' ℝ)
    (continuous_charPoly σ κ β φ).continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (charPoly σ κ β φ 1) (charPoly σ κ β φ 0) by
      rw [charPoly_one, charPoly_zero]; exact ⟨by nlinarith, hσ⟩)
  obtain ⟨r, ⟨h0, h1⟩, hr⟩ := h
  exact ⟨r, h0, h1, hr⟩

/-- Galí (2015), p. 138: the stacked vector `(a_t, b_t)`. -/
def stack (a b : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![a t, b t]

/-- **Galí (2015), p. 138 and Ex. 4.6 (uniqueness of the zero deviation)**: for `φ_p > 0`, the
only bounded adapted solution of the deviation system
`σ y_t = σ E_t y_{t+1} − ((φ_p + 1) q_t − E_t q_{t+1})`,
`(1 + β) q_t − q_{t−1} = β E_t q_{t+1} + κ y_t`, `q_{−1} = 0`, is zero. -/
theorem dev_zero {β σ κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφ : 0 < φ) {y q : ℕ → Ω → ℝ} (hya : 𝔼.Adapted y) (hqa : 𝔼.Adapted q)
    (hyb : BoundedProc y) (hqb : BoundedProc q)
    (he : ∀ t ω, σ * y t ω = σ * 𝔼.E t (y (t + 1)) ω - ((φ + 1) * q t ω - 𝔼.E t (q (t + 1)) ω) ∧
      (1 + β) * q t ω - lag q t ω = β * 𝔼.E t (q (t + 1)) ω + κ * y t ω) :
    y = 0 ∧ q = 0 := by
  obtain ⟨r, hr0, hr1, hP⟩ := exists_root_pos (β := β) hσ hκ hφ
  have hP1 : 0 < charPoly σ κ β φ (-1) := by rw [charPoly_neg_one]; positivity
  have hr : |r| < 1 := abs_lt.2 ⟨by linarith, hr1⟩
  have hA := schur_fwdA hσ hκ hβ0 hβ1 hP hr (mul_pos hφ hr0) (mul_pos hr0 hP1)
  have hla := lag_adapted 𝔼 hqa
  set X : ℕ → Fin 2 → Ω → ℝ :=
    stack (fun t => q t - r • lag q t) (fun t => y t - loadY κ β r • lag q t) with hX
  have hs : 𝔼.Solves (fwdA σ κ β φ r) 0 X := by
    intro t j
    funext ω
    obtain ⟨e1, e2⟩ := he t ω
    have h1 := (pc_iff (r := r) hκ.ne' _ _ _ _).1 e2
    have h2 := (is_iff (k := lag q t ω) hκ.ne' hP _ _ _ _).1 e1
    have hfw := fwd_of hσ.ne' hκ.ne' hP h1 h2
    have hEw : 𝔼.E t (q (t + 1) - r • q t) ω = 𝔼.E t (q (t + 1)) ω - r * q t ω := by
      rw [map_sub, map_smul, hqa t]; rfl
    have hEv : 𝔼.E t (y (t + 1) - loadY κ β r • q t) ω =
        𝔼.E t (y (t + 1)) ω - loadY κ β r * q t ω := by
      rw [map_sub, map_smul, hqa t]; rfl
    fin_cases j
    · simp only [hX, stack, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, lag_succ]
      rw [hEw, hEv]
      simp only [fwdA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact hfw.1
    · simp only [hX, stack, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
        Pi.zero_apply, add_zero, lag_succ]
      rw [hEw, hEv]
      simp only [fwdA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact hfw.2
  have hav : 𝔼.AdaptedVec X := by
    intro t j
    fin_cases j
    · change 𝔼.E t (q t - r • lag q t) = q t - r • lag q t
      rw [map_sub, map_smul, hqa t, hla t]
    · change 𝔼.E t (y t - loadY κ β r • lag q t) = y t - loadY κ β r • lag q t
      rw [map_sub, map_smul, hya t, hla t]
  obtain ⟨My, hMy⟩ := hyb
  obtain ⟨Mq, hMq⟩ := hqb
  have hbv : BoundedVec X := by
    refine ⟨Mq + |r| * Mq + My + |loadY κ β r| * Mq, fun t j ω => ?_⟩
    have hMq0 : 0 ≤ Mq := (abs_nonneg _).trans (hMq 0 ω)
    have hlb : |lag q t ω| ≤ Mq := by
      cases t with
      | zero => simpa using hMq0
      | succ t => exact hMq t ω
    have h1 := abs_nonneg (q t ω)
    have h2 := abs_nonneg (y t ω)
    have h3 : |r * lag q t ω| ≤ |r| * Mq := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hlb (abs_nonneg r)
    have h4 : |loadY κ β r * lag q t ω| ≤ |loadY κ β r| * Mq := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hlb (abs_nonneg _)
    have h5 := abs_nonneg (r * lag q t ω)
    have h6 := abs_nonneg (loadY κ β r * lag q t ω)
    fin_cases j
    · change |q t ω - r * lag q t ω| ≤ _
      linarith [abs_sub (q t ω) (r * lag q t ω), hMq t ω, hMy t ω]
    · change |y t ω - loadY κ β r * lag q t ω| ≤ _
      linarith [abs_sub (y t ω) (loadY κ β r * lag q t ω), hMq t ω, hMy t ω]
  have h0 : 𝔼.Solves (fwdA σ κ β φ r) 0 0 := fun t j => by simp
  have heq := 𝔼.system_unique hA hs h0 hav (fun t j => map_zero _) hbv ⟨0, fun t j ω => by simp⟩
  have hw : ∀ t, q t = r • lag q t := fun t => by
    have := congrFun (congrFun heq t) 0
    simp only [hX, stack, Matrix.cons_val_zero, Pi.zero_apply] at this
    exact sub_eq_zero.1 this
  have hv : ∀ t, y t = loadY κ β r • lag q t := fun t => by
    have := congrFun (congrFun heq t) 1
    simp only [hX, stack, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.zero_apply] at this
    exact sub_eq_zero.1 this
  have hq0 : ∀ t, q t = 0 := by
    intro t
    induction t with
    | zero => rw [hw 0]; simp
    | succ t ih => rw [hw (t + 1), lag_succ, ih, smul_zero]
  refine ⟨funext fun t => ?_, funext hq0⟩
  rw [hv t]
  cases t with
  | zero => simp
  | succ t => rw [lag_succ, hq0 t, smul_zero]; rfl

end Rule

/-- Galí (2015), p. 138 (with C5-1): the implementing rule
`i_t = r^e_t − (φ_p + (1 − δ)(1 − σκ/ϑ)) ∑_{k=0}^{t} δ^{k+1} u_{t−k} + φ_p p̂_t`. -/
noncomputable def ruleRate (β κ ϑ σ φ : ℝ) (re u p : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  re t - (φ + (1 - del β κ ϑ) * (1 - σ * κ / ϑ)) •
    ∑ k ∈ Finset.range (t + 1), del β κ ϑ ^ (k + 1) • u (t - k) + φ • p t

/-- Galí (2015), p. 138: an equilibrium under the implementing rule, given `p̂_{−1} = 0`: the
dynamic IS equation (7), the Phillips curve (2) with `π_t = p̂_t − p̂_{t−1}`, and the rule. -/
def RuleEq (β κ ϑ σ φ : ℝ) (re u x p i : ℕ → Ω → ℝ) : Prop :=
  DIS 𝔼 σ re i (inflOf p) x ∧ NKPC 𝔼 β κ u (inflOf p) x ∧ ∀ t, i t = ruleRate β κ ϑ σ φ re u p t

/-- Galí (2015), (7), p. 132 (pointwise algebra): `x = E x' − σ⁻¹ (i − E π' − r)` iff
`σ x = σ E x' − (i − E π' − r)`. -/
theorem dis_pointwise {σ : ℝ} (hσ : σ ≠ 0) (X EX I EP R : ℝ) :
    X = EX - σ⁻¹ * (I - EP - R) ↔ σ * X = σ * EX - (I - EP - R) := by
  constructor <;> intro h
  · rw [h]; field_simp
  · field_simp; linarith

/-- **Galí (2015), p. 138 (the implementing rule)**: with `ρ_u = 0` and any `φ_p > 0`, the rule
`i_t = r^e_t − (φ_p + (1 − δ)(1 − σκ/ϑ)) ∑_{k=0}^{t} δ^{k+1} u_{t−k} + φ_p p̂_t` (with `ϑ` in
place of the book's `α_x`, C5-1) supports the commitment allocation as an equilibrium, along which
`i_t = r^e_t − (1 − δ)(1 − σκ/ϑ) p̂_t`, and it is the unique bounded adapted equilibrium. -/
theorem rule_implements {β κ ϑ σ φ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ)
    (hκ : 0 < κ) (hσ : 0 < σ) (hφ : 0 < φ) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M)
    (har : 𝔼.IsAR1 0 u) (re : ℕ → Ω → ℝ) :
    (RuleEq 𝔼 β κ ϑ σ φ re u (gapC 𝔼 β κ ϑ u) (pHat 𝔼 β κ ϑ u)
        (ruleRate β κ ϑ σ φ re u (pHat 𝔼 β κ ϑ u)) ∧
      ∀ t, ruleRate β κ ϑ σ φ re u (pHat 𝔼 β κ ϑ u) t =
        re t - ((1 - del β κ ϑ) * (1 - σ * κ / ϑ)) • pHat 𝔼 β κ ϑ u t) ∧
    ∀ x p i, RuleEq 𝔼 β κ ϑ σ φ re u x p i → 𝔼.Adapted x → 𝔼.Adapted p → BoundedProc x →
      BoundedProc p →
        x = gapC 𝔼 β κ ϑ u ∧ p = pHat 𝔼 β κ ϑ u ∧
          i = ruleRate β κ ϑ σ φ re u (pHat 𝔼 β κ ϑ u) := by
  have hκ' := hκ.ne'
  have hrate : ∀ t, ruleRate β κ ϑ σ φ re u (pHat 𝔼 β κ ϑ u) t =
      re t - ((1 - del β κ ϑ) * (1 - σ * κ / ϑ)) • pHat 𝔼 β κ ϑ u t := fun t => by
    rw [ruleRate, ← pHat_rho0_sum 𝔼 hβ0 hβ1 hϑ hκ' hu har t, add_smul]
    abel
  have hdis := (dis_iff_rate_rho0 𝔼 hβ0 hβ1 hϑ hκ' hσ hu har re
    (ruleRate β κ ϑ σ φ re u (pHat 𝔼 β κ ϑ u))).2 hrate
  have hnk := cand_nkpc 𝔼 hβ0 hβ1 hϑ hκ' hu har.1
  have hpa := pHat_adapted 𝔼 hβ0 hβ1 hϑ hκ' hu har.1
  obtain ⟨-, hga, -, hgb⟩ := cand_adapted_bounded 𝔼 hβ0 hβ1 hϑ hκ' hu har.1
  refine ⟨⟨⟨hdis, hnk, fun t => rfl⟩, hrate⟩, fun x p i he hxa hpa' hxb hpb => ?_⟩
  obtain ⟨hd, hn, hi⟩ := he
  have hEi : ∀ (q : ℕ → Ω → ℝ), 𝔼.Adapted q → ∀ t,
      𝔼.E t (inflOf q (t + 1)) = 𝔼.E t (q (t + 1)) - q t := fun q hq t => by
    change 𝔼.E t (q (t + 1) - q t) = _
    rw [map_sub, hq t]
  have hlagsub : ∀ t ω, lag (fun s => p s - pHat 𝔼 β κ ϑ u s) t ω =
      lag p t ω - lag (pHat 𝔼 β κ ϑ u) t ω := fun t ω => by
    cases t <;> simp
  obtain ⟨Bx, hBx⟩ := hxb
  obtain ⟨Bg, hBg⟩ := hgb
  obtain ⟨Bp, hBp⟩ := hpb
  obtain ⟨Bs, hBs⟩ := pHat_bounded 𝔼 hβ0 hβ1 hϑ hκ' hu
  have hdev := Rule.dev_zero 𝔼 (y := fun t => x t - gapC 𝔼 β κ ϑ u t)
    (q := fun t => p t - pHat 𝔼 β κ ϑ u t) hσ hκ hβ0 hβ1 hφ
    (fun t => by simp only [map_sub, hxa t, hga t])
    (fun t => by simp only [map_sub, hpa' t, hpa t])
    ⟨Bx + Bg, fun t ω => (abs_sub _ _).trans (add_le_add (hBx t ω) (hBg t ω))⟩
    ⟨Bp + Bs, fun t ω => (abs_sub _ _).trans (add_le_add (hBp t ω) (hBs t ω))⟩
    (fun t ω => ?_)
  · obtain ⟨hx0, hp0⟩ := hdev
    have hx : x = gapC 𝔼 β κ ϑ u := funext fun t => sub_eq_zero.1 (congrFun hx0 t)
    have hp : p = pHat 𝔼 β κ ϑ u := funext fun t => sub_eq_zero.1 (congrFun hp0 t)
    refine ⟨hx, hp, funext fun t => ?_⟩
    rw [hi t, hp]
  · have e1 := congrFun (hd t) ω
    have e1s := congrFun (hdis t) ω
    have e2 := congrFun (hn t) ω
    have e2s := congrFun (hnk t) ω
    have e3 := congrFun (hi t) ω
    rw [hEi p hpa' t] at e1 e2
    simp only [inflC] at e1s e2s
    rw [hEi _ hpa t] at e1s e2s
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, inflOf] at e1 e1s e2 e2s
    rw [dis_pointwise hσ.ne'] at e1 e1s
    simp only [map_sub, Pi.sub_apply, hlagsub, ruleRate, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at e3 e1s ⊢
    constructor
    · linear_combination e1 - e1s - e3
    · linear_combination e2 - e2s

end Gali.DiscretionCommitment.Commitment
