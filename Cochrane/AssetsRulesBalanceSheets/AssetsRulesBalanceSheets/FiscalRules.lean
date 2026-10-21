/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.InflationTarget

/-!
# Fiscal rules with indexed debt

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.3.1–§9.3.3,
eqs. (9.7)–(9.14), pp. 265–269.

## Dating convention

Lean date `t` carries the real (indexed) debt `b t` outstanding at the start of date `t`, the
book's `b_{t−1}`. The flow condition (9.8) reads `b t = s t + β b (t + 1)`.

## Main results

* §9.3.1: `PresentValue.price_unique_of_strictMonoOn`, `existsUnique_price`: `b_{T−1} = s(P_T)`
  with `s`
  strictly increasing determines `P_T`; `eq_9_7_iff`: under (9.7) the price level is `P*_T`.
* §9.3.2: `PresentValue.real_iterate`, `PresentValue.hasSum_of_tvc`, `eq_9_9`: (9.8) iterated
  forward with the
  transversality condition gives (9.9) ex post; `hyperplane_equilibrium`,
  `not_determined_by_valuation`: (9.9) determines only the `β`-weighted sum of price levels;
  `price_eq_target_of_debtRule`, `money_pos_of_below`: the debt rule (9.11) gives `P = P*`, and
  `P < P*` means money is printed (9.10).
* **Theorem FR** for the interest-rate target (9.12):
  (a) `fr_perfectForesight`: under perfect foresight only `P = P*` satisfies (9.9) and (9.12);
  (b) `Sunspot.sunspot_counterexample`: under uncertainty the claim is **false** (error E9.9):
  an explicit infinite "settle-or-continue" event tree, for every `0 < β < 1` and every
  `0 < P_0 < 1 = P*_0`, satisfies (9.12) at every node, (9.8) on every edge with predetermined
  real debt, (9.9) at every node (genuine infinite sums of explicit conditional expectations),
  and the transversality condition;
  (c) `fr_jensen`: what survives under uncertainty is the one-sided bound `P_0 ≤ P*_0`;
  (d) `fr_unique_bounded` (via `unique_of_ratio_tvc`): uniqueness is restored under uncertainty if
  the price level is bounded above, or bounded away from zero — `Z_t = S_t/P_t` obeys
  `E_t Z_{t+1} = (Z_t − 1)/β`, so `Z_t − 1/(1 − β) = βᵏ E_t(Z_{t+k} − 1/(1 − β)) → 0`. The sunspot
  tree's prices are unbounded above and tend to zero (`settlePrice_unbounded`,
  `contPrice_tendsto_zero`).
* §9.3.3: `regular_solve`, `regular_tvc`, `regular_hasSum`: with `α_r > 0` the regular budget
  repays itself (the book's claim, checked correct, survey E9.6); `emergency_hasSum` (9.14);
  `total_hasSum`; the lagged-rule variant `lagged_tvc`, `lagged_tvc_iff`, `lagged_hasSum` needs
  `0 < α_r < 2`.
-/

namespace Cochrane.AssetsRulesBalanceSheets.FiscalRules

open Filter Topology PresentValue

/-! ### §9.3.1 Indexed debt in a one-period model -/

/-- Cochrane (2023), §9.3.1, p. 265: "this condition can determine the price level `P_T`,
although the debt is fully indexed" — with `s` strictly increasing and `b` in its range, there is
exactly one positive price level. -/
theorem existsUnique_price {s : ℝ → ℝ} (hs : StrictMonoOn s (Set.Ioi 0)) {b : ℝ}
    (hb : ∃ P, 0 < P ∧ b = s P) : ∃! P, 0 < P ∧ b = s P := by
  obtain ⟨P, hP, hbP⟩ := hb
  exact ⟨P, ⟨hP, hbP⟩, fun P' h' => price_unique_of_strictMonoOn hs h'.1 hP h'.2 hbP⟩

/-- Cochrane (2023), eq. (9.7), p. 265: with the rule `s_T(P_T) = b_{T−1} + θ (P_T − P*_T)`,
`θ ≠ 0`, the valuation `b_{T−1} = s_T(P_T)` holds if and only if `P_T = P*_T`. -/
theorem eq_9_7_iff {θ : ℝ} (hθ : θ ≠ 0) (b Pstar P : ℝ) :
    b = b + θ * (P - Pstar) ↔ P = Pstar := by
  constructor
  · intro h
    have h' : θ * (P - Pstar) = 0 := by linarith
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact absurd h0 hθ
    · linarith
  · intro h
    rw [h]
    ring

/-! ### §9.3.2 A dynamic fiscal rule with indexed debt (ex post, along a path) -/

/-- Cochrane (2023), eq. (9.9), p. 266: with the surplus rule `s_t = s_{0,t} + θ (P_t − P*_t)`,
(9.8) and the transversality condition give
`b_{t−1} = ∑ⱼ βʲ s_{0,t+j} + θ ∑ⱼ βʲ (P_{t+j} − P*_{t+j})` (ex post). -/
theorem eq_9_9 {β θ : ℝ} {b s0 P Pstar : ℕ → ℝ}
    (h : ∀ t, b t = (s0 t + θ * (P t - Pstar t)) + β * b (t + 1)) (t : ℕ)
    (htvc : Tendsto (fun T => β ^ T * b (t + T)) atTop (𝓝 0))
    (hs0 : Summable (fun j => β ^ j * s0 (t + j)))
    (hP : Summable (fun j => β ^ j * (P (t + j) - Pstar (t + j)))) :
    b t = ∑' j, β ^ j * s0 (t + j) + θ * ∑' j, β ^ j * (P (t + j) - Pstar (t + j)) := by
  have hsum : Summable (fun j => β ^ j * (s0 (t + j) + θ * (P (t + j) - Pstar (t + j)))) := by
    have := hs0.add (hP.mul_left θ)
    refine this.congr fun j => ?_
    ring
  have hh := hasSum_of_tvc (s := fun t => s0 t + θ * (P t - Pstar t)) h t htvc hsum
  rw [← hh.tsum_eq, ← tsum_mul_left, ← hs0.tsum_add (hP.mul_left θ)]
  refine tsum_congr fun j => ?_
  ring

/-- Cochrane (2023), §9.3.2, pp. 266–267: an equilibrium path of the dynamic fiscal rule with
indexed debt (ex post, along one path): positive prices, the flow condition (9.8) with the rule
`s_t = s_{0,t} + θ (P_t − P*_t)`, and the transversality condition at every date. -/
def RuleEquilibrium (β θ : ℝ) (s0 Pstar P b : ℕ → ℝ) : Prop :=
  (∀ t, 0 < P t) ∧ (∀ t, b t = (s0 t + θ * (P t - Pstar t)) + β * b (t + 1)) ∧
    ∀ t, Tendsto (fun T => β ^ T * b (t + T)) atTop (𝓝 0)

/-- Cochrane (2023), §9.3.2, p. 266: the discounted sum `Z_t = ∑ⱼ βʲ z_{t+j}` of a bounded
sequence obeys `Z_t = z_t + β Z_{t+1}`. -/
theorem tsum_shift {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {z : ℕ → ℝ} (hz : ∀ j, |z j| ≤ M)
    (t : ℕ) : ∑' j, β ^ j * z (t + j) = z t + β * ∑' j, β ^ j * z (t + 1 + j) := by
  rw [(summable_of_bounded hβ0 hβ1 hz t).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, add_zero]
  congr 1
  refine tsum_congr fun j => ?_
  rw [show t + (j + 1) = t + 1 + j by ring, pow_succ]
  ring

/-- Cochrane (2023), §9.3.2, p. 266: the discounted sum of a sequence bounded by `M` is bounded
by `M / (1 − β)`. -/
theorem abs_tsum_le {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {z : ℕ → ℝ} (hz : ∀ j, |z j| ≤ M)
    (t : ℕ) : |∑' j, β ^ j * z (t + j)| ≤ M / (1 - β) := by
  have hg : HasSum (fun j : ℕ => M * β ^ j) (M / (1 - β)) := by
    have := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left M
    simpa [div_eq_mul_inv] using this
  have := tsum_of_norm_bounded hg (f := fun j => β ^ j * z (t + j)) fun j => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 j), mul_comm M]
    exact mul_le_mul_of_nonneg_left (hz (t + j)) (pow_nonneg hβ0 j)
  simpa [Real.norm_eq_abs] using this

/-- Cochrane (2023), §9.3.2, p. 266 ("the valuation equation and the surplus rule determine the
value of the sum `∑ βʲ P_{t+j}` but not the shape of that path"): adding to an equilibrium price
path any bounded `z` with `∑ⱼ βʲ zⱼ = 0` (keeping prices positive) gives another equilibrium with
the same initial debt; real debt changes by `θ ∑ⱼ βʲ z_{t+j}`. -/
theorem hyperplane_equilibrium {β θ M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {s0 Pstar P b z : ℕ → ℝ} (hE : RuleEquilibrium β θ s0 Pstar P b)
    (hz : HasSum (fun j => β ^ j * z j) 0) (hzM : ∀ j, |z j| ≤ M) (hpos : ∀ t, 0 < P t + z t) :
    RuleEquilibrium β θ s0 Pstar (fun t => P t + z t)
        (fun t => b t + θ * ∑' j, β ^ j * z (t + j)) ∧
      b 0 + θ * ∑' j, β ^ j * z (0 + j) = b 0 := by
  obtain ⟨_, hflow, htvc⟩ := hE
  refine ⟨⟨hpos, fun t => ?_, fun t => ?_⟩, ?_⟩
  · beta_reduce
    rw [hflow t, tsum_shift hβ0 hβ1 hzM t]
    ring
  · have hZ : Tendsto (fun T => β ^ T * ∑' j, β ^ j * z (t + T + j)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun T => β ^ T * (M / (1 - β))) (fun T => ?_) ?_
      · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 T)]
        exact mul_le_mul_of_nonneg_left (abs_tsum_le hβ0 hβ1 hzM (t + T)) (pow_nonneg hβ0 T)
      · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const (M / (1 - β))
    have := (htvc t).add (hZ.const_mul θ)
    simp only [mul_zero, add_zero] at this
    refine this.congr fun T => ?_
    ring
  · simp only [zero_add, hz.tsum_eq, mul_zero, add_zero]

/-- Cochrane (2023), §9.3.2, p. 266: the explicit deviation `z = (β/2, −1/2, 0, 0, …)`, whose
discounted sum is zero. -/
noncomputable def hyperplaneShift (β : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then β / 2 else if j = 1 then -1 / 2 else 0

/-- Cochrane (2023), §9.3.2, p. 266: `∑ⱼ βʲ zⱼ = 0` for `hyperplaneShift`. -/
theorem hasSum_hyperplaneShift (β : ℝ) : HasSum (fun j => β ^ j * hyperplaneShift β j) 0 := by
  have h : HasSum (fun j : ℕ => β ^ j * hyperplaneShift β j)
      (∑ j ∈ Finset.range 2, β ^ j * hyperplaneShift β j) :=
    hasSum_sum_of_ne_finset_zero (fun j hj => by
      simp only [Finset.mem_range, not_lt] at hj
      have h0 : j ≠ 0 := by omega
      have h1 : j ≠ 1 := by omega
      simp [hyperplaneShift, h0, h1])
  convert h using 1
  simp [Finset.sum_range_succ, hyperplaneShift]
  ring

/-- Cochrane (2023), §9.3.2, p. 266 (perfect foresight): the valuation equation (9.9) and the
surplus rule do not determine the price level. With `P* ≡ 1`, `s₀ ≡ 1 − β` and real debt
`b ≡ 1`, both `P ≡ P*` and `P = P* + (β/2, −1/2, 0, …)` are equilibria with the same initial
debt. -/
theorem not_determined_by_valuation {β θ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ P P' b b' : ℕ → ℝ, RuleEquilibrium β θ (fun _ => 1 - β) (fun _ => 1) P b ∧
      RuleEquilibrium β θ (fun _ => 1 - β) (fun _ => 1) P' b' ∧ b 0 = b' 0 ∧ P ≠ P' := by
  have hbase : RuleEquilibrium β θ (fun _ => 1 - β) (fun _ => 1) (fun _ => 1) (fun _ => 1) := by
    refine ⟨fun _ => one_pos, fun t => by ring, fun t => ?_⟩
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (1 : ℝ)
  have hzM : ∀ j, |hyperplaneShift β j| ≤ 1 := fun j => by
    unfold hyperplaneShift
    split_ifs
    · rw [abs_of_pos (by linarith)]
      linarith
    · norm_num
    · norm_num
  have hpos : ∀ t, 0 < (fun _ => (1 : ℝ)) t + hyperplaneShift β t := fun t => by
    unfold hyperplaneShift
    split_ifs <;> linarith
  obtain ⟨h1, h2⟩ := hyperplane_equilibrium hβ0.le hβ1 hbase (hasSum_hyperplaneShift β) hzM hpos
  refine ⟨_, _, _, _, hbase, h1, h2.symm, fun h => ?_⟩
  have := congrFun h 1
  simp [hyperplaneShift] at this

/-- Cochrane (2023), eqs. (9.10)–(9.11), p. 267: with the flow budget constraint including money,
`b_{t−1} = s_{0,t} + θ (P_t − P*_t) + β b_t + M_t/P_t`, the debt rule
`β b_t = b_{t−1} − s_{0,t}` and `M_t = 0` in equilibrium force `P_t = P*_t`. -/
theorem price_eq_target_of_debtRule {β θ b b' s0 P Pstar M : ℝ} (hθ : θ ≠ 0)
    (hflow : b = s0 + θ * (P - Pstar) + β * b' + M / P) (hrule : β * b' = b - s0) (hM : M = 0) :
    P = Pstar := by
  rw [hM, zero_div, add_zero, hrule] at hflow
  have h : θ * (P - Pstar) = 0 := by linarith
  rcases mul_eq_zero.mp h with h0 | h0
  · exact absurd h0 hθ
  · linarith

/-- Cochrane (2023), §9.3.2, p. 267: under the debt rule (9.11), a price level below target
`P_t < P*_t` (with `θ > 0`) must result in money creation `M_t > 0` in (9.10). -/
theorem money_pos_of_below {β θ b b' s0 P Pstar M : ℝ} (hθ : 0 < θ) (hP : 0 < P)
    (hflow : b = s0 + θ * (P - Pstar) + β * b' + M / P) (hrule : β * b' = b - s0)
    (hlow : P < Pstar) : 0 < M := by
  rw [hrule] at hflow
  have h : M / P = θ * (Pstar - P) := by linarith
  have h2 : M = θ * (Pstar - P) * P := by
    field_simp at h
    linarith
  rw [h2]
  exact mul_pos (mul_pos hθ (by linarith)) hP

/-- Cochrane (2023), §9.3.2, p. 267: symmetrically, a price level above target means money is
soaked up, `M_t < 0`. -/
theorem money_neg_of_above {β θ b b' s0 P Pstar M : ℝ} (hθ : 0 < θ) (hP : 0 < P)
    (hflow : b = s0 + θ * (P - Pstar) + β * b' + M / P) (hrule : β * b' = b - s0)
    (hhigh : Pstar < P) : M < 0 := by
  rw [hrule] at hflow
  have h : M / P = θ * (Pstar - P) := by linarith
  have h2 : M = θ * (Pstar - P) * P := by
    field_simp at h
    linarith
  rw [h2]
  exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hθ (by linarith)) hP

/-! ### Theorem FR (a): perfect foresight -/

/-- Cochrane (2023), §9.3.2, p. 267 (**Theorem FR (a)**): under perfect foresight, if the
interest rate follows the target, `β P_t/P_{t+1} = β P*_t/P*_{t+1}` ((9.12)), and the valuation
(9.9) holds at date 0 with the initial debt equal to the present value of `s₀` (the book's
`a(β) = 0` case), then `P_t = P*_t` at every date (`θ ≠ 0`, `∑ βʲ P*_j < ∞`). -/
theorem fr_perfectForesight {β θ : ℝ} (hβ0 : 0 < β) (hθ : θ ≠ 0) {P Pstar s0 : ℕ → ℝ}
    {b0 : ℝ} (hP : ∀ t, 0 < P t) (hPs : ∀ t, 0 < Pstar t)
    (h912 : ∀ t, β * (P t / P (t + 1)) = β * (Pstar t / Pstar (t + 1)))
    (h99 : HasSum (fun j => β ^ j * (s0 j + θ * (P j - Pstar j))) b0)
    (hb : HasSum (fun j => β ^ j * s0 j) b0) (hPsum : Summable (fun j => β ^ j * Pstar j)) :
    P = Pstar := by
  set c := P 0 / Pstar 0 with hc
  have hscale : ∀ t, P t = c * Pstar t := by
    intro t
    induction t with
    | zero =>
      rw [hc]
      field_simp [(hPs 0).ne']
    | succ t ih =>
      have h := mul_left_cancel₀ hβ0.ne' (h912 t)
      rw [ih] at h
      have hP1 := (hP (t + 1)).ne'
      have hPs1 := (hPs (t + 1)).ne'
      have hPt := (hPs t).ne'
      rw [div_eq_div_iff hP1 hPs1] at h
      have : Pstar t * (c * Pstar (t + 1)) = Pstar t * P (t + 1) := by linarith
      exact (mul_left_cancel₀ hPt this).symm
  have hdiff := h99.sub hb
  have hfun : (fun j => β ^ j * (s0 j + θ * (P j - Pstar j)) - β ^ j * s0 j) =
      fun j => θ * (c - 1) * (β ^ j * Pstar j) := by
    funext j
    rw [hscale j]
    ring
  rw [hfun, sub_self] at hdiff
  have h2 := hPsum.hasSum.mul_left (θ * (c - 1))
  have h0 : θ * (c - 1) * ∑' j, β ^ j * Pstar j = 0 := h2.unique hdiff
  have hpos : 0 < ∑' j, β ^ j * Pstar j :=
    hPsum.tsum_pos (fun j => (mul_pos (pow_pos hβ0 j) (hPs j)).le) 0 (by simpa using hPs 0)
  have hc1 : c = 1 := by
    rcases mul_eq_zero.mp h0 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hθ
      · linarith
    · linarith
  funext t
  rw [hscale t, hc1, one_mul]

/-- Cochrane (2023), §9.3.2, p. 267 (existence for Theorem FR (a)): under perfect foresight with
bounded `s₀`, the price path `P = P*` with real debt `b_t = ∑ⱼ βʲ s_{0,t+j}` is an equilibrium of
the
fiscal rule. -/
theorem fr_exists {β θ M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s0 Pstar : ℕ → ℝ}
    (hPs : ∀ t, 0 < Pstar t) (hM : ∀ t, |s0 t| ≤ M) :
    RuleEquilibrium β θ s0 Pstar Pstar (fun t => ∑' j, β ^ j * s0 (t + j)) := by
  refine ⟨hPs, fun t => ?_, fun t => ?_⟩
  · beta_reduce
    rw [tsum_shift hβ0 hβ1 hM t]
    ring
  · refine squeeze_zero_norm (a := fun T => β ^ T * (M / (1 - β))) (fun T => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 T)]
      exact mul_le_mul_of_nonneg_left (abs_tsum_le hβ0 hβ1 hM (t + T)) (pow_nonneg hβ0 T)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const (M / (1 - β))

/-- Cochrane (2023), §9.3.2, p. 266 ("with `s_{0,t} = a(L)ε_{s,t}` and `a(β) = 0` … as there are no
innovations to the first term of (9.9), there are no innovations to the second term as well"): if
real debt `b_{t−1}` and the first term `X` are known at `t − 1` and `b_{t−1} = X + θ Y` with `θ ≠
0`, then
the weighted sum of price deviations `Y` is known at `t − 1` (has no innovation at `t`) — only the
weighted sum, not each price level. -/
theorem no_innovation_weighted_sum {Ω : Type*} (𝔼 : ExpectationSystem Ω) {θ : ℝ} (hθ : θ ≠ 0)
    {s : ℕ} {b X Y : Ω → ℝ} (hb : 𝔼.E s b = b) (hX : 𝔼.E s X = X) (h : b = X + θ • Y) :
    𝔼.E s Y = Y := by
  have hY : Y = θ⁻¹ • (b - X) := by
    rw [h, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hθ, one_smul]
  rw [hY, map_smul, map_sub, hb, hX]

/-! ### Theorem FR (c): the Jensen bound under uncertainty -/

/-- Cochrane (2023), §9.3.2, p. 267 (supporting line for Theorem FR (c)): for `y, m > 0`,
`2/m − y/m² ≤ 1/y`. -/
theorem inv_ge_tangent {y m : ℝ} (hy : 0 < y) (hm : 0 < m) : 2 / m - y / m ^ 2 ≤ 1 / y := by
  have key : 0 ≤ m * (y - m) ^ 2 := mul_nonneg hm.le (sq_nonneg _)
  rw [div_sub_div _ _ hm.ne' (pow_ne_zero 2 hm.ne'), div_le_div_iff₀ (by positivity) hy]
  nlinarith [key]

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §9.3.2, p. 267 (Jensen's inequality used in Theorem FR (c)): under `PullOut`,
`1/E_t y ≤ E_t (1/y)` for positive `y` with positive conditional mean. -/
theorem jensen_inv (h𝔼 : 𝔼.PullOut) {t : ℕ} {y : Ω → ℝ} (hy : ∀ ω, 0 < y ω)
    (hm : ∀ ω, 0 < 𝔼.E t y ω) (ω : Ω) : 1 / 𝔼.E t y ω ≤ 𝔼.E t (fun ω => 1 / y ω) ω := by
  set m := 𝔼.E t y with hm_def
  have hmk : 𝔼.E t m = m := 𝔼.E_E_self t y
  have hinv : 𝔼.E t m⁻¹ = m⁻¹ := InflationTarget.known_inv 𝔼 h𝔼 hmk (fun ω => (hm ω).ne')
  have hinv2 : 𝔼.E t (m⁻¹ * m⁻¹) = m⁻¹ * m⁻¹ := InflationTarget.known_mul 𝔼 h𝔼 hinv hinv
  have hle : (2 : ℝ) • m⁻¹ - (m⁻¹ * m⁻¹) * y ≤ fun ω => 1 / y ω := fun ω => by
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.inv_apply, smul_eq_mul]
    have h1 := inv_ge_tangent (hy ω) (hm ω)
    have h2 : 2 * (m ω)⁻¹ - (m ω)⁻¹ * (m ω)⁻¹ * y ω = 2 / m ω - y ω / m ω ^ 2 := by ring
    linarith
  have hmono := 𝔼.mono t hle ω
  rw [map_sub, map_smul, hinv, h𝔼 t _ _ hinv2] at hmono
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.inv_apply, smul_eq_mul] at hmono
  have hm0 := (hm ω).ne'
  calc 1 / m ω = 2 * (m ω)⁻¹ - (m ω)⁻¹ * (m ω)⁻¹ * m ω := by field_simp; ring
    _ ≤ _ := hmono

/-- Cochrane (2023), eq. (9.12), p. 267: with a deterministic target `P*`, the interest-rate
target `β E_t (P_t/P_{t+1}) = β P*_t/P*_{t+1}` makes `y_t = P*_t/P_t` a martingale. -/
theorem fr_martingale (h𝔼 : 𝔼.PullOut) {β : ℝ} (hβ0 : 0 < β) {P : ℕ → Ω → ℝ}
    {Pstar : ℕ → ℝ} (hP : ∀ t ω, 0 < P t ω) (hPs : ∀ t, 0 < Pstar t) (hPa : 𝔼.Adapted P)
    (h912 : ∀ t, β • 𝔼.E t (P t / P (t + 1)) = fun _ => β * (Pstar t / Pstar (t + 1)))
    (t : ℕ) : 𝔼.E t (fun ω => Pstar (t + 1) / P (t + 1) ω) = fun ω => Pstar t / P t ω := by
  have hsplit : P t / P (t + 1) = P t * fun ω => 1 / P (t + 1) ω := by
    funext ω
    simp only [Pi.div_apply, Pi.mul_apply]
    ring
  have h1 := h912 t
  rw [hsplit, h𝔼 t _ _ (hPa t)] at h1
  have hy : (fun ω => Pstar (t + 1) / P (t + 1) ω) = Pstar (t + 1) • fun ω => 1 / P (t + 1) ω := by
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hy, map_smul]
  funext ω
  have h2 := congrFun h1 ω
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at h2 ⊢
  have hPt := (hP t ω).ne'
  have hPs1 := (hPs (t + 1)).ne'
  have h3 : 𝔼.E t (fun ω => 1 / P (t + 1) ω) ω = Pstar t / Pstar (t + 1) / P t ω := by
    field_simp
    have := mul_left_cancel₀ hβ0.ne' (by linarith : β * (P t ω * 𝔼.E t (fun ω =>
      1 / P (t + 1) ω) ω) = β * (Pstar t / Pstar (t + 1)))
    field_simp at this
    linarith
  rw [h3]
  field_simp

/-- Cochrane (2023), §9.3.2, p. 267 (**Theorem FR (c)**): under genuine uncertainty, with a
deterministic target `P*`, the interest-rate target (9.12) and the date-0 valuation (9.9) in
expected form, `b_{−1} = ∑ βʲ E_0 s_{0,j} + θ ∑ βʲ E_0 (P_j − P*_j)`, with `b_{−1}` equal to the
present value of `s₀`, force only `P_0 ≤ P*_0` (Jensen's inequality, since `P*_t/P_t` is a
martingale). -/
theorem fr_jensen (h𝔼 : 𝔼.PullOut) {β θ : ℝ} (hβ0 : 0 < β) (hθ : θ ≠ 0) {P s0 : ℕ → Ω → ℝ}
    {Pstar : ℕ → ℝ} {b0 : Ω → ℝ} (hP : ∀ t ω, 0 < P t ω) (hPs : ∀ t, 0 < Pstar t)
    (hPa : 𝔼.Adapted P)
    (h912 : ∀ t, β • 𝔼.E t (P t / P (t + 1)) = fun _ => β * (Pstar t / Pstar (t + 1)))
    (h99 : ∀ ω, HasSum (fun j => β ^ j * (𝔼.E 0 (s0 j) ω + θ * (𝔼.E 0 (P j) ω - Pstar j)))
      (b0 ω))
    (hb : ∀ ω, HasSum (fun j => β ^ j * 𝔼.E 0 (s0 j) ω) (b0 ω))
    (hPsum : Summable (fun j => β ^ j * Pstar j)) (ω : Ω) : P 0 ω ≤ Pstar 0 := by
  set y : ℕ → Ω → ℝ := fun t ω => Pstar t / P t ω with hy_def
  have hypos : ∀ t ω, 0 < y t ω := fun t ω => div_pos (hPs t) (hP t ω)
  have hmart : ∀ t, 𝔼.E t (y (t + 1)) = y t :=
    fun t => fr_martingale 𝔼 h𝔼 hβ0 hP hPs hPa h912 t
  have hy0 : 𝔼.E 0 (y 0) = y 0 := by
    have : y 0 = Pstar 0 • (P 0)⁻¹ := by
      funext ω
      simp only [hy_def, Pi.smul_apply, Pi.inv_apply, smul_eq_mul]
      ring
    rw [this, map_smul, InflationTarget.known_inv 𝔼 h𝔼 (hPa 0) (fun ω => (hP 0 ω).ne')]
  have hE0 : ∀ j, 𝔼.E 0 (y j) = y 0 := by
    intro j
    induction j with
    | zero => exact hy0
    | succ j ih => rw [← 𝔼.tower (Nat.zero_le j), hmart j, ih]
  have hbound : ∀ j, (P 0 ω / Pstar 0) * Pstar j ≤ 𝔼.E 0 (P j) ω := by
    intro j
    have hJ := jensen_inv 𝔼 h𝔼 (hypos j) (fun ω => by rw [hE0 j]; exact hypos 0 ω) ω
    rw [hE0 j] at hJ
    have hfun : (fun ω => 1 / y j ω) = (Pstar j)⁻¹ • P j := by
      funext ω
      simp only [hy_def, Pi.smul_apply, smul_eq_mul]
      field_simp [(hP j ω).ne', (hPs j).ne']
    rw [hfun, map_smul] at hJ
    simp only [hy_def, Pi.smul_apply, smul_eq_mul] at hJ
    have hPs0 := (hPs 0).ne'
    have hP0 := (hP 0 ω).ne'
    have hPsj := hPs j
    rw [one_div_div] at hJ
    calc P 0 ω / Pstar 0 * Pstar j ≤ (Pstar j)⁻¹ * 𝔼.E 0 (P j) ω * Pstar j :=
          mul_le_mul_of_nonneg_right hJ hPsj.le
      _ = 𝔼.E 0 (P j) ω := by field_simp
  have hdiff := (h99 ω).sub (hb ω)
  rw [sub_self] at hdiff
  have hg : HasSum (fun j => β ^ j * (𝔼.E 0 (P j) ω - Pstar j)) 0 := by
    have := hdiff.mul_left θ⁻¹
    rw [mul_zero] at this
    refine this.congr_fun fun j => ?_
    field_simp
    ring
  set c := P 0 ω / Pstar 0 with hc
  have hf : HasSum (fun j => (c - 1) * (β ^ j * Pstar j)) ((c - 1) * ∑' j, β ^ j * Pstar j) :=
    hPsum.hasSum.mul_left (c - 1)
  have hle := hasSum_le (fun j => by
    have := hbound j
    have hb' := pow_pos hβ0 j
    nlinarith) hf hg
  have hpos : 0 < ∑' j, β ^ j * Pstar j :=
    hPsum.tsum_pos (fun j => (mul_pos (pow_pos hβ0 j) (hPs j)).le) 0 (by simpa using hPs 0)
  have hc1 : c ≤ 1 := by nlinarith
  rw [hc, div_le_one (hPs 0)] at hc1
  exact hc1

/-! ### Theorem FR (d): bounded price levels restore uniqueness -/

/-- Cochrane (2023), §9.3.2, p. 267 (**Theorem FR (d)**, core, answering the open question of
E9.9): with `P* ≡ 1`, let `S_t` be a process with `S_t = P_t + β S_{t+1}`, `S_{t+1}` known at `t`
(predetermined real debt) and `S_0 = 1/(1 − β)`, and let `1/P` be a martingale ((9.12)). Then
`Z_t = S_t/P_t` obeys `E_t Z_{t+1} = (Z_t − 1)/β`; if `βᵏ E_t Z_{t+k} → 0`, then `P ≡ 1 = P*`. -/
theorem unique_of_ratio_tvc (h𝔼 : 𝔼.PullOut) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {P S : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω)
    (hmart : ∀ t, 𝔼.E t (fun ω => 1 / P (t + 1) ω) = fun ω => 1 / P t ω)
    (hrec : ∀ t, S t = P t + β • S (t + 1)) (hpre : ∀ t, 𝔼.E t (S (t + 1)) = S (t + 1))
    (hS0 : S 0 = fun _ => 1 / (1 - β))
    (hZ : ∀ t ω, Tendsto (fun k => β ^ k * 𝔼.E t (fun ω => S (t + k) ω / P (t + k) ω) ω)
      atTop (𝓝 0)) :
    P = fun _ _ => 1 := by
  set A := 1 / (1 - β) with hA_def
  have h1β : 1 - β ≠ 0 := by linarith
  have hA1 : 1 + β * A = A := by rw [hA_def]; field_simp; ring
  have hA0 : A ≠ 0 := by rw [hA_def]; exact one_div_ne_zero h1β
  -- the recursion for Z
  have hZrec : ∀ t, 𝔼.E t (fun ω => S (t + 1) ω / P (t + 1) ω) =
      fun ω => (S t ω / P t ω - 1) / β := by
    intro t
    have hsplit : (fun ω => S (t + 1) ω / P (t + 1) ω) =
        S (t + 1) * fun ω => 1 / P (t + 1) ω := by
      funext ω
      simp only [Pi.mul_apply]
      ring
    rw [hsplit, h𝔼 t _ _ (hpre t), hmart t]
    funext ω
    have h := congrFun (hrec t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply] at h ⊢
    have hP0 := (hP t ω).ne'
    have hS1 : S (t + 1) ω = (S t ω - P t ω) / β := by
      rw [eq_div_iff hβ0.ne']
      linarith
    rw [hS1]
    field_simp
  set X : ℕ → Ω → ℝ := fun t ω => S t ω / P t ω - A with hX_def
  have hX : ∀ t, X t = β • 𝔼.E t (X (t + 1)) := by
    intro t
    have hXs : X (t + 1) = (fun ω => S (t + 1) ω / P (t + 1) ω) - fun _ => A := by
      funext ω
      simp [hX_def]
    rw [hXs, map_sub, hZrec t, 𝔼.const]
    funext ω
    simp only [hX_def, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    linarith
  have hXtvc : TVC 𝔼 β X := fun t ω => by
    have e : ∀ k, β ^ k * 𝔼.E t (X (t + k)) ω =
        β ^ k * 𝔼.E t (fun ω => S (t + k) ω / P (t + k) ω) ω - β ^ k * A := fun k => by
      have hXs : X (t + k) = (fun ω => S (t + k) ω / P (t + k) ω) - fun _ => A := by
        funext ω
        simp [hX_def]
      rw [hXs, map_sub, 𝔼.const]
      simp only [Pi.sub_apply]
      ring
    simp_rw [e]
    simpa using (hZ t ω).sub ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const A)
  have hX0 : ∀ t ω, X t ω = 0 := fun t ω => congrFun (eq_zero_of_tvc 𝔼 hX hXtvc t) ω
  have hSP : ∀ t ω, S t ω = A * P t ω := by
    intro t ω
    have h := hX0 t ω
    simp only [hX_def] at h
    have hP0 := (hP t ω).ne'
    field_simp at h
    linarith
  have hknown : ∀ t, 𝔼.E t (P (t + 1)) = P (t + 1) := by
    intro t
    have e : P (t + 1) = A⁻¹ • S (t + 1) := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul, hSP]
      field_simp
    rw [e, map_smul, hpre t]
  funext t
  induction t with
  | zero =>
    funext ω
    have h := hSP 0 ω
    rw [hS0] at h
    have : A * 1 = A * P 0 ω := by rw [mul_one]; exact h
    exact (mul_left_cancel₀ hA0 this).symm
  | succ t ih =>
    have hinv : 𝔼.E t (P (t + 1))⁻¹ = (P (t + 1))⁻¹ :=
      InflationTarget.known_inv 𝔼 h𝔼 (hknown t) (fun ω => (hP (t + 1) ω).ne')
    have e1 : (fun ω => 1 / P (t + 1) ω) = (P (t + 1))⁻¹ := by
      funext ω
      simp
    have h := hmart t
    rw [e1, hinv, ih] at h
    funext ω
    have h2 := congrFun h ω
    simp only [Pi.inv_apply] at h2
    have := (hP (t + 1) ω).ne'
    field_simp at h2
    linarith

/-- Cochrane (2023), §9.3.2, p. 266 (supporting Theorem FR (d)): if `S_t = P_t + β E_t S_{t+1}`
with `P > 0` adapted and the transversality condition `βᵏ E_t S_{t+k} → 0`, then
`0 ≤ S_t`, and `S_t ≤ M/(1 − β)` when `P ≤ M`. -/
theorem value_bounds {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {P S : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (hPa : 𝔼.Adapted P) (hsol : ForwardSolution.Solves 𝔼 β P S)
    (hTS : ∀ t ω, Tendsto (fun k => β ^ k * 𝔼.E t (S (t + k)) ω) atTop (𝓝 0)) (t : ℕ) (ω : Ω) :
    0 ≤ S t ω ∧ ∀ M, (∀ t ω, P t ω ≤ M) → S t ω ≤ M / (1 - β) := by
  have hpart := tendsto_partialSums_of_tvc 𝔼 hPa hsol t ω (hTS t ω)
  have hEnn : ∀ j, 0 ≤ 𝔼.E t (P (t + j)) ω := fun j => by
    have := 𝔼.mono t (show (fun _ => (0 : ℝ)) ≤ P (t + j) from fun ω => (hP _ ω).le) ω
    rwa [𝔼.const] at this
  refine ⟨ge_of_tendsto' hpart fun k => Finset.sum_nonneg fun j _ =>
    mul_nonneg (pow_nonneg hβ0.le j) (hEnn j), fun M hM => ?_⟩
  have hM0 : 0 ≤ M := (hP 0 ω).le.trans (hM 0 ω)
  refine le_of_tendsto' hpart fun k => ?_
  have hEM : ∀ j, 𝔼.E t (P (t + j)) ω ≤ M := fun j => by
    have := 𝔼.mono t (show P (t + j) ≤ fun _ => M from fun ω => hM _ ω) ω
    rwa [𝔼.const] at this
  have hgeo := summable_geometric_of_lt_one hβ0.le hβ1
  calc ∑ j ∈ Finset.range k, β ^ j * 𝔼.E t (P (t + j)) ω
      ≤ ∑ j ∈ Finset.range k, β ^ j * M :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hEM j) (pow_nonneg hβ0.le j)
    _ = M * ∑ j ∈ Finset.range k, β ^ j := by rw [Finset.mul_sum]; ring_nf
    _ ≤ M * ∑' j, β ^ j := mul_le_mul_of_nonneg_left
        (hgeo.sum_le_tsum _ fun j _ => pow_nonneg hβ0.le j) hM0
    _ = M / (1 - β) := by rw [tsum_geometric_of_lt_one hβ0.le hβ1, div_eq_mul_inv]

/-- Cochrane (2023), §9.3.2, p. 266 (**Theorem FR (d)**, settling E9.9): under genuine
uncertainty (any expectation system with the pull-out property), with `P* ≡ 1`, real debt
following (9.8) with the rule `s_t = (1 − β) b̄ + θ (P_t − 1)` (`θ ≠ 0`), predetermined real debt,
initial debt `b_{−1} = b̄` equal to the present value of `s₀`, the transversality condition, and
the interest-rate target (9.12): if the price level is **bounded above, or bounded away from
zero**, then `P_t = P*_t = 1` at every date and state. Together with `Sunspot`, whose prices are
unbounded above and approach zero, this settles the question. -/
theorem fr_unique_bounded (h𝔼 : 𝔼.PullOut) {β θ bbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 0) {P b : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω) (hPa : 𝔼.Adapted P)
    (h912 : ∀ t, β • 𝔼.E t (P t / P (t + 1)) = fun _ => β)
    (hflow : ∀ t ω, b t ω = (1 - β) * bbar + θ * (P t ω - 1) + β * b (t + 1) ω)
    (hpre : ∀ t, 𝔼.E t (b (t + 1)) = b (t + 1)) (hb0 : ∀ ω, b 0 ω = bbar)
    (htvc : ∀ t ω, Tendsto (fun T => β ^ T * 𝔼.E t (b (t + T)) ω) atTop (𝓝 0))
    (hbdd : (∃ M, ∀ t ω, P t ω ≤ M) ∨ ∃ m, 0 < m ∧ ∀ t ω, m ≤ P t ω) :
    P = fun _ _ => 1 := by
  have h1β : 1 - β ≠ 0 := by linarith
  set A := 1 / (1 - β) with hA_def
  set S : ℕ → Ω → ℝ := fun t ω => A + (b t ω - bbar) / θ with hS_def
  have hSlin : ∀ t, S t = (fun _ => A - bbar / θ) + θ⁻¹ • b t := fun t => by
    funext ω
    simp only [hS_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hrec : ∀ t, S t = P t + β • S (t + 1) := by
    intro t
    funext ω
    simp only [hS_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hflow t ω, hA_def]
    field_simp
    ring
  have hSpre : ∀ t, 𝔼.E t (S (t + 1)) = S (t + 1) := fun t => by
    rw [hSlin, map_add, 𝔼.const, map_smul, hpre t]
  have hS0 : S 0 = fun _ => 1 / (1 - β) := by
    funext ω
    simp [hS_def, hb0 ω, hA_def]
  have hmart : ∀ t, 𝔼.E t (fun ω => 1 / P (t + 1) ω) = fun ω => 1 / P t ω := by
    intro t
    have h := fr_martingale 𝔼 h𝔼 hβ0 (Pstar := fun _ => 1) hP (fun _ => one_pos) hPa
      (fun t => by rw [h912 t]; funext; simp) t
    simpa using h
  have hTS : ∀ t ω, Tendsto (fun k => β ^ k * 𝔼.E t (S (t + k)) ω) atTop (𝓝 0) := by
    intro t ω
    have e : ∀ k, β ^ k * 𝔼.E t (S (t + k)) ω =
        (A - bbar / θ) * β ^ k + θ⁻¹ * (β ^ k * 𝔼.E t (b (t + k)) ω) := fun k => by
      rw [hSlin, map_add, 𝔼.const, map_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simp_rw [e]
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul (A - bbar / θ)).add
      ((htvc t ω).const_mul θ⁻¹)
  have hsol : ForwardSolution.Solves 𝔼 β P S := fun t => by
    rw [hSpre t, hrec t]
    abel
  have hbnd := value_bounds 𝔼 hβ0 hβ1 hP hPa hsol hTS
  have hyiter : ∀ t k, 𝔼.E t (fun ω => 1 / P (t + k) ω) = fun ω => 1 / P t ω := by
    intro t k
    induction k with
    | zero =>
      simp only [add_zero]
      rw [show (fun ω => 1 / P t ω) = (P t)⁻¹ from funext fun ω => by simp]
      exact InflationTarget.known_inv 𝔼 h𝔼 (hPa t) (fun ω => (hP t ω).ne')
    | succ k ih =>
      rw [← add_assoc, ← 𝔼.tower (Nat.le_add_right t k), hmart (t + k), ih]
  refine unique_of_ratio_tvc 𝔼 h𝔼 hβ0 hβ1 hP hmart hrec hSpre hS0 fun t ω => ?_
  have hZnn : ∀ k, 0 ≤ 𝔼.E t (fun ω => S (t + k) ω / P (t + k) ω) ω := fun k => by
    have := 𝔼.mono t (show (fun _ => (0 : ℝ)) ≤ fun ω => S (t + k) ω / P (t + k) ω from
      fun ω => div_nonneg (hbnd _ ω).1 (hP _ ω).le) ω
    rwa [𝔼.const] at this
  rcases hbdd with ⟨M, hM⟩ | ⟨m, hm, hm'⟩
  · -- bounded above: E_t Z_{t+k} ≤ (M/(1 − β)) E_t (1/P_{t+k}) = (M/(1 − β))/P_t
    have hle : ∀ k, 𝔼.E t (fun ω => S (t + k) ω / P (t + k) ω) ω ≤ M / (1 - β) * (1 / P t ω) :=
      fun k => by
        have hmono := 𝔼.mono t (show (fun ω => S (t + k) ω / P (t + k) ω) ≤
            (M / (1 - β)) • fun ω => 1 / P (t + k) ω from fun ω => by
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [mul_one_div]
          exact div_le_div_of_nonneg_right ((hbnd _ ω).2 M hM) (hP _ ω).le) ω
        rwa [map_smul, hyiter t k] at hmono
    refine squeeze_zero (fun k => mul_nonneg (pow_nonneg hβ0.le k) (hZnn k))
      (fun k => mul_le_mul_of_nonneg_left (hle k) (pow_nonneg hβ0.le k)) ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const
      (M / (1 - β) * (1 / P t ω))
  · -- bounded away from zero: E_t Z_{t+k} ≤ E_t S_{t+k}/m
    have hle : ∀ k, 𝔼.E t (fun ω => S (t + k) ω / P (t + k) ω) ω ≤
        m⁻¹ * 𝔼.E t (S (t + k)) ω := fun k => by
      have hmono := 𝔼.mono t (show (fun ω => S (t + k) ω / P (t + k) ω) ≤
          m⁻¹ • S (t + k) from fun ω => by
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [inv_mul_eq_div]
        exact div_le_div_of_nonneg_left (hbnd _ ω).1 hm (hm' _ ω)) ω
      rwa [map_smul] at hmono
    have hb2 : ∀ k, β ^ k * 𝔼.E t (fun ω => S (t + k) ω / P (t + k) ω) ω ≤
        m⁻¹ * (β ^ k * 𝔼.E t (S (t + k)) ω) := fun k => by
      calc _ ≤ β ^ k * (m⁻¹ * 𝔼.E t (S (t + k)) ω) :=
            mul_le_mul_of_nonneg_left (hle k) (pow_nonneg hβ0.le k)
        _ = _ := by ring
    refine squeeze_zero (fun k => mul_nonneg (pow_nonneg hβ0.le k) (hZnn k)) hb2 ?_
    simpa using (hTS t ω).const_mul m⁻¹

/-! ### Theorem FR (b): the settle-or-continue sunspot tree -/

namespace Sunspot

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample E9.9): the coefficient
`L = c₀/(1 − β²)` of the value of the continue node. -/
noncomputable def coefL (β c0 : ℝ) : ℝ := c0 / (1 - β ^ 2)

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample E9.9): the coefficient
`K = 1/(1 − β) − c₀/(1 − β²)` of the value of the continue node. -/
noncomputable def coefK (β c0 : ℝ) : ℝ := 1 / (1 - β) - c0 / (1 - β ^ 2)

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample E9.9): the price level `c₀ βⁿ` at the date-`n`
node where the path has not yet settled. -/
noncomputable def contPrice (β c0 : ℝ) (n : ℕ) : ℝ := c0 * β ^ n

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample E9.9): `S_n = K β⁻ⁿ + L βⁿ`, the expected
present value `∑ⱼ βʲ E_n P_{n+j}` at the date-`n` continue node (and the value of a node that
settled at date `n`). -/
noncomputable def value (β c0 : ℝ) (n : ℕ) : ℝ := coefK β c0 * β⁻¹ ^ n + coefL β c0 * β ^ n

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample E9.9): the price level `(1 − β) S_n` at which
a path that settles at date `n` stays forever. -/
noncomputable def settlePrice (β c0 : ℝ) (n : ℕ) : ℝ := (1 - β) * value β c0 n

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample E9.9): the probability of settling at date
`n + 1` given that the path has not settled by date `n`, chosen so that `1/P` is a martingale. -/
noncomputable def settleProb (β c0 : ℝ) (n : ℕ) : ℝ :=
  (1 / contPrice β c0 (n + 1) - 1 / contPrice β c0 n) /
    (1 / contPrice β c0 (n + 1) - 1 / settlePrice β c0 (n + 1))

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample E9.9): the probability, at the date-`t`
continue node, that the path is still unsettled at date `t + j`. -/
noncomputable def contProb (β c0 : ℝ) (t j : ℕ) : ℝ :=
  ∏ i ∈ Finset.range j, (1 - settleProb β c0 (t + i))

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample E9.9): the explicit conditional expectation,
at the date-`t` continue node, of a date-`(t + j)` random variable `X`. A node is `none` (not yet
settled) or `some k` (settled at date `k`); with probability `contProb t j` the path is still
unsettled, and with probability `contProb t i · settleProb (t + i)` it settled at date `t + i + 1`.
At a settled node the conditional expectation is the value itself. -/
noncomputable def condE (β c0 : ℝ) (t j : ℕ) (X : Option ℕ → ℝ) : ℝ :=
  contProb β c0 t j * X none +
    ∑ i ∈ Finset.range j, contProb β c0 t i * settleProb β c0 (t + i) * X (some (t + i + 1))

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample E9.9): the price level at a date-`n` node. -/
noncomputable def price (β c0 : ℝ) (n : ℕ) (x : Option ℕ) : ℝ :=
  x.elim (contPrice β c0 n) (settlePrice β c0)

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample E9.9): `∑ⱼ βʲ E_n P_{n+j}` at a date-`n`
node. -/
noncomputable def nodeValue (β c0 : ℝ) (n : ℕ) (x : Option ℕ) : ℝ :=
  x.elim (value β c0 n) (value β c0)

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample E9.9): real (indexed) debt outstanding at a
date-`n` node, `b̄ + θ (∑ⱼ βʲ E_n P_{n+j} − 1/(1 − β))`. -/
noncomputable def debt (β c0 θ bbar : ℝ) (n : ℕ) (x : Option ℕ) : ℝ :=
  bbar + θ * (nodeValue β c0 n x - 1 / (1 - β))

/-- Cochrane (2023), §9.3.2, p. 266 (counterexample E9.9): the surplus at a date-`n` node,
`s_{0} + θ (P − P*)` with `s₀ = (1 − β) b̄` and `P* ≡ 1`. -/
noncomputable def surplus (β c0 θ bbar : ℝ) (n : ℕ) (x : Option ℕ) : ℝ :=
  (1 - β) * bbar + θ * (price β c0 n x - 1)

variable {β c0 : ℝ}

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): `S_n = P_n + β S_{n+1}` along the continue path. -/
theorem value_rec (hβ0 : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    value β c0 n = contPrice β c0 n + β * value β c0 (n + 1) := by
  have hβ := hβ0.ne'
  have h2 : 1 - β ^ 2 ≠ 0 := by nlinarith
  unfold value contPrice coefL coefK
  rw [pow_succ β⁻¹, pow_succ β]
  field_simp
  ring

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): `S_0 = 1/(1 − β)`, the present value of `P* ≡ 1`. -/
theorem value_zero : value β c0 0 = 1 / (1 - β) := by
  simp [value, coefK, coefL]

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): `K > 0` when `c₀ < 1`. -/
theorem coefK_pos (hβ0 : 0 < β) (hβ1 : β < 1) (hc1 : c0 < 1) : 0 < coefK β c0 := by
  unfold coefK
  have h1 : 0 < 1 - β := by linarith
  have h2 : 0 < 1 - β ^ 2 := by nlinarith
  rw [show 1 / (1 - β) - c0 / (1 - β ^ 2) = (1 + β - c0) / (1 - β ^ 2) by field_simp; ring]
  exact div_pos (by linarith) h2

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): `L > 0`. -/
theorem coefL_pos (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) : 0 < coefL β c0 :=
  div_pos hc0 (by nlinarith)

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): `S_n > 0`. -/
theorem value_pos (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (n : ℕ) :
    0 < value β c0 n := by
  unfold value
  have := coefK_pos hβ0 hβ1 hc1
  have := coefL_pos hβ0 hβ1 hc0
  positivity

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): `S_n ≤ (K + L) β⁻ⁿ`. -/
theorem value_le (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (n : ℕ) :
    value β c0 n ≤ (coefK β c0 + coefL β c0) * β⁻¹ ^ n := by
  unfold value
  have hL := coefL_pos hβ0 hβ1 hc0
  have h1 : β ^ n ≤ β⁻¹ ^ n := by
    have : β ^ n ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
    have : 1 ≤ β⁻¹ ^ n := one_le_pow₀ (one_le_inv₀ hβ0 |>.mpr hβ1.le)
    linarith
  nlinarith

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the settle price exceeds the current continue price,
`P_n < (1 − β) S_{n+1}`; this is where `c₀ < 1` (i.e. `P_0 < P*_0`) is used. -/
theorem contPrice_lt_settlePrice (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (n : ℕ) : contPrice β c0 n < settlePrice β c0 (n + 1) := by
  unfold contPrice settlePrice value coefK coefL
  set y := β ^ n with hy_def
  have hy : 0 < y := pow_pos hβ0 n
  have hy1 : y ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
  have hβ := hβ0.ne'
  have h1 : 0 < 1 - β := by linarith
  have h2 : 0 < 1 + β := by linarith
  have hinv : β⁻¹ ^ (n + 1) = (y * β)⁻¹ := by rw [inv_pow, pow_succ]
  rw [hinv, pow_succ β n, ← hy_def]
  rw [show (1 - β) * ((1 / (1 - β) - c0 / (1 - β ^ 2)) * (y * β)⁻¹ + c0 / (1 - β ^ 2) * (y * β))
      = ((1 + β - c0) + c0 * y ^ 2 * β ^ 2) / ((1 + β) * y * β) by
    have h3 : 1 - β ^ 2 = (1 - β) * (1 + β) := by ring
    rw [h3]
    field_simp]
  rw [lt_div_iff₀ (by positivity)]
  have hy2 : y ^ 2 ≤ 1 := by nlinarith
  have h4 : c0 * y ^ 2 * β ≤ c0 * β := by
    have := mul_le_mul_of_nonneg_left hy2 (mul_nonneg hc0.le hβ0.le)
    nlinarith
  nlinarith

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the settle probability lies strictly between
`1 − β` and `1`. -/
theorem settleProb_bounds (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (n : ℕ) :
    1 - β < settleProb β c0 n ∧ settleProb β c0 n < 1 := by
  have hlt := contPrice_lt_settlePrice hβ0 hβ1 hc0 hc1 n
  have hc : 0 < contPrice β c0 n := by unfold contPrice; positivity
  have hc' : contPrice β c0 (n + 1) = β * contPrice β c0 n := by
    unfold contPrice
    ring
  set c := contPrice β c0 n
  set H := settlePrice β c0 (n + 1)
  have hH : 0 < H := lt_trans hc hlt
  have hβ := hβ0.ne'
  unfold settleProb
  rw [hc']
  have hD : 0 < 1 / (β * c) - 1 / H := by
    rw [sub_pos, div_lt_div_iff₀ hH (by positivity)]
    nlinarith
  constructor
  · rw [lt_div_iff₀ hD]
    have : 0 < 1 / H := by positivity
    have e : (1 - β) * (1 / (β * c) - 1 / H) = (1 / (β * c) - 1 / c) - (1 - β) * (1 / H) := by
      field_simp
    rw [e]
    nlinarith
  · rw [div_lt_one hD, sub_lt_sub_iff_left]
    exact one_div_lt_one_div_of_lt hc hlt

/-- Cochrane (2023), eq. (9.12), p. 267 (E9.9): with these probabilities `1/P` is a martingale at
the continue node, `p/H_{n+1} + (1 − p)/P_{n+1} = 1/P_n`. -/
theorem martingale_inv (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (n : ℕ) :
    settleProb β c0 n / settlePrice β c0 (n + 1) +
      (1 - settleProb β c0 n) / contPrice β c0 (n + 1) = 1 / contPrice β c0 n := by
  have hlt := contPrice_lt_settlePrice hβ0 hβ1 hc0 hc1 n
  have hc : 0 < contPrice β c0 n := by unfold contPrice; positivity
  have hc' : 0 < contPrice β c0 (n + 1) := by unfold contPrice; positivity
  have hH : 0 < settlePrice β c0 (n + 1) := lt_trans hc hlt
  have h1 : contPrice β c0 (n + 1) < settlePrice β c0 (n + 1) := by
    have : contPrice β c0 (n + 1) = β * contPrice β c0 n := by unfold contPrice; ring
    rw [this]
    nlinarith
  have hne : settlePrice β c0 (n + 1) - contPrice β c0 (n + 1) ≠ 0 := by linarith
  have hD : 1 / contPrice β c0 (n + 1) - 1 / settlePrice β c0 (n + 1) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    rw [div_eq_div_iff hc'.ne' hH.ne'] at h
    linarith
  have hp : settleProb β c0 n * (1 / contPrice β c0 (n + 1) - 1 / settlePrice β c0 (n + 1)) =
      1 / contPrice β c0 (n + 1) - 1 / contPrice β c0 n := by
    unfold settleProb
    field_simp
  linear_combination -hp

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): `contProb t (j + 1) = (1 − p_t) contProb (t + 1) j`. -/
theorem contProb_succ' (t j : ℕ) :
    contProb β c0 t (j + 1) = (1 - settleProb β c0 t) * contProb β c0 (t + 1) j := by
  unfold contProb
  rw [Finset.prod_range_succ']
  simp only [add_zero]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [show t + (i + 1) = t + 1 + i by ring]

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): `0 ≤ contProb t j ≤ βʲ`. -/
theorem contProb_bounds (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (t j : ℕ) :
    0 ≤ contProb β c0 t j ∧ contProb β c0 t j ≤ β ^ j := by
  induction j with
  | zero => simp [contProb]
  | succ j ih =>
    have hp := settleProb_bounds hβ0 hβ1 hc0 hc1 (t + j)
    have h : contProb β c0 t (j + 1) = contProb β c0 t j * (1 - settleProb β c0 (t + j)) := by
      unfold contProb
      rw [Finset.prod_range_succ]
    rw [h, pow_succ]
    constructor
    · exact mul_nonneg ih.1 (by linarith)
    · exact mul_le_mul ih.2 (by linarith) (by linarith) (pow_nonneg hβ0.le j)

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the law of iterated expectations on the tree,
`E_t X_{t+j+1} = p_t X(settled at t+1) + (1 − p_t) E_{t+1} X_{t+j+1}`. -/
theorem condE_succ (t j : ℕ) (X : Option ℕ → ℝ) :
    condE β c0 t (j + 1) X = settleProb β c0 t * X (some (t + 1)) +
      (1 - settleProb β c0 t) * condE β c0 (t + 1) j X := by
  unfold condE
  rw [contProb_succ', Finset.sum_range_succ']
  simp only [add_zero, contProb, Finset.range_zero, Finset.prod_empty, one_mul]
  rw [mul_add, Finset.mul_sum]
  have hterm : ∀ i ∈ Finset.range j,
      (∏ i ∈ Finset.range (i + 1), (1 - settleProb β c0 (t + i))) * settleProb β c0 (t + (i + 1)) *
        X (some (t + (i + 1) + 1)) = (1 - settleProb β c0 t) *
        ((∏ i_1 ∈ Finset.range i, (1 - settleProb β c0 (t + 1 + i_1))) *
          settleProb β c0 (t + 1 + i) * X (some (t + 1 + i + 1))) := by
    intro i _
    have h := contProb_succ' (β := β) (c0 := c0) t i
    unfold contProb at h
    rw [h, show t + (i + 1) = t + 1 + i by ring]
    ring
  rw [Finset.sum_congr rfl hterm]
  ring

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): conditional expectations are affine,
`E (a + b X) = a + b E X` (so the probabilities sum to one). -/
theorem condE_affine (t j : ℕ) (a b : ℝ) (X : Option ℕ → ℝ) :
    condE β c0 t j (fun x => a + b * X x) = a + b * condE β c0 t j X := by
  induction j generalizing t with
  | zero => simp [condE, contProb]
  | succ j ih =>
    rw [condE_succ, condE_succ, ih]
    ring

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the probabilities at each horizon sum to one. -/
theorem condE_const (t j : ℕ) (a : ℝ) : condE β c0 t j (fun _ => a) = a := by
  have := condE_affine (β := β) (c0 := c0) t j a 0 (fun _ => 0)
  simpa using this

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): conditional expectations of nonnegative variables
are nonnegative. -/
theorem condE_nonneg (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (t j : ℕ)
    {X : Option ℕ → ℝ} (hX : ∀ x, 0 ≤ X x) : 0 ≤ condE β c0 t j X := by
  induction j generalizing t with
  | zero => simpa [condE, contProb] using hX none
  | succ j ih =>
    rw [condE_succ]
    have hp := settleProb_bounds hβ0 hβ1 hc0 hc1 t
    have := ih (t + 1)
    have := hX (some (t + 1))
    have : 0 ≤ settleProb β c0 t := by linarith
    have : 0 ≤ 1 - settleProb β c0 t := by linarith
    positivity

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): for `(1 − β) ∑_{j<T} βʲ + βᵀ = 1`. -/
theorem geom_identity (T : ℕ) : (1 - β) * ∑ j ∈ Finset.range T, β ^ j + β ^ T = 1 := by
  have := geom_sum_mul β T
  linarith

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the finite-horizon identity
`S_n = ∑_{j<T} βʲ E_n P_{n+j} + βᵀ E_n S_{n+T}` at the continue node. -/
theorem value_finite (hβ0 : 0 < β) (hβ1 : β < 1) (T : ℕ) (n : ℕ) :
    value β c0 n = ∑ j ∈ Finset.range T, β ^ j * condE β c0 n j (price β c0 (n + j)) +
      β ^ T * condE β c0 n T (nodeValue β c0 (n + T)) := by
  induction T generalizing n with
  | zero => simp [condE, contProb, nodeValue]
  | succ T ih =>
    have hsum : ∑ j ∈ Finset.range T, β ^ (j + 1) * condE β c0 n (j + 1) (price β c0 (n + (j + 1)))
        = settleProb β c0 n * settlePrice β c0 (n + 1) * β * ∑ j ∈ Finset.range T, β ^ j +
          (1 - settleProb β c0 n) * β *
            ∑ j ∈ Finset.range T, β ^ j * condE β c0 (n + 1) j (price β c0 (n + 1 + j)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [condE_succ, show n + (j + 1) = n + 1 + j by ring]
      simp only [price, Option.elim_some]
      ring
    have hrem : condE β c0 n (T + 1) (nodeValue β c0 (n + (T + 1))) =
        settleProb β c0 n * value β c0 (n + 1) +
          (1 - settleProb β c0 n) * condE β c0 (n + 1) T (nodeValue β c0 (n + 1 + T)) := by
      rw [condE_succ, show n + (T + 1) = n + 1 + T by ring]
      simp only [nodeValue, Option.elim_some]
    rw [Finset.sum_range_succ', hsum, hrem]
    have hih := ih (n + 1)
    have hg := geom_identity (β := β) T
    have hrec := value_rec (c0 := c0) hβ0 hβ1 n
    have h0 : condE β c0 n 0 (price β c0 (n + 0)) = contPrice β c0 n := by
      simp [condE, contProb, price]
    rw [h0, hrec]
    unfold settlePrice
    rw [pow_succ]
    linear_combination (1 - settleProb β c0 n) * β * hih -
      settleProb β c0 n * β * value β c0 (n + 1) * hg

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9, the transversality condition for the value):
`βᵀ E_n S_{n+T} → 0` at the continue node. -/
theorem remainder_tendsto (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (n : ℕ) :
    Tendsto (fun T => β ^ T * condE β c0 n T (nodeValue β c0 (n + T))) atTop (𝓝 0) := by
  set C := coefK β c0 + coefL β c0 with hC
  have hCpos : 0 < C := add_pos (coefK_pos hβ0 hβ1 hc1) (coefL_pos hβ0 hβ1 hc0)
  have hβ := hβ0.ne'
  have hbound : ∀ T, β ^ T * condE β c0 n T (nodeValue β c0 (n + T)) ≤
      β ^ T * (C * β⁻¹ ^ n) + (T * β ^ T) * (C * β⁻¹ ^ (n + 1)) := by
    intro T
    have hsplit : condE β c0 n T (nodeValue β c0 (n + T)) = contProb β c0 n T * value β c0 (n + T)
        + ∑ i ∈ Finset.range T, contProb β c0 n i * settleProb β c0 (n + i) *
          value β c0 (n + i + 1) := by
      simp [condE, nodeValue]
    have h1 : contProb β c0 n T * value β c0 (n + T) ≤ C * β⁻¹ ^ n := by
      have hq := contProb_bounds hβ0 hβ1 hc0 hc1 n T
      have hv := value_le hβ0 hβ1 hc0 (n + T)
      have hvp := value_pos hβ0 hβ1 hc0 hc1 (n + T)
      calc contProb β c0 n T * value β c0 (n + T) ≤ β ^ T * (C * β⁻¹ ^ (n + T)) :=
            mul_le_mul hq.2 hv hvp.le (pow_nonneg hβ0.le T)
        _ = C * β⁻¹ ^ n * (β ^ T * β⁻¹ ^ T) := by rw [pow_add]; ring
        _ = C * β⁻¹ ^ n := by rw [← mul_pow, mul_inv_cancel₀ hβ, one_pow, mul_one]
    have h2 : ∑ i ∈ Finset.range T, contProb β c0 n i * settleProb β c0 (n + i) *
        value β c0 (n + i + 1) ≤ T * (C * β⁻¹ ^ (n + 1)) := by
      have : ∀ i ∈ Finset.range T, contProb β c0 n i * settleProb β c0 (n + i) *
          value β c0 (n + i + 1) ≤ C * β⁻¹ ^ (n + 1) := by
        intro i _
        have hq := contProb_bounds hβ0 hβ1 hc0 hc1 n i
        have hp := settleProb_bounds hβ0 hβ1 hc0 hc1 (n + i)
        have hv := value_le hβ0 hβ1 hc0 (n + i + 1)
        have hvp := value_pos hβ0 hβ1 hc0 hc1 (n + i + 1)
        calc contProb β c0 n i * settleProb β c0 (n + i) * value β c0 (n + i + 1)
            ≤ β ^ i * 1 * (C * β⁻¹ ^ (n + i + 1)) := by
              apply mul_le_mul (mul_le_mul hq.2 hp.2.le (by linarith) (pow_nonneg hβ0.le i)) hv
                hvp.le (by positivity)
          _ = C * β⁻¹ ^ (n + 1) * (β ^ i * β⁻¹ ^ i) := by
              rw [show n + i + 1 = n + 1 + i by ring, pow_add]
              ring
          _ = C * β⁻¹ ^ (n + 1) := by rw [← mul_pow, mul_inv_cancel₀ hβ, one_pow, mul_one]
      calc _ ≤ ∑ _i ∈ Finset.range T, C * β⁻¹ ^ (n + 1) := Finset.sum_le_sum this
        _ = T * (C * β⁻¹ ^ (n + 1)) := by simp
    rw [hsplit, mul_add]
    have hβT := pow_pos hβ0 T
    refine add_le_add (mul_le_mul_of_nonneg_left h1 hβT.le) ?_
    calc _ ≤ β ^ T * (T * (C * β⁻¹ ^ (n + 1))) := mul_le_mul_of_nonneg_left h2 hβT.le
      _ = _ := by ring
  have hnonneg : ∀ T, 0 ≤ β ^ T * condE β c0 n T (nodeValue β c0 (n + T)) := fun T =>
    mul_nonneg (pow_nonneg hβ0.le T) (condE_nonneg hβ0 hβ1 hc0 hc1 n T (fun x => by
      cases x with
      | none => exact (value_pos hβ0 hβ1 hc0 hc1 _).le
      | some k => exact (value_pos hβ0 hβ1 hc0 hc1 k).le))
  have hlim : Tendsto (fun T : ℕ => β ^ T * (C * β⁻¹ ^ n) + (T * β ^ T) * (C * β⁻¹ ^ (n + 1)))
      atTop (𝓝 0) := by
    have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (C * β⁻¹ ^ n)
    have h2 := (tendsto_self_mul_const_pow_of_lt_one hβ0.le hβ1).mul_const (C * β⁻¹ ^ (n + 1))
    simpa using h1.add h2
  exact squeeze_zero hnonneg hbound hlim

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): at the date-`n` continue node the expected present
value of the price level is a genuine convergent series, `∑ⱼ βʲ E_n P_{n+j} = S_n`. -/
theorem hasSum_value (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (n : ℕ) :
    HasSum (fun j => β ^ j * condE β c0 n j (price β c0 (n + j))) (value β c0 n) := by
  have hnonneg : ∀ j, 0 ≤ β ^ j * condE β c0 n j (price β c0 (n + j)) := fun j =>
    mul_nonneg (pow_nonneg hβ0.le j) (condE_nonneg hβ0 hβ1 hc0 hc1 n j (fun x => by
      cases x with
      | none => exact (by unfold price contPrice; simp only [Option.elim_none]; positivity)
      | some k =>
        simp only [price, Option.elim_some, settlePrice]
        exact mul_nonneg (by linarith) (value_pos hβ0 hβ1 hc0 hc1 k).le))
  rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
  have heq : (fun T => ∑ j ∈ Finset.range T, β ^ j * condE β c0 n j (price β c0 (n + j))) =
      fun T => value β c0 n - β ^ T * condE β c0 n T (nodeValue β c0 (n + T)) := by
    funext T
    have := value_finite (c0 := c0) hβ0 hβ1 T n
    linarith
  rw [heq]
  simpa using (remainder_tendsto hβ0 hβ1 hc0 hc1 n).const_sub (value β c0 n)

/-- Cochrane (2023), eq. (9.9), p. 266, at the continue node (E9.9): real debt equals the expected
present value of surpluses, `b_{n−1} = ∑ⱼ βʲ E_n s_{n+j}`. -/
theorem valuation_cont (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (θ bbar : ℝ) (n : ℕ) :
    HasSum (fun j => β ^ j * condE β c0 n j (surplus β c0 θ bbar (n + j)))
      (debt β c0 θ bbar n none) := by
  have hsurp : ∀ j, condE β c0 n j (surplus β c0 θ bbar (n + j)) =
      ((1 - β) * bbar - θ) + θ * condE β c0 n j (price β c0 (n + j)) := by
    intro j
    rw [← condE_affine]
    unfold surplus
    congr 1
    funext x
    ring
  have hg := hasSum_geometric_of_lt_one hβ0.le hβ1
  have h := (hg.mul_left ((1 - β) * bbar - θ)).add ((hasSum_value hβ0 hβ1 hc0 hc1 n).mul_left θ)
  have h1 : (1 - β) ≠ 0 := by linarith
  convert h using 1
  · funext j
    rw [hsurp]
    ring
  · simp only [debt, nodeValue, Option.elim_none]
    field_simp
    ring

/-- Cochrane (2023), eq. (9.9), p. 266, at a settled node (E9.9): the price stays at `H_k`
forever and real debt equals the present value of the constant surplus. -/
theorem valuation_settled (hβ0 : 0 < β) (hβ1 : β < 1) (θ bbar : ℝ) (n k : ℕ) :
    HasSum (fun j => β ^ j * surplus β c0 θ bbar (n + j) (some k))
      (debt β c0 θ bbar n (some k)) := by
  have hg := (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_left
    ((1 - β) * bbar + θ * (settlePrice β c0 k - 1))
  have h1 : (1 - β) ≠ 0 := by linarith
  convert hg using 1
  · funext j
    simp only [surplus, price, Option.elim_some]
    ring
  · simp only [debt, nodeValue, Option.elim_some, settlePrice]
    field_simp

/-- Cochrane (2023), eq. (9.8), p. 266, on the edges out of the continue node (E9.9): real debt is
predetermined — both children carry the same debt — and `b_{n−1} = s_n + β b_n` on both edges. -/
theorem flow_cont (hβ0 : 0 < β) (hβ1 : β < 1) (θ bbar : ℝ) (n : ℕ) :
    debt β c0 θ bbar (n + 1) none = debt β c0 θ bbar (n + 1) (some (n + 1)) ∧
      debt β c0 θ bbar n none = surplus β c0 θ bbar n none + β * debt β c0 θ bbar (n + 1) none :=
    by
  refine ⟨by simp [debt, nodeValue], ?_⟩
  have hrec := value_rec (c0 := c0) hβ0 hβ1 n
  have h1 : (1 - β) ≠ 0 := by linarith
  simp only [debt, surplus, nodeValue, price, Option.elim_none]
  rw [hrec]
  field_simp
  ring

/-- Cochrane (2023), eq. (9.8), p. 266, at a settled node (E9.9). -/
theorem flow_settled (hβ1 : β < 1) (θ bbar : ℝ) (n k : ℕ) :
    debt β c0 θ bbar n (some k) =
      surplus β c0 θ bbar n (some k) + β * debt β c0 θ bbar (n + 1) (some k) := by
  have h1 : (1 - β) ≠ 0 := by linarith
  simp only [debt, surplus, nodeValue, price, Option.elim_some, settlePrice]
  field_simp
  ring

/-- Cochrane (2023), eq. (9.12), p. 267, at the continue node (E9.9):
`E_n (P_n / P_{n+1}) = 1 = P*_n/P*_{n+1}`, so
`1/(1 + i_n) = β E_n(P_n/P_{n+1}) = β E_n(P*_n/P*_{n+1})`. -/
theorem rate_target_cont (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (n : ℕ) :
    condE β c0 n 1 (fun x => price β c0 n none / price β c0 (n + 1) x) = 1 := by
  have hm := martingale_inv hβ0 hβ1 hc0 hc1 n
  have hc : 0 < contPrice β c0 n := by unfold contPrice; positivity
  simp only [condE, contProb, Finset.range_one, Finset.prod_singleton, Finset.sum_singleton,
    Finset.range_zero, Finset.prod_empty, one_mul, add_zero, price, Option.elim_none,
    Option.elim_some]
  have : contPrice β c0 n * (settleProb β c0 n / settlePrice β c0 (n + 1) +
      (1 - settleProb β c0 n) / contPrice β c0 (n + 1)) = 1 := by
    rw [hm]
    field_simp
  linear_combination this

/-- Cochrane (2023), eq. (9.12), p. 267, at a settled node (E9.9): the price is constant. -/
theorem rate_target_settled (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (n k : ℕ) : price β c0 n (some k) / price β c0 (n + 1) (some k) = 1 := by
  simp only [price, Option.elim_some, settlePrice]
  have := value_pos hβ0 hβ1 hc0 hc1 k
  have h1 : 0 < 1 - β := by linarith
  exact div_self (by positivity)

/-- Cochrane (2023), §9.3.2, p. 266 (E9.9): the transversality condition at the continue node,
`βᵀ E_n b_{n+T−1} → 0`. -/
theorem tvc_cont (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) (θ bbar : ℝ)
    (n : ℕ) :
    Tendsto (fun T => β ^ T * condE β c0 n T (debt β c0 θ bbar (n + T))) atTop (𝓝 0) := by
  have hd : ∀ T, condE β c0 n T (debt β c0 θ bbar (n + T)) =
      (bbar - θ * (1 / (1 - β))) + θ * condE β c0 n T (nodeValue β c0 (n + T)) := by
    intro T
    rw [← condE_affine]
    unfold debt
    congr 1
    funext x
    ring
  simp_rw [hd]
  have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const
    (bbar - θ * (1 / (1 - β)))
  have h2 := (remainder_tendsto hβ0 hβ1 hc0 hc1 n).const_mul θ
  have := h1.add h2
  simp only [zero_mul, mul_zero, add_zero] at this
  refine this.congr fun T => ?_
  ring

/-- Cochrane (2023), §9.3.2, p. 266 (E9.9): the transversality condition at a settled node. -/
theorem tvc_settled (hβ0 : 0 < β) (hβ1 : β < 1) (θ bbar : ℝ) (n k : ℕ) :
    Tendsto (fun T => β ^ T * debt β c0 θ bbar (n + T) (some k)) atTop (𝓝 0) := by
  have : (fun T => β ^ T * debt β c0 θ bbar (n + T) (some k)) =
      fun T => β ^ T * debt β c0 θ bbar 0 (some k) := by
    funext T
    simp [debt, nodeValue]
  rw [this]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const
    (debt β c0 θ bbar 0 (some k))

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the settled price levels are unbounded (so the
counterexample does not settle whether bounded price levels would restore uniqueness). -/
theorem settlePrice_unbounded (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1) :
    ¬ ∃ M, ∀ k, settlePrice β c0 k ≤ M := by
  rintro ⟨M, hM⟩
  have hK := coefK_pos hβ0 hβ1 hc1
  have hL := coefL_pos hβ0 hβ1 hc0
  have h1 : 0 < 1 - β := by linarith
  have hlim : Tendsto (fun k : ℕ => (1 - β) * coefK β c0 * β⁻¹ ^ k) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt ((one_lt_inv₀ hβ0).mpr hβ1)).const_mul_atTop
      (mul_pos h1 hK)
  obtain ⟨k, hk⟩ := (hlim.eventually_gt_atTop M).exists
  have := hM k
  have hle : (1 - β) * coefK β c0 * β⁻¹ ^ k ≤ settlePrice β c0 k := by
    unfold settlePrice value
    have : 0 ≤ coefL β c0 * β ^ k := by positivity
    nlinarith
  linarith

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): along the unsettled path the price level tends to
zero, so the counterexample's prices are neither bounded above nor bounded away from zero
(consistent with `fr_unique_bounded`). -/
theorem contPrice_tendsto_zero (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun n => contPrice β c0 n) atTop (𝓝 0) := by
  simpa [contPrice] using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul c0

/-- Cochrane (2023), §9.3.2, p. 267 (E9.9): the probability of never settling is zero,
`contProb t j → 0`. -/
theorem contProb_tendsto_zero (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (t : ℕ) : Tendsto (fun j => contProb β c0 t j) atTop (𝓝 0) :=
  squeeze_zero (fun j => (contProb_bounds hβ0 hβ1 hc0 hc1 t j).1)
    (fun j => (contProb_bounds hβ0 hβ1 hc0 hc1 t j).2)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1)

/-- Cochrane (2023), §9.3.2, p. 266 (E9.9): the node visited at date `n` by the path that settles
at date `k`. -/
def pathNode (k n : ℕ) : Option ℕ := if n < k then none else some k

/-- Cochrane (2023), eq. (9.9), p. 266, ex post (E9.9): along every path that settles (at any date
`k`), real debt equals the realised discounted sum of surpluses,
`b_{n−1} = ∑ⱼ βʲ s_{n+j}`, the path satisfying (9.8) and the pathwise transversality condition. -/
theorem valuation_expost (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (θ bbar : ℝ) (k n : ℕ) :
    HasSum (fun j => β ^ j * surplus β c0 θ bbar (n + j) (pathNode k (n + j)))
      (debt β c0 θ bbar n (pathNode k n)) := by
  set b : ℕ → ℝ := fun m => debt β c0 θ bbar m (pathNode k m) with hb
  set sp : ℕ → ℝ := fun m => surplus β c0 θ bbar m (pathNode k m) with hsp
  have hflow : ∀ m, b m = sp m + β * b (m + 1) := by
    intro m
    simp only [hb, hsp, pathNode]
    by_cases h1 : m + 1 < k
    · have h0 : m < k := by omega
      simp only [h0, h1, ↓reduceIte]
      exact (flow_cont hβ0 hβ1 θ bbar m).2
    · by_cases h0 : m < k
      · have hk' : k = m + 1 := by omega
        simp only [h0, h1, ↓reduceIte]
        rw [hk', ← (flow_cont (c0 := c0) hβ0 hβ1 θ bbar m).1]
        exact (flow_cont hβ0 hβ1 θ bbar m).2
      · simp only [h0, h1, ↓reduceIte]
        exact flow_settled hβ1 θ bbar m k
  have htvc : Tendsto (fun T => β ^ T * b (n + T)) atTop (𝓝 0) := by
    have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const
      (debt β c0 θ bbar 0 (some k))
    rw [zero_mul] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop k] with T hT
    have h0 : ¬ (n + T < k) := by omega
    simp only [hb, pathNode, h0, ↓reduceIte, debt, nodeValue, Option.elim_some]
  have hbound : ∀ m, |sp m| ≤ |(1 - β) * bbar| + |θ| * (c0 + settlePrice β c0 k + 1) := by
    intro m
    have hH : 0 < settlePrice β c0 k :=
      mul_pos (by linarith) (value_pos hβ0 hβ1 hc0 hc1 k)
    have hP : 0 ≤ price β c0 m (pathNode k m) ∧
        price β c0 m (pathNode k m) ≤ c0 + settlePrice β c0 k := by
      unfold pathNode
      split_ifs
      · simp only [price, Option.elim_none, contPrice]
        have h1 : β ^ m ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
        constructor
        · positivity
        · nlinarith
      · simp only [price, Option.elim_some]
        constructor <;> linarith
    simp only [hsp, surplus]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg θ)
    rw [abs_le]
    constructor <;> linarith [hP.1, hP.2]
  exact hasSum_of_tvc hflow n htvc (summable_of_bounded hβ0.le hβ1 hbound n)

/-- Cochrane (2023), §9.3.2, p. 267 (**Theorem FR (b)**, error E9.9): the claim "only the sequence
`P_t = P*_t` satisfies both (9.9) and (9.12)" is false under uncertainty. For every `0 < β < 1`,
every initial price level `0 < P_0 = c₀ < 1 = P*_0`, every rule coefficient `θ` and initial real
debt `b̄` (equal to the present value of `s₀ = (1 − β) b̄`), the settle-or-continue tree has
genuine probabilities, satisfies (9.12) at every node, (9.8) on every edge with predetermined real
debt, (9.9) at every node and the transversality condition at every node. -/
theorem sunspot_counterexample (hβ0 : 0 < β) (hβ1 : β < 1) (hc0 : 0 < c0) (hc1 : c0 < 1)
    (θ bbar : ℝ) :
    (∀ n, 0 < settleProb β c0 n ∧ settleProb β c0 n < 1) ∧
    (∀ n, condE β c0 n 1 (fun x => price β c0 n none / price β c0 (n + 1) x) = 1) ∧
    (∀ n k, price β c0 n (some k) / price β c0 (n + 1) (some k) = 1) ∧
    (∀ n, debt β c0 θ bbar (n + 1) none = debt β c0 θ bbar (n + 1) (some (n + 1)) ∧
      debt β c0 θ bbar n none = surplus β c0 θ bbar n none + β * debt β c0 θ bbar (n + 1) none) ∧
    (∀ n k, debt β c0 θ bbar n (some k) =
      surplus β c0 θ bbar n (some k) + β * debt β c0 θ bbar (n + 1) (some k)) ∧
    (∀ n, HasSum (fun j => β ^ j * condE β c0 n j (surplus β c0 θ bbar (n + j)))
      (debt β c0 θ bbar n none)) ∧
    (∀ n k, HasSum (fun j => β ^ j * surplus β c0 θ bbar (n + j) (some k))
      (debt β c0 θ bbar n (some k))) ∧
    (∀ n, Tendsto (fun T => β ^ T * condE β c0 n T (debt β c0 θ bbar (n + T))) atTop (𝓝 0)) ∧
    (∀ n k, Tendsto (fun T => β ^ T * debt β c0 θ bbar (n + T) (some k)) atTop (𝓝 0)) ∧
    HasSum (fun j => β ^ j * ((1 - β) * bbar)) bbar ∧ debt β c0 θ bbar 0 none = bbar ∧
    price β c0 0 none = c0 ∧ price β c0 0 none < 1 := by
  refine ⟨fun n => ?_, rate_target_cont hβ0 hβ1 hc0 hc1, rate_target_settled hβ0 hβ1 hc0 hc1,
    flow_cont hβ0 hβ1 θ bbar, flow_settled hβ1 θ bbar, valuation_cont hβ0 hβ1 hc0 hc1 θ bbar,
    valuation_settled hβ0 hβ1 θ bbar, tvc_cont hβ0 hβ1 hc0 hc1 θ bbar, tvc_settled hβ0 hβ1 θ bbar,
    ?_, ?_, ?_, ?_⟩
  · have := settleProb_bounds hβ0 hβ1 hc0 hc1 n
    exact ⟨by linarith, this.2⟩
  · have h1 : (1 - β) ≠ 0 := by linarith
    have := (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_left ((1 - β) * bbar)
    convert this using 1
    · funext j
      ring
    · field_simp
  · simp [debt, nodeValue, value_zero]
  · simp [price, contPrice]
  · simp [price, contPrice, hc1]

end Sunspot

/-! ### §9.3.3 A better fiscal rule: regular and emergency budgets -/

/-- Cochrane (2023), §9.3.3, p. 269: with the same-date rule `s_{r,t} = s_{0,t} + α_r b_{r,t}` and
`b_{r,t} = R (b_{r,t−1} − s_{r,t})`, the regular debt evolves as
`b_{r,t} = R/(1 + R α_r) · (b_{r,t−1} − s_{0,t})`. -/
theorem regular_solve {R αr br br' sr s0 : ℝ} (hR : 0 < R) (hα : 0 < αr)
    (hrec : br' = R * (br - sr)) (hrule : sr = s0 + αr * br') :
    br' = R / (1 + R * αr) * (br - s0) := by
  have h : 0 < 1 + R * αr := by positivity
  rw [hrule] at hrec
  rw [div_mul_eq_mul_div, eq_div_iff h.ne']
  linear_combination hrec

/-- Cochrane (2023), §9.3.3, p. 269 (checked correct, survey E9.6): with `α_r > 0` and bounded
`s₀`, the regular debt satisfies the transversality condition `βᵀ b_{r,T} → 0` automatically, for
every `α_r > 0`. -/
theorem regular_tvc {β αr M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hα : 0 < αr) {br sr s0 : ℕ → ℝ}
    (hM : ∀ t, |s0 t| ≤ M) (hrec : ∀ t, br (t + 1) = β⁻¹ * (br t - sr t))
    (hrule : ∀ t, sr t = s0 t + αr * br (t + 1)) :
    Tendsto (fun T => β ^ T * br T) atTop (𝓝 0) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set c := β / (β + αr) with hc
  have hcpos : 0 < c := div_pos hβ0 (by linarith)
  have hc1 : c < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hstep : ∀ T, br (T + 1) = (br T - s0 T) / (β + αr) := by
    intro T
    have := regular_solve (inv_pos.mpr hβ0) hα (hrec T) (hrule T)
    rw [this]
    field_simp
  refine InflationTarget.tendsto_zero_of_contraction (c := c) (M := c * M)
    (by rw [abs_of_pos hcpos]; exact hc1) hβ0 hβ1 (mul_nonneg hcpos.le hM0) (fun T => ?_)
  rw [hstep T, hc, pow_succ]
  rw [show β ^ T * β * ((br T - s0 T) / (β + αr)) - β / (β + αr) * (β ^ T * br T) =
      -(β / (β + αr) * (β ^ T * s0 T)) by field_simp; ring, abs_neg, abs_mul, abs_mul,
    abs_of_pos (div_pos hβ0 (by linarith : 0 < β + αr)), abs_of_pos (pow_pos hβ0 T)]
  have hcT : 0 ≤ β / (β + αr) * β ^ T := by positivity
  calc β / (β + αr) * (β ^ T * |s0 T|) = (β / (β + αr) * β ^ T) * |s0 T| := by ring
    _ ≤ (β / (β + αr) * β ^ T) * M := mul_le_mul_of_nonneg_left (hM T) hcT
    _ = _ := by ring

/-- Cochrane (2023), §9.3.3, p. 269: "With `α_r > 0`, the regular surplus repays its debts
automatically, without an extra `a(β) = 0` assumption": `b_{r,t−1} = ∑ⱼ βʲ s_{r,t+j}`. -/
theorem regular_hasSum {β αr M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hα : 0 < αr)
    {br sr s0 : ℕ → ℝ} (hM : ∀ t, |s0 t| ≤ M) (hrec : ∀ t, br (t + 1) = β⁻¹ * (br t - sr t))
    (hrule : ∀ t, sr t = s0 t + αr * br (t + 1)) (t : ℕ) :
    HasSum (fun j => β ^ j * sr (t + j)) (br t) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hflow : ∀ t, br t = sr t + β * br (t + 1) := fun t => by
    rw [hrec t]
    field_simp
    ring
  have hx := regular_tvc hβ0 hβ1 hα hM hrec hrule
  have hβt : (β ^ t)⁻¹ * β ^ t = 1 := inv_mul_cancel₀ (pow_ne_zero t hβ0.ne')
  have htvc : Tendsto (fun T => β ^ T * br (t + T)) atTop (𝓝 0) := by
    have := (hx.comp (tendsto_add_atTop_nat t)).const_mul (β ^ t)⁻¹
    rw [mul_zero] at this
    refine this.congr fun T => ?_
    simp only [Function.comp, pow_add, add_comm T t]
    rw [← mul_assoc, ← mul_assoc, hβt, one_mul]
  -- summability of the regular surplus
  set c := β / (β + αr) with hc
  have hcpos : 0 < c := div_pos hβ0 (by linarith)
  have hc1 : c < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hstep : ∀ T, br (T + 1) = (br T - s0 T) / (β + αr) := by
    intro T
    have := regular_solve (inv_pos.mpr hβ0) hα (hrec T) (hrule T)
    rw [this]
    field_simp
  have hsx : Summable (fun T => β ^ T * br T) := by
    refine InflationTarget.summable_of_contraction (c := c) (M := c * M)
      (by rw [abs_of_pos hcpos]; exact hc1) hβ0 hβ1 (mul_nonneg hcpos.le hM0) (fun T => ?_)
    rw [hstep T, hc, pow_succ]
    rw [show β ^ T * β * ((br T - s0 T) / (β + αr)) - β / (β + αr) * (β ^ T * br T) =
        -(β / (β + αr) * (β ^ T * s0 T)) by field_simp; ring, abs_neg, abs_mul, abs_mul,
      abs_of_pos (div_pos hβ0 (by linarith : 0 < β + αr)), abs_of_pos (pow_pos hβ0 T)]
    have hcT : 0 ≤ β / (β + αr) * β ^ T := by positivity
    calc β / (β + αr) * (β ^ T * |s0 T|) = (β / (β + αr) * β ^ T) * |s0 T| := by ring
      _ ≤ (β / (β + αr) * β ^ T) * M := mul_le_mul_of_nonneg_left (hM T) hcT
      _ = _ := by ring
  have hsb : Summable (fun j => β ^ j * br (t + j + 1)) := by
    have h1 := ((summable_nat_add_iff (t + 1)).mpr hsx).mul_left (β ^ (t + 1))⁻¹
    refine h1.congr fun j => ?_
    rw [show j + (t + 1) = t + j + 1 by ring, show t + j + 1 = (t + 1) + j by ring,
      pow_add β (t + 1) j, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hβ0.ne'),
      one_mul]
  have hsum : Summable (fun j => β ^ j * sr (t + j)) := by
    have := (summable_of_bounded hβ0.le hβ1 hM t).add (hsb.mul_left αr)
    refine this.congr fun j => ?_
    rw [hrule (t + j)]
    ring
  exact hasSum_of_tvc hflow t htvc hsum

/-- Cochrane (2023), eq. (9.14), p. 269: the price-level-stabilisation budget,
`b_{p,t} = R (b_{p,t−1} − s_{p,t})`, `s_{p,t} = θ (P_t − P*_t)`, with its transversality condition,
obeys `b_{p,t−1} = ∑ⱼ βʲ s_{p,t+j} = θ ∑ⱼ βʲ (P_{t+j} − P*_{t+j})`. -/
theorem emergency_hasSum {β θ : ℝ} (hβ0 : 0 < β) {bp sp P Pstar : ℕ → ℝ}
    (hrec : ∀ t, bp (t + 1) = β⁻¹ * (bp t - sp t)) (hrule : ∀ t, sp t = θ * (P t - Pstar t))
    (t : ℕ) (htvc : Tendsto (fun T => β ^ T * bp (t + T)) atTop (𝓝 0))
    (hsum : Summable (fun j => β ^ j * (P (t + j) - Pstar (t + j)))) :
    HasSum (fun j => β ^ j * sp (t + j)) (bp t) ∧
      bp t = θ * ∑' j, β ^ j * (P (t + j) - Pstar (t + j)) := by
  have hflow : ∀ t, bp t = sp t + β * bp (t + 1) := fun t => by
    rw [hrec t]
    field_simp
    ring
  have hs : Summable (fun j => β ^ j * sp (t + j)) := by
    refine (hsum.mul_left θ).congr fun j => ?_
    rw [hrule (t + j)]
    ring
  have h := hasSum_of_tvc hflow t htvc hs
  refine ⟨h, ?_⟩
  rw [← h.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [hrule (t + j)]
  ring

/-- Cochrane (2023), §9.3.3, p. 269 ("we can pair this fiscal policy with a debt target, here
`b_{p,t} = 0`"): with the emergency budget held at zero debt, `b_{p,t} = R(b_{p,t−1} − s_{p,t})`
forces
`s_{p,t} = 0`, hence `P_t = P*_t` (`θ ≠ 0`). -/
theorem emergency_debt_target {β θ : ℝ} (hθ : θ ≠ 0) {bp sp P Pstar : ℕ → ℝ}
    (hrec : ∀ t, bp (t + 1) = β⁻¹ * (bp t - sp t)) (hrule : ∀ t, sp t = θ * (P t - Pstar t))
    (hzero : ∀ t, bp t = 0) (hβ : β ≠ 0) (t : ℕ) : P t = Pstar t := by
  have h := hrec t
  rw [hzero, hzero, zero_sub, hrule t] at h
  have h2 : θ * (P t - Pstar t) = 0 := by
    have := (mul_eq_zero.mp h.symm).resolve_left (inv_ne_zero hβ)
    linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hθ
  · linarith

/-- Cochrane (2023), §9.3.3, p. 269 (lagged-rule variant, survey E9.6): with the lagged rule
`s_{r,t} = s_{0,t} + α_r b_{r,t−1}` and `b_{r,t} = R(b_{r,t−1} − s_{r,t})`, `R = 1/β`, bounded `s₀`
and
`0 < α_r < 2`, the regular debt satisfies `βᵀ b_{r,T} → 0`. -/
theorem lagged_tvc {β αr M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 < αr) (hα2 : αr < 2)
    {br sr s0 : ℕ → ℝ} (hM : ∀ t, |s0 t| ≤ M) (hrec : ∀ t, br (t + 1) = β⁻¹ * (br t - sr t))
    (hrule : ∀ t, sr t = s0 t + αr * br t) :
    Tendsto (fun T => β ^ T * br T) atTop (𝓝 0) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hc : |1 - αr| < 1 := by rw [abs_lt]; constructor <;> linarith
  refine InflationTarget.tendsto_zero_of_contraction (c := 1 - αr) hc hβ0 hβ1 hM0 (fun T => ?_)
  rw [hrec T, hrule T, pow_succ]
  rw [show β ^ T * β * (β⁻¹ * (br T - (s0 T + αr * br T))) - (1 - αr) * (β ^ T * br T) =
      -(β ^ T * s0 T) by field_simp; ring, abs_neg, abs_mul, abs_of_pos (pow_pos hβ0 T)]
  exact mul_le_mul_of_nonneg_left (hM T) (pow_pos hβ0 T).le

/-- Cochrane (2023), §9.3.3, p. 269 (lagged-rule variant): with `s₀ = 0`, `βᵀ b_{r,T} = (1 − α_r)ᵀ
b_{r,0}`,
so for `b_{r,0} ≠ 0` the transversality condition holds iff `0 < α_r < 2` (unlike the book's
same-date rule, which works for every `α_r > 0`). -/
theorem lagged_tvc_iff {β αr : ℝ} (hβ0 : 0 < β) {br sr : ℕ → ℝ}
    (hrec : ∀ t, br (t + 1) = β⁻¹ * (br t - sr t)) (hrule : ∀ t, sr t = 0 + αr * br t)
    (hb : br 0 ≠ 0) :
    Tendsto (fun T => β ^ T * br T) atTop (𝓝 0) ↔ 0 < αr ∧ αr < 2 := by
  have hx : ∀ T, β ^ T * br T = (1 - αr) ^ T * br 0 := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [hrec T, hrule T, pow_succ, pow_succ,
        show (1 - αr) ^ T * (1 - αr) * br 0 = (1 - αr) * ((1 - αr) ^ T * br 0) by ring, ← ih]
      field_simp
      ring
  simp_rw [hx]
  constructor
  · intro h
    by_contra hα
    have hc : 1 ≤ |1 - αr| := by
      rcases not_and_or.mp hα with h1 | h1
      · rw [abs_of_nonneg (by linarith [not_lt.mp h1])]
        linarith [not_lt.mp h1]
      · rw [abs_of_nonpos (by linarith [not_lt.mp h1])]
        linarith [not_lt.mp h1]
    have hlow : ∀ T : ℕ, |br 0| ≤ |(1 - αr) ^ T * br 0| := fun T => by
      rw [abs_mul, abs_pow]
      exact le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ hc)
    have habs := h.abs
    rw [abs_zero] at habs
    exact hb (abs_nonpos_iff.mp (ge_of_tendsto' habs hlow))
  · rintro ⟨h0, h2⟩
    have hc : |1 - αr| < 1 := by rw [abs_lt]; constructor <;> linarith
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hc).mul_const (br 0)

/-- Cochrane (2023), §9.3.3, p. 269 (lagged-rule variant): with `0 < α_r < 2` and bounded `s₀` the
regular debt is repaid, `b_{r,t−1} = ∑ⱼ βʲ s_{r,t+j}`. -/
theorem lagged_hasSum {β αr M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 < αr) (hα2 : αr < 2)
    {br sr s0 : ℕ → ℝ} (hM : ∀ t, |s0 t| ≤ M) (hrec : ∀ t, br (t + 1) = β⁻¹ * (br t - sr t))
    (hrule : ∀ t, sr t = s0 t + αr * br t) (t : ℕ) :
    HasSum (fun j => β ^ j * sr (t + j)) (br t) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hc : |1 - αr| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hflow : ∀ t, br t = sr t + β * br (t + 1) := fun t => by
    rw [hrec t]
    field_simp
    ring
  have hstep : ∀ T, |β ^ (T + 1) * br (T + 1) - (1 - αr) * (β ^ T * br T)| ≤ β ^ T * M := by
    intro T
    rw [hrec T, hrule T, pow_succ]
    rw [show β ^ T * β * (β⁻¹ * (br T - (s0 T + αr * br T))) - (1 - αr) * (β ^ T * br T) =
        -(β ^ T * s0 T) by field_simp; ring, abs_neg, abs_mul, abs_of_pos (pow_pos hβ0 T)]
    exact mul_le_mul_of_nonneg_left (hM T) (pow_pos hβ0 T).le
  have hx := lagged_tvc hβ0 hβ1 hα0 hα2 hM hrec hrule
  have hsx := InflationTarget.summable_of_contraction (x := fun T => β ^ T * br T) hc hβ0 hβ1
    hM0 hstep
  have hβt : (β ^ t)⁻¹ * β ^ t = 1 := inv_mul_cancel₀ (pow_ne_zero t hβ0.ne')
  have htvc : Tendsto (fun T => β ^ T * br (t + T)) atTop (𝓝 0) := by
    have := (hx.comp (tendsto_add_atTop_nat t)).const_mul (β ^ t)⁻¹
    rw [mul_zero] at this
    refine this.congr fun T => ?_
    simp only [Function.comp, pow_add, add_comm T t]
    rw [← mul_assoc, ← mul_assoc, hβt, one_mul]
  have hsb : Summable (fun j => β ^ j * br (t + j)) := by
    have h1 := ((summable_nat_add_iff t).mpr hsx).mul_left (β ^ t)⁻¹
    refine h1.congr fun j => ?_
    rw [show j + t = t + j by ring, pow_add β t j, ← mul_assoc, ← mul_assoc, hβt, one_mul]
  have hsum : Summable (fun j => β ^ j * sr (t + j)) := by
    have := (summable_of_bounded hβ0.le hβ1 hM t).add (hsb.mul_left αr)
    refine this.congr fun j => ?_
    rw [hrule (t + j)]
    ring
  exact hasSum_of_tvc hflow t htvc hsum

/-- Cochrane (2023), §9.3.3, pp. 268–269: the total surplus `s = s_r + s_p` and debt
`b = b_r + b_p` obey the usual flow and valuation `b_{t−1} = ∑ⱼ βʲ s_{t+j}`. -/
theorem total_hasSum {β : ℝ} {br bp sr sp : ℕ → ℝ} {t : ℕ}
    (hr : HasSum (fun j => β ^ j * sr (t + j)) (br t))
    (hp : HasSum (fun j => β ^ j * sp (t + j)) (bp t)) :
    HasSum (fun j => β ^ j * (sr (t + j) + sp (t + j))) (br t + bp t) := by
  have := hr.add hp
  refine this.congr_fun fun j => ?_
  ring

end Cochrane.AssetsRulesBalanceSheets.FiscalRules
