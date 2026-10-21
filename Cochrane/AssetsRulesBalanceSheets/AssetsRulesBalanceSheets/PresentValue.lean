/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.ForwardSolution

/-!
# Present values, transversality conditions and forward iteration

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 8, §8.1, eqs. (8.1)–(8.2)
(pp. 239–240), and Chapter 9, §9.3.1–9.3.2 (pp. 265–266): the shared valuation machinery used by
the Chapter 8, 9 and 10 modules of this project.

Every valuation equation in these chapters has the same structure: a real value `x_t` obeys the
flow `x_t = s_t + β E_t x_{t+1}`, and iterating forward with a transversality condition gives
`x_t = E_t ∑ βʲ s_{t+j}`. This module proves that step once, in its expected form (for any
`ExpectationSystem`) and in its pathwise (ex post) form, together with the elementary price
uniqueness lemmas used throughout ("`B/P = V` determines `P`").

## Main results

* `epv`, `pv`: the ex post and expected present values (8.1)/(8.2); `pv_eq_forwardSeries`,
  `pv_bounded`.
* `TVC` (the transversality condition `βᵀ E_t x_{t+T} → 0`), `tvc_of_bounded`.
* `tendsto_partialSums_of_tvc`: flow plus TVC at `(t, ω)` gives convergence of the partial sums
  of `∑ βʲ E_t s_{t+j}` to `x_t` (no bound on `s` needed);
  `eq_forwardSeries_of_tvc`, `flow_tvc_iff_pv` (flow + TVC ⇔ `x = pv`), `eq_zero_of_tvc` (the
  homogeneous case: `X_t = β E_t X_{t+1}` plus TVC forces `X = 0`).
* Pathwise: `real_iterate`, `real_flow_tvc_iff`, `hasSum_of_tvc`, `summable_of_bounded`.
* Price uniqueness: `valuation_price_unique` (`B/P = V` with `B, V > 0`),
  `price_unique_of_strictMonoOn` (`b = s(P)` with `s` strictly increasing).
-/

namespace Cochrane.AssetsRulesBalanceSheets.PresentValue

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Present values -/

/-- Cochrane (2023), eq. (8.1), p. 239: the ex post discounted sum `∑_{j ≥ 0} βʲ s_{t+j}`,
state by state. -/
noncomputable def epv (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, β ^ j * s (t + j) ω

/-- Cochrane (2023), eq. (8.2), p. 240: the present value `E_t ∑_{j ≥ 0} βʲ s_{t+j}`. -/
noncomputable def pv (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := 𝔼.E t (epv β s t)

/-- Cochrane (2023), eq. (8.2), p. 240: for bounded surpluses and `0 ≤ β < 1` the expectation
commutes with the sum, `E_t ∑ βʲ s_{t+j} = ∑ βʲ E_t s_{t+j}`. -/
theorem pv_eq_forwardSeries {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (t : ℕ) : pv 𝔼 β s t = 𝔼.forwardSeries β s t := by
  funext ω
  have hb : ∀ k ω', |β ^ k * s (t + k) ω'| ≤ β ^ k * M := fun k ω' => by
    rw [abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (hs (t + k) ω') (pow_nonneg hβ0 k)
  change 𝔼.E t (fun ω' => ∑' k, β ^ k * s (t + k) ω') ω = ∑' k, β ^ k * 𝔼.E t (s (t + k)) ω
  rw [𝔼.E_tsum hβ0 hβ1 hb t ω]
  refine tsum_congr fun k => ?_
  change 𝔼.E t (β ^ k • s (t + k)) ω = _
  rw [map_smul, Pi.smul_apply, smul_eq_mul]

/-- Cochrane (2023), eq. (8.2), p. 240: the present value of bounded surpluses is bounded. -/
theorem pv_bounded {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) : BoundedProc (pv 𝔼 β s) := by
  have h : pv 𝔼 β s = 𝔼.forwardSeries β s := funext (pv_eq_forwardSeries 𝔼 hβ0 hβ1 hs)
  rw [h]
  exact 𝔼.forwardSeries_bounded hβ0 hβ1 hs

/-! ### The transversality condition and forward iteration -/

/-- Cochrane (2023), p. 239 ("iterating forward"; survey E8.2): the transversality condition
`βᵀ E_t x_{t+T} → 0` for a real value process `x`, stated explicitly. -/
def TVC (β : ℝ) (x : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Tendsto (fun T : ℕ => β ^ T * 𝔼.E t (x (t + T)) ω) atTop (𝓝 0)

/-- Cochrane (2023), p. 239: a bounded value process satisfies the transversality condition. -/
theorem tvc_of_bounded {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x : ℕ → Ω → ℝ}
    (hx : BoundedProc x) : TVC 𝔼 β x := by
  obtain ⟨K, hK⟩ := hx
  intro t ω
  refine squeeze_zero_norm (a := fun T => β ^ T * K) (fun T => ?_) ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hK (t + T)) t ω) (pow_nonneg hβ0 T)
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const K

/-- Cochrane (2023), eqs. (8.1)–(8.2), p. 239, and §9.2, p. 264 ("iterating forward"): if
`x_t = s_t + β E_t x_{t+1}` at every date with adapted `s`, and `βᵀ E_t x_{t+T} → 0` at `(t, ω)`,
then the partial sums of `∑ βʲ E_t s_{t+j}` converge to `x_t` at `ω`. No bound on `s` and no sign
of `β` is needed. -/
theorem tendsto_partialSums_of_tvc {β : ℝ} {s x : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted s)
    (hx : ForwardSolution.Solves 𝔼 β s x) (t : ℕ) (ω : Ω)
    (htvc : Tendsto (fun T : ℕ => β ^ T * 𝔼.E t (x (t + T)) ω) atTop (𝓝 0)) :
    Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * 𝔼.E t (s (t + j)) ω) atTop
      (𝓝 (x t ω)) := by
  have h1 : ∀ T, ∑ j ∈ Finset.range T, β ^ j * 𝔼.E t (s (t + j)) ω =
      x t ω - β ^ T * 𝔼.E t (x (t + T)) ω := by
    intro T
    have h := congrFun (ForwardSolution.iterate_A15 𝔼 hsa hx t T) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at h
    linarith
  simp_rw [h1]
  simpa using (tendsto_const_nhds (x := x t ω)).sub htvc

/-- Cochrane (2023), eq. (8.1), p. 239 (iterating forward): a solution of
`x_t = s_t + β E_t x_{t+1}` that satisfies the transversality condition is the forward sum
`∑ βʲ E_t s_{t+j}`. -/
theorem eq_forwardSeries_of_tvc {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s x : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s) (hx : ForwardSolution.Solves 𝔼 β s x)
    (htvc : TVC 𝔼 β x) : x = 𝔼.forwardSeries β s := by
  funext t ω
  exact tendsto_nhds_unique (tendsto_partialSums_of_tvc 𝔼 hsa hx t ω (htvc t ω))
    (𝔼.forwardSeries_summable hβ0 hβ1 hs t ω).hasSum.tendsto_sum_nat

/-- Cochrane (2023), eqs. (8.1)–(8.3), pp. 239–246 (the valuation equation from the flow
condition): for bounded adapted surpluses and `0 ≤ β < 1`, a value process satisfies the flow
`x_t = s_t + β E_t x_{t+1}` and the transversality condition if and only if
`x_t = E_t ∑_{j ≥ 0} βʲ s_{t+j}` at every date. -/
theorem flow_tvc_iff_pv {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s x : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s) :
    (ForwardSolution.Solves 𝔼 β s x ∧ TVC 𝔼 β x) ↔ x = pv 𝔼 β s := by
  have hpv : pv 𝔼 β s = 𝔼.forwardSeries β s := funext (pv_eq_forwardSeries 𝔼 hβ0 hβ1 hs)
  constructor
  · rintro ⟨hx, htvc⟩
    rw [hpv]
    exact eq_forwardSeries_of_tvc 𝔼 hβ0 hβ1 hs hsa hx htvc
  · intro hx
    rw [hx, hpv]
    exact ⟨fun t => 𝔼.forwardSeries_solves hβ0 hβ1 hs hsa t,
      tvc_of_bounded 𝔼 hβ0 hβ1 (𝔼.forwardSeries_bounded hβ0 hβ1 hs)⟩

/-- Cochrane (2023), p. 291 ("to avoid an explosion, a transversality-condition violation, both
sides must be zero"), and §9.2, p. 264: if `X_t = β E_t X_{t+1}` at every date and
`βᵀ E_t X_{t+T} → 0`, then `X_t = 0` at every date. -/
theorem eq_zero_of_tvc {β : ℝ} {X : ℕ → Ω → ℝ} (hX : ∀ t, X t = β • 𝔼.E t (X (t + 1)))
    (htvc : TVC 𝔼 β X) : ∀ t, X t = 0 := by
  have hsol : ForwardSolution.Solves 𝔼 β (fun _ => 0) X := fun t => by
    rw [hX t, add_zero]
  have hua : 𝔼.Adapted (fun _ : ℕ => (0 : Ω → ℝ)) := fun t => map_zero _
  intro t
  funext ω
  have h := tendsto_partialSums_of_tvc 𝔼 hua hsol t ω (htvc t ω)
  simp only [map_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h
  exact (tendsto_nhds_unique tendsto_const_nhds h).symm

/-! ### Pathwise iteration of a real flow -/

/-- Cochrane (2023), p. 239, and eq. (9.8), p. 266, iterated: if `b_t = s_t + β b_{t+1}` at
every date then `b_t = ∑_{j<T} βʲ s_{t+j} + βᵀ b_{t+T}`. -/
theorem real_iterate {β : ℝ} {b s : ℕ → ℝ} (h : ∀ t, b t = s t + β * b (t + 1)) (t T : ℕ) :
    b t = ∑ j ∈ Finset.range T, β ^ j * s (t + j) + β ^ T * b (t + T) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [ih, h (t + T), Finset.sum_range_succ, pow_succ, show t + (T + 1) = t + T + 1 by omega]
    ring

/-- Cochrane (2023), eq. (8.1), p. 239, pathwise and with the transversality condition explicit
(survey E8.2): the real flow `b_{t−1} = s_t + β b_t` at every date together with
`βᵀ b_{t+T−1} → 0` at every date is equivalent to the convergence, at every date, of the partial
sums of `∑_{j ≥ 0} βʲ s_{t+j}` to `b_{t−1}`. No summability, and no sign restriction on `β`, is
needed. -/
theorem real_flow_tvc_iff (β : ℝ) (b s : ℕ → ℝ) :
    ((∀ t, b t = s t + β * b (t + 1)) ∧
      ∀ t, Tendsto (fun T : ℕ => β ^ T * b (t + T)) atTop (𝓝 0)) ↔
    ∀ t, Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * s (t + j)) atTop (𝓝 (b t)) := by
  constructor
  · rintro ⟨h, htvc⟩ t
    have h1 : ∀ T, ∑ j ∈ Finset.range T, β ^ j * s (t + j) = b t - β ^ T * b (t + T) :=
      fun T => by linarith [real_iterate h t T]
    simp_rw [h1]
    simpa using (tendsto_const_nhds (x := b t)).sub (htvc t)
  · intro hlim
    have hflow : ∀ t, b t = s t + β * b (t + 1) := by
      intro t
      have hsplit : ∀ T, ∑ j ∈ Finset.range (T + 1), β ^ j * s (t + j) =
          s t + β * ∑ j ∈ Finset.range T, β ^ j * s (t + 1 + j) := by
        intro T
        rw [Finset.sum_range_succ', Finset.mul_sum]
        simp only [pow_zero, one_mul, add_zero]
        rw [add_comm]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show t + (j + 1) = t + 1 + j by omega, pow_succ]
        ring
      have hA : Tendsto (fun T => ∑ j ∈ Finset.range (T + 1), β ^ j * s (t + j)) atTop
          (𝓝 (b t)) := (hlim t).comp (tendsto_add_atTop_nat 1)
      have hB : Tendsto (fun T => ∑ j ∈ Finset.range (T + 1), β ^ j * s (t + j)) atTop
          (𝓝 (s t + β * b (t + 1))) := by
        simp_rw [hsplit]
        exact tendsto_const_nhds.add ((hlim (t + 1)).const_mul β)
      exact tendsto_nhds_unique hA hB
    refine ⟨hflow, fun t => ?_⟩
    have h1 : ∀ T, β ^ T * b (t + T) = b t - ∑ j ∈ Finset.range T, β ^ j * s (t + j) :=
      fun T => by linarith [real_iterate hflow t T]
    simp_rw [h1]
    simpa using (tendsto_const_nhds (x := b t)).sub (hlim t)

/-- Cochrane (2023), §9.3.2, p. 266 ("iterating forward and imposing the transversality
condition"), and eq. (8.1), p. 239: the flow `b_t = s_t + β b_{t+1}` with `βᵀ b_{t+T} → 0` at
date `t` gives `b_{t−1} = ∑ⱼ βʲ s_{t+j}` (ex post), as a genuine sum when the terms are
summable. -/
theorem hasSum_of_tvc {β : ℝ} {b s : ℕ → ℝ} (h : ∀ t, b t = s t + β * b (t + 1)) (t : ℕ)
    (htvc : Tendsto (fun T => β ^ T * b (t + T)) atTop (𝓝 0))
    (hsum : Summable (fun j => β ^ j * s (t + j))) :
    HasSum (fun j => β ^ j * s (t + j)) (b t) := by
  have hpart : Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * s (t + j)) atTop (𝓝 (b t)) := by
    have heq : (fun T => ∑ j ∈ Finset.range T, β ^ j * s (t + j)) =
        fun T => b t - β ^ T * b (t + T) := by
      funext T
      have := real_iterate h t T
      linarith
    rw [heq]
    simpa using htvc.const_sub (b t)
  have h1 := hsum.hasSum
  rwa [tendsto_nhds_unique h1.tendsto_sum_nat hpart] at h1

/-- Cochrane (2023), §9.3.2, p. 266: for bounded surpluses and `0 ≤ β < 1` the discounted
surpluses are absolutely summable. -/
theorem summable_of_bounded {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → ℝ}
    (hs : ∀ t, |s t| ≤ M) (t : ℕ) : Summable (fun j => β ^ j * s (t + j)) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right M)
    (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 j)]
  exact mul_le_mul_of_nonneg_left (hs (t + j)) (pow_nonneg hβ0 j)

/-! ### Price uniqueness -/

/-- Cochrane (2023), p. 289 (`B_{t−1}/P_t = b_t`) and p. 295 (`N/P_t = E_t ∑ βʲ s_{t+j}`): the
valuation equation `B/P = V` with positive nominal claims `B` and positive real backing `V` has
exactly one positive solution, `P = B/V`. -/
theorem valuation_price_unique {B V : ℝ} (hB : 0 < B) (hV : 0 < V) :
    ∃! P : ℝ, 0 < P ∧ B / P = V := by
  refine ⟨B / V, ⟨div_pos hB hV, ?_⟩, ?_⟩
  · rw [div_div_eq_mul_div, mul_div_assoc, mul_div_cancel₀ V hB.ne']
  · rintro P ⟨hP, h⟩
    rw [eq_div_iff hV.ne', ← h]
    field_simp

/-- Cochrane (2023), §9.3.1, p. 265 (and §10.1.1, p. 289): if the surplus rises with the price
level (`s` strictly increasing on positive prices), `b_{T−1} = s_T(P_T)` has at most one
solution `P_T > 0`. -/
theorem price_unique_of_strictMonoOn {s : ℝ → ℝ} (hs : StrictMonoOn s (Set.Ioi 0))
    {b P₁ P₂ : ℝ} (h₁ : 0 < P₁) (h₂ : 0 < P₂) (e₁ : b = s P₁) (e₂ : b = s P₂) : P₁ = P₂ :=
  hs.injOn h₁ h₂ (e₁.symm.trans e₂)

end Cochrane.AssetsRulesBalanceSheets.PresentValue
