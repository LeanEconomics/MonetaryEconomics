/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.Expectations
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Discount rates versus rates of return

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.6, pp. 204–205,
equation (6.14).

One can always discount a one-period payoff by the ex-post return, `1 = E_t[R_{t+1}⁻¹ R_{t+1}]`,
and iterating gives the finite-horizon return-discounted value identity (6.14). Whether the
infinite-horizon version holds is a separate question: the sum and the terminal term need not
converge, even when the stochastic-discount-factor (SDF) present value does.

## Main results

* `one_eq_E_inv_mul`: `1 = E_t[R⁻¹ R]` for a nowhere-zero return.
* `eq_6_14_pathwise`: (6.14) holds state by state, `p_t = Σ_{j=1}^T (Π_{k≤j} R_{t+k}⁻¹) d_{t+j}
  + (Π_{k≤T} R_{t+k}⁻¹) p_{t+T}`, for any price and dividend paths with nonzero values.
* `eq_6_14`: hence its conditional-expectation form for an adapted price.
* `sdf_finite_horizon`, `sdf_finite_horizon_div`: the SDF version (p. 204, display above
  (6.14)) from one-period pricing, by the law of iterated expectations.
* `return_pv_iff_terminal`: if the return-discounted sum converges, the price equals it iff
  the return-discounted terminal term tends to zero (p. 204, "if the sum and terminal value
  converge").
* `linear_discount_factor_prices`: the linear discount factor `R_{t+1}/E_t(R_{t+1}²)` prices
  the return (p. 204).
-/

namespace Cochrane.FiscalConstraints.ReturnDiscounting

open Filter Topology

variable {Ω : Type*}

/-- Cochrane (2023), p. 204: the gross return from `s` to `s + 1`,
`R_{s+1} = (p_{s+1} + d_{s+1})/p_s`. -/
noncomputable def grossReturn (p d : ℕ → Ω → ℝ) (s : ℕ) (ω : Ω) : ℝ :=
  (p (s + 1) ω + d (s + 1) ω) / p s ω

/-- Cochrane (2023), (6.14) p. 204: the return discount factor `Π_{k=1}^j R_{t+k}⁻¹`. -/
noncomputable def returnDiscount (p d : ℕ → Ω → ℝ) (t j : ℕ) (ω : Ω) : ℝ :=
  ∏ k ∈ Finset.range j, (grossReturn p d (t + k) ω)⁻¹

/-- Cochrane (2023), (6.14) p. 204: the return-discounted value of dividends over
`t + 1, …, t + T`. -/
noncomputable def returnPV (p d : ℕ → Ω → ℝ) (t T : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range T, returnDiscount p d t (j + 1) ω * d (t + j + 1) ω

/-- Cochrane (2023), p. 204: `1 = E_t[R_{t+1}⁻¹ R_{t+1}]` for a return that is nowhere zero. -/
theorem one_eq_E_inv_mul (𝔼 : ExpectationSystem Ω) (t : ℕ) {R : Ω → ℝ}
    (hR : ∀ ω, R ω ≠ 0) : 𝔼.E t (fun ω => (R ω)⁻¹ * R ω) = fun _ => 1 := by
  have h : (fun ω => (R ω)⁻¹ * R ω) = fun _ => (1 : ℝ) := by
    funext ω; exact inv_mul_cancel₀ (hR ω)
  rw [h, 𝔼.const]

/-- Cochrane (2023), (6.14) p. 204: one more period of return discounting,
`(Π_{k≤j+1} R⁻¹)(p_{t+j+1} + d_{t+j+1}) = (Π_{k≤j} R⁻¹) p_{t+j}`. -/
theorem returnDiscount_succ_mul {p d : ℕ → Ω → ℝ}
    (hpd : ∀ s ω, p (s + 1) ω + d (s + 1) ω ≠ 0) (t j : ℕ) (ω : Ω) :
    returnDiscount p d t (j + 1) ω * (p (t + j + 1) ω + d (t + j + 1) ω) =
      returnDiscount p d t j ω * p (t + j) ω := by
  unfold returnDiscount
  rw [Finset.prod_range_succ, grossReturn, inv_div, mul_assoc,
    div_mul_cancel₀ _ (hpd (t + j) ω)]

/-- Cochrane (2023), (6.14) p. 204, state by state: for price and dividend paths with
`p_{s+1} + d_{s+1} ≠ 0`,
`p_t = Σ_{j=1}^T (Π_{k=1}^j R_{t+k}⁻¹) d_{t+j} + (Π_{k=1}^T R_{t+k}⁻¹) p_{t+T}`. -/
theorem eq_6_14_pathwise {p d : ℕ → Ω → ℝ}
    (hpd : ∀ s ω, p (s + 1) ω + d (s + 1) ω ≠ 0) (t : ℕ) (ω : Ω) :
    ∀ T, p t ω = returnPV p d t T ω + returnDiscount p d t T ω * p (t + T) ω := by
  intro T
  induction T with
  | zero => simp [returnPV, returnDiscount]
  | succ T ih =>
    rw [ih, returnPV, returnPV, Finset.sum_range_succ, ← returnDiscount_succ_mul hpd t T ω,
      ← add_assoc t T 1]
    ring

/-- Cochrane (2023), (6.14) p. 204: for an adapted price process the identity holds under
`E_t`: `p_t = E_t[Σ_{j=1}^T (Π R⁻¹) d_{t+j} + (Π R⁻¹) p_{t+T}]`. -/
theorem eq_6_14 (𝔼 : ExpectationSystem Ω) {p d : ℕ → Ω → ℝ}
    (hpd : ∀ s ω, p (s + 1) ω + d (s + 1) ω ≠ 0) (hpa : 𝔼.Adapted p) (t T : ℕ) :
    p t = 𝔼.E t (fun ω => returnPV p d t T ω + returnDiscount p d t T ω * p (t + T) ω) := by
  have h : (fun ω => returnPV p d t T ω + returnDiscount p d t T ω * p (t + T) ω) = p t := by
    funext ω; exact (eq_6_14_pathwise hpd t ω T).symm
  rw [h, hpa t]

/-- Cochrane (2023), p. 204 (the SDF present value above (6.14)): if one-period pricing
`Λ_t p_t = E_t[Λ_{t+1}(p_{t+1} + d_{t+1})]` holds at every date, then for every horizon
`Λ_t p_t = E_t[Σ_{j=1}^T Λ_{t+j} d_{t+j} + Λ_{t+T} p_{t+T}]`. -/
theorem sdf_finite_horizon (𝔼 : ExpectationSystem Ω) {p d Λ : ℕ → Ω → ℝ}
    (hpr : ∀ s, Λ s * p s = 𝔼.E s (Λ (s + 1) * (p (s + 1) + d (s + 1)))) (t : ℕ) :
    ∀ T, Λ t * p t = 𝔼.E t (∑ j ∈ Finset.range T, Λ (t + j + 1) * d (t + j + 1) +
      Λ (t + T) * p (t + T)) := by
  intro T
  induction T with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add, add_zero]
    rw [hpr t, 𝔼.E_E_self]
  | succ T ih =>
    rw [ih, Finset.sum_range_succ, map_add, map_add, map_add, hpr (t + T),
      𝔼.tower (Nat.le_add_right t T), ← add_assoc t T 1, mul_add, map_add]
    ring

/-- Cochrane (2023), p. 204: dividing by `Λ_t` (positive and known at `t`, with the pull-out
property), `p_t = E_t[Σ_{j=1}^T (Λ_{t+j}/Λ_t) d_{t+j} + (Λ_{t+T}/Λ_t) p_{t+T}]`. -/
theorem sdf_finite_horizon_div (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut)
    {p d Λ : ℕ → Ω → ℝ} (hΛ : ∀ s ω, Λ s ω ≠ 0)
    (hinv : ∀ s, 𝔼.E s (fun ω => (Λ s ω)⁻¹) = fun ω => (Λ s ω)⁻¹)
    (hpr : ∀ s, Λ s * p s = 𝔼.E s (Λ (s + 1) * (p (s + 1) + d (s + 1)))) (t T : ℕ) :
    p t = 𝔼.E t (fun ω => ∑ j ∈ Finset.range T, Λ (t + j + 1) ω / Λ t ω * d (t + j + 1) ω +
      Λ (t + T) ω / Λ t ω * p (t + T) ω) := by
  have h := congrArg (fun x => (fun ω => (Λ t ω)⁻¹) * x) (sdf_finite_horizon 𝔼 hpr t T)
  rw [← hpo t _ _ (hinv t)] at h
  funext ω
  have hω := congrFun h ω
  simp only [Pi.mul_apply] at hω
  rw [← mul_assoc, inv_mul_cancel₀ (hΛ t ω), one_mul] at hω
  rw [hω]
  refine congrFun (congrArg (𝔼.E t) ?_) ω
  funext ω'
  simp only [Pi.mul_apply, Pi.add_apply, Finset.sum_apply, div_eq_mul_inv]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => by ring
  · ring

/-- Cochrane (2023), p. 204 ("the present value discounted at the ex-post return is correct,
if the sum and terminal value converge"): if the return-discounted dividends are summable with
sum `S`, then the return-discounted terminal value converges to `p_t − S`, and `p_t = S` iff
that terminal value tends to zero. -/
theorem return_pv_iff_terminal {p d : ℕ → Ω → ℝ}
    (hpd : ∀ s ω, p (s + 1) ω + d (s + 1) ω ≠ 0) (t : ℕ) (ω : Ω) {S : ℝ}
    (hS : HasSum (fun j => returnDiscount p d t (j + 1) ω * d (t + j + 1) ω) S) :
    Tendsto (fun T => returnDiscount p d t T ω * p (t + T) ω) atTop (𝓝 (p t ω - S)) ∧
      (p t ω = S ↔
        Tendsto (fun T => returnDiscount p d t T ω * p (t + T) ω) atTop (𝓝 0)) := by
  have hpart : Tendsto (fun T => returnPV p d t T ω) atTop (𝓝 S) := hS.tendsto_sum_nat
  have heq : (fun T => returnDiscount p d t T ω * p (t + T) ω) =
      fun T => p t ω - returnPV p d t T ω := by
    funext T; linarith [eq_6_14_pathwise hpd t ω T]
  have hlim : Tendsto (fun T => returnDiscount p d t T ω * p (t + T) ω) atTop
      (𝓝 (p t ω - S)) := by
    rw [heq]; exact tendsto_const_nhds.sub hpart
  refine ⟨hlim, ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [h, sub_self] at hlim; exact hlim
  · have := tendsto_nhds_unique hlim h
    linarith

/-- Cochrane (2023), p. 204: the linear one-period discount factor
`Λ_{t+1}/Λ_t = R_{t+1}/E_t(R_{t+1}²)` prices the return, `E_t[(R/E_t R²) R] = 1`, when
`E_t R²` is nowhere zero and its reciprocal is known at `t`. -/
theorem linear_discount_factor_prices (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) (t : ℕ)
    (R : Ω → ℝ) (hv : ∀ ω, 𝔼.E t (R * R) ω ≠ 0)
    (hinv : 𝔼.E t (fun ω => (𝔼.E t (R * R) ω)⁻¹) = fun ω => (𝔼.E t (R * R) ω)⁻¹) :
    𝔼.E t (fun ω => (𝔼.E t (R * R) ω)⁻¹ * R ω * R ω) = fun _ => 1 := by
  have h : (fun ω => (𝔼.E t (R * R) ω)⁻¹ * R ω * R ω) =
      (fun ω => (𝔼.E t (R * R) ω)⁻¹) * (R * R) := by
    funext ω; simp only [Pi.mul_apply]; ring
  rw [h, hpo t _ _ hinv]
  funext ω
  simp only [Pi.mul_apply]
  exact inv_mul_cancel₀ (hv ω)

end Cochrane.FiscalConstraints.ReturnDiscounting
