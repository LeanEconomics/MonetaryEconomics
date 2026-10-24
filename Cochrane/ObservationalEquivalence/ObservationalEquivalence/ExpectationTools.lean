/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.ForwardSolution

/-!
# Shared tools: innovations, full information, ex-post present values, flow identities

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.1, p. 495, §22.3,
p. 501 (footnote 1), §22.7, p. 508, and Online Appendix Chapter 2, §2.2–2.3, pp. 604–606.

Objects used by both chains of this project, collected in one place (dedupe pass):

* `innov`: the innovation operator `ΔE_{t+1} = E_{t+1} − E_t` (Cochrane (2023), (22.1), p. 495
  and p. 501, footnote 1), a linear map; `innov_apply`, `innov_of_known`.
* `fullInfo`: the expectation system with full information at every date, `E_t = id`
  (perfect foresight on an arbitrary state space).
* `pvExPost`: the ex-post present value `∑_{j ≥ 0} ρʲ s_{t+1+j}` (p. 495; Online Appendix
  §2.3, p. 606).
* `summable_pow_mul_of_bounded`, `tendsto_pow_mul_of_bounded`: geometric weights on bounded
  sequences (`|ρ| < 1`): the present value converges absolutely and the transversality term
  vanishes.
* `flow_telescope`: iterating a flow identity `ρ v_{t+1} = v_t − y_t` forward, in any real
  vector space (ex post for paths, or for random variables).
* `pv_of_flow`: iterating the flow identity under `E_t` and imposing the transversality
  condition gives the present-value relation (Online Appendix p. 605).
-/

namespace Cochrane.ObservationalEquivalence.ExpectationTools

open Filter Topology

variable {Ω : Type*}

/-! ### Innovations -/

/-- Cochrane (2023), (22.1), p. 495, and p. 501, footnote 1: the innovation operator
`ΔE_{t+1} = E_{t+1} − E_t`. -/
def innov (𝔼 : ExpectationSystem Ω) (t : ℕ) : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) := 𝔼.E (t + 1) - 𝔼.E t

/-- Cochrane (2023), (22.1), p. 495: `ΔE_{t+1} x = E_{t+1} x − E_t x`. -/
theorem innov_apply (𝔼 : ExpectationSystem Ω) (t : ℕ) (x : Ω → ℝ) :
    innov 𝔼 t x = 𝔼.E (t + 1) x - 𝔼.E t x := rfl

/-- Cochrane (2023), (22.1), p. 495: a random variable known at date `t` has no date-`t + 1`
innovation, `ΔE_{t+1} x = 0`. -/
theorem innov_of_known (𝔼 : ExpectationSystem Ω) {t : ℕ} {x : Ω → ℝ} (hx : 𝔼.E t x = x) :
    innov 𝔼 t x = 0 := by
  have h1 : 𝔼.E (t + 1) x = x := by
    rw [← hx]
    exact 𝔼.known (Nat.le_succ t) x
  rw [innov_apply, h1, hx, sub_self]

/-! ### Full information -/

/-- Cochrane (2023), §22.7, p. 508, and Online Appendix p. 602: the expectation system in which
every date has full information about the state, `E_t = id` (perfect foresight on an arbitrary
state space). -/
def fullInfo (Ω : Type*) : ExpectationSystem Ω where
  E := fun _ => LinearMap.id
  const := fun _ _ => rfl
  mono := fun _ _ _ h => h
  tower := fun _ _ => rfl
  known := fun _ _ => rfl

/-- Cochrane (2023), §22.7, p. 508: under full information `E_t x = x`. -/
theorem fullInfo_E (t : ℕ) (x : Ω → ℝ) : (fullInfo Ω).E t x = x := rfl

/-! ### Present values with geometric weights -/

/-- Cochrane (2023), §22.1, p. 495, and Online Appendix §2.3, p. 606: the ex-post present value
`∑_{j ≥ 0} ρʲ s_{t+1+j}`, a random variable. -/
noncomputable def pvExPost (ρ : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, ρ ^ j * s (t + 1 + j) ω

/-- Cochrane (2023), §22.1, p. 495: with `|ρ| < 1` a bounded sequence has an absolutely
summable present value `∑ ρʲ x_j`. -/
theorem summable_pow_mul_of_bounded {ρ K : ℝ} (hρ : |ρ| < 1) {x : ℕ → ℝ}
    (hx : ∀ j, |x j| ≤ K) : Summable (fun j => ρ ^ j * x j) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right K)
    (fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hx j) (pow_nonneg (abs_nonneg ρ) j))

/-- Cochrane (2023), §22.1, p. 495 (bounded debt satisfies the transversality condition): with
`|ρ| < 1`, `ρᵀ x_T → 0` for every bounded sequence `x`. -/
theorem tendsto_pow_mul_of_bounded {ρ K : ℝ} (hρ : |ρ| < 1) {x : ℕ → ℝ}
    (hx : ∀ T, |x T| ≤ K) : Tendsto (fun T => ρ ^ T * x T) atTop (𝓝 0) := by
  refine squeeze_zero_norm (a := fun T => |ρ| ^ T * K) (fun T => ?_) ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hx T) (pow_nonneg (abs_nonneg ρ) T)
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg ρ) hρ).mul_const K

/-! ### Iterating a flow identity -/

/-- Cochrane (2023), §22.1, p. 495, and Online Appendix §2.3, p. 606 (iterating the flow
condition forward): if `ρ v_{t+1} = v_t − y_t` at every date (in any real vector space), then
`v_t = ∑_{j<T} ρʲ y_{t+j} + ρᵀ v_{t+T}`. -/
theorem flow_telescope {M : Type*} [AddCommGroup M] [Module ℝ M] {ρ : ℝ} {v y : ℕ → M}
    (h : ∀ t, ρ • v (t + 1) = v t - y t) (t T : ℕ) :
    v t = ∑ j ∈ Finset.range T, ρ ^ j • y (t + j) + ρ ^ T • v (t + T) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have e : v (t + T) = ρ • v (t + (T + 1)) + y (t + T) := by
      rw [show t + (T + 1) = t + T + 1 by omega, h (t + T)]
      abel
    rw [ih, e, Finset.sum_range_succ, smul_add, smul_smul, ← pow_succ]
    abel

/-- Cochrane (2023), Online Appendix p. 605 ("we derived (2.26) by iterating forward (2.24)"),
and §22.1, p. 495: if `ρv_{t+1} = v_t − y_{t+1}` at every date, `v_t` is known at `t` and
`ρᵀE_t v_{t+T} → 0`, then `v_t = ∑_{j≥0} ρʲ E_t y_{t+1+j}` as the limit of the partial sums. -/
theorem pv_of_flow (𝔼 : ExpectationSystem Ω) {ρ : ℝ} {v y : ℕ → Ω → ℝ}
    (hflow : ∀ t, ρ • v (t + 1) = v t - y (t + 1)) (t : ℕ) (hv : 𝔼.E t (v t) = v t) (w : Ω)
    (hlim : Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) w) atTop (𝓝 0)) :
    Tendsto (fun T => ∑ j ∈ Finset.range T, ρ ^ j * 𝔼.E t (y (t + 1 + j)) w) atTop
      (𝓝 (v t w)) := by
  set F : ℕ → ℝ := fun j => 𝔼.E t (v (t + j)) w with hF
  have hstep : ∀ j, F j = ρ * F (j + 1) + 𝔼.E t (y (t + 1 + j)) w := by
    intro j
    have h := congrArg (fun x => 𝔼.E t x w) (hflow (t + j))
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
    simp only [hF, show t + (j + 1) = t + j + 1 by omega, show t + 1 + j = t + j + 1 by omega]
    linarith
  have hiter : ∀ T, F 0 = ρ ^ T * F T +
      ∑ j ∈ Finset.range T, ρ ^ j * 𝔼.E t (y (t + 1 + j)) w := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [ih, Finset.sum_range_succ, hstep T]
      ring
  have hF0 : F 0 = v t w := by simp [hF, hv]
  have hlim' : Tendsto (fun T => F 0 - ρ ^ T * F T) atTop (𝓝 (F 0 - 0)) :=
    tendsto_const_nhds.sub hlim
  rw [sub_zero, hF0] at hlim'
  refine hlim'.congr fun T => ?_
  rw [← hF0, hiter T]
  ring

end Cochrane.ObservationalEquivalence.ExpectationTools
