/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite moving averages, covariances and the Kac–Murdock–Szegő kernel

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.3, p. 501, Chapter 24,
§24.1, p. 519, and Online Appendix Chapter 2 (introduction, p. 593): infrastructure for the
claim that "even with completely exogenous surpluses, we expect a positive regression
coefficient of surpluses on debt" (module `SurplusRegression`).

The book's time-series claims are about linear processes driven by serially uncorrelated
unit-variance shocks, `s_t = a(L)ε_t`. We represent such a process by its coefficient vector.
Covariances are computed with an abstract symmetric bilinear "covariance" form `B` on a real
vector space `V` of random variables, for which the shocks `e : ℤ → V` are orthonormal
(`WhiteNoise B e`). Any `L²` model (random variables on a probability space, `B(x, y) = E[xy]`,
with uncorrelated mean-zero unit-variance shocks) is an instance; `finsuppCov`/`finsuppNoise`
give a concrete instance, so the hypotheses are consistent.

## Main definitions

* `WhiteNoise B e`: `B(e_j, e_k) = 1` if `j = k` and `0` otherwise.
* `maProc a N e t = ∑_{k ≤ N} a_k e_{t−k}`: the finite moving average `a(L)e_t`.
* `autocov a N h = ∑_{k ≤ N} a_{k+h} a_k`: the lag-`h` autocovariance of the coefficients.
* `kmsKernel ρ k l = ρ^{|k−l|}`, `kmsForm ρ n x = ∑_{k,l<n} ρ^{|k−l|} x_k x_l` (the
  Kac–Murdock–Szegő quadratic form), `kmsTail ρ n x m = ∑_{k=m}^{n−1} ρ^{k−m} x_k`.

## Main results

* `cov_maProc`: `B(a(L)e_{t+h}, b(L)e_t) = ∑_k a_{k+h} b_k` — covariance is the inner product of
  the (shifted) coefficient vectors; `var_maProc`, `cov_maProc_stationary`.
* `var_maProc_eq_zero_iff`: a finite MA has zero variance iff all its coefficients vanish.
* `kmsForm_eq_ldl`: the LDL factorisation
  `∑_{k,l<n} ρ^{|k−l|} x_k x_l = y_0² + (1 − ρ²) ∑_{1 ≤ m < n} y_m²`, `y_m = ∑_{k ≥ m} ρ^{k−m} x_k`;
  `kmsForm_nonneg` (`ρ² ≤ 1`), `kmsForm_eq_zero_iff`, `kmsForm_pos` (`ρ² < 1`): the kernel
  `ρ^{|k−l|}` is positive semidefinite for `|ρ| ≤ 1` and positive definite for `|ρ| < 1`;
  `kmsMatrix_posDef`: the same as a Mathlib `Matrix.PosDef` statement.
* `kmsTail_succ`: `x_m = y_m − ρ y_{m+1}` (the AR(1) filter inverts the tail sums).
-/

namespace Cochrane.ObservationalEquivalence.MACovariance

open Finset
open scoped Matrix

/-! ### White noise and finite moving averages -/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Cochrane (2023), p. 501 and Online Appendix p. 593 (`s_t = a(L)ε_t` with serially
uncorrelated unit-variance shocks): the shocks `e_k` are orthonormal for the covariance form. -/
def WhiteNoise (B : LinearMap.BilinForm ℝ V) (e : ℤ → V) : Prop :=
  ∀ j k, B (e j) (e k) = if j = k then 1 else 0

/-- Cochrane (2023), Online Appendix p. 593: the finite moving average
`a(L)e_t = ∑_{k=0}^{N} a_k e_{t−k}`. -/
def maProc (a : ℕ → ℝ) (N : ℕ) (e : ℤ → V) (t : ℤ) : V :=
  ∑ k ∈ range (N + 1), a k • e (t - k)

/-- Cochrane (2023), Online Appendix p. 593: the lag-`h` autocovariance of a finite moving
average in terms of its coefficients, `∑_{k ≤ N} a_{k+h} a_k`. -/
def autocov (a : ℕ → ℝ) (N h : ℕ) : ℝ := ∑ k ∈ range (N + 1), a (k + h) * a k

/-- Cochrane (2023), p. 501 (covariances of moving averages): with white-noise shocks,
`B(a(L)e_{t+h}, b(L)e_t) = ∑_{k ≤ N} a_{k+h} b_k`, provided `a` vanishes beyond lag `N` — the
covariance is the inner product of the shifted coefficient vectors. -/
theorem cov_maProc {B : LinearMap.BilinForm ℝ V} {e : ℤ → V} (he : WhiteNoise B e)
    {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (b : ℕ → ℝ) (t : ℤ) (h : ℕ) :
    B (maProc a N e (t + h)) (maProc b N e t) = ∑ l ∈ range (N + 1), a (l + h) * b l := by
  simp only [maProc, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hk : ∀ k : ℕ, (t + (h : ℤ) - k = t - l) ↔ k = l + h := by intro k; omega
  have he' : ∀ j k, B (e j) (e k) = if j = k then 1 else 0 := he
  simp only [he', hk, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with hl
  · ring
  · rw [ha (l + h) (by omega)]; ring

/-- Cochrane (2023), p. 501: the variance of a finite moving average is the sum of its squared
coefficients, `B(a(L)e_t, a(L)e_t) = ∑ a_k²`. -/
theorem var_maProc {B : LinearMap.BilinForm ℝ V} {e : ℤ → V} (he : WhiteNoise B e)
    {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (t : ℤ) :
    B (maProc a N e t) (maProc a N e t) = ∑ l ∈ range (N + 1), a l ^ 2 := by
  have := cov_maProc he ha a t 0
  simp only [Nat.cast_zero, add_zero] at this
  rw [this]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- Cochrane (2023), p. 501 (stationarity): the covariance of a finite moving average with its
`h`-lead is `autocov a N h`, independent of the date `t`. -/
theorem cov_maProc_stationary {B : LinearMap.BilinForm ℝ V} {e : ℤ → V} (he : WhiteNoise B e)
    {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (t : ℤ) (h : ℕ) :
    B (maProc a N e (t + h)) (maProc a N e t) = autocov a N h :=
  cov_maProc he ha a t h

/-- Cochrane (2023), p. 501: a finite moving average has zero variance iff all its coefficients
`a_0, …, a_N` vanish. -/
theorem var_maProc_eq_zero_iff {B : LinearMap.BilinForm ℝ V} {e : ℤ → V} (he : WhiteNoise B e)
    {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (t : ℤ) :
    B (maProc a N e t) (maProc a N e t) = 0 ↔ ∀ k ≤ N, a k = 0 := by
  rw [var_maProc he ha, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  simp only [Finset.mem_range, pow_eq_zero_iff two_ne_zero]
  exact ⟨fun h k hk => h k (by omega), fun h k hk => h k (by omega)⟩

/-! ### A concrete white-noise model -/

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): the coordinate inner product
`B(x, y) = ∑_k x_k y_k` on finitely supported sequences `ℤ →₀ ℝ`. -/
noncomputable def finsuppCov : LinearMap.BilinForm ℝ (ℤ →₀ ℝ) :=
  Finsupp.lsum ℝ fun k => LinearMap.smulRight LinearMap.id (Finsupp.lapply k)

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): the unit vectors of `ℤ →₀ ℝ`. -/
noncomputable def finsuppNoise (k : ℤ) : ℤ →₀ ℝ := Finsupp.single k 1

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): the unit vectors are white noise for
the coordinate inner product, so `WhiteNoise` is satisfiable. -/
theorem finsuppNoise_whiteNoise : WhiteNoise finsuppCov finsuppNoise := by
  intro j k
  simp only [finsuppCov, finsuppNoise, Finsupp.lsum_single, LinearMap.smulRight_apply,
    LinearMap.id_apply, one_smul, Finsupp.lapply_apply, Finsupp.single_apply]
  by_cases h : j = k
  · simp [h]
  · simp [h, Ne.symm h]

/-! ### The Kac–Murdock–Szegő kernel -/

/-- Cochrane (2023), p. 501 (Theorem RG of the survey): the kernel `ρ^{|k−l|}` (with `|k − l|`
written `(k − l) + (l − k)` in truncated natural subtraction). -/
def kmsKernel (ρ : ℝ) (k l : ℕ) : ℝ := ρ ^ (k - l + (l - k))

/-- Cochrane (2023), p. 501: the Kac–Murdock–Szegő quadratic form
`∑_{k,l<n} ρ^{|k−l|} x_k x_l`. -/
def kmsForm (ρ : ℝ) (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range n, ∑ l ∈ range n, kmsKernel ρ k l * x k * x l

/-- Cochrane (2023), p. 501: the tail sums `y_m = ∑_{k=m}^{n−1} ρ^{k−m} x_k`. -/
def kmsTail (ρ : ℝ) (n : ℕ) (x : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ range (n - m), ρ ^ k * x (m + k)

/-- Cochrane (2023), p. 501: the LDL form `y_0² + (1 − ρ²) ∑_{1 ≤ m < n} y_m²`. -/
def kmsLDL (ρ : ℝ) (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ m ∈ range n, (if m = 0 then 1 else 1 - ρ ^ 2) * kmsTail ρ n x m ^ 2

/-- Cochrane (2023), p. 501: the kernel is symmetric. -/
theorem kmsKernel_symm (ρ : ℝ) (k l : ℕ) : kmsKernel ρ k l = kmsKernel ρ l k := by
  unfold kmsKernel; rw [add_comm]

/-- Cochrane (2023), p. 501: the kernel is shift invariant. -/
theorem kmsKernel_succ (ρ : ℝ) (k l : ℕ) : kmsKernel ρ (k + 1) (l + 1) = kmsKernel ρ k l := by
  unfold kmsKernel
  rw [Nat.add_sub_add_right, Nat.add_sub_add_right]

/-- Cochrane (2023), p. 501: the tail sum peels off its first term,
`y_0 = x_0 + ρ y_0(x_{·+1})`. -/
theorem kmsTail_zero_succ (ρ : ℝ) (n : ℕ) (x : ℕ → ℝ) :
    kmsTail ρ (n + 1) x 0 = x 0 + ρ * kmsTail ρ n (fun k => x (k + 1)) 0 := by
  simp only [kmsTail, Nat.sub_zero, zero_add]
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, one_mul, pow_succ]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Cochrane (2023), p. 501: tail sums of the shifted vector,
`y_{m+1}(x) = y_m(x_{·+1})`. -/
theorem kmsTail_shift (ρ : ℝ) (n : ℕ) (x : ℕ → ℝ) (m : ℕ) :
    kmsTail ρ (n + 1) x (m + 1) = kmsTail ρ n (fun k => x (k + 1)) m := by
  simp only [kmsTail, Nat.add_sub_add_right]
  exact Finset.sum_congr rfl fun k _ => by rw [show m + 1 + k = m + k + 1 by omega]

/-- Cochrane (2023), p. 501: the AR(1) filter inverts the tail sums,
`x_m = y_m − ρ y_{m+1}` for `m < n`. -/
theorem kmsTail_succ (ρ : ℝ) {n m : ℕ} (hm : m < n) (x : ℕ → ℝ) :
    kmsTail ρ n x m = x m + ρ * kmsTail ρ n x (m + 1) := by
  simp only [kmsTail]
  obtain ⟨r, hr⟩ : ∃ r, n - m = r + 1 := ⟨n - m - 1, by omega⟩
  rw [hr, show n - (m + 1) = r by omega, Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, one_mul, add_zero]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by
    rw [show m + (k + 1) = m + 1 + k by omega, pow_succ]; ring

/-- Cochrane (2023), p. 501: tail sums vanish from `n` on. -/
theorem kmsTail_of_le (ρ : ℝ) {n m : ℕ} (hm : n ≤ m) (x : ℕ → ℝ) : kmsTail ρ n x m = 0 := by
  simp [kmsTail, Nat.sub_eq_zero_of_le hm]

/-- Cochrane (2023), p. 501: the recursive structure of the quadratic form,
`Q_{n+1}(x) = x_0² + 2ρx_0 y_0(x_{·+1}) + Q_n(x_{·+1})`. -/
theorem kmsForm_succ (ρ : ℝ) (n : ℕ) (x : ℕ → ℝ) :
    kmsForm ρ (n + 1) x = x 0 ^ 2 + 2 * ρ * x 0 * kmsTail ρ n (fun k => x (k + 1)) 0 +
      kmsForm ρ n (fun k => x (k + 1)) := by
  simp only [kmsForm, kmsTail, Nat.sub_zero, zero_add]
  rw [Finset.sum_range_succ']
  simp only [Finset.sum_range_succ', kmsKernel_succ]
  have h0 : ∀ l : ℕ, kmsKernel ρ 0 (l + 1) = ρ ^ (l + 1) := by
    intro l; simp [kmsKernel]
  have h0' : ∀ k : ℕ, kmsKernel ρ (k + 1) 0 = ρ ^ (k + 1) := by
    intro k; simp [kmsKernel]
  have hk00 : kmsKernel ρ 0 0 = 1 := by simp [kmsKernel]
  simp only [h0, h0', hk00, Finset.sum_add_distrib, Finset.mul_sum]
  have e1 : ∑ i ∈ range n, ρ ^ (i + 1) * x 0 * x (i + 1) =
      ∑ i ∈ range n, ρ * x 0 * (ρ ^ i * x (i + 1)) :=
    Finset.sum_congr rfl fun i _ => by rw [pow_succ]; ring
  have e2 : ∑ i ∈ range n, ρ ^ (i + 1) * x (i + 1) * x 0 =
      ∑ i ∈ range n, ρ * x 0 * (ρ ^ i * x (i + 1)) :=
    Finset.sum_congr rfl fun i _ => by rw [pow_succ]; ring
  rw [e1, e2]
  have e3 : ∑ i ∈ range n, 2 * ρ * x 0 * (ρ ^ i * x (i + 1)) =
      2 * ∑ i ∈ range n, ρ * x 0 * (ρ ^ i * x (i + 1)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e3]
  ring

/-- Cochrane (2023), p. 501: the recursive structure of the LDL form,
`L_{n+1}(x) = x_0² + 2ρx_0 y_0(x_{·+1}) + L_n(x_{·+1})`. -/
theorem kmsLDL_succ (ρ : ℝ) (n : ℕ) (x : ℕ → ℝ) :
    kmsLDL ρ (n + 1) x = x 0 ^ 2 + 2 * ρ * x 0 * kmsTail ρ n (fun k => x (k + 1)) 0 +
      kmsLDL ρ n (fun k => x (k + 1)) := by
  set y := fun m => kmsTail ρ n (fun k => x (k + 1)) m with hy
  have hsplit : kmsLDL ρ (n + 1) x =
      ∑ m ∈ range n, (1 - ρ ^ 2) * y m ^ 2 + kmsTail ρ (n + 1) x 0 ^ 2 := by
    simp only [kmsLDL]
    rw [Finset.sum_range_succ']
    simp only [Nat.succ_ne_zero, ↓reduceIte, one_mul, kmsTail_shift, hy]
  have hdiff : ∑ m ∈ range n, (1 - ρ ^ 2) * y m ^ 2 =
      kmsLDL ρ n (fun k => x (k + 1)) - ρ ^ 2 * y 0 ^ 2 := by
    have h1 : kmsLDL ρ n (fun k => x (k + 1)) - ∑ m ∈ range n, (1 - ρ ^ 2) * y m ^ 2 =
        ∑ m ∈ range n, (if m = 0 then ρ ^ 2 else 0) * y m ^ 2 := by
      simp only [kmsLDL, ← Finset.sum_sub_distrib, hy]
      exact Finset.sum_congr rfl fun m _ => by split_ifs <;> ring
    have h2 : ∑ m ∈ range n, (if m = 0 then ρ ^ 2 else 0) * y m ^ 2 = ρ ^ 2 * y 0 ^ 2 := by
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range]
      split_ifs with hn
      · rfl
      · have : y 0 = 0 := kmsTail_of_le ρ (by omega) _
        rw [this]; ring
    linarith
  rw [hsplit, hdiff, kmsTail_zero_succ]
  ring

/-- Cochrane (2023), p. 501 (survey Theorem RG, positive-definiteness of the Kac–Murdock–Szegő
kernel): the LDL factorisation
`∑_{k,l<n} ρ^{|k−l|} x_k x_l = y_0² + (1 − ρ²) ∑_{1 ≤ m < n} y_m²`. -/
theorem kmsForm_eq_ldl (ρ : ℝ) (n : ℕ) (x : ℕ → ℝ) : kmsForm ρ n x = kmsLDL ρ n x := by
  induction n generalizing x with
  | zero => simp [kmsForm, kmsLDL]
  | succ n ih => rw [kmsForm_succ, kmsLDL_succ, ih]

/-- Cochrane (2023), p. 501: for `ρ² ≤ 1` the Kac–Murdock–Szegő form is positive
semidefinite. -/
theorem kmsForm_nonneg {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) (n : ℕ) (x : ℕ → ℝ) : 0 ≤ kmsForm ρ n x := by
  rw [kmsForm_eq_ldl]
  refine Finset.sum_nonneg fun m _ => mul_nonneg ?_ (sq_nonneg _)
  split_ifs <;> linarith

/-- Cochrane (2023), p. 501: for `ρ² < 1` the Kac–Murdock–Szegő form vanishes only at `x = 0`
(on the first `n` coordinates). -/
theorem kmsForm_eq_zero_iff {ρ : ℝ} (hρ : ρ ^ 2 < 1) (n : ℕ) (x : ℕ → ℝ) :
    kmsForm ρ n x = 0 ↔ ∀ k < n, x k = 0 := by
  constructor
  · intro h
    rw [kmsForm_eq_ldl, kmsLDL] at h
    have hcoef : ∀ m, 0 < (if m = 0 then (1 : ℝ) else 1 - ρ ^ 2) := by
      intro m; split_ifs <;> linarith
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun m _ => mul_nonneg (hcoef m).le (sq_nonneg (kmsTail ρ n x m)))).mp h
    have hy : ∀ m, kmsTail ρ n x m = 0 := by
      intro m
      by_cases hm : m < n
      · have := hall m (Finset.mem_range.mpr hm)
        rcases mul_eq_zero.mp this with h1 | h1
        · exact absurd h1 (hcoef m).ne'
        · exact pow_eq_zero_iff two_ne_zero |>.mp h1
      · exact kmsTail_of_le ρ (by omega) x
    intro k hk
    have := kmsTail_succ ρ hk x
    rw [hy k, hy (k + 1)] at this
    linarith
  · intro h
    unfold kmsForm
    refine Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun l _ => ?_
    rw [h k (Finset.mem_range.mp hk)]; ring

/-- Cochrane (2023), p. 501: for `ρ² < 1` the Kac–Murdock–Szegő form is positive definite. -/
theorem kmsForm_pos {ρ : ℝ} (hρ : ρ ^ 2 < 1) {n : ℕ} {x : ℕ → ℝ} (hx : ∃ k < n, x k ≠ 0) :
    0 < kmsForm ρ n x := by
  rcases (kmsForm_nonneg hρ.le n x).lt_or_eq with h | h
  · exact h
  · obtain ⟨k, hk, hxk⟩ := hx
    exact absurd ((kmsForm_eq_zero_iff hρ n x).mp h.symm k hk) hxk

/-- Cochrane (2023), p. 501: the Kac–Murdock–Szegő matrix `(ρ^{|k−l|})_{k,l<n}`. -/
def kmsMatrix (ρ : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun k l => kmsKernel ρ k l

/-- Cochrane (2023), p. 501: the quadratic form of the matrix is the Kac–Murdock–Szegő form of
the extended vector. -/
theorem kmsMatrix_quad (ρ : ℝ) (n : ℕ) (x : Fin n → ℝ) :
    star x ⬝ᵥ (kmsMatrix ρ n *ᵥ x) =
      kmsForm ρ n (fun k => if h : k < n then x ⟨k, h⟩ else 0) := by
  simp only [star_trivial, dotProduct, Matrix.mulVec, kmsMatrix, Matrix.of_apply, kmsForm]
  rw [← Fin.sum_univ_eq_sum_range (fun k => ∑ l ∈ range n,
    kmsKernel ρ k l * (if h : k < n then x ⟨k, h⟩ else 0) *
      (if h : l < n then x ⟨l, h⟩ else 0))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun l => kmsKernel ρ k l *
    (if h : k < n then x ⟨k, h⟩ else 0) * (if h : l < n then x ⟨l, h⟩ else 0)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Fin.is_lt, ↓reduceDIte, Fin.eta]
  ring

/-- Cochrane (2023), p. 501 (survey Theorem RG): for `|ρ| < 1` the Kac–Murdock–Szegő matrix
`(ρ^{|k−l|})` is positive definite. -/
theorem kmsMatrix_posDef {ρ : ℝ} (hρ : |ρ| < 1) (n : ℕ) : (kmsMatrix ρ n).PosDef := by
  have hρ2 : ρ ^ 2 < 1 := by
    have h0 := abs_nonneg ρ
    rw [← sq_abs]; nlinarith
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext k l
    simp [kmsMatrix, Matrix.conjTranspose_apply, kmsKernel_symm]
  · rw [kmsMatrix_quad]
    refine kmsForm_pos hρ2 ?_
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hx (funext hcon)
    exact ⟨i, i.isLt, by simpa using hi⟩

end Cochrane.ObservationalEquivalence.MACovariance
