/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.MACovariance
import ObservationalEquivalence.ExpectationTools
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Surpluses on debt: a positive regression coefficient with exogenous surpluses

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.3, p. 501 ("We may easily
see a coefficient `γ > 0` from a fiscal-theory equilibrium"), Chapter 24, §24.1, p. 519 ("a
surplus moving average with `a(ρ) < 1` generates a regression coefficient `γ > 0`"), and Online
Appendix Chapter 2, introduction, p. 593 ("Even with completely exogenous surpluses, we expect a
positive regression coefficient of surpluses on debt").

## Setting

An active-fiscal equilibrium with a constant discount rate and an exogenous surplus: the surplus
is a finite moving average `s_t = a(L)ε_t = ∑_{k ≤ N} a_k ε_{t−k}` of white-noise shocks that are
a martingale difference sequence for the agents' information (`ShockInfo`), and the value of debt
is given by the valuation equation `v_t = E_t ∑_{j≥0} ρ^j s_{t+1+j}` (a genuine `tsum`, with
`|ρ| < 1` and bounded shocks). Covariances are taken with a covariance form `B` for which the
shocks are white noise. The population OLS coefficient of `s_{t+1}` on `v_t` is
`γ̂ = Cov(s_{t+1}, v_t)/Var(v_t)`.

## Main results

* `value_eq_maProc`: `v_t = b(L)ε_t` with `b_m = ∑_j ρ^j a_{m+1+j}`.
* `cov_surplus_value`: `Cov(s_{t+1}, v_t) = ∑_k a_{k+1} b_k`.
* `two_cov_eq_kms` (**Theorem RG** of the survey):
  `2 Cov(s_{t+1}, v_t) = ∑_{k≥1} a_k² + ∑_{k,l≥1} ρ^{|k−l|} a_k a_l`.
* `cov_pos_iff`, `regCoeff_pos_iff`: for `ρ² ≤ 1`, the covariance and the regression coefficient
  are strictly positive iff the surplus is not white noise (`a_k ≠ 0` for some `k ≥ 1`);
  `iid_cov_zero`: white-noise surpluses give `v ≡ 0`.
* `book_claim_aRho_lt_one`: the book's statement (`a(ρ) < 1` with `a_0 = 1` ⇒ `γ̂ > 0`) is true;
  `ma1_aRho_gt_one`, `ma1_regCoeff_pos`: but the hypothesis `a(ρ) < 1` is superfluous — e.g. the
  MA(1) `a = (1, 1)` has `a(ρ) = 1 + ρ > 1` and `γ̂ > 0` (survey **E16**).
* Infinite moving averages with `∑|a_k| < ∞` (`x_k = a_{k+1}`, `b_m = ∑_j ρ^j x_{m+j}`, all sums
  genuine with proved summability: `bInf_bound`, `covInf_summable`, `kmsInf_summable`,
  `sq_summable`, `bInf_sq_summable`): `two_covInf_eq`
  `2 ∑_m x_m b_m = ∑ x_k² + ∑_k ∑_l ρ^{|k−l|} x_k x_l` (finite identity `two_finite_eq` passed to
  the limit by dominated convergence); the infinite Kac–Murdock–Szegő form is positive
  semidefinite (`kmsInf_nonneg`), bounded below by `(1−ρ²)/(1+|ρ|)² ∑ x_k²` (`kmsInf_lower`,
  from `kmsForm_lower`) and positive definite for `|ρ| < 1` (`kmsInf_pos`); `covInf_pos_iff`,
  `regInf_pos_iff`: covariance and regression coefficient are positive iff the surplus is not
  white noise; `cov_trunc_tendsto`: the genuine covariances of the lag-`N` truncations converge
  to `∑_m a_{m+1} b_m`; `ar1_covInf`: the AR(1) case `η²σ²/(1 − ρη)`, `σ² = 1/(1 − η²)`, as a
  corollary.
* `truncSystem`, `clampShock`, `truncCov`, `truncModel_regCoeff_pos`: a model (states = shock
  paths, `E_t` = set future shocks to zero) in which all the hypotheses hold with nonzero
  shocks, so the theorem is not vacuous.
* AR(1) surpluses (an infinite moving average, any `ExpectationSystem`): `ar1_value`
  `v_t = η s_t/(1 − ρη)`, `ar1_cov` `Cov(s_{t+1}, v_t) = η²σ²/(1 − ρη)`, `ar1_regCoeff`
  `γ̂ = 1 − ρη > 0` for every `η ≠ 0` with `|ρη| < 1` — including `η > 0`, where
  `a(ρ) = 1/(1 − ρη) > 1` (`ar1_aRho_gt_one`).
-/

namespace Cochrane.ObservationalEquivalence.SurplusRegression

open Finset Filter Topology Cochrane.ObservationalEquivalence.MACovariance
open Cochrane.ObservationalEquivalence.ExpectationTools (pvExPost)

variable {Ω : Type*}

/-! ### Exogenous moving-average surpluses and the value of debt -/

/-- Cochrane (2023), Online Appendix p. 602 (agents' information): the shocks are a martingale
difference sequence — `E_t ε_k = ε_k` for `k ≤ t` and `E_t ε_k = 0` for `k > t`. -/
def ShockInfo (𝔼 : ExpectationSystem Ω) (ε : ℤ → Ω → ℝ) : Prop :=
  ∀ (t : ℕ) (k : ℤ), 𝔼.E t (ε k) = if k ≤ (t : ℤ) then ε k else 0

/-- Cochrane (2023), p. 501 and Online Appendix p. 593: the exogenous surplus
`s_t = a(L)ε_t`, at the model dates `t ∈ ℕ`. -/
def surplus (a : ℕ → ℝ) (N : ℕ) (ε : ℤ → Ω → ℝ) (t : ℕ) : Ω → ℝ := maProc a N ε (t : ℤ)

/-- Cochrane (2023), p. 501 and eq. (2.22), p. 602: the value of debt from the valuation
equation with a constant discount factor, `v_t = E_t ∑_{j≥0} ρ^j s_{t+1+j}` (the expectation of
the shared ex-post present value `pvExPost`). -/
noncomputable def valueOfDebt (𝔼 : ExpectationSystem Ω) (ρ : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) :
    Ω → ℝ :=
  𝔼.E t (pvExPost ρ s t)

/-- Cochrane (2023), p. 501: the moving-average coefficients of the value of debt,
`b_m = ∑_{j ≥ 0} ρ^j a_{m+1+j}`. -/
def vCoeff (ρ : ℝ) (a : ℕ → ℝ) (N m : ℕ) : ℝ := ∑ j ∈ range (N + 1), ρ ^ j * a (m + 1 + j)

/-- Cochrane (2023), p. 501: the population regression coefficient of `s_{t+1}` on `v_t`,
`Cov(s_{t+1}, v_t)/Var(v_t)`. -/
noncomputable def regCoeff (B : LinearMap.BilinForm ℝ (Ω → ℝ)) (s v : Ω → ℝ) : ℝ :=
  B s v / B v v

/-- Cochrane (2023), Online Appendix p. 593: the surplus is white noise ("iid") when
`a_k = 0` for every `k ≥ 1`. -/
def IsIID (a : ℕ → ℝ) : Prop := ∀ k, 1 ≤ k → a k = 0

/-- Cochrane (2023), p. 519: `a(ρ) = ∑_{k ≤ N} ρ^k a_k`. -/
def aRho (a : ℕ → ℝ) (N : ℕ) (ρ : ℝ) : ℝ := ∑ k ∈ range (N + 1), ρ ^ k * a k

variable {𝔼 : ExpectationSystem Ω}

/-- Cochrane (2023), Online Appendix p. 602: conditional expectations of a moving average keep
the realised shocks and drop the future ones. -/
theorem E_maProc {ε : ℤ → Ω → ℝ} (hε : ShockInfo 𝔼 ε) (a : ℕ → ℝ) (N : ℕ) (τ : ℤ) (t : ℕ)
    (ω : Ω) :
    𝔼.E t (maProc a N ε τ) ω =
      ∑ k ∈ range (N + 1), a k * (if τ - k ≤ (t : ℤ) then ε (τ - k) ω else 0) := by
  have hε' : ∀ k, 𝔼.E t (ε k) = if k ≤ (t : ℤ) then ε k else 0 := hε t
  simp only [maProc, map_sum, map_smul, hε', Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

/-- Cochrane (2023), p. 501: a bounded-shock moving average is bounded by `∑|a_k| M`. -/
theorem abs_maProc_le {ε : ℤ → Ω → ℝ} {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) (a : ℕ → ℝ) (N : ℕ)
    (τ : ℤ) (ω : Ω) : |maProc a N ε τ ω| ≤ (∑ k ∈ range (N + 1), |a k|) * M := by
  simp only [maProc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hM _ ω) (abs_nonneg _)

/-- Cochrane (2023), p. 501 (index bookkeeping): the expected `(t+1+j)`-surplus is the moving
average `∑_m a_{m+1+j} ε_{t−m}` of the realised shocks. -/
theorem shifted_sum {ε : ℤ → Ω → ℝ} {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0)
    (t j : ℕ) (ω : Ω) :
    ∑ k ∈ range (N + 1), a k *
        (if ((t + 1 + j : ℕ) : ℤ) - k ≤ (t : ℤ) then ε (((t + 1 + j : ℕ) : ℤ) - k) ω else 0) =
      ∑ m ∈ range (N + 1), a (m + 1 + j) * ε ((t : ℤ) - m) ω := by
  set g : ℕ → ℝ := fun k => a k *
    (if ((t + 1 + j : ℕ) : ℤ) - k ≤ (t : ℤ) then ε (((t + 1 + j : ℕ) : ℤ) - k) ω else 0) with hg
  have h1 : ∑ k ∈ range (N + 1), g k = ∑ k ∈ range ((j + 1) + (N + 1)), g k := by
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun k hk hk' => ?_
    have : N < k := by
      simp only [Finset.mem_range] at hk hk'; omega
    simp [hg, ha k this]
  rw [h1, Finset.sum_range_add]
  have h2 : ∑ k ∈ range (j + 1), g k = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk' : k < j + 1 := Finset.mem_range.mp hk
    have hc : ¬ (((t + 1 + j : ℕ) : ℤ) - k ≤ (t : ℤ)) := by push_cast; omega
    simp only [hg]
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc), mul_zero]
  rw [h2, zero_add]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hc : ((t + 1 + j : ℕ) : ℤ) - ((j + 1 + m : ℕ) : ℤ) ≤ (t : ℤ) := by push_cast; omega
  have he : ((t + 1 + j : ℕ) : ℤ) - ((j + 1 + m : ℕ) : ℤ) = (t : ℤ) - m := by push_cast; ring
  simp only [hg]
  rw [ite_eq_left_of_eq_true _ _ (eq_true hc), he, show j + 1 + m = m + 1 + j by omega]

/-- Cochrane (2023), p. 501 and eq. (2.22), p. 602: with an exogenous moving-average surplus,
the value of debt from the valuation equation is itself a moving average of the same shocks,
`v_t = b(L)ε_t`, `b_m = ∑_j ρ^j a_{m+1+j}` (the infinite sum is genuine; `|ρ| < 1`, bounded
shocks). -/
theorem value_eq_maProc {ε : ℤ → Ω → ℝ} (hε : ShockInfo 𝔼 ε) {M : ℝ}
    (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ} {N : ℕ}
    (ha : ∀ k, N < k → a k = 0) (t : ℕ) :
    valueOfDebt 𝔼 ρ (surplus a N ε) t = maProc (vCoeff ρ a N) N ε (t : ℤ) := by
  funext ω
  set C : ℝ := (∑ k ∈ range (N + 1), |a k|) * M with hC
  have hbd : ∀ j ω', |ρ ^ j * surplus a N ε (t + 1 + j) ω'| ≤ |ρ| ^ j * C := by
    intro j ω'
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (abs_maProc_le hM a N _ ω') (pow_nonneg (abs_nonneg _) _)
  have hE := 𝔼.E_tsum (abs_nonneg ρ) hρ (f := fun j ω' => ρ ^ j * surplus a N ε (t + 1 + j) ω')
    hbd t ω
  unfold valueOfDebt pvExPost
  rw [hE]
  have hterm : ∀ j, 𝔼.E t (fun ω' => ρ ^ j * surplus a N ε (t + 1 + j) ω') ω =
      ρ ^ j * ∑ m ∈ range (N + 1), a (m + 1 + j) * ε ((t : ℤ) - m) ω := by
    intro j
    have hf : (fun ω' => ρ ^ j * surplus a N ε (t + 1 + j) ω') =
        ρ ^ j • surplus a N ε (t + 1 + j) := rfl
    rw [hf, map_smul, Pi.smul_apply, smul_eq_mul, surplus, E_maProc hε, shifted_sum ha]
  simp only [hterm]
  have hvanish : ∀ j ∉ range (N + 1),
      ρ ^ j * ∑ m ∈ range (N + 1), a (m + 1 + j) * ε ((t : ℤ) - m) ω = 0 := by
    intro j hj
    have hj' : N + 1 ≤ j := by simpa using hj
    rw [Finset.sum_eq_zero fun m _ => by rw [ha (m + 1 + j) (by omega), zero_mul], mul_zero]
  rw [tsum_eq_sum hvanish]
  simp only [maProc, vCoeff, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => by ring

/-! ### The covariance of surpluses with lagged debt -/

/-- Cochrane (2023), p. 501: the value-of-debt coefficients vanish beyond lag `N − 1`. -/
theorem vCoeff_of_le (ρ : ℝ) {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) {m : ℕ}
    (hm : N ≤ m) : vCoeff ρ a N m = 0 :=
  Finset.sum_eq_zero fun j _ => by rw [ha (m + 1 + j) (by omega), mul_zero]

/-- Cochrane (2023), p. 501: the value-of-debt coefficients are the Kac–Murdock–Szegő tail sums
of the lagged surplus coefficients, `b_m = y_m(a_{·+1})`. -/
theorem vCoeff_eq_kmsTail (ρ : ℝ) {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (m : ℕ) :
    vCoeff ρ a N m = kmsTail ρ N (fun k => a (k + 1)) m := by
  unfold vCoeff kmsTail
  dsimp only
  symm
  refine (Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun j hj hj' => ?_).trans
    (Finset.sum_congr rfl fun j _ => by rw [show m + j + 1 = m + 1 + j by omega])
  have : N < m + j + 1 := by simp only [Finset.mem_range] at hj hj'; omega
  rw [ha _ this, mul_zero]

/-- Cochrane (2023), p. 501: `Cov(s_{t+1}, v_t) = ∑_k a_{k+1} b_k` (stationary: independent of
`t`). -/
theorem cov_surplus_value {B : LinearMap.BilinForm ℝ (Ω → ℝ)} {ε : ℤ → Ω → ℝ}
    (hw : WhiteNoise B ε) (hε : ShockInfo 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ}
    (hρ : |ρ| < 1) {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (t : ℕ) :
    B (surplus a N ε (t + 1)) (valueOfDebt 𝔼 ρ (surplus a N ε) t) =
      ∑ k ∈ range (N + 1), a (k + 1) * vCoeff ρ a N k := by
  rw [value_eq_maProc hε hM hρ ha, surplus]
  have := cov_maProc hw ha (vCoeff ρ a N) (t : ℤ) 1
  simpa using this

/-- Cochrane (2023), p. 501: `Var(v_t) = ∑_k b_k²`. -/
theorem var_value {B : LinearMap.BilinForm ℝ (Ω → ℝ)} {ε : ℤ → Ω → ℝ}
    (hw : WhiteNoise B ε) (hε : ShockInfo 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ}
    (hρ : |ρ| < 1) {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (t : ℕ) :
    B (valueOfDebt 𝔼 ρ (surplus a N ε) t) (valueOfDebt 𝔼 ρ (surplus a N ε) t) =
      ∑ k ∈ range (N + 1), vCoeff ρ a N k ^ 2 := by
  rw [value_eq_maProc hε hM hρ ha]
  exact var_maProc hw (fun k hk => vCoeff_of_le ρ ha hk.le) _

/-- Cochrane (2023), p. 501 (algebra of Theorem RG): with `b_m = y_m(a_{·+1})`,
`2 ∑_k a_{k+1} b_k = ∑_{k<N} a_{k+1}² + L_N(a_{·+1})`, the LDL form of the Kac–Murdock–Szegő
kernel. -/
theorem two_sum_eq_ldl (ρ : ℝ) {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) :
    2 * ∑ k ∈ range (N + 1), a (k + 1) * vCoeff ρ a N k =
      ∑ k ∈ range N, a (k + 1) ^ 2 + kmsLDL ρ N (fun k => a (k + 1)) := by
  set x : ℕ → ℝ := fun k => a (k + 1) with hx
  set y : ℕ → ℝ := fun m => kmsTail ρ N x m with hy
  have hb : ∀ m, vCoeff ρ a N m = y m := fun m => vCoeff_eq_kmsTail ρ ha m
  have hyN : y N = 0 := kmsTail_of_le ρ le_rfl x
  have hxy : ∀ m ∈ range N, x m = y m - ρ * y (m + 1) := by
    intro m hm
    have := kmsTail_succ ρ (Finset.mem_range.mp hm) x
    simp only [hy]; linarith
  have hcov : ∑ k ∈ range (N + 1), a (k + 1) * vCoeff ρ a N k = ∑ k ∈ range N, x k * y k := by
    rw [Finset.sum_range_succ, hb N, hyN, mul_zero, add_zero]
    exact Finset.sum_congr rfl fun k _ => by rw [hb k]
  have hsq : ∑ k ∈ range N, a (k + 1) ^ 2 = ∑ k ∈ range N, (y k - ρ * y (k + 1)) ^ 2 :=
    Finset.sum_congr rfl fun k hk => by rw [← hxy k hk]
  have hcross : ∑ k ∈ range N, x k * y k = ∑ k ∈ range N, (y k - ρ * y (k + 1)) * y k :=
    Finset.sum_congr rfl fun k hk => by rw [hxy k hk]
  have hshift : ∑ k ∈ range N, y (k + 1) ^ 2 =
      ∑ m ∈ range N, (if m = 0 then 0 else 1) * y m ^ 2 := by
    have h1 : ∑ m ∈ range (N + 1), (if m = 0 then (0 : ℝ) else 1) * y m ^ 2 =
        ∑ k ∈ range N, y (k + 1) ^ 2 := by
      rw [Finset.sum_range_succ']; simp
    have h2 : ∑ m ∈ range (N + 1), (if m = 0 then (0 : ℝ) else 1) * y m ^ 2 =
        ∑ m ∈ range N, (if m = 0 then 0 else 1) * y m ^ 2 := by
      rw [Finset.sum_range_succ, hyN]; ring
    rw [← h1, h2]
  have hldl : kmsLDL ρ N x = ∑ m ∈ range N, y m ^ 2 -
      ρ ^ 2 * ∑ m ∈ range N, (if m = 0 then 0 else 1) * y m ^ 2 := by
    simp only [kmsLDL, Finset.mul_sum, ← Finset.sum_sub_distrib, hy]
    exact Finset.sum_congr rfl fun m _ => by split_ifs <;> ring
  rw [hcov, hcross, hsq, hldl, ← hshift]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Cochrane (2023), p. 501, §24.1 p. 519 and Online Appendix p. 593 (survey **Theorem RG**):
with an exogenous moving-average surplus and the valuation equation,
`2 Cov(s_{t+1}, v_t) = ∑_{k≥1} a_k² + ∑_{k,l≥1} ρ^{|k−l|} a_k a_l`. -/
theorem two_cov_eq_kms {B : LinearMap.BilinForm ℝ (Ω → ℝ)} {ε : ℤ → Ω → ℝ}
    (hw : WhiteNoise B ε) (hε : ShockInfo 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ}
    (hρ : |ρ| < 1) {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (t : ℕ) :
    2 * B (surplus a N ε (t + 1)) (valueOfDebt 𝔼 ρ (surplus a N ε) t) =
      ∑ k ∈ range N, a (k + 1) ^ 2 + kmsForm ρ N (fun k => a (k + 1)) := by
  rw [cov_surplus_value hw hε hM hρ ha, two_sum_eq_ldl ρ ha, kmsForm_eq_ldl]

/-- Cochrane (2023), p. 501: `∑_{k<N} a_{k+1}² > 0` iff the surplus is not white noise. -/
theorem sum_sq_pos_iff {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) :
    0 < ∑ k ∈ range N, a (k + 1) ^ 2 ↔ ¬ IsIID a := by
  constructor
  · intro h hiid
    rw [Finset.sum_eq_zero fun k _ => by rw [hiid (k + 1) (by omega)]; ring] at h
    exact lt_irrefl 0 h
  · intro h
    unfold IsIID at h
    push Not at h
    obtain ⟨k, hk1, hk⟩ := h
    have hkN : k ≤ N := by
      by_contra hcon; exact hk (ha k (by omega))
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact Finset.sum_pos' (fun _ _ => sq_nonneg _)
      ⟨j, Finset.mem_range.mpr (by omega), by positivity⟩

/-- Cochrane (2023), p. 501, §24.1 p. 519, Online Appendix p. 593 (survey Theorem RG, sign):
for `|ρ| < 1` the covariance of surpluses with lagged debt is strictly positive iff the
exogenous surplus is not white noise. -/
theorem cov_pos_iff {B : LinearMap.BilinForm ℝ (Ω → ℝ)} {ε : ℤ → Ω → ℝ}
    (hw : WhiteNoise B ε) (hε : ShockInfo 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ}
    (hρ : |ρ| < 1) {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (t : ℕ) :
    0 < B (surplus a N ε (t + 1)) (valueOfDebt 𝔼 ρ (surplus a N ε) t) ↔ ¬ IsIID a := by
  have h2 := two_cov_eq_kms hw hε hM hρ ha t
  have hρ2 : ρ ^ 2 ≤ 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg ρ]
  have hk := kmsForm_nonneg hρ2 N (fun k => a (k + 1))
  constructor
  · intro hpos hiid
    have hz : ∑ k ∈ range N, a (k + 1) ^ 2 = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [hiid (k + 1) (by omega)]; ring
    have hkz : kmsForm ρ N (fun k => a (k + 1)) = 0 := by
      unfold kmsForm
      exact Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => by
        change kmsKernel ρ k l * a (k + 1) * a (l + 1) = 0
        rw [hiid (k + 1) (by omega)]; ring
    linarith
  · intro h
    have := (sum_sq_pos_iff ha).mpr h
    linarith

/-- Cochrane (2023), Online Appendix p. 593: with a white-noise surplus the value of debt is
identically zero (nothing is forecastable), so the covariance vanishes. -/
theorem iid_value_zero {ε : ℤ → Ω → ℝ} (hε : ShockInfo 𝔼 ε) {M : ℝ}
    (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ} {N : ℕ}
    (ha : ∀ k, N < k → a k = 0) (hiid : IsIID a) (t : ℕ) :
    valueOfDebt 𝔼 ρ (surplus a N ε) t = 0 := by
  rw [value_eq_maProc hε hM hρ ha]
  have hb : ∀ m, vCoeff ρ a N m = 0 := fun m =>
    Finset.sum_eq_zero fun j _ => by rw [hiid (m + 1 + j) (by omega), mul_zero]
  simp [maProc, hb]

/-- Cochrane (2023), Online Appendix p. 593: with a white-noise surplus the covariance of
surpluses with lagged debt is zero. -/
theorem iid_cov_zero {B : LinearMap.BilinForm ℝ (Ω → ℝ)} {ε : ℤ → Ω → ℝ}
    (hε : ShockInfo 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ} (hρ : |ρ| < 1)
    {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (hiid : IsIID a) (t : ℕ) :
    B (surplus a N ε (t + 1)) (valueOfDebt 𝔼 ρ (surplus a N ε) t) = 0 := by
  rw [iid_value_zero hε hM hρ ha hiid, map_zero]

/-- Cochrane (2023), p. 501, §24.1 p. 519, Online Appendix p. 593 (survey Theorem RG): the
population regression coefficient `γ̂` of `s_{t+1}` on `v_t` is strictly positive iff the
exogenous surplus is not white noise — "even with completely exogenous surpluses, we expect a
positive regression coefficient of surpluses on debt". -/
theorem regCoeff_pos_iff {B : LinearMap.BilinForm ℝ (Ω → ℝ)} {ε : ℤ → Ω → ℝ}
    (hw : WhiteNoise B ε) (hε : ShockInfo 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ}
    (hρ : |ρ| < 1) {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (t : ℕ) :
    0 < regCoeff B (surplus a N ε (t + 1)) (valueOfDebt 𝔼 ρ (surplus a N ε) t) ↔
      ¬ IsIID a := by
  rw [← cov_pos_iff hw hε hM hρ ha t]
  unfold regCoeff
  constructor
  · intro h
    rcases lt_or_ge 0 (B (surplus a N ε (t + 1)) (valueOfDebt 𝔼 ρ (surplus a N ε) t))
      with hc | hc
    · exact hc
    · have hv : 0 ≤ B (valueOfDebt 𝔼 ρ (surplus a N ε) t)
          (valueOfDebt 𝔼 ρ (surplus a N ε) t) := by
        rw [var_value hw hε hM hρ ha]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
      have := div_nonpos_of_nonpos_of_nonneg hc hv
      linarith
  · intro hc
    refine div_pos hc ?_
    rw [var_value hw hε hM hρ ha]
    rcases (Finset.sum_nonneg fun k (_ : k ∈ range (N + 1)) =>
      sq_nonneg (vCoeff ρ a N k)).lt_or_eq with hv | hv
    · exact hv
    · exfalso
      have hz := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg (vCoeff ρ a N k)).mp
        hv.symm
      rw [cov_surplus_value hw hε hM hρ ha,
        Finset.sum_eq_zero fun k hk => by rw [pow_eq_zero_iff two_ne_zero |>.mp (hz k hk),
          mul_zero]] at hc
      exact lt_irrefl 0 hc

/-! ### The book's sufficient condition `a(ρ) < 1` and survey E16 -/

/-- Cochrane (2023), §24.1, p. 519 ("a surplus moving average with `a(ρ) < 1` generates a
regression coefficient `γ > 0`"), normalising `a_0 = 1`: true, because `a(ρ) < 1 = a_0` forces the
surplus not to be white noise. -/
theorem book_claim_aRho_lt_one {B : LinearMap.BilinForm ℝ (Ω → ℝ)} {ε : ℤ → Ω → ℝ}
    (hw : WhiteNoise B ε) (hε : ShockInfo 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ}
    (hρ : |ρ| < 1) {a : ℕ → ℝ} {N : ℕ} (ha : ∀ k, N < k → a k = 0) (ha0 : a 0 = 1)
    (haρ : aRho a N ρ < 1) (t : ℕ) :
    0 < regCoeff B (surplus a N ε (t + 1)) (valueOfDebt 𝔼 ρ (surplus a N ε) t) := by
  rw [regCoeff_pos_iff hw hε hM hρ ha]
  intro hiid
  have : aRho a N ρ = 1 := by
    unfold aRho
    rw [Finset.sum_range_succ', Finset.sum_eq_zero fun k _ => by
      rw [hiid (k + 1) (by omega), mul_zero]]
    simp [ha0]
  linarith

/-- Cochrane (2023), §24.1, p. 519 (survey E16): the MA(1) surplus `s_t = ε_t + ε_{t−1}`. -/
def ma1Coeff (k : ℕ) : ℝ := if k ≤ 1 then 1 else 0

/-- Cochrane (2023), §24.1, p. 519 (survey E16): the MA(1) `a = (1, 1)` has `a(ρ) = 1 + ρ > 1`
for `ρ > 0`. -/
theorem ma1_aRho_gt_one {ρ : ℝ} (hρ : 0 < ρ) : 1 < aRho ma1Coeff 1 ρ := by
  simp [aRho, ma1Coeff, Finset.sum_range_succ]
  linarith

/-- Cochrane (2023), §24.1, p. 519 (survey E16): nevertheless the MA(1) `a = (1, 1)` produces a
strictly positive regression coefficient of surpluses on debt, so the book's hypothesis
`a(ρ) < 1` is superfluous: every non-white-noise exogenous surplus does (`regCoeff_pos_iff`). -/
theorem ma1_regCoeff_pos {B : LinearMap.BilinForm ℝ (Ω → ℝ)} {ε : ℤ → Ω → ℝ}
    (hw : WhiteNoise B ε) (hε : ShockInfo 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ}
    (hρ : |ρ| < 1) (t : ℕ) :
    0 < regCoeff B (surplus ma1Coeff 1 ε (t + 1)) (valueOfDebt 𝔼 ρ (surplus ma1Coeff 1 ε) t) := by
  rw [regCoeff_pos_iff hw hε hM hρ (fun k hk => by simp [ma1Coeff]; omega)]
  intro hiid
  have := hiid 1 le_rfl
  simp [ma1Coeff] at this

/-! ### AR(1) surpluses -/

/-- Cochrane (2023), Online Appendix p. 604: with an AR(1) surplus `E_t s_{t+1} = ηs_t`
(any `ExpectationSystem`, bounded `s`, `|ρ| < 1`, `|ρη| < 1`), the valuation equation gives
`v_t = E_t ∑ ρ^j s_{t+1+j} = η s_t/(1 − ρη)`. -/
theorem ar1_value {η ρ M : ℝ} {s : ℕ → Ω → ℝ} (hs : 𝔼.IsAR1 η s) (hM : ∀ t ω, |s t ω| ≤ M)
    (hρ : |ρ| < 1) (hρη : |ρ * η| < 1) (t : ℕ) :
    valueOfDebt 𝔼 ρ s t = (η / (1 - ρ * η)) • s t := by
  funext ω
  have hbd : ∀ j ω', |ρ ^ j * s (t + 1 + j) ω'| ≤ |ρ| ^ j * M := by
    intro j ω'
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hM _ ω') (pow_nonneg (abs_nonneg _) _)
  have hE := 𝔼.E_tsum (abs_nonneg ρ) hρ (f := fun j ω' => ρ ^ j * s (t + 1 + j) ω') hbd t ω
  unfold valueOfDebt pvExPost
  rw [hE]
  have hterm : ∀ j, 𝔼.E t (fun ω' => ρ ^ j * s (t + 1 + j) ω') ω =
      η * s t ω * (ρ * η) ^ j := by
    intro j
    have hf : (fun ω' => ρ ^ j * s (t + 1 + j) ω') = ρ ^ j • s (t + (j + 1)) := by
      funext ω'; simp only [Pi.smul_apply, smul_eq_mul]; rw [show t + 1 + j = t + (j + 1) by omega]
    rw [hf, map_smul, 𝔼.ar1_iterate hs, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_pow, pow_succ]
    ring
  simp only [hterm]
  rw [tsum_mul_left, tsum_geometric_of_abs_lt_one hρη, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- Cochrane (2023), p. 501 and Online Appendix p. 604: with an AR(1) surplus whose innovation
`s_{t+1} − ηs_t` is uncorrelated with `s_t` and with `Var(s_t) = σ²`,
`Cov(s_{t+1}, v_t) = η²σ²/(1 − ρη)`. -/
theorem ar1_cov {B : LinearMap.BilinForm ℝ (Ω → ℝ)} {η ρ M σ2 : ℝ} {s : ℕ → Ω → ℝ}
    (hs : 𝔼.IsAR1 η s) (hM : ∀ t ω, |s t ω| ≤ M) (hρ : |ρ| < 1) (hρη : |ρ * η| < 1) (t : ℕ)
    (hinn : B (s (t + 1) - η • s t) (s t) = 0) (hvar : B (s t) (s t) = σ2) :
    B (s (t + 1)) (valueOfDebt 𝔼 ρ s t) = η ^ 2 * σ2 / (1 - ρ * η) := by
  rw [ar1_value hs hM hρ hρη, map_smul, smul_eq_mul]
  have h1 : B (s (t + 1)) (s t) = η * σ2 := by
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hvar] at hinn
    linarith
  rw [h1]
  ring

/-- Cochrane (2023), p. 501, §24.1 p. 519 and Online Appendix p. 604: with an AR(1) surplus the
regression coefficient of `s_{t+1}` on `v_t` is exactly `γ̂ = 1 − ρη`, strictly positive whenever
`|ρη| < 1` (and `η ≠ 0`, `σ² > 0`, so that the regression is defined). -/
theorem ar1_regCoeff {B : LinearMap.BilinForm ℝ (Ω → ℝ)} {η ρ M σ2 : ℝ} {s : ℕ → Ω → ℝ}
    (hs : 𝔼.IsAR1 η s) (hM : ∀ t ω, |s t ω| ≤ M) (hρ : |ρ| < 1) (hρη : |ρ * η| < 1) (t : ℕ)
    (hinn : B (s (t + 1) - η • s t) (s t) = 0) (hvar : B (s t) (s t) = σ2) (hη : η ≠ 0)
    (hσ : 0 < σ2) :
    regCoeff B (s (t + 1)) (valueOfDebt 𝔼 ρ s t) = 1 - ρ * η ∧ 0 < 1 - ρ * η := by
  have hpos : 0 < 1 - ρ * η := by have := (abs_lt.mp hρη).2; linarith
  refine ⟨?_, hpos⟩
  unfold regCoeff
  rw [ar1_cov hs hM hρ hρη t hinn hvar, ar1_value hs hM hρ hρη]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hvar]
  field_simp

/-- Cochrane (2023), §24.1, p. 519 and Online Appendix p. 604 (survey E16): the AR(1) has
`a(ρ) = ∑ ρ^j η^j = 1/(1 − ρη)`, which exceeds one when `0 < ρη < 1`; yet `γ̂ = 1 − ρη > 0`
(`ar1_regCoeff`). -/
theorem ar1_aRho_gt_one {η ρ : ℝ} (h0 : 0 < ρ * η) (h1 : ρ * η < 1) :
    HasSum (fun j : ℕ => ρ ^ j * η ^ j) (1 / (1 - ρ * η)) ∧ 1 < 1 / (1 - ρ * η) := by
  refine ⟨?_, ?_⟩
  · have := hasSum_geometric_of_lt_one h0.le h1
    rw [one_div]
    simpa [mul_pow] using this
  · rw [lt_div_iff₀ (by linarith)]; linarith

/-! ### Infinite moving averages with absolutely summable coefficients -/

/-- Cochrane (2023), p. 501 (infinite moving averages): the truncation `x_k 1{k < N}`. -/
def truncSeq (x : ℕ → ℝ) (N : ℕ) (k : ℕ) : ℝ := if k < N then x k else 0

/-- Cochrane (2023), p. 501: the value-of-debt coefficients of an infinite moving average, with
`x_k = a_{k+1}`: `b_m = ∑_{j ≥ 0} ρ^j x_{m+j} = ∑_j ρ^j a_{m+1+j}`. -/
noncomputable def bInf (ρ : ℝ) (x : ℕ → ℝ) (m : ℕ) : ℝ := ∑' j, ρ ^ j * x (m + j)

/-- Cochrane (2023), p. 501: the covariance of surpluses with lagged debt in coefficient form,
`Cov(s_{t+1}, v_t) = ∑_m a_{m+1} b_m` (here `x_m = a_{m+1}`). -/
noncomputable def covInf (ρ : ℝ) (x : ℕ → ℝ) : ℝ := ∑' m, x m * bInf ρ x m

/-- Cochrane (2023), p. 501: the infinite Kac–Murdock–Szegő form
`∑_k ∑_l ρ^{|k−l|} x_k x_l` (an iterated genuine sum). -/
noncomputable def kmsInf (ρ : ℝ) (x : ℕ → ℝ) : ℝ := ∑' k, ∑' l, kmsKernel ρ k l * x k * x l

/-- Cochrane (2023), p. 501: `|ρ^{|k−l|}| ≤ 1` for `|ρ| ≤ 1`. -/
theorem abs_kmsKernel_le {ρ : ℝ} (hρ : |ρ| ≤ 1) (k l : ℕ) : |kmsKernel ρ k l| ≤ 1 := by
  unfold kmsKernel; rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hρ

/-- Cochrane (2023), p. 501 (tool): a series dominated by a summable sequence is summable and
`|∑ f| ≤ ∑ g`. -/
theorem abs_tsum_le_of_le {f g : ℕ → ℝ} (hg : Summable g) (h : ∀ k, |f k| ≤ g k) :
    Summable f ∧ |∑' k, f k| ≤ ∑' k, g k := by
  have hfa : Summable fun k => |f k| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) h hg
  refine ⟨hfa.of_abs, ?_⟩
  have hn := norm_tsum_le_tsum_norm (f := f) (by simpa only [Real.norm_eq_abs] using hfa)
  simp only [Real.norm_eq_abs] at hn
  exact hn.trans (Summable.tsum_le_tsum h hfa hg)

/-- Cochrane (2023), p. 501 (tool): tails of an absolutely summable sequence are absolutely
summable and bounded by the full sum. -/
theorem tail_abs {x : ℕ → ℝ} (hx : Summable fun k => |x k|) (m : ℕ) :
    Summable (fun j => |x (m + j)|) ∧ ∑' j, |x (m + j)| ≤ ∑' k, |x k| := by
  have hs : Summable (fun j => |x (j + m)|) := (summable_nat_add_iff m).mpr hx
  have e : (fun j => |x (m + j)|) = fun j => |x (j + m)| := by
    funext j; rw [add_comm]
  rw [e]
  refine ⟨hs, ?_⟩
  rw [← hx.sum_add_tsum_nat_add m]
  have : 0 ≤ ∑ i ∈ range m, |x i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  linarith

/-- Cochrane (2023), p. 501 (tool): `|x_k| ≤ ∑ |x|`. -/
theorem abs_le_tsum_abs {x : ℕ → ℝ} (hx : Summable fun k => |x k|) (k : ℕ) :
    |x k| ≤ ∑' k, |x k| :=
  hx.le_tsum k fun _ _ => abs_nonneg _

/-- Cochrane (2023), p. 501 (tool): truncation is dominated, `|x_k 1{k<N}| ≤ |x_k|`. -/
theorem abs_truncSeq_le (x : ℕ → ℝ) (N k : ℕ) : |truncSeq x N k| ≤ |x k| := by
  unfold truncSeq; split_ifs <;> simp

/-- Cochrane (2023), p. 501 (tool): truncations converge pointwise. -/
theorem tendsto_truncSeq (x : ℕ → ℝ) (k : ℕ) :
    Tendsto (fun N => truncSeq x N k) atTop (𝓝 (x k)) :=
  tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨k + 1, fun N hN => by
    simp [truncSeq, show k < N by omega]⟩)

/-- Cochrane (2023), p. 501: for any `y` dominated by an absolutely summable `x` and
`|ρ| ≤ 1`, `b_m(y)` is a genuine sum and `|b_m(y)| ≤ ∑_j |x_{m+j}| ≤ ∑ |x|`. -/
theorem bInf_bound {ρ : ℝ} (hρ : |ρ| ≤ 1) {x y : ℕ → ℝ} (hx : Summable fun k => |x k|)
    (hy : ∀ k, |y k| ≤ |x k|) (m : ℕ) :
    Summable (fun j => ρ ^ j * y (m + j)) ∧ |bInf ρ y m| ≤ ∑' k, |x k| := by
  obtain ⟨hs, hle⟩ := tail_abs hx m
  have hb : ∀ j, |ρ ^ j * y (m + j)| ≤ |x (m + j)| := by
    intro j
    rw [abs_mul, abs_pow]
    calc |ρ| ^ j * |y (m + j)| ≤ 1 * |x (m + j)| :=
          mul_le_mul (pow_le_one₀ (abs_nonneg _) hρ) (hy _) (abs_nonneg _) zero_le_one
      _ = |x (m + j)| := one_mul _
  obtain ⟨h1, h2⟩ := abs_tsum_le_of_le hs hb
  exact ⟨h1, h2.trans hle⟩

/-- Cochrane (2023), p. 501: the terms of `covInf` are absolutely summable (a genuine sum). -/
theorem covInf_summable {ρ : ℝ} (hρ : |ρ| ≤ 1) {x : ℕ → ℝ} (hx : Summable fun k => |x k|) :
    Summable (fun m => x m * bInf ρ x m) := by
  refine (abs_tsum_le_of_le (hx.mul_right (∑' k, |x k|)) fun m => ?_).1
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (bInf_bound hρ hx (fun _ => le_rfl) m).2 (abs_nonneg _)

/-- Cochrane (2023), p. 501: the inner and outer sums of `kmsInf` are absolutely summable. -/
theorem kmsInf_summable {ρ : ℝ} (hρ : |ρ| ≤ 1) {x : ℕ → ℝ} (hx : Summable fun k => |x k|) :
    (∀ k, Summable (fun l => kmsKernel ρ k l * x k * x l)) ∧
      Summable (fun k => ∑' l, kmsKernel ρ k l * x k * x l) := by
  have hin : ∀ k l, |kmsKernel ρ k l * x k * x l| ≤ |x k| * |x l| := by
    intro k l
    rw [abs_mul, abs_mul]
    have := abs_kmsKernel_le hρ k l
    have h1 : |kmsKernel ρ k l| * |x k| ≤ 1 * |x k| :=
      mul_le_mul_of_nonneg_right this (abs_nonneg _)
    nlinarith [abs_nonneg (x l), abs_nonneg (x k)]
  refine ⟨fun k => (abs_tsum_le_of_le (hx.mul_left |x k|) (hin k)).1, ?_⟩
  refine (abs_tsum_le_of_le (hx.mul_right (∑' k, |x k|)) fun k => ?_).1
  have := (abs_tsum_le_of_le (hx.mul_left |x k|) (hin k)).2
  rwa [tsum_mul_left] at this

/-- Cochrane (2023), p. 501: `∑ x_k²` is a genuine sum for absolutely summable `x`. -/
theorem sq_summable {x : ℕ → ℝ} (hx : Summable fun k => |x k|) : Summable (fun k => x k ^ 2) :=
  (abs_tsum_le_of_le (hx.mul_left (∑' k, |x k|)) fun k => by
    rw [abs_pow, sq]
    exact mul_le_mul_of_nonneg_right (abs_le_tsum_abs hx k) (abs_nonneg _)).1

/-! #### Truncations: the finite identities -/

/-- Cochrane (2023), p. 501: for the truncation, `b_m = y_m`, the Kac–Murdock–Szegő tail sum. -/
theorem bInf_trunc (ρ : ℝ) (x : ℕ → ℝ) (N m : ℕ) :
    bInf ρ (truncSeq x N) m = kmsTail ρ N x m := by
  unfold bInf kmsTail
  rw [tsum_eq_sum (s := range (N - m)) fun j hj => by
    have : ¬ m + j < N := by simp only [Finset.mem_range] at hj; omega
    simp [truncSeq, this]]
  refine Finset.sum_congr rfl fun j hj => ?_
  have : m + j < N := by simp only [Finset.mem_range] at hj; omega
  simp [truncSeq, this]

/-- Cochrane (2023), p. 501: `covInf` of the truncation is the finite covariance
`∑_{k<N} x_k y_k`. -/
theorem covInf_trunc (ρ : ℝ) (x : ℕ → ℝ) (N : ℕ) :
    covInf ρ (truncSeq x N) = ∑ k ∈ range N, x k * kmsTail ρ N x k := by
  unfold covInf
  rw [tsum_eq_sum (s := range N) fun k hk => by
    have : ¬ k < N := by simpa using hk
    simp [truncSeq, this]]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [bInf_trunc]
  simp [truncSeq, Finset.mem_range.mp hk]

/-- Cochrane (2023), p. 501: `∑ x_k²` of the truncation. -/
theorem sq_trunc (x : ℕ → ℝ) (N : ℕ) :
    ∑' k, truncSeq x N k ^ 2 = ∑ k ∈ range N, x k ^ 2 := by
  rw [tsum_eq_sum (s := range N) fun k hk => by
    have : ¬ k < N := by simpa using hk
    simp [truncSeq, this]]
  exact Finset.sum_congr rfl fun k hk => by simp [truncSeq, Finset.mem_range.mp hk]

/-- Cochrane (2023), p. 501: `kmsInf` of the truncation is the finite form `kmsForm`. -/
theorem kmsInf_trunc (ρ : ℝ) (x : ℕ → ℝ) (N : ℕ) :
    kmsInf ρ (truncSeq x N) = kmsForm ρ N x := by
  unfold kmsInf kmsForm
  rw [tsum_eq_sum (s := range N) fun k hk => by
    have : ¬ k < N := by simpa using hk
    simp [truncSeq, this]]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [tsum_eq_sum (s := range N) fun l hl => by
    have : ¬ l < N := by simpa using hl
    simp [truncSeq, this]]
  refine Finset.sum_congr rfl fun l hl => ?_
  simp [truncSeq, Finset.mem_range.mp hk, Finset.mem_range.mp hl]

/-- Cochrane (2023), p. 501 (Theorem RG, finite form):
`2 ∑_{k<N} x_k y_k = ∑_{k<N} x_k² + ∑_{k,l<N} ρ^{|k−l|} x_k x_l`, `y_k = ∑_{j} ρ^j x_{k+j}`. -/
theorem two_finite_eq (ρ : ℝ) (N : ℕ) (x : ℕ → ℝ) :
    2 * ∑ k ∈ range N, x k * kmsTail ρ N x k =
      ∑ k ∈ range N, x k ^ 2 + kmsForm ρ N x := by
  set y : ℕ → ℝ := fun m => kmsTail ρ N x m with hy
  have hyN : y N = 0 := kmsTail_of_le ρ le_rfl x
  have hxy : ∀ m ∈ range N, x m = y m - ρ * y (m + 1) := by
    intro m hm
    have := kmsTail_succ ρ (Finset.mem_range.mp hm) x
    simp only [hy]; linarith
  have hsq : ∑ k ∈ range N, x k ^ 2 = ∑ k ∈ range N, (y k - ρ * y (k + 1)) ^ 2 :=
    Finset.sum_congr rfl fun k hk => by rw [← hxy k hk]
  have hcross : ∑ k ∈ range N, x k * kmsTail ρ N x k =
      ∑ k ∈ range N, (y k - ρ * y (k + 1)) * y k :=
    Finset.sum_congr rfl fun k hk => by rw [hxy k hk]
  have hshift : ∑ k ∈ range N, y (k + 1) ^ 2 =
      ∑ m ∈ range N, (if m = 0 then 0 else 1) * y m ^ 2 := by
    have h1 : ∑ m ∈ range (N + 1), (if m = 0 then (0 : ℝ) else 1) * y m ^ 2 =
        ∑ k ∈ range N, y (k + 1) ^ 2 := by
      rw [Finset.sum_range_succ']; simp
    have h2 : ∑ m ∈ range (N + 1), (if m = 0 then (0 : ℝ) else 1) * y m ^ 2 =
        ∑ m ∈ range N, (if m = 0 then 0 else 1) * y m ^ 2 := by
      rw [Finset.sum_range_succ, hyN]; ring
    rw [← h1, h2]
  have hldl : kmsLDL ρ N x = ∑ m ∈ range N, y m ^ 2 -
      ρ ^ 2 * ∑ m ∈ range N, (if m = 0 then 0 else 1) * y m ^ 2 := by
    simp only [kmsLDL, Finset.mul_sum, ← Finset.sum_sub_distrib, hy]
    exact Finset.sum_congr rfl fun m _ => by split_ifs <;> ring
  rw [kmsForm_eq_ldl, hcross, hsq, hldl, ← hshift]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Cochrane (2023), p. 501 (a uniform lower bound for the Kac–Murdock–Szegő form, the finite
version of the spectral bound `(1−ρ²)/|1−ρe^{iω}|² ≥ (1−|ρ|)/(1+|ρ|)`):
`(1 − ρ²) ∑_{k<N} x_k² ≤ (1 + |ρ|)² ∑_{k,l<N} ρ^{|k−l|} x_k x_l` for `ρ² ≤ 1`. -/
theorem kmsForm_lower {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) (N : ℕ) (x : ℕ → ℝ) :
    (1 - ρ ^ 2) * ∑ k ∈ range N, x k ^ 2 ≤ (1 + |ρ|) ^ 2 * kmsForm ρ N x := by
  set y : ℕ → ℝ := fun m => kmsTail ρ N x m with hy
  have hyN : y N = 0 := kmsTail_of_le ρ le_rfl x
  have hr0 := abs_nonneg ρ
  have hr2 : |ρ| ^ 2 = ρ ^ 2 := sq_abs ρ
  have hpt : ∀ m ∈ range N, x m ^ 2 ≤ (1 + |ρ|) * (y m ^ 2 + |ρ| * y (m + 1) ^ 2) := by
    intro m hm
    have hx : x m = y m - ρ * y (m + 1) := by
      have := kmsTail_succ ρ (Finset.mem_range.mp hm) x
      simp only [hy]; linarith
    rw [hx]
    have hab : -(ρ * (y m * y (m + 1))) ≤ |ρ| * |y m| * |y (m + 1)| := by
      rw [mul_assoc, ← abs_mul, ← abs_mul]
      exact neg_le_abs _
    have hsq1 : y m ^ 2 = |y m| ^ 2 := (sq_abs _).symm
    have hsq2 : y (m + 1) ^ 2 = |y (m + 1)| ^ 2 := (sq_abs _).symm
    nlinarith [sq_nonneg (|y m| - |y (m + 1)|), mul_nonneg hr0 (sq_nonneg (|y m| - |y (m + 1)|))]
  have hshift : ∑ m ∈ range N, y (m + 1) ^ 2 ≤ ∑ m ∈ range N, y m ^ 2 := by
    have h1 := Finset.sum_range_succ' (fun m => y m ^ 2) N
    have h2 := Finset.sum_range_succ (fun m => y m ^ 2) N
    rw [hyN] at h2
    nlinarith [sq_nonneg (y 0)]
  have hsum : ∑ k ∈ range N, x k ^ 2 ≤ (1 + |ρ|) ^ 2 * ∑ m ∈ range N, y m ^ 2 := by
    calc ∑ k ∈ range N, x k ^ 2
        ≤ ∑ m ∈ range N, (1 + |ρ|) * (y m ^ 2 + |ρ| * y (m + 1) ^ 2) :=
          Finset.sum_le_sum hpt
      _ = (1 + |ρ|) * (∑ m ∈ range N, y m ^ 2 + |ρ| * ∑ m ∈ range N, y (m + 1) ^ 2) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ (1 + |ρ|) * (∑ m ∈ range N, y m ^ 2 + |ρ| * ∑ m ∈ range N, y m ^ 2) := by
          gcongr
      _ = (1 + |ρ|) ^ 2 * ∑ m ∈ range N, y m ^ 2 := by ring
  have hL : (1 - ρ ^ 2) * ∑ m ∈ range N, y m ^ 2 ≤ kmsForm ρ N x := by
    rw [kmsForm_eq_ldl, kmsLDL, Finset.mul_sum]
    refine Finset.sum_le_sum fun m _ => ?_
    split_ifs
    · nlinarith [sq_nonneg (y m)]
    · exact le_of_eq (by simp only [hy])
  have h1r : 0 ≤ 1 - ρ ^ 2 := by linarith
  calc (1 - ρ ^ 2) * ∑ k ∈ range N, x k ^ 2
      ≤ (1 - ρ ^ 2) * ((1 + |ρ|) ^ 2 * ∑ m ∈ range N, y m ^ 2) :=
        mul_le_mul_of_nonneg_left hsum h1r
    _ = (1 + |ρ|) ^ 2 * ((1 - ρ ^ 2) * ∑ m ∈ range N, y m ^ 2) := by ring
    _ ≤ (1 + |ρ|) ^ 2 * kmsForm ρ N x := mul_le_mul_of_nonneg_left hL (by positivity)

/-! #### Passing to the limit -/

/-- Cochrane (2023), p. 501: the truncated covariances converge, `covInf(x 1{·<N}) → covInf x`
(dominated convergence). -/
theorem tendsto_covInf_trunc {ρ : ℝ} (hρ : |ρ| ≤ 1) {x : ℕ → ℝ}
    (hx : Summable fun k => |x k|) :
    Tendsto (fun N => covInf ρ (truncSeq x N)) atTop (𝓝 (covInf ρ x)) := by
  set S := ∑' k, |x k|
  unfold covInf
  refine tendsto_tsum_of_dominated_convergence (bound := fun m => |x m| * S)
    (hx.mul_right S) (fun m => ?_) (Eventually.of_forall fun N m => ?_)
  · refine (tendsto_truncSeq x m).mul ?_
    unfold bInf
    refine tendsto_tsum_of_dominated_convergence (bound := fun j => |x (m + j)|)
      (tail_abs hx m).1 (fun j => (tendsto_truncSeq x (m + j)).const_mul _)
      (Eventually.of_forall fun N j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    calc |ρ| ^ j * |truncSeq x N (m + j)| ≤ 1 * |x (m + j)| :=
          mul_le_mul (pow_le_one₀ (abs_nonneg _) hρ) (abs_truncSeq_le _ _ _) (abs_nonneg _)
            zero_le_one
      _ = |x (m + j)| := one_mul _
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_truncSeq_le _ _ _) (bInf_bound hρ hx (abs_truncSeq_le x N) m).2
      (abs_nonneg _) (abs_nonneg _)

/-- Cochrane (2023), p. 501: `∑ (x_k 1{k<N})² → ∑ x_k²`. -/
theorem tendsto_sq_trunc {x : ℕ → ℝ} (hx : Summable fun k => |x k|) :
    Tendsto (fun N => ∑' k, truncSeq x N k ^ 2) atTop (𝓝 (∑' k, x k ^ 2)) := by
  refine tendsto_tsum_of_dominated_convergence (bound := fun k => (∑' k, |x k|) * |x k|)
    (hx.mul_left _) (fun k => (tendsto_truncSeq x k).pow 2) (Eventually.of_forall fun N k => ?_)
  rw [Real.norm_eq_abs, abs_pow, sq]
  exact mul_le_mul ((abs_truncSeq_le _ _ _).trans (abs_le_tsum_abs hx k)) (abs_truncSeq_le _ _ _)
    (abs_nonneg _) (by positivity)

/-- Cochrane (2023), p. 501: `kmsInf(x 1{·<N}) → kmsInf x`. -/
theorem tendsto_kmsInf_trunc {ρ : ℝ} (hρ : |ρ| ≤ 1) {x : ℕ → ℝ}
    (hx : Summable fun k => |x k|) :
    Tendsto (fun N => kmsInf ρ (truncSeq x N)) atTop (𝓝 (kmsInf ρ x)) := by
  set S := ∑' k, |x k|
  have hin : ∀ N k l, |kmsKernel ρ k l * truncSeq x N k * truncSeq x N l| ≤ |x k| * |x l| := by
    intro N k l
    rw [abs_mul, abs_mul]
    have h1 := abs_kmsKernel_le hρ k l
    have h2 := abs_truncSeq_le x N k
    have h3 := abs_truncSeq_le x N l
    have := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    calc |kmsKernel ρ k l| * |truncSeq x N k| * |truncSeq x N l| ≤ 1 * |x k| * |x l| :=
          mul_le_mul this h3 (abs_nonneg _) (by positivity)
      _ = |x k| * |x l| := by ring
  unfold kmsInf
  refine tendsto_tsum_of_dominated_convergence (bound := fun k => |x k| * S)
    (hx.mul_right S) (fun k => ?_) (Eventually.of_forall fun N k => ?_)
  · refine tendsto_tsum_of_dominated_convergence (bound := fun l => |x k| * |x l|)
      (hx.mul_left _) (fun l => ?_) (Eventually.of_forall fun N l => ?_)
    · exact ((tendsto_truncSeq x k).const_mul _).mul (tendsto_truncSeq x l)
    · rw [Real.norm_eq_abs]; exact hin N k l
  · rw [Real.norm_eq_abs]
    have := (abs_tsum_le_of_le (hx.mul_left |x k|) (hin N k)).2
    rwa [tsum_mul_left] at this

/-- Cochrane (2023), p. 501, §24.1 p. 519, Online Appendix p. 593 (**Theorem RG for infinite
moving averages**): for absolutely summable `x` (`x_k = a_{k+1}`) and `|ρ| ≤ 1`, with every sum a
genuine (absolutely convergent) sum,
`2 ∑_m x_m b_m = ∑_k x_k² + ∑_k ∑_l ρ^{|k−l|} x_k x_l`, `b_m = ∑_j ρ^j x_{m+j}`. -/
theorem two_covInf_eq {ρ : ℝ} (hρ : |ρ| ≤ 1) {x : ℕ → ℝ} (hx : Summable fun k => |x k|) :
    2 * covInf ρ x = ∑' k, x k ^ 2 + kmsInf ρ x := by
  have h1 := (tendsto_covInf_trunc hρ hx).const_mul 2
  have h2 := (tendsto_sq_trunc hx).add (tendsto_kmsInf_trunc hρ hx)
  refine tendsto_nhds_unique h1 (h2.congr fun N => ?_)
  rw [sq_trunc, kmsInf_trunc, covInf_trunc, two_finite_eq]

/-- Cochrane (2023), p. 501: the infinite Kac–Murdock–Szegő form is positive semidefinite on
absolutely summable sequences for `|ρ| ≤ 1`. -/
theorem kmsInf_nonneg {ρ : ℝ} (hρ : |ρ| ≤ 1) {x : ℕ → ℝ} (hx : Summable fun k => |x k|) :
    0 ≤ kmsInf ρ x := by
  have hρ2 : ρ ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg ρ]
  refine ge_of_tendsto' (tendsto_kmsInf_trunc hρ hx) fun N => ?_
  rw [kmsInf_trunc]; exact kmsForm_nonneg hρ2 N x

/-- Cochrane (2023), p. 501: the infinite form is bounded below,
`(1 − ρ²) ∑ x_k² ≤ (1 + |ρ|)² ∑_k ∑_l ρ^{|k−l|} x_k x_l`. -/
theorem kmsInf_lower {ρ : ℝ} (hρ : |ρ| ≤ 1) {x : ℕ → ℝ} (hx : Summable fun k => |x k|) :
    (1 - ρ ^ 2) * ∑' k, x k ^ 2 ≤ (1 + |ρ|) ^ 2 * kmsInf ρ x := by
  have hρ2 : ρ ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg ρ]
  refine le_of_tendsto_of_tendsto' ((tendsto_sq_trunc hx).const_mul _)
    ((tendsto_kmsInf_trunc hρ hx).const_mul _) fun N => ?_
  rw [sq_trunc, kmsInf_trunc]
  exact kmsForm_lower hρ2 N x

/-- Cochrane (2023), p. 501: for `|ρ| < 1` the infinite Kac–Murdock–Szegő form is positive
definite on absolutely summable sequences. -/
theorem kmsInf_pos {ρ : ℝ} (hρ : |ρ| < 1) {x : ℕ → ℝ} (hx : Summable fun k => |x k|)
    (hne : ∃ k, x k ≠ 0) : 0 < kmsInf ρ x := by
  obtain ⟨k, hk⟩ := hne
  have hsq : 0 < ∑' k, x k ^ 2 :=
    (sq_summable hx).tsum_pos (fun _ => sq_nonneg _) k (by positivity)
  have hρ2 : 0 < 1 - ρ ^ 2 := by rw [← sq_abs]; nlinarith [abs_nonneg ρ]
  have := kmsInf_lower hρ.le hx
  have h1 : 0 < (1 - ρ ^ 2) * ∑' k, x k ^ 2 := mul_pos hρ2 hsq
  have h2 : 0 < (1 + |ρ|) ^ 2 := by positivity
  by_contra hcon
  push Not at hcon
  nlinarith

/-- Cochrane (2023), p. 501, §24.1 p. 519, Online Appendix p. 593 (**Theorem RG, infinite
moving averages**): for an absolutely summable surplus moving average `a` and `|ρ| ≤ 1`, the
covariance of surpluses with lagged debt, `∑_m a_{m+1} b_m`, is strictly positive iff the
surplus is not white noise. -/
theorem covInf_pos_iff {ρ : ℝ} (hρ : |ρ| ≤ 1) {a : ℕ → ℝ} (ha : Summable fun k => |a k|) :
    0 < covInf ρ (fun k => a (k + 1)) ↔ ¬ IsIID a := by
  have hx : Summable fun k => |a (k + 1)| := (summable_nat_add_iff 1).mpr ha
  have h2 := two_covInf_eq hρ hx
  have hk := kmsInf_nonneg hρ hx
  constructor
  · intro hpos hiid
    have hz : covInf ρ (fun k => a (k + 1)) = 0 := by
      unfold covInf
      exact (tsum_congr fun m => by beta_reduce; rw [hiid (m + 1) (by omega), zero_mul]).trans
        tsum_zero
    linarith
  · intro h
    unfold IsIID at h
    push Not at h
    obtain ⟨k, hk1, hk0⟩ := h
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hsq : 0 < ∑' i, a (i + 1) ^ 2 :=
      (sq_summable hx).tsum_pos (fun _ => sq_nonneg _) j (by positivity)
    linarith

/-! #### The value of debt and the regression coefficient -/

/-- Cochrane (2023), p. 501: for `|ρ| < 1` the value-of-debt coefficients `b` of an absolutely
summable moving average are themselves absolutely summable, so `Var(v) = ∑ b_m²` is a genuine
sum. -/
theorem bInf_abs_summable {ρ : ℝ} (hρ : |ρ| < 1) {x : ℕ → ℝ} (hx : Summable fun k => |x k|) :
    Summable (fun m => |bInf ρ x m|) := by
  set g : ℕ × ℕ → ℝ := fun p => |ρ| ^ p.2 * |x (p.1 + p.2)| with hg
  have hg0 : 0 ≤ g := fun p => by positivity
  have hswap : Summable (fun p : ℕ × ℕ => g p.swap) := by
    refine (summable_prod_of_nonneg (f := fun p : ℕ × ℕ => g p.swap)
      (fun p => hg0 p.swap)).mpr ⟨fun j => ?_, ?_⟩
    · simp only [hg, Prod.swap_prod_mk]
      have := (summable_nat_add_iff j).mpr hx
      exact this.mul_left _
    · refine Summable.of_nonneg_of_le (fun j => tsum_nonneg fun m => hg0 _) (fun j => ?_)
        ((summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right (∑' k, |x k|))
      simp only [hg, Prod.swap_prod_mk]
      rw [tsum_mul_left]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have h := tail_abs hx j
      simpa only [add_comm] using h.2
  have hgs : Summable g := by
    have := hswap.comp_injective Prod.swap_injective
    simpa [Function.comp_def] using this
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun m => ?_) hgs.prod
  have hb : ∀ j, |ρ ^ j * x (m + j)| ≤ g (m, j) := by
    intro j; simp only [hg, abs_mul, abs_pow, le_refl]
  exact (abs_tsum_le_of_le (hgs.prod_factor m) hb).2

/-- Cochrane (2023), p. 501: the variance of the value of debt, `∑ b_m²`, is a genuine sum. -/
theorem bInf_sq_summable {ρ : ℝ} (hρ : |ρ| < 1) {x : ℕ → ℝ} (hx : Summable fun k => |x k|) :
    Summable (fun m => bInf ρ x m ^ 2) :=
  (abs_tsum_le_of_le ((bInf_abs_summable hρ hx).mul_left (∑' k, |x k|)) fun m => by
    rw [abs_pow, sq]
    exact mul_le_mul_of_nonneg_right (bInf_bound hρ.le hx (fun _ => le_rfl) m).2
      (abs_nonneg _)).1

/-- Cochrane (2023), p. 501, §24.1 p. 519 (Theorem RG, regression form, infinite moving
averages): for `|ρ| < 1` the population regression coefficient
`γ̂ = ∑_m a_{m+1} b_m / ∑_m b_m²` of surpluses on lagged debt is strictly positive iff the
surplus is not white noise. -/
theorem regInf_pos_iff {ρ : ℝ} (hρ : |ρ| < 1) {a : ℕ → ℝ} (ha : Summable fun k => |a k|) :
    0 < covInf ρ (fun k => a (k + 1)) / ∑' m, bInf ρ (fun k => a (k + 1)) m ^ 2 ↔
      ¬ IsIID a := by
  rw [← covInf_pos_iff hρ.le ha]
  have hv0 : 0 ≤ ∑' m, bInf ρ (fun k => a (k + 1)) m ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have := div_nonpos_of_nonpos_of_nonneg hc hv0
    linarith
  · intro hc
    refine div_pos hc (lt_of_le_of_ne hv0 fun h0 => ?_)
    have hx : Summable fun k => |a (k + 1)| := (summable_nat_add_iff 1).mpr ha
    have hz : ∀ m, bInf ρ (fun k => a (k + 1)) m = 0 := by
      intro m
      by_contra hm
      have := (bInf_sq_summable hρ hx).tsum_pos (fun _ => sq_nonneg _) m (by positivity)
      linarith
    have hcz : covInf ρ (fun k => a (k + 1)) = 0 := by
      unfold covInf
      refine (tsum_congr fun m => ?_).trans tsum_zero
      rw [hz m, mul_zero]
    linarith

/-! #### Link with the covariances of the stochastic model -/

/-- Cochrane (2023), p. 501: the truncated surplus `a 1{k ≤ N}` (an `N`-lag moving average). -/
theorem truncSeq_support (a : ℕ → ℝ) (N : ℕ) : ∀ k, N < k → truncSeq a (N + 1) k = 0 := by
  intro k hk; simp [truncSeq, show ¬ k < N + 1 by omega]

/-- Cochrane (2023), p. 501, §24.1 p. 519 (Theorem RG, infinite moving averages, stochastic
form): the genuine covariances `Cov(s^N_{t+1}, v^N_t)` of the surplus truncated at lag `N` and
the value of debt it implies (finite moving averages of the white-noise shocks, valuation
equation as a genuine `E_t ∑`) converge to `∑_m a_{m+1} b_m` as `N → ∞`. -/
theorem cov_trunc_tendsto {B : LinearMap.BilinForm ℝ (Ω → ℝ)} {ε : ℤ → Ω → ℝ}
    (hw : WhiteNoise B ε) (hε : ShockInfo 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ}
    (hρ : |ρ| < 1) {a : ℕ → ℝ} (ha : Summable fun k => |a k|) (t : ℕ) :
    Tendsto (fun N => B (surplus (truncSeq a (N + 1)) N ε (t + 1))
      (valueOfDebt 𝔼 ρ (surplus (truncSeq a (N + 1)) N ε) t)) atTop
      (𝓝 (covInf ρ (fun k => a (k + 1)))) := by
  have hx : Summable fun k => |a (k + 1)| := (summable_nat_add_iff 1).mpr ha
  refine (tendsto_covInf_trunc hρ.le hx).congr fun N => ?_
  rw [cov_surplus_value hw hε hM hρ (truncSeq_support a N), covInf_trunc,
    Finset.sum_range_succ]
  have hN : truncSeq a (N + 1) (N + 1) = 0 := truncSeq_support a N (N + 1) (by omega)
  rw [hN, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < N := Finset.mem_range.mp hk
  rw [vCoeff_eq_kmsTail ρ (truncSeq_support a N)]
  have e1 : truncSeq a (N + 1) (k + 1) = a (k + 1) := by simp [truncSeq, hk']
  rw [e1]
  congr 1
  unfold kmsTail
  refine Finset.sum_congr rfl fun j hj => ?_
  have : k + j + 1 < N + 1 := by simp only [Finset.mem_range] at hj; omega
  simp [truncSeq, this]

/-! #### AR(1) as a corollary -/

/-- Cochrane (2023), Online Appendix p. 604 (AR(1) surplus `a_k = η^k`, `|η| < 1`, `|ρ| < 1`):
`b_m = η^{m+1}/(1 − ρη)`. -/
theorem ar1_bInf {η ρ : ℝ} (hρη : |ρ * η| < 1) (m : ℕ) :
    bInf ρ (fun k => η ^ (k + 1)) m = η ^ (m + 1) / (1 - ρ * η) := by
  unfold bInf
  have e : ∀ j, ρ ^ j * η ^ (m + j + 1) = η ^ (m + 1) * (ρ * η) ^ j := by
    intro j; rw [mul_pow, pow_add, pow_add]; ring
  simp only [e]
  rw [tsum_mul_left, tsum_geometric_of_abs_lt_one hρη, div_eq_mul_inv]

/-- Cochrane (2023), p. 501 and Online Appendix p. 604 (AR(1) as a corollary of the
infinite-MA Theorem RG): with `a_k = η^k`, `Cov(s_{t+1}, v_t) = η² σ²/(1 − ρη)` where
`σ² = ∑ η^{2k} = 1/(1 − η²)` is the variance of the surplus (agreeing with `ar1_cov`), and this
is strictly positive iff `η ≠ 0`. -/
theorem ar1_covInf {η ρ : ℝ} (hη : |η| < 1) (hρ : |ρ| < 1) :
    covInf ρ (fun k => η ^ (k + 1)) = η ^ 2 * (∑' k : ℕ, (η ^ k) ^ 2) / (1 - ρ * η) ∧
      ∑' k : ℕ, (η ^ k) ^ 2 = 1 / (1 - η ^ 2) ∧
      (0 < covInf ρ (fun k => η ^ (k + 1)) ↔ η ≠ 0) := by
  have hρη : |ρ * η| < 1 := by
    rw [abs_mul]; nlinarith [abs_nonneg ρ, abs_nonneg η]
  have hη2 : |η ^ 2| < 1 := by rw [abs_pow]; nlinarith [abs_nonneg η]
  have hgeo : ∑' k : ℕ, (η ^ k) ^ 2 = 1 / (1 - η ^ 2) := by
    have e : (fun k : ℕ => (η ^ k) ^ 2) = fun k => (η ^ 2) ^ k :=
      funext fun k => by rw [← pow_mul, ← pow_mul, mul_comm]
    rw [e, tsum_geometric_of_abs_lt_one hη2, one_div]
  refine ⟨?_, hgeo, ?_⟩
  · unfold covInf
    simp only [ar1_bInf hρη]
    have e : ∀ m : ℕ, η ^ (m + 1) * (η ^ (m + 1) / (1 - ρ * η)) =
        η ^ 2 / (1 - ρ * η) * (η ^ m) ^ 2 := by
      intro m; rw [pow_succ]; ring
    simp only [e]
    rw [tsum_mul_left]
    ring
  · have ha : Summable fun k => |η ^ k| := by
      simpa [abs_pow] using summable_geometric_of_lt_one (abs_nonneg η) hη
    rw [covInf_pos_iff hρ.le ha]
    constructor
    · intro h hη0
      exact h fun k hk => by rw [hη0, zero_pow (by omega)]
    · intro h hiid
      have := hiid 1 le_rfl
      simp only [pow_one] at this
      exact h this

/-! ### A model satisfying all the hypotheses -/

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): states are realisations
`ω : ℤ → ℝ` of the shock sequence, and `truncPath t ω` sets the shocks after date `t` to their
mean, zero. -/
def truncPath (t : ℕ) (ω : ℤ → ℝ) : ℤ → ℝ := fun k => if k ≤ (t : ℤ) then ω k else 0

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): truncating at `s ≤ t` after
truncating at `t`. -/
theorem truncPath_trunc_le {s t : ℕ} (hst : s ≤ t) (ω : ℤ → ℝ) :
    truncPath s (truncPath t ω) = truncPath s ω := by
  funext k
  simp only [truncPath]
  split_ifs with h1 h2 <;> first | rfl | omega

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): truncating at `t ≥ s` after
truncating at `s`. -/
theorem truncPath_le_trunc {s t : ℕ} (hst : s ≤ t) (ω : ℤ → ℝ) :
    truncPath t (truncPath s ω) = truncPath s ω := by
  funext k
  simp only [truncPath]
  split_ifs with h1 h2 <;> first | rfl | omega

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): the expectation system
`E_t x(ω) = x(truncPath t ω)` — the conditional expectation of the linear (certainty-equivalent)
model, future mean-zero shocks replaced by zero. -/
def truncSystem : ExpectationSystem (ℤ → ℝ) where
  E t := LinearMap.funLeft ℝ ℝ (truncPath t)
  const _ _ := rfl
  mono _ _ _ h _ := h _
  tower {s t} hst x := by
    funext ω
    simp only [LinearMap.funLeft_apply, truncPath_le_trunc hst]
  known {s t} hst x := by
    funext ω
    simp only [LinearMap.funLeft_apply, truncPath_trunc_le hst]

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): the bounded shocks
`ε_k(ω) = max(−1, min(1, ω_k))`. -/
def clampShock (k : ℤ) (ω : ℤ → ℝ) : ℝ := max (-1) (min 1 (ω k))

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): the shocks are bounded by one. -/
theorem clampShock_bounded (k : ℤ) (ω : ℤ → ℝ) : |clampShock k ω| ≤ 1 := by
  unfold clampShock
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): the shocks satisfy `ShockInfo` in
the truncation system. -/
theorem clampShock_info : ShockInfo truncSystem clampShock := by
  intro t k
  funext ω
  simp only [truncSystem, LinearMap.funLeft_apply, clampShock, truncPath]
  split_ifs with h
  · rfl
  · simp

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): the shocks are linearly
independent random variables. -/
theorem clampShock_linearIndependent : LinearIndependent ℝ clampShock := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h := congrFun hg (Pi.single i 1)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
  rw [Finset.sum_eq_single i (fun j _ hji => by simp [clampShock, hji])
    (fun h' => absurd hi h')] at h
  simpa [clampShock] using h

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): a linear map sending each shock
`ε_k` to the unit vector `e_k` (the shocks' coordinates, extended to all random variables). -/
noncomputable def shockCoord : ((ℤ → ℝ) → ℝ) →ₗ[ℝ] (ℤ →₀ ℝ) :=
  Classical.choose (LinearMap.exists_extend clampShock_linearIndependent.repr)

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): `shockCoord ε_k = e_k`. -/
theorem shockCoord_shock (k : ℤ) : shockCoord (clampShock k) = Finsupp.single k 1 := by
  have hspec := Classical.choose_spec (LinearMap.exists_extend
    clampShock_linearIndependent.repr)
  have hk : clampShock k ∈ Submodule.span ℝ (Set.range clampShock) :=
    Submodule.subset_span ⟨k, rfl⟩
  have := congrArg (fun f => f ⟨clampShock k, hk⟩) hspec
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
  rw [shockCoord, this, clampShock_linearIndependent.repr_eq_single k _ rfl]

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): the covariance form
`B(x, y) = ⟨shockCoord x, shockCoord y⟩`. -/
noncomputable def truncCov : LinearMap.BilinForm ℝ ((ℤ → ℝ) → ℝ) :=
  finsuppCov.compl₁₂ shockCoord shockCoord

/-- Cochrane (2023), p. 501 (consistency of the hypotheses): the shocks are white noise for
`truncCov`. -/
theorem clampShock_whiteNoise : WhiteNoise truncCov clampShock := by
  intro j k
  simp only [truncCov, LinearMap.compl₁₂_apply, shockCoord_shock]
  exact finsuppNoise_whiteNoise j k

/-- Cochrane (2023), p. 501, §24.1 p. 519 (survey Theorem RG is not vacuous): in the truncation
model, with bounded white-noise shocks, the MA(1) surplus `s_t = ε_t + ε_{t−1}` has a strictly
positive regression coefficient on debt. -/
theorem truncModel_regCoeff_pos {ρ : ℝ} (hρ : |ρ| < 1) (t : ℕ) :
    0 < regCoeff truncCov (surplus ma1Coeff 1 clampShock (t + 1))
      (valueOfDebt truncSystem ρ (surplus ma1Coeff 1 clampShock) t) :=
  ma1_regCoeff_pos clampShock_whiteNoise clampShock_info clampShock_bounded hρ t

end Cochrane.ObservationalEquivalence.SurplusRegression
