/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DebtDeficitsInflation.SurplusProcessFacts
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# The debt-feedback surplus as a closed-form moving average

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.2.6, p. 96 (survey E10,
the Chapter 4 half).

The surplus `s̃_{t+1} = αv_t + u_{s,t+1}` with `ρv_{t+1} = v_t − s̃_{t+1}` and a disturbance with
moving-average representation `u_t = a_u(L)ε_t` is itself a moving average in the same shock.
With `λ = (1 − α)/ρ` (`|λ| < 1`), the stationary value of debt is
`v_t = −ρ⁻¹∑_m c_mε_{t−m}`, `c_m = ∑_{k ≤ m} a_{u,k}λ^{m−k}`, and the surplus has coefficients
`a_{s,0} = a_{u,0}`, `a_{s,m+1} = a_{u,m+1} − (α/ρ)c_m`, i.e. `a_s(L) = a_u(L)(1 − ρ⁻¹L)/(1 − λL)`.
Hence `a_s(ρ) = 0` whatever `a_u`, while `a_u(ρ) = 1/(1 − ρη) > 1` for an AR(1) disturbance with
`η > 0`. The module `SurplusProcessFacts` proved the same fact termwise
(`SurplusProcessFacts.feedback_full_repayment`); here it is a statement about the coefficient
sequence, and the two are linked.

## Main definitions

* `lam`, `debtCoeff` (`c_m`), `fbCoeff` (`a_s`), `fbFactor` (the coefficients of
  `(1 − ρ⁻¹L)/(1 − λL)`), `statValue` (the stationary value of debt), `maSeries`.

## Main results

* `debtCoeff_succ`, `fbCoeff_eq_conv` (`a_s = a_u * fbFactor`), `summable_abs_debtCoeff`,
  `summable_abs_fbCoeff`.
* Generating functions: `hasSum_gen_debtCoeff` (`c(z) = a_u(z)/(1 − λz)`),
  `hasSum_gen_fbCoeff` (`a_s(z) = a_u(z)(1 − z/ρ)/(1 − λz)`), `gen_fbCoeff_rho`
  (`a_s(ρ) = 0`).
* The process: `statValue_succ`, `fbValue_eq_statValue`, `fbSurplus_eq_maSeries`,
  `isMA_maSeries`, `isMA_statValue`.
* Headlines: `feedback_ma_repaid` (the surplus is the moving average `a_s`, `a_s(ρ) = 0`, and
  `∑ρʲΔs̃_{t+1+j} = a_s(ρ)ε_{t+1} = 0` while `∑ρʲΔu_{t+1+j} = a_u(ρ)ε_{t+1}`),
  `feedback_ma_link` (the termwise `SurplusProcessFacts.feedback_full_repayment` is the same
  series), `debtCoeff_ar1`, `fbCoeff_ar1`, `feedback_ar1_closed_form` (AR(1) disturbance:
  explicit sequences, `a_s(ρ) = 0 < 1 < a_u(ρ)`).
-/

namespace Cochrane.DebtDeficitsInflation.TidyR6FeedbackMA

open Filter Topology
open Cochrane.DebtDeficitsInflation.Innovations
open Cochrane.DebtDeficitsInflation.LinearizedIdentities
open Cochrane.DebtDeficitsInflation.SurplusMA
open Cochrane.DebtDeficitsInflation.SurplusProcessFacts

/-! ### The coefficient sequences -/

/-- Cochrane (2023), §4.2.6, p. 96: the debt-feedback root `λ = (1 − α)/ρ` (from
`v_{t+1} = λv_t − u_{t+1}/ρ`). -/
noncomputable def lam (ρ α : ℝ) : ℝ := (1 - α) / ρ

/-- Cochrane (2023), §4.2.6, p. 96: the debt coefficients `c_m = ∑_{k ≤ m} a_{u,k}λ^{m−k}`, so
that `v_t = −ρ⁻¹∑_m c_mε_{t−m}` (the coefficients of `a_u(L)/(1 − λL)`). -/
noncomputable def debtCoeff (ρ α : ℝ) (a : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), a k * lam ρ α ^ (m - k)

/-- Cochrane (2023), §4.2.6, p. 96: the moving-average coefficients `a_s` of the debt-feedback
surplus, `a_{s,0} = a_{u,0}`, `a_{s,m+1} = a_{u,m+1} − (α/ρ)c_m`. -/
noncomputable def fbCoeff (ρ α : ℝ) (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => a 0
  | m + 1 => a (m + 1) - α / ρ * debtCoeff ρ α a m

/-- Cochrane (2023), §4.2.6, p. 96: the coefficients of the lag polynomial
`(1 − ρ⁻¹L)/(1 − λL)`: `1, −(α/ρ), −(α/ρ)λ, −(α/ρ)λ², …`. -/
noncomputable def fbFactor (ρ α : ℝ) : ℕ → ℝ
  | 0 => 1
  | m + 1 => -(α / ρ) * lam ρ α ^ m

/-- Cochrane (2023), §4.2.6, p. 96: `c_0 = a_{u,0}`. -/
theorem debtCoeff_zero (ρ α : ℝ) (a : ℕ → ℝ) : debtCoeff ρ α a 0 = a 0 := by
  simp [debtCoeff]

/-- Cochrane (2023), §4.2.6, p. 96: the debt coefficients follow the debt dynamics,
`c_{m+1} = λc_m + a_{u,m+1}`. -/
theorem debtCoeff_succ (ρ α : ℝ) (a : ℕ → ℝ) (m : ℕ) :
    debtCoeff ρ α a (m + 1) = lam ρ α * debtCoeff ρ α a m + a (m + 1) := by
  unfold debtCoeff
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [show m + 1 - k = (m - k) + 1 by omega, pow_succ]
  ring

/-- Cochrane (2023), §4.2.6, p. 96: the closed form `a_s(L) = a_u(L)·(1 − ρ⁻¹L)/(1 − λL)` as a
convolution of coefficient sequences, `a_{s,j} = ∑_{k ≤ j} a_{u,k}·fbFactor_{j−k}`, provided
`ρ ≠ 0` (it uses `λ − ρ⁻¹ = −α/ρ`). -/
theorem fbCoeff_eq_conv (ρ α : ℝ) (a : ℕ → ℝ) (j : ℕ) :
    fbCoeff ρ α a j = ∑ k ∈ Finset.range (j + 1), a k * fbFactor ρ α (j - k) := by
  rcases j with _ | m
  · simp [fbCoeff, fbFactor]
  · rw [Finset.sum_range_succ, Nat.sub_self]
    simp only [fbCoeff, debtCoeff, Finset.mul_sum]
    rw [show fbFactor ρ α 0 = 1 from rfl, mul_one, sub_eq_add_neg, add_comm,
      ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [show m + 1 - k = (m - k) + 1 by omega,
      show fbFactor ρ α (m - k + 1) = -(α / ρ) * lam ρ α ^ (m - k) from rfl]
    ring

/-- Cochrane (2023), §4.2.6, p. 96: with `∑|a_{u,j}| < ∞` and `|λ| < 1` the debt coefficients are
absolutely summable. -/
theorem summable_abs_debtCoeff {ρ α : ℝ} (hl : |lam ρ α| < 1) {a : ℕ → ℝ}
    (ha : Summable fun j => |a j|) : Summable fun m => |debtCoeff ρ α a m| := by
  have hg : Summable fun n => ‖lam ρ α ^ n‖ := by
    simpa [norm_pow, Real.norm_eq_abs] using
      summable_geometric_of_lt_one (abs_nonneg _) hl
  have h := summable_norm_sum_mul_range_of_summable_norm
    (f := a) (g := fun n => lam ρ α ^ n) (by simpa [Real.norm_eq_abs] using ha) hg
  simpa [Real.norm_eq_abs, debtCoeff] using h

/-- Cochrane (2023), §4.2.6, p. 96: the surplus coefficients are absolutely summable. -/
theorem summable_abs_fbCoeff {ρ α : ℝ} (hl : |lam ρ α| < 1) {a : ℕ → ℝ}
    (ha : Summable fun j => |a j|) : Summable fun j => |fbCoeff ρ α a j| := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun m => ?_)
    (((summable_nat_add_iff 1).2 ha).add ((summable_abs_debtCoeff hl ha).mul_left |α / ρ|))
  simp only [fbCoeff]
  calc |a (m + 1) - α / ρ * debtCoeff ρ α a m|
      ≤ |a (m + 1)| + |α / ρ * debtCoeff ρ α a m| := abs_sub _ _
    _ = |a (m + 1)| + |α / ρ| * |debtCoeff ρ α a m| := by rw [abs_mul]

/-! ### Generating functions -/

/-- Cochrane (2023), §4.2.6, p. 96: the generating function of the debt coefficients,
`∑ c_mzᵐ = a_u(z)/(1 − λz)`, whenever `∑|a_{u,j}zʲ| < ∞` and `|λz| < 1`. -/
theorem hasSum_gen_debtCoeff {ρ α z : ℝ} {a : ℕ → ℝ} (ha : Summable fun j => |a j * z ^ j|)
    (hz : |lam ρ α * z| < 1) :
    HasSum (fun m => debtCoeff ρ α a m * z ^ m) (gen a z / (1 - lam ρ α * z)) := by
  have hg : Summable fun n => ‖(lam ρ α * z) ^ n‖ := by
    simpa [norm_pow, Real.norm_eq_abs] using summable_geometric_of_lt_one (abs_nonneg _) hz
  have hf : Summable fun j => ‖a j * z ^ j‖ := by simpa [Real.norm_eq_abs] using ha
  have hterm : ∀ m, ∑ k ∈ Finset.range (m + 1), a k * z ^ k * (lam ρ α * z) ^ (m - k) =
      debtCoeff ρ α a m * z ^ m := fun m => by
    rw [debtCoeff, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have : z ^ m = z ^ k * z ^ (m - k) := by rw [← pow_add, Nat.add_sub_cancel' hk']
    rw [this, mul_pow]
    ring
  have hsum := summable_norm_sum_mul_range_of_summable_norm hf hg
  simp_rw [hterm] at hsum
  have heq := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hg
  simp_rw [hterm] at heq
  have hgeo : ∑' n, (lam ρ α * z) ^ n = (1 - lam ρ α * z)⁻¹ :=
    tsum_geometric_of_abs_lt_one hz
  rw [hgeo] at heq
  have hval : gen a z / (1 - lam ρ α * z) = ∑' m, debtCoeff ρ α a m * z ^ m := by
    rw [div_eq_mul_inv, gen, heq]
  rw [hval]
  exact (hsum.of_norm).hasSum

/-- Cochrane (2023), §4.2.6, p. 96: the generating function of the debt-feedback surplus,
`a_s(z) = a_u(z)(1 − z/ρ)/(1 − λz)` (`ρ ≠ 0`, `∑|a_{u,j}zʲ| < ∞`, `|λz| < 1`). -/
theorem hasSum_gen_fbCoeff {ρ α z : ℝ} (hρ : ρ ≠ 0) {a : ℕ → ℝ}
    (ha : Summable fun j => |a j * z ^ j|) (hz : |lam ρ α * z| < 1) :
    HasSum (fun j => fbCoeff ρ α a j * z ^ j)
      (gen a z * (1 - z / ρ) / (1 - lam ρ α * z)) := by
  have hA : HasSum (fun j => a j * z ^ j) (gen a z) := (ha.of_abs).hasSum
  have hC := hasSum_gen_debtCoeff ha hz
  have hd : 1 - lam ρ α * z ≠ 0 := by
    intro h0
    have : lam ρ α * z = 1 := by linarith
    rw [this, abs_one] at hz
    exact lt_irrefl _ hz
  rw [← hasSum_nat_add_iff' 1]
  have h1 := (hasSum_nat_add_iff' 1).2 hA
  have h2 := h1.sub (hC.mul_left (α / ρ * z))
  convert h2 using 1
  · funext m
    simp only [fbCoeff, pow_succ]
    ring
  · simp only [Finset.range_one, Finset.sum_singleton, fbCoeff, pow_zero, mul_one]
    have key : 1 - z / ρ = (1 - lam ρ α * z) - α / ρ * z := by
      unfold lam; field_simp; ring
    rw [key]
    field_simp
    ring

/-- Cochrane (2023), §4.2.6, p. 96 ("surpluses themselves `s_t` may be fully repaid with
`a_s(ρ) = 0`"): `a_s(ρ) = 0` for every disturbance with `∑|a_{u,j}ρʲ| < ∞`, provided `ρ ≠ 0` and
`|1 − α| < 1` (so `|λρ| < 1`). -/
theorem gen_fbCoeff_rho {ρ α : ℝ} (hρ : ρ ≠ 0) (hα : |1 - α| < 1) {a : ℕ → ℝ}
    (ha : Summable fun j => |a j * ρ ^ j|) : gen (fbCoeff ρ α a) ρ = 0 := by
  have hz : |lam ρ α * ρ| < 1 := by rwa [lam, div_mul_cancel₀ _ hρ]
  have h := hasSum_gen_fbCoeff hρ ha hz
  rw [div_self hρ, sub_self, mul_zero, zero_div] at h
  exact h.tsum_eq

/-! ### The debt-feedback process as a moving average -/

variable {Ω : Type*}

/-- Cochrane (2023), eq. (4.1), p. 87: the moving average `∑_j b_jε_{t−j}` of a shock with an
infinite past. -/
noncomputable def maSeries (b : ℕ → ℝ) (ε : ℤ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, b j * ε ((t : ℤ) - j) ω

/-- Cochrane (2023), §4.2.6, p. 96: the stationary value of debt under the debt-feedback
surplus, `v_t = −ρ⁻¹∑_m c_mε_{t−m}`. -/
noncomputable def statValue (ρ α : ℝ) (a : ℕ → ℝ) (ε : ℤ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  maSeries (fun m => -ρ⁻¹ * debtCoeff ρ α a m) ε t

/-- Cochrane (2023), eq. (4.1), p. 87 (tool): an absolutely summable moving average of a bounded
shock converges at every date and state. -/
theorem summable_ma_term {b : ℕ → ℝ} (hb : Summable fun j => |b j|) {ε : ℤ → Ω → ℝ} {M : ℝ}
    (hM : ∀ k ω, |ε k ω| ≤ M) (τ : ℤ) (ω : Ω) : Summable fun j => b j * ε (τ - j) ω :=
  Summable.of_norm_bounded (hb.mul_right M) fun j => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM _ ω) (abs_nonneg _)

/-- Cochrane (2023), eq. (4.1), p. 87: `maSeries b ε` is a moving average in the sense of
`Innovations.IsMA`. -/
theorem isMA_maSeries {b : ℕ → ℝ} (hb : Summable fun j => |b j|) (ε : ℤ → Ω → ℝ) :
    IsMA b ε (maSeries b ε) :=
  ⟨hb, fun _ _ => rfl⟩

/-- Cochrane (2023), §4.2.6, p. 96: the stationary value of debt is a moving average with
coefficients `−ρ⁻¹c_m`. -/
theorem isMA_statValue {ρ α : ℝ} (hl : |lam ρ α| < 1) {a : ℕ → ℝ}
    (ha : Summable fun j => |a j|) (ε : ℤ → Ω → ℝ) :
    IsMA (fun m => -ρ⁻¹ * debtCoeff ρ α a m) ε (statValue ρ α a ε) :=
  isMA_maSeries (by simpa [abs_mul] using (summable_abs_debtCoeff hl ha).mul_left |ρ⁻¹|) ε

/-- Cochrane (2023), §4.2.6, p. 96 (tool): the date-`t` value of debt is `−ρ⁻¹∑_m c_mε_{t−m}`. -/
theorem statValue_apply (ρ α : ℝ) (a : ℕ → ℝ) (ε : ℤ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    statValue ρ α a ε t ω = -ρ⁻¹ * ∑' m, debtCoeff ρ α a m * ε ((t : ℤ) - m) ω := by
  simp only [statValue, maSeries]
  rw [← tsum_mul_left]
  exact tsum_congr fun m => by ring

/-- Cochrane (2023), §4.2.6, p. 96 (tool): peeling off the current shock of a moving average,
`∑_j b_jε_{t+1−j} = b_0ε_{t+1} + ∑_m b_{m+1}ε_{t−m}`. -/
theorem tsum_ma_succ {b : ℕ → ℝ} (hb : Summable fun j => |b j|) {ε : ℤ → Ω → ℝ} {M : ℝ}
    (hM : ∀ k ω, |ε k ω| ≤ M) (t : ℕ) (ω : Ω) :
    ∑' j, b j * ε (((t + 1 : ℕ) : ℤ) - j) ω =
      b 0 * ε ((t : ℤ) + 1) ω + ∑' m, b (m + 1) * ε ((t : ℤ) - m) ω := by
  rw [(summable_ma_term hb hM _ ω).tsum_eq_zero_add]
  congr 1
  refine tsum_congr fun m => ?_
  rw [show ((t + 1 : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ) = (t : ℤ) - m by push_cast; ring]

/-- Cochrane (2023), §4.2.6, p. 96: the stationary value of debt solves the debt-feedback
dynamics `v_{t+1} = ρ⁻¹((1 − α)v_t − u_{t+1})` when `u = a_u(L)ε`, `ρ ≠ 0`, `|λ| < 1`. -/
theorem statValue_succ {ρ α : ℝ} (hρ : ρ ≠ 0) (hl : |lam ρ α| < 1) {a : ℕ → ℝ}
    (ha : Summable fun j => |a j|) {ε : ℤ → Ω → ℝ} {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    {u : ℕ → Ω → ℝ} (hu : IsMA a ε u) (t : ℕ) :
    statValue ρ α a ε (t + 1) = ρ⁻¹ • ((1 - α) • statValue ρ α a ε t - u (t + 1)) := by
  funext ω
  have hc := summable_abs_debtCoeff hl ha
  have ha1 : Summable fun m => |a (m + 1)| := (summable_nat_add_iff 1).2 ha
  have hS : ∑' m, debtCoeff ρ α a m * ε (((t + 1 : ℕ) : ℤ) - m) ω =
      lam ρ α * ∑' m, debtCoeff ρ α a m * ε ((t : ℤ) - m) ω + u (t + 1) ω := by
    rw [tsum_ma_succ hc hM, hu.2 (t + 1) ω, tsum_ma_succ ha hM, debtCoeff_zero]
    simp_rw [debtCoeff_succ, add_mul]
    have hs1 : Summable fun m => lam ρ α * debtCoeff ρ α a m * ε ((t : ℤ) - m) ω := by
      simpa [mul_assoc] using (summable_ma_term hc hM t ω).mul_left (lam ρ α)
    rw [Summable.tsum_add hs1 (summable_ma_term ha1 hM t ω)]
    simp_rw [mul_assoc]
    rw [tsum_mul_left]
    ring
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [statValue_apply, statValue_apply, hS, lam]
  field_simp
  ring

/-- Cochrane (2023), §4.2.6, p. 96: started at the stationary `v_0`, the value of debt of
`SurplusProcessFacts` (`SurplusProcessFacts.fbValue`) is the stationary value at every date. -/
theorem fbValue_eq_statValue {ρ α : ℝ} (hρ : ρ ≠ 0) (hl : |lam ρ α| < 1) {a : ℕ → ℝ}
    (ha : Summable fun j => |a j|) {ε : ℤ → Ω → ℝ} {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    {u : ℕ → Ω → ℝ} (hu : IsMA a ε u) (t : ℕ) :
    fbValue ρ α (statValue ρ α a ε 0) u t = statValue ρ α a ε t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change ρ⁻¹ • ((1 - α) • fbValue ρ α (statValue ρ α a ε 0) u t - u (t + 1)) = _
    rw [ih, statValue_succ hρ hl ha hM hu t]

/-- Cochrane (2023), §4.2.6, p. 96: **the debt-feedback surplus is the moving average `a_s(L)ε`**,
`s̃_{t+1} = αv_t + u_{t+1} = ∑_j a_{s,j}ε_{t+1−j}`. -/
theorem fbSurplus_eq_maSeries {ρ α : ℝ} (hρ : ρ ≠ 0) (hl : |lam ρ α| < 1) {a : ℕ → ℝ}
    (ha : Summable fun j => |a j|) {ε : ℤ → Ω → ℝ} {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    {u : ℕ → Ω → ℝ} (hu : IsMA a ε u) (t : ℕ) :
    fbSurplus ρ α (statValue ρ α a ε 0) u (t + 1) = maSeries (fbCoeff ρ α a) ε (t + 1) := by
  change α • fbValue ρ α (statValue ρ α a ε 0) u t + u (t + 1) = _
  rw [fbValue_eq_statValue hρ hl ha hM hu t]
  funext ω
  have hc := summable_abs_debtCoeff hl ha
  have ha1 : Summable fun m => |a (m + 1)| := (summable_nat_add_iff 1).2 ha
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, maSeries]
  rw [tsum_ma_succ (summable_abs_fbCoeff hl ha) hM, statValue_apply, hu.2 (t + 1) ω,
    tsum_ma_succ ha hM]
  simp only [fbCoeff, sub_mul]
  have hs2 : Summable fun m => α / ρ * debtCoeff ρ α a m * ε ((t : ℤ) - m) ω := by
    simpa [mul_assoc] using (summable_ma_term hc hM t ω).mul_left (α / ρ)
  rw [Summable.tsum_sub (summable_ma_term ha1 hM t ω) hs2]
  simp_rw [mul_assoc]
  rw [tsum_mul_left]
  ring

/-- Cochrane (2023), §4.2.6, p. 96 (survey E10, the Chapter 4 half), **closed form**: let the
disturbance be a moving average `u = a_u(L)ε` in a bounded martingale-difference shock,
`ρ ≠ 0`, `|ρ| ≤ 1`, `|1 − α| < |ρ|`. Then the debt-feedback surplus (from the stationary value of
debt) is the moving average with the explicit coefficients `a_s = fbCoeff`, with the same impact
`a_{s,0} = a_{u,0}`; `a_s(ρ) = 0`; and the discounted surplus news is `a_s(ρ)ε_{t+1} = 0`, while
the discounted disturbance news is `a_u(ρ)ε_{t+1}`. -/
theorem feedback_ma_repaid (𝔼 : ExpectationSystem Ω) {ρ α : ℝ} (hρ : ρ ≠ 0) (hρ1 : |ρ| ≤ 1)
    (hα : |1 - α| < |ρ|) {a : ℕ → ℝ} (ha : Summable fun j => |a j|) {ε : ℤ → Ω → ℝ}
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {u : ℕ → Ω → ℝ} (hu : IsMA a ε u) :
    IsMA (fbCoeff ρ α a) ε (maSeries (fbCoeff ρ α a) ε) ∧
    (∀ t, fbSurplus ρ α (statValue ρ α a ε 0) u (t + 1) = maSeries (fbCoeff ρ α a) ε (t + 1)) ∧
    fbCoeff ρ α a 0 = a 0 ∧ gen (fbCoeff ρ α a) ρ = 0 ∧
    (∀ t ω, HasSum (fun j => ρ ^ j *
      innov 𝔼 t (fbSurplus ρ α (statValue ρ α a ε 0) u (t + 1 + j)) ω)
        (gen (fbCoeff ρ α a) ρ * ε ((t : ℤ) + 1) ω)) ∧
    (∀ t ω, HasSum (fun j => ρ ^ j *
      innov 𝔼 t (fbSurplus ρ α (statValue ρ α a ε 0) u (t + 1 + j)) ω) 0) ∧
    (∀ t ω, HasSum (fun j => ρ ^ j * innov 𝔼 t (u (t + 1 + j)) ω)
      (gen a ρ * ε ((t : ℤ) + 1) ω)) := by
  have hρp : 0 < |ρ| := abs_pos.2 hρ
  have hl : |lam ρ α| < 1 := by
    rw [lam, abs_div, div_lt_one hρp]
    exact hα
  have hα1 : |1 - α| < 1 := lt_of_lt_of_le hα hρ1
  have hMA := isMA_maSeries (summable_abs_fbCoeff hl ha) ε
  have hS := fbSurplus_eq_maSeries hρ hl ha hM hu
  have hsr : Summable fun j => |a j * ρ ^ j| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun j => by
      rw [abs_mul, abs_pow]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hρ1)) ha
  have h0 := gen_fbCoeff_rho hρ hα1 hsr
  have hterm : ∀ t ω, HasSum (fun j => ρ ^ j *
      innov 𝔼 t (fbSurplus ρ α (statValue ρ α a ε 0) u (t + 1 + j)) ω)
        (gen (fbCoeff ρ α a) ρ * ε ((t : ℤ) + 1) ω) := fun t ω =>
    (innov_PV_termwise 𝔼 hMA hε hM hρ1 t ω).congr_fun fun j => by
      rw [show t + 1 + j = (t + j) + 1 by omega, hS (t + j)]
  refine ⟨hMA, hS, rfl, h0, hterm, fun t ω => ?_, fun t ω => innov_PV_termwise 𝔼 hu hε hM hρ1 t ω⟩
  simpa [h0] using hterm t ω

/-- Cochrane (2023), §4.2.6, p. 96, **link to the termwise result**: for `0 < ρ < 1` and
`|1 − α| < ρ`, the series `∑ρʲΔs̃_{t+1+j}` of `SurplusProcessFacts.feedback_full_repayment` (with
the stationary `v_0`) is the same series, and it converges both to `0` (the termwise proof) and
to `a_s(ρ)ε_{t+1}` (the closed form); the two agree because `a_s(ρ) = 0`. -/
theorem feedback_ma_link (𝔼 : ExpectationSystem Ω) {ρ α : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hα : |1 - α| < ρ) {a : ℕ → ℝ} (ha : Summable fun j => |a j|) {ε : ℤ → Ω → ℝ}
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {u : ℕ → Ω → ℝ} (hu : IsMA a ε u)
    (t : ℕ) (ω : Ω) :
    SeriesTo (fun j => ρ ^ j *
      innov 𝔼 t (fbSurplus ρ α (statValue ρ α a ε 0) u (t + 1 + j)) ω) 0 ∧
    SeriesTo (fun j => ρ ^ j *
      innov 𝔼 t (fbSurplus ρ α (statValue ρ α a ε 0) u (t + 1 + j)) ω)
        (gen (fbCoeff ρ α a) ρ * ε ((t : ℤ) + 1) ω) ∧
    gen (fbCoeff ρ α a) ρ = 0 := by
  have hρa : |ρ| = ρ := abs_of_pos hρ0
  have hl : |lam ρ α| < 1 := by
    rw [lam, abs_div, hρa, div_lt_one hρ0]
    exact hα
  obtain ⟨-, -, -, h0, hterm, -, -⟩ := feedback_ma_repaid 𝔼 hρ0.ne' (by rw [hρa]; exact hρ1.le)
    (by rwa [hρa]) ha hε hM hu
  have hV := isMA_statValue hl ha ε
  have hVv := (isMA_iff_vec _ ε _).1 hV
  have huv := (isMA_iff_vec a ε u).1 hu
  have hεv := isMDSVec_of_isMDS 𝔼 hε
  have hv0b : ∀ ω', |statValue ρ α a ε 0 ω'| ≤
      ∑ _i : Fin 1, (∑' j, |-ρ⁻¹ * debtCoeff ρ α a j|) * M :=
    fun ω' => abs_MAVec_le hVv (fun k _ ω'' => hM k ω'') 0 ω'
  have hv0 : 𝔼.E 0 (statValue ρ α a ε 0) = statValue ρ α a ε 0 :=
    adapted_MAVec 𝔼 hVv hεv (fun k _ ω'' => hM k ω'') 0
  have hub : ∀ τ ω', |u τ ω'| ≤ ∑ _i : Fin 1, (∑' j, |a j|) * M :=
    fun τ ω' => abs_MAVec_le huv (fun k _ ω'' => hM k ω'') τ ω'
  have hua : 𝔼.Adapted u := adapted_MAVec 𝔼 huv hεv (fun k _ ω'' => hM k ω'')
  exact ⟨feedback_full_repayment 𝔼 hρ0 hρ1 hα hv0b hv0 hub hua t ω,
    seriesTo_of_hasSum (hterm t ω), h0⟩

/-! ### The AR(1) disturbance: explicit sequences -/

/-- Cochrane (2023), §4.2.6, p. 96, AR(1) disturbance `a_{u,j} = ηʲ`, `η ≠ λ`: the debt
coefficients in closed form, `c_m = (η^{m+1} − λ^{m+1})/(η − λ)`. -/
theorem debtCoeff_ar1 {ρ α η : ℝ} (hne : η ≠ lam ρ α) (m : ℕ) :
    debtCoeff ρ α (fun j => η ^ j) m = (η ^ (m + 1) - lam ρ α ^ (m + 1)) / (η - lam ρ α) := by
  rw [eq_div_iff (sub_ne_zero.2 hne), ← geom_sum₂_mul]
  simp [debtCoeff]

/-- Cochrane (2023), §4.2.6, p. 96, AR(1) disturbance with `η = λ`: `c_m = (m + 1)λᵐ`. -/
theorem debtCoeff_ar1_eq {ρ α : ℝ} (m : ℕ) :
    debtCoeff ρ α (fun j => lam ρ α ^ j) m = (m + 1) * lam ρ α ^ m := by
  unfold debtCoeff
  rw [Finset.sum_congr rfl fun k hk => (show lam ρ α ^ k * lam ρ α ^ (m - k) = lam ρ α ^ m by
    rw [← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))])]
  simp

/-- Cochrane (2023), §4.2.6, p. 96, AR(1) disturbance, `η ≠ λ`: the surplus coefficients
`a_{s,0} = 1`, `a_{s,m+1} = η^{m+1} − (α/ρ)(η^{m+1} − λ^{m+1})/(η − λ)`. -/
theorem fbCoeff_ar1 {ρ α η : ℝ} (hne : η ≠ lam ρ α) :
    fbCoeff ρ α (fun j => η ^ j) 0 = 1 ∧ ∀ m, fbCoeff ρ α (fun j => η ^ j) (m + 1) =
      η ^ (m + 1) - α / ρ * ((η ^ (m + 1) - lam ρ α ^ (m + 1)) / (η - lam ρ α)) :=
  ⟨by simp [fbCoeff], fun m => by simp only [fbCoeff, debtCoeff_ar1 hne]⟩

/-- Cochrane (2023), §4.2.6, p. 96 ("the `u_{s,t}` term may have `a_u(ρ) > 1` … surpluses
themselves may be fully repaid with `a_s(ρ) = 0`"), **closed form for an AR(1) disturbance**
(`0 < ρ`, `0 < η`, `|ρη| < 1`, `|1 − α| < 1`, `η ≠ λ`): the explicit coefficient sequence, the
generating function `a_s(z) = (1 − z/ρ)/((1 − ηz)(1 − λz))`, `a_s(ρ) = 0`, and
`a_u(ρ) = 1/(1 − ρη) > 1`. -/
theorem feedback_ar1_closed_form {ρ α η : ℝ} (hρ : 0 < ρ) (hα : |1 - α| < 1) (hη : 0 < η)
    (hρη : |ρ * η| < 1) (hne : η ≠ lam ρ α) :
    fbCoeff ρ α (fun j => η ^ j) 0 = 1 ∧
    (∀ m, fbCoeff ρ α (fun j => η ^ j) (m + 1) =
      η ^ (m + 1) - α / ρ * ((η ^ (m + 1) - lam ρ α ^ (m + 1)) / (η - lam ρ α))) ∧
    (∀ z, |η * z| < 1 → |lam ρ α * z| < 1 →
      HasSum (fun j => fbCoeff ρ α (fun j => η ^ j) j * z ^ j)
        ((1 - z / ρ) / ((1 - η * z) * (1 - lam ρ α * z)))) ∧
    gen (fbCoeff ρ α (fun j => η ^ j)) ρ = 0 ∧
    gen (fun j => η ^ j) ρ = 1 / (1 - ρ * η) ∧ 1 < gen (fun j => η ^ j) ρ := by
  have hsum : ∀ z, |η * z| < 1 → Summable fun j => |η ^ j * z ^ j| := fun z hz => by
    simpa [← mul_pow, abs_pow] using summable_geometric_of_lt_one (abs_nonneg _) hz
  refine ⟨(fbCoeff_ar1 hne).1, (fbCoeff_ar1 hne).2, fun z hz hlz => ?_,
    gen_fbCoeff_rho hρ.ne' hα (hsum ρ (by rwa [mul_comm])), gen_ar1 hρη,
    (one_lt_gen_ar1_iff hρ hρη).2 hη⟩
  have h := hasSum_gen_fbCoeff hρ.ne' (hsum z hz) hlz
  rw [gen_ar1 (by rwa [mul_comm])] at h
  convert h using 1
  have h1 : 1 - z * η ≠ 0 := by
    intro h0
    have : η * z = 1 := by linarith
    rw [this, abs_one] at hz
    exact lt_irrefl _ hz
  have h2 : 1 - lam ρ α * z ≠ 0 := by
    intro h0
    have : lam ρ α * z = 1 := by linarith
    rw [this, abs_one] at hlz
    exact lt_irrefl _ hlz
  rw [mul_comm η z]
  field_simp

end Cochrane.DebtDeficitsInflation.TidyR6FeedbackMA
