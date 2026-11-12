/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.SurplusRegression
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.PSeries

/-!
# Theorem RG for square-summable moving averages: the coefficient algebra

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.3, p. 501, Chapter 24,
§24.1, p. 519, and Online Appendix Chapter 2, introduction, p. 593 (surpluses `s_t = a(L)ε_t`).

`SurplusRegression` proves the coefficient identities of Theorem RG for absolutely summable
moving averages. A stationary moving average only needs square-summable coefficients
(`∑ a_k² < ∞`). This module proves the identities for every square-summable `x` (`x_k = a_{k+1}`)
and `|ρ| < 1`, with every sum a genuine absolutely convergent sum:

* `summable_bterm`, `bInf_sq_summable_of_sq`: `b_m = ∑_j ρ^j x_{m+j}` converges and `b ∈ ℓ²`
  (weighted Cauchy–Schwarz `sq_tsum_le`);
* `covInf_summable_of_sq`: `∑_m x_m b_m` converges absolutely;
* `bInf_succ`: `b_m = x_m + ρ b_{m+1}`;
* `two_covInf_ldl`: `2 ∑ x_m b_m − ∑ x_m² = b_0² + (1 − ρ²) ∑_{m≥1} b_m²`;
* `kms_abs_summable`: the Kac–Murdock–Szegő double series is absolutely summable on `ℓ²` (Schur
  test with row sums `≤ 2/(1 − |ρ|)`, `kms_row_le`);
* `kmsInf_eq_of_sq`, `two_covInf_eq_of_sq` (**Theorem RG, square-summable form**):
  `2 ∑_m x_m b_m = ∑_k x_k² + ∑_k ∑_l ρ^{|k−l|} x_k x_l`; `kmsInf_nonneg_of_sq`;
* `covInf_pos_iff_of_sq`, `regInf_pos_iff_of_sq`: positive iff the surplus is not white noise.
-/

namespace Cochrane.ObservationalEquivalence.SquareSummableRG

open Filter Topology
open Cochrane.ObservationalEquivalence.MACovariance
open Cochrane.ObservationalEquivalence.SurplusRegression

/-! ### Elementary bounds -/

/-- Cochrane (2023), p. 501 (tool): `|ab| ≤ (a² + b²)/2`. -/
theorem abs_mul_le_half (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  rw [abs_mul]
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]

/-- Cochrane (2023), p. 501 (tool): the product of two square-summable families is summable. -/
theorem summable_mul_of_sq {ι : Type*} {f g : ι → ℝ} (hf : Summable fun k => f k ^ 2)
    (hg : Summable fun k => g k ^ 2) : Summable fun k => f k * g k :=
  Summable.of_norm_bounded ((hf.add hg).div_const 2) fun k => by
    rw [Real.norm_eq_abs]; exact abs_mul_le_half _ _

/-- Cochrane (2023), p. 501 (tool): shifts of a square-summable sequence are square-summable. -/
theorem summable_sq_shift {x : ℕ → ℝ} (hx : Summable fun k => x k ^ 2) (m : ℕ) :
    Summable fun j => x (m + j) ^ 2 :=
  ((summable_nat_add_iff m).mpr hx).congr fun j => by rw [add_comm]

/-- Cochrane (2023), p. 501 (tool): the tail of a nonnegative series is bounded by the series. -/
theorem tsum_shift_le {y : ℕ → ℝ} (hy0 : ∀ k, 0 ≤ y k) (hy : Summable y) (m : ℕ) :
    ∑' j, y (j + m) ≤ ∑' k, y k := by
  rw [← hy.sum_add_tsum_nat_add m]
  have : 0 ≤ ∑ i ∈ Finset.range m, y i := Finset.sum_nonneg fun i _ => hy0 i
  linarith

/-- Cochrane (2023), p. 501 (tool): `(ρ^j)²` is summable for `|ρ| < 1`. -/
theorem summable_pow_sq {ρ : ℝ} (hρ : |ρ| < 1) : Summable fun j : ℕ => (ρ ^ j) ^ 2 := by
  have h2 : |ρ ^ 2| < 1 := by rw [abs_pow]; nlinarith [abs_nonneg ρ]
  exact (summable_geometric_of_abs_lt_one h2).congr fun j => by rw [← pow_mul, ← pow_mul,
    mul_comm]

/-- Cochrane (2023), p. 501 (tool, weighted Cauchy–Schwarz for series):
`(∑ w_j y_j)² ≤ (∑ w_j)(∑ w_j y_j²)` for `w ≥ 0`. -/
theorem sq_tsum_le {w y : ℕ → ℝ} (hw0 : ∀ j, 0 ≤ w j) (hw : Summable w)
    (hwy : Summable fun j => w j * y j ^ 2) :
    (∑' j, w j * y j) ^ 2 ≤ (∑' j, w j) * ∑' j, w j * y j ^ 2 := by
  have hs : Summable fun j => w j * y j :=
    Summable.of_norm_bounded ((hw.add hwy).div_const 2) fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 j)]
      nlinarith [sq_nonneg (|y j| - 1), hw0 j, sq_abs (y j)]
  have hq : ∀ c : ℝ, 0 ≤ (∑' j, w j) * (c * c) + (-2 * ∑' j, w j * y j) * c +
      ∑' j, w j * y j ^ 2 := by
    intro c
    have e : ∑' j, w j * (y j - c) ^ 2 = (∑' j, w j) * (c * c) +
        (-2 * ∑' j, w j * y j) * c + ∑' j, w j * y j ^ 2 := by
      rw [← tsum_mul_right, show (-2 * ∑' j, w j * y j) * c = ∑' j, (-2 * c) * (w j * y j) by
        rw [tsum_mul_left]; ring, ← Summable.tsum_add (hw.mul_right _) (hs.mul_left _),
        ← Summable.tsum_add ((hw.mul_right _).add (hs.mul_left _)) hwy]
      exact tsum_congr fun j => by ring
    rw [← e]
    exact tsum_nonneg fun j => mul_nonneg (hw0 j) (sq_nonneg _)
  have := discrim_le_zero hq
  unfold discrim at this
  nlinarith

/-! ### The value-of-debt coefficients of a square-summable moving average -/

variable {ρ : ℝ} {x : ℕ → ℝ}

/-- Cochrane (2023), p. 501: for square-summable `x` and `|ρ| < 1`, `b_m = ∑_j ρ^j x_{m+j}`
converges absolutely. -/
theorem summable_bterm (hρ : |ρ| < 1) (hx : Summable fun k => x k ^ 2) (m : ℕ) :
    Summable fun j => ρ ^ j * x (m + j) :=
  summable_mul_of_sq (summable_pow_sq hρ) (summable_sq_shift hx m)

/-- Cochrane (2023), p. 501: the recursion `b_m = x_m + ρ b_{m+1}`. -/
theorem bInf_succ (hρ : |ρ| < 1) (hx : Summable fun k => x k ^ 2) (m : ℕ) :
    bInf ρ x m = x m + ρ * bInf ρ x (m + 1) := by
  unfold bInf
  rw [(summable_bterm hρ hx m).tsum_eq_zero_add, pow_zero, one_mul, add_zero, ← tsum_mul_left]
  congr 1
  exact tsum_congr fun j => by rw [pow_succ, show m + (j + 1) = m + 1 + j by omega]; ring

/-- Cochrane (2023), p. 501: `|b_m| ≤ ∑_j |ρ|^j |x_{m+j}|`. -/
theorem abs_bInf_le (hρ : |ρ| < 1) (hx : Summable fun k => x k ^ 2) (m : ℕ) :
    |bInf ρ x m| ≤ ∑' j, |ρ| ^ j * |x (m + j)| := by
  have hs := summable_bterm hρ hx m
  have hn := norm_tsum_le_tsum_norm (f := fun j => ρ ^ j * x (m + j))
    (by simpa only [Real.norm_eq_abs] using hs.abs)
  simp only [Real.norm_eq_abs, abs_mul, abs_pow] at hn
  exact hn

/-- Cochrane (2023), p. 501 (tool): `∑_{(m,j)} |ρ|^j x_{m+j}²` is summable. -/
theorem summable_weighted_sq (hρ : |ρ| < 1) (hx : Summable fun k => x k ^ 2) :
    Summable fun p : ℕ × ℕ => |ρ| ^ p.2 * x (p.1 + p.2) ^ 2 := by
  have h0 : ∀ p : ℕ × ℕ, 0 ≤ |ρ| ^ p.1 * x (p.2 + p.1) ^ 2 := fun p => by positivity
  have hs : Summable fun p : ℕ × ℕ => |ρ| ^ p.1 * x (p.2 + p.1) ^ 2 := by
    refine (summable_prod_of_nonneg h0).mpr ⟨fun j => ?_, ?_⟩
    · exact ((summable_nat_add_iff j).mpr hx).mul_left (|ρ| ^ j)
    refine Summable.of_nonneg_of_le (fun j => tsum_nonneg fun m => h0 (j, m)) (fun j => ?_)
      ((summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right (∑' k, x k ^ 2))
    change ∑' m, |ρ| ^ j * x (m + j) ^ 2 ≤ |ρ| ^ j * ∑' k, x k ^ 2
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (tsum_shift_le (fun k => sq_nonneg _) hx j)
      (pow_nonneg (abs_nonneg _) _)
  exact hs.prod_symm

/-- Cochrane (2023), p. 501: for square-summable `x` and `|ρ| < 1`, `b ∈ ℓ²`, so `Var(v)` is a
genuine sum. -/
theorem bInf_sq_summable_of_sq (hρ : |ρ| < 1) (hx : Summable fun k => x k ^ 2) :
    Summable fun m => bInf ρ x m ^ 2 := by
  have hr0 := abs_nonneg ρ
  have hr1 : 0 < 1 - |ρ| := by linarith
  have hgeo := summable_geometric_of_lt_one hr0 hρ
  have hD := (summable_weighted_sq hρ hx).prod
  refine Summable.of_nonneg_of_le (fun m => sq_nonneg _) (fun m => ?_)
    (hD.mul_left (∑' j : ℕ, |ρ| ^ j))
  have hcs := sq_tsum_le (w := fun j => |ρ| ^ j) (y := fun j => |x (m + j)|)
    (fun j => pow_nonneg hr0 j) hgeo (by
      simpa only [sq_abs] using
        (summable_weighted_sq hρ hx).prod_factor m)
  have h1 := abs_bInf_le hρ hx m
  have h2 : bInf ρ x m ^ 2 ≤ (∑' j, |ρ| ^ j * |x (m + j)|) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  refine h2.trans (hcs.trans (le_of_eq ?_))
  simp only [sq_abs]

/-- Cochrane (2023), p. 501: `∑_m x_m b_m` converges absolutely for square-summable `x`. -/
theorem covInf_summable_of_sq (hρ : |ρ| < 1) (hx : Summable fun k => x k ^ 2) :
    Summable fun m => x m * bInf ρ x m :=
  summable_mul_of_sq hx (bInf_sq_summable_of_sq hρ hx)

/-- Cochrane (2023), p. 501 (the LDL form for square-summable `x`):
`2 ∑ x_m b_m − ∑ x_m² = b_0² + (1 − ρ²) ∑_{m ≥ 0} b_{m+1}²`. -/
theorem two_covInf_ldl (hρ : |ρ| < 1) (hx : Summable fun k => x k ^ 2) :
    2 * covInf ρ x - ∑' k, x k ^ 2 =
      bInf ρ x 0 ^ 2 + (1 - ρ ^ 2) * ∑' m, bInf ρ x (m + 1) ^ 2 := by
  have hb := bInf_sq_summable_of_sq hρ hx
  have hb1 : Summable fun m => bInf ρ x (m + 1) ^ 2 := (summable_nat_add_iff 1).mpr hb
  have hc := covInf_summable_of_sq hρ hx
  have hterm : ∀ m, 2 * (x m * bInf ρ x m) - x m ^ 2 =
      bInf ρ x m ^ 2 - ρ ^ 2 * bInf ρ x (m + 1) ^ 2 := by
    intro m
    have := bInf_succ hρ hx m
    have hxm : x m = bInf ρ x m - ρ * bInf ρ x (m + 1) := by linarith
    rw [hxm]
    ring
  unfold covInf
  rw [← tsum_mul_left, ← Summable.tsum_sub (hc.mul_left 2) hx]
  rw [tsum_congr hterm, Summable.tsum_sub hb (hb1.mul_left _), tsum_mul_left,
    hb.tsum_eq_zero_add]
  ring

/-! ### The Kac–Murdock–Szegő double series on `ℓ²` -/

/-- Cochrane (2023), p. 501: `|ρ^{|k−l|}| = |ρ|^{|k−l|}`. -/
theorem abs_kmsKernel (ρ : ℝ) (k l : ℕ) : |kmsKernel ρ k l| = |ρ| ^ (k - l + (l - k)) := by
  unfold kmsKernel; rw [abs_pow]

/-- Cochrane (2023), p. 501: each row of the kernel is absolutely summable. -/
theorem kms_row_summable (hρ : |ρ| < 1) (k : ℕ) : Summable fun l => |kmsKernel ρ k l| := by
  refine (summable_nat_add_iff k).mp ?_
  refine (summable_geometric_of_lt_one (abs_nonneg ρ) hρ).congr fun l => ?_
  rw [abs_kmsKernel, show k - (l + k) + (l + k - k) = l by omega]

/-- Cochrane (2023), p. 501 (Schur test): the row sums of the kernel are bounded,
`∑_l |ρ|^{|k−l|} ≤ 2/(1 − |ρ|)`. -/
theorem kms_row_le (hρ : |ρ| < 1) (k : ℕ) : ∑' l, |kmsKernel ρ k l| ≤ 2 / (1 - |ρ|) := by
  have hr0 := abs_nonneg ρ
  have hr1 : 0 < 1 - |ρ| := by linarith
  have hgeo := summable_geometric_of_lt_one hr0 hρ
  rw [← (kms_row_summable hρ k).sum_add_tsum_nat_add k]
  have htail : ∑' l, |kmsKernel ρ k (l + k)| = (1 - |ρ|)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hr0 hρ]
    exact tsum_congr fun l => by rw [abs_kmsKernel, show k - (l + k) + (l + k - k) = l by omega]
  have hhead : ∑ l ∈ Finset.range k, |kmsKernel ρ k l| ≤ (1 - |ρ|)⁻¹ := by
    have e : ∑ l ∈ Finset.range k, |kmsKernel ρ k l| =
        ∑ i ∈ Finset.range k, |ρ| ^ (i + 1) := by
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun l hl => ?_
      have hl' := Finset.mem_range.mp hl
      rw [abs_kmsKernel, show k - (k - 1 - l) + (k - 1 - l - k) = l + 1 by omega]
    rw [e, ← tsum_geometric_of_lt_one hr0 hρ]
    calc ∑ i ∈ Finset.range k, |ρ| ^ (i + 1) ≤ ∑ i ∈ Finset.range k, |ρ| ^ i :=
          Finset.sum_le_sum fun i _ => pow_le_pow_of_le_one hr0 hρ.le (by omega)
      _ ≤ ∑' i, |ρ| ^ i := hgeo.sum_le_tsum _ fun i _ => pow_nonneg hr0 i
  rw [htail, div_eq_mul_inv]
  linarith

/-- Cochrane (2023), p. 501 (tool): `|ρ^{|k−l|}| ≤ 1`. -/
theorem abs_kmsKernel_le_one (hρ : |ρ| < 1) (k l : ℕ) : |kmsKernel ρ k l| ≤ 1 := by
  rw [abs_kmsKernel]; exact pow_le_one₀ (abs_nonneg _) hρ.le

/-- Cochrane (2023), p. 501 (Schur test): for square-summable `x` the Kac–Murdock–Szegő double
series `∑_{k,l} |ρ|^{|k−l|} |x_k| |x_l|` converges. -/
theorem kms_abs_summable (hρ : |ρ| < 1) (hx : Summable fun k => x k ^ 2) :
    Summable fun p : ℕ × ℕ => |kmsKernel ρ p.1 p.2| * |x p.1| * |x p.2| := by
  have hr1 : 0 < 1 - |ρ| := by linarith [abs_nonneg ρ]
  have h0 : ∀ p : ℕ × ℕ, 0 ≤ |kmsKernel ρ p.1 p.2| * x p.1 ^ 2 := fun p =>
    mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hG : Summable fun p : ℕ × ℕ => |kmsKernel ρ p.1 p.2| * x p.1 ^ 2 := by
    refine (summable_prod_of_nonneg h0).mpr ⟨fun k => ?_, ?_⟩
    · exact (kms_row_summable hρ k).mul_right (x k ^ 2)
    refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun l => h0 (k, l)) (fun k => ?_)
      (hx.mul_left (2 / (1 - |ρ|)))
    change ∑' l, |kmsKernel ρ k l| * x k ^ 2 ≤ 2 / (1 - |ρ|) * x k ^ 2
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (kms_row_le hρ k) (sq_nonneg _)
  have hG' : Summable fun p : ℕ × ℕ => |kmsKernel ρ p.1 p.2| * x p.2 ^ 2 := by
    refine hG.prod_symm.congr fun p => ?_
    change |kmsKernel ρ p.2 p.1| * x p.2 ^ 2 = |kmsKernel ρ p.1 p.2| * x p.2 ^ 2
    rw [kmsKernel_symm]
  refine Summable.of_nonneg_of_le
    (fun p => mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))
    (fun p => ?_) ((hG.add hG').div_const 2)
  have := abs_mul_le_half (x p.1) (x p.2)
  rw [abs_mul] at this
  have hk := abs_nonneg (kmsKernel ρ p.1 p.2)
  calc |kmsKernel ρ p.1 p.2| * |x p.1| * |x p.2|
      = |kmsKernel ρ p.1 p.2| * (|x p.1| * |x p.2|) := by ring
    _ ≤ |kmsKernel ρ p.1 p.2| * ((x p.1 ^ 2 + x p.2 ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left this hk
    _ = (|kmsKernel ρ p.1 p.2| * x p.1 ^ 2 + |kmsKernel ρ p.1 p.2| * x p.2 ^ 2) / 2 := by ring

/-- Cochrane (2023), p. 501 (tool): `l ↦ ρ^{|k−l|} x_l` is summable for square-summable `x`. -/
theorem kms_row_mul_summable (hρ : |ρ| < 1) (hx : Summable fun k => x k ^ 2) (k : ℕ) :
    Summable fun l => kmsKernel ρ k l * x l := by
  have hK2 : Summable fun l => kmsKernel ρ k l ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun l => by
      rw [← sq_abs]
      have h1 := abs_kmsKernel_le_one hρ k l
      have h0 := abs_nonneg (kmsKernel ρ k l)
      nlinarith) (kms_row_summable hρ k)
  exact summable_mul_of_sq hK2 hx

/-- Cochrane (2023), p. 501: a row of the Kac–Murdock–Szegő form splits into the lags before `k`
and the value-of-debt coefficient: `∑_l ρ^{|k−l|} x_l = ∑_{l<k} ρ^{k−l} x_l + b_k`. -/
theorem kms_row_eq (hρ : |ρ| < 1) (hx : Summable fun k => x k ^ 2) (k : ℕ) :
    ∑' l, kmsKernel ρ k l * x l =
      ∑ l ∈ Finset.range k, ρ ^ (k - l) * x l + bInf ρ x k := by
  rw [← (kms_row_mul_summable hρ hx k).sum_add_tsum_nat_add k]
  congr 1
  · refine Finset.sum_congr rfl fun l hl => ?_
    have := Finset.mem_range.mp hl
    rw [kmsKernel, show k - l + (l - k) = k - l by omega]
  · unfold bInf
    exact tsum_congr fun l => by
      rw [kmsKernel, show k - (l + k) + (l + k - k) = l by omega, add_comm l k]

/-- Cochrane (2023), p. 501, §24.1 p. 519 (**Kac–Murdock–Szegő form on `ℓ²`**): for
square-summable `x` and `|ρ| < 1`, `∑_k ∑_l ρ^{|k−l|} x_k x_l = 2 ∑ x_m b_m − ∑ x_m²`. -/
theorem kmsInf_eq_of_sq (hρ : |ρ| < 1) (hx : Summable fun k => x k ^ 2) :
    kmsInf ρ x = 2 * covInf ρ x - ∑' k, x k ^ 2 := by
  have hS := kms_abs_summable hρ hx
  have hc := covInf_summable_of_sq hρ hx
  set c : ℕ → ℝ := fun k => ∑ l ∈ Finset.range k, ρ ^ (k - l) * x l with hc_def
  -- the triangular part
  set T : ℕ → ℕ → ℝ := fun k l => if l < k then ρ ^ (k - l) * x k * x l else 0 with hT
  have hTs : Summable (Function.uncurry T) := hS.of_norm_bounded fun p => by
    simp only [Function.uncurry, hT, Real.norm_eq_abs]
    split_ifs with h
    · rw [abs_mul, abs_mul, abs_pow, abs_kmsKernel, show p.1 - p.2 + (p.2 - p.1) = p.1 - p.2
        by omega]
    · rw [abs_zero]; positivity
  have hrowT : ∀ k, ∑' l, T k l = x k * c k := by
    intro k
    rw [tsum_eq_sum (s := Finset.range k) fun l hl => by
      have : ¬ l < k := by simpa using hl
      simp [hT, this]]
    rw [hc_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    simp only [hT, Finset.mem_range.mp hl, ↓reduceIte]
    ring
  have hcolT : ∀ l, ∑' k, T k l = x l * (bInf ρ x l - x l) := by
    intro l
    have hsum : Summable fun k => T k l := hTs.prod_symm.prod_factor l
    rw [← hsum.sum_add_tsum_nat_add (l + 1)]
    have hz : ∑ k ∈ Finset.range (l + 1), T k l = 0 := Finset.sum_eq_zero fun k hk => by
      have : ¬ l < k := by simp only [Finset.mem_range] at hk; omega
      simp [hT, this]
    rw [hz, zero_add]
    have hb := bInf_succ hρ hx l
    have e : bInf ρ x l - x l = ρ * bInf ρ x (l + 1) := by linarith
    rw [e]
    unfold bInf
    rw [← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp only [hT, show l < j + (l + 1) by omega, ↓reduceIte]
    rw [show j + (l + 1) - l = j + 1 by omega, show l + 1 + j = j + (l + 1) by omega, pow_succ]
    ring
  have hxc : Summable fun k => x k * c k := by
    refine (hTs.prod).congr fun k => ?_
    exact hrowT k
  have hrow : ∀ k, ∑' l, kmsKernel ρ k l * x k * x l = x k * c k + x k * bInf ρ x k := by
    intro k
    rw [show (fun l => kmsKernel ρ k l * x k * x l) = fun l => x k * (kmsKernel ρ k l * x l) by
      funext l; ring, tsum_mul_left, kms_row_eq hρ hx k]
    ring
  unfold kmsInf
  rw [tsum_congr hrow, Summable.tsum_add hxc hc]
  have hswap : ∑' k, x k * c k = ∑' l, x l * (bInf ρ x l - x l) := by
    rw [← tsum_congr hrowT, ← tsum_congr hcolT]
    exact hTs.tsum_comm.symm
  rw [hswap]
  have e2 : ∑' l, x l * (bInf ρ x l - x l) = covInf ρ x - ∑' k, x k ^ 2 := by
    unfold covInf
    rw [← Summable.tsum_sub hc hx]
    exact tsum_congr fun l => by ring
  rw [e2]
  unfold covInf
  ring

/-- Cochrane (2023), p. 501, §24.1 p. 519, Online Appendix p. 593 (**Theorem RG, square-summable
moving averages**, coefficient form): `2 ∑_m x_m b_m = ∑_k x_k² + ∑_k ∑_l ρ^{|k−l|} x_k x_l`,
every sum absolutely convergent. -/
theorem two_covInf_eq_of_sq (hρ : |ρ| < 1) (hx : Summable fun k => x k ^ 2) :
    2 * covInf ρ x = ∑' k, x k ^ 2 + kmsInf ρ x := by
  rw [kmsInf_eq_of_sq hρ hx]; ring

/-- Cochrane (2023), p. 501: the Kac–Murdock–Szegő form is positive semidefinite on `ℓ²`,
`∑∑ ρ^{|k−l|} x_k x_l = b_0² + (1 − ρ²) ∑_{m≥1} b_m² ≥ 0`. -/
theorem kmsInf_nonneg_of_sq (hρ : |ρ| < 1) (hx : Summable fun k => x k ^ 2) :
    kmsInf ρ x = bInf ρ x 0 ^ 2 + (1 - ρ ^ 2) * ∑' m, bInf ρ x (m + 1) ^ 2 ∧
      0 ≤ kmsInf ρ x := by
  have h := two_covInf_ldl hρ hx
  rw [kmsInf_eq_of_sq hρ hx]
  refine ⟨h, ?_⟩
  rw [h]
  have hρ2 : 0 ≤ 1 - ρ ^ 2 := by rw [← sq_abs]; nlinarith [abs_nonneg ρ]
  exact add_nonneg (sq_nonneg _) (mul_nonneg hρ2 (tsum_nonneg fun _ => sq_nonneg _))

/-- Cochrane (2023), p. 501, §24.1 p. 519, Online Appendix p. 593 (Theorem RG, sign,
square-summable): for a square-summable surplus moving average, `∑_m a_{m+1} b_m > 0` iff the
surplus is not white noise. -/
theorem covInf_pos_iff_of_sq (hρ : |ρ| < 1) {a : ℕ → ℝ} (ha : Summable fun k => a k ^ 2) :
    0 < covInf ρ (fun k => a (k + 1)) ↔ ¬ IsIID a := by
  have hx : Summable fun k => a (k + 1) ^ 2 := (summable_nat_add_iff 1).mpr ha
  have h2 := two_covInf_eq_of_sq hρ hx
  have hk := (kmsInf_nonneg_of_sq hρ hx).2
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
    have hsq : 0 < ∑' i, a (i + 1) ^ 2 := hx.tsum_pos (fun _ => sq_nonneg _) j (by positivity)
    linarith

/-- Cochrane (2023), p. 501, §24.1 p. 519 (Theorem RG, regression form, square-summable): the
regression coefficient `∑_m a_{m+1} b_m / ∑_m b_m²` is positive iff the surplus is not white
noise. -/
theorem regInf_pos_iff_of_sq (hρ : |ρ| < 1) {a : ℕ → ℝ} (ha : Summable fun k => a k ^ 2) :
    0 < covInf ρ (fun k => a (k + 1)) / ∑' m, bInf ρ (fun k => a (k + 1)) m ^ 2 ↔
      ¬ IsIID a := by
  rw [← covInf_pos_iff_of_sq hρ ha]
  have hx : Summable fun k => a (k + 1) ^ 2 := (summable_nat_add_iff 1).mpr ha
  have hv0 : 0 ≤ ∑' m, bInf ρ (fun k => a (k + 1)) m ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have := div_nonpos_of_nonpos_of_nonneg hc hv0
    linarith
  · intro hc
    refine div_pos hc (lt_of_le_of_ne hv0 fun h0 => ?_)
    have hz : ∀ m, bInf ρ (fun k => a (k + 1)) m = 0 := by
      intro m
      by_contra hm
      have := (bInf_sq_summable_of_sq hρ hx).tsum_pos (fun _ => sq_nonneg _) m (by positivity)
      linarith
    have hcz : covInf ρ (fun k => a (k + 1)) = 0 := by
      unfold covInf
      refine (tsum_congr fun m => ?_).trans tsum_zero
      rw [hz m, mul_zero]
    linarith

/-- Cochrane (2023), p. 501 (**a square-summable but not absolutely summable surplus**): the
coefficients `a_0 = 0`, `a_{k+1} = 1/(k+1)` are square-summable but not absolutely summable, so
the results of this module go beyond `SurplusRegression`. -/
theorem harmonic_sq_not_abs :
    Summable (fun k : ℕ => (if k = 0 then (0 : ℝ) else 1 / k) ^ 2) ∧
      ¬ Summable (fun k : ℕ => |if k = 0 then (0 : ℝ) else 1 / k|) := by
  constructor
  · refine (Real.summable_one_div_nat_pow.mpr one_lt_two).congr fun k => ?_
    by_cases hk : k = 0
    · simp [hk]
    · simp [hk]
  · intro h
    apply Real.not_summable_one_div_natCast
    refine h.congr fun k => ?_
    by_cases hk : k = 0
    · simp [hk]
    · simp [hk]

end Cochrane.ObservationalEquivalence.SquareSummableRG
