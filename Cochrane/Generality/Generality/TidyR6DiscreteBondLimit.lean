/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.Links
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# The discrete bond-price recursion converges to `Q' = (i + ϖ)Q − 1` for time-varying rates

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.1 and §3.6.2–3.6.3,
pp. 53, 75–78 (the bond price of the geometric portfolio), and Online Appendix A1.2.1,
pp. 559–560 ((1.14) in discrete time, (1.17) in continuous time).

The `Links` module proved only that the constant-rate closed forms converge
(`Links.annuity_tendsto_bondPrice`). Here the rate `i(·)` varies over time. With period length
`h > 0`, a per-period continuously compounded rate `i_h(s)` (so `1 + i_h = e^{h·i_h}`) and the
per-period decay `ω_h = e^{−ϖh}`, the geometric portfolio paying the coupon `h` at `s, s+h, …`
has the discrete price

`Q_h(s) = h + e^{−h(i_h(s)+ϖ)} Q_h(s+h)`,

whose bounded (transversality) solution is the forward sum `discPrice`. We prove:

* the discrete recursion, the discrete transversality condition and uniqueness of its
  transversality solution (`discPrice_rec`, `discPrice_tvc`, `discPrice_unique`); the
  difference form `(Q_h(s+h) − Q_h(s))/h = ((1 − a_h(s))/h)Q_h(s+h) − 1` with
  `(1 − a_h(s))/h → i(s) + ϖ` (`discPrice_diff`, `tendsto_rate_of_factor`);
* an exact error representation and bound (`err_rec`, `err_le`, `delta_le`);
* **uniform convergence on compacts** `[t₀, X]` to the continuous bond price
  `ContinuousLong.bondPrice i ϖ`, for any rate continuous on `[t₀, ∞)` with `i + ϖ ≥ c > 0`
  (`tendstoUniformlyOn_Icc`), and **uniform convergence on all of `[t₀, ∞)`** when the rate is
  moreover bounded and uniformly continuous (`tendstoUniformlyOn_Ici`);
* the limit is the unique transversality solution of `Q' = (i + ϖ)Q − 1`
  (`tendsto_unique_ode_solution`); the exact-compounding special case `i_h = i`
  (`tendstoUniformlyOn_Icc_exact`, `tendstoUniformlyOn_Ici_exact`); with a constant rate the
  discrete price is the annuity of `Links.annuity_tendsto_bondPrice` (`discPrice_const`,
  `const_case`);
* where the data do not allow it: per-period rates that converge uniformly on compacts but not
  on `[0, ∞)` give convergence on every `[0, X]` but not uniformly on `[0, ∞)`
  (`not_uniform_Ici`).
-/

namespace Cochrane.Generality.TidyR6DiscreteBondLimit

open MeasureTheory Filter Topology Cochrane.Generality.ContinuousShort

/-! ### The discrete recursion -/

/-- Cochrane (2023), A1 (1.14), p. 559, with period `h`: the one-period factor
`ω_h/(1 + i_h(s)) = e^{−h(i_h(s) + ϖ)}` of the geometric portfolio. -/
noncomputable def factor (ih : ℝ → ℝ → ℝ) (ϖ h s : ℝ) : ℝ := Real.exp (-(h * (ih h s + ϖ)))

/-- Cochrane (2023), A1 (1.14), p. 559: the `k`-period discount-and-decay factor
`∏_{m<k} a_h(s + mh)`. -/
noncomputable def cumFactor (ih : ℝ → ℝ → ℝ) (ϖ h s : ℝ) (k : ℕ) : ℝ :=
  ∏ m ∈ Finset.range k, factor ih ϖ h (s + m * h)

/-- Cochrane (2023), A1 (1.14), p. 559, with period `h` and time-varying rates: the price of the
geometric portfolio paying the coupon `h` per period, `Q_h(s) = h∑_k ∏_{m<k} a_h(s + mh)`. -/
noncomputable def discPrice (ih : ℝ → ℝ → ℝ) (ϖ h s : ℝ) : ℝ := h * ∑' k, cumFactor ih ϖ h s k

/-- Cochrane (2023), A1 (1.14): the one-period factor is positive. -/
theorem factor_pos (ih : ℝ → ℝ → ℝ) (ϖ h s : ℝ) : 0 < factor ih ϖ h s := Real.exp_pos _

/-- Cochrane (2023), A1 (1.14): the one-period factor is `ω_h/(1 + i_h)` with
`ω_h = e^{−ϖh}` and `1 + i_h = e^{h·i_h}`. -/
theorem factor_eq (ih : ℝ → ℝ → ℝ) (ϖ h s : ℝ) :
    factor ih ϖ h s = Real.exp (-(ϖ * h)) / Real.exp (h * ih h s) := by
  rw [factor, ← Real.exp_sub]
  ring_nf

/-- Cochrane (2023), A1 (1.14): the cumulative factor is positive. -/
theorem cumFactor_pos (ih : ℝ → ℝ → ℝ) (ϖ h s : ℝ) (k : ℕ) : 0 < cumFactor ih ϖ h s k :=
  Finset.prod_pos fun _ _ => factor_pos ih ϖ h _

/-- Cochrane (2023), A1 (1.14): `∏_{m<0} = 1`. -/
@[simp] theorem cumFactor_zero (ih : ℝ → ℝ → ℝ) (ϖ h s : ℝ) : cumFactor ih ϖ h s 0 = 1 := by
  simp [cumFactor]

/-- Cochrane (2023), A1 (1.14): `∏_{m<k+1} a(s + mh) = a(s)·∏_{m<k} a(s + h + mh)`. -/
theorem cumFactor_succ (ih : ℝ → ℝ → ℝ) (ϖ h s : ℝ) (k : ℕ) :
    cumFactor ih ϖ h s (k + 1) = factor ih ϖ h s * cumFactor ih ϖ h (s + h) k := by
  rw [cumFactor, Finset.prod_range_succ', cumFactor, mul_comm]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun m _ => ?_
    congr 1
    push_cast
    ring

/-- Cochrane (2023), A1 (1.14): `∏_{m<k+1} a(s + mh) = ∏_{m<k} a(s + mh)·a(s + kh)`. -/
theorem cumFactor_succ' (ih : ℝ → ℝ → ℝ) (ϖ h s : ℝ) (k : ℕ) :
    cumFactor ih ϖ h s (k + 1) = cumFactor ih ϖ h s k * factor ih ϖ h (s + k * h) := by
  rw [cumFactor, Finset.prod_range_succ, cumFactor]

/-- Cochrane (2023), A1 (1.14): if the discrete rates satisfy `i_h + ϖ ≥ c` on `[t₀, ∞)`, then
from `s ≥ t₀` the cumulative factor decays at least geometrically, `≤ e^{−chk}`. -/
theorem cumFactor_le {ih : ℝ → ℝ → ℝ} {ϖ h s c t₀ : ℝ} (hh : 0 ≤ h) (hs : t₀ ≤ s)
    (hlow : ∀ u, t₀ ≤ u → c ≤ ih h u + ϖ) (k : ℕ) :
    cumFactor ih ϖ h s k ≤ Real.exp (-(c * h)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih' =>
    rw [cumFactor_succ', pow_succ]
    refine mul_le_mul ih' ?_ (factor_pos _ _ _ _).le (pow_nonneg (Real.exp_pos _).le k)
    rw [factor, Real.exp_le_exp, neg_le_neg_iff]
    have hu : t₀ ≤ s + k * h := by
      have : (0 : ℝ) ≤ k * h := mul_nonneg (Nat.cast_nonneg k) hh
      linarith
    nlinarith [hlow _ hu]

/-- Cochrane (2023), A1 (1.14): the geometric bound `e^{−x} < 1` for `x > 0`. -/
theorem exp_neg_lt_one {x : ℝ} (hx : 0 < x) : Real.exp (-x) < 1 :=
  Real.exp_lt_one_iff.mpr (by linarith)

/-- Cochrane (2023), A1 (1.14): the coupon stream of the discrete portfolio is summable. -/
theorem summable_cumFactor {ih : ℝ → ℝ → ℝ} {ϖ h s c t₀ : ℝ} (hc : 0 < c) (hh : 0 < h)
    (hs : t₀ ≤ s) (hlow : ∀ u, t₀ ≤ u → c ≤ ih h u + ϖ) :
    Summable (cumFactor ih ϖ h s) := by
  refine Summable.of_nonneg_of_le (fun k => (cumFactor_pos _ _ _ _ k).le)
    (cumFactor_le hh.le hs hlow) (summable_geometric_of_lt_one (Real.exp_pos _).le
      (exp_neg_lt_one (mul_pos hc hh)))

/-- Cochrane (2023), A1 (1.14) (auxiliary): `h/(1 − e^{−ch}) ≤ h + 1/c` for `c, h > 0`. -/
theorem geom_bound {c h : ℝ} (hc : 0 < c) (hh : 0 < h) :
    h / (1 - Real.exp (-(c * h))) ≤ h + 1 / c := by
  have hx : 0 < c * h := mul_pos hc hh
  have h1 : 0 < 1 - Real.exp (-(c * h)) := by linarith [exp_neg_lt_one hx]
  have h2 : Real.exp (-(c * h)) * (1 + c * h) ≤ 1 := by
    have := Real.add_one_le_exp (c * h)
    have he : Real.exp (-(c * h)) * Real.exp (c * h) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    nlinarith [Real.exp_pos (-(c * h))]
  rw [div_le_iff₀ h1]
  have : (h + 1 / c) * (1 - Real.exp (-(c * h))) =
      h + 1 / c - (Real.exp (-(c * h)) * (1 + c * h)) / c := by
    field_simp
    ring
  rw [this]
  have h3 : Real.exp (-(c * h)) * (1 + c * h) / c ≤ 1 / c := div_le_div_of_nonneg_right h2 hc.le
  linarith

/-- Cochrane (2023), A1 (1.14): `h∑_{k<N} e^{−chk} ≤ h + 1/c`. -/
theorem sum_geom_le {c h : ℝ} (hc : 0 < c) (hh : 0 < h) (N : ℕ) :
    h * ∑ k ∈ Finset.range N, Real.exp (-(c * h)) ^ k ≤ h + 1 / c := by
  have hx := exp_neg_lt_one (mul_pos hc hh)
  have h0 := (Real.exp_pos (-(c * h))).le
  have hs := summable_geometric_of_lt_one h0 hx
  calc h * ∑ k ∈ Finset.range N, Real.exp (-(c * h)) ^ k
      ≤ h * ∑' k, Real.exp (-(c * h)) ^ k :=
        mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ fun k _ => pow_nonneg h0 k) hh.le
    _ = h / (1 - Real.exp (-(c * h))) := by
        rw [tsum_geometric_of_lt_one h0 hx, div_eq_mul_inv]
    _ ≤ h + 1 / c := geom_bound hc hh

/-- Cochrane (2023), A1 (1.14): the discrete price is nonnegative and at most `h + 1/c`. -/
theorem discPrice_bound {ih : ℝ → ℝ → ℝ} {ϖ h s c t₀ : ℝ} (hc : 0 < c) (hh : 0 < h)
    (hs : t₀ ≤ s) (hlow : ∀ u, t₀ ≤ u → c ≤ ih h u + ϖ) :
    0 ≤ discPrice ih ϖ h s ∧ discPrice ih ϖ h s ≤ h + 1 / c := by
  have hx := exp_neg_lt_one (mul_pos hc hh)
  have h0 := (Real.exp_pos (-(c * h))).le
  have hsum := summable_cumFactor hc hh hs hlow
  refine ⟨mul_nonneg hh.le (tsum_nonneg fun k => (cumFactor_pos _ _ _ _ k).le), ?_⟩
  calc discPrice ih ϖ h s ≤ h * ∑' k, Real.exp (-(c * h)) ^ k :=
        mul_le_mul_of_nonneg_left (hsum.tsum_le_tsum (cumFactor_le hh.le hs hlow)
          (summable_geometric_of_lt_one h0 hx)) hh.le
    _ = h / (1 - Real.exp (-(c * h))) := by
        rw [tsum_geometric_of_lt_one h0 hx, div_eq_mul_inv]
    _ ≤ h + 1 / c := geom_bound hc hh

/-- Cochrane (2023), A1 (1.14), p. 559, with period `h`: the discrete bond-price recursion
`Q_h(s) = h + a_h(s)Q_h(s + h)`. -/
theorem discPrice_rec {ih : ℝ → ℝ → ℝ} {ϖ h s c t₀ : ℝ} (hc : 0 < c) (hh : 0 < h)
    (hs : t₀ ≤ s) (hlow : ∀ u, t₀ ≤ u → c ≤ ih h u + ϖ) :
    discPrice ih ϖ h s = h + factor ih ϖ h s * discPrice ih ϖ h (s + h) := by
  have hsum := summable_cumFactor hc hh hs hlow
  rw [discPrice, hsum.tsum_eq_zero_add, cumFactor_zero, discPrice]
  simp_rw [cumFactor_succ]
  rw [tsum_mul_left]
  ring

/-- Cochrane (2023), A1 (1.14) and §3.6.2: the recursion in difference form,
`(Q_h(s+h) − Q_h(s))/h = ((1 − a_h(s))/h)·Q_h(s+h) − 1`, the discrete counterpart of
`Q' = (i + ϖ)Q − 1`. -/
theorem discPrice_diff {ih : ℝ → ℝ → ℝ} {ϖ h s c t₀ : ℝ} (hc : 0 < c) (hh : 0 < h)
    (hs : t₀ ≤ s) (hlow : ∀ u, t₀ ≤ u → c ≤ ih h u + ϖ) :
    (discPrice ih ϖ h (s + h) - discPrice ih ϖ h s) / h =
      (1 - factor ih ϖ h s) / h * discPrice ih ϖ h (s + h) - 1 := by
  rw [discPrice_rec hc hh hs hlow]
  field_simp
  ring

/-- Cochrane (2023), §3.6.2 and A1 (1.17): with exact compounding the per-period rate implied by
the one-period factor converges, `(1 − e^{−h(i(s)+ϖ)})/h → i(s) + ϖ` as `h → 0⁺`. -/
theorem tendsto_rate_of_factor (i : ℝ → ℝ) (ϖ s : ℝ) :
    Tendsto (fun h => (1 - factor (fun _ u => i u) ϖ h s) / h) (𝓝[>] 0) (𝓝 (i s + ϖ)) := by
  have hd : HasDerivAt (fun h : ℝ => Real.exp (-(h * (i s + ϖ)))) (-(i s + ϖ)) 0 := by
    have h1 : HasDerivAt (fun h : ℝ => -(h * (i s + ϖ))) (-(1 * (i s + ϖ))) 0 :=
      ((hasDerivAt_id' (0 : ℝ)).mul_const (i s + ϖ)).neg
    have h2 := h1.exp
    refine h2.congr_deriv ?_
    simp
  have hs := hd.tendsto_slope_zero_right
  have h3 := hs.neg
  rw [neg_neg] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : (0 : ℝ) < h := hh
  simp only [factor, zero_add, zero_mul, neg_zero, Real.exp_zero, smul_eq_mul]
  field_simp
  ring

/-- Cochrane (2023), A1 (1.14) and A1.2.1: the discrete transversality condition
`(∏_{m<N} a_h(s + mh))·Q_h(s + Nh) → 0` holds for the forward sum. -/
theorem discPrice_tvc {ih : ℝ → ℝ → ℝ} {ϖ h s c t₀ : ℝ} (hc : 0 < c) (hh : 0 < h)
    (hs : t₀ ≤ s) (hlow : ∀ u, t₀ ≤ u → c ≤ ih h u + ϖ) :
    Tendsto (fun N : ℕ => cumFactor ih ϖ h s N * discPrice ih ϖ h (s + N * h)) atTop (𝓝 0) := by
  have hx := exp_neg_lt_one (mul_pos hc hh)
  have h0 := (Real.exp_pos (-(c * h))).le
  have hg : Tendsto (fun N : ℕ => Real.exp (-(c * h)) ^ N * (h + 1 / c)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0 hx).mul_const (h + 1 / c)
  refine squeeze_zero (fun N => mul_nonneg (cumFactor_pos _ _ _ _ N).le ?_) (fun N => ?_) hg
  · have : t₀ ≤ s + N * h := by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) hh.le]
    exact (discPrice_bound hc hh this hlow).1
  · have hN : t₀ ≤ s + N * h := by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) hh.le]
    exact mul_le_mul (cumFactor_le hh.le hs hlow N) (discPrice_bound hc hh hN hlow).2
      (discPrice_bound hc hh hN hlow).1 (pow_nonneg h0 N)

/-- Cochrane (2023), A1 (1.14) and A1.2.1: **uniqueness of the discrete bond price.** Any
solution `X` of the recursion `X(s + kh) = h + a_h(s + kh)X(s + (k+1)h)` along the grid that
satisfies the discrete transversality condition equals the forward sum `Q_h(s)`. -/
theorem discPrice_unique {ih : ℝ → ℝ → ℝ} {ϖ h s c t₀ : ℝ} (hc : 0 < c) (hh : 0 < h)
    (hs : t₀ ≤ s) (hlow : ∀ u, t₀ ≤ u → c ≤ ih h u + ϖ) {X : ℝ → ℝ}
    (hX : ∀ k : ℕ, X (s + k * h) = h + factor ih ϖ h (s + k * h) * X (s + (k + 1 : ℕ) * h))
    (hT : Tendsto (fun N : ℕ => cumFactor ih ϖ h s N * X (s + N * h)) atTop (𝓝 0)) :
    X s = discPrice ih ϖ h s := by
  have hsum := summable_cumFactor hc hh hs hlow
  have hrec : ∀ k : ℕ, (fun n : ℕ => X (s + n * h)) k =
      (fun _ : ℕ => h) k + (fun n : ℕ => factor ih ϖ h (s + n * h)) k *
        (fun n : ℕ => X (s + n * h)) (k + 1) := fun k => hX k
  have hs' : Summable fun j : ℕ => (∏ k ∈ Finset.range j,
      (fun n : ℕ => factor ih ϖ h (s + n * h)) (0 + k)) * (fun _ : ℕ => h) (0 + j) := by
    simpa [cumFactor] using hsum.mul_right h
  have h1 := (Money.pv_discount_iff hrec 0 hs').mp (by simpa [cumFactor] using hT)
  simp only [Nat.cast_zero, zero_mul, add_zero, zero_add] at h1
  rw [h1, discPrice, ← tsum_mul_left]
  exact tsum_congr fun j => by rw [cumFactor, mul_comm]

/-- Cochrane (2023), A1 (1.14) and `Links.annuity_tendsto_bondPrice`: with a constant rate the
discrete price is the annuity `h∑_j ω_hʲ/(1 + i_h)ʲ` with `ω_h = e^{−ϖh}`, `1 + i_h = e^{ih}`. -/
theorem discPrice_const (i ϖ h s : ℝ) :
    discPrice (fun _ _ => i) ϖ h s =
      h * ∑' j : ℕ, Real.exp (-ϖ * h) ^ j / Real.exp (i * h) ^ j := by
  rw [discPrice]
  congr 1
  refine tsum_congr fun j => ?_
  have hc : ∀ m : ℕ, factor (fun _ _ => i) ϖ h (s + m * h) = factor (fun _ _ => i) ϖ h 0 :=
    fun _ => rfl
  rw [cumFactor, Finset.prod_congr rfl fun m _ => hc m, Finset.prod_const, Finset.card_range,
    ← div_pow]
  congr 1
  rw [factor, ← Real.exp_sub]
  ring_nf

/-! ### The continuous bond price and the one-step error -/

/-- Cochrane (2023), §3.6.1 (auxiliary): if `r ≥ c` on `[s, u]` then `∫_s^u r ≥ c(u − s)`. -/
theorem cumRate_ge {r : ℝ → ℝ} {c s u : ℝ} (hr : ContinuousOn r (Set.Ici s)) (hsu : s ≤ u)
    (hge : ∀ x, s ≤ x → c ≤ r x) : c * (u - s) ≤ cumRate r s u := by
  have h := intervalIntegral.integral_mono_on hsu intervalIntegrable_const
    (intervalIntegrable_of_ici hr le_rfl hsu) (fun x hx => hge x hx.1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  rw [cumRate]
  linarith

/-- Cochrane (2023), §3.6.1 (auxiliary): if `|r| ≤ M` on `[s, u]` then `|∫_s^u r| ≤ M(u − s)`. -/
theorem abs_cumRate_le {r : ℝ → ℝ} {M s u : ℝ} (hsu : s ≤ u)
    (hM : ∀ x ∈ Set.Icc s u, |r x| ≤ M) : |cumRate r s u| ≤ M * (u - s) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := u) (f := r)
    (C := M) fun x hx => by
      rw [Set.uIoc_of_le hsu] at hx
      exact hM x ⟨hx.1.le, hx.2⟩
  rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ u - s)] at h

/-- Cochrane (2023), §3.6 (auxiliary): `e^{−x}` is `1`-Lipschitz on `[0, ∞)`. -/
theorem abs_exp_neg_sub_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| := by
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b → Real.exp (-a) - Real.exp (-b) ≤ b - a := by
    intro a b ha hab
    have h1 : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : 1 - (b - a) ≤ Real.exp (-(b - a)) := by
      have := Real.add_one_le_exp (-(b - a)); linarith
    have h3 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [h1]
    nlinarith [Real.exp_pos (-a), Real.exp_pos (-(b - a))]
  rcases le_total x y with hxy | hxy
  · have h := key x y hx hxy
    have h' : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · have h := key y x hy hxy
    have h' : Real.exp (-x) ≤ Real.exp (-y) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- Cochrane (2023), §3.6.2 and A1 (1.17): with `i + ϖ ≥ c > 0` on `[s, ∞)`, the continuous
bond price satisfies `0 < Q(s) ≤ 1/c`. -/
theorem bondPrice_mem {i : ℝ → ℝ} {ϖ c s : ℝ} (hi : ContinuousOn i (Set.Ici s)) (hc : 0 < c)
    (hge : ∀ u, s ≤ u → c ≤ i u + ϖ) :
    0 < ContinuousLong.bondPrice i ϖ s ∧ ContinuousLong.bondPrice i ϖ s ≤ 1 / c := by
  have hI := ContinuousLong.bondIntegrable_of_ge hi hc hge
  refine ⟨ContinuousLong.bondPrice_pos hi hI, ?_⟩
  have hJ := pvIntegrable_const hc 1 s
  rw [← pv_const_const hc 1 s, ContinuousLong.bondPrice, pv, pv]
  refine setIntegral_mono_on hI hJ measurableSet_Ioi fun u hu => ?_
  have hu' : s ≤ u := le_of_lt hu
  rw [mul_one, mul_one, disc, disc, Real.exp_le_exp, neg_le_neg_iff, cumRate_const]
  exact cumRate_ge (hi.add continuousOn_const) hu' hge

/-- Cochrane (2023), A1 (1.14) and (3.47): the one-step discretisation error
`δ_h(s) = (h − ∫_s^{s+h}D(s,u)du) + (a_h(s) − D(s, s+h))Q(s+h)`, with
`D(s,u) = exp(−∫_s^u (i + ϖ))` and `Q = ContinuousLong.bondPrice i ϖ`. -/
noncomputable def delta (ih : ℝ → ℝ → ℝ) (i : ℝ → ℝ) (ϖ h s : ℝ) : ℝ :=
  (h - ∫ τ in s..s + h, disc (fun u => i u + ϖ) s τ * 1) +
    (factor ih ϖ h s - disc (fun u => i u + ϖ) s (s + h)) * ContinuousLong.bondPrice i ϖ (s + h)

/-- Cochrane (2023), A1 (1.14) and (3.47): the error `e_h = Q_h − Q` obeys
`e_h(s) = δ_h(s) + a_h(s)e_h(s + h)`. -/
theorem err_rec {i : ℝ → ℝ} {ih : ℝ → ℝ → ℝ} {ϖ c h s t₀ : ℝ}
    (hi : ContinuousOn i (Set.Ici t₀)) (hc : 0 < c) (hh : 0 < h) (hs : t₀ ≤ s)
    (hge : ∀ u, t₀ ≤ u → c ≤ i u + ϖ) (hlow : ∀ u, t₀ ≤ u → c ≤ ih h u + ϖ) :
    discPrice ih ϖ h s - ContinuousLong.bondPrice i ϖ s = delta ih i ϖ h s +
      factor ih ϖ h s * (discPrice ih ϖ h (s + h) - ContinuousLong.bondPrice i ϖ (s + h)) := by
  have his : ContinuousOn i (Set.Ici s) := hi.mono (Set.Ici_subset_Ici.2 hs)
  have hges : ∀ u, s ≤ u → c ≤ i u + ϖ := fun u hu => hge u (hs.trans hu)
  have hI := ContinuousLong.bondIntegrable_of_ge his hc hges
  have hone := pv_finite (his.add continuousOn_const) continuousOn_const
    (ContinuousLong.bondPrice_flow his hI) (T := s + h) (by linarith)
  have hrec := discPrice_rec hc hh hs hlow
  unfold delta
  change disc (fun u => i u + ϖ) s (s + h) * ContinuousLong.bondPrice i ϖ (s + h) =
    ContinuousLong.bondPrice i ϖ s - ∫ τ in s..s + h, disc (fun u => i u + ϖ) s τ * 1 at hone
  linear_combination hrec + hone

/-- Cochrane (2023), A1 (1.14) and (3.47): **the one-step error is `O(h)·(h + modulus)`.** If
`|i + ϖ| ≤ M` and `|i(u) − i(s)| ≤ η₂` on `[s, s+h]`, and `|i_h(s) − i(s)| ≤ η₁`, then
`|δ_h(s)| ≤ h(hM + (η₁ + η₂)/c)`. -/
theorem delta_le {i : ℝ → ℝ} {ih : ℝ → ℝ → ℝ} {ϖ c h s M η₁ η₂ : ℝ}
    (hi : ContinuousOn i (Set.Ici s)) (hc : 0 < c) (hh : 0 < h)
    (hge : ∀ u, s ≤ u → c ≤ i u + ϖ) (hlow : c ≤ ih h s + ϖ)
    (hM : ∀ u ∈ Set.Icc s (s + h), |i u + ϖ| ≤ M) (h1 : |ih h s - i s| ≤ η₁)
    (h2 : ∀ u ∈ Set.Icc s (s + h), |i u - i s| ≤ η₂) :
    |delta ih i ϖ h s| ≤ h * (h * M + (η₁ + η₂) / c) := by
  have hr : ContinuousOn (fun u => i u + ϖ) (Set.Ici s) := hi.add continuousOn_const
  have hsh : s ≤ s + h := by linarith
  have hcum0 : ∀ τ, s ≤ τ → 0 ≤ cumRate (fun u => i u + ϖ) s τ := fun τ hτ =>
    le_trans (mul_nonneg hc.le (by linarith)) (cumRate_ge hr hτ hge)
  -- the first term
  have hP1 : |h - ∫ τ in s..s + h, disc (fun u => i u + ϖ) s τ * 1| ≤ M * h * h := by
    have hDint : IntervalIntegrable (fun τ => disc (fun u => i u + ϖ) s τ * 1) volume s (s + h) :=
      intervalIntegrable_of_ici ((continuousOn_disc hr).mul continuousOn_const) le_rfl hsh
    have he : h - ∫ τ in s..s + h, disc (fun u => i u + ϖ) s τ * 1 =
        ∫ τ in s..s + h, (1 - disc (fun u => i u + ϖ) s τ * 1) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hDint,
        intervalIntegral.integral_const, smul_eq_mul, mul_one, add_sub_cancel_left]
    rw [he]
    have h' := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := s + h)
      (f := fun τ => 1 - disc (fun u => i u + ϖ) s τ * 1) (C := M * h) fun τ hτ => by
        rw [Set.uIoc_of_le hsh] at hτ
        have hτ' : s ≤ τ := hτ.1.le
        have h0 := hcum0 τ hτ'
        have hb := abs_cumRate_le hτ' fun x hx => hM x ⟨hx.1, hx.2.trans hτ.2⟩
        rw [abs_of_nonneg h0] at hb
        have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM s ⟨le_rfl, hsh⟩)
        have hx1 := Real.add_one_le_exp (-cumRate (fun u => i u + ϖ) s τ)
        have hx2 : Real.exp (-cumRate (fun u => i u + ϖ) s τ) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by linarith)
        rw [Real.norm_eq_abs, mul_one, disc, abs_of_nonneg (by linarith)]
        nlinarith [hτ.2]
    rw [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hh] at h'
    exact h'
  -- the second term
  have hP2 : |factor ih ϖ h s - disc (fun u => i u + ϖ) s (s + h)| ≤ h * η₁ + h * η₂ := by
    have hx : 0 ≤ h * (ih h s + ϖ) := mul_nonneg hh.le (by linarith)
    have hb := abs_exp_neg_sub_le hx (hcum0 (s + h) hsh)
    have hsplit : h * (ih h s + ϖ) - cumRate (fun u => i u + ϖ) s (s + h) =
        h * (ih h s - i s) + ∫ τ in s..s + h, (i s - i τ) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        (intervalIntegrable_of_ici hi le_rfl hsh), intervalIntegral.integral_const, smul_eq_mul,
        add_sub_cancel_left, cumRate, intervalIntegral.integral_add
        (intervalIntegrable_of_ici hi le_rfl hsh) intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left]
      ring
    have hI2 : |∫ τ in s..s + h, (i s - i τ)| ≤ η₂ * h := by
      have h' := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := s + h)
        (f := fun τ => i s - i τ) (C := η₂) fun τ hτ => by
          rw [Set.uIoc_of_le hsh] at hτ
          rw [Real.norm_eq_abs, abs_sub_comm]
          exact h2 τ ⟨hτ.1.le, hτ.2⟩
      rwa [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hh] at h'
    refine hb.trans ?_
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos hh]
    nlinarith [mul_le_mul_of_nonneg_left h1 hh.le]
  -- the bond price
  have hQ := bondPrice_mem (hi.mono (Set.Ici_subset_Ici.2 hsh)) hc
    (fun u hu => hge u (hsh.trans hu))
  unfold delta
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_pos hQ.1]
  have hη : 0 ≤ h * η₁ + h * η₂ := (abs_nonneg _).trans hP2
  have h3 : |factor ih ϖ h s - disc (fun u => i u + ϖ) s (s + h)| *
      ContinuousLong.bondPrice i ϖ (s + h) ≤ (h * η₁ + h * η₂) * (1 / c) :=
    mul_le_mul hP2 hQ.2 hQ.1.le hη
  have h4 : (h * η₁ + h * η₂) * (1 / c) = h * ((η₁ + η₂) / c) := by ring
  nlinarith

/-- Cochrane (2023), A1 (1.14) and (3.47): **the global error bound.** If the one-step errors
along the first `N` grid points are at most `hη`, then
`|Q_h(t) − Q(t)| ≤ (h + 1/c)η + e^{−chN}(h + 2/c)`. -/
theorem err_le {i : ℝ → ℝ} {ih : ℝ → ℝ → ℝ} {ϖ c h t t₀ η : ℝ}
    (hi : ContinuousOn i (Set.Ici t₀)) (hc : 0 < c) (hh : 0 < h) (ht : t₀ ≤ t) (hη : 0 ≤ η)
    (hge : ∀ u, t₀ ≤ u → c ≤ i u + ϖ) (hlow : ∀ u, t₀ ≤ u → c ≤ ih h u + ϖ) (N : ℕ)
    (hδ : ∀ k < N, |delta ih i ϖ h (t + k * h)| ≤ h * η) :
    |discPrice ih ϖ h t - ContinuousLong.bondPrice i ϖ t| ≤
      (h + 1 / c) * η + Real.exp (-(c * h)) ^ N * (h + 2 / c) := by
  have hgrid : ∀ k : ℕ, t₀ ≤ t + k * h := fun k => by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hh.le]
  set x : ℕ → ℝ := fun k => discPrice ih ϖ h (t + k * h) - ContinuousLong.bondPrice i ϖ (t + k * h)
    with hxdef
  have hrec : ∀ k, x k = (fun k : ℕ => delta ih i ϖ h (t + k * h)) k +
      (fun k : ℕ => factor ih ϖ h (t + k * h)) k * x (k + 1) := by
    intro k
    have e : t + ((k + 1 : ℕ) : ℝ) * h = t + k * h + h := by push_cast; ring
    simp only [hxdef, e]
    exact err_rec hi hc hh (hgrid k) hge hlow
  have hit := Money.iterate_discount hrec 0 N
  simp only [zero_add] at hit
  have hx0 : x 0 = discPrice ih ϖ h t - ContinuousLong.bondPrice i ϖ t := by
    simp [hxdef]
  rw [hx0] at hit
  rw [hit]
  have hq0 := (Real.exp_pos (-(c * h))).le
  -- the sum
  have hS : |∑ j ∈ Finset.range N, (∏ k ∈ Finset.range j, factor ih ϖ h (t + k * h)) *
      delta ih i ϖ h (t + j * h)| ≤ (h + 1 / c) * η := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ Finset.range N, |(∏ k ∈ Finset.range j, factor ih ϖ h (t + k * h)) *
          delta ih i ϖ h (t + j * h)|
        ≤ ∑ j ∈ Finset.range N, Real.exp (-(c * h)) ^ j * (h * η) := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [abs_mul, abs_of_pos (show 0 < ∏ k ∈ Finset.range j, factor ih ϖ h (t + k * h) from
            cumFactor_pos ih ϖ h t j)]
          exact mul_le_mul (cumFactor_le hh.le ht hlow j) (hδ j (Finset.mem_range.mp hj))
            (abs_nonneg _) (pow_nonneg hq0 j)
      _ = η * (h * ∑ j ∈ Finset.range N, Real.exp (-(c * h)) ^ j) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
      _ ≤ η * (h + 1 / c) := mul_le_mul_of_nonneg_left (sum_geom_le hc hh N) hη
      _ = (h + 1 / c) * η := by ring
  -- the terminal term
  have hQd := discPrice_bound hc hh (hgrid N) hlow
  have hQ := bondPrice_mem (hi.mono (Set.Ici_subset_Ici.2 (hgrid N))) hc
    (fun u hu => hge u ((hgrid N).trans hu))
  have hT : |(∏ k ∈ Finset.range N, factor ih ϖ h (t + k * h)) * x N| ≤
      Real.exp (-(c * h)) ^ N * (h + 2 / c) := by
    rw [abs_mul, abs_of_pos (show 0 < ∏ k ∈ Finset.range N, factor ih ϖ h (t + k * h) from
      cumFactor_pos ih ϖ h t N)]
    refine mul_le_mul (cumFactor_le hh.le ht hlow N) ?_ (abs_nonneg _) (pow_nonneg hq0 N)
    simp only [hxdef]
    have h2c : 2 / c = 1 / c + 1 / c := by ring
    rw [abs_le]
    constructor <;> linarith [hQd.1, hQd.2, hQ.1, hQ.2]
  exact (abs_add_le _ _).trans (add_le_add hS hT)

/-! ### Uniform convergence -/

/-- Cochrane (2023), A1 (1.14) and (3.47) (auxiliary): the bound on the one-step error used in
both convergence theorems, `hM + (θc/4 + θc/4)/c ≤ θ` once `h(2(M + 1)) < θ`. -/
theorem eta_le {h M c θ : ℝ} (hh : 0 < h) (hM : 0 ≤ M) (hc : 0 < c) (hθ : 0 < θ)
    (hhM : h < θ / (2 * (M + 1))) : h * M + (c * θ / 4 + c * θ / 4) / c ≤ θ := by
  have h1 : h * (2 * (M + 1)) < θ := (lt_div_iff₀ (by positivity)).mp hhM
  have h2 : (c * θ / 4 + c * θ / 4) / c = θ / 2 := by field_simp; ring
  rw [h2]
  nlinarith

/-- Cochrane (2023), A1 (1.14) and (3.47), §3.6.2: **the discrete bond price converges to the
continuous one uniformly on `[t₀, ∞)`** when the data allow it: if the nominal rate is
uniformly continuous and bounded on `[t₀, ∞)` with `i + ϖ ≥ c > 0`, the per-period rates
`i_h → i` uniformly on `[t₀, ∞)` and are eventually bounded below (`i_h + ϖ ≥ c`), then
`Q_h → ContinuousLong.bondPrice i ϖ` uniformly on `[t₀, ∞)` as `h → 0⁺`. -/
theorem tendstoUniformlyOn_Ici {i : ℝ → ℝ} {ih : ℝ → ℝ → ℝ} {ϖ c M t₀ : ℝ} (hc : 0 < c)
    (hi : UniformContinuousOn i (Set.Ici t₀)) (hM : ∀ u, t₀ ≤ u → |i u + ϖ| ≤ M)
    (hge : ∀ u, t₀ ≤ u → c ≤ i u + ϖ)
    (hlow : ∀ᶠ h in 𝓝[>] 0, ∀ u, t₀ ≤ u → c ≤ ih h u + ϖ)
    (hconv : TendstoUniformlyOn ih i (𝓝[>] 0) (Set.Ici t₀)) :
    TendstoUniformlyOn (discPrice ih ϖ) (ContinuousLong.bondPrice i ϖ) (𝓝[>] 0)
      (Set.Ici t₀) := by
  have hic : ContinuousOn i (Set.Ici t₀) := hi.continuousOn
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM t₀ le_rfl)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hc1 : 0 < 1 + 1 / c := by positivity
  set θ := ε / (2 * (1 + 1 / c)) with hθ
  have hθ0 : 0 < θ := by positivity
  have hθε : (1 + 1 / c) * θ < ε := by
    rw [hθ]
    have : (1 + 1 / c) * (ε / (2 * (1 + 1 / c))) = ε / 2 := by field_simp
    linarith
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff.mp hi (c * θ / 4) (by positivity)
  have hconv' := Metric.tendstoUniformlyOn_iff.mp hconv (c * θ / 4) (by positivity)
  have hsmall : Set.Ioo (0 : ℝ) (min 1 (min δ (θ / (2 * (M + 1))))) ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT (by positivity)
  filter_upwards [hlow, hconv', hsmall] with h hlowh hconvh hhs
  obtain ⟨hh0, hh1⟩ := hhs
  have hh1' : h < 1 := lt_of_lt_of_le hh1 (min_le_left _ _)
  have hhδ : h < δ := lt_of_lt_of_le hh1 ((min_le_right _ _).trans (min_le_left _ _))
  have hhM : h < θ / (2 * (M + 1)) :=
    lt_of_lt_of_le hh1 ((min_le_right _ _).trans (min_le_right _ _))
  intro t ht
  have ht' : t₀ ≤ t := ht
  set η := h * M + (c * θ / 4 + c * θ / 4) / c with hηdef
  have hη0 : 0 ≤ η := by positivity
  have hηθ : η ≤ θ := eta_le hh0 hM0 hc hθ0 hhM
  have hbound : ∀ N : ℕ, |discPrice ih ϖ h t - ContinuousLong.bondPrice i ϖ t| ≤
      (h + 1 / c) * η + Real.exp (-(c * h)) ^ N * (h + 2 / c) := by
    intro N
    refine err_le hic hc hh0 ht' hη0 hge hlowh N fun k _ => ?_
    have hs : t₀ ≤ t + k * h := by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hh0.le]
    refine delta_le (hic.mono (Set.Ici_subset_Ici.2 hs)) hc hh0 (fun u hu => hge u (hs.trans hu))
      (hlowh _ hs) (fun u hu => hM u (hs.trans hu.1)) ?_ ?_
    · have h1 := hconvh _ hs
      rw [Real.dist_eq, abs_sub_comm] at h1
      exact h1.le
    · intro u hu
      have h1 := hδ u (hs.trans hu.1) _ hs (by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hu.1])]
        linarith [hu.2])
      rw [Real.dist_eq] at h1
      exact h1.le
  have hlim : Tendsto (fun N : ℕ => (h + 1 / c) * η + Real.exp (-(c * h)) ^ N * (h + 2 / c))
      atTop (𝓝 ((h + 1 / c) * η)) := by
    have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-(c * h))).le
      (exp_neg_lt_one (mul_pos hc hh0))).mul_const (h + 2 / c)
    simpa using h1.const_add ((h + 1 / c) * η)
  have hle := ge_of_tendsto' hlim hbound
  rw [Real.dist_eq, abs_sub_comm]
  have h2 : (h + 1 / c) * η ≤ (1 + 1 / c) * θ :=
    mul_le_mul (by linarith) hηθ hη0 hc1.le
  linarith

/-- Cochrane (2023), A1 (1.14) and (3.47), §3.6.2: **the discrete bond price converges to the
continuous one uniformly on compacts.** If the nominal rate is continuous on `[t₀, ∞)` with
`i + ϖ ≥ c > 0`, the per-period rates `i_h → i` uniformly on every `[t₀, X]` and are eventually
bounded below (`i_h + ϖ ≥ c` on `[t₀, ∞)`), then `Q_h → ContinuousLong.bondPrice i ϖ`
uniformly on `[t₀, X]` for every `X`, as `h → 0⁺`. No boundedness or uniform continuity of the
rate on `[t₀, ∞)` is needed. -/
theorem tendstoUniformlyOn_Icc {i : ℝ → ℝ} {ih : ℝ → ℝ → ℝ} {ϖ c t₀ : ℝ} (hc : 0 < c)
    (hi : ContinuousOn i (Set.Ici t₀)) (hge : ∀ u, t₀ ≤ u → c ≤ i u + ϖ)
    (hlow : ∀ᶠ h in 𝓝[>] 0, ∀ u, t₀ ≤ u → c ≤ ih h u + ϖ)
    (hconv : ∀ X, TendstoUniformlyOn ih i (𝓝[>] 0) (Set.Icc t₀ X)) (X : ℝ) :
    TendstoUniformlyOn (discPrice ih ϖ) (ContinuousLong.bondPrice i ϖ) (𝓝[>] 0)
      (Set.Icc t₀ X) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hc1 : 0 < 1 + 1 / c := by positivity
  have hc2 : 0 < 1 + 2 / c := by positivity
  set θ := ε / (4 * (1 + 1 / c)) with hθ
  have hθ0 : 0 < θ := by positivity
  have hθε : (1 + 1 / c) * θ = ε / 4 := by rw [hθ]; field_simp
  -- the horizon `L`
  have hexp : Tendsto (fun L : ℝ => Real.exp (-(c * L)) * (1 + 2 / c)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun L : ℝ => -(c * L)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hc)
    simpa using (Real.tendsto_exp_atBot.comp h1).mul_const (1 + 2 / c)
  obtain ⟨L, hL, hL0⟩ := ((hexp.eventually (gt_mem_nhds (half_pos hε))).and
    (eventually_gt_atTop 0)).exists
  set Y := max t₀ X + L + 1 with hY
  have hY0 : t₀ ≤ Y := by have := le_max_left t₀ X; linarith
  have hKi : ContinuousOn i (Set.Icc t₀ Y) := hi.mono Set.Icc_subset_Ici_self
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hKi.add continuousOn_const)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM t₀ ⟨le_rfl, hY0⟩)
  have hUC := isCompact_Icc.uniformContinuousOn_of_continuous hKi
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff.mp hUC (c * θ / 4) (by positivity)
  have hconv' := Metric.tendstoUniformlyOn_iff.mp (hconv Y) (c * θ / 4) (by positivity)
  have hsmall : Set.Ioo (0 : ℝ) (min 1 (min δ (θ / (2 * (M + 1))))) ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT (by positivity)
  filter_upwards [hlow, hconv', hsmall] with h hlowh hconvh hhs
  obtain ⟨hh0, hh1⟩ := hhs
  have hh1' : h < 1 := lt_of_lt_of_le hh1 (min_le_left _ _)
  have hhδ : h < δ := lt_of_lt_of_le hh1 ((min_le_right _ _).trans (min_le_left _ _))
  have hhM : h < θ / (2 * (M + 1)) :=
    lt_of_lt_of_le hh1 ((min_le_right _ _).trans (min_le_right _ _))
  intro t ht
  have ht' : t₀ ≤ t := ht.1
  have htX : t ≤ max t₀ X := ht.2.trans (le_max_right _ _)
  set N := ⌈L / h⌉₊ with hNdef
  have hN1 : L ≤ N * h := (div_le_iff₀ hh0).mp (Nat.le_ceil _)
  have hN2 : (N : ℝ) * h < L + h := by
    have h1 := Nat.ceil_lt_add_one (div_nonneg hL0.le hh0.le) (R := ℝ)
    rw [← hNdef] at h1
    have h2 := mul_lt_mul_of_pos_right h1 hh0
    rwa [add_mul, div_mul_cancel₀ _ hh0.ne', one_mul] at h2
  set η := h * M + (c * θ / 4 + c * θ / 4) / c with hηdef
  have hη0 : 0 ≤ η := by positivity
  have hηθ : η ≤ θ := eta_le hh0 hM0 hc hθ0 hhM
  have hbound := err_le hi hc hh0 ht' hη0 hge hlowh N fun k hk => by
    have hs : t₀ ≤ t + k * h := by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hh0.le]
    have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
    have hsY : t + k * h + h ≤ Y := by nlinarith
    have hmem : ∀ u ∈ Set.Icc (t + k * h) (t + k * h + h), u ∈ Set.Icc t₀ Y :=
      fun u hu => ⟨hs.trans hu.1, hu.2.trans hsY⟩
    refine delta_le (hi.mono (Set.Ici_subset_Ici.2 hs)) hc hh0
      (fun u hu => hge u (hs.trans hu)) (hlowh _ hs)
      (fun u hu => by rw [← Real.norm_eq_abs]; exact hM u (hmem u hu)) ?_ ?_
    · have h1 := hconvh _ ⟨hs, by linarith⟩
      rw [Real.dist_eq, abs_sub_comm] at h1
      exact h1.le
    · intro u hu
      have h1 := hδ u (hmem u hu) _ (hmem _ ⟨le_rfl, by linarith⟩) (by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hu.1])]
        linarith [hu.2])
      rw [Real.dist_eq] at h1
      exact h1.le
  have hq : Real.exp (-(c * h)) ^ N ≤ Real.exp (-(c * L)) := by
    rw [← Real.exp_nat_mul, Real.exp_le_exp]
    nlinarith
  have h2 : (h + 1 / c) * η ≤ (1 + 1 / c) * θ := mul_le_mul (by linarith) hηθ hη0 hc1.le
  have h3 : Real.exp (-(c * h)) ^ N * (h + 2 / c) ≤ Real.exp (-(c * L)) * (1 + 2 / c) :=
    mul_le_mul hq (by linarith) (by positivity) (Real.exp_pos _).le
  rw [Real.dist_eq, abs_sub_comm]
  linarith

/-! ### The limit solves `Q' = (i + ϖ)Q − 1`; exact compounding -/

/-- Cochrane (2023), §3.6.2, (3.47), A1 (1.17): **the limit of the discrete recursion is the
unique transversality solution of `Q' = (i + ϖ)Q − 1`.** Under the hypotheses of
`tendstoUniformlyOn_Icc`, every function `Q` that solves `Q' = (i + ϖ)Q − 1` on `[t₀, ∞)` with
the transversality condition is the uniform-on-compacts limit of the discrete prices. -/
theorem tendsto_unique_ode_solution {i Q : ℝ → ℝ} {ih : ℝ → ℝ → ℝ} {ϖ c t₀ : ℝ} (hc : 0 < c)
    (hi : ContinuousOn i (Set.Ici t₀)) (hge : ∀ u, t₀ ≤ u → c ≤ i u + ϖ)
    (hlow : ∀ᶠ h in 𝓝[>] 0, ∀ u, t₀ ≤ u → c ≤ ih h u + ϖ)
    (hconv : ∀ X, TendstoUniformlyOn ih i (𝓝[>] 0) (Set.Icc t₀ X))
    (hF : FlowOn (fun u => i u + ϖ) (fun _ => 1) Q t₀) (hT : TVC (fun u => i u + ϖ) Q t₀)
    (X : ℝ) : TendstoUniformlyOn (discPrice ih ϖ) Q (𝓝[>] 0) (Set.Icc t₀ X) := by
  have hU := ContinuousLong.bondPrice_unique hi (ContinuousLong.bondIntegrable_of_ge hi hc hge)
    hF hT
  exact (tendstoUniformlyOn_Icc hc hi hge hlow hconv X).congr_right
    fun u hu => (hU (Set.Icc_subset_Ici_self hu)).symm

/-- Cochrane (2023), A1 (1.14): exact compounding, `1 + i_h(s) = e^{h·i(s)}`, satisfies the
hypotheses on the per-period rates: it is bounded below and converges uniformly on every set. -/
theorem exact_hyps {i : ℝ → ℝ} {ϖ c t₀ : ℝ} (hge : ∀ u, t₀ ≤ u → c ≤ i u + ϖ) (S : Set ℝ) :
    (∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ u, t₀ ≤ u → c ≤ (fun (_ : ℝ) u => i u) h u + ϖ) ∧
      TendstoUniformlyOn (fun (_ : ℝ) u => i u) i (𝓝[>] 0) S := by
  refine ⟨Eventually.of_forall fun _ u hu => hge u hu, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  exact Eventually.of_forall fun _ x _ => by rw [dist_self]; exact hε

/-- Cochrane (2023), A1 (1.14), (3.47): with exact compounding `1 + i_h = e^{h·i(s)}` and decay
`ω_h = e^{−ϖh}`, the discrete price converges to `ContinuousLong.bondPrice i ϖ` uniformly on every
`[t₀, X]`, for every rate continuous on `[t₀, ∞)` with `i + ϖ ≥ c > 0`. -/
theorem tendstoUniformlyOn_Icc_exact {i : ℝ → ℝ} {ϖ c t₀ : ℝ} (hc : 0 < c)
    (hi : ContinuousOn i (Set.Ici t₀)) (hge : ∀ u, t₀ ≤ u → c ≤ i u + ϖ) (X : ℝ) :
    TendstoUniformlyOn (discPrice (fun _ u => i u) ϖ) (ContinuousLong.bondPrice i ϖ) (𝓝[>] 0)
      (Set.Icc t₀ X) :=
  tendstoUniformlyOn_Icc hc hi hge (exact_hyps hge Set.univ).1
    (fun Y => (exact_hyps hge (Set.Icc t₀ Y)).2) X

/-- Cochrane (2023), A1 (1.14), (3.47): with exact compounding the convergence is uniform on all
of `[t₀, ∞)` when the rate is bounded and uniformly continuous there. -/
theorem tendstoUniformlyOn_Ici_exact {i : ℝ → ℝ} {ϖ c M t₀ : ℝ} (hc : 0 < c)
    (hi : UniformContinuousOn i (Set.Ici t₀)) (hM : ∀ u, t₀ ≤ u → |i u + ϖ| ≤ M)
    (hge : ∀ u, t₀ ≤ u → c ≤ i u + ϖ) :
    TendstoUniformlyOn (discPrice (fun _ u => i u) ϖ) (ContinuousLong.bondPrice i ϖ) (𝓝[>] 0)
      (Set.Ici t₀) :=
  tendstoUniformlyOn_Ici hc hi hM hge (exact_hyps hge Set.univ).1
    (exact_hyps hge (Set.Ici t₀)).2

/-- Cochrane (2023), A1 (1.14), (1.17), and `Links.annuity_tendsto_bondPrice`: the constant-rate
statement of `Links` is the special case of `tendstoUniformlyOn_Ici_exact` with `i ≡ i₀`: the
annuity `h∑_j e^{−ϖhj}/e^{i₀hj}` converges to `1/(i₀ + ϖ)` uniformly in the date. -/
theorem const_case {i₀ ϖ : ℝ} (h : 0 < i₀ + ϖ) :
    TendstoUniformlyOn
      (fun h (_ : ℝ) => h * ∑' j : ℕ, Real.exp (-ϖ * h) ^ j / Real.exp (i₀ * h) ^ j)
      (fun _ => 1 / (i₀ + ϖ)) (𝓝[>] 0) (Set.Ici 0) := by
  have h1 := tendstoUniformlyOn_Ici_exact (i := fun _ => i₀) (ϖ := ϖ) (c := i₀ + ϖ)
    (M := |i₀ + ϖ|) (t₀ := 0) h uniformContinuous_const.uniformContinuousOn (fun _ _ => le_rfl)
    (fun _ _ => le_rfl)
  have e1 : discPrice (fun _ u => (fun _ => i₀) u) ϖ =
      fun h s => h * ∑' j : ℕ, Real.exp (-ϖ * h) ^ j / Real.exp (i₀ * h) ^ j := by
    funext h s
    exact discPrice_const i₀ ϖ h s
  rw [e1] at h1
  exact h1.congr_right fun s _ => ContinuousLong.bondPrice_const h s

/-! ### Where the data do not allow: convergence on compacts without uniform convergence -/

/-- Cochrane (2023), A1 (1.14) (a discretisation that is only locally consistent): the per-period
rate equals `i₀` before date `1/h` and `i₀ + 1` from then on. -/
noncomputable def jumpRate (i₀ h s : ℝ) : ℝ := if s < 1 / h then i₀ else i₀ + 1

/-- Cochrane (2023), A1 (1.14): from a date `t ≥ 1/h` on, the discrete price with `jumpRate` is the
constant-rate price at `i₀ + 1`. -/
theorem discPrice_jumpRate {i₀ ϖ h t : ℝ} (hh : 0 < h) (ht : 1 / h ≤ t) :
    discPrice (jumpRate i₀) ϖ h t = discPrice (fun _ _ => i₀ + 1) ϖ h t := by
  unfold discPrice cumFactor
  congr 2
  funext k
  refine Finset.prod_congr rfl fun m _ => ?_
  have hm : 1 / h ≤ t + m * h := by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) hh.le]
  simp only [factor, jumpRate, not_lt.mpr hm, ↓reduceIte]

/-- Cochrane (2023), A1 (1.14), (3.47): **uniform convergence on `[t₀, ∞)` needs uniformly
consistent rates.** With a constant true rate `i₀` (`i₀ + ϖ > 0`) and the per-period rates
`jumpRate i₀`, which converge to `i₀` uniformly on every compact but not on `[0, ∞)`, the
discrete prices converge to the continuous bond price uniformly on every `[0, X]`
(`tendstoUniformlyOn_Icc`) but **not** uniformly on `[0, ∞)`: from date `1/h` on they price
the rate `i₀ + 1`. -/
theorem not_uniform_Ici {i₀ ϖ : ℝ} (hc : 0 < i₀ + ϖ) :
    (∀ X, TendstoUniformlyOn (discPrice (jumpRate i₀) ϖ)
        (ContinuousLong.bondPrice (fun _ => i₀) ϖ) (𝓝[>] 0) (Set.Icc 0 X)) ∧
      ¬ TendstoUniformlyOn (discPrice (jumpRate i₀) ϖ)
        (ContinuousLong.bondPrice (fun _ => i₀) ϖ) (𝓝[>] 0) (Set.Ici 0) := by
  have hlow : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ u, (0 : ℝ) ≤ u → i₀ + ϖ ≤ jumpRate i₀ h u + ϖ :=
    Eventually.of_forall fun h u _ => by
      unfold jumpRate
      split_ifs <;> linarith
  refine ⟨fun X => tendstoUniformlyOn_Icc hc continuousOn_const (fun _ _ => le_rfl) hlow
    (fun Y => ?_) X, fun hU => ?_⟩
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hsmall : Set.Ioo (0 : ℝ) (1 / (|Y| + 1)) ∈ 𝓝[>] (0 : ℝ) :=
      Ioo_mem_nhdsGT (by positivity)
    filter_upwards [hsmall] with h hh s hs
    have h1 : s < 1 / h := by
      rw [lt_div_iff₀ hh.1]
      have h2 := (lt_div_iff₀ (by positivity : (0 : ℝ) < |Y| + 1)).mp hh.2
      have h3 : s ≤ |Y| := hs.2.trans (le_abs_self Y)
      nlinarith [hs.1, hh.1]
    simp only [jumpRate, h1, ↓reduceIte, dist_self]
    exact hε
  · have hc1 : 0 < i₀ + 1 + ϖ := by linarith
    set gap := 1 / (i₀ + ϖ) - 1 / (i₀ + 1 + ϖ) with hgap
    have hgap0 : 0 < gap := by
      rw [hgap, sub_pos]
      exact one_div_lt_one_div_of_lt hc (by linarith)
    have hA := Links.annuity_tendsto_bondPrice (i := i₀ + 1) (ϖ := ϖ) (by linarith) 0
    rw [ContinuousLong.bondPrice_const (by linarith)] at hA
    have h1 := Metric.tendstoUniformlyOn_iff.mp hU (gap / 2) (by positivity)
    have h2 := (Metric.tendsto_nhds.mp hA) (gap / 2) (by positivity)
    obtain ⟨h, ⟨hu, hv⟩, hh⟩ := ((h1.and h2).and self_mem_nhdsWithin).exists
    have hh' : (0 : ℝ) < h := hh
    have ht : (1 / h) ∈ Set.Ici (0 : ℝ) := (by positivity : (0 : ℝ) ≤ 1 / h)
    have hu' := hu (1 / h) ht
    rw [ContinuousLong.bondPrice_const hc, discPrice_jumpRate hh' le_rfl, discPrice_const]
      at hu'
    rw [Real.dist_eq] at hu' hv
    rw [abs_lt] at hu' hv
    obtain ⟨hu1, hu2⟩ := hu'
    obtain ⟨hv1, hv2⟩ := hv
    have : gap = 1 / (i₀ + ϖ) - 1 / (i₀ + 1 + ϖ) := hgap
    linarith

end Cochrane.Generality.TidyR6DiscreteBondLimit
