/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR6aFeas

/-!
# Feasible directions near the efficient steady state: the size of `F̂`, `K̂` and `Δ` gaps

Woodford (2003), *Interest and Prices*, Chapter 3 ((2.12)–(2.13), (2.20): the exact Calvo price
index and the law of motion of dispersion) and Chapter 6, §2.2, pp. 396–401 (dispersion is of
second order).

For two feasible plans `w` and `r = w + h` near the efficient steady state, the feasibility
constraints pin down every component of `h` in terms of output and inflation gaps `h₀, h₁`:

* **`price_gap`**: the reset-price gap is controlled by inflation, `|x̂_h| ≤ 3α/(1−α)·|h₁|`.
* **`disp_gap`**: the dispersion gap follows `h_Δ − αe^{aπ_r}h_{Δ,−1} = O(η)(|h₁| + |x̂_h|)`.
* **`F_rel`**: the `F` gap follows `h_F − αβM h_F = O(η)(|h_F| + M|h_F|) + O(|h₀| + M|h₁|)`.
* **`fwd_sq'`, `bwd_sq'`, `margin`**: the forms of the discounted `ℓ²` bounds used for these
  relations, with constants uniform in the distance `η` to the steady state.
-/

namespace Woodford.StabilizationWelfare.TidyR6aGap

open Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyTree TidyR5RamseyWeighted
open TidyR6aTreeSum TidyR6aLagr TidyR6aHess TidyR6aFeas

/-! ## Node estimates -/

/-- Woodford (2003), App. E: `|k(eᶻ − 1) − z| ≤ (2c + 1)η|z|` when `|z| ≤ η ≤ 1` and
`|k − 1| ≤ cη`. -/
theorem lin_eta {k z η c : ℝ} (hz : |z| ≤ η) (hη : η ≤ 1) (hk : |k - 1| ≤ c * η) :
    |k * (Real.exp z - 1) - z| ≤ (2 * c + 1) * η * |z| := by
  have h := lin_rem (k := k) (hz.trans hη)
  have h1 : 2 * |k - 1| * |z| ≤ 2 * (c * η) * |z| := by
    have := mul_le_mul_of_nonneg_right hk (abs_nonneg z); linarith
  have h2 : z ^ 2 ≤ η * |z| := by
    rw [← sq_abs, sq]; exact mul_le_mul_of_nonneg_right hz (abs_nonneg z)
  calc _ ≤ _ := h
    _ ≤ 2 * (c * η) * |z| + η * |z| := by linarith
    _ = _ := by ring

/-- **Woodford (2003), Ch. 3, (2.20) (the reset-price gap is controlled by inflation).** If the
exact price index holds at `(π, x̂)` and at `(π + h, x̂ + y)`, all within `η` of zero with
`(θ−1)η ≤ 1/10`, then `|y| ≤ 3α/(1−α)·|h|`. -/
theorem price_gap {α b P X H Y η : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hb : 0 < b)
    (hη : b * η ≤ 1 / 10) (hP : |P| ≤ η) (hX : |X| ≤ η) (hH : |H| ≤ η) (hY : |Y| ≤ η)
    (hw : α * (Real.exp (b * P) - 1) + (1 - α) * (Real.exp (-(b * X)) - 1) = 0)
    (hr : α * (Real.exp (b * (P + H)) - 1) + (1 - α) * (Real.exp (-(b * (X + Y))) - 1) = 0) :
    |Y| ≤ 3 * α / (1 - α) * |H| := by
  have ab : ∀ {u : ℝ}, |u| ≤ η → |b * u| ≤ b * η := fun hu => by
    rw [abs_mul, abs_of_pos hb]; exact mul_le_mul_of_nonneg_left hu hb.le
  have bH := ab hH
  have bY := ab hY
  have bP := ab hP
  have bX := ab hX
  have h1 : |b * H| ≤ 1 := by linarith
  have h2 : |b * Y| ≤ 1 := by linarith
  have key := price_lin hα0.le hα1.le hw hr h1 h2
  have e1 : |Real.exp (b * P) - 1| ≤ 1 / 5 := by
    have := Real.abs_exp_sub_one_le (x := b * P) (by linarith); linarith
  have e2 : |Real.exp (-(b * X)) - 1| ≤ 1 / 5 := by
    have := Real.abs_exp_sub_one_le (x := -(b * X)) (by rw [abs_neg]; linarith)
    rw [abs_neg] at this; linarith
  have s1 : (b * H) ^ 2 ≤ |b * H| / 10 := by
    rw [← sq_abs, sq]; nlinarith [abs_nonneg (b * H)]
  have s2 : (b * Y) ^ 2 ≤ |b * Y| / 10 := by
    rw [← sq_abs, sq]; nlinarith [abs_nonneg (b * Y)]
  have t1 : 2 * |Real.exp (b * P) - 1| * |b * H| ≤ 2 / 5 * |b * H| := by
    have := mul_le_mul_of_nonneg_right e1 (abs_nonneg (b * H)); linarith
  have t2 : 2 * |Real.exp (-(b * X)) - 1| * |b * Y| ≤ 2 / 5 * |b * Y| := by
    have := mul_le_mul_of_nonneg_right e2 (abs_nonneg (b * Y)); linarith
  have h1α : 0 < 1 - α := by linarith
  have r1 : α * (2 * |Real.exp (b * P) - 1| * |b * H| + (b * H) ^ 2) ≤ α * (|b * H| / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hα0.le
  have r2 : (1 - α) * (2 * |Real.exp (-(b * X)) - 1| * |b * Y| + (b * Y) ^ 2) ≤
      (1 - α) * (|b * Y| / 2) := mul_le_mul_of_nonneg_left (by linarith) h1α.le
  have tri : (1 - α) * |b * Y| - α * |b * H| ≤ |α * (b * H) - (1 - α) * (b * Y)| := by
    have := abs_sub_abs_le_abs_sub ((1 - α) * (b * Y)) (α * (b * H))
    have eY : |(1 - α) * (b * Y)| = (1 - α) * |b * Y| := by rw [abs_mul, abs_of_pos h1α]
    have eH : |α * (b * H)| = α * |b * H| := by rw [abs_mul, abs_of_pos hα0]
    rw [eY, eH, abs_sub_comm] at this
    exact this
  have hyh : (1 - α) * |b * Y| ≤ 3 * α * |b * H| := by linarith
  rw [abs_mul, abs_mul, abs_of_pos hb] at hyh
  rw [div_mul_eq_mul_div, le_div_iff₀ h1α]
  have : b * ((1 - α) * |Y|) ≤ b * (3 * α * |H|) := by linarith
  have := le_of_mul_le_mul_left this hb
  linarith

/-- **Woodford (2003), Ch. 6, (2.12)–(2.13), p. 400 (the dispersion gap is first-order small).**
With `a, b > 0`, `aη, bη ≤ 1/10`, inflation and the reset gap of both plans within `η` of zero
and `|Δ_{−1} − 1| ≤ η`, the dispersion gap satisfies
`|h_Δ − αe^{a(π+h)}h_{Δ,−1}| ≤ (6a + 5a² + 5ab)η(|h| + |y|)`. -/
theorem disp_gap {α a b P X H Y Dw hD w4 r4 η : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (ha : 0 < a)
    (hb : 0 < b) (haη : a * η ≤ 1 / 10) (hbη : b * η ≤ 1 / 10) (hP : |P| ≤ η) (hX : |X| ≤ η)
    (hH : |H| ≤ η) (hY : |Y| ≤ η) (hDw : |Dw - 1| ≤ η)
    (hw7 : α * (Real.exp (b * P) - 1) + (1 - α) * (Real.exp (-(b * X)) - 1) = 0)
    (hr7 : α * (Real.exp (b * (P + H)) - 1) + (1 - α) * (Real.exp (-(b * (X + Y))) - 1) = 0)
    (hw8 : w4 = α * Dw * Real.exp (a * P) + (1 - α) * Real.exp (-(a * X)))
    (hr8 : r4 = α * (Dw + hD) * Real.exp (a * (P + H)) + (1 - α) * Real.exp (-(a * (X + Y)))) :
    |(r4 - w4) - α * Real.exp (a * (P + H)) * hD| ≤
      (6 * a + 5 * a ^ 2 + 5 * a * b) * η * (|H| + |Y|) := by
  have hη0 : 0 ≤ η := (abs_nonneg _).trans hP
  have mk : ∀ {c u : ℝ}, 0 < c → |u| ≤ η → |c * u| = c * |u| ∧ c * |u| ≤ c * η :=
    fun hc hu => ⟨by rw [abs_mul, abs_of_pos hc], mul_le_mul_of_nonneg_left hu hc.le⟩
  obtain ⟨aH, aH'⟩ := mk ha hH
  obtain ⟨aY, aY'⟩ := mk ha hY
  obtain ⟨bH, bH'⟩ := mk hb hH
  obtain ⟨bY, bY'⟩ := mk hb hY
  obtain ⟨aP, aP'⟩ := mk ha hP
  obtain ⟨aX, aX'⟩ := mk ha hX
  obtain ⟨bP, bP'⟩ := mk hb hP
  obtain ⟨bX, bX'⟩ := mk hb hX
  have key := disp_lin hα0.le hα1.le hb ha.le hw7 hr7 hw8 hr8 (by rw [bH]; linarith)
    (by rw [bY]; linarith) (by rw [aH]; linarith) (by rw [aY]; linarith)
  have eaP : |Real.exp (a * P) - 1| ≤ 2 * a * η := by
    have := Real.abs_exp_sub_one_le (x := a * P) (by rw [aP]; linarith); rw [aP] at this
    linarith
  have ebP : |Real.exp (b * P) - 1| ≤ 2 * b * η := by
    have := Real.abs_exp_sub_one_le (x := b * P) (by rw [bP]; linarith); rw [bP] at this
    linarith
  have eaX : |Real.exp (-(a * X)) - 1| ≤ 2 * a * η := by
    have := Real.abs_exp_sub_one_le (x := -(a * X)) (by rw [abs_neg, aX]; linarith)
    rw [abs_neg, aX] at this; linarith
  have ebX : |Real.exp (-(b * X)) - 1| ≤ 2 * b * η := by
    have := Real.abs_exp_sub_one_le (x := -(b * X)) (by rw [abs_neg, bX]; linarith)
    rw [abs_neg, bX] at this; linarith
  have eD : |Dw * Real.exp (a * P) - 1| ≤ (3 + 2 * a) * η := by
    have e : Dw * Real.exp (a * P) - 1 = (Dw - 1) * Real.exp (a * P) + (Real.exp (a * P) - 1) :=
      by ring
    have h3 := abs_mul_exp_le (k := Dw - 1) (u := a * P) (by rw [aP]; linarith)
    rw [e]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ 3 * |Dw - 1| + 2 * a * η := add_le_add h3 eaP
      _ ≤ _ := by linarith
  have hHn := abs_nonneg H
  have hYn := abs_nonneg Y
  have hab : 0 ≤ a / b := div_nonneg ha.le hb.le
  have q1 : 2 * |Dw * Real.exp (a * P) - 1| * |a * H| ≤ 2 * ((3 + 2 * a) * η) * (a * |H|) := by
    rw [aH]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left eD (by norm_num))
      (by positivity)
  have sq_le : ∀ {c u : ℝ}, 0 < c → |c * u| = c * |u| → |u| ≤ η → (c * u) ^ 2 ≤ c ^ 2 * η * |u| :=
    fun {c u} hc hcu hu => by
      rw [← sq_abs, hcu]
      have := mul_le_mul_of_nonneg_right hu (by positivity : (0 : ℝ) ≤ c ^ 2 * |u|)
      calc (c * |u|) ^ 2 = |u| * (c ^ 2 * |u|) := by ring
        _ ≤ η * (c ^ 2 * |u|) := this
        _ = _ := by ring
  have q2 := sq_le ha aH hH
  have q3 := sq_le hb bH hH
  have q4 := sq_le ha aY hY
  have q5 := sq_le hb bY hY
  have q6 : 2 * |Real.exp (b * P) - 1| * |b * H| ≤ 2 * (2 * b * η) * (b * |H|) := by
    rw [bH]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ebP (by norm_num))
      (by positivity)
  have q7 : 2 * |Real.exp (-(a * X)) - 1| * |a * Y| ≤ 2 * (2 * a * η) * (a * |Y|) := by
    rw [aY]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left eaX (by norm_num))
      (by positivity)
  have q8 : 2 * |Real.exp (-(b * X)) - 1| * |b * Y| ≤ 2 * (2 * b * η) * (b * |Y|) := by
    rw [bY]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ebX (by norm_num))
      (by positivity)
  have hbne : b ≠ 0 := hb.ne'
  have B1 : 2 * |Dw * Real.exp (a * P) - 1| * |a * H| + (a * H) ^ 2 +
      a / b * (2 * |Real.exp (b * P) - 1| * |b * H| + (b * H) ^ 2) ≤
        (6 * a + 5 * a ^ 2 + 5 * a * b) * η * |H| := by
    have := mul_le_mul_of_nonneg_left (add_le_add q6 q3) hab
    have e : a / b * (2 * (2 * b * η) * (b * |H|) + b ^ 2 * η * |H|) = 5 * a * b * η * |H| := by
      field_simp; ring
    have e2 : 2 * ((3 + 2 * a) * η) * (a * |H|) + a ^ 2 * η * |H| + 5 * a * b * η * |H| =
        (6 * a + 5 * a ^ 2 + 5 * a * b) * η * |H| := by ring
    linarith
  have B2 : 2 * |Real.exp (-(a * X)) - 1| * |a * Y| + (a * Y) ^ 2 +
      a / b * (2 * |Real.exp (-(b * X)) - 1| * |b * Y| + (b * Y) ^ 2) ≤
        (6 * a + 5 * a ^ 2 + 5 * a * b) * η * |Y| := by
    have := mul_le_mul_of_nonneg_left (add_le_add q8 q5) hab
    have e : a / b * (2 * (2 * b * η) * (b * |Y|) + b ^ 2 * η * |Y|) = 5 * a * b * η * |Y| := by
      field_simp; ring
    have : 0 ≤ 6 * a * η * |Y| := by positivity
    have e2 : 2 * (2 * a * η) * (a * |Y|) + a ^ 2 * η * |Y| + 5 * a * b * η * |Y| +
        6 * a * η * |Y| = (6 * a + 5 * a ^ 2 + 5 * a * b) * η * |Y| := by ring
    linarith
  have h1α : 0 ≤ 1 - α := by linarith
  have C0 : 0 ≤ (6 * a + 5 * a ^ 2 + 5 * a * b) * η * |H| := by positivity
  have C1 : 0 ≤ (6 * a + 5 * a ^ 2 + 5 * a * b) * η * |Y| := by positivity
  calc _ ≤ _ := key
    _ ≤ α * ((6 * a + 5 * a ^ 2 + 5 * a * b) * η * |H|) +
        (1 - α) * ((6 * a + 5 * a ^ 2 + 5 * a * b) * η * |Y|) :=
        add_le_add (mul_le_mul_of_nonneg_left B1 hα0.le) (mul_le_mul_of_nonneg_left B2 h1α)
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_right hα1.le C0
        have : 0 ≤ α * ((6 * a + 5 * a ^ 2 + 5 * a * b) * η * |Y|) := by positivity
        linarith

/-! ## Uniform discounted `ℓ²` constants -/

/-- Woodford (2003), App. A.3 (**a uniform contraction margin**): for `0 < q < 1`,
`κ = (1−q)/(4q)` and `0 ≤ t ≤ (1−q)/8`, `(1+κ)q(1+t)² ≤ (1−t)² − (1−q)/8`. -/
theorem margin {q t : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (ht0 : 0 ≤ t) (ht : t ≤ (1 - q) / 8) :
    (1 + (1 - q) / (4 * q)) * q * (1 + t) ^ 2 ≤ (1 - t) ^ 2 - (1 - q) / 8 := by
  have e : (1 + (1 - q) / (4 * q)) * q = (1 + 3 * q) / 4 := by field_simp; ring
  rw [e]
  have ht1 : t ≤ 1 / 8 := by linarith
  have h1 : (1 + t) ^ 2 ≤ 1 + 3 * t := by nlinarith
  have h2 : (1 + 3 * q) / 4 * (1 + t) ^ 2 ≤ (1 + 3 * q) / 4 * (1 + 3 * t) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith

/-- **Woodford (2003), App. A.3 (the forward bound with a margin).** If
`|g − cMg| ≤ a₀|g| + a₁M|g| + v`, `c ≥ 0`, `a₀ < 1` and `(1+κ)(c + a₁)² ≤ β((1 − a₀)² − m)` with
`m > 0`, then `S[g²] ≤ (1 + 1/κ)/m · S[v²]` at every node. -/
theorem fwd_sq' {X : Type*} (T : LagTree X) {β c a0 a1 κ m : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hc : 0 ≤ c) (ha01 : a0 < 1) (hκ : 0 < κ) (hm : 0 < m)
    (hκβ : (1 + κ) * (c + a1) ^ 2 ≤ β * ((1 - a0) ^ 2 - m))
    {g v : X → ℝ} (hg : Bdd g) (hv : Bdd v)
    (h : ∀ x, |g x - c * T.M g x| ≤ a0 * |g x| + a1 * T.M (fun y => |g y|) x + v x) (x : X) :
    S T β (fun y => g y ^ 2) x ≤ (1 + 1 / κ) / m * S T β (fun y => v y ^ 2) x := by
  have hlt : (1 + κ) * (c + a1) ^ 2 < β * (1 - a0) ^ 2 := by nlinarith
  have hS := fwd_sq T hβ0 hβ1 hc ha01 hκ hlt hg hv h x
  have hv2 : Bdd (fun y => v y ^ 2) := (hv.mul hv).congr fun y => by ring
  have hS0 := S_nonneg T hβ0.le hβ1 hv2 (fun y => sq_nonneg _) x
  have h1a : 0 < (1 - a0) ^ 2 := by have : 0 < 1 - a0 := by linarith
                                    positivity
  have eq : (1 + 1 / κ) / (1 - a0) ^ 2 / (1 - (1 + κ) * (c + a1) ^ 2 / (1 - a0) ^ 2 / β) =
      (1 + 1 / κ) / ((1 - a0) ^ 2 - (1 + κ) * (c + a1) ^ 2 / β) := by
    rw [div_div]
    congr 1
    rw [mul_sub, mul_one, div_div, mul_div_assoc', mul_div_mul_left _ _ h1a.ne']
  have hd : m ≤ (1 - a0) ^ 2 - (1 + κ) * (c + a1) ^ 2 / β := by
    rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hβ0]; linarith
  have hC : (1 + 1 / κ) / ((1 - a0) ^ 2 - (1 + κ) * (c + a1) ^ 2 / β) ≤ (1 + 1 / κ) / m :=
    div_le_div_of_nonneg_left (by positivity) hm hd
  rw [eq] at hS
  exact hS.trans (mul_le_mul_of_nonneg_right hC hS0)

/-- **Woodford (2003), App. A.3 (the backward bound with a margin).** If `|g − k·lag g| ≤ v`,
`|k| ≤ K` and `(1+κ)K²β ≤ 1 − m` with `m > 0`, then at every root
`S[g²] ≤ (1 + 1/κ)/m · S[v²]`. -/
theorem bwd_sq' {X : Type*} (T : LagTree X) {β K κ m : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hm : 0 < m) (hKβ : (1 + κ) * K ^ 2 * β ≤ 1 - m)
    {g k v : X → ℝ} (hg : Bdd g) (hv : Bdd v) (hk : ∀ x, |k x| ≤ K)
    (h : ∀ x, |g x - k x * lag0 T g x| ≤ v x) {x : X} (hx : T.depth x = 0) :
    S T β (fun y => g y ^ 2) x ≤ (1 + 1 / κ) / m * S T β (fun y => v y ^ 2) x := by
  have hS := bwd_sq T hβ0 hβ1 hκ (by linarith) hg hv hk h hx
  have hv2 : Bdd (fun y => v y ^ 2) := (hv.mul hv).congr fun y => by ring
  have hS0 := S_nonneg T hβ0.le hβ1 hv2 (fun y => sq_nonneg _) x
  have hC : (1 + 1 / κ) / (1 - (1 + κ) * K ^ 2 * β) ≤ (1 + 1 / κ) / m :=
    div_le_div_of_nonneg_left (by positivity) hm (by linarith)
  exact hS.trans (mul_le_mul_of_nonneg_right hC hS0)

/-! ## Relations along the tree -/

variable {Y : Type*} (T : LagTree Y)

/-- Woodford (2003), App. A.3: the expectation of a difference. -/
theorem M_sub (f g : Y → ℝ) (x : Y) : T.M (fun y => f y - g y) x = T.M f x - T.M g x := by
  have e := congrFun (M_lin T 1 (-1) f g) x
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at e
  exact e

/-- Woodford (2003), App. A.3: the expectation is monotone on bounded functions. -/
theorem M_mono {f g : Y → ℝ} (hf : Bdd f) (hg : Bdd g) (h : ∀ y, f y ≤ g y) (x : Y) :
    T.M f x ≤ T.M g x := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  have h1 := M_nonneg T (k := fun y => g y - f y) (C := A + B) (fun y => by linarith [h y])
    (fun y => by linarith [le_abs_self (g y), neg_le_abs (f y), hA y, hB y]) x
  rw [M_sub T] at h1
  linarith

omit T in
/-- Bounded functions: absolute values. -/
theorem bdd_abs {f : Y → ℝ} (hf : Bdd f) : Bdd (fun y => |f y|) := by
  obtain ⟨A, hA⟩ := hf
  exact ⟨A, fun y => by rw [abs_abs]; exact hA y⟩

omit T in
/-- Bounded functions: a coordinate gap between two bounded plans. -/
theorem bdd_gap {w r : Y → Fin 9 → ℝ} (hw : VBdd w) (hr : VBdd r) (i : Fin 9) :
    Bdd (fun y => r y i - w y i) :=
  ((hr.coord i).lin (hw.coord i) 1 (-1)).congr fun y => by ring

/-- Woodford (2003), Ch. 7: the lagged dispersion of `r` is that of `w` plus the lagged gap. -/
theorem lagDv_sub (Dm1 : ℝ) (w r : Y → Fin 9 → ℝ) (y : Y) :
    lagDv T Dm1 r y = lagDv T Dm1 w y + lag0 T (fun z => r z 4 - w z 4) y := by
  unfold lagDv lag0; split_ifs <;> ring

/-- **Woodford (2003), (2.12)–(2.13) and (2.20) (the dispersion gap along the tree).** For two
feasible plans with inflation, reset gaps and lagged dispersion within `η` of the efficient steady
state, the dispersion gap `g = r_Δ − w_Δ` satisfies
`|g − αe^{aπ_r}·lag g| ≤ (6a + 5a² + 5a(θ−1))η(1 + 3α/(1−α))|h₁|` at every node. -/
theorem D_rel {p : Par} (hp : p.Std) {e : Y → Fin 5 → ℝ} {w r : Y → Fin 9 → ℝ} {Dm1 : ℝ}
    (hFw : Feas T p e Dm1 w) (hFr : Feas T p e Dm1 r) {η : ℝ} (haη : aE p * η ≤ 1 / 10)
    (hbη : (p.θ - 1) * η ≤ 1 / 10)
    (hb : ∀ y, |w y 1| ≤ η ∧ |xr p (w y)| ≤ η ∧ |r y 1 - w y 1| ≤ η ∧
      |xr p (r y) - xr p (w y)| ≤ η ∧ |lagDv T Dm1 w y - 1| ≤ η) (y : Y) :
    |(r y 4 - w y 4) - p.α * Real.exp (aE p * r y 1) * lag0 T (fun z => r z 4 - w z 4) y| ≤
      (6 * aE p + 5 * aE p ^ 2 + 5 * aE p * (p.θ - 1)) * η * (1 + 3 * p.α / (1 - p.α)) *
        |r y 1 - w y 1| := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hb y
  have hb0 : 0 < p.θ - 1 := by linarith [hp.one_lt_θ]
  have ha0 : 0 < aE p := by unfold aE; nlinarith [hp.one_lt_θ, hp.ω_nonneg]
  have hw7 := (hFw y).2.2.1
  have hr7 : p.α * (Real.exp ((p.θ - 1) * (w y 1 + (r y 1 - w y 1))) - 1) +
      (1 - p.α) * (Real.exp (-((p.θ - 1) * (xr p (w y) + (xr p (r y) - xr p (w y))))) - 1) = 0 := by
    rw [show w y 1 + (r y 1 - w y 1) = r y 1 by ring,
      show xr p (w y) + (xr p (r y) - xr p (w y)) = xr p (r y) by ring]
    exact (hFr y).2.2.1
  have hw8 : w y 4 = p.α * lagDv T Dm1 w y * Real.exp (aE p * w y 1) +
      (1 - p.α) * Real.exp (-(aE p * xr p (w y))) := by linarith [(hFw y).2.2.2]
  have hr8 : r y 4 = p.α * (lagDv T Dm1 w y + lag0 T (fun z => r z 4 - w z 4) y) *
      Real.exp (aE p * (w y 1 + (r y 1 - w y 1))) +
      (1 - p.α) * Real.exp (-(aE p * (xr p (w y) + (xr p (r y) - xr p (w y))))) := by
    rw [show w y 1 + (r y 1 - w y 1) = r y 1 by ring,
      show xr p (w y) + (xr p (r y) - xr p (w y)) = xr p (r y) by ring, ← lagDv_sub T]
    linarith [(hFr y).2.2.2]
  have hD := disp_gap hp.α_pos hp.α_lt_one ha0 hb0 haη hbη h1 h2 h3 h4 h5 hw7 hr7 hw8 hr8
  have hP := price_gap hp.α_pos hp.α_lt_one hb0 hbη h1 h2 h3 h4 hw7 hr7
  rw [show w y 1 + (r y 1 - w y 1) = r y 1 by ring] at hD
  have hC : 0 ≤ (6 * aE p + 5 * aE p ^ 2 + 5 * aE p * (p.θ - 1)) * η := by
    have : 0 ≤ η := (abs_nonneg _).trans h1
    positivity
  calc _ ≤ _ := hD
    _ ≤ (6 * aE p + 5 * aE p ^ 2 + 5 * aE p * (p.θ - 1)) * η *
        (|r y 1 - w y 1| + 3 * p.α / (1 - p.α) * |r y 1 - w y 1|) :=
        mul_le_mul_of_nonneg_left (by linarith) hC
    _ = _ := by ring

/-- **Woodford (2003), Ch. 6, §2.2 and Ch. 3 (the `F` gap along the tree).** For two feasible
plans within `η` of the efficient steady state (with `θη ≤ 1/40` and `(|1−σ| + σ + 1)η ≤ 1`),
the gap `g = r_F − w_F` of the `F` recursion satisfies the forward relation
`|g − αβMg| ≤ 5θη|g| + αβ·5θη·M|g| + 6|1−σ||h₀| + 2αβ(θ−1)M|h₁|`. -/
theorem F_rel {p : Par} (hp : p.Std) {e : Y → Fin 5 → ℝ} {w r : Y → Fin 9 → ℝ} (hw : VBdd w)
    (hr : VBdd r) {Dm1 : ℝ} (hFw : Feas T p e Dm1 w) (hFr : Feas T p e Dm1 r) {η : ℝ}
    (hθη : p.θ * η ≤ 1 / 40) (hU : (|1 - p.σ| + p.σ + 1) * η ≤ 1)
    (hb : ∀ y, |e y 1| ≤ η ∧ |e y 2| ≤ η ∧ |w y 0| ≤ η ∧ |w y 1| ≤ η ∧ |w y 2| ≤ η ∧
      |r y 0 - w y 0| ≤ η ∧ |r y 1 - w y 1| ≤ η ∧ |r y 2 - w y 2| ≤ η) (x : Y) :
    |(r x 2 - w x 2) - p.α * p.β * T.M (fun y => r y 2 - w y 2) x| ≤
      5 * p.θ * η * |r x 2 - w x 2| +
        p.α * p.β * (5 * p.θ * η) * T.M (fun y => |r y 2 - w y 2|) x +
        (6 * |1 - p.σ| * |r x 0 - w x 0| +
          2 * p.α * p.β * (p.θ - 1) * T.M (fun y => |r y 1 - w y 1|) x) := by
  have hθ1 := hp.one_lt_θ
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hb x).1
  have hηθ : η ≤ p.θ * η := by nlinarith
  have hη1 : η ≤ 1 := by linarith
  have hθη1 : p.θ * η ≤ 1 := by linarith
  have ht1 : 5 * p.θ * η ≤ 1 := by linarith
  have hσ := hp.σ_pos
  have hab0 : 0 < p.α * p.β := mul_pos hp.α_pos hp.β_pos
  have hab1 := hp.ab_lt_one
  obtain ⟨he1, he2, hw0, hw1, hw2, hh0, hh1, hh2⟩ := hb x
  -- the key identity
  have F0r := (hFr x).1
  have F0w := (hFw x).1
  have e1 : Real.exp (r x 2) = Real.exp (w x 2) * Real.exp (r x 2 - w x 2) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp ((1 - p.σ) * r x 0 + p.σ * e x 1 + e x 2) =
      Real.exp ((1 - p.σ) * w x 0 + p.σ * e x 1 + e x 2) *
        Real.exp ((1 - p.σ) * (r x 0 - w x 0)) := by
    rw [← Real.exp_add]; ring_nf
  have key : (r x 2 - w x 2) - p.α * p.β * T.M (fun y => r y 2 - w y 2) x =
      ((r x 2 - w x 2) - Real.exp (w x 2) * (Real.exp (r x 2 - w x 2) - 1)) +
        (1 - p.α * p.β) * Real.exp ((1 - p.σ) * w x 0 + p.σ * e x 1 + e x 2) *
          (Real.exp ((1 - p.σ) * (r x 0 - w x 0)) - 1) +
        p.α * p.β * T.M (fun y => Real.exp ((p.θ - 1) * r y 1 + r y 2) -
          Real.exp ((p.θ - 1) * w y 1 + w y 2) - (r y 2 - w y 2)) x := by
    have hM : T.M (fun y => Real.exp ((p.θ - 1) * r y 1 + r y 2) -
        Real.exp ((p.θ - 1) * w y 1 + w y 2) - (r y 2 - w y 2)) x =
        T.M (fun y => Real.exp ((p.θ - 1) * r y 1 + r y 2)) x -
          T.M (fun y => Real.exp ((p.θ - 1) * w y 1 + w y 2)) x -
          T.M (fun y => r y 2 - w y 2) x := by
      rw [M_sub T (fun y => Real.exp ((p.θ - 1) * r y 1 + r y 2) -
          Real.exp ((p.θ - 1) * w y 1 + w y 2)) (fun y => r y 2 - w y 2) x,
        M_sub T (fun y => Real.exp ((p.θ - 1) * r y 1 + r y 2))
          (fun y => Real.exp ((p.θ - 1) * w y 1 + w y 2)) x]
    rw [hM]
    linear_combination F0r - F0w - e1 + (1 - p.α * p.β) * e2
  rw [key]
  -- the current-period estimates
  have B1 : |(r x 2 - w x 2) - Real.exp (w x 2) * (Real.exp (r x 2 - w x 2) - 1)| ≤
      5 * p.θ * η * |r x 2 - w x 2| := by
    have hk : |Real.exp (w x 2) - 1| ≤ 2 * η := by
      have := Real.abs_exp_sub_one_le (x := w x 2) (by linarith); linarith
    have := lin_eta (k := Real.exp (w x 2)) hh2 hη1 hk
    rw [abs_sub_comm]
    calc _ ≤ _ := this
      _ = 5 * η * |r x 2 - w x 2| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  have B2 : |(1 - p.α * p.β) * Real.exp ((1 - p.σ) * w x 0 + p.σ * e x 1 + e x 2) *
      (Real.exp ((1 - p.σ) * (r x 0 - w x 0)) - 1)| ≤ 6 * |1 - p.σ| * |r x 0 - w x 0| := by
    have hu : |(1 - p.σ) * w x 0 + p.σ * e x 1 + e x 2| ≤ 1 := by
      have a1 : |(1 - p.σ) * w x 0| ≤ |1 - p.σ| * η := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left hw0 (abs_nonneg _)
      have a2 : |p.σ * e x 1| ≤ p.σ * η := by
        rw [abs_mul, abs_of_pos hσ]; exact mul_le_mul_of_nonneg_left he1 hσ.le
      have := abs_add_le ((1 - p.σ) * w x 0 + p.σ * e x 1) (e x 2)
      have := abs_add_le ((1 - p.σ) * w x 0) (p.σ * e x 1)
      linarith
    have hz : |(1 - p.σ) * (r x 0 - w x 0)| ≤ |1 - p.σ| * η := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hh0 (abs_nonneg _)
    have hz1 : |(1 - p.σ) * (r x 0 - w x 0)| ≤ 1 := by
      have : |1 - p.σ| * η ≤ (|1 - p.σ| + p.σ + 1) * η := by nlinarith
      linarith
    have h3 := abs_mul_exp_le (k := (1 : ℝ)) hu
    rw [one_mul, abs_one, mul_one] at h3
    have h4 := Real.abs_exp_sub_one_le hz1
    rw [abs_mul (1 - p.σ)] at h4
    have hs : |1 - p.α * p.β| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    rw [abs_mul, abs_mul]
    calc _ ≤ 1 * 3 * (2 * (|1 - p.σ| * |r x 0 - w x 0|)) := by
          apply mul_le_mul (mul_le_mul hs h3 (abs_nonneg _) (by norm_num)) h4 (abs_nonneg _)
            (by norm_num)
      _ = _ := by ring
  -- the expectation term
  set t := 5 * p.θ * η with ht
  have hg1 := bdd_gap hw hr 1
  have hg2 := bdd_gap hw hr 2
  have hfw : Bdd (fun y => Real.exp ((p.θ - 1) * w y 1 + w y 2)) :=
    bdd_exp (((hw.coord 1).lin (hw.coord 2) (p.θ - 1) 1).congr fun y => by ring)
  have hfr : Bdd (fun y => Real.exp ((p.θ - 1) * r y 1 + r y 2)) :=
    bdd_exp (((hr.coord 1).lin (hr.coord 2) (p.θ - 1) 1).congr fun y => by ring)
  have hφ : Bdd (fun y => Real.exp ((p.θ - 1) * r y 1 + r y 2) -
      Real.exp ((p.θ - 1) * w y 1 + w y 2) - (r y 2 - w y 2)) :=
    ((hfr.lin hfw 1 (-1)).lin hg2 1 (-1)).congr fun y => by ring
  have hψ : Bdd (fun y => t * |r y 2 - w y 2| + 2 * (p.θ - 1) * |r y 1 - w y 1|) :=
    (bdd_abs hg2).lin (bdd_abs hg1) t (2 * (p.θ - 1))
  have pt : ∀ y, |Real.exp ((p.θ - 1) * r y 1 + r y 2) - Real.exp ((p.θ - 1) * w y 1 + w y 2) -
      (r y 2 - w y 2)| ≤ t * |r y 2 - w y 2| + 2 * (p.θ - 1) * |r y 1 - w y 1| := by
    intro y
    obtain ⟨-, -, -, hw1', hw2', -, hh1', hh2'⟩ := hb y
    have hb0 : 0 < p.θ - 1 := by linarith
    have eu : ∀ {u v : ℝ}, |u| ≤ η → |v| ≤ η → |(p.θ - 1) * u + v| ≤ p.θ * η := by
      intro u v hu hv
      have := abs_add_le ((p.θ - 1) * u) v
      rw [abs_mul, abs_of_pos hb0] at this
      have := mul_le_mul_of_nonneg_left hu hb0.le
      linarith
    have hz := eu hh1' hh2'
    have hu := eu hw1' hw2'
    have hk : |Real.exp ((p.θ - 1) * w y 1 + w y 2) - 1| ≤ 2 * (p.θ * η) := by
      have := Real.abs_exp_sub_one_le (hu.trans hθη1); linarith
    have L := lin_eta hz hθη1 hk
    have e3 : Real.exp ((p.θ - 1) * r y 1 + r y 2) - Real.exp ((p.θ - 1) * w y 1 + w y 2) -
        (r y 2 - w y 2) = (Real.exp ((p.θ - 1) * w y 1 + w y 2) *
          (Real.exp ((p.θ - 1) * (r y 1 - w y 1) + (r y 2 - w y 2)) - 1) -
            ((p.θ - 1) * (r y 1 - w y 1) + (r y 2 - w y 2))) + (p.θ - 1) * (r y 1 - w y 1) := by
      have : Real.exp ((p.θ - 1) * r y 1 + r y 2) = Real.exp ((p.θ - 1) * w y 1 + w y 2) *
          Real.exp ((p.θ - 1) * (r y 1 - w y 1) + (r y 2 - w y 2)) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]; ring
    rw [e3]
    have hz' : |(p.θ - 1) * (r y 1 - w y 1) + (r y 2 - w y 2)| ≤
        (p.θ - 1) * |r y 1 - w y 1| + |r y 2 - w y 2| := by
      have := abs_add_le ((p.θ - 1) * (r y 1 - w y 1)) (r y 2 - w y 2)
      rwa [abs_mul, abs_of_pos hb0] at this
    have ht0 : 0 ≤ t := by positivity
    have L' : |Real.exp ((p.θ - 1) * w y 1 + w y 2) *
        (Real.exp ((p.θ - 1) * (r y 1 - w y 1) + (r y 2 - w y 2)) - 1) -
          ((p.θ - 1) * (r y 1 - w y 1) + (r y 2 - w y 2))| ≤
          t * ((p.θ - 1) * |r y 1 - w y 1| + |r y 2 - w y 2|) := by
      calc _ ≤ _ := L
        _ = t * |(p.θ - 1) * (r y 1 - w y 1) + (r y 2 - w y 2)| := by rw [ht]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hz' ht0
    have h5 := abs_add_le (Real.exp ((p.θ - 1) * w y 1 + w y 2) *
        (Real.exp ((p.θ - 1) * (r y 1 - w y 1) + (r y 2 - w y 2)) - 1) -
          ((p.θ - 1) * (r y 1 - w y 1) + (r y 2 - w y 2))) ((p.θ - 1) * (r y 1 - w y 1))
    rw [abs_mul (p.θ - 1), abs_of_pos hb0] at h5
    have h6 : t * ((p.θ - 1) * |r y 1 - w y 1|) ≤ (p.θ - 1) * |r y 1 - w y 1| := by
      have : 0 ≤ (p.θ - 1) * |r y 1 - w y 1| := by positivity
      nlinarith
    linarith
  have B3 : |T.M (fun y => Real.exp ((p.θ - 1) * r y 1 + r y 2) -
      Real.exp ((p.θ - 1) * w y 1 + w y 2) - (r y 2 - w y 2)) x| ≤
        t * T.M (fun y => |r y 2 - w y 2|) x + 2 * (p.θ - 1) * T.M (fun y => |r y 1 - w y 1|) x
      := by
    have h1 := abs_M_le T hφ x
    have h2 := M_mono T (bdd_abs hφ) hψ pt x
    rw [congrFun (M_lin T t (2 * (p.θ - 1)) (fun y => |r y 2 - w y 2|)
      (fun y => |r y 1 - w y 1|)) x] at h2
    linarith
  have B3' := mul_le_mul_of_nonneg_left B3 hab0.le
  have := abs_add_le (((r x 2 - w x 2) - Real.exp (w x 2) * (Real.exp (r x 2 - w x 2) - 1)) +
    (1 - p.α * p.β) * Real.exp ((1 - p.σ) * w x 0 + p.σ * e x 1 + e x 2) *
      (Real.exp ((1 - p.σ) * (r x 0 - w x 0)) - 1))
    (p.α * p.β * T.M (fun y => Real.exp ((p.θ - 1) * r y 1 + r y 2) -
      Real.exp ((p.θ - 1) * w y 1 + w y 2) - (r y 2 - w y 2)) x)
  have := abs_add_le ((r x 2 - w x 2) - Real.exp (w x 2) * (Real.exp (r x 2 - w x 2) - 1))
    ((1 - p.α * p.β) * Real.exp ((1 - p.σ) * w x 0 + p.σ * e x 1 + e x 2) *
      (Real.exp ((1 - p.σ) * (r x 0 - w x 0)) - 1))
  rw [abs_mul (p.α * p.β), abs_of_pos hab0] at *
  linarith

end Woodford.StabilizationWelfare.TidyR6aGap
