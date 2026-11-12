/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR6aHess

/-!
# What feasibility implies for the directions between two feasible plans

Woodford (2003), *Interest and Prices*, Chapter 3 (the exact Calvo price index and the law of
motion of price dispersion, (2.12)–(2.13), (2.20)) and Chapter 6, §2.2, pp. 396–401 (dispersion
is of second order: its first-order term vanishes on the price-index manifold).

For two plans `w` and `r = w + h` that both satisfy the exact constraints, the direction `h`
satisfies the constraints to first order with an error that is small relative to `h` when the
plans are near the steady state:

* `lin_rem`: `|k(eᶻ − 1) − z| ≤ 2|k − 1||z| + z²`.
* **`price_lin`** (price index): `|α(θ−1)hπ − (1−α)(θ−1)h_x| ≤ ⋯`, quadratic in `h` plus
  `O(|e^{(θ−1)π} − 1|)·|h|`.
* **`disp_lin`** (dispersion, using the price index): the dispersion difference satisfies
  `h_Δ − αe^{aπ_r}h_{Δ,−1} = O((ε + ρ)(|hπ| + |h_x|))`: its first-order term cancels on the
  price-index manifold (the linear coefficient of `Δ̂ = αΔ̂₋ + a[απ − (1−α)x̂]` vanishes).
-/

namespace Woodford.StabilizationWelfare.TidyR6aFeas

open Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovRamsey TidyR6aLagr TidyR6aHess

/-- Woodford (2003), App. E: `|k(eᶻ − 1) − z| ≤ 2|k − 1||z| + z²` for `|z| ≤ 1`. -/
theorem lin_rem {k z : ℝ} (hz : |z| ≤ 1) :
    |k * (Real.exp z - 1) - z| ≤ 2 * |k - 1| * |z| + z ^ 2 := by
  have e : k * (Real.exp z - 1) - z = (k - 1) * (Real.exp z - 1) + (Real.exp z - 1 - z) := by ring
  rw [e]
  have h1 := Real.abs_exp_sub_one_le hz
  have h2 := Real.abs_exp_sub_one_sub_id_le hz
  calc _ ≤ |(k - 1) * (Real.exp z - 1)| + |Real.exp z - 1 - z| := abs_add_le _ _
    _ ≤ |k - 1| * (2 * |z|) + z ^ 2 := by
        rw [abs_mul]; exact add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) h2
    _ = _ := by ring

/-- **Woodford (2003), Ch. 3, (2.20) (the price index between two feasible plans).** If the exact
price index holds at `(π, x̂)` and at `(π + h, x̂ + y)`, then
`|α(θ−1)h − (1−α)(θ−1)y| ≤ α(2|e^{(θ−1)π} − 1||(θ−1)h| + ((θ−1)h)²)
  + (1−α)(2|e^{−(θ−1)x̂} − 1||(θ−1)y| + ((θ−1)y)²)` (for `|(θ−1)h|, |(θ−1)y| ≤ 1`). -/
theorem price_lin {α b P H X Y : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hw : α * (Real.exp (b * P) - 1) + (1 - α) * (Real.exp (-(b * X)) - 1) = 0)
    (hr : α * (Real.exp (b * (P + H)) - 1) + (1 - α) * (Real.exp (-(b * (X + Y))) - 1) = 0)
    (hH : |b * H| ≤ 1) (hY : |b * Y| ≤ 1) :
    |α * (b * H) - (1 - α) * (b * Y)| ≤
      α * (2 * |Real.exp (b * P) - 1| * |b * H| + (b * H) ^ 2) +
        (1 - α) * (2 * |Real.exp (-(b * X)) - 1| * |b * Y| + (b * Y) ^ 2) := by
  have hY' : |-(b * Y)| ≤ 1 := by rwa [abs_neg]
  have e1 : Real.exp (b * (P + H)) = Real.exp (b * P) * Real.exp (b * H) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(b * (X + Y))) = Real.exp (-(b * X)) * Real.exp (-(b * Y)) := by
    rw [← Real.exp_add]; ring_nf
  have key : α * (b * H) - (1 - α) * (b * Y) =
      -(α * (Real.exp (b * P) * (Real.exp (b * H) - 1) - b * H)) -
        (1 - α) * (Real.exp (-(b * X)) * (Real.exp (-(b * Y)) - 1) - -(b * Y)) := by
    rw [e1, e2] at hr
    linear_combination hr - hw
  rw [key]
  have r1 := lin_rem (k := Real.exp (b * P)) hH
  have r2 := lin_rem (k := Real.exp (-(b * X))) hY'
  rw [abs_neg, neg_sq] at r2
  have h1α : 0 ≤ 1 - α := by linarith
  calc _ ≤ |α * (Real.exp (b * P) * (Real.exp (b * H) - 1) - b * H)| +
        |(1 - α) * (Real.exp (-(b * X)) * (Real.exp (-(b * Y)) - 1) - -(b * Y))| := by
        have := abs_sub (-(α * (Real.exp (b * P) * (Real.exp (b * H) - 1) - b * H)))
          ((1 - α) * (Real.exp (-(b * X)) * (Real.exp (-(b * Y)) - 1) - -(b * Y)))
        rwa [abs_neg] at this
    _ ≤ _ := by
        rw [abs_mul, abs_mul, abs_of_nonneg hα0, abs_of_nonneg h1α]
        exact add_le_add (mul_le_mul_of_nonneg_left r1 hα0) (mul_le_mul_of_nonneg_left r2 h1α)

/-- **Woodford (2003), Ch. 6, (2.12)–(2.13), p. 400 (the dispersion law between two feasible
plans).** With `a = θ(1+ω)`, `b = θ − 1 > 0`: if the price index and the dispersion law hold at
`(Δ₋, π, x̂, Δ)` and at `(Δ₋ + h_{Δ,−1}, π + h, x̂ + y, Δ + h_Δ)`, then
`h_Δ − αe^{a(π+h)}h_{Δ,−1}` is bounded by first-order coefficient deviations times `|h|, |y|`
plus quadratic terms: the linear term `a[αh − (1−α)y]` cancels by the price index. -/
theorem disp_lin {α a b P H X Y Dw hD w4 r4 : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hb : 0 < b)
    (ha : 0 ≤ a)
    (hw7 : α * (Real.exp (b * P) - 1) + (1 - α) * (Real.exp (-(b * X)) - 1) = 0)
    (hr7 : α * (Real.exp (b * (P + H)) - 1) + (1 - α) * (Real.exp (-(b * (X + Y))) - 1) = 0)
    (hw8 : w4 = α * Dw * Real.exp (a * P) + (1 - α) * Real.exp (-(a * X)))
    (hr8 : r4 = α * (Dw + hD) * Real.exp (a * (P + H)) + (1 - α) * Real.exp (-(a * (X + Y))))
    (hbH : |b * H| ≤ 1) (hbY : |b * Y| ≤ 1) (haH : |a * H| ≤ 1) (haY : |a * Y| ≤ 1) :
    |(r4 - w4) - α * Real.exp (a * (P + H)) * hD| ≤
      α * (2 * |Dw * Real.exp (a * P) - 1| * |a * H| + (a * H) ^ 2 +
          a / b * (2 * |Real.exp (b * P) - 1| * |b * H| + (b * H) ^ 2)) +
        (1 - α) * (2 * |Real.exp (-(a * X)) - 1| * |a * Y| + (a * Y) ^ 2 +
          a / b * (2 * |Real.exp (-(b * X)) - 1| * |b * Y| + (b * Y) ^ 2)) := by
  have haY' : |-(a * Y)| ≤ 1 := by rwa [abs_neg]
  have hbY' : |-(b * Y)| ≤ 1 := by rwa [abs_neg]
  have e1 : Real.exp (b * (P + H)) = Real.exp (b * P) * Real.exp (b * H) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(b * (X + Y))) = Real.exp (-(b * X)) * Real.exp (-(b * Y)) := by
    rw [← Real.exp_add]; ring_nf
  have e3 : Real.exp (a * (P + H)) = Real.exp (a * P) * Real.exp (a * H) := by
    rw [← Real.exp_add]; ring_nf
  have e4 : Real.exp (-(a * (X + Y))) = Real.exp (-(a * X)) * Real.exp (-(a * Y)) := by
    rw [← Real.exp_add]; ring_nf
  set R1 := Dw * Real.exp (a * P) * (Real.exp (a * H) - 1) - a * H with hR1
  set R2' := Real.exp (b * P) * (Real.exp (b * H) - 1) - b * H with hR2
  set R3 := Real.exp (-(a * X)) * (Real.exp (-(a * Y)) - 1) - -(a * Y) with hR3
  set R4 := Real.exp (-(b * X)) * (Real.exp (-(b * Y)) - 1) - -(b * Y) with hR4
  have hbne : b ≠ 0 := hb.ne'
  have key : (r4 - w4) - α * Real.exp (a * (P + H)) * hD =
      α * (R1 - a / b * R2') + (1 - α) * (R3 - a / b * R4) := by
    rw [hr8, hw8, e3, e4]
    have h7 : α * (Real.exp (b * P) * (Real.exp (b * H) - 1)) +
        (1 - α) * (Real.exp (-(b * X)) * (Real.exp (-(b * Y)) - 1)) = 0 := by
      rw [e1, e2] at hr7; linear_combination hr7 - hw7
    simp only [hR1, hR2, hR3, hR4]
    generalize Real.exp (b * P) = E1 at h7 ⊢
    generalize Real.exp (b * H) = E2' at h7 ⊢
    generalize Real.exp (-(b * X)) = E3 at h7 ⊢
    generalize Real.exp (-(b * Y)) = E4 at h7 ⊢
    field_simp
    linear_combination a * h7
  rw [key]
  have r1 := lin_rem (k := Dw * Real.exp (a * P)) haH
  have r2 := lin_rem (k := Real.exp (b * P)) hbH
  have r3 := lin_rem (k := Real.exp (-(a * X))) haY'
  have r4' := lin_rem (k := Real.exp (-(b * X))) hbY'
  rw [abs_neg, neg_sq] at r3 r4'
  have hab : 0 ≤ a / b := div_nonneg ha hb.le
  have h1α : 0 ≤ 1 - α := by linarith
  have t1 : |R1 - a / b * R2'| ≤ 2 * |Dw * Real.exp (a * P) - 1| * |a * H| + (a * H) ^ 2 +
      a / b * (2 * |Real.exp (b * P) - 1| * |b * H| + (b * H) ^ 2) := by
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · simpa [hR1, mul_assoc] using r1
    · rw [abs_mul, abs_of_nonneg hab]; exact mul_le_mul_of_nonneg_left r2 hab
  have t2 : |R3 - a / b * R4| ≤ 2 * |Real.exp (-(a * X)) - 1| * |a * Y| + (a * Y) ^ 2 +
      a / b * (2 * |Real.exp (-(b * X)) - 1| * |b * Y| + (b * Y) ^ 2) := by
    refine (abs_sub _ _).trans (add_le_add r3 ?_)
    rw [abs_mul, abs_of_nonneg hab]; exact mul_le_mul_of_nonneg_left r4' hab
  calc _ ≤ |α * (R1 - a / b * R2')| + |(1 - α) * (R3 - a / b * R4)| := abs_add_le _ _
    _ ≤ _ := by
        rw [abs_mul, abs_mul, abs_of_nonneg hα0, abs_of_nonneg h1α]
        exact add_le_add (mul_le_mul_of_nonneg_left t1 hα0) (mul_le_mul_of_nonneg_left t2 h1α)

/-! ## Discounted `ℓ²` bounds for forward and backward relations -/

open NonlinearNKMarkovRamseyTree TidyR6aTreeSum TidyR5RamseyWeighted

variable {X : Type*} (T : LagTree X)

/-- Woodford (2003), App. A.3: `|Mg| ≤ M|g|` for bounded `g`. -/
theorem abs_M_le {g : X → ℝ} (hg : Bdd g) (x : X) : |T.M g x| ≤ T.M (fun y => |g y|) x := by
  obtain ⟨B, hB⟩ := hg
  have h1 := M_nonneg T (k := fun y => |g y| - g y) (C := 2 * B)
    (fun y => by linarith [le_abs_self (g y)]) (fun y => by linarith [neg_abs_le (g y), hB y]) x
  have h2 := M_nonneg T (k := fun y => |g y| + g y) (C := 2 * B)
    (fun y => by linarith [neg_abs_le (g y)]) (fun y => by linarith [le_abs_self (g y), hB y]) x
  have e1 := congrFun (M_lin T 1 (-1) (fun y => |g y|) g) x
  have e2 := congrFun (M_lin T 1 1 (fun y => |g y|) g) x
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at e1 e2
  rw [e1] at h1
  rw [e2] at h2
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- Woodford (2003), App. A.3 (**Young's inequality**): `(u + v)² ≤ (1+κ)u² + (1 + 1/κ)v²`. -/
theorem young {u v κ : ℝ} (hκ : 0 < κ) : (u + v) ^ 2 ≤ (1 + κ) * u ^ 2 + (1 + 1 / κ) * v ^ 2 := by
  have h : 2 * u * v ≤ κ * u ^ 2 + v ^ 2 / κ := by
    rw [← sub_nonneg]
    have : κ * u ^ 2 + v ^ 2 / κ - 2 * u * v = (κ * u - v) ^ 2 / κ := by field_simp; ring
    rw [this]; positivity
  have e : (1 + 1 / κ) * v ^ 2 = v ^ 2 + v ^ 2 / κ := by field_simp
  nlinarith

/-- **Woodford (2003), App. A.3 (a forward relation controls the discounted `ℓ²` norm).** If
`|g − cMg| ≤ a₀|g| + a₁M|g| + v` with `c ≥ 0`, `a₀ < 1` and `(1+κ)(c + a₁)² < β(1 − a₀)²`, then
`S[g²] ≤ C·S[v²]` at every node, with `C = (1 + 1/κ)/((1 − a₀)²(1 − (1+κ)(c+a₁)²/((1−a₀)²β)))`. -/
theorem fwd_sq {β c a0 a1 κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hc : 0 ≤ c)
    (ha01 : a0 < 1) (hκ : 0 < κ) (hκβ : (1 + κ) * (c + a1) ^ 2 < β * (1 - a0) ^ 2)
    {g v : X → ℝ} (hg : Bdd g) (hv : Bdd v)
    (h : ∀ x, |g x - c * T.M g x| ≤ a0 * |g x| + a1 * T.M (fun y => |g y|) x + v x) (x : X) :
    S T β (fun y => g y ^ 2) x ≤ (1 + 1 / κ) / (1 - a0) ^ 2 /
      (1 - (1 + κ) * (c + a1) ^ 2 / (1 - a0) ^ 2 / β) * S T β (fun y => v y ^ 2) x := by
  have hβ : |β| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  have h1a : 0 < 1 - a0 := by linarith
  have hag : Bdd (fun y => |g y|) := by
    obtain ⟨B, hB⟩ := hg; exact ⟨B, fun y => by rw [abs_abs]; exact hB y⟩
  have hg2 : Bdd (fun y => g y ^ 2) := (hg.mul hg).congr fun y => by ring
  have hv2 : Bdd (fun y => v y ^ 2) := (hv.mul hv).congr fun y => by ring
  set κ' := (1 + κ) * (c + a1) ^ 2 / (1 - a0) ^ 2 with hκ'
  have hκ'0 : 0 ≤ κ' := by positivity
  have hκ'β : κ' < β := by rw [hκ', div_lt_iff₀ (by positivity)]; linarith
  have pt : ∀ y, g y ^ 2 ≤
      (1 + 1 / κ) / (1 - a0) ^ 2 * v y ^ 2 + κ' * T.M (fun y => g y ^ 2) y := by
    intro y
    have hM := abs_M_le T hg y
    have hJ : T.M (fun z => |g z|) y ^ 2 ≤ T.M (fun z => g z ^ 2) y := by
      have := M_sq_le T hag y
      simpa [sq_abs] using this
    have hb : (1 - a0) * |g y| ≤ (c + a1) * T.M (fun z => |g z|) y + v y := by
      have := abs_sub_abs_le_abs_sub (g y) (c * T.M g y)
      rw [abs_mul, abs_of_nonneg hc] at this
      have := h y
      nlinarith [mul_le_mul_of_nonneg_left hM hc]
    have hy := young (u := (c + a1) * T.M (fun z => |g z|) y) (v := v y) hκ
    have hsq : ((1 - a0) * |g y|) ^ 2 ≤ ((c + a1) * T.M (fun z => |g z|) y + v y) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hb 2
    have e : ((1 - a0) * |g y|) ^ 2 = (1 - a0) ^ 2 * g y ^ 2 := by rw [mul_pow, sq_abs]
    rw [e] at hsq
    have h3 : (1 - a0) ^ 2 * g y ^ 2 ≤ (1 + κ) * (c + a1) ^ 2 * T.M (fun z => g z ^ 2) y +
        (1 + 1 / κ) * v y ^ 2 := by
      have := mul_le_mul_of_nonneg_left hJ (by positivity : (0 : ℝ) ≤ (1 + κ) * (c + a1) ^ 2)
      nlinarith
    rw [hκ']
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, le_div_iff₀ (by positivity)]
    linarith
  have hfb := S_forward_bound T hβ0 hβ1 hκ'0 hκ'β hg2
    (hv2.lin hv2 ((1 + 1 / κ) / (1 - a0) ^ 2) 0)
    (fun y => sq_nonneg _) (fun y => by have := pt y; linarith) x
  rw [S_lin T hβ hv2 hv2] at hfb
  calc _ ≤ _ := hfb
    _ = _ := by rw [hκ']; ring

/-- **Woodford (2003), App. A.3 (a backward relation controls the discounted `ℓ²` norm at the
root).** If `|g − k·lag g| ≤ v` with `|k| ≤ K`, `v ≥ 0` and `(1+κ)K²β < 1`, then at every root
`S[g²] ≤ (1 + 1/κ)/(1 − (1+κ)K²β)·S[v²]`. -/
theorem bwd_sq {β K κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hKβ : (1 + κ) * K ^ 2 * β < 1)
    {g k v : X → ℝ} (hg : Bdd g) (hv : Bdd v) (hk : ∀ x, |k x| ≤ K)
    (h : ∀ x, |g x - k x * lag0 T g x| ≤ v x) {x : X} (hx : T.depth x = 0) :
    S T β (fun y => g y ^ 2) x ≤ (1 + 1 / κ) / (1 - (1 + κ) * K ^ 2 * β) *
      S T β (fun y => v y ^ 2) x := by
  have hβ : |β| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  have hg2 : Bdd (fun y => g y ^ 2) := (hg.mul hg).congr fun y => by ring
  have hv2 : Bdd (fun y => v y ^ 2) := (hv.mul hv).congr fun y => by ring
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hk x)
  have pt : ∀ y, g y ^ 2 ≤
      (1 + 1 / κ) * v y ^ 2 + ((1 + κ) * K ^ 2) * lag0 T (fun z => g z ^ 2) y := by
    intro y
    have hl : lag0 T (fun z => g z ^ 2) y = lag0 T g y ^ 2 := by
      unfold lag0; split_ifs <;> simp
    rw [hl]
    have e : g y = k y * lag0 T g y + (g y - k y * lag0 T g y) := by ring
    have hy := young (u := k y * lag0 T g y) (v := g y - k y * lag0 T g y) hκ
    rw [← e] at hy
    have h1 : (k y * lag0 T g y) ^ 2 ≤ K ^ 2 * lag0 T g y ^ 2 := by
      have hk2 : k y ^ 2 ≤ K ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hk y) 2
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hk2 (sq_nonneg _)
    have h2 : (g y - k y * lag0 T g y) ^ 2 ≤ v y ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h y) 2
    have : 0 ≤ 1 + 1 / κ := by positivity
    nlinarith
  have hb := S_backward_bound T hβ0.le hβ1 hKβ hg2 (hv2.lin hv2 (1 + 1 / κ) 0)
    (fun y => by have := pt y; linarith) hx
  rw [S_lin T hβ hv2 hv2] at hb
  calc _ ≤ _ := hb
    _ = _ := by ring

end Woodford.StabilizationWelfare.TidyR6aFeas
