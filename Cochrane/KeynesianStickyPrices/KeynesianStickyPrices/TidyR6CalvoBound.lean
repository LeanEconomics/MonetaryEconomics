/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR6CalvoPC

/-!
# An explicit quadratic bound on the Calvo disturbance

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, eq. (17.17), p. 407, and
Chapter 5, §5.1, p. 118.

TidyR6CalvoPC derives (17.17) from the Calvo price setter with the explicit disturbance
`u_π = calvoRem`, bounded there term by term. Here the terms are combined into **one** bound
`|u_{π,t}| ≤ C·L²` almost surely, with an explicit constant `C = calvoC` depending only on the
parameters, whenever output gap and inflation are bounded by `L` and `L` is small (`Small`).

## Constants

* `Kf = |1 − γ| + 4δ(ε − 1)/(1 − δ)`, `Kk = (1 + ϕ) + 4δη/(1 − δ)`: `|f_t| ≤ Kf·L`,
  `|k_t| ≤ Kk·L` (`fc_abs_le`, `kc_abs_le`), from the tight two-sided bounds of the discounted
  weights (`wA_lo`, `wB_lo`, `log_ratio_le`).
* `Kr = 4α/(1 − α)`: the Calvo index forces `|r_t| ≤ Kr·L` (`r_abs_le`), so the bound `Lr` on
  reset prices assumed in TidyR6CalvoPC is automatic.
* `CF = 2Kf² + (1 − γ)² + (ε − 1 + Kf)²`, `CK = 2Kk² + (1 + ϕ)² + (η + Kk)²`,
  `CI = (ε − 1)²(α + (1 − α)Kr²)`: `|R^F_t| ≤ CF·L²`, `|R^K_t| ≤ CK·L²`, `0 ≤ R^I_t ≤ CI·L²`.
* `calvoC = ((1 − α)/(cα))(CF + CK) + (β + 1/α)CI/(ε − 1)`.

## Smallness

`Small p L`: `L ≥ 0`, `δe^{ηL} ≤ (1 + δ)/2`, `(ε − 1 + Kf)L ≤ 1`, `(η + Kk)L ≤ 1` and
`Kr(ε − 1)L ≤ 1`. Every condition is a continuous inequality in `L` that is strict at `L = 0`,
so it holds for all small enough `L ≥ 0`.

## Main results

* `calvoRem_abs_le`: almost surely `|u_{π,t}| ≤ calvoC·L²`.
* `calvo_iff_PC_small`: `TidyR6CalvoPC.calvo_iff_PC` without the separate bound on reset prices,
  together with the bound on its disturbance.
-/

namespace Cochrane.KeynesianStickyPrices.TidyR6CalvoBound

open MeasureTheory ProbabilityTheory Filter Topology TidyR5ExpectationsMeasure
open TidyR6HouseholdMeasure TidyR6CalvoReset TidyR6EulerIS TidyR6RotembergPC TidyR6CalvoPC

/-! ### Constants -/

/-- Cochrane (2023), p. 118: the slope of the bound on `f_t`, `|1 − γ| + 4δ(ε − 1)/(1 − δ)`. -/
noncomputable def Kf (p : CalvoPar) : ℝ := |1 - p.γ| + 4 * p.δ * (p.ε - 1) / (1 - p.δ)

/-- Cochrane (2023), p. 118: the slope of the bound on `k_t`, `(1 + ϕ) + 4δη/(1 − δ)`. -/
noncomputable def Kk (p : CalvoPar) : ℝ := (1 + p.ϕ) + 4 * p.δ * p.η / (1 - p.δ)

/-- Cochrane (2023), p. 421: the slope of the bound on the reset price, `4α/(1 − α)`. -/
noncomputable def Kr (p : CalvoPar) : ℝ := 4 * p.α / (1 - p.α)

/-- Cochrane (2023), p. 118: the constant of the bound on `R^F`. -/
noncomputable def CF (p : CalvoPar) : ℝ := 2 * Kf p ^ 2 + (1 - p.γ) ^ 2 + (p.ε - 1 + Kf p) ^ 2

/-- Cochrane (2023), p. 118: the constant of the bound on `R^K`. -/
noncomputable def CK (p : CalvoPar) : ℝ := 2 * Kk p ^ 2 + (1 + p.ϕ) ^ 2 + (p.η + Kk p) ^ 2

/-- Cochrane (2023), p. 421: the constant of the bound on `R^I`. -/
noncomputable def CI (p : CalvoPar) : ℝ := (p.ε - 1) ^ 2 * (p.α + (1 - p.α) * Kr p ^ 2)

/-- Cochrane (2023), eq. (17.17), p. 407: the constant of the combined bound on `u_π`,
`((1 − α)/(cα))(CF + CK) + (β + 1/α)CI/(ε − 1)`. -/
noncomputable def calvoC (p : CalvoPar) : ℝ :=
  (1 - p.α) / (p.c * p.α) * (CF p + CK p) + (p.β + 1 / p.α) * CI p / (p.ε - 1)

/-- Cochrane (2023), p. 118: the smallness conditions on the bound `L` of output gap and
inflation. -/
def Small (p : CalvoPar) (L : ℝ) : Prop :=
  0 ≤ L ∧ p.δ * Real.exp (p.η * L) ≤ (1 + p.δ) / 2 ∧ (p.ε - 1 + Kf p) * L ≤ 1 ∧
    (p.η + Kk p) * L ≤ 1 ∧ Kr p * (p.ε - 1) * L ≤ 1

/-! ### Real-variable estimates -/

/-- Cochrane (2023), p. 118: `e^z − 1 ≤ 2z` for `0 ≤ z ≤ 1`. -/
theorem exp_sub_one_le_two_mul {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1) : Real.exp z - 1 ≤ 2 * z := by
  have := expRem_le_sq (z := z) (by rw [abs_of_nonneg h0]; exact h1)
  simp only [expRem] at this
  nlinarith

/-- Cochrane (2023), p. 118: `|e^z − 1| ≤ 2|z|` for `|z| ≤ 1`. -/
theorem abs_exp_sub_one_le {z : ℝ} (h : |z| ≤ 1) : |Real.exp z - 1| ≤ 2 * |z| := by
  have h1 := expRem_le_sq h
  have h2 := expRem_nonneg z
  simp only [expRem] at h1 h2
  have h3 : z ^ 2 ≤ |z| := by
    rw [← sq_abs]; nlinarith [abs_nonneg z]
  rw [abs_le]
  constructor <;> cases abs_cases z <;> nlinarith

/-- Cochrane (2023), p. 118: `(e^f − 1)²e^{−f} ≤ 2f²` for `|f| ≤ 1`. -/
theorem sq_exp_mul_le {f : ℝ} (h : |f| ≤ 1) :
    (Real.exp f - 1) ^ 2 * Real.exp (-f) ≤ 2 * f ^ 2 := by
  have h1 := expRem_le_sq h
  have h2 := expRem_le_sq (z := -f) (by rwa [abs_neg])
  have hinv : Real.exp f * Real.exp (-f) = 1 := by rw [← Real.exp_add]; simp
  have e : (Real.exp f - 1) ^ 2 * Real.exp (-f) = expRem f + expRem (-f) := by
    simp only [expRem]
    linear_combination (Real.exp f - 2) * hinv
  rw [e]
  nlinarith

/-- Cochrane (2023), p. 118: **the log-ratio bound**. If
`Ye^{−aL}/(1 − δe^{−eL}) ≤ F ≤ Ye^{aL}/(1 − δe^{eL})` with `Y > 0`, `0 < δ < 1`, `e, L ≥ 0`,
`eL ≤ 1` and `δe^{eL} ≤ (1 + δ)/2`, then `|log(F/(Y/(1 − δ)))| ≤ (a + 4δe/(1 − δ))L`. -/
theorem log_ratio_le {Y a e δ L F : ℝ} (hY : 0 < Y) (hδ : 0 < δ) (hδ1 : δ < 1)
    (he : 0 ≤ e) (hL : 0 ≤ L) (heL : e * L ≤ 1)
    (hρ : δ * Real.exp (e * L) ≤ (1 + δ) / 2)
    (hlo : Y * Real.exp (-(a * L)) / (1 - δ * Real.exp (-(e * L))) ≤ F)
    (hhi : F ≤ Y * Real.exp (a * L) / (1 - δ * Real.exp (e * L))) :
    |Real.log (F / (Y / (1 - δ)))| ≤ (a + 4 * δ * e / (1 - δ)) * L := by
  have heL0 : 0 ≤ e * L := mul_nonneg he hL
  have hd : 0 < 1 - δ := by linarith
  -- the two discount ratios
  have hm1 : Real.exp (-(e * L)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hm2 : 1 - e * L ≤ Real.exp (-(e * L)) := by linarith [Real.add_one_le_exp (-(e * L))]
  have hm : 0 < 1 - δ * Real.exp (-(e * L)) := by nlinarith
  have hp : (1 - δ) / 2 ≤ 1 - δ * Real.exp (e * L) := by linarith
  have hp0 : 0 < 1 - δ * Real.exp (e * L) := by linarith
  have hp2 : Real.exp (e * L) - 1 ≤ 2 * (e * L) := exp_sub_one_le_two_mul heL0 heL
  have hlo0 : 0 < Y * Real.exp (-(a * L)) / (1 - δ * Real.exp (-(e * L))) := by positivity
  have hF0 : 0 < F := hlo0.trans_le hlo
  have hYd : 0 < Y / (1 - δ) := div_pos hY hd
  have hK : 0 ≤ 4 * δ * e / (1 - δ) := by positivity
  rw [abs_le]
  constructor
  · -- the lower bound
    have e1 : Y * Real.exp (-(a * L)) / (1 - δ * Real.exp (-(e * L))) / (Y / (1 - δ)) =
        (1 - δ) / (1 - δ * Real.exp (-(e * L))) * Real.exp (-(a * L)) := by
      field_simp
    have hlog := Real.log_le_log (div_pos hlo0 hYd) (div_le_div_of_nonneg_right hlo hYd.le)
    rw [e1, Real.log_mul (div_pos hd hm).ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
    have hl := Real.one_sub_inv_le_log_of_pos (div_pos hd hm)
    rw [inv_div] at hl
    have hq : -(δ * e * L / (1 - δ)) ≤ 1 - (1 - δ * Real.exp (-(e * L))) / (1 - δ) := by
      have e2 : 1 - (1 - δ * Real.exp (-(e * L))) / (1 - δ) =
          (δ * Real.exp (-(e * L)) - δ) / (1 - δ) := by field_simp; ring
      rw [e2, ← neg_div]
      exact div_le_div_of_nonneg_right (by nlinarith) hd.le
    have hq2 : δ * e * L / (1 - δ) ≤ 4 * δ * e / (1 - δ) * L := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (by nlinarith [mul_nonneg (mul_nonneg hδ.le he) hL])
        hd.le
    nlinarith
  · -- the upper bound
    have e1 : Y * Real.exp (a * L) / (1 - δ * Real.exp (e * L)) / (Y / (1 - δ)) =
        (1 - δ) / (1 - δ * Real.exp (e * L)) * Real.exp (a * L) := by
      field_simp
    have hlog : Real.log (F / (Y / (1 - δ))) ≤
        Real.log (Y * Real.exp (a * L) / (1 - δ * Real.exp (e * L)) / (Y / (1 - δ))) :=
      Real.log_le_log (div_pos hF0 hYd) (div_le_div_of_nonneg_right hhi hYd.le)
    rw [e1, Real.log_mul (div_pos hd hp0).ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
    have hl := Real.log_le_sub_one_of_pos (div_pos hd hp0)
    have hq : (1 - δ) / (1 - δ * Real.exp (e * L)) - 1 ≤ 4 * δ * e / (1 - δ) * L := by
      rw [div_sub_one hp0.ne', div_mul_eq_mul_div, div_le_div_iff₀ hp0 hd]
      have h1 : (1 - δ - (1 - δ * Real.exp (e * L))) * (1 - δ) ≤ 2 * δ * (e * L) * (1 - δ) := by
        have : 1 - δ - (1 - δ * Real.exp (e * L)) = δ * (Real.exp (e * L) - 1) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right (by nlinarith) hd.le
      have h2 : 2 * δ * (e * L) * (1 - δ) ≤ 4 * δ * e * L * (1 - δ * Real.exp (e * L)) := by
        have := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ 4 * δ * e * L)
        nlinarith
      linarith
    nlinarith

/-- Cochrane (2023), p. 421: **the index bounds the reset price**: if
`αe^{(ε−1)π} + (1 − α)e^{(1−ε)r} = 1` with `0 < α < 1`, `ε > 1`, `|π| ≤ L`, `(ε − 1)L ≤ 1` and
`Kr(ε − 1)L ≤ 1` (`Kr = 4α/(1 − α)`), then `|r| ≤ Kr·L`. -/
theorem r_abs_le_pt {α ε π r L : ℝ} (hα : 0 < α) (hα1 : α < 1) (hε : 1 < ε) (hπ : |π| ≤ L)
    (hεL : (ε - 1) * L ≤ 1) (hKL : 4 * α / (1 - α) * (ε - 1) * L ≤ 1)
    (hI : α * Real.exp ((ε - 1) * π) + (1 - α) * Real.exp ((1 - ε) * r) = 1) :
    |r| ≤ 4 * α / (1 - α) * L := by
  have hα' : 0 < 1 - α := by linarith
  have hε1 : 0 < ε - 1 := by linarith
  set w := (ε - 1) * π with hw
  set z := (1 - ε) * r with hz
  set s := 2 * α * (ε - 1) * L / (1 - α) with hs
  have hwL : |w| ≤ (ε - 1) * L := by
    rw [hw, abs_mul, abs_of_pos hε1]; exact mul_le_mul_of_nonneg_left hπ hε1.le
  have hw1 := abs_exp_sub_one_le (hwL.trans hεL)
  -- `e^z − 1 = α(1 − e^w)/(1 − α)`
  have hez : Real.exp z - 1 = α * (1 - Real.exp w) / (1 - α) := by
    field_simp; linarith
  have hezs : |Real.exp z - 1| ≤ s := by
    rw [hez, abs_div, abs_mul, abs_of_pos hα, abs_of_pos hα', abs_sub_comm, hs]
    refine div_le_div_of_nonneg_right ?_ hα'.le
    have := mul_le_mul_of_nonneg_left (hw1.trans (mul_le_mul_of_nonneg_left hwL two_pos.le))
      hα.le
    linarith
  have hs2 : s ≤ 1 / 2 := by
    have : s = (4 * α / (1 - α) * (ε - 1) * L) / 2 := by rw [hs]; field_simp; ring
    rw [this]; linarith
  have hs0 : 0 ≤ s := (abs_nonneg _).trans hezs
  have hzs : |z| ≤ 2 * s := by
    rw [abs_le] at hezs ⊢
    constructor
    · -- `z ≥ 1 − e^{−z} ≥ 1 − 1/(1 − s) ≥ −2s`
      have h1 : 1 - Real.exp (-z) ≤ z := by linarith [Real.add_one_le_exp (-z)]
      have hpos : 0 < Real.exp z := Real.exp_pos z
      have hinv : Real.exp (-z) * Real.exp z = 1 := by rw [← Real.exp_add]; simp
      have h2 : Real.exp (-z) ≤ 1 + 2 * s := by
        have h3 : 1 - s ≤ Real.exp z := by linarith [hezs.1]
        nlinarith [mul_le_mul_of_nonneg_left h3 (Real.exp_pos (-z)).le]
      linarith
    · have := Real.add_one_le_exp z
      linarith [hezs.2]
  have hzr : |z| = (ε - 1) * |r| := by
    rw [hz, abs_mul, show 1 - ε = -(ε - 1) by ring, abs_neg, abs_of_pos hε1]
  rw [hzr] at hzs
  have e2 : 2 * s = (ε - 1) * (4 * α / (1 - α) * L) := by rw [hs]; field_simp; ring
  rw [e2] at hzs
  exact le_of_mul_le_mul_left hzs hε1

/-! ### Tight lower bounds on the discounted weights -/

variable {Ω : Type*}

/-- Cochrane (2023), p. 118: `W_{A,t} ≥ Ȳ^{1−γ}e^{−|1−γ|L}/(1 − δe^{−(ε−1)L})` (every future
weight is bounded below, not only the current one). -/
theorem wA_lo {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ} (hB : Bounded x π L)
    (hρ : p.δ * Real.exp (p.η * L) < 1) (t : ℕ) (ω : Ω) :
    p.Ybar ^ (1 - p.γ) * Real.exp (-(|1 - p.γ| * L)) /
      (1 - p.δ * Real.exp (-((p.ε - 1) * L))) ≤ wA p x π t ω := by
  have hY := Real.rpow_pos_of_pos h.2.2.2.2.2.2.1 (1 - p.γ)
  have hε1 : 0 ≤ p.ε - 1 := by linarith [h.2.2.2.2.1]
  set ρm := p.δ * Real.exp (-((p.ε - 1) * L)) with hρm
  have hρm0 : 0 ≤ ρm := mul_nonneg h.δ_pos.le (Real.exp_pos _).le
  have hρm1 : ρm < 1 := by
    have : Real.exp (-((p.ε - 1) * L)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [hB.1])
    nlinarith [h.δ_lt, h.δ_pos]
  have hs := (wA_bounds h hB hρ t ω).1
  have hg := (summable_geometric_of_lt_one hρm0 hρm1).mul_left
    (p.Ybar ^ (1 - p.γ) * Real.exp (-(|1 - p.γ| * L)))
  have hle : ∀ k, p.Ybar ^ (1 - p.γ) * Real.exp (-(|1 - p.γ| * L)) * ρm ^ k ≤
      p.δ ^ k * aW p x π t k ω := fun k => by
    have h1 := (hB.2 (t + k) ω).1
    have h2 := abs_cumπ_le (fun s ω => (hB.2 s ω).2) t k ω
    have he : Real.exp (-(|1 - p.γ| * L)) * Real.exp (-((p.ε - 1) * L)) ^ k ≤
        Real.exp ((1 - p.γ) * x (t + k) ω + (p.ε - 1) * cumπ π t k ω) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      refine Real.exp_le_exp.2 (add_le_add ?_ ?_)
      · have : |(1 - p.γ) * x (t + k) ω| ≤ |1 - p.γ| * L := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        linarith [neg_abs_le ((1 - p.γ) * x (t + k) ω)]
      · have : -(k * L) ≤ cumπ π t k ω := by linarith [neg_abs_le (cumπ π t k ω)]
        nlinarith
    simp only [aW, hρm]
    rw [mul_pow]
    have := mul_le_mul_of_nonneg_left he hY.le
    have hd := pow_nonneg h.δ_pos.le k
    nlinarith [mul_le_mul_of_nonneg_left this hd]
  calc p.Ybar ^ (1 - p.γ) * Real.exp (-(|1 - p.γ| * L)) / (1 - ρm)
      = ∑' k, p.Ybar ^ (1 - p.γ) * Real.exp (-(|1 - p.γ| * L)) * ρm ^ k := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hρm0 hρm1, div_eq_mul_inv]
    _ ≤ wA p x π t ω := hg.tsum_le_tsum hle hs

/-- Cochrane (2023), p. 118: `W_{B,t} ≥ (Ȳ^{1+ϕ}/(1 + ϕ))e^{−(1+ϕ)L}/(1 − δe^{−ηL})`. -/
theorem wB_lo {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ} (hB : Bounded x π L)
    (hρ : p.δ * Real.exp (p.η * L) < 1) (t : ℕ) (ω : Ω) :
    p.Ybar ^ (1 + p.ϕ) / (1 + p.ϕ) * Real.exp (-((1 + p.ϕ) * L)) /
      (1 - p.δ * Real.exp (-(p.η * L))) ≤ wB p x π t ω := by
  have h1ϕ : (0 : ℝ) < 1 + p.ϕ := by linarith [h.2.2.2.2.2.1]
  have hY : 0 < p.Ybar ^ (1 + p.ϕ) / (1 + p.ϕ) :=
    div_pos (Real.rpow_pos_of_pos h.2.2.2.2.2.2.1 _) h1ϕ
  have hη0 : 0 ≤ p.η := by have := h.η_gt; linarith [h.2.2.2.2.1]
  set ρm := p.δ * Real.exp (-(p.η * L)) with hρm
  have hρm0 : 0 ≤ ρm := mul_nonneg h.δ_pos.le (Real.exp_pos _).le
  have hρm1 : ρm < 1 := by
    have : Real.exp (-(p.η * L)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hB.1])
    nlinarith [h.δ_lt, h.δ_pos]
  have hs := (wB_bounds h hB hρ t ω).1
  have hg := (summable_geometric_of_lt_one hρm0 hρm1).mul_left
    (p.Ybar ^ (1 + p.ϕ) / (1 + p.ϕ) * Real.exp (-((1 + p.ϕ) * L)))
  have hle : ∀ k, p.Ybar ^ (1 + p.ϕ) / (1 + p.ϕ) * Real.exp (-((1 + p.ϕ) * L)) * ρm ^ k ≤
      p.δ ^ k * bW p x π t k ω := fun k => by
    have h1 := (hB.2 (t + k) ω).1
    have h2 := abs_cumπ_le (fun s ω => (hB.2 s ω).2) t k ω
    have he : Real.exp (-((1 + p.ϕ) * L)) * Real.exp (-(p.η * L)) ^ k ≤
        Real.exp ((1 + p.ϕ) * x (t + k) ω + p.η * cumπ π t k ω) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      refine Real.exp_le_exp.2 (add_le_add ?_ ?_)
      · have : |(1 + p.ϕ) * x (t + k) ω| ≤ (1 + p.ϕ) * L := by
          rw [abs_mul, abs_of_pos h1ϕ]; exact mul_le_mul_of_nonneg_left h1 h1ϕ.le
        linarith [neg_abs_le ((1 + p.ϕ) * x (t + k) ω)]
      · have : -(k * L) ≤ cumπ π t k ω := by linarith [neg_abs_le (cumπ π t k ω)]
        nlinarith
    simp only [bW, hρm]
    rw [mul_pow]
    have := mul_le_mul_of_nonneg_left he hY.le
    have hd := pow_nonneg h.δ_pos.le k
    nlinarith [mul_le_mul_of_nonneg_left this hd]
  calc p.Ybar ^ (1 + p.ϕ) / (1 + p.ϕ) * Real.exp (-((1 + p.ϕ) * L)) / (1 - ρm)
      = ∑' k, p.Ybar ^ (1 + p.ϕ) / (1 + p.ϕ) * Real.exp (-((1 + p.ϕ) * L)) * ρm ^ k := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hρm0 hρm1, div_eq_mul_inv]
    _ ≤ wB p x π t ω := hg.tsum_le_tsum hle hs

/-! ### The logs of the forecasts are first order -/

variable [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-- Cochrane (2023), p. 118: under `Small`, `δe^{ηL} < 1`. -/
theorem Small.ρ_lt {p : CalvoPar} (h : p.Valid) {L : ℝ} (hs : Small p L) :
    p.δ * Real.exp (p.η * L) < 1 := by
  have := h.δ_lt; linarith [hs.2.1]

/-- Cochrane (2023), p. 118: `Kf ≥ 0`. -/
theorem Kf_nonneg {p : CalvoPar} (h : p.Valid) : 0 ≤ Kf p := by
  have : 0 < 1 - p.δ := by linarith [h.δ_lt]
  have : 0 ≤ p.ε - 1 := by linarith [h.2.2.2.2.1]
  have := h.δ_pos
  unfold Kf; positivity

/-- Cochrane (2023), p. 118: `Kk ≥ 0`. -/
theorem Kk_nonneg {p : CalvoPar} (h : p.Valid) : 0 ≤ Kk p := by
  have : 0 < 1 - p.δ := by linarith [h.δ_lt]
  have : 0 ≤ p.η := by linarith [h.η_gt, h.2.2.2.2.1]
  have := h.δ_pos
  have : 0 ≤ 1 + p.ϕ := by linarith [h.2.2.2.2.2.1]
  unfold Kk; positivity

/-- Cochrane (2023), p. 118: **`f_t` is first order**: `|f_t| ≤ Kf·L` almost surely. -/
theorem fc_abs_le {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ} (hB : Bounded x π L)
    (hs : Small p L) (hx : StronglyAdapted S.𝓕 x) (hπ : StronglyAdapted S.𝓕 π) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, |fc S p x π t ω| ≤ Kf p * L := by
  have hρ := hs.ρ_lt h
  have hε1 : 0 ≤ p.ε - 1 := by linarith [h.2.2.2.2.1]
  have hmem := E_mem (S := S) (wA_integrable h hB hρ hx hπ t)
    (fun ω => ⟨wA_lo h hB hρ t ω, (wA_bounds h hB hρ t ω).2.2⟩) t
  filter_upwards [hmem] with ω hω
  have heL : (p.ε - 1) * L ≤ 1 := by
    have := Kf_nonneg h; nlinarith [hs.2.2.1, hs.1]
  have hρ' : p.δ * Real.exp ((p.ε - 1) * L) ≤ (1 + p.δ) / 2 := by
    refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) h.δ_pos.le) hs.2.1
    exact mul_le_mul_of_nonneg_right h.η_gt.le hs.1
  exact log_ratio_le (Real.rpow_pos_of_pos h.2.2.2.2.2.2.1 _) h.δ_pos h.δ_lt hε1 hs.1 heL
    hρ' hω.1 hω.2

/-- Cochrane (2023), p. 118: **`k_t` is first order**: `|k_t| ≤ Kk·L` almost surely. -/
theorem kc_abs_le {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ} (hB : Bounded x π L)
    (hs : Small p L) (hx : StronglyAdapted S.𝓕 x) (hπ : StronglyAdapted S.𝓕 π) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, |kc S p x π t ω| ≤ Kk p * L := by
  have hρ := hs.ρ_lt h
  have hη0 : 0 ≤ p.η := by linarith [h.η_gt, h.2.2.2.2.1]
  have h1ϕ : (0 : ℝ) < 1 + p.ϕ := by linarith [h.2.2.2.2.2.1]
  have hmem := E_mem (S := S) (wB_integrable h hB hρ hx hπ t)
    (fun ω => ⟨wB_lo h hB hρ t ω, (wB_bounds h hB hρ t ω).2.2⟩) t
  filter_upwards [hmem] with ω hω
  have heL : p.η * L ≤ 1 := by
    have := Kk_nonneg h; nlinarith [hs.2.2.2.1, hs.1]
  have hK : p.Kbar = p.Ybar ^ (1 + p.ϕ) / (1 + p.ϕ) / (1 - p.δ) := by
    simp only [CalvoPar.Kbar, div_div]
  simp only [kc, hK]
  exact log_ratio_le (div_pos (Real.rpow_pos_of_pos h.2.2.2.2.2.2.1 _) h1ϕ) h.δ_pos h.δ_lt
    hη0 hs.1 heL hs.2.1 hω.1 hω.2

/-! ### The remainders are second order -/

/-- Cochrane (2023), p. 118: **`|R^F_t| ≤ CF·L²`** almost surely. -/
theorem RF_abs_le {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ} (hB : Bounded x π L)
    (hs : Small p L) (hx : StronglyAdapted S.𝓕 x) (hπ : StronglyAdapted S.𝓕 π) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, |RF S p x π t ω| ≤ CF p * L ^ 2 := by
  have hρ := hs.ρ_lt h
  have hKf := Kf_nonneg h
  have hε1 : 0 ≤ p.ε - 1 := by linarith [h.2.2.2.2.1]
  have hL := hs.1
  have hKL : Kf p * L ≤ 1 := by nlinarith [hs.2.2.1]
  have hW : ∀ᵐ ω ∂S.μ, |expRem ((p.ε - 1) * π (t + 1) ω + fc S p x π (t + 1) ω)| ≤
      ((p.ε - 1 + Kf p) * L) ^ 2 := by
    filter_upwards [fc_abs_le h hB hs hx hπ (t + 1)] with ω hf
    have hπ1 := (hB.2 (t + 1) ω).2
    have hw : |(p.ε - 1) * π (t + 1) ω + fc S p x π (t + 1) ω| ≤ (p.ε - 1 + Kf p) * L := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hε1]
      nlinarith [mul_le_mul_of_nonneg_left hπ1 hε1]
    rw [abs_of_nonneg (expRem_nonneg _)]
    refine (expRem_le_sq (hw.trans hs.2.2.1)).trans ?_
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hw 2
  filter_upwards [rF_bounds h hB hρ hx hπ t, fc_abs_le h hB hs hx hπ t, S.abs_E_le hW t]
    with ω h1 h2 h3
  have hA1 : (Real.exp (fc S p x π t ω) - 1) ^ 2 * Real.exp (-fc S p x π t ω) ≤
      2 * (Kf p * L) ^ 2 := by
    refine (sq_exp_mul_le (h2.trans hKL)).trans ?_
    rw [← sq_abs]
    nlinarith [pow_le_pow_left₀ (abs_nonneg _) h2 2]
  have hx1 : |(1 - p.γ) * x t ω| ≤ |1 - p.γ| * L := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB.2 t ω).1 (abs_nonneg _)
  have hγL : |1 - p.γ| * L ≤ 1 := by
    have : |1 - p.γ| ≤ Kf p := by
      have : 0 < 1 - p.δ := by linarith [h.δ_lt]
      have := h.δ_pos
      unfold Kf; have : 0 ≤ 4 * p.δ * (p.ε - 1) / (1 - p.δ) := by positivity
      linarith
    nlinarith
  have hA2 : expRem ((1 - p.γ) * x t ω) ≤ (1 - p.γ) ^ 2 * L ^ 2 := by
    refine (expRem_le_sq (hx1.trans hγL)).trans ?_
    rw [← sq_abs, ← sq_abs (1 - p.γ), ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hx1 2
  have hA3 := (le_abs_self _).trans h3
  have hd0 := h.δ_pos
  have hd1 := h.δ_lt
  have hR0 := expRem_nonneg ((1 - p.γ) * x t ω)
  have hCF : CF p * L ^ 2 = 2 * (Kf p * L) ^ 2 + (1 - p.γ) ^ 2 * L ^ 2 +
      ((p.ε - 1 + Kf p) * L) ^ 2 := by simp only [CF]; ring
  rw [abs_le, hCF]
  constructor
  · nlinarith [sq_nonneg (1 - p.γ), sq_nonneg L, sq_nonneg ((p.ε - 1 + Kf p) * L)]
  · have e1 : p.δ * S.E t (fun ω => expRem ((p.ε - 1) * π (t + 1) ω +
        fc S p x π (t + 1) ω)) ω ≤ ((p.ε - 1 + Kf p) * L) ^ 2 := by
      nlinarith [sq_nonneg ((p.ε - 1 + Kf p) * L)]
    nlinarith [sq_nonneg (Kf p * L)]

/-- Cochrane (2023), p. 118: **`|R^K_t| ≤ CK·L²`** almost surely. -/
theorem RK_abs_le {p : CalvoPar} (h : p.Valid) {x π : ℕ → Ω → ℝ} {L : ℝ} (hB : Bounded x π L)
    (hs : Small p L) (hx : StronglyAdapted S.𝓕 x) (hπ : StronglyAdapted S.𝓕 π) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, |RK S p x π t ω| ≤ CK p * L ^ 2 := by
  have hρ := hs.ρ_lt h
  have hKk := Kk_nonneg h
  have hη0 : 0 ≤ p.η := by linarith [h.η_gt, h.2.2.2.2.1]
  have h1ϕ : (0 : ℝ) < 1 + p.ϕ := by linarith [h.2.2.2.2.2.1]
  have hL := hs.1
  have hKL : Kk p * L ≤ 1 := by nlinarith [hs.2.2.2.1]
  have hW : ∀ᵐ ω ∂S.μ, |expRem (p.η * π (t + 1) ω + kc S p x π (t + 1) ω)| ≤
      ((p.η + Kk p) * L) ^ 2 := by
    filter_upwards [kc_abs_le h hB hs hx hπ (t + 1)] with ω hk
    have hπ1 := (hB.2 (t + 1) ω).2
    have hw : |p.η * π (t + 1) ω + kc S p x π (t + 1) ω| ≤ (p.η + Kk p) * L := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hη0]
      nlinarith [mul_le_mul_of_nonneg_left hπ1 hη0]
    rw [abs_of_nonneg (expRem_nonneg _)]
    refine (expRem_le_sq (hw.trans hs.2.2.2.1)).trans ?_
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hw 2
  filter_upwards [rK_bounds h hB hρ hx hπ t, kc_abs_le h hB hs hx hπ t, S.abs_E_le hW t]
    with ω h1 h2 h3
  have hA1 : (Real.exp (kc S p x π t ω) - 1) ^ 2 * Real.exp (-kc S p x π t ω) ≤
      2 * (Kk p * L) ^ 2 := by
    refine (sq_exp_mul_le (h2.trans hKL)).trans ?_
    rw [← sq_abs]
    nlinarith [pow_le_pow_left₀ (abs_nonneg _) h2 2]
  have hx1 : |(1 + p.ϕ) * x t ω| ≤ (1 + p.ϕ) * L := by
    rw [abs_mul, abs_of_pos h1ϕ]; exact mul_le_mul_of_nonneg_left (hB.2 t ω).1 h1ϕ.le
  have hϕL : (1 + p.ϕ) * L ≤ 1 := by
    have : 1 + p.ϕ ≤ Kk p := by
      have : 0 < 1 - p.δ := by linarith [h.δ_lt]
      have := h.δ_pos
      unfold Kk; have : 0 ≤ 4 * p.δ * p.η / (1 - p.δ) := by positivity
      linarith
    nlinarith
  have hA2 : expRem ((1 + p.ϕ) * x t ω) ≤ (1 + p.ϕ) ^ 2 * L ^ 2 := by
    refine (expRem_le_sq (hx1.trans hϕL)).trans ?_
    rw [← sq_abs, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hx1 2
  have hA3 := (le_abs_self _).trans h3
  have hd0 := h.δ_pos
  have hd1 := h.δ_lt
  have hR0 := expRem_nonneg ((1 + p.ϕ) * x t ω)
  have hCK : CK p * L ^ 2 = 2 * (Kk p * L) ^ 2 + (1 + p.ϕ) ^ 2 * L ^ 2 +
      ((p.η + Kk p) * L) ^ 2 := by simp only [CK]; ring
  rw [abs_le, hCK]
  constructor
  · nlinarith [sq_nonneg (1 + p.ϕ), sq_nonneg L, sq_nonneg ((p.η + Kk p) * L)]
  · have e1 : p.δ * S.E t (fun ω => expRem (p.η * π (t + 1) ω + kc S p x π (t + 1) ω)) ω ≤
        ((p.η + Kk p) * L) ^ 2 := by
      nlinarith [sq_nonneg ((p.η + Kk p) * L)]
    nlinarith [sq_nonneg (Kk p * L)]

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 421: **the index bounds every reset price**: `|r_t| ≤ Kr·L` (so the
bound `Lr` of TidyR6CalvoPC is automatic). -/
theorem r_abs_le {p : CalvoPar} (h : p.Valid) {x π r : ℕ → Ω → ℝ} {L : ℝ}
    (hB : Bounded x π L) (hs : Small p L) (hI : Index p π r) (t : ℕ) (ω : Ω) :
    |r t ω| ≤ Kr p * L := by
  have hKf := Kf_nonneg h
  have hεL : (p.ε - 1) * L ≤ 1 := by nlinarith [hs.2.2.1, hs.1]
  exact r_abs_le_pt h.1 h.2.1 h.2.2.2.2.1 (hB.2 t ω).2 hεL hs.2.2.2.2 (hI t ω)

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 421: **`0 ≤ R^I_t ≤ CI·L²`** at every date and state. -/
theorem RI_le {p : CalvoPar} (h : p.Valid) {x π r : ℕ → Ω → ℝ} {L : ℝ}
    (hB : Bounded x π L) (hs : Small p L) (hI : Index p π r) (t : ℕ) (ω : Ω) :
    0 ≤ RI p π r t ω ∧ RI p π r t ω ≤ CI p * L ^ 2 := by
  have hα0 := h.1
  have hα1 : 0 < 1 - p.α := by linarith [h.2.1]
  have hε1 : 0 ≤ p.ε - 1 := by linarith [h.2.2.2.2.1]
  have hKf := Kf_nonneg h
  have hL := hs.1
  have hεL : (p.ε - 1) * L ≤ 1 := by nlinarith [hs.2.2.1]
  have h1 : |(p.ε - 1) * π t ω| ≤ (p.ε - 1) * L := by
    rw [abs_mul, abs_of_nonneg hε1]; exact mul_le_mul_of_nonneg_left (hB.2 t ω).2 hε1
  have h2 : |(1 - p.ε) * r t ω| ≤ (p.ε - 1) * (Kr p * L) := by
    rw [abs_mul, show 1 - p.ε = -(p.ε - 1) by ring, abs_neg, abs_of_nonneg hε1]
    exact mul_le_mul_of_nonneg_left (r_abs_le h hB hs hI t ω) hε1
  have h2' : (p.ε - 1) * (Kr p * L) ≤ 1 := by linarith [hs.2.2.2.2]
  have e1 : expRem ((p.ε - 1) * π t ω) ≤ ((p.ε - 1) * L) ^ 2 := by
    refine (expRem_le_sq (h1.trans hεL)).trans ?_
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have e2 : expRem ((1 - p.ε) * r t ω) ≤ ((p.ε - 1) * (Kr p * L)) ^ 2 := by
    refine (expRem_le_sq (h2.trans h2')).trans ?_
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have n1 := expRem_nonneg ((p.ε - 1) * π t ω)
  have n2 := expRem_nonneg ((1 - p.ε) * r t ω)
  rw [RI_eq]
  constructor
  · positivity
  · have : CI p * L ^ 2 = p.α * ((p.ε - 1) * L) ^ 2 +
        (1 - p.α) * ((p.ε - 1) * (Kr p * L)) ^ 2 := by simp only [CI]; ring
    rw [this]
    exact add_le_add (mul_le_mul_of_nonneg_left e1 hα0.le)
      (mul_le_mul_of_nonneg_left e2 hα1.le)

/-! ### The combined bound -/

/-- Cochrane (2023), eq. (17.17), p. 407, **the Calvo disturbance is second order with an
explicit constant**: with valid parameters, output gap and inflation bounded by `L` with
`Small p L`, adapted variables and the Calvo index at every date, almost surely
`|u_{π,t}| ≤ calvoC·L²`, `calvoC = ((1 − α)/(cα))(CF + CK) + (β + 1/α)CI/(ε − 1)`. -/
theorem calvoRem_abs_le {p : CalvoPar} (h : p.Valid) {x π r : ℕ → Ω → ℝ} {L : ℝ}
    (hB : Bounded x π L) (hs : Small p L) (hx : StronglyAdapted S.𝓕 x)
    (hπ : StronglyAdapted S.𝓕 π) (hI : Index p π r) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, |calvoRem S p x π r t ω| ≤ calvoC p * L ^ 2 := by
  have hE : ∀ᵐ ω ∂S.μ, |S.E t (RI p π r (t + 1)) ω| ≤ CI p * L ^ 2 :=
    S.abs_E_le (Eventually.of_forall fun ω => by
      obtain ⟨a, b⟩ := RI_le h hB hs hI (t + 1) ω
      rwa [abs_of_nonneg a]) t
  filter_upwards [RF_abs_le h hB hs hx hπ t, RK_abs_le h hB hs hx hπ t, hE] with ω h1 h2 h3
  obtain ⟨i0, i1⟩ := RI_le h hB hs hI t ω
  have hα0 := h.1
  have hα1 : 0 < 1 - p.α := by linarith [h.2.1]
  have hε1 : 0 < p.ε - 1 := by linarith [h.2.2.2.2.1]
  have hc := h.c_pos
  have hβ := h.2.2.1
  have hA : 0 ≤ (1 - p.α) / (p.c * p.α) := by positivity
  have t1 : |(1 - p.α) / (p.c * p.α) * (RK S p x π t ω - RF S p x π t ω)| ≤
      (1 - p.α) / (p.c * p.α) * ((CF p + CK p) * L ^ 2) := by
    rw [abs_mul, abs_of_nonneg hA]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans ?_) hA
    linarith
  have t2 : |p.β / (p.ε - 1) * S.E t (RI p π r (t + 1)) ω| ≤
      p.β / (p.ε - 1) * (CI p * L ^ 2) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have t3 : |RI p π r t ω / (p.α * (p.ε - 1))| ≤ CI p * L ^ 2 / (p.α * (p.ε - 1)) := by
    rw [abs_div, abs_of_nonneg i0, abs_of_pos (by positivity)]
    exact div_le_div_of_nonneg_right i1 (by positivity)
  have e : calvoC p * L ^ 2 = (1 - p.α) / (p.c * p.α) * ((CF p + CK p) * L ^ 2) +
      p.β / (p.ε - 1) * (CI p * L ^ 2) + CI p * L ^ 2 / (p.α * (p.ε - 1)) := by
    simp only [calvoC]
    field_simp
    ring
  rw [e]
  simp only [calvoRem]
  exact (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add t1 t2)) t3)

/-- Cochrane (2023), eq. (17.17), p. 407, **the Calvo Phillips curve with a bounded
disturbance**: with valid parameters, `Small p L`, adapted variables (reset prices adapted) and
the Calvo index at every date, resetting optimally at every date is equivalent to (17.17) at every
date with slope `κ` and disturbance `u_π = calvoRem`, and that disturbance satisfies
`|u_{π,t}| ≤ calvoC·L²` almost surely. No separate bound on reset prices is assumed. -/
theorem calvo_iff_PC_small {p : CalvoPar} (h : p.Valid) {x π r : ℕ → Ω → ℝ} {L : ℝ}
    (hB : Bounded x π L) (hs : Small p L) (hx : StronglyAdapted S.𝓕 x)
    (hπ : StronglyAdapted S.𝓕 π) (hr : StronglyAdapted S.𝓕 r) (hI : Index p π r) :
    ((∀ t, ResetOpt S t p.δ p.ε p.η (aW p x π t) (bW p x π t) (r t)) ↔
      ∀ t, PCM S p.β p.κ (calvoRem S p x π r) x π t) ∧
      ∀ t, ∀ᵐ ω ∂S.μ, |calvoRem S p x π r t ω| ≤ calvoC p * L ^ 2 :=
  ⟨calvo_iff_PC h hB (hs.ρ_lt h) hx hπ hr (r_abs_le h hB hs hI) hI,
    fun t => calvoRem_abs_le h hB hs hx hπ hI t⟩

end Cochrane.KeynesianStickyPrices.TidyR6CalvoBound
