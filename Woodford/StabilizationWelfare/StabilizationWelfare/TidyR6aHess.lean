/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR6aLagr
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The Hessian of the Ramsey Lagrangian at the efficient steady state, and cubic bounds

Woodford (2003), *Interest and Prices*, Chapter 6, §2.2 and §3 (the welfare loss
`π² + (κ/θ)x²` is the second-order term of welfare at the efficient steady state), §5 and
Appendix E.

The exact second-order remainder `TidyR6aLagr.R2` of the Lagrangian density is compared with the
quadratic form `H0` of the efficient steady state (`Φ = 0`, no disturbances, multipliers
`λ̄₁ = λ̄₂ = 0`, `λ̄₄ = A/((1+ω)(1−αβ))`, `λ̄₃ = aλ̄₄/(θ − 1)`):
`H0 = −A(σ+ω)ŷ² − 2AŷΔ̂ − λ̄₄a(1+ωθ)(απ² + (1−α)x̂²) − 2λ̄₄αaπΔ̂₋`.

* Atoms: `abs_E2_le`, `abs_E2_sub_le`, `abs_Gx_sub_le`, `abs_Gx_sub_sub_le`; generic term
  bounds `gE2`, `glin`, `gG`.
* **`R2_bound`**: there are `δ₀ > 0` and `K ≥ 0` such that at every node whose data are within
  `ε ≤ δ₀` of the efficient steady state, for every direction with `|hᵢ|, |h_{Δ,−1}| ≤ ρ ≤ δ₀`,
  `|R2 − H0/2| ≤ K(ε + ρ)n`, `n = ∑ᵢ hᵢ² + h_{Δ,−1}²`: the Hessian at the plan differs from that of
  the steady state by `O(ε)`, and the cubic remainder is `O(ρ)` relative to `n` (the bound
  `‖h‖∞ · ∑|h|²` in discounted form after summation).
* **`H0_le`**: `H0/2 ≤ −(A(σ+ω)/2)ŷ² − (λ̄₄a(1+ωθ)α/2)π² + A|ŷ||Δ̂| + λ̄₄αa|π||Δ̂₋|`
  (negative definite up to the dispersion cross terms).
-/

namespace Woodford.StabilizationWelfare.TidyR6aHess

open Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovRamsey TidyR6aLagr

/-! ## Atoms -/

/-- Woodford (2003), App. E: `|E2(z)| ≤ z²` for `|z| ≤ 1`. -/
theorem abs_E2_le {z : ℝ} (hz : |z| ≤ 1) : |E2 z| ≤ z ^ 2 :=
  Real.abs_exp_sub_one_sub_id_le hz

/-- Woodford (2003), App. E: `|E2(z) − z²/2| ≤ |z|³` for `|z| ≤ 1`. -/
theorem abs_E2_sub_le {z : ℝ} (hz : |z| ≤ 1) : |E2 z - z ^ 2 / 2| ≤ |z| ^ 3 := by
  have h := ExpLogCES.abs_expRem_le hz
  have e : E2 z - z ^ 2 / 2 = ExpLogCES.expRem z := by unfold E2 ExpLogCES.expRem; ring
  rw [e]
  have : 0 ≤ |z| ^ 3 := by positivity
  linarith

/-- Woodford (2003), App. E: `|Gx(c, h) − h| ≤ |c|h²` for `|ch| ≤ 1`. -/
theorem abs_Gx_sub_le {c h : ℝ} (hch : |c * h| ≤ 1) : |Gx c h - h| ≤ |c| * h ^ 2 := by
  unfold Gx
  split_ifs with hc
  · simp [hc]
  · have e : (Real.exp (c * h) - 1) / c - h = E2 (c * h) / c := by
      unfold E2; field_simp
    rw [e, abs_div]
    have h1 := abs_E2_le hch
    rw [div_le_iff₀ (abs_pos.2 hc)]
    calc |E2 (c * h)| ≤ (c * h) ^ 2 := h1
      _ = |c| * h ^ 2 * |c| := by rw [mul_pow, ← sq_abs c]; ring

/-- Woodford (2003), App. E: `|Gx(c, h) − h − ch²/2| ≤ c²|h|³` for `|ch| ≤ 1`. -/
theorem abs_Gx_sub_sub_le {c h : ℝ} (hch : |c * h| ≤ 1) :
    |Gx c h - h - c * h ^ 2 / 2| ≤ c ^ 2 * |h| ^ 3 := by
  unfold Gx
  split_ifs with hc
  · simp [hc]
  · have e : (Real.exp (c * h) - 1) / c - h - c * h ^ 2 / 2 =
        (E2 (c * h) - (c * h) ^ 2 / 2) / c := by
      unfold E2; field_simp
    rw [e, abs_div]
    have h1 := abs_E2_sub_le hch
    rw [div_le_iff₀ (abs_pos.2 hc)]
    calc |E2 (c * h) - (c * h) ^ 2 / 2| ≤ |c * h| ^ 3 := h1
      _ = c ^ 2 * |h| ^ 3 * |c| := by rw [abs_mul, mul_pow, ← sq_abs c]; ring

/-! ## Generic term bounds -/

/-- Woodford (2003), App. E (**a generic second-order term**): if `|z| ≤ 1`, `|k − k₀| ≤ K_cε`,
`|z| ≤ K_zρ`, then `|kE2(z) − k₀z²/2| ≤ (K_c + |k₀|K_z)(ε + ρ)z²`. -/
theorem gE2 {k k0 z ε ρ Kc Kz : ℝ} (hz1 : |z| ≤ 1) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (hKc : 0 ≤ Kc)
    (hKz : 0 ≤ Kz) (hk : |k - k0| ≤ Kc * ε) (hz : |z| ≤ Kz * ρ) :
    |k * E2 z - k0 * (z ^ 2 / 2)| ≤ (Kc + |k0| * Kz) * (ε + ρ) * z ^ 2 := by
  have e : k * E2 z - k0 * (z ^ 2 / 2) = (k - k0) * E2 z + k0 * (E2 z - z ^ 2 / 2) := by ring
  rw [e]
  have a1 := abs_E2_le hz1
  have a2 := abs_E2_sub_le hz1
  have a3 : |z| ^ 3 ≤ Kz * ρ * z ^ 2 := by
    rw [show |z| ^ 3 = |z| * z ^ 2 by rw [← sq_abs z]; ring]
    exact mul_le_mul_of_nonneg_right hz (sq_nonneg _)
  calc _ ≤ |(k - k0) * E2 z| + |k0 * (E2 z - z ^ 2 / 2)| := abs_add_le _ _
    _ = |k - k0| * |E2 z| + |k0| * |E2 z - z ^ 2 / 2| := by rw [abs_mul, abs_mul]
    _ ≤ Kc * ε * z ^ 2 + |k0| * (Kz * ρ * z ^ 2) := add_le_add
        (mul_le_mul hk a1 (abs_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_left (a2.trans a3) (abs_nonneg _))
    _ ≤ _ := by
        have t1 := mul_nonneg (mul_nonneg hKc hρ) (sq_nonneg z)
        have t2 := mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg k0) hKz) hε) (sq_nonneg z)
        nlinarith

/-- Woodford (2003), App. E (**a generic bilinear term**): if `|z| ≤ 1`, `|k − k₀| ≤ K_cε`,
`|q| ≤ ρ`, then `|kq(eᶻ − 1) − k₀qz| ≤ (K_c + |k₀|)(ε + ρ)(q² + z²)`. -/
theorem glin {k k0 z q ε ρ Kc : ℝ} (hz1 : |z| ≤ 1) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (hKc : 0 ≤ Kc)
    (hk : |k - k0| ≤ Kc * ε) (hq : |q| ≤ ρ) :
    |k * q * (Real.exp z - 1) - k0 * q * z| ≤ (Kc + |k0|) * (ε + ρ) * (q ^ 2 + z ^ 2) := by
  have e : k * q * (Real.exp z - 1) - k0 * q * z = (k - k0) * q * (Real.exp z - 1) +
      k0 * q * (Real.exp z - 1 - z) := by ring
  rw [e]
  have a1 := Real.abs_exp_sub_one_le hz1
  have a2 := Real.abs_exp_sub_one_sub_id_le hz1
  have hqz : |q| * |z| ≤ (q ^ 2 + z ^ 2) / 2 := by
    nlinarith [sq_nonneg (|q| - |z|), sq_abs q, sq_abs z]
  calc _ ≤ |(k - k0) * q * (Real.exp z - 1)| + |k0 * q * (Real.exp z - 1 - z)| := abs_add_le _ _
    _ = |k - k0| * |q| * |Real.exp z - 1| + |k0| * |q| * |Real.exp z - 1 - z| := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul]
    _ ≤ Kc * ε * |q| * (2 * |z|) + |k0| * ρ * z ^ 2 := add_le_add
        (mul_le_mul (mul_le_mul_of_nonneg_right hk (abs_nonneg _)) a1 (abs_nonneg _)
          (by positivity))
        (mul_le_mul (mul_le_mul_of_nonneg_left hq (abs_nonneg _)) a2 (abs_nonneg _)
          (by positivity))
    _ ≤ _ := by
        have hKe := mul_nonneg hKc hε
        have t1 : Kc * ε * |q| * (2 * |z|) ≤ Kc * ε * (q ^ 2 + z ^ 2) := by
          have := mul_le_mul_of_nonneg_left hqz hKe; nlinarith
        have t2 : |k0| * ρ * z ^ 2 ≤ |k0| * ρ * (q ^ 2 + z ^ 2) :=
          mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg q]) (mul_nonneg (abs_nonneg _) hρ)
        have t3 := mul_nonneg (mul_nonneg hKc hρ) (add_nonneg (sq_nonneg q) (sq_nonneg z))
        have t4 := mul_nonneg (mul_nonneg (abs_nonneg k0) hε)
          (add_nonneg (sq_nonneg q) (sq_nonneg z))
        nlinarith

/-- Woodford (2003), App. E (**the generic utility term**): if `|ch| ≤ 1`, `|k − k₀| ≤ K_cε`,
`|h| ≤ ρ`, then `|k(Gx(c, h) − h) − k₀ch²/2| ≤ (K_c|c| + |k₀|c²)(ε + ρ)h²`. -/
theorem gG {k k0 c h ε ρ Kc : ℝ} (hch : |c * h| ≤ 1) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (hKc : 0 ≤ Kc)
    (hk : |k - k0| ≤ Kc * ε) (hh : |h| ≤ ρ) :
    |k * (Gx c h - h) - k0 * (c * h ^ 2 / 2)| ≤ (Kc * |c| + |k0| * c ^ 2) * (ε + ρ) * h ^ 2 := by
  have e : k * (Gx c h - h) - k0 * (c * h ^ 2 / 2) = (k - k0) * (Gx c h - h) +
      k0 * (Gx c h - h - c * h ^ 2 / 2) := by ring
  rw [e]
  have a1 := abs_Gx_sub_le hch
  have a2 := abs_Gx_sub_sub_le hch
  have a3 : |h| ^ 3 ≤ ρ * h ^ 2 := by
    rw [show |h| ^ 3 = |h| * h ^ 2 by rw [← sq_abs h]; ring]
    exact mul_le_mul_of_nonneg_right hh (sq_nonneg _)
  calc _ ≤ |(k - k0) * (Gx c h - h)| + |k0 * (Gx c h - h - c * h ^ 2 / 2)| := abs_add_le _ _
    _ = |k - k0| * |Gx c h - h| + |k0| * |Gx c h - h - c * h ^ 2 / 2| := by
        rw [abs_mul, abs_mul]
    _ ≤ Kc * ε * (|c| * h ^ 2) + |k0| * (c ^ 2 * (ρ * h ^ 2)) := add_le_add
        (mul_le_mul hk a1 (abs_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_left (a2.trans (mul_le_mul_of_nonneg_left a3 (sq_nonneg c)))
          (abs_nonneg _))
    _ ≤ _ := by
        have t1 := mul_nonneg (mul_nonneg (mul_nonneg hKc (abs_nonneg c)) hρ) (sq_nonneg h)
        have t2 := mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg k0) (sq_nonneg c)) hε)
          (sq_nonneg h)
        nlinarith

/-- Woodford (2003), App. E: `|eᵘ − 1| ≤ 2|u|` for `|u| ≤ 1`, in the form used for the
coefficients. -/
theorem exp_dev {u K ε : ℝ} (hu1 : |u| ≤ 1) (hu : |u| ≤ K * ε) :
    |Real.exp u - 1| ≤ 2 * K * ε := by
  have := Real.abs_exp_sub_one_le hu1
  linarith

/-- Woodford (2003), App. E: `|k eᵘ| ≤ 3|k|` for `|u| ≤ 1`. -/
theorem abs_mul_exp_le {k u : ℝ} (hu : |u| ≤ 1) : |k * Real.exp u| ≤ 3 * |k| := by
  rw [abs_mul, abs_of_pos (Real.exp_pos u)]
  have h1 : Real.exp u ≤ Real.exp 1 := Real.exp_le_exp.2 ((le_abs_self u).trans hu)
  have h2 : Real.exp 1 < 3 := Real.exp_one_lt_three
  nlinarith [abs_nonneg k]

/-! ## The steady-state multipliers and the Hessian -/

/-- Woodford (2003), §5: the steady-state dispersion multiplier `λ̄₄ = A/((1+ω)(1−αβ))` of the
efficient economy. -/
noncomputable def lam4 (p : Par) (A : ℝ) : ℝ := A / ((1 + p.ω) * (1 - p.α * p.β))

/-- Woodford (2003), §5: the steady-state price-index multiplier `λ̄₃ = aλ̄₄/(θ − 1)`. -/
noncomputable def lam3 (p : Par) (A : ℝ) : ℝ := aE p * lam4 p A / (p.θ - 1)

/-- Woodford (2003), §5: these are the steady-state multipliers of the efficient economy. -/
theorem lam_eq (p : Par) (A : ℝ) :
    ramseyLam p (TidyR5RamseyDate0.R0 A) 3 = lam4 p A ∧
      ramseyLam p (TidyR5RamseyDate0.R0 A) 2 = lam3 p A := by
  simp [ramseyLam, TidyR5RamseyDate0.R0, lam4, lam3]

/-- Woodford (2003), §2.2, §3 and App. E (**the Hessian of the Lagrangian at the efficient
steady state**): `H0 = −A(σ+ω)ŷ² − 2AŷΔ̂ − λ̄₄a(1+ωθ)(απ² + (1−α)x̂²) − 2λ̄₄αaπΔ̂₋`. -/
noncomputable def H0 (p : Par) (A : ℝ) (h : Fin 9 → ℝ) (hDp : ℝ) : ℝ :=
  -(A * (p.σ + p.ω) * h 0 ^ 2) - 2 * A * h 4 * h 0 -
    lam4 p A * aE p * p.c0 * (p.α * h 1 ^ 2 + (1 - p.α) * xr p h ^ 2) -
    2 * lam4 p A * p.α * aE p * hDp * h 1

/-- The squared size of a direction at a node: `∑_{i ≤ 4} hᵢ² + h_{Δ,−1}²`. -/
noncomputable def nrm (h : Fin 9 → ℝ) (hDp : ℝ) : ℝ :=
  h 0 ^ 2 + h 1 ^ 2 + h 2 ^ 2 + h 3 ^ 2 + h 4 ^ 2 + hDp ^ 2

/-- Woodford (2003), §2.2 (**the Hessian is negative up to the dispersion cross terms**):
`H0/2 ≤ −(A(σ+ω)/2)ŷ² − (λ̄₄a(1+ωθ)α/2)π² + A|ŷ||Δ̂| + λ̄₄αa|π||Δ̂₋|` for `A > 0`. -/
theorem H0_le {p : Par} (hp : p.Std) {A : ℝ} (hA : 0 < A) (h : Fin 9 → ℝ) (hDp : ℝ) :
    H0 p A h hDp / 2 ≤ -(A * (p.σ + p.ω) / 2) * h 0 ^ 2 -
      lam4 p A * aE p * p.c0 * p.α / 2 * h 1 ^ 2 + A * |h 0| * |h 4| +
        lam4 p A * p.α * aE p * |h 1| * |hDp| := by
  have hl4 : 0 < lam4 p A := by
    unfold lam4
    have : 0 < 1 - p.α * p.β := by linarith [hp.ab_lt_one]
    have : 0 < 1 + p.ω := by linarith [hp.ω_nonneg]
    positivity
  have ha : 0 < aE p := by unfold aE; nlinarith [hp.one_lt_θ, hp.ω_nonneg]
  have hc0 := hp.c0_pos
  have h1α : 0 ≤ 1 - p.α := by linarith [hp.α_lt_one]
  have t1 : -(2 * A * h 4 * h 0) ≤ 2 * A * |h 0| * |h 4| := by
    have := neg_abs_le (h 4 * h 0)
    rw [abs_mul] at this
    nlinarith
  have t2 : -(2 * lam4 p A * p.α * aE p * hDp * h 1) ≤
      2 * lam4 p A * p.α * aE p * |h 1| * |hDp| := by
    have := neg_abs_le (hDp * h 1)
    rw [abs_mul] at this
    have hk : 0 ≤ 2 * lam4 p A * p.α * aE p := by have := hp.α_pos; positivity
    nlinarith
  have t3 : 0 ≤ lam4 p A * aE p * p.c0 * ((1 - p.α) * xr p h ^ 2) := by positivity
  unfold H0
  nlinarith

/-- Woodford (2003), §5: the node data `(e, w, Δ₋, λ₋)` are within `ε` of the efficient steady
state (no disturbances, `ŷ = π = F̂ = K̂ = 0`, `Δ = 1`, `λ₁ = λ₂ = 0`, `λ₃ = λ̄₃`, `λ₄ = λ̄₄`). -/
def Near (p : Par) (A ε : ℝ) (e : Fin 5 → ℝ) (m5 m6 : ℝ) (w : Fin 9 → ℝ) (Dp : ℝ) : Prop :=
  (∀ i, |e i| ≤ ε) ∧ |w 0| ≤ ε ∧ |w 1| ≤ ε ∧ |w 2| ≤ ε ∧ |w 3| ≤ ε ∧ |w 4 - 1| ≤ ε ∧
    |w 5| ≤ ε ∧ |w 6| ≤ ε ∧ |w 7 - lam3 p A| ≤ ε ∧ |w 8 - lam4 p A| ≤ ε ∧ |Dp - 1| ≤ ε ∧
    |m5| ≤ ε ∧ |m6| ≤ ε

/-- Woodford (2003), §1: a direction with all relevant components bounded by `ρ`. -/
def Small (ρ : ℝ) (h : Fin 9 → ℝ) (hDp : ℝ) : Prop :=
  |h 0| ≤ ρ ∧ |h 1| ≤ ρ ∧ |h 2| ≤ ρ ∧ |h 3| ≤ ρ ∧ |h 4| ≤ ρ ∧ |hDp| ≤ ρ

/-- Woodford (2003), App. E (**coefficient deviations**): if `|w − w₀| ≤ K_wε`, `|u| ≤ K_uε` and
`|u| ≤ 1`, then `|weᵘ − w₀| ≤ (3K_w + 2|w₀|K_u)ε`. -/
theorem cdev {w w0 u Kw Ku ε : ℝ} (hu : |u| ≤ Ku * ε) (hu1 : |u| ≤ 1) (hw : |w - w0| ≤ Kw * ε) :
    |w * Real.exp u - w0| ≤ (3 * Kw + 2 * |w0| * Ku) * ε := by
  have e : w * Real.exp u - w0 = (w - w0) * Real.exp u + w0 * (Real.exp u - 1) := by ring
  rw [e]
  have h1 := abs_mul_exp_le (k := w - w0) hu1
  have h2 := Real.abs_exp_sub_one_le hu1
  calc _ ≤ |(w - w0) * Real.exp u| + |w0 * (Real.exp u - 1)| := abs_add_le _ _
    _ ≤ 3 * (Kw * ε) + |w0| * (2 * (Ku * ε)) := by
        rw [abs_mul w0]
        refine add_le_add (h1.trans (by linarith)) (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
        linarith
    _ = _ := by ring

/-- Woodford (2003), App. E: the uniform form of `gE2` (constant `(K_c + MΛ + M)(1 + Λ + 3Λ²)`,
`z² ≤ 2Λ²N`). -/
theorem termE2 {k k0 z ε ρ Kc M Λ N : ℝ} (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (hKc : 0 ≤ Kc) (hM : 0 ≤ M)
    (hΛ : 0 ≤ Λ) (hN : 0 ≤ N) (hk : |k - k0| ≤ Kc * ε) (hk0 : |k0| ≤ M) (hz1 : |z| ≤ 1)
    (hzΛ : |z| ≤ Λ * ρ) (hzn : z ^ 2 ≤ 2 * Λ ^ 2 * N) :
    |k * E2 z - k0 * (z ^ 2 / 2)| ≤ (Kc + M * Λ + M) * (1 + Λ + 3 * Λ ^ 2) * (ε + ρ) * N := by
  have h := gE2 hz1 hε hρ hKc hΛ hk hzΛ
  have h1 : (Kc + |k0| * Λ) ≤ (Kc + M * Λ + M) := by nlinarith [abs_nonneg k0]
  have h2 : 2 * Λ ^ 2 ≤ 1 + Λ + 3 * Λ ^ 2 := by nlinarith
  calc _ ≤ (Kc + |k0| * Λ) * (ε + ρ) * z ^ 2 := h
    _ ≤ (Kc + M * Λ + M) * (ε + ρ) * (2 * Λ ^ 2 * N) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right h1 (by positivity)) hzn (sq_nonneg _)
        have : 0 ≤ Kc + M * Λ + M := by positivity
        positivity
    _ ≤ _ := by
        have : 0 ≤ (Kc + M * Λ + M) * (ε + ρ) * N := by positivity
        nlinarith

/-- Woodford (2003), App. E: the uniform form of `glin` (`q² ≤ N`, `z² ≤ 2Λ²N`). -/
theorem termLin {k k0 z q ε ρ Kc M Λ N : ℝ} (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (hKc : 0 ≤ Kc)
    (hM : 0 ≤ M) (hΛ : 0 ≤ Λ) (hk : |k - k0| ≤ Kc * ε) (hk0 : |k0| ≤ M) (hz1 : |z| ≤ 1)
    (hq : |q| ≤ ρ) (hqn : q ^ 2 ≤ N) (hzn : z ^ 2 ≤ 2 * Λ ^ 2 * N) :
    |k * q * (Real.exp z - 1) - k0 * q * z| ≤
      (Kc + M * Λ + M) * (1 + Λ + 3 * Λ ^ 2) * (ε + ρ) * N := by
  have h := glin hz1 hε hρ hKc hk hq
  have hN : 0 ≤ N := (sq_nonneg q).trans hqn
  have h1 : (Kc + |k0|) ≤ (Kc + M * Λ + M) := by nlinarith [abs_nonneg k0]
  have h3 : q ^ 2 + z ^ 2 ≤ (1 + Λ + 3 * Λ ^ 2) * N := by nlinarith
  calc _ ≤ (Kc + |k0|) * (ε + ρ) * (q ^ 2 + z ^ 2) := h
    _ ≤ (Kc + M * Λ + M) * (ε + ρ) * ((1 + Λ + 3 * Λ ^ 2) * N) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right h1 (by positivity)) h3 (by positivity)
        have : 0 ≤ Kc + M * Λ + M := by positivity
        positivity
    _ = _ := by ring

/-- Woodford (2003), App. E: the uniform form of `gG` (`|c| ≤ Λ`, `h² ≤ N`). -/
theorem termG {k k0 c h ε ρ Kc M Λ N : ℝ} (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (hKc : 0 ≤ Kc) (hM : 0 ≤ M)
    (hΛ : 0 ≤ Λ) (hk : |k - k0| ≤ Kc * ε) (hk0 : |k0| ≤ M) (hch : |c * h| ≤ 1) (hh : |h| ≤ ρ)
    (hc : |c| ≤ Λ) (hhn : h ^ 2 ≤ N) :
    |k * (Gx c h - h) - k0 * (c * h ^ 2 / 2)| ≤
      (Kc + M * Λ + M) * (1 + Λ + 3 * Λ ^ 2) * (ε + ρ) * N := by
  have h0 := gG hch hε hρ hKc hk hh
  have hN : 0 ≤ N := (sq_nonneg h).trans hhn
  have h1 : Kc * |c| + |k0| * c ^ 2 ≤ (Kc + M * Λ + M) * (1 + Λ + 3 * Λ ^ 2) := by
    have hc2 : c ^ 2 ≤ Λ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hc 2
    have a1 : Kc * |c| ≤ Kc * Λ := mul_le_mul_of_nonneg_left hc hKc
    have a2 : |k0| * c ^ 2 ≤ M * Λ ^ 2 := mul_le_mul hk0 hc2 (sq_nonneg _) hM
    nlinarith [mul_nonneg hKc hΛ, mul_nonneg hM hΛ, mul_nonneg (mul_nonneg hM hΛ) hΛ,
      mul_nonneg hKc (sq_nonneg Λ), mul_nonneg (mul_nonneg hM hΛ) (sq_nonneg Λ)]
  calc _ ≤ (Kc * |c| + |k0| * c ^ 2) * (ε + ρ) * h ^ 2 := h0
    _ ≤ ((Kc + M * Λ + M) * (1 + Λ + 3 * Λ ^ 2)) * (ε + ρ) * N := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right h1 (by positivity)) hhn (sq_nonneg _)
        have : 0 ≤ Kc + M * Λ + M := by positivity
        positivity

/-- Woodford (2003), App. E: `(kx)² ≤ 2Λ²N` for `|k| ≤ Λ`, `x² ≤ N`. -/
theorem sq_mul_le {k x Λ N : ℝ} (hk : |k| ≤ Λ) (hx : x ^ 2 ≤ N) (hN : 0 ≤ N) :
    (k * x) ^ 2 ≤ 2 * Λ ^ 2 * N := by
  have hk2 : k ^ 2 ≤ Λ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hk 2
  rw [mul_pow]
  have h1 := mul_le_mul hk2 hx (sq_nonneg _) (sq_nonneg _)
  have h2 : 0 ≤ Λ ^ 2 * N := mul_nonneg (sq_nonneg _) hN
  linarith

/-- Woodford (2003), App. E: `(kx + y)² ≤ 2Λ²N` for `|k| ≤ Λ`, `1 ≤ Λ`, `x² + y² ≤ N`. -/
theorem sq_mul_add_le {k x y Λ N : ℝ} (hk : |k| ≤ Λ) (hΛ : 1 ≤ Λ) (hxy : x ^ 2 + y ^ 2 ≤ N) :
    (k * x + y) ^ 2 ≤ 2 * Λ ^ 2 * N := by
  have hk2 : k ^ 2 ≤ Λ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hk 2
  have hΛ2 : 1 ≤ Λ ^ 2 := by nlinarith
  have e1 : (k * x + y) ^ 2 ≤ 2 * (k ^ 2 * x ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (k * x - y)]
  have e2 : k ^ 2 * x ^ 2 + y ^ 2 ≤ Λ ^ 2 * (x ^ 2 + y ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hk2 (sq_nonneg x), sq_nonneg y]
  have e3 : Λ ^ 2 * (x ^ 2 + y ^ 2) ≤ Λ ^ 2 * N := mul_le_mul_of_nonneg_left hxy (sq_nonneg _)
  linarith

/-- Woodford (2003), App. E: `(k x̂)² ≤ 2Λ²N` for `0 ≤ k`, `2k/(1+ωθ) ≤ Λ`, `h₂² + h₃² ≤ N`. -/
theorem sq_xr_le {p : Par} (hc0 : 0 < p.c0) {k Λ N : ℝ} (hk : 0 ≤ k) (hkΛ : 2 * k / p.c0 ≤ Λ)
    (h : Fin 9 → ℝ) (h23 : h 2 ^ 2 + h 3 ^ 2 ≤ N) : (-(k * xr p h)) ^ 2 ≤ 2 * Λ ^ 2 * N := by
  have hkc : k / p.c0 ≤ Λ := by
    have : k / p.c0 ≤ 2 * k / p.c0 := div_le_div_of_nonneg_right (by linarith) hc0.le
    linarith
  have e : (-(k * xr p h)) ^ 2 = (k / p.c0) ^ 2 * (h 3 - h 2) ^ 2 := by
    unfold xr; field_simp
  rw [e]
  have hk2 : (k / p.c0) ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ (div_nonneg hk hc0.le) hkc 2
  have h32 : (h 3 - h 2) ^ 2 ≤ 2 * N := by nlinarith [sq_nonneg (h 3 + h 2)]
  have := mul_le_mul hk2 h32 (sq_nonneg _) (sq_nonneg _)
  linarith

set_option maxHeartbeats 4000000 in
-- fourteen explicit term estimates in one context
/-- **Woodford (2003), §2.2, §5 and App. E (the Hessian at a nearby plan and the cubic
remainder).** For `A > 0` there are `δ₀ > 0` and `K ≥ 0` such that for node data within
`ε ≤ δ₀` of the efficient steady state and directions bounded by `ρ ≤ δ₀`,
`|R2 − H0/2| ≤ K(ε + ρ)·n`. -/
theorem R2_bound {p : Par} (hp : p.Std) {A : ℝ} (hA : 0 < A) :
    ∃ δ₀ > 0, ∃ K, 0 ≤ K ∧ ∀ (e : Fin 5 → ℝ) (m5 m6 : ℝ) (w : Fin 9 → ℝ) (Dp : ℝ)
      (h : Fin 9 → ℝ) (hDp ε ρ : ℝ), 0 ≤ ε → 0 ≤ ρ → ε ≤ δ₀ → ρ ≤ δ₀ →
        Near p A ε e m5 m6 w Dp → Small ρ h hDp →
          |R2 p A e m5 m6 w Dp h hDp - H0 p A h hDp / 2| ≤ K * (ε + ρ) * nrm h hDp := by
  have hb : 0 < p.θ - 1 := by linarith [hp.one_lt_θ]
  have ha : 0 < aE p := by unfold aE; nlinarith [hp.one_lt_θ, hp.ω_nonneg]
  have hc0 := hp.c0_pos
  have hα0 := hp.α_pos
  have hα1 : 0 < 1 - p.α := by linarith [hp.α_lt_one]
  have hs0 : 0 < 1 - p.α * p.β := by linarith [hp.ab_lt_one]
  have hs1 : 1 - p.α * p.β ≤ 1 := by nlinarith [hp.α_pos, hp.β_pos]
  have hω := hp.ω_nonneg
  have hl4 : 0 < lam4 p A := by unfold lam4; positivity
  have hl3 : 0 < lam3 p A := by unfold lam3; positivity
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = 2 + |p.σ| + |1 - p.σ| + 2 * (1 + p.ω) + 2 * p.ω + 2 * aE p +
      2 * (p.θ - 1) + 4 * (aE p + (p.θ - 1)) / p.c0 := ⟨_, rfl⟩
  have hΛ0 : 0 < Λ := by rw [hΛ]; positivity
  obtain ⟨M, hMd⟩ : ∃ M : ℝ, M = 1 + A + A / (1 + p.ω) + lam3 p A + lam4 p A := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hMd]; positivity
  obtain ⟨Kc, hKcd⟩ : ∃ Kc : ℝ, Kc = 9 * M + 2 * M * Λ := ⟨_, rfl⟩
  have hKc0 : 0 ≤ Kc := by rw [hKcd]; positivity
  obtain ⟨Kt, hKtd⟩ : ∃ Kt : ℝ, Kt = (Kc + M * Λ + M) * (1 + Λ + 3 * Λ ^ 2) := ⟨_, rfl⟩
  have hKt0 : 0 ≤ Kt := by rw [hKtd]; positivity
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 14 * Kt := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨1 / Λ, by positivity, K, hK0, fun e m5 m6 w Dp h hDp ε ρ hε hρ hεδ hρδ hN hS => ?_⟩
  obtain ⟨he, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hDp1, hm5, hm6⟩ := hN
  obtain ⟨hh0, hh1, hh2, hh3, hh4, hhD⟩ := hS
  have hΛε : Λ * ε ≤ 1 := by rw [le_div_iff₀ hΛ0] at hεδ; linarith
  have hΛρ : Λ * ρ ≤ 1 := by rw [le_div_iff₀ hΛ0] at hρδ; linarith
  have hσa := abs_nonneg p.σ
  have hca := abs_nonneg (1 - p.σ)
  have hab0 : 0 ≤ aE p + (p.θ - 1) := by linarith
  have hq0 : 0 ≤ 4 * (aE p + (p.θ - 1)) / p.c0 := div_nonneg (by linarith) hc0.le
  -- `Λ` dominates every coefficient
  have L1 : |p.σ| + |1 - p.σ| ≤ Λ := by rw [hΛ]; linarith
  have L2 : 1 + p.ω + p.ω ≤ Λ := by rw [hΛ]; linarith
  have L3 : |1 - p.σ| + |p.σ| + 1 ≤ Λ := by rw [hΛ]; linarith
  have L4 : 1 + p.ω + p.ω + 1 ≤ Λ := by rw [hΛ]; linarith
  have L5 : p.θ - 1 + 1 ≤ Λ := by rw [hΛ]; linarith
  have L6 : aE p + 1 ≤ Λ := by rw [hΛ]; linarith
  have L7 : 2 * (p.θ - 1) / p.c0 ≤ Λ := by
    rw [hΛ]
    have : 2 * (p.θ - 1) / p.c0 ≤ 4 * (aE p + (p.θ - 1)) / p.c0 :=
      div_le_div_of_nonneg_right (by linarith) hc0.le
    linarith
  have L8 : 2 * aE p / p.c0 ≤ Λ := by
    rw [hΛ]
    have : 2 * aE p / p.c0 ≤ 4 * (aE p + (p.θ - 1)) / p.c0 :=
      div_le_div_of_nonneg_right (by linarith) hc0.le
    linarith
  have L9 : 1 + p.ω ≤ Λ := by rw [hΛ]; linarith
  have L10 : |1 - p.σ| ≤ Λ := by rw [hΛ]; linarith
  have hΛ1 : 1 ≤ Λ := by rw [hΛ]; linarith
  -- arguments of the coefficient exponentials
  have he1 := he 1
  have he2 := he 2
  have he3 := he 3
  have he4 := he 4
  have hxw : |xr p w| ≤ 2 / p.c0 * ε := by
    unfold xr; rw [abs_div, abs_of_pos hc0, div_le_iff₀ hc0]
    have := abs_sub (w 3) (w 2)
    have e : 2 / p.c0 * ε * p.c0 = 2 * ε := by field_simp
    rw [e]; linarith
  have hxh : |xr p h| ≤ 2 / p.c0 * ρ := by
    unfold xr; rw [abs_div, abs_of_pos hc0, div_le_iff₀ hc0]
    have := abs_sub (h 3) (h 2)
    have e : 2 / p.c0 * ρ * p.c0 = 2 * ρ := by field_simp
    rw [e]; linarith
  have hsq := fun i => sq_nonneg (h i)
  have hsqD := sq_nonneg hDp
  have hn0 : h 0 ^ 2 ≤ nrm h hDp := by
    unfold nrm; linarith [hsq 1, hsq 2, hsq 3, hsq 4]
  have hn1 : h 1 ^ 2 ≤ nrm h hDp := by
    unfold nrm; linarith [hsq 0, hsq 2, hsq 3, hsq 4]
  have hn2 : h 2 ^ 2 ≤ nrm h hDp := by
    unfold nrm; linarith [hsq 0, hsq 1, hsq 3, hsq 4]
  have hn3 : h 3 ^ 2 ≤ nrm h hDp := by
    unfold nrm; linarith [hsq 0, hsq 1, hsq 2, hsq 4]
  have hn4 : h 4 ^ 2 ≤ nrm h hDp := by
    unfold nrm; linarith [hsq 0, hsq 1, hsq 2, hsq 3]
  have hnD : hDp ^ 2 ≤ nrm h hDp := by
    unfold nrm; linarith [hsq 0, hsq 1, hsq 2, hsq 3, hsq 4]
  have hn23 : h 2 ^ 2 + h 3 ^ 2 ≤ nrm h hDp := by
    unfold nrm; linarith [hsq 0, hsq 1, hsq 4]
  have hn0' : 0 ≤ nrm h hDp := (sq_nonneg _).trans hn0
  have arg : ∀ {u K : ℝ}, |u| ≤ K * ε → K ≤ Λ → |u| ≤ Λ * ε ∧ |u| ≤ 1 := fun hu hK =>
    ⟨hu.trans (mul_le_mul_of_nonneg_right hK hε),
      (hu.trans (mul_le_mul_of_nonneg_right hK hε)).trans hΛε⟩
  have argh : ∀ {u K : ℝ}, |u| ≤ K * ρ → K ≤ Λ → |u| ≤ Λ * ρ ∧ |u| ≤ 1 := fun hu hK =>
    ⟨hu.trans (mul_le_mul_of_nonneg_right hK hρ),
      (hu.trans (mul_le_mul_of_nonneg_right hK hρ)).trans hΛρ⟩
  have u1 := arg (u := p.σ * e 1 + (1 - p.σ) * w 0) (K := |p.σ| + |1 - p.σ|) (by
    calc _ ≤ |p.σ * e 1| + |(1 - p.σ) * w 0| := abs_add_le _ _
      _ = |p.σ| * |e 1| + |1 - p.σ| * |w 0| := by rw [abs_mul, abs_mul]
      _ ≤ |p.σ| * ε + |1 - p.σ| * ε := add_le_add (mul_le_mul_of_nonneg_left he1 hσa)
          (mul_le_mul_of_nonneg_left hw0 hca)
      _ = _ := by ring) L1
  have absmul : ∀ {k x K : ℝ}, |x| ≤ K * ε → |k * x| ≤ |k| * K * ε := fun hx => by
    rw [abs_mul, mul_assoc]; exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  have u2 := arg (u := (1 + p.ω) * w 0 - p.ω * e 3) (K := 1 + p.ω + p.ω) (by
    have a := absmul (k := 1 + p.ω) (K := 1) (by simpa using hw0)
    have b := absmul (k := p.ω) (K := 1) (by simpa using he3)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + p.ω)] at a
    rw [abs_of_nonneg hω] at b
    calc _ ≤ |(1 + p.ω) * w 0| + |p.ω * e 3| := abs_sub _ _
      _ ≤ _ := by linarith) L2
  have u3 := arg (u := w 2) (K := 1) (by simpa using hw2) hΛ1
  have u4 := arg (u := (1 - p.σ) * w 0 + p.σ * e 1 + e 2) (K := |1 - p.σ| + |p.σ| + 1) (by
    have a := absmul (k := 1 - p.σ) (K := 1) (by simpa using hw0)
    have b := absmul (k := p.σ) (K := 1) (by simpa using he1)
    calc _ ≤ |(1 - p.σ) * w 0 + p.σ * e 1| + |e 2| := abs_add_le _ _
      _ ≤ |(1 - p.σ) * w 0| + |p.σ * e 1| + |e 2| := by
          have := abs_add_le ((1 - p.σ) * w 0) (p.σ * e 1); linarith
      _ ≤ _ := by linarith) L3
  have u5 := arg (u := w 3) (K := 1) (by simpa using hw3) hΛ1
  have u6 := arg (u := (1 + p.ω) * w 0 - p.ω * e 3 + e 4) (K := 1 + p.ω + p.ω + 1) (by
    have a := absmul (k := 1 + p.ω) (K := 1) (by simpa using hw0)
    have b := absmul (k := p.ω) (K := 1) (by simpa using he3)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + p.ω)] at a
    rw [abs_of_nonneg hω] at b
    calc _ ≤ |(1 + p.ω) * w 0 - p.ω * e 3| + |e 4| := abs_add_le _ _
      _ ≤ |(1 + p.ω) * w 0| + |p.ω * e 3| + |e 4| := by
          have := abs_sub ((1 + p.ω) * w 0) (p.ω * e 3); linarith
      _ ≤ _ := by linarith) L4
  have u7 := arg (u := (p.θ - 1) * w 1) (K := p.θ - 1 + 1) (by
    have a := absmul (k := p.θ - 1) (K := 1) (by simpa using hw1)
    rw [abs_of_pos hb] at a; linarith) L5
  have u8 := arg (u := -((p.θ - 1) * xr p w)) (K := 2 * (p.θ - 1) / p.c0) (by
    rw [abs_neg, abs_mul, abs_of_pos hb]
    calc _ ≤ (p.θ - 1) * (2 / p.c0 * ε) := mul_le_mul_of_nonneg_left hxw hb.le
      _ = _ := by ring) L7
  have u9 := arg (u := aE p * w 1) (K := aE p + 1) (by
    have a := absmul (k := aE p) (K := 1) (by simpa using hw1)
    rw [abs_of_pos ha] at a; linarith) L6
  have u10 := arg (u := -(aE p * xr p w)) (K := 2 * aE p / p.c0) (by
    rw [abs_neg, abs_mul, abs_of_pos ha]
    calc _ ≤ aE p * (2 / p.c0 * ε) := mul_le_mul_of_nonneg_left hxw ha.le
      _ = _ := by ring) L8
  have u11 := arg (u := (p.θ - 1) * w 1 + w 2) (K := p.θ - 1 + 1) (by
    have a := absmul (k := p.θ - 1) (K := 1) (by simpa using hw1)
    rw [abs_of_pos hb] at a
    have := abs_add_le ((p.θ - 1) * w 1) (w 2); linarith) L5
  have u12 := arg (u := aE p * w 1 + w 3) (K := aE p + 1) (by
    have a := absmul (k := aE p) (K := 1) (by simpa using hw1)
    rw [abs_of_pos ha] at a
    have := abs_add_le (aE p * w 1) (w 3); linarith) L6
  -- coefficient deviations
  have fin : ∀ {X Kw w0 : ℝ}, X ≤ (3 * Kw + 2 * |w0| * Λ) * ε → Kw ≤ 3 * M → |w0| ≤ M →
      X ≤ Kc * ε := fun hX hKw hw0' => hX.trans (mul_le_mul_of_nonneg_right (by
        rw [hKcd]
        have := mul_le_mul_of_nonneg_right hw0' hΛ0.le
        linarith) hε)
  have hAM : |A| ≤ M := by
    rw [abs_of_pos hA, hMd]
    have : 0 ≤ A / (1 + p.ω) := by positivity
    linarith
  have hAoM : |A / (1 + p.ω)| ≤ M := by
    rw [abs_of_nonneg (by positivity), hMd]; linarith
  have h0M : |(0 : ℝ)| ≤ M := by rw [abs_zero]; exact hM0
  have hαle : p.α ≤ 1 := hp.α_lt_one.le
  have h1αle : 1 - p.α ≤ 1 := by linarith
  have hAo0 : 0 ≤ A / (1 + p.ω) := by positivity
  have h3M : |lam3 p A * p.α| ≤ M := by
    rw [abs_of_nonneg (by positivity), hMd]
    have := mul_le_of_le_one_right hl3.le hαle
    linarith
  have h3M' : |lam3 p A * (1 - p.α)| ≤ M := by
    rw [abs_of_nonneg (by positivity), hMd]
    have := mul_le_of_le_one_right hl3.le h1αle
    linarith
  have h4M : |lam4 p A * p.α| ≤ M := by
    rw [abs_of_nonneg (by positivity), hMd]
    have := mul_le_of_le_one_right hl4.le hαle
    linarith
  have h4M' : |lam4 p A * (1 - p.α)| ≤ M := by
    rw [abs_of_nonneg (by positivity), hMd]
    have := mul_le_of_le_one_right hl4.le h1αle
    linarith
  have h1M : (1 : ℝ) ≤ 3 * M := by rw [hMd]; linarith
  have h0M' : (0 : ℝ) ≤ 3 * M := by linarith
  have hεle1 : ε ≤ 1 := by
    calc ε = 1 * ε := (one_mul ε).symm
      _ ≤ Λ * ε := mul_le_mul_of_nonneg_right hΛ1 hε
      _ ≤ 1 := hΛε
  have k1 : |A * Real.exp (p.σ * e 1) * Real.exp ((1 - p.σ) * w 0) - A| ≤ Kc * ε := by
    rw [mul_assoc, ← Real.exp_add]
    exact fin (cdev (Kw := 0) u1.1 u1.2 (by simp)) h0M' hAM
  have k2a : |A * Real.exp ((1 + p.ω) * w 0 - p.ω * e 3) / (1 + p.ω) * w 4 - A / (1 + p.ω)| ≤
      Kc * ε := by
    rw [show A * Real.exp ((1 + p.ω) * w 0 - p.ω * e 3) / (1 + p.ω) * w 4 =
      A / (1 + p.ω) * w 4 * Real.exp ((1 + p.ω) * w 0 - p.ω * e 3) by ring]
    refine fin (cdev (Kw := A / (1 + p.ω)) u2.1 u2.2 ?_) (by rw [hMd]; linarith) hAoM
    rw [show A / (1 + p.ω) * w 4 - A / (1 + p.ω) = A / (1 + p.ω) * (w 4 - 1) by ring, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ A / (1 + p.ω))]
    exact mul_le_mul_of_nonneg_left hw4 (by positivity)
  have k2b : |A * Real.exp ((1 + p.ω) * w 0 - p.ω * e 3) / (1 + p.ω) - A / (1 + p.ω)| ≤
      Kc * ε := by
    rw [show A * Real.exp ((1 + p.ω) * w 0 - p.ω * e 3) / (1 + p.ω) =
      A / (1 + p.ω) * Real.exp ((1 + p.ω) * w 0 - p.ω * e 3) by ring]
    exact fin (cdev (Kw := 0) u2.1 u2.2 (by simp)) h0M' hAoM
  have k3 : |w 5 * Real.exp (w 2) - 0| ≤ Kc * ε :=
    fin (cdev (Kw := 1) u3.1 u3.2 (by simpa using hw5)) h1M h0M
  have k4 : |w 5 * (1 - p.α * p.β) * Real.exp ((1 - p.σ) * w 0 + p.σ * e 1 + e 2) - 0| ≤
      Kc * ε := by
    refine fin (cdev (Kw := 1) u4.1 u4.2 ?_) h1M h0M
    rw [sub_zero, abs_mul, abs_of_pos hs0, one_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) hs1).trans hw5
  have k5 : |w 6 * Real.exp (w 3) - 0| ≤ Kc * ε :=
    fin (cdev (Kw := 1) u5.1 u5.2 (by simpa using hw6)) h1M h0M
  have k6 : |w 6 * (1 - p.α * p.β) * Real.exp ((1 + p.ω) * w 0 - p.ω * e 3 + e 4) - 0| ≤
      Kc * ε := by
    refine fin (cdev (Kw := 1) u6.1 u6.2 ?_) h1M h0M
    rw [sub_zero, abs_mul, abs_of_pos hs0, one_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) hs1).trans hw6
  have k7a : |w 7 * p.α * Real.exp ((p.θ - 1) * w 1) - lam3 p A * p.α| ≤ Kc * ε := by
    refine fin (cdev (Kw := 1) u7.1 u7.2 ?_) h1M h3M
    rw [show w 7 * p.α - lam3 p A * p.α = p.α * (w 7 - lam3 p A) by ring, abs_mul,
      abs_of_pos hα0, one_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hαle).trans hw7
  have k7b : |w 7 * (1 - p.α) * Real.exp (-((p.θ - 1) * xr p w)) - lam3 p A * (1 - p.α)| ≤
      Kc * ε := by
    refine fin (cdev (Kw := 1) u8.1 u8.2 ?_) h1M h3M'
    rw [show w 7 * (1 - p.α) - lam3 p A * (1 - p.α) = (1 - p.α) * (w 7 - lam3 p A) by ring,
      abs_mul, abs_of_pos hα1, one_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) h1αle).trans hw7
  have hDpa : |Dp| ≤ 2 := by
    have := abs_sub_abs_le_abs_sub Dp 1; rw [abs_one] at this; linarith
  have k8a : |w 8 * p.α * Real.exp (aE p * w 1) * Dp - lam4 p A * p.α| ≤ Kc * ε := by
    rw [show w 8 * p.α * Real.exp (aE p * w 1) * Dp = w 8 * p.α * Dp * Real.exp (aE p * w 1) by
      ring]
    refine fin (cdev (Kw := 2 + lam4 p A) u9.1 u9.2 ?_) (by rw [hMd]; linarith) h4M
    rw [show w 8 * p.α * Dp - lam4 p A * p.α =
      p.α * ((w 8 - lam4 p A) * Dp + lam4 p A * (Dp - 1)) by ring, abs_mul, abs_of_pos hα0]
    have t1 : |(w 8 - lam4 p A) * Dp + lam4 p A * (Dp - 1)| ≤ (2 + lam4 p A) * ε := by
      calc _ ≤ |(w 8 - lam4 p A) * Dp| + |lam4 p A * (Dp - 1)| := abs_add_le _ _
        _ = |w 8 - lam4 p A| * |Dp| + lam4 p A * |Dp - 1| := by
            rw [abs_mul, abs_mul, abs_of_pos hl4]
        _ ≤ ε * 2 + lam4 p A * ε := add_le_add (mul_le_mul hw8 hDpa (abs_nonneg _) hε)
            (mul_le_mul_of_nonneg_left hDp1 hl4.le)
        _ = _ := by ring
    have : p.α * |(w 8 - lam4 p A) * Dp + lam4 p A * (Dp - 1)| ≤
        1 * |(w 8 - lam4 p A) * Dp + lam4 p A * (Dp - 1)| :=
      mul_le_mul_of_nonneg_right hp.α_lt_one.le (abs_nonneg _)
    linarith
  have k8b : |w 8 * p.α * Real.exp (aE p * w 1) - lam4 p A * p.α| ≤ Kc * ε := by
    refine fin (cdev (Kw := 1) u9.1 u9.2 ?_) h1M h4M
    rw [show w 8 * p.α - lam4 p A * p.α = p.α * (w 8 - lam4 p A) by ring, abs_mul,
      abs_of_pos hα0, one_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hαle).trans hw8
  have k8c : |w 8 * (1 - p.α) * Real.exp (-(aE p * xr p w)) - lam4 p A * (1 - p.α)| ≤
      Kc * ε := by
    refine fin (cdev (Kw := 1) u10.1 u10.2 ?_) h1M h4M'
    rw [show w 8 * (1 - p.α) - lam4 p A * (1 - p.α) = (1 - p.α) * (w 8 - lam4 p A) by ring,
      abs_mul, abs_of_pos hα1, one_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) h1αle).trans hw8
  have k9 : |p.α * m5 * Real.exp ((p.θ - 1) * w 1 + w 2) - 0| ≤ Kc * ε := by
    refine fin (cdev (Kw := 1) u11.1 u11.2 ?_) h1M h0M
    rw [sub_zero, abs_mul, abs_of_pos hα0, one_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hαle).trans hm5
  have k10 : |p.α * m6 * Real.exp (aE p * w 1 + w 3) - 0| ≤ Kc * ε := by
    refine fin (cdev (Kw := 1) u12.1 u12.2 ?_) h1M h0M
    rw [sub_zero, abs_mul, abs_of_pos hα0, one_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hαle).trans hm6
  -- the sizes of the increments
  have hn12 : h 1 ^ 2 + h 2 ^ 2 ≤ nrm h hDp := by unfold nrm; linarith [hsq 0, hsq 3, hsq 4]
  have hn13 : h 1 ^ 2 + h 3 ^ 2 ≤ nrm h hDp := by unfold nrm; linarith [hsq 0, hsq 2, hsq 4]
  have hoa : |1 + p.ω| ≤ Λ := by rw [abs_of_nonneg (by linarith)]; exact L9
  have hba : |p.θ - 1| ≤ Λ := by rw [abs_of_pos hb]; linarith
  have haa : |aE p| ≤ Λ := by rw [abs_of_pos ha]; linarith
  have z0c := argh (u := (1 - p.σ) * h 0) (K := |1 - p.σ|) (by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hh0 hca) L10
  have z0o := argh (u := (1 + p.ω) * h 0) (K := 1 + p.ω) (by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + p.ω)]
    exact mul_le_mul_of_nonneg_left hh0 (by linarith)) L9
  have z2 := argh (u := h 2) (K := 1) (by simpa using hh2) hΛ1
  have z3 := argh (u := h 3) (K := 1) (by simpa using hh3) hΛ1
  have z1b := argh (u := (p.θ - 1) * h 1) (K := p.θ - 1) (by
    rw [abs_mul, abs_of_pos hb]; exact mul_le_mul_of_nonneg_left hh1 hb.le) (by linarith)
  have z1a := argh (u := aE p * h 1) (K := aE p) (by
    rw [abs_mul, abs_of_pos ha]; exact mul_le_mul_of_nonneg_left hh1 ha.le) (by linarith)
  have zxb := argh (u := -((p.θ - 1) * xr p h)) (K := 2 * (p.θ - 1) / p.c0) (by
    rw [abs_neg, abs_mul, abs_of_pos hb]
    calc _ ≤ (p.θ - 1) * (2 / p.c0 * ρ) := mul_le_mul_of_nonneg_left hxh hb.le
      _ = _ := by ring) L7
  have zxa := argh (u := -(aE p * xr p h)) (K := 2 * aE p / p.c0) (by
    rw [abs_neg, abs_mul, abs_of_pos ha]
    calc _ ≤ aE p * (2 / p.c0 * ρ) := mul_le_mul_of_nonneg_left hxh ha.le
      _ = _ := by ring) L8
  have z12 := argh (u := (p.θ - 1) * h 1 + h 2) (K := p.θ - 1 + 1) (by
    have a := abs_add_le ((p.θ - 1) * h 1) (h 2)
    rw [abs_mul, abs_of_pos hb] at a
    have := mul_le_mul_of_nonneg_left hh1 hb.le
    linarith) L5
  have z13 := argh (u := aE p * h 1 + h 3) (K := aE p + 1) (by
    have a := abs_add_le (aE p * h 1) (h 3)
    rw [abs_mul, abs_of_pos ha] at a
    have := mul_le_mul_of_nonneg_left hh1 ha.le
    linarith) L6
  -- the fourteen terms
  have hKt : (Kc + M * Λ + M) * (1 + Λ + 3 * Λ ^ 2) = Kt := hKtd.symm
  have b1 := termG hε hρ hKc0 hM0 hΛ0.le k1 hAM z0c.2 hh0 L10 hn0
  have b2a := termE2 hε hρ hKc0 hM0 hΛ0.le hn0' k2a hAoM z0o.2 z0o.1 (sq_mul_le hoa hn0 hn0')
  have b2b := termLin hε hρ hKc0 hM0 hΛ0.le k2b hAoM z0o.2 hh4 hn4 (sq_mul_le hoa hn0 hn0')
  have b3 := termE2 hε hρ hKc0 hM0 hΛ0.le hn0' k3 h0M z2.2 z2.1
    (by simpa using sq_mul_le (k := 1) (by simp; linarith) hn2 hn0')
  have b4 := termE2 hε hρ hKc0 hM0 hΛ0.le hn0' k4 h0M z0c.2 z0c.1 (sq_mul_le L10 hn0 hn0')
  have b5 := termE2 hε hρ hKc0 hM0 hΛ0.le hn0' k5 h0M z3.2 z3.1
    (by simpa using sq_mul_le (k := 1) (by simp; linarith) hn3 hn0')
  have b6 := termE2 hε hρ hKc0 hM0 hΛ0.le hn0' k6 h0M z0o.2 z0o.1 (sq_mul_le hoa hn0 hn0')
  have b7a := termE2 hε hρ hKc0 hM0 hΛ0.le hn0' k7a h3M z1b.2 z1b.1 (sq_mul_le hba hn1 hn0')
  have b7b := termE2 hε hρ hKc0 hM0 hΛ0.le hn0' k7b h3M' zxb.2 zxb.1 (sq_xr_le hc0 hb.le L7 h hn23)
  have b8a := termE2 hε hρ hKc0 hM0 hΛ0.le hn0' k8a h4M z1a.2 z1a.1 (sq_mul_le haa hn1 hn0')
  have b8b := termLin hε hρ hKc0 hM0 hΛ0.le k8b h4M z1a.2 hhD hnD (sq_mul_le haa hn1 hn0')
  have b8c := termE2 hε hρ hKc0 hM0 hΛ0.le hn0' k8c h4M' zxa.2 zxa.1 (sq_xr_le hc0 ha.le L8 h hn23)
  have b9 := termE2 hε hρ hKc0 hM0 hΛ0.le hn0' k9 h0M z12.2 z12.1 (sq_mul_add_le hba hΛ1 hn12)
  have b10 := termE2 hε hρ hKc0 hM0 hΛ0.le hn0' k10 h0M z13.2 z13.1 (sq_mul_add_le haa hΛ1 hn13)
  rw [hKt] at b1 b2a b2b b3 b4 b5 b6 b7a b7b b8a b8b b8c b9 b10
  -- the exact decomposition of the remainder
  have hid : R2 p A e m5 m6 w Dp h hDp - H0 p A h hDp / 2 =
      (A * Real.exp (p.σ * e 1) * Real.exp ((1 - p.σ) * w 0) * (Gx (1 - p.σ) (h 0) - h 0) -
        A * ((1 - p.σ) * h 0 ^ 2 / 2)) -
      (A * Real.exp ((1 + p.ω) * w 0 - p.ω * e 3) / (1 + p.ω) * w 4 * E2 ((1 + p.ω) * h 0) -
        A / (1 + p.ω) * (((1 + p.ω) * h 0) ^ 2 / 2)) -
      (A * Real.exp ((1 + p.ω) * w 0 - p.ω * e 3) / (1 + p.ω) * h 4 *
        (Real.exp ((1 + p.ω) * h 0) - 1) - A / (1 + p.ω) * h 4 * ((1 + p.ω) * h 0)) +
      (w 5 * Real.exp (w 2) * E2 (h 2) - 0 * (h 2 ^ 2 / 2)) -
      (w 5 * (1 - p.α * p.β) * Real.exp ((1 - p.σ) * w 0 + p.σ * e 1 + e 2) *
        E2 ((1 - p.σ) * h 0) - 0 * (((1 - p.σ) * h 0) ^ 2 / 2)) +
      (w 6 * Real.exp (w 3) * E2 (h 3) - 0 * (h 3 ^ 2 / 2)) -
      (w 6 * (1 - p.α * p.β) * Real.exp ((1 + p.ω) * w 0 - p.ω * e 3 + e 4) *
        E2 ((1 + p.ω) * h 0) - 0 * (((1 + p.ω) * h 0) ^ 2 / 2)) +
      (w 7 * p.α * Real.exp ((p.θ - 1) * w 1) * E2 ((p.θ - 1) * h 1) -
        lam3 p A * p.α * (((p.θ - 1) * h 1) ^ 2 / 2)) +
      (w 7 * (1 - p.α) * Real.exp (-((p.θ - 1) * xr p w)) * E2 (-((p.θ - 1) * xr p h)) -
        lam3 p A * (1 - p.α) * ((-((p.θ - 1) * xr p h)) ^ 2 / 2)) -
      (w 8 * p.α * Real.exp (aE p * w 1) * Dp * E2 (aE p * h 1) -
        lam4 p A * p.α * ((aE p * h 1) ^ 2 / 2)) -
      (w 8 * p.α * Real.exp (aE p * w 1) * hDp * (Real.exp (aE p * h 1) - 1) -
        lam4 p A * p.α * hDp * (aE p * h 1)) -
      (w 8 * (1 - p.α) * Real.exp (-(aE p * xr p w)) * E2 (-(aE p * xr p h)) -
        lam4 p A * (1 - p.α) * ((-(aE p * xr p h)) ^ 2 / 2)) -
      (p.α * m5 * Real.exp ((p.θ - 1) * w 1 + w 2) * E2 ((p.θ - 1) * h 1 + h 2) -
        0 * (((p.θ - 1) * h 1 + h 2) ^ 2 / 2)) -
      (p.α * m6 * Real.exp (aE p * w 1 + w 3) * E2 (aE p * h 1 + h 3) -
        0 * ((aE p * h 1 + h 3) ^ 2 / 2)) := by
    have hl3e : lam3 p A * (p.θ - 1) = aE p * lam4 p A := by
      unfold lam3; field_simp
    have hac : aE p - p.c0 = p.θ - 1 := by unfold aE Par.c0; ring
    unfold R2 H0
    have ho0 : 1 + p.ω ≠ 0 := by linarith
    field_simp
    linear_combination (p.θ - 1) * (p.α * h 1 ^ 2 + (1 - p.α) * xr p h ^ 2) *
      (1 + p.ω) * hl3e - (1 + p.ω) * lam4 p A * aE p * (p.α * h 1 ^ 2 + (1 - p.α) * xr p h ^ 2) *
        hac
  rw [hid, abs_le]
  have a1 := abs_le.1 b1
  have a2 := abs_le.1 b2a
  have a3 := abs_le.1 b2b
  have a4 := abs_le.1 b3
  have a5 := abs_le.1 b4
  have a6 := abs_le.1 b5
  have a7 := abs_le.1 b6
  have a8 := abs_le.1 b7a
  have a9 := abs_le.1 b7b
  have a10 := abs_le.1 b8a
  have a11 := abs_le.1 b8b
  have a12 := abs_le.1 b8c
  have a13 := abs_le.1 b9
  have a14 := abs_le.1 b10
  rw [hK]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2, a5.1, a5.2, a6.1,
    a6.2, a7.1, a7.2, a8.1, a8.2, a9.1, a9.2, a10.1, a10.2, a11.1, a11.2, a12.1, a12.2, a13.1,
    a13.2, a14.1, a14.2]

end Woodford.StabilizationWelfare.TidyR6aHess
