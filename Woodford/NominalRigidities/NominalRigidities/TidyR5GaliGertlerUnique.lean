/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.TidyR5GaliGertler

/-!
# The Galí–Gertler model reproducing (3.6) at `β = 1` is unique

Woodford (2003), *Interest and Prices*, Chapter 3, §3.2, p. 217: "in the limiting case `β = 1`,
the two models have identical implications". `TidyR5GaliGertler.gg_identical_beta_one` shows
that for every `γ ∈ [0, 1]` and slope `s > 0` some Galí–Gertler model (Calvo parameter `θ'`,
backward share `ϖ`) reproduces the weights and slope of (3.6). This module shows that the model
is unique:

* `slopeFn_strictAntiOn`: `θ ↦ (1 − θγ)(1 − θ)²/θ` is strictly decreasing on `(0, 1)`.
* `gg_beta_one_share`: matching the weights at `β = 1` forces `ϖ = θγ`.
* `gg_identical_beta_one_existsUnique`: there is exactly one pair `(θ', ϖ)` with
  `θ' ∈ (0, 1)`, `ϖ ∈ [0, 1)` reproducing (3.6).
-/

namespace Woodford.NominalRigidities.TidyR5GaliGertlerUnique

open TidyR5GaliGertler

/-- Woodford (2003), p. 217: for `0 ≤ γ ≤ 1` the slope function `(1 − θγ)(1 − θ)²/θ` is strictly
decreasing in the Calvo parameter `θ ∈ (0, 1)`. -/
theorem slopeFn_strictAntiOn {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    StrictAntiOn (slopeFn γ) (Set.Ioo 0 1) := by
  intro x hx y hy hxy
  obtain ⟨hx0, -⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  unfold slopeFn
  have h1 : 0 < 1 - y * γ := by nlinarith
  have h2 : 1 - y * γ ≤ 1 - x * γ := by nlinarith
  have h3 : (1 - y) ^ 2 / y < (1 - x) ^ 2 / x := by
    rw [div_lt_div_iff₀ hy0 hx0]
    have hxy1 : 0 < 1 - x * y := by nlinarith
    have key : (1 - x) ^ 2 * y - (1 - y) ^ 2 * x = (y - x) * (1 - x * y) := by ring
    nlinarith [mul_pos (sub_pos.mpr hxy) hxy1]
  have h4 : 0 ≤ (1 - x) ^ 2 / x := div_nonneg (sq_nonneg _) hx0.le
  calc (1 - y * γ) * (1 - y) ^ 2 / y = (1 - y * γ) * ((1 - y) ^ 2 / y) := by ring
    _ < (1 - y * γ) * ((1 - x) ^ 2 / x) := mul_lt_mul_of_pos_left h3 h1
    _ ≤ (1 - x * γ) * ((1 - x) ^ 2 / x) := mul_le_mul_of_nonneg_right h2 h4
    _ = (1 - x * γ) * (1 - x) ^ 2 / x := by ring

/-- Woodford (2003), p. 217: at `β = 1`, Galí–Gertler weights `γ/(1 + γ)` and `1/(1 + γ)` force
the backward share `ϖ = θγ`. -/
theorem gg_beta_one_share {θ ϖ γ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hϖ0 : 0 ≤ ϖ) (hγ0 : 0 ≤ γ)
    (hb : ggBack θ 1 ϖ = γ / (1 + γ)) (hf : ggFwd θ 1 ϖ = 1 / (1 + γ)) : ϖ = θ * γ := by
  have hφ := ggPhi_pos hθ0 hθ1 zero_le_one hϖ0
  have hd : (0 : ℝ) < 1 + γ := by linarith
  unfold ggBack at hb
  unfold ggFwd at hf
  rw [div_eq_div_iff hφ.ne' hd.ne'] at hb hf
  have hφeq : θ * (1 + γ) = ggPhi θ 1 ϖ := by linear_combination hf
  have : (ϖ - θ * γ) * (1 + γ) = 0 := by linear_combination hb - γ * hφeq
  have := (mul_eq_zero.mp this).resolve_right hd.ne'
  linarith

/-- Woodford (2003), p. 217 (**the Galí–Gertler model matching (3.6) at `β = 1` is unique**): for
`0 ≤ γ ≤ 1` and `s > 0` there is exactly one pair `(θ', ϖ)` with `0 < θ' < 1`, `0 ≤ ϖ < 1`
whose weights are `γ/(1 + γ)`, `1/(1 + γ)` and whose slope is `s/(1 + γ)`. -/
theorem gg_identical_beta_one_existsUnique {γ s : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hs : 0 < s) :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ p.1 < 1 ∧ 0 ≤ p.2 ∧ p.2 < 1 ∧
      ggBack p.1 1 p.2 = γ / (1 + γ) ∧ ggFwd p.1 1 p.2 = 1 / (1 + γ) ∧
      ggSlope p.1 1 p.2 = s / (1 + γ) := by
  obtain ⟨θ', h0, h1, h2, h3, hb, hf, hsl⟩ := gg_identical_beta_one hγ0 hγ1 hs
  have hγ : (1 : ℝ) + γ ≠ 0 := by linarith
  -- the slope condition is `slopeFn γ θ = s`
  have hslope : ∀ θ, 0 < θ → (ggSlope θ 1 (θ * γ) = s / (1 + γ) ↔ slopeFn γ θ = s) := by
    intro θ hθ
    rw [ggSlope, ggPhi_beta_one, slopeFn]
    have hθ' : θ ≠ 0 := hθ.ne'
    constructor <;> intro h
    · field_simp at h ⊢; linear_combination h
    · field_simp at h ⊢; linear_combination h
  refine ⟨(θ', θ' * γ), ⟨h0, h1, h2, h3, hb, hf, hsl⟩, ?_⟩
  rintro ⟨θ, ϖ⟩ ⟨k0, k1, k2, k3, kb, kf, ksl⟩
  simp only at k0 k1 k2 k3 kb kf ksl
  have hϖ := gg_beta_one_share k0 k1 k2 hγ0 kb kf
  subst hϖ
  have e1 := (hslope θ k0).mp ksl
  have e2 := (hslope θ' h0).mp hsl
  have hθ : θ = θ' := (slopeFn_strictAntiOn hγ0 hγ1).injOn ⟨k0, k1⟩ ⟨h0, h1⟩ (e1.trans e2.symm)
  subst hθ
  rfl

end Woodford.NominalRigidities.TidyR5GaliGertlerUnique
