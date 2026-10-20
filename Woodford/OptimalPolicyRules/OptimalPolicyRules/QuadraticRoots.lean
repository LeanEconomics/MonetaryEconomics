/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The roots of `βλ² − (1 + β + c)λ + 1`

Woodford (2003), *Interest and Prices*, Ch. 3, Prop. 3.4, p. 182, and App. B.3, pp. 659–660; used
throughout Chapter 8 (survey §4.3, the workhorse second-order equation of §2.1, (2.9), (2.32),
(3.10) and Lemma G.2, p. 720).

For `0 < β` and `c > 0` the quadratic `βλ² − (1 + β + c)λ + 1` has two real roots
`0 < λ₁ < 1 < λ₂` with `λ₁ + λ₂ = (1 + β + c)/β` and `λ₁λ₂ = β⁻¹` (`lam1`, `lam2`,
`lam1_add_lam2`, `lam1_mul_lam2`, `lam1_lt_one_lt_lam2`, `lam1_pos`). This is the single copy of
these facts for the chapter (the stable root `μ₁` of the §2.1 workhorse is `lam1`; the roots of
(3.10) in Lemma G.2 are `lam1 β (κσ)`, `lam2 β (κσ)`).
-/

namespace Woodford.OptimalPolicyRules.QuadraticRoots

/-! ### The roots of `βλ² − (1 + β + c)λ + 1` -/

/-- Woodford (2003), Ch. 8, p. 571 (via Ch. 3 eq. (2.10)): the characteristic polynomial
`βλ² − (1 + β + c)λ + 1` of the second-order equation behind (2.32) (restated from the Chapter 3
project). -/
def charPoly (β c x : ℝ) : ℝ := β * x ^ 2 - (1 + β + c) * x + 1

/-- Woodford (2003), Ch. 3, App. B.3, p. 659: the discriminant `(1 + β + c)² − 4β`. -/
def charDisc (β c : ℝ) : ℝ := (1 + β + c) ^ 2 - 4 * β

/-- Woodford (2003), Ch. 3, Prop. 3.4, p. 182: the smaller root `λ₁` (restated). -/
noncomputable def lam1 (β c : ℝ) : ℝ := ((1 + β + c) - Real.sqrt (charDisc β c)) / (2 * β)

/-- Woodford (2003), Ch. 3, Prop. 3.4, p. 182: the larger root `λ₂` (restated). -/
noncomputable def lam2 (β c : ℝ) : ℝ := ((1 + β + c) + Real.sqrt (charDisc β c)) / (2 * β)

/-- Woodford (2003), Ch. 3, App. B.3, p. 659: the discriminant is positive (restated). -/
theorem charDisc_pos {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : 0 < charDisc β c := by
  unfold charDisc
  nlinarith [sq_nonneg (1 - β)]

/-- Woodford (2003), Ch. 3, App. B.3, p. 660 (Vieta): `λ₁ + λ₂ = (1 + β + c)/β` (restated). -/
theorem lam1_add_lam2 {β c : ℝ} (hβ : 0 < β) : lam1 β c + lam2 β c = (1 + β + c) / β := by
  unfold lam1 lam2
  field_simp
  ring

/-- Woodford (2003), Ch. 3, fn. 41, p. 186 (Vieta): `λ₁λ₂ = β⁻¹` (restated). -/
theorem lam1_mul_lam2 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : lam1 β c * lam2 β c = β⁻¹ := by
  have h := Real.sq_sqrt (charDisc_pos hβ hc).le
  have hm : ((1 + β + c) - Real.sqrt (charDisc β c)) * ((1 + β + c) + Real.sqrt (charDisc β c))
      = 4 * β := by
    unfold charDisc at h ⊢
    linear_combination (-1 : ℝ) * h
  unfold lam1 lam2
  rw [div_mul_div_comm, hm]
  field_simp
  ring

/-- Woodford (2003), Ch. 3, App. B.3, p. 659: `P(x) = β(x − λ₁)(x − λ₂)` (restated). -/
theorem charPoly_factor {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (x : ℝ) :
    charPoly β c x = β * (x - lam1 β c) * (x - lam2 β c) := by
  have hs := lam1_add_lam2 (c := c) hβ
  have hp := lam1_mul_lam2 hβ hc
  have e : β * (x - lam1 β c) * (x - lam2 β c)
      = β * x ^ 2 - β * (lam1 β c + lam2 β c) * x + β * (lam1 β c * lam2 β c) := by ring
  rw [e, hs, hp, charPoly]
  field_simp

/-- Woodford (2003), Ch. 3, Prop. 3.4, p. 182: `λ₁ < λ₂` (restated). -/
theorem lam1_lt_lam2 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : lam1 β c < lam2 β c := by
  have h := Real.sqrt_pos.mpr (charDisc_pos hβ hc)
  unfold lam1 lam2
  exact div_lt_div_of_pos_right (by linarith) (by positivity)

/-- Woodford (2003), Ch. 3, App. B.3, p. 660: `β(λ₁ + λ₂) = 1 + β + c` (restated). -/
theorem beta_mul_sum {β c : ℝ} (hβ : 0 < β) : β * (lam1 β c + lam2 β c) = 1 + β + c := by
  rw [lam1_add_lam2 hβ]; field_simp

/-- Woodford (2003), Ch. 3, App. B.3, p. 660: `βλ₁λ₂ = 1` (restated). -/
theorem beta_mul_prod {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : β * (lam1 β c * lam2 β c) = 1 := by
  rw [lam1_mul_lam2 hβ hc]; field_simp

/-- Woodford (2003), Ch. 3, App. B.3, p. 659: `P(x) < 0` forces `λ₁ < x < λ₂` (restated). -/
theorem between_roots_of_neg {β c x : ℝ} (hβ : 0 < β) (hc : 0 < c) (hx : charPoly β c x < 0) :
    lam1 β c < x ∧ x < lam2 β c := by
  rw [charPoly_factor hβ hc] at hx
  have h12 := lam1_lt_lam2 hβ hc
  constructor
  · by_contra h
    push Not at h
    have : 0 ≤ β * (x - lam1 β c) * (x - lam2 β c) :=
      mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hβ.le (by linarith))
        (by linarith)
    linarith
  · by_contra h
    push Not at h
    have : 0 ≤ β * (x - lam1 β c) * (x - lam2 β c) :=
      mul_nonneg (mul_nonneg hβ.le (by linarith)) (by linarith)
    linarith

/-- Woodford (2003), Ch. 3, App. B.3, p. 659: `P(1) = −c` (restated). -/
theorem charPoly_one (β c : ℝ) : charPoly β c 1 = -c := by
  simp only [charPoly]; ring

/-- Woodford (2003), Ch. 3, Prop. 3.4, p. 182: `λ₁ < 1 < λ₂` (restated). -/
theorem lam1_lt_one_lt_lam2 {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    lam1 β c < 1 ∧ 1 < lam2 β c :=
  between_roots_of_neg hβ hc (by rw [charPoly_one]; linarith)

/-- Woodford (2003), Ch. 3, Prop. 3.4, p. 182: `λ₁ > 0` (restated). -/
theorem lam1_pos {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : 0 < lam1 β c := by
  have h1 := (lam1_lt_one_lt_lam2 hβ hc).2
  have hp := lam1_mul_lam2 hβ hc
  have hinv : 0 < β⁻¹ := inv_pos.mpr hβ
  by_contra h
  push Not at h
  have : lam1 β c * lam2 β c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by linarith)
  linarith

/-- Woodford (2003), survey §4.3 (Ch. 7 (2.29), Ch. 8 (2.9)): `λ₁` is a root,
`β λ₁² − (1 + β + c) λ₁ + 1 = 0`. -/
theorem lam1_root {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    β * lam1 β c ^ 2 - (1 + β + c) * lam1 β c + 1 = 0 := by
  have h := charPoly_factor hβ hc (lam1 β c)
  rw [sub_self, mul_zero, zero_mul] at h
  unfold charPoly at h
  exact h

/-- Woodford (2003), survey §4.3: `λ₁ < 1` (since `c > 0`). -/
theorem lam1_lt_one {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) : lam1 β c < 1 :=
  (lam1_lt_one_lt_lam2 hβ hc).1

/-- Woodford (2003), survey §4.3: `0 ≤ β λ₁ < 1` (for `0 < β < 1`). -/
theorem beta_lam1_mem {β c : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hc : 0 < c) :
    0 ≤ β * lam1 β c ∧ β * lam1 β c < 1 := by
  have h1 := lam1_pos hβ0 hc
  have h2 := lam1_lt_one hβ0 hc
  exact ⟨by positivity, by nlinarith⟩

/-- Woodford (2003), (2.14), p. 566 (the flexible-wage limit): `λ₁ ≤ (1 + β)/(1 + β + c)`, so
`λ₁ → 0` as `c → ∞`. -/
theorem lam1_le {β c : ℝ} (hβ0 : 0 < β) (hc : 0 < c) :
    lam1 β c ≤ (1 + β) / (1 + β + c) := by
  have hμ0 := lam1_pos hβ0 hc
  have hμ1 := lam1_lt_one hβ0 hc
  have hr := lam1_root hβ0 hc
  rw [le_div_iff₀ (by linarith)]
  nlinarith [mul_pos hβ0 hμ0]

end Woodford.OptimalPolicyRules.QuadraticRoots
