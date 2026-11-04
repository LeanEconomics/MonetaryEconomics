/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR5InertiaSingular
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Algebra.Polynomial.Roots

/-!
# The genericity condition of (18.2) as a polynomial condition in the parameters

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 18, eq. (18.2), p. 427, with the
three-equation model (17.15)–(17.17), p. 407, and the roots (5.6), p. 119.

`TidyR5Inertia.generic182_iff` and `TidyR5InertiaForward.determinate182_closed_iff` state the
Blanchard–Kahn genericity condition of the inertial rule (18.2) at the explicit root
`μ* = 1/λ₁ = λ₂/β` of the peg polynomial `q(μ) = βμ² − (1 + β + σκ)μ + 1`:
`G(μ*) ≠ 0`, `G(μ) = κ(φ_π + φ_{π,1}μ) + (φ_x + φ_{x,1}μ)(1 − βμ)`. Here `μ*` is eliminated.

* `resp_eq_lin`: on the roots of `q`, `G(μ) = A + Bμ` with the polynomials
  `A = κφ_π + φ_x + φ_{x,1}` (`gA`) and `B = κφ_{π,1} − βφ_x − φ_{x,1}(β + σκ)` (`gB`).
* `res182 = βA² + (1 + β + σκ)AB + B²`, the resultant of `q` and `A + Bμ` (`= B² q(−A/B)`).
* **`resp_zero_iff`**: for `σ, κ, β > 0`, `G(μ*) = 0` iff `res182 = 0` and `B(A + B) ≥ 0`.
  The sign condition selects the root `μ* < 1` from the other root `1/λ₂ > 1` of `q`
  (`B(A + B) = B²(1 − r)` at the common root `r = −A/B`). The resultant alone is **not**
  equivalent: `res182_zero_but_generic` has `res182 = 0`, the response condition satisfied and the
  system generic (the common root is `1/λ₂ = 4`).
* **`generic182_iff_poly`**, **`determinate182_poly_iff`**, **`determinate182_singular_poly_iff`**:
  genericity, and determinacy of (18.2) in both the regular and the singular case, as polynomial
  (in)equalities in the eight parameters `σ, β, κ, φ_i, φ_π, φ_x, φ_{π,1}, φ_{x,1}`.
* The failure set: it is contained in the hypersurface `res182 = 0` of a nonzero polynomial
  (`nongeneric_subset_res`, `res182_ne_zero_somewhere`); it is nonempty (no feedback at all,
  `nongeneric_no_response`, and with feedback, `nongeneric_with_response`) and a strict subset of
  that hypersurface within the admissible region (`res182_zero_but_generic`). It is semialgebraic
  (`resp_zero_iff`), and has Lebesgue measure zero in `ℝ⁸` (`volume_nonGeneric`): for every
  value of the other seven parameters the failure set in `φ_π` has at most two points
  (`res182_slice_finite`).
-/

namespace Cochrane.KeynesianStickyPrices.TidyR6Genericity182

open Polynomial MeasureTheory FullModel TidyR5BlanchardKahn TidyR5Inertia TidyR5InertiaForward
open TidyR5InertiaSingular

/-! ### The polynomials -/

/-- Cochrane (2023), eq. (18.2), p. 427: the constant term `A = κφ_π + φ_x + φ_{x,1}` of the
response function reduced modulo the peg polynomial. -/
def gA (κ φπ φx φx1 : ℝ) : ℝ := κ * φπ + φx + φx1

/-- Cochrane (2023), eq. (18.2), p. 427: the linear coefficient
`B = κφ_{π,1} − βφ_x − φ_{x,1}(β + σκ)` of the response function reduced modulo the peg
polynomial. -/
def gB (σ β κ φx φπ1 φx1 : ℝ) : ℝ := κ * φπ1 - β * φx - φx1 * (β + σ * κ)

/-- Cochrane (2023), eq. (18.2), p. 427 with (5.6): the resultant
`βA² + (1 + β + σκ)AB + B²` of the peg polynomial `βμ² − (1 + β + σκ)μ + 1` and `A + Bμ`. -/
def res182 (σ β κ φπ φx φπ1 φx1 : ℝ) : ℝ :=
  β * gA κ φπ φx φx1 ^ 2 + (1 + β + σ * κ) * gA κ φπ φx φx1 * gB σ β κ φx φπ1 φx1 +
    gB σ β κ φx φπ1 φx1 ^ 2

/-- Cochrane (2023), eq. (18.2), p. 427: the response of the rule along a direction `μ`,
`G(μ) = κ(φ_π + φ_{π,1}μ) + (φ_x + φ_{x,1}μ)(1 − βμ)`. -/
def resp (β κ φπ φx φπ1 φx1 μ : ℝ) : ℝ :=
  κ * (φπ + φπ1 * μ) + (φx + φx1 * μ) * (1 - β * μ)

/-- Cochrane (2023), eq. (18.2) with (5.6): on a root of the peg polynomial,
`G(μ) = A + Bμ`. -/
theorem resp_eq_lin {σ β κ φπ φx φπ1 φx1 μ : ℝ}
    (hq : β * μ ^ 2 - (1 + β + σ * κ) * μ + 1 = 0) :
    resp β κ φπ φx φπ1 φx1 μ = gA κ φπ φx φx1 + gB σ β κ φx φπ1 φx1 * μ := by
  unfold resp gA gB
  linear_combination (-φx1) * hq

/-- Cochrane (2023), eq. (5.6): the resultant is `B² q(r)` at `r = −A/B`, in the polynomial form
`βA² + sAB + B² = B²(βr² − sr + 1)` whenever `A = −Br`. -/
theorem res182_of_root {σ β κ φπ φx φπ1 φx1 r : ℝ}
    (h : gA κ φπ φx φx1 = -(gB σ β κ φx φπ1 φx1 * r)) :
    res182 σ β κ φπ φx φπ1 φx1 =
      gB σ β κ φx φπ1 φx1 ^ 2 * (β * r ^ 2 - (1 + β + σ * κ) * r + 1) := by
  unfold res182
  rw [h]
  ring

/-- Cochrane (2023), eq. (5.6), p. 119: `μ* = 1/λ₁` is a root of the peg polynomial
`βμ² − (1 + β + σκ)μ + 1`.
Restates `TidyR5InertiaSingular.peg_root_lam1`. -/
theorem peg_inv_lam1 {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) :
    β * (lam1 σ β κ)⁻¹ ^ 2 - (1 + β + σ * κ) * (lam1 σ β κ)⁻¹ + 1 = 0 := by
  have h := peg_root_lam1 ha hβ
  linear_combination h

/-- Cochrane (2023), eq. (5.6), p. 119: a root `r ≤ 1` of the peg polynomial is `1/λ₁` (the
other root `1/λ₂` exceeds one).
Compare `TidyR5Inertia.peg_root` and `PersistenceFreedom.one_lt_inv_lam2`. -/
theorem peg_root_le_one {σ β κ r : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β)
    (hq : β * r ^ 2 - (1 + β + σ * κ) * r + 1 = 0) (hr : r ≤ 1) : r = (lam1 σ β κ)⁻¹ := by
  have hs := lam_sum σ β κ
  have hp := lam_prod ha hβ
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans (one_lt_lam1 ha hβ)
  have hfac : (lam1 σ β κ * r - 1) * (lam2 σ β κ * r - 1) = 0 := by
    linear_combination hq + r ^ 2 * hp - r * hs
  rcases mul_eq_zero.mp hfac with h | h
  · field_simp
    linarith
  · exfalso
    have : lam2 σ β κ * r < 1 := by nlinarith
    linarith

/-- **The genericity condition without the root** (Cochrane (2023), eq. (18.2), p. 427, with
(5.6)): for `σ, κ, β > 0`, the response along the peg's stable direction vanishes,
`G(1/λ₁) = 0`, iff `βA² + (1 + β + σκ)AB + B² = 0` and `B(A + B) ≥ 0`. -/
theorem resp_zero_iff {σ β κ φπ φx φπ1 φx1 : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    resp β κ φπ φx φπ1 φx1 (lam1 σ β κ)⁻¹ = 0 ↔
      res182 σ β κ φπ φx φπ1 φx1 = 0 ∧
        0 ≤ gB σ β κ φx φπ1 φx1 * (gA κ φπ φx φx1 + gB σ β κ φx φπ1 φx1) := by
  have ha := mul_pos hσ hκ
  have hq := peg_inv_lam1 ha hβ
  have hl1 := one_lt_lam1 ha hβ
  have hm1 : (lam1 σ β κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  rw [resp_eq_lin hq]
  set A := gA κ φπ φx φx1
  set B := gB σ β κ φx φπ1 φx1
  set m := (lam1 σ β κ)⁻¹
  constructor
  · intro h
    have hA : A = -(B * m) := by linarith
    refine ⟨?_, ?_⟩
    · rw [res182_of_root hA, hq, mul_zero]
    · rw [hA]
      have : B * (-(B * m) + B) = B ^ 2 * (1 - m) := by ring
      rw [this]
      exact mul_nonneg (sq_nonneg B) (by linarith)
  · rintro ⟨hR, hS⟩
    by_cases hB : B = 0
    · have hR' : β * A ^ 2 = 0 := by
        have : res182 σ β κ φπ φx φπ1 φx1 = β * A ^ 2 + (1 + β + σ * κ) * A * B + B ^ 2 := rfl
        rw [this, hB] at hR
        linarith
      have hA : A = 0 := by
        rcases mul_eq_zero.mp hR' with h | h
        · exact absurd h hβ.ne'
        · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
      rw [hA, hB]
      ring
    · set r := -A / B with hr
      have hAr : A = -(B * r) := by rw [hr]; field_simp
      have hqr : β * r ^ 2 - (1 + β + σ * κ) * r + 1 = 0 := by
        have h1 := res182_of_root hAr
        rw [hR] at h1
        have hB2 : B ^ 2 ≠ 0 := pow_ne_zero 2 hB
        rcases mul_eq_zero.mp h1.symm with h | h
        · exact absurd h hB2
        · exact h
      have hr1 : r ≤ 1 := by
        rw [hAr] at hS
        have : B * (-(B * r) + B) = B ^ 2 * (1 - r) := by ring
        rw [this] at hS
        have hB2 : 0 < B ^ 2 := by positivity
        by_contra hc
        push Not at hc
        have : B ^ 2 * (1 - r) < 0 := mul_neg_of_pos_of_neg hB2 (by linarith)
        linarith
      have hrm := peg_root_le_one ha hβ hqr hr1
      rw [hAr, hrm]
      ring

/-- Cochrane (2023), eq. (18.2), p. 427: the response condition at `μ* = 1/λ₁` as stated in
`TidyR5Inertia.generic182_iff` is `G(1/λ₁) ≠ 0`. -/
theorem resp_def (β κ φπ φx φπ1 φx1 l : ℝ) :
    κ * (φπ + φπ1 * l⁻¹) + (φx + φx1 * l⁻¹) * (1 - β * l⁻¹) = resp β κ φπ φx φπ1 φx1 l⁻¹ :=
  rfl

/-- **Genericity of (18.2) as a polynomial condition** (Cochrane (2023), eq. (18.2), p. 427): for
`σ, κ, β > 0` and `1 − σφ_{x,1} ≠ 0`, the Blanchard–Kahn genericity condition holds iff
`βA² + (1 + β + σκ)AB + B² ≠ 0` or `B(A + B) < 0`.
Polynomial form of `TidyR5Inertia.generic182_iff`. -/
theorem generic182_iff_poly {σ β κ φi φπ φx φπ1 φx1 : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hg : 1 - σ * φx1 ≠ 0) :
    Generic (A182 σ β κ φi φπ φx φπ1 φx1) ↔
      res182 σ β κ φπ φx φπ1 φx1 ≠ 0 ∨
        gB σ β κ φx φπ1 φx1 * (gA κ φπ φx φx1 + gB σ β κ φx φπ1 φx1) < 0 := by
  rw [generic182_iff hσ hκ hβ hg, resp_def, Ne, resp_zero_iff hσ hκ hβ, not_and_or, not_le]

/-- Cochrane (2023), eq. (18.2), p. 427: the response condition at `λ₂/β` (the form used in
`TidyR5InertiaForward.determinate182_closed_iff`) is the polynomial condition. -/
theorem resp_lam2_ne_iff {σ β κ φπ φx φπ1 φx1 : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    κ * (φπ + φπ1 * (lam2 σ β κ / β)) + (φx + φx1 * (lam2 σ β κ / β)) *
        (1 - β * (lam2 σ β κ / β)) ≠ 0 ↔
      res182 σ β κ φπ φx φπ1 φx1 ≠ 0 ∨
        gB σ β κ φx φπ1 φx1 * (gA κ φπ φx φx1 + gB σ β κ φx φπ1 φx1) < 0 := by
  rw [← lam1_inv_eq (mul_pos hσ hκ) hβ, resp_def, Ne, resp_zero_iff hσ hκ hβ, not_and_or,
    not_le]

/-- **Determinacy of (18.2) in the eight parameters** (Cochrane (2023), eq. (18.2), p. 427; the
book makes no claim): for `σ, κ, β > 0` and `1 − σφ_{x,1} ≠ 0`, under any expectation system on
a nonempty state space, determinate iff the closed-form root count of
`TidyR5InertiaForward.determinate182_closed_iff` holds and
`βA² + (1 + β + σκ)AB + B² ≠ 0 ∨ B(A + B) < 0` — every condition a polynomial (in)equality. -/
theorem determinate182_poly_iff {Ω : Type*} (𝔼 : ExpectationSystem Ω) [Nonempty Ω]
    {σ β κ φi φπ φx φπ1 φx1 : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hg : 1 - σ * φx1 ≠ 0) :
    Determinate182 𝔼 σ β κ φi φπ φx φπ1 φx1 ↔
      ((D1 σ β κ φi φπ φx φπ1 φx1 * kk σ β φx1 < 0 ∧
            0 < Dm1 σ β κ φi φπ φx φπ1 φx1 * kk σ β φx1) ∨
          (Dm1 σ β κ φi φπ φx φπ1 φx1 * kk σ β φx1 < 0 ∧
            0 < D1 σ β κ φi φπ φx φπ1 φx1 * kk σ β φx1 ∧
            (0 < C15num σ β κ φi φπ φx φπ1 φx1 ∨
              3 * |kk σ β φx1| < |N2 σ β κ φi φx φπ1 φx1|))) ∧
        (res182 σ β κ φπ φx φπ1 φx1 ≠ 0 ∨
          gB σ β κ φx φπ1 φx1 * (gA κ φπ φx φx1 + gB σ β κ φx φπ1 φx1) < 0) := by
  rw [determinate182_closed_iff 𝔼 hσ hκ hβ hg, resp_lam2_ne_iff hσ hκ hβ]

/-- **Determinacy of (18.2) in the singular case, polynomially** (Cochrane (2023), eq. (18.2),
p. 427): for `σ, κ, β > 0` and `σφ_{x,1} = 1`, determinate iff `D₁D₋₁ < 0` and
`βA² + (1 + β + σκ)AB + B² ≠ 0 ∨ B(A + B) < 0`.
Polynomial form of `TidyR5InertiaSingular.determinate182_singular_iff`. -/
theorem determinate182_singular_poly_iff {Ω : Type*} (𝔼 : ExpectationSystem Ω) [Nonempty Ω]
    {σ β κ φi φπ φx φπ1 φx1 : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hg0 : 1 - σ * φx1 = 0) :
    Determinate182 𝔼 σ β κ φi φπ φx φπ1 φx1 ↔
      D1 σ β κ φi φπ φx φπ1 φx1 * Dm1 σ β κ φi φπ φx φπ1 φx1 < 0 ∧
        (res182 σ β κ φπ φx φπ1 φx1 ≠ 0 ∨
          gB σ β κ φx φπ1 φx1 * (gA κ φπ φx φx1 + gB σ β κ φx φπ1 φx1) < 0) := by
  rw [determinate182_singular_iff 𝔼 hσ hκ hβ hg0, resp_lam2_ne_iff hσ hκ hβ]

/-! ### The set where genericity fails -/

/-- Cochrane (2023), eq. (18.2), p. 427: if genericity fails then the parameters lie on the
hypersurface `βA² + (1 + β + σκ)AB + B² = 0`. -/
theorem nongeneric_subset_res {σ β κ φi φπ φx φπ1 φx1 : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (hg : 1 - σ * φx1 ≠ 0) (h : ¬ Generic (A182 σ β κ φi φπ φx φπ1 φx1)) :
    res182 σ β κ φπ φx φπ1 φx1 = 0 := by
  rw [generic182_iff_poly hσ hκ hβ hg] at h
  push Not at h
  exact h.1

/-- Cochrane (2023), eq. (18.2), p. 427: the hypersurface is proper — at `φ_π = 1` and all other
responses zero, `res182 = βκ² ≠ 0` and the system is generic. -/
theorem res182_ne_zero_somewhere {σ β κ φi : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    res182 σ β κ 1 0 0 0 ≠ 0 ∧ Generic (A182 σ β κ φi 1 0 0 0) := by
  have hR : res182 σ β κ 1 0 0 0 = β * κ ^ 2 := by unfold res182 gA gB; ring
  have hne : res182 σ β κ 1 0 0 0 ≠ 0 := by rw [hR]; positivity
  exact ⟨hne, (generic182_iff_poly hσ hκ hβ (by simp)).mpr (Or.inl hne)⟩

/-- Cochrane (2023), eq. (18.2), p. 427: the failure set is nonempty — a rule with no feedback,
`i_t = φ_i i_{t−1} + u_t`, is never generic (compare
`TidyR5Inertia.not_determinate182_no_response`). -/
theorem nongeneric_no_response {σ β κ φi : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    ¬ Generic (A182 σ β κ φi 0 0 0 0) := by
  rw [generic182_iff_poly hσ hκ hβ (by simp)]
  unfold res182 gA gB
  simp

/-- Cochrane (2023), eq. (18.2), p. 427: genericity also fails for rules that do respond: at
`β = 1/2`, `σ = 1`, `κ = 3/4` (so `μ* = 1/2`), `φ_π = −4/3`, `φ_{π,1} = 8/3`. -/
theorem nongeneric_with_response (φi : ℝ) :
    ¬ Generic (A182 1 (1 / 2) (3 / 4) φi (-4 / 3) 0 (8 / 3) 0) := by
  rw [generic182_iff_poly one_pos (by norm_num) (by norm_num) (by norm_num)]
  unfold res182 gA gB
  norm_num

/-- Cochrane (2023), eq. (18.2), p. 427 (**the resultant alone is not the condition**): at
`β = 1/2`, `σ = 1`, `κ = 3/4`, `φ_π = −16/3`, `φ_{π,1} = 4/3`, `res182 = 0` (the common
root of `q` and `A + Bμ` is the unstable `1/λ₂ = 4`), yet the response condition holds and the
system is generic. -/
theorem res182_zero_but_generic (φi : ℝ) :
    res182 1 (1 / 2) (3 / 4) (-16 / 3) 0 (4 / 3) 0 = 0 ∧
      Generic (A182 1 (1 / 2) (3 / 4) φi (-16 / 3) 0 (4 / 3) 0) := by
  have hR : res182 1 (1 / 2) (3 / 4) (-16 / 3) 0 (4 / 3) 0 = 0 := by
    unfold res182 gA gB; norm_num
  refine ⟨hR, (generic182_iff_poly one_pos (by norm_num) (by norm_num) (by norm_num)).mpr
    (Or.inr ?_)⟩
  unfold gA gB
  norm_num

/-! ### Measure zero -/

/-- Cochrane (2023), eq. (18.2), p. 427: `res182` is a quadratic in `φ_π` with leading coefficient
`βκ²`. -/
noncomputable def resPoly (σ β κ φx φπ1 φx1 : ℝ) : ℝ[X] :=
  C (β * κ ^ 2) * X ^ 2 +
    C (2 * β * κ * (φx + φx1) + (1 + β + σ * κ) * κ * gB σ β κ φx φπ1 φx1) * X +
    C (β * (φx + φx1) ^ 2 + (1 + β + σ * κ) * (φx + φx1) * gB σ β κ φx φπ1 φx1 +
      gB σ β κ φx φπ1 φx1 ^ 2)

/-- Cochrane (2023), eq. (18.2): evaluating the quadratic gives `res182`. -/
theorem resPoly_eval (σ β κ φπ φx φπ1 φx1 : ℝ) :
    (resPoly σ β κ φx φπ1 φx1).eval φπ = res182 σ β κ φπ φx φπ1 φx1 := by
  simp only [resPoly, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  unfold res182 gA
  ring

/-- Cochrane (2023), eq. (18.2): for `β, κ > 0` the quadratic in `φ_π` is nonzero. -/
theorem resPoly_ne_zero {σ β κ φx φπ1 φx1 : ℝ} (hβ : 0 < β) (hκ : 0 < κ) :
    resPoly σ β κ φx φπ1 φx1 ≠ 0 := by
  intro h
  have h2 := congrArg (fun p => Polynomial.coeff p 2) h
  simp only [resPoly, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X, coeff_zero] at h2
  norm_num at h2
  rcases h2 with h | h
  · exact hβ.ne' h
  · exact hκ.ne' h

/-- Cochrane (2023), eq. (18.2), p. 427: for `β, κ > 0` and any values of the other parameters,
`res182 = 0` holds for finitely many `φ_π` (at most two). -/
theorem res182_slice_finite {σ β κ φx φπ1 φx1 : ℝ} (hβ : 0 < β) (hκ : 0 < κ) :
    Set.Finite {φπ : ℝ | res182 σ β κ φπ φx φπ1 φx1 = 0} := by
  have h := Polynomial.finite_setOfPred_isRoot (resPoly_ne_zero (σ := σ) (φx := φx) (φπ1 := φπ1)
    (φx1 := φx1) hβ hκ)
  refine h.subset fun φπ hφ => ?_
  simp only [Set.mem_ofPred_eq, IsRoot.def, resPoly_eval] at hφ ⊢
  exact hφ

/-- Cochrane (2023), eq. (18.2), p. 427: the set of parameter points
`((σ, β, κ, φ_i, φ_x, φ_{π,1}, φ_{x,1}), φ_π)` with `σ, κ, β > 0`, `1 − σφ_{x,1} ≠ 0` at which the
genericity condition fails. -/
def nonGeneric : Set ((ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) × ℝ) :=
  {q | 0 < q.1.1 ∧ 0 < q.1.2.2.1 ∧ 0 < q.1.2.1 ∧ 1 - q.1.1 * q.1.2.2.2.2.2.2 ≠ 0 ∧
    ¬ Generic (A182 q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2.1 q.2 q.1.2.2.2.2.1 q.1.2.2.2.2.2.1
      q.1.2.2.2.2.2.2)}

/-- **The failure set has Lebesgue measure zero** (Cochrane (2023), eq. (18.2), p. 427): in
`ℝ⁸ = ℝ⁷ × ℝ` with the product Lebesgue measure, the parameters at which the genericity condition
of (18.2) fails form a null set. -/
theorem volume_nonGeneric : volume nonGeneric = 0 := by
  set Z : Set ((ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) × ℝ) :=
    {q | 0 < q.1.2.1 ∧ 0 < q.1.2.2.1 ∧
      res182 q.1.1 q.1.2.1 q.1.2.2.1 q.2 q.1.2.2.2.2.1 q.1.2.2.2.2.2.1 q.1.2.2.2.2.2.2 = 0}
    with hZ
  have hsub : nonGeneric ⊆ Z := by
    rintro q ⟨hσ, hκ, hβ, hg, hn⟩
    exact ⟨hβ, hκ, nongeneric_subset_res hσ hκ hβ hg hn⟩
  have hres : Measurable fun q : (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) × ℝ =>
      res182 q.1.1 q.1.2.1 q.1.2.2.1 q.2 q.1.2.2.2.2.1 q.1.2.2.2.2.2.1 q.1.2.2.2.2.2.2 := by
    unfold res182 gA gB
    fun_prop
  have hZm : MeasurableSet Z := by
    have m1 : Measurable fun q : (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) × ℝ => q.1.2.1 := by fun_prop
    have m2 : Measurable fun q : (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) × ℝ => q.1.2.2.1 := by fun_prop
    exact (measurableSet_lt measurable_const m1).inter
      ((measurableSet_lt measurable_const m2).inter
      (measurableSet_eq_fun hres measurable_const))
  refine measure_mono_null hsub ?_
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hZm]
  refine Filter.Eventually.of_forall fun p => ?_
  by_cases hp : 0 < p.2.1 ∧ 0 < p.2.2.1
  · have hfin := res182_slice_finite (σ := p.1) (φx := p.2.2.2.2.1) (φπ1 := p.2.2.2.2.2.1)
      (φx1 := p.2.2.2.2.2.2) hp.1 hp.2
    refine measure_mono_null (fun φπ hφ => ?_) (hfin.countable.measure_zero volume)
    exact hφ.2.2
  · have he : Prod.mk p ⁻¹' Z = ∅ := by
      ext φπ
      simp only [Set.mem_preimage, hZ, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hp ⟨h.1, h.2.1⟩
    simp [he]

end Cochrane.KeynesianStickyPrices.TidyR6Genericity182
