/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MonetaryPolicyDesign.Expectations
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Exercise 4.6: a price-level based interest rate rule

Galí (2015), Chapter 4, Exercise 4.6, p. 125. The economy is the dynamic IS equation
`ỹ_t = E_t ỹ_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − r^n_t)` and the New Keynesian Phillips curve
`π_t = β E_t π_{t+1} + κ ỹ_t`, with `π_t = p̂_t − p̂_{t−1}`. Policy follows the price-level rule
`i_t = r^n_t + φ_p p̂_t`, `p̂_t = p_t − p*`. The book asks to show that the rule generates a
unique stationary equilibrium if and only if `φ_p > 0`.

The lagged price level `p̂_{t−1}` is predetermined (`p̂_{−1}` is given), so the equilibrium is a
system in `(p̂_{t−1}, p̂_t, ỹ_t)` with one predetermined and two jump variables. A bounded
equilibrium exists and is unique for every initial price level iff exactly one root of the
characteristic polynomial (`charPoly`)

  `P(λ) = σ (λ − 1)² (1 − βλ) − κ λ (1 + φ_p − λ)`

lies inside the unit circle (`λ` is the ratio `p̂_t / p̂_{t−1}` of a perfect-foresight mode).

## The factorisation

For a real root `λ` of `P`, put `w_t = p̂_t − λ p̂_{t−1}` and `v_t = ỹ_t − c(λ) p̂_{t−1}` with
`c(λ) = −(1 − λ)(1 − βλ)/κ` (`loadY`). The predetermined variable drops out and `(w, v)` solves
a *homogeneous* two-dimensional forward system `x_t = A(λ) E_t x_{t+1}` (`reduce_solves`), whose
matrix (`fwdA`) has `det A = βλ` (`det2_fwdA`) and
`σ (1 − λ)(1 − tr A + det A) = κ φ_p λ`, `σ (1 + λ)(1 + tr A + det A) = λ P(−1)` (`key_one`,
`key_neg_one`). The natural rate drops out of the system entirely.

## Main results

* `determinate_of_root`: if `P(λ) = 0`, `|λ| < 1` and `A(λ)` is Schur stable, then for every
  initial price level there is exactly one bounded equilibrium, `p̂_t = λ^{t+1} p̂_{−1}`,
  `ỹ_t = c(λ) λᵗ p̂_{−1}`, `i_t = r^n_t + φ_p p̂_t` (`bounded_eq_explicit`).
* `determinate_of_pos`: **`φ_p > 0` ⇒ determinacy** (a root in `(0, 1)`).
* `not_determinate_of_two_roots`, `not_determinate_of_neg`: for
  `φ* ≤ φ_p ≤ 0`, `φ* = −2 − 4σ(1 + β)/κ` (`phiStar`), there are two bounded equilibria with the
  same initial price level (two roots in the closed unit disc; for `φ* < φ_p < 0` the stable
  roots may be complex and the second equilibrium is built from the backward matrix `bwdB`).
* `determinate_of_lt_phiStar` (**correction**): for `φ_p < φ*` the equilibrium is again
  determinate (an oscillating stable root in `(−1, 0)`).
* `determinate_iff`: determinacy `⟺ φ_p > 0 ∨ φ_p < φ*`; `determinate_iff_pos_of_ge`: the book's
  claim holds for `φ_p ≥ φ*`, in particular for all `φ_p ≥ 0`; `book_claim_false`: the printed
  "if and only if `φ_p > 0`" fails over all real `φ_p`.
-/

namespace Gali.MonetaryPolicyDesign.Ex4_6

open Filter Topology

/-! ### The characteristic polynomial and the reduced matrices -/

/-- Galí (2015), Ex. 4.6, p. 125: the characteristic polynomial
`P(λ) = σ (λ − 1)² (1 − βλ) − κ λ (1 + φ_p − λ)` of the equilibrium dynamics. -/
def charPoly (σ κ β φ r : ℝ) : ℝ := σ * (r - 1) ^ 2 * (1 - β * r) - κ * r * (1 + φ - r)

/-- Galí (2015), Ex. 4.6: the loading `c(λ) = −(1 − λ)(1 − βλ)/κ` of the output gap on the
lagged price level in the `λ`-mode. -/
noncomputable def loadY (κ β r : ℝ) : ℝ := -((1 - r) * (1 - β * r)) / κ

/-- Galí (2015), Ex. 4.6: the coefficient `e(λ) = σ c(λ) − φ_p − 1 + λ` of the reduced IS
equation. -/
noncomputable def eCoef (σ κ β φ r : ℝ) : ℝ := σ * loadY κ β r - φ - 1 + r

/-- Galí (2015), Ex. 4.6: the coefficient `1 + β − βλ` of the reduced Phillips curve. -/
def mCoef (β r : ℝ) : ℝ := 1 + β - β * r

/-- Galí (2015), Ex. 4.6: the forward matrix `A(λ)` of the reduced system
`(w_t, v_t) = A(λ) E_t (w_{t+1}, v_{t+1})`. -/
noncomputable def fwdA (σ κ β φ r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![r / σ * (σ * β + κ), r / σ * (κ * σ);
    r / σ * (eCoef σ κ β φ r * β + mCoef β r), r / σ * (mCoef β r * σ)]

/-- Galí (2015), Ex. 4.6: the backward matrix `B(λ) = A(λ)⁻¹` of the reduced system
(perfect foresight: `(w_{t+1}, v_{t+1}) = B(λ) (w_t, v_t)`). -/
noncomputable def bwdB (σ κ β φ r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![mCoef β r / β, -κ / β;
    -(mCoef β r + β * eCoef σ κ β φ r) / (β * σ), (κ + β * σ) / (β * σ)]

/-- Galí (2015), Ex. 4.6: the lower determinacy threshold `φ* = −2 − 4σ(1 + β)/κ`, at which
`P(−1) = 0`. -/
noncomputable def phiStar (σ κ β : ℝ) : ℝ := -2 - 4 * σ * (1 + β) / κ

/-- Galí (2015), Ex. 4.6: `κ c(λ) = −(1 − λ)(1 − βλ)`. -/
theorem loadY_mul {κ : ℝ} (hκ : κ ≠ 0) (β r : ℝ) :
    κ * loadY κ β r = -((1 - r) * (1 - β * r)) := by
  unfold loadY; field_simp

/-- Galí (2015), Ex. 4.6: `P(0) = σ`. -/
theorem charPoly_zero (σ κ β φ : ℝ) : charPoly σ κ β φ 0 = σ := by
  unfold charPoly; ring

/-- Galí (2015), Ex. 4.6: `P(1) = −κ φ_p`. -/
theorem charPoly_one (σ κ β φ : ℝ) : charPoly σ κ β φ 1 = -(κ * φ) := by
  unfold charPoly; ring

/-- Galí (2015), Ex. 4.6: `P(−1) = 4σ(1 + β) + κ(2 + φ_p)`. -/
theorem charPoly_neg_one (σ κ β φ : ℝ) :
    charPoly σ κ β φ (-1) = 4 * σ * (1 + β) + κ * (2 + φ) := by
  unfold charPoly; ring

/-- Galí (2015), Ex. 4.6: for `κ > 0`, `P(−1) > 0` iff `φ_p > φ*`, and `P(−1) < 0` iff
`φ_p < φ*`. -/
theorem charPoly_neg_one_pos_iff {σ κ β φ : ℝ} (hκ : 0 < κ) :
    0 < charPoly σ κ β φ (-1) ↔ phiStar σ κ β < φ := by
  rw [charPoly_neg_one, phiStar,
    show -2 - 4 * σ * (1 + β) / κ = (-(2 * κ) - 4 * σ * (1 + β)) / κ by field_simp,
    div_lt_iff₀ hκ]
  constructor <;> intro h <;> linarith

/-- Galí (2015), Ex. 4.6: `P(−1) < 0` iff `φ_p < φ*` (for `κ > 0`). -/
theorem charPoly_neg_one_neg_iff {σ κ β φ : ℝ} (hκ : 0 < κ) :
    charPoly σ κ β φ (-1) < 0 ↔ φ < phiStar σ κ β := by
  rw [charPoly_neg_one, phiStar,
    show -2 - 4 * σ * (1 + β) / κ = (-(2 * κ) - 4 * σ * (1 + β)) / κ by field_simp,
    lt_div_iff₀ hκ]
  constructor <;> intro h <;> linarith

/-- Galí (2015), Ex. 4.6: `P` is continuous. -/
theorem continuous_charPoly (σ κ β φ : ℝ) : Continuous (charPoly σ κ β φ) := by
  unfold charPoly; fun_prop

/-- Galí (2015), Ex. 4.6: at a root `λ` of `P`, `σ c(λ)(1 − λ) + λ (1 + φ_p − λ) = 0`, the
coefficient of `p̂_{t−1}` in the reduced IS equation. -/
theorem is_coef_zero {σ κ β φ r : ℝ} (hκ : κ ≠ 0) (hP : charPoly σ κ β φ r = 0) :
    σ * loadY κ β r * (1 - r) + r * (1 + φ - r) = 0 := by
  have h := loadY_mul hκ β r
  apply mul_left_cancel₀ hκ
  unfold charPoly at hP
  linear_combination σ * (1 - r) * h - hP

/-- Galí (2015), Ex. 4.6: at a root `λ` of `P`, `λ (σ (1 + β − βλ) − κ e(λ)) = σ`; the
determinant of the reduced system's left-hand matrix is `σ/λ`. -/
theorem delta_eq {σ κ β φ r : ℝ} (hκ : κ ≠ 0) (hP : charPoly σ κ β φ r = 0) :
    r * (σ * mCoef β r - κ * eCoef σ κ β φ r) = σ := by
  have h := loadY_mul hκ β r
  unfold eCoef mCoef
  unfold charPoly at hP
  linear_combination (-(r * σ)) * h - hP

/-! ### The reduction, pointwise -/

/-- Galí (2015), Ex. 4.6 (pointwise algebra): the Phillips curve
`(1 + β) p̂_t − p̂_{t−1} = β E_t p̂_{t+1} + κ ỹ_t` holds iff
`(1 + β − βλ) w_t − κ v_t = β E_t w_{t+1}`, for any `λ`. -/
theorem pc_iff {κ β r : ℝ} (hκ : κ ≠ 0) (k p y Ep : ℝ) :
    (1 + β) * p - k = β * Ep + κ * y ↔
      mCoef β r * (p - r * k) - κ * (y - loadY κ β r * k) = β * (Ep - r * p) := by
  have h := loadY_mul hκ β r
  unfold mCoef
  constructor <;> intro e
  · linear_combination e + k * h
  · linear_combination e - k * h

/-- Galí (2015), Ex. 4.6 (pointwise algebra): at a root `λ` of `P`, the IS equation
`σ ỹ_t = σ E_t ỹ_{t+1} − ((φ_p + 1) p̂_t − E_t p̂_{t+1})` holds iff
`σ v_t = σ E_t v_{t+1} + e(λ) w_t + E_t w_{t+1}`. -/
theorem is_iff {σ κ β φ r : ℝ} (hκ : κ ≠ 0) (hP : charPoly σ κ β φ r = 0) (k p y Ep Ey : ℝ) :
    σ * y = σ * Ey - ((φ + 1) * p - Ep) ↔
      σ * (y - loadY κ β r * k) =
        σ * (Ey - loadY κ β r * p) + eCoef σ κ β φ r * (p - r * k) + (Ep - r * p) := by
  have h := is_coef_zero hκ hP
  unfold eCoef
  constructor <;> intro e
  · linear_combination e - k * h
  · linear_combination e + k * h

/-- Galí (2015), Ex. 4.6 (pointwise algebra): the reduced Phillips curve and IS equation give
the forward form `(w, v) = A(λ) (E w', E v')`. -/
theorem fwd_of {σ κ β φ r : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hP : charPoly σ κ β φ r = 0)
    {w v Ew Ev : ℝ} (h1 : mCoef β r * w - κ * v = β * Ew)
    (h2 : σ * v = σ * Ev + eCoef σ κ β φ r * w + Ew) :
    w = r / σ * (σ * β + κ) * Ew + r / σ * (κ * σ) * Ev ∧
      v = r / σ * (eCoef σ κ β φ r * β + mCoef β r) * Ew + r / σ * (mCoef β r * σ) * Ev := by
  have hΔ := delta_eq hκ hP
  constructor
  · field_simp
    linear_combination r * (σ * h1 + κ * h2) - w * hΔ
  · field_simp
    linear_combination r * (mCoef β r * h2 + eCoef σ κ β φ r * h1) - v * hΔ

/-- Galí (2015), Ex. 4.6 (pointwise algebra): the backward recursion
`(w', v') = B(λ) (w, v)` gives the reduced Phillips curve and IS equation. -/
theorem bwd_step {σ κ β φ r : ℝ} (hσ : σ ≠ 0) (hβ : β ≠ 0) (x : Fin 2 → ℝ) :
    mCoef β r * x 0 - κ * x 1 = β * (bwdB σ κ β φ r).mulVec x 0 ∧
      σ * x 1 = σ * (bwdB σ κ β φ r).mulVec x 1 + eCoef σ κ β φ r * x 0 +
        (bwdB σ κ β φ r).mulVec x 0 := by
  simp only [bwdB, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-! ### The forward matrix: determinant, trace and Schur stability -/

/-- Galí (2015), Ex. 4.6: at a root `λ` of `P`, `det A(λ) = βλ`. -/
theorem det2_fwdA {σ κ β φ r : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hP : charPoly σ κ β φ r = 0) :
    det2 (fwdA σ κ β φ r) = β * r := by
  have hΔ := delta_eq hκ hP
  have hr : r ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hΔ
    exact hσ hΔ.symm
  have hm : σ * mCoef β r - κ * eCoef σ κ β φ r = σ / r := by
    rw [eq_div_iff hr]; linarith
  calc det2 (fwdA σ κ β φ r)
      = (r / σ) ^ 2 * σ * β * (σ * mCoef β r - κ * eCoef σ κ β φ r) := by
        simp only [det2, fwdA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one]
        ring
    _ = β * r := by rw [hm]; field_simp

/-- Galí (2015), Ex. 4.6: `tr A(λ) = λ (σβ + κ + σ(1 + β − βλ))/σ`. -/
theorem tr2_fwdA (σ κ β φ r : ℝ) :
    tr2 (fwdA σ κ β φ r) = r / σ * (σ * β + κ) + r / σ * (mCoef β r * σ) := by
  simp only [tr2, fwdA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]

/-- Galí (2015), Ex. 4.6: at a root `λ` of `P`, `σ (1 − λ)(1 − tr A + det A) = κ φ_p λ`. -/
theorem key_one {σ κ β φ r : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hP : charPoly σ κ β φ r = 0) :
    σ * (1 - r) * (1 - tr2 (fwdA σ κ β φ r) + det2 (fwdA σ κ β φ r)) = κ * φ * r := by
  rw [det2_fwdA hσ hκ hP, tr2_fwdA]
  unfold mCoef
  unfold charPoly at hP
  field_simp
  linear_combination hP

/-- Galí (2015), Ex. 4.6: at a root `λ` of `P`, `σ (1 + λ)(1 + tr A + det A) = λ P(−1)`. -/
theorem key_neg_one {σ κ β φ r : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hP : charPoly σ κ β φ r = 0) :
    σ * (1 + r) * (1 + tr2 (fwdA σ κ β φ r) + det2 (fwdA σ κ β φ r)) =
      r * charPoly σ κ β φ (-1) := by
  rw [det2_fwdA hσ hκ hP, tr2_fwdA]
  unfold mCoef
  have hP' := hP
  unfold charPoly at hP' ⊢
  field_simp
  linear_combination hP'

/-- Galí (2015), Ex. 4.6: if `λ` is a root of `P` with `|λ| < 1`, `φ_p λ > 0` and
`λ P(−1) > 0`, the forward matrix `A(λ)` is Schur stable (both eigenvalues inside the unit
circle). -/
theorem schur_fwdA {σ κ β φ r : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hP : charPoly σ κ β φ r = 0) (hr : |r| < 1) (h1 : 0 < φ * r)
    (h2 : 0 < r * charPoly σ κ β φ (-1)) :
    SchurStable (tr2 (fwdA σ κ β φ r)) (det2 (fwdA σ κ β φ r)) := by
  have k1 := key_one hσ.ne' hκ.ne' hP
  have k2 := key_neg_one hσ.ne' hκ.ne' hP
  rw [det2_fwdA hσ.ne' hκ.ne' hP] at k1 k2 ⊢
  obtain ⟨hr0, hr1⟩ := abs_lt.1 hr
  have hpos1 : 0 < σ * (1 - r) := mul_pos hσ (by linarith)
  have hpos2 : 0 < σ * (1 + r) := mul_pos hσ (by linarith)
  have e1 : 0 < 1 - tr2 (fwdA σ κ β φ r) + β * r := by
    have : 0 < σ * (1 - r) * (1 - tr2 (fwdA σ κ β φ r) + β * r) := by
      rw [k1]; nlinarith
    exact pos_of_mul_pos_right this hpos1.le
  have e2 : 0 < 1 + tr2 (fwdA σ κ β φ r) + β * r := by
    have : 0 < σ * (1 + r) * (1 + tr2 (fwdA σ κ β φ r) + β * r) := by rw [k2]; exact h2
    exact pos_of_mul_pos_right this hpos2.le
  refine ⟨?_, abs_lt.2 ⟨by linarith, by linarith⟩⟩
  rw [abs_mul, abs_of_pos hβ0]
  nlinarith [abs_nonneg r]

/-! ### The model -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Ex. 4.6: the lagged price level `p̂_{t−1}`, with `p̂_{−1}` given. -/
def lagP (pm1 : Ω → ℝ) (p : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => pm1
  | t + 1 => p t

/-- Galí (2015), Ex. 4.6: inflation `π_t = p̂_t − p̂_{t−1}`. -/
def infl (pm1 : Ω → ℝ) (p : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := p t - lagP pm1 p t

/-- Galí (2015), Ex. 4.6, p. 125: an equilibrium given the initial price level `p̂_{−1}`: the IS
equation, the Phillips curve and the price-level rule `i_t = r^n_t + φ_p p̂_t`. -/
def IsEquilibrium (β σ κ φ : ℝ) (rn : ℕ → Ω → ℝ) (pm1 : Ω → ℝ) (y p i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, y t = 𝔼.E t (y (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl pm1 p (t + 1)) - rn t) ∧
    infl pm1 p t = β • 𝔼.E t (infl pm1 p (t + 1)) + κ • y t ∧
    i t = rn t + φ • p t

/-- Galí (2015), Ex. 4.6: a stationary (bounded, adapted) equilibrium. -/
def BoundedEq (β σ κ φ : ℝ) (rn : ℕ → Ω → ℝ) (pm1 : Ω → ℝ) (y p i : ℕ → Ω → ℝ) : Prop :=
  IsEquilibrium 𝔼 β σ κ φ rn pm1 y p i ∧ 𝔼.Adapted y ∧ 𝔼.Adapted p ∧ BoundedProc y ∧
    BoundedProc p

/-- Galí (2015), Ex. 4.6: the rule generates a unique stationary equilibrium: for every natural
rate and every bounded initial price level known at date 0, a bounded equilibrium exists and any
two coincide. -/
def Determinate (β σ κ φ : ℝ) : Prop :=
  ∀ (rn : ℕ → Ω → ℝ) (pm1 : Ω → ℝ), 𝔼.E 0 pm1 = pm1 → (∃ M, ∀ ω, |pm1 ω| ≤ M) →
    (∃ y p i, BoundedEq 𝔼 β σ κ φ rn pm1 y p i) ∧
    ∀ y p i y' p' i', BoundedEq 𝔼 β σ κ φ rn pm1 y p i → BoundedEq 𝔼 β σ κ φ rn pm1 y' p' i' →
      y = y' ∧ p = p' ∧ i = i'

/-- Galí (2015), Ex. 4.6: the initial price level is known at every date. -/
theorem known_pm1 {pm1 : Ω → ℝ} (h : 𝔼.E 0 pm1 = pm1) (t : ℕ) : 𝔼.E t pm1 = pm1 := by
  have := 𝔼.known (Nat.zero_le t) pm1
  rwa [h] at this

/-- Galí (2015), Ex. 4.6: the lagged price level is adapted. -/
theorem lagP_adapted {pm1 : Ω → ℝ} {p : ℕ → Ω → ℝ} (h : 𝔼.E 0 pm1 = pm1) (hp : 𝔼.Adapted p) :
    𝔼.Adapted (lagP pm1 p) := by
  intro t
  cases t with
  | zero => exact h
  | succ t =>
    change 𝔼.E (t + 1) (p t) = p t
    have := 𝔼.known (Nat.le_succ t) (p t)
    rwa [hp t] at this

/-- Galí (2015), Ex. 4.6: for an adapted price level, the equilibrium conditions hold iff,
pointwise, `σ ỹ_t = σ E_t ỹ_{t+1} − ((φ_p + 1) p̂_t − E_t p̂_{t+1})`,
`(1 + β) p̂_t − p̂_{t−1} = β E_t p̂_{t+1} + κ ỹ_t` and the rule holds. -/
theorem eq_iff_pointwise {β σ κ φ : ℝ} (hσ : σ ≠ 0) {rn : ℕ → Ω → ℝ} {pm1 : Ω → ℝ}
    {y p i : ℕ → Ω → ℝ} (hp : 𝔼.Adapted p) :
    IsEquilibrium 𝔼 β σ κ φ rn pm1 y p i ↔ ∀ t ω,
      σ * y t ω = σ * 𝔼.E t (y (t + 1)) ω - ((φ + 1) * p t ω - 𝔼.E t (p (t + 1)) ω) ∧
      (1 + β) * p t ω - lagP pm1 p t ω = β * 𝔼.E t (p (t + 1)) ω + κ * y t ω ∧
      i t ω = rn t ω + φ * p t ω := by
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  have hE : ∀ t, 𝔼.E t (infl pm1 p (t + 1)) = 𝔼.E t (p (t + 1)) - p t := fun t => by
    change 𝔼.E t (p (t + 1) - p t) = _
    rw [map_sub, hp t]
  constructor
  · intro h t ω
    obtain ⟨h1, h2, h3⟩ := h t
    rw [hE] at h1 h2
    have e1 := congrFun h1 ω
    have e2 := congrFun h2 ω
    have e3 := congrFun h3 ω
    simp only [infl, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3
    refine ⟨?_, by linarith, e3⟩
    linear_combination σ * e1 - e3 -
      (i t ω - (𝔼.E t (p (t + 1)) ω - p t ω) - rn t ω) * hinv
  · intro h t
    refine ⟨funext fun ω => ?_, funext fun ω => ?_, funext fun ω => (h t ω).2.2⟩
    · obtain ⟨e1, -, e3⟩ := h t ω
      rw [hE]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination σ⁻¹ * e1 - (y t ω - 𝔼.E t (y (t + 1)) ω) * hinv + σ⁻¹ * e3
    · obtain ⟨-, e2, -⟩ := h t ω
      rw [hE]
      simp only [infl, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linarith

/-- Galí (2015), Ex. 4.6: the transformed variable `w_t = p̂_t − λ p̂_{t−1}`. -/
def wseq (r : ℝ) (pm1 : Ω → ℝ) (p : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := p t - r • lagP pm1 p t

/-- Galí (2015), Ex. 4.6: the transformed variable `v_t = ỹ_t − c(λ) p̂_{t−1}`. -/
noncomputable def vseq (κ β r : ℝ) (pm1 : Ω → ℝ) (p y : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  y t - loadY κ β r • lagP pm1 p t

/-- Galí (2015), Ex. 4.6: the stacked vector `(w_t, v_t)`. -/
def stack (a b : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![a t, b t]

/-- **The factorisation** (Galí 2015, Ex. 4.6): at a root `λ` of `P`, in every equilibrium with
an adapted price level, `(w, v)` solves the homogeneous forward system
`(w_t, v_t) = A(λ) E_t (w_{t+1}, v_{t+1})`; the predetermined price level and the natural rate
drop out. -/
theorem reduce_solves {β σ κ φ r : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hP : charPoly σ κ β φ r = 0)
    {rn : ℕ → Ω → ℝ} {pm1 : Ω → ℝ} {y p i : ℕ → Ω → ℝ}
    (he : IsEquilibrium 𝔼 β σ κ φ rn pm1 y p i) (hp : 𝔼.Adapted p) :
    𝔼.Solves (fwdA σ κ β φ r) 0 (stack (wseq r pm1 p) (vseq κ β r pm1 p y)) := by
  have hpt := (eq_iff_pointwise 𝔼 hσ hp).1 he
  intro t j
  funext ω
  obtain ⟨e1, e2, -⟩ := hpt t ω
  have h1 := (pc_iff (r := r) hκ _ _ _ _).1 e2
  have h2 := (is_iff (k := lagP pm1 p t ω) hκ hP _ _ _ _).1 e1
  have hfw := fwd_of hσ hκ hP h1 h2
  have hEw : 𝔼.E t (wseq r pm1 p (t + 1)) ω = 𝔼.E t (p (t + 1)) ω - r * p t ω := by
    change 𝔼.E t (p (t + 1) - r • p t) ω = _
    rw [map_sub, map_smul, hp t]; rfl
  have hEv : 𝔼.E t (vseq κ β r pm1 p y (t + 1)) ω =
      𝔼.E t (y (t + 1)) ω - loadY κ β r * p t ω := by
    change 𝔼.E t (y (t + 1) - loadY κ β r • p t) ω = _
    rw [map_sub, map_smul, hp t]; rfl
  fin_cases j
  · simp only [stack, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [hEw, hEv]
    simp only [fwdA, wseq, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact hfw.1
  · simp only [stack, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Pi.zero_apply, add_zero]
    rw [hEw, hEv]
    simp only [fwdA, vseq, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact hfw.2

/-! ### Determinacy -/

/-- Galí (2015), Ex. 4.6: at a root `λ` of `P`, the `λ`-mode `p̂_t = λ^{t+1} p̂_{−1}`,
`ỹ_t = c(λ) λᵗ p̂_{−1}`, `i_t = r^n_t + φ_p p̂_t` is an equilibrium for every initial price level
known at date 0. -/
theorem mode_isEquilibrium {β σ κ φ r : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0)
    (hP : charPoly σ κ β φ r = 0) (rn : ℕ → Ω → ℝ) {pm1 : Ω → ℝ} (hpm : 𝔼.E 0 pm1 = pm1) :
    IsEquilibrium 𝔼 β σ κ φ rn pm1 (fun t => (loadY κ β r * r ^ t) • pm1)
      (fun t => r ^ (t + 1) • pm1) (fun t => rn t + φ • (r ^ (t + 1) • pm1)) := by
  have hpa : 𝔼.Adapted (fun t => r ^ (t + 1) • pm1) := fun t => by
    simp only [map_smul, known_pm1 𝔼 hpm t]
  have hlag : ∀ t, lagP pm1 (fun t => r ^ (t + 1) • pm1) t = r ^ t • pm1 := fun t => by
    cases t with
    | zero => simp [lagP]
    | succ t => rfl
  refine (eq_iff_pointwise 𝔼 hσ hpa).2 fun t ω => ?_
  simp only [map_smul, known_pm1 𝔼 hpm t, hlag t, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  refine ⟨(is_iff (k := r ^ t * pm1 ω) hκ hP _ _ _ _).2 (by ring),
    (pc_iff (r := r) hκ _ _ _ _).2 (by ring), trivial⟩

/-- Galí (2015), Ex. 4.6: if `P(λ) = 0` and `A(λ)` is Schur stable, every stationary equilibrium
is the `λ`-mode: `p̂_t = λ^{t+1} p̂_{−1}` and `ỹ_t = c(λ) λᵗ p̂_{−1}`. -/
theorem bounded_eq_explicit {β σ κ φ r : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0)
    (hP : charPoly σ κ β φ r = 0) (hA : SchurStable (tr2 (fwdA σ κ β φ r)) (det2 (fwdA σ κ β φ r)))
    {rn : ℕ → Ω → ℝ} {pm1 : Ω → ℝ} (hpm : 𝔼.E 0 pm1 = pm1) (hpmb : ∃ M, ∀ ω, |pm1 ω| ≤ M)
    {y p i : ℕ → Ω → ℝ} (he : BoundedEq 𝔼 β σ κ φ rn pm1 y p i) :
    p = (fun t => r ^ (t + 1) • pm1) ∧ y = (fun t => (loadY κ β r * r ^ t) • pm1) := by
  obtain ⟨he, hya, hpa, ⟨My, hMy⟩, ⟨Mp, hMp⟩⟩ := he
  obtain ⟨M0, hM0⟩ := hpmb
  have hs := reduce_solves 𝔼 hσ hκ hP he hpa
  have hlb : ∀ t ω, |lagP pm1 p t ω| ≤ M0 + Mp := by
    intro t ω
    cases t with
    | zero =>
      change |pm1 ω| ≤ _
      have := abs_nonneg (p 0 ω); linarith [hM0 ω, hMp 0 ω]
    | succ t =>
      change |p t ω| ≤ _
      have := abs_nonneg (pm1 ω); linarith [hM0 ω, hMp t ω]
  have hla := lagP_adapted 𝔼 hpm hpa
  have hav : 𝔼.AdaptedVec (stack (wseq r pm1 p) (vseq κ β r pm1 p y)) := by
    intro t j
    fin_cases j
    · change 𝔼.E t (p t - r • lagP pm1 p t) = p t - r • lagP pm1 p t
      rw [map_sub, map_smul, hpa t, hla t]
    · change 𝔼.E t (y t - loadY κ β r • lagP pm1 p t) = y t - loadY κ β r • lagP pm1 p t
      rw [map_sub, map_smul, hya t, hla t]
  have hbv : BoundedVec (stack (wseq r pm1 p) (vseq κ β r pm1 p y)) := by
    refine ⟨Mp + |r| * (M0 + Mp) + My + |loadY κ β r| * (M0 + Mp), fun t j ω => ?_⟩
    have h1 := abs_nonneg (p t ω)
    have h2 := abs_nonneg (y t ω)
    have h3 : |r * lagP pm1 p t ω| ≤ |r| * (M0 + Mp) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hlb t ω) (abs_nonneg r)
    have h4 : |loadY κ β r * lagP pm1 p t ω| ≤ |loadY κ β r| * (M0 + Mp) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hlb t ω) (abs_nonneg _)
    have h5 := abs_nonneg (r * lagP pm1 p t ω)
    have h6 := abs_nonneg (loadY κ β r * lagP pm1 p t ω)
    fin_cases j
    · change |p t ω - r * lagP pm1 p t ω| ≤ _
      linarith [abs_sub (p t ω) (r * lagP pm1 p t ω), hMp t ω, hMy t ω]
    · change |y t ω - loadY κ β r * lagP pm1 p t ω| ≤ _
      linarith [abs_sub (y t ω) (loadY κ β r * lagP pm1 p t ω), hMp t ω, hMy t ω]
  have h0 : 𝔼.Solves (fwdA σ κ β φ r) 0 0 := fun t j => by simp
  have heq := 𝔼.system_unique hA hs h0 hav (fun t j => map_zero _) hbv
    ⟨0, fun t j ω => by simp⟩
  have hw : ∀ t, p t = r • lagP pm1 p t := fun t => by
    have := congrFun (congrFun heq t) 0
    simp only [stack, Matrix.cons_val_zero, wseq] at this
    exact sub_eq_zero.1 this
  have hv : ∀ t, y t = loadY κ β r • lagP pm1 p t := fun t => by
    have := congrFun (congrFun heq t) 1
    simp only [stack, Matrix.cons_val_one, Matrix.cons_val_fin_one, vseq] at this
    exact sub_eq_zero.1 this
  have hpexp : ∀ t, p t = r ^ (t + 1) • pm1 := by
    intro t
    induction t with
    | zero => rw [hw 0]; simp [lagP]
    | succ t ih =>
      rw [hw (t + 1)]
      change r • p t = _
      rw [ih, smul_smul]
      congr 1
      ring
  refine ⟨funext hpexp, funext fun t => ?_⟩
  rw [hv t]
  cases t with
  | zero => simp [lagP]
  | succ t =>
    change loadY κ β r • p t = _
    rw [hpexp t, smul_smul]

/-- Galí (2015), Ex. 4.6: if `P(λ) = 0`, `|λ| < 1` and `A(λ)` is Schur stable, the rule
generates a unique stationary equilibrium for every initial price level. -/
theorem determinate_of_root {β σ κ φ r : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0)
    (hP : charPoly σ κ β φ r = 0) (hr : |r| < 1)
    (hA : SchurStable (tr2 (fwdA σ κ β φ r)) (det2 (fwdA σ κ β φ r))) :
    Determinate 𝔼 β σ κ φ := by
  intro rn pm1 hpm hpmb
  refine ⟨⟨_, _, _, mode_isEquilibrium 𝔼 hσ hκ hP rn hpm, fun t => ?_, fun t => ?_, ?_, ?_⟩, ?_⟩
  · simp only [map_smul, known_pm1 𝔼 hpm t]
  · simp only [map_smul, known_pm1 𝔼 hpm t]
  · obtain ⟨M, hM⟩ := hpmb
    refine ⟨|loadY κ β r| * M, fun t ω => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
    have h1 : |r| ^ t ≤ 1 := pow_le_one₀ (abs_nonneg r) hr.le
    have h2 := abs_nonneg (pm1 ω)
    have h3 := mul_le_mul_of_nonneg_left (hM ω) (abs_nonneg (loadY κ β r))
    calc |loadY κ β r| * |r| ^ t * |pm1 ω| ≤ |loadY κ β r| * 1 * |pm1 ω| := by gcongr
      _ ≤ |loadY κ β r| * M := by rw [mul_one]; exact h3
  · obtain ⟨M, hM⟩ := hpmb
    refine ⟨M, fun t ω => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
    have h1 : |r| ^ (t + 1) ≤ 1 := pow_le_one₀ (abs_nonneg r) hr.le
    have h2 := abs_nonneg (pm1 ω)
    nlinarith [hM ω]
  · intro y p i y' p' i' he he'
    obtain ⟨hp1, hy1⟩ := bounded_eq_explicit 𝔼 hσ hκ hP hA hpm hpmb he
    obtain ⟨hp2, hy2⟩ := bounded_eq_explicit 𝔼 hσ hκ hP hA hpm hpmb he'
    refine ⟨hy1.trans hy2.symm, hp1.trans hp2.symm, funext fun t => ?_⟩
    rw [(he.1 t).2.2, (he'.1 t).2.2, hp1, hp2]

/-! ### Roots of the characteristic polynomial -/

/-- Galí (2015), Ex. 4.6: for `φ_p > 0` the polynomial has a root in `(0, 1)` (`P(0) = σ > 0`,
`P(1) = −κφ_p < 0`). -/
theorem exists_root_pos {σ κ β φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hφ : 0 < φ) :
    ∃ r, 0 < r ∧ r < 1 ∧ charPoly σ κ β φ r = 0 := by
  have h := intermediate_value_Ioo' (zero_le_one' ℝ)
    (continuous_charPoly σ κ β φ).continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (charPoly σ κ β φ 1) (charPoly σ κ β φ 0) by
      rw [charPoly_one, charPoly_zero]; exact ⟨by nlinarith, hσ⟩)
  obtain ⟨r, ⟨h0, h1⟩, hr⟩ := h
  exact ⟨r, h0, h1, hr⟩

/-- Galí (2015), Ex. 4.6: for `φ_p < φ*` the polynomial has a root in `(−1, 0)`
(`P(−1) < 0 < σ = P(0)`). -/
theorem exists_root_neg {σ κ β φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hφ : φ < phiStar σ κ β) :
    ∃ r, -1 < r ∧ r < 0 ∧ charPoly σ κ β φ r = 0 := by
  have h := intermediate_value_Ioo (show (-1 : ℝ) ≤ 0 by norm_num)
    (continuous_charPoly σ κ β φ).continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (charPoly σ κ β φ (-1)) (charPoly σ κ β φ 0) by
      rw [charPoly_zero]; exact ⟨(charPoly_neg_one_neg_iff hκ).2 hφ, hσ⟩)
  obtain ⟨r, ⟨h0, h1⟩, hr⟩ := h
  exact ⟨r, h0, h1, hr⟩

/-- Galí (2015), Ex. 4.6: for `φ_p < 1/β − 1` (in particular `φ_p ≤ 0`) the polynomial has a
root `λ > 1/β` (`P(1/β) > 0` and `P(λ) → −∞`). -/
theorem exists_root_large {σ κ β φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφ : φ ≤ 0) : ∃ r, 1 / β < r ∧ charPoly σ κ β φ r = 0 := by
  set a := σ + 2 * σ * β + κ with ha
  set b := 2 * σ + σ * β + κ * (1 + φ) with hb
  set K := a + |b| + σ with hK
  have hKpos : 0 < K := by have := abs_nonneg b; rw [hK, ha]; positivity
  set X := K / (σ * β) + 1 / β + 1 with hX
  have hσβ : 0 < σ * β := mul_pos hσ hβ0
  have hX1 : 1 / β < X := by rw [hX]; have := div_pos hKpos hσβ; linarith
  have hb1 : 1 < 1 / β := by rw [lt_div_iff₀ hβ0]; linarith
  have hXge : 1 ≤ X := by linarith
  have hXeq : σ * β * X = K + σ + σ * β := by rw [hX]; field_simp
  have hexp : charPoly σ κ β φ X = -(σ * β * X) * X ^ 2 + a * X ^ 2 - b * X + σ := by
    rw [ha, hb]; unfold charPoly; ring
  have hPX : charPoly σ κ β φ X < 0 := by
    rw [hexp, hXeq]
    have h1 : -b * X ≤ |b| * X ^ 2 := by
      have := neg_abs_le b
      have hX2 : X ≤ X ^ 2 := by nlinarith
      nlinarith [abs_nonneg b]
    have h2 : σ ≤ σ * X ^ 2 := by nlinarith
    have h3 : 0 < X ^ 2 := by positivity
    nlinarith
  have hP1 : 0 < charPoly σ κ β φ (1 / β) := by
    unfold charPoly
    have : 1 - β * (1 / β) = 0 := by field_simp; ring
    rw [this, mul_zero, zero_sub, neg_pos]
    have h1 : 1 + φ - 1 / β < 0 := by linarith
    have h2 : 0 < κ * (1 / β) := by positivity
    nlinarith
  have h := intermediate_value_Ioo' hX1.le (continuous_charPoly σ κ β φ).continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (charPoly σ κ β φ X) (charPoly σ κ β φ (1 / β)) from ⟨hPX, hP1⟩)
  obtain ⟨r, ⟨h0, -⟩, hr⟩ := h
  exact ⟨r, h0, hr⟩

/-! ### The determinacy region -/

/-- **Ex. 4.6, sufficiency** (Galí 2015, p. 125): for `φ_p > 0` the price-level rule generates a
unique stationary equilibrium for every initial price level. -/
theorem determinate_of_pos {β σ κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφ : 0 < φ) : Determinate 𝔼 β σ κ φ := by
  obtain ⟨r, hr0, hr1, hP⟩ := exists_root_pos (β := β) hσ hκ hφ
  have hP1 : 0 < charPoly σ κ β φ (-1) := by rw [charPoly_neg_one]; positivity
  exact determinate_of_root 𝔼 hσ.ne' hκ.ne' hP (abs_lt.2 ⟨by linarith, hr1⟩)
    (schur_fwdA hσ hκ hβ0 hβ1 hP (abs_lt.2 ⟨by linarith, hr1⟩) (mul_pos hφ hr0)
      (mul_pos hr0 hP1))

/-- **Ex. 4.6, correction** (Galí 2015, p. 125): for `φ_p < φ* = −2 − 4σ(1 + β)/κ` the rule
*also* generates a unique stationary equilibrium (the stable root lies in `(−1, 0)`). -/
theorem determinate_of_lt_phiStar {β σ κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφ : φ < phiStar σ κ β) : Determinate 𝔼 β σ κ φ := by
  obtain ⟨r, hr0, hr1, hP⟩ := exists_root_neg (β := β) hσ hκ hφ
  have hP1 := (charPoly_neg_one_neg_iff hκ).2 hφ
  have hφneg : φ < 0 := by
    have : phiStar σ κ β < 0 := by
      unfold phiStar
      have : 0 < 4 * σ * (1 + β) / κ := by positivity
      linarith
    linarith
  exact determinate_of_root 𝔼 hσ.ne' hκ.ne' hP (abs_lt.2 ⟨hr0, by linarith⟩)
    (schur_fwdA hσ hκ hβ0 hβ1 hP (abs_lt.2 ⟨hr0, by linarith⟩) (mul_pos_of_neg_of_neg hφneg hr1)
      (mul_pos_of_neg_of_neg hr1 hP1))

/-- Galí (2015), Ex. 4.6: the zero outcome (`ỹ = p̂ = 0`, `i = r^n`) is a stationary equilibrium
when `p̂_{−1} = 0`. -/
theorem zero_boundedEq {β σ κ φ : ℝ} (hσ : σ ≠ 0) (rn : ℕ → Ω → ℝ) :
    BoundedEq 𝔼 β σ κ φ rn (fun _ => 0) (fun _ => 0) (fun _ => 0) rn := by
  have hpa : 𝔼.Adapted (fun _ => (0 : Ω → ℝ)) := fun t => map_zero _
  refine ⟨(eq_iff_pointwise 𝔼 hσ hpa).2 fun t ω => ?_, hpa, hpa, ⟨0, fun t ω => by simp⟩,
    ⟨0, fun t ω => by simp⟩⟩
  cases t <;> simp [lagP]

/-- Galí (2015), Ex. 4.6 (**multiplicity**): if `P` has two distinct real roots `λ, μ` in the
closed unit disc, the rule does not generate a unique stationary equilibrium: with
`p̂_{−1} = 0`, both `0` and the deterministic path `p̂_t = λ^{t+1} − μ^{t+1}` are stationary
equilibria. -/
theorem not_determinate_of_two_roots [Nonempty Ω] {β σ κ φ r s : ℝ} (hσ : σ ≠ 0)
    (hκ : κ ≠ 0) (hPr : charPoly σ κ β φ r = 0) (hPs : charPoly σ κ β φ s = 0) (hrs : r ≠ s)
    (hr : |r| ≤ 1) (hs : |s| ≤ 1) : ¬ Determinate 𝔼 β σ κ φ := by
  intro hD
  obtain ⟨-, huniq⟩ := hD (fun _ => 0) (fun _ => 0) (map_zero _) ⟨0, fun _ => by simp⟩
  set p : ℕ → Ω → ℝ := fun t _ => r ^ (t + 1) - s ^ (t + 1) with hp
  set y : ℕ → Ω → ℝ := fun t _ => loadY κ β r * r ^ t - loadY κ β s * s ^ t with hy
  have hpa : 𝔼.Adapted p := fun t => 𝔼.const t _
  have hya : 𝔼.Adapted y := fun t => 𝔼.const t _
  have hlag : ∀ t ω, lagP (fun _ => 0) p t ω = r ^ t - s ^ t := by
    intro t ω
    cases t with
    | zero => simp [lagP]
    | succ t => rfl
  have he : IsEquilibrium 𝔼 β σ κ φ (fun _ => 0) (fun _ => 0) y p
      (fun t => (fun _ => 0) + φ • p t) := by
    refine (eq_iff_pointwise 𝔼 hσ hpa).2 fun t ω => ?_
    rw [hlag t ω, hp, hy, 𝔼.const, 𝔼.const]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_add]
    have i1 := (is_iff (k := r ^ t) hκ hPr (r ^ (t + 1)) (loadY κ β r * r ^ t) (r ^ (t + 2))
      (loadY κ β r * r ^ (t + 1))).2 (by ring)
    have i2 := (is_iff (k := s ^ t) hκ hPs (s ^ (t + 1)) (loadY κ β s * s ^ t) (s ^ (t + 2))
      (loadY κ β s * s ^ (t + 1))).2 (by ring)
    have p1 := (pc_iff (r := r) (β := β) hκ (r ^ t) (r ^ (t + 1)) (loadY κ β r * r ^ t)
      (r ^ (t + 2))).2 (by ring)
    have p2 := (pc_iff (r := s) (β := β) hκ (s ^ t) (s ^ (t + 1)) (loadY κ β s * s ^ t)
      (s ^ (t + 2))).2 (by ring)
    refine ⟨by linear_combination i1 - i2, by linear_combination p1 - p2, by simp⟩
  have hb : BoundedEq 𝔼 β σ κ φ (fun _ => 0) (fun _ => 0) y p
      (fun t => (fun _ => 0) + φ • p t) := by
    refine ⟨he, hya, hpa, ⟨|loadY κ β r| + |loadY κ β s|, fun t ω => ?_⟩,
      ⟨2, fun t ω => ?_⟩⟩
    · have h1 : |r| ^ t ≤ 1 := pow_le_one₀ (abs_nonneg r) hr
      have h2 : |s| ^ t ≤ 1 := pow_le_one₀ (abs_nonneg s) hs
      calc |loadY κ β r * r ^ t - loadY κ β s * s ^ t|
          ≤ |loadY κ β r * r ^ t| + |loadY κ β s * s ^ t| := abs_sub _ _
        _ = |loadY κ β r| * |r| ^ t + |loadY κ β s| * |s| ^ t := by rw [abs_mul, abs_mul,
            abs_pow, abs_pow]
        _ ≤ |loadY κ β r| * 1 + |loadY κ β s| * 1 := by gcongr
        _ = _ := by ring
    · have h1 : |r| ^ (t + 1) ≤ 1 := pow_le_one₀ (abs_nonneg r) hr
      have h2 : |s| ^ (t + 1) ≤ 1 := pow_le_one₀ (abs_nonneg s) hs
      calc |r ^ (t + 1) - s ^ (t + 1)| ≤ |r ^ (t + 1)| + |s ^ (t + 1)| := abs_sub _ _
        _ ≤ 2 := by rw [abs_pow, abs_pow]; linarith
  obtain ⟨-, hp0, -⟩ := huniq _ _ _ _ _ _ hb (zero_boundedEq 𝔼 hσ _)
  have := congrFun (congrFun hp0 0) (Classical.arbitrary Ω)
  simp only [hp, zero_add, pow_one] at this
  exact hrs (sub_eq_zero.1 this)

/-- Galí (2015), Ex. 4.6: for `φ_p = 0` the rule does not pin down a unique stationary
equilibrium (roots `1` and a root in `(0, 1)`). -/
theorem not_determinate_zero [Nonempty Ω] {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    ¬ Determinate 𝔼 β σ κ 0 := by
  set g : ℝ → ℝ := fun x => σ * (x - 1) * (1 - β * x) + κ * x with hg
  have hgc : Continuous g := by rw [hg]; fun_prop
  obtain ⟨r, ⟨hr0, hr1⟩, hgr⟩ := intermediate_value_Ioo (zero_le_one' ℝ) hgc.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (g 0) (g 1) by simp only [hg]; constructor <;> nlinarith)
  have hPr : charPoly σ κ β 0 r = 0 := by
    have : charPoly σ κ β 0 r = (r - 1) * g r := by simp only [hg]; unfold charPoly; ring
    rw [this, hgr, mul_zero]
  have hP1 : charPoly σ κ β 0 1 = 0 := by rw [charPoly_one]; ring
  exact not_determinate_of_two_roots 𝔼 hσ.ne' hκ.ne' hPr hP1 hr1.ne
    (by rw [abs_of_pos hr0]; exact hr1.le) (by norm_num)

/-- Galí (2015), Ex. 4.6: at `φ_p = φ*` the rule does not pin down a unique stationary
equilibrium (roots `−1` and a root in `(−1, 0)`). -/
theorem not_determinate_phiStar [Nonempty Ω] {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) : ¬ Determinate 𝔼 β σ κ (phiStar σ κ β) := by
  set g : ℝ → ℝ := fun x => -(σ * β) * x ^ 2 + (σ + 3 * σ * β + κ) * x + σ with hg
  have hgc : Continuous g := by rw [hg]; fun_prop
  obtain ⟨r, ⟨hr0, hr1⟩, hgr⟩ := intermediate_value_Ioo (show (-1 : ℝ) ≤ 0 by norm_num)
    hgc.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (g (-1)) (g 0) by simp only [hg]; constructor <;> nlinarith)
  have hfac : ∀ x, charPoly σ κ β (phiStar σ κ β) x = (x + 1) * g x := by
    intro x; simp only [hg]; unfold charPoly phiStar; field_simp; ring
  have hPr : charPoly σ κ β (phiStar σ κ β) r = 0 := by rw [hfac, hgr, mul_zero]
  have hP1 : charPoly σ κ β (phiStar σ κ β) (-1) = 0 := by rw [hfac]; ring
  exact not_determinate_of_two_roots 𝔼 hσ.ne' hκ.ne' hPr hP1 (by linarith)
    (abs_le.2 ⟨by linarith, by linarith⟩) (by norm_num)

/-! ### The region `φ* < φ_p < 0`: complex stable roots -/

/-- Galí (2015), Ex. 4.6: the determinant of the backward matrix, `det B(λ) = (σ(1 + β − βλ) −
κ e(λ))/(βσ)`. -/
theorem det2_bwdB {σ κ β φ r : ℝ} (hσ : σ ≠ 0) (hβ : β ≠ 0) :
    det2 (bwdB σ κ β φ r) = (σ * mCoef β r - κ * eCoef σ κ β φ r) / (β * σ) := by
  simp only [det2, bwdB, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), Ex. 4.6: the trace of the backward matrix. -/
theorem tr2_bwdB (σ κ β φ r : ℝ) :
    tr2 (bwdB σ κ β φ r) = mCoef β r / β + (κ + β * σ) / (β * σ) := by
  simp only [tr2, bwdB, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]

/-- Galí (2015), Ex. 4.6: `βσ (1 − tr B + det B) = −κ (1 + e(λ))`. -/
theorem bwdB_one (σ κ β φ r : ℝ) (hσ : σ ≠ 0) (hβ : β ≠ 0) :
    β * σ * (1 - tr2 (bwdB σ κ β φ r) + det2 (bwdB σ κ β φ r)) =
      -(κ * (1 + eCoef σ κ β φ r)) := by
  rw [det2_bwdB hσ hβ, tr2_bwdB]
  field_simp
  ring

/-- Galí (2015), Ex. 4.6: `βσ (1 + tr B + det B) = 2βσ + 2σ(1 + β − βλ) + κ − κ e(λ)`. -/
theorem bwdB_neg_one (σ κ β φ r : ℝ) (hσ : σ ≠ 0) (hβ : β ≠ 0) :
    β * σ * (1 + tr2 (bwdB σ κ β φ r) + det2 (bwdB σ κ β φ r)) =
      2 * β * σ + 2 * σ * mCoef β r + κ - κ * eCoef σ κ β φ r := by
  rw [det2_bwdB hσ hβ, tr2_bwdB]
  field_simp
  ring

/-- Galí (2015), Ex. 4.6: at a root `λ` of `P`,
`βσ (1 − λ)(1 − tr B + det B) = κ φ_p`. -/
theorem keyB_one {σ κ β φ r : ℝ} (hσ : σ ≠ 0) (hβ : β ≠ 0) (hκ : κ ≠ 0)
    (hP : charPoly σ κ β φ r = 0) :
    β * σ * (1 - r) * (1 - tr2 (bwdB σ κ β φ r) + det2 (bwdB σ κ β φ r)) = κ * φ := by
  have h := loadY_mul hκ β r
  rw [show β * σ * (1 - r) * (1 - tr2 (bwdB σ κ β φ r) + det2 (bwdB σ κ β φ r)) =
    (1 - r) * (β * σ * (1 - tr2 (bwdB σ κ β φ r) + det2 (bwdB σ κ β φ r))) by ring,
    bwdB_one σ κ β φ r hσ hβ]
  unfold eCoef
  unfold charPoly at hP
  linear_combination (-(σ * (1 - r))) * h + hP

/-- Galí (2015), Ex. 4.6: at a root `λ` of `P`,
`βσ (1 + λ)(1 + tr B + det B) = P(−1)`. -/
theorem keyB_neg_one {σ κ β φ r : ℝ} (hσ : σ ≠ 0) (hβ : β ≠ 0) (hκ : κ ≠ 0)
    (hP : charPoly σ κ β φ r = 0) :
    β * σ * (1 + r) * (1 + tr2 (bwdB σ κ β φ r) + det2 (bwdB σ κ β φ r)) =
      charPoly σ κ β φ (-1) := by
  have h := loadY_mul hκ β r
  rw [show β * σ * (1 + r) * (1 + tr2 (bwdB σ κ β φ r) + det2 (bwdB σ κ β φ r)) =
    (1 + r) * (β * σ * (1 + tr2 (bwdB σ κ β φ r) + det2 (bwdB σ κ β φ r))) by ring,
    bwdB_neg_one σ κ β φ r hσ hβ]
  unfold eCoef mCoef
  unfold charPoly at hP ⊢
  linear_combination (-(σ * (1 + r))) * h - hP

/-- Galí (2015), Ex. 4.6: a real sequence tending to zero is bounded. -/
theorem bounded_of_tendsto_zero {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 0)) :
    ∃ M, ∀ t, |u t| ≤ M := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto u hu)
  exact ⟨M, fun t => by simpa [Real.norm_eq_abs] using hM (u t) ⟨t, rfl⟩⟩

/-- Galí (2015), Ex. 4.6 (**multiplicity for `φ* < φ_p < 0`**): the polynomial has a root
`λ > 1/β`, the backward matrix `B(λ)` (whose eigenvalues are the two other roots, possibly
complex) is Schur stable, and its decaying solutions give a second stationary equilibrium with
`p̂_{−1} = 0` next to the zero one. -/
theorem not_determinate_of_neg [Nonempty Ω] {β σ κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφ : φ < 0) (hφs : phiStar σ κ β < φ) :
    ¬ Determinate 𝔼 β σ κ φ := by
  obtain ⟨r, hr, hP⟩ := exists_root_large (β := β) hσ hκ hβ0 hβ1 hφ.le
  have hb1 : 1 < 1 / β := by rw [lt_div_iff₀ hβ0]; linarith
  have hr1 : 1 < r := hb1.trans hr
  have hβr : 1 < β * r := by rw [div_lt_iff₀ hβ0] at hr; linarith
  set B := bwdB σ κ β φ r with hBdef
  -- Schur stability of `B`
  have hΔ := delta_eq hκ.ne' hP
  have hD : det2 B = 1 / (β * r) := by
    have hr0 : r ≠ 0 := by linarith
    have hm : σ * mCoef β r - κ * eCoef σ κ β φ r = σ / r := by
      rw [eq_div_iff hr0]; linarith
    rw [hBdef, det2_bwdB hσ.ne' hβ0.ne', hm]
    field_simp
  have hD0 : 0 < det2 B := by rw [hD]; exact div_pos one_pos (by linarith)
  have hD1 : det2 B < 1 := by rw [hD, div_lt_one (by linarith)]; exact hβr
  have k1 := keyB_one hσ.ne' hβ0.ne' hκ.ne' hP
  have k2 := keyB_neg_one hσ.ne' hβ0.ne' hκ.ne' hP
  rw [← hBdef] at k1 k2
  have hP1 := (charPoly_neg_one_pos_iff hκ).2 hφs
  have e1 : 0 < 1 - tr2 B + det2 B := by
    have hneg : β * σ * (1 - r) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
    have : β * σ * (1 - r) * (1 - tr2 B + det2 B) < 0 := by rw [k1]; nlinarith
    by_contra hc
    push Not at hc
    nlinarith
  have e2 : 0 < 1 + tr2 B + det2 B := by
    have hpos : 0 < β * σ * (1 + r) := by positivity
    have : 0 < β * σ * (1 + r) * (1 + tr2 B + det2 B) := by rw [k2]; exact hP1
    exact pos_of_mul_pos_right this hpos.le
  have hB : SchurStable (tr2 B) (det2 B) :=
    ⟨by rw [abs_of_pos hD0]; exact hD1, abs_lt.2 ⟨by linarith, by linarith⟩⟩
  -- the construction
  set dd := r ^ 2 - tr2 B * r + det2 B with hdd
  have hdd0 : 0 < dd := by rw [hdd]; nlinarith
  set s0 : Fin 2 → ℝ := ![B 0 1, B 1 1 - r] with hs0
  set sseq : ℕ → Fin 2 → ℝ := fun t => (B ^ t).mulVec s0 with hsseq
  set hf : (Fin 2 → ℝ) → ℝ := fun x => (r - B 1 1) * x 0 + B 0 1 * x 1 with hhf
  set kseq : ℕ → ℝ := fun t => -hf (sseq t) / dd with hkseq
  have hstep : ∀ t, sseq (t + 1) = B.mulVec (sseq t) := fun t => by
    simp only [hsseq, pow_succ', Matrix.mulVec_mulVec]
  have hk0 : kseq 0 = 0 := by
    simp only [hkseq, hsseq, pow_zero, Matrix.one_mulVec, hhf, hs0, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  have hk : ∀ t, kseq (t + 1) = r * kseq t + sseq t 0 := fun t => by
    have hid : r * hf (sseq t) - hf (B.mulVec (sseq t)) = dd * sseq t 0 := by
      simp only [hhf, hdd, tr2, det2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    simp only [hkseq, hstep t]
    field_simp
    linear_combination hid
  have hbw := fun t => bwd_step (κ := κ) (φ := φ) (r := r) hσ.ne' hβ0.ne' (sseq t)
  -- convergence to zero
  have hs_lim : ∀ j, Tendsto (fun t => sseq t j) atTop (𝓝 0) := fun j => by
    have := ((tendsto_pow_entry hB j 0).mul_const (s0 0)).add
      ((tendsto_pow_entry hB j 1).mul_const (s0 1))
    simpa [hsseq, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hk_lim : Tendsto kseq atTop (𝓝 0) := by
    have := ((((hs_lim 0).const_mul (r - B 1 1)).add ((hs_lim 1).const_mul (B 0 1))).neg).div_const
      dd
    simpa [hkseq, hhf] using this
  obtain ⟨Mk, hMk⟩ := bounded_of_tendsto_zero hk_lim
  obtain ⟨Ms, hMs⟩ := bounded_of_tendsto_zero (hs_lim 1)
  -- the second equilibrium
  set p : ℕ → Ω → ℝ := fun t _ => kseq (t + 1) with hp
  set y : ℕ → Ω → ℝ := fun t _ => sseq t 1 + loadY κ β r * kseq t with hy
  have hpa : 𝔼.Adapted p := fun t => 𝔼.const t _
  have hya : 𝔼.Adapted y := fun t => 𝔼.const t _
  have hlag : ∀ t ω, lagP (fun _ => 0) p t ω = kseq t := by
    intro t ω
    cases t with
    | zero => simp [lagP, hk0]
    | succ t => rfl
  have he : IsEquilibrium 𝔼 β σ κ φ (fun _ => 0) (fun _ => 0) y p
      (fun t => (fun _ => 0) + φ • p t) := by
    refine (eq_iff_pointwise 𝔼 hσ.ne' hpa).2 fun t ω => ?_
    rw [hlag t ω, hp, hy, 𝔼.const, 𝔼.const]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have b1 := (hbw t).1
    have b2 := (hbw t).2
    rw [← hstep t] at b1 b2
    refine ⟨(is_iff (k := kseq t) hκ.ne' hP _ _ _ _).2 ?_, (pc_iff (r := r) hκ.ne' _ _ _ _).2 ?_,
      by simp⟩
    · rw [hk (t + 1), hk t]
      linear_combination b2
    · rw [hk (t + 1), hk t]
      linear_combination b1
  have hb : BoundedEq 𝔼 β σ κ φ (fun _ => 0) (fun _ => 0) y p
      (fun t => (fun _ => 0) + φ • p t) := by
    refine ⟨he, hya, hpa, ⟨Ms + |loadY κ β r| * Mk, fun t ω => ?_⟩, ⟨Mk, fun t ω => hMk (t + 1)⟩⟩
    have h1 := mul_le_mul_of_nonneg_left (hMk t) (abs_nonneg (loadY κ β r))
    calc |sseq t 1 + loadY κ β r * kseq t| ≤ |sseq t 1| + |loadY κ β r * kseq t| :=
          abs_add_le _ _
      _ ≤ Ms + |loadY κ β r| * Mk := by rw [abs_mul]; linarith [hMs t]
  intro hD
  obtain ⟨-, huniq⟩ := hD (fun _ => 0) (fun _ => 0) (map_zero _) ⟨0, fun _ => by simp⟩
  obtain ⟨-, hp0, -⟩ := huniq _ _ _ _ _ _ hb (zero_boundedEq 𝔼 hσ.ne' _)
  have h0 := congrFun (congrFun hp0 0) (Classical.arbitrary Ω)
  simp only [hp, hk 0, hk0, mul_zero, zero_add, hsseq, pow_zero, Matrix.one_mulVec, hs0,
    Matrix.cons_val_zero] at h0
  simp only [hBdef, bwdB, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] at h0
  have : -κ / β ≠ 0 := div_ne_zero (neg_ne_zero.2 hκ.ne') hβ0.ne'
  exact this h0

/-! ### The determinacy region: the corrected statement -/

/-- Galí (2015), Ex. 4.6 (**necessity on `[φ*, 0]`**): for `φ* ≤ φ_p ≤ 0` the price-level rule
does not generate a unique stationary equilibrium. -/
theorem not_determinate_of_le [Nonempty Ω] {β σ κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφ0 : φ ≤ 0) (hφs : phiStar σ κ β ≤ φ) :
    ¬ Determinate 𝔼 β σ κ φ := by
  rcases hφ0.lt_or_eq with hφ | rfl
  · rcases hφs.lt_or_eq with hφs | rfl
    · exact not_determinate_of_neg 𝔼 hσ hκ hβ0 hβ1 hφ hφs
    · exact not_determinate_phiStar 𝔼 hσ hκ hβ0
  · exact not_determinate_zero 𝔼 hσ hκ

/-- **Ex. 4.6, corrected** (Galí 2015, p. 125): for `σ, κ > 0` and `0 < β < 1`, the price-level
rule `i_t = r^n_t + φ_p p̂_t` generates a unique stationary equilibrium (for every initial price
level) if and only if `φ_p > 0` or `φ_p < φ* = −2 − 4σ(1 + β)/κ`. -/
theorem determinate_iff [Nonempty Ω] {β σ κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) : Determinate 𝔼 β σ κ φ ↔ 0 < φ ∨ φ < phiStar σ κ β := by
  constructor
  · intro hD
    by_contra hc
    push Not at hc
    exact not_determinate_of_le 𝔼 hσ hκ hβ0 hβ1 hc.1 hc.2 hD
  · rintro (h | h)
    · exact determinate_of_pos 𝔼 hσ hκ hβ0 hβ1 h
    · exact determinate_of_lt_phiStar 𝔼 hσ hκ hβ0 hβ1 h

/-- **Ex. 4.6** (Galí 2015, p. 125, the book's claim where it is true): for `φ_p ≥ φ*`, in
particular for every `φ_p ≥ 0`, the rule generates a unique stationary equilibrium iff
`φ_p > 0`. -/
theorem determinate_iff_pos_of_ge [Nonempty Ω] {β σ κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφs : phiStar σ κ β ≤ φ) :
    Determinate 𝔼 β σ κ φ ↔ 0 < φ := by
  rw [determinate_iff 𝔼 hσ hκ hβ0 hβ1]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd hφs (not_le.2 h)
  · exact Or.inl

/-- **Ex. 4.6, counterexample** (Galí 2015, p. 125): the printed claim "unique stationary
equilibrium if and only if `φ_p > 0`" fails over all real `φ_p`: `φ_p = φ* − 1 < 0` is
determinate. -/
theorem book_claim_false [Nonempty Ω] {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) : ¬ ∀ φ, Determinate 𝔼 β σ κ φ ↔ 0 < φ := by
  intro h
  have hD := determinate_of_lt_phiStar 𝔼 (φ := phiStar σ κ β - 1) hσ hκ hβ0 hβ1 (by linarith)
  have hneg : phiStar σ κ β - 1 < 0 := by
    unfold phiStar
    have : 0 < 4 * σ * (1 + β) / κ := by positivity
    linarith
  exact absurd ((h _).1 hD) (not_lt.2 hneg.le)

end Gali.MonetaryPolicyDesign.Ex4_6
