/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.ExpLogCES
import Mathlib.Algebra.BigOperators.Option

/-!
# Cross-sectional moments, the Calvo mixture and the Calvo slopes

Woodford (2003), *Interest and Prices*, Chapter 6, §2 (pp. 392–405) and Appendix E.2
(pp. 694–696), App. E.6–E.7 (pp. 703–706): the cross-sectional moment algebra shared by every
welfare criterion of the chapter, for a finite weighted population of goods (the moments
`ExpLogCES.crossMean`, `ExpLogCES.crossVar`).

## Main results

* The Calvo mixture (E.8), p. 695, as an identity between moments (proved once, used by every
  form of the mixture: finite weights, distributions on `ℝ`, the goods population, list
  populations): `mix_var_shift`, `mix_mean_shift`, `mix_var_meanChange` (with an indexation
  shift `d`, (2.24), p. 402).
* Finite weighted populations: `crossMean_affine`, `crossVar_affine`, `crossVar_demand`
  ((2.12), p. 396: `var_i log y = θ² var_i log p`), `sum_sq_eq`, `mean_quadratic`, and the
  Calvo mixture of a finite population (`Option ι` adjoins the atom `p*`): `mixW`, `mixX`,
  `mixW_sum`, `mix_mean`, `mix_var` (exact (E.8)/(2.24)).
* The Calvo slopes (Chapter 3, restated): `calvoXi` (`ξ = (1−α)(1−αβ)/(α(1+ωθ))`), `calvoK`
  (`α/((1−α)(1−αβ))`, the coefficient of the discounted dispersion), `calvoKappa`
  (`κ = ξ(ω+σ⁻¹)`), and the identity `calvoK_mul` (`(1+ωθ)·α/((1−α)(1−αβ)) = ξ⁻¹`) behind every
  `λ = κ/θ` of the chapter.
-/

namespace Woodford.StabilizationWelfare.Moments

open ExpLogCES

/-! ### The Calvo mixture (E.8): exact moment algebra -/

/-- Woodford (2003), eq. (E.8), p. 695 (the moment algebra, with an indexation shift `d`):
if the new cross-section is `α` times the old one shifted by `d` plus an atom `1 − α` at `p`,
so that `m' = α(m + d) + (1−α)p` and `s' = α(s + 2dm + d²) + (1−α)p²`, then
`s' − m'² = α(s − m²) + α(1−α)(p − m − d)²`. -/
theorem mix_var_shift {α m s d p m' s' : ℝ} (hm : m' = α * (m + d) + (1 - α) * p)
    (hs : s' = α * (s + 2 * d * m + d ^ 2) + (1 - α) * p ^ 2) :
    s' - m' ^ 2 = α * (s - m ^ 2) + α * (1 - α) * (p - m - d) ^ 2 := by
  subst hm hs
  ring

/-- Woodford (2003), p. 695: the mean moves as `m' − m − d = (1 − α)(p − m − d)`. -/
theorem mix_mean_shift {α m d p m' : ℝ} (hm : m' = α * (m + d) + (1 - α) * p) :
    m' - m - d = (1 - α) * (p - m - d) := by
  subst hm
  ring

/-- Woodford (2003), eq. (E.8), p. 695 (moment algebra, in terms of the change in the mean):
for `α ≠ 1`, `s' − m'² = α(s − m²) + (α/(1−α))(m' − m − d)²`. -/
theorem mix_var_meanChange {α m s d p m' s' : ℝ} (hα : α ≠ 1)
    (hm : m' = α * (m + d) + (1 - α) * p)
    (hs : s' = α * (s + 2 * d * m + d ^ 2) + (1 - α) * p ^ 2) :
    s' - m' ^ 2 = α * (s - m ^ 2) + α / (1 - α) * (m' - m - d) ^ 2 := by
  rw [mix_var_shift hm hs, mix_mean_shift hm]
  have : (1 : ℝ) - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hα)
  field_simp

/-! ### Finite weighted populations -/

variable {ι : Type*} [Fintype ι]

/-- Woodford (2003), eq. (2.12), p. 396: the mean of an affine transform,
`E(a + b z) = a + b E z` (weights summing to one). -/
theorem crossMean_affine {w : ι → ℝ} (hw : ∑ i, w i = 1) (a b : ℝ) (z : ι → ℝ) :
    crossMean w (fun i => a + b * z i) = a + b * crossMean w z := by
  rw [crossMean_const_add hw a (fun i => b * z i), crossMean_mul]

/-- Woodford (2003), eq. (2.12), p. 396: the variance of an affine transform,
`var(a + b z) = b² var z` (weights summing to one). -/
theorem crossVar_affine {w : ι → ℝ} (hw : ∑ i, w i = 1) (a b : ℝ) (z : ι → ℝ) :
    crossVar w (fun i => a + b * z i) = b ^ 2 * crossVar w z := by
  rw [crossVar_const_add hw a (fun i => b * z i), crossVar_mul]

/-- Woodford (2003), eq. (2.12), p. 396: with Dixit–Stiglitz demand
`log y(i) = log Y − θ(log p(i) − log P)` the dispersion of log output is `θ²` times the
dispersion of log prices: `var_i ŷ(i) = θ² var_i log p(i)` (weights summing to one). -/
theorem crossVar_demand {w : ι → ℝ} (hw : ∑ i, w i = 1) (p : ι → ℝ) (Y P θ : ℝ) :
    crossVar w (fun i => Y - θ * (p i - P)) = θ ^ 2 * crossVar w p := by
  have h := crossVar_affine hw (Y + θ * P) (-θ) p
  rw [neg_sq] at h
  rw [← h]
  congr 1
  funext i
  ring

/-- Woodford (2003), App. E.1, p. 694: `E_i z² = var_i z + (E_i z)²` (weights summing to
one). -/
theorem sum_sq_eq {w : ι → ℝ} (hw : ∑ i, w i = 1) (z : ι → ℝ) :
    ∑ i, w i * z i ^ 2 = crossVar w z + crossMean w z ^ 2 := by
  rw [crossVar_eq hw]
  unfold crossMean
  ring

/-- Woodford (2003), App. E.1, p. 694 ("integrating this expression over the differentiated
goods"): the cross-sectional average of a quadratic `a z + b z²` is
`a E z + b((E z)² + var z)`. -/
theorem mean_quadratic {w : ι → ℝ} (hw : ∑ i, w i = 1) (a b : ℝ) (z : ι → ℝ) :
    ∑ i, w i * (a * z i + b * z i ^ 2) =
      a * crossMean w z + b * (crossMean w z ^ 2 + crossVar w z) := by
  have h : ∀ i, w i * (a * z i + b * z i ^ 2) = a * (w i * z i) + b * (w i * z i ^ 2) :=
    fun i => by ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_sq_eq hw]
  unfold crossMean
  ring

/-! ### The Calvo mixture of a finite population -/

/-- Woodford (2003), App. E.2, p. 695 and E.7, p. 706: the weights of the Calvo mixture, `α w_i`
on the old population and `1 − α` on the atom (`none`). -/
def mixW (α : ℝ) (w : ι → ℝ) : Option ι → ℝ := fun o => o.elim (1 - α) fun i => α * w i

/-- Woodford (2003), pp. 695 and 402: the log prices of the mixture, the new price `p` on the
atom and the old prices shifted by `d` (`d = 0`: Calvo; `d = γ π_{t−1}`: indexation). -/
def mixX (x : ι → ℝ) (d p : ℝ) : Option ι → ℝ := fun o => o.elim p fun i => x i + d

/-- Woodford (2003), App. E.2, p. 695: the mixture weights sum to one. -/
theorem mixW_sum {w : ι → ℝ} (hw : ∑ i, w i = 1) (α : ℝ) : ∑ o, mixW α w o = 1 := by
  rw [Fintype.sum_option]
  simp only [mixW, Option.elim_none, Option.elim_some, ← Finset.mul_sum, hw]
  ring

/-- Woodford (2003), App. E.2, p. 695 (exact): the mixture mean is
`P̄_t = α (P̄_{t−1} + d) + (1 − α) p*`. -/
theorem mix_mean {w : ι → ℝ} (hw : ∑ i, w i = 1) (α : ℝ) (x : ι → ℝ) (d p : ℝ) :
    crossMean (mixW α w) (mixX x d p) = α * (crossMean w x + d) + (1 - α) * p := by
  simp only [crossMean, Fintype.sum_option, mixW, mixX, Option.elim_none, Option.elim_some]
  have : ∀ i, α * w i * (x i + d) = α * (w i * x i) + α * d * w i := fun i => by ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hw]
  ring

/-- Woodford (2003), eq. (E.8), p. 695, (2.24), p. 402, and App. E.7, p. 706 (**finite
weights, exact**): the variance of `α · (old population shifted by d) + (1 − α) · δ_p` is
`Δ_t = α Δ_{t−1} + (α/(1−α)) (P̄_t − P̄_{t−1} − d)²`. -/
theorem mix_var {w : ι → ℝ} (hw : ∑ i, w i = 1) {α : ℝ} (hα : α ≠ 1) (x : ι → ℝ)
    (d p : ℝ) :
    crossVar (mixW α w) (mixX x d p) =
      α * crossVar w x +
        α / (1 - α) * (crossMean (mixW α w) (mixX x d p) - crossMean w x - d) ^ 2 := by
  rw [crossVar_eq (mixW_sum hw α), crossVar_eq hw]
  refine mix_var_meanChange hα (mix_mean hw α x d p) ?_
  simp only [crossMean, Fintype.sum_option, mixW, mixX, Option.elim_none, Option.elim_some]
  have : ∀ i, α * w i * (x i + d) ^ 2 =
      α * (w i * x i ^ 2) + 2 * d * α * (w i * x i) + α * d ^ 2 * w i := fun i => by ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, hw]
  ring

/-! ### The Calvo slopes (Chapter 3, restated) -/

/-- Woodford (2003), Ch. 3, eq. (2.19) (restated): the Calvo slope factor
`ξ = (1 − α)(1 − αβ)/[α(1 + ωθ)]` (for wages, `ω = ν` and `θ = θ_w`). -/
noncomputable def calvoXi (α β ω θ : ℝ) : ℝ := (1 - α) * (1 - α * β) / (α * (1 + ω * θ))

/-- Woodford (2003), p. 400: the Calvo coefficient `α/[(1 − α)(1 − αβ)]` of the discounted
dispersion. -/
noncomputable def calvoK (α β : ℝ) : ℝ := α / ((1 - α) * (1 - α * β))

/-- Woodford (2003), Ch. 3, eq. (2.19), restated: the slope of the New Keynesian Phillips curve
with Calvo pricing and firm-specific inputs, `κ = (1−α)(1−αβ)/α · (ω+σ⁻¹)/(1+ωθ)`. -/
noncomputable def calvoKappa (α β ω θ σ : ℝ) : ℝ :=
  (1 - α) * (1 - α * β) / α * ((ω + σ) / (1 + ω * θ))

/-- Woodford (2003), Ch. 3: `κ = ξ (ω + σ⁻¹)`. -/
theorem calvoKappa_eq (α β ω θ σ : ℝ) : calvoKappa α β ω θ σ = calvoXi α β ω θ * (ω + σ) := by
  unfold calvoKappa calvoXi
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- Woodford (2003), p. 400 (the weight on discounted squared inflation):
`(1 + ωθ) · α/((1 − α)(1 − αβ)) = ξ⁻¹`. Every `λ = κ/θ` of the chapter is this identity. -/
theorem calvoK_mul (α β ω θ : ℝ) : (1 + ω * θ) * calvoK α β = (calvoXi α β ω θ)⁻¹ := by
  unfold calvoK calvoXi
  rw [inv_div]
  ring

end Woodford.StabilizationWelfare.Moments
