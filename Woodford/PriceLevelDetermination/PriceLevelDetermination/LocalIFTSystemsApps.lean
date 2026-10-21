/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.LocalIFTSystems
import PriceLevelDetermination.InertialRules

/-!
# Applications of the `n`-dimensional local determinacy theorem

Woodford (2003), *Interest and Prices*, Appendix A.3, pp. 631–635, applied to a model of the
book with a predetermined variable, and linked to the scalar theory of `LocalIFT`.

## The inertial rule (2.12) (Prop. 2.8, p. 96; App. A.8)

The exact perfect-foresight conditions with `x_t = (π_t, î_t)` and disturbances
`e_t = (r̂_t, ν_t)` are the Fisher equation (1.32) `î_t = r̂_t + π_{t+1}` and a nonlinear inertial
rule `î_t = Ψ(π_t, î_{t−1}) + ν_t` (`Finert`); `î_{t−1}` is predetermined. Its linearisation has
`f₃ = [[−1, 0], [0, 0]]` singular (`M_Finert`), and
`det(f₃λ² + f₂λ + f₁) = λ²(φ_π + ρ − λ)` (`quadPoly_inert`, `roots_inert`).

* `isUnit_linOp_inert_iff`, `rootCondition_inert_iff`, `homInjective_inert_iff`: the root
  condition holds iff `φ_π ≠ 0` and `|φ_π + ρ| > 1` — condition (A.22) of Prop. 2.8, recovered
  from the general theorem and cross-checked against `InertialRules.determinate8_iff`
  (`isUnit_linOp_inert_iff_determinate8`).
* `inertial_local_determinacy`: under (A.22) the exact model has a locally unique equilibrium
  for every initial interest rate near the steady state and small disturbances, `C¹` in
  `(î_{−1}, r̂, ν)`, approximated by the log-linear solution; `inertial_second_order`: with
  error `O(‖u‖²)` for a `C²` rule; `inertial_iff`: and only then (with a differentiable solution
  map).
* `inert_book_count_fails`: the printed count "`n` roots inside and `n` outside" never holds for
  this model (degree 3 < 4), determinate or not — the singular-`f₃` failure of (A.9) occurs in
  the book's own model.

## The scalar case

* `embedF`: a scalar condition `F₀(x_t, x_{t+1}, e_t) = 0` of `LocalIFT` as an `n = 1` system;
  `solves_embedF_iff`, `linOp_embedF` (the operator (A.8) is `LocalIFT.TOp a b`),
  `isUnit_linOp_embedF_iff`, `rootCondition_embedF_iff` (the general root condition is
  `|b| < |a|`, `LocalIFT.isUnit_TOp_iff`), `linSol_embedF` (the linear solution is
  `LocalIFT.linSol3`), and `scalar_local_determinacy_recovered`: the statement of
  `LocalIFT.local_determinacy_loc` derived from the `n`-dimensional theorem.
* E18 in this framework: `not_second_order_C1` — for the `C¹` condition `F0g` (built on
  `LocalIFT.gE`) no `O(‖u‖²)` bound holds, so `LocalIFTSystems.second_order_loc` needs `C²`.
-/

namespace Woodford.PriceLevelDetermination.LocalIFTSystemsApps

open scoped Topology Matrix
open Polynomial LinearSystems LocalIFTSystems

/-! ### The inertial rule (2.12) as an exact two-variable system with a predetermined variable -/

/-- Woodford (2003), eqs. (1.32) and (2.12), pp. 79, 96: the exact perfect-foresight conditions
with `x_t = (π_t, î_t)` (coordinates `0`, `1`) and disturbances `e_t = (r̂_t, ν_t)`: the Fisher
equation `î_t = r̂_t + π_{t+1}` (exact in logs) and a nonlinear inertial rule
`î_t = Ψ(π_t, î_{t−1}) + ν_t` (for `Ψ(π, i) = φ_π π + ρ i` this is (2.12) with
`ν_t = ī_t − ρ ī_{t−1}`). The lagged interest rate is the predetermined variable. -/
def Finert (Ψ : ℝ × ℝ → ℝ) (p : Arg (Fin 2) (Fin 2 → ℝ)) : Fin 2 → ℝ :=
  ![p.2.1 1 - p.2.2.1 0 - p.2.2.2 0, p.2.1 1 - Ψ (p.2.1 0, p.1 1) - p.2.2.2 1]

/-- Woodford (2003), (2.12), p. 96 (tool): the linear map `(x_{t−1}, x_t, …) ↦ (π_t, î_{t−1})`
feeding the rule. -/
noncomputable def ruleArg : Arg (Fin 2) (Fin 2 → ℝ) →L[ℝ] ℝ × ℝ :=
  ((ContinuousLinearMap.proj 0).comp ((ContinuousLinearMap.fst ℝ (Fin 2 → ℝ)
      ((Fin 2 → ℝ) × (Fin 2 → ℝ))).comp (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ)
        ((Fin 2 → ℝ) × (Fin 2 → ℝ) × (Fin 2 → ℝ))))).prod
    ((ContinuousLinearMap.proj 1).comp (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ)
      ((Fin 2 → ℝ) × (Fin 2 → ℝ) × (Fin 2 → ℝ))))

/-- Woodford (2003), (2.12), p. 96 (tool): coordinates of `ruleArg`. -/
@[simp] theorem ruleArg_apply (p : Arg (Fin 2) (Fin 2 → ℝ)) :
    ruleArg p = (p.2.1 0, p.1 1) := rfl

/-- Woodford (2003), (1.32), p. 79 (tool): the linear part of the conditions,
`(x_{t−1}, x_t, x_{t+1}, e_t) ↦ (î_t − π_{t+1} − r̂_t, î_t − ν_t)`. -/
noncomputable def linPart : Arg (Fin 2) (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi fun k => ![
    (ContinuousLinearMap.proj 1).comp ((ContinuousLinearMap.fst ℝ (Fin 2 → ℝ)
        ((Fin 2 → ℝ) × (Fin 2 → ℝ))).comp (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ)
          ((Fin 2 → ℝ) × (Fin 2 → ℝ) × (Fin 2 → ℝ)))) -
      (ContinuousLinearMap.proj 0).comp ((ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 2 → ℝ)).comp
        ((ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) ((Fin 2 → ℝ) × (Fin 2 → ℝ))).comp
          (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) ((Fin 2 → ℝ) × (Fin 2 → ℝ) × (Fin 2 → ℝ))))) -
      (ContinuousLinearMap.proj 0).comp ((ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ)).comp
        ((ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) ((Fin 2 → ℝ) × (Fin 2 → ℝ))).comp
          (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) ((Fin 2 → ℝ) × (Fin 2 → ℝ) × (Fin 2 → ℝ))))),
    (ContinuousLinearMap.proj 1).comp ((ContinuousLinearMap.fst ℝ (Fin 2 → ℝ)
        ((Fin 2 → ℝ) × (Fin 2 → ℝ))).comp (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ)
          ((Fin 2 → ℝ) × (Fin 2 → ℝ) × (Fin 2 → ℝ)))) -
      (ContinuousLinearMap.proj 1).comp ((ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ)).comp
        ((ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) ((Fin 2 → ℝ) × (Fin 2 → ℝ))).comp
          (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) ((Fin 2 → ℝ) × (Fin 2 → ℝ) × (Fin 2 → ℝ)))))] k

/-- Woodford (2003), (1.32), p. 79 (tool): coordinates of the linear part. -/
theorem linPart_apply (p : Arg (Fin 2) (Fin 2 → ℝ)) :
    linPart p = ![p.2.1 1 - p.2.2.1 0 - p.2.2.2 0, p.2.1 1 - p.2.2.2 1] := by
  funext k
  fin_cases k <;> rfl

/-- Woodford (2003), (2.12), p. 96 (tool): the rule enters only the second equation. -/
noncomputable def ruleInj : ℝ →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi fun k => ![0, ContinuousLinearMap.id ℝ ℝ] k

/-- Woodford (2003), (2.12), p. 96 (tool): coordinates of `ruleInj`. -/
theorem ruleInj_apply (a : ℝ) : ruleInj a = ![0, a] := by
  funext k
  fin_cases k <;> rfl

/-- Woodford (2003), (1.32) and (2.12), pp. 79, 96 (tool): the conditions are the linear part
minus the rule. -/
theorem Finert_eq (Ψ : ℝ × ℝ → ℝ) :
    Finert Ψ = fun p => linPart p - ruleInj (Ψ (ruleArg p)) := by
  funext p k
  rw [linPart_apply, ruleInj_apply, ruleArg_apply]
  fin_cases k
  · simp [Finert]
  · simp [Finert]
    ring

/-- Woodford (2003), (2.12), p. 96: the derivative `(π, î_{−1}) ↦ φ_π π + ρ î_{−1}` of a rule
with slopes `φ_π`, `ρ` at the steady state. -/
noncomputable def ruleD (φ ρ : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  φ • ContinuousLinearMap.fst ℝ ℝ ℝ + ρ • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- Woodford (2003), (2.12), p. 96: the derivative of the exact conditions at the steady state,
when the rule has slopes `φ_π = ∂Ψ/∂π` and `ρ = ∂Ψ/∂î_{−1}` there. -/
theorem hasFDerivAt_Finert {Ψ : ℝ × ℝ → ℝ} {φ ρ : ℝ}
    (hΨ : HasFDerivAt Ψ (ruleD φ ρ) 0) :
    HasFDerivAt (Finert Ψ) (linPart - ruleInj.comp ((ruleD φ ρ).comp ruleArg)) 0 := by
  rw [Finert_eq]
  have h0 : ruleArg (0 : Arg (Fin 2) (Fin 2 → ℝ)) = 0 := map_zero _
  have hΨ' : HasFDerivAt Ψ (ruleD φ ρ) (ruleArg (0 : Arg (Fin 2) (Fin 2 → ℝ))) := by
    rw [h0]; exact hΨ
  exact linPart.hasFDerivAt.sub
    (ruleInj.hasFDerivAt.comp 0 (hΨ'.comp 0 ruleArg.hasFDerivAt))

/-- Woodford (2003), (1.32) and (2.12), pp. 79, 96: the linearised conditions,
`(î_t − π_{t+1} − r̂_t, î_t − φ_π π_t − ρ î_{t−1} − ν_t)`. -/
theorem fderiv_Finert_apply {Ψ : ℝ × ℝ → ℝ} {φ ρ : ℝ}
    (hΨ : HasFDerivAt Ψ (ruleD φ ρ) 0)
    (p : Arg (Fin 2) (Fin 2 → ℝ)) :
    fderiv ℝ (Finert Ψ) 0 p =
      ![p.2.1 1 - p.2.2.1 0 - p.2.2.2 0, p.2.1 1 - (φ * p.2.1 0 + ρ * p.1 1) - p.2.2.2 1] := by
  rw [(hasFDerivAt_Finert hΨ).fderiv]
  funext k
  fin_cases k
  · simp [linPart_apply, ruleInj_apply]
  · simp [linPart_apply, ruleInj_apply, ruleD]
    ring

/-- Woodford (2003), (2.12), p. 96: `f₁` of the inertial system (only `î_{t−1}` enters). -/
def inF1 (ρ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, -ρ]

/-- Woodford (2003), (1.32) and (2.12), pp. 79, 96: `f₂` of the inertial system. -/
def inF2 (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -φ, 1]

/-- Woodford (2003), (1.32), p. 79: `f₃` of the inertial system (singular: only `π_{t+1}`
enters, in the Fisher equation). -/
def inF3 : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 0; 0, 0]

/-- Woodford (2003), (1.32) and (2.12), pp. 79, 96: the coefficient matrices of the linearised
inertial system are `f₁ = [[0, 0], [0, −ρ]]`, `f₂ = [[0, 1], [−φ_π, 1]]`,
`f₃ = [[−1, 0], [0, 0]]`. -/
theorem M_Finert {Ψ : ℝ × ℝ → ℝ} {φ ρ : ℝ}
    (hΨ : HasFDerivAt Ψ (ruleD φ ρ) 0) :
    M1 (Finert Ψ) = inF1 ρ ∧ M2 (Finert Ψ) = inF2 φ ∧ M3 (Finert Ψ) = inF3 := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;>
    simp only [M1, M2, M3, LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe, d1, d2, d3,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply, fderiv_Finert_apply hΨ] <;>
    fin_cases i <;> fin_cases j <;> simp [inF1, inF2, inF3]

/-- Woodford (2003), (1.32) and (2.12), pp. 79, 96: the disturbance derivative is `−1` (each
disturbance moves one equation). -/
theorem dE_Finert {Ψ : ℝ × ℝ → ℝ} {φ ρ : ℝ}
    (hΨ : HasFDerivAt Ψ (ruleD φ ρ) 0)
    (v : Fin 2 → ℝ) : dE (Finert Ψ) v = -v := by
  simp only [dE, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    fderiv_Finert_apply hΨ]
  funext k
  fin_cases k <;> simp

/-- Woodford (2003), eq. (A.9), p. 632, for rule (2.12): the characteristic polynomial is
`det(f₃λ² + f₂λ + f₁) = λ²(φ_π + ρ − λ)` — of degree `3 < 2n = 4`, since `f₃` is singular. -/
theorem quadPoly_inert (φ ρ : ℝ) :
    quadPoly (inF1 ρ) (inF2 φ) inF3 = X ^ 2 * (C (φ + ρ) - X) := by
  refine Polynomial.funext fun r => ?_
  rw [eval_quadPoly, Matrix.det_fin_two]
  simp [inF1, inF2, inF3]
  ring

/-- Woodford (2003), eq. (A.9), p. 632, for rule (2.12): the roots are `0, 0, φ_π + ρ`. -/
theorem roots_inert (φ ρ : ℝ) :
    ((quadPoly (inF1 ρ) (inF2 φ) inF3).map Complex.ofRealHom).roots =
      2 • ({0} : Multiset ℂ) + {((φ + ρ : ℝ) : ℂ)} := by
  have e : (quadPoly (inF1 ρ) (inF2 φ) inF3).map Complex.ofRealHom =
      -(X ^ 2 * (X - C ((φ + ρ : ℝ) : ℂ))) := by
    rw [quadPoly_inert, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_X,
      Polynomial.map_C]
    simp only [Complex.ofRealHom_eq_coe]
    ring
  have hm : (X ^ 2 * (X - C ((φ + ρ : ℝ) : ℂ))).Monic := (monic_X_pow 2).mul (monic_X_sub_C _)
  rw [e, roots_neg, roots_mul hm.ne_zero, roots_X_pow, roots_X_sub_C]

/-- Woodford (2003), (2.12), p. 96 (tool): a bounded geometric sequence with ratio of modulus
above one starts at zero. -/
theorem eq_zero_of_geom_bounded {a c C : ℝ} (ha : 1 < |a|) (h : ∀ t : ℕ, |a ^ t * c| ≤ C) :
    c = 0 := by
  by_contra hc
  have hc' : 0 < |c| := abs_pos.mpr hc
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / |c|) ha
  have := h n
  rw [abs_mul, abs_pow] at this
  rw [div_lt_iff₀ hc'] at hn
  linarith

/-- Woodford (2003), Prop. 2.8, p. 96, and (A.22): genericity for rule (2.12) — the
homogeneous linearised system with `x_{−1} = 0` has no nonzero bounded solution iff `φ_π ≠ 0`
and `|φ_π + ρ| > 1`. -/
theorem homInjective_inert_iff (φ ρ : ℝ) :
    HomInjective (inF1 ρ) (inF2 φ) inF3 ↔ φ ≠ 0 ∧ 1 < |φ + ρ| := by
  have hsol : ∀ x : ℕ → Fin 2 → ℝ, SolvesLin (inF1 ρ) (inF2 φ) inF3 0 0 x ↔
      ∀ t, x t 1 - x (t + 1) 0 = 0 ∧ x t 1 - φ * x t 0 - ρ * lagV 0 x t 1 = 0 := by
    intro x
    refine forall_congr' fun t => ?_
    rw [funext_iff, Fin.forall_fin_two]
    simp only [inF1, inF2, inF3, Pi.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Pi.zero_apply]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  constructor
  · intro hinj
    by_contra hc
    -- a nonzero bounded solution of the homogeneous system
    set a := φ + ρ with ha
    by_cases hφ : φ = 0
    · set x : ℕ → Fin 2 → ℝ := fun t => if t = 0 then ![1, 0] else 0 with hx
      have hxs : SolvesLin (inF1 ρ) (inF2 φ) inF3 0 0 x := by
        rw [hsol]
        intro t
        cases t with
        | zero => simp [hx, hφ]
        | succ t => cases t <;> simp [hx, hφ]
      have := congrFun (congrFun (hinj x ⟨1, fun t i => by
        by_cases ht : t = 0
        · subst ht; fin_cases i <;> simp [hx]
        · simp [hx, ht]⟩ hxs) 0) 0
      simp [hx] at this
    · have hle : |a| ≤ 1 := by
        push Not at hc
        exact hc hφ
      set x : ℕ → Fin 2 → ℝ := fun t => ![lagV 1 (fun s => a ^ s * φ) t, a ^ t * φ] with hx
      have hxs : SolvesLin (inF1 ρ) (inF2 φ) inF3 0 0 x := by
        rw [hsol]
        intro t
        cases t with
        | zero => simp [hx]
        | succ t =>
          simp only [hx, lagV_succ, Matrix.cons_val_one, Matrix.cons_val_zero]
          constructor
          · ring
          · rw [ha]; ring
      have hp : ∀ t : ℕ, |a ^ t * φ| ≤ |φ| := fun t => by
        rw [abs_mul, abs_pow]
        exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hle)
      have hxb : BoundedSeq x := ⟨max 1 |φ|, fun t i => by
        fin_cases i
        · cases t with
          | zero => simp [hx]
          | succ t => exact le_max_of_le_right (by simpa [hx] using hp t)
        · exact le_max_of_le_right (by simpa [hx] using hp t)⟩
      have := congrFun (congrFun (hinj x hxb hxs) 0) 0
      simp [hx] at this
  · rintro ⟨hφ, ha⟩ x hxb hx
    rw [hsol] at hx
    obtain ⟨C, hC⟩ := hxb
    have hi : ∀ t, x t 1 = (φ + ρ) ^ t * x 0 1 := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        have h1 := (hx t).1
        have h2 := (hx (t + 1)).2
        simp only [lagV_succ] at h2
        rw [pow_succ, mul_comm ((φ + ρ) ^ t), mul_assoc, ← ih]
        linear_combination h2 - φ * h1
    have hi0 : x 0 1 = 0 := eq_zero_of_geom_bounded ha fun t => by rw [← hi]; exact hC t 1
    have hi' : ∀ t, x t 1 = 0 := fun t => by rw [hi, hi0, mul_zero]
    funext t k
    fin_cases k
    · cases t with
      | zero =>
        have h2 := (hx 0).2
        simp only [lagV_zero, Pi.zero_apply, hi0] at h2
        simp only [Pi.zero_apply]
        have : φ * x 0 0 = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left hφ
      | succ t =>
        have h1 := (hx t).1
        change x (t + 1) 0 = 0
        linarith [hi' t]
    · exact hi' t

/-- **Prop. 2.8 / (A.22) from the general theorem** (Woodford (2003), eq. (A.9), p. 632 and
Prop. 2.8, p. 96): for the inertial system the exact root condition holds iff `φ_π ≠ 0` and
`|φ_π + ρ| > 1`. -/
theorem rootCondition_inert_iff (φ ρ : ℝ) :
    (quadPoly (inF1 ρ) (inF2 φ) inF3 ≠ 0 ∧
      (∀ μ ∈ ((quadPoly (inF1 ρ) (inF2 φ) inF3).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1) ∧
      Multiset.card (((quadPoly (inF1 ρ) (inF2 φ) inF3).map Complex.ofRealHom).roots.filter
        (fun μ => ‖μ‖ < 1)) = Fintype.card (Fin 2) ∧ HomInjective (inF1 ρ) (inF2 φ) inF3) ↔
      φ ≠ 0 ∧ 1 < |φ + ρ| := by
  rw [homInjective_inert_iff, roots_inert]
  have hn : ‖((φ + ρ : ℝ) : ℂ)‖ = |φ + ρ| := by rw [Complex.norm_real, Real.norm_eq_abs]
  constructor
  · rintro ⟨-, -, -, h⟩
    exact h
  · rintro ⟨hφ, ha⟩
    refine ⟨?_, ?_, ?_, hφ, ha⟩
    · rw [quadPoly_inert]
      exact mul_ne_zero (pow_ne_zero 2 X_ne_zero) (by
        rw [← neg_sub]
        exact neg_ne_zero.mpr (X_sub_C_ne_zero _))
    · intro μ hμ
      simp only [Multiset.mem_add, Multiset.mem_nsmul, Multiset.mem_singleton] at hμ
      rcases hμ with ⟨-, rfl⟩ | rfl
      · simp
      · rw [hn]; exact ha.ne'
    · rw [Multiset.filter_add, Multiset.filter_nsmul, Multiset.filter_singleton,
        Multiset.filter_singleton, hn]
      simp [not_lt.mpr ha.le]

/-- **Prop. 2.8 / (A.22) from the general theorem**, operator form (Woodford (2003), App. A.3,
pp. 632–633): the derivative (A.8) of the exact inertial system is invertible on `ℓ∞` iff
`φ_π ≠ 0` and `|φ_π + ρ| > 1`. -/
theorem isUnit_linOp_inert_iff {Ψ : ℝ × ℝ → ℝ} {φ ρ : ℝ} (hΨ : HasFDerivAt Ψ (ruleD φ ρ) 0) :
    IsUnit (linOp (Finert Ψ)) ↔ φ ≠ 0 ∧ 1 < |φ + ρ| := by
  obtain ⟨h1, h2, h3⟩ := M_Finert hΨ
  rw [isUnit_linOp_iff, h1, h2, h3]
  exact rootCondition_inert_iff φ ρ

/-- Woodford (2003), Prop. 2.8, p. 96 (**cross-check with `InertialRules`**): invertibility of
(A.8) for the exact inertial system is the determinacy of the linear model (1.32)+(2.12) proved
directly in `InertialRules.determinate8_iff` (here under perfect foresight). -/
theorem isUnit_linOp_inert_iff_determinate8 {Ψ : ℝ × ℝ → ℝ} {φ ρ : ℝ}
    (hΨ : HasFDerivAt Ψ (ruleD φ ρ) 0) :
    IsUnit (linOp (Finert Ψ)) ↔ InertialRules.Determinate8 perfectForesight φ ρ := by
  rw [isUnit_linOp_inert_iff hΨ, InertialRules.determinate8_iff]

/-- Woodford (2003), (1.32) and (2.12) (tool): the exact inertial conditions are `C¹` near the
steady state when the rule is. -/
theorem contDiffAt_Finert {Ψ : ℝ × ℝ → ℝ} {k : ℕ} (hΨ : ContDiffAt ℝ k Ψ 0) :
    ContDiffAt ℝ k (Finert Ψ) 0 := by
  rw [Finert_eq]
  have h0 : ruleArg (0 : Arg (Fin 2) (Fin 2 → ℝ)) = 0 := map_zero _
  have hΨ' : ContDiffAt ℝ k Ψ (ruleArg (0 : Arg (Fin 2) (Fin 2 → ℝ))) := by rw [h0]; exact hΨ
  exact linPart.contDiff.contDiffAt.sub
    (ruleInj.contDiff.contDiffAt.comp 0 (hΨ'.comp 0 ruleArg.contDiff.contDiffAt))

/-- Woodford (2003), (1.32) and (2.12): the steady state solves the exact conditions. -/
theorem Finert_zero {Ψ : ℝ × ℝ → ℝ} (h0 : Ψ 0 = 0) : Finert Ψ 0 = 0 := by
  funext k
  have h : Ψ (0, 0) = 0 := by rw [Prod.mk_zero_zero]; exact h0
  fin_cases k <;> simp [Finert, h]

/-- **Local determinacy of the exact inertial-rule model** (Woodford (2003), Prop. 2.8, p. 96,
nonlinear part, and App. A.3, pp. 632–633; the book leaves it to A.3): for a rule
`î_t = Ψ(π_t, î_{t−1}) + ν_t`, `C¹` near the steady state with slopes `φ_π ≠ 0`, `ρ` and
`|φ_π + ρ| > 1`, for every initial interest rate `î_{−1}` near the steady state and all small
bounded disturbance paths `{r̂_t, ν_t}` there is exactly one perfect-foresight equilibrium
`{π_t, î_t}` near the steady state; it depends `C¹` on `(î_{−1}, r̂, ν)` and its derivative is
the solution of the log-linear model (1.32)+(2.12). -/
theorem inertial_local_determinacy {Ψ : ℝ × ℝ → ℝ} {φ ρ : ℝ} (hΨc : ContDiffAt ℝ 1 Ψ 0)
    (hΨ0 : Ψ 0 = 0) (hΨ : HasFDerivAt Ψ (ruleD φ ρ) 0) (hφ : φ ≠ 0) (ha : 1 < |φ + ρ|)
    {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ε ≤ η ∧ ∃ δ > 0, δ ≤ η ∧ ∃ X : Par (Fin 2) (Fin 2 → ℝ) → SeqV (Fin 2), X 0 = 0 ∧
      HasFDerivAt X (linSol (Finert Ψ)) 0 ∧
      ∀ u : Par (Fin 2) (Fin 2 → ℝ), ‖u‖ < δ → ‖X u‖ < ε / 2 ∧ Solves (Finert Ψ) u (X u) ∧
        ContDiffAt ℝ 1 X u ∧ ∀ x : SeqV (Fin 2), ‖x‖ < ε → Solves (Finert Ψ) u x → x = X u :=
  local_determinacy (contDiffAt_Finert hΨc) (Finert_zero hΨ0)
    ((isUnit_linOp_inert_iff hΨ).mpr ⟨hφ, ha⟩) hη

/-- **Necessity for the exact inertial-rule model** (Woodford (2003), Prop. 2.8, p. 96, and
App. A.3): the exact model is locally determinate with a solution map differentiable at the
steady state **iff** `φ_π ≠ 0` and `|φ_π + ρ| > 1`. When the condition fails, either local
uniqueness fails or no equilibrium selection is differentiable in the disturbances. -/
theorem inertial_iff {Ψ : ℝ × ℝ → ℝ} {φ ρ : ℝ} (hΨc : ContDiffAt ℝ 1 Ψ 0) (hΨ0 : Ψ 0 = 0)
    (hΨ : HasFDerivAt Ψ (ruleD φ ρ) 0) :
    (φ ≠ 0 ∧ 1 < |φ + ρ|) ↔ ∃ ε > 0, ∃ δ > 0, ∃ X : Par (Fin 2) (Fin 2 → ℝ) → SeqV (Fin 2),
      X 0 = 0 ∧ DifferentiableAt ℝ X 0 ∧ ∀ u : Par (Fin 2) (Fin 2 → ℝ), ‖u‖ < δ →
        Solves (Finert Ψ) u (X u) ∧
          ∀ x : SeqV (Fin 2), ‖x‖ < ε → Solves (Finert Ψ) u x → x = X u := by
  rw [← isUnit_linOp_inert_iff hΨ]
  refine isUnit_linOp_iff_local_determinacy (contDiffAt_Finert hΨc) (Finert_zero hΨ0) ?_
  intro y
  exact ⟨-y, by rw [dE_Finert hΨ, neg_neg]⟩

/-- **The printed root count fails for the book's own model** (Woodford (2003), eq. (A.9),
p. 632, and (2.12), p. 96): for the inertial system `f₃` is singular and
`det(f₃λ² + f₂λ + f₁) = λ²(φ_π + ρ − λ)` has at most one root outside the unit circle, so "two
inside and two outside" never holds — even when the model is determinate. Counting the infinite
root as outside (`LinearSystems.outside_add_infinite`) restores the count. -/
theorem inert_book_count_fails (φ ρ : ℝ) :
    inF3.det = 0 ∧ ¬ BookRootCount (inF1 ρ) (inF2 φ) inF3 := by
  refine ⟨by simp [inF3, Matrix.det_fin_two], ?_⟩
  rintro ⟨-, h2⟩
  rw [roots_inert, Multiset.filter_add, Multiset.filter_nsmul, Multiset.filter_singleton,
    Multiset.filter_singleton] at h2
  have hn : ¬ (1 : ℝ) < ‖(0 : ℂ)‖ := by simp
  simp only [hn, ↓reduceIte] at h2
  split_ifs at h2 <;> norm_num at h2

/-- Woodford (2003), App. A.3, p. 633, with E18, for the inertial model: if the rule is `C²`
near the steady state (and the determinacy condition holds), the exact equilibrium differs from
the log-linear solution by `O(‖(î_{−1}, r̂, ν)‖²)`. -/
theorem inertial_second_order {Ψ : ℝ × ℝ → ℝ} {φ ρ : ℝ} (hΨc : ContDiffAt ℝ 2 Ψ 0)
    (hΨ0 : Ψ 0 = 0) (hΨ : HasFDerivAt Ψ (ruleD φ ρ) 0) (hφ : φ ≠ 0) (ha : 1 < |φ + ρ|)
    {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ε ≤ η ∧ ∃ δ > 0, δ ≤ η ∧ ∃ C : ℝ, ∀ u : Par (Fin 2) (Fin 2 → ℝ), ‖u‖ < δ →
      ∀ x : SeqV (Fin 2), ‖x‖ < ε → Solves (Finert Ψ) u x →
        ‖x - linSol (Finert Ψ) u‖ ≤ C * ‖u‖ ^ 2 :=
  second_order_loc (contDiffAt_Finert hΨc) (Finert_zero hΨ0)
    ((isUnit_linOp_inert_iff hΨ).mpr ⟨hφ, ha⟩) hη

/-! ### The scalar forward-looking theory `LocalIFT` is the case `n = 1` -/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Woodford (2003), App. A.3, eq. (A.7), p. 631: a scalar condition `F₀(x_t, x_{t+1}, e_t) = 0`
(the class of `LocalIFT`) as an `n = 1` condition `F(x_{t−1}, x_t, x_{t+1}, e_t) = 0` that does
not depend on `x_{t−1}`. -/
def embedF (F₀ : ℝ × ℝ × E → ℝ) (p : Arg (Fin 1) E) : Fin 1 → ℝ :=
  fun _ => F₀ (p.2.1 0, p.2.2.1 0, p.2.2.2)

/-- Woodford (2003), App. A.3, p. 631 (tool): the scalar argument `(x_t, x_{t+1}, e_t)`. -/
noncomputable def scalarArg : Arg (Fin 1) E →L[ℝ] ℝ × ℝ × E :=
  ((ContinuousLinearMap.proj 0).comp ((ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) ((Fin 1 → ℝ) × E)).comp
      (ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) ((Fin 1 → ℝ) × (Fin 1 → ℝ) × E)))).prod
    (((ContinuousLinearMap.proj 0).comp ((ContinuousLinearMap.fst ℝ (Fin 1 → ℝ) E).comp
      ((ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) ((Fin 1 → ℝ) × E)).comp
        (ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) ((Fin 1 → ℝ) × (Fin 1 → ℝ) × E))))).prod
      ((ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) E).comp
        ((ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) ((Fin 1 → ℝ) × E)).comp
          (ContinuousLinearMap.snd ℝ (Fin 1 → ℝ) ((Fin 1 → ℝ) × (Fin 1 → ℝ) × E)))))

/-- Woodford (2003), App. A.3, p. 631 (tool): the embedding `ℝ → ℝ¹`. -/
noncomputable def constEmb : ℝ →L[ℝ] (Fin 1 → ℝ) :=
  ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ ℝ

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 631 (tool): `embedF F₀ = ι ∘ F₀ ∘ π`. -/
theorem embedF_eq (F₀ : ℝ × ℝ × E → ℝ) : embedF F₀ = fun p => constEmb (F₀ (scalarArg p)) :=
  rfl

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 632: the derivative of the embedded condition. -/
theorem fderiv_embedF_apply {F₀ : ℝ × ℝ × E → ℝ} (hF : DifferentiableAt ℝ F₀ 0)
    (p : Arg (Fin 1) E) :
    fderiv ℝ (embedF F₀) 0 p = fun _ => LocalIFT.slopeA F₀ * p.2.1 0 +
      LocalIFT.slopeB F₀ * p.2.2.1 0 + LocalIFT.slopeC F₀ p.2.2.2 := by
  have h0 : scalarArg (0 : Arg (Fin 1) E) = 0 := map_zero _
  have hF' : HasFDerivAt F₀ (fderiv ℝ F₀ 0) (scalarArg (0 : Arg (Fin 1) E)) := by
    rw [h0]; exact hF.hasFDerivAt
  have h := constEmb.hasFDerivAt.comp 0 (hF'.comp 0 (scalarArg (E := E)).hasFDerivAt)
  rw [embedF_eq, show (fun p => constEmb (F₀ (scalarArg p))) =
    ⇑constEmb ∘ F₀ ∘ ⇑(scalarArg (E := E)) from rfl, h.fderiv]
  funext i
  simp only [ContinuousLinearMap.comp_apply]
  rw [show scalarArg p = (p.2.1 0, p.2.2.1 0, p.2.2.2) from rfl, LocalIFT.fderiv_zero_apply3]
  rfl

/-- Woodford (2003), App. A.3, p. 632 (tool): the scalar sequence of an `ℓ∞(ℕ, ℝ¹)` element. -/
noncomputable def toLinf : SeqV (Fin 1) →L[ℝ] LocalIFT.Linf :=
  LinearMap.mkContinuous
    { toFun := fun y => LocalIFT.mk (fun t => y t 0) ⟨‖y‖, fun t => by
        rw [← Real.norm_eq_abs]
        exact (norm_le_pi_norm (y t) 0).trans (LocalIFT.norm_seq_apply_le y t)⟩
      map_add' := fun y z => by ext t; rfl
      map_smul' := fun c y => by ext t; rfl }
    1 (fun y => by
      rw [one_mul]
      refine LocalIFT.norm_le_of_abs_le (norm_nonneg _) fun t => ?_
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm (y t) 0).trans (LocalIFT.norm_seq_apply_le y t))

/-- Woodford (2003), App. A.3, p. 632 (tool): a scalar bounded sequence as an element of
`ℓ∞(ℕ, ℝ¹)`. -/
noncomputable def ofLinf : LocalIFT.Linf →L[ℝ] SeqV (Fin 1) :=
  LinearMap.mkContinuous
    { toFun := fun x => LocalIFT.mkS (fun t _ => x t) ⟨‖x‖, fun t => by
        rw [pi_norm_const, Real.norm_eq_abs]
        exact LocalIFT.abs_apply_le x t⟩
      map_add' := fun x z => seq_ext fun t => rfl
      map_smul' := fun c x => seq_ext fun t => rfl }
    1 (fun x => by
      rw [one_mul]
      refine LocalIFT.norm_seq_le (norm_nonneg _) fun t => ?_
      change ‖(fun _ : Fin 1 => x t)‖ ≤ ‖x‖
      rw [pi_norm_const, Real.norm_eq_abs]
      exact LocalIFT.abs_apply_le x t)

/-- Woodford (2003), App. A.3, p. 632 (tool): coordinates of `ofLinf`. -/
@[simp] theorem ofLinf_apply (x : LocalIFT.Linf) (t : ℕ) (i : Fin 1) : ofLinf x t i = x t := rfl

/-- Woodford (2003), App. A.3, p. 632 (tool): coordinates of `toLinf`. -/
@[simp] theorem toLinf_apply (y : SeqV (Fin 1)) (t : ℕ) : toLinf y t = y t 0 := rfl

/-- Woodford (2003), App. A.3, p. 632 (tool): `toLinf ∘ ofLinf = id`. -/
theorem toLinf_ofLinf (x : LocalIFT.Linf) : toLinf (ofLinf x) = x := by
  ext t
  rfl

/-- Woodford (2003), App. A.3, p. 632 (tool): `ofLinf ∘ toLinf = id`. -/
theorem ofLinf_toLinf (y : SeqV (Fin 1)) : ofLinf (toLinf y) = y := by
  refine seq_ext fun t => funext fun i => ?_
  rw [Subsingleton.elim i 0]
  rfl

/-- Woodford (2003), App. A.3, p. 632 (tool): the identification preserves norms (one way). -/
theorem norm_ofLinf_le (x : LocalIFT.Linf) : ‖ofLinf x‖ ≤ ‖x‖ :=
  (ofLinf.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _)
    (LinearMap.mkContinuous_norm_le _ zero_le_one _))

/-- Woodford (2003), App. A.3, p. 632 (tool): the identification preserves norms (other way). -/
theorem norm_toLinf_le (y : SeqV (Fin 1)) : ‖toLinf y‖ ≤ ‖y‖ :=
  (toLinf.le_opNorm y).trans (mul_le_of_le_one_left (norm_nonneg _)
    (LinearMap.mkContinuous_norm_le _ zero_le_one _))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, eq. (A.7), p. 631: the embedded `n = 1` conditions have the same
solutions as the scalar conditions of `LocalIFT`, whatever the (irrelevant) initial
condition. -/
theorem solves_embedF_iff (F₀ : ℝ × ℝ × E → ℝ) (u : Par (Fin 1) E) (x : LocalIFT.Linf) :
    Solves (embedF F₀) u (ofLinf x) ↔ LocalIFT.Solves F₀ u.2 x := by
  refine forall_congr' fun t => ?_
  constructor
  · intro h
    exact congrFun h 0
  · intro h
    funext i
    exact h

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: the linearised operator of the embedded system
is the scalar operator `a + bS` of `LocalIFT` (`a = ∂F₀/∂x_t`, `b = ∂F₀/∂x_{t+1}`). -/
theorem linOp_embedF {F₀ : ℝ × ℝ × E → ℝ} (hF : DifferentiableAt ℝ F₀ 0) (y : SeqV (Fin 1)) :
    linOp (embedF F₀) y =
      ofLinf (LocalIFT.TOp (LocalIFT.slopeA F₀) (LocalIFT.slopeB F₀) (toLinf y)) := by
  refine seq_ext fun t => funext fun i => ?_
  rw [linOp_apply]
  simp only [d1, d2, d3, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, fderiv_embedF_apply hF, Pi.add_apply, ofLinf_apply,
    LocalIFT.TOp_apply, toLinf_apply]
  simp

omit [FiniteDimensional ℝ E] in
/-- **The scalar invertibility criterion is the case `n = 1`** (Woodford (2003), eq. (A.9),
p. 632): for an embedded scalar condition, (A.8) is invertible iff `|∂F₀/∂x_{t+1}| <
|∂F₀/∂x_t|` — the criterion `LocalIFT.isUnit_TOp_iff`. -/
theorem isUnit_linOp_embedF_iff {F₀ : ℝ × ℝ × E → ℝ} (hF : DifferentiableAt ℝ F₀ 0) :
    IsUnit (linOp (embedF F₀)) ↔ |LocalIFT.slopeB F₀| < |LocalIFT.slopeA F₀| := by
  rw [← LocalIFT.isUnit_TOp_iff, ContinuousLinearMap.isUnit_iff_bijective,
    ContinuousLinearMap.isUnit_iff_bijective]
  set T := LocalIFT.TOp (LocalIFT.slopeA F₀) (LocalIFT.slopeB F₀) with hT
  have he : ⇑(linOp (embedF F₀)) = ⇑ofLinf ∘ ⇑T ∘ ⇑toLinf := funext (linOp_embedF hF)
  have hof : Function.Bijective ofLinf :=
    ⟨Function.LeftInverse.injective toLinf_ofLinf,
      Function.RightInverse.surjective ofLinf_toLinf⟩
  have hto : Function.Bijective toLinf :=
    ⟨Function.LeftInverse.injective ofLinf_toLinf,
      Function.RightInverse.surjective toLinf_ofLinf⟩
  rw [he]
  constructor
  · intro h
    have e : ⇑T = ⇑toLinf ∘ (⇑ofLinf ∘ ⇑T ∘ ⇑toLinf) ∘ ⇑ofLinf := by
      funext x
      simp [toLinf_ofLinf]
    rw [e]
    exact hto.comp (h.comp hof)
  · intro h
    exact hof.comp (h.comp hto)

omit [FiniteDimensional ℝ E] in
/-- **The general root condition reduces to the scalar one** (Woodford (2003), eq. (A.9),
p. 632): for an embedded scalar condition the exact root condition of `LocalIFTSystems` (on
`det(f₃λ² + f₂λ + f₁) = λ(bλ + a)`) holds iff `|b| < |a|`. -/
theorem rootCondition_embedF_iff {F₀ : ℝ × ℝ × E → ℝ} (hF : DifferentiableAt ℝ F₀ 0) :
    (quadPoly (M1 (embedF F₀)) (M2 (embedF F₀)) (M3 (embedF F₀)) ≠ 0 ∧
      (∀ μ ∈ ((quadPoly (M1 (embedF F₀)) (M2 (embedF F₀)) (M3 (embedF F₀))).map
        Complex.ofRealHom).roots, ‖μ‖ ≠ 1) ∧
      Multiset.card (((quadPoly (M1 (embedF F₀)) (M2 (embedF F₀)) (M3 (embedF F₀))).map
        Complex.ofRealHom).roots.filter (fun μ => ‖μ‖ < 1)) = Fintype.card (Fin 1) ∧
      HomInjective (M1 (embedF F₀)) (M2 (embedF F₀)) (M3 (embedF F₀))) ↔
      |LocalIFT.slopeB F₀| < |LocalIFT.slopeA F₀| := by
  rw [← isUnit_linOp_iff, isUnit_linOp_embedF_iff hF]

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, eq. (A.10), p. 633: the solution of the linearised embedded system
is the scalar forward sum `LocalIFT.linSol3` (for any initial condition). -/
theorem linSol_embedF {F₀ : ℝ × ℝ × E → ℝ} (hF : DifferentiableAt ℝ F₀ 0)
    (hab : |LocalIFT.slopeB F₀| < |LocalIFT.slopeA F₀|) (u : Par (Fin 1) E) :
    linSol (embedF F₀) u = ofLinf (LocalIFT.linSol3 F₀ u.2) := by
  have hL := (isUnit_linOp_embedF_iff hF).mpr hab
  refine (eq_linSol hL fun t => funext fun i => ?_).symm
  simp only [d1, d2, d3, dE, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, fderiv_embedF_apply hF, Pi.add_apply, ofLinf_apply,
    Pi.zero_apply]
  have := LocalIFT.linSol3_solves hab u.2 t
  simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, mul_zero, map_zero, add_zero,
    zero_add]
  linarith

/-- **`LocalIFT.local_determinacy_loc` recovered as the case `n = 1`** (Woodford (2003),
App. A.3, pp. 632–633): the scalar local determinacy theorem — existence, local uniqueness, `C¹`
dependence and first-order term `LocalIFT.linSol3` — follows from the `n`-dimensional
`LocalIFTSystems.local_determinacy` applied to the embedded condition (using from `LocalIFT`
only its linear facts `isUnit_TOp_iff` and `linSol3_solves`). -/
theorem scalar_local_determinacy_recovered {F₀ : ℝ × ℝ × E → ℝ} (hF : ContDiffAt ℝ 1 F₀ 0)
    (h0 : F₀ 0 = 0) (hab : |LocalIFT.slopeB F₀| < |LocalIFT.slopeA F₀|) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ε ≤ η ∧ ∃ δ > 0, δ ≤ η ∧ ∃ X : LocalIFT.Seq E → LocalIFT.Linf, X 0 = 0 ∧
      HasFDerivAt X (LocalIFT.linSol3 F₀) 0 ∧
      ∀ e : LocalIFT.Seq E, ‖e‖ < δ → ‖X e‖ < ε / 2 ∧ LocalIFT.Solves F₀ e (X e) ∧
        ContDiffAt ℝ 1 X e ∧ ∀ x : LocalIFT.Linf, ‖x‖ < ε → LocalIFT.Solves F₀ e x → x = X e := by
  have hd : DifferentiableAt ℝ F₀ 0 := hF.differentiableAt one_ne_zero
  have hc : ContDiffAt ℝ 1 (embedF F₀) 0 := by
    have h0' : scalarArg (0 : Arg (Fin 1) E) = 0 := map_zero _
    have hF' : ContDiffAt ℝ 1 F₀ (scalarArg (0 : Arg (Fin 1) E)) := by rw [h0']; exact hF
    rw [embedF_eq]
    exact constEmb.contDiff.contDiffAt.comp 0
      (hF'.comp 0 (scalarArg (E := E)).contDiff.contDiffAt)
  have he0 : embedF F₀ 0 = 0 := by
    funext i
    simp only [embedF, Pi.zero_apply]
    exact h0
  obtain ⟨ε, hε, hεη, δ, hδ, hδη, X, hX0, hXd, hX⟩ :=
    local_determinacy hc he0 ((isUnit_linOp_embedF_iff hd).mpr hab) hη
  set inj : LocalIFT.Seq E →L[ℝ] Par (Fin 1) E :=
    ContinuousLinearMap.inr ℝ (Fin 1 → ℝ) (LocalIFT.Seq E) with hinj
  have hnorm : ∀ e : LocalIFT.Seq E, ‖inj e‖ = ‖e‖ := fun e => by
    rw [hinj, ContinuousLinearMap.inr_apply, Prod.norm_mk, norm_zero,
      max_eq_right (norm_nonneg _)]
  refine ⟨ε, hε, hεη, δ, hδ, hδη, fun e => toLinf (X (inj e)), ?_, ?_, fun e he => ?_⟩
  · simp only [map_zero, hX0]
  · have h := toLinf.hasFDerivAt.comp (0 : LocalIFT.Seq E)
      ((by rw [map_zero]; exact hXd : HasFDerivAt X (linSol (embedF F₀)) (inj 0)).comp
        (0 : LocalIFT.Seq E) inj.hasFDerivAt)
    refine h.congr_fderiv (ContinuousLinearMap.ext fun e => ?_)
    simp only [ContinuousLinearMap.comp_apply]
    rw [linSol_embedF hd hab, toLinf_ofLinf]
    rfl
  · have he' : ‖inj e‖ < δ := by rw [hnorm]; exact he
    obtain ⟨hXn, hXs, hXc, hXu⟩ := hX (inj e) he'
    refine ⟨(norm_toLinf_le _).trans_lt hXn, ?_, ?_, fun x hx hsol => ?_⟩
    · have := (solves_embedF_iff F₀ (inj e) (toLinf (X (inj e)))).mp
        (by rw [ofLinf_toLinf]; exact hXs)
      exact this
    · exact toLinf.contDiff.contDiffAt.comp e (hXc.comp e inj.contDiff.contDiffAt)
    · have h1 := hXu (ofLinf x) ((norm_ofLinf_le x).trans_lt hx)
        ((solves_embedF_iff F₀ (inj e) x).mpr hsol)
      change x = toLinf (X (inj e))
      rw [← h1, toLinf_ofLinf]


/-! ### E18 in `n` dimensions: `C¹` gives only `o(‖u‖)` -/

/-- Woodford (2003), App. A.3, p. 633, erratum E18 (counterexample data): the scalar `C¹` (not
`C²`) condition `F₀(x, x', ν) = 2x + ν + ν^{3/2} − x'` of `LocalIFT.gE`. -/
noncomputable def F0g (p : ℝ × ℝ × ℝ) : ℝ := LocalIFT.gE (p.1, p.2.2) - p.2.1

/-- Woodford (2003), App. A.3, erratum E18: the derivative of `F0g` at the steady state,
`(x, x', ν) ↦ 2x − x' + ν`. -/
theorem hasFDerivAt_F0g : HasFDerivAt F0g
    (((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ +
      (0 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))) -
      (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) 0 := by
  set L : ℝ × ℝ × ℝ →L[ℝ] ℝ × ℝ := (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) with hL
  have h0 : L 0 = 0 := map_zero _
  have hg : HasFDerivAt LocalIFT.gE ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ContinuousLinearMap.snd ℝ ℝ ℝ + (0 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) (L 0) := by
    rw [h0]; exact LocalIFT.hasFDerivAt_gE
  exact (hg.comp 0 L.hasFDerivAt).sub
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt

/-- Woodford (2003), App. A.3, erratum E18: the slopes of the counterexample, `a = 2`, `b = −1`,
`c = 1`. -/
theorem slopes_F0g : LocalIFT.slopeA F0g = 2 ∧ LocalIFT.slopeB F0g = -1 ∧
    ∀ v : ℝ, LocalIFT.slopeC F0g v = v := by
  obtain ⟨h1, h2, h3⟩ := LocalIFT.slopes_of_hasFDerivAt hasFDerivAt_F0g
  refine ⟨by rw [h1]; simp, by rw [h2]; simp, fun v => by rw [h3]; simp⟩

/-- **E18 in `n` dimensions: the `O(‖u‖²)` claim fails for a `C¹` condition** (Woodford (2003),
App. A.3, p. 633): the embedded `C¹` condition `2x_t + ν_t + ν_t^{3/2} − x_{t+1} = 0` is
determinate (`|b| = 1 < 2 = |a|`), but no bound `‖x − x̂‖ ≤ C ‖(x_{−1}, ν)‖²` holds near the
steady state (along `ν_t ≡ η²` the error is `η³`); `second_order_loc` needs `C²`, and for `C¹`
only `first_order_loc` (`o(‖u‖)`) holds. -/
theorem not_second_order_C1 :
    ContDiff ℝ 1 (embedF F0g) ∧ embedF F0g 0 = 0 ∧ IsUnit (linOp (embedF F0g)) ∧
      ¬ ∃ ε > 0, ∃ δ > 0, ∃ C : ℝ, ∀ u : Par (Fin 1) ℝ, ‖u‖ < δ → ∀ x : SeqV (Fin 1),
        ‖x‖ < ε → Solves (embedF F0g) u x → ‖x - linSol (embedF F0g) u‖ ≤ C * ‖u‖ ^ 2 := by
  obtain ⟨ha, hb, hc⟩ := slopes_F0g
  have hd : DifferentiableAt ℝ F0g 0 := hasFDerivAt_F0g.differentiableAt
  have hab : |LocalIFT.slopeB F0g| < |LocalIFT.slopeA F0g| := by rw [ha, hb]; norm_num
  have hL := (isUnit_linOp_embedF_iff hd).mpr hab
  have hcd : ContDiff ℝ 1 F0g :=
    (LocalIFT.contDiff_gE.comp (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd))).sub
      (contDiff_fst.comp contDiff_snd)
  refine ⟨?_, ?_, hL, ?_⟩
  · rw [embedF_eq]
    exact constEmb.contDiff.comp (hcd.comp (scalarArg (E := ℝ)).contDiff)
  · funext i
    simp [embedF, F0g, LocalIFT.gE]
  rintro ⟨ε, hε, δ, hδ, C, hC⟩
  set η : ℝ := min (1 / 2) (min (δ / 2) (min (ε / 4) (1 / (2 * (|C| + 1))))) with hηdef
  have hCp : 0 < |C| + 1 := by positivity
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 / 2 := min_le_left _ _
  have hηδ : η ≤ δ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηε : η ≤ ε / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηC : η ≤ 1 / (2 * (|C| + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  set ξ : ℝ := η ^ 2 with hξ
  have hξ0 : 0 ≤ ξ := by positivity
  set u : Par (Fin 1) ℝ := (0, LocalIFT.const ξ) with hu
  set c : ℝ := -(ξ + η ^ 3) with hcdef
  set x : SeqV (Fin 1) := ofLinf (LocalIFT.const c) with hx
  -- the exact equilibrium
  have hsol : Solves (embedF F0g) u x := by
    refine (solves_embedF_iff F0g u (LocalIFT.const c)).mpr fun t => ?_
    simp only [F0g, LocalIFT.gE, LocalIFT.const_apply, hu]
    rw [LocalIFT.sq_rpow_three_halves hη0.le]
    rw [hcdef]
    ring
  -- the log-linear solution
  have hlin : linSol (embedF F0g) u = ofLinf (LocalIFT.const (-ξ)) := by
    rw [linSol_embedF hd hab]
    congr 1
    refine (LocalIFT.eq_linSol3 hab fun t => ?_).symm
    rw [ha, hb, hc]
    simp [hu]
    ring
  have hnu : ‖u‖ ≤ ξ := by
    refine norm_prod_le_iff.mpr ⟨by rw [norm_zero]; exact hξ0, ?_⟩
    exact LocalIFT.norm_le_of_abs_le hξ0 fun t => by rw [hu]; simp [abs_of_nonneg hξ0]
  have hnx : ‖x‖ < ε := by
    refine (norm_ofLinf_le _).trans_lt ?_
    refine (LocalIFT.norm_le_of_abs_le (abs_nonneg c) fun t => le_rfl).trans_lt ?_
    have h3 : η ^ 3 ≤ η ^ 2 := pow_le_pow_of_le_one hη0.le (by linarith) (by norm_num)
    have h2 : η ^ 2 ≤ η := by nlinarith
    rw [hcdef, abs_neg, abs_of_nonneg (by positivity)]
    linarith
  have hnδ : ‖u‖ < δ := by
    refine hnu.trans_lt ?_
    have h2 : η ^ 2 ≤ η := by nlinarith
    rw [hξ]
    linarith
  have key := hC u hnδ x hnx hsol
  rw [hlin] at key
  have hlow : η ^ 3 ≤ ‖x - ofLinf (LocalIFT.const (-ξ))‖ := by
    have h := (norm_le_pi_norm ((x - ofLinf (LocalIFT.const (-ξ))) 0) 0).trans
      (LocalIFT.norm_seq_apply_le (x - ofLinf (LocalIFT.const (-ξ))) 0)
    have e : (x - ofLinf (LocalIFT.const (-ξ))) 0 0 = -η ^ 3 := by
      simp only [hx, lp.coeFn_sub, Pi.sub_apply, ofLinf_apply, LocalIFT.const_apply, hcdef]
      ring
    rw [e, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)] at h
    exact h
  have hup : C * ‖u‖ ^ 2 ≤ |C| * η ^ 4 := by
    have h1 : ‖u‖ ^ 2 ≤ ξ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnu 2
    calc C * ‖u‖ ^ 2 ≤ |C| * ‖u‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * ξ ^ 2 := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
      _ = |C| * η ^ 4 := by rw [hξ]; ring
  have hfin : η ^ 3 ≤ |C| * η ^ 4 := (hlow.trans key).trans hup
  have hηC' : η * (|C| + 1) ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (|C| + 1))] at hηC
    nlinarith
  have h3pos : 0 < η ^ 3 := by positivity
  have : 1 ≤ |C| * η := by
    have h' : η ^ 3 * 1 ≤ η ^ 3 * (|C| * η) := by nlinarith
    exact le_of_mul_le_mul_left h' h3pos
  nlinarith [abs_nonneg C]

end Woodford.PriceLevelDetermination.LocalIFTSystemsApps
