/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.MoneyRuleRoots
import BasicNewKeynesianModel.GeneralBK

/-!
# Determinacy under an exogenous money supply

Galí (2015), Chapter 3, §3.4.2, p. 75 and fn. 14: "the equilibrium is always determined under an
exogenous path for the money supply". This module proves it in the strong sense of the general
Blanchard–Kahn theorem (`GeneralBK`, restated from the Woodford Chapter 4 project): for every
bounded adapted path of the shocks `s_t = (r̂ⁿ_t, ŷⁿ_t, Δm_t)`, every initial real balance
`l̂_{−1}` and any `ExpectationSystem`, system (34),
`A_{M,0} x_t = A_{M,1} E_t x_{t+1} + B_M s_t` with `l̂_{t−1}` predetermined, has exactly one
bounded adapted solution.

## The state-space form

The state is `x_t = (ỹ_t, π_t; l̂_{t−1})`, indexed by `Fin 2 ⊕ Fin 1` (two non-predetermined
variables, one predetermined).

* `η > 0`: `A_{M,1}` is invertible (`det A_{M,1} = σηβ`), and (34) is
  `E_t x_{t+1} = A_b x_t − A_{M,1}⁻¹ B_M s_t` with `A_b = A_{M,1}⁻¹ A_{M,0} = A_M⁻¹`
  (`Ab3_eq_inv_AM`). Its characteristic polynomial is `(X − r⁻¹)(X² + (q₁/q₀) X + 1/q₀)`
  (`charpoly_Ab3_factor`): one eigenvalue `1/r ∈ (0, 1)` and two outside the closed unit disc
  (`Ab3_root_location`). Genericity holds because the stable eigenvector has a non-zero
  real-balance component (`Abk_genericX`).
* `η = 0` (allowed by Galí, Ch. 2, p. 21): `A_{M,1}` is singular (one infinite generalised
  eigenvalue). The first row of (34) is then static, `ỹ_t = l̂_t − ŷⁿ_t`, and the system reduces
  exactly to `(π_t; l̂_{t−1})` with `E_t (π_{t+1}, l̂_t) = B (π_t, l̂_{t−1}) + w_t`,
  `B = [[(1+κ)/β, −κ/β], [−1, 1]]`, whose eigenvalues are `ρ₁ ∈ (0,1)` and `1/(βρ₁) > 1`.

## Main results

* `Abk_determinate`, `B2_determinate`: the Blanchard–Kahn conditions hold, so the state-space
  systems are determinate for EVERY bounded adapted forcing vector.
* `system34_existsUnique`: for `σ > 0`, `η ≥ 0`, `κ > 0`, `0 < β ≤ 1` and bounded adapted shocks,
  (34) has exactly one bounded adapted equilibrium with predetermined real balances starting at
  any given `l̂_{−1}` — for every `ExpectationSystem`.
* `model_existsUnique`: for `η > 0`, the same for the model equations themselves — the NKPC (22),
  the DIS (23), money demand (31) and the identity (33) — with the nominal rate included.
-/

namespace Gali.BasicNewKeynesianModel.MoneyRuleDeterminacy

open Polynomial MoneyRule MoneyRuleRoots InvariantSplit GeneralBKForward GeneralBK
open scoped Matrix

/-! ### Tools -/

/-- Galí (2015), p. 75 (tool): the eigenvalues are invariant under a relabelling of the state. -/
theorem eigs_submatrix_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (M : Matrix κ κ ℝ) : eigs (M.submatrix e e) = eigs M := by
  unfold eigs
  rw [show (M.submatrix e e).map Complex.ofReal = Matrix.reindex e.symm e.symm
    (M.map Complex.ofReal) from rfl, Matrix.charpoly_reindex]

/-- Galí (2015), p. 75 (tool): if the stable count is one and a real eigenvector of a stable
eigenvalue has a non-zero predetermined component, the genericity condition holds (the stable
subspace is the line through that eigenvector). -/
theorem genericX_of_eigvec {Z X : Type*} [Fintype Z] [Fintype X] [DecidableEq Z]
    [DecidableEq X] {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} (hnu : NoUnit A) (hs : stableCount A = 1)
    {ρ : ℝ} (hρ : |ρ| < 1) {e : Z ⊕ X → ℝ} (he : A *ᵥ e = ρ • e) {j : X}
    (hej : e (Sum.inr j) ≠ 0) : GenericX A := by
  have he0 : e ≠ 0 := fun h => hej (by rw [h]; rfl)
  have hmem : e ∈ boundedOrbits A := by
    refine ⟨∑ k, |e k|, fun t i => ?_⟩
    rw [pow_mulVec_eigvec he t, Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
    calc |ρ| ^ t * |e i| ≤ 1 * |e i| :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (abs_nonneg _) hρ.le) (abs_nonneg _)
      _ = |e i| := one_mul _
      _ ≤ ∑ k, |e k| :=
          Finset.single_le_sum (f := fun k => |e k|) (fun k _ => abs_nonneg _)
            (Finset.mem_univ i)
  have hspan : Submodule.span ℝ {e} = boundedOrbits A := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hmem
    · rw [finrank_span_singleton he0, finrank_eq_stableCount hnu, hs]
  intro v hv hvx
  rw [← hspan, Submodule.mem_span_singleton] at hv
  obtain ⟨c, rfl⟩ := hv
  have h := hvx j
  rw [Pi.smul_apply, smul_eq_mul, mul_eq_zero] at h
  rcases h with h | h
  · rw [h, zero_smul]
  · exact absurd h hej

/-- Galí (2015), p. 75 (tool): the roots of `X² + (q₁/q₀) X + 1/q₀` are the reciprocals of the
roots of `X² + q₁ X + q₀`, so they lie OUTSIDE the closed unit disc when the latter satisfies the
Schur–Cohn conditions. -/
theorem norm_gt_one_of_recip {q₁ q₀ : ℝ} (hS : SchurStable (-q₁) q₀) (hq0 : q₀ ≠ 0) {μ : ℂ}
    (h : μ ∈ ((quadPoly (q₁ / q₀) q₀⁻¹).map Complex.ofRealHom).roots) : 1 < ‖μ‖ := by
  have h1 := quadPoly_root h
  have hq0c : (q₀ : ℂ) ≠ 0 := by exact_mod_cast hq0
  have hμ : μ ≠ 0 := by
    rintro rfl
    have : ((q₀⁻¹ : ℝ) : ℂ) = 0 := by simpa using h1
    exact hq0 (by exact_mod_cast inv_eq_zero.mp (by exact_mod_cast this))
  have h2 : (q₀ : ℂ) * μ ^ 2 + q₁ * μ + 1 = 0 := by
    have e : (q₀ : ℂ) * (μ ^ 2 + ((q₁ / q₀ : ℝ) : ℂ) * μ + ((q₀⁻¹ : ℝ) : ℂ)) =
        q₀ * μ ^ 2 + q₁ * μ + 1 := by
      push_cast
      field_simp
    rw [← e, h1, mul_zero]
  set ν := μ⁻¹ with hν
  have hνμ : ν * μ = 1 := inv_mul_cancel₀ hμ
  have h3 : ν ^ 2 + q₁ * ν + q₀ = 0 := by
    linear_combination ν ^ 2 * h2 - ((q₁ : ℂ) * ν + q₀ * (1 + ν * μ)) * hνμ
  have hn := norm_lt_one_of_quadratic hS.1 (by have := hS.2; rwa [abs_neg] at this) h3
  have hν0 : ν ≠ 0 := inv_ne_zero hμ
  have hμν : μ = ν⁻¹ := by rw [hν, inv_inv]
  rw [hμν, norm_inv]
  exact (one_lt_inv₀ (norm_pos_iff.mpr hν0)).mpr hn

/-! ### `η > 0`: the backward matrix `A_b = A_{M,1}⁻¹ A_{M,0}` -/

/-- Galí (2015), eq. (34), p. 75: with `A_{M,1}` invertible, (34) reads
`E_t x_{t+1} = A_b x_t − A_{M,1}⁻¹ B_M s_t` with `A_b = A_{M,1}⁻¹ A_{M,0}`. -/
noncomputable def Ab3 (σ η β κ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (AM1 σ η β)⁻¹ * AM0 σ η κ

/-- Galí (2015), p. 75: `A_{M,1}` is invertible iff `σηβ ≠ 0`; in particular for `η > 0`. -/
theorem isUnit_det_AM1 {σ η β : ℝ} (hσ : σ ≠ 0) (hη : η ≠ 0) (hβ : β ≠ 0) :
    IsUnit (AM1 σ η β).det := by
  rw [det_AM1]
  exact (mul_ne_zero (mul_ne_zero hσ hη) hβ).isUnit

/-- Galí (2015), p. 75: `A_{M,0}` is invertible whenever `1 + ση ≠ 0`. -/
theorem isUnit_det_AM0 {σ η κ : ℝ} (hb : 1 + σ * η ≠ 0) : IsUnit (AM0 σ η κ).det := by
  rw [det_AM0]
  exact hb.isUnit

/-- Galí (2015), p. 75: the backward matrix is the inverse of `A_M = A_{M,0}⁻¹ A_{M,1}`, so its
eigenvalues are the reciprocals of those of `A_M`. -/
theorem Ab3_eq_inv_AM {σ η β κ : ℝ} (hb : 1 + σ * η ≠ 0) :
    Ab3 σ η β κ = (AM σ η β κ)⁻¹ := by
  rw [AM, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_AM0 hb), Ab3]

/-- Galí (2015), p. 75: `det(z A_{M,1} − A_{M,0}) = σηβ z³ + c₁ z² + c₂ z − (1+ση)`, the
reversed characteristic cubic `z³ f(1/z)`. -/
theorem det_pencil (σ η β κ z : ℝ) :
    (z • AM1 σ η β - AM0 σ η κ).det =
      σ * η * β * z ^ 3 + coef1 σ η β κ * z ^ 2 + coef2 σ η β κ * z - (1 + σ * η) := by
  simp [Matrix.det_fin_three, AM0, AM1, coef1, coef2]
  ring

/-- Galí (2015), p. 75: with `f(r) = 0`,
`det(z A_{M,1} − A_{M,0}) = −(1+ση)(1 − r z)(1 + q₁ z + q₀ z²)`. -/
theorem det_pencil_factor {σ η β κ r : ℝ} (hb : 1 + σ * η ≠ 0) (hr : charCubic σ η β κ r = 0)
    (z : ℝ) : (z • AM1 σ η β - AM0 σ η κ).det =
      -(1 + σ * η) * (1 - r * z) * (1 + quadQ1 σ η β κ r * z + quadQ0 σ η β κ r * z ^ 2) := by
  have h1 := quadQ1_mul (κ := κ) (β := β) hb r
  have h0 := quadQ0_mul (κ := κ) (β := β) hb r
  rw [det_pencil]
  rw [charCubic_eq_coef] at hr
  linear_combination (z - r ^ 2 * z ^ 3) * h1 + (z ^ 2 - r * z ^ 3) * h0 + z ^ 3 * hr

/-- Galí (2015), p. 75: `det A_{M,1} · det(z − A_b) = det(z A_{M,1} − A_{M,0})`. -/
theorem det_AM1_mul_charpoly_Ab3 {σ η β κ : ℝ} (hu : IsUnit (AM1 σ η β).det) (z : ℝ) :
    (AM1 σ η β).det * (Ab3 σ η β κ).charpoly.eval z = (z • AM1 σ η β - AM0 σ η κ).det := by
  rw [Matrix.eval_charpoly, ← Matrix.det_mul]
  congr 1
  rw [Matrix.mul_sub, Ab3, Matrix.mul_nonsing_inv_cancel_left _ _ hu, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

/-- Galí (2015), p. 75: for `σ, η, β ≠ 0`, `1 + ση ≠ 0` and a root `r` of the cubic, the
characteristic polynomial of `A_b` is `(X − r⁻¹)(X² + (q₁/q₀) X + q₀⁻¹)`. -/
theorem charpoly_Ab3_factor {σ η β κ r : ℝ} (hσ : σ ≠ 0) (hη : η ≠ 0) (hβ : β ≠ 0)
    (hb : 1 + σ * η ≠ 0) (hr : charCubic σ η β κ r = 0) :
    (Ab3 σ η β κ).charpoly = (X - C r⁻¹) *
      quadPoly (quadQ1 σ η β κ r / quadQ0 σ η β κ r) (quadQ0 σ η β κ r)⁻¹ := by
  have hu := isUnit_det_AM1 hσ hη hβ
  obtain ⟨hv0, -, -⟩ := quad_values hb hr
  have hsηβ : σ * η * β ≠ 0 := mul_ne_zero (mul_ne_zero hσ hη) hβ
  have hr0 : r ≠ 0 := by rintro rfl; apply hsηβ; rw [← hv0]; ring
  have hq0 : quadQ0 σ η β κ r ≠ 0 := by rintro h; apply hsηβ; rw [← hv0, h]; ring
  refine Polynomial.funext fun z => ?_
  have e := det_AM1_mul_charpoly_Ab3 (κ := κ) hu z
  rw [det_pencil_factor hb hr, det_AM1, ← hv0] at e
  have hden : (1 + σ * η) * r * quadQ0 σ η β κ r ≠ 0 := by rw [hv0]; exact hsηβ
  simp only [quadPoly, eval_mul, eval_sub, eval_X, eval_C, eval_add, eval_pow]
  have key : (1 + σ * η) * r * quadQ0 σ η β κ r * ((z - r⁻¹) * (z ^ 2 +
      quadQ1 σ η β κ r / quadQ0 σ η β κ r * z + (quadQ0 σ η β κ r)⁻¹)) =
      -(1 + σ * η) * (1 - r * z) * (1 + quadQ1 σ η β κ r * z + quadQ0 σ η β κ r * z ^ 2) := by
    field_simp
    ring
  exact mul_left_cancel₀ hden (e.trans key.symm)

/-- Galí (2015), p. 75, fn. 14 (backward form, `η > 0`): for `σ, η, β > 0`, `κ > 0`, `β ≤ 1`,
`A_b = A_M⁻¹` has exactly one eigenvalue in the open unit disc (namely `1/r`), two outside the
closed disc and none on the unit circle (with algebraic multiplicity over `ℂ`). -/
theorem Ab3_root_location {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) :
    NoUnit (Ab3 σ η β κ) ∧ stableCount (Ab3 σ η β κ) = 1 ∧ unstableCount (Ab3 σ η β κ) = 2 := by
  obtain ⟨r, hr1, hr⟩ := exists_root_gt_one hσ.le hη.le hκ hβ0.le hβ1
  have hb : 1 + σ * η ≠ 0 := by have := mul_pos hσ hη; linarith
  obtain ⟨hS, -⟩ := quad_schurStable hσ.le hη.le hκ hβ0.le hβ1 hr1 hr
  obtain ⟨hv0, -, -⟩ := quad_values hb hr
  have hq0 : quadQ0 σ η β κ r ≠ 0 := by
    intro h
    rw [h, mul_zero] at hv0
    have := mul_pos (mul_pos hσ hη) hβ0
    linarith
  set R := ((quadPoly (quadQ1 σ η β κ r / quadQ0 σ η β κ r)
    (quadQ0 σ η β κ r)⁻¹).map Complex.ofRealHom).roots with hRdef
  have hRout : ∀ μ ∈ R, 1 < ‖μ‖ := fun μ hμ => norm_gt_one_of_recip hS hq0 hμ
  have he : eigs (Ab3 σ η β κ) = {((r⁻¹ : ℝ) : ℂ)} + R := by
    have hne : ((Ab3 σ η β κ).charpoly.map Complex.ofRealHom) ≠ 0 :=
      ((Matrix.charpoly_monic _).map _).ne_zero
    rw [eigs, charpoly_map_ofReal]
    rw [charpoly_Ab3_factor hσ.ne' hη.ne' hβ0.ne' hb hr, Polynomial.map_mul] at hne ⊢
    rw [roots_mul hne, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, roots_X_sub_C]
    rfl
  have hr0 : 0 < r := by linarith
  have hrlt : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr1
  have hra : |r⁻¹| = r⁻¹ := abs_of_pos (inv_pos.mpr hr0)
  have hcard : Multiset.card R = 2 := by
    have h3 := card_eigs (Ab3 σ η β κ)
    rw [he, Multiset.card_add, Multiset.card_singleton, Fintype.card_fin] at h3
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro μ hμ
    rw [he, Multiset.mem_add, Multiset.mem_singleton] at hμ
    rcases hμ with rfl | hμ
    · rw [Complex.norm_real, Real.norm_eq_abs, hra]; exact hrlt.ne
    · exact (hRout μ hμ).ne'
  · rw [stableCount, he, Multiset.filter_add,
      Multiset.filter_eq_nil.mpr (fun μ hμ => not_lt.mpr (hRout μ hμ).le), add_zero,
      Multiset.filter_singleton]
    simp [abs_of_pos hr0, hrlt]
  · rw [unstableCount, he, Multiset.filter_add, Multiset.filter_eq_self.mpr hRout,
      Multiset.filter_singleton]
    simp [abs_of_pos hr0, hrlt.le, hcard]

/-- Galí (2015), p. 75: the relabelling of `Fin 3` as `Fin 2 ⊕ Fin 1`: `ỹ_t, π_t`
non-predetermined (`Sum.inl 0`, `Sum.inl 1`), `l̂_{t−1}` predetermined (`Sum.inr 0`). -/
abbrev eS : Fin 2 ⊕ Fin 1 ≃ Fin 3 := finSumFinEquiv

/-- Galí (2015), eq. (34), p. 75: the backward matrix on the split state `Fin 2 ⊕ Fin 1`. -/
noncomputable def Abk (σ η β κ : ℝ) : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ :=
  (Ab3 σ η β κ).submatrix eS eS

/-- Galí (2015), p. 75: a real eigenvector of the pencil for the root `r`:
`A_{M,1} v = r A_{M,0} v` with `v = ((r − β)(r − 1), rκ(r − 1), r²κ)`. -/
def eigv3 (β κ r : ℝ) : Fin 3 → ℝ := ![(r - β) * (r - 1), r * κ * (r - 1), r ^ 2 * κ]

/-- Galí (2015), p. 75: `A_{M,1} v = r A_{M,0} v` when `f(r) = 0`. -/
theorem pencil_eigvec {σ η β κ r : ℝ} (hr : charCubic σ η β κ r = 0) :
    AM1 σ η β *ᵥ eigv3 β κ r = r • (AM0 σ η κ *ᵥ eigv3 β κ r) := by
  unfold charCubic at hr
  funext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, eigv3]
    linear_combination hr
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, eigv3]
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, eigv3]
    ring

/-- Galí (2015), p. 75: `A_b v = r⁻¹ v` (the stable eigenvector of the backward matrix). -/
theorem Ab3_eigvec {σ η β κ r : ℝ} (hu : IsUnit (AM1 σ η β).det) (hr0 : r ≠ 0)
    (hr : charCubic σ η β κ r = 0) : Ab3 σ η β κ *ᵥ eigv3 β κ r = r⁻¹ • eigv3 β κ r := by
  have h := pencil_eigvec (σ := σ) (η := η) hr
  have h0 : AM0 σ η κ *ᵥ eigv3 β κ r = r⁻¹ • (AM1 σ η β *ᵥ eigv3 β κ r) := by
    rw [h, smul_smul, inv_mul_cancel₀ hr0, one_smul]
  rw [Ab3, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

/-- Galí (2015), p. 75: the eigenvalues of the split backward matrix are those of `A_b`. -/
theorem eigs_Abk (σ η β κ : ℝ) : eigs (Abk σ η β κ) = eigs (Ab3 σ η β κ) :=
  eigs_submatrix_equiv eS _

/-- Galí (2015), p. 75, fn. 14 (`η > 0`): the Blanchard–Kahn conditions for (34): no eigenvalue
of the backward matrix on the unit circle, exactly one (= the number of predetermined variables)
in the open unit disc, and genericity (the stable eigenvector moves real balances). -/
theorem Abk_bk_conditions {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) :
    NoUnit (Abk σ η β κ) ∧ stableCount (Abk σ η β κ) = Fintype.card (Fin 1) ∧
      GenericX (Abk σ η β κ) := by
  obtain ⟨hnu, hs, -⟩ := Ab3_root_location hσ hη hκ hβ0 hβ1
  have hnu' : NoUnit (Abk σ η β κ) := by unfold NoUnit; rw [eigs_Abk]; exact hnu
  have hs' : stableCount (Abk σ η β κ) = 1 := by unfold stableCount; rw [eigs_Abk]; exact hs
  refine ⟨hnu', hs', ?_⟩
  obtain ⟨r, hr1, hr⟩ := exists_root_gt_one hσ.le hη.le hκ hβ0.le hβ1
  have hr0 : 0 < r := by linarith
  have hu := isUnit_det_AM1 hσ.ne' hη.ne' hβ0.ne'
  have hev : Abk σ η β κ *ᵥ (eigv3 β κ r ∘ eS) = r⁻¹ • (eigv3 β κ r ∘ eS) := by
    rw [Abk, Matrix.submatrix_mulVec_equiv, Function.comp_assoc, Equiv.self_comp_symm,
      Function.comp_id, Ab3_eigvec hu hr0.ne' hr]
    rfl
  refine genericX_of_eigvec hnu' hs' (ρ := r⁻¹) ?_ hev (j := 0) ?_
  · rw [abs_of_pos (inv_pos.mpr hr0)]; exact inv_lt_one_of_one_lt₀ hr1
  · change r ^ 2 * κ ≠ 0
    positivity

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- **Galí (2015), p. 75, fn. 14 (`η > 0`)**: the backward form of (34) is determinate, in the
strong Blanchard–Kahn sense: for EVERY bounded adapted forcing vector and every initial real
balance there is exactly one bounded equilibrium, for any expectation system. -/
theorem Abk_determinate {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) : Determinate 𝔼 (Abk σ η β κ) := by
  obtain ⟨hnu, hs, hg⟩ := Abk_bk_conditions hσ hη hκ hβ0 hβ1
  exact determinate_of 𝔼 hnu (by rw [finrank_eq_stableCount hnu, hs]) hg

/-! ### `η > 0`: from the state-space form back to (34) -/

/-- Galí (2015), eq. (34), p. 75: the state `x_t = (ỹ_t, π_t; l̂_{t−1})` as a vector process on
the split index `Fin 2 ⊕ Fin 1`. -/
def yvec (ygap infl L : ℕ → Ω → ℝ) : ℕ → Fin 2 ⊕ Fin 1 → Ω → ℝ :=
  fun t k => ![ygap t, infl t, L t] (eS k)

/-- Galí (2015), eq. (34), p. 75: the shock vector `s_t = (r̂ⁿ_t, ŷⁿ_t, Δm_t)` as a vector
process. -/
def svec (rn yn dm : ℕ → Ω → ℝ) : ℕ → Fin 3 → Ω → ℝ := fun t => ![rn t, yn t, dm t]

/-- Galí (2015), eq. (34), p. 75: the forcing `−A_{M,1}⁻¹ B_M s_t` of the backward form. -/
noncomputable def wvec (σ η β : ℝ) (rn yn dm : ℕ → Ω → ℝ) : ℕ → Fin 2 ⊕ Fin 1 → Ω → ℝ :=
  fun t k => mv (-((AM1 σ η β)⁻¹ * BM η)) (svec rn yn dm t) (eS k)

omit 𝔼 in
/-- Galí (2015), p. 75 (tool): the state vector at an outcome, relabelled. -/
theorem yvec_apply (ygap infl L : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    (fun k => yvec ygap infl L t k ω) = stateVec ygap infl L t ω ∘ eS := by
  funext k
  simp only [Function.comp, yvec, stateVec]
  generalize eS k = i
  fin_cases i <;> rfl

/-- Galí (2015), p. 75 (tool): the forecast vector at an outcome, relabelled. -/
theorem E_yvec_apply (ygap infl L : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    (fun k => 𝔼.E t (yvec ygap infl L (t + 1) k) ω) = expVec 𝔼 ygap infl L t ω ∘ eS := by
  funext k
  simp only [Function.comp, yvec, expVec]
  generalize eS k = i
  fin_cases i <;> rfl

omit 𝔼 in
/-- Galí (2015), p. 75 (tool): the forcing at an outcome, relabelled. -/
theorem wvec_apply (σ η β : ℝ) (rn yn dm : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    (fun k => wvec σ η β rn yn dm t k ω) =
      ((-((AM1 σ η β)⁻¹ * BM η)) *ᵥ shockVec rn yn dm t ω) ∘ eS := by
  funext k
  simp only [Function.comp, wvec, mv_apply]
  congr 2
  funext j
  fin_cases j <;> rfl

omit 𝔼 in
/-- Galí (2015), p. 75 (tool): the split backward matrix acting on a state, relabelled. -/
theorem mv_Abk_apply (σ η β κ : ℝ) (a : Fin 2 ⊕ Fin 1 → Ω → ℝ) (ω : Ω) :
    (fun k => mv (Abk σ η β κ) a k ω) = (Ab3 σ η β κ *ᵥ ((fun k => a k ω) ∘ eS.symm)) ∘ eS := by
  funext k
  rw [mv_apply, Abk, Matrix.submatrix_mulVec_equiv]

/-- Galí (2015), eq. (34), p. 75: with `A_{M,1}` invertible,
`E = A_b x − A_{M,1}⁻¹ B_M s` iff `A_{M,0} x = A_{M,1} E + B_M s`. -/
theorem backward_iff {σ η β κ : ℝ} (hu : IsUnit (AM1 σ η β).det) (x Ex s : Fin 3 → ℝ) :
    Ex = Ab3 σ η β κ *ᵥ x + (-((AM1 σ η β)⁻¹ * BM η)) *ᵥ s ↔
      AM0 σ η κ *ᵥ x = AM1 σ η β *ᵥ Ex + BM η *ᵥ s := by
  constructor
  · rintro rfl
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Ab3,
      Matrix.mul_nonsing_inv_cancel_left _ _ hu, Matrix.mul_neg,
      Matrix.mul_nonsing_inv_cancel_left _ _ hu, Matrix.neg_mulVec]
    abel
  · intro h
    have hE : Ex = (AM1 σ η β)⁻¹ *ᵥ (AM1 σ η β *ᵥ Ex) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
    have h1 : AM1 σ η β *ᵥ Ex = AM0 σ η κ *ᵥ x - BM η *ᵥ s := by rw [h]; abel
    rw [hE, h1, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Ab3,
      Matrix.neg_mulVec, sub_eq_add_neg]

/-- Galí (2015), eq. (34), p. 75 (`η > 0`): the backward state-space system holds iff (34) holds. -/
theorem solves_Abk_iff {σ η β κ : ℝ} (hu : IsUnit (AM1 σ η β).det)
    {ygap infl L rn yn dm : ℕ → Ω → ℝ} :
    Solves 𝔼 (Abk σ η β κ) (wvec σ η β rn yn dm) (yvec ygap infl L) ↔
      System34 𝔼 σ η β κ ygap infl L rn yn dm := by
  have key : ∀ t ω, (∀ k, 𝔼.E t (yvec ygap infl L (t + 1) k) ω =
      mv (Abk σ η β κ) (yvec ygap infl L t) k ω + wvec σ η β rn yn dm t k ω) ↔
      (AM0 σ η κ).mulVec (stateVec ygap infl L t ω) =
        (AM1 σ η β).mulVec (expVec 𝔼 ygap infl L t ω) + (BM η).mulVec (shockVec rn yn dm t ω) := by
    intro t ω
    rw [← backward_iff hu]
    have hfun : (∀ k, 𝔼.E t (yvec ygap infl L (t + 1) k) ω =
        mv (Abk σ η β κ) (yvec ygap infl L t) k ω + wvec σ η β rn yn dm t k ω) ↔
        (fun k => 𝔼.E t (yvec ygap infl L (t + 1) k) ω) =
          (fun k => mv (Abk σ η β κ) (yvec ygap infl L t) k ω) +
            (fun k => wvec σ η β rn yn dm t k ω) :=
      ⟨fun h => funext h, fun h k => congrFun h k⟩
    rw [hfun, E_yvec_apply, mv_Abk_apply, wvec_apply, yvec_apply, Function.comp_assoc,
      Equiv.self_comp_symm, Function.comp_id, ← Pi.add_comp]
    exact eS.surjective.injective_comp_right.eq_iff
  constructor
  · intro h t ω
    exact (key t ω).mp fun k => congrFun (h t k) ω
  · intro h t k
    funext ω
    exact (key t ω).mpr (h t ω) k

/-- Galí (2015), eq. (34), p. 75: a bounded equilibrium of (34) with predetermined real balances
starting at `l̂_{−1} = L0`: (34) holds, `l̂_t` is known at `t`, all three variables are adapted
and bounded. -/
def Equil34 (σ η β κ L0 : ℝ) (rn yn dm ygap infl L : ℕ → Ω → ℝ) : Prop :=
  System34 𝔼 σ η β κ ygap infl L rn yn dm ∧ Predetermined 𝔼 L ∧ L 0 = (fun _ => L0) ∧
    𝔼.Adapted ygap ∧ 𝔼.Adapted infl ∧ 𝔼.Adapted L ∧
    BoundedProc ygap ∧ BoundedProc infl ∧ BoundedProc L

/-- Galí (2015), p. 75 (`η > 0`): equilibria of the backward state-space form are exactly the
bounded equilibria of (34). -/
theorem equil_Abk_iff {σ η β κ L0 : ℝ} (hu : IsUnit (AM1 σ η β).det)
    {ygap infl L rn yn dm : ℕ → Ω → ℝ} :
    Equil 𝔼 (Abk σ η β κ) (wvec σ η β rn yn dm) (fun _ => L0) (yvec ygap infl L) ↔
      Equil34 𝔼 σ η β κ L0 rn yn dm ygap infl L := by
  have hA : AdaptedV 𝔼 (yvec ygap infl L) ↔
      𝔼.Adapted ygap ∧ 𝔼.Adapted infl ∧ 𝔼.Adapted L := by
    constructor
    · intro h
      exact ⟨fun t => h t (Sum.inl 0), fun t => h t (Sum.inl 1), fun t => h t (Sum.inr 0)⟩
    · rintro ⟨h1, h2, h3⟩ t k
      rcases k with i | j
      · fin_cases i
        · exact h1 t
        · exact h2 t
      · fin_cases j
        exact h3 t
  have hK : (∀ t (j : Fin 1), 𝔼.E t (yvec ygap infl L (t + 1) (Sum.inr j)) =
      yvec ygap infl L (t + 1) (Sum.inr j)) ↔ Predetermined 𝔼 L := by
    constructor
    · intro h t
      exact h t 0
    · intro h t j
      fin_cases j
      exact h t
  have hI : (∀ j : Fin 1, yvec ygap infl L 0 (Sum.inr j) = fun _ => (fun _ => L0) j) ↔
      L 0 = fun _ => L0 := by
    constructor
    · intro h
      exact h 0
    · intro h j
      fin_cases j
      exact h
  have hB : BoundedV (yvec ygap infl L) ↔
      BoundedProc ygap ∧ BoundedProc infl ∧ BoundedProc L := by
    constructor
    · rintro ⟨M, hM⟩
      exact ⟨⟨M, fun t ω => hM t (Sum.inl 0) ω⟩, ⟨M, fun t ω => hM t (Sum.inl 1) ω⟩,
        ⟨M, fun t ω => hM t (Sum.inr 0) ω⟩⟩
    · rintro ⟨⟨M1, h1⟩, ⟨M2, h2⟩, ⟨M3, h3⟩⟩
      refine ⟨max M1 (max M2 M3), fun t k ω => ?_⟩
      rcases k with i | j
      · fin_cases i
        · exact (h1 t ω).trans (le_max_left _ _)
        · exact (h2 t ω).trans ((le_max_left _ _).trans (le_max_right _ _))
      · fin_cases j
        exact (h3 t ω).trans ((le_max_right _ _).trans (le_max_right _ _))
  unfold Equil Equil34
  rw [solves_Abk_iff 𝔼 hu, hA, hK, hI, hB]
  tauto

omit 𝔼 in
/-- Galí (2015), p. 75 (tool): bounded shocks give a bounded shock vector. -/
theorem svec_boundedV {rn yn dm : ℕ → Ω → ℝ} (h1 : BoundedProc rn) (h2 : BoundedProc yn)
    (h3 : BoundedProc dm) : BoundedV (svec rn yn dm) := by
  obtain ⟨M1, h1⟩ := h1
  obtain ⟨M2, h2⟩ := h2
  obtain ⟨M3, h3⟩ := h3
  refine ⟨max M1 (max M2 M3), fun t k ω => ?_⟩
  fin_cases k
  · exact (h1 t ω).trans (le_max_left _ _)
  · exact (h2 t ω).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h3 t ω).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- Galí (2015), p. 75 (tool): adapted shocks give an adapted shock vector. -/
theorem svec_adaptedV {rn yn dm : ℕ → Ω → ℝ} (h1 : 𝔼.Adapted rn) (h2 : 𝔼.Adapted yn)
    (h3 : 𝔼.Adapted dm) : AdaptedV 𝔼 (svec rn yn dm) := by
  intro t k
  fin_cases k
  · exact h1 t
  · exact h2 t
  · exact h3 t

/-- **Galí (2015), p. 75, fn. 14 (`η > 0`), PROVED**: for `σ, η, β > 0`, `κ > 0`, `β ≤ 1`, any
expectation system, bounded adapted shocks `r̂ⁿ, ŷⁿ, Δm` and any initial real balance
`l̂_{−1} = L0`, system (34) has exactly one bounded adapted equilibrium with predetermined real
balances. -/
theorem system34_existsUnique_pos {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) {rn yn dm : ℕ → Ω → ℝ} (hrnb : BoundedProc rn)
    (hynb : BoundedProc yn) (hdmb : BoundedProc dm) (hrna : 𝔼.Adapted rn)
    (hyna : 𝔼.Adapted yn) (hdma : 𝔼.Adapted dm) (L0 : ℝ) :
    ∃! v : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      Equil34 𝔼 σ η β κ L0 rn yn dm v.1 v.2.1 v.2.2 := by
  have hu := isUnit_det_AM1 hσ.ne' hη.ne' hβ0.ne'
  have hwb : BoundedV (wvec σ η β rn yn dm) := by
    obtain ⟨B, hB⟩ := boundedV_mv (-((AM1 σ η β)⁻¹ * BM η)) (svec_boundedV hrnb hynb hdmb)
    exact ⟨B, fun t k ω => hB t (eS k) ω⟩
  have hwa : AdaptedV 𝔼 (wvec σ η β rn yn dm) := fun t k =>
    adaptedV_mv 𝔼 (-((AM1 σ η β)⁻¹ * BM η)) (svec_adaptedV 𝔼 hrna hyna hdma) t (eS k)
  obtain ⟨y, hy, huniq⟩ := Abk_determinate 𝔼 hσ hη hκ hβ0 hβ1 _ hwb hwa (fun _ => L0)
  have hyv : yvec (fun t => y t (Sum.inl 0)) (fun t => y t (Sum.inl 1))
      (fun t => y t (Sum.inr 0)) = y := by
    funext t k
    rcases k with i | j
    · fin_cases i <;> rfl
    · fin_cases j; rfl
  refine ⟨(fun t => y t (Sum.inl 0), fun t => y t (Sum.inl 1), fun t => y t (Sum.inr 0)),
    ?_, ?_⟩
  · exact (equil_Abk_iff 𝔼 hu).mp (by rw [hyv]; exact hy)
  · rintro ⟨a, b, c⟩ hv
    have h := huniq _ ((equil_Abk_iff 𝔼 hu).mpr hv)
    rw [← h]
    rfl

/-! ### `η = 0`: the reduced two-variable system -/

/-- Galí (2015), eq. (34), p. 75 with `η = 0`: the backward matrix of the reduced system in
`(π_t; l̂_{t−1})`, `[[(1+κ)/β, −κ/β], [−1, 1]]`. -/
noncomputable def B2f (β κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![(1 + κ) / β, -κ / β; -1, 1]

/-- Galí (2015), p. 75: the relabelling of `Fin 2` as `Fin 1 ⊕ Fin 1` (`π_t` non-predetermined,
`l̂_{t−1}` predetermined). -/
abbrev eS2 : Fin 1 ⊕ Fin 1 ≃ Fin 2 := finSumFinEquiv

/-- Galí (2015), eq. (34), p. 75 with `η = 0`: the reduced backward matrix on `Fin 1 ⊕ Fin 1`. -/
noncomputable def B2 (β κ : ℝ) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ :=
  (B2f β κ).submatrix eS2 eS2

omit 𝔼 in
/-- Galí (2015), p. 75 (`η = 0`): the stable root `ρ₁ ∈ (0, 1)` of
`β ρ² − (1 + β + κ) ρ + 1 = 0` (IVT: the left side is `1` at `0` and `−κ` at `1`). -/
theorem exists_rho1 {β κ : ℝ} (hκ : 0 < κ) :
    ∃ ρ, 0 < ρ ∧ ρ < 1 ∧ β * ρ ^ 2 - (1 + β + κ) * ρ + 1 = 0 := by
  have hcont : ContinuousOn (fun z : ℝ => β * z ^ 2 - (1 + β + κ) * z + 1) (Set.Icc 0 1) := by
    fun_prop
  have hmem : (0 : ℝ) ∈ Set.Ioo ((fun z : ℝ => β * z ^ 2 - (1 + β + κ) * z + 1) 1)
      ((fun z : ℝ => β * z ^ 2 - (1 + β + κ) * z + 1) 0) := by
    simp only [Set.mem_Ioo]
    constructor <;> nlinarith
  obtain ⟨z, ⟨hz0, hz1⟩, hz⟩ := intermediate_value_Ioo' zero_le_one hcont hmem
  exact ⟨z, hz0, hz1, hz⟩

omit 𝔼 in
/-- Galí (2015), p. 75 (`η = 0`): the characteristic polynomial of the reduced matrix is
`(X − ρ₁)(X − 1/(βρ₁))`. -/
theorem charpoly_B2f {β κ ρ : ℝ} (hβ : β ≠ 0) (hρ0 : ρ ≠ 0)
    (hρ : β * ρ ^ 2 - (1 + β + κ) * ρ + 1 = 0) :
    (B2f β κ).charpoly = (X - C ρ) * (X - C (1 / (β * ρ))) := by
  refine Polynomial.funext fun z => ?_
  rw [Matrix.eval_charpoly, Matrix.det_fin_two]
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  simp [B2f, Matrix.scalar_apply]
  field_simp
  linear_combination z * hρ

omit 𝔼 in
/-- Galí (2015), p. 75 (`η = 0`): the reduced matrix has one eigenvalue `ρ₁ ∈ (0, 1)`, one
eigenvalue `1/(βρ₁) > 1`, none on the unit circle. -/
theorem B2f_root_location {β κ : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    NoUnit (B2f β κ) ∧ stableCount (B2f β κ) = 1 := by
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := exists_rho1 (β := β) hκ
  have hβρ : β * ρ < 1 := by nlinarith
  have hρ2 : 1 < 1 / (β * ρ) := one_lt_one_div (by positivity) hβρ
  have he : eigs (B2f β κ) = {(ρ : ℂ)} + {((1 / (β * ρ) : ℝ) : ℂ)} := by
    have hne : ((B2f β κ).charpoly.map Complex.ofRealHom) ≠ 0 :=
      ((Matrix.charpoly_monic _).map _).ne_zero
    rw [eigs, charpoly_map_ofReal]
    rw [charpoly_B2f hβ0.ne' hρ0.ne' hρ, Polynomial.map_mul] at hne ⊢
    rw [roots_mul hne, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, roots_X_sub_C,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, roots_X_sub_C]
    rfl
  have hn1 : ‖(ρ : ℂ)‖ = ρ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
  have hn2 : ‖((1 / (β * ρ) : ℝ) : ℂ)‖ = 1 / (β * ρ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  refine ⟨?_, ?_⟩
  · intro μ hμ
    rw [he, Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_singleton] at hμ
    rcases hμ with rfl | rfl
    · rw [hn1]; exact hρ1.ne
    · rw [hn2]; exact hρ2.ne'
  · have hlt2 : ¬ 1 / (β * ρ) < 1 := not_lt.mpr hρ2.le
    rw [stableCount, he, Multiset.filter_add, Multiset.filter_singleton,
      Multiset.filter_singleton]
    simp only [hn1, hn2, hρ1, hlt2, ↓reduceIte, Multiset.card_add, Multiset.card_singleton,
      Multiset.empty_eq_zero, Multiset.card_zero]

omit 𝔼 in
/-- Galí (2015), p. 75 (`η = 0`): the Blanchard–Kahn conditions for the reduced system: no
eigenvalue on the unit circle, exactly one in the open disc, genericity (the stable eigenvector
`(1 − ρ₁, 1)` moves real balances). -/
theorem B2_bk_conditions {β κ : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    NoUnit (B2 β κ) ∧ stableCount (B2 β κ) = Fintype.card (Fin 1) ∧ GenericX (B2 β κ) := by
  obtain ⟨hnu, hs⟩ := B2f_root_location hκ hβ0 hβ1
  have heq : eigs (B2 β κ) = eigs (B2f β κ) := eigs_submatrix_equiv eS2 _
  have hnu' : NoUnit (B2 β κ) := by unfold NoUnit; rw [heq]; exact hnu
  have hs' : stableCount (B2 β κ) = 1 := by unfold stableCount; rw [heq]; exact hs
  refine ⟨hnu', hs', ?_⟩
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := exists_rho1 (β := β) hκ
  have hv : B2f β κ *ᵥ ![1 - ρ, 1] = ρ • ![1 - ρ, 1] := by
    funext i
    fin_cases i
    · simp [B2f, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      field_simp
      linear_combination hρ
    · simp [B2f, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hev : B2 β κ *ᵥ (![1 - ρ, 1] ∘ eS2) = ρ • (![1 - ρ, 1] ∘ eS2) := by
    rw [B2, Matrix.submatrix_mulVec_equiv, Function.comp_assoc, Equiv.self_comp_symm,
      Function.comp_id, hv]
    rfl
  refine genericX_of_eigvec hnu' hs' (ρ := ρ) ?_ hev (j := 0) ?_
  · rw [abs_of_pos hρ0]; exact hρ1
  · change (1 : ℝ) ≠ 0
    exact one_ne_zero

/-- **Galí (2015), p. 75 (`η = 0`)**: the reduced backward system is determinate for every
bounded adapted forcing vector, for any expectation system. -/
theorem B2_determinate {β κ : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    Determinate 𝔼 (B2 β κ) := by
  obtain ⟨hnu, hs, hg⟩ := B2_bk_conditions hκ hβ0 hβ1
  exact determinate_of 𝔼 hnu (by rw [finrank_eq_stableCount hnu, hs]) hg

/-- Galí (2015), eq. (34), p. 75 (`η = 0`): the reduced state `(π_t; l̂_{t−1})`. -/
def y2 (infl L : ℕ → Ω → ℝ) : ℕ → Fin 1 ⊕ Fin 1 → Ω → ℝ := fun t k => ![infl t, L t] (eS2 k)

/-- Galí (2015), eq. (34), p. 75 (`η = 0`): the reduced forcing
`((κ/β)(ŷⁿ_t − Δm_t); Δm_t)`. -/
noncomputable def w2 (β κ : ℝ) (yn dm : ℕ → Ω → ℝ) : ℕ → Fin 1 ⊕ Fin 1 → Ω → ℝ :=
  fun t k => ![(κ / β) • (yn t - dm t), dm t] (eS2 k)

/-- Galí (2015), eq. (34), p. 75 (`η = 0`): the reduced system, written out:
`E_t π_{t+1} = ((1+κ)/β) π_t − (κ/β) l̂_{t−1} + (κ/β)(ŷⁿ_t − Δm_t)` and
`E_t l̂_t = −π_t + l̂_{t−1} + Δm_t`. -/
theorem solves_B2_iff {β κ : ℝ} {infl L yn dm : ℕ → Ω → ℝ} :
    Solves 𝔼 (B2 β κ) (w2 β κ yn dm) (y2 infl L) ↔
      (∀ t ω, 𝔼.E t (infl (t + 1)) ω = (1 + κ) / β * infl t ω + -κ / β * L t ω +
        κ / β * (yn t ω - dm t ω)) ∧
      (∀ t ω, 𝔼.E t (L (t + 1)) ω = -infl t ω + L t ω + dm t ω) := by
  have h0 : ∀ t ω, mv (B2 β κ) (y2 infl L t) (Sum.inl 0) ω =
      (1 + κ) / β * infl t ω + -κ / β * L t ω := by
    intro t ω
    rw [mv_apply_sum, Fintype.sum_sum_type]
    simp [B2, B2f, y2, show eS2 (Sum.inl 0) = 0 from rfl, show eS2 (Sum.inr 0) = 1 from rfl]
  have h1 : ∀ t ω, mv (B2 β κ) (y2 infl L t) (Sum.inr 0) ω = -infl t ω + L t ω := by
    intro t ω
    rw [mv_apply_sum, Fintype.sum_sum_type]
    simp [B2, B2f, y2, show eS2 (Sum.inl 0) = 0 from rfl, show eS2 (Sum.inr 0) = 1 from rfl]
  constructor
  · intro h
    refine ⟨fun t ω => ?_, fun t ω => ?_⟩
    · have := congrFun (h t (Sum.inl 0)) ω
      rw [Pi.add_apply, h0] at this
      exact this
    · have := congrFun (h t (Sum.inr 0)) ω
      rw [Pi.add_apply, h1] at this
      exact this
  · rintro ⟨ha, hb⟩ t k
    funext ω
    rcases k with i | j
    · fin_cases i
      rw [Pi.add_apply]
      have := h0 t ω
      simp only [Fin.zero_eta, Fin.isValue] at this ⊢
      rw [this]
      exact ha t ω
    · fin_cases j
      rw [Pi.add_apply]
      have := h1 t ω
      simp only [Fin.zero_eta, Fin.isValue] at this ⊢
      rw [this]
      exact hb t ω

/-- Galí (2015), eq. (34), p. 75 (`η = 0`): with predetermined real balances, (34) is the static
equation `ỹ_t = l̂_t − ŷⁿ_t` together with the reduced two-variable system. -/
theorem system34_zero_iff {σ β κ : ℝ} (hβ : β ≠ 0) {ygap infl L rn yn dm : ℕ → Ω → ℝ}
    (hL : Predetermined 𝔼 L) :
    System34 𝔼 σ 0 β κ ygap infl L rn yn dm ↔
      (∀ t, ygap t = L (t + 1) - yn t) ∧
      (∀ t ω, 𝔼.E t (infl (t + 1)) ω = (1 + κ) / β * infl t ω + -κ / β * L t ω +
        κ / β * (yn t ω - dm t ω)) ∧
      (∀ t ω, 𝔼.E t (L (t + 1)) ω = -infl t ω + L t ω + dm t ω) := by
  have e1 : ∀ x l s : ℝ, β * ((1 + κ) / β * x + -κ / β * l + κ / β * s) =
      (1 + κ) * x - κ * l + κ * s := by
    intro x l s
    field_simp
    ring
  constructor
  · intro h
    have hrow : ∀ t ω, ygap t ω = L (t + 1) ω - yn t ω ∧
        -κ * ygap t ω + infl t ω = β * 𝔼.E t (infl (t + 1)) ω ∧
        -infl t ω + L t ω = L (t + 1) ω - dm t ω := by
      intro t ω
      have h0 := congrFun (h t ω) 0
      have h1 := congrFun (h t ω) 1
      have h2 := congrFun (h t ω) 2
      have hLω := congrFun (hL t) ω
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec] at h0 h1 h2
      refine ⟨by linarith, by linarith, by linarith⟩
    refine ⟨fun t => funext fun ω => (hrow t ω).1, fun t ω => ?_, fun t ω => ?_⟩
    · obtain ⟨a, b, c⟩ := hrow t ω
      apply mul_left_cancel₀ hβ
      rw [e1]
      linear_combination -b - κ * a + κ * c
    · have hLω := congrFun (hL t) ω
      obtain ⟨-, -, c⟩ := hrow t ω
      linarith
  · rintro ⟨ha, hb, hc⟩ t ω
    have a := congrFun (ha t) ω
    have b := hb t ω
    have c := hc t ω
    have hLω := congrFun (hL t) ω
    have b' : β * 𝔼.E t (infl (t + 1)) ω =
        (1 + κ) * infl t ω - κ * L t ω + κ * (yn t ω - dm t ω) := by rw [b, e1]
    simp only [Pi.sub_apply] at a
    funext j
    fin_cases j
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec]
      linarith
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec]
      linear_combination (-κ) * a - b' + κ * hLω - κ * c
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec]
      linarith

/-- **Galí (2015), p. 75, fn. 14 (`η = 0`), PROVED**: with an interest-inelastic money demand
(`η = 0`, allowed in Galí, Ch. 2, p. 21), `κ > 0`, `0 < β ≤ 1`, any `σ`, any expectation system,
bounded adapted shocks and any initial real balance, (34) has exactly one bounded adapted
equilibrium with predetermined real balances (the natural rate `r̂ⁿ` does not enter). -/
theorem system34_existsUnique_zero {σ β κ : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {rn yn dm : ℕ → Ω → ℝ} (hynb : BoundedProc yn) (hdmb : BoundedProc dm)
    (hyna : 𝔼.Adapted yn) (hdma : 𝔼.Adapted dm) (L0 : ℝ) :
    ∃! v : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      Equil34 𝔼 σ 0 β κ L0 rn yn dm v.1 v.2.1 v.2.2 := by
  obtain ⟨My, hMy⟩ := hynb
  obtain ⟨Md, hMd⟩ := hdmb
  have hwb : BoundedV (w2 β κ yn dm) := by
    refine ⟨|κ / β| * (My + Md) + Md, fun t k ω => ?_⟩
    have hd0 : 0 ≤ Md := (abs_nonneg _).trans (hMd 0 ω)
    have hk : 0 ≤ |κ / β| * (My + Md) := by
      have : 0 ≤ My := (abs_nonneg _).trans (hMy 0 ω)
      positivity
    rcases k with i | j
    · fin_cases i
      change |(κ / β) * (yn t ω - dm t ω)| ≤ _
      rw [abs_mul]
      have : |yn t ω - dm t ω| ≤ My + Md :=
        (abs_sub _ _).trans (add_le_add (hMy t ω) (hMd t ω))
      nlinarith [abs_nonneg (κ / β)]
    · fin_cases j
      change |dm t ω| ≤ _
      linarith [hMd t ω]
  have hwa : AdaptedV 𝔼 (w2 β κ yn dm) := by
    intro t k
    rcases k with i | j
    · fin_cases i
      change 𝔼.E t ((κ / β) • (yn t - dm t)) = (κ / β) • (yn t - dm t)
      rw [map_smul, map_sub, hyna t, hdma t]
    · fin_cases j
      exact hdma t
  obtain ⟨y, ⟨hs, ha, hk, hi, hb⟩, huniq⟩ :=
    B2_determinate 𝔼 hκ hβ0 hβ1 (w2 β κ yn dm) hwb hwa (fun _ => L0)
  set infl : ℕ → Ω → ℝ := fun t => y t (Sum.inl 0) with hinfl
  set L : ℕ → Ω → ℝ := fun t => y t (Sum.inr 0) with hLdef
  have hyv : y2 infl L = y := by
    funext t k
    rcases k with i | j
    · fin_cases i; rfl
    · fin_cases j; rfl
  have hpred : Predetermined 𝔼 L := fun t => hk t 0
  rw [← hyv, solves_B2_iff] at hs
  refine ⟨(fun t => L (t + 1) - yn t, infl, L), ⟨?_, hpred, hi 0, ?_, fun t => ha t (Sum.inl 0),
    fun t => ha t (Sum.inr 0), ?_, ?_, ?_⟩, ?_⟩
  · exact (system34_zero_iff 𝔼 hβ0.ne' hpred).mpr ⟨fun t => rfl, hs.1, hs.2⟩
  · intro t
    change 𝔼.E t (L (t + 1) - yn t) = L (t + 1) - yn t
    rw [map_sub, hpred t, hyna t]
  · obtain ⟨M, hM⟩ := hb
    refine ⟨M + My, fun t ω => ?_⟩
    change |L (t + 1) ω - yn t ω| ≤ _
    exact (abs_sub _ _).trans (add_le_add (hM (t + 1) (Sum.inr 0) ω) (hMy t ω))
  · obtain ⟨M, hM⟩ := hb
    exact ⟨M, fun t ω => hM t (Sum.inl 0) ω⟩
  · obtain ⟨M, hM⟩ := hb
    exact ⟨M, fun t ω => hM t (Sum.inr 0) ω⟩
  · rintro ⟨g', i', L'⟩ ⟨hsys, hpred', hL0, -, hai, haL, -, hbi, hbL⟩
    obtain ⟨hg, ha', hb'⟩ := (system34_zero_iff 𝔼 hβ0.ne' hpred').mp hsys
    have heq : y2 i' L' = y := by
      refine huniq _ ⟨(solves_B2_iff 𝔼).mpr ⟨ha', hb'⟩, ?_, ?_, ?_, ?_⟩
      · intro t k
        rcases k with i | j
        · fin_cases i; exact hai t
        · fin_cases j; exact haL t
      · intro t j
        fin_cases j
        exact hpred' t
      · intro j
        fin_cases j
        exact hL0
      · obtain ⟨M1, h1⟩ := hbi
        obtain ⟨M2, h2⟩ := hbL
        refine ⟨max M1 M2, fun t k ω => ?_⟩
        rcases k with i | j
        · fin_cases i; exact (h1 t ω).trans (le_max_left _ _)
        · fin_cases j; exact (h2 t ω).trans (le_max_right _ _)
    have hi' : i' = infl := funext fun t => congrFun (congrFun heq t) (Sum.inl 0)
    have hL' : L' = L := funext fun t => congrFun (congrFun heq t) (Sum.inr 0)
    subst hi' hL'
    have hg' : g' = fun t => L (t + 1) - yn t := funext hg
    rw [hg']

/-- **Galí (2015), p. 75 and fn. 14, PROVED** ("the equilibrium is always determined under an
exogenous path for the money supply"): for `σ > 0`, `η ≥ 0`, `κ > 0`, `0 < β ≤ 1`, any
expectation system, bounded adapted shocks `r̂ⁿ, ŷⁿ, Δm` and any initial real balance
`l̂_{−1} = L0`, system (34) has exactly one bounded adapted equilibrium `(ỹ, π, l̂)` with real
balances predetermined. -/
theorem system34_existsUnique {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) {rn yn dm : ℕ → Ω → ℝ} (hrnb : BoundedProc rn)
    (hynb : BoundedProc yn) (hdmb : BoundedProc dm) (hrna : 𝔼.Adapted rn)
    (hyna : 𝔼.Adapted yn) (hdma : 𝔼.Adapted dm) (L0 : ℝ) :
    ∃! v : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      Equil34 𝔼 σ η β κ L0 rn yn dm v.1 v.2.1 v.2.2 := by
  rcases hη.lt_or_eq with h | h
  · exact system34_existsUnique_pos 𝔼 hσ h hκ hβ0 hβ1 hrnb hynb hdmb hrna hyna hdma L0
  · subst h
    exact system34_existsUnique_zero 𝔼 hκ hβ0 hβ1 hynb hdmb hyna hdma L0

/-- Galí (2015), §3.4.2: an equilibrium of the model under an exogenous money supply: the NKPC
(22), the DIS (23), the real-balance identity (33) and money demand (31), with predetermined real
balances starting at `l̂_{−1} = L0` and output gap, inflation, real balances and the nominal rate
all adapted and bounded. -/
def ModelEquil (σ η β κ L0 : ℝ) (rn yn dm ygap infl L i : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β κ infl ygap ∧ DIS 𝔼 σ ygap infl i rn ∧ RealBalanceId infl L dm ∧
    MoneyDemandGap η ygap i yn L ∧ Predetermined 𝔼 L ∧ L 0 = (fun _ => L0) ∧
    𝔼.Adapted ygap ∧ 𝔼.Adapted infl ∧ 𝔼.Adapted L ∧ 𝔼.Adapted i ∧
    BoundedProc ygap ∧ BoundedProc infl ∧ BoundedProc L ∧ BoundedProc i

/-- **Galí (2015), §3.4.2, pp. 74–75 and fn. 14: determinacy of the model, PROVED** (`η > 0`): for
`σ, η > 0`, `κ > 0`, `0 < β ≤ 1`, any expectation system, bounded adapted shocks and any initial
real balance, the model equations (22), (23), (31), (33) have exactly one bounded adapted
solution `(ỹ, π, l̂, i)` with predetermined real balances. -/
theorem model_existsUnique {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) {rn yn dm : ℕ → Ω → ℝ} (hrnb : BoundedProc rn)
    (hynb : BoundedProc yn) (hdmb : BoundedProc dm) (hrna : 𝔼.Adapted rn)
    (hyna : 𝔼.Adapted yn) (hdma : 𝔼.Adapted dm) (L0 : ℝ) :
    ∃! v : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      ModelEquil 𝔼 σ η β κ L0 rn yn dm v.1 v.2.1 v.2.2.1 v.2.2.2 := by
  obtain ⟨⟨g, p, L⟩, ⟨hsys, hpred, hL0, hag, hap, haL, hbg, hbp, hbL⟩, huniq⟩ :=
    system34_existsUnique_pos 𝔼 hσ hη hκ hβ0 hβ1 hrnb hynb hdmb hrna hyna hdma L0
  set i : ℕ → Ω → ℝ := fun t => η⁻¹ • (g t - L (t + 1) + yn t) with hidef
  have hMD : MoneyDemandGap η g i yn L := by
    intro t
    funext ω
    simp only [hidef, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  obtain ⟨hN, hD, hR⟩ := (model_iff_system34 𝔼 hσ.ne' hη.ne' hMD hpred).mpr hsys
  obtain ⟨My, hMy⟩ := hynb
  refine ⟨(g, p, L, i), ⟨hN, hD, hR, hMD, hpred, hL0, hag, hap, haL, ?_, hbg, hbp, hbL, ?_⟩, ?_⟩
  · intro t
    change 𝔼.E t (η⁻¹ • (g t - L (t + 1) + yn t)) = η⁻¹ • (g t - L (t + 1) + yn t)
    rw [map_smul, map_add, map_sub, hag t, hpred t, hyna t]
  · obtain ⟨Mg, hMg⟩ := hbg
    obtain ⟨ML, hML⟩ := hbL
    refine ⟨|η⁻¹| * (Mg + ML + My), fun t ω => ?_⟩
    change |η⁻¹ * (g t ω - L (t + 1) ω + yn t ω)| ≤ _
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc |g t ω - L (t + 1) ω + yn t ω| ≤ |g t ω - L (t + 1) ω| + |yn t ω| := abs_add_le _ _
      _ ≤ |g t ω| + |L (t + 1) ω| + |yn t ω| := by gcongr; exact abs_sub _ _
      _ ≤ Mg + ML + My := by gcongr <;> [exact hMg t ω; exact hML (t + 1) ω; exact hMy t ω]
  · rintro ⟨g', p', L', i'⟩ ⟨hN', hD', hR', hMD', hpred', hL0', hag', hap', haL', -, hbg', hbp',
      hbL', -⟩
    have hsys' := (model_iff_system34 𝔼 hσ.ne' hη.ne' hMD' hpred').mp ⟨hN', hD', hR'⟩
    have h3 := huniq (g', p', L') ⟨hsys', hpred', hL0', hag', hap', haL', hbg', hbp', hbL'⟩
    simp only [Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl, rfl⟩ := h3
    have hi' : i' = i := by
      funext t ω
      have e := congrFun (hMD' t) ω
      simp only [hidef, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
      field_simp
      linarith
    rw [hi']

end Gali.BasicNewKeynesianModel.MoneyRuleDeterminacy
