/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MonetaryPolicyDesign.Expectations
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# The money-supply system (34) of Chapter 3

Galí (2015), Chapter 3, §3.4.2, pp. 74–75, used in Chapter 4, Ex. 4.4(c), p. 123 (a money supply
rule). Restated from the Chapter 3 project (`BasicNewKeynesianModel.MoneyRule`, namespace renamed;
this project does not import across projects): the matrices `A_{M,0}`, `A_{M,1}`, `B_M` of (34),
the system itself with real balances `l̂_{t−1}` predetermined, the characteristic cubic
`f(z) = det(A_{M,1} − z A_{M,0})` and its basic properties, and the statement of the book's
determinacy claim (fn. 14), proved in `MoneyRuleRoots.bookDeterminacyClaim_holds`.
-/

namespace Gali.MonetaryPolicyDesign.MoneyRuleSystem

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), p. 75: real balances `l̂_{t−1}` are predetermined, so `l̂_t` is known at `t`. -/
def Predetermined (L : ℕ → Ω → ℝ) : Prop :=
  ∀ t, 𝔼.E t (L (t + 1)) = L (t + 1)

/-! ### The matrix form (34) -/

/-- Galí (2015), eq. (34), p. 75: the matrix `A_{M,0}`. -/
def AM0 (σ η κ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1 + σ * η, 0, 0; -κ, 1, 0; 0, -1, 1]

/-- Galí (2015), eq. (34), p. 75: the matrix `A_{M,1}`. -/
def AM1 (σ η β : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![σ * η, η, 1; 0, β, 0; 0, 0, 1]

/-- Galí (2015), eq. (34), p. 75: the matrix `B_M`. -/
def BM (η : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![η, -1, 0; 0, 0, 0; 0, 0, -1]

/-- Galí (2015), eq. (34), p. 75: the state `x_t = (ỹ_t, π_t, l̂_{t−1})`. -/
def stateVec (ygap infl L : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  ![ygap t ω, infl t ω, L t ω]

/-- Galí (2015), eq. (34), p. 75: the forecast
`E_t x_{t+1} = (E_t ỹ_{t+1}, E_t π_{t+1}, E_t l̂_t)`. -/
def expVec (ygap infl L : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  ![𝔼.E t (ygap (t + 1)) ω, 𝔼.E t (infl (t + 1)) ω, 𝔼.E t (L (t + 1)) ω]

omit 𝔼 in
/-- Galí (2015), eq. (34), p. 75: the shocks `(r̂^n_t, ŷ^n_t, Δm_t)`. -/
def shockVec (rn yn dm : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  ![rn t ω, yn t ω, dm t ω]

/-- Galí (2015), eq. (34), p. 75: `A_{M,0} x_t = A_{M,1} E_t x_{t+1} + B_M s_t` in every
state. -/
def System34 (σ η β κ : ℝ) (ygap infl L rn yn dm : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, (AM0 σ η κ).mulVec (stateVec ygap infl L t ω) =
    (AM1 σ η β).mulVec (expVec 𝔼 ygap infl L t ω) + (BM η).mulVec (shockVec rn yn dm t ω)

/-! ### Eigenvalues of `A_M` -/

/-- Galí (2015), p. 75 (survey §3.1): the characteristic cubic
`f(z) = det(A_{M,1} − z A_{M,0}) = (ση − z(1+ση))(β−z)(1−z) − ηκz(1−z) + κz²`. -/
def charCubic (σ η β κ z : ℝ) : ℝ :=
  (σ * η - z * (1 + σ * η)) * (β - z) * (1 - z) - η * κ * z * (1 - z) + κ * z ^ 2

/-- Galí (2015), p. 75: `det(A_{M,1} − z A_{M,0})` is the characteristic cubic (exact). -/
theorem det_AM1_sub_smul_AM0 (σ η β κ z : ℝ) :
    (AM1 σ η β - z • AM0 σ η κ).det = charCubic σ η β κ z := by
  simp [Matrix.det_fin_three, AM0, AM1, charCubic]
  ring

/-- Galí (2015), p. 75: `det A_{M,0} = 1 + ση`. -/
theorem det_AM0 (σ η κ : ℝ) : (AM0 σ η κ).det = 1 + σ * η := by
  simp [Matrix.det_fin_three, AM0]

/-- Galí (2015), p. 75: `det A_{M,1} = σηβ`. -/
theorem det_AM1 (σ η β : ℝ) : (AM1 σ η β).det = σ * η * β := by
  simp [Matrix.det_fin_three, AM1]

/-- Galí (2015), p. 75: the matrix `A_M ≡ A_{M,0}⁻¹ A_{M,1}`. -/
noncomputable def AM (σ η β κ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (AM0 σ η κ)⁻¹ * AM1 σ η β

/-- Galí (2015), p. 75: `det(A_M − z I) = (1+ση)⁻¹ f(z)` when `1 + ση ≠ 0`. -/
theorem det_AM_sub_smul {σ η β κ : ℝ} (h : 1 + σ * η ≠ 0) (z : ℝ) :
    (AM σ η β κ - z • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det =
      (1 + σ * η)⁻¹ * charCubic σ η β κ z := by
  have hu : IsUnit (AM0 σ η κ).det := by rw [det_AM0]; exact h.isUnit
  have hfac : AM σ η β κ - z • (1 : Matrix (Fin 3) (Fin 3) ℝ) =
      (AM0 σ η κ)⁻¹ * (AM1 σ η β - z • AM0 σ η κ) := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hu, AM]
  rw [hfac, Matrix.det_mul, Matrix.det_nonsing_inv, det_AM0, Ring.inverse_eq_inv',
    det_AM1_sub_smul_AM0]

/-- Galí (2015), p. 75: the characteristic polynomial of `A_M` evaluated at `z` is
`−(1+ση)⁻¹ f(z)`, so the eigenvalues of `A_M` are exactly the roots of `f`. -/
theorem charpoly_AM_eval {σ η β κ : ℝ} (h : 1 + σ * η ≠ 0) (z : ℝ) :
    (AM σ η β κ).charpoly.eval z = -((1 + σ * η)⁻¹ * charCubic σ η β κ z) := by
  rw [Matrix.eval_charpoly, ← det_AM_sub_smul h]
  have : Matrix.scalar (Fin 3) z - AM σ η β κ =
      -(AM σ η β κ - z • (1 : Matrix (Fin 3) (Fin 3) ℝ)) := by
    rw [neg_sub, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
  rw [this, Matrix.det_neg]
  simp only [Fintype.card_fin]
  ring

/-- Galí (2015), p. 75: a real `z` is an eigenvalue of `A_M` iff `f(z) = 0`. -/
theorem isRoot_charpoly_AM_iff {σ η β κ : ℝ} (h : 1 + σ * η ≠ 0) (z : ℝ) :
    (AM σ η β κ).charpoly.IsRoot z ↔ charCubic σ η β κ z = 0 := by
  rw [Polynomial.IsRoot.def, charpoly_AM_eval h, neg_eq_zero, mul_eq_zero]
  simp [inv_eq_zero, h]

/-- Galí (2015), p. 75: the cubic expanded; its leading coefficient is `−(1+ση)`. -/
theorem charCubic_expand (σ η β κ z : ℝ) :
    charCubic σ η β κ z = -(1 + σ * η) * z ^ 3 +
      (σ * η + (1 + σ * η) * (1 + β) + η * κ + κ) * z ^ 2 +
      (-(σ * η) * (1 + β) - (1 + σ * η) * β - η * κ) * z + σ * η * β := by
  unfold charCubic
  ring

/-- Galí (2015), p. 75: `f(0) = σηβ`. -/
theorem charCubic_zero (σ η β κ : ℝ) : charCubic σ η β κ 0 = σ * η * β := by
  unfold charCubic; ring

/-- Galí (2015), p. 75: `f(1) = κ`. -/
theorem charCubic_one (σ η β κ : ℝ) : charCubic σ η β κ 1 = κ := by
  unfold charCubic; ring

/-- Galí (2015), p. 75: `f(0) > 0` and `f(1) > 0` for `σ, η, β, κ > 0`, and the leading
coefficient `−(1+ση)` is negative. -/
theorem charCubic_signs {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hβ : 0 < β) (hκ : 0 < κ) :
    0 < charCubic σ η β κ 0 ∧ 0 < charCubic σ η β κ 1 ∧ -(1 + σ * η) < 0 := by
  rw [charCubic_zero, charCubic_one]
  refine ⟨by positivity, hκ, ?_⟩
  have : 0 < σ * η := mul_pos hσ hη
  linarith

/-- Galí (2015), p. 75: the cubic has a real root strictly greater than one (IVT between
`f(1) = κ > 0` and a point where `f < 0`). -/
theorem charCubic_root_gt_one {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hβ : 0 < β)
    (hκ : 0 < κ) : ∃ z, 1 < z ∧ charCubic σ η β κ z = 0 := by
  set b := 1 + σ * η with hb
  set c₂ := σ * η + b * (1 + β) + η * κ + κ with hc₂
  have hsη : 0 < σ * η := mul_pos hσ hη
  have hb0 : 0 < b := by linarith
  have hc₂0 : 0 < c₂ := by
    have : 0 < η * κ := mul_pos hη hκ
    nlinarith
  set R := 1 + c₂ / b with hR
  have hR1 : 1 < R := by have := div_pos hc₂0 hb0; linarith
  have hbR : b * R = b + c₂ := by rw [hR]; field_simp
  have hfR : charCubic σ η β κ R < 0 := by
    rw [charCubic_expand]
    have hηκ : 0 < η * κ := mul_pos hη hκ
    have hsηβ : 0 < σ * η * β := by positivity
    have hlead : -b * R ^ 3 + c₂ * R ^ 2 = -b * R ^ 2 := by
      have : -b * R ^ 3 + c₂ * R ^ 2 = R ^ 2 * (c₂ - b * R) := by ring
      rw [this, hbR]; ring
    have hc1 : (-(σ * η) * (1 + β) - b * β - η * κ) * R ≤
        -(σ * η) * (1 + β) - b * β - η * κ := by
      have hneg : -(σ * η) * (1 + β) - b * β - η * κ < 0 := by nlinarith
      nlinarith
    have hR2 : 1 < R ^ 2 := by nlinarith
    have hsum : -(σ * η) * (1 + β) - b * β - η * κ + σ * η * β < 0 := by nlinarith
    have hfin : -b * R ^ 2 < 0 := by nlinarith
    calc -(1 + σ * η) * R ^ 3 + (σ * η + (1 + σ * η) * (1 + β) + η * κ + κ) * R ^ 2 +
          (-(σ * η) * (1 + β) - (1 + σ * η) * β - η * κ) * R + σ * η * β
        = (-b * R ^ 3 + c₂ * R ^ 2) +
          (-(σ * η) * (1 + β) - b * β - η * κ) * R + σ * η * β := by
          rw [hb, hc₂]
      _ < 0 := by rw [hlead]; linarith
  have hcont : ContinuousOn (charCubic σ η β κ) (Set.Icc 1 R) := by
    unfold charCubic
    fun_prop
  have hmem : (0 : ℝ) ∈ Set.Ioo (charCubic σ η β κ R) (charCubic σ η β κ 1) := by
    rw [charCubic_one]
    exact ⟨hfR, hκ⟩
  obtain ⟨z, ⟨hz1, -⟩, hz⟩ := intermediate_value_Ioo' hR1.le hcont hmem
  exact ⟨z, hz1, hz⟩

/-- Galí (2015), p. 75: for `σ, η, β, κ > 0`, `A_M` has a real eigenvalue strictly
greater than one (so at least one eigenvalue lies outside the unit circle). -/
theorem AM_has_eigenvalue_gt_one {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hβ : 0 < β)
    (hκ : 0 < κ) : ∃ z, 1 < z ∧ (AM σ η β κ).charpoly.IsRoot z := by
  obtain ⟨z, hz1, hz⟩ := charCubic_root_gt_one hσ hη hβ hκ
  have h : 1 + σ * η ≠ 0 := by have := mul_pos hσ hη; linarith
  exact ⟨z, hz1, (isRoot_charpoly_AM_iff h z).mpr hz⟩

/-- Galí (2015), p. 75: `det A_M = σηβ/(1+ση)`, the product of the three eigenvalues. -/
theorem det_AM {σ η β κ : ℝ} (h : 1 + σ * η ≠ 0) :
    (AM σ η β κ).det = σ * η * β / (1 + σ * η) := by
  rw [AM, Matrix.det_mul, Matrix.det_nonsing_inv, det_AM0, Ring.inverse_eq_inv', det_AM1]
  field_simp

/-- Galí (2015), p. 75: for `σ, η > 0` and `0 < β < 1`, the product of the eigenvalues of
`A_M` lies in `(0, 1)`. -/
theorem det_AM_pos_lt_one {σ η β κ : ℝ} (hσ : 0 < σ) (hη : 0 < η) (hβ : 0 < β)
    (hβ1 : β < 1) : 0 < (AM σ η β κ).det ∧ (AM σ η β κ).det < 1 := by
  have hsη : 0 < σ * η := mul_pos hσ hη
  have hb : 0 < 1 + σ * η := by linarith
  rw [det_AM hb.ne']
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hb]
  nlinarith

/-- Galí (2015), p. 75 and fn. 14: the book's determinacy claim: the cubic factors as
`−(1+ση)(z − r)(z² + q₁ z + q₀)` with `r > 1` and both roots of the quadratic factor inside the
unit circle (Schur–Cohn). The book supports it numerically only; it is proved in
`MoneyRuleRoots.bookDeterminacyClaim_holds`. -/
def BookDeterminacyClaim (σ η β κ : ℝ) : Prop :=
  ∃ r q₁ q₀ : ℝ, 1 < r ∧
    (∀ z, charCubic σ η β κ z = -(1 + σ * η) * (z - r) * (z ^ 2 + q₁ * z + q₀)) ∧
    SchurStable (-q₁) q₀

end Gali.MonetaryPolicyDesign.MoneyRuleSystem
