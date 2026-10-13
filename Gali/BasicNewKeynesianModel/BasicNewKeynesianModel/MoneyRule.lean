/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.Expectations
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Equilibrium under an exogenous money supply

Galí (2015), Chapter 3, §3.4.2, pp. 73–79. With the money supply exogenous, the
money-demand equation (4) joins the NKPC (22) and the DIS (23):

* (31), p. 74: money demand in terms of the output gap, `l_t = ỹ_t − η i_t + y^n_t`;
* (32), p. 74: eliminating `i_t`,
  `(1 + ση) ỹ_t = ση E_t ỹ_{t+1} + l̂_t + η E_t π_{t+1} + η r̂^n_t − ŷ^n_t`;
* (33), p. 74: the real-balance identity `l̂_{t−1} = l̂_t + π_t − Δm_t`;
* (34), p. 75: the 3×3 system `A_{M,0} x_t = A_{M,1} E_t x_{t+1} + B_M s_t`;
* (35), p. 75: AR(1) money growth;
* p. 77: the interest-rate equation and its forward solution;
* p. 79: the money rule as a price-level rule.

## Conventions

All variables are deviations from steady state (constants dropped, as the book does
from (32) on). The predetermined variable `l̂_{t−1}` is the process `L t`, so `L (t + 1)`
is `l̂_t` and `L 0` is the initial condition `l̂_{−1}`. NKPC and DIS are stated here as
model equations with parameters (Galí (22), (23), p. 63).

## Main results

* `model_iff_system34`: the model equations ⇔ the matrix form (34).
* `det_AM1_sub_smul_AM0`: `det(A_{M,1} − z A_{M,0}) = (ση − z(1+ση))(β−z)(1−z) − ηκz(1−z) + κz²`.
* `charpoly_AM_eval`: the eigenvalues of `A_M = A_{M,0}⁻¹ A_{M,1}` are exactly the roots of
  that cubic.
* `charCubic_zero`, `charCubic_one`, `charCubic_expand`: `f(0) = σηβ > 0`, `f(1) = κ > 0`,
  leading coefficient `−(1+ση) < 0`.
* `AM_has_eigenvalue_gt_one`: `A_M` has a real eigenvalue strictly greater than one (IVT).
* `det_AM`, `det_AM_pos_lt_one`: the product of the eigenvalues is `σηβ/(1+ση) ∈ (0,1)`.
* `interest_rate_equation`: `i_t = η/(1+η) E_t i_{t+1} + ρ_m/(1+η) Δm_t + (σ−1)/(1+η) E_t Δy_{t+1}`.
* `interest_rate_forward_unique`, `interest_rate_forward_exists`: the forward solution is
  the unique bounded solution (genuine infinite sum).
* `interest_rate_log_utility`, `interest_rate_comoves`: `σ = 1 ⇒ i_t = ρ_m Δm_t/(1+η(1−ρ_m))`.
* `price_level_rule`: the p. 79 rewrite with `v_t = −η⁻¹ Δm_t`.

## Not yet claimed

The book's statement (p. 75, fn. 14) that `A_M` ALWAYS has two eigenvalues inside and one
outside the unit circle is supported in the book only numerically. Here it is recorded as
the proposition `BookDeterminacyClaim` and NOT proved: only the existence of one real
eigenvalue `> 1` and the product of the eigenvalues are proved.
-/

namespace Gali.BasicNewKeynesianModel.MoneyRule

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Model equations -/

/-- Galí (2015), eq. (22), p. 63: the New Keynesian Phillips curve
`π_t = β E_t π_{t+1} + κ ỹ_t`. -/
def NKPC (β κ : ℝ) (infl ygap : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t

/-- Galí (2015), eq. (23), p. 63 (deviations from steady state): the dynamic IS equation
`ỹ_t = −σ⁻¹(î_t − E_t π_{t+1} − r̂^n_t) + E_t ỹ_{t+1}`. -/
def DIS (σ : ℝ) (ygap infl i rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ygap t = -σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - rn t) + 𝔼.E t (ygap (t + 1))

/-- Galí (2015), eq. (31), p. 74 (deviations): money demand in terms of the output gap,
`l̂_t = ỹ_t − η î_t + ŷ^n_t`, with `l̂_t = L (t + 1)`. -/
def MoneyDemandGap (η : ℝ) (ygap i yn L : ℕ → Ω → ℝ) : Prop :=
  ∀ t, L (t + 1) = ygap t - η • i t + yn t

/-- Galí (2015), eq. (32), p. 74: the DIS with the interest rate eliminated,
`(1+ση) ỹ_t = ση E_t ỹ_{t+1} + l̂_t + η E_t π_{t+1} + η r̂^n_t − ŷ^n_t`. -/
def Eq32 (σ η : ℝ) (ygap infl L rn yn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (1 + σ * η) • ygap t = (σ * η) • 𝔼.E t (ygap (t + 1)) + L (t + 1) +
    η • 𝔼.E t (infl (t + 1)) + η • rn t - yn t

/-- Galí (2015), eq. (33), p. 74: the real-balance identity `l̂_{t−1} = l̂_t + π_t − Δm_t`. -/
def RealBalanceId (infl L dm : ℕ → Ω → ℝ) : Prop :=
  ∀ t, L t = L (t + 1) + infl t - dm t

/-- Galí (2015), p. 75: real balances `l̂_{t−1}` are predetermined, so `l̂_t` is known at `t`. -/
def Predetermined (L : ℕ → Ω → ℝ) : Prop :=
  ∀ t, 𝔼.E t (L (t + 1)) = L (t + 1)

omit 𝔼 in
/-- Galí (2015), eq. (31), p. 74: money demand (4), `m_t − p_t = y_t − η i_t`, with
`y_t = ỹ_t + y^n_t`, gives (31). -/
theorem eq31_of_money_demand (η : ℝ) {m p y ygap yn i L : ℕ → Ω → ℝ}
    (hMD : ∀ t, m t - p t = y t - η • i t) (hy : ∀ t, y t = ygap t + yn t)
    (hL : ∀ t, L (t + 1) = m t - p t) : MoneyDemandGap η ygap i yn L := by
  intro t
  rw [hL, hMD, hy]
  abel

omit 𝔼 in
/-- Galí (2015), eq. (33), p. 74: with `l_t = m_t − p_t`, `π_t = p_t − p_{t−1}` and
`Δm_t = m_t − m_{t−1}`, the real-balance identity holds at every date `t ≥ 1`. -/
theorem eq33_of_levels {m p L infl dm : ℕ → Ω → ℝ}
    (hL : ∀ t, L (t + 1) = m t - p t) (hp : ∀ t, infl (t + 1) = p (t + 1) - p t)
    (hm : ∀ t, dm (t + 1) = m (t + 1) - m t) (t : ℕ) :
    L (t + 1) = L (t + 1 + 1) + infl (t + 1) - dm (t + 1) := by
  rw [hL, hL, hp, hm]
  abel

/-- Galí (2015), eq. (32), p. 74: given money demand (31), the DIS (23) is equivalent to
(32) (for `σ ≠ 0`, `η ≠ 0`). -/
theorem dis_iff_eq32 {σ η : ℝ} (hσ : σ ≠ 0) (hη : η ≠ 0) {ygap infl i rn yn L : ℕ → Ω → ℝ}
    (hMD : MoneyDemandGap η ygap i yn L) :
    DIS 𝔼 σ ygap infl i rn ↔ Eq32 𝔼 σ η ygap infl L rn yn := by
  constructor
  · intro h t
    funext ω
    have h1 := congrFun (h t) ω
    have h2 := congrFun (hMD t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    rw [h2]
    have h1' : σ * ygap t ω = -(i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) +
        σ * 𝔼.E t (ygap (t + 1)) ω := by
      rw [h1]; field_simp
    linear_combination η * h1'
  · intro h t
    funext ω
    have h1 := congrFun (h t) ω
    have h2 := congrFun (hMD t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    rw [h2] at h1
    have h3 : σ * ygap t ω = -(i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) +
        σ * 𝔼.E t (ygap (t + 1)) ω := by
      have h4 : η * (σ * ygap t ω - (-(i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) +
          σ * 𝔼.E t (ygap (t + 1)) ω)) = 0 := by linear_combination h1
      rcases mul_eq_zero.mp h4 with h5 | h5
      · exact absurd h5 hη
      · linarith
    field_simp
    linear_combination h3

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

/-- Galí (2015), eq. (34), p. 75: with `l̂` predetermined, the matrix system (34) is
equivalent to (32), the NKPC (22) and the identity (33). -/
theorem system34_iff {σ η β κ : ℝ} {ygap infl L rn yn dm : ℕ → Ω → ℝ}
    (hL : Predetermined 𝔼 L) :
    System34 𝔼 σ η β κ ygap infl L rn yn dm ↔
      Eq32 𝔼 σ η ygap infl L rn yn ∧ NKPC 𝔼 β κ infl ygap ∧ RealBalanceId infl L dm := by
  constructor
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_,
      fun t => funext fun ω => ?_⟩
    · have h0 := congrFun (h t ω) 0
      have hLω := congrFun (hL t) ω
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec] at h0 ⊢
      linarith
    · have h1 := congrFun (h t ω) 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec] at h1 ⊢
      linarith
    · have h2 := congrFun (h t ω) 2
      have hLω := congrFun (hL t) ω
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec] at h2 ⊢
      linarith
  · rintro ⟨h32, h22, h33⟩ t ω
    have a := congrFun (h32 t) ω
    have b := congrFun (h22 t) ω
    have c := congrFun (h33 t) ω
    have hLω := congrFun (hL t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b c
    funext j
    fin_cases j <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec] <;> linarith

/-- Galí (2015), eqs. (22), (23), (31), (33) and (34), pp. 63–75: given money demand (31)
and predetermined real balances, the model equations NKPC, DIS and (33) hold if and only
if the matrix system (34) holds (`σ ≠ 0`, `η ≠ 0`). -/
theorem model_iff_system34 {σ η β κ : ℝ} (hσ : σ ≠ 0) (hη : η ≠ 0)
    {ygap infl i L rn yn dm : ℕ → Ω → ℝ} (hMD : MoneyDemandGap η ygap i yn L)
    (hL : Predetermined 𝔼 L) :
    (NKPC 𝔼 β κ infl ygap ∧ DIS 𝔼 σ ygap infl i rn ∧ RealBalanceId infl L dm) ↔
      System34 𝔼 σ η β κ ygap infl L rn yn dm := by
  rw [system34_iff 𝔼 hL, dis_iff_eq32 𝔼 hσ hη hMD]
  tauto

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

/-- Galí (2015), p. 75 and fn. 14: the book's determinacy claim, NOT YET CLAIMED here:
the cubic factors as `−(1+ση)(z − r)(z² + q₁ z + q₀)` with `r > 1` and both roots of the
quadratic factor inside the unit circle (Schur–Cohn). The book supports it numerically
only; this definition records the statement without proof. -/
def BookDeterminacyClaim (σ η β κ : ℝ) : Prop :=
  ∃ r q₁ q₀ : ℝ, 1 < r ∧
    (∀ z, charCubic σ η β κ z = -(1 + σ * η) * (z - r) * (z ^ 2 + q₁ * z + q₀)) ∧
    SchurStable (-q₁) q₀

/-! ### Money growth and the interest rate (pp. 75–77) -/

/-- Galí (2015), eq. (35), p. 75: money growth `Δm_{t+1} = ρ_m Δm_t + ε^m_{t+1}` with
innovations of conditional mean zero is an AR(1) process. -/
theorem moneyGrowth_isAR1 {ρm : ℝ} {dm ε : ℕ → Ω → ℝ} (hadapt : 𝔼.Adapted dm)
    (hlaw : ∀ t, dm (t + 1) = ρm • dm t + ε (t + 1)) (hε : ∀ t, 𝔼.E t (ε (t + 1)) = 0) :
    𝔼.IsAR1 ρm dm := by
  refine ⟨hadapt, fun t => ?_⟩
  rw [hlaw, map_add, map_smul, hadapt t, hε, add_zero]

/-- Galí (2015), p. 77: combining money demand (4), `m_t − p_t = y_t − η i_t`, with the DIS
(23) (natural rate and natural output constant, deviations) gives
`(1+η) i_t = η E_t i_{t+1} + E_t Δm_{t+1} + (σ−1) E_t Δy_{t+1}`. -/
theorem interest_rate_equation_raw {σ η : ℝ} (hσ : σ ≠ 0) {m p y i infl dm dy : ℕ → Ω → ℝ}
    (hMD : ∀ t, m t - p t = y t - η • i t)
    (hIS : ∀ t, y t = 𝔼.E t (y (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1))))
    (hp : ∀ t, p (t + 1) = p t + infl (t + 1)) (hm : ∀ t, m (t + 1) = m t + dm (t + 1))
    (hy : ∀ t, y (t + 1) = y t + dy (t + 1))
    (hap : 𝔼.Adapted p) (ham : 𝔼.Adapted m) (hay : 𝔼.Adapted y) (t : ℕ) :
    (1 + η) • i t = η • 𝔼.E t (i (t + 1)) + 𝔼.E t (dm (t + 1)) +
      (σ - 1) • 𝔼.E t (dy (t + 1)) := by
  have hMD1 := congrArg (𝔼.E t) (hMD (t + 1))
  rw [hm, hp, hy] at hMD1
  simp only [map_sub, map_add, map_smul, hap t, ham t, hay t] at hMD1
  have hIS' := hIS t
  rw [hy, map_add, hay t] at hIS'
  funext ω
  have a := congrFun hMD1 ω
  have b := congrFun (hMD t) ω
  have c := congrFun hIS' ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b c ⊢
  have c' : 𝔼.E t (infl (t + 1)) ω = i t ω - σ * 𝔼.E t (dy (t + 1)) ω := by
    have : σ⁻¹ * (i t ω - 𝔼.E t (infl (t + 1)) ω) = 𝔼.E t (dy (t + 1)) ω := by linarith
    field_simp at this
    linarith
  linear_combination b - a - c'

/-- Galí (2015), p. 77: with AR(1) money growth (35), the interest-rate equation
`i_t = η/(1+η) E_t i_{t+1} + ρ_m/(1+η) Δm_t + (σ−1)/(1+η) E_t Δy_{t+1}` (for `η ≠ −1`). -/
theorem interest_rate_equation {σ η ρm : ℝ} (hσ : σ ≠ 0) (hη : 1 + η ≠ 0)
    {m p y i infl dm dy : ℕ → Ω → ℝ}
    (hMD : ∀ t, m t - p t = y t - η • i t)
    (hIS : ∀ t, y t = 𝔼.E t (y (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1))))
    (hp : ∀ t, p (t + 1) = p t + infl (t + 1)) (hm : ∀ t, m (t + 1) = m t + dm (t + 1))
    (hy : ∀ t, y (t + 1) = y t + dy (t + 1))
    (hap : 𝔼.Adapted p) (ham : 𝔼.Adapted m) (hay : 𝔼.Adapted y) (hdm : 𝔼.IsAR1 ρm dm)
    (t : ℕ) :
    i t = (η / (1 + η)) • 𝔼.E t (i (t + 1)) + (ρm / (1 + η)) • dm t +
      ((σ - 1) / (1 + η)) • 𝔼.E t (dy (t + 1)) := by
  have h := interest_rate_equation_raw 𝔼 hσ hMD hIS hp hm hy hap ham hay t
  rw [hdm.2 t] at h
  funext ω
  have a := congrFun h ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at a ⊢
  field_simp
  linear_combination a

/-! ### Forward solutions as genuine infinite sums -/

/-- Galí (2015), p. 77 (used for the forward solution): `E_t` commutes with a series
dominated by a geometric series `|f_k| ≤ aᵏ M`, `0 ≤ a < 1`. -/
theorem E_tsum {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {f : ℕ → Ω → ℝ}
    (hf : ∀ k ω, |f k ω| ≤ a ^ k * M) (t : ℕ) (ω : Ω) :
    𝔼.E t (fun ω' => ∑' k, f k ω') ω = ∑' k, 𝔼.E t (f k) ω := by
  have hgeo : Summable (fun k : ℕ => a ^ k * M) :=
    (summable_geometric_of_lt_one ha0 ha1).mul_right M
  have hsum : ∀ ω', Summable (fun k => f k ω') := fun ω' =>
    Summable.of_norm_bounded hgeo (fun k => by rw [Real.norm_eq_abs]; exact hf k ω')
  have hEs : Summable (fun k => 𝔼.E t (f k) ω) :=
    Summable.of_norm_bounded hgeo (fun k => by
      rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (hf k) t ω)
  -- tail bound for the partial sums
  have htail : ∀ N ω', |(∑' k, f k ω') - ∑ k ∈ Finset.range N, f k ω'| ≤
      a ^ N * M / (1 - a) := by
    intro N ω'
    have hsplit := (hsum ω').sum_add_tsum_nat_add N
    have hsN : Summable (fun k => f (k + N) ω') := (summable_nat_add_iff N).mpr (hsum ω')
    have hgN : Summable (fun k : ℕ => a ^ N * M * a ^ k) :=
      (summable_geometric_of_lt_one ha0 ha1).mul_left (a ^ N * M)
    have hb : ∀ k, |f (k + N) ω'| ≤ a ^ N * M * a ^ k := fun k => by
      have := hf (k + N) ω'
      rw [pow_add] at this
      linarith [show a ^ k * a ^ N * M = a ^ N * M * a ^ k by ring]
    have hval : ∑' k : ℕ, a ^ N * M * a ^ k = a ^ N * M / (1 - a) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one ha0 ha1, div_eq_mul_inv]
    have hup : ∑' k, f (k + N) ω' ≤ a ^ N * M / (1 - a) := by
      rw [← hval]
      exact Summable.tsum_le_tsum (fun k => (le_abs_self _).trans (hb k)) hsN hgN
    have hlo : -(a ^ N * M / (1 - a)) ≤ ∑' k, f (k + N) ω' := by
      rw [← hval, ← tsum_neg]
      exact Summable.tsum_le_tsum (fun k => by linarith [neg_abs_le (f (k + N) ω'), hb k])
        hgN.neg hsN
    rw [← hsplit, add_sub_cancel_left, abs_le]
    exact ⟨hlo, hup⟩
  have hlim1 : Tendsto (fun N => ∑ k ∈ Finset.range N, 𝔼.E t (f k) ω) atTop
      (𝓝 (𝔼.E t (fun ω' => ∑' k, f k ω') ω)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm (a := fun N => a ^ N * M / (1 - a)) (fun N => ?_) ?_
    · rw [norm_norm, Real.norm_eq_abs, abs_sub_comm]
      have hE : ∑ k ∈ Finset.range N, 𝔼.E t (f k) ω =
          𝔼.E t (∑ k ∈ Finset.range N, f k) ω := by
        rw [map_sum, Finset.sum_apply]
      rw [hE, ← Pi.sub_apply, ← map_sub]
      refine 𝔼.abs_E_le (fun ω' => ?_) t ω
      rw [Pi.sub_apply, Finset.sum_apply]
      exact htail N ω'
    · simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).mul_const M).div_const
        (1 - a)
  exact tendsto_nhds_unique hlim1 hEs.hasSum.tendsto_sum_nat

/-- Galí (2015), p. 77: the forward solution `z_t = ∑_{k ≥ 0} aᵏ E_t u_{t+k}` of
`z_t = a E_t z_{t+1} + u_t`. -/
noncomputable def forwardSeries (a : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω

/-- Galí (2015), p. 77: the forward series is summable for bounded forcing. -/
theorem forwardSeries_summable {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (t : ℕ) (ω : Ω) :
    Summable (fun k => a ^ k * 𝔼.E t (u (t + k)) ω) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0 ha1).mul_right M)
    (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0]
  exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (t + k)) t ω) (pow_nonneg ha0 k)

/-- Galí (2015), p. 77: the forward series solves `z_t = a E_t z_{t+1} + u_t` for bounded
adapted forcing `u` and `0 ≤ a < 1`. -/
theorem forwardSeries_solves {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hadapt : 𝔼.Adapted u) (t : ℕ) :
    forwardSeries 𝔼 a u t = a • 𝔼.E t (forwardSeries 𝔼 a u (t + 1)) + u t := by
  funext ω
  have hE : 𝔼.E t (forwardSeries 𝔼 a u (t + 1)) ω =
      ∑' k, a ^ k * 𝔼.E t (u (t + 1 + k)) ω := by
    have hb : ∀ k ω', |a ^ k * 𝔼.E (t + 1) (u (t + 1 + k)) ω'| ≤ a ^ k * M := by
      intro k ω'
      rw [abs_mul, abs_pow, abs_of_nonneg ha0]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (t + 1 + k)) (t + 1) ω')
        (pow_nonneg ha0 k)
    change 𝔼.E t (fun ω' => ∑' k, a ^ k * 𝔼.E (t + 1) (u (t + 1 + k)) ω') ω = _
    rw [E_tsum 𝔼 ha0 ha1 hb t ω]
    refine tsum_congr fun k => ?_
    change 𝔼.E t (a ^ k • 𝔼.E (t + 1) (u (t + 1 + k))) ω = _
    rw [map_smul, 𝔼.tower (Nat.le_succ t), Pi.smul_apply, smul_eq_mul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω = _
  rw [hE, (forwardSeries_summable 𝔼 ha0 ha1 hu t ω).tsum_eq_zero_add,
    pow_zero, one_mul, add_zero, hadapt t, ← tsum_mul_left, add_comm]
  congr 1
  refine tsum_congr fun k => ?_
  rw [show t + (k + 1) = t + 1 + k by omega, pow_succ]
  ring

/-- Galí (2015), p. 77: the forward series is bounded by `M / (1 − a)`. -/
theorem forwardSeries_bounded {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) : BoundedProc (forwardSeries 𝔼 a u) := by
  refine ⟨M / (1 - a), fun t ω => ?_⟩
  have hs := forwardSeries_summable 𝔼 ha0 ha1 hu t ω
  have hg : Summable (fun k : ℕ => M * a ^ k) :=
    (summable_geometric_of_lt_one ha0 ha1).mul_left M
  have hval : ∑' k : ℕ, M * a ^ k = M / (1 - a) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one ha0 ha1, div_eq_mul_inv]
  have hb : ∀ k, |a ^ k * 𝔼.E t (u (t + k)) ω| ≤ M * a ^ k := fun k => by
    rw [abs_mul, abs_pow, abs_of_nonneg ha0, mul_comm M]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (t + k)) t ω) (pow_nonneg ha0 k)
  have hlo : ∀ k, -(M * a ^ k) ≤ a ^ k * 𝔼.E t (u (t + k)) ω := fun k => by
    have := neg_abs_le (a ^ k * 𝔼.E t (u (t + k)) ω)
    linarith [hb k]
  change |∑' k, a ^ k * 𝔼.E t (u (t + k)) ω| ≤ _
  rw [abs_le, ← hval]
  constructor
  · rw [← tsum_neg]
    exact Summable.tsum_le_tsum hlo hg.neg hs
  · exact Summable.tsum_le_tsum (fun k => (le_abs_self _).trans (hb k)) hs hg

/-- Galí (2015), p. 77: any bounded solution of `z_t = a E_t z_{t+1} + u_t` (bounded
adapted `u`, `0 ≤ a < 1`) is the forward series. -/
theorem eq_forwardSeries {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {u z : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hadapt : 𝔼.Adapted u)
    (hz : ∀ t, z t = a • 𝔼.E t (z (t + 1)) + u t) (hzb : BoundedProc z) :
    z = forwardSeries 𝔼 a u := by
  have ha : |a| < 1 := by rw [abs_of_nonneg ha0]; exact ha1
  exact 𝔼.forward_unique ha hz (forwardSeries_solves 𝔼 ha0 ha1 hu hadapt) hzb
    (forwardSeries_bounded 𝔼 ha0 ha1 hu)

/-- Galí (2015), p. 77: the forcing term of the interest-rate equation,
`u_t = ρ_m/(1+η) Δm_t + (σ−1)/(1+η) E_t Δy_{t+1}`. -/
noncomputable def rateForcing (σ η ρm : ℝ) (dm dy : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (ρm / (1 + η)) • dm t + ((σ - 1) / (1 + η)) • 𝔼.E t (dy (t + 1))

/-- Galí (2015), p. 77: the printed forward solution
`i_t = ρ_m/(1+η(1−ρ_m)) Δm_t + (σ−1)/(1+η) ∑_{k≥0} (η/(1+η))ᵏ E_t Δy_{t+1+k}`. -/
noncomputable def rateForward (σ η ρm : ℝ) (dm dy : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ρm / (1 + η * (1 - ρm)) * dm t ω +
    (σ - 1) / (1 + η) * ∑' k, (η / (1 + η)) ^ k * 𝔼.E t (dy (t + 1 + k)) ω

/-- Galí (2015), p. 77: the forward series of the interest-rate equation equals the printed
closed form (`η ≥ 0`, `|ρ_m| < 1`, bounded `Δy`). -/
theorem forwardSeries_rate_eq {σ η ρm Mdy : ℝ} (hη : 0 ≤ η) (hρ : |ρm| < 1)
    {dm dy : ℕ → Ω → ℝ} (hdm : 𝔼.IsAR1 ρm dm) (hdy : ∀ t ω, |dy t ω| ≤ Mdy) :
    forwardSeries 𝔼 (η / (1 + η)) (rateForcing 𝔼 σ η ρm dm dy) =
      rateForward 𝔼 σ η ρm dm dy := by
  funext t ω
  set a := η / (1 + η) with ha
  have h1η : 0 < 1 + η := by linarith
  have ha0 : 0 ≤ a := div_nonneg hη h1η.le
  have ha1 : a < 1 := by rw [ha, div_lt_one h1η]; linarith
  have haρ : |a * ρm| < 1 := by
    rw [abs_mul, abs_of_nonneg ha0]
    calc a * |ρm| ≤ 1 * |ρm| := mul_le_mul_of_nonneg_right ha1.le (abs_nonneg _)
      _ < 1 := by rw [one_mul]; exact hρ
  have hterm : ∀ k, a ^ k * 𝔼.E t (rateForcing 𝔼 σ η ρm dm dy (t + k)) ω =
      ρm / (1 + η) * dm t ω * (a * ρm) ^ k +
        (σ - 1) / (1 + η) * (a ^ k * 𝔼.E t (dy (t + 1 + k)) ω) := by
    intro k
    have hdmk := congrFun (𝔼.ar1_iterate hdm t k) ω
    have hdyk : 𝔼.E t (𝔼.E (t + k) (dy (t + k + 1))) = 𝔼.E t (dy (t + 1 + k)) := by
      rw [𝔼.tower (Nat.le_add_right t k), show t + k + 1 = t + 1 + k by omega]
    simp only [rateForcing, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      hdmk, hdyk]
    ring
  have hs1 : Summable (fun k : ℕ => ρm / (1 + η) * dm t ω * (a * ρm) ^ k) :=
    (summable_geometric_of_abs_lt_one haρ).mul_left _
  have hs2 : Summable (fun k => (σ - 1) / (1 + η) * (a ^ k * 𝔼.E t (dy (t + 1 + k)) ω)) := by
    refine (Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0 ha1).mul_right Mdy)
      (fun k => ?_)).mul_left ((σ - 1) / (1 + η))
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hdy (t + 1 + k)) t ω) (pow_nonneg ha0 k)
  rw [forwardSeries, tsum_congr hterm, hs1.tsum_add hs2, tsum_mul_left,
    tsum_geometric_of_abs_lt_one haρ, tsum_mul_left, rateForward]
  congr 1
  have h2 : 0 < 1 + η * (1 - ρm) := by
    have : ρm < 1 := (abs_lt.mp hρ).2
    nlinarith
  have hx : 1 - η / (1 + η) * ρm = (1 + η * (1 - ρm)) / (1 + η) := by
    field_simp
    ring
  rw [ha, hx]
  field_simp

/-- Galí (2015), p. 77: the forcing term is adapted. -/
theorem rateForcing_adapted {σ η ρm : ℝ} {dm dy : ℕ → Ω → ℝ} (hdm : 𝔼.Adapted dm) :
    𝔼.Adapted (rateForcing 𝔼 σ η ρm dm dy) := by
  intro t
  simp only [rateForcing, map_add, map_smul, hdm t, 𝔼.E_E_self]

/-- Galí (2015), p. 77: the forcing term is bounded when `Δm` and `Δy` are. -/
theorem rateForcing_bounded {σ η ρm Mdm Mdy : ℝ} {dm dy : ℕ → Ω → ℝ}
    (hdmb : ∀ t ω, |dm t ω| ≤ Mdm) (hdy : ∀ t ω, |dy t ω| ≤ Mdy) (t : ℕ) (ω : Ω) :
    |rateForcing 𝔼 σ η ρm dm dy t ω| ≤ |ρm / (1 + η)| * Mdm + |(σ - 1) / (1 + η)| * Mdy := by
  simp only [rateForcing, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
  · exact mul_le_mul_of_nonneg_left (hdmb t ω) (abs_nonneg _)
  · exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hdy (t + 1)) t ω) (abs_nonneg _)

/-- Galí (2015), p. 77: the forward solution exists: the printed closed form solves
`i_t = η/(1+η) E_t i_{t+1} + ρ_m/(1+η) Δm_t + (σ−1)/(1+η) E_t Δy_{t+1}` and is bounded
(`η ≥ 0`, `|ρ_m| < 1`, bounded `Δm`, `Δy`). -/
theorem interest_rate_forward_exists {σ η ρm Mdm Mdy : ℝ} (hη : 0 ≤ η) (hρ : |ρm| < 1)
    {dm dy : ℕ → Ω → ℝ} (hdm : 𝔼.IsAR1 ρm dm) (hdmb : ∀ t ω, |dm t ω| ≤ Mdm)
    (hdy : ∀ t ω, |dy t ω| ≤ Mdy) :
    (∀ t, rateForward 𝔼 σ η ρm dm dy t =
      (η / (1 + η)) • 𝔼.E t (rateForward 𝔼 σ η ρm dm dy (t + 1)) + (ρm / (1 + η)) • dm t +
        ((σ - 1) / (1 + η)) • 𝔼.E t (dy (t + 1))) ∧
      BoundedProc (rateForward 𝔼 σ η ρm dm dy) := by
  have h1η : 0 < 1 + η := by linarith
  have ha0 : 0 ≤ η / (1 + η) := div_nonneg hη h1η.le
  have ha1 : η / (1 + η) < 1 := by rw [div_lt_one h1η]; linarith
  have hub := rateForcing_bounded 𝔼 (σ := σ) (η := η) (ρm := ρm) hdmb hdy
  rw [← forwardSeries_rate_eq 𝔼 hη hρ hdm hdy]
  refine ⟨fun t => ?_, forwardSeries_bounded 𝔼 ha0 ha1 hub⟩
  rw [forwardSeries_solves 𝔼 ha0 ha1 hub (rateForcing_adapted 𝔼 hdm.1) t, rateForcing,
    add_assoc]

/-- Galí (2015), p. 77: the forward solution is the unique bounded equilibrium interest
rate: under money demand (4), the DIS (23), AR(1) money growth (35) and bounded `Δm`, `Δy`,
every bounded `i` equals
`ρ_m/(1+η(1−ρ_m)) Δm_t + (σ−1)/(1+η) ∑_{k≥0} (η/(1+η))ᵏ E_t Δy_{t+1+k}`. -/
theorem interest_rate_forward_unique {σ η ρm Mdm Mdy : ℝ} (hσ : σ ≠ 0) (hη : 0 ≤ η)
    (hρ : |ρm| < 1) {m p y i infl dm dy : ℕ → Ω → ℝ}
    (hMD : ∀ t, m t - p t = y t - η • i t)
    (hIS : ∀ t, y t = 𝔼.E t (y (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1))))
    (hp : ∀ t, p (t + 1) = p t + infl (t + 1)) (hm : ∀ t, m (t + 1) = m t + dm (t + 1))
    (hy : ∀ t, y (t + 1) = y t + dy (t + 1))
    (hap : 𝔼.Adapted p) (ham : 𝔼.Adapted m) (hay : 𝔼.Adapted y) (hdm : 𝔼.IsAR1 ρm dm)
    (hdmb : ∀ t ω, |dm t ω| ≤ Mdm) (hdy : ∀ t ω, |dy t ω| ≤ Mdy) (hib : BoundedProc i) :
    i = rateForward 𝔼 σ η ρm dm dy := by
  have h1η : 0 < 1 + η := by linarith
  have ha0 : 0 ≤ η / (1 + η) := div_nonneg hη h1η.le
  have ha1 : η / (1 + η) < 1 := by rw [div_lt_one h1η]; linarith
  have hub := rateForcing_bounded 𝔼 (σ := σ) (η := η) (ρm := ρm) hdmb hdy
  have hi : ∀ t, i t = (η / (1 + η)) • 𝔼.E t (i (t + 1)) +
      rateForcing 𝔼 σ η ρm dm dy t := fun t => by
    rw [rateForcing, ← add_assoc]
    exact interest_rate_equation 𝔼 hσ h1η.ne' hMD hIS hp hm hy hap ham hay hdm t
  rw [eq_forwardSeries 𝔼 ha0 ha1 hub (rateForcing_adapted 𝔼 hdm.1) hi hib,
    forwardSeries_rate_eq 𝔼 hη hρ hdm hdy]

/-- Galí (2015), p. 77: with log utility (`σ = 1`) the bounded equilibrium interest rate is
`i_t = ρ_m Δm_t / (1 + η(1−ρ_m))`. -/
theorem interest_rate_log_utility {η ρm Mdm Mdy : ℝ} (hη : 0 ≤ η)
    (hρ : |ρm| < 1) {m p y i infl dm dy : ℕ → Ω → ℝ}
    (hMD : ∀ t, m t - p t = y t - η • i t)
    (hIS : ∀ t, y t = 𝔼.E t (y (t + 1)) - (1 : ℝ)⁻¹ • (i t - 𝔼.E t (infl (t + 1))))
    (hp : ∀ t, p (t + 1) = p t + infl (t + 1)) (hm : ∀ t, m (t + 1) = m t + dm (t + 1))
    (hy : ∀ t, y (t + 1) = y t + dy (t + 1))
    (hap : 𝔼.Adapted p) (ham : 𝔼.Adapted m) (hay : 𝔼.Adapted y) (hdm : 𝔼.IsAR1 ρm dm)
    (hdmb : ∀ t ω, |dm t ω| ≤ Mdm) (hdy : ∀ t ω, |dy t ω| ≤ Mdy) (hib : BoundedProc i)
    (t : ℕ) : i t = (ρm / (1 + η * (1 - ρm))) • dm t := by
  rw [interest_rate_forward_unique 𝔼 one_ne_zero hη hρ hMD hIS hp hm hy hap ham hay hdm hdmb
    hdy hib]
  funext ω
  simp [rateForward]

/-- Galí (2015), p. 77: for `ρ_m ∈ [0, 1)` and `η ≥ 0` the coefficient
`ρ_m/(1+η(1−ρ_m))` is nonnegative (positive if `ρ_m > 0`), so with `σ = 1` the nominal
rate comoves positively with money growth: `i_t Δm_t ≥ 0` in every state. -/
theorem interest_rate_comoves {η ρm : ℝ} (hη : 0 ≤ η) (hρ0 : 0 ≤ ρm) (hρ1 : ρm < 1)
    {i dm : ℕ → Ω → ℝ} (hi : ∀ t, i t = (ρm / (1 + η * (1 - ρm))) • dm t) :
    0 ≤ ρm / (1 + η * (1 - ρm)) ∧ (0 < ρm → 0 < ρm / (1 + η * (1 - ρm))) ∧
      ∀ t ω, 0 ≤ i t ω * dm t ω := by
  have hden : 0 < 1 + η * (1 - ρm) := by nlinarith
  refine ⟨div_nonneg hρ0 hden.le, fun h => div_pos h hden, fun t ω => ?_⟩
  rw [hi t, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact mul_nonneg (div_nonneg hρ0 hden.le) (mul_self_nonneg _)

/-- Galí (2015), p. 77: a liquidity effect is possible: if `σ > 1` and the expected
discounted output growth `∑ (η/(1+η))ᵏ E_t Δy_{t+1+k}` is negative, the nominal rate lies
below the money-growth term `ρ_m Δm_t/(1+η(1−ρ_m))`. -/
theorem liquidity_effect_of_sigma_gt_one {σ η ρm : ℝ} (hσ : 1 < σ) (hη : 0 ≤ η)
    {dm dy : ℕ → Ω → ℝ} (t : ℕ) (ω : Ω)
    (hneg : ∑' k, (η / (1 + η)) ^ k * 𝔼.E t (dy (t + 1 + k)) ω < 0) :
    rateForward 𝔼 σ η ρm dm dy t ω < ρm / (1 + η * (1 - ρm)) * dm t ω := by
  have h1η : 0 < 1 + η := by linarith
  have hc : 0 < (σ - 1) / (1 + η) := div_pos (by linarith) h1η
  have := mul_neg_of_pos_of_neg hc hneg
  simp only [rateForward]
  linarith

omit 𝔼 in
/-- Galí (2015), p. 79: money demand (4), `m_t − p_t = ŷ_t − η i_t`, rewritten as an
interest-rate rule targeting the price level, with `v_t = −η⁻¹ Δm_t`:
`i_t = η⁻¹(p_t − m_{t−1}) + η⁻¹ ŷ_t + v_t = η⁻¹(p_{t−1} − m_{t−1}) + η⁻¹ π_t + η⁻¹ ŷ_t + v_t`
(stated at dates `t + 1 ≥ 1`). -/
theorem price_level_rule {η : ℝ} (hη : η ≠ 0) {m p y i infl dm v : ℕ → Ω → ℝ}
    (hMD : ∀ t, m t - p t = y t - η • i t) (hp : ∀ t, infl (t + 1) = p (t + 1) - p t)
    (hm : ∀ t, dm (t + 1) = m (t + 1) - m t) (hv : ∀ t, v t = -η⁻¹ • dm t) (t : ℕ) :
    i (t + 1) = η⁻¹ • (p (t + 1) - m t) + η⁻¹ • y (t + 1) + v (t + 1) ∧
      i (t + 1) = η⁻¹ • (p t - m t) + η⁻¹ • infl (t + 1) + η⁻¹ • y (t + 1) + v (t + 1) := by
  have key : i (t + 1) = η⁻¹ • (p (t + 1) - m t) + η⁻¹ • y (t + 1) + v (t + 1) := by
    funext ω
    have a := congrFun (hMD (t + 1)) ω
    have b := congrFun (hm t) ω
    have c := congrFun (hv (t + 1)) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b c ⊢
    rw [c, b, show i (t + 1) ω = η⁻¹ * (η * i (t + 1) ω) by field_simp]
    linear_combination η⁻¹ * a
  refine ⟨key, ?_⟩
  rw [key, hp]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Gali.BasicNewKeynesianModel.MoneyRule
