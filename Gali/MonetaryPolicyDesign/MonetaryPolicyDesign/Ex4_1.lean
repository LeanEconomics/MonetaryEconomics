/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MonetaryPolicyDesign.Expectations
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Exercise 4.1: some indeterminacy proofs

Galí (2015), Chapter 4, Exercise 4.1, p. 121, on the systems (9)–(10) (p. 104–105)
and (12)–(13) (p. 105) of §4.3.1.

The non-policy block is the NKPC `π_t = β E_t π_{t+1} + κ ỹ_t` and the DIS equation
`ỹ_t = E_t ỹ_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − r^n_t)` (eqs. (6), (7), p. 104).

## Main results

* `isEigenvalue_iff_root`: a complex number is an eigenvalue of a real `2 × 2`
  matrix iff it is a root of `z² − tr A z + det A`.
* `equilibrium_AO_iff`: under the rule `i_t = r^n_t` (8) the model is
  `x_t = A_O E_t x_{t+1}` with `A_O = [[1, σ⁻¹], [κ, β + κ/σ]]` (10).
* **Exercise 4.1(a)** `AO_eigenvalues`: `A_O` has two real eigenvalues
  `0 < λ₁ < 1 < λ₂`, and no others. Hence (`AO_not_unique`) the efficient outcome
  `ỹ = π = 0` is not the only bounded equilibrium.
* `equilibrium_iff_structural`, `structural_iff_solves`: under the rule
  `i_t = r^n_t + φ_π π_t + φ_y ỹ_t − u_t` the model is `x_t = A_T E_t x_{t+1} + B_T u_t`
  with `A_T` of (13).
* **Exercise 4.1(b)** `AT_eigenvalues_inside_iff`: for `φ_π, φ_y ≥ 0` both eigenvalues
  of `A_T` lie strictly **inside** the unit circle iff condition (14),
  `κ (φ_π − 1) + (1 − β) φ_y > 0`.
* **Correction C4-2**: the exercise as printed says "outside". `AT_not_both_outside`:
  the two eigenvalues of `A_T` are never both on or outside the unit circle, so
  `printed_iff_iff_not14` (the printed equivalence holds exactly when (14) fails) and
  `printed_ex4_1b_false` (the printed claim is false).
* General infrastructure used by Exercises 4.2 and 4.3: the MSV solution of the
  structural system for an AR(1) forcing (`msv_structural`), linearity
  (`structural_add`, `structural_smul`), uniqueness under (14) (`structural_unique`) and
  multiplicity without it (`structural_not_unique`).

The `A_T` algebra, the Bullard–Mitra lemma and the MSV formulas are restated from the
Chapter 3 project (`TaylorRuleSystem.lean`).
-/

namespace Gali.MonetaryPolicyDesign.Ex4_1

open Filter Topology

/-! ### Eigenvalues of real `2 × 2` matrices -/

/-- Galí (2015), p. 105: `z ∈ ℂ` is an eigenvalue of the real matrix `A`, i.e. there is a
nonzero complex vector `v` with `A v = z v`. -/
def IsEigenvalue (A : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) : Prop :=
  ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ Matrix.mulVec (A.map (fun a : ℝ => (a : ℂ))) v = z • v

/-- Galí (2015), p. 105: the characteristic determinant of a real `2 × 2` matrix,
`det (z I − A) = z² − tr A z + det A`. -/
theorem det_charMatrix (A : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) :
    (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) - A.map (fun a : ℝ => (a : ℂ))).det
      = z ^ 2 - (tr2 A : ℂ) * z + (det2 A : ℂ) := by
  rw [Matrix.det_fin_two]
  simp [tr2, det2]
  ring

/-- Galí (2015), p. 105: `z` is an eigenvalue of `A` iff `z² − tr A z + det A = 0`. -/
theorem isEigenvalue_iff_charpoly (A : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) :
    IsEigenvalue A z ↔ z ^ 2 - (tr2 A : ℂ) * z + (det2 A : ℂ) = 0 := by
  rw [← det_charMatrix, ← Matrix.exists_mulVec_eq_zero_iff]
  unfold IsEigenvalue
  refine exists_congr fun v => and_congr_right fun _ => ?_
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero, eq_comm]

/-- Galí (2015), p. 105: the eigenvalues of a real `2 × 2` matrix are exactly the two roots
`root₁`, `root₂` of its characteristic polynomial. -/
theorem isEigenvalue_iff_root (A : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) :
    IsEigenvalue A z ↔ z = root₁ (tr2 A) (det2 A) ∨ z = root₂ (tr2 A) (det2 A) := by
  rw [isEigenvalue_iff_charpoly]
  exact ⟨eq_root_of_eq, root_eq _ _ z⟩

/-- Galí (2015), p. 105: both eigenvalues lie strictly inside the unit circle iff the
Schur–Cohn condition holds. -/
theorem eigenvalues_inside_iff (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ z, IsEigenvalue A z → ‖z‖ < 1) ↔ SchurStable (tr2 A) (det2 A) := by
  rw [schurStable_iff_roots]
  simp only [isEigenvalue_iff_root]
  constructor
  · intro h
    exact ⟨h _ (Or.inl rfl), h _ (Or.inr rfl)⟩
  · rintro ⟨h1, h2⟩ z (rfl | rfl)
    exacts [h1, h2]

/-! ### The model -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (7), p. 104: the NKPC `π_t = β E_t π_{t+1} + κ ỹ_t`. -/
def NKPC (β κ : ℝ) (ygap infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t

/-- Galí (2015), eq. (6), p. 104: the DIS equation
`ỹ_t = E_t ỹ_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − r^n_t)`. -/
def DIS (σ : ℝ) (ygap i infl rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ygap t = 𝔼.E t (ygap (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - rn t)

/-- Galí (2015), eq. (9), p. 104: the stacked vector `x_t = (ỹ_t, π_t)`. -/
def stack (ygap infl : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![ygap t, infl t]

/-- Galí (2015), eq. (12), p. 105: two bounded processes stack to a bounded vector. -/
theorem boundedVec_stack {a b : ℕ → Ω → ℝ} (ha : BoundedProc a) (hb : BoundedProc b) :
    BoundedVec (stack a b) := by
  obtain ⟨M₁, h₁⟩ := ha
  obtain ⟨M₂, h₂⟩ := hb
  refine ⟨max M₁ M₂, fun t j ω => ?_⟩
  fin_cases j
  · exact (h₁ t ω).trans (le_max_left _ _)
  · exact (h₂ t ω).trans (le_max_right _ _)

/-- Galí (2015), eq. (12), p. 105: two adapted processes stack to an adapted vector. -/
theorem adaptedVec_stack {a b : ℕ → Ω → ℝ} (ha : 𝔼.Adapted a) (hb : 𝔼.Adapted b) :
    𝔼.AdaptedVec (stack a b) := by
  intro t j
  fin_cases j
  · exact ha t
  · exact hb t

/-! ### Exercise 4.1(a): the exogenous rule `i_t = r^n_t` -/

/-- Galí (2015), eq. (10), p. 105: `A_O = [[1, 1/σ], [κ, β + κ/σ]]`. -/
noncomputable def AO (β σ κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1 / σ; κ, β + κ / σ]

/-- Galí (2015), eq. (10), p. 105: `tr A_O = 1 + β + κ/σ`. -/
theorem tr2_AO (β σ κ : ℝ) : tr2 (AO β σ κ) = 1 + β + κ / σ := by
  simp [tr2, AO]
  ring

/-- Galí (2015), eq. (10), p. 105: `det A_O = β`. -/
theorem det2_AO {β σ κ : ℝ} (hσ : σ ≠ 0) : det2 (AO β σ κ) = β := by
  simp [det2, AO]
  field_simp
  ring

/-- Galí (2015), eqs. (8)–(10), pp. 104–105: under the rule `i_t = r^n_t` the NKPC and the
DIS equation hold iff `x_t = A_O E_t x_{t+1}`. -/
theorem equilibrium_AO_iff (β σ κ : ℝ) (rn ygap infl : ℕ → Ω → ℝ) :
    (NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap rn infl rn) ↔
      𝔼.Solves (AO β σ κ) 0 (stack ygap infl) := by
  constructor
  · rintro ⟨hp, hd⟩ t j
    funext ω
    have e1 := congrFun (hd t) ω
    have e2 := congrFun (hp t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    fin_cases j
    · simp [stack, AO]
      linear_combination e1
    · simp [stack, AO]
      linear_combination e2 + κ * e1
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have e0 := congrFun (h t 0) ω
      have e1 := congrFun (h t 1) ω
      simp [stack, AO] at e0 e1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e1 - κ * e0
    · have e0 := congrFun (h t 0) ω
      simp [stack, AO] at e0
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e0

/-- **Exercise 4.1(a)** (Galí 2015, p. 121; claim on p. 105): for `σ, κ > 0` and
`0 < β < 1`, the matrix `A_O` has two real eigenvalues `λ₁, λ₂` with
`0 < λ₁ < 1 < λ₂`, and every complex eigenvalue is one of them. -/
theorem AO_eigenvalues {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ l₁ l₂ : ℝ, 0 < l₁ ∧ l₁ < 1 ∧ 1 < l₂ ∧
      ∀ z : ℂ, IsEigenvalue (AO β σ κ) z ↔ z = l₁ ∨ z = l₂ := by
  obtain ⟨T, hT⟩ : ∃ T, T = 1 + β + κ / σ := ⟨_, rfl⟩
  have hk : 0 < κ / σ := div_pos hκ hσ
  have hd : 0 ≤ T ^ 2 - 4 * β := by nlinarith
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (T ^ 2 - 4 * β) := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := hs ▸ Real.sqrt_nonneg _
  have hs2 : s ^ 2 = T ^ 2 - 4 * β := hs ▸ Real.sq_sqrt hd
  have hT0 : 0 < T := by linarith
  refine ⟨(T - s) / 2, (T + s) / 2, ?_, ?_, ?_, fun z => ?_⟩
  · have : s < T := by nlinarith
    linarith
  · have : T - 2 < s := by nlinarith
    linarith
  · have : 2 - T < s := by nlinarith
    linarith
  · rw [isEigenvalue_iff_charpoly, tr2_AO, det2_AO hσ.ne', ← hT]
    have hs2c : (s : ℂ) ^ 2 = (T : ℂ) ^ 2 - 4 * β := by exact_mod_cast hs2
    constructor
    · intro h
      have hm : (z - (((T - s) / 2 : ℝ) : ℂ)) * (z - (((T + s) / 2 : ℝ) : ℂ)) = 0 := by
        push_cast
        linear_combination h - (1 / 4 : ℂ) * hs2c
      rcases mul_eq_zero.mp hm with h' | h'
      · exact Or.inl (sub_eq_zero.mp h')
      · exact Or.inr (sub_eq_zero.mp h')
    · rintro (rfl | rfl)
      · push_cast
        linear_combination (1 / 4 : ℂ) * hs2c
      · push_cast
        linear_combination (1 / 4 : ℂ) * hs2c

/-- Galí (2015), p. 105: `A_O` violates the Schur–Cohn condition (one eigenvalue is
outside the unit circle). -/
theorem not_schurStable_AO {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    ¬ SchurStable (tr2 (AO β σ κ)) (det2 (AO β σ κ)) := by
  rw [tr2_AO, det2_AO hσ.ne']
  rintro ⟨-, h⟩
  rw [abs_lt] at h
  have := div_pos hκ hσ
  linarith

/-- Galí (2015), p. 105: the efficient outcome `ỹ = π = 0` is an equilibrium under the
rule `i_t = r^n_t`. -/
theorem AO_zero_equilibrium (β σ κ : ℝ) (rn : ℕ → Ω → ℝ) :
    NKPC 𝔼 β κ (fun _ => 0) (fun _ => 0) ∧ DIS 𝔼 σ (fun _ => 0) rn (fun _ => 0) rn := by
  refine ⟨fun t => ?_, fun t => ?_⟩ <;> simp

/-- Galí (2015), p. 105: the system under `i_t = r^n_t` is not determinate. -/
theorem AO_not_determinate [Nonempty Ω] {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    ¬ 𝔼.Determinate (AO β σ κ) := by
  rw [𝔼.determinate_iff]
  exact not_schurStable_AO hσ hκ

/-- **Indeterminacy under `i_t = r^n_t`** (Galí 2015, p. 105): besides `ỹ = π = 0` there is
an equilibrium with bounded adapted output gap and inflation that is not identically
zero. -/
theorem AO_not_unique [Nonempty Ω] {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (rn : ℕ → Ω → ℝ) :
    ∃ ygap infl : ℕ → Ω → ℝ, (NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap rn infl rn) ∧
      𝔼.Adapted ygap ∧ 𝔼.Adapted infl ∧ BoundedProc ygap ∧ BoundedProc infl ∧
      (ygap ≠ (fun _ => 0) ∨ infl ≠ (fun _ => 0)) := by
  have hz : 𝔼.Solves (AO β σ κ) 0 0 := fun t i => by simp
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ := 𝔼.system_not_unique (not_schurStable_AO hσ hκ) hz
    (fun t i => by simp) ⟨0, fun t i ω => by simp⟩
  have hst : stack (fun t => y t 0) (fun t => y t 1) = y := by
    funext t j
    fin_cases j <;> rfl
  refine ⟨fun t => y t 0, fun t => y t 1, (equilibrium_AO_iff 𝔼 β σ κ rn _ _).mpr (hst ▸ hy),
    fun t => hay t 0, fun t => hay t 1, ⟨M, fun t ω => hM t 0 ω⟩, ⟨M, fun t ω => hM t 1 ω⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  funext t j
  fin_cases j
  · exact congrFun hcon.1 t
  · exact congrFun hcon.2 t

/-! ### Exercise 4.1(b): the rule `i_t = r^n_t + φ_π π_t + φ_y ỹ_t` -/

/-- Galí (2015), p. 105, with a forcing term `u`: the equilibrium conditions with the
interest rate substituted out,
`(σ + φ_y) ỹ_t + φ_π π_t = σ E_t ỹ_{t+1} + E_t π_{t+1} + u_t`, together with the NKPC. -/
def Structural (β σ κ φπ φy : ℝ) (u ygap infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (σ + φy) • ygap t + φπ • infl t
      = σ • 𝔼.E t (ygap (t + 1)) + 𝔼.E t (infl (t + 1)) + u t ∧
    infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t

/-- Galí (2015), eqs. (6), (7), (11), pp. 104–105: if the rule is
`i_t = r^n_t + φ_π π_t + φ_y ỹ_t − u_t` (rule (11) is `u = 0`), the NKPC and the DIS hold
iff the structural equations hold with forcing `u`. -/
theorem equilibrium_iff_structural {β σ κ φπ φy : ℝ} (hσ : σ ≠ 0)
    {rn u ygap infl i : ℕ → Ω → ℝ}
    (hrule : ∀ t, i t = rn t + φπ • infl t + φy • ygap t - u t) :
    (NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl rn) ↔
      Structural 𝔼 β σ κ φπ φy u ygap infl := by
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  constructor
  · rintro ⟨hp, hd⟩ t
    refine ⟨?_, hp t⟩
    funext ω
    have e := congrFun (hd t) ω
    have r := congrFun (hrule t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e r ⊢
    linear_combination σ * e - (i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) * hinv - r
  · intro h
    refine ⟨fun t => (h t).2, fun t => ?_⟩
    funext ω
    have e := congrFun (h t).1 ω
    have r := congrFun (hrule t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e r ⊢
    linear_combination σ⁻¹ * e + σ⁻¹ * r
      - (ygap t ω - 𝔼.E t (ygap (t + 1)) ω) * hinv

/-- Galí (2015), p. 105: `Ω = 1/(σ + φ_y + κ φ_π)`. -/
noncomputable def omega (σ κ φπ φy : ℝ) : ℝ := 1 / (σ + φy + κ * φπ)

/-- Galí (2015), eq. (13), p. 105: `A_T = Ω [[σ, 1 − βφ_π], [σκ, κ + β(σ + φ_y)]]`. -/
noncomputable def AT (β σ κ φπ φy : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![omega σ κ φπ φy * σ, omega σ κ φπ φy * (1 - β * φπ);
    omega σ κ φπ φy * (σ * κ), omega σ κ φπ φy * (κ + β * (σ + φy))]

/-- Galí (2015), p. 105 (Chapter 3, eq. (27)): the vector `B_T = Ω (1, κ)`. -/
noncomputable def BT (σ κ φπ φy : ℝ) : Fin 2 → ℝ := ![omega σ κ φπ φy, omega σ κ φπ φy * κ]

/-- Galí (2015), eq. (12), p. 105: the forcing term `B u_t` of the system. -/
def forcing (b : Fin 2 → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t j => b j • u t

/-- Galí (2015), eq. (12), p. 105: the structural equations are equivalent to
`x_t = A_T E_t x_{t+1} + B_T u_t`, provided `σ + φ_y + κ φ_π ≠ 0`. Restated from the
Chapter 3 project. -/
theorem structural_iff_solves {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0)
    (u ygap infl : ℕ → Ω → ℝ) :
    Structural 𝔼 β σ κ φπ φy u ygap infl ↔
      𝔼.Solves (AT β σ κ φπ φy) (forcing (BT σ κ φπ φy) u) (stack ygap infl) := by
  constructor
  · intro h t j
    obtain ⟨h1, h2⟩ := h t
    funext ω
    have e1 := congrFun h1 ω
    have e2 := congrFun h2 ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    fin_cases j
    · simp [stack, forcing, AT, BT, omega]
      field_simp
      linear_combination e1 - φπ * e2
    · simp [stack, forcing, AT, BT, omega]
      field_simp
      linear_combination κ * e1 + (σ + φy) * e2
  · intro h t
    have h0 := h t 0
    have h1 := h t 1
    simp only [stack, Fin.isValue, Matrix.cons_val_zero, AT, omega, one_div, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one, forcing, BT] at h0 h1
    refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
    · have e0 := congrFun h0 ω
      have e1 := congrFun h1 ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1 ⊢
      field_simp at e0 e1
      apply mul_left_cancel₀ hS
      linear_combination (σ + φy) * e0 + φπ * e1
    · have e0 := congrFun h0 ω
      have e1 := congrFun h1 ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1 ⊢
      field_simp at e0 e1
      apply mul_left_cancel₀ hS
      linear_combination e1 - κ * e0

/-- Galí (2015), eq. (13), p. 105: `tr A_T = (σ (1 + β) + κ + β φ_y)/(σ + φ_y + κ φ_π)`. -/
theorem tr2_AT {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0) :
    tr2 (AT β σ κ φπ φy) = (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) := by
  simp only [tr2, AT, omega, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), eq. (13), p. 105: `det A_T = σ β/(σ + φ_y + κ φ_π)`. -/
theorem det2_AT {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0) :
    det2 (AT β σ κ φπ φy) = σ * β / (σ + φy + κ * φπ) := by
  simp only [det2, AT, omega, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), p. 105: `0 < det A_T < 1` for `σ, κ > 0`, `0 < β < 1`, `φ_π, φ_y ≥ 0`. -/
theorem det2_AT_mem {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    0 < det2 (AT β σ κ φπ φy) ∧ det2 (AT β σ κ φπ φy) < 1 := by
  have hS : 0 < σ + φy + κ * φπ := by positivity
  rw [det2_AT hS.ne']
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hS]
  nlinarith

/-- **Bullard–Mitra** (Galí 2015, eq. (14), p. 106): for `σ, κ > 0`, `0 < β < 1` and
`φ_π, φ_y ≥ 0`, `A_T` satisfies the Schur–Cohn condition iff
`κ (φ_π − 1) + (1 − β) φ_y > 0`. Restated from the Chapter 3 project. -/
theorem schurStable_AT_iff {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    SchurStable (tr2 (AT β σ κ φπ φy)) (det2 (AT β σ κ φπ φy)) ↔
      0 < κ * (φπ - 1) + (1 - β) * φy := by
  have hS : 0 < σ + φy + κ * φπ := by positivity
  obtain ⟨hD0, hD1⟩ := det2_AT_mem hσ hκ hβ0 hβ1 hφπ hφy
  rw [det2_AT hS.ne'] at hD0 hD1
  rw [tr2_AT hS.ne', det2_AT hS.ne']
  have hT0 : 0 < (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) := by positivity
  unfold SchurStable
  rw [abs_of_pos hD0, abs_of_pos hT0]
  have key : (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) < 1 + σ * β / (σ + φy + κ * φπ)
      ↔ σ * (1 + β) + κ + β * φy < σ + φy + κ * φπ + σ * β := by
    rw [one_add_div hS.ne', div_lt_div_iff_of_pos_right hS]
  rw [key]
  constructor
  · rintro ⟨-, h⟩
    linarith
  · intro h
    exact ⟨hD1, by linarith⟩

/-- **Exercise 4.1(b), corrected** (Galí 2015, p. 121; text p. 106): for `σ, κ > 0`,
`0 < β < 1` and `φ_π, φ_y ≥ 0`, both eigenvalues of `A_T` lie strictly inside the unit
circle iff condition (14), `κ (φ_π − 1) + (1 − β) φ_y > 0`. -/
theorem AT_eigenvalues_inside_iff {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    (∀ z, IsEigenvalue (AT β σ κ φπ φy) z → ‖z‖ < 1) ↔
      0 < κ * (φπ - 1) + (1 - β) * φy := by
  rw [eigenvalues_inside_iff]
  exact schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy

/-- Galí (2015), Exercise 4.1(b), p. 121 (correction C4-2): the two eigenvalues of `A_T`
are never both on or outside the unit circle, since their product is
`det A_T ∈ (0, 1)`. -/
theorem AT_not_both_outside {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    ¬ ∀ z, IsEigenvalue (AT β σ κ φπ φy) z → 1 ≤ ‖z‖ := by
  intro h
  simp only [isEigenvalue_iff_root] at h
  have h1 := h _ (Or.inl rfl)
  have h2 := h _ (Or.inr rfl)
  obtain ⟨hD0, hD1⟩ := det2_AT_mem hσ hκ hβ0 hβ1 hφπ hφy
  have hp : ‖root₁ (tr2 (AT β σ κ φπ φy)) (det2 (AT β σ κ φπ φy))‖ *
      ‖root₂ (tr2 (AT β σ κ φπ φy)) (det2 (AT β σ κ φπ φy))‖
        = det2 (AT β σ κ φπ φy) := by
    rw [← norm_mul, root_prod, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD0]
  nlinarith

/-- Galí (2015), Exercise 4.1(b), p. 121 (correction C4-2): the printed equivalence
"both eigenvalues outside the unit circle iff (14)" holds exactly when (14) fails. -/
theorem printed_iff_iff_not14 {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    ((∀ z, IsEigenvalue (AT β σ κ φπ φy) z → 1 < ‖z‖) ↔
      0 < κ * (φπ - 1) + (1 - β) * φy) ↔ ¬ 0 < κ * (φπ - 1) + (1 - β) * φy := by
  have hno : ¬ ∀ z, IsEigenvalue (AT β σ κ φπ φy) z → 1 < ‖z‖ := fun h =>
    AT_not_both_outside hσ hκ hβ0 hβ1 hφπ hφy fun z hz => (h z hz).le
  constructor
  · intro h h14
    exact hno (h.mpr h14)
  · intro h
    exact ⟨fun h' => absurd h' hno, fun h' => absurd h' h⟩

/-- **The printed Exercise 4.1(b) is false** (Galí 2015, p. 121, correction C4-2): at
`β = 1/2`, `σ = κ = 1`, `φ_π = 2`, `φ_y = 0` condition (14) holds but the eigenvalues
of `A_T` are not outside the unit circle. -/
theorem printed_ex4_1b_false :
    ¬ ∀ β σ κ φπ φy : ℝ, 0 < σ → 0 < κ → 0 < β → β < 1 → 0 ≤ φπ → 0 ≤ φy →
      ((∀ z, IsEigenvalue (AT β σ κ φπ φy) z → 1 < ‖z‖) ↔
        0 < κ * (φπ - 1) + (1 - β) * φy) := by
  intro h
  have h' := h (1 / 2) 1 1 2 0 one_pos one_pos (by norm_num) (by norm_num) (by norm_num)
    le_rfl
  rw [printed_iff_iff_not14 one_pos one_pos (by norm_num) (by norm_num) (by norm_num)
    le_rfl] at h'
  exact h' (by norm_num)

/-- Galí (2015), p. 106: the system under rule (11) is determinate (at most one bounded
adapted solution for every forcing) iff (14) holds. -/
theorem determinate_iff_14 [Nonempty Ω] {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    𝔼.Determinate (AT β σ κ φπ φy) ↔ 0 < κ * (φπ - 1) + (1 - β) * φy :=
  (𝔼.determinate_iff _).trans (schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy)

/-- Galí (2015), p. 106: under (14), two bounded adapted solutions of the structural
equations with the same forcing coincide. -/
theorem structural_unique {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (h14 : 0 < κ * (φπ - 1) + (1 - β) * φy)
    {u ygap infl ygap' infl' : ℕ → Ω → ℝ}
    (hs : Structural 𝔼 β σ κ φπ φy u ygap infl) (hs' : Structural 𝔼 β σ κ φπ φy u ygap' infl')
    (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl) (ha' : 𝔼.Adapted ygap')
    (hb' : 𝔼.Adapted infl') (hba : BoundedProc ygap) (hbb : BoundedProc infl)
    (hba' : BoundedProc ygap') (hbb' : BoundedProc infl') :
    ygap = ygap' ∧ infl = infl' := by
  have hS : σ + φy + κ * φπ ≠ 0 := by positivity
  have heq := 𝔼.system_unique ((schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy).mpr h14)
    ((structural_iff_solves 𝔼 hS _ _ _).mp hs) ((structural_iff_solves 𝔼 hS _ _ _).mp hs')
    (adaptedVec_stack 𝔼 ha hb) (adaptedVec_stack 𝔼 ha' hb')
    (boundedVec_stack hba hbb) (boundedVec_stack hba' hbb')
  exact ⟨funext fun t => by simpa [stack] using congrFun (congrFun heq t) 0,
    funext fun t => by simpa [stack] using congrFun (congrFun heq t) 1⟩

/-- Galí (2015), p. 106: without (14), next to any bounded adapted solution of the
structural equations there is a second one. -/
theorem structural_not_unique [Nonempty Ω] {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy)
    (h14 : κ * (φπ - 1) + (1 - β) * φy ≤ 0) {u ygap infl : ℕ → Ω → ℝ}
    (hs : Structural 𝔼 β σ κ φπ φy u ygap infl) (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl)
    (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    ∃ ygap' infl', Structural 𝔼 β σ κ φπ φy u ygap' infl' ∧ 𝔼.Adapted ygap' ∧
      𝔼.Adapted infl' ∧ BoundedProc ygap' ∧ BoundedProc infl' ∧
      (ygap' ≠ ygap ∨ infl' ≠ infl) := by
  have hS : σ + φy + κ * φπ ≠ 0 := by positivity
  have hns : ¬ SchurStable (tr2 (AT β σ κ φπ φy)) (det2 (AT β σ κ φπ φy)) := by
    rw [schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy]
    linarith
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ := 𝔼.system_not_unique hns
    ((structural_iff_solves 𝔼 hS _ _ _).mp hs) (adaptedVec_stack 𝔼 ha hb)
    (boundedVec_stack hba hbb)
  have hst : stack (fun t => y t 0) (fun t => y t 1) = y := by
    funext t j
    fin_cases j <;> rfl
  refine ⟨fun t => y t 0, fun t => y t 1, (structural_iff_solves 𝔼 hS _ _ _).mpr (hst ▸ hy),
    fun t => hay t 0, fun t => hay t 1, ⟨M, fun t ω => hM t 0 ω⟩, ⟨M, fun t ω => hM t 1 ω⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hst, hcon.1, hcon.2]

/-- **Rule (11) under (14)** (Galí 2015, p. 106): with `i_t = r^n_t + φ_π π_t + φ_y ỹ_t`
and (14), the only equilibrium with bounded adapted output gap and inflation is
`ỹ = π = 0`. -/
theorem rule11_unique {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (h14 : 0 < κ * (φπ - 1) + (1 - β) * φy)
    {rn ygap infl i : ℕ → Ω → ℝ} (hrule : ∀ t, i t = rn t + φπ • infl t + φy • ygap t)
    (he : NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl rn) (ha : 𝔼.Adapted ygap)
    (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    ygap = (fun _ => 0) ∧ infl = (fun _ => 0) := by
  have hr0 : ∀ t, i t = rn t + φπ • infl t + φy • ygap t - (fun _ => (0 : Ω → ℝ)) t :=
    fun t => by rw [hrule t, sub_zero]
  have hs := (equilibrium_iff_structural 𝔼 hσ.ne' hr0).mp he
  have hz : Structural 𝔼 β σ κ φπ φy (fun _ => 0) (fun _ => 0) (fun _ => 0) :=
    fun t => ⟨by simp, by simp⟩
  exact structural_unique 𝔼 hσ hκ hβ0 hβ1 hφπ hφy h14 hs hz ha hb (fun t => by simp)
    (fun t => by simp) hba hbb ⟨0, fun t ω => by simp⟩ ⟨0, fun t ω => by simp⟩

/-- **Rule (11) without (14)** (Galí 2015, p. 106): if (14) fails, rule (11) admits an
equilibrium with bounded adapted output gap and inflation other than `ỹ = π = 0`. -/
theorem rule11_not_unique [Nonempty Ω] {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy)
    (h14 : κ * (φπ - 1) + (1 - β) * φy ≤ 0) (rn : ℕ → Ω → ℝ) :
    ∃ ygap infl : ℕ → Ω → ℝ,
      (NKPC 𝔼 β κ ygap infl ∧
        DIS 𝔼 σ ygap (fun t => rn t + φπ • infl t + φy • ygap t) infl rn) ∧
      𝔼.Adapted ygap ∧ 𝔼.Adapted infl ∧ BoundedProc ygap ∧ BoundedProc infl ∧
      (ygap ≠ (fun _ => 0) ∨ infl ≠ (fun _ => 0)) := by
  have hz : Structural 𝔼 β σ κ φπ φy (fun _ => 0) (fun _ => 0) (fun _ => 0) :=
    fun t => ⟨by simp, by simp⟩
  obtain ⟨y', p', hs, ha, hb, hba, hbb, hne⟩ := structural_not_unique 𝔼 hσ hκ hβ0 hβ1 hφπ
    hφy h14 hz (fun t => by simp) (fun t => by simp) ⟨0, fun t ω => by simp⟩
    ⟨0, fun t ω => by simp⟩
  have hr0 : ∀ t, (fun t => rn t + φπ • p' t + φy • y' t) t
      = rn t + φπ • p' t + φy • y' t - (fun _ => (0 : Ω → ℝ)) t := fun t => by simp
  exact ⟨y', p', (equilibrium_iff_structural 𝔼 hσ.ne' hr0).mpr hs, ha, hb, hba, hbb, hne⟩

/-! ### MSV solutions for AR(1) forcing (used in Exercises 4.2 and 4.3) -/

/-- Galí (2015), p. 112 (Chapter 3, p. 66): the denominator
`(1 − βρ_u)(σ (1 − ρ_u) + φ_y) + κ (φ_π − ρ_u)` of `Λ_u`. -/
def msvDen (β σ κ φπ φy ρu : ℝ) : ℝ := (1 - β * ρu) * (σ * (1 - ρu) + φy) + κ * (φπ - ρu)

/-- Galí (2015), p. 112: `Λ_u = 1/((1 − βρ_u)(σ (1 − ρ_u) + φ_y) + κ (φ_π − ρ_u))`. -/
noncomputable def msvLambda (β σ κ φπ φy ρu : ℝ) : ℝ := 1 / msvDen β σ κ φπ φy ρu

/-- Galí (2015), p. 112: the output-gap coefficient `(1 − βρ_u) Λ_u`. -/
noncomputable def msvPsiY (β σ κ φπ φy ρu : ℝ) : ℝ := (1 - β * ρu) * msvLambda β σ κ φπ φy ρu

/-- Galí (2015), p. 112: the inflation coefficient `κ Λ_u`. -/
noncomputable def msvPsiPi (β σ κ φπ φy ρu : ℝ) : ℝ := κ * msvLambda β σ κ φπ φy ρu

/-- Galí (2015), p. 112: the denominator of `Λ_u` is
`(1 − ρ_u)((1 − βρ_u) σ + κ + β φ_y) + [κ (φ_π − 1) + (1 − β) φ_y]`. -/
theorem msvDen_eq (β σ κ φπ φy ρu : ℝ) :
    msvDen β σ κ φπ φy ρu
      = (1 - ρu) * ((1 - β * ρu) * σ + κ + β * φy) + (κ * (φπ - 1) + (1 - β) * φy) := by
  unfold msvDen
  ring

/-- Galí (2015), p. 112: under (14) and `ρ_u < 1` the denominator of `Λ_u` is positive. -/
theorem msvDen_pos {β σ κ φπ φy ρu : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρu < 1)
    (h14 : 0 < κ * (φπ - 1) + (1 - β) * φy) : 0 < msvDen β σ κ φπ φy ρu := by
  rw [msvDen_eq]
  have hbr : β * ρu < 1 := by nlinarith
  have h2 : 0 ≤ (1 - ρu) * ((1 - β * ρu) * σ + κ + β * φy) := by
    apply mul_nonneg <;> nlinarith
  linarith

/-- Galí (2015), p. 112: a scalar multiple of an AR(1) process is AR(1) with the same
persistence. -/
theorem isAR1_smul {ρu : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρu u) (c : ℝ) :
    𝔼.IsAR1 ρu (fun t => c • u t) :=
  ⟨fun t => by simp only [map_smul, hu.1 t], fun t => by
    simp only [map_smul, hu.2 t, smul_comm c ρu]⟩

/-- Galí (2015), p. 112: a scalar multiple of a bounded process is bounded. -/
theorem boundedProc_smul {u : ℕ → Ω → ℝ} (hu : BoundedProc u) (c : ℝ) :
    BoundedProc (fun t => c • u t) := by
  obtain ⟨M, hM⟩ := hu
  exact ⟨|c| * M, fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg c)⟩

/-- Galí (2015), p. 112: the sum of two bounded processes is bounded. -/
theorem boundedProc_add {u v : ℕ → Ω → ℝ} (hu : BoundedProc u) (hv : BoundedProc v) :
    BoundedProc (fun t => u t + v t) := by
  obtain ⟨M, hM⟩ := hu
  obtain ⟨N, hN⟩ := hv
  exact ⟨M + N, fun t ω => (abs_add_le _ _).trans (add_le_add (hM t ω) (hN t ω))⟩

/-- Galí (2015), p. 112: for an AR(1) forcing with persistence `ρ_u` (and a nonzero
denominator), `ỹ_t = (1 − βρ_u) Λ_u u_t`, `π_t = κ Λ_u u_t` solve the structural
equations. Restated from the Chapter 3 project. -/
theorem msv_structural {β σ κ φπ φy ρu : ℝ} (hD : msvDen β σ κ φπ φy ρu ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρu u) :
    Structural 𝔼 β σ κ φπ φy u (fun t => msvPsiY β σ κ φπ φy ρu • u t)
      (fun t => msvPsiPi β σ κ φπ φy ρu • u t) := by
  have c1 : (σ + φy) * msvPsiY β σ κ φπ φy ρu + φπ * msvPsiPi β σ κ φπ φy ρu
      = σ * (msvPsiY β σ κ φπ φy ρu * ρu) + msvPsiPi β σ κ φπ φy ρu * ρu + 1 := by
    unfold msvPsiY msvPsiPi msvLambda
    field_simp
    unfold msvDen
    ring
  have c2 : msvPsiPi β σ κ φπ φy ρu
      = β * (msvPsiPi β σ κ φπ φy ρu * ρu) + κ * msvPsiY β σ κ φπ φy ρu := by
    unfold msvPsiY msvPsiPi
    ring
  intro t
  simp only [map_smul, hu.2 t, smul_smul]
  refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination u t ω * c1
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination u t ω * c2

/-- Galí (2015), p. 112: the structural equations are linear, so solutions for two
forcing processes add up to a solution for their sum. -/
theorem structural_add {β σ κ φπ φy : ℝ} {u₁ u₂ y₁ y₂ p₁ p₂ : ℕ → Ω → ℝ}
    (h₁ : Structural 𝔼 β σ κ φπ φy u₁ y₁ p₁) (h₂ : Structural 𝔼 β σ κ φπ φy u₂ y₂ p₂) :
    Structural 𝔼 β σ κ φπ φy (fun t => u₁ t + u₂ t) (fun t => y₁ t + y₂ t)
      (fun t => p₁ t + p₂ t) := by
  intro t
  obtain ⟨a₁, b₁⟩ := h₁ t
  obtain ⟨a₂, b₂⟩ := h₂ t
  simp only [map_add, smul_add]
  constructor
  · rw [add_add_add_comm, a₁, a₂]
    abel
  · rw [b₁, b₂]
    abel

/-- Galí (2015), p. 112: scaling the forcing scales the solution. -/
theorem structural_smul {β σ κ φπ φy : ℝ} {u y p : ℕ → Ω → ℝ}
    (h : Structural 𝔼 β σ κ φπ φy u y p) (c : ℝ) :
    Structural 𝔼 β σ κ φπ φy (fun t => c • u t) (fun t => c • y t) (fun t => c • p t) := by
  intro t
  obtain ⟨a, b⟩ := h t
  simp only [map_smul]
  constructor
  · rw [smul_comm (σ + φy) c, smul_comm φπ c, ← smul_add, a, smul_comm σ c, smul_add,
      smul_add]
  · rw [b, smul_add, smul_comm β c, smul_comm κ c]

end Gali.MonetaryPolicyDesign.Ex4_1
