/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR5InertiaForward
import KeynesianStickyPrices.TidyR5GeneralBKSingular
import KeynesianStickyPrices.TidyR5QuadRoots

/-!
# The inertial rule (18.2) when `1 − σφ_{x,1} = 0`: the system drops an order

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 18, eq. (18.2), p. 427, with
`σφ_{x,1} = 1`; a completion (the book makes no determinacy claim).

With `σφ_{x,1} = 1` the expected future output gap cancels between the IS curve and the rule:
the matrix `M` multiplying `E_t y_{t+1}` in the structural form `M E_t y_{t+1} = N y_t + w_t`
(`M3`, `N3`; `y = (π, x, i_{−1})`) is singular, the system is not in Blanchard–Kahn form and
`det(λM − N)` drops to degree at most two. It is handled by the Blanchard–Kahn theorem for
singular pencils (King–Watson, Klein; `TidyR5GeneralBKSingular.determinatePencil_iff_general`,
restated from the Woodford Chapter 4 project):

* `equil182_iff_pencil`, **`determinate182_iff_pencil`**: for **all** parameters, the model with
  the rule (18.2) is exactly the pencil system `M E_t y_{t+1} = N y_t + w_t` with the lagged rate
  predetermined (`A0`, `A1`: `M3`, `N3` on the index type `Fin 2 ⊕ Fin 1`).
* `pencilPoly_eq`: `det(λM − N) = kλ³ − N₂λ² + N₁λ − φ_i` (`TidyR5InertiaForward.kk`, `N2`,
  `N1`), for all parameters.
* `generic_imp`, `imp_generic`: the pencil genericity condition holds iff
  `κ(φ_π + φ_{π,1}μ) + (φ_x + φ_{x,1}μ)(1 − βμ) ≠ 0` at `μ = 1/λ₁` (the converse under the root
  count).
* **`determinate182_singular_iff`**: for `σ, κ, β > 0` and `1 − σφ_{x,1} = 0`, the model is
  determinate iff `D₁ D₋₁ < 0` (`TidyR5InertiaForward.D1`, `Dm1`: exactly one generalised
  eigenvalue inside the unit circle, none on it; the infinite one counts as unstable;
  `TidyR5QuadRoots.count_one_iff`) and
  `κ(φ_π + φ_{π,1}μ) + (φ_x + φ_{x,1}μ)(1 − βμ) ≠ 0` at `μ = λ₂/β`.
-/

namespace Cochrane.KeynesianStickyPrices.TidyR5InertiaSingular

open Polynomial FullModel TidyR5BlanchardKahn TidyR5Inertia TidyR5InertiaForward
open TidyR5InvariantSplit TidyR5GeneralBKForward TidyR5GeneralBKPencil TidyR5GeneralBKSingular
open TidyR5QuadRoots
open scoped Matrix

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The pencil form -/

/-- The relabelling of `Fin 2 ⊕ Fin 1` (non-predetermined `π`, `x`; predetermined `i_{−1}`) as
`Fin 3`. -/
abbrev eF : Fin 2 ⊕ Fin 1 ≃ Fin 3 := finSumFinEquiv

/-- Cochrane (2023), eq. (18.2), p. 427: the matrix `M` multiplying `E_t (π, x, i)_{t+1}` in the
Phillips curve, the IS curve and the rule. -/
def M3 (σ β φπ1 φx1 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![β, 0, 0; σ, 1, -σ; -φπ1, -φx1, 1]

/-- Cochrane (2023), eq. (18.2), p. 427: the matrix `N` multiplying `(π, x, i_{−1})_t`. -/
def N3 (κ φi φπ φx : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1, -κ, 0; 0, 1, 0; φπ, φx, φi]

/-- Cochrane (2023), eq. (18.2): `M` on the index type `Fin 2 ⊕ Fin 1`. -/
def A0 (σ β φπ1 φx1 : ℝ) : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ :=
  (M3 σ β φπ1 φx1).submatrix eF eF

/-- Cochrane (2023), eq. (18.2): `N` on the index type `Fin 2 ⊕ Fin 1`. -/
def A1 (κ φi φπ φx : ℝ) : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ :=
  (N3 κ φi φπ φx).submatrix eF eF

/-- Cochrane (2023), eq. (18.2): the structural forcing `(−u_π, −u_x, u_i)` on `Fin 2 ⊕ Fin 1`. -/
def wP (u : ℕ → Fin 3 → Ω → ℝ) : ℕ → Fin 2 ⊕ Fin 1 → Ω → ℝ :=
  fun t a => (![-(u t 0), -(u t 1), u t 2] : Fin 3 → Ω → ℝ) (eF a)

/-- The relabelling sends `inl 0`, `inl 1`, `inr 0` to `0`, `1`, `2`. -/
theorem eF_vals : eF (Sum.inl 0) = 0 ∧ eF (Sum.inl 1) = 1 ∧ eF (Sum.inr 0) = 2 :=
  ⟨rfl, rfl, rfl⟩

/-- The action of a matrix on `Fin 2 ⊕ Fin 1`, written out. -/
theorem mv_three (A : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ) (v : Fin 2 ⊕ Fin 1 → Ω → ℝ)
    (a : Fin 2 ⊕ Fin 1) (ω : Ω) :
    mv A v a ω = A a (Sum.inl 0) * v (Sum.inl 0) ω + A a (Sum.inl 1) * v (Sum.inl 1) ω +
      A a (Sum.inr 0) * v (Sum.inr 0) ω := by
  simp only [mv, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_one, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]

/-- Cochrane (2023), eq. (18.2): the entries of `M` on `Fin 2 ⊕ Fin 1`. -/
theorem A0_entries (σ β φπ1 φx1 : ℝ) :
    A0 σ β φπ1 φx1 (Sum.inl 0) (Sum.inl 0) = β ∧ A0 σ β φπ1 φx1 (Sum.inl 0) (Sum.inl 1) = 0 ∧
      A0 σ β φπ1 φx1 (Sum.inl 0) (Sum.inr 0) = 0 ∧ A0 σ β φπ1 φx1 (Sum.inl 1) (Sum.inl 0) = σ ∧
      A0 σ β φπ1 φx1 (Sum.inl 1) (Sum.inl 1) = 1 ∧
      A0 σ β φπ1 φx1 (Sum.inl 1) (Sum.inr 0) = -σ ∧
      A0 σ β φπ1 φx1 (Sum.inr 0) (Sum.inl 0) = -φπ1 ∧
      A0 σ β φπ1 φx1 (Sum.inr 0) (Sum.inl 1) = -φx1 ∧
      A0 σ β φπ1 φx1 (Sum.inr 0) (Sum.inr 0) = 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Cochrane (2023), eq. (18.2): the entries of `N` on `Fin 2 ⊕ Fin 1`. -/
theorem A1_entries (κ φi φπ φx : ℝ) :
    A1 κ φi φπ φx (Sum.inl 0) (Sum.inl 0) = 1 ∧ A1 κ φi φπ φx (Sum.inl 0) (Sum.inl 1) = -κ ∧
      A1 κ φi φπ φx (Sum.inl 0) (Sum.inr 0) = 0 ∧ A1 κ φi φπ φx (Sum.inl 1) (Sum.inl 0) = 0 ∧
      A1 κ φi φπ φx (Sum.inl 1) (Sum.inl 1) = 1 ∧ A1 κ φi φπ φx (Sum.inl 1) (Sum.inr 0) = 0 ∧
      A1 κ φi φπ φx (Sum.inr 0) (Sum.inl 0) = φπ ∧ A1 κ φi φπ φx (Sum.inr 0) (Sum.inl 1) = φx ∧
      A1 κ φi φπ φx (Sum.inr 0) (Sum.inr 0) = φi :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Cochrane (2023), eq. (18.2), p. 427: for adapted disturbances, `Equil182` is the pencil
equilibrium of `M E_t y_{t+1} = N y_t + (−u_π, −u_x, u_i)` (for **all** parameters). -/
theorem equil182_iff_pencil {σ β κ φi φπ φx φπ1 φx1 : ℝ} {u : ℕ → Fin 3 → Ω → ℝ}
    (hu : VAdapted 𝔼 u) (i0 : ℝ) (y : ℕ → Fin 3 → Ω → ℝ) :
    Equil182 𝔼 σ β κ φi φπ φx φπ1 φx1 u i0 y ↔
      EquilPencil 𝔼 (A0 σ β φπ1 φx1) (A1 κ φi φπ φx) (wP u) (fun _ => i0)
        (fun t a => y t (eF a)) := by
  constructor
  · rintro ⟨hN, hI, hR, h0, ha, hbd⟩
    have hp : ∀ t, 𝔼.E t (y (t + 1) 2) = y (t + 1) 2 := by
      intro t
      rw [hR t, map_add, map_add, map_add, map_add, map_add, map_smul, map_smul, map_smul,
        map_smul, map_smul, ha t 0, ha t 1, ha t 2, 𝔼.E_E_self, 𝔼.E_E_self, hu t 2]
    refine ⟨fun t => ?_, fun t a => ha t (eF a), fun t j => ?_, fun j => ?_, ?_⟩
    · funext a ω
      have n := congrFun (hN t) ω
      have s := congrFun (hI t) ω
      have r := congrFun (hR t) ω
      have p := congrFun (hp t) ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at n s r p
      rw [Pi.add_apply, Pi.add_apply, mv_three, mv_three]
      rcases a with a | a <;> fin_cases a
      · change β * 𝔼.E t (y (t + 1) 0) ω + 0 * 𝔼.E t (y (t + 1) 1) ω +
          0 * 𝔼.E t (y (t + 1) 2) ω = 1 * y t 0 ω + -κ * y t 1 ω + 0 * y t 2 ω + -(u t 0 ω)
        linear_combination -n
      · change σ * 𝔼.E t (y (t + 1) 0) ω + 1 * 𝔼.E t (y (t + 1) 1) ω +
          -σ * 𝔼.E t (y (t + 1) 2) ω = 0 * y t 0 ω + 1 * y t 1 ω + 0 * y t 2 ω + -(u t 1 ω)
        rw [p]; linear_combination -s
      · change -φπ1 * 𝔼.E t (y (t + 1) 0) ω + -φx1 * 𝔼.E t (y (t + 1) 1) ω +
          1 * 𝔼.E t (y (t + 1) 2) ω = φπ * y t 0 ω + φx * y t 1 ω + φi * y t 2 ω + u t 2 ω
        rw [p]; linear_combination r
    · fin_cases j; exact hp t
    · fin_cases j; exact h0
    · obtain ⟨M, hM⟩ := hbd
      exact ⟨M, fun t a ω => hM t (eF a) ω⟩
  · rintro ⟨hs, ha, hp, h0, hbd⟩
    have row : ∀ t (a : Fin 2 ⊕ Fin 1) ω,
        mv (A0 σ β φπ1 φx1) (fun b => 𝔼.E t (y (t + 1) (eF b))) a ω =
          mv (A1 κ φi φπ φx) (fun b => y t (eF b)) a ω + wP u t a ω := fun t a ω => by
      have := congrFun (congrFun (hs t) a) ω
      simpa only [Pi.add_apply] using this
    have hp2 : ∀ t, 𝔼.E t (y (t + 1) 2) = y (t + 1) 2 := fun t => hp t 0
    refine ⟨fun t => ?_, fun t => ?_, fun t => ?_, h0 0, fun t i => ?_, ?_⟩
    · funext ω
      have r := row t (Sum.inl 0) ω
      rw [mv_three, mv_three] at r
      have r' : β * 𝔼.E t (y (t + 1) 0) ω + 0 * 𝔼.E t (y (t + 1) 1) ω +
          0 * 𝔼.E t (y (t + 1) 2) ω = 1 * y t 0 ω + -κ * y t 1 ω + 0 * y t 2 ω + -(u t 0 ω) := r
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination -r'
    · funext ω
      have r := row t (Sum.inl 1) ω
      have p := congrFun (hp2 t) ω
      rw [mv_three, mv_three] at r
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have r' : σ * 𝔼.E t (y (t + 1) 0) ω + 1 * 𝔼.E t (y (t + 1) 1) ω +
          -σ * 𝔼.E t (y (t + 1) 2) ω = 0 * y t 0 ω + 1 * y t 1 ω + 0 * y t 2 ω + -(u t 1 ω) := r
      rw [p] at r'
      linear_combination -r'
    · funext ω
      have r := row t (Sum.inr 0) ω
      have p := congrFun (hp2 t) ω
      rw [mv_three, mv_three] at r
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have r' : -φπ1 * 𝔼.E t (y (t + 1) 0) ω + -φx1 * 𝔼.E t (y (t + 1) 1) ω +
          1 * 𝔼.E t (y (t + 1) 2) ω = φπ * y t 0 ω + φx * y t 1 ω + φi * y t 2 ω + u t 2 ω := r
      rw [p] at r'
      linear_combination r'
    · have := ha t (eF.symm i)
      simpa using this
    · obtain ⟨M, hM⟩ := hbd
      exact ⟨M, fun t i ω => by simpa using hM t (eF.symm i) ω⟩

/-- Cochrane (2023), eq. (18.2): the disturbances `(u_π, u_x, u_i)` recovered from a structural
forcing on `Fin 2 ⊕ Fin 1`. -/
def uOf (w : ℕ → Fin 2 ⊕ Fin 1 → Ω → ℝ) : ℕ → Fin 3 → Ω → ℝ :=
  fun t => ![-(w t (Sum.inl 0)), -(w t (Sum.inl 1)), w t (Sum.inr 0)]

/-- `wP` inverts `uOf`. -/
theorem wP_uOf (w : ℕ → Fin 2 ⊕ Fin 1 → Ω → ℝ) : wP (uOf w) = w := by
  funext t a
  rcases a with a | a <;> fin_cases a
  · change -(-(w t (Sum.inl 0))) = _; rw [neg_neg]; rfl
  · change -(-(w t (Sum.inl 1))) = _; rw [neg_neg]; rfl
  · rfl

/-- Cochrane (2023), eq. (18.2), p. 427: for **all** parameters, determinacy of the model with
the rule (18.2) is Blanchard–Kahn determinacy of the pencil system
`M E_t y_{t+1} = N y_t + w_t` with the lagged rate predetermined. -/
theorem determinate182_iff_pencil (σ β κ φi φπ φx φπ1 φx1 : ℝ) :
    Determinate182 𝔼 σ β κ φi φπ φx φπ1 φx1 ↔
      DeterminatePencil 𝔼 (A0 σ β φπ1 φx1) (A1 κ φi φπ φx) := by
  constructor
  · intro h w hwb hwa x0
    have hub : VBounded (uOf w) := by
      obtain ⟨M, hM⟩ := hwb
      refine ⟨M, fun t k ω => ?_⟩
      fin_cases k
      · change |-(w t (Sum.inl 0) ω)| ≤ M; rw [abs_neg]; exact hM t _ ω
      · change |-(w t (Sum.inl 1) ω)| ≤ M; rw [abs_neg]; exact hM t _ ω
      · exact hM t _ ω
    have hua : VAdapted 𝔼 (uOf w) := by
      intro t k
      fin_cases k
      · change 𝔼.E t (-(w t (Sum.inl 0))) = -(w t (Sum.inl 0)); rw [map_neg, hwa t]
      · change 𝔼.E t (-(w t (Sum.inl 1))) = -(w t (Sum.inl 1)); rw [map_neg, hwa t]
      · exact hwa t _
    have hx0 : (fun _ : Fin 1 => x0 0) = x0 := by funext j; fin_cases j; rfl
    obtain ⟨y, hy, huniq⟩ := h _ hub hua (x0 0)
    have hiff := fun y => equil182_iff_pencil 𝔼 (σ := σ) (β := β) (κ := κ) (φi := φi)
      (φπ := φπ) (φx := φx) (φπ1 := φπ1) (φx1 := φx1) hua (x0 0) y
    rw [wP_uOf, hx0] at hiff
    refine ⟨fun t a => y t (eF a), (hiff y).mp hy, fun y'' hy'' => ?_⟩
    have e : (fun t a => (fun t k => y'' t (eF.symm k)) t (eF a)) = y'' := by
      funext t a; simp
    have h3 : EquilPencil 𝔼 (A0 σ β φπ1 φx1) (A1 κ φi φπ φx) w x0
        (fun t a => (fun t k => y'' t (eF.symm k)) t (eF a)) := by rw [e]; exact hy''
    have := huniq _ ((hiff (fun t k => y'' t (eF.symm k))).mpr h3)
    rw [← e, this]
  · intro h u hub hua i0
    have hwb : BoundedV (wP u) := by
      obtain ⟨M, hM⟩ := hub
      refine ⟨M, fun t a ω => ?_⟩
      rcases a with a | a <;> fin_cases a
      · change |-(u t 0 ω)| ≤ M; rw [abs_neg]; exact hM t 0 ω
      · change |-(u t 1 ω)| ≤ M; rw [abs_neg]; exact hM t 1 ω
      · exact hM t 2 ω
    have hwa : AdaptedV 𝔼 (wP u) := by
      intro t a
      rcases a with a | a <;> fin_cases a
      · change 𝔼.E t (-(u t 0)) = -(u t 0); rw [map_neg, hua t 0]
      · change 𝔼.E t (-(u t 1)) = -(u t 1); rw [map_neg, hua t 1]
      · exact hua t 2
    obtain ⟨y', hy', huniq⟩ := h _ hwb hwa (fun _ => i0)
    have hiff := fun y => equil182_iff_pencil 𝔼 (σ := σ) (β := β) (κ := κ) (φi := φi)
      (φπ := φπ) (φx := φx) (φπ1 := φπ1) (φx1 := φx1) hua i0 y
    have e : (fun t a => (fun t k => y' t (eF.symm k)) t (eF a)) = y' := by
      funext t a; simp
    have h3 : EquilPencil 𝔼 (A0 σ β φπ1 φx1) (A1 κ φi φπ φx) (wP u) (fun _ => i0)
        (fun t a => (fun t k => y' t (eF.symm k)) t (eF a)) := by rw [e]; exact hy'
    refine ⟨fun t k => y' t (eF.symm k), (hiff _).mpr h3, fun y3 hy3 => ?_⟩
    have := huniq _ ((hiff y3).mp hy3)
    funext t k
    rw [← this]
    simp

/-! ### The generalised eigenvalues -/

/-- Cochrane (2023), eq. (18.2): `λA₀ − A₁` is `λM − N` relabelled. -/
theorem pencil_submatrix (σ β κ φi φπ φx φπ1 φx1 r : ℝ) :
    r • A0 σ β φπ1 φx1 - A1 κ φi φπ φx = (r • M3 σ β φπ1 φx1 - N3 κ φi φπ φx).submatrix eF eF := by
  ext a b
  rfl

/-- Cochrane (2023), eq. (18.2), p. 427: for **all** parameters,
`det(λM − N) = kλ³ − N₂λ² + N₁λ − φ_i`, `k = β(1 − σφ_{x,1})`. -/
theorem pencilPoly_eq (σ β κ φi φπ φx φπ1 φx1 : ℝ) :
    pencilPoly (A0 σ β φπ1 φx1) (A1 κ φi φπ φx) =
      C (kk σ β φx1) * X ^ 3 + C (-N2 σ β κ φi φx φπ1 φx1) * X ^ 2 +
        C (N1 σ β κ φi φπ φx) * X + C (-φi) := by
  refine Polynomial.funext fun r => ?_
  rw [eval_pencilPoly, pencil_submatrix, Matrix.det_submatrix_equiv_self, Matrix.det_fin_three]
  simp [M3, N3, kk, N2, N1]
  ring

/-- Cochrane (2023), eq. (18.2): a kernel vector of `μM − N` gives one of `μA₀ − A₁`. -/
theorem mulVec_relabel (σ β κ φi φπ φx φπ1 φx1 μ : ℝ) (w : Fin 3 → ℝ) :
    (μ • A0 σ β φπ1 φx1 - A1 κ φi φπ φx) *ᵥ (w ∘ eF) =
      ((μ • M3 σ β φπ1 φx1 - N3 κ φi φπ φx) *ᵥ w) ∘ eF := by
  rw [pencil_submatrix, Matrix.submatrix_mulVec_equiv]
  congr 2
  funext k
  simp

/-- Cochrane (2023), eq. (18.2): a kernel vector of `μA₀ − A₁` with `|μ| ≤ 1` starts a bounded
deterministic solution `μᵗ v` of `A₀ y_{t+1} = A₁ y_t`. -/
theorem pencilBounded_of_kernel {A B : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ} {μ : ℝ}
    (hμ : |μ| ≤ 1) {v : Fin 2 ⊕ Fin 1 → ℝ} (hv : (μ • A - B) *ᵥ v = 0) :
    PencilBounded A B v := by
  have hAB : μ • (A *ᵥ v) = B *ᵥ v := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, sub_eq_zero] at hv
    exact hv
  refine ⟨fun t => μ ^ t • v, by simp, ⟨∑ i, |v i|, fun t i => ?_⟩, fun t => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
    calc |μ| ^ t * |v i| ≤ 1 * |v i| :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (abs_nonneg _) hμ) (abs_nonneg _)
      _ = |v i| := one_mul _
      _ ≤ ∑ j, |v j| := Finset.single_le_sum (f := fun j => |v j|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  · rw [Matrix.mulVec_smul, Matrix.mulVec_smul, pow_succ, mul_smul, hAB]

/-- Cochrane (2023), eq. (18.2): the rows of `(μM − N)w = 0` when the lagged-rate component of
`w` is zero, and the conclusion: for `|μ| < 1` and
`κ(φ_π + φ_{π,1}/λ₁) + (φ_x + φ_{x,1}/λ₁)(1 − β/λ₁) ≠ 0`, `w = 0`. -/
theorem kernel_zero {σ β κ φi φπ φx φπ1 φx1 μ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hμ : |μ| < 1) {w : Fin 3 → ℝ} (hk : (μ • M3 σ β φπ1 φx1 - N3 κ φi φπ φx) *ᵥ w = 0)
    (h2 : w 2 = 0)
    (hexpr : κ * (φπ + φπ1 * (lam1 σ β κ)⁻¹) + (φx + φx1 * (lam1 σ β κ)⁻¹) *
      (1 - β * (lam1 σ β κ)⁻¹) ≠ 0) : w = 0 := by
  have ha := mul_pos hσ hκ
  have r0 : (μ * β - 1) * w 0 + (μ * 0 - -κ) * w 1 + (μ * 0 - 0) * w 2 = 0 := by
    have := congrFun hk 0
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.zero_apply] at this
    exact this
  have r1 : (μ * σ - 0) * w 0 + (μ * 1 - 1) * w 1 + (μ * -σ - 0) * w 2 = 0 := by
    have := congrFun hk 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.zero_apply] at this
    exact this
  have r2 : (μ * -φπ1 - φπ) * w 0 + (μ * -φx1 - φx) * w 1 + (μ * 1 - φi) * w 2 = 0 := by
    have := congrFun hk 2
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.zero_apply] at this
    exact this
  rw [h2] at r0 r1 r2
  have hq : ((1 - β * μ) * (1 - μ) - σ * κ * μ) * w 0 = 0 := by
    linear_combination (μ - 1) * r0 - κ * r1
  by_cases hw0 : w 0 = 0
  · have hw1 : w 1 = 0 := by
      rw [hw0] at r0
      have : κ * w 1 = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hκ.ne'
      · exact h
    funext j
    fin_cases j
    · exact hw0
    · exact hw1
    · exact h2
  · exfalso
    have hq0 : (1 - β * μ) * (1 - μ) - σ * κ * μ = 0 := (mul_eq_zero.mp hq).resolve_right hw0
    have hμm := peg_root ha hβ hμ hq0
    rw [hμm] at r0 r2
    apply hexpr
    have key : (κ * (φπ + φπ1 * (lam1 σ β κ)⁻¹) + (φx + φx1 * (lam1 σ β κ)⁻¹) *
        (1 - β * (lam1 σ β κ)⁻¹)) * w 0 = 0 := by
      linear_combination -κ * r2 - (φx + φx1 * (lam1 σ β κ)⁻¹) * r0
    exact (mul_eq_zero.mp key).resolve_right hw0

/-- `1/λ₁` is a root of the peg polynomial `(1 − βμ)(1 − μ) − σκμ`. -/
theorem peg_root_lam1 {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) :
    (1 - β * (lam1 σ β κ)⁻¹) * (1 - (lam1 σ β κ)⁻¹) - σ * κ * (lam1 σ β κ)⁻¹ = 0 := by
  have hs := lam_sum σ β κ
  have hp := lam_prod ha hβ
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  have : lam1 σ β κ * (lam1 σ β κ)⁻¹ = 1 := mul_inv_cancel₀ hl0
  linear_combination (lam2 σ β κ * (lam1 σ β κ)⁻¹ - 1) * this -
    (lam1 σ β κ)⁻¹ ^ 2 * hp + (lam1 σ β κ)⁻¹ * hs

/-- Cochrane (2023), eq. (18.2), p. 427: if the pencil genericity condition holds,
`κ(φ_π + φ_{π,1}μ) + (φ_x + φ_{x,1}μ)(1 − βμ) ≠ 0` at `μ = 1/λ₁` (otherwise
`(μ*)ᵗ (κ, 1 − βμ*, 0)` is a nonzero bounded solution with zero lagged rate). -/
theorem generic_imp {σ β κ φi φπ φx φπ1 φx1 : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hg : GenericPencil (A0 σ β φπ1 φx1) (A1 κ φi φπ φx)) :
    κ * (φπ + φπ1 * (lam1 σ β κ)⁻¹) + (φx + φx1 * (lam1 σ β κ)⁻¹) *
      (1 - β * (lam1 σ β κ)⁻¹) ≠ 0 := by
  have ha := mul_pos hσ hκ
  have hl1 := one_lt_lam1 ha hβ
  set m := (lam1 σ β κ)⁻¹ with hm
  have hm0 : 0 < m := inv_pos.mpr (one_pos.trans hl1)
  have hm1 : m < 1 := inv_lt_one_of_one_lt₀ hl1
  have hqm := peg_root_lam1 ha hβ
  rw [← hm] at hqm
  intro hexpr
  set w3 : Fin 3 → ℝ := ![κ, 1 - β * m, 0] with hw3
  have hk : (m • M3 σ β φπ1 φx1 - N3 κ φi φπ φx) *ᵥ w3 = 0 := by
    funext j
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.zero_apply]
    fin_cases j
    · change (m * β - 1) * κ + (m * 0 - -κ) * (1 - β * m) + (m * 0 - 0) * 0 = 0
      ring
    · change (m * σ - 0) * κ + (m * 1 - 1) * (1 - β * m) + (m * -σ - 0) * 0 = 0
      linear_combination -hqm
    · change (m * -φπ1 - φπ) * κ + (m * -φx1 - φx) * (1 - β * m) + (m * 1 - φi) * 0 = 0
      linear_combination -hexpr
  have hb := pencilBounded_of_kernel (abs_le.mpr ⟨by linarith, hm1.le⟩)
    ((mulVec_relabel σ β κ φi φπ φx φπ1 φx1 m w3).trans (by rw [hk]; rfl))
  have h0 := hg _ hb (fun j => by fin_cases j; rfl)
  have := congrFun h0 (Sum.inl 0)
  change κ = 0 at this
  exact hκ.ne' this

/-- Cochrane (2023), eq. (18.2), p. 427: if the pencil is regular, has no generalised eigenvalue
on the unit circle and exactly one inside, and a real stable root `ρ`, then
`κ(φ_π + φ_{π,1}/λ₁) + (φ_x + φ_{x,1}/λ₁)(1 − β/λ₁) ≠ 0` implies the pencil genericity condition
(the bounded deterministic solutions form the line through the stable eigen-solution). -/
theorem imp_generic {σ β κ φi φπ φx φπ1 φx1 : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hreg : pencilPoly (A0 σ β φπ1 φx1) (A1 κ φi φπ φx) ≠ 0)
    (hnu : ∀ μ ∈ ((pencilPoly (A0 σ β φπ1 φx1) (A1 κ φi φπ φx)).map
      Complex.ofRealHom).roots, ‖μ‖ ≠ 1)
    (hc : Multiset.card (((pencilPoly (A0 σ β φπ1 φx1) (A1 κ φi φπ φx)).map
      Complex.ofRealHom).roots.filter (fun μ => ‖μ‖ < 1)) = 1)
    {ρ : ℝ} (hρ : |ρ| < 1) (hρr : (pencilPoly (A0 σ β φπ1 φx1) (A1 κ φi φπ φx)).eval ρ = 0)
    (hexpr : κ * (φπ + φπ1 * (lam1 σ β κ)⁻¹) + (φx + φx1 * (lam1 σ β κ)⁻¹) *
      (1 - β * (lam1 σ β κ)⁻¹) ≠ 0) :
    GenericPencil (A0 σ β φπ1 φx1) (A1 κ φi φπ φx) := by
  obtain ⟨c, hB⟩ := exists_regular_point hreg
  obtain ⟨m, P, Q, Ni, hFit⟩ := exists_fitting ((c • A0 σ β φπ1 φx1 - A1 κ φi φπ φx)⁻¹ *
    A0 σ β φπ1 φx1)
  have hF : Fitting ((c • A0 σ β φπ1 φx1 - A1 κ φi φπ φx)⁻¹ * A0 σ β φπ1 φx1) m P Q Ni := hFit
  have hnuA := (noUnit_ahat_iff hB hF).mpr hnu
  have hfr : Module.finrank ℝ (boundedOrbits (ahat c P Q Ni)) = 1 := by
    rw [finrank_eq_stableCount hnuA, stableCount_ahat hB hF, hc]
  -- the stable eigen-solution
  rw [eval_pencilPoly] at hρr
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hρr
  have hwb : w ∈ boundedOrbits (ahat c P Q Ni) :=
    (mem_boundedOrbits_ahat hB hF w).mpr (pencilBounded_of_kernel hρ.le hw)
  intro v hv hvl
  have hvb : v ∈ boundedOrbits (ahat c P Q Ni) := (mem_boundedOrbits_ahat hB hF v).mpr hv
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨w, hwb⟩ : boundedOrbits (ahat c P Q Ni))
    (by intro h; exact hw0 (congrArg Subtype.val h))).mp hfr ⟨v, hvb⟩
  have hva : a • w = v := congrArg Subtype.val ha
  by_cases ha0 : a = 0
  · rw [← hva, ha0, zero_smul]
  · exfalso
    have hwl : w (Sum.inr 0) = 0 := by
      have := congrFun hva (Sum.inr 0)
      rw [hvl 0, Pi.smul_apply, smul_eq_mul] at this
      exact (mul_eq_zero.mp this).resolve_left ha0
    set w3 : Fin 3 → ℝ := w ∘ eF.symm with hw3
    have hwe : w = w3 ∘ eF := by funext k; simp [hw3]
    have hk : (ρ • M3 σ β φπ1 φx1 - N3 κ φi φπ φx) *ᵥ w3 = 0 := by
      have h1 := mulVec_relabel σ β κ φi φπ φx φπ1 φx1 ρ w3
      rw [← hwe, hw] at h1
      funext j
      have := congrFun h1 (eF.symm j)
      simp only [Function.comp_apply, Equiv.apply_symm_apply, Pi.zero_apply] at this
      exact this.symm
    have h0 := kernel_zero hσ hκ hβ hρ hk (by rw [hw3]; exact hwl) hexpr
    apply hw0
    rw [hwe, h0]
    rfl

/-! ### The characterisation when `1 − σφ_{x,1} = 0` -/

/-- Cochrane (2023), eq. (18.2): `det(M − N) = D₁` and `det(−M − N) = D₋₁` in the notation of
TidyR5InertiaForward: `k − N₂ + N₁ − φ_i = D₁` and `−k − N₂ − N₁ − φ_i = D₋₁`. -/
theorem D_identities (σ β κ φi φπ φx φπ1 φx1 : ℝ) :
    kk σ β φx1 - N2 σ β κ φi φx φπ1 φx1 + N1 σ β κ φi φπ φx - φi =
        D1 σ β κ φi φπ φx φπ1 φx1 ∧
      -kk σ β φx1 - N2 σ β κ φi φx φπ1 φx1 - N1 σ β κ φi φπ φx - φi =
        Dm1 σ β κ φi φπ φx φπ1 φx1 := by
  simp only [kk, N2, N1, D1, Dm1]
  constructor <;> ring

/-- **Determinacy when `1 − σφ_{x,1} = 0`** (Cochrane (2023), eq. (18.2), p. 427; the book makes
no claim): for `σ, κ, β > 0` and `σφ_{x,1} = 1`, under any expectation system on a nonempty
state space, the model with the rule (18.2) is determinate iff `D₁ D₋₁ < 0` (exactly one
generalised eigenvalue of the degenerate pencil inside the unit circle, none on it; the
infinite eigenvalue is unstable) and `κ(φ_π + φ_{π,1}μ) + (φ_x + φ_{x,1}μ)(1 − βμ) ≠ 0` at
`μ = λ₂/β`. -/
theorem determinate182_singular_iff [Nonempty Ω] {σ β κ φi φπ φx φπ1 φx1 : ℝ} (hσ : 0 < σ)
    (hκ : 0 < κ) (hβ : 0 < β) (hg0 : 1 - σ * φx1 = 0) :
    Determinate182 𝔼 σ β κ φi φπ φx φπ1 φx1 ↔
      D1 σ β κ φi φπ φx φπ1 φx1 * Dm1 σ β κ φi φπ φx φπ1 φx1 < 0 ∧
        κ * (φπ + φπ1 * (lam2 σ β κ / β)) + (φx + φx1 * (lam2 σ β κ / β)) *
          (1 - β * (lam2 σ β κ / β)) ≠ 0 := by
  have hk : kk σ β φx1 = 0 := by simp only [kk, hg0, mul_zero]
  obtain ⟨hD1, hDm1⟩ := D_identities σ β κ φi φπ φx φπ1 φx1
  rw [hk] at hD1 hDm1
  have hP : pencilPoly (A0 σ β φπ1 φx1) (A1 κ φi φπ φx) =
      C (-N2 σ β κ φi φx φπ1 φx1) * X ^ 2 + C (N1 σ β κ φi φπ φx) * X + C (-φi) := by
    rw [pencilPoly_eq, hk, C_0, zero_mul, zero_add]
  have hev : (C (-N2 σ β κ φi φx φπ1 φx1) * X ^ 2 + C (N1 σ β κ φi φπ φx) * X +
      C (-φi)).eval 1 * (C (-N2 σ β κ φi φx φπ1 φx1) * X ^ 2 + C (N1 σ β κ φi φπ φx) * X +
      C (-φi)).eval (-1) = D1 σ β κ φi φπ φx φπ1 φx1 * Dm1 σ β κ φi φπ φx φπ1 φx1 := by
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
    rw [← hD1, ← hDm1]
    ring
  have hcount := count_one_iff (-N2 σ β κ φi φx φπ1 φx1) (N1 σ β κ φi φπ φx) (-φi)
  rw [hev] at hcount
  rw [determinate182_iff_pencil, determinatePencil_iff_general, ← lam1_inv_eq (mul_pos hσ hκ) hβ,
    Fintype.card_fin]
  constructor
  · rintro ⟨hreg, hnu, hc, hgen⟩
    rw [hP] at hreg hnu hc
    exact ⟨hcount.mp ⟨hreg, hnu, hc⟩, generic_imp hσ hκ hβ hgen⟩
  · rintro ⟨hD, hexpr⟩
    obtain ⟨hreg, hnu, hc⟩ := hcount.mpr hD
    have hroot : ∃ ρ : ℝ, -1 < ρ ∧ ρ < 1 ∧
        (pencilPoly (A0 σ β φπ1 φx1) (A1 κ φi φπ φx)).eval ρ = 0 := by
      apply exists_root_Ioo
      rw [hP, hev]
      exact hD
    obtain ⟨ρ, hρ1, hρ2, hρ⟩ := hroot
    rw [← hP] at hreg hnu hc
    exact ⟨hreg, hnu, hc, imp_generic hσ hκ hβ hreg hnu hc (abs_lt.mpr ⟨hρ1, hρ2⟩) hρ hexpr⟩

end Cochrane.KeynesianStickyPrices.TidyR5InertiaSingular
