/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyWagesPrices.GapForm
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The equilibrium system under a simple interest rate rule

Galí (2015), Chapter 6, §6.2, pp. 173–175. Closing the gap form (18), (20), (21),
(22) with the rule (23) `i_t = ρ + φ_p π^p_t + φ_w π^w_t + φ_y ŷ_t + v_t` gives the
four-variable system (24) `A₀ x_t = A₁ E_t x_{t+1} + B₀ u_t` with
`x_t = [ỹ_t, π^p_t, π^w_t, ω̃_{t−1}]` and `u_t = [r̂ⁿ_t − v_t − φ_y ŷⁿ_t, Δωⁿ_t]`.

Convention: the fourth state is the LAGGED real wage gap; the process `wl` has
`wl t = ω̃_{t−1}`, so `ω̃_t = wl (t + 1)` and `wl 0 = ω̃_{−1}` is the initial
condition. `r̂ⁿ = rⁿ − ρ` is the natural rate in deviation from `ρ`.

## Main results

* `equilibrium_iff_matrixEq`: the model equations (18), (20), (21), (22), (23)
  are equivalent to the matrix equation (24) (given that `ω̃_t` is known at `t`).
* `zeroPath_iff`, `zeroPath_exists_iff`: the path `ỹ = π^p = π^w = 0` solves (24),
  with `ω̃_{−1} = 0`, iff `u_{1} ≡ 0` and `Δωⁿ ≡ 0`.
* `zeroPath_iff_primitives` (corrected p. 174 statement): with AR(1) technology
  (`ρ_a ≠ 1`), the zero path solves (24) iff the natural wage is constant at its
  steady state AND `v = r̂ⁿ`, for every `φ_y`. `zeroPath_solves_any_phiY`: the
  printed hypothesis `φ_y = 0` is redundant; `zeroPath_fails_v_eq_rn`: the printed
  `v = rⁿ` (without hat) does not work when `ρ ≠ 0`.
* `det_A0_sub_A1_eq`: `det(A₀ − A₁) = −λ_p λ_w Θ_y (LHS − 1)` with
  `LHS = φ_p + φ_w + φ_y (1 − β)/Θ_y (1/λ_p + 1/λ_w)` (the p. 174 condition).
* `one_eigenvalue_iff`: `1` is an eigenvalue of `A₀⁻¹ A₁` iff `LHS = 1`, i.e.
  exactly on the determinacy boundary.
* `detCondition_phiY_zero`, `detCondition_iff_threshold`, `threshold_strictAnti`:
  for `φ_y = 0` the condition reads `φ_p + φ_w > 1`; the threshold on
  `φ_p + φ_w` strictly decreases in `φ_y` (Figure 6.1).

The determinacy theorem itself (eigenvalue location) is in another module.
-/

namespace Gali.StickyWagesPrices.System

open GapForm
open scoped Matrix

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The rule (23) and the matrix form (24) -/

/-- Galí (2015), eq. (23), p. 173: the interest rate rule
`i_t = ρ + φ_p π^p_t + φ_w π^w_t + φ_y ŷ_t + v_t`. -/
def Rule (ρ φp φw φy : ℝ) (i pp pw yhat v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = (fun _ => ρ) + φp • pp t + φw • pw t + φy • yhat t + v t

/-- Galí (2015), eq. (21), p. 172, in the lagged convention `wl t = ω̃_{t−1}`:
`ω̃_t = ω̃_{t−1} + π^w_t − π^p_t − Δωⁿ_t`. -/
def WageGapLaw (wl pp pw dwn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, wl (t + 1) = wl t + pw t - pp t - dwn t

/-- Galí (2015), eqs. (18), (20), (21), (22), pp. 172–173: the non-policy block in
gaps, with `ω̃_t = wl (t + 1)`. -/
def Equilibrium (σ β κp κw lamP lamW : ℝ) (ygap pp pw wl i rn dwn : ℕ → Ω → ℝ) : Prop :=
  DISGap 𝔼 σ ygap i pp rn ∧ PriceGapNKPC 𝔼 β κp lamP pp ygap (fun t => wl (t + 1)) ∧
    WageGapNKPC 𝔼 β κw lamW pw ygap (fun t => wl (t + 1)) ∧ WageGapLaw wl pp pw dwn

/-- Galí (2015), eq. (24), p. 173: the matrix `A₀ʷ`. -/
def A0 (σ φp φw φy κp κw : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![σ + φy, φp, φw, 0; -κp, 1, 0, 0; -κw, 0, 1, 0; 0, -1, 1, 1]

/-- Galí (2015), eq. (24), p. 173: the matrix `A₁ʷ`. -/
def A1 (σ β lamP lamW : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![σ, 1, 0, 0; 0, β, 0, lamP; 0, 0, β, -lamW; 0, 0, 0, 1]

/-- Galí (2015), eq. (24), p. 173: the matrix `B₀ʷ`. -/
def B0 : Matrix (Fin 4) (Fin 2) ℝ := !![1, 0; 0, 0; 0, 0; 0, 1]

/-- Galí (2015), eq. (24), p. 173: the state `x_t = [ỹ_t, π^p_t, π^w_t, ω̃_{t−1}]`. -/
def stateVec (ygap pp pw wl : ℕ → Ω → ℝ) : ℕ → Fin 4 → Ω → ℝ :=
  fun t => ![ygap t, pp t, pw t, wl t]

/-- Galí (2015), eq. (24), p. 173: the forcing vector `u_t = [u₁_t, Δωⁿ_t]`. -/
def shockVec (u1 dwn : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![u1 t, dwn t]

/-- Galí (2015), eq. (24), p. 173: `A₀ x_t = A₁ E_t x_{t+1} + B₀ u_t` at every date. -/
def MatrixEq (A₀ A₁ : Matrix (Fin 4) (Fin 4) ℝ) (B₀ : Matrix (Fin 4) (Fin 2) ℝ)
    (x : ℕ → Fin 4 → Ω → ℝ) (u : ℕ → Fin 2 → Ω → ℝ) : Prop :=
  ∀ t i, ∑ j, A₀ i j • x t j = ∑ j, A₁ i j • 𝔼.E t (x (t + 1) j) + ∑ k, B₀ i k • u t k

/-- Galí (2015), eq. (24), p. 173: the matrix equation written row by row. -/
theorem matrixEq_iff_rows {σ β φp φw φy κp κw lamP lamW : ℝ} (ygap pp pw wl u1 dwn : ℕ → Ω → ℝ) :
    MatrixEq 𝔼 (A0 σ φp φw φy κp κw) (A1 σ β lamP lamW) B0 (stateVec ygap pp pw wl)
        (shockVec u1 dwn) ↔
      ∀ t, ((σ + φy) • ygap t + φp • pp t + φw • pw t
          = σ • 𝔼.E t (ygap (t + 1)) + 𝔼.E t (pp (t + 1)) + u1 t) ∧
        (-(κp • ygap t) + pp t = β • 𝔼.E t (pp (t + 1)) + lamP • 𝔼.E t (wl (t + 1))) ∧
        (-(κw • ygap t) + pw t = β • 𝔼.E t (pw (t + 1)) - lamW • 𝔼.E t (wl (t + 1))) ∧
        (-pp t + pw t + wl t = 𝔼.E t (wl (t + 1)) + dwn t) := by
  unfold MatrixEq
  constructor
  · intro h t
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [Fin.sum_univ_four, A0, A1, B0, stateVec, shockVec, sub_eq_add_neg] using h t 0
    · simpa [Fin.sum_univ_four, A0, A1, B0, stateVec, shockVec, sub_eq_add_neg] using h t 1
    · simpa [Fin.sum_univ_four, A0, A1, B0, stateVec, shockVec, sub_eq_add_neg] using h t 2
    · simpa [Fin.sum_univ_four, A0, A1, B0, stateVec, shockVec, sub_eq_add_neg] using h t 3
  · rintro h t i
    obtain ⟨h0, h1, h2, h3⟩ := h t
    fin_cases i
    · simpa [Fin.sum_univ_four, A0, A1, B0, stateVec, shockVec, sub_eq_add_neg] using h0
    · simpa [Fin.sum_univ_four, A0, A1, B0, stateVec, shockVec, sub_eq_add_neg] using h1
    · simpa [Fin.sum_univ_four, A0, A1, B0, stateVec, shockVec, sub_eq_add_neg] using h2
    · simpa [Fin.sum_univ_four, A0, A1, B0, stateVec, shockVec, sub_eq_add_neg] using h3

/-- Galí (2015), eq. (24), p. 173: given the rule (23) with `ŷ = ỹ + ŷⁿ` and a real
wage gap known at each date (`E_t ω̃_t = ω̃_t`), the model equations (18), (20),
(21), (22) are equivalent to the matrix equation (24) with
`u_t = [r̂ⁿ_t − v_t − φ_y ŷⁿ_t, Δωⁿ_t]`, `r̂ⁿ_t = rⁿ_t − ρ`. -/
theorem equilibrium_iff_matrixEq {σ β ρ φp φw φy κp κw lamP lamW : ℝ} (hσ : σ ≠ 0)
    {ygap pp pw wl i rn dwn v yhat ynhat : ℕ → Ω → ℝ}
    (hrule : Rule ρ φp φw φy i pp pw yhat v) (hyhat : ∀ t, yhat t = ygap t + ynhat t)
    (hadapt : ∀ t, 𝔼.E t (wl (t + 1)) = wl (t + 1)) :
    Equilibrium 𝔼 σ β κp κw lamP lamW ygap pp pw wl i rn dwn ↔
      MatrixEq 𝔼 (A0 σ φp φw φy κp κw) (A1 σ β lamP lamW) B0 (stateVec ygap pp pw wl)
        (shockVec (fun t => rn t - (fun _ => ρ) - v t - φy • ynhat t) dwn) := by
  rw [matrixEq_iff_rows]
  unfold Equilibrium DISGap PriceGapNKPC WageGapNKPC WageGapLaw
  simp only [hadapt]
  constructor
  · rintro ⟨hd, h18, h20, h21⟩ t
    refine ⟨?_, ?_, ?_, ?_⟩
    · funext x
      have e1 := congrFun (hd t) x
      have e2 := congrFun (hrule t) x
      have e3 := congrFun (hyhat t) x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 ⊢
      rw [e3] at e2
      rw [e2] at e1
      field_simp at e1
      linear_combination e1
    · funext x
      have e := congrFun (h18 t) x
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at e ⊢
      linear_combination e
    · funext x
      have e := congrFun (h20 t) x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
        at e ⊢
      linear_combination e
    · funext x
      have e := congrFun (h21 t) x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply] at e ⊢
      linear_combination -e
  · intro h
    refine ⟨fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
    · funext x
      have e1 := congrFun (h t).1 x
      have e2 := congrFun (hrule t) x
      have e3 := congrFun (hyhat t) x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 ⊢
      rw [e3] at e2
      rw [e2]
      field_simp
      linear_combination e1
    · funext x
      have e := congrFun (h t).2.1 x
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at e ⊢
      linear_combination e
    · funext x
      have e := congrFun (h t).2.2.1 x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
        at e ⊢
      linear_combination e
    · funext x
      have e := congrFun (h t).2.2.2 x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply] at e ⊢
      linear_combination -e

/-- Galí (2015), p. 173: `{u_t}` is a linear transformation of the shifters
`{a_t, z_t, v_t}`: with `rⁿ_t = ρ − σ (1 − ρ_a) ψ_ya a_t + (1 − ρ_z) z_t` and
`ŷⁿ_t = ψ_ya a_t`, `u₁_t = −(σ (1 − ρ_a) + φ_y) ψ_ya a_t + (1 − ρ_z) z_t − v_t`. -/
theorem u1_linear (σ ρ ρa ρz ψya φy : ℝ) (a z v : ℕ → Ω → ℝ) (t : ℕ) :
    ((fun _ => ρ) - (σ * (1 - ρa) * ψya) • a t + (1 - ρz) • z t) - (fun _ => ρ) - v t
        - φy • (ψya • a t)
      = -((σ * (1 - ρa) + φy) * ψya) • a t + (1 - ρz) • z t - v t := by
  funext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### When is `ỹ = π^p = π^w = 0` an equilibrium? (p. 174) -/

/-- Galí (2015), p. 174: with `λ_p ≠ 0` and a real wage gap known at each date,
the path `ỹ = π^p = π^w = 0` (with lagged gap `wl`) solves (24) iff
`u₁ ≡ 0`, `ω̃_t = 0` for all `t ≥ 0`, `Δωⁿ_0 = ω̃_{−1}` and `Δωⁿ_t = 0` for `t ≥ 1`. -/
theorem zeroPath_iff {σ β φp φw φy κp κw lamP lamW : ℝ} (hlamP : lamP ≠ 0)
    {wl u1 dwn : ℕ → Ω → ℝ} (hadapt : ∀ t, 𝔼.E t (wl (t + 1)) = wl (t + 1)) :
    MatrixEq 𝔼 (A0 σ φp φw φy κp κw) (A1 σ β lamP lamW) B0
        (stateVec (fun _ => 0) (fun _ => 0) (fun _ => 0) wl) (shockVec u1 dwn) ↔
      (∀ t, u1 t = 0) ∧ (∀ t, wl (t + 1) = 0) ∧ dwn 0 = wl 0 ∧ ∀ t, dwn (t + 1) = 0 := by
  rw [matrixEq_iff_rows]
  simp only [hadapt, map_zero, smul_zero, add_zero, zero_add, neg_zero]
  have hw : (∀ t, (0 : Ω → ℝ) = lamP • wl (t + 1)) ↔ ∀ t, wl (t + 1) = 0 := by
    refine forall_congr' fun t => ?_
    rw [eq_comm, smul_eq_zero]
    simp [hlamP]
  constructor
  · intro h
    have hw1 : ∀ t, wl (t + 1) = 0 := hw.mp fun t => (h t).2.1
    refine ⟨fun t => ((h t).1).symm, hw1, ?_, fun t => ?_⟩
    · have e := (h 0).2.2.2
      rw [hw1 0, zero_add] at e
      exact e.symm
    · have e := (h (t + 1)).2.2.2
      rw [hw1 t, hw1 (t + 1), zero_add] at e
      exact e.symm
  · rintro ⟨hu, hw1, hd0, hd⟩ t
    refine ⟨(hu t).symm, hw.mpr hw1 t, ?_, ?_⟩
    · rw [hw1 t, smul_zero, sub_zero]
    · rw [hw1 t]
      cases t with
      | zero => rw [hd0, zero_add]
      | succ s => rw [hd s, hw1 s, add_zero]

/-- Galí (2015), p. 174 (corrected): with `λ_p ≠ 0`, there is a solution of (24)
with `ỹ = π^p = π^w = 0` for all `t`, initial condition `ω̃_{−1} = 0` and a real
wage gap known at each date, iff `u₁_t = r̂ⁿ_t − v_t − φ_y ŷⁿ_t ≡ 0` and
`Δωⁿ ≡ 0`. -/
theorem zeroPath_exists_iff {σ β φp φw φy κp κw lamP lamW : ℝ} (hlamP : lamP ≠ 0)
    {u1 dwn : ℕ → Ω → ℝ} :
    (∃ wl : ℕ → Ω → ℝ, wl 0 = 0 ∧ (∀ t, 𝔼.E t (wl (t + 1)) = wl (t + 1)) ∧
        MatrixEq 𝔼 (A0 σ φp φw φy κp κw) (A1 σ β lamP lamW) B0
          (stateVec (fun _ => 0) (fun _ => 0) (fun _ => 0) wl) (shockVec u1 dwn)) ↔
      (∀ t, u1 t = 0) ∧ ∀ t, dwn t = 0 := by
  constructor
  · rintro ⟨wl, h0, hadapt, h⟩
    obtain ⟨hu, -, hd0, hd⟩ := (zeroPath_iff 𝔼 hlamP hadapt).mp h
    refine ⟨hu, fun t => ?_⟩
    cases t with
    | zero => rw [hd0, h0]
    | succ s => exact hd s
  · rintro ⟨hu, hd⟩
    have hadapt : ∀ t, 𝔼.E t ((fun _ => (0 : Ω → ℝ)) (t + 1)) = (fun _ => 0) (t + 1) :=
      fun t => map_zero _
    refine ⟨fun _ => 0, rfl, hadapt, (zeroPath_iff 𝔼 hlamP hadapt).mpr ⟨hu, fun _ => rfl, ?_,
      fun t => hd (t + 1)⟩⟩
    exact hd 0

/-- Galí (2015), p. 174 (corrected statement; survey error 1). Technology `a` is
AR(1) with `ρ_a ≠ 1` (in deviations from steady state), `ŷⁿ_t = ψ_ya a_t`, the
natural real wage in deviations is `ω̂ⁿ_t = ψ_wa a_t` with `ψ_wa ≠ 0` (lagged
convention: `wnl (t + 1) = ω̂ⁿ_t`, `wnl 0 = ω̂ⁿ_{−1}`), `Δωⁿ_t = ω̂ⁿ_t − ω̂ⁿ_{t−1}`.
Then, for EVERY `φ_y`, the path `ỹ = π^p = π^w = 0` with `ω̃_{−1} = 0` solves (24)
iff the natural wage is constant at its steady state (`ω̂ⁿ ≡ 0`, at all dates
from `−1`) and `v = r̂ⁿ`. -/
theorem zeroPath_iff_primitives {σ β φp φw φy κp κw lamP lamW ρa ψya ψwa : ℝ}
    (hlamP : lamP ≠ 0) (hψ : ψwa ≠ 0) (hρa : ρa ≠ 1) {a wnl rnhat v : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (hwn : ∀ t, wnl (t + 1) = ψwa • a t) :
    (∃ wl : ℕ → Ω → ℝ, wl 0 = 0 ∧ (∀ t, 𝔼.E t (wl (t + 1)) = wl (t + 1)) ∧
        MatrixEq 𝔼 (A0 σ φp φw φy κp κw) (A1 σ β lamP lamW) B0
          (stateVec (fun _ => 0) (fun _ => 0) (fun _ => 0) wl)
          (shockVec (fun t => rnhat t - v t - φy • (ψya • a t))
            (fun t => wnl (t + 1) - wnl t))) ↔
      (∀ t, wnl t = 0) ∧ ∀ t, v t = rnhat t := by
  rw [zeroPath_exists_iff 𝔼 hlamP]
  have ha0 : ∀ t, ψwa • a t = 0 → a t = 0 := fun t h => by
    rcases smul_eq_zero.mp h with h' | h'
    · exact absurd h' hψ
    · exact h'
  constructor
  · rintro ⟨hu, hd⟩
    -- the natural wage is constant over time
    have hconst : ∀ t, wnl t = wnl 0 := by
      intro t
      induction t with
      | zero => rfl
      | succ s ih => rw [← ih]; exact sub_eq_zero.mp (hd s)
    -- hence technology is constant, and AR(1) with ρ_a ≠ 1 forces it to be zero
    have hac : a 1 = a 0 := by
      have h1 : ψwa • a 1 = ψwa • a 0 := by rw [← hwn, ← hwn, hconst 2, hconst 1]
      exact smul_right_injective _ hψ h1
    have hz : a 0 = 0 := by
      have e := ha.2 0
      rw [hac, ha.1 0] at e
      funext x
      have ex := congrFun e x
      simp only [Pi.smul_apply, smul_eq_mul] at ex
      have : (1 - ρa) * a 0 x = 0 := by linear_combination ex
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd (by linarith : ρa = 1) hρa
      · exact h'
    have hw0 : ∀ t, wnl t = 0 := by
      intro t
      rw [hconst t, ← hconst 1, hwn 0, hz, smul_zero]
    have hat : ∀ t, a t = 0 := fun t => by
      have h := hwn t
      rw [hw0 (t + 1)] at h
      exact ha0 t h.symm
    refine ⟨hw0, fun t => ?_⟩
    have e := hu t
    rw [hat t, smul_zero, smul_zero, sub_zero] at e
    exact (sub_eq_zero.mp e).symm
  · rintro ⟨hw0, hv⟩
    have hat : ∀ t, a t = 0 := fun t => by
      have h := hwn t
      rw [hw0 (t + 1)] at h
      exact ha0 t h.symm
    refine ⟨fun t => ?_, fun t => ?_⟩
    · rw [hat t, hv t, smul_zero, smul_zero, sub_self, sub_zero]
    · rw [hw0 (t + 1), hw0 t, sub_zero]

/-- Galí (2015), p. 174 (the printed hypothesis `φ_y = 0` is redundant): if the
natural wage is at its steady state at all dates (`ω̂ⁿ ≡ 0`, so `a ≡ 0` and
`ŷⁿ ≡ 0`) and `v = r̂ⁿ`, then `ỹ = π^p = π^w = 0` (with `ω̃ ≡ 0`) solves (24) for
ANY `φ_y`, in particular `φ_y ≠ 0`. -/
theorem zeroPath_solves_any_phiY {σ β φp φw φy κp κw lamP lamW ψya ψwa : ℝ}
    (hlamP : lamP ≠ 0) (hψ : ψwa ≠ 0) {a wnl rnhat v : ℕ → Ω → ℝ}
    (hwn : ∀ t, wnl (t + 1) = ψwa • a t) (hw0 : ∀ t, wnl t = 0) (hv : ∀ t, v t = rnhat t) :
    MatrixEq 𝔼 (A0 σ φp φw φy κp κw) (A1 σ β lamP lamW) B0
      (stateVec (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0))
      (shockVec (fun t => rnhat t - v t - φy • (ψya • a t)) (fun t => wnl (t + 1) - wnl t)) := by
  have hat : ∀ t, a t = 0 := fun t => by
    have h := hwn t
    rw [hw0 (t + 1)] at h
    rcases smul_eq_zero.mp h.symm with h' | h'
    · exact absurd h' hψ
    · exact h'
  have hadapt : ∀ t, 𝔼.E t ((fun _ => (0 : Ω → ℝ)) (t + 1)) = (fun _ => 0) (t + 1) :=
    fun t => map_zero _
  refine (zeroPath_iff 𝔼 hlamP hadapt).mpr ⟨fun t => ?_, fun _ => rfl, ?_, fun t => ?_⟩
  · rw [hat t, hv t, smul_zero, smul_zero, sub_self, sub_zero]
  · rw [hw0 1, hw0 0, sub_zero]
  · rw [hw0 (t + 2), hw0 (t + 1), sub_zero]

/-- Galí (2015), p. 174 (the printed `v_t = rⁿ_t` must be `v_t = r̂ⁿ_t = rⁿ_t − ρ`):
if `v = rⁿ = ρ + r̂ⁿ` with `ρ ≠ 0`, then even with a constant natural wage
(`ω̂ⁿ ≡ 0`) the path `ỹ = π^p = π^w = 0` (with `ω̃_{−1} = 0`) does NOT solve (24). -/
theorem zeroPath_fails_v_eq_rn [Nonempty Ω] {σ β φp φw φy κp κw lamP lamW ρ ψya ψwa : ℝ}
    (hlamP : lamP ≠ 0) (hψ : ψwa ≠ 0) (hρ : ρ ≠ 0) {a wnl rnhat v : ℕ → Ω → ℝ}
    (hwn : ∀ t, wnl (t + 1) = ψwa • a t) (hw0 : ∀ t, wnl t = 0)
    (hv : ∀ t, v t = (fun _ => ρ) + rnhat t) :
    ¬ ∃ wl : ℕ → Ω → ℝ, wl 0 = 0 ∧ (∀ t, 𝔼.E t (wl (t + 1)) = wl (t + 1)) ∧
        MatrixEq 𝔼 (A0 σ φp φw φy κp κw) (A1 σ β lamP lamW) B0
          (stateVec (fun _ => 0) (fun _ => 0) (fun _ => 0) wl)
          (shockVec (fun t => rnhat t - v t - φy • (ψya • a t))
            (fun t => wnl (t + 1) - wnl t)) := by
  rw [zeroPath_exists_iff 𝔼 hlamP]
  rintro ⟨hu, -⟩
  have ha : a 0 = 0 := by
    have h := hwn 0
    rw [hw0 1] at h
    rcases smul_eq_zero.mp h.symm with h' | h'
    · exact absurd h' hψ
    · exact h'
  have e := hu 0
  rw [ha, hv 0, smul_zero, smul_zero, sub_zero] at e
  obtain ⟨x⟩ := ‹Nonempty Ω›
  have ex := congrFun e x
  simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply] at ex
  exact hρ (by linarith)

/-! ### The determinant identity and the determinacy boundary (p. 174) -/

/-- Galí (2015), p. 174: the left-hand side of the determinacy condition,
`φ_p + φ_w + φ_y (1 − β)/Θ_y (1/λ_p + 1/λ_w)`, `Θ_y = σ + (α + φ)/(1 − α)`. -/
noncomputable def detLHS (σ φ α β lamP lamW φp φw φy : ℝ) : ℝ :=
  φp + φw + φy * (1 - β) / thetaY σ φ α * (1 / lamP + 1 / lamW)

/-- Galí (2015), eq. (24), p. 173: `det(A₀ − A₁)` for general slopes `κ_p, κ_w`:
`−φ_y (1 − β)(λ_p + λ_w) − (φ_p + φ_w − 1)(λ_w κ_p + λ_p κ_w)`. -/
theorem det_A0_sub_A1 (σ β φp φw φy κp κw lamP lamW : ℝ) :
    (A0 σ φp φw φy κp κw - A1 σ β lamP lamW).det
      = -(φy * (1 - β) * (lamP + lamW)) - (φp + φw - 1) * (lamW * κp + lamP * κw) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove, A0, A1]
  ring

/-- Galí (2015), p. 174: with `κ_p = α λ_p/(1 − α)` and `κ_w = λ_w (σ + φ/(1 − α))`,
`det(A₀ − A₁) = −λ_p λ_w Θ_y (LHS − 1)`, where `LHS` is the left side of the
determinacy condition. -/
theorem det_A0_sub_A1_eq {σ φ α β φp φw φy lamP lamW : ℝ} (hlamP : lamP ≠ 0) (hlamW : lamW ≠ 0)
    (hΘ : thetaY σ φ α ≠ 0) :
    (A0 σ φp φw φy (kappaP α lamP) (kappaW σ φ α lamW) - A1 σ β lamP lamW).det
      = -(lamP * lamW * thetaY σ φ α) * (detLHS σ φ α β lamP lamW φp φw φy - 1) := by
  rw [det_A0_sub_A1]
  have hk : lamW * kappaP α lamP + lamP * kappaW σ φ α lamW = lamP * lamW * thetaY σ φ α := by
    unfold kappaP kappaW thetaY
    ring
  rw [hk]
  unfold detLHS
  field_simp
  ring

/-- Galí (2015), eq. (24), p. 173: `det A₀ = σ + φ_y + φ_p κ_p + φ_w κ_w`. -/
theorem det_A0 (σ φp φw φy κp κw : ℝ) :
    (A0 σ φp φw φy κp κw).det = σ + φy + φp * κp + φw * κw := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove, A0]
  ring

/-- Galí (2015), p. 174: under `σ > 0`, `φ ≥ 0`, `0 ≤ α < 1`, `λ_p, λ_w > 0` and
nonnegative policy coefficients, `A₀` is invertible (`det A₀ > 0`). -/
theorem det_A0_pos {σ φ α φp φw φy lamP lamW : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hlamP : 0 < lamP) (hlamW : 0 < lamW) (hp : 0 ≤ φp) (hw : 0 ≤ φw)
    (hy : 0 ≤ φy) : 0 < (A0 σ φp φw φy (kappaP α lamP) (kappaW σ φ α lamW)).det := by
  rw [det_A0]
  have h1 := mul_nonneg hp (kappaP_nonneg hα0 hα1 hlamP.le)
  have h2 := mul_nonneg hw (kappaW_pos hσ hφ hα1 hlamW).le
  linarith

/-- Galí (2015), p. 174: `1` is an eigenvalue of `A ≡ A₀⁻¹ A₁` exactly on the
boundary of the determinacy region: there is `v ≠ 0` with `A v = v` iff
`φ_p + φ_w + φ_y (1 − β)/Θ_y (1/λ_p + 1/λ_w) = 1`. -/
theorem one_eigenvalue_iff {σ φ α β φp φw φy lamP lamW : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hlamP : 0 < lamP) (hlamW : 0 < lamW) (hp : 0 ≤ φp)
    (hw : 0 ≤ φw) (hy : 0 ≤ φy) :
    (∃ x : Fin 4 → ℝ, x ≠ 0 ∧
        ((A0 σ φp φw φy (kappaP α lamP) (kappaW σ φ α lamW))⁻¹ * A1 σ β lamP lamW) *ᵥ x = x) ↔
      detLHS σ φ α β lamP lamW φp φw φy = 1 := by
  set M := A0 σ φp φw φy (kappaP α lamP) (kappaW σ φ α lamW)
  set N := A1 σ β lamP lamW
  have hdet : IsUnit M.det := (det_A0_pos hσ hφ hα0 hα1 hlamP hlamW hp hw hy).ne'.isUnit
  have hΘ := thetaY_pos hσ hφ hα0 hα1
  have key : ∀ x : Fin 4 → ℝ, (M⁻¹ * N) *ᵥ x = x ↔ (M - N) *ᵥ x = 0 := by
    intro x
    constructor
    · intro h
      have h2 : N *ᵥ x = M *ᵥ x := by
        calc N *ᵥ x = (M * (M⁻¹ * N)) *ᵥ x := by
                rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
          _ = M *ᵥ x := by rw [← Matrix.mulVec_mulVec, h]
      rw [Matrix.sub_mulVec, h2, sub_self]
    · intro h
      rw [Matrix.sub_mulVec, sub_eq_zero] at h
      rw [← Matrix.mulVec_mulVec, ← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
        Matrix.one_mulVec]
  have hex : (∃ x : Fin 4 → ℝ, x ≠ 0 ∧ (M⁻¹ * N) *ᵥ x = x) ↔ (M - N).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact exists_congr fun x => and_congr_right fun _ => key x
  rw [hex, det_A0_sub_A1_eq hlamP.ne' hlamW.ne' hΘ.ne']
  have hc : lamP * lamW * thetaY σ φ α ≠ 0 := (mul_pos (mul_pos hlamP hlamW) hΘ).ne'
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd (neg_eq_zero.mp h') hc
    · linarith
  · intro h
    rw [h, sub_self, mul_zero]

/-- Galí (2015), p. 174: the sign of `det(A₀ − A₁)` tells on which side of the
boundary the coefficients lie: `det(A₀ − A₁) < 0` iff `LHS > 1`. -/
theorem det_neg_iff {σ φ α β φp φw φy lamP lamW : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hlamP : 0 < lamP) (hlamW : 0 < lamW) :
    (A0 σ φp φw φy (kappaP α lamP) (kappaW σ φ α lamW) - A1 σ β lamP lamW).det < 0 ↔
      1 < detLHS σ φ α β lamP lamW φp φw φy := by
  have hΘ := thetaY_pos hσ hφ hα0 hα1
  have hc : 0 < lamP * lamW * thetaY σ φ α := mul_pos (mul_pos hlamP hlamW) hΘ
  rw [det_A0_sub_A1_eq hlamP.ne' hlamW.ne' hΘ.ne', neg_mul, neg_lt_zero]
  constructor
  · intro h
    have := (pos_iff_pos_of_mul_pos h).mp hc
    linarith
  · intro h
    exact mul_pos hc (by linarith)

/-- Galí (2015), p. 174: in the special case `φ_y = 0` the determinacy condition
reads `φ_p + φ_w > 1`. -/
theorem detCondition_phiY_zero (σ φ α β lamP lamW φp φw : ℝ) :
    1 < detLHS σ φ α β lamP lamW φp φw 0 ↔ 1 < φp + φw := by
  unfold detLHS
  simp

/-- Galí (2015), p. 175, Figure 6.1: the lower bound on `φ_p + φ_w` implied by the
determinacy condition, `1 − φ_y (1 − β)/Θ_y (1/λ_p + 1/λ_w)`. -/
noncomputable def threshold (σ φ α β lamP lamW φy : ℝ) : ℝ :=
  1 - φy * (1 - β) / thetaY σ φ α * (1 / lamP + 1 / lamW)

/-- Galí (2015), pp. 174–175: the determinacy condition is `φ_p + φ_w > threshold(φ_y)`. -/
theorem detCondition_iff_threshold (σ φ α β lamP lamW φp φw φy : ℝ) :
    1 < detLHS σ φ α β lamP lamW φp φw φy ↔ threshold σ φ α β lamP lamW φy < φp + φw := by
  unfold detLHS threshold
  constructor <;> intro h <;> linarith

/-- Galí (2015), p. 174: at `φ_y = 0` the threshold is `1`. -/
theorem threshold_zero (σ φ α β lamP lamW : ℝ) : threshold σ φ α β lamP lamW 0 = 1 := by
  simp [threshold]

/-- Galí (2015), p. 175 and Figure 6.1: "as `φ_y` increases, the lower bound on
`φ_p + φ_w` consistent with a unique equilibrium declines" — the threshold is
strictly decreasing in `φ_y` for `β < 1`. -/
theorem threshold_strictAnti {σ φ α β lamP lamW : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ : β < 1) (hlamP : 0 < lamP) (hlamW : 0 < lamW) :
    StrictAnti (threshold σ φ α β lamP lamW) := by
  intro a b hab
  have hΘ := thetaY_pos hσ hφ hα0 hα1
  have hs : 0 < 1 / lamP + 1 / lamW := by positivity
  have hc : 0 < (1 - β) / thetaY σ φ α * (1 / lamP + 1 / lamW) :=
    mul_pos (div_pos (by linarith) hΘ) hs
  have e : ∀ y, threshold σ φ α β lamP lamW y
      = 1 - y * ((1 - β) / thetaY σ φ α * (1 / lamP + 1 / lamW)) := by
    intro y
    unfold threshold
    ring
  rw [e, e]
  have := mul_lt_mul_of_pos_right hab hc
  linarith

end Gali.StickyWagesPrices.System
