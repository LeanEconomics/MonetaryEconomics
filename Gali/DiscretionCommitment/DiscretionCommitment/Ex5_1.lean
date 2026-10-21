/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DiscretionCommitment.Expectations
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FinCases

/-!
# Exercise 5.1: an optimized Taylor rule

Galí (2015), Chapter 5, Exercise 5.1, p. 159. The economy is
`x_t = E_t x_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − ρ) + z_t`, `π_t = β E_t π_{t+1} + κ x_t + u_t`,
with i.i.d. mutually uncorrelated demand and supply shocks `z`, `u` (variances `σ_z²`, `σ_u²`),
and the central bank follows `i_t = ρ + φ_π π_t`.

## (a) The equilibrium
* `msv_equilibrium`: `x_t = (σ z_t − φ_π u_t)/(σ + κ φ_π)`,
  `π_t = σ (κ z_t + u_t)/(σ + κ φ_π)` is an equilibrium (i.i.d. shocks: `E_t z_{t+1} = 0`,
  `E_t u_{t+1} = 0`).
* `ex5_1a_unique`: for `φ_π > 1` every equilibrium whose deviation from it is bounded and
  adapted coincides with it (Galí's convention, also for unbounded, e.g. normal, shocks);
  `ex5_1a_unique_bounded`: in particular it is the unique bounded equilibrium for bounded shocks.
* `ex5_1a_not_unique`: for `0 ≤ φ_π ≤ 1` there are other bounded equilibria next to it, so
  `φ_π > 1` is exactly the determinacy region (`schurStable_A_iff`).

## (b) The optimal inflation coefficient
With a covariance form `B` (any bilinear form, e.g. the covariance) and uncorrelated shocks,
`ex5_1b_loss_eq`: `ϑ var x_t + var π_t = L(φ_π) = (ϑ σ_u² φ_π² + C)/(σ + κ φ_π)²`,
`C = σ² ((ϑ + κ²) σ_z² + σ_u²)`. `lossFn_eq` (a Lagrange identity) writes
`L(φ) = L* + (a σ φ − κ C)²/((a σ² + κ² C)(σ + κ φ)²)`, `a = ϑ σ_u²`, so
`φ_π* = (κσ/ϑ)[1 + (ϑ + κ²) σ_z²/σ_u²]` (`phiStar`, `phiStar_foc`) is the unique global
minimiser among all `φ` with `σ + κφ ≠ 0` (`lossFn_ge`, `lossFn_phiStar`). Over the
determinacy region:
`ex5_1b_optimal` (if `φ_π* > 1`, `φ_π*` is the unique minimiser over `φ_π > 1`, also in
terms of equilibrium losses, `ex5_1b_equilibrium_optimal`) and `ex5_1b_corner` (if
`φ_π* ≤ 1`, the loss is strictly increasing on `(1, ∞)` and has no minimiser there;
`lossFn_strictMonoOn`).

## (c) Comparative statics
`phiStar_eq_phiR`, `phiR_eq`: `φ_π* = φ(r) = κσ/ϑ + κσ r + κ³σ r/ϑ`, `r = σ_z²/σ_u²`;
`phiR_strictAntiOn_weight` (decreasing in `ϑ`), `phiR_strictMono_ratio` (increasing in `r`),
`phiR_strictMono_sigma`, `phiR_strictMonoOn_kappa`; `tendsto_phiR_weight_zero`,
`tendsto_phiR_ratio_atTop` (aggressive responses, `φ_π* → ∞`, when the weight on output
vanishes or demand shocks dominate), `tendsto_phiR_weight_atTop` (`φ_π* → κσ r`) and
`tendsto_phiR_ratio_zero` (`φ_π* → κσ/ϑ` with supply shocks only). The verbal discussion
of part (c) is not formalised beyond these statements.
-/

namespace Gali.DiscretionCommitment.Ex5_1

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The model -/

/-- Galí (2015), Exercise 5.1, p. 159: the dynamic IS equation
`x_t = E_t x_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − ρ) + z_t`. -/
def DIS (σ ρ : ℝ) (x infl i z : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t = 𝔼.E t (x (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - fun _ => ρ) + z t

/-- Galí (2015), Exercise 5.1, p. 159: the New Keynesian Phillips curve
`π_t = β E_t π_{t+1} + κ x_t + u_t`. -/
def NKPC (β κ : ℝ) (x infl u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • x t + u t

/-- Galí (2015), Exercise 5.1, p. 159: the simple Taylor rule `i_t = ρ + φ_π π_t`. -/
def TaylorRule (ρ φ : ℝ) (infl i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = (fun _ => ρ) + φ • infl t

/-- Galí (2015), Exercise 5.1, p. 159: an equilibrium under the Taylor rule. -/
def Equilibrium (β σ κ ρ φ : ℝ) (z u x infl i : ℕ → Ω → ℝ) : Prop :=
  DIS 𝔼 σ ρ x infl i z ∧ NKPC 𝔼 β κ x infl u ∧ TaylorRule ρ φ infl i

/-- Galí (2015), Exercise 5.1(a): the homogeneous system satisfied by the difference of two
equilibria, `d^x_t = E_t d^x_{t+1} − σ⁻¹(φ_π d^π_t − E_t d^π_{t+1})`,
`d^π_t = β E_t d^π_{t+1} + κ d^x_t`. -/
def HomEq (β σ κ φ : ℝ) (dx dp : ℕ → Ω → ℝ) : Prop :=
  ∀ t, dx t = 𝔼.E t (dx (t + 1)) - σ⁻¹ • (φ • dp t - 𝔼.E t (dp (t + 1))) ∧
    dp t = β • 𝔼.E t (dp (t + 1)) + κ • dx t

/-- Galí (2015), Exercise 5.1(a): stacking `(x, π)` into a vector process. -/
def stack (x p : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![x t, p t]

/-- Galí (2015), Exercise 5.1(a) (cf. ch. 4, eq. (13), p. 107, with `φ_y = 0`): the matrix
`A = (σ + κφ_π)⁻¹ [[σ, 1 − βφ_π], [κσ, κ + βσ]]` of the system `x_t = A E_t x_{t+1}`. -/
noncomputable def A (β σ κ φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![σ / (σ + κ * φ), (1 - β * φ) / (σ + κ * φ);
    κ * σ / (σ + κ * φ), (κ + β * σ) / (σ + κ * φ)]

/-- Galí (2015), Exercise 5.1(a): `tr A = (σ + κ + βσ)/(σ + κφ_π)`. -/
theorem tr2_A (β σ κ φ : ℝ) : tr2 (A β σ κ φ) = (σ + κ + β * σ) / (σ + κ * φ) := by
  simp only [tr2, A, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- Galí (2015), Exercise 5.1(a): `det A = βσ/(σ + κφ_π)`. -/
theorem det2_A {β σ κ φ : ℝ} (hD : σ + κ * φ ≠ 0) :
    det2 (A β σ κ φ) = β * σ / (σ + κ * φ) := by
  simp only [det2, A, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  field_simp
  ring

/-- **Exercise 5.1(a), determinacy region** (Galí 2015, p. 159; ch. 4, (14) with
`φ_y = 0`): for `σ, κ > 0`, `0 < β < 1` and `φ_π ≥ 0`, the Schur–Cohn condition on `A` holds
iff `φ_π > 1`. -/
theorem schurStable_A_iff {β σ κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφ : 0 ≤ φ) : SchurStable (tr2 (A β σ κ φ)) (det2 (A β σ κ φ)) ↔ 1 < φ := by
  have hD : 0 < σ + κ * φ := by positivity
  rw [tr2_A, det2_A hD.ne', SchurStable]
  have hdet : |β * σ / (σ + κ * φ)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one hD]
    nlinarith [mul_nonneg hκ.le hφ]
  have htr : |(σ + κ + β * σ) / (σ + κ * φ)| = (σ + κ + β * σ) / (σ + κ * φ) :=
    abs_of_pos (by positivity)
  rw [htr]
  constructor
  · rintro ⟨-, h⟩
    rw [div_lt_iff₀ hD, add_mul, one_mul, div_mul_cancel₀ _ hD.ne'] at h
    nlinarith
  · intro h
    refine ⟨hdet, ?_⟩
    rw [div_lt_iff₀ hD, add_mul, one_mul, div_mul_cancel₀ _ hD.ne']
    nlinarith

/-- Galí (2015), Exercise 5.1(a): the homogeneous structural system is the system
`d_t = A E_t d_{t+1}` in `(d^x, d^π)`. -/
theorem homEq_iff_solves {β σ κ φ : ℝ} (hσ : σ ≠ 0) (hD : σ + κ * φ ≠ 0)
    (dx dp : ℕ → Ω → ℝ) :
    HomEq 𝔼 β σ κ φ dx dp ↔ 𝔼.Solves (A β σ κ φ) 0 (stack dx dp) := by
  constructor
  · intro h t i
    obtain ⟨h1, h2⟩ := h t
    funext ω
    have e1 := congrFun h1 ω
    have e2 := congrFun h2 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    have e1' : σ * dx t ω = σ * 𝔼.E t (dx (t + 1)) ω - (φ * dp t ω - 𝔼.E t (dp (t + 1)) ω) := by
      rw [e1]; field_simp
    fin_cases i <;>
      simp only [stack, A, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero, Fin.zero_eta, Fin.mk_one] <;>
      field_simp
    · linear_combination e1' - φ * e2
    · linear_combination κ * e1' + σ * e2
  · intro h t
    have h0 := h t 0
    have h1 := h t 1
    simp only [stack, A, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Pi.zero_apply, add_zero] at h0 h1
    constructor
    · funext ω
      have e0 := congrFun h0 ω
      have e1 := congrFun h1 ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [e0, e1]
      field_simp
      ring
    · funext ω
      have e0 := congrFun h0 ω
      have e1 := congrFun h1 ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [e0, e1]
      field_simp
      ring

/-! ### (a) Existence and uniqueness -/

/-- Galí (2015), Exercise 5.1(a), p. 159: the output gap `x_t = (σ z_t − φ_π u_t)/(σ + κφ_π)`. -/
noncomputable def xs (σ κ φ : ℝ) (z u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (σ / (σ + κ * φ)) • z t + (-φ / (σ + κ * φ)) • u t

/-- Galí (2015), Exercise 5.1(a), p. 159: inflation `π_t = σ (κ z_t + u_t)/(σ + κφ_π)`. -/
noncomputable def ps (σ κ φ : ℝ) (z u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (σ * κ / (σ + κ * φ)) • z t + (σ / (σ + κ * φ)) • u t

/-- Galí (2015), Exercise 5.1, p. 159: the nominal rate implied by the rule, `ρ + φ_π π_t`. -/
def rate (ρ φ : ℝ) (infl : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => (fun _ => ρ) + φ • infl t

omit 𝔼 in
/-- Galí (2015), Exercise 5.1(a): linear combinations of bounded processes are bounded. -/
theorem bounded_comb {z u : ℕ → Ω → ℝ} (hz : BoundedProc z) (hu : BoundedProc u) (a b : ℝ) :
    BoundedProc fun t => a • z t + b • u t := by
  obtain ⟨M, hM⟩ := hz
  obtain ⟨N, hN⟩ := hu
  refine ⟨|a| * M + |b| * N, fun t ω => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
  · exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg a)
  · exact mul_le_mul_of_nonneg_left (hN t ω) (abs_nonneg b)

omit 𝔼 in
/-- Galí (2015), Exercise 5.1(a): differences of bounded processes are bounded. -/
theorem bounded_sub {x y : ℕ → Ω → ℝ} (hx : BoundedProc x) (hy : BoundedProc y) :
    BoundedProc (x - y) := by
  obtain ⟨M, hM⟩ := hx
  obtain ⟨N, hN⟩ := hy
  exact ⟨M + N, fun t ω => (abs_sub _ _).trans (add_le_add (hM t ω) (hN t ω))⟩

/-- Galí (2015), Exercise 5.1(a): linear combinations of adapted processes are adapted. -/
theorem adapted_comb {z u : ℕ → Ω → ℝ} (hz : 𝔼.Adapted z) (hu : 𝔼.Adapted u) (a b : ℝ) :
    𝔼.Adapted fun t => a • z t + b • u t := by
  intro t
  simp only [map_add, map_smul, hz t, hu t]

/-- **Exercise 5.1(a), existence** (Galí 2015, p. 159): with i.i.d. shocks
(`E_t z_{t+1} = E_t u_{t+1} = 0`), `x_t = (σ z_t − φ_π u_t)/(σ + κφ_π)`,
`π_t = σ (κ z_t + u_t)/(σ + κφ_π)`, `i_t = ρ + φ_π π_t` is an equilibrium. -/
theorem msv_equilibrium {β σ κ ρ φ : ℝ} (hσ : σ ≠ 0) (hD : σ + κ * φ ≠ 0)
    {z u : ℕ → Ω → ℝ} (hz : 𝔼.IsAR1 0 z) (hu : 𝔼.IsAR1 0 u) :
    Equilibrium 𝔼 β σ κ ρ φ z u (xs σ κ φ z u) (ps σ κ φ z u) (rate ρ φ (ps σ κ φ z u)) := by
  have hEz : ∀ t, 𝔼.E t (z (t + 1)) = 0 := fun t => by rw [hz.2 t, zero_smul]
  have hEu : ∀ t, 𝔼.E t (u (t + 1)) = 0 := fun t => by rw [hu.2 t, zero_smul]
  have hEx : ∀ t, 𝔼.E t (xs σ κ φ z u (t + 1)) = 0 := fun t => by
    simp only [xs, map_add, map_smul, hEz, hEu, smul_zero, add_zero]
  have hEp : ∀ t, 𝔼.E t (ps σ κ φ z u (t + 1)) = 0 := fun t => by
    simp only [ps, map_add, map_smul, hEz, hEu, smul_zero, add_zero]
  refine ⟨fun t => ?_, fun t => ?_, fun t => rfl⟩
  · rw [hEx, hEp]
    funext ω
    simp only [xs, ps, rate, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply]
    field_simp
    ring
  · rw [hEp]
    funext ω
    simp only [xs, ps, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    field_simp
    ring

/-- Galí (2015), Exercise 5.1(a): the difference of two equilibria solves the homogeneous
system. -/
theorem equilibrium_sub {β σ κ ρ φ : ℝ} {z u x p i x' p' i' : ℕ → Ω → ℝ}
    (h : Equilibrium 𝔼 β σ κ ρ φ z u x p i) (h' : Equilibrium 𝔼 β σ κ ρ φ z u x' p' i') :
    HomEq 𝔼 β σ κ φ (x - x') (p - p') := by
  obtain ⟨hd, hn, hr⟩ := h
  obtain ⟨hd', hn', hr'⟩ := h'
  intro t
  have a1 := hd t
  have a2 := hd' t
  have b1 := hn t
  have b2 := hn' t
  rw [hr t] at a1
  rw [hr' t] at a2
  constructor
  · funext ω
    have e1 := congrFun a1 ω
    have e2 := congrFun a2 ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_sub] at e1 e2 ⊢
    rw [e1, e2]
    ring
  · funext ω
    have e1 := congrFun b1 ω
    have e2 := congrFun b2 ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_sub] at e1 e2 ⊢
    rw [e1, e2]
    ring

/-- Galí (2015), Exercise 5.1(a): adding a solution of the homogeneous system to an
equilibrium gives an equilibrium. -/
theorem equilibrium_add_hom {β σ κ ρ φ : ℝ} {z u x p dx dp : ℕ → Ω → ℝ}
    (h : Equilibrium 𝔼 β σ κ ρ φ z u x p (rate ρ φ p)) (hd : HomEq 𝔼 β σ κ φ dx dp) :
    Equilibrium 𝔼 β σ κ ρ φ z u (x + dx) (p + dp) (rate ρ φ (p + dp)) := by
  obtain ⟨h1, h2, -⟩ := h
  refine ⟨fun t => ?_, fun t => ?_, fun t => rfl⟩
  · funext ω
    have e1 := congrFun (h1 t) ω
    have e2 := congrFun (hd t).1 ω
    simp only [rate, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      map_add] at e1 e2 ⊢
    rw [e1, e2]
    ring
  · funext ω
    have e1 := congrFun (h2 t) ω
    have e2 := congrFun (hd t).2 ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add] at e1 e2 ⊢
    rw [e1, e2]
    ring

omit 𝔼 in
/-- Galí (2015), Exercise 5.1(a): stacking bounded processes. -/
theorem boundedVec_stack {x p : ℕ → Ω → ℝ} (hx : BoundedProc x) (hp : BoundedProc p) :
    BoundedVec (stack x p) := by
  obtain ⟨M, hM⟩ := hx
  obtain ⟨N, hN⟩ := hp
  refine ⟨max M N, fun t i ω => ?_⟩
  fin_cases i
  · exact (hM t ω).trans (le_max_left _ _)
  · exact (hN t ω).trans (le_max_right _ _)

/-- Galí (2015), Exercise 5.1(a): stacking adapted processes. -/
theorem adaptedVec_stack {x p : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) (hp : 𝔼.Adapted p) :
    𝔼.AdaptedVec (stack x p) := by
  intro t i
  fin_cases i
  · exact hx t
  · exact hp t

/-- Galí (2015), Exercise 5.1(a): the equilibrium output gap and inflation are adapted. -/
theorem msv_adapted {σ κ φ : ℝ} {z u : ℕ → Ω → ℝ} (hz : 𝔼.Adapted z) (hu : 𝔼.Adapted u) :
    𝔼.Adapted (xs σ κ φ z u) ∧ 𝔼.Adapted (ps σ κ φ z u) :=
  ⟨adapted_comb 𝔼 hz hu _ _, adapted_comb 𝔼 hz hu _ _⟩

/-- **Exercise 5.1(a), uniqueness** (Galí 2015, p. 159): for `φ_π > 1`, every equilibrium
`(x, π, i)` with adapted `x, π` whose deviation from the solution above is bounded coincides
with it. -/
theorem ex5_1a_unique {β σ κ ρ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφ : 1 < φ) {z u x p i : ℕ → Ω → ℝ} (hz : 𝔼.IsAR1 0 z) (hu : 𝔼.IsAR1 0 u)
    (he : Equilibrium 𝔼 β σ κ ρ φ z u x p i) (hax : 𝔼.Adapted x) (hap : 𝔼.Adapted p)
    (hbx : BoundedProc (x - xs σ κ φ z u)) (hbp : BoundedProc (p - ps σ κ φ z u)) :
    x = xs σ κ φ z u ∧ p = ps σ κ φ z u ∧ i = rate ρ φ (ps σ κ φ z u) := by
  have hD : 0 < σ + κ * φ := by nlinarith
  have hS := (schurStable_A_iff hσ hκ hβ0 hβ1 (by linarith)).mpr hφ
  have hhom := equilibrium_sub 𝔼 he (msv_equilibrium 𝔼 (ρ := ρ) (β := β) hσ.ne' hD.ne' hz hu)
  have hsol := (homEq_iff_solves 𝔼 hσ.ne' hD.ne' _ _).mp hhom
  obtain ⟨hxa, hpa⟩ := msv_adapted 𝔼 (σ := σ) (κ := κ) (φ := φ) hz.1 hu.1
  have had : 𝔼.AdaptedVec (stack (x - xs σ κ φ z u) (p - ps σ κ φ z u)) :=
    adaptedVec_stack 𝔼 (fun t => by simp only [Pi.sub_apply, map_sub, hax t, hxa t])
      (fun t => by simp only [Pi.sub_apply, map_sub, hap t, hpa t])
  have h0 : 𝔼.Solves (A β σ κ φ) 0 0 := fun t i => by simp
  have heq := 𝔼.system_unique hS hsol h0 had (fun t i => by simp) (boundedVec_stack hbx hbp)
    ⟨0, fun t i ω => by simp⟩
  have hx : x = xs σ κ φ z u := by
    funext t
    have := congrFun (congrFun heq t) 0
    simpa [stack, sub_eq_zero] using this
  have hp : p = ps σ κ φ z u := by
    funext t
    have := congrFun (congrFun heq t) 1
    simpa [stack, sub_eq_zero] using this
  refine ⟨hx, hp, ?_⟩
  funext t
  rw [he.2.2 t, hp]
  rfl

/-- **Exercise 5.1(a)** (Galí 2015, p. 159; Galí's convention): with bounded i.i.d. shocks and
`φ_π > 1`, the solution above is the unique equilibrium with bounded adapted `x` and `π`. -/
theorem ex5_1a_unique_bounded {β σ κ ρ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφ : 1 < φ) {z u x p i : ℕ → Ω → ℝ} (hz : 𝔼.IsAR1 0 z) (hu : 𝔼.IsAR1 0 u)
    (hzb : BoundedProc z) (hub : BoundedProc u) (he : Equilibrium 𝔼 β σ κ ρ φ z u x p i)
    (hax : 𝔼.Adapted x) (hap : 𝔼.Adapted p) (hbx : BoundedProc x) (hbp : BoundedProc p) :
    x = xs σ κ φ z u ∧ p = ps σ κ φ z u ∧ i = rate ρ φ (ps σ κ φ z u) :=
  ex5_1a_unique 𝔼 hσ hκ hβ0 hβ1 hφ hz hu he hax hap
    (bounded_sub hbx (bounded_comb hzb hub _ _)) (bounded_sub hbp (bounded_comb hzb hub _ _))

/-- **Exercise 5.1(a), indeterminacy** (Galí 2015, p. 159): for `0 ≤ φ_π ≤ 1` there is
another equilibrium, with adapted `x, π` at a bounded (nonzero) distance from the solution
above. -/
theorem ex5_1a_not_unique [Nonempty Ω] {β σ κ ρ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) {z u : ℕ → Ω → ℝ} (hz : 𝔼.IsAR1 0 z)
    (hu : 𝔼.IsAR1 0 u) :
    ∃ x p i, Equilibrium 𝔼 β σ κ ρ φ z u x p i ∧ 𝔼.Adapted x ∧ 𝔼.Adapted p ∧
      BoundedProc (x - xs σ κ φ z u) ∧ BoundedProc (p - ps σ κ φ z u) ∧
      ¬ (x = xs σ κ φ z u ∧ p = ps σ κ φ z u) := by
  have hD : 0 < σ + κ * φ := by positivity
  have hS : ¬ SchurStable (tr2 (A β σ κ φ)) (det2 (A β σ κ φ)) := by
    rw [schurStable_A_iff hσ hκ hβ0 hβ1 hφ0]; linarith
  have h0 : 𝔼.Solves (A β σ κ φ) 0 0 := fun t i => by simp
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ :=
    𝔼.system_not_unique hS h0 (fun t i => by simp) ⟨0, fun t i ω => by simp⟩
  have hst : stack (fun t => y t 0) (fun t => y t 1) = y := by
    funext t i
    fin_cases i <;> rfl
  have hhom : HomEq 𝔼 β σ κ φ (fun t => y t 0) (fun t => y t 1) :=
    (homEq_iff_solves 𝔼 hσ.ne' hD.ne' _ _).mpr (by rw [hst]; exact hy)
  obtain ⟨hxa, hpa⟩ := msv_adapted 𝔼 (σ := σ) (κ := κ) (φ := φ) hz.1 hu.1
  refine ⟨xs σ κ φ z u + fun t => y t 0, ps σ κ φ z u + fun t => y t 1, _,
    equilibrium_add_hom 𝔼 (msv_equilibrium 𝔼 hσ.ne' hD.ne' hz hu) hhom,
    fun t => by simp only [Pi.add_apply, map_add, hxa t, hay t 0],
    fun t => by simp only [Pi.add_apply, map_add, hpa t, hay t 1],
    ⟨M, fun t ω => by simpa using hM t 0 ω⟩, ⟨M, fun t ω => by simpa using hM t 1 ω⟩, ?_⟩
  rintro ⟨h1, h2⟩
  apply hne
  funext t i
  fin_cases i
  · funext ω
    have := congrFun (congrFun h1 t) ω
    simpa using this
  · funext ω
    have := congrFun (congrFun h2 t) ω
    simpa using this

/-! ### (b) The loss and its minimiser -/

omit 𝔼 in
/-- Galí (2015), Exercise 5.1(b): for a bilinear covariance form `B` and uncorrelated `z, u`,
`var (a z + b u) = a² var z + b² var u` (restated from the Chapter 4 project, Ex. 4.2). -/
theorem bilin_quad (B : LinearMap.BilinForm ℝ (Ω → ℝ)) (a b : ℝ) (z u : Ω → ℝ)
    (h1 : B z u = 0) (h2 : B u z = 0) :
    B (a • z + b • u) (a • z + b • u) = a ^ 2 * B z z + b ^ 2 * B u u := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1, h2]
  ring

/-- Galí (2015), Exercise 5.1(b), p. 159: the loss `ϑ var x_t + var π_t` under the rule as a
function of `φ_π`: `L(φ_π) = (ϑ σ_u² φ_π² + σ²((ϑ + κ²) σ_z² + σ_u²))/(σ + κφ_π)²`. -/
noncomputable def lossFn (ϑ σ κ vz vu φ : ℝ) : ℝ :=
  (ϑ * vu * φ ^ 2 + σ ^ 2 * ((ϑ + κ ^ 2) * vz + vu)) / (σ + κ * φ) ^ 2

/-- Galí (2015), Exercise 5.1(b): the constant `C = σ²((ϑ + κ²) σ_z² + σ_u²)` of the loss. -/
def lossC (ϑ σ κ vz vu : ℝ) : ℝ := σ ^ 2 * ((ϑ + κ ^ 2) * vz + vu)

/-- Galí (2015), Exercise 5.1(b): the minimum loss `L* = a C/(a σ² + κ² C)`, `a = ϑ σ_u²`. -/
noncomputable def lossMin (ϑ σ κ vz vu : ℝ) : ℝ :=
  ϑ * vu * lossC ϑ σ κ vz vu / (ϑ * vu * σ ^ 2 + κ ^ 2 * lossC ϑ σ κ vz vu)

/-- **Exercise 5.1(b), the optimal coefficient** (Galí 2015, p. 159):
`φ_π* = (κσ/ϑ)[1 + (ϑ + κ²) σ_z²/σ_u²]`. -/
noncomputable def phiStar (ϑ σ κ vz vu : ℝ) : ℝ := κ * σ / ϑ * (1 + (ϑ + κ ^ 2) * vz / vu)

/-- Galí (2015), Exercise 5.1(b): the equilibrium loss is `L(φ_π)`. For `φ_π > 1`, in the
unique equilibrium, with `var z_t = σ_z²`, `var u_t = σ_u²` and `z_t, u_t` uncorrelated
under the covariance form `B`, `ϑ var x_t + var π_t = L(φ_π)`. -/
theorem ex5_1b_loss_eq (B : LinearMap.BilinForm ℝ (Ω → ℝ)) {β σ κ ρ φ ϑ vz vu : ℝ}
    (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hφ : 1 < φ)
    {z u x p i : ℕ → Ω → ℝ} (hz : 𝔼.IsAR1 0 z) (hu : 𝔼.IsAR1 0 u)
    (he : Equilibrium 𝔼 β σ κ ρ φ z u x p i) (hax : 𝔼.Adapted x) (hap : 𝔼.Adapted p)
    (hbx : BoundedProc (x - xs σ κ φ z u)) (hbp : BoundedProc (p - ps σ κ φ z u)) (t : ℕ)
    (hvz : B (z t) (z t) = vz) (hvu : B (u t) (u t) = vu) (h1 : B (z t) (u t) = 0)
    (h2 : B (u t) (z t) = 0) :
    ϑ * B (x t) (x t) + B (p t) (p t) = lossFn ϑ σ κ vz vu φ := by
  obtain ⟨hx, hp, -⟩ := ex5_1a_unique 𝔼 hσ hκ hβ0 hβ1 hφ hz hu he hax hap hbx hbp
  have hD : σ + κ * φ ≠ 0 := by nlinarith
  rw [hx, hp]
  simp only [xs, ps]
  rw [bilin_quad B _ _ _ _ h1 h2, bilin_quad B _ _ _ _ h1 h2, hvz, hvu, lossFn]
  field_simp
  ring

/-- **Exercise 5.1(b), the Lagrange identity** (Galí 2015, p. 159): with `a = ϑ σ_u²`,
`L(φ) = L* + (a σ φ − κ C)²/((a σ² + κ² C)(σ + κ φ)²)`. -/
theorem lossFn_eq {ϑ σ κ vz vu φ : ℝ} (hD : σ + κ * φ ≠ 0)
    (hK : ϑ * vu * σ ^ 2 + κ ^ 2 * lossC ϑ σ κ vz vu ≠ 0) :
    lossFn ϑ σ κ vz vu φ = lossMin ϑ σ κ vz vu +
      (ϑ * vu * σ * φ - κ * lossC ϑ σ κ vz vu) ^ 2 /
        ((ϑ * vu * σ ^ 2 + κ ^ 2 * lossC ϑ σ κ vz vu) * (σ + κ * φ) ^ 2) := by
  unfold lossFn lossMin
  rw [div_add_div _ _ hK (mul_ne_zero hK (pow_ne_zero 2 hD)), div_eq_div_iff (pow_ne_zero 2 hD)
    (mul_ne_zero hK (mul_ne_zero hK (pow_ne_zero 2 hD)))]
  unfold lossC
  ring

/-- Galí (2015), Exercise 5.1(b): `C > 0`. -/
theorem lossC_pos {ϑ σ κ vz vu : ℝ} (hϑ : 0 < ϑ) (hσ : 0 < σ) (hvz : 0 ≤ vz) (hvu : 0 < vu) :
    0 < lossC ϑ σ κ vz vu := by
  unfold lossC; positivity

/-- Galí (2015), Exercise 5.1(b): `φ_π* > 0`. -/
theorem phiStar_pos {ϑ σ κ vz vu : ℝ} (hϑ : 0 < ϑ) (hσ : 0 < σ) (hκ : 0 < κ) (hvz : 0 ≤ vz)
    (hvu : 0 < vu) : 0 < phiStar ϑ σ κ vz vu := by
  unfold phiStar; positivity

/-- Galí (2015), Exercise 5.1(b): `φ_π*` is the root of the first-order condition,
`a σ φ_π* = κ C`. -/
theorem phiStar_foc {ϑ σ κ vz vu : ℝ} (hϑ : ϑ ≠ 0) (hvu : vu ≠ 0) :
    ϑ * vu * σ * phiStar ϑ σ κ vz vu = κ * lossC ϑ σ κ vz vu := by
  unfold phiStar lossC
  field_simp
  ring

/-- **Exercise 5.1(b), global minimum** (Galí 2015, p. 159): `L* ≤ L(φ)` for every `φ` with
`σ + κφ ≠ 0`, with equality iff `φ = φ_π*`. -/
theorem lossFn_ge {ϑ σ κ vz vu φ : ℝ} (hϑ : 0 < ϑ) (hσ : 0 < σ) (hvz : 0 ≤ vz) (hvu : 0 < vu)
    (hD : σ + κ * φ ≠ 0) :
    lossMin ϑ σ κ vz vu ≤ lossFn ϑ σ κ vz vu φ ∧
      (lossFn ϑ σ κ vz vu φ = lossMin ϑ σ κ vz vu ↔ φ = phiStar ϑ σ κ vz vu) := by
  have hC := lossC_pos (κ := κ) hϑ hσ hvz hvu
  have hK : 0 < ϑ * vu * σ ^ 2 + κ ^ 2 * lossC ϑ σ κ vz vu := by positivity
  rw [lossFn_eq hD hK.ne']
  refine ⟨le_add_of_nonneg_right (by positivity), ?_⟩
  have hfoc := phiStar_foc (σ := σ) (κ := κ) (vz := vz) hϑ.ne' hvu.ne'
  constructor
  · intro h
    have h0 : (ϑ * vu * σ * φ - κ * lossC ϑ σ κ vz vu) ^ 2 /
        ((ϑ * vu * σ ^ 2 + κ ^ 2 * lossC ϑ σ κ vz vu) * (σ + κ * φ) ^ 2) = 0 := by linarith
    rw [div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · have h00 : ϑ * vu * σ * φ = ϑ * vu * σ * phiStar ϑ σ κ vz vu := by
        rw [hfoc]; linarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp h0]
      exact mul_left_cancel₀ (by positivity) h00
    · exact absurd h0 (mul_ne_zero hK.ne' (pow_ne_zero 2 hD))
  · intro h
    rw [h, hfoc, sub_self]
    simp

/-- **Exercise 5.1(b)** (Galí 2015, p. 159): `L(φ_π*) = L*`. -/
theorem lossFn_phiStar {ϑ σ κ vz vu : ℝ} (hϑ : 0 < ϑ) (hσ : 0 < σ) (hκ : 0 < κ) (hvz : 0 ≤ vz)
    (hvu : 0 < vu) : lossFn ϑ σ κ vz vu (phiStar ϑ σ κ vz vu) = lossMin ϑ σ κ vz vu := by
  have hD : σ + κ * phiStar ϑ σ κ vz vu ≠ 0 := by
    have := phiStar_pos hϑ hσ hκ hvz hvu; positivity
  exact ((lossFn_ge hϑ hσ hvz hvu hD).2).mpr rfl

/-- **Exercise 5.1(b), the optimal rule** (Galí 2015, p. 159): if `φ_π* > 1`, then `φ_π*` is
the unique minimiser of `L` over the determinacy region `φ_π > 1`. -/
theorem ex5_1b_optimal {ϑ σ κ vz vu : ℝ} (hϑ : 0 < ϑ) (hσ : 0 < σ) (hκ : 0 < κ) (hvz : 0 ≤ vz)
    (hvu : 0 < vu) (h1 : 1 < phiStar ϑ σ κ vz vu) :
    phiStar ϑ σ κ vz vu ∈ Set.Ioi (1 : ℝ) ∧
      (∀ φ ∈ Set.Ioi (1 : ℝ), lossFn ϑ σ κ vz vu (phiStar ϑ σ κ vz vu) ≤ lossFn ϑ σ κ vz vu φ) ∧
      ∀ φ ∈ Set.Ioi (1 : ℝ),
        lossFn ϑ σ κ vz vu φ = lossFn ϑ σ κ vz vu (phiStar ϑ σ κ vz vu) →
          φ = phiStar ϑ σ κ vz vu := by
  rw [lossFn_phiStar hϑ hσ hκ hvz hvu]
  refine ⟨h1, fun φ hφ => ?_, fun φ hφ h => ?_⟩
  · have hD : σ + κ * φ ≠ 0 := by
      have : (1 : ℝ) < φ := hφ
      nlinarith
    exact (lossFn_ge hϑ hσ hvz hvu hD).1
  · have hD : σ + κ * φ ≠ 0 := by
      have : (1 : ℝ) < φ := hφ
      nlinarith
    exact ((lossFn_ge hϑ hσ hvz hvu hD).2).mp h

/-- Galí (2015), Exercise 5.1(b): the loss is strictly increasing to the right of `φ_π*`
(where `σ + κφ > 0`). -/
theorem lossFn_strictMonoOn {ϑ σ κ vz vu : ℝ} (hϑ : 0 < ϑ) (hσ : 0 < σ) (hκ : 0 < κ)
    (hvz : 0 ≤ vz) (hvu : 0 < vu) :
    StrictMonoOn (lossFn ϑ σ κ vz vu) (Set.Ici (phiStar ϑ σ κ vz vu)) := by
  intro φ₁ h₁ φ₂ h₂ h12
  simp only [Set.mem_Ici] at h₁ h₂
  have hp := phiStar_pos hϑ hσ hκ hvz hvu
  have hC := lossC_pos (κ := κ) hϑ hσ hvz hvu
  have hK : 0 < ϑ * vu * σ ^ 2 + κ ^ 2 * lossC ϑ σ κ vz vu := by positivity
  have hD1 : 0 < σ + κ * φ₁ := by nlinarith
  have hD2 : 0 < σ + κ * φ₂ := by nlinarith
  have hfoc := phiStar_foc (σ := σ) (κ := κ) (vz := vz) hϑ.ne' hvu.ne'
  have ha : 0 < ϑ * vu * σ := by positivity
  rw [lossFn_eq hD1.ne' hK.ne', lossFn_eq hD2.ne' hK.ne', add_lt_add_iff_left]
  set K := ϑ * vu * σ ^ 2 + κ ^ 2 * lossC ϑ σ κ vz vu
  set g := fun φ : ℝ => (ϑ * vu * σ * φ - κ * lossC ϑ σ κ vz vu) / (σ + κ * φ) with hg
  have hrw : ∀ φ : ℝ, 0 < σ + κ * φ → (ϑ * vu * σ * φ - κ * lossC ϑ σ κ vz vu) ^ 2 /
      (K * (σ + κ * φ) ^ 2) = g φ ^ 2 / K := by
    intro φ hφ
    simp only [hg]
    field_simp
  rw [hrw φ₁ hD1, hrw φ₂ hD2]
  have hg1 : 0 ≤ g φ₁ := by
    simp only [hg]
    refine div_nonneg ?_ hD1.le
    nlinarith [mul_le_mul_of_nonneg_left h₁ ha.le]
  have hg12 : g φ₂ - g φ₁ = K * (φ₂ - φ₁) / ((σ + κ * φ₁) * (σ + κ * φ₂)) := by
    simp only [hg, K]
    rw [div_sub_div _ _ hD2.ne' hD1.ne', div_eq_div_iff (mul_ne_zero hD2.ne' hD1.ne')
      (mul_ne_zero hD1.ne' hD2.ne')]
    unfold lossC
    ring
  have hlt : g φ₁ < g φ₂ := by
    have : 0 < K * (φ₂ - φ₁) / ((σ + κ * φ₁) * (σ + κ * φ₂)) := by
      apply div_pos (mul_pos hK (by linarith)) (mul_pos hD1 hD2)
    linarith
  exact div_lt_div_of_pos_right (by nlinarith) hK

/-- **Exercise 5.1(b), the corner case** (Galí 2015, p. 159): if `φ_π* ≤ 1`, the loss is
strictly increasing on the determinacy region `φ_π > 1`, so it has no minimiser there. -/
theorem ex5_1b_corner {ϑ σ κ vz vu : ℝ} (hϑ : 0 < ϑ) (hσ : 0 < σ) (hκ : 0 < κ) (hvz : 0 ≤ vz)
    (hvu : 0 < vu) (h1 : phiStar ϑ σ κ vz vu ≤ 1) :
    StrictMonoOn (lossFn ϑ σ κ vz vu) (Set.Ioi 1) ∧
      ¬ ∃ φ ∈ Set.Ioi (1 : ℝ), ∀ φ' ∈ Set.Ioi (1 : ℝ),
        lossFn ϑ σ κ vz vu φ ≤ lossFn ϑ σ κ vz vu φ' := by
  have hmono : StrictMonoOn (lossFn ϑ σ κ vz vu) (Set.Ioi 1) :=
    (lossFn_strictMonoOn hϑ hσ hκ hvz hvu).mono fun φ hφ => by
      simp only [Set.mem_Ioi] at hφ
      simp only [Set.mem_Ici]
      linarith
  refine ⟨hmono, ?_⟩
  rintro ⟨φ, hφ, hmin⟩
  simp only [Set.mem_Ioi] at hφ
  have hm : (1 + φ) / 2 ∈ Set.Ioi (1 : ℝ) := by simp only [Set.mem_Ioi]; linarith
  have := hmono hm (Set.mem_Ioi.mpr hφ) (by linarith)
  linarith [hmin _ hm]

/-- **Exercise 5.1(b) in terms of equilibria** (Galí 2015, p. 159): if `φ_π* > 1`, the
equilibrium loss `ϑ var x_t + var π_t` under `φ_π*` is at most that under any `φ_π > 1`, and
strictly smaller unless `φ_π = φ_π*`. -/
theorem ex5_1b_equilibrium_optimal (B : LinearMap.BilinForm ℝ (Ω → ℝ))
    {β σ κ ρ φ ϑ vz vu : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hϑ : 0 < ϑ) (hvz0 : 0 ≤ vz) (hvu0 : 0 < vu) (h1 : 1 < phiStar ϑ σ κ vz vu) (hφ : 1 < φ)
    {z u x p i x' p' i' : ℕ → Ω → ℝ} (hz : 𝔼.IsAR1 0 z) (hu : 𝔼.IsAR1 0 u)
    (he : Equilibrium 𝔼 β σ κ ρ φ z u x p i) (hax : 𝔼.Adapted x) (hap : 𝔼.Adapted p)
    (hbx : BoundedProc (x - xs σ κ φ z u)) (hbp : BoundedProc (p - ps σ κ φ z u))
    (he' : Equilibrium 𝔼 β σ κ ρ (phiStar ϑ σ κ vz vu) z u x' p' i') (hax' : 𝔼.Adapted x')
    (hap' : 𝔼.Adapted p') (hbx' : BoundedProc (x' - xs σ κ (phiStar ϑ σ κ vz vu) z u))
    (hbp' : BoundedProc (p' - ps σ κ (phiStar ϑ σ κ vz vu) z u)) (t : ℕ)
    (hvz : B (z t) (z t) = vz) (hvu : B (u t) (u t) = vu) (hzu : B (z t) (u t) = 0)
    (huz : B (u t) (z t) = 0) :
    ϑ * B (x' t) (x' t) + B (p' t) (p' t) ≤ ϑ * B (x t) (x t) + B (p t) (p t) ∧
      (ϑ * B (x t) (x t) + B (p t) (p t) = ϑ * B (x' t) (x' t) + B (p' t) (p' t) →
        φ = phiStar ϑ σ κ vz vu) := by
  rw [ex5_1b_loss_eq 𝔼 B hσ hκ hβ0 hβ1 hφ hz hu he hax hap hbx hbp t hvz hvu hzu huz,
    ex5_1b_loss_eq 𝔼 B hσ hκ hβ0 hβ1 h1 hz hu he' hax' hap' hbx' hbp' t hvz hvu hzu huz]
  obtain ⟨-, hle, huniq⟩ := ex5_1b_optimal hϑ hσ hκ hvz0 hvu0 h1
  exact ⟨hle φ hφ, huniq φ hφ⟩

/-! ### (c) Comparative statics -/

/-- Galí (2015), Exercise 5.1(c): `φ_π*` as a function of the variance ratio
`r = σ_z²/σ_u²`, `φ(r) = (κσ/ϑ)(1 + (ϑ + κ²) r)`. -/
noncomputable def phiR (ϑ σ κ r : ℝ) : ℝ := κ * σ / ϑ * (1 + (ϑ + κ ^ 2) * r)

/-- Galí (2015), Exercise 5.1(c): `φ_π* = φ(σ_z²/σ_u²)`. -/
theorem phiStar_eq_phiR (ϑ σ κ vz vu : ℝ) : phiStar ϑ σ κ vz vu = phiR ϑ σ κ (vz / vu) := by
  unfold phiStar phiR; ring

/-- Galí (2015), Exercise 5.1(c): `φ(r) = κσ/ϑ + κσ r + κ³σ r/ϑ`. -/
theorem phiR_eq {ϑ : ℝ} (hϑ : ϑ ≠ 0) (σ κ r : ℝ) :
    phiR ϑ σ κ r = κ * σ * (1 + κ ^ 2 * r) / ϑ + κ * σ * r := by
  unfold phiR; field_simp; ring

/-- **Exercise 5.1(c), the weight on output** (Galí 2015, p. 159): `φ_π*` is strictly
decreasing in `ϑ > 0`. -/
theorem phiR_strictAntiOn_weight {σ κ r : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hr : 0 ≤ r) :
    StrictAntiOn (fun ϑ => phiR ϑ σ κ r) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  simp only [phiR_eq ha.ne', phiR_eq hb.ne', add_lt_add_iff_right]
  exact div_lt_div_of_pos_left (by positivity) ha hab

/-- **Exercise 5.1(c), the variance ratio** (Galí 2015, p. 159): `φ_π*` is strictly increasing
in `r = σ_z²/σ_u²`. -/
theorem phiR_strictMono_ratio {ϑ σ κ : ℝ} (hϑ : 0 < ϑ) (hσ : 0 < σ) (hκ : 0 < κ) :
    StrictMono (fun r => phiR ϑ σ κ r) := by
  intro a b hab
  simp only [phiR]
  have : 0 < κ * σ / ϑ := by positivity
  have : 0 < ϑ + κ ^ 2 := by positivity
  nlinarith [mul_pos this (sub_pos.mpr hab), mul_pos ‹0 < κ * σ / ϑ› (mul_pos this
    (sub_pos.mpr hab))]

/-- Galí (2015), Exercise 5.1(c): `φ_π*` is strictly increasing in `σ` (for `r ≥ 0`). -/
theorem phiR_strictMono_sigma {ϑ κ r : ℝ} (hϑ : 0 < ϑ) (hκ : 0 < κ) (hr : 0 ≤ r) :
    StrictMono (fun σ => phiR ϑ σ κ r) := by
  intro a b hab
  simp only [phiR]
  have h : 0 < κ / ϑ * (1 + (ϑ + κ ^ 2) * r) := by positivity
  have ea : κ * a / ϑ * (1 + (ϑ + κ ^ 2) * r) = a * (κ / ϑ * (1 + (ϑ + κ ^ 2) * r)) := by ring
  have eb : κ * b / ϑ * (1 + (ϑ + κ ^ 2) * r) = b * (κ / ϑ * (1 + (ϑ + κ ^ 2) * r)) := by ring
  rw [ea, eb]
  exact mul_lt_mul_of_pos_right hab h

/-- Galí (2015), Exercise 5.1(c): `φ_π*` is strictly increasing in the slope `κ > 0`
(for `r ≥ 0`). -/
theorem phiR_strictMonoOn_kappa {ϑ σ r : ℝ} (hϑ : 0 < ϑ) (hσ : 0 < σ) (hr : 0 ≤ r) :
    StrictMonoOn (fun κ => phiR ϑ σ κ r) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  simp only [phiR_eq hϑ.ne']
  have h1 : a * σ * (1 + a ^ 2 * r) < b * σ * (1 + b ^ 2 * r) := by
    have h3 : a ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ ha.le hab.le 3
    have ea : a * σ * (1 + a ^ 2 * r) = a * σ + σ * r * a ^ 3 := by ring
    have eb : b * σ * (1 + b ^ 2 * r) = b * σ + σ * r * b ^ 3 := by ring
    rw [ea, eb]
    nlinarith [mul_le_mul_of_nonneg_left h3 (mul_nonneg hσ.le hr),
      mul_lt_mul_of_pos_right hab hσ]
  have h2 : a * σ * r ≤ b * σ * r :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hab.le hσ.le) hr
  have := div_lt_div_of_pos_right h1 hϑ
  linarith

/-- **Exercise 5.1(c), aggressive responses** (Galí 2015, p. 159): as the weight on output
`ϑ → 0⁺`, `φ_π* → ∞`. -/
theorem tendsto_phiR_weight_zero {σ κ r : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hr : 0 ≤ r) :
    Tendsto (fun ϑ => phiR ϑ σ κ r) (𝓝[>] 0) atTop := by
  have hc : 0 < κ * σ * (1 + κ ^ 2 * r) := by positivity
  have h : Tendsto (fun ϑ : ℝ => κ * σ * (1 + κ ^ 2 * r) * ϑ⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop hc
  refine tendsto_atTop_mono' _ ?_ h
  filter_upwards [self_mem_nhdsWithin] with ϑ hϑ
  simp only [Set.mem_Ioi] at hϑ
  rw [phiR_eq hϑ.ne', ← div_eq_mul_inv]
  have : 0 ≤ κ * σ * r := by positivity
  linarith

/-- **Exercise 5.1(c), aggressive responses** (Galí 2015, p. 159): as demand shocks dominate,
`r = σ_z²/σ_u² → ∞`, `φ_π* → ∞`. -/
theorem tendsto_phiR_ratio_atTop {ϑ σ κ : ℝ} (hϑ : 0 < ϑ) (hσ : 0 < σ) (hκ : 0 < κ) :
    Tendsto (fun r => phiR ϑ σ κ r) atTop atTop := by
  have hc : 0 < κ * σ / ϑ * (ϑ + κ ^ 2) := by positivity
  have h : Tendsto (fun r : ℝ => κ * σ / ϑ + κ * σ / ϑ * (ϑ + κ ^ 2) * r) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop hc)
  refine h.congr fun r => ?_
  simp only [phiR]
  ring

/-- Galí (2015), Exercise 5.1(c): as `ϑ → ∞`, `φ_π* → κσ r`. -/
theorem tendsto_phiR_weight_atTop (σ κ r : ℝ) :
    Tendsto (fun ϑ => phiR ϑ σ κ r) atTop (𝓝 (κ * σ * r)) := by
  have h : Tendsto (fun ϑ : ℝ => κ * σ * (1 + κ ^ 2 * r) / ϑ + κ * σ * r) atTop
      (𝓝 (0 + κ * σ * r)) :=
    (tendsto_const_nhds.div_atTop tendsto_id).add tendsto_const_nhds
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with ϑ hϑ
  rw [phiR_eq hϑ.ne']

/-- Galí (2015), Exercise 5.1(c): with supply shocks only (`r → 0`), `φ_π* → κσ/ϑ`. -/
theorem tendsto_phiR_ratio_zero (ϑ σ κ : ℝ) :
    Tendsto (fun r => phiR ϑ σ κ r) (𝓝 0) (𝓝 (κ * σ / ϑ)) := by
  have hc : Continuous fun r : ℝ => phiR ϑ σ κ r := by
    unfold phiR; fun_prop
  have := hc.tendsto 0
  simpa [phiR] using this

end Gali.DiscretionCommitment.Ex5_1
