/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR5ThreeByThree
import KeynesianStickyPrices.History

/-!
# Determinacy of the three-equation model with the inertial rule (18.2)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 18, eq. (18.2), p. 427:
`i_t = φ_i i_{t−1} + φ_π π_t + φ_x x_t + φ_{π,1} E_t π_{t+1} + φ_{x,1} E_t x_{t+1} + u_{i,t}`,
with the IS curve (17.15)–(17.16) and the Phillips curve (17.17). With inertia `φ_i ≠ 0` the
lagged rate is a predetermined variable and the deviation system is three-dimensional. The book
makes no determinacy claim about it; this module characterises determinacy completely, as a
completion, with the Blanchard–Kahn theorem for one predetermined variable
(`TidyR5BlanchardKahn.determinate3_iff`, restated from the Woodford Chapter 4 project).

## The system

`Equil182`: the model in deviations, with disturbances `u = (u_π, u_x, u_i)` in the Phillips
curve, the IS curve and the rule, state `y_t = (π_t, x_t, i_{t−1})` (so `i_t = y_{t+1,2}`), a
given initial lagged rate, adapted and bounded. It implies the book's (18.2)
(`equil182_rule182`). `Determinate182`: for every bounded adapted disturbance and every
initial lagged rate there is exactly one equilibrium.

For `β ≠ 0` and `1 − σφ_{x,1} ≠ 0` the model is `E_t y_{t+1} = A y_t + W u_t` with the explicit
matrices `A182`, `W182` (`equil182_iff`), `W` invertible (`W182_mul_U182`), so
`Determinate182 ↔ TidyR5BlanchardKahn.Determinate3 A182` (`determinate182_iff_three`).

## The characterisation

* `cubic_A182`: the eigenvalues of `A` are the roots of
  `det(λM − N) = (βλ − 1)[(λ − 1)(λ − φ_i) − σλ(φ_{x,1}λ + φ_x)]
  − σκλ[(λ − φ_i) − (φ_{π,1}λ + φ_π)]`
  (`β(1 − σφ_{x,1})` times the characteristic polynomial); `P1_A182`: at `λ = 1`,
  `σ[κ(φ_π + φ_{π,1} + φ_i − 1) + (1 − β)(φ_x + φ_{x,1})]/(β(1 − σφ_{x,1}))` — the long-run
  Taylor principle with all four responses and the inertia.
* `generic182_iff`: the Blanchard–Kahn genericity condition (the stable eigenvector has a nonzero
  lagged-rate component) holds iff `κ(φ_π + φ_{π,1}μ) + (φ_x + φ_{x,1}μ)(1 − βμ) ≠ 0` at
  `μ = 1/λ₁`, the stable root of the interest-rate peg: the rule must respond along the peg's
  stable direction.
* **`determinate182_iff`**: for `σ, κ, β > 0` and `1 − σφ_{x,1} ≠ 0`, determinate iff exactly one
  root of `det(λM − N)` lies in the open unit disc and two outside the closed disc
  (`TidyR5SchurCohn.OneInTwoOut`) **and** that response condition holds;
  `determinate182_iff_cases` with Woodford's Cases I, II, III′ (Prop. C.2).

## Backward-looking responses: an explicit condition

With `φ_{π,1} = φ_{x,1} = 0` the matrix is Woodford's `A44` with `φ_x` in quarterly units
(`A182_noForward`), and for `0 < β < 1`, `σ, κ > 0`, `φ_i, φ_π, φ_x ≥ 0`
(`determinate182_noForward_iff`): determinate iff
`κ(φ_π + φ_i − 1) + (1 − β)φ_x > 0` **and** `φ_π > 0 ∨ φ_x > 0`. Hence:

* superinertial rules `φ_i ≥ 1` that respond at all are determinate
  (`determinate182_superinertial`);
* inertia alone is never enough: with `φ_π = φ_x = 0` the rule `i_t = φ_i i_{t−1} + u_t` makes
  the rate exogenous and the system is not determinate for any `φ_i ≥ 0`, although for `φ_i > 1`
  the long-run Taylor principle `κ(φ_i − 1) > 0` holds (`not_determinate182_no_response`);
* without inertia it is the two-dimensional condition of (18.1) (`TaylorDeterminacy.Determinate`,
  Bullard–Mitra; `determinate182_noInertia_iff`).
-/

namespace Cochrane.KeynesianStickyPrices.TidyR5Inertia

open Filter Topology FullModel TidyR5SchurCohn TidyR5BlanchardKahn TidyR5ThreeByThree
open scoped Matrix

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The model -/

/-- Cochrane (2023), eq. (18.2), p. 427, with (17.15)–(17.17), in deviations: state
`y_t = (π_t, x_t, i_{t−1})`, disturbances `u_t = (u_{π,t}, u_{x,t}, u_{i,t})`; the Phillips curve,
the IS curve with `r_t = i_t − E_t π_{t+1}`, the rule
`i_t = φ_i i_{t−1} + φ_π π_t + φ_x x_t + φ_{π,1} E_t π_{t+1} + φ_{x,1} E_t x_{t+1} + u_{i,t}`,
the initial lagged rate `i_{−1} = i0`, adaptedness and boundedness. -/
def Equil182 (σ β κ φi φπ φx φπ1 φx1 : ℝ) (u : ℕ → Fin 3 → Ω → ℝ) (i0 : ℝ)
    (y : ℕ → Fin 3 → Ω → ℝ) : Prop :=
  (∀ t, y t 0 = β • 𝔼.E t (y (t + 1) 0) + κ • y t 1 + u t 0) ∧
  (∀ t, y t 1 = 𝔼.E t (y (t + 1) 1) - σ • (y (t + 1) 2 - 𝔼.E t (y (t + 1) 0)) + u t 1) ∧
  (∀ t, y (t + 1) 2 = φi • y t 2 + φπ • y t 0 + φx • y t 1 + φπ1 • 𝔼.E t (y (t + 1) 0) +
    φx1 • 𝔼.E t (y (t + 1) 1) + u t 2) ∧
  y 0 2 = (fun _ => i0) ∧ VAdapted 𝔼 y ∧ VBounded y

/-- Cochrane (2023), eq. (18.2), p. 427: determinacy with inertia — for every bounded adapted
disturbance and every initial lagged rate there is exactly one equilibrium. -/
def Determinate182 (σ β κ φi φπ φx φπ1 φx1 : ℝ) : Prop :=
  ∀ u : ℕ → Fin 3 → Ω → ℝ, VBounded u → VAdapted 𝔼 u → ∀ i0 : ℝ,
    ∃! y, Equil182 𝔼 σ β κ φi φπ φx φπ1 φx1 u i0 y

/-- Cochrane (2023), eq. (18.2), p. 427: an equilibrium satisfies the book's rule
`History.Rule182` with `i_t = y_{t+1,2}`, `x_t = y_{t,1}`, `π_t = y_{t,0}`. -/
theorem equil182_rule182 {σ β κ φi φπ φx φπ1 φx1 : ℝ} {u : ℕ → Fin 3 → Ω → ℝ} {i0 : ℝ}
    {y : ℕ → Fin 3 → Ω → ℝ} (h : Equil182 𝔼 σ β κ φi φπ φx φπ1 φx1 u i0 y) :
    History.Rule182 𝔼 φi φπ φx φπ1 φx1 (fun t => u t 2) (fun t => y (t + 1) 2)
      (fun t => y t 1) (fun t => y t 0) :=
  fun t => h.2.2.1 (t + 1)

/-! ### The first-order form -/

/-- Cochrane (2023), eq. (18.2), p. 427: the transition matrix `A` of
`E_t y_{t+1} = A y_t + W u_t`, `y = (π, x, i_{−1})`. -/
noncomputable def A182 (σ β κ φi φπ φx φπ1 φx1 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![β⁻¹, -(β⁻¹ * κ), 0;
    σ * (φπ + (φπ1 - 1) * β⁻¹) / (1 - σ * φx1),
      (1 + σ * φx - σ * (φπ1 - 1) * β⁻¹ * κ) / (1 - σ * φx1), σ * φi / (1 - σ * φx1);
    φπ + φπ1 * β⁻¹ + φx1 * (σ * (φπ + (φπ1 - 1) * β⁻¹) / (1 - σ * φx1)),
      φx - φπ1 * β⁻¹ * κ + φx1 * ((1 + σ * φx - σ * (φπ1 - 1) * β⁻¹ * κ) / (1 - σ * φx1)),
      φi + φx1 * (σ * φi / (1 - σ * φx1))]

/-- Cochrane (2023), eq. (18.2), p. 427: the loading `W` of the disturbances in
`E_t y_{t+1} = A y_t + W u_t`. -/
noncomputable def W182 (σ β φπ1 φx1 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-β⁻¹, 0, 0;
    σ * (1 - φπ1) * β⁻¹ / (1 - σ * φx1), -1 / (1 - σ * φx1), σ / (1 - σ * φx1);
    -(φπ1 * β⁻¹) + φx1 * (σ * (1 - φπ1) * β⁻¹ / (1 - σ * φx1)), -(φx1 / (1 - σ * φx1)),
      1 + φx1 * (σ / (1 - σ * φx1))]

/-- Cochrane (2023), eq. (18.2): the inverse of `W182`. -/
def U182 (σ β φπ1 φx1 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-β, 0, 0; -σ, -1, σ; -φπ1, -φx1, 1]

/-- Cochrane (2023), eq. (18.2): `W U = 1`, so every bounded adapted forcing of the first-order
system comes from a bounded adapted disturbance `u`. -/
theorem W182_mul_U182 {σ β φπ1 φx1 : ℝ} (hβ : β ≠ 0) (hg : 1 - σ * φx1 ≠ 0) :
    W182 σ β φπ1 φx1 * U182 σ β φπ1 φx1 = 1 := by
  have hg' : 1 - φx1 * σ ≠ 0 := by rwa [mul_comm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [W182, U182, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp <;> ring

/-- Cochrane (2023), eq. (18.2), p. 427: for `β ≠ 0`, `1 − σφ_{x,1} ≠ 0` and adapted
disturbances, `Equil182` is the Blanchard–Kahn equilibrium of `E_t y_{t+1} = A y_t + W u_t`. -/
theorem equil182_iff {σ β κ φi φπ φx φπ1 φx1 : ℝ} (hβ : β ≠ 0) (hg : 1 - σ * φx1 ≠ 0)
    {u : ℕ → Fin 3 → Ω → ℝ} (hu : VAdapted 𝔼 u) (i0 : ℝ) (y : ℕ → Fin 3 → Ω → ℝ) :
    Equil182 𝔼 σ β κ φi φπ φx φπ1 φx1 u i0 y ↔
      Equil3 𝔼 (A182 σ β κ φi φπ φx φπ1 φx1) (fun t => rvMul (W182 σ β φπ1 φx1) (u t)) i0 y := by
  have hb : β⁻¹ * β = 1 := inv_mul_cancel₀ hβ
  constructor
  · rintro ⟨hN, hI, hR, h0, ha, hbd⟩
    have hp : ∀ t, 𝔼.E t (y (t + 1) 2) = y (t + 1) 2 := by
      intro t
      rw [hR t, map_add, map_add, map_add, map_add, map_add, map_smul, map_smul, map_smul,
        map_smul, map_smul, ha t 0, ha t 1, ha t 2, 𝔼.E_E_self, 𝔼.E_E_self, hu t 2]
    refine ⟨fun t i => ?_, ha, hp, h0, hbd⟩
    funext ω
    have n := congrFun (hN t) ω
    have s := congrFun (hI t) ω
    have r := congrFun (hR t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at n s r
    have hP : 𝔼.E t (y (t + 1) 0) ω = β⁻¹ * (y t 0 ω - κ * y t 1 ω - u t 0 ω) := by
      linear_combination (-β⁻¹) * n - (𝔼.E t (y (t + 1) 0) ω) * hb
    have hX : (1 - σ * φx1) * 𝔼.E t (y (t + 1) 1) ω = (1 + σ * φx) * y t 1 ω +
        σ * φi * y t 2 ω + σ * φπ * y t 0 ω + σ * (φπ1 - 1) * 𝔼.E t (y (t + 1) 0) ω +
        σ * u t 2 ω - u t 1 ω := by
      linear_combination -s + σ * r
    have hX' : 𝔼.E t (y (t + 1) 1) ω =
        (1 - σ * φx1)⁻¹ * ((1 - σ * φx1) * 𝔼.E t (y (t + 1) 1) ω) := by
      field_simp
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Pi.add_apply]
      rw [hP]
      simp [rvMul_apply, Fin.sum_univ_three, A182, W182]
      ring
    · simp only [Fin.mk_one, Fin.isValue, Pi.add_apply]
      rw [hX', hX, hP]
      simp [rvMul_apply, Fin.sum_univ_three, A182, W182]
      ring
    · simp only [Fin.reduceFinMk, Fin.isValue, Pi.add_apply]
      rw [hp t, r, hX', hX, hP]
      simp [rvMul_apply, Fin.sum_univ_three, A182, W182]
      ring
  · rintro ⟨hs, ha, hp, h0, hbd⟩
    have row : ∀ t (i : Fin 3) ω, 𝔼.E t (y (t + 1) i) ω =
        (rvMul (A182 σ β κ φi φπ φx φπ1 φx1) (y t) i +
          rvMul (W182 σ β φπ1 φx1) (u t) i) ω := fun t i ω => congrFun (hs t i) ω
    have r0 : ∀ t ω, 𝔼.E t (y (t + 1) 0) ω =
        β⁻¹ * y t 0 ω - β⁻¹ * κ * y t 1 ω - β⁻¹ * u t 0 ω := by
      intro t ω
      rw [row]
      simp [rvMul_apply, Fin.sum_univ_three, A182, W182]
      ring
    have r1 : ∀ t ω, 𝔼.E t (y (t + 1) 1) ω =
        σ * (φπ + (φπ1 - 1) * β⁻¹) / (1 - σ * φx1) * y t 0 ω +
        (1 + σ * φx - σ * (φπ1 - 1) * β⁻¹ * κ) / (1 - σ * φx1) * y t 1 ω +
        σ * φi / (1 - σ * φx1) * y t 2 ω + σ * (1 - φπ1) * β⁻¹ / (1 - σ * φx1) * u t 0 ω +
        -1 / (1 - σ * φx1) * u t 1 ω + σ / (1 - σ * φx1) * u t 2 ω := by
      intro t ω
      rw [row]
      simp [rvMul_apply, Fin.sum_univ_three, A182, W182]
      ring
    have r2 : ∀ t ω, y (t + 1) 2 ω = φi * y t 2 ω + φπ * y t 0 ω + φx * y t 1 ω +
        φπ1 * 𝔼.E t (y (t + 1) 0) ω + φx1 * 𝔼.E t (y (t + 1) 1) ω + u t 2 ω := by
      intro t ω
      rw [← hp t, row, r0, r1]
      simp [rvMul_apply, Fin.sum_univ_three, A182, W182]
      ring
    refine ⟨fun t => ?_, fun t => ?_, fun t => ?_, h0, ha, hbd⟩ <;> funext ω <;>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    · rw [r0]; linear_combination (-(y t 0 ω - κ * y t 1 ω - u t 0 ω)) * hb
    · rw [r2, r1, r0]; field_simp; ring
    · rw [r2]

/-- Cochrane (2023), eq. (18.2), p. 427: for `β ≠ 0`, `1 − σφ_{x,1} ≠ 0`, determinacy of the
model with inertia is Blanchard–Kahn determinacy of `E_t y_{t+1} = A y_t + w_t`. -/
theorem determinate182_iff_three {σ β κ φi φπ φx φπ1 φx1 : ℝ} (hβ : β ≠ 0)
    (hg : 1 - σ * φx1 ≠ 0) :
    Determinate182 𝔼 σ β κ φi φπ φx φπ1 φx1 ↔ Determinate3 𝔼 (A182 σ β κ φi φπ φx φπ1 φx1) := by
  constructor
  · intro h w hw hwa x0
    have hub := vBounded_rvMul (U182 σ β φπ1 φx1) hw
    have hua := vAdapted_rvMul 𝔼 (U182 σ β φπ1 φx1) hwa
    have hwu : (fun t => rvMul (W182 σ β φπ1 φx1) (rvMul (U182 σ β φπ1 φx1) (w t))) = w :=
      funext fun t => by rw [rvMul_rvMul, W182_mul_U182 hβ hg, rvMul_one]
    obtain ⟨y, hy, huniq⟩ := h _ hub hua x0
    have hiff := fun y => equil182_iff 𝔼 (κ := κ) (φi := φi) (φπ := φπ) (φx := φx)
      (φπ1 := φπ1) hβ hg hua x0 y
    rw [hwu] at hiff
    exact ⟨y, (hiff y).mp hy, fun y' hy' => huniq y' ((hiff y').mpr hy')⟩
  · intro h u hu hua i0
    obtain ⟨y, hy, huniq⟩ := h _ (vBounded_rvMul (W182 σ β φπ1 φx1) hu)
      (vAdapted_rvMul 𝔼 (W182 σ β φπ1 φx1) hua) i0
    exact ⟨y, (equil182_iff 𝔼 hβ hg hua i0 y).mpr hy,
      fun y' hy' => huniq y' ((equil182_iff 𝔼 hβ hg hua i0 y').mp hy')⟩

/-! ### The characteristic polynomial -/

/-- Cochrane (2023), eq. (18.2), p. 427: `β(1 − σφ_{x,1})` times the characteristic polynomial of
`A` is `det(λM − N) = (βλ − 1)[(λ − 1)(λ − φ_i) − σλ(φ_{x,1}λ + φ_x)]
− σκλ[(λ − φ_i) − (φ_{π,1}λ + φ_π)]`. -/
theorem cubic_A182 {σ β κ φi φπ φx φπ1 φx1 : ℝ} (hβ : β ≠ 0) (hg : 1 - σ * φx1 ≠ 0) (l : ℝ) :
    β * (1 - σ * φx1) * cubicR (ch2 (A182 σ β κ φi φπ φx φπ1 φx1))
        (ch1 (A182 σ β κ φi φπ φx φπ1 φx1)) (ch0 (A182 σ β κ φi φπ φx φπ1 φx1)) l =
      (β * l - 1) * ((l - 1) * (l - φi) - σ * l * (φx1 * l + φx)) -
        σ * κ * l * ((l - φi) - (φπ1 * l + φπ)) := by
  simp [cubicR, ch2, ch1, ch0, A182]
  field_simp
  ring

/-- Cochrane (2023), eq. (18.2), p. 427, and Woodford's (C.22): the characteristic polynomial at
`λ = 1` is `σ[κ(φ_π + φ_{π,1} + φ_i − 1) + (1 − β)(φ_x + φ_{x,1})]/(β(1 − σφ_{x,1}))` — its
sign is the long-run Taylor principle with all responses and the inertia. -/
theorem P1_A182 {σ β κ φi φπ φx φπ1 φx1 : ℝ} (hβ : β ≠ 0) (hg : 1 - σ * φx1 ≠ 0) :
    P1 (ch2 (A182 σ β κ φi φπ φx φπ1 φx1)) (ch1 (A182 σ β κ φi φπ φx φπ1 φx1))
        (ch0 (A182 σ β κ φi φπ φx φπ1 φx1)) =
      σ * (κ * (φπ + φπ1 + φi - 1) + (1 - β) * (φx + φx1)) / (β * (1 - σ * φx1)) := by
  have h := cubic_A182 (κ := κ) (φi := φi) (φπ := φπ) (φx := φx) (φπ1 := φπ1) hβ hg 1
  have e : P1 (ch2 (A182 σ β κ φi φπ φx φπ1 φx1)) (ch1 (A182 σ β κ φi φπ φx φπ1 φx1))
      (ch0 (A182 σ β κ φi φπ φx φπ1 φx1)) = cubicR (ch2 (A182 σ β κ φi φπ φx φπ1 φx1))
        (ch1 (A182 σ β κ φi φπ φx φπ1 φx1)) (ch0 (A182 σ β κ φi φπ φx φπ1 φx1)) 1 := by
    simp [P1, cubicR]
  rw [e, eq_div_iff (mul_ne_zero hβ hg)]
  linear_combination h

/-! ### Genericity -/

/-- Cochrane (2023), eq. (18.2): for a vector with zero lagged-rate component, the eigenvector
equations `A v = μ v` reduce to `(1 − βμ) v_π = κ v_x`, `(1 − μ) v_x = σμ v_π` and
`(φ_π + φ_{π,1}μ) v_π + (φ_x + φ_{x,1}μ) v_x = 0` (the three identities behind
`generic182_iff`). -/
theorem rows182 {σ β κ φi φπ φx φπ1 φx1 : ℝ} (hβ : β ≠ 0) (hg : 1 - σ * φx1 ≠ 0) (μ : ℝ)
    (v : Fin 3 → ℝ) (h2 : v 2 = 0) :
    β * ((A182 σ β κ φi φπ φx φπ1 φx1 *ᵥ v) 0 - μ * v 0) = (1 - β * μ) * v 0 - κ * v 1 ∧
      (1 - σ * φx1) * ((A182 σ β κ φi φπ φx φπ1 φx1 *ᵥ v) 1 - μ * v 1) =
        σ * ((φπ + φπ1 * μ) * v 0 + (φx + φx1 * μ) * v 1) + ((1 - μ) * v 1 - σ * μ * v 0) +
          σ * (φπ1 - 1) * ((A182 σ β κ φi φπ φx φπ1 φx1 *ᵥ v) 0 - μ * v 0) ∧
      (A182 σ β κ φi φπ φx φπ1 φx1 *ᵥ v) 2 = (φπ + φπ1 * μ) * v 0 + (φx + φx1 * μ) * v 1 +
        φπ1 * ((A182 σ β κ φi φπ φx φπ1 φx1 *ᵥ v) 0 - μ * v 0) +
        φx1 * ((A182 σ β κ φi φπ φx φπ1 φx1 *ᵥ v) 1 - μ * v 1) := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h2, mul_zero, add_zero, A182,
    Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
    Matrix.cons_val_one, Matrix.cons_val]
  refine ⟨by field_simp; ring, by field_simp; ring, by ring⟩

/-- Cochrane (2023), §17.4.1, eq. (5.6): the roots of `βμ² − (1 + β + σκ)μ + 1` are `1/λ₁` and
`1/λ₂`; the only one in the open unit disc is `1/λ₁` (the stable root of the peg). -/
theorem peg_root {σ β κ μ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hμ : |μ| < 1)
    (hq : (1 - β * μ) * (1 - μ) - σ * κ * μ = 0) : μ = (lam1 σ β κ)⁻¹ := by
  have hs := lam_sum σ β κ
  have hp := lam_prod ha hβ
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans (one_lt_lam1 ha hβ)
  have hfac : (lam1 σ β κ * μ - 1) * (lam2 σ β κ * μ - 1) = 0 := by
    linear_combination hq + μ ^ 2 * hp - μ * hs
  rcases mul_eq_zero.mp hfac with h | h
  · field_simp
    linarith
  · exfalso
    have : lam2 σ β κ * |μ| < 1 := by
      calc lam2 σ β κ * |μ| < 1 * 1 := mul_lt_mul'' h21 hμ h2.le (abs_nonneg _)
        _ = 1 := one_mul 1
    have e : lam2 σ β κ * μ = 1 := by linarith
    have : |lam2 σ β κ * μ| = lam2 σ β κ * |μ| := by rw [abs_mul, abs_of_pos h2]
    rw [e, abs_one] at this
    linarith

/-- Cochrane (2023), eq. (18.2), p. 427: for `σ, κ, β > 0` and `1 − σφ_{x,1} ≠ 0`, the
Blanchard–Kahn genericity condition holds iff
`κ(φ_π + φ_{π,1}μ) + (φ_x + φ_{x,1}μ)(1 − βμ) ≠ 0` at `μ = 1/λ₁`. -/
theorem generic182_iff {σ β κ φi φπ φx φπ1 φx1 : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hg : 1 - σ * φx1 ≠ 0) :
    Generic (A182 σ β κ φi φπ φx φπ1 φx1) ↔
      κ * (φπ + φπ1 * (lam1 σ β κ)⁻¹) + (φx + φx1 * (lam1 σ β κ)⁻¹) *
        (1 - β * (lam1 σ β κ)⁻¹) ≠ 0 := by
  have ha := mul_pos hσ hκ
  have hl1 := one_lt_lam1 ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans hl1
  set m := (lam1 σ β κ)⁻¹ with hm
  have hm0 : 0 < m := inv_pos.mpr hl0
  have hm1 : m < 1 := inv_lt_one_of_one_lt₀ hl1
  have hmabs : |m| < 1 := by rw [abs_of_pos hm0]; exact hm1
  have hqm : (1 - β * m) * (1 - m) - σ * κ * m = 0 := by
    have hs := lam_sum σ β κ
    have hp := lam_prod ha hβ
    have : lam1 σ β κ * m = 1 := by rw [hm]; field_simp
    linear_combination (lam2 σ β κ * m - 1) * this - m ^ 2 * hp + m * hs
  constructor
  · intro hgen hexpr
    have hv := hgen m ![κ, 1 - β * m, 0] hmabs ?_ (by simp)
    · have := congrFun hv 0
      simp at this
      linarith
    · obtain ⟨e0, e1, e2⟩ := rows182 (κ := κ) (φi := φi) (φπ := φπ) (φx := φx) (φπ1 := φπ1)
        hβ.ne' hg m ![κ, 1 - β * m, 0] (by simp)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1 e2
      have E0 : (A182 σ β κ φi φπ φx φπ1 φx1 *ᵥ ![κ, 1 - β * m, 0]) 0 - m * κ = 0 := by
        have : β * ((A182 σ β κ φi φπ φx φπ1 φx1 *ᵥ ![κ, 1 - β * m, 0]) 0 - m * κ) = 0 := by
          rw [e0]; ring
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hβ.ne'
        · exact h
      have E1 : (A182 σ β κ φi φπ φx φπ1 φx1 *ᵥ ![κ, 1 - β * m, 0]) 1 - m * (1 - β * m) = 0 := by
        have : (1 - σ * φx1) *
            ((A182 σ β κ φi φπ φx φπ1 φx1 *ᵥ ![κ, 1 - β * m, 0]) 1 - m * (1 - β * m)) = 0 := by
          rw [e1, E0]; linear_combination σ * hexpr + hqm
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hg
        · exact h
      funext j
      fin_cases j
      · simp only [Pi.smul_apply, smul_eq_mul]; simp; linarith
      · simp only [Pi.smul_apply, smul_eq_mul]; simp; linarith
      · change (A182 σ β κ φi φπ φx φπ1 φx1 *ᵥ ![κ, 1 - β * m, 0]) 2 =
          m * ![κ, 1 - β * m, 0] 2
        rw [e2, E0, E1]
        simp
        linear_combination hexpr
  · intro hexpr μ v hμ hv h2
    obtain ⟨e0, e1, e2⟩ := rows182 (κ := κ) (φi := φi) (φπ := φπ) (φx := φx) (φπ1 := φπ1)
      hβ.ne' hg μ v h2
    have E0 : (A182 σ β κ φi φπ φx φπ1 φx1 *ᵥ v) 0 - μ * v 0 = 0 := by
      rw [hv]; simp
    have E1 : (A182 σ β κ φi φπ φx φπ1 φx1 *ᵥ v) 1 - μ * v 1 = 0 := by
      rw [hv]; simp
    have E2 : (A182 σ β κ φi φπ φx φπ1 φx1 *ᵥ v) 2 = 0 := by
      rw [hv]; simp [h2]
    rw [E0, mul_zero] at e0
    rw [E0, E1, mul_zero, mul_zero, add_zero] at e1
    rw [E0, E1, E2, mul_zero, mul_zero, add_zero, add_zero] at e2
    -- `(1 − βμ) v₀ = κ v₁`, `(1 − μ) v₁ = σμ v₀`, `(φ_π + φ_{π,1}μ) v₀ + (φ_x + φ_{x,1}μ) v₁ = 0`
    have r1 : (1 - μ) * v 1 - σ * μ * v 0 = 0 := by linear_combination -e1 + σ * e2
    have hq : ((1 - β * μ) * (1 - μ) - σ * κ * μ) * v 0 = 0 := by
      linear_combination -(1 - μ) * e0 + κ * r1
    by_cases hv0 : v 0 = 0
    · have hv1 : v 1 = 0 := by
        rw [hv0] at e0
        have : κ * v 1 = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hκ.ne'
        · exact h
      funext j
      fin_cases j
      · exact hv0
      · exact hv1
      · exact h2
    · exfalso
      have hq0 : (1 - β * μ) * (1 - μ) - σ * κ * μ = 0 :=
        (mul_eq_zero.mp hq).resolve_right hv0
      have hμm := peg_root ha hβ hμ hq0
      rw [← hm] at hμm
      rw [hμm] at e0 e2
      have key : (κ * (φπ + φπ1 * m) + (φx + φx1 * m) * (1 - β * m)) * v 0 = 0 := by
        linear_combination -κ * e2 - (φx + φx1 * m) * e0
      exact hexpr ((mul_eq_zero.mp key).resolve_right hv0)

/-! ### The characterisation -/

/-- **Determinacy with inertia** (Cochrane (2023), eq. (18.2), p. 427; the book makes no claim):
for `σ, κ, β > 0` and `1 − σφ_{x,1} ≠ 0`, under any expectation system on a nonempty state
space, the model with the inertial rule is determinate iff exactly one root of
`det(λM − N)` (`cubic_A182`) lies in the open unit disc and two outside the closed disc, and
`κ(φ_π + φ_{π,1}μ) + (φ_x + φ_{x,1}μ)(1 − βμ) ≠ 0` at `μ = 1/λ₁`. -/
theorem determinate182_iff [Nonempty Ω] {σ β κ φi φπ φx φπ1 φx1 : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (hg : 1 - σ * φx1 ≠ 0) :
    Determinate182 𝔼 σ β κ φi φπ φx φπ1 φx1 ↔
      OneInTwoOut (ch2 (A182 σ β κ φi φπ φx φπ1 φx1)) (ch1 (A182 σ β κ φi φπ φx φπ1 φx1))
          (ch0 (A182 σ β κ φi φπ φx φπ1 φx1)) ∧
        κ * (φπ + φπ1 * (lam1 σ β κ)⁻¹) + (φx + φx1 * (lam1 σ β κ)⁻¹) *
          (1 - β * (lam1 σ β κ)⁻¹) ≠ 0 := by
  rw [determinate182_iff_three 𝔼 hβ.ne' hg, determinate3_iff, generic182_iff hσ hκ hβ hg]

/-- Cochrane (2023), eq. (18.2), with Woodford's Prop. C.2 (Cases I, II, III′): the same
characterisation with the root count written through `P(1)`, `P(−1)` and the coefficients. -/
theorem determinate182_iff_cases [Nonempty Ω] {σ β κ φi φπ φx φπ1 φx1 : ℝ} (hσ : 0 < σ)
    (hκ : 0 < κ) (hβ : 0 < β) (hg : 1 - σ * φx1 ≠ 0) :
    Determinate182 𝔼 σ β κ φi φπ φx φπ1 φx1 ↔
      (CaseI3 (ch2 (A182 σ β κ φi φπ φx φπ1 φx1)) (ch1 (A182 σ β κ φi φπ φx φπ1 φx1))
          (ch0 (A182 σ β κ φi φπ φx φπ1 φx1)) ∨
        CaseII3 (ch2 (A182 σ β κ φi φπ φx φπ1 φx1)) (ch1 (A182 σ β κ φi φπ φx φπ1 φx1))
          (ch0 (A182 σ β κ φi φπ φx φπ1 φx1)) ∨
        CaseIII3' (ch2 (A182 σ β κ φi φπ φx φπ1 φx1)) (ch1 (A182 σ β κ φi φπ φx φπ1 φx1))
          (ch0 (A182 σ β κ φi φπ φx φπ1 φx1))) ∧
        κ * (φπ + φπ1 * (lam1 σ β κ)⁻¹) + (φx + φx1 * (lam1 σ β κ)⁻¹) *
          (1 - β * (lam1 σ β κ)⁻¹) ≠ 0 := by
  rw [determinate182_iff 𝔼 hσ hκ hβ hg, oneInTwoOut_iff_cases]

/-! ### Backward-looking responses -/

/-- Cochrane (2023), eq. (18.2) with `φ_{π,1} = φ_{x,1} = 0`: the matrix is Woodford's `A44`
(Prop. 4.4) with the output response in Woodford's annualised units, `4φ_x`. -/
theorem A182_noForward (σ β κ φi φπ φx : ℝ) :
    A182 σ β κ φi φπ φx 0 0 = A44 β κ σ φi φπ (4 * φx) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [A182, A44, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val_one, Matrix.cons_val] <;> ring

/-- **Determinacy with backward-looking inertia** (Cochrane (2023), eq. (18.2), p. 427, with
`φ_{π,1} = φ_{x,1} = 0`; Woodford's Prop. 4.4 as corrected in `TidyR5ThreeByThree.prop44`): for
`0 < β < 1`, `σ, κ > 0`, `φ_i, φ_π, φ_x ≥ 0`, the model is determinate iff
`κ(φ_π + φ_i − 1) + (1 − β)φ_x > 0` and the rule responds to inflation or output. -/
theorem determinate182_noForward_iff [Nonempty Ω] {σ β κ φi φπ φx : ℝ} (hσ : 0 < σ)
    (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) (hφi : 0 ≤ φi) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    Determinate182 𝔼 σ β κ φi φπ φx 0 0 ↔
      0 < κ * (φπ + φi - 1) + (1 - β) * φx ∧ (0 < φπ ∨ 0 < φx) := by
  have hg : (1 : ℝ) - σ * 0 ≠ 0 := by norm_num
  rw [determinate182_iff_three 𝔼 hβ.ne' hg, A182_noForward]
  have h29 : 1 - φi < φπ + (1 - β) / (4 * κ) * (4 * φx) ↔
      0 < κ * (φπ + φi - 1) + (1 - β) * φx := by
    have e : (1 - β) / (4 * κ) * (4 * φx) = (1 - β) * φx / κ := by field_simp
    rw [e]
    constructor
    · intro h
      have : 0 < φπ + (1 - β) * φx / κ - (1 - φi) := by linarith
      have := mul_pos hκ this
      have e2 : κ * (φπ + (1 - β) * φx / κ - (1 - φi)) = κ * (φπ + φi - 1) + (1 - β) * φx := by
        field_simp; ring
      linarith
    · intro h
      have e2 : φπ + (1 - β) * φx / κ - (1 - φi) = (κ * (φπ + φi - 1) + (1 - β) * φx) / κ := by
        field_simp; ring
      have := div_pos h hκ
      linarith
  have h4 : (0 < φπ ∨ 0 < 4 * φx) ↔ (0 < φπ ∨ 0 < φx) := by
    constructor <;> rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have hφx4 : 0 ≤ 4 * φx := by linarith
  constructor
  · intro hd
    have hfor := determinateFor_of_determinate3 𝔼 hd (aIS σ)
    have h44 := (prop44 𝔼 hβ hβ1 hκ hσ hφi hφπ hφx4).mp ((determinate44_iff_for 𝔼 hβ.ne').mpr hfor)
    exact ⟨h29.mp h44.1, h4.mp h44.2⟩
  · rintro ⟨h1, h2⟩
    exact determinate3_of 𝔼 (oneInTwoOut_A44 hβ hβ1 hκ hσ hφi hφπ hφx4 (h29.mpr h1))
      (generic_A44 hβ hβ1 hκ hφπ hφx4 (h4.mpr h2))

/-- Cochrane (2023), eq. (18.2), p. 427 (superinertial rules): with `φ_i ≥ 1` and some response
to inflation or output, the model with backward-looking inertia is determinate. -/
theorem determinate182_superinertial [Nonempty Ω] {σ β κ φi φπ φx : ℝ} (hσ : 0 < σ)
    (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1) (hφi : 1 ≤ φi) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (hφ : 0 < φπ ∨ 0 < φx) : Determinate182 𝔼 σ β κ φi φπ φx 0 0 := by
  refine (determinate182_noForward_iff 𝔼 hσ hκ hβ hβ1 (by linarith) hφπ hφx).mpr ⟨?_, hφ⟩
  have h1 : 0 ≤ (1 - β) * φx := mul_nonneg (by linarith) hφx
  rcases hφ with h | h
  · have : 0 < κ * (φπ + φi - 1) := mul_pos hκ (by linarith)
    linarith
  · have : 0 < (1 - β) * φx := mul_pos (by linarith) h
    have : 0 ≤ κ * (φπ + φi - 1) := mul_nonneg hκ.le (by linarith)
    linarith

/-- Cochrane (2023), eq. (18.2), p. 427: inertia alone is not enough. With `φ_π = φ_x = 0` (and no
forward responses) the rule `i_t = φ_i i_{t−1} + u_{i,t}` makes the rate exogenous and the model
is not determinate for any `φ_i ≥ 0` — although for `φ_i > 1` the long-run Taylor principle
`κ(φ_π + φ_i − 1) + (1 − β)φ_x > 0` holds. -/
theorem not_determinate182_no_response [Nonempty Ω] {σ β κ φi : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (hβ1 : β < 1) (hφi : 0 ≤ φi) :
    ¬ Determinate182 𝔼 σ β κ φi 0 0 0 0 ∧
      (1 < φi → 0 < κ * (0 + φi - 1) + (1 - β) * 0) := by
  refine ⟨fun h => ?_, fun h => by
    simp only [zero_add, mul_zero, add_zero]; exact mul_pos hκ (by linarith)⟩
  obtain ⟨-, h2⟩ := (determinate182_noForward_iff 𝔼 hσ hκ hβ hβ1 hφi le_rfl le_rfl).mp h
  rcases h2 with h2 | h2 <;> exact lt_irrefl _ h2

/-- Cochrane (2023), eqs. (18.1)–(18.2), p. 427: without inertia and forward responses the
three-dimensional system is determinate iff the two-dimensional deviation system with (18.1) is
(`TaylorDeterminacy.determinate_iff_BM`, `History.rule181_determinate_iff`). -/
theorem determinate182_noInertia_iff [Nonempty Ω] {σ β κ φπ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    Determinate182 𝔼 σ β κ 0 φπ φx 0 0 ↔ TaylorDeterminacy.Determinate 𝔼 σ β κ φπ φx := by
  rw [determinate182_noForward_iff 𝔼 hσ hκ hβ hβ1 le_rfl hφπ hφx,
    TaylorDeterminacy.determinate_iff_BM 𝔼 hσ hκ hβ hβ1 hφπ hφx]
  constructor
  · rintro ⟨h, -⟩; linarith
  · intro h
    refine ⟨by linarith, ?_⟩
    by_contra hc
    push Not at hc
    have e1 : φπ = 0 := le_antisymm hc.1 hφπ
    have e2 : φx = 0 := le_antisymm hc.2 hφx
    rw [e1, e2] at h
    linarith

end Cochrane.KeynesianStickyPrices.TidyR5Inertia
