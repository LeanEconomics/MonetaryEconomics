/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.BlanchardKahn

/-!
# Determinacy with a predetermined variable: Propositions 4.4, 4.6 and 4.7

Woodford (2003), *Interest and Prices*, Chapter 4, §2.2, pp. 255–261, and Appendix C.3, C.5,
C.6, pp. 677–683. Each rule gives a system with one predetermined variable. The models are
stated in their primitive form — NKPC (1.13), IS relation (1.12), policy rule — for an arbitrary
`ExpectationSystem`, shown equivalent to `E_t y_{t+1} = A y_t + a e_t` (`equil44_iff`,
`equil46_iff`, `equil47_iff`), and analysed with `BlanchardKahn` and Prop. C.2 (`SchurCohn`).
"Determinate" means: for every bounded adapted disturbance `e_t = r̂ⁿ_t − ī_t + π̄` and every
initial value of the predetermined variable there is exactly one bounded adapted equilibrium.

## Proposition 4.4 (inertial Taylor rule (2.8))

* Coefficients (App. C.3, verified): `ch2_A44`, `ch1_A44`, `ch0_A44`; `P1_A44`
  (`P(1) = (σκ/β)[φ_π + (1 − β)φ_x/(4κ) − (1 − ρ)]`, so (C.22) is (2.9)), `Pm1_A44_neg`
  ((C.14) automatic), `C15_A44` ((C.15) is (C.23)), `C24_iff` ((C.24) is `A₂ < −3`).
* The corner/monotonicity argument (pp. 679–680, Fig. C.1) as an exact decomposition
  `lhs23_decomp`, whence `lhs23_pos_of_not_C24` ((C.22) and not (C.24) imply (C.23); corner
  value `(β − ρ)²/(βκσ)`), and `oneInTwoOut_A44`.
* **Correction**: `prop44` — determinate iff (2.9) **and** `φ_π > 0 ∨ φ_x > 0`. As printed the
  proposition is false: with `φ_π = φ_x = 0` and `ρ > 1`, (2.9) holds but the interest rate is
  exogenous and equilibrium is not determinate (`prop44_printed_false`; the stable eigenvector of
  Prop. 4.2's matrix has no interest-rate component, `not_generic_A44_zero`).
  `prop44_of_response`: the printed equivalence under that extra hypothesis.
* At equality in (2.9) there is a unit eigenvalue (`fn27_unit_eigenvector`, with eigenvector
  `(1, (1 − β)/κ, 1)` in the units of (1.14); `left_unit_A44`), and resonance rules out a
  bounded equilibrium for a constant disturbance — the boundary case is settled, not omitted.
* Long run (p. 256): `longrun_form` (`Φ_π + (1 − β)Φ_x/(4κ) > 1` for `ρ < 1`),
  `taylor_automatic` and `determinate44_superinertial` (`ρ ≥ 1` with some response).

## Proposition 4.6 (forward-looking inertial rule (2.12)) — necessity only

`prop46_necessity`: determinacy implies (2.9) and (2.13), with `P1_A46`, `Pm1_A46` and
`caseI_impossible_46` (the book's "(A.1) and (A.2) imply `φ_x < 0`"; its labels "(A.1)–(A.7)"
are stale, survey E27). Boundary cases `P(±1) = 0` are handled by resonance (`left_unit_A46`,
`left_negunit_A46`). Sufficiency is not claimed (deferred; the book omits it too).

## Proposition 4.7 (price-level rule (2.14))

`prop47` (and `prop47_general` for forcing in every equation): determinate for every
`φ_p > 0`, `φ_x ≥ 0`. The book cites Giannoni (2000); here the proof is complete:
`P(1) = σκφ_p/β > 0` (`P1_A47`), `P(−1) < 0` (`Pm1_A47`), `A₂ < −3` (`ch2_A47`), so Case III′
of Prop. C.2 (`oneInTwoOut_A47`), plus genericity (`generic_A47`). The printed matrix, in the
book's state order, has the same characteristic polynomial (`A47book_ch`). The NKPC is in first
differences (printed with Δ on p. 683; `level_nkpc_differs` shows the level form is a different
restriction).
-/

namespace Woodford.NeoWicksellianFramework.ThreeByThree

open SchurCohn BlanchardKahn
open scoped Matrix

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), (C.19), p. 677: the disturbance direction `a = (0, −σ, 0)` of the IS relation
(the disturbance is `e_t = r̂ⁿ_t − ī_t + π̄`). -/
def aIS (σ : ℝ) : Fin 3 → ℝ := ![0, -σ, 0]

/-! ### Proposition 4.4: the inertial Taylor rule (2.8) -/

/-- Woodford (2003), (1.12), (1.13), (2.8), pp. 246, 255 (App. C.3, (C.21)): equilibrium of the
basic model under the inertial rule, in deviations from the target steady state:
`y_t = (π_t − π̄, x_t − x̄, ı̂_{t−1} − ī_{t−1})`, so `ı̂_t − ī_t` is `y_{t+1,2}`. The NKPC (1.13),
the IS relation (1.12) with disturbance `e_t = r̂ⁿ_t − ī_t + π̄`, and the rule (2.8) hold at every
date; `ı̂_{−1} − ī_{−1} = i₀` is given; the solution is adapted and bounded. -/
def Equil44 (β κ σ ρ φπ φx : ℝ) (e : ℕ → Ω → ℝ) (i0 : ℝ) (y : ℕ → Fin 3 → Ω → ℝ) : Prop :=
  (∀ t, y t 0 = κ • y t 1 + β • 𝔼.E t (y (t + 1) 0)) ∧
  (∀ t, y t 1 = 𝔼.E t (y (t + 1) 1) - σ • (y (t + 1) 2 - 𝔼.E t (y (t + 1) 0)) + σ • e t) ∧
  (∀ t, y (t + 1) 2 = ρ • y t 2 + φπ • y t 0 + (φx / 4) • y t 1) ∧
  y 0 2 = (fun _ => i0) ∧ VAdapted 𝔼 y ∧ VBounded y

/-- Woodford (2003), Prop. 4.4, p. 255: equilibrium under the rule (2.8) is determinate — for
every bounded adapted disturbance and every initial interest rate there is exactly one bounded
equilibrium. -/
def Determinate44 (β κ σ ρ φπ φx : ℝ) : Prop :=
  ∀ e : ℕ → Ω → ℝ, BoundedProc e → 𝔼.Adapted e → ∀ i0 : ℝ,
    ∃! y, Equil44 𝔼 β κ σ ρ φπ φx e i0 y

/-- Woodford (2003), (C.21), p. 678: the matrix `A` of the inertial-rule system. -/
noncomputable def A44 (β κ σ ρ φπ φx : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![β⁻¹, -(β⁻¹ * κ), 0; σ * (φπ - β⁻¹), 1 + σ * (φx / 4 + β⁻¹ * κ), σ * ρ; φπ, φx / 4, ρ]

/-- Woodford (2003), (C.21), p. 678: `A v` written out. -/
theorem mulVec_A44 (β κ σ ρ φπ φx : ℝ) (v : Fin 3 → ℝ) :
    A44 β κ σ ρ φπ φx *ᵥ v = ![β⁻¹ * v 0 - β⁻¹ * κ * v 1,
      σ * (φπ - β⁻¹) * v 0 + (1 + σ * (φx / 4 + β⁻¹ * κ)) * v 1 + σ * ρ * v 2,
      φπ * v 0 + φx / 4 * v 1 + ρ * v 2] := by
  funext i
  fin_cases i <;> simp [A44, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- Woodford (2003), (C.21), p. 678: `q A` written out. -/
theorem vecMul_A44 (β κ σ ρ φπ φx : ℝ) (q : Fin 3 → ℝ) :
    q ᵥ* A44 β κ σ ρ φπ φx = ![β⁻¹ * q 0 + σ * (φπ - β⁻¹) * q 1 + φπ * q 2,
      -(β⁻¹ * κ) * q 0 + (1 + σ * (φx / 4 + β⁻¹ * κ)) * q 1 + φx / 4 * q 2,
      σ * ρ * q 1 + ρ * q 2] := by
  funext i
  fin_cases i <;> simp [A44, Matrix.vecMul, dotProduct, Fin.sum_univ_three] <;> ring

/-- Woodford (2003), (C.21), p. 678: the model (1.12), (1.13), (2.8) is exactly the system
`E_t y_{t+1} = A y_t + a e_t` with one predetermined variable. -/
theorem equil44_iff {β κ σ ρ φπ φx : ℝ} (hβ : β ≠ 0) (e : ℕ → Ω → ℝ) (i0 : ℝ)
    (y : ℕ → Fin 3 → Ω → ℝ) :
    Equil44 𝔼 β κ σ ρ φπ φx e i0 y ↔
      Equil3 𝔼 (A44 β κ σ ρ φπ φx) (fun t i => aIS σ i • e t) i0 y := by
  have hb : β⁻¹ * β = 1 := inv_mul_cancel₀ hβ
  constructor
  · rintro ⟨hN, hI, hR, h0, ha, hbd⟩
    have hp : ∀ t, 𝔼.E t (y (t + 1) 2) = y (t + 1) 2 := by
      intro t
      rw [hR t, map_add, map_add, map_smul, map_smul, map_smul, ha t 0, ha t 1, ha t 2]
    refine ⟨fun t i => ?_, ha, hp, h0, hbd⟩
    funext ω
    have n := congrFun (hN t) ω
    have s := congrFun (hI t) ω
    have r := congrFun (hR t) ω
    have p := congrFun (hp t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at n s r p
    fin_cases i <;> simp [rvMul_apply, Fin.sum_univ_three, A44, aIS]
    · linear_combination (-β⁻¹) * n - (𝔼.E t (y (t + 1) 0) ω) * hb
    · linear_combination (-1 : ℝ) * s + σ * r + σ * β⁻¹ * n + σ * (𝔼.E t (y (t + 1) 0) ω) * hb
    · linear_combination p + r
  · rintro ⟨hs, ha, hp, h0, hbd⟩
    have row : ∀ t (i : Fin 3) ω, 𝔼.E t (y (t + 1) i) ω =
        (rvMul (A44 β κ σ ρ φπ φx) (y t) i + aIS σ i • e t) ω := fun t i ω => congrFun (hs t i) ω
    have r0 : ∀ t ω, 𝔼.E t (y (t + 1) 0) ω = β⁻¹ * y t 0 ω - β⁻¹ * κ * y t 1 ω := by
      intro t ω
      rw [row]
      simp [rvMul_apply, Fin.sum_univ_three, A44, aIS]
      ring
    have r1 : ∀ t ω, 𝔼.E t (y (t + 1) 1) ω = σ * (φπ - β⁻¹) * y t 0 ω +
        (1 + σ * (φx / 4 + β⁻¹ * κ)) * y t 1 ω + σ * ρ * y t 2 ω - σ * e t ω := by
      intro t ω
      rw [row]
      simp [rvMul_apply, Fin.sum_univ_three, A44, aIS]
      ring
    have r2 : ∀ t ω, y (t + 1) 2 ω = φπ * y t 0 ω + φx / 4 * y t 1 ω + ρ * y t 2 ω := by
      intro t ω
      rw [← hp t, row]
      simp [rvMul_apply, Fin.sum_univ_three, A44, aIS]
    refine ⟨fun t => ?_, fun t => ?_, fun t => ?_, h0, ha, hbd⟩ <;> funext ω <;>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    · rw [r0]; linear_combination (-(y t 0 ω - κ * y t 1 ω)) * hb
    · rw [r1, r0, r2]; ring
    · rw [r2]; ring

/-- Woodford (2003), Prop. 4.4, p. 255: determinacy of the model is determinacy of the system
`E_t y_{t+1} = A y_t + a e_t` in the sense of `BlanchardKahn.DeterminateFor`. -/
theorem determinate44_iff_for {β κ σ ρ φπ φx : ℝ} (hβ : β ≠ 0) :
    Determinate44 𝔼 β κ σ ρ φπ φx ↔ DeterminateFor 𝔼 (A44 β κ σ ρ φπ φx) (aIS σ) := by
  unfold Determinate44 DeterminateFor
  simp only [equil44_iff 𝔼 hβ]

/-- Woodford (2003), p. 678 (App. C.3): `A₂ = −β⁻¹(1 + κσ) − 1 − ρ − σφ_x/4`. -/
theorem ch2_A44 (β κ σ ρ φπ φx : ℝ) :
    ch2 (A44 β κ σ ρ φπ φx) = -(β⁻¹ * (1 + κ * σ)) - 1 - ρ - σ * φx / 4 := by
  simp [ch2, A44]; ring

/-- Woodford (2003), p. 678 (App. C.3): `A₁ = ρ + β⁻¹(1 + ρ(1 + κσ)) + β⁻¹σ(κφ_π + φ_x/4)`. -/
theorem ch1_A44 (β κ σ ρ φπ φx : ℝ) :
    ch1 (A44 β κ σ ρ φπ φx) =
      ρ + β⁻¹ * (1 + ρ * (1 + κ * σ)) + β⁻¹ * σ * (κ * φπ + φx / 4) := by
  simp [ch1, A44]; ring

/-- Woodford (2003), p. 678 (App. C.3): `A₀ = −β⁻¹ρ`. -/
theorem ch0_A44 (β κ σ ρ φπ φx : ℝ) : ch0 (A44 β κ σ ρ φπ φx) = -(β⁻¹ * ρ) := by
  simp [ch0, A44]; ring

/-- Woodford (2003), (C.22), p. 678: `P(1) = (σκ/β)[φ_π + (1 − β)φ_x/(4κ) − (1 − ρ)]`, so (C.13)
is the Taylor principle (2.9). -/
theorem P1_A44 {β κ σ ρ φπ φx : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0) :
    P1 (ch2 (A44 β κ σ ρ φπ φx)) (ch1 (A44 β κ σ ρ φπ φx)) (ch0 (A44 β κ σ ρ φπ φx)) =
      σ * κ / β * (φπ + (1 - β) / (4 * κ) * φx - (1 - ρ)) := by
  rw [P1, ch2_A44, ch1_A44, ch0_A44]
  field_simp
  ring

/-- Woodford (2003), p. 678 (App. C.3): `P(−1) = −[2 + 2ρ + β⁻¹(2 + κσ + 2ρ + ρκσ) + β⁻¹σκφ_π +
(1 + β⁻¹)σφ_x/4]`. -/
theorem Pm1_A44 (β κ σ ρ φπ φx : ℝ) :
    Pm1 (ch2 (A44 β κ σ ρ φπ φx)) (ch1 (A44 β κ σ ρ φπ φx)) (ch0 (A44 β κ σ ρ φπ φx)) =
      -(2 + 2 * ρ + β⁻¹ * (2 + κ * σ + 2 * ρ + ρ * κ * σ) + β⁻¹ * σ * κ * φπ
        + (1 + β⁻¹) * σ * φx / 4) := by
  rw [Pm1, ch2_A44, ch1_A44, ch0_A44]
  ring

/-- Woodford (2003), p. 678 (App. C.3): under the sign restrictions (C.14) `P(−1) < 0` always
holds, so (C.12) is violated and Case I is excluded. -/
theorem Pm1_A44_neg {β κ σ ρ φπ φx : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 ≤ ρ)
    (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    Pm1 (ch2 (A44 β κ σ ρ φπ φx)) (ch1 (A44 β κ σ ρ φπ φx)) (ch0 (A44 β κ σ ρ φπ φx)) < 0 := by
  rw [Pm1_A44]
  have hb : 0 < β⁻¹ := inv_pos.mpr hβ
  have : 0 ≤ β⁻¹ * σ * κ * φπ := by positivity
  have : 0 ≤ (1 + β⁻¹) * σ * φx / 4 := by positivity
  have : 0 < β⁻¹ * (2 + κ * σ + 2 * ρ + ρ * κ * σ) := by positivity
  linarith

/-- Woodford (2003), (C.23), p. 678: the left-hand side
`φ_π + (1 − ρ)φ_x/(4κ) + (β⁻¹ − 1)[(κσ)⁻¹(1 − ρ)(β − ρ) − ρ]` (the bracket that pdftotext drops,
restored from the page image). -/
noncomputable def lhs23 (β κ σ ρ φπ φx : ℝ) : ℝ :=
  φπ + (1 - ρ) / (4 * κ) * φx + (β⁻¹ - 1) * ((1 - ρ) * (β - ρ) / (κ * σ) - ρ)

/-- Woodford (2003), (C.15) and (C.23), p. 678: `A₀² − A₀A₂ + A₁ − 1 = (σκ/β) · LHS(C.23)`, so
(C.15) is (C.23). -/
theorem C15_A44 {β κ σ ρ φπ φx : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0) (hσ : σ ≠ 0) :
    C15 (ch2 (A44 β κ σ ρ φπ φx)) (ch1 (A44 β κ σ ρ φπ φx)) (ch0 (A44 β κ σ ρ φπ φx)) =
      σ * κ / β * lhs23 β κ σ ρ φπ φx := by
  rw [C15, ch2_A44, ch1_A44, ch0_A44, lhs23]
  field_simp
  ring

/-- Woodford (2003), (C.24), p. 679: `β⁻¹(1 + κσ) + ρ + σφ_x/4 > 2`. -/
def C24 (β κ σ ρ φx : ℝ) : Prop := 2 < β⁻¹ * (1 + κ * σ) + ρ + σ * φx / 4

/-- Woodford (2003), (C.24) and fn. 4, p. 679: (C.24) is exactly `A₂ < −3`, the relevant half of
(C.17). -/
theorem C24_iff (β κ σ ρ φπ φx : ℝ) : C24 β κ σ ρ φx ↔ ch2 (A44 β κ σ ρ φπ φx) < -3 := by
  rw [C24, ch2_A44]
  constructor <;> intro h <;> linarith

/-- Woodford (2003), p. 679: `β + β⁻¹ > 2` for `0 < β < 1`. -/
theorem add_inv_gt_two {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : 2 < β + β⁻¹ := by
  have h : β⁻¹ * β = 1 := inv_mul_cancel₀ hβ0.ne'
  have hb : 1 < β⁻¹ := one_lt_inv₀ hβ0 |>.mpr hβ1
  nlinarith

/-- Woodford (2003), p. 679: "(C.24) can fail to hold only if `ρ < β`". -/
theorem rho_lt_beta_of_not_C24 {β κ σ ρ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hφx : 0 ≤ φx) (h : ¬ C24 β κ σ ρ φx) : ρ < β := by
  unfold C24 at h
  push Not at h
  have := add_inv_gt_two hβ0 hβ1
  have hb : 0 < β⁻¹ := inv_pos.mpr hβ0
  have : 0 ≤ β⁻¹ * (κ * σ) := by positivity
  have : 0 ≤ σ * φx / 4 := by positivity
  nlinarith

/-- **The corner argument** (Woodford (2003), App. C.3, pp. 679–680, Fig. C.1), formalised: with
`ρ_m = 2 − β⁻¹(1 + κσ) − σφ_x/4` the largest `ρ` at which (C.24) is (weakly) violated and
`F = φ_x/(4κ)`,
`LHS(C.23) = [φ_π + (1 − β)F − (1 − ρ)] + (ρ_m − ρ) K + (β − ρ_m)²/(βκσ)`
with `K = β⁻¹ + F + (β⁻¹ − 1)(1 + β − ρ − ρ_m)/(κσ)`: the first term is the slack in (C.22), the
second the monotonicity of LHS(C.23) in `ρ` (and in `φ_π`), the third the corner value. -/
theorem lhs23_decomp {β κ σ ρ φπ φx : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0) (hσ : σ ≠ 0) :
    lhs23 β κ σ ρ φπ φx =
      (φπ + (1 - β) / (4 * κ) * φx - (1 - ρ)) +
      ((2 - β⁻¹ * (1 + κ * σ) - σ * φx / 4) - ρ) *
        (β⁻¹ + φx / (4 * κ) + (β⁻¹ - 1) * (1 + β - ρ - (2 - β⁻¹ * (1 + κ * σ) - σ * φx / 4))
          / (κ * σ)) +
      (β - (2 - β⁻¹ * (1 + κ * σ) - σ * φx / 4)) ^ 2 / (β * (κ * σ)) := by
  rw [lhs23]
  field_simp
  ring

/-- Woodford (2003), App. C.3, p. 680: (C.22) and the failure of (C.24) imply (C.23) — the values
of Fig. C.1 where (C.22) holds and (C.24) fails lie inside the region where (C.23) holds. -/
theorem lhs23_pos_of_not_C24 {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hφx : 0 ≤ φx)
    (h22 : 1 - ρ < φπ + (1 - β) / (4 * κ) * φx) (h24 : ¬ C24 β κ σ ρ φx) :
    0 < lhs23 β κ σ ρ φπ φx := by
  have hρβ := rho_lt_beta_of_not_C24 hβ0 hβ1 hκ hσ hφx h24
  unfold C24 at h24
  push Not at h24
  set ρm := 2 - β⁻¹ * (1 + κ * σ) - σ * φx / 4 with hρm
  have hm1 : ρ ≤ ρm := by rw [hρm]; linarith
  have hm2 : ρm < β := by
    have := add_inv_gt_two hβ0 hβ1
    have hb : 0 < β⁻¹ := inv_pos.mpr hβ0
    have : 0 ≤ β⁻¹ * (κ * σ) := by positivity
    have : 0 ≤ σ * φx / 4 := by positivity
    rw [hρm]; nlinarith
  rw [lhs23_decomp hβ0.ne' hκ.ne' hσ.ne', ← hρm]
  have hb1 : 1 < β⁻¹ := one_lt_inv₀ hβ0 |>.mpr hβ1
  have hu : 0 < κ * σ := mul_pos hκ hσ
  have t1 : 0 < φπ + (1 - β) / (4 * κ) * φx - (1 - ρ) := by linarith
  have hK : 0 ≤ β⁻¹ + φx / (4 * κ) + (β⁻¹ - 1) * (1 + β - ρ - ρm) / (κ * σ) := by
    have : 0 ≤ (β⁻¹ - 1) * (1 + β - ρ - ρm) := mul_nonneg (by linarith) (by linarith)
    have : 0 ≤ φx / (4 * κ) := by positivity
    have : 0 ≤ (β⁻¹ - 1) * (1 + β - ρ - ρm) / (κ * σ) := by positivity
    linarith
  have t2 : 0 ≤ (ρm - ρ) * (β⁻¹ + φx / (4 * κ) + (β⁻¹ - 1) * (1 + β - ρ - ρm) / (κ * σ)) :=
    mul_nonneg (by linarith) hK
  have t3 : 0 ≤ (β - ρm) ^ 2 / (β * (κ * σ)) := by positivity
  linarith

/-- Woodford (2003), App. C.3, p. 679: under the sign restrictions and the Taylor principle (2.9),
Case II or Case III′ of Prop. C.2 holds, so `A` has one eigenvalue inside and two outside the
unit circle. -/
theorem oneInTwoOut_A44 {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (h29 : 1 - ρ < φπ + (1 - β) / (4 * κ) * φx) :
    OneInTwoOut (ch2 (A44 β κ σ ρ φπ φx)) (ch1 (A44 β κ σ ρ φπ φx)) (ch0 (A44 β κ σ ρ φπ φx)) := by
  have hP1 : 0 < P1 (ch2 (A44 β κ σ ρ φπ φx)) (ch1 (A44 β κ σ ρ φπ φx))
      (ch0 (A44 β κ σ ρ φπ φx)) := by
    rw [P1_A44 hβ0.ne' hκ.ne']
    have : 0 < σ * κ / β := by positivity
    exact mul_pos this (by linarith)
  have hPm1 := Pm1_A44_neg hβ0 hκ hσ hρ hφπ hφx
  apply oneInTwoOut_of_cases
  by_cases h24 : C24 β κ σ ρ φx
  · right; right
    refine ⟨hP1, hPm1, ?_⟩
    have := (C24_iff β κ σ ρ φπ φx).mp h24
    rw [abs_of_neg (by linarith)]
    linarith
  · right; left
    refine ⟨hP1, hPm1, ?_⟩
    rw [C15_A44 hβ0.ne' hκ.ne' hσ.ne']
    exact mul_pos (by positivity) (lhs23_pos_of_not_C24 hβ0 hβ1 hκ hσ hφx h29 h24)

/-- Woodford (2003), Prop. 4.4 (the genericity the book leaves implicit): if the rule responds to
inflation or the output gap (`φ_π > 0` or `φ_x > 0`), no eigenvector of an eigenvalue in the unit
disc has a zero lagged-interest-rate component. -/
theorem generic_A44 {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (hφ : 0 < φπ ∨ 0 < φx) : Generic (A44 β κ σ ρ φπ φx) := by
  intro μ v hμ hv h2
  rw [mulVec_A44] at hv
  have r0 : β⁻¹ * v 0 - β⁻¹ * κ * v 1 = μ * v 0 := congrFun hv 0
  have r2 : φπ * v 0 + φx / 4 * v 1 + ρ * v 2 = μ * v 2 := congrFun hv 2
  rw [h2] at r2
  have hb1 : 1 < β⁻¹ := one_lt_inv₀ hβ0 |>.mpr hβ1
  have hμ1 : μ < 1 := (abs_lt.mp hμ).2
  have hcoef : 0 < 4 * β⁻¹ * κ * φπ + φx * (β⁻¹ - μ) := by
    rcases hφ with h | h
    · have : 0 ≤ φx * (β⁻¹ - μ) := mul_nonneg hφx (by linarith)
      have : 0 < 4 * β⁻¹ * κ * φπ := by positivity
      linarith
    · have : 0 < φx * (β⁻¹ - μ) := mul_pos h (by linarith)
      have : 0 ≤ 4 * β⁻¹ * κ * φπ := by positivity
      linarith
  have hv0 : v 0 = 0 := by
    have e : v 0 * (4 * β⁻¹ * κ * φπ + φx * (β⁻¹ - μ)) = 0 := by
      linear_combination (4 * β⁻¹ * κ) * r2 + φx * r0
    rcases mul_eq_zero.mp e with e | e
    · exact e
    · linarith
  have hv1 : v 1 = 0 := by
    rw [hv0] at r0
    have hbk : β⁻¹ * κ ≠ 0 := by positivity
    have : β⁻¹ * κ * v 1 = 0 := by linarith
    rcases mul_eq_zero.mp this with e | e
    · exact absurd e hbk
    · exact e
  funext i
  fin_cases i
  · exact hv0
  · exact hv1
  · exact h2

/-- Woodford (2003), p. 252 (the exogenous-rate matrix of Prop. 4.2): with `φ_π = φ_x = 0` the
polynomial `μ² − [1 + β⁻¹(1 + κσ)]μ + β⁻¹` has a root `μ₁ ∈ (0, 1)`. -/
theorem exists_stable_root_exog {β κ σ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hσ : 0 < σ) :
    ∃ m : ℝ, 0 < m ∧ m < 1 ∧ m ^ 2 - (1 + β⁻¹ * (1 + κ * σ)) * m + β⁻¹ = 0 := by
  set f : ℝ → ℝ := fun m => m ^ 2 - (1 + β⁻¹ * (1 + κ * σ)) * m + β⁻¹ with hf
  have hb : 0 < β⁻¹ := inv_pos.mpr hβ0
  have f0 : 0 < f 0 := by simp [hf, hb]
  have f1 : f 1 < 0 := by
    simp only [hf]; have : 0 < β⁻¹ * (κ * σ) := by positivity
    nlinarith
  have hcont : ContinuousOn f (Set.Icc 0 1) := by rw [hf]; fun_prop
  obtain ⟨m, hm, hfm⟩ := intermediate_value_Icc' (by norm_num) hcont ⟨f1.le, f0.le⟩
  refine ⟨m, lt_of_le_of_ne hm.1 ?_, lt_of_le_of_ne hm.2 ?_, hfm⟩
  · rintro rfl; linarith
  · rintro rfl; linarith

/-- Woodford (2003), Prop. 4.2, p. 253, inside Prop. 4.4: with `φ_π = φ_x = 0` the stable root
`μ₁` of the exogenous-rate system is an eigenvalue of `A` whose eigenvector `(β⁻¹κ, β⁻¹ − μ₁, 0)`
has a zero lagged-interest-rate component — the genericity condition fails, whatever `ρ`. -/
theorem not_generic_A44_zero {β κ σ ρ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hσ : 0 < σ) :
    ¬ Generic (A44 β κ σ ρ 0 0) := by
  obtain ⟨m, hm0, hm1, hm⟩ := exists_stable_root_exog hβ0 hκ hσ
  intro hg
  have hv := hg m ![β⁻¹ * κ, β⁻¹ - m, 0] (by rw [abs_of_pos hm0]; exact hm1) ?_ (by simp)
  · have h0 : β⁻¹ * κ = 0 := congrFun hv 0
    exact absurd h0 (by positivity)
  · rw [mulVec_A44]
    have e0 : β⁻¹ * (β⁻¹ * κ) - β⁻¹ * κ * (β⁻¹ - m) = m * (β⁻¹ * κ) := by ring
    have e1 : σ * (0 - β⁻¹) * (β⁻¹ * κ) + (1 + σ * (0 / 4 + β⁻¹ * κ)) * (β⁻¹ - m) +
        σ * ρ * 0 = m * (β⁻¹ - m) := by linear_combination hm
    have e2 : (0 : ℝ) * (β⁻¹ * κ) + 0 / 4 * (β⁻¹ - m) + ρ * 0 = m * 0 := by ring
    funext i
    fin_cases i
    · exact e0
    · exact e1
    · exact e2

/-- Woodford (2003), Prop. 4.4, p. 256, fn. 27: at equality in (2.9), `q A = q` for
`q = (σ(β⁻¹ − ρβ⁻¹ − φ_π), (1 − ρ)(β⁻¹ − 1), σρ(β⁻¹ − 1))` — a left eigenvector of the unit
eigenvalue. -/
theorem left_unit_A44 {β κ σ ρ φπ φx : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0)
    (heq : φπ + (1 - β) / (4 * κ) * φx = 1 - ρ) :
    ![σ * (β⁻¹ - ρ * β⁻¹ - φπ), (1 - ρ) * (β⁻¹ - 1), σ * ρ * (β⁻¹ - 1)] ᵥ* A44 β κ σ ρ φπ φx =
      (1 : ℝ) • ![σ * (β⁻¹ - ρ * β⁻¹ - φπ), (1 - ρ) * (β⁻¹ - 1), σ * ρ * (β⁻¹ - 1)] := by
  have hφ : φπ = 1 - ρ - (1 - β) / (4 * κ) * φx := by linarith
  rw [vecMul_A44, one_smul]
  have e0 : β⁻¹ * (σ * (β⁻¹ - ρ * β⁻¹ - φπ)) + σ * (φπ - β⁻¹) * ((1 - ρ) * (β⁻¹ - 1)) +
      φπ * (σ * ρ * (β⁻¹ - 1)) = σ * (β⁻¹ - ρ * β⁻¹ - φπ) := by ring
  have e1 : -(β⁻¹ * κ) * (σ * (β⁻¹ - ρ * β⁻¹ - φπ)) +
      (1 + σ * (φx / 4 + β⁻¹ * κ)) * ((1 - ρ) * (β⁻¹ - 1)) + φx / 4 * (σ * ρ * (β⁻¹ - 1)) =
      (1 - ρ) * (β⁻¹ - 1) := by
    rw [hφ]; field_simp; ring
  have e2 : σ * ρ * ((1 - ρ) * (β⁻¹ - 1)) + ρ * (σ * ρ * (β⁻¹ - 1)) = σ * ρ * (β⁻¹ - 1) := by
    ring
  funext j
  fin_cases j
  · exact e0
  · exact e1
  · exact e2

/-- Woodford (2003), Prop. 4.4, p. 256, fn. 27 (in the units of (1.14)): at equality in (2.9),
`(1, (1 − β)/κ, 1)` is an eigenvector of the unit eigenvalue. -/
theorem fn27_unit_eigenvector {β κ σ ρ φπ φx : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0)
    (heq : φπ + (1 - β) / (4 * κ) * φx = 1 - ρ) :
    A44 β κ σ ρ φπ φx *ᵥ ![1, (1 - β) / κ, 1] = ![1, (1 - β) / κ, 1] := by
  have hφ : φπ = 1 - ρ - (1 - β) / (4 * κ) * φx := by linarith
  rw [mulVec_A44]
  have e0 : β⁻¹ * 1 - β⁻¹ * κ * ((1 - β) / κ) = 1 := by field_simp; ring
  have e1 : σ * (φπ - β⁻¹) * 1 + (1 + σ * (φx / 4 + β⁻¹ * κ)) * ((1 - β) / κ) + σ * ρ * 1 =
      (1 - β) / κ := by rw [hφ]; field_simp; ring
  have e2 : φπ * 1 + φx / 4 * ((1 - β) / κ) + ρ * 1 = 1 := by rw [hφ]; field_simp; ring
  funext i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2

/-- **Proposition 4.4, corrected** (Woodford (2003), p. 255; proof App. C.3, pp. 677–680): for
`0 < β < 1`, `κ, σ > 0` and `ρ, φ_π, φ_x ≥ 0`, equilibrium under the inertial rule (2.8) is
determinate if and only if (2.9) `φ_π + (1 − β)φ_x/(4κ) > 1 − ρ` holds **and** the rule responds
to inflation or the output gap. (Without the second condition the statement is false:
`prop44_printed_false`.) -/
theorem prop44 [Nonempty Ω] {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    Determinate44 𝔼 β κ σ ρ φπ φx ↔
      1 - ρ < φπ + (1 - β) / (4 * κ) * φx ∧ (0 < φπ ∨ 0 < φx) := by
  rw [determinate44_iff_for 𝔼 hβ0.ne']
  constructor
  · intro hd
    have hφ : 0 < φπ ∨ 0 < φx := by
      by_contra h
      push Not at h
      have e1 : φπ = 0 := le_antisymm h.1 hφπ
      have e2 : φx = 0 := le_antisymm h.2 hφx
      subst e1 e2
      exact not_generic_A44_zero hβ0 hκ hσ (generic_of_determinateFor 𝔼 hd)
    refine ⟨?_, hφ⟩
    by_contra h29
    push Not at h29
    rcases eq_or_lt_of_le h29 with heq | hlt
    · -- equality: the unit eigenvalue and resonance
      have hρ1 : ρ ≠ 1 := by
        rintro rfl
        have : φπ + (1 - β) / (4 * κ) * φx = 0 := by linarith
        have h1 : 0 ≤ (1 - β) / (4 * κ) * φx := by
          have : 0 < 1 - β := by linarith
          positivity
        rcases hφ with h | h
        · linarith
        · have : 0 < (1 - β) / (4 * κ) * φx := by
            have : 0 < 1 - β := by linarith
            positivity
          linarith
      refine not_determinateFor_of_unit_left 𝔼 (left_unit_A44 hβ0.ne' hκ.ne' heq) (one_pow 2)
        ?_ hd
      rw [Fin.sum_univ_three]
      change σ * (β⁻¹ - ρ * β⁻¹ - φπ) * 0 + (1 - ρ) * (β⁻¹ - 1) * (-σ) +
        σ * ρ * (β⁻¹ - 1) * 0 ≠ 0
      have hb1 : 1 < β⁻¹ := one_lt_inv₀ hβ0 |>.mpr hβ1
      have : (1 - ρ) * (β⁻¹ - 1) * σ ≠ 0 :=
        mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hρ1)) (by linarith)) hσ.ne'
      intro h0; apply this; linarith
    · -- strict violation: no unit root, and the eigenvalue count fails
      have hP1 : P1 (ch2 (A44 β κ σ ρ φπ φx)) (ch1 (A44 β κ σ ρ φπ φx))
          (ch0 (A44 β κ σ ρ φπ φx)) < 0 := by
        rw [P1_A44 hβ0.ne' hκ.ne']
        exact mul_neg_of_pos_of_neg (by positivity) (by linarith)
      have hPm1 := Pm1_A44_neg hβ0 hκ hσ hρ hφπ hφx
      have hoit := oneInTwoOut_of_determinateFor 𝔼 hd hP1.ne hPm1.ne
      rcases cases_of_oneInTwoOut hoit with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> linarith
  · rintro ⟨h29, hφ⟩
    exact determinateFor_of_determinate3 𝔼
      (determinate3_of 𝔼 (oneInTwoOut_A44 hβ0 hβ1 hκ hσ hρ hφπ hφx h29)
        (generic_A44 hβ0 hβ1 hκ hφπ hφx hφ)) _

/-- Woodford (2003), Prop. 4.4, p. 255, as printed under the extra hypothesis that the rule
responds to inflation or the output gap: determinate iff (2.9). -/
theorem prop44_of_response [Nonempty Ω] {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (hφ : 0 < φπ ∨ 0 < φx) :
    Determinate44 𝔼 β κ σ ρ φπ φx ↔ 1 - ρ < φπ + (1 - β) / (4 * κ) * φx := by
  rw [prop44 𝔼 hβ0 hβ1 hκ hσ hρ hφπ hφx]
  exact ⟨fun h => h.1, fun h => ⟨h, hφ⟩⟩

/-- Woodford (2003), Prop. 4.4, p. 255 (**the printed statement is false**): with
`φ_π = φ_x = 0` and `ρ > 1`, (2.9) holds (`0 > 1 − ρ`), but the rule `ı̂_t − ī_t = ρ(ı̂_{t−1} −
ī_{t−1})` makes the interest rate exogenous and equilibrium is not determinate (Prop. 4.2). -/
theorem prop44_printed_false [Nonempty Ω] {β κ σ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 1 < ρ) :
    1 - ρ < 0 + (1 - β) / (4 * κ) * 0 ∧ ¬ Determinate44 𝔼 β κ σ ρ 0 0 := by
  refine ⟨by simp; linarith, fun h => ?_⟩
  have := (prop44 𝔼 hβ0 hβ1 hκ hσ (by linarith) le_rfl le_rfl).mp h
  rcases this.2 with h | h <;> exact lt_irrefl _ h

/-- Woodford (2003), p. 256: for `ρ < 1`, (2.9) is the long-run Taylor principle
`Φ_π + (1 − β)Φ_x/(4κ) > 1` with `Φ = φ/(1 − ρ)`. -/
theorem longrun_form {β κ ρ φπ φx : ℝ} (hρ : ρ < 1) :
    1 - ρ < φπ + (1 - β) / (4 * κ) * φx ↔
      1 < φπ / (1 - ρ) + (1 - β) / (4 * κ) * (φx / (1 - ρ)) := by
  have h : 0 < 1 - ρ := by linarith
  rw [mul_div_assoc', ← add_div, lt_div_iff₀ h, one_mul]

/-- Woodford (2003), p. 256: for `ρ ≥ 1` (2.9) holds automatically when the rule responds to
inflation or the output gap. -/
theorem taylor_automatic {β κ ρ φπ φx : ℝ} (hβ1 : β < 1) (hκ : 0 < κ) (hρ : 1 ≤ ρ)
    (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (hφ : 0 < φπ ∨ 0 < φx) :
    1 - ρ < φπ + (1 - β) / (4 * κ) * φx := by
  have h1 : 0 < 1 - β := by linarith
  rcases hφ with h | h
  · have : 0 ≤ (1 - β) / (4 * κ) * φx := by positivity
    linarith
  · have : 0 < (1 - β) / (4 * κ) * φx := by positivity
    linarith

/-- Woodford (2003), p. 256 ("a determinate equilibrium necessarily exists for rules with
`ρ ≥ 1`"): superinertial rules responding to inflation or the output gap are determinate. -/
theorem determinate44_superinertial [Nonempty Ω] {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 1 ≤ ρ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (hφ : 0 < φπ ∨ 0 < φx) : Determinate44 𝔼 β κ σ ρ φπ φx :=
  (prop44 𝔼 hβ0 hβ1 hκ hσ (by linarith) hφπ hφx).mpr
    ⟨taylor_automatic hβ1 hκ hρ hφπ hφx hφ, hφ⟩

/-! ### Proposition 4.6: the inertial forward-looking rule (2.12) — necessity -/

/-- Woodford (2003), (1.12), (1.13), (2.12), pp. 246, 258: equilibrium under the inertial rule
responding to expected inflation, `ı̂_t − ī_t = ρ(ı̂_{t−1} − ī_{t−1}) + φ_π(E_t π_{t+1} − π̄) +
φ_x(x_t − x̄)/4`, with the state of (C.21). -/
def Equil46 (β κ σ ρ φπ φx : ℝ) (e : ℕ → Ω → ℝ) (i0 : ℝ) (y : ℕ → Fin 3 → Ω → ℝ) : Prop :=
  (∀ t, y t 0 = κ • y t 1 + β • 𝔼.E t (y (t + 1) 0)) ∧
  (∀ t, y t 1 = 𝔼.E t (y (t + 1) 1) - σ • (y (t + 1) 2 - 𝔼.E t (y (t + 1) 0)) + σ • e t) ∧
  (∀ t, y (t + 1) 2 = ρ • y t 2 + φπ • 𝔼.E t (y (t + 1) 0) + (φx / 4) • y t 1) ∧
  y 0 2 = (fun _ => i0) ∧ VAdapted 𝔼 y ∧ VBounded y

/-- Woodford (2003), Prop. 4.6, p. 258: determinacy under the rule (2.12). -/
def Determinate46 (β κ σ ρ φπ φx : ℝ) : Prop :=
  ∀ e : ℕ → Ω → ℝ, BoundedProc e → 𝔼.Adapted e → ∀ i0 : ℝ,
    ∃! y, Equil46 𝔼 β κ σ ρ φπ φx e i0 y

/-- Woodford (2003), App. C.5, p. 682: the matrix `A` of the forward-looking inertial system. -/
noncomputable def A46 (β κ σ ρ φπ φx : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![β⁻¹, -(β⁻¹ * κ), 0;
    σ * β⁻¹ * (φπ - 1), 1 + σ * (φx / 4 - β⁻¹ * κ * (φπ - 1)), σ * ρ;
    β⁻¹ * φπ, φx / 4 - β⁻¹ * κ * φπ, ρ]

/-- Woodford (2003), App. C.5, p. 682: `q A` written out. -/
theorem vecMul_A46 (β κ σ ρ φπ φx : ℝ) (q : Fin 3 → ℝ) :
    q ᵥ* A46 β κ σ ρ φπ φx = ![β⁻¹ * q 0 + σ * β⁻¹ * (φπ - 1) * q 1 + β⁻¹ * φπ * q 2,
      -(β⁻¹ * κ) * q 0 + (1 + σ * (φx / 4 - β⁻¹ * κ * (φπ - 1))) * q 1
        + (φx / 4 - β⁻¹ * κ * φπ) * q 2,
      σ * ρ * q 1 + ρ * q 2] := by
  funext i
  fin_cases i <;> simp [A46, Matrix.vecMul, dotProduct, Fin.sum_univ_three] <;> ring

/-- Woodford (2003), App. C.5, p. 682: the model (1.12), (1.13), (2.12) is the system
`E_t y_{t+1} = A y_t + a e_t` with one predetermined variable. -/
theorem equil46_iff {β κ σ ρ φπ φx : ℝ} (hβ : β ≠ 0) (e : ℕ → Ω → ℝ) (i0 : ℝ)
    (y : ℕ → Fin 3 → Ω → ℝ) :
    Equil46 𝔼 β κ σ ρ φπ φx e i0 y ↔
      Equil3 𝔼 (A46 β κ σ ρ φπ φx) (fun t i => aIS σ i • e t) i0 y := by
  have hb : β⁻¹ * β = 1 := inv_mul_cancel₀ hβ
  constructor
  · rintro ⟨hN, hI, hR, h0, ha, hbd⟩
    have hp : ∀ t, 𝔼.E t (y (t + 1) 2) = y (t + 1) 2 := by
      intro t
      rw [hR t, map_add, map_add, map_smul, map_smul, map_smul, ha t 1, ha t 2, 𝔼.E_E_self]
    refine ⟨fun t i => ?_, ha, hp, h0, hbd⟩
    funext ω
    have n := congrFun (hN t) ω
    have s := congrFun (hI t) ω
    have r := congrFun (hR t) ω
    have p := congrFun (hp t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at n s r p
    fin_cases i <;> simp [rvMul_apply, Fin.sum_univ_three, A46, aIS]
    · linear_combination (-β⁻¹) * n - (𝔼.E t (y (t + 1) 0) ω) * hb
    · linear_combination (-1 : ℝ) * s + σ * r - σ * (φπ - 1) * β⁻¹ * n
        - σ * (φπ - 1) * (𝔼.E t (y (t + 1) 0) ω) * hb
    · linear_combination p + r - φπ * β⁻¹ * n - φπ * (𝔼.E t (y (t + 1) 0) ω) * hb
  · rintro ⟨hs, ha, hp, h0, hbd⟩
    have row : ∀ t (i : Fin 3) ω, 𝔼.E t (y (t + 1) i) ω =
        (rvMul (A46 β κ σ ρ φπ φx) (y t) i + aIS σ i • e t) ω := fun t i ω => congrFun (hs t i) ω
    have r0 : ∀ t ω, 𝔼.E t (y (t + 1) 0) ω = β⁻¹ * y t 0 ω - β⁻¹ * κ * y t 1 ω := by
      intro t ω
      rw [row]
      simp [rvMul_apply, Fin.sum_univ_three, A46, aIS]
      ring
    have r1 : ∀ t ω, 𝔼.E t (y (t + 1) 1) ω = σ * β⁻¹ * (φπ - 1) * y t 0 ω +
        (1 + σ * (φx / 4 - β⁻¹ * κ * (φπ - 1))) * y t 1 ω + σ * ρ * y t 2 ω - σ * e t ω := by
      intro t ω
      rw [row]
      simp [rvMul_apply, Fin.sum_univ_three, A46, aIS]
      ring
    have r2 : ∀ t ω, y (t + 1) 2 ω =
        β⁻¹ * φπ * y t 0 ω + (φx / 4 - β⁻¹ * κ * φπ) * y t 1 ω + ρ * y t 2 ω := by
      intro t ω
      rw [← hp t, row]
      simp [rvMul_apply, Fin.sum_univ_three, A46, aIS]
    refine ⟨fun t => ?_, fun t => ?_, fun t => ?_, h0, ha, hbd⟩ <;> funext ω <;>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    · rw [r0]; linear_combination (-(y t 0 ω - κ * y t 1 ω)) * hb
    · rw [r1, r0, r2]; ring
    · rw [r2, r0]; ring

/-- Woodford (2003), Prop. 4.6, p. 258: determinacy of the model is determinacy of its system. -/
theorem determinate46_iff_for {β κ σ ρ φπ φx : ℝ} (hβ : β ≠ 0) :
    Determinate46 𝔼 β κ σ ρ φπ φx ↔ DeterminateFor 𝔼 (A46 β κ σ ρ φπ φx) (aIS σ) := by
  unfold Determinate46 DeterminateFor
  simp only [equil46_iff 𝔼 hβ]

/-- Woodford (2003), App. C.5, p. 682: `A₂ = −tr A` for the forward-looking inertial system. -/
theorem ch2_A46 (β κ σ ρ φπ φx : ℝ) :
    ch2 (A46 β κ σ ρ φπ φx) = -(β⁻¹ + 1 + σ * (φx / 4 - β⁻¹ * κ * (φπ - 1)) + ρ) := by
  simp [ch2, A46]; ring

/-- Woodford (2003), App. C.5, p. 682: `A₁` for the forward-looking inertial system. -/
theorem ch1_A46 (β κ σ ρ φπ φx : ℝ) :
    ch1 (A46 β κ σ ρ φπ φx) = β⁻¹ * (1 + σ * φx / 4) + β⁻¹ * ρ +
      (1 + σ * (φx / 4 - β⁻¹ * κ * (φπ - 1))) * ρ - σ * ρ * (φx / 4 - β⁻¹ * κ * φπ) := by
  simp [ch1, A46]; ring

/-- Woodford (2003), App. C.5, p. 682: `A₀ = −det A = −β⁻¹ρ` for the forward-looking inertial
system. -/
theorem ch0_A46 (β κ σ ρ φπ φx : ℝ) : ch0 (A46 β κ σ ρ φπ φx) = -(β⁻¹ * ρ) := by
  simp [ch0, A46]; ring

/-- Woodford (2003), App. C.5, p. 682: `P(1) = (σκ/β)[φ_π + (1 − β)φ_x/(4κ) − (1 − ρ)]`, so
(C.13) is (C.20) = (2.9) (the survey's verified formula; the book only asserts the
correspondence). -/
theorem P1_A46 {β κ σ ρ φπ φx : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0) :
    P1 (ch2 (A46 β κ σ ρ φπ φx)) (ch1 (A46 β κ σ ρ φπ φx)) (ch0 (A46 β κ σ ρ φπ φx)) =
      σ * κ / β * (φπ + (1 - β) / (4 * κ) * φx - (1 - ρ)) := by
  rw [P1, ch2_A46, ch1_A46, ch0_A46]
  field_simp
  ring

/-- Woodford (2003), App. C.5, p. 682:
`P(−1) = (σκ/β)[φ_π − (1 + ρ) − (1 + β)(φ_x + 8σ⁻¹(1 + ρ))/(4κ)]`, so (C.14) is (C.26) = (2.13). -/
theorem Pm1_A46 {β κ σ ρ φπ φx : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0) (hσ : σ ≠ 0) :
    Pm1 (ch2 (A46 β κ σ ρ φπ φx)) (ch1 (A46 β κ σ ρ φπ φx)) (ch0 (A46 β κ σ ρ φπ φx)) =
      σ * κ / β * (φπ - (1 + ρ) - (1 + β) / (4 * κ) * (φx + 8 / σ * (1 + ρ))) := by
  rw [Pm1, ch2_A46, ch1_A46, ch0_A46]
  field_simp
  ring

/-- Woodford (2003), App. C.5, p. 682: "(A.1) and (A.2) imply that `φ_x < 0`" — precisely, (C.11)
and (C.12) imply `φ_x/(2κ) < −2ρ − 2(1 + β)(1 + ρ)/(κσ)`, so Case I is impossible under the
sign restrictions. -/
theorem caseI_impossible_46 {β κ σ ρ φπ φx : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hσ : 0 < σ)
    (h11 : P1 (ch2 (A46 β κ σ ρ φπ φx)) (ch1 (A46 β κ σ ρ φπ φx)) (ch0 (A46 β κ σ ρ φπ φx)) < 0)
    (h12 : 0 < Pm1 (ch2 (A46 β κ σ ρ φπ φx)) (ch1 (A46 β κ σ ρ φπ φx))
      (ch0 (A46 β κ σ ρ φπ φx))) :
    φx / (2 * κ) < -2 * ρ - 2 * (1 + β) * (1 + ρ) / (κ * σ) := by
  rw [P1_A46 hβ.ne' hκ.ne'] at h11
  rw [Pm1_A46 hβ.ne' hκ.ne' hσ.ne'] at h12
  have hc : 0 < σ * κ / β := by positivity
  have hd : (φπ + (1 - β) / (4 * κ) * φx - (1 - ρ)) -
      (φπ - (1 + ρ) - (1 + β) / (4 * κ) * (φx + 8 / σ * (1 + ρ))) =
      2 * ρ + φx / (2 * κ) + 2 * (1 + β) * (1 + ρ) / (κ * σ) := by
    field_simp; ring
  have h1 : φπ + (1 - β) / (4 * κ) * φx - (1 - ρ) < 0 := by
    by_contra h; push Not at h; nlinarith
  have h2 : 0 < φπ - (1 + ρ) - (1 + β) / (4 * κ) * (φx + 8 / σ * (1 + ρ)) := by
    by_contra h; push Not at h; nlinarith
  linarith

/-- Woodford (2003), App. C.5, p. 682: at equality in (2.9) the vector
`q = (−σβ⁻¹(φ_π − 1 + ρ), (1 − ρ)(β⁻¹ − 1), σρ(β⁻¹ − 1))` is a left eigenvector of the unit
eigenvalue. -/
theorem left_unit_A46 {β κ σ ρ φπ φx : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0)
    (heq : φπ + (1 - β) / (4 * κ) * φx = 1 - ρ) :
    ![-(σ * β⁻¹ * (φπ - 1 + ρ)), (1 - ρ) * (β⁻¹ - 1), σ * ρ * (β⁻¹ - 1)] ᵥ* A46 β κ σ ρ φπ φx =
      (1 : ℝ) • ![-(σ * β⁻¹ * (φπ - 1 + ρ)), (1 - ρ) * (β⁻¹ - 1), σ * ρ * (β⁻¹ - 1)] := by
  have hφ : φπ = 1 - ρ - (1 - β) / (4 * κ) * φx := by linarith
  rw [vecMul_A46, one_smul]
  have e0 : β⁻¹ * -(σ * β⁻¹ * (φπ - 1 + ρ)) + σ * β⁻¹ * (φπ - 1) * ((1 - ρ) * (β⁻¹ - 1)) +
      β⁻¹ * φπ * (σ * ρ * (β⁻¹ - 1)) = -(σ * β⁻¹ * (φπ - 1 + ρ)) := by ring
  have e1 : -(β⁻¹ * κ) * -(σ * β⁻¹ * (φπ - 1 + ρ)) +
      (1 + σ * (φx / 4 - β⁻¹ * κ * (φπ - 1))) * ((1 - ρ) * (β⁻¹ - 1)) +
      (φx / 4 - β⁻¹ * κ * φπ) * (σ * ρ * (β⁻¹ - 1)) = (1 - ρ) * (β⁻¹ - 1) := by
    rw [hφ]; field_simp; ring
  have e2 : σ * ρ * ((1 - ρ) * (β⁻¹ - 1)) + ρ * (σ * ρ * (β⁻¹ - 1)) = σ * ρ * (β⁻¹ - 1) := by
    ring
  funext j
  fin_cases j
  · exact e0
  · exact e1
  · exact e2

/-- Woodford (2003), App. C.5, p. 682: at equality in (2.13) the vector
`q = (−σβ⁻¹(φ_π − 1 − ρ), (1 + ρ)(β⁻¹ + 1), −σρ(β⁻¹ + 1))` is a left eigenvector of the
eigenvalue `−1`. -/
theorem left_negunit_A46 {β κ σ ρ φπ φx : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0) (hσ : σ ≠ 0)
    (heq : φπ = 1 + ρ + (1 + β) / (4 * κ) * (φx + 8 / σ * (1 + ρ))) :
    ![-(σ * β⁻¹ * (φπ - 1 - ρ)), (1 + ρ) * (β⁻¹ + 1), -(σ * ρ * (β⁻¹ + 1))] ᵥ*
      A46 β κ σ ρ φπ φx =
      (-1 : ℝ) • ![-(σ * β⁻¹ * (φπ - 1 - ρ)), (1 + ρ) * (β⁻¹ + 1), -(σ * ρ * (β⁻¹ + 1))] := by
  rw [vecMul_A46]
  have e0 : β⁻¹ * -(σ * β⁻¹ * (φπ - 1 - ρ)) + σ * β⁻¹ * (φπ - 1) * ((1 + ρ) * (β⁻¹ + 1)) +
      β⁻¹ * φπ * -(σ * ρ * (β⁻¹ + 1)) = -1 * -(σ * β⁻¹ * (φπ - 1 - ρ)) := by ring
  have e1 : -(β⁻¹ * κ) * -(σ * β⁻¹ * (φπ - 1 - ρ)) +
      (1 + σ * (φx / 4 - β⁻¹ * κ * (φπ - 1))) * ((1 + ρ) * (β⁻¹ + 1)) +
      (φx / 4 - β⁻¹ * κ * φπ) * -(σ * ρ * (β⁻¹ + 1)) = -1 * ((1 + ρ) * (β⁻¹ + 1)) := by
    rw [heq]; field_simp; ring
  have e2 : σ * ρ * ((1 + ρ) * (β⁻¹ + 1)) + ρ * -(σ * ρ * (β⁻¹ + 1)) =
      -1 * -(σ * ρ * (β⁻¹ + 1)) := by ring
  funext j
  fin_cases j
  · exact e0
  · exact e1
  · exact e2

/-- Woodford (2003), App. C.5: with `φ_π = φ_x = 0` the forward-looking and the backward-looking
inertial rules coincide. -/
theorem A46_zero (β κ σ ρ : ℝ) : A46 β κ σ ρ 0 0 = A44 β κ σ ρ 0 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A46, A44]

/-- **Proposition 4.6, necessity** (Woodford (2003), p. 258; App. C.5, p. 682): for `0 < β < 1`,
`κ, σ > 0`, `ρ, φ_π, φ_x ≥ 0`, determinacy under the forward-looking inertial rule (2.12)
requires both (2.9) and (2.13). Sufficiency (which the book leaves open, "I omit analysis") is
deferred and not claimed. The printed proof cites equation labels "(A.1)–(A.7)" that do not exist
(survey E27); they are (C.11)–(C.17). -/
theorem prop46_necessity [Nonempty Ω] {β κ σ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (hd : Determinate46 𝔼 β κ σ ρ φπ φx) :
    1 - ρ < φπ + (1 - β) / (4 * κ) * φx ∧
      φπ < 1 + ρ + (1 + β) / (4 * κ) * (φx + 8 / σ * (1 + ρ)) := by
  rw [determinate46_iff_for 𝔼 hβ0.ne'] at hd
  have hb1 : 1 < β⁻¹ := one_lt_inv₀ hβ0 |>.mpr hβ1
  have hc : 0 < σ * κ / β := by positivity
  -- the rule must respond to something
  have hφ : 0 < φπ ∨ 0 < φx := by
    by_contra h
    push Not at h
    have e1 : φπ = 0 := le_antisymm h.1 hφπ
    have e2 : φx = 0 := le_antisymm h.2 hφx
    subst e1 e2
    rw [A46_zero] at hd
    exact not_generic_A44_zero hβ0 hκ hσ (generic_of_determinateFor 𝔼 hd)
  -- no unit eigenvalue
  have hP1 : P1 (ch2 (A46 β κ σ ρ φπ φx)) (ch1 (A46 β κ σ ρ φπ φx))
      (ch0 (A46 β κ σ ρ φπ φx)) ≠ 0 := by
    rw [P1_A46 hβ0.ne' hκ.ne']
    intro h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact hc.ne' h
    have heq : φπ + (1 - β) / (4 * κ) * φx = 1 - ρ := by linarith
    have hρ1 : ρ ≠ 1 := by
      rintro rfl
      have hpos : 0 < 1 - β := by linarith
      rcases hφ with h' | h'
      · have : 0 ≤ (1 - β) / (4 * κ) * φx := by positivity
        linarith
      · have : 0 < (1 - β) / (4 * κ) * φx := by positivity
        linarith
    refine not_determinateFor_of_unit_left 𝔼 (left_unit_A46 hβ0.ne' hκ.ne' heq) (one_pow 2)
      ?_ hd
    rw [Fin.sum_univ_three]
    change -(σ * β⁻¹ * (φπ - 1 + ρ)) * 0 + (1 - ρ) * (β⁻¹ - 1) * (-σ) +
      σ * ρ * (β⁻¹ - 1) * 0 ≠ 0
    have : (1 - ρ) * (β⁻¹ - 1) * σ ≠ 0 :=
      mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hρ1)) (by linarith)) hσ.ne'
    intro h0; apply this; linarith
  have hPm1 : Pm1 (ch2 (A46 β κ σ ρ φπ φx)) (ch1 (A46 β κ σ ρ φπ φx))
      (ch0 (A46 β κ σ ρ φπ φx)) ≠ 0 := by
    rw [Pm1_A46 hβ0.ne' hκ.ne' hσ.ne']
    intro h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact hc.ne' h
    have heq : φπ = 1 + ρ + (1 + β) / (4 * κ) * (φx + 8 / σ * (1 + ρ)) := by linarith
    refine not_determinateFor_of_unit_left 𝔼 (left_negunit_A46 hβ0.ne' hκ.ne' hσ.ne' heq)
      (by norm_num) ?_ hd
    rw [Fin.sum_univ_three]
    change -(σ * β⁻¹ * (φπ - 1 - ρ)) * 0 + (1 + ρ) * (β⁻¹ + 1) * (-σ) +
      -(σ * ρ * (β⁻¹ + 1)) * 0 ≠ 0
    have : 0 < (1 + ρ) * (β⁻¹ + 1) * σ := by positivity
    intro h0; linarith
  -- the eigenvalue count, and Prop. C.2
  have hoit := oneInTwoOut_of_determinateFor 𝔼 hd hP1 hPm1
  rcases cases_of_oneInTwoOut hoit with ⟨h1, h2⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · exfalso
    have := caseI_impossible_46 hβ0 hκ hσ h1 h2
    have : 0 ≤ φx / (2 * κ) := by positivity
    have : 0 ≤ 2 * (1 + β) * (1 + ρ) / (κ * σ) := by positivity
    linarith
  all_goals
    rw [P1_A46 hβ0.ne' hκ.ne'] at h1
    rw [Pm1_A46 hβ0.ne' hκ.ne' hσ.ne'] at h2
    have e1 : 0 < φπ + (1 - β) / (4 * κ) * φx - (1 - ρ) := by
      by_contra h; push Not at h; nlinarith
    have e2 : φπ - (1 + ρ) - (1 + β) / (4 * κ) * (φx + 8 / σ * (1 + ρ)) < 0 := by
      by_contra h; push Not at h; nlinarith
    exact ⟨by linarith, by linarith⟩

/-! ### Proposition 4.7: the Wicksellian price-level rule (2.14) -/

/-- Woodford (2003), (1.10), (1.12), (2.14), pp. 245–246, 261 (App. C.6, (C.27)): equilibrium
under the price-level rule `ı̂_t − ī_t = φ_p(p_t − p̄_t) + φ_x(x_t − x̄)` with the state
`y_t = (p_t − p̄_t, x_t − x̄, p_{t−1} − p̄_{t−1})` (the book orders it
`(p_t − p̄_t, p_{t−1} − p̄_{t−1}, x_t − x̄)`). The NKPC is in first differences,
`Δ(p_t − p̄_t) = κ(x_t − x̄) + β E_t Δ(p_{t+1} − p̄_{t+1})`, and `E_t π_{t+1}` in (1.12) is
`E_t Δ(p_{t+1} − p̄_{t+1}) + π̄` (as printed on p. 683; the Δ is lost in text extraction). -/
def Equil47 (β κ σ φp φx : ℝ) (e : ℕ → Ω → ℝ) (p0 : ℝ) (y : ℕ → Fin 3 → Ω → ℝ) : Prop :=
  (∀ t, y t 0 - y t 2 = κ • y t 1 + β • (𝔼.E t (y (t + 1) 0) - y t 0)) ∧
  (∀ t, y t 1 = 𝔼.E t (y (t + 1) 1) -
      σ • (φp • y t 0 + φx • y t 1 - (𝔼.E t (y (t + 1) 0) - y t 0)) + σ • e t) ∧
  (∀ t, y (t + 1) 2 = y t 0) ∧
  y 0 2 = (fun _ => p0) ∧ VAdapted 𝔼 y ∧ VBounded y

/-- Woodford (2003), Prop. 4.7, p. 261: determinacy under the price-level rule (2.14). -/
def Determinate47 (β κ σ φp φx : ℝ) : Prop :=
  ∀ e : ℕ → Ω → ℝ, BoundedProc e → 𝔼.Adapted e → ∀ p0 : ℝ,
    ∃! y, Equil47 𝔼 β κ σ φp φx e p0 y

/-- Woodford (2003), App. C.6, p. 683: the matrix `A` in the state order
`(p_t − p̄_t, x_t − x̄, p_{t−1} − p̄_{t−1})` (predetermined variable last). -/
noncomputable def A47 (β κ σ φp φx : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 + β⁻¹, -(β⁻¹ * κ), -β⁻¹; σ * (φp - β⁻¹), 1 + σ * (φx + β⁻¹ * κ), σ * β⁻¹; 1, 0, 0]

/-- Woodford (2003), App. C.6, p. 683: the matrix exactly as printed, in the order
`(p_t − p̄_t, p_{t−1} − p̄_{t−1}, x_t − x̄)`. -/
noncomputable def A47book (β κ σ φp φx : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 + β⁻¹, -β⁻¹, -(β⁻¹ * κ); 1, 0, 0; σ * (φp - β⁻¹), σ * β⁻¹, 1 + σ * (φx + β⁻¹ * κ)]

/-- Woodford (2003), App. C.6, p. 683: reordering the state does not change the characteristic
polynomial: the printed matrix and `A47` have the same `A₂, A₁, A₀`. -/
theorem A47book_ch (β κ σ φp φx : ℝ) :
    ch2 (A47book β κ σ φp φx) = ch2 (A47 β κ σ φp φx) ∧
      ch1 (A47book β κ σ φp φx) = ch1 (A47 β κ σ φp φx) ∧
      ch0 (A47book β κ σ φp φx) = ch0 (A47 β κ σ φp φx) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [ch2, ch1, ch0, A47book, A47] <;> ring

/-- Woodford (2003), App. C.6, p. 683: `A v` written out. -/
theorem mulVec_A47 (β κ σ φp φx : ℝ) (v : Fin 3 → ℝ) :
    A47 β κ σ φp φx *ᵥ v = ![(1 + β⁻¹) * v 0 - β⁻¹ * κ * v 1 - β⁻¹ * v 2,
      σ * (φp - β⁻¹) * v 0 + (1 + σ * (φx + β⁻¹ * κ)) * v 1 + σ * β⁻¹ * v 2, v 0] := by
  funext i
  fin_cases i <;> simp [A47, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- Woodford (2003), App. C.6, p. 683: the model (1.10), (1.12), (2.14) is the system
`E_t y_{t+1} = A y_t + a e_t` with one predetermined variable. -/
theorem equil47_iff {β κ σ φp φx : ℝ} (hβ : β ≠ 0) (e : ℕ → Ω → ℝ) (p0 : ℝ)
    (y : ℕ → Fin 3 → Ω → ℝ) :
    Equil47 𝔼 β κ σ φp φx e p0 y ↔
      Equil3 𝔼 (A47 β κ σ φp φx) (fun t i => aIS σ i • e t) p0 y := by
  have hb : β⁻¹ * β = 1 := inv_mul_cancel₀ hβ
  constructor
  · rintro ⟨hN, hI, hL, h0, ha, hbd⟩
    have hp : ∀ t, 𝔼.E t (y (t + 1) 2) = y (t + 1) 2 := by
      intro t; rw [hL t, ha t 0]
    refine ⟨fun t i => ?_, ha, hp, h0, hbd⟩
    funext ω
    have n := congrFun (hN t) ω
    have s := congrFun (hI t) ω
    have l := congrFun (hL t) ω
    have p := congrFun (hp t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at n s l p
    fin_cases i <;> simp [rvMul_apply, Fin.sum_univ_three, A47, aIS]
    · linear_combination (-β⁻¹) * n - (𝔼.E t (y (t + 1) 0) ω - y t 0 ω) * hb
    · linear_combination (-1 : ℝ) * s + σ * β⁻¹ * n
        + σ * (𝔼.E t (y (t + 1) 0) ω - y t 0 ω) * hb
    · linear_combination p + l
  · rintro ⟨hs, ha, hp, h0, hbd⟩
    have row : ∀ t (i : Fin 3) ω, 𝔼.E t (y (t + 1) i) ω =
        (rvMul (A47 β κ σ φp φx) (y t) i + aIS σ i • e t) ω := fun t i ω => congrFun (hs t i) ω
    have r0 : ∀ t ω, 𝔼.E t (y (t + 1) 0) ω =
        (1 + β⁻¹) * y t 0 ω - β⁻¹ * κ * y t 1 ω - β⁻¹ * y t 2 ω := by
      intro t ω
      rw [row]
      simp [rvMul_apply, Fin.sum_univ_three, A47, aIS]
      ring
    have r1 : ∀ t ω, 𝔼.E t (y (t + 1) 1) ω = σ * (φp - β⁻¹) * y t 0 ω +
        (1 + σ * (φx + β⁻¹ * κ)) * y t 1 ω + σ * β⁻¹ * y t 2 ω - σ * e t ω := by
      intro t ω
      rw [row]
      simp [rvMul_apply, Fin.sum_univ_three, A47, aIS]
      ring
    have r2 : ∀ t ω, y (t + 1) 2 ω = y t 0 ω := by
      intro t ω
      rw [← hp t, row]
      simp [rvMul_apply, Fin.sum_univ_three, A47, aIS]
    refine ⟨fun t => ?_, fun t => ?_, fun t => funext (r2 t), h0, ha, hbd⟩ <;> funext ω <;>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    · rw [r0]; linear_combination (-(y t 0 ω - y t 2 ω - κ * y t 1 ω)) * hb
    · rw [r1, r0]; ring

/-- Woodford (2003), Prop. 4.7, p. 261: determinacy of the model is determinacy of its system. -/
theorem determinate47_iff_for {β κ σ φp φx : ℝ} (hβ : β ≠ 0) :
    Determinate47 𝔼 β κ σ φp φx ↔ DeterminateFor 𝔼 (A47 β κ σ φp φx) (aIS σ) := by
  unfold Determinate47 DeterminateFor
  simp only [equil47_iff 𝔼 hβ]

/-- Woodford (2003), App. C.6, p. 683: `A₂ = −(2 + β⁻¹ + σφ_x + σκβ⁻¹)`. -/
theorem ch2_A47 (β κ σ φp φx : ℝ) :
    ch2 (A47 β κ σ φp φx) = -(2 + β⁻¹ + σ * φx + σ * κ * β⁻¹) := by
  simp [ch2, A47]; ring

/-- Woodford (2003), App. C.6, p. 683 (the self-contained proof replacing the citation of
Giannoni 2000): `P(1) = σκφ_p/β`, so (C.13) holds for every `φ_p > 0`. -/
theorem P1_A47 (β κ σ φp φx : ℝ) :
    P1 (ch2 (A47 β κ σ φp φx)) (ch1 (A47 β κ σ φp φx)) (ch0 (A47 β κ σ φp φx)) =
      σ * κ * φp * β⁻¹ := by
  simp [P1, ch2, ch1, ch0, A47]; ring

/-- Woodford (2003), App. C.6, p. 683: `P(−1) = −[4(1 + β⁻¹) + 2(1 + β⁻¹)σφ_x + 2σκβ⁻¹ +
σκφ_pβ⁻¹]`, so (C.14) always holds. -/
theorem Pm1_A47 (β κ σ φp φx : ℝ) :
    Pm1 (ch2 (A47 β κ σ φp φx)) (ch1 (A47 β κ σ φp φx)) (ch0 (A47 β κ σ φp φx)) =
      -(4 * (1 + β⁻¹) + 2 * (1 + β⁻¹) * σ * φx + 2 * σ * κ * β⁻¹ + σ * κ * φp * β⁻¹) := by
  simp [Pm1, ch2, ch1, ch0, A47]; ring

/-- Woodford (2003), App. C.6, p. 683: under the sign restrictions Case III′ of Prop. C.2 holds
(`P(1) > 0`, `P(−1) < 0`, `A₂ < −3`), so one eigenvalue is inside and two outside. -/
theorem oneInTwoOut_A47 {β κ σ φp φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hφp : 0 < φp) (hφx : 0 ≤ φx) :
    OneInTwoOut (ch2 (A47 β κ σ φp φx)) (ch1 (A47 β κ σ φp φx)) (ch0 (A47 β κ σ φp φx)) := by
  have hb1 : 1 < β⁻¹ := one_lt_inv₀ hβ0 |>.mpr hβ1
  have hb0 : 0 < β⁻¹ := by linarith
  apply oneInTwoOut_of_cases
  right; right
  refine ⟨?_, ?_, ?_⟩
  · rw [P1_A47]; positivity
  · rw [Pm1_A47]
    have : 0 ≤ 2 * (1 + β⁻¹) * σ * φx := by positivity
    have : 0 < σ * κ * φp * β⁻¹ := by positivity
    have : 0 < 2 * σ * κ * β⁻¹ := by positivity
    linarith
  · rw [ch2_A47, abs_neg]
    have : 0 ≤ σ * φx := by positivity
    have : 0 < σ * κ * β⁻¹ := by positivity
    rw [abs_of_pos (by linarith)]
    linarith

/-- Woodford (2003), App. C.6, p. 683: no eigenvector of `A47` has a zero lagged-price
component — the genericity condition holds for every eigenvalue. -/
theorem generic_A47 {β κ σ φp φx : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) :
    Generic (A47 β κ σ φp φx) := by
  intro μ v _ hv h2
  rw [mulVec_A47] at hv
  have r0 : (1 + β⁻¹) * v 0 - β⁻¹ * κ * v 1 - β⁻¹ * v 2 = μ * v 0 := congrFun hv 0
  have r2 : v 0 = μ * v 2 := congrFun hv 2
  rw [h2, mul_zero] at r2
  rw [r2, h2] at r0
  have hbk : β⁻¹ * κ ≠ 0 := by positivity
  have hv1 : v 1 = 0 := by
    have : β⁻¹ * κ * v 1 = 0 := by linarith
    rcases mul_eq_zero.mp this with e | e
    · exact absurd e hbk
    · exact e
  funext i
  fin_cases i
  · exact r2
  · exact hv1
  · exact h2

/-- **Proposition 4.7** (Woodford (2003), p. 261; App. C.6, p. 683, completed): for
`0 < β < 1`, `κ, σ > 0`, `φ_p > 0` and `φ_x ≥ 0`, equilibrium under the price-level rule (2.14)
is determinate — for every bounded adapted disturbance and every initial price level there is
exactly one bounded equilibrium. The book defers to Giannoni (2000); here the proof is complete:
Case III′ of Prop. C.2 (`oneInTwoOut_A47`), the genericity condition (`generic_A47`) and the
Blanchard–Kahn theorem. -/
theorem prop47 [Nonempty Ω] {β κ σ φp φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hφp : 0 < φp) (hφx : 0 ≤ φx) : Determinate47 𝔼 β κ σ φp φx :=
  (determinate47_iff_for 𝔼 hβ0.ne').mpr (determinateFor_of_determinate3 𝔼
    (determinate3_of 𝔼 (oneInTwoOut_A47 hβ0 hβ1 hκ hσ hφp hφx) (generic_A47 hβ0 hκ)) _)

/-- Woodford (2003), Prop. 4.7, p. 261, in its strongest form: under the price-level rule the
system is determinate for every bounded adapted forcing in all three equations, not only for the
disturbance `a e_t`. -/
theorem prop47_general [Nonempty Ω] {β κ σ φp φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hφp : 0 < φp) (hφx : 0 ≤ φx) :
    Determinate3 𝔼 (A47 β κ σ φp φx) :=
  determinate3_of 𝔼 (oneInTwoOut_A47 hβ0 hβ1 hκ hσ hφp hφx) (generic_A47 hβ0 hκ)

/-- Woodford (2003), App. C.6, p. 683 (why the NKPC must be written in first differences): the
level relation `p_t − p̄_t = κ(x_t − x̄) + βE_t(p_{t+1} − p̄_{t+1})` is a different restriction —
a constant price gap `1` with output gap `(1 − β)/κ` satisfies it but violates the
first-difference form used in `Equil47` and in the printed matrix. -/
theorem level_nkpc_differs {β κ : ℝ} (hβ1 : β < 1) (hκ : 0 < κ) :
    (1 : ℝ) = κ * ((1 - β) / κ) + β * 1 ∧ ¬ ((1 : ℝ) - 1 = κ * ((1 - β) / κ) + β * (1 - 1)) := by
  have e : κ * ((1 - β) / κ) = 1 - β := by field_simp
  refine ⟨by rw [e]; ring, fun h => ?_⟩
  rw [e] at h
  linarith

end Woodford.NeoWicksellianFramework.ThreeByThree
