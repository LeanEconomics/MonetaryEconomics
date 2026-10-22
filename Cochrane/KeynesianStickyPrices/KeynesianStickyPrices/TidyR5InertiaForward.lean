/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR5Inertia

/-!
# The inertial rule (18.2) with forward responses: closed-form determinacy conditions

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 18, eq. (18.2), p. 427, with
inertia `φ_i` and forward responses `φ_{π,1}`, `φ_{x,1}`; a completion (the book makes no
determinacy claim).

`TidyR5Inertia.determinate182_iff_cases` characterised determinacy by Woodford's Cases I, II,
III′ (Prop. C.2) for the characteristic polynomial of `A182`. Here every quantity in those cases
is written in closed form in the eight parameters. With `k = β(1 − σφ_{x,1})`,
`N₂ = β(1 + φ_i + σφ_x) + 1 − σφ_{x,1} + σκ(1 − φ_{π,1})`,
`N₁ = βφ_i + 1 + φ_i + σφ_x + σκ(φ_i + φ_π)`, the characteristic polynomial is
`λ³ − (N₂/k)λ² + (N₁/k)λ − φ_i/k` (`ch2_A182`, `ch1_A182`, `ch0_A182`), and

* `P(1) = D₁/k`, `D₁ = σ[κ(φ_π + φ_{π,1} + φ_i − 1) + (1 − β)(φ_x + φ_{x,1})]` (`P1_A182'`);
* `P(−1) = D₋₁/k`, `D₋₁ = −(1 + β)[2(1 + φ_i) + σ(φ_x − φ_{x,1})] − σκ(1 + φ_i + φ_π − φ_{π,1})`
  (`Pm1_A182`);
* `A₀² − A₀A₂ + A₁ − 1 = (φ_i² − φ_iN₂ + N₁k − k²)/k²` (`C15_A182`); `|A₂| = |N₂|/|k|`.

**`determinate182_closed_iff`**: for `σ, κ, β > 0` and `1 − σφ_{x,1} ≠ 0`, the model with the
rule (18.2) is determinate iff

* (Case I) `D₁k < 0 < D₋₁k`, or
* (Cases II, III′) `D₋₁k < 0 < D₁k` and (`φ_i² − φ_iN₂ + N₁k − k² > 0` or `3|k| < |N₂|`),

and `κ(φ_π + φ_{π,1}μ) + (φ_x + φ_{x,1}μ)(1 − βμ) ≠ 0` at `μ = λ₂/β = 1/λ₁`
(`lam1_inv_eq`), all polynomial inequalities in the parameters (and `λ₂`, the explicit smaller
root (5.6)).
-/

namespace Cochrane.KeynesianStickyPrices.TidyR5InertiaForward

open FullModel TidyR5SchurCohn TidyR5BlanchardKahn TidyR5Inertia

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), eq. (18.2): `k = β(1 − σφ_{x,1})`, the determinant of the matrix of
expectations (the leading coefficient of `det(λM − N)`). -/
def kk (σ β φx1 : ℝ) : ℝ := β * (1 - σ * φx1)

/-- Cochrane (2023), eq. (18.2): `N₂ = β(1 + φ_i + σφ_x) + 1 − σφ_{x,1} + σκ(1 − φ_{π,1})`. -/
def N2 (σ β κ φi φx φπ1 φx1 : ℝ) : ℝ :=
  β * (1 + φi + σ * φx) + (1 - σ * φx1) + σ * κ * (1 - φπ1)

/-- Cochrane (2023), eq. (18.2): `N₁ = βφ_i + 1 + φ_i + σφ_x + σκ(φ_i + φ_π)`. -/
def N1 (σ β κ φi φπ φx : ℝ) : ℝ := β * φi + 1 + φi + σ * φx + σ * κ * (φi + φπ)

/-- Cochrane (2023), eq. (18.2): `D₁ = det(M − N) = σ[κ(φ_π + φ_{π,1} + φ_i − 1) +
(1 − β)(φ_x + φ_{x,1})]`. -/
def D1 (σ β κ φi φπ φx φπ1 φx1 : ℝ) : ℝ :=
  σ * (κ * (φπ + φπ1 + φi - 1) + (1 - β) * (φx + φx1))

/-- Cochrane (2023), eq. (18.2): `D₋₁ = det(−M − N) = −(1 + β)[2(1 + φ_i) + σ(φ_x − φ_{x,1})]
− σκ(1 + φ_i + φ_π − φ_{π,1})`. -/
def Dm1 (σ β κ φi φπ φx φπ1 φx1 : ℝ) : ℝ :=
  -(1 + β) * (2 * (1 + φi) + σ * (φx - φx1)) - σ * κ * (1 + φi + φπ - φπ1)

/-- Cochrane (2023), eq. (18.2): the numerator `φ_i² − φ_iN₂ + N₁k − k²` of Woodford's (C.15). -/
def C15num (σ β κ φi φπ φx φπ1 φx1 : ℝ) : ℝ :=
  φi ^ 2 - φi * N2 σ β κ φi φx φπ1 φx1 + N1 σ β κ φi φπ φx * kk σ β φx1 - kk σ β φx1 ^ 2

/-- Cochrane (2023), eq. (18.2): `A₂ = −N₂/k`. -/
theorem ch2_A182 {σ β κ φi φπ φx φπ1 φx1 : ℝ} (hβ : β ≠ 0) (hg : 1 - σ * φx1 ≠ 0) :
    ch2 (A182 σ β κ φi φπ φx φπ1 φx1) = -N2 σ β κ φi φx φπ1 φx1 / kk σ β φx1 := by
  have hg' : 1 - φx1 * σ ≠ 0 := by rwa [mul_comm]
  simp [ch2, A182, N2, kk]
  field_simp
  ring

/-- Cochrane (2023), eq. (18.2): `A₁ = N₁/k`. -/
theorem ch1_A182 {σ β κ φi φπ φx φπ1 φx1 : ℝ} (hβ : β ≠ 0) (hg : 1 - σ * φx1 ≠ 0) :
    ch1 (A182 σ β κ φi φπ φx φπ1 φx1) = N1 σ β κ φi φπ φx / kk σ β φx1 := by
  have hg' : 1 - φx1 * σ ≠ 0 := by rwa [mul_comm]
  simp [ch1, A182, N1, kk]
  field_simp
  ring

/-- Cochrane (2023), eq. (18.2): `A₀ = −φ_i/k`. -/
theorem ch0_A182 {σ β κ φi φπ φx φπ1 φx1 : ℝ} (hβ : β ≠ 0) (hg : 1 - σ * φx1 ≠ 0) :
    ch0 (A182 σ β κ φi φπ φx φπ1 φx1) = -φi / kk σ β φx1 := by
  have hg' : 1 - φx1 * σ ≠ 0 := by rwa [mul_comm]
  simp [ch0, A182, kk]
  field_simp
  ring

/-- Cochrane (2023), eq. (18.2): `P(1) = D₁/k`. -/
theorem P1_A182' {σ β κ φi φπ φx φπ1 φx1 : ℝ} (hβ : β ≠ 0) (hg : 1 - σ * φx1 ≠ 0) :
    P1 (ch2 (A182 σ β κ φi φπ φx φπ1 φx1)) (ch1 (A182 σ β κ φi φπ φx φπ1 φx1))
        (ch0 (A182 σ β κ φi φπ φx φπ1 φx1)) = D1 σ β κ φi φπ φx φπ1 φx1 / kk σ β φx1 := by
  have hk : kk σ β φx1 ≠ 0 := mul_ne_zero hβ hg
  rw [P1, ch2_A182 hβ hg, ch1_A182 hβ hg, ch0_A182 hβ hg]
  field_simp
  simp only [N2, N1, D1, kk]
  ring

/-- Cochrane (2023), eq. (18.2): `P(−1) = D₋₁/k`. -/
theorem Pm1_A182 {σ β κ φi φπ φx φπ1 φx1 : ℝ} (hβ : β ≠ 0) (hg : 1 - σ * φx1 ≠ 0) :
    Pm1 (ch2 (A182 σ β κ φi φπ φx φπ1 φx1)) (ch1 (A182 σ β κ φi φπ φx φπ1 φx1))
        (ch0 (A182 σ β κ φi φπ φx φπ1 φx1)) = Dm1 σ β κ φi φπ φx φπ1 φx1 / kk σ β φx1 := by
  have hk : kk σ β φx1 ≠ 0 := mul_ne_zero hβ hg
  rw [Pm1, ch2_A182 hβ hg, ch1_A182 hβ hg, ch0_A182 hβ hg]
  field_simp
  simp only [N2, N1, Dm1, kk]
  ring

/-- Cochrane (2023), eq. (18.2), Woodford's (C.15): `A₀² − A₀A₂ + A₁ − 1 =
(φ_i² − φ_iN₂ + N₁k − k²)/k²`. -/
theorem C15_A182 {σ β κ φi φπ φx φπ1 φx1 : ℝ} (hβ : β ≠ 0) (hg : 1 - σ * φx1 ≠ 0) :
    C15 (ch2 (A182 σ β κ φi φπ φx φπ1 φx1)) (ch1 (A182 σ β κ φi φπ φx φπ1 φx1))
        (ch0 (A182 σ β κ φi φπ φx φπ1 φx1)) =
      C15num σ β κ φi φπ φx φπ1 φx1 / kk σ β φx1 ^ 2 := by
  have hk : kk σ β φx1 ≠ 0 := mul_ne_zero hβ hg
  rw [C15, ch2_A182 hβ hg, ch1_A182 hβ hg, ch0_A182 hβ hg, C15num]
  field_simp

/-- Signs of quotients: `a/k < 0 ↔ ak < 0`. -/
theorem div_neg_iff_mul {a k : ℝ} : a / k < 0 ↔ a * k < 0 := by
  rw [div_neg_iff, mul_neg_iff]

/-- Signs of quotients: `0 < a/k ↔ 0 < ak`. -/
theorem div_pos_iff_mul {a k : ℝ} : 0 < a / k ↔ 0 < a * k := by
  rw [div_pos_iff, mul_pos_iff]

/-- Cochrane (2023), eq. (18.2), Woodford's (C.17): `3 < |A₂|` iff `3|k| < |N₂|`. -/
theorem abs_ch2_A182 {σ β κ φi φπ φx φπ1 φx1 : ℝ} (hβ : β ≠ 0) (hg : 1 - σ * φx1 ≠ 0) :
    3 < |ch2 (A182 σ β κ φi φπ φx φπ1 φx1)| ↔
      3 * |kk σ β φx1| < |N2 σ β κ φi φx φπ1 φx1| := by
  have hk : 0 < |kk σ β φx1| := abs_pos.mpr (mul_ne_zero hβ hg)
  rw [ch2_A182 hβ hg, neg_div, abs_neg, abs_div, lt_div_iff₀ hk]

/-- Cochrane (2023), §17.4.1, eq. (5.6): the stable root of the peg is `1/λ₁ = λ₂/β`. -/
theorem lam1_inv_eq {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) :
    (lam1 σ β κ)⁻¹ = lam2 σ β κ / β := by
  have hp := lam_prod ha hβ
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  field_simp
  linarith [hp, mul_comm (lam1 σ β κ) (lam2 σ β κ)]

/-- **Determinacy with inertia and forward responses, closed form** (Cochrane (2023), eq. (18.2),
p. 427; the book makes no claim): for `σ, κ, β > 0` and `1 − σφ_{x,1} ≠ 0`, under any
expectation system on a nonempty state space, the model is determinate iff
(`D₁k < 0 < D₋₁k`, or `D₋₁k < 0 < D₁k` and (`φ_i² − φ_iN₂ + N₁k − k² > 0` or `3|k| < |N₂|`))
and `κ(φ_π + φ_{π,1}μ) + (φ_x + φ_{x,1}μ)(1 − βμ) ≠ 0` at `μ = λ₂/β`. -/
theorem determinate182_closed_iff [Nonempty Ω] {σ β κ φi φπ φx φπ1 φx1 : ℝ} (hσ : 0 < σ)
    (hκ : 0 < κ) (hβ : 0 < β) (hg : 1 - σ * φx1 ≠ 0) :
    Determinate182 𝔼 σ β κ φi φπ φx φπ1 φx1 ↔
      ((D1 σ β κ φi φπ φx φπ1 φx1 * kk σ β φx1 < 0 ∧
            0 < Dm1 σ β κ φi φπ φx φπ1 φx1 * kk σ β φx1) ∨
          (Dm1 σ β κ φi φπ φx φπ1 φx1 * kk σ β φx1 < 0 ∧
            0 < D1 σ β κ φi φπ φx φπ1 φx1 * kk σ β φx1 ∧
            (0 < C15num σ β κ φi φπ φx φπ1 φx1 ∨
              3 * |kk σ β φx1| < |N2 σ β κ φi φx φπ1 φx1|))) ∧
        κ * (φπ + φπ1 * (lam2 σ β κ / β)) + (φx + φx1 * (lam2 σ β κ / β)) *
          (1 - β * (lam2 σ β κ / β)) ≠ 0 := by
  have hk2 : 0 < kk σ β φx1 ^ 2 := by
    have : kk σ β φx1 ≠ 0 := mul_ne_zero hβ.ne' hg
    positivity
  rw [determinate182_iff_cases 𝔼 hσ hκ hβ hg, ← lam1_inv_eq (mul_pos hσ hκ) hβ]
  refine and_congr_left fun _ => ?_
  simp only [CaseI3, CaseII3, CaseIII3', P1_A182' hβ.ne' hg, Pm1_A182 hβ.ne' hg,
    C15_A182 hβ.ne' hg, abs_ch2_A182 hβ.ne' hg, div_neg_iff_mul, div_pos_iff_mul,
    div_pos_iff_of_pos_right hk2]
  tauto

end Cochrane.KeynesianStickyPrices.TidyR5InertiaForward
