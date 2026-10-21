/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.Determinacy2

/-!
# Forward-looking rules, price-level rules and the Clarida et al. numbers

Woodford (2003), *Interest and Prices*, Chapter 4, §2.2, pp. 256–261, with Appendix C.4
(p. 681).

## Main results

* **Proposition 4.5** (`prop_4_5`): under the forward-looking rule (2.10)
  `î_t = ī_t + φ_π (E_t π_{t+1} − π̄) + φ_x (x_t − x̄)/4` equilibrium is determinate iff (2.7)
  and (2.11) `φ_π < 1 + (1 + β)(φ_x + 8σ⁻¹)/(4κ)`, by the book's route through `tr A`, `det A`
  of the C.4 matrix (`fwdA_tr`, `fwdA_det`, `fwdB_eq_inv`, `fwdA_C2_iff`, `fwdA_C3_iff`).
* Too strong a response to expected inflation gives indeterminacy
  (`fwd_large_phiPi_indeterminate`), unlike a response to current inflation
  (`current_large_phiPi_determinate`); the Figure 4.1 bound `φ_π < 27.5` with the Table 5.1
  parameters (`fig41_upper`).
* Footnote 27 for (2.10): the same unit eigenvector `(1, (1 − β)/κ)` (`fwd_fn27_eigenvector`).
* The Clarida et al. (2000) numbers on p. 260 (`clarida_early_longRun`, `clarida_early_29_iff`,
  `clarida_printed_bound_wrong`, survey E20) and the later-period claim (`clarida_later`).
* (2.14)–(2.15): with `φ_p = 0` the price-level rule (2.14) is (1.14) with `φ_π = 0` and the
  output coefficient multiplied by 4, determinate iff `φ_x > κ/(1 − β)` (`eq_2_15`); survey E21
  (`e21_notation`).
-/

namespace Woodford.NeoWicksellianFramework.Determinacy2Forward

open Woodford.NeoWicksellianFramework.Determinacy2 BlanchardKahn
open BasicModel (IS112 NKPCurve xbar)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The forward-looking rule (2.10) -/

/-- Woodford (2003), eq. (2.10), p. 257: the forward-looking Taylor rule
`î_t = ī_t + φ_π (E_t π_{t+1} − π̄) + φ_x (x_t − x̄)/4`, as a process. -/
noncomputable def fwdRate (β κ φπ φx πbar : ℝ) (ib infl x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => ib t + φπ • (𝔼.E t (infl (t + 1)) - fun _ => πbar)
    + (φx / 4) • (x t - fun _ => xbar β κ πbar)

/-- Woodford (2003), eqs. (1.12), (1.13), (2.10), pp. 246, 257: `(π, x)` is an equilibrium under
the forward-looking rule (2.10). -/
def FwdEqm (β σ κ φπ φx πbar : ℝ) (rn ib infl x : ℕ → Ω → ℝ) : Prop :=
  IS112 𝔼 σ x (fwdRate 𝔼 β κ φπ φx πbar ib infl x) infl rn ∧ NKPCurve 𝔼 β κ infl x

/-- Woodford (2003), App. C.4, p. 681: `Γ = 1 + σ φ_x/4 = β det A`. -/
noncomputable def fwdGamma (σ φx : ℝ) : ℝ := 1 + σ * φx / 4

/-- Woodford (2003), eq. (2.18), p. 263 (for the rule (2.10)): the matrix `B = A⁻¹` of the
forward form `z_t = B E_t z_{t+1} + b e_t`. -/
noncomputable def fwdB (β σ κ φπ φx : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(β * fwdGamma σ φx + κ * σ * (1 - φπ)) / fwdGamma σ φx, κ / fwdGamma σ φx;
    σ * (1 - φπ) / fwdGamma σ φx, 1 / fwdGamma σ φx]

/-- Woodford (2003), eq. (2.18), p. 263 (for the rule (2.10)): the forcing coefficients. -/
noncomputable def fwdb (σ κ φx : ℝ) : Fin 2 → ℝ :=
  ![κ * σ / fwdGamma σ φx, σ / fwdGamma σ φx]

/-- Woodford (2003), App. C.4, p. 681: `Γ ≥ 1` under the sign restrictions. -/
theorem one_le_fwdGamma {σ φx : ℝ} (hσ : 0 < σ) (hφx : 0 ≤ φx) : 1 ≤ fwdGamma σ φx := by
  unfold fwdGamma
  have : 0 ≤ σ * φx := mul_nonneg hσ.le hφx
  linarith

/-- Woodford (2003), eq. (2.10) and App. C.4, state by state: under (2.10) the IS relation and
the NKPC are equivalent to the forward form `z = B E z′ + b (r̂ⁿ − ī + π̄)` in deviations. -/
theorem fwd_pt {β σ κ φπ φx πbar xb : ℝ} (hxb : κ * xb = (1 - β) * πbar)
    (hΓ : fwdGamma σ φx ≠ 0) {p x P X rn ib r : ℝ}
    (hr : r = ib + φπ * (P - πbar) + φx / 4 * (x - xb)) :
    (x = X - σ * (r - P - rn) ∧ p = κ * x + β * P) ↔
      (p - πbar = fwdB β σ κ φπ φx 0 0 * (P - πbar) + fwdB β σ κ φπ φx 0 1 * (X - xb)
          + fwdb σ κ φx 0 * (rn - ib + πbar) ∧
        x - xb = fwdB β σ κ φπ φx 1 0 * (P - πbar) + fwdB β σ κ φπ φx 1 1 * (X - xb)
          + fwdb σ κ φx 1 * (rn - ib + πbar)) := by
  subst hr
  simp only [fwdB, fwdb, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  set Γ := fwdGamma σ φx with hΓdef
  have hΓe : Γ = 1 + σ * φx / 4 := rfl
  constructor
  · rintro ⟨h1, h2⟩
    have k1 : Γ * (x - xb) = σ * (1 - φπ) * (P - πbar) + (X - xb) + σ * (rn - ib + πbar) := by
      rw [hΓe]; linear_combination h1
    have k2 : Γ * (p - πbar) = (β * Γ + κ * σ * (1 - φπ)) * (P - πbar) + κ * (X - xb)
        + κ * σ * (rn - ib + πbar) := by
      rw [hΓe]
      linear_combination κ * h1 + (1 + σ * φx / 4) * h2 + (1 + σ * φx / 4) * hxb
    constructor
    · apply mul_left_cancel₀ hΓ
      rw [k2]
      field_simp
    · apply mul_left_cancel₀ hΓ
      rw [k1]
      field_simp
  · rintro ⟨h1, h2⟩
    have k2 : Γ * (p - πbar) = (β * Γ + κ * σ * (1 - φπ)) * (P - πbar) + κ * (X - xb)
        + κ * σ * (rn - ib + πbar) := by
      rw [h1]; field_simp
    have k1 : Γ * (x - xb) = σ * (1 - φπ) * (P - πbar) + (X - xb) + σ * (rn - ib + πbar) := by
      rw [h2]; field_simp
    have e : Γ * (p - κ * x - β * P) = 0 := by
      linear_combination k2 - κ * k1 - Γ * hxb
    have hn : p = κ * x + β * P := by
      have := (mul_eq_zero.mp e).resolve_left hΓ
      linarith
    refine ⟨?_, hn⟩
    rw [hΓe] at k1
    linear_combination k1

/-- Woodford (2003), eq. (2.10) and App. C.4: under (2.10) the model is exactly the forward
system `z_t = B E_t z_{t+1} + b (r̂ⁿ_t − ī_t + π̄)` in `z = (π − π̄, x − x̄)`. -/
theorem fwdEqm_iff_solves {β σ κ φπ φx : ℝ} (hκ : κ ≠ 0) (hΓ : fwdGamma σ φx ≠ 0)
    (πbar : ℝ) (rn ib infl x : ℕ → Ω → ℝ) :
    FwdEqm 𝔼 β σ κ φπ φx πbar rn ib infl x ↔
      𝔼.Solves (fwdB β σ κ φπ φx) (fwdForcing (fwdb σ κ φx) rn ib πbar)
        (devStack infl x πbar (xbar β κ πbar)) := by
  rw [solves_dev_iff, FwdEqm, IS_iff, NKPC_iff, ← forall_and]
  refine forall_congr' fun t => ?_
  rw [← forall_and]
  refine forall_congr' fun ω => ?_
  exact fwd_pt (kappa_mul_xbar hκ πbar) hΓ (by simp [fwdRate])

/-- Woodford (2003), App. C.4, p. 681: the matrix `A` of the system (C.19) under (2.10). -/
noncomputable def fwdA (β σ κ φπ φx : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![β⁻¹, -(β⁻¹ * κ); σ * β⁻¹ * (φπ - 1), 1 + σ * (φx / 4 - β⁻¹ * κ * (φπ - 1))]

/-- Woodford (2003), App. C.4, p. 681, state by state: under (2.10) the model is
`E_t z_{t+1} = A z_t + a (r̂ⁿ_t − ī_t + π̄)`, `a = (0, −σ)`, with the C.4 matrix `A`. -/
theorem fwd_C4_pt {β σ κ φπ φx πbar xb : ℝ} (hβ : β ≠ 0) (hxb : κ * xb = (1 - β) * πbar)
    {p x P X rn ib r : ℝ} (hr : r = ib + φπ * (P - πbar) + φx / 4 * (x - xb)) :
    (x = X - σ * (r - P - rn) ∧ p = κ * x + β * P) ↔
      (P - πbar = fwdA β σ κ φπ φx 0 0 * (p - πbar) + fwdA β σ κ φπ φx 0 1 * (x - xb)
          + 0 * (rn - ib + πbar) ∧
        X - xb = fwdA β σ κ φπ φx 1 0 * (p - πbar) + fwdA β σ κ φπ φx 1 1 * (x - xb)
          + -σ * (rn - ib + πbar)) := by
  subst hr
  simp only [fwdA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  constructor
  · rintro ⟨h1, h2⟩
    have hb : β * (P - πbar) = (p - πbar) - κ * (x - xb) := by linear_combination -h2 - hxb
    have hP : P - πbar = β⁻¹ * ((p - πbar) - κ * (x - xb)) := by
      rw [← hb]; field_simp
    refine ⟨by rw [hP]; ring, ?_⟩
    linear_combination -h1 + σ * (φπ - 1) * hP
  · rintro ⟨h1, h2⟩
    have hb : β * (P - πbar) = (p - πbar) - κ * (x - xb) := by rw [h1]; field_simp; ring
    have hP : P - πbar = β⁻¹ * ((p - πbar) - κ * (x - xb)) := by rw [h1]; ring
    refine ⟨?_, by linear_combination -hb - hxb⟩
    linear_combination -h2 + σ * (φπ - 1) * hP

/-- Woodford (2003), App. C.4, p. 681: under (2.10) the model (1.12)–(1.13) is the system
(C.19) with the C.4 matrix `A`. -/
theorem fwdEqm_iff_C4 {β σ κ φπ φx : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0) (πbar : ℝ)
    (rn ib infl x : ℕ → Ω → ℝ) :
    FwdEqm 𝔼 β σ κ φπ φx πbar rn ib infl x ↔ ∀ t ω,
      (𝔼.E t (infl (t + 1)) ω - πbar =
          fwdA β σ κ φπ φx 0 0 * (infl t ω - πbar)
          + fwdA β σ κ φπ φx 0 1 * (x t ω - xbar β κ πbar) + 0 * (rn t ω - ib t ω + πbar)) ∧
      (𝔼.E t (x (t + 1)) ω - xbar β κ πbar =
          fwdA β σ κ φπ φx 1 0 * (infl t ω - πbar)
          + fwdA β σ κ φπ φx 1 1 * (x t ω - xbar β κ πbar)
          + -σ * (rn t ω - ib t ω + πbar)) := by
  rw [FwdEqm, IS_iff, NKPC_iff, ← forall_and]
  refine forall_congr' fun t => ?_
  rw [← forall_and]
  refine forall_congr' fun ω => ?_
  exact fwd_C4_pt hβ (kappa_mul_xbar hκ πbar) (by simp [fwdRate])

/-- Woodford (2003), App. C.4, p. 681: `tr A = 1 + β⁻¹ + σ(φ_x/4 − β⁻¹κ(φ_π − 1))`. -/
theorem fwdA_tr (β σ κ φπ φx : ℝ) :
    tr2 (fwdA β σ κ φπ φx) = 1 + β⁻¹ + σ * (φx / 4 - β⁻¹ * κ * (φπ - 1)) := by
  simp only [fwdA, tr2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- Woodford (2003), App. C.4, p. 681: `det A = β⁻¹(1 + σ φ_x/4)`. -/
theorem fwdA_det (β σ κ φπ φx : ℝ) :
    det2 (fwdA β σ κ φπ φx) = β⁻¹ * (1 + σ * φx / 4) := by
  simp only [fwdA, det2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- Woodford (2003), eq. (2.18) and App. C.4: the forward-form matrix `B` under (2.10) is the
inverse of the C.4 matrix `A`. -/
theorem fwdB_eq_inv {β σ κ φπ φx : ℝ} (hβ : β ≠ 0) :
    fwdB β σ κ φπ φx = inv2 (fwdA β σ κ φπ φx) := by
  have hd := fwdA_det β σ κ φπ φx
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [fwdB, inv2, hd, fwdGamma, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one] <;>
    simp only [fwdA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    field_simp <;> ring

/-- Woodford (2003), eq. (2.11), p. 257: the upper bound `1 + (1 + β)(φ_x + 8σ⁻¹)/(4κ)` on
`φ_π`. -/
noncomputable def fwdUpper (β σ κ φx : ℝ) : ℝ := 1 + (1 + β) / (4 * κ) * (φx + 8 * σ⁻¹)

/-- Woodford (2003), App. C.4, p. 681: (C.2) `det A − tr A > −1` is again equivalent to (2.7),
since `det A − tr A + 1 = (σκ/β)(φ_π + (1 − β)φ_x/(4κ) − 1)`. -/
theorem fwdA_C2_iff {β σ κ φπ φx : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) :
    -1 < det2 (fwdA β σ κ φπ φx) - tr2 (fwdA β σ κ φπ φx) ↔ 1 < taylorLHS β κ φπ φx := by
  have e : det2 (fwdA β σ κ φπ φx) - tr2 (fwdA β σ κ φπ φx) + 1 =
      σ * κ / β * (taylorLHS β κ φπ φx - 1) := by
    rw [fwdA_det, fwdA_tr, taylorLHS]
    field_simp
    ring
  have hc : 0 < σ * κ / β := by positivity
  constructor
  · intro h
    have : 0 < σ * κ / β * (taylorLHS β κ φπ φx - 1) := by linarith
    have := (pos_iff_pos_of_mul_pos this).mp hc
    linarith
  · intro h
    have : 0 < σ * κ / β * (taylorLHS β κ φπ φx - 1) := mul_pos hc (by linarith)
    linarith

/-- Woodford (2003), App. C.4, p. 681: (C.3) `det A + tr A > −1` is equivalent to (2.11) (= (C.25)),
since `det A + tr A + 1 = (σκ/β)(1 + (1 + β)(φ_x + 8σ⁻¹)/(4κ) − φ_π)`. -/
theorem fwdA_C3_iff {β σ κ φπ φx : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) :
    -1 < det2 (fwdA β σ κ φπ φx) + tr2 (fwdA β σ κ φπ φx) ↔ φπ < fwdUpper β σ κ φx := by
  have e : det2 (fwdA β σ κ φπ φx) + tr2 (fwdA β σ κ φπ φx) + 1 =
      σ * κ / β * (fwdUpper β σ κ φx - φπ) := by
    rw [fwdA_det, fwdA_tr, fwdUpper]
    field_simp
    ring
  have hc : 0 < σ * κ / β := by positivity
  constructor
  · intro h
    have : 0 < σ * κ / β * (fwdUpper β σ κ φx - φπ) := by linarith
    have := (pos_iff_pos_of_mul_pos this).mp hc
    linarith
  · intro h
    have : 0 < σ * κ / β * (fwdUpper β σ κ φx - φπ) := mul_pos hc (by linarith)
    linarith

/-- Woodford (2003), App. C.4, p. 681: (C.1) `det A > 1` holds under the sign restrictions
(so Case II of Proposition C.1 is impossible, `not_caseII`). -/
theorem fwdA_C1 {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hφx : 0 ≤ φx) :
    1 < det2 (fwdA β σ κ φπ φx) := by
  rw [fwdA_det]
  have hb : 1 < β⁻¹ := (one_lt_inv₀ hβ0).mpr hβ1
  have hg := one_le_fwdGamma hσ hφx
  unfold fwdGamma at hg
  nlinarith

/-- Woodford (2003), App. C.4, p. 681: both eigenvalues of the C.4 matrix lie outside the unit
circle iff (2.7) and (2.11). -/
theorem fwdB_schurStable_iff {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) (hφx : 0 ≤ φx) :
    SchurStable (tr2 (fwdB β σ κ φπ φx)) (det2 (fwdB β σ κ φπ φx)) ↔
      1 < taylorLHS β κ φπ φx ∧ φπ < fwdUpper β σ κ φx := by
  have h1 := fwdA_C1 (κ := κ) (φπ := φπ) hβ0 hβ1 hσ hφx
  rw [fwdB_eq_inv hβ0.ne', schurStable_inv_iff_caseI (by linarith),
    ← fwdA_C2_iff hβ0 hσ hκ, ← fwdA_C3_iff hβ0 hσ hκ]
  exact ⟨fun h => h.2, fun h => ⟨h1, h⟩⟩

/-- **Proposition 4.5** (Woodford (2003), p. 257, proof App. C.4, p. 681): under the
forward-looking rule (2.10) with `φ_π, φ_x ≥ 0`, equilibrium is determinate — for every bounded
adapted `r̂ⁿ` and `ī` exactly one bounded adapted equilibrium — iff (2.7) and (2.11)
`φ_π < 1 + (1 + β)(φ_x + 8σ⁻¹)/(4κ)`. No boundary case is excluded. -/
theorem prop_4_5 [Nonempty Ω] {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) (hφx : 0 ≤ φx) (πbar : ℝ) :
    ModelDeterminate 𝔼 (FwdEqm 𝔼 β σ κ φπ φx πbar) ↔
      1 < taylorLHS β κ φπ φx ∧ φπ < fwdUpper β σ κ φx := by
  have hΓ := one_le_fwdGamma hσ hφx
  rw [modelDeterminate_iff 𝔼 (fwdB β σ κ φπ φx) (fwdb σ κ φx) πbar πbar
    (xbar β κ πbar) _ (fun rn ib infl x =>
      fwdEqm_iff_solves 𝔼 hκ.ne' (by linarith) πbar rn ib infl x)]
  exact fwdB_schurStable_iff hβ0 hβ1 hσ hκ hφx

/-- Woodford (2003), p. 257: under (2.10), (2.11) fails for large enough `φ_π` even though the
Taylor principle holds: every `φ_π ≥ 1 + (1 + β)(φ_x + 8σ⁻¹)/(4κ)` gives indeterminacy. -/
theorem fwd_large_phiPi_indeterminate [Nonempty Ω] {β σ κ φπ φx : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ) (hφx : 0 ≤ φx) (h : fwdUpper β σ κ φx ≤ φπ)
    (πbar : ℝ) : ¬ ModelDeterminate 𝔼 (FwdEqm 𝔼 β σ κ φπ φx πbar) := by
  rw [prop_4_5 𝔼 hβ0 hβ1 hσ hκ hφx]
  exact fun h' => absurd h'.2 (not_lt.mpr h)

/-- Woodford (2003), p. 257: "This problem does not arise in the case of a strong response to
the inflation that has already occurred no matter how large `φ_π` is made": under (1.14) every
`φ_π > 1` gives determinacy. -/
theorem current_large_phiPi_determinate [Nonempty Ω] {β σ κ φπ φx : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ) (hφx : 0 ≤ φx) (h : 1 < φπ) (πbar : ℝ) :
    ModelDeterminate 𝔼 (TaylorEqm 𝔼 β σ κ φπ φx πbar) := by
  rw [prop_4_3 𝔼 hβ0 hβ1 hσ hκ (by linarith) hφx]
  exact taylor_large_phiPi hβ1 hκ hφx h

/-- Woodford (2003), Figure 4.1, p. 258: with the Table 5.1 parameters (`β = 0.99`,
`σ = 1/0.16`, `κ = 0.024`) the upper bound (2.11) is `1 + 1.99 (φ_x + 1.28)/0.096`, equal to
`413/15 ≈ 27.5` at `φ_x = 0` and increasing in `φ_x`; so every `φ_π ≤ 27.5` with `φ_x ≥ 0`
satisfies (2.11): indeterminacy from too high a `φ_π` needs values far above empirical ones. -/
theorem fig41_upper {φx : ℝ} (hφx : 0 ≤ φx) :
    fwdUpper 0.99 (1 / 0.16) 0.024 0 = 413 / 15 ∧
      ∀ φπ : ℝ, φπ ≤ 27.5 → φπ < fwdUpper 0.99 (1 / 0.16) 0.024 φx := by
  refine ⟨by unfold fwdUpper; norm_num, fun φπ h => ?_⟩
  unfold fwdUpper
  norm_num
  nlinarith

/-- Woodford (2003), fn. 27, p. 256 (for the rule (2.10)): when (2.7) holds with equality,
`(1, (1 − β)/κ)` is again an eigenvector with eigenvalue `1` of the C.4 matrix. -/
theorem fwd_fn27_eigenvector {β σ κ φπ φx : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0)
    (h : taylorLHS β κ φπ φx = 1) :
    (fwdA β σ κ φπ φx).mulVec ![1, (1 - β) / κ] = ![1, (1 - β) / κ] := by
  unfold taylorLHS at h
  ext i
  fin_cases i <;>
    simp [fwdA, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp
  · ring
  · field_simp at h
    linear_combination σ * β * h

/-! ### The Clarida et al. (2000) numbers, p. 260 -/

/-- Woodford (2003), eq. (2.9), p. 255: the Taylor-principle condition for the inertial rules
(2.8), (2.12): `φ_π + (1 − β)φ_x/(4κ) > 1 − ρ`. -/
def Cond29 (β κ ρ φπ φx : ℝ) : Prop := 1 - ρ < taylorLHS β κ φπ φx

/-- Woodford (2003), eq. (2.13), p. 258: `φ_π < 1 + ρ + (1 + β)(φ_x + 8σ⁻¹(1 + ρ))/(4κ)`. -/
def Cond213 (β σ κ ρ φπ φx : ℝ) : Prop :=
  φπ < 1 + ρ + (1 + β) / (4 * κ) * (φx + 8 * σ⁻¹ * (1 + ρ))

/-- Woodford (2003), p. 260: with the Clarida et al. early-period estimates `ρ = 0.68`,
`φ_π = 0.27`, the long-run inflation response is `0.27/0.32 = 0.84375` — 84 basis points per
point of inflation (the text says 83). -/
theorem clarida_early_longRun : (0.27 : ℝ) / (1 - 0.68) = 0.84375 := by norm_num

/-- Woodford (2003), p. 260, corrected (survey E20): with `ρ = 0.68`, `φ_π = 0.27`,
`φ_x = 0.09`, condition (2.9) holds iff `κ < 0.45(1 − β)` (not `0.4(1 − β)` as printed). -/
theorem clarida_early_29_iff {β κ : ℝ} (hκ : 0 < κ) :
    Cond29 β κ 0.68 0.27 0.09 ↔ κ < 0.45 * (1 - β) := by
  unfold Cond29 taylorLHS
  rw [div_mul_eq_mul_div]
  constructor
  · intro h
    have h' : 0.05 < (1 - β) * 0.09 / (4 * κ) := by linarith
    rw [lt_div_iff₀ (by linarith)] at h'
    linarith
  · intro h
    have h' : 0.05 < (1 - β) * 0.09 / (4 * κ) := by
      rw [lt_div_iff₀ (by linarith)]
      linarith
    linarith

/-- Woodford (2003), p. 260, survey E20 (counterexample to the printed bound): with `β = 0.99`
the bound is `κ < 0.0045`; `κ = 0.0042` exceeds the printed `0.4(1 − β) = 0.004` yet satisfies
(2.9). -/
theorem clarida_printed_bound_wrong :
    (0.45 : ℝ) * (1 - 0.99) = 0.0045 ∧ (0.4 : ℝ) * (1 - 0.99) < 0.0042 ∧
      Cond29 0.99 0.0042 0.68 0.27 0.09 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [clarida_early_29_iff (by norm_num)]
  norm_num

/-- Woodford (2003), p. 260: with the Clarida et al. later-period estimates `ρ = 0.79`,
`φ_π = 0.45`, `φ_x = 0.20`: `φ_π > 1 − ρ`, so (2.9) holds whatever the slope `κ`; and
`φ_π < 1`, so (2.13) holds as well (for all admissible `β`, `σ`, `κ`). -/
theorem clarida_later {β σ κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ) :
    Cond29 β κ 0.79 0.45 0.20 ∧ (0.45 : ℝ) < 1 ∧ Cond213 β σ κ 0.79 0.45 0.20 := by
  refine ⟨?_, by norm_num, ?_⟩
  · unfold Cond29 taylorLHS
    have : 0 ≤ (1 - β) / (4 * κ) * 0.20 :=
      mul_nonneg (div_nonneg (by linarith) (by linarith)) (by norm_num)
    linarith
  · unfold Cond213
    have : 0 ≤ (1 + β) / (4 * κ) * (0.20 + 8 * σ⁻¹ * (1 + 0.79)) := by positivity
    linarith

/-! ### The price-level rule (2.14) with `φ_p = 0` -/

/-- Woodford (2003), eq. (2.14), p. 261: the rule `î_t = ī_t + φ_p (p_t − p̄_t) + φ_x (x_t − x̄)`
(note: no division of `φ_x` by 4), as a process, for given price-level paths. -/
noncomputable def plRate (β κ φp φx πbar : ℝ) (ib p pbar x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => ib t + φp • (p t - pbar t) + φx • (x t - fun _ => xbar β κ πbar)

/-- Woodford (2003), eqs. (1.12), (1.13), (2.14): `(π, x)` is an equilibrium under the rule
(2.14) for given price-level paths `p`, `p̄`. -/
def PLEqm (β σ κ φp φx πbar : ℝ) (p pbar rn ib infl x : ℕ → Ω → ℝ) : Prop :=
  IS112 𝔼 σ x (plRate β κ φp φx πbar ib p pbar x) infl rn ∧ NKPCurve 𝔼 β κ infl x

/-- Woodford (2003), p. 261: with `φ_p = 0`, the rule (2.14) is (1.14) with `φ_π = 0` and the
output coefficient `4 φ_x` (survey E21). -/
theorem plEqm_zero_eq (β σ κ φx πbar : ℝ) (p pbar : ℕ → Ω → ℝ) :
    (fun rn ib infl x => PLEqm 𝔼 β σ κ 0 φx πbar p pbar rn ib infl x) =
      TaylorEqm 𝔼 β σ κ 0 (4 * φx) πbar := by
  funext rn ib infl x
  have : plRate β κ 0 φx πbar ib p pbar x = taylorRate β κ 0 (4 * φx) πbar ib infl x := by
    funext t
    simp only [plRate, taylorRate, zero_smul, add_zero]
    congr 1
    ring_nf
  rw [PLEqm, TaylorEqm, this]

/-- Woodford (2003), eq. (2.15), p. 261: with `φ_p = 0` the rule (2.14) gives a determinate
equilibrium iff `φ_x > κ/(1 − β)` (in the notation of (2.14)). -/
theorem eq_2_15 [Nonempty Ω] {β σ κ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) (hφx : 0 ≤ φx) (πbar : ℝ) (p pbar : ℕ → Ω → ℝ) :
    ModelDeterminate 𝔼 (fun rn ib infl x => PLEqm 𝔼 β σ κ 0 φx πbar p pbar rn ib infl x) ↔
      κ / (1 - β) < φx := by
  rw [plEqm_zero_eq, prop_4_3 𝔼 hβ0 hβ1 hσ hκ le_rfl (by linarith)]
  unfold taylorLHS
  have h1 : 0 < 1 - β := by linarith
  rw [div_lt_iff₀ h1]
  constructor
  · intro h
    have e : (0 : ℝ) + (1 - β) / (4 * κ) * (4 * φx) = (1 - β) * φx / κ := by
      field_simp; ring
    rw [e, lt_div_iff₀ hκ] at h
    linarith
  · intro h
    have e : (0 : ℝ) + (1 - β) / (4 * κ) * (4 * φx) = (1 - β) * φx / κ := by
      field_simp; ring
    rw [e, lt_div_iff₀ hκ]
    linarith

/-- Woodford (2003), p. 261, survey E21 (notation): read in the notation of (1.14) (output
coefficient divided by 4), `φ_π = 0` gives determinacy iff `φ_x > 4κ/(1 − β)`, not
`κ/(1 − β)`. With `φ_x = 2κ/(1 − β)`, (2.14) is determinate but (1.14) with the same number is
not. -/
theorem e21_notation [Nonempty Ω] {β σ κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) (πbar : ℝ) (p pbar : ℕ → Ω → ℝ) :
    ModelDeterminate 𝔼 (fun rn ib infl x =>
        PLEqm 𝔼 β σ κ 0 (2 * κ / (1 - β)) πbar p pbar rn ib infl x) ∧
      ¬ ModelDeterminate 𝔼 (TaylorEqm 𝔼 β σ κ 0 (2 * κ / (1 - β)) πbar) := by
  have h1 : 0 < 1 - β := by linarith
  have hφ : 0 ≤ 2 * κ / (1 - β) := by positivity
  refine ⟨(eq_2_15 𝔼 hβ0 hβ1 hσ hκ hφ πbar p pbar).mpr ?_, ?_⟩
  · rw [div_lt_div_iff_of_pos_right h1]
    linarith
  · rw [prop_4_3 𝔼 hβ0 hβ1 hσ hκ le_rfl hφ]
    unfold taylorLHS
    have e : (0 : ℝ) + (1 - β) / (4 * κ) * (2 * κ / (1 - β)) = 1 / 2 := by
      field_simp
      ring
    rw [e]
    norm_num

end Woodford.NeoWicksellianFramework.Determinacy2Forward
