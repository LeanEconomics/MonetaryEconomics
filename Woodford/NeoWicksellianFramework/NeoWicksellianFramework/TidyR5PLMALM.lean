/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.TidyR5ForecastSums

/-!
# The perceived-to-actual law of motion under the exact convergence condition

Woodford (2003), *Interest and Prices*, Chapter 4, §2.3, p. 274 (Preston (2005), App. 4): the
`T`-map of Proposition 4.10 maps the perceived law of motion `(Φ̂, Ĉ)` to the actual one.
`PrestonLearning.E_succ_eq_tMapP` proves this assuming every eigenvalue of `βĈ` lies inside the
unit circle. The spectral hypothesis is not needed:

* **`E_succ_eq_tMapP_exact`**: the same conclusion under the exact condition of
  `TidyR5ForecastSums.decisionRules_iff_exact` (the rows of `Φ̂ₛ` and `f_r` annihilate the
  generalised eigenvectors of `βĈ`, resp. `αβĈ`, with eigenvalues of modulus `≥ 1`, and
  `I − βĈ`, `I − αβĈ` are invertible);
* `E_succ_eq_tMapP_of_hasSum`: under per-state convergence of the forecast sums to their closed
  forms (the hypotheses of `TidyR5ForecastSums.decisionRules_iff_of_hasSum`);
* `E_succ_eq_tMapP_without_spectral`: in the counterexample `Ĉ = diag(1/2, 2)`,
  `1/2 < β < 1` (so `βĈ` has the eigenvalue `2β > 1`), the rational forecast is still the
  forecast of `T(Φ̂, Ĉ)`.
-/

namespace Woodford.NeoWicksellianFramework.TidyR5PLMALM

open Matrix Determinacy2 PrestonLearning TidyR5ForecastSums

variable {Ω : Type*} {n : ℕ}

/-- Woodford (2003), p. 274: **PLM → ALM under per-state convergence**: if the forecast sums
converge to their closed forms at the states of date `t + 1`, and (2.29), (2.30), (1.14) hold at
`t + 1` with the estimated model `(Φ̂, Ĉ)` while the states follow (2.24) with matrix `C`, then
`E_t z_{t+1}` is the forecast of the model `T(Φ̂, Ĉ)`. -/
theorem E_succ_eq_tMapP_of_hasSum {𝔼 : ExpectationSystem Ω} {C : Matrix (Fin n) (Fin n) ℝ}
    {s e : ℕ → Fin n → Ω → ℝ} (h : Learning.Regression.StateLaw 𝔼 C s e)
    {α β κ σ φπ φx πbar xbar ci : ℝ} {gr gi : Fin n → ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hΔ : taylorDelta σ κ φπ φx ≠ 0) {Φ : Learning.Regression.Belief (Fin 3) (Fin n)}
    {Ch : Matrix (Fin n) (Fin n) ℝ} (z : ℕ → Fin 3 → Ω → ℝ) (t : ℕ)
    (hD : ∀ ω j, HasSum (fun k => Φ.2 j ⬝ᵥ ((β • Ch) ^ k *ᵥ sv s (t + 1) ω))
      (Φ.2 j ⬝ᵥ ((1 - β • Ch)⁻¹ *ᵥ sv s (t + 1) ω)))
    (hSu : ∀ ω j, HasSum (fun k => Φ.2 j ⬝ᵥ (((α * β) • Ch) ^ k *ᵥ sv s (t + 1) ω))
      (Φ.2 j ⬝ᵥ ((1 - (α * β) • Ch)⁻¹ *ᵥ sv s (t + 1) ω)))
    (hR : ∀ ω, HasSum (fun k => gr ⬝ᵥ ((β • Ch) ^ k *ᵥ sv s (t + 1) ω))
      (gr ⬝ᵥ ((1 - β • Ch)⁻¹ *ᵥ sv s (t + 1) ω)))
    (hz : IS229 β σ gr Φ Ch s z (t + 1) ∧ AS230 α β κ Φ Ch s z (t + 1) ∧
        TaylorRule φπ φx πbar xbar ci gi s z (t + 1)) (j : Fin 3) :
    𝔼.E t (z (t + 1) j) = Learning.Regression.forecast
      (tMapP α β κ σ φπ φx (taylorConst φπ φx πbar xbar ci) gr gi C (Φ, Ch)).1 s t j := by
  have hz' := (decisionRules_iff_of_hasSum hβ0 hβ1 hα0 hα1 hΔ s z (t + 1) hD hSu hR).mp hz
  have hzj : z (t + 1) j = Learning.Regression.affRV
      (interceptP α β κ σ φπ φx (taylorConst φπ φx πbar xbar ci) Φ.1 j)
      (slopeP α β κ σ φπ φx gr gi Φ.2 Ch j) (s (t + 1)) := by
    funext ω
    have := congrFun (hz' ω) j
    rw [tempSol_eq] at this
    rw [this]
    simp [Learning.Regression.affRV, mulVec, dotProduct, sv]
  rw [hzj, Learning.Regression.E_affRV_succ h]
  rfl

/-- Woodford (2003), p. 274: **PLM → ALM under the exact convergence condition**
(`PrestonLearning.E_succ_eq_tMapP` without the spectral hypothesis on `βĈ`). -/
theorem E_succ_eq_tMapP_exact {𝔼 : ExpectationSystem Ω} {C : Matrix (Fin n) (Fin n) ℝ}
    {s e : ℕ → Fin n → Ω → ℝ} (h : Learning.Regression.StateLaw 𝔼 C s e)
    {α β κ σ φπ φx πbar xbar ci : ℝ} {gr gi : Fin n → ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hΔ : taylorDelta σ κ φπ φx ≠ 0) {Φ : Learning.Regression.Belief (Fin 3) (Fin n)}
    {Ch : Matrix (Fin n) (Fin n) ℝ} (hd1 : (1 - β • Ch).det ≠ 0)
    (hd2 : (1 - (α * β) • Ch).det ≠ 0)
    (hΦ1 : ∀ j, ∀ l : ℂ, 1 ≤ ‖l‖ → ∀ v, IsGenEig ((β • Ch).map Complex.ofReal) l v →
      (fun i => (Φ.2 j i : ℂ)) ⬝ᵥ v = 0)
    (hΦ2 : ∀ j, ∀ l : ℂ, 1 ≤ ‖l‖ → ∀ v, IsGenEig (((α * β) • Ch).map Complex.ofReal) l v →
      (fun i => (Φ.2 j i : ℂ)) ⬝ᵥ v = 0)
    (hgr : ∀ l : ℂ, 1 ≤ ‖l‖ → ∀ v, IsGenEig ((β • Ch).map Complex.ofReal) l v →
      (fun i => (gr i : ℂ)) ⬝ᵥ v = 0)
    (z : ℕ → Fin 3 → Ω → ℝ) (t : ℕ)
    (hz : IS229 β σ gr Φ Ch s z (t + 1) ∧ AS230 α β κ Φ Ch s z (t + 1) ∧
        TaylorRule φπ φx πbar xbar ci gi s z (t + 1)) (j : Fin 3) :
    𝔼.E t (z (t + 1) j) = Learning.Regression.forecast
      (tMapP α β κ σ φπ φx (taylorConst φπ φx πbar xbar ci) gr gi C (Φ, Ch)).1 s t j :=
  E_succ_eq_tMapP_of_hasSum h hβ0 hβ1 hα0 hα1 hΔ z t
    (fun _ j => hasSum_of_summable_all hd1 ((summable_all_iff _ _).mpr (hΦ1 j)) _)
    (fun _ j => hasSum_of_summable_all hd2 ((summable_all_iff _ _).mpr (hΦ2 j)) _)
    (fun _ => hasSum_of_summable_all hd1 ((summable_all_iff _ _).mpr hgr) _) hz j

/-- Woodford (2003), p. 274: **PLM → ALM in the counterexample**: with `Ĉ = diag(1/2, 2)`,
`1/2 < β < 1`, `0 ≤ α < 1`, `2αβ ≠ 1`, and beliefs and `f_r` with no weight on the second
state, the rational forecast `E_t z_{t+1}` is the forecast of `T(Φ̂, Ĉ)`, although `βĈ` has the
eigenvalue `2β > 1`. -/
theorem E_succ_eq_tMapP_without_spectral {𝔼 : ExpectationSystem Ω}
    {C : Matrix (Fin 2) (Fin 2) ℝ} {s e : ℕ → Fin 2 → Ω → ℝ}
    (h : Learning.Regression.StateLaw 𝔼 C s e) {α β κ σ φπ φx πbar xbar ci : ℝ}
    {gr gi : Fin 2 → ℝ} (hβ0 : 1 / 2 < β) (hβ1 : β < 1) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (h2αβ : 2 * (α * β) ≠ 1) (hΔ : taylorDelta σ κ φπ φx ≠ 0)
    (Φ : Learning.Regression.Belief (Fin 3) (Fin 2)) (hΦ : ∀ j, Φ.2 j 1 = 0) (hgr : gr 1 = 0)
    (z : ℕ → Fin 3 → Ω → ℝ) (t : ℕ)
    (hz : IS229 β σ gr Φ cexCh s z (t + 1) ∧ AS230 α β κ Φ cexCh s z (t + 1) ∧
        TaylorRule φπ φx πbar xbar ci gi s z (t + 1)) (j : Fin 3) :
    𝔼.E t (z (t + 1) j) = Learning.Regression.forecast
      (tMapP α β κ σ φπ φx (taylorConst φπ φx πbar xbar ci) gr gi C (Φ, cexCh)).1 s t j := by
  have hβa : |β| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hαβa : |α * β| < 1 := by rw [abs_lt]; constructor <;> nlinarith
  have h2β : 2 * β ≠ 1 := by intro h; linarith
  exact E_succ_eq_tMapP_of_hasSum h (by linarith) hβ1 hα0 hα1 hΔ z t
    (fun _ j => cexCh_hasSum hβa h2β _ (hΦ j) _) (fun _ j => cexCh_hasSum hαβa h2αβ _ (hΦ j) _)
    (fun _ => cexCh_hasSum hβa h2β _ hgr _) hz j

end Woodford.NeoWicksellianFramework.TidyR5PLMALM
