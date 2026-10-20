/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.Prop410

/-!
# The fixed point of Preston's `T`-map is a rational-expectations equilibrium

Woodford (2003), *Interest and Prices*, Chapter 4, p. 274: "Once again, the (generically unique)
fixed point `(Φ̄, C)` of this mapping is an r.e.e." (Preston (2005), §3.1). Uniqueness of the
fixed point is `Prop410.fixed_existsUnique_of_taylor`; here the r.e.e. property.

* `E_affRV_iter`: `E_t(c + a′s_{t+k}) = c + a′Cᵏ s_t` under (2.24).
* `z_eq_affRV`, `z_bounded`, `rnP`, `rnP_bounded`: the d.g.p. is affine in the state, bounded
  for a bounded state.
* `fcast_eq_E`, `rnfc_eq_E`, `subj_eq_E`: at a fixed point every subjective forecast entering
  (2.29)–(2.30) is the rational forecast.
* `prestonIS_of_fixed`, `prestonAS_of_fixed`: (2.29) and (2.30) hold with rational
  expectations (`Learning.Preston.PrestonIS`, `PrestonAS`; `E_t` commutes with the dominated
  sums, `ExpectationSystem.E_tsum`).
* **`fixed_isREE`**: hence (by `Learning.Preston.preston_IS_iff`, `preston_AS_iff`) the d.g.p.
  satisfies (2.17), (2.16) and (1.14) under rational expectations: it is a rational-expectations
  equilibrium of the basic neo-Wicksellian model, for every `ExpectationSystem`.
-/

namespace Woodford.NeoWicksellianFramework.Prop410REE

open Matrix Determinacy2 PrestonLearning Prop410
open Learning.Regression (affRV StateLaw E_affRV_succ E_affRV_of_known affRV_bounded)

variable {Ω : Type*} {n : ℕ}

/-- Woodford (2003), (2.24) p. 270: `E_t (c + a′ s_{t+k}) = c + a′ Cᵏ s_t` (iterating
`E_t s_{t+1} = C s_t` with the law of iterated expectations). -/
theorem E_affRV_iter {𝔼 : ExpectationSystem Ω} {C : Matrix (Fin n) (Fin n) ℝ}
    {s e : ℕ → Fin n → Ω → ℝ} (h : StateLaw 𝔼 C s e) (t k : ℕ) (c : ℝ) (a : Fin n → ℝ) :
    𝔼.E t (affRV c a (s (t + k))) = affRV c (a ᵥ* C ^ k) (s t) := by
  induction k generalizing a with
  | zero =>
    simp only [add_zero, pow_zero, vecMul_one]
    exact E_affRV_of_known 𝔼 c a (h.1 t)
  | succ k ih =>
    have htw := 𝔼.tower (Nat.le_add_right t k) (affRV c a (s (t + k + 1)))
    rw [show t + (k + 1) = t + k + 1 by omega, ← htw, E_affRV_succ h (t + k), ih,
      vecMul_vecMul, pow_succ']

/-- Woodford (2003), p. 274: under the long-horizon rules and the Taylor rule at date `t`, with
the estimated model `(Φ̂, Ĉ)`, `z_t` is affine in `s_t` with intercept `T₀(Φ̂₀)` and slopes
`Mₛ(Φ̂ₛ, Ĉ)`. -/
theorem z_eq_affRV {α β κ σ φπ φx πbar xbar ci : ℝ} {gr gi : Fin n → ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hΔ : taylorDelta σ κ φπ φx ≠ 0) {Φ : Learning.Regression.Belief (Fin 3) (Fin n)}
    {Ch : Matrix (Fin n) (Fin n) ℝ}
    (hK : ∀ w, KroneckerSpectrum.IsEig ((β • Ch).map Complex.ofReal) w → ‖w‖ < 1)
    {s : ℕ → Fin n → Ω → ℝ} {z : ℕ → Fin 3 → Ω → ℝ} {t : ℕ}
    (hz : IS229 β σ gr Φ Ch s z t ∧ AS230 α β κ Φ Ch s z t ∧
        TaylorRule φπ φx πbar xbar ci gi s z t) (j : Fin 3) :
    z t j = affRV (interceptP α β κ σ φπ φx (taylorConst φπ φx πbar xbar ci) Φ.1 j)
      (slopeP α β κ σ φπ φx gr gi Φ.2 Ch j) (s t) := by
  have hz' := (decisionRules_iff hβ0 hβ1 hα0 hα1 hΔ hK s z t).mp hz
  funext ω
  have := congrFun (hz' ω) j
  rw [tempSol_eq] at this
  rw [this]
  simp [affRV, mulVec, dotProduct, sv]

/-! ### At the fixed point, subjective forecasts are rational -/

/-- Woodford (2003), p. 274: at a fixed point `(Φ̄, C)` the estimated model's forecast of
`z_{t+k+1}` is the rational forecast `E_t z_{t+k+1}` (the actual law of motion is the
perceived one). -/
theorem fcast_eq_E {𝔼 : ExpectationSystem Ω} {C : Matrix (Fin n) (Fin n) ℝ}
    {s e : ℕ → Fin n → Ω → ℝ} (h : StateLaw 𝔼 C s e) {α β κ σ φπ φx πbar xbar ci : ℝ}
    {gr gi : Fin n → ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hΔ : taylorDelta σ κ φπ φx ≠ 0)
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ‖ρ‖ < 1)
    {Φ : Learning.Regression.Belief (Fin 3) (Fin n)} {z : ℕ → Fin 3 → Ω → ℝ}
    (hz : ∀ t, IS229 β σ gr Φ C s z t ∧ AS230 α β κ Φ C s z t ∧
      TaylorRule φπ φx πbar xbar ci gi s z t)
    (hfix : tMapP α β κ σ φπ φx (taylorConst φπ φx πbar xbar ci) gr gi C (Φ, C) = (Φ, C))
    (t k : ℕ) (j : Fin 3) :
    (fun ω => fcast Φ C s t k j ω) = 𝔼.E t (z (t + k + 1) j) := by
  have hK := norm_lt_one_of_isEig_smul hC (a := β) (by rw [abs_le]; constructor <;> linarith)
  have hI : interceptP α β κ σ φπ φx (taylorConst φπ φx πbar xbar ci) Φ.1 = Φ.1 :=
    congrArg (fun B => B.1.1) hfix
  have hS : slopeP α β κ σ φπ φx gr gi Φ.2 C * C = Φ.2 := congrArg (fun B => B.1.2) hfix
  rw [z_eq_affRV hβ0 hβ1 hα0 hα1 hΔ hK (hz (t + k + 1)) j,
    show t + k + 1 = t + (k + 1) by omega, E_affRV_iter h, hI]
  have hrow : slopeP α β κ σ φπ φx gr gi Φ.2 C j ᵥ* C ^ (k + 1) = Φ.2 j ᵥ* C ^ k := by
    rw [pow_succ', ← vecMul_vecMul]
    congr 1
    conv_rhs => rw [← hS]
    funext l
    simp [Matrix.mul_apply, vecMul, dotProduct]
  rw [hrow]
  funext ω
  simp only [fcast, affRV, dotProduct_mulVec]
  rfl

/-- Woodford (2003), p. 274: with the true `Ĉ = C`, the subjective forecast of the natural
rate is rational, `Ê_t r̂ⁿ_{t+k} = E_t r̂ⁿ_{t+k}`. -/
theorem rnfc_eq_E {𝔼 : ExpectationSystem Ω} {C : Matrix (Fin n) (Fin n) ℝ}
    {s e : ℕ → Fin n → Ω → ℝ} (h : StateLaw 𝔼 C s e) (gr : Fin n → ℝ) (t k : ℕ) :
    (fun ω => rnfc gr C s t k ω) = 𝔼.E t (fun ω => gr ⬝ᵥ sv s (t + k) ω) := by
  have e1 : (fun ω => gr ⬝ᵥ sv s (t + k) ω) = affRV 0 gr (s (t + k)) := by
    funext ω
    simp [affRV, dotProduct, sv]
  rw [e1, E_affRV_iter h]
  funext ω
  simp only [rnfc, affRV, dotProduct_mulVec, zero_add]
  rfl


/-- Woodford (2003), p. 274: at a fixed point every subjective forecast entering (2.29)–(2.30)
is rational: `Ê_t z_{t+m} = E_t z_{t+m}` for all `m ≥ 0` (current values are known). -/
theorem subj_eq_E {𝔼 : ExpectationSystem Ω} {C : Matrix (Fin n) (Fin n) ℝ}
    {s e : ℕ → Fin n → Ω → ℝ} (h : StateLaw 𝔼 C s e) {α β κ σ φπ φx πbar xbar ci : ℝ}
    {gr gi : Fin n → ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hΔ : taylorDelta σ κ φπ φx ≠ 0)
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ‖ρ‖ < 1)
    {Φ : Learning.Regression.Belief (Fin 3) (Fin n)} {z : ℕ → Fin 3 → Ω → ℝ}
    (hz : ∀ t, IS229 β σ gr Φ C s z t ∧ AS230 α β κ Φ C s z t ∧
      TaylorRule φπ φx πbar xbar ci gi s z t)
    (hfix : tMapP α β κ σ φπ φx (taylorConst φπ φx πbar xbar ci) gr gi C (Φ, C) = (Φ, C))
    (t m : ℕ) (j : Fin 3) :
    (fun ω => subj z Φ C s t m j ω) = 𝔼.E t (z (t + m) j) := by
  rcases m with _ | k
  · have hK := norm_lt_one_of_isEig_smul hC (a := β) (by rw [abs_le]; constructor <;> linarith)
    simp only [subj, ↓reduceIte, add_zero]
    rw [z_eq_affRV hβ0 hβ1 hα0 hα1 hΔ hK (hz t) j, E_affRV_of_known 𝔼 _ _ (h.1 t)]
  · simp only [subj, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel]
    exact fcast_eq_E h hβ0 hβ1 hα0 hα1 hΔ hC hz hfix t k j

/-- Woodford (2003), (2.24): the natural rate `r̂ⁿ_t = f_r′ s_t`. -/
def rnP (gr : Fin n → ℝ) (s : ℕ → Fin n → Ω → ℝ) (t : ℕ) : Ω → ℝ := fun ω => gr ⬝ᵥ sv s t ω

/-- Woodford (2003), p. 274: with a bounded state, the d.g.p. at a fixed point is bounded. -/
theorem z_bounded {α β κ σ φπ φx πbar xbar ci : ℝ}
    {gr gi : Fin n → ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hΔ : taylorDelta σ κ φπ φx ≠ 0) {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ‖ρ‖ < 1)
    {Φ : Learning.Regression.Belief (Fin 3) (Fin n)} {s : ℕ → Fin n → Ω → ℝ}
    (hsb : ∃ M, ∀ t j ω, |s t j ω| ≤ M) {z : ℕ → Fin 3 → Ω → ℝ}
    (hz : ∀ t, IS229 β σ gr Φ C s z t ∧ AS230 α β κ Φ C s z t ∧
      TaylorRule φπ φx πbar xbar ci gi s z t) :
    ∃ M, ∀ t j ω, |z t j ω| ≤ M := by
  have hK := norm_lt_one_of_isEig_smul hC (a := β) (by rw [abs_le]; constructor <;> linarith)
  obtain ⟨M, hM⟩ := affRV_bounded hsb
    (interceptP α β κ σ φπ φx (taylorConst φπ φx πbar xbar ci) Φ.1)
    (slopeP α β κ σ φπ φx gr gi Φ.2 C)
  refine ⟨M, fun t j ω => ?_⟩
  rw [z_eq_affRV hβ0 hβ1 hα0 hα1 hΔ hK (hz t) j]
  exact hM t j ω

/-- Woodford (2003), (2.24): with a bounded state the natural rate is bounded. -/
theorem rnP_bounded (gr : Fin n → ℝ) {s : ℕ → Fin n → Ω → ℝ}
    (hsb : ∃ M, ∀ t j ω, |s t j ω| ≤ M) : ∃ M, ∀ t ω, |rnP gr s t ω| ≤ M := by
  obtain ⟨M, hM⟩ := affRV_bounded (ι := Fin 1) hsb (fun _ => 0) (fun _ => gr)
  refine ⟨M, fun t ω => ?_⟩
  have := hM t 0 ω
  simpa [affRV, rnP, dotProduct, sv] using this

/-- Woodford (2003), (2.29) p. 273: **at the fixed point `(Φ̄, C)` the long-horizon demand rule
holds with rational expectations**, `x_t = E_t ∑ βᵏ[(1 − β)x_{t+k+1} − σ(î_{t+k} − π_{t+k+1} −
r̂ⁿ_{t+k})]` (bounded state). -/
theorem prestonIS_of_fixed {𝔼 : ExpectationSystem Ω} {C : Matrix (Fin n) (Fin n) ℝ}
    {s e : ℕ → Fin n → Ω → ℝ} (h : StateLaw 𝔼 C s e) (hsb : ∃ M, ∀ t j ω, |s t j ω| ≤ M)
    {α β κ σ φπ φx πbar xbar ci : ℝ} {gr gi : Fin n → ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hΔ : taylorDelta σ κ φπ φx ≠ 0)
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ‖ρ‖ < 1)
    {Φ : Learning.Regression.Belief (Fin 3) (Fin n)} {z : ℕ → Fin 3 → Ω → ℝ}
    (hz : ∀ t, IS229 β σ gr Φ C s z t ∧ AS230 α β κ Φ C s z t ∧
      TaylorRule φπ φx πbar xbar ci gi s z t)
    (hfix : tMapP α β κ σ φπ φx (taylorConst φπ φx πbar xbar ci) gr gi C (Φ, C) = (Φ, C)) :
    Learning.Preston.PrestonIS 𝔼.E β σ (fun t => z t 1) (fun t => z t 0) (fun t => z t 2)
      (rnP gr s) := by
  obtain ⟨Mz, hMz⟩ := z_bounded hβ0 hβ1 hα0 hα1 hΔ hC hsb hz
  obtain ⟨Mr, hMr⟩ := rnP_bounded gr hsb
  intro t
  funext ω
  have hdom : ∀ k ω', |β ^ k * ((1 - β) * z (t + k + 1) 1 ω' -
      σ * (z (t + k) 2 ω' - z (t + k + 1) 0 ω' - rnP gr s (t + k) ω'))| ≤
      β ^ k * (|1 - β| * Mz + |σ| * (Mz + Mz + Mr)) := by
    intro k ω'
    rw [abs_mul, abs_pow, abs_of_pos hβ0]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0.le k)
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hMz _ _ _) (abs_nonneg _)
    · rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
        (add_le_add (hMz _ _ _) (hMz _ _ _))) (hMr _ _))
  beta_reduce
  rw [𝔼.E_tsum hβ0.le hβ1 hdom t ω, (hz t).1 ω]
  congr 1
  funext k
  have e : (fun ω' => β ^ k * ((1 - β) * z (t + k + 1) 1 ω' -
      σ * (z (t + k) 2 ω' - z (t + k + 1) 0 ω' - rnP gr s (t + k) ω'))) =
      β ^ k • ((1 - β) • z (t + k + 1) 1 - σ • (z (t + k) 2 - z (t + k + 1) 0 -
        rnP gr s (t + k))) := by
    funext ω'
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [e, map_smul, map_sub, map_smul, map_smul, map_sub, map_sub]
  have e1 : 𝔼.E t (z (t + k + 1) 1) ω = subj z Φ C s t (k + 1) 1 ω :=
    (congrFun (subj_eq_E h hβ0 hβ1 hα0 hα1 hΔ hC hz hfix t (k + 1) 1) ω).symm
  have e2 : 𝔼.E t (z (t + k + 1) 0) ω = subj z Φ C s t (k + 1) 0 ω :=
    (congrFun (subj_eq_E h hβ0 hβ1 hα0 hα1 hΔ hC hz hfix t (k + 1) 0) ω).symm
  have e3 : 𝔼.E t (z (t + k) 2) ω = subj z Φ C s t k 2 ω :=
    (congrFun (subj_eq_E h hβ0 hβ1 hα0 hα1 hΔ hC hz hfix t k 2) ω).symm
  have e4 : 𝔼.E t (rnP gr s (t + k)) ω = rnfc gr C s t k ω :=
    (congrFun (rnfc_eq_E h gr t k) ω).symm
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, e1, e2, e3, e4]

/-- Woodford (2003), (2.30) p. 273: **at the fixed point the long-horizon inflation equation
holds with rational expectations**, `π_t = E_t ∑ (αβ)ᵏ[κx_{t+k} + (1 − α)βπ_{t+k+1}]`. -/
theorem prestonAS_of_fixed {𝔼 : ExpectationSystem Ω} {C : Matrix (Fin n) (Fin n) ℝ}
    {s e : ℕ → Fin n → Ω → ℝ} (h : StateLaw 𝔼 C s e) (hsb : ∃ M, ∀ t j ω, |s t j ω| ≤ M)
    {α β κ σ φπ φx πbar xbar ci : ℝ} {gr gi : Fin n → ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hΔ : taylorDelta σ κ φπ φx ≠ 0)
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ‖ρ‖ < 1)
    {Φ : Learning.Regression.Belief (Fin 3) (Fin n)} {z : ℕ → Fin 3 → Ω → ℝ}
    (hz : ∀ t, IS229 β σ gr Φ C s z t ∧ AS230 α β κ Φ C s z t ∧
      TaylorRule φπ φx πbar xbar ci gi s z t)
    (hfix : tMapP α β κ σ φπ φx (taylorConst φπ φx πbar xbar ci) gr gi C (Φ, C) = (Φ, C)) :
    Learning.Preston.PrestonAS 𝔼.E α β κ (fun t => z t 1) (fun t => z t 0) := by
  obtain ⟨Mz, hMz⟩ := z_bounded hβ0 hβ1 hα0 hα1 hΔ hC hsb hz
  have hab0 : 0 ≤ α * β := mul_nonneg hα0 hβ0.le
  have hab1 : α * β < 1 := by nlinarith
  intro t
  funext ω
  have hdom : ∀ k ω', |(α * β) ^ k * (κ * z (t + k) 1 ω' + (1 - α) * β * z (t + k + 1) 0 ω')| ≤
      (α * β) ^ k * (|κ| * Mz + |(1 - α) * β| * Mz) := by
    intro k ω'
    rw [abs_mul, abs_pow, abs_of_nonneg hab0]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hab0 k)
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hMz _ _ _) (abs_nonneg _)
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hMz _ _ _) (abs_nonneg _)
  beta_reduce
  rw [𝔼.E_tsum hab0 hab1 hdom t ω, (hz t).2.1 ω]
  congr 1
  funext k
  have e : (fun ω' => (α * β) ^ k * (κ * z (t + k) 1 ω' + (1 - α) * β * z (t + k + 1) 0 ω')) =
      (α * β) ^ k • (κ • z (t + k) 1 + ((1 - α) * β) • z (t + k + 1) 0) := by
    funext ω'
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [e, map_smul, map_add, map_smul, map_smul]
  have e1 : 𝔼.E t (z (t + k) 1) ω = subj z Φ C s t k 1 ω :=
    (congrFun (subj_eq_E h hβ0 hβ1 hα0 hα1 hΔ hC hz hfix t k 1) ω).symm
  have e2 : 𝔼.E t (z (t + k + 1) 0) ω = subj z Φ C s t (k + 1) 0 ω :=
    (congrFun (subj_eq_E h hβ0 hβ1 hα0 hα1 hΔ hC hz hfix t (k + 1) 0) ω).symm
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, e1, e2]

/-- Woodford (2003), p. 274: **"the fixed point `(Φ̄, C)` of this mapping is an r.e.e."**: with
a bounded state following (2.24) with stationary `C`, if inflation, output gap and interest rate
follow Preston's long-horizon rules and the Taylor rule at every date under the beliefs of a
fixed point `(Φ̄, C)` of the `T`-map, then under rational expectations they satisfy the
equilibrium conditions of the basic neo-Wicksellian model: the IS relation (2.17)
`x_t = E_t x_{t+1} − σ(î_t − E_t π_{t+1} − r̂ⁿ_t)`, the Phillips curve (2.16)
`π_t = κx_t + βE_t π_{t+1}`, and the Taylor rule (1.14). -/
theorem fixed_isREE {𝔼 : ExpectationSystem Ω} {C : Matrix (Fin n) (Fin n) ℝ}
    {s e : ℕ → Fin n → Ω → ℝ} (h : StateLaw 𝔼 C s e) (hsb : ∃ M, ∀ t j ω, |s t j ω| ≤ M)
    {α β κ σ φπ φx πbar xbar ci : ℝ} {gr gi : Fin n → ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hΔ : taylorDelta σ κ φπ φx ≠ 0)
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ‖ρ‖ < 1)
    {Φ : Learning.Regression.Belief (Fin 3) (Fin n)} {z : ℕ → Fin 3 → Ω → ℝ}
    (hz : ∀ t, IS229 β σ gr Φ C s z t ∧ AS230 α β κ Φ C s z t ∧
      TaylorRule φπ φx πbar xbar ci gi s z t)
    (hfix : tMapP α β κ σ φπ φx (taylorConst φπ φx πbar xbar ci) gr gi C (Φ, C) = (Φ, C)) :
    Learning.Preston.OneStepIS 𝔼.E σ (fun t => z t 1) (fun t => z t 0) (fun t => z t 2)
        (rnP gr s) ∧
      Learning.Preston.OneStepAS 𝔼.E β κ (fun t => z t 1) (fun t => z t 0) ∧
      ∀ t, TaylorRule φπ φx πbar xbar ci gi s z t := by
  have hK := norm_lt_one_of_isEig_smul hC (a := β) (by rw [abs_le]; constructor <;> linarith)
  obtain ⟨Mz, hMz⟩ := z_bounded hβ0 hβ1 hα0 hα1 hΔ hC hsb hz
  obtain ⟨Mr, hMr⟩ := rnP_bounded gr hsb
  have hzb : ∀ j, BoundedProc (fun t => z t j) := fun j => ⟨Mz, fun t ω => hMz t j ω⟩
  have hza : ∀ j, 𝔼.Adapted (fun t => z t j) := fun j t => by
    simp only
    rw [z_eq_affRV hβ0 hβ1 hα0 hα1 hΔ hK (hz t) j, E_affRV_of_known 𝔼 _ _ (h.1 t)]
  have hra : 𝔼.Adapted (rnP gr s) := fun t => by
    have e1 : rnP gr s t = affRV 0 gr (s t) := by
      funext ω
      simp [affRV, rnP, dotProduct, sv]
    rw [e1, E_affRV_of_known 𝔼 _ _ (h.1 t)]
  refine ⟨(Learning.Preston.preston_IS_iff 𝔼 hβ0 hβ1 (hzb 1) (hzb 0) (hzb 2) ⟨Mr, hMr⟩
      (hza 2) hra).mp (prestonIS_of_fixed h hsb hβ0 hβ1 hα0 hα1 hΔ hC hz hfix),
    (Learning.Preston.preston_AS_iff 𝔼 hα0 hα1 hβ0 hβ1 (hzb 1) (hzb 0) (hza 1)).mp
      (prestonAS_of_fixed h hsb hβ0 hβ1 hα0 hα1 hΔ hC hz hfix), fun t => (hz t).2.2⟩

end Woodford.NeoWicksellianFramework.Prop410REE
