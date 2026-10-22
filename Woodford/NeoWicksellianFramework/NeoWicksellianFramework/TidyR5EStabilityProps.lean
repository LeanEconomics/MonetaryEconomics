/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.TidyR5EStabilityODE
import NeoWicksellianFramework.TidyR5ComplexRegion

/-!
# Propositions 4.8–4.10 as statements about the E-stability differential equation

Woodford (2003), *Interest and Prices*, Chapter 4, §2.3: Propositions 4.8 (p. 266), 4.9
(p. 271) and 4.10 (p. 274), with E-stability read as in the book's definition (pp. 264–265): the
behaviour of the solutions of `θ̇ = T(θ) − θ` (2.20). Via the module TidyR5EStabilityODE:

* `prop_4_8_ode`, `prop_4_8_locallyStable`: for the sample-mean `T`-map (2.19), which is affine,
  every solution of the actual equation (2.20) converges to the s.c.e. `z̄` (from every initial
  belief) iff the Taylor principle (2.7) holds; equivalently `z̄` is a locally stable rest point.
* `prop_4_9_ode`: for the regression `T`-map (affine in the vectorised beliefs), every solution
  of (2.20) converges to the r.e.e. iff (2.7), for any stationary `C`.
* `prop_4_10_ode` (real eigenvalues of `C`) and `prop_4_10_complex_ode` (any stationary `C`):
  Preston's `T`-map is not affine in `Ĉ`; every solution of (2.20) linearised at the r.e.e.
  converges iff (2.7) (respectively iff (2.7) and the block conditions `HurwitzC(B̃(ρ))` at the
  non-real eigenvalues of `C`).

The stochastic-approximation results the book cites from Evans and Honkapohja (pp. 265–266) are
not formalised.
-/

namespace Woodford.NeoWicksellianFramework.TidyR5EStabilityProps

open Matrix Filter Topology Determinacy2 TidyR5EStabilityODE PrestonLearning
open Determinacy2Learning (EStable EStableAt Tmap prop_4_8)

/-- Woodford (2003), **Proposition 4.8** (p. 266) **as a statement about (2.20)**: for the
Bullard–Mitra temporary equilibrium and the sample-mean `T`-map (2.19), every solution of
`żᵉ = T(zᵉ) − zᵉ` converges to the s.c.e. `z̄`, from every initial belief, iff the Taylor
principle (2.7) holds. -/
theorem prop_4_8_ode {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ)
    (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (zbar : Fin 2 → ℝ) :
    (∀ θ, IsESol (Tmap (taylorB β σ κ φπ φx) zbar) θ → Tendsto θ atTop (𝓝 zbar)) ↔
      1 < taylorLHS β κ φπ φx := by
  rw [← prop_4_8 hβ0 hβ1 hσ hκ hφπ hφx, eStable_iff_tendsto _ zbar]
  rfl

/-- Woodford (2003), **Proposition 4.8** with the book's definition (p. 264): `z̄` is a locally
stable rest point of (2.20) iff (2.7) holds. -/
theorem prop_4_8_locallyStable {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (zbar : Fin 2 → ℝ) :
    IsLocallyStable (Tmap (taylorB β σ κ φπ φx) zbar) zbar ↔ 1 < taylorLHS β κ φπ φx := by
  rw [← prop_4_8 hβ0 hβ1 hσ hκ hφπ hφx, eStable_iff_locallyStable _ zbar]
  rfl

/-- Woodford (2003), **Proposition 4.9** (p. 271) **as a statement about (2.20)**: with
regression learning on a stationary state, every solution of the E-stability equation for the
(vectorised, affine) regression `T`-map converges to the r.e.e. `Φ̄`, from every initial belief,
iff the Taylor principle (2.7) holds. -/
theorem prop_4_9_ode {β σ κ φπ φx : ℝ} {S : Type*} [Fintype S] (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hπ : 0 ≤ φπ) (hx : 0 ≤ φx) (zbar : Fin 2 → ℝ)
    (g : S → ℝ) (C : Matrix S S ℝ)
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ‖ρ‖ < 1)
    {Φ : Learning.Regression.Belief (Fin 2) S}
    (hfix : Learning.Regression.tMap zbar (taylorB β σ κ φπ φx) (taylorb σ κ φπ φx) g C Φ = Φ) :
    (∀ θ, IsESol (Learning.Regression.tVec zbar (taylorB β σ κ φπ φx) (taylorb σ κ φπ φx) g C) θ →
        Tendsto θ atTop (𝓝 (Learning.Regression.vecBelief Φ))) ↔
      1 < taylorLHS β κ φπ φx := by
  classical
  have hfix' : Learning.Regression.tVec zbar (taylorB β σ κ φπ φx) (taylorb σ κ φπ φx) g C
      (Learning.Regression.vecBelief Φ) = Learning.Regression.vecBelief Φ := by
    rw [Learning.Regression.tVec, Learning.Regression.unvecBelief_vecBelief, hfix]
  rw [← eStable_iff_tendsto_affine (Learning.Regression.tVec_eq zbar _ _ g C) hfix',
    Learning.BullardMitra.prop_4_9 hβ0 hβ1 hκ hσ hπ hx C hC]

/-- Woodford (2003), p. 274: at a fixed point of Preston's `T`-map with stationary `C`, the map
is differentiable (Cramer's rule, `PrestonLearning.differentiableAt_tVecP`). -/
theorem differentiableAt_tVecP_of_fixed {n : ℕ} {α β κ σ φπ φx c : ℝ} {gr gi : Fin n → ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ‖ρ‖ < 1)
    {v : IdxP n → ℝ} (hfix : tVecP α β κ σ φπ φx c gr gi C v = v) :
    DifferentiableAt ℝ (tVecP α β κ σ φπ φx c gr gi C) v := by
  have hab : |α * β| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  have hb : |β| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨-, hv⟩ := unvecP_snd_of_fixed hfix
  refine differentiableAt_tVecP α β κ σ φπ φx c gr gi C v ?_ ?_
  · rw [hv]
    exact Prop410.det_one_sub_smul_ne_zero hC hab
  · rw [hv]
    exact Prop410.det_one_sub_smul_ne_zero hC hb

/-- Woodford (2003), **Proposition 4.10** (p. 274) **as a statement about (2.20)**: with every
eigenvalue of `C` real and inside the unit circle, every solution of the E-stability equation
linearised at an r.e.e. `v` of Preston's `T`-map converges to `v`, from every initial belief,
iff the Taylor principle (2.7) holds. -/
theorem prop_4_10_ode {n : ℕ} {α β κ σ φπ φx c : ℝ} {gr gi : Fin n → ℝ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hπ : 0 ≤ φπ)
    (hx : 0 ≤ φx) {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ρ.im = 0 ∧ ‖ρ‖ < 1)
    {v : IdxP n → ℝ} (hfix : tVecP α β κ σ φπ φx c gr gi C v = v) :
    (∀ θ, IsESol (linT (LinearMap.toMatrix'
        (fderiv ℝ (tVecP α β κ σ φπ φx c gr gi C) v : (IdxP n → ℝ) →ₗ[ℝ] (IdxP n → ℝ))) v) θ →
        Tendsto θ atTop (𝓝 v)) ↔ 1 < taylorLHS β κ φπ φx := by
  have hd := differentiableAt_tVecP_of_fixed hα0 hα1 hβ0 hβ1 (fun ρ hρ => (hC ρ hρ).2) hfix
  rw [← Prop410.prop_4_10 hα0 hα1 hβ0 hβ1 hκ hσ hπ hx hC hfix, eStableAt_iff_ode]
  exact ⟨fun h => ⟨hfix, hd, h⟩, fun h => h.2.2⟩

/-- Woodford (2003), **Proposition 4.10 for any stationary `C`, as a statement about (2.20)**:
every solution of the E-stability equation linearised at an r.e.e. `v` of Preston's `T`-map
converges to `v` iff (2.7) holds and `HurwitzC(B̃(ρ))` holds at every non-real eigenvalue `ρ` of
`C` (`TidyR5ComplexRegion.prop_4_10_complex`). -/
theorem prop_4_10_complex_ode {n : ℕ} {α β κ σ φπ φx c : ℝ} {gr gi : Fin n → ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hπ : 0 ≤ φπ) (hx : 0 ≤ φx) {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ‖ρ‖ < 1)
    {v : IdxP n → ℝ} (hfix : tVecP α β κ σ φπ φx c gr gi C v = v) :
    (∀ θ, IsESol (linT (LinearMap.toMatrix'
        (fderiv ℝ (tVecP α β κ σ φπ φx c gr gi C) v : (IdxP n → ℝ) →ₗ[ℝ] (IdxP n → ℝ))) v) θ →
        Tendsto θ atTop (𝓝 v)) ↔
      1 < taylorLHS β κ φπ φx ∧
        ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ρ.im ≠ 0 →
          TidyR5ComplexRegion.HurwitzC (TidyR5ComplexRegion.bTilC α β κ σ φπ φx ρ) := by
  have hd := differentiableAt_tVecP_of_fixed hα0 hα1 hβ0 hβ1 hC hfix
  rw [← TidyR5ComplexRegion.prop_4_10_complex hα0 hα1 hβ0 hβ1 hκ hσ hπ hx hC hfix,
    eStableAt_iff_ode]
  exact ⟨fun h => ⟨hfix, hd, h⟩, fun h => h.2.2⟩

end Woodford.NeoWicksellianFramework.TidyR5EStabilityProps
