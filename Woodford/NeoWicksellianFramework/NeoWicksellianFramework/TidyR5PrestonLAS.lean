/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.TidyR5Lyapunov
import NeoWicksellianFramework.TidyR5ComplexRegion

/-!
# Proposition 4.10 for the nonlinear E-stability equation (2.20)

Woodford (2003), *Interest and Prices*, Chapter 4, §2.3, Proposition 4.10, p. 274, with the
book's definition of E-stability (pp. 264–265): local stability of the r.e.e. as a rest point of
the **nonlinear** differential equation `θ̇ = T(θ) − θ` (2.20) for Preston's `T`-map (which is not
affine in the beliefs `Ĉ`).

* Stability: `PrestonLearning.eStableAt_tVecP_iff` and `TidyR5Lyapunov.isLAS_of_eStableAt`
  (Lyapunov's indirect method).
* Instability, exactly and including the boundary case: the set of beliefs with `Ĉ = C` is
  invariant, and on it (2.20) is affine with matrix `DT_Φ = blockdiag(DT₀, H)`
  (`PrestonLearning.tVecP_inl_eq`): `liftSol`, `isESol_liftSol` turn every solution of the
  linear equation with matrix `DT_Φ` into a solution of the nonlinear (2.20); so local
  attraction of the r.e.e. forces local attraction of the linear equation
  (`attracting_of_isLAS`), hence E-stability of `DT_Φ` (`eStable_of_attracting`), even when an
  eigenvalue of `DT_Φ − I` has zero real part.
* **`isLAS_iff_eStable`**: for any stationary `C`, the r.e.e. is a locally asymptotically stable
  rest point of the nonlinear (2.20) iff `DT_Φ` is E-stable;
  **`prop_4_10_LAS`**: with real eigenvalues of `C`, iff the Taylor principle (2.7) holds;
  **`prop_4_10_LAS_complex`**: for any stationary `C`, iff (2.7) and the block conditions
  `HurwitzC(B̃(ρ))` at the non-real eigenvalues of `C`.

The stochastic-approximation results the book cites from Evans and Honkapohja are not formalised.
-/

namespace Woodford.NeoWicksellianFramework.TidyR5PrestonLAS

open Matrix Filter Topology Determinacy2 PrestonLearning TidyR5EStabilityODE TidyR5Lyapunov
open Determinacy2Learning (EStable EStableAt)

variable {n : ℕ}

/-- Woodford (2003), p. 266: **local attraction of the linear(ised) equation implies
E-stability** (the scaling argument of `TidyR5EStabilityODE.eStable_iff_locallyStable`, restated
with only the attraction hypothesis). -/
theorem eStable_of_attracting {ι : Type*} [Fintype ι] [DecidableEq ι] {J : Matrix ι ι ℝ}
    {θs : ι → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hconv : ∀ θ, IsESol (linT J θs) θ → ‖θ 0 - θs‖ < δ → Tendsto θ atTop (𝓝 θs)) :
    EStable J := by
  refine eStable_of_tendsto (θs := θs) fun θ h => ?_
  set c : ℝ := δ / (2 * (‖θ 0 - θs‖ + 1)) with hc
  have hc0 : 0 < c := by positivity
  have hsol := isESol_scale h c
  have hsmall : ‖(θs + c • (θ 0 - θs)) - θs‖ < δ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc0, hc]
    have hn := norm_nonneg (θ 0 - θs)
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have t := hconv _ hsol hsmall
  have t2 := (t.sub_const θs).const_smul c⁻¹
  simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc0.ne', one_smul,
    sub_self, smul_zero] at t2
  simpa using t2.const_add θs

/-- Woodford (2003), p. 275: the belief with `Ĉ = C` and belief part `φ` (vectorised). -/
def liftSol (C : Matrix (Fin n) (Fin n) ℝ) (φ : ℝ → Fin 3 ⊕ (Fin n × Fin 3) → ℝ) :
    ℝ → IdxP n → ℝ :=
  fun τ => Sum.elim (φ τ) (vec C)

/-- Woodford (2003), p. 275 ("if private agents have beliefs `Ĉ = C` …"): **on the invariant
set `Ĉ = C` the nonlinear equation (2.20) for Preston's `T`-map is the affine equation with
matrix `DT_Φ`**: if `w̄ = k + DT_Φ w̄` and `φ` solves `φ̇ = w̄ + DT_Φ(φ − w̄) − φ`, then
`(φ, C)` solves (2.20). -/
theorem isESol_liftSol {α β κ σ φπ φx c : ℝ} {gr gi : Fin n → ℝ}
    {C : Matrix (Fin n) (Fin n) ℝ} {wb : Fin 3 ⊕ (Fin n × Fin 3) → ℝ}
    (hwb : wb = Learning.Regression.vecBelief (interceptP α β κ σ φπ φx c 0,
        slopeP α β κ σ φπ φx gr gi 0 C * C) + dTP α β κ σ φπ φx C *ᵥ wb)
    {φ : ℝ → Fin 3 ⊕ (Fin n × Fin 3) → ℝ} (hφ : IsESol (linT (dTP α β κ σ φπ φx C) wb) φ) :
    IsESol (tVecP α β κ σ φπ φx c gr gi C) (liftSol C φ) := by
  intro τ
  refine hasDerivAt_pi.2 fun x => ?_
  rcases x with a | b
  · have h := hasDerivAt_pi.1 (hφ τ) a
    have e := congrFun (tVecP_inl_eq α β κ σ φπ φx c gr gi C (φ τ)) a
    simp only [Function.comp_apply] at e
    have hlin : linT (dTP α β κ σ φπ φx C) wb (φ τ) =
        Learning.Regression.vecBelief (interceptP α β κ σ φπ φx c 0,
          slopeP α β κ σ φπ φx gr gi 0 C * C) + dTP α β κ σ φπ φx C *ᵥ φ τ := by
      rw [linT, mulVec_sub]
      nth_rewrite 1 [hwb]
      abel
    rw [hlin] at h
    convert h using 1
    · rfl
    · change tVecP α β κ σ φπ φx c gr gi C (Sum.elim (φ τ) (vec C)) (Sum.inl a) - φ τ a = _
      rw [e, Pi.sub_apply]
  · have e := congrFun (tVecP_inr α β κ σ φπ φx c gr gi C (Sum.elim (φ τ) (vec C))) b
    simp only [Function.comp_apply] at e
    simp only [liftSol, Pi.sub_apply, Sum.elim_inr, e, sub_self]
    exact hasDerivAt_const τ _

/-- Woodford (2003), p. 264: **if the r.e.e. of Preston's `T`-map is a locally asymptotically
stable rest point of the nonlinear (2.20), then the linear equation with matrix `DT_Φ` is
locally attracting** (through the invariant set `Ĉ = C`). -/
theorem attracting_of_isLAS {α β κ σ φπ φx c : ℝ} {gr gi : Fin n → ℝ}
    {C : Matrix (Fin n) (Fin n) ℝ} {v : IdxP n → ℝ}
    (hfix : tVecP α β κ σ φπ φx c gr gi C v = v)
    (h : IsLAS (tVecP α β κ σ φπ φx c gr gi C) v) :
    ∃ δ > 0, ∀ φ, IsESol (linT (dTP α β κ σ φπ φx C) (v ∘ Sum.inl)) φ →
      ‖φ 0 - v ∘ Sum.inl‖ < δ → Tendsto φ atTop (𝓝 (v ∘ Sum.inl)) := by
  obtain ⟨hinr, -⟩ := unvecP_snd_of_fixed hfix
  have hv : v = Sum.elim (v ∘ Sum.inl) (vec C) := by
    funext x
    rcases x with a | b
    · rfl
    · exact congrFun hinr b
  have hwb : v ∘ Sum.inl = Learning.Regression.vecBelief (interceptP α β κ σ φπ φx c 0,
      slopeP α β κ σ φπ φx gr gi 0 C * C) + dTP α β κ σ φπ φx C *ᵥ (v ∘ Sum.inl) := by
    have e := tVecP_inl_eq α β κ σ φπ φx c gr gi C (v ∘ Sum.inl)
    rw [← hv, hfix] at e
    exact e
  obtain ⟨-, δ, hδ, hconv⟩ := h
  refine ⟨δ, hδ, fun φ hφ h0 => ?_⟩
  have hsol := isESol_liftSol hwb hφ
  have hn : ‖liftSol C φ 0 - v‖ < δ := by
    have heq : liftSol C φ 0 - v = Sum.elim (φ 0 - v ∘ Sum.inl) 0 := by
      conv_lhs => rw [hv]
      funext x
      rcases x with a | b <;> simp [liftSol]
    rw [heq]
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun x => ?_) h0
    rcases x with a | b
    · exact norm_le_pi_norm (φ 0 - v ∘ Sum.inl) a
    · simp
  have t := hconv _ (isFwdSol_of_isESol hsol) hn
  have hc : Continuous fun f : IdxP n → ℝ => f ∘ Sum.inl :=
    continuous_pi fun a => continuous_apply _
  have t2 := (hc.tendsto v).comp t
  simpa [Function.comp_def, liftSol] using t2

/-- Woodford (2003), **Proposition 4.10 with the book's definition of E-stability**: for any
stationary `C` (`0 < β < 1`, `0 ≤ α < 1`), an r.e.e. `v` of Preston's `T`-map is a locally
asymptotically stable rest point of the **nonlinear** equation `θ̇ = T(θ) − θ` (2.20) iff
`DT_Φ = blockdiag(DT₀, H)` is E-stable (every eigenvalue of `DT_Φ − I` has negative real part).
No genericity assumption: zero real parts are covered. -/
theorem isLAS_iff_eStable {α β κ σ φπ φx c : ℝ} {gr gi : Fin n → ℝ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ‖ρ‖ < 1)
    {v : IdxP n → ℝ} (hfix : tVecP α β κ σ φπ φx c gr gi C v = v) :
    IsLAS (tVecP α β κ σ φπ φx c gr gi C) v ↔ EStable (dTP α β κ σ φπ φx C) := by
  have hab : |α * β| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  have hb : |β| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have hiff := eStableAt_tVecP_iff hfix (Prop410.det_one_sub_smul_ne_zero hC hab)
    (Prop410.det_one_sub_smul_ne_zero hC hb)
  constructor
  · intro h
    obtain ⟨δ, hδ, hconv⟩ := attracting_of_isLAS hfix h
    exact eStable_of_attracting hδ hconv
  · intro h
    exact isLAS_of_eStableAt (hiff.mpr h)

/-- Woodford (2003), **Proposition 4.10** (p. 274) **for the nonlinear E-stability equation**:
with every eigenvalue of `C` real and inside the unit circle, the r.e.e. of Preston's `T`-map
is a locally asymptotically stable rest point of `θ̇ = T(θ) − θ` (2.20) iff the Taylor
principle (2.7) holds (`0 < β < 1`, `0 ≤ α < 1`, `κ, σ > 0`, `φ_π, φ_x ≥ 0`). -/
theorem prop_4_10_LAS {α β κ σ φπ φx c : ℝ} {gr gi : Fin n → ℝ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hπ : 0 ≤ φπ)
    (hx : 0 ≤ φx) {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ρ.im = 0 ∧ ‖ρ‖ < 1)
    {v : IdxP n → ℝ} (hfix : tVecP α β κ σ φπ φx c gr gi C v = v) :
    IsLAS (tVecP α β κ σ φπ φx c gr gi C) v ↔ 1 < taylorLHS β κ φπ φx := by
  rw [isLAS_iff_eStable hα0 hα1 hβ0 hβ1 (fun ρ hρ => (hC ρ hρ).2) hfix]
  exact Prop410.eStable_dTP_iff hα0 hα1 hβ0 hβ1 hκ hσ hπ hx hC

/-- Woodford (2003), **Proposition 4.10 for any stationary `C`, nonlinear (2.20)**: the r.e.e.
is a locally asymptotically stable rest point of `θ̇ = T(θ) − θ` iff (2.7) holds and
`HurwitzC(B̃(ρ))` holds at every non-real eigenvalue `ρ` of `C`. -/
theorem prop_4_10_LAS_complex {α β κ σ φπ φx c : ℝ} {gr gi : Fin n → ℝ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hπ : 0 ≤ φπ)
    (hx : 0 ≤ φx) {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ‖ρ‖ < 1)
    {v : IdxP n → ℝ} (hfix : tVecP α β κ σ φπ φx c gr gi C v = v) :
    IsLAS (tVecP α β κ σ φπ φx c gr gi C) v ↔
      1 < taylorLHS β κ φπ φx ∧
        ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ρ.im ≠ 0 →
          TidyR5ComplexRegion.HurwitzC (TidyR5ComplexRegion.bTilC α β κ σ φπ φx ρ) := by
  have hab : |α * β| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  have hb : |β| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  rw [isLAS_iff_eStable hα0 hα1 hβ0 hβ1 hC hfix, ← eStableAt_tVecP_iff hfix
    (Prop410.det_one_sub_smul_ne_zero hC hab) (Prop410.det_one_sub_smul_ne_zero hC hb)]
  exact TidyR5ComplexRegion.prop_4_10_complex hα0 hα1 hβ0 hβ1 hκ hσ hπ hx hC hfix

end Woodford.NeoWicksellianFramework.TidyR5PrestonLAS
