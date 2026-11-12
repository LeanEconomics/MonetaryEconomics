/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.SimplestModel
import NewKeynesianSelection.LowerBound
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# E-stability (Evans–Honkapohja) and the selection of §16.10.7

Cochrane (2023), Chapter 16, §16.10.7, pp. 394–395: "McCallum … claim that applying the
e-stability concept in Evans and Honkapohja (2001) … the active, `Π*` equilibrium of Figure 16.2
is learnable, while the passive `Π_L` equilibrium … [is] not"; Cochrane's reply that `φ` is not
identified and hence not learnable.

E-stability is defined as in Woodford (2003), Ch. 4, p. 266 (restated from the Woodford Chapter 4
project, modules KroneckerSpectrum and Determinacy2Learning): a self-consistent equilibrium `θ̄`
of the T-map is E-stable when every complex eigenvalue of `DT(θ̄) − I` has negative real part
(`EStable`, `EStableAt`).

## Main results

* Linear algebra: `isEig_diag2_iff`, `eStable_diag2_iff`, `isEig_one_iff`, `eStable_one_iff`;
  the scalar notion `EStableAt1` is the Woodford notion for the lifted map (`eStableAt_lift_iff`).
* The linear model (16.1)–(16.2) with AR(1) `u` and the MSV perceived law `π_t = a + b u_t`:
  `E_plm`, `tempEq_iff` (the actual law of motion is `tMap`), `tMap_fixed_iff` (the unique
  self-consistent equilibrium is the MSV solution (16.9), `SimplestModel.ar1Pi`),
  `msv_eStable_iff` (E-stable iff `1/φ < 1` and `η/φ < 1`), `msv_eStable_iff_pos` (for `φ > 0`,
  `η < 1`: E-stable iff `φ > 1`), `active_eStable`, `passive_not_eStable` (McCallum's claim in
  the linear model) and the precision `negative_passive_eStable` (`−1 < φ < 0`: indeterminate
  but E-stable).
* Cochrane's objection made exact: `msv_reparam`, `eStability_not_identified` — every observed
  MSV equilibrium is generated both by an E-stable and by a non-E-stable policy rule, with the
  same inflation and interest rate.
* The nonlinear model of Figure 16.2 under steady-state learning: `tempEqNL_iff` (temporary
  equilibrium `Φ(Π_t) = Πᵉ`), `tmap_exists` (the T-map is the local inverse of `Φ`),
  `hasDerivAt_tmap`, `steady_eStable_iff` (E-stable iff `1/Φ′(Π̄) < 1`), `target_eStable`,
  `lower_not_eStable`, `mccallum_claim`, `tangency_not_eStable`.
* The E-stability differential equation `θ̇ = T(θ) − θ` (`IsESol1`): `esol_linear_eq`,
  `esol_linear_tendsto_iff` (linear: every solution converges iff `T′ < 1`), and for the
  nonlinear map `eStable_local_convergence` (`T′ < 1`: every solution starting near `θ̄`
  converges) and `unstable_no_convergence` (`T′ > 1`: a solution converging to `θ̄` is
  eventually equal to it).
-/

namespace Cochrane.NewKeynesianSelection.TidyR6EStability

open Matrix Filter Topology

/-! ## E-stability, restated from the Woodford Chapter 4 project -/

/-- Restated from the Woodford Chapter 4 project (module KroneckerSpectrum), for Cochrane (2023),
§16.10.7, p. 394: `μ` is a complex eigenvalue of the square complex matrix `M`. -/
def IsEig {m : Type*} [Fintype m] (M : Matrix m m ℂ) (μ : ℂ) : Prop :=
  ∃ v : m → ℂ, v ≠ 0 ∧ M *ᵥ v = μ • v

/-- Restated from the Woodford Chapter 4 project, for Cochrane (2023), §16.10.7, p. 394: `μ` is
an eigenvalue of `M` iff `det (μ I − M) = 0`. -/
theorem isEig_iff_det {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ) (μ : ℂ) :
    IsEig M μ ↔ (μ • (1 : Matrix m m ℂ) - M).det = 0 := by
  rw [← exists_mulVec_eq_zero_iff]
  unfold IsEig
  refine exists_congr fun v => and_congr_right fun _ => ?_
  rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero, eq_comm]

/-- Restated from the Woodford Chapter 4 project (module Determinacy2Learning), for Cochrane
(2023), §16.10.7, p. 394, and Woodford (2003), p. 266: a self-consistent equilibrium with
Jacobian `DT` is E-stable when every eigenvalue of `DT − I` has negative real part. -/
def EStable {ι : Type*} [Fintype ι] [DecidableEq ι] (DT : Matrix ι ι ℝ) : Prop :=
  ∀ ν : ℂ, IsEig ((DT - 1).map Complex.ofReal) ν → ν.re < 0

/-- Restated from the Woodford Chapter 4 project, for Cochrane (2023), §16.10.7, p. 394: `ν` is
an eigenvalue of `DT − I` iff `ν + 1` is an eigenvalue of `DT`. -/
theorem isEig_sub_one_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (ν : ℂ) :
    IsEig ((M - 1).map Complex.ofReal) ν ↔ IsEig (M.map Complex.ofReal) (ν + 1) := by
  rw [isEig_iff_det, isEig_iff_det]
  have h : (M - 1).map Complex.ofReal = M.map Complex.ofReal - 1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [h, add_smul, one_smul]
  congr! 2
  abel

/-- Restated from the Woodford Chapter 4 project, for Cochrane (2023), §16.10.7, p. 394:
E-stability means every eigenvalue of `DT` has real part less than one. -/
theorem eStable_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) :
    EStable M ↔ ∀ μ : ℂ, IsEig (M.map Complex.ofReal) μ → μ.re < 1 := by
  constructor
  · intro h μ hμ
    have := h (μ - 1) ((isEig_sub_one_iff M _).mpr (by simpa using hμ))
    simpa using this
  · intro h ν hν
    have := h (ν + 1) ((isEig_sub_one_iff M ν).mp hν)
    simp only [Complex.add_re, Complex.one_re] at this
    linarith

/-- Restated from the Woodford Chapter 4 project, for Cochrane (2023), §16.10.7, p. 394: a rest
point `x̄` of `ẋ = T(x) − x`, with `T` differentiable at `x̄`, is E-stable when the matrix of the
Fréchet derivative `DT(x̄)` is. -/
def EStableAt {ι : Type*} [Fintype ι] [DecidableEq ι] (T : (ι → ℝ) → (ι → ℝ))
    (xbar : ι → ℝ) : Prop :=
  T xbar = xbar ∧ DifferentiableAt ℝ T xbar ∧
    EStable (LinearMap.toMatrix' (fderiv ℝ T xbar : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)))

/-- Restated from the Woodford Chapter 4 project, for Cochrane (2023), §16.10.7, p. 394: an
affine map `T(x) = c + M x` has Fréchet derivative `M` everywhere. -/
theorem hasFDerivAt_affine {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ)
    (M : Matrix ι ι ℝ) (x : ι → ℝ) :
    HasFDerivAt (fun y => c + M *ᵥ y) (LinearMap.toContinuousLinearMap (Matrix.toLin' M)) x := by
  have h := (LinearMap.toContinuousLinearMap (Matrix.toLin' M)).hasFDerivAt (x := x)
  have h2 := h.const_add c
  convert h2 using 1
  funext y
  simp [Matrix.toLin'_apply]

/-- Restated from the Woodford Chapter 4 project, for Cochrane (2023), §16.10.7, p. 394: for an
affine `T(x) = c + M x`, a fixed point is E-stable iff `M` is. -/
theorem eStableAt_affine_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ)
    (M : Matrix ι ι ℝ) (xbar : ι → ℝ) (hfix : c + M *ᵥ xbar = xbar) :
    EStableAt (fun y => c + M *ᵥ y) xbar ↔ EStable M := by
  have hd := hasFDerivAt_affine c M xbar
  unfold EStableAt
  rw [hd.fderiv]
  simp only [LinearMap.coe_toContinuousLinearMap, LinearMap.toMatrix'_toLin']
  exact ⟨fun h => h.2.2, fun h => ⟨hfix, hd.differentiableAt, h⟩⟩

/-! ## Diagonal and scalar Jacobians -/

/-- Cochrane (2023), §16.10.7, p. 394: the eigenvalues of `diag(a, b)` are `a` and `b`. -/
theorem isEig_diag2_iff (a b : ℝ) (μ : ℂ) :
    IsEig ((!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) ℝ).map Complex.ofReal) μ ↔
      μ = a ∨ μ = b := by
  rw [isEig_iff_det, Matrix.det_fin_two]
  simp [sub_eq_zero]

/-- Cochrane (2023), §16.10.7, p. 394: `diag(a, b)` is E-stable iff `a < 1` and `b < 1`. -/
theorem eStable_diag2_iff (a b : ℝ) : EStable !![a, 0; 0, b] ↔ a < 1 ∧ b < 1 := by
  rw [eStable_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa using h a ((isEig_diag2_iff a b a).mpr (Or.inl rfl))
    · simpa using h b ((isEig_diag2_iff a b b).mpr (Or.inr rfl))
  · rintro ⟨ha, hb⟩ μ hμ
    rcases (isEig_diag2_iff a b μ).mp hμ with h | h <;> simp [h, ha, hb]

/-- Cochrane (2023), §16.10.7, p. 394: the only eigenvalue of the `1 × 1` matrix `(a)` is `a`. -/
theorem isEig_one_iff (a : ℝ) (μ : ℂ) :
    IsEig ((!![a] : Matrix (Fin 1) (Fin 1) ℝ).map Complex.ofReal) μ ↔ μ = a := by
  rw [isEig_iff_det, Matrix.det_fin_one]
  simp [sub_eq_zero]

/-- Cochrane (2023), §16.10.7, p. 394: the `1 × 1` matrix `(a)` is E-stable iff `a < 1`. -/
theorem eStable_one_iff (a : ℝ) : EStable !![a] ↔ a < 1 := by
  rw [eStable_iff]
  constructor
  · intro h
    simpa using h a ((isEig_one_iff a a).mpr rfl)
  · intro ha μ hμ
    rw [(isEig_one_iff a μ).mp hμ]
    simpa using ha

/-- Cochrane (2023), §16.10.7, p. 394: E-stability of a rest point of a scalar map: `T x̄ = x̄`
and `T′(x̄) < 1`. -/
def EStableAt1 (T : ℝ → ℝ) (x : ℝ) : Prop := T x = x ∧ ∃ a, HasDerivAt T a x ∧ a < 1

/-- Cochrane (2023), §16.10.7, p. 394: the scalar notion `EStableAt1` is Woodford's `EStableAt`
for the map lifted to `Fin 1 → ℝ`. -/
theorem eStableAt_lift_iff {T : ℝ → ℝ} {x : ℝ} (hT : DifferentiableAt ℝ T x) :
    EStableAt (fun v : Fin 1 → ℝ => fun _ => T (v 0)) (fun _ => x) ↔ EStableAt1 T x := by
  have hp : HasFDerivAt (fun v : Fin 1 → ℝ => v 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) (fun _ => x) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt
  have hc : HasFDerivAt (fun v : Fin 1 → ℝ => T (v 0))
      (deriv T x • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
      (fun _ => x) := hT.hasDerivAt.comp_hasFDerivAt (f := fun v : Fin 1 → ℝ => v 0) _ hp
  have hL : HasFDerivAt (fun v : Fin 1 → ℝ => fun _ : Fin 1 => T (v 0))
      (ContinuousLinearMap.pi fun _ : Fin 1 =>
        deriv T x • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)
      (fun _ => x) := hasFDerivAt_pi.mpr fun _ => hc
  have hM : LinearMap.toMatrix' ((fderiv ℝ (fun v : Fin 1 → ℝ => fun _ : Fin 1 => T (v 0))
      (fun _ => x)) : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)) = !![deriv T x] := by
    rw [hL.fderiv]
    ext i j
    fin_cases i
    fin_cases j
    simp [LinearMap.toMatrix'_apply]
  unfold EStableAt EStableAt1
  rw [hM, eStable_one_iff]
  constructor
  · rintro ⟨hfix, -, ha⟩
    exact ⟨congrFun hfix 0, deriv T x, hT.hasDerivAt, ha⟩
  · rintro ⟨hfix, a, ha, ha1⟩
    refine ⟨funext fun _ => hfix, hL.differentiableAt, ?_⟩
    rwa [ha.deriv]

/-! ## The linear model (16.1)–(16.2) under MSV learning -/

variable {Ω : Type*}

/-- Cochrane (2023), §16.10.7, p. 394, and §16.10.1, p. 385: the forecast of `π_{t+1}` made with
the perceived law of motion `π_t = a + b u_t` when `u` is AR(1) with coefficient `η`:
`Ê_t π_{t+1} = a + bη u_t`. -/
def plmForecast (a b η : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := fun ω => a + b * η * u t ω

/-- Cochrane (2023), §16.10.7, p. 394: if the perceived law `π_t = a + b u_t` were true and `u`
is AR(1), the rational forecast of `π_{t+1}` would be `plmForecast`. -/
theorem E_plm (𝔼 : ExpectationSystem Ω) {η : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 η u)
    (a b : ℝ) (t : ℕ) :
    𝔼.E t (fun ω => a + b * u (t + 1) ω) = plmForecast a b η u t := by
  have e : (fun ω => a + b * u (t + 1) ω) = (fun _ => a) + b • u (t + 1) := by
    funext ω; simp
  rw [e, map_add, map_smul, 𝔼.const, hu.2 t]
  funext ω
  simp [plmForecast]
  ring

/-- Cochrane (2023), §16.10.7, p. 394: the T-map of the MSV perceived law `θ = (a, b)`:
`T(a, b) = (a/φ, (bη − 1)/φ)`. -/
noncomputable def tMap (φ η : ℝ) (θ : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![θ 0 / φ, (θ 1 * η - 1) / φ]

/-- Cochrane (2023), eqs. (16.1)–(16.2), p. 364, with subjective forecasts (§16.10.7, p. 394):
for `φ ≠ 0`, the rate equals the forecast `Ê_tπ_{t+1} = a + bηu_t` and the rule
`i_t = φπ_t + u_t` at every date iff inflation follows the actual law of motion
`π_t = T(a,b)₀ + T(a,b)₁ u_t` and the rate is the forecast. -/
theorem tempEq_iff {φ η a b : ℝ} (hφ : φ ≠ 0) {u i π : ℕ → Ω → ℝ} :
    (∀ t, i t = plmForecast a b η u t ∧ i t = φ • π t + u t) ↔
      ∀ t, i t = plmForecast a b η u t ∧
        π t = fun ω => tMap φ η ![a, b] 0 + tMap φ η ![a, b] 1 * u t ω := by
  refine forall_congr' fun t => and_congr_right fun hi => ?_
  rw [hi]
  constructor
  · intro h
    funext ω
    have := congrFun h ω
    simp only [plmForecast, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [tMap, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp
    linarith
  · intro h
    funext ω
    have := congrFun h ω
    simp only [tMap, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
    simp only [plmForecast, Pi.add_apply, Pi.smul_apply, smul_eq_mul, this]
    field_simp
    ring

/-- Cochrane (2023), §16.10.1, p. 385 and §16.10.7, p. 394: for `φ ≠ 1` and `φ ≠ η` the unique
self-consistent equilibrium (fixed point of the T-map) is `(a, b) = (0, −1/(φ − η))`, the MSV
solution (16.9). -/
theorem tMap_fixed_iff {φ η : ℝ} (hφ : φ ≠ 0) (h1 : φ ≠ 1) (hη : φ ≠ η) (θ : Fin 2 → ℝ) :
    tMap φ η θ = θ ↔ θ = ![0, -(φ - η)⁻¹] := by
  have hne : φ - η ≠ 0 := sub_ne_zero.mpr hη
  have h1' : φ - 1 ≠ 0 := sub_ne_zero.mpr h1
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [tMap, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h0 h1
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      field_simp at h0
      have : θ 0 * (φ - 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h h1'
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      field_simp at h1 ⊢
      linarith
  · rintro rfl
    ext i
    fin_cases i
    · simp [tMap]
    · simp only [tMap, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      field_simp
      ring

/-- Cochrane (2023), eq. (16.9), p. 365: at the self-consistent equilibrium the actual law of
motion is the MSV solution `π_t = −u_t/(φ − η)` (`SimplestModel.ar1Pi`), which solves (16.4). -/
theorem fixed_is_msv (𝔼 : ExpectationSystem Ω) {φ η : ℝ} (hη : φ ≠ η) {u : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 η u) :
    (∀ t, (fun ω => (![0, -(φ - η)⁻¹] : Fin 2 → ℝ) 0 + (![0, -(φ - η)⁻¹] : Fin 2 → ℝ) 1 *
      u t ω) = SimplestModel.ar1Pi φ η u t) ∧
      SimplestModel.Eq164 𝔼 φ u (SimplestModel.ar1Pi φ η u) := by
  refine ⟨fun t => ?_, SimplestModel.ar1Pi_eq164 𝔼 hη hu⟩
  funext ω
  simp [SimplestModel.ar1Pi]

/-- Cochrane (2023), §16.10.7, p. 394: the T-map is affine, `T(θ) = c + Mθ` with
`c = (0, −1/φ)` and `M = diag(1/φ, η/φ)`. -/
theorem tMap_affine (φ η : ℝ) :
    tMap φ η = fun θ => ![0, -φ⁻¹] + !![φ⁻¹, 0; 0, η / φ] *ᵥ θ := by
  funext θ
  ext i
  fin_cases i
  · simp [tMap, dotProduct, Fin.sum_univ_two, div_eq_mul_inv, mul_comm]
  · simp [tMap, dotProduct, Fin.sum_univ_two, div_eq_mul_inv]
    ring

/-- Cochrane (2023), §16.10.7, p. 394: for `φ ≠ 0, 1, η`, the MSV equilibrium is E-stable iff
`1/φ < 1` and `η/φ < 1`. -/
theorem msv_eStable_iff {φ η : ℝ} (hφ : φ ≠ 0) (h1 : φ ≠ 1) (hη : φ ≠ η) :
    EStableAt (tMap φ η) ![0, -(φ - η)⁻¹] ↔ φ⁻¹ < 1 ∧ η / φ < 1 := by
  rw [tMap_affine, eStableAt_affine_iff, eStable_diag2_iff]
  have := (tMap_fixed_iff hφ h1 hη ![0, -(φ - η)⁻¹]).mpr rfl
  rw [tMap_affine] at this
  exact this

/-- Cochrane (2023), §16.10.7, p. 394: for `φ > 0` (`φ ≠ 1`, `φ ≠ η`) and `η < 1`, the MSV
equilibrium is E-stable iff `φ > 1`. -/
theorem msv_eStable_iff_pos {φ η : ℝ} (hφ : 0 < φ) (h1 : φ ≠ 1) (hη : φ ≠ η) (hη1 : η < 1) :
    EStableAt (tMap φ η) ![0, -(φ - η)⁻¹] ↔ 1 < φ := by
  rw [msv_eStable_iff hφ.ne' h1 hη, inv_lt_one_iff₀, div_lt_one hφ]
  constructor
  · rintro ⟨h | h, -⟩
    · linarith
    · exact h
  · intro h
    exact ⟨Or.inr h, by linarith⟩

/-- Cochrane (2023), §16.10.7, p. 394, McCallum's claim in the linear model: the active (`φ > 1`)
MSV equilibrium is E-stable (`η < 1`). -/
theorem active_eStable {φ η : ℝ} (hφ : 1 < φ) (hη1 : η < 1) :
    EStableAt (tMap φ η) ![0, -(φ - η)⁻¹] :=
  (msv_eStable_iff_pos (by linarith) hφ.ne' (by intro h; linarith) hη1).mpr hφ

/-- Cochrane (2023), §16.10.7, p. 394, McCallum's claim in the linear model: a passive rule with
`0 < φ < 1` (`φ ≠ η`) gives an MSV equilibrium that is not E-stable. -/
theorem passive_not_eStable {φ η : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) (hη : φ ≠ η) :
    ¬ EStableAt (tMap φ η) ![0, -(φ - η)⁻¹] := by
  rw [msv_eStable_iff hφ0.ne' hφ1.ne hη]
  rintro ⟨h, -⟩
  have : 1 < φ⁻¹ := (one_lt_inv₀ hφ0).mpr hφ1
  linarith

/-- Cochrane (2023), §16.10.7, p. 394, precision: E-stability is not the Taylor principle. For
`−1 < φ < 0` and `η ≥ 0` the MSV equilibrium is E-stable although (16.4) is indeterminate
(`SimplestModel.determinate_iff`: determinacy needs `|φ| > 1`). -/
theorem negative_passive_eStable {φ η : ℝ} (hφ0 : φ < 0) (hη : 0 ≤ η) :
    EStableAt (tMap φ η) ![0, -(φ - η)⁻¹] := by
  rw [msv_eStable_iff hφ0.ne (by intro h; linarith) (by intro h; linarith)]
  refine ⟨by have := inv_lt_zero.mpr hφ0; linarith, ?_⟩
  have : η / φ ≤ 0 := div_nonpos_of_nonneg_of_nonpos hη hφ0.le
  linarith

/-- Cochrane (2023), §16.10.7, p. 394: the MSV equilibrium of `(φ, u)` is also the MSV
equilibrium of `(φ', u')` with `u' = ((φ' − η)/(φ − η)) u`, for every `φ' ≠ η`. -/
theorem msv_reparam {φ φ' η : ℝ} (hη : φ ≠ η) (hη' : φ' ≠ η) (u : ℕ → Ω → ℝ) :
    SimplestModel.ar1Pi φ' η (((φ' - η) / (φ - η)) • u) = SimplestModel.ar1Pi φ η u := by
  have h1 : φ - η ≠ 0 := sub_ne_zero.mpr hη
  have h2 : φ' - η ≠ 0 := sub_ne_zero.mpr hη'
  funext t ω
  simp only [SimplestModel.ar1Pi, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- Cochrane (2023), §16.10.7, p. 394, "people in the economy cannot learn it": E-stability is a
property of the off-equilibrium `φ`, not of the data. For every AR(1) disturbance (`η < 1`) and
every `φ ≠ η`, the observed MSV equilibrium inflation and interest rate are generated both by a
policy `(φ₁, u₁)` with `φ₁ > 1` whose MSV equilibrium is E-stable and by a policy `(φ₂, u₂)`
with `0 < φ₂ < 1` whose MSV equilibrium is not E-stable; both rules satisfy (16.2) with the same
`π` and `i`. -/
theorem eStability_not_identified (𝔼 : ExpectationSystem Ω) {φ η : ℝ} (hη1 : η < 1)
    (hη : φ ≠ η) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 η u) :
    ∃ φ₁ u₁ φ₂ u₂, SimplestModel.ar1Pi φ₁ η u₁ = SimplestModel.ar1Pi φ η u ∧
      SimplestModel.ar1Pi φ₂ η u₂ = SimplestModel.ar1Pi φ η u ∧
      (∀ t, φ₁ • SimplestModel.ar1Pi φ η u t + u₁ t =
        𝔼.E t (SimplestModel.ar1Pi φ η u (t + 1))) ∧
      (∀ t, φ₂ • SimplestModel.ar1Pi φ η u t + u₂ t =
        𝔼.E t (SimplestModel.ar1Pi φ η u (t + 1))) ∧
      EStableAt (tMap φ₁ η) ![0, -(φ₁ - η)⁻¹] ∧ ¬ EStableAt (tMap φ₂ η) ![0, -(φ₂ - η)⁻¹] ∧
      1 < φ₁ ∧ 0 < φ₂ ∧ φ₂ < 1 := by
  -- choose `φ₂ ∈ (0, 1)` with `φ₂ ≠ η`
  obtain ⟨p, hp0, hp1, hpη⟩ : ∃ p : ℝ, 0 < p ∧ p < 1 ∧ p ≠ η := by
    by_cases h : η ≤ 0
    · exact ⟨1 / 2, by norm_num, by norm_num, by intro h'; linarith⟩
    · push Not at h
      exact ⟨(1 + η) / 2, by linarith, by linarith, by intro h'; linarith⟩
  have h2η : (2 : ℝ) ≠ η := by intro h; linarith
  refine ⟨2, ((2 - η) / (φ - η)) • u, p, ((p - η) / (φ - η)) • u,
    msv_reparam hη h2η u, msv_reparam hη hpη u, fun t => ?_, fun t => ?_,
    active_eStable (by norm_num) hη1, passive_not_eStable hp0 hp1 hpη, by norm_num, hp0, hp1⟩
  · rw [← msv_reparam hη h2η u, SimplestModel.ar1Pi_eq164 𝔼 h2η (by
      refine ⟨fun t => ?_, fun t => ?_⟩
      · simp only [Pi.smul_apply]
        rw [𝔼.E_smul, hu.1 t]
      · simp only [Pi.smul_apply]
        rw [𝔼.E_smul, hu.2 t, smul_comm]) t]
  · rw [← msv_reparam hη hpη u, SimplestModel.ar1Pi_eq164 𝔼 hpη (by
      refine ⟨fun t => ?_, fun t => ?_⟩
      · simp only [Pi.smul_apply]
        rw [𝔼.E_smul, hu.1 t]
      · simp only [Pi.smul_apply]
        rw [𝔼.E_smul, hu.2 t, smul_comm]) t]

/-! ## The nonlinear model of Figure 16.2 under steady-state learning -/

/-- Cochrane (2023), eqs. (16.27)–(16.28), p. 378, with subjective expected gross inflation
`Πᵉ` (steady-state learning, §16.10.7, p. 394): the consumer's condition `Πᵉ = β(1 + i_t)` and
the rule `1 + i_t = (1 + r)Φ(Π_t)`. -/
def TempEqNL (r : ℝ) (Φ : ℝ → ℝ) (Pe x i : ℝ) : Prop :=
  (1 + r)⁻¹ * (1 + i) = Pe ∧ 1 + i = (1 + r) * Φ x

/-- Cochrane (2023), §16.10.7, p. 394: for `1 + r > 0`, the temporary equilibrium given expected
inflation `Πᵉ` has `Φ(Π_t) = Πᵉ` (and `1 + i_t = (1 + r)Πᵉ`): the actual inflation is a
preimage of the expectation under the rule. -/
theorem tempEqNL_iff {r : ℝ} (hr : 0 < 1 + r) {Φ : ℝ → ℝ} {Pe x i : ℝ} :
    TempEqNL r Φ Pe x i ↔ Φ x = Pe ∧ 1 + i = (1 + r) * Pe := by
  unfold TempEqNL
  constructor
  · rintro ⟨h1, h2⟩
    have : Φ x = Pe := by rw [← h1, h2, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
    exact ⟨this, by rw [h2, this]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h2, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul], by rw [h2, h1]⟩

/-- Cochrane (2023), §16.10.7, p. 394: the steady-state T-map exists. If `Φ(Π̄) = Π̄` and `Φ` has
strict derivative `d ≠ 0` at `Π̄`, there is a map `T`, continuous at `Π̄`, with `T(Π̄) = Π̄`,
`Φ(T(p)) = p` for `p` near `Π̄` (the temporary-equilibrium inflation), and `T′(Π̄) = 1/d`. -/
theorem tmap_exists {Φ : ℝ → ℝ} {Pb d : ℝ} (hfix : Φ Pb = Pb) (hd : HasStrictDerivAt Φ d Pb)
    (hd0 : d ≠ 0) :
    ∃ T : ℝ → ℝ, T Pb = Pb ∧ (∀ᶠ p in 𝓝 Pb, Φ (T p) = p) ∧ HasDerivAt T d⁻¹ Pb := by
  refine ⟨HasStrictDerivAt.localInverse Φ d Pb hd hd0, ?_, ?_, ?_⟩
  · have := (HasStrictDerivAt.eventually_left_inverse hd hd0).self_of_nhds
    rwa [hfix] at this
  · have := HasStrictDerivAt.eventually_right_inverse hd hd0
    rwa [hfix] at this
  · have := (HasStrictDerivAt.to_localInverse hd hd0).hasDerivAt
    rwa [hfix] at this

/-- Cochrane (2023), §16.10.7, p. 394: any T-map (a local inverse of `Φ`, continuous at the
steady state) has derivative `1/Φ′(Π̄)` at `Π̄`. -/
theorem hasDerivAt_tmap {Φ T : ℝ → ℝ} {Pb d : ℝ} (hT : T Pb = Pb) (hcont : ContinuousAt T Pb)
    (hd : HasDerivAt Φ d Pb) (hd0 : d ≠ 0) (hinv : ∀ᶠ p in 𝓝 Pb, Φ (T p) = p) :
    HasDerivAt T d⁻¹ Pb :=
  HasDerivAt.of_local_left_inverse hcont (by rwa [hT]) hd0 hinv

/-- Cochrane (2023), §16.10.7, p. 394: a steady state `Π̄` with `Φ′(Π̄) = d ≠ 0` is E-stable
under steady-state learning iff `1/d < 1` (i.e. `d > 1` or `d < 0`). -/
theorem steady_eStable_iff {Φ T : ℝ → ℝ} {Pb d : ℝ} (hT : T Pb = Pb)
    (hcont : ContinuousAt T Pb) (hd : HasDerivAt Φ d Pb) (hd0 : d ≠ 0)
    (hinv : ∀ᶠ p in 𝓝 Pb, Φ (T p) = p) : EStableAt1 T Pb ↔ d⁻¹ < 1 := by
  have hT' := hasDerivAt_tmap hT hcont hd hd0 hinv
  constructor
  · rintro ⟨-, a, ha, ha1⟩
    rwa [ha.unique hT'] at ha1
  · intro h
    exact ⟨hT, d⁻¹, hT', h⟩

/-- Cochrane (2023), p. 378 and §16.10.7, p. 394: the active steady state `Π*` with
`Φ′(Π*) > 1` is E-stable. -/
theorem target_eStable {Φ T : ℝ → ℝ} {Pis d : ℝ} (hT : T Pis = Pis)
    (hcont : ContinuousAt T Pis) (hd : HasDerivAt Φ d Pis) (hd1 : 1 < d)
    (hinv : ∀ᶠ p in 𝓝 Pis, Φ (T p) = p) : EStableAt1 T Pis :=
  (steady_eStable_iff hT hcont hd (by linarith) hinv).mpr (inv_lt_one_of_one_lt₀ hd1)

/-- Cochrane (2023), p. 379 and §16.10.7, p. 394: a passive steady state `Π_L` with
`0 < Φ′(Π_L) ≤ 1` (`LowerBound.lower_steady_state` gives `Φ′(Π_L) ≤ 1`) is not E-stable. -/
theorem lower_not_eStable {Φ T : ℝ → ℝ} {PL d : ℝ} (hT : T PL = PL)
    (hcont : ContinuousAt T PL) (hd : HasDerivAt Φ d PL) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hinv : ∀ᶠ p in 𝓝 PL, Φ (T p) = p) : ¬ EStableAt1 T PL := by
  rw [steady_eStable_iff hT hcont hd hd0.ne' hinv, not_lt]
  exact one_le_inv₀ hd0 |>.mpr hd1

/-- Cochrane (2023), §16.10.7, p. 394, McCallum's claim for Figure 16.2: if `Φ` has strict
derivatives `Φ′(Π*) > 1` and `0 < Φ′(Π_L) ≤ 1` at its two steady states, the steady-state
T-maps exist, `Π*` is E-stable and `Π_L` is not. -/
theorem mccallum_claim {Φ : ℝ → ℝ} {Pis PL d dL : ℝ} (hfix : Φ Pis = Pis)
    (hfixL : Φ PL = PL) (hd : HasStrictDerivAt Φ d Pis) (hd1 : 1 < d)
    (hdL : HasStrictDerivAt Φ dL PL) (hdL0 : 0 < dL) (hdL1 : dL ≤ 1) :
    (∃ T : ℝ → ℝ, (∀ᶠ p in 𝓝 Pis, Φ (T p) = p) ∧ EStableAt1 T Pis) ∧
      ∃ T : ℝ → ℝ, (∀ᶠ p in 𝓝 PL, Φ (T p) = p) ∧ T PL = PL ∧ ¬ EStableAt1 T PL := by
  obtain ⟨T, hT, hinv, hT'⟩ := tmap_exists hfix hd (by linarith)
  obtain ⟨TL, hTL, hinvL, hTL'⟩ := tmap_exists hfixL hdL hdL0.ne'
  refine ⟨⟨T, hinv, hT, d⁻¹, hT', inv_lt_one_of_one_lt₀ hd1⟩, TL, hinvL, hTL, ?_⟩
  rintro ⟨-, a, ha, ha1⟩
  rw [ha.unique hTL'] at ha1
  linarith [(one_le_inv₀ hdL0).mpr hdL1]

/-- Cochrane (2023), p. 379, error E2 and §16.10.7: in the tangency counterexample
`LowerBound.phiTan` (`Φ′(Π_L) = 1` at `Π_L = 1`) the lower steady state is not E-stable either:
`1/Φ′(Π_L) = 1` is not `< 1`. -/
theorem tangency_not_eStable {T : ℝ → ℝ} (hT : T 1 = 1) (hcont : ContinuousAt T 1)
    (hinv : ∀ᶠ p in 𝓝 (1 : ℝ), LowerBound.phiTan (T p) = p) : ¬ EStableAt1 T 1 := by
  have hd := LowerBound.hasDerivAt_phiTan (x := 1) (by norm_num)
  have hd' : HasDerivAt LowerBound.phiTan 1 1 := by convert hd using 1; norm_num
  exact lower_not_eStable hT hcont hd' one_pos le_rfl hinv

/-! ## The E-stability differential equation -/

/-- Cochrane (2023), §16.10.7, p. 394, and Woodford (2003), (2.20), p. 265: `θ : ℝ → ℝ` solves
the E-stability equation `θ̇ = T(θ) − θ` at every notional time `τ`. -/
def IsESol1 (T : ℝ → ℝ) (θ : ℝ → ℝ) : Prop := ∀ τ, HasDerivAt θ (T (θ τ) - θ τ) τ

/-- Cochrane (2023), §16.10.7, p. 394: for the linearised map `T(x) = x̄ + a(x − x̄)` every
solution is `θ(τ) = x̄ + e^{(a−1)τ}(θ(0) − x̄)`. -/
theorem esol_linear_eq {a xb : ℝ} {θ : ℝ → ℝ} (h : IsESol1 (fun x => xb + a * (x - xb)) θ)
    (τ : ℝ) : θ τ = xb + Real.exp ((a - 1) * τ) * (θ 0 - xb) := by
  set g : ℝ → ℝ := fun s => Real.exp (-((a - 1) * s)) * (θ s - xb) with hg
  have hgd : ∀ s, HasDerivAt g 0 s := by
    intro s
    have hlin : HasDerivAt (fun s : ℝ => -((a - 1) * s)) (-(a - 1)) s := by
      convert ((hasDerivAt_id' s).const_mul (a - 1)).neg using 1
      ring
    have h1 : HasDerivAt (fun s => Real.exp (-((a - 1) * s)))
        (Real.exp (-((a - 1) * s)) * (-(a - 1))) s := hlin.exp
    have h2 : HasDerivAt (fun s => θ s - xb) (xb + a * (θ s - xb) - θ s) s :=
      (h s).sub_const xb
    convert h1.mul h2 using 1
    ring
  have hc : ∀ s, g s = g 0 := fun s =>
    is_const_of_deriv_eq_zero (fun s => (hgd s).differentiableAt) (fun s => (hgd s).deriv) s 0
  have := hc τ
  simp only [hg, mul_zero, neg_zero, Real.exp_zero, one_mul] at this
  have he : Real.exp ((a - 1) * τ) * Real.exp (-((a - 1) * τ)) = 1 := by
    rw [← Real.exp_add]; simp
  calc θ τ = xb + (Real.exp ((a - 1) * τ) * Real.exp (-((a - 1) * τ))) * (θ τ - xb) := by
        rw [he]; ring
    _ = xb + Real.exp ((a - 1) * τ) * (θ 0 - xb) := by rw [← this]; ring

/-- Cochrane (2023), §16.10.7, p. 394: the formula of `esol_linear_eq` is a solution. -/
theorem esol_linear_sol (a xb x0 : ℝ) :
    IsESol1 (fun x => xb + a * (x - xb)) (fun τ => xb + Real.exp ((a - 1) * τ) * (x0 - xb)) := by
  intro τ
  have := (((hasDerivAt_id' τ).const_mul (a - 1)).exp.mul_const (x0 - xb)).const_add xb
  convert this using 1
  ring

/-- Cochrane (2023), §16.10.7, p. 394, and Woodford (2003), p. 266: for the linearised map, every
solution of the E-stability equation converges to `x̄` iff `T′ = a < 1`, i.e. iff `x̄` is
E-stable. -/
theorem esol_linear_tendsto_iff (a xb : ℝ) :
    (∀ θ, IsESol1 (fun x => xb + a * (x - xb)) θ → Tendsto θ atTop (𝓝 xb)) ↔ a < 1 := by
  constructor
  · intro h
    by_contra ha
    push Not at ha
    have hs := h _ (esol_linear_sol a xb (xb + 1))
    have hge : ∀ τ : ℝ, 0 ≤ τ → xb + 1 ≤ xb + Real.exp ((a - 1) * τ) * (xb + 1 - xb) := by
      intro τ hτ
      have : 1 ≤ Real.exp ((a - 1) * τ) := Real.one_le_exp (by nlinarith)
      nlinarith
    have := ge_of_tendsto hs (eventually_atTop.mpr ⟨0, hge⟩)
    linarith
  · intro ha θ hθ
    have he : Tendsto (fun τ => Real.exp ((a - 1) * τ)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp ((tendsto_id.const_mul_atTop_of_neg (by linarith)))
    have := (he.mul_const (θ 0 - xb)).const_add xb
    simp only [zero_mul, add_zero] at this
    exact this.congr fun τ => (esol_linear_eq hθ τ).symm

/-- Cochrane (2023), §16.10.7, p. 394: near a rest point with `T′(x̄) = a`, the field
`f(x) = T(x) − x` satisfies `f(x)(x − x̄) ≤ (a − 1 + c)(x − x̄)²` and
`f(x)(x − x̄) ≥ (a − 1 − c)(x − x̄)²` for any `c > 0`. -/
theorem field_bounds {T : ℝ → ℝ} {xb a : ℝ} (hfix : T xb = xb) (hT : HasDerivAt T a xb)
    {c : ℝ} (hc : 0 < c) :
    ∃ δ > 0, ∀ x, |x - xb| < δ →
      (T x - x) * (x - xb) ≤ (a - 1 + c) * (x - xb) ^ 2 ∧
        (a - 1 - c) * (x - xb) ^ 2 ≤ (T x - x) * (x - xb) := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff] at hT
  have hev := hT hc
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have h := hball (by rw [Real.dist_eq]; exact hx)
  simp only [Real.norm_eq_abs, smul_eq_mul, hfix] at h
  have hsq : |x - xb| * |x - xb| = (x - xb) ^ 2 := by rw [abs_mul_abs_self, sq]
  have key : |(T x - x - (a - 1) * (x - xb)) * (x - xb)| ≤ c * (x - xb) ^ 2 := by
    rw [abs_mul, ← hsq]
    have : T x - x - (a - 1) * (x - xb) = T x - xb - (x - xb) * a := by ring
    rw [this]
    nlinarith [abs_nonneg (x - xb)]
  have e : (T x - x) * (x - xb) =
      (T x - x - (a - 1) * (x - xb)) * (x - xb) + (a - 1) * (x - xb) ^ 2 := by ring
  constructor
  · rw [e]; nlinarith [le_abs_self ((T x - x - (a - 1) * (x - xb)) * (x - xb))]
  · rw [e]; nlinarith [neg_abs_le ((T x - x - (a - 1) * (x - xb)) * (x - xb))]

/-- Cochrane (2023), §16.10.7, p. 394, E-stability as local stability of the learning dynamics
(nonlinear): if `T(x̄) = x̄` and `T′(x̄) < 1`, there is `δ > 0` such that every solution of
`θ̇ = T(θ) − θ` with `|θ(0) − x̄| < δ` converges to `x̄`. -/
theorem eStable_local_convergence {T : ℝ → ℝ} {xb a : ℝ} (hfix : T xb = xb)
    (hT : HasDerivAt T a xb) (ha : a < 1) :
    ∃ δ > 0, ∀ θ, IsESol1 T θ → |θ 0 - xb| < δ → Tendsto θ atTop (𝓝 xb) := by
  set c : ℝ := (1 - a) / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  obtain ⟨δ, hδ, hb⟩ := field_bounds hfix hT hc0
  refine ⟨δ, hδ, fun θ hθ h0 => ?_⟩
  set V : ℝ → ℝ := fun τ => (θ τ - xb) ^ 2 with hV
  set W : ℝ → ℝ := fun τ => Real.exp (2 * c * τ) * V τ with hW
  have hWd : ∀ τ, HasDerivAt W (Real.exp (2 * c * τ) *
      (2 * c * V τ + 2 * ((T (θ τ) - θ τ) * (θ τ - xb)))) τ := by
    intro τ
    have hl : HasDerivAt (fun τ : ℝ => 2 * c * τ) (2 * c) τ := by
      convert (hasDerivAt_id' τ).const_mul (2 * c) using 1; ring
    have h1 : HasDerivAt (fun τ => Real.exp (2 * c * τ)) (Real.exp (2 * c * τ) * (2 * c)) τ :=
      hl.exp
    have h2 : HasDerivAt V (2 * (θ τ - xb) * (T (θ τ) - θ τ)) τ := by
      have := ((hθ τ).sub_const xb).pow 2
      convert this using 1; simp
    convert h1.mul h2 using 1; ring
  have hWc : Continuous W := continuous_iff_continuousAt.mpr fun τ => (hWd τ).continuousAt
  have hθc : Continuous θ := continuous_iff_continuousAt.mpr fun τ => (hθ τ).continuousAt
  -- inside the neighbourhood `W` is nonincreasing
  have hneg : ∀ τ, |θ τ - xb| < δ → Real.exp (2 * c * τ) *
      (2 * c * V τ + 2 * ((T (θ τ) - θ τ) * (θ τ - xb))) ≤ 0 := by
    intro τ hτ
    have := (hb (θ τ) hτ).1
    have hle : 2 * c * V τ + 2 * ((T (θ τ) - θ τ) * (θ τ - xb)) ≤ 0 := by
      simp only [hV]; nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hle
  have hV0 : V 0 < δ ^ 2 := by
    simp only [hV]
    have := abs_nonneg (θ 0 - xb)
    nlinarith [sq_abs (θ 0 - xb)]
  -- the solution never leaves the neighbourhood
  have hstay : ∀ τ, 0 ≤ τ → V τ < δ ^ 2 := by
    by_contra hcon
    push Not at hcon
    set A : Set ℝ := {τ | 0 ≤ τ ∧ δ ^ 2 ≤ V τ} with hA
    have hAne : A.Nonempty := hcon
    have hAb : BddBelow A := ⟨0, fun τ h => h.1⟩
    have hAcl : IsClosed A := by
      have hVc : Continuous V := by simp only [hV]; fun_prop
      exact (isClosed_le continuous_const continuous_id).inter
        (isClosed_le continuous_const hVc)
    have hmem := hAcl.csInf_mem hAne hAb
    set s := sInf A with hs
    have hs0 : 0 < s := by
      rcases hmem.1.lt_or_eq with h | h
      · exact h
      · exfalso; have := hmem.2; rw [← h] at this; linarith
    have hbefore : ∀ τ, 0 ≤ τ → τ < s → V τ < δ ^ 2 := by
      intro τ h0' hτ
      by_contra hc'
      push Not at hc'
      have := csInf_le hAb ⟨h0', hc'⟩
      linarith
    have hanti : AntitoneOn W (Set.Icc 0 s) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 s) hWc.continuousOn
      · intro τ _
        exact (hWd τ).differentiableAt.differentiableWithinAt
      · intro τ hτ
        rw [interior_Icc] at hτ
        rw [(hWd τ).deriv]
        apply hneg
        have := hbefore τ hτ.1.le hτ.2
        simp only [hV] at this
        exact abs_lt_of_sq_lt_sq this hδ.le
    have := hanti ⟨le_rfl, hs0.le⟩ ⟨hs0.le, le_rfl⟩ hs0.le
    simp only [hW, mul_zero, Real.exp_zero, one_mul] at this
    have hexp : 1 < Real.exp (2 * c * s) := Real.one_lt_exp_iff.mpr (by positivity)
    have hVs := hmem.2
    have hVpos : 0 < V s := lt_of_lt_of_le (by positivity) hVs
    nlinarith
  -- hence `W` is nonincreasing on `[0, ∞)`, and `V τ ≤ e^{−2cτ} V 0`
  have hanti : AntitoneOn W (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hWc.continuousOn
    · intro τ _
      exact (hWd τ).differentiableAt.differentiableWithinAt
    · intro τ hτ
      rw [interior_Ici] at hτ
      rw [(hWd τ).deriv]
      apply hneg
      have := hstay τ (le_of_lt hτ)
      simp only [hV] at this
      exact abs_lt_of_sq_lt_sq this hδ.le
  have hVle : ∀ τ, 0 ≤ τ → V τ ≤ Real.exp (-(2 * c * τ)) * V 0 := by
    intro τ hτ
    have h := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hτ) hτ
    simp only [hW, mul_zero, Real.exp_zero, one_mul] at h
    have he : Real.exp (-(2 * c * τ)) * Real.exp (2 * c * τ) = 1 := by
      rw [← Real.exp_add]; simp
    calc V τ = Real.exp (-(2 * c * τ)) * (Real.exp (2 * c * τ) * V τ) := by
          rw [← mul_assoc, he, one_mul]
      _ ≤ Real.exp (-(2 * c * τ)) * V 0 := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
  have hlim : Tendsto (fun τ => Real.exp (-(2 * c * τ)) * V 0) atTop (𝓝 0) := by
    have : Tendsto (fun τ => Real.exp (-(2 * c * τ))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (tendsto_id.const_mul_atTop (by positivity)))
    simpa using this.mul_const (V 0)
  have hVlim : Tendsto V atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun τ => sq_nonneg _)
      (eventually_atTop.mpr ⟨0, fun τ hτ => hVle τ hτ⟩)
  have habs : Tendsto (fun τ => |θ τ - xb|) atTop (𝓝 0) := by
    have := hVlim.sqrt
    simp only [Real.sqrt_zero] at this
    exact this.congr fun τ => by simp only [hV]; exact Real.sqrt_sq_eq_abs _
  have := (tendsto_zero_iff_abs_tendsto_zero _).mpr habs
  simpa using this.add_const xb

/-- Cochrane (2023), §16.10.7, p. 394, failure of E-stability (nonlinear): if `T(x̄) = x̄` and
`T′(x̄) > 1`, every solution of `θ̇ = T(θ) − θ` that converges to `x̄` is eventually equal to `x̄`:
learning dynamics never approach the rest point asymptotically. -/
theorem unstable_no_convergence {T : ℝ → ℝ} {xb a : ℝ} (hfix : T xb = xb)
    (hT : HasDerivAt T a xb) (ha : 1 < a) {θ : ℝ → ℝ} (hθ : IsESol1 T θ)
    (hlim : Tendsto θ atTop (𝓝 xb)) : ∀ᶠ τ in atTop, θ τ = xb := by
  set c : ℝ := (a - 1) / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  obtain ⟨δ, hδ, hb⟩ := field_bounds hfix hT hc0
  obtain ⟨τ1, hτ1⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hlim) δ hδ)
  set V : ℝ → ℝ := fun τ => (θ τ - xb) ^ 2 with hV
  set W : ℝ → ℝ := fun τ => Real.exp (-(2 * c * τ)) * V τ with hW
  have hWd : ∀ τ, HasDerivAt W (Real.exp (-(2 * c * τ)) *
      (-(2 * c * V τ) + 2 * ((T (θ τ) - θ τ) * (θ τ - xb)))) τ := by
    intro τ
    have hl : HasDerivAt (fun τ : ℝ => -(2 * c * τ)) (-(2 * c)) τ := by
      convert ((hasDerivAt_id' τ).const_mul (2 * c)).neg using 1; ring
    have h1 : HasDerivAt (fun τ => Real.exp (-(2 * c * τ)))
        (Real.exp (-(2 * c * τ)) * (-(2 * c))) τ := hl.exp
    have h2 : HasDerivAt V (2 * (θ τ - xb) * (T (θ τ) - θ τ)) τ := by
      have := ((hθ τ).sub_const xb).pow 2
      convert this using 1; simp
    convert h1.mul h2 using 1; ring
  have hWc : Continuous W := continuous_iff_continuousAt.mpr fun τ => (hWd τ).continuousAt
  have hmono : MonotoneOn W (Set.Ici τ1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici τ1) hWc.continuousOn
    · intro τ _
      exact (hWd τ).differentiableAt.differentiableWithinAt
    · intro τ hτ
      rw [interior_Ici] at hτ
      rw [(hWd τ).deriv]
      have hin := hτ1 τ (le_of_lt hτ)
      rw [Real.dist_eq] at hin
      have := (hb (θ τ) hin).2
      have : 0 ≤ -(2 * c * V τ) + 2 * ((T (θ τ) - θ τ) * (θ τ - xb)) := by
        simp only [hV]; nlinarith
      exact mul_nonneg (Real.exp_pos _).le this
  have hVlim : Tendsto V atTop (𝓝 0) := by
    have := (hlim.sub_const xb).pow 2
    simpa [hV] using this
  have hWlim : Tendsto W atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hVlim
      (Eventually.of_forall fun τ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) ?_
    filter_upwards [eventually_ge_atTop 0] with τ hτ
    have : Real.exp (-(2 * c * τ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    exact mul_le_of_le_one_left (sq_nonneg _) this
  filter_upwards [eventually_ge_atTop τ1] with τ hτ
  have hW0 : W τ ≤ 0 := by
    refine ge_of_tendsto hWlim ?_
    filter_upwards [eventually_ge_atTop τ] with σ hσ
    exact hmono hτ (le_trans hτ hσ) hσ
  have hWnn : 0 ≤ W τ := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hWz : W τ = 0 := le_antisymm hW0 hWnn
  simp only [hW, mul_eq_zero, Real.exp_ne_zero, false_or, hV, pow_eq_zero_iff,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, sub_eq_zero] at hWz
  exact hWz

end Cochrane.NewKeynesianSelection.TidyR6EStability
