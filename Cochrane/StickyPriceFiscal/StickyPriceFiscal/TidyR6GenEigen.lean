/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.CTMatrixMethod
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The matrix exponential on generalised eigenspaces

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.13,
pp. 580–585 (the continuous-time matrix method behind §§5.7.3–5.7.5).

A1 §1.13 eigen-decomposes `A = QΛQ⁻¹`. `CTRules` proves the method for real diagonalisable `A`
and `CTMatrixMethod` given a Jordan decomposition `A = QJQ⁻¹` as a hypothesis. This module and
`TidyR6MatrixMethod` remove the hypothesis: for **every** operator `A` on a finite-dimensional
complex normed space (every complex matrix, and every real matrix by complexification) we build

* the matrix exponential `expT A t = exp(tA)` (Mathlib's `NormedSpace.exp`), its derivative, the
  group law, and **uniqueness**: every solution of `z' = Az` on `(0, ∞)`, continuous on `[0, ∞)`,
  is `z_t = exp(tA) z_0` (`ode_unique`);
* the generalised eigenspaces `E_μ = ker (A − μ)^∞`, which span the space and are independent
  (Mathlib's `Module.End.iSup_maxGenEigenspace_eq_top`,
  `Module.End.independent_maxGenEigenspace`), and the
  **spectral projections** `proj A μ` onto them (`proj_mem`, `proj_of_mem`, `proj_of_mem_ne`,
  `exists_decomp`: every vector is the finite sum of its components);
* the **closed form on a generalised eigenspace** (`expT_apply_of_pow`): if `(A − μ)^m v = 0`,
  `exp(tA) v = e^{μt} ∑_{j<m} (t^j/j!) (A − μ)^j v`, and `exp(tA)` maps `E_μ` into itself;
* the **asymptotics** (`tendsto_norm_expT_div`): for `0 ≠ v ∈ E_μ` with chain length `k`
  (`(A − μ)^k v ≠ 0 = (A − μ)^{k+1} v`), `‖exp(tA) v‖ / (t^k e^{(Re μ)t}) → ‖(A − μ)^k v‖/k! > 0`:
  each generalised-eigenvector component grows exactly like `t^k e^{(Re μ) t}`;
* the **bounded-component criterion** (`bounded_expT_iff`): for `v ∈ E_μ`, `t ↦ exp(tA) v` is
  bounded on `[0, ∞)` iff (`Re μ > 0 ⇒ v = 0`) and (`Re μ = 0 ⇒ (A − μ)v = 0`);
  `tendsto_expT_zero` (`Re μ < 0`: it tends to zero).
-/

namespace Cochrane.StickyPriceFiscal.TidyR6GenEigen

open Filter Topology NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-! ### The matrix exponential -/

/-- Cochrane (2023), A1 §1.13, p. 583 (`e^{At}`): the operator exponential `exp(tA)`. -/
noncomputable def expT (A : V →L[ℂ] V) (t : ℝ) : V →L[ℂ] V := exp (t • A)

/-- Cochrane (2023), A1 §1.13, p. 583: `d/dt exp(tA) = exp(tA) A`. -/
theorem hasDerivAt_expT (A : V →L[ℂ] V) (t : ℝ) :
    HasDerivAt (expT A) (expT A t * A) t :=
  hasDerivAt_exp_smul_const A t

/-- Cochrane (2023), A1 §1.13, p. 583: `d/dt exp(tA) = A exp(tA)`. -/
theorem hasDerivAt_expT' (A : V →L[ℂ] V) (t : ℝ) :
    HasDerivAt (expT A) (A * expT A t) t :=
  hasDerivAt_exp_smul_const' A t

omit [CompleteSpace V] in
/-- Cochrane (2023), A1 §1.13, p. 583: `exp(0·A) = I`. -/
theorem expT_zero (A : V →L[ℂ] V) : expT A 0 = 1 := by
  simp [expT]

/-- Cochrane (2023), A1 §1.13, p. 583: the group law `exp((s + t)A) = exp(sA) exp(tA)`. -/
theorem expT_add (A : V →L[ℂ] V) (s t : ℝ) : expT A (s + t) = expT A s * expT A t := by
  rw [expT, expT, expT, add_smul]
  have hr := expSeries_radius_eq_top ℂ (V →L[ℂ] V)
  exact exp_add_of_commute_of_mem_ball (𝕂 := ℂ) ((Commute.refl A).smul_left s |>.smul_right t)
    (hr.symm ▸ edist_lt_top _ _) (hr.symm ▸ edist_lt_top _ _)

/-- Cochrane (2023), A1 §1.13, p. 583: `exp(tA) exp(−tA) = I`. -/
theorem expT_mul_neg (A : V →L[ℂ] V) (t : ℝ) : expT A t * expT A (-t) = 1 := by
  rw [← expT_add, add_neg_cancel, expT_zero]

/-- Cochrane (2023), A1 §1.13, p. 583: `exp(tA)` is continuous in `t`. -/
theorem continuous_expT (A : V →L[ℂ] V) : Continuous (expT A) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_expT A t).continuousAt

omit [CompleteSpace V] in
/-- Cochrane (2023), A1 §1.13, p. 583: `A` commutes with `exp(tA)`. -/
theorem commute_expT (A : V →L[ℂ] V) (t : ℝ) : Commute A (expT A t) :=
  ((Commute.refl A).smul_right t).exp_right

omit [CompleteSpace V] in
/-- Cochrane (2023), A1 §1.13 (tool): the product rule for a time-varying complex operator
applied to a time-varying vector, `d/dt L_t z_t = L_t' z_t + L_t z_t'`. -/
theorem hasDerivAt_apply {L : ℝ → V →L[ℂ] V} {L' : V →L[ℂ] V} {z : ℝ → V} {z' : V} {t : ℝ}
    (hL : HasDerivAt L L' t) (hz : HasDerivAt z z' t) :
    HasDerivAt (fun u => L u (z u)) (L' (z t) + L t z') t := by
  have hR : HasDerivAt (fun u => ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ (L u))
      (ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ L') t :=
    (ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hL
  simpa using hR.clm_apply hz

/-- Cochrane (2023), A1 §1.13, p. 583: `t ↦ exp(tA) v` solves `z' = Az`. -/
theorem hasDerivAt_expT_apply (A : V →L[ℂ] V) (v : V) (t : ℝ) :
    HasDerivAt (fun u => expT A u v) (A (expT A t v)) t := by
  have h := hasDerivAt_apply (hasDerivAt_expT' A t) (hasDerivAt_const t v)
  simpa using h

/-- Cochrane (2023), A1 §1.13, pp. 581–583: **uniqueness of the solution of `z' = Az`.** If `z`
is continuous on `[0, ∞)` and `z' = Az` on `(0, ∞)`, then `z_t = exp(tA) z_0` for `t ≥ 0`. -/
theorem ode_unique {A : V →L[ℂ] V} {z : ℝ → V} (hc : ContinuousOn z (Set.Ici 0))
    (hd : ∀ t, 0 < t → HasDerivAt z (A (z t)) t) (t : ℝ) (ht : 0 ≤ t) :
    z t = expT A t (z 0) := by
  have hneg : ∀ τ : ℝ, HasDerivAt (fun u : ℝ => expT A (-u)) (-(expT A (-τ) * A)) τ := by
    intro τ
    have h := (hasDerivAt_expT A (-τ)).scomp τ (hasDerivAt_neg τ)
    simpa [Function.comp_def] using h
  have hG : ∀ τ ∈ Set.Ioo (0 : ℝ) t,
      HasDerivAt (fun u : ℝ => expT A (-u) (z u)) ((fun _ => (0 : V)) τ) τ := by
    intro τ hτ
    have h := hasDerivAt_apply (hneg τ) (hd τ hτ.1)
    convert h using 1
    simp [mul_apply_eq_comp]
  have hGc : ContinuousOn (fun u : ℝ => expT A (-u) (z u)) (Set.Icc 0 t) := by
    have h1 : Continuous fun u : ℝ => expT A (-u) := (continuous_expT A).comp continuous_neg
    exact (h1.continuousOn.clm_apply hc).mono Set.Icc_subset_Ici_self
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hGc hG
    (intervalIntegrable_const (μ := MeasureTheory.volume))
  simp only [intervalIntegral.integral_zero, neg_zero, expT_zero,
    one_apply_eq_self] at h
  have e : z t = expT A t (expT A (-t) (z t)) := by
    rw [← mul_apply_eq_comp, expT_mul_neg,
      one_apply_eq_self]
  rw [e, ← sub_eq_zero.1 h.symm]

/-! ### Generalised eigenspaces and spectral projections -/

variable [FiniteDimensional ℂ V]

/-- Cochrane (2023), A1 §1.13, p. 583 (the eigen-decomposition of `A`): the **generalised
eigenspace** `E_μ = ⋃_k ker (A − μ)^k` of `A` (Mathlib's `Module.End.maxGenEigenspace`). -/
abbrev gE (A : V →L[ℂ] V) (μ : ℂ) : Submodule ℂ V :=
  Module.End.maxGenEigenspace (A : V →ₗ[ℂ] V) μ

/-- Cochrane (2023), A1 §1.13 (Jordan blocks): the nilpotent part on `E_μ`, `N_μ = A − μ I`. -/
noncomputable def nil (A : V →L[ℂ] V) (μ : ℂ) : V →L[ℂ] V := A - μ • (1 : V →L[ℂ] V)

omit [CompleteSpace V] [FiniteDimensional ℂ V] in
/-- Cochrane (2023), A1 §1.13 (tool): powers of `N_μ` as a continuous or as an algebraic
endomorphism agree. -/
theorem nil_pow_apply (A : V →L[ℂ] V) (μ : ℂ) (j : ℕ) (v : V) :
    ((nil A μ) ^ j) v = (((A : V →ₗ[ℂ] V) - μ • 1) ^ j) v := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', pow_succ', mul_apply_eq_comp, Module.End.mul_apply, ih]
    simp [nil]

omit [CompleteSpace V] [FiniteDimensional ℂ V] in
/-- Cochrane (2023), A1 §1.13: `v ∈ E_μ` iff `(A − μ)^k v = 0` for some `k`. -/
theorem mem_gE_iff (A : V →L[ℂ] V) (μ : ℂ) (v : V) :
    v ∈ gE A μ ↔ ∃ k : ℕ, ((nil A μ) ^ k) v = 0 := by
  simp only [Module.End.mem_maxGenEigenspace, nil_pow_apply]

omit [CompleteSpace V] [FiniteDimensional ℂ V] in
/-- Cochrane (2023), A1 §1.13: every `N_ν = A − ν` maps `E_μ` into itself. -/
theorem nil_mem {A : V →L[ℂ] V} {μ : ℂ} (ν : ℂ) {v : V} (hv : v ∈ gE A μ) :
    nil A ν v ∈ gE A μ := by
  have hc : Commute (A : V →ₗ[ℂ] V) ((A : V →ₗ[ℂ] V) - ν • 1) :=
    (Commute.refl _).sub_right ((Commute.one_right _).smul_right ν)
  have h := Module.End.mapsTo_maxGenEigenspace_of_comm hc μ hv
  simpa [nil] using h

omit [CompleteSpace V] [FiniteDimensional ℂ V] in
/-- Cochrane (2023), A1 §1.13: every power `N_ν^j` maps `E_μ` into itself. -/
theorem nil_pow_mem {A : V →L[ℂ] V} {μ : ℂ} (ν : ℂ) (j : ℕ) {v : V} (hv : v ∈ gE A μ) :
    ((nil A ν) ^ j) v ∈ gE A μ := by
  induction j with
  | zero => simpa using hv
  | succ j ih =>
    rw [pow_succ', mul_apply_eq_comp]
    exact nil_mem ν ih

omit [CompleteSpace V] in
/-- Cochrane (2023), A1 §1.13, p. 583: **the generalised eigenspaces decompose the space**: they
are independent and span it (an internal direct sum), for every operator on a finite-dimensional
complex space — no diagonalisability or Jordan-form hypothesis. -/
theorem isInternal (A : V →L[ℂ] V) : DirectSum.IsInternal fun μ => gE A μ :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨Module.End.independent_maxGenEigenspace _, Module.End.iSup_maxGenEigenspace_eq_top _⟩

/-- Cochrane (2023), A1 §1.13 (the coordinates `Q⁻¹z`): the decomposition of a vector into its
generalised-eigenspace components, as an element of the direct sum. -/
noncomputable def decomp (A : V →L[ℂ] V) : V ≃ₗ[ℂ] DirectSum ℂ fun μ => gE A μ :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun μ => gE A μ) (isInternal A)).symm

/-- Cochrane (2023), A1 §1.13, p. 583 (the selector of the `μ`-modes): the **spectral
projection** onto `E_μ` along the other generalised eigenspaces, as a linear map. -/
noncomputable def projL (A : V →L[ℂ] V) (μ : ℂ) : V →ₗ[ℂ] V :=
  (gE A μ).subtype ∘ₗ (DirectSum.component ℂ ℂ (fun ν => gE A ν) μ) ∘ₗ
    (decomp A).toLinearMap

/-- Cochrane (2023), A1 §1.13, p. 583: the spectral projection onto `E_μ`, a continuous linear
map (finite dimension). -/
noncomputable def proj (A : V →L[ℂ] V) (μ : ℂ) : V →L[ℂ] V :=
  LinearMap.toContinuousLinearMap (projL A μ)

omit [CompleteSpace V] in
/-- Cochrane (2023), A1 §1.13: the projection is the `μ`-coordinate of the decomposition. -/
theorem proj_apply (A : V →L[ℂ] V) (μ : ℂ) (v : V) : proj A μ v = (decomp A v μ : V) := rfl

omit [CompleteSpace V] in
/-- Cochrane (2023), A1 §1.13: `proj A μ v ∈ E_μ`. -/
theorem proj_mem (A : V →L[ℂ] V) (μ : ℂ) (v : V) : proj A μ v ∈ gE A μ :=
  (decomp A v μ).2

omit [CompleteSpace V] in
/-- Cochrane (2023), A1 §1.13: the projection fixes `E_μ`. -/
theorem proj_of_mem {A : V →L[ℂ] V} {μ : ℂ} {v : V} (hv : v ∈ gE A μ) : proj A μ v = v := by
  rw [proj_apply, decomp, (isInternal A).ofBijective_coeLinearMap_of_mem hv]

omit [CompleteSpace V] in
/-- Cochrane (2023), A1 §1.13: the projection onto `E_μ` kills `E_ν` for `ν ≠ μ`. -/
theorem proj_of_mem_ne {A : V →L[ℂ] V} {μ ν : ℂ} (hne : ν ≠ μ) {v : V} (hv : v ∈ gE A ν) :
    proj A μ v = 0 := by
  rw [proj_apply, decomp, (isInternal A).ofBijective_coeLinearMap_of_mem_ne hne hv]
  rfl

omit [CompleteSpace V] in
/-- Cochrane (2023), A1 §1.13, p. 583 (`z = Q z̃`): **every vector is the finite sum of its
generalised-eigenspace components**, which vanish off a finite set of eigenvalues. -/
theorem exists_decomp (A : V →L[ℂ] V) (v : V) :
    ∃ s : Finset ℂ, (∀ μ ∉ s, proj A μ v = 0) ∧ v = ∑ μ ∈ s, proj A μ v := by
  classical
  refine ⟨(decomp A v).support, fun μ hμ => ?_, ?_⟩
  · rw [proj_apply, DFinsupp.notMem_support_iff.1 hμ]
    rfl
  · have h : v = DirectSum.coeLinearMap (fun μ => gE A μ) (decomp A v) :=
      ((LinearEquiv.ofBijective (DirectSum.coeLinearMap fun μ => gE A μ)
        (isInternal A)).apply_symm_apply v).symm
    rw [DirectSum.coeLinearMap_eq_dfinsuppSum] at h
    exact h

/-! ### The exponential on a generalised eigenspace -/

omit [FiniteDimensional ℂ V] in
/-- Cochrane (2023), A1 §1.13, p. 583 (`e^{Jt}` on a Jordan block): **the closed form on a
generalised eigenspace.** If `(A − μ)^m v = 0`, then
`exp(tA) v = e^{μt} ∑_{j<m} (t^j/j!) (A − μ)^j v`. -/
theorem expT_apply_of_pow (A : V →L[ℂ] V) (μ : ℂ) {v : V} {m : ℕ}
    (hv : ((nil A μ) ^ m) v = 0) (t : ℝ) :
    expT A t v = Complex.exp (μ * t) •
      ∑ j ∈ Finset.range m, (t ^ j / (j.factorial : ℝ)) • ((nil A μ) ^ j) v := by
  have hsplit : (t : ℝ) • A = algebraMap ℂ (V →L[ℂ] V) (μ * t) + t • nil A μ := by
    have e : (t : ℝ) • μ • (1 : V →L[ℂ] V) = (μ * t) • 1 := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, mul_comm]
      rfl
    rw [Algebra.algebraMap_eq_smul_one, nil, smul_sub, e]
    abel
  have hr := expSeries_radius_eq_top ℂ (V →L[ℂ] V)
  have hcomm : Commute (algebraMap ℂ (V →L[ℂ] V) (μ * t)) (t • nil A μ) :=
    Algebra.commute_algebraMap_left _ _
  rw [expT, hsplit, exp_add_of_commute_of_mem_ball (𝕂 := ℂ) hcomm (hr.symm ▸ edist_lt_top _ _)
    (hr.symm ▸ edist_lt_top _ _), ← algebraMap_exp_comm, ← Complex.exp_eq_exp_ℂ,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_apply]
  congr 1
  have hs := (exp_series_hasSum_exp' (𝕂 := ℝ) (t • nil A μ)).mapL
    (ContinuousLinearMap.apply ℂ V v)
  have hf : HasSum (fun n : ℕ => ContinuousLinearMap.apply ℂ V v
      (((n.factorial : ℝ)⁻¹) • (t • nil A μ) ^ n))
      (∑ n ∈ Finset.range m, ContinuousLinearMap.apply ℂ V v
        (((n.factorial : ℝ)⁻¹) • (t • nil A μ) ^ n)) := by
    refine hasSum_sum_of_ne_finset_zero fun n hn => ?_
    have hmn : m ≤ n := by simpa using hn
    have hz : ((nil A μ) ^ n) v = 0 := by
      rw [← Nat.sub_add_cancel hmn, pow_add, mul_apply_eq_comp, hv, map_zero]
    simp [smul_pow, hz]
  simp only [ContinuousLinearMap.apply_apply] at hs hf
  rw [hs.unique hf]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [smul_apply, smul_pow, smul_smul]
  congr 1
  ring

omit [FiniteDimensional ℂ V] in
/-- Cochrane (2023), A1 §1.13: `exp(tA)` maps the generalised eigenspace `E_μ` into itself. -/
theorem expT_mem {A : V →L[ℂ] V} {μ : ℂ} {v : V} (hv : v ∈ gE A μ) (t : ℝ) :
    expT A t v ∈ gE A μ := by
  obtain ⟨m, hm⟩ := (mem_gE_iff A μ v).1 hv
  rw [expT_apply_of_pow A μ hm t]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ =>
    Submodule.smul_of_tower_mem _ _ (nil_pow_mem μ j hv))

/-! ### Asymptotics of a generalised-eigenvector component -/

open Classical in
/-- Cochrane (2023), A1 §1.13 (the length of a Jordan chain): for `v ∈ E_μ`, the largest `k`
with `(A − μ)^k v ≠ 0` (`0` if no power kills `v`, which cannot happen on `E_μ`). -/
noncomputable def chainLen (A : V →L[ℂ] V) (μ : ℂ) (v : V) : ℕ :=
  if h : ∃ m : ℕ, ((nil A μ) ^ (m + 1)) v = 0 then Nat.find h else 0

omit [CompleteSpace V] [FiniteDimensional ℂ V] in
/-- Cochrane (2023), A1 §1.13: for `v ∈ E_μ` with chain length `k`, `(A − μ)^{k+1} v = 0`, and
`(A − μ)^k v ≠ 0` when `v ≠ 0`. -/
theorem chainLen_spec {A : V →L[ℂ] V} {μ : ℂ} {v : V} (hv : v ∈ gE A μ) :
    ((nil A μ) ^ (chainLen A μ v + 1)) v = 0 ∧
      (v ≠ 0 → ((nil A μ) ^ (chainLen A μ v)) v ≠ 0) := by
  classical
  obtain ⟨m, hm⟩ := (mem_gE_iff A μ v).1 hv
  have h : ∃ m : ℕ, ((nil A μ) ^ (m + 1)) v = 0 :=
    ⟨m, by rw [pow_succ', mul_apply_eq_comp, hm, map_zero]⟩
  have hk : chainLen A μ v = Nat.find h := by
    unfold chainLen
    simp only [h, ↓reduceDIte]
  rw [hk]
  refine ⟨Nat.find_spec h, fun hv0 => ?_⟩
  rcases hfk : Nat.find h with _ | j
  · simpa using hv0
  · exact Nat.find_min h (by omega : j < Nat.find h)

omit [CompleteSpace V] [FiniteDimensional ℂ V] in
/-- Cochrane (2023), A1 §1.13: every power beyond the chain length kills `v ∈ E_μ`. -/
theorem nil_pow_eq_zero_of_lt {A : V →L[ℂ] V} {μ : ℂ} {v : V} (hv : v ∈ gE A μ) {j : ℕ}
    (hj : chainLen A μ v < j) : ((nil A μ) ^ j) v = 0 := by
  rw [← Nat.sub_add_cancel (Nat.succ_le_of_lt hj), pow_add, mul_apply_eq_comp,
    (chainLen_spec hv).1, map_zero]

omit [FiniteDimensional ℂ V] in
/-- Cochrane (2023), A1 §1.13 (tool): `‖exp(tA)v‖ = e^{(Re μ)t} ‖∑_{j≤k} (t^j/j!) N^j v‖` on
`E_μ`. -/
theorem norm_expT_apply {A : V →L[ℂ] V} {μ : ℂ} {v : V} {m : ℕ}
    (hv : ((nil A μ) ^ m) v = 0) (t : ℝ) :
    ‖expT A t v‖ = Real.exp (μ.re * t) *
      ‖∑ j ∈ Finset.range m, (t ^ j / (j.factorial : ℝ)) • ((nil A μ) ^ j) v‖ := by
  rw [expT_apply_of_pow A μ hv t, norm_smul, Complex.norm_exp]
  simp

omit [CompleteSpace V] [FiniteDimensional ℂ V] in
/-- Cochrane (2023), A1 §1.13 (tool): the normalised polynomial part
`∑_{j≤k} (t^j/(j! t^k)) N^j v` tends to `N^k v / k!`. -/
theorem tendsto_poly_part (A : V →L[ℂ] V) (μ : ℂ) (v : V) (k : ℕ) :
    Tendsto (fun t : ℝ => ∑ j ∈ Finset.range (k + 1),
        (t ^ j / (j.factorial : ℝ) / t ^ k) • ((nil A μ) ^ j) v) atTop
      (𝓝 (((k.factorial : ℝ))⁻¹ • ((nil A μ) ^ k) v)) := by
  simp only [Finset.sum_range_succ]
  rw [show (((k.factorial : ℝ))⁻¹ • ((nil A μ) ^ k) v) =
    (0 : V) + ((k.factorial : ℝ))⁻¹ • ((nil A μ) ^ k) v by rw [zero_add]]
  refine Tendsto.add ?_ ?_
  · rw [show (0 : V) = ∑ j ∈ Finset.range k, (0 : ℝ) • ((nil A μ) ^ j) v by simp]
    refine tendsto_finsetSum _ fun j hj => ?_
    refine Tendsto.smul_const ?_ _
    have hjk : j < k := Finset.mem_range.1 hj
    have h0 : Tendsto (fun t : ℝ => ((j.factorial : ℝ))⁻¹ * (t⁻¹) ^ (k - j)) atTop (𝓝 0) := by
      have := (tendsto_inv_atTop_zero.pow (k - j)).const_mul ((j.factorial : ℝ))⁻¹
      rwa [zero_pow (by omega), mul_zero] at this
    refine h0.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    have htk : t ^ k = t ^ j * t ^ (k - j) := by rw [← pow_add, Nat.add_sub_cancel' hjk.le]
    rw [htk, inv_pow]
    field_simp
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    have : t ^ k ≠ 0 := pow_ne_zero _ ht.ne'
    congr 1
    field_simp

omit [FiniteDimensional ℂ V] in
/-- Cochrane (2023), A1 §1.13, p. 583: **the growth of a generalised-eigenvector component.**
For `0 ≠ v ∈ E_μ` with chain length `k`,
`‖exp(tA) v‖ / (t^k e^{(Re μ)t}) → ‖(A − μ)^k v‖ / k!`, and the limit is positive: the component
grows exactly like `t^k e^{(Re μ)t}`. -/
theorem tendsto_norm_expT_div {A : V →L[ℂ] V} {μ : ℂ} {v : V} (hv : v ∈ gE A μ) (hv0 : v ≠ 0) :
    Tendsto (fun t : ℝ => ‖expT A t v‖ / (t ^ chainLen A μ v * Real.exp (μ.re * t))) atTop
        (𝓝 (‖((nil A μ) ^ chainLen A μ v) v‖ / (chainLen A μ v).factorial)) ∧
      0 < ‖((nil A μ) ^ chainLen A μ v) v‖ / (chainLen A μ v).factorial := by
  set k := chainLen A μ v
  refine ⟨?_, div_pos (norm_pos_iff.2 ((chainLen_spec hv).2 hv0)) (by positivity)⟩
  have h := (tendsto_poly_part A μ v k).norm
  rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_eq_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [norm_expT_apply (chainLen_spec hv).1 t]
  have hp : 0 < t ^ k := pow_pos ht k
  have he : 0 < Real.exp (μ.re * t) := Real.exp_pos _
  have hsum : ∑ j ∈ Finset.range (k + 1), (t ^ j / (j.factorial : ℝ) / t ^ k) •
      ((nil A μ) ^ j) v = (t ^ k)⁻¹ • ∑ j ∈ Finset.range (k + 1),
        (t ^ j / (j.factorial : ℝ)) • ((nil A μ) ^ j) v := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul]
    congr 1
    ring
  rw [hsum, norm_smul, Real.norm_of_nonneg (by positivity)]
  field_simp
  rfl

omit [FiniteDimensional ℂ V] in
/-- Cochrane (2023), A1 §1.13, p. 583: **a stable component decays**: for `v ∈ E_μ` with
`Re μ < 0`, `exp(tA) v → 0` (whatever the size of the Jordan block). -/
theorem tendsto_expT_zero {A : V →L[ℂ] V} {μ : ℂ} {v : V} (hv : v ∈ gE A μ) (hre : μ.re < 0) :
    Tendsto (fun t : ℝ => expT A t v) atTop (𝓝 0) := by
  by_cases hv0 : v = 0
  · simp [hv0]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  obtain ⟨h1, -⟩ := tendsto_norm_expT_div hv hv0
  set k := chainLen A μ v
  have h2 : Tendsto (fun t : ℝ => t ^ k * Real.exp (μ.re * t)) atTop (𝓝 0) := by
    have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) (-μ.re) (by linarith)
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [Real.rpow_natCast, neg_neg]
  have h3 := h1.mul h2
  rw [mul_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have : t ^ k * Real.exp (μ.re * t) ≠ 0 := by positivity
  field_simp

omit [FiniteDimensional ℂ V] in
/-- Cochrane (2023), A1 §1.13, pp. 583–585: **the bounded-component criterion** (no Jordan
hypothesis). For `v ∈ E_μ`, `t ↦ exp(tA) v` is bounded on `[0, ∞)` iff (`Re μ > 0 ⇒ v = 0`) and
(`Re μ = 0 ⇒ (A − μ) v = 0`): explosive components must vanish, and on the imaginary axis only
eigenvectors (not longer Jordan chains) survive. -/
theorem bounded_expT_iff {A : V →L[ℂ] V} {μ : ℂ} {v : V} (hv : v ∈ gE A μ) :
    (∃ K, ∀ t, 0 ≤ t → ‖expT A t v‖ ≤ K) ↔
      (0 < μ.re → v = 0) ∧ (μ.re = 0 → nil A μ v = 0) := by
  constructor
  · rintro ⟨K, hK⟩
    -- an unbounded lower bound gives a contradiction
    have key : ∀ (hv0 : v ≠ 0), ¬ Tendsto (fun t : ℝ => t ^ chainLen A μ v *
        Real.exp (μ.re * t)) atTop atTop := by
      intro hv0 hT
      obtain ⟨h1, hL⟩ := tendsto_norm_expT_div hv hv0
      set L := ‖((nil A μ) ^ chainLen A μ v) v‖ / (chainLen A μ v).factorial
      have hev : ∀ᶠ t : ℝ in atTop, L / 2 < ‖expT A t v‖ /
          (t ^ chainLen A μ v * Real.exp (μ.re * t)) :=
        h1.eventually (lt_mem_nhds (by linarith))
      have hbig : Tendsto (fun t : ℝ => L / 2 * (t ^ chainLen A μ v *
          Real.exp (μ.re * t))) atTop atTop := hT.const_mul_atTop (by linarith)
      obtain ⟨t, ht1, ht2, ht3⟩ := (hev.and ((hbig.eventually_gt_atTop K).and
        (eventually_gt_atTop 0))).exists
      have hpos : 0 < t ^ chainLen A μ v * Real.exp (μ.re * t) := by positivity
      rw [lt_div_iff₀ hpos] at ht1
      linarith [hK t ht3.le]
    refine ⟨fun hre => ?_, fun hre => ?_⟩
    · by_contra hv0
      refine key hv0 (tendsto_atTop_mono' _ ?_
        (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hre)))
      filter_upwards [eventually_ge_atTop 1] with t ht
      simp only [Function.comp_apply, id]
      exact le_mul_of_one_le_left (Real.exp_pos _).le (one_le_pow₀ ht)
    · by_contra hN
      have hv0 : v ≠ 0 := fun h => hN (by rw [h, map_zero])
      have hk : 1 ≤ chainLen A μ v := by
        by_contra h0
        have h0' : chainLen A μ v = 0 := by omega
        have := (chainLen_spec hv).1
        rw [h0', zero_add, pow_one] at this
        exact hN this
      refine key hv0 (tendsto_atTop_mono' _ ?_ tendsto_id)
      filter_upwards [eventually_ge_atTop 1] with t ht
      rw [hre, zero_mul, Real.exp_zero, mul_one]
      exact le_self_pow₀ ht (by omega)
  · rintro ⟨h1, h2⟩
    by_cases hv0 : v = 0
    · exact ⟨0, fun t _ => by simp [hv0]⟩
    rcases lt_trichotomy μ.re 0 with hre | hre | hre
    · -- decay, then compactness on `[0, T]`
      have hT := tendsto_expT_zero hv hre
      rw [tendsto_zero_iff_norm_tendsto_zero] at hT
      obtain ⟨T, hT⟩ := eventually_atTop.1 (hT.eventually (gt_mem_nhds zero_lt_one))
      have hcont : ContinuousOn (fun t : ℝ => ‖expT A t v‖) (Set.Icc 0 T) :=
        ((continuous_expT A).clm_apply continuous_const).norm.continuousOn
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
      refine ⟨max C 1, fun t ht => ?_⟩
      rcases le_total t T with htT | htT
      · have := hC t ⟨ht, htT⟩
        rw [Real.norm_of_nonneg (norm_nonneg _)] at this
        exact this.trans (le_max_left _ _)
      · exact (hT t htT).le.trans (le_max_right _ _)
    · have hN := h2 hre
      refine ⟨‖v‖, fun t _ => ?_⟩
      have hv1 : ((nil A μ) ^ 1) v = 0 := by rw [pow_one]; exact hN
      rw [norm_expT_apply hv1 t, hre]
      simp
    · exact absurd (h1 hre) hv0

end Cochrane.StickyPriceFiscal.TidyR6GenEigen
