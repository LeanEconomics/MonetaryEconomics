/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.TidyR6GenEigen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# The continuous-time matrix method without a Jordan-decomposition hypothesis

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.13,
pp. 580–585 (eqs. (1.52)–(1.53) and the Table 5.2 integrals), the method used for §§5.7.3–5.7.5.

`CTRules` (`CTRules.matrix_solution`, `CTRules.matrix_bounded_iff`, `CTRules.matrix_errors`,
`CTRules.matrix_errors_unique`, `CTRules.matrix_pv`) assumes `A = QΛQ⁻¹` with real diagonal
`Λ`; `CTMatrixMethod` assumes a Jordan decomposition. Here every result holds for **every**
operator `A` on a finite-dimensional complex
normed space, through the spectral projections `TidyR6GenEigen.proj A μ` onto the generalised
eigenspaces and the matrix exponential `TidyR6GenEigen.expT`; real matrices are handled by
complexification (`cplx`).

The book's selector "`z̃_+ = 0`" becomes `Good A v`: for every `μ`, the `μ`-component of `v`
vanishes if `Re μ > 0`, and is an eigenvector (`(A − μ)` kills it) if `Re μ = 0`.

## Main results

* `proj_expT`, `solution_decomp`, `solution_formula`: `z_t = exp(tA) z_0 = ∑_μ exp(tA) P_μ z_0`
  and, explicitly, `∑_μ e^{μt} ∑_{j<n} (t^j/j!) (A − μ)^j P_μ z_0` (`n` the dimension).
* **`bounded_iff`**: a solution of `z' = Az` after the news is bounded on `[0, ∞)` iff
  `Good A z_0`. `good_expT`: the bounded subspace is invariant.
* (1.53): `errors_iff` (the expectational errors are pinned by the explosive and the defective
  imaginary-axis components), `errors_unique` (they are unique when `Cη` is never in the
  bounded subspace for `η ≠ 0`), `errors_exist` (they exist when the bounded subspace and the
  range of `C` span the space).
* Table 5.2 integrals: **`pv`**: for a bounded response and `r > 0`,
  `I = ∫_0^∞ e^{−rt} z_t dt` satisfies `(r − A) I = z_0`, lies in the bounded subspace, and is the
  only such vector (so `I = (r − A)⁻¹ z_0` whenever `r` is not an eigenvalue).
* Real systems: `cplx`, `real_bounded_iff`, `real_pv`.
-/

namespace Cochrane.StickyPriceFiscal.TidyR6MatrixMethod

open Filter Topology MeasureTheory TidyR6GenEigen

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V]

/-- Cochrane (2023), A1 §1.13, p. 583 ("`z̃_+ = 0`"), without a diagonalisation: `v` has no
explosive component, and its components on the imaginary axis are eigenvectors. -/
def Good (A : V →L[ℂ] V) (v : V) : Prop :=
  ∀ μ : ℂ, (0 < μ.re → proj A μ v = 0) ∧ (μ.re = 0 → nil A μ (proj A μ v) = 0)

omit [CompleteSpace V] in
/-- Cochrane (2023), A1 §1.13 (tool): `Good A` is closed under linear combinations. -/
theorem good_comb {A : V →L[ℂ] V} {v w : V} (hv : Good A v) (hw : Good A w) (a b : ℂ) :
    Good A (a • v + b • w) := by
  intro μ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [map_add, map_smul, map_smul, (hv μ).1 h, (hw μ).1 h, smul_zero, smul_zero, add_zero]
  · rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul, (hv μ).2 h, (hw μ).2 h,
      smul_zero, smul_zero, add_zero]

omit [CompleteSpace V] in
/-- Cochrane (2023), A1 §1.13 (tool): `Good A` is closed under subtraction. -/
theorem good_sub {A : V →L[ℂ] V} {v w : V} (hv : Good A v) (hw : Good A w) :
    Good A (v - w) := by
  have h := good_comb hv hw 1 (-1)
  rwa [one_smul, neg_one_smul, ← sub_eq_add_neg] at h

/-- Cochrane (2023), A1 §1.13: the spectral projections commute with `exp(tA)`. -/
theorem proj_expT (A : V →L[ℂ] V) (μ : ℂ) (v : V) (t : ℝ) :
    proj A μ (expT A t v) = expT A t (proj A μ v) := by
  obtain ⟨s, hs0, hs⟩ := exists_decomp A v
  conv_lhs => rw [hs, map_sum, map_sum]
  by_cases hμ : μ ∈ s
  · rw [Finset.sum_eq_single μ (fun ν _ hν => proj_of_mem_ne hν (expT_mem (proj_mem A ν v) t))
      (fun h => absurd hμ h)]
    exact proj_of_mem (expT_mem (proj_mem A μ v) t)
  · rw [Finset.sum_eq_zero fun ν hν => proj_of_mem_ne (by rintro rfl; exact hμ hν)
      (expT_mem (proj_mem A ν v) t), hs0 μ hμ, map_zero]

omit [CompleteSpace V] [FiniteDimensional ℂ V] in
/-- Cochrane (2023), A1 §1.13 (tool): `A − μ` commutes with `exp(tA)`. -/
theorem nil_expT (A : V →L[ℂ] V) (μ : ℂ) (t : ℝ) (v : V) :
    nil A μ (expT A t v) = expT A t (nil A μ v) := by
  have h := commute_expT A t
  simp only [nil, sub_apply, smul_apply,
    one_apply_eq_self, map_sub, map_smul]
  rw [← mul_apply_eq_comp, h.eq, mul_apply_eq_comp]

/-- Cochrane (2023), A1 §1.13: the bounded subspace is invariant under `exp(tA)`. -/
theorem good_expT {A : V →L[ℂ] V} {v : V} (hv : Good A v) (t : ℝ) : Good A (expT A t v) := by
  intro μ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [proj_expT, (hv μ).1 h, map_zero]
  · rw [proj_expT, nil_expT, (hv μ).2 h, map_zero]

/-- Cochrane (2023), A1 §1.13, pp. 581–583: **the solution, component by component**: along
`z' = Az` after the news, `z_t = ∑_{μ ∈ s} exp(tA) P_μ z_0` for a finite set `s` of eigenvalues
(and `P_μ z_0 = 0` off `s`). -/
theorem solution_decomp {A : V →L[ℂ] V} {z : ℝ → V} (hc : ContinuousOn z (Set.Ici 0))
    (hd : ∀ t, 0 < t → HasDerivAt z (A (z t)) t) :
    ∃ s : Finset ℂ, (∀ μ ∉ s, proj A μ (z 0) = 0) ∧
      ∀ t, 0 ≤ t → z t = ∑ μ ∈ s, expT A t (proj A μ (z 0)) := by
  obtain ⟨s, hs0, hs⟩ := exists_decomp A (z 0)
  refine ⟨s, hs0, fun t ht => ?_⟩
  rw [ode_unique hc hd t ht]
  conv_lhs => rw [hs]
  rw [map_sum]

/-- Cochrane (2023), A1 §1.13, p. 583 (`z_t = Q e^{Jt} Q⁻¹ z_0`), **hypothesis-free closed
form**: with `n = dim V`, `z_t = ∑_{μ ∈ s} e^{μt} ∑_{j<n} (t^j/j!) (A − μ)^j P_μ z_0`. -/
theorem solution_formula {A : V →L[ℂ] V} {z : ℝ → V} (hc : ContinuousOn z (Set.Ici 0))
    (hd : ∀ t, 0 < t → HasDerivAt z (A (z t)) t) :
    ∃ s : Finset ℂ, (∀ μ ∉ s, proj A μ (z 0) = 0) ∧ ∀ t, 0 ≤ t → z t =
      ∑ μ ∈ s, Complex.exp (μ * t) • ∑ j ∈ Finset.range (Module.finrank ℂ V),
        (t ^ j / (j.factorial : ℝ)) • ((nil A μ) ^ j) (proj A μ (z 0)) := by
  obtain ⟨s, hs0, hs⟩ := solution_decomp hc hd
  refine ⟨s, hs0, fun t ht => ?_⟩
  rw [hs t ht]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hm : ((nil A μ) ^ Module.finrank ℂ V) (proj A μ (z 0)) = 0 := by
    have h := proj_mem A μ (z 0)
    rw [gE, Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
      Module.End.mem_genEigenspace_nat, LinearMap.mem_ker] at h
    rw [nil_pow_apply]
    exact h
  exact expT_apply_of_pow A μ hm t

/-- Cochrane (2023), A1 §1.13, p. 583 ("to have `E_t z̃_{t+j}` not explode, we must have
`z̃_+ = 0`"), **for every matrix**: a solution of `z' = Az` after the news (continuous on
`[0, ∞)`) is bounded on `[0, ∞)` iff `Good A z_0`: no component on a generalised eigenspace with
`Re μ > 0`, and only eigenvector components for `Re μ = 0`. -/
theorem bounded_iff {A : V →L[ℂ] V} {z : ℝ → V} (hc : ContinuousOn z (Set.Ici 0))
    (hd : ∀ t, 0 < t → HasDerivAt z (A (z t)) t) :
    (∃ K, ∀ t, 0 ≤ t → ‖z t‖ ≤ K) ↔ Good A (z 0) := by
  constructor
  · rintro ⟨K, hK⟩ μ
    refine (bounded_expT_iff (proj_mem A μ (z 0))).1 ⟨‖proj A μ‖ * K, fun t ht => ?_⟩
    rw [← proj_expT, ← ode_unique hc hd t ht]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_left (hK t ht) (norm_nonneg _))
  · intro hg
    obtain ⟨s, -, hs⟩ := solution_decomp hc hd
    have hb : ∀ μ, ∃ K, ∀ t, 0 ≤ t → ‖expT A t (proj A μ (z 0))‖ ≤ K := fun μ =>
      (bounded_expT_iff (proj_mem A μ (z 0))).2 (hg μ)
    choose K hK using hb
    refine ⟨∑ μ ∈ s, K μ, fun t ht => ?_⟩
    rw [hs t ht]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ => hK μ t ht)

/-- Cochrane (2023), A1 §1.13, p. 583, (1.53), **for every matrix**: after a shock `ε` with
expectational errors `δ` (`z_0 = Bε + Cδ`), the response is bounded iff on every explosive
generalised eigenspace `P_μ Cδ = −P_μ Bε`, and on every imaginary-axis one
`(A − μ) P_μ Cδ = −(A − μ) P_μ Bε`. -/
theorem errors_iff {W₁ W₂ : Type*} [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂]
    [Module ℂ W₂] {A : V →L[ℂ] V} {B : W₁ →ₗ[ℂ] V} {C : W₂ →ₗ[ℂ] V} {ε : W₁} {δ : W₂}
    {z : ℝ → V} (hc : ContinuousOn z (Set.Ici 0)) (hd : ∀ t, 0 < t → HasDerivAt z (A (z t)) t)
    (h0 : z 0 = B ε + C δ) :
    (∃ K, ∀ t, 0 ≤ t → ‖z t‖ ≤ K) ↔ ∀ μ : ℂ,
      (0 < μ.re → proj A μ (C δ) = -proj A μ (B ε)) ∧
        (μ.re = 0 → nil A μ (proj A μ (C δ)) = -nil A μ (proj A μ (B ε))) := by
  rw [bounded_iff hc hd, h0]
  refine forall_congr' fun μ => and_congr (imp_congr_right fun _ => ?_)
    (imp_congr_right fun _ => ?_)
  · rw [map_add, add_comm, add_eq_zero_iff_eq_neg]
  · rw [map_add, map_add, add_comm, add_eq_zero_iff_eq_neg]

/-- Cochrane (2023), A1 §1.13, p. 583 ("so long as `Q₊⁻¹C` is invertible"), **for every matrix**:
if no nonzero `Cη` lies in the bounded subspace, two bounded responses to the same shock `ε`
have the same expectational errors. -/
theorem errors_unique {W₁ W₂ : Type*} [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂]
    [Module ℂ W₂] {A : V →L[ℂ] V} {B : W₁ →ₗ[ℂ] V} {C : W₂ →ₗ[ℂ] V} {ε : W₁} {δ δ' : W₂}
    (hinj : ∀ η : W₂, Good A (C η) → η = 0) {z z' : ℝ → V} (hc : ContinuousOn z (Set.Ici 0))
    (hd : ∀ t, 0 < t → HasDerivAt z (A (z t)) t) (h0 : z 0 = B ε + C δ)
    (hb : ∃ K, ∀ t, 0 ≤ t → ‖z t‖ ≤ K) (hc' : ContinuousOn z' (Set.Ici 0))
    (hd' : ∀ t, 0 < t → HasDerivAt z' (A (z' t)) t) (h0' : z' 0 = B ε + C δ')
    (hb' : ∃ K, ∀ t, 0 ≤ t → ‖z' t‖ ≤ K) : δ = δ' := by
  have g := (bounded_iff hc hd).1 hb
  have g' := (bounded_iff hc' hd').1 hb'
  rw [h0] at g
  rw [h0'] at g'
  have := hinj (δ - δ') (by
    have h := good_sub g g'
    rwa [add_sub_add_left_eq_sub, ← map_sub] at h)
  exact sub_eq_zero.1 this

/-- Cochrane (2023), A1 §1.13, p. 583 (existence of the expectational errors), **for every
matrix**: if every vector is a bounded-subspace vector plus some `Cη`, then for every shock `ε`
there are errors `δ` whose response `t ↦ exp(tA)(Bε + Cδ)` solves `z' = Az` and is bounded. -/
theorem errors_exist {W₁ W₂ : Type*} [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂]
    [Module ℂ W₂] {A : V →L[ℂ] V} {B : W₁ →ₗ[ℂ] V} {C : W₂ →ₗ[ℂ] V}
    (hspan : ∀ w : V, ∃ η : W₂, Good A (w + C η)) (ε : W₁) :
    ∃ δ : W₂, (∀ t, HasDerivAt (fun u => expT A u (B ε + C δ))
        (A (expT A t (B ε + C δ))) t) ∧
      ∃ K, ∀ t, 0 ≤ t → ‖expT A t (B ε + C δ)‖ ≤ K := by
  obtain ⟨δ, hδ⟩ := hspan (B ε)
  refine ⟨δ, fun t => hasDerivAt_expT_apply A _ t, ?_⟩
  have hc : ContinuousOn (fun u => expT A u (B ε + C δ)) (Set.Ici 0) :=
    ((continuous_expT A).clm_apply continuous_const).continuousOn
  have h := (bounded_iff hc fun t _ => hasDerivAt_expT_apply A (B ε + C δ) t).2
  simp only [expT_zero, one_apply_eq_self] at h
  exact h hδ

/-! ### The discounted integrals of Table 5.2 -/

/-- Cochrane (2023), A1 §1.13, p. 585 (Table 5.2 terms, `∫ e^{(A − rI)τ} dτ = (rI − A)⁻¹`), **for
every matrix**: for a bounded response `z` of `z' = Az` and `r > 0`, the discounted integral
`I = ∫_0^∞ e^{−rt} z_t dt` satisfies `(r − A) I = z_0`, lies in the bounded subspace, and is the
**only** vector of the bounded subspace with `(r − A) I = z_0`. -/
theorem pv {A : V →L[ℂ] V} {z : ℝ → V} {r : ℝ} (hr : 0 < r) (hc : ContinuousOn z (Set.Ici 0))
    (hd : ∀ t, 0 < t → HasDerivAt z (A (z t)) t) (hb : ∃ K, ∀ t, 0 ≤ t → ‖z t‖ ≤ K) :
    (r : ℂ) • (∫ t in Set.Ioi 0, Real.exp (-(r * t)) • z t) -
        A (∫ t in Set.Ioi 0, Real.exp (-(r * t)) • z t) = z 0 ∧
      Good A (∫ t in Set.Ioi 0, Real.exp (-(r * t)) • z t) ∧
      ∀ w : V, Good A w → (r : ℂ) • w - A w = z 0 →
        w = ∫ t in Set.Ioi 0, Real.exp (-(r * t)) • z t := by
  obtain ⟨K, hK⟩ := hb
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 le_rfl)
  set I := ∫ t in Set.Ioi 0, Real.exp (-(r * t)) • z t
  -- integrability of `e^{−rt} L z_t` for any continuous linear `L`
  have hint : ∀ L : V →L[ℂ] V, IntegrableOn (fun t => Real.exp (-(r * t)) • L (z t))
      (Set.Ioi 0) := by
    intro L
    have hm : AEStronglyMeasurable (fun t => Real.exp (-(r * t)) • L (z t))
        (volume.restrict (Set.Ioi 0)) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      exact ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(r * t))).continuousOn.smul
        (L.continuous.comp_continuousOn (hc.mono Set.Ioi_subset_Ici_self)))
    refine Integrable.mono' ((CTSimple.integrableOn_exp_Ioi hr).const_mul (‖L‖ * K)) hm ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
    exact mul_le_mul_of_nonneg_right ((L.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hK t (le_of_lt ht)) (norm_nonneg _))) (Real.exp_pos _).le
  have hint1 : IntegrableOn (fun t => Real.exp (-(r * t)) • z t) (Set.Ioi 0) := by
    simpa using hint 1
  -- the good subspace at every date
  have hgood : ∀ t, 0 ≤ t → Good A (z t) := by
    intro t ht
    rw [ode_unique hc hd t ht]
    exact good_expT ((bounded_iff hc hd).1 ⟨K, hK⟩) t
  -- (r − A) I = z_0 by integrating the derivative of `e^{−rt} z_t`
  have hflow : (r : ℂ) • I - A I = z 0 := by
    have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun u => Real.exp (-(r * u)) • z u)
        (Real.exp (-(r * t)) • A (z t) + (-r) • (Real.exp (-(r * t)) • z t)) t := by
      intro t ht
      have h1 : HasDerivAt (fun u : ℝ => -(r * u)) (-r) t := by
        have := (hasDerivAt_id t).const_mul (-r)
        simp only [id, mul_one] at this
        convert this using 1
        funext u
        ring
      exact (h1.exp.smul (hd t ht)).congr_deriv (by rw [smul_smul, mul_comm (-r)])
    have hcont : ContinuousWithinAt (fun u => Real.exp (-(r * u)) • z u) (Set.Ici 0) 0 :=
      ((by fun_prop : Continuous fun u : ℝ => Real.exp (-(r * u))).continuousWithinAt).smul
        (hc 0 (Set.mem_Ici.2 le_rfl))
    have hlim : Tendsto (fun u => Real.exp (-(r * u)) • z u) atTop (𝓝 0) := by
      have h0 : Tendsto (fun u : ℝ => K * Real.exp (-(r * u))) atTop (𝓝 0) := by
        have := (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hr)).inv_tendsto_atTop
        have h2 := this.const_mul K
        rw [mul_zero] at h2
        refine h2.congr fun u => ?_
        simp [Real.exp_neg]
      refine squeeze_zero_norm' ?_ h0
      filter_upwards [eventually_ge_atTop 0] with u hu
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
      exact mul_le_mul_of_nonneg_right (hK u hu) (Real.exp_pos _).le
    have hi2 : IntegrableOn (fun t => (-r) • (Real.exp (-(r * t)) • z t)) (Set.Ioi 0) :=
      hint1.smul (-r)
    have hI := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
      ((hint A).add hi2) hlim
    rw [integral_add (hint A) hi2] at hI
    have e1 : ∫ t in Set.Ioi 0, Real.exp (-(r * t)) • A (z t) = A I := by
      rw [← ContinuousLinearMap.integral_comp_comm A hint1]
      congr 1
      funext t
      exact (A.map_smul_of_tower _ _).symm
    have e2 : ∫ t in Set.Ioi 0, (-r) • (Real.exp (-(r * t)) • z t) = (-r) • I :=
      integral_smul _ _
    rw [e1, e2] at hI
    simp only [zero_sub, mul_zero, neg_zero, Real.exp_zero, one_smul] at hI
    rw [Complex.coe_smul]
    rw [neg_smul] at hI
    linear_combination (norm := module) -hI
  -- `I` is in the bounded subspace
  have hIgood : Good A I := by
    intro μ
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [← ContinuousLinearMap.integral_comp_comm _ hint1]
      refine (setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_).trans
        (integral_zero _ _)
      rw [ContinuousLinearMap.map_smul_of_tower, (hgood t (le_of_lt ht) μ).1 h, smul_zero]
    · rw [← ContinuousLinearMap.comp_apply,
        ← ContinuousLinearMap.integral_comp_comm _ hint1]
      refine (setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_).trans
        (integral_zero _ _)
      rw [ContinuousLinearMap.map_smul_of_tower, ContinuousLinearMap.comp_apply,
        (hgood t (le_of_lt ht) μ).2 h, smul_zero]
  refine ⟨hflow, hIgood, fun w hw hwe => ?_⟩
  -- uniqueness: `(r − A)` is injective on the bounded subspace
  set d := w - I
  have hdg : Good A d := good_sub hw hIgood
  have hAd : nil A (r : ℂ) d = 0 := by
    simp only [d, nil, sub_apply, smul_apply,
      one_apply_eq_self, map_sub]
    linear_combination (norm := module) hflow - hwe
  have hmem : d ∈ gE A (r : ℂ) := (mem_gE_iff A _ d).2 ⟨1, by rw [pow_one]; exact hAd⟩
  have h0 := (hdg (r : ℂ)).1 (by simpa using hr)
  rw [proj_of_mem hmem] at h0
  exact sub_eq_zero.1 h0

/-! ### Real systems by complexification -/

/-- Cochrane (2023), A1 §1.13 (the book's matrices are real): the complexification of a real
`n × n` matrix, as an operator on `ℂⁿ`. -/
noncomputable def cplx {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (A.map Complex.ofRealHom))

/-- Cochrane (2023), A1 §1.13 (tool): the complexified operator acts by the complexified matrix. -/
theorem cplx_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℂ) :
    cplx A w = (A.map Complex.ofRealHom).mulVec w := rfl

/-- Cochrane (2023), A1 §1.13 (tool): a real solution of `z' = Az`, complexified, solves the
complexified system. -/
theorem cplx_solution {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {z : ℝ → Fin n → ℝ}
    (hc : ContinuousOn z (Set.Ici 0)) (hd : ∀ t, 0 < t → HasDerivAt z (A.mulVec (z t)) t) :
    ContinuousOn (fun t j => (z t j : ℂ)) (Set.Ici 0) ∧
      ∀ t, 0 < t → HasDerivAt (fun t j => (z t j : ℂ)) (cplx A (fun j => (z t j : ℂ))) t := by
  refine ⟨continuousOn_pi.2 fun j => Complex.continuous_ofReal.comp_continuousOn
    ((continuous_apply j).comp_continuousOn hc), fun t ht => ?_⟩
  refine hasDerivAt_pi.2 fun j => ?_
  have h := (hasDerivAt_pi.1 (hd t ht) j).ofReal_comp
  rw [cplx_apply]
  have e : (A.map Complex.ofRealHom).mulVec (fun j => (z t j : ℂ)) j =
      ((A.mulVec (z t) j : ℝ) : ℂ) := by
    have := RingHom.map_mulVec Complex.ofRealHom A (z t) j
    simpa [Function.comp_def] using this.symm
  rw [e]
  exact h

/-- Cochrane (2023), A1 §1.13, p. 583, **every real matrix**: a real solution of `z' = Az` after
the news is bounded on `[0, ∞)` iff its complexified initial value satisfies `Good` for the
complexified matrix. -/
theorem real_bounded_iff {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {z : ℝ → Fin n → ℝ}
    (hc : ContinuousOn z (Set.Ici 0)) (hd : ∀ t, 0 < t → HasDerivAt z (A.mulVec (z t)) t) :
    (∃ K, ∀ t, 0 ≤ t → ∀ j, |z t j| ≤ K) ↔ Good (cplx A) (fun j => (z 0 j : ℂ)) := by
  obtain ⟨hcc, hdc⟩ := cplx_solution hc hd
  rw [← bounded_iff hcc hdc]
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨max K 0, fun t ht => (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun j => ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (hK t ht j).trans (le_max_left _ _)
  · rintro ⟨K, hK⟩
    refine ⟨K, fun t ht j => ?_⟩
    have := (norm_le_pi_norm (fun j => (z t j : ℂ)) j).trans (hK t ht)
    rwa [Complex.norm_real, Real.norm_eq_abs] at this

/-- Cochrane (2023), A1 §1.13, p. 585 (Table 5.2 terms), **every real matrix**: for a bounded real
response `z` of `z' = Az` and `r > 0`, the discounted integrals `I_j = ∫_0^∞ e^{−rt} z_{t,j} dt`
satisfy `rI − AI = z_0`, `I` (complexified) lies in the bounded subspace, and `I` is the only real
vector with these two properties. -/
theorem real_pv {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {z : ℝ → Fin n → ℝ} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn z (Set.Ici 0)) (hd : ∀ t, 0 < t → HasDerivAt z (A.mulVec (z t)) t)
    (hb : ∃ K, ∀ t, 0 ≤ t → ∀ j, |z t j| ≤ K) :
    r • (fun j => ∫ t in Set.Ioi 0, Real.exp (-(r * t)) * z t j) -
        A.mulVec (fun j => ∫ t in Set.Ioi 0, Real.exp (-(r * t)) * z t j) = z 0 ∧
      Good (cplx A) (fun j => ((∫ t in Set.Ioi 0, Real.exp (-(r * t)) * z t j : ℝ) : ℂ)) ∧
      ∀ w : Fin n → ℝ, Good (cplx A) (fun j => (w j : ℂ)) → r • w - A.mulVec w = z 0 →
        w = fun j => ∫ t in Set.Ioi 0, Real.exp (-(r * t)) * z t j := by
  obtain ⟨hcc, hdc⟩ := cplx_solution hc hd
  have hbc := (real_bounded_iff hc hd).1 hb
  rw [← bounded_iff hcc hdc] at hbc
  obtain ⟨h1, h2, h3⟩ := pv hr hcc hdc hbc
  obtain ⟨K, hK⟩ := hb
  set Ir : Fin n → ℝ := fun j => ∫ t in Set.Ioi 0, Real.exp (-(r * t)) * z t j
  have hintj : ∀ j, IntegrableOn (fun t => Real.exp (-(r * t)) * z t j) (Set.Ioi 0) := by
    intro j
    have hm : AEStronglyMeasurable (fun t => Real.exp (-(r * t)) * z t j)
        (volume.restrict (Set.Ioi 0)) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      exact (by fun_prop : Continuous fun t : ℝ => Real.exp (-(r * t))).continuousOn.mul
        ((continuous_apply j).comp_continuousOn (hc.mono Set.Ioi_subset_Ici_self))
    refine Integrable.mono' ((CTSimple.integrableOn_exp_Ioi hr).const_mul K) hm ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hK t (le_of_lt ht) j) (Real.exp_pos _).le
  have hIc : (∫ t in Set.Ioi 0, Real.exp (-(r * t)) • fun j => (z t j : ℂ)) =
      fun j => ((Ir j : ℝ) : ℂ) := by
    have hcomp : ∀ j, Integrable (fun t => (Real.exp (-(r * t)) • fun j => (z t j : ℂ)) j)
        (volume.restrict (Set.Ioi 0)) := by
      intro j
      have := (hintj j).ofReal (𝕜 := ℂ)
      refine this.congr (Eventually.of_forall fun t => ?_)
      simp [Complex.real_smul]
    funext j
    rw [eval_integral hcomp j]
    simp only [Pi.smul_apply, Complex.real_smul, ← Complex.ofReal_mul]
    exact integral_ofReal
  rw [hIc] at h1 h2 h3
  refine ⟨?_, h2, fun w hw hwe => ?_⟩
  · funext j
    have := congrFun h1 j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cplx_apply] at this
    have e : (A.map Complex.ofRealHom).mulVec (fun j => ((Ir j : ℝ) : ℂ)) j =
        ((A.mulVec Ir j : ℝ) : ℂ) := by
      have := RingHom.map_mulVec Complex.ofRealHom A Ir j
      simpa [Function.comp_def] using this.symm
    rw [e] at this
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact_mod_cast this
  · have hweq := h3 (fun j => (w j : ℂ)) hw (by
      funext j
      have := congrFun hwe j
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
      have e : (A.map Complex.ofRealHom).mulVec (fun j => (w j : ℂ)) j =
          ((A.mulVec w j : ℝ) : ℂ) := by
        have := RingHom.map_mulVec Complex.ofRealHom A w j
        simpa [Function.comp_def] using this.symm
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cplx_apply, e]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, this])
    funext j
    exact_mod_cast congrFun hweq j

end Cochrane.StickyPriceFiscal.TidyR6MatrixMethod
