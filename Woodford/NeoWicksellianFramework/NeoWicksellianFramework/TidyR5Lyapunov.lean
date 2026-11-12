/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.TidyR5EStabilityODE
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Lyapunov's indirect method for the E-stability equation (2.20)

Woodford (2003), *Interest and Prices*, Chapter 4, §2.3, pp. 264–266: an s.c.e. `θ̄` is E-stable
if it is a locally stable rest point of the (in general nonlinear) differential equation
`θ̇ = T(θ) − θ` (2.20), and "the local stability … depends on the eigenvalues of the Jacobian
matrix `DT(θ̄) − I`". Here the stability half of that link is proved for an arbitrary map `T`
that is merely differentiable at the rest point:

* `IsFwdSol` (a solution of (2.20) on `[0, ∞)`: continuous there, with right derivatives
  `T(θ(τ)) − θ(τ)`), `IsLAS` (local asymptotic stability: Lyapunov stability and local
  attraction, over all such solutions); `isFwdSol_of_isESol`.
* `lyapunov_exists`: if every eigenvalue of `A = DT − I` has negative real part, the Lyapunov
  equation `AᵀP + PA = −I` has a symmetric positive-definite solution. `X ↦ AᵀX + XA` is injective
  (if `AᵀX + XA = 0`, `t ↦ (e^{tA}x)′X(e^{tA}y)` is constant and tends to `0`), hence onto;
  positivity because `t ↦ (e^{tA}x)′P(e^{tA}x)` is strictly decreasing to `0`.
* `quad_bounds`, `bilin_bound`, `norm_sq_le_dot`: norm equivalences for the quadratic form.
* `decay_of_eStableAt`: near `θ̄`, every forward solution satisfies
  `‖θ(τ) − θ̄‖² ≤ c ‖θ(0) − θ̄‖² e^{−kτ}`, by a barrier (fencing) argument for
  `V(θ) = (θ − θ̄)′P(θ − θ̄)` (`image_le_of_deriv_right_lt_deriv_boundary`).
* **`isLAS_of_eStableAt`**: E-stability (eigenvalues of `DT(θ̄) − I` with negative real part)
  implies that `θ̄` is a locally (exponentially) asymptotically stable rest point of the nonlinear
  equation (2.20).

The instability half for a general nonlinear `T` (an eigenvalue with positive real part makes
`θ̄` unstable) is not proved here; for Preston's `T`-map the converse is proved exactly,
boundary case included, in the module TidyR5PrestonLAS through an invariant affine subspace.
-/

namespace Woodford.NeoWicksellianFramework.TidyR5Lyapunov

open Matrix Filter Topology TidyR5EStabilityODE
open Determinacy2Learning (EStable EStableAt)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Forward solutions and local asymptotic stability -/

/-- Woodford (2003), (2.20) p. 265: `θ` solves `θ̇ = T(θ) − θ` on `[0, ∞)`: continuous there,
with right derivative `T(θ(τ)) − θ(τ)` at every `τ ≥ 0`. -/
def IsFwdSol (T : (ι → ℝ) → ι → ℝ) (θ : ℝ → ι → ℝ) : Prop :=
  ContinuousOn θ (Set.Ici 0) ∧
    ∀ τ : ℝ, 0 ≤ τ → HasDerivWithinAt θ (T (θ τ) - θ τ) (Set.Ici τ) τ

/-- Woodford (2003), p. 264: `θ̄` is a **locally asymptotically stable rest point** of (2.20):
forward solutions starting close stay close (Lyapunov stability) and forward solutions starting
close enough converge to `θ̄`. -/
def IsLAS (T : (ι → ℝ) → ι → ℝ) (θs : ι → ℝ) : Prop :=
  (∀ ε > 0, ∃ δ > 0, ∀ θ, IsFwdSol T θ → ‖θ 0 - θs‖ < δ → ∀ τ : ℝ, 0 ≤ τ → ‖θ τ - θs‖ < ε) ∧
    ∃ δ > 0, ∀ θ, IsFwdSol T θ → ‖θ 0 - θs‖ < δ → Tendsto θ atTop (𝓝 θs)

set_option linter.unusedFintypeInType false in
omit [DecidableEq ι] in
/-- Woodford (2003), (2.20): a solution on all of `ℝ` is a forward solution. -/
theorem isFwdSol_of_isESol {T : (ι → ℝ) → ι → ℝ} {θ : ℝ → ι → ℝ} (h : IsESol T θ) :
    IsFwdSol T θ :=
  ⟨fun τ _ => (h τ).continuousAt.continuousWithinAt, fun τ _ => (h τ).hasDerivWithinAt⟩

/-! ### Calculus and norms for quadratic forms -/

omit [DecidableEq ι] in
/-- Woodford (2003), (2.20): the derivative of `τ ↦ u(τ)′ X w(τ)`. -/
theorem hasDerivWithinAt_bilin (X : Matrix ι ι ℝ) {u w : ℝ → ι → ℝ} {u' w' : ι → ℝ}
    {s : Set ℝ} {t : ℝ} (hu : HasDerivWithinAt u u' s t) (hw : HasDerivWithinAt w w' s t) :
    HasDerivWithinAt (fun τ => u τ ⬝ᵥ (X *ᵥ w τ)) (u' ⬝ᵥ (X *ᵥ w t) + u t ⬝ᵥ (X *ᵥ w')) s t := by
  have hui : ∀ i, HasDerivWithinAt (fun τ => u τ i) (u' i) s t := fun i =>
    hasDerivWithinAt_pi.1 hu i
  have hwi : ∀ i, HasDerivWithinAt (fun τ => w τ i) (w' i) s t := fun i =>
    hasDerivWithinAt_pi.1 hw i
  have h := HasDerivWithinAt.sum (u := Finset.univ) fun i _ =>
    (hui i).mul (HasDerivWithinAt.sum (u := Finset.univ) fun j _ => (hwi j).const_mul (X i j))
  convert h using 1
  · funext τ
    simp [dotProduct, mulVec]
  · simp [dotProduct, mulVec, Finset.sum_add_distrib]

omit [DecidableEq ι] in
/-- Woodford (2003), (2.20): `(Au)′Xw + u′X(Aw) = u′(AᵀX + XA)w`. -/
theorem dot_mulVec_add (A X : Matrix ι ι ℝ) (u w : ι → ℝ) :
    (A *ᵥ u) ⬝ᵥ (X *ᵥ w) + u ⬝ᵥ (X *ᵥ (A *ᵥ w)) = u ⬝ᵥ ((Aᵀ * X + X * A) *ᵥ w) := by
  rw [add_mulVec, dotProduct_add, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_comm (A *ᵥ u),
    dotProduct_mulVec, dotProduct_comm, mulVec_transpose]

omit [DecidableEq ι] in
/-- Woodford (2003), (2.20): `u′u > 0` for `u ≠ 0`. -/
theorem dot_self_pos {u : ι → ℝ} (hu : u ≠ 0) : 0 < u ⬝ᵥ u := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
  simp only [dotProduct]
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg (u j))
    ⟨i, Finset.mem_univ _, mul_self_pos.mpr hi⟩

omit [DecidableEq ι] in
/-- Woodford (2003), (2.20): `‖u‖² ≤ u′u` (sup norm). -/
theorem norm_sq_le_dot (u : ι → ℝ) : ‖u‖ ^ 2 ≤ u ⬝ᵥ u := by
  have h : ‖u‖ ≤ Real.sqrt (u ⬝ᵥ u) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    simp only [dotProduct]
    rw [sq]
    exact Finset.single_le_sum (f := fun j => u j * u j) (fun j _ => mul_self_nonneg (u j))
      (Finset.mem_univ i)
  have h0 : 0 ≤ u ⬝ᵥ u := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg (u j)
  calc ‖u‖ ^ 2 ≤ Real.sqrt (u ⬝ᵥ u) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = u ⬝ᵥ u := Real.sq_sqrt h0

omit [DecidableEq ι] in
/-- Woodford (2003), (2.20): `|u′Pr| ≤ K ‖u‖ ‖r‖` with `K = ∑ᵢⱼ |Pᵢⱼ|`. -/
theorem bilin_bound (P : Matrix ι ι ℝ) (u r : ι → ℝ) :
    |u ⬝ᵥ (P *ᵥ r)| ≤ (∑ i, ∑ j, |P i j|) * ‖u‖ * ‖r‖ := by
  simp only [dotProduct, mulVec]
  calc |∑ i, u i * ∑ j, P i j * r j| ≤ ∑ i, |u i * ∑ j, P i j * r j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |P i j| * ‖u‖ * ‖r‖ := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        calc |u i| * |∑ j, P i j * r j| ≤ |u i| * ∑ j, |P i j * r j| :=
              mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
          _ = ∑ j, |u i| * (|P i j| * |r j|) := by rw [Finset.mul_sum]; simp [abs_mul]
          _ ≤ ∑ j, |P i j| * ‖u‖ * ‖r‖ := Finset.sum_le_sum fun j _ => by
              have h1 : |u i| ≤ ‖u‖ := by
                have := norm_le_pi_norm u i
                rwa [Real.norm_eq_abs] at this
              have h2 : |r j| ≤ ‖r‖ := by
                have := norm_le_pi_norm r j
                rwa [Real.norm_eq_abs] at this
              have := mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg (P i j)))
                (by positivity) (norm_nonneg _)
              nlinarith [abs_nonneg (P i j), norm_nonneg u, norm_nonneg r]
    _ = (∑ i, ∑ j, |P i j|) * ‖u‖ * ‖r‖ := by simp only [Finset.sum_mul]

omit [DecidableEq ι] in
/-- Woodford (2003), (2.20): the quadratic form `x′Px` is continuous. -/
theorem continuous_quad (P : Matrix ι ι ℝ) : Continuous fun x : ι → ℝ => x ⬝ᵥ (P *ᵥ x) :=
  continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)

omit [DecidableEq ι] in
/-- Woodford (2003), (2.20): a positive-definite quadratic form is comparable with `‖x‖²`:
`c₁‖x‖² ≤ x′Px ≤ c₂‖x‖²`, `c₁, c₂ > 0` (compactness of the unit sphere). -/
theorem quad_bounds (P : Matrix ι ι ℝ) (hP : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (P *ᵥ x)) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ x : ι → ℝ, c₁ * ‖x‖ ^ 2 ≤ x ⬝ᵥ (P *ᵥ x) ∧ x ⬝ᵥ (P *ᵥ x) ≤ c₂ * ‖x‖ ^ 2 := by
  have hhom : ∀ (c : ℝ) (x : ι → ℝ), (c • x) ⬝ᵥ (P *ᵥ (c • x)) = c ^ 2 * (x ⬝ᵥ (P *ᵥ x)) := by
    intro c x
    rw [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    ring
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨1, 1, one_pos, one_pos, fun x => ?_⟩
    have hx : x = 0 := Subsingleton.elim _ _
    subst hx
    simp
  · have hS : IsCompact (Metric.sphere (0 : ι → ℝ) 1) := isCompact_sphere 0 1
    have hne : (Metric.sphere (0 : ι → ℝ) 1).Nonempty := by
      refine ⟨fun _ => 1, ?_⟩
      rw [mem_sphere_zero_iff_norm]
      refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp) ?_
      simp
    obtain ⟨xm, hxm, hmin⟩ := hS.exists_isMinOn hne (continuous_quad P).continuousOn
    obtain ⟨xM, hxM, hmax⟩ := hS.exists_isMaxOn hne (continuous_quad P).continuousOn
    have hxm0 : xm ≠ 0 := by
      intro h
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at hxm
      norm_num at hxm
    set m := xm ⬝ᵥ (P *ᵥ xm)
    set M := xM ⬝ᵥ (P *ᵥ xM)
    have hm : 0 < m := hP xm hxm0
    refine ⟨m, max M 1, hm, lt_of_lt_of_le one_pos (le_max_right _ _), fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx
      simp
    · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      set y := ‖x‖⁻¹ • x with hy
      have hyS : y ∈ Metric.sphere (0 : ι → ℝ) 1 := by
        rw [mem_sphere_zero_iff_norm, hy, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ hn.ne']
      have hxy : x = ‖x‖ • y := by
        rw [hy, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      have h1 : m ≤ y ⬝ᵥ (P *ᵥ y) := hmin hyS
      have h2 : y ⬝ᵥ (P *ᵥ y) ≤ M := hmax hyS
      have hq : x ⬝ᵥ (P *ᵥ x) = ‖x‖ ^ 2 * (y ⬝ᵥ (P *ᵥ y)) := by
        conv_lhs => rw [hxy]
        exact hhom _ _
      rw [hq]
      have hsq : 0 ≤ ‖x‖ ^ 2 := by positivity
      constructor
      · exact mul_le_mul_of_nonneg_left h1 hsq |>.trans_eq' (by ring)
      · calc ‖x‖ ^ 2 * (y ⬝ᵥ (P *ᵥ y)) ≤ ‖x‖ ^ 2 * max M 1 :=
            mul_le_mul_of_nonneg_left (h2.trans (le_max_left _ _)) hsq
          _ = max M 1 * ‖x‖ ^ 2 := by ring

/-! ### The Lyapunov equation -/

/-- Woodford (2003), p. 266: **the Lyapunov matrix**: if `J` is E-stable (every eigenvalue of
`A = J − I` has negative real part), there is a symmetric `P` with `AᵀP + PA = −I` and
`x′Px > 0` for `x ≠ 0`. -/
theorem lyapunov_exists {J : Matrix ι ι ℝ} (hJ : EStable J) :
    ∃ P : Matrix ι ι ℝ, Pᵀ = P ∧ (J - 1)ᵀ * P + P * (J - 1) = -1 ∧
      ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (P *ᵥ x) := by
  set A := J - 1 with hA
  have hlim : ∀ x, Tendsto (fun t => flow A t x) atTop (𝓝 0) := tendsto_flow_of_eStable hJ
  have hder : ∀ (X : Matrix ι ι ℝ) (x y : ι → ℝ) (t : ℝ),
      HasDerivAt (fun τ => flow A τ x ⬝ᵥ (X *ᵥ flow A τ y))
        (flow A t x ⬝ᵥ ((Aᵀ * X + X * A) *ᵥ flow A t y)) t := by
    intro X x y t
    have h := hasDerivWithinAt_bilin X (s := Set.univ)
      (hasDerivAt_flow_apply A x t).hasDerivWithinAt (hasDerivAt_flow_apply A y t).hasDerivWithinAt
    rw [hasDerivWithinAt_univ, dot_mulVec_add] at h
    exact h
  have hlimq : ∀ (X : Matrix ι ι ℝ) (x y : ι → ℝ),
      Tendsto (fun τ => flow A τ x ⬝ᵥ (X *ᵥ flow A τ y)) atTop (𝓝 0) := by
    intro X x y
    have hc : Continuous fun p : (ι → ℝ) × (ι → ℝ) => p.1 ⬝ᵥ (X *ᵥ p.2) :=
      continuous_fst.dotProduct (continuous_const.matrix_mulVec continuous_snd)
    have := (hc.tendsto ((0 : ι → ℝ), (0 : ι → ℝ))).comp ((hlim x).prodMk_nhds (hlim y))
    simpa [Function.comp_def] using this
  set L : Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ :=
    LinearMap.mulLeft ℝ Aᵀ + LinearMap.mulRight ℝ A with hL
  have hLapp : ∀ X, L X = Aᵀ * X + X * A := fun X => rfl
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX
    rw [hLapp] at hX
    have hzero : ∀ x y : ι → ℝ, x ⬝ᵥ (X *ᵥ y) = 0 := by
      intro x y
      have hc : ∀ t, flow A t x ⬝ᵥ (X *ᵥ flow A t y) = flow A 0 x ⬝ᵥ (X *ᵥ flow A 0 y) :=
        fun t => is_const_of_deriv_eq_zero (fun s => (hder X x y s).differentiableAt)
          (fun s => by rw [(hder X x y s).deriv, hX, zero_mulVec, dotProduct_zero]) t 0
      have h1 := hlimq X x y
      simp only [hc, flow_zero, one_apply_eq_self] at h1
      exact tendsto_nhds_unique tendsto_const_nhds h1
    ext i j
    have := hzero (Pi.single i 1) (Pi.single j 1)
    simpa [mulVec_single_one, single_one_dotProduct] using this
  obtain ⟨P, hP⟩ := (LinearMap.injective_iff_surjective.mp hinj) (-1)
  rw [hLapp] at hP
  have hsym : Pᵀ = P := by
    apply hinj
    rw [hLapp, hLapp, hP]
    have := congrArg Matrix.transpose hP
    rw [transpose_add, transpose_mul, transpose_mul, transpose_transpose, transpose_neg,
      transpose_one] at this
    rw [← this, add_comm]
  refine ⟨P, hsym, hP, fun x hx => ?_⟩
  set g : ℝ → ℝ := fun τ => flow A τ x ⬝ᵥ (P *ᵥ flow A τ x) with hg
  have hne : ∀ t, flow A t x ≠ 0 := by
    intro t h0
    apply hx
    have h1 := flow_mul_flow_neg (-A) t
    rw [neg_neg] at h1
    have := congrArg (fun F : (ι → ℝ) →L[ℝ] (ι → ℝ) => F x) h1
    simp only [mul_apply_eq_comp, h0, map_zero, one_apply_eq_self] at this
    exact this.symm
  have hgd : ∀ t, HasDerivAt g (-(flow A t x ⬝ᵥ flow A t x)) t := by
    intro t
    have := hder P x x t
    rw [hP, neg_mulVec, one_mulVec, dotProduct_neg] at this
    exact this
  have hanti : StrictAnti g := strictAnti_of_deriv_neg fun t => by
    rw [(hgd t).deriv]
    exact neg_neg_of_pos (dot_self_pos (hne t))
  have hlimg : Tendsto g atTop (𝓝 0) := hlimq P x x
  have h1 : 0 ≤ g 1 := by
    refine le_of_tendsto hlimg ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact hanti.antitone ht
  have h0 : g 0 = x ⬝ᵥ (P *ᵥ x) := by
    simp [hg, flow_zero]
  rw [← h0]
  exact lt_of_le_of_lt h1 (hanti zero_lt_one)

/-! ### Exponential decay near an E-stable rest point -/

/-- Woodford (2003), pp. 264–266: **exponential decay near an E-stable rest point**: if
`EStableAt T θ̄`, there are `ρ, c, k > 0` such that every forward solution of (2.20) with
`‖θ(0) − θ̄‖ < ρ` satisfies `‖θ(τ) − θ̄‖² ≤ c ‖θ(0) − θ̄‖² e^{−kτ}` for all `τ ≥ 0`. -/
theorem decay_of_eStableAt {T : (ι → ℝ) → ι → ℝ} {θs : ι → ℝ} (h : EStableAt T θs) :
    ∃ ρ c k : ℝ, 0 < ρ ∧ 0 < c ∧ 0 < k ∧ ∀ θ, IsFwdSol T θ → ‖θ 0 - θs‖ < ρ →
      ∀ τ : ℝ, 0 ≤ τ → ‖θ τ - θs‖ ^ 2 ≤ c * ‖θ 0 - θs‖ ^ 2 * Real.exp (-(k * τ)) := by
  obtain ⟨hfix, hd, hJ⟩ := h
  set J := LinearMap.toMatrix' (fderiv ℝ T θs : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) with hJdef
  obtain ⟨P, hPs, hL, hPpos⟩ := lyapunov_exists hJ
  obtain ⟨c₁, c₂, hc₁, hc₂, hb⟩ := quad_bounds P hPpos
  set K := ∑ i, ∑ j, |P i j| with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  set η := 1 / (4 * (K + 1)) with hη
  have hηpos : 0 < η := by positivity
  have hKη : K * η ≤ 1 / 4 := by
    rw [hη, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hJapp : ∀ y, J *ᵥ y = fderiv ℝ T θs y := fun y => by
    rw [hJdef, LinearMap.toMatrix'_mulVec]
    rfl
  obtain ⟨ρ0, hρ0, hrem⟩ := Metric.eventually_nhds_iff.mp
    (hd.hasFDerivAt.isLittleO.def hηpos)
  -- the derivative of `V` along the vector field
  have hD : ∀ y, ‖y - θs‖ < ρ0 →
      (T y - y) ⬝ᵥ (P *ᵥ (y - θs)) + (y - θs) ⬝ᵥ (P *ᵥ (T y - y)) ≤ -(‖y - θs‖ ^ 2 / 2) := by
    intro y hy
    set x := y - θs with hx
    set r := T y - θs - J *ᵥ x with hr
    have hF : T y - y = (J - 1) *ᵥ x + r := by
      rw [hr, hx, sub_mulVec, one_mulVec]
      abel
    have hrb : ‖r‖ ≤ η * ‖x‖ := by
      have := hrem (y := y) (by rwa [dist_eq_norm])
      rw [hfix] at this
      rw [hr, hJapp]
      exact this
    have hsym : r ⬝ᵥ (P *ᵥ x) = x ⬝ᵥ (P *ᵥ r) := by
      rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hPs]
    rw [hF, add_dotProduct, mulVec_add, dotProduct_add, hsym]
    have hq : ((J - 1) *ᵥ x) ⬝ᵥ (P *ᵥ x) + x ⬝ᵥ (P *ᵥ ((J - 1) *ᵥ x)) = -(x ⬝ᵥ x) := by
      rw [dot_mulVec_add, hL, neg_mulVec, one_mulVec, dotProduct_neg]
    have hbl := bilin_bound P x r
    have h1 : x ⬝ᵥ (P *ᵥ r) ≤ K * ‖x‖ * (η * ‖x‖) :=
      (le_abs_self _).trans (hbl.trans (mul_le_mul_of_nonneg_left hrb (by positivity)))
    have h2 : K * ‖x‖ * (η * ‖x‖) ≤ ‖x‖ ^ 2 / 4 := by
      have : K * ‖x‖ * (η * ‖x‖) = (K * η) * ‖x‖ ^ 2 := by ring
      rw [this]
      nlinarith [sq_nonneg ‖x‖]
    have h3 := norm_sq_le_dot x
    linarith
  set k := 1 / (4 * c₂) with hk
  have hkpos : 0 < k := by positivity
  set rr := c₁ / (c₁ + c₂) with hrr
  have hrr0 : 0 < rr := by positivity
  have hrr1 : rr ≤ 1 := by rw [hrr, div_le_one (by positivity)]; linarith
  have hrrc : c₂ * rr ≤ c₁ := by
    rw [hrr, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨ρ0 * rr, c₂ / c₁, k, by positivity, by positivity, hkpos, fun θ hθ h0 τ hτ => ?_⟩
  obtain ⟨hcont, hder⟩ := hθ
  set V : ℝ → ℝ := fun s => (θ s - θs) ⬝ᵥ (P *ᵥ (θ s - θs)) with hV
  set V0 := V 0 with hV0
  have hV0b : V0 ≤ c₂ * ‖θ 0 - θs‖ ^ 2 := (hb _).2
  have hV0small : V0 < c₁ * ρ0 ^ 2 := by
    have hn : ‖θ 0 - θs‖ ^ 2 < (ρ0 * rr) ^ 2 :=
      pow_lt_pow_left₀ h0 (norm_nonneg _) two_ne_zero
    calc V0 ≤ c₂ * ‖θ 0 - θs‖ ^ 2 := hV0b
      _ < c₂ * (ρ0 * rr) ^ 2 := mul_lt_mul_of_pos_left hn hc₂
      _ = (c₂ * rr) * rr * ρ0 ^ 2 := by ring
      _ ≤ c₁ * 1 * ρ0 ^ 2 := by
          gcongr
      _ = c₁ * ρ0 ^ 2 := by ring
  -- the barrier argument
  have hbar : ∀ η' > 0, V0 + η' < c₁ * ρ0 ^ 2 → ∀ t, 0 ≤ t →
      V t ≤ (V0 + η') * Real.exp (-(k * t)) := by
    intro η' hη' hsm t ht
    have hVc : ContinuousOn V (Set.Icc 0 t) :=
      (continuous_quad P).comp_continuousOn
        ((hcont.mono Set.Icc_subset_Ici_self).sub continuousOn_const)
    have hVd : ∀ s ∈ Set.Ico (0 : ℝ) t, HasDerivWithinAt V
        ((T (θ s) - θ s) ⬝ᵥ (P *ᵥ (θ s - θs)) + (θ s - θs) ⬝ᵥ (P *ᵥ (T (θ s) - θ s)))
        (Set.Ici s) s := by
      intro s hs
      have hs' := (hder s hs.1).sub_const θs
      exact hasDerivWithinAt_bilin P hs' hs'
    have hB : ∀ s, HasDerivAt (fun s => (V0 + η') * Real.exp (-(k * s)))
        ((V0 + η') * (Real.exp (-(k * s)) * -(k * 1))) s := fun s =>
      (((hasDerivAt_id s).const_mul k).neg.exp).const_mul (V0 + η')
    have hV0B : V 0 ≤ (V0 + η') * Real.exp (-(k * 0)) := by
      simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
      linarith
    refine image_le_of_deriv_right_lt_deriv_boundary hVc hVd hV0B hB ?_
      ⟨ht, le_rfl⟩
    intro s hs hcontact
    have hV0nn : 0 ≤ V0 := by
      have := (hb (θ 0 - θs)).1
      nlinarith [sq_nonneg ‖θ 0 - θs‖]
    have hBpos : 0 < (V0 + η') * Real.exp (-(k * s)) :=
      mul_pos (by linarith) (Real.exp_pos _)
    have hBle : (V0 + η') * Real.exp (-(k * s)) ≤ V0 + η' :=
      mul_le_of_le_one_right (by linarith)
        (Real.exp_le_one_iff.mpr (by nlinarith [hs.1]))
    have hin : ‖θ s - θs‖ < ρ0 := by
      have h1 := (hb (θ s - θs)).1
      have h2 : c₁ * ‖θ s - θs‖ ^ 2 < c₁ * ρ0 ^ 2 := by
        have : V s = (V0 + η') * Real.exp (-(k * s)) := hcontact
        simp only [hV] at this
        linarith
      have h3 : ‖θ s - θs‖ ^ 2 < ρ0 ^ 2 := lt_of_mul_lt_mul_left h2 hc₁.le
      exact lt_of_pow_lt_pow_left₀ 2 hρ0.le h3
    have hDs := hD (θ s) hin
    have hupper := (hb (θ s - θs)).2
    have hVs : V s = (V0 + η') * Real.exp (-(k * s)) := hcontact
    simp only [hV] at hVs
    rw [hVs] at hupper
    have hk2 : k * (4 * c₂) = 1 := by rw [hk]; field_simp
    nlinarith [hBpos]
  have hfin : V τ ≤ V0 * Real.exp (-(k * τ)) := by
    have hgap : 0 < c₁ * ρ0 ^ 2 - V0 := by linarith
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set η' := min ε ((c₁ * ρ0 ^ 2 - V0) / 2) with hη'
    have hη'0 : 0 < η' := lt_min hε (by linarith)
    have hη'le : η' ≤ ε := min_le_left _ _
    have hη's : V0 + η' < c₁ * ρ0 ^ 2 := by
      have := min_le_right ε ((c₁ * ρ0 ^ 2 - V0) / 2)
      linarith
    have := hbar η' hη'0 hη's τ hτ
    have he : Real.exp (-(k * τ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have he0 : 0 < Real.exp (-(k * τ)) := Real.exp_pos _
    nlinarith
  have hlow := (hb (θ τ - θs)).1
  have he0 : 0 < Real.exp (-(k * τ)) := Real.exp_pos _
  have : c₁ * ‖θ τ - θs‖ ^ 2 ≤ c₂ * ‖θ 0 - θs‖ ^ 2 * Real.exp (-(k * τ)) := by
    calc c₁ * ‖θ τ - θs‖ ^ 2 ≤ V τ := hlow
      _ ≤ V0 * Real.exp (-(k * τ)) := hfin
      _ ≤ c₂ * ‖θ 0 - θs‖ ^ 2 * Real.exp (-(k * τ)) :=
          mul_le_mul_of_nonneg_right hV0b he0.le
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hc₁]
  linarith

/-- Woodford (2003), pp. 264–266: **Lyapunov's indirect method for (2.20) (stability half)**: if
`T` is differentiable at a rest point `θ̄` and every eigenvalue of `DT(θ̄) − I` has negative
real part (`EStableAt`), then `θ̄` is a locally asymptotically stable rest point of the nonlinear
equation `θ̇ = T(θ) − θ` (Lyapunov stable and locally attracting, exponentially). -/
theorem isLAS_of_eStableAt {T : (ι → ℝ) → ι → ℝ} {θs : ι → ℝ} (h : EStableAt T θs) :
    IsLAS T θs := by
  obtain ⟨ρ, c, k, hρ, hc, hk, hdec⟩ := decay_of_eStableAt h
  refine ⟨fun ε hε => ?_, ⟨ρ, hρ, fun θ hθ h0 => ?_⟩⟩
  · refine ⟨min ρ (ε / (c + 1)), lt_min hρ (by positivity), fun θ hθ h0 τ hτ => ?_⟩
    have h1 := hdec θ hθ (lt_of_lt_of_le h0 (min_le_left _ _)) τ hτ
    have h2 : ‖θ 0 - θs‖ < ε / (c + 1) := lt_of_lt_of_le h0 (min_le_right _ _)
    have he : Real.exp (-(k * τ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have h3 : ‖θ 0 - θs‖ ^ 2 < (ε / (c + 1)) ^ 2 :=
      pow_lt_pow_left₀ h2 (norm_nonneg _) two_ne_zero
    have h4 : c * (ε / (c + 1)) ^ 2 ≤ ε ^ 2 := by
      rw [div_pow, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (sq_nonneg ε) (by positivity : (0 : ℝ) ≤ c ^ 2 + c + 1)]
    have h5 : ‖θ τ - θs‖ ^ 2 < ε ^ 2 := by
      calc ‖θ τ - θs‖ ^ 2 ≤ c * ‖θ 0 - θs‖ ^ 2 * Real.exp (-(k * τ)) := h1
        _ ≤ c * ‖θ 0 - θs‖ ^ 2 := by
            have : 0 ≤ c * ‖θ 0 - θs‖ ^ 2 := by positivity
            nlinarith [Real.exp_pos (-(k * τ))]
        _ < c * (ε / (c + 1)) ^ 2 := mul_lt_mul_of_pos_left h3 hc
        _ ≤ ε ^ 2 := h4
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h5
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun τ : ℝ => Real.sqrt (c * ‖θ 0 - θs‖ ^ 2 * Real.exp (-(k * τ))))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun τ : ℝ => Real.exp (-(k * τ))) atTop (𝓝 0) := by
        have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (tendsto_id.const_mul_atTop hk)
        simpa [Function.comp_def] using this
      have h2 := (h1.const_mul (c * ‖θ 0 - θs‖ ^ 2)).sqrt
      simpa using h2
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
    rw [← Real.sqrt_sq (norm_nonneg (θ τ - θs))]
    exact Real.sqrt_le_sqrt (hdec θ hθ h0 τ hτ)

end Woodford.NeoWicksellianFramework.TidyR5Lyapunov
