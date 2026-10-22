/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergAENewton
import StabilizationWelfare.NonlinearRotembergMarkov

/-!
# The exact Rotemberg model on a general filtered probability space (almost surely)

Woodford (2003), *Interest and Prices*, Appendix A.3 (pp. 631–635, (A.11)–(A.13), p. 633: variables
are functions of the information), Chapter 4, Proposition 4.3 (p. 254), Chapter 6, §1 and
Chapter 3, fn. 44 (the Rotemberg model of `NonlinearRotemberg`).

With Mathlib's conditional expectation `μ[· | 𝓕_t]` (`ExpectationsMeasure.MeasExpectationSystem`)
on an ARBITRARY filtered probability space:

* `block_alg`, `homog_alg`: the pointwise algebra of the IS–AS reduction;
* `linSolA`, **`linSolA_spec`**, **`LA_inj`**: the linearised operator is a.s. invertible on a.s.
  measurable essentially bounded processes, with the parameter-only bound `KL p`;
* **`seq_existence_ae`**: under the Taylor principle there are `r, δ > 0` such that for every
  a.s. measurable disturbance process with `‖e_t‖ ≤ δ` a.s. the exact stochastic conditions have
  an a.s. measurable solution within `r`, a.s. unique among a.s. measurable processes within `r`;
* **`seq_existence_ae_adapted`**: with adapted disturbances the solution is ADAPTED;
* **`ar1_iid_equilibrium`**: the instance with an AR(1) driven by i.i.d. innovations with ANY
  bounded law.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergAE

open MeasureTheory Filter Topology
open NonlinearNKMarkov (mnorm norm_mulVec_le mnorm_nonneg)
open NonlinearNKMarkovAE NonlinearNKMarkovAEAdapted ExpectationsMeasure
open NonlinearRotemberg NonlinearRotembergAENewton

variable {p : Par}

/-! ## Pointwise algebra of the IS–AS reduction -/

/-- The forcing `b = B₀⁻¹g` of the IS–AS block at a point. -/
noncomputable def bRv (p : Par) (r : Fin 3 → ℝ) : Fin 2 → ℝ :=
  ![(r 0 + p.φy * r 2 - p.φ * ((r 1 - p.θ * p.m * p.ω * r 2) / p.ψ)) / p.dd,
    (p.κ * (r 0 + p.φy * r 2) + (p.σ + p.φy) * ((r 1 - p.θ * p.m * p.ω * r 2) / p.ψ)) / p.dd]

/-- The pointwise forcing is the forcing of a one-point state space. -/
theorem bRv_eq (r : Fin 3 → ℝ) : bRv p r = bR p (fun _ : Unit => r) () := rfl

/-- `‖b‖ ≤ c_b‖r‖`. -/
theorem norm_bRv_le (hp : p.Basic) {r : Fin 3 → ℝ} {a : ℝ} (ha : 0 ≤ a) (hr : ‖r‖ ≤ a) :
    ‖bRv p r‖ ≤ cb p * a := by
  rw [bRv_eq]; exact norm_bR_le hp ha (fun _ => hr) ()

/-- The pointwise forcing is continuous. -/
theorem continuous_bRv : Continuous (bRv p) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp only [bRv, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
    Matrix.cons_val_one] <;> fun_prop

/-- Woodford (2003), (A.12)–(A.13), Rotemberg pricing (**the block solves the linearised
conditions, pointwise**): if `(u₀, u₁) = A(w₂, w₁) + b(r)` then
`DQ(u₀ − r₂, u₁, u₀) + DN w = r` (`w` the forecasts; `DN` only reads `w₂`, `w₁`). -/
theorem block_alg (hb : p.Basic) (r w : Fin 3 → ℝ) (u : Fin 2 → ℝ)
    (hu : u = (Arot p).mulVec ![w 2, w 1] + bRv p r) :
    DQ0 p ![u 0 - r 2, u 1, u 0] + DN0 p w = r := by
  have hd := hb.dd_pos
  have hψ := hb.ψ_pos
  have h0 := congrFun hu 0
  have h1 := congrFun hu 1
  simp only [Arot, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Pi.add_apply, bRv] at h0 h1
  funext i
  fin_cases i
  · simp only [DQ0, DN0, Fin.zero_eta, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [Matrix.cons_val]
    rw [h0, h1]
    field_simp
    unfold Par.dd
    ring
  · simp only [DQ0, DN0, Fin.mk_one, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [Matrix.cons_val]
    rw [show p.θ * p.m * (p.ω * (u 0 - r 2) + p.σ * u 0) =
      p.κ * p.ψ * u 0 - p.θ * p.m * p.ω * r 2 by rw [hb.κ_mul]; ring]
    rw [h0, h1]
    field_simp
    unfold Par.dd
    ring
  · simp [DQ0, DN0]

/-- Woodford (2003), Proposition 4.3, Rotemberg slope (**the homogeneous reduction, pointwise**):
if `DQ v + DN w = 0` then `v₂ = v₀` and `(v₂, v₁) = A(w₂, w₁)`. -/
theorem homog_alg (hb : p.Basic) (v w : Fin 3 → ℝ) (h : DQ0 p v + DN0 p w = 0) :
    v 2 = v 0 ∧ (![v 2, v 1] : Fin 2 → ℝ) = (Arot p).mulVec ![w 2, w 1] := by
  have hd := hb.dd_pos
  have hψ := hb.ψ_pos
  have hk := hb.κ_mul
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  have e2 := congrFun h 2
  simp only [DQ0, DN0, Pi.add_apply, Pi.zero_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val] at e0 e1 e2
  have hv2 : v 2 = v 0 := by linarith
  rw [hv2] at e0 e1
  have e1' : v 1 = p.κ * v 0 + p.β * w 1 := by
    have : p.ψ * (v 1 - p.κ * v 0 - p.β * w 1) = 0 := by
      linear_combination e1 - v 0 * hk
    have := (mul_eq_zero.1 this).resolve_left hψ.ne'
    linarith
  refine ⟨hv2, ?_⟩
  funext i
  fin_cases i
  · simp only [Arot, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.zero_eta]
    rw [hv2]
    field_simp
    unfold Par.dd
    linear_combination e0 - p.φ * e1'
  · simp only [Arot, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.mk_one]
    field_simp
    unfold Par.dd
    linear_combination p.κ * e0 + (p.σ + p.φy) * e1'

/-! ## The linearised operator, almost surely -/

variable {Ω : Type*} [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)

/-- `DN` as a matrix. -/
noncomputable def DNmat (p : Par) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -1, -p.σ; 0, -(p.β * p.ψ), 0; 0, 0, 0]

/-- `DN w = DNmat w`. -/
theorem DN0_eq (w : Fin 3 → ℝ) : DN0 p w = (DNmat p).mulVec w := by
  funext i
  fin_cases i
  · simp [DN0, DNmat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring
  · simp [DN0, DNmat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · simp [DN0, DNmat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The linearised operator in the Rotemberg form, a.s.:
`(LA v)_t =ᵐ DQ v_t + DN μ[v_{t+1} | 𝓕_t]`. -/
theorem LA_eq {v : ℕ → Ω → Fin 3 → ℝ} (hv : Gd E v) {V : ℝ} (hvb : Bd E v V) (t : ℕ) :
    LA E (Qmap p) (Nmap p) v t =ᵐ[E.μ] fun ω => DQ0 p (v t ω) + DN0 p (MvA E v t ω) := by
  have h := MvA_mulVec E (DNmat p) hv hvb t
  filter_upwards [h] with ω hω
  simp only [LA, fderiv_Qmap_inr, fderiv_Nmap_inr, DN0_eq]
  rw [hω]

/-- Woodford (2003), (A.13) a.s., Rotemberg pricing: the inverse of the linearised operator,
`(ĉ, π)` from the forward series of the IS–AS block and `ŷ = ĉ − r₂`. -/
noncomputable def linSolA (p : Par) (r : ℕ → Ω → Fin 3 → ℝ) : ℕ → Ω → Fin 3 → ℝ :=
  fun t ω => ![fwdSolA E (Arot p) (fun s ω' => bRv p (r s ω')) t ω 0 - r t ω 2,
    fwdSolA E (Arot p) (fun s ω' => bRv p (r s ω')) t ω 1,
    fwdSolA E (Arot p) (fun s ω' => bRv p (r s ω')) t ω 0]

/-- Woodford (2003), App. A.3 a.s. (**the linearised operator is ONTO the essentially bounded
processes with a parameter-only bound**). -/
theorem linSolA_spec (hp : p.Std) {r : ℕ → Ω → Fin 3 → ℝ} (hrG : Gd E r) {a : ℝ} (ha : 0 ≤ a)
    (hr : Bd E r a) :
    Gd E (linSolA E p r) ∧ Bd E (linSolA E p r) (KL p * a) ∧
      ∀ t, LA E (Qmap p) (Nmap p) (linSolA E p r) t =ᵐ[E.μ] r t := by
  have hb := hp.basic
  set b : ℕ → Ω → Fin 2 → ℝ := fun s ω' => bRv p (r s ω') with hbdef
  have hbG : Gd E b := fun t => continuous_bRv.comp_aestronglyMeasurable (hrG t)
  have hbB : Bd E b (cb p * a) := fun t => by
    filter_upwards [hr t] with ω hω; exact norm_bRv_le hb ha hω
  obtain ⟨huG, huB, hrec⟩ := fwdSolA_spec E (summable_Arot hp) hbG
    (mul_nonneg (cb_nonneg hb) ha) hbB
  set u := fwdSolA E (Arot p) b with hu
  set S := ∑' k, mnorm (Arot p ^ k) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun k => mnorm_nonneg _
  have hG : Gd E (linSolA E p r) := fun t => by
    refine aesm_vec E fun i => ?_
    fin_cases i
    · exact (aesm_comp E (huG t) 0).sub (aesm_comp E (hrG t) 2)
    · exact aesm_comp E (huG t) 1
    · exact aesm_comp E (huG t) 0
  have hB : Bd E (linSolA E p r) (KL p * a) := fun t => by
    have hK : S * (cb p * a) + a = KL p * a := by unfold KL; ring
    have hSa : 0 ≤ S * (cb p * a) := mul_nonneg hS0 (mul_nonneg (cb_nonneg hb) ha)
    filter_upwards [huB t, hr t] with ω h1 h2
    have huc : ∀ i, |u t ω i| ≤ S * (cb p * a) := fun i => by
      have := norm_le_pi_norm (u t ω) i; rw [Real.norm_eq_abs] at this; exact this.trans h1
    have hrc : ∀ i, |r t ω i| ≤ a := fun i => by
      have := norm_le_pi_norm (r t ω) i; rw [Real.norm_eq_abs] at this; exact this.trans h2
    refine (pi_norm_le_iff_of_nonneg (by rw [← hK]; linarith)).2 fun i => ?_
    rw [Real.norm_eq_abs, ← hK]
    fin_cases i
    · simp only [linSolA, Fin.zero_eta, Matrix.cons_val_zero]
      exact (abs_sub _ _).trans (add_le_add (huc 0) (hrc 2))
    · simp only [linSolA, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      linarith [huc 1]
    · simp only [linSolA, Fin.reduceFinMk, Matrix.cons_val]
      linarith [huc 0]
  refine ⟨hG, hB, fun t => ?_⟩
  filter_upwards [LA_eq E hG hB t, hrec t] with ω h1 h2
  rw [h1]
  have hm2 : MvA E (linSolA E p r) t ω 2 = MvA E u t ω 0 := rfl
  have hm1 : MvA E (linSolA E p r) t ω 1 = MvA E u t ω 1 := rfl
  have e : (![MvA E (linSolA E p r) t ω 2, MvA E (linSolA E p r) t ω 1] : Fin 2 → ℝ) =
      MvA E u t ω := by
    funext i; fin_cases i
    · exact hm2
    · exact hm1
  have := block_alg hb (r t ω) (MvA E (linSolA E p r) t ω) (u t ω) (by rw [e]; exact h2)
  exact this

/-- Woodford (2003), App. A.3 and Proposition 4.3 a.s. (**the a.s. a-priori injectivity**): an a.s.
measurable essentially bounded `v` with `LA v = 0` a.s. vanishes a.s. -/
theorem LA_inj (hp : p.Std) {v : ℕ → Ω → Fin 3 → ℝ} (hv : Gd E v) {V : ℝ} (hV : 0 ≤ V)
    (hvb : Bd E v V) (h0 : ∀ t, LA E (Qmap p) (Nmap p) v t =ᵐ[E.μ] 0) :
    ∀ t, v t =ᵐ[E.μ] 0 := by
  have hb := hp.basic
  set u : ℕ → Ω → Fin 2 → ℝ := fun s ω => ![v s ω 2, v s ω 1] with hu
  have huG : Gd E u := fun t => aesm_vec E fun i => by
    fin_cases i
    · exact aesm_comp E (hv t) 2
    · exact aesm_comp E (hv t) 1
  have huB : Bd E u V := fun t => by
    filter_upwards [hvb t] with ω hω
    refine (pi_norm_le_iff_of_nonneg hV).2 fun i => ?_
    fin_cases i
    · simpa [hu] using (norm_le_pi_norm (v t ω) 2).trans hω
    · simpa [hu] using (norm_le_pi_norm (v t ω) 1).trans hω
  have hpt : ∀ t, ∀ᵐ ω ∂E.μ, v t ω 2 = v t ω 0 ∧
      u t ω = (Arot p).mulVec (MvA E u t ω) := fun t => by
    filter_upwards [LA_eq E hv hvb t, h0 t] with ω h1 h2
    rw [h1] at h2
    have := homog_alg hb (v t ω) (MvA E v t ω) h2
    exact ⟨this.1, this.2⟩
  have heq : ∀ t, u t =ᵐ[E.μ] fun ω => (Arot p).mulVec (MvA E u t ω) +
      (fun _ _ => (0 : Fin 2 → ℝ)) t ω := fun t => by
    filter_upwards [hpt t] with ω hω; simpa using hω.2
  have hz : ∀ k, iterA E k (fun _ _ => (0 : Fin 2 → ℝ)) = fun _ _ => 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [iterA_succ, ih, MvA_const]
  have hb0 : Bd E (fun _ _ => (0 : Fin 2 → ℝ)) 0 := fun t =>
    Eventually.of_forall fun _ => by simp
  have hu0 : ∀ t, ∀ᵐ ω ∂E.μ, u t ω = 0 := fun t => by
    have hm : ∀ m, ∀ᵐ ω ∂E.μ, ‖u t ω‖ ≤ mnorm (Arot p ^ m) * V := fun m => by
      have hit := iterate_eq_ae E (Arot p) (fun _ => aestronglyMeasurable_const) hV le_rfl
        huB hb0 heq m t
      filter_upwards [hit, iterA_bd E hV huB m t] with ω e hN
      rw [e]
      simp only [hz, Matrix.mulVec_zero, Finset.sum_const_zero, zero_add]
      exact (norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left hN (mnorm_nonneg _))
    filter_upwards [ae_all_iff.2 hm] with ω hω
    have hl : Tendsto (fun m => mnorm (Arot p ^ m) * V) atTop (𝓝 0) := by
      simpa using (summable_Arot hp).tendsto_atTop_zero.mul_const V
    exact norm_le_zero_iff.1 (ge_of_tendsto' hl hω)
  intro t
  filter_upwards [hu0 t, hpt t] with ω h1 h2
  have e2 : v t ω 2 = 0 := by have := congrFun h1 0; simpa [hu] using this
  have e1 : v t ω 1 = 0 := by have := congrFun h1 1; simpa [hu] using this
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Pi.zero_apply]; linarith [h2.1]
  · exact e1
  · exact e2

/-- Woodford (2003), App. A.3 a.s.: `linSolA (LA v) = v` a.s. -/
theorem linSolA_left (hp : p.Std) {v : ℕ → Ω → Fin 3 → ℝ} (hv : Gd E v) {V : ℝ} (hV : 0 ≤ V)
    (hvb : Bd E v V) : ∀ t, linSolA E p (LA E (Qmap p) (Nmap p) v) t =ᵐ[E.μ] v t := by
  have hLb := bd_LA E (Q := Qmap p) (N := Nmap p) hV hvb
  set c := (‖fderiv ℝ (Qmap p) (0, 0)‖ + ‖fderiv ℝ (Nmap p) (0, 0)‖) * V with hc
  have hc0 : 0 ≤ c := by positivity
  obtain ⟨hG, hB, hL⟩ := linSolA_spec E hp (gd_LA E hv) hc0 hLb
  have hK := (KL_pos hp.basic).le
  have hd := LA_inj E hp (v := fun s ω => linSolA E p (LA E (Qmap p) (Nmap p) v) s ω - v s ω)
    (fun t => (hG t).sub (hv t)) (add_nonneg (mul_nonneg hK hc0) hV)
    (fun t => by
      filter_upwards [hB t, hvb t] with ω h1 h2; exact (norm_sub_le _ _).trans (add_le_add h1 h2))
    (fun t => by
      filter_upwards [LA_sub E hG hv hB hvb t, hL t] with ω h1 h2
      rw [h1, h2]; simp)
  intro t
  filter_upwards [hd t] with ω hω
  exact sub_eq_zero.1 (by simpa using hω)

/-- Woodford (2003), App. A.3 a.s.: `linSolA` is a.s. additive in differences. -/
theorem linSolA_sub (hp : p.Std) {r r' : ℕ → Ω → Fin 3 → ℝ} (hrG : Gd E r) (hr'G : Gd E r')
    {a a' : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a') (hr : Bd E r a) (hr' : Bd E r' a') :
    ∀ t, linSolA E p (fun s ω => r s ω - r' s ω) t =ᵐ[E.μ]
      fun ω => linSolA E p r t ω - linSolA E p r' t ω := by
  have hdG : Gd E (fun s ω => r s ω - r' s ω) := fun t => (hrG t).sub (hr'G t)
  have hdb : Bd E (fun s ω => r s ω - r' s ω) (a + a') := fun t => by
    filter_upwards [hr t, hr' t] with ω h1 h2; exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  obtain ⟨g1, b1, hL1⟩ := linSolA_spec E hp hdG (add_nonneg ha ha') hdb
  obtain ⟨g2, b2, hL2⟩ := linSolA_spec E hp hrG ha hr
  obtain ⟨g3, b3, hL3⟩ := linSolA_spec E hp hr'G ha' hr'
  have g23 : Gd E (fun s ω => linSolA E p r s ω - linSolA E p r' s ω) := fun t =>
    (g2 t).sub (g3 t)
  have b23 : Bd E (fun s ω => linSolA E p r s ω - linSolA E p r' s ω)
      (KL p * a + KL p * a') := fun t => by
    filter_upwards [b2 t, b3 t] with ω h1 h2; exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  have hK := (KL_pos hp.basic).le
  have hd := LA_inj E hp (v := fun s ω => linSolA E p (fun s ω => r s ω - r' s ω) s ω -
      (linSolA E p r s ω - linSolA E p r' s ω)) (fun t => (g1 t).sub (g23 t))
    (by positivity : 0 ≤ KL p * (a + a') + (KL p * a + KL p * a'))
    (fun t => by
      filter_upwards [b1 t, b23 t] with ω h1 h2
      exact (norm_sub_le _ _).trans (add_le_add h1 h2))
    (fun t => by
      filter_upwards [LA_sub E g1 g23 b1 b23 t, hL1 t, LA_sub E g2 g3 b2 b3 t, hL2 t, hL3 t]
        with ω h1 h2 h3 h4 h5
      rw [h1, h2, h3, h4, h5]; simp)
  intro t
  filter_upwards [hd t] with ω hω
  exact sub_eq_zero.1 (by simpa using hω)

/-! ## Existence, uniqueness and adaptedness on a general filtered probability space -/

/-- Woodford (2003), (A.11) on a probability space, Rotemberg pricing (**the exact stochastic
conditions almost surely**): `Q(e_t, z_t) + μ[N(e_{t+1}, z_{t+1}) | 𝓕_t] = 0` a.s. at every
date (Euler equation with the rule, exact pricing condition, resource constraint). -/
def SeqEqmAE (p : Par) (e : ℕ → Ω → Fin 3 → ℝ) (z : ℕ → Ω → Fin 3 → ℝ) : Prop :=
  ∀ t, PhiA E (Qmap p) (Nmap p) e z t =ᵐ[E.μ] 0

/-- Woodford (2003), App. A.3 a.s.: the a-priori bound `‖v‖ ≤ K‖LA v‖` a.s. for the Rotemberg
operator. -/
theorem apriori_ae (hp : p.Std) (v : ℕ → Ω → Fin 3 → ℝ) (V a : ℝ) (hv : Gd E v) (hV : 0 ≤ V)
    (hvb : Bd E v V) (ha : 0 ≤ a) (hL : Bd E (LA E (Qmap p) (Nmap p) v) a) :
    Bd E v (KL p * a) := by
  obtain ⟨-, hB, -⟩ := linSolA_spec E hp (gd_LA E hv) ha hL
  have h := linSolA_left E hp hv hV hvb
  intro t
  filter_upwards [hB t, h t] with ω h1 h2
  rwa [h2] at h1

/-- Woodford (2003), App. A.3 and Proposition 4.3 a.s., Rotemberg pricing (**existence in an
invariant class and uniqueness, uniform over filtered probability spaces**). -/
theorem rot_ae (hp : p.Std) :
    ∃ r > 0, ∃ δ > 0, ∀ (Ω : Type*) [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)
      (e : ℕ → Ω → Fin 3 → ℝ), Gd E e → Bd E e δ →
      (∀ S : (ℕ → Ω → Fin 3 → ℝ) → Prop, S (fun _ _ => 0) →
        (∀ z, Gd E z → Bd E z r → S z →
          S (fun t ω => z t ω - linSolA E p (PhiA E (Qmap p) (Nmap p) e z) t ω)) →
        (∀ (zs : ℕ → ℕ → Ω → Fin 3 → ℝ) (z : ℕ → Ω → Fin 3 → ℝ), (∀ k, S (zs k)) →
          (∀ t, ∀ᵐ ω ∂E.μ, Tendsto (fun k => zs k t ω) atTop (𝓝 (z t ω))) → S z) →
        ∃ z, S z ∧ Gd E z ∧ Bd E z r ∧ SeqEqmAE E p e z) ∧
      ∀ z z' : ℕ → Ω → Fin 3 → ℝ, Gd E z → Gd E z' → Bd E z r → Bd E z' r →
        SeqEqmAE E p e z → SeqEqmAE E p e z' → ∀ t, z t =ᵐ[E.μ] z' t := by
  have hK := KL_pos hp.basic
  obtain ⟨ρ, hρ, hu⟩ := unique_ae (contDiff_Qmap (p := p) (n := 1))
    (contDiff_Nmap (p := p) (n := 1)) hK
  obtain ⟨r0, hr0, hex⟩ := exist_ae (contDiff_Qmap (p := p) (n := 1))
    (contDiff_Nmap (p := p) (n := 1)) steadyState_zero hK
  obtain ⟨δ1, hδ1, hex1⟩ := hex (min r0 ρ) (lt_min hr0 hρ) (min_le_left _ _)
  refine ⟨min r0 ρ, lt_min hr0 hρ, min δ1 ρ, lt_min hδ1 hρ, fun Ω _ E e he heb => ⟨?_, ?_⟩⟩
  · intro S hS0 hSinv hSlim
    exact hex1 Ω E (linSolA E p) (fun r a hr ha hrb => linSolA_spec E hp hr ha hrb)
      (fun r r' a a' hr hr' ha ha' hrb hr'b => linSolA_sub E hp hr hr' ha ha' hrb hr'b)
      (fun v V hv hV hvb => linSolA_left E hp hv hV hvb) e he
      (fun t => by filter_upwards [heb t] with ω hω; exact hω.trans (min_le_left _ _))
      S hS0 hSinv hSlim
  · intro z z' hz hz' hzb hz'b hE hE'
    exact hu Ω E (fun v V a hv hV hvb ha hL => apriori_ae E hp v V a hv hV hvb ha hL) e z z'
      he hz hz' (fun t => by filter_upwards [heb t] with ω hω; exact hω.trans (min_le_right _ _))
      (fun t => by filter_upwards [hzb t] with ω hω; exact hω.trans (min_le_right _ _))
      (fun t => by filter_upwards [hz'b t] with ω hω; exact hω.trans (min_le_right _ _)) hE hE'

/-- Woodford (2003), App. A.3 and Proposition 4.3, Rotemberg pricing (**EXISTENCE AND UNIQUENESS
ON A GENERAL FILTERED PROBABILITY SPACE**): under the Taylor principle there are `r, δ > 0` such
that on every filtered probability space, for every a.s. measurable disturbance process with
`‖e_t‖ ≤ δ` a.s., the exact stochastic conditions with Mathlib's conditional expectations have an
a.s. measurable solution with `‖z_t‖ ≤ r` a.s., and every a.s. measurable solution within `r` is
a.s. equal to it at every date. -/
theorem seq_existence_ae (hp : p.Std) :
    ∃ r > 0, ∃ δ > 0, ∀ (Ω : Type*) [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)
      (e : ℕ → Ω → Fin 3 → ℝ), Gd E e → Bd E e δ →
        ∃ z : ℕ → Ω → Fin 3 → ℝ, (Gd E z ∧ Bd E z r ∧ SeqEqmAE E p e z) ∧
          ∀ z' : ℕ → Ω → Fin 3 → ℝ, Gd E z' → Bd E z' r → SeqEqmAE E p e z' →
            ∀ t, z' t =ᵐ[E.μ] z t := by
  obtain ⟨r, hr, δ, hδ, h⟩ := rot_ae hp
  refine ⟨r, hr, δ, hδ, fun Ω _ E e he heb => ?_⟩
  obtain ⟨hex, hu⟩ := h Ω E e he heb
  obtain ⟨z, -, hzG, hzB, hz⟩ := hex (fun _ => True) trivial (fun _ _ _ _ => trivial)
    (fun _ _ _ _ => trivial)
  exact ⟨z, ⟨hzG, hzB, hz⟩, fun z' hz'G hz'B hz' => hu z' z hz'G hzG hz'B hzB hz' hz⟩

/-- Woodford (2003), App. A.3: the inverse of the linearised operator maps adapted bounded
processes to adapted processes. -/
theorem adA_linSolA (hp : p.Std) {r : ℕ → Ω → Fin 3 → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hr : Bd E r a) (hrA : AdA E r) : AdA E (linSolA E p r) := by
  have hb := hp.basic
  have hbB : Bd E (fun s ω' => bRv p (r s ω')) (cb p * a) := fun t => by
    filter_upwards [hr t] with ω hω; exact norm_bRv_le hb ha hω
  have hbA : AdA E (fun s ω' => bRv p (r s ω')) := fun t =>
    continuous_bRv.comp_aestronglyMeasurable (hrA t)
  have huA := adA_fwdSolA E (summable_Arot hp) (mul_nonneg (cb_nonneg hb) ha) hbB hbA
  intro t
  refine aesmSub_vec fun i => ?_
  fin_cases i
  · exact (adA_comp E huA 0 t).sub (adA_comp E hrA 2 t)
  · exact adA_comp E huA 1 t
  · exact adA_comp E huA 0 t

/-- Woodford (2003), App. A.3, p. 633, on a general probability space, Rotemberg pricing (**the
a.s. unique equilibrium is ADAPTED**): with adapted disturbances the solution within `r` is
adapted (each `z_t` a.s. equal to an `𝓕_t`-strongly measurable variable); it is a.s. unique among
a.s. measurable solutions within `r`. -/
theorem seq_existence_ae_adapted (hp : p.Std) :
    ∃ r > 0, ∃ δ > 0, ∀ (Ω : Type*) [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)
      (e : ℕ → Ω → Fin 3 → ℝ), Gd E e → Bd E e δ → AdA E e →
        ∃ z : ℕ → Ω → Fin 3 → ℝ, ((Gd E z ∧ Bd E z r ∧ SeqEqmAE E p e z) ∧ AdA E z) ∧
          ∀ z' : ℕ → Ω → Fin 3 → ℝ, Gd E z' → Bd E z' r → SeqEqmAE E p e z' →
            ∀ t, z' t =ᵐ[E.μ] z t := by
  obtain ⟨r, hr, δ, hδ, h⟩ := rot_ae hp
  refine ⟨r, hr, δ, hδ, fun Ω _ E e he heb heA => ?_⟩
  obtain ⟨hex, hu⟩ := h Ω E e he heb
  set R := max δ r with hR
  have hR0 : 0 ≤ R := le_max_of_le_right hr.le
  obtain ⟨CQ, hCQ⟩ := (isCompact_closedBall (0 : (Fin 3 → ℝ) × (Fin 3 → ℝ))
    R).exists_bound_of_continuousOn ((contDiff_Qmap (p := p) (n := 0)).continuous.continuousOn)
  obtain ⟨CN, hCN⟩ := (isCompact_closedBall (0 : (Fin 3 → ℝ) × (Fin 3 → ℝ))
    R).exists_bound_of_continuousOn ((contDiff_Nmap (p := p) (n := 0)).continuous.continuousOn)
  have hCQ0 : 0 ≤ CQ := (norm_nonneg _).trans (hCQ 0 (Metric.mem_closedBall_self hR0))
  have hCN0 : 0 ≤ CN := (norm_nonneg _).trans (hCN 0 (Metric.mem_closedBall_self hR0))
  have hPhiB : ∀ z, Bd E z r → Bd E (PhiA E (Qmap p) (Nmap p) e z) (CQ + CN) := fun z hz t => by
    have hNb : Bd E (fun s ω => Nmap p (e s ω, z s ω)) CN := fun t => by
      filter_upwards [heb t, hz t] with ω h1 h2
      exact hCN _ (by rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
                      exact max_le (h1.trans (le_max_left _ _)) (h2.trans (le_max_right _ _)))
    filter_upwards [heb t, hz t, MvA_bd E hCN0 hNb t] with ω h1 h2 h3
    exact (norm_add_le _ _).trans (add_le_add (hCQ _ (by
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
      exact max_le (h1.trans (le_max_left _ _)) (h2.trans (le_max_right _ _)))) h3)
  have hPhiA : ∀ z, AdA E z → AdA E (PhiA E (Qmap p) (Nmap p) e z) := fun z hz t =>
    ((contDiff_Qmap (p := p) (n := 0)).continuous.comp_aestronglyMeasurable
      ((heA t).prodMk (hz t))).add (adA_MvA E _ t)
  obtain ⟨z, hzA, hzG, hzB, hz⟩ := hex (AdA E) (fun t => aestronglyMeasurable_const)
    (fun z _ hzB hzA t => (hzA t).sub (adA_linSolA E hp (add_nonneg hCQ0 hCN0)
      (hPhiB z hzB) (hPhiA z hzA) t))
    (fun zs z hzs hlim t => aesmSub_lim (fun k => hzs k t) (hlim t))
  exact ⟨z, ⟨⟨hzG, hzB, hz⟩, hzA⟩, fun z' hz'G hz'B hz' => hu z' z hz'G hzG hz'B hzB hz' hz⟩

/-- Woodford (2003), App. A.3 a.s., Rotemberg pricing (**every a.s. measurable solution near the
steady state is adapted**): with adapted disturbances, any a.s. measurable solution within `r` is
a.s. equal at every date to an `𝓕_t`-measurable variable. -/
theorem solution_adapted (hp : p.Std) :
    ∃ r > 0, ∃ δ > 0, ∀ (Ω : Type*) [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)
      (e : ℕ → Ω → Fin 3 → ℝ), Gd E e → Bd E e δ → AdA E e →
        ∀ z : ℕ → Ω → Fin 3 → ℝ, Gd E z → Bd E z r → SeqEqmAE E p e z → AdA E z := by
  obtain ⟨r, hr, δ, hδ, h⟩ := seq_existence_ae_adapted hp
  refine ⟨r, hr, δ, hδ, fun Ω _ E e he heb heA z hzG hzB hz t => ?_⟩
  obtain ⟨w, ⟨-, hwA⟩, hu⟩ := h Ω E e he heb heA
  exact (hwA t).congr (hu z hzG hzB hz t).symm

open ExpectationsMeasureIID in
/-- Woodford (2003), Ch. 6, §1 and App. A.3, Rotemberg pricing (**the exact model driven by an
AR(1) with a GENERAL bounded innovation law**): on the i.i.d. product space `ν^ℕ` of any law `ν`
with `|ε| ≤ B` a.s., with `x_t = ρx_{t−1} + ε_t` (`|ρ| < 1`) and disturbances `e_t = x_t c`, if
`B‖c‖/(1 − |ρ|) ≤ δ` there is an a.s. measurable solution within `r` of the exact stochastic
conditions with Mathlib's conditional expectations, unique a.s. among such solutions. -/
theorem ar1_iid_equilibrium (hp : p.Std) :
    ∃ r > 0, ∃ δ > 0, ∀ (ν : ProbabilityMeasure ℝ) (B ρ : ℝ), |ρ| < 1 →
      (∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) → ∀ c : Fin 3 → ℝ, B / (1 - |ρ|) * ‖c‖ ≤ δ →
        ∃ z : ℕ → (ℕ → ℝ) → Fin 3 → ℝ, (Gd (iidSystem ν) z ∧ Bd (iidSystem ν) z r ∧
          SeqEqmAE (iidSystem ν) p (fun t ω => ar1 ρ t ω • c) z) ∧
          ∀ z' : ℕ → (ℕ → ℝ) → Fin 3 → ℝ, Gd (iidSystem ν) z' → Bd (iidSystem ν) z' r →
            SeqEqmAE (iidSystem ν) p (fun t ω => ar1 ρ t ω • c) z' →
              ∀ t, z' t =ᵐ[(iidSystem ν).μ] z t := by
  obtain ⟨r, hr, δ, hδ, h⟩ := seq_existence_ae hp
  refine ⟨r, hr, δ, hδ, fun ν B ρ hρ hB c hc => h (ℕ → ℝ) (iidSystem ν) _ (fun t => ?_)
    (fun t => ?_)⟩
  · exact (((ar1_adapted ν ρ t).mono ((iidSystem ν).𝓕.le t)).aestronglyMeasurable).smul_const c
  · filter_upwards [ar1_bdd (ν := ν) hρ hB t] with ω hω
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hω (norm_nonneg c)).trans hc

end Woodford.StabilizationWelfare.NonlinearRotembergAE
