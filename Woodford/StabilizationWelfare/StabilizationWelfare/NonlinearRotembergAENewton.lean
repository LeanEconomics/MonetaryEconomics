/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergNewton
import StabilizationWelfare.NonlinearNKMarkovAEAdapted

/-!
# A quantitative implicit function theorem on a filtered probability space (almost surely)

Woodford (2003), *Interest and Prices*, Appendix A.3 (pp. 631–635, (A.11)–(A.13)) and
Chapter 6, §1 (pp. 383–392).

The almost-sure counterpart of `NonlinearRotembergNewton`, abstracted from the Calvo-specific
argument of `NonlinearNKMarkovAE.seq_existence_ae` and `NonlinearNKMarkovAE.seq_uniqueness_ae`:
for ANY `C¹` maps `Q, N : ℝᵐ × ℝⁿ → ℝⁿ` with `Q(0,0) + N(0,0) = 0` and the conditions
`Q(e_t, z_t) + μ[N(e_{t+1}, z_{t+1}) | 𝓕_t] = 0` a.s. (`PhiA`) on an ARBITRARY filtered
probability space (`ExpectationsMeasure.MeasExpectationSystem`), on a.s. measurable essentially
bounded processes:

* **`unique_ae`**: if the linearised operator `LA` satisfies the a-priori bound
  `‖v‖ ≤ K‖LA v‖` a.s., two solutions within `ρ` coincide a.s. at every date;
* **`exist_ae`**: if `LA` has an a.s. right inverse with bound `K` that is additive and a left
  inverse, there is a solution within `r`, in every class `S` of processes containing `0`,
  invariant under the Newton step and closed under a.s. limits (e.g. adapted processes).

The radii depend only on `Q, N` and `K`.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergAENewton

open MeasureTheory Filter Topology
open NonlinearNKMarkov (mnorm)
open NonlinearNKMarkovAE ExpectationsMeasure NonlinearNKMarkovRamseyIFT

variable {Ω : Type*} [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) {m n : ℕ}

/-- Woodford (2003), (A.11) a.s.: the residual `Q(e_t, z_t) + μ[N(e_{t+1}, z_{t+1}) | 𝓕_t]`. -/
noncomputable def PhiA (Q N : (Fin m → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)) (e : ℕ → Ω → Fin m → ℝ)
    (z : ℕ → Ω → Fin n → ℝ) : ℕ → Ω → Fin n → ℝ :=
  fun t ω => Q (e t ω, z t ω) + MvA E (fun s ω' => N (e s ω', z s ω')) t ω

/-- Woodford (2003), (A.12) a.s.: the linearised operator
`(LA v)_t = DQ(0, v_t) + μ[DN(0, v_{t+1}) | 𝓕_t]`. -/
noncomputable def LA (Q N : (Fin m → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)) (v : ℕ → Ω → Fin n → ℝ) :
    ℕ → Ω → Fin n → ℝ :=
  fun t ω => fderiv ℝ Q (0, 0) (0, v t ω) +
    MvA E (fun s ω' => fderiv ℝ N (0, 0) (0, v s ω')) t ω

variable {Q N : (Fin m → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)}

/-- The derivative applied to a good process is good. -/
theorem gd_D (D : (Fin m → ℝ) × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) {v : ℕ → Ω → Fin n → ℝ}
    (hv : Gd E v) : Gd E (fun s ω => D (0, v s ω)) := fun t =>
  (D.continuous.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable (hv t)

/-- The derivative applied to a bounded process is bounded. -/
theorem bd_D (D : (Fin m → ℝ) × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) {v : ℕ → Ω → Fin n → ℝ}
    {V : ℝ} (hv : Bd E v V) : Bd E (fun s ω => D (0, v s ω)) (‖D‖ * V) := fun t => by
  filter_upwards [hv t] with ω hω
  refine (D.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  rw [NonlinearRotembergNewton.norm_pair_zero']; exact hω

/-- The linearised operator maps good processes to good processes. -/
theorem gd_LA {v : ℕ → Ω → Fin n → ℝ} (hv : Gd E v) : Gd E (LA E Q N v) :=
  gd_add E (gd_D E _ hv) (MvA_gd E _)

/-- The linearised operator maps bounded processes to bounded processes. -/
theorem bd_LA {v : ℕ → Ω → Fin n → ℝ} {V : ℝ} (hV : 0 ≤ V) (hv : Bd E v V) :
    Bd E (LA E Q N v) ((‖fderiv ℝ Q (0, 0)‖ + ‖fderiv ℝ N (0, 0)‖) * V) := fun t => by
  filter_upwards [bd_D E (fderiv ℝ Q (0, 0)) hv t,
    MvA_bd E (mul_nonneg (norm_nonneg _) hV) (bd_D E (fderiv ℝ N (0, 0)) hv) t] with ω h1 h2
  calc ‖LA E Q N v t ω‖ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

/-- The linearised operator is a.s. additive in differences. -/
theorem LA_sub {v w : ℕ → Ω → Fin n → ℝ} (hv : Gd E v) (hw : Gd E w) {V W : ℝ}
    (hvb : Bd E v V) (hwb : Bd E w W) (t : ℕ) :
    LA E Q N (fun s ω => v s ω - w s ω) t =ᵐ[E.μ] fun ω => LA E Q N v t ω - LA E Q N w t ω := by
  have h := MvA_sub E (gd_D E (fderiv ℝ N (0, 0)) hv) (gd_D E (fderiv ℝ N (0, 0)) hw)
    (bd_D E _ hvb) (bd_D E _ hwb) t
  have h0 : ∀ a b : Fin n → ℝ, ((0 : Fin m → ℝ), a - b) = ((0 : Fin m → ℝ), a) - (0, b) :=
    fun a b => by simp
  filter_upwards [h] with ω hω
  simp only [LA, h0, map_sub]
  rw [hω]; abel

/-- The linearised operator respects a.s. equality. -/
theorem LA_congr {v w : ℕ → Ω → Fin n → ℝ} (h : ∀ t, v t =ᵐ[E.μ] w t) (t : ℕ) :
    LA E Q N v t =ᵐ[E.μ] LA E Q N w t := by
  have h1 : ∀ t, (fun ω => fderiv ℝ N (0, 0) (0, v t ω)) =ᵐ[E.μ]
      fun ω => fderiv ℝ N (0, 0) (0, w t ω) := fun t => by
    filter_upwards [h t] with ω hω; rw [hω]
  filter_upwards [h t, MvA_congr E h1 t] with ω h2 h3
  simp only [LA]; rw [h2, h3]

/-- `LA 0 = 0`. -/
theorem LA_zero : LA E Q N (fun _ _ => (0 : Fin n → ℝ)) = fun _ _ => 0 := by
  have h : ((0 : Fin m → ℝ), (0 : Fin n → ℝ)) = 0 := rfl
  funext t ω
  simp only [LA, h, map_zero, MvA_const, zero_add]

/-- Woodford (2003), App. A.3 a.s. (**the residual minus its linearisation is small**). -/
theorem resid_ae {η ρ : ℝ} (hη0 : 0 ≤ η)
    (hQ : ∀ e w w', ‖e‖ ≤ ρ → ‖w‖ ≤ ρ → ‖w'‖ ≤ ρ →
      ‖Q (e, w) - Q (e, w') - fderiv ℝ Q (0, 0) (0, w - w')‖ ≤ η * ‖w - w'‖)
    (hN : ∀ e w w', ‖e‖ ≤ ρ → ‖w‖ ≤ ρ → ‖w'‖ ≤ ρ →
      ‖N (e, w) - N (e, w') - fderiv ℝ N (0, 0) (0, w - w')‖ ≤ η * ‖w - w'‖)
    (hNc : Continuous N)
    {CN : ℝ} (hCN : ∀ q ∈ Metric.closedBall (0 : (Fin m → ℝ) × (Fin n → ℝ)) ρ, ‖N q‖ ≤ CN)
    {e : ℕ → Ω → Fin m → ℝ} {z z' : ℕ → Ω → Fin n → ℝ} (he : Gd E e) (hz : Gd E z)
    (hz' : Gd E z') (heb : Bd E e ρ) (hzb : Bd E z ρ) (hz'b : Bd E z' ρ) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : Bd E (fun s ω => z s ω - z' s ω) D) :
    Bd E (fun s ω => PhiA E Q N e z s ω - PhiA E Q N e z' s ω -
      LA E Q N (fun s ω => z s ω - z' s ω) s ω) (2 * η * D) := by
  have hNb : ∀ w : ℕ → Ω → Fin n → ℝ, Bd E w ρ →
      Bd E (fun s ω => N (e s ω, w s ω)) CN := fun w hw t => by
    filter_upwards [heb t, hw t] with ω h1 h2
    exact hCN _ (by rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]; exact max_le h1 h2)
  have hNg : ∀ w : ℕ → Ω → Fin n → ℝ, Gd E w → Gd E (fun s ω => N (e s ω, w s ω)) :=
    fun w hw => gd_pair E hNc he hw
  set d : ℕ → Ω → Fin n → ℝ := fun s ω => z s ω - z' s ω with hd
  have hdG : Gd E d := fun t => (hz t).sub (hz' t)
  have hRN : Bd E (fun s ω => N (e s ω, z s ω) - N (e s ω, z' s ω) -
      fderiv ℝ N (0, 0) (0, d s ω)) (η * D) := fun t => by
    filter_upwards [heb t, hzb t, hz'b t, hD t] with ω h1 h2 h3 h4
    exact (hN (e t ω) (z t ω) (z' t ω) h1 h2 h3).trans (mul_le_mul_of_nonneg_left h4 hη0)
  have hNdg : Gd E (fun s ω => N (e s ω, z s ω) - N (e s ω, z' s ω)) := fun t =>
    ((hNg z hz) t).sub ((hNg z' hz') t)
  have hNdb : Bd E (fun s ω => N (e s ω, z s ω) - N (e s ω, z' s ω)) (CN + CN) :=
    fun t => by
      filter_upwards [hNb z hzb t, hNb z' hz'b t] with ω h1 h2
      exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  intro t
  have s1 := MvA_sub E (hNg z hz) (hNg z' hz') (hNb z hzb) (hNb z' hz'b) t
  have s2 := MvA_sub E hNdg (gd_D E (fderiv ℝ N (0, 0)) hdG) hNdb (bd_D E _ hD) t
  have hRb := MvA_bd E (mul_nonneg hη0 hD0) hRN t
  filter_upwards [s1, s2, hRb, heb t, hzb t, hz'b t, hD t] with ω m1 m2 hR h1 h2 h3 h4
  have hQx := hQ (e t ω) (z t ω) (z' t ω) h1 h2 h3
  have key : PhiA E Q N e z t ω - PhiA E Q N e z' t ω - LA E Q N d t ω =
      (Q (e t ω, z t ω) - Q (e t ω, z' t ω) - fderiv ℝ Q (0, 0) (0, z t ω - z' t ω)) +
      MvA E (fun s ω => N (e s ω, z s ω) - N (e s ω, z' s ω) -
        fderiv ℝ N (0, 0) (0, d s ω)) t ω := by
    rw [m2, m1]
    simp only [PhiA, LA, hd]
    abel
  rw [key]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ η * D + η * D := add_le_add (hQx.trans (mul_le_mul_of_nonneg_left h4 hη0)) hR
    _ = 2 * η * D := by ring

/-- Woodford (2003), App. A.3 a.s. (**uniqueness among essentially bounded processes, uniform
over probability spaces**): if `Q, N` are `C¹` and `K > 0`, there is `ρ > 0` such that on every
filtered probability space on which `LA` satisfies the a-priori bound `‖v‖ ≤ K‖LA v‖` a.s., two
a.s. measurable solutions of the conditions within `ρ` (disturbances within `ρ`) coincide a.s. -/
theorem unique_ae (hQ : ContDiff ℝ 1 Q) (hN : ContDiff ℝ 1 N) {K : ℝ} (hK : 0 < K) :
    ∃ ρ > 0, ∀ (Ω : Type*) [MeasurableSpace Ω] (E : MeasExpectationSystem Ω),
      (∀ (v : ℕ → Ω → Fin n → ℝ) (V a : ℝ), Gd E v → 0 ≤ V → Bd E v V → 0 ≤ a →
        Bd E (LA E Q N v) a → Bd E v (K * a)) →
      ∀ (e : ℕ → Ω → Fin m → ℝ) (z z' : ℕ → Ω → Fin n → ℝ), Gd E e → Gd E z → Gd E z' →
        Bd E e ρ → Bd E z ρ → Bd E z' ρ → (∀ t, PhiA E Q N e z t =ᵐ[E.μ] 0) →
          (∀ t, PhiA E Q N e z' t =ᵐ[E.μ] 0) → ∀ t, z t =ᵐ[E.μ] z' t := by
  set η := 1 / (4 * K) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρQ, hρQ, hQr⟩ := remainder_gen hQ hη0
  obtain ⟨ρN, hρN, hNr⟩ := remainder_gen hN hη0
  set ρ := min ρQ ρN with hρ
  have hρ0 : 0 < ρ := lt_min hρQ hρN
  have hQ' : ∀ e w w', ‖e‖ ≤ ρ → ‖w‖ ≤ ρ → ‖w'‖ ≤ ρ →
      ‖Q (e, w) - Q (e, w') - fderiv ℝ Q (0, 0) (0, w - w')‖ ≤ η * ‖w - w'‖ :=
    fun e w w' he hw hw' => hQr e w w' (he.trans (min_le_left _ _)) (hw.trans (min_le_left _ _))
      (hw'.trans (min_le_left _ _))
  have hN' : ∀ e w w', ‖e‖ ≤ ρ → ‖w‖ ≤ ρ → ‖w'‖ ≤ ρ →
      ‖N (e, w) - N (e, w') - fderiv ℝ N (0, 0) (0, w - w')‖ ≤ η * ‖w - w'‖ :=
    fun e w w' he hw hw' => hNr e w w' (he.trans (min_le_right _ _))
      (hw.trans (min_le_right _ _)) (hw'.trans (min_le_right _ _))
  obtain ⟨CN, hCN⟩ := (isCompact_closedBall (0 : (Fin m → ℝ) × (Fin n → ℝ))
    ρ).exists_bound_of_continuousOn hN.continuous.continuousOn
  refine ⟨ρ, hρ0, fun Ω _ E hap e z z' he hz hz' heb hzb hz'b hE hE' => ?_⟩
  set d : ℕ → Ω → Fin n → ℝ := fun s ω => z s ω - z' s ω with hd
  have hdG : Gd E d := fun t => (hz t).sub (hz' t)
  have hdb : Bd E d (2 * ρ) := fun t => by
    filter_upwards [hzb t, hz'b t] with ω h1 h2
    exact (norm_sub_le _ _).trans (by linarith)
  have himp : ∀ U, Bd E d U → Bd E d (0 + 1 / 2 * U) := by
    intro U hU
    by_cases hU0 : 0 ≤ U
    · have hR := resid_ae E hη0.le hQ' hN' hN.continuous hCN he hz hz' heb hzb hz'b hU0 hU
      have hLd : Bd E (LA E Q N d) (2 * η * U) := fun t => by
        filter_upwards [hR t, hE t, hE' t] with ω h1 h2 h3
        simp only [Pi.zero_apply] at h2 h3
        rw [h2, h3] at h1
        simpa using h1
      have h := hap d (2 * ρ) _ hdG (by positivity) hdb (by positivity) hLd
      intro t
      filter_upwards [h t] with ω hω
      calc _ ≤ _ := hω
        _ = 0 + 1 / 2 * U := by rw [hη]; field_simp; ring
    · intro t
      have : ∀ᵐ ω ∂E.μ, False := by
        filter_upwards [hU t] with ω hω; exact hU0 ((norm_nonneg _).trans hω)
      filter_upwards [this] with ω hω; exact hω.elim
  have h0 := bound_improve_ae E (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hdb himp
  intro t
  filter_upwards [h0 t] with ω hω
  have : d t ω = 0 := norm_le_zero_iff.1 (by simpa using hω)
  exact sub_eq_zero.1 this

/-- Woodford (2003), App. A.3 a.s. (**a quantitative implicit function theorem on a filtered
probability space: existence in an invariant class**). If `Q, N` are `C¹`, `Q(0,0)+N(0,0) = 0`
and `K > 0`, there is `r₀ > 0` such that for every `0 < r ≤ r₀` there is `δ > 0` (depending only
on `Q, N, K`) with: on every filtered probability space, if `Linv` is an a.s. right inverse of
`LA` on good bounded processes with bound `K`, a.s. additive and an a.s. left inverse, then for
every a.s. measurable disturbance with `‖e_t‖ ≤ δ` a.s. and every class `S` containing `0`,
invariant under the Newton step and closed under a.s. limits, there is a solution `z ∈ S`, a.s.
measurable, `‖z_t‖ ≤ r` a.s., of the conditions a.s. at every date. -/
theorem exist_ae (hQ : ContDiff ℝ 1 Q) (hN : ContDiff ℝ 1 N) (hs : Q (0, 0) + N (0, 0) = 0)
    {K : ℝ} (hK : 0 < K) :
    ∃ r0 > 0, ∀ r, 0 < r → r ≤ r0 → ∃ δ > 0, ∀ (Ω : Type*) [MeasurableSpace Ω]
      (E : MeasExpectationSystem Ω) (Linv : (ℕ → Ω → Fin n → ℝ) → (ℕ → Ω → Fin n → ℝ)),
      (∀ ρ a, Gd E ρ → 0 ≤ a → Bd E ρ a →
        Gd E (Linv ρ) ∧ Bd E (Linv ρ) (K * a) ∧ ∀ t, LA E Q N (Linv ρ) t =ᵐ[E.μ] ρ t) →
      (∀ ρ ρ' a a', Gd E ρ → Gd E ρ' → 0 ≤ a → 0 ≤ a' → Bd E ρ a → Bd E ρ' a' →
        ∀ t, Linv (fun s ω => ρ s ω - ρ' s ω) t =ᵐ[E.μ] fun ω => Linv ρ t ω - Linv ρ' t ω) →
      (∀ v V, Gd E v → 0 ≤ V → Bd E v V → ∀ t, Linv (LA E Q N v) t =ᵐ[E.μ] v t) →
      ∀ e : ℕ → Ω → Fin m → ℝ, Gd E e → Bd E e δ →
      ∀ S : (ℕ → Ω → Fin n → ℝ) → Prop, S (fun _ _ => 0) →
        (∀ z, Gd E z → Bd E z r → S z → S (fun t ω => z t ω - Linv (PhiA E Q N e z) t ω)) →
        (∀ (zs : ℕ → ℕ → Ω → Fin n → ℝ) (z : ℕ → Ω → Fin n → ℝ), (∀ k, S (zs k)) →
          (∀ t, ∀ᵐ ω ∂E.μ, Tendsto (fun k => zs k t ω) atTop (𝓝 (z t ω))) → S z) →
        ∃ z, S z ∧ Gd E z ∧ Bd E z r ∧ ∀ t, PhiA E Q N e z t =ᵐ[E.μ] 0 := by
  set η := 1 / (4 * K) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρQ, hρQ, hQr⟩ := remainder_gen hQ hη0
  obtain ⟨ρN, hρN, hNr⟩ := remainder_gen hN hη0
  set r0 := min ρQ ρN with hr0
  have hr00 : 0 < r0 := lt_min hρQ hρN
  have hQ' : ∀ e w w', ‖e‖ ≤ r0 → ‖w‖ ≤ r0 → ‖w'‖ ≤ r0 →
      ‖Q (e, w) - Q (e, w') - fderiv ℝ Q (0, 0) (0, w - w')‖ ≤ η * ‖w - w'‖ :=
    fun e w w' he hw hw' => hQr e w w' (he.trans (min_le_left _ _)) (hw.trans (min_le_left _ _))
      (hw'.trans (min_le_left _ _))
  have hN' : ∀ e w w', ‖e‖ ≤ r0 → ‖w‖ ≤ r0 → ‖w'‖ ≤ r0 →
      ‖N (e, w) - N (e, w') - fderiv ℝ N (0, 0) (0, w - w')‖ ≤ η * ‖w - w'‖ :=
    fun e w w' he hw hw' => hNr e w w' (he.trans (min_le_right _ _))
      (hw.trans (min_le_right _ _)) (hw'.trans (min_le_right _ _))
  obtain ⟨CQ, hCQ⟩ := (isCompact_closedBall (0 : (Fin m → ℝ) × (Fin n → ℝ))
    r0).exists_bound_of_continuousOn hQ.continuous.continuousOn
  obtain ⟨CN, hCN⟩ := (isCompact_closedBall (0 : (Fin m → ℝ) × (Fin n → ℝ))
    r0).exists_bound_of_continuousOn hN.continuous.continuousOn
  have hCQ0 : 0 ≤ CQ := (norm_nonneg _).trans (hCQ 0 (Metric.mem_closedBall_self hr00.le))
  have hCN0 : 0 ≤ CN := (norm_nonneg _).trans (hCN 0 (Metric.mem_closedBall_self hr00.le))
  refine ⟨r0, hr00, fun r hr0' hrr0 => ?_⟩
  set τ := r / (4 * K) with hτ
  have hτ0 : 0 < τ := by positivity
  have hcQ : ContinuousAt (fun e : Fin m → ℝ => Q (e, 0)) 0 :=
    (hQ.continuous.comp (continuous_id.prodMk continuous_const)).continuousAt
  have hcN : ContinuousAt (fun e : Fin m → ℝ => N (e, 0)) 0 :=
    (hN.continuous.comp (continuous_id.prodMk continuous_const)).continuousAt
  obtain ⟨δQ, hδQ, hQc⟩ := Metric.continuousAt_iff.1 hcQ τ hτ0
  obtain ⟨δN, hδN, hNc⟩ := Metric.continuousAt_iff.1 hcN τ hτ0
  set δ := min r (min (δQ / 2) (δN / 2)) with hδ
  have hδ0 : 0 < δ := lt_min hr0' (lt_min (by positivity) (by positivity))
  refine ⟨δ, hδ0, fun Ω _ E Linv hL hadd hleft e he heb S hS0 hSinv hSlim => ?_⟩
  have heb0 : Bd E e r0 := fun t => by
    filter_upwards [heb t] with ω hω; exact hω.trans ((min_le_left _ _).trans hrr0)
  have hPhiG : ∀ z, Gd E z → Gd E (PhiA E Q N e z) := fun z hz =>
    gd_add E (gd_pair E hQ.continuous he hz) (MvA_gd E _)
  have hPhiB : ∀ z, Bd E z r → Bd E (PhiA E Q N e z) (CQ + CN) := fun z hz t => by
    have hNb : Bd E (fun s ω => N (e s ω, z s ω)) CN := fun t => by
      filter_upwards [heb0 t, hz t] with ω h1 h2
      exact hCN _ (by rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
                      exact max_le h1 (h2.trans hrr0))
    filter_upwards [heb0 t, hz t, MvA_bd E hCN0 hNb t] with ω h1 h2 h3
    exact (norm_add_le _ _).trans (add_le_add (hCQ _ (by
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
      exact max_le h1 (h2.trans hrr0))) h3)
  set T : (ℕ → Ω → Fin n → ℝ) → (ℕ → Ω → Fin n → ℝ) :=
    fun z t ω => z t ω - Linv (PhiA E Q N e z) t ω with hT
  have hTG : ∀ z, Gd E z → Bd E z r → Gd E (T z) := fun z hz hzb t =>
    (hz t).sub ((hL _ _ (hPhiG z hz) (add_nonneg hCQ0 hCN0) (hPhiB z hzb)).1 t)
  have hcontr : ∀ z z', Gd E z → Gd E z' → Bd E z r → Bd E z' r → ∀ D, 0 ≤ D →
      Bd E (fun s ω => z s ω - z' s ω) D → Bd E (fun s ω => T z s ω - T z' s ω) (D / 2) := by
    intro z z' hz hz' hzb hz'b D hD0 hD
    have hzb0 : Bd E z r0 := fun t => by
      filter_upwards [hzb t] with ω hω; exact hω.trans hrr0
    have hz'b0 : Bd E z' r0 := fun t => by
      filter_upwards [hz'b t] with ω hω; exact hω.trans hrr0
    have hR := resid_ae E hη0.le hQ' hN' hN.continuous hCN he hz hz' heb0 hzb0 hz'b0 hD0 hD
    have hdG : Gd E (fun s ω => z s ω - z' s ω) := fun t => (hz t).sub (hz' t)
    have hLd := bd_LA E (Q := Q) (N := N) hD0 hD
    have hPd : Bd E (fun s ω => PhiA E Q N e z s ω - PhiA E Q N e z' s ω)
        (CQ + CN + (CQ + CN)) := fun t => by
      filter_upwards [hPhiB z hzb t, hPhiB z' hz'b t] with ω h1 h2
      exact (norm_sub_le _ _).trans (add_le_add h1 h2)
    have hPdG : Gd E (fun s ω => PhiA E Q N e z s ω - PhiA E Q N e z' s ω) := fun t =>
      ((hPhiG z hz) t).sub ((hPhiG z' hz') t)
    have e1 := hadd _ _ _ _ (hPhiG z hz) (hPhiG z' hz') (add_nonneg hCQ0 hCN0)
      (add_nonneg hCQ0 hCN0) (hPhiB z hzb) (hPhiB z' hz'b)
    have e2 := hadd _ _ _ _ hPdG (gd_LA E hdG) (by positivity)
      (mul_nonneg (by positivity) hD0) hPd hLd
    have e3 := hleft _ D hdG hD0 hD
    have hRG : Gd E (fun s ω => PhiA E Q N e z s ω - PhiA E Q N e z' s ω -
        LA E Q N (fun s ω => z s ω - z' s ω) s ω) := fun t => (hPdG t).sub (gd_LA E hdG t)
    have hb := (hL _ _ hRG (by positivity) hR).2.1
    intro t
    filter_upwards [e1 t, e2 t, e3 t, hb t] with ω h1 h2 h3 h4
    have key : T z t ω - T z' t ω = -Linv (fun s ω => PhiA E Q N e z s ω -
        PhiA E Q N e z' s ω - LA E Q N (fun s ω => z s ω - z' s ω) s ω) t ω := by
      rw [h2]
      simp only [hT]
      rw [h1, h3]
      abel
    rw [key, norm_neg]
    calc _ ≤ _ := h4
      _ = D / 2 := by rw [hη]; field_simp; ring
  have hT0 : Bd E (T fun _ _ => 0) (r / 2) := by
    have hb : Bd E (PhiA E Q N e fun _ _ => 0) (2 * τ) := fun t => by
      have hNg : Gd E (fun s ω => N (e s ω, (0 : Fin n → ℝ))) :=
        gd_pair E hN.continuous he (fun _ => aestronglyMeasurable_const)
      have hNb : Bd E (fun s ω => N (e s ω, (0 : Fin n → ℝ))) CN := fun t => by
        filter_upwards [heb0 t] with ω h1
        exact hCN _ (by rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
                        exact max_le h1 (by simp [hr00.le]))
      have mm := MvA_sub E hNg (fun _ => aestronglyMeasurable_const) hNb
        (C := CN) (D := ‖N (0, 0)‖) (h := fun s ω => N (e s ω, 0))
        (g := fun _ _ => N (0, 0)) (fun _ => Eventually.of_forall fun _ => le_rfl) t
      have hbN : Bd E (fun s ω => N (e s ω, (0 : Fin n → ℝ)) - N (0, 0)) τ :=
        fun t => by
          filter_upwards [heb t] with ω h1
          have h := hNc (x := e t ω) (by
            rw [dist_zero_right]; exact lt_of_le_of_lt (h1.trans
              ((min_le_right _ _).trans (min_le_right _ _))) (by linarith))
          rw [dist_eq_norm] at h; exact h.le
      filter_upwards [heb t, mm, MvA_bd E hτ0.le hbN t] with ω h1 hm h3
      have hq : ‖Q (e t ω, 0) - Q (0, 0)‖ ≤ τ := by
        have h := hQc (x := e t ω) (by
          rw [dist_zero_right]; exact lt_of_le_of_lt (h1.trans
            ((min_le_right _ _).trans (min_le_left _ _))) (by linarith))
        rw [dist_eq_norm] at h; exact h.le
      have key : PhiA E Q N e (fun _ _ => 0) t ω = (Q (e t ω, 0) - Q (0, 0)) +
          MvA E (fun s ω => N (e s ω, 0) - N (0, 0)) t ω := by
        rw [hm, MvA_const]
        simp only [PhiA]
        linear_combination (norm := abel_nf) hs
      rw [key]
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ τ + τ := add_le_add hq h3
        _ = 2 * τ := by ring
    have hl := (hL _ _ (hPhiG _ fun _ => aestronglyMeasurable_const) (by positivity) hb).2.1
    intro t
    filter_upwards [hl t] with ω hω
    simp only [hT, zero_sub, norm_neg]
    calc _ ≤ K * (2 * τ) := hω
      _ = r / 2 := by rw [hτ]; field_simp; ring
  have hballB : ∀ z, Gd E z → Bd E z r → Bd E (T z) r := by
    intro z hz hzb t
    have h1 := hcontr z (fun _ _ => 0) hz (fun _ => aestronglyMeasurable_const) hzb
      (fun t => Eventually.of_forall fun _ => by simp [hr0'.le]) r hr0'.le
      (fun t => by filter_upwards [hzb t] with ω hω; simpa using hω) t
    filter_upwards [h1, hT0 t] with ω e1 e2
    calc ‖T z t ω‖ ≤ ‖T z t ω - T (fun _ _ => 0) t ω‖ + ‖T (fun _ _ => 0) t ω‖ := by
          have := norm_add_le (T z t ω - T (fun _ _ => 0) t ω) (T (fun _ _ => 0) t ω)
          simpa using this
      _ ≤ r / 2 + r / 2 := add_le_add e1 e2
      _ = r := by ring
  set zs : ℕ → ℕ → Ω → Fin n → ℝ := fun k => T^[k] fun _ _ => 0 with hzs
  have hzsI : ∀ k, Gd E (zs k) ∧ Bd E (zs k) r ∧ S (zs k) := by
    intro k
    induction k with
    | zero =>
      exact ⟨fun _ => aestronglyMeasurable_const,
        fun t => Eventually.of_forall fun _ => by simp [hzs, hr0'.le], hS0⟩
    | succ k ih =>
      have e : zs (k + 1) = T (zs k) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e]
      exact ⟨hTG _ ih.1 ih.2.1, hballB _ ih.1 ih.2.1, hSinv _ ih.1 ih.2.1 ih.2.2⟩
  have hstep : ∀ k, Bd E (fun s ω => zs k s ω - zs (k + 1) s ω) (r / 2 / 2 ^ k) := by
    intro k
    induction k with
    | zero =>
      intro t
      filter_upwards [hT0 t] with ω hω
      simp only [hzs, Function.iterate_zero, id, pow_zero, div_one]
      rw [norm_sub_rev]; simpa using hω
    | succ k ih =>
      have e1 : zs (k + 1 + 1) = T (zs (k + 1)) := by
        simp only [hzs, Function.iterate_succ_apply']
      have e2 : zs (k + 1) = T (zs k) := by simp only [hzs, Function.iterate_succ_apply']
      have h := hcontr (zs (k + 1)) (zs k) (hzsI _).1 (hzsI _).1 (hzsI _).2.1 (hzsI _).2.1
        (r / 2 / 2 ^ k) (by positivity) (fun t => by
          filter_upwards [ih t] with ω hω; rwa [norm_sub_rev])
      intro t
      filter_upwards [h t] with ω hω
      rw [e1, norm_sub_rev]
      conv_lhs => rw [show zs (k + 1) t ω = T (zs k) t ω from by rw [e2]]
      calc _ ≤ r / 2 / 2 ^ k / 2 := hω
        _ = r / 2 / 2 ^ (k + 1) := by rw [pow_succ]; ring
  have hall : ∀ t, ∀ᵐ ω ∂E.μ, ∀ k, ‖zs k t ω - zs (k + 1) t ω‖ ≤ r / 2 / 2 ^ k := fun t =>
    ae_all_iff.2 fun k => hstep k t
  set z : ℕ → Ω → Fin n → ℝ := fun t ω => limUnder atTop fun k => zs k t ω with hz
  have hconv : ∀ t, ∀ᵐ ω ∂E.μ, Tendsto (fun k => zs k t ω) atTop (𝓝 (z t ω)) := fun t => by
    filter_upwards [hall t] with ω hω
    have hc : CauchySeq fun k => zs k t ω :=
      cauchySeq_of_le_geometric_two (C := r) fun k => by rw [dist_eq_norm]; exact hω k
    obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hc
    exact tendsto_nhds_limUnder ⟨l, hl⟩
  have hzG : Gd E z := fun t =>
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hzsI k).1 t) (hconv t)
  have hzdist : ∀ k, Bd E (fun s ω => zs k s ω - z s ω) (r / 2 ^ k) := fun k t => by
    filter_upwards [hall t, hconv t] with ω hω hc
    have := dist_le_of_le_geometric_two_of_tendsto (C := r) (f := fun k => zs k t ω)
      (fun k => by rw [dist_eq_norm]; exact hω k) hc k
    rwa [dist_eq_norm] at this
  have hzB : Bd E z r := fun t => by
    filter_upwards [hconv t, ae_all_iff.2 fun k => (hzsI k).2.1 t] with ω hc hb
    exact le_of_tendsto' hc.norm hb
  have hfix : ∀ t, T z t =ᵐ[E.μ] z t := by
    intro t
    have hTn : ∀ k, Bd E (fun s ω => T z s ω - T (zs k) s ω) (r / 2 ^ k / 2) := fun k =>
      hcontr z (zs k) hzG (hzsI k).1 hzB (hzsI k).2.1 (r / 2 ^ k) (by positivity) (fun t => by
        filter_upwards [hzdist k t] with ω hω; rwa [norm_sub_rev])
    filter_upwards [hconv t, ae_all_iff.2 fun k => hTn k t] with ω hc hT'
    have hlim : Tendsto (fun k => zs (k + 1) t ω) atTop (𝓝 (T z t ω)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hg : Tendsto (fun k : ℕ => r / 2 ^ k / 2) atTop (𝓝 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (r / 2)
        simp only [mul_zero] at this
        refine this.congr fun k => ?_
        rw [one_div, inv_pow]; field_simp
      refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hg
      have e : zs (k + 1) = T (zs k) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e, norm_sub_rev]
      exact hT' k
    exact tendsto_nhds_unique hlim (hc.comp (tendsto_add_atTop_nat 1))
  have hl0 : ∀ t, Linv (PhiA E Q N e z) t =ᵐ[E.μ] fun _ => 0 := fun t => by
    filter_upwards [hfix t] with ω hω
    have := congrArg (fun v => z t ω - v) hω
    simp only [hT, sub_sub_cancel, sub_self] at this
    exact this
  obtain ⟨-, -, hLz⟩ := hL _ _ (hPhiG z hzG) (add_nonneg hCQ0 hCN0) (hPhiB z hzB)
  refine ⟨z, hSlim zs z (fun k => (hzsI k).2.2) hconv, hzG, hzB, fun t => ?_⟩
  have hc := LA_congr E (Q := Q) (N := N) hl0 t
  rw [LA_zero] at hc
  filter_upwards [hLz t, hc] with ω h1 h2
  rw [← h1, h2]; rfl

end Woodford.StabilizationWelfare.NonlinearRotembergAENewton
