/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearNKMarkovRamseyAEIFT
import StabilizationWelfare.TidyR6bRamseyNewton

/-!
# The Newton contraction on a filtered probability space, for abstract conditions

Woodford (2003), *Interest and Prices*, Chapter 7, §1–2, Chapter 6, §5, and Appendix A.3.

`NonlinearNKMarkovRamseyAEIFT.ramsey_existence_ae` uses the exact Calvo Ramsey conditions only
through `C¹` smoothness, the steady state, and an a.s. inverse of the linearised operator with a
uniform `RHyp` bound, the right-inverse property a.s. and a.s. injectivity on adapted bounded
processes. Here the theorem is proved for ANY `C¹` conditions `Q(e, w₋, w) + E_t N(w′)` in `ℝ⁹`
with any disturbance space `ℝᵏ` (restated from that module).

* `LGA`, `PhiGA`; `MvA_clm`, `rhyp_LGA`, `LGA_sub`, `LGA_ae_zero`.
* `InvBoundA`, `Li_LGA`, `Li_subA`: the three properties and their consequences.
* **`newton_ae`**: an adapted solution within `r`, a.s. unique among adapted solutions within
  `r`, with `‖z‖ ≤ C‖Φ(0)‖` a.s., on every filtered probability space.
-/

namespace Woodford.StabilizationWelfare.TidyR6bRamseyNewtonAE

universe u

open MeasureTheory Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovGeneral NonlinearNKMarkovRamseyTree ExpectationsMeasure
open NonlinearNKMarkovAE NonlinearNKMarkovAEAdapted NonlinearNKMarkovRamseyAE
open NonlinearNKMarkovRamseyIFT (remainder_gen)
open NonlinearNKMarkovRamseyAEIFT (lagIA rhyp_of adA_of_rhyp adV_mono)
open TidyR6bRamseyNewton (fderiv_snd_comp)

variable {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)

/-- Woodford (2003), Ch. 7 and App. A.3 (**the linearised operator of abstract conditions, a.s.
form**): `(Lv)_t = DQ(0)(0, v_{t−1}, v_t) + DN(0)(E_t v_{t+1})`, zero lag at date `0`. -/
noncomputable def LGA (Q : (Fin k → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) → Fin 9 → ℝ)
    (N : (Fin 9 → ℝ) → Fin 9 → ℝ) (v : ℕ → Ω → Fin 9 → ℝ) (t : ℕ) (ω : Ω) : Fin 9 → ℝ :=
  fderiv ℝ Q 0 (0, lagvS v t ω, v t ω) + fderiv ℝ N 0 (MvA E v t ω)

/-- Woodford (2003), Ch. 7 (**the exact conditions on a filtered probability space**):
`Q(e_t, lag z_t, z_t) + E_t N(z_{t+1})`, with the predetermined initial value `d`. -/
noncomputable def PhiGA (Q : (Fin k → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) → Fin 9 → ℝ)
    (N : (Fin 9 → ℝ) → Fin 9 → ℝ) (e : ℕ → Ω → Fin k → ℝ) (d : Ω → Fin 9 → ℝ)
    (z : ℕ → Ω → Fin 9 → ℝ) (t : ℕ) (ω : Ω) : Fin 9 → ℝ :=
  Q (e t ω, lagIA z d t ω, z t ω) + MvA E (fun s ω' => N (z s ω')) t ω

/-- Woodford (2003), App. A.3: the forecast a.s. commutes with a linear map. -/
theorem MvA_clm (A : (Fin 9 → ℝ) →L[ℝ] (Fin 9 → ℝ)) {w : ℕ → Ω → Fin 9 → ℝ} (hw : Gd E w)
    {B : ℝ} (hb : Bd E w B) (t : ℕ) :
    MvA E (fun s ω => A (w s ω)) t =ᵐ[E.μ] fun ω => A (MvA E w t ω) := by
  have e : ∀ v, A v = (LinearMap.toMatrix' A.toLinearMap).mulVec v := fun v => by
    rw [LinearMap.toMatrix'_mulVec]; rfl
  simp only [e]
  exact MvA_mulVec E _ hw hb t

/-- Woodford (2003), App. A.3: the linearised operator maps adapted bounded processes to adapted
bounded processes. -/
theorem rhyp_LGA (Q : (Fin k → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) → Fin 9 → ℝ)
    (N : (Fin 9 → ℝ) → Fin 9 → ℝ) {v : ℕ → Ω → Fin 9 → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hv : RHyp E v B) :
    RHyp E (LGA E Q N v) ((‖fderiv ℝ Q 0‖ + ‖fderiv ℝ N 0‖) * B) := by
  have hl : ∀ k, AdB E (fun t ω => lagvS v t ω k) 1 B := fun k =>
    adb_lag E (by positivity) (hv k)
  have hm : ∀ k, AdB E (fun t ω => MvA E v t ω k) 1 B := fun k => adb_Ms E (hv k)
  intro i
  refine ⟨fun t => ?_, fun t => ?_⟩
  · have hq : AEStronglyMeasurable[E.𝓕 t] (fun ω => (lagvS v t ω, v t ω, MvA E v t ω)) E.μ :=
      (aesmSub_vec fun i => (hl i).1 t).prodMk
        ((aesmSub_vec fun i => (hv i).1 t).prodMk (aesmSub_vec fun i => (hm i).1 t))
    have hc : Continuous fun q : (Fin 9 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) =>
        (fderiv ℝ Q 0 (0, q.1, q.2.1) + fderiv ℝ N 0 q.2.2) i :=
      (continuous_apply i).comp (((fderiv ℝ Q 0).continuous.comp
        (continuous_const.prodMk (continuous_fst.prodMk (continuous_fst.comp
          continuous_snd)))).add ((fderiv ℝ N 0).continuous.comp
            (continuous_snd.comp continuous_snd)))
    change AEStronglyMeasurable[E.𝓕 t] (fun ω => LGA E Q N v t ω i) E.μ
    exact hc.comp_aestronglyMeasurable hq
  · filter_upwards [norm_of_rhyp E hB hl t, norm_of_rhyp E hB hv t, norm_of_rhyp E hB hm t]
      with ω h1 h2 h3
    have h4 : ‖((0 : Fin k → ℝ), lagvS v t ω, v t ω)‖ ≤ B := by
      simp only [Prod.norm_def, norm_zero]
      exact max_le hB (max_le h1 h2)
    have hn : ‖LGA E Q N v t ω‖ ≤ (‖fderiv ℝ Q 0‖ + ‖fderiv ℝ N 0‖) * B := by
      calc ‖LGA E Q N v t ω‖ ≤ ‖fderiv ℝ Q 0‖ * B + ‖fderiv ℝ N 0‖ * B :=
            (norm_add_le _ _).trans (add_le_add
              (((fderiv ℝ Q 0).le_opNorm _).trans (mul_le_mul_of_nonneg_left h4 (norm_nonneg _)))
              (((fderiv ℝ N 0).le_opNorm _).trans
                (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))))
        _ = _ := by ring
    have := (norm_le_pi_norm (LGA E Q N v t ω) i).trans hn
    rw [Real.norm_eq_abs] at this
    simpa using this

/-- Woodford (2003), App. A.3: the linearised operator is a.s. subtractive. -/
theorem LGA_sub (Q : (Fin k → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) → Fin 9 → ℝ)
    (N : (Fin 9 → ℝ) → Fin 9 → ℝ) {v w : ℕ → Ω → Fin 9 → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hv : RHyp E v B) (hw : RHyp E w B) (t : ℕ) :
    LGA E Q N (fun s ω => v s ω - w s ω) t =ᵐ[E.μ]
      fun ω => LGA E Q N v t ω - LGA E Q N w t ω := by
  have hG : ∀ {u : ℕ → Ω → Fin 9 → ℝ}, RHyp E u B → Gd E u := fun hu s =>
    aesm_vec E fun k => (hu k).aesm E s
  filter_upwards [MvA_sub E (hG hv) (hG hw) (fun s => norm_of_rhyp E hB hv s)
    (fun s => norm_of_rhyp E hB hw s) t] with ω hm
  have hl : lagvS (fun s ω => v s ω - w s ω) t ω = lagvS v t ω - lagvS w t ω := by
    funext i; cases t <;> simp [lagvS, lagS]
  simp only [LGA, hl, hm]
  have e : ((0 : Fin k → ℝ), lagvS v t ω - lagvS w t ω, v t ω - w t ω) =
      ((0 : Fin k → ℝ), lagvS v t ω, v t ω) - (0, lagvS w t ω, w t ω) := by simp
  rw [e, map_sub, map_sub]
  abel

/-- Woodford (2003), Ch. 7 and App. A.3: the linearised operator of an a.s. zero process is a.s.
zero. -/
theorem LGA_ae_zero (Q : (Fin k → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) → Fin 9 → ℝ)
    (N : (Fin 9 → ℝ) → Fin 9 → ℝ) {w : ℕ → Ω → Fin 9 → ℝ} (h : ∀ t, w t =ᵐ[E.μ] 0)
    (t : ℕ) : LGA E Q N w t =ᵐ[E.μ] 0 := by
  have hm : ∀ k, E.E t (fun ω' => w (t + 1) ω' k) =ᵐ[E.μ] 0 := fun k => by
    have := E.E_congr (x := fun ω' => w (t + 1) ω' k) (y := 0) (by
      filter_upwards [h (t + 1)] with ω hω; simp [hω]) t
    rwa [E.E_zero] at this
  have hl : ∀ᵐ ω ∂E.μ, lagvS w t ω = 0 := by
    cases t with
    | zero => exact Eventually.of_forall fun ω => by funext k; simp [lagvS, lagS]
    | succ t =>
      filter_upwards [h t] with ω hω
      funext k; simp [lagvS, lagS, hω]
  filter_upwards [h t, hl, ae_all_iff.2 hm] with ω h1 h2 h3
  have h3' : MvA E w t ω = 0 := funext fun k => h3 k
  simp only [LGA, h1, h2, h3', Pi.zero_apply]
  have : ((0 : Fin k → ℝ), (0 : Fin 9 → ℝ), (0 : Fin 9 → ℝ)) = 0 := rfl
  rw [this, map_zero, map_zero, add_zero]

/-- Woodford (2003), App. A.3: the three properties of an a.s. inverse family (uniform `RHyp`
bound, right inverse a.s., a.s. injectivity on adapted bounded processes). -/
def InvBoundA (Q : (Fin k → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) → Fin 9 → ℝ)
    (N : (Fin 9 → ℝ) → Fin 9 → ℝ)
    (Li : ∀ {Ω : Type u} [MeasurableSpace Ω], MeasExpectationSystem Ω →
      (ℕ → Ω → Fin 9 → ℝ) → ℕ → Ω → Fin 9 → ℝ) : Prop :=
  (∃ K, 0 ≤ K ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)
      (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → RHyp E r A → RHyp E (Li E r) (K * A)) ∧
  (∀ {Ω : Type u} [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 9 → ℝ)
      (A : ℝ), 0 ≤ A → RHyp E r A → ∀ t, LGA E Q N (Li E r) t =ᵐ[E.μ] r t) ∧
  ∀ {Ω : Type u} [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (v : ℕ → Ω → Fin 9 → ℝ)
      (B : ℝ), 0 ≤ B → RHyp E v B → (∀ t, LGA E Q N v t =ᵐ[E.μ] 0) → ∀ t, v t =ᵐ[E.μ] 0

/-- Woodford (2003), App. A.3 (**the left inverse a.s.**). -/
theorem Li_LGA {Q : (Fin k → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) → Fin 9 → ℝ}
    {N : (Fin 9 → ℝ) → Fin 9 → ℝ}
    {Li : ∀ {Ω : Type u} [MeasurableSpace Ω], MeasExpectationSystem Ω →
      (ℕ → Ω → Fin 9 → ℝ) → ℕ → Ω → Fin 9 → ℝ}
    {Ω : Type u} [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (hL : InvBoundA Q N Li)
    {v : ℕ → Ω → Fin 9 → ℝ} {B : ℝ} (hB : 0 ≤ B) (hv : RHyp E v B) (t : ℕ) :
    Li E (LGA E Q N v) t =ᵐ[E.μ] v t := by
  obtain ⟨⟨K, hK, hKr⟩, hRi, hIn⟩ := hL
  set CL := ‖fderiv ℝ Q 0‖ + ‖fderiv ℝ N 0‖
  have hLv := rhyp_LGA E Q N hB hv
  have hw := hKr E _ _ (by positivity) hLv
  set M := B + K * (CL * B)
  have hKC : 0 ≤ K * (CL * B) := by positivity
  have hvM := rhyp_mono E hv (show B ≤ M by linarith)
  have hwM := rhyp_mono E hw (show K * (CL * B) ≤ M by linarith)
  have hd := rhyp_sub E hvM hwM
  have hz := hIn E (fun s ω => v s ω - Li E (LGA E Q N v) s ω) (2 * M)
    (by positivity) hd (fun s => by
      filter_upwards [LGA_sub E Q N (by positivity) hvM hwM s,
        hRi E (LGA E Q N v) _ (by positivity) hLv s] with ω h1 h2
      rw [h1, h2, sub_self]; rfl) t
  filter_upwards [hz] with ω h
  exact (sub_eq_zero.1 (by simpa using h)).symm

/-- Woodford (2003), App. A.3: the inverse is a.s. subtractive. -/
theorem Li_subA {Q : (Fin k → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) → Fin 9 → ℝ}
    {N : (Fin 9 → ℝ) → Fin 9 → ℝ}
    {Li : ∀ {Ω : Type u} [MeasurableSpace Ω], MeasExpectationSystem Ω →
      (ℕ → Ω → Fin 9 → ℝ) → ℕ → Ω → Fin 9 → ℝ}
    {Ω : Type u} [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (hL : InvBoundA Q N Li)
    {r r' : ℕ → Ω → Fin 9 → ℝ} {A : ℝ} (hA : 0 ≤ A) (hr : RHyp E r A) (hr' : RHyp E r' A)
    (t : ℕ) : Li E (fun s ω => r s ω - r' s ω) t =ᵐ[E.μ]
      fun ω => Li E r t ω - Li E r' t ω := by
  obtain ⟨⟨K, hK, hKr⟩, hRi, hIn⟩ := hL
  have hrd := rhyp_sub E hr hr'
  have w1 := hKr E _ _ (by positivity) hrd
  have w2 := hKr E _ _ hA hr
  have w3 := hKr E _ _ hA hr'
  set M := K * (2 * A) + K * A
  have hKA : 0 ≤ K * A := by positivity
  have hK2A : 0 ≤ K * (2 * A) := by positivity
  have h1M := rhyp_mono E w1 (show K * (2 * A) ≤ M by linarith)
  have h2M := rhyp_mono E w2 (show K * A ≤ M by linarith)
  have h3M := rhyp_mono E w3 (show K * A ≤ M by linarith)
  have h23 := rhyp_sub E h2M h3M
  have h1M' := rhyp_mono E h1M (show M ≤ 2 * M by linarith)
  have hz := hIn E (fun s ω => Li E (fun s ω => r s ω - r' s ω) s ω -
    (Li E r s ω - Li E r' s ω)) (2 * (2 * M)) (by positivity)
    (rhyp_sub E h1M' h23) (fun s => by
      filter_upwards [LGA_sub E Q N (by positivity) h1M' h23 s, LGA_sub E Q N (by positivity) h2M
        h3M s, hRi E _ _ (by positivity) hrd s,
        hRi E _ _ hA hr s, hRi E _ _ hA hr' s] with ω e1 e2 e3 e4 e5
      rw [e1, e2, e3, e4, e5]
      simp) t
  filter_upwards [hz] with ω h
  simp only [Pi.zero_apply] at h
  exact sub_eq_zero.1 h

/-- Woodford (2003), Ch. 7 and App. A.3 (**the Newton contraction for abstract conditions on a
filtered probability space**): if `Q`, `N` are `C¹`, `Q(0) + N(0) = 0`, and the linearised
operator has an a.s. inverse family with the three properties, there are `r, δ > 0` such that on
every filtered probability space, for adapted disturbances `e` and an `𝓕₀`-measurable initial
value `d` with `‖e_t‖, ‖d‖ ≤ δ` a.s., the conditions hold a.s. at every date for an adapted `z`
with `‖z_t‖ ≤ r` a.s., every adapted solution within `r` is a.s. equal to it, and
`‖z_t‖ ≤ C‖Φ(0)‖` a.s. -/
theorem newton_ae {Q : (Fin k → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) → Fin 9 → ℝ}
    {N : (Fin 9 → ℝ) → Fin 9 → ℝ} (hQ : ContDiff ℝ 1 Q) (hN : ContDiff ℝ 1 N)
    (h0 : Q 0 + N 0 = 0)
    {Li : ∀ {Ω : Type u} [MeasurableSpace Ω], MeasExpectationSystem Ω →
      (ℕ → Ω → Fin 9 → ℝ) → ℕ → Ω → Fin 9 → ℝ} (hL : InvBoundA Q N Li) :
    ∃ r > 0, ∃ δ > 0, ∃ C > 0, ∀ (Ω : Type u) [MeasurableSpace Ω]
      (E : MeasExpectationSystem Ω) (e : ℕ → Ω → Fin k → ℝ) (d : Ω → Fin 9 → ℝ), AdA E e →
        Bd E e δ → AEStronglyMeasurable[E.𝓕 0] d E.μ → (∀ᵐ ω ∂E.μ, ‖d ω‖ ≤ δ) →
        ∃ z : ℕ → Ω → Fin 9 → ℝ, (AdA E z ∧ Bd E z r ∧ ∀ t, PhiGA E Q N e d z t =ᵐ[E.μ] 0) ∧
          (∀ z' : ℕ → Ω → Fin 9 → ℝ, AdA E z' → Bd E z' r →
            (∀ t, PhiGA E Q N e d z' t =ᵐ[E.μ] 0) → ∀ t, z' t =ᵐ[E.μ] z t) ∧
          ∀ τ', 0 ≤ τ' → Bd E (PhiGA E Q N e d fun _ _ => 0) τ' → Bd E z (C * τ') := by
  obtain ⟨⟨K, hK0, hKr⟩, hRi, hIn⟩ := id hL
  set K' := K + 1 with hK'
  have hK'0 : 0 < K' := by linarith
  set η := 1 / (8 * K') with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρQ, hρQ, hQr⟩ := remainder_gen hQ hη0
  obtain ⟨ρN, hρN, hNr⟩ := remainder_gen (g := fun q : (Fin k → ℝ) × (Fin 9 → ℝ) => N q.2)
    (hN.comp contDiff_snd) hη0
  set r := min ρQ ρN with hr
  have hr0 : 0 < r := lt_min hρQ hρN
  obtain ⟨CQ, hCQ⟩ := (isCompact_closedBall (0 : (Fin k → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ))
    r).exists_bound_of_continuousOn hQ.continuous.continuousOn
  obtain ⟨CN, hCN⟩ := (isCompact_closedBall (0 : Fin 9 → ℝ) r).exists_bound_of_continuousOn
    hN.continuous.continuousOn
  have hCQ0 : 0 ≤ CQ := (norm_nonneg _).trans (hCQ 0 (Metric.mem_closedBall_self hr0.le))
  have hCN0 : 0 ≤ CN := (norm_nonneg _).trans (hCN 0 (Metric.mem_closedBall_self hr0.le))
  set τ := r / (2 * K') with hτ
  have hτ0 : 0 < τ := by positivity
  obtain ⟨δQ, hδQ, hQc⟩ := Metric.continuousAt_iff.1
    (hQ.continuous.continuousAt (x := 0)) τ hτ0
  refine ⟨r, hr0, min r (δQ / 2), lt_min hr0 (by positivity), 2 * K', by positivity,
    fun Ω _ E e d he heb hd hdb => ?_⟩
  set CL := ‖fderiv ℝ Q 0‖ + ‖fderiv ℝ N 0‖ with hCL
  have heR : Bd E e r := fun t => by
    filter_upwards [heb t] with ω h; exact h.trans (min_le_left _ _)
  have hdR : ∀ᵐ ω ∂E.μ, ‖d ω‖ ≤ r := by
    filter_upwards [hdb] with ω h; exact h.trans (min_le_left _ _)
  have hlagB : ∀ z : ℕ → Ω → Fin 9 → ℝ, Bd E z r → Bd E (lagIA z d) r := fun z hz t => by
    cases t with
    | zero => exact hdR
    | succ t => exact hz t
  have hlagA : ∀ z : ℕ → Ω → Fin 9 → ℝ, AdA E z → AdA E (lagIA z d) := fun z hz t => by
    cases t with
    | zero => exact hd
    | succ t => exact adV_mono E (Nat.le_succ t) (hz t)
  have hin : ∀ z : ℕ → Ω → Fin 9 → ℝ, Bd E z r → ∀ t, ∀ᵐ ω ∂E.μ,
      (e t ω, lagIA z d t ω, z t ω) ∈ Metric.closedBall (0 : (Fin k → ℝ) × (Fin 9 → ℝ) ×
        (Fin 9 → ℝ)) r := fun z hz t => by
    filter_upwards [heR t, hlagB z hz t, hz t] with ω h1 h2 h3
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Prod.norm_def]
    exact max_le h1 (max_le h2 h3)
  have hNb : ∀ w : ℕ → Ω → Fin 9 → ℝ, Bd E w r → Bd E (fun s ω => N (w s ω)) CN :=
    fun w hw t => by
      filter_upwards [hw t] with ω h
      exact hCN _ (by rw [Metric.mem_closedBall, dist_zero_right]; exact h)
  have hNg : ∀ w : ℕ → Ω → Fin 9 → ℝ, Gd E w → Gd E (fun s ω => N (w s ω)) :=
    fun w hw t => hN.continuous.comp_aestronglyMeasurable (hw t)
  have hgd : ∀ w : ℕ → Ω → Fin 9 → ℝ, AdA E w → Gd E w := fun w hw t =>
    aesm_vec E fun k => aesm_of_sub (E.𝓕.le t)
      ((continuous_apply k).comp_aestronglyMeasurable (hw t))
  have hPhiB : ∀ z : ℕ → Ω → Fin 9 → ℝ, Bd E z r → Bd E (PhiGA E Q N e d z) (CQ + CN) :=
    fun z hz t => by
      filter_upwards [hin z hz t, MvA_bd E hCN0 (hNb z hz) t] with ω h1 h2
      exact (norm_add_le _ _).trans (add_le_add (hCQ _ h1) h2)
  have hPhiA : ∀ z : ℕ → Ω → Fin 9 → ℝ, AdA E z → AdA E (PhiGA E Q N e d z) := fun z hz t =>
    (hQ.continuous.comp_aestronglyMeasurable
      ((he t).prodMk ((hlagA z hz t).prodMk (hz t)))).add (adA_MvA E _ t)
  have hPhiR : ∀ z : ℕ → Ω → Fin 9 → ℝ, AdA E z → Bd E z r →
      RHyp E (PhiGA E Q N e d z) (CQ + CN) := fun z hz hzb =>
    rhyp_of E (hPhiA z hz) (hPhiB z hzb)
  have hLinvB : ∀ (s : ℕ → Ω → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → RHyp E s A →
      Bd E (Li E s) (K' * A) := fun s A hA hs t => by
    filter_upwards [norm_of_rhyp E (by positivity) (hKr E s A hA hs) t] with ω h
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith) hA)
  -- the Newton map
  set T : (ℕ → Ω → Fin 9 → ℝ) → (ℕ → Ω → Fin 9 → ℝ) :=
    fun z t ω => z t ω - Li E (PhiGA E Q N e d z) t ω with hT
  have hTA : ∀ z : ℕ → Ω → Fin 9 → ℝ, AdA E z → Bd E z r → AdA E (T z) := fun z hz hzb t =>
    (hz t).sub (adA_of_rhyp E (hKr E _ _ (by positivity) (hPhiR z hz hzb)) t)
  have hcontr : ∀ z z' : ℕ → Ω → Fin 9 → ℝ, AdA E z → AdA E z' → Bd E z r → Bd E z' r →
      ∀ D, 0 ≤ D → Bd E (fun s ω => z s ω - z' s ω) D →
        Bd E (fun s ω => T z s ω - T z' s ω) (D / 2) := by
    intro z z' hz hz' hzb hz'b D hD0 hD
    set dd : ℕ → Ω → Fin 9 → ℝ := fun s ω => z s ω - z' s ω with hdd
    have hdA : AdA E dd := fun t => (hz t).sub (hz' t)
    have hdR : RHyp E dd D := rhyp_of E hdA hD
    -- the remainder
    have hRN : Bd E (fun s ω => N (z s ω) - N (z' s ω) - fderiv ℝ N 0 (dd s ω)) (η * D) :=
      fun t => by
        filter_upwards [hzb t, hz'b t, hD t] with ω h2 h3 h4
        have := hNr 0 (z t ω) (z' t ω) (by rw [norm_zero]; exact hρN.le)
          (h2.trans (min_le_right _ _)) (h3.trans (min_le_right _ _))
        rw [fderiv_snd_comp hN] at this
        exact this.trans (mul_le_mul_of_nonneg_left h4 hη0.le)
    have hNdg : Gd E (fun s ω => N (z s ω) - N (z' s ω)) := fun t =>
      ((hNg z (hgd z hz)) t).sub ((hNg z' (hgd z' hz')) t)
    have hNdb : Bd E (fun s ω => N (z s ω) - N (z' s ω)) (CN + CN) := fun t => by
      filter_upwards [hNb z hzb t, hNb z' hz'b t] with ω h1 h2
      exact (norm_sub_le _ _).trans (add_le_add h1 h2)
    have hDNg : Gd E (fun s ω => fderiv ℝ N 0 (dd s ω)) := fun t =>
      (fderiv ℝ N 0).continuous.comp_aestronglyMeasurable (hgd dd hdA t)
    have hDNb : Bd E (fun s ω => fderiv ℝ N 0 (dd s ω))
        (‖fderiv ℝ N 0‖ * D) := fun t => by
      filter_upwards [hD t] with ω h
      exact ((fderiv ℝ N 0).le_opNorm (dd t ω)).trans
        (mul_le_mul_of_nonneg_left h (norm_nonneg _))
    have hrem : Bd E (fun s ω => PhiGA E Q N e d z s ω - PhiGA E Q N e d z' s ω -
        LGA E Q N dd s ω) (η * D + η * D) := by
      intro t
      have s1 := MvA_sub E (hNg z (hgd z hz)) (hNg z' (hgd z' hz')) (hNb z hzb) (hNb z' hz'b) t
      have s2 := MvA_sub E hNdg hDNg hNdb hDNb t
      have s3 := MvA_clm E (fderiv ℝ N 0) (hgd dd hdA) hD t
      have hRb := MvA_bd E (by positivity) hRN t
      have hlD : ∀ᵐ ω ∂E.μ, ‖lagIA z d t ω - lagIA z' d t ω‖ ≤ D := by
        cases t with
        | zero => exact Eventually.of_forall fun ω => by simp [lagIA, hD0]
        | succ t => exact hD t
      filter_upwards [s1, s2, s3, hRb, heR t, hlagB z hzb t, hlagB z' hz'b t, hzb t, hz'b t,
        hD t, hlD] with ω m1 m2 m3 hR h1 h2 h3 h4 h5 h6 h7
      have hl : lagvS dd t ω = lagIA z d t ω - lagIA z' d t ω := by
        funext i; cases t <;> simp [lagvS, lagS, lagIA, hdd]
      have hu1 : ‖(lagIA z d t ω, z t ω)‖ ≤ ρQ := by
        rw [Prod.norm_def]; exact max_le (h2.trans (min_le_left _ _)) (h4.trans (min_le_left _ _))
      have hu2 : ‖(lagIA z' d t ω, z' t ω)‖ ≤ ρQ := by
        rw [Prod.norm_def]; exact max_le (h3.trans (min_le_left _ _)) (h5.trans (min_le_left _ _))
      have hq := hQr (e t ω) _ _ (h1.trans (min_le_left _ _)) hu1 hu2
      rw [Prod.mk_sub_mk, show fderiv ℝ Q ((0 : Fin k → ℝ),
        (0 : (Fin 9 → ℝ) × (Fin 9 → ℝ))) = fderiv ℝ Q 0 from rfl] at hq
      have hqD : ‖(lagIA z d t ω - lagIA z' d t ω, z t ω - z' t ω)‖ ≤ D := by
        rw [Prod.norm_def]; exact max_le h7 h6
      have key : PhiGA E Q N e d z t ω - PhiGA E Q N e d z' t ω - LGA E Q N dd t ω =
          (Q (e t ω, lagIA z d t ω, z t ω) - Q (e t ω, lagIA z' d t ω, z' t ω) -
            fderiv ℝ Q 0 (0, lagIA z d t ω - lagIA z' d t ω, z t ω - z' t ω)) +
          MvA E (fun s ω => N (z s ω) - N (z' s ω) - fderiv ℝ N 0 (dd s ω)) t ω := by
        rw [m2, m1, m3]
        simp only [PhiGA, LGA]
        rw [hl]
        simp only [hdd]
        abel
      rw [key]
      exact (norm_add_le _ _).trans (add_le_add (hq.trans
        (mul_le_mul_of_nonneg_left hqD hη0.le)) hR)
    -- the inverse of the remainder
    have hPz := hPhiR z hz hzb
    have hPz' := hPhiR z' hz' hz'b
    have hPd := rhyp_sub E hPz hPz'
    have hLd := rhyp_LGA E Q N hD0 hdR
    set M := 2 * (CQ + CN) + CL * D
    have hCLD : 0 ≤ CL * D := by positivity
    have hCC : 0 ≤ 2 * (CQ + CN) := by positivity
    have hM1 : 2 * (CQ + CN) ≤ M := by linarith
    have hM2 : CL * D ≤ M := by linarith
    have hresA : AdA E (fun s ω => PhiGA E Q N e d z s ω - PhiGA E Q N e d z' s ω -
        LGA E Q N dd s ω) := fun t => (adA_of_rhyp E hPd t).sub (adA_of_rhyp E hLd t)
    have hresR := rhyp_of E hresA hrem
    have hb := hLinvB _ _ (by positivity) hresR
    intro t
    filter_upwards [Li_subA E hL (by positivity) hPz hPz' t,
      Li_subA E hL (by positivity) (rhyp_mono E hPd hM1) (rhyp_mono E hLd hM2) t,
      Li_LGA E hL hD0 hdR t, hb t] with ω h1 h2 h3 h4
    have key : T z t ω - T z' t ω = -Li E (fun s ω => PhiGA E Q N e d z s ω -
        PhiGA E Q N e d z' s ω - LGA E Q N dd s ω) t ω := by
      rw [h2]
      simp only [hT]
      rw [h1, h3]
      funext i
      simp only [Pi.sub_apply, Pi.neg_apply, hdd]
      ring
    rw [key, norm_neg]
    calc _ ≤ _ := h4
      _ = D / 4 := by rw [hη]; field_simp; ring
      _ ≤ D / 2 := by linarith
  have h0A : AdA E (fun _ _ => (0 : Fin 9 → ℝ)) := fun _ => aestronglyMeasurable_const
  have h0B : Bd E (fun _ _ => (0 : Fin 9 → ℝ)) r := fun _ =>
    Eventually.of_forall fun _ => by simp [hr0.le]
  -- `T 0` is small
  have hT0 : Bd E (T fun _ _ => 0) (r / 2) := by
    have hb : Bd E (PhiGA E Q N e d fun _ _ => 0) τ := fun t => by
      have hss := h0
      filter_upwards [heb t, hlagB _ h0B t, hdb] with ω h1 h2 h3
      have e1 : PhiGA E Q N e d (fun _ _ => 0) t ω =
          Q (e t ω, lagIA (fun _ _ => 0) d t ω, 0) - Q 0 := by
        simp only [PhiGA, MvA_const]
        rw [eq_neg_of_add_eq_zero_right hss]
        abel
      rw [e1, ← dist_eq_norm]
      refine (hQc ?_).le
      rw [dist_zero_right, Prod.norm_def, Prod.norm_def]
      have hl : ‖lagIA (fun _ _ => (0 : Fin 9 → ℝ)) d t ω‖ ≤ δQ / 2 := by
        cases t with
        | zero => exact h3.trans (min_le_right _ _)
        | succ t => simp only [lagIA, norm_zero]; positivity
      have h0' : ‖(0 : Fin 9 → ℝ)‖ ≤ δQ / 2 := by rw [norm_zero]; positivity
      exact lt_of_le_of_lt (max_le (h1.trans (min_le_right _ _)) (max_le hl h0')) (by linarith)
    have hl := hLinvB _ _ hτ0.le (rhyp_of E (hPhiA _ h0A) hb)
    intro t
    filter_upwards [hl t] with ω hω
    simp only [hT, zero_sub, norm_neg]
    calc _ ≤ K' * τ := hω
      _ = r / 2 := by rw [hτ]; field_simp
  have hballB : ∀ z, AdA E z → Bd E z r → Bd E (T z) r := by
    intro z hz hzb t
    have h1 := hcontr z (fun _ _ => 0) hz h0A hzb h0B r hr0.le
      (fun t => by filter_upwards [hzb t] with ω hω; simpa using hω) t
    filter_upwards [h1, hT0 t] with ω e1 e2
    calc ‖T z t ω‖ ≤ ‖T z t ω - T (fun _ _ => 0) t ω‖ + ‖T (fun _ _ => 0) t ω‖ := by
          have := norm_add_le (T z t ω - T (fun _ _ => 0) t ω) (T (fun _ _ => 0) t ω)
          simpa using this
      _ ≤ r / 2 + r / 2 := add_le_add e1 e2
      _ = r := by ring
  -- Picard iteration
  set zs : ℕ → ℕ → Ω → Fin 9 → ℝ := fun n => T^[n] fun _ _ => 0 with hzs
  have hzsI : ∀ n, AdA E (zs n) ∧ Bd E (zs n) r := by
    intro n
    induction n with
    | zero => exact ⟨h0A, h0B⟩
    | succ n ih =>
      have e : zs (n + 1) = T (zs n) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e]; exact ⟨hTA _ ih.1 ih.2, hballB _ ih.1 ih.2⟩
  have hstep : ∀ n, Bd E (fun s ω => zs n s ω - zs (n + 1) s ω) (r / 2 / 2 ^ n) := by
    intro n
    induction n with
    | zero =>
      intro t
      filter_upwards [hT0 t] with ω hω
      simp only [hzs, Function.iterate_zero, id, pow_zero, div_one]
      rw [norm_sub_rev]; simpa using hω
    | succ n ih =>
      have e1 : zs (n + 1 + 1) = T (zs (n + 1)) := by
        simp only [hzs, Function.iterate_succ_apply']
      have e2 : zs (n + 1) = T (zs n) := by simp only [hzs, Function.iterate_succ_apply']
      have h := hcontr (zs (n + 1)) (zs n) (hzsI _).1 (hzsI _).1 (hzsI _).2 (hzsI _).2
        (r / 2 / 2 ^ n) (by positivity) (fun t => by
          filter_upwards [ih t] with ω hω; rwa [norm_sub_rev])
      intro t
      filter_upwards [h t] with ω hω
      rw [e1, norm_sub_rev]
      conv_lhs => rw [show zs (n + 1) t ω = T (zs n) t ω from by rw [e2]]
      calc _ ≤ r / 2 / 2 ^ n / 2 := hω
        _ = r / 2 / 2 ^ (n + 1) := by rw [pow_succ]; ring
  have hall : ∀ t, ∀ᵐ ω ∂E.μ, ∀ n, ‖zs n t ω - zs (n + 1) t ω‖ ≤ r / 2 / 2 ^ n := fun t =>
    ae_all_iff.2 fun n => hstep n t
  set z : ℕ → Ω → Fin 9 → ℝ := fun t ω => limUnder atTop fun n => zs n t ω with hz
  have hconv : ∀ t, ∀ᵐ ω ∂E.μ, Tendsto (fun n => zs n t ω) atTop (𝓝 (z t ω)) := fun t => by
    filter_upwards [hall t] with ω hω
    have hc : CauchySeq fun n => zs n t ω :=
      cauchySeq_of_le_geometric_two (C := r) fun n => by rw [dist_eq_norm]; exact hω n
    obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hc
    exact tendsto_nhds_limUnder ⟨l, hl⟩
  have hzA : AdA E z := fun t => aesmSub_lim (fun n => (hzsI n).1 t) (hconv t)
  have hzdist : ∀ n, Bd E (fun s ω => zs n s ω - z s ω) (r / 2 ^ n) := fun n t => by
    filter_upwards [hall t, hconv t] with ω hω hc
    have := dist_le_of_le_geometric_two_of_tendsto (C := r) (f := fun n => zs n t ω)
      (fun n => by rw [dist_eq_norm]; exact hω n) hc n
    rwa [dist_eq_norm] at this
  have hzB : Bd E z r := fun t => by
    filter_upwards [hconv t, ae_all_iff.2 fun n => (hzsI n).2 t] with ω hc hb
    exact le_of_tendsto' hc.norm hb
  have hfix : ∀ t, T z t =ᵐ[E.μ] z t := by
    intro t
    have hTn : ∀ n, Bd E (fun s ω => T z s ω - T (zs n) s ω) (r / 2 ^ n / 2) := fun n =>
      hcontr z (zs n) hzA (hzsI n).1 hzB (hzsI n).2 (r / 2 ^ n) (by positivity) (fun t => by
        filter_upwards [hzdist n t] with ω hω; rwa [norm_sub_rev])
    filter_upwards [hconv t, ae_all_iff.2 fun n => hTn n t] with ω hc hT'
    have hlim : Tendsto (fun n => zs (n + 1) t ω) atTop (𝓝 (T z t ω)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hg : Tendsto (fun n : ℕ => r / 2 ^ n / 2) atTop (𝓝 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (r / 2)
        simp only [mul_zero] at this
        refine this.congr fun n => ?_
        rw [one_div, inv_pow]; field_simp
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hg
      have e : zs (n + 1) = T (zs n) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e, norm_sub_rev]
      exact hT' n
    exact tendsto_nhds_unique hlim (hc.comp (tendsto_add_atTop_nat 1))
  -- fixed points are the solutions
  have hsol : ∀ w, AdA E w → Bd E w r →
      ((∀ t, T w t =ᵐ[E.μ] w t) ↔ ∀ t, PhiGA E Q N e d w t =ᵐ[E.μ] 0) := by
    intro w hw hwb
    have hP := hPhiR w hw hwb
    have hLL := hRi E _ _ (by positivity) hP
    constructor
    · intro h t
      have hl0 : ∀ s, Li E (PhiGA E Q N e d w) s =ᵐ[E.μ] 0 := fun s => by
        filter_upwards [h s] with ω hω
        have := congrArg (fun v => w s ω - v) hω
        simp only [hT, sub_sub_cancel, sub_self] at this
        exact this
      filter_upwards [hLL t, LGA_ae_zero E Q N hl0 t] with ω h1 h2
      rw [← h1, h2]
    · intro h t
      have hz0 := hIn E (Li E (PhiGA E Q N e d w)) _
        (by positivity) (hKr E _ _ (by positivity) hP) (fun s => by
          filter_upwards [hLL s, h s] with ω h1 h2
          rw [h1, h2]) t
      filter_upwards [hz0] with ω hω
      simp only [hT, hω, Pi.zero_apply, sub_zero]
  have hsmall : ∀ τ', 0 ≤ τ' → Bd E (PhiGA E Q N e d fun _ _ => 0) τ' →
      Bd E z (2 * K' * τ') := by
    intro τ' hτ' hb
    have hl := hLinvB _ _ hτ' (rhyp_of E (hPhiA _ h0A) hb)
    have hT0' : Bd E (T fun _ _ => 0) (K' * τ') := fun t => by
      filter_upwards [hl t] with ω hω
      simp only [hT, zero_sub, norm_neg]; exact hω
    have hn : ∀ n : ℕ, Bd E z (r / 2 ^ n + 2 * K' * τ') := by
      intro n
      induction n with
      | zero =>
        intro t
        filter_upwards [hzB t] with ω h
        have : 0 ≤ 2 * K' * τ' := by positivity
        simp only [pow_zero, div_one]; linarith
      | succ n ih =>
        have h := hcontr z (fun _ _ => 0) hzA h0A hzB h0B (r / 2 ^ n + 2 * K' * τ')
          (by positivity) (fun t => by filter_upwards [ih t] with ω hω; simpa using hω)
        intro t
        filter_upwards [h t, hfix t, hT0' t] with ω h1 h2 h3
        rw [h2] at h1
        calc ‖z t ω‖ ≤ ‖z t ω - T (fun _ _ => 0) t ω‖ + ‖T (fun _ _ => 0) t ω‖ := by
              have := norm_add_le (z t ω - T (fun _ _ => 0) t ω) (T (fun _ _ => 0) t ω)
              simpa using this
          _ ≤ (r / 2 ^ n + 2 * K' * τ') / 2 + K' * τ' := add_le_add h1 h3
          _ = r / 2 ^ (n + 1) + 2 * K' * τ' := by rw [pow_succ]; ring
    intro t
    have ht : Tendsto (fun n : ℕ => r / 2 ^ n + 2 * K' * τ') atTop (𝓝 (0 + 2 * K' * τ')) := by
      refine Tendsto.add ?_ tendsto_const_nhds
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul r
      simp only [mul_zero] at this
      refine this.congr fun n => ?_
      rw [one_div, inv_pow]; field_simp
    filter_upwards [ae_all_iff.2 fun n => hn n t] with ω h
    have := ge_of_tendsto' ht h
    simpa using this
  refine ⟨z, ⟨hzA, hzB, (hsol z hzA hzB).1 hfix⟩, fun z' hz'A hz'B hz' => ?_, hsmall⟩
  have hfix' := (hsol z' hz'A hz'B).2 hz'
  have hD : ∀ n : ℕ, Bd E (fun s ω => z' s ω - z s ω) (2 * r / 2 ^ n) := by
    intro n
    induction n with
    | zero =>
      intro t
      filter_upwards [hz'B t, hzB t] with ω h1 h2
      have := (norm_sub_le (z' t ω) (z t ω)).trans (add_le_add h1 h2)
      simp only [pow_zero, div_one]; linarith
    | succ n ih =>
      have h := hcontr z' z hz'A hzA hz'B hzB _ (by positivity) ih
      intro t
      filter_upwards [h t, hfix t, hfix' t] with ω h1 h2 h3
      rw [h2, h3] at h1
      exact h1.trans (le_of_eq (by rw [pow_succ]; ring))
  intro t
  have ht : Tendsto (fun n : ℕ => 2 * r / 2 ^ n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (2 * r)
    simp only [mul_zero] at this
    refine this.congr fun n => ?_
    rw [one_div, inv_pow]; field_simp
  filter_upwards [ae_all_iff.2 fun n => hD n t] with ω h
  have := ge_of_tendsto' ht h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

end Woodford.StabilizationWelfare.TidyR6bRamseyNewtonAE
