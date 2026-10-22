/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergRamseyAE
import StabilizationWelfare.NonlinearRotembergRamseyIFT
import StabilizationWelfare.NonlinearNKMarkovRamseyAEIFT

/-!
# The timeless Rotemberg Ramsey equilibrium on a general filtered probability space

Woodford (2003), *Interest and Prices*, Chapter 7, §1–2 and Appendix A.3, for the exact
Rotemberg Ramsey conditions. The Newton contraction of
`NonlinearNKMarkovRamseyAEIFT.ramsey_existence_ae` (Calvo), with the Rotemberg a.s. inverse
`NonlinearRotembergRamseyAE.LinvRA`.

* `PhiRA`: the exact conditions `Q(e_t, lag z_t, z_t) + E_t N(z_{t+1})` with Mathlib's `condExp`,
  the predetermined initial multiplier `d` entering through `λ_{−1}`.
* **`ramsey_existence_ae`**: if `G > 0`, there are `r, δ > 0`, depending only on the parameters,
  such that on EVERY filtered probability space, for adapted `e` and `𝓕₀`-measurable `d` with
  `‖e_t‖, ‖d‖ ≤ δ` a.s., the exact Ramsey conditions have an ADAPTED solution with `‖z_t‖ ≤ r`
  a.s., and every adapted solution within `r` is a.s. equal to it at every date.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergRamseyAEIFT

open MeasureTheory Filter Topology
open NonlinearNKMarkov (Mv IsMarkov Mv_norm_le)
open NonlinearNKMarkovAE (MvA Ms Gd Bd MvA_sub MvA_mulVec MvA_bd MvA_gd aesm_vec gd_pair
  bound_improve_ae MvA_const)
open NonlinearNKMarkovAEAdapted (AdA aesmSub_vec aesmSub_lim adA_MvA)
open NonlinearNKMarkovRamseyAE (lagS lagvS AdB adb_lin2 adb_lag adb_Ms aesm_of_sub)
open NonlinearNKMarkovRamseyIFT (remainder_gen)
open ExpectationsMeasure
open NonlinearRotemberg NonlinearRotembergRamsey NonlinearRotembergRamseyLin
open NonlinearRotembergRamseyTree NonlinearRotembergRamseyAE
open NonlinearRotembergRamseyIFT (DNlin fderiv_Nd_snd)

variable {p : Par}

/-- Woodford (2003), Ch. 7: the lag with the predetermined initial value `d` at date `0`. -/
def lagIA {Ω : Type*} {n : ℕ} (z : ℕ → Ω → Fin n → ℝ) (d : Ω → Fin n → ℝ) : ℕ → Ω → Fin n → ℝ
  | 0 => d
  | t + 1 => z t

variable {Ω : Type*} [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)

/-- Woodford (2003), §5 and Ch. 7 (**the exact Ramsey conditions on a filtered probability
space**), in deviations `z = w − w̄`: `Q(e_t, lag z_t, z_t) + E_t N(z_{t+1})`. -/
noncomputable def PhiRA (p : Par) (e : ℕ → Ω → Fin 3 → ℝ) (d : Ω → Fin 5 → ℝ)
    (z : ℕ → Ω → Fin 5 → ℝ) (t : ℕ) (ω : Ω) : Fin 5 → ℝ :=
  Qd p (e t ω, lagIA z d t ω, z t ω) + MvA E (fun s ω' => Nd p (z s ω')) t ω

/-- Adapted vector processes with an a.s. sup bound satisfy `RHyp`. -/
theorem rhyp_of {w : ℕ → Ω → Fin 5 → ℝ} {A : ℝ} (hA : AdA E w) (hb : Bd E w A) : RHyp E w A :=
  fun k => ⟨fun t => (continuous_apply k).comp_aestronglyMeasurable (hA t), fun t => by
    filter_upwards [hb t] with ω h
    have := (norm_le_pi_norm (w t ω) k).trans h
    rw [Real.norm_eq_abs] at this; simpa using this⟩

/-- The vector process of an `RHyp` process is adapted. -/
theorem adA_of_rhyp {w : ℕ → Ω → Fin 5 → ℝ} {A : ℝ} (h : RHyp E w A) : AdA E w := fun t =>
  aesmSub_vec fun k => (h k).1 t

/-- The linearised operator of an a.s. zero process is a.s. zero. -/
theorem LRA_ae_zero {w : ℕ → Ω → Fin 5 → ℝ} (h : ∀ t, w t =ᵐ[E.μ] 0)
    (t : ℕ) : LRA E p w t =ᵐ[E.μ] 0 := by
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
  simp only [LRA, h1, h2, h3', Pi.zero_apply]
  funext i; fin_cases i <;> simp [DQr, DNr]

/-- Woodford (2003), App. A.3: the forecast a.s. commutes with the linearised lead. -/
theorem MvA_DNr {w : ℕ → Ω → Fin 5 → ℝ} (hw : Gd E w) {B : ℝ}
    (hb : Bd E w B) (t : ℕ) :
    MvA E (fun s ω => DNr p (w s ω)) t =ᵐ[E.μ] fun ω => DNr p (MvA E w t ω) := by
  have e : ∀ n, DNr p n = (LinearMap.toMatrix' (DNlin p)).mulVec n := fun n => by
    rw [LinearMap.toMatrix'_mulVec]; rfl
  simp only [e]
  exact MvA_mulVec E _ hw hb t

/-- A sub-σ-algebra a.s. measurable vector for an earlier date is one for a later date. -/
theorem adV_mono {s t : ℕ} (hst : s ≤ t) {n : ℕ} {f : Ω → Fin n → ℝ}
    (hf : AEStronglyMeasurable[E.𝓕 s] f E.μ) : AEStronglyMeasurable[E.𝓕 t] f E.μ :=
  ⟨hf.mk f, hf.stronglyMeasurable_mk.mono (E.𝓕.mono hst), hf.ae_eq_mk⟩

/-- Woodford (2003), Ch. 7 and App. A.3 (**EXISTENCE, ADAPTEDNESS AND A.S. UNIQUENESS of the
timeless Ramsey equilibrium on a general filtered probability space**): if `G > 0` (`0 < Gw p`),
there are `r, δ > 0`, depending only on the parameters, such that on every filtered probability
space, for adapted disturbances `e` and an `𝓕₀`-measurable predetermined initial value `d` with
`‖e_t‖, ‖d‖ ≤ δ` a.s., the exact Ramsey conditions hold a.s. at every date for an adapted `z` with
`‖z_t‖ ≤ r` a.s., and every adapted solution within `r` is a.s. equal to it. -/
theorem ramsey_existence_ae {p : Par} (hp : p.Basic) (hG : 0 < Gw p) :
    ∃ r > 0, ∃ δ > 0, ∀ (Ω : Type*) [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)
      (e : ℕ → Ω → Fin 3 → ℝ) (d : Ω → Fin 5 → ℝ), AdA E e → Bd E e δ →
        AEStronglyMeasurable[E.𝓕 0] d E.μ → (∀ᵐ ω ∂E.μ, ‖d ω‖ ≤ δ) →
        ∃ z : ℕ → Ω → Fin 5 → ℝ, (AdA E z ∧ Bd E z r ∧ ∀ t, PhiRA E p e d z t =ᵐ[E.μ] 0) ∧
          ∀ z' : ℕ → Ω → Fin 5 → ℝ, AdA E z' → Bd E z' r →
            (∀ t, PhiRA E p e d z' t =ᵐ[E.μ] 0) → ∀ t, z' t =ᵐ[E.μ] z t := by
  obtain ⟨K, hK0, hKr⟩ := rhyp_LinvRA hp hG
  set K' := K + 1 with hK'
  have hK'0 : 0 < K' := by linarith
  set η := 1 / (8 * K') with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρQ, hρQ, hQ⟩ := remainder_gen (contDiff_Qd (n := 1) p) hη0
  obtain ⟨ρN, hρN, hN⟩ := remainder_gen (g := fun q : (Fin 3 → ℝ) × (Fin 5 → ℝ) => Nd p q.2)
    ((contDiff_Nd (n := 1) p).comp contDiff_snd) hη0
  set r := min ρQ ρN with hr
  have hr0 : 0 < r := lt_min hρQ hρN
  obtain ⟨CQ, hCQ⟩ := (isCompact_closedBall (0 : (Fin 3 → ℝ) × (Fin 5 → ℝ) × (Fin 5 → ℝ))
    r).exists_bound_of_continuousOn ((contDiff_Qd (n := 0) p).continuous.continuousOn)
  obtain ⟨CN, hCN⟩ := (isCompact_closedBall (0 : Fin 5 → ℝ) r).exists_bound_of_continuousOn
    ((contDiff_Nd (n := 0) p).continuous.continuousOn)
  have hCQ0 : 0 ≤ CQ := (norm_nonneg _).trans (hCQ 0 (Metric.mem_closedBall_self hr0.le))
  have hCN0 : 0 ≤ CN := (norm_nonneg _).trans (hCN 0 (Metric.mem_closedBall_self hr0.le))
  set τ := r / (2 * K') with hτ
  have hτ0 : 0 < τ := by positivity
  obtain ⟨δQ, hδQ, hQc⟩ := Metric.continuousAt_iff.1
    ((contDiff_Qd (n := 0) p).continuous.continuousAt (x := 0)) τ hτ0
  refine ⟨r, hr0, min r (δQ / 2), lt_min hr0 (by positivity),
    fun Ω _ E e d he heb hd hdb => ?_⟩
  set CL := ‖LinearMap.toContinuousLinearMap (DLin p)‖ with hCL
  have heR : Bd E e r := fun t => by
    filter_upwards [heb t] with ω h; exact h.trans (min_le_left _ _)
  have hdR : ∀ᵐ ω ∂E.μ, ‖d ω‖ ≤ r := by
    filter_upwards [hdb] with ω h; exact h.trans (min_le_left _ _)
  have hlagB : ∀ z : ℕ → Ω → Fin 5 → ℝ, Bd E z r → Bd E (lagIA z d) r := fun z hz t => by
    cases t with
    | zero => exact hdR
    | succ t => exact hz t
  have hlagA : ∀ z : ℕ → Ω → Fin 5 → ℝ, AdA E z → AdA E (lagIA z d) := fun z hz t => by
    cases t with
    | zero => exact hd
    | succ t => exact adV_mono E (Nat.le_succ t) (hz t)
  have hin : ∀ z : ℕ → Ω → Fin 5 → ℝ, Bd E z r → ∀ t, ∀ᵐ ω ∂E.μ,
      (e t ω, lagIA z d t ω, z t ω) ∈ Metric.closedBall (0 : (Fin 3 → ℝ) × (Fin 5 → ℝ) ×
        (Fin 5 → ℝ)) r := fun z hz t => by
    filter_upwards [heR t, hlagB z hz t, hz t] with ω h1 h2 h3
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Prod.norm_def]
    exact max_le h1 (max_le h2 h3)
  have hNb : ∀ w : ℕ → Ω → Fin 5 → ℝ, Bd E w r → Bd E (fun s ω => Nd p (w s ω)) CN :=
    fun w hw t => by
      filter_upwards [hw t] with ω h
      exact hCN _ (by rw [Metric.mem_closedBall, dist_zero_right]; exact h)
  have hNg : ∀ w : ℕ → Ω → Fin 5 → ℝ, Gd E w → Gd E (fun s ω => Nd p (w s ω)) :=
    fun w hw t => (contDiff_Nd (n := 0) p).continuous.comp_aestronglyMeasurable (hw t)
  have hgd : ∀ w : ℕ → Ω → Fin 5 → ℝ, AdA E w → Gd E w := fun w hw t =>
    aesm_vec E fun k => aesm_of_sub (E.𝓕.le t)
      ((continuous_apply k).comp_aestronglyMeasurable (hw t))
  have hPhiB : ∀ z : ℕ → Ω → Fin 5 → ℝ, Bd E z r → Bd E (PhiRA E p e d z) (CQ + CN) :=
    fun z hz t => by
      filter_upwards [hin z hz t, MvA_bd E hCN0 (hNb z hz) t] with ω h1 h2
      exact (norm_add_le _ _).trans (add_le_add (hCQ _ h1) h2)
  have hPhiA : ∀ z : ℕ → Ω → Fin 5 → ℝ, AdA E z → AdA E (PhiRA E p e d z) := fun z hz t =>
    ((contDiff_Qd (n := 0) p).continuous.comp_aestronglyMeasurable
      ((he t).prodMk ((hlagA z hz t).prodMk (hz t)))).add (adA_MvA E _ t)
  have hPhiR : ∀ z : ℕ → Ω → Fin 5 → ℝ, AdA E z → Bd E z r →
      RHyp E (PhiRA E p e d z) (CQ + CN) := fun z hz hzb =>
    rhyp_of E (hPhiA z hz) (hPhiB z hzb)
  have hLinvB : ∀ (s : ℕ → Ω → Fin 5 → ℝ) (A : ℝ), 0 ≤ A → RHyp E s A →
      Bd E (LinvRA E p s) (K' * A) := fun s A hA hs t => by
    filter_upwards [norm_of_rhyp E (by positivity) (hKr E s A hA hs) t] with ω h
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith) hA)
  -- the Newton map
  set T : (ℕ → Ω → Fin 5 → ℝ) → (ℕ → Ω → Fin 5 → ℝ) :=
    fun z t ω => z t ω - LinvRA E p (PhiRA E p e d z) t ω with hT
  have hTA : ∀ z : ℕ → Ω → Fin 5 → ℝ, AdA E z → Bd E z r → AdA E (T z) := fun z hz hzb t =>
    (hz t).sub (adA_of_rhyp E (hKr E _ _ (by positivity) (hPhiR z hz hzb)) t)
  have hcontr : ∀ z z' : ℕ → Ω → Fin 5 → ℝ, AdA E z → AdA E z' → Bd E z r → Bd E z' r →
      ∀ D, 0 ≤ D → Bd E (fun s ω => z s ω - z' s ω) D →
        Bd E (fun s ω => T z s ω - T z' s ω) (D / 2) := by
    intro z z' hz hz' hzb hz'b D hD0 hD
    set dd : ℕ → Ω → Fin 5 → ℝ := fun s ω => z s ω - z' s ω with hdd
    have hdA : AdA E dd := fun t => (hz t).sub (hz' t)
    have hdR : RHyp E dd D := rhyp_of E hdA hD
    -- the remainder
    have hRN : Bd E (fun s ω => Nd p (z s ω) - Nd p (z' s ω) - DNr p (dd s ω)) (η * D) :=
      fun t => by
        filter_upwards [hzb t, hz'b t, hD t] with ω h2 h3 h4
        have := hN 0 (z t ω) (z' t ω) (by rw [norm_zero]; exact hρN.le)
          (h2.trans (min_le_right _ _)) (h3.trans (min_le_right _ _))
        rw [fderiv_Nd_snd] at this
        exact this.trans (mul_le_mul_of_nonneg_left h4 hη0.le)
    have hNdg : Gd E (fun s ω => Nd p (z s ω) - Nd p (z' s ω)) := fun t =>
      ((hNg z (hgd z hz)) t).sub ((hNg z' (hgd z' hz')) t)
    have hNdb : Bd E (fun s ω => Nd p (z s ω) - Nd p (z' s ω)) (CN + CN) := fun t => by
      filter_upwards [hNb z hzb t, hNb z' hz'b t] with ω h1 h2
      exact (norm_sub_le _ _).trans (add_le_add h1 h2)
    have hDNg : Gd E (fun s ω => DNr p (dd s ω)) := fun t =>
      (DNlin p).continuous_of_finiteDimensional.comp_aestronglyMeasurable (hgd dd hdA t)
    have hDNb : Bd E (fun s ω => DNr p (dd s ω))
        (‖LinearMap.toContinuousLinearMap (DNlin p)‖ * D) := fun t => by
      filter_upwards [hD t] with ω h
      exact ((LinearMap.toContinuousLinearMap (DNlin p)).le_opNorm (dd t ω)).trans
        (mul_le_mul_of_nonneg_left h (norm_nonneg _))
    have hrem : Bd E (fun s ω => PhiRA E p e d z s ω - PhiRA E p e d z' s ω -
        LRA E p dd s ω) (η * D + η * D) := by
      intro t
      have s1 := MvA_sub E (hNg z (hgd z hz)) (hNg z' (hgd z' hz')) (hNb z hzb) (hNb z' hz'b) t
      have s2 := MvA_sub E hNdg hDNg hNdb hDNb t
      have s3 := MvA_DNr E (p := p) (hgd dd hdA) hD t
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
      have hq := hQ (e t ω) _ _ (h1.trans (min_le_left _ _)) hu1 hu2
      rw [Prod.mk_sub_mk, show fderiv ℝ (Qd p) ((0 : Fin 3 → ℝ),
        (0 : (Fin 5 → ℝ) × (Fin 5 → ℝ))) = fderiv ℝ (Qd p) 0 from rfl, fderiv_Qd] at hq
      have hqD : ‖(lagIA z d t ω - lagIA z' d t ω, z t ω - z' t ω)‖ ≤ D := by
        rw [Prod.norm_def]; exact max_le h7 h6
      have key : PhiRA E p e d z t ω - PhiRA E p e d z' t ω - LRA E p dd t ω =
          (Qd p (e t ω, lagIA z d t ω, z t ω) - Qd p (e t ω, lagIA z' d t ω, z' t ω) -
            DQr p (lagIA z d t ω - lagIA z' d t ω) (z t ω - z' t ω)) +
          MvA E (fun s ω => Nd p (z s ω) - Nd p (z' s ω) - DNr p (dd s ω)) t ω := by
        rw [m2, m1, m3]
        simp only [PhiRA, LRA]
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
    have hLd := rhyp_LRA E (p := p) hD0 hdR
    set M := 2 * (CQ + CN) + CL * D
    have hCLD : 0 ≤ CL * D := by positivity
    have hCC : 0 ≤ 2 * (CQ + CN) := by positivity
    have hM1 : 2 * (CQ + CN) ≤ M := by linarith
    have hM2 : CL * D ≤ M := by linarith
    have hresA : AdA E (fun s ω => PhiRA E p e d z s ω - PhiRA E p e d z' s ω -
        LRA E p dd s ω) := fun t => (adA_of_rhyp E hPd t).sub (adA_of_rhyp E hLd t)
    have hresR := rhyp_of E hresA hrem
    have hb := hLinvB _ _ (by positivity) hresR
    intro t
    filter_upwards [LinvRA_sub E hp hG (by positivity) hPz hPz' t,
      LinvRA_sub E hp hG (by positivity) (rhyp_mono E hPd hM1) (rhyp_mono E hLd hM2) t,
      LinvRA_LRA E hp hG hD0 hdR t, hb t] with ω h1 h2 h3 h4
    have key : T z t ω - T z' t ω = -LinvRA E p (fun s ω => PhiRA E p e d z s ω -
        PhiRA E p e d z' s ω - LRA E p dd s ω) t ω := by
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
  have h0A : AdA E (fun _ _ => (0 : Fin 5 → ℝ)) := fun _ => aestronglyMeasurable_const
  have h0B : Bd E (fun _ _ => (0 : Fin 5 → ℝ)) r := fun _ =>
    Eventually.of_forall fun _ => by simp [hr0.le]
  -- `T 0` is small
  have hT0 : Bd E (T fun _ _ => 0) (r / 2) := by
    have hb : Bd E (PhiRA E p e d fun _ _ => 0) τ := fun t => by
      have hss := Qd_Nd_zero hp
      filter_upwards [heb t, hlagB _ h0B t, hdb] with ω h1 h2 h3
      have e1 : PhiRA E p e d (fun _ _ => 0) t ω =
          Qd p (e t ω, lagIA (fun _ _ => 0) d t ω, 0) - Qd p 0 := by
        simp only [PhiRA, MvA_const]
        rw [eq_neg_of_add_eq_zero_right hss]
        abel
      rw [e1, ← dist_eq_norm]
      refine (hQc ?_).le
      rw [dist_zero_right, Prod.norm_def, Prod.norm_def]
      have hl : ‖lagIA (fun _ _ => (0 : Fin 5 → ℝ)) d t ω‖ ≤ δQ / 2 := by
        cases t with
        | zero => exact h3.trans (min_le_right _ _)
        | succ t => simp only [lagIA, norm_zero]; positivity
      have h0 : ‖(0 : Fin 5 → ℝ)‖ ≤ δQ / 2 := by rw [norm_zero]; positivity
      exact lt_of_le_of_lt (max_le (h1.trans (min_le_right _ _)) (max_le hl h0)) (by linarith)
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
  set zs : ℕ → ℕ → Ω → Fin 5 → ℝ := fun n => T^[n] fun _ _ => 0 with hzs
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
  set z : ℕ → Ω → Fin 5 → ℝ := fun t ω => limUnder atTop fun n => zs n t ω with hz
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
      ((∀ t, T w t =ᵐ[E.μ] w t) ↔ ∀ t, PhiRA E p e d w t =ᵐ[E.μ] 0) := by
    intro w hw hwb
    have hP := hPhiR w hw hwb
    have hLL := LRA_LinvRA E hp hG _ _ (by positivity) hP
    constructor
    · intro h t
      have hl0 : ∀ s, LinvRA E p (PhiRA E p e d w) s =ᵐ[E.μ] 0 := fun s => by
        filter_upwards [h s] with ω hω
        have := congrArg (fun v => w s ω - v) hω
        simp only [hT, sub_sub_cancel, sub_self] at this
        exact this
      filter_upwards [hLL t, LRA_ae_zero E (p := p) hl0 t] with ω h1 h2
      rw [← h1, h2]
    · intro h t
      have hz0 := LRA_inj E hp hG (LinvRA E p (PhiRA E p e d w)) _
        (by positivity) (hKr E _ _ (by positivity) hP) (fun s => by
          filter_upwards [hLL s, h s] with ω h1 h2
          rw [h1, h2]) t
      filter_upwards [hz0] with ω hω
      simp only [hT, hω, Pi.zero_apply, sub_zero]
  refine ⟨z, ⟨hzA, hzB, (hsol z hzA hzB).1 hfix⟩, fun z' hz'A hz'B hz' => ?_⟩
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

end Woodford.StabilizationWelfare.NonlinearRotembergRamseyAEIFT
