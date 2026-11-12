/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearNKMarkovRamseyTree

/-!
# Existence and uniqueness of the timeless Ramsey equilibrium near the steady state

Woodford (2003), *Interest and Prices*, Chapter 7, §1–2 (optimal policy from a timeless
perspective, the predetermined `Δ_{−1}, λ_{−1}`), Chapter 6, §5 (Benigno–Woodford) and
Appendix A.3 (the implicit function theorem in sequence space).

On an event tree (`NonlinearNKMarkovRamseyTree.LagTree`) the exact Ramsey conditions in
deviations `z = w − w̄` from the zero-inflation steady state, with disturbances `e` and initial
lag `d` (the predetermined `Δ_{−1}, λ₁_{−1}, λ₂_{−1}` enter through it) are
`Q(e, lag z, z) + M N(z) = 0` (`PhiR`, `lagI`).

* `remainder_gen`: a uniform first-order remainder for `C¹` maps of `(parameter, unknown)`.
* `Mv_DNr`: the expectation commutes with the linearised lead.
* **`ramsey_existence`**: there are `r, δ > 0`, depending only on the parameters, such that on
  EVERY event tree, for all disturbances and initial lags with `‖e‖, ‖d‖ ≤ δ`, the exact Ramsey
  conditions have a solution with `‖z‖ ≤ r`, and it is the only one with `‖z‖ ≤ r` (the
  Newton–Picard contraction `z ↦ z − L⁻¹Φ(z)` with the inverse of `LinvR`).
-/

namespace Woodford.StabilizationWelfare.NonlinearNKMarkovRamseyIFT

open Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovGeneral NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyLin
open NonlinearNKMarkovRamseyTree

/-- Woodford (2003), App. A.3 (**a uniform first-order remainder**): for a `C¹` map `g(e, u)` and
`η > 0` there is `ρ > 0` with `‖g(e,u) − g(e,u′) − Dg(0,0)(0, u − u′)‖ ≤ η‖u − u′‖` whenever
`‖e‖, ‖u‖, ‖u′‖ ≤ ρ`. -/
theorem remainder_gen {E U F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E × U → F} (hg : ContDiff ℝ 1 g) {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, ∀ e u u', ‖e‖ ≤ ρ → ‖u‖ ≤ ρ → ‖u'‖ ≤ ρ →
      ‖g (e, u) - g (e, u') - fderiv ℝ g (0, 0) (0, u - u')‖ ≤ η * ‖u - u'‖ := by
  have hc : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  obtain ⟨ρ', hρ', hball⟩ := Metric.continuousAt_iff.1 hc.continuousAt η hη
  refine ⟨ρ' / 2, by positivity, fun e w w' he hw hw' => ?_⟩
  set A := fderiv ℝ g (0, 0) with hA
  set I := ContinuousLinearMap.inr ℝ E U
  set B := Metric.closedBall (0 : U) (ρ' / 2)
  have hdiff : ∀ u ∈ B, HasFDerivWithinAt (fun u => g (e, u) - A (0, u))
      ((fderiv ℝ g (e, u) - A).comp I) B u := fun u _ => by
    have h1 : HasFDerivAt (fun u => g (e, u)) ((fderiv ℝ g (e, u)).comp I) u :=
      ((hg.differentiable one_ne_zero) (e, u)).hasFDerivAt.comp u (hasFDerivAt_prodMk_right e u)
    have h2 : HasFDerivAt (fun u => A (0, u)) (A.comp I) u := (A.comp I).hasFDerivAt
    have := h1.sub h2
    rw [← ContinuousLinearMap.sub_comp] at this
    exact this.hasFDerivWithinAt
  have hbound : ∀ u ∈ B, ‖(fderiv ℝ g (e, u) - A).comp I‖ ≤ η := fun u hu => by
    have hd : dist (e, u) (0, 0) < ρ' := by
      have hu' : ‖u‖ ≤ ρ' / 2 := by simpa [B] using hu
      change dist (e, u) 0 < ρ'
      rw [dist_zero_right, Prod.norm_def]
      exact lt_of_le_of_lt (max_le he hu') (by linarith)
    have h := hball hd
    rw [dist_eq_norm] at h
    calc ‖(fderiv ℝ g (e, u) - A).comp I‖ ≤ ‖fderiv ℝ g (e, u) - A‖ * ‖I‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ η * 1 := mul_le_mul h.le (ContinuousLinearMap.norm_inr_le_one ℝ _ _) (norm_nonneg _)
          hη.le
      _ = η := mul_one η
  have hwB : w ∈ B := by simpa [B] using hw
  have hw'B : w' ∈ B := by simpa [B] using hw'
  have := (convex_closedBall (0 : U) (ρ' / 2)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hdiff hbound hw'B hwB
  have e1 : g (e, w) - A (0, w) - (g (e, w') - A (0, w')) =
      g (e, w) - g (e, w') - A (0, w - w') := by
    have : ((0 : E), w - w') = ((0 : E), w) - (0, w') := by simp
    rw [this, map_sub]; abel
  rw [e1] at this
  exact this

/-- Woodford (2003), §5: the linearised lead as a linear map. -/
noncomputable def DNlin (p : Par) (R : RPar) : (Fin 9 → ℝ) →ₗ[ℝ] (Fin 9 → ℝ) where
  toFun n := DNr p R n
  map_add' n n' := by funext i; fin_cases i <;> simp [DNr] <;> ring
  map_smul' c n := by funext i; fin_cases i <;> simp [DNr] <;> ring

variable {X : Type*} (T : LagTree X)

/-- Woodford (2003), App. A.3: the expectation commutes with the linearised lead. -/
theorem Mv_DNr (p : Par) (R : RPar) (w : X → Fin 9 → ℝ) (x : X) :
    Mv T.M (fun y => DNr p R (w y)) x = DNr p R (Mv T.M w x) := by
  have e : ∀ n, DNr p R n = (LinearMap.toMatrix' (DNlin p R)).mulVec n := fun n => by
    rw [LinearMap.toMatrix'_mulVec]; rfl
  simp only [e]
  exact congrFun (Mv_mulVec T.M _ w) x

/-- `Mv` of a constant vector. -/
theorem Mv_const' {n : ℕ} (c : Fin n → ℝ) (x : X) : Mv T.M (fun _ => c) x = c :=
  Mv_const T.markov c x

/-- Woodford (2003), Ch. 7: the lag with the initial (predetermined) value `d` at the roots. -/
def lagI {n : ℕ} (z d : X → Fin n → ℝ) (x : X) : Fin n → ℝ :=
  if T.depth x = 0 then d x else z (T.par x)

/-- Woodford (2003), §5 and Ch. 7 (**the exact Ramsey conditions on an event tree**), in
deviations `z = w − w̄`, with disturbances `e` and initial lag `d`:
`Φ(z)(x) = Q(e(x), lag z(x), z(x)) + E_x N(z)`. -/
noncomputable def PhiR (p : Par) (R : RPar) (e : X → Fin 5 → ℝ) (d z : X → Fin 9 → ℝ) (x : X) :
    Fin 9 → ℝ :=
  Qd p R (e x, lagI T z d x, z x) + Mv T.M (fun y => Nd p R (z y)) x

/-- The linearised operator vanishes at zero. -/
theorem LR_zero (p : Par) (R : RPar) (x : X) : LR T p R (fun _ => 0) x = 0 := by
  have := LR_sub T p R (fun _ => (0 : Fin 9 → ℝ)) (fun _ => 0) x
  simp only [sub_self] at this
  exact this

/-- The lag of a difference is the difference of the lags with a common initial value. -/
theorem lagv_sub_lagI (z z' d : X → Fin 9 → ℝ) (x : X) :
    lagv T (fun y => z y - z' y) x = lagI T z d x - lagI T z' d x := by
  funext i
  simp only [lagv, lag0, lagI, Pi.sub_apply]
  split_ifs <;> simp

/-- Woodford (2003), App. A.3: the derivative of the lead part composed with the projection. -/
theorem fderiv_Nd_snd {p : Par} (R : RPar) (w : Fin 9 → ℝ) :
    fderiv ℝ (fun q : (Fin 5 → ℝ) × (Fin 9 → ℝ) => Nd p R q.2) (0, 0) (0, w) = DNr p R w := by
  have hNd : HasFDerivAt (Nd p R) (fderiv ℝ (Nd p R) 0) ((0 : Fin 5 → ℝ), (0 : Fin 9 → ℝ)).2 :=
    ((contDiff_Nd (n := 1) p R).differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hs : HasFDerivAt (fun q : (Fin 5 → ℝ) × (Fin 9 → ℝ) => q.2)
      (ContinuousLinearMap.snd ℝ (Fin 5 → ℝ) (Fin 9 → ℝ)) (0, 0) := hasFDerivAt_snd
  have h := (hNd.comp ((0 : Fin 5 → ℝ), (0 : Fin 9 → ℝ)) hs).fderiv
  change fderiv ℝ (Nd p R ∘ Prod.snd) (0, 0) (0, w) = DNr p R w
  rw [h]
  simpa using fderiv_Nd R w

/-- Woodford (2003), Ch. 7 and App. A.3 (**EXISTENCE AND UNIQUENESS of the timeless Ramsey
equilibrium near the steady state, on every event tree**): if `A_uG ≠ 0`, there are `r, δ > 0`,
depending only on the parameters, such that on every event tree, for all disturbances `e` and
predetermined initial lags `d` with `‖e‖, ‖d‖ ≤ δ`, the exact Ramsey conditions `Φ(z) = 0` have
a solution with `‖z‖ ≤ r`, and every solution with `‖z′‖ ≤ r` equals it. -/
theorem ramsey_existence {p : Par} (R : RPar) (hp : p.Std) (hG : R.Au * Gw p R ≠ 0) :
    ∃ r > 0, ∃ δ > 0, ∃ C > 0, ∀ {Y : Type*} (T : LagTree Y) (e : Y → Fin 5 → ℝ)
      (d : Y → Fin 9 → ℝ), (∀ y, ‖e y‖ ≤ δ) → (∀ y, ‖d y‖ ≤ δ) →
        ∃ z : Y → Fin 9 → ℝ, ((∀ y, ‖z y‖ ≤ r) ∧ PhiR T p R e d z = 0) ∧
          (∀ z' : Y → Fin 9 → ℝ, (∀ y, ‖z' y‖ ≤ r) → PhiR T p R e d z' = 0 → z' = z) ∧
          ∀ τ', 0 ≤ τ' → (∀ y, ‖PhiR T p R e d (fun _ => 0) y‖ ≤ τ') → ∀ y, ‖z y‖ ≤ C * τ' := by
  obtain ⟨K, hK0, hK⟩ := LinvR_bound R hp
  set K' := K + 1 with hK'
  have hK'0 : 0 < K' := by linarith
  set η := 1 / (8 * K') with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρQ, hρQ, hQ⟩ := remainder_gen (contDiff_Qd (n := 1) p R) hη0
  obtain ⟨ρN, hρN, hN⟩ := remainder_gen (g := fun q : (Fin 5 → ℝ) × (Fin 9 → ℝ) => Nd p R q.2)
    ((contDiff_Nd (n := 1) p R).comp contDiff_snd) hη0
  set r := min ρQ ρN with hr
  have hr0 : 0 < r := lt_min hρQ hρN
  obtain ⟨CQ, hCQ⟩ := (isCompact_closedBall (0 : (Fin 5 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ))
    r).exists_bound_of_continuousOn ((contDiff_Qd (n := 0) p R).continuous.continuousOn)
  obtain ⟨CN, hCN⟩ := (isCompact_closedBall (0 : Fin 9 → ℝ) r).exists_bound_of_continuousOn
    ((contDiff_Nd (n := 0) p R).continuous.continuousOn)
  have hCQ0 : 0 ≤ CQ := (norm_nonneg _).trans (hCQ 0 (Metric.mem_closedBall_self hr0.le))
  have hCN0 : 0 ≤ CN := (norm_nonneg _).trans (hCN 0 (Metric.mem_closedBall_self hr0.le))
  set τ := r / (2 * K') with hτ
  have hτ0 : 0 < τ := by positivity
  obtain ⟨δQ, hδQ, hQc⟩ := Metric.continuousAt_iff.1
    ((contDiff_Qd (n := 0) p R).continuous.continuousAt (x := 0)) τ hτ0
  refine ⟨r, hr0, min r (δQ / 2), lt_min hr0 (by positivity), 2 * K', by positivity,
    fun {Y} T e d he hd => ?_⟩
  have hKK : ∀ (s : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A →
      (∀ y, ‖s y‖ ≤ A) → ∀ y, ‖LinvR T p R s y‖ ≤ K' * A := fun s A hA hs y =>
    (hK T s A hA hs y).trans (mul_le_mul_of_nonneg_right (by linarith) hA)
  have heR : ∀ y, ‖e y‖ ≤ r := fun y => (he y).trans (min_le_left _ _)
  have hdR : ∀ y, ‖d y‖ ≤ r := fun y => (hd y).trans (min_le_left _ _)
  have hlag : ∀ z : Y → Fin 9 → ℝ, (∀ y, ‖z y‖ ≤ r) → ∀ x, ‖lagI T z d x‖ ≤ r := fun z hz x => by
    unfold lagI; split_ifs
    · exact hdR x
    · exact hz _
  have hin : ∀ z : Y → Fin 9 → ℝ, (∀ y, ‖z y‖ ≤ r) → ∀ x,
      (e x, lagI T z d x, z x) ∈ Metric.closedBall (0 : (Fin 5 → ℝ) × (Fin 9 → ℝ) ×
        (Fin 9 → ℝ)) r := fun z hz x => by
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Prod.norm_def]
    exact max_le (heR x) (max_le (hlag z hz x) (hz x))
  have hPhiB : ∀ z : Y → Fin 9 → ℝ, (∀ y, ‖z y‖ ≤ r) → ∀ x, ‖PhiR T p R e d z x‖ ≤ CQ + CN :=
    fun z hz x => (norm_add_le _ _).trans (add_le_add (hCQ _ (hin z hz x))
      (Mv_norm_le T.markov hCN0 (fun y => hCN _ (by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hz y)) x))
  -- the Newton map
  set Tm : (Y → Fin 9 → ℝ) → (Y → Fin 9 → ℝ) :=
    fun Z x => Z x - LinvR T p R (PhiR T p R e d Z) x with hTm
  have hcontr : ∀ z z' : Y → Fin 9 → ℝ, (∀ y, ‖z y‖ ≤ r) → (∀ y, ‖z' y‖ ≤ r) → ∀ D,
      (∀ y, ‖z y - z' y‖ ≤ D) → ∀ x, ‖Tm z x - Tm z' x‖ ≤ D / 2 := by
    intro z z' hz hz' D hD x
    have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD x)
    set CL := ‖LinearMap.toContinuousLinearMap (DLin p R)‖
    have hLz : ∀ y, ‖LR T p R (fun y => z y - z' y) y‖ ≤ CL * D :=
      norm_LR_le T p R hD0 hD
    have hdPhi : ∀ y, ‖PhiR T p R e d z y - PhiR T p R e d z' y‖ ≤ (CQ + CN) + (CQ + CN) :=
      fun y => (norm_sub_le _ _).trans (add_le_add (hPhiB z hz y) (hPhiB z' hz' y))
    -- the remainder
    have hrem : ∀ y, ‖(PhiR T p R e d z y - PhiR T p R e d z' y) -
        LR T p R (fun y => z y - z' y) y‖ ≤ η * D + η * D := by
      intro y
      have hl := lagv_sub_lagI T z z' d y
      have hu1 : ‖(lagI T z d y, z y)‖ ≤ ρQ := by
        rw [Prod.norm_def]
        exact max_le ((hlag z hz y).trans (min_le_left _ _)) ((hz y).trans (min_le_left _ _))
      have hu2 : ‖(lagI T z' d y, z' y)‖ ≤ ρQ := by
        rw [Prod.norm_def]
        exact max_le ((hlag z' hz' y).trans (min_le_left _ _)) ((hz' y).trans (min_le_left _ _))
      have hq := hQ (e y) (lagI T z d y, z y) (lagI T z' d y, z' y)
        ((heR y).trans (min_le_left _ _)) hu1 hu2
      rw [Prod.mk_sub_mk, show fderiv ℝ (Qd p R) ((0 : Fin 5 → ℝ),
        (0 : (Fin 9 → ℝ) × (Fin 9 → ℝ))) = fderiv ℝ (Qd p R) 0 from rfl, fderiv_Qd R hp] at hq
      have hqD : ‖(lagI T z d y, z y) - (lagI T z' d y, z' y)‖ ≤ D := by
        rw [Prod.mk_sub_mk, Prod.norm_def, ← hl]
        exact max_le (norm_lagv_le T hD0 hD y) (hD y)
      have hnB : ∀ y', ‖Nd p R (z y') - Nd p R (z' y') - DNr p R (z y' - z' y')‖ ≤ η * D :=
        fun y' => by
          have h := hN 0 (z y') (z' y') (by rw [norm_zero]; exact hρN.le)
            ((hz y').trans (min_le_right _ _))
            ((hz' y').trans (min_le_right _ _))
          rw [fderiv_Nd_snd R] at h
          exact h.trans (mul_le_mul_of_nonneg_left (hD y') hη0.le)
      have hMv := Mv_norm_le T.markov (by positivity) hnB y
      have e1 : Mv T.M (fun y' => Nd p R (z y') - Nd p R (z' y') - DNr p R (z y' - z' y')) y =
          Mv T.M (fun y' => Nd p R (z y')) y - Mv T.M (fun y' => Nd p R (z' y')) y -
            DNr p R (Mv T.M (fun y' => z y' - z' y') y) := by
        rw [NonlinearNKMarkovLinks.Mv_sub, NonlinearNKMarkovLinks.Mv_sub]
        simp only
        rw [Mv_DNr]
      rw [e1] at hMv
      have e2 : (PhiR T p R e d z y - PhiR T p R e d z' y) - LR T p R (fun y => z y - z' y) y =
          (Qd p R (e y, lagI T z d y, z y) - Qd p R (e y, lagI T z' d y, z' y) -
            DQr p R (lagI T z d y - lagI T z' d y) (z y - z' y)) +
          (Mv T.M (fun y' => Nd p R (z y')) y - Mv T.M (fun y' => Nd p R (z' y')) y -
            DNr p R (Mv T.M (fun y' => z y' - z' y') y)) := by
        simp only [PhiR, LR, hl]
        abel
      rw [e2]
      exact (norm_add_le _ _).trans (add_le_add (hq.trans
        (mul_le_mul_of_nonneg_left hqD hη0.le)) hMv)
    have hs1 := LinvR_sub T R hp hG (r := PhiR T p R e d z) (r' := PhiR T p R e d z')
      (A := CQ + CN) (A' := CQ + CN) (by positivity)
      (by positivity) (hPhiB z hz) (hPhiB z' hz')
    have hs2 := LinvR_sub T R hp hG (A := (CQ + CN) + (CQ + CN)) (A' := CL * D)
      (by positivity) (by positivity) hdPhi hLz
    have hLL := LinvR_LR T R hp hG hD0 hD
    have key : Tm z x - Tm z' x = -LinvR T p R (fun y => (PhiR T p R e d z y -
        PhiR T p R e d z' y) - LR T p R (fun y => z y - z' y) y) x := by
      rw [hs2]
      simp only [hTm]
      rw [hs1, hLL]
      funext i
      simp only [Pi.sub_apply, Pi.neg_apply]
      ring
    rw [key, norm_neg]
    calc _ ≤ K' * (η * D + η * D) := hKK _ _ (by positivity) hrem x
      _ = D / 4 := by rw [hη]; field_simp; ring
      _ ≤ D / 2 := by linarith
  -- `T 0` is small
  have hT0 : ∀ x, ‖Tm (fun _ => 0) x‖ ≤ r / 2 := by
    intro x
    have hb : ∀ y, ‖PhiR T p R e d (fun _ => 0) y‖ ≤ τ := fun y => by
      have hss := Qd_Nd_zero R hp
      have e1 : PhiR T p R e d (fun _ => 0) y =
          Qd p R (e y, lagI T (fun _ => 0) d y, 0) - Qd p R 0 := by
        simp only [PhiR, Mv_const']
        rw [eq_neg_of_add_eq_zero_right hss]
        abel
      rw [e1, ← dist_eq_norm]
      refine (hQc ?_).le
      rw [dist_zero_right, Prod.norm_def, Prod.norm_def]
      have hl : ‖lagI T (fun _ => (0 : Fin 9 → ℝ)) d y‖ ≤ δQ / 2 := by
        unfold lagI; split_ifs
        · exact (hd y).trans (min_le_right _ _)
        · rw [norm_zero]; positivity
      have h0 : ‖(0 : Fin 9 → ℝ)‖ ≤ δQ / 2 := by rw [norm_zero]; positivity
      exact lt_of_le_of_lt (max_le ((he y).trans (min_le_right _ _)) (max_le hl h0))
        (by linarith)
    have h := hKK _ τ hτ0.le hb x
    simp only [hTm, zero_sub, norm_neg]
    calc _ ≤ K' * τ := h
      _ = r / 2 := by rw [hτ]; field_simp
  have hball : ∀ z : Y → Fin 9 → ℝ, (∀ y, ‖z y‖ ≤ r) → ∀ x, ‖Tm z x‖ ≤ r := by
    intro z hz x
    have h1 := hcontr z (fun _ => 0) hz (fun y => by simp [hr0.le]) r
      (fun y => by simpa using hz y) x
    calc ‖Tm z x‖ ≤ ‖Tm z x - Tm (fun _ => 0) x‖ + ‖Tm (fun _ => 0) x‖ := by
          have := norm_add_le (Tm z x - Tm (fun _ => 0) x) (Tm (fun _ => 0) x); simpa using this
      _ ≤ r / 2 + r / 2 := add_le_add h1 (hT0 x)
      _ = r := by ring
  -- Picard iteration
  set zs : ℕ → Y → Fin 9 → ℝ := fun n => Tm^[n] (fun _ => 0) with hzs
  have hzsB : ∀ n x, ‖zs n x‖ ≤ r := by
    intro n
    induction n with
    | zero => intro x; simp [hzs, hr0.le]
    | succ n ih =>
      intro x
      simp only [hzs, Function.iterate_succ_apply']
      exact hball _ ih x
  have hstep : ∀ n x, ‖zs n x - zs (n + 1) x‖ ≤ r / 2 / 2 ^ n := by
    intro n
    induction n with
    | zero =>
      intro x
      simp only [hzs, Function.iterate_zero, id, pow_zero, div_one]
      rw [norm_sub_rev]; simpa using hT0 x
    | succ n ih =>
      intro x
      have h := hcontr (zs (n + 1)) (zs n) (hzsB _) (hzsB _) (r / 2 / 2 ^ n)
        (fun x => by rw [norm_sub_rev]; exact ih x) x
      have e1 : zs (n + 1 + 1) = Tm (zs (n + 1)) := by
        simp only [hzs, Function.iterate_succ_apply']
      have e2 : zs (n + 1) = Tm (zs n) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e1, norm_sub_rev]
      conv_lhs => rw [show zs (n + 1) x = Tm (zs n) x from congrFun e2 x]
      calc _ ≤ r / 2 / 2 ^ n / 2 := h
        _ = r / 2 / 2 ^ (n + 1) := by rw [pow_succ]; ring
  have hcau : ∀ x, CauchySeq fun n => zs n x := fun x =>
    cauchySeq_of_le_geometric_two (C := r) fun n => by rw [dist_eq_norm]; exact hstep n x
  choose z hz using fun x => cauchySeq_tendsto_of_complete (hcau x)
  have hzdist : ∀ n x, ‖zs n x - z x‖ ≤ r / 2 ^ n := fun n x => by
    have := dist_le_of_le_geometric_two_of_tendsto (C := r) (f := fun n => zs n x)
      (fun n => by rw [dist_eq_norm]; exact hstep n x) (hz x) n
    rwa [dist_eq_norm] at this
  have hzB : ∀ x, ‖z x‖ ≤ r := fun x => le_of_tendsto' ((hz x).norm) fun n => hzsB n x
  have hfix : Tm z = z := by
    funext x
    have hlim : Tendsto (fun n => zs (n + 1) x) atTop (𝓝 (Tm z x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hg : Tendsto (fun n : ℕ => r / 2 ^ n / 2) atTop (𝓝 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (r / 2)
        simp only [mul_zero] at this
        refine this.congr fun n => ?_
        rw [one_div, inv_pow]; field_simp
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hg
      have e : zs (n + 1) = Tm (zs n) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e, norm_sub_rev]
      exact hcontr z (zs n) hzB (hzsB n) (r / 2 ^ n) (fun x => by
        rw [norm_sub_rev]; exact hzdist n x) x
    exact tendsto_nhds_unique hlim ((hz x).comp (tendsto_add_atTop_nat 1))
  -- fixed points of `Tm` in the ball are exactly the solutions
  have hsol : ∀ w : Y → Fin 9 → ℝ, (∀ y, ‖w y‖ ≤ r) →
      (Tm w = w ↔ PhiR T p R e d w = 0) := by
    intro w hw
    have hr' : ∀ y k, |PhiR T p R e d w y k| ≤ CQ + CN := fun y k => by
      have := (norm_le_pi_norm _ k).trans (hPhiB w hw y); rwa [Real.norm_eq_abs] at this
    have hRL := LR_LinvR T R hp hG (PhiR T p R e d w) (CQ + CN) (by positivity) hr'
    constructor
    · intro h
      have hl : LinvR T p R (PhiR T p R e d w) = fun _ => 0 := by
        funext x
        have := congrFun h x
        simp only [hTm] at this
        have := congrArg (fun v => w x - v) this
        simp only [sub_sub_cancel, sub_self] at this
        exact this
      rw [← hRL, hl]
      funext x; exact LR_zero T p R x
    · intro h
      have h0 : LinvR T p R (PhiR T p R e d w) = fun _ => 0 := by
        rw [h]
        have := LinvR_LR T R hp hG (v := fun _ => (0 : Fin 9 → ℝ)) le_rfl (fun _ => by simp)
        have e : LR T p R (fun _ => (0 : Fin 9 → ℝ)) = 0 := funext fun x => LR_zero T p R x
        rw [e] at this
        exact this
      funext x
      simp only [hTm, h0, sub_zero]
  have hsmall : ∀ τ', 0 ≤ τ' → (∀ y, ‖PhiR T p R e d (fun _ => 0) y‖ ≤ τ') →
      ∀ y, ‖z y‖ ≤ 2 * K' * τ' := by
    intro τ' hτ' hb
    have hT0' : ∀ x, ‖Tm (fun _ => 0) x‖ ≤ K' * τ' := fun x => by
      have h := hKK _ τ' hτ' hb x
      simp only [hTm, zero_sub, norm_neg]
      exact h
    have hn : ∀ n : ℕ, ∀ y, ‖z y‖ ≤ r / 2 ^ n + 2 * K' * τ' := by
      intro n
      induction n with
      | zero => intro y; have := hzB y; have : 0 ≤ 2 * K' * τ' := by positivity
                simp only [pow_zero, div_one]; linarith
      | succ n ih =>
        intro y
        have h := hcontr z (fun _ => 0) hzB (fun y => by simp [hr0.le]) _
          (fun y => by simpa using ih y) y
        rw [hfix] at h
        calc ‖z y‖ ≤ ‖z y - Tm (fun _ => 0) y‖ + ‖Tm (fun _ => 0) y‖ := by
              have := norm_add_le (z y - Tm (fun _ => 0) y) (Tm (fun _ => 0) y); simpa using this
          _ ≤ (r / 2 ^ n + 2 * K' * τ') / 2 + K' * τ' := add_le_add h (hT0' y)
          _ = r / 2 ^ (n + 1) + 2 * K' * τ' := by rw [pow_succ]; ring
    intro y
    have ht : Tendsto (fun n : ℕ => r / 2 ^ n + 2 * K' * τ') atTop (𝓝 (0 + 2 * K' * τ')) := by
      refine Tendsto.add ?_ tendsto_const_nhds
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul r
      simp only [mul_zero] at this
      refine this.congr fun n => ?_
      rw [one_div, inv_pow]; field_simp
    have := ge_of_tendsto' ht fun n => hn n y
    simpa using this
  refine ⟨z, ⟨hzB, (hsol z hzB).1 hfix⟩, fun z' hz'B hz' => ?_, hsmall⟩
  have hfix' := (hsol z' hz'B).2 hz'
  have hD : ∀ n : ℕ, ∀ x, ‖z' x - z x‖ ≤ 2 * r / 2 ^ n := by
    intro n
    induction n with
    | zero =>
      intro x
      have := (norm_sub_le (z' x) (z x)).trans (add_le_add (hz'B x) (hzB x))
      simp only [pow_zero, div_one]; linarith
    | succ n ih =>
      intro x
      have h := hcontr z' z hz'B hzB _ ih x
      rw [hfix, hfix'] at h
      exact h.trans (le_of_eq (by rw [pow_succ]; ring))
  funext x
  have ht : Tendsto (fun n : ℕ => 2 * r / 2 ^ n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (2 * r)
    simp only [mul_zero] at this
    refine this.congr fun n => ?_
    rw [one_div, inv_pow]; field_simp
  have := ge_of_tendsto' ht fun n => hD n x
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

end Woodford.StabilizationWelfare.NonlinearNKMarkovRamseyIFT
