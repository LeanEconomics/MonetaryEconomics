/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearNKMarkovRamseyIFT
import StabilizationWelfare.NonlinearNKMarkovLinks

/-!
# The Newton contraction with a lag on an event tree, for abstract conditions

Woodford (2003), *Interest and Prices*, Chapter 7, §1–2 (the timeless Ramsey problem with
predetermined `Δ_{−1}, λ_{−1}`), Chapter 6, §5, and Appendix A.3 (the sequence-space implicit
function theorem).

`NonlinearNKMarkovRamseyIFT.ramsey_existence` proves existence and local uniqueness for the exact
Calvo Ramsey conditions. Its proof uses the conditions `Q(e, w₋, w) + E N(w′) = 0` only through
`C¹` smoothness, the steady state `Q(0) + N(0) = 0`, and an inverse of the linearised operator
`L v = DQ(0)(0, lag v, v) + DN(0)(M v)` with three properties (a uniform bound, a right inverse on
bounded forcings, injectivity on bounded processes). Here the theorem is proved for ANY `C¹`
conditions in `ℝⁿ` with any disturbance space `ℝᵏ`, so that the Ramsey problem with government
purchases (`TidyR6bGovRamseyTree`) and other variants are instances.

* `LG`, `PhiG`: the linearised operator and the exact conditions on an event tree.
* `LG_sub`, `LG_zero`, `norm_LG_le`, `Mv_clm`: linearity, boundedness, and the commutation of the
  expectation with a linear map.
* `Li_LG`, `Li_sub`: the left inverse and subtractivity from the three properties.
* **`newton_tree`**: existence, local uniqueness and the bound `‖z‖ ≤ C‖Φ(0)‖` on every event
  tree, uniformly; the solution lies in every class containing `0`, invariant under the Newton
  map on the ball and closed under pointwise limits (used for measurability).
-/

namespace Woodford.StabilizationWelfare.TidyR6bRamseyNewton

universe u

open Filter Topology
open NonlinearNKMarkov (Mv IsMarkov Mv_norm_le Mv_mulVec)
open NonlinearNKMarkovGeneral (Mv_const)
open NonlinearNKMarkovRamseyTree (LagTree lag0 lagv norm_lagv_le lag0_lin)
open NonlinearNKMarkovRamseyIFT (remainder_gen lagI)

variable {k n : ℕ}

/-- Woodford (2003), Ch. 7 and App. A.3 (**the linearised operator of abstract conditions**):
`(Lv)(x) = DQ(0)(0, v(par x), v(x)) + DN(0)((Mv)(x))`, zero lag at the roots. -/
noncomputable def LG {X : Type*} (T : LagTree X)
    (Q : (Fin k → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ) (N : (Fin n → ℝ) → Fin n → ℝ)
    (v : X → Fin n → ℝ) (x : X) : Fin n → ℝ :=
  fderiv ℝ Q 0 (0, lagv T v x, v x) + fderiv ℝ N 0 (Mv T.M v x)

/-- Woodford (2003), Ch. 7 (**the exact conditions on an event tree**) with disturbances `e` and
initial lag `d`: `Φ(z)(x) = Q(e(x), lag z(x), z(x)) + E_x N(z)`. -/
noncomputable def PhiG {X : Type*} (T : LagTree X)
    (Q : (Fin k → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ) (N : (Fin n → ℝ) → Fin n → ℝ)
    (e : X → Fin k → ℝ) (d z : X → Fin n → ℝ) (x : X) : Fin n → ℝ :=
  Q (e x, lagI T z d x, z x) + Mv T.M (fun y => N (z y)) x

variable {X : Type*} (T : LagTree X)

/-- Woodford (2003), App. A.3: the expectation commutes with a linear map. -/
theorem Mv_clm (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (w : X → Fin n → ℝ) (x : X) :
    Mv T.M (fun y => A (w y)) x = A (Mv T.M w x) := by
  have e : ∀ v, A v = (LinearMap.toMatrix' A.toLinearMap).mulVec v := fun v => by
    rw [LinearMap.toMatrix'_mulVec]; rfl
  simp only [e]
  exact congrFun (Mv_mulVec T.M _ w) x

/-- Woodford (2003), Ch. 7 and App. A.3: the lag of a difference is the difference of the lags
with a common initial value. -/
theorem lagv_sub_lagI' (z z' d : X → Fin n → ℝ) (x : X) :
    lagv T (fun y => z y - z' y) x = lagI T z d x - lagI T z' d x := by
  funext i
  simp only [lagv, lag0, lagI, Pi.sub_apply]
  split_ifs <;> simp

/-- Woodford (2003), Ch. 7 and App. A.3: the lag of a difference. -/
theorem lagv_sub (v w : X → Fin n → ℝ) (x : X) :
    lagv T (fun y => v y - w y) x = lagv T v x - lagv T w x := by
  funext i
  simp only [lagv, lag0, Pi.sub_apply]
  split_ifs <;> simp

/-- Woodford (2003), App. A.3: the linearised operator is subtractive. -/
theorem LG_sub (Q : (Fin k → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ)
    (N : (Fin n → ℝ) → Fin n → ℝ) (v w : X → Fin n → ℝ) (x : X) :
    LG T Q N (fun y => v y - w y) x = LG T Q N v x - LG T Q N w x := by
  have hm := congrFun (NonlinearNKMarkovLinks.Mv_sub T.M v w) x
  simp only [LG, lagv_sub, hm]
  have e : ((0 : Fin k → ℝ), lagv T v x - lagv T w x, v x - w x) =
      ((0 : Fin k → ℝ), lagv T v x, v x) - (0, lagv T w x, w x) := by simp
  rw [e, map_sub, map_sub]
  abel

/-- Woodford (2003), Ch. 7 and App. A.3: the linearised operator vanishes at zero. -/
theorem LG_zero (Q : (Fin k → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ)
    (N : (Fin n → ℝ) → Fin n → ℝ) (x : X) : LG T Q N (fun _ => 0) x = 0 := by
  have := LG_sub T Q N (fun _ => (0 : Fin n → ℝ)) (fun _ => 0) x
  simp only [sub_self] at this
  exact this

/-- Woodford (2003), App. A.3: the linearised operator is bounded. -/
theorem norm_LG_le (Q : (Fin k → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ)
    (N : (Fin n → ℝ) → Fin n → ℝ) {v : X → Fin n → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, ‖v x‖ ≤ B) (x : X) :
    ‖LG T Q N v x‖ ≤ (‖fderiv ℝ Q 0‖ + ‖fderiv ℝ N 0‖) * B := by
  have h1 : ‖((0 : Fin k → ℝ), lagv T v x, v x)‖ ≤ B := by
    simp only [Prod.norm_def, norm_zero]
    exact max_le hB0 (max_le (norm_lagv_le T hB0 hB x) (hB x))
  have h2 : ‖Mv T.M v x‖ ≤ B := Mv_norm_le T.markov hB0 hB x
  calc ‖LG T Q N v x‖ ≤ ‖fderiv ℝ Q 0‖ * B + ‖fderiv ℝ N 0‖ * B :=
        (norm_add_le _ _).trans (add_le_add
          (((fderiv ℝ Q 0).le_opNorm _).trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)))
          (((fderiv ℝ N 0).le_opNorm _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))))
    _ = _ := by ring

/-- Woodford (2003), App. A.3: the bound hypothesis on an inverse family. -/
def InvBound (Q : (Fin k → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ)
    (N : (Fin n → ℝ) → Fin n → ℝ)
    (Li : ∀ {Y : Type u}, LagTree Y → (Y → Fin n → ℝ) → Y → Fin n → ℝ) : Prop :=
  (∃ K, 0 ≤ K ∧ ∀ {Y : Type u} (T : LagTree Y) (r : Y → Fin n → ℝ) (A : ℝ), 0 ≤ A →
      (∀ y, ‖r y‖ ≤ A) → ∀ y, ‖Li T r y‖ ≤ K * A) ∧
  (∀ {Y : Type u} (T : LagTree Y) (r : Y → Fin n → ℝ) (A : ℝ), 0 ≤ A →
      (∀ y k, |r y k| ≤ A) → LG T Q N (Li T r) = r) ∧
  ∀ {Y : Type u} (T : LagTree Y) (v : Y → Fin n → ℝ) (B : ℝ),
      (∀ x k, |v x k| ≤ B) → LG T Q N v = 0 → v = 0

/-- Woodford (2003), App. A.3 (**the left inverse from the three properties**). -/
theorem Li_LG {Q : (Fin k → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ}
    {N : (Fin n → ℝ) → Fin n → ℝ}
    {Li : ∀ {Y : Type u}, LagTree Y → (Y → Fin n → ℝ) → Y → Fin n → ℝ}
    (hL : InvBound Q N Li) {X : Type u} (T : LagTree X) {v : X → Fin n → ℝ} {B : ℝ}
    (hB0 : 0 ≤ B) (hvB : ∀ x, ‖v x‖ ≤ B) : Li T (LG T Q N v) = v := by
  obtain ⟨⟨K, hK0, hK⟩, hR, hI⟩ := hL
  set CL := ‖fderiv ℝ Q 0‖ + ‖fderiv ℝ N 0‖
  have hLB : ∀ x, ‖LG T Q N v x‖ ≤ CL * B := norm_LG_le T Q N hB0 hvB
  have hLB' : ∀ x k, |LG T Q N v x k| ≤ CL * B := fun x k => by
    have := (norm_le_pi_norm (LG T Q N v x) k).trans (hLB x); rwa [Real.norm_eq_abs] at this
  have hw := hR T (LG T Q N v) (CL * B) (by positivity) hLB'
  have hbd := hK T (LG T Q N v) (CL * B) (by positivity) hLB
  have hz := hI T (fun x => v x - Li T (LG T Q N v) x) (B + K * (CL * B))
    (fun x k => by
      have := (norm_le_pi_norm (v x - Li T (LG T Q N v) x) k).trans
        ((norm_sub_le _ _).trans (add_le_add (hvB x) (hbd x)))
      rwa [Real.norm_eq_abs] at this)
    (by funext x; rw [LG_sub, hw, sub_self]; rfl)
  funext x
  have := congrFun hz x
  simp only [Pi.zero_apply] at this
  exact (sub_eq_zero.1 this).symm

/-- Woodford (2003), App. A.3: the inverse is subtractive on bounded forcings. -/
theorem Li_sub {Q : (Fin k → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ}
    {N : (Fin n → ℝ) → Fin n → ℝ}
    {Li : ∀ {Y : Type u}, LagTree Y → (Y → Fin n → ℝ) → Y → Fin n → ℝ}
    (hL : InvBound Q N Li) {X : Type u} (T : LagTree X) {r r' : X → Fin n → ℝ} {A A' : ℝ}
    (hA : 0 ≤ A) (hA' : 0 ≤ A') (hr : ∀ x, ‖r x‖ ≤ A) (hr' : ∀ x, ‖r' x‖ ≤ A') :
    Li T (fun x => r x - r' x) = fun x => Li T r x - Li T r' x := by
  obtain ⟨⟨K, hK0, hK⟩, hR, hI⟩ := id hL
  have hc : ∀ {s : X → Fin n → ℝ} {S : ℝ}, (∀ x, ‖s x‖ ≤ S) → ∀ x k, |s x k| ≤ S :=
    fun hs x k => by
      have := (norm_le_pi_norm _ k).trans (hs x); rwa [Real.norm_eq_abs] at this
  have hw := hR T r A hA (hc hr)
  have hw' := hR T r' A' hA' (hc hr')
  have hBd : ∀ x, ‖Li T r x - Li T r' x‖ ≤ K * A + K * A' := fun x =>
    (norm_sub_le _ _).trans (add_le_add (hK T r A hA hr x) (hK T r' A' hA' hr' x))
  have e := Li_LG hL T (by positivity) hBd
  rw [← e]
  congr 1
  funext x
  rw [LG_sub, hw, hw']

/-- Woodford (2003), App. A.3: the derivative of the lead part composed with the projection. -/
theorem fderiv_snd_comp {N : (Fin n → ℝ) → Fin n → ℝ} (hN : ContDiff ℝ 1 N) (w : Fin n → ℝ) :
    fderiv ℝ (fun q : (Fin k → ℝ) × (Fin n → ℝ) => N q.2) (0, 0) (0, w) = fderiv ℝ N 0 w := by
  have hNd : HasFDerivAt N (fderiv ℝ N 0) ((0 : Fin k → ℝ), (0 : Fin n → ℝ)).2 :=
    (hN.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hs : HasFDerivAt (fun q : (Fin k → ℝ) × (Fin n → ℝ) => q.2)
      (ContinuousLinearMap.snd ℝ (Fin k → ℝ) (Fin n → ℝ)) (0, 0) := hasFDerivAt_snd
  have h := (hNd.comp ((0 : Fin k → ℝ), (0 : Fin n → ℝ)) hs).fderiv
  change fderiv ℝ (N ∘ Prod.snd) (0, 0) (0, w) = fderiv ℝ N 0 w
  rw [h]
  simp

/-- Woodford (2003), Ch. 7 and App. A.3 (**the Newton contraction for abstract conditions**): let
`Q`, `N` be `C¹` with `Q(0) + N(0) = 0`, and let the linearised operator have an inverse `Li`
that is uniformly bounded, a right inverse on bounded forcings and injective on bounded
processes. Then there are `r, δ, C > 0` such that on every event tree, for all disturbances and
initial lags with `‖e‖, ‖d‖ ≤ δ`, the exact conditions `Φ(z) = 0` have a solution within `r`, it
is the only one within `r`, `‖z‖ ≤ C‖Φ(0)‖`, and `z` lies in every class of processes that
contains `0`, is invariant under the Newton map on the ball and is closed under limits. -/
theorem newton_tree {Q : (Fin k → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ}
    {N : (Fin n → ℝ) → Fin n → ℝ} (hQ : ContDiff ℝ 1 Q) (hN : ContDiff ℝ 1 N)
    (h0 : Q 0 + N 0 = 0)
    {Li : ∀ {Y : Type u}, LagTree Y → (Y → Fin n → ℝ) → Y → Fin n → ℝ}
    (hL : InvBound Q N Li) :
    ∃ r > 0, ∃ δ > 0, ∃ C > 0, ∀ {Y : Type u} (T : LagTree Y) (e : Y → Fin k → ℝ)
      (d : Y → Fin n → ℝ), (∀ y, ‖e y‖ ≤ δ) → (∀ y, ‖d y‖ ≤ δ) →
        ∃ z : Y → Fin n → ℝ, ((∀ y, ‖z y‖ ≤ r) ∧ PhiG T Q N e d z = 0) ∧
          (∀ z' : Y → Fin n → ℝ, (∀ y, ‖z' y‖ ≤ r) → PhiG T Q N e d z' = 0 → z' = z) ∧
          (∀ τ', 0 ≤ τ' → (∀ y, ‖PhiG T Q N e d (fun _ => 0) y‖ ≤ τ') →
            ∀ y, ‖z y‖ ≤ C * τ') ∧
          ∀ A : (Y → Fin n → ℝ) → Prop, A (fun _ => 0) →
            (∀ w, (∀ y, ‖w y‖ ≤ r) → A w → A (fun x => w x - Li T (PhiG T Q N e d w) x)) →
            (∀ (ws : ℕ → Y → Fin n → ℝ) (w : Y → Fin n → ℝ), (∀ m, A (ws m)) →
              (∀ m y, ‖ws m y‖ ≤ r) → (∀ x, Tendsto (fun m => ws m x) atTop (𝓝 (w x))) →
                A w) → A z := by
  obtain ⟨⟨K, hK0, hK⟩, hR, -⟩ := id hL
  set K' := K + 1 with hK'
  have hK'0 : 0 < K' := by linarith
  set η := 1 / (8 * K') with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρQ, hρQ, hQr⟩ := remainder_gen hQ hη0
  obtain ⟨ρN, hρN, hNr⟩ := remainder_gen (g := fun q : (Fin k → ℝ) × (Fin n → ℝ) => N q.2)
    (hN.comp contDiff_snd) hη0
  set r := min ρQ ρN with hr
  have hr0 : 0 < r := lt_min hρQ hρN
  obtain ⟨CQ, hCQ⟩ := (isCompact_closedBall (0 : (Fin k → ℝ) × (Fin n → ℝ) × (Fin n → ℝ))
    r).exists_bound_of_continuousOn hQ.continuous.continuousOn
  obtain ⟨CN, hCN⟩ := (isCompact_closedBall (0 : Fin n → ℝ) r).exists_bound_of_continuousOn
    hN.continuous.continuousOn
  have hCQ0 : 0 ≤ CQ := (norm_nonneg _).trans (hCQ 0 (Metric.mem_closedBall_self hr0.le))
  have hCN0 : 0 ≤ CN := (norm_nonneg _).trans (hCN 0 (Metric.mem_closedBall_self hr0.le))
  set τ := r / (2 * K') with hτ
  have hτ0 : 0 < τ := by positivity
  obtain ⟨δQ, hδQ, hQc⟩ := Metric.continuousAt_iff.1
    (hQ.continuous.continuousAt (x := 0)) τ hτ0
  refine ⟨r, hr0, min r (δQ / 2), lt_min hr0 (by positivity), 2 * K', by positivity,
    fun {Y} T e d he hd => ?_⟩
  have hKK : ∀ (s : Y → Fin n → ℝ) (A : ℝ), 0 ≤ A →
      (∀ y, ‖s y‖ ≤ A) → ∀ y, ‖Li T s y‖ ≤ K' * A := fun s A hA hs y =>
    (hK T s A hA hs y).trans (mul_le_mul_of_nonneg_right (by linarith) hA)
  have heR : ∀ y, ‖e y‖ ≤ r := fun y => (he y).trans (min_le_left _ _)
  have hdR : ∀ y, ‖d y‖ ≤ r := fun y => (hd y).trans (min_le_left _ _)
  have hlag : ∀ z : Y → Fin n → ℝ, (∀ y, ‖z y‖ ≤ r) → ∀ x, ‖lagI T z d x‖ ≤ r := fun z hz x => by
    unfold lagI; split_ifs
    · exact hdR x
    · exact hz _
  have hin : ∀ z : Y → Fin n → ℝ, (∀ y, ‖z y‖ ≤ r) → ∀ x,
      (e x, lagI T z d x, z x) ∈ Metric.closedBall (0 : (Fin k → ℝ) × (Fin n → ℝ) ×
        (Fin n → ℝ)) r := fun z hz x => by
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Prod.norm_def]
    exact max_le (heR x) (max_le (hlag z hz x) (hz x))
  have hPhiB : ∀ z : Y → Fin n → ℝ, (∀ y, ‖z y‖ ≤ r) → ∀ x, ‖PhiG T Q N e d z x‖ ≤ CQ + CN :=
    fun z hz x => (norm_add_le _ _).trans (add_le_add (hCQ _ (hin z hz x))
      (Mv_norm_le T.markov hCN0 (fun y => hCN _ (by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hz y)) x))
  -- the Newton map
  set Tm : (Y → Fin n → ℝ) → (Y → Fin n → ℝ) :=
    fun Z x => Z x - Li T (PhiG T Q N e d Z) x with hTm
  have hcontr : ∀ z z' : Y → Fin n → ℝ, (∀ y, ‖z y‖ ≤ r) → (∀ y, ‖z' y‖ ≤ r) → ∀ D,
      (∀ y, ‖z y - z' y‖ ≤ D) → ∀ x, ‖Tm z x - Tm z' x‖ ≤ D / 2 := by
    intro z z' hz hz' D hD x
    have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD x)
    set CL := ‖fderiv ℝ Q 0‖ + ‖fderiv ℝ N 0‖
    have hLz : ∀ y, ‖LG T Q N (fun y => z y - z' y) y‖ ≤ CL * D :=
      norm_LG_le T Q N hD0 hD
    have hdPhi : ∀ y, ‖PhiG T Q N e d z y - PhiG T Q N e d z' y‖ ≤ (CQ + CN) + (CQ + CN) :=
      fun y => (norm_sub_le _ _).trans (add_le_add (hPhiB z hz y) (hPhiB z' hz' y))
    have hrem : ∀ y, ‖(PhiG T Q N e d z y - PhiG T Q N e d z' y) -
        LG T Q N (fun y => z y - z' y) y‖ ≤ η * D + η * D := by
      intro y
      have hl := lagv_sub_lagI' T z z' d y
      have hu1 : ‖(lagI T z d y, z y)‖ ≤ ρQ := by
        rw [Prod.norm_def]
        exact max_le ((hlag z hz y).trans (min_le_left _ _)) ((hz y).trans (min_le_left _ _))
      have hu2 : ‖(lagI T z' d y, z' y)‖ ≤ ρQ := by
        rw [Prod.norm_def]
        exact max_le ((hlag z' hz' y).trans (min_le_left _ _)) ((hz' y).trans (min_le_left _ _))
      have hq := hQr (e y) (lagI T z d y, z y) (lagI T z' d y, z' y)
        ((heR y).trans (min_le_left _ _)) hu1 hu2
      rw [Prod.mk_sub_mk, show fderiv ℝ Q ((0 : Fin k → ℝ),
        (0 : (Fin n → ℝ) × (Fin n → ℝ))) = fderiv ℝ Q 0 from rfl] at hq
      have hqD : ‖(lagI T z d y, z y) - (lagI T z' d y, z' y)‖ ≤ D := by
        rw [Prod.mk_sub_mk, Prod.norm_def, ← hl]
        exact max_le (norm_lagv_le T hD0 hD y) (hD y)
      have hnB : ∀ y', ‖N (z y') - N (z' y') - fderiv ℝ N 0 (z y' - z' y')‖ ≤ η * D :=
        fun y' => by
          have h := hNr 0 (z y') (z' y') (by rw [norm_zero]; exact hρN.le)
            ((hz y').trans (min_le_right _ _))
            ((hz' y').trans (min_le_right _ _))
          rw [fderiv_snd_comp hN] at h
          exact h.trans (mul_le_mul_of_nonneg_left (hD y') hη0.le)
      have hMv := Mv_norm_le T.markov (by positivity) hnB y
      have e1 : Mv T.M (fun y' => N (z y') - N (z' y') - fderiv ℝ N 0 (z y' - z' y')) y =
          Mv T.M (fun y' => N (z y')) y - Mv T.M (fun y' => N (z' y')) y -
            fderiv ℝ N 0 (Mv T.M (fun y' => z y' - z' y') y) := by
        rw [NonlinearNKMarkovLinks.Mv_sub, NonlinearNKMarkovLinks.Mv_sub]
        simp only
        rw [Mv_clm]
      rw [e1] at hMv
      have e2 : (PhiG T Q N e d z y - PhiG T Q N e d z' y) - LG T Q N (fun y => z y - z' y) y =
          (Q (e y, lagI T z d y, z y) - Q (e y, lagI T z' d y, z' y) -
            fderiv ℝ Q 0 (0, lagI T z d y - lagI T z' d y, z y - z' y)) +
          (Mv T.M (fun y' => N (z y')) y - Mv T.M (fun y' => N (z' y')) y -
            fderiv ℝ N 0 (Mv T.M (fun y' => z y' - z' y') y)) := by
        simp only [PhiG, LG, hl]
        abel
      rw [e2]
      exact (norm_add_le _ _).trans (add_le_add (hq.trans
        (mul_le_mul_of_nonneg_left hqD hη0.le)) hMv)
    have hs1 := Li_sub hL T (r := PhiG T Q N e d z) (r' := PhiG T Q N e d z')
      (A := CQ + CN) (A' := CQ + CN) (by positivity)
      (by positivity) (hPhiB z hz) (hPhiB z' hz')
    have hs2 := Li_sub hL T (A := (CQ + CN) + (CQ + CN)) (A' := CL * D)
      (by positivity) (by positivity) hdPhi hLz
    have hLL := Li_LG hL T hD0 hD
    have key : Tm z x - Tm z' x = -Li T (fun y => (PhiG T Q N e d z y -
        PhiG T Q N e d z' y) - LG T Q N (fun y => z y - z' y) y) x := by
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
    have hb : ∀ y, ‖PhiG T Q N e d (fun _ => 0) y‖ ≤ τ := fun y => by
      have e1 : PhiG T Q N e d (fun _ => 0) y =
          Q (e y, lagI T (fun _ => 0) d y, 0) - Q 0 := by
        simp only [PhiG, Mv_const T.markov]
        rw [eq_neg_of_add_eq_zero_right h0]
        abel
      rw [e1, ← dist_eq_norm]
      refine (hQc ?_).le
      rw [dist_zero_right, Prod.norm_def, Prod.norm_def]
      have hl : ‖lagI T (fun _ => (0 : Fin n → ℝ)) d y‖ ≤ δQ / 2 := by
        unfold lagI; split_ifs
        · exact (hd y).trans (min_le_right _ _)
        · rw [norm_zero]; positivity
      have h0' : ‖(0 : Fin n → ℝ)‖ ≤ δQ / 2 := by rw [norm_zero]; positivity
      exact lt_of_le_of_lt (max_le ((he y).trans (min_le_right _ _)) (max_le hl h0'))
        (by linarith)
    have h := hKK _ τ hτ0.le hb x
    simp only [hTm, zero_sub, norm_neg]
    calc _ ≤ K' * τ := h
      _ = r / 2 := by rw [hτ]; field_simp
  have hball : ∀ z : Y → Fin n → ℝ, (∀ y, ‖z y‖ ≤ r) → ∀ x, ‖Tm z x‖ ≤ r := by
    intro z hz x
    have h1 := hcontr z (fun _ => 0) hz (fun y => by simp [hr0.le]) r
      (fun y => by simpa using hz y) x
    calc ‖Tm z x‖ ≤ ‖Tm z x - Tm (fun _ => 0) x‖ + ‖Tm (fun _ => 0) x‖ := by
          have := norm_add_le (Tm z x - Tm (fun _ => 0) x) (Tm (fun _ => 0) x); simpa using this
      _ ≤ r / 2 + r / 2 := add_le_add h1 (hT0 x)
      _ = r := by ring
  -- Picard iteration
  set zs : ℕ → Y → Fin n → ℝ := fun m => Tm^[m] (fun _ => 0) with hzs
  have hzsB : ∀ m x, ‖zs m x‖ ≤ r := by
    intro m
    induction m with
    | zero => intro x; simp [hzs, hr0.le]
    | succ m ih =>
      intro x
      simp only [hzs, Function.iterate_succ_apply']
      exact hball _ ih x
  have hstep : ∀ m x, ‖zs m x - zs (m + 1) x‖ ≤ r / 2 / 2 ^ m := by
    intro m
    induction m with
    | zero =>
      intro x
      simp only [hzs, Function.iterate_zero, id, pow_zero, div_one]
      rw [norm_sub_rev]; simpa using hT0 x
    | succ m ih =>
      intro x
      have h := hcontr (zs (m + 1)) (zs m) (hzsB _) (hzsB _) (r / 2 / 2 ^ m)
        (fun x => by rw [norm_sub_rev]; exact ih x) x
      have e1 : zs (m + 1 + 1) = Tm (zs (m + 1)) := by
        simp only [hzs, Function.iterate_succ_apply']
      have e2 : zs (m + 1) = Tm (zs m) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e1, norm_sub_rev]
      conv_lhs => rw [show zs (m + 1) x = Tm (zs m) x from congrFun e2 x]
      calc _ ≤ r / 2 / 2 ^ m / 2 := h
        _ = r / 2 / 2 ^ (m + 1) := by rw [pow_succ]; ring
  have hcau : ∀ x, CauchySeq fun m => zs m x := fun x =>
    cauchySeq_of_le_geometric_two (C := r) fun m => by rw [dist_eq_norm]; exact hstep m x
  choose z hz using fun x => cauchySeq_tendsto_of_complete (hcau x)
  have hzdist : ∀ m x, ‖zs m x - z x‖ ≤ r / 2 ^ m := fun m x => by
    have := dist_le_of_le_geometric_two_of_tendsto (C := r) (f := fun m => zs m x)
      (fun m => by rw [dist_eq_norm]; exact hstep m x) (hz x) m
    rwa [dist_eq_norm] at this
  have hzB : ∀ x, ‖z x‖ ≤ r := fun x => le_of_tendsto' ((hz x).norm) fun m => hzsB m x
  have hfix : Tm z = z := by
    funext x
    have hlim : Tendsto (fun m => zs (m + 1) x) atTop (𝓝 (Tm z x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hg : Tendsto (fun m : ℕ => r / 2 ^ m / 2) atTop (𝓝 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (r / 2)
        simp only [mul_zero] at this
        refine this.congr fun m => ?_
        rw [one_div, inv_pow]; field_simp
      refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) hg
      have e : zs (m + 1) = Tm (zs m) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e, norm_sub_rev]
      exact hcontr z (zs m) hzB (hzsB m) (r / 2 ^ m) (fun x => by
        rw [norm_sub_rev]; exact hzdist m x) x
    exact tendsto_nhds_unique hlim ((hz x).comp (tendsto_add_atTop_nat 1))
  -- fixed points of `Tm` in the ball are exactly the solutions
  have hsol : ∀ w : Y → Fin n → ℝ, (∀ y, ‖w y‖ ≤ r) →
      (Tm w = w ↔ PhiG T Q N e d w = 0) := by
    intro w hw
    have hr' : ∀ y k, |PhiG T Q N e d w y k| ≤ CQ + CN := fun y k => by
      have := (norm_le_pi_norm _ k).trans (hPhiB w hw y); rwa [Real.norm_eq_abs] at this
    have hRL : LG T Q N (Li T (PhiG T Q N e d w)) = PhiG T Q N e d w :=
      hR T (PhiG T Q N e d w) (CQ + CN) (by positivity) hr'
    constructor
    · intro h
      have hl : Li T (PhiG T Q N e d w) = fun _ => 0 := by
        funext x
        have := congrFun h x
        simp only [hTm] at this
        have := congrArg (fun v => w x - v) this
        simp only [sub_sub_cancel, sub_self] at this
        exact this
      rw [← hRL, hl]
      funext x; exact LG_zero T Q N x
    · intro h
      have h0' : Li T (PhiG T Q N e d w) = fun _ => 0 := by
        rw [h]
        have := Li_LG hL T (v := fun _ => (0 : Fin n → ℝ)) le_rfl (fun _ => by simp)
        have e : LG T Q N (fun _ => (0 : Fin n → ℝ)) = 0 := funext fun x => LG_zero T Q N x
        rw [e] at this
        exact this
      funext x
      simp only [hTm, h0', sub_zero]
  have hsmall : ∀ τ', 0 ≤ τ' → (∀ y, ‖PhiG T Q N e d (fun _ => 0) y‖ ≤ τ') →
      ∀ y, ‖z y‖ ≤ 2 * K' * τ' := by
    intro τ' hτ' hb
    have hT0' : ∀ x, ‖Tm (fun _ => 0) x‖ ≤ K' * τ' := fun x => by
      have h := hKK _ τ' hτ' hb x
      simp only [hTm, zero_sub, norm_neg]
      exact h
    have hn : ∀ m : ℕ, ∀ y, ‖z y‖ ≤ r / 2 ^ m + 2 * K' * τ' := by
      intro m
      induction m with
      | zero => intro y; have := hzB y; have : 0 ≤ 2 * K' * τ' := by positivity
                simp only [pow_zero, div_one]; linarith
      | succ m ih =>
        intro y
        have h := hcontr z (fun _ => 0) hzB (fun y => by simp [hr0.le]) _
          (fun y => by simpa using ih y) y
        rw [hfix] at h
        calc ‖z y‖ ≤ ‖z y - Tm (fun _ => 0) y‖ + ‖Tm (fun _ => 0) y‖ := by
              have := norm_add_le (z y - Tm (fun _ => 0) y) (Tm (fun _ => 0) y); simpa using this
          _ ≤ (r / 2 ^ m + 2 * K' * τ') / 2 + K' * τ' := add_le_add h (hT0' y)
          _ = r / 2 ^ (m + 1) + 2 * K' * τ' := by rw [pow_succ]; ring
    intro y
    have ht : Tendsto (fun m : ℕ => r / 2 ^ m + 2 * K' * τ') atTop (𝓝 (0 + 2 * K' * τ')) := by
      refine Tendsto.add ?_ tendsto_const_nhds
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul r
      simp only [mul_zero] at this
      refine this.congr fun m => ?_
      rw [one_div, inv_pow]; field_simp
    have := ge_of_tendsto' ht fun m => hn m y
    simpa using this
  have hinv : ∀ A : (Y → Fin n → ℝ) → Prop, A (fun _ => 0) →
      (∀ w, (∀ y, ‖w y‖ ≤ r) → A w → A (fun x => w x - Li T (PhiG T Q N e d w) x)) →
      (∀ (ws : ℕ → Y → Fin n → ℝ) (w : Y → Fin n → ℝ), (∀ m, A (ws m)) →
        (∀ m y, ‖ws m y‖ ≤ r) → (∀ x, Tendsto (fun m => ws m x) atTop (𝓝 (w x))) → A w) →
      A z := by
    intro A hA0 hAT hAl
    have hAm : ∀ m, A (zs m) := by
      intro m
      induction m with
      | zero => simpa [hzs] using hA0
      | succ m ih =>
        have e : zs (m + 1) = Tm (zs m) := by simp only [hzs, Function.iterate_succ_apply']
        rw [e]; exact hAT _ (hzsB m) ih
    exact hAl zs z hAm hzsB hz
  refine ⟨z, ⟨hzB, (hsol z hzB).1 hfix⟩, fun z' hz'B hz' => ?_, hsmall, hinv⟩
  have hfix' := (hsol z' hz'B).2 hz'
  have hD : ∀ m : ℕ, ∀ x, ‖z' x - z x‖ ≤ 2 * r / 2 ^ m := by
    intro m
    induction m with
    | zero =>
      intro x
      have := (norm_sub_le (z' x) (z x)).trans (add_le_add (hz'B x) (hzB x))
      simp only [pow_zero, div_one]; linarith
    | succ m ih =>
      intro x
      have h := hcontr z' z hz'B hzB _ ih x
      rw [hfix, hfix'] at h
      exact h.trans (le_of_eq (by rw [pow_succ]; ring))
  funext x
  have ht : Tendsto (fun m : ℕ => 2 * r / 2 ^ m) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (2 * r)
    simp only [mul_zero] at this
    refine this.congr fun m => ?_
    rw [one_div, inv_pow]; field_simp
  have := ge_of_tendsto' ht fun m => hD m x
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

end Woodford.StabilizationWelfare.TidyR6bRamseyNewton
