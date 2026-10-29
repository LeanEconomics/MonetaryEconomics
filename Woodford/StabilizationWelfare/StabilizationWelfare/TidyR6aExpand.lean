/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR6aShock
import StabilizationWelfare.NonlinearNKMarkovRamseyIFT

/-!
# The first-order component of the exact Ramsey solution in sequence space

Woodford (2003), *Interest and Prices*, Chapter 6, §5 (pp. 455–463: the welfare expansion is
taken along a family of equilibria whose deviations are of first order in the amplitude of the
disturbances), Chapter 7, §1–2 (the timeless Ramsey plan) and Appendix A.3 (the implicit
function theorem in sequence space).

`NonlinearNKMarkovRamseyIFT.ramsey_existence` constructs, on every event tree, the locally unique
solution of the exact Ramsey conditions by a Newton–Picard contraction with the inverse
`LinvR` of the linearised operator. Here:

* `quad_remainder`: the second-order remainder of a `C²` map on a ball is `O(‖q‖²)`.
* **`ramsey_newton`**: the existence theorem with the A POSTERIORI bound: the solution lies within
  `C‖Φ(z̃)‖` of ANY approximate solution `z̃` in the ball (the contraction argument
  of `ramsey_existence`, restated with the general comparison point).
* `lagI_smul`, `DQr_lin`: the linear structure of the lag and of the linearisation.
* **`first_order_family`**: for disturbances `εê` (`‖ê‖ ≤ 1`) and initial lags `d(ε)` with
  `‖d(ε)‖ ≤ ε²` (the predetermined dispersion is second order), the exact solution `z(ε)`
  exists, is locally unique, and `‖z(ε) − εz₁‖ ≤ Cε²` UNIFORMLY over nodes and event trees,
  where `z₁ = L⁻¹(−DQs(ê))` is the solution of the linearised system with the disturbance
  forcing (`first_order_solves`). This is the first-order component in the sense of
  `BridgeExtensions.UProc` (`X − εX₁ = O(ε²)` uniformly in date and state).
-/

namespace Woodford.StabilizationWelfare.TidyR6aExpand

open Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovGeneral NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyLin
open NonlinearNKMarkovRamseyTree NonlinearNKMarkovRamseyIFT TidyR6aShock

/-- Woodford (2003), App. A.3 (**a second-order remainder bound**): for a `C²` map `g` there are
`ρ > 0` and `C ≥ 0` with `‖g(q) − g(0) − Dg(0)q‖ ≤ C‖q‖²` for `‖q‖ ≤ ρ`. -/
theorem quad_remainder {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F} (hg : ContDiff ℝ 2 g) :
    ∃ ρ > 0, ∃ C, 0 ≤ C ∧ ∀ q, ‖q‖ ≤ ρ → ‖g q - g 0 - fderiv ℝ g 0 q‖ ≤ C * ‖q‖ ^ 2 := by
  have hg1 : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := hg1.contDiffAt.exists_lipschitzOnWith (x := (0 : E))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 ht
  refine ⟨δ / 2, by positivity, K, K.coe_nonneg, fun q hq => ?_⟩
  have hlip : ∀ x ∈ Metric.closedBall (0 : E) (δ / 2),
      ‖fderiv ℝ g x - fderiv ℝ g 0‖ ≤ K * ‖x‖ := fun x hx => by
    have hx' : x ∈ Metric.ball (0 : E) δ := by
      rw [Metric.mem_closedBall] at hx; rw [Metric.mem_ball]; linarith
    have := hK.dist_le_mul x (hball hx') 0 (hball (Metric.mem_ball_self hδ))
    simpa [dist_eq_norm] using this
  set Bq := Metric.closedBall (0 : E) ‖q‖ with hBq
  have hsub : Bq ⊆ Metric.closedBall (0 : E) (δ / 2) := Metric.closedBall_subset_closedBall hq
  have hdiff2 : ∀ x ∈ Bq, HasFDerivWithinAt (fun x => g x - fderiv ℝ g 0 x)
      (fderiv ℝ g x - fderiv ℝ g 0) Bq x := fun x _ => by
    have h1 : HasFDerivAt g (fderiv ℝ g x) x :=
      ((hg.differentiable (by norm_num)) x).hasFDerivAt
    exact (h1.sub (fderiv ℝ g 0).hasFDerivAt).hasFDerivWithinAt
  have hbd : ∀ x ∈ Bq, ‖fderiv ℝ g x - fderiv ℝ g 0‖ ≤ K * ‖q‖ := fun x hx => by
    refine (hlip x (hsub hx)).trans (mul_le_mul_of_nonneg_left ?_ K.coe_nonneg)
    simpa [hBq] using hx
  have hq0 : (0 : E) ∈ Bq := Metric.mem_closedBall_self (norm_nonneg q)
  have hqq : q ∈ Bq := by rw [hBq, Metric.mem_closedBall, dist_zero_right]
  have := (convex_closedBall (0 : E) ‖q‖).norm_image_sub_le_of_norm_hasFDerivWithin_le hdiff2 hbd
    hq0 hqq
  have e : g q - fderiv ℝ g 0 q - (g 0 - fderiv ℝ g 0 0) = g q - g 0 - fderiv ℝ g 0 q := by
    rw [map_zero]; abel
  rw [e, sub_zero] at this
  calc _ ≤ K * ‖q‖ * ‖q‖ := this
    _ = K * ‖q‖ ^ 2 := by ring

/-- Woodford (2003), Ch. 7 and App. A.3 (**existence, local uniqueness and the a posteriori
bound**): if `A_uG ≠ 0` there are `r, δ, C > 0`, depending only on the parameters, such that on
every event tree, for disturbances and initial lags with `‖e‖, ‖d‖ ≤ δ`, the exact Ramsey
conditions `Φ(z) = 0` have a solution with `‖z‖ ≤ r`, the only one there, and for EVERY `z̃` with
`‖z̃‖ ≤ r`, `‖z − z̃‖ ≤ C sup‖Φ(z̃)‖` (the proof of
`NonlinearNKMarkovRamseyIFT.ramsey_existence`, with a general comparison point). -/
theorem ramsey_newton {p : Par} (R : RPar) (hp : p.Std) (hG : R.Au * Gw p R ≠ 0) :
    ∃ r > 0, ∃ δ > 0, ∃ C > 0, ∀ {Y : Type*} (T : LagTree Y) (e : Y → Fin 5 → ℝ)
      (d : Y → Fin 9 → ℝ), (∀ y, ‖e y‖ ≤ δ) → (∀ y, ‖d y‖ ≤ δ) →
        ∃ z : Y → Fin 9 → ℝ, ((∀ y, ‖z y‖ ≤ r) ∧ PhiR T p R e d z = 0) ∧
          (∀ z' : Y → Fin 9 → ℝ, (∀ y, ‖z' y‖ ≤ r) → PhiR T p R e d z' = 0 → z' = z) ∧
          ∀ zt : Y → Fin 9 → ℝ, (∀ y, ‖zt y‖ ≤ r) → ∀ τ', 0 ≤ τ' →
            (∀ y, ‖PhiR T p R e d zt y‖ ≤ τ') → ∀ y, ‖z y - zt y‖ ≤ C * τ' := by
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
  have hpost : ∀ zt : Y → Fin 9 → ℝ, (∀ y, ‖zt y‖ ≤ r) → ∀ τ', 0 ≤ τ' →
      (∀ y, ‖PhiR T p R e d zt y‖ ≤ τ') → ∀ y, ‖z y - zt y‖ ≤ 2 * K' * τ' := by
    intro zt hzt τ' hτ' hb
    have hT0' : ∀ x, ‖Tm zt x - zt x‖ ≤ K' * τ' := fun x => by
      have h := hKK _ τ' hτ' hb x
      simp only [hTm, sub_sub_cancel_left, norm_neg]
      exact h
    have hn : ∀ n : ℕ, ∀ y, ‖z y - zt y‖ ≤ 2 * r / 2 ^ n + 2 * K' * τ' := by
      intro n
      induction n with
      | zero =>
        intro y
        have := (norm_sub_le (z y) (zt y)).trans (add_le_add (hzB y) (hzt y))
        have : 0 ≤ 2 * K' * τ' := by positivity
        simp only [pow_zero, div_one]; linarith
      | succ n ih =>
        intro y
        have h := hcontr z zt hzB hzt _ ih y
        rw [hfix] at h
        calc ‖z y - zt y‖ ≤ ‖z y - Tm zt y‖ + ‖Tm zt y - zt y‖ := by
              have := norm_add_le (z y - Tm zt y) (Tm zt y - zt y); simpa using this
          _ ≤ (2 * r / 2 ^ n + 2 * K' * τ') / 2 + K' * τ' := add_le_add h (hT0' y)
          _ = 2 * r / 2 ^ (n + 1) + 2 * K' * τ' := by rw [pow_succ]; ring
    intro y
    have ht : Tendsto (fun n : ℕ => 2 * r / 2 ^ n + 2 * K' * τ') atTop
        (𝓝 (0 + 2 * K' * τ')) := by
      refine Tendsto.add ?_ tendsto_const_nhds
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (2 * r)
      simp only [mul_zero] at this
      refine this.congr fun n => ?_
      rw [one_div, inv_pow]; field_simp
    have := ge_of_tendsto' ht fun n => hn n y
    simpa using this
  refine ⟨z, ⟨hzB, (hsol z hzB).1 hfix⟩, fun z' hz'B hz' => ?_, hpost⟩
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

/-! ## Linear structure -/

/-- Woodford (2003), §5: the disturbance derivative is linear. -/
theorem DQs_smul (p : Par) (R : RPar) (c : ℝ) (e : Fin 5 → ℝ) :
    DQs p R (c • e) = c • DQs p R e := by
  funext i; fin_cases i <;> simp [DQs] <;> ring

/-- Woodford (2003), §5: the lag/current linearisation is linear,
`DQr(ca + b, cu) = c DQr(a, u) + DQr(b, 0)`. -/
theorem DQr_lin (p : Par) (R : RPar) (c : ℝ) (a b u : Fin 9 → ℝ) :
    DQr p R (c • a + b) (c • u) = c • DQr p R a u + DQr p R b 0 := by
  funext i; fin_cases i <;> simp [DQr] <;> ring

/-- Woodford (2003), §5: the lead linearisation is homogeneous. -/
theorem DNr_smul (p : Par) (R : RPar) (c : ℝ) (n : Fin 9 → ℝ) :
    DNr p R (c • n) = c • DNr p R n := by
  funext i; fin_cases i <;> simp [DNr] <;> ring

/-- Woodford (2003), §5: the disturbance derivative is bounded,
`‖DQs e‖ ≤ ‖DQd(0)‖ ‖e‖`. -/
theorem norm_DQs_le {p : Par} (R : RPar) (hp : p.Std) (e : Fin 5 → ℝ) :
    ‖DQs p R e‖ ≤ ‖fderiv ℝ (Qd p R) 0‖ * ‖e‖ := by
  have h := fderiv_Qd_full R hp e 0 0
  have h0 : DQr p R 0 0 = 0 := by funext i; fin_cases i <;> simp [DQr]
  rw [h0, add_zero] at h
  rw [← h]
  refine ((fderiv ℝ (Qd p R) 0).le_opNorm _).trans (le_of_eq ?_)
  congr 1
  simp [Prod.norm_def]

variable {Y : Type*} (T : LagTree Y)

/-- Woodford (2003), Ch. 7: the lag of `εz` with the initial value `d` is `ε lag z` plus `d` at
the roots. -/
theorem lagI_smul (c : ℝ) (z d : Y → Fin 9 → ℝ) (x : Y) :
    lagI T (fun y => c • z y) d x = c • lagv T z x + (if T.depth x = 0 then d x else 0) := by
  funext i
  simp only [lagI, lagv, lag0, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- Woodford (2003), App. A.3: the first-order component `z₁ = L⁻¹(−DQs(ê))` solves the
linearised Ramsey system with the disturbance forcing, and is bounded by `K‖DQd(0)‖`. -/
theorem first_order_solves {p : Par} (R : RPar) (hp : p.Std) (hG : R.Au * Gw p R ≠ 0) :
    ∃ B, 0 ≤ B ∧ ∀ {Y : Type*} (T : LagTree Y) (ê : Y → Fin 5 → ℝ), (∀ y, ‖ê y‖ ≤ 1) →
      LR T p R (LinvR T p R fun y => -DQs p R (ê y)) = (fun y => -DQs p R (ê y)) ∧
        ∀ y, ‖LinvR T p R (fun y => -DQs p R (ê y)) y‖ ≤ B := by
  obtain ⟨K, hK0, hK⟩ := LinvR_bound R hp
  set CD := ‖fderiv ℝ (Qd p R) 0‖
  refine ⟨K * CD, by positivity, fun T ê hê => ⟨?_, ?_⟩⟩
  · refine LR_LinvR T R hp hG _ CD (norm_nonneg _) fun y k => ?_
    have := (norm_le_pi_norm (-DQs p R (ê y)) k).trans
      ((norm_neg _).le.trans ((norm_DQs_le R hp (ê y)).trans
        (by simpa using mul_le_mul_of_nonneg_left (hê y) (norm_nonneg (fderiv ℝ (Qd p R) 0)))))
    rwa [Real.norm_eq_abs] at this
  · exact hK T _ CD (norm_nonneg _) fun y => (norm_neg _).le.trans ((norm_DQs_le R hp (ê y)).trans
      (by simpa using mul_le_mul_of_nonneg_left (hê y) (norm_nonneg (fderiv ℝ (Qd p R) 0))))

/-- Woodford (2003), App. A.3: the residual of the exact conditions at the first-order
approximation `εz₁` is the root-lag term plus the second-order remainders. -/
theorem residual_split {p : Par} (R : RPar) (hp : p.Std) (ê : Y → Fin 5 → ℝ)
    (d z1 : Y → Fin 9 → ℝ) (ε : ℝ) (hL : LR T p R z1 = fun y => -DQs p R (ê y)) (x : Y) :
    PhiR T p R (fun y => ε • ê y) d (fun y => ε • z1 y) x =
      DQr p R (if T.depth x = 0 then d x else 0) 0 +
        (Qd p R (ε • ê x, lagI T (fun y => ε • z1 y) d x, ε • z1 x) - Qd p R 0 -
          fderiv ℝ (Qd p R) 0 (ε • ê x, lagI T (fun y => ε • z1 y) d x, ε • z1 x)) +
        Mv T.M (fun y => Nd p R (ε • z1 y) - Nd p R 0 - fderiv ℝ (Nd p R) 0 (ε • z1 y)) x := by
  set q : (Fin 5 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) :=
    (ε • ê x, lagI T (fun y => ε • z1 y) d x, ε • z1 x) with hq
  set RNf : Y → Fin 9 → ℝ := fun y => Nd p R (ε • z1 y) - Nd p R 0 -
    fderiv ℝ (Nd p R) 0 (ε • z1 y) with hRN
  have e2 : fderiv ℝ (Qd p R) 0 q = ε • DQs p R (ê x) + ε • DQr p R (lagv T z1 x) (z1 x) +
      DQr p R (if T.depth x = 0 then d x else 0) 0 := by
    rw [hq, fderiv_Qd_full R hp, lagI_smul, DQr_lin, DQs_smul]
    abel
  have e3 : Mv T.M (fun y => Nd p R (ε • z1 y)) x =
      Nd p R 0 + ε • DNr p R (Mv T.M z1 x) + Mv T.M RNf x := by
    have hf : (fun y => Nd p R (ε • z1 y)) =
        fun y => (Nd p R 0 + ε • DNr p R (z1 y)) + RNf y := by
      funext y
      simp only [hRN, fderiv_Nd, DNr_smul]
      abel
    rw [hf, congrFun (Mv_add T.M _ _) x, congrFun (Mv_add T.M _ _) x, Mv_const' T,
      Mv_smul, Mv_DNr]
  have e4 : DQr p R (lagv T z1 x) (z1 x) + DNr p R (Mv T.M z1 x) = -DQs p R (ê x) :=
    congrFun hL x
  have e5 : Qd p R 0 + Nd p R 0 = 0 := Qd_Nd_zero R hp
  have e1 : PhiR T p R (fun y => ε • ê y) d (fun y => ε • z1 y) x =
      Qd p R q + Mv T.M (fun y => Nd p R (ε • z1 y)) x := rfl
  rw [e1, e3]
  have e6 : Qd p R q = Qd p R 0 + fderiv ℝ (Qd p R) 0 q +
      (Qd p R q - Qd p R 0 - fderiv ℝ (Qd p R) 0 q) := by abel
  rw [e6, e2]
  have e7 : DQr p R (lagv T z1 x) (z1 x) = -DQs p R (ê x) - DNr p R (Mv T.M z1 x) := by
    rw [← e4]; abel
  rw [e7]
  have e8 : Nd p R 0 = -Qd p R 0 := by rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact e5
  rw [e8]
  module

/-- **Woodford (2003), Ch. 6, §5, and App. A.3 (the first-order component of the exact Ramsey
solution).** If `A_uG ≠ 0` there are `r, δ₀ > 0` and `C ≥ 0`, depending only on the parameters,
such that on every event tree, for every disturbance pattern `ê` with `‖ê‖ ≤ 1`, every amplitude
`|ε| ≤ δ₀` and every initial lag `d` with `‖d‖ ≤ ε²`, the exact Ramsey conditions with
disturbances `εê` have a solution `z` with `‖z‖ ≤ r`, the only one there, and
`‖z − εz₁‖ ≤ Cε²` at every node, `z₁ = L⁻¹(−DQe(ê))` (`first_order_solves`). -/
theorem first_order_family {p : Par} (R : RPar) (hp : p.Std) (hG : R.Au * Gw p R ≠ 0) :
    ∃ r > 0, ∃ δ₀ > 0, ∃ C, 0 ≤ C ∧ ∀ {Y : Type*} (T : LagTree Y) (ê : Y → Fin 5 → ℝ)
      (d : Y → Fin 9 → ℝ) (ε : ℝ), (∀ y, ‖ê y‖ ≤ 1) → |ε| ≤ δ₀ → (∀ y, ‖d y‖ ≤ ε ^ 2) →
        ∃ z : Y → Fin 9 → ℝ, ((∀ y, ‖z y‖ ≤ r) ∧ PhiR T p R (fun y => ε • ê y) d z = 0) ∧
          (∀ z' : Y → Fin 9 → ℝ, (∀ y, ‖z' y‖ ≤ r) →
            PhiR T p R (fun y => ε • ê y) d z' = 0 → z' = z) ∧
          ∀ y, ‖z y - ε • LinvR T p R (fun y => -DQs p R (ê y)) y‖ ≤ C * ε ^ 2 := by
  obtain ⟨r, hr, δ, hδ, CN, hCN, hNew⟩ := ramsey_newton R hp hG
  obtain ⟨B1, hB1, hz1⟩ := first_order_solves R hp hG
  obtain ⟨ρQ, hρQ, CQ, hCQ, hQ⟩ := quad_remainder (contDiff_Qd (n := 2) p R)
  obtain ⟨ρN, hρN, CN2, hCN2, hN⟩ := quad_remainder (contDiff_Nd (n := 2) p R)
  set CL := ‖LinearMap.toContinuousLinearMap (DLin p R)‖ with hCL
  set a := B1 + 2 with ha
  have ha0 : 0 < a := by positivity
  set δ₀ := min (min 1 δ) (min (ρQ / a) (min (ρN / a) (r / a))) with hδ₀
  have hδ₀0 : 0 < δ₀ := by positivity
  refine ⟨r, hr, δ₀, hδ₀0, CN * (CL + CQ * a ^ 2 + CN2 * a ^ 2), by positivity,
    fun {Y} T ê d ε hê hε hd => ?_⟩
  have hε1 : |ε| ≤ 1 := hε.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεδ : |ε| ≤ δ := hε.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεQ : |ε| * a ≤ ρQ := by
    have := hε.trans ((min_le_right _ _).trans (min_le_left _ _))
    rwa [le_div_iff₀ ha0] at this
  have hεN : |ε| * a ≤ ρN := by
    have := hε.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    rwa [le_div_iff₀ ha0] at this
  have hεr : |ε| * a ≤ r := by
    have := hε.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    rwa [le_div_iff₀ ha0] at this
  have hε2 : ε ^ 2 ≤ |ε| := by
    rw [← sq_abs]; nlinarith [abs_nonneg ε]
  have he : ∀ y, ‖ε • ê y‖ ≤ δ := fun y => by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg ε) (hê y)).trans hεδ
  have hdδ : ∀ y, ‖d y‖ ≤ δ := fun y => (hd y).trans (hε2.trans hεδ)
  obtain ⟨z, hz, huniq, hpost⟩ := hNew T (fun y => ε • ê y) d he hdδ
  obtain ⟨hLz1, hz1b⟩ := hz1 T ê hê
  set z1 := LinvR T p R (fun y => -DQs p R (ê y)) with hz1d
  have hzt : ∀ y, ‖ε • z1 y‖ ≤ |ε| * B1 := fun y => by
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hz1b y) (abs_nonneg ε)
  have hztr : ∀ y, ‖ε • z1 y‖ ≤ r := fun y =>
    (hzt y).trans ((mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg ε)).trans hεr)
  have hres : ∀ x, ‖PhiR T p R (fun y => ε • ê y) d (fun y => ε • z1 y) x‖ ≤
      (CL + CQ * a ^ 2 + CN2 * a ^ 2) * ε ^ 2 := by
    intro x
    rw [residual_split T R hp ê d z1 ε hLz1 x]
    have hdr : ‖(if T.depth x = 0 then d x else 0 : Fin 9 → ℝ)‖ ≤ ε ^ 2 := by
      split_ifs
      · exact hd x
      · rw [norm_zero]; positivity
    have hDN0 : DNr p R 0 = 0 := by funext i; fin_cases i <;> simp [DNr]
    have b1 : ‖DQr p R (if T.depth x = 0 then d x else 0) 0‖ ≤ CL * ε ^ 2 := by
      have := norm_DLin_le p R (if T.depth x = 0 then d x else 0) 0 0 hdr
        (by rw [norm_zero]; positivity) (by rw [norm_zero]; positivity)
      rwa [hDN0, add_zero] at this
    have hqn : ‖((ε • ê x, lagI T (fun y => ε • z1 y) d x, ε • z1 x) :
        (Fin 5 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ))‖ ≤ |ε| * a := by
      rw [Prod.norm_def, Prod.norm_def]
      have h1 : ‖ε • ê x‖ ≤ |ε| * a := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left ((hê x).trans (by linarith)) (abs_nonneg ε)
      have h2 : ‖lagI T (fun y => ε • z1 y) d x‖ ≤ |ε| * a := by
        unfold lagI; split_ifs
        · exact (hd x).trans (hε2.trans (le_mul_of_one_le_right (abs_nonneg ε) (by linarith)))
        · exact (hzt _).trans (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg ε))
      have h3 : ‖ε • z1 x‖ ≤ |ε| * a :=
        (hzt x).trans (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg ε))
      exact max_le h1 (max_le h2 h3)
    have b2 := hQ _ (hqn.trans hεQ)
    have b2' : CQ * ‖((ε • ê x, lagI T (fun y => ε • z1 y) d x, ε • z1 x) :
        (Fin 5 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ))‖ ^ 2 ≤ CQ * a ^ 2 * ε ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hqn 2
      rw [mul_pow, sq_abs] at this
      nlinarith
    have b3 : ∀ y, ‖Nd p R (ε • z1 y) - Nd p R 0 - fderiv ℝ (Nd p R) 0 (ε • z1 y)‖ ≤
        CN2 * a ^ 2 * ε ^ 2 := fun y => by
      have hza : ‖ε • z1 y‖ ≤ |ε| * a :=
        (hzt y).trans (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg ε))
      refine (hN _ (hza.trans hεN)).trans ?_
      have := pow_le_pow_left₀ (norm_nonneg _) hza 2
      rw [mul_pow, sq_abs] at this
      nlinarith
    have b3' := Mv_norm_le T.markov (by positivity) b3 x
    calc _ ≤ ‖DQr p R (if T.depth x = 0 then d x else 0) 0‖ +
          ‖Qd p R (ε • ê x, lagI T (fun y => ε • z1 y) d x, ε • z1 x) - Qd p R 0 -
            fderiv ℝ (Qd p R) 0 (ε • ê x, lagI T (fun y => ε • z1 y) d x, ε • z1 x)‖ +
          ‖Mv T.M (fun y => Nd p R (ε • z1 y) - Nd p R 0 -
            fderiv ℝ (Nd p R) 0 (ε • z1 y)) x‖ := norm_add₃_le
      _ ≤ CL * ε ^ 2 + CQ * a ^ 2 * ε ^ 2 + CN2 * a ^ 2 * ε ^ 2 :=
          add_le_add (add_le_add b1 (b2.trans b2')) b3'
      _ = (CL + CQ * a ^ 2 + CN2 * a ^ 2) * ε ^ 2 := by ring
  have hp' := hpost (fun y => ε • z1 y) hztr _ (by positivity) hres
  refine ⟨z, hz, huniq, fun y => ?_⟩
  calc _ ≤ CN * ((CL + CQ * a ^ 2 + CN2 * a ^ 2) * ε ^ 2) := hp' y
    _ = _ := by ring

end Woodford.StabilizationWelfare.TidyR6aExpand
