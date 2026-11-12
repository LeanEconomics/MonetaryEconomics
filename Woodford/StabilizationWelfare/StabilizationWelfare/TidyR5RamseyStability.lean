/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR5RamseyWeighted
import StabilizationWelfare.NonlinearNKMarkovRamseyIFT

/-!
# Stability of the exact Ramsey dynamics: the effect of the initial commitment dies out

Woodford (2003), *Interest and Prices*, Chapter 6, §3.2, pp. 414–415 (the date-0 optimal
commitment converges to the plan that is optimal from a timeless perspective) and Chapter 7, §1
(the two plans differ only through the initial values of the lagged multipliers); Appendix A.3
(the implicit function theorem in sequence space).

The exact Ramsey conditions `NonlinearNKMarkovRamseyIFT.PhiR` on an event tree depend on the
initial (predetermined) lag `d` of `Δ, λ₁, λ₂` only at the root. Here: if `z′` solves the
conditions with initial lag `d′`, and `d` is close to `d′`, the solution with initial lag `d`
exists and differs from `z′` by at most `Cε μ^{date}` (`ε = sup‖d − d′‖`), for any
`max(α, z₁) < μ ≤ 1`: the influence of the initial commitment decays geometrically.

## Main results

* `norm_Mv_weighted`: the expectation of a weighted vector process.
* **`lag_stability`**: the weighted Newton–Picard argument around the given solution `z′`, using
  the weighted inverse `TidyR5RamseyWeighted.wLinvR_bound`; radii and constants depend only on the
  parameters and `μ`, uniformly over event trees.
-/

namespace Woodford.StabilizationWelfare.TidyR5RamseyStability

open Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovGeneral NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyLin
open NonlinearNKMarkovRamseyTree NonlinearNKMarkovRamseyIFT TidyR5RamseyWeighted

variable {X : Type*} (T : LagTree X)

/-- Woodford (2003), App. A.3: the expectation of a vector process with
`‖f(y)‖ ≤ B μ^{date(y)}` keeps the bound (`0 < μ ≤ 1`). -/
theorem norm_Mv_weighted {μ B : ℝ} (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (hB : 0 ≤ B)
    {f : X → Fin 9 → ℝ} (hf : ∀ y, ‖f y‖ ≤ B * μ ^ T.depth y) (x : X) :
    ‖Mv T.M f x‖ ≤ B * μ ^ T.depth x := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  have hfi : WB T μ (fun y => f y i) B := fun y => by
    have := (norm_le_pi_norm (f y) i).trans (hf y); rwa [Real.norm_eq_abs] at this
  exact (hfi.M hμ0 hμ1 hB) x

/-- **Woodford (2003), pp. 414–415 and Ch. 7, §1 (the initial commitment's influence decays
geometrically).** If `A_uG ≠ 0` and `max(α, z₁) < μ ≤ 1`, there are `r₀ > 0` and `C ≥ 0`,
depending only on the parameters and `μ`, such that for every radius `0 < r ≤ r₀` and on every
event tree: if `z′` solves the exact Ramsey conditions with disturbances `e` and initial lag `d′`
(all of size `≤ r`, `‖z′‖ ≤ r/2`) and `‖d − d′‖ ≤ ε` with `Cε ≤ r/2`, then there is a solution
`Z` with initial lag `d`, `‖Z‖ ≤ r`, and `‖Z(y) − z′(y)‖ ≤ Cε μ^{date(y)}`. -/
theorem lag_stability {p : Par} (R : RPar) (hp : p.Std) (hG : R.Au * Gw p R ≠ 0) {μ : ℝ}
    (hμα : p.α < μ) (hμz : z1 p < μ) (hμ1 : μ ≤ 1) :
    ∃ r0 > 0, ∃ C, 0 ≤ C ∧ ∀ r', 0 < r' → r' ≤ r0 → ∀ {Y : Type*} (T : LagTree Y)
      (e : Y → Fin 5 → ℝ) (d d' z' : Y → Fin 9 → ℝ), (∀ y, ‖e y‖ ≤ r') → (∀ y, ‖d y‖ ≤ r') →
        (∀ y, ‖d' y‖ ≤ r') → (∀ y, ‖z' y‖ ≤ r' / 2) → PhiR T p R e d' z' = 0 → ∀ ε, 0 ≤ ε →
          (∀ y, ‖d y - d' y‖ ≤ ε) → C * ε ≤ r' / 2 →
            ∃ Z : Y → Fin 9 → ℝ, (∀ y, ‖Z y‖ ≤ r') ∧ PhiR T p R e d Z = 0 ∧
              ∀ y, ‖Z y - z' y‖ ≤ C * ε * μ ^ T.depth y := by
  have hμ0 : 0 < μ := lt_trans hp.α_pos hμα
  obtain ⟨K0, hK00, hK0⟩ := LinvR_bound R hp
  obtain ⟨Kw, hKw0, hKw⟩ := wLinvR_bound R hp hμα hμz hμ1
  set K' := K0 + Kw + 1 with hK'
  have hK'0 : 0 < K' := by positivity
  set η := μ / (8 * K') with hη
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
  set CL := ‖LinearMap.toContinuousLinearMap (DLin p R)‖ with hCL
  set C0 := Kw * (CL + η) with hC0
  have hC00 : 0 ≤ C0 := by positivity
  refine ⟨r, hr0, 2 * C0, by positivity,
    fun r' hr' hr'r {Y} T e d d' z' he' hd' hdd' hz' hsol' ε hε hdd hCε => ?_⟩
  have he : ∀ y, ‖e y‖ ≤ r := fun y => (he' y).trans hr'r
  have hd : ∀ y, ‖d y‖ ≤ r := fun y => (hd' y).trans hr'r
  replace hd' : ∀ y, ‖d' y‖ ≤ r := fun y => (hdd' y).trans hr'r
  have hKK : ∀ (s : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A →
      (∀ y, ‖s y‖ ≤ A) → ∀ y, ‖LinvR T p R s y‖ ≤ K' * A := fun s A hA hs y =>
    (hK0 T s A hA hs y).trans (mul_le_mul_of_nonneg_right (by linarith) hA)
  have hKKw : ∀ (s : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A →
      (∀ y, ‖s y‖ ≤ A * μ ^ T.depth y) → ∀ y, ‖LinvR T p R s y‖ ≤ Kw * A * μ ^ T.depth y :=
    fun s A hA hs y => hKw T s A hA hs y
  have hpow : ∀ y : Y, μ ^ T.depth y ≤ 1 := fun y => pow_le_one₀ hμ0.le hμ1
  have hpow0 : ∀ y : Y, 0 ≤ μ ^ T.depth y := fun y => pow_nonneg hμ0.le _
  have hlag : ∀ (z dd : Y → Fin 9 → ℝ), (∀ y, ‖dd y‖ ≤ r) → (∀ y, ‖z y‖ ≤ r) →
      ∀ x, ‖lagI T z dd x‖ ≤ r := fun z dd hdd hz x => by
    unfold lagI; split_ifs
    · exact hdd x
    · exact hz _
  have hin : ∀ (z dd : Y → Fin 9 → ℝ), (∀ y, ‖dd y‖ ≤ r) → (∀ y, ‖z y‖ ≤ r) → ∀ x,
      (e x, lagI T z dd x, z x) ∈ Metric.closedBall (0 : (Fin 5 → ℝ) × (Fin 9 → ℝ) ×
        (Fin 9 → ℝ)) r := fun z dd hdd hz x => by
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Prod.norm_def]
    exact max_le (he x) (max_le (hlag z dd hdd hz x) (hz x))
  have hPhiB : ∀ (z dd : Y → Fin 9 → ℝ), (∀ y, ‖dd y‖ ≤ r) → (∀ y, ‖z y‖ ≤ r) →
      ∀ x, ‖PhiR T p R e dd z x‖ ≤ CQ + CN :=
    fun z dd hdd hz x => (norm_add_le _ _).trans (add_le_add (hCQ _ (hin z dd hdd hz x))
      (Mv_norm_le T.markov hCN0 (fun y => hCN _ (by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hz y)) x))
  -- the Newton map with the initial lag `d`
  set Tm : (Y → Fin 9 → ℝ) → (Y → Fin 9 → ℝ) :=
    fun Z x => Z x - LinvR T p R (PhiR T p R e d Z) x with hTm
  -- the weighted contraction
  have hcontr : ∀ z z'' : Y → Fin 9 → ℝ, (∀ y, ‖z y‖ ≤ r) → (∀ y, ‖z'' y‖ ≤ r) → ∀ B, 0 ≤ B →
      (∀ y, ‖z y - z'' y‖ ≤ B * μ ^ T.depth y) →
        ∀ x, ‖Tm z x - Tm z'' x‖ ≤ B / 2 * μ ^ T.depth x := by
    intro z z'' hz hz'' B hB hD x
    have hDs : ∀ y, ‖z y - z'' y‖ ≤ B := fun y =>
      (hD y).trans (by nlinarith [hpow y, hpow0 y])
    have hLz : ∀ y, ‖LR T p R (fun y => z y - z'' y) y‖ ≤ CL * B :=
      norm_LR_le T p R hB hDs
    have hdPhi : ∀ y, ‖PhiR T p R e d z y - PhiR T p R e d z'' y‖ ≤ (CQ + CN) + (CQ + CN) :=
      fun y => (norm_sub_le _ _).trans (add_le_add (hPhiB z d hd hz y) (hPhiB z'' d hd hz'' y))
    -- the weighted remainder
    have hrem : ∀ y, ‖(PhiR T p R e d z y - PhiR T p R e d z'' y) -
        LR T p R (fun y => z y - z'' y) y‖ ≤ (2 * η / μ * B) * μ ^ T.depth y := by
      intro y
      have hl := lagv_sub_lagI T z z'' d y
      have hu1 : ‖(lagI T z d y, z y)‖ ≤ ρQ := by
        rw [Prod.norm_def]
        exact max_le ((hlag z d hd hz y).trans (min_le_left _ _)) ((hz y).trans (min_le_left _ _))
      have hu2 : ‖(lagI T z'' d y, z'' y)‖ ≤ ρQ := by
        rw [Prod.norm_def]
        exact max_le ((hlag z'' d hd hz'' y).trans (min_le_left _ _))
          ((hz'' y).trans (min_le_left _ _))
      have hq := hQ (e y) (lagI T z d y, z y) (lagI T z'' d y, z'' y)
        ((he y).trans (min_le_left _ _)) hu1 hu2
      rw [Prod.mk_sub_mk, show fderiv ℝ (Qd p R) ((0 : Fin 5 → ℝ),
        (0 : (Fin 9 → ℝ) × (Fin 9 → ℝ))) = fderiv ℝ (Qd p R) 0 from rfl, fderiv_Qd R hp] at hq
      have hqD : ‖(lagI T z d y, z y) - (lagI T z'' d y, z'' y)‖ ≤ B / μ * μ ^ T.depth y := by
        rw [Prod.mk_sub_mk, Prod.norm_def, ← hl]
        refine max_le ?_ ((hD y).trans ?_)
        · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
          rw [Real.norm_eq_abs]
          have hwi : WB T μ (fun y => z y i - z'' y i) B := fun y' => by
            have := (norm_le_pi_norm (z y' - z'' y') i).trans (hD y')
            rwa [Real.norm_eq_abs] at this
          exact WB.lag hμ0 hB hwi y
        · have : B ≤ B / μ := le_div_self hB hμ0 hμ1
          exact mul_le_mul_of_nonneg_right this (hpow0 y)
      have hnB : ∀ y', ‖Nd p R (z y') - Nd p R (z'' y') - DNr p R (z y' - z'' y')‖ ≤
          (η * B) * μ ^ T.depth y' := fun y' => by
        have h := hN 0 (z y') (z'' y') (by rw [norm_zero]; exact hρN.le)
          ((hz y').trans (min_le_right _ _)) ((hz'' y').trans (min_le_right _ _))
        rw [fderiv_Nd_snd R] at h
        refine h.trans ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hD y') hη0.le
      have hMv := norm_Mv_weighted T hμ0 hμ1 (by positivity) hnB y
      have e1 : Mv T.M (fun y' => Nd p R (z y') - Nd p R (z'' y') - DNr p R (z y' - z'' y')) y =
          Mv T.M (fun y' => Nd p R (z y')) y - Mv T.M (fun y' => Nd p R (z'' y')) y -
            DNr p R (Mv T.M (fun y' => z y' - z'' y') y) := by
        rw [NonlinearNKMarkovLinks.Mv_sub, NonlinearNKMarkovLinks.Mv_sub]
        simp only
        rw [Mv_DNr]
      rw [e1] at hMv
      have e2 : (PhiR T p R e d z y - PhiR T p R e d z'' y) - LR T p R (fun y => z y - z'' y) y =
          (Qd p R (e y, lagI T z d y, z y) - Qd p R (e y, lagI T z'' d y, z'' y) -
            DQr p R (lagI T z d y - lagI T z'' d y) (z y - z'' y)) +
          (Mv T.M (fun y' => Nd p R (z y')) y - Mv T.M (fun y' => Nd p R (z'' y')) y -
            DNr p R (Mv T.M (fun y' => z y' - z'' y') y)) := by
        simp only [PhiR, LR, hl]
        abel
      rw [e2]
      refine (norm_add_le _ _).trans ?_
      have h1 := hq.trans (mul_le_mul_of_nonneg_left hqD hη0.le)
      have h2 : η * B * μ ^ T.depth y ≤ η * (B / μ * μ ^ T.depth y) := by
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (le_div_self hB hμ0 hμ1) (hpow0 y)) hη0.le
        linarith
      have e3 : 2 * η / μ * B * μ ^ T.depth y = η * (B / μ * μ ^ T.depth y) +
          η * (B / μ * μ ^ T.depth y) := by field_simp; ring
      rw [e3]
      exact add_le_add h1 (hMv.trans h2)
    have hs1 := LinvR_sub T R hp hG (r := PhiR T p R e d z) (r' := PhiR T p R e d z'')
      (A := CQ + CN) (A' := CQ + CN) (by positivity) (by positivity) (hPhiB z d hd hz)
      (hPhiB z'' d hd hz'')
    have hs2 := LinvR_sub T R hp hG (A := (CQ + CN) + (CQ + CN)) (A' := CL * B)
      (by positivity) (by positivity) hdPhi hLz
    have hLL := LinvR_LR T R hp hG hB hDs
    have key : Tm z x - Tm z'' x = -LinvR T p R (fun y => (PhiR T p R e d z y -
        PhiR T p R e d z'' y) - LR T p R (fun y => z y - z'' y) y) x := by
      rw [hs2]
      simp only [hTm]
      rw [hs1, hLL]
      funext i
      simp only [Pi.sub_apply, Pi.neg_apply]
      ring
    rw [key, norm_neg]
    have hw := hKKw _ (2 * η / μ * B) (by positivity) hrem x
    refine hw.trans (mul_le_mul_of_nonneg_right ?_ (hpow0 x))
    have : Kw * (2 * η / μ * B) = Kw / (4 * K') * B := by rw [hη]; field_simp; ring
    rw [this]
    have hKw' : Kw / (4 * K') ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    nlinarith
  -- the first step from `z'`
  have hstep0 : ∀ x, ‖Tm z' x - z' x‖ ≤ C0 * ε * μ ^ T.depth x := by
    intro x
    have hz'r : ∀ y, ‖z' y‖ ≤ r := fun y => (hz' y).trans (by linarith)
    have hb : ∀ y, ‖PhiR T p R e d z' y‖ ≤ ((CL + η) * ε) * μ ^ T.depth y := by
      intro y
      have h0 := congrFun hsol' y
      simp only [Pi.zero_apply] at h0
      by_cases hy : T.depth y = 0
      · have hdiff : PhiR T p R e d z' y = Qd p R (e y, d y, z' y) - Qd p R (e y, d' y, z' y) := by
          have e1 : PhiR T p R e d z' y = Qd p R (e y, d y, z' y) +
              Mv T.M (fun y' => Nd p R (z' y')) y := by simp [PhiR, lagI, hy]
          have e2 : PhiR T p R e d' z' y = Qd p R (e y, d' y, z' y) +
              Mv T.M (fun y' => Nd p R (z' y')) y := by simp [PhiR, lagI, hy]
          rw [e1]; rw [e2] at h0
          rw [eq_neg_of_add_eq_zero_left h0]
          abel
        rw [hdiff, hy, pow_zero, mul_one]
        have hu1 : ‖(d y, z' y)‖ ≤ ρQ := by
          rw [Prod.norm_def]; exact max_le ((hd y).trans (min_le_left _ _))
            ((hz'r y).trans (min_le_left _ _))
        have hu2 : ‖(d' y, z' y)‖ ≤ ρQ := by
          rw [Prod.norm_def]; exact max_le ((hd' y).trans (min_le_left _ _))
            ((hz'r y).trans (min_le_left _ _))
        have hq := hQ (e y) (d y, z' y) (d' y, z' y) ((he y).trans (min_le_left _ _)) hu1 hu2
        rw [Prod.mk_sub_mk, sub_self, show fderiv ℝ (Qd p R) ((0 : Fin 5 → ℝ),
          (0 : (Fin 9 → ℝ) × (Fin 9 → ℝ))) = fderiv ℝ (Qd p R) 0 from rfl, fderiv_Qd R hp]
          at hq
        have hnd : ‖(d y - d' y, (0 : Fin 9 → ℝ))‖ ≤ ε := by
          rw [Prod.norm_def, norm_zero]; exact max_le (hdd y) hε
        have hlin : ‖DQr p R (d y - d' y) 0‖ ≤ CL * ε := by
          have := norm_DLin_le p R (d y - d' y) 0 0 (B := ε) (hdd y) (by rw [norm_zero]; exact hε)
            (by rw [norm_zero]; exact hε)
          have hDN : DNr p R 0 = 0 := by
            have := (DNlin p R).map_zero
            simpa [DNlin] using this
          rwa [hDN, add_zero] at this
        calc ‖Qd p R (e y, d y, z' y) - Qd p R (e y, d' y, z' y)‖
            ≤ ‖Qd p R (e y, d y, z' y) - Qd p R (e y, d' y, z' y) - DQr p R (d y - d' y) 0‖ +
              ‖DQr p R (d y - d' y) 0‖ := by
              have := norm_add_le (Qd p R (e y, d y, z' y) - Qd p R (e y, d' y, z' y) -
                DQr p R (d y - d' y) 0) (DQr p R (d y - d' y) 0)
              simpa using this
          _ ≤ η * ε + CL * ε := add_le_add (hq.trans (mul_le_mul_of_nonneg_left hnd hη0.le)) hlin
          _ = (CL + η) * ε := by ring
      · have hsame : PhiR T p R e d z' y = PhiR T p R e d' z' y := by
          simp [PhiR, lagI, hy]
        rw [hsame, h0, norm_zero]
        positivity
    have h := hKKw _ ((CL + η) * ε) (by positivity) hb x
    simp only [hTm, sub_sub_cancel_left, norm_neg]
    calc _ ≤ Kw * ((CL + η) * ε) * μ ^ T.depth x := h
      _ = C0 * ε * μ ^ T.depth x := by rw [hC0]; ring
  -- the Picard iteration from `z'`
  set zs : ℕ → Y → Fin 9 → ℝ := fun n => Tm^[n] z' with hzs
  have hsucc : ∀ n, zs (n + 1) = Tm (zs n) := fun n => by
    simp only [hzs, Function.iterate_succ_apply']
  have hP : ∀ n : ℕ, (∀ y, ‖zs n y - z' y‖ ≤ 2 * C0 * ε * (1 - 1 / 2 ^ n) * μ ^ T.depth y) ∧
      ∀ y, ‖zs n y - zs (n + 1) y‖ ≤ C0 * ε / 2 ^ n * μ ^ T.depth y := by
    have hball : ∀ n : ℕ, (∀ y, ‖zs n y - z' y‖ ≤ 2 * C0 * ε * (1 - 1 / 2 ^ n) *
        μ ^ T.depth y) → ∀ y, ‖zs n y‖ ≤ r := fun n h y => by
      have h2 : 2 * C0 * ε * (1 - 1 / 2 ^ n) * μ ^ T.depth y ≤ 2 * C0 * ε := by
        have : 0 ≤ 1 / (2 : ℝ) ^ n := by positivity
        have : (1 : ℝ) - 1 / 2 ^ n ≤ 1 := by linarith
        have h3 : 0 ≤ 2 * C0 * ε := by positivity
        have h4 : (0 : ℝ) ≤ 1 - 1 / 2 ^ n := by
          have : (0 : ℝ) < 2 ^ n := by positivity
          rw [sub_nonneg, div_le_one this]; exact one_le_pow₀ (by norm_num)
        calc _ ≤ 2 * C0 * ε * 1 * 1 := by gcongr; exact hpow y
          _ = 2 * C0 * ε := by ring
      calc ‖zs n y‖ ≤ ‖zs n y - z' y‖ + ‖z' y‖ := by
            have := norm_add_le (zs n y - z' y) (z' y); simpa using this
        _ ≤ 2 * C0 * ε + r' / 2 := add_le_add ((h y).trans h2) (hz' y)
        _ ≤ r := by linarith
    intro n
    induction n with
    | zero =>
      refine ⟨fun y => by simp [hzs], fun y => ?_⟩
      rw [norm_sub_rev, hsucc]
      simpa [hzs] using hstep0 y
    | succ n ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hn1 : ∀ y, ‖zs (n + 1) y - z' y‖ ≤ 2 * C0 * ε * (1 - 1 / 2 ^ (n + 1)) *
          μ ^ T.depth y := fun y => by
        calc ‖zs (n + 1) y - z' y‖ ≤ ‖zs n y - z' y‖ + ‖zs n y - zs (n + 1) y‖ := by
              have := norm_sub_le (zs n y - z' y) (zs n y - zs (n + 1) y)
              rw [show zs n y - z' y - (zs n y - zs (n + 1) y) = zs (n + 1) y - z' y by abel]
                at this
              exact this
          _ ≤ 2 * C0 * ε * (1 - 1 / 2 ^ n) * μ ^ T.depth y + C0 * ε / 2 ^ n * μ ^ T.depth y :=
              add_le_add (ih1 y) (ih2 y)
          _ = 2 * C0 * ε * (1 - 1 / 2 ^ (n + 1)) * μ ^ T.depth y := by
              rw [pow_succ]; field_simp; ring
      refine ⟨hn1, fun y => ?_⟩
      have h := hcontr (zs (n + 1)) (zs n) (hball (n + 1) hn1) (hball n ih1) (C0 * ε / 2 ^ n)
        (by positivity) (fun y => by rw [norm_sub_rev]; exact ih2 y) y
      rw [← hsucc, ← hsucc, norm_sub_rev] at h
      calc _ ≤ C0 * ε / 2 ^ n / 2 * μ ^ T.depth y := h
        _ = C0 * ε / 2 ^ (n + 1) * μ ^ T.depth y := by rw [pow_succ]; ring
  have hballn : ∀ n y, ‖zs n y‖ ≤ r' := fun n y => by
    have h2 : 2 * C0 * ε * (1 - 1 / 2 ^ n) * μ ^ T.depth y ≤ 2 * C0 * ε := by
      have h3 : 0 ≤ 2 * C0 * ε := by positivity
      have h4 : (0 : ℝ) ≤ 1 - 1 / 2 ^ n := by
        have : (0 : ℝ) < 2 ^ n := by positivity
        rw [sub_nonneg, div_le_one this]; exact one_le_pow₀ (by norm_num)
      have h5 : (1 : ℝ) - 1 / 2 ^ n ≤ 1 := by
        have : 0 ≤ 1 / (2 : ℝ) ^ n := by positivity
        linarith
      calc _ ≤ 2 * C0 * ε * 1 * 1 := by gcongr; exact hpow y
        _ = 2 * C0 * ε := by ring
    calc ‖zs n y‖ ≤ ‖zs n y - z' y‖ + ‖z' y‖ := by
          have := norm_add_le (zs n y - z' y) (z' y); simpa using this
      _ ≤ 2 * C0 * ε + r' / 2 := add_le_add (((hP n).1 y).trans h2) (hz' y)
      _ ≤ r' := by linarith
  have hcau : ∀ x, CauchySeq fun n => zs n x := fun x =>
    cauchySeq_of_le_geometric_two (C := 2 * C0 * ε * μ ^ T.depth x) fun n => by
      rw [dist_eq_norm]
      refine ((hP n).2 x).trans (le_of_eq ?_)
      ring
  choose Z hZ using fun x => cauchySeq_tendsto_of_complete (hcau x)
  have hZdist : ∀ n x, ‖zs n x - Z x‖ ≤ 2 * C0 * ε * μ ^ T.depth x / 2 ^ n := fun n x => by
    have := dist_le_of_le_geometric_two_of_tendsto (C := 2 * C0 * ε * μ ^ T.depth x)
      (f := fun n => zs n x) (fun n => by
        rw [dist_eq_norm]
        refine ((hP n).2 x).trans (le_of_eq ?_)
        ring) (hZ x) n
    rwa [dist_eq_norm] at this
  have hZB' : ∀ x, ‖Z x‖ ≤ r' := fun x => le_of_tendsto' ((hZ x).norm) fun n => hballn n x
  have hZB : ∀ x, ‖Z x‖ ≤ r := fun x => (hZB' x).trans hr'r
  have hballr : ∀ n y, ‖zs n y‖ ≤ r := fun n y => (hballn n y).trans hr'r
  have hZw : ∀ x, ‖Z x - z' x‖ ≤ 2 * C0 * ε * μ ^ T.depth x := fun x => by
    have ht : Tendsto (fun n => ‖zs n x - z' x‖) atTop (𝓝 ‖Z x - z' x‖) :=
      ((hZ x).sub_const (z' x)).norm
    refine le_of_tendsto' ht fun n => ((hP n).1 x).trans ?_
    have h4 : (1 : ℝ) - 1 / 2 ^ n ≤ 1 := by
      have : 0 ≤ 1 / (2 : ℝ) ^ n := by positivity
      linarith
    have h3 : 0 ≤ 2 * C0 * ε := by positivity
    calc _ ≤ 2 * C0 * ε * 1 * μ ^ T.depth x := by gcongr
      _ = _ := by ring
  have hfix : Tm Z = Z := by
    funext x
    have hlim : Tendsto (fun n => zs (n + 1) x) atTop (𝓝 (Tm Z x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hg : Tendsto (fun n : ℕ => 2 * C0 * ε / 2 ^ n / 2 * μ ^ T.depth x) atTop (𝓝 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (2 * C0 * ε / 2 * μ ^ T.depth x)
        simp only [mul_zero] at this
        refine this.congr fun n => ?_
        rw [one_div, inv_pow]; field_simp
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hg
      rw [hsucc, norm_sub_rev]
      have hw : ∀ y, ‖Z y - zs n y‖ ≤ (2 * C0 * ε / 2 ^ n) * μ ^ T.depth y := fun y => by
        rw [norm_sub_rev]
        refine (hZdist n y).trans (le_of_eq ?_)
        ring
      exact hcontr Z (zs n) hZB (hballr n) (2 * C0 * ε / 2 ^ n) (by positivity) hw x
    exact tendsto_nhds_unique hlim ((hZ x).comp (tendsto_add_atTop_nat 1))
  -- the fixed point solves the conditions
  have hsolZ : PhiR T p R e d Z = 0 := by
    have hr' : ∀ y k, |PhiR T p R e d Z y k| ≤ CQ + CN := fun y k => by
      have := (norm_le_pi_norm _ k).trans (hPhiB Z d hd hZB y); rwa [Real.norm_eq_abs] at this
    have hRL := LR_LinvR T R hp hG (PhiR T p R e d Z) (CQ + CN) (by positivity) hr'
    have hl : LinvR T p R (PhiR T p R e d Z) = fun _ => 0 := by
      funext x
      have := congrFun hfix x
      simp only [hTm] at this
      have := congrArg (fun v => Z x - v) this
      simp only [sub_sub_cancel, sub_self] at this
      exact this
    rw [← hRL, hl]
    funext x; exact LR_zero T p R x
  exact ⟨Z, hZB', hsolZ, fun y => (hZw y).trans (le_of_eq (by ring))⟩

end Woodford.StabilizationWelfare.TidyR5RamseyStability
