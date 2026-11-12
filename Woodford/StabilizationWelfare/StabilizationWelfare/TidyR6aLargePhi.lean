/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR6aBridge

/-!
# Large distortions: the Ramsey plans around the distorted steady state

Woodford (2003), *Interest and Prices*, Chapter 6, §3.2, pp. 414–415, and §5, pp. 455–463
(Benigno–Woodford: `Φ` need not be small), and Chapter 7, §1.

`TidyR5RamseyDate0.date0_main` constructs the date-0 plan by perturbing from the EFFICIENT steady
state, so it needs `Φ` small. Here every result is obtained directly at the DISTORTED steady
state `w̄(Φ)` of `NonlinearNKMarkovRamsey.ramsey_steadyState`, for every `Φ` with `A_uG ≠ 0` (in
particular
every `A_u > 0`, `0 ≤ Φ ≤ 1`, `NonlinearNKMarkovRamseyLin.AuGw_pos`), using that the root and
invertibility conditions of the linearised system hold there (`root_any_Phi`: the commitment
polynomial `βz² − (1 + β + κθ)z + 1` does not depend on `Φ`, because `λ_x = κ/θ` for every `Φ`,
`NonlinearNKMarkovRamseyLin.key_theta`; the inverse `LinvR` and its sup and weighted bounds
`LinvR_bound`, `TidyR5RamseyWeighted.wLinvR_bound` hold for every `RPar`):

* **`timeless_any_Phi`**: the timeless plan exists and is locally unique for small disturbances
  and `Δ_{−1}` near `1`, and without disturbances it converges geometrically to the distorted
  steady state, `‖w(y) − w̄(Φ)‖ ≤ C|Δ_{−1} − 1|μ^{date(y)}`.
* **`date0_any_Phi`**: the date-0 plan exists, is locally unique and converges geometrically to
  the timeless plan, `‖w⁰ − wᵀ‖ ≤ C|λ̄₁(Φ)|μ^{date}`, for every `Φ` whose date-0 commitment gap
  `|λ̄₁(Φ)| = ΦA_u/((1−αβ)(ω+σ))` lies within the radius `δ(Φ)` of the distorted steady state.
* `lam1_scale`: the gap is homogeneous of degree one in A_u, like the conditions themselves
  (`TidyR5RamseyDate0.scale_solution`), so renormalising A_u cannot make it small relative to
  the radius.

The date-0 plan of a distorted economy is at a POSITIVE distance `ρ(Φ)` from the steady state at
date 0 (`TidyR6aBridge.date0_far`), so its existence for every `Φ ∈ [0, 1)` is not a local
question at `w̄(Φ)`; see the report for what a global argument would need.
-/

namespace Woodford.StabilizationWelfare.TidyR6aLargePhi

open Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovGeneral NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyLin
open NonlinearNKMarkovRamseyTree NonlinearNKMarkovRamseyIFT TidyR5RamseyWeighted
open TidyR5RamseyStability TidyR5RamseyDate0

/-- Woodford (2003), Ch. 7, pp. 475–476, and §5 (**the root condition holds at every distorted
steady state**): the stable root `z₁` of `βz² − (1 + β + κθ)z + 1` satisfies `0 < z₁ < 1 < z₂`,
and the polynomial does not involve `Φ` (the weight `λ_x/κ = 1/θ` of the linearised targeting
rule is `Φ`-independent, `key_theta`); for `A_u > 0`, `0 ≤ Φ ≤ 1` the targeting rule's weight is
positive. -/
theorem root_any_Phi {p : Par} (hp : p.Std) (R : RPar) (hA : 0 < R.Au) (hΦ0 : 0 ≤ R.Φ)
    (hΦ1 : R.Φ ≤ 1) :
    0 < z1 p ∧ z1 p < 1 ∧ 1 < z2 p ∧ 0 < R.Au * Gw p R ∧
      (1 - p.α * p.β) * (p.σ + p.ω) * aE p * (ramseyLam p R 3 - ramseyLam p R 0) =
        R.Au * Gw p R * p.θ := by
  obtain ⟨h1, h2, h3, -, -⟩ := z_props hp
  exact ⟨h1, h2, h3, AuGw_pos R hp hA hΦ0 hΦ1, key_theta R hp⟩

/-- Woodford (2003), Ch. 7: the timeless root lag in deviations from the steady state of the same
economy: only `Δ_{−1} − 1`. -/
theorem lagTL_sub (p : Par) (R : RPar) (Dm1 : ℝ) :
    lagTL p R Dm1 - ramseySS p R = ![0, 0, 0, 0, Dm1 - 1, 0, 0, 0, 0] := by
  funext i; fin_cases i <;> simp [lagTL, ramseySS]

/-- Woodford (2003), Ch. 7: the size of the timeless root lag in deviations. -/
theorem norm_lagTL_sub (p : Par) (R : RPar) (Dm1 : ℝ) :
    ‖lagTL p R Dm1 - ramseySS p R‖ ≤ |Dm1 - 1| := by
  rw [lagTL_sub]
  exact norm_le_of_abs (abs_nonneg _) fun i => by fin_cases i <;> simp

/-- Woodford (2003), Ch. 7: the date-0 root lag in deviations from the steady state of the same
economy, in its relevant components `(Δ, λ₁, λ₂)`. -/
noncomputable def d0R (p : Par) (R : RPar) (Dm1 : ℝ) : Fin 9 → ℝ :=
  ![0, 0, 0, 0, Dm1 - 1, -ramseyLam p R 0, -ramseyLam p R 1, 0, 0]

/-- Woodford (2003), Ch. 7: the date-0 conditions in levels are `PhiR = 0` in deviations from
the steady state of the same economy, with the root lag `d0R`. -/
theorem date0_iffR {Y : Type*} (T : LagTree Y) (p : Par) (R : RPar) (e : Y → Fin 5 → ℝ)
    (Dm1 : ℝ) (w : Y → Fin 9 → ℝ) :
    RamseyL T p R e (lagD0 Dm1) w ↔
      PhiR T p R e (fun _ => d0R p R Dm1) (fun y => w y - ramseySS p R) = 0 := by
  rw [ramseyL_iff, PhiR_congr_lag T p R _ (d' := fun _ => d0R p R Dm1)
    (fun y => by simp [d0R, lagD0, ramseySS])]

/-- Woodford (2003), Ch. 7: the date-0 and the timeless root lags of the same economy differ by the
steady-state multipliers of the `F`, `K` recursions, of size `|λ̄₁|`. -/
theorem norm_d0R_sub (p : Par) (R : RPar) (Dm1 : ℝ) :
    ‖d0R p R Dm1 - (lagTL p R Dm1 - ramseySS p R)‖ ≤ |ramseyLam p R 0| := by
  have h1 : ramseyLam p R 1 = -ramseyLam p R 0 := rfl
  rw [lagTL_sub]
  refine norm_le_of_abs (abs_nonneg _) fun i => ?_
  fin_cases i <;> simp [d0R, h1]

/-- Woodford (2003), Ch. 7: the size of the date-0 root lag in deviations. -/
theorem norm_d0R (p : Par) (R : RPar) (Dm1 : ℝ) :
    ‖d0R p R Dm1‖ ≤ |Dm1 - 1| + |ramseyLam p R 0| := by
  have h1 : ramseyLam p R 1 = -ramseyLam p R 0 := rfl
  refine norm_le_of_abs (by positivity) fun i => ?_
  have a1 := abs_nonneg (Dm1 - 1)
  have a2 := abs_nonneg (ramseyLam p R 0)
  fin_cases i <;> simp [d0R, h1] <;> linarith

/-- **Woodford (2003), Ch. 6, §5 and Ch. 7, §1 (the timeless plan for ANY distortion).** Let
`A_uG ≠ 0` and `max(α, z₁) < μ ≤ 1`. There are `r, δ > 0` and `C ≥ 0` such that on every event
tree, for disturbances `‖e‖ ≤ δ` and `|Δ_{−1} − 1| ≤ δ`, the timeless Ramsey conditions have a
solution within `r` of the distorted steady state `w̄(Φ)`, the only one there; without
disturbances `‖w(y) − w̄(Φ)‖ ≤ C|Δ_{−1} − 1|μ^{date(y)}` (geometric convergence to `w̄(Φ)`). -/
theorem timeless_any_Phi {p : Par} (hp : p.Std) (R : RPar) (hG : R.Au * Gw p R ≠ 0) {μ : ℝ}
    (hμα : p.α < μ) (hμz : z1 p < μ) (hμ1 : μ ≤ 1) :
    ∃ r > 0, ∃ δ > 0, ∃ C, 0 ≤ C ∧ ∀ {Y : Type*} (T : LagTree Y) (e : Y → Fin 5 → ℝ) (Dm1 : ℝ),
      (∀ y, ‖e y‖ ≤ δ) → |Dm1 - 1| ≤ δ → ∃ w : Y → Fin 9 → ℝ,
        (RamseyL T p R e (lagTL p R Dm1) w ∧ (∀ y, ‖w y - ramseySS p R‖ ≤ r) ∧
          ∀ w', RamseyL T p R e (lagTL p R Dm1) w' → (∀ y, ‖w' y - ramseySS p R‖ ≤ r) →
            w' = w) ∧
        ((∀ y, e y = 0) → ∀ y, ‖w y - ramseySS p R‖ ≤ C * |Dm1 - 1| * μ ^ T.depth y) := by
  obtain ⟨rE, hrE, δE, hδE, CE, hCE, hEx⟩ := ramsey_existence R hp hG
  obtain ⟨rS, hrS, CS, hCS, hSt⟩ := lag_stability R hp hG hμα hμz hμ1
  set r := min rE rS with hr
  have hr0 : 0 < r := lt_min hrE hrS
  obtain ⟨δc, hδc, hsmall⟩ := phiR_zero_small R hp (τ := r / (2 * CE)) (by positivity)
  set δ := min (min δE δc) (min (r / 2) (r / (2 * (CS + 1)))) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ δE := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ δc := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : δ ≤ r / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ4 : δ ≤ r / (2 * (CS + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r, hr0, δ, hδ0, CS, hCS, fun {Y} T e Dm1 he hD => ?_⟩
  set d : Y → Fin 9 → ℝ := fun _ => lagTL p R Dm1 - ramseySS p R with hd
  have hdb : ∀ y, ‖d y‖ ≤ δ := fun _ => (norm_lagTL_sub p R Dm1).trans hD
  obtain ⟨z, ⟨hzb, hz⟩, hu, hsm⟩ := hEx T e d (fun y => (he y).trans hδ1)
    (fun y => (hdb y).trans hδ1)
  have hzs := hsm (r / (2 * CE)) (by positivity) (hsmall T e d (fun y => (he y).trans hδ2)
    (fun y => (hdb y).trans hδ2))
  have hzr : ∀ y, ‖z y‖ ≤ r / 2 := fun y => (hzs y).trans (le_of_eq (by field_simp))
  refine ⟨fun y => ramseySS p R + z y, ⟨?_, fun y => ?_, fun w' hw' hw'b => ?_⟩, fun he0 y => ?_⟩
  · rw [ramseyL_iff]; simpa using hz
  · simpa using (hzr y).trans (by linarith [min_le_left rE rS])
  · have := hu (fun y => w' y - ramseySS p R) (fun y => (hw'b y).trans (min_le_left _ _))
      ((ramseyL_iff _ _ _ _ _ _).1 hw')
    funext y; rw [← congrFun this y]; abel
  · -- compare with the steady state, which solves the conditions with zero initial lag
    have hss : PhiR T p R e (fun _ => 0) (fun _ => 0) = 0 := by
      funext x
      simp only [PhiR, lagI, Mv_const' T]
      have h := Qd_Nd_zero R hp
      rw [he0 x]
      split_ifs <;> exact h
    obtain ⟨Z, hZb, hZ, hZw⟩ := hSt r hr0 (min_le_right _ _) T e d (fun _ => 0) (fun _ => 0)
      (fun y => (he y).trans (hδ3.trans (by linarith)))
      (fun y => (hdb y).trans (hδ3.trans (by linarith))) (fun _ => by simp [hr0.le])
      (fun _ => by rw [norm_zero]; positivity) hss |Dm1 - 1| (abs_nonneg _)
      (fun y => by simpa using (norm_lagTL_sub p R Dm1)) (by
        have : CS * |Dm1 - 1| ≤ CS * (r / (2 * (CS + 1))) :=
          mul_le_mul_of_nonneg_left (hD.trans hδ4) hCS
        refine this.trans ?_
        rw [show CS * (r / (2 * (CS + 1))) = r / 2 * (CS / (CS + 1)) by field_simp]
        have : CS / (CS + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        nlinarith)
    have hZz : Z = z := hu Z (fun y => (hZb y).trans (min_le_left _ _)) hZ
    have h := hZw y
    rw [hZz] at h
    simpa using h

/-- **Woodford (2003), pp. 414–415 and Ch. 7, §1 (the date-0 plan for ANY distortion whose
commitment gap is within the radius of the distorted steady state).** Let `A_uG ≠ 0` and
`max(α, z₁) < μ ≤ 1`. There are `r, δ > 0` and `C ≥ 0`, depending only on the parameters
(including `Φ`) and `μ`, such that if `|λ̄₁(Φ)| ≤ δ`, then on every event tree, for disturbances
`‖e‖ ≤ δ` and `|Δ_{−1} − 1| ≤ δ`, the date-0 plan and the timeless plan both exist within `r`
of the distorted steady state, each the only one there, and
`‖w⁰(y) − wᵀ(y)‖ ≤ C|λ̄₁(Φ)|μ^{date(y)}`. -/
theorem date0_any_Phi {p : Par} (hp : p.Std) (R : RPar) (hG : R.Au * Gw p R ≠ 0) {μ : ℝ}
    (hμα : p.α < μ) (hμz : z1 p < μ) (hμ1 : μ ≤ 1) :
    ∃ r > 0, ∃ δ > 0, ∃ C, 0 ≤ C ∧ (|ramseyLam p R 0| ≤ δ → ∀ {Y : Type*} (T : LagTree Y)
      (e : Y → Fin 5 → ℝ) (Dm1 : ℝ), (∀ y, ‖e y‖ ≤ δ) → |Dm1 - 1| ≤ δ →
        ∃ w0 wT : Y → Fin 9 → ℝ,
          (RamseyL T p R e (lagD0 Dm1) w0 ∧ (∀ y, ‖w0 y - ramseySS p R‖ ≤ r) ∧
            ∀ w', RamseyL T p R e (lagD0 Dm1) w' → (∀ y, ‖w' y - ramseySS p R‖ ≤ r) →
              w' = w0) ∧
          (RamseyL T p R e (lagTL p R Dm1) wT ∧ (∀ y, ‖wT y - ramseySS p R‖ ≤ r) ∧
            ∀ w', RamseyL T p R e (lagTL p R Dm1) w' → (∀ y, ‖w' y - ramseySS p R‖ ≤ r) →
              w' = wT) ∧
          ∀ y, ‖w0 y - wT y‖ ≤ C * |ramseyLam p R 0| * μ ^ T.depth y) := by
  obtain ⟨rE, hrE, δE, hδE, CE, hCE, hEx⟩ := ramsey_existence R hp hG
  obtain ⟨rS, hrS, CS, hCS, hSt⟩ := lag_stability R hp hG hμα hμz hμ1
  set r := min rE rS with hr
  have hr0 : 0 < r := lt_min hrE hrS
  obtain ⟨δc, hδc, hsmall⟩ := phiR_zero_small R hp (τ := r / (2 * CE)) (by positivity)
  set δ := min (min (δE / 2) (r / 4)) (min (δc / 2) (r / (2 * (CS + 1)))) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ δE / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ r / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : δ ≤ δc / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ4 : δ ≤ r / (2 * (CS + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r, hr0, δ, hδ0, CS, hCS, fun hlam {Y} T e Dm1 he hD => ?_⟩
  set lam := |ramseyLam p R 0| with hlamd
  set d0 : Y → Fin 9 → ℝ := fun _ => d0R p R Dm1 with hd0
  set dT : Y → Fin 9 → ℝ := fun _ => lagTL p R Dm1 - ramseySS p R with hdT
  have hd0b : ∀ y, ‖d0 y‖ ≤ 2 * δ := fun _ => (norm_d0R p R Dm1).trans (by linarith)
  have hdTb : ∀ y, ‖dT y‖ ≤ 2 * δ := fun _ => (norm_lagTL_sub p R Dm1).trans (by linarith)
  have exist : ∀ dd : Y → Fin 9 → ℝ, (∀ y, ‖dd y‖ ≤ 2 * δ) →
      ∃ z : Y → Fin 9 → ℝ, ((∀ y, ‖z y‖ ≤ r / 2) ∧ PhiR T p R e dd z = 0) ∧
        ∀ z' : Y → Fin 9 → ℝ, (∀ y, ‖z' y‖ ≤ r) → PhiR T p R e dd z' = 0 → z' = z := by
    intro dd hdd
    obtain ⟨z, ⟨hzb, hz⟩, huniq, hsm⟩ := hEx T e dd (fun y => (he y).trans (by linarith))
      (fun y => (hdd y).trans (by linarith))
    have hzs := hsm (r / (2 * CE)) (by positivity) (hsmall T e dd
      (fun y => (he y).trans (by linarith)) (fun y => (hdd y).trans (by linarith)))
    exact ⟨z, ⟨fun y => (hzs y).trans (le_of_eq (by field_simp)), hz⟩,
      fun z' hz'b hz' => huniq z' (fun y => (hz'b y).trans (min_le_left _ _)) hz'⟩
  obtain ⟨z0, ⟨hz0b, hz0⟩, hu0⟩ := exist d0 hd0b
  obtain ⟨zT, ⟨hzTb, hzT⟩, huT⟩ := exist dT hdTb
  obtain ⟨Z, hZb, hZ, hZw⟩ := hSt r hr0 (min_le_right _ _) T e d0 dT zT
    (fun y => (he y).trans (by linarith)) (fun y => (hd0b y).trans (by linarith))
    (fun y => (hdTb y).trans (by linarith)) hzTb hzT lam (abs_nonneg _)
    (fun _ => norm_d0R_sub p R Dm1) (by
      have : CS * lam ≤ CS * (r / (2 * (CS + 1))) :=
        mul_le_mul_of_nonneg_left (hlam.trans hδ4) hCS
      refine this.trans ?_
      rw [show CS * (r / (2 * (CS + 1))) = r / 2 * (CS / (CS + 1)) by field_simp]
      have : CS / (CS + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      nlinarith)
  have hZz0 : Z = z0 := hu0 Z hZb hZ
  refine ⟨fun y => ramseySS p R + z0 y, fun y => ramseySS p R + zT y,
    ⟨?_, fun y => ?_, fun w' hw' hw'b => ?_⟩, ⟨?_, fun y => ?_, fun w' hw' hw'b => ?_⟩,
    fun y => ?_⟩
  · rw [date0_iffR]; simpa using hz0
  · simpa using (hz0b y).trans (by linarith)
  · have := hu0 (fun y => w' y - ramseySS p R) hw'b ((date0_iffR _ _ _ _ _ _).1 hw')
    funext y; rw [← congrFun this y]; abel
  · rw [ramseyL_iff]; simpa using hzT
  · simpa using (hzTb y).trans (by linarith)
  · have := huT (fun y => w' y - ramseySS p R) hw'b ((ramseyL_iff _ _ _ _ _ _).1 hw')
    funext y; rw [← congrFun this y]; abel
  · have h := hZw y
    rw [hZz0] at h
    simpa [add_sub_add_left_eq_sub] using h

/-- Woodford (2003), §5 (**the date-0 commitment gap is homogeneous of degree one in A_u**):
`λ̄₁(sA_u, Φ) = sλ̄₁(A_u, Φ)`; with `TidyR5RamseyDate0.scale_solution` (the conditions are
homogeneous of degree one in `(A_u, multipliers)`), renormalising A_u rescales the gap and the
multiplier part of every solution together, so it cannot bring the gap inside the radius. -/
theorem lam1_scale (p : Par) (Au Φ s : ℝ) :
    ramseyLam p ⟨s * Au, Φ⟩ 0 = s * ramseyLam p ⟨Au, Φ⟩ 0 := by
  simp only [ramseyLam, Matrix.cons_val_zero]
  ring

end Woodford.StabilizationWelfare.TidyR6aLargePhi
