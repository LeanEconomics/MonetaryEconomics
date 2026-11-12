/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR6bGovRamseyTree

/-!
# Existence and uniqueness of the timeless Ramsey equilibrium with government purchases

Woodford (2003), *Interest and Prices*, Chapter 6, §5 (Assumption 6.2 with `s_C < 1`), Chapter 7,
§1–2, and Appendix A.3.

* **`LG_QdG`**: the linearised operator of the smooth conditions with purchases is
  `TidyR6bGovRamseyTree.LRX` with `γ = γ_G`.
* **`invBound_gov`**: under the root condition `TidyR6bGovRamseyTree.RootOK` for `γ = γ_G`
  (`H = A_uG − γ_G ≠ 0` and `κθ_X > 0` or `κθ_X < −2(1+β)`, `θ_X = A_uGθ/H`), the inverse
  `TidyR6bGovRamseyTree.LinvRX` is uniformly bounded, a right inverse and injective on every event
  tree.
* `PhiTrue`: the TRUE Ramsey conditions with purchases on an event tree
  (`TidyR6bGovRamsey.ramseyQG`, consumption
  `Y − G` with `Real.log`).
* **`gov_ramsey_existence`**: if `s_C > 0` and the root condition holds, there are `r, δ > 0`
  such that on
  EVERY event tree, for all disturbances (including purchases `Ĝ`) and predetermined initial
  lags with `‖e‖, ‖d‖ ≤ δ`, the true Ramsey conditions have a solution within `r`, and it is the
  only one within `r`.
* `rootOK_iff`: the root condition is `A_uG·H > 0` (one root in `(0, 1)`) or `H ≠ 0` with
  `κθ_X < −2(1+β)` (one root in `(−1, 0)`, oscillating); for `s_C = 1` it is `A_uG ≠ 0` on the
  admissible range, the hypothesis of the `s_C = 1` results.
* `Hy_pos_iff`, `Hy_eq_of_sC_one`, `Hy_eq_of_Phi_zero`, **`Hy_neg_case`**: `H > 0` is
  `Φσ(1 − s_C) < s_C(σ + ω)G`; it holds without purchases or without distortion, but FAILS for
  admissible parameters (`σ = 2`, `ω = 0`, `Φ = 1/2`, `s_C = 1/5`: `H = −A_u/2`), so the root
  condition of the `s_C = 1` model does not carry over to every `s_C < 1`.
-/

namespace Woodford.StabilizationWelfare.TidyR6bGovRamseyIFT

universe u

open Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovGeneral NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyLin
open NonlinearNKMarkovRamseyTree NonlinearNKMarkovRamseyIFT TidyR6bGovRamsey TidyR6bGovRamseyTree
open TidyR6bRamseyNewton

/-- Woodford (2003), §5 and App. A.3 (**the linearised operator with purchases**). -/
theorem LG_QdG {p : Par} (R : RPar) (hp : p.Std) {sC : ℝ} (hs : 0 < sC) {X : Type*}
    (T : LagTree X) (v : X → Fin 9 → ℝ) (x : X) :
    LG T (QdG p R sC) (Nd p R) v x = LRX T p R (gamG p R sC) v x := by
  simp only [LG, LRX, fderiv_QdG R hp hs, fderiv_Nd]

/-- Woodford (2003), Ch. 7 and App. A.3 (**the three properties of the inverse with purchases**):
under the root condition, `TidyR6bGovRamseyTree.LinvRX` with `γ = γ_G` is a uniformly bounded
right inverse of the
linearised
operator, and that operator is injective on bounded processes, on every event tree. -/
theorem invBound_gov {p : Par} (R : RPar) (hp : p.Std) {sC : ℝ} (hs : 0 < sC)
    (hpos : RootOK p R (gamG p R sC)) :
    InvBound (QdG p R sC) (Nd p R)
      (fun {Y : Type u} (T : LagTree Y) r => LinvRX T p R (gamG p R sC) r) := by
  obtain ⟨K, hK0, hK⟩ := LinvRX_bound R hp (gamG p R sC) hpos
  refine ⟨⟨K, hK0, fun T r A hA hr y => hK T r A hA hr y⟩, fun T r A hA hr => ?_,
    fun T v B hB h0 => ?_⟩
  · funext x
    rw [LG_QdG R hp hs]
    exact congrFun (LRX_LinvRX T R hp (gamG p R sC) hpos r A hA hr) x
  · refine LRX_inj T R hp (gamG p R sC) hpos v B hB ?_
    funext x
    rw [← LG_QdG R hp hs]
    exact congrFun h0 x

/-- Woodford (2003), §5 and Ch. 7 (**the true Ramsey conditions with purchases on an event
tree**), in deviations `z = w − w̄`, with disturbances `e = (ν, ĉ, τ̂, q, μ̂ʷ, Ĝ)` and initial
lag `d`. -/
noncomputable def PhiTrue {X : Type*} (T : LagTree X) (p : Par) (R : RPar) (sC : ℝ)
    (e : X → Fin 6 → ℝ) (d z : X → Fin 9 → ℝ) (x : X) : Fin 9 → ℝ :=
  ramseyQG p R sC (e x) (ramseySS p R + lagI T z d x) (ramseySS p R + z x) +
    Mv T.M (fun y => ramseyN p (ramseySS p R + z y)) x

/-- Woodford (2003), App. A.3: within `s_C/4` the smooth and the true conditions coincide. -/
theorem PhiTrue_eq {X : Type*} (T : LagTree X) {p : Par} (R : RPar) {sC : ℝ} (hs : 0 < sC)
    {e : X → Fin 6 → ℝ} {d z : X → Fin 9 → ℝ} (he : ∀ y, ‖e y‖ ≤ sC / 4)
    (hz : ∀ y, ‖z y‖ ≤ sC / 4) : PhiTrue T p R sC e d z = PhiG T (QdG p R sC) (Nd p R) e d z := by
  funext x
  have hy : |z x 0| ≤ sC / 4 := by
    have := (norm_le_pi_norm (z x) 0).trans (hz x); rwa [Real.norm_eq_abs] at this
  have hg : |e x 5| ≤ sC / 4 := by
    have := (norm_le_pi_norm (e x) 5).trans (he x); rwa [Real.norm_eq_abs] at this
  simp only [PhiTrue, PhiG, Nd]
  rw [QdG_eq (q := (e x, lagI T z d x, z x)) R hs hy hg]

/-- **Woodford (2003), Ch. 6, §5 and Ch. 7, §1–2 (EXISTENCE AND UNIQUENESS of the timeless Ramsey
equilibrium with government purchases, on every event tree).** If `s_C > 0` and the root
condition `TidyR6bGovRamseyTree.RootOK` holds for `γ = γ_G` (in particular whenever `A_uG·H > 0`,
`H = A_uG − γ_G`),
there are `r, δ > 0` such that on every event tree, for all disturbances
`e = (ν, ĉ, τ̂, q, μ̂ʷ, Ĝ)` and predetermined initial lags `d` with `‖e‖, ‖d‖ ≤ δ`, the TRUE
Ramsey conditions with consumption `Y − G` have a solution with `‖z‖ ≤ r`, and every solution
with `‖z′‖ ≤ r` equals it. -/
theorem gov_ramsey_existence {p : Par} (R : RPar) (hp : p.Std) {sC : ℝ} (hs : 0 < sC)
    (hpos : RootOK p R (gamG p R sC)) :
    ∃ r > 0, ∃ δ > 0, ∀ {Y : Type u} (T : LagTree Y) (e : Y → Fin 6 → ℝ) (d : Y → Fin 9 → ℝ),
      (∀ y, ‖e y‖ ≤ δ) → (∀ y, ‖d y‖ ≤ δ) →
        ∃ z : Y → Fin 9 → ℝ, ((∀ y, ‖z y‖ ≤ r) ∧ PhiTrue T p R sC e d z = 0) ∧
          ∀ z' : Y → Fin 9 → ℝ, (∀ y, ‖z' y‖ ≤ r) → PhiTrue T p R sC e d z' = 0 → z' = z := by
  have hQ : ContDiff ℝ 1 (QdG p R sC) := contDiff_QdG p R sC
  obtain ⟨r0, hr0, δ0, hδ0, C, hC, hN⟩ := newton_tree.{u} hQ (contDiff_Nd p R)
    (QdG_Nd_zero R hp hs) (invBound_gov R hp hs hpos)
  set τ0 := sC / 4 / C with hτ0
  have hτ0p : 0 < τ0 := by positivity
  obtain ⟨δQ, hδQ, hQc⟩ := Metric.continuousAt_iff.1 (hQ.continuous.continuousAt (x := 0))
    τ0 hτ0p
  set r := min r0 (sC / 4) with hr
  have hrp : 0 < r := lt_min hr0 (by positivity)
  refine ⟨r, hrp, min δ0 (min (δQ / 2) (sC / 4)), lt_min hδ0 (lt_min (by positivity)
    (by positivity)), fun {Y} T e d he hd => ?_⟩
  have he0 : ∀ y, ‖e y‖ ≤ δ0 := fun y => (he y).trans (min_le_left _ _)
  have hd0 : ∀ y, ‖d y‖ ≤ δ0 := fun y => (hd y).trans (min_le_left _ _)
  have heS : ∀ y, ‖e y‖ ≤ sC / 4 :=
    fun y => (he y).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨z, ⟨hzB, hz0⟩, huniq, hsmall, -⟩ := hN T e d he0 hd0
  -- the residual at zero is small
  have hb : ∀ y, ‖PhiG T (QdG p R sC) (Nd p R) e d (fun _ => 0) y‖ ≤ τ0 := fun y => by
    have e1 : PhiG T (QdG p R sC) (Nd p R) e d (fun _ => 0) y =
        QdG p R sC (e y, lagI T (fun _ => 0) d y, 0) - QdG p R sC 0 := by
      simp only [PhiG, Mv_const T.markov]
      rw [eq_neg_of_add_eq_zero_right (QdG_Nd_zero R hp hs)]
      abel
    rw [e1, ← dist_eq_norm]
    refine (hQc ?_).le
    rw [dist_zero_right, Prod.norm_def, Prod.norm_def]
    have hl : ‖lagI T (fun _ => (0 : Fin 9 → ℝ)) d y‖ ≤ δQ / 2 := by
      unfold lagI; split_ifs
      · exact (hd y).trans ((min_le_right _ _).trans (min_le_left _ _))
      · rw [norm_zero]; positivity
    have h0' : ‖(0 : Fin 9 → ℝ)‖ ≤ δQ / 2 := by rw [norm_zero]; positivity
    exact lt_of_le_of_lt (max_le ((he y).trans ((min_le_right _ _).trans (min_le_left _ _)))
      (max_le hl h0')) (by linarith)
  have hzS : ∀ y, ‖z y‖ ≤ sC / 4 := fun y => by
    have := hsmall τ0 hτ0p.le hb y
    rwa [hτ0, mul_div_cancel₀ _ hC.ne'] at this
  refine ⟨z, ⟨fun y => le_min (hzB y) (hzS y), ?_⟩, fun z' hz'B hz' => ?_⟩
  · rw [PhiTrue_eq T R hs heS hzS]; exact hz0
  · have hz'S : ∀ y, ‖z' y‖ ≤ sC / 4 := fun y => (hz'B y).trans (min_le_right _ _)
    refine huniq z' (fun y => (hz'B y).trans (min_le_left _ _)) ?_
    rw [← PhiTrue_eq T R hs heS hz'S]; exact hz'

/-! ## When is the output weight positive? -/

/-- Woodford (2003), §5: for `A_u > 0`, `H > 0` iff `Φσ(1 − s_C) < s_C(σ + ω)G`. -/
theorem Hy_pos_iff {p : Par} (R : RPar) (hp : p.Std) {sC : ℝ} (hs : 0 < sC) (hAu : 0 < R.Au) :
    0 < Hy p R sC ↔ R.Φ * p.σ * (1 - sC) < sC * (p.σ + p.ω) * Gw p R := by
  have hωσ : 0 < p.σ + p.ω := by linarith [hp.ω_nonneg, hp.σ_pos]
  have e : Hy p R sC = R.Au / (sC * (p.σ + p.ω)) *
      (sC * (p.σ + p.ω) * Gw p R - R.Φ * p.σ * (1 - sC)) := by
    simp only [Hy, gamG_eq R hp hs]; field_simp
  rw [e]
  constructor
  · intro h
    have hk : 0 < R.Au / (sC * (p.σ + p.ω)) := by positivity
    have := (pos_iff_pos_of_mul_pos h).1 hk
    linarith [(mul_pos_iff_of_pos_left hk).1 h]
  · intro h
    exact mul_pos (by positivity) (by linarith)

/-- Woodford (2003), §5: without purchases (`s_C = 1`) the weight is `A_uG`. -/
theorem Hy_eq_of_sC_one {p : Par} (R : RPar) : Hy p R 1 = R.Au * Gw p R := by
  simp [Hy, gamG]

/-- Woodford (2003), §5: without distortion (`Φ = 0`) the weight is `A_uG`. -/
theorem Hy_eq_of_Phi_zero {p : Par} (R : RPar) (hp : p.Std) {sC : ℝ} (hs : 0 < sC)
    (hΦ : R.Φ = 0) : Hy p R sC = R.Au * Gw p R := by
  simp [Hy, gamG_eq R hp hs, hΦ]

/-- Woodford (2003), §5 (**the root condition can fail with purchases**): with `σ = 2`, `ω = 0`,
`A_u = 1`, `Φ = 1/2` (an admissible distortion) and `s_C = 1/5`, `A_uG = 3/2 > 0` but
`H = −1/2 < 0`. -/
theorem Hy_neg_case {α β θ φ φy : ℝ} (hab : 1 - α * β ≠ 0) :
    (⟨1, 1 / 2⟩ : RPar).Au * Gw ⟨α, β, θ, 0, 2, φ, φy⟩ ⟨1, 1 / 2⟩ = 3 / 2 ∧
      Hy ⟨α, β, θ, 0, 2, φ, φy⟩ ⟨1, 1 / 2⟩ (1 / 5) = -1 / 2 := by
  constructor
  · simp only [Gw]; norm_num
  · simp only [Hy, gamG, Gw, ramseyLam, Matrix.cons_val]
    field_simp
    ring


/-- Woodford (2003), Ch. 7, (1.20): the root condition is `A_uG·H > 0` or (`H ≠ 0` and
`κθ_X < −2(1+β)`). -/
theorem rootOK_iff {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ) :
    RootOK p R γ ↔ 0 < R.Au * Gw p R * (R.Au * Gw p R - γ) ∨
      (R.Au * Gw p R - γ ≠ 0 ∧ p.κ * thX p R γ < -(2 * (1 + p.β))) := by
  constructor
  · rintro ⟨hH, hc | hc⟩
    · left
      have ht : 0 < thX p R γ := (pos_iff_pos_of_mul_pos hc).1 hp.κ_pos
      have hθ := lt_trans one_pos hp.one_lt_θ
      have e : R.Au * Gw p R * (R.Au * Gw p R - γ) =
          thX p R γ * (R.Au * Gw p R - γ) ^ 2 / p.θ := by
        unfold thX; field_simp
      rw [e]; exact div_pos (mul_pos ht (by positivity)) hθ
    · exact Or.inr ⟨hH, hc⟩
  · rintro (h | ⟨hH, hc⟩)
    · exact rootOK_of_pos R hp h
    · exact ⟨hH, Or.inr hc⟩

/-- Woodford (2003), Ch. 7: the oscillating case occurs for admissible parameters: with
`α = β = 1/2`, `θ = 2`, `ω = 0`, `σ = 2`, `A_u = 1`, `Φ = 1/2`, `s_C = 1/5`, `H = −1/2` and
`κθ_X = −9 < −2(1+β) = −3`, so `TidyR6bGovRamseyTree.RootOK` holds with an oscillating stable
root. -/
theorem oscillating_case (φ φy : ℝ) :
    (⟨1 / 2, 1 / 2, 2, 0, 2, φ, φy⟩ : Par).κ * thX ⟨1 / 2, 1 / 2, 2, 0, 2, φ, φy⟩ ⟨1, 1 / 2⟩
      (gamG ⟨1 / 2, 1 / 2, 2, 0, 2, φ, φy⟩ ⟨1, 1 / 2⟩ (1 / 5)) = -9 := by
  simp only [Par.κ, Moments.calvoKappa, thX, gamG, ramseyLam, Gw, Matrix.cons_val]
  norm_num

/-- Woodford (2003), Ch. 7 (**a case the root condition excludes**): with `α = 9/10` and the other
parameters of `oscillating_case`, `κθ_X = −11/15 ∈ (−2(1+β), 0) = (−3, 0)`: both roots of
`βz² − (1+β+κθ_X)z + 1` lie outside the unit circle, and the linearised Ramsey system with
purchases has no stable root. -/
theorem excluded_case (φ φy : ℝ) :
    (⟨9 / 10, 1 / 2, 2, 0, 2, φ, φy⟩ : Par).κ * thX ⟨9 / 10, 1 / 2, 2, 0, 2, φ, φy⟩ ⟨1, 1 / 2⟩
      (gamG ⟨9 / 10, 1 / 2, 2, 0, 2, φ, φy⟩ ⟨1, 1 / 2⟩ (1 / 5)) = -11 / 15 := by
  simp only [Par.κ, Moments.calvoKappa, thX, gamG, ramseyLam, Gw, Matrix.cons_val]
  norm_num

end Woodford.StabilizationWelfare.TidyR6bGovRamseyIFT
