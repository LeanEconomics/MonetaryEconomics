/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.OptimalTaylor
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Algebra.Polynomial.Roots

/-!
# Taylor rules with coefficients of any sign

Woodford (2003), *Interest and Prices*, Chapter 7, §3.2 (pp. 513–515), footnote 33, and the
"almost all parameter values" remark of p. 515.

Footnote 33 notes that the Taylor principle (3.9) is necessary and sufficient for determinacy
only when `φ_π, φ_x ≥ 0`, and that rules with negative feedback coefficients could be allowed "as
long as they imply a determinate equilibrium". This module removes the sign restriction.

## Main results

* **The exact determinacy region for all real `(φ_π, φ_x)`** (`taylor_determinate_iff_region`):
  with `Δ = 1 + σφ_x/4 + σκφ_π`, `A = κ(φ_π − 1) + (1 − β)φ_x/4` and
  `C = 2(1 + β) + σκ(1 + φ_π) + (1 + β)σφ_x/4`, equilibrium is determinate iff
  `(β < Δ ∧ A > 0 ∧ C > 0) ∨ (Δ < −β ∧ A < 0 ∧ C < 0)`. When `Δ = 0` there is always a second
  bounded equilibrium (`not_modelDet_of_delta_zero`). For `φ_π, φ_x ≥ 0` the region is (3.9)
  (`region_iff_taylorLHS`), so this extends Prop. 4.3 / (3.9).
* Every determinate Taylor rule has an equilibrium of the form (3.6) (`taylor_eqm_plan2_region`)
  and **no determinate Taylor rule, of any sign, beats the optimal noninertial plan**
  (`prop_7_12_optimal_region`).
* **Proposition 7.12 for all real coefficients, exactly** (`oni_implementable_iff`): when the
  consistency system is nonsingular, the optimal noninertial plan is the equilibrium of some
  determinate Taylor rule iff the unique consistent coefficients `(φ_π, φ_x)(ρ_r, ρ_u)` lie in
  the region; then it is the unique equilibrium (`prop_7_12_region`).
* (3.10) is sufficient but not necessary once negative coefficients are allowed: at the fn. 32
  calibration and `ρ = .7` (outside (3.10)) the plan is implemented by a determinate rule with
  `φ_π < 0`, `φ_x < 0` (`negative_rule_implements`), while at `ρ = .9` no determinate Taylor rule
  implements it (`no_rule_implements`).
* **"Almost all parameter values"** (p. 515): for `λᵢ > 0` the set of `(ρ_r, ρ_u)` at which the
  consistency system is singular is a closed Lebesgue-null subset of `ℝ²` with empty interior,
  contained in the zero set of a polynomial that is not identically zero (`detG_zero_null`,
  `detG_zero_interior_empty`, `detG_zero_subset`); for `λᵢ = 0` the system is singular
  everywhere (`detG_li_zero`).
-/

namespace Woodford.GainsFromCommitment.TidyR5TaylorRegion

open Filter Topology MeasureTheory
open OptimalTaylor (taylorDelta taylorB taylorW TaylorEqm ModelDet taylorLHS detT pbarT xbarT
  fpiT fxT gpiT gxT taylorEqm_iff_solves modelDet_iff_of_reduction plan2_bdd_adapted plan2_of
  taylorRule_plan2 detG phiPiG phiXG rule_matches_general cramer_unique Drho phiPiStar phiXStar
  Cond310 rule_matches_f4_u rule_matches_f4_r detG_diag kappa_sigma_Drho)
open Noninertial (AS IS taylorRule Nondeg2)
open VarianceFrontier (plan2 plan2_apply)

/-! ### The determinacy region -/

/-- Woodford (2003), (3.9), p. 514 (rescaled): `A = κ(φ_π − 1) + (1 − β)φ_x/4`; (3.9) is
`A > 0` when `κ > 0`. -/
noncomputable def regA (β κ φπ φx : ℝ) : ℝ := κ * (φπ - 1) + (1 - β) * φx / 4

/-- Woodford (2003), App. C.2, p. 677 (the second Schur–Cohn inequality under (3.1)):
`C = 2(1 + β) + σκ(1 + φ_π) + (1 + β)σφ_x/4`. -/
noncomputable def regC (β σ κ φπ φx : ℝ) : ℝ :=
  2 * (1 + β) + σ * κ * (1 + φπ) + (1 + β) * σ * φx / 4

/-- Woodford (2003), fn. 33, p. 515: the determinacy region of the Taylor rule (3.1) for
coefficients of any sign, `(β < Δ ∧ A > 0 ∧ C > 0) ∨ (Δ < −β ∧ A < 0 ∧ C < 0)`. -/
def TaylorRegion (β σ κ φπ φx : ℝ) : Prop :=
  (β < taylorDelta σ κ φπ φx ∧ 0 < regA β κ φπ φx ∧ 0 < regC β σ κ φπ φx) ∨
    (taylorDelta σ κ φπ φx < -β ∧ regA β κ φπ φx < 0 ∧ regC β σ κ φπ φx < 0)

/-- Woodford (2003), eq. (2.18), p. 263: `tr B = (1 + β + σκ + βσφ_x/4)/Δ`. -/
theorem taylorB_tr (β σ κ φπ φx : ℝ) :
    tr2 (taylorB β σ κ φπ φx) = (1 + β + σ * κ + β * σ * φx / 4) / taylorDelta σ κ φπ φx := by
  simp only [taylorB, tr2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- Woodford (2003), eq. (2.18), p. 263: `det B = β/Δ` when `Δ ≠ 0`. -/
theorem taylorB_det {β σ κ φπ φx : ℝ} (hΔ : taylorDelta σ κ φπ φx ≠ 0) :
    det2 (taylorB β σ κ φπ φx) = β / taylorDelta σ κ φπ φx := by
  simp only [taylorB, det2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  field_simp
  unfold taylorDelta
  ring

/-- Woodford (2003), App. C.2, p. 677, for coefficients of any sign: when `Δ ≠ 0`, `B` satisfies
the Schur–Cohn condition iff `(φ_π, φ_x)` lies in `TaylorRegion`. -/
theorem schurStable_iff_region {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hσ : 0 < σ)
    (hΔ : taylorDelta σ κ φπ φx ≠ 0) :
    SchurStable (tr2 (taylorB β σ κ φπ φx)) (det2 (taylorB β σ κ φπ φx)) ↔
      TaylorRegion β σ κ φπ φx := by
  rw [taylorB_tr, taylorB_det hΔ]
  set Δ := taylorDelta σ κ φπ φx with hΔd
  set a := 1 + β + σ * κ + β * σ * φx / 4 with ha
  have e1 : Δ + β - a = σ * regA β κ φπ φx := by
    rw [hΔd, ha]; unfold taylorDelta regA; ring
  have e2 : Δ + β + a = regC β σ κ φπ φx := by
    rw [hΔd, ha]; unfold taylorDelta regC; ring
  unfold SchurStable TaylorRegion
  rw [← hΔd]
  rcases lt_or_gt_of_ne hΔ with hneg | hpos
  · have hD : |β / Δ| = β / -Δ := by
      rw [abs_div, abs_of_pos hβ0, abs_of_neg hneg]
    have hT : |a / Δ| = |a| / -Δ := by rw [abs_div, abs_of_neg hneg]
    have hn : 0 < -Δ := by linarith
    rw [hD, hT, div_lt_one hn,
      show 1 + β / Δ = (-Δ - β) / -Δ by field_simp; ring, div_lt_div_iff_of_pos_right hn,
      abs_lt]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine Or.inr ⟨by linarith, ?_, by linarith⟩
      have : σ * regA β κ φπ φx < 0 := by linarith
      exact neg_of_mul_neg_right this hσ.le
    · rintro (⟨h1, -, -⟩ | ⟨h1, h2, h3⟩)
      · exact absurd h1 (by linarith)
      · have : σ * regA β κ φπ φx < 0 := mul_neg_of_pos_of_neg hσ h2
        exact ⟨by linarith, by linarith, by linarith⟩
  · have hD : |β / Δ| = β / Δ := by rw [abs_of_pos (div_pos hβ0 hpos)]
    have hT : |a / Δ| = |a| / Δ := by rw [abs_div, abs_of_pos hpos]
    rw [hD, hT, div_lt_one hpos,
      show 1 + β / Δ = (Δ + β) / Δ by field_simp, div_lt_div_iff_of_pos_right hpos, abs_lt]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine Or.inl ⟨h1, ?_, by linarith⟩
      have : 0 < σ * regA β κ φπ φx := by linarith
      exact (pos_iff_pos_of_mul_pos this).mp hσ
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, -, -⟩)
      · have : 0 < σ * regA β κ φπ φx := mul_pos hσ h2
        exact ⟨h1, by linarith, by linarith⟩
      · exact absurd h1 (by linarith)

/-- Woodford (2003), fn. 33, p. 515: the region excludes `Δ = 0`. -/
theorem delta_ne_zero_of_region {β σ κ φπ φx : ℝ} (hβ0 : 0 < β)
    (h : TaylorRegion β σ κ φπ φx) : taylorDelta σ κ φπ φx ≠ 0 := by
  rcases h with ⟨h1, -, -⟩ | ⟨h1, -, -⟩ <;> intro h0 <;> rw [h0] at h1 <;> linarith

/-- Woodford (2003), (3.9), p. 514 and fn. 33: for `φ_π, φ_x ≥ 0` the region is exactly the
Taylor principle (3.9) (so `taylor_determinate_iff_region` extends Prop. 4.3). -/
theorem region_iff_taylorLHS {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    TaylorRegion β σ κ φπ φx ↔ 1 < taylorLHS β κ φπ φx := by
  have hΔ := OptimalTaylor.one_le_taylorDelta hσ hκ hφπ hφx
  have hA : regA β κ φπ φx = κ * (taylorLHS β κ φπ φx - 1) := by
    unfold regA taylorLHS; field_simp; ring
  have hC : 0 < regC β σ κ φπ φx := by
    unfold regC
    have : 0 ≤ σ * κ * (1 + φπ) := by positivity
    have : 0 ≤ (1 + β) * σ * φx / 4 := by positivity
    linarith
  unfold TaylorRegion
  rw [hA]
  constructor
  · rintro (⟨-, h, -⟩ | ⟨h, -, -⟩)
    · have := (pos_iff_pos_of_mul_pos h).mp hκ; linarith
    · linarith
  · intro h
    exact Or.inl ⟨by linarith, mul_pos hκ (by linarith), hC⟩


variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), fn. 33, p. 515 (the boundary `Δ = 0`): when `1 + σφ_x/4 + σκφ_π = 0` the
Taylor rule never implies determinacy. With `u = 0` and `rⁿ = ī − π̄` both the steady state and
the steady state perturbed by `x_0 = x̄ + 1`, `π_0 = π̄ + κ` (zero afterwards) are equilibria. -/
theorem not_modelDet_of_delta_zero [Nonempty Ω] {β σ κ φπ φx πbar xbar ibar : ℝ}
    (hxb : κ * xbar = (1 - β) * πbar) (hΔ : taylorDelta σ κ φπ φx = 0) :
    ¬ ModelDet 𝔼 (TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar) := by
  intro hdet
  have hE : ∀ t (c : ℝ) ω, 𝔼.E t (fun _ => c) ω = c := fun t c ω => by rw [𝔼.const]
  have hu : BoundedProc (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) := ⟨0, fun _ _ => by simp⟩
  have hr : BoundedProc (fun (_ : ℕ) (_ : Ω) => ibar - πbar) :=
    ⟨|ibar - πbar|, fun _ _ => le_rfl⟩
  have hau : 𝔼.Adapted (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) := fun t => 𝔼.const t 0
  have har : 𝔼.Adapted (fun (_ : ℕ) (_ : Ω) => ibar - πbar) := fun t => 𝔼.const t _
  obtain ⟨p, -, hpu⟩ := hdet _ _ hu hr hau har
  set π2 : ℕ → Ω → ℝ := fun t _ => πbar + if t = 0 then κ else 0 with hπ2
  set x2 : ℕ → Ω → ℝ := fun t _ => xbar + if t = 0 then 1 else 0 with hx2
  have hd : 1 + σ * φx / 4 + σ * κ * φπ = 0 := hΔ
  have e1 : TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar (fun _ _ => 0) (fun _ _ => ibar - πbar)
      (fun _ _ => πbar) (fun _ _ => xbar) := by
    refine ⟨(OptimalTaylor.AS_iff 𝔼 _ _ _ _ _).mpr fun t ω => ?_,
      (OptimalTaylor.IS_iff 𝔼 _ _ _ _ _).mpr fun t ω => ?_⟩
    · rw [hE]; linear_combination -hxb
    · simp only [hE, taylorRule]; ring
  have e2 : TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar (fun _ _ => 0) (fun _ _ => ibar - πbar)
      π2 x2 := by
    refine ⟨(OptimalTaylor.AS_iff 𝔼 _ _ _ _ _).mpr fun t ω => ?_,
      (OptimalTaylor.IS_iff 𝔼 _ _ _ _ _).mpr fun t ω => ?_⟩
    · simp only [hπ2, hx2, hE, Nat.add_one_ne_zero, ↓reduceIte]
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · simp only [↓reduceIte]; linear_combination -hxb
      · simp only [ht.ne', ↓reduceIte]; linear_combination -hxb
    · simp only [hπ2, hx2, hE, Nat.add_one_ne_zero, ↓reduceIte, taylorRule]
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · simp only [↓reduceIte]; linear_combination hd
      · simp only [ht.ne', ↓reduceIte]; ring
  have b2 : BoundedProc π2 := ⟨|πbar| + |κ|, fun t _ => by
    simp only [hπ2]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    split_ifs <;> simp⟩
  have c2 : BoundedProc x2 := ⟨|xbar| + 1, fun t _ => by
    simp only [hx2]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    split_ifs <;> simp⟩
  have a2 : 𝔼.Adapted π2 := fun t => 𝔼.const t _
  have d2 : 𝔼.Adapted x2 := fun t => 𝔼.const t _
  have q1 := hpu (fun _ _ => πbar, fun _ _ => xbar)
    ⟨⟨|πbar|, fun _ _ => le_rfl⟩, ⟨|xbar|, fun _ _ => le_rfl⟩, fun t => 𝔼.const t _,
      fun t => 𝔼.const t _, e1⟩
  have q2 := hpu (π2, x2) ⟨b2, c2, a2, d2, e2⟩
  have := congrArg Prod.snd (q1.trans q2.symm)
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have h0 := congrFun (congrFun this 0) ω
  simp [hx2] at h0

/-- **(3.9) for coefficients of any sign** (Woodford (2003), fn. 33, p. 515, extending Prop. 4.3
and App. C.2): under the Taylor rule (3.1) with arbitrary real `φ_π, φ_x` (`0 < β < 1`,
`σ, κ > 0`, `κ x̄ = (1 − β) π̄`), equilibrium is determinate — exactly one bounded adapted
equilibrium for every bounded adapted `(u, rⁿ)` — iff `(φ_π, φ_x) ∈ TaylorRegion`. -/
theorem taylor_determinate_iff_region [Nonempty Ω] {β σ κ φπ φx πbar xbar ibar : ℝ}
    (hβ0 : 0 < β) (hσ : 0 < σ) (hxb : κ * xbar = (1 - β) * πbar) :
    ModelDet 𝔼 (TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar) ↔ TaylorRegion β σ κ φπ φx := by
  by_cases hΔ0 : taylorDelta σ κ φπ φx = 0
  · exact ⟨fun h => absurd h (not_modelDet_of_delta_zero 𝔼 hxb hΔ0),
      fun h => absurd hΔ0 (delta_ne_zero_of_region hβ0 h)⟩
  rw [← schurStable_iff_region hβ0 hσ hΔ0]
  refine modelDet_iff_of_reduction 𝔼 (W := fun u rn => taylorW σ κ φπ φx ibar πbar u rn)
    (fun u rn π x => taylorEqm_iff_solves 𝔼 hxb hΔ0 u rn π x) ?_ ?_
  · intro u rn hu hrn hau harn
    obtain ⟨M₁, hM₁⟩ := hu
    obtain ⟨M₂, hM₂⟩ := hrn
    set Δ := taylorDelta σ κ φπ φx
    have hΔp : 0 < |Δ| := abs_pos.mpr hΔ0
    refine ⟨⟨(|κ * σ| * (M₂ + |ibar| + |πbar|) + |1 + σ * φx / 4| * M₁ +
        |σ| * (M₂ + |ibar| + |πbar|) + |σ * φπ| * M₁) / |Δ|, fun t i ω => ?_⟩, fun t i => ?_⟩
    · have he : |rn t ω - ibar + πbar| ≤ M₂ + |ibar| + |πbar| := by
        calc |rn t ω - ibar + πbar| ≤ |rn t ω - ibar| + |πbar| := abs_add_le _ _
          _ ≤ |rn t ω| + |ibar| + |πbar| := by gcongr; exact abs_sub _ _
          _ ≤ M₂ + |ibar| + |πbar| := by gcongr; exact hM₂ t ω
      have hu' := hM₁ t ω
      have a1 : |κ * σ * (rn t ω - ibar + πbar)| ≤ |κ * σ| * (M₂ + |ibar| + |πbar|) := by
        rw [abs_mul]; gcongr
      have a2 : |(1 + σ * φx / 4) * u t ω| ≤ |1 + σ * φx / 4| * M₁ := by rw [abs_mul]; gcongr
      have a3 : |σ * (rn t ω - ibar + πbar)| ≤ |σ| * (M₂ + |ibar| + |πbar|) := by
        rw [abs_mul]; gcongr
      have a4 : |σ * φπ * u t ω| ≤ |σ * φπ| * M₁ := by rw [abs_mul]; gcongr
      have p1 : 0 ≤ |κ * σ| * (M₂ + |ibar| + |πbar|) := (abs_nonneg _).trans a1
      have p2 : 0 ≤ |(1 + σ * φx / 4)| * M₁ := (abs_nonneg _).trans a2
      have p3 : 0 ≤ |σ| * (M₂ + |ibar| + |πbar|) := (abs_nonneg _).trans a3
      have p4 : 0 ≤ |σ * φπ| * M₁ := (abs_nonneg _).trans a4
      fin_cases i
      · simp only [taylorW, Fin.zero_eta, Matrix.cons_val_zero]
        rw [abs_div]
        gcongr
        exact (abs_add_le _ _).trans (by linarith)
      · simp only [taylorW, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [abs_div]
        gcongr
        exact (abs_sub _ _).trans (by linarith)
    · have e0 : (fun ω => (κ * σ * (rn t ω - ibar + πbar) + (1 + σ * φx / 4) * u t ω) / Δ) =
          (κ * σ / Δ) • rn t + (fun _ => κ * σ * (πbar - ibar) / Δ) +
            ((1 + σ * φx / 4) / Δ) • u t := by
        funext ω; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      have e1 : (fun ω => (σ * (rn t ω - ibar + πbar) - σ * φπ * u t ω) / Δ) =
          (σ / Δ) • rn t + (fun _ => σ * (πbar - ibar) / Δ) + (-(σ * φπ) / Δ) • u t := by
        funext ω; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      fin_cases i
      · simp only [taylorW, Fin.zero_eta, Matrix.cons_val_zero]
        rw [e0, map_add, map_add, map_smul, map_smul, 𝔼.const, harn t, hau t]
      · simp only [taylorW, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [e1, map_add, map_add, map_smul, map_smul, 𝔼.const, harn t, hau t]
  · refine ⟨fun _ _ => 0, fun _ _ => ibar - πbar, ⟨0, fun _ _ => by simp⟩,
      ⟨|ibar - πbar|, fun _ _ => le_rfl⟩, fun t => 𝔼.const t 0, fun t => 𝔼.const t _, ?_⟩
    funext t i ω
    fin_cases i <;> simp [taylorW]


/-! ### Equilibrium of the form (3.6) under any determinate Taylor rule -/

omit 𝔼 in
/-- Woodford (2003), App. C.1, p. 670 (tool): under the Schur–Cohn condition `|D| < 1`,
`|T| < 1 + D`, the polynomial `1 − Tρ + Dρ²` (that is, `det(I − ρK)`) is positive on `|ρ| ≤ 1`. -/
theorem one_sub_mul_add_pos {T D ρ : ℝ} (h : SchurStable T D) (hρ : |ρ| ≤ 1) :
    0 < 1 - T * ρ + D * ρ ^ 2 := by
  obtain ⟨hD, hT⟩ := h
  have hD' := abs_lt.mp hD
  have h1 : T * ρ ≤ |T| * |ρ| := (le_abs_self _).trans (abs_mul T ρ).le
  have hsq : ρ ^ 2 = |ρ| ^ 2 := (sq_abs ρ).symm
  rcases eq_or_lt_of_le (abs_nonneg ρ) with h0 | hpos
  · have : ρ = 0 := abs_eq_zero.mp h0.symm
    subst this; norm_num
  · have h2 : |T| * |ρ| < (1 + D) * |ρ| := mul_lt_mul_of_pos_right hT hpos
    have h3 : 0 ≤ (1 - |ρ|) * (1 - D * |ρ|) := by
      apply mul_nonneg (by linarith)
      nlinarith [abs_nonneg ρ]
    nlinarith

omit 𝔼 in
/-- Woodford (2003), p. 514: the determinant of the response system is
`detT(ρ) = Δ · (1 − ρ tr B + ρ² det B) = Δ det(I − ρB)`. -/
theorem detT_eq {β σ κ φπ φx : ℝ} (hΔ : taylorDelta σ κ φπ φx ≠ 0) (ρ : ℝ) :
    detT β κ σ φπ φx ρ = taylorDelta σ κ φπ φx *
      (1 - tr2 (taylorB β σ κ φπ φx) * ρ + det2 (taylorB β σ κ φπ φx) * ρ ^ 2) := by
  rw [taylorB_tr, taylorB_det hΔ]
  field_simp
  unfold detT taylorDelta
  ring

omit 𝔼 in
/-- Woodford (2003), p. 514, for coefficients of any sign: under a determinate Taylor rule the
response system is nonsingular for every `|ρ| ≤ 1`. -/
theorem detT_ne_zero_of_region {β σ κ φπ φx ρ : ℝ} (hβ0 : 0 < β) (hσ : 0 < σ)
    (h : TaylorRegion β σ κ φπ φx) (hρ : |ρ| ≤ 1) : detT β κ σ φπ φx ρ ≠ 0 := by
  have hΔ := delta_ne_zero_of_region hβ0 h
  rw [detT_eq hΔ]
  exact mul_ne_zero hΔ (one_sub_mul_add_pos ((schurStable_iff_region hβ0 hσ hΔ).mpr h) hρ).ne'

omit 𝔼 in
/-- Woodford (2003), p. 514: in the region `A ≠ 0`, so the long-run values `OptimalTaylor.pbarT`,
`OptimalTaylor.xbarT` are well defined. -/
theorem regA_ne_zero_of_region {β σ κ φπ φx : ℝ} (h : TaylorRegion β σ κ φπ φx) :
    regA β κ φπ φx ≠ 0 := by
  rcases h with ⟨-, h, -⟩ | ⟨-, h, -⟩
  · exact h.ne'
  · exact h.ne

/-- Woodford (2003), p. 514, for coefficients of any sign: if the response systems at `ρ_u`, `ρ_r`
are nonsingular and `A ≠ 0`, the plan (3.6) with coefficients `OptimalTaylor.pbarT`,
`OptimalTaylor.fpiT`, `OptimalTaylor.gpiT`, … is an equilibrium under the Taylor rule. -/
theorem taylor_eqm_plan2_of_ne {β σ κ φπ φx πbar xbar ibar rbar ρu ρr : ℝ}
    (hxb : κ * xbar = (1 - β) * πbar) (hdu' : detT β κ σ φπ φx ρu ≠ 0)
    (hdr' : detT β κ σ φπ φx ρr ≠ 0) (hC' : regA β κ φπ φx ≠ 0) {u r : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρu u) (hr : 𝔼.IsAR1 ρr r) :
    TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar u (fun t ω => rbar + r t ω)
      (plan2 (pbarT β κ φπ φx rbar ibar πbar) (fpiT β κ σ φπ φx ρu) (gpiT β κ σ φπ φx ρr) u r)
      (plan2 (xbarT β κ φπ φx rbar ibar πbar xbar) (fxT β κ σ φπ φx ρu) (gxT β κ σ φπ φx ρr)
        u r) := by
  have hC'' : κ * (φπ - 1) + (1 - β) * φx / 4 ≠ 0 := hC'
  unfold TaylorEqm
  rw [taylorRule_plan2]
  refine plan2_of 𝔼 hu hr ?_ ?_ ?_ ?_ ?_ ?_
  · unfold pbarT xbarT; linear_combination -hxb
  · have hinv : (κ * (φπ - 1) + (1 - β) * φx / 4) * (κ * (φπ - 1) + (1 - β) * φx / 4)⁻¹ = 1 :=
      mul_inv_cancel₀ hC''
    unfold pbarT xbarT
    simp only [div_eq_mul_inv]
    linear_combination (rbar + πbar - ibar) * hinv
  · have hinv := mul_inv_cancel₀ hdu'
    have hdef : detT β κ σ φπ φx ρu =
        (1 - β * ρu) * ((1 - ρu) + σ * φx / 4) + κ * σ * (φπ - ρu) := rfl
    unfold fpiT fxT
    simp only [div_eq_mul_inv]
    linear_combination hinv - (detT β κ σ φπ φx ρu)⁻¹ * hdef
  · unfold fpiT fxT
    simp only [div_eq_mul_inv]
    ring
  · unfold gpiT gxT; field_simp
  · have hinv := mul_inv_cancel₀ hdr'
    have hdef : detT β κ σ φπ φx ρr =
        (1 - β * ρr) * ((1 - ρr) + σ * φx / 4) + κ * σ * (φπ - ρr) := rfl
    unfold gpiT gxT
    simp only [div_eq_mul_inv]
    linear_combination σ * hinv - σ * (detT β κ σ φπ φx ρr)⁻¹ * hdef

/-- Woodford (2003), p. 514 ("this equilibrium is one in which the equilibrium values … depend only
on the current disturbances"), for coefficients of any sign: under every determinate Taylor rule
and AR(1) disturbances with `|ρ_u|, |ρ_r| ≤ 1`, the plan (3.6) with the explicit coefficients is
an equilibrium. -/
theorem taylor_eqm_plan2_region {β σ κ φπ φx πbar xbar ibar rbar ρu ρr : ℝ} (hβ0 : 0 < β)
    (hσ : 0 < σ) (hreg : TaylorRegion β σ κ φπ φx) (hxb : κ * xbar = (1 - β) * πbar)
    (hρu : |ρu| ≤ 1) (hρr : |ρr| ≤ 1) {u r : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρu u)
    (hr : 𝔼.IsAR1 ρr r) :
    TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar u (fun t ω => rbar + r t ω)
      (plan2 (pbarT β κ φπ φx rbar ibar πbar) (fpiT β κ σ φπ φx ρu) (gpiT β κ σ φπ φx ρr) u r)
      (plan2 (xbarT β κ φπ φx rbar ibar πbar xbar) (fxT β κ σ φπ φx ρu) (gxT β κ σ φπ φx ρr)
        u r) :=
  taylor_eqm_plan2_of_ne 𝔼 hxb (detT_ne_zero_of_region hβ0 hσ hreg hρu)
    (detT_ne_zero_of_region hβ0 hσ hreg hρr) (regA_ne_zero_of_region hreg) hu hr

/-- **Proposition 7.12, optimality, for coefficients of any sign** (Woodford (2003), p. 514 and
fn. 33, p. 515): with independent AR(1) disturbances (`|ρ_u|, |ρ_r| < 1`, innovation variances
`s_u, s_r > 0`, non-degenerate as a pair) and the pull-out property, every bounded adapted
equilibrium under every determinate Taylor rule — `φ_π`, `φ_x` of any sign — has a stabilization
loss at least that of the optimal noninertial plan. -/
theorem prop_7_12_optimal_region (hpo : 𝔼.PullOut) {β κ σ rbar lx li istar ρr ρu su sr : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 ≤ li)
    (hρr : |ρr| < 1) (hρu : |ρu| < 1) (hsu : 0 < su) (hsr : 0 < sr)
    {u εu r εr : ℕ → Ω → ℝ}
    (hu : Noninertial.AR1Innov 𝔼 ρu su u εu) (hr : Noninertial.AR1Innov 𝔼 ρr sr r εr)
    (hind : ∀ t, 𝔼.E t (εu (t + 1) * εr (t + 1)) = fun _ => 0) (hnd : Nondeg2 u r)
    (hub : BoundedProc u) (hrb : BoundedProc r) (t₀ : ℕ) (ω : Ω) {xs is : ℝ}
    (hxs : xs = (1 - β) / κ * Noninertial.piBar119 β li rbar istar)
    (his : is = rbar + Noninertial.piBar119 β li rbar istar)
    {ibar φπ φx πbar xbar : ℝ} (hdet : ModelDet 𝔼 (TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar))
    (hxb : κ * xbar = (1 - β) * πbar) {π x : ℕ → Ω → ℝ} (hπb : BoundedProc π)
    (hxbd : BoundedProc x) (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x)
    (heq : TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar u (fun t ω => rbar + r t ω) π x) :
    Noninertial.Lstab 𝔼 β lx li t₀
        (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
          (Noninertial.piRF4 β κ σ lx li ρr) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r)
        (plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr) u r) ω ≤
      Noninertial.Lstab 𝔼 β lx li t₀ π x (taylorRule ibar φπ φx πbar xbar π x) ω := by
  have hrn : BoundedProc (fun t ω => rbar + r t ω) := by
    obtain ⟨N, hN⟩ := hrb
    exact ⟨|rbar| + N, fun t ω => (abs_add_le _ _).trans (add_le_add le_rfl (hN t ω))⟩
  have hrna : 𝔼.Adapted (fun t ω => rbar + r t ω) := by
    intro t
    change 𝔼.E t (fun ω => rbar + r t ω) = fun ω => rbar + r t ω
    have e : (fun ω => rbar + r t ω) = (fun _ => rbar) + r t := rfl
    rw [e, map_add, 𝔼.const, hr.1 t]
  have : Nonempty Ω := ⟨ω⟩
  have hreg := (taylor_determinate_iff_region 𝔼 hβ0 hσ hxb).mp hdet
  have hplan := taylor_eqm_plan2_region 𝔼 (rbar := rbar) (ibar := ibar) hβ0 hσ hreg hxb
    hρu.le hρr.le hu.isAR1 hr.isAR1
  obtain ⟨b1, a1⟩ := plan2_bdd_adapted 𝔼 hub hrb hu.1 hr.1 (pbarT β κ φπ φx rbar ibar πbar)
    (fpiT β κ σ φπ φx ρu) (gpiT β κ σ φπ φx ρr)
  obtain ⟨b2, a2⟩ := plan2_bdd_adapted 𝔼 hub hrb hu.1 hr.1
    (xbarT β κ φπ φx rbar ibar πbar xbar) (fxT β κ σ φπ φx ρu) (gxT β κ σ φπ φx ρr)
  obtain ⟨p, -, hpu⟩ := hdet u _ hub hrn hu.1 hrna
  have e1 := hpu (π, x) ⟨hπb, hxbd, hπa, hxa, heq⟩
  have e2 := hpu (plan2 (pbarT β κ φπ φx rbar ibar πbar) (fpiT β κ σ φπ φx ρu)
    (gpiT β κ σ φπ φx ρr) u r, plan2 (xbarT β κ φπ φx rbar ibar πbar xbar) (fxT β κ σ φπ φx ρu)
    (gxT β κ σ φπ φx ρr) u r) ⟨b1, b2, a1, a2, hplan⟩
  have hpx := e1.trans e2.symm
  simp only [Prod.mk.injEq] at hpx
  obtain ⟨rfl, rfl⟩ := hpx
  rw [taylorRule_plan2]
  have hAI := hplan
  unfold TaylorEqm at hAI
  rw [taylorRule_plan2] at hAI
  exact ((Noninertial.f4_lstab 𝔼 hpo hβ0 hβ1 hκ hσ hlx hli hρu hρr hsu hsr hu hr hind hnd t₀
    ω hxs his).2 _ _ _ _ _ _ _ _ _ hAI.1 hAI.2).1


/-! ### Proposition 7.12 for coefficients of any sign, exactly -/

omit 𝔼 in
/-- Woodford (2003), eq. (3.1), p. 507 (tool): only `ī − φ_π π̄ − φ_x x̄/4` matters; the rule
is the same as the rule centred at `(0, 0)` with that intercept. -/
theorem taylorRule_recenter {Ω' : Type*} (ibar φπ φx πbar xbar : ℝ) (π x : ℕ → Ω' → ℝ) :
    taylorRule ibar φπ φx πbar xbar π x =
      taylorRule (ibar - φπ * πbar - φx * xbar / 4) φπ φx 0 0 π x := by
  funext t ω
  simp only [taylorRule]
  ring

/-- Woodford (2003), fn. 33, p. 515: the determinacy region for a Taylor rule with arbitrary
intercepts (no restriction linking `x̄` to `π̄`). -/
theorem taylor_determinate_iff_region_any [Nonempty Ω] {β σ κ φπ φx πbar xbar ibar : ℝ}
    (hβ0 : 0 < β) (hσ : 0 < σ) :
    ModelDet 𝔼 (TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar) ↔ TaylorRegion β σ κ φπ φx := by
  have e : TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar =
      TaylorEqm 𝔼 β σ κ (ibar - φπ * πbar - φx * xbar / 4) φπ φx 0 0 := by
    funext u rn π x
    unfold TaylorEqm
    rw [taylorRule_recenter]
  rw [e]
  exact taylor_determinate_iff_region 𝔼 hβ0 hσ (by ring)

/-- **Proposition 7.12 for coefficients of any sign** (Woodford (2003), p. 514 and fn. 33,
p. 515): at `(ρ_r, ρ_u)` where the consistency system is nonsingular, with bounded AR(1)
disturbances, if `(φ_π, φ_x)(ρ_r, ρ_u)` lies in `TaylorRegion` then the Taylor rule with those
coefficients and intercepts (3.11) reproduces the optimal noninertial plan's interest rate,
equilibrium is determinate, and the plan is the unique bounded adapted equilibrium. -/
theorem prop_7_12_region [Nonempty Ω] {β κ σ rbar lx li istar ρr ρu : ℝ} (hβ0 : 0 < β)
    (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 ≤ lx) (hli : 0 ≤ li)
    (hd : detG β κ σ lx li (ρr, ρu) ≠ 0)
    (hreg : TaylorRegion β σ κ (phiPiG β κ σ lx li (ρr, ρu)) (phiXG β κ σ lx li (ρr, ρu)))
    {u r : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρu u)
    (hr : 𝔼.IsAR1 ρr r) (hub : BoundedProc u) (hrb : BoundedProc r) {xs is : ℝ}
    (hxs : xs = (1 - β) / κ * Noninertial.piBar119 β li rbar istar)
    (his : is = rbar + Noninertial.piBar119 β li rbar istar) :
    plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr) u r =
      taylorRule is (phiPiG β κ σ lx li (ρr, ρu)) (phiXG β κ σ lx li (ρr, ρu))
        (Noninertial.piBar119 β li rbar istar) xs
        (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
          (Noninertial.piRF4 β κ σ lx li ρr) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r) ∧
    ModelDet 𝔼 (TaylorEqm 𝔼 β σ κ is (phiPiG β κ σ lx li (ρr, ρu))
      (phiXG β κ σ lx li (ρr, ρu)) (Noninertial.piBar119 β li rbar istar) xs) ∧
    ∀ π x : ℕ → Ω → ℝ, BoundedProc π → BoundedProc x → 𝔼.Adapted π → 𝔼.Adapted x →
      (TaylorEqm 𝔼 β σ κ is (phiPiG β κ σ lx li (ρr, ρu)) (phiXG β κ σ lx li (ρr, ρu))
        (Noninertial.piBar119 β li rbar istar) xs u (fun t ω => rbar + r t ω) π x ↔
      π = plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
        (Noninertial.piRF4 β κ σ lx li ρr) u r ∧
      x = plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r) := by
  obtain ⟨m1, m2⟩ := rule_matches_general hd
  set πs := Noninertial.piBar119 β li rbar istar
  have hxb : κ * xs = (1 - β) * πs := by rw [hxs]; field_simp
  have hrule : plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr) u r =
      taylorRule is (phiPiG β κ σ lx li (ρr, ρu)) (phiXG β κ σ lx li (ρr, ρu)) πs xs
        (plan2 πs (Noninertial.piUF4 β κ σ lx li ρu) (Noninertial.piRF4 β κ σ lx li ρr) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r) := by
    rw [taylorRule_plan2]
    simp only at m1 m2
    rw [m1, m2]
    congr 1 <;> ring
  have heq : TaylorEqm 𝔼 β σ κ is (phiPiG β κ σ lx li (ρr, ρu)) (phiXG β κ σ lx li (ρr, ρu))
      πs xs u (fun t ω => rbar + r t ω)
      (plan2 πs (Noninertial.piUF4 β κ σ lx li ρu) (Noninertial.piRF4 β κ σ lx li ρr) u r)
      (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r) := by
    obtain ⟨c1, c2⟩ := Noninertial.f4_u_feasible (β := β) (ρ := ρu) hκ hσ hlx hli
    obtain ⟨c3, c4⟩ := Noninertial.f4_r_feasible (β := β) (ρ := ρr) hκ hσ hlx hli
    unfold TaylorEqm
    rw [← hrule]
    exact plan2_of 𝔼 hu hr (by linarith [hxb]) his c1 c2 c3 c4
  have hdet := (taylor_determinate_iff_region 𝔼 (ibar := is) hβ0 hσ hxb).mpr hreg
  refine ⟨hrule, hdet, fun π x hπb hxb' hπa hxa => ⟨fun hπx => ?_, ?_⟩⟩
  · have hrn : BoundedProc (fun t ω => rbar + r t ω) := by
      obtain ⟨N, hN⟩ := hrb
      exact ⟨|rbar| + N, fun t ω => (abs_add_le _ _).trans (add_le_add le_rfl (hN t ω))⟩
    have hrna : 𝔼.Adapted (fun t ω => rbar + r t ω) := by
      intro t
      change 𝔼.E t (fun ω => rbar + r t ω) = fun ω => rbar + r t ω
      have e : (fun ω => rbar + r t ω) = (fun _ => rbar) + r t := rfl
      rw [e, map_add, 𝔼.const, hr.1 t]
    obtain ⟨p, -, hpu⟩ := hdet u (fun t ω => rbar + r t ω) hub hrn hu.1 hrna
    obtain ⟨b1, a1⟩ := plan2_bdd_adapted 𝔼 hub hrb hu.1 hr.1 πs (Noninertial.piUF4 β κ σ lx li ρu)
      (Noninertial.piRF4 β κ σ lx li ρr)
    obtain ⟨b2, a2⟩ := plan2_bdd_adapted 𝔼 hub hrb hu.1 hr.1 xs (Noninertial.xUF4 β κ σ lx li ρu)
      (Noninertial.xRF4 β κ σ lx li ρr)
    have e1 := hpu (π, x) ⟨hπb, hxb', hπa, hxa, hπx⟩
    have e2 := hpu (_, _) ⟨b1, b2, a1, a2, heq⟩
    have := e1.trans e2.symm
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  · rintro ⟨rfl, rfl⟩
    exact heq

/-- **Proposition 7.12 for coefficients of any sign, exact form** (Woodford (2003), pp. 514–515
and fn. 33): at `(ρ_r, ρ_u)` where the consistency system is nonsingular, with bounded AR(1)
disturbances that are non-degenerate as a pair, the optimal noninertial plan is an equilibrium of
some Taylor rule (3.1) (any intercepts, any real coefficients) that implies a determinate
equilibrium **iff** the unique consistent coefficients `(φ_π, φ_x)(ρ_r, ρ_u)` lie in
`TaylorRegion`. -/
theorem oni_implementable_iff [Nonempty Ω] {β κ σ rbar lx li istar ρr ρu : ℝ} (hβ0 : 0 < β)
    (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 ≤ lx) (hli : 0 ≤ li)
    (hd : detG β κ σ lx li (ρr, ρu) ≠ 0) {u r : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρu u)
    (hr : 𝔼.IsAR1 ρr r) (hub : BoundedProc u) (hrb : BoundedProc r) (hnd : Nondeg2 u r)
    {xs is : ℝ} (hxs : xs = (1 - β) / κ * Noninertial.piBar119 β li rbar istar)
    (his : is = rbar + Noninertial.piBar119 β li rbar istar) :
    (∃ ibar φπ φx πbar xbar : ℝ, ModelDet 𝔼 (TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar) ∧
      TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar u (fun t ω => rbar + r t ω)
        (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
          (Noninertial.piRF4 β κ σ lx li ρr) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r)) ↔
      TaylorRegion β σ κ (phiPiG β κ σ lx li (ρr, ρu)) (phiXG β κ σ lx li (ρr, ρu)) := by
  constructor
  · rintro ⟨ibar, φπ, φx, πbar, xbar, hdet, heq⟩
    have hreg := (taylor_determinate_iff_region_any 𝔼 hβ0 hσ).mp hdet
    set πs := Noninertial.piBar119 β li rbar istar
    obtain ⟨c1, c2⟩ := Noninertial.f4_u_feasible (β := β) (ρ := ρu) hκ hσ hlx hli
    obtain ⟨c3, c4⟩ := Noninertial.f4_r_feasible (β := β) (ρ := ρr) hκ hσ hlx hli
    have hxb : κ * xs = (1 - β) * πs := by rw [hxs]; field_simp
    have hO := plan2_of 𝔼 (rbar := rbar) (πbar := πs) (xbar := xs) hu hr (by linarith [hxb]) his
      c1 c2 c3 c4
    have hI1 := (OptimalTaylor.IS_iff 𝔼 _ _ _ _ _).mp heq.2
    have hI2 := (OptimalTaylor.IS_iff 𝔼 _ _ _ _ _).mp hO.2
    have hi : ∀ t ω, taylorRule ibar φπ φx πbar xbar
        (plan2 πs (Noninertial.piUF4 β κ σ lx li ρu) (Noninertial.piRF4 β κ σ lx li ρr) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r) t ω =
        plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr) u r t ω := by
      intro t ω
      have h := (hI1 t ω).symm.trans (hI2 t ω)
      have : σ * (taylorRule ibar φπ φx πbar xbar
          (plan2 πs (Noninertial.piUF4 β κ σ lx li ρu) (Noninertial.piRF4 β κ σ lx li ρr) u r)
          (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r) t ω -
          plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr) u r t ω)
          = 0 := by linarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hσ.ne')
    rw [taylorRule_plan2] at hi
    obtain ⟨-, k1, k2⟩ := Noninertial.affine_zero2 hnd
      (a := ibar + φπ * (πs - πbar) + φx * (xs - xbar) / 4 - is)
      (b := φπ * Noninertial.piUF4 β κ σ lx li ρu + φx * Noninertial.xUF4 β κ σ lx li ρu / 4 -
        Noninertial.iUF4 β κ σ lx li ρu)
      (c := φπ * Noninertial.piRF4 β κ σ lx li ρr + φx * Noninertial.xRF4 β κ σ lx li ρr / 4 -
        Noninertial.iRF4 β κ σ lx li ρr) (fun t ω => by
          have h := hi t ω
          simp only [plan2_apply] at h
          linear_combination h)
    have hd' : Noninertial.piUF4 β κ σ lx li ρu * Noninertial.xRF4 β κ σ lx li ρr -
        Noninertial.xUF4 β κ σ lx li ρu * Noninertial.piRF4 β κ σ lx li ρr ≠ 0 := hd
    obtain ⟨q1, q2⟩ := cramer_unique (x := φπ) (y := φx / 4)
      (c1 := Noninertial.iUF4 β κ σ lx li ρu) (c2 := Noninertial.iRF4 β κ σ lx li ρr) hd'
      (by linear_combination -k1) (by linear_combination -k2)
    have hπ : φπ = phiPiG β κ σ lx li (ρr, ρu) := q1
    have hx : φx = phiXG β κ σ lx li (ρr, ρu) := by
      have e4 : φx = 4 * (φx / 4) := by ring
      rw [e4, q2]
      rfl
    rw [← hπ, ← hx]
    exact hreg
  · intro hreg
    obtain ⟨-, hdet, hall⟩ := prop_7_12_region 𝔼 hβ0 hκ hσ hlx hli hd hreg hu hr hub hrb hxs his
    obtain ⟨b1, a1⟩ := plan2_bdd_adapted 𝔼 hub hrb hu.1 hr.1 (Noninertial.piBar119 β li rbar istar)
      (Noninertial.piUF4 β κ σ lx li ρu) (Noninertial.piRF4 β κ σ lx li ρr)
    obtain ⟨b2, a2⟩ := plan2_bdd_adapted 𝔼 hub hrb hu.1 hr.1 xs
      (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr)
    exact ⟨_, _, _, _, _, hdet, (hall _ _ b1 b2 a1 a2).mpr ⟨rfl, rfl⟩⟩


/-! ### The diagonal `ρ_r = ρ_u = ρ`: (3.10) is sufficient but not necessary -/

omit 𝔼 in
/-- Woodford (2003), (3.12), p. 514: on the diagonal, whenever `D(ρ) λᵢ ≠ 0` (of either sign) the
consistency system is nonsingular and its solution is (3.12). -/
theorem phiG_diag_ne {β κ σ lx li ρ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 ≤ lx) (hli : 0 ≤ li)
    (hD : Drho β κ σ ρ * li ≠ 0) :
    detG β κ σ lx li (ρ, ρ) ≠ 0 ∧ phiPiG β κ σ lx li (ρ, ρ) = phiPiStar β κ σ li ρ ∧
      phiXG β κ σ lx li (ρ, ρ) = phiXStar β κ σ lx li ρ := by
  have hh := Noninertial.hF4_pos (β := β) (σ := σ) (ρ := ρ) hκ.ne' hlx hli
  have hli' : li ≠ 0 := right_ne_zero_of_mul hD
  have hG : Noninertial.gamF4 β ρ - ρ * κ * σ ≠ 0 := by
    rw [← kappa_sigma_Drho hκ.ne' hσ.ne']
    exact mul_ne_zero (mul_ne_zero hκ.ne' hσ.ne') (left_ne_zero_of_mul hD)
  have hd : detG β κ σ lx li (ρ, ρ) ≠ 0 := by
    rw [detG_diag hκ hσ hlx hli]
    have : σ⁻¹ ≠ 0 := inv_ne_zero hσ.ne'
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hli' this) hG) hh.ne'
  obtain ⟨e1, e2⟩ := cramer_unique (x := phiPiStar β κ σ li ρ) (y := phiXStar β κ σ lx li ρ / 4)
    hd (rule_matches_f4_u hκ hσ hlx hli hD) (rule_matches_f4_r hκ hσ hlx hli hD)
  refine ⟨hd, ?_, ?_⟩
  · unfold phiPiG; rw [e1]; rfl
  · have e4 : phiXStar β κ σ lx li ρ = 4 * (phiXStar β κ σ lx li ρ / 4) := by ring
    rw [e4, e2]
    rfl

/-- **Proposition 7.12 on the diagonal, exact, any sign** (Woodford (2003), pp. 514–515, fn. 33):
with a common `ρ` and `D(ρ) λᵢ ≠ 0`, the optimal noninertial plan is the equilibrium of some
determinate Taylor rule iff the coefficients (3.12) lie in `TaylorRegion`. -/
theorem oni_implementable_diag_iff [Nonempty Ω] {β κ σ rbar lx li istar ρ : ℝ} (hβ0 : 0 < β)
    (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 ≤ lx) (hli : 0 ≤ li) (hD : Drho β κ σ ρ * li ≠ 0)
    {u r : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hr : 𝔼.IsAR1 ρ r) (hub : BoundedProc u)
    (hrb : BoundedProc r) (hnd : Nondeg2 u r) {xs is : ℝ}
    (hxs : xs = (1 - β) / κ * Noninertial.piBar119 β li rbar istar)
    (his : is = rbar + Noninertial.piBar119 β li rbar istar) :
    (∃ ibar φπ φx πbar xbar : ℝ, ModelDet 𝔼 (TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar) ∧
      TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar u (fun t ω => rbar + r t ω)
        (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρ)
          (Noninertial.piRF4 β κ σ lx li ρ) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρ) (Noninertial.xRF4 β κ σ lx li ρ) u r)) ↔
      TaylorRegion β σ κ (phiPiStar β κ σ li ρ) (phiXStar β κ σ lx li ρ) := by
  obtain ⟨hd, e1, e2⟩ := phiG_diag_ne (β := β) hκ hσ hlx hli hD
  rw [← e1, ← e2]
  exact oni_implementable_iff 𝔼 hβ0 hκ hσ hlx hli hd hu hr hub hrb hnd hxs his

omit 𝔼 in
/-- Woodford (2003), fn. 32–33, p. 515: at the fn. 32 calibration (`β = .99`, `κ = .024`,
`σ = 6.25`, `λₓ = .003`, `λᵢ = .236`) and `ρ = .7` — outside the interval `(.17, .68)` where
(3.10) holds — (3.10) fails, yet the coefficients (3.12) (`φ_π ≈ −49.3`, `φ_x ≈ −7.6`, both
negative) lie in `TaylorRegion` (`Δ ≈ −18.2 < −β`, `A < 0`, `C < 0`). -/
theorem negative_rule_region :
    ¬ Cond310 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) (7 / 10) ∧
      Drho (99 / 100) (24 / 1000) (625 / 100) (7 / 10) * (236 / 1000) ≠ 0 ∧
      phiPiStar (99 / 100) (24 / 1000) (625 / 100) (236 / 1000) (7 / 10) < 0 ∧
      phiXStar (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) (7 / 10) < 0 ∧
      TaylorRegion (99 / 100) (625 / 100) (24 / 1000)
        (phiPiStar (99 / 100) (24 / 1000) (625 / 100) (236 / 1000) (7 / 10))
        (phiXStar (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) (7 / 10)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold Cond310 Drho; norm_num
  · unfold Drho; norm_num
  · unfold phiPiStar Drho; norm_num
  · unfold phiXStar phiPiStar Drho; norm_num
  · refine Or.inr ⟨?_, ?_, ?_⟩ <;>
    · simp only [taylorDelta, regA, regC, phiXStar, phiPiStar, Drho]; norm_num

omit 𝔼 in
/-- Woodford (2003), fn. 32–33, p. 515: at the same calibration and `ρ = .9`, `D(ρ) λᵢ ≠ 0` but
the coefficients (3.12) are not in `TaylorRegion` (`Δ ≈ −.204`, between `−β` and `β`). -/
theorem no_rule_region :
    Drho (99 / 100) (24 / 1000) (625 / 100) (9 / 10) * (236 / 1000) ≠ 0 ∧
      ¬ TaylorRegion (99 / 100) (625 / 100) (24 / 1000)
        (phiPiStar (99 / 100) (24 / 1000) (625 / 100) (236 / 1000) (9 / 10))
        (phiXStar (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) (9 / 10)) := by
  refine ⟨?_, ?_⟩
  · unfold Drho; norm_num
  · unfold TaylorRegion taylorDelta regA regC phiXStar phiPiStar Drho
    norm_num

/-- **Correction to the reading of Prop. 7.12 / (3.10)** (Woodford (2003), pp. 514–515, fn. 32–33):
at the fn. 32 calibration and `ρ = .7`, where (3.10) fails, the optimal noninertial plan is
nevertheless the equilibrium of a determinate Taylor rule — one with negative coefficients. -/
theorem negative_rule_implements [Nonempty Ω] {rbar istar : ℝ} {u r : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 (7 / 10) u) (hr : 𝔼.IsAR1 (7 / 10) r) (hub : BoundedProc u)
    (hrb : BoundedProc r) {xs is : ℝ}
    (hxs : xs = (1 - 99 / 100) / (24 / 1000) *
      Noninertial.piBar119 (99 / 100) (236 / 1000) rbar istar)
    (his : is = rbar + Noninertial.piBar119 (99 / 100) (236 / 1000) rbar istar) :
    ¬ Cond310 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) (7 / 10) ∧
    ∃ ibar φπ φx πbar xbar : ℝ, φπ < 0 ∧ φx < 0 ∧
      ModelDet 𝔼 (TaylorEqm 𝔼 (99 / 100) (625 / 100) (24 / 1000) ibar φπ φx πbar xbar) ∧
      TaylorEqm 𝔼 (99 / 100) (625 / 100) (24 / 1000) ibar φπ φx πbar xbar u
        (fun t ω => rbar + r t ω)
        (plan2 (Noninertial.piBar119 (99 / 100) (236 / 1000) rbar istar)
          (Noninertial.piUF4 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) (7 / 10))
          (Noninertial.piRF4 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) (7 / 10))
          u r)
        (plan2 xs
          (Noninertial.xUF4 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) (7 / 10))
          (Noninertial.xRF4 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) (7 / 10))
          u r) := by
  obtain ⟨h310, hD, hπ, hx, hreg⟩ := negative_rule_region
  refine ⟨h310, ?_⟩
  have hκ : (0 : ℝ) < 24 / 1000 := by norm_num
  have hσ : (0 : ℝ) < 625 / 100 := by norm_num
  have hlx : (0 : ℝ) ≤ 3 / 1000 := by norm_num
  have hli : (0 : ℝ) ≤ 236 / 1000 := by norm_num
  obtain ⟨hd, e1, e2⟩ := phiG_diag_ne (β := 99 / 100) hκ hσ hlx hli hD
  have hreg' := hreg
  rw [← e1, ← e2] at hreg'
  obtain ⟨-, hdet, hall⟩ := prop_7_12_region 𝔼 (by norm_num) hκ hσ hlx hli hd hreg' hu hr hub hrb
    hxs his
  obtain ⟨b1, a1⟩ := plan2_bdd_adapted 𝔼 hub hrb hu.1 hr.1
    (Noninertial.piBar119 (99 / 100) (236 / 1000) rbar istar)
    (Noninertial.piUF4 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) (7 / 10))
    (Noninertial.piRF4 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) (7 / 10))
  obtain ⟨b2, a2⟩ := plan2_bdd_adapted 𝔼 hub hrb hu.1 hr.1 xs
    (Noninertial.xUF4 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) (7 / 10))
    (Noninertial.xRF4 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) (7 / 10))
  refine ⟨_, _, _, _, _, ?_, ?_, hdet, (hall _ _ b1 b2 a1 a2).mpr ⟨rfl, rfl⟩⟩
  · rw [e1]; exact hπ
  · rw [e2]; exact hx

/-- Woodford (2003), fn. 32–33, p. 515: at the fn. 32 calibration and `ρ = .9` no Taylor rule of
any sign both implies determinacy and has the optimal noninertial plan as an equilibrium. -/
theorem no_rule_implements [Nonempty Ω] {rbar istar : ℝ} {u r : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 (9 / 10) u) (hr : 𝔼.IsAR1 (9 / 10) r) (hub : BoundedProc u)
    (hrb : BoundedProc r) (hnd : Nondeg2 u r) {xs is : ℝ}
    (hxs : xs = (1 - 99 / 100) / (24 / 1000) *
      Noninertial.piBar119 (99 / 100) (236 / 1000) rbar istar)
    (his : is = rbar + Noninertial.piBar119 (99 / 100) (236 / 1000) rbar istar) :
    ¬ ∃ ibar φπ φx πbar xbar : ℝ,
      ModelDet 𝔼 (TaylorEqm 𝔼 (99 / 100) (625 / 100) (24 / 1000) ibar φπ φx πbar xbar) ∧
      TaylorEqm 𝔼 (99 / 100) (625 / 100) (24 / 1000) ibar φπ φx πbar xbar u
        (fun t ω => rbar + r t ω)
        (plan2 (Noninertial.piBar119 (99 / 100) (236 / 1000) rbar istar)
          (Noninertial.piUF4 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) (9 / 10))
          (Noninertial.piRF4 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) (9 / 10))
          u r)
        (plan2 xs
          (Noninertial.xUF4 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) (9 / 10))
          (Noninertial.xRF4 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) (9 / 10))
          u r) := by
  obtain ⟨hD, hnot⟩ := no_rule_region
  rw [oni_implementable_diag_iff 𝔼 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hD hu hr hub hrb hnd hxs his]
  exact hnot

/-! ### "Almost all parameter values" (p. 515) -/

omit 𝔼 in
/-- Woodford (2003), App. F.4, p. 713: `γ − ρκσ = βρ² − (1 + β + κσ)ρ + 1` as a polynomial. -/
noncomputable def polyG (β κ σ : ℝ) : Polynomial ℝ :=
  Polynomial.C β * Polynomial.X ^ 2 + Polynomial.C (-(1 + β + κ * σ)) * Polynomial.X + 1

omit 𝔼 in
/-- Woodford (2003), App. F.4, p. 713: the numerator of `π_u`,
`A(ρ) = λᵢσ⁻²(γ − ρκσ)(1 − ρ) + λₓ(1 − βρ)`, as a polynomial. -/
noncomputable def polyA (β κ σ lx li : ℝ) : Polynomial ℝ :=
  Polynomial.C (li * σ⁻¹ ^ 2) * polyG β κ σ * (1 - Polynomial.X) +
    Polynomial.C lx * (1 - Polynomial.C β * Polynomial.X)

omit 𝔼 in
/-- Woodford (2003), App. F.4, p. 713: `B(ρ) = κ² − κρλᵢσ⁻¹(γ − ρκσ)` (`−κ` times the numerator
of `x_u`). -/
noncomputable def polyB (β κ σ li : ℝ) : Polynomial ℝ :=
  Polynomial.C (κ ^ 2) - Polynomial.C (κ * li * σ⁻¹) * Polynomial.X * polyG β κ σ

omit 𝔼 in
/-- Woodford (2003), p. 515: the polynomial function whose zero set is the singular set,
`F(ρ_r, ρ_u) = λᵢσ⁻¹ G(ρ_r) (A(ρ_u)(1 − βρ_r) + B(ρ_u))`. -/
noncomputable def detGpoly (β κ σ lx li : ℝ) (p : ℝ × ℝ) : ℝ :=
  li * σ⁻¹ * (polyG β κ σ).eval p.1 *
    ((polyA β κ σ lx li).eval p.2 * (1 - β * p.1) + (polyB β κ σ li).eval p.2)

omit 𝔼 in
/-- Woodford (2003), App. F.4, p. 713: `G(ρ) = γ − ρκσ`. -/
theorem polyG_eval (β κ σ ρ : ℝ) :
    (polyG β κ σ).eval ρ = Noninertial.gamF4 β ρ - ρ * κ * σ := by
  simp only [polyG, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_one]
  unfold Noninertial.gamF4
  ring

omit 𝔼 in
/-- Woodford (2003), p. 515: `detG = F / (h_r h_u)`, so `OptimalTaylor.detG` vanishes exactly on the
zero set of the polynomial function `F` (`κ ≠ 0`, `λₓ, λᵢ ≥ 0`). -/
theorem detG_eq_poly {β κ σ lx li : ℝ} (hκ : κ ≠ 0) (hlx : 0 ≤ lx) (hli : 0 ≤ li) (p : ℝ × ℝ) :
    detG β κ σ lx li p = detGpoly β κ σ lx li p /
      (Noninertial.hF4 β κ σ lx li p.1 * Noninertial.hF4 β κ σ lx li p.2) := by
  have h1 := (Noninertial.hF4_pos (β := β) (σ := σ) (ρ := p.1) hκ hlx hli).ne'
  have h2 := (Noninertial.hF4_pos (β := β) (σ := σ) (ρ := p.2) hκ hlx hli).ne'
  rw [eq_div_iff (mul_ne_zero h1 h2)]
  unfold detG detGpoly
  simp only [polyA, polyB, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, polyG_eval]
  unfold Noninertial.piUF4 Noninertial.xRF4 Noninertial.xUF4 Noninertial.piRF4 Noninertial.xiF4
  field_simp
  ring

omit 𝔼 in
/-- Woodford (2003), p. 515 ("certain functions of the model parameters must be nonzero"): the
singular set is the zero set of the polynomial function `detGpoly`. -/
theorem detG_zero_subset {β κ σ lx li : ℝ} (hκ : κ ≠ 0) (hlx : 0 ≤ lx) (hli : 0 ≤ li) :
    {p : ℝ × ℝ | detG β κ σ lx li p = 0} = {p | detGpoly β κ σ lx li p = 0} := by
  ext p
  simp only [Set.mem_ofPred_eq, detG_eq_poly hκ hlx hli p]
  have h1 := (Noninertial.hF4_pos (β := β) (σ := σ) (ρ := p.1) hκ hlx hli).ne'
  have h2 := (Noninertial.hF4_pos (β := β) (σ := σ) (ρ := p.2) hκ hlx hli).ne'
  rw [div_eq_zero_iff]
  exact ⟨fun h => h.resolve_right (mul_ne_zero h1 h2), Or.inl⟩

omit 𝔼 in
/-- Woodford (2003), p. 515 (a *proper* algebraic set): for `λᵢ > 0`, `σ > 0` the polynomial
function is not identically zero: `F(0, 0) = λᵢσ⁻¹(λᵢσ⁻² + λₓ + κ²) > 0`. -/
theorem detGpoly_zero_zero_pos {β κ σ lx li : ℝ} (hσ : 0 < σ) (hlx : 0 ≤ lx) (hli : 0 < li) :
    0 < detGpoly β κ σ lx li (0, 0) := by
  unfold detGpoly
  simp only [polyA, polyB, polyG, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_pow]
  have : 0 < σ⁻¹ := inv_pos.mpr hσ
  norm_num
  positivity

omit 𝔼 in
/-- Woodford (2003), p. 515: with `λᵢ = 0` the system is singular for every `(ρ_r, ρ_u)` (the
responses to `r̂ⁿ` of inflation and the output gap vanish), so `λᵢ > 0` is needed. -/
theorem detG_li_zero (β κ σ lx : ℝ) (p : ℝ × ℝ) : detG β κ σ lx 0 p = 0 := by
  unfold detG Noninertial.piRF4 Noninertial.xRF4
  simp

omit 𝔼 in
/-- Woodford (2003), p. 515 (tool): `G` is a nonzero polynomial. -/
theorem polyG_ne_zero (β κ σ : ℝ) : polyG β κ σ ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 0) h
  simp [polyG] at this

omit 𝔼 in
/-- Woodford (2003), p. 515 (tool): `A` is a nonzero polynomial when `λᵢ > 0`. -/
theorem polyA_ne_zero {β κ σ lx li : ℝ} (hσ : 0 < σ) (hlx : 0 ≤ lx) (hli : 0 < li) :
    polyA β κ σ lx li ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 0) h
  simp only [polyA, polyG, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_pow,
    Polynomial.eval_zero] at this
  have : 0 < σ⁻¹ := inv_pos.mpr hσ
  nlinarith [sq_nonneg σ⁻¹, mul_pos hli (pow_pos this 2)]

omit 𝔼 in
/-- Woodford (2003), p. 515 (tool): `OptimalTaylor.detG` is continuous on `ℝ²`. -/
theorem detG_continuous {β κ σ lx li : ℝ} (hκ : 0 < κ) (hlx : 0 ≤ lx) (hli : 0 ≤ li) :
    Continuous (detG β κ σ lx li) := by
  obtain ⟨c1, c2, -, c4, c5, -⟩ := OptimalTaylor.f4_continuous (β := β) (σ := σ) hκ hlx hli
  unfold detG
  exact ((c1.comp continuous_snd).mul (c5.comp continuous_fst)).sub
    ((c2.comp continuous_snd).mul (c4.comp continuous_fst))

omit 𝔼 in
/-- **"Almost all possible parameter values"** (Woodford (2003), p. 515): for `β ≠ 0`, `κ, σ > 0`,
`λₓ ≥ 0`, `λᵢ > 0`, the set of `(ρ_r, ρ_u) ∈ ℝ²` at which the consistency system for
`(φ_π, φ_x)` is singular has Lebesgue measure zero. -/
theorem detG_zero_null {β κ σ lx li : ℝ} (hβ : β ≠ 0) (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 ≤ lx)
    (hli : 0 < li) : volume {p : ℝ × ℝ | detG β κ σ lx li p = 0} = 0 := by
  set S := {p : ℝ × ℝ | detG β κ σ lx li p = 0} with hS
  have hmeas : MeasurableSet S :=
    (isClosed_eq (detG_continuous hκ hlx hli.le) continuous_const).measurableSet
  have hAfin := Polynomial.finite_setOfPred_isRoot (polyA_ne_zero (β := β) (κ := κ) hσ hlx hli)
  have hGfin := Polynomial.finite_setOfPred_isRoot (polyG_ne_zero β κ σ)
  have hae : ∀ᵐ y : ℝ, (polyA β κ σ lx li).eval y ≠ 0 := by
    rw [ae_iff]
    simpa [Polynomial.IsRoot] using hAfin.measure_zero volume
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hmeas]
  refine (lintegral_congr_ae (hae.mono fun y hy => ?_)).trans lintegral_zero
  set a := (polyA β κ σ lx li).eval y
  set b := (polyB β κ σ li).eval y
  have hsub : (fun x => (x, y)) ⁻¹' S ⊆
      {x | (polyG β κ σ).IsRoot x} ∪ {(a + b) / (a * β)} := by
    intro x hx
    simp only [Set.mem_preimage, hS, Set.mem_ofPred_eq] at hx
    rw [detG_eq_poly hκ.ne' hlx hli.le, div_eq_zero_iff] at hx
    have h1 := (Noninertial.hF4_pos (β := β) (σ := σ) (ρ := x) hκ.ne' hlx hli.le).ne'
    have h2 := (Noninertial.hF4_pos (β := β) (σ := σ) (ρ := y) hκ.ne' hlx hli.le).ne'
    have hx' := hx.resolve_right (mul_ne_zero h1 h2)
    unfold detGpoly at hx'
    simp only at hx'
    rcases mul_eq_zero.mp hx' with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' (mul_ne_zero hli.ne' (inv_ne_zero hσ.ne'))
      · exact Or.inl h'
    · right
      rw [Set.mem_singleton_iff, eq_div_iff (mul_ne_zero hy hβ)]
      linear_combination -h
  exact measure_mono_null hsub (measure_union_null (hGfin.measure_zero volume)
    (measure_singleton _))

omit 𝔼 in
/-- Woodford (2003), p. 515 ("this excludes only certain extremely special parameter values"):
the singular set is closed with empty interior, so the set where `(φ_π, φ_x)(ρ_r, ρ_u)` exists is
open and dense in `ℝ²`. -/
theorem detG_zero_interior_empty {β κ σ lx li : ℝ} (hβ : β ≠ 0) (hκ : 0 < κ) (hσ : 0 < σ)
    (hlx : 0 ≤ lx) (hli : 0 < li) :
    IsClosed {p : ℝ × ℝ | detG β κ σ lx li p = 0} ∧
      interior {p : ℝ × ℝ | detG β κ σ lx li p = 0} = ∅ ∧
      Dense {p : ℝ × ℝ | detG β κ σ lx li p ≠ 0} := by
  have hc : IsClosed {p : ℝ × ℝ | detG β κ σ lx li p = 0} :=
    isClosed_eq (detG_continuous hκ hlx hli.le) continuous_const
  have hi := Measure.interior_eq_empty_of_null (μ := volume)
    (detG_zero_null (β := β) (lx := lx) hβ hκ hσ hlx hli)
  refine ⟨hc, hi, ?_⟩
  have : {p : ℝ × ℝ | detG β κ σ lx li p ≠ 0} = {p | detG β κ σ lx li p = 0}ᶜ := rfl
  rw [this, ← interior_eq_empty_iff_dense_compl]
  exact hi

end Woodford.GainsFromCommitment.TidyR5TaylorRegion
