/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.OptimalPolicy
import KeynesianStickyPrices.FiscalUnderpinnings

/-!
# Determinacy in the three-equation model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.5.2 "Determinacy",
eqs. (17.29)–(17.33), pp. 420–421; Online Appendix A1, §1.13.1, eqs. (1.55)–(1.58),
pp. 586–587; Chapter 16, p. 369, and Chapter 12, p. 328 ("φ > 1 is neither necessary nor
sufficient").

## Generic structural systems

A two-variable system `P x_t = Q E_t x_{t+1}` (`StructSolves`) is *determinate* when its only
bounded adapted solution is zero (`StructDeterminate`). For an arbitrary expectation system
(with `Ω` nonempty), `structDeterminate_iff`: determinate iff `det P ≠ 0` and `A = P⁻¹Q`
satisfies the Schur–Cohn condition (both eigenvalues inside the unit circle — both eigenvalues
of the transition matrix `A⁻¹` of `E_t x_{t+1} = A⁻¹ x_t` explosive). If `det P = 0` there is a
one-period self-fulfilling blip (`not_determinate_of_det_zero`). The proof uses the core
`ExpectationSystem.system_unique` / `system_not_unique` (Galí's `TaylorRuleSystem` pattern).

## The deviation system (17.29)–(17.32), with an output response

Deviations from an equilibrium follow `ĩ = r̃ + E π̃'`, `x̃ = E x̃' − σ r̃`,
`π̃ = β E π̃' + κ x̃`, `ĩ = φ π̃ + φ_x x̃` (`Deviation`; (17.32) is `φ_x = 0`). With
`D = 1 + σφ_x + σκφ` and `T = 1 + β + σκ + βσφ_x`:

* `determinate_iff` / `determinate_iff_explicit`: determinate iff `D ≠ 0` and
  `SchurStable (T/D) (β/D)`, i.e. `(D > 0 ∧ β < D ∧ |T| < D + β) ∨ (D < 0 ∧ β < −D ∧ |T| < −D − β)`.
* `determinate_iff_phi` (A1 p. 587 and (1.58)): for `φ_x = 0`, `σ, κ > 0`, `0 < β < 1`,
  determinate iff `φ > 1` or `φ < −(1 + 2(1 + β)/(σκ))`.
* `determinate_iff_BM`: for `φ, φ_x ≥ 0`, determinate iff `κ(φ − 1) + (1 − β)φ_x > 0`
  (restated from Galí's Bullard–Mitra condition; Cochrane's `σ` is Galí's `1/σ`).
* "φ > 1 is neither necessary nor sufficient" (p. 420, A1 p. 587, Ch16 p. 369, Ch12 P8):
  `not_necessary_witness`, `not_necessary_phix` (every `φ ∈ [0, 1)` is made determinate by some
  `φ_x ≥ 0`), `not_necessary_negative` (oscillating region, `φ_x = 0`), `not_sufficient_witness`
  and `not_sufficient` (every `φ > 1` is made indeterminate by some `φ_x < 0`), while for
  `φ_x ≥ 0` the condition `φ > 1` is sufficient (`sufficient_of_phix_nonneg`) and output
  responses only widen the region (`widens_with_phix`).
* (17.33) and (1.55): `deviation_iff_17_33`, `eq_1_55`; the printed `u_x` coefficient of
  (1.55) is off by a factor `β` (`printed_1_55_iff`).
* (1.57): `trM`, `detM`, `eq_1_57` (the printed eigenvalues are the roots of the characteristic
  polynomial `λ² − tr M λ + det M`), `plus_root_gt_one`, `roots_phi_lt_one` (`φ < 1`: one root
  below one; inside `(−1, 1)` iff `φ > −(1 + 2(1+β)/(σκ))`; below `−1` beyond (1.58)),
  `roots_phi_gt_one` (`φ > 1`: both roots explosive, real or complex).
* φ irrelevance (pp. 419–420): `deviation_of_eqm`, `phi_irrelevance` — for every `φ` in the
  determinacy region the bounded equilibria of the model with King's rule are exactly the
  starred one, so the equilibrium set does not depend on `φ` (`phi_irrelevance_sets`); the
  reverse-engineered disturbances of p. 414 give unique equilibria (`standard_rule_unique`,
  `reverse_engineered_unique`).
* p. 421 (real explosions): for `φ < 1/β` (in particular `1 < φ < 1/β`) a non-selected path
  has `βᵗ x̃_t → −∞` (`real_explosion`).
-/

namespace Cochrane.KeynesianStickyPrices.TaylorDeterminacy

open Filter Topology FullModel OptimalPolicy
open SharedTools (Pmat Qmat solvedA tr2_solvedA det2_solvedA det2_Pmat)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Generic structural systems `P x_t = Q E_t x_{t+1}` -/

/-- Cochrane (2023), p. 420 (the system behind (17.33)): `x` solves `P x_t = Q E_t x_{t+1}`. -/
def StructSolves (P Q : Matrix (Fin 2) (Fin 2) ℝ) (x : ℕ → Fin 2 → Ω → ℝ) : Prop :=
  ∀ t i, P i 0 • x t 0 + P i 1 • x t 1 =
    Q i 0 • 𝔼.E t (x (t + 1) 0) + Q i 1 • 𝔼.E t (x (t + 1) 1)

/-- Cochrane (2023), p. 420: determinacy — the only bounded adapted solution of
`P x_t = Q E_t x_{t+1}` is zero. -/
def StructDeterminate (P Q : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ x, 𝔼.AdaptedVec x → BoundedVec x → StructSolves 𝔼 P Q x → x = 0

/-- Solving two linear equations by Cramer's rule. -/
theorem solve2 {P00 P01 P10 P11 q0 q1 a b : ℝ} (hD : P00 * P11 - P01 * P10 ≠ 0) :
    (P00 * a + P01 * b = q0 ∧ P10 * a + P11 * b = q1) ↔
      (a = (P11 * q0 - P01 * q1) / (P00 * P11 - P01 * P10) ∧
        b = (P00 * q1 - P10 * q0) / (P00 * P11 - P01 * P10)) := by
  constructor
  · rintro ⟨h0, h1⟩
    constructor <;> rw [eq_div_iff hD]
    · linear_combination P11 * h0 - P01 * h1
    · linear_combination P00 * h1 - P10 * h0
  · rintro ⟨ha, hb⟩
    have ka : a * (P00 * P11 - P01 * P10) = P11 * q0 - P01 * q1 := by
      rw [ha, div_mul_cancel₀ _ hD]
    have kb : b * (P00 * P11 - P01 * P10) = P00 * q1 - P10 * q0 := by
      rw [hb, div_mul_cancel₀ _ hD]
    constructor <;> apply mul_right_cancel₀ hD
    · linear_combination P00 * ka + P01 * kb
    · linear_combination P10 * ka + P11 * kb

/-- For `det P ≠ 0`, `P x_t = Q E_t x_{t+1}` iff `x_t = A E_t x_{t+1}`, `A = P⁻¹ Q`. -/
theorem struct_iff_solves {P : Matrix (Fin 2) (Fin 2) ℝ} (hP : det2 P ≠ 0)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (x : ℕ → Fin 2 → Ω → ℝ) :
    StructSolves 𝔼 P Q x ↔ 𝔼.Solves (solvedA P Q) 0 x := by
  have hP' : P 0 0 * P 1 1 - P 0 1 * P 1 0 ≠ 0 := hP
  have hd : det2 P = P 0 0 * P 1 1 - P 0 1 * P 1 0 := rfl
  constructor
  · intro h t i
    funext ω
    have e0 := congrFun (h t 0) ω
    have e1 := congrFun (h t 1) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1
    obtain ⟨ha, hb⟩ := (solve2 hP').mp ⟨e0, e1⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero]
    fin_cases i
    · simp only [solvedA, hd, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue]
      rw [ha]; ring
    · simp only [solvedA, hd, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.mk_one, Fin.isValue]
      rw [hb]; ring
  · intro h t i
    funext ω
    have e0 := congrFun (h t 0) ω
    have e1 := congrFun (h t 1) ω
    simp only [solvedA, hd, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, add_zero] at e0 e1
    have hab := (solve2 hP' (a := x t 0 ω) (b := x t 1 ω)
      (q0 := Q 0 0 * 𝔼.E t (x (t + 1) 0) ω + Q 0 1 * 𝔼.E t (x (t + 1) 1) ω)
      (q1 := Q 1 0 * 𝔼.E t (x (t + 1) 0) ω + Q 1 1 * 𝔼.E t (x (t + 1) 1) ω)).mpr
      ⟨by rw [e0]; ring, by rw [e1]; ring⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fin_cases i
    · exact hab.1
    · exact hab.2

/-- Cochrane (2023), p. 420: if `det P = 0` the system is not determinate — a vector `v ≠ 0`
with `P v = 0` gives the bounded solution `x_0 = v`, `x_t = 0` for `t ≥ 1`. -/
theorem not_determinate_of_det_zero [Nonempty Ω] {P : Matrix (Fin 2) (Fin 2) ℝ}
    (hP : det2 P = 0) (Q : Matrix (Fin 2) (Fin 2) ℝ) : ¬ StructDeterminate 𝔼 P Q := by
  have hP' : P 0 0 * P 1 1 - P 0 1 * P 1 0 = 0 := hP
  obtain ⟨v, hv0, hv⟩ : ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ ∀ i, P i 0 * v 0 + P i 1 * v 1 = 0 := by
    by_cases h0 : P 0 0 = 0 ∧ P 0 1 = 0
    · by_cases h1 : P 1 0 = 0 ∧ P 1 1 = 0
      · refine ⟨![1, 0], fun h => by simpa using congrFun h 0, fun i => ?_⟩
        fin_cases i <;> simp [h0.1, h1.1]
      · refine ⟨![P 1 1, -P 1 0], fun h => h1 ⟨by simpa using congrFun h 1,
          by simpa using congrFun h 0⟩, fun i => ?_⟩
        fin_cases i
        · simp [h0.1, h0.2]
        · simp; ring
    · refine ⟨![P 0 1, -P 0 0], fun h => h0 ⟨by simpa using congrFun h 1,
        by simpa using congrFun h 0⟩, fun i => ?_⟩
      fin_cases i
      · simp; ring
      · simp; linear_combination -hP'
  intro hdet
  set x : ℕ → Fin 2 → Ω → ℝ := fun t j _ => if t = 0 then v j else 0 with hx
  have hsol : StructSolves 𝔼 P Q x := by
    intro t i
    funext ω
    simp only [hx, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.add_one_ne_zero, ↓reduceIte,
      𝔼.const, mul_zero, add_zero]
    split_ifs
    · exact hv i
    · simp
  have h := hdet x (fun t j => by simp only [hx]; exact 𝔼.const t _)
    ⟨|v 0| + |v 1|, fun t j ω => by
      simp only [hx]
      split_ifs
      · fin_cases j <;> simp
      · simp only [abs_zero]; positivity⟩ hsol
  apply hv0
  funext j
  have := congrFun (congrFun (congrFun h 0) j) (Classical.arbitrary Ω)
  simpa [hx] using this

/-- Cochrane (2023), p. 420, and A1 p. 587 (Blanchard–Kahn): `P x_t = Q E_t x_{t+1}` is
determinate iff `det P ≠ 0` and `A = P⁻¹Q` satisfies the Schur–Cohn condition. -/
theorem structDeterminate_iff [Nonempty Ω] (P Q : Matrix (Fin 2) (Fin 2) ℝ) :
    StructDeterminate 𝔼 P Q ↔
      det2 P ≠ 0 ∧ SchurStable (tr2 (solvedA P Q)) (det2 (solvedA P Q)) := by
  constructor
  · intro h
    have hP : det2 P ≠ 0 := fun h0 => not_determinate_of_det_zero 𝔼 h0 Q h
    refine ⟨hP, ?_⟩
    by_contra hA
    have hz : 𝔼.Solves (solvedA P Q) 0 0 := fun t i => by simp
    obtain ⟨y, hy, hay, hby, hne⟩ :=
      𝔼.system_not_unique hA hz (fun t i => by simp) ⟨0, fun t i ω => by simp⟩
    exact hne (h y hay hby ((struct_iff_solves 𝔼 hP Q y).mpr hy))
  · rintro ⟨hP, hA⟩ x hax hbx hx
    have hz : 𝔼.Solves (solvedA P Q) 0 0 := fun t i => by simp
    exact 𝔼.system_unique hA ((struct_iff_solves 𝔼 hP Q x).mp hx) hz hax
      (fun t i => by simp) hbx ⟨0, fun t i ω => by simp⟩

/-! ### The deviation system (17.29)–(17.32) -/

/-- Cochrane (2023), eqs. (17.29)–(17.32), p. 420, with an output response `φ_x` (eq. (18.1),
p. 427): `ĩ_t = r̃_t + E_t π̃_{t+1}`, `x̃_t = E_t x̃_{t+1} − σ r̃_t`,
`π̃_t = β E_t π̃_{t+1} + κ x̃_t`, `ĩ_t = φ π̃_t + φ_x x̃_t`. -/
def Deviation (σ β κ φ φx : ℝ) (i r x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = r t + 𝔼.E t (π (t + 1)) ∧ x t = 𝔼.E t (x (t + 1)) - σ • r t ∧
    π t = β • 𝔼.E t (π (t + 1)) + κ • x t ∧ i t = φ • π t + φx • x t

/-- The stacked vector `(x̃_t, π̃_t)`. -/
def stack (x π : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![x t, π t]

/-- Cochrane (2023), eqs. (17.29)–(17.32): eliminating `ĩ` and `r̃`, the deviation system is
`(1 + σφ_x) x̃_t + σφ π̃_t = E_t x̃_{t+1} + σ E_t π̃_{t+1}`, `−κ x̃_t + π̃_t = β E_t π̃_{t+1}`. -/
theorem deviation_iff_struct (σ β κ φ φx : ℝ) (i r x π : ℕ → Ω → ℝ) :
    Deviation 𝔼 σ β κ φ φx i r x π ↔
      (∀ t, i t = φ • π t + φx • x t) ∧ (∀ t, r t = i t - 𝔼.E t (π (t + 1))) ∧
        StructSolves 𝔼 (Pmat σ κ φ φx) (Qmat σ β) (stack x π) := by
  constructor
  · intro h
    refine ⟨fun t => (h t).2.2.2, fun t => by rw [(h t).1]; abel, fun t j => ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := h t
    funext ω
    have e1 := congrFun h1 ω
    have e2 := congrFun h2 ω
    have e3 := congrFun h3 ω
    have e4 := congrFun h4 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 e4
    fin_cases j
    · simp only [Pmat, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_fin_one, stack, Matrix.cons_val_one, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Qmat, one_smul]
      linear_combination e2 + σ * e1 - σ * e4
    · simp only [Pmat, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, stack, neg_smul,
        one_smul, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Qmat, zero_smul,
        Pi.zero_apply, zero_add]
      linear_combination e3
  · rintro ⟨hi, hr, hs⟩ t
    have e0 := hs t 0
    have e1 := hs t 1
    simp only [Pmat, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, stack, Matrix.cons_val_one, Qmat, one_smul, neg_smul, zero_smul,
      zero_add] at e0 e1
    refine ⟨by rw [hr t]; abel, ?_, ?_, hi t⟩
    · funext ω
      have f0 := congrFun e0 ω
      have fi := congrFun (hi t) ω
      rw [hr t]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at f0 fi ⊢
      rw [fi]
      linear_combination f0
    · funext ω
      have f1 := congrFun e1 ω
      simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at f1 ⊢
      linear_combination f1

/-- Cochrane (2023), p. 420: the deviation system is *determinate* when its only bounded
adapted solution has `x̃ = π̃ = 0` (and then `ĩ = r̃ = 0`). -/
def Determinate (σ β κ φ φx : ℝ) : Prop :=
  ∀ i r x π : ℕ → Ω → ℝ, 𝔼.Adapted x → 𝔼.Adapted π → BoundedProc x → BoundedProc π →
    Deviation 𝔼 σ β κ φ φx i r x π → x = 0 ∧ π = 0

/-- Determinacy of the deviation system is determinacy of the structural system. -/
theorem determinate_iff_struct (σ β κ φ φx : ℝ) :
    Determinate 𝔼 σ β κ φ φx ↔ StructDeterminate 𝔼 (Pmat σ κ φ φx) (Qmat σ β) := by
  constructor
  · intro h v hav hbv hv
    set x : ℕ → Ω → ℝ := fun t => v t 0
    set π : ℕ → Ω → ℝ := fun t => v t 1
    have hst : stack x π = v := by
      funext t j; fin_cases j <;> rfl
    have hd : Deviation 𝔼 σ β κ φ φx (fun t => φ • π t + φx • x t)
        (fun t => φ • π t + φx • x t - 𝔼.E t (π (t + 1))) x π :=
      (deviation_iff_struct 𝔼 σ β κ φ φx _ _ x π).mpr ⟨fun t => rfl, fun t => rfl, hst ▸ hv⟩
    obtain ⟨M, hM⟩ := hbv
    obtain ⟨h1, h2⟩ := h _ _ x π (fun t => hav t 0) (fun t => hav t 1)
      ⟨M, fun t ω => hM t 0 ω⟩ ⟨M, fun t ω => hM t 1 ω⟩ hd
    rw [← hst, h1, h2]
    funext t j
    fin_cases j <;> rfl
  · intro h i r x π hx hπ hbx hbπ hd
    have hs := ((deviation_iff_struct 𝔼 σ β κ φ φx i r x π).mp hd).2.2
    obtain ⟨M₁, h₁⟩ := hbx
    obtain ⟨M₂, h₂⟩ := hbπ
    have h0 := h (stack x π) (fun t j => by fin_cases j; exacts [hx t, hπ t])
      ⟨max M₁ M₂, fun t j ω => by
        fin_cases j
        · exact (h₁ t ω).trans (le_max_left _ _)
        · exact (h₂ t ω).trans (le_max_right _ _)⟩ hs
    exact ⟨funext fun t => by simpa [stack] using congrFun (congrFun h0 t) 0,
      funext fun t => by simpa [stack] using congrFun (congrFun h0 t) 1⟩

/-- Cochrane (2023), p. 420 and A1 p. 587: the deviation system (with output response) is
determinate iff `D = 1 + σφ_x + σκφ ≠ 0` and `SchurStable (T/D) (β/D)`,
`T = 1 + β + σκ + βσφ_x`. -/
theorem determinate_iff [Nonempty Ω] (σ β κ φ φx : ℝ) :
    Determinate 𝔼 σ β κ φ φx ↔
      1 + σ * φx + σ * κ * φ ≠ 0 ∧
        SchurStable ((1 + β + σ * κ + β * σ * φx) / (1 + σ * φx + σ * κ * φ))
          (β / (1 + σ * φx + σ * κ * φ)) := by
  rw [determinate_iff_struct, structDeterminate_iff, det2_Pmat]
  refine and_congr_right fun hD => ?_
  have hD' : det2 (Pmat σ κ φ φx) ≠ 0 := by rwa [det2_Pmat]
  rw [tr2_solvedA, det2_solvedA hD', det2_Pmat]
  have hq : det2 (Qmat σ β) = β := by simp [det2, Qmat]
  rw [hq]
  have ht : Pmat σ κ φ φx 1 1 * Qmat σ β 0 0 - Pmat σ κ φ φx 0 1 * Qmat σ β 1 0 -
      Pmat σ κ φ φx 1 0 * Qmat σ β 0 1 + Pmat σ κ φ φx 0 0 * Qmat σ β 1 1 =
      1 + β + σ * κ + β * σ * φx := by
    simp [Pmat, Qmat]; ring
  rw [ht]

/-- Schur–Cohn for `(T/D, β/D)` with `D > 0`, `β > 0`: `β < D ∧ |T| < D + β`. -/
theorem schur_div_pos {T D β : ℝ} (hD : 0 < D) (hβ : 0 < β) :
    SchurStable (T / D) (β / D) ↔ β < D ∧ |T| < D + β := by
  unfold SchurStable
  rw [abs_div, abs_div, abs_of_pos hD, abs_of_pos hβ, div_lt_one hD, one_add_div hD.ne',
    div_lt_div_iff_of_pos_right hD]

/-- Schur–Cohn for `(T/D, β/D)` with `D < 0`, `β > 0`: `β < −D ∧ |T| < −D − β`. -/
theorem schur_div_neg {T D β : ℝ} (hD : D < 0) (hβ : 0 < β) :
    SchurStable (T / D) (β / D) ↔ β < -D ∧ |T| < -D - β := by
  unfold SchurStable
  have hD' : 0 < -D := by linarith
  have hD0 : D ≠ 0 := hD.ne
  rw [abs_div, abs_div, abs_of_neg hD, abs_of_pos hβ, div_lt_one hD',
    show 1 + β / D = (-D - β) / -D by field_simp; ring, div_lt_div_iff_of_pos_right hD']

/-- Cochrane (2023), p. 420 and A1 p. 587, explicit form: determinate iff
`(D > 0 ∧ β < D ∧ |T| < D + β) ∨ (D < 0 ∧ β < −D ∧ |T| < −D − β)`. -/
theorem determinate_iff_explicit [Nonempty Ω] {σ β κ φ φx : ℝ} (hβ : 0 < β) :
    Determinate 𝔼 σ β κ φ φx ↔
      (0 < 1 + σ * φx + σ * κ * φ ∧ β < 1 + σ * φx + σ * κ * φ ∧
          |1 + β + σ * κ + β * σ * φx| < 1 + σ * φx + σ * κ * φ + β) ∨
        (1 + σ * φx + σ * κ * φ < 0 ∧ β < -(1 + σ * φx + σ * κ * φ) ∧
          |1 + β + σ * κ + β * σ * φx| < -(1 + σ * φx + σ * κ * φ) - β) := by
  rw [determinate_iff]
  rcases lt_trichotomy (1 + σ * φx + σ * κ * φ) 0 with hD | hD | hD
  · rw [schur_div_neg hD hβ]
    constructor
    · rintro ⟨-, h⟩; exact Or.inr ⟨hD, h⟩
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · linarith
      · exact ⟨hD.ne, h⟩
  · rw [hD]
    simp only [ne_eq, not_true_eq_false, false_and, lt_self_iff_false, false_or]
  · rw [schur_div_pos hD hβ]
    constructor
    · rintro ⟨-, h⟩; exact Or.inl ⟨hD, h⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact ⟨hD.ne', h⟩
      · linarith

/-- Cochrane (2023), A1 p. 587 and eq. (1.58), with Ch17 p. 420: in the three-equation model
with `i = φπ` (`φ_x = 0`), `σ, κ > 0`, `0 < β < 1`, the equilibrium is determinate iff
`φ > 1` or `φ < −(1 + 2(1 + β)/(σκ))`. -/
theorem determinate_iff_phi [Nonempty Ω] {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hβ1 : β < 1) :
    Determinate 𝔼 σ β κ φ 0 ↔ 1 < φ ∨ φ < -(1 + 2 * (1 + β) / (σ * κ)) := by
  have ha := mul_pos hσ hκ
  rw [determinate_iff_explicit 𝔼 hβ]
  simp only [mul_zero, add_zero]
  have hT : 0 < 1 + β + σ * κ := by linarith
  rw [abs_of_pos hT]
  have hb : -(1 + 2 * (1 + β) / (σ * κ)) * (σ * κ) = -(σ * κ) - 2 * (1 + β) := by
    field_simp
    ring
  constructor
  · rintro (⟨-, -, h⟩ | ⟨-, -, h⟩)
    · left
      nlinarith
    · right
      have : φ * (σ * κ) < -(1 + 2 * (1 + β) / (σ * κ)) * (σ * κ) := by rw [hb]; nlinarith
      exact lt_of_mul_lt_mul_right this ha.le
  · rintro (h | h)
    · left
      refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
    · right
      have : φ * (σ * κ) < -(σ * κ) - 2 * (1 + β) := by
        rw [← hb]; exact mul_lt_mul_of_pos_right h ha
      refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- Cochrane (2023), Ch16 p. 369 and A1 p. 587 (restated from Galí's Bullard–Mitra condition):
for `σ, κ > 0`, `0 < β < 1` and `φ, φ_x ≥ 0`, determinate iff `κ(φ − 1) + (1 − β)φ_x > 0`. -/
theorem determinate_iff_BM [Nonempty Ω] {σ β κ φ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (hβ1 : β < 1) (hφ : 0 ≤ φ) (hφx : 0 ≤ φx) :
    Determinate 𝔼 σ β κ φ φx ↔ 0 < κ * (φ - 1) + (1 - β) * φx := by
  rw [determinate_iff_explicit 𝔼 hβ]
  have h1 : 0 ≤ σ * φx := mul_nonneg hσ.le hφx
  have h2 : 0 ≤ σ * κ * φ := mul_nonneg (mul_pos hσ hκ).le hφ
  have hT : 0 < 1 + β + σ * κ + β * σ * φx := by
    have := mul_nonneg hβ.le h1
    nlinarith [mul_pos hσ hκ]
  rw [abs_of_pos hT]
  constructor
  · rintro (⟨-, -, h⟩ | ⟨h, -⟩)
    · have : 0 < σ * (κ * (φ - 1) + (1 - β) * φx) := by nlinarith
      exact pos_of_mul_pos_right this hσ.le
    · linarith
  · intro h
    left
    refine ⟨by linarith, by linarith, ?_⟩
    nlinarith [mul_pos hσ h]


/-! ### φ > 1 is neither necessary nor sufficient -/

/-- Cochrane (2023), p. 420, A1 p. 587, Ch16 p. 369 and Ch12 p. 328 ("φ > 1 is neither
necessary …"): with `σ = κ = 1`, `β = 1/2`, the rule `i = 0.5 π + 2 x` (`φ < 1`) is
determinate. -/
theorem not_necessary_witness [Nonempty Ω] : Determinate 𝔼 1 (1 / 2) 1 (1 / 2) 2 :=
  (determinate_iff_BM 𝔼 one_pos one_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).mpr (by norm_num)

/-- Cochrane (2023), p. 420 ("adding `φ_x x_t` responses widens the range"): for `σ, κ > 0`,
`0 < β < 1`, every `φ ∈ [0, 1)` is made determinate by a large enough output response. -/
theorem not_necessary_phix [Nonempty Ω] {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hβ1 : β < 1) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) :
    ∃ φx, 0 ≤ φx ∧ Determinate 𝔼 σ β κ φ φx := by
  have h1β : 0 < 1 - β := by linarith
  refine ⟨κ * (1 - φ) / (1 - β) + 1, by positivity, ?_⟩
  rw [determinate_iff_BM 𝔼 hσ hκ hβ hβ1 hφ0 (by positivity)]
  field_simp
  nlinarith

/-- Cochrane (2023), A1 p. 587, eq. (1.58): even with `φ_x = 0`, `φ > 1` is not necessary —
`σ = κ = 1`, `β = 1/2`, `φ = −5 < −(1 + 2(1 + β)/(σκ)) = −4` is determinate. -/
theorem not_necessary_negative [Nonempty Ω] : Determinate 𝔼 1 (1 / 2) 1 (-5) 0 :=
  (determinate_iff_phi 𝔼 one_pos one_pos (by norm_num) (by norm_num)).mpr (Or.inr (by norm_num))

/-- Cochrane (2023), p. 420, Ch16 p. 369, Ch12 P8 p. 328 ("… nor sufficient"; "the coefficient
can exceed 1 while the eigenvalue is stable"): with `σ = κ = 1`, `β = 1/2`, the rule
`i = 2π − 2x` (`φ = 2 > 1`) is not determinate. -/
theorem not_sufficient_witness [Nonempty Ω] : ¬ Determinate 𝔼 1 (1 / 2) 1 2 (-2) := by
  rw [determinate_iff_explicit 𝔼 (by norm_num)]
  norm_num

/-- Cochrane (2023), p. 420: for **every** `φ` (in particular every `φ > 1`) and `σ ≠ 0` there
is an output response `φ_x = −(1 + σκφ)/σ` that makes the system indeterminate. -/
theorem not_sufficient [Nonempty Ω] {σ β κ : ℝ} (hσ : σ ≠ 0) (φ : ℝ) :
    ∃ φx, ¬ Determinate 𝔼 σ β κ φ φx := by
  refine ⟨-(1 + σ * κ * φ) / σ, fun h => ((determinate_iff 𝔼 _ _ _ _ _).mp h).1 ?_⟩
  field_simp
  ring

/-- Cochrane (2023), p. 420: with a nonnegative output response, `φ > 1` is sufficient. -/
theorem sufficient_of_phix_nonneg [Nonempty Ω] {σ β κ φ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (hβ1 : β < 1) (hφ : 1 < φ) (hφx : 0 ≤ φx) : Determinate 𝔼 σ β κ φ φx :=
  (determinate_iff_BM 𝔼 hσ hκ hβ hβ1 (by linarith) hφx).mpr
    (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - β) hφx])

/-- Cochrane (2023), p. 420 ("adding `φ_x x_t` responses widens the range of parameters"):
for `φ ≥ 0`, raising a nonnegative output response preserves determinacy. -/
theorem widens_with_phix [Nonempty Ω] {σ β κ φ φx φx' : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (hβ1 : β < 1) (hφ : 0 ≤ φ) (hφx : 0 ≤ φx) (hle : φx ≤ φx')
    (h : Determinate 𝔼 σ β κ φ φx) : Determinate 𝔼 σ β κ φ φx' := by
  rw [determinate_iff_BM 𝔼 hσ hκ hβ hβ1 hφ hφx] at h
  rw [determinate_iff_BM 𝔼 hσ hκ hβ hβ1 hφ (hφx.trans hle)]
  nlinarith

/-! ### The matrix forms (17.33) and (1.55) -/

/-- Cochrane (2023), eq. (17.33), p. 420 (with output response): for `β ≠ 0` the deviation
system is `E_t x̃_{t+1} = β⁻¹[(β + σκ + βσφ_x) x̃_t − σ(1 − βφ) π̃_t]`,
`E_t π̃_{t+1} = β⁻¹[−κ x̃_t + π̃_t]` (with `ĩ = φπ̃ + φ_x x̃`, `r̃ = ĩ − E π̃'`); (17.33) is
`φ_x = 0`. -/
theorem deviation_iff_17_33 {σ β κ φ φx : ℝ} (hβ : β ≠ 0) (i r x π : ℕ → Ω → ℝ) :
    Deviation 𝔼 σ β κ φ φx i r x π ↔
      (∀ t, i t = φ • π t + φx • x t) ∧ (∀ t, r t = i t - 𝔼.E t (π (t + 1))) ∧
        ∀ t, 𝔼.E t (x (t + 1)) =
            β⁻¹ • ((β + σ * κ + β * σ * φx) • x t - (σ * (1 - β * φ)) • π t) ∧
          𝔼.E t (π (t + 1)) = β⁻¹ • (-κ • x t + π t) := by
  rw [deviation_iff_struct]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h t
    have e0 := h t 0
    have e1 := h t 1
    simp only [Pmat, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, stack, Matrix.cons_val_one, Qmat, one_smul, neg_smul, zero_smul,
      zero_add] at e0 e1
    refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
    · have f0 := congrFun e0 ω
      have f1 := congrFun e1 ω
      simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at f0 f1 ⊢
      rw [eq_inv_mul_iff_mul_eq₀ hβ]
      linear_combination -β * f0 + σ * f1
    · have f1 := congrFun e1 ω
      simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at f1 ⊢
      rw [eq_inv_mul_iff_mul_eq₀ hβ]
      linear_combination -f1
  · intro h t j
    obtain ⟨h0, h1⟩ := h t
    funext ω
    have f0 := congrFun h0 ω
    have f1 := congrFun h1 ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at f0 f1
    fin_cases j
    · simp only [Pmat, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_fin_one, stack, Matrix.cons_val_one, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Qmat, one_smul]
      rw [f0, f1]
      field_simp
      ring
    · simp only [Pmat, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, stack, neg_smul,
        one_smul, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Qmat, zero_smul,
        Pi.zero_apply, zero_add]
      rw [f1]
      field_simp

/-- Cochrane (2023), A1 eq. (1.55), p. 586 (corrected): in the model (17.15)–(17.17) with
`i_t = φ π_t + u_{i,t}` and `β ≠ 0`,
`E_t x_{t+1} = β⁻¹[(β + σκ) x_t − σ(1 − βφ) π_t] + β⁻¹[−β u_{x,t} + σ u_{π,t} + σβ u_{i,t}]`,
`E_t π_{t+1} = β⁻¹[−κ x_t + π_t] − β⁻¹ u_{π,t}`. The printed shock row has `−1` in place of
`−β` for `u_x` (see `printed_1_55_iff`). -/
theorem eq_1_55 {σ β κ φ : ℝ} (hβ : β ≠ 0) {ux uπ ui i r x π : ℕ → Ω → ℝ}
    (h : Model 𝔼 σ β κ ux uπ i r x π) (hrule : ∀ t, i t = φ • π t + ui t) (t : ℕ) :
    𝔼.E t (x (t + 1)) = β⁻¹ • ((β + σ * κ) • x t - (σ * (1 - β * φ)) • π t) +
        β⁻¹ • (-β • ux t + σ • uπ t + (σ * β) • ui t) ∧
      𝔼.E t (π (t + 1)) = β⁻¹ • (-κ • x t + π t) - β⁻¹ • uπ t := by
  obtain ⟨his, hf, hpc⟩ := h
  refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
  · have e1 := congrFun (his t) ω
    have e2 := congrFun (hf t) ω
    have e3 := congrFun (hpc t) ω
    have e4 := congrFun (hrule t) ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at *
    rw [← mul_add, eq_inv_mul_iff_mul_eq₀ hβ]
    linear_combination -β * e1 - β * σ * e2 + β * σ * e4 + σ * e3
  · have e3 := congrFun (hpc t) ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e3 ⊢
    rw [← mul_sub, eq_inv_mul_iff_mul_eq₀ hβ]
    linear_combination -e3

/-- Cochrane (2023), A1 eq. (1.55), p. 586, as printed: its first row, with `u_x` coefficient
`−1/β`, holds at a date and state iff `β = 1` or `u_{x,t} = 0` there — the printed shock
matrix is wrong for `β ≠ 1` (new error, not in the survey). -/
theorem printed_1_55_iff {σ β κ φ : ℝ} (hβ : β ≠ 0) {ux uπ ui i r x π : ℕ → Ω → ℝ}
    (h : Model 𝔼 σ β κ ux uπ i r x π) (hrule : ∀ t, i t = φ • π t + ui t) (t : ℕ) (ω : Ω) :
    𝔼.E t (x (t + 1)) ω = β⁻¹ * ((β + σ * κ) * x t ω - σ * (1 - β * φ) * π t ω) +
        β⁻¹ * (-1 * ux t ω + σ * uπ t ω + σ * β * ui t ω) ↔ β = 1 ∨ ux t ω = 0 := by
  have e := congrFun (eq_1_55 𝔼 hβ h hrule t).1 ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e
  rw [e]
  constructor
  · intro h'
    have : (β - 1) * ux t ω = 0 := by
      field_simp at h'
      linear_combination -h'
    rcases mul_eq_zero.mp this with h1 | h1
    · exact Or.inl (by linarith)
    · exact Or.inr h1
  · rintro (h1 | h1)
    · subst h1; ring
    · rw [h1]; ring

/-! ### The eigenvalues (1.57) -/

/-- Cochrane (2023), eq. (1.57), p. 587: `tr M = (1 + β + σκ)/β` for the transition matrix `M`
of (17.33). -/
noncomputable def trM (σ β κ : ℝ) : ℝ := (1 + β + σ * κ) / β

/-- Cochrane (2023), eq. (1.57), p. 587: `det M = (1 + σκφ)/β`. -/
noncomputable def detM (σ β κ φ : ℝ) : ℝ := (1 + σ * κ * φ) / β

/-- Cochrane (2023), eq. (17.33), p. 420: the transition matrix
`M = β⁻¹ [[β + σκ, −σ(1 − βφ)], [−κ, 1]]`. -/
noncomputable def Mmat (σ β κ φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(β + σ * κ) / β, -(σ * (1 - β * φ)) / β; -κ / β, 1 / β]

/-- Cochrane (2023), eq. (1.57): `tr M` and `det M`. -/
theorem tr_det_Mmat {σ β κ φ : ℝ} (hβ : β ≠ 0) :
    tr2 (Mmat σ β κ φ) = trM σ β κ ∧ det2 (Mmat σ β κ φ) = detM σ β κ φ := by
  simp only [tr2, det2, Mmat, trM, detM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  constructor <;> field_simp <;> ring

/-- Cochrane (2023), eq. (1.57), p. 587: the discriminant
`Δ = (1 − β + σκ)² − 4βσκ(φ − 1)`. -/
def discE (σ β κ φ : ℝ) : ℝ := (1 - β + σ * κ) ^ 2 - 4 * β * σ * κ * (φ - 1)

/-- `discQ (tr M) (det M) = Δ/β²`. -/
theorem discQ_eq {σ β κ φ : ℝ} (hβ : β ≠ 0) :
    discQ (trM σ β κ) (detM σ β κ φ) = discE σ β κ φ / β ^ 2 := by
  unfold discQ trM detM discE
  field_simp
  ring

/-- Cochrane (2023), eq. (1.57), p. 587: for `β > 0` and `Δ ≥ 0` the eigenvalues of `M` are
`λ = 1 + [(1 − β + σκ) ± √Δ]/(2β)`: they are the roots `root₁`, `root₂` of the characteristic
polynomial `λ² − tr M λ + det M`. -/
theorem eq_1_57 {σ β κ φ : ℝ} (hβ : 0 < β) (hΔ : 0 ≤ discE σ β κ φ) :
    root₁ (trM σ β κ) (detM σ β κ φ) =
        ((1 + ((1 - β + σ * κ) + Real.sqrt (discE σ β κ φ)) / (2 * β) : ℝ) : ℂ) ∧
      root₂ (trM σ β κ) (detM σ β κ φ) =
        ((1 + ((1 - β + σ * κ) - Real.sqrt (discE σ β κ φ)) / (2 * β) : ℝ) : ℂ) := by
  have hd := discQ_eq (σ := σ) (κ := κ) (φ := φ) hβ.ne'
  have hnn : 0 ≤ discQ (trM σ β κ) (detM σ β κ φ) := by rw [hd]; positivity
  have hs : Real.sqrt (discQ (trM σ β κ) (detM σ β κ φ)) = Real.sqrt (discE σ β κ φ) / β := by
    rw [hd, Real.sqrt_div hΔ, Real.sqrt_sq hβ.le]
  unfold root₁ root₂
  simp only [hnn, ↓reduceIte, hs]
  simp only [trM]
  constructor <;> congr 1 <;> field_simp <;> ring

/-- Cochrane (2023), A1 p. 587 ("the + eigenvalue is greater than one"): for `σκ > 0`,
`0 < β < 1` and `Δ ≥ 0`, `λ₊ > 1`. -/
theorem plus_root_gt_one {σ β κ φ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hβ1 : β < 1) :
    1 < 1 + ((1 - β + σ * κ) + Real.sqrt (discE σ β κ φ)) / (2 * β) := by
  have := Real.sqrt_nonneg (discE σ β κ φ)
  have : 0 < ((1 - β + σ * κ) + Real.sqrt (discE σ β κ φ)) / (2 * β) := by
    apply div_pos <;> linarith
  linarith

/-- Cochrane (2023), A1 p. 587 ("if φ < 1 the − eigenvalue is less than one") and eq. (1.58):
for `σ, κ > 0`, `0 < β < 1` and `φ < 1`, the eigenvalues are real, `λ₋ < 1`, and `λ₋ > −1`
(stable) iff `φ > −(1 + 2(1 + β)/(σκ))`; below that bound `λ₋ < −1` (oscillating
explosion). -/
theorem roots_phi_lt_one {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1)
    (hφ : φ < 1) :
    0 < discE σ β κ φ ∧ 1 + ((1 - β + σ * κ) - Real.sqrt (discE σ β κ φ)) / (2 * β) < 1 ∧
      (-1 < 1 + ((1 - β + σ * κ) - Real.sqrt (discE σ β κ φ)) / (2 * β) ↔
        -(1 + 2 * (1 + β) / (σ * κ)) < φ) := by
  have ha := mul_pos hσ hκ
  have hb : 0 < 1 - β + σ * κ := by linarith
  have hgt : (1 - β + σ * κ) ^ 2 < discE σ β κ φ := by
    unfold discE
    have : 0 < 4 * β * σ * κ * (1 - φ) := by
      have := mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hβ) hσ) hκ
      exact mul_pos this (by linarith)
    nlinarith
  have hsq : 1 - β + σ * κ < Real.sqrt (discE σ β κ φ) := (Real.lt_sqrt hb.le).mpr hgt
  refine ⟨lt_trans (by positivity) hgt, ?_, ?_⟩
  · have : ((1 - β + σ * κ) - Real.sqrt (discE σ β κ φ)) / (2 * β) < 0 :=
      div_neg_of_neg_of_pos (by linarith) (by linarith)
    linarith
  · have hc : 0 < 1 + 3 * β + σ * κ := by linarith
    have key : -1 < 1 + ((1 - β + σ * κ) - Real.sqrt (discE σ β κ φ)) / (2 * β) ↔
        Real.sqrt (discE σ β κ φ) < 1 + 3 * β + σ * κ := by
      rw [← sub_pos, show 1 + ((1 - β + σ * κ) - Real.sqrt (discE σ β κ φ)) / (2 * β) - -1 =
        (1 + 3 * β + σ * κ - Real.sqrt (discE σ β κ φ)) / (2 * β) by field_simp; ring,
        div_pos_iff_of_pos_right (by linarith), sub_pos]
    rw [key, Real.sqrt_lt' hc]
    have e : (1 + 3 * β + σ * κ) ^ 2 - discE σ β κ φ =
        4 * β * (2 + 2 * β + σ * κ + σ * κ * φ) := by unfold discE; ring
    have hb2 : -(1 + 2 * (1 + β) / (σ * κ)) * (σ * κ) = -(σ * κ) - 2 * (1 + β) := by
      field_simp; ring
    constructor
    · intro h
      have h4 : 0 < 4 * β * (2 + 2 * β + σ * κ + σ * κ * φ) := by linarith
      have h5 : 0 < 2 + 2 * β + σ * κ + σ * κ * φ := pos_of_mul_pos_right h4 (by linarith)
      have : -(1 + 2 * (1 + β) / (σ * κ)) * (σ * κ) < φ * (σ * κ) := by rw [hb2]; linarith
      exact lt_of_mul_lt_mul_right this ha.le
    · intro h
      have := mul_lt_mul_of_pos_right h ha
      rw [hb2] at this
      have h5 : 0 < 2 + 2 * β + σ * κ + σ * κ * φ := by linarith
      nlinarith

/-- Cochrane (2023), Ch17 p. 420 ("‖φ‖ < 1 leaves one stable eigenvalue"): for `|φ| < 1`,
`−1 < λ₋ < 1 < λ₊`. -/
theorem abs_phi_lt_one_one_stable {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hβ1 : β < 1) (hφ : |φ| < 1) :
    -1 < 1 + ((1 - β + σ * κ) - Real.sqrt (discE σ β κ φ)) / (2 * β) ∧
      1 + ((1 - β + σ * κ) - Real.sqrt (discE σ β κ φ)) / (2 * β) < 1 ∧
      1 < 1 + ((1 - β + σ * κ) + Real.sqrt (discE σ β κ φ)) / (2 * β) := by
  rw [abs_lt] at hφ
  obtain ⟨-, h2, h3⟩ := roots_phi_lt_one hσ hκ hβ hβ1 hφ.2
  refine ⟨h3.mpr ?_, h2, plus_root_gt_one (mul_pos hσ hκ) hβ hβ1⟩
  have : 0 < 2 * (1 + β) / (σ * κ) := by have := mul_pos hσ hκ; positivity
  linarith

/-- Cochrane (2023), Ch17 p. 420 and A1 p. 587 ("if φ > 1 then both eigenvalues are greater
than one"): for `φ > 1` either the roots are real and `λ₋ > 1`, or they are complex with modulus
greater than one (survey error E11: "greater than one" must be read as modulus). -/
theorem roots_phi_gt_one {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1)
    (hφ : 1 < φ) :
    (0 ≤ discE σ β κ φ ∧ 1 < 1 + ((1 - β + σ * κ) - Real.sqrt (discE σ β κ φ)) / (2 * β)) ∨
      (discE σ β κ φ < 0 ∧ 1 < ‖root₁ (trM σ β κ) (detM σ β κ φ)‖ ∧
        1 < ‖root₂ (trM σ β κ) (detM σ β κ φ)‖) := by
  have ha := mul_pos hσ hκ
  have hb : 0 < 1 - β + σ * κ := by linarith
  rcases le_or_gt 0 (discE σ β κ φ) with hΔ | hΔ
  · left
    refine ⟨hΔ, ?_⟩
    have hlt : discE σ β κ φ < (1 - β + σ * κ) ^ 2 := by
      unfold discE
      have := mul_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hβ) hσ) hκ)
        (sub_pos.mpr hφ)
      nlinarith
    have := (Real.sqrt_lt' hb).mpr hlt
    have : 0 < ((1 - β + σ * κ) - Real.sqrt (discE σ β κ φ)) / (2 * β) :=
      div_pos (by linarith) (by linarith)
    linarith
  · right
    have hneg : discQ (trM σ β κ) (detM σ β κ φ) < 0 := by
      rw [discQ_eq hβ.ne']; exact div_neg_of_neg_of_pos hΔ (by positivity)
    obtain ⟨h1, h2⟩ := normSq_root_of_neg hneg
    have hdet : 1 < detM σ β κ φ := by
      unfold detM
      rw [one_lt_div hβ]
      nlinarith
    refine ⟨hΔ, ?_, ?_⟩
    · by_contra hc
      push Not at hc
      have := norm_nonneg (root₁ (trM σ β κ) (detM σ β κ φ))
      nlinarith
    · by_contra hc
      push Not at hc
      have := norm_nonneg (root₂ (trM σ β κ) (detM σ β κ φ))
      nlinarith


/-! ### φ irrelevance (pp. 419–420) -/

/-- Cochrane (2023), eqs. (17.22)–(17.24): an equilibrium of the full model (17.15)–(17.17)
(starred form) under King's rule `i_t = i*_t + φ(π_t − π*_t)`. -/
def KingEqm (σ β κ φ : ℝ) (ux uπ istar πstar i x π : ℕ → Ω → ℝ) : Prop :=
  Starred 𝔼 σ β κ ux uπ i x π ∧ KingRule φ i istar π πstar

/-- Cochrane (2023), p. 420 ("subtracting, deviations must follow the same model … but without
constants or disturbances"): if `(i*, x*, π*)` solves the starred model and `(i, x, π)` is an
equilibrium under King's rule, the deviations solve (17.29)–(17.32). -/
theorem deviation_of_eqm {σ β κ φ : ℝ} {ux uπ istar xstar πstar i x π : ℕ → Ω → ℝ}
    (hs : Starred 𝔼 σ β κ ux uπ istar xstar πstar)
    (he : KingEqm 𝔼 σ β κ φ ux uπ istar πstar i x π) :
    Deviation 𝔼 σ β κ φ 0 (fun t => i t - istar t)
      (fun t => i t - istar t - 𝔼.E t (π (t + 1) - πstar (t + 1)))
      (fun t => x t - xstar t) (fun t => π t - πstar t) := by
  obtain ⟨⟨h1, h2⟩, hk⟩ := he
  obtain ⟨g1, g2⟩ := hs
  intro t
  beta_reduce
  refine ⟨by abel, ?_, ?_, ?_⟩
  · rw [h1 t, g1 t]
    simp only [map_sub, smul_sub]
    abel
  · rw [h2 t, g2 t]
    simp only [map_sub, smul_sub]
    abel
  · rw [hk t]
    simp

/-- Cochrane (2023), pp. 419–420 (φ irrelevance): if the deviation system with coefficient `φ`
is determinate (e.g. `φ > 1`, `determinate_iff_phi`), the bounded adapted equilibria under
King's rule are exactly the starred paths, whatever `φ`. -/
theorem phi_irrelevance [Nonempty Ω] {σ β κ φ : ℝ} (hdet : Determinate 𝔼 σ β κ φ 0)
    {ux uπ istar xstar πstar i x π : ℕ → Ω → ℝ}
    (hs : Starred 𝔼 σ β κ ux uπ istar xstar πstar) (hxs : 𝔼.Adapted xstar)
    (hπs : 𝔼.Adapted πstar) (hbxs : BoundedProc xstar) (hbπs : BoundedProc πstar)
    (hx : 𝔼.Adapted x) (hπ : 𝔼.Adapted π) (hbx : BoundedProc x) (hbπ : BoundedProc π) :
    KingEqm 𝔼 σ β κ φ ux uπ istar πstar i x π ↔ i = istar ∧ x = xstar ∧ π = πstar := by
  constructor
  · intro he
    have hd := deviation_of_eqm 𝔼 hs he
    have hbsub : ∀ {a b : ℕ → Ω → ℝ}, BoundedProc a → BoundedProc b →
        BoundedProc fun t => a t - b t := by
      intro a b ⟨M, hM⟩ ⟨N, hN⟩
      exact ⟨M + N, fun t ω => (abs_sub _ _).trans (add_le_add (hM t ω) (hN t ω))⟩
    obtain ⟨h1, h2⟩ := hdet _ _ _ _ (fun t => by simp only [map_sub, hx t, hxs t])
      (fun t => by simp only [map_sub, hπ t, hπs t]) (hbsub hbx hbxs) (hbsub hbπ hbπs) hd
    have ex : x = xstar := funext fun t => sub_eq_zero.mp (congrFun h1 t)
    have eπ : π = πstar := funext fun t => sub_eq_zero.mp (congrFun h2 t)
    refine ⟨funext fun t => ?_, ex, eπ⟩
    rw [he.2 t, eπ]
    simp
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨hs, king_equilibrium _ _ _⟩

/-- Cochrane (2023), pp. 419–420 ("the parameter φ does not enter equilibrium dynamics"): for
any two coefficients `φ`, `φ'` in the determinacy region, the bounded adapted equilibria under
King's rule coincide. -/
theorem phi_irrelevance_sets [Nonempty Ω] {σ β κ φ φ' : ℝ} (hdet : Determinate 𝔼 σ β κ φ 0)
    (hdet' : Determinate 𝔼 σ β κ φ' 0) {ux uπ istar xstar πstar i x π : ℕ → Ω → ℝ}
    (hs : Starred 𝔼 σ β κ ux uπ istar xstar πstar) (hxs : 𝔼.Adapted xstar)
    (hπs : 𝔼.Adapted πstar) (hbxs : BoundedProc xstar) (hbπs : BoundedProc πstar)
    (hx : 𝔼.Adapted x) (hπ : 𝔼.Adapted π) (hbx : BoundedProc x) (hbπ : BoundedProc π) :
    KingEqm 𝔼 σ β κ φ ux uπ istar πstar i x π ↔ KingEqm 𝔼 σ β κ φ' ux uπ istar πstar i x π := by
  rw [phi_irrelevance 𝔼 hdet hs hxs hπs hbxs hbπs hx hπ hbx hbπ,
    phi_irrelevance 𝔼 hdet' hs hxs hπs hbxs hbπs hx hπ hbx hbπ]

/-- Cochrane (2023), p. 418 and p. 414: with the disturbance `u_{i,t} = i*_t − φ π*_t`, the
standard rule `i_t = φ π_t + u_{i,t}` has the starred paths as its unique bounded adapted
equilibrium whenever `φ` is in the determinacy region. -/
theorem standard_rule_unique [Nonempty Ω] {σ β κ φ : ℝ} (hdet : Determinate 𝔼 σ β κ φ 0)
    {ux uπ istar xstar πstar i x π : ℕ → Ω → ℝ}
    (hs : Starred 𝔼 σ β κ ux uπ istar xstar πstar) (hxs : 𝔼.Adapted xstar)
    (hπs : 𝔼.Adapted πstar) (hbxs : BoundedProc xstar) (hbπs : BoundedProc πstar)
    (hx : 𝔼.Adapted x) (hπ : 𝔼.Adapted π) (hbx : BoundedProc x) (hbπ : BoundedProc π) :
    (Starred 𝔼 σ β κ ux uπ i x π ∧ ∀ t, i t = φ • π t + (istar t - φ • πstar t)) ↔
      i = istar ∧ x = xstar ∧ π = πstar := by
  rw [← king_iff_standard]
  exact phi_irrelevance 𝔼 hdet hs hxs hπs hbxs hbπs hx hπ hbx hbπ

/-- A perfect-foresight equilibrium of `FullModel.PFEqm` solves the starred model under the
`perfectForesight` expectation system (no disturbances). -/
theorem pf_starred {σ β κ : ℝ} {i x π : ℕ → ℝ} (h : PFEqm σ β κ i x π) :
    Starred perfectForesight σ β κ 0 0 (fun t _ => i t) (fun t _ => x t) (fun t _ => π t) := by
  refine ⟨fun t => funext fun _ => ?_, fun t => funext fun _ => ?_⟩ <;>
    simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, add_zero]
  · exact (h t).1
  · exact (h t).2

/-- Cochrane (2023), p. 414 ("if fed these `{u_t}` paths, the model produces the given interest
rate and inflation paths"): for `σ, κ > 0`, `0 < β < 1`, `φ > 1`, a bounded rate path `i*` and
any initial inflation `p`, the reverse-engineered disturbance `u = i* − φ π*` (with
`π* = path p`) makes `(i*, x*, π*)` the **unique** bounded equilibrium of the model with
`i_t = φ π_t + u_t` (perfect foresight). -/
theorem reverse_engineered_unique {σ β κ φ M p : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hβ1 : β < 1) (hφ : 1 < φ) {istar : ℕ → ℝ} (hi : ∀ t, |istar t| ≤ M)
    {i x π : ℕ → Unit → ℝ} (hbx : BoundedProc x) (hbπ : BoundedProc π) :
    (Starred perfectForesight σ β κ 0 0 i x π ∧
        ∀ t, i t = φ • π t + fun _ => istar t - φ * path σ β κ istar p t) ↔
      i = (fun t _ => istar t) ∧
        x = (fun t _ => (path σ β κ istar p t - β * path σ β κ istar p (t + 1)) / κ) ∧
        π = fun t _ => path σ β κ istar p t := by
  obtain ⟨-, -, hb, heq⟩ := FiscalUnderpinnings.reverse_engineer (φ := φ) hσ hκ hβ hi p
  have hs := pf_starred heq
  have hdet := (determinate_iff_phi perfectForesight hσ hκ hβ hβ1).mpr (Or.inl hφ)
  have hbx' : BoundedProc
      (fun t (_ : Unit) => (path σ β κ istar p t - β * path σ β κ istar p (t + 1)) / κ) := by
    obtain ⟨Mp, hMp⟩ := hb
    refine ⟨(Mp + |β| * Mp) / κ, fun t _ => ?_⟩
    rw [abs_div, abs_of_pos hκ]
    gcongr
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    gcongr
    · exact hMp t
    · exact hMp (t + 1)
  have hbπ' : BoundedProc (fun t (_ : Unit) => path σ β κ istar p t) := by
    obtain ⟨Mp, hMp⟩ := hb
    exact ⟨Mp, fun t _ => hMp t⟩
  have := standard_rule_unique perfectForesight hdet hs (fun _ => rfl) (fun _ => rfl) hbx'
    hbπ' (x := x) (π := π) (i := i) (fun _ => rfl) (fun _ => rfl) hbx hbπ
  rw [← this]
  refine and_congr_right fun _ => forall_congr' fun t => ?_
  constructor <;> intro h <;> rw [h] <;> funext u <;> simp [smul_eq_mul]

/-! ### Real explosions (p. 421) -/

/-- Cochrane (2023), p. 421 ("nominal explosions can also be real explosions … faster than the
interest rate so `E_t βʲ x_{t+j} → ∞`"): for `σ, κ > 0`, `β > 0` and `φ < 1/β` — in
particular for `1 < φ < 1/β`, where the deviation system is determinate and this path is one
of the explosions ruled out — the deviation system (17.29)–(17.32) has a perfect-foresight
solution with `βᵗ x̃_t → −∞`, which violates a real transversality condition. -/
theorem real_explosion {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hφβ : φ < 1 / β) :
    ∃ x π : ℕ → ℝ,
      Deviation perfectForesight σ β κ φ 0 (fun t _ => φ * π t)
        (fun t _ => φ * π t - π (t + 1)) (fun t _ => x t) (fun t _ => π t) ∧
      Tendsto (fun t => β ^ t * x t) atTop atBot := by
  have ha := mul_pos hσ hκ
  obtain ⟨μ, hμ1, hroot⟩ : ∃ μ : ℝ, 1 < μ ∧
      μ ^ 2 - (1 + β + σ * κ) * μ + β * (1 + σ * κ * φ) = 0 := by
    set A := 1 + β + σ * κ with hA
    set B := β * (1 + σ * κ * φ) with hB
    have hβφ : β * φ < 1 := by rwa [lt_div_iff₀ hβ, mul_comm] at hφβ
    have hq1 : 1 - A + B < 0 := by
      have : σ * κ * (β * φ - 1) < 0 := mul_neg_of_pos_of_neg ha (by linarith)
      nlinarith
    have hdisc : (A - 2) ^ 2 < A ^ 2 - 4 * B := by nlinarith
    have hsq2 : Real.sqrt (A ^ 2 - 4 * B) ^ 2 = A ^ 2 - 4 * B :=
      Real.sq_sqrt (by nlinarith [sq_nonneg (A - 2)])
    have hlt : |A - 2| < Real.sqrt (A ^ 2 - 4 * B) :=
      (Real.lt_sqrt (abs_nonneg _)).mpr (by rw [sq_abs]; exact hdisc)
    refine ⟨(A + Real.sqrt (A ^ 2 - 4 * B)) / 2, ?_, ?_⟩
    · have := neg_abs_le (A - 2)
      linarith
    · nlinarith [hsq2]
  have hβ0 : β ≠ 0 := hβ.ne'
  have hβμ : β * (μ / β) = μ := mul_div_cancel₀ μ hβ0
  have hbr : (1 - μ) - (1 - μ) * (μ / β) + σ * φ * κ - σ * κ * (μ / β) = 0 := by
    field_simp
    linear_combination hroot
  refine ⟨fun t => (1 - μ) * (μ / β) ^ t, fun t => κ * (μ / β) ^ t, fun t => ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> funext u <;>
      simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, zero_mul, add_zero]
    · ring
    · rw [pow_succ]
      linear_combination ((μ / β) ^ t) * hbr
    · rw [pow_succ]
      linear_combination (-(κ * (μ / β) ^ t)) * hβμ
  · have h1 : Tendsto (fun t : ℕ => μ ^ t) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hμ1
    have h2 := h1.const_mul_atTop_of_neg (by linarith : 1 - μ < 0)
    refine h2.congr fun t => ?_
    simp only [div_pow]
    field_simp

end Cochrane.KeynesianStickyPrices.TaylorDeterminacy
