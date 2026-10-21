/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MonetaryPolicyDesign.RuleTaylorPrinciple

/-!
# A forward-looking interest-rate rule

Galí (2015), Chapter 4, §4.3.1.3 and §4.3.2, pp. 107–110. With the NKPC
`π_t = β E_t π_{t+1} + κ ỹ_t` and the DIS
`ỹ_t = E_t ỹ_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − r^n_t)` (stated in `RuleExogenous`),
the forward-looking rule (16) `i_t = r^n_t + φ_π E_t π_{t+1} + φ_y E_t ỹ_{t+1}`
gives `x_t = A_F E_t x_{t+1}` with

  `A_F = [[1 − φ_y/σ, (1 − φ_π)/σ], [κ (1 − φ_y/σ), β + κ (1 − φ_π)/σ]]`.

**Correction (C4-1).** The book (p. 108) prints the `(2,2)` entry as
`β − κ φ_π/σ`; the correct entry is `β + κ (1 − φ_π)/σ` (`AF_ne_AFprinted`). Conditions
(17)–(18) characterise determinacy for the corrected matrix (`determinate_iff_17_18`),
and the printed matrix gives a different verdict at `σ = κ = 1`, `β = 1/2`,
`φ_π = 3`, `φ_y = 0` (`printed_verdict_differs`).

## Main results

* `equilibrium_iff_solves`: the NKPC, DIS and rule (16) hold iff `(ỹ, π)` solves
  `x_t = A_F E_t x_{t+1}`.
* `schurStable_AF_iff`, `determinate_iff_17_18`: for `σ > 0`, `0 < β < 1`,
  `φ_y ≥ 0`, determinacy holds iff (17) `κ (φ_π − 1) + (1 − β) φ_y > 0` and
  (18) `κ (φ_π − 1) + (1 + β) φ_y < 2σ (1 + β)`.
* `equilibrium_iff_zero`, `exists_nonzero_equilibrium`: under (17)–(18),
  `ỹ = π = 0`, `i = r^n` is the unique bounded equilibrium; otherwise not.
* `fn7_implied`, `abs_det2_AF_lt_one_iff`: footnote 7, the Bullard–Mitra condition
  `φ_y < σ (1 + β⁻¹)` is `|det A_F| < 1` and is implied by (17)–(18).
* `determinate_contemporaneous_phiy_zero`, `determinate_forward_phiy_zero`: p. 110, with
  `φ_y = 0`: `φ_π > 1` for rule (11), `1 < φ_π < 1 + 2σ(1 + β)/κ` for rule (16).
* `boundary_eigenvalue_neg_one`, `not_determinate_at_boundary`: at
  `φ_π = 1 + 2σ(1 + β)/κ` the matrix `A_F` has the eigenvalue `−1` and the
  system is indeterminate, so the book's "no greater than" must be strict (C4-4).
-/

namespace Gali.MonetaryPolicyDesign.RuleForward

open Gali.MonetaryPolicyDesign.RuleExogenous

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (16), p. 108: the forward-looking rule
`i_t = r^n_t + φ_π E_t π_{t+1} + φ_y E_t ỹ_{t+1}`. -/
def ForwardRule (φπ φy : ℝ) (i rn infl ygap : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = rn t + φπ • 𝔼.E t (infl (t + 1)) + φy • 𝔼.E t (ygap (t + 1))

/-- Galí (2015), §4.3.1.3, p. 108: an equilibrium under rule (16): the DIS (6),
the NKPC (7) and the rule (16). -/
def Equilibrium (β σ κ φπ φy : ℝ) (rn ygap infl i : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl rn ∧ ForwardRule 𝔼 φπ φy i rn infl ygap

/-- Galí (2015), p. 108, **corrected** (C4-1): the system matrix under rule (16),
`A_F = [[1 − φ_y/σ, (1 − φ_π)/σ], [κ (1 − φ_y/σ), β + κ (1 − φ_π)/σ]]`. -/
noncomputable def AF (β σ κ φπ φy : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 - φy / σ, (1 - φπ) / σ; κ * (1 - φy / σ), β + κ * (1 - φπ) / σ]

/-- Galí (2015), p. 108, **as printed**: the `(2,2)` entry is `β − κ φ_π/σ`. -/
noncomputable def AFprinted (β σ κ φπ φy : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 - φy / σ, (1 - φπ) / σ; κ * (1 - φy / σ), β - κ * φπ / σ]

/-- Galí (2015), p. 108: given rule (16), the NKPC and the DIS hold iff
`x_t = (ỹ_t, π_t)` solves `x_t = A_F E_t x_{t+1}`, with the corrected `A_F`. -/
theorem nk_iff_solves {β σ κ φπ φy : ℝ} {rn ygap infl i : ℕ → Ω → ℝ}
    (hrule : ForwardRule 𝔼 φπ φy i rn infl ygap) :
    (NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl rn) ↔
      𝔼.Solves (AF β σ κ φπ φy) 0 (stack ygap infl) := by
  constructor
  · rintro ⟨hp, hd⟩ t j
    funext ω
    have e := congrFun (hd t) ω
    have p := congrFun (hp t) ω
    have r := congrFun (hrule t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e p r
    rw [r] at e
    fin_cases j
    · simp [stack, AF]
      linear_combination e
    · simp [stack, AF]
      linear_combination p + κ * e
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have e0 := congrFun (h t 0) ω
      have e1 := congrFun (h t 1) ω
      simp [stack, AF] at e0 e1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e1 - κ * e0
    · have e0 := congrFun (h t 0) ω
      have r := congrFun (hrule t) ω
      simp [stack, AF] at e0
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at r ⊢
      rw [r]
      linear_combination e0

/-- Galí (2015), p. 108: `(ỹ, π, i)` is an equilibrium under rule (16) iff
`(ỹ, π)` solves `x_t = A_F E_t x_{t+1}` and `i` is given by the rule. -/
theorem equilibrium_iff_solves {β σ κ φπ φy : ℝ} {rn ygap infl i : ℕ → Ω → ℝ} :
    Equilibrium 𝔼 β σ κ φπ φy rn ygap infl i ↔
      𝔼.Solves (AF β σ κ φπ φy) 0 (stack ygap infl) ∧ ForwardRule 𝔼 φπ φy i rn infl ygap := by
  constructor
  · rintro ⟨hp, hd, hr⟩
    exact ⟨(nk_iff_solves 𝔼 hr).mp ⟨hp, hd⟩, hr⟩
  · rintro ⟨hs, hr⟩
    obtain ⟨hp, hd⟩ := (nk_iff_solves 𝔼 hr).mpr hs
    exact ⟨hp, hd, hr⟩

/-- Galí (2015), p. 108: `ỹ = π = 0`, `i = r^n` is an equilibrium under rule (16). -/
theorem zero_equilibrium (β σ κ φπ φy : ℝ) (rn : ℕ → Ω → ℝ) :
    Equilibrium 𝔼 β σ κ φπ φy rn 0 0 rn := by
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩ <;> simp

/-- **C4-1** (Galí 2015, p. 108): the printed matrix differs from the system's
matrix whenever `κ ≠ 0` and `σ ≠ 0`; the `(2,2)` entries differ by `κ/σ`. -/
theorem AF_ne_AFprinted {β σ κ φπ φy : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) :
    AF β σ κ φπ φy ≠ AFprinted β σ κ φπ φy := by
  intro h
  have h11 := congrFun (congrFun h 1) 1
  simp only [AF, AFprinted, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h11
  have : κ / σ = 0 := by linear_combination h11
  exact div_ne_zero hκ hσ this

/-- The `(2,2)` entry of `A_F`: `β + κ (1 − φ_π)/σ` (Galí 2015, p. 108, corrected). -/
theorem AF_one_one (β σ κ φπ φy : ℝ) : AF β σ κ φπ φy 1 1 = β + κ * (1 - φπ) / σ := by
  simp [AF]

/-- The trace of `A_F`: `1 − φ_y/σ + β + κ (1 − φ_π)/σ` (Galí 2015, p. 108). -/
theorem tr2_AF (β σ κ φπ φy : ℝ) :
    tr2 (AF β σ κ φπ φy) = 1 - φy / σ + β + κ * (1 - φπ) / σ := by
  simp [tr2, AF]
  ring

/-- The determinant of `A_F`: `β (1 − φ_y/σ)` (Galí 2015, p. 108). -/
theorem det2_AF (β σ κ φπ φy : ℝ) : det2 (AF β σ κ φπ φy) = β * (1 - φy / σ) := by
  simp [det2, AF]
  ring

/-- Galí (2015), fn. 7, p. 108: for `σ > 0`, `0 < β < 1` and `φ_y ≥ 0`, the
Bullard–Mitra condition `φ_y < σ (1 + β⁻¹)` is exactly `|det A_F| < 1`. -/
theorem abs_det2_AF_lt_one_iff {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφy : 0 ≤ φy) : |det2 (AF β σ κ φπ φy)| < 1 ↔ φy < σ * (1 + β⁻¹) := by
  rw [det2_AF, abs_lt]
  have hD1 : β * (1 - φy / σ) < 1 := by
    have : 0 ≤ φy / σ := div_nonneg hφy hσ.le
    nlinarith
  have key : -1 < β * (1 - φy / σ) ↔ φy < σ * (1 + β⁻¹) := by
    have e : β * (1 - φy / σ) + 1 = β * (σ * (1 + β⁻¹) - φy) / σ := by
      field_simp
      ring
    rw [← sub_pos (a := β * (1 - φy / σ)), sub_neg_eq_add, e,
      div_pos_iff_of_pos_right hσ, mul_pos_iff_of_pos_left hβ0, sub_pos]
  rw [key]
  exact ⟨fun h => h.1, fun h => ⟨h, hD1⟩⟩

/-- **Galí (2015), fn. 7, p. 108**: conditions (17) and (18) imply the third
Bullard–Mitra condition `φ_y < σ (1 + β⁻¹)` (adding them gives
`2β φ_y < 2σ (1 + β)`). -/
theorem fn7_implied {β σ κ φπ φy : ℝ} (hβ0 : 0 < β)
    (h17 : 0 < κ * (φπ - 1) + (1 - β) * φy)
    (h18 : κ * (φπ - 1) + (1 + β) * φy < 2 * σ * (1 + β)) : φy < σ * (1 + β⁻¹) := by
  have h : β * φy < β * (σ * (1 + β⁻¹)) := by
    have e : β * (σ * (1 + β⁻¹)) = σ * (1 + β) := by field_simp; ring
    rw [e]; linarith
  exact lt_of_mul_lt_mul_left h hβ0.le

/-- **Determinacy conditions (17)–(18)** (Galí 2015, p. 108, for the corrected
`A_F`): for `σ > 0`, `0 < β < 1` and `φ_y ≥ 0`, both eigenvalues of `A_F` lie
inside the unit circle iff `κ (φ_π − 1) + (1 − β) φ_y > 0` and
`κ (φ_π − 1) + (1 + β) φ_y < 2σ (1 + β)`. -/
theorem schurStable_AF_iff {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφy : 0 ≤ φy) :
    SchurStable (tr2 (AF β σ κ φπ φy)) (det2 (AF β σ κ φπ φy)) ↔
      0 < κ * (φπ - 1) + (1 - β) * φy ∧
        κ * (φπ - 1) + (1 + β) * φy < 2 * σ * (1 + β) := by
  have e1 : 1 + det2 (AF β σ κ φπ φy) - tr2 (AF β σ κ φπ φy)
      = (κ * (φπ - 1) + (1 - β) * φy) / σ := by
    rw [tr2_AF, det2_AF]; field_simp; ring
  have e2 : 1 + det2 (AF β σ κ φπ φy) + tr2 (AF β σ κ φπ φy)
      = (2 * σ * (1 + β) - (κ * (φπ - 1) + (1 + β) * φy)) / σ := by
    rw [tr2_AF, det2_AF]; field_simp; ring
  have hT : |tr2 (AF β σ κ φπ φy)| < 1 + det2 (AF β σ κ φπ φy) ↔
      0 < κ * (φπ - 1) + (1 - β) * φy ∧
        κ * (φπ - 1) + (1 + β) * φy < 2 * σ * (1 + β) := by
    rw [abs_lt]
    constructor
    · rintro ⟨h1, h2⟩
      have a : 0 < 1 + det2 (AF β σ κ φπ φy) - tr2 (AF β σ κ φπ φy) := by linarith
      have b : 0 < 1 + det2 (AF β σ κ φπ φy) + tr2 (AF β σ κ φπ φy) := by linarith
      rw [e1, div_pos_iff_of_pos_right hσ] at a
      rw [e2, div_pos_iff_of_pos_right hσ] at b
      exact ⟨a, by linarith⟩
    · rintro ⟨h1, h2⟩
      have a : 0 < 1 + det2 (AF β σ κ φπ φy) - tr2 (AF β σ κ φπ φy) := by
        rw [e1]; exact div_pos h1 hσ
      have b : 0 < 1 + det2 (AF β σ κ φπ φy) + tr2 (AF β σ κ φπ φy) := by
        rw [e2]; exact div_pos (by linarith) hσ
      constructor <;> linarith
  unfold SchurStable
  rw [hT, abs_det2_AF_lt_one_iff hσ hβ0 hβ1 hφy]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨fn7_implied hβ0 h.1 h.2, h⟩

/-- Galí (2015), eqs. (17)–(18), p. 108: under rule (16) (for `σ > 0`,
`0 < β < 1`, `φ_y ≥ 0`) the system is determinate iff (17) and (18) hold. -/
theorem determinate_iff_17_18 [Nonempty Ω] {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy) :
    𝔼.Determinate (AF β σ κ φπ φy) ↔
      0 < κ * (φπ - 1) + (1 - β) * φy ∧
        κ * (φπ - 1) + (1 + β) * φy < 2 * σ * (1 + β) :=
  (𝔼.determinate_iff _).trans (schurStable_AF_iff hσ hβ0 hβ1 hφy)

/-- **Implementation under rule (16)** (Galí 2015, pp. 108–109): under (17) and
(18), `ỹ = π = 0` and `i = r^n` is the unique equilibrium with bounded adapted
output gap and inflation. -/
theorem equilibrium_iff_zero {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφy : 0 ≤ φy) (h17 : 0 < κ * (φπ - 1) + (1 - β) * φy)
    (h18 : κ * (φπ - 1) + (1 + β) * φy < 2 * σ * (1 + β))
    {rn ygap infl i : ℕ → Ω → ℝ} (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl)
    (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    Equilibrium 𝔼 β σ κ φπ φy rn ygap infl i ↔ ygap = 0 ∧ infl = 0 ∧ i = rn := by
  constructor
  · intro he
    obtain ⟨hx, hr⟩ := (equilibrium_iff_solves 𝔼).mp he
    obtain ⟨h0, -⟩ := (equilibrium_iff_solves 𝔼).mp (zero_equilibrium 𝔼 β σ κ φπ φy rn)
    have heq := 𝔼.system_unique ((schurStable_AF_iff hσ hβ0 hβ1 hφy).mpr ⟨h17, h18⟩) hx h0
      (adaptedVec_stack 𝔼 ha hb) (adaptedVec_stack 𝔼 (fun t => by simp) (fun t => by simp))
      (boundedVec_stack hba hbb) (boundedVec_stack ⟨0, fun t ω => by simp⟩
        ⟨0, fun t ω => by simp⟩)
    have h1 : ygap = 0 := funext fun t => by
      simpa [stack] using congrFun (congrFun heq t) 0
    have h2 : infl = 0 := funext fun t => by
      simpa [stack] using congrFun (congrFun heq t) 1
    refine ⟨h1, h2, funext fun t => ?_⟩
    rw [hr t, h1, h2]
    simp
  · rintro ⟨h1, h2, h3⟩
    rw [h1, h2, h3]
    exact zero_equilibrium 𝔼 β σ κ φπ φy rn

/-- **Indeterminacy without (17)–(18)** (Galí 2015, p. 108): if (17) or (18)
fails (with `σ > 0`, `0 < β < 1`, `φ_y ≥ 0`), there is an equilibrium under rule
(16) with bounded adapted output gap and inflation other than `ỹ = π = 0`. -/
theorem exists_nonzero_equilibrium [Nonempty Ω] {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy)
    (hfail : ¬ (0 < κ * (φπ - 1) + (1 - β) * φy ∧
      κ * (φπ - 1) + (1 + β) * φy < 2 * σ * (1 + β))) (rn : ℕ → Ω → ℝ) :
    ∃ ygap infl i, Equilibrium 𝔼 β σ κ φπ φy rn ygap infl i ∧
      𝔼.Adapted ygap ∧ 𝔼.Adapted infl ∧ BoundedProc ygap ∧ BoundedProc infl ∧
      (ygap ≠ 0 ∨ infl ≠ 0) := by
  have hns : ¬ SchurStable (tr2 (AF β σ κ φπ φy)) (det2 (AF β σ κ φπ φy)) := by
    rw [schurStable_AF_iff hσ hβ0 hβ1 hφy]; exact hfail
  obtain ⟨h0, -⟩ := (equilibrium_iff_solves 𝔼).mp (zero_equilibrium 𝔼 β σ κ φπ φy rn)
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ := 𝔼.system_not_unique hns h0
    (adaptedVec_stack 𝔼 (fun t => by simp) (fun t => by simp))
    (boundedVec_stack ⟨0, fun t ω => by simp⟩ ⟨0, fun t ω => by simp⟩)
  have hst : stack (fun t => y t 0) (fun t => y t 1) = y := by
    funext t j
    fin_cases j <;> rfl
  refine ⟨fun t => y t 0, fun t => y t 1,
    fun t => rn t + φπ • 𝔼.E t (y (t + 1) 1) + φy • 𝔼.E t (y (t + 1) 0),
    (equilibrium_iff_solves 𝔼).mpr ⟨hst ▸ hy, fun t => rfl⟩,
    fun t => hay t 0, fun t => hay t 1, ⟨M, fun t ω => hM t 0 ω⟩,
    ⟨M, fun t ω => hM t 1 ω⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hst, hcon.1, hcon.2]

/-! ### The printed matrix gives the wrong verdict (C4-1) -/

/-- **C4-1** (Galí 2015, p. 108): at `σ = κ = 1`, `β = 1/2`, `φ_π = 3`,
`φ_y = 0`, conditions (17)–(18) hold and the corrected `A_F` satisfies the
Schur–Cohn condition, but the printed matrix does not (its trace is `−3/2` and its
determinant `−1/2`). -/
theorem printed_verdict_differs :
    (0 < (1 : ℝ) * (3 - 1) + (1 - 1 / 2) * 0 ∧
      (1 : ℝ) * (3 - 1) + (1 + 1 / 2) * 0 < 2 * 1 * (1 + 1 / 2)) ∧
    SchurStable (tr2 (AF (1 / 2) 1 1 3 0)) (det2 (AF (1 / 2) 1 1 3 0)) ∧
    ¬ SchurStable (tr2 (AFprinted (1 / 2) 1 1 3 0)) (det2 (AFprinted (1 / 2) 1 1 3 0)) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [schurStable_AF_iff (by norm_num) (by norm_num) (by norm_num) le_rfl]
    norm_num
  · simp only [SchurStable, tr2, det2, AFprinted, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    norm_num [abs_of_neg]

/-- **C4-1, in terms of equilibria** (Galí 2015, p. 108): at `σ = κ = 1`,
`β = 1/2`, `φ_π = 3`, `φ_y = 0`, the system under rule (16) is determinate, but the
printed system is not; so the printed matrix does not describe the equilibrium
conditions. -/
theorem printed_determinacy_differs [Nonempty Ω] :
    𝔼.Determinate (AF (1 / 2) 1 1 3 0) ∧ ¬ 𝔼.Determinate (AFprinted (1 / 2) 1 1 3 0) := by
  rw [𝔼.determinate_iff, 𝔼.determinate_iff]
  exact ⟨printed_verdict_differs.2.1, printed_verdict_differs.2.2⟩

/-- **C4-1, a solution of the printed system that is not an equilibrium**
(Galí 2015, p. 108): at `σ = κ = 1`, `β = 1/2`, `φ_π = 3`, `φ_y = 0` there is a
bounded adapted `(ỹ, π) ≠ (0, 0)` solving `x_t = A_F^{printed} E_t x_{t+1}` that is
not an equilibrium under rule (16) for any nominal-rate path. -/
theorem printed_solution_not_equilibrium [Nonempty Ω] (rn : ℕ → Ω → ℝ) :
    ∃ ygap infl : ℕ → Ω → ℝ, 𝔼.Solves (AFprinted (1 / 2) 1 1 3 0) 0 (stack ygap infl) ∧
      𝔼.Adapted ygap ∧ 𝔼.Adapted infl ∧ BoundedProc ygap ∧ BoundedProc infl ∧
      ∀ i, ¬ Equilibrium 𝔼 (1 / 2) 1 1 3 0 rn ygap infl i := by
  have hz : 𝔼.Solves (AFprinted (1 / 2) 1 1 3 0) 0 0 := fun t j => by simp
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ := 𝔼.system_not_unique printed_verdict_differs.2.2 hz
    (fun t j => by simp) ⟨0, fun t j ω => by simp⟩
  have hst : stack (fun t => y t 0) (fun t => y t 1) = y := by
    funext t j
    fin_cases j <;> rfl
  refine ⟨fun t => y t 0, fun t => y t 1, hst ▸ hy, fun t => hay t 0, fun t => hay t 1,
    ⟨M, fun t ω => hM t 0 ω⟩, ⟨M, fun t ω => hM t 1 ω⟩, fun i he => ?_⟩
  obtain ⟨hx, -⟩ := (equilibrium_iff_solves 𝔼).mp he
  have hz' : 𝔼.Solves (AF (1 / 2) 1 1 3 0) 0 0 := fun t j => by simp
  have hax : 𝔼.AdaptedVec (stack (fun t => y t 0) (fun t => y t 1)) := by
    rw [hst]; exact hay
  have hbx : BoundedVec (stack (fun t => y t 0) (fun t => y t 1)) := by
    rw [hst]; exact ⟨M, hM⟩
  have heq := 𝔼.system_unique printed_verdict_differs.2.1 hx hz'
    hax (fun t j => by simp) hbx ⟨0, fun t j ω => by simp⟩
  rw [hst] at heq
  exact hne heq

/-! ### Rules without an output-gap response (p. 110) -/

/-- Galí (2015), p. 110: with `φ_y = 0` the contemporaneous rule (11) (with
`φ_π ≥ 0`) is determinate iff `φ_π > 1`. -/
theorem determinate_contemporaneous_phiy_zero [Nonempty Ω] {β σ κ φπ : ℝ} (hσ : 0 < σ)
    (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) :
    𝔼.Determinate (RuleTaylorPrinciple.AT β σ κ φπ 0) ↔ 1 < φπ := by
  rw [RuleTaylorPrinciple.determinate_iff_14 𝔼 hσ hκ hβ0 hβ1 hφπ le_rfl, mul_zero, add_zero,
    mul_pos_iff_of_pos_left hκ, sub_pos]

/-- **Galí (2015), p. 110 (with C4-4)**: with `φ_y = 0` the forward-looking rule
(16) is determinate iff `1 < φ_π < 1 + 2σ (1 + β)/κ`, both inequalities strict. -/
theorem determinate_forward_phiy_zero [Nonempty Ω] {β σ κ φπ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    𝔼.Determinate (AF β σ κ φπ 0) ↔ 1 < φπ ∧ φπ < 1 + 2 * σ * (1 + β) / κ := by
  rw [determinate_iff_17_18 𝔼 hσ hβ0 hβ1 le_rfl]
  simp only [mul_zero, add_zero]
  rw [mul_pos_iff_of_pos_left hκ, sub_pos]
  have e : κ * (φπ - 1) < 2 * σ * (1 + β) ↔ φπ < 1 + 2 * σ * (1 + β) / κ := by
    rw [← sub_lt_iff_lt_add', lt_div_iff₀ hκ, mul_comm]
  rw [e]

/-- **C4-4** (Galí 2015, p. 110): at the boundary `φ_π = 1 + 2σ (1 + β)/κ`,
`φ_y = 0`, the matrix `A_F` has the eigenvalue `−1`:
`det (−I − A_F) = 1 + tr A_F + det A_F = 0`. -/
theorem boundary_eigenvalue_neg_one {β σ κ : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) :
    Matrix.det ((-1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
      - AF β σ κ (1 + 2 * σ * (1 + β) / κ) 0) = 0 := by
  rw [Matrix.det_fin_two]
  simp [AF]
  field_simp
  ring

/-- **C4-4** (Galí 2015, p. 110): the book's "no greater than `1 + 2σ(1 + β)/κ`"
is not sufficient: at `φ_π = 1 + 2σ (1 + β)/κ` (which satisfies `1 < φ_π`),
`φ_y = 0`, the system under rule (16) is indeterminate. -/
theorem not_determinate_at_boundary [Nonempty Ω] {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    1 < 1 + 2 * σ * (1 + β) / κ ∧
      ¬ 𝔼.Determinate (AF β σ κ (1 + 2 * σ * (1 + β) / κ) 0) := by
  refine ⟨by have : 0 < 2 * σ * (1 + β) / κ := by positivity
             linarith, ?_⟩
  rw [determinate_forward_phiy_zero 𝔼 hσ hκ hβ0 hβ1]
  exact fun h => lt_irrefl _ h.2

end Gali.MonetaryPolicyDesign.RuleForward
