/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MonetaryPolicyDesign.RuleExogenous

/-!
# An interest-rate rule with an endogenous component: the Taylor principle

Galí (2015), Chapter 4, §4.3.1.2, pp. 105–107. With the NKPC
`π_t = β E_t π_{t+1} + κ ỹ_t` and the DIS
`ỹ_t = E_t ỹ_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − r^n_t)` (eqs. (6)–(7), stated in
`RuleExogenous`), the rule (11) `i_t = r^n_t + φ_π π_t + φ_y ỹ_t` gives the system
(12) `x_t = A_T E_t x_{t+1}` with (13)
`A_T = Ω [[σ, 1 − βφ_π], [σκ, κ + β(σ + φ_y)]]`, `Ω = 1/(σ + φ_y + κφ_π)`.

## Main results

* `equilibrium_iff_solves`: the NKPC, DIS and rule (11) hold iff `(ỹ, π)` solves (12).
* `schurStable_AT_iff`, `determinate_iff_14` (Bullard–Mitra): for `φ_π, φ_y ≥ 0`
  the system is determinate iff (14) `κ (φ_π − 1) + (1 − β) φ_y > 0`.
* `equilibrium_iff_zero`: under (14), `ỹ = π = 0`, `i = r^n` is THE unique
  equilibrium with bounded adapted output gap and inflation.
* `exists_nonzero_equilibrium`: without (14) there is a bounded equilibrium
  other than `ỹ = π = 0`.
* `tendsto_gap_of_tendsto_infl`, `tendsto_rate_of_tendsto_infl`: eq. (15): after
  a permanent change of inflation to `π̄` the NKPC forces `ỹ → (1 − β) π̄/κ`
  and the rule gives `i_t − r^n_t → (φ_π + φ_y (1 − β)/κ) π̄`.
* `taylorPrinciple_iff`: (14) holds iff the long-run response (15) exceeds one;
  `tendsto_realRate_of_tendsto_infl`: then the real rate eventually rises.
-/

namespace Gali.MonetaryPolicyDesign.RuleTaylorPrinciple

open Filter Topology Gali.MonetaryPolicyDesign.RuleExogenous

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (11), p. 105: the rule `i_t = r^n_t + φ_π π_t + φ_y ỹ_t`. -/
def TaylorRule (φπ φy : ℝ) (i rn infl ygap : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = rn t + φπ • infl t + φy • ygap t

/-- Galí (2015), §4.3.1.2, p. 105: an equilibrium under rule (11): the DIS (6),
the NKPC (7) and the rule (11). -/
def Equilibrium (β σ κ φπ φy : ℝ) (rn ygap infl i : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl rn ∧ TaylorRule φπ φy i rn infl ygap

/-- Galí (2015), p. 105: `Ω = 1/(σ + φ_y + κ φ_π)`. -/
noncomputable def omega (σ κ φπ φy : ℝ) : ℝ := 1 / (σ + φy + κ * φπ)

/-- Galí (2015), eq. (13), p. 105:
`A_T = Ω [[σ, 1 − βφ_π], [σκ, κ + β(σ + φ_y)]]`. -/
noncomputable def AT (β σ κ φπ φy : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![omega σ κ φπ φy * σ, omega σ κ φπ φy * (1 - β * φπ);
    omega σ κ φπ φy * (σ * κ), omega σ κ φπ φy * (κ + β * (σ + φy))]

/-- Galí (2015), eqs. (12)–(13), p. 105: given rule (11), the NKPC and the DIS
hold iff `x_t = (ỹ_t, π_t)` solves `x_t = A_T E_t x_{t+1}` (for `σ ≠ 0` and
`σ + φ_y + κ φ_π ≠ 0`). Adapted from the Chapter 3 project. -/
theorem nk_iff_solves {β σ κ φπ φy : ℝ} (hσ : σ ≠ 0) (hS : σ + φy + κ * φπ ≠ 0)
    {rn ygap infl i : ℕ → Ω → ℝ} (hrule : TaylorRule φπ φy i rn infl ygap) :
    (NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl rn) ↔
      𝔼.Solves (AT β σ κ φπ φy) 0 (stack ygap infl) := by
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  constructor
  · rintro ⟨hp, hd⟩ t j
    funext ω
    have e := congrFun (hd t) ω
    have p := congrFun (hp t) ω
    have r := congrFun (hrule t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e p r
    -- the structural form `(σ + φ_y) ỹ_t + φ_π π_t = σ E_t ỹ_{t+1} + E_t π_{t+1}`
    have s : (σ + φy) * ygap t ω + φπ * infl t ω
        = σ * 𝔼.E t (ygap (t + 1)) ω + 𝔼.E t (infl (t + 1)) ω := by
      linear_combination σ * e - r - (i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) * hinv
    fin_cases j
    · simp [stack, AT, omega]
      field_simp
      linear_combination s - φπ * p
    · simp [stack, AT, omega]
      field_simp
      linear_combination κ * s + (σ + φy) * p
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have e0 := congrFun (h t 0) ω
      have e1 := congrFun (h t 1) ω
      simp [stack, AT, omega] at e0 e1
      field_simp at e0 e1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      apply mul_left_cancel₀ hS
      linear_combination e1 - κ * e0
    · have e0 := congrFun (h t 0) ω
      have e1 := congrFun (h t 1) ω
      have r := congrFun (hrule t) ω
      simp [stack, AT, omega] at e0 e1
      field_simp at e0 e1
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at r ⊢
      have s : (σ + φy) * ygap t ω + φπ * infl t ω
          = σ * 𝔼.E t (ygap (t + 1)) ω + 𝔼.E t (infl (t + 1)) ω := by
        apply mul_left_cancel₀ hS
        linear_combination (σ + φy) * e0 + φπ * e1
      rw [r]
      linear_combination σ⁻¹ * s - (ygap t ω - 𝔼.E t (ygap (t + 1)) ω) * hinv

/-- Galí (2015), eqs. (11)–(13), p. 105: `(ỹ, π, i)` is an equilibrium under
rule (11) iff `(ỹ, π)` solves (12) and `i` is given by the rule. -/
theorem equilibrium_iff_solves {β σ κ φπ φy : ℝ} (hσ : σ ≠ 0) (hS : σ + φy + κ * φπ ≠ 0)
    {rn ygap infl i : ℕ → Ω → ℝ} :
    Equilibrium 𝔼 β σ κ φπ φy rn ygap infl i ↔
      𝔼.Solves (AT β σ κ φπ φy) 0 (stack ygap infl) ∧ TaylorRule φπ φy i rn infl ygap := by
  constructor
  · rintro ⟨hp, hd, hr⟩
    exact ⟨(nk_iff_solves 𝔼 hσ hS hr).mp ⟨hp, hd⟩, hr⟩
  · rintro ⟨hs, hr⟩
    obtain ⟨hp, hd⟩ := (nk_iff_solves 𝔼 hσ hS hr).mpr hs
    exact ⟨hp, hd, hr⟩

/-- Galí (2015), p. 106: `ỹ = π = 0`, `i = r^n` is always an equilibrium under
rule (11). -/
theorem zero_equilibrium (β σ κ φπ φy : ℝ) (rn : ℕ → Ω → ℝ) :
    Equilibrium 𝔼 β σ κ φπ φy rn 0 0 rn := by
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩ <;> simp

/-- The trace of `A_T`: `(σ (1 + β) + κ + β φ_y)/(σ + φ_y + κ φ_π)` (Galí 2015,
eq. (13), p. 105). Restated from the Chapter 3 project. -/
theorem tr2_AT {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0) :
    tr2 (AT β σ κ φπ φy) = (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) := by
  simp only [tr2, AT, omega, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- The determinant of `A_T`: `σ β/(σ + φ_y + κ φ_π)` (Galí 2015, eq. (13),
p. 105). Restated from the Chapter 3 project. -/
theorem det2_AT {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0) :
    det2 (AT β σ κ φπ φy) = σ * β / (σ + φy + κ * φπ) := by
  simp only [det2, AT, omega, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- **Bullard–Mitra** (Galí 2015, eq. (14), p. 106): for `σ, κ > 0`,
`0 < β < 1` and `φ_π, φ_y ≥ 0`, both eigenvalues of `A_T` lie inside the unit
circle iff `κ (φ_π − 1) + (1 − β) φ_y > 0`. Restated from the Chapter 3 project. -/
theorem schurStable_AT_iff {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    SchurStable (tr2 (AT β σ κ φπ φy)) (det2 (AT β σ κ φπ φy)) ↔
      0 < κ * (φπ - 1) + (1 - β) * φy := by
  have hS : 0 < σ + φy + κ * φπ := by positivity
  rw [tr2_AT hS.ne', det2_AT hS.ne']
  have hD0 : 0 < σ * β / (σ + φy + κ * φπ) := by positivity
  have hD1 : σ * β / (σ + φy + κ * φπ) < 1 := by
    rw [div_lt_one hS]; nlinarith
  have hT0 : 0 < (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) := by positivity
  unfold SchurStable
  rw [abs_of_pos hD0, abs_of_pos hT0]
  have key : (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) < 1 + σ * β / (σ + φy + κ * φπ)
      ↔ σ * (1 + β) + κ + β * φy < σ + φy + κ * φπ + σ * β := by
    rw [one_add_div hS.ne', div_lt_div_iff_of_pos_right hS]
  rw [key]
  constructor
  · rintro ⟨-, h⟩; linarith
  · intro h; exact ⟨hD1, by linarith⟩

/-- Galí (2015), eq. (14), p. 106: under rule (11) with `φ_π, φ_y ≥ 0` the system
(12) is determinate (at most one bounded adapted solution for every forcing)
iff `κ (φ_π − 1) + (1 − β) φ_y > 0`. -/
theorem determinate_iff_14 [Nonempty Ω] {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    𝔼.Determinate (AT β σ κ φπ φy) ↔ 0 < κ * (φπ - 1) + (1 - β) * φy :=
  (𝔼.determinate_iff _).trans (schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy)

/-- **Implementation of the optimal policy** (Galí 2015, p. 106): under (14),
`ỹ = π = 0` and `i = r^n` is the unique equilibrium under rule (11) with bounded
adapted output gap and inflation. -/
theorem equilibrium_iff_zero {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (h14 : 0 < κ * (φπ - 1) + (1 - β) * φy)
    {rn ygap infl i : ℕ → Ω → ℝ} (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl)
    (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    Equilibrium 𝔼 β σ κ φπ φy rn ygap infl i ↔ ygap = 0 ∧ infl = 0 ∧ i = rn := by
  have hS : σ + φy + κ * φπ ≠ 0 := by positivity
  constructor
  · intro he
    obtain ⟨hx, hr⟩ := (equilibrium_iff_solves 𝔼 hσ.ne' hS).mp he
    obtain ⟨h0, -⟩ := (equilibrium_iff_solves 𝔼 hσ.ne' hS).mp (zero_equilibrium 𝔼 β σ κ φπ φy rn)
    have heq := 𝔼.system_unique ((schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy).mpr h14) hx h0
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

/-- **Indeterminacy without (14)** (Galí 2015, p. 106): if `φ_π, φ_y ≥ 0` and
`κ (φ_π − 1) + (1 − β) φ_y ≤ 0`, there is an equilibrium under rule (11) with
bounded adapted output gap and inflation other than `ỹ = π = 0`. -/
theorem exists_nonzero_equilibrium [Nonempty Ω] {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy)
    (h14 : κ * (φπ - 1) + (1 - β) * φy ≤ 0) (rn : ℕ → Ω → ℝ) :
    ∃ ygap infl i, Equilibrium 𝔼 β σ κ φπ φy rn ygap infl i ∧
      𝔼.Adapted ygap ∧ 𝔼.Adapted infl ∧ BoundedProc ygap ∧ BoundedProc infl ∧
      (ygap ≠ 0 ∨ infl ≠ 0) := by
  have hS : σ + φy + κ * φπ ≠ 0 := by positivity
  have hns : ¬ SchurStable (tr2 (AT β σ κ φπ φy)) (det2 (AT β σ κ φπ φy)) := by
    rw [schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy]; linarith
  obtain ⟨h0, -⟩ := (equilibrium_iff_solves 𝔼 hσ.ne' hS).mp (zero_equilibrium 𝔼 β σ κ φπ φy rn)
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ := 𝔼.system_not_unique hns h0
    (adaptedVec_stack 𝔼 (fun t => by simp) (fun t => by simp))
    (boundedVec_stack ⟨0, fun t ω => by simp⟩ ⟨0, fun t ω => by simp⟩)
  have hst : stack (fun t => y t 0) (fun t => y t 1) = y := by
    funext t j
    fin_cases j <;> rfl
  refine ⟨fun t => y t 0, fun t => y t 1,
    fun t => rn t + φπ • y t 1 + φy • y t 0,
    (equilibrium_iff_solves 𝔼 hσ.ne' hS).mpr ⟨hst ▸ hy, fun t => rfl⟩,
    fun t => hay t 0, fun t => hay t 1, ⟨M, fun t ω => hM t 0 ω⟩,
    ⟨M, fun t ω => hM t 1 ω⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hst, hcon.1, hcon.2]

/-! ### The long-run response (15) and the Taylor principle -/

/-- Galí (2015), eq. (15), p. 106: the long-run response of the nominal rate to a
permanent change in inflation, `φ_π + φ_y (1 − β)/κ`. -/
noncomputable def longRunResponse (β κ φπ φy : ℝ) : ℝ := φπ + φy * (1 - β) / κ

/-- Galí (2015), p. 106: the long-run relation implied by (7). If inflation
converges to `π̄` (both `π_t` and `E_t π_{t+1}`, as after a permanent change in
inflation), the NKPC forces the output gap to converge to `(1 − β) π̄/κ`. -/
theorem tendsto_gap_of_tendsto_infl {β κ : ℝ} (hκ : κ ≠ 0) {ygap infl : ℕ → Ω → ℝ}
    (hp : NKPC 𝔼 β κ ygap infl) {pibar : ℝ} (ω : Ω)
    (h1 : Tendsto (fun t => infl t ω) atTop (𝓝 pibar))
    (h2 : Tendsto (fun t => 𝔼.E t (infl (t + 1)) ω) atTop (𝓝 pibar)) :
    Tendsto (fun t => ygap t ω) atTop (𝓝 ((1 - β) * pibar / κ)) := by
  have he : (fun t => ygap t ω) = fun t => κ⁻¹ * (infl t ω - β * 𝔼.E t (infl (t + 1)) ω) := by
    funext t
    have p := congrFun (hp t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at p
    field_simp
    linear_combination -p
  rw [he]
  have hl := (h1.sub (h2.const_mul β)).const_mul κ⁻¹
  convert hl using 2
  field_simp

/-- **Eq. (15)** (Galí 2015, p. 106): after a permanent change of inflation to `π̄`
(with `r^n` held fixed by measuring `i_t − r^n_t`), rule (11) and the NKPC give
`i_t − r^n_t → (φ_π + φ_y (1 − β)/κ) π̄`. -/
theorem tendsto_rate_of_tendsto_infl {β κ φπ φy : ℝ} (hκ : κ ≠ 0)
    {rn ygap infl i : ℕ → Ω → ℝ} (hp : NKPC 𝔼 β κ ygap infl)
    (hr : TaylorRule φπ φy i rn infl ygap) {pibar : ℝ} (ω : Ω)
    (h1 : Tendsto (fun t => infl t ω) atTop (𝓝 pibar))
    (h2 : Tendsto (fun t => 𝔼.E t (infl (t + 1)) ω) atTop (𝓝 pibar)) :
    Tendsto (fun t => i t ω - rn t ω) atTop (𝓝 (longRunResponse β κ φπ φy * pibar)) := by
  have he : (fun t => i t ω - rn t ω) = fun t => φπ * infl t ω + φy * ygap t ω := by
    funext t
    have r := congrFun (hr t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at r
    linear_combination r
  rw [he]
  have hl := (h1.const_mul φπ).add ((tendsto_gap_of_tendsto_infl 𝔼 hκ hp ω h1 h2).const_mul φy)
  convert hl using 2
  unfold longRunResponse
  field_simp

/-- **The Taylor principle** (Galí 2015, p. 107): for `κ > 0`, condition (14)
holds iff the long-run response (15) of the nominal rate to inflation is
greater than one. -/
theorem taylorPrinciple_iff {β κ φπ φy : ℝ} (hκ : 0 < κ) :
    0 < κ * (φπ - 1) + (1 - β) * φy ↔ 1 < longRunResponse β κ φπ φy := by
  have h : longRunResponse β κ φπ φy - 1 = (κ * (φπ - 1) + (1 - β) * φy) / κ := by
    unfold longRunResponse
    field_simp
    ring
  rw [← sub_pos (a := longRunResponse β κ φπ φy) (b := 1), h, div_pos_iff_of_pos_right hκ]

/-- Galí (2015), p. 107: the long-run response of the real rate `i_t − E_t π_{t+1}`
(net of `r^n_t`) to a permanent change of inflation to `π̄` is
`(φ_π + φ_y (1 − β)/κ − 1) π̄`. -/
theorem tendsto_realRate_of_tendsto_infl {β κ φπ φy : ℝ} (hκ : κ ≠ 0)
    {rn ygap infl i : ℕ → Ω → ℝ} (hp : NKPC 𝔼 β κ ygap infl)
    (hr : TaylorRule φπ φy i rn infl ygap) {pibar : ℝ} (ω : Ω)
    (h1 : Tendsto (fun t => infl t ω) atTop (𝓝 pibar))
    (h2 : Tendsto (fun t => 𝔼.E t (infl (t + 1)) ω) atTop (𝓝 pibar)) :
    Tendsto (fun t => i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) atTop
      (𝓝 ((longRunResponse β κ φπ φy - 1) * pibar)) := by
  have hl := (tendsto_rate_of_tendsto_infl 𝔼 hκ hp hr ω h1 h2).sub h2
  convert hl using 2 <;> ring

/-- **The real rate eventually rises** (Galí 2015, p. 107): under (14), after a
permanent increase of inflation to `π̄ > 0` the real rate (net of `r^n_t`) is
eventually positive. -/
theorem realRate_eventually_pos {β κ φπ φy : ℝ} (hκ : 0 < κ)
    (h14 : 0 < κ * (φπ - 1) + (1 - β) * φy) {rn ygap infl i : ℕ → Ω → ℝ}
    (hp : NKPC 𝔼 β κ ygap infl) (hr : TaylorRule φπ φy i rn infl ygap) {pibar : ℝ}
    (hpi : 0 < pibar) (ω : Ω) (h1 : Tendsto (fun t => infl t ω) atTop (𝓝 pibar))
    (h2 : Tendsto (fun t => 𝔼.E t (infl (t + 1)) ω) atTop (𝓝 pibar)) :
    ∀ᶠ t in atTop, 0 < i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω := by
  have hpos : 0 < (longRunResponse β κ φπ φy - 1) * pibar :=
    mul_pos (sub_pos.mpr ((taylorPrinciple_iff hκ).mp h14)) hpi
  exact (tendsto_realRate_of_tendsto_infl 𝔼 hκ.ne' hp hr ω h1 h2).eventually
    (lt_mem_nhds hpos)

end Gali.MonetaryPolicyDesign.RuleTaylorPrinciple
