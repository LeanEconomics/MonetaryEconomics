/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.DIS

/-!
# Equilibrium under a simple interest-rate rule

Galí (2015), Chapter 3, §3.4.1, pp. 64–66. The non-policy block of the basic
New Keynesian model is the NKPC `π_t = β E_t π_{t+1} + κ ỹ_t` (eq. (22), with
`κ > 0` a parameter) and the DIS equation (23). Monetary policy follows the
Taylor-type rule (26), `i_t = ρ + φ_π π_t + φ_y ŷ_t + v_t`.

## Main results

* `taylorRule_iff_gap`: the rule rewritten with the output gap (p. 65).
* `equilibrium_iff_solves`: the NKPC, the DIS and the rule hold if and only
  if `(ỹ, π)` solves the system (27), `x_t = A_T E_t x_{t+1} + B_T u_t`, with
  `A_T = Ω [[σ, 1 − βφ_π], [σκ, κ + β(σ + φ_y)]]` and `Ω = 1/(σ + φ_y + κφ_π)`.
* `schurStable_AT_iff` (**Bullard–Mitra**): for `σ, κ > 0`, `0 < β < 1` and
  `φ_π, φ_y ≥ 0`, both eigenvalues of `A_T` lie inside the unit circle iff
  `κ (φ_π − 1) + (1 − β) φ_y > 0`, condition (28).
* `determinate_iff_BM`, `equilibrium_unique`, `equilibrium_not_unique`: the
  equilibrium is determinate iff (28) holds; under (28) bounded equilibria
  coincide, and without it every bounded equilibrium has a second one.
* `msvLambda_pos`, `msv_structural`, `equilibrium_iff_msv`: for an AR(1)
  composite shock `u` the MSV solution (29)–(30), `ỹ_t = (1 − βρ_u) Λ_u u_t`,
  `π_t = κ Λ_u u_t`, has `Λ_u > 0` under (28) for every `ρ_u < 1` and is the unique bounded
  equilibrium.
-/

namespace Gali.BasicNewKeynesianModel.TaylorRuleSystem

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (22), p. 63: the New Keynesian Phillips curve
`π_t = β E_t π_{t+1} + κ ỹ_t`. -/
def NKPC (β κ : ℝ) (ygap infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t

/-- Galí (2015), eq. (26), p. 64: the interest-rate rule
`i_t = ρ + φ_π π_t + φ_y ŷ_t + v_t`, with `ŷ_t` the deviation of output from
its steady-state value. -/
def TaylorRule (ρ φπ φy : ℝ) (i infl yhat v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = (fun _ => ρ) + φπ • infl t + φy • yhat t + v t

/-- Galí (2015), p. 65: the rule (26) in terms of the output gap,
`i_t = ρ + φ_π π_t + φ_y ỹ_t + φ_y ŷ^n_t + v_t`. -/
def TaylorRuleGap (ρ φπ φy : ℝ) (i infl ygap yhatn v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = (fun _ => ρ) + φπ • infl t + φy • ygap t + φy • yhatn t + v t

/-- Galí (2015), p. 65: since `ŷ_t = ỹ_t + ŷ^n_t`, rule (26) is the same as
its output-gap form. -/
theorem taylorRule_iff_gap {ρ φπ φy : ℝ} {i infl yhat ygap yhatn v : ℕ → Ω → ℝ}
    (hyhat : ∀ t, yhat t = ygap t + yhatn t) :
    TaylorRule ρ φπ φy i infl yhat v ↔ TaylorRuleGap ρ φπ φy i infl ygap yhatn v := by
  simp only [TaylorRule, TaylorRuleGap, hyhat, smul_add, add_assoc]

/-- Galí (2015), p. 65: the composite shock of system (27),
`u_t = r̂^n_t − φ_y ŷ^n_t − v_t` with `r̂^n_t = r^n_t − ρ`. -/
def shockU (ρ φy : ℝ) (rn yhatn v : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => rn t - (fun _ => ρ) - φy • yhatn t - v t

/-- Galí (2015), §3.4.1, pp. 63–65: an equilibrium under the interest-rate rule:
the NKPC (22), the DIS (23) and the rule (26) in gap form. -/
def Equilibrium (β σ κ ρ φπ φy : ℝ) (rn yhatn v ygap infl i : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β κ ygap infl ∧ DIS.DISGap 𝔼 σ ygap i infl rn ∧
    TaylorRuleGap ρ φπ φy i infl ygap yhatn v

/-- Galí (2015), §3.4.1, p. 65: the equilibrium conditions with the interest
rate substituted out, `(σ + φ_y) ỹ_t + φ_π π_t = σ E_t ỹ_{t+1} + E_t π_{t+1} + u_t`
together with the NKPC. -/
def Structural (β σ κ φπ φy : ℝ) (u ygap infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (σ + φy) • ygap t + φπ • infl t
      = σ • 𝔼.E t (ygap (t + 1)) + 𝔼.E t (infl (t + 1)) + u t ∧
    infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t

/-- Galí (2015), p. 65: `Ω = 1/(σ + φ_y + κ φ_π)`. -/
noncomputable def omega (σ κ φπ φy : ℝ) : ℝ := 1 / (σ + φy + κ * φπ)

/-- Galí (2015), eq. (27), p. 65: the matrix
`A_T = Ω [[σ, 1 − βφ_π], [σκ, κ + β(σ + φ_y)]]`. -/
noncomputable def AT (β σ κ φπ φy : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![omega σ κ φπ φy * σ, omega σ κ φπ φy * (1 - β * φπ);
    omega σ κ φπ φy * (σ * κ), omega σ κ φπ φy * (κ + β * (σ + φy))]

/-- Galí (2015), eq. (27), p. 65: the vector `B_T = Ω (1, κ)`. -/
noncomputable def BT (σ κ φπ φy : ℝ) : Fin 2 → ℝ := ![omega σ κ φπ φy, omega σ κ φπ φy * κ]

/-- Galí (2015), eq. (27): the stacked vector `x_t = (ỹ_t, π_t)`. -/
def stack (ygap infl : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![ygap t, infl t]

/-- Galí (2015), eq. (27): the forcing term `B u_t` of the system. -/
def forcing (b : Fin 2 → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t j => b j • u t

/-- Galí (2015), §3.4.1, p. 65: with the rule in gap form, the NKPC and the
DIS hold if and only if the structural equations hold with the composite shock
`u_t = r̂^n_t − φ_y ŷ^n_t − v_t`. -/
theorem nk_iff_structural {β σ κ ρ φπ φy : ℝ} (hσ : σ ≠ 0)
    {rn yhatn v ygap infl i : ℕ → Ω → ℝ} (hrule : TaylorRuleGap ρ φπ φy i infl ygap yhatn v) :
    (NKPC 𝔼 β κ ygap infl ∧ DIS.DISGap 𝔼 σ ygap i infl rn) ↔
      Structural 𝔼 β σ κ φπ φy (shockU ρ φy rn yhatn v) ygap infl := by
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  constructor
  · rintro ⟨hp, hd⟩ t
    refine ⟨?_, hp t⟩
    funext ω
    have e := congrFun (hd t) ω
    have r := congrFun (hrule t) ω
    simp only [shockU, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e r ⊢
    linear_combination σ * e - r - (i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) * hinv
  · intro h
    refine ⟨fun t => (h t).2, fun t => ?_⟩
    funext ω
    have e := congrFun (h t).1 ω
    have r := congrFun (hrule t) ω
    simp only [shockU, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e r ⊢
    linear_combination σ⁻¹ * e + σ⁻¹ * r
      - (ygap t ω - 𝔼.E t (ygap (t + 1)) ω) * hinv

/-- Galí (2015), eq. (27), p. 65: the structural equations are equivalent to
`x_t = A_T E_t x_{t+1} + B_T u_t` for `x_t = (ỹ_t, π_t)`, provided
`σ + φ_y + κ φ_π ≠ 0`. -/
theorem structural_iff_solves {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0)
    (u ygap infl : ℕ → Ω → ℝ) :
    Structural 𝔼 β σ κ φπ φy u ygap infl ↔
      𝔼.Solves (AT β σ κ φπ φy) (forcing (BT σ κ φπ φy) u) (stack ygap infl) := by
  constructor
  · intro h t j
    obtain ⟨h1, h2⟩ := h t
    funext ω
    have e1 := congrFun h1 ω
    have e2 := congrFun h2 ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    fin_cases j
    · simp [stack, forcing, AT, BT, omega]
      field_simp
      linear_combination e1 - φπ * e2
    · simp [stack, forcing, AT, BT, omega]
      field_simp
      linear_combination κ * e1 + (σ + φy) * e2
  · intro h t
    have h0 := h t 0
    have h1 := h t 1
    simp only [stack, Fin.isValue, Matrix.cons_val_zero, AT, omega, one_div, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one, forcing, BT] at h0 h1
    refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
    · have e0 := congrFun h0 ω
      have e1 := congrFun h1 ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1 ⊢
      field_simp at e0 e1
      apply mul_left_cancel₀ hS
      linear_combination (σ + φy) * e0 + φπ * e1
    · have e0 := congrFun h0 ω
      have e1 := congrFun h1 ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1 ⊢
      field_simp at e0 e1
      apply mul_left_cancel₀ hS
      linear_combination e1 - κ * e0
/-- Galí (2015), eq. (27), p. 65: with the rule (26) in gap form, `(ỹ, π)`
satisfies the NKPC and the DIS if and only if it solves
`x_t = A_T E_t x_{t+1} + B_T u_t`. -/
theorem equilibrium_iff_solves {β σ κ ρ φπ φy : ℝ} (hσ : σ ≠ 0)
    (hS : σ + φy + κ * φπ ≠ 0) {rn yhatn v ygap infl i : ℕ → Ω → ℝ}
    (hrule : TaylorRuleGap ρ φπ φy i infl ygap yhatn v) :
    Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap infl i ↔
      𝔼.Solves (AT β σ κ φπ φy) (forcing (BT σ κ φπ φy) (shockU ρ φy rn yhatn v))
        (stack ygap infl) := by
  rw [← structural_iff_solves 𝔼 hS, ← nk_iff_structural 𝔼 hσ hrule]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hrule⟩⟩

/-- The trace of `A_T`: `tr A_T = (σ (1 + β) + κ + β φ_y)/(σ + φ_y + κ φ_π)`
(Galí 2015, p. 65). -/
theorem tr2_AT {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0) :
    tr2 (AT β σ κ φπ φy) = (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) := by
  simp only [tr2, AT, omega, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- The determinant of `A_T`: `det A_T = σ β/(σ + φ_y + κ φ_π)`
(Galí 2015, p. 65). -/
theorem det2_AT {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0) :
    det2 (AT β σ κ φπ φy) = σ * β / (σ + φy + κ * φπ) := by
  simp only [det2, AT, omega, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- **Bullard–Mitra** (Galí 2015, eq. (28), p. 65): for `σ, κ > 0`,
`0 < β < 1` and `φ_π, φ_y ≥ 0`, both eigenvalues of `A_T` lie inside the unit
circle (the Schur–Cohn condition) if and only if
`κ (φ_π − 1) + (1 − β) φ_y > 0`. -/
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

/-- Galí (2015), p. 65 (Blanchard–Kahn and Bullard–Mitra): the system (27) is
determinate, i.e. has at most one bounded adapted solution for every forcing
process, if and only if condition (28) holds. -/
theorem determinate_iff_BM [Nonempty Ω] {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    𝔼.Determinate (AT β σ κ φπ φy) ↔ 0 < κ * (φπ - 1) + (1 - β) * φy :=
  (𝔼.determinate_iff _).trans (schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy)

/-- Two bounded processes stack to a bounded vector process. -/
theorem boundedVec_stack {a b : ℕ → Ω → ℝ} (ha : BoundedProc a) (hb : BoundedProc b) :
    BoundedVec (stack a b) := by
  obtain ⟨M₁, h₁⟩ := ha
  obtain ⟨M₂, h₂⟩ := hb
  refine ⟨max M₁ M₂, fun t j ω => ?_⟩
  fin_cases j
  · exact (h₁ t ω).trans (le_max_left _ _)
  · exact (h₂ t ω).trans (le_max_right _ _)

/-- Two adapted processes stack to an adapted vector process. -/
theorem adaptedVec_stack {a b : ℕ → Ω → ℝ} (ha : 𝔼.Adapted a) (hb : 𝔼.Adapted b) :
    𝔼.AdaptedVec (stack a b) := by
  intro t j
  fin_cases j
  · exact ha t
  · exact hb t

/-- **Uniqueness under (28)** (Galí 2015, p. 65): if
`κ (φ_π − 1) + (1 − β) φ_y > 0`, two equilibria with bounded adapted output
gap and inflation, driven by the same exogenous processes, coincide (output
gap, inflation and the nominal rate). -/
theorem equilibrium_unique {β σ κ ρ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy)
    {rn yhatn v ygap infl i ygap' infl' i' : ℕ → Ω → ℝ}
    (he : Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap infl i)
    (he' : Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap' infl' i')
    (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl) (ha' : 𝔼.Adapted ygap')
    (hb' : 𝔼.Adapted infl') (hba : BoundedProc ygap) (hbb : BoundedProc infl)
    (hba' : BoundedProc ygap') (hbb' : BoundedProc infl') :
    ygap = ygap' ∧ infl = infl' ∧ i = i' := by
  have hS : σ + φy + κ * φπ ≠ 0 := by positivity
  have hx := (equilibrium_iff_solves 𝔼 hσ.ne' hS he.2.2).mp he
  have hy := (equilibrium_iff_solves 𝔼 hσ.ne' hS he'.2.2).mp he'
  have heq := 𝔼.system_unique ((schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy).mpr h28) hx hy
    (adaptedVec_stack 𝔼 ha hb) (adaptedVec_stack 𝔼 ha' hb')
    (boundedVec_stack hba hbb) (boundedVec_stack hba' hbb')
  have h1 : ygap = ygap' := funext fun t => by
    simpa [stack] using congrFun (congrFun heq t) 0
  have h2 : infl = infl' := funext fun t => by
    simpa [stack] using congrFun (congrFun heq t) 1
  refine ⟨h1, h2, funext fun t => ?_⟩
  rw [he.2.2 t, he'.2.2 t, h1, h2]

/-- **Indeterminacy without (28)** (Galí 2015, p. 65): if
`κ (φ_π − 1) + (1 − β) φ_y ≤ 0`, then next to any equilibrium with bounded
adapted output gap and inflation there is a second one, with a different
output gap or inflation path. -/
theorem equilibrium_not_unique [Nonempty Ω] {β σ κ ρ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy)
    (h28 : κ * (φπ - 1) + (1 - β) * φy ≤ 0) {rn yhatn v ygap infl i : ℕ → Ω → ℝ}
    (he : Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap infl i)
    (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap)
    (hbb : BoundedProc infl) :
    ∃ ygap' infl' i', Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap' infl' i' ∧
      𝔼.Adapted ygap' ∧ 𝔼.Adapted infl' ∧ BoundedProc ygap' ∧ BoundedProc infl' ∧
      (ygap' ≠ ygap ∨ infl' ≠ infl) := by
  have hS : σ + φy + κ * φπ ≠ 0 := by positivity
  have hns : ¬ SchurStable (tr2 (AT β σ κ φπ φy)) (det2 (AT β σ κ φπ φy)) := by
    rw [schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy]; linarith
  have hx := (equilibrium_iff_solves 𝔼 hσ.ne' hS he.2.2).mp he
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ := 𝔼.system_not_unique hns hx
    (adaptedVec_stack 𝔼 ha hb) (boundedVec_stack hba hbb)
  set ygap' : ℕ → Ω → ℝ := fun t => y t 0
  set infl' : ℕ → Ω → ℝ := fun t => y t 1
  have hst : stack ygap' infl' = y := by
    funext t j
    fin_cases j <;> rfl
  have hrule' : TaylorRuleGap ρ φπ φy
      (fun t => (fun _ => ρ) + φπ • infl' t + φy • ygap' t + φy • yhatn t + v t)
      infl' ygap' yhatn v := fun t => rfl
  refine ⟨ygap', infl', _, (equilibrium_iff_solves 𝔼 hσ.ne' hS hrule').mpr (hst ▸ hy),
    fun t => hay t 0, fun t => hay t 1, ⟨M, fun t ω => hM t 0 ω⟩, ⟨M, fun t ω => hM t 1 ω⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hst, hcon.1, hcon.2]

/-! ### The minimum-state-variable solution -/

/-- Galí (2015), p. 66: the denominator
`(1 − βρ_u)(σ (1 − ρ_u) + φ_y) + κ (φ_π − ρ_u)` of `Λ_u`. -/
def msvDen (β σ κ φπ φy ρu : ℝ) : ℝ := (1 - β * ρu) * (σ * (1 - ρu) + φy) + κ * (φπ - ρu)

/-- Galí (2015), p. 66: `Λ_u = 1/((1 − βρ_u)(σ (1 − ρ_u) + φ_y) + κ (φ_π − ρ_u))`. -/
noncomputable def msvLambda (β σ κ φπ φy ρu : ℝ) : ℝ := 1 / msvDen β σ κ φπ φy ρu

/-- Galí (2015), eq. (29), p. 66: `ψ_y = (1 − βρ_u) Λ_u`. -/
noncomputable def msvPsiY (β σ κ φπ φy ρu : ℝ) : ℝ := (1 - β * ρu) * msvLambda β σ κ φπ φy ρu

/-- Galí (2015), eq. (30), p. 66: `ψ_π = κ Λ_u`. -/
noncomputable def msvPsiPi (β σ κ φπ φy ρu : ℝ) : ℝ := κ * msvLambda β σ κ φπ φy ρu

/-- The denominator of `Λ_u` decomposes as
`(1 − ρ_u)((1 − βρ_u) σ + κ + β φ_y) + [κ (φ_π − 1) + (1 − β) φ_y]`
(Galí 2015, p. 66). -/
theorem msvDen_eq (β σ κ φπ φy ρu : ℝ) :
    msvDen β σ κ φπ φy ρu
      = (1 - ρu) * ((1 - β * ρu) * σ + κ + β * φy) + (κ * (φπ - 1) + (1 - β) * φy) := by
  unfold msvDen; ring

/-- Galí (2015), p. 66: under (28) and for `ρ_u < 1` (in particular
`ρ_u ∈ [0, 1)`) the denominator of `Λ_u` is positive. -/
theorem msvDen_pos {β σ κ φπ φy ρu : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρu < 1)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) : 0 < msvDen β σ κ φπ φy ρu := by
  rw [msvDen_eq]
  have hbr : β * ρu < 1 := by nlinarith
  have h1 : 0 ≤ (1 - β * ρu) * σ := by nlinarith
  have h2 : 0 ≤ (1 - ρu) * ((1 - β * ρu) * σ + κ + β * φy) := by
    apply mul_nonneg <;> nlinarith
  linarith

/-- Galí (2015), p. 66: `Λ_u > 0` under (28), for every `ρ_u < 1`. -/
theorem msvLambda_pos {β σ κ φπ φy ρu : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρu < 1)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) : 0 < msvLambda β σ κ φπ φy ρu :=
  one_div_pos.mpr (msvDen_pos hσ hκ hβ0 hβ1 hφy hρ1 h28)

/-- A scalar multiple of an AR(1) process is AR(1) with the same persistence. -/
theorem isAR1_smul {ρu : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρu u) (c : ℝ) :
    𝔼.IsAR1 ρu (fun t => c • u t) :=
  ⟨fun t => by simp only [map_smul, hu.1 t], fun t => by
    simp only [map_smul, hu.2 t, smul_comm c ρu]⟩

/-- Galí (2015), eqs. (29)–(30), p. 66: for an AR(1) composite shock with
persistence `ρ_u` (and a nonzero denominator), the MSV processes
`ỹ_t = ψ_y u_t`, `π_t = ψ_π u_t` satisfy the structural equations. -/
theorem msv_structural {β σ κ φπ φy ρu : ℝ} (hD : msvDen β σ κ φπ φy ρu ≠ 0)
    {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρu u) :
    Structural 𝔼 β σ κ φπ φy u (fun t => msvPsiY β σ κ φπ φy ρu • u t)
      (fun t => msvPsiPi β σ κ φπ φy ρu • u t) := by
  have c1 : (σ + φy) * msvPsiY β σ κ φπ φy ρu + φπ * msvPsiPi β σ κ φπ φy ρu
      = σ * (msvPsiY β σ κ φπ φy ρu * ρu) + msvPsiPi β σ κ φπ φy ρu * ρu + 1 := by
    unfold msvPsiY msvPsiPi msvLambda
    field_simp
    unfold msvDen
    ring
  have c2 : msvPsiPi β σ κ φπ φy ρu
      = β * (msvPsiPi β σ κ φπ φy ρu * ρu) + κ * msvPsiY β σ κ φπ φy ρu := by
    unfold msvPsiY msvPsiPi
    ring
  intro t
  simp only [map_smul, hu.2 t, smul_smul]
  refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination u t ω * c1
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination u t ω * c2

/-- Galí (2015), p. 66: under (28), for a bounded AR(1) composite shock with
`ρ_u < 1`, every bounded adapted solution of the structural equations is
the MSV solution (29)–(30). -/
theorem msv_unique {β σ κ φπ φy ρu : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρu < 1)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) {u ygap infl : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρu u) (hub : BoundedProc u)
    (hs : Structural 𝔼 β σ κ φπ φy u ygap infl) (ha : 𝔼.Adapted ygap)
    (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    ygap = (fun t => msvPsiY β σ κ φπ φy ρu • u t) ∧
      infl = (fun t => msvPsiPi β σ κ φπ φy ρu • u t) := by
  have hS : σ + φy + κ * φπ ≠ 0 := by positivity
  have hD := (msvDen_pos hσ hκ hβ0 hβ1 hφy hρ1 h28).ne'
  have hbs : ∀ c : ℝ, BoundedProc (fun t => c • u t) := by
    intro c
    obtain ⟨M, hM⟩ := hub
    exact ⟨|c| * M, fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg c)⟩
  have heq := 𝔼.system_unique ((schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy).mpr h28)
    ((structural_iff_solves 𝔼 hS _ _ _).mp hs)
    ((structural_iff_solves 𝔼 hS _ _ _).mp (msv_structural 𝔼 hD hu))
    (adaptedVec_stack 𝔼 ha hb)
    (adaptedVec_stack 𝔼 (isAR1_smul 𝔼 hu _).1 (isAR1_smul 𝔼 hu _).1)
    (boundedVec_stack hba hbb) (boundedVec_stack (hbs _) (hbs _))
  exact ⟨funext fun t => by simpa [stack] using congrFun (congrFun heq t) 0,
    funext fun t => by simpa [stack] using congrFun (congrFun heq t) 1⟩

/-- **The unique bounded equilibrium** (Galí 2015, eqs. (29)–(30), p. 66): under
(28), with a bounded AR(1) composite shock `u = r̂^n − φ_y ŷ^n − v` of
persistence `ρ_u < 1`, a triple `(ỹ, π, i)` with bounded adapted `ỹ`, `π`
is an equilibrium if and only if `ỹ_t = (1 − βρ_u) Λ_u u_t`,
`π_t = κ Λ_u u_t` and `i_t` is given by the rule. The MSV triple is itself
bounded and adapted, so it is the unique bounded equilibrium. -/
theorem equilibrium_iff_msv {β σ κ ρ φπ φy ρu : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρ1 : ρu < 1)
    (h28 : 0 < κ * (φπ - 1) + (1 - β) * φy) {rn yhatn v : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρu (shockU ρ φy rn yhatn v)) (hub : BoundedProc (shockU ρ φy rn yhatn v))
    {ygap infl i : ℕ → Ω → ℝ} (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl)
    (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn v ygap infl i ↔
      ygap = (fun t => msvPsiY β σ κ φπ φy ρu • shockU ρ φy rn yhatn v t) ∧
      infl = (fun t => msvPsiPi β σ κ φπ φy ρu • shockU ρ φy rn yhatn v t) ∧
      i = fun t => (fun _ => ρ) + φπ • infl t + φy • ygap t + φy • yhatn t + v t := by
  have hD := (msvDen_pos hσ hκ hβ0 hβ1 hφy hρ1 h28).ne'
  constructor
  · intro he
    obtain ⟨h1, h2⟩ := msv_unique 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρ1 h28 hu hub
      ((nk_iff_structural 𝔼 hσ.ne' he.2.2).mp ⟨he.1, he.2.1⟩) ha hb hba hbb
    exact ⟨h1, h2, funext he.2.2⟩
  · rintro ⟨h1, h2, h3⟩
    have hrule : TaylorRuleGap ρ φπ φy i infl ygap yhatn v := fun t => by rw [h3]
    have hs := (nk_iff_structural 𝔼 (β := β) (κ := κ) (rn := rn) hσ.ne' hrule).mpr
      (h1 ▸ h2 ▸ msv_structural 𝔼 hD hu)
    exact ⟨hs.1, hs.2, hrule⟩

end Gali.BasicNewKeynesianModel.TaylorRuleSystem
