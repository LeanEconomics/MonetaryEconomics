/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DiscretionCommitment.Expectations
import DiscretionCommitment.Ex5_3

/-!
# Exercise 5.4: inflation persistence and monetary policy

Galí (2015), Chapter 5, Exercise 5.4, p. 161 (based on Steinsson 2003). With partial
indexation `γ`, the loss is `½ E_0 ∑ βᵗ [ϑ x_t² + (π_t − γπ_{t−1})²]` and inflation follows
`π_t − γπ_{t−1} = κ x_t + β E_t (π_{t+1} − γπ_t) + u_t`. Write `π̃_t = π_t − γπ_{t−1}` (`tilde`,
with a given initial `π_{−1}`): the problem is the chapter's problem with `π̃` in place of `π`.

## (a) Discretion
* `period_loss_eq`, `period_opt_iff`, `period_targeting_iff`: given `v = β E_t π̃_{t+1} + u_t`
  (which, in an equilibrium where `π̃` depends only on current shocks, the current choice does
  not affect), `ϑ x² + (κ x + v)²` has the unique minimiser `x* = −κ v/(ϑ + κ²)`, which is
  characterised by the targeting rule `x = −(κ/ϑ) π̃`.
* `ex5_4a_period_optimal`: in the discretionary equilibrium each period's choice minimises the
  short-term loss.
* `ex5_4a_unique`: the unique equilibrium with bounded `π̃` and `x` is
  `π̃_t = ϑ u_t/(κ² + ϑ(1 − βρ_u))`, `x_t = −κ u_t/(κ² + ϑ(1 − βρ_u))` (`ρ_u = 0` in the book:
  `π̃_t = ϑ u_t/(ϑ + κ²)`); `ex5_4a_exists` (constructed by `π_t = γπ_{t−1} + ψ u_t`,
  `discInfl`), `ex5_4a_inflation`: `π_t = γ π_{t−1} + ϑ u_t/(κ² + ϑ(1 − βρ_u))`.
* `period_foc_alt`: if instead `E_t π_{t+1}` were taken as given, the period FOC would be
  `ϑ (1 + βγ) x = −κ π̃` — a different, not Markov-perfect, condition (remark).

## (b) Commitment
Deterministic (perfect-foresight) problem over bounded `(x, π̃)`, as in §5.2.2:
minimise `∑ βᵗ (ϑ x_t² + π̃_t²)` subject to `π̃_t = κ x_t + β π̃_{t+1} + u_t`.
* `partial_sum_identity`, `ex5_4b_sufficient`, `ex5_4b_necessary`, `ex5_4b_optimal_iff`:
  optimal ⟺ the FOCs `ϑ x_t − κ ξ_t = 0`, `π̃_t + ξ_t − ξ_{t−1} = 0`, `ξ_{−1} = 0`.
* `foc_iff_level_rule`: ⟺ `x_t = −(κ/ϑ) p̃_t` with `p̃_t = ∑_{s ≤ t} π̃_s` (the `p̃`-level
  rule), ⟺ `x_t − x_{t−1} = −(κ/ϑ) π̃_t`, `x_{−1} = 0` (`level_rule_iff_diff`).
* `cumsum_tilde_eq`: in terms of the log price level,
  `p̃_t = (p_t − p_{−1}) − γ (p_{t−1} − p_{−2})`; `ex5_4b`: the optimal plan is characterised by
  `x_t = −(κ/ϑ)[(p_t − p_{−1}) − γ(p_{t−1} − p_{−2})]`.

## (c) Discussion
Part (c) asks for a verbal discussion of how `γ` affects the responses; it is not formalised.
-/

namespace Gali.DiscretionCommitment.Ex5_4

open Filter Topology
open Gali.DiscretionCommitment.Ex5_3 (lag Bdd bdd_lin bdd_shift bdd_lag eq_zero_of_quadratic)

/-! ### (a) Discretion: the period problem -/

/-- Galí (2015), Exercise 5.4(a): the minimiser `x* = −κ v/(ϑ + κ²)` of the period loss
`ϑ x² + (κ x + v)²`. -/
noncomputable def periodOpt (ϑ κ v : ℝ) : ℝ := -κ * v / (ϑ + κ ^ 2)

/-- Galí (2015), Exercise 5.4(a): `ϑ x² + (κx + v)² = ϑ x*² + (κx* + v)² + (ϑ + κ²)(x − x*)²`. -/
theorem period_loss_eq {ϑ κ v : ℝ} (hK : ϑ + κ ^ 2 ≠ 0) (x : ℝ) :
    ϑ * x ^ 2 + (κ * x + v) ^ 2 = ϑ * periodOpt ϑ κ v ^ 2 + (κ * periodOpt ϑ κ v + v) ^ 2 +
      (ϑ + κ ^ 2) * (x - periodOpt ϑ κ v) ^ 2 := by
  unfold periodOpt
  field_simp
  ring

/-- **Exercise 5.4(a), the period problem** (Galí 2015, p. 161): `x` minimises
`ϑ x² + (κ x + v)²` iff `x = x*`. -/
theorem period_opt_iff {ϑ κ v x : ℝ} (hϑ : 0 < ϑ) :
    (∀ x', ϑ * x ^ 2 + (κ * x + v) ^ 2 ≤ ϑ * x' ^ 2 + (κ * x' + v) ^ 2) ↔
      x = periodOpt ϑ κ v := by
  have hK : 0 < ϑ + κ ^ 2 := by positivity
  constructor
  · intro h
    have h1 := h (periodOpt ϑ κ v)
    rw [period_loss_eq hK.ne' x] at h1
    have h2 : (ϑ + κ ^ 2) * (x - periodOpt ϑ κ v) ^ 2 ≤ 0 := by linarith
    have h3 : (x - periodOpt ϑ κ v) ^ 2 = 0 :=
      le_antisymm (by nlinarith [sq_nonneg (x - periodOpt ϑ κ v)]) (sq_nonneg _)
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)
  · rintro rfl x'
    rw [period_loss_eq hK.ne' x']
    nlinarith [sq_nonneg (x' - periodOpt ϑ κ v)]

/-- **Exercise 5.4(a), the targeting rule** (Galí 2015, p. 161): `x = x*` iff
`x = −(κ/ϑ) π̃` with `π̃ = κ x + v`. -/
theorem period_targeting_iff {ϑ κ v x : ℝ} (hϑ : 0 < ϑ) :
    x = periodOpt ϑ κ v ↔ x = -(κ / ϑ) * (κ * x + v) := by
  have hK : 0 < ϑ + κ ^ 2 := by positivity
  unfold periodOpt
  constructor
  · intro h
    rw [h]
    field_simp
    ring
  · intro h
    rw [eq_div_iff hK.ne']
    field_simp at h
    linear_combination h

/-- Galí (2015), Exercise 5.4(a) (**remark on timing**): if the central bank took `E_t π_{t+1}`
(rather than `E_t π̃_{t+1}`) as given, then `π_t = (κ x + w)/(1 + βγ)` and the period loss
`ϑ x² + (π_t − γπ_{t−1})²` would be minimised iff `ϑ (1 + βγ) x = −κ π̃`. -/
theorem period_foc_alt {ϑ κ β γ w pm x : ℝ} (hϑ : 0 < ϑ) (hb : 0 < 1 + β * γ) :
    (∀ x', ϑ * x ^ 2 + ((κ * x + w) / (1 + β * γ) - γ * pm) ^ 2 ≤
        ϑ * x' ^ 2 + ((κ * x' + w) / (1 + β * γ) - γ * pm) ^ 2) ↔
      ϑ * (1 + β * γ) * x = -κ * ((κ * x + w) / (1 + β * γ) - γ * pm) := by
  set k := κ / (1 + β * γ)
  set v := w / (1 + β * γ) - γ * pm
  have e : ∀ x', (κ * x' + w) / (1 + β * γ) - γ * pm = k * x' + v := fun x' => by
    simp only [k, v]; field_simp; ring
  simp only [e]
  rw [period_opt_iff hϑ, period_targeting_iff hϑ]
  have hk : κ = k * (1 + β * γ) := by simp only [k]; field_simp
  have key : x = -(k / ϑ) * (k * x + v) ↔ ϑ * x = -k * (k * x + v) := by
    constructor
    · intro h
      nth_rewrite 1 [h]
      field_simp
    · intro h
      field_simp
      linear_combination h
  rw [key, hk]
  constructor
  · intro h
    linear_combination (1 + β * γ) * h
  · intro h
    apply mul_left_cancel₀ hb.ne'
    linear_combination h

/-! ### (a) Discretion: the equilibrium -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Exercise 5.4: lagged inflation `π_{t−1}`, with the given initial `π_{−1}`. -/
def prev (p0 : Ω → ℝ) (p : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => p0
  | t + 1 => p t

/-- Galí (2015), Exercise 5.4, p. 161: quasi-differenced inflation `π̃_t = π_t − γ π_{t−1}`. -/
def tilde (γ : ℝ) (p0 : Ω → ℝ) (p : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => p t - γ • prev p0 p t

/-- Galí (2015), Exercise 5.4, p. 161: the Phillips curve with indexation,
`π_t − γπ_{t−1} = κ x_t + β E_t(π_{t+1} − γπ_t) + u_t`. -/
def NKPCInd (β κ γ : ℝ) (p0 : Ω → ℝ) (x p u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, tilde γ p0 p t = κ • x t + β • 𝔼.E t (tilde γ p0 p (t + 1)) + u t

/-- Galí (2015), Exercise 5.4(a): the discretionary equilibrium, the Phillips curve together
with the targeting rule `x_t = −(κ/ϑ) π̃_t`. -/
def DiscretionEq (β κ γ ϑ : ℝ) (p0 : Ω → ℝ) (x p u : ℕ → Ω → ℝ) : Prop :=
  NKPCInd 𝔼 β κ γ p0 x p u ∧ ∀ t, x t = -(κ / ϑ) • tilde γ p0 p t

omit 𝔼 in
/-- Galí (2015), Exercise 5.4: `π̃_{t+1} = π_{t+1} − γ π_t`. -/
theorem tilde_succ (γ : ℝ) (p0 : Ω → ℝ) (p : ℕ → Ω → ℝ) (t : ℕ) :
    tilde γ p0 p (t + 1) = p (t + 1) - γ • p t := rfl

/-- **Exercise 5.4(a), period optimality** (Galí 2015, p. 161): in the discretionary
equilibrium, at every date and state, `(x_t, π̃_t)` minimises `ϑ x² + π̃²` over the choices
`π̃ = κ x + v_t` with `v_t = β E_t π̃_{t+1} + u_t` given. -/
theorem ex5_4a_period_optimal {β κ γ ϑ : ℝ} (hϑ : 0 < ϑ) {p0 : Ω → ℝ} {x p u : ℕ → Ω → ℝ}
    (he : DiscretionEq 𝔼 β κ γ ϑ p0 x p u) (t : ℕ) (ω : Ω) (x' : ℝ) :
    ϑ * x t ω ^ 2 + tilde γ p0 p t ω ^ 2 ≤
      ϑ * x' ^ 2 + (κ * x' + (β * 𝔼.E t (tilde γ p0 p (t + 1)) ω + u t ω)) ^ 2 := by
  have h1 := congrFun (he.1 t) ω
  have h2 := congrFun (he.2 t) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  set v := β * 𝔼.E t (tilde γ p0 p (t + 1)) ω + u t ω
  have hp : tilde γ p0 p t ω = κ * x t ω + v := by rw [h1]; ring
  have hx : x t ω = periodOpt ϑ κ v :=
    (period_targeting_iff hϑ).mpr (by rw [← hp]; exact h2)
  rw [hp]
  exact (period_opt_iff hϑ).mpr hx x'

/-- Galí (2015), Exercise 5.4(a): `βρ_u < 1`. -/
theorem beta_rho_lt_one {β ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : |ρ| < 1) : β * ρ < 1 := by
  have h1 : β * ρ ≤ β * |ρ| := mul_le_mul_of_nonneg_left (le_abs_self ρ) hβ0.le
  have h2 : β * |ρ| < β * 1 := mul_lt_mul_of_pos_left hρ hβ0
  linarith

/-- Galí (2015), Exercise 5.4(a): the discretionary coefficient `ψ = ϑ/(κ² + ϑ(1 − βρ_u))`. -/
noncomputable def psiD (β κ ϑ ρ : ℝ) : ℝ := ϑ / (κ ^ 2 + ϑ * (1 - β * ρ))

/-- **Exercise 5.4(a), uniqueness** (Galí 2015, p. 161): in every discretionary equilibrium with
bounded `π̃`, `π̃_t = ϑ u_t/(κ² + ϑ(1 − βρ_u))` and `x_t = −κ u_t/(κ² + ϑ(1 − βρ_u))`. -/
theorem ex5_4a_unique {β κ γ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hϑ : 0 < ϑ)
    (hρ : |ρ| < 1) {p0 : Ω → ℝ} {u x p : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u)
    (hub : BoundedProc u) (he : DiscretionEq 𝔼 β κ γ ϑ p0 x p u)
    (hb : BoundedProc (tilde γ p0 p)) :
    tilde γ p0 p = (fun t => psiD β κ ϑ ρ • u t) ∧
      x = fun t => (-(κ / ϑ) * psiD β κ ϑ ρ) • u t := by
  have hβρ := beta_rho_lt_one hβ0 hβ1 hρ
  have hD : 0 < κ ^ 2 + ϑ * (1 - β * ρ) := by
    have : 0 < 1 - β * ρ := by linarith
    positivity
  have hK : 0 < ϑ + κ ^ 2 := by positivity
  set a := ϑ * β / (ϑ + κ ^ 2)
  set b := ϑ / (ϑ + κ ^ 2)
  have ha : |a| < 1 := by
    rw [abs_of_nonneg (by positivity), div_lt_one hK]
    nlinarith [pow_pos (abs_pos.mpr hκ) 2, sq_abs κ]
  set q := tilde γ p0 p
  have h1 : ∀ t, q t = a • 𝔼.E t (q (t + 1)) + b • u t := by
    intro t
    funext ω
    have e1 := congrFun (he.1 t) ω
    have e2 := congrFun (he.2 t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
    rw [e2] at e1
    simp only [a, b]
    field_simp
    have hinv : ϑ * ϑ⁻¹ = 1 := mul_inv_cancel₀ hϑ.ne'
    linear_combination ϑ * e1 - q t ω * κ ^ 2 * hinv
  have h2 : ∀ t, (fun t => psiD β κ ϑ ρ • u t) t =
      a • 𝔼.E t ((fun t => psiD β κ ϑ ρ • u t) (t + 1)) + b • u t := by
    intro t
    funext ω
    simp only [map_smul, hu.2 t, Pi.add_apply, Pi.smul_apply, smul_eq_mul, a, b, psiD]
    field_simp
    ring
  obtain ⟨M, hM⟩ := hub
  have hcb : BoundedProc fun t => psiD β κ ϑ ρ • u t :=
    ⟨|psiD β κ ϑ ρ| * M, fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)⟩
  have hq := 𝔼.forward_unique ha h1 h2 hb hcb
  refine ⟨hq, ?_⟩
  funext t
  have hqt := congrFun hq t
  simp only [q] at hqt
  rw [he.2 t, hqt, smul_smul]

/-- Galí (2015), Exercise 5.4(a): inflation under discretion, constructed recursively by
`π_t = γ π_{t−1} + ψ u_t` from `π_{−1}`. -/
noncomputable def discInfl (γ ψ : ℝ) (p0 : Ω → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => γ • p0 + ψ • u 0
  | t + 1 => γ • discInfl γ ψ p0 u t + ψ • u (t + 1)

omit 𝔼 in
/-- Galí (2015), Exercise 5.4(a): `π̃ = ψ u` along the constructed path. -/
theorem tilde_discInfl (γ ψ : ℝ) (p0 : Ω → ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) :
    tilde γ p0 (discInfl γ ψ p0 u) t = ψ • u t := by
  rcases t with _ | t
  · simp [tilde, prev, discInfl]
  · simp [tilde, prev, discInfl]

/-- **Exercise 5.4(a), existence** (Galí 2015, p. 161): `π_t = γπ_{t−1} + ψ u_t`,
`x_t = −(κ/ϑ) ψ u_t` (`ψ = ϑ/(κ² + ϑ(1 − βρ_u))`) is a discretionary equilibrium. -/
theorem ex5_4a_exists {β κ γ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hρ : |ρ| < 1)
    (p0 : Ω → ℝ) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) :
    DiscretionEq 𝔼 β κ γ ϑ p0 (fun t => (-(κ / ϑ) * psiD β κ ϑ ρ) • u t)
      (discInfl γ (psiD β κ ϑ ρ) p0 u) u := by
  have hβρ := beta_rho_lt_one hβ0 hβ1 hρ
  have hD : 0 < κ ^ 2 + ϑ * (1 - β * ρ) := by
    have : 0 < 1 - β * ρ := by linarith
    positivity
  refine ⟨fun t => ?_, fun t => ?_⟩
  · rw [tilde_discInfl, tilde_discInfl]
    funext ω
    simp only [map_smul, hu.2 t, Pi.add_apply, Pi.smul_apply, smul_eq_mul, psiD]
    field_simp
    ring
  · rw [tilde_discInfl, smul_smul]

/-- **Exercise 5.4(a), inflation persistence** (Galí 2015, p. 161): in every discretionary
equilibrium with bounded `π̃`, `π_t = γ π_{t−1} + ϑ u_t/(κ² + ϑ(1 − βρ_u))`. -/
theorem ex5_4a_inflation {β κ γ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hϑ : 0 < ϑ) (hρ : |ρ| < 1) {p0 : Ω → ℝ} {u x p : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u)
    (hub : BoundedProc u) (he : DiscretionEq 𝔼 β κ γ ϑ p0 x p u)
    (hb : BoundedProc (tilde γ p0 p)) (t : ℕ) :
    p t = γ • prev p0 p t + psiD β κ ϑ ρ • u t := by
  have h := congrFun (ex5_4a_unique 𝔼 hβ0 hβ1 hκ hϑ hρ hu hub he hb).1 t
  simp only [tilde] at h
  rw [← h]
  abel

/-! ### (b) Commitment (deterministic) -/

/-- Galí (2015), Exercise 5.4(b): feasibility, `π̃_t = κ x_t + β π̃_{t+1} + u_t`. -/
def CFeasible (β κ : ℝ) (u x q : ℕ → ℝ) : Prop := ∀ t, q t = κ * x t + β * q (t + 1) + u t

/-- Galí (2015), Exercise 5.4(b): the date-`t` loss term `βᵗ (ϑ x_t² + π̃_t²)`. -/
def lossTerm (β ϑ : ℝ) (x q : ℕ → ℝ) (t : ℕ) : ℝ := β ^ t * (ϑ * x t ^ 2 + q t ^ 2)

/-- Galí (2015), Exercise 5.4, p. 161: the loss `∑ βᵗ (ϑ x_t² + π̃_t²)` (up to the factor `½`). -/
noncomputable def loss (β ϑ : ℝ) (x q : ℕ → ℝ) : ℝ := ∑' t, lossTerm β ϑ x q t

/-- Galí (2015), Exercise 5.4(b): optimality among bounded feasible plans. -/
def COptimal (β κ ϑ : ℝ) (u x q : ℕ → ℝ) : Prop :=
  CFeasible β κ u x q ∧ Bdd x ∧ Bdd q ∧
    ∀ x' q', CFeasible β κ u x' q' → Bdd x' → Bdd q' → loss β ϑ x q ≤ loss β ϑ x' q'

/-- **Exercise 5.4(b), the FOCs** (Galí 2015, p. 161; cf. p. 134): `ϑ x_t − κ ξ_t = 0`,
`π̃_t + ξ_t − ξ_{t−1} = 0`, `ξ_{−1} = 0`. -/
def CFOC (κ ϑ : ℝ) (x q ξ : ℕ → ℝ) : Prop :=
  ∀ t, ϑ * x t - κ * ξ t = 0 ∧ q t + ξ t - lag ξ t = 0

/-- Galí (2015), Exercise 5.4(b): the cross term `βᵗ (ϑ x_t dx_t + π̃_t dπ̃_t)`. -/
def cross (β ϑ : ℝ) (x q dx dq : ℕ → ℝ) (t : ℕ) : ℝ := β ^ t * (ϑ * x t * dx t + q t * dq t)

/-- Galí (2015), Exercise 5.4(b) (**summation by parts**): if `ϑ x = κ ξ`, then for every
homogeneous direction (`dπ̃_t = κ dx_t + β dπ̃_{t+1}`),
`∑_{t ≤ T} βᵗ(ϑ x dx + π̃ dπ̃) = ∑_{t ≤ T} βᵗ R_t dπ̃_t − β^{T+1} ξ_T dπ̃_{T+1}`,
`R_t = π̃_t + ξ_t − ξ_{t−1}`. -/
theorem partial_sum_identity {β κ ϑ : ℝ} {x q ξ dx dq : ℕ → ℝ}
    (hx : ∀ t, ϑ * x t = κ * ξ t) (hd : ∀ t, dq t = κ * dx t + β * dq (t + 1)) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), cross β ϑ x q dx dq t =
      ∑ t ∈ Finset.range (T + 1), β ^ t * ((q t + ξ t - lag ξ t) * dq t) -
        β ^ (T + 1) * ξ T * dq (T + 1) := by
  induction T with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, cross, pow_zero, one_mul, pow_one]
    rw [hx 0]
    simp only [lag]
    linear_combination (-ξ 0) * hd 0
  | succ T ih =>
    rw [Finset.sum_range_succ (fun t => cross β ϑ x q dx dq t) (T + 1), ih,
      Finset.sum_range_succ (fun t => β ^ t * ((q t + ξ t - lag ξ t) * dq t)) (T + 1)]
    generalize ∑ t ∈ Finset.range (T + 1), β ^ t * ((q t + ξ t - lag ξ t) * dq t) = S
    simp only [cross]
    rw [hx (T + 1)]
    simp only [lag]
    linear_combination (-β ^ (T + 1) * ξ (T + 1)) * hd (T + 1)

/-- Galí (2015), Exercise 5.4(b): the loss series of bounded paths is summable. -/
theorem loss_summable {β ϑ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hϑ : 0 ≤ ϑ) {x q : ℕ → ℝ}
    (hx : Bdd x) (hq : Bdd q) : Summable (lossTerm β ϑ x q) := by
  obtain ⟨A, hA⟩ := hx
  obtain ⟨B, hB⟩ := hq
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (ϑ * A ^ 2 + B ^ 2)) (fun t => ?_)
  rw [Real.norm_eq_abs, lossTerm, abs_mul, abs_pow, abs_of_nonneg hβ0]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 t)
  have h1 : x t ^ 2 ≤ A ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hA t) 2
  have h2 : q t ^ 2 ≤ B ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB t) 2
  rw [abs_of_nonneg (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h1 hϑ]

/-- Galí (2015), Exercise 5.4(b): the cross series of bounded paths is summable. -/
theorem cross_summable {β ϑ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {x q dx dq : ℕ → ℝ}
    (hx : Bdd x) (hq : Bdd q) (hdx : Bdd dx) (hdq : Bdd dq) :
    Summable (cross β ϑ x q dx dq) := by
  obtain ⟨A, hA⟩ := hx
  obtain ⟨B, hB⟩ := hq
  obtain ⟨D, hD⟩ := hdx
  obtain ⟨E, hE⟩ := hdq
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (|ϑ| * A * D + B * E)) (fun t => ?_)
  rw [Real.norm_eq_abs, cross, abs_mul, abs_pow, abs_of_nonneg hβ0]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 t)
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_mul, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hA t) (hD t) (abs_nonneg _) hA0) (abs_nonneg _)
  · rw [abs_mul]; exact mul_le_mul (hB t) (hE t) (abs_nonneg _) hB0

/-- Galí (2015), Exercise 5.4(b): two bounded plans that agree from date `k` on have losses
differing by the finite sum of the first `k` terms. -/
theorem loss_eq_of_eq_after {β ϑ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hϑ : 0 ≤ ϑ)
    {x q x' q' : ℕ → ℝ} (hx : Bdd x) (hq : Bdd q) (hx' : Bdd x') (hq' : Bdd q') (k : ℕ)
    (heq : ∀ t, x' (t + k) = x (t + k) ∧ q' (t + k) = q (t + k)) :
    loss β ϑ x' q' = loss β ϑ x q +
      ∑ t ∈ Finset.range k, (lossTerm β ϑ x' q' t - lossTerm β ϑ x q t) := by
  unfold loss
  rw [← (loss_summable hβ0 hβ1 hϑ hx' hq').sum_add_tsum_nat_add k,
    ← (loss_summable hβ0 hβ1 hϑ hx hq).sum_add_tsum_nat_add k, Finset.sum_sub_distrib]
  have : ∑' t, lossTerm β ϑ x' q' (t + k) = ∑' t, lossTerm β ϑ x q (t + k) :=
    tsum_congr fun t => by simp only [lossTerm, (heq t).1, (heq t).2]
  rw [this]
  ring

/-- **Exercise 5.4(b), sufficiency** (Galí 2015, p. 161): a bounded feasible plan satisfying
the FOCs is optimal among bounded feasible plans, and it is the only optimal one. -/
theorem ex5_4b_sufficient {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hϑ : 0 < ϑ)
    {u x q ξ : ℕ → ℝ} (hf : CFeasible β κ u x q) (hx : Bdd x) (hq : Bdd q)
    (hfoc : CFOC κ ϑ x q ξ) :
    COptimal β κ ϑ u x q ∧
      ∀ x' q', CFeasible β κ u x' q' → Bdd x' → Bdd q' → loss β ϑ x' q' ≤ loss β ϑ x q →
        x' = x ∧ q' = q := by
  have hξe : ξ = fun t => (ϑ / κ) * x t + 0 * x t := by
    funext t
    have := (hfoc t).1
    field_simp
    linear_combination -this
  have hξ : Bdd ξ := by rw [hξe]; exact bdd_lin hx hx _ _
  have hbd : ∀ (z z' : ℕ → ℝ), Bdd z → Bdd z' → Bdd fun t => z' t - z t := by
    intro z z' hz hz'
    have := bdd_lin hz' hz 1 (-1); simpa [sub_eq_add_neg] using this
  have key : ∀ x' q', CFeasible β κ u x' q' → Bdd x' → Bdd q' →
      loss β ϑ x' q' = loss β ϑ x q + loss β ϑ (fun t => x' t - x t) (fun t => q' t - q t) := by
    intro x' q' hf' hx' hq'
    set dx : ℕ → ℝ := fun t => x' t - x t
    set dq : ℕ → ℝ := fun t => q' t - q t
    have hd : ∀ t, dq t = κ * dx t + β * dq (t + 1) := fun t => by
      simp only [dx, dq]; linear_combination hf' t - hf t
    have hbdx : Bdd dx := hbd x x' hx hx'
    have hbdq : Bdd dq := hbd q q' hq hq'
    have hcs := cross_summable (ϑ := ϑ) hβ0.le hβ1 hx hq hbdx hbdq
    have hxf : ∀ t, ϑ * x t = κ * ξ t := fun t => by linarith [(hfoc t).1]
    have hpart : ∀ T, ∑ t ∈ Finset.range (T + 1), cross β ϑ x q dx dq t =
        -(β ^ (T + 1) * ξ T * dq (T + 1)) := by
      intro T
      rw [partial_sum_identity hxf hd T]
      simp [(hfoc _).2]
    obtain ⟨A, hA⟩ := hξ
    obtain ⟨E, hE⟩ := hbdq
    have hbound : ∀ T, ‖-(β ^ (T + 1) * ξ T * dq (T + 1))‖ ≤ β ^ (T + 1) * (A * E) := by
      intro T
      have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
      rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos hβ0, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hA T) (hE (T + 1)) (abs_nonneg _) hA0)
        (pow_nonneg hβ0.le _)
    have hlim : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), cross β ϑ x q dx dq t)
        atTop (𝓝 0) := by
      simp only [hpart]
      refine squeeze_zero_norm hbound ?_
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).comp
        (tendsto_add_atTop_nat 1)).mul_const (A * E)
    have htsum : ∑' t, cross β ϑ x q dx dq t = 0 :=
      tendsto_nhds_unique ((hcs.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)) hlim
    have hl := loss_summable hβ0.le hβ1 hϑ.le hx hq
    have hqq := loss_summable hβ0.le hβ1 hϑ.le hbdx ⟨E, hE⟩
    have hsplit : lossTerm β ϑ x' q' = fun t => lossTerm β ϑ x q t +
        2 * cross β ϑ x q dx dq t + lossTerm β ϑ dx dq t := by
      funext t
      simp only [lossTerm, cross, dx, dq]
      ring
    unfold loss
    rw [hsplit, (hl.add (hcs.mul_left 2)).tsum_add hqq, hl.tsum_add (hcs.mul_left 2),
      tsum_mul_left, htsum, mul_zero, add_zero]
  have hqnn : ∀ dx dq : ℕ → ℝ, ∀ t, 0 ≤ lossTerm β ϑ dx dq t := fun dx dq t => by
    unfold lossTerm; positivity
  refine ⟨⟨hf, hx, hq, fun x' q' hf' hx' hq' => ?_⟩, fun x' q' hf' hx' hq' hle => ?_⟩
  · rw [key x' q' hf' hx' hq']
    exact le_add_of_nonneg_right (tsum_nonneg (hqnn _ _))
  · rw [key x' q' hf' hx' hq'] at hle
    have h0 : loss β ϑ (fun t => x' t - x t) (fun t => q' t - q t) ≤ 0 := by linarith
    have hs := loss_summable hβ0.le hβ1 hϑ.le (hbd x x' hx hx') (hbd q q' hq hq')
    have hz : ∀ t, lossTerm β ϑ (fun t => x' t - x t) (fun t => q' t - q t) t = 0 := fun t =>
      le_antisymm ((hs.le_tsum t (fun j _ => hqnn _ _ j)).trans h0) (hqnn _ _ t)
    have hall : ∀ t, x' t - x t = 0 ∧ q' t - q t = 0 := by
      intro t
      have h := hz t
      simp only [lossTerm] at h
      have hin : ϑ * (x' t - x t) ^ 2 + (q' t - q t) ^ 2 = 0 := by
        rcases mul_eq_zero.mp h with h | h
        · exact absurd h (pow_ne_zero t hβ0.ne')
        · exact h
      have a1 := mul_nonneg hϑ.le (sq_nonneg (x' t - x t))
      have a2 := sq_nonneg (q' t - q t)
      refine ⟨?_, pow_eq_zero_iff two_ne_zero |>.mp (by linarith)⟩
      have : (x' t - x t) ^ 2 = 0 := by
        rcases mul_eq_zero.mp (show ϑ * (x' t - x t) ^ 2 = 0 by linarith) with h | h
        · exact absurd h hϑ.ne'
        · exact h
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    exact ⟨funext fun t => sub_eq_zero.mp (hall t).1, funext fun t => sub_eq_zero.mp (hall t).2⟩

/-- Galí (2015), Exercise 5.4(b): the test direction `dπ̃ = 𝟙_{t = s}`. -/
def dirQ (s : ℕ) : ℕ → ℝ := fun t => if t = s then 1 else 0

/-- Galí (2015), Exercise 5.4(b): the output part of the test direction,
`dx_t = (dπ̃_t − β dπ̃_{t+1})/κ`. -/
noncomputable def dirX (β κ : ℝ) (s : ℕ) : ℕ → ℝ := fun t => (dirQ s t - β * dirQ s (t + 1)) / κ

/-- **Exercise 5.4(b), necessity** (Galí 2015, p. 161): an optimal bounded feasible plan
satisfies the FOCs with `ξ = (ϑ/κ) x`. -/
theorem ex5_4b_necessary {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hϑ : 0 ≤ ϑ)
    {u x q : ℕ → ℝ} (hopt : COptimal β κ ϑ u x q) :
    CFOC κ ϑ x q (fun t => ϑ / κ * x t) := by
  obtain ⟨hf, hx, hq, hmin⟩ := hopt
  set ξ : ℕ → ℝ := fun t => ϑ / κ * x t
  have hxf : ∀ t, ϑ * x t = κ * ξ t := fun t => by simp only [ξ]; field_simp
  intro s
  refine ⟨by linarith [hxf s], ?_⟩
  have h0 : Bdd (dirQ s) := ⟨1, fun t => by simp only [dirQ]; split_ifs <;> simp⟩
  have h1 : Bdd (dirX β κ s) := by
    have := bdd_lin h0 (bdd_shift h0) κ⁻¹ (-β / κ)
    refine this.elim fun M hM => ⟨M, fun t => ?_⟩
    have e : dirX β κ s t = κ⁻¹ * dirQ s t + -β / κ * dirQ s (t + 1) := by
      simp only [dirX]; ring
    rw [e]; exact hM t
  have hd : ∀ t, dirQ s t = κ * dirX β κ s t + β * dirQ s (t + 1) := fun t => by
    simp only [dirX]; field_simp; ring
  have hz : ∀ t, s < t → dirQ s t = 0 ∧ dirX β κ s t = 0 := by
    have hp : ∀ u, s < u → dirQ s u = 0 := fun u hu => by
      simp only [dirQ]
      split_ifs
      · omega
      · rfl
    intro t ht
    refine ⟨hp t ht, ?_⟩
    simp only [dirX]; rw [hp t ht, hp (t + 1) (by omega)]; simp
  set C := ∑ t ∈ Finset.range (s + 1), cross β ϑ x q (dirX β κ s) (dirQ s) t
  set Q := ∑ t ∈ Finset.range (s + 1), lossTerm β ϑ (dirX β κ s) (dirQ s) t
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun t _ => by unfold lossTerm; positivity
  have hquad : ∀ ε : ℝ, 0 ≤ 2 * ε * C + ε ^ 2 * Q := by
    intro ε
    have hb : ∀ z d : ℕ → ℝ, Bdd z → Bdd d → Bdd fun t => z t + ε * d t := fun z d hz' hd' => by
      have := bdd_lin hz' hd' 1 ε; simpa using this
    have hf' : CFeasible β κ u (fun t => x t + ε * dirX β κ s t) (fun t => q t + ε * dirQ s t) :=
      fun t => by linear_combination hf t + ε * hd t
    have hle := hmin _ _ hf' (hb _ _ hx h1) (hb _ _ hq h0)
    rw [loss_eq_of_eq_after hβ0.le hβ1 hϑ hx hq (hb _ _ hx h1) (hb _ _ hq h0) (s + 1)
      (fun t => by
        obtain ⟨a1, a2⟩ := hz (t + (s + 1)) (by omega)
        simp [a1, a2])] at hle
    have hsum : ∑ t ∈ Finset.range (s + 1),
        (lossTerm β ϑ (fun t => x t + ε * dirX β κ s t) (fun t => q t + ε * dirQ s t) t -
          lossTerm β ϑ x q t) = 2 * ε * C + ε ^ 2 * Q := by
      simp only [C, Q, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [lossTerm, cross]
      ring
    linarith
  have hC := eq_zero_of_quadratic hQ hquad
  have hid := partial_sum_identity (q := q) hxf hd s
  rw [(hz (s + 1) (by omega)).1] at hid
  have hsingle : ∑ t ∈ Finset.range (s + 1), β ^ t * ((q t + ξ t - lag ξ t) * dirQ s t) =
      β ^ s * (q s + ξ s - lag ξ s) := by
    rw [Finset.sum_eq_single s (fun t _ hts => by simp [dirQ, hts])
      (fun h => absurd (Finset.mem_range.mpr (Nat.lt_succ_self s)) h)]
    simp [dirQ]
  rw [hsingle] at hid
  have : β ^ s * (q s + ξ s - lag ξ s) = 0 := by
    have hC' : C = 0 := hC
    simp only [C] at hC'
    rw [hC'] at hid
    simp only [mul_zero, sub_zero] at hid
    linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (pow_ne_zero s hβ0.ne')
  · exact h

/-- **Exercise 5.4(b)** (Galí 2015, p. 161): a bounded feasible plan is optimal under commitment
iff it satisfies the FOCs for some multiplier. -/
theorem ex5_4b_optimal_iff {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hϑ : 0 < ϑ)
    {u x q : ℕ → ℝ} (hf : CFeasible β κ u x q) (hx : Bdd x) (hq : Bdd q) :
    COptimal β κ ϑ u x q ↔ ∃ ξ, CFOC κ ϑ x q ξ :=
  ⟨fun h => ⟨_, ex5_4b_necessary hβ0 hβ1 hκ hϑ.le h⟩,
    fun ⟨_, h⟩ => (ex5_4b_sufficient hβ0 hβ1 hκ hϑ hf hx hq h).1⟩

/-- Galí (2015), Exercise 5.4(b): the quasi-differenced price level `p̃_t = ∑_{s ≤ t} π̃_s`. -/
def cumsum (q : ℕ → ℝ) (t : ℕ) : ℝ := ∑ s ∈ Finset.range (t + 1), q s

/-- **Exercise 5.4(b), the `p̃`-level rule** (Galí 2015, p. 161; cf. (13), p. 135): the FOCs
hold for some multiplier iff `x_t = −(κ/ϑ) p̃_t` for all `t`. -/
theorem foc_iff_level_rule {κ ϑ : ℝ} (hϑ : ϑ ≠ 0) {x q : ℕ → ℝ} :
    (∃ ξ, CFOC κ ϑ x q ξ) ↔ ∀ t, x t = -(κ / ϑ) * cumsum q t := by
  constructor
  · rintro ⟨ξ, hfoc⟩
    have hξ : ∀ t, ξ t = -cumsum q t := by
      intro t
      induction t with
      | zero =>
        have := (hfoc 0).2
        simp only [lag] at this
        simp only [cumsum, zero_add, Finset.sum_range_one]
        linarith
      | succ t ih =>
        have := (hfoc (t + 1)).2
        simp only [lag] at this
        simp only [cumsum] at ih ⊢
        rw [Finset.sum_range_succ]
        linarith
    intro t
    have := (hfoc t).1
    rw [hξ t] at this
    field_simp
    linear_combination this
  · intro h
    refine ⟨fun t => -cumsum q t, fun t => ⟨?_, ?_⟩⟩
    · rw [h t]; field_simp; ring
    · rcases t with _ | t
      · simp [lag, cumsum]
      · simp only [lag, cumsum]
        rw [Finset.sum_range_succ]
        ring

/-- Galí (2015), Exercise 5.4(b): the level rule is equivalent to the difference rule
`x_t − x_{t−1} = −(κ/ϑ) π̃_t` with `x_{−1} = 0`. -/
theorem level_rule_iff_diff {κ ϑ : ℝ} {x q : ℕ → ℝ} :
    (∀ t, x t = -(κ / ϑ) * cumsum q t) ↔ ∀ t, x t - lag x t = -(κ / ϑ) * q t := by
  constructor
  · intro h t
    rcases t with _ | t
    · simp [lag, h 0, cumsum]
    · simp only [lag, h (t + 1), h t, cumsum]
      rw [Finset.sum_range_succ]
      ring
  · intro h t
    induction t with
    | zero =>
      have := h 0
      simp only [lag, sub_zero] at this
      simp [cumsum, this]
    | succ t ih =>
      have := h (t + 1)
      simp only [lag] at this
      simp only [cumsum] at ih ⊢
      rw [Finset.sum_range_succ]
      linear_combination this + ih

/-- Galí (2015), Exercise 5.4(b): with the log price level `P` (`P 0 = p_{−2}`, `P 1 = p_{−1}`,
`P (t+2) = p_t`), inflation `π_t = p_t − p_{t−1}` and `π_{−1} = p_{−1} − p_{−2}`,
`p̃_t = ∑_{s ≤ t} (π_s − γ π_{s−1}) = (p_t − p_{−1}) − γ (p_{t−1} − p_{−2})`. -/
theorem cumsum_tilde_eq (γ : ℝ) (P : ℕ → ℝ) (t : ℕ) :
    cumsum (fun s => (P (s + 2) - P (s + 1)) - γ * (P (s + 1) - P s)) t =
      (P (t + 2) - P 1) - γ * (P (t + 1) - P 0) := by
  induction t with
  | zero => simp [cumsum]
  | succ t ih =>
    simp only [cumsum] at ih ⊢
    rw [Finset.sum_range_succ, ih]
    ring

/-- **Exercise 5.4(b), optimal commitment policy** (Galí 2015, p. 161): with
`π̃_t = π_t − γ π_{t−1}` and the log price level `P` as in `cumsum_tilde_eq`, a bounded feasible
plan is optimal under commitment iff
`x_t = −(κ/ϑ)[(p_t − p_{−1}) − γ (p_{t−1} − p_{−2})]` for all `t ≥ 0`. -/
theorem ex5_4b {β κ ϑ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hϑ : 0 < ϑ)
    {u x : ℕ → ℝ} (P : ℕ → ℝ)
    (hf : CFeasible β κ u x (fun s => (P (s + 2) - P (s + 1)) - γ * (P (s + 1) - P s)))
    (hx : Bdd x) (hq : Bdd fun s => (P (s + 2) - P (s + 1)) - γ * (P (s + 1) - P s)) :
    COptimal β κ ϑ u x (fun s => (P (s + 2) - P (s + 1)) - γ * (P (s + 1) - P s)) ↔
      ∀ t, x t = -(κ / ϑ) * ((P (t + 2) - P 1) - γ * (P (t + 1) - P 0)) := by
  rw [ex5_4b_optimal_iff hβ0 hβ1 hκ hϑ hf hx hq, foc_iff_level_rule hϑ.ne']
  simp only [cumsum_tilde_eq]

end Gali.DiscretionCommitment.Ex5_4
