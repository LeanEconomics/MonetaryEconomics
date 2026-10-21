/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MonetaryPolicyDesign.Expectations
import MonetaryPolicyDesign.Welfare
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.FinCases

/-!
# Two simple monetary policy rules

Galí (2015), Chapter 4, §4.4.1–4.4.2, pp. 111–116: a Taylor rule on output and a
constant money growth rule, evaluated with the loss function of `Welfare`.

## The Taylor rule (19)

* `rule19_iff_rule20`: `i_t = ρ + φ_π π_t + φ_y ŷ_t` is the gap rule (20) with the
  pseudo-shock `v_t = φ_y ŷ^n_t`.
* `equilibrium_iff_solves`: the equilibrium is `x_t = A_T E_t x_{t+1} + B_T(r̂^n_t − v_t)`
  (ch. 3's system with `v` reinterpreted); `schurStable_AT_iff`, `determinate_iff`: it is
  determinate iff (14) holds.
* `natRate_eq`, `drivingForce_eq`: with AR(1) technology,
  `r̂^n_t − v_t = −ψ_ya(σ(1 − ρ_a) + φ_y) a_t + (1 − ρ_z) z_t`.
* `equilibrium_iff_msv` (both shocks), `equilibrium_iff_msv_single`: under (14) the MSV
  solution `ỹ = ∑ ψ_y(ρ_k) c_k s_k`, `π = ∑ ψ_π(ρ_k) c_k s_k` exists and is the unique
  bounded equilibrium (uniqueness from the core's `system_unique`).
* `msvLoss`, `msvLoss_eq`, `msv_moments`, `equilibrium_loss`: the loss is
  `½[(σ + (φ+α)/(1−α)) ψ_y² + (ε/λ) ψ_π²] c² var(s)`, for any second-moment functional
  homogeneous of degree two (`variance_isSecondMoment`: Mathlib's variance is one);
  `ar1Var`, `ar1Var_fixed_point`, `ar1Var_hasSum`: the stationary AR(1) variance
  `σ_e²/(1 − ρ²)`.
* `msvLoss_tendsto_zero` (fn. 10): the variances of the gap and of inflation and the loss
  tend to `0` as `φ_π → ∞`.

## The constant money growth rule

`moneyDemand_iff_plus`, `constantMoney_iff_plus`, `predetermined_plus`,
`constantMoney_iff_system34`: with `l^+_t = l_t + ζ_t`, the model under `Δm_t = 0` is exactly
ch. 3's system (34) with shock vector `(r̂^n_t, ŷ^n_t, Δζ_t)`.

## Table 4.1

`table41_tech_1` … `table41_tech_4`, `table41_demand_1` … `table41_demand_4`: all 32 printed
entries follow from the closed forms at the baseline (`kappa_base`, `lambda_base`,
`gapCoeff_base`, `psiYA_base`), proved by `norm_num`. The book **truncates** to the printed
digits (`table41_truncated`: eight entries would differ under rounding).
-/

namespace Gali.MonetaryPolicyDesign.SimpleRules

open Filter Topology Welfare

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The model under the Taylor rule (19) -/

/-- Galí (2015), eq. (7), p. 103 (ch. 3, eq. (22)): the New Keynesian Phillips curve
`π_t = β E_t π_{t+1} + κ ỹ_t`. -/
def NKPC (β κ : ℝ) (ygap infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t

/-- Galí (2015), eq. (6), p. 103 (ch. 3, eq. (23)): the dynamic IS equation
`ỹ_t = −σ⁻¹(i_t − E_t π_{t+1} − r^n_t) + E_t ỹ_{t+1}`. -/
def DIS (σ : ℝ) (ygap i infl rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ygap t = -σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - rn t) + 𝔼.E t (ygap (t + 1))

omit 𝔼 in
/-- Galí (2015), eq. (19), p. 111: the Taylor rule `i_t = ρ + φ_π π_t + φ_y ŷ_t`, with
`ŷ_t = log(Y_t/Y)` the deviation of output from steady state. -/
def TaylorRule (ρ φπ φy : ℝ) (i infl yhat : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = (fun _ => ρ) + φπ • infl t + φy • yhat t

omit 𝔼 in
/-- Galí (2015), p. 112: the pseudo-shock `v_t = φ_y ŷ^n_t`. -/
def pseudoShock (φy : ℝ) (yhatn : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => φy • yhatn t

omit 𝔼 in
/-- Galí (2015), eq. (20), p. 112: the rule in terms of the output gap,
`i_t = ρ + φ_π π_t + φ_y ỹ_t + v_t`. -/
def TaylorRuleGap (ρ φπ φy : ℝ) (i infl ygap v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = (fun _ => ρ) + φπ • infl t + φy • ygap t + v t

omit 𝔼 in
/-- Galí (2015), eqs. (19)–(20), p. 112: since `ŷ_t = ỹ_t + ŷ^n_t`, the Taylor rule (19) on
output is the gap rule (20) with the pseudo-shock `v_t = φ_y ŷ^n_t`. -/
theorem rule19_iff_rule20 {ρ φπ φy : ℝ} {i infl yhat ygap yhatn : ℕ → Ω → ℝ}
    (hyhat : ∀ t, yhat t = ygap t + yhatn t) :
    TaylorRule ρ φπ φy i infl yhat ↔
      TaylorRuleGap ρ φπ φy i infl ygap (pseudoShock φy yhatn) := by
  simp only [TaylorRule, TaylorRuleGap, pseudoShock, hyhat, smul_add, add_assoc]

omit 𝔼 in
/-- Galí (2015), p. 112: the driving force of the system, `r̂^n_t − v_t = r^n_t − ρ − v_t`. -/
def drivingForce (ρ : ℝ) (rn v : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => rn t - (fun _ => ρ) - v t

/-- Galí (2015), §4.4.1, pp. 111–112: an equilibrium under the Taylor rule (19): the NKPC,
the DIS and rule (19) with output `ŷ_t = ỹ_t + ŷ^n_t`. -/
def Equilibrium (β σ κ ρ φπ φy : ℝ) (rn yhatn ygap infl i : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl rn ∧
    TaylorRule ρ φπ φy i infl (fun t => ygap t + yhatn t)

/-- Galí (2015), p. 112 (ch. 3, p. 65): the equilibrium conditions with the interest rate
substituted out, `(σ + φ_y) ỹ_t + φ_π π_t = σ E_t ỹ_{t+1} + E_t π_{t+1} + u_t` and the NKPC. -/
def Structural (β σ κ φπ φy : ℝ) (u ygap infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (σ + φy) • ygap t + φπ • infl t
      = σ • 𝔼.E t (ygap (t + 1)) + 𝔼.E t (infl (t + 1)) + u t ∧
    infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t

/-- Galí (2015), p. 112: `Ω = 1/(σ + φ_y + κ φ_π)`. -/
noncomputable def omega (σ κ φπ φy : ℝ) : ℝ := 1 / (σ + φy + κ * φπ)

/-- Galí (2015), p. 112 (restated from the Chapter 3 project): the matrix
`A_T = Ω [[σ, 1 − βφ_π], [σκ, κ + β(σ + φ_y)]]`. -/
noncomputable def AT (β σ κ φπ φy : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![omega σ κ φπ φy * σ, omega σ κ φπ φy * (1 - β * φπ);
    omega σ κ φπ φy * (σ * κ), omega σ κ φπ φy * (κ + β * (σ + φy))]

/-- Galí (2015), p. 112: the vector `B_T = Ω (1, κ)`. -/
noncomputable def BT (σ κ φπ φy : ℝ) : Fin 2 → ℝ := ![omega σ κ φπ φy, omega σ κ φπ φy * κ]

omit 𝔼 in
/-- Galí (2015), p. 112: the stacked vector `x_t = (ỹ_t, π_t)`. -/
def stack (ygap infl : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![ygap t, infl t]

omit 𝔼 in
/-- Galí (2015), p. 112: the forcing term `B_T (r^n_t − v_t)`. -/
def forcing (b : Fin 2 → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t j => b j • u t

/-- Galí (2015), p. 112 (restated from the Chapter 3 project): with the gap rule (20), the
NKPC and the DIS hold iff the structural equations hold with `u = r̂^n − v`. -/
theorem nk_iff_structural {β σ κ ρ φπ φy : ℝ} (hσ : σ ≠ 0) {rn v ygap infl i : ℕ → Ω → ℝ}
    (hrule : TaylorRuleGap ρ φπ φy i infl ygap v) :
    (NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl rn) ↔
      Structural 𝔼 β σ κ φπ φy (drivingForce ρ rn v) ygap infl := by
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  constructor
  · rintro ⟨hp, hd⟩ t
    refine ⟨?_, hp t⟩
    funext ω
    have e := congrFun (hd t) ω
    have r := congrFun (hrule t) ω
    simp only [drivingForce, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e r ⊢
    linear_combination σ * e - r - (i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) * hinv
  · intro h
    refine ⟨fun t => (h t).2, fun t => ?_⟩
    funext ω
    have e := congrFun (h t).1 ω
    have r := congrFun (hrule t) ω
    simp only [drivingForce, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e r ⊢
    linear_combination σ⁻¹ * e + σ⁻¹ * r - (ygap t ω - 𝔼.E t (ygap (t + 1)) ω) * hinv

/-- Galí (2015), p. 112 (restated from the Chapter 3 project): the structural equations are
equivalent to `x_t = A_T E_t x_{t+1} + B_T u_t`, provided `σ + φ_y + κ φ_π ≠ 0`. -/
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

/-- Galí (2015), p. 112 (**the system under rule (19)**): `(ỹ, π, i)` is an equilibrium under
the Taylor rule (19) iff `i` is given by the rule and `x_t = (ỹ_t, π_t)` solves
`x_t = A_T E_t x_{t+1} + B_T (r̂^n_t − v_t)` with the pseudo-shock `v_t = φ_y ŷ^n_t`: the
dynamics of ch. 3's rule, with `v` reinterpreted. -/
theorem equilibrium_iff_solves {β σ κ ρ φπ φy : ℝ} (hσ : σ ≠ 0)
    (hS : σ + φy + κ * φπ ≠ 0) {rn yhatn ygap infl i : ℕ → Ω → ℝ}
    (hrule : TaylorRule ρ φπ φy i infl (fun t => ygap t + yhatn t)) :
    Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn ygap infl i ↔
      𝔼.Solves (AT β σ κ φπ φy)
        (forcing (BT σ κ φπ φy) (drivingForce ρ rn (pseudoShock φy yhatn))) (stack ygap infl) := by
  have hgap := (rule19_iff_rule20 (fun _ => rfl)).mp hrule
  rw [← structural_iff_solves 𝔼 hS, ← nk_iff_structural 𝔼 hσ hgap]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hrule⟩⟩

/-- Galí (2015), p. 112 (restated from the Chapter 3 project): the trace of `A_T`. -/
theorem tr2_AT {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0) :
    tr2 (AT β σ κ φπ φy) = (σ * (1 + β) + κ + β * φy) / (σ + φy + κ * φπ) := by
  simp only [tr2, AT, omega, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), p. 112 (restated from the Chapter 3 project): the determinant of `A_T`. -/
theorem det2_AT {β σ κ φπ φy : ℝ} (hS : σ + φy + κ * φπ ≠ 0) :
    det2 (AT β σ κ φπ φy) = σ * β / (σ + φy + κ * φπ) := by
  simp only [det2, AT, omega, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), eq. (14), p. 106, as required on p. 111 (restated from the Chapter 3
project, Bullard–Mitra): for `σ, κ > 0`, `0 < β < 1`, `φ_π, φ_y ≥ 0`, both eigenvalues of `A_T`
lie inside the unit circle iff `κ(φ_π − 1) + (1 − β)φ_y > 0`. -/
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

/-- Galí (2015), p. 111: under rule (19) the system is determinate iff (14) holds (the
pseudo-shock is exogenous, so determinacy is that of ch. 3's rule). -/
theorem determinate_iff [Nonempty Ω] {β σ κ φπ φy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    𝔼.Determinate (AT β σ κ φπ φy) ↔ 0 < κ * (φπ - 1) + (1 - β) * φy :=
  (𝔼.determinate_iff _).trans (schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy)

omit 𝔼 in
/-- Restated from the Chapter 3 project: two bounded processes stack to a bounded vector. -/
theorem boundedVec_stack {a b : ℕ → Ω → ℝ} (ha : BoundedProc a) (hb : BoundedProc b) :
    BoundedVec (stack a b) := by
  obtain ⟨M₁, h₁⟩ := ha
  obtain ⟨M₂, h₂⟩ := hb
  refine ⟨max M₁ M₂, fun t j ω => ?_⟩
  fin_cases j
  · exact (h₁ t ω).trans (le_max_left _ _)
  · exact (h₂ t ω).trans (le_max_right _ _)

/-- Restated from the Chapter 3 project: two adapted processes stack to an adapted vector. -/
theorem adaptedVec_stack {a b : ℕ → Ω → ℝ} (ha : 𝔼.Adapted a) (hb : 𝔼.Adapted b) :
    𝔼.AdaptedVec (stack a b) := by
  intro t j
  fin_cases j
  · exact ha t
  · exact hb t

/-! ### The driving force (20) -/

/-- Galí (2015), p. 112 (with ch. 3, p. 62): with AR(1) technology `E_t a_{t+1} = ρ_a a_t`,
natural output `ŷ^n_t = ψ_ya a_t` and the natural rate
`r^n_t = ρ + σ E_t Δŷ^n_{t+1} + (1 − ρ_z) z_t`, one has
`r^n_t − ρ = −σψ_ya(1 − ρ_a) a_t + (1 − ρ_z) z_t`. -/
theorem natRate_eq {σ ρ ρa ρz ψya : ℝ} {a z rn yhatn : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (hyn : ∀ t, yhatn t = ψya • a t)
    (hrn : ∀ t, rn t = (fun _ => ρ) + σ • (𝔼.E t (yhatn (t + 1)) - yhatn t) + (1 - ρz) • z t)
    (t : ℕ) : rn t - (fun _ => ρ) = (-(σ * ψya * (1 - ρa))) • a t + (1 - ρz) • z t := by
  rw [hrn t, hyn t, hyn (t + 1), map_smul, ha.2 t]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), p. 112 (**the driving force under rule (19)**):
`r̂^n_t − v_t = −σψ_ya(1 − ρ_a)a_t − φ_yψ_ya a_t + (1 − ρ_z)z_t
= −ψ_ya(σ(1 − ρ_a) + φ_y) a_t + (1 − ρ_z) z_t`. -/
theorem drivingForce_eq {σ ρ ρa ρz ψya φy : ℝ} {a z rn yhatn : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (hyn : ∀ t, yhatn t = ψya • a t)
    (hrn : ∀ t, rn t = (fun _ => ρ) + σ • (𝔼.E t (yhatn (t + 1)) - yhatn t) + (1 - ρz) • z t)
    (t : ℕ) :
    drivingForce ρ rn (pseudoShock φy yhatn) t
      = (-(ψya * (σ * (1 - ρa) + φy))) • a t + (1 - ρz) • z t := by
  have h := natRate_eq 𝔼 ha hyn hrn t
  unfold drivingForce pseudoShock
  rw [h, hyn t]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### Minimum-state-variable solutions -/

/-- Galí (2015), p. 66 (used on p. 113): the denominator
`(1 − βρ)(σ(1 − ρ) + φ_y) + κ(φ_π − ρ)` of `Λ`. -/
def msvDen (β σ κ φπ φy ρu : ℝ) : ℝ := (1 - β * ρu) * (σ * (1 - ρu) + φy) + κ * (φπ - ρu)

/-- Galí (2015), p. 66: `Λ = 1/msvDen`. -/
noncomputable def msvLambda (β σ κ φπ φy ρu : ℝ) : ℝ := 1 / msvDen β σ κ φπ φy ρu

/-- Galí (2015), p. 66: the MSV output-gap coefficient `ψ_y = (1 − βρ) Λ`. -/
noncomputable def msvPsiY (β σ κ φπ φy ρu : ℝ) : ℝ := (1 - β * ρu) * msvLambda β σ κ φπ φy ρu

/-- Galí (2015), p. 66: the MSV inflation coefficient `ψ_π = κ Λ`. -/
noncomputable def msvPsiPi (β σ κ φπ φy ρu : ℝ) : ℝ := κ * msvLambda β σ κ φπ φy ρu

/-- Galí (2015), p. 66 (restated from the Chapter 3 project): `msvDen = (1 − ρ)((1 − βρ)σ + κ
+ βφ_y) + [κ(φ_π − 1) + (1 − β)φ_y]`. -/
theorem msvDen_eq (β σ κ φπ φy ρu : ℝ) :
    msvDen β σ κ φπ φy ρu
      = (1 - ρu) * ((1 - β * ρu) * σ + κ + β * φy) + (κ * (φπ - 1) + (1 - β) * φy) := by
  unfold msvDen; ring

/-- Galí (2015), p. 66 (restated from the Chapter 3 project): under (14) and `ρ < 1`,
`msvDen > 0`. -/
theorem msvDen_pos {β σ κ φπ φy ρu : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφy : 0 ≤ φy) (hρ1 : ρu < 1)
    (h14 : 0 < κ * (φπ - 1) + (1 - β) * φy) : 0 < msvDen β σ κ φπ φy ρu := by
  rw [msvDen_eq]
  have hbr : β * ρu < 1 := by nlinarith
  have h1 : 0 ≤ (1 - β * ρu) * σ := by nlinarith
  have h2 : 0 ≤ (1 - ρu) * ((1 - β * ρu) * σ + κ + β * φy) := by
    apply mul_nonneg <;> nlinarith
  linarith

/-- Restated from the Chapter 3 project: a scalar multiple of an AR(1) process is AR(1). -/
theorem isAR1_smul {ρu : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρu u) (c : ℝ) :
    𝔼.IsAR1 ρu (fun t => c • u t) :=
  ⟨fun t => by simp only [map_smul, hu.1 t], fun t => by
    simp only [map_smul, hu.2 t, smul_comm c ρu]⟩

/-- Galí (2015), p. 66 (restated from the Chapter 3 project): for an AR(1) driving force with
persistence `ρ` and `msvDen ≠ 0`, `ỹ_t = ψ_y u_t`, `π_t = ψ_π u_t` satisfy the structural
equations. -/
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

/-- Galí (2015), p. 112: the structural equations are linear, so solutions for two driving
forces add up to a solution for their sum. -/
theorem structural_add {β σ κ φπ φy : ℝ} {u₁ u₂ y₁ y₂ p₁ p₂ : ℕ → Ω → ℝ}
    (h₁ : Structural 𝔼 β σ κ φπ φy u₁ y₁ p₁) (h₂ : Structural 𝔼 β σ κ φπ φy u₂ y₂ p₂) :
    Structural 𝔼 β σ κ φπ φy (fun t => u₁ t + u₂ t) (fun t => y₁ t + y₂ t)
      (fun t => p₁ t + p₂ t) := by
  intro t
  obtain ⟨a₁, b₁⟩ := h₁ t
  obtain ⟨a₂, b₂⟩ := h₂ t
  simp only [map_add]
  refine ⟨?_, ?_⟩
  · rw [smul_add, smul_add, smul_add]
    calc (σ + φy) • y₁ t + (σ + φy) • y₂ t + (φπ • p₁ t + φπ • p₂ t)
        = ((σ + φy) • y₁ t + φπ • p₁ t) + ((σ + φy) • y₂ t + φπ • p₂ t) := by abel
      _ = _ := by rw [a₁, a₂]; abel
  · rw [smul_add, smul_add, b₁, b₂]
    abel

omit 𝔼 in
/-- Galí (2015), p. 112: a linear combination of bounded processes is bounded. -/
theorem boundedProc_lin {a z : ℕ → Ω → ℝ} (ha : BoundedProc a) (hz : BoundedProc z)
    (c₁ c₂ : ℝ) : BoundedProc (fun t => c₁ • a t + c₂ • z t) := by
  obtain ⟨M₁, h₁⟩ := ha
  obtain ⟨M₂, h₂⟩ := hz
  refine ⟨|c₁| * M₁ + |c₂| * M₂, fun t ω => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (h₁ t ω) (abs_nonneg _))
    (mul_le_mul_of_nonneg_left (h₂ t ω) (abs_nonneg _))

/-- Galí (2015), p. 112: a linear combination of adapted processes is adapted. -/
theorem adapted_lin {a z : ℕ → Ω → ℝ} (ha : 𝔼.Adapted a) (hz : 𝔼.Adapted z) (c₁ c₂ : ℝ) :
    𝔼.Adapted (fun t => c₁ • a t + c₂ • z t) := fun t => by
  simp only [map_add, map_smul, ha t, hz t]

/-- Galí (2015), pp. 112–113 (**the MSV solution under rule (19), existence and uniqueness**).
Let technology `a` and preferences `z` be bounded AR(1) processes with persistences
`ρ_a, ρ_z < 1`, and let the driving force be `r̂^n_t − v_t = c_a a_t + c_z z_t` (by
`drivingForce_eq`, `c_a = −ψ_ya(σ(1−ρ_a) + φ_y)`, `c_z = 1 − ρ_z`). Under (14), a triple with
bounded adapted `ỹ`, `π` is an equilibrium iff
`ỹ_t = ψ_y(ρ_a) c_a a_t + ψ_y(ρ_z) c_z z_t`, `π_t = ψ_π(ρ_a) c_a a_t + ψ_π(ρ_z) c_z z_t` and
`i_t` is given by (19); this triple is bounded and adapted, so it is the unique bounded
equilibrium. -/
theorem equilibrium_iff_msv {β σ κ ρ φπ φy ρa ρz ca cz : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρa : ρa < 1) (hρz : ρz < 1)
    (h14 : 0 < κ * (φπ - 1) + (1 - β) * φy) {rn yhatn a z : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (hz : 𝔼.IsAR1 ρz z) (hab : BoundedProc a) (hzb : BoundedProc z)
    (hu : ∀ t, drivingForce ρ rn (pseudoShock φy yhatn) t = ca • a t + cz • z t)
    {ygap infl i : ℕ → Ω → ℝ} (hya : 𝔼.Adapted ygap) (hpa : 𝔼.Adapted infl)
    (hyb : BoundedProc ygap) (hpb : BoundedProc infl) :
    Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn ygap infl i ↔
      ygap = (fun t => (msvPsiY β σ κ φπ φy ρa * ca) • a t +
        (msvPsiY β σ κ φπ φy ρz * cz) • z t) ∧
      infl = (fun t => (msvPsiPi β σ κ φπ φy ρa * ca) • a t +
        (msvPsiPi β σ κ φπ φy ρz * cz) • z t) ∧
      i = fun t => (fun _ => ρ) + φπ • infl t + φy • (ygap t + yhatn t) := by
  have hS : σ + φy + κ * φπ ≠ 0 := by positivity
  have hDa := (msvDen_pos hσ hκ hβ0 hβ1 hφy hρa h14).ne'
  have hDz := (msvDen_pos hσ hκ hβ0 hβ1 hφy hρz h14).ne'
  have hU : drivingForce ρ rn (pseudoShock φy yhatn) = fun t => ca • a t + cz • z t :=
    funext hu
  have hmsv := structural_add 𝔼 (msv_structural 𝔼 hDa (isAR1_smul 𝔼 ha ca))
    (msv_structural 𝔼 hDz (isAR1_smul 𝔼 hz cz))
  have hY : (fun t => msvPsiY β σ κ φπ φy ρa • (ca • a t) + msvPsiY β σ κ φπ φy ρz • (cz • z t))
      = fun t => (msvPsiY β σ κ φπ φy ρa * ca) • a t + (msvPsiY β σ κ φπ φy ρz * cz) • z t := by
    simp only [smul_smul]
  have hP : (fun t => msvPsiPi β σ κ φπ φy ρa • (ca • a t) +
      msvPsiPi β σ κ φπ φy ρz • (cz • z t))
      = fun t => (msvPsiPi β σ κ φπ φy ρa * ca) • a t +
        (msvPsiPi β σ κ φπ φy ρz * cz) • z t := by
    simp only [smul_smul]
  rw [hY, hP] at hmsv
  constructor
  · intro he
    have hgap := (rule19_iff_rule20 (fun _ => rfl)).mp he.2.2
    have hs := (nk_iff_structural 𝔼 hσ.ne' hgap).mp ⟨he.1, he.2.1⟩
    rw [hU] at hs
    have heq := 𝔼.system_unique ((schurStable_AT_iff hσ hκ hβ0 hβ1 hφπ hφy).mpr h14)
      ((structural_iff_solves 𝔼 hS _ _ _).mp hs)
      ((structural_iff_solves 𝔼 hS _ _ _).mp hmsv)
      (adaptedVec_stack 𝔼 hya hpa)
      (adaptedVec_stack 𝔼 (adapted_lin 𝔼 ha.1 hz.1 _ _) (adapted_lin 𝔼 ha.1 hz.1 _ _))
      (boundedVec_stack hyb hpb)
      (boundedVec_stack (boundedProc_lin hab hzb _ _) (boundedProc_lin hab hzb _ _))
    refine ⟨funext fun t => by simpa [stack] using congrFun (congrFun heq t) 0,
      funext fun t => by simpa [stack] using congrFun (congrFun heq t) 1, funext he.2.2⟩
  · rintro ⟨h1, h2, h3⟩
    have hrule : TaylorRule ρ φπ φy i infl (fun t => ygap t + yhatn t) := fun t => by rw [h3]
    have hgap := (rule19_iff_rule20 (fun _ => rfl)).mp hrule
    have hs : Structural 𝔼 β σ κ φπ φy (drivingForce ρ rn (pseudoShock φy yhatn)) ygap infl := by
      rw [hU, h1, h2]
      exact hmsv
    have hnk := (nk_iff_structural 𝔼 hσ.ne' hgap).mpr hs
    exact ⟨hnk.1, hnk.2, hrule⟩

/-- Galí (2015), p. 113 (**single-shock version**, as used for each half of Table 4.1): with
one bounded AR(1) shock `s` and driving force `r̂^n_t − v_t = c s_t`, under (14) the unique
bounded equilibrium is `ỹ_t = ψ_y c s_t`, `π_t = ψ_π c s_t`. -/
theorem equilibrium_iff_msv_single {β σ κ ρ φπ φy ρs c : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρs : ρs < 1)
    (h14 : 0 < κ * (φπ - 1) + (1 - β) * φy) {rn yhatn s : ℕ → Ω → ℝ}
    (hs : 𝔼.IsAR1 ρs s) (hsb : BoundedProc s)
    (hu : ∀ t, drivingForce ρ rn (pseudoShock φy yhatn) t = c • s t)
    {ygap infl i : ℕ → Ω → ℝ} (hya : 𝔼.Adapted ygap) (hpa : 𝔼.Adapted infl)
    (hyb : BoundedProc ygap) (hpb : BoundedProc infl) :
    Equilibrium 𝔼 β σ κ ρ φπ φy rn yhatn ygap infl i ↔
      ygap = (fun t => (msvPsiY β σ κ φπ φy ρs * c) • s t) ∧
      infl = (fun t => (msvPsiPi β σ κ φπ φy ρs * c) • s t) ∧
      i = fun t => (fun _ => ρ) + φπ • infl t + φy • (ygap t + yhatn t) := by
  have h0 : 𝔼.IsAR1 0 (fun _ => (0 : Ω → ℝ)) :=
    ⟨fun t => by simp, fun t => by simp⟩
  have h0b : BoundedProc (fun _ => (0 : Ω → ℝ)) := ⟨0, fun _ _ => by simp⟩
  have h := equilibrium_iff_msv 𝔼 (ca := c) (cz := 0) (i := i) hσ hκ hβ0 hβ1 hφπ hφy hρs
    (by norm_num) h14 hs h0 hsb h0b (fun t => by rw [hu t]; simp) hya hpa hyb hpb
  simpa using h

/-! ### Losses as quadratic forms in the MSV coefficients -/

/-- Galí (2015), p. 111 and Table 4.1, p. 113: the average loss `L` implied by a single AR(1)
shock with stationary variance `va` and loading `c` on the driving force, under rule (19):
`var(ỹ) = (ψ_y c)² va`, `var(π) = (ψ_π c)² va`, with `κ = λ(σ + (φ+α)/(1−α))`. -/
noncomputable def msvLoss (β θ σ φ α ε φπ φy ρu c va : ℝ) : ℝ :=
  avgLoss β θ σ φ α ε ((msvPsiY β σ (kappaNK β θ σ φ α ε) φπ φy ρu * c) ^ 2 * va)
    ((msvPsiPi β σ (kappaNK β θ σ φ α ε) φπ φy ρu * c) ^ 2 * va)

/-- Galí (2015), p. 111 (**the loss as a quadratic form in the MSV coefficients times the
shock variance**): `L = ½[(σ + (φ+α)/(1−α)) ψ_y² + (ε/λ) ψ_π²] c² var(s)`. -/
theorem msvLoss_eq (β θ σ φ α ε φπ φy ρu c va : ℝ) :
    msvLoss β θ σ φ α ε φπ φy ρu c va
      = (gapCoeff σ φ α * msvPsiY β σ (kappaNK β θ σ φ α ε) φπ φy ρu ^ 2 +
          ε / lambdaNK β θ α ε * msvPsiPi β σ (kappaNK β θ σ φ α ε) φπ φy ρu ^ 2) / 2 *
        c ^ 2 * va := by
  unfold msvLoss avgLoss
  ring

omit 𝔼 in
/-- Galí (2015), p. 113: an abstract second-moment functional `Var` (homogeneous of degree
two, `Var(k X) = k² Var X`) applied to the MSV solution gives
`Var(ỹ_t) = (ψ_y c)² Var(s_t)`, `Var(π_t) = (ψ_π c)² Var(s_t)`, and the period loss
`L = msvLoss(…, Var(s_t))`. -/
theorem msv_moments (Var : (Ω → ℝ) → ℝ) (hVar : ∀ (k : ℝ) (X : Ω → ℝ), Var (k • X) = k ^ 2 * Var X)
    {β θ σ φ α ε φπ φy ρs c : ℝ} {s ygap infl : ℕ → Ω → ℝ}
    (hy : ygap = fun t => (msvPsiY β σ (kappaNK β θ σ φ α ε) φπ φy ρs * c) • s t)
    (hp : infl = fun t => (msvPsiPi β σ (kappaNK β θ σ φ α ε) φπ φy ρs * c) • s t) (t : ℕ) :
    Var (ygap t) = (msvPsiY β σ (kappaNK β θ σ φ α ε) φπ φy ρs * c) ^ 2 * Var (s t) ∧
      Var (infl t) = (msvPsiPi β σ (kappaNK β θ σ φ α ε) φπ φy ρs * c) ^ 2 * Var (s t) ∧
      avgLoss β θ σ φ α ε (Var (ygap t)) (Var (infl t))
        = msvLoss β θ σ φ α ε φπ φy ρs c (Var (s t)) := by
  subst hy hp
  refine ⟨hVar _ _, hVar _ _, ?_⟩
  simp only [hVar]
  rfl

/-- Galí (2015), pp. 111–113 (**the loss of the unique equilibrium**): under (14), with one
bounded AR(1) shock `s` loading `c` on the driving force and `κ = λ(σ + (φ+α)/(1−α))`, every
bounded equilibrium has, for any second-moment functional `Var`,
`L_t = ½[(σ + (φ+α)/(1−α)) Var(ỹ_t) + (ε/λ) Var(π_t)] = msvLoss(…, Var(s_t))`. -/
theorem equilibrium_loss (Var : (Ω → ℝ) → ℝ)
    (hVar : ∀ (k : ℝ) (X : Ω → ℝ), Var (k • X) = k ^ 2 * Var X)
    {β θ σ φ α ε ρ φπ φy ρs c : ℝ} (hσ : 0 < σ) (hκ : 0 < kappaNK β θ σ φ α ε)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) (hρs : ρs < 1)
    (h14 : 0 < kappaNK β θ σ φ α ε * (φπ - 1) + (1 - β) * φy) {rn yhatn s : ℕ → Ω → ℝ}
    (hs : 𝔼.IsAR1 ρs s) (hsb : BoundedProc s)
    (hu : ∀ t, drivingForce ρ rn (pseudoShock φy yhatn) t = c • s t)
    {ygap infl i : ℕ → Ω → ℝ} (hya : 𝔼.Adapted ygap) (hpa : 𝔼.Adapted infl)
    (hyb : BoundedProc ygap) (hpb : BoundedProc infl)
    (he : Equilibrium 𝔼 β σ (kappaNK β θ σ φ α ε) ρ φπ φy rn yhatn ygap infl i) (t : ℕ) :
    avgLoss β θ σ φ α ε (Var (ygap t)) (Var (infl t))
      = msvLoss β θ σ φ α ε φπ φy ρs c (Var (s t)) := by
  obtain ⟨h1, h2, -⟩ := (equilibrium_iff_msv_single 𝔼 hσ hκ hβ0 hβ1 hφπ hφy hρs h14 hs hsb hu
    hya hpa hyb hpb).mp he
  exact (msv_moments Var hVar h1 h2 t).2.2

omit 𝔼 in
/-- Galí (2015), p. 113: Mathlib's variance on any probability space is such a second-moment
functional, `var(k X) = k² var X`. -/
theorem variance_isSecondMoment [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (k : ℝ)
    (X : Ω → ℝ) : ProbabilityTheory.variance (k • X) μ = k ^ 2 * ProbabilityTheory.variance X μ :=
  ProbabilityTheory.variance_smul k X μ

/-- Galí (2015), p. 113 (innovations with standard deviation `σ_e`): the stationary variance of
an AR(1) process, `σ_e²/(1 − ρ²)`. -/
noncomputable def ar1Var (σe ρ : ℝ) : ℝ := σe ^ 2 / (1 - ρ ^ 2)

/-- Galí (2015), p. 113: the stationary AR(1) variance is the unique fixed point of
`V = ρ² V + σ_e²` (for `|ρ| < 1`). -/
theorem ar1Var_fixed_point {σe ρ V : ℝ} (hρ : |ρ| < 1) :
    V = ρ ^ 2 * V + σe ^ 2 ↔ V = ar1Var σe ρ := by
  have h : ρ ^ 2 < 1 := by
    have := sq_abs ρ
    nlinarith [abs_nonneg ρ]
  have h1 : 1 - ρ ^ 2 ≠ 0 := by linarith
  unfold ar1Var
  constructor
  · intro hV
    field_simp
    linarith
  · intro hV
    rw [hV]
    field_simp
    ring

/-- Galí (2015), p. 113: the MA(∞) form `s_t = ∑ ρᵏ e_{t−k}` with uncorrelated innovations of
variance `σ_e²` has variance `∑ ρ²ᵏ σ_e² = σ_e²/(1 − ρ²)`. -/
theorem ar1Var_hasSum {σe ρ : ℝ} (hρ : |ρ| < 1) :
    HasSum (fun k : ℕ => (ρ ^ k) ^ 2 * σe ^ 2) (ar1Var σe ρ) := by
  have h0 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  have h : ρ ^ 2 < 1 := by
    have := sq_abs ρ
    nlinarith [abs_nonneg ρ]
  have hg := (hasSum_geometric_of_lt_one h0 h).mul_right (σe ^ 2)
  unfold ar1Var
  convert hg using 1
  · funext k
    ring
  · rw [div_eq_inv_mul]

/-- Galí (2015), fn. 10, p. 114 (**losses vanish as `φ_π → ∞`**): with `κ > 0`, `βρ ≠ 1` held
fixed, the variances `(ψ_y c)² va`, `(ψ_π c)² va` of the output gap and of inflation, and
hence the loss `L`, tend to `0` as `φ_π → +∞`. -/
theorem msvLoss_tendsto_zero {β θ σ φ α ε φy ρu c va : ℝ} (hκ : 0 < kappaNK β θ σ φ α ε) :
    Tendsto (fun φπ => (msvPsiY β σ (kappaNK β θ σ φ α ε) φπ φy ρu * c) ^ 2 * va) atTop
        (𝓝 0) ∧
      Tendsto (fun φπ => (msvPsiPi β σ (kappaNK β θ σ φ α ε) φπ φy ρu * c) ^ 2 * va) atTop
        (𝓝 0) ∧
      Tendsto (fun φπ => msvLoss β θ σ φ α ε φπ φy ρu c va) atTop (𝓝 0) := by
  set κ := kappaNK β θ σ φ α ε
  have hD : Tendsto (fun φπ => msvDen β σ κ φπ φy ρu) atTop atTop := by
    have : (fun φπ => msvDen β σ κ φπ φy ρu)
        = fun φπ => κ * φπ + ((1 - β * ρu) * (σ * (1 - ρu) + φy) - κ * ρu) := by
      funext φπ
      unfold msvDen
      ring
    rw [this]
    exact tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop hκ)
  have hL : Tendsto (fun φπ => msvLambda β σ κ φπ φy ρu) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.comp hD
    simpa [msvLambda, one_div, Function.comp_def] using this
  have hY : Tendsto (fun φπ => msvPsiY β σ κ φπ φy ρu) atTop (𝓝 0) := by
    have := hL.const_mul (1 - β * ρu)
    simpa [msvPsiY] using this
  have hP : Tendsto (fun φπ => msvPsiPi β σ κ φπ φy ρu) atTop (𝓝 0) := by
    have := hL.const_mul κ
    simpa [msvPsiPi] using this
  have hY2 : Tendsto (fun φπ => (msvPsiY β σ κ φπ φy ρu * c) ^ 2 * va) atTop (𝓝 0) := by
    have := ((hY.mul_const c).pow 2).mul_const va
    simpa using this
  have hP2 : Tendsto (fun φπ => (msvPsiPi β σ κ φπ φy ρu * c) ^ 2 * va) atTop (𝓝 0) := by
    have := ((hP.mul_const c).pow 2).mul_const va
    simpa using this
  refine ⟨hY2, hP2, ?_⟩
  have := ((hY2.const_mul (gapCoeff σ φ α)).add
    (hP2.const_mul (ε / lambdaNK β θ α ε))).div_const 2
  simpa [msvLoss, avgLoss] using this

/-! ### §4.4.2: a constant money growth rule with money-demand shocks -/

omit 𝔼 in
/-- Galí (2015), ch. 3, eq. (31), p. 74 (restated from the Chapter 3 project), here with
real balances `l̂_t = L (t + 1)`: `l̂_t = ỹ_t − η î_t + ŷ^n_t`. -/
def MoneyDemandGap (η : ℝ) (ygap i yn L : ℕ → Ω → ℝ) : Prop :=
  ∀ t, L (t + 1) = ygap t - η • i t + yn t

/-- Galí (2015), ch. 3, eq. (32), p. 74 (restated from the Chapter 3 project): the DIS with
the interest rate eliminated. -/
def Eq32 (σ η : ℝ) (ygap infl L rn yn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (1 + σ * η) • ygap t = (σ * η) • 𝔼.E t (ygap (t + 1)) + L (t + 1) +
    η • 𝔼.E t (infl (t + 1)) + η • rn t - yn t

omit 𝔼 in
/-- Galí (2015), ch. 3, eq. (33), p. 74 (restated from the Chapter 3 project):
`l̂_{t−1} = l̂_t + π_t − Δm_t`. -/
def RealBalanceId (infl L dm : ℕ → Ω → ℝ) : Prop :=
  ∀ t, L t = L (t + 1) + infl t - dm t

/-- Galí (2015), ch. 3, p. 75 (restated from the Chapter 3 project): `l̂_{t−1}` is
predetermined. -/
def Predetermined (L : ℕ → Ω → ℝ) : Prop :=
  ∀ t, 𝔼.E t (L (t + 1)) = L (t + 1)

/-- Galí (2015), ch. 3, eq. (32), p. 74 (restated from the Chapter 3 project): given money
demand (31), the DIS is equivalent to (32) (for `σ ≠ 0`, `η ≠ 0`). -/
theorem dis_iff_eq32 {σ η : ℝ} (hσ : σ ≠ 0) (hη : η ≠ 0) {ygap infl i rn yn L : ℕ → Ω → ℝ}
    (hMD : MoneyDemandGap η ygap i yn L) :
    DIS 𝔼 σ ygap i infl rn ↔ Eq32 𝔼 σ η ygap infl L rn yn := by
  constructor
  · intro h t
    funext ω
    have h1 := congrFun (h t) ω
    have h2 := congrFun (hMD t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    rw [h2]
    have h1' : σ * ygap t ω = -(i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) +
        σ * 𝔼.E t (ygap (t + 1)) ω := by
      rw [h1]; field_simp
    linear_combination η * h1'
  · intro h t
    funext ω
    have h1 := congrFun (h t) ω
    have h2 := congrFun (hMD t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    rw [h2] at h1
    have h3 : σ * ygap t ω = -(i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) +
        σ * 𝔼.E t (ygap (t + 1)) ω := by
      have h4 : η * (σ * ygap t ω - (-(i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) +
          σ * 𝔼.E t (ygap (t + 1)) ω)) = 0 := by linear_combination h1
      rcases mul_eq_zero.mp h4 with h5 | h5
      · exact absurd h5 hη
      · linarith
    field_simp
    linear_combination h3

/-- Galí (2015), ch. 3, eq. (34), p. 75: the matrix `A_{M,0}`. -/
def AM0 (σ η κ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1 + σ * η, 0, 0; -κ, 1, 0; 0, -1, 1]

/-- Galí (2015), ch. 3, eq. (34), p. 75: the matrix `A_{M,1}`. -/
def AM1 (σ η β : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![σ * η, η, 1; 0, β, 0; 0, 0, 1]

/-- Galí (2015), ch. 3, eq. (34), p. 75: the matrix `B_M`. -/
def BM (η : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![η, -1, 0; 0, 0, 0; 0, 0, -1]

omit 𝔼 in
/-- Galí (2015), ch. 3, eq. (34), p. 75: the state `(ỹ_t, π_t, l̂_{t−1})`. -/
def stateVec (ygap infl L : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  ![ygap t ω, infl t ω, L t ω]

/-- Galí (2015), ch. 3, eq. (34), p. 75: the forecast `(E_t ỹ_{t+1}, E_t π_{t+1}, E_t l̂_t)`. -/
def expVec (ygap infl L : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  ![𝔼.E t (ygap (t + 1)) ω, 𝔼.E t (infl (t + 1)) ω, 𝔼.E t (L (t + 1)) ω]

omit 𝔼 in
/-- Galí (2015), ch. 3, eq. (34), p. 75: the shock vector `(r̂^n_t, ŷ^n_t, Δm_t)`. -/
def shockVec (rn yn dm : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  ![rn t ω, yn t ω, dm t ω]

/-- Galí (2015), ch. 3, eq. (34), p. 75: `A_{M,0} x_t = A_{M,1} E_t x_{t+1} + B_M s_t`. -/
def System34 (σ η β κ : ℝ) (ygap infl L rn yn dm : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, (AM0 σ η κ).mulVec (stateVec ygap infl L t ω) =
    (AM1 σ η β).mulVec (expVec 𝔼 ygap infl L t ω) + (BM η).mulVec (shockVec rn yn dm t ω)

/-- Galí (2015), ch. 3, eq. (34), p. 75 (restated from the Chapter 3 project): with `l̂`
predetermined, (34) is equivalent to (32), the NKPC and (33). -/
theorem system34_iff {σ η β κ : ℝ} {ygap infl L rn yn dm : ℕ → Ω → ℝ}
    (hL : Predetermined 𝔼 L) :
    System34 𝔼 σ η β κ ygap infl L rn yn dm ↔
      Eq32 𝔼 σ η ygap infl L rn yn ∧ NKPC 𝔼 β κ ygap infl ∧ RealBalanceId infl L dm := by
  constructor
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_,
      fun t => funext fun ω => ?_⟩
    · have h0 := congrFun (h t ω) 0
      have hLω := congrFun (hL t) ω
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec] at h0 ⊢
      linarith
    · have h1 := congrFun (h t ω) 1
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec] at h1 ⊢
      linarith
    · have h2 := congrFun (h t ω) 2
      have hLω := congrFun (hL t) ω
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec] at h2 ⊢
      linarith
  · rintro ⟨h32, h22, h33⟩ t ω
    have a := congrFun (h32 t) ω
    have b := congrFun (h22 t) ω
    have c := congrFun (h33 t) ω
    have hLω := congrFun (hL t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b c
    funext j
    fin_cases j <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, AM0, AM1, BM, stateVec, expVec,
        shockVec] <;> linarith

omit 𝔼 in
/-- Galí (2015), p. 114: money demand with a money-demand shock, in deviations,
`l̂_t = ỹ_t + ŷ^n_t − η î_t − ζ_t`, with `l̂_t = L (t + 1)` and `ζ_t = ζ (t + 1)` (so `ζ 0` is
`ζ_{−1}`). -/
def MoneyDemandShock (η : ℝ) (ygap yn i zeta L : ℕ → Ω → ℝ) : Prop :=
  ∀ t, L (t + 1) = ygap t + yn t - η • i t - zeta (t + 1)

omit 𝔼 in
/-- Galí (2015), p. 114: the constant money growth rule `Δm_t = 0` together with
`l̂_{t−1} = l̂_t + π_t − Δm_t`: `l̂_{t−1} = l̂_t + π_t`. -/
def ConstantMoney (infl L : ℕ → Ω → ℝ) : Prop := ∀ t, L t = L (t + 1) + infl t

omit 𝔼 in
/-- Galí (2015), p. 114: with `l_t = m_t − p_t`, `π_t = p_t − p_{t−1}` and a constant money
stock `m_t = m̄` (the rule `m_t = 0`), real balances satisfy `l̂_{t−1} = l̂_t + π_t` at every
date `t ≥ 1`. -/
theorem constantMoney_of_levels {mbar : ℝ} {p L infl : ℕ → Ω → ℝ}
    (hL : ∀ t, L (t + 1) = (fun _ => mbar) - p t) (hp : ∀ t, infl (t + 1) = p (t + 1) - p t)
    (t : ℕ) : L (t + 1) = L (t + 1 + 1) + infl (t + 1) := by
  rw [hL, hL, hp]
  abel

omit 𝔼 in
/-- Galí (2015), p. 115: `l^+_t = l_t + ζ_t`, i.e. `L⁺ t = L t + ζ t` (both shifted). -/
def Lplus (L zeta : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => L t + zeta t

omit 𝔼 in
/-- Galí (2015), p. 115: `Δζ_t = ζ_t − ζ_{t−1}`, i.e. `ζ (t + 1) − ζ t`. -/
def dZeta (zeta : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => zeta (t + 1) - zeta t

omit 𝔼 in
/-- Galí (2015), p. 115: money demand with the shock is ch. 3's (31) for adjusted real
balances, `l̂^+_t = ỹ_t − η î_t + ŷ^n_t` (equivalently `î_t = (ỹ_t + ŷ^n_t − l̂^+_t)/η`). -/
theorem moneyDemand_iff_plus {η : ℝ} {ygap yn i zeta L : ℕ → Ω → ℝ} :
    MoneyDemandShock η ygap yn i zeta L ↔ MoneyDemandGap η ygap i yn (Lplus L zeta) := by
  constructor
  · intro h t
    simp only [Lplus]
    rw [h t]
    abel
  · intro h t
    have := h t
    simp only [Lplus] at this
    rw [eq_sub_of_add_eq this]
    abel

omit 𝔼 in
/-- Galí (2015), p. 115: under the constant-money rule, adjusted real balances obey
`l̂^+_{t−1} = l̂^+_t + π_t − Δζ_t`, ch. 3's (33) with `Δm` replaced by `Δζ`. -/
theorem constantMoney_iff_plus {infl L zeta : ℕ → Ω → ℝ} :
    ConstantMoney infl L ↔ RealBalanceId infl (Lplus L zeta) (dZeta zeta) := by
  constructor
  · intro h t
    simp only [Lplus, dZeta]
    rw [h t]
    abel
  · intro h t
    have := h t
    simp only [Lplus, dZeta] at this
    have h2 := congrArg (fun x => x - zeta t) this
    simp only [add_sub_cancel_right] at h2
    rw [h2]
    abel

/-- Galí (2015), p. 115: if `l̂_{t−1}` is predetermined and the money-demand shock is known
when it occurs, adjusted real balances `l̂^+_{t−1}` are predetermined. -/
theorem predetermined_plus {L zeta : ℕ → Ω → ℝ} (hL : Predetermined 𝔼 L)
    (hz : ∀ t, 𝔼.E t (zeta (t + 1)) = zeta (t + 1)) : Predetermined 𝔼 (Lplus L zeta) := by
  intro t
  simp only [Lplus, map_add, hL t, hz t]

/-- Galí (2015), §4.4.2, p. 115 (**the constant money growth rule is ch. 3's system (34)**):
with money demand `l̂_t = ỹ_t + ŷ^n_t − η î_t − ζ_t`, the rule `Δm_t = 0` and predetermined
adjusted real balances, the NKPC, the DIS and the money-market condition hold iff
`A_{M,0}(ỹ_t, π_t, l̂^+_{t−1}) = A_{M,1}(E_t ỹ_{t+1}, E_t π_{t+1}, l̂^+_t)`
`+ B_M(r̂^n_t, ŷ^n_t, Δζ_t)` with the same matrices as (34): money-demand shocks enter exactly
as money-supply shocks. -/
theorem constantMoney_iff_system34 {σ η β κ : ℝ} (hσ : σ ≠ 0) (hη : η ≠ 0)
    {ygap infl i L zeta rn yn : ℕ → Ω → ℝ} (hMD : MoneyDemandShock η ygap yn i zeta L)
    (hL : Predetermined 𝔼 (Lplus L zeta)) :
    (NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl rn ∧ ConstantMoney infl L) ↔
      System34 𝔼 σ η β κ ygap infl (Lplus L zeta) rn yn (dZeta zeta) := by
  rw [system34_iff 𝔼 hL, ← dis_iff_eq32 𝔼 hσ hη (moneyDemand_iff_plus.mp hMD),
    ← constantMoney_iff_plus]
  tauto

/-! ### Table 4.1 from the closed forms -/

/-- Galí (2015), p. 112: the loading of technology in the driving force,
`c_a = −ψ_ya(σ(1 − ρ_a) + φ_y)`. -/
noncomputable def techLoad (σ φy ρa ψya : ℝ) : ℝ := -(ψya * (σ * (1 - ρa) + φy))

/-- Galí (2015), p. 112: the loading of the preference shock in the driving force,
`c_z = 1 − ρ_z`. -/
def demandLoad (ρz : ℝ) : ℝ := 1 - ρz

/-- Galí (2015), Table 4.1, p. 113: the baseline calibration of ch. 3 (`β = 0.99`, `σ = 1`,
`φ = 5`, `α = 1/4`, `ε = 9`, `θ = 3/4`), innovations with a standard deviation of one
percent: the standard deviation (in percent) of the output gap for a shock of persistence
`ρ` with loading `c`, `|ψ_y c|/√(1 − ρ²)`. -/
noncomputable def baseSdGap (φπ φy ρ c : ℝ) : ℝ :=
  Real.sqrt ((msvPsiY 0.99 1 (kappaNK 0.99 0.75 1 5 0.25 9) φπ φy ρ * c) ^ 2 * ar1Var 1 ρ)

/-- Galí (2015), Table 4.1, p. 113: the standard deviation (in percent) of quarterly
inflation, `|ψ_π c|/√(1 − ρ²)`, at the baseline. -/
noncomputable def baseSdInfl (φπ φy ρ c : ℝ) : ℝ :=
  Real.sqrt ((msvPsiPi 0.99 1 (kappaNK 0.99 0.75 1 5 0.25 9) φπ φy ρ * c) ^ 2 * ar1Var 1 ρ)

/-- Galí (2015), Table 4.1, p. 113: the standard deviation (in percent) of output under a
technology shock, `ŷ_t = ỹ_t + ψ_ya a_t = (ψ_y c_a + ψ_ya) a_t`, at the baseline. (Under the
preference shock `ŷ^n = 0`, so `σ(y) = σ(ỹ)`.) -/
noncomputable def baseSdOutputTech (φπ φy : ℝ) : ℝ :=
  Real.sqrt ((msvPsiY 0.99 1 (kappaNK 0.99 0.75 1 5 0.25 9) φπ φy 0.9 *
    techLoad 1 φy 0.9 (psiYA 1 5 0.25) + psiYA 1 5 0.25) ^ 2 * ar1Var 1 0.9)

/-- Galí (2015), Table 4.1, p. 113: the welfare loss `L` in percent of steady-state
consumption at the baseline (variances in squared percentage points, hence the `1/100`). -/
noncomputable def baseLoss (φπ φy ρ c : ℝ) : ℝ :=
  msvLoss 0.99 0.75 1 5 0.25 9 φπ φy ρ c (ar1Var 1 ρ) / 100

/-- Galí (2015), p. 67 (used for Table 4.1): `κ = 103/600` at the baseline. -/
theorem kappa_base : kappaNK 0.99 0.75 1 5 0.25 9 = 103 / 600 := by
  unfold kappaNK lambdaNK bigTheta gapCoeff
  norm_num

/-- Galí (2015), p. 67: `λ = 103/4800` at the baseline. -/
theorem lambda_base : lambdaNK 0.99 0.75 0.25 9 = 103 / 4800 := by
  unfold lambdaNK bigTheta
  norm_num

/-- Galí (2015), p. 111: the gap coefficient `σ + (φ+α)/(1−α) = 8` at the baseline. -/
theorem gapCoeff_base : gapCoeff 1 5 0.25 = 8 := by
  unfold gapCoeff
  norm_num

/-- Galí (2015), p. 113 (ch. 3 fn. 12): `ψ_ya = 1` at the baseline. -/
theorem psiYA_base : psiYA 1 5 0.25 = 1 := by
  unfold psiYA
  norm_num

/-- Bounds on a square root from bounds on its argument (for the printed standard
deviations of Galí 2015, Tables 4.1). -/
theorem sqrt_bounds {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (h1 : a ^ 2 ≤ x) (h2 : x < b ^ 2) :
    a ≤ Real.sqrt x ∧ Real.sqrt x < b :=
  ⟨(Real.le_sqrt ha ((sq_nonneg a).trans h1)).2 h1, (Real.sqrt_lt' hb).2 h2⟩

/-- Galí (2015), Table 4.1, p. 113, technology, Taylor's rule `φ_π = 1.5`, `φ_y = 0.125`
(the book truncates to two decimals): `σ(y) ∈ [1.85, 1.86)`, `σ(ỹ) ∈ [0.44, 0.45)`,
`σ(π) ∈ [0.69, 0.70)`, `L ∈ [1.02, 1.03)`. -/
theorem table41_tech_1 :
    (1.85 ≤ baseSdOutputTech 1.5 0.125 ∧ baseSdOutputTech 1.5 0.125 < 1.86) ∧
    (0.44 ≤ baseSdGap 1.5 0.125 0.9 (techLoad 1 0.125 0.9 (psiYA 1 5 0.25)) ∧
      baseSdGap 1.5 0.125 0.9 (techLoad 1 0.125 0.9 (psiYA 1 5 0.25)) < 0.45) ∧
    (0.69 ≤ baseSdInfl 1.5 0.125 0.9 (techLoad 1 0.125 0.9 (psiYA 1 5 0.25)) ∧
      baseSdInfl 1.5 0.125 0.9 (techLoad 1 0.125 0.9 (psiYA 1 5 0.25)) < 0.70) ∧
    (1.02 ≤ baseLoss 1.5 0.125 0.9 (techLoad 1 0.125 0.9 (psiYA 1 5 0.25)) ∧
      baseLoss 1.5 0.125 0.9 (techLoad 1 0.125 0.9 (psiYA 1 5 0.25)) < 1.03) := by
  simp only [baseSdOutputTech, baseSdGap, baseSdInfl, baseLoss, msvLoss, avgLoss, kappa_base,
    lambda_base, gapCoeff_base, psiYA_base, msvPsiY, msvPsiPi, msvLambda, msvDen, ar1Var,
    techLoad]
  refine ⟨sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ⟨by norm_num, by norm_num⟩⟩

/-- Galí (2015), Table 4.1, p. 113, technology, `φ_π = 1.5`, `φ_y = 0` (truncated to the
printed digits): `σ(y) ∈ [2.07, 2.08)`, `σ(ỹ) ∈ [0.21, 0.22)`, `σ(π) ∈ [0.34, 0.35)`,
`L ∈ [0.25, 0.26)`. -/
theorem table41_tech_2 :
    (2.07 ≤ baseSdOutputTech 1.5 0 ∧ baseSdOutputTech 1.5 0 < 2.08) ∧
    (0.21 ≤ baseSdGap 1.5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) ∧
      baseSdGap 1.5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) < 0.22) ∧
    (0.34 ≤ baseSdInfl 1.5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) ∧
      baseSdInfl 1.5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) < 0.35) ∧
    (0.25 ≤ baseLoss 1.5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) ∧
      baseLoss 1.5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) < 0.26) := by
  simp only [baseSdOutputTech, baseSdGap, baseSdInfl, baseLoss, msvLoss, avgLoss, kappa_base,
    lambda_base, gapCoeff_base, psiYA_base, msvPsiY, msvPsiPi, msvLambda, msvDen, ar1Var,
    techLoad]
  refine ⟨sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ⟨by norm_num, by norm_num⟩⟩

/-- Galí (2015), Table 4.1, p. 113, technology, `φ_π = 5`, `φ_y = 0` (truncated to the
printed digits): `σ(y) ∈ [2.25, 2.26)`, `σ(ỹ) ∈ [0.03, 0.04)`, `σ(π) ∈ [0.05, 0.06)`,
`L ∈ [0.006, 0.007)`. -/
theorem table41_tech_3 :
    (2.25 ≤ baseSdOutputTech 5 0 ∧ baseSdOutputTech 5 0 < 2.26) ∧
    (0.03 ≤ baseSdGap 5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) ∧
      baseSdGap 5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) < 0.04) ∧
    (0.05 ≤ baseSdInfl 5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) ∧
      baseSdInfl 5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) < 0.06) ∧
    (0.006 ≤ baseLoss 5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) ∧
      baseLoss 5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) < 0.007) := by
  simp only [baseSdOutputTech, baseSdGap, baseSdInfl, baseLoss, msvLoss, avgLoss, kappa_base,
    lambda_base, gapCoeff_base, psiYA_base, msvPsiY, msvPsiPi, msvLambda, msvDen, ar1Var,
    techLoad]
  refine ⟨sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ⟨by norm_num, by norm_num⟩⟩

/-- Galí (2015), Table 4.1, p. 113, technology, `φ_π = 1.5`, `φ_y = 1` (truncated to the
printed digits): `σ(y) ∈ [1.06, 1.07)`, `σ(ỹ) ∈ [1.23, 1.24)`, `σ(π) ∈ [1.94, 1.95)`,
`L ∈ [7.98, 7.99)`. -/
theorem table41_tech_4 :
    (1.06 ≤ baseSdOutputTech 1.5 1 ∧ baseSdOutputTech 1.5 1 < 1.07) ∧
    (1.23 ≤ baseSdGap 1.5 1 0.9 (techLoad 1 1 0.9 (psiYA 1 5 0.25)) ∧
      baseSdGap 1.5 1 0.9 (techLoad 1 1 0.9 (psiYA 1 5 0.25)) < 1.24) ∧
    (1.94 ≤ baseSdInfl 1.5 1 0.9 (techLoad 1 1 0.9 (psiYA 1 5 0.25)) ∧
      baseSdInfl 1.5 1 0.9 (techLoad 1 1 0.9 (psiYA 1 5 0.25)) < 1.95) ∧
    (7.98 ≤ baseLoss 1.5 1 0.9 (techLoad 1 1 0.9 (psiYA 1 5 0.25)) ∧
      baseLoss 1.5 1 0.9 (techLoad 1 1 0.9 (psiYA 1 5 0.25)) < 7.99) := by
  simp only [baseSdOutputTech, baseSdGap, baseSdInfl, baseLoss, msvLoss, avgLoss, kappa_base,
    lambda_base, gapCoeff_base, psiYA_base, msvPsiY, msvPsiPi, msvLambda, msvDen, ar1Var,
    techLoad]
  refine ⟨sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ⟨by norm_num, by norm_num⟩⟩

/-- Galí (2015), Table 4.1, p. 113, demand (preference) shock, `φ_π = 1.5`, `φ_y = 0.125`
(truncated to the printed digits; `σ(y) = σ(ỹ)` since `ŷ^n = 0`):
`σ(ỹ) ∈ [0.59, 0.60)`, `σ(π) ∈ [0.20, 0.21)`, `L ∈ [0.10, 0.11)`. -/
theorem table41_demand_1 :
    (0.59 ≤ baseSdGap 1.5 0.125 0.5 (demandLoad 0.5) ∧
      baseSdGap 1.5 0.125 0.5 (demandLoad 0.5) < 0.60) ∧
    (0.20 ≤ baseSdInfl 1.5 0.125 0.5 (demandLoad 0.5) ∧
      baseSdInfl 1.5 0.125 0.5 (demandLoad 0.5) < 0.21) ∧
    (0.10 ≤ baseLoss 1.5 0.125 0.5 (demandLoad 0.5) ∧
      baseLoss 1.5 0.125 0.5 (demandLoad 0.5) < 0.11) := by
  simp only [baseSdGap, baseSdInfl, baseLoss, msvLoss, avgLoss, kappa_base, lambda_base,
    gapCoeff_base, msvPsiY, msvPsiPi, msvLambda, msvDen, ar1Var, demandLoad]
  refine ⟨sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ⟨by norm_num, by norm_num⟩⟩

/-- Galí (2015), Table 4.1, p. 113, demand (preference) shock, `φ_π = 1.5`, `φ_y = 0`
(truncated to the printed digits; `σ(y) = σ(ỹ)` since `ŷ^n = 0`):
`σ(ỹ) ∈ [0.68, 0.69)`, `σ(π) ∈ [0.23, 0.24)`, `L ∈ [0.13, 0.14)`. -/
theorem table41_demand_2 :
    (0.68 ≤ baseSdGap 1.5 0 0.5 (demandLoad 0.5) ∧ baseSdGap 1.5 0 0.5 (demandLoad 0.5) < 0.69) ∧
    (0.23 ≤ baseSdInfl 1.5 0 0.5 (demandLoad 0.5) ∧ baseSdInfl 1.5 0 0.5 (demandLoad 0.5) < 0.24) ∧
    (0.13 ≤ baseLoss 1.5 0 0.5 (demandLoad 0.5) ∧ baseLoss 1.5 0 0.5 (demandLoad 0.5) < 0.14) := by
  simp only [baseSdGap, baseSdInfl, baseLoss, msvLoss, avgLoss, kappa_base, lambda_base,
    gapCoeff_base, msvPsiY, msvPsiPi, msvLambda, msvDen, ar1Var, demandLoad]
  refine ⟨sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ⟨by norm_num, by norm_num⟩⟩

/-- Galí (2015), Table 4.1, p. 113, demand (preference) shock, `φ_π = 5`, `φ_y = 0`
(truncated to the printed digits; `σ(y) = σ(ỹ)` since `ŷ^n = 0`):
`σ(ỹ) ∈ [0.28, 0.29)`, `σ(π) ∈ [0.09, 0.10)`, `L ∈ [0.02, 0.03)`. -/
theorem table41_demand_3 :
    (0.28 ≤ baseSdGap 5 0 0.5 (demandLoad 0.5) ∧ baseSdGap 5 0 0.5 (demandLoad 0.5) < 0.29) ∧
    (0.09 ≤ baseSdInfl 5 0 0.5 (demandLoad 0.5) ∧ baseSdInfl 5 0 0.5 (demandLoad 0.5) < 0.10) ∧
    (0.02 ≤ baseLoss 5 0 0.5 (demandLoad 0.5) ∧ baseLoss 5 0 0.5 (demandLoad 0.5) < 0.03) := by
  simp only [baseSdGap, baseSdInfl, baseLoss, msvLoss, avgLoss, kappa_base, lambda_base,
    gapCoeff_base, msvPsiY, msvPsiPi, msvLambda, msvDen, ar1Var, demandLoad]
  refine ⟨sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ⟨by norm_num, by norm_num⟩⟩

/-- Galí (2015), Table 4.1, p. 113, demand (preference) shock, `φ_π = 1.5`, `φ_y = 1`
(truncated to the printed digits; `σ(y) = σ(ỹ)` since `ŷ^n = 0`):
`σ(ỹ) ∈ [0.31, 0.32)`, `σ(π) ∈ [0.10, 0.11)`, `L ∈ [0.02, 0.03)`. -/
theorem table41_demand_4 :
    (0.31 ≤ baseSdGap 1.5 1 0.5 (demandLoad 0.5) ∧ baseSdGap 1.5 1 0.5 (demandLoad 0.5) < 0.32) ∧
    (0.10 ≤ baseSdInfl 1.5 1 0.5 (demandLoad 0.5) ∧ baseSdInfl 1.5 1 0.5 (demandLoad 0.5) < 0.11) ∧
    (0.02 ≤ baseLoss 1.5 1 0.5 (demandLoad 0.5) ∧ baseLoss 1.5 1 0.5 (demandLoad 0.5) < 0.03) := by
  simp only [baseSdGap, baseSdInfl, baseLoss, msvLoss, avgLoss, kappa_base, lambda_base,
    gapCoeff_base, msvPsiY, msvPsiPi, msvLambda, msvDen, ar1Var, demandLoad]
  refine ⟨sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    sqrt_bounds (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ⟨by norm_num, by norm_num⟩⟩

/-- Galí (2015), Table 4.1, p. 113 (**the printed entries are truncated, not rounded**): e.g.
for technology with `φ_π = 1.5`, `φ_y = 0`, `σ(π) ≈ 0.3458` (printed `0.34`) and
`σ(ỹ) ≈ 0.2196` (printed `0.21`); for demand with `φ_π = 1.5`, `φ_y = 1`, `L ≈ 0.0278`
(printed `0.02`). All 32 entries agree with the closed forms after truncation. -/
theorem table41_truncated :
    0.345 < baseSdInfl 1.5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) ∧
      0.215 < baseSdGap 1.5 0 0.9 (techLoad 1 0 0.9 (psiYA 1 5 0.25)) ∧
      0.025 < baseLoss 1.5 1 0.5 (demandLoad 0.5) := by
  simp only [baseSdGap, baseSdInfl, baseLoss, msvLoss, avgLoss, kappa_base, lambda_base,
    gapCoeff_base, psiYA_base, msvPsiY, msvPsiPi, msvLambda, msvDen, ar1Var, techLoad,
    demandLoad]
  refine ⟨(Real.lt_sqrt (by norm_num)).2 (by norm_num),
    (Real.lt_sqrt (by norm_num)).2 (by norm_num), by norm_num⟩

end Gali.MonetaryPolicyDesign.SimpleRules
