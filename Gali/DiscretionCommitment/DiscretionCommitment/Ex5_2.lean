/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DiscretionCommitment.Expectations

/-!
# Exercise 5.2: optimal Markovian policy

Galí (2015), Chapter 5, Exercise 5.2, p. 160. Inflation follows the New Keynesian Phillips
curve `π_t = β E_t π_{t+1} + κ x_t + u_t` with an AR(1) cost-push shock
(`E_t u_{t+1} = ρ_u u_t`). In period 0 the central bank chooses, once and for all, a policy
`x_t = ψ_x u_t`, `π_t = ψ_π u_t` minimising `E_0 ∑ βᵗ (π_t² + ϑ x_t²)` subject to the
Phillips curve at every date.

The loss is a genuine infinite sum, `loss x π ω = ∑' t, βᵗ E_0[π_t² + ϑ x_t²](ω)`, summable for
bounded processes (`loss_summable`). For a Markov policy it factors as
`(ψ_π² + ϑ ψ_x²) W`, `W = ∑' t, βᵗ E_0[u_t²]` (`loss_markov`, `shockWeight_pos`).

## (a) The optimal Markov policy
`markov_feasible_iff`: the policy satisfies the Phillips curve at every date iff
`ψ_π (1 − βρ_u) = κ ψ_x + 1` (for a shock that is not identically zero). `objective_eq`:
on that line `ψ_π² + ϑψ_x² = ϑ/Δ + (ψ_π − ψ_π*)² + ϑ (ψ_x − ψ_x*)²` with
`Δ = κ² + ϑ(1 − βρ_u)²`, `ψ_π* = ϑ(1 − βρ_u)/Δ`, `ψ_x* = −κ/Δ`; hence `ex5_2a` (the unique
minimiser of the loss among feasible Markov policies).

## (b) Comparison with discretion
`discretion_unique`: the discretionary targeting rule `x_t = −(κ/ϑ) π_t` (text, eq. (4)) has
the unique bounded solution `π_t = ϑ u_t/(κ² + ϑ(1 − βρ_u))`, `x_t = −κ u_t/(κ² + ϑ(1 − βρ_u))`
(text, eqs. (5)–(6)); it is a feasible Markov policy. `ex5_2b`: the optimal Markov policy is
weakly better than discretion, **strictly better iff `ρ_u ≠ 0`** (for either sign of `ρ_u`), and
coincides with discretion when `ρ_u = 0`.

## (c) Comparison with commitment
`ex5_2c`: for every `|ρ_u| < 1` there is a feasible (bounded, adapted) commitment path with a
strictly lower loss than the optimal Markov policy, built by perturbing the Markov path at
dates 0 (`ρ_u ≠ 0`) or 0 and 1 (`ρ_u = 0`). Hence (`ex5_2c_commitment`) any optimal policy
under commitment is strictly better than the optimal Markov policy (in particular weakly
better), and the optimal Markov policy is not optimal under commitment.
-/

namespace Gali.DiscretionCommitment.Ex5_2

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The model and the loss -/

/-- Galí (2015), Exercise 5.2, p. 160: the Phillips curve `π_t = β E_t π_{t+1} + κ x_t + u_t`
at every date. -/
def NKPC (β κ : ℝ) (x infl u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • x t + u t

/-- Galí (2015), Exercise 5.2, p. 160: the date-`t` term `βᵗ E_0[π_t² + ϑ x_t²]` of the loss. -/
noncomputable def lossTerm (β ϑ : ℝ) (x infl : ℕ → Ω → ℝ) (ω : Ω) (t : ℕ) : ℝ :=
  β ^ t * 𝔼.E 0 (fun ω' => infl t ω' ^ 2 + ϑ * x t ω' ^ 2) ω

/-- Galí (2015), Exercise 5.2, p. 160: the loss `E_0 ∑ βᵗ (π_t² + ϑ x_t²)` (in state `ω`). -/
noncomputable def loss (β ϑ : ℝ) (x infl : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑' t, lossTerm 𝔼 β ϑ x infl ω t

/-- Galí (2015), Exercise 5.2: the shock weight `W = ∑' t, βᵗ E_0[u_t²]`. -/
noncomputable def shockWeight (β : ℝ) (u : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑' t, β ^ t * 𝔼.E 0 (fun ω' => u t ω' ^ 2) ω

/-- Galí (2015), Exercise 5.2: a Markov policy `x_t = ψ_x u_t`, `π_t = ψ_π u_t`. -/
def markov (ψ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => ψ • u t

/-- Galí (2015), Exercise 5.2: `E_t` of a nonnegative random variable is nonnegative. -/
theorem E_nonneg {f : Ω → ℝ} (hf : 0 ≤ f) (t : ℕ) (ω : Ω) : 0 ≤ 𝔼.E t f ω := by
  have h := 𝔼.mono t hf ω
  simpa using h

/-- Galí (2015), Exercise 5.2: for bounded processes the loss series is summable
(`0 ≤ β < 1`, `ϑ ≥ 0`). -/
theorem loss_summable {β ϑ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hϑ : 0 ≤ ϑ) {x p : ℕ → Ω → ℝ}
    (hx : BoundedProc x) (hp : BoundedProc p) (ω : Ω) :
    Summable (lossTerm 𝔼 β ϑ x p ω) := by
  obtain ⟨M, hM⟩ := hx
  obtain ⟨N, hN⟩ := hp
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (N ^ 2 + ϑ * M ^ 2)) (fun t => ?_)
  rw [Real.norm_eq_abs, lossTerm, abs_mul, abs_pow, abs_of_nonneg hβ0]
  refine mul_le_mul_of_nonneg_left (𝔼.abs_E_le (fun ω' => ?_) 0 ω) (pow_nonneg hβ0 t)
  have h1 : p t ω' ^ 2 ≤ N ^ 2 := by
    have := hN t ω'; rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have h2 : x t ω' ^ 2 ≤ M ^ 2 := by
    have := hM t ω'; rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
  rw [abs_of_nonneg (by positivity)]
  nlinarith

/-- Galí (2015), Exercise 5.2: the shock-weight series is summable for bounded `u`. -/
theorem shockWeight_summable {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u : ℕ → Ω → ℝ}
    (hu : BoundedProc u) (ω : Ω) :
    Summable (fun t => β ^ t * 𝔼.E 0 (fun ω' => u t ω' ^ 2) ω) := by
  have h := loss_summable 𝔼 hβ0 hβ1 le_rfl (x := 0) ⟨0, fun _ _ => by simp⟩ hu ω
  refine h.congr fun t => ?_
  simp [lossTerm]

/-- Galí (2015), Exercise 5.2: `W ≥ E_0[u_0²] > 0` when `E_0[u_0²] > 0`. -/
theorem shockWeight_pos {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {u : ℕ → Ω → ℝ}
    (hu : BoundedProc u) {ω : Ω} (h0 : 0 < 𝔼.E 0 (fun ω' => u 0 ω' ^ 2) ω) :
    0 < shockWeight 𝔼 β u ω := by
  have hs := shockWeight_summable 𝔼 hβ0 hβ1 hu ω
  have hle := hs.le_tsum 0 (fun t _ =>
    mul_nonneg (pow_nonneg hβ0 t) (E_nonneg 𝔼 (fun ω' => sq_nonneg _) 0 ω))
  simp only [pow_zero, one_mul] at hle
  exact h0.trans_le hle

/-- Galí (2015), Exercise 5.2, p. 160: the loss of a Markov policy is
`(ψ_π² + ϑ ψ_x²) ∑' t, βᵗ E_0[u_t²]`. -/
theorem loss_markov (β ϑ ψx ψp : ℝ) (u : ℕ → Ω → ℝ) (ω : Ω) :
    loss 𝔼 β ϑ (markov ψx u) (markov ψp u) ω = (ψp ^ 2 + ϑ * ψx ^ 2) * shockWeight 𝔼 β u ω := by
  unfold loss shockWeight lossTerm
  rw [← tsum_mul_left]
  refine tsum_congr fun t => ?_
  have hf : (fun ω' => markov ψp u t ω' ^ 2 + ϑ * markov ψx u t ω' ^ 2) =
      (ψp ^ 2 + ϑ * ψx ^ 2) • fun ω' => u t ω' ^ 2 := by
    funext ω'
    simp only [markov, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hf, map_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### (a) The optimal Markov policy -/

/-- Galí (2015), Exercise 5.2(a): at date `t` a Markov policy satisfies the Phillips curve iff
`(ψ_π (1 − βρ_u) − κψ_x − 1) u_t = 0`. -/
theorem markov_nkpc_iff {β κ ρ ψx ψp : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (t : ℕ) :
    markov ψp u t = β • 𝔼.E t (markov ψp u (t + 1)) + κ • markov ψx u t + u t ↔
      (ψp * (1 - β * ρ) - κ * ψx - 1) • u t = 0 := by
  simp only [markov, map_smul, hu.2 t, smul_smul]
  constructor
  · intro h
    funext ω
    have := congrFun h ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    linear_combination this
  · intro h
    funext ω
    have := congrFun h ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    linear_combination this

/-- Galí (2015), Exercise 5.2(a): a Markov policy on the constraint line
`ψ_π (1 − βρ_u) = κ ψ_x + 1` satisfies the Phillips curve at every date. -/
theorem markov_feasible {β κ ρ ψx ψp : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u)
    (h : ψp * (1 - β * ρ) = κ * ψx + 1) : NKPC 𝔼 β κ (markov ψx u) (markov ψp u) u := by
  intro t
  refine (markov_nkpc_iff 𝔼 hu t).mpr ?_
  rw [show ψp * (1 - β * ρ) - κ * ψx - 1 = 0 by linarith, zero_smul]

/-- Galí (2015), Exercise 5.2(a): a Markov policy satisfies the Phillips curve at every date
iff `ψ_π (1 − βρ_u) = κ ψ_x + 1`, for a shock that is not identically zero. -/
theorem markov_feasible_iff {β κ ρ ψx ψp : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u)
    (hne : ∃ t ω, u t ω ≠ 0) :
    NKPC 𝔼 β κ (markov ψx u) (markov ψp u) u ↔ ψp * (1 - β * ρ) = κ * ψx + 1 := by
  refine ⟨fun h => ?_, markov_feasible 𝔼 hu⟩
  obtain ⟨t, ω, hω⟩ := hne
  have h1 := congrFun ((markov_nkpc_iff 𝔼 hu t).mp (h t)) ω
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · linarith
  · exact absurd h1 hω

/-- Galí (2015), Exercise 5.2(a): `Δ = κ² + ϑ(1 − βρ_u)²`. -/
def delta2 (β κ ϑ ρ : ℝ) : ℝ := κ ^ 2 + ϑ * (1 - β * ρ) ^ 2

/-- **Exercise 5.2(a)** (Galí 2015, p. 160): the optimal `ψ_π* = ϑ(1 − βρ_u)/Δ`. -/
noncomputable def psiP (β κ ϑ ρ : ℝ) : ℝ := ϑ * (1 - β * ρ) / delta2 β κ ϑ ρ

/-- **Exercise 5.2(a)** (Galí 2015, p. 160): the optimal `ψ_x* = −κ/Δ`. -/
noncomputable def psiX (β κ ϑ ρ : ℝ) : ℝ := -κ / delta2 β κ ϑ ρ

/-- Galí (2015), Exercise 5.2(a): the objective `ψ_π² + ϑ ψ_x²` per unit of shock weight. -/
def objective (ϑ ψx ψp : ℝ) : ℝ := ψp ^ 2 + ϑ * ψx ^ 2

/-- Galí (2015), Exercise 5.2(a): `Δ > 0` for `κ ≠ 0`, `ϑ ≥ 0`. -/
theorem delta2_pos {β κ ϑ ρ : ℝ} (hκ : κ ≠ 0) (hϑ : 0 ≤ ϑ) : 0 < delta2 β κ ϑ ρ := by
  unfold delta2; positivity

/-- Galí (2015), Exercise 5.2(a): `(ψ_x*, ψ_π*)` satisfies the constraint. -/
theorem psi_feasible {β κ ϑ ρ : ℝ} (hκ : κ ≠ 0) (hϑ : 0 ≤ ϑ) :
    psiP β κ ϑ ρ * (1 - β * ρ) = κ * psiX β κ ϑ ρ + 1 := by
  have := (delta2_pos (β := β) (ρ := ρ) hκ hϑ).ne'
  unfold psiP psiX
  field_simp
  unfold delta2
  ring

/-- **Exercise 5.2(a), the key identity** (Galí 2015, p. 160): on the constraint line,
`ψ_π² + ϑψ_x² = ϑ/Δ + (ψ_π − ψ_π*)² + ϑ(ψ_x − ψ_x*)²`. -/
theorem objective_eq {β κ ϑ ρ ψx ψp : ℝ} (hκ : κ ≠ 0) (hϑ : 0 ≤ ϑ)
    (h : ψp * (1 - β * ρ) = κ * ψx + 1) :
    objective ϑ ψx ψp = ϑ / delta2 β κ ϑ ρ + (ψp - psiP β κ ϑ ρ) ^ 2 +
      ϑ * (ψx - psiX β κ ϑ ρ) ^ 2 := by
  have hΔ := (delta2_pos (β := β) (ρ := ρ) hκ hϑ).ne'
  have key : objective ϑ ψx ψp - (ϑ / delta2 β κ ϑ ρ + (ψp - psiP β κ ϑ ρ) ^ 2 +
      ϑ * (ψx - psiX β κ ϑ ρ) ^ 2) =
      2 * ϑ / delta2 β κ ϑ ρ * (ψp * (1 - β * ρ) - κ * ψx - 1) := by
    unfold objective psiP psiX
    field_simp
    unfold delta2
    ring
  rw [show ψp * (1 - β * ρ) - κ * ψx - 1 = 0 by linarith, mul_zero, sub_eq_zero] at key
  exact key

/-- Galí (2015), Exercise 5.2(a): the minimal objective is `ϑ/Δ`. -/
theorem objective_opt {β κ ϑ ρ : ℝ} (hκ : κ ≠ 0) (hϑ : 0 ≤ ϑ) :
    objective ϑ (psiX β κ ϑ ρ) (psiP β κ ϑ ρ) = ϑ / delta2 β κ ϑ ρ := by
  rw [objective_eq hκ hϑ (psi_feasible hκ hϑ)]
  ring

/-- **Exercise 5.2(a), the optimal Markov policy** (Galí 2015, p. 160): with `κ ≠ 0`,
`ϑ > 0` and a shock that is not identically zero, `ψ_x* = −κ/Δ`, `ψ_π* = ϑ(1 − βρ_u)/Δ` is
feasible, and every feasible Markov policy has a loss at least as large, strictly larger
unless it is `(ψ_x*, ψ_π*)` (when `W > 0`, e.g. `shockWeight_pos`). -/
theorem ex5_2a {β κ ϑ ρ : ℝ} (hκ : κ ≠ 0) (hϑ : 0 < ϑ) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u)
    (hne : ∃ t ω, u t ω ≠ 0) (ω : Ω) (hW : 0 < shockWeight 𝔼 β u ω) :
    NKPC 𝔼 β κ (markov (psiX β κ ϑ ρ) u) (markov (psiP β κ ϑ ρ) u) u ∧
      loss 𝔼 β ϑ (markov (psiX β κ ϑ ρ) u) (markov (psiP β κ ϑ ρ) u) ω =
        ϑ / delta2 β κ ϑ ρ * shockWeight 𝔼 β u ω ∧
      ∀ ψx ψp, NKPC 𝔼 β κ (markov ψx u) (markov ψp u) u →
        loss 𝔼 β ϑ (markov (psiX β κ ϑ ρ) u) (markov (psiP β κ ϑ ρ) u) ω ≤
          loss 𝔼 β ϑ (markov ψx u) (markov ψp u) ω ∧
        (loss 𝔼 β ϑ (markov ψx u) (markov ψp u) ω =
          loss 𝔼 β ϑ (markov (psiX β κ ϑ ρ) u) (markov (psiP β κ ϑ ρ) u) ω →
            ψx = psiX β κ ϑ ρ ∧ ψp = psiP β κ ϑ ρ) := by
  refine ⟨markov_feasible 𝔼 hu (psi_feasible hκ hϑ.le), ?_, fun ψx ψp hf => ?_⟩
  · rw [loss_markov, ← objective_opt (β := β) (ρ := ρ) hκ hϑ.le]
    rfl
  have hc := (markov_feasible_iff 𝔼 hu hne).mp hf
  have he := objective_eq (β := β) (ρ := ρ) hκ hϑ.le hc
  rw [loss_markov, loss_markov]
  change objective ϑ _ _ * _ ≤ objective ϑ _ _ * _ ∧ (objective ϑ _ _ * _ = objective ϑ _ _ * _ → _)
  rw [objective_opt hκ hϑ.le, he]
  have hle : ϑ / delta2 β κ ϑ ρ ≤ ϑ / delta2 β κ ϑ ρ + (ψp - psiP β κ ϑ ρ) ^ 2 +
      ϑ * (ψx - psiX β κ ϑ ρ) ^ 2 := by
    nlinarith [sq_nonneg (ψp - psiP β κ ϑ ρ), sq_nonneg (ψx - psiX β κ ϑ ρ)]
  refine ⟨mul_le_mul_of_nonneg_right hle hW.le, fun h => ?_⟩
  have h2 : (ψp - psiP β κ ϑ ρ) ^ 2 + ϑ * (ψx - psiX β κ ϑ ρ) ^ 2 = 0 := by
    have := mul_right_cancel₀ hW.ne' h
    linarith
  have hq1 := sq_nonneg (ψp - psiP β κ ϑ ρ)
  have hq2 := mul_nonneg hϑ.le (sq_nonneg (ψx - psiX β κ ϑ ρ))
  have h3 : (ψp - psiP β κ ϑ ρ) ^ 2 = 0 := by linarith
  have h4 : ϑ * (ψx - psiX β κ ϑ ρ) ^ 2 = 0 := by linarith
  rw [mul_eq_zero] at h4
  rcases h4 with h4 | h4
  · exact absurd h4 hϑ.ne'
  exact ⟨sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4),
    sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)⟩

/-! ### (b) Comparison with discretion -/

/-- Galí (2015), eqs. (5)–(6), p. 130: `Δ_d = κ² + ϑ(1 − βρ_u)`. -/
def deltaD (β κ ϑ ρ : ℝ) : ℝ := κ ^ 2 + ϑ * (1 - β * ρ)

/-- Galí (2015), eq. (5), p. 130: discretionary inflation `π_t = ϑ u_t/Δ_d`. -/
noncomputable def discP (β κ ϑ ρ : ℝ) : ℝ := ϑ / deltaD β κ ϑ ρ

/-- Galí (2015), eq. (6), p. 130: the discretionary output gap `x_t = −κ u_t/Δ_d`. -/
noncomputable def discX (β κ ϑ ρ : ℝ) : ℝ := -κ / deltaD β κ ϑ ρ

/-- Galí (2015), Exercise 5.2: `βρ_u < 1` for `0 < β < 1`, `|ρ_u| < 1`. -/
theorem beta_rho_lt_one {β ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : |ρ| < 1) : β * ρ < 1 := by
  have h1 : β * ρ ≤ β * |ρ| := mul_le_mul_of_nonneg_left (le_abs_self ρ) hβ0.le
  have h2 : β * |ρ| < β * 1 := mul_lt_mul_of_pos_left hρ hβ0
  linarith

/-- Galí (2015), eqs. (5)–(6): `Δ_d > 0`. -/
theorem deltaD_pos {β κ ϑ ρ : ℝ} (hκ : κ ≠ 0) (hϑ : 0 ≤ ϑ) (hβρ : β * ρ < 1) :
    0 < deltaD β κ ϑ ρ := by
  unfold deltaD
  have : 0 < 1 - β * ρ := by linarith
  positivity

/-- Galí (2015), eq. (4), p. 130: the discretionary coefficients satisfy the targeting rule
`x_t = −(κ/ϑ) π_t`. -/
theorem disc_targeting {β κ ϑ ρ : ℝ} (hϑ : ϑ ≠ 0) :
    discX β κ ϑ ρ = -(κ / ϑ) * discP β κ ϑ ρ := by
  unfold discX discP
  by_cases h : deltaD β κ ϑ ρ = 0
  · simp [h]
  · field_simp

/-- Galí (2015), Exercise 5.2(b): discretion is a feasible Markov policy. -/
theorem disc_feasible {β κ ϑ ρ : ℝ} (hκ : κ ≠ 0) (hϑ : 0 ≤ ϑ) (hβρ : β * ρ < 1) :
    discP β κ ϑ ρ * (1 - β * ρ) = κ * discX β κ ϑ ρ + 1 := by
  have := (deltaD_pos hκ hϑ hβρ).ne'
  unfold discP discX
  field_simp
  unfold deltaD
  ring

/-- **Galí (2015), eqs. (4)–(6), p. 130 (discretion)**: if the output gap follows the targeting
rule `x_t = −(κ/ϑ) π_t` and the Phillips curve holds, the unique bounded inflation process is
`π_t = ϑ u_t/Δ_d`, and `x_t = −κ u_t/Δ_d`. -/
theorem discretion_unique {β κ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hϑ : 0 < ϑ)
    (hρ : |ρ| < 1) {u x p : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u)
    (hn : NKPC 𝔼 β κ x p u) (ht : ∀ t, x t = -(κ / ϑ) • p t) (hpb : BoundedProc p) :
    p = markov (discP β κ ϑ ρ) u ∧ x = markov (discX β κ ϑ ρ) u := by
  have hβρ := beta_rho_lt_one hβ0 hβ1 hρ
  have hD := deltaD_pos hκ hϑ.le hβρ
  have hK : 0 < ϑ + κ ^ 2 := by positivity
  set a := ϑ * β / (ϑ + κ ^ 2)
  set b := ϑ / (ϑ + κ ^ 2)
  have ha : |a| < 1 := by
    rw [abs_of_nonneg (by positivity), div_lt_one hK]
    nlinarith [sq_nonneg κ, pow_pos (abs_pos.mpr hκ) 2]
  have h1 : ∀ t, p t = a • 𝔼.E t (p (t + 1)) + b • u t := by
    intro t
    funext ω
    have e1 := congrFun (hn t) ω
    have e2 := congrFun (ht t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
    rw [e2] at e1
    simp only [a, b]
    field_simp
    have hinv : ϑ * ϑ⁻¹ = 1 := mul_inv_cancel₀ hϑ.ne'
    linear_combination ϑ * e1 - p t ω * κ ^ 2 * hinv
  have h2 : ∀ t, markov (discP β κ ϑ ρ) u t =
      a • 𝔼.E t (markov (discP β κ ϑ ρ) u (t + 1)) + b • u t := by
    intro t
    funext ω
    simp only [markov, map_smul, hu.2 t, Pi.add_apply, Pi.smul_apply, smul_eq_mul, a, b,
      discP]
    unfold deltaD at hD ⊢
    field_simp
    ring
  obtain ⟨M, hM⟩ := hub
  have hcb : BoundedProc (markov (discP β κ ϑ ρ) u) :=
    ⟨|discP β κ ϑ ρ| * M, fun t ω => by
      simp only [markov, Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)⟩
  have hp := 𝔼.forward_unique ha h1 h2 hpb hcb
  refine ⟨hp, ?_⟩
  funext t
  rw [ht t, hp]
  simp only [markov, smul_smul, disc_targeting (β := β) (ρ := ρ) hϑ.ne']

/-- **Exercise 5.2(b)** (Galí 2015, p. 160): the optimal Markov policy is weakly better than
discretion; it is **strictly** better iff `ρ_u ≠ 0`; for `ρ_u = 0` the two coincide. -/
theorem ex5_2b_objective {β κ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hϑ : 0 < ϑ)
    (hρ : |ρ| < 1) :
    objective ϑ (psiX β κ ϑ ρ) (psiP β κ ϑ ρ) ≤ objective ϑ (discX β κ ϑ ρ) (discP β κ ϑ ρ) ∧
      (objective ϑ (psiX β κ ϑ ρ) (psiP β κ ϑ ρ) <
          objective ϑ (discX β κ ϑ ρ) (discP β κ ϑ ρ) ↔ ρ ≠ 0) ∧
      (ρ = 0 → psiX β κ ϑ ρ = discX β κ ϑ ρ ∧ psiP β κ ϑ ρ = discP β κ ϑ ρ) := by
  have hβρ := beta_rho_lt_one hβ0 hβ1 hρ
  have hD := deltaD_pos hκ hϑ.le hβρ
  have hΔ := delta2_pos (β := β) (ρ := ρ) hκ hϑ.le
  have he := objective_eq (β := β) (ρ := ρ) hκ hϑ.le (disc_feasible hκ hϑ.le hβρ)
  rw [objective_opt hκ hϑ.le, he]
  have hzero : ρ = 0 → psiX β κ ϑ ρ = discX β κ ϑ ρ ∧ psiP β κ ϑ ρ = discP β κ ϑ ρ := by
    rintro rfl
    constructor <;> simp [psiX, psiP, discX, discP, delta2, deltaD]
  refine ⟨by nlinarith [sq_nonneg (discP β κ ϑ ρ - psiP β κ ϑ ρ),
    sq_nonneg (discX β κ ϑ ρ - psiX β κ ϑ ρ)], ⟨fun h hρ0 => ?_, fun hρ0 => ?_⟩, hzero⟩
  · obtain ⟨h1, h2⟩ := hzero hρ0
    rw [h1, h2, sub_self, sub_self] at h
    simp at h
  · have hne : discX β κ ϑ ρ ≠ psiX β κ ϑ ρ := by
      intro h
      unfold discX psiX at h
      rw [div_eq_div_iff hD.ne' hΔ.ne'] at h
      have h' : κ * (deltaD β κ ϑ ρ - delta2 β κ ϑ ρ) = 0 := by linarith
      rcases mul_eq_zero.mp h' with h' | h'
      · exact hκ h'
      · unfold deltaD delta2 at h'
        have h'' : ϑ * (1 - β * ρ) * (β * ρ) = 0 := by linarith
        rcases mul_eq_zero.mp h'' with h3 | h3
        · rcases mul_eq_zero.mp h3 with h4 | h4
          · exact hϑ.ne' h4
          · linarith
        · rcases mul_eq_zero.mp h3 with h4 | h4
          · exact hβ0.ne' h4
          · exact hρ0 h4
    have : 0 < ϑ * (discX β κ ϑ ρ - psiX β κ ϑ ρ) ^ 2 :=
      mul_pos hϑ (sq_pos_iff.mpr (sub_ne_zero.mpr hne))
    nlinarith [sq_nonneg (discP β κ ϑ ρ - psiP β κ ϑ ρ)]

/-- **Exercise 5.2(b), in terms of the loss** (Galí 2015, p. 160): the optimal Markov policy
has a loss no larger than discretion's, and strictly smaller iff `ρ_u ≠ 0` (when `W > 0`). -/
theorem ex5_2b {β κ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hϑ : 0 < ϑ)
    (hρ : |ρ| < 1) (u : ℕ → Ω → ℝ) (ω : Ω) (hW : 0 < shockWeight 𝔼 β u ω) :
    loss 𝔼 β ϑ (markov (psiX β κ ϑ ρ) u) (markov (psiP β κ ϑ ρ) u) ω ≤
        loss 𝔼 β ϑ (markov (discX β κ ϑ ρ) u) (markov (discP β κ ϑ ρ) u) ω ∧
      (loss 𝔼 β ϑ (markov (psiX β κ ϑ ρ) u) (markov (psiP β κ ϑ ρ) u) ω <
          loss 𝔼 β ϑ (markov (discX β κ ϑ ρ) u) (markov (discP β κ ϑ ρ) u) ω ↔ ρ ≠ 0) := by
  obtain ⟨h1, h2, -⟩ := ex5_2b_objective hβ0 hβ1 hκ hϑ hρ
  rw [loss_markov, loss_markov]
  change objective ϑ _ _ * _ ≤ objective ϑ _ _ * _ ∧ (objective ϑ _ _ * _ < objective ϑ _ _ * _ ↔ _)
  refine ⟨mul_le_mul_of_nonneg_right h1 hW.le, ?_⟩
  rw [mul_lt_mul_iff_left₀ hW]
  exact h2

/-! ### (c) Comparison with commitment -/

/-- Galí (2015), §5.2.2 and Exercise 5.2(c): a path is feasible under commitment if it is
bounded, adapted and satisfies the Phillips curve at every date. -/
def CommitFeasible (β κ : ℝ) (u x p : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted x ∧ 𝔼.Adapted p ∧ BoundedProc x ∧ BoundedProc p ∧ NKPC 𝔼 β κ x p u

/-- Galí (2015), Exercise 5.2(c): two bounded paths that agree from date `k` on have losses
differing by the finite sum of the first `k` terms. -/
theorem loss_eq_of_eq_after {β ϑ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hϑ : 0 ≤ ϑ)
    {x p x' p' : ℕ → Ω → ℝ} (hx : BoundedProc x) (hp : BoundedProc p) (hx' : BoundedProc x')
    (hp' : BoundedProc p') (k : ℕ)
    (heq : ∀ t, x' (t + k) = x (t + k) ∧ p' (t + k) = p (t + k)) (ω : Ω) :
    loss 𝔼 β ϑ x' p' ω = loss 𝔼 β ϑ x p ω +
      ∑ t ∈ Finset.range k, (lossTerm 𝔼 β ϑ x' p' ω t - lossTerm 𝔼 β ϑ x p ω t) := by
  unfold loss
  rw [← (loss_summable 𝔼 hβ0 hβ1 hϑ hx' hp' ω).sum_add_tsum_nat_add k,
    ← (loss_summable 𝔼 hβ0 hβ1 hϑ hx hp ω).sum_add_tsum_nat_add k, Finset.sum_sub_distrib]
  have : ∑' t, lossTerm 𝔼 β ϑ x' p' ω (t + k) = ∑' t, lossTerm 𝔼 β ϑ x p ω (t + k) :=
    tsum_congr fun t => by simp only [lossTerm, (heq t).1, (heq t).2]
  rw [this]
  ring

omit 𝔼 in
/-- Galí (2015), Exercise 5.2: a Markov policy driven by a bounded shock is bounded. -/
theorem markov_bounded {u : ℕ → Ω → ℝ} (hub : BoundedProc u) (ψ : ℝ) :
    BoundedProc (markov ψ u) := by
  obtain ⟨M, hM⟩ := hub
  exact ⟨|ψ| * M, fun t ω => by
    simp only [markov, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)⟩

/-- Galí (2015), Exercise 5.2: a Markov policy driven by an adapted shock is adapted. -/
theorem markov_adapted {u : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u) (ψ : ℝ) :
    𝔼.Adapted (markov ψ u) := fun t => by simp only [markov, map_smul, hu t]

omit 𝔼 in
/-- Galí (2015), Exercise 5.2(c): a bounded process plus a bounded multiple of `u_0` is
bounded. -/
theorem bounded_add_smul {u y : ℕ → Ω → ℝ} (hub : BoundedProc u) (hy : BoundedProc y)
    {g : ℕ → ℝ} {C : ℝ} (hg : ∀ t, |g t| ≤ C) : BoundedProc fun t => y t + g t • u 0 := by
  obtain ⟨M, hM⟩ := hub
  obtain ⟨N, hN⟩ := hy
  refine ⟨N + C * M, fun t ω => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ω)
  refine (abs_add_le _ _).trans (add_le_add (hN t ω) ?_)
  rw [abs_mul]
  exact mul_le_mul (hg t) (hM 0 ω) (abs_nonneg _) ((abs_nonneg _).trans (hg t))

/-- Galí (2015), Exercise 5.2(c): `u_0` is known at every date, `E_t u_0 = u_0`. -/
theorem E_u0 {ρ : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (t : ℕ) : 𝔼.E t (u 0) = u 0 := by
  rw [← hu.1 0, 𝔼.known (Nat.zero_le t)]

/-- Galí (2015), Exercise 5.2(c): adding a multiple of `u_0` keeps a process adapted. -/
theorem adapted_add_smul {ρ : ℝ} {u y : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hy : 𝔼.Adapted y)
    (g : ℕ → ℝ) : 𝔼.Adapted fun t => y t + g t • u 0 := fun t => by
  simp only [map_add, map_smul, hy t, E_u0 𝔼 hu t]

/-- Galí (2015), Exercise 5.2(c): `E_0[k u_t²] = k E_0[u_t²]` in the form used below. -/
theorem E0_sq_smul {f : Ω → ℝ} {k : ℝ} {g : Ω → ℝ} (hg : g = k • fun ω' => f ω' ^ 2)
    (ω : Ω) : 𝔼.E 0 g ω = k * 𝔼.E 0 (fun ω' => f ω' ^ 2) ω := by
  rw [hg, map_smul, Pi.smul_apply, smul_eq_mul]

/-- **Exercise 5.2(c), the date-0 improvement** (Galí 2015, p. 160): if a feasible Markov
policy has `κψ_π + ϑψ_x ≠ 0`, perturbing it at date 0 alone, by
`(Δx_0, Δπ_0) = (ε u_0, κ ε u_0)` with `ε = −(κψ_π + ϑψ_x)/(κ² + ϑ)`, gives a feasible
commitment path whose loss is lower by `(κψ_π + ϑψ_x)²/(κ² + ϑ) · E_0[u_0²]`. -/
theorem improve_date0 {β κ ϑ ρ ψx ψp : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hϑ : 0 < ϑ)
    {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u)
    (hcon : ψp * (1 - β * ρ) = κ * ψx + 1) (hc : κ * ψp + ϑ * ψx ≠ 0) {ω : Ω}
    (h0 : 0 < 𝔼.E 0 (fun ω' => u 0 ω' ^ 2) ω) :
    ∃ x p, CommitFeasible 𝔼 β κ u x p ∧
      loss 𝔼 β ϑ x p ω < loss 𝔼 β ϑ (markov ψx u) (markov ψp u) ω := by
  set c := κ * ψp + ϑ * ψx with hc_def
  have hK : 0 < κ ^ 2 + ϑ := by positivity
  set ε := -c / (κ ^ 2 + ϑ) with hε
  set gx : ℕ → ℝ := fun t => if t = 0 then ε else 0 with hgx
  set gp : ℕ → ℝ := fun t => if t = 0 then κ * ε else 0 with hgp
  set x : ℕ → Ω → ℝ := fun t => markov ψx u t + gx t • u 0 with hx
  set p : ℕ → Ω → ℝ := fun t => markov ψp u t + gp t • u 0 with hp
  have hm := markov_feasible 𝔼 hu hcon
  have hbx : BoundedProc x := bounded_add_smul hub (markov_bounded hub ψx) (C := |ε|)
    (fun t => by simp only [hgx]; split_ifs <;> simp)
  have hbp : BoundedProc p := bounded_add_smul hub (markov_bounded hub ψp) (C := |κ * ε|)
    (fun t => by
      simp only [hgp]
      split_ifs
      · exact le_rfl
      · simp only [abs_zero]; positivity)
  have hfeas : CommitFeasible 𝔼 β κ u x p := by
    refine ⟨adapted_add_smul 𝔼 hu (markov_adapted 𝔼 hu.1 ψx) gx,
      adapted_add_smul 𝔼 hu (markov_adapted 𝔼 hu.1 ψp) gp, hbx, hbp, fun t => ?_⟩
    have e := hm t
    funext ω'
    have e' := congrFun e ω'
    simp only [hx, hp, hgx, hgp, map_add, map_smul, E_u0 𝔼 hu, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at e' ⊢
    rcases t with _ | n
    · simp only [↓reduceIte, Nat.add_one_ne_zero, zero_mul, add_zero] at e' ⊢
      linear_combination e'
    · simp only [Nat.add_one_ne_zero, ↓reduceIte, zero_mul, add_zero] at e' ⊢
      linear_combination e'
  refine ⟨x, p, hfeas, ?_⟩
  rw [loss_eq_of_eq_after 𝔼 hβ0 hβ1 hϑ.le (markov_bounded hub ψx) (markov_bounded hub ψp)
    hbx hbp 1 (fun t => by simp [hx, hp, hgx, hgp]) ω, Finset.sum_range_one]
  have e1 : lossTerm 𝔼 β ϑ x p ω 0 =
      ((ψp + κ * ε) ^ 2 + ϑ * (ψx + ε) ^ 2) * 𝔼.E 0 (fun ω' => u 0 ω' ^ 2) ω := by
    rw [lossTerm, pow_zero, one_mul]
    refine E0_sq_smul 𝔼 (funext fun ω' => ?_) ω
    simp only [hx, hp, hgx, hgp, markov, ↓reduceIte, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have e2 : lossTerm 𝔼 β ϑ (markov ψx u) (markov ψp u) ω 0 =
      (ψp ^ 2 + ϑ * ψx ^ 2) * 𝔼.E 0 (fun ω' => u 0 ω' ^ 2) ω := by
    rw [lossTerm, pow_zero, one_mul]
    refine E0_sq_smul 𝔼 (funext fun ω' => ?_) ω
    simp only [markov, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e1, e2, ← sub_mul]
  have hcoef : (ψp + κ * ε) ^ 2 + ϑ * (ψx + ε) ^ 2 - (ψp ^ 2 + ϑ * ψx ^ 2) =
      -(c ^ 2 / (κ ^ 2 + ϑ)) := by
    rw [hε, hc_def]
    field_simp
    ring
  rw [hcoef]
  have : 0 < c ^ 2 / (κ ^ 2 + ϑ) := div_pos (sq_pos_iff.mpr hc) hK
  nlinarith

/-- **Exercise 5.2(c), the date-1 improvement** (Galí 2015, p. 160): if a feasible Markov
policy has `κψ_π + ϑψ_x = 0` but `ψ_π ≠ 0` (the case `ρ_u = 0`), the perturbation
`Δx_1 = ε u_0`, `Δπ_1 = κ ε u_0`, `Δπ_0 = βκ ε u_0` (a promise about date-1 policy that lowers
inflation expectations at date 0), with `ε = −κψ_π/(βκ² + κ² + ϑ)`, is feasible and lowers the
loss by `β κ² ψ_π²/(βκ² + κ² + ϑ) · E_0[u_0²]`. -/
theorem improve_date1 {β κ ϑ ρ ψx ψp : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hϑ : 0 < ϑ) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u)
    (hcon : ψp * (1 - β * ρ) = κ * ψx + 1) (hc : κ * ψp + ϑ * ψx = 0) (hψ : ψp ≠ 0)
    {ω : Ω} (h0 : 0 < 𝔼.E 0 (fun ω' => u 0 ω' ^ 2) ω) :
    ∃ x p, CommitFeasible 𝔼 β κ u x p ∧
      loss 𝔼 β ϑ x p ω < loss 𝔼 β ϑ (markov ψx u) (markov ψp u) ω := by
  have hK : 0 < β * κ ^ 2 + κ ^ 2 + ϑ := by positivity
  set ε := -(ψp * κ) / (β * κ ^ 2 + κ ^ 2 + ϑ) with hε
  set gx : ℕ → ℝ := fun t => if t = 1 then ε else 0 with hgx
  set gp : ℕ → ℝ := fun t => if t = 0 then β * κ * ε else if t = 1 then κ * ε else 0 with hgp
  set x : ℕ → Ω → ℝ := fun t => markov ψx u t + gx t • u 0 with hx
  set p : ℕ → Ω → ℝ := fun t => markov ψp u t + gp t • u 0 with hp
  have hm := markov_feasible 𝔼 hu hcon
  have hbx : BoundedProc x := bounded_add_smul hub (markov_bounded hub ψx) (C := |ε|)
    (fun t => by simp only [hgx]; split_ifs <;> simp)
  have hbp : BoundedProc p := bounded_add_smul hub (markov_bounded hub ψp)
    (C := |β * κ * ε| + |κ * ε|)
    (fun t => by
      simp only [hgp]
      split_ifs
      · linarith [abs_nonneg (κ * ε)]
      · linarith [abs_nonneg (β * κ * ε)]
      · simp only [abs_zero]; positivity)
  have hfeas : CommitFeasible 𝔼 β κ u x p := by
    refine ⟨adapted_add_smul 𝔼 hu (markov_adapted 𝔼 hu.1 ψx) gx,
      adapted_add_smul 𝔼 hu (markov_adapted 𝔼 hu.1 ψp) gp, hbx, hbp, fun t => ?_⟩
    have e := hm t
    funext ω'
    have e' := congrFun e ω'
    simp only [hx, hp, hgx, hgp, map_add, map_smul, E_u0 𝔼 hu, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at e' ⊢
    rcases t with _ | _ | n
    · simp at e' ⊢
      linear_combination e'
    · simp at e' ⊢
      linear_combination e'
    · simp at e' ⊢
      linear_combination e'
  refine ⟨x, p, hfeas, ?_⟩
  rw [loss_eq_of_eq_after 𝔼 hβ0.le hβ1 hϑ.le (markov_bounded hub ψx) (markov_bounded hub ψp)
    hbx hbp 2 (fun t => by simp [hx, hp, hgx, hgp]) ω, Finset.sum_range_succ,
    Finset.sum_range_one]
  have e1 : lossTerm 𝔼 β ϑ x p ω 0 - lossTerm 𝔼 β ϑ (markov ψx u) (markov ψp u) ω 0 =
      (2 * ψp * β * κ * ε + β ^ 2 * κ ^ 2 * ε ^ 2) * 𝔼.E 0 (fun ω' => u 0 ω' ^ 2) ω := by
    rw [lossTerm, lossTerm, pow_zero, one_mul, one_mul, ← Pi.sub_apply, ← map_sub]
    refine E0_sq_smul 𝔼 (funext fun ω' => ?_) ω
    simp only [hx, hp, hgx, hgp, markov, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    simp
    ring
  have e2 : lossTerm 𝔼 β ϑ x p ω 1 - lossTerm 𝔼 β ϑ (markov ψx u) (markov ψp u) ω 1 =
      β * (ε ^ 2 * (κ ^ 2 + ϑ)) * 𝔼.E 0 (fun ω' => u 0 ω' ^ 2) ω := by
    rw [lossTerm, lossTerm, pow_one, ← mul_sub, ← Pi.sub_apply, ← map_sub, mul_assoc]
    congr 1
    refine E0_sq_smul 𝔼 (funext fun ω' => ?_) ω
    simp only [hx, hp, hgx, hgp, markov, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    simp
    linear_combination (2 * ε * u 0 ω' * u 1 ω') * hc
  rw [e1, e2, ← add_mul]
  have hcoef : 2 * ψp * β * κ * ε + β ^ 2 * κ ^ 2 * ε ^ 2 + β * (ε ^ 2 * (κ ^ 2 + ϑ)) =
      -(β * κ ^ 2 * ψp ^ 2 / (β * κ ^ 2 + κ ^ 2 + ϑ)) := by
    rw [hε]
    field_simp
    ring
  rw [hcoef]
  have : 0 < β * κ ^ 2 * ψp ^ 2 / (β * κ ^ 2 + κ ^ 2 + ϑ) :=
    div_pos (by have := sq_pos_iff.mpr hψ; have := sq_pos_iff.mpr hκ; positivity) hK
  nlinarith

/-- Galí (2015), Exercise 5.2(c): for the optimal Markov policy,
`κψ_π* + ϑψ_x* = −κϑβρ_u/Δ`. -/
theorem coef_opt {β κ ϑ ρ : ℝ} (hκ : κ ≠ 0) (hϑ : 0 ≤ ϑ) :
    κ * psiP β κ ϑ ρ + ϑ * psiX β κ ϑ ρ = -(κ * ϑ * β * ρ) / delta2 β κ ϑ ρ := by
  have := (delta2_pos (β := β) (ρ := ρ) hκ hϑ).ne'
  unfold psiP psiX
  field_simp
  ring

/-- **Exercise 5.2(c)** (Galí 2015, p. 160): for every `|ρ_u| < 1` there is a path feasible
under commitment (bounded, adapted, satisfying the Phillips curve) with a strictly lower loss
than the optimal Markov policy (when `E_0[u_0²] > 0`). -/
theorem ex5_2c {β κ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hϑ : 0 < ϑ)
    (hρ : |ρ| < 1) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u) {ω : Ω}
    (h0 : 0 < 𝔼.E 0 (fun ω' => u 0 ω' ^ 2) ω) :
    ∃ x p, CommitFeasible 𝔼 β κ u x p ∧
      loss 𝔼 β ϑ x p ω < loss 𝔼 β ϑ (markov (psiX β κ ϑ ρ) u) (markov (psiP β κ ϑ ρ) u) ω := by
  have hcon := psi_feasible (β := β) (ρ := ρ) hκ hϑ.le
  have hΔ := delta2_pos (β := β) (ρ := ρ) hκ hϑ.le
  by_cases hρ0 : ρ = 0
  · subst hρ0
    refine improve_date1 𝔼 hβ0 hβ1 hκ hϑ hu hub hcon ?_ ?_ h0
    · rw [coef_opt hκ hϑ.le]; simp
    · unfold psiP
      simp only [mul_zero, sub_zero, mul_one]
      exact div_ne_zero hϑ.ne' hΔ.ne'
  · refine improve_date0 𝔼 hβ0.le hβ1 hϑ hu hub hcon ?_ h0
    rw [coef_opt hκ hϑ.le]
    refine div_ne_zero ?_ hΔ.ne'
    simp only [neg_ne_zero]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hκ hϑ.ne') hβ0.ne') hρ0

/-- **Exercise 5.2(c), commitment versus the optimal Markov policy** (Galí 2015, p. 160): the
optimal Markov policy is feasible under commitment but not optimal there; any optimal policy
under commitment has a strictly lower loss (in particular a weakly lower one). -/
theorem ex5_2c_commitment {β κ ϑ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hϑ : 0 < ϑ) (hρ : |ρ| < 1) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u)
    {ω : Ω} (h0 : 0 < 𝔼.E 0 (fun ω' => u 0 ω' ^ 2) ω) :
    CommitFeasible 𝔼 β κ u (markov (psiX β κ ϑ ρ) u) (markov (psiP β κ ϑ ρ) u) ∧
      (¬ ∀ x p, CommitFeasible 𝔼 β κ u x p →
        loss 𝔼 β ϑ (markov (psiX β κ ϑ ρ) u) (markov (psiP β κ ϑ ρ) u) ω ≤
          loss 𝔼 β ϑ x p ω) ∧
      ∀ xc pc, CommitFeasible 𝔼 β κ u xc pc →
        (∀ x p, CommitFeasible 𝔼 β κ u x p → loss 𝔼 β ϑ xc pc ω ≤ loss 𝔼 β ϑ x p ω) →
          loss 𝔼 β ϑ xc pc ω <
            loss 𝔼 β ϑ (markov (psiX β κ ϑ ρ) u) (markov (psiP β κ ϑ ρ) u) ω := by
  obtain ⟨x, p, hf, hlt⟩ := ex5_2c 𝔼 hβ0 hβ1 hκ hϑ hρ hu hub h0
  refine ⟨⟨markov_adapted 𝔼 hu.1 _, markov_adapted 𝔼 hu.1 _, markov_bounded hub _,
    markov_bounded hub _, markov_feasible 𝔼 hu (psi_feasible hκ hϑ.le)⟩,
    fun h => absurd (h x p hf) (not_le.mpr hlt), fun xc pc _ hopt => ?_⟩
  exact (hopt x p hf).trans_lt hlt

end Gali.DiscretionCommitment.Ex5_2
